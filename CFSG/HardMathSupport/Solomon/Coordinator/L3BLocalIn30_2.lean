module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3BLocalSyl
public import CFSG.HardMathSupport.Solomon.Coordinator.L3BLocalExp3

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns CFSG.RankThree.PartTwo.Sec4
  CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial Matrix

variable {π : Bool} {p f : ℕ} {K : Type} [Field K] {X : Type} [Group X] [Finite X]
  {φ : X →* GL (Fin 3) K}

theorem l3b_P1 (hK : PiField π p f K) (hq : ModThree π (p ^ f)) (hφ : L3Model π p f φ) :
    ∀ F : Subgroup (X ⧸ Subgroup.center X), IsElemAbelian 3 F → Nat.card F = 3 ^ 2 →
      (AutHasQ8 F ↔ TotallyFused F) ∧
      (TotallyFused F ↔
        (¬ IsMulCommutative (F.comap (QuotientGroup.mk' (Subgroup.center X))) ∧
          ∀ x ∈ F.comap (QuotientGroup.mk' (Subgroup.center X)), x ^ 3 = 1)) := by
  intro F hF hc'
  have hc : Nat.card F = 9 := by rw [hc']; norm_num
  by_cases hexp : ∀ x ∈ F.comap (QuotientGroup.mk' (Subgroup.center X)), x ^ 3 = 1
  · obtain ⟨hnc, hQ⟩ := l3b_exp3_data hK hq hφ hF hc hexp
    have hfused := l3b_fused_of_q8 hF hc hQ
    exact ⟨⟨fun _ => hfused, fun _ => hQ⟩, ⟨fun _ => ⟨hnc, hexp⟩, fun _ => hfused⟩⟩
  · push Not at hexp
    have hnf := l3b_not_fused_of_cube (fun z hz => hφ.center_pow hK hq hz)
      (hφ.card_center hK hq) hF hc hexp
    refine ⟨⟨fun h => absurd (l3b_fused_of_q8 hF hc h) hnf, fun h => absurd h hnf⟩,
      ⟨fun h => absurd h hnf, fun h => ?_⟩⟩
    obtain ⟨x, hx, hx3⟩ := hexp
    exact absurd (h.2 x hx) hx3

theorem l3b_P2 (hK : PiField π p f K) (hq : ModThree π (p ^ f)) (hφ : L3Model π p f φ)
    (hsyl : (Nat.card (X ⧸ Subgroup.center X)).factorization 3 = 2)
    (P : Sylow 3 (X ⧸ Subgroup.center X)) :
    IsElemAbelian 3 (P : Subgroup (X ⧸ Subgroup.center X)) ∧
      AutHasQ8 (P : Subgroup (X ⧸ Subgroup.center X)) := by
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  obtain ⟨g, hg, x₁, x₂, h₁, h₂, hle⟩ := l3b_sylow_heis hK hq hφ hτ hτ1 P
  obtain ⟨hE1, hE2, hE3, -⟩ := l3b_heis_data hK hq hφ hτ hτ1 hg h₁ h₂
    (E := Subgroup.zpowers (QuotientGroup.mk x₁ : X ⧸ Subgroup.center X) ⊔
      Subgroup.zpowers (QuotientGroup.mk x₂ : X ⧸ Subgroup.center X)) rfl
  have hcardP : Nat.card (P : Subgroup (X ⧸ Subgroup.center X)) = 9 := by
    rw [P.card_eq_multiplicity, hsyl]; norm_num
  have hEP := Subgroup.eq_of_le_of_card_ge hle (by rw [hcardP, hE2])
  exact ⟨hEP ▸ hE1, hEP ▸ hE3⟩

omit [Finite X] in
theorem l3b_mem_cent_iff (x u : X) :
    u ∈ (Subgroup.centralizer ({(QuotientGroup.mk x : X ⧸ Subgroup.center X)} :
      Set (X ⧸ Subgroup.center X))).comap (QuotientGroup.mk' (Subgroup.center X)) ↔
      ∃ z ∈ Subgroup.center X, u * x * u⁻¹ = x * z := by
  rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h' : (QuotientGroup.mk u : X ⧸ Subgroup.center X) * QuotientGroup.mk x =
        QuotientGroup.mk x * QuotientGroup.mk u := h
    refine ⟨x⁻¹ * (u * x * u⁻¹), ?_, by group⟩
    rw [← QuotientGroup.eq_one_iff]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [h']; group
  · rintro ⟨z, hz, h⟩
    have h1 : (QuotientGroup.mk (u * x * u⁻¹) : X ⧸ Subgroup.center X) = QuotientGroup.mk x := by
      rw [h, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff z).2 hz, mul_one]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h1
    show (QuotientGroup.mk u : X ⧸ Subgroup.center X) * QuotientGroup.mk x =
      QuotientGroup.mk x * QuotientGroup.mk u
    calc (QuotientGroup.mk u : X ⧸ Subgroup.center X) * QuotientGroup.mk x =
        (QuotientGroup.mk u * QuotientGroup.mk x * (QuotientGroup.mk u)⁻¹) * QuotientGroup.mk u := by
          group
      _ = _ := by rw [h1]

theorem l3b_P3 (hK : PiField π p f K) (hq : ModThree π (p ^ f)) (hφ : L3Model π p f φ)
    (x : X ⧸ Subgroup.center X) (hx3 : orderOf x = 3)
    (hP : ∃ P : Sylow 3 (X ⧸ Subgroup.center X), x ∈ P ∧ ∀ y ∈ P, x * y = y * x) :
    IsThreeNilpotent ↥(Subgroup.centralizer ({x} : Set (X ⧸ Subgroup.center X))) := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  obtain ⟨P, -, hxc⟩ := hP
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  obtain ⟨g, hg, x₁, x₂, h₁, h₂, hle⟩ := l3b_sylow_heis hK hq hφ hτ hτ1 P
  obtain ⟨-, -, -, hcent, hlift⟩ := l3b_heis_data hK hq hφ hτ hτ1 hg h₁ h₂
    (E := Subgroup.zpowers (QuotientGroup.mk x₁ : X ⧸ Subgroup.center X) ⊔
      Subgroup.zpowers (QuotientGroup.mk x₂ : X ⧸ Subgroup.center X)) rfl
  have hxE := hcent x (fun e he => (hxc e (hle he)).symm)
  obtain ⟨xh, rfl, hxh3⟩ := hlift x hxE
  have hxhZ : xh ∉ Subgroup.center X := by
    intro h
    have : (QuotientGroup.mk xh : X ⧸ Subgroup.center X) = 1 := (QuotientGroup.eq_one_iff xh).2 h
    rw [this, orderOf_one] at hx3
    omega
  obtain ⟨g', hg', hgx'⟩ := hφ.exists_conj_diagTau hK hq hτ hτ1 hxhZ hxh3
  have : NeZero (qSubPi π (p ^ f)) := ⟨qSubPi_ne_zero hK hq⟩
  obtain ⟨e₀⟩ := centralizer_diagTau_mulEquiv hK hq hτ hτ1
  refine l3b_threeNilpotent xh ?_ ?_
  ·
    intro a ha b hb
    have hmem : ∀ c : X, c ∈ Subgroup.centralizer ({xh} : Set X) →
        g'⁻¹ * φ c * g' ∈ slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {diagTau hτ} := by
      intro c hc
      refine ⟨?_, ?_⟩
      · have := conj_mem_slPi hπ (inv_mem hg') (hφ.mem_sl c)
        rwa [inv_inv] at this
      · show g'⁻¹ * φ c * g' ∈ Subgroup.centralizer {diagTau hτ}
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hc1 : c * xh = xh * c := (Subgroup.mem_centralizer_singleton_iff.1 hc)
        have hd : diagTau hτ = g'⁻¹ * φ xh * g' := by rw [hgx']; group
        rw [hd]
        calc g'⁻¹ * φ c * g' * (g'⁻¹ * φ xh * g') = g'⁻¹ * φ (c * xh) * g' := by
              rw [map_mul]; group
          _ = g'⁻¹ * φ (xh * c) * g' := by rw [hc1]
          _ = g'⁻¹ * φ xh * g' * (g'⁻¹ * φ c * g') := by rw [map_mul]; group
    have h1 : e₀ (⟨_, hmem a ha⟩ * ⟨_, hmem b hb⟩) = e₀ (⟨_, hmem b hb⟩ * ⟨_, hmem a ha⟩) := by
      rw [map_mul, map_mul]; exact mul_comm _ _
    have h2 : g'⁻¹ * φ a * g' * (g'⁻¹ * φ b * g') = g'⁻¹ * φ b * g' * (g'⁻¹ * φ a * g') :=
      congrArg Subtype.val (e₀.injective h1)
    apply hφ.inj
    rw [map_mul, map_mul]
    have h3 : g'⁻¹ * (φ a * φ b) * g' = g'⁻¹ * (φ b * φ a) * g' := by
      calc g'⁻¹ * (φ a * φ b) * g' = g'⁻¹ * φ a * g' * (g'⁻¹ * φ b * g') := by group
        _ = g'⁻¹ * φ b * g' * (g'⁻¹ * φ a * g') := h2
        _ = g'⁻¹ * (φ b * φ a) * g' := by group
    exact mul_left_cancel (mul_right_cancel h3)
  ·
    set A := Subgroup.centralizer ({xh} : Set X) with hA
    set C := (Subgroup.centralizer ({(QuotientGroup.mk xh : X ⧸ Subgroup.center X)} :
      Set (X ⧸ Subgroup.center X))).comap (QuotientGroup.mk' (Subgroup.center X)) with hC
    have hAmap : A.map φ = slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {φ xh} := by
      ext s
      constructor
      · rintro ⟨a, ha, rfl⟩
        refine ⟨hφ.mem_sl a, ?_⟩
        show φ a ∈ Subgroup.centralizer {φ xh}
        rw [Subgroup.mem_centralizer_singleton_iff]
        have := Subgroup.mem_centralizer_singleton_iff.1 ha
        rw [← map_mul, ← map_mul, this]
      · rintro ⟨hs, hc⟩
        obtain ⟨a, rfl⟩ := hφ.exists_of_mem_sl hs
        refine ⟨a, ?_, rfl⟩
        show a ∈ Subgroup.centralizer {xh}
        rw [Subgroup.mem_centralizer_singleton_iff]
        apply hφ.inj
        rw [map_mul, map_mul]
        exact Subgroup.mem_centralizer_singleton_iff.1
          (show φ a ∈ Subgroup.centralizer {φ xh} from hc)
    have hCmap : C.map φ = centMod (slPi π 3 (p ^ f) K) (φ xh) := by
      ext s
      rw [mem_centMod_iff_scalar]
      constructor
      · rintro ⟨u, hu, rfl⟩
        obtain ⟨z, hz, hzu⟩ := (l3b_mem_cent_iff xh u).1 hu
        have hzs := (hφ.mem_center_iff hK hq z).1 hz
        refine ⟨hφ.mem_sl u, φ z, hzs, ?_⟩
        calc φ u * φ xh * (φ u)⁻¹ = φ (u * xh * u⁻¹) := by rw [map_mul, map_mul, map_inv]
          _ = φ (xh * z) := by rw [hzu]
          _ = φ z * φ xh := by
            rw [map_mul]; exact commute_of_mem_statedScalars hzs (φ xh)
      · rintro ⟨hs, z, hz, hzs⟩
        obtain ⟨u, rfl⟩ := hφ.exists_of_mem_sl hs
        have hzmem : z ∈ slPi π 3 (p ^ f) K := by
          have : z = φ u * φ xh * (φ u)⁻¹ * (φ xh)⁻¹ := by rw [hzs]; group
          rw [this]
          exact mul_mem (mul_mem (mul_mem hs (hφ.mem_sl xh)) (inv_mem hs))
            (inv_mem (hφ.mem_sl xh))
        obtain ⟨z₀, rfl⟩ := hφ.exists_of_mem_sl hzmem
        have hz₀ : z₀ ∈ Subgroup.center X := (hφ.mem_center_iff hK hq z₀).2 hz
        refine ⟨u, (l3b_mem_cent_iff xh u).2 ⟨z₀, hz₀, ?_⟩, rfl⟩
        apply hφ.inj
        rw [map_mul, map_mul, map_inv, hzs, map_mul]
        exact (commute_of_mem_statedScalars hz (φ xh)).symm
    rw [← Subgroup.relIndex_map_map_of_injective A C hφ.inj, hAmap, hCmap, hgx',
      ← map_conj_centralizer hπ hg' (diagTau hτ), ← map_conj_centMod hπ hg' (diagTau hτ),
      Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g').injective]
    exact relindex_centralizer_diagTau hK hq hτ hτ1

end CFSG.HardMathSupport.Solomon.Coordinator
