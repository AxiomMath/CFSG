module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHighD4Three2

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHigh3

section G2Frame

set_option linter.unusedSectionVars false

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.CTP
  CFSG.HardMathSupport.Lang.D4Three CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.SeitzGeneration.ExcWideThree
  CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph
  CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator CFSG.HardMathSupport.Seitz.Proving
  CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2Nonsplit
open scoped commutatorElement

local notation "𝕩" => xPar (rootOperatorFamily Tag.D4)

variable {K : Type} [Field K]

theorem frameK_mem_of_frameDiag [Finite K] (hK4 : 4 ≤ Nat.card K) {B : SL2 K}
    (hB : B ∉ Subgroup.center (SL2 K))
    (hwit : ∃ C : SL2 K,
      ⁅B * (C * B * C⁻¹), B⁻¹ * (C * B⁻¹ * C⁻¹)⁆ ∉ Subgroup.center (SL2 K))
    {M : Subgroup ↥(adjointGroup Tag.D4 K)} (hΔ : ∀ C, frameDiag C ∈ M)
    (hd : frameD K B ∈ M) (A : SL2 K) :
    frameK₁ K A ∈ M ∧ frameK₃ K A ∈ M ∧ frameK₂ K A ∈ M := by
  set f := (frameK₂ K).noncommCoprod (frameK₃ K)
    (fun X Y => ((frameK_commute (K := K) Y X).2.2).symm) with hf
  have hfapp : ∀ p : SL2 K × SL2 K, f p = frameK₂ K p.1 * frameK₃ K p.2 := fun p => rfl
  set L := M.comap f with hL
  have hLn : ∀ C : SL2 K, ∀ p ∈ L, ((C, C) : SL2 K × SL2 K) * p * (C, C)⁻¹ ∈ L := by
    intro C p hp
    have hp' : frameK₂ K p.1 * frameK₃ K p.2 ∈ M := by rw [← hfapp]; exact hp
    show f _ ∈ M
    rw [hfapp]
    simp only [Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv]
    rw [← frameDiag_conj_frameK₂, ← frameDiag_conj_frameK₃,
      show frameDiag C * frameK₂ K p.1 * (frameDiag C)⁻¹ *
          (frameDiag C * frameK₃ K p.2 * (frameDiag C)⁻¹) =
        frameDiag C * (frameK₂ K p.1 * frameK₃ K p.2) * (frameDiag C)⁻¹ by group]
    exact M.mul_mem (M.mul_mem (hΔ C) hp') (M.inv_mem (hΔ C))
  have hBL : ((B, B⁻¹) : SL2 K × SL2 K) ∈ L := by
    show f _ ∈ M
    rw [hfapp, map_inv]
    exact hd
  have h2 : ∀ X, frameK₂ K X ∈ M := by
    intro X
    have h := twistDiag hK4 hB hwit L hLn hBL X
    have h' : f (X, 1) ∈ M := h
    rwa [hfapp, map_one, mul_one] at h'
  have h3 : ∀ Y, frameK₃ K Y ∈ M := by
    set N := M.comap (frameK₃ K) with hN
    have hNn : N.Normal := ⟨fun y hy C => by
      show frameK₃ K (C * y * C⁻¹) ∈ M
      rw [← frameDiag_conj_frameK₃]
      exact M.mul_mem (M.mul_mem (hΔ C) hy) (M.inv_mem (hΔ C))⟩
    have hBN : B⁻¹ ∈ N := by
      show frameK₃ K B⁻¹ ∈ M
      have e : frameK₃ K B⁻¹ = (frameK₂ K B)⁻¹ * frameD K B := by
        rw [frameD, map_inv, inv_mul_cancel_left]
      rw [e]
      exact M.mul_mem (M.inv_mem (h2 B)) hd
    have hBZ : B⁻¹ ∉ Subgroup.center (SL2 K) := fun h => hB (by
      simpa using (Subgroup.center (SL2 K)).inv_mem h)
    have htop := eq_top_of_normal_of_not_le_center hK4 N hBN hBZ
    intro Y
    show Y ∈ N
    rw [htop]
    trivial
  refine ⟨?_, h3 A, h2 A⟩
  have e : frameK₁ K A = frameDiag A * (frameK₂ K A)⁻¹ * (frameK₃ K A)⁻¹ := by
    rw [frameDiag]
    group
  rw [e]
  exact M.mul_mem (M.mul_mem (hΔ A) (M.inv_mem (h2 A))) (M.inv_mem (h3 A))

theorem closure_fixedSubgroup_d4Graph_frameD [Finite K] (hK4 : 4 ≤ Nat.card K) :
    Subgroup.closure ((fixedSubgroup (d4Graph K 1) : Set ↥(adjointGroup Tag.D4 K)) ∪
      {frameD K (orderThreeSL K)}) = ⊤ := by
  set M := Subgroup.closure ((fixedSubgroup (d4Graph K 1) : Set ↥(adjointGroup Tag.D4 K)) ∪
    {frameD K (orderThreeSL K)}) with hM
  have hγ : ∀ g, d4Graph K 1 g = g → g ∈ M := fun g hg => Subgroup.subset_closure (Or.inl hg)
  have hΔ : ∀ C, frameDiag C ∈ M := fun C => hγ _ (d4Graph_frameDiag C)
  have hd : frameD K (orderThreeSL K) ∈ M := Subgroup.subset_closure (Or.inr rfl)
  have hfr := frameK_mem_of_frameDiag hK4 orderThreeSL_not_mem_center
    (exists_witness_orderThreeSL hK4) hΔ hd
  have hβ : ∀ β ∈ longOrthRoots, ∀ c, 𝕩 β c ∈ M ∧ 𝕩 (-β) c ∈ M := by
    intro β hβl c
    rw [longOrthRoots_eq] at hβl
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hβl
    rcases hβl with rfl | rfl | rfl
    · exact isFrameHom_frameK₁.xPar_mem (fun A => (hfr A).1) c
    · exact isFrameHom_frameK₂.xPar_mem (fun A => (hfr A).2.2) c
    · exact isFrameHom_frameK₃.xPar_mem (fun A => (hfr A).2.1) c
  have hn : weylG2 ∈ M := hγ _ d4Graph_one_weylG2
  refine eq_top_of_simple_mem fun i c => ?_
  by_cases hi : i = ⟨2, by decide⟩
  · subst hi
    exact ⟨hγ _ (d4Graph_one_xPar_two c).1, hγ _ (d4Graph_one_xPar_two c).2⟩
  · obtain ⟨β, hβl, hpos, hneg⟩ := longOrth_reflect i hi
    obtain ⟨hβr, hβr', -⟩ := longOrth_facts β hβl
    obtain ⟨ε, hε, hc⟩ := exists_weylG2_conj (K := K) hβr
    obtain ⟨ε', hε', hc'⟩ := exists_weylG2_conj (K := K) hβr'
    rw [hpos] at hc
    rw [hneg] at hc'
    exact ⟨mem_of_conj_eq hn hε hc (fun c => (hβ β hβl c).1) c,
      mem_of_conj_eq hn hε' hc' (fun c => (hβ β hβl c).2) c⟩

end G2Frame

section G2Sylow

set_option linter.unusedSectionVars false

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.CTP
  CFSG.HardMathSupport.Lang.D4Three CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator CFSG.HardMathSupport.Seitz.Proving
  CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2Nonsplit

theorem mul_yP_one_not_diag {L : Type} [Field L] [Finite L] {ω : Lˣ} (hω : orderOf ω = 3)
    {r : ↥(adjointGroup Tag.D4 L)} {x z : Lˣ}
    (hr : (r : ModGL Tag.D4 L) = rootDiagUnit Tag.D4 (tupXZ x z)) {b : Fin Tag.D4.rank → Lˣ}
    (hb : ((r * yP (one_pow_three_units (K := L)) : ↥(adjointGroup Tag.D4 L)) :
      ModGL Tag.D4 L) = rootDiagUnit Tag.D4 b) : False := by
  refine yP_one_pow_not_diag hω (k := 1) (Or.inl rfl) (a := (tupXZ x z)⁻¹ * b) ?_
  rw [pow_one, show yP (one_pow_three_units (K := L)) =
      r⁻¹ * (r * yP (one_pow_three_units (K := L))) by group, Subgroup.coe_mul, Subgroup.coe_inv,
    hb, hr, rootDiagUnit_inv, ← rootDiagUnit_mul]

theorem ιTw_d4Graph {K K₂ : Type} [Field K] [Field K₂] [Algebra K K₂] (Q : SL2 K₂)
    (h : ↥(adjointGroup Tag.D4 K)) :
    ιTw K Q (d4Graph K 1 h) = d4Graph K₂ 1 (ιTw K Q h) := by
  have hg : d4Graph K₂ 1 (gTw Q) = gTw Q := d4Graph_gTw Q
  rw [ιTw_apply, ιTw_apply, bcAd_d4Graph, map_mul, map_mul, map_inv, hg]

theorem exists_sylow_frameD_gamma_of_ext {K : Type} [Field K] [Finite K]
    (hq : Nat.card K % 3 = 2) (hK4 : 4 ≤ Nat.card K) {K₂ : Type} [Field K₂] [Finite K₂]
    [Algebra K K₂] (hcard : Nat.card K₂ = Nat.card K ^ 2) (σ : K₂ →+* K₂)
    (hσ : ∀ x, σ x = x ^ Nat.card K) :
    ∃ P : Subgroup ↥(adjointGroup Tag.D4 K), P ≤ fixedSubgroup (d4Graph K 1) ∧
      IsPGroup 3 P ∧ (∀ y ∈ P, y * frameD K (orderThreeSL K) = frameD K (orderThreeSL K) * y) ∧
      ∀ R : Subgroup ↥(adjointGroup Tag.D4 K), IsPGroup 3 R →
        R ≤ fixedSubgroup (d4Graph K 1) → Nat.card R ≤ Nat.card P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, ω, c₀, hQ, hω, -, hQc, hc₀⟩ := exists_twist_data hq hcard hσ
  have h1 : (1 : K₂ˣ) ^ 3 = 1 := one_pow 3
  have hK₂ : Nat.card K₂ % 3 = 1 := by rw [hcard]; exact sq_mod_three hq
  have hK₂4 : 4 ≤ Nat.card K₂ := by rw [hcard]; nlinarith
  obtain ⟨ζ, hζ⟩ := exists_orderOf_eq_three_pow (K := K₂)
  set e := (Nat.card K₂ - 1).factorization 3 with he
  set μ := Subgroup.zpowers ζ with hμ
  have hμsq : ∀ u ∈ μ, ∃ b : K₂ˣ, u = b ^ 2 := mu_sq (Odd.pow (by decide : Odd 3)) hζ
  have hcardμ : Nat.card μ = 3 ^ e := by rw [hμ, Nat.card_zpowers, hζ]
  have hζq : ζ ^ (Nat.card K + 1) = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hζ]
    have hdvd : 3 ^ e ∣ (Nat.card K - 1) * (Nat.card K + 1) := by
      have h1 : 3 ^ e ∣ Nat.card K₂ - 1 := Nat.ordProj_dvd _ _
      have h2 : Nat.card K₂ - 1 = (Nat.card K - 1) * (Nat.card K + 1) := by
        rw [hcard]
        obtain ⟨m, hm⟩ : ∃ m, Nat.card K = m + 1 := ⟨Nat.card K - 1, by
          have := Nat.card_pos (α := K); omega⟩
        rw [hm, Nat.add_sub_cancel]
        have : (m + 1) ^ 2 = m * (m + 1 + 1) + 1 := by ring
        omega
      rwa [h2] at h1
    have hcop : Nat.Coprime (3 ^ e) (Nat.card K - 1) := by
      apply Nat.Coprime.pow_left
      rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
      omega
    exact hcop.dvd_of_dvd_mul_left hdvd
  have hμq : ∀ u ∈ μ, u ^ (Nat.card K + 1) = 1 := by
    intro u hu
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζq, one_zpow]
  have hμσ : ∀ u ∈ μ, Units.map σ.toMonoidHom u = u⁻¹ := by
    intro u hu
    rw [units_frob hσ]
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hμq u hu)
  have hζe : ζ ^ 3 ^ e = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  have hμ3 : ∀ u ∈ μ, u ^ 3 ^ e = 1 := by
    intro u hu
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζe, one_zpow]
  have hT3ι : T3fix (ω := 1) (K := K₂) μ ≤ (ιTw K Q).range := by
    rintro t ⟨⟨a, ha, hta⟩, -⟩
    have hσt : bcAd σ t = t⁻¹ := by
      apply Subtype.ext
      rw [coe_bcAd_of_eq_rootDiagUnit σ hta, Subgroup.coe_inv, hta, rootDiagUnit_inv]
      congr 1
      funext j
      rw [Pi.inv_apply, hμσ _ (ha j)]
    have htinv : ((t⁻¹ : ↥(adjointGroup Tag.D4 K₂)) : ModGL Tag.D4 K₂) =
        rootDiagUnit Tag.D4 a⁻¹ := by
      rw [Subgroup.coe_inv, hta, rootDiagUnit_inv]
    refine mem_range_ιTw_of_fixed σ hσ hQc (k := e) ?_ ?_
    · rw [hσt, gTw_nSL_conj_diag c₀ htinv, inv_inv]
    · apply Subtype.ext
      rw [Subgroup.coe_pow, hta, ← rootDiagUnit_pow_D4, Subgroup.coe_one, ← rootDiagUnit_one]
      congr 1
      funext j
      rw [Pi.pow_apply, Pi.one_apply, hμ3 _ (ha j)]
  obtain ⟨r, a₁, a₂, hr, hcr⟩ := exists_cocyc_eq_mul_bcAd hcard Nat.card_pos σ hσ hc₀
  have hπ3 : (r * yP h1) ^ 3 = 1 := mul_yP_pow_three h1 hr
  have hπnd : r * yP h1 ∉ T3fix (ω := 1) (K := K₂) μ := by
    rintro ⟨⟨b, -, hb⟩, -⟩
    exact mul_yP_one_not_diag hω hr hb
  have hπ1 : r * yP h1 ≠ 1 := by
    intro h1
    apply hπnd
    rw [h1]
    exact Subgroup.one_mem _
  have hπord : orderOf (r * yP h1) = 3 := orderOf_eq_prime hπ3 hπ1
  have hπι : r * yP h1 ∈ (ιTw K Q).range :=
    mem_range_ιTw_of_fixed σ hσ hQc (fixed_mul_yP h1 (by simp) hr hcr) (k := 1)
      (by rw [pow_one]; exact hπ3)
  set P' := T3fix (ω := 1) (K := K₂) μ ⊔ Subgroup.zpowers (r * yP h1) with hP'
  have hcardP' : Nat.card P' = Nat.card (T3fix (ω := 1) (K := K₂) μ) * 3 := by
    rw [hP', card_sup_of_le_normalizer
      ((Subgroup.zpowers_le).2 (mul_yP_mem_normalizer_T3fix h1 μ hr))
      (inf_zpowers_eq_bot_of_pow_three hπ3 hπnd), Nat.card_zpowers, hπord]
  have hP'ge : 3 * Nat.card μ ^ 2 ≤ Nat.card P' := by
    rw [hcardP', mul_comm 3]
    exact Nat.mul_le_mul_right 3 (card_T3fix_ge (ω := 1) μ hμsq)
  have hP'p : IsPGroup 3 P' := by
    have hdvdT : Nat.card (T3fix (ω := 1) (K := K₂) μ) ∣ 3 ^ (4 * e) := by
      have h := Subgroup.card_dvd_of_le
        (inf_le_left : T3fix (ω := 1) (K := K₂) μ ≤ torusSub μ)
      rwa [card_torusSub μ hμsq, hcardμ, ← pow_mul, mul_comm e 4] at h
    refine IsPGroup.of_card_dvd_pow (n := 4 * e + 1) ?_
    rw [hcardP', pow_succ]
    exact Nat.mul_dvd_mul_right hdvdT 3
  have hP'ι : P' ≤ (ιTw K Q).range := sup_le hT3ι ((Subgroup.zpowers_le).2 hπι)
  have hP'α : P' ≤ fixedSubgroup (gammaP K₂ (HSL (1 : K₂ˣ))) :=
    sup_le inf_le_right ((Subgroup.zpowers_le).2 (gammaP_HSL_mul_yP h1 hr))
  have hP'd : P' ≤ Subgroup.centralizer
      ({torusElement Tag.D4 K₂ ⟨0, by decide⟩ ω * torusElement Tag.D4 K₂ ⟨1, by decide⟩ ω⁻¹} :
        Set ↥(adjointGroup Tag.D4 K₂)) := by
    refine sup_le ?_ ((Subgroup.zpowers_le).2 ?_)
    · rintro y ⟨⟨a, -, hya⟩, -⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact commute_of_diag hya (coe_dTorus ω)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact mul_yP_commute_dTorus h1 hr ω
  set P := P'.comap (ιTw K Q) with hP
  have hιinj : Function.Injective (ιTw K Q) := ιTw_injective Q
  have hcardP : Nat.card P = Nat.card P' := by
    rw [← Subgroup.card_map_of_injective hιinj, hP, Subgroup.map_comap_eq_self hP'ι]
  have hPp : IsPGroup 3 P := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hP'p
    exact IsPGroup.of_card (n := n) (by rw [hcardP, hn])
  have hPC : P ≤ fixedSubgroup (d4Graph K 1) := by
    intro y hy
    show d4Graph K 1 y = y
    apply hιinj
    rw [ιTw_d4Graph Q y, ← gammaP_HSL_one]
    exact hP'α hy
  have hPd : ∀ y ∈ P, Commute y (frameD K (orderThreeSL K)) := by
    intro y hy
    show y * frameD K (orderThreeSL K) = frameD K (orderThreeSL K) * y
    apply hιinj
    rw [map_mul, map_mul, ιTw_frameD hQ]
    exact Subgroup.mem_centralizer_singleton_iff.1 (hP'd hy)
  have hmax : ∀ R : Subgroup ↥(adjointGroup Tag.D4 K), IsPGroup 3 R →
      R ≤ fixedSubgroup (d4Graph K 1) → Nat.card R ≤ Nat.card P := by
    intro R hR hRC
    have h := card_le_of_isPGroup_fixed_gamma hK₂ hK₂4 hω hζ (hR.map (ιTw K Q)) ?_
    · rw [Subgroup.card_map_of_injective hιinj] at h
      rw [hcardP]
      exact h.trans hP'ge
    · rintro y ⟨z, hz, rfl⟩
      rw [gammaP_HSL_one, ← ιTw_d4Graph Q z, show d4Graph K 1 z = z from hRC hz]
  exact ⟨P, hPC, hPp, fun y hy => (hPd y hy).eq, hmax⟩

theorem sylowPairGenAt_d4Graph_nonsplit {K : Type} [Field K] [Finite K]
    (hq : Nat.card K % 3 = 2) (hK4 : 4 ≤ Nat.card K) : SylowPairGenAt (d4Graph K 1) := by
  have : Finite (ModGL Tag.D4 K) := finite_modGL
  have : Finite ↥(adjointGroup Tag.D4 K) := Subtype.finite
  have := Fintype.ofFinite K
  obtain ⟨n, hp, -⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hp⟩
  obtain ⟨P, hPC, hPp, hPd, hmax⟩ := exists_sylow_frameD_gamma_of_ext hq hK4
    (FiniteField.natCard_extension K (ringChar K) 2)
    (FiniteField.Extension.frob K (ringChar K) 2).toRingEquiv.toRingHom
    (fun y => FiniteField.Extension.frob_apply K (ringChar K) 2)
  exact sylowPairGenAt_of_sylow_central hPC hPp hmax hPd
    (closure_fixedSubgroup_d4Graph_frameD hK4)

theorem d4GraphG2SylowPairNonsplit_holds : D4GraphG2SylowPairNonsplit := by
  intro K _ _ hq hK5
  exact sylowPairGenAt_d4Graph_nonsplit hq (by omega)

end G2Sylow

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHigh3

end
