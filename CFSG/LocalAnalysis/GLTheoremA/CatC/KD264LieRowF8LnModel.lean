module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowF8LnCore
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowF8LnDesc
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowF8Pieces
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOutCycLinear
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagPSLn

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.F8Ln

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.ComponentClassification
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.LieType.SemisimpleCentralizers.HeldLang
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Transfer
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Std
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Final
  CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore

section Aux

theorem finite_mulAut' {P : Type*} [Group P] [Finite P] : Finite (MulAut P) :=
  Finite.of_injective (fun α : MulAut P => (α : P → P)) fun _ _ h => MulEquiv.ext (congrFun h)

theorem center_projectiveSL_eq_bot {N : ℕ} (hN : 3 ≤ N) {K : Type} [Field K] :
    Subgroup.center (projectiveSL N K) = ⊥ := by
  haveI : IsSimpleGroup (projectiveSL N K) :=
    CFSG.GH74.GLS.Stage2.Bender.Thm1.Ln.isSimpleGroup_projectiveSL hN
  exact center_eq_bot_of_simple_nonabelian
    (CFSG.GH74.GLS.Stage2.Bender.Thm1.Ln.exists_noncomm_projectiveSL hN)

theorem conj_injective' {P : Type*} [Group P] (hZ : Subgroup.center P = ⊥) :
    Function.Injective (MulAut.conj : P →* MulAut P) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hmem : x ∈ Subgroup.center P := by
    rw [Subgroup.mem_center_iff]
    intro z
    have h1 : x * z * x⁻¹ = z := by
      simpa [MulAut.conj_apply] using congrArg (fun φ : MulAut P => φ z) hx
    calc z * x = (x * z * x⁻¹) * x := by rw [h1]
      _ = x * z := by group
  rw [hZ] at hmem
  exact hmem

theorem mulAut_conj_conj {P : Type*} [Group P] (φ : MulAut P) (x : P) :
    φ * MulAut.conj x * φ⁻¹ = MulAut.conj (φ x) := by
  ext z
  simp [MulAut.conj_apply]

theorem mem_inner_of_pow_three {N : ℕ} (hN : 3 ≤ N) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 8) {a : MulAut (projectiveSL N K)}
    (ha : a ∈ innAutDerived (projectiveSL N K)) (ha3 : a ^ 3 = 1) :
    a ∈ (MulAut.conj : projectiveSL N K →* MulAut (projectiveSL N K)).range := by
  obtain ⟨X, rfl⟩ := (mem_linearAutGroup_iff).1
    (CFSG.HardMathSupport.Solomon.Coordinator.innAutDerived_le_linearAutGroup hN ha)
  have h1 : conjAut N K (X ^ 3) = 1 := by rw [map_pow]; exact ha3
  obtain ⟨u, hu⟩ := (conjAut_eq_one_iff hN _).1 h1
  have h7 : ∀ w : Kˣ, w ^ 7 = 1 := fun w => by
    have : Nat.card Kˣ = 7 := by rw [Nat.card_units, hK]
    rw [← this]
    exact pow_card_eq_one'
  have hd3 : (Matrix.GeneralLinearGroup.det X) ^ 3 = u ^ N := by
    rw [← map_pow, hu, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin]
  set d := Matrix.GeneralLinearGroup.det X with hd
  have hdμ : d = (u ^ 5) ^ N := by
    calc d = d ^ 15 := by
          have : d ^ 15 = (d ^ 7) ^ 2 * d := by group
          rw [this, h7, one_pow, one_mul]
      _ = (d ^ 3) ^ 5 := by rw [← pow_mul]
      _ = (u ^ 5) ^ N := by rw [hd3, ← pow_mul, ← pow_mul, mul_comm]
  let Z : GL (Fin N) K := Matrix.GeneralLinearGroup.scalar (Fin N) (u ^ 5)⁻¹ * X
  have hZdet : Matrix.GeneralLinearGroup.det Z = 1 := by
    rw [map_mul, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, ← hd, hdμ, inv_pow,
      inv_mul_cancel]
  let g : Matrix.SpecialLinearGroup (Fin N) K :=
    ⟨(Z : Matrix (Fin N) (Fin N) K), by
      rw [← Matrix.GeneralLinearGroup.val_det_apply, hZdet, Units.val_one]⟩
  have hg : Matrix.SpecialLinearGroup.toGL g = Z := Units.ext rfl
  refine ⟨proj N K g, ?_⟩
  rw [← conjAut_toGL_eq, hg]
  show conjAut N K Z = conjAut N K X
  rw [map_mul, conjAut_scalar, one_mul]

end Aux

section Model

variable {N : ℕ} {K : Type} [Field K] [Finite K]

theorem card_quotient_center_of_equiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    Nat.card (A ⧸ Subgroup.center A) = Nat.card (B ⧸ Subgroup.center B) :=
  Nat.card_congr (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).toEquiv

theorem card_eq_pow_pRank {G : Type*} [Group G] [Finite G] {E : Subgroup G}
    (hE : IsElemAbelian 3 E) : Nat.card E = 3 ^ CFSG.Open.pRank 3 E := by
  obtain ⟨k, hk⟩ := card_eq_pow_three hE
  rw [hk, pRank_eq_of_card' Nat.prime_three hE hk]

theorem kerLn_model (hN : 4 ≤ N) (hK : Nat.card K = 8)
    (A : Subgroup (MulAut (projectiveSL N K))) (hA : IsElemAbelian 3 A)
    (hout : ∀ a ∈ A, a ∉ (MulAut.conj : projectiveSL N K →* MulAut (projectiveSL N K)).range →
      ∀ E : Subgroup (projectiveSL N K), E ≤ fixSubgroup a → IsElemAbelian 3 E →
        CFSG.Open.pRank 3 E + 1 ≤ CFSG.Open.pRank 3 A)
    (hnot : ¬ A ≤ innAutDerived (projectiveSL N K)) :
    KD264F8Datum (projectiveSL N K) A := by
  classical
  have hN3 : 3 ≤ N := by omega
  haveI := finite_mulAut' (P := projectiveSL N K)
  obtain ⟨b, hbA, hbout⟩ := SetLike.not_le_iff_exists.1 hnot
  have hb3 : b ^ 3 = 1 := hA.2 b hbA
  obtain ⟨ι, hιinj, hιfix, hιnorm, hι3⟩ := exists_descent hN3 hK b hb3 hbout
  have hZ := center_projectiveSL_eq_bot (K := K) hN3
  have hconjinj := conj_injective' hZ
  have hbnotinn : b ∉ (MulAut.conj : projectiveSL N K →* MulAut (projectiveSL N K)).range :=
    fun h => hbout (inner_le_innAutDerived _ h)
  obtain ⟨E0, hE0, hE0card⟩ := exists_elemAb_card (Fin N → ZMod 2) N (Module.finrank_fin_fun _)
  have hbound : N / 2 + 1 ≤ CFSG.Open.pRank 3 A := by
    have hE0ab : IsElemAbelian 3 (E0.map ι) := isElemAbelian_map_gen ι hE0
    have hc : Nat.card (E0.map ι) = 3 ^ (N / 2) := by
      rw [Subgroup.card_map_of_injective hιinj, hE0card]
    have h1 := hout b hbA hbnotinn (E0.map ι) (by
      rintro _ ⟨v, -, rfl⟩
      exact mem_fixSubgroup.2 (hιfix v)) hE0ab
    rwa [pRank_eq_of_card' Nat.prime_three hE0ab hc] at h1
  have hAcard := card_eq_pow_pRank hA
  have hout3 := outCycAt_projectiveSL (K := K) hN3 Nat.prime_three (by norm_num) A hA
  have hA0inn : A ⊓ innAutDerived (projectiveSL N K) ≤
      (MulAut.conj : projectiveSL N K →* MulAut (projectiveSL N K)).range :=
    fun a ha => mem_inner_of_pow_three hN3 hK ha.2 (hA.2 a ha.1)
  let Ebar : Subgroup (projectiveSL N K) :=
    A.comap (MulAut.conj : projectiveSL N K →* MulAut (projectiveSL N K))
  have hEbar_map : Ebar.map (MulAut.conj : projectiveSL N K →* MulAut (projectiveSL N K)) =
      (MulAut.conj : projectiveSL N K →* MulAut (projectiveSL N K)).range ⊓ A :=
    Subgroup.map_comap_eq _ _
  have hA0le : A ⊓ innAutDerived (projectiveSL N K) ≤
      Ebar.map (MulAut.conj : projectiveSL N K →* MulAut (projectiveSL N K)) := by
    rw [hEbar_map]
    exact le_inf hA0inn inf_le_left
  have hcardEbar : 3 ^ (N / 2) ≤ Nat.card Ebar := by
    have h1 := Subgroup.card_le_of_le hA0le
    rw [Subgroup.card_map_of_injective hconjinj] at h1
    have h2 : 3 ^ (N / 2 + 1) ≤ Nat.card A := by
      rw [hAcard]
      exact Nat.pow_le_pow_right (by norm_num) hbound
    have h3 : 3 ^ (N / 2) * 3 ≤ 3 * Nat.card Ebar := by
      calc 3 ^ (N / 2) * 3 = 3 ^ (N / 2 + 1) := by ring
        _ ≤ Nat.card A := h2
        _ ≤ 3 * Nat.card ↥(A ⊓ innAutDerived (projectiveSL N K)) := hout3
        _ ≤ 3 * Nat.card Ebar := Nat.mul_le_mul_left _ h1
    omega
  have hEbar_ab : IsElemAbelian 3 Ebar := by
    refine isElemAbelian_of_map_injective _ hconjinj ?_
    exact isElemAbelian_of_le (by rw [hEbar_map]; exact inf_le_right) hA
  have hEbar_fix : ∀ x ∈ Ebar, b x = x := by
    intro x hx
    have hcomm : Commute b (MulAut.conj x) := kd264F8_commute hA hbA hx
    have h1 : MulAut.conj (b x) = MulAut.conj x := by
      rw [← mulAut_conj_conj, hcomm.eq]
      group
    exact hconjinj h1
  have hEbar_ι : Ebar ≤ ι.range := by
    intro x hx
    have hx3 : x ^ 3 = 1 := by
      apply hconjinj
      rw [map_pow, map_one]
      exact hA.2 _ hx
    exact hι3 x (hEbar_fix x hx) hx3
  let Et : Subgroup (VecAut N) := Ebar.comap ι
  have hEt_map : Et.map ι = Ebar := Subgroup.map_comap_eq_self hEbar_ι
  have hEt_card : 3 ^ (N / 2) ≤ Nat.card Et := by
    rw [← Subgroup.card_map_of_injective (K := Et) hιinj, hEt_map]
    exact hcardEbar
  have hEt_ab : IsElemAbelian 3 Et :=
    isElemAbelian_of_map_injective ι hιinj (by rw [hEt_map]; exact hEbar_ab)
  obtain ⟨ct, hctE, hct1, L, hLc, hLn, hLq, hLd⟩ :=
    core_c (V := Fin N → ZMod 2) (Module.finrank_fin_fun _) hN Et hEt_ab hEt_card
  set x : projectiveSL N K := ι ct with hx
  have hxE : x ∈ Ebar := by
    have : ι ct ∈ Et.map ι := Subgroup.mem_map_of_mem ι hctE
    rwa [hEt_map] at this
  have hcA : MulAut.conj x ∈ A := hxE
  have hfixc : ∀ g, g ∈ Subgroup.centralizer ({ct} : Set (VecAut N)) →
      MulAut.conj x (ι g) = ι g := by
    intro g hg
    have h1 : ct * g = g * ct := Subgroup.mem_centralizer_iff.1 hg ct (Set.mem_singleton _)
    have h2 : ct * g * ct⁻¹ = g := by rw [h1]; group
    rw [MulAut.conj_apply, hx, ← map_inv, ← map_mul, ← map_mul, h2]
  set M : Subgroup (projectiveSL N K) := (Subgroup.centralizer ({ct} : Set (VecAut N))).map ι
    with hM
  have hMb : M ≤ fixSubgroup b := by
    rintro _ ⟨g, -, rfl⟩
    exact mem_fixSubgroup.2 (hιfix g)
  have hMc : M ≤ fixSubgroup (MulAut.conj x) := by
    rintro _ ⟨g, hg, rfl⟩
    exact mem_fixSubgroup.2 (hfixc g hg)
  have hMT := kd264F8_le_fixSubgroup_iInf hMb hMc
  refine ⟨b, hbA, MulAut.conj x, hcA, hbout, inner_le_innAutDerived _ ⟨x, rfl⟩, ?_, L.map ι,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    apply hct1
    apply hιinj
    rw [map_one]
    exact hconjinj (h.trans (map_one _).symm)
  · rintro _ ⟨l, hl, rfl⟩
    exact mem_fixSubgroup.2 (hιfix l)
  · rintro _ ⟨l, hl, rfl⟩
    exact mem_fixSubgroup.2 (hfixc l (hLc hl))
  ·
    have hHM : L.map ι ≤ M := Subgroup.map_mono hLc
    have hHMn : ((L.map ι).subgroupOf M).Normal := by
      constructor
      intro n hn g
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      obtain ⟨l, hl, hln⟩ := hn
      obtain ⟨g₀, hg₀, hgg⟩ := g.2
      have hmem := hLn.conj_mem ⟨l, hLc hl⟩ (Subgroup.mem_subgroupOf.2 hl) ⟨g₀, hg₀⟩
      rw [Subgroup.mem_subgroupOf] at hmem
      refine ⟨g₀ * l * g₀⁻¹, hmem, ?_⟩
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hgg, ← hln]
      simp
    have hMTn : (M.subgroupOf (⨅ f ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers (MulAut.conj x),
        fixSubgroup f)).Normal := by
      constructor
      intro n hn t
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      obtain ⟨g, hg, hgn⟩ := hn
      have ht := t.2
      have htb : b (t : projectiveSL N K) = t := by
        have := Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 ht b)
          (Subgroup.mem_sup_left (Subgroup.mem_zpowers b))
        exact mem_fixSubgroup.1 this
      have htc : MulAut.conj x (t : projectiveSL N K) = t := by
        have := Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 ht (MulAut.conj x))
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
        exact mem_fixSubgroup.1 this
      obtain ⟨v, hv⟩ := hιnorm t htb g
      have hvc : v ∈ Subgroup.centralizer ({ct} : Set (VecAut N)) := by
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        rw [hh]
        apply hιinj
        have h1 : MulAut.conj x (ι v) = ι v := by
          rw [hv, map_mul, map_mul, map_inv, htc, hfixc g hg]
        rw [MulAut.conj_apply, hx] at h1
        rw [map_mul, map_mul]
        have h2 : ι ct * ι v * (ι ct)⁻¹ = ι v := h1
        calc ι ct * ι v = ι ct * ι v * (ι ct)⁻¹ * ι ct := by group
          _ = ι v * ι ct := by rw [h2]
      refine ⟨v, hvc, ?_⟩
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hgn, ← hv]
    exact CFSG.Open.IsSubnormal.step hHM hHMn
      (CFSG.Open.IsSubnormal.step hMT hMTn (CFSG.Open.IsSubnormal.refl _))
  · exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
      (L.equivMapOfInjective ι hιinj) hLq
  · rw [← card_quotient_center_of_equiv (L.equivMapOfInjective ι hιinj)]
    exact hLd

end Model

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.F8Ln

end
