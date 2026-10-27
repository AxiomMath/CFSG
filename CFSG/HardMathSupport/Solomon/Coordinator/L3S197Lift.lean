module

public import CFSG.HardMathSupport.Solomon.LocalBalance.AutL3Struct

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ClassicalGroups.UnitaryFlag
  CFSG.Assembly.LowTwoRank CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.AutL3

section Alg

theorem comm_of_central_lift {Γ E : Type*} [Group Γ] [Group E] (φ : Γ →* E)
    (hker : φ.ker ≤ Subgroup.center Γ)
    (hEc : ∀ a b : E, a * b = b * a) (hE3 : ∀ a : E, a ^ 3 = 1) (hE9 : Nat.card E = 9) (x : Γ)
    (hx : x ∈ Subgroup.center Γ) (hx1 : φ x ≠ 1) (a b : Γ) : a * b = b * a := by
  let _ : CommGroup E := { (inferInstance : Group E) with mul_comm := hEc }
  set H : Subgroup E := Subgroup.zpowers (φ x) with hH
  have hH3 : Nat.card H = 3 := by
    rw [hH, Nat.card_zpowers]
    exact orderOf_eq_prime (hE3 _) hx1
  have hQ : Nat.card (E ⧸ H) = 3 := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup H
    rw [hE9, hH3] at this
    omega
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : IsCyclic (E ⧸ H) := isCyclic_of_prime_card hQ
  set ψ : Γ →* E ⧸ H := (QuotientGroup.mk' H).comp φ
  have hψk : ψ.ker ≤ Subgroup.center Γ := by
    intro g hg
    have h1 : φ g ∈ H := (QuotientGroup.eq_one_iff _).1 hg
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h1
    have h2 : g * (x ^ k)⁻¹ ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_zpow, hk, mul_inv_cancel]
    have h3 := hker h2
    have h4 : x ^ k ∈ Subgroup.center Γ := zpow_mem hx k
    have := mul_mem h3 h4
    rwa [inv_mul_cancel_right] at this
  exact (ψ.isMulCommutative_of_isCyclic_of_ker_le_center hψk).is_comm.comm a b

end Alg

section Lift

variable {π : Bool} {p f : ℕ} {K : Type} [Field K]

@[expose] noncomputable def cj (hK : PiField π p f K) {g : GL (Fin 3) K}
    (hg : g ∈ glPi π 3 (p ^ f) K) : MulAut ↥(slPi π 3 (p ^ f) K) :=
  (conjSL' (fun h => by subst h; exact hK.unitary) hg).symm

theorem coe_cj (hK : PiField π p f K) {g : GL (Fin 3) K} (hg : g ∈ glPi π 3 (p ^ f) K)
    (s : ↥(slPi π 3 (p ^ f) K)) : ((cj hK hg s : ↥(slPi π 3 (p ^ f) K)) : GL (Fin 3) K) =
      g * s * g⁻¹ := rfl

@[expose] noncomputable def cjHom (hK : PiField π p f K) :
    ↥(glPi π 3 (p ^ f) K) →* MulAut ↥(slPi π 3 (p ^ f) K) where
  toFun g := cj hK g.2
  map_one' := MulEquiv.ext fun s => Subtype.ext (by
    show (1 : GL (Fin 3) K) * s * (1 : GL (Fin 3) K)⁻¹ = s
    group)
  map_mul' g h := MulEquiv.ext fun s => Subtype.ext (by
    show ((g * h : ↥(glPi π 3 (p ^ f) K)) : GL (Fin 3) K) * s *
      ((g * h : ↥(glPi π 3 (p ^ f) K)) : GL (Fin 3) K)⁻¹ =
        (g : GL (Fin 3) K) * ((h : GL (Fin 3) K) * s * (h : GL (Fin 3) K)⁻¹) *
          (g : GL (Fin 3) K)⁻¹
    simp only [Subgroup.coe_mul]
    group)

theorem cjHom_apply (hK : PiField π p f K) (g : ↥(glPi π 3 (p ^ f) K)) :
    cjHom hK g = cj hK g.2 := rfl

@[expose] noncomputable def lam (hK : PiField π p f K) {M : Type*} [Group M]
    (η : (↥(slPi π 3 (p ^ f) K) ⧸ Subgroup.center ↥(slPi π 3 (p ^ f) K)) ≃* M) :
    ↥(glPi π 3 (p ^ f) K) →* MulAut M :=
  (MulAut.congr η).toMonoidHom.comp ((centerDescend _).comp (cjHom hK))

theorem lam_apply (hK : PiField π p f K) {M : Type*} [Group M]
    (η : (↥(slPi π 3 (p ^ f) K) ⧸ Subgroup.center ↥(slPi π 3 (p ^ f) K)) ≃* M)
    (g : ↥(glPi π 3 (p ^ f) K)) :
    lam hK η g = MulAut.congr η (centerDescend _ (cj hK g.2)) := rfl

theorem scalar_of_lam_eq_one (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (hq2 : π = false → 2 < p ^ f) {M : Type*} [Group M]
    (η : (↥(slPi π 3 (p ^ f) K) ⧸ Subgroup.center ↥(slPi π 3 (p ^ f) K)) ≃* M)
    {g : ↥(glPi π 3 (p ^ f) K)} (h : lam hK η g = 1) :
    (g : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K := by
  have hGq : CFSG.Open.IsQuasisimple ↥(slPi π 3 (p ^ f) K) :=
    isQuasisimple_slPi hK (fun hf => by have := hq2 hf; omega)
  have h1 : centerDescend _ (cj hK g.2) = 1 :=
    (MulAut.congr η).injective (by rw [← lam_apply, h, map_one])
  have h2 : cj hK g.2 = 1 := eq_one_of_centerDescend_eq_one hGq h1
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  refine mem_statedScalars_of_commute hπ hq' hτ hτ1 fun s hs => ?_
  have h3 := congrArg (fun z : MulAut ↥(slPi π 3 (p ^ f) K) => ((z ⟨s, hs⟩ :
    ↥(slPi π 3 (p ^ f) K)) : GL (Fin 3) K)) h2
  simp only [coe_cj] at h3
  change (g : GL (Fin 3) K) * s * (g : GL (Fin 3) K)⁻¹ = s at h3
  set G0 : GL (Fin 3) K := (g : GL (Fin 3) K) with hG0
  calc G0 * s = (G0 * s * G0⁻¹) * G0 := by group
    _ = s * G0 := by rw [h3]

theorem het_star (hK : PiField π p f K) (hq : ModThree π (p ^ f)) (hq2 : π = false → 2 < p ^ f)
    {M : Type*} [Group M]
    (η : (↥(slPi π 3 (p ^ f) K) ⧸ Subgroup.center ↥(slPi π 3 (p ^ f) K)) ≃* M)
    {D : Subgroup (MulAut M)} (hD : CFSG.Open.IsElemAbelian 3 D) (hcard : Nat.card D = 9)
    (hnc : ∃ a b : ↥(glPi π 3 (p ^ f) K), lam hK η a ∈ D ∧ lam hK η b ∈ D ∧ a * b ≠ b * a)
    (x : ↥(glPi π 3 (p ^ f) K)) (hx : lam hK η x ∈ D) (hx1 : lam hK η x ≠ 1) :
    ∃ b : ↥(glPi π 3 (p ^ f) K), lam hK η b ∈ D ∧ b * x ≠ x * b := by
  by_contra hall
  push Not at hall
  set Γ : Subgroup ↥(glPi π 3 (p ^ f) K) := D.comap (lam hK η) with hΓ
  set φ : ↥Γ →* ↥D := ((lam hK η).comp Γ.subtype).codRestrict D (fun g => g.2)
  have hker : φ.ker ≤ Subgroup.center ↥Γ := by
    intro g hg
    have h1 : lam hK η (g : ↥(glPi π 3 (p ^ f) K)) = 1 := congrArg Subtype.val hg
    have hsc := scalar_of_lam_eq_one hK hq hq2 η h1
    rw [Subgroup.mem_center_iff]
    intro b
    apply Subtype.ext
    apply Subtype.ext
    exact commute_of_mem_statedScalars hsc ((b : ↥Γ) : ↥(glPi π 3 (p ^ f) K))
  have hEc : ∀ a b : ↥D, a * b = b * a := fun a b => Subtype.ext (by
    simpa using congrArg Subtype.val (hD.1.is_comm.comm a b))
  have hE3 : ∀ a : ↥D, a ^ 3 = 1 := fun a => Subtype.ext (hD.2 a a.2)
  have hxΓ : x ∈ Γ := by rw [hΓ, Subgroup.mem_comap]; exact hx
  have hxc : (⟨x, hxΓ⟩ : ↥Γ) ∈ Subgroup.center ↥Γ := by
    rw [Subgroup.mem_center_iff]
    intro b
    apply Subtype.ext
    exact hall b b.2
  have hφx : φ ⟨x, hxΓ⟩ ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
  obtain ⟨a, b, ha, hb, hab⟩ := hnc
  have := comm_of_central_lift φ hker hEc hE3 (hcard)
    ⟨x, hxΓ⟩ hxc hφx ⟨a, ha⟩ ⟨b, hb⟩
  exact hab (congrArg (fun z : ↥Γ => (z : ↥(glPi π 3 (p ^ f) K))) this)

end Lift

section InnerDiag

theorem inndiag_of_mem_innerDiag {Y : Type} [Group Y] (hY : CFSG.Open.IsQuasisimple Y)
    {M : Type*} [Group M] (ε : (Y ⧸ Subgroup.center Y) ≃* M) (P : PinnedAut M) (hP : GoodPinned P)
    {α : MulAut Y} (hα : α ∈ Lemma513Ns.innerDiag Y) :
    MulAut.congr ε (centerDescend Y α) ∈ P.inndiag := by
  set Φ : MulAut Y →* MulAut M := (MulAut.congr ε).toMonoidHom.comp (centerDescend Y) with hΦ
  have hle : Lemma513Ns.innerDiag Y ≤ P.inndiag.comap Φ := by
    unfold Lemma513Ns.innerDiag
    refine sup_le ?_ ?_
    · rintro _ ⟨y, rfl⟩
      show Φ (MulAut.conj y) ∈ P.inndiag
      have : Φ (MulAut.conj y) = MulAut.conj (ε (QuotientGroup.mk y)) := by
        simp only [hΦ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
        rw [centerDescend_conj, congr_mulAutConj]
      rw [this]
      exact P.inn_le ⟨_, rfl⟩
    · intro β hβ
      show Φ β ∈ P.inndiag
      have h1 := diagAut_descend_mem_commutator hY hβ
      exact hP.down ((mem_commutator_congr (MulAut.congr ε)).2 h1)
  exact hle hα

theorem mem_diagAut_of_mem_linearAutGroup {Y : Type*} [Group Y] {K : Type} [Field K] [Finite K]
    (ε : (Y ⧸ Subgroup.center Y) ≃* projectiveSL 3 K) {α : MulAut Y}
    (hD : MulAut.congr ε (centerDescend Y α) ∈ linearAutGroup 3 K) :
    α ∈ Lemma513Ns.diagAut Y := by
  rw [linearAutGroup_eq_range] at hD
  obtain ⟨A, hA⟩ := hD
  apply Subgroup.subset_closure
  left
  refine ⟨K, inferInstance, inferInstance, ε.trans (psiO K).symm, A, ?_, ?_⟩
  · intro M
    exact ⟨⟨A * (M : GL (Fin 3) K) * A⁻¹,
      (Subgroup.mem_normalizer_iff.1 (mem_normalizer_statedSL A) M).1 M.2⟩, rfl⟩
  · apply diagProp_of_congr_eq_conjAut
    have : (ε.trans (psiO K).symm).trans (psiO K) = ε := by
      ext x; simp
    rw [this]
    exact hA.symm

theorem mem_diagAut_of_mem_psuConj_range {Y : Type*} [Group Y] {p f : ℕ} {K : Type} [Field K]
    (hF : UnitaryFieldData p f K) (ε : (Y ⧸ Subgroup.center Y) ≃* unitaryPSU hF 3)
    {α : MulAut Y} (hD : MulAut.congr ε (centerDescend Y α) ∈ (psuConj hF).range) :
    α ∈ Lemma513Ns.diagAut Y := by
  have hfin := hF.finite
  obtain ⟨A, hA⟩ := hD
  apply Subgroup.subset_closure
  right
  refine ⟨K, inferInstance, hfin, p ^ f, ε.trans (psuO hF), (A : GL (Fin 3) K),
    by rw [hF.card, pow_mul'], ?_, ?_⟩
  · intro M
    exact ⟨⟨(A : GL (Fin 3) K) * (M : GL (Fin 3) K) * (A : GL (Fin 3) K)⁻¹,
      conj_mem_unitarySU A.2 M.2⟩, rfl⟩
  · apply diagPropU_of_congr_eq_psuConj hF _ α A
    have : (ε.trans (psuO hF)).trans (psuO hF).symm = ε := by
      ext x; simp
    rw [this]
    exact hA.symm

end InnerDiag

end CFSG.HardMathSupport.Solomon.Coordinator
