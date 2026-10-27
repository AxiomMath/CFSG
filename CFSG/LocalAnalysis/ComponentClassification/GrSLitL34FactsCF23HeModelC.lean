module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23HeModelQ

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.CF23L34

open CFSG Subgroup CFSG.Sporadic.HeldB CFSG.Sporadic.Schreier
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34
open CFSG.ComponentClassification.GrSLit.L34Facts

theorem hj_commutator_le_of_index_two {A : Type*} [Group A] {H : Subgroup A} (h : H.index = 2) :
    commutator A ≤ H := by
  rw [_root_.commutator_def, Subgroup.commutator_le]
  intro g₁ _ g₂ _
  rw [commutatorElement_def, Subgroup.mul_mem_iff_of_index_two h,
    Subgroup.mul_mem_iff_of_index_two h, Subgroup.mul_mem_iff_of_index_two h, inv_mem_iff,
    inv_mem_iff]
  tauto


theorem isPerfect_hjJ : Group.IsPerfect ↥hjJ := by
  have : Group.IsPerfect Cover := Group.isPerfect_def.2 commutator_cover
  exact Group.IsPerfect.ofSurjective hjL_surjective

theorem nonempty_hjJ_quot_equiv : Nonempty (↥hjJ ⧸ center ↥hjJ ≃* ↥PSL3Four.S) := by
  set f := hjQ.codRestrict PSL3Four.S hjQ_mem_S with hfdef
  have hf : Function.Surjective f := fun s => by
    obtain ⟨e, he⟩ := hjQ_surj s s.2
    exact ⟨e, Subtype.ext he⟩
  have hker : f.ker = center ↥hjJ := by rw [hfdef, MonoidHom.ker_codRestrict, ker_hjQ]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)⟩

theorem isQuasisimple_hjJ : IsQuasisimple ↥hjJ := by
  have hp := isPerfect_hjJ
  obtain ⟨e⟩ := nonempty_hjJ_quot_equiv
  have hs : IsSimpleGroup (↥hjJ ⧸ center ↥hjJ) := by
    have := hj_isSimpleGroup_S
    exact e.isSimpleGroup
  refine ⟨hp, hs, ?_⟩
  by_contra hno
  push Not at hno
  have hle : commutator ↥hjJ ≤ center ↥hjJ := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [commutatorElement_def, ← QuotientGroup.eq_one_iff]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [← commutatorElement_def, commutatorElement_eq_one_iff_mul_comm]
    exact hno _ _
  rw [hp.commutator_eq_top, top_le_iff] at hle
  obtain ⟨y, hy⟩ := exists_ne (1 : ↥hjJ ⧸ center ↥hjJ)
  obtain ⟨y0, rfl⟩ := QuotientGroup.mk_surjective y
  apply hy
  rw [QuotientGroup.eq_one_iff, hle]
  exact mem_top y0

theorem component_eq_hjJ
    {X : Subgroup ↥(centralizerIn heP (heGenPerm 0))}
    (hX : IsComponent X) : X = hjJ.subgroupOf (centralizerIn heP (heGenPerm 0)) := by
  have hXJ : X ≤ hjJ.subgroupOf (centralizerIn heP (heGenPerm 0)) := by
    have hXp : ⁅X, X⁆ = X := Subgroup.isPerfect_iff.mp hX.1.1
    rw [← hXp]
    exact (Subgroup.commutator_mono le_top le_top).trans
      (hj_commutator_le_of_index_two index_hjJ)
  have hXc := LocalCores.component_overgroup hX hXJ
  have hJq : IsQuasisimple ↥(hjJ.subgroupOf (centralizerIn heP (heGenPerm 0))) :=
    LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hjJ_le).symm
      isQuasisimple_hjJ
  have htop : IsComponent (⊤ : Subgroup ↥(hjJ.subgroupOf (centralizerIn heP (heGenPerm 0)))) :=
    ⟨LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hJq, Subgroup.IsSubnormal.top⟩
  rcases LocalCores.component_subnormal_subgroup htop hXc.2 with h | h
  · apply le_antisymm hXJ
    intro j hj
    have := h (mem_top (⟨j, hj⟩ : ↥(hjJ.subgroupOf (centralizerIn heP (heGenPerm 0)))))
    rwa [mem_subgroupOf] at this
  · exfalso
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h
    obtain ⟨-, -, a, b, hab⟩ := hXc.1
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    apply hab
    have hc : a' * b' = b' * a' := by
      apply Subtype.ext
      exact (mem_centralizer_iff.mp (h (mem_top (a' : ↥(hjJ.subgroupOf
        (centralizerIn heP (heGenPerm 0)))))) b' b'.2).symm
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hc]

theorem center_hjJ_cases {e : ↥hjJ} (he : e ∈ center ↥hjJ) :
    (e : Equiv.Perm (Fin 8330)) = 1 ∨ (e : Equiv.Perm (Fin 8330)) = hjZP ∨
      (e : Equiv.Perm (Fin 8330)) = heGenPerm 0 ∨
        (e : Equiv.Perm (Fin 8330)) = hjZP * heGenPerm 0 :=
  ker_hjQ_cases (ker_hjQ ▸ he)

theorem comm_hjZP {g : Equiv.Perm (Fin 8330)} (hg : g ∈ hjJ) : g * hjZP = hjZP * g := by
  obtain ⟨c, rfl⟩ := hg
  rw [← map_mul, ← map_mul, (mem_center_iff.1 z₁_mem_center c)]

theorem mem_hjJ_of_comm
    {g : Equiv.Perm (Fin 8330)} (hg : g ∈ centralizerIn heP (heGenPerm 0))
    (hgz : g * hjZP = hjZP * g) : g ∈ hjJ := by
  have hJM : hjJ.subgroupOf (centralizerIn heP (heGenPerm 0)) ≤
      (centralizer ({hjZP} : Set (Equiv.Perm (Fin 8330)))).subgroupOf
        (centralizerIn heP (heGenPerm 0)) := fun j hj => by
    rw [mem_subgroupOf] at hj ⊢
    rw [mem_centralizer_singleton_iff]
    exact comm_hjZP hj
  have hdvd := Subgroup.index_dvd_of_le hJM
  rw [index_hjJ] at hdvd
  have hMtop : (centralizer ({hjZP} : Set (Equiv.Perm (Fin 8330)))).subgroupOf
      (centralizerIn heP (heGenPerm 0)) ≠ ⊤ := fun htop => by
    have : (⟨hjGP, hjGP_mem⟩ : ↥(centralizerIn heP (heGenPerm 0))) ∈
        (centralizer ({hjZP} : Set (Equiv.Perm (Fin 8330)))).subgroupOf
          (centralizerIn heP (heGenPerm 0)) := htop ▸ mem_top _
    rw [mem_subgroupOf, mem_centralizer_singleton_iff] at this
    exact hjGP_not_comm this
  have hMi : ((centralizer ({hjZP} : Set (Equiv.Perm (Fin 8330)))).subgroupOf
      (centralizerIn heP (heGenPerm 0))).index = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exact absurd (Subgroup.index_eq_one.mp h1) hMtop
    · exact h2
  have hMJ : (centralizer ({hjZP} : Set (Equiv.Perm (Fin 8330)))).subgroupOf
      (centralizerIn heP (heGenPerm 0)) = hjJ.subgroupOf (centralizerIn heP (heGenPerm 0)) := by
    refine (Subgroup.eq_of_le_of_card_ge hJM ?_).symm
    have h1 := ((centralizer ({hjZP} : Set (Equiv.Perm (Fin 8330)))).subgroupOf
      (centralizerIn heP (heGenPerm 0))).card_mul_index
    have h2 := (hjJ.subgroupOf (centralizerIn heP (heGenPerm 0))).card_mul_index
    rw [hMi] at h1
    rw [index_hjJ] at h2
    omega
  have hgM : (⟨g, hg⟩ : ↥(centralizerIn heP (heGenPerm 0))) ∈
      (centralizer ({hjZP} : Set (Equiv.Perm (Fin 8330)))).subgroupOf
        (centralizerIn heP (heGenPerm 0)) := by
    rw [mem_subgroupOf, mem_centralizer_singleton_iff]
    exact hgz
  rw [hMJ, mem_subgroupOf] at hgM
  exact hgM

end CFSG.ComponentClassification.GSThmB.CF23L34
