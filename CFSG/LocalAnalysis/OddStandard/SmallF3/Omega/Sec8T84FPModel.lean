module

public import Certificates.Data.T84P
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84FPConj

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup Matrix Certificates.Asc82NormA6
open Certificates.A5GL42 (Mat4 Vec4)
open Certificates.T84P (Elt mulE oneE M0l Vl)

private lemma t84_exists_vecOfCode (w : Vec4) :
    ∃ c < 16, Certificates.A5GL42.vecOfCode c = w := by
  have h : ∃ c ∈ Finset.range 16, Certificates.A5GL42.vecOfCode c = w := by
    revert w
    decide
  obtain ⟨c, hc, hcw⟩ := h
  exact ⟨c, Finset.mem_range.mp hc, hcw⟩

private lemma t84_mem_codesS0 {k : ℕ} :
    k ∈ codesS0 ↔ ∃ a : Equiv.Perm (Fin 6), a.sign = 1 ∧ rhoCode a = k := by
  simp [codesS0, Finset.mem_sort, Finset.mem_image, Finset.mem_filter]

@[expose] noncomputable def sec8t84FPAct (F : Facts) :
    ↥(alternatingGroup (Fin 6)) →* MulAut (Multiplicative Vec4) :=
  (CFSG.SectionRank.Ccomm.mulAutEquivGL (p := 2) 4).symm.toMonoidHom.comp
    ((sec8t84RhoGL F).comp (alternatingGroup (Fin 6)).subtype)

theorem sec8t84FPAct_apply (F : Facts) (a : ↥(alternatingGroup (Fin 6)))
    (v : Multiplicative Vec4) :
    Multiplicative.toAdd (sec8t84FPAct F a v) =
      rho (a : Equiv.Perm (Fin 6)) *ᵥ Multiplicative.toAdd v := by
  have h := CFSG.SectionRank.Ccomm.mulAutEquivGL_mulVec (p := 2) 4
    (sec8t84FPAct F a) (Multiplicative.toAdd v)
  have h2 : CFSG.SectionRank.Ccomm.mulAutEquivGL (p := 2) 4 (sec8t84FPAct F a) =
      sec8t84RhoGL F (a : Equiv.Perm (Fin 6)) := by
    simp only [sec8t84FPAct, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply]
    rfl
  rw [h2, sec8t84RhoGL_coe, ofAdd_toAdd] at h
  exact h.symm

abbrev Sec8T84FPM0 (F : Facts) : Type :=
  Multiplicative Vec4 ⋊[sec8t84FPAct F] ↥(alternatingGroup (Fin 6))

instance (F : Facts) : Finite (Sec8T84FPM0 F) :=
  Finite.of_equiv _ SemidirectProduct.equivProd.symm

@[expose] def sec8t84FPRaw (F : Facts) (x : Sec8T84FPM0 F) : Elt :=
  (Multiplicative.toAdd x.left, rho (x.right : Equiv.Perm (Fin 6)))

theorem sec8t84FPRaw_mul (F : Facts) (x y : Sec8T84FPM0 F) :
    sec8t84FPRaw F (x * y) = mulE (sec8t84FPRaw F x) (sec8t84FPRaw F y) := by
  apply Prod.ext
  · simp only [sec8t84FPRaw, mulE, SemidirectProduct.mul_left, toAdd_mul]
    rw [sec8t84FPAct_apply]
  · simp only [sec8t84FPRaw, mulE, SemidirectProduct.mul_right, Subgroup.coe_mul,
      F.rho_mul]

theorem sec8t84FPRaw_one (F : Facts) : sec8t84FPRaw F 1 = oneE := by
  simp only [sec8t84FPRaw, oneE, SemidirectProduct.one_left, SemidirectProduct.one_right,
    toAdd_one, Subgroup.coe_one, F.rho_one]

theorem sec8t84FPRaw_injective (F : Facts) : Function.Injective (sec8t84FPRaw F) := by
  intro x y h
  have h1 : Multiplicative.toAdd x.left = Multiplicative.toAdd y.left := by
    simpa only [sec8t84FPRaw] using congrArg Prod.fst h
  have h2 : rho (x.right : Equiv.Perm (Fin 6)) = rho (y.right : Equiv.Perm (Fin 6)) := by
    simpa only [sec8t84FPRaw] using congrArg Prod.snd h
  apply SemidirectProduct.ext
  · exact Multiplicative.toAdd.injective h1
  · apply Subtype.ext
    apply sec8t84RhoGL_injective F
    apply Units.ext
    simpa only [sec8t84RhoGL_coe] using h2

theorem sec8t84FPRaw_mem (F : Facts) (x : Sec8T84FPM0 F) : sec8t84FPRaw F x ∈ M0l := by
  obtain ⟨c, hc, hcw⟩ := t84_exists_vecOfCode (Multiplicative.toAdd x.left)
  rw [M0l, List.mem_flatMap]
  refine ⟨c, List.mem_range.mpr hc, ?_⟩
  rw [List.mem_map]
  refine ⟨rhoCode (x.right : Equiv.Perm (Fin 6)),
    t84_mem_codesS0.mpr ⟨(x.right : Equiv.Perm (Fin 6)),
      Equiv.Perm.mem_alternatingGroup.mp x.right.2, rfl⟩, ?_⟩
  simp only [sec8t84FPRaw, hcw, rho]

theorem sec8t84FPRaw_surj (F : Facts) {z : Elt} (hz : z ∈ M0l) :
    ∃ x : Sec8T84FPM0 F, sec8t84FPRaw F x = z := by
  rw [M0l, List.mem_flatMap] at hz
  obtain ⟨c, _, hz'⟩ := hz
  rw [List.mem_map] at hz'
  obtain ⟨k, hk, hkz⟩ := hz'
  obtain ⟨a, ha, hak⟩ := t84_mem_codesS0.mp hk
  refine ⟨⟨Multiplicative.ofAdd (Certificates.A5GL42.vecOfCode c),
    ⟨a, Equiv.Perm.mem_alternatingGroup.mpr ha⟩⟩, ?_⟩
  rw [← hkz]
  simp only [sec8t84FPRaw, toAdd_ofAdd, hak, rho]

theorem sec8t84FPM0_card (F : Facts) : Nat.card (Sec8T84FPM0 F) = 5760 := by
  rw [Sec8T84FPM0, SemidirectProduct.card]
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_fin,
    nat_card_alternatingGroup, Nat.card_fin]
  norm_num

@[expose] noncomputable def Sec8T84FPV0 (F : Facts) : Subgroup (Sec8T84FPM0 F) :=
  (SemidirectProduct.inl : Multiplicative Vec4 →* Sec8T84FPM0 F).range

theorem sec8t84FPV0_normal (F : Facts) : (Sec8T84FPV0 F).Normal := by
  show ((SemidirectProduct.inl : Multiplicative Vec4 →* Sec8T84FPM0 F).range).Normal
  rw [SemidirectProduct.range_inl_eq_ker_rightHom]
  exact MonoidHom.normal_ker _

theorem sec8t84FPV0_mem (F : Facts) (x : Sec8T84FPM0 F) :
    x ∈ Sec8T84FPV0 F ↔ sec8t84FPRaw F x ∈ Vl := by
  have hmem : x ∈ Sec8T84FPV0 F ↔ x.right = 1 := by
    show x ∈ (SemidirectProduct.inl : Multiplicative Vec4 →* Sec8T84FPM0 F).range ↔
      x.right = 1
    rw [SemidirectProduct.range_inl_eq_ker_rightHom, MonoidHom.mem_ker]
    rfl
  have hvl : sec8t84FPRaw F x ∈ Vl ↔ rho (x.right : Equiv.Perm (Fin 6)) = 1 := by
    constructor
    · intro h
      rw [Vl, List.mem_map] at h
      obtain ⟨c, _, hcz⟩ := h
      exact (congrArg Prod.snd hcz).symm
    · intro h
      rw [Vl, List.mem_map]
      obtain ⟨c, hc, hcw⟩ := t84_exists_vecOfCode (Multiplicative.toAdd x.left)
      exact ⟨c, List.mem_range.mpr hc, by simp only [sec8t84FPRaw, hcw, h]⟩
  rw [hmem, hvl]
  constructor
  · intro h
    rw [h]
    simpa using F.rho_one
  · intro h
    exact Subtype.ext (F.rho_ker _ h)

@[expose] def sec8t84FPOfList (F : Facts) (l : List Elt) (h1 : oneE ∈ l)
    (hmul : ∀ x ∈ l, ∀ y ∈ l, mulE x y ∈ l) : Subgroup (Sec8T84FPM0 F) where
  carrier := {x | sec8t84FPRaw F x ∈ l}
  mul_mem' := by
    intro x y hx hy
    change sec8t84FPRaw F (x * y) ∈ l
    rw [sec8t84FPRaw_mul]
    exact hmul _ hx _ hy
  one_mem' := by
    change sec8t84FPRaw F 1 ∈ l
    rw [sec8t84FPRaw_one]
    exact h1
  inv_mem' := by
    intro x hx
    change sec8t84FPRaw F x⁻¹ ∈ l
    have hpow : ∀ n : ℕ, sec8t84FPRaw F (x ^ n) ∈ l := by
      intro n
      induction n with
      | zero => rw [pow_zero, sec8t84FPRaw_one]; exact h1
      | succ n ih => rw [pow_succ, sec8t84FPRaw_mul]; exact hmul _ ih _ hx
    have hinv : x⁻¹ = x ^ (orderOf x - 1) := by
      rw [eq_comm, pow_sub x (orderOf_pos x), pow_orderOf_eq_one, one_mul, pow_one]
    rw [hinv]
    exact hpow _

theorem sec8t84FPOfList_mem (F : Facts) {l : List Elt} (h1 : oneE ∈ l)
    (hmul : ∀ x ∈ l, ∀ y ∈ l, mulE x y ∈ l) (x : Sec8T84FPM0 F) :
    x ∈ sec8t84FPOfList F l h1 hmul ↔ sec8t84FPRaw F x ∈ l :=
  Iff.rfl

theorem sec8t84FPOfList_card (F : Facts) {l : List Elt} (h1 : oneE ∈ l)
    (hmul : ∀ x ∈ l, ∀ y ∈ l, mulE x y ∈ l) (hl : ∀ z ∈ l, z ∈ M0l) :
    Nat.card (sec8t84FPOfList F l h1 hmul) = l.toFinset.card := by
  let g : sec8t84FPOfList F l h1 hmul → {z : Elt // z ∈ l.toFinset} :=
    fun x => ⟨sec8t84FPRaw F (x : Sec8T84FPM0 F),
      List.mem_toFinset.mpr (show sec8t84FPRaw F (x : Sec8T84FPM0 F) ∈ l from x.2)⟩
  have hg : Function.Bijective g := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      apply sec8t84FPRaw_injective F
      exact congrArg Subtype.val hxy
    · intro z
      have hzmem : z.1 ∈ l := List.mem_toFinset.mp z.2
      obtain ⟨x, hx⟩ := sec8t84FPRaw_surj F (hl z.1 hzmem)
      refine ⟨⟨x, ?_⟩, ?_⟩
      · change sec8t84FPRaw F x ∈ l
        rw [hx]
        exact hzmem
      · apply Subtype.ext
        exact hx
  rw [Nat.card_congr (Equiv.ofBijective g hg), Nat.card_eq_fintype_card, Fintype.card_coe]

end CFSG.OddStandard.SmallF3.Omega
