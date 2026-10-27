module

public import CFSG.Dihedral.GorensteinWalter.Support
public import Mathlib.GroupTheory.Focal
public import Mathlib.GroupTheory.Perm.Subgroup
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Presheaf

public section

namespace CFSG

open scoped commutatorElement Pointwise

namespace GorensteinWalter.Helpers

def dihedralRotations (n : ℕ) : Subgroup (DihedralGroup n) where
  carrier := Set.range DihedralGroup.r
  one_mem' := ⟨0, DihedralGroup.r_zero⟩
  mul_mem' := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    exact ⟨i + j, (DihedralGroup.r_mul_r i j).symm⟩
  inv_mem' := by
    rintro _ ⟨i, rfl⟩
    exact ⟨-i, (DihedralGroup.inv_r i).symm⟩

@[simp]
lemma r_mem_dihedralRotations {n : ℕ} (i : ZMod n) :
    DihedralGroup.r i ∈ dihedralRotations n :=
  ⟨i, rfl⟩

@[simp]
lemma sr_not_mem_dihedralRotations {n : ℕ} (i : ZMod n) :
    DihedralGroup.sr i ∉ dihedralRotations n := by
  rintro ⟨j, h⟩
  injection h

private def rotationSubgroup {G : Type*} [Group G] (P : Sylow 2 G) {n : ℕ}
    (e : P ≃* DihedralGroup n) : Subgroup G :=
  (dihedralRotations n).map ((P : Subgroup G).subtype.comp e.symm.toMonoidHom)

private lemma rotationSubgroup_lt_sylow {G : Type*} [Group G] (P : Sylow 2 G) {n : ℕ}
    (e : P ≃* DihedralGroup n) : rotationSubgroup P e < P := by
  let f : DihedralGroup n →* G := (P : Subgroup G).subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f :=
    (P : Subgroup G).subtype_injective.comp e.symm.injective
  refine lt_iff_le_and_ne.mpr ⟨?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact (e.symm x).2
  · intro heq
    have hle : (P : Subgroup G) ≤ rotationSubgroup P e := by
      rw [heq]
    have href : f (DihedralGroup.sr 0) ∈ rotationSubgroup P e :=
      hle (e.symm (DihedralGroup.sr 0)).2
    change f (DihedralGroup.sr 0) ∈ (dihedralRotations n).map f at href
    obtain ⟨x, hx, heq⟩ := href
    have : x = DihedralGroup.sr 0 := hf heq
    subst x
    exact sr_not_mem_dihedralRotations 0 hx

lemma dihedralIndex_ne_zero {G : Type*} [Group G] [Finite G]
    (P : Sylow 2 G) {n : ℕ}
    (h : Nonempty ((P : Subgroup G) ≃* DihedralGroup n)) : n ≠ 0 := by
  intro hn
  subst n
  have hcard := Nat.card_congr h.some.toEquiv
  rw [DihedralGroup.nat_card] at hcard
  exact Nat.card_pos.ne' hcard

private lemma dihedralIndex_eq_two_pow {G : Type*} [Group G] [Finite G]
    (P : Sylow 2 G) {n : ℕ}
    (h : Nonempty ((P : Subgroup G) ≃* DihedralGroup n)) :
    ∃ m : ℕ, n = 2 ^ m := by
  obtain ⟨e⟩ := h
  let : Finite (DihedralGroup n) := Finite.of_equiv _ e.toEquiv
  obtain ⟨r, hr⟩ := (P.isPGroup'.of_equiv e).exists_card_eq
  rw [DihedralGroup.nat_card] at hr
  cases r with
  | zero => simp at hr
  | succ m =>
      rw [pow_succ, Nat.mul_comm (2 ^ m) 2] at hr
      exact ⟨m, Nat.mul_left_cancel zero_lt_two hr⟩

lemma commutator_eq_top_of_noncommutative {G : Type*} [Group G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) : commutator G = ⊤ := by
  rcases (Subgroup.commutator_normal (⊤ : Subgroup G) (⊤ : Subgroup G)).eq_bot_or_eq_top with h | h
  · obtain ⟨a, b, hab⟩ := hnonab
    exact (hab ((isMulCommutative_iff.mp ((commutator_eq_bot_iff G).mp h)) a b)).elim
  · exact h

lemma center_eq_bot_of_noncommutative {G : Type*} [Group G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) : Subgroup.center G = ⊥ := by
  rcases (inferInstance : (Subgroup.center G).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · obtain ⟨a, b, hab⟩ := hnonab
    exact (hab ((isMulCommutative_iff.mp (Subgroup.center_eq_top_iff.mp h)) a b)).elim

private lemma sylow_ne_top_of_noncommutative {G : Type*} [Group G] [Finite G]
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) (P : Sylow 2 G) :
    (P : Subgroup G) ≠ ⊤ := by
  intro htop
  have hpTop : IsPGroup 2 (⊤ : Subgroup G) := by
    rw [← htop]
    exact P.isPGroup'
  have hpG : IsPGroup 2 G := hpTop.of_equiv Subgroup.topEquiv
  let : Nontrivial (Subgroup.center G) := hpG.center_nontrivial
  simpa [center_eq_bot_of_noncommutative hnonab] using
    (Finite.one_lt_card (α := Subgroup.center G))

private lemma dihedralIndex_ne_one {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (P : Sylow 2 G) {n : ℕ}
    (h : Nonempty ((P : Subgroup G) ≃* DihedralGroup n)) : n ≠ 1 := by
  intro hn
  subst n
  obtain ⟨e⟩ := h
  have hPcard : Nat.card P = 2 := by
    calc
      Nat.card P = Nat.card (DihedralGroup 1) := Nat.card_congr e.toEquiv
      _ = 2 := by simpa using (DihedralGroup.card (n := 1))
  have htwo : 2 ∣ Nat.card G := hPcard ▸ Subgroup.card_subgroup_dvd_card (P : Subgroup G)
  have hmin : (Nat.card G).minFac = 2 := (Nat.minFac_eq_two_iff _).mpr htwo
  have hcyc : IsCyclic P := e.isCyclic.mpr (DihedralGroup.isCyclic_iff.mpr rfl)
  let hnorm := hcyc.normalizer_le_centralizer hmin
  let K := (MonoidHom.transferSylow P hnorm).ker
  have hcomp : K.IsComplement' P := MonoidHom.ker_transferSylow_isComplement' P hnorm
  have hKnormal : K.Normal := inferInstance
  rcases hKnormal.eq_bot_or_eq_top with hKbot | hKtop
  · have hPtop : (P : Subgroup G) = ⊤ := by
      rw [hKbot] at hcomp
      exact Subgroup.isComplement'_bot_left.mp hcomp
    exact sylow_ne_top_of_noncommutative hnonab P hPtop
  · have hPbot : (P : Subgroup G) = ⊥ := by
      rw [hKtop] at hcomp
      exact Subgroup.isComplement'_top_left.mp hcomp
    rw [hPbot, Subgroup.card_bot] at hPcard
    omega

lemma dihedralIndex_eq_two_pow_pos {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (P : Sylow 2 G) {n : ℕ}
    (h : Nonempty ((P : Subgroup G) ≃* DihedralGroup n)) :
    ∃ m > 0, n = 2 ^ m := by
  obtain ⟨m, hm⟩ := dihedralIndex_eq_two_pow P h
  have hn1 := dihedralIndex_ne_one hnonab P h
  have hm0 : m ≠ 0 := by
    intro hm0
    apply hn1
    simpa [hm0] using hm
  exact ⟨m, Nat.pos_of_ne_zero hm0, hm⟩

lemma sylow_not_isCyclic_of_dihedral {G : Type*} [Group G] [Finite G]
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) (P : Sylow 2 G)
    {n : ℕ} (h : Nonempty ((P : Subgroup G) ≃* DihedralGroup n)) :
    ¬IsCyclic P := by
  intro hcyclic
  have hn1 := dihedralIndex_ne_one hnonab P h
  obtain ⟨e⟩ := h
  exact DihedralGroup.not_isCyclic hn1 (e.isCyclic.mp hcyclic)

private lemma focalSubgroup_eq_sylow {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (P : Sylow 2 G) :
    P.focalSubgroup = P := by
  rw [← Subgroup.commutator_inf_eq_focalSubgroup P,
    commutator_eq_top_of_noncommutative hnonab]
  simp

private lemma exists_focal_generator_outside_rotations {G : Type*} [Group G] [Finite G]
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) (P : Sylow 2 G)
    {n : ℕ} (e : P ≃* DihedralGroup n) :
    ∃ g : G, g ∈ P ∧ (∃ x ∈ P, ∃ u : G, g = ⁅x, u⁆) ∧
      g ∉ rotationSubgroup P e := by
  let S : Set G := {g | g ∈ P ∧ ∃ x ∈ P, ∃ u : G, g = ⁅x, u⁆}
  have hnot : ¬S ⊆ rotationSubgroup P e := by
    intro hle
    have hfocal : P.focalSubgroup ≤ rotationSubgroup P e := by
      rw [Subgroup.focalSubgroup_def, Subgroup.closure_le]
      exact hle
    have hP : (P : Subgroup G) ≤ rotationSubgroup P e := by
      rw [← focalSubgroup_eq_sylow hnonab P]
      exact hfocal
    exact (not_le_of_gt (rotationSubgroup_lt_sylow P e)) hP
  obtain ⟨g, hg, hgnmem⟩ := Set.not_subset.mp hnot
  exact ⟨g, hg.1, hg.2, hgnmem⟩

private lemma exists_rotation_reflection_fusion {G : Type*} [Group G] [Finite G]
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) (P : Sylow 2 G)
    {n : ℕ} (e : P ≃* DihedralGroup n) :
    ∃ a b : P,
      (∃ i : ZMod n, e a = DihedralGroup.r i) ∧
      (∃ j : ZMod n, e b = DihedralGroup.sr j) ∧
      ∃ u : G, (b : G) = u * (a : G)⁻¹ * u⁻¹ ∨
        (a : G) = u * (b : G)⁻¹ * u⁻¹ := by
  obtain ⟨g, hgP, ⟨x, hxP, u, hg⟩, hgR⟩ :=
    exists_focal_generator_outside_rotations hnonab P e
  let xP : P := ⟨x, hxP⟩
  let y : G := u * x⁻¹ * u⁻¹
  have hy_eq : y = x⁻¹ * g := by
    rw [hg]
    simp [y, commutatorElement_def, mul_assoc]
  have hyP : y ∈ P := by
    rw [hy_eq]
    exact P.mul_mem (P.inv_mem hxP) hgP
  let yP : P := ⟨y, hyP⟩
  let gP : P := ⟨g, hgP⟩
  have hprod : e xP * e yP = e gP := by
    rw [← e.map_mul]
    apply congrArg e
    apply Subtype.ext
    simp [xP, yP, gP, y, hg, commutatorElement_def, mul_assoc]
  have hgD : e gP ∉ dihedralRotations n := by
    intro hmem
    apply hgR
    change g ∈ (dihedralRotations n).map
      ((P : Subgroup G).subtype.comp e.symm.toMonoidHom)
    exact ⟨e gP, hmem, by simp [gP]⟩
  generalize hxImage : e xP = ex
  generalize hyImage : e yP = ey
  cases ex with
  | r i =>
      cases ey with
      | r j =>
          exfalso
          apply hgD
          rw [← hprod, hxImage, hyImage]
          simp
      | sr j =>
          exact ⟨xP, yP, ⟨i, hxImage⟩, ⟨j, hyImage⟩, u, Or.inl rfl⟩
  | sr i =>
      cases ey with
      | r j =>
          exact ⟨yP, xP, ⟨j, hyImage⟩, ⟨i, hxImage⟩, u, Or.inr rfl⟩
      | sr j =>
          exfalso
          apply hgD
          rw [← hprod, hxImage, hyImage]
          simp

private lemma exists_fused_rotation_reflection_involutions {G : Type*} [Group G] [Finite G]
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) (P : Sylow 2 G)
    {n : ℕ} (e : P ≃* DihedralGroup n) :
    ∃ a b : P,
      (∃ i : ZMod n, e a = DihedralGroup.r i) ∧
      (∃ j : ZMod n, e b = DihedralGroup.sr j) ∧
      orderOf (a : G) = 2 ∧ orderOf (b : G) = 2 ∧
      ∃ u : G, (b : G) = u * (a : G)⁻¹ * u⁻¹ ∨
        (a : G) = u * (b : G)⁻¹ * u⁻¹ := by
  obtain ⟨a, b, ha, hb, u, hab⟩ := exists_rotation_reflection_fusion hnonab P e
  have hbOrder : orderOf (b : G) = 2 := by
    obtain ⟨j, hbj⟩ := hb
    calc
      orderOf (b : G) = orderOf b :=
        orderOf_injective (P : Subgroup G).subtype (P : Subgroup G).subtype_injective b
      _ = orderOf (e b) := (e.orderOf_eq b).symm
      _ = 2 := by rw [hbj]; exact DihedralGroup.orderOf_sr j
  have haOrder : orderOf (a : G) = 2 := by
    rcases hab with hab | hab
    · calc
        orderOf (a : G) = orderOf (a : G)⁻¹ := (orderOf_inv (a : G)).symm
        _ = orderOf (u * (a : G)⁻¹ * u⁻¹) := by
          simpa [MulAut.conj_apply] using
            ((MulAut.conj u).orderOf_eq ((a : G)⁻¹)).symm
        _ = orderOf (b : G) := by rw [← hab]
        _ = 2 := hbOrder
    · calc
        orderOf (a : G) = orderOf (u * (b : G)⁻¹ * u⁻¹) := by rw [hab]
        _ = orderOf (b : G)⁻¹ := by
          simpa [MulAut.conj_apply] using
            (MulAut.conj u).orderOf_eq ((b : G)⁻¹)
        _ = orderOf (b : G) := orderOf_inv (b : G)
        _ = 2 := hbOrder
  exact ⟨a, b, ha, hb, haOrder, hbOrder, u, hab⟩

private lemma exists_fused_central_rotation_reflection_involutions {G : Type*} [Group G]
    [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (P : Sylow 2 G) {n : ℕ} (e : P ≃* DihedralGroup n) :
    ∃ a b : P,
      a ∈ Subgroup.center P ∧
      (∃ i : ZMod n, e a = DihedralGroup.r i) ∧
      (∃ j : ZMod n, e b = DihedralGroup.sr j) ∧
      orderOf (a : G) = 2 ∧ orderOf (b : G) = 2 ∧
      ∃ u : G, (b : G) = u * (a : G)⁻¹ * u⁻¹ ∨
        (a : G) = u * (b : G)⁻¹ * u⁻¹ := by
  obtain ⟨a, b, ha, hb, haOrder, hbOrder, u, hab⟩ :=
    exists_fused_rotation_reflection_involutions hnonab P e
  obtain ⟨i, hai⟩ := ha
  have heaOrder : orderOf (e a) = 2 := by
    calc
      orderOf (e a) = orderOf a := e.orderOf_eq a
      _ = orderOf (a : G) :=
        (orderOf_injective (P : Subgroup G).subtype
          (P : Subgroup G).subtype_injective a).symm
      _ = 2 := haOrder
  have hpow := pow_orderOf_eq_one (e a)
  rw [heaOrder, hai, pow_two, DihedralGroup.r_mul_r,
    DihedralGroup.one_def] at hpow
  have hi2 : i + i = 0 := DihedralGroup.r.inj hpow
  have hiNeg : -i = i := (neg_eq_iff_add_eq_zero).2 hi2
  have haCenterD : e a ∈ Subgroup.center (DihedralGroup n) := by
    rw [Subgroup.mem_center_iff]
    intro z
    rw [hai]
    cases z with
    | r j => simp [add_comm]
    | sr j => simp [sub_eq_add_neg, hiNeg]
  have haCenterP : a ∈ Subgroup.center P := by
    rw [Subgroup.mem_center_iff] at haCenterD
    apply (Subgroup.mem_center_iff (G := (P : Subgroup G))).2
    intro z
    apply e.injective
    simpa using haCenterD (e z)
  exact ⟨a, b, haCenterP, ⟨i, hai⟩, hb, haOrder, hbOrder, u, hab⟩

private lemma exists_conjugate_central_rotation_reflection_involutions {G : Type*} [Group G]
    [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (P : Sylow 2 G) {n : ℕ} (e : P ≃* DihedralGroup n) :
    ∃ a b : P,
      a ∈ Subgroup.center P ∧
      (∃ i : ZMod n, e a = DihedralGroup.r i) ∧
      (∃ j : ZMod n, e b = DihedralGroup.sr j) ∧
      orderOf (a : G) = 2 ∧ orderOf (b : G) = 2 ∧
      ∃ u : G, (b : G) = u * (a : G) * u⁻¹ := by
  obtain ⟨a, b, haCenter, ha, hb, haOrder, hbOrder, u, hab⟩ :=
    exists_fused_central_rotation_reflection_involutions hnonab P e
  have haInv : (a : G)⁻¹ = (a : G) := inv_eq_self_of_orderOf_eq_two haOrder
  have hbInv : (b : G)⁻¹ = (b : G) := inv_eq_self_of_orderOf_eq_two hbOrder
  refine ⟨a, b, haCenter, ha, hb, haOrder, hbOrder, ?_⟩
  rcases hab with hab | hab
  · exact ⟨u, by simpa [haInv] using hab⟩
  · refine ⟨u⁻¹, ?_⟩
    rw [hab, hbInv]
    simp [mul_assoc]

private lemma sylow_le_centralizer_singleton_iff_mem_center {G : Type*} [Group G]
    (P : Sylow 2 G) (b : P) :
    (P : Subgroup G) ≤ Subgroup.centralizer {(b : G)} ↔
      b ∈ Subgroup.center P := by
  constructor
  · intro h
    apply (Subgroup.mem_center_iff (G := P)).mpr
    intro x
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (h x.2))
  · intro hb x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hb) ⟨x, hx⟩)

private lemma conjugate_sylow_le_centralizer_singleton {G : Type*} [Group G]
    (P : Sylow 2 G) (a : P) (ha : a ∈ Subgroup.center P) (b u : G)
    (hab : b = u * (a : G) * u⁻¹) :
    ((u • P : Sylow 2 G) : Subgroup G) ≤ Subgroup.centralizer {b} := by
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  change x ∈ MulAut.conj u • (P : Subgroup G) at hx
  have hxP : (MulAut.conj u)⁻¹ • x ∈ (P : Subgroup G) :=
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem.mp hx
  have hcomm := (Subgroup.mem_center_iff.mp ha) ⟨(MulAut.conj u)⁻¹ • x, hxP⟩
  have hcommG : ((MulAut.conj u)⁻¹ • x) * (a : G) =
      (a : G) * ((MulAut.conj u)⁻¹ • x) := congrArg Subtype.val hcomm
  have hucomm := congrArg (fun z : G ↦ MulAut.conj u z) hcommG
  simpa [hab, MulAut.conj_apply, mul_assoc] using hucomm

private lemma normalClosure_singleton_eq_top_of_orderOf_eq_two {G : Type*} [Group G]
    [IsSimpleGroup G] {a : G} (ha : orderOf a = 2) :
    Subgroup.normalClosure {a} = ⊤ := by
  have haNe : a ≠ 1 := by
    intro haOne
    subst a
    simp at ha
  apply Subgroup.normalClosure_normal.eq_bot_or_eq_top.resolve_left
  simp [haNe]

private lemma sr_not_mem_center_of_two_lt {n : ℕ} (hn : 2 < n) (j : ZMod n) :
    DihedralGroup.sr j ∉ Subgroup.center (DihedralGroup n) := by
  intro hj
  have hcomm := (Subgroup.mem_center_iff.mp hj) (DihedralGroup.r 1)
  have heq : j - 1 = j + 1 := DihedralGroup.sr.inj (by simpa using hcomm)
  rw [sub_eq_add_neg] at heq
  have hone : -(1 : ZMod n) = 1 := add_left_cancel heq
  have htwo : (2 : ZMod n) = 0 := by
    calc
      (2 : ZMod n) = 1 + 1 := by norm_num
      _ = 1 + -1 := by rw [hone]
      _ = 0 := add_neg_cancel 1
  have hdiv : n ∣ 2 := (ZMod.natCast_eq_zero_iff 2 n).mp htwo
  exact (not_le_of_gt hn) (Nat.le_of_dvd (by omega) hdiv)

private lemma exists_conjugate_central_noncentral_involutions_of_one_lt {G : Type*}
    [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (P : Sylow 2 G) {m : ℕ}
    (hm : 1 < m) (e : P ≃* DihedralGroup (2 ^ m)) :
    ∃ a b : P,
      a ∈ Subgroup.center P ∧ b ∉ Subgroup.center P ∧
      (∃ i : ZMod (2 ^ m), e a = DihedralGroup.r i) ∧
      (∃ j : ZMod (2 ^ m), e b = DihedralGroup.sr j) ∧
      orderOf (a : G) = 2 ∧ orderOf (b : G) = 2 ∧
      ∃ u : G, (b : G) = u * (a : G) * u⁻¹ := by
  obtain ⟨a, b, haCenter, ha, hb, haOrder, hbOrder, u, hab⟩ :=
    exists_conjugate_central_rotation_reflection_involutions hnonab P e
  have hn : 2 < 2 ^ m := by
    simpa using (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mpr hm
  have hbNotCenter : b ∉ Subgroup.center P := by
    intro hbCenter
    obtain ⟨j, hbj⟩ := hb
    have hebCenter : e b ∈ Subgroup.center (DihedralGroup (2 ^ m)) := by
      exact MulEquivClass.apply_mem_center e hbCenter
    rw [hbj] at hebCenter
    exact sr_not_mem_center_of_two_lt hn j hebCenter
  exact ⟨a, b, haCenter, hbNotCenter, ha, hb, haOrder, hbOrder, u, hab⟩

private lemma exists_distinct_conjugate_sylow_in_involution_centralizer {G : Type*}
    [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (P : Sylow 2 G) {m : ℕ}
    (hm : 1 < m) (e : P ≃* DihedralGroup (2 ^ m)) :
    ∃ a b : P, ∃ u : G,
      a ∈ Subgroup.center P ∧ b ∉ Subgroup.center P ∧
      orderOf (a : G) = 2 ∧ orderOf (b : G) = 2 ∧
      (b : G) = u * (a : G) * u⁻¹ ∧
      ((u • P : Sylow 2 G) : Subgroup G) ≤ Subgroup.centralizer {(b : G)} ∧
      u • P ≠ P := by
  obtain ⟨a, b, haCenter, hbNotCenter, -, -, haOrder, hbOrder, u, hab⟩ :=
    exists_conjugate_central_noncentral_involutions_of_one_lt hnonab P hm e
  have hconjLe : ((u • P : Sylow 2 G) : Subgroup G) ≤
      Subgroup.centralizer {(b : G)} :=
    conjugate_sylow_le_centralizer_singleton P a haCenter b u hab
  have hPNotLe : ¬(P : Subgroup G) ≤ Subgroup.centralizer {(b : G)} :=
    (sylow_le_centralizer_singleton_iff_mem_center P b).not.mpr hbNotCenter
  have hne : u • P ≠ P := by
    intro heq
    apply hPNotLe
    simpa [heq] using hconjLe
  exact ⟨a, b, u, haCenter, hbNotCenter, haOrder, hbOrder, hab, hconjLe, hne⟩

private lemma odd_index_of_sylow_le {G : Type*} [Group G] [Finite G]
    (P : Sylow 2 G) (H : Subgroup G) (hPH : (P : Subgroup G) ≤ H) :
    Odd H.index := by
  rw [← Nat.not_even_iff_odd]
  intro hEven
  apply P.not_dvd_index
  exact (even_iff_two_dvd.mp hEven).trans (Subgroup.index_dvd_of_le hPH)

private lemma exists_noncentral_involution_with_odd_centralizer_index {G : Type*}
    [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (P : Sylow 2 G) {m : ℕ}
    (hm : 1 < m) (e : P ≃* DihedralGroup (2 ^ m)) :
    ∃ b : P,
      b ∉ Subgroup.center P ∧ orderOf (b : G) = 2 ∧
      Odd (Subgroup.centralizer {(b : G)}).index ∧
      Subgroup.normalClosure {(b : G)} = ⊤ := by
  obtain ⟨-, b, u, -, hbNotCenter, -, hbOrder, -, hconjLe, -⟩ :=
    exists_distinct_conjugate_sylow_in_involution_centralizer hnonab P hm e
  exact ⟨b, hbNotCenter, hbOrder,
    odd_index_of_sylow_le (u • P) (Subgroup.centralizer {(b : G)}) hconjLe,
    normalClosure_singleton_eq_top_of_orderOf_eq_two hbOrder⟩

private lemma dihedral_sylow_index_one_or_involution_configuration {G : Type*}
    [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (P : Sylow 2 G) {m : ℕ}
    (hm : 0 < m) (e : P ≃* DihedralGroup (2 ^ m)) :
    m = 1 ∨
      ∃ b : P,
        b ∉ Subgroup.center P ∧ orderOf (b : G) = 2 ∧
        Odd (Subgroup.centralizer {(b : G)}).index ∧
        Subgroup.normalClosure {(b : G)} = ⊤ := by
  rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr hm.ne') with hmOne | hmLarge
  · exact Or.inl hmOne.symm
  · exact Or.inr
      (exists_noncentral_involution_with_odd_centralizer_index hnonab P hmLarge e)

private lemma exists_involution_with_odd_centralizer_index_of_dihedral_two {G : Type*}
    [Group G] [Finite G] [IsSimpleGroup G]
    (P : Sylow 2 G) (e : P ≃* DihedralGroup 2) :
    ∃ b : P,
      orderOf (b : G) = 2 ∧ Odd (Subgroup.centralizer {(b : G)}).index ∧
      Subgroup.normalClosure {(b : G)} = ⊤ := by
  let : Nontrivial P := e.toEquiv.nontrivial
  let : IsKleinFour P :=
    { card_four := by
        calc
          Nat.card P = Nat.card (DihedralGroup 2) := Nat.card_congr e.toEquiv
          _ = 4 := by simp
      exponent_two :=
        (Monoid.exponent_eq_of_mulEquiv e).trans (by simp) }
  obtain ⟨b, hb⟩ := exists_ne (1 : P)
  have hbCenter : b ∈ Subgroup.center P := by
    apply (Subgroup.mem_center_iff (G := (P : Subgroup G))).mpr
    exact fun g ↦ isMulCommutative_iff.mp IsKleinFour.isMulCommutative g b
  have hbOrder : orderOf (b : G) = 2 := by
    calc
      orderOf (b : G) = orderOf b :=
        orderOf_injective (P : Subgroup G).subtype
          (P : Subgroup G).subtype_injective b
      _ = 2 := (orderOf_eq_two_iff IsKleinFour.exponent_two).mpr hb
  have hPLe : (P : Subgroup G) ≤ Subgroup.centralizer {(b : G)} :=
    (sylow_le_centralizer_singleton_iff_mem_center P b).mpr hbCenter
  exact ⟨b, hbOrder,
    odd_index_of_sylow_le P (Subgroup.centralizer {(b : G)}) hPLe,
    normalClosure_singleton_eq_top_of_orderOf_eq_two hbOrder⟩

private lemma exists_involution_with_odd_centralizer_index_of_dihedral_two_pow {G : Type*}
    [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (P : Sylow 2 G) {m : ℕ}
    (hm : 0 < m) (e : P ≃* DihedralGroup (2 ^ m)) :
    ∃ b : P,
      orderOf (b : G) = 2 ∧ Odd (Subgroup.centralizer {(b : G)}).index ∧
      Subgroup.normalClosure {(b : G)} = ⊤ := by
  rcases dihedral_sylow_index_one_or_involution_configuration hnonab P hm e with
    hmOne | ⟨b, -, hbOrder, hbOdd, hbNormal⟩
  · subst m
    simpa using exists_involution_with_odd_centralizer_index_of_dihedral_two P e
  · exact ⟨b, hbOrder, hbOdd, hbNormal⟩

private lemma centralizer_singleton_ne_top_of_orderOf_eq_two {G : Type*} [Group G]
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) {b : G}
    (hb : orderOf b = 2) : Subgroup.centralizer {b} ≠ ⊤ := by
  intro htop
  have hbCenter : b ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subgroup.mem_centralizer_singleton_iff.mp
    rw [htop]
    exact Subgroup.mem_top g
  have hbOne : b = 1 := by
    have : b ∈ (⊥ : Subgroup G) := by
      rw [← center_eq_bot_of_noncommutative hnonab]
      exact hbCenter
    simpa using this
  subst b
  simp at hb

private lemma normalCore_centralizer_singleton_eq_bot_of_orderOf_eq_two {G : Type*}
    [Group G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) {b : G}
    (hb : orderOf b = 2) :
    (Subgroup.centralizer {b}).normalCore = ⊥ := by
  let H := Subgroup.centralizer {b}
  rcases H.normalCore_normal.eq_bot_or_eq_top with hbot | htop
  · exact hbot
  · exfalso
    apply centralizer_singleton_ne_top_of_orderOf_eq_two hnonab hb
    apply top_unique
    rw [← htop]
    exact H.normalCore_le

private lemma faithfulSMul_quotient_centralizer_singleton_of_orderOf_eq_two {G : Type*}
    [Group G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) {b : G}
    (hb : orderOf b = 2) :
    FaithfulSMul G (G ⧸ Subgroup.centralizer {b}) := by
  let H := Subgroup.centralizer {b}
  rw [faithfulSMul_iff]
  intro g hg
  have hgKer : g ∈ (MulAction.toPermHom G (G ⧸ H)).ker := by
    rw [MonoidHom.mem_ker]
    apply Equiv.ext
    intro q
    change g • q = q
    exact hg q
  have hgCore : g ∈ H.normalCore := by
    rw [H.normalCore_eq_ker]
    exact hgKer
  rw [normalCore_centralizer_singleton_eq_bot_of_orderOf_eq_two hnonab hb] at hgCore
  simpa using hgCore

noncomputable local instance quotientFintype {G : Type*} [Group G] [Finite G]
    {H : Subgroup G} : Fintype (G ⧸ H) :=
  Fintype.ofFinite (G ⧸ H)

noncomputable local instance quotientDecidableEq {G : Type*} [Group G]
    {H : Subgroup G} : DecidableEq (G ⧸ H) :=
  Classical.decEq (G ⧸ H)

private lemma cosetAction_mem_alternating_of_noncommutative {G : Type*} [Group G] [Finite G]
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) (H : Subgroup G) (g : G) :
    MulAction.toPerm g ∈ alternatingGroup (G ⧸ H) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  have hgComm : g ∈ commutator G := by
    rw [commutator_eq_top_of_noncommutative hnonab]
    exact Subgroup.mem_top g
  exact MonoidHom.mem_ker.mp
    (Abelianization.commutator_subset_ker
      (Equiv.Perm.sign.comp (MulAction.toPermHom G (G ⧸ H))) hgComm)

private noncomputable def cosetActionMulEquivRange {G : Type*} [Group G]
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) {b : G}
    (hb : orderOf b = 2) :
    G ≃* (MulAction.toPermHom G (G ⧸ Subgroup.centralizer {b})).range := by
  letI : FaithfulSMul G (G ⧸ Subgroup.centralizer {b}) :=
    faithfulSMul_quotient_centralizer_singleton_of_orderOf_eq_two hnonab hb
  exact Equiv.Perm.subgroupOfMulAction G (G ⧸ Subgroup.centralizer {b})

private lemma cosetAction_range_le_alternating_of_noncommutative {G : Type*} [Group G]
    [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (H : Subgroup G) :
    (MulAction.toPermHom G (G ⧸ H)).range ≤ alternatingGroup (G ⧸ H) := by
  rintro σ ⟨g, rfl⟩
  exact cosetAction_mem_alternating_of_noncommutative hnonab H g

lemma exists_faithful_odd_degree_alternating_coset_representation {G : Type*}
    [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (P : Sylow 2 G) {m : ℕ}
    (hm : 0 < m) (e : P ≃* DihedralGroup (2 ^ m)) :
    ∃ b : G,
      orderOf b = 2 ∧ Odd (Nat.card (G ⧸ Subgroup.centralizer {b})) ∧
      Nonempty
        (G ≃* (MulAction.toPermHom G (G ⧸ Subgroup.centralizer {b})).range) ∧
      (MulAction.toPermHom G (G ⧸ Subgroup.centralizer {b})).range ≤
        alternatingGroup (G ⧸ Subgroup.centralizer {b}) := by
  obtain ⟨b, hbOrder, hbOdd, -⟩ :=
    exists_involution_with_odd_centralizer_index_of_dihedral_two_pow hnonab P hm e
  refine ⟨(b : G), hbOrder, ?_, ⟨cosetActionMulEquivRange hnonab hbOrder⟩, ?_⟩
  · rw [← (Subgroup.centralizer ({(b : G)} : Set G)).index_eq_card]
    exact hbOdd
  · exact cosetAction_range_le_alternating_of_noncommutative hnonab _

private lemma normalCore_eq_bot_of_ne_top {G : Type*} [Group G] [IsSimpleGroup G]
    (H : Subgroup G) (hH : H ≠ ⊤) : H.normalCore = ⊥ := by
  rcases H.normalCore_normal.eq_bot_or_eq_top with hbot | htop
  · exact hbot
  · exfalso
    apply hH
    apply top_unique
    rw [← htop]
    exact H.normalCore_le

private lemma faithfulSMul_quotient_of_normalCore_eq_bot {G : Type*} [Group G]
    (H : Subgroup G) (hcore : H.normalCore = ⊥) : FaithfulSMul G (G ⧸ H) := by
  rw [faithfulSMul_iff]
  intro g hg
  have hgKer : g ∈ (MulAction.toPermHom G (G ⧸ H)).ker := by
    rw [MonoidHom.mem_ker]
    apply Equiv.ext
    intro q
    change g • q = q
    exact hg q
  have hgCore : g ∈ H.normalCore := by
    rw [H.normalCore_eq_ker]
    exact hgKer
  rw [hcore] at hgCore
  simpa using hgCore

private noncomputable def cosetActionMulEquivRangeOfNormalCoreEqBot {G : Type*} [Group G]
    (H : Subgroup G) (hcore : H.normalCore = ⊥) :
    G ≃* (MulAction.toPermHom G (G ⧸ H)).range := by
  letI : FaithfulSMul G (G ⧸ H) :=
    faithfulSMul_quotient_of_normalCore_eq_bot H hcore
  exact Equiv.Perm.subgroupOfMulAction G (G ⧸ H)

private lemma exists_odd_index_isCoatom_above {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) (hH : H ≠ ⊤) (hOdd : Odd H.index) :
    ∃ M : Subgroup G, IsCoatom M ∧ H ≤ M ∧ Odd M.index := by
  rcases eq_top_or_exists_le_coatom H with htop | ⟨M, hM, hHM⟩
  · exact (hH htop).elim
  · refine ⟨M, hM, hHM, ?_⟩
    have hMul : Odd (H.relIndex M * M.index) := by
      rw [H.relIndex_mul_index hHM]
      exact hOdd
    exact (Nat.odd_mul.mp hMul).2

private lemma exists_sylow_le_involution_centralizer_of_dihedral_two_pow {G : Type*}
    [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (P : Sylow 2 G) {m : ℕ}
    (hm : 0 < m) (e : P ≃* DihedralGroup (2 ^ m)) :
    ∃ b : G, ∃ Q : Sylow 2 G,
      orderOf b = 2 ∧ (Q : Subgroup G) ≤ Subgroup.centralizer {b} ∧
      Subgroup.normalClosure {b} = ⊤ := by
  rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr hm.ne') with hmOne | hmLarge
  · subst m
    let : Nontrivial P := e.toEquiv.nontrivial
    let : IsKleinFour P :=
      { card_four := by
          calc
            Nat.card P = Nat.card (DihedralGroup 2) := Nat.card_congr e.toEquiv
            _ = 4 := by simp
        exponent_two :=
          (Monoid.exponent_eq_of_mulEquiv e).trans (by simp) }
    obtain ⟨b, hb⟩ := exists_ne (1 : P)
    have hbCenter : b ∈ Subgroup.center P := by
      apply (Subgroup.mem_center_iff (G := (P : Subgroup G))).mpr
      exact fun g ↦ isMulCommutative_iff.mp IsKleinFour.isMulCommutative g b
    have hbOrder : orderOf (b : G) = 2 := by
      calc
        orderOf (b : G) = orderOf b :=
          orderOf_injective (P : Subgroup G).subtype
            (P : Subgroup G).subtype_injective b
        _ = 2 := (orderOf_eq_two_iff IsKleinFour.exponent_two).mpr hb
    have hPLe : (P : Subgroup G) ≤ Subgroup.centralizer {(b : G)} :=
      (sylow_le_centralizer_singleton_iff_mem_center P b).mpr hbCenter
    exact ⟨b, P, hbOrder, hPLe,
      normalClosure_singleton_eq_top_of_orderOf_eq_two hbOrder⟩
  · obtain ⟨-, b, u, -, -, -, hbOrder, -, hconjLe, -⟩ :=
      exists_distinct_conjugate_sylow_in_involution_centralizer
        hnonab P hmLarge e
    exact ⟨b, u • P, hbOrder, hconjLe,
      normalClosure_singleton_eq_top_of_orderOf_eq_two hbOrder⟩

private lemma involution_mem_sylow_of_sylow_le_centralizer {G : Type*} [Group G]
    {b : G} (Q : Sylow 2 G) (hbOrder : orderOf b = 2)
    (hQ : (Q : Subgroup G) ≤ Subgroup.centralizer {b}) : b ∈ Q := by
  have hbCentralizesQ : b ∈ Subgroup.centralizer (Q : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact Subgroup.mem_centralizer_singleton_iff.mp (hQ hq)
  have hZPowers : IsPGroup 2 (Subgroup.zpowers b) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hbOrder, pow_one]
  have hZPowersNormalizesQ :
      Subgroup.zpowers b ≤ Subgroup.normalizer (Q : Subgroup G) :=
    (Subgroup.zpowers_le.mpr hbCentralizesQ).trans
      (Subgroup.centralizer_le_normalizer (Q : Set G))
  have hSup :
      IsPGroup 2 (Subgroup.zpowers b ⊔ (Q : Subgroup G) : Subgroup G) :=
    hZPowers.to_sup_of_normal_right' Q.isPGroup' hZPowersNormalizesQ
  have hSupEq : Subgroup.zpowers b ⊔ (Q : Subgroup G) = Q :=
    Q.is_maximal' hSup le_sup_right
  change b ∈ (Q : Subgroup G)
  rw [← hSupEq]
  exact (le_sup_left : Subgroup.zpowers b ≤
    Subgroup.zpowers b ⊔ (Q : Subgroup G)) (Subgroup.mem_zpowers b)

private lemma involution_mem_center_sylow_of_sylow_le_centralizer {G : Type*} [Group G]
    {b : G} (Q : Sylow 2 G) (hbOrder : orderOf b = 2)
    (hQ : (Q : Subgroup G) ≤ Subgroup.centralizer {b}) :
    (⟨b, involution_mem_sylow_of_sylow_le_centralizer Q hbOrder hQ⟩ : Q) ∈
      Subgroup.center Q := by
  apply (Subgroup.mem_center_iff (G := Q)).mpr
  intro q
  apply Subtype.ext
  simpa using Subgroup.mem_centralizer_singleton_iff.mp (hQ q.2)

private lemma four_dvd_card_support_of_orderOf_eq_two_mem_alternating {α : Type*}
    [Fintype α] [DecidableEq α] {σ : Equiv.Perm α}
    (hσOrder : orderOf σ = 2) (hσEven : σ ∈ alternatingGroup α) :
    4 ∣ σ.support.card := by
  have hσSq : σ ^ 2 = 1 := by
    simpa [hσOrder] using pow_orderOf_eq_one σ
  have hSupportEven : 2 ∣ σ.support.card :=
    Equiv.Perm.two_dvd_card_support hσSq
  have hSupportFormula :
      Fintype.card α - Fintype.card (Function.fixedPoints σ) = σ.support.card := by
    rw [Equiv.Perm.card_fixedPoints, Nat.sub_sub_self σ.sum_cycleType_le,
      Equiv.Perm.sum_cycleType]
  have hSign := Equiv.Perm.sign_of_pow_two_eq_one hσSq
  rw [Equiv.Perm.mem_alternatingGroup.mp hσEven, hSupportFormula] at hSign
  have hHalfEven : Even (σ.support.card / 2) := by
    rcases Nat.even_or_odd (σ.support.card / 2) with hEven | hOdd
    · exact hEven
    · rw [hOdd.neg_one_pow] at hSign
      norm_num at hSign
  obtain ⟨k, hk⟩ := hSupportEven
  obtain ⟨l, hl⟩ := hHalfEven
  refine ⟨l, ?_⟩
  omega

private lemma card_support_eq_four_or_eight_le_of_orderOf_eq_two_mem_alternating
    {α : Type*} [Fintype α] [DecidableEq α] {σ : Equiv.Perm α}
    (hσOrder : orderOf σ = 2) (hσEven : σ ∈ alternatingGroup α) :
    σ.support.card = 4 ∨ 8 ≤ σ.support.card := by
  have hσNe : σ ≠ 1 := by
    intro hσ
    have : orderOf σ = 1 := orderOf_eq_one_iff.mpr hσ
    omega
  have hSupportNe : σ.support.card ≠ 0 :=
    (Equiv.Perm.card_support_eq_zero.not).mpr hσNe
  obtain ⟨k, hk⟩ :=
    four_dvd_card_support_of_orderOf_eq_two_mem_alternating hσOrder hσEven
  omega

private lemma card_support_eq_four_or_eight_le_of_faithful_even_involution
    {G : Type*} [Group G] [Finite G] (M : Subgroup G)
    (hcore : M.normalCore = ⊥) {b : G} (hbOrder : orderOf b = 2)
    (hbEven : MulAction.toPerm b ∈ alternatingGroup (G ⧸ M)) :
    (MulAction.toPermHom G (G ⧸ M) b).support.card = 4 ∨
      8 ≤ (MulAction.toPermHom G (G ⧸ M) b).support.card := by
  let : FaithfulSMul G (G ⧸ M) :=
    faithfulSMul_quotient_of_normalCore_eq_bot M hcore
  have hbPermOrder : orderOf (MulAction.toPerm b : Equiv.Perm (G ⧸ M)) = 2 := by
    calc
      orderOf (MulAction.toPerm b : Equiv.Perm (G ⧸ M)) = orderOf b := by
        simpa using orderOf_injective (MulAction.toPermHom G (G ⧸ M))
          (MulAction.toPerm_injective (α := G) (β := G ⧸ M)) b
      _ = 2 := hbOrder
  exact card_support_eq_four_or_eight_le_of_orderOf_eq_two_mem_alternating
    hbPermOrder hbEven

lemma cosetAction_range_eq_alternating_of_involution_support_inter_card_one
    {G : Type*} [Group G] [Finite G] (M : Subgroup G)
    (hPrimitive : MulAction.IsPreprimitive G (G ⧸ M))
    (hAlternating : (MulAction.toPermHom G (G ⧸ M)).range ≤
      alternatingGroup (G ⧸ M)) {b : G} (hbOrder : orderOf b = 2)
    {τ : Equiv.Perm (G ⧸ M)}
    (hτMem : τ ∈ (MulAction.toPermHom G (G ⧸ M)).range)
    (hτSq : τ ^ 2 = 1)
    (hInter : ((MulAction.toPermHom G (G ⧸ M) b).support ∩ τ.support).card = 1) :
    (MulAction.toPermHom G (G ⧸ M)).range = alternatingGroup (G ⧸ M) := by
  let φ := MulAction.toPermHom G (G ⧸ M)
  let H := φ.range
  let : MulAction.IsPreprimitive G (G ⧸ M) := hPrimitive
  let f : (G ⧸ M) →ₑ[φ.rangeRestrict] (G ⧸ M) :=
    { toFun := id
      map_smul' := fun _ _ ↦ rfl }
  have hRangePrimitive : MulAction.IsPreprimitive H (G ⧸ M) :=
    MulAction.IsPreprimitive.of_surjective (f := f) Function.surjective_id
  have hbSq : b ^ 2 = 1 := by
    simpa [hbOrder] using pow_orderOf_eq_one b
  have hbPermSq : φ b ^ 2 = 1 := by
    rw [← map_pow, hbSq, map_one]
  exact Support.subgroup_eq_alternatingGroup_of_involution_support_inter_card_one
    H hRangePrimitive hAlternating ⟨b, rfl⟩ hτMem hbPermSq hτSq hInter

private lemma five_le_card_quotient_of_faithful_even_involution {G : Type*} [Group G]
    [Finite G] (M : Subgroup G) (hcore : M.normalCore = ⊥) {b : G}
    (hbOrder : orderOf b = 2)
    (hbEven : MulAction.toPerm b ∈ alternatingGroup (G ⧸ M)) :
    Odd (Nat.card (G ⧸ M)) → 5 ≤ Nat.card (G ⧸ M) := by
  intro hOdd
  let : FaithfulSMul G (G ⧸ M) :=
    faithfulSMul_quotient_of_normalCore_eq_bot M hcore
  let σ : Equiv.Perm (G ⧸ M) := MulAction.toPerm b
  have hσOrder : orderOf σ = 2 := by
    calc
      orderOf σ = orderOf b := by
        simpa [σ] using orderOf_injective (MulAction.toPermHom G (G ⧸ M))
          (MulAction.toPerm_injective (α := G) (β := G ⧸ M)) b
      _ = 2 := hbOrder
  have hσSq : σ ^ 2 = 1 := by
    simpa [hσOrder] using pow_orderOf_eq_one σ
  have hσNe : σ ≠ 1 := by
    intro hσ
    have : orderOf σ = 1 := orderOf_eq_one_iff.mpr hσ
    omega
  have hSupportNeTwo : σ.support.card ≠ 2 := by
    intro hSupport
    have hSwap : σ.IsSwap := Equiv.Perm.card_support_eq_two.mp hSupport
    have hSign : Equiv.Perm.sign σ = 1 :=
      Equiv.Perm.mem_alternatingGroup.mp hbEven
    have hSignSwap := hSwap.sign_eq
    rw [hSign] at hSignSwap
    norm_num at hSignSwap
  have hSupportFour : 4 ≤ σ.support.card := by
    have hSupportTwo := Equiv.Perm.two_le_card_support_of_ne_one hσNe
    have hSupportEven := Equiv.Perm.two_dvd_card_support hσSq
    omega
  have hDegreeFour : 4 ≤ Nat.card (G ⧸ M) := by
    calc
      4 ≤ σ.support.card := hSupportFour
      _ ≤ Fintype.card (G ⧸ M) := σ.support.card_le_univ
      _ = Nat.card (G ⧸ M) := Fintype.card_eq_nat_card
  obtain ⟨k, hk⟩ := hOdd
  omega

private lemma exists_faithful_primitive_odd_degree_alternating_coset_representation
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (P : Sylow 2 G) {m : ℕ}
    (hm : 0 < m) (e : P ≃* DihedralGroup (2 ^ m)) :
    ∃ b : G, ∃ Q : Sylow 2 G, ∃ M : Subgroup G,
      orderOf b = 2 ∧ b ∈ Q ∧
      Nonempty (Q ≃* DihedralGroup (2 ^ m)) ∧
      (Q : Subgroup G) ≤ Subgroup.centralizer {b} ∧
      Subgroup.centralizer {b} ≤ M ∧ (Q : Subgroup G) ≤ M ∧ IsCoatom M ∧
      Odd (Nat.card (G ⧸ M)) ∧ 5 ≤ Nat.card (G ⧸ M) ∧
      ((MulAction.toPermHom G (G ⧸ M) b).support.card = 4 ∨
        8 ≤ (MulAction.toPermHom G (G ⧸ M) b).support.card) ∧
      M.normalCore = ⊥ ∧
      MulAction.IsPreprimitive G (G ⧸ M) ∧
      Nonempty (G ≃* (MulAction.toPermHom G (G ⧸ M)).range) ∧
      (MulAction.toPermHom G (G ⧸ M)).range ≤ alternatingGroup (G ⧸ M) := by
  obtain ⟨b, Q, hbOrder, hQH, -⟩ :=
    exists_sylow_le_involution_centralizer_of_dihedral_two_pow hnonab P hm e
  have hbQ : b ∈ Q :=
    involution_mem_sylow_of_sylow_le_centralizer Q hbOrder hQH
  have hQDihedral : Nonempty (Q ≃* DihedralGroup (2 ^ m)) :=
    ⟨(P.equiv Q).symm.trans e⟩
  let H := Subgroup.centralizer {(b : G)}
  have hHne : H ≠ ⊤ :=
    centralizer_singleton_ne_top_of_orderOf_eq_two hnonab hbOrder
  have hbOdd : Odd H.index := odd_index_of_sylow_le Q H hQH
  obtain ⟨M, hM, hHM, hMOdd⟩ := exists_odd_index_isCoatom_above H hHne hbOdd
  have hQM : (Q : Subgroup G) ≤ M := hQH.trans hHM
  have hMne : M ≠ ⊤ := hM.1
  have hcore : M.normalCore = ⊥ := normalCore_eq_bot_of_ne_top M hMne
  have hMOddCard : Odd (Nat.card (G ⧸ M)) := by
    rw [← M.index_eq_card]
    exact hMOdd
  have hDegreeFive : 5 ≤ Nat.card (G ⧸ M) :=
    five_le_card_quotient_of_faithful_even_involution M hcore hbOrder
      (cosetAction_mem_alternating_of_noncommutative hnonab M b) hMOddCard
  have hSupportDichotomy :
      (MulAction.toPermHom G (G ⧸ M) b).support.card = 4 ∨
        8 ≤ (MulAction.toPermHom G (G ⧸ M) b).support.card :=
    card_support_eq_four_or_eight_le_of_faithful_even_involution M hcore hbOrder
      (cosetAction_mem_alternating_of_noncommutative hnonab M b)
  let : Nontrivial (G ⧸ M) := QuotientGroup.nontrivial_iff.mpr hMne
  have hprim : MulAction.IsPreprimitive G (G ⧸ M) := by
    rw [← MulAction.isCoatom_stabilizer_iff_preprimitive G ((1 : G) : G ⧸ M),
      MulAction.stabilizer_quotient]
    exact hM
  refine ⟨b, Q, M, hbOrder, hbQ, hQDihedral, hQH, hHM, hQM, hM, hMOddCard,
    hDegreeFive, hSupportDichotomy, hcore, hprim,
    ⟨cosetActionMulEquivRangeOfNormalCoreEqBot M hcore⟩, ?_⟩
  · exact cosetAction_range_le_alternating_of_noncommutative hnonab M

lemma exists_faithful_primitive_odd_degree_alternating_coset_representation_with_central_involution
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (P : Sylow 2 G) {m : ℕ}
    (hm : 0 < m) (e : P ≃* DihedralGroup (2 ^ m)) :
    ∃ Q : Sylow 2 G, ∃ b : Q, ∃ M : Subgroup G,
      orderOf (b : G) = 2 ∧ b ∈ Subgroup.center Q ∧
      Nonempty (Q ≃* DihedralGroup (2 ^ m)) ∧
      (Q : Subgroup G) ≤ Subgroup.centralizer {(b : G)} ∧
      Subgroup.centralizer {(b : G)} ≤ M ∧ (Q : Subgroup G) ≤ M ∧
      IsCoatom M ∧
      Odd (Nat.card (G ⧸ M)) ∧ 5 ≤ Nat.card (G ⧸ M) ∧
      ((MulAction.toPermHom G (G ⧸ M) (b : G)).support.card = 4 ∨
        8 ≤ (MulAction.toPermHom G (G ⧸ M) (b : G)).support.card) ∧
      M.normalCore = ⊥ ∧
      MulAction.IsPreprimitive G (G ⧸ M) ∧
      Nonempty (G ≃* (MulAction.toPermHom G (G ⧸ M)).range) ∧
      (MulAction.toPermHom G (G ⧸ M)).range ≤ alternatingGroup (G ⧸ M) := by
  obtain ⟨b, Q, M, hbOrder, hbQ, hQDihedral, hQH, hHM, hQM, hM, hMOdd,
      hDegreeFive, hSupportDichotomy, hcore, hprim, hEquiv, hAlternating⟩ :=
    exists_faithful_primitive_odd_degree_alternating_coset_representation
      hnonab P hm e
  let bQ : Q := ⟨b, hbQ⟩
  have hbCenter : bQ ∈ Subgroup.center Q := by
    dsimp [bQ]
    simpa using involution_mem_center_sylow_of_sylow_le_centralizer Q hbOrder hQH
  exact ⟨Q, bQ, M, hbOrder, hbCenter, hQDihedral, hQH, hHM, hQM, hM, hMOdd,
    hDegreeFive, hSupportDichotomy, hcore, hprim, hEquiv, hAlternating⟩

end GorensteinWalter.Helpers

end CFSG
