module

public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.Foundations.HigherElementaryThompson
public import CFSG.LocalAnalysis.SignalizerFunctor.Maximality
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG Subgroup

section Defs

@[expose] def fixedIn (J : Type) [Group J] (S : Subgroup (MulAut J)) : Subgroup J where
  carrier := {x | ∀ φ ∈ S, φ x = x}
  mul_mem' := fun {a b} ha hb φ hφ => by rw [map_mul, ha φ hφ, hb φ hφ]
  one_mem' := fun φ _ => map_one φ
  inv_mem' := fun {a} ha φ hφ => by rw [map_inv, ha φ hφ]

theorem mem_fixedIn {J : Type} [Group J] {S : Subgroup (MulAut J)} {x : J} :
    x ∈ fixedIn J S ↔ ∀ φ ∈ S, φ x = x := Iff.rfl

@[expose] def NoOddNormal {J : Type} [Group J] (H : Subgroup J) : Prop :=
  ∀ N : Subgroup J, N ≤ H → Odd (Nat.card ↥N) → (∀ x ∈ H, x ∈ normalizer (N : Set J)) → N = ⊥

@[expose] def gammaAct {J : Type} [Group J] {A : Type} [Group A] (α : A →* MulAut J) : Subgroup J :=
  ⨆ (E : Subgroup A) (_ : pRank 2 A - 1 ≤ pRank 2 ↥E), fixedIn J (E.map α)

@[expose] def IsRank23 (A : Type) [Group A] : Prop :=
  CFSG.IsElementaryAbelian 2 A ∧ (pRank 2 A = 2 ∨ pRank 2 A = 3)

@[expose] def LocE1 {J : Type} [Group J] {A : Type} [Group A] (α : A →* MulAut J) : Prop :=
  ∀ E : Subgroup A, pRank 2 A - 1 ≤ pRank 2 ↥E → NoOddNormal (fixedIn J (E.map α))

@[expose] def LocE2 {J : Type} [Group J] {A : Type} [Group A] (α : A →* MulAut J) : Prop :=
  ∀ φ : MulAut J, Odd (orderOf φ) → (∀ x ∈ gammaAct α, φ x = x) → φ = 1

@[expose] def LocE3 {J : Type} [Group J] {A : Type} [Group A] (α : A →* MulAut J) : Prop :=
  ∃ E : Subgroup A, pRank 2 A - 1 ≤ pRank 2 ↥E ∧ ∃ x ∈ fixedIn J (E.map α),
    (∃ n : ℕ, x ^ (2 ^ n) = 1) ∧ ∃ y : J, y * x ≠ x * y

@[expose] def NC2 (J : Type) [Group J] : Prop :=
  ∃ x : J, (∃ n : ℕ, x ^ (2 ^ n) = 1) ∧ ∃ y : J, y * x ≠ x * y

@[expose] def GenProp (J : Type) [Group J] : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (α : A →* MulAut J), IsRank23 A → gammaAct α = ⊤

@[expose] def LocProp (J : Type) [Group J] : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (α : A →* MulAut J), IsRank23 A → LocE1 α ∧ LocE2 α ∧ LocE3 α

@[expose] def GenLoc (J : Type) [Group J] : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (α : A →* MulAut J), IsRank23 A →
    gammaAct α = ⊤ ∨ (LocE1 α ∧ LocE2 α ∧ LocE3 α)

theorem GenProp.genLoc {J : Type} [Group J] (h : GenProp J) : GenLoc J :=
  fun A _ _ α hA => Or.inl (h A α hA)

theorem LocProp.genLoc {J : Type} [Group J] (h : LocProp J) : GenLoc J :=
  fun A _ _ α hA => Or.inr (h A α hA)

end Defs

section Act

variable {Y : Type} [Group Y] {J : Type} [Group J]

@[expose] def conjL (L : Subgroup Y) (n : Y) (hn : n ∈ normalizer (L : Set Y)) : L ≃* L where
  toFun l := ⟨n * l * n⁻¹, (mem_normalizer_iff.mp hn _).mp l.2⟩
  invFun l := ⟨n⁻¹ * l * n, by simpa using (mem_normalizer_iff.mp (inv_mem hn) _).mp l.2⟩
  left_inv l := by apply Subtype.ext; simp [mul_assoc]
  right_inv l := by apply Subtype.ext; simp [mul_assoc]
  map_mul' a b := by apply Subtype.ext; simp [mul_assoc]

@[expose] def conjAut (L : Subgroup Y) (e : L ≃* J) (n : Y) (hn : n ∈ normalizer (L : Set Y)) :
    MulAut J :=
  (e.symm.trans (conjL L n hn)).trans e

theorem coe_symm_conjAut (L : Subgroup Y) (e : L ≃* J) (n : Y) (hn : n ∈ normalizer (L : Set Y))
    (x : J) : ((e.symm (conjAut L e n hn x) : L) : Y) = n * (e.symm x : Y) * n⁻¹ := by
  simp [conjAut, conjL]

@[expose] def actOn (L : Subgroup Y) (e : L ≃* J) : ↥(normalizer (L : Set Y)) →* MulAut J where
  toFun n := conjAut L e n n.2
  map_one' := by
    ext x
    apply e.symm.injective
    apply Subtype.ext
    rw [coe_symm_conjAut]
    simp
  map_mul' a b := by
    ext x
    apply e.symm.injective
    apply Subtype.ext
    rw [coe_symm_conjAut]
    simp only [MulAut.mul_apply]
    rw [coe_symm_conjAut, coe_symm_conjAut]
    simp [mul_assoc]

theorem coe_symm_actOn (L : Subgroup Y) (e : L ≃* J) (n : ↥(normalizer (L : Set Y))) (x : J) :
    ((e.symm (actOn L e n x) : L) : Y) = (n : Y) * (e.symm x : Y) * (n : Y)⁻¹ :=
  coe_symm_conjAut L e n n.2 x

end Act

namespace WeakSigGen

section Gen

variable {Y : Type} [Group Y]

theorem centralizes_of_normalize {L W : Subgroup Y} (hL : IsQuasisimple ↥L) (hL2 : 2 ∣ Nat.card ↥L)
    (hW : Odd (Nat.card ↥W)) (hLW : L ≤ normalizer (W : Set Y)) (hWL : W ≤ normalizer (L : Set Y)) :
    W ≤ centralizer (L : Set Y) := by
  have hN : ((L ⊓ W).subgroupOf L).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨hnL, hnW⟩ := hn
    refine ⟨?_, ?_⟩
    · exact L.mul_mem (L.mul_mem g.2 hnL) (L.inv_mem g.2)
    · exact (mem_normalizer_iff.mp (hLW g.2) _).mp hnW
  have hcen : ∀ y ∈ L ⊓ W, ∀ l ∈ L, l * y = y * l := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hL hN with h | h
    · exfalso
      have hLle : L ≤ W := by
        intro l hl
        have : (⟨l, hl⟩ : ↥L) ∈ (L ⊓ W).subgroupOf L := by rw [h]; trivial
        exact (Subgroup.mem_subgroupOf.mp this).2
      have hdvd : Nat.card ↥L ∣ Nat.card ↥W := Subgroup.card_dvd_of_le hLle
      have h2 : 2 ∣ Nat.card ↥W := hL2.trans hdvd
      exact (Nat.not_even_iff_odd.mpr hW) (even_iff_two_dvd.mpr h2)
    · intro y hy l hl
      have hy' : (⟨y, hy.1⟩ : ↥L) ∈ (L ⊓ W).subgroupOf L := hy
      have := Subgroup.mem_center_iff.mp (h hy') ⟨l, hl⟩
      exact congrArg Subtype.val this
  have hcomm : ⁅L, W⁆ ≤ L ⊓ W := by
    rw [Subgroup.commutator_le]
    intro l hl w hw
    have h1 : l * w * l⁻¹ * w⁻¹ ∈ W :=
      W.mul_mem ((mem_normalizer_iff.mp (hLW hl) w).mp hw) (W.inv_mem hw)
    have h2 : l * w * l⁻¹ * w⁻¹ ∈ L := by
      have := L.mul_mem hl ((mem_normalizer_iff.mp (hWL hw) l⁻¹).mp (L.inv_mem hl))
      simpa [mul_assoc] using this
    exact ⟨h2, h1⟩
  have hdbl : ⁅⁅L, W⁆, L⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro y hy
    rw [mem_centralizer_iff]
    intro l hl
    exact hcen y (hcomm hy) l hl
  have hLW1 : ⁅L, W⁆ = ⊥ := CFSG.LocalCores.perfect_double_commutator hL.1 hdbl
  rw [Subgroup.commutator_comm] at hLW1
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hLW1

theorem normalizes_of_noncentral_two_elt [Finite Y] {L W : Subgroup Y} (hL : IsComponent L)
    (hW : Odd (Nat.card ↥W)) {x : Y} (hxL : x ∈ L) (hxN : x ∈ normalizer (W : Set Y))
    (hx2 : ∃ n : ℕ, x ^ (2 ^ n) = 1) (hxc : ∃ y ∈ L, y * x ≠ x * y) :
    W ≤ normalizer (L : Set Y) := by
  intro w hw
  by_contra hwL
  let L' : Subgroup Y := L.map (MulAut.conj w).toMonoidHom
  have hL' : IsComponent L' := CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj w) hL
  have hne : L ≠ L' := by
    intro h
    apply hwL
    rw [mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      have : w * z * w⁻¹ ∈ L' := ⟨z, hz, by simp⟩
      rwa [← h] at this
    · intro hz
      rw [h] at hz
      obtain ⟨z', hz', hzz⟩ := hz
      have : z' = z := by
        have h1 : w * z' * w⁻¹ = w * z * w⁻¹ := by simpa using hzz
        have h2 := mul_left_cancel (mul_right_cancel h1)
        exact h2
      rwa [← this]
  have hcomm : L ≤ centralizer (L' : Set Y) := by
    rcases CFSG.LocalCores.distinct_components_commute hL hL' with h | h
    · exact absurd h hne
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
  have hx'L' : w * x * w⁻¹ ∈ L' := ⟨x, hxL, by simp⟩
  have hcW : (w * x * w⁻¹) * x⁻¹ ∈ W := by
    have h1 : x * w⁻¹ * x⁻¹ ∈ W := (mem_normalizer_iff.mp hxN w⁻¹).mp (W.inv_mem hw)
    have h2 : w * (x * w⁻¹ * x⁻¹) ∈ W := W.mul_mem hw h1
    simpa [mul_assoc] using h2
  have hxcomm : (w * x * w⁻¹) * x⁻¹ = x⁻¹ * (w * x * w⁻¹) := by
    exact Subgroup.mem_centralizer_iff.mp (hcomm (L.inv_mem hxL)) _ hx'L'
  obtain ⟨n, hn⟩ := hx2
  have hc2 : ((w * x * w⁻¹) * x⁻¹) ^ (2 ^ n) = 1 := by
    have hc : Commute (w * x * w⁻¹) x⁻¹ := hxcomm
    rw [hc.mul_pow, inv_pow, hn, inv_one, mul_one, conj_pow, hn]
    simp
  have hdvd : orderOf ((w * x * w⁻¹) * x⁻¹) ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hc2
  have hdvdW : orderOf ((w * x * w⁻¹) * x⁻¹) ∣ Nat.card ↥W := by
    have := Subgroup.orderOf_dvd_natCard W hcW
    exact this
  have hcop : Nat.Coprime (2 ^ n) (Nat.card ↥W) :=
    Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hW)
  have hord : orderOf ((w * x * w⁻¹) * x⁻¹) = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd hdvdW
  have hc1 : (w * x * w⁻¹) * x⁻¹ = 1 := orderOf_eq_one_iff.mp hord
  have hxx : w * x * w⁻¹ = x := mul_inv_eq_one.mp hc1
  obtain ⟨y, hyL, hyx⟩ := hxc
  apply hyx
  have hxL' : x ∈ L' := by rw [← hxx]; exact hx'L'
  exact (Subgroup.mem_centralizer_iff.mp (hcomm hyL) x hxL').symm

end Gen

section Rank

variable {G : Type} [Group G]

theorem card_eq_two_pow_pRank [Finite G] {U : Subgroup G} (h : CFSG.IsElementaryAbelian 2 ↥U) :
    Nat.card ↥U = 2 ^ pRank 2 ↥U := by
  have hp : IsPGroup 2 ↥U := CFSG.IsElementaryAbelian.isPGroup 2 ↥U
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hp
  rw [hk, CFSG.pRank_eq_of_card_eq_pow one_lt_two hk]

theorem isElementaryAbelian_of_forall {U : Subgroup G} (hab : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u)
    (hsq : ∀ u ∈ U, u * u = 1) : CFSG.IsElementaryAbelian 2 ↥U :=
  CFSG.IsElementaryAbelian.two_of_forall_mul_self hab hsq

theorem forall_of_isElementaryAbelian {U : Subgroup G} (h : CFSG.IsElementaryAbelian 2 ↥U) :
    (∀ u ∈ U, ∀ v ∈ U, u * v = v * u) ∧ (∀ u ∈ U, u * u = 1) := by
  refine ⟨fun u hu v hv => ?_, fun u hu => ?_⟩
  · have hc := mul_comm' (⟨u, hu⟩ : ↥U) ⟨v, hv⟩
    exact congrArg Subtype.val hc
  · have : (u : G) ^ 2 = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := U) u hu
    rwa [sq] at this

theorem mul_self_eq_one_of_isElementaryAbelian {A : Type} [Group A]
    (hA : CFSG.IsElementaryAbelian 2 A) (a : A) : a * a = 1 := by
  have h2 : a ^ 2 = 1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (CFSG.IsElementaryAbelian.exponent_dvd_p 2 A) a
  rwa [sq] at h2

theorem pRank_top_eq {A : Type} [Group A] [Finite A] (hA : CFSG.IsElementaryAbelian 2 A) :
    pRank 2 ↥(⊤ : Subgroup A) = pRank 2 A := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 (CFSG.IsElementaryAbelian.isPGroup 2 A)
  have h1 : pRank 2 A = k := CFSG.pRank_eq_of_card_eq_pow one_lt_two hk
  have htop : CFSG.IsElementaryAbelian 2 ↥(⊤ : Subgroup A) :=
    isElementaryAbelian_of_forall (fun u _ v _ => mul_comm' u v)
      (fun u _ => mul_self_eq_one_of_isElementaryAbelian hA u)
  have h2 : Nat.card ↥(⊤ : Subgroup A) = 2 ^ k := by rw [Subgroup.card_top]; exact hk
  rw [h1]
  exact CFSG.pRank_eq_of_card_eq_pow one_lt_two h2

theorem le_iSup_centralizer_hyperplanes [Finite G] {B Y' : Subgroup G}
    (hB : CFSG.IsElementaryAbelian 2 ↥B) (hr : 2 ≤ pRank 2 ↥B) (hBY : B ≤ normalizer (Y' : Set G))
    (hY : Odd (Nat.card ↥Y')) :
    Y' ≤ ⨆ (E : Subgroup G) (_ : E ≤ B) (_ : pRank 2 ↥B - 1 ≤ pRank 2 ↥E),
      Y' ⊓ centralizer (E : Set G) := by
  have hcard : Nat.card ↥B = 2 ^ pRank 2 ↥B := card_eq_two_pow_pRank hB
  obtain ⟨hab, hsq⟩ := forall_of_isElementaryAbelian hB
  have hElem : CFSG.Open.IsElemAbelian 2 B := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hab a a.2 b b.2)⟩⟩, fun x hx => ?_⟩
    rw [sq]
    exact hsq x hx
  have hlarge : 2 ^ (pRank 2 ↥B - 1 + 1) ≤ Nat.card ↥B := by
    rw [hcard]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hcop : Nat.Coprime 2 (Nat.card ↥Y') := Nat.coprime_two_left.2 hY
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 2
    (pRank 2 ↥B - 1) Nat.prime_two B Y' hElem hlarge hBY hcop
  refine le_of_eq_of_le hgen.symm ?_
  refine iSup_le fun S => iSup_le fun hS => ?_
  obtain ⟨hSB, hScard⟩ := hS
  have hSel : CFSG.IsElementaryAbelian 2 ↥S :=
    isElementaryAbelian_of_forall (fun u hu v hv => hab u (hSB hu) v (hSB hv))
      (fun u hu => hsq u (hSB hu))
  have hrank : pRank 2 ↥S = pRank 2 ↥B - 1 := CFSG.pRank_eq_of_card_eq_pow one_lt_two hScard
  exact le_iSup_of_le S (le_iSup_of_le hSB (le_iSup_of_le hrank.ge le_rfl))

theorem pRank_comap_subtype [Finite G] {D E' : Subgroup G} (hD : CFSG.IsElementaryAbelian 2 ↥D)
    (hE : E' ≤ D) : pRank 2 ↥(E'.comap D.subtype) = pRank 2 ↥E' := by
  obtain ⟨hab, hsq⟩ := forall_of_isElementaryAbelian hD
  have h1 : CFSG.IsElementaryAbelian 2 ↥E' :=
    isElementaryAbelian_of_forall (fun u hu v hv => hab u (hE hu) v (hE hv))
      (fun u hu => hsq u (hE hu))
  have h2 : CFSG.IsElementaryAbelian 2 ↥(E'.comap D.subtype) := by
    refine isElementaryAbelian_of_forall (G := ↥D) (fun u hu v hv => ?_) (fun u hu => ?_)
    · exact Subtype.ext (hab u.1 u.2 v.1 v.2)
    · exact Subtype.ext (hsq u.1 u.2)
  have hmap : (E'.comap D.subtype).map D.subtype = E' :=
    Subgroup.map_comap_eq_self (by rw [Subgroup.range_subtype]; exact hE)
  have hcard : Nat.card ↥(E'.comap D.subtype) = Nat.card ↥E' := by
    have := Subgroup.card_map_of_injective (K := E'.comap D.subtype) D.subtype_injective
    rw [hmap] at this
    exact this.symm
  have e1 := card_eq_two_pow_pRank h1
  have e2 := card_eq_two_pow_pRank h2
  rw [hcard] at e2
  exact Nat.pow_right_injective (le_refl 2) (e2.symm.trans e1)

end Rank

end WeakSigGen

end CFSG.GH74.Generic.BProg.B2
