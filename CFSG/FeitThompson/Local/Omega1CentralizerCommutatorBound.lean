module

public import CFSG.FeitThompson.Local.ClassTwoPrimeTorsionCharacteristic
public import CFSG.FeitThompson.Local.AutomorphismsFixingSubgroupQuotientCommute
import CFSG.FeitThompson.Local.DisplacementOddPrimeOrderAutomorphism
public import Mathlib.Algebra.Module.Torsion.Basic

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup

section Aut

variable {A : Type*} [CommGroup A] {p n : ℕ}

theorem mem_torsionBy_additive_iff {d : Additive A} :
    d ∈ AddSubgroup.torsionBy (Additive A) (p : ℤ) ↔ (Additive.toMul d : A) ^ p = 1 := by
  rw [AddSubgroup.torsionBy.nsmul_iff,
    show (p • d : Additive A) = Additive.ofMul ((Additive.toMul d : A) ^ p) from
      (ofMul_pow (α := A) p (Additive.toMul d)).symm,
    ← ofMul_one, Equiv.apply_eq_iff_eq]

theorem iterate_toAdditive_eq_id {u : MulAut A} (hup : u ^ p = 1) :
    (⇑(MulEquiv.toAdditive u))^[p] = id := by
  have h : ∀ (k : ℕ) (b : A), (⇑(MulEquiv.toAdditive u))^[k] (Additive.ofMul b)
      = Additive.ofMul ((u ^ k) b) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro b
      rw [Function.iterate_succ_apply,
        show MulEquiv.toAdditive u (Additive.ofMul b) = Additive.ofMul (u b) from rfl, ih (u b),
        pow_succ, MulAut.mul_apply]
  ext a
  have := h p (Additive.toMul a)
  rw [hup] at this
  simpa using this

theorem toAdditive_mem_twoSectionStabilizer (hp : p.Prime) (hodd : Odd p)
    (hcard : Nat.card A = p ^ n) {u : MulAut A} (hup : u ^ p = 1)
    (hufix : ∀ a : A, a ^ p = 1 → u a = a) :
    MulEquiv.toAdditive u ∈
      twoSectionStabilizer (AddSubgroup.torsionBy (Additive A) (p : ℤ)) := by
  have hcard' : Nat.card (Additive A) = p ^ n := by
    rw [← hcard]; exact Nat.card_congr (Additive.ofMul (α := A)).symm
  have hfix' : ∀ b : Additive A, p • b = 0 → MulEquiv.toAdditive u b = b := by
    intro b hb
    have h1 : (Additive.toMul b : A) ^ p = 1 :=
      mem_torsionBy_additive_iff.mp (AddSubgroup.torsionBy.nsmul_iff.2 hb)
    change Additive.ofMul (u (Additive.toMul b)) = b
    rw [hufix _ h1]
    rfl
  refine mem_twoSectionStabilizer_of (fun d hd => hfix' d (AddSubgroup.torsionBy.nsmul_iff.1 hd))
    fun a => AddSubgroup.torsionBy.nsmul_iff.2 ?_
  exact nsmul_apply_sub_self_eq_zero hp hodd hcard' _ (iterate_toAdditive_eq_id hup) hfix' a

theorem commute_of_pow_eq_one_of_fix_prime_torsion (hp : p.Prime) (hodd : Odd p)
    (hcard : Nat.card A = p ^ n) {t s : MulAut A} (htp : t ^ p = 1) (hsp : s ^ p = 1)
    (htfix : ∀ a : A, a ^ p = 1 → t a = a) (hsfix : ∀ a : A, a ^ p = 1 → s a = a) :
    t * s = s * t := by
  have hcomm := add_comm_of_mem_twoSectionStabilizer
    (toAdditive_mem_twoSectionStabilizer hp hodd hcard htp htfix)
    (toAdditive_mem_twoSectionStabilizer hp hodd hcard hsp hsfix)
  refine MulEquiv.ext fun a => ?_
  have h := congrArg (fun f : AddAut (Additive A) => f (Additive.ofMul a)) hcomm
  simp only [AddAut.add_apply] at h
  exact h

end Aut

variable {P : Type*} [Group P] {p n : ℕ}

theorem conjNormal_ker (B : Subgroup P) [B.Normal] :
    (MulAut.conjNormal (G := P) (H := B)).ker = centralizer (B : Set P) := by
  ext x
  simp only [MonoidHom.mem_ker, mem_centralizer_iff]
  refine ⟨fun h a ha => ?_, fun h => ?_⟩
  · have h2 := congrArg (fun f => (f (⟨a, ha⟩ : ↥B) : P)) h
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h2
    nth_rewrite 1 [← h2]; group
  · ext a
    rw [MulAut.conjNormal_apply]
    simp only [MulAut.one_apply]
    rw [← h a a.2]; group

theorem coe_map_omega1_subtype (K : Subgroup P) :
    ((omega1 p ↥K).map K.subtype : Subgroup P) = closure {x : P | x ∈ K ∧ x ^ p = 1} := by
  rw [omega1_eq_closure, MonoidHom.map_closure]
  congr 1
  ext y
  simp only [Set.mem_image, Set.mem_ofPred_eq, coe_subtype]
  refine ⟨?_, ?_⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, by simpa using congrArg Subtype.val hx⟩
  · rintro ⟨hy, hyp⟩
    exact ⟨⟨y, hy⟩, Subtype.ext (by simpa using hyp), rfl⟩

def pTorsionSet (p : ℕ) (B : Subgroup P) : Set P := {a : P | a ∈ B ∧ a ^ p = 1}

theorem mem_pTorsionSet {B : Subgroup P} {a : P} :
    a ∈ pTorsionSet p B ↔ a ∈ B ∧ a ^ p = 1 := Iff.rfl

theorem pTorsionSet_subset {B : Subgroup P} : pTorsionSet p B ⊆ (B : Set P) := fun _ h => h.1

theorem pTorsionSet_eq_coe_omega1_map (B : Subgroup P) [hB : IsMulCommutative ↥B] :
    pTorsionSet p B = (((omega1 p ↥B).map B.subtype : Subgroup P) : Set P) := by
  rw [coe_map_omega1_subtype]
  refine Set.Subset.antisymm (fun x hx => subset_closure hx) ?_
  intro x hx
  induction hx using closure_induction with
  | mem x hx => exact hx
  | one => exact ⟨one_mem _, one_pow p⟩
  | mul a b _ _ ha hb =>
    refine ⟨mul_mem ha.1 hb.1, ?_⟩
    have hcomm : a * b = b * a := by
      simpa using congrArg Subtype.val (hB.is_comm.comm (⟨a, ha.1⟩ : ↥B) ⟨b, hb.1⟩)
    rw [Commute.mul_pow hcomm p, ha.2, hb.2, one_mul]
  | inv a _ ha => exact ⟨inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩

def omega1Centralizer (p : ℕ) (B : Subgroup P) : Subgroup P :=
  (omega1 p ↥(centralizer (pTorsionSet p B))).map (centralizer (pTorsionSet p B)).subtype

theorem omega1Centralizer_eq_closure {B : Subgroup P} :
    omega1Centralizer p B = closure {x : P | x ∈ centralizer (pTorsionSet p B) ∧ x ^ p = 1} :=
  coe_map_omega1_subtype _

theorem omega1Centralizer_le_centralizer {B : Subgroup P} :
    omega1Centralizer p B ≤ centralizer (pTorsionSet p B) := by
  rw [omega1Centralizer_eq_closure]
  exact (closure_le _).2 fun _ hx => hx.1

theorem mem_omega1Centralizer_of {B : Subgroup P} {x : P}
    (hx : x ∈ centralizer (pTorsionSet p B)) (hxp : x ^ p = 1) : x ∈ omega1Centralizer p B := by
  rw [omega1Centralizer_eq_closure]; exact subset_closure ⟨hx, hxp⟩

variable (B : Subgroup P) [B.Normal] [IsMulCommutative ↥B]

theorem commutator_omega1Centralizer_le (hp : p.Prime) (hodd : Odd p)
    (hcard : Nat.card P = p ^ n) (hcent : centralizer (B : Set P) = B) :
    ⁅omega1Centralizer p B, omega1Centralizer p B⁆ ≤ B := by
  let _iB : CommGroup ↥B := IsMulCommutative.instCommGroup
  have : Fact p.Prime := ⟨hp⟩
  have : Finite P := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hp.pos.ne')
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp ((IsPGroup.of_card hcard).to_subgroup B)
  set φ := MulAut.conjNormal (G := P) (H := B) with hφ
  set S : Set P := {x : P | x ∈ centralizer (pTorsionSet p B) ∧ x ^ p = 1} with hS
  have hgen : ∀ x ∈ S, (φ x) ^ p = 1 ∧ ∀ a : ↥B, a ^ p = 1 → φ x a = a := by
    rintro x ⟨hx1, hx2⟩
    refine ⟨by rw [← map_pow, hx2, map_one], fun a ha => ?_⟩
    have hap : (a : P) ^ p = 1 := by simpa using congrArg Subtype.val ha
    have hcm := (mem_centralizer_iff.mp hx1) (a : P) ⟨a.2, hap⟩
    refine Subtype.ext ?_
    rw [hφ, MulAut.conjNormal_apply, ← hcm]
    group
  have himgcomm : IsMulCommutative ↥(map φ (omega1Centralizer p B)) := by
    rw [omega1Centralizer_eq_closure, ← hS, MonoidHom.map_closure]
    refine isMulCommutative_closure ?_
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ -
    exact commute_of_pow_eq_one_of_fix_prime_torsion hp hodd hm (hgen x hx).1 (hgen y hy).1
      (hgen x hx).2 (hgen y hy).2
  have hbot : map φ ⁅omega1Centralizer p B, omega1Centralizer p B⁆ = ⊥ := by
    rw [map_commutator]
    exact commutator_self_eq_bot_iff.2 himgcomm
  rwa [Subgroup.map_eq_bot_iff, conjNormal_ker, hcent] at hbot

theorem isMulCommutative_commutator_omega1Centralizer (hp : p.Prime) (hodd : Odd p)
    (hcard : Nat.card P = p ^ n) (hcent : centralizer (B : Set P) = B) :
    IsMulCommutative ↥⁅omega1Centralizer p B, omega1Centralizer p B⁆ :=
  isMulCommutative_iff_of_setLike.2 fun _ ha _ hb =>
    setLike_mul_comm (s := B) (commutator_omega1Centralizer_le B hp hodd hcard hcent ha)
      (commutator_omega1Centralizer_le B hp hodd hcard hcent hb)

theorem mem_center_of_mem_commutator_of_pow_eq_one (hp : p.Prime) (hodd : Odd p)
    (hcard : Nat.card P = p ^ n) (hcent : centralizer (B : Set P) = B) {c : P}
    (hc : c ∈ ⁅omega1Centralizer p B, omega1Centralizer p B⁆) (hcp : c ^ p = 1) :
    (⟨c, commutator_le_self _ hc⟩ : ↥(omega1Centralizer p B)) ∈
      center ↥(omega1Centralizer p B) := by
  have hcD : c ∈ pTorsionSet p B :=
    ⟨commutator_omega1Centralizer_le B hp hodd hcard hcent hc, hcp⟩
  rw [mem_center_iff]
  intro g
  exact Subtype.ext (by
    simpa using ((mem_centralizer_iff.mp (omega1Centralizer_le_centralizer g.2)) c hcD).symm)

theorem mul_comm_of_mem_commutator_of_pow_eq_one (hp : p.Prime) (hodd : Odd p)
    (hcard : Nat.card P = p ^ n) (hcent : centralizer (B : Set P) = B) {c : P}
    (hc : c ∈ ⁅omega1Centralizer p B, omega1Centralizer p B⁆) (hcp : c ^ p = 1)
    {x : P} (hx : x ∈ omega1Centralizer p B) : x * c = c * x :=
  ((mem_centralizer_iff.mp (omega1Centralizer_le_centralizer hx)) c
    ⟨commutator_omega1Centralizer_le B hp hodd hcard hcent hc, hcp⟩).symm

end CFSG.FeitThompson
