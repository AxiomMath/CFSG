module

public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.FixedPointFree
public import Mathlib.GroupTheory.Nilpotent
import CFSG.FeitThompson.Local.FrobeniusWielandtFixedPointOrder
import CFSG.FeitThompson.Representations.FixedPointFreeComplementOrderBounds
import CFSG.FeitThompson.OddOrder.SemidirectReassociation

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {L : Type*} [Group L]

theorem fixedPointFree_conjNormal_of_inf_centralizer_eq_bot {H : Subgroup L} [H.Normal] {x : L}
    (hx : H ⊓ Subgroup.centralizer {x} = ⊥) :
    MonoidHom.FixedPointFree ((MulAut.conjNormal x : MulAut H) : H → H) := by
  intro h hfix
  have h1 : x * (h : L) * x⁻¹ = (h : L) := by
    simpa [MulAut.conjNormal_apply] using congrArg Subtype.val hfix
  have h2 : (h : L) ∈ H ⊓ Subgroup.centralizer {x} :=
    ⟨h.2, Subgroup.mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.mp h1).symm⟩
  rw [hx, Subgroup.mem_bot] at h2
  exact Subtype.ext h2

theorem natCard_fixedPoints_eq_one_of_mem_of_fixedPointFree {A K : Type*} [Group A] [Group K]
    (ρ : A →* MulAut K)
    {B : Subgroup A} {b : A} (hb : b ∈ B)
    (hfree : MonoidHom.FixedPointFree ((ρ b : MulAut K) : K → K)) :
    Nat.card {v : K // ∀ c ∈ B, ρ c v = v} = 1 := by
  rw [Nat.card_eq_one_iff_exists]
  exact ⟨⟨1, fun c _ => map_one _⟩, fun y => Subtype.ext (hfree _ (y.2 b hb))⟩

theorem false_of_frobenius_pair_le_free_complement
    [Finite L] [Group.IsSolvable L] {H E : Subgroup L} [H.Normal] (hH : H ≠ ⊥)
    (hfree : ∀ e ∈ E, e ≠ 1 → H ⊓ Subgroup.centralizer {e} = ⊥)
    {U V : Subgroup L} (hUE : U ≤ E) (hVE : V ≤ E) (hU : U ≠ ⊥) (hV : V ≠ ⊥)
    (hnorm : V ≤ Subgroup.normalizer (U : Set L)) (hUV : U ⊓ V = ⊥)
    (hUfree : ∀ v ∈ V, v ≠ 1 → U ⊓ Subgroup.centralizer {v} = ⊥) : False := by
  classical
  have hHnt : Nontrivial H := (Subgroup.nontrivial_iff_ne_bot H).2 hH
  have hcopE : Nat.Coprime (Nat.card H) (Nat.card E) :=
    coprime_card_of_fixedPointFree (φ := (MulAut.conjNormal (H := H)).comp E.subtype)
      (fun u hu => fixedPointFree_conjNormal_of_inf_centralizer_eq_bot
        (hfree (u : L) u.2 (by simpa using hu)))
  set A : Subgroup L := U ⊔ V
  have hAE : A ≤ E := sup_le hUE hVE
  have hUA : U ≤ A := le_sup_left
  have hVA : V ≤ A := le_sup_right
  have hcop : (Nat.card A).Coprime (Nat.card H) :=
    Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le hAE) hcopE.symm
  let ρ : A →* MulAut H := (MulAut.conjNormal (H := H)).comp A.subtype
  have hAfree : ∀ b : A, (b : L) ≠ 1 →
      MonoidHom.FixedPointFree ((ρ b : MulAut H) : H → H) := fun b hb =>
    fixedPointFree_conjNormal_of_inf_centralizer_eq_bot (hfree (b : L) (hAE b.2) hb)
  have hUn : (U.subgroupOf A).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (sup_le Subgroup.le_normalizer hnorm)
  have hcompl : (U.subgroupOf A).IsComplement' (V.subgroupOf A) :=
    isComplement'_subgroupOf_sup hnorm (disjoint_iff.2 hUV)
  have hC : ∀ w ∈ V.subgroupOf A, w ≠ 1 →
      U.subgroupOf A ⊓ Subgroup.centralizer {w} = ⊥ := by
    intro w hw hw1
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hxU : (x : L) ∈ U := Subgroup.mem_subgroupOf.1 hx.1
    have hxc : (x : L) ∈ Subgroup.centralizer {(w : L)} :=
      Subgroup.mem_centralizer_singleton_iff.2 <| congrArg Subtype.val
        (Subgroup.mem_centralizer_singleton_iff.1 hx.2)
    have hbot := hUfree (w : L) (Subgroup.mem_subgroupOf.1 hw) (by simpa using hw1)
    rw [Subgroup.eq_bot_iff_forall] at hbot
    exact Subtype.ext (hbot _ ⟨hxU, hxc⟩)
  have key := natCard_mul_natCard_fixedPoints_pow_natCard_eq ρ hcop hUn hcompl hC
  obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hU
  obtain ⟨v, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hV
  have hu1' : (u : L) ≠ 1 := fun h => hu1 (Subtype.ext h)
  have hv1' : (v : L) ≠ 1 := fun h => hv1 (Subtype.ext h)
  have hCU : Nat.card {x : H // ∀ c ∈ U.subgroupOf A, ρ c x = x} = 1 :=
    natCard_fixedPoints_eq_one_of_mem_of_fixedPointFree ρ (b := ⟨(u : L), hUA u.2⟩)
      (Subgroup.mem_subgroupOf.2 u.2) (hAfree _ hu1')
  have hCV : Nat.card {x : H // ∀ c ∈ V.subgroupOf A, ρ c x = x} = 1 :=
    natCard_fixedPoints_eq_one_of_mem_of_fixedPointFree ρ (b := ⟨(v : L), hVA v.2⟩)
      (Subgroup.mem_subgroupOf.2 v.2) (hAfree _ hv1')
  have hCA : Nat.card {x : H // ∀ c ∈ (⊤ : Subgroup A), ρ c x = x} = 1 :=
    natCard_fixedPoints_eq_one_of_mem_of_fixedPointFree ρ (b := ⟨(u : L), hUA u.2⟩)
      (Subgroup.mem_top _)
      (hAfree _ hu1')
  rw [hCU, hCV, hCA] at key
  simp only [one_pow, mul_one] at key
  have : (1 : ℕ) < Nat.card H := Finite.one_lt_card_iff_nontrivial.2 hHnt
  omega

theorem not_exists_frobenius_pair_le_free_complement [Finite L] [Group.IsSolvable L]
    (_hodd : Odd (Nat.card L)) {H E : Subgroup L} [H.Normal] (hH : H ≠ ⊥) (_hE : E ≠ ⊥)
    (_hHE : H.IsComplement' E) (_hnil : Group.IsNilpotent H)
    (hfree : ∀ e ∈ E, e ≠ 1 → H ⊓ Subgroup.centralizer {e} = ⊥) :
    ¬ ∃ U V : Subgroup L, U ≤ E ∧ V ≤ E ∧ U ≠ ⊥ ∧ V ≠ ⊥ ∧
      V ≤ Subgroup.normalizer (U : Set L) ∧ U ⊓ V = ⊥ ∧
      ∀ v ∈ V, v ≠ 1 → U ⊓ Subgroup.centralizer {v} = ⊥ := by
  rintro ⟨U, V, hUE, hVE, hU, hV, hnorm, hUV, hUfree⟩
  exact false_of_frobenius_pair_le_free_complement hH hfree hUE hVE hU hV hnorm hUV hUfree

end CFSG.FeitThompson
