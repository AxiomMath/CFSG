module

public import CFSG.LieType.Ree.Endo
public import CFSG.LieType.Ree.ShortRepresentation

public noncomputable section

namespace CFSG.LieType.Ree

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

open ReeTag

theorem finite_exceptional_automorphism_existence
    (t : ReeTag) (f : ℕ) (_hf : 1 ≤ f)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = t.prime ^ f) :
    ∃ φ : MulAut (adjointGroup t.tag K),
      (∀ (i : Fin t.tag.rank) (c : K),
        φ (xElement i c) = xElement (t.perm i) (c ^ t.exponent i) ∧
          φ (yElement i c) = yElement (t.perm i) (c ^ t.exponent i)) ∧
      (∀ ψ : MulAut (adjointGroup t.tag K),
        (∀ (i : Fin t.tag.rank) (c : K),
          ψ (xElement i c) = xElement (t.perm i) (c ^ t.exponent i) ∧
            ψ (yElement i c) = yElement (t.perm i) (c ^ t.exponent i)) → ψ = φ) ∧
      ∀ Fr : K →+* K, (∀ c, Fr c = c ^ t.prime) →
        φ.toMonoidHom.comp φ.toMonoidHom = frobeniusTwist t.tag K Fr ∧
          φ.toMonoidHom.comp (frobeniusTwist t.tag K Fr) =
            (frobeniusTwist t.tag K Fr).comp φ.toMonoidHom := by
  have : Fintype K := Fintype.ofFinite K
  have : CharP K t.prime := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hK])
  have hp : (t.prime : K) = 0 := CharP.cast_eq_zero K t.prime
  have hf' : t.ShortFaithful K := shortFaithful hp
  set e := t.exceptionalEndo K hp hf' with he
  have hinj : Function.Injective e := exceptionalEndo_injective hp hf'
  set φ : MulAut (adjointGroup t.tag K) := MulEquiv.ofBijective e hinj.bijective_of_finite
  have hφ : φ.toMonoidHom = e := MonoidHom.ext fun _ => rfl
  have hgen : ∀ (i : Fin t.tag.rank) (c : K),
      φ (xElement i c) = xElement (t.perm i) (c ^ t.exponent i) ∧
        φ (yElement i c) = yElement (t.perm i) (c ^ t.exponent i) :=
    fun i c => ⟨exceptionalEndo_xElement hp hf' i c, exceptionalEndo_yElement hp hf' i c⟩
  have hsq : e.comp e = frobeniusTwist t.tag K (frobenius K t.prime) :=
    exceptionalEndo_comp_self hp hf'
  refine ⟨φ, hgen, fun ψ hψ => ?_, fun Fr hFr => ?_⟩
  · refine MulEquiv.ext fun g => ?_
    have h := adjointGroup_hom_ext (f := ψ.toMonoidHom) (g := φ.toMonoidHom)
      (fun i c => by
        change ψ (xElement i c) = φ (xElement i c)
        rw [(hψ i c).1, (hgen i c).1])
      (fun i c => by
        change ψ (yElement i c) = φ (yElement i c)
        rw [(hψ i c).2, (hgen i c).2])
    exact DFunLike.congr_fun h g
  · have hFr' : Fr = frobenius K t.prime := RingHom.ext fun c => by
      rw [hFr, frobenius_def]
    subst hFr'
    rw [hφ, hsq]
    refine ⟨rfl, ?_⟩
    rw [← hsq, ← MonoidHom.comp_assoc]
