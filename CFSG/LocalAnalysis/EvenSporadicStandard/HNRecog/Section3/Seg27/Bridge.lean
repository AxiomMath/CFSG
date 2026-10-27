module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Seg27.Lift
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Seg27.FactA
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Seg27.FactB
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.LinesProof.SixAShape

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

structure Seg27Five {H : Type} [Group H]
    (φ : alternatingGroup (Fin 8) ≃* ↥(_root_.commutator H)) (a : H) (K : Subgroup H) :
    Prop where
  shape : IsShapeZ2TimesSym 5 ↥K
  derived : IsShapeA5 ↥(derivedOf K)
  six : HasSixOrbit φ (derivedOf K)
  ne_one : a ≠ 1
  mul_self : a * a = 1
  inf_center : K ⊓ Subgroup.center H = Subgroup.zpowers a

theorem seg27_bridge_five {H : Type} [Group H] [Finite H] {θ : H →* Equiv.Perm (Fin 8)}
    (φ : alternatingGroup (Fin 8) ≃* ↥(_root_.commutator H))
    (hθ : ∀ g, θ (φ g : H) = (g : Equiv.Perm (Fin 8)))
    (hA : ∀ h, θ h ∈ alternatingGroup (Fin 8)) (hker : θ.ker = Subgroup.center H)
    {a : H} {K : Subgroup H} (hK : Seg27Five φ a K) :
    Nat.card (K.map θ) = 120 ∧ ∃ p q : Fin 8, Seg27Six ((derivedOf K).map θ) p q := by
  classical
  have hKd : derivedOf K ≤ _root_.commutator H := seg27_derivedOf_le_commutator K
  have hXalt : (derivedOf K).map θ ≤ alternatingGroup (Fin 8) :=
    Subgroup.map_le_iff_le_comap.mpr fun x _ => hA x
  obtain ⟨eL⟩ := seg27_nonempty_mulEquiv_map φ hθ hKd
  obtain ⟨e5⟩ := hK.derived
  have eX : ↥((derivedOf K).map θ) ≃* alternatingGroup (Fin 5) := eL.symm.trans e5
  obtain ⟨o, ho⟩ := (seg27_hasSixOrbit_iff φ hθ hKd).1 hK.six
  obtain ⟨p, q, hpq⟩ := seg27_six_of_A5 hXalt eX ho
  have hcardK : Nat.card K = 240 := lines_card_z2_sym5 hK.shape
  have hker' : Nat.card (K ⊓ θ.ker : Subgroup H) = 2 := by
    rw [show K ⊓ θ.ker = Subgroup.zpowers a by rw [hker, hK.inf_center], Nat.card_zpowers]
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by simpa [pow_two] using hK.mul_self) hK.ne_one
  have hmul := seg27_card_map_mul θ K
  rw [hcardK, hker'] at hmul
  exact ⟨by omega, ⟨p, q, hpq⟩⟩

theorem seg27_bridge_six {H : Type} [Group H] [Finite H] {θ : H →* Equiv.Perm (Fin 8)}
    (φ : alternatingGroup (Fin 8) ≃* ↥(_root_.commutator H))
    (hθ : ∀ g, θ (φ g : H) = (g : Equiv.Perm (Fin 8)))
    (hA : ∀ h, θ h ∈ alternatingGroup (Fin 8)) {K : Subgroup H}
    (hK : IsShapeZ2TimesSym 6 ↥K) :
    ∃ p q : Fin 8, p ≠ q ∧ (derivedOf K).map θ = seg27AltFix {p, q} := by
  classical
  have hKd : derivedOf K ≤ _root_.commutator H := seg27_derivedOf_le_commutator K
  have hYalt : (derivedOf K).map θ ≤ alternatingGroup (Fin 8) :=
    Subgroup.map_le_iff_le_comap.mpr fun x _ => hA x
  obtain ⟨eL⟩ := seg27_nonempty_mulEquiv_map φ hθ hKd
  obtain ⟨e6⟩ := seg27_isShapeA6_derivedOf hK
  exact seg27_eq_altFix_of_A6 hYalt (eL.symm.trans e6)

end CFSG.EvenSporadicStandard.HNRecog.Section3
