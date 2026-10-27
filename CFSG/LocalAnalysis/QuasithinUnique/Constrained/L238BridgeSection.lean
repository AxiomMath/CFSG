
module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeSecHypS
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeKVocab

public section

namespace CFSG.QuasithinUnique

open CFSG.Quasithin CFSG.Open

namespace Bridge

theorem KClosed.of_hom_surjective {KP : ∀ (Y : Type) [Group Y], Prop} (hK : KClosed KP) {Y Q : Type}
    [Group Y] [Group Q] (hY : KP Y) (φ : Y →* Q) (hφ : Function.Surjective φ) : KP Q :=
  hK.inj (QuotientGroup.quotientKerEquivOfSurjective φ hφ).symm.toMonoidHom
    (QuotientGroup.quotientKerEquivOfSurjective φ hφ).symm.injective (hK.quot φ.ker hY)

structure SecHyp {V : Type} [CommGroup V] (L A : Subgroup (MulAut V)) (U Z : Subgroup V) (m : ℕ) :
    Prop where
  five_le : 5 ≤ m
  iso : Nonempty (↥L ≃* alternatingGroup (Fin m))
  normA : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ ∈ L
  noncomm : ∃ a ∈ A, ∃ l ∈ L, a * l ≠ l * a
  stabLU : L ≤ stabSub U
  stabAU : A ≤ stabSub U
  stabAZ : A ≤ stabSub Z
  fixZ : Z = U ⊓ fixV L
  ltZU : Z < U
  irr : ∀ J : Subgroup V, Z ≤ J → J ≤ U → (∀ l ∈ L, ∀ w ∈ J, l w ∈ J) → J = Z ∨ J = U
  comm : U ≤ commSub U L

namespace SecHyp

variable {V : Type} [CommGroup V] [Finite V] {L A : Subgroup (MulAut V)} {U Z : Subgroup V}
  {m : ℕ} (H : SecHyp L A U Z m)

include H

omit [Finite V] in
theorem isSimple : IsSimpleGroup ↥L := by
  obtain ⟨e⟩ := H.iso
  have : IsSimpleGroup (alternatingGroup (Fin m)) := alt_isSimple H.five_le
  exact e.isSimpleGroup

omit [Finite V] in
theorem exists_noncomm_L : ∃ a b : ↥L, a * b ≠ b * a := by
  obtain ⟨e⟩ := H.iso
  obtain ⟨a, b, hab⟩ := alt_exists_noncomm H.five_le
  exact ⟨e.symm a, e.symm b, fun h => hab (e.symm.injective (by rw [map_mul, map_mul]; exact h))⟩

omit [Finite V] in
theorem toSecHypS : L2Block.SecHypS L A U Z :=
  ⟨H.isSimple, H.exists_noncomm_L, H.normA, H.noncomm, H.stabLU, H.stabAU, H.stabAZ, H.fixZ, H.ltZU,
    H.irr, H.comm⟩

omit [Finite V] in
theorem fix_le : Z ≤ fixV L :=
  H.toSecHypS.fix_le

omit [Finite V] in
theorem stabLZ : L ≤ stabSub Z :=
  H.toSecHypS.stabLZ

omit [Finite V] in
theorem stabX : L ⊔ A ≤ stabSub U ⊓ stabSub Z :=
  H.toSecHypS.stabX

omit [Finite V] in
theorem stabL : L ≤ stabSub U ⊓ stabSub Z :=
  H.toSecHypS.stabL

omit [Finite V] in
theorem stabA : A ≤ stabSub U ⊓ stabSub Z :=
  H.toSecHypS.stabA

omit [Finite V] in
theorem le_normalizer : A ≤ Subgroup.normalizer (L : Set (MulAut V)) :=
  H.toSecHypS.le_normalizer

omit [Finite V] in
theorem normX : ∀ g ∈ L ⊔ A, ∀ l ∈ L, g * l * g⁻¹ ∈ L :=
  H.toSecHypS.normX

omit [Finite V] H in
theorem conj_mem_centSec {g k : MulAut V} (hg : g ∈ stabSub U ⊓ stabSub Z) (hk : k ∈ centSec U Z) :
    g * k * g⁻¹ ∈ centSec U Z :=
  L2Block.SecHypS.conj_mem_centSec hg hk

omit [Finite V] in
theorem not_le_centSec : ¬ L ≤ centSec U Z :=
  H.toSecHypS.not_le_centSec

omit [Finite V] in
theorem inf_centSec_eq_bot : L ⊓ centSec U Z = ⊥ :=
  H.toSecHypS.inf_centSec_eq_bot

omit [Finite V] in
theorem commute_of_mem_centSec {x : MulAut V} (hx : x ∈ A) (hxs : x ∈ centSec U Z) :
    ∀ l ∈ L, x * l = l * x :=
  H.toSecHypS.commute_of_mem_centSec hx hxs

omit [Finite V] in
theorem inf_centSec_le_centSub : A ⊓ centSec U Z ≤ centSub U :=
  H.toSecHypS.inf_centSec_le_centSub

omit [Finite V] in
theorem not_le_centSec_A : ¬ A ≤ centSec U Z :=
  H.toSecHypS.not_le_centSec_A

variable {G : Subgroup (MulAut V)}

theorem card_le_autSec (hA : IsFFStarOffender G A) :
    Nat.card (Sec U Z) ≤ Nat.card ↥(autSec A U Z) * Nat.card ↥(fixV (autSec A U Z)) :=
  H.toSecHypS.card_le_autSec hA

theorem isFFModule (hA : IsFFStarOffender G A) : IsFFModule (autSec (L ⊔ A) U Z) :=
  H.toSecHypS.isFFModule hA

omit [Finite V] in
theorem secRestrict_injective : Function.Injective (secRestrict H.stabL (U' := Z)) :=
  H.toSecHypS.secRestrict_injective

omit [Finite V] in
theorem exists_equiv_autSec : Nonempty (↥L ≃* ↥(autSec L U Z)) :=
  H.toSecHypS.exists_equiv_autSec

omit [Finite V] in
theorem iso_autSec : Nonempty (↥(autSec L U Z) ≃* alternatingGroup (Fin m)) := by
  obtain ⟨e₁⟩ := H.exists_equiv_autSec
  obtain ⟨e₂⟩ := H.iso
  exact ⟨e₁.symm.trans e₂⟩

omit [Finite V] in
theorem isSimple_autSec : IsSimpleGroup ↥(autSec L U Z) :=
  H.toSecHypS.isSimple_autSec

omit [Finite V] in
theorem quasisimple_autSec : CFSG.Open.IsQuasisimple ↥(autSec L U Z) :=
  H.toSecHypS.quasisimple_autSec

omit [Finite V] in
theorem normG : ∀ y ∈ autSec (L ⊔ A) U Z, ∀ l ∈ autSec L U Z, y * l * y⁻¹ ∈ autSec L U Z :=
  H.toSecHypS.normG

omit [Finite V] in
theorem sqG (hA2 : ∀ a ∈ A, a ^ 2 = 1) : ∀ y ∈ autSec (L ⊔ A) U Z, y ^ 2 ∈ autSec L U Z :=
  H.toSecHypS.sqG hA2

omit [Finite V] H in
theorem le_autSec : autSec L U Z ≤ autSec (L ⊔ A) U Z :=
  L2Block.SecHypS.le_autSec

omit [Finite V] in
theorem exists_noncomm_autSec : ∃ a b : ↥(autSec L U Z), a * b ≠ b * a :=
  H.toSecHypS.exists_noncomm_autSec

omit [Finite V] in
theorem isIrrSec : XMod.IsIrrSec ↥(autSec L U Z) (⊥ : Subgroup (Sec U Z)) ⊤ :=
  H.toSecHypS.isIrrSec

omit [Finite V] H in
theorem eq_one_of_commOf_eq_bot
    (h : XMod.commOf ↥(autSec L U Z) (⊤ : Subgroup (Sec U Z)) = ⊥) (a : ↥(autSec L U Z)) :
    a = 1 :=
  L2Block.SecHypS.eq_one_of_commOf_eq_bot h a

omit [Finite V] in
theorem commOf_top : XMod.commOf ↥(autSec L U Z) (⊤ : Subgroup (Sec U Z)) = ⊤ :=
  H.toSecHypS.commOf_top

omit [Finite V] in
theorem isIrrSec_fixed :
    XMod.IsIrrSec ↥(autSec L U Z) (XMod.fixed ↥(autSec L U Z) (⊤ : Subgroup (Sec U Z))) ⊤ :=
  H.toSecHypS.isIrrSec_fixed

theorem isTwoReduced : XMod.IsTwoReduced ↥(autSec L U Z) (⊤ : Subgroup (Sec U Z)) :=
  H.toSecHypS.isTwoReduced

theorem pCoreOf_eq_bot (hV : ∀ v : V, v ^ 2 = 1) : pCoreOf 2 (autSec (L ⊔ A) U Z) = ⊥ :=
  H.toSecHypS.pCoreOf_eq_bot hV

theorem genFitting_eq (hA2 : ∀ a ∈ A, a ^ 2 = 1) (hV : ∀ v : V, v ^ 2 = 1) :
    quasithinGenFitting (autSec (L ⊔ A) U Z) = autSec L U Z :=
  H.toSecHypS.genFitting_eq hA2 hV

theorem stronglyQuasithin (hA2 : ∀ a ∈ A, a ^ 2 = 1) (hm8 : m ≤ 8) :
    CFSG.Open.SQTKTauCeti.StronglyQuasithin ↥(autSec (L ⊔ A) U Z) := by
  intro p hp hp2
  obtain ⟨e⟩ := H.iso_autSec
  exact pRank_top_le_two_of_sq_mem (L := (autSec L U Z).subgroupOf (autSec (L ⊔ A) U Z))
    (fun y => Subgroup.mem_subgroupOf.2 (H.sqG hA2 y y.2)) hm8
    ((Subgroup.subgroupOfEquivOfLe (le_autSec (A := A))).trans e) hp hp2

omit [Finite V] in
theorem kGroup {KP : ∀ (Y : Type) [Group Y], Prop} (hK : KClosed KP) {G : Subgroup (MulAut V)}
    (hKG : KP ↥G) (hLA : L ⊔ A ≤ G) : KP ↥(autSec (L ⊔ A) U Z) :=
  KClosed.of_hom_surjective hK
    (hK.inj (Subgroup.inclusion hLA) (Subgroup.inclusion_injective hLA) hKG)
    (secRestrict H.stabX) (secRestrict_surjective H.stabX)

theorem b4Hyp {KP : ∀ (Y : Type) [Group Y], Prop} (hK : KClosed KP) {G : Subgroup (MulAut V)}
    (hV : ∀ v : V, v ^ 2 = 1) (hA : IsFFStarOffender G A) (hKG : KP ↥G) (hLA : L ⊔ A ≤ G)
    (hm8 : m ≤ 8) :
    B4HypWith KP (autSec (L ⊔ A) U Z) (autSec L U Z) ∧
      ∃ A₂, IsFFStarOffender (autSec (L ⊔ A) U Z) A₂ := by
  have hA2 : ∀ a ∈ A, a ^ 2 = 1 := hA.2.2.1.2
  have := H.isSimple_autSec
  obtain ⟨a, b, hab⟩ := H.exists_noncomm_autSec
  refine ⟨⟨⟨H.stronglyQuasithin hA2 hm8, H.kGroup hK hKG hLA⟩,
    (H.genFitting_eq hA2 hV).symm, (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup ⟨a, b, hab⟩).1,
    H.isIrrSec⟩, ?_⟩
  exact ((B1_4_5 (sec_sq_eq_one hV U Z) (autSec (L ⊔ A) U Z)).out 1 2).1 (H.isFFModule hA)

end SecHyp

end Bridge

end CFSG.QuasithinUnique
