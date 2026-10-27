module

public import CFSG.LocalAnalysis.OddStandard.Solomon75LPlusCaseA
public import CFSG.LocalAnalysis.OddStandard.Solomon75LPlusCaseB
public import CFSG.ClassicalInvolution.LBalance.Main

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG

variable {G : Type} [Group G]

theorem card_lt_of_lt' [Finite G] {B T : Subgroup G} (h : B < T) : Nat.card B < Nat.card T := by
  by_contra hc
  push Not at hc
  exact h.ne (Subgroup.eq_of_le_of_card_ge h.le hc)

theorem nPlus_balance_core [Finite G] (hG : pPrimeCore 2 G = ⊥) :
    ∀ (n : ℕ) (B : Subgroup G), IsPGroup 2 B → Nat.card G - Nat.card B = n →
      ∀ u ∈ NPlusIn (centralizer (B : Set G)), TwoElt u → u ∈ LPlus G ⊔ pCore 2 G := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro B hB hn
    by_cases hodd : Odd ((B ⊓ (LPlus G ⊔ pCore 2 G)).relIndex (LPlus G ⊔ pCore 2 G))
    · exact caseA hG B hB hodd
    · have heven : ¬ Odd (B.relIndex ((LPlus G ⊔ pCore 2 G) ⊔ B)) := by
        rw [sup_comm, relIndex_sup_eq B]
        exact hodd
      obtain ⟨T, hTp, hBT, hTK, hTn⟩ :=
        exists_two_subgroup_normalizing ((LPlus G ⊔ pCore 2 G) ⊔ B) B hB le_sup_right heven
      have hlt : Nat.card B < Nat.card T := card_lt_of_lt' hBT
      have hTG : Nat.card T ≤ Nat.card G := Subgroup.card_le_card_group T
      refine caseB (LPlus G ⊔ pCore 2 G) B T hTp hBT.le hTn hTK ?_
      intro d hd h2d
      exact ih (Nat.card G - Nat.card T) (by omega) T hTp rfl d hd h2d

@[expose] def oddTwoCoreG (G : Type) [Group G] : Subgroup G :=
  (pCore 2 (G ⧸ pPrimeCore 2 G)).comap (QuotientGroup.mk' (pPrimeCore 2 G))

instance oddTwoCoreG_normal : (oddTwoCoreG G).Normal :=
  Subgroup.Normal.comap pCore_normal _

theorem nPlus_balance_general [Finite G] (B : Subgroup G) (hB : IsPGroup 2 B) :
    ∀ u ∈ NPlusIn (centralizer (B : Set G)), TwoElt u → u ∈ LPlus G ⊔ oddTwoCoreG G := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (IsPGroup 2 ↥B) := ⟨hB⟩
  set O := pPrimeCore 2 G with hO
  set π := QuotientGroup.mk' O with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hbar : pPrimeCore 2 (G ⧸ O) = ⊥ := pPrimeCore_quotient_pPrimeCore_eq_bot 2
  have hB' : IsPGroup 2 (B.map π) := hB.map π
  have hcent : centralizer ((B.map π : Subgroup (G ⧸ O)) : Set (G ⧸ O)) =
      (centralizer (B : Set G)).map π :=
    centralizer_map_quotient_eq_map_centralizer 2 B O pPrimeCore_normal pPrimeCore_coprime_card
  set Y : Subgroup G := centralizer (B : Set G) with hY
  set Yb : Subgroup (G ⧸ O) := centralizer ((B.map π : Subgroup (G ⧸ O)) : Set (G ⧸ O)) with hYb
  have hmemYb : ∀ y : ↥Y, π (y : G) ∈ Yb := fun y => by
    rw [hcent]
    exact ⟨y, y.2, rfl⟩
  let φ : ↥Y →* ↥Yb := (π.comp Y.subtype).codRestrict Yb hmemYb
  have hφs : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    have hx' : x ∈ Subgroup.map π Y := hcent ▸ hx
    obtain ⟨y, hy, rfl⟩ := hx'
    exact ⟨⟨y, hy⟩, rfl⟩
  have hker : φ.ker ≤ pPrimeCore 2 ↥Y := by
    intro y hy
    rw [MonoidHom.mem_ker] at hy
    have hyπ : π (y : G) = 1 := congrArg Subtype.val hy
    exact subgroupOf_pPrimeCore_le Y ((QuotientGroup.eq_one_iff (y : G)).mp hyπ)
  have hcomap := NPlus_comap φ hφs hker
  intro u hu h2u
  obtain ⟨z, hz, rfl⟩ := hu
  have hφz : φ z ∈ NPlus ↥Yb := by
    have : z ∈ (NPlus ↥Yb).comap φ := hcomap ▸ hz
    exact this
  have hmem : π (z : G) ∈ LPlus (G ⧸ O) ⊔ pCore 2 (G ⧸ O) :=
    nPlus_balance_core hbar _ (B.map π) hB' rfl (π (z : G)) ⟨φ z, hφz, rfl⟩ (h2u.map π)
  have hkerπ : π.ker ≤ pPrimeCore 2 G := le_of_eq (QuotientGroup.ker_mk' O)
  have h3 := (Subgroup.comap_sup_eq (f := π) (LPlus (G ⧸ O)) (pCore 2 (G ⧸ O)) hπs).symm
  have h4 : (LPlus (G ⧸ O)).comap π = LPlus G := LPlus_comap π hπs hkerπ
  have h5 : (LPlus (G ⧸ O) ⊔ pCore 2 (G ⧸ O)).comap π = LPlus G ⊔ oddTwoCoreG G := by
    rw [h3, h4]
    rfl
  rw [← h5]
  exact hmem

theorem lPlus_balance_top [Finite G] (B : Subgroup G) (hB : IsPGroup 2 B) :
    oTwoPrimeOf (LPlusIn (centralizer (B : Set G))) ≤ oTwoPrimeOf (LPlus G) ⊔ oddTwoCoreG G := by
  set Y : Subgroup G := centralizer (B : Set G) with hY
  rw [oTwoPrimeOf_le_iff]
  rintro _ ⟨z, hz, rfl⟩ h2
  have hz2 : TwoElt z := TwoElt.of_injective (f := Y.subtype) Y.subtype_injective h2
  rw [LPlus_eq_pLayer_sup_NPlus] at hz
  have hchar : (pLayer ↥Y 2).Characteristic :=
    ComponentClassification.CatalogueBPrimeJoin.pLayer_characteristic
  have hmem := twoElt_mem_sup_of_normalizes (Subgroup.le_normalizer_of_normal)
    (Subgroup.le_normalizer_of_normal) hz hz2
  set Tgt : Subgroup G := oTwoPrimeOf (LPlus G) ⊔ oddTwoCoreG G with hTgt
  have hle : oTwoPrimeOf (pLayer ↥Y 2) ⊔ oTwoPrimeOf (NPlus ↥Y) ≤ Tgt.comap Y.subtype := by
    refine sup_le (oTwoPrimeOf_le_iff.mpr ?_) (oTwoPrimeOf_le_iff.mpr ?_)
    · intro w hw h2w
      have h1 : (w : G) ∈ pLayer G 2 := ClassicalInvolution.l2PrimeBalance G B hB ⟨w, hw, rfl⟩
      have h2' : (w : G) ∈ LPlus G := by
        rw [LPlus_eq_pLayer_sup_NPlus]
        exact Subgroup.mem_sup_left h1
      exact Subgroup.mem_sup_left (mem_oTwoPrimeOf_of_twoElt h2' (h2w.map Y.subtype))
    · intro w hw h2w
      have h1 : (w : G) ∈ LPlus G ⊔ oddTwoCoreG G :=
        nPlus_balance_general B hB w ⟨w, hw, rfl⟩ (h2w.map Y.subtype)
      have h3 := twoElt_mem_sup_of_normalizes (U := LPlus G) (V := oddTwoCoreG G)
        Subgroup.le_normalizer_of_normal Subgroup.le_normalizer_of_normal h1
        (h2w.map Y.subtype)
      exact sup_le_sup le_rfl (oTwoPrimeOf_le _) h3
  exact hle hmem

end CFSG.OddStandard.Solomon75
