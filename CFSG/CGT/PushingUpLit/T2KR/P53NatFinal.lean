module

public import CFSG.CGT.PushingUpLit.T2KR.P53Final
public import CFSG.CGT.PushingUpLit.T2KR.P53NatBlocks
public import CFSG.CGT.PushingUpLit.CGT6.EightOneCore
public import CFSG.CGT.PushingUpLit.T2KR.P53Setup

public section

namespace CFSG.CGT.PushingUpLit.T2KR.P53

open CFSG CFSG.Quasithin CFSG.Quasithin.BlueprintB2 CFSG.QuasithinUnique.Setup.Campbell
  CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open CFSG.CGT.PushingUpLit.Nine CFSG.CGT.PushingUpLit.CGT6 CFSG.CGT.PushingUpLit.BHS
open CFSG.CGT.PushingUpLit.EightOneRel CFSG.CGT.PushingUpLit.Glue
open CFSG.CGT.PushingUpLit.T2K (T2Hyp)
open CFSG.Assembly (KProper InCatalog)

variable {G : Type} [Group G] [Finite G]

theorem one_le_of_isNaturalAltModule {Z : Subgroup G} (hZ : InClassX ↥Z) {a : ℕ}
    (h : IsNaturalAltModule ↥Z a) : 1 ≤ a := by
  by_contra hlt
  have ha : a = 0 := by omega
  subst ha
  obtain ⟨φ, -⟩ := h
  have hperm : Subsingleton (Equiv.Perm (Fin (2 * 0 + 1))) := by
    show Subsingleton (Equiv.Perm (Fin 1))
    infer_instance
  have hsub : Subsingleton (alternatingGroup (Fin (2 * 0 + 1))) :=
    ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
  have hq : Subsingleton (↥Z ⧸ pCore 2 ↥Z) := φ.toEquiv.subsingleton
  apply InClassX.not_isPGroup hZ
  intro z
  have hz : z ∈ pCore 2 ↥Z := by
    have : (QuotientGroup.mk z : ↥Z ⧸ pCore 2 ↥Z) = 1 := Subsingleton.elim _ _
    exact (QuotientGroup.eq_one_iff z).1 this
  obtain ⟨k, hk⟩ := pCore_isPGroup ⟨z, hz⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem exists_maximal_nat_above : ∀ (k : ℕ) (Y : Subgroup G), Nat.card G - Nat.card Y = k →
    InClassXG Y → ∃ W : Subgroup G, Y ≤ W ∧ IsMaximalInClassXGNat W ∧
      (W = Y ∨ ∃ a : ℕ, IsNaturalAltModule ↥W a) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro Y hk hY
  by_cases hmax : IsMaximalInClassXGNat Y
  · exact ⟨Y, le_rfl, hmax, Or.inl rfl⟩
  · have hex : ∃ Z : Subgroup G, InClassXG Z ∧ ArrowNat Y Z ∧ Z ≠ Y := by
      by_contra hcon
      push Not at hcon
      exact hmax ⟨hY, hcon⟩
    obtain ⟨Z, hZ, hYZ, hne⟩ := hex
    rcases hYZ with h | ⟨a, b, φ, F, -, hnat, -, -, hle, -⟩
    · exact absurd h.symm hne
    · have hlt : Y < Z := lt_of_le_of_ne hle (Ne.symm hne)
      have hcard : Nat.card Y < Nat.card Z := card_lt_of_lt hlt
      have hZG : Nat.card Z ≤ Nat.card G := Subgroup.card_le_card_group Z
      obtain ⟨W, hZW, hWmax, hW⟩ := ih (Nat.card G - Nat.card Z) (by omega) Z rfl hZ
      refine ⟨W, hle.trans hZW, hWmax, Or.inr ?_⟩
      rcases hW with h2 | h2
      · subst h2
        exact ⟨a, φ, hnat⟩
      · exact h2

theorem print53_of_natCore (hbhs : BHSLocalCStar) (h616 : AschbacherSixSixteenNormal)
    (hCore : AschbacherSixThreeCoreNat) (hBS : BenderSuzukiStatement)
    (hE2 : CFSG.CGT.PushingUpLit.SolomonAlternatingBlockK) :
    CFSG.CGT.PushingUpLit.T2K.Print53 := by
  intro G _ _ L M T n h hT hTM hu hnoG4
  have := h.simple
  obtain ⟨T', rfl⟩ := exists_sylow_of_isSylowOf_top hT
  obtain ⟨I, H, S, Y, L', hc, hY, hmax, hYG⟩ := exists_setup hbhs h616 hBS h T' hu
  have hKG : ∀ N' : Subgroup G, IsMaximalTwoLocal N' → CFSG.IsKGroup ↥N' := fun N' hN' =>
    isKGroup_of_isMaximalTwoLocal h.kproper hN'
  obtain ⟨W, hYW, hWmax, hW⟩ := exists_maximal_nat_above _ Y rfl hYG
  obtain ⟨N', hN'u, hWsub⟩ :=
    factorizationThree_of_eightOneKNat (eightOneK_of_coreNat hCore) h.kproper h.charTwo hKG hWmax
  have hWY : W = Y := by
    rcases hW with hWY | ⟨a, ha⟩
    · exact hWY
    · exfalso
      have hW1 : InClassX ↥W := hWmax.1.1
      have hmem : N' ∈ maximalTwoLocalsContaining (W : Set G) := by rw [hN'u]; rfl
      exact hnoG4 (hE2 G h.kproper h.simple h.charTwo N' W hmem.1 (fun x hx => hmem.2 hx) hWsub
        hW1 ⟨a, one_le_of_isNaturalAltModule hW1 ha, ha⟩ hN'u)
  subst hWY
  exact conclusion_of_block h T' hTM hc hY.not_le hY.le_normalizer hWmax.1.1 ⟨N', hN'u, hWsub⟩

end CFSG.CGT.PushingUpLit.T2KR.P53
