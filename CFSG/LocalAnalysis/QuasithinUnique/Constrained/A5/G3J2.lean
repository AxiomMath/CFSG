module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3J2Check
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3J2Group
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3Tab

public section

namespace CFSG.QuasithinUnique.A5.G3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native
  CFSG.ComponentClassification.J2Cover CFSG.Sporadic.Schreier

theorem noPairTwoFive_P :
    NoPairTwoFive P := by
  rintro ⟨t, x, h2, h5, h5', h2'⟩
  have hn : (315 : ℕ) < 2 ^ 32 := by norm_num
  have hcl := (pair_check).2.2.2.2.2.1
  have hcard := card_image_pairs_eq_classTotal hn autChain autChain_valid (mx := 2) (my := 5)
    (r := 5) (s := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) genTables_spec
    4000 (by rw [orderTables_autChain]; exact hcl)
  rw [orderTables_autChain, orderTables_autChain, j2_pair_five_total, autChain_originalSubgroup]
    at hcard
  have hne : Nonempty {p : P × P // orderOf p.1 = 2 ∧ orderOf p.2 = 5 ∧
      orderOf (p.1 * p.2) = 5 ∧ orderOf (p.1 * p.2 * p.1⁻¹ * p.2⁻¹) = 2} :=
    ⟨⟨(t, x), h2, h5, h5', h2'⟩⟩
  have hpos := Nat.card_pos (α := {p : P × P // orderOf p.1 = 2 ∧ orderOf p.2 = 5 ∧
      orderOf (p.1 * p.2) = 5 ∧ orderOf (p.1 * p.2 * p.1⁻¹ * p.2⁻¹) = 2})
  omega

theorem noPairTwoFive_J2
    : NoPairTwoFive (CFSG.Blueprint.NativeSporadic.Carrier .J2) :=
  NoPairTwoFive.of_mulEquiv nativeEquivP.symm noPairTwoFive_P

theorem noPairTwoFive_of_isSporadic
    {X : Type} [Group X] (h : IsSporadic .J2 X) :
    NoPairTwoFive X := by
  obtain ⟨e⟩ := h
  exact NoPairTwoFive.of_mulEquiv e.symm noPairTwoFive_J2

theorem noDelta5In_j2
    {X : Type} [Group X] [Finite X] (h : IsSporadic .J2 X) : NoDelta5In X :=
  noDelta5In_of_noPair (noPairTwoFive_of_isSporadic h)

theorem tabKc3J2 :
    TabKc3J2 := by
  intro G _ _ K L hq ⟨e⟩ hLK hs hL
  have : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .J2) :=
    CFSG.Sporadic.J2.isSimpleGroup_J2
  have hcen : Subgroup.center ↥K = CFSG.pCore 2 ↥K := center_eq_pCore_of_simple_quotient hq e
  have hZ : IsPGroup 2 ↥(Subgroup.center ↥K) := by
    rw [hcen]
    exact CFSG.pCore_isPGroup (p := 2) (G := ↥K)
  exact false_of_alt5_block_of_noPair noPairTwoFive_J2
    ((QuotientGroup.quotientMulEquivOfEq hcen).trans e) hs hL hLK hZ

theorem tabKc3
    : A5.TabKc3 := tabKc3_of tabKc3J2

structure Delta5Residual3 : Prop where
  rows : Delta5Rows
  m24 : ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X → IsSporadic .M24 X → NoDelta5In X
  hs : ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X → IsSporadic .HS X → NoDelta5In X
  he : ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X → IsSporadic .He X → NoDelta5In X
  ru : ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X → IsSporadic .Ru X → NoDelta5In X

theorem Delta5Residual3.toResidual2
    (h : Delta5Residual3) : Delta5Residual2 where
  rows := h.rows
  m24 := h.m24
  j2 := fun _ _ _ _ hm => noDelta5In_j2 hm
  hs := h.hs
  he := h.he
  ru := h.ru

theorem a314A5Excluded_direct3
    (hT : ThreeCoverFactCat) (hcore : A36CoreForSQTKCat)
    (h37 : A37ForSQTKCat) (h39 : A39ForSQTKCat) (hR : Delta5Residual3) : A314A5Excluded :=
  a314A5Excluded_direct2 hT hcore h37 h39 hR.toResidual2

end CFSG.QuasithinUnique.A5.G3
