module

public import CFSG.Quasithin.H13.U3L15A
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6Inputs13_3
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3L15Gen

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.U3

open Equiv Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6
open scoped commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

open scoped IsMulCommutative in

theorem setting4_of_case_b_F4 (h1332 : Stmt13_3_2_F4) {T L V : Subgroup G} [IsMulCommutative ↥V]
    (h : QTH13 G T L) (hV : IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V)
    (hZV : V ⊓ centralizer (L : Set G) = ⊥)
    (hnat : AlternatingNatural (V := ↥V) (autOn L V) ⊤ ⊥ 6) : Nonempty (Setting4 G T L V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h5, ⟨hTN, hmax, hMmax, huniq⟩, ⟨-, hall⟩, -⟩ := h1332 G T L h L h.faithful
  have uniqueM : IsUniqueM (L ⊔ T) (normalizer (L : Set G)) :=
    ⟨⟨hMmax, sup_le le_normalizer hTN⟩, fun M' hM' => huniq M' hM'.1 hM'.2⟩
  obtain ⟨hVT, hTV, hfsu, -, -⟩ := hall V hV
  have hLV : L ≤ normalizer (V : Set G) := hV.2.2.1
  have ha6 : IsA6On L V := nonempty_mulEquiv_of_realizes (altDn_faithful (by norm_num)) hnat
  have hVf := fun v (hv : v ∈ V) => mem_reducedAggregate' (hV.1 hv)
  have hO : pCoreOf 2 L ≤ centralizer (V : Set G) := by
    refine (pCoreOf_le_pCoreOf_sup hTN).trans ?_
    intro k hk
    exact mem_centralizer_iff.2 fun v hv => ((hVf v hv).2.1 k hk).symm
  have hA6 := a6CentralQuotient_of_isA6On hLV hO h5 ha6
  obtain ⟨R⟩ := exists_rawData4 hLV hnat
  have hcard : Nat.card V = 16 := by
    rw [Nat.card_congr R.ψ.toEquiv]
    have : Fintype.card {x : P6 // InW4 x} = 16 := by decide +kernel
    rw [← this, ← Nat.card_eq_fintype_card]
    rfl
  have hV2 : IsPGroup 2 V := IsPGroup.of_card (n := 4) (by rw [hcard]; norm_num)
  have hLTV : L ⊔ T ≤ normalizer (V : Set G) := sup_le hLV hTV
  have hNL : normalizer (V : Set G) ≤ normalizer (L : Set G) := by
    obtain ⟨M', hM', hM'le⟩ := exists_maxTwoLocal_ge
      (⟨V, hV.2.1, hV2, rfl⟩ : IsTwoLocal (normalizer (V : Set G)))
    have := uniqueM.2 M' ⟨hM', hLTV.trans hM'le⟩
    exact this ▸ hM'le
  have hsylLT : IsSylowTwoOf T (L ⊔ T) := A5.isSylowTwoOf_of_le h.sylow le_sup_right
  have hsylL : IsSylowTwoOf (T ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal hsylLT le_sup_left (sup_le le_normalizer hTN)
  obtain ⟨F⟩ := exists_frame4 R hNL h.sylow.1 hTV hsylL
  exact ⟨{
    h13 := h
    irr := hV
    zv := hZV
    T_le_NL := hTN
    maximal := hmax
    uniqueM := uniqueM
    V_le_T := hVT
    fsu := hfsu
    a6 := ha6
    centralQuot := hA6
    frame := F }⟩

@[expose] def U3HatL2Plus_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V V₂ : Subgroup G), QTH13 G T L →
    IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V → V ⊓ centralizer (L : Set G) = ⊥ →
    IsA6On L V → IsHatA6 L → IsV2 T V V₂ →
      oTwoRes ⁅L₁Of L V₂, T ⊓ L⁆ ⊓ o2Z L ≤ pCoreOf 2 L

theorem u3Stmt13_3_15_of_A6_F4
    (h1332 : Stmt13_3_2_F4) (h13314 : A6.Stmt13_3_14_F4)
    (hhatP : U3HatL2Plus_F4) {T L V V₂ X I₂ : Subgroup G} (S : Setting4 G T L V)
    (hV2 : IsV2 T V V₂) (hXhat : IsHatA6 L → X = oTwoRes ⁅L₁Of L V₂, T ⊓ L⁆)
    (hXn : ¬ IsHatA6 L → X = L₁Of L V₂)
    (hI₂ : I₂ = conjClosure (pCoreOf 2 (A6.g1 T V)) (normalizer (V₂ : Set G))) :
    normalizer (V₂ : Set G) ≤ normalizer (I₂ : Set G) ∧
      I₂ = X ⊔ pCoreOf 2 (A6.g1 T V) ∧
      I₂ ⊓ centralizer (V₂ : Set G) = pCoreOf 2 I₂ ∧
      Nonempty (↥I₂ ⧸ CFSG.pCore 2 ↥I₂ ≃* Equiv.Perm (Fin 3)) ∧ oTwoRes I₂ = X ∧
      pCoreOf 2 (A6.g1 T V) ⊓ centralizer (V₂ : Set G) ≤ pCoreOf 2 I₂ ∧
      pCoreOf 2 I₂ ≤ pCoreOf 2 (normalizer (V₂ : Set G)) ∧
      CFSG.pRank 3 ↥(centralizer (V₂ : Set G)) ≤ 1 ∧
      ∀ V₃ : Subgroup G, V₂ ≤ V₃ → V₃ ≤ V → T ≤ normalizer (V₃ : Set G) →
        Nat.card V₃ = 8 →
          centralizer (V₃ : Set G) ≤ normalizer (V : Set G) ∧
            (¬ LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1 →
              ⁅V, centralizer (V₃ : Set G)⁆ ≤ fsuV1 T V) := by
  have hV2e : V₂ = S.V2 := S.V2_unique hV2
  subst hV2e
  have hgen' : ∀ {Y : Subgroup G}, Y ≤ L → (∃ x ∈ Y, ∃ hx : x ∈ normalizer (V : Set G),
      S.frame.ρ ⟨x, hx⟩ = a6s3 ∨ S.frame.ρ ⟨x, hx⟩ = a6s3 * a6s3) →
      ∀ V₃ : Subgroup G, S.V2 ≤ V₃ → V₃ ≤ V → T ≤ normalizer (V₃ : Set G) → Nat.card V₃ = 8 →
        autOn (Y ⊔ L ⊓ normalizer (V₃ : Set G)) V = autOn L V := by
    intro Y hYL hY V₃ h23 h3V hT3 hc3
    rw [L15A.V3_eq S h23 h3V hT3 hc3]
    exact L15A.gen_A6 S hYL hY
  have hmod : ¬ LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1 → ∀ V₃ : Subgroup G, S.V2 ≤ V₃ →
      V₃ ≤ V → T ≤ normalizer (V₃ : Set G) → Nat.card V₃ = 8 →
      ∀ c ∈ normalizer (V : Set G) ⊓ normalizer (L : Set G) ⊓ centralizer (V₃ : Set G),
        ∀ v ∈ V, ⁅v, c⁆ ∈ fsuV1 T V := by
    intro _ V₃ h23 h3V hT3 hc3
    rw [L15A.V3_eq S h23 h3V hT3 hc3]
    exact L15A.mod_A6 S
  have hq1 := h13314 G T L V S.V2 S.h13 S.irr S.zv hV2 S.not_iso_a5
  by_cases hhat : IsHatA6 L
  · have hX := hXhat hhat
    subst hX
    have hP := hhatP G T L V S.V2 S.h13 S.irr S.zv S.a6 hhat hV2
    obtain ⟨hXL, hXN, hXT, hXres⟩ := X_facts_L₂plus (L := L) S.T_le_NL S.T_le_normalizer_V2
    obtain ⟨x, hxX, hx3, hxc, hx, hρx⟩ := L15A.exists_X_hat S hP
    refine (core15_of_F4 h1332 S.h13 S.irr S.zv hV2 hq1 hXL hXN hXT hXres ⟨x, hxX, hx3, hxc⟩
      (L15A.isPGroup_X_ker S hXL hP) ?_ (hgen' hXL ⟨x, hxX, hx, hρx⟩)).stmt hI₂ hmod
    intro h
    exact hxc (Subgroup.centralizer_le S.V2_le_V (S.o2Z_le_centralizer (h hxX)))
  · have hX := hXn hhat
    subst hX
    obtain ⟨hXL, hXN, hXT, hXres⟩ := X_facts_L₂ (L := L) S.T_le_NL S.T_le_normalizer_V2
    obtain ⟨x, hxX, hx3, hxc, hx, hρx⟩ := L15A.exists_X_nonhat S hhat
    have hZ : L₁Of L S.V2 ⊓ o2Z L ≤ pCoreOf 2 L :=
      inf_le_right.trans (o2Z_le_pCoreOf_of_center_eq_bot (S.center_Q_eq_bot hhat))
    refine (core15_of_F4 h1332 S.h13 S.irr S.zv hV2 hq1 hXL hXN hXT hXres ⟨x, hxX, hx3, hxc⟩
      (L15A.isPGroup_X_ker S hXL hZ) ?_ (hgen' hXL ⟨x, hxX, hx, hρx⟩)).stmt hI₂ hmod
    intro h
    exact hxc (Subgroup.centralizer_le S.V2_le_V (S.o2Z_le_centralizer (h hxX)))

end CFSG.Quasithin.H13.U3
