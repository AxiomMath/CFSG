module

public import CFSG.Quasithin.H13.A6HatPlusB
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3L15A

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped commutatorElement

open scoped IsMulCommutative in

theorem exists_setting4_of_1332_F4 (h1332 : Stmt13_3_2_F4) {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]
    {T L V : Subgroup G} (h : QTH13 G T L) (hA6 : A6CentralQuotient L)
    (hV : IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V)
    (hZV : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) : Nonempty (Setting4 G T L V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, ⟨hTN, hmax, hMmax, huniq⟩, ⟨-, hall⟩, -⟩ := h1332 G T L h L h.faithful
  have uniqueM : IsUniqueM (L ⊔ T) (Subgroup.normalizer (L : Set G)) :=
    ⟨⟨hMmax, sup_le Subgroup.le_normalizer hTN⟩, fun M' hM' => huniq M' hM'.1 hM'.2⟩
  obtain ⟨hVT, hTV, hfsu, hab, hmod⟩ := hall V hV
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hV.2.2.1

  have hnat : AlternatingNatural (V := ↥V) (autOn L V) ⊤ ⊥ 6 := by
    rcases hmod with ⟨h5, -⟩ | ⟨h6, -⟩ | ⟨-, hc2, -⟩ | ⟨hl, -, -⟩ | ⟨hu, -, -⟩
    · exfalso
      obtain ⟨e⟩ := nonempty_mulEquiv_of_realizes (altDn_faithful (by norm_num)) h5
      obtain ⟨φ, hφ⟩ := exists_surjective_autOn hLV
      exact false_of_surjective_alt5 hA6 (e.toMonoidHom.comp φ) (e.surjective.comp hφ)
    · exact h6
    · exfalso
      rw [hZV, Subgroup.card_bot] at hc2
      exact absurd hc2 (by norm_num)
    · exact (false_of_psl32_of_a6CentralQuotient hA6 hl).elim
    · exfalso
      have h1 := card_of_lieModel_psu33 hu
      obtain ⟨e⟩ := hA6
      have h2 : Nat.card ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸
          Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) = 360 := by
        rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
          Fintype.card_fin]
        rfl
      have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup
        (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L))
      rw [h1, h2] at h3
      omega
  obtain ⟨R⟩ := exists_rawData4 hLV hnat
  have hcard : Nat.card V = 16 := by
    rw [Nat.card_congr R.ψ.toEquiv]
    have : Fintype.card {x : P6 // InW4 x} = 16 := by decide +kernel
    rw [← this, ← Nat.card_eq_fintype_card]
    rfl
  have hV2 : IsPGroup 2 V := IsPGroup.of_card (n := 4) (by rw [hcard]; norm_num)
  have hLTV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := sup_le hLV hTV
  have hNL : Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (L : Set G) := by
    obtain ⟨M', hM', hM'le⟩ := exists_maxTwoLocal_ge
      (⟨V, hV.2.1, hV2, rfl⟩ : IsTwoLocal (Subgroup.normalizer (V : Set G)))
    have := uniqueM.2 M' ⟨hM', hLTV.trans hM'le⟩
    exact this ▸ hM'le
  have hsylLT : IsSylowTwoOf T (L ⊔ T) := A5.isSylowTwoOf_of_le h.sylow le_sup_right
  have hsylL : IsSylowTwoOf (T ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal hsylLT le_sup_left (sup_le Subgroup.le_normalizer hTN)
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
    a6 := nonempty_mulEquiv_of_realizes (altDn_faithful (by norm_num)) hnat
    centralQuot := hA6
    frame := F }⟩

theorem u3HatL2Plus_of_F4 (h1332 : Stmt13_3_2_F4) :
    U3.U3HatL2Plus_F4 := by
  intro G _ _ T L V V₂ hH hV hZV _ hhat hV2
  obtain ⟨S⟩ := exists_setting4_of_1332_F4 h1332 hH hhat.2.2 hV hZV
  have hV2e : V₂ = S.V2 := S.V2_unique hV2
  subst hV2e
  exact S.hatL2Plus hhat

end CFSG.Quasithin.H13.A6
