module

public import CFSG.Quasithin.H13.NQS13410C
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3S135Gen
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Statements

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G}

theorem mem_L_of_orderOf_three_F4 (h1332 : Stmt13_3_2_F4) (h1228 : Stmt12_2_8_F4)
    (S : A6.Setting134 G T L V) {x : G} (hx : x ∈ normalizer (L : Set G))
    (hx3 : orderOf x = 3) : x ∈ L := by
  obtain ⟨h5, -, -, -⟩ := h1332 G T L S.h13 L S.h13.faithful
  have hyp := U3.hyp1223_of_F4 h1332 S.h13 S.irr
  have hLV : L ≤ normalizer (V : Set G) := S.irr.2.2.1
  have hO := pCoreOf_L_le_centralizer_V S
  have h360 : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have h60 : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  rcases h1228 G T L V hyp with h | h | ⟨-, h⟩
  · rw [← h]
    exact subset_closure ⟨hx, 1, by rw [pow_one, ← hx3, pow_orderOf_eq_one]⟩
  · exfalso
    have hcase := U3.a6_or_hatA6_of_isA6On hLV hO h5 (U3.s134_isA6On S)
    have hc : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 360 ∨
        Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 1080 := by
      rcases hcase with he | ⟨-, hz, ⟨e⟩⟩
      · left
        obtain ⟨e⟩ := he
        rw [Nat.card_congr e.toEquiv, h360]
      · right
        have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
          (center (↥L ⧸ CFSG.pCore 2 ↥L))
        rw [Nat.card_congr e.toEquiv, h360, hz] at h1
        rw [h1]
    rcases h with he5 | h32
    · obtain ⟨e5⟩ := he5
      have := Nat.card_congr e5.toEquiv
      rw [h60] at this
      omega
    · obtain ⟨e3⟩ := nonempty_equiv_SL32_of_lieModel h32
      have := Nat.card_congr e3.toEquiv
      rw [HSType.card_SL_three_two] at this
      omega
  · rw [h]
    exact subset_closure ⟨hx, hx3⟩

theorem mem_L_of_pow_three_F4 (h1332 : Stmt13_3_2_F4) (h1228 : Stmt12_2_8_F4)
    (S : A6.Setting134 G T L V)
    (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6))) {x : G}
    (hx : x ∈ normalizer (L : Set G)) {k : ℕ} (hxk : x ^ 3 ^ k = 1) : x ∈ L := by
  have hyp := U3.hyp1223_of_F4 h1332 S.h13 S.irr
  have hcen : center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ :=
    center_eq_bot_of_simple_types (Or.inr (Or.inr he))
  rcases h1228 G T L V hyp with h | h | ⟨⟨n, -, -, hz, -⟩, -⟩
  · rw [← h]
    exact subset_closure ⟨hx, k, hxk⟩
  · exfalso
    obtain ⟨e⟩ := he
    have h360 : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      decide
    have h60 : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      decide
    have hc : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 360 := by rw [Nat.card_congr e.toEquiv, h360]
    rcases h with he5 | h32
    · obtain ⟨e5⟩ := he5
      have := Nat.card_congr e5.toEquiv
      rw [h60] at this
      omega
    · obtain ⟨e3⟩ := nonempty_equiv_SL32_of_lieModel h32
      have := Nat.card_congr e3.toEquiv
      rw [HSType.card_SL_three_two] at this
      omega
  · exfalso
    rw [hcen, Subgroup.card_bot] at hz
    omega

theorem mem_L1_of_pow_three_F4 (h1332 : Stmt13_3_2_F4) (h1228 : Stmt12_2_8_F4)
    (S : A6.Setting134 G T L V)
    (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6))) {x : G}
    (hxZ : x ∈ centralizer (quasithinOmegaOneCenter T : Set G)) {k : ℕ} (hxk : x ^ 3 ^ k = 1) :
    x ∈ L₁Of L (fsuV1 T V) := by
  have hZV : V ⊓ centralizer (L : Set G) ≤ quasithinOmegaOneCenter T :=
    S.ZV_le_ZL.trans inf_le_left
  have hxM : x ∈ normalizer (L : Set G) :=
    S.centralizer_ZV_le (centralizer_le (SetLike.coe_subset_coe.mpr hZV) hxZ)
  have hxL := mem_L_of_pow_three_F4 h1332 h1228 S he hxM hxk
  have hxN : x ∈ normalizer (fsuV1 T V : Set G) :=
    centralizer_le_normalizer _ (centralizer_le (SetLike.coe_subset_coe.mpr
      (inf_le_right : fsuV1 T V ≤ quasithinOmegaOneCenter T)) hxZ)
  exact U3.mem_oTwoRes_of_odd (mem_inf.2 ⟨hxL, hxN⟩) (Odd.pow (by decide : Odd 3)) hxk

theorem L1_le_of_pow_three_F4 (h1332 : Stmt13_3_2_F4) (h1228 : Stmt12_2_8_F4)
    (S : A6.Setting134 G T L V)
    (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6))) {X : Subgroup G}
    (hX : L₁Of L (fsuV1 T V) ≤ normalizer (X : Set G)) {y : G} (hyX : y ∈ X)
    (hyZ : y ∈ centralizer (quasithinOmegaOneCenter T : Set G)) (hy1 : y ≠ 1) {k : ℕ}
    (hyk : y ^ 3 ^ k = 1) : L₁Of L (fsuV1 T V) ≤ X :=
  L1_le_of_mem S he hX hyX (mem_L1_of_pow_three_F4 h1332 h1228 S he hyZ hyk) hy1
    (Odd.pow (by decide : Odd 3)) hyk

end CFSG.Quasithin.H13.NQS134
