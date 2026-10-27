module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Defs
public import CFSG.LocalAnalysis.GLTheoremB.NormalPlane
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.NormalFourExistence
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C5Counting
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)

section Basic

variable {G : Type} [Group G] [Finite G]

abbrev Input31Link (p k : ℕ) (R X Y : Subgroup G) : Prop :=
  IsEkIn p k R X ∧ IsEkIn p k R Y ∧ 2 ≤ CFSG.Open.pRank p (X ⊓ Y)

theorem input31_isEkIn_iff {p k : ℕ} {R X : Subgroup G} :
    IsEkIn p k R X ↔ X ≤ R ∧ IsElemAbelian p X ∧ Nat.card X = p ^ k := Iff.rfl

theorem input31_isPPlane_iff {p : ℕ} {U : Subgroup G} :
    IsPPlane p U ↔ IsElemAbelian p U ∧ Nat.card U = p ^ 2 := Iff.rfl

theorem input31_le_centralizer_symm {X Y : Subgroup G}
    (h : X ≤ Subgroup.centralizer (Y : Set G)) : Y ≤ Subgroup.centralizer (X : Set G) :=
  fun y hy => Subgroup.mem_centralizer_iff.2 fun x hx =>
    (Subgroup.mem_centralizer_iff.1 (h hx) y hy).symm

theorem input31_le_centralizer_of_le {X Y Z : Subgroup G}
    (h : X ≤ Subgroup.centralizer (Y : Set G)) (hZ : Z ≤ Y) :
    X ≤ Subgroup.centralizer (Z : Set G) :=
  fun x hx => Subgroup.mem_centralizer_iff.2 fun z hz =>
    Subgroup.mem_centralizer_iff.1 (h hx) z (hZ hz)

theorem input31_card_sup_mul_card_inf {X Y : Subgroup G}
    (h : X ≤ Subgroup.centralizer (Y : Set G)) :
    Nat.card (X ⊔ Y : Subgroup G) * Nat.card (X ⊓ Y : Subgroup G) = Nat.card X * Nat.card Y :=
  CFSG.QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer
    (h.trans (Subgroup.centralizer_le_normalizer _))

theorem input31_link {p k : ℕ} [hp : Fact p.Prime] {R X Y : Subgroup G} (hX : IsEkIn p k R X)
    (hY : IsEkIn p k R Y) (h : p ^ 2 ≤ Nat.card (X ⊓ Y : Subgroup G)) :
    Input31Link p k R X Y := by
  refine ⟨hX, hY, ?_⟩
  have hE : IsElemAbelian p (X ⊓ Y : Subgroup G) := isElemAbelian_mono hX.2.1 inf_le_left
  obtain ⟨m, hm⟩ := exists_card_eq_pow hE.isPGroup
  have hm2 : 2 ≤ m := by
    by_contra hlt
    push_neg at hlt
    have hlt' : p ^ m < p ^ 2 := Nat.pow_lt_pow_right hp.out.one_lt hlt
    rw [hm] at h
    exact absurd h (not_le.2 hlt')
  have hle := CFSG.SectionRank.le_pRank hp.out.one_lt (le_refl (X ⊓ Y : Subgroup G)) hE hm
  omega

theorem input31_reflTransGen_symm {α : Type*} {r : α → α → Prop}
    (hr : ∀ a b, r a b → r b a) {a b : α} (h : Relation.ReflTransGen r a b) :
    Relation.ReflTransGen r b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (hr _ _ hbc) ih

theorem input31_card_two_le {p k : ℕ} [hp : Fact p.Prime] (hk : 3 ≤ k) {Q X Y : Subgroup G}
    (hQ : Q ≤ X ⊓ Y) (hQc : Nat.card Q = p ^ (k - 1)) :
    p ^ 2 ≤ Nat.card (X ⊓ Y : Subgroup G) := by
  have h1 : Nat.card Q ≤ Nat.card (X ⊓ Y : Subgroup G) := Subgroup.card_le_of_le hQ
  have h2 : p ^ 2 ≤ p ^ (k - 1) := Nat.pow_le_pow_right hp.out.pos (by omega)
  rw [hQc] at h1
  exact h2.trans h1

theorem input31_card_inter_of_le_join {p k : ℕ} [hp : Fact p.Prime] (hk : 3 ≤ k)
    {D X Y : Subgroup G} (hD : IsElemAbelian p D) (hDc : Nat.card D = p ^ (k + 1))
    (hX : X ≤ D) (hY : Y ≤ D) (hXc : Nat.card X = p ^ k) (hYc : Nat.card Y = p ^ k) :
    p ^ 2 ≤ Nat.card (X ⊓ Y : Subgroup G) := by
  have hcomm : X ≤ Subgroup.centralizer (Y : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.2 fun y hy => (elemAbelian_comm hD (hX hx) (hY hy)).symm
  have hprod := input31_card_sup_mul_card_inf hcomm
  have hsup : Nat.card (X ⊔ Y : Subgroup G) ≤ p ^ (k + 1) := by
    rw [← hDc]
    exact Subgroup.card_le_of_le (sup_le hX hY)
  rw [hXc, hYc] at hprod
  have hkey : p ^ (k + 1) * p ^ (k - 1) = p ^ k * p ^ k := by
    rw [← pow_add, ← pow_add, show k + 1 + (k - 1) = k + k by omega]
  have hpos : 0 < p ^ (k + 1) := pow_pos hp.out.pos _
  have hle : p ^ (k + 1) * p ^ (k - 1) ≤ p ^ (k + 1) * Nat.card (X ⊓ Y : Subgroup G) := by
    rw [hkey, ← hprod]
    exact Nat.mul_le_mul_right _ hsup
  have hk1 : p ^ (k - 1) ≤ Nat.card (X ⊓ Y : Subgroup G) := Nat.le_of_mul_le_mul_left hle hpos
  have h2 : p ^ 2 ≤ p ^ (k - 1) := Nat.pow_le_pow_right hp.out.pos (by omega)
  exact h2.trans hk1

end Basic

section NormalPlane

variable {G : Type} [Group G] [Finite G]

theorem input31_normal_plane {p : ℕ} [hp : Fact p.Prime] {R : Subgroup G}
    (hR : IsPGroup p R) (h3 : 3 ≤ CFSG.Open.pRank p R) :
    ∃ U : Subgroup G, U ≤ R ∧ IsPPlane p U ∧ R ≤ Subgroup.normalizer (U : Set G) := by
  by_cases hp2 : p = 2
  · subst hp2
    obtain ⟨E, hER, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank (p := 2) (by norm_num) R
    have hE' : IsElemAbelian 2 (E.subgroupOf R) := hE.subgroupOf R
    have hcard' : Nat.card (E.subgroupOf R) = 2 ^ CFSG.Open.pRank 2 R :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hER).toEquiv).trans hEcard
    have hle : CFSG.Open.pRank 2 R ≤ CFSG.Open.pRank 2 (⊤ : Subgroup ↥R) :=
      CFSG.SectionRank.le_pRank (p := 2) (by norm_num) (H := (⊤ : Subgroup ↥R))
        (E := E.subgroupOf R) le_top hE' hcard'
    have hrank : 3 ≤ CFSG.Open.twoRank ↥R := h3.trans hle
    obtain ⟨V, hVn, hVe, hV4⟩ :=
      CFSG.ProperTwoGeneratedCore.high_two_rank_normal_four ↥R hR hrank
    have hUe : IsPPlane 2 (V.map R.subtype) :=
      input31_isPPlane_iff.2 ⟨CFSG.SectionRank.isElemAbelian_map hVe R.subtype,
        by rw [Subgroup.card_map_of_injective R.subtype_injective, hV4] <;> norm_num⟩
    refine ⟨V.map R.subtype, Subgroup.map_subtype_le V, hUe, ?_⟩
    rw [← Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le V),
      show (V.map R.subtype).subgroupOf R = V from
        Subgroup.comap_map_eq_self_of_injective R.subtype_injective V]
    exact hVn
  · obtain ⟨U, hUR, hU, hN⟩ :=
      normalPlaneLemma p hp.out hp2 G R hR ((by norm_num : 2 ≤ 3).trans h3)
    exact ⟨U, hUR, hU, hN⟩

end NormalPlane

section Chain

variable {G : Type} [Group G] [Finite G]

theorem input31_Q_exists {p k : ℕ} [hp : Fact p.Prime] (hk : 3 ≤ k) {R U W : Subgroup G}
    (hR : IsPGroup p R) (hU : IsPPlane p U) (hUR : U ≤ R)
    (hN : R ≤ Subgroup.normalizer (U : Set G)) (hW : IsEkIn p k R W) :
    ∃ Q : Subgroup G, Q ≤ W ∧ Q ≤ Subgroup.centralizer (U : Set G) ∧ IsElemAbelian p Q ∧
      Nat.card Q = p ^ (k - 1) := by
  obtain ⟨hWR, hWe, hWk⟩ := input31_isEkIn_iff.1 hW
  have hp0 : 0 < p := hp.out.pos
  have hp1 : 1 < p := hp.out.one_lt
  have hcardC : p ^ (k - 1) ≤ Nat.card (W ⊓ Subgroup.centralizer (U : Set G) : Subgroup G) := by
    have h1 := card_le_mul_card_inf_centralizer hR hU hUR hN hWR
    have h2 : p ^ k = p * p ^ (k - 1) := by
      rw [← pow_succ', show k - 1 + 1 = k by omega]
    rw [hWk, h2] at h1
    exact Nat.le_of_mul_le_mul_left h1 hp0
  have hCdvd : p ^ (k - 1) ∣ Nat.card (W ⊓ Subgroup.centralizer (U : Set G) : Subgroup G) := by
    have h1 : Nat.card (W ⊓ Subgroup.centralizer (U : Set G) : Subgroup G) ∣ Nat.card W :=
      Subgroup.card_dvd_of_le inf_le_left
    rw [hWk] at h1
    obtain ⟨c, -, hCc⟩ := (Nat.dvd_prime_pow hp.out).1 h1
    have hkc : k - 1 ≤ c := by
      by_contra hlt
      push_neg at hlt
      have hlt' : p ^ c < p ^ (k - 1) := Nat.pow_lt_pow_right hp1 hlt
      rw [← hCc] at hlt'
      exact absurd hcardC (not_le.2 hlt')
    rw [hCc]
    exact pow_dvd_pow p hkc
  have hCe : IsElemAbelian p (W ⊓ Subgroup.centralizer (U : Set G) : Subgroup G) :=
    isElemAbelian_mono hWe inf_le_left
  obtain ⟨Q, hQC, hQe, hQcard⟩ := exists_le_isElemAbelian_card hCe hCdvd
  exact ⟨Q, hQC.trans inf_le_left, hQC.trans inf_le_right, hQe, hQcard⟩

theorem input31_Q_inter {p : ℕ} [hp : Fact p.Prime] {U W Q : Subgroup G} (hU : IsPPlane p U)
    (hUW : ¬ U ≤ W) (hQW : Q ≤ W) :
    Nat.card (Q ⊓ U : Subgroup G) = 1 ∨ Nat.card (Q ⊓ U : Subgroup G) = p := by
  have hQUdvd : Nat.card (Q ⊓ U : Subgroup G) ∣ p ^ 2 := by
    rw [← hU.2]
    exact Subgroup.card_dvd_of_le inf_le_right
  obtain ⟨i, hi, hQUi⟩ := (Nat.dvd_prime_pow hp.out).1 hQUdvd
  have hi2 : i ≠ 2 := by
    rintro rfl
    have heq : Q ⊓ U = U :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (hU.2.trans hQUi.symm).le
    exact hUW ((heq.symm.le.trans inf_le_left).trans hQW)
  rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
  · left
    rw [hQUi, pow_zero]
  · right
    rw [hQUi, pow_one]

theorem input31_case_one {p k : ℕ} [hp : Fact p.Prime] (hk : 3 ≤ k) {R U W Q : Subgroup G}
    (hW : IsEkIn p k R W) (hU : IsPPlane p U) (hUR : U ≤ R) (hQW : Q ≤ W)
    (hQcomm : Q ≤ Subgroup.centralizer (U : Set G)) (hQe : IsElemAbelian p Q)
    (hQcard : Nat.card Q = p ^ (k - 1)) (hQU : Q ⊓ U = ⊥) :
    ∃ W' : Subgroup G, IsEkIn p k R W' ∧ U ≤ W' ∧
      Relation.ReflTransGen (Input31Link p k R) W W' := by
  obtain ⟨hWR, -, -⟩ := input31_isEkIn_iff.1 hW
  have hp0 : 0 < p := hp.out.pos
  have hpU : Nat.card U = p ^ 2 := hU.2
  have hQR : Q ≤ R := hQW.trans hWR
  have hQUcard : Nat.card (Q ⊓ U : Subgroup G) = 1 := by
    rw [hQU, Subgroup.card_bot]
  have hDe : IsElemAbelian p (Q ⊔ U : Subgroup G) :=
    isElemAbelian_sup_of_commute hQe hU.1 hQcomm
  have hDR : Q ⊔ U ≤ R := sup_le hQR hUR
  have hDk : Nat.card (Q ⊔ U : Subgroup G) = p ^ (k + 1) := by
    have h := input31_card_sup_mul_card_inf hQcomm
    rw [hQcard, hpU, hQUcard, mul_one] at h
    rw [h, ← pow_add, show k - 1 + 2 = k + 1 by omega]
  obtain ⟨T, hTU, hTe, hTcard⟩ := exists_le_isElemAbelian_card hU.1 (n := 1)
    (by rw [hpU]; exact pow_dvd_pow p (by norm_num))
  have hQT : Q ≤ Subgroup.centralizer (T : Set G) := input31_le_centralizer_of_le hQcomm hTU
  have hTQbot : Q ⊓ T = ⊥ := by
    apply le_bot_iff.1
    intro x hx
    have hx' : x ∈ Q ⊓ U := ⟨hx.1, hTU hx.2⟩
    rw [hQU] at hx'
    exact hx'
  have hQTcard : Nat.card (Q ⊓ T : Subgroup G) = 1 := by
    rw [hTQbot, Subgroup.card_bot]
  have hZe : IsElemAbelian p (Q ⊔ T : Subgroup G) := isElemAbelian_sup_of_commute hQe hTe hQT
  have hZcard : Nat.card (Q ⊔ T : Subgroup G) = p ^ k := by
    have h := input31_card_sup_mul_card_inf hQT
    rw [hQcard, hTcard, hQTcard, pow_one, mul_one] at h
    rw [h, ← pow_succ, show k - 1 + 1 = k by omega]
  obtain ⟨S, hSQ, hSe, hScard⟩ := exists_le_isElemAbelian_card hQe (n := k - 2)
    (by rw [hQcard]; exact pow_dvd_pow p (by omega))
  have hUS : U ≤ Subgroup.centralizer (S : Set G) :=
    input31_le_centralizer_of_le (input31_le_centralizer_symm hQcomm) hSQ
  have hUSbot : U ⊓ S = ⊥ := by
    apply le_bot_iff.1
    intro x hx
    have hx' : x ∈ Q ⊓ U := ⟨hSQ hx.2, hx.1⟩
    rw [hQU] at hx'
    exact hx'
  have hZ'e : IsElemAbelian p (U ⊔ S : Subgroup G) := isElemAbelian_sup_of_commute hU.1 hSe hUS
  have hZ'card : Nat.card (U ⊔ S : Subgroup G) = p ^ k := by
    have h := input31_card_sup_mul_card_inf hUS
    rw [hpU, hScard, hUSbot, Subgroup.card_bot, mul_one] at h
    rw [h, ← pow_add, show 2 + (k - 2) = k by omega]
  have hZD : Q ⊔ T ≤ Q ⊔ U := sup_le le_sup_left (hTU.trans le_sup_right)
  have hZ'D : U ⊔ S ≤ Q ⊔ U := sup_le le_sup_right (hSQ.trans le_sup_left)
  have hZR : Q ⊔ T ≤ R := le_trans hZD hDR
  have hZ'R : U ⊔ S ≤ R := le_trans hZ'D hDR
  have hZi : IsEkIn p k R (Q ⊔ T : Subgroup G) := input31_isEkIn_iff.2 ⟨hZR, hZe, hZcard⟩
  have hZ'i : IsEkIn p k R (U ⊔ S : Subgroup G) := input31_isEkIn_iff.2 ⟨hZ'R, hZ'e, hZ'card⟩
  have hWZ : p ^ 2 ≤ Nat.card (W ⊓ (Q ⊔ T) : Subgroup G) :=
    input31_card_two_le hk (le_inf hQW le_sup_left) hQcard
  have hZZ' : p ^ 2 ≤ Nat.card ((Q ⊔ T) ⊓ (U ⊔ S) : Subgroup G) :=
    input31_card_inter_of_le_join hk hDe hDk hZD hZ'D hZcard hZ'card
  exact ⟨U ⊔ S, hZ'i, le_sup_left,
    Relation.ReflTransGen.tail (Relation.ReflTransGen.single (input31_link hW hZi hWZ))
      (input31_link hZi hZ'i hZZ')⟩

theorem input31_case_p {p k : ℕ} [hp : Fact p.Prime] (hk : 3 ≤ k) {R U W Q : Subgroup G}
    (hW : IsEkIn p k R W) (hU : IsPPlane p U) (hUR : U ≤ R) (hQW : Q ≤ W)
    (hQcomm : Q ≤ Subgroup.centralizer (U : Set G)) (hQe : IsElemAbelian p Q)
    (hQcard : Nat.card Q = p ^ (k - 1)) (hQUp : Nat.card (Q ⊓ U : Subgroup G) = p) :
    ∃ W' : Subgroup G, IsEkIn p k R W' ∧ U ≤ W' ∧
      Relation.ReflTransGen (Input31Link p k R) W W' := by
  obtain ⟨hWR, -, -⟩ := input31_isEkIn_iff.1 hW
  have hp0 : 0 < p := hp.out.pos
  have hpU : Nat.card U = p ^ 2 := hU.2
  have hQR : Q ≤ R := hQW.trans hWR
  have hDe : IsElemAbelian p (Q ⊔ U : Subgroup G) :=
    isElemAbelian_sup_of_commute hQe hU.1 hQcomm
  have hDR : Q ⊔ U ≤ R := sup_le hQR hUR
  have hDk : Nat.card (Q ⊔ U : Subgroup G) = p ^ k := by
    have h := input31_card_sup_mul_card_inf hQcomm
    rw [hQcard, hpU, hQUp] at h
    apply Nat.eq_of_mul_eq_mul_right hp0
    rw [h, ← pow_add, ← pow_succ, show k - 1 + 2 = k + 1 by omega]
  have hDi : IsEkIn p k R (Q ⊔ U : Subgroup G) := input31_isEkIn_iff.2 ⟨hDR, hDe, hDk⟩
  have hWD : p ^ 2 ≤ Nat.card (W ⊓ (Q ⊔ U) : Subgroup G) :=
    input31_card_two_le hk (le_inf hQW le_sup_left) hQcard
  exact ⟨Q ⊔ U, hDi, le_sup_right,
    Relation.ReflTransGen.single (input31_link hW hDi hWD)⟩

theorem input31_chain_to_plane {p k : ℕ} [hp : Fact p.Prime] (hk : 3 ≤ k) {R U W : Subgroup G}
    (hR : IsPGroup p R) (hU : IsPPlane p U) (hUR : U ≤ R)
    (hN : R ≤ Subgroup.normalizer (U : Set G)) (hW : IsEkIn p k R W) :
    ∃ W' : Subgroup G, IsEkIn p k R W' ∧ U ≤ W' ∧
      Relation.ReflTransGen (Input31Link p k R) W W' := by
  by_cases hUW : U ≤ W
  · exact ⟨W, hW, hUW, Relation.ReflTransGen.refl⟩
  obtain ⟨Q, hQW, hQcomm, hQe, hQcard⟩ := input31_Q_exists hk hR hU hUR hN hW
  rcases input31_Q_inter hU hUW hQW with h1 | h1
  · exact input31_case_one hk hW hU hUR hQW hQcomm hQe hQcard (Subgroup.card_eq_one.1 h1)
  · exact input31_case_p hk hW hU hUR hQW hQcomm hQe hQcard h1

end Chain

theorem input31_8_holds : Input31_8 := by
  intro G _ _ p k hp hk R hR A B hA hB
  haveI : Fact p.Prime := ⟨hp⟩
  have h3 : 3 ≤ CFSG.Open.pRank p R := by
    obtain ⟨hAR, hAe, hAk⟩ := input31_isEkIn_iff.1 hA
    have := CFSG.SectionRank.le_pRank hp.one_lt hAR hAe hAk
    omega
  obtain ⟨U, hUR, hU, hN⟩ := input31_normal_plane hR h3
  obtain ⟨A', hA', hUA', hAA'⟩ := input31_chain_to_plane hk hR hU hUR hN hA
  obtain ⟨B', hB', hUB', hBB'⟩ := input31_chain_to_plane hk hR hU hUR hN hB
  have hU2 : p ^ 2 ≤ Nat.card (A' ⊓ B' : Subgroup G) := by
    rw [← hU.2]
    exact Subgroup.card_le_of_le (le_inf hUA' hUB')
  have hmid : Relation.ReflTransGen (Input31Link p k R) A' B' :=
    Relation.ReflTransGen.single (input31_link hA' hB' hU2)
  have hsymm : ∀ X Y : Subgroup G, Input31Link p k R X Y → Input31Link p k R Y X :=
    fun X Y h => ⟨h.2.1, h.1, by rw [inf_comm]; exact h.2.2⟩
  exact hAA'.trans (hmid.trans (input31_reflTransGen_symm (r := Input31Link p k R) hsymm hBB'))


@[expose] def Input31_GL3Rank : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → ∀ A N : Subgroup G,
    IsElemAbelian p A → IsElemAbelian p N → Nat.card N = p ^ 3 →
      A ≤ Subgroup.normalizer (N : Set G) →
        Nat.card A ≤ p ^ 2 * Nat.card (A ⊓ Subgroup.centralizer (N : Set G) : Subgroup G)

section Input31_6

variable {G : Type} [Group G] [Finite G]

theorem input31_kconnected_iff {p k : ℕ} {X A B : Subgroup G} :
    IsKConnectedIn p k X A B ↔ A ≤ X ∧ IsElemAbelian p A ∧ p ^ k ≤ Nat.card A ∧ B ≤ X ∧
      IsElemAbelian p B ∧ p ^ k ≤ Nat.card B ∧
      (A ≤ Subgroup.centralizer (B : Set G) ∨
        ∃ U V : Subgroup G, IsEkIn p k X U ∧ IsEkIn p k X V ∧
          A ≤ Subgroup.centralizer (U : Set G) ∧ Relation.ReflTransGen (IsKConnStep p k X) U V ∧
          V ≤ Subgroup.centralizer (B : Set G)) :=
  Iff.rfl

theorem input31_kconnStep_iff {p k : ℕ} {X U V : Subgroup G} :
    IsKConnStep p k X U V ↔ IsEkIn p k X U ∧ IsEkIn p k X V ∧ U ≤ Subgroup.centralizer (V : Set G) :=
  Iff.rfl

theorem input31_le_centralizer_of_elemAbelian {p : ℕ} {E F : Subgroup G}
    (hE : IsElemAbelian p E) (hF : F ≤ E) : E ≤ Subgroup.centralizer (F : Set G) :=
  fun e he => Subgroup.mem_centralizer_iff.2 fun f hf => elemAbelian_comm hE (hF hf) he

theorem input31_sub_of_card_le {p : ℕ} [hp : Fact p.Prime] {E F : Subgroup G}
    (hE : IsElemAbelian p E) (hF : F ≤ E) {m : ℕ} (hm : p ^ m ≤ Nat.card F) :
    ∃ K : Subgroup G, K ≤ F ∧ IsElemAbelian p K ∧ Nat.card K = p ^ m := by
  have hFe : IsElemAbelian p F := isElemAbelian_mono hE hF
  obtain ⟨c, hc⟩ := exists_card_eq_pow hFe.isPGroup
  have hmc : m ≤ c := by
    by_contra hlt
    push_neg at hlt
    have hlt' : p ^ c < p ^ m := Nat.pow_lt_pow_right hp.out.one_lt hlt
    rw [hc] at hm
    exact absurd hm (not_le.2 hlt')
  exact exists_le_isElemAbelian_card hFe (n := m) (by rw [hc]; exact pow_dvd_pow p hmc)

theorem input31_plane_below {p : ℕ} [hp : Fact p.Prime] {R U E : Subgroup G} (hR : IsPGroup p R)
    (hU : IsPPlane p U) (hUR : U ≤ R) (hN : R ≤ Subgroup.normalizer (U : Set G))
    (hE : IsEkIn p 3 R E) :
    ∃ D : Subgroup G, IsEkIn p 2 R D ∧ D ≤ E ∧ D ≤ Subgroup.centralizer (U : Set G) := by
  obtain ⟨hER, hEe, hEk⟩ := input31_isEkIn_iff.1 hE
  have h1 := card_le_mul_card_inf_centralizer hR hU hUR hN hER
  rw [hEk] at h1
  have h3 : p * p ^ 2 = p ^ 3 := by ring
  rw [← h3] at h1
  have h2 : p ^ 2 ≤ Nat.card (E ⊓ Subgroup.centralizer (U : Set G) : Subgroup G) :=
    Nat.le_of_mul_le_mul_left h1 hp.out.pos
  obtain ⟨D, hDF, hDe, hDc⟩ := input31_sub_of_card_le hEe (inf_le_left :
    E ⊓ Subgroup.centralizer (U : Set G) ≤ E) h2
  exact ⟨D, input31_isEkIn_iff.2 ⟨hDF.trans (inf_le_left.trans hER), hDe, hDc⟩,
    hDF.trans inf_le_left, hDF.trans inf_le_right⟩

theorem input31_two_connected {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {R : Subgroup G}
    (hR : IsPGroup p R) {A B : Subgroup G} (hA : IsEkIn p 3 R A) (hB : IsEkIn p 3 R B) :
    IsKConnectedIn p 2 R A B := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h2 : 2 ≤ CFSG.Open.pRank p R := by
    have := CFSG.SectionRank.le_pRank hp.one_lt (input31_isEkIn_iff.1 hA).1
      (input31_isEkIn_iff.1 hA).2.1 (input31_isEkIn_iff.1 hA).2.2
    omega
  obtain ⟨U, hUR, hU, hN⟩ := normalPlaneLemma p hp hp2 G R hR h2
  have hUk : IsEkIn p 2 R U := input31_isEkIn_iff.2 ⟨hUR, hU.1, hU.2⟩
  obtain ⟨DA, hDA, hDAA, hDAU⟩ := input31_plane_below hR hU hUR hN hA
  obtain ⟨DB, hDB, hDBB, hDBU⟩ := input31_plane_below hR hU hUR hN hB
  have hAc : 2 ≤ 3 := by norm_num
  refine input31_kconnected_iff.2 ⟨(input31_isEkIn_iff.1 hA).1,
    (input31_isEkIn_iff.1 hA).2.1, ?_, (input31_isEkIn_iff.1 hB).1,
    (input31_isEkIn_iff.1 hB).2.1, ?_, Or.inr ⟨DA, DB, hDA, hDB,
      input31_le_centralizer_of_elemAbelian (input31_isEkIn_iff.1 hA).2.1 hDAA, ?_, ?_⟩⟩
  · rw [(input31_isEkIn_iff.1 hA).2.2]
    exact Nat.pow_le_pow_right hp.pos hAc
  · rw [(input31_isEkIn_iff.1 hB).2.2]
    exact Nat.pow_le_pow_right hp.pos hAc
  · exact Relation.ReflTransGen.tail
      (Relation.ReflTransGen.single (input31_kconnStep_iff.2 ⟨hDA, hUk, hDAU⟩))
      (input31_kconnStep_iff.2 ⟨hUk, hDB, input31_le_centralizer_symm hDBU⟩)
  · exact (input31_le_centralizer_of_elemAbelian (input31_isEkIn_iff.1 hB).2.1 hDBB |>
      input31_le_centralizer_symm)

theorem input31_three_connected (hI3 : Input31_3) (hG3 : Input31_GL3Rank) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {R : Subgroup G} (hR : IsPGroup p R) {A B : Subgroup G}
    (hA : IsEkIn p 5 R A) (hB : IsEkIn p 5 R B) : IsKConnectedIn p 3 R A B := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h3 : 3 ≤ CFSG.Open.pRank p R := by
    have := CFSG.SectionRank.le_pRank hp.one_lt (input31_isEkIn_iff.1 hA).1
      (input31_isEkIn_iff.1 hA).2.1 (input31_isEkIn_iff.1 hA).2.2
    omega
  obtain ⟨N, hNk, hNn⟩ := hI3 G p hp hp2 R hR 3 (by norm_num) h3
  obtain ⟨hNR, hNe, hNc⟩ := input31_isEkIn_iff.1 hNk
  have hNnorm : R ≤ Subgroup.normalizer (N : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNR).1 hNn
  have hDfor : ∀ {E : Subgroup G}, IsEkIn p 5 R E →
      ∃ D : Subgroup G, IsEkIn p 3 R D ∧ D ≤ E ∧ D ≤ Subgroup.centralizer (N : Set G) := by
    intro E hE
    obtain ⟨hER, hEe, hEk⟩ := input31_isEkIn_iff.1 hE
    have hGA := hG3 G p hp E N hEe hNe hNc (hER.trans hNnorm)
    rw [hEk] at hGA
    have h5 : p ^ 5 = p ^ 2 * p ^ 3 := by ring
    have h6 : p ^ 2 * p ^ 3 ≤ p ^ 2 * Nat.card (E ⊓ Subgroup.centralizer (N : Set G) : Subgroup G) := by
      rw [← h5]
      exact hGA
    have h7 : p ^ 3 ≤ Nat.card (E ⊓ Subgroup.centralizer (N : Set G) : Subgroup G) :=
      Nat.le_of_mul_le_mul_left h6 (pow_pos hp.pos 2)
    obtain ⟨D, hDF, hDe, hDc⟩ := input31_sub_of_card_le hEe (inf_le_left :
      E ⊓ Subgroup.centralizer (N : Set G) ≤ E) h7
    exact ⟨D, input31_isEkIn_iff.2 ⟨hDF.trans (inf_le_left.trans hER), hDe, hDc⟩,
      hDF.trans inf_le_left, hDF.trans inf_le_right⟩
  obtain ⟨DA, hDA, hDAA, hDAN⟩ := hDfor hA
  obtain ⟨DB, hDB, hDBB, hDBN⟩ := hDfor hB
  have hNk' : IsEkIn p 3 R N := hNk
  refine input31_kconnected_iff.2 ⟨(input31_isEkIn_iff.1 hA).1,
    (input31_isEkIn_iff.1 hA).2.1, ?_, (input31_isEkIn_iff.1 hB).1,
    (input31_isEkIn_iff.1 hB).2.1, ?_, Or.inr ⟨DA, DB, hDA, hDB,
      input31_le_centralizer_of_elemAbelian (input31_isEkIn_iff.1 hA).2.1 hDAA, ?_, ?_⟩⟩
  · rw [(input31_isEkIn_iff.1 hA).2.2]
    exact Nat.pow_le_pow_right hp.pos (by norm_num)
  · rw [(input31_isEkIn_iff.1 hB).2.2]
    exact Nat.pow_le_pow_right hp.pos (by norm_num)
  · exact Relation.ReflTransGen.tail
      (Relation.ReflTransGen.single (input31_kconnStep_iff.2 ⟨hDA, hNk', hDAN⟩))
      (input31_kconnStep_iff.2 ⟨hNk', hDB, input31_le_centralizer_symm hDBN⟩)
  · exact (input31_le_centralizer_of_elemAbelian (input31_isEkIn_iff.1 hB).2.1 hDBB |>
      input31_le_centralizer_symm)

theorem input31_6_of (hI3 : Input31_3) (hG3 : Input31_GL3Rank) : Input31_6 := by
  intro G _ _ p hp hp2 R hR
  exact ⟨fun A B hA hB => input31_three_connected hI3 hG3 hp hp2 hR hA hB,
    fun A B hA hB => input31_two_connected hp hp2 hR hA hB⟩

end Input31_6

end CFSG.LocalAnalysis.GLTheoremB.MovingAround

end
