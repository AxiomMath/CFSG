module

public import CFSG.LocalAnalysis.SectionRank.QTK.J4InspA1
public import CFSG.Quasithin.H13.A5S136r
public import CFSG.Quasithin.Vol2.Ch9Sec3L34KGMPf
public import CFSG.Quasithin.Background.A3Structure314Excl
public import CFSG.Quasithin.Background.H47WW9
public import CFSG.Quasithin.Background.H47WW16
public import CFSG.Quasithin.Background.H47WW64
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Lemma19

public section

open scoped IsMulCommutative

namespace CFSG.SectionRank.QTK

@[expose] def FaithfulL34ModDim : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ X : Subgroup (MulAut V), CFSG.Quasithin.IsPSL 3 2 2 ↥X → 2 ^ 9 ≤ Nat.card V

theorem two_pow_nine_le_of_irreducible (hFM : CFSG.Quasithin.H13.Ch9.FactL34Modules)
    (V : Type) [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    (X : Subgroup (MulAut V)) (hX : CFSG.Quasithin.IsPSL 3 2 2 ↥X)
    (hirr : CFSG.Quasithin.XMod.IsIrrSec ↥X (⊥ : Subgroup V) ⊤) : 2 ^ 9 ≤ Nat.card V := by
  have hs : IsSimpleGroup ↥X := CFSG.Quasithin.H13.A5.isSimpleGroup_of_isPSL34 hX
  have hcard : Nat.card ↥X = 20160 := CFSG.Quasithin.H13.A5.card_of_isPSL34 hX
  obtain ⟨a, b, hab⟩ :=
    CFSG.Quasithin.A314.exists_noncomm_of_simple hs (by rw [hcard]; norm_num)
  have hz : Subgroup.center ↥X = ⊥ := by
    haveI := hs
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥X) with h | h
    · exact h
    · exfalso
      have ha : a ∈ Subgroup.center ↥X := by
        rw [h]
        exact Subgroup.mem_top a
      exact hab (Subgroup.mem_center_iff.mp ha b).symm
  have hC : ∀ x ∈ X, (∀ l ∈ X, x * l = l * x) → x = 1 := by
    intro x hx hcomm
    have hxz : (⟨x, hx⟩ : ↥X) ∈ Subgroup.center ↥X :=
      Subgroup.mem_center_iff.mpr (fun g => Subtype.ext (hcomm g.1 g.2).symm)
    rw [hz, Subgroup.mem_bot] at hxz
    exact congrArg Subtype.val hxz
  have hX2 : ∀ x ∈ X, ∃ m : ℕ, x ^ 2 ^ m ∈ X := fun x hx => ⟨0, by simpa using hx⟩
  rcases hFM V hV X hirr X le_rfl Subgroup.le_normalizer hX hC hX2 with
    ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩
  · rw [Nat.card_congr e.toEquiv, CFSG.Quasithin.H47W.card_W9]
  · rw [Nat.card_congr e.toEquiv, Nat.card_prod, CFSG.Quasithin.H47W.card_W9]
    norm_num
  · rw [Nat.card_congr e.toEquiv, CFSG.Quasithin.H47W.card_Wn16]
    norm_num
  · rw [Nat.card_congr e.toEquiv, CFSG.Quasithin.H47W.card_Wn64]
    norm_num

theorem two_pow_nine_le_of_irreducible'
    (V : Type) [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    (X : Subgroup (MulAut V)) (hX : CFSG.Quasithin.IsPSL 3 2 2 ↥X)
    (hirr : CFSG.Quasithin.XMod.IsIrrSec ↥X (⊥ : Subgroup V) ⊤) : 2 ^ 9 ≤ Nat.card V :=
  two_pow_nine_le_of_irreducible CFSG.Quasithin.H13.Ch9.L34B.factL34Modules_holds V hV X hX hirr

theorem isPSL_of_mulEquiv {X Y : Type} [Group X] [Group Y] {n p e : ℕ} (f : X ≃* Y)
    (h : CFSG.Quasithin.IsPSL n p e X) : CFSG.Quasithin.IsPSL n p e Y := by
  obtain ⟨hadm, K, hK, hfin, hcard, ⟨g⟩⟩ := h
  exact ⟨hadm, K, hK, hfin, hcard, ⟨f.symm.trans g⟩⟩

theorem two_pow_nine_le_card (hFM : FaithfulL34ModDim) {L : Type} [Group L] [Finite L]
    (Q : Subgroup L) [Q.Normal] (hQ : IsPGroup 2 ↥Q)
    (hperf : ⁅(⊤ : Subgroup L), (⊤ : Subgroup L)⁆ = ⊤)
    (hPSL : CFSG.Quasithin.IsPSL 3 2 2 (L ⧸ Q)) (hnt : ⁅Q, (⊤ : Subgroup L)⁆ ≠ ⊥) :
    2 ^ 9 ≤ Nat.card ↥Q := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsimp : IsSimpleGroup (L ⧸ Q) := CFSG.Quasithin.H13.A5.isSimpleGroup_of_isPSL34 hPSL
  have hfe := CFSG.GroupTheory.frattini_elementary_quotient (p := 2) (P := ↥Q) hQ
  have hcomm : IsMulCommutative (↥Q ⧸ frattini ↥Q) := hfe.2.1
  have hexp : ∀ v : ↥Q ⧸ frattini ↥Q, v ^ 2 = 1 := hfe.2.2.1
  haveI := hcomm
  have hQC : Q ≤ (frattiniConjAct Q).ker := by
    intro q hq
    exact MonoidHom.mem_ker.mpr (frattiniConjAct_of_mem Q hQ ⟨q, hq⟩)
  let ψ : L ⧸ Q →* MulAut (↥Q ⧸ frattini ↥Q) := QuotientGroup.lift Q (frattiniConjAct Q) hQC
  have hψ : ∀ x : L, ψ (QuotientGroup.mk' Q x) = frattiniConjAct Q x := fun x => rfl
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Q a
    rw [hψ] at ha
    have hx : x ∈ Q := frattini_kernel_le Q hQ hperf hsimp hnt x ha
    exact (QuotientGroup.eq_one_iff x).mpr hx
  have hPSLX : CFSG.Quasithin.IsPSL 3 2 2 ↥ψ.range :=
    isPSL_of_mulEquiv (MonoidHom.ofInjective hinj) hPSL
  have hdim : 2 ^ 9 ≤ Nat.card (↥Q ⧸ frattini ↥Q) :=
    hFM (↥Q ⧸ frattini ↥Q) hexp ψ.range hPSLX
  have hmul := Subgroup.card_mul_index (frattini ↥Q)
  have hpos : 0 < Nat.card (frattini ↥Q) := Nat.card_pos
  have hidx : (frattini ↥Q).index = Nat.card (↥Q ⧸ frattini ↥Q) := rfl
  calc 2 ^ 9 ≤ Nat.card (↥Q ⧸ frattini ↥Q) := hdim
    _ = (frattini ↥Q).index := hidx.symm
    _ ≤ Nat.card (frattini ↥Q) * (frattini ↥Q).index := Nat.le_mul_of_pos_left _ hpos
    _ = Nat.card ↥Q := hmul

theorem two_pow_fifteen_dvd_card (hFM : FaithfulL34ModDim) {L S : Type} [Group L] [Finite L]
    [Group S] [Finite S] (j : L →* S) (hj : Function.Injective j) (Q : Subgroup L) [Q.Normal]
    (hQ : IsPGroup 2 ↥Q) (hperf : ⁅(⊤ : Subgroup L), (⊤ : Subgroup L)⁆ = ⊤)
    (hPSL : CFSG.Quasithin.IsPSL 3 2 2 (L ⧸ Q)) (hnt : ⁅Q, (⊤ : Subgroup L)⁆ ≠ ⊥) :
    2 ^ 15 ∣ Nat.card S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h9 := two_pow_nine_le_card hFM Q hQ hperf hPSL hnt
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := ↥Q)).mp hQ
  have h9n : 9 ≤ n := by
    rw [hn] at h9
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h9
  have hQdvd : 2 ^ 9 ∣ Nat.card ↥Q := by
    rw [hn]
    exact pow_dvd_pow 2 h9n
  have hquot : Nat.card (L ⧸ Q) = 20160 := CFSG.Quasithin.H13.A5.card_of_isPSL34 hPSL
  have hLcard : Nat.card L = Nat.card ↥Q * 20160 := by
    rw [← hquot]
    have := Subgroup.card_mul_index Q
    rw [← this]
    rfl
  have hL15 : 2 ^ 15 ∣ Nat.card L := by
    rw [hLcard]
    have h1 : 2 ^ 15 ∣ 2 ^ 9 * 20160 := ⟨315, by norm_num⟩
    exact dvd_trans h1 (mul_dvd_mul_right hQdvd 20160)
  exact dvd_trans hL15 (Subgroup.card_dvd_of_injective j hj)

end CFSG.SectionRank.QTK
