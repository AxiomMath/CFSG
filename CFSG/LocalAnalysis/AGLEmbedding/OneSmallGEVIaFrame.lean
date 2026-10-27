module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroFusion
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIaOrder
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSmallPFrame

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isElemAbelian_sup_zpowers_of_commute {A : Subgroup G} {z : G}
    (hA : IsElemAbelian 3 A) (hz3 : z ^ 3 = 1) (hzA : ∀ a ∈ A, a * z = z * a) :
    IsElemAbelian 3 (A ⊔ Subgroup.zpowers z) := by
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  set k : Set G := (A : Set G) ∪ (Subgroup.zpowers z : Set G) with hk
  have hcomm : k.Pairwise Commute := by
    intro x hx y hy _
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact hAc x hx y hy
    · obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact Commute.zpow_right (hzA x hx) j
    · obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact Commute.zpow_left (hzA y hy).symm j
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact Commute.zpow_zpow_self z i j
  have heq : A ⊔ Subgroup.zpowers z = Subgroup.closure k := Subgroup.sup_eq_closure _ _
  refine ⟨heq ▸ Subgroup.isMulCommutative_closure hcomm, fun x hx => ?_⟩
  rw [heq] at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with hy | hy
    · exact hA.2 y hy
    · obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz3, one_zpow]
  | one => exact one_pow 3
  | mul a b ha hb iha ihb =>
    have hab : Commute a b := by
      have := Subgroup.isMulCommutative_closure hcomm
      exact congrArg Subtype.val (this.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    rw [hab.mul_pow, iha, ihb, one_mul]
  | inv a ha iha => rw [inv_pow, iha, inv_one]

theorem le_card_of_frame_81 {P R : Subgroup G} {z : G} (hP : IsPGroup 3 P) (hRP : R ≤ P)
    (hRcard : Nat.card R = 81) (hzR : z ∈ R) (hzp : orderOf z = 3)
    (hRz : ∀ r ∈ R, r * z = z * r) (hB0 : ∀ g ∈ P, g * z = z * g → g ∈ R)
    (hZ : (fusionSet R z).ncard < 9) (hR3 : Open.pRank 3 R ≤ 3)
    (h4 : 4 ≤ Open.pRank 3 P) : 3 ^ 6 ≤ Nat.card P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hzp; norm_num at hzp
  have hz3 : z ^ 3 = 1 := by rw [← hzp]; exact pow_orderOf_eq_one z
  set N : Subgroup G := P ⊓ Subgroup.normalizer (R : Set G) with hNdef
  have hRN : R ≤ N := le_inf hRP Subgroup.le_normalizer
  have hNp : IsPGroup 3 N := hP.to_le inf_le_left
  have hidx := index_le_ncard_fusionSet (N := N) inf_le_right hz1
    (fun n hn hc => hB0 n hn.1 hc) hRz
  have hNcard : Nat.card N ≤ 243 := by
    have := card_le_three_mul_of_index_lt_nine hRN hNp (hidx.trans_lt hZ)
    rw [hRcard] at this
    omega
  obtain ⟨E, hEP, hEel, hEcard⟩ :=
    CFSG.PreuniquenessRankFour.Helpers.pRank_attained 3 Nat.prime_three P
  have hE81 : 81 ≤ Nat.card E := by
    rw [hEcard]
    calc 81 = 3 ^ 4 := by norm_num
      _ ≤ 3 ^ Open.pRank 3 P := Nat.pow_le_pow_right (by norm_num) h4
  have hno : ∀ F : Subgroup G, F ≤ R → IsElemAbelian 3 F → 81 ≤ Nat.card F → False := by
    intro F hFR hF h81
    have hFp : IsPGroup 3 F := fun x => ⟨1, Subtype.ext (by simpa using hF.2 x x.2)⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hFp
    have hkR : k ≤ Open.pRank 3 R :=
      le_csSup (CFSG.PreuniquenessRankFour.Helpers.pRank_bddAbove 3 Nat.prime_three R)
        ⟨F, hFR, hF, hk⟩
    have hk4 : 4 ≤ k := by
      by_contra hlt
      push Not at hlt
      have : 3 ^ k ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    omega
  have hNP : N ≠ P := by
    intro hNP
    have hEN : E ≤ N := hNP ▸ hEP
    have hEnorm : E ≤ Subgroup.normalizer (R : Set G) := hEN.trans inf_le_right
    have hc := card_sup_mul_card_inf_eq_of_le_normalizer hEnorm
    have hsup : Nat.card (R ⊔ E : Subgroup G) ≤ 243 :=
      (Subgroup.card_le_of_le (sup_le hRN hEN)).trans hNcard
    have hI : 27 ≤ Nat.card (R ⊓ E : Subgroup G) := by
      rw [hRcard] at hc
      by_contra h
      push Not at h
      have : Nat.card (R ⊔ E : Subgroup G) * Nat.card (R ⊓ E : Subgroup G) ≤ 243 * 26 :=
        Nat.mul_le_mul hsup (by omega)
      omega
    have hIel : IsElemAbelian 3 (R ⊓ E : Subgroup G) :=
      ⟨⟨⟨fun a b => Subtype.ext (by
        have := congrArg Subtype.val (hEel.1.is_comm.comm ⟨a, a.2.2⟩ ⟨b, b.2.2⟩)
        simpa using this)⟩⟩, fun x hx => hEel.2 x hx.2⟩
    by_cases hzE : z ∈ E
    ·
      have hER : E ≤ R := fun e he => hB0 e (hEP he)
        (congrArg Subtype.val (hEel.1.is_comm.comm ⟨e, he⟩ ⟨z, hzE⟩))
      exact hno E hER hEel hE81
    ·
      have hF := isElemAbelian_sup_zpowers_of_commute hIel hz3 (fun a ha => hRz a ha.1)
      have hFR : (R ⊓ E) ⊔ Subgroup.zpowers z ≤ R := sup_le inf_le_left
        (Subgroup.zpowers_le.mpr hzR)
      have hinf : (R ⊓ E) ⊓ Subgroup.zpowers z = ⊥ := by
        rw [eq_bot_iff]
        intro x ⟨hxI, hxz⟩
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxz
        by_contra hne
        apply hzE
        have := mem_zpowers_of_mem_zpowers_of_prime Nat.prime_three hzp
          (Subgroup.zpow_mem_zpowers z j) hne
        exact (Subgroup.zpowers_le.mpr hxI.2) this
      have hcardF := mul_card_le_of_inf_eq_bot (le_sup_left : R ⊓ E ≤ (R ⊓ E) ⊔ _)
        (le_sup_right : Subgroup.zpowers z ≤ (R ⊓ E) ⊔ _) hinf
      rw [Nat.card_zpowers, hzp] at hcardF
      exact hno _ hFR hF (by omega)
  have hRP' : R ≠ P := by
    intro h
    rw [h] at hR3
    omega
  have hRN' : R ≠ N := by
    intro hRN''
    apply hRP'
    symm
    exact eq_of_isPGroup_of_le_of_normalizer hP hRP fun g hgP hgN => by
      rw [hRN'']
      exact ⟨hgP, hgN⟩
  have h1 : 3 * Nat.card R ≤ Nat.card N := three_mul_card_le_of_lt hNp hRN hRN'
  have h2 : 3 * Nat.card N ≤ Nat.card P := three_mul_card_le_of_lt hP inf_le_left hNP
  rw [hRcard] at h1
  calc 3 ^ 6 = 3 * (3 * 81) := by norm_num
    _ ≤ 3 * Nat.card N := Nat.mul_le_mul_left 3 h1
    _ ≤ Nat.card P := h2

end CFSG.AGLEmbedding
