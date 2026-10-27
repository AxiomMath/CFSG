module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ4FinkCheck
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicYCore
public import CFSG.Sporadic.J4.QTOutChar
public import CFSG.Sporadic.J4.QT2LocCntMain
public import CFSG.Sporadic.J4.QT2AGen

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.J4Fink

open Subgroup CFSG.ABGLocalTools CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2
open CFSG.Sporadic.J4.Native

section Generic

variable {G : Type*} [Group G]

theorem eq_one_or_eq_of_mem_zpowers {z g : G} (hz : z * z = 1) (hg : g ∈ zpowers z) :
    g = 1 ∨ g = z := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
  have h2 : z ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hz
  rw [zpow_eq_zpow_emod k h2]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [h, zpow_zero]
  · right
    rw [h, zpow_one]

theorem exists_mem_second_center [Finite G] {S N : Subgroup G} {z : G} (hS : IsPGroup 2 S)
    (hNS : N ≤ S) (hn : ∀ s ∈ S, ∀ x ∈ N, s * x * s⁻¹ ∈ N) (hz : ∀ s ∈ S, s * z = z * s)
    (hN : ¬ N ≤ zpowers z) :
    ∃ x ∈ N, x ∉ zpowers z ∧ ∀ s ∈ S, x * s * x⁻¹ * s⁻¹ ∈ zpowers z := by
  obtain ⟨Z, hZ⟩ : ∃ Z : Subgroup S, Z = (zpowers z).subgroupOf S := ⟨_, rfl⟩
  have hmemZ : ∀ x : S, x ∈ Z ↔ (x : G) ∈ zpowers z := fun x => by rw [hZ, mem_subgroupOf]
  have : Z.Normal := ⟨fun n hn g => by
    rw [hmemZ] at hn ⊢
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hn
    have hc : Commute (g : G) (n : G) := by
      rw [← hk]
      exact (show Commute (g : G) z from hz g g.2).zpow_right k
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hc.eq, mul_inv_cancel_right]
    exact hn⟩
  have hone : ∀ x : S, QuotientGroup.mk' Z x = 1 ↔ (x : G) ∈ zpowers z := fun x => by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hmemZ]
  have hQp : IsPGroup 2 (⊤ : Subgroup (S ⧸ Z)) := (hS.to_quotient Z).to_subgroup ⊤
  have hN'n : ∀ s ∈ (⊤ : Subgroup (S ⧸ Z)), ∀ x ∈ (N.subgroupOf S).map (QuotientGroup.mk' Z),
      s * x * s⁻¹ ∈ (N.subgroupOf S).map (QuotientGroup.mk' Z) := by
    intro s _ x hx
    obtain ⟨s', rfl⟩ := QuotientGroup.mk'_surjective Z s
    obtain ⟨x', hx', rfl⟩ := hx
    refine ⟨s' * x' * s'⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    rw [SetLike.mem_coe, mem_subgroupOf] at hx' ⊢
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hn _ s'.2 _ hx'
  have hN'ne : (N.subgroupOf S).map (QuotientGroup.mk' Z) ≠ ⊥ := by
    obtain ⟨y, hyN, hyz⟩ := IsConcreteLE.not_le_iff_exists.mp hN
    intro hbot
    have hmem : QuotientGroup.mk' Z ⟨y, hNS hyN⟩ ∈ (N.subgroupOf S).map (QuotientGroup.mk' Z) :=
      ⟨⟨y, hNS hyN⟩, hyN, rfl⟩
    rw [hbot, mem_bot, hone] at hmem
    exact hyz hmem
  obtain ⟨_, ⟨x, hx, rfl⟩, hx1, -, hxc⟩ :=
    QT2A.exists_central_involution ⊤ _ hQp le_top hN'n hN'ne
  refine ⟨x, mem_subgroupOf.mp hx, fun hxz => hx1 ((hone x).2 hxz), fun s hs => ?_⟩
  have h := hxc (QuotientGroup.mk' Z ⟨s, hs⟩) (mem_top _)
  have h1 : QuotientGroup.mk' Z (x * ⟨s, hs⟩ * x⁻¹ * (⟨s, hs⟩ : S)⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← h]
    group
  exact (hone _).1 h1

theorem false_of_dihedral [Finite G] {M : Subgroup G} {u v : G} (hu : u ∈ M) (hv : v ∈ M)
    (hu2 : u * u = 1) (hv2 : v * v = 1) (hu1 : u ≠ 1) (hw4 : (u * v) ^ 4 = 1)
    (hw2 : (u * v) ^ 2 ≠ 1)
    (hab : ∀ Q : Subgroup G, Q ≤ M → IsPGroup 2 Q → ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨w, hw⟩ : ∃ w, w = u * v := ⟨_, rfl⟩
  rw [← hw] at hw4 hw2
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  have huw : u * w * u⁻¹ = w⁻¹ := by
    rw [hw, mul_inv_rev, hvi, hui, ← mul_assoc, hu2, one_mul]
  have hu_ord : orderOf u = 2 := orderOf_eq_prime (by rw [sq]; exact hu2) hu1
  have hw_ord : orderOf w = 4 := by
    have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := w) (by simpa using hw2)
      (by simpa using hw4)
    simpa using this
  have hPu : IsPGroup 2 (zpowers u) :=
    IsPGroup.of_card (n := 1) (by simp [Nat.card_zpowers, hu_ord])
  have hPw : IsPGroup 2 (zpowers w) :=
    IsPGroup.of_card (n := 2) (by simp [Nat.card_zpowers, hw_ord])
  have hconj : ∀ k : ℤ, u * w ^ k * u⁻¹ = w⁻¹ ^ k := fun k => by
    rw [← huw, conj_zpow]
  have hnorm : zpowers u ≤ normalizer (zpowers w : Set G) := by
    rw [zpowers_le, mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hh
      rw [hconj]
      exact zpow_mem (inv_mem (mem_zpowers w)) k
    · intro hh
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hh
      have hh' : h = u * w ^ k * u⁻¹ := by
        calc h = (u * u) * h * (u * u)⁻¹ := by rw [hu2, one_mul, inv_one, mul_one]
          _ = u * (u * h * u⁻¹) * u⁻¹ := by group
          _ = u * w ^ k * u⁻¹ := by rw [hk]
      rw [hh', hconj]
      exact zpow_mem (inv_mem (mem_zpowers w)) k
  have hD := IsPGroup.to_sup_of_normal_right' hPu hPw hnorm
  have hwM : w ∈ M := by
    rw [hw]
    exact mul_mem hu hv
  have hDM : zpowers u ⊔ zpowers w ≤ M := sup_le (zpowers_le.mpr hu) (zpowers_le.mpr hwM)
  have hcomm := hab _ hDM hD u (mem_sup_left (mem_zpowers u)) w (mem_sup_right (mem_zpowers w))
  have h1 : w = w⁻¹ := by
    rw [← huw, hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hww : w * w = 1 := by
    calc w * w = w * w⁻¹ := by rw [← h1]
      _ = 1 := mul_inv_cancel w
  exact hw2 (by rw [sq]; exact hww)

end Generic

section TwoA

theorem mem_Zc_zero {x : J} : x ∈ Zc 0 ↔ x = 1 := Iff.rfl

theorem mem_Zc_succ {k : ℕ} {x : J} :
    x ∈ Zc (k + 1) ↔ x ∈ P0 ∧ ∀ y ∈ P0, x * y * x⁻¹ * y⁻¹ ∈ Zc k := Iff.rfl

theorem mem_ZE {L : List ℕ} {x : J} : x ∈ QT.ZE L ↔ ∃ c ∈ L, x = eta uJ 11 c := Iff.rfl

theorem Zc_one :
    Zc 1 = QT.ZE [0, 1131] :=
  Zc_eq j4Facts.mat j4Facts 1 (by norm_num)

theorem Zc_two :
    Zc 2 = QT.ZE [0, 911, 1131, 2020] :=
  Zc_eq j4Facts.mat j4Facts 2 (by norm_num)

theorem eta_1131_mem_Zc_one :
    eta uJ 11 1131 ∈ Zc 1 := by
  rw [Zc_one]
  exact mem_ZE.mpr ⟨1131, by simp, rfl⟩

theorem P0_le_centralizer_z :
    P0 ≤ centralizer ({eta uJ 11 1131} : Set J) := by
  intro x hx
  rw [mem_centralizer_singleton_iff]
  have h := (mem_Zc_succ.mp eta_1131_mem_Zc_one).2 x hx
  rw [mem_Zc_zero, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h
  exact h.symm

theorem card_centralizer_z_factorization :
    (Nat.card ↥(centralizer ({eta uJ 11 1131} : Set J))).factorization 2 = 21 := by
  rw [card_centralizer_eta_1131]
  have h : (21799895040 : ℕ) = 2 ^ 21 * 10395 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  norm_num

theorem isSylowOf_P0_centralizer_z :
    IsSylowOf 2 P0 (centralizer ({eta uJ 11 1131} : Set J)) := by
  refine isSylowOf_of_card P0_le_centralizer_z ?_
  rw [card_P0 j4Facts.mat j4Facts, card_centralizer_z_factorization]

theorem eq_of_central
    {x : J} (hx : x ∈ P0)
    (hc : ∀ s ∈ P0, s * x = x * s) :
    x = 1 ∨ x = eta uJ 11 1131 := by
  have hZ : x ∈ Zc 1 := mem_Zc_succ.mpr ⟨hx, fun y hy => by
    rw [mem_Zc_zero, mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
    exact (hc y hy).symm⟩
  rw [Zc_one] at hZ
  obtain ⟨c, hcL, rfl⟩ := mem_ZE.mp hZ
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hcL
  rcases hcL with rfl | rfl
  · exact Or.inl (eta_zero _ _)
  · exact Or.inr rfl

theorem c1_facts :
    mixElt y7Word ∈ centralizer ({eta uJ 11 1131} : Set J) ∧
      (eta uJ 11 911 * (mixElt y7Word * eta uJ 11 911 * (mixElt y7Word)⁻¹)) ^ 4 = 1 ∧
      (eta uJ 11 911 * (mixElt y7Word * eta uJ 11 911 * (mixElt y7Word)⁻¹)) ^ 2 ≠ 1 := by
  have hM := j4Facts.mat
  have hcomm : chkCommRoot (locMats ()) (locInvs ()) y7Word = true := by
    have h := y7Word_check
    unfold chkOrder at h
    rw [Bool.and_eq_true] at h
    exact h.1
  have hy7 : mixElt y7Word ^ 7 = 1 := by
    rw [← orderOf_mixElt hM y7Word (by norm_num) y7Word_check]
    exact pow_orderOf_eq_one _
  have hinv : (mixElt y7Word)⁻¹ = mixElt y7Word ^ 6 := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ']
    exact hy7
  have hMx : Mx (eta uJ 11 911 * (mixElt y7Word * eta uJ 11 911 * (mixElt y7Word)⁻¹)) =
      rowsMatrix (mulRows (etaRows (uTab (locMats ()) (locInvs ())) 11 z2Mask)
        (mulRows (mulRows (mixRowsOf y7Word) (etaRows (uTab (locMats ()) (locInvs ())) 11 z2Mask))
          (powRows (mixRowsOf y7Word) 6))) := by
    rw [hinv, map_mul, map_mul, map_mul, map_pow, Mx_eta hM 11 le_rfl, Mx_mixElt hM,
      rowsMatrix_mulRows, rowsMatrix_mulRows, rowsMatrix_mulRows, rowsMatrix_powRows]
    rfl
  have hC1 := fink_c1Check
  unfold chkFinkC1 at hC1
  simp only [Bool.and_eq_true] at hC1
  obtain ⟨h4, h2⟩ := hC1
  refine ⟨mem_centralizer_singleton_iff.mpr (mixElt_comm_notin hM y7Word hcomm).1, ?_, ?_⟩
  · apply Mx_injective
    rw [map_pow, hMx, ← rowsMatrix_powRows, eqRows_iff.1 h4, rowsMatrix_idRows, map_one]
  · intro hsq
    have hsq' := congrArg Mx hsq
    rw [map_pow, map_one, hMx, ← rowsMatrix_powRows] at hsq'
    apply differs_toVec h2
    rw [frApply_toVec_eq_vecMul, hsq', Matrix.vecMul_one]

theorem false_of_twoA
    {M P : Subgroup J}
    (hMz : M ≤ centralizer ({eta uJ 11 1131} : Set J))
    (hMn : ∀ c ∈ centralizer ({eta uJ 11 1131} : Set J), ∀ m ∈ M, c * m * c⁻¹ ∈ M)
    (hab : ∀ Q : Subgroup J, Q ≤ M → IsPGroup 2 Q → ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x)
    (hPM : P ≤ M) (hP : IsPGroup 2 P) (hP4 : 4 ≤ Nat.card P) : False := by
  have hM := j4Facts.mat
  obtain ⟨m, hm, hmP⟩ :=
    exists_conj_le_of_isSylowOf isSylowOf_P0_centralizer_z hP (hPM.trans hMz)
  have hN4 : 4 ≤ Nat.card ↥(M ⊓ P0) := by
    refine hP4.trans (Nat.card_le_card_of_injective
      (fun x : P => (⟨m⁻¹ * x * m, mem_inf.mpr ⟨?_, hmP x x.2⟩⟩ : ↥(M ⊓ P0))) ?_)
    · simpa using hMn m⁻¹ (inv_mem hm) x (hPM x.2)
    · intro a b hab
      have h := congrArg Subtype.val hab
      simp only at h
      exact Subtype.ext (mul_left_cancel (mul_right_cancel h))
  have hNn : ∀ s ∈ P0, ∀ x ∈ M ⊓ P0, s * x * s⁻¹ ∈ M ⊓ P0 := fun s hs x hx =>
    mem_inf.mpr ⟨hMn s (P0_le_centralizer_z hs) x (mem_inf.mp hx).1,
      mul_mem (mul_mem hs (mem_inf.mp hx).2) (inv_mem hs)⟩
  have hz2 : eta uJ 11 1131 * eta uJ 11 1131 = 1 := by
    rw [← eta_xor (elem_uJ hM) le_rfl, Nat.xor_self, eta_zero]
  have hzN : eta uJ 11 1131 ∈ M ⊓ P0 := by
    have hne : M ⊓ P0 ≠ ⊥ := by
      intro h
      rw [h, card_bot] at hN4
      omega
    obtain ⟨z', hz'N, hz'1, -, hz'c⟩ :=
      QT2A.exists_central_involution P0 (M ⊓ P0) isSylowOf_P0_centralizer_z.isPGroup
        inf_le_right hNn hne
    rcases eq_of_central (mem_inf.mp hz'N).2 hz'c with h | h
    · exact absurd h hz'1
    · rw [← h]
      exact hz'N
  have hzc : ∀ s ∈ P0, s * eta uJ 11 1131 = eta uJ 11 1131 * s := by
    intro s hs
    have h := P0_le_centralizer_z hs
    rw [mem_centralizer_singleton_iff] at h
    exact h
  have hNz : ¬ M ⊓ P0 ≤ zpowers (eta uJ 11 1131) := by
    intro hle
    have h1 := card_le_of_le hle
    have hord : orderOf (eta uJ 11 1131) = 2 :=
      orderOf_eq_prime (by rw [sq]; exact hz2) (eta_ne_one hM (by norm_num) (by norm_num))
    rw [Nat.card_zpowers, hord] at h1
    omega
  obtain ⟨x, hxN, hxz, hxc⟩ :=
    exists_mem_second_center isSylowOf_P0_centralizer_z.isPGroup inf_le_right hNn hzc hNz
  have hxZ2 : x ∈ Zc 2 := by
    refine mem_Zc_succ.mpr ⟨(mem_inf.mp hxN).2, fun y hy => ?_⟩
    have hcases : x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = eta uJ 11 1131 :=
      eq_one_or_eq_of_mem_zpowers hz2 (hxc y hy)
    rw [Zc_one]
    rcases hcases with h | h
    · exact mem_ZE.mpr ⟨0, by simp, by rw [h, eta_zero]⟩
    · exact mem_ZE.mpr ⟨1131, by simp, h⟩
  rw [Zc_two] at hxZ2
  obtain ⟨c, hcL, rfl⟩ := mem_ZE.mp hxZ2
  have hu : eta uJ 11 911 ∈ M := by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hcL
    rcases hcL with rfl | rfl | rfl | rfl
    · exact (hxz (by rw [eta_zero]; exact one_mem _)).elim
    · exact (mem_inf.mp hxN).1
    · exact (hxz (mem_zpowers _)).elim
    · have hx : (2020 ^^^ 1131 : ℕ) = 911 := by decide
      have h911 : eta uJ 11 911 = eta uJ 11 2020 * eta uJ 11 1131 := by
        calc eta uJ 11 911 = eta uJ 11 (2020 ^^^ 1131) := by rw [hx]
          _ = _ := eta_xor (elem_uJ hM) le_rfl 2020 1131
      rw [h911]
      exact mul_mem (mem_inf.mp hxN).1 (mem_inf.mp hzN).1
  obtain ⟨hy, hw4, hw2⟩ := c1_facts
  have hu2 : eta uJ 11 911 * eta uJ 11 911 = 1 := by
    rw [← eta_xor (elem_uJ hM) le_rfl, Nat.xor_self, eta_zero]
  have hv2 : (mixElt y7Word * eta uJ 11 911 * (mixElt y7Word)⁻¹) *
      (mixElt y7Word * eta uJ 11 911 * (mixElt y7Word)⁻¹) = 1 := by
    calc (mixElt y7Word * eta uJ 11 911 * (mixElt y7Word)⁻¹) *
        (mixElt y7Word * eta uJ 11 911 * (mixElt y7Word)⁻¹) =
          mixElt y7Word * (eta uJ 11 911 * eta uJ 11 911) * (mixElt y7Word)⁻¹ := by group
      _ = 1 := by rw [hu2, mul_one, mul_inv_cancel]
  exact false_of_dihedral hu (hMn _ hy _ hu) hu2 hv2 (eta_ne_one hM (by norm_num) (by norm_num))
    hw4 hw2 hab

end TwoA

end CFSG.ComponentClassification.RankTwoSporadic.J4Fink
