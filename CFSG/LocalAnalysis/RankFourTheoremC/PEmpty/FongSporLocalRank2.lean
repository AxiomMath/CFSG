module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalRows
public import CFSG.LocalAnalysis.SectionRank.GroupRankTransport
public import CFSG.LocalAnalysis.SectionRank.AmbientRank
public import CFSG.Sporadic.NativeFinite
public import CFSG.Sporadic.Bridge.J2
public import CFSG.Sporadic.Bridge.HSSurj
public import CFSG.Sporadic.Presentation.McLExact
public import CFSG.Sporadic.Bridge.HeSurj
public import CFSG.Sporadic.Bridge.RuSurj
public import CFSG.Sporadic.Bridge.SuzSurj
public import CFSG.Sporadic.Bridge.ONSurj
public import CFSG.Sporadic.Presentation.Co2Exact
public import CFSG.Sporadic.Bridge.Co3Surj
public import CFSG.Sporadic.Bridge.J4Surj
public import CFSG.Sporadic.Bridge.LySurj
public import CFSG.Sporadic.Bridge.HNSurj
public import CFSG.Sporadic.Bridge.ThSurj
public import CFSG.RankThree.PartTwo.Sec17.G1724J2
public import CFSG.RankThree.PartOne.MultRes.McL
public import CFSG.RankThree.PartOne.MultRes.Suz
public import CFSG.RankThree.PartOne.MultRes.ON
public import CFSG.RankThree.PartOne.MultRes.Co2
public import CFSG.RankThree.PartOne.MultRes.Co3
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2PRankFive
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2PRankHNFive
public import CFSG.RankThree.PartOne.MultRes.Th

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

open CFSG.Open Subgroup
open scoped commutatorElement

theorem closure_comm_of_pairwise {G : Type*} [Group G] {S : Set G}
    (hS : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) {a b : G}
    (ha : a ∈ Subgroup.closure S) (hb : b ∈ Subgroup.closure S) : a * b = b * a := by
  have h1 : ∀ c ∈ Subgroup.closure S, ∀ s ∈ S, Commute c s := by
    intro c hc s hs
    induction hc using Subgroup.closure_induction with
    | mem x hx => exact hS x hx s hs
    | one => exact Commute.one_left s
    | mul x y _ _ hx hy => exact hx.mul_left hy
    | inv x _ hx => exact hx.inv_left
  have h2 : ∀ d ∈ Subgroup.closure S, ∀ c ∈ Subgroup.closure S, Commute c d := by
    intro d hd c hc
    induction hd using Subgroup.closure_induction with
    | mem x hx => exact h1 c hc x hx
    | one => exact Commute.one_right c
    | mul x y _ _ hx hy => exact hx.mul_right hy
    | inv x _ hx => exact hx.inv_right
  exact h2 b hb a ha

theorem isMulCommutative_closure_of_pairwise {G : Type*} [Group G] {S : Set G}
    (hS : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) :
    IsMulCommutative (↥(Subgroup.closure S)) :=
  ⟨⟨fun a b => Subtype.ext (closure_comm_of_pairwise hS a.2 b.2)⟩⟩

theorem closure_pow_eq_one_of_pairwise {G : Type*} [Group G] {S : Set G} {p : ℕ}
    (hS : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) (hp : ∀ s ∈ S, s ^ p = 1) {w : G}
    (hw : w ∈ Subgroup.closure S) : w ^ p = 1 := by
  induction hw using Subgroup.closure_induction with
  | mem x hx => exact hp x hx
  | one => exact one_pow p
  | mul x y hx hy ihx ihy =>
    have hc : Commute x y := closure_comm_of_pairwise hS hx hy
    rw [hc.mul_pow, ihx, ihy, one_mul]
  | inv x hx ih => rw [inv_pow, ih, inv_one]

theorem rank2_bddAbove {G : Type*} [Group G] [Finite G] (p : ℕ) (hp : 2 ≤ p) (H : Subgroup G) :
    BddAbove {k : ℕ | ∃ E : Subgroup G, E ≤ H ∧ CFSG.Open.IsElemAbelian p E ∧
      Nat.card E = p ^ k} := by
  refine ⟨Nat.card G, ?_⟩
  rintro k ⟨E, -, -, hE⟩
  have h1 : Nat.card E ≤ Nat.card G := Subgroup.card_le_card_group E
  have h2 : k < p ^ k := Nat.lt_pow_self (by omega)
  calc k ≤ p ^ k := h2.le
    _ = Nat.card E := hE.symm
    _ ≤ Nat.card G := h1

theorem two_le_pRank_of_commuting {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) {x y : G}
    (hx : x ^ p = 1) (hy : y ^ p = 1) (hxy : x * y = y * x)
    (hc : Nat.card (Subgroup.closure ({x, y} : Set G)) = p ^ 2) :
    2 ≤ CFSG.Open.pRank p (⊤ : Subgroup G) := by
  have hS : ∀ a ∈ ({x, y} : Set G), ∀ b ∈ ({x, y} : Set G), a * b = b * a := by
    intro a ha b hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with h | h <;> rcases hb with h' | h' <;> rw [h, h']
    all_goals first | rfl | exact hxy | exact hxy.symm
  have hpS : ∀ s ∈ ({x, y} : Set G), s ^ p = 1 := by
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with h | h
    · rw [h]; exact hx
    · rw [h]; exact hy
  have hE : CFSG.Open.IsElemAbelian p (Subgroup.closure ({x, y} : Set G)) := by
    unfold CFSG.Open.IsElemAbelian
    exact ⟨isMulCommutative_closure_of_pairwise hS, fun w hw =>
      closure_pow_eq_one_of_pairwise hS hpS hw⟩
  have hmem : (2 : ℕ) ∈ {k : ℕ | ∃ E : Subgroup G, E ≤ (⊤ : Subgroup G) ∧
      CFSG.Open.IsElemAbelian p E ∧ Nat.card E = p ^ k} :=
    ⟨Subgroup.closure ({x, y} : Set G), le_top, hE, hc⟩
  unfold CFSG.Open.pRank
  exact le_csSup (rank2_bddAbove p hp.two_le ⊤) hmem

theorem two_le_pRank_of_heisenberg {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) {x y : G}
    (hx : x ^ p = 1) (hy : y ^ p = 1) (hne : ⁅x, y⁆ ≠ 1) (hzx : Commute ⁅x, y⁆ x)
    (hzy : Commute ⁅x, y⁆ y) (hc : Nat.card (Subgroup.closure ({x, y} : Set G)) = p ^ 3) :
    2 ≤ CFSG.Open.pRank p (⊤ : Subgroup G) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hkey : x * y = ⁅x, y⁆ * y * x := by
    rw [commutatorElement_def]; group
  have hxH : x ∈ Subgroup.closure ({x, y} : Set G) := Subgroup.subset_closure (by simp)
  have hyH : y ∈ Subgroup.closure ({x, y} : Set G) := Subgroup.subset_closure (by simp)
  have hzH : ⁅x, y⁆ ∈ Subgroup.closure ({x, y} : Set G) := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hxH hyH) (inv_mem hxH)) (inv_mem hyH)
  obtain ⟨z, hz⟩ : ∃ z, ⁅x, y⁆ = z := ⟨_, rfl⟩
  rw [hz] at hkey hne hzx hzy hzH
  have hkey2 : x * y = y * x * z := by
    calc x * y = z * y * x := hkey
      _ = y * z * x := by rw [hzy.eq]
      _ = y * (z * x) := by rw [mul_assoc]
      _ = y * (x * z) := by rw [hzx.eq]
      _ = y * x * z := by rw [mul_assoc]
  have hpow : ∀ k : ℕ, x * y ^ k = y ^ k * x * z ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hzk : Commute (z ^ k) y := hzy.pow_left k
      calc x * y ^ (k + 1) = x * y ^ k * y := by rw [pow_succ, mul_assoc]
        _ = y ^ k * x * z ^ k * y := by rw [ih]
        _ = y ^ k * x * (z ^ k * y) := by rw [mul_assoc (y ^ k * x) (z ^ k) y]
        _ = y ^ k * x * (y * z ^ k) := by rw [hzk.eq]
        _ = y ^ k * (x * y) * z ^ k := by simp only [mul_assoc]
        _ = y ^ k * (y * x * z) * z ^ k := by rw [hkey2]
        _ = y ^ (k + 1) * x * z ^ (k + 1) := by
          rw [pow_succ y k, pow_succ' z k]; simp only [mul_assoc]
  have hzp : z ^ p = 1 := by
    have h1 := hpow p
    rw [hy, mul_one, one_mul] at h1
    have h2 : x * z ^ p = x * 1 := by rw [mul_one]; exact h1.symm
    exact mul_left_cancel h2
  have hx1 : x ≠ 1 := by
    intro h
    apply hne
    rw [← hz, h]
    simp [commutatorElement_def]
  have hord_x : orderOf x = p := orderOf_eq_prime hx hx1
  have hord_z : orderOf z = p := orderOf_eq_prime hzp hne
  have hzn : z ∉ Subgroup.zpowers x := by
    intro hzmem
    have hle : Subgroup.zpowers z ≤ Subgroup.zpowers x := Subgroup.zpowers_le.mpr hzmem
    have hcard : Nat.card (Subgroup.zpowers x) ≤ Nat.card (Subgroup.zpowers z) :=
      le_of_eq (by rw [Nat.card_zpowers, Nat.card_zpowers, hord_x, hord_z])
    have heq : Subgroup.zpowers z = Subgroup.zpowers x :=
      Subgroup.eq_of_le_of_card_ge hle hcard
    have hxz : x ∈ Subgroup.zpowers z := by
      rw [heq]; exact Subgroup.mem_zpowers x
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxz
    have hcomm : Commute x y := by
      rw [← hk]; exact hzy.zpow_left k
    apply hne
    rw [← hz]
    exact commutatorElement_eq_one_iff_mul_comm.mpr hcomm.eq
  have hxz_comm : x * z = z * x := hzx.eq.symm
  have hS_xz : ∀ a ∈ ({x, z} : Set G), ∀ b ∈ ({x, z} : Set G), a * b = b * a := by
    intro a ha b hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with h | h <;> rcases hb with h' | h' <;> rw [h, h']
    all_goals first | rfl | exact hxz_comm | exact hxz_comm.symm
  have hEH : Subgroup.closure ({x, z} : Set G) ≤ Subgroup.closure ({x, y} : Set G) := by
    rw [Subgroup.closure_le]
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with h | h
    · rw [h]; exact hxH
    · rw [h]; exact hzH
  have hxE : Subgroup.zpowers x ≤ Subgroup.closure ({x, z} : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
  have hzE : z ∈ Subgroup.closure ({x, z} : Set G) := Subgroup.subset_closure (by simp)
  have hdvd : Nat.card (Subgroup.closure ({x, z} : Set G)) ∣ p ^ 3 := by
    rw [← hc]
    exact Subgroup.card_dvd_of_le hEH
  obtain ⟨m, hm, hEm⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  have hcardE : Nat.card (Subgroup.closure ({x, z} : Set G)) = p ^ 2 := by
    interval_cases m
    ·
      exfalso
      have h1 : p ∣ Nat.card (Subgroup.closure ({x, z} : Set G)) := by
        have h2 := Subgroup.card_dvd_of_le hxE
        rw [Nat.card_zpowers, hord_x] at h2
        exact h2
      rw [hEm, pow_zero] at h1
      exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
    ·
      exfalso
      have heq : Subgroup.zpowers x = Subgroup.closure ({x, z} : Set G) :=
        Subgroup.eq_of_le_of_card_ge hxE
          (le_of_eq (by rw [hEm, pow_one, Nat.card_zpowers, hord_x]))
      apply hzn
      rw [heq]
      exact hzE
    · exact hEm
    ·
      exfalso
      have heq : Subgroup.closure ({x, z} : Set G) = Subgroup.closure ({x, y} : Set G) :=
        Subgroup.eq_of_le_of_card_ge hEH (le_of_eq (by rw [hEm, hc]))
      have hyE : y ∈ Subgroup.closure ({x, z} : Set G) := by
        rw [heq]
        exact Subgroup.subset_closure (by simp)
      have hxE' : x ∈ Subgroup.closure ({x, z} : Set G) := Subgroup.subset_closure (by simp)
      have hcomm : x * y = y * x := closure_comm_of_pairwise hS_xz hxE' hyE
      apply hne
      rw [← hz]
      exact commutatorElement_eq_one_iff_mul_comm.mpr hcomm
  exact two_le_pRank_of_commuting hp hx hzp hxz_comm hcardE

theorem two_le_pRank_of_mulEquiv {A : Type} [Group A] [Finite A] (L : Subgroup A) {H : Type}
    [Group H] [Finite H] (e : ↥L ≃* H) {p : ℕ} (hp : p.Prime)
    (h : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup H)) :
    2 ≤ CFSG.Open.pRank p L := by
  rw [← CFSG.SectionRank.pRank_coe_eq_openPRank p L, CFSG.pRank_congr_of_mulEquiv e p,
    CFSG.SectionRank.pRank_eq_open_pRank_top p H]
  exact h

theorem row_of_rank2 (s : TauCeti.SporadicName) (p : ℕ)
    (h : ∀ (A : Type) [Group A] [Finite A] (L : Subgroup A),
      Nonempty (↥L ≃* (TauCeti.CFSGIndex.sporadic s).Group) → 2 ≤ CFSG.Open.pRank p L) :
    KFactSporLocalRow s p := by
  unfold KFactSporLocalRow
  intro A _ _ L K₀ z hL _ _ hp hp5 hrk
  exact absurd (h A L hL) (by omega)

theorem rank2_J2_5 :
    ∀ (A : Type) [Group A] [Finite A] (L : Subgroup A),
      Nonempty (↥L ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.J2).Group) →
        2 ≤ CFSG.Open.pRank 5 L := by
  intro A _ _ L hL
  obtain ⟨eL⟩ := hL
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J2.nonempty_mulEquiv
  haveI : Finite CFSG.Blueprint.NativeSporadic.J2 :=
    CFSG.Sporadic.finite_carrier_of_ne_M TauCeti.SporadicName.J2 (by decide)
  have hN : 2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup CFSG.Blueprint.NativeSporadic.J2) :=
    CFSG.RankThree.PartTwo.Sec17.G1724.two_le_pRank_five_J2
  exact two_le_pRank_of_mulEquiv L (eL.trans b.symm) (by norm_num) hN

theorem row_J2_5 :
    KFactSporLocalRow TauCeti.SporadicName.J2 5 :=
  row_of_rank2 TauCeti.SporadicName.J2 5 rank2_J2_5

theorem rank2_HS_5 :
    ∀ (A : Type) [Group A] [Finite A] (L : Subgroup A),
      Nonempty (↥L ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.HS).Group) →
        2 ≤ CFSG.Open.pRank 5 L := by
  intro A _ _ L hL
  obtain ⟨eL⟩ := hL
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.HS.nonempty_mulEquiv
  haveI : Finite CFSG.Blueprint.NativeSporadic.HS :=
    CFSG.Sporadic.finite_carrier_of_ne_M TauCeti.SporadicName.HS (by decide)
  obtain ⟨x, y, h, hx, hy, hne, hzx, hzy, hc, -⟩ := CFSG.SectionRank.HS_sylow5_cubic_witness
  have hN : 2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup CFSG.Blueprint.NativeSporadic.HS) :=
    two_le_pRank_of_heisenberg (by norm_num) hx hy hne hzx hzy hc
  have e : ↥L ≃* CFSG.Blueprint.NativeSporadic.HS := eL.trans b.symm
  exact @two_le_pRank_of_mulEquiv _ _ _ L CFSG.Blueprint.NativeSporadic.HS Units.instGroup _ e _
    (by norm_num) hN

theorem row_HS_5 :
    KFactSporLocalRow TauCeti.SporadicName.HS 5 :=
  row_of_rank2 TauCeti.SporadicName.HS 5 rank2_HS_5

theorem rank2_McL_5 :
    ∀ (A : Type) [Group A] [Finite A] (L : Subgroup A),
      Nonempty (↥L ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.McL).Group) →
        2 ≤ CFSG.Open.pRank 5 L := by
  intro A _ _ L hL
  obtain ⟨eL⟩ := hL
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.McL.nonempty_mulEquiv
  haveI : Finite CFSG.Blueprint.NativeSporadic.McL :=
    CFSG.Sporadic.finite_carrier_of_ne_M TauCeti.SporadicName.McL (by decide)
  obtain ⟨x, y, h, hx, hy, hne, hzx, hzy, hc, -⟩ :=
    CFSG.RankThree.PartOne.MultRes.McL_sylow5_cubic_witness
  have hN : 2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup CFSG.Blueprint.NativeSporadic.McL) :=
    two_le_pRank_of_heisenberg (by norm_num) hx hy hne hzx hzy hc
  have e : ↥L ≃* CFSG.Blueprint.NativeSporadic.McL := eL.trans b.symm
  exact @two_le_pRank_of_mulEquiv _ _ _ L CFSG.Blueprint.NativeSporadic.McL Units.instGroup _ e _
    (by norm_num) hN

theorem row_McL_5 :
    KFactSporLocalRow TauCeti.SporadicName.McL 5 :=
  row_of_rank2 TauCeti.SporadicName.McL 5 rank2_McL_5

theorem rank2_He_5 :
    ∀ (A : Type) [Group A] [Finite A] (L : Subgroup A),
      Nonempty (↥L ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.He).Group) →
        2 ≤ CFSG.Open.pRank 5 L := by
  intro A _ _ L hL
  obtain ⟨eL⟩ := hL
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.He.nonempty_mulEquiv
  haveI : Finite CFSG.Blueprint.NativeSporadic.He :=
    CFSG.Sporadic.finite_carrier_of_ne_M TauCeti.SporadicName.He (by decide)
  obtain ⟨x, y, h, hx, hy, hxy, hc, -⟩ := CFSG.SectionRank.He_sylow5_square_witness
  have hN : 2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup CFSG.Blueprint.NativeSporadic.He) :=
    two_le_pRank_of_commuting (by norm_num) hx hy hxy hc
  have e : ↥L ≃* CFSG.Blueprint.NativeSporadic.He := eL.trans b.symm
  exact @two_le_pRank_of_mulEquiv _ _ _ L CFSG.Blueprint.NativeSporadic.He Units.instGroup _ e _
    (by norm_num) hN

theorem row_He_5 :
    KFactSporLocalRow TauCeti.SporadicName.He 5 :=
  row_of_rank2 TauCeti.SporadicName.He 5 rank2_He_5

theorem rank2_He_7 :
    ∀ (A : Type) [Group A] [Finite A] (L : Subgroup A),
      Nonempty (↥L ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.He).Group) →
        2 ≤ CFSG.Open.pRank 7 L := by
  intro A _ _ L hL
  obtain ⟨eL⟩ := hL
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.He.nonempty_mulEquiv
  haveI : Finite CFSG.Blueprint.NativeSporadic.He :=
    CFSG.Sporadic.finite_carrier_of_ne_M TauCeti.SporadicName.He (by decide)
  obtain ⟨x, y, h, hx, hy, hne, hzx, hzy, hc, -⟩ := CFSG.SectionRank.He_sylow7_cubic_witness
  have hN : 2 ≤ CFSG.Open.pRank 7 (⊤ : Subgroup CFSG.Blueprint.NativeSporadic.He) :=
    two_le_pRank_of_heisenberg (by norm_num) hx hy hne hzx hzy hc
  have e : ↥L ≃* CFSG.Blueprint.NativeSporadic.He := eL.trans b.symm
  exact @two_le_pRank_of_mulEquiv _ _ _ L CFSG.Blueprint.NativeSporadic.He Units.instGroup _ e _
    (by norm_num) hN

theorem row_He_7 :
    KFactSporLocalRow TauCeti.SporadicName.He 7 :=
  row_of_rank2 TauCeti.SporadicName.He 7 rank2_He_7

theorem rank2_Ru_5 :
    ∀ (A : Type) [Group A] [Finite A] (L : Subgroup A),
      Nonempty (↥L ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.Ru).Group) →
        2 ≤ CFSG.Open.pRank 5 L := by
  intro A _ _ L hL
  obtain ⟨eL⟩ := hL
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Ru.nonempty_mulEquiv
  haveI : Finite CFSG.Blueprint.NativeSporadic.Ru :=
    CFSG.Sporadic.finite_carrier_of_ne_M TauCeti.SporadicName.Ru (by decide)
  obtain ⟨x, y, h, hx, hy, hne, hzx, hzy, hc, -⟩ := CFSG.SectionRank.Ru_sylow5_cubic_witness
  have hN : 2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup CFSG.Blueprint.NativeSporadic.Ru) :=
    two_le_pRank_of_heisenberg (by norm_num) hx hy hne hzx hzy hc
  have e : ↥L ≃* CFSG.Blueprint.NativeSporadic.Ru := eL.trans b.symm
  exact @two_le_pRank_of_mulEquiv _ _ _ L CFSG.Blueprint.NativeSporadic.Ru Units.instGroup _ e _
    (by norm_num) hN

theorem row_Ru_5 :
    KFactSporLocalRow TauCeti.SporadicName.Ru 5 :=
  row_of_rank2 TauCeti.SporadicName.Ru 5 rank2_Ru_5

theorem rank2_Suz_5 :
    ∀ (A : Type) [Group A] [Finite A] (L : Subgroup A),
      Nonempty (↥L ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.Suz).Group) →
        2 ≤ CFSG.Open.pRank 5 L := by
  intro A _ _ L hL
  obtain ⟨eL⟩ := hL
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Suz.nonempty_mulEquiv
  haveI : Finite CFSG.Blueprint.NativeSporadic.Suz :=
    CFSG.Sporadic.finite_carrier_of_ne_M TauCeti.SporadicName.Suz (by decide)
  obtain ⟨x, y, h, hx, hy, hxy, hc, -⟩ :=
    CFSG.RankThree.PartOne.MultRes.Suz_sylow5_square_witness
  have hN : 2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup CFSG.Blueprint.NativeSporadic.Suz) :=
    two_le_pRank_of_commuting (by norm_num) hx hy hxy hc
  have e : ↥L ≃* CFSG.Blueprint.NativeSporadic.Suz := eL.trans b.symm
  exact @two_le_pRank_of_mulEquiv _ _ _ L CFSG.Blueprint.NativeSporadic.Suz Units.instGroup _ e _
    (by norm_num) hN

theorem row_Suz_5 :
    KFactSporLocalRow TauCeti.SporadicName.Suz 5 :=
  row_of_rank2 TauCeti.SporadicName.Suz 5 rank2_Suz_5

theorem rank2_ONan_7 :
    ∀ (A : Type) [Group A] [Finite A] (L : Subgroup A),
      Nonempty (↥L ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.ONan).Group) →
        2 ≤ CFSG.Open.pRank 7 L := by
  intro A _ _ L hL
  obtain ⟨eL⟩ := hL
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
  haveI : Finite CFSG.Blueprint.NativeSporadic.ON :=
    CFSG.Sporadic.finite_carrier_of_ne_M TauCeti.SporadicName.ONan (by decide)
  obtain ⟨x, y, h, hx, hy, hne, hzx, hzy, hc, -⟩ :=
    CFSG.RankThree.PartOne.MultRes.ON_sylow7_cubic_witness
  have hN : 2 ≤ CFSG.Open.pRank 7 (⊤ : Subgroup CFSG.Blueprint.NativeSporadic.ON) :=
    two_le_pRank_of_heisenberg (by norm_num) hx hy hne hzx hzy hc
  have e : ↥L ≃* CFSG.Blueprint.NativeSporadic.ON := eL.trans b.symm
  exact @two_le_pRank_of_mulEquiv _ _ _ L CFSG.Blueprint.NativeSporadic.ON Units.instGroup _ e _
    (by norm_num) hN

theorem row_ONan_7 :
    KFactSporLocalRow TauCeti.SporadicName.ONan 7 :=
  row_of_rank2 TauCeti.SporadicName.ONan 7 rank2_ONan_7

theorem rank2_Co2_5 :
    ∀ (A : Type) [Group A] [Finite A] (L : Subgroup A),
      Nonempty (↥L ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.Co2).Group) →
        2 ≤ CFSG.Open.pRank 5 L := by
  intro A _ _ L hL
  obtain ⟨eL⟩ := hL
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Co2.nonempty_mulEquiv
  haveI : Finite CFSG.Blueprint.NativeSporadic.Co2 :=
    CFSG.Sporadic.finite_carrier_of_ne_M TauCeti.SporadicName.Co2 (by decide)
  obtain ⟨x, y, h, hx, hy, hne, hzx, hzy, hc, -⟩ :=
    CFSG.RankThree.PartOne.MultRes.Co2_sylow5_cubic_witness
  have hN : 2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup CFSG.Blueprint.NativeSporadic.Co2) :=
    two_le_pRank_of_heisenberg (by norm_num) hx hy hne hzx hzy hc
  have e : ↥L ≃* CFSG.Blueprint.NativeSporadic.Co2 := eL.trans b.symm
  exact @two_le_pRank_of_mulEquiv _ _ _ L CFSG.Blueprint.NativeSporadic.Co2 Units.instGroup _ e _
    (by norm_num) hN

theorem row_Co2_5 :
    KFactSporLocalRow TauCeti.SporadicName.Co2 5 :=
  row_of_rank2 TauCeti.SporadicName.Co2 5 rank2_Co2_5

theorem rank2_Co3_5 :
    ∀ (A : Type) [Group A] [Finite A] (L : Subgroup A),
      Nonempty (↥L ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.Co3).Group) →
        2 ≤ CFSG.Open.pRank 5 L := by
  intro A _ _ L hL
  obtain ⟨eL⟩ := hL
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Co3.nonempty_mulEquiv
  haveI : Finite CFSG.Blueprint.NativeSporadic.Co3 :=
    CFSG.Sporadic.finite_carrier_of_ne_M TauCeti.SporadicName.Co3 (by decide)
  obtain ⟨x, y, h, hx, hy, hne, hzx, hzy, hc, -⟩ :=
    CFSG.RankThree.PartOne.MultRes.Co3_sylow5_cubic_witness
  have hN : 2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup CFSG.Blueprint.NativeSporadic.Co3) :=
    two_le_pRank_of_heisenberg (by norm_num) hx hy hne hzx hzy hc
  have e : ↥L ≃* CFSG.Blueprint.NativeSporadic.Co3 := eL.trans b.symm
  exact @two_le_pRank_of_mulEquiv _ _ _ L CFSG.Blueprint.NativeSporadic.Co3 Units.instGroup _ e _
    (by norm_num) hN

theorem row_Co3_5 :
    KFactSporLocalRow TauCeti.SporadicName.Co3 5 :=
  row_of_rank2 TauCeti.SporadicName.Co3 5 rank2_Co3_5

theorem rank2_J4_11 :
    ∀ (A : Type) [Group A] [Finite A] (L : Subgroup A),
      Nonempty (↥L ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.J4).Group) →
        2 ≤ CFSG.Open.pRank 11 L := by
  intro A _ _ L hL
  obtain ⟨eL⟩ := hL
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J4.nonempty_mulEquiv
  haveI : Finite CFSG.Blueprint.NativeSporadic.J4 :=
    CFSG.Sporadic.finite_carrier_of_ne_M TauCeti.SporadicName.J4 (by decide)
  obtain ⟨x, y, h, hx, hy, hne, hzx, hzy, hc, -⟩ := CFSG.SectionRank.J4_sylow11_cubic_witness
  have hN : 2 ≤ CFSG.Open.pRank 11 (⊤ : Subgroup CFSG.Blueprint.NativeSporadic.J4) :=
    two_le_pRank_of_heisenberg (by norm_num) hx hy hne hzx hzy hc
  have e : ↥L ≃* CFSG.Blueprint.NativeSporadic.J4 := eL.trans b.symm
  exact @two_le_pRank_of_mulEquiv _ _ _ L CFSG.Blueprint.NativeSporadic.J4 Units.instGroup _ e _
    (by norm_num) hN

theorem row_J4_11 :
    KFactSporLocalRow TauCeti.SporadicName.J4 11 :=
  row_of_rank2 TauCeti.SporadicName.J4 11 rank2_J4_11

theorem rank2_Ly_5 :
    ∀ (A : Type) [Group A] [Finite A] (L : Subgroup A),
      Nonempty (↥L ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.Ly).Group) →
        2 ≤ CFSG.Open.pRank 5 L := by
  intro A _ _ L hL
  obtain ⟨eL⟩ := hL
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Ly.nonempty_mulEquiv
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier TauCeti.SporadicName.Ly) :=
    CFSG.Sporadic.finite_carrier_of_ne_M TauCeti.SporadicName.Ly (by decide)
  have hN : 3 ≤ CFSG.Open.pRank 5
      (⊤ : Subgroup (CFSG.Blueprint.NativeSporadic.Carrier TauCeti.SporadicName.Ly)) :=
    CFSG.AGLEmbeddingD2.three_le_pRank_Ly_five
  have b' : CFSG.Blueprint.NativeSporadic.Carrier TauCeti.SporadicName.Ly ≃*
      TauCeti.SporadicName.Ly.Group := b
  exact two_le_pRank_of_mulEquiv L (eL.trans b'.symm) (by norm_num)
    ((show 2 ≤ 3 by norm_num).trans hN)

theorem row_Ly_5 :
    KFactSporLocalRow TauCeti.SporadicName.Ly 5 :=
  row_of_rank2 TauCeti.SporadicName.Ly 5 rank2_Ly_5

theorem rank2_HN_5 :
    ∀ (A : Type) [Group A] [Finite A] (L : Subgroup A),
      Nonempty (↥L ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.HN).Group) →
        2 ≤ CFSG.Open.pRank 5 L := by
  intro A _ _ L hL
  obtain ⟨eL⟩ := hL
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.HN.nonempty_mulEquiv
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier TauCeti.SporadicName.HN) :=
    CFSG.Sporadic.finite_carrier_of_ne_M TauCeti.SporadicName.HN (by decide)
  have hN : 3 ≤ CFSG.Open.pRank 5
      (⊤ : Subgroup (CFSG.Blueprint.NativeSporadic.Carrier TauCeti.SporadicName.HN)) :=
    CFSG.AGLEmbeddingD2.three_le_pRank_HN_five
  have b' : CFSG.Blueprint.NativeSporadic.Carrier TauCeti.SporadicName.HN ≃*
      TauCeti.SporadicName.HN.Group := b
  exact two_le_pRank_of_mulEquiv L (eL.trans b'.symm) (by norm_num)
    ((show 2 ≤ 3 by norm_num).trans hN)

theorem row_HN_5 :
    KFactSporLocalRow TauCeti.SporadicName.HN 5 :=
  row_of_rank2 TauCeti.SporadicName.HN 5 rank2_HN_5

theorem rank2_Th_5 :
    ∀ (A : Type) [Group A] [Finite A] (L : Subgroup A),
      Nonempty (↥L ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.Th).Group) →
        2 ≤ CFSG.Open.pRank 5 L := by
  intro A _ _ L hL
  obtain ⟨eL⟩ := hL
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Th.nonempty_mulEquiv
  haveI : Finite CFSG.Blueprint.NativeSporadic.Th :=
    CFSG.Sporadic.finite_carrier_of_ne_M TauCeti.SporadicName.Th (by decide)
  obtain ⟨x, y, h, hx, hy, hne, hzx, hzy, hc, -⟩ :=
    CFSG.RankThree.PartOne.MultRes.Th_sylow5_cubic_witness
  have hN : 2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup CFSG.Blueprint.NativeSporadic.Th) :=
    two_le_pRank_of_heisenberg (by norm_num) hx hy hne hzx hzy hc
  have e : ↥L ≃* CFSG.Blueprint.NativeSporadic.Th := eL.trans b.symm
  exact @two_le_pRank_of_mulEquiv _ _ _ L CFSG.Blueprint.NativeSporadic.Th Units.instGroup _ e _
    (by norm_num) hN

theorem row_Th_5 :
    KFactSporLocalRow TauCeti.SporadicName.Th 5 :=
  row_of_rank2 TauCeti.SporadicName.Th 5 rank2_Th_5

theorem rank2_Th_7 :
    ∀ (A : Type) [Group A] [Finite A] (L : Subgroup A),
      Nonempty (↥L ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.Th).Group) →
        2 ≤ CFSG.Open.pRank 7 L := by
  intro A _ _ L hL
  obtain ⟨eL⟩ := hL
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Th.nonempty_mulEquiv
  haveI : Finite CFSG.Blueprint.NativeSporadic.Th :=
    CFSG.Sporadic.finite_carrier_of_ne_M TauCeti.SporadicName.Th (by decide)
  obtain ⟨x, y, h, hx, hy, hxy, hc, -⟩ :=
    CFSG.RankThree.PartOne.MultRes.Th_sylow7_square_witness
  have hN : 2 ≤ CFSG.Open.pRank 7 (⊤ : Subgroup CFSG.Blueprint.NativeSporadic.Th) :=
    two_le_pRank_of_commuting (by norm_num) hx hy hxy hc
  have e : ↥L ≃* CFSG.Blueprint.NativeSporadic.Th := eL.trans b.symm
  exact @two_le_pRank_of_mulEquiv _ _ _ L CFSG.Blueprint.NativeSporadic.Th Units.instGroup _ e _
    (by norm_num) hN

theorem row_Th_7 :
    KFactSporLocalRow TauCeti.SporadicName.Th 7 :=
  row_of_rank2 TauCeti.SporadicName.Th 7 rank2_Th_7

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
