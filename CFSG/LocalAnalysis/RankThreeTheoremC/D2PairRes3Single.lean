module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairStrong3Irr
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairRes3Cent
import CFSG.LocalAnalysis.AGLEmbedding.LemmaBGlue
public import CFSG.LocalAnalysis.AGLEmbeddingD2.HSFiveCaseTwoTools

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {M H R : Subgroup G}

theorem _root_.CFSG.AGLEmbeddingD2.AGLPair.barM_inf_barM_le (h : AGLPair 3 M H R) {L : Subgroup G} :
    barM M L ⊓ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G)) ≤
      barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L) := by
  rintro b ⟨hbL, hbB⟩
  obtain ⟨a, haL, rfl⟩ := mem_barM_iff.mp hbL
  obtain ⟨a', ha'N, ha'b⟩ := mem_barM_iff.mp hbB
  have hq : QuotientGroup.mk' (CFSG.pCore 2 ↥M) (a'⁻¹ * a) = 1 := by
    rw [map_mul, map_inv, ha'b, inv_mul_cancel]
  have hqS : ((a'⁻¹ * a : ↥M) : G) ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    Subgroup.le_normalizer (h.twoCore_M_le (coe_mem_pCoreOf_two_of_mk_eq_one _ hq))
  have haN : (a : G) ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) := by
    have : (a : G) = (a' : G) * ((a'⁻¹ * a : ↥M) : G) := by simp
    rw [this]
    exact (Subgroup.normalizer (pCoreOf 2 H : Set G)).mul_mem ha'N hqS
  exact mem_barM_iff.mpr ⟨a, ⟨haN, haL⟩, rfl⟩

theorem _root_.CFSG.AGLEmbeddingD2.AGLPair.commutative_barM_of_le_sup
    (h : AGLPair 3 M H R) (h84 : Asc81bEightFour) (h86 : Asc81bEightSix) (hD2 : NoXBlockFor G)
    (hH : Open.pRank 3 H = 2)
    (hthree : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      BlockHasThree M (pCoreOf 2 H) L)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hk1 : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' → barM M L' = barM M L)
    (hRL : barM M R ≤ barM M L ⊔
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hy : ∃ y ∈ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L), y ^ 3 = 1 ∧
      y ∉ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hP : ∀ T : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
      T ≤ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L) → IsPGroup 3 T →
        IsElemAbelian 3 T) :
    ∀ x ∈ barM M R, ∀ x' ∈ barM M R, x * x' = x' * x := by
  have h3 : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨h3⟩
  set S := pCoreOf 2 H with hS
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set Lb := barM M L with hLb
  set Cb := Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) with hCb
  set Rb := barM M R with hRb
  set Bb := barM M (Subgroup.normalizer (S : Set G)) with hBb
  set Pb := barM M (Subgroup.normalizer (S : Set G) ⊓ L) with hPb
  obtain ⟨y, hyP, hy3, hyC⟩ := hy
  have hBH : Open.pRank 3 Bb ≤ 2 := (h.pRank_barM_normalizer_le h3 (by decide)).trans hH.le
  have hCB : Cb ≤ Bb := fun c hc =>
    h.mem_barM_normalizer_of_centralizes_weakSBlocks h84 h86 hD2 fun L' hL' =>
      (hk1 L' hL').symm ▸ hc
  have hRB : Rb ≤ Bb := barM_mono fun r hr => by
    rw [h.normalizer_twoCore_H]
    exact h.le_H hr
  have hRp : IsPGroup 3 Rb := isPGroup_barM h.isPGroup_R
  have hR3 : ∀ x ∈ Rb, IsPGroup 3 (Subgroup.zpowers x) := fun x hx =>
    hRp.to_le (Subgroup.zpowers_le.mpr hx)
  have hRN : Rb ≤ Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := fun x hx =>
    h.mem_normalizer_weakSBlock_of_isPGroup hH hthree hL (hR3 x hx)
  have hLC : ∀ l ∈ Lb, ∀ c ∈ Cb, l * c = c * l := fun l hl c hc =>
    (Subgroup.mem_centralizer_iff.mp hc l hl)
  have hNC := normalizer_le_normalizer_centralizer_res3 Lb
  have hRCn : Rb ≤ Subgroup.normalizer (Cb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := fun r hr =>
    hNC (hRN hr)
  have hLCn : Lb ≤ Subgroup.normalizer (Cb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := fun l hl =>
    hNC (Subgroup.le_normalizer hl)
  have hPeq : Lb ⊓ Bb ≤ Pb := h.barM_inf_barM_le
  set D := Lb ⊓ (Rb ⊔ Cb) with hD
  have hDP : D ≤ Pb := fun d hd => hPeq ⟨hd.1, (sup_le hRB hCB) hd.2⟩
  have hDcomm : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := by
    refine commutative_of_central_by_three (N₀ := D ⊓ Cb) inf_le_left ?_ ?_ ?_
    · intro n hn d hd
      exact (hLC d hd.1 n hn.2).symm
    · intro d hd
      have hd' : d ∈ ((Rb ⊔ Cb : Subgroup _) : Set _) := hd.2
      rw [Subgroup.coe_mul_of_left_le_normalizer_right Rb Cb hRCn] at hd'
      obtain ⟨r, hr, c, hc, rfl⟩ := hd'
      obtain ⟨k, hk⟩ := hRp ⟨r, hr⟩
      have hk' : r ^ 3 ^ k = 1 := congrArg Subtype.val hk
      obtain ⟨c', hc', hpow⟩ := pow_mem_mul_of_mem_normalizer (hRCn hr) hc (3 ^ k)
      exact ⟨k, D.pow_mem hd _, by rw [hpow, hk', one_mul]; exact hc'⟩
    · intro T hTD hT3 a ha b hb
      exact congrArg Subtype.val
        ((hP T (hTD.trans hDP) hT3).1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  set E := Cb ⊓ (Lb ⊔ Rb) with hE
  have hyL : y ∈ Lb := barM_mono inf_le_right hyP
  have hyB : y ∈ Bb := barM_mono inf_le_left hyP
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    refine commutative_of_central_by_three (N₀ := E ⊓ Lb) inf_le_left ?_ ?_ ?_
    · intro n hn e he
      exact hLC n hn.2 e he.1
    · intro e he
      have he' : e ∈ ((Rb ⊔ Lb : Subgroup _) : Set _) := by
        rw [sup_comm]
        exact he.2
      rw [Subgroup.coe_mul_of_left_le_normalizer_right Rb Lb hRN] at he'
      obtain ⟨r, hr, l, hl, rfl⟩ := he'
      obtain ⟨k, hk⟩ := hRp ⟨r, hr⟩
      have hk' : r ^ 3 ^ k = 1 := congrArg Subtype.val hk
      obtain ⟨l', hl', hpow⟩ := pow_mem_mul_of_mem_normalizer (hRN hr) hl (3 ^ k)
      exact ⟨k, E.pow_mem he _, by rw [hpow, hk', one_mul]; exact hl'⟩
    · intro T hTE hT3
      have hTC : T ≤ Cb := hTE.trans inf_le_left
      have hTB : T ≤ Bb := hTC.trans hCB
      have hyT : y ∈ Subgroup.centralizer (T : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
        rw [Subgroup.mem_centralizer_iff]
        intro t ht
        exact (Subgroup.mem_centralizer_iff.mp (hTC ht) y hyL).symm
      have hsucc := succ_pRank_le_of_commute (q := 3) hTB hTC hyB hy3 hyC hyT
      exact commutative_of_isPGroup_of_pRank_le_one hT3 (by omega)
  have decomp : ∀ r ∈ Rb, ∃ l ∈ D, ∃ c ∈ E, r = l * c := by
    intro r hr
    have hr' : r ∈ ((Lb ⊔ Cb : Subgroup _) : Set _) := hRL hr
    rw [Subgroup.coe_mul_of_left_le_normalizer_right Lb Cb hLCn] at hr'
    obtain ⟨l, hl, c, hc, rfl⟩ := hr'
    refine ⟨l, ⟨hl, ?_⟩, c, ⟨hc, ?_⟩, rfl⟩
    · have : l = (l * c) * c⁻¹ := by group
      rw [this]
      exact (Rb ⊔ Cb).mul_mem (Subgroup.mem_sup_left hr)
        ((Rb ⊔ Cb).inv_mem (Subgroup.mem_sup_right hc))
    · have : c = l⁻¹ * (l * c) := by group
      rw [this]
      exact (Lb ⊔ Rb).mul_mem ((Lb ⊔ Rb).inv_mem (Subgroup.mem_sup_left hl))
        (Subgroup.mem_sup_right hr)
  intro x hx x' hx'
  obtain ⟨l, hl, c, hc, rfl⟩ := decomp x hx
  obtain ⟨l', hl', c', hc', rfl⟩ := decomp x' hx'
  have h1 : l * l' = l' * l := hDcomm l hl l' hl'
  have h2 : c * c' = c' * c := hEcomm c hc c' hc'
  have h3' : c * l' = l' * c := (hLC l' hl'.1 c hc.1).symm
  have h4 : c' * l = l * c' := (hLC l hl.1 c' hc'.1).symm
  calc l * c * (l' * c') = l * (c * l') * c' := by group
    _ = l * (l' * c) * c' := by rw [h3']
    _ = (l * l') * (c * c') := by group
    _ = (l' * l) * (c' * c) := by rw [h1, h2]
    _ = l' * (l * c') * c := by group
    _ = l' * (c' * l) * c := by rw [← h4]
    _ = l' * c' * (l * c) := by group

theorem _root_.CFSG.AGLEmbeddingD2.AGLPair.commutative_barM_of_one_weakSBlock
    (h : AGLPair 3 M H R) (h84 : Asc81bEightFour) (h86 : Asc81bEightSix) (hD2 : NoXBlockFor G)
    (hH : Open.pRank 3 H = 2)
    (hthree : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      BlockHasThree M (pCoreOf 2 H) L)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hk1 : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' → barM M L' = barM M L)
    (ho : ∀ u ∈ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)),
      IsPGroup 3 (Subgroup.zpowers u) →
        u ∈ barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hy : ∃ y ∈ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L), y ^ 3 = 1 ∧
      y ∉ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hP : ∀ T : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
      T ≤ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L) → IsPGroup 3 T →
        IsElemAbelian 3 T) :
    ∀ x ∈ barM M R, ∀ x' ∈ barM M R, x * x' = x' * x := by
  have hRp : IsPGroup 3 (barM M R) := isPGroup_barM h.isPGroup_R
  exact h.commutative_barM_of_le_sup h84 h86 hD2 hH hthree hL hk1
    (fun x hx => ho x (h.mem_normalizer_weakSBlock_of_isPGroup hH hthree hL
      (hRp.to_le (Subgroup.zpowers_le.mpr hx))) (hRp.to_le (Subgroup.zpowers_le.mpr hx))) hy hP

end CFSG.LocalAnalysis.RankThreeTheoremC
