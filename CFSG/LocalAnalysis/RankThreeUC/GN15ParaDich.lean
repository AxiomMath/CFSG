module

public import CFSG.LocalAnalysis.RankThreeUC.GN15ParaLift
public import CFSG.Quasithin.Background.C118WeakPair
import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenSolvC126
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.PermutableOrderThree
import CFSG.Quasithin.SteinbergBTResidualAbelianIndexTwo

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.GN
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

section NoTwoQuotient

variable {Y : Type} [Group Y] [Finite Y]

private theorem map_mem_zpowers_of_noTwoQuotient {Rs : Subgroup Y} (hRs : IsPGroup 2 Rs) {c : Y}
    (hnorm : Rs ≤ Subgroup.normalizer (Subgroup.zpowers c : Set Y))
    {L : Type} [Group L] (hL : ∀ (N : Subgroup L) [N.Normal], IsPGroup 2 (L ⧸ N) → N = ⊤)
    (f : L →* Y) (hf : ∀ x, f x ∈ Rs ⊔ Subgroup.zpowers c) (x : L) :
    f x ∈ Subgroup.zpowers c := by
  have hZn := normal_zpowers_subgroupOf_sup_of_le_normalizer hnorm
  set Hs : Subgroup Y := Rs ⊔ Subgroup.zpowers c with hHs
  let φ : L →* ↥Hs ⧸ (Subgroup.zpowers c).subgroupOf Hs :=
    (QuotientGroup.mk' _).comp (f.codRestrict Hs hf)
  have htop : φ.ker = ⊤ :=
    CFSG.Quasithin.SteinbergBT.ker_eq_top_of_isPGroup_two_range hL φ
      ((isPGroup_quotient_sup_zpowers hRs hnorm).to_subgroup _)
  have hx : φ x = 1 := MonoidHom.mem_ker.mp (htop ▸ Subgroup.mem_top x)
  have := (QuotientGroup.eq_one_iff _).1 hx
  simpa [Subgroup.mem_subgroupOf] using this

end NoTwoQuotient

section Dichotomy

variable {X : Type} [Group X] [Finite X] {T : Subgroup X}

theorem threeElement_dichotomy_of_weak (hX : GNSetting X T) {R D T₂ : Subgroup X}
    (hW : IsC118WeakPair R D T₂) (hRT : R ≤ T)
    (hCR : T ⊓ gnC T ≤ R) (hQR : pCoreOf 2 (⊤ : Subgroup X) ≤ R)
    {c : X ⧸ gnC T} (hc3 : orderOf c = 3)
    (hnorm : gnImg T R ≤ Subgroup.normalizer (Subgroup.zpowers c : Set (X ⧸ gnC T)))
    (hnot : ¬ Subgroup.zpowers c ≤ Subgroup.normalizer (gnImg T R : Set (X ⧸ gnC T))) :
    c ∈ gnImg T (Subgroup.centralizer (D : Set X)) ∨
      c ∈ gnImg T (Subgroup.normalizer (T₂ : Set X)) ∨
      ∃ H Kb : Subgroup X, pCoreOf 2 (⊤ : Subgroup X) ≤ H ∧ IsBlock2 H Kb ∧ IsAltType Kb 3 ∧
        ¬ Kb ≤ gnC T ∧ gnImg T Kb = Subgroup.zpowers c := by
  set π := QuotientGroup.mk' (gnC T) with hπ
  obtain ⟨K, M, hmin, hF, hRK, hsolv, himg⟩ :=
    exists_solvable_minParabolic_lift hX hRT hCR hQR hc3 hnorm hnot
  have hperf : perfectCore K ≤ Subgroup.centralizer (VZ R K : Set X) := by
    rw [(isSolvable_iff_perfectCore_eq_bot K).1 hsolv]
    exact bot_le
  have hc : c ∈ K.map π := by
    rw [himg]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers c)
  obtain ⟨k, hkK, hkc⟩ := Subgroup.mem_map.mp hc
  rcases concl1Gen_of_perfectCore_le_weak hW hmin hF hperf with
    h1 | h2 | ⟨K', hK'blk, hK'J, hK'gen⟩
  · left
    refine ⟨k, ?_, hkc⟩
    refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
    exact (Subgroup.mem_centralizer_iff.mp (h1 hz).2 k hkK).symm
  · right; left
    exact ⟨k, h2 hkK, hkc⟩
  · right; right
    have hblk : IsBlock2 K K' := hK'blk.1
    have hA3 : IsAltType K' 3 := C1Pack.isAltType_three_of_isBlock2_of_solvable hblk hsolv
    have hRp : IsPGroup 2 R := hX.sylow.2.1.to_le hRT
    have hRsp : IsPGroup 2 (gnImg T R) := hRp.map π
    have hKK : K' ≤ K := hblk.2.1
    have himgle : ∀ x : ↥K', π (x : X) ∈ Subgroup.zpowers c := fun x =>
      map_mem_zpowers_of_noTwoQuotient hRsp hnorm (fun N _ hp => hblk.1.1 N hp)
        (π.comp K'.subtype) (fun y => by
          rw [← himg]; exact ⟨(y : X), hKK y.2, rfl⟩) x
    have hnotC : ¬ K' ≤ gnC T := by
      intro hK'C
      have hcc : conjClosure K' R ≤ gnC T :=
        conjClosure_le fun h _ z hz => (gnC_normal T).conj_mem z (hK'C hz) h
      have hKle : K ≤ R ⊔ gnC T := by
        rw [hK'gen]; exact sup_le le_sup_left (hcc.trans le_sup_right)
      obtain ⟨r, hr, w, hw, hrw⟩ := Subgroup.mem_sup_of_normal_right.mp (hKle hkK)
      have hcR : c ∈ gnImg T R := by
        rw [← hkc, ← hrw, map_mul, show π w = 1 from (QuotientGroup.eq_one_iff w).2 hw, mul_one]
        exact ⟨r, hr, rfl⟩
      have h1' : c ∈ gnImg T R ⊓ Subgroup.zpowers c := ⟨hcR, Subgroup.mem_zpowers c⟩
      rw [CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.inf_eq_bot_of_isPGroup_two_of_card_three hRsp
        ((Nat.card_zpowers c).trans hc3), Subgroup.mem_bot] at h1'
      rw [h1', orderOf_one] at hc3
      omega
    refine ⟨K, K', hQR.trans hRK, hblk, hA3, hnotC, ?_⟩
    obtain ⟨x, hxK', hxC⟩ : ∃ x ∈ K', x ∉ gnC T := by
      by_contra hcon
      exact hnotC fun y hy => by_contra fun hy' => hcon ⟨y, hy, hy'⟩
    have hy : π x ∈ Subgroup.zpowers c := himgle ⟨x, hxK'⟩
    have hy1 : π x ≠ 1 := fun h => hxC ((QuotientGroup.eq_one_iff x).1 h)
    have hord : orderOf (π x) = 3 := by
      have hd : orderOf (π x) ∣ 3 := hc3 ▸ orderOf_dvd_of_mem_zpowers hy
      rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h
      · exact absurd (orderOf_eq_one_iff.1 h) hy1
      · exact h
    have hzz : Subgroup.zpowers (π x) = Subgroup.zpowers c := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hy) ?_
      rw [Nat.card_zpowers, Nat.card_zpowers, hord, hc3]
    apply le_antisymm
    · rintro _ ⟨y, hy', rfl⟩
      exact himgle ⟨y, hy'⟩
    · rw [← hzz, Subgroup.zpowers_le]
      exact ⟨x, hxK', rfl⟩

theorem threeElement_dichotomy {T₁ T₂ : Subgroup X} (hX : GNSetting X T)
    (hP : IsC118Pair T T₁ T₂) {R : Subgroup X}
    (hBR : baum T ≤ R) (hRT : R ≤ T) (hQR : pCoreOf 2 (⊤ : Subgroup X) ≤ R)
    (hCR : T ⊓ gnC T ≤ R) {c : X ⧸ gnC T} (hc3 : orderOf c = 3)
    (hnorm : gnImg T R ≤ Subgroup.normalizer (Subgroup.zpowers c : Set (X ⧸ gnC T)))
    (hnot : ¬ Subgroup.zpowers c ≤ Subgroup.normalizer (gnImg T R : Set (X ⧸ gnC T))) :
    c ∈ gnImg T (Subgroup.centralizer (T₁ : Set X)) ∨
      c ∈ gnImg T (Subgroup.normalizer (T₂ : Set X)) ∨
      ∃ H Kb : Subgroup X, pCoreOf 2 (⊤ : Subgroup X) ≤ H ∧ IsBlock2 H Kb ∧ IsAltType Kb 3 ∧
        ¬ Kb ≤ gnC T ∧ gnImg T Kb = Subgroup.zpowers c :=
  threeElement_dichotomy_of_weak hX (hP.toWeakOfLe hBR hRT) hRT hCR hQR hc3 hnorm hnot

end Dichotomy

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15
