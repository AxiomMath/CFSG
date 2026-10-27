module

public import CFSG.LocalAnalysis.AGLEmbedding.NongenerationTransfer
public import CFSG.RankThree.PartTwo.Sec4.T444.Coprime
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64FreePrimeCore

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64Asm

open CFSG.Open CFSG.GH74.Uniqueness.SU CFSG.LocalAnalysis.GLTheoremB Subgroup

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem isElemAbelian_of_injOn {A B : Type*} [Group A] [Group B] {φ : A →* B}
    {P E : Subgroup A} (h : Set.InjOn φ P) (hEP : E ≤ P) (hE : IsElemAbelian p (E.map φ)) :
    IsElemAbelian p E := by
  rw [SU1.isElemAbelian_iff] at hE ⊢
  obtain ⟨hc, hp⟩ := hE
  refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
  · apply h (P.mul_mem (hEP ha) (hEP hb)) (P.mul_mem (hEP hb) (hEP ha))
    rw [map_mul, map_mul]
    exact hc _ (mem_map_of_mem φ ha) _ (mem_map_of_mem φ hb)
  · apply h (P.pow_mem (hEP ha) p) P.one_mem
    rw [map_pow, map_one]
    exact hp _ (mem_map_of_mem φ ha)

theorem injOn_mk_of_isPGroup (hp : p.Prime) (O : Subgroup G) [O.Normal]
    (hO : Nat.Coprime p (Nat.card O)) {T : Subgroup G} (hT : IsPGroup p T) :
    Set.InjOn (QuotientGroup.mk' O) T := by
  intro x hx y hy hxy
  have hker : x * y⁻¹ ∈ O := by
    rw [← QuotientGroup.eq_one_iff]
    change QuotientGroup.mk' O (x * y⁻¹) = 1
    rw [map_mul, map_inv, hxy, mul_inv_cancel]
  have hm : x * y⁻¹ ∈ T ⊓ O := ⟨T.mul_mem hx (T.inv_mem hy), hker⟩
  rw [CFSG.AGLEmbedding.inf_eq_bot_of_isPGroup hp hT hO, mem_bot, mul_inv_eq_one] at hm
  exact hm

theorem normalizer_le_map_of_gamma (hp : p.Prime) (O : Subgroup G) [O.Normal]
    (hO : Nat.Coprime p (Nat.card O)) {R Y' : Subgroup G} (hR : IsPGroup p R) {k : ℕ}
    (hN : ∀ S : Subgroup G, S ≤ R → k ≤ Open.pRank p S → normalizer (S : Set G) ≤ Y')
    {Sb : Subgroup (G ⧸ O)} (hSb : Sb ≤ R.map (QuotientGroup.mk' O)) (hk : k ≤ Open.pRank p Sb) :
    normalizer (Sb : Set (G ⧸ O)) ≤ Y'.map (QuotientGroup.mk' O) := by
  set π := QuotientGroup.mk' O with hπ
  set S : Subgroup G := Sb.comap π ⊓ R with hS
  have hSR : S ≤ R := inf_le_right
  have hSmap : S.map π = Sb := CFSG.AGLEmbedding.map_comap_inf_eq π hSb
  have hSp : IsPGroup p S := hR.to_le hSR
  have hrk : k ≤ Open.pRank p S := by
    have h1 := CFSG.RankThree.PartTwo.Sec4.pRank_map_le_of_not_dvd hp π
      (by rw [QuotientGroup.ker_mk']; exact (Nat.Prime.coprime_iff_not_dvd hp).mp hO) S
    rw [hSmap] at h1
    exact hk.trans h1
  have hNS := hN S hSR hrk
  intro g hg
  rw [← hSmap] at hg
  obtain ⟨g₀, rfl⟩ := QuotientGroup.mk'_surjective O g
  have hmem : g₀ ∈ O ⊔ normalizer (S : Set G) :=
    CFSG.AGLEmbedding.comap_normalizer_map_le_sup hp O hO hSp hg
  obtain ⟨o, ho, n, hn, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hmem
  refine ⟨n, hNS hn, ?_⟩
  have h1 : π o = 1 := (QuotientGroup.eq_one_iff o).mpr ho
  change π n = π (o * n)
  rw [map_mul, h1, one_mul]

theorem mem_map_of_mem_centralizer (hp : p.Prime) (O : Subgroup G) [O.Normal]
    (hO : Nat.Coprime p (Nat.card O)) {B : Subgroup G} (hBel : IsElemAbelian p B)
    (hsc : ∀ y ∈ centralizer (B : Set G), y ^ p = 1 → y ∈ B) :
    ∀ y ∈ centralizer ((B.map (QuotientGroup.mk' O) : Subgroup (G ⧸ O)) : Set (G ⧸ O)),
      y ^ p = 1 → y ∈ B.map (QuotientGroup.mk' O) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hSC : IsSCp p ⊤ B := by
    refine ⟨le_top, hBel, fun E _ hE hBE => ?_⟩
    refine le_antisymm (fun y hy => ?_) hBE
    have hcomm := (SU1.isElemAbelian_iff.mp hE).1
    have hyc : y ∈ centralizer (B : Set G) := by
      rw [mem_centralizer_iff]
      intro b hb
      exact hcomm b (hBE hb) y hy
    exact hsc y hyc ((SU1.isElemAbelian_iff.mp hE).2 y hy)
  have hN : ¬ p ∣ Nat.card O := (Nat.Prime.coprime_iff_not_dvd hp).mp hO
  have hSCb := isSCp_map_quotient O hN hSC
  intro y hy hyp
  by_contra hyB
  set Bb := B.map (QuotientGroup.mk' O) with hBb
  have hcomm : ∀ a ∈ Bb, ∀ b ∈ zpowers y, a * b = b * a := by
    rintro a ha b ⟨n, rfl⟩
    exact (Commute.zpow_right (show Commute a y from (mem_centralizer_iff.mp hy) a ha) n).eq
  have hel : IsElemAbelian p (Bb ⊔ zpowers y) :=
    SU1.IsElemAbelian.sup hSCb.2.1 (SU1.isElemAbelian_zpowers hyp) hcomm
  have h := hSCb.2.2 (Bb ⊔ zpowers y) le_top hel le_sup_left
  apply hyB
  rw [← h]
  exact Subgroup.mem_sup_right (mem_zpowers y)

section Normalizer

variable {A : Type} [Group A] [Finite A]

theorem normalizer_subgroupOf_le {X Y : Subgroup A} (S : Subgroup ↥X)
    (h : normalizer ((S.map X.subtype : Subgroup A) : Set A) ⊓ X ≤ Y) :
    normalizer (S : Set ↥X) ≤ Y.subgroupOf X := by
  intro y hy
  have hSX : S.map X.subtype ≤ X := Subgroup.map_subtype_le S
  have e : (S.map X.subtype).subgroupOf X = S :=
    Subgroup.comap_map_eq_self_of_injective X.subtype_injective S
  rw [← e] at hy
  exact h ⟨P64Free.mem_normalizer_of_mem_normalizer_subgroupOf hSX hy, y.2⟩

end Normalizer

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64Asm
