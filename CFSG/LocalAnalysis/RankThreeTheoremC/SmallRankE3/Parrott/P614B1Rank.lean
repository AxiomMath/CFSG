module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614B1Lift
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614L615
public import CFSG.Goldschmidt.Steps.G310Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614B1

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K2 (Bar barMk)

section SubgroupOf

variable {G : Type} [Group G]

theorem isElemAbelian_subgroupOf {p : ℕ} {E : Subgroup G} (M : Subgroup G)
    (hE : IsElemAbelian p E) : IsElemAbelian p (E.subgroupOf M) := by
  obtain ⟨hcomm, hpow⟩ := hE
  refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun y hy => Subtype.ext (hpow _ hy)⟩
  have h := mul_comm' (⟨a.1.1, Subgroup.mem_subgroupOf.mp a.2⟩ : E)
    ⟨b.1.1, Subgroup.mem_subgroupOf.mp b.2⟩
  have h' := congrArg Subtype.val h
  exact h'

theorem mem_normalizer_subgroupOf {A M : Subgroup G} {y : ↥M}
    (hy : (y : G) ∈ normalizer (A : Set G)) :
    y ∈ normalizer ((A.subgroupOf M : Subgroup ↥M) : Set ↥M) := by
  rw [mem_normalizer_iff]
  intro t
  exact mem_normalizer_iff.mp hy (t : G)

theorem isMaxTwoInvariantIn_subgroupOf {B M T : Subgroup G} (hBM : B ≤ M)
    (hT : IsMaxTwoInvariantIn B M T) :
    IsMaxTwoInvariantIn (B.subgroupOf M) ⊤ (T.subgroupOf M) := by
  obtain ⟨⟨hTM, hT2, hBT⟩, hmax⟩ := hT
  refine ⟨⟨le_top, hT2.comap_subtype, fun b hb => mem_normalizer_subgroupOf (hBT hb)⟩, ?_⟩
  rintro S' ⟨-, hS'2, hBS'⟩ hTS'
  have hinv : IsTwoInvariantIn B M (S'.map M.subtype) := by
    refine ⟨map_subtype_le _, hS'2.map _, fun b hb => ?_⟩
    have hb' : (⟨b, hBM hb⟩ : ↥M) ∈ B.subgroupOf M := hb
    exact le_normalizer_map M.subtype ⟨⟨b, hBM hb⟩, hBS' hb', rfl⟩
  have hle : T ≤ S'.map M.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hTM]
    exact map_mono hTS'
  have heq : S'.map M.subtype = T := hmax _ hinv hle
  rw [← heq]
  exact (Subgroup.comap_map_eq_self_of_injective M.subtype_injective S').symm

end SubgroupOf

theorem le_pRank_normalizer_of_sylow {X : Type} [Group X] [Finite X] {R H T : Subgroup X}
    (hR : ¬ 3 ∣ Nat.card R) (hT : fusionIsSylowIn 2 T R) (hHR : H ≤ normalizer (R : Set X)) :
    CFSG.Open.pRank 3 H ≤ CFSG.Open.pRank 3 (normalizer (T : Set X)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E, hEH, hE, hEc⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3) H
  have hE3 : IsPGroup 3 E := IsPGroup.of_card hEc
  have hbot2 : IsPGroup 2 (⊥ : Subgroup X) := IsPGroup.of_card (n := 0) (by simp)
  have hbot3 : IsPGroup 3 (⊥ : Subgroup X) := IsPGroup.of_card (n := 0) (by simp)
  have hEbot : E ≤ normalizer ((⊥ : Subgroup X) : Set X) := by
    rw [normalizer_eq_top_iff.mpr inferInstance]
    exact le_top
  obtain ⟨S₂, hS₂, -, hES₂⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
    Nat.prime_three Nat.prime_two hE3 hR (hEH.trans hHR) bot_le hbot2 hEbot
  obtain ⟨c, -, hS₂eq⟩ := CFSG.Goldschmidt.G310.exists_conj_of_invariant_sylows
    Nat.prime_three Nat.prime_two hbot3 hR bot_le hT hS₂ bot_le bot_le
  have hT' : S₂.map (MulAut.conj c⁻¹).toMonoidHom = T := by
    rw [CFSG.Goldschmidt.G310.conjSub_eq_map_conj, inv_inv, hS₂eq,
      CFSG.Goldschmidt.G310.conjSub_eq_map_conj, CFSG.Goldschmidt.G310.conjSub_conjSub_inv]
  have hE'N : E.map (MulAut.conj c⁻¹).toMonoidHom ≤ normalizer (T : Set X) := by
    rw [← hT', ← Subgroup.map_equiv_normalizer_eq]
    exact map_mono hES₂
  have hE'c : Nat.card ↥(E.map (MulAut.conj c⁻¹).toMonoidHom) = 3 ^ CFSG.Open.pRank 3 H := by
    rw [Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective, hEc]
  exact CFSG.SectionRank.le_pRank (by norm_num) hE'N (CFSG.SectionRank.isElemAbelian_map hE _)
    hE'c

theorem fusionIsSylowIn_of_isMax {X : Type} [Group X] [Finite X] {B R T : Subgroup X}
    (hB : IsPGroup 3 B) (hR : ¬ 3 ∣ Nat.card R) (hBR : B ≤ normalizer (R : Set X))
    (hTR : T ≤ R) (hT : IsMaxTwoInvariantIn B ⊤ T) : fusionIsSylowIn 2 T R := by
  obtain ⟨S₁, hS₁, hTS₁, hBS₁⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
    Nat.prime_three Nat.prime_two hB hR hBR hTR hT.1.2.1 hT.1.2.2
  have heq : S₁ = T := hT.2 S₁ ⟨le_top, hS₁.2.1, hBS₁⟩ hTS₁
  rwa [heq] at hS₁

theorem l62_caseDelta_rank (k292 : KFact292) (hNC : T29.NoncyclicCentreRank)
    (hQ : KFactThreeComponentsQRank) {X : Type} [Group X] [Finite X] {S : Sylow 3 X} {x z : X}
    (h : L62Data X S x z) (hnc : ¬ HasPrimeConstraint (G := X) 3) {Px B T : Subgroup X}
    (hPx : CFSG.ABGLocalTools.IsSylowOf 3 Px (centralizer ({x} : Set X))) (hBPx : B ≤ Px)
    (hB : IsElemAbelian 3 B) (hΩ : ∀ q ∈ Px, q ^ 3 = 1 → q ∈ B)
    (hT : IsMaxTwoInvariantIn B ⊤ T) :
    3 ≤ CFSG.Open.pRank 3 (normalizer (T : Set X)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S', x', z', hB'⟩ := l62Data_toBar h
  obtain ⟨L, hL⟩ :=
    Stroth.Bal3.exists_isComponentOf_of_not_hasPrimeConstraint Nat.prime_three hnc
  have huniq := l62_unique_component hNC hQ h hB' hL
  obtain ⟨hxbar, hCmap, -, hcent⟩ := l62_bar_point h
  have hrank : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (Bar X)) :=
    hB'.rank.ge.trans (pRank_mono 3 (by norm_num) le_top)
  have hO : ¬ 3 ∣ Nat.card (primeComplementCore (G := X) 3) := K2.qs_not_dvd_core
  have hsurj : Function.Surjective (barMk X) := QuotientGroup.mk'_surjective _
  have hPxbar : CFSG.ABGLocalTools.IsSylowOf 3 (Px.map (barMk X))
      (centralizer ({barMk X x} : Set (Bar X))) := by
    rw [hCmap]
    exact isSylowOf_map_hom hPx (barMk X)
  have hΩbar : ∀ q ∈ Px.map (barMk X), q ^ 3 = 1 → q ∈ B.map (barMk X) := by
    rintro _ ⟨p, hp, rfl⟩ hq3
    have hp3 : p ^ 3 ∈ primeComplementCore (G := X) 3 :=
      (QuotientGroup.eq_one_iff _).mp (by rw [← map_pow] at hq3; exact hq3)
    exact ⟨p, hΩ p hp (K2.qs_eq_one_of_mem hPx.isPGroup (pow_mem hp 3) hp3), rfl⟩
  have hTbar : IsTwoInvariantIn (B.map (barMk X)) ⊤ (T.map (barMk X)) :=
    ⟨le_top, hT.1.2.1.map _, (map_mono hT.1.2.2).trans (le_normalizer_map _)⟩
  obtain ⟨Tst, hTTst, hTst⟩ := exists_isMaxTwoInvariantIn_of_le hTbar
  have hk := k292 (Bar X) hB'.catalog hB'.core L hL huniq hrank
    (fun N _ hN => eq_top_of_isPGroup_quotient hB'.no_normal_three N hN) (barMk X x) hxbar hcent
    (Px.map (barMk X)) (B.map (barMk X)) hPxbar (map_mono hBPx)
    (CFSG.SectionRank.isElemAbelian_map hB _) hΩbar Tst hTst
  set R₀ : Subgroup X := Tst.comap (barMk X) with hR₀def
  set H₀ : Subgroup X := (normalizer (Tst : Set (Bar X))).comap (barMk X) with hH₀def
  have hR₀ : ¬ 3 ∣ Nat.card R₀ := by
    intro hdvd
    obtain ⟨r, hr⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
    have hr' : orderOf (r : X) = 3 := by rw [Subgroup.orderOf_coe]; exact hr
    have hr3 : (r : X) ^ 3 = 1 := by rw [← hr']; exact pow_orderOf_eq_one _
    have h1 : barMk X (r : X) = 1 := by
      obtain ⟨k, hk⟩ := hTst.1.2.1 ⟨barMk X (r : X), r.2⟩
      have hk' : (barMk X (r : X)) ^ 2 ^ k = 1 := congrArg Subtype.val hk
      have h3 : (barMk X (r : X)) ^ 3 = 1 := by rw [← map_pow, hr3, map_one]
      exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
        (Nat.Coprime.pow_right k (by norm_num)) (orderOf_dvd_of_pow_eq_one h3)
        (orderOf_dvd_of_pow_eq_one hk'))
    have hrD : (r : X) ∈ primeComplementCore (G := X) 3 := (QuotientGroup.eq_one_iff _).mp h1
    have h3 := orderOf_dvd_natCard (⟨(r : X), hrD⟩ : primeComplementCore (G := X) 3)
    rw [Subgroup.orderOf_mk, hr'] at h3
    exact hO h3
  have hTR₀ : T ≤ R₀ := Subgroup.map_le_iff_le_comap.mp hTTst
  have hBR₀ : B ≤ normalizer (R₀ : Set X) :=
    CFSG.Goldschmidt.G310.le_normalizer_comap _ hTst.1.2.2
  have hHR₀ : H₀ ≤ normalizer (R₀ : Set X) :=
    CFSG.Goldschmidt.G310.le_normalizer_comap _ (Subgroup.map_comap_le _ _)
  have hH₀rank : 3 ≤ CFSG.Open.pRank 3 H₀ := by
    have h1 : H₀.map (barMk X) = normalizer (Tst : Set (Bar X)) :=
      Subgroup.map_comap_eq_self_of_surjective hsurj _
    have hcop : ¬ 3 ∣ Nat.card ↥(H₀ ⊓ (barMk X).ker) := fun hd =>
      hO (hd.trans (Subgroup.card_dvd_of_le (inf_le_right.trans K2.qs_ker.le)))
    have h2 := K2.pRank_map_eq_of_coprime_ker (barMk X) Nat.prime_three hcop
    rw [h1] at h2
    omega
  have hB3 : IsPGroup 3 B := fun b => ⟨1, Subtype.ext (by simpa using hB.2 _ b.2)⟩
  have hTsyl : fusionIsSylowIn 2 T R₀ := fusionIsSylowIn_of_isMax hB3 hR₀ hBR₀ hTR₀ hT
  exact hH₀rank.trans (le_pRank_normalizer_of_sylow hR₀ hTsyl hHR₀)

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614B1
