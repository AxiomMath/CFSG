module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointBorelData
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoUnipotentCentralizer

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.PreuniquenessRankFour.Helpers Subgroup

section Reduced

variable {Y : Type} [Group Y] [Finite Y]

theorem centralizer_sylow_inf_le_sup_of_psl2GF {p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hn : 1 ≤ n) {K : Subgroup Y} (hKn : K.Normal) (hK : Nonempty (K ≃* PSL2GF p n))
    (Rb : Sylow p Y) :
    Subgroup.centralizer ((((Rb : Subgroup Y) ⊓ K : Subgroup Y)) : Set Y) ≤
      ((Rb : Subgroup Y) ⊓ K) ⊔ Subgroup.centralizer (K : Set Y) := by
  obtain ⟨e⟩ := hK
  obtain ⟨T, hT⟩ := exists_sylow_map_subtype_eq_inf K Rb
  have hTmem : ∀ t ∈ (T : Subgroup K), (t : Y) ∈ (Rb : Subgroup Y) ⊓ K := fun t ht =>
    hT ▸ Subgroup.mem_map_of_mem K.subtype ht
  have hes : Function.Surjective (e : K →* PSL2GF p n) := e.surjective
  set U : Sylow p (PSL2GF p n) := T.mapSurjective hes with hU
  have hUmem : ∀ u ∈ (U : Subgroup (PSL2GF p n)), ∃ t ∈ (T : Subgroup K), e t = u := by
    intro u hu
    rw [hU, Sylow.coe_mapSurjective] at hu
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hu
    exact ⟨t, ht, rfl⟩
  intro y hy
  set α : MulAut (PSL2GF p n) := MulAut.congr e (MulAut.conjNormal y) with hα
  have hαe : ∀ k : K, α (e k) = e (MulAut.conjNormal y k) := fun k => by
    simp [hα, MulAut.congr]
  have hfix : ∀ u ∈ (U : Subgroup (PSL2GF p n)), α u = u := by
    intro u hu
    obtain ⟨t, ht, rfl⟩ := hUmem u hu
    rw [hαe]
    congr 1
    refine Subtype.ext ?_
    rw [MulAut.conjNormal_apply]
    exact mul_inv_eq_of_eq_mul (Subgroup.mem_centralizer_iff.mp hy _ (hTmem t ht)).symm
  obtain ⟨u, hu, hαu⟩ := kFactL2UnipotentCentralizer p n hp2 hn U α hfix
  obtain ⟨t, ht, rfl⟩ := hUmem u hu
  have hconj : ∀ k : K, y * (k : Y) * y⁻¹ = (t : Y) * k * (t : Y)⁻¹ := by
    intro k
    have h := hαe k
    rw [hαu, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul] at h
    have h' := congrArg Subtype.val (e.injective h)
    rw [MulAut.conjNormal_apply] at h'
    simpa using h'.symm
  have hcent : (t : Y)⁻¹ * y ∈ Subgroup.centralizer (K : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have h := hconj ⟨k, hk⟩
    calc k * ((t : Y)⁻¹ * y) = (t : Y)⁻¹ * ((t : Y) * k * (t : Y)⁻¹) * y := by group
      _ = (t : Y)⁻¹ * (y * k * y⁻¹) * y := by rw [← h]
      _ = (t : Y)⁻¹ * y * k := by group
  have hy' : y = (t : Y) * ((t : Y)⁻¹ * y) := by group
  rw [hy']
  exact Subgroup.mul_mem_sup (hTmem t ht) hcent

theorem eq_bot_of_inf_le_normalizer_of_centralizer_le_of_isPGroup {p : ℕ} (hp : p.Prime)
    {W Y₀ K T B : Subgroup Y} [K.Normal] (hWY₀ : W ≤ Y₀)
    (hY₀W : Y₀ ≤ Subgroup.normalizer (W : Set Y)) (hW : p.Coprime (Nat.card W))
    (hT : IsPGroup p T) (hTY₀ : T ≤ Y₀) (hTK : T ≤ K)
    (hY₀K : Y₀ ⊓ K ≤ Subgroup.normalizer (T : Set Y))
    (hCT : Subgroup.centralizer (T : Set Y) ≤ B) (hB : IsPGroup p B) : W = ⊥ := by
  have hWB : W ⊓ B = ⊥ := by
    rw [inf_comm]
    exact inf_eq_bot_of_isPGroup hp hB hW
  have hWT : W ⊓ T = ⊥ := by
    rw [inf_comm]
    exact inf_eq_bot_of_isPGroup hp hT hW
  have hcW : ∀ w ∈ W, ∀ t ∈ T, w * t * w⁻¹ * t⁻¹ ∈ W := by
    intro w hw t ht
    have h := (Subgroup.mem_normalizer_iff.mp (hY₀W (hTY₀ ht)) w⁻¹).mp (W.inv_mem hw)
    simpa only [mul_assoc] using W.mul_mem hw h
  have hcomm : ∀ S : Subgroup Y, W ⊓ S = ⊥ → ∀ w ∈ W,
      (∀ t ∈ T, w * t * w⁻¹ * t⁻¹ ∈ S) → w ∈ Subgroup.centralizer (T : Set Y) := by
    intro S hS w hw hwS
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have h : w * t * w⁻¹ * t⁻¹ ∈ W ⊓ S := ⟨hcW w hw t ht, hwS t ht⟩
    rw [hS, Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h
    exact h.symm
  have hWK : W ⊓ K = ⊥ := by
    rw [eq_bot_iff]
    rintro w ⟨hw, hwK⟩
    have hwN := hY₀K ⟨hWY₀ hw, hwK⟩
    have hwC := hcomm T hWT w hw fun t ht =>
      T.mul_mem ((Subgroup.mem_normalizer_iff.mp hwN t).mp ht) (T.inv_mem ht)
    have : w ∈ W ⊓ B := ⟨hw, hCT hwC⟩
    rw [hWB] at this
    exact this
  rw [eq_bot_iff]
  intro w hw
  have hwC := hcomm K hWK w hw fun t ht =>
    K.mul_mem (Subgroup.Normal.conj_mem inferInstance t (hTK ht) w) (K.inv_mem (hTK ht))
  have : w ∈ W ⊓ B := ⟨hw, hCT hwC⟩
  rw [hWB] at this
  exact this

theorem eq_bot_of_coprime_of_psl2GF {p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hn : 3 ≤ n)
    {K : Subgroup Y} (hKn : K.Normal) (e : K ≃* PSL2GF p n)
    (hD : IsPGroup p (Subgroup.centralizer (K : Set Y))) (Rb : Sylow p Y) (Y₀ : Subgroup Y)
    (hN : Subgroup.normalizer (((Rb : Subgroup Y) ⊓ K : Subgroup Y) : Set Y) ≤ Y₀)
    (hKY₀ : ¬ K ≤ Y₀) {W : Subgroup Y} (hWY₀ : W ≤ Y₀)
    (hY₀W : Y₀ ≤ Subgroup.normalizer (W : Set Y)) (hW : p.Coprime (Nat.card W)) : W = ⊥ := by
  have hp : p.Prime := Fact.out
  have hn1 : 1 ≤ n := by omega
  set T : Subgroup Y := (Rb : Subgroup Y) ⊓ K with hT
  have hTp : IsPGroup p T := Rb.isPGroup'.to_inf_left
  set D : Subgroup Y := Subgroup.centralizer (K : Set Y) with hDdef
  have : K.Normal := hKn
  have hB : IsPGroup p ↥(T ⊔ D) := by
    intro g
    obtain ⟨t, ht, d, hd, hg⟩ := Subgroup.mem_sup_of_normal_right.mp g.2
    obtain ⟨a, ha⟩ := hTp ⟨t, ht⟩
    obtain ⟨b, hb⟩ := hD ⟨d, hd⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have hcomm : Commute t d := Subgroup.mem_centralizer_iff.mp hd t ht.2
    have ht' : t ^ (p ^ a) = 1 := by simpa using congrArg Subtype.val ha
    have hd' : d ^ (p ^ b) = 1 := by simpa using congrArg Subtype.val hb
    have h1 : t ^ (p ^ (a + b)) = 1 := by rw [pow_add, pow_mul, ht', one_pow]
    have h2 : d ^ (p ^ (a + b)) = 1 := by rw [pow_add, mul_comm, pow_mul, hd', one_pow]
    show (g : Y) ^ (p ^ (a + b)) = 1
    rw [← hg, hcomm.mul_pow, h1, h2, one_mul]
  have hTY₀ : T ≤ Y₀ := Subgroup.le_normalizer.trans hN
  exact eq_bot_of_inf_le_normalizer_of_centralizer_le_of_isPGroup hp hWY₀ hY₀W hW hTp hTY₀
    inf_le_right (inf_le_normalizer_of_psl2GF hp2 hn1 e Rb hN hKY₀)
    (centralizer_sylow_inf_le_sup_of_psl2GF hp2 hn1 hKn ⟨e⟩ Rb) hB

end Reduced

variable {G : Type} [Group G] [Finite G]

namespace IsPPoint

variable {M : Subgroup G} {x : G}

theorem not_two_dvd_card_inf_primeCore_three {P : Sylow 3 G} (hin : PPointThreeInputs)
    (hS : D1Global G) (hD1 : D1For G) (hFC : FullCoreLocality G) (hloc : D1Local 3 P M)
    (h : IsPPoint 3 P M x) :
    ¬ 2 ∣ Nat.card (GLBPrimeCore 3 M ⊓ centralizer ({x} : Set G) : Subgroup G) := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  obtain ⟨R, K, d, n, hf, hn, hd, -, -⟩ := h.exists_linTwo_three hin.h243 hin.h244 hin.hsig
    hin.h313 hin.hUB hin.hUI hin.hRB hin.hRI hin.hKU9 hin.hM11 hS hD1 hFC hloc
  obtain ⟨eK⟩ := hf.equiv
  obtain ⟨eP⟩ := nonempty_mulEquiv_psl2GF_of_isLinTwoIndex hd
  set e : K ≃* PSL2GF 3 n := eK.trans eP with he
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set Ob : Subgroup C := primeComplementCore (G := C) 3 with hOb
  set ρ : C →* RedCent 3 x := QuotientGroup.mk' Ob with hρ
  set N : Subgroup G := GLBPrimeCore 3 M with hNdef
  set Zc : Subgroup C := (N ⊓ C).subgroupOf C with hZc
  set W : Subgroup (RedCent 3 x) := Zc.map ρ with hW
  have hNM : N ≤ M := glbPrimeCore_le 3 M
  have hMN : M ≤ normalizer (N : Set G) := le_normalizer_glbPrimeCore 3 M
  have hred := hf.red
  have hWX₀ : W ≤ redCentM 3 M x :=
    Subgroup.map_mono fun c hc => mem_subgroupOf.mpr ⟨c.2, hNM (mem_subgroupOf.mp hc).1⟩
  have hX₀W : redCentM 3 M x ≤ normalizer (W : Set (RedCent 3 x)) := by
    rintro _ ⟨c, hc, rfl⟩
    have hcM : (c : G) ∈ M := (mem_subgroupOf.mp hc).2
    have hcZ : c ∈ normalizer (Zc : Set C) := by
      rw [mem_normalizer_iff]
      intro z
      have hz := mem_normalizer_iff.mp (hMN hcM) (z : G)
      constructor
      · intro hzZ
        exact mem_subgroupOf.mpr ⟨hz.mp (mem_subgroupOf.mp hzZ).1, (c * z * c⁻¹).2⟩
      · intro hzZ
        exact mem_subgroupOf.mpr ⟨hz.mpr (mem_subgroupOf.mp hzZ).1, z.2⟩
    exact Subgroup.le_normalizer_map ρ ⟨c, hcZ, rfl⟩
  have hWcop : (3 : ℕ).Coprime (Nat.card W) := by
    have h1 : Nat.card W ∣ Nat.card Zc := Subgroup.card_map_dvd Zc ρ
    have h2 : Nat.card Zc ∣ Nat.card N := by
      rw [hZc, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : N ⊓ C ≤ C)).toEquiv]
      exact Subgroup.card_dvd_of_le inf_le_left
    exact (glbPrimeCore_coprime 3 M).coprime_dvd_right (h1.trans h2)
  have hn1 : 1 ≤ n := by omega
  have hKn : K.Normal := hred.normal
  obtain ⟨hTab, hTcard⟩ := isElemAbelian_sylow_inf_of_psl2GF hn1 e R
  have hrank : 3 ≤ Open.pRank 3 ((R : Subgroup (RedCent 3 x)) ⊓ K) :=
    hn.trans (le_csSup (pRank_bddAbove 3 hp _) ⟨_, le_rfl, hTab, hTcard⟩)
  have hN : normalizer ((((R : Subgroup (RedCent 3 x)) ⊓ K : Subgroup (RedCent 3 x))) :
      Set (RedCent 3 x)) ≤ redCentM 3 M x :=
    (normalizer_le_glbCore 3 2 inf_le_left (by omega)).trans hred.fullCore
  have hWbot : W = ⊥ := eq_bot_of_coprime_of_psl2GF (by norm_num) hn hKn e hf.isPGroup R _ hN
    hred.not_le hWX₀ hX₀W hWcop
  have hZO : Zc ≤ Ob := by
    have := (Subgroup.map_eq_bot_iff (f := ρ) (H := Zc)).mp hWbot
    rwa [hρ, QuotientGroup.ker_mk'] at this
  have hNC : N ⊓ C ≤ GLBPrimeCore 3 C := fun g hg => by
    have := hZO (mem_subgroupOf.mpr hg : (⟨g, hg.2⟩ : C) ∈ Zc)
    have h3 : (⟨g, hg.2⟩ : C) ∈ (GLBPrimeCore 3 C).subgroupOf C := by
      rw [glbPrimeCore_subgroupOf]
      exact this
    exact mem_subgroupOf.mp h3
  intro h2
  exact h.not_two_dvd_card_primeCore hS hD1 hloc (h2.trans (Subgroup.card_dvd_of_le hNC))

end IsPPoint

end CFSG.LocalAnalysis.RankFourTheoremC
