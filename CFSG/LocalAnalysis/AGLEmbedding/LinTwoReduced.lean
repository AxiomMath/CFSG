module

public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoFacts
public import CFSG.LocalAnalysis.AGLEmbedding.RankLemmas
public import CFSG.LocalAnalysis.AGLEmbedding.ReducedQuotient

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers

section Reduced

variable {Y : Type} [Group Y] [Finite Y]

theorem exists_sylow_map_subtype_eq_inf {p : ℕ} [Fact p.Prime] (K : Subgroup Y) [K.Normal]
    (Rb : Sylow p Y) :
    ∃ T : Sylow p K, (T : Subgroup K).map K.subtype = (Rb : Subgroup Y) ⊓ K := by
  have hR : CFSG.ABGLocalTools.IsSylowOf p (Rb : Subgroup Y) ⊤ :=
    CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨le_top, Rb.isPGroup', by
      rw [Subgroup.relIndex_top_right]
      exact Rb.not_dvd_index⟩
  exact hR.inf_of_le_normalizer le_top (Subgroup.normalizer_eq_top (H := K)).ge

theorem centralizer_sylow_inf_le_of_psl2GF (hKL1 : KFactL2UnipotentCentralizer)
    {p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hn : 1 ≤ n) {K : Subgroup Y} (hKn : K.Normal)
    (hK : Nonempty (K ≃* PSL2GF p n)) (hC : Subgroup.centralizer (K : Set Y) = ⊥)
    (Rb : Sylow p Y) :
    Subgroup.centralizer ((((Rb : Subgroup Y) ⊓ K : Subgroup Y)) : Set Y) ≤
      (Rb : Subgroup Y) ⊓ K := by
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
  obtain ⟨u, hu, hαu⟩ := hKL1 p n hp2 hn U α hfix
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
  rw [hC, Subgroup.mem_bot, inv_mul_eq_one] at hcent
  exact hcent ▸ hTmem t ht

omit [Finite Y] in
theorem card_dvd_of_isPGroup_of_psl2GF (hKL2 : KFactL2AutPCard) {p n : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hn : 1 ≤ n) {K : Subgroup Y} (hKn : K.Normal)
    (hK : Nonempty (K ≃* PSL2GF p n)) (hC : Subgroup.centralizer (K : Set Y) = ⊥)
    (A : Subgroup Y) (hA : IsPGroup p A) : Nat.card A ∣ p ^ n * n := by
  obtain ⟨e⟩ := hK
  let f : Y →* MulAut (PSL2GF p n) :=
    (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal (H := K))
  have hinj : Function.Injective (MulAut.conjNormal (H := K) : Y →* MulAut K) := by
    rw [← MonoidHom.ker_eq_bot_iff, ker_conjNormal_eq_centralizer, hC]
  have hf : Function.Injective f := (MulAut.congr e).injective.comp hinj
  have h := hKL2 p n hp2 hn (A.map f) (hA.map f)
  rwa [Subgroup.card_map_of_injective hf] at h

theorem isElemAbelian_sylow_inf_of_psl2GF {p n : ℕ} [Fact p.Prime] (hn : 1 ≤ n)
    {K : Subgroup Y} [K.Normal] (e : K ≃* PSL2GF p n) (Rb : Sylow p Y) :
    IsElemAbelian p ((Rb : Subgroup Y) ⊓ K) ∧
      Nat.card ((Rb : Subgroup Y) ⊓ K : Subgroup Y) = p ^ n := by
  obtain ⟨T, hT⟩ := exists_sylow_map_subtype_eq_inf K Rb
  have hes : Function.Surjective (e : K →* PSL2GF p n) := e.surjective
  obtain ⟨hUab, hUcard⟩ := psl2GF_sylow p n hn (T.mapSurjective hes)
  rw [Sylow.coe_mapSurjective] at hUab hUcard
  have hTU : ((T : Subgroup K).map (e : K →* PSL2GF p n)).map (e.symm : PSL2GF p n →* K) = T :=
    (Subgroup.map_symm_eq_iff_map_eq _).mpr rfl
  refine ⟨?_, ?_⟩
  · have h := elementary_abelian_map p
      (elementary_abelian_map p hUab (e.symm : PSL2GF p n →* K)) K.subtype
    rwa [hTU, hT] at h
  · rw [← hT, Subgroup.card_map_of_injective K.subtype_injective, ← hUcard,
      Subgroup.card_map_of_injective (show Function.Injective (e : K →* PSL2GF p n) from
        e.injective)]

theorem inf_le_normalizer_of_psl2GF {p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hn : 1 ≤ n)
    {K : Subgroup Y} [K.Normal] (e : K ≃* PSL2GF p n) (Rb : Sylow p Y) {Y₀ : Subgroup Y}
    (hN : Subgroup.normalizer (((Rb : Subgroup Y) ⊓ K : Subgroup Y) : Set Y) ≤ Y₀)
    (hKY₀ : ¬ K ≤ Y₀) :
    Y₀ ⊓ K ≤ Subgroup.normalizer (((Rb : Subgroup Y) ⊓ K : Subgroup Y) : Set Y) := by
  obtain ⟨T, hT⟩ := exists_sylow_map_subtype_eq_inf K Rb
  have hes : Function.Surjective (e : K →* PSL2GF p n) := e.surjective
  have hB : IsCoatom (Subgroup.normalizer ((T : Subgroup K) : Set K)) := by
    have h := psl2GF_borelCoatom p n hp2 hn (T.mapSurjective hes)
    rw [Sylow.coe_mapSurjective, ← MulEquiv.toMonoidHom_eq_coe,
      ← Subgroup.map_equiv_normalizer_eq] at h
    exact (OrderIso.isCoatom_iff e.mapSubgroup _).mp h
  have hmap : ∀ k ∈ Subgroup.normalizer ((T : Subgroup K) : Set K),
      (k : Y) ∈ Subgroup.normalizer (((Rb : Subgroup Y) ⊓ K : Subgroup Y) : Set Y) := by
    intro k hk
    rw [← hT]
    exact Subgroup.le_normalizer_map K.subtype (Subgroup.mem_map_of_mem K.subtype hk)
  have hNK : Subgroup.normalizer ((T : Subgroup K) : Set K) ≤ Y₀.subgroupOf K :=
    fun k hk => Subgroup.mem_subgroupOf.mpr (hN (hmap k hk))
  have heq : Y₀.subgroupOf K = Subgroup.normalizer ((T : Subgroup K) : Set K) :=
    (hB.le_iff.mp hNK).resolve_left fun h => hKY₀ (Subgroup.subgroupOf_eq_top.mp h)
  rintro y ⟨hy₀, hyK⟩
  exact hmap ⟨y, hyK⟩ (heq ▸ Subgroup.mem_subgroupOf.mpr hy₀)

theorem eq_bot_of_inf_le_normalizer_of_centralizer_le {p : ℕ} (hp : p.Prime)
    {W Y₀ K T : Subgroup Y} [K.Normal] (hWY₀ : W ≤ Y₀)
    (hY₀W : Y₀ ≤ Subgroup.normalizer (W : Set Y)) (hW : p.Coprime (Nat.card W))
    (hT : IsPGroup p T) (hTY₀ : T ≤ Y₀) (hTK : T ≤ K)
    (hY₀K : Y₀ ⊓ K ≤ Subgroup.normalizer (T : Set Y))
    (hCT : Subgroup.centralizer (T : Set Y) ≤ T) : W = ⊥ := by
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
    rw [eq_bot_iff, ← hWT]
    rintro w ⟨hw, hwK⟩
    have hwN := hY₀K ⟨hWY₀ hw, hwK⟩
    refine ⟨hw, hCT (hcomm T hWT w hw fun t ht => ?_)⟩
    exact T.mul_mem ((Subgroup.mem_normalizer_iff.mp hwN t).mp ht) (T.inv_mem ht)
  rw [eq_bot_iff, ← hWT]
  intro w hw
  refine ⟨hw, hCT (hcomm K hWK w hw fun t ht => ?_)⟩
  exact K.mul_mem (Subgroup.Normal.conj_mem inferInstance t (hTK ht) w) (K.inv_mem (hTK ht))

theorem primeComplementCore_eq_bot_of_psl2GF (hKL1 : KFactL2UnipotentCentralizer)
    {p n : ℕ} [Fact p.Prime] (Rb : Sylow p Y) (Y₀ : Subgroup Y)
    (hred : ReducedNongeneration p Y Rb Y₀) (hn : 3 ≤ n) {K : Subgroup Y} (hKn : K.Normal)
    (hK : Nonempty (K ≃* PSL2GF p n)) (hC : Subgroup.centralizer (K : Set Y) = ⊥) :
    primeComplementCore (G := Y₀) p = ⊥ := by
  obtain ⟨e⟩ := hK
  have hp : p.Prime := hred.prime
  have hn1 : 1 ≤ n := by omega
  obtain ⟨hTab, hTcard⟩ := isElemAbelian_sylow_inf_of_psl2GF hn1 e Rb
  have hrank : 3 ≤ Open.pRank p ((Rb : Subgroup Y) ⊓ K) :=
    hn.trans (le_csSup (pRank_bddAbove p hp _) ⟨_, le_rfl, hTab, hTcard⟩)
  have hN : Subgroup.normalizer (((Rb : Subgroup Y) ⊓ K : Subgroup Y) : Set Y) ≤ Y₀ :=
    (normalizer_le_weakCore p inf_le_left (by omega)
      (hrank.trans (pRank_mono p hp le_sup_left))).trans hred.weakCore_le
  have hKY₀ : ¬ K ≤ Y₀ := not_le_of_weakCore_le hp Rb hred.weakCore_le hred.ne_top hrank
  have hWsub : ((primeComplementCore (G := Y₀) p).map Y₀.subtype).subgroupOf Y₀ =
      primeComplementCore (G := Y₀) p :=
    Subgroup.comap_map_eq_self_of_injective Y₀.subtype_injective _
  have hW : (primeComplementCore (G := Y₀) p).map Y₀.subtype = ⊥ :=
    eq_bot_of_inf_le_normalizer_of_centralizer_le (T := (Rb : Subgroup Y) ⊓ K) hp
      (Subgroup.map_subtype_le _)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).mp
        (by rw [hWsub]; infer_instance))
      (by rw [Subgroup.card_map_of_injective Y₀.subtype_injective]
          exact primeComplementCore_coprime p)
      Rb.isPGroup'.to_inf_left (Subgroup.le_normalizer.trans hN) inf_le_right
      (inf_le_normalizer_of_psl2GF hred.ne_two hn1 e Rb hN hKY₀)
      (centralizer_sylow_inf_le_of_psl2GF hKL1 hred.ne_two hn1 hKn ⟨e⟩ hC Rb)
  exact (Subgroup.map_eq_bot_iff_of_injective _ Y₀.subtype_injective).mp hW

end Reduced

end CFSG.AGLEmbedding
