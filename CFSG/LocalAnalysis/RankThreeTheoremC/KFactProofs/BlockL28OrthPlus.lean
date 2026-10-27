module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockL28Generic
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthPlusMain
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockL28Arith

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.LeviBlock CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit CFSG.LieType.Universal.Spin

theorem plus_eq_eight_of_mem_plusBlockOrders {q f : ℕ} (hq : q = 2 ^ f)
    (h : 504 ∈ plusBlockOrders q) : q = 8 := by
  rcases h with ⟨k, -, hk⟩ | ⟨m, -, hm⟩
  · exact ((ordA_eq_504_iff hq).1 hk.symm).2
  · exact absurd hm.symm (ordD_ne_504 hq)

theorem plus_exists_extend {M : Type*} [Group M] {k r : ℕ} (hk : k ≤ r) :
    ∃ e : (Fin k → M) →* (Fin r → M), Function.Injective e := by
  refine ⟨{ toFun := fun t i => if h : (i : ℕ) < k then t ⟨i, h⟩ else 1
            map_one' := ?_
            map_mul' := ?_ }, ?_⟩
  · funext i
    by_cases h : (i : ℕ) < k <;> simp [h]
  · intro a b
    funext i
    by_cases h : (i : ℕ) < k <;> simp [h]
  · intro a b h
    funext j
    have := congrFun h ⟨j, by omega⟩
    simpa using this

theorem plus_exists_torus_of_borel_le {Y : Type} [Group Y] [Finite Y] {L P : Subgroup Y}
    {r k : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] (hr : 3 ≤ r) (hk : k ≤ r)
    (ρ : ↥(orthElementaryGroup (quadPlus r K)) ≃* ↥L)
    (hB : borel r K ≤ ((P.subgroupOf L).comap ρ.toMonoidHom).map
      (orthElementaryGroup (quadPlus r K)).subtype) :
    ∃ f : (Fin k → Kˣ) →* Y, Function.Injective f ∧ f.range ≤ P := by
  have hE : ∀ a : Fin r → Kˣ, torusElt r K a ∈ orthElementaryGroup (quadPlus r K) := fun a =>
    maxStab_le_orthElementaryGroup hr (mem_posBorel.1 (torusElt_mem_posBorel a)).1
  let τ : (Fin r → Kˣ) →* ↥(orthElementaryGroup (quadPlus r K)) :=
    (torusElt r K).codRestrict _ hE
  obtain ⟨e, he⟩ := plus_exists_extend (M := Kˣ) hk
  refine ⟨L.subtype.comp (ρ.toMonoidHom.comp (τ.comp e)), ?_, ?_⟩
  · intro a b h
    apply he
    have h1 : ρ (τ (e a)) = ρ (τ (e b)) := Subtype.ext h
    exact torusElt_injective (congrArg Subtype.val (ρ.injective h1))
  · rintro _ ⟨a, rfl⟩
    have hb : torusElt r K (e a) ∈ borel r K := torus_le_borel ⟨hE _, e a, rfl⟩
    obtain ⟨y, hy, hya⟩ := hB hb
    have : y = τ (e a) := Subtype.ext hya
    rw [this] at hy
    exact Subgroup.mem_subgroupOf.1 hy

theorem plus_exists_torus_of_l28Section (hZ : OddCenterRest) {Y : Type} [Group Y] [Finite Y]
    {L P : Subgroup Y} (hCP : CompParab L P) (hD : IsLieOf IdxD (↥L ⧸ Subgroup.center ↥L))
    {N : Subgroup Y} (hNP : N ≤ P) (hPN : P ≤ Subgroup.normalizer (N : Set Y))
    {d : TauCeti.ValidLieTypeIndex} (ψ : ↥N →* CatGroup d) (hd : IsCaseTwoIndex 3 d)
    (hψ : Function.Surjective ψ) (k : ℕ) (hk : k ≤ 4) :
    ∃ (M : Type) (_ : CommGroup M), Nat.card M = 7 ∧
      ∃ f : (Fin k → M) →* Y, Function.Injective f ∧ f.range ≤ P := by
  obtain ⟨r, K, _, _, _, ρ, hr, hQ, hB⟩ := exists_hasLeviBlocks_of_idxD hZ hCP hD
  have := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  have hK : Nat.card K = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  have : Finite ↥(orthElementaryGroup (quadPlus r K)) := Finite.of_equiv _ ρ.symm.toEquiv
  have h504 : 504 ∈ plusBlockOrders (Nat.card K) :=
    card_mem_of_l28Section hCP.parab.1 ρ.toMonoidHom ρ.surjective hQ hNP hPN ψ hd hψ
  have h8 : Nat.card K = 8 := plus_eq_eight_of_mem_plusBlockOrders hK h504
  obtain ⟨f, hf, hfP⟩ := plus_exists_torus_of_borel_le (k := k) (by omega) (by omega) ρ hB
  exact ⟨Kˣ, inferInstance, by rw [Nat.card_units, h8], f, hf, hfP⟩

theorem kFactCompParabL28RankOn_idxD (hZ : OddCenterRest) :
    KFactCompParabL28RankOn (IsLieOf IdxD) := by
  intro Y _ _ L P hCP hD N hNP hPN d ψ hd hψ
  obtain ⟨M, _, hM, f, hf, hfP⟩ := plus_exists_torus_of_l28Section hZ hCP hD hNP hPN ψ hd hψ 2
    (by norm_num)
  exact l28_E_of_torus_of_not_dvd hM
    (not_dvd_card_center_rest hZ hCP.comp hCP.odd (Or.inr (Or.inl hD))
      (by norm_num : Nat.Prime 7) (by norm_num))
    f hf (hfP.trans hCP.parab.1)

theorem kFactCompParabL28TwoRankOn_idxD (hZ : OddCenterRest) :
    KFactCompParabL28TwoRankOn (IsLieOf IdxD) := by
  intro Y _ _ L P hCP hD N hNP hPN d₁ d₂ ψ hd₁ hd₂ hψ
  have hfst : Function.Surjective (MonoidHom.fst (CatGroup d₁) (CatGroup d₂)) :=
    fun a => ⟨(a, 1), rfl⟩
  have hψ₁ : Function.Surjective ((MonoidHom.fst (CatGroup d₁) (CatGroup d₂)).comp ψ) :=
    hfst.comp hψ
  obtain ⟨M, _, hM, f, hf, hfP⟩ := plus_exists_torus_of_l28Section hZ hCP hD hNP hPN
    ((MonoidHom.fst (CatGroup d₁) (CatGroup d₂)).comp ψ) hd₁ hψ₁ 3 (by norm_num)
  exact three_le_pRank_of_torus hM f hf (hfP.trans hCP.parab.1)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
