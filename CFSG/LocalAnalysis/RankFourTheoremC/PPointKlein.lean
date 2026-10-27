module

public import CFSG.CharacterTheory.PSL2Table.Basic
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCatalog
import CFSG.CharacterTheory.PSL2Table.Tori
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoFacts

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.PSL2Table
open scoped MatrixGroups

theorem exists_isPGroup_two_normalized_of_commute {G : Type*} [Group G] {x y z : G}
    (hx : x * x = 1) (hy : y * y = 1) (hxy : x * y = y * x)
    (hzx : z * x * z⁻¹ = y) (hzy : z * y * z⁻¹ = x * y) :
    ∃ V : Subgroup G, IsPGroup 2 V ∧ x ∈ V ∧ z ∈ Subgroup.normalizer (V : Set G) := by
  have hz2 : ∀ t : G, t * t = 1 → IsPGroup 2 (Subgroup.zpowers t) := by
    intro t ht
    have hdvd : orderOf t ∣ 2 := orderOf_dvd_of_pow_eq_one (by rwa [pow_two])
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
  have hxN : Subgroup.zpowers x ≤ Subgroup.normalizer (Subgroup.zpowers y : Set G) := by
    refine Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer
      (Subgroup.zpowers y : Set G) ?_)
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact (Commute.zpow_left (show Commute y x from hxy.symm) k).eq
  have hV : Subgroup.closure ({x, y} : Set G) = Subgroup.zpowers x ⊔ Subgroup.zpowers y := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union]
    rfl
  set V : Subgroup G := Subgroup.closure ({x, y} : Set G) with hVdef
  have hxV : x ∈ V := Subgroup.subset_closure (by simp)
  have hyV : y ∈ V := Subgroup.subset_closure (by simp)
  have key : ∀ g : G, g * x * g⁻¹ ∈ V → g * y * g⁻¹ ∈ V → ∀ h ∈ V, g * h * g⁻¹ ∈ V := by
    intro g hgx hgy h hh
    induction hh using Subgroup.closure_induction with
    | mem t ht =>
      rcases ht with rfl | ht
      · exact hgx
      · rw [Set.mem_singleton_iff.mp ht]
        exact hgy
    | one => simp
    | mul a b _ _ ha hb =>
      have : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
      rw [this]
      exact V.mul_mem ha hb
    | inv a _ ha =>
      have : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
      rw [this]
      exact V.inv_mem ha
  have h1 : z * (x * y) * z⁻¹ = x := by
    calc z * (x * y) * z⁻¹ = (z * x * z⁻¹) * (z * y * z⁻¹) := by group
      _ = y * (x * y) := by rw [hzx, hzy]
      _ = x := by rw [hxy, ← mul_assoc, hy, one_mul]
  have hzx' : z⁻¹ * x * z⁻¹⁻¹ = x * y := by
    calc z⁻¹ * x * z⁻¹⁻¹ = z⁻¹ * (z * (x * y) * z⁻¹) * z⁻¹⁻¹ := by rw [h1]
      _ = x * y := by group
  have hzy' : z⁻¹ * y * z⁻¹⁻¹ = x := by
    calc z⁻¹ * y * z⁻¹⁻¹ = z⁻¹ * (z * x * z⁻¹) * z⁻¹⁻¹ := by rw [hzx]
      _ = x := by group
  refine ⟨V, ?_, hxV, ?_⟩
  · rw [hV]
    exact IsPGroup.to_sup_of_normal_right' (hz2 x hx) (hz2 y hy) hxN
  · rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨key z (hzx ▸ hyV) (hzy ▸ V.mul_mem hxV hyV) h, fun hh => ?_⟩
    have := key z⁻¹ (hzx' ▸ V.mul_mem hxV hyV) (hzy' ▸ hxV) _ hh
    simpa [mul_assoc] using this

theorem exists_klein_generators {F : Type} [Field F] [CharP F 3] {s : F} (hs : s ≠ 0) :
    ∃ x y : PSL(2, F), x * x = 1 ∧ y * y = 1 ∧ x * y = y * x ∧
      mk (unip s) * x * (mk (unip s))⁻¹ = y ∧ mk (unip s) * y * (mk (unip s))⁻¹ = x * y ∧
      x ∉ borel F := by
  have h3 : (3 : F) = 0 := by
    have := CharP.cast_eq_zero F 3
    exact_mod_cast this
  have hss : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  have hss' : s⁻¹ * s = 1 := inv_mul_cancel₀ hs
  obtain ⟨w, hw⟩ : ∃ w : SL(2, F), (w : Matrix (Fin 2) (Fin 2) F) = !![0, s; -s⁻¹, 0] :=
    ⟨⟨!![0, s; -s⁻¹, 0], by simp [Matrix.det_fin_two_of, hss]⟩, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : SL(2, F), (a : Matrix (Fin 2) (Fin 2) F) = !![1, s; s⁻¹, -1] :=
    ⟨⟨!![1, s; s⁻¹, -1], by rw [Matrix.det_fin_two_of]; linear_combination -hss - h3⟩, rfl⟩
  have hww : w * w = -1 := by
    apply SL_ext <;> simp [mul_apply_SL, neg_apply_SL, hw, hss, hss']
  have haa : a * a = -1 := by
    apply SL_ext <;> simp [mul_apply_SL, neg_apply_SL, ha, hss, hss'] <;> linear_combination h3
  have haw : a * w = -(w * a) := by
    apply SL_ext <;> simp [mul_apply_SL, neg_apply_SL, ha, hw]
  have huw : unip s * w * (unip s)⁻¹ = -a := by
    rw [unip_neg]
    apply SL_ext <;> simp [mul_apply_SL, neg_apply_SL, ha, hw, hss, hss']
    linear_combination s * h3
  have hua : unip s * a * (unip s)⁻¹ = -(w * a) := by
    rw [unip_neg]
    apply SL_ext <;> simp [mul_apply_SL, neg_apply_SL, ha, hw, hss, hss']
    · linear_combination h3
    · linear_combination -s * h3
    · linear_combination -h3
  refine ⟨mk w, mk a, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_mul, hww, mk_neg, map_one]
  · rw [← map_mul, haa, mk_neg, map_one]
  · rw [← map_mul, ← map_mul, haw, mk_neg]
  · rw [mk_conj, huw, mk_neg]
  · rw [mk_conj, hua, mk_neg, map_mul]
  · rw [mk_mem_borel_iff, mem_borelSL_iff]
    simp [hw, hs]

theorem exists_klein_normalized_psl2 {F : Type} [Field F] [CharP F 3] {s : F} (hs : s ≠ 0) :
    ∃ V : Subgroup PSL(2, F), IsPGroup 2 V ∧
      mk (unip s) ∈ Subgroup.normalizer (V : Set PSL(2, F)) ∧ ¬ V ≤ borel F := by
  obtain ⟨x, y, hx, hy, hxy, hzx, hzy, hxB⟩ := exists_klein_generators hs
  obtain ⟨V, hV, hxV, hzV⟩ := exists_isPGroup_two_normalized_of_commute hx hy hxy hzx hzy
  exact ⟨V, hV, hzV, fun hVB => hxB (hVB hxV)⟩

theorem exists_isPGroup_two_normalized_of_mulEquiv {K H : Type*} [Group K] [Group H] (ψ : K ≃* H)
    {T : Subgroup K} {P : Subgroup H} (hTP : ∀ k, k ∈ T ↔ ψ k ∈ P) {u : K} {V₀ : Subgroup H}
    (hV₀ : IsPGroup 2 V₀) (hu : ψ u ∈ Subgroup.normalizer (V₀ : Set H))
    (hVP : ¬ V₀ ≤ Subgroup.normalizer (P : Set H)) :
    ∃ V : Subgroup K, IsPGroup 2 V ∧ u ∈ Subgroup.normalizer (V : Set K) ∧
      ¬ V ≤ Subgroup.normalizer (T : Set K) := by
  refine ⟨V₀.comap ψ.toMonoidHom, hV₀.comap_of_injective _ ψ.injective, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff] at hu ⊢
    intro h
    simpa only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, map_mul, map_inv] using hu (ψ h)
  · intro hle
    obtain ⟨x, hxV, hxP⟩ := IsConcreteLE.not_le_iff_exists.mp hVP
    apply hxP
    have hv : ψ.symm x ∈ V₀.comap ψ.toMonoidHom := by simpa using hxV
    have hvT := Subgroup.mem_normalizer_iff.mp (hle hv)
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have := hvT (ψ.symm y)
    rw [hTP, hTP] at this
    simpa [map_mul, map_inv] using this

theorem exists_isPGroup_two_normalized_not_le_normalizer {K : Type} [Group K] [Finite K] {n : ℕ}
    [Fact (Nat.Prime 3)] (hn : 1 ≤ n) (e : K ≃* CFSG.AGLEmbedding.PSL2GF 3 n) (T : Sylow 3 K)
    {u : K} (hu : u ∈ (T : Subgroup K)) (hu1 : u ≠ 1) :
    ∃ V : Subgroup K, IsPGroup 2 V ∧ u ∈ Subgroup.normalizer (V : Set K) ∧
      ¬ V ≤ Subgroup.normalizer ((T : Subgroup K) : Set K) := by
  have hF : ringChar (GaloisField 3 n) ≠ 2 := by
    rw [ringChar.eq (GaloisField 3 n) 3]
    norm_num
  obtain ⟨U, hU⟩ := CFSG.AGLEmbedding.exists_sylow_eq_unipotent_psl2GF (p := 3) (n := n)
    (by norm_num) hn
  have hes : Function.Surjective (e : K →* CFSG.AGLEmbedding.PSL2GF 3 n) := e.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (CFSG.AGLEmbedding.PSL2GF 3 n) U
    (T.mapSurjective hes)
  have hgU : ∀ x, x ∈ (T.mapSurjective hes : Subgroup (CFSG.AGLEmbedding.PSL2GF 3 n)) ↔
      g⁻¹ * x * g ∈ unipotent (GaloisField 3 n) := by
    intro x
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, hU]
    have : (MulAut.conj g)⁻¹ • x = g⁻¹ * x * g := by
      rw [MulAut.smul_def, ← map_inv, MulAut.conj_apply, inv_inv]
    rw [this]
  have hTP : ∀ k : K, k ∈ (T : Subgroup K) ↔ g⁻¹ * e k * g ∈ unipotent (GaloisField 3 n) := by
    intro k
    rw [← hgU, Sylow.coe_mapSurjective]
    exact (Subgroup.mem_map_iff_mem e.injective).symm
  let ψ : K ≃* CFSG.AGLEmbedding.PSL2GF 3 n := e.trans (MulAut.conj g⁻¹)
  have hψ : ∀ k, ψ k = g⁻¹ * e k * g := by
    intro k
    simp [ψ]
  obtain ⟨t, ht⟩ := (mem_unipotent_iff_exists _).mp ((hTP u).mp hu)
  have ht0 : t ≠ 0 := by
    rintro rfl
    apply hu1
    have h1 : g⁻¹ * e u * g = 1 := by rw [ht, unip_zero, map_one]
    have h2 : e u = 1 := by
      have := congrArg (fun y => g * y * g⁻¹) h1
      simpa [mul_assoc] using this
    exact e.injective (h2.trans (map_one e).symm)
  obtain ⟨V₀, hV₀, hzV₀, hV₀B⟩ := exists_klein_normalized_psl2 (F := GaloisField 3 n) ht0
  refine exists_isPGroup_two_normalized_of_mulEquiv ψ (P := unipotent (GaloisField 3 n))
    (fun k => by rw [hψ]; exact hTP k) hV₀ ?_ ?_
  · rw [hψ, ht]
    exact hzV₀
  · rwa [CFSG.AGLEmbedding.normalizer_unipotent_eq_borel hF]

end CFSG.LocalAnalysis.RankFourTheoremC
