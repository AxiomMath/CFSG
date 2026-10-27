module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank619Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank619Basic
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank619Thompson
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627L32Data
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank619L32

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family

variable {G : Type} [Group G] [Finite G] {M B H S K : Subgroup G} {z : G} {f : ↥K →* GL32}

private theorem excl_not_mem_Inn (h : Data619 M B H S K z f) (hV : K ⊓ S ≤ pCoreOf 2 H)
    {Φ : ↥S →* MulAut GL32}
    (hΦ : ∀ (n : ↥S) (k k' : ↥K), (k' : G) = (n : G) * (k : G) * (n : G)⁻¹ → Φ n (f k) = f k')
    {a : G} (haS : a ∈ S) (ha : a ∉ pCoreOf 2 H) : Φ ⟨a, haS⟩ ∉ L32Insp.Inn := by
  intro hmem
  obtain ⟨k, hk, o, ho, hao⟩ := h.exists_mul_of_mem_sup haS (h.mem_sup_of_mem_Inn hΦ hmem)
  exact ha (hao ▸ mul_mem (hV hk) ho)

private theorem excl_inv_mul_mem (h : Data619 M B H S K z f) (hV : K ⊓ S ≤ pCoreOf 2 H)
    {Φ : ↥S →* MulAut GL32}
    (hΦ : ∀ (n : ↥S) (k k' : ↥K), (k' : G) = (n : G) * (k : G) * (n : G)⁻¹ → Φ n (f k) = f k')
    {a b : G} (haS : a ∈ S) (hbS : b ∈ S) (ha : a ∉ pCoreOf 2 H) (hb : b ∉ pCoreOf 2 H) :
    a⁻¹ * b ∈ pCoreOf 2 H := by
  by_contra hab
  refine excl_not_mem_Inn h hV hΦ (a := a⁻¹ * b) (mul_mem (inv_mem haS) hbS) hab ?_
  have : (⟨a⁻¹ * b, mul_mem (inv_mem haS) hbS⟩ : ↥S) = (⟨a, haS⟩ : ↥S)⁻¹ * ⟨b, hbS⟩ := rfl
  rw [this, map_mul, map_inv, Subgroup.mul_mem_iff_of_index_two L32Insp.index_Inn, inv_mem_iff]
  simp [excl_not_mem_Inn h hV hΦ haS ha, excl_not_mem_Inn h hV hΦ hbS hb]

private theorem excl_mul_self_mem (h : Data619 M B H S K z f) (hV : K ⊓ S ≤ pCoreOf 2 H)
    {Φ : ↥S →* MulAut GL32}
    (hΦ : ∀ (n : ↥S) (k k' : ↥K), (k' : G) = (n : G) * (k : G) * (n : G)⁻¹ → Φ n (f k) = f k')
    {a : G} (haS : a ∈ S) : a * a ∈ pCoreOf 2 H := by
  by_contra hne
  refine excl_not_mem_Inn h hV hΦ (a := a * a) (mul_mem haS haS) hne ?_
  have : (⟨a * a, mul_mem haS haS⟩ : ↥S) = (⟨a, haS⟩ : ↥S) * ⟨a, haS⟩ := rfl
  rw [this, map_mul]
  exact Subgroup.mul_self_mem_of_index_two L32Insp.index_Inn _

private theorem excl_phi_mul_self (h : Data619 M B H S K z f) (hV : K ⊓ S ≤ pCoreOf 2 H)
    {Φ : ↥S →* MulAut GL32}
    (hΦ : ∀ (n : ↥S) (k k' : ↥K), (k' : G) = (n : G) * (k : G) * (n : G)⁻¹ → Φ n (f k) = f k')
    {a : G} (haS : a ∈ S) : Φ ⟨a, haS⟩ * Φ ⟨a, haS⟩ = 1 := by
  rw [← map_mul]
  exact h.phi_eq_one_of_mem_core hΦ (a := ⟨a, haS⟩ * ⟨a, haS⟩) (excl_mul_self_mem h hV hΦ haS)

private theorem excl_exists_abelian (h : Data619 M B H S K z f) :
    ∃ A ∈ CFSG.thompsonAbelianSubgroups S, ¬ A ≤ pCoreOf 2 H := by
  by_contra hcon
  have hN := normalizer_le_normalizer_thompsonSubgroup h.core_le
    (fun A hA => by_contra fun hA' => hcon ⟨A, hA, hA'⟩)
  exact h.K_not_le (h.K_le.trans (h.eq_normalizer.le.trans (hN.trans
    (h.char_le _ (thompsonSubgroup_le' S) (thompsonSubgroup_ne_bot h.S_ne_bot)
      (thompsonSubgroup_characteristic S)))))

private theorem excl_le_normalizer (h : Data619 M B H S K z f) :
    H ≤ normalizer (omegaCenter (pCoreOf 2 H) : Set G) :=
  h.eq_normalizer.le.trans (normalizer_le_normalizer_omegaCenter _)

omit [Finite G] in
private theorem excl_core_le_centralizer (H : Subgroup G) :
    pCoreOf 2 H ≤ centralizer (omegaCenter (pCoreOf 2 H) : Set G) := fun o ho =>
  mem_centralizer_iff.2 fun _ hv =>
    (mem_centralizer_iff.1 (omegaCenter_le_centralizer _ hv) o ho).symm

private theorem excl_not_le_centralizer (h : Data619 M B H S K z f) :
    ¬ K ≤ centralizer (omegaCenter (pCoreOf 2 H) : Set G) := by
  intro hKC
  have hSO : S ⊓ centralizer (pCoreOf 2 H : Set G) ≤ pCoreOf 2 H := fun x hx =>
    h.charTwo H h.twoLocal ⟨h.maxInv.1.1 hx.1, hx.2⟩
  have hle : omegaCenter S ≤ omegaCenter (pCoreOf 2 H) := omegaCenter_le_omegaCenter h.core_le hSO
  refine h.K_not_le fun k hk => h.char_le (omegaCenter S) (omegaCenter_le S)
    (omegaCenter_ne_bot h.maxInv.1.2.1 h.S_ne_bot) (omegaCenter_characteristic S) ?_
  exact centralizer_le_normalizer _
    (mem_centralizer_iff.2 fun v hv => mem_centralizer_iff.1 (hKC hk) v (hle hv))

private theorem excl_inf_centralizer_normal (h : Data619 M B H S K z f) :
    ((K ⊓ centralizer (omegaCenter (pCoreOf 2 H) : Set G)).subgroupOf K).Normal := by
  rw [normal_subgroupOf_iff inf_le_left]
  intro g k hg hk
  refine ⟨K.mul_mem (K.mul_mem hk hg.1) (K.inv_mem hk), mem_centralizer_iff.2 fun v hv => ?_⟩
  have hv' : k⁻¹ * v * k ∈ omegaCenter (pCoreOf 2 H) := by
    rw [mem_normalizer_iff.1 (excl_le_normalizer h (h.K_le hk)) (k⁻¹ * v * k)]
    have e : k * (k⁻¹ * v * k) * k⁻¹ = v := by group
    rwa [e]
  have hc := mem_centralizer_iff.1 hg.2 _ hv'
  calc v * (k * g * k⁻¹) = k * (k⁻¹ * v * k * g) * k⁻¹ := by group
    _ = k * (g * (k⁻¹ * v * k)) * k⁻¹ := by rw [hc]
    _ = k * g * k⁻¹ * v := by group

private theorem excl_inf_centralizer_le (h : Data619 M B H S K z f) :
    K ⊓ centralizer (omegaCenter (pCoreOf 2 H) : Set G) ≤ pCoreOf 2 H := by
  rcases h.K_simple _ inf_le_left (excl_inf_centralizer_normal h)
    (le_inf inf_le_left ((inf_le_right).trans (excl_core_le_centralizer H))) with h1 | h1
  · exact h1.le.trans inf_le_right
  · exact absurd (h1 ▸ inf_le_right) (excl_not_le_centralizer h)

private theorem excl_final (h : Data619 M B H S K z f) {κ : ↥K} (hord : orderOf (f κ) = 7)
    (h12 : (κ : G) ^ 12 ∈ centralizer (omegaCenter (pCoreOf 2 H) : Set G)) : False := by
  have h7 : (κ : G) ^ 7 ∈ centralizer (omegaCenter (pCoreOf 2 H) : Set G) := by
    have h1 : f (κ ^ 7) = 1 := by
      rw [map_pow]
      simpa [hord] using pow_orderOf_eq_one (f κ)
    simpa using excl_core_le_centralizer H ((h.f_ker _).1 h1)
  have hnot : (κ : G) ∉ centralizer (omegaCenter (pCoreOf 2 H) : Set G) := fun hc => by
    have h1 := (h.f_ker κ).2 (excl_inf_centralizer_le h ⟨κ.2, hc⟩)
    rw [h1, orderOf_one] at hord
    omega
  refine hnot ?_
  have e : (κ : G) = ((κ : G) ^ 12) ^ 3 * (((κ : G) ^ 7) ^ 5)⁻¹ := by group
  rw [e]
  exact mul_mem (pow_mem h12 3) (inv_mem (pow_mem h7 5))

theorem Data619.false_of_inf_le (h : Data619 M B H S K z f) (hV : K ⊓ S ≤ pCoreOf 2 H) :
    False := by
  obtain ⟨Φ, hΦ⟩ := h.exists_phi
  obtain ⟨A, hA, hAO⟩ := excl_exists_abelian h
  obtain ⟨a, haA, hao⟩ := IsConcreteLE.not_le_iff_exists.1 hAO
  have haS : a ∈ S := hA.1 haA
  have hVelem := isElemAbelian_omegaCenter (pCoreOf 2 H)
  have haN := excl_le_normalizer h (h.maxInv.1.1 haS)
  obtain ⟨w, hw, hgw⟩ := exists_small_of_mem_thompsonAbelianSubgroups hA
    ((omegaCenter_le _).trans h.core_le) hVelem (omegaCenter_le_centralizer _)
    (fun a ha a' ha' h1 h2 => excl_inv_mul_mem h hV hΦ (hA.1 ha) (hA.1 ha') h1 h2) haA haN
  obtain ⟨q, hq⟩ := L32Insp.exists_orderOf_eq_seven_of_not_mem_Inn
    (excl_not_mem_Inn h hV hΦ haS hao) (excl_phi_mul_self h hV hΦ haS)
  obtain ⟨k, rfl⟩ := h.f_surj q
  have hk' : a * (k : G) * a⁻¹ ∈ K :=
    (mem_normalizer_iff.1 (h.K_normal (h.maxInv.1.1 haS)) _).1 k.2
  have hfk' : Φ ⟨a, haS⟩ (f k) = f ⟨a * (k : G) * a⁻¹, hk'⟩ := hΦ ⟨a, haS⟩ k _ rfl
  have hκ : (((⟨a * (k : G) * a⁻¹, hk'⟩ : ↥K)⁻¹ * k : ↥K) : G) = a * (k : G)⁻¹ * a⁻¹ * k := by
    show (a * (k : G) * a⁻¹)⁻¹ * (k : G) = _
    group
  refine excl_final h (κ := (⟨a * (k : G) * a⁻¹, hk'⟩ : ↥K)⁻¹ * k) ?_ ?_
  · rwa [map_mul, map_inv, ← hfk']
  · have hVc : ∀ v ∈ omegaCenter (pCoreOf 2 H), ∀ v' ∈ omegaCenter (pCoreOf 2 H),
        v * v' = v' * v := by
      have := hVelem.1
      exact fun v hv v' hv' => setLike_mul_comm hv hv'
    have hg2 : a ^ 2 ∈ centralizer (omegaCenter (pCoreOf 2 H) : Set G) := by
      rw [pow_two]
      exact excl_core_le_centralizer H (excl_mul_self_mem h hV hΦ haS)
    have h12 := pow_twelve_mem_centralizer_of_small hVc hVelem.2 haN
      (excl_le_normalizer h (h.K_le k.2)) hg2 hw hgw
    rwa [← hκ] at h12

end CFSG.LocalAnalysis.RankThreeTheoremC
