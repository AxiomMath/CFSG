module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Case2Setup
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Case2Odd
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6Struct
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerRank
import CFSG.Quasithin.Background.B2Factorization

@[expose] public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.ABGLocalTools CFSG.Quasithin Subgroup GL83P3A6Aux GL83P3A6Core

theorem edge_of_inV {G : Type} [Group G] [Finite G] {M O : Subgroup G} {x e₂ e₃ t ρ : G}
    {s : ℤ} (hf : A6VIFrame M O x e₂ e₃ t ρ s) {U J : Subgroup G} (hU9 : Nat.card U = 9)
    (hxU : x ∈ U)
    (hδ : ∀ g : G, (zpowers x).map (MulAut.conj g).toMonoidHom ≠ U ⊓ J) (he₂J : e₂ ∈ J)
    (he₃J : e₃ ∈ J) (hxJ : x ∉ J) :
    ∀ u ∈ U, (u ∈ zpowers x ∨ u ∈ zpowers e₂ ∨ u ∈ zpowers e₃) → u ∈ zpowers x := by
  have key : ∀ ℓ g : G, ℓ ^ 3 = 1 → ℓ ≠ 1 → ℓ ∈ J → ℓ ∈ U → g * x * g⁻¹ = ℓ → False := by
    intro ℓ g hℓ3 hℓ1 hℓJ hℓU hg
    have hle : zpowers ℓ ≤ U ⊓ J := le_inf (zpowers_le.mpr hℓU) (zpowers_le.mpr hℓJ)
    have hcardU : Nat.card (U ⊓ J : Subgroup G) ∣ 3 ^ 2 := by
      have := Subgroup.card_dvd_of_le (inf_le_left : U ⊓ J ≤ U)
      rwa [hU9] at this
    have hℓ3' : Nat.card (zpowers ℓ) = 3 := by rw [Nat.card_zpowers, orderOf_eq_prime hℓ3 hℓ1]
    have hge : 3 ≤ Nat.card (U ⊓ J : Subgroup G) := by
      have := Subgroup.card_le_of_le hle
      rwa [hℓ3'] at this
    have hne9 : Nat.card (U ⊓ J : Subgroup G) ≠ 9 := by
      intro h9
      have hUJ : U ⊓ J = U := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h9, hU9])
      have hx : x ∈ U ⊓ J := by rw [hUJ]; exact hxU
      exact hxJ hx.2
    have h3 : Nat.card (U ⊓ J : Subgroup G) = 3 := by
      obtain ⟨i, hi, hcard⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hcardU
      interval_cases i
      · omega
      · simpa using hcard
      · exact absurd (by simpa using hcard) hne9
    have heq : U ⊓ J = zpowers ℓ :=
      (Subgroup.eq_of_le_of_card_ge hle (by rw [h3, hℓ3'])).symm
    apply hδ g
    rw [MonoidHom.map_zpowers]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hg, heq]
  intro u hu hline
  rcases hline with h | h | h
  · exact h
  · by_cases hu1 : u = 1
    · rw [hu1]; exact one_mem _
    have hzp : zpowers u = zpowers e₂ := zpowers_eq_of_mem hf.e₂_pow hf.e₂_ne h hu1
    have he₂U : e₂ ∈ U := (zpowers_le.mpr hu) (by rw [hzp]; exact mem_zpowers e₂)
    exact (key e₂ t hf.e₂_pow hf.e₂_ne he₂J he₂U hf.t_x).elim
  · by_cases hu1 : u = 1
    · rw [hu1]; exact one_mem _
    have hzp : zpowers u = zpowers e₃ := zpowers_eq_of_mem hf.e₃_pow hf.e₃_ne h hu1
    have he₃U : e₃ ∈ U := (zpowers_le.mpr hu) (by rw [hzp]; exact mem_zpowers e₃)
    exact (key e₃ (t * t) hf.e₃_pow hf.e₃_ne he₃J he₃U hf.e₃_eq.symm).elim

theorem odd_conj {G : Type} [Group G] {M O : Subgroup G} (hOn : M ≤ normalizer (O : Set G))
    {ℓ ℓ' τ : G} (hτ : τ ∈ M) (hℓ' : τ * ℓ * τ⁻¹ = ℓ')
    (h : ∀ w ∈ O, w ^ 2 = 1 → w * ℓ = ℓ * w → w = 1) :
    ∀ w ∈ O, w ^ 2 = 1 → w * ℓ' = ℓ' * w → w = 1 := by
  intro w hwO hw2 hwc
  have hw' : τ⁻¹ * w * τ ∈ O := by
    have := (mem_normalizer_iff.mp (hOn (M.inv_mem hτ)) w).mp hwO
    simpa using this
  have hw'2 : (τ⁻¹ * w * τ) ^ 2 = 1 := by
    have e : (τ⁻¹ * w * τ) ^ 2 = τ⁻¹ * w ^ 2 * τ := by rw [pow_two, pow_two]; group
    rw [e, hw2]
    group
  have hcomm : (τ⁻¹ * w * τ) * ℓ = ℓ * (τ⁻¹ * w * τ) := by
    rw [← hℓ'] at hwc
    calc τ⁻¹ * w * τ * ℓ = τ⁻¹ * (w * (τ * ℓ * τ⁻¹)) * τ := by group
      _ = τ⁻¹ * ((τ * ℓ * τ⁻¹) * w) * τ := by rw [hwc]
      _ = ℓ * (τ⁻¹ * w * τ) := by group
  have h1 := h _ hw' hw'2 hcomm
  have : w = τ * (τ⁻¹ * w * τ) * τ⁻¹ := by group
  rw [this, h1]
  group

def A6VICase2Layer (G : Type) [Group G] [Finite G] : Prop :=
  GenericA6At G fun p P M x J => A6Prop34S p P J x →
    ¬ LineWeaklyClosed x ((P : Subgroup G) ⊓ centralizer ({x} : Set G)) →
    ¬ (∀ m ∈ M, ∀ q ∈ (P : Subgroup G) ⊓ J, m * q * m⁻¹ ∈ (P : Subgroup G) ⊔ GLBPrimeCore p M) →
    ∀ U : Subgroup G, A6InV p P J x U → ∀ Y : Subgroup G, IsPGroup 2 Y → Y ≤ M →
      U ≤ normalizer (Y : Set G) → IsSylowOf 2 (Y ⊓ GLBPrimeCore p M) (GLBPrimeCore p M) →
      ¬ Y ≤ normalizer
        ((((P : Subgroup G) ⊓ centralizer ({x} : Set G)) ⊔ GLBPrimeCore p M : Subgroup G) :
          Set G) →
      (∀ Y₀ : Subgroup G, Y₀ ≤ Y → Y₀ ≠ ⊥ → (Y₀.subgroupOf Y).Characteristic →
        CFSG.Open.pRank p (normalizer (Y₀ : Set G) ⊓ M) < 3) →
      ∃ (hx : x ∈ M) (hN : ((GLBPrimeCore p M).subgroupOf M).Normal),
        @LayerOut G _ M (GLBPrimeCore p M) hN ((P : Subgroup G) ⊓ centralizer ({x} : Set G)) x hx

theorem a6VICase2_of_layer (h2811 : KFact2811) (hLe8 : KFactPSp43ElemLe8)
    (h2sub : KFactPSp43TwoSubgroups) (hKA : KFactA6TwoNormalized) {G : Type} [Group G] [Finite G]
    (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G) (hLayer : A6VICase2Layer G) :
    A6VICase2 G := by
  intro p hp P M hM hfail hIH x hgen hp3 J hJC hCJ hperf hlt hmin hnot Q _ ψ hψ hker hQ h34 hnwc
    hC1 U hU Y hY2 hYM hUY hYO hYN hbig
  subst hp3
  have hJ : IsA6Normal M x J :=
    ⟨hJC, hCJ, hperf, hnot, hlt, hmin, Q, inferInstance, ψ, hψ, hker, hQ⟩
  obtain ⟨hxM, hN, hL⟩ := hLayer 3 hp P M hM hfail hIH x hgen rfl J hJC hCJ hperf hlt hmin hnot Q
    ψ hψ hker hQ h34 hnwc hC1 U hU Y hY2 hYM hUY hYO hYN hbig
  haveI := hN
  obtain ⟨e₂, e₃, t, ρ, s, hf, hQeq, -, -⟩ := a6vi_frame hS hU0 hD1 hp hM hgen hJ h34 hnwc
  have hUQ : U ≤ Qf x e₂ e₃ := hQeq ▸ hU.1
  have hU9 : Nat.card U = 9 := by simpa using hU.2.2.1
  have hxU : x ∈ U := hU.2.2.2.1
  have hfus := h34.1.2.2
  have hxe : ∀ ℓ g : G, g * x * g⁻¹ = ℓ → ℓ ∉ zpowers x → ℓ ∈ Qf x e₂ e₃ → ℓ ∈ J := by
    intro ℓ g hg hℓx hℓQ
    have hle : (zpowers x).map (MulAut.conj g).toMonoidHom ≤
        (P : Subgroup G) ⊓ centralizer ({x} : Set G) := by
      rw [← hQeq, MonoidHom.map_zpowers]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [hg]
      exact zpowers_le.mpr hℓQ
    rcases hfus g hle with h | h
    · exfalso
      apply hℓx
      rw [← h, MonoidHom.map_zpowers]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [hg]
      exact mem_zpowers ℓ
    · rw [MonoidHom.map_zpowers] at h
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
      rw [hg] at h
      exact (zpowers_le.mp h)
  have h2Q : e₂ ∈ Qf x e₂ e₃ := mem_sup_right (mem_sup_left (mem_zpowers e₂))
  have h3Q : e₃ ∈ Qf x e₂ e₃ := mem_sup_right (mem_sup_right (mem_zpowers e₃))
  have he₂x : e₂ ∉ zpowers x := fun h => hf.e₂_ne (by
    have : e₂ ∈ (zpowers e₂ ⊔ zpowers e₃) ⊓ zpowers x :=
      ⟨mem_sup_left (mem_zpowers e₂), h⟩
    rw [hf.ind_x] at this
    exact mem_bot.mp this)
  have he₃x : e₃ ∉ zpowers x := fun h => hf.e₃_ne (by
    have : e₃ ∈ (zpowers e₂ ⊔ zpowers e₃) ⊓ zpowers x :=
      ⟨mem_sup_right (mem_zpowers e₃), h⟩
    rw [hf.ind_x] at this
    exact mem_bot.mp this)
  have he₂J : e₂ ∈ J := hxe e₂ t hf.t_x he₂x h2Q
  have he₃J : e₃ ∈ J := hxe e₃ (t * t) hf.e₃_eq.symm he₃x h3Q
  have hxJ : x ∉ J := a6_x_not_mem_J hS hU0 hp hM hgen hJ
  have hedgeU := edge_of_inV hf hU9 hxU hU.2.2.2.2 he₂J he₃J hxJ
  have hYne : Y ≠ ⊥ := by
    rintro rfl
    exact hYN (fun y hy => by rw [(Subgroup.mem_bot.mp hy)]; exact one_mem _)
  have hJY : ¬ ∃ E : Subgroup G, E ≤ normalizer ((thompsonJ Y : Subgroup G) : Set G) ⊓ M ∧
      IsElemAbelian 3 E ∧ Nat.card E = 27 := by
    rintro ⟨E, hEle, hEel, hE27⟩
    have hfact : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h3 : 3 ≤ CFSG.Open.pRank 3 (normalizer ((thompsonJ Y : Subgroup G) : Set G) ⊓ M) :=
      le_pRank_of_elemAbelian_card (p := 3) (k := 3) hEle hEel (by rw [hE27]; norm_num)
    exact absurd (hbig (thompsonJ Y) (thompsonJ_le_self Y)
      (GL83P3A6Setup.thompsonJ_ne_bot hY2 hYne)
      (CFSG.QuasithinUnique.Setup.characteristic_thompsonJ Y)) (not_lt.mpr h3)
  have hodd₁ := a6_odd_involution hS hD1 hU0 hKA hp hM hgen hJ
  have hOn : M ≤ normalizer ((GLBPrimeCore 3 M : Subgroup G) : Set G) := hf.O_norm
  have hodd₂ := odd_conj hOn hf.t_mem hf.t_x hodd₁
  have hodd₃ := odd_conj hOn hf.t_mem hf.t_e₂ hodd₂
  have hodd : ∀ ℓ, (ℓ = x ∨ ℓ = e₂ ∨ ℓ = e₃) → ∀ w ∈ GLBPrimeCore 3 M, w ^ 2 = 1 →
      w * ℓ = ℓ * w → w = 1 := by
    rintro ℓ (h | h | h)
    · rw [h]; exact hodd₁
    · rw [h]; exact hodd₂
    · rw [h]; exact hodd₃
  have hYN' : ¬ Y ≤ normalizer ((Qf x e₂ e₃ ⊔ GLBPrimeCore 3 M : Subgroup G) : Set G) := by
    rw [hQeq]
    exact hYN
  obtain ⟨t', ρ', Y', U', x', hd⟩ := GL83P3A6Setup.exists_coreData hf hY2 hYM hYO hUQ hU9 hxU hUY
    hedgeU hYN' hJY hodd
  refine hd.false h2811 hLe8 h2sub ?_
  rw [hQeq]
  exact hL

theorem gl83P3A6_holds_of_layer (h2811 : KFact2811) (hLe8 : KFactPSp43ElemLe8)
    (h2sub : KFactPSp43TwoSubgroups) (hKA : KFactA6TwoNormalized) :
    ∀ (G : Type) [Group G] [Finite G], Setting G → TheoremD1 G → FullCoreLocal G →
      A6VICase2Layer G → GL83GenericPrimeThreeA6Lemma43VI G :=
  fun _ _ _ hS hD1 hU0 hLayer =>
    gl83P3A6_of_case2 hS hD1 hU0 (a6VICase2_of_layer h2811 hLe8 h2sub hKA hS hD1 hU0 hLayer)

end CFSG.LocalAnalysis.RankThreeTheoremC
