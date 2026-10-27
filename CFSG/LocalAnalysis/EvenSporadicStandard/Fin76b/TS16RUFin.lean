module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RUEmb
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RUKs2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RUInv
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RUG1
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RUG2

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Sporadic.SmallOddCore CFSG.EvenSporadicStandard.M24Std.CU43
  CFSG.EvenSporadicStandard.Fin76b.U16

section Basic


theorem invIx_seven : invIx 7 = 7 := by decide

theorem mem_U43Ext_iff_cos {x : Equiv.Perm (Fin 820)} : x ∈ U43Ext ↔ InCos 0 x ∨ InCos 5 x := by
  constructor
  · intro hx
    rcases mem_U43Ext_iff.1 hx with hP | ⟨g, hg, rfl⟩
    · exact Or.inl (inCos_zero_iff.2 hP)
    · obtain ⟨g₀, hg₀, hρ⟩ := rho_coset
      exact Or.inr (inCos_iff.2 ⟨g * g₀, P.mul_mem hg hg₀, by rw [hρ]; group⟩)
  · rintro (h | h)
    · exact P_le_U43Ext (inCos_zero_iff.1 h)
    · obtain ⟨g, hg, rfl⟩ := inCos_iff.1 h
      obtain ⟨g₀, hg₀, hρ⟩ := rho_coset
      have e : g * tP 5 = (g * g₀⁻¹) * rhoPerm := by rw [hρ]; group
      rw [e]
      exact U43Ext.mul_mem (P_le_U43Ext (P.mul_mem hg (P.inv_mem hg₀))) rho_mem_U43Ext

end Basic

theorem beta_inv_ne {G : Type} [Group G] {β : G} (hβ3 : orderOf β = 3) : β⁻¹ ≠ β := by
  intro h
  have h2 : β ^ 2 = 1 := by
    rw [pow_two]
    calc β * β = β⁻¹ * β := by rw [h]
      _ = 1 := inv_mul_cancel β
  have := orderOf_dvd_of_pow_eq_one h2
  rw [hβ3] at this
  omega

theorem not_mem_cent_of_inv {G : Type} [Group G] {β g : G} (hβ3 : orderOf β = 3)
    (h : g * β * g⁻¹ = β⁻¹) : g ∉ centralizer ({β} : Set G) := by
  intro hg
  have h1 := mem_centralizer_singleton_iff.1 hg
  apply beta_inv_ne hβ3
  rw [← h]
  calc g * β * g⁻¹ = β * g * g⁻¹ := by rw [h1]
    _ = β := by group

section Context

variable
  {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G} {Q : Sylow 2 G}
  {x : G} {B : Subgroup G} {β : G} {S : Subgroup G}

namespace OuterS16Ctx

variable (c : OuterS16Ctx G L z t T E Q x B β S) (Em : KEmb G β)
  (hDP : ∀ d ∈ L ⊓ centralizer ({β} : Set G), Em.f d ∈ P)

include c Em hDP

theorem coset_vxi {σ v ξ : G} (hD : S16LData G L z t β E σ v ξ) :
    InCos 7 (Em.f v) ∧ InCos 7 (Em.f ξ) ∧ orderOf (Em.f v) = 8 ∧ Em.f ξ * Em.f ξ = 1 ∧
      Em.f ξ * Em.f v = (Em.f v)⁻¹ * Em.f ξ ∧ Em.f v ∈ U43ExtStar ∧ Em.f ξ ∈ U43ExtStar := by
  have hcfg := c.hyp.outerE.cfg
  have hβ3 : orderOf β = 3 := c.hyp.outerB.beta_order
  have hvK : v ∈ Kst β := mem_normalizer_zpowers_of_conj (Or.inr hD.v_β)
  have hξK : ξ ∈ Kst β := mem_normalizer_zpowers_of_conj (Or.inr hD.ξ_β)
  have hv_notK : v ∉ centralizer ({β} : Set G) := not_mem_cent_of_inv hβ3 hD.v_β
  have hv8 : orderOf v = 8 := by
    have h8 : orderOf v = 2 ^ (2 + 1) := by
      refine orderOf_eq_prime_pow (p := 2) ?_ ?_
      · intro h
        apply hcfg.t_ne
        rw [← hD.v4]
        simpa using h
      · simpa using hD.v8
    simpa using h8
  obtain ⟨P64, hP2, hPn, hSP, hvP, hPc, hPcard⟩ := c.exists_cent_64_v hD
  obtain ⟨R, hRKs, hR2, ⟨eR⟩, hfR, hRf⟩ := Em.exists_image hP2 hPn
  have hRcard : Nat.card ↥R = 64 := by rw [← Nat.card_congr eR.toEquiv, hPcard]
  have hfv_ord : orderOf (Em.f v) = 8 := by rw [Em.orderOf_f hP2 hPn hvP, hv8]
  have hRc : ∀ r ∈ R, r * Em.f v = Em.f v * r := by
    intro r hr
    obtain ⟨g, hg, rfl⟩ := hRf r hr
    have h1 := mem_centralizer_singleton_iff.1 (hPc hg)
    rw [← Em.mul g (hPn hg) v (hPn hvP), ← Em.mul v (hPn hvP) g (hPn hg), h1]
  have hfvKs : Em.f v ∈ U43ExtStar := Em.mem v hvK
  have h2 := (ks_cent8_two_le hfvKs hfv_ord hRKs hRc hR2).2
  obtain ⟨k, hk8, hkV, hkc⟩ := mem_Ks_iff.1 hfvKs
  have hnotKb : Em.f v ∉ U43Ext := fun h => hv_notK ((Em.inner v hvK).2 h)
  have hk7 : InCos 7 (Em.f v) := by
    rcases hkV with rfl | rfl | rfl | rfl
    · exact absurd (mem_U43Ext_iff_cos.2 (Or.inl hkc)) hnotKb
    · exfalso
      have := h2 hkc
      omega
    · exact absurd (mem_U43Ext_iff_cos.2 (Or.inr hkc)) hnotKb
    · exact hkc
  have hvξ : v * ξ ∈ L ⊓ centralizer ({β} : Set G) := by
    refine ⟨mul_mem hD.v_L hD.ξ_L, mem_centralizer_singleton_iff.2 ?_⟩
    calc v * ξ * β = v * (ξ * β * ξ⁻¹) * ξ := by group
      _ = v * β⁻¹ * ξ := by rw [hD.ξ_β]
      _ = (v * β⁻¹ * v⁻¹) * (v * ξ) := by group
      _ = β * (v * ξ) := by
        have : v * β⁻¹ * v⁻¹ = β := by
          have h1 : v * β⁻¹ * v⁻¹ = (v * β * v⁻¹)⁻¹ := by group
          rw [h1, hD.v_β, inv_inv]
        rw [this]
  have hfvξ : Em.f (v * ξ) ∈ P := hDP _ hvξ
  have hmul : Em.f (v * ξ) = Em.f v * Em.f ξ := Em.mul v hvK ξ hξK
  have hfξeq : Em.f ξ = (Em.f v)⁻¹ * Em.f (v * ξ) := by rw [hmul]; group
  have hξ7 : InCos 7 (Em.f ξ) := by
    have h1 := inCos_inv (by norm_num : 7 < 8) hk7
    have h2 := inCos_mul (invIx_spec 7 (by norm_num)).1 (by norm_num : 0 < 8) h1
      (inCos_zero_iff.2 hfvξ)
    rw [invIx_seven] at h2
    have h3 : mulTab 7 0 = 7 := by decide
    rw [h3, ← hfξeq] at h2
    exact h2
  refine ⟨hk7, hξ7, hfv_ord, ?_, ?_, hfvKs, Em.mem ξ hξK⟩
  · rw [← Em.mul ξ hξK ξ hξK, show ξ * ξ = 1 from hD.ξ_sq, Em.one]
  · have hrel : ξ * v = v⁻¹ * ξ := by
      have := hD.ξ_v
      calc ξ * v = ξ * v * ξ⁻¹ * ξ := by group
        _ = v⁻¹ * ξ := by rw [this]
    rw [← Em.mul ξ hξK v hvK, hrel, Em.mul _ ((Kst β).inv_mem hvK) ξ hξK, Em.inv hvK]

theorem S_dih {σ v ξ : G} (hD : S16LData G L z t β E σ v ξ) :
    Nonempty (↥S ≃* DihedralGroup 8) := by
  obtain ⟨hv7, hξ7, hv8, hξ2, hrel, hvKs, hξKs⟩ := c.coset_vxi Em hDP hD
  have hβ3 : orderOf β = 3 := c.hyp.outerB.beta_order
  have hSK : ∀ s ∈ S, s * β = β * s := fun s hs => (c.BS β c.hyp.outerB.beta_mem s hs).symm
  have hSKst : S ≤ Kst β := fun s hs => cent_le_Kst β (mem_centralizer_singleton_iff.2 (hSK s hs))
  obtain ⟨R, hRKs, hR2, ⟨eR⟩, hfR, hRf⟩ := Em.exists_image c.S2 hSKst
  have hRcard : Nat.card ↥R = 16 := by rw [← Nat.card_congr eR.toEquiv, c.card16]
  have hvEB : v ∈ L ⊓ centralizer ({t} : Set G) :=
    ⟨hD.v_L, mem_centralizer_singleton_iff.2 hD.v_t⟩
  have hξEB : ξ ∈ L ⊓ centralizer ({t} : Set G) :=
    ⟨hD.ξ_L, mem_centralizer_singleton_iff.2 hD.ξ_t⟩
  have hvK : v ∈ Kst β := mem_normalizer_zpowers_of_conj (Or.inr hD.v_β)
  have hξK : ξ ∈ Kst β := mem_normalizer_zpowers_of_conj (Or.inr hD.ξ_β)
  have hc1 : ∀ r ∈ R, r * Em.f v = Em.f v * r := by
    intro r hr
    obtain ⟨g, hg, rfl⟩ := hRf r hr
    have h1 := mem_centralizer_iff.1 (c.EB_le_centS hvEB) g hg
    rw [← Em.mul g (hSKst hg) v hvK, ← Em.mul v hvK g (hSKst hg), h1]
  have hc2 : ∀ r ∈ R, r * Em.f ξ = Em.f ξ * r := by
    intro r hr
    obtain ⟨g, hg, rfl⟩ := hRf r hr
    have h1 := mem_centralizer_iff.1 (c.EB_le_centS hξEB) g hg
    rw [← Em.mul g (hSKst hg) ξ hξK, ← Em.mul ξ hξK g (hSKst hg), h1]
  obtain ⟨e⟩ := ks_pair_D16 hvKs hv8 hv7 hξKs hξ2 hξ7 hrel hRKs hc1 hc2 hRcard
  exact ⟨eR.trans e⟩

omit Em hDP in
theorem exists_S16Gen (e : ↥S ≃* DihedralGroup 8) : ∃ s : G, S16Gen S s z t := by
  have hcfg := c.hyp.outerE.cfg
  obtain ⟨s, hsS, hs8, hzs, hs4, hgen⟩ := exists_dihedral_gen e c.zS c.t_mem_S hcfg.z_sq hcfg.z_ne
    hcfg.z_ne_t hcfg.t_sq hcfg.t_ne c.t_comm_S
  refine ⟨s, ⟨hsS, c.zS, ?_, hs4, hcfg.z_sq, hzs, hs8, ?_, hgen⟩⟩
  · have := pow_orderOf_eq_one s
    rwa [hs8] at this
  · intro hz
    have hcomm : z * s = s * z := by
      obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hz
      rw [← hk]
      exact (Commute.zpow_self s k).eq
    have h1 : s⁻¹ = s := by
      rw [← hzs, hcomm]
      group
    have h2 : s ^ 2 = 1 := by
      rw [pow_two]
      calc s * s = s⁻¹ * s := by rw [h1]
        _ = 1 := inv_mul_cancel s
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hs8] at this
    omega

omit c hDP in
theorem no_cent_128 {s : G} (h8 : orderOf s = 8) {P : Subgroup G} (hP2 : IsPGroup 2 P)
    (hPn : P ≤ Kst β) (hsP : s ∈ P) (hPc : P ≤ centralizer ({s} : Set G))
    (hcard : Nat.card ↥P = 128) : False := by
  obtain ⟨R, hRKs, hR2, ⟨eR⟩, hfR, hRf⟩ := Em.exists_image hP2 hPn
  have hRcard : Nat.card ↥R = 128 := by rw [← Nat.card_congr eR.toEquiv, hcard]
  have hsK : s ∈ Kst β := hPn hsP
  have hord : orderOf (Em.f s) = 8 := by rw [Em.orderOf_f hP2 hPn hsP, h8]
  have hRc : ∀ r ∈ R, r * Em.f s = Em.f s * r := by
    intro r hr
    obtain ⟨g, hg, rfl⟩ := hRf r hr
    have h1 := mem_centralizer_singleton_iff.1 (hPc hg)
    rw [← Em.mul g (hPn hg) s hsK, ← Em.mul s hsK g (hPn hg), h1]
  have := (ks_cent8_two_le (Em.mem s hsK) hord hRKs hRc hR2).1
  omega

omit hDP in
theorem sigma_exp {s σ v ξ : G} (hS : S16Gen S s z t) (hD : S16LData G L z t β E σ v ξ) :
    ∃ j : ℕ, σ * s * σ⁻¹ = s ^ j ∧ (j % 8 = 3 ∨ j % 8 = 5) := by
  have hcfg := c.hyp.outerE.cfg
  have hσS : ∀ y ∈ S, σ * y * σ⁻¹ ∈ S := fun y hy => c.normHE_norm_S hD.σ_E hD.σ_z hy
  have hσs : σ * s * σ⁻¹ ∈ S := hσS s hS.hs
  have hord : orderOf (σ * s * σ⁻¹) = 8 := by
    have : σ * s * σ⁻¹ = (MulAut.conj σ) s := rfl
    rw [this, MulEquiv.orderOf_eq]
    exact hS.hord
  obtain ⟨k, hkodd, hk⟩ := order8_in_dihedral hcfg.z_sq hS.hzs hS.hord hS.hgen hσs hord
  have hkodd' : k % 2 = 1 := Nat.odd_iff.1 hkodd
  have hmod : s ^ k = s ^ (k % 8) := by
    rw [← hS.hord] at *
    exact (pow_mod_orderOf s k).symm
  have hs8 : s ^ 8 = 1 := hS.hs8
  have hβL : β ∈ L := c.hyp.outerB.B_le c.hyp.outerB.beta_mem
  have hzL : ∀ ℓ ∈ L, z * ℓ = ℓ * z := fun ℓ hℓ => (hcfg.z_comm_of_mem_A hℓ).symm
  have hKst : ∀ P' : Subgroup G, P' ≤ normalizer ((zpowers β : Subgroup G) : Set G) → P' ≤ Kst β :=
    fun P' h => h
  refine ⟨k % 8, by rw [← hmod]; exact hk, ?_⟩
  by_contra hne
  have h1 : k % 8 = 1 ∨ k % 8 = 7 := by omega
  rcases h1 with h1 | h1
  ·
    have hσs' : σ * s * σ⁻¹ = s := by rw [hk, hmod, h1, pow_one]
    obtain ⟨P, hP2, hPn, hsP, hPc, hPcard⟩ := c.exists_cent_128' hS hD.v_L hD.ξ_L hD.v_t hD.ξ_t
      hD.v4 hD.v_β hD.ξ_β hD.σ_β hD.σ_z hD.card_Y hσs'
    exact no_cent_128 Em hS.hord hP2 hPn hsP hPc hPcard
  ·
    have hsinv : σ * s * σ⁻¹ = s⁻¹ := by
      rw [hk, hmod, h1]
      apply eq_inv_of_mul_eq_one_left
      calc s ^ 7 * s = s ^ 8 := by rw [← pow_succ]
        _ = 1 := hs8
    have hσs' : (σ * z) * s * (σ * z)⁻¹ = s := by
      calc σ * z * s * (σ * z)⁻¹ = σ * (z * s * z⁻¹) * σ⁻¹ := by group
        _ = σ * s⁻¹ * σ⁻¹ := by rw [hS.hzs]
        _ = (σ * s * σ⁻¹)⁻¹ := by group
        _ = s := by rw [hsinv]; group
    have hσβ' : (σ * z) * β * (σ * z)⁻¹ = β⁻¹ := by
      calc σ * z * β * (σ * z)⁻¹ = σ * (z * β * z⁻¹) * σ⁻¹ := by group
        _ = σ * β * σ⁻¹ := by rw [hzL β hβL]; group
        _ = β⁻¹ := hD.σ_β
    have hσz' : (σ * z) * z = z * (σ * z) := by
      calc σ * z * z = z * σ * z := by rw [hD.σ_z]
        _ = z * (σ * z) := by group
    have hcard := card_closure_mul_z hcfg.z_sq hzL hD.σ_z hD.σ_sq hD.σ_notL hD.v_L hD.ξ_L hD.v4
      hD.σ_v hD.σ_ξ hD.card_Y
    obtain ⟨P, hP2, hPn, hsP, hPc, hPcard⟩ := c.exists_cent_128' hS hD.v_L hD.ξ_L hD.v_t hD.ξ_t
      hD.v4 hD.v_β hD.ξ_β hσβ' hσz' hcard hσs'
    exact no_cent_128 Em hS.hord hP2 hPn hsP hPc hPcard

omit hDP in
theorem sigma_s (e : ↥S ≃* DihedralGroup 8) {σ v ξ : G} (hD : S16LData G L z t β E σ v ξ)
    {s : G} (hs : s ∈ S) (h8 : orderOf s = 8) :
    σ * s * σ⁻¹ = s ^ 3 ∨ σ * s * σ⁻¹ = s ^ 5 := by
  have hcfg := c.hyp.outerE.cfg
  obtain ⟨s₀, hS₀⟩ := c.exists_S16Gen e
  obtain ⟨j, hj, hj35⟩ := c.sigma_exp Em hS₀ hD
  obtain ⟨k, hkodd, hsk⟩ := order8_in_dihedral hcfg.z_sq hS₀.hzs hS₀.hord hS₀.hgen hs h8
  have hσs : σ * s * σ⁻¹ = s ^ j := by
    rw [hsk]
    exact conj_pow_of_conj hj k
  have hmod : s ^ j = s ^ (j % 8) := by
    have := pow_mod_orderOf s j
    rw [h8] at this
    exact this.symm
  rw [hσs, hmod]
  rcases hj35 with h | h
  · left
    rw [h]
  · right
    rw [h]

omit c Em hDP in
theorem not_odd_of_invol {x : G} (h2 : x * x = 1) (h1 : x ≠ 1) : ¬ Odd (orderOf x) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two]; exact h2) h1
  rw [h]
  decide

theorem z_coset5 {σ v ξ : G} (hD : S16LData G L z t β E σ v ξ) : InCos 5 (Em.f z) := by
  have hcfg := c.hyp.outerE.cfg
  have hβL : β ∈ L := c.hyp.outerB.B_le c.hyp.outerB.beta_mem
  have hzK : z ∈ centralizer ({β} : Set G) :=
    mem_centralizer_singleton_iff.2 (hcfg.z_comm_of_mem_A hβL).symm
  have hzKst : z ∈ Kst β := cent_le_Kst β hzK
  have hfz : Em.f z ∈ U43Ext := (Em.inner z hzKst).1 hzK
  rcases mem_U43Ext_iff_cos.1 hfz with h0 | h5
  swap
  · exact h5
  exfalso
  have hfzP : Em.f z ∈ P := inCos_zero_iff.1 h0
  have htK : t ∈ centralizer ({β} : Set G) :=
    mem_centralizer_singleton_iff.2
      (mem_centralizer_singleton_iff.1 (c.hyp.outerB.B_cent c.hyp.outerB.beta_mem)).symm
  have htKst : t ∈ Kst β := cent_le_Kst β htK
  have hvK : v ∈ Kst β := mem_normalizer_zpowers_of_conj (Or.inr hD.v_β)
  have hft : Em.f t = (Em.f v) ^ 4 := by
    rw [← hD.v4]
    exact Em.f_pow (P := zpowers v) (zpowers_le.2 hvK) (mem_zpowers v) 4
  have hftP : Em.f t ∈ P := by rw [hft]; exact pow_four_mem_P (Em.mem v hvK)
  have hft2 : Em.f t * Em.f t = 1 := by
    rw [← Em.mul t htKst t htKst, hcfg.t_sq, Em.one]
  have hfz2 : Em.f z * Em.f z = 1 := by
    rw [← Em.mul z hzKst z hzKst, hcfg.z_sq, Em.one]
  have hft1 : Em.f t ≠ 1 := fun h =>
    not_odd_of_invol hcfg.t_sq hcfg.t_ne (odd_orderOf_OG ((Em.ker t htKst).1 h))
  have hfz1 : Em.f z ≠ 1 := fun h =>
    not_odd_of_invol hcfg.z_sq hcfg.z_ne (odd_orderOf_OG ((Em.ker z hzKst).1 h))
  obtain ⟨c₀, hc₀, hcz⟩ := inner_involutions_conj hftP hfzP hft2 hfz2 hft1 hfz1
  obtain ⟨g, hg⟩ := Em.lift_conj htKst hzKst hcfg.t_sq hcfg.z_sq (P_le_U43Ext hc₀) hcz
  apply hcfg.conj_z_ne_t g⁻¹
  rw [← hg]
  group

theorem zsigma (e : ↥S ≃* DihedralGroup 8) {σ v ξ : G} (hD : S16LData G L z t β E σ v ξ)
    {s : G} (hs : s ∈ S) (h8 : orderOf s = 8) (hσ5 : σ * s * σ⁻¹ = s ^ 5) :
    ∃ g : G, g * (z * σ) * g⁻¹ = ξ := by
  have hcfg := c.hyp.outerE.cfg
  have hβ3 : orderOf β = 3 := c.hyp.outerB.beta_order
  obtain ⟨s₀, hS₀⟩ := c.exists_S16Gen e
  obtain ⟨j, hj, hj35⟩ := c.sigma_exp Em hS₀ hD
  obtain ⟨k, hkodd, hsk⟩ := order8_in_dihedral hcfg.z_sq hS₀.hzs hS₀.hord hS₀.hgen hs h8
  have hσs : σ * s * σ⁻¹ = s ^ j := by
    rw [hsk]
    exact conj_pow_of_conj hj k
  have hj5 : j % 8 = 5 := by
    have h1 : s ^ j = s ^ 5 := hσs.symm.trans hσ5
    have h2 := (pow_eq_pow_iff_modEq).1 h1
    rw [h8] at h2
    unfold Nat.ModEq at h2
    omega
  have hσs₀ : σ * s₀ * σ⁻¹ = s₀ ^ 5 := by
    rw [hj]
    have h1 := pow_mod_orderOf s₀ j
    rw [hS₀.hord, hj5] at h1
    exact h1.symm
  obtain ⟨R, hRP, hRn, hσR, hRc, hRexp, hRcard⟩ := c.exists_cent_64_sigma hS₀ hD hσs₀
  obtain ⟨hv7, hξ7, hv8, hξ2, hrel, hvKs, hξKs⟩ := c.coset_vxi Em hDP hD
  have hz5 := c.z_coset5 Em hDP hD
  have hσK : σ ∈ Kst β := mem_normalizer_zpowers_of_conj (Or.inr hD.σ_β)
  have hσ_notK : σ ∉ centralizer ({β} : Set G) := not_mem_cent_of_inv hβ3 hD.σ_β
  have hβL : β ∈ L := c.hyp.outerB.B_le c.hyp.outerB.beta_mem
  have hzK : z ∈ centralizer ({β} : Set G) :=
    mem_centralizer_singleton_iff.2 (hcfg.z_comm_of_mem_A hβL).symm
  have hzKst : z ∈ Kst β := cent_le_Kst β hzK
  have hfσKs : Em.f σ ∈ U43ExtStar := Em.mem σ hσK
  have hfσ2 : Em.f σ * Em.f σ = 1 := by
    rw [← Em.mul σ hσK σ hσK, hD.σ_sq, Em.one]
  have hnotKb : Em.f σ ∉ U43Ext := fun h => hσ_notK ((Em.inner σ hσK).2 h)
  obtain ⟨k₀, hk8, hkV, hkc⟩ := mem_Ks_iff.1 hfσKs
  have hσ2 : InCos 2 (Em.f σ) := by
    rcases hkV with rfl | rfl | rfl | rfl
    · exact absurd (mem_U43Ext_iff_cos.2 (Or.inl hkc)) hnotKb
    · exact hkc
    · exact absurd (mem_U43Ext_iff_cos.2 (Or.inr hkc)) hnotKb
    · exfalso
      obtain ⟨R', hR'Ks, hR'2, ⟨eR'⟩, hfR', hR'f⟩ := Em.exists_image hRP hRn
      have hR'card : Nat.card ↥R' = 64 := by rw [← Nat.card_congr eR'.toEquiv, hRcard]
      have hc' : ∀ r ∈ R', r * Em.f σ = Em.f σ * r := by
        intro r hr
        obtain ⟨g, hg, rfl⟩ := hR'f r hr
        have h1 := mem_centralizer_singleton_iff.1 (hRc hg)
        rw [← Em.mul g (hRn hg) σ hσK, ← Em.mul σ hσK g (hRn hg), h1]
      obtain ⟨r, hr, hr8⟩ := ks_inv7_sylow hfσKs hfσ2 hkc hR'Ks hc' hR'2 (by omega)
      obtain ⟨g, hg, rfl⟩ := hR'f r hr
      have h4 : (Em.f g) ^ 4 = 1 := by
        rw [← Em.f_pow hRn hg, hRexp g hg, Em.one]
      have := orderOf_dvd_of_pow_eq_one h4
      rw [hr8] at this
      omega
  have h7 : InCos 7 (Em.f (z * σ)) := by
    rw [Em.mul z hzKst σ hσK]
    have := inCos_mul (by norm_num : 5 < 8) (by norm_num : 2 < 8) hz5 hσ2
    have h3 : mulTab 5 2 = 7 := by decide
    rwa [h3] at this
  have hzσKst : z * σ ∈ Kst β := (Kst β).mul_mem hzKst hσK
  have hzσ2 : (z * σ) * (z * σ) = 1 := by
    calc z * σ * (z * σ) = z * (σ * z) * σ := by group
      _ = z * (z * σ) * σ := by rw [hD.σ_z]
      _ = (z * z) * (σ * σ) := by group
      _ = 1 := by rw [hcfg.z_sq, hD.σ_sq, one_mul]
  have hfzσ2 : Em.f (z * σ) * Em.f (z * σ) = 1 := by
    rw [← Em.mul _ hzσKst _ hzσKst, hzσ2, Em.one]
  obtain ⟨c₀, hc₀, hcξ⟩ := inv_coset_conj (k := 7) (Or.inr rfl) (Em.mem _ hzσKst) hξKs hfzσ2 hξ2
    h7 hξ7
  have hξK : ξ ∈ Kst β := mem_normalizer_zpowers_of_conj (Or.inr hD.ξ_β)
  obtain ⟨g, hg⟩ := Em.lift_conj hzσKst hξK hzσ2 hD.ξ_sq (P_le_U43Ext hc₀) hcξ
  exact ⟨g, hg⟩

omit hDP in
theorem K0_facts {σ v ξ : G} (hD : S16LData G L z t β E σ v ξ)
    (hDP : ∀ d ∈ L ⊓ centralizer ({β} : Set G), Em.f d ∈ P) :
    ∃ K0 : Subgroup G, K0 ≤ centralizer ({β} : Set G) ∧
      ∀ k ∈ centralizer ({β} : Set G), k * k = 1 → k ≠ 1 →
        (k ∈ K0 → ∃ g : G, g * t * g⁻¹ = k) ∧ (k ∉ K0 → ∃ g : G, g * z * g⁻¹ = k) := by
  have hcfg := c.hyp.outerE.cfg
  set K0 : Subgroup G := (P.comap (Em.homOn (centralizer ({β} : Set G)) (cent_le_Kst β))).map
    (centralizer ({β} : Set G)).subtype with hK0
  have hmem : ∀ k (hk : k ∈ centralizer ({β} : Set G)), k ∈ K0 ↔ Em.f k ∈ P := by
    intro k hk
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro h
      exact ⟨⟨k, hk⟩, h, rfl⟩
  refine ⟨K0, Subgroup.map_subtype_le _, fun k hk hk2 hk1 => ?_⟩
  have hkKst : k ∈ Kst β := cent_le_Kst β hk
  have hfk2 : Em.f k * Em.f k = 1 := by rw [← Em.mul k hkKst k hkKst, hk2, Em.one]
  have hfk1 : Em.f k ≠ 1 := fun h =>
    not_odd_of_invol hk2 hk1 (odd_orderOf_OG ((Em.ker k hkKst).1 h))
  have hfkKb : Em.f k ∈ U43Ext := (Em.inner k hkKst).1 hk
  have hβL : β ∈ L := c.hyp.outerB.B_le c.hyp.outerB.beta_mem
  have hzK : z ∈ centralizer ({β} : Set G) :=
    mem_centralizer_singleton_iff.2 (hcfg.z_comm_of_mem_A hβL).symm
  have hzKst : z ∈ Kst β := cent_le_Kst β hzK
  have htK : t ∈ centralizer ({β} : Set G) :=
    mem_centralizer_singleton_iff.2
      (mem_centralizer_singleton_iff.1 (c.hyp.outerB.B_cent c.hyp.outerB.beta_mem)).symm
  have htKst : t ∈ Kst β := cent_le_Kst β htK
  refine ⟨fun hk0 => ?_, fun hk0 => ?_⟩
  ·
    have hfkP : Em.f k ∈ P := (hmem k hk).1 hk0
    have hvK : v ∈ Kst β := mem_normalizer_zpowers_of_conj (Or.inr hD.v_β)
    have hft : Em.f t = (Em.f v) ^ 4 := by
      rw [← hD.v4]
      exact Em.f_pow (P := zpowers v) (zpowers_le.2 hvK) (mem_zpowers v) 4
    have hftP : Em.f t ∈ P := by rw [hft]; exact pow_four_mem_P (Em.mem v hvK)
    have hft2 : Em.f t * Em.f t = 1 := by
      rw [← Em.mul t htKst t htKst, hcfg.t_sq, Em.one]
    have hft1 : Em.f t ≠ 1 := fun h =>
      not_odd_of_invol hcfg.t_sq hcfg.t_ne (odd_orderOf_OG ((Em.ker t htKst).1 h))
    obtain ⟨c₀, hc₀, hck⟩ := inner_involutions_conj hftP hfkP hft2 hfk2 hft1 hfk1
    exact Em.lift_conj htKst hkKst hcfg.t_sq hk2 (P_le_U43Ext hc₀) hck
  ·
    have hfkP : Em.f k ∉ P := fun h => hk0 ((hmem k hk).2 h)
    have hk5 : InCos 5 (Em.f k) := by
      rcases mem_U43Ext_iff_cos.1 hfkKb with h | h
      · exact absurd (inCos_zero_iff.1 h) hfkP
      · exact h
    have hz5 := c.z_coset5 Em hDP hD
    have hfz2 : Em.f z * Em.f z = 1 := by
      rw [← Em.mul z hzKst z hzKst, hcfg.z_sq, Em.one]
    obtain ⟨c₀, hc₀, hck⟩ := inv_coset_conj (k := 5) (Or.inl rfl) (Em.mem _ hzKst)
      (Em.mem _ hkKst) hfz2 hfk2 hz5 hk5
    exact Em.lift_conj hzKst hkKst hcfg.z_sq hk2 (P_le_U43Ext hc₀) hck

end OuterS16Ctx

end Context

end CFSG.EvenSporadicStandard.Fin76b
