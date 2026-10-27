module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3L28EndgameMain
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Reduced3

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3L28Cl

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup
open CFSG.AGLEmbedding (CatalogSimpleSections exists_mem_sylow_inf_component)
open GL83P3L28End
open scoped Pointwise

variable {Y : Type} [Group Y]

structure ClosedData [Finite Y] (P : Subgroup Y) (x k : Y) : Prop where
  catalog : CatalogSimpleSections Y
  sylow : IsSylowOf 3 P ⊤
  focal : P ≤ ⁅(⊤ : Subgroup Y), (⊤ : Subgroup Y)⁆
  shape : L28Shape 3 P
  x_mem : x ∈ L28Z P
  x_ne : x ≠ 1
  k_mem : k ∈ P
  k_order : orderOf k = 9
  k_norm : P ≤ normalizer (zpowers k : Set Y)
  k_cube : k ^ 3 ∈ L28Z P
  x_not : x ∉ zpowers k
  z_card : Nat.card (L28Z P) = 3 ^ 2
  invert : ∃ ι : Y, ι * x * ι⁻¹ = x ∧ ι * k ^ 3 * ι⁻¹ = (k ^ 3)⁻¹
  solv : ∀ K : Subgroup Y, IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) → 3 ∣ Nat.card K →
    ¬ K ≤ centralizer ({x} : Set Y)

theorem comm_mem_Z_of_cube {P K : Subgroup Y} (hKP : K ≤ P) (hPK : P ≤ normalizer (K : Set Y))
    (hKab : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a) (hK9 : ∀ a ∈ K, a ^ 9 = 1)
    (hZ : ∀ a : Y, a ∈ L28Z P ↔ a ∈ K ∧ a ^ 3 = 1) {w q : Y} (hw : w ∈ P) (hw3 : w ^ 3 = 1)
    (hq : q ∈ K) : w * q * w⁻¹ * q⁻¹ ∈ L28Z P := by
  set d : Y := w * q * w⁻¹ * q⁻¹ with hd
  have hq' : w * q * w⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hPK hw) q).mp hq
  have hdK : d ∈ K := K.mul_mem hq' (K.inv_mem hq)
  have hq3Z : q ^ 3 ∈ L28Z P :=
    (hZ _).mpr ⟨K.pow_mem hq 3, by rw [← pow_mul]; exact hK9 q hq⟩
  have hq3c : w * q ^ 3 = q ^ 3 * w := (GL83P3L28Aux.mem_L28Z_iff.mp hq3Z).2 w hw
  have hd3 : d ^ 3 = 1 := by
    have hcomm : Commute (w * q * w⁻¹) q⁻¹ := hKab _ hq' _ (K.inv_mem hq)
    have h1 : d ^ 3 = (w * q * w⁻¹) ^ 3 * (q⁻¹) ^ 3 := hcomm.mul_pow 3
    have h2 : (w * q * w⁻¹) ^ 3 = q ^ 3 := by
      have : (w * q * w⁻¹) ^ 3 = w * q ^ 3 * w⁻¹ := conj_pow
      rw [this, hq3c]
      group
    rw [h1, h2, inv_pow, mul_inv_cancel]
  exact (hZ _).mpr ⟨hdK, hd3⟩

theorem comm_mem_Z {P : Subgroup Y} (h : L28Shape 3 P) {f t : Y} (hf : f ∈ P) (ht : t ∈ P)
    (ht3 : t ^ 3 = 1) : f * t * f⁻¹ * t⁻¹ ∈ L28Z P := by
  obtain ⟨K, hKP, hKmax, hPK, hKab, hK9, -, hZ⟩ := GL83P3L28Aux.l28shape_K h
  by_cases htK : t ∈ K
  · have htZ : t ∈ L28Z P := (hZ t).mpr ⟨htK, ht3⟩
    have hft : f * t = t * f := (GL83P3L28Aux.mem_L28Z_iff.mp htZ).2 f hf
    have : f * t * f⁻¹ * t⁻¹ = 1 := by rw [hft]; group
    rw [this]
    exact (L28Z P).one_mem
  · have hPeq : zpowers t ⊔ K = P := by
      refine hKmax _ (lt_of_le_of_ne le_sup_right fun h' => htK ?_)
        (sup_le (zpowers_le.mpr ht) hKP)
      rw [h']
      exact mem_sup_left (mem_zpowers t)
    have hzn : zpowers t ≤ normalizer (K : Set Y) := zpowers_le.mpr (hPK ht)
    have hset := Subgroup.coe_mul_of_left_le_normalizer_right (zpowers t) K hzn
    have hmem : f ∈ (zpowers t : Set Y) * (K : Set Y) := by
      rw [← hset, hPeq]
      exact hf
    obtain ⟨w, hw, q, hq, hwq⟩ := hmem
    have hwq' : w * q = f := hwq
    have hwP : w ∈ P := (zpowers_le.mpr ht) hw
    have hwt : w * t = t * w := by
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hw
      exact ((Commute.refl t).zpow_left i).eq
    have hd := comm_mem_Z_of_cube hKP hPK hKab hK9 hZ ht ht3 hq
    set d : Y := t * q * t⁻¹ * q⁻¹ with hdd
    have hdinv : d⁻¹ ∈ L28Z P := (L28Z P).inv_mem hd
    have hdc : w * d⁻¹ = d⁻¹ * w := (GL83P3L28Aux.mem_L28Z_iff.mp hdinv).2 w hwP
    have hqt : q * t * q⁻¹ = d⁻¹ * t := by rw [hdd]; group
    have hres : f * t * f⁻¹ * t⁻¹ = d⁻¹ := by
      rw [← hwq']
      calc w * q * t * (w * q)⁻¹ * t⁻¹ = w * (q * t * q⁻¹) * w⁻¹ * t⁻¹ := by group
        _ = w * (d⁻¹ * t) * w⁻¹ * t⁻¹ := by rw [hqt]
        _ = (w * d⁻¹) * (t * w⁻¹) * t⁻¹ := by group
        _ = (d⁻¹ * w) * (t * w⁻¹) * t⁻¹ := by rw [hdc]
        _ = d⁻¹ * ((w * t) * w⁻¹) * t⁻¹ := by group
        _ = d⁻¹ * ((t * w) * w⁻¹) * t⁻¹ := by rw [hwt]
        _ = d⁻¹ := by group
    rw [hres]
    exact hdinv

section Components

variable [Finite Y] {P : Subgroup Y}

structure CompSetting (P : Subgroup Y) : Prop where
  sylow : IsSylowOf 3 P ⊤
  shape : L28Shape 3 P
  core : primeComplementCore (G := Y) 3 = ⊥
  pcore : CFSG.pCore 3 Y = ⊥

namespace CompSetting

theorem exists_sylow (hs : CompSetting P) : ∃ S : Sylow 3 Y, (S : Subgroup Y) = P := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hp, hidx⟩ := isSylowOf_iff.mp hs.sylow
  rw [Subgroup.relIndex_top_right] at hidx
  exact ⟨hp.toSylow hidx, rfl⟩

theorem centralizer_layer (hs : CompSetting P) : centralizer (CFSG.layer Y : Set Y) = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact centralizer_layer_eq_bot_of_pCore_eq_bot hs.core hs.pcore

theorem center_bot (hs : CompSetting P) {K : Subgroup Y} (hK : IsComponentOf K ⊤) :
    center K = ⊥ := center_eq_bot_of_centralizer_layer_eq_bot hs.centralizer_layer hK

theorem simple (hs : CompSetting P) {K : Subgroup Y} (hK : IsComponentOf K ⊤) :
    IsSimpleGroup K ∧ ∃ a b : K, a * b ≠ b * a :=
  isSimpleGroup_of_isComponentOf_of_center_eq_bot hK (hs.center_bot hK)

theorem exists_t (hs : CompSetting P) {K : Subgroup Y} (hK : IsComponentOf K ⊤) :
    ∃ t ∈ P ⊓ K, orderOf t = 3 ∧ t ∉ centralizer (K : Set Y) := by
  obtain ⟨S, hS⟩ := hs.exists_sylow
  obtain ⟨t, ht, hto, htC⟩ := exists_mem_sylow_inf_component Nat.prime_three (by norm_num)
    hs.core S hK
  rw [hS] at ht
  exact ⟨t, ht, hto, htC⟩

theorem comp_le_centralizer {K L : Subgroup Y} (hK : IsComponentOf K ⊤) (hL : IsComponentOf L ⊤)
    (hne : K ≠ L) : K ≤ centralizer (L : Set Y) :=
  commutator_eq_bot_iff_le_centralizer.mp
    (CFSG.ComponentClassification.LocalComponents.commute_of_ne K L hK hL hne)

theorem normalizes (hs : CompSetting P) {K : Subgroup Y} (hK : IsComponentOf K ⊤) :
    P ≤ normalizer (K : Set Y) := by
  intro f hf
  by_contra hfK
  obtain ⟨n, hn⟩ := hs.sylow.isPGroup ⟨f, hf⟩
  have hfn : f ^ 3 ^ n = 1 := congrArg Subtype.val hn
  obtain ⟨t₁, ht₁, ht₁o, ht₁C⟩ := hs.exists_t hK
  have ht₁3 : t₁ ^ 3 = 1 := ht₁o ▸ pow_orderOf_eq_one t₁
  obtain ⟨z, hz⟩ : ∃ z, z = f * t₁ * f⁻¹ * t₁⁻¹ := ⟨_, rfl⟩
  obtain ⟨t₂, ht₂⟩ : ∃ t₂, t₂ = f * t₁ * f⁻¹ := ⟨_, rfl⟩
  obtain ⟨t₃, ht₃⟩ : ∃ t₃, t₃ = f * t₂ * f⁻¹ := ⟨_, rfl⟩
  have hzZ : z ∈ L28Z P := hz ▸ comm_mem_Z hs.shape hf ht₁.1 ht₁3
  have hzc : ∀ g ∈ P, g * z = z * g := (GL83P3L28Aux.mem_L28Z_iff.mp hzZ).2
  have hzt : t₁ * z = z * t₁ := hzc t₁ ht₁.1
  have e2 : t₂ = z * t₁ := by rw [hz, ht₂]; group
  have e3 : t₃ = z * t₂ :=
    calc t₃ = f * t₂ * f⁻¹ := ht₃
      _ = f * (z * t₁) * f⁻¹ := by rw [← e2]
      _ = (f * z) * t₁ * f⁻¹ := by group
      _ = (z * f) * t₁ * f⁻¹ := by rw [hzc f hf]
      _ = z * (f * t₁ * f⁻¹) := by group
      _ = z * t₂ := by rw [ht₂]
  have e4 : t₂ * t₂ = t₃ * t₁ := by
    rw [e3, e2]
    calc z * t₁ * (z * t₁) = z * (t₁ * z) * t₁ := by group
      _ = z * (z * t₁) * t₁ := by rw [hzt]
  have e5 : t₁ = t₃⁻¹ * (t₂ * t₂) := by rw [e4]; group
  have hK2 : IsComponentOf (K.map (MulAut.conj f).toMonoidHom) ⊤ :=
    (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj f) K).mpr hK
  have hK3 : IsComponentOf (K.map (MulAut.conj (f ^ 2)).toMonoidHom) ⊤ :=
    (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj (f ^ 2)) K).mpr hK
  have hne2 : K.map (MulAut.conj f).toMonoidHom ≠ K := fun h =>
    hfK (mem_normalizer_iff_map_conj_eq.mpr h)
  have hne3 : K.map (MulAut.conj (f ^ 2)).toMonoidHom ≠ K := fun h =>
    hfK (mem_normalizer_of_pow_mem' hfn (m := 2) (by norm_num [Nat.Coprime])
      (mem_normalizer_iff_map_conj_eq.mpr h))
  have ht₂C : t₂ ∈ centralizer (K : Set Y) :=
    comp_le_centralizer hK2 hK hne2 ⟨t₁, ht₁.2, by
      show f * t₁ * f⁻¹ = t₂
      rw [ht₂]⟩
  have ht₃C : t₃ ∈ centralizer (K : Set Y) :=
    comp_le_centralizer hK3 hK hne3 ⟨t₁, ht₁.2, by
      show f ^ 2 * t₁ * (f ^ 2)⁻¹ = t₃
      rw [ht₃, ht₂, pow_two]
      group⟩
  apply ht₁C
  rw [e5]
  exact (centralizer (K : Set Y)).mul_mem ((centralizer (K : Set Y)).inv_mem ht₃C)
    ((centralizer (K : Set Y)).mul_mem ht₂C ht₂C)

theorem exists_central (hs : CompSetting P) {K : Subgroup Y} (hK : IsComponentOf K ⊤) :
    ∃ z ∈ P ⊓ K, z ≠ 1 ∧ z ^ 3 = 1 ∧ (∀ g ∈ P, g * z = z * g) ∧
      z ∉ centralizer (K : Set Y) := by
  obtain ⟨t, ht, hto, -⟩ := hs.exists_t hK
  have hNP := hs.normalizes hK
  have hne : P ⊓ K ≠ ⊥ := by
    intro h
    have ht1 : t = 1 := by simpa [h] using ht
    rw [ht1, orderOf_one] at hto
    omega
  obtain ⟨z, hz, hz1, hz3, hzc⟩ := FData.exists_central (A := P ⊓ K) hs.sylow.isPGroup inf_le_left
    (fun g hg a ha => ⟨P.mul_mem (P.mul_mem hg ha.1) (P.inv_mem hg),
      ((mem_normalizer_iff.mp (hNP hg)) a).mp ha.2⟩) hne
  refine ⟨z, hz, hz1, hz3, hzc, fun hC => hz1 ?_⟩
  have hzK : (⟨z, hz.2⟩ : K) ∈ center K := Subgroup.mem_center_iff.mpr fun g =>
    Subtype.ext (mem_centralizer_iff.mp hC g g.2)
  rw [hs.center_bot hK, mem_bot] at hzK
  exact congrArg Subtype.val hzK

theorem card_le_two (hs : CompSetting P) (hzc : Nat.card (L28Z P) = 3 ^ 2)
    (s : Finset (Subgroup Y)) (hsK : ∀ K ∈ s, IsComponentOf K ⊤) : s.card ≤ 2 := by
  classical
  have hex : ∀ K : s, ∃ z ∈ P ⊓ (K : Subgroup Y), z ≠ 1 ∧ z ^ 3 = 1 ∧
      (∀ g ∈ P, g * z = z * g) ∧ z ∉ centralizer ((K : Subgroup Y) : Set Y) :=
    fun K => hs.exists_central (hsK K K.2)
  choose z hzK hz1 hz3 hzcen hzC using hex
  have hKK : ∀ i j : s, i ≠ j → (i : Subgroup Y) ≤ centralizer ((j : Subgroup Y) : Set Y) :=
    fun i j hij => comp_le_centralizer (hsK i i.2) (hsK j j.2) fun h => hij (Subtype.ext h)
  obtain ⟨-, hEc⟩ := isElemAbelian_iSup_zpowers Nat.prime_three
    (fun K : s => (K : Subgroup Y)) z hz3 (fun K => (hzK K).2) hzC hKK Finset.univ
  have hle : (⨆ i ∈ (Finset.univ : Finset s), zpowers (z i)) ≤ L28Z P :=
    iSup₂_le fun i _ => zpowers_le.mpr (GL83P3L28Aux.mem_L28Z_iff.mpr ⟨(hzK i).1, hzcen i⟩)
  have h1 := Subgroup.card_le_of_le hle
  rw [hEc, hzc, Finset.card_univ, Fintype.card_coe] at h1
  by_contra hlt
  push Not at hlt
  have h2 : 3 ^ 3 ≤ 3 ^ s.card := Nat.pow_le_pow_right (by norm_num) hlt
  omega

end CompSetting

namespace ClosedData

variable {x k : Y}

theorem exists_component (hd : ClosedData P x k) (hs : CompSetting P) :
    ∃ K : Subgroup Y, IsComponentOf K ⊤ := by
  by_contra hno
  push Not at hno
  have hlay : CFSG.layer Y = ⊥ := CFSG.LocalCores.layer_eq_bot_of_forall
    (fun K hK => hno K ((CFSG.isComponent_iff_open K).mp hK))
  have h := hs.centralizer_layer
  rw [hlay] at h
  have hY : ∀ g : Y, g = 1 := fun g => by
    have hg : g ∈ centralizer (((⊥ : Subgroup Y)) : Set Y) := by
      rw [mem_centralizer_iff]
      intro h' hh'
      rw [SetLike.mem_coe, mem_bot] at hh'
      rw [hh']
      group
    rw [h] at hg
    exact mem_bot.mp hg
  have hP : Nat.card P = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    exact ⟨⟨fun a b => Subtype.ext ((hY a).trans (hY b).symm)⟩, ⟨1⟩⟩
  have := hd.shape.1
  omega

theorem false_of_unique (hd : ClosedData P x k) (hs : CompSetting P)
    (h12 : KFactL28ThreeQuotient) {K : Subgroup Y} (hK : IsComponentOf K ⊤)
    (hu : ∀ L : Subgroup Y, IsComponentOf L ⊤ → L = K) : False := by
  have hKn : K.Normal := ⟨fun n hn g => by
    have hmap : K.map (MulAut.conj g).toMonoidHom = K :=
      hu _ ((CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj g) K).mpr hK)
    rw [← hmap]
    exact ⟨n, hn, by simp [MulAut.conj_apply]⟩⟩
  have hlay : CFSG.layer Y = K := by
    refine le_antisymm (sSup_le fun L hL => ?_) (le_sSup ((CFSG.isComponent_iff_open K).mpr hK))
    exact (hu L ((CFSG.isComponent_iff_open L).mp hL)).le
  have hCK : centralizer (K : Set Y) = ⊥ := by
    have := hs.centralizer_layer
    rwa [hlay] at this
  obtain ⟨hKs, hKnab⟩ := hs.simple hK
  have hcat : IsCatalogGroup K := hd.catalog.simple_subgroup K hKs hKnab
  obtain ⟨t, ht, hto, -⟩ := hs.exists_t hK
  have h3 : 3 ∣ Nat.card K := by
    have hord : orderOf (⟨t, ht.2⟩ : K) = 3 := by
      rw [← Subgroup.orderOf_coe]
      exact hto
    exact hord ▸ _root_.orderOf_dvd_natCard _
  exact h12 Y K hKn hKs hKnab hcat hCK h3 P hd.sylow hd.shape hd.focal

theorem two_components (hd : ClosedData P x k) (hs : CompSetting P) (h12 : KFactL28ThreeQuotient) :
    ∃ K₁ K₂ : Subgroup Y, IsComponentOf K₁ ⊤ ∧ IsComponentOf K₂ ⊤ ∧ K₁ ≠ K₂ ∧
      ∀ K : Subgroup Y, IsComponentOf K ⊤ → K = K₁ ∨ K = K₂ := by
  classical
  obtain ⟨K₀, hK₀⟩ := hd.exists_component hs
  by_cases h : ∃ K : Subgroup Y, IsComponentOf K ⊤ ∧ K ≠ K₀
  · obtain ⟨K₂, hK₂, hne⟩ := h
    refine ⟨K₀, K₂, hK₀, hK₂, hne.symm, fun K hK => ?_⟩
    by_contra hcon
    push Not at hcon
    have hcard := hs.card_le_two hd.z_card {K₀, K₂, K} (by
      intro L hL
      simp only [Finset.mem_insert, Finset.mem_singleton] at hL
      rcases hL with rfl | rfl | rfl <;> assumption)
    rw [Finset.card_eq_three.mpr ⟨K₀, K₂, K, hne.symm, hcon.1.symm, hcon.2.symm, rfl⟩] at hcard
    omega
  · push Not at h
    exact (hd.false_of_unique hs h12 hK₀ (fun L hL => h L hL)).elim

end ClosedData

end Components

end CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3L28Cl
