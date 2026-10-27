module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoReducedBAux
import CFSG.LocalAnalysis.AGLEmbedding.OneLieBender

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers

section Reduced

variable {p : ℕ} {Y : Type} [Group Y] [Finite Y] {Rb : Sylow p Y} {Y₀ : Subgroup Y}

theorem ReducedNongeneration.centralizer_le_sup_of_caseTwo (h : ReducedNongeneration p Y Rb Y₀)
    (hKL : KFactCaseTwoLocal) {L : Subgroup Y} (hL : IsComponentOf L ⊤)
    (hiso : IsCaseTwoGroup p L) (hcyc : IsCyclic ((Rb : Subgroup Y) ⊓ L : Subgroup Y)) {t : Y}
    (ht : t ∈ (Rb : Subgroup Y) ⊓ L) (htp : orderOf t = p) :
    Subgroup.centralizer ({t} : Set Y) ≤ (Rb : Subgroup Y) ⊔ Subgroup.centralizer (L : Set Y) := by
  have : Fact p.Prime := ⟨h.prime⟩
  have htC := h.not_mem_centralizer_of_isCyclic hL hcyc ht.2 htp
  have hNC : Subgroup.normalizer (L : Set Y) ≤
      Subgroup.normalizer (Subgroup.centralizer (L : Set Y) : Set Y) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
      (Subgroup.normal_subgroupOf_centralizer_normalizer _)
  exact le_sup_of_forall_coprime_mem Rb (h.sylow_le_centralizer_of_isCyclic hL hcyc ht htp)
    (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ht.2))
    (fun c hc => hNC (mem_normalizer_of_mem_centralizer_of_component hL ht.2 htC hc))
    (fun c hc hcop => h.mem_centralizer_of_coprime_of_caseTwo hKL hL hiso hcyc ht htp hc hcop)

theorem ReducedNongeneration.le_centralizer_of_inf_eq_bot (h : ReducedNongeneration p Y Rb Y₀)
    (hKL : KFactCaseTwoLocal)
    (hcyc : ∀ L : Subgroup Y, IsComponentOf L ⊤ → IsCyclic ((Rb : Subgroup Y) ⊓ L : Subgroup Y))
    {L : Subgroup Y} (hL : IsComponentOf L ⊤) (hiso : IsCaseTwoGroup p L)
    (hN : ∀ t ∈ (Rb : Subgroup Y) ⊓ L, orderOf t = p →
      L ⊓ Subgroup.normalizer (Subgroup.zpowers t : Set Y) ≤ Y₀)
    {V : Subgroup Y} (hVR : V ≤ Rb) (hVn : Y₀ ≤ Subgroup.normalizer (V : Set Y))
    (hVL : V ⊓ ((Rb : Subgroup Y) ⊓ L) = ⊥) : V ≤ Subgroup.centralizer (L : Set Y) := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have := hcyc L hL
  obtain ⟨T, hT⟩ := Walter.exists_sylow_map_eq_inf_of_isSubnormal Rb
    (ComponentClassification.Components.mathlib_subnormal_of_chain hL.2.1
      Subgroup.IsSubnormal.top)
  obtain ⟨⟨s, hsN, hsfix⟩, hinn, -⟩ := (hKL p L hiso).2.2 T
  obtain ⟨t, ht, htp, -⟩ := exists_mem_sylow_inf_component hp h.ne_two h.core_eq_bot Rb hL
  have hsT : (s : Y) ∈ Subgroup.normalizer (((Rb : Subgroup Y) ⊓ L : Subgroup Y) : Set Y) := by
    have hs := (coe_mem_normalizer_map hsN).2
    rwa [hT] at hs
  have hsY₀ : (s : Y) ∈ Y₀ :=
    hN t ht htp ⟨s.2, mem_normalizer_zpowers_of_mem_zpowers
      (conj_mem_zpowers_of_isCyclic rfl ht ((Subgroup.mem_normalizer_iff.mp hsT t).mp ht))⟩
  intro v hv
  have hvN : v ∈ Subgroup.normalizer (L : Set Y) := h.sylow_le_normalizer_component hL (hVR hv)
  have hbot : ∀ g ∈ L, g ∈ Y₀ → g * v * g⁻¹ * v⁻¹ ∈ (Rb : Subgroup Y) → g * v = v * g := by
    intro g hgL hgY₀ hgR
    have h1 : g * v * g⁻¹ * v⁻¹ ∈ V :=
      V.mul_mem ((Subgroup.mem_normalizer_iff.mp (hVn hgY₀) v).mp hv) (V.inv_mem hv)
    have h2 : g * v * g⁻¹ * v⁻¹ ∈ L := by
      have h3 := L.mul_mem hgL ((Subgroup.mem_normalizer_iff.mp hvN g⁻¹).mp (L.inv_mem hgL))
      simpa only [mul_assoc] using h3
    have h4 : g * v * g⁻¹ * v⁻¹ ∈ V ⊓ ((Rb : Subgroup Y) ⊓ L) := ⟨h1, hgR, h2⟩
    rw [hVL, Subgroup.mem_bot] at h4
    calc g * v = g * v * g⁻¹ * v⁻¹ * (v * g) := by group
      _ = v * g := by rw [h4, one_mul]
  set φ := L.normalizerMonoidHom ⟨v, hvN⟩ with hφ
  obtain ⟨x, hxT, hφx⟩ := hinn φ fun y hy => by
    have hyT : (y : Y) ∈ (Rb : Subgroup Y) ⊓ L := hT ▸ ⟨y, hy, rfl⟩
    have hyv := hbot y y.2 (h.sylow_le hyT.1)
      (Rb.mul_mem (Rb.mul_mem (Rb.mul_mem hyT.1 (hVR hv)) (Rb.inv_mem hyT.1))
        (Rb.inv_mem (hVR hv)))
    apply Subtype.ext
    rw [hφ, Subgroup.normalizerMonoidHom_apply_apply_coe, ← hyv]
    group
  have hsv := hbot s s.2 hsY₀ (hVR (V.mul_mem
    ((Subgroup.mem_normalizer_iff.mp (hVn hsY₀) v).mp hv) (V.inv_mem hv)))
  have hxs : s * x * s⁻¹ = x := by
    have h1 := congrArg (fun f : MulAut L => ((f s : L) : Y)) hφx
    simp only [hφ, Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.conj_apply,
      Subgroup.coe_mul, Subgroup.coe_inv] at h1
    have h2 : v * (s : Y) * v⁻¹ = s := by rw [← hsv]; group
    rw [h2] at h1
    have h3 : (s : Y) * x * (s : Y)⁻¹ = x :=
      calc (s : Y) * x * (s : Y)⁻¹ = (x : Y) * s * (x : Y)⁻¹ * x * (s : Y)⁻¹ := by rw [← h1]
        _ = x := by group
    exact Subtype.ext (by simpa using h3)
  have hx1 : x = 1 := hsfix x hxT hxs
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have h1 := congrArg (fun f : MulAut L => ((f ⟨y, hy⟩ : L) : Y)) hφx
  simp only [hφ, Subgroup.normalizerMonoidHom_apply_apply_coe, hx1, map_one,
    MulAut.one_apply] at h1
  calc y * v = v * y * v⁻¹ * v := by rw [h1]
    _ = v * y := by group

theorem ReducedNongeneration.pCore_eq_bot_of_two_components (h : ReducedNongeneration p Y Rb Y₀)
    {L₁ L₂ : Subgroup Y} (hL₁ : IsComponentOf L₁ ⊤) (hL₂ : IsComponentOf L₂ ⊤) (hne : L₁ ≠ L₂)
    (hcyc₁ : IsCyclic ((Rb : Subgroup Y) ⊓ L₁ : Subgroup Y)) (hL₂Y₀ : ¬ L₂ ≤ Y₀) :
    CFSG.pCore p Y = ⊥ := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have : (CFSG.pCore p Y).Normal := CFSG.pCore_normal
  have : IsCyclic (CFSG.pCore p Y) := h.isCyclic_pCore_of_component hL₁
  by_contra hO
  obtain ⟨z, hzO, hz, -⟩ := exists_mem_centralizer_orderOf_eq CFSG.pCore_isPGroup hO
  obtain ⟨t, ⟨htR, htL⟩, ht, -⟩ :=
    exists_mem_sylow_inf_component hp h.ne_two h.core_eq_bot Rb hL₁
  have hEC : CFSG.layer Y ≤ Subgroup.centralizer (CFSG.pCore p Y : Set Y) := by
    rw [← CFSG.Fitting_eq_pcore Y p h.core_eq_bot]
    exact Subgroup.le_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp CFSG.LocalCores.fitting_layer_commute)
  have hzC : ∀ {L : Subgroup Y}, IsComponentOf L ⊤ → z ∈ Subgroup.centralizer (L : Set Y) :=
    fun hL => Subgroup.le_centralizer_iff.mp ((le_layer_of_isComponentOf hL).trans hEC) hzO
  have hzt : z ∉ Subgroup.zpowers t := by
    intro hzt
    have hz1 := h.eq_one_of_mem_centralizer_of_isCyclic hL₁ hcyc₁
      (Subgroup.zpowers_le.mpr htL hzt) (hzC hL₁)
    rw [hz1, orderOf_one] at hz
    exact hp.one_lt.ne hz
  have hzconj : ∀ g : Y, g * z * g⁻¹ ∈ Subgroup.zpowers z := fun g =>
    conj_mem_zpowers_of_isCyclic rfl hzO (‹(CFSG.pCore p Y).Normal›.conj_mem z hzO g)
  have hQR : Subgroup.zpowers t ⊔ Subgroup.zpowers z ≤ Rb :=
    sup_le (Subgroup.zpowers_le.mpr htR)
      (Subgroup.zpowers_le.mpr (CFSG.pCore_isPGroup.le_sylow_of_normal Rb hzO))
  have hQ2 : 2 ≤ Open.pRank p (Subgroup.zpowers t ⊔ Subgroup.zpowers z) :=
    two_le_pRank_of_commute_of_not_mem_zpowers hp ht (hz ▸ pow_orderOf_eq_one z) hzt
      (Subgroup.mem_centralizer_iff.mp (hzC hL₁) t htL)
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers t))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers z))
  have hC := h.three_le_pRank_inf_centralizer_sup_zpowers ht hz
    (fun v hv => h.conj_mem_zpowers_of_component hL₁ hcyc₁ ⟨htR, htL⟩ hv) fun v _ => hzconj v
  have hNQ : Subgroup.normalizer
      ((Subgroup.zpowers t ⊔ Subgroup.zpowers z : Subgroup Y) : Set Y) ≤ Y₀ :=
    (normalizer_le_weakCore p hQR hQ2 (hC.trans (pRank_mono p hp le_sup_right))).trans
      h.weakCore_le
  refine hL₂Y₀ (le_trans ?_ ((Subgroup.centralizer_le_normalizer _).trans hNQ))
  exact le_centralizer_sup_zpowers
    (fun v hv => Subgroup.mem_centralizer_iff.mp (le_centralizer_of_component_ne hL₁ hL₂ hne htL)
      v hv)
    (fun v hv => Subgroup.mem_centralizer_iff.mp (hzC hL₂) v hv)

theorem ReducedNongeneration.centralizer_inf_centralizer_eq_bot
    (h : ReducedNongeneration p Y Rb Y₀) {L₁ L₂ : Subgroup Y} (hL₁ : IsComponentOf L₁ ⊤)
    (hL₂ : IsComponentOf L₂ ⊤) (hne : L₁ ≠ L₂)
    (hcyc₁ : IsCyclic ((Rb : Subgroup Y) ⊓ L₁ : Subgroup Y))
    (hcyc₂ : IsCyclic ((Rb : Subgroup Y) ⊓ L₂ : Subgroup Y)) (hO : CFSG.pCore p Y = ⊥) :
    Subgroup.centralizer (L₁ : Set Y) ⊓ Subgroup.centralizer (L₂ : Set Y) = ⊥ := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hF : CFSG.generalizedFitting Y ≤ L₁ ⊔ L₂ := by
    refine sup_le ?_ (sSup_le fun K hK => ?_)
    · rw [CFSG.Fitting_eq_pcore Y p h.core_eq_bot, hO]
      exact bot_le
    · rcases h.eq_or_eq_of_isComponentOf hL₁ hL₂ hne ((CFSG.isComponent_iff_open K).mp hK) with
        rfl | rfl
      · exact le_sup_left
      · exact le_sup_right
  have hC12 : Subgroup.centralizer (L₁ : Set Y) ⊓ Subgroup.centralizer (L₂ : Set Y) ≤
      Subgroup.centralizer ((L₁ ⊔ L₂ : Subgroup Y) : Set Y) :=
    Subgroup.le_centralizer_iff.mpr (sup_le (Subgroup.le_centralizer_iff.mp inf_le_left)
      (Subgroup.le_centralizer_iff.mp inf_le_right))
  have h₁₂ := le_centralizer_of_component_ne hL₁ hL₂ hne
  have h₂₁ := le_centralizer_of_component_ne hL₂ hL₁ hne.symm
  rw [eq_bot_iff]
  intro x hx
  have hxF : x ∈ L₁ ⊔ L₂ :=
    hF (CFSG.centralizer_generalizedFitting_le Y (Subgroup.centralizer_le hF (hC12 hx)))
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right L₁ L₂
    (h₁₂.trans (Subgroup.centralizer_le_normalizer _))] at hxF
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hxF
  have ha1 : a = 1 := h.eq_one_of_mem_centralizer_of_isCyclic hL₁ hcyc₁ ha (by
    have := (Subgroup.centralizer (L₁ : Set Y)).mul_mem hx.1
      ((Subgroup.centralizer (L₁ : Set Y)).inv_mem (h₂₁ hb))
    rwa [mul_inv_cancel_right] at this)
  rw [ha1, one_mul] at hx
  rw [ha1, one_mul, Subgroup.mem_bot]
  exact h.eq_one_of_mem_centralizer_of_isCyclic hL₂ hcyc₂ hb hx.2

theorem ReducedNongeneration.centralizer_le_of_two_components
    (h : ReducedNongeneration p Y Rb Y₀) (hKL : KFactCaseTwoLocal)
    (hcyc : ∀ L : Subgroup Y, IsComponentOf L ⊤ → IsCyclic ((Rb : Subgroup Y) ⊓ L : Subgroup Y))
    {L₁ L₂ : Subgroup Y} (hL₁ : IsComponentOf L₁ ⊤) (hL₂ : IsComponentOf L₂ ⊤) (hne : L₁ ≠ L₂)
    (hL₁Y₀ : ¬ L₁ ≤ Y₀) (hiso₁ : IsCaseTwoGroup p L₁) (hiso₂ : IsCaseTwoGroup p L₂)
    {t₁ t₂ : Y} (ht₁ : t₁ ∈ (Rb : Subgroup Y) ⊓ L₁) (ht₁p : orderOf t₁ = p)
    (ht₂ : t₂ ∈ (Rb : Subgroup Y) ⊓ L₂) (ht₂p : orderOf t₂ = p) :
    Subgroup.centralizer ({t₁} : Set Y) ⊓ Subgroup.centralizer ({t₂} : Set Y) ≤ Rb := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hC := h.centralizer_inf_centralizer_eq_bot hL₁ hL₂ hne (hcyc L₁ hL₁) (hcyc L₂ hL₂)
    (h.pCore_eq_bot_of_two_components hL₂ hL₁ hne.symm (hcyc L₂ hL₂) hL₁Y₀)
  have hD : IsPGroup p (Subgroup.centralizer ({t₁} : Set Y) ⊓
      Subgroup.centralizer ({t₂} : Set Y) : Subgroup Y) := by
    refine isPGroup_of_forall_coprime_eq_one hp _ fun c hc hcop => ?_
    have hc' : c ∈ Subgroup.centralizer (L₁ : Set Y) ⊓ Subgroup.centralizer (L₂ : Set Y) :=
      ⟨h.mem_centralizer_of_coprime_of_caseTwo hKL hL₁ hiso₁ (hcyc L₁ hL₁) ht₁ ht₁p hc.1 hcop,
        h.mem_centralizer_of_coprime_of_caseTwo hKL hL₂ hiso₂ (hcyc L₂ hL₂) ht₂ ht₂p hc.2 hcop⟩
    rwa [hC, Subgroup.mem_bot] at hc'
  exact (Rb.is_maximal' hD (le_inf (h.sylow_le_centralizer_of_isCyclic hL₁ (hcyc L₁ hL₁) ht₁ ht₁p)
    (h.sylow_le_centralizer_of_isCyclic hL₂ (hcyc L₂ hL₂) ht₂ ht₂p))).le

theorem ReducedNongeneration.centralizer_le_of_mem_pCore (h : ReducedNongeneration p Y Rb Y₀)
    (hKL : KFactCaseTwoLocal)
    (hcyc : ∀ L : Subgroup Y, IsComponentOf L ⊤ → IsCyclic ((Rb : Subgroup Y) ⊓ L : Subgroup Y))
    {L : Subgroup Y} (hL : IsComponentOf L ⊤)
    (huniq : ∀ L' : Subgroup Y, IsComponentOf L' ⊤ → L' = L) (hLY₀ : ¬ L ≤ Y₀)
    (hiso : IsCaseTwoGroup p L) {t z : Y} (ht : t ∈ (Rb : Subgroup Y) ⊓ L) (htp : orderOf t = p)
    (hz : z ∈ CFSG.pCore p Y) (hzp : orderOf z = p) :
    Subgroup.centralizer ({t} : Set Y) ⊓ Subgroup.centralizer ({z} : Set Y) ≤ Rb := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have : (CFSG.pCore p Y).Normal := CFSG.pCore_normal
  have : IsCyclic (CFSG.pCore p Y) := h.isCyclic_pCore_of_component hL
  have : L.Normal := ⟨fun n hn g => huniq _
    ((ComponentClassification.LocalComponents.equiv_iff (MulAut.conj g) L).mpr hL) ▸
      (⟨n, hn, rfl⟩ : g * n * g⁻¹ ∈ L.map (MulAut.conj g).toMonoidHom)⟩
  have hEC : CFSG.layer Y ≤ Subgroup.centralizer (CFSG.pCore p Y : Set Y) := by
    rw [← CFSG.Fitting_eq_pcore Y p h.core_eq_bot]
    exact Subgroup.le_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp CFSG.LocalCores.fitting_layer_commute)
  have hzC : z ∈ Subgroup.centralizer (L : Set Y) :=
    Subgroup.le_centralizer_iff.mp ((le_layer_of_isComponentOf hL).trans hEC) hz
  have hzN : ∀ g : Y, g ∈ Subgroup.normalizer (Subgroup.zpowers z : Set Y) := fun g =>
    mem_normalizer_zpowers_of_mem_zpowers
      (conj_mem_zpowers_of_isCyclic rfl hz (‹(CFSG.pCore p Y).Normal›.conj_mem z hz g))
  have hz1 : Subgroup.zpowers z ≠ ⊥ := by
    rw [Ne, Subgroup.zpowers_eq_bot]
    rintro rfl
    rw [orderOf_one] at hzp
    exact hp.one_lt.ne hzp
  have hCz : Subgroup.centralizer (L : Set Y) ⊓
      Subgroup.centralizer (Subgroup.zpowers z : Set Y) ≤ Rb :=
    h.inf_centralizer_le_of_isCyclic (fun A hAC hA => h.isCyclic_of_le_centralizer hL hLY₀ hA hAC)
      (Subgroup.zpowers_le.mpr hzC) hz1 (CFSG.pCore_isPGroup.to_le (Subgroup.zpowers_le.mpr hz))
      fun g _ => hzN g
  have hD : IsPGroup p (Subgroup.centralizer ({t} : Set Y) ⊓
      Subgroup.centralizer ({z} : Set Y) : Subgroup Y) := by
    refine isPGroup_of_forall_coprime_eq_one hp _ fun c hc hcop => ?_
    have hcz : c ∈ Subgroup.centralizer (Subgroup.zpowers z : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hzc : z ∈ Subgroup.centralizer ({c} : Set Y) :=
        Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_singleton_iff.mp hc.2).symm
      exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.zpowers_le.mpr hzc hy)
    exact eq_one_of_mem_of_coprime Rb.isPGroup'
      (hCz ⟨h.mem_centralizer_of_coprime_of_caseTwo hKL hL hiso (hcyc L hL) ht htp hc.1 hcop, hcz⟩)
      hcop
  have hRz : (Rb : Subgroup Y) ≤ Subgroup.centralizer ({z} : Set Y) := by
    intro v hv
    obtain ⟨k, hk⟩ := Rb.isPGroup' ⟨v, hv⟩
    have hvk : v ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (commute_of_mem_normalizer_zpowers_of_pow_prime_pow hp hzp (hzN v) hvk).eq
  exact (Rb.is_maximal' hD
    (le_inf (h.sylow_le_centralizer_of_isCyclic hL (hcyc L hL) ht htp) hRz)).le

theorem ReducedNongeneration.centralizer_le_of_isPGroup (h : ReducedNongeneration p Y Rb Y₀)
    (hKL : KFactCaseTwoLocal)
    (hcyc : ∀ L : Subgroup Y, IsComponentOf L ⊤ → IsCyclic ((Rb : Subgroup Y) ⊓ L : Subgroup Y))
    {L : Subgroup Y} (hL : IsComponentOf L ⊤) (hiso : IsCaseTwoGroup p L)
    (hW : IsPGroup p (Subgroup.centralizer (L : Set Y)))
    {t : Y} (ht : t ∈ (Rb : Subgroup Y) ⊓ L) (htp : orderOf t = p) :
    Subgroup.centralizer ({t} : Set Y) ≤ Rb := by
  have : Fact p.Prime := ⟨h.prime⟩
  refine (h.centralizer_le_sup_of_caseTwo hKL hL hiso (hcyc L hL) ht htp).trans
    (sup_le le_rfl ?_)
  have hNC : Subgroup.normalizer (L : Set Y) ≤
      Subgroup.normalizer (Subgroup.centralizer (L : Set Y) : Set Y) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
      (Subgroup.normal_subgroupOf_centralizer_normalizer _)
  have hpg : IsPGroup p (((Rb : Subgroup Y) ⊔ Subgroup.centralizer (L : Set Y) : Subgroup Y)) :=
    Rb.isPGroup'.to_sup_of_normal_right' hW ((h.sylow_le_normalizer_component hL).trans hNC)
  exact le_sup_right.trans (Rb.is_maximal' hpg le_sup_left).le

end Reduced

end CFSG.AGLEmbedding
