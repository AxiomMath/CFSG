module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2012NFTypes

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2012

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Bg CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Final
  CFSG.GH74.GLS.Stage2.Final.Thm6 CFSG.GH74.GLS.Stage2.Final.Thm6.L20 CFSG.GH74.GLS.Stage2.Bender.Thm1
  CFSG.GH74.GLS.Stage2.Final.Thm4 CFSG.GH74.GLS.Stage2.Final.Thm6.SL2Bound


section Odd

variable {G : Type} [Group G] [Finite G]

theorem centralizes_oddCore_of_F {z u : G} (hu : u ∈ Cen z) (hu2 : u * u = 1)
    (hF : ∀ f ∈ F20 z, u * f = f * u) : ∀ a ∈ OddCore z, u * a = a * u := by
  intro a ha
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hA_le : OddCore z ≤ Cen z := Subgroup.map_subtype_le _
  have hnorm : ∀ x ∈ OddCore z, u * x * u⁻¹ ∈ OddCore z := fun x hx =>
    (Subgroup.mem_normalizer_iff.1 (Cen_le_normalizer_OddCore z hu) x).1 hx
  have hFcomm : ∀ f ∈ F20 z, u * f * u⁻¹ = f := fun f hf => by
    rw [hF f hf]; group
  set a' : G := u * a * u⁻¹ with ha'
  have ha'A : a' ∈ OddCore z := hnorm a ha
  have hc : a'⁻¹ * a ∈ OddCore z := (OddCore z).mul_mem ((OddCore z).inv_mem ha'A) ha
  have hcF : ∀ f ∈ F20 z, f * (a'⁻¹ * a) = (a'⁻¹ * a) * f := by
    intro f hf
    have hconj : a' * f * a'⁻¹ = a * f * a⁻¹ := by
      have h1 : a * f * a⁻¹ ∈ F20 z := F20_conj_mem z (hA_le ha) hf
      calc a' * f * a'⁻¹ = u * (a * (u⁻¹ * f * u) * a⁻¹) * u⁻¹ := by simp only [ha']; group
        _ = u * (a * f * a⁻¹) * u⁻¹ := by
          have : u⁻¹ * f * u = f := by rw [huinv]; calc u * f * u = u * f * u⁻¹ := by rw [huinv]
                                                      _ = f := hFcomm f hf
          rw [this]
        _ = a * f * a⁻¹ := hFcomm _ h1
    calc f * (a'⁻¹ * a) = a'⁻¹ * (a' * f * a'⁻¹) * a := by group
      _ = a'⁻¹ * (a * f * a⁻¹) * a := by rw [hconj]
      _ = (a'⁻¹ * a) * f := by group
  have hcFm : a'⁻¹ * a ∈ F20 z := oddCore_centralizer_le_F z hc (fun f hf => hcF f hf)
  set c : G := a'⁻¹ * a with hcdef
  have h1 : a = a' * c := by rw [hcdef]; group
  have h2 : a' = a * c := by
    have : u * a * u⁻¹ = (u * a' * u⁻¹) * (u * c * u⁻¹) := by
      conv_lhs => rw [h1]
      group
    have e1 : u * a' * u⁻¹ = a := by simp only [ha']; rw [huinv]; calc u * (u * a * u) * u = (u * u) * a * (u * u) := by group
                                                                                            _ = a := by rw [hu2]; group
    rw [e1, hFcomm c hcFm] at this
    exact this
  have hcc : c * c = 1 := by
    have : a = a * c * c := by
      calc a = a' * c := h1
        _ = a * c * c := by rw [h2]
    calc c * c = a⁻¹ * (a * c * c) := by group
      _ = a⁻¹ * a := by rw [← this]
      _ = 1 := by group
  have hodd : Odd (orderOf c) := CFSG.GH74.GLS.Stage2.Final.Thm6.L20.odd_orderOf_of_mem_pPrimeCoreOf
    (F := Cen z) (F20_le_OddCore z hcFm)
  have hc1 : c = 1 := eq_one_of_sq_odd_nf hcc hodd
  have : a' = a := by rw [h2, hc1, mul_one]
  calc u * a = (u * a * u⁻¹) * u := by group
    _ = a * u := by rw [← ha', this]


end Odd

section NF

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {ε : Bool} {q : ℕ}
  {L₁ L₂ : Subgroup (CentralizerBar z)} {K₁ K₂ : Subgroup G}

omit [Finite G] in
theorem barOf_mono {K K' : Subgroup G} (h : K ≤ K') : barOf z K ≤ barOf z K' :=
  Subgroup.map_mono (fun _ hx => Subgroup.mem_subgroupOf.2 (h (Subgroup.mem_subgroupOf.1 hx)))

theorem NFCtx.LC_decomp (h : NFCtx G z S ε q L₁ L₂ K₁ K₂) {l : G} (hl : l ∈ LC z) :
    ∃ a ∈ OddCore z, ∃ k ∈ Em (Cen z), l = a * k := by
  have hlC : l ∈ Cen z := LC_le_Cen z hl
  have hb : toBar z ⟨l, hlC⟩ ∈ LBar z := ⟨⟨l, hlC⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
  have hK₁ : K₁ ≤ Em (Cen z) := h.comp.layer ▸ le_sup_left
  have hK₂ : K₂ ≤ Em (Cen z) := h.comp.layer ▸ le_sup_right
  have hL₁ : L₁ ≤ barOf z (Em (Cen z)) := h.comp.bar₁ ▸ barOf_mono hK₁
  have hL₂ : L₂ ≤ barOf z (Em (Cen z)) := h.comp.bar₂ ▸ barOf_mono hK₂
  rw [← h.pair.prod.1] at hb
  have hb' := sup_le hL₁ hL₂ hb
  obtain ⟨k, hkC, hkE, hk⟩ := bar_mem_barOf_iff.1 hb'
  refine ⟨l * k⁻¹, ?_, k, hkE, by group⟩
  have h1 : toBar z ⟨l * k⁻¹, (Cen z).mul_mem hlC ((Cen z).inv_mem hkC)⟩ = 1 := by
    have : (⟨l * k⁻¹, (Cen z).mul_mem hlC ((Cen z).inv_mem hkC)⟩ : ↥(Cen z)) =
        ⟨l, hlC⟩ * ⟨k, hkC⟩⁻¹ := rfl
    rw [this, map_mul, map_inv, hk]
    group
  have h2 : (⟨l * k⁻¹, (Cen z).mul_mem hlC ((Cen z).inv_mem hkC)⟩ : ↥(Cen z)) ∈ pPrimeCore 2 ↥(Cen z) :=
    (QuotientGroup.eq_one_iff _).1 h1
  exact ⟨_, h2, rfl⟩

theorem NFCtx.swapper_ne_z (h : NFCtx G z S ε q L₁ L₂ K₁ K₂) {y : G} (hysw : Swaps z y L₁ L₂) : y ≠ z := by
  intro hyz
  subst hyz
  obtain ⟨hyC, h1, -⟩ := hysw
  have hfix : conjugate L₁ (toBar y ⟨y, hyC⟩) = L₁ :=
    bar_mem_normalizer_iff_conjugate_eq.1
      (Subgroup.center_le_normalizer (L₁ : Set (CentralizerBar y)) (by
        have hc := toBar_z_mem_center y
        exact hc))
  exact h.pair.ne (hfix.symm.trans h1)


omit [Finite G] in
theorem isConj_conj_self (z g : G) : IsConj z (g * z * g⁻¹) := isConj_iff.2 ⟨g, rfl⟩

theorem NFCtx.exists_g (h : NFCtx G z S ε q L₁ L₂ K₁ K₂) {y : G} (hy : y ∈ Cen z) (hyconj : IsConj z y) :
    ∃ g : G, zc z g = y ∧ g * z * g⁻¹ ∈ S := by
  obtain ⟨c0, hc0⟩ := isConj_iff.mp hyconj
  set g₀ := c0⁻¹ with hg₀
  have hzc0 : zc z g₀ = y := by
    simp only [zc, hg₀, inv_inv]
    exact hc0
  have htC : g₀ * z * g₀⁻¹ ∈ Cen z := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp hy
    rw [← hzc0] at h1
    simp only [zc] at h1
    calc g₀ * z * g₀⁻¹ * z = g₀ * (z * (g₀⁻¹ * z * g₀)) * g₀⁻¹ := by group
      _ = g₀ * ((g₀⁻¹ * z * g₀) * z) * g₀⁻¹ := by rw [← h1]
      _ = z * (g₀ * z * g₀⁻¹) := by group
  have ht2 : (g₀ * z * g₀⁻¹) * (g₀ * z * g₀⁻¹) = 1 := by
    calc (g₀ * z * g₀⁻¹) * (g₀ * z * g₀⁻¹) = g₀ * (z * z) * g₀⁻¹ := by group
      _ = 1 := by rw [h.z2]; group
  obtain ⟨c, hcC, hc⟩ := exists_mem_conj_into_sylow h.ctx.sylow htC ht2
  refine ⟨c * g₀, ?_, ?_⟩
  · have h1 := Subgroup.mem_centralizer_singleton_iff.mp hcC
    simp only [zc]
    have : c⁻¹ * z * c = z := by
      calc c⁻¹ * z * c = c⁻¹ * (z * c) := by group
        _ = c⁻¹ * (c * z) := by rw [h1]
        _ = z := by group
    calc (c * g₀)⁻¹ * z * (c * g₀) = g₀⁻¹ * (c⁻¹ * z * c) * g₀ := by group
      _ = g₀⁻¹ * z * g₀ := by rw [this]
      _ = y := hzc0
  · have e : c * g₀ * z * (c * g₀)⁻¹ = c * (g₀ * z * g₀⁻¹) * c⁻¹ := by group
    rw [e]
    exact hc

theorem NFCtx.partner_swaps (h : NFCtx G z S ε q L₁ L₂ K₁ K₂) {y : G} (hyS : y ∈ S) (hyconj : IsConj z y)
    (hysw : Swaps z y L₁ L₂) {g : G} (hg : zc z g = y) (htS : g * z * g⁻¹ ∈ S) :
    Swaps z (g * z * g⁻¹) L₁ L₂ := by
  rcases h.swaps_or_nrm htS with hsw | ⟨hn₁, hn₂⟩
  · exact hsw
  exfalso
  obtain ⟨x, hx⟩ := h.two
  set t₁ := g * z * g⁻¹ with ht₁
  have ht₁C : t₁ ∈ Cen z := h.SC htS
  have hz2 := h.z2
  have ht₁2 : t₁ * t₁ = 1 := by
    calc t₁ * t₁ = g * (z * z) * g⁻¹ := by simp only [ht₁]; group
      _ = 1 := by rw [hz2]; group
  have hyne : y ≠ z := h.swapper_ne_z hysw
  have ht₁z : t₁ ≠ z := by
    intro e
    apply hyne
    rw [← hg]
    simp only [zc]
    have hcomm : g * z = z * g := by
      calc g * z = (g * z * g⁻¹) * g := by group
        _ = z * g := by rw [← ht₁, e]
    calc g⁻¹ * z * g = g⁻¹ * (z * g) := by group
      _ = g⁻¹ * (g * z) := by rw [hcomm]
      _ = z := by group
  have ht₁1 : t₁ ≠ 1 := by
    intro e
    have : z = g⁻¹ * t₁ * g := by simp only [ht₁]; group
    rw [e] at this
    apply h.z1
    rw [this]; group
  have ht₁conj : IsConj z t₁ := isConj_conj_self z g
  have hLC : t₁ ∉ LC z := by
    intro hLC
    have hbar : toBar z ⟨t₁, ht₁C⟩ ∈ L₁ ⊔ L₂ := by
      rw [h.pair.prod.1]
      exact ⟨⟨t₁, ht₁C⟩, Subgroup.mem_subgroupOf.mpr hLC, rfl⟩
    have hem := h.comp.mem_layer t₁ ht₁C ht₁2 hbar
    exact ht₁z (layer_conj_eq_of_two h.ctx.central hx t₁ hem ht₁conj)
  have hgood : GoodInvolution z S L₁ L₂ q t₁ := h.good_of_nrm htS ht₁2 ht₁1 hn₁ hn₂ hLC
  have hc1 : IsConj z (t₁ * z) := h.fuse _ (h.good_mul_z hgood)
  have hc2 : IsConj x (y * z) := (hx.swap_conseq y hyS hyconj hysw).1
  have hc3 : IsConj (y * z) (z * t₁) := by
    refine isConj_iff.2 ⟨g, ?_⟩
    have : g * y * g⁻¹ = z := by rw [← hg]; simp only [zc]; group
    calc g * (y * z) * g⁻¹ = (g * y * g⁻¹) * (g * z * g⁻¹) := by group
      _ = z * t₁ := by rw [this]
  have hcomm : t₁ * z = z * t₁ := h.ctx.S_comm_z htS
  have hc4 : IsConj x (t₁ * z) := by rw [hcomm]; exact hc2.trans hc3
  exact hx.x_nonCentral (isCentralInvolution_of_conj' h.ctx.central (hc1.trans hc4.symm))


omit [Finite G] in
theorem mul_self_eq_one_of_conj' {z y : G} (hz2 : z * z = 1) (h : IsConj z y) : y * y = 1 := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  rw [← hc]
  calc c * z * c⁻¹ * (c * z * c⁻¹) = c * (z * z) * c⁻¹ := by group
    _ = 1 := by rw [hz2]; group

theorem NFCtx.inverts_of_S (h11 : Lemma20_11) {k : Kind} {M : Subgroup G} (hF : Fail20 G z k S M)
    (hMC : M = Cen z) (hT : TypeCl z k S) (h : NFCtx G z S ε q L₁ L₂ K₁ K₂) {y : G} (hyS : y ∈ S)
    (hyconj : IsConj z y) (hysw : Swaps z y L₁ L₂) : ∀ f ∈ F20 z, y * f * y⁻¹ = f⁻¹ := by
  have hz2 := h.z2
  have hyC : y ∈ Cen z := h.SC hyS
  have hy2 : y * y = 1 := mul_self_eq_one_of_conj' hz2 hyconj
  obtain ⟨g, hzcg, htS⟩ := h.exists_g hyC hyconj
  have hyne : y ≠ z := h.swapper_ne_z hysw
  have hynot : y ∉ zpowers z := by
    intro hmem
    rcases eq_one_or_eq_of_mem_zpowers hz2 hmem with h1 | h1
    · rw [h1] at hyconj
      have h3 := orderOf_eq_two_of_conj h.ctx.orderOf_z hyconj
      rw [orderOf_one] at h3
      omega
    · exact hyne h1
  have hyC' : zc z g ∈ Cen z := by rw [hzcg]; exact hyC
  have hy2' : zc z g * zc z g = 1 := by rw [hzcg]; exact hy2
  have hsw₁ : cj (toBar z ⟨zc z g, hyC'⟩) L₁ = L₂ := by
    obtain ⟨hy, hsw'⟩ := swaps_cj hysw
    have e : (⟨zc z g, hyC'⟩ : ↥(Cen z)) = ⟨y, hy⟩ := Subtype.ext hzcg
    rwa [e]
  obtain ⟨ht₁C', htsw₁'⟩ := swaps_cj (h.partner_swaps hyS hyconj hysw hzcg htS)
  have hfix : ∀ e ∈ F20 z, y * e * y⁻¹ = e → e = 1 := by
    intro e he hye
    have heA : e ∈ OddCore z := F20_le_OddCore z he
    have hodd : Odd (orderOf e) := CFSG.GH74.GLS.Stage2.Final.Thm6.L20.odd_orderOf_of_mem_pPrimeCoreOf
      (F := Cen z) heA
    have heC : e ∈ Cen (zc z g) := by
      rw [hzcg, Subgroup.mem_centralizer_singleton_iff]
      calc e * y = (y * e * y⁻¹) * y := by rw [hye]
        _ = y * e := by group
    have hxI : e ∈ centralizer (Em ((K₁ ⊔ K₂) ⊓ centralizer ({zc z g} : Set G)) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro i hi
      have hiL : i ∈ Em (Cen z) := by
        rw [h.comp.layer]
        exact (Subgroup.map_subtype_le _ hi).1
      exact (h.comp.oddcomm e heA i hiL).symm
    have hmem := oddA_y h.comp hz2 hyC' hy2' hsw₁ ht₁C' htsw₁' heC hodd hxI
    have hbot := h11 G z k S M hF hMC hT g (by rw [hzcg]; exact hyS) (by rw [hzcg]; exact hynot)
    have : e ∈ F20 z ⊓ Ag z g := ⟨he, hmem⟩
    rw [hbot] at this
    exact Subgroup.mem_bot.mp this
  intro f hf
  exact inverted_of_fixed_point_free hy2 (fun e he => F20_conj_mem z hyC he) hfix f hf


theorem NFCtx.swapper_inverts_F (h11 : Lemma20_11) {k : Kind} {M : Subgroup G} (hF : Fail20 G z k S M)
    (hMC : M = Cen z) (hT : TypeCl z k S) (h : NFCtx G z S ε q L₁ L₂ K₁ K₂) {v : G} (hvC : v ∈ Cen z)
    (hv : IsConj z v) (hsw : Swaps z v L₁ L₂) : ∀ f ∈ F20 z, v * f * v⁻¹ = f⁻¹ := by
  have hv2 := mul_self_eq_one_of_conj' h.z2 hv
  have hvo : orderOf v = 2 := orderOf_eq_two_of_conj h.ctx.orderOf_z hv
  obtain ⟨kk, hkk, hmem⟩ := exists_conj_mem_S h.ctx.sylow hvC hvo
  set y := kk⁻¹ * v * kk with hy
  have hySw : Swaps z y L₁ L₂ := by
    have := swaps_conj h.pair ((Cen z).inv_mem hkk) hsw
    simpa [hy] using this
  have hyconj : IsConj z y := hv.trans (isConj_iff.2 ⟨kk⁻¹, by simp [hy]⟩)
  have hinv := h.inverts_of_S h11 hF hMC hT hmem hyconj hySw
  intro f hf
  have hf' : kk⁻¹ * f * kk ∈ F20 z := by
    have := F20_conj_mem z ((Cen z).inv_mem hkk) hf
    simpa using this
  have h1 := hinv _ hf'
  calc v * f * v⁻¹ = kk * (y * (kk⁻¹ * f * kk) * y⁻¹) * kk⁻¹ := by simp only [hy]; group
    _ = kk * (kk⁻¹ * f * kk)⁻¹ * kk⁻¹ := by rw [h1]
    _ = f⁻¹ := by group

theorem NFCtx.F_comm (h11 : Lemma20_11) {k : Kind} {M : Subgroup G} (hF : Fail20 G z k S M)
    (hMC : M = Cen z) (hT : TypeCl z k S) (h : NFCtx G z S ε q L₁ L₂ K₁ K₂) :
    ∀ f₁ ∈ F20 z, ∀ f₂ ∈ F20 z, f₁ * f₂ = f₂ * f₁ := by
  obtain ⟨x, hx⟩ := h.two
  obtain ⟨s, hsS, hsconj, hssw⟩ := hx.swap_exists
  have hinv := h.swapper_inverts_F h11 hF hMC hT (h.SC hsS) hsconj hssw
  intro f₁ hf₁ f₂ hf₂
  have h12 := hinv (f₁ * f₂) ((F20 z).mul_mem hf₁ hf₂)
  have e : s * (f₁ * f₂) * s⁻¹ = (s * f₁ * s⁻¹) * (s * f₂ * s⁻¹) := by group
  rw [e, hinv f₁ hf₁, hinv f₂ hf₂] at h12
  have : f₁⁻¹ * f₂⁻¹ = f₂⁻¹ * f₁⁻¹ := by rw [h12]; group
  have h3 := congrArg (fun w => w⁻¹) this
  simpa [mul_inv_rev] using h3.symm


theorem NFCtx.good_centralizes_F (h11 : Lemma20_11) {k : Kind} {M : Subgroup G} (hF : Fail20 G z k S M)
    (hMC : M = Cen z) (hT : TypeCl z k S) (h : NFCtx G z S ε q L₁ L₂ K₁ K₂) {u : G}
    (hg : GoodInvolution z S L₁ L₂ q u) : ∀ f ∈ F20 z, u * f * u⁻¹ = f := by
  obtain ⟨x, hx⟩ := h.two
  obtain ⟨s, hsS, hsconj, hssw⟩ := hx.swap_exists
  obtain ⟨-, hnsw, -, -, -, -⟩ := h.good_props hg
  have huS := hg.1
  have huC : u ∈ Cen z := h.SC huS
  have hu2 : u * u = 1 := sq_of_good hg
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hsinv := h.swapper_inverts_F h11 hF hMC hT (h.SC hsS) hsconj hssw
  have hgS : u * s ∈ S := S.mul_mem huS hsS
  obtain ⟨l, hlLC, hlconj⟩ := hx.coset (u * s) (Subgroup.mem_sup_right hgS)
  have hlC : l ∈ Cen z := LC_le_Cen z hlLC
  have hvC : u * s * l ∈ Cen z := (Cen z).mul_mem ((Cen z).mul_mem huC (h.SC hsS)) hlC
  have hvsw : Swaps z (u * s * l) L₁ L₂ :=
    swaps_mul_LC h.pair (swaps_mul_of_not_swaps h.pair huC hnsw hssw) hlLC
  have hvinv := h.swapper_inverts_F h11 hF hMC hT hvC hlconj hvsw
  obtain ⟨a, haA, k', hk'E, hlak⟩ := h.LC_decomp hlLC
  have hA_le : OddCore z ≤ Cen z := Subgroup.map_subtype_le _
  have haC : a ∈ Cen z := hA_le haA
  have hlf : ∀ f ∈ F20 z, l * f * l⁻¹ = a * f * a⁻¹ := by
    intro f hf
    have hkf : k' * f = f * k' := (h.comp.oddcomm f (F20_le_OddCore z hf) k' hk'E).symm
    rw [hlak]
    calc a * k' * f * (a * k')⁻¹ = a * (k' * f) * k'⁻¹ * a⁻¹ := by group
      _ = a * (f * k') * k'⁻¹ * a⁻¹ := by rw [hkf]
      _ = a * f * a⁻¹ := by group
  have hstep : ∀ f ∈ F20 z, u * (l * f * l⁻¹) * u⁻¹ = f := by
    intro f hf
    have hf' : l * f * l⁻¹ ∈ F20 z := F20_conj_mem z hlC hf
    have h1 := hvinv f hf
    have e : u * s * l * f * (u * s * l)⁻¹ = u * (s * (l * f * l⁻¹) * s⁻¹) * u⁻¹ := by group
    rw [e, hsinv _ hf'] at h1
    have h2 : (u * (l * f * l⁻¹) * u⁻¹)⁻¹ = f⁻¹ := by
      rw [← h1]; group
    have h3 := congrArg (fun w => w⁻¹) h2
    simpa using h3
  have hstepa : ∀ f ∈ F20 z, u * (a * f * a⁻¹) * u⁻¹ = f := fun f hf => by
    rw [← hlf f hf]; exact hstep f hf
  have huf : ∀ f ∈ F20 z, u * f * u⁻¹ = a * f * a⁻¹ := by
    intro f hf
    have hf' : a * f * a⁻¹ ∈ F20 z := F20_conj_mem z haC hf
    have h1 := hstepa f hf
    have hmem : u * f * u⁻¹ ∈ F20 z := F20_conj_mem z huC hf
    calc u * f * u⁻¹ = u * (u * (a * f * a⁻¹) * u⁻¹) * u⁻¹ := by rw [h1]
      _ = (u * u) * (a * f * a⁻¹) * (u⁻¹ * u⁻¹) := by group
      _ = a * f * a⁻¹ := by rw [hu2, ← mul_inv_rev, hu2]; group
  have ha2 : ∀ f ∈ F20 z, f * (a * a) = (a * a) * f := by
    intro f hf
    have hf' : a * f * a⁻¹ ∈ F20 z := F20_conj_mem z haC hf
    have h1 : a * (a * f * a⁻¹) * a⁻¹ = f := ((huf _ hf').symm).trans (hstepa f hf)
    calc f * (a * a) = (a * (a * f * a⁻¹) * a⁻¹) * (a * a) := by rw [h1]
      _ = (a * a) * f := by group
  have hodda : Odd (orderOf a) := CFSG.GH74.GLS.Stage2.Final.Thm6.L20.odd_orderOf_of_mem_pPrimeCoreOf
    (F := Cen z) haA
  have haaA : a * a ∈ OddCore z := (OddCore z).mul_mem haA haA
  have haaF : a * a ∈ F20 z := oddCore_centralizer_le_F z haaA ha2
  have haF : a ∈ F20 z := by
    obtain ⟨n, hn⟩ := hodda
    have h1 : (a * a) ^ (n + 1) = a := by
      calc (a * a) ^ (n + 1) = a ^ (2 * (n + 1)) := by rw [← sq, ← pow_mul]
        _ = a ^ (orderOf a) * a := by rw [hn]; group
        _ = a := by rw [pow_orderOf_eq_one, one_mul]
    rw [← h1]
    exact (F20 z).pow_mem haaF _
  intro f hf
  have hcom := h.F_comm h11 hF hMC hT a haF f hf
  rw [huf f hf]
  calc a * f * a⁻¹ = (f * a) * a⁻¹ := by rw [← hcom]
    _ = f := by group

theorem NFCtx.good_centralizes_A (h11 : Lemma20_11) {k : Kind} {M : Subgroup G} (hF : Fail20 G z k S M)
    (hMC : M = Cen z) (hT : TypeCl z k S) (h : NFCtx G z S ε q L₁ L₂ K₁ K₂) {u : G}
    (hg : GoodInvolution z S L₁ L₂ q u) : ∀ a ∈ OddCore z, u * a = a * u := by
  apply centralizes_oddCore_of_F (h.SC hg.1) (sq_of_good hg)
  intro f hf
  have := h.good_centralizes_F h11 hF hMC hT hg f hf
  calc u * f = (u * f * u⁻¹) * u := by group
    _ = f * u := by rw [this]

end NF


end CFSG.GH74.GLS.Stage2.Final.Thm6.L2012
