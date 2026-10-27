module

public import CFSG.LocalAnalysis.EvenBN.TwoF4.FusionModel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreeLocalFusionZStar
public import CFSG.Monster.B.Recog.GenericBurnsideCenter

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.TwoF4

open Subgroup
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
open CFSG.QuasithinUnique.Vol2Native.L239.Lie.F4 (rel_C5)
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_iff)
open CFSG.ProperTwoGeneratedCore.LocalCriterionThreeLocalFusion
  (not_isolated_involution_of_nonabelian_simple)
open scoped commutatorElement

theorem commutator_self_le {X : Type*} [Group X] (D : Subgroup X) : ⁅D, D⁆ ≤ D :=
  commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

theorem conj_mem_commutator_self {X : Type*} [Group X] {D : Subgroup X} {d x : X} (hd : d ∈ D)
    (hx : x ∈ ⁅D, D⁆) : d * x * d⁻¹ ∈ ⁅D, D⁆ :=
  le_normalizer_iff.1 (le_normalizer_iff_commutator_le_right.2
    (commutator_mono le_rfl (commutator_self_le D))) d hd x hx

theorem exists_mul_of_mem_sup_of_le_centralizer {X : Type*} [Group X] {A B : Subgroup X}
    (hB : B ≤ centralizer (A : Set X)) {u : X} (hu : u ∈ A ⊔ B) :
    ∃ x ∈ A, ∃ y ∈ B, u = x * y := by
  rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left A B
    (hB.trans (centralizer_le_normalizer _)), Set.mem_mul] at hu
  obtain ⟨x, hx, y, hy, rfl⟩ := hu
  exact ⟨x, hx, y, hy, rfl⟩

namespace Setup

variable {G : Type} [Group G] [Finite G]
  (h : Setup G)

theorem Tsyl_le_C : h.Tsyl ≤ h.C := inf_le_right

theorem L_sup_Tsyl_le_C : h.L ⊔ h.Tsyl ≤ h.C := sup_le h.L_le_C h.Tsyl_le_C

theorem t_sq : h.t ^ 2 = 1 := by rw [sq, h.t_mul_t]

theorem commute_t {x : G} (hx : x ∈ h.C) : x * h.t = h.t * x :=
  mem_centralizer_singleton_iff.1 hx

theorem commute_t_of_mem_L {x : G} (hx : x ∈ h.L) : x * h.t = h.t * x :=
  h.commute_t (h.L_le_C hx)

theorem conj_pow_t {g : G} (hg : g ∈ h.C) (k : ℕ) : g⁻¹ * h.t ^ k * g = h.t ^ k := by
  rw [mul_assoc, ← (Commute.pow_right (h.commute_t hg) k).eq, inv_mul_cancel_left]

theorem conj_mem_Tsyl {x : G} (hx : x ∈ h.C) {c : G} (hc : c ∈ h.Tsyl) : x * c * x⁻¹ ∈ h.Tsyl := by
  have := h.normal_kernel_subgroupOf_C.conj_mem ⟨c, hc.2⟩ (by rw [mem_subgroupOf]; exact hc)
    ⟨x, hx⟩
  rwa [mem_subgroupOf] at this

theorem exists_hom_ne_one : ∃ (A : Type) (_ : CommGroup A) (χ : h.C →* A),
    χ ⟨h.t, h.t_mem_C⟩ ≠ 1 := by
  classical
  set T := h.Tsyl with hT
  let _ : CommGroup T :=
    { (inferInstance : Group T) with mul_comm := fun x y => Subtype.ext (h.kernel_comm x.2 y.2) }
  have hcomm : ∀ (l : h.L) (c : T), Commute (h.L.subtype l) (T.subtype c) := fun l c =>
    mem_centralizer_iff.1 (mem_inf.1 c.2).1 l l.2
  set F := MonoidHom.noncommCoprod h.L.subtype T.subtype hcomm with hF
  have hFinj : Function.Injective F := by
    rw [injective_iff_map_eq_one]
    rintro ⟨l, c⟩ hlc
    rw [hF, MonoidHom.noncommCoprod_apply] at hlc
    change (l : G) * c = 1 at hlc
    have hl : (l : G) = (c : G)⁻¹ := eq_inv_of_mul_eq_one_left hlc
    have hmem : (l : G) ∈ h.L ⊓ centralizer (h.L : Set G) := by
      refine mem_inf.2 ⟨l.2, ?_⟩
      rw [hl]
      exact Subgroup.inv_mem _ (mem_inf.1 c.2).1
    rw [h.inf_centralizer_eq_bot, mem_bot] at hmem
    have hc : (c : G) = 1 := by rw [hmem, one_mul] at hlc; exact hlc
    ext <;> simp [hmem, hc]
  have hFrange : F.range = h.L ⊔ T := by
    rw [hF, MonoidHom.noncommCoprod_range, range_subtype, range_subtype]
  set H₀ : Subgroup h.C := (h.L ⊔ T).subgroupOf h.C with hH₀
  let e₁ : H₀ ≃* (h.L ⊔ T : Subgroup G) := subgroupOfEquivOfLe h.L_sup_Tsyl_le_C
  let e₂ : (h.L ⊔ T : Subgroup G) ≃* F.range := MulEquiv.subgroupCongr hFrange.symm
  let e₃ : F.range ≃* h.L × T := (MonoidHom.ofInjective hFinj).symm
  let ψ : H₀ →* T := (MonoidHom.snd h.L T).comp (e₁.trans (e₂.trans e₃)).toMonoidHom
  have htH : (⟨h.t, h.t_mem_C⟩ : h.C) ∈ H₀ := by
    rw [hH₀, mem_subgroupOf]
    exact mem_sup_right h.t_mem_Tsyl
  have hFt : F (1, ⟨h.t, h.t_mem_Tsyl⟩) = h.t := by
    rw [hF, MonoidHom.noncommCoprod_apply]
    exact one_mul _
  have hψ : ψ ⟨⟨h.t, h.t_mem_C⟩, htH⟩ = ⟨h.t, h.t_mem_Tsyl⟩ := by
    have h1 : e₂ (e₁ ⟨⟨h.t, h.t_mem_C⟩, htH⟩) =
        MonoidHom.ofInjective hFinj (1, ⟨h.t, h.t_mem_Tsyl⟩) := by
      apply Subtype.ext
      rw [MonoidHom.ofInjective_apply, hFt]
      rfl
    change (e₃ (e₂ (e₁ ⟨⟨h.t, h.t_mem_C⟩, htH⟩))).2 = _
    rw [h1]
    change ((MonoidHom.ofInjective hFinj).symm (MonoidHom.ofInjective hFinj _)).2 = _
    rw [MulEquiv.symm_apply_apply]
  refine ⟨T, inferInstance, MonoidHom.transfer ψ, ?_⟩
  rw [MonoidHom.transfer_eq_pow ψ _ fun k g₀ _ => ?_]
  · obtain ⟨m, hm⟩ := h.odd_relIndex
    have hidx : H₀.index = 2 * m + 1 := hm
    have hpow : (⟨(⟨h.t, h.t_mem_C⟩ : h.C) ^ H₀.index,
        MonoidHom.transfer_eq_pow_aux _ fun k g₀ _ => Subtype.ext (by
          simp only [coe_mul, coe_inv, SubgroupClass.coe_pow]
          exact h.conj_pow_t g₀.2 k)⟩ : H₀) = ⟨⟨h.t, h.t_mem_C⟩, htH⟩ ^ H₀.index := rfl
    rw [hpow, map_pow, hψ, hidx]
    intro h1
    apply h.t_ne_one
    have h2 := congrArg Subtype.val h1
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h2
    rwa [pow_succ, pow_mul, h.t_sq, one_pow, one_mul] at h2
  · apply Subtype.ext
    simp only [coe_mul, coe_inv, SubgroupClass.coe_pow]
    exact h.conj_pow_t g₀.2 k

theorem t_not_mem_commutator {X : Subgroup G} (hXC : X ≤ h.C) : h.t ∉ ⁅X, X⁆ := by
  obtain ⟨A, _, χ, hχ⟩ := h.exists_hom_ne_one
  intro ht
  have hle : ⁅X, X⁆ ≤ (χ.ker).map h.C.subtype := by
    rw [commutator_le]
    intro x hx y hy
    refine ⟨⁅(⟨x, hXC hx⟩ : h.C), ⟨y, hXC hy⟩⁆, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  obtain ⟨c, hc, hct⟩ := hle ht
  have : c = ⟨h.t, h.t_mem_C⟩ := Subtype.ext hct
  rw [this] at hc
  exact hχ hc

theorem conj_inv_mem_C {g y x : G} (hg : g * h.t * g⁻¹ = y) (hx : x * y = y * x) :
    g⁻¹ * x * g ∈ h.C := by
  rw [mem_centralizer_singleton_iff]
  have ht : h.t = g⁻¹ * y * g := by rw [← hg]; group
  rw [ht]
  calc g⁻¹ * x * g * (g⁻¹ * y * g) = g⁻¹ * (x * y) * g := by group
    _ = g⁻¹ * (y * x) * g := by rw [hx]
    _ = g⁻¹ * y * g * (g⁻¹ * x * g) := by group

theorem conj_ne_e (g : G) : g * h.t * g⁻¹ ≠ h.e := by
  intro hg
  have hαe : h.elt (sylowD h.a h.K 1 0) * h.e = h.e * h.elt (sylowD h.a h.K 1 0) :=
    h.commute_e h.elt_sylowD_mem_P
  have hfe : h.f * h.e = h.e * h.f := h.commute_e (h.V_le_P .i10 h.e_f_mem_orderOf.2.1)
  apply h.t_not_mem_commutator (le_refl h.C)
  have ht : h.t = ⁅g⁻¹ * h.elt (sylowD h.a h.K 1 0) * g, g⁻¹ * h.f * g⁆ := by
    have h1 : h.t = g⁻¹ * h.e * g := by rw [← hg]; group
    rw [h1, h.e_eq_commutator, commutatorElement_def, commutatorElement_def]
    group
  rw [ht]
  exact commutator_mem_commutator (h.conj_inv_mem_C hg hαe) (h.conj_inv_mem_C hg hfe)

theorem conj_ne_f (g : G) : g * h.t * g⁻¹ ≠ h.f := by
  intro hg
  obtain ⟨x, y, z, w, hx, hy, hz, hw, hf⟩ := h.f_eq_commutator
  apply h.t_not_mem_commutator (le_refl h.C)
  have ht : h.t = ⁅g⁻¹ * x * g, g⁻¹ * y * g⁆ * ⁅g⁻¹ * z * g, g⁻¹ * w * g⁆⁻¹ := by
    have h1 : h.t = g⁻¹ * h.f * g := by rw [← hg]; group
    rw [h1, hf, commutatorElement_def, commutatorElement_def, commutatorElement_def,
      commutatorElement_def]
    group
  rw [ht]
  exact mul_mem (commutator_mem_commutator (h.conj_inv_mem_C hg hx) (h.conj_inv_mem_C hg hy))
    (inv_mem (commutator_mem_commutator (h.conj_inv_mem_C hg hz) (h.conj_inv_mem_C hg hw)))

theorem conj_t_mul_self (g : G) : g * h.t * g⁻¹ * (g * h.t * g⁻¹) = 1 := by
  calc g * h.t * g⁻¹ * (g * h.t * g⁻¹) = g * (h.t * h.t) * g⁻¹ := by group
    _ = 1 := by rw [h.t_mul_t]; group

theorem conj_t_ne_one (g : G) : g * h.t * g⁻¹ ≠ 1 := fun e => h.t_ne_one (by
  calc h.t = g⁻¹ * (g * h.t * g⁻¹) * g := by group
    _ = 1 := by rw [e]; group)

theorem conj_not_mem_L (g : G) : g * h.t * g⁻¹ ∉ h.L := by
  intro hl
  obtain ⟨x, -, hxe | hxf⟩ := h.exists_conj_e_or_f hl (h.conj_t_mul_self g) (h.conj_t_ne_one g)
  · exact h.conj_ne_e (x * g) (by rw [← hxe]; group)
  · exact h.conj_ne_f (x * g) (by rw [← hxf]; group)

theorem mul_conj_mem_L {g : G} (hg : g * h.t * g⁻¹ ∈ h.C) :
    h.t * (g * h.t * g⁻¹) ∈ h.L := by
  rcases h.involution_mem hg (by rw [sq]; exact h.conj_t_mul_self g) with hL | hL
  · exact absurd hL (h.conj_not_mem_L g)
  · exact hL

theorem exists_conj_te_or_tf {g : G} (hg : g * h.t * g⁻¹ ∈ h.C)
    (hne : g * h.t * g⁻¹ ≠ h.t) :
    ∃ x ∈ h.L, x * g * h.t * (x * g)⁻¹ = h.t * h.e ∨ x * g * h.t * (x * g)⁻¹ = h.t * h.f := by
  set y := g * h.t * g⁻¹ with hy
  set l := h.t * y with hl
  have hlL : l ∈ h.L := h.mul_conj_mem_L hg
  have hyt : y * h.t = h.t * y := h.commute_t hg
  have hl2 : l * l = 1 := by
    calc l * l = h.t * (y * h.t) * y := by rw [hl]; group
      _ = (h.t * h.t) * (y * y) := by rw [hyt]; group
      _ = 1 := by rw [h.t_mul_t, h.conj_t_mul_self g, one_mul]
  have hl1 : l ≠ 1 := by
    intro e
    apply hne
    calc y = h.t * l := by rw [hl, ← mul_assoc, h.t_mul_t, one_mul]
      _ = h.t := by rw [e, mul_one]
  have hyl : y = h.t * l := by rw [hl, ← mul_assoc, h.t_mul_t, one_mul]
  obtain ⟨x, hx, hxe | hxf⟩ := h.exists_conj_e_or_f hlL hl2 hl1
  · refine ⟨x, hx, Or.inl ?_⟩
    calc x * g * h.t * (x * g)⁻¹ = x * y * x⁻¹ := by rw [hy]; group
      _ = x * h.t * x⁻¹ * (x * l * x⁻¹) := by rw [hyl]; group
      _ = h.t * h.e := by rw [hxe, h.commute_t_of_mem_L hx]; group
  · refine ⟨x, hx, Or.inr ?_⟩
    calc x * g * h.t * (x * g)⁻¹ = x * y * x⁻¹ := by rw [hy]; group
      _ = x * h.t * x⁻¹ * (x * l * x⁻¹) := by rw [hyl]; group
      _ = h.t * h.f := by rw [hxf, h.commute_t_of_mem_L hx]; group

section CaseB

theorem S₂_le_commutator : h.S₂ ≤ ⁅h.C ⊓ centralizer ({h.f} : Set G),
    h.C ⊓ centralizer ({h.f} : Set G)⁆ := by
  set X := h.C ⊓ centralizer ({h.f} : Set G) with hX
  have hK := h.card_K
  have hF : invF h.K h.a ∈ F4.reeGamma h.K h.a :=
    rootV_le_reeGamma hK .i10 (rootElt_mem_rootV _ _)
  have hmemX : ∀ {g : ModGL F4.tag h.K}, g ∈ F4.reeGamma h.K h.a →
      g * invF h.K h.a = invF h.K h.a * g → h.elt g ∈ X := fun hg hgf =>
    ⟨h.L_le_C (h.elt_mem hg), mem_centralizer_singleton_iff.2 ((h.commute_elt_iff hg hF).2 hgf)⟩
  have hS4 : ∀ {i : Idx}, i ∈ ({.i2, .i5, .i6, .i8, .i7, .i9, .i10, .i11, .i12} : Finset Idx) →
      ∀ u, h.elt (rootElt h.K h.a i u) ∈ X := by
    intro i hi u
    have hmem : rootElt h.K h.a i u ∈ tKernel h.K h.a := by
      rw [← S4_eq_tKernel hK]
      exact rootV_le_rootJoin hi (rootElt_mem_rootV _ _)
    exact hmemX (rootV_le_reeGamma hK i (rootElt_mem_rootV _ _))
      (mem_centralizer_singleton_iff.1 (tKernel_le_centralizer hK 1 hmem))
  have hN3 : ∀ {g : ModGL F4.tag h.K}, g ∈ leviN h.K h.a .i3 → h.elt g ∈ X := fun hg =>
    hmemX (leviN_le_reeGamma hK _ hg)
      (mem_centralizer_singleton_iff.1 (rankOneGroupOne_le_centralizer_sylowL 1 hg))
  have hΓ : ∀ (i : Idx) (u : h.K), rootElt h.K h.a i u ∈ F4.reeGamma h.K h.a :=
    fun i u => rootV_le_reeGamma hK i (rootElt_mem_rootV _ _)
  have h12 : ∀ u, h.elt (rootElt h.K h.a .i12 u) ∈ ⁅X, X⁆ := by
    intro u
    have hAF : ⁅rootElt h.K h.a .i3 u, rootElt h.K h.a .i11 1⁆ = rootElt h.K h.a .i12 u := by
      have := comm_famAF hK u 1
      rwa [mul_one] at this
    rw [← hAF, h.elt_commutator (hΓ .i3 u) (hΓ .i11 1)]
    exact commutator_mem_commutator (hN3 (rootV_le_leviN hK .i3 (rootElt_mem_rootV .i3 u)))
      (hS4 (i := .i11) (by decide) 1)
  have hs : weylOne h.K ∈ F4.reeGamma h.K h.a := weylS_mem_reeGamma
  have h11 : ∀ u, h.elt (rootElt h.K h.a .i11 u) ∈ ⁅X, X⁆ := by
    intro u
    have hc : weylOne h.K * rootElt h.K h.a .i12 u * (weylOne h.K)⁻¹ = rootElt h.K h.a .i11 u :=
      weylOne_conj_sylowH u
    rw [← hc, h.elt_mul' (mul_mem hs (hΓ .i12 u)) (inv_mem hs),
      h.elt_mul' hs (hΓ .i12 u), h.elt_inv' hs]
    exact conj_mem_commutator_self (hN3 weylS_mem_leviN) (h12 u)
  have h10 : ∀ u, h.elt (rootElt h.K h.a .i10 u) ∈ ⁅X, X⁆ := by
    intro u
    have h5 : ⁅rootElt h.K h.a .i2 u, rootElt h.K h.a .i8 1⁆ = rootElt h.K h.a .i10 u *
        rootElt h.K h.a .i11 (largeReeSigma h.a u) * rootElt h.K h.a .i12 u := by
      have := rel_C5 hK (m := h.a) u 1
      simp only [largeReeSigma_one, one_mul, mul_one] at this
      exact this
    have hL : rootElt h.K h.a .i10 u = ⁅rootElt h.K h.a .i2 u, rootElt h.K h.a .i8 1⁆ *
        (rootElt h.K h.a .i11 (largeReeSigma h.a u) * rootElt h.K h.a .i12 u)⁻¹ := by
      rw [h5]
      group
    have hc : ⁅rootElt h.K h.a .i2 u, rootElt h.K h.a .i8 1⁆ ∈ F4.reeGamma h.K h.a := by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem (hΓ .i2 u) (hΓ .i8 1)) (inv_mem (hΓ .i2 u)))
        (inv_mem (hΓ .i8 1))
    have hFH : rootElt h.K h.a .i11 (largeReeSigma h.a u) * rootElt h.K h.a .i12 u ∈
        F4.reeGamma h.K h.a := mul_mem (hΓ .i11 _) (hΓ .i12 u)
    rw [hL, h.elt_mul' hc (inv_mem hFH), h.elt_inv' hFH, h.elt_commutator (hΓ .i2 u) (hΓ .i8 1),
      h.elt_mul' (hΓ .i11 _) (hΓ .i12 u)]
    exact mul_mem (commutator_mem_commutator (hS4 (i := .i2) (by decide) u)
      (hS4 (i := .i8) (by decide) 1)) (inv_mem (mul_mem (h11 _) (h12 u)))
  intro w hw
  obtain ⟨g, hg, hgΓ, rfl⟩ := (h.mem_pull_iff_elt).1 hw
  have hg' : g ∈ (S2 h.K h.a : Set (ModGL F4.tag h.K)) := hg
  rw [(S2_spec hK).2.1] at hg'
  obtain ⟨x, hx, rfl⟩ := hg'
  rw [sylowVec_eq_of_mem_S2 hK hx, h.elt_mul' (mul_mem (hΓ .i11 _) (hΓ .i12 _)) (hΓ .i10 _),
    h.elt_mul' (hΓ .i11 _) (hΓ .i12 _)]
  exact mul_mem (mul_mem (h11 _) (h12 _)) (h10 _)

theorem S₄_le_L : h.S₄ ≤ h.L := h.pull_le_L _

theorem Tsyl_le_centralizer_S₄ : h.Tsyl ≤ centralizer (h.S₄ : Set G) := fun _ hc =>
  centralizer_le (fun _ hx => h.S₄_le_L hx) (mem_inf.1 hc).1

theorem isPGroup_S₄_sup_Tsyl : IsPGroup 2 (h.S₄ ⊔ h.Tsyl : Subgroup G) := by
  have hS4P : h.S₄ ≤ h.P := h.pull_mono (rootJoin_le_sylowP h.card_K _)
  exact (h.isPGroup_P.to_le hS4P).to_sup_of_normal_left' h.isPGroup_kernel fun c hc =>
    Subgroup.centralizer_le_normalizer _ (h.Tsyl_le_centralizer_S₄ hc)

theorem conj_mem_S₄_of_mem {x : G} (hx : x ∈ h.C ⊓ centralizer ({h.f} : Set G)) {s : G}
    (hs : s ∈ h.S₄) : x * s * x⁻¹ ∈ h.S₄ := by
  have hS4P : h.S₄ ≤ h.P := h.pull_mono (rootJoin_le_sylowP h.card_K _)
  set M := h.S₄.map (MulAut.conj x).toMonoidHom with hM
  have hxL : ∀ {l : G}, l ∈ h.L → x * l * x⁻¹ ∈ h.L := fun hl => h.conj_mem_L (mem_inf.1 hx).1 hl
  have hxf : x * h.f = h.f * x := mem_centralizer_singleton_iff.1 (mem_inf.1 hx).2
  have hconjf : ∀ {y : G}, y * h.f = h.f * y → x * y * x⁻¹ * h.f = h.f * (x * y * x⁻¹) :=
    fun {y} hy => by
      calc x * y * x⁻¹ * h.f = x * y * (x⁻¹ * h.f) := by group
        _ = x * y * (h.f * x⁻¹) := by
            rw [show x⁻¹ * h.f = h.f * x⁻¹ by
              calc x⁻¹ * h.f = x⁻¹ * (h.f * x) * x⁻¹ := by group
                _ = x⁻¹ * (x * h.f) * x⁻¹ := by rw [hxf]
                _ = h.f * x⁻¹ := by group]
        _ = x * (y * h.f) * x⁻¹ := by group
        _ = x * (h.f * y) * x⁻¹ := by rw [hy]
        _ = h.f * (x * y * x⁻¹) := by
            rw [show x * (h.f * y) * x⁻¹ = (x * h.f) * y * x⁻¹ by group, hxf]; group
  have hML : M ≤ h.L ⊓ centralizer ({h.f} : Set G) := by
    rintro _ ⟨s, hs, rfl⟩
    have := h.S₄_le hs
    exact ⟨hxL this.1, mem_centralizer_singleton_iff.2 (hconjf
      (mem_centralizer_singleton_iff.1 this.2))⟩
  have hMn : ∀ y ∈ h.L ⊓ centralizer ({h.f} : Set G), ∀ m ∈ M, y * m * y⁻¹ ∈ M := by
    rintro y hy _ ⟨s, hs, rfl⟩
    have hy' : x⁻¹ * y * x ∈ h.L ⊓ centralizer ({h.f} : Set G) := by
      refine mem_inf.2 ⟨?_, ?_⟩
      · have := h.conj_mem_L (inv_mem (mem_inf.1 hx).1) (mem_inf.1 hy).1
        rwa [inv_inv] at this
      · rw [mem_centralizer_singleton_iff]
        have hyf := mem_centralizer_singleton_iff.1 (mem_inf.1 hy).2
        have hxf' : x⁻¹ * h.f = h.f * x⁻¹ := by
          calc x⁻¹ * h.f = x⁻¹ * (h.f * x) * x⁻¹ := by group
            _ = x⁻¹ * (x * h.f) * x⁻¹ := by rw [hxf]
            _ = h.f * x⁻¹ := by group
        calc x⁻¹ * y * x * h.f = x⁻¹ * y * (h.f * x) := by rw [mul_assoc, hxf]
          _ = x⁻¹ * (y * h.f) * x := by group
          _ = x⁻¹ * (h.f * y) * x := by rw [hyf]
          _ = (x⁻¹ * h.f) * y * x := by group
          _ = h.f * (x⁻¹ * y * x) := by rw [hxf']; group
    refine ⟨(x⁻¹ * y * x) * s * (x⁻¹ * y * x)⁻¹, h.conj_mem_S₄ hy' hs, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hM2 : IsPGroup 2 M := (h.isPGroup_P.to_le hS4P).map _
  exact h.le_S₄_of_normal hML hMn hM2 ⟨s, hs, rfl⟩

theorem conj_mem_S₄_sup_Tsyl_of_mem {x : G} (hx : x ∈ h.C ⊓ centralizer ({h.f} : Set G))
    {y : G} (hy : y ∈ h.S₄ ⊔ h.Tsyl) : x * y * x⁻¹ ∈ h.S₄ ⊔ h.Tsyl := by
  obtain ⟨s, hs, c, hc, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer
    h.Tsyl_le_centralizer_S₄ hy
  rw [show x * (s * c) * x⁻¹ = (x * s * x⁻¹) * (x * c * x⁻¹) by group]
  exact mul_mem (mem_sup_left (h.conj_mem_S₄_of_mem hx hs))
    (mem_sup_right (h.conj_mem_Tsyl (mem_inf.1 hx).1 hc))

theorem f_mem_L : h.f ∈ h.L :=
  h.P_le_L (h.V_le_P .i10 h.e_f_mem_orderOf.2.1)

theorem e_mem_L : h.e ∈ h.L :=
  h.P_le_L (h.V_le_P .i12 h.e_f_mem_orderOf.1)

theorem Tsyl_le_X : h.Tsyl ≤ h.C ⊓ centralizer ({h.f} : Set G) := fun _ hc =>
  mem_inf.2 ⟨(mem_inf.1 hc).2, mem_centralizer_singleton_iff.2
    (mem_centralizer_iff.1 (mem_inf.1 hc).1 h.f h.f_mem_L).symm⟩

theorem S₄_sup_Tsyl_le_X : h.S₄ ⊔ h.Tsyl ≤ h.C ⊓ centralizer ({h.f} : Set G) := by
  refine sup_le (fun s hs => ?_) h.Tsyl_le_X
  have := h.S₄_le hs
  exact mem_inf.2 ⟨h.L_le_C (mem_inf.1 this).1, (mem_inf.1 this).2⟩

theorem conj_mem_S₄_sup_Tsyl {g : G}
    (hg : ∀ x ∈ h.C ⊓ centralizer ({h.f} : Set G), g * x * g⁻¹ ∈ h.C ⊓ centralizer ({h.f} : Set G))
    (hg' : ∀ x ∈ h.C ⊓ centralizer ({h.f} : Set G),
      g⁻¹ * x * g ∈ h.C ⊓ centralizer ({h.f} : Set G))
    {y : G} (hy : y ∈ h.S₄ ⊔ h.Tsyl) : g * y * g⁻¹ ∈ h.S₄ ⊔ h.Tsyl := by
  set X := h.C ⊓ centralizer ({h.f} : Set G) with hX
  set U := (h.S₄ ⊔ h.Tsyl).map (MulAut.conj g).toMonoidHom with hU
  have hUmem : ∀ {u : G}, u ∈ U ↔ g⁻¹ * u * g ∈ h.S₄ ⊔ h.Tsyl := fun {u} => by
    constructor
    · rintro ⟨y, hy, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rwa [show g⁻¹ * (g * y * g⁻¹) * g = y by group]
    · intro hu
      exact ⟨g⁻¹ * u * g, hu, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
  have hUX : U ≤ X := by
    rintro _ ⟨y, hy, rfl⟩
    exact hg y (h.S₄_sup_Tsyl_le_X hy)
  have hU2 : IsPGroup 2 U := h.isPGroup_S₄_sup_Tsyl.map _
  have hXU : ∀ x ∈ X, ∀ u ∈ U, x * u * x⁻¹ ∈ U := by
    intro x hx u hu
    rw [hUmem] at hu ⊢
    have := h.conj_mem_S₄_sup_Tsyl_of_mem (hg' x hx) hu
    rwa [show g⁻¹ * x * g * (g⁻¹ * u * g) * (g⁻¹ * x * g)⁻¹ = g⁻¹ * (x * u * x⁻¹) * g by group]
      at this
  have hTU : h.Tsyl ≤ normalizer (U : Set G) := fun c hc =>
    mem_normalizer_iff.2 fun u => ⟨fun hu => hXU c (h.Tsyl_le_X hc) u hu, fun hu => by
      have := hXU c⁻¹ (inv_mem (h.Tsyl_le_X hc)) _ hu
      rwa [inv_inv, show c⁻¹ * (c * u * c⁻¹) * c = u by group] at this⟩
  have hUT2 : IsPGroup 2 (U ⊔ h.Tsyl : Subgroup G) :=
    hU2.to_sup_of_normal_left' h.isPGroup_kernel hTU
  have hUTX : U ⊔ h.Tsyl ≤ X := sup_le hUX h.Tsyl_le_X
  set M := (U ⊔ h.Tsyl) ⊓ h.L with hM
  have hCLfX : h.L ⊓ centralizer ({h.f} : Set G) ≤ X := fun y hy =>
    mem_inf.2 ⟨h.L_le_C (mem_inf.1 hy).1, (mem_inf.1 hy).2⟩
  have hXUT : ∀ x ∈ X, x ∈ normalizer ((U ⊔ h.Tsyl : Subgroup G) : Set G) := by
    intro x hx
    refine inf_normalizer_le_normalizer_sup U h.Tsyl (mem_inf.2 ⟨?_, ?_⟩)
    · exact mem_normalizer_iff.2 fun u => ⟨fun hu => hXU x hx u hu, fun hu => by
        have := hXU x⁻¹ (inv_mem hx) _ hu
        rwa [inv_inv, show x⁻¹ * (x * u * x⁻¹) * x = u by group] at this⟩
    · exact mem_normalizer_iff.2 fun c => ⟨fun hc => h.conj_mem_Tsyl (mem_inf.1 hx).1 hc,
        fun hc => by
          have := h.conj_mem_Tsyl (inv_mem (mem_inf.1 hx).1) hc
          rwa [inv_inv, show x⁻¹ * (x * c * x⁻¹) * x = c by group] at this⟩
  have hMle : M ≤ h.L ⊓ centralizer ({h.f} : Set G) := fun m hm =>
    mem_inf.2 ⟨(mem_inf.1 hm).2, (mem_inf.1 (hUTX (mem_inf.1 hm).1)).2⟩
  have hMn : ∀ y ∈ h.L ⊓ centralizer ({h.f} : Set G), ∀ m ∈ M, y * m * y⁻¹ ∈ M := by
    intro y hy m hm
    refine mem_inf.2 ⟨(mem_normalizer_iff.1 (hXUT y (hCLfX hy)) m).1 (mem_inf.1 hm).1, ?_⟩
    exact h.conj_mem_L (h.L_le_C (mem_inf.1 hy).1) (mem_inf.1 hm).2
  have hM2 : IsPGroup 2 M := hUT2.to_le inf_le_left
  have hMS4 := h.le_S₄_of_normal hMle hMn hM2
  have hu : g * y * g⁻¹ ∈ U := hUmem.2 (by rwa [show g⁻¹ * (g * y * g⁻¹) * g = y by group])
  have huLT := h.le_sup_of_isPGroup (hUX.trans inf_le_left) hU2 hu
  obtain ⟨l, hl, c, hc, hlc⟩ := exists_mul_of_mem_sup_of_le_centralizer
    (fun _ hc => (mem_inf.1 hc).1) huLT
  have hlM : l ∈ M := by
    refine mem_inf.2 ⟨?_, hl⟩
    rw [show l = (g * y * g⁻¹) * c⁻¹ by rw [hlc]; group]
    exact mul_mem (mem_sup_left hu) (mem_sup_right (inv_mem hc))
  rw [hlc]
  exact mul_mem (mem_sup_left (hMS4 hlM)) (mem_sup_right hc)

theorem conj_mem_S₂ {g : G}
    (hg : ∀ x ∈ h.C ⊓ centralizer ({h.f} : Set G), g * x * g⁻¹ ∈ h.C ⊓ centralizer ({h.f} : Set G))
    (hg' : ∀ x ∈ h.C ⊓ centralizer ({h.f} : Set G),
      g⁻¹ * x * g ∈ h.C ⊓ centralizer ({h.f} : Set G))
    {s : G} (hs : s ∈ h.S₂) : g * s * g⁻¹ ∈ h.S₂ := by
  set X := h.C ⊓ centralizer ({h.f} : Set G) with hX
  obtain ⟨-, h23, h34, -, -, -⟩ := h.S₁_le_S₂_le_S₃_le_S₄_le_S
  have hS24 : h.S₂ ≤ h.S₄ := h23.trans h34
  have hsc : ∀ y ∈ h.S₄ ⊔ h.Tsyl, s * y = y * s := by
    intro y hy
    obtain ⟨w, hw, c, hc, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer
      h.Tsyl_le_centralizer_S₄ hy
    have h1 := h.S₂_commute hs hw
    have h2 : c * s = s * c :=
      (mem_centralizer_iff.1 (h.Tsyl_le_centralizer_S₄ hc) s (hS24 hs)).symm
    calc s * (w * c) = w * s * c := by rw [← mul_assoc, h1]
      _ = w * c * s := by rw [mul_assoc, ← h2, ← mul_assoc]
  set u := g * s * g⁻¹ with hu
  have huY : u ∈ h.S₄ ⊔ h.Tsyl := h.conj_mem_S₄_sup_Tsyl hg hg' (mem_sup_left (hS24 hs))
  have huc : ∀ y ∈ h.S₄ ⊔ h.Tsyl, u * y = y * u := by
    intro y hy
    have hy' := h.conj_mem_S₄_sup_Tsyl (g := g⁻¹) (fun x hx => by rw [inv_inv]; exact hg' x hx)
      (fun x hx => by rw [inv_inv]; exact hg x hx) hy
    rw [inv_inv] at hy'
    have := hsc _ hy'
    calc u * y = g * (s * (g⁻¹ * y * g)) * g⁻¹ := by rw [hu]; group
      _ = g * ((g⁻¹ * y * g) * s) * g⁻¹ := by rw [this]
      _ = y * u := by rw [hu]; group
  obtain ⟨s', hs', c, hc, hsc'⟩ := exists_mul_of_mem_sup_of_le_centralizer
    h.Tsyl_le_centralizer_S₄ huY
  have hcs' : c * s' = s' * c := (mem_centralizer_iff.1 (h.Tsyl_le_centralizer_S₄ hc) s' hs').symm
  have hs'S₂ : s' ∈ h.S₂ := by
    refine h.mem_S₂_of_commute hs' fun w hw => ?_
    have h1 := huc w (mem_sup_left hw)
    rw [hsc'] at h1
    have hcw : c * w = w * c := (mem_centralizer_iff.1 (h.Tsyl_le_centralizer_S₄ hc) w hw).symm
    have : s' * c * w = w * s' * c := h1.trans (by group)
    calc w * s' = w * s' * c * c⁻¹ := by group
      _ = s' * c * w * c⁻¹ := by rw [this]
      _ = s' * w := by rw [mul_assoc s', hcw]; group
  have hu2 : u * u = 1 := by
    rw [hu]
    calc g * s * g⁻¹ * (g * s * g⁻¹) = g * (s * s) * g⁻¹ := by group
      _ = 1 := by rw [h.mul_self_of_mem_S₂ hs]; group
  have hc2 : c * c = 1 := by
    have h1 : s' * c * (s' * c) = 1 := by rw [← hsc']; exact hu2
    calc c * c = (s' * s') * (c * c) := by rw [h.mul_self_of_mem_S₂ hs'S₂, one_mul]
      _ = s' * c * (s' * c) := by
          rw [show s' * c * (s' * c) = s' * (c * s') * c by group, hcs']; group
      _ = 1 := h1
  have huX' : u ∈ ⁅X, X⁆ := by
    have hX'' : (⁅X, X⁆ : Subgroup G).map (MulAut.conj g).toMonoidHom ≤ ⁅X, X⁆ := by
      rw [map_commutator]
      have hXX : X.map (MulAut.conj g).toMonoidHom ≤ X := by
        rintro _ ⟨x, hx, rfl⟩
        exact hg x hx
      exact commutator_mono hXX hXX
    exact hX'' ⟨s, h.S₂_le_commutator hs, rfl⟩
  have hc1 : c = 1 := by
    by_contra hc1
    have hct : c = h.t := h.eq_t_of_mem_kernel hc (orderOf_eq_prime (by rw [sq]; exact hc2) hc1)
    apply h.t_not_mem_commutator (X := X) inf_le_left
    have : h.t = s'⁻¹ * u := by rw [hsc', hct]; group
    rw [this]
    exact mul_mem (inv_mem (h.S₂_le_commutator hs'S₂)) huX'
  rw [hsc', hc1, mul_one]
  exact hs'S₂

theorem conj_mem_X_of {g : G} (hgt : g * h.t * g⁻¹ = h.t * h.f) (hgf : g * h.f * g⁻¹ = h.f)
    {x : G} (hx : x ∈ h.C ⊓ centralizer ({h.f} : Set G)) :
    g * x * g⁻¹ ∈ h.C ⊓ centralizer ({h.f} : Set G) := by
  have hxt : x * h.t = h.t * x := h.commute_t (mem_inf.1 hx).1
  have hxf : x * h.f = h.f * x := mem_centralizer_singleton_iff.1 (mem_inf.1 hx).2
  have hff : h.f * h.f = 1 := by rw [← sq, ← h.e_f_mem_orderOf.2.2.2, pow_orderOf_eq_one]
  have hf' : g * x * g⁻¹ * h.f = h.f * (g * x * g⁻¹) := by
    rw [← hgf]
    calc g * x * g⁻¹ * (g * h.f * g⁻¹) = g * (x * h.f) * g⁻¹ := by group
      _ = g * (h.f * x) * g⁻¹ := by rw [hxf]
      _ = g * h.f * g⁻¹ * (g * x * g⁻¹) := by group
  have htf' : g * x * g⁻¹ * (h.t * h.f) = h.t * h.f * (g * x * g⁻¹) := by
    rw [← hgt]
    calc g * x * g⁻¹ * (g * h.t * g⁻¹) = g * (x * h.t) * g⁻¹ := by group
      _ = g * (h.t * x) * g⁻¹ := by rw [hxt]
      _ = g * h.t * g⁻¹ * (g * x * g⁻¹) := by group
  refine mem_inf.2 ⟨mem_centralizer_singleton_iff.2 ?_, mem_centralizer_singleton_iff.2 hf'⟩
  have ht : h.t = h.t * h.f * h.f := by rw [mul_assoc, hff, mul_one]
  rw [ht]
  calc g * x * g⁻¹ * (h.t * h.f * h.f) = (g * x * g⁻¹ * (h.t * h.f)) * h.f := by group
    _ = h.t * h.f * (g * x * g⁻¹ * h.f) := by rw [htf']; group
    _ = h.t * h.f * h.f * (g * x * g⁻¹) := by rw [hf']; group

theorem exists_conj_te_of_conj_tf {g₁ : G} (hg₁ : g₁ * h.t * g₁⁻¹ = h.t * h.f) :
    ∃ g : G, g * h.t * g⁻¹ = h.t * h.e := by
  by_contra hno
  push Not at hno
  obtain ⟨hfS₂, hfS₁, heS₁, x₀, hx₀, hx₀1, hx₀e⟩ := h.f_mem_S₂_e_mem_S₁
  obtain ⟨h12, h23, h34, -, -, -⟩ := h.S₁_le_S₂_le_S₃_le_S₄_le_S
  have hS₁₄ : h.S₁ ≤ h.S₄ := h12.trans (h23.trans h34)
  have hS₂₄ : h.S₂ ≤ h.S₄ := h23.trans h34
  have hcomm₂ : ∀ {u w : G}, u ∈ h.S₂ → w ∈ h.S₂ → u * w = w * u :=
    fun hu hw => h.S₂_commute hu (hS₂₄ hw)
  have htL : ∀ {u : G}, u ∈ h.S₂ → u * h.t = h.t * u := fun hu =>
    h.commute_t_of_mem_L (h.S₄_le_L (hS₂₄ hu))
  set α := h.elt (sylowD h.a h.K 1 0) with hα
  have hαL : α ∈ h.L := h.P_le_L h.elt_sylowD_mem_P
  have hαt : α * h.t = h.t * α := h.commute_t_of_mem_L hαL
  have hαf : α * h.f * α⁻¹ = h.e * h.f := h.conj_f_eq
  have hαe : α * h.e = h.e * α := h.commute_e h.elt_sylowD_mem_P
  have hfe : h.f * h.e = h.e * h.f := hcomm₂ hfS₂ (h12 heS₁)
  have hee : h.e * h.e = 1 := h.mul_self_of_mem_S₂ (h12 heS₁)
  have hft : h.f * h.t = h.t * h.f := htL hfS₂
  have het : h.e * h.t = h.t * h.e := htL (h12 heS₁)
  have hα1 : α * (h.t * h.f) * α⁻¹ = h.t * h.f * h.e := by
    calc α * (h.t * h.f) * α⁻¹ = (α * h.t) * h.f * α⁻¹ := by group
      _ = h.t * (α * h.f * α⁻¹) := by rw [hαt]; group
      _ = h.t * h.f * h.e := by rw [hαf, ← hfe]; group
  have hα2 : α * (h.t * h.f * h.e) * α⁻¹ = h.t * h.f := by
    calc α * (h.t * h.f * h.e) * α⁻¹ = α * (h.t * h.f) * α⁻¹ * (α * h.e * α⁻¹) := by group
      _ = h.t * h.f * (h.e * h.e) := by
          rw [hα1, show α * h.e * α⁻¹ = h.e by rw [hαe]; group]; group
      _ = h.t * h.f := by rw [hee, mul_one]
  set g' := g₁⁻¹ * α * g₁ with hg'
  have hg't : g' * h.t * g'⁻¹ = g₁⁻¹ * (h.t * h.f * h.e) * g₁ := by
    rw [hg', ← hα1, ← hg₁]
    group
  have hh₁ : g₁⁻¹ * (h.t * h.f) * g₁ = h.t := by rw [← hg₁]; group
  have hzw : h.t * h.f * h.e * (h.t * h.f) = h.t * h.f * (h.t * h.f * h.e) := by
    calc h.t * h.f * h.e * (h.t * h.f) = h.t * h.f * (h.e * h.t) * h.f := by group
      _ = h.t * h.f * h.t * (h.e * h.f) := by rw [het]; group
      _ = h.t * h.f * h.t * (h.f * h.e) := by rw [hfe]
      _ = h.t * h.f * (h.t * h.f * h.e) := by group
  have hconjC : ∀ z, z * (h.t * h.f) = (h.t * h.f) * z → g₁⁻¹ * z * g₁ ∈ h.C := fun z hz => by
    rw [mem_centralizer_singleton_iff]
    calc g₁⁻¹ * z * g₁ * h.t = g₁⁻¹ * z * g₁ * (g₁⁻¹ * (h.t * h.f) * g₁) := by rw [hh₁]
      _ = g₁⁻¹ * (z * (h.t * h.f)) * g₁ := by group
      _ = g₁⁻¹ * ((h.t * h.f) * z) * g₁ := by rw [hz]
      _ = g₁⁻¹ * (h.t * h.f) * g₁ * (g₁⁻¹ * z * g₁) := by group
      _ = h.t * (g₁⁻¹ * z * g₁) := by rw [hh₁]
  have hg'C : g' * h.t * g'⁻¹ ∈ h.C := by
    rw [hg't]
    exact hconjC _ hzw
  have he1 : h.e ≠ 1 := fun e1 => by
    have := h.e_f_mem_orderOf.2.2.1
    rw [e1, orderOf_one] at this
    exact absurd this (by norm_num)
  have hg'ne : g' * h.t * g'⁻¹ ≠ h.t := by
    rw [hg't]
    intro e
    apply he1
    have h1 : h.t * h.f * h.e = h.t * h.f := mul_left_cancel (mul_right_cancel (e.trans hh₁.symm))
    calc h.e = (h.t * h.f)⁻¹ * (h.t * h.f * h.e) := by group
      _ = 1 := by rw [h1]; group
  obtain ⟨k, hk, hke | hkf⟩ := h.exists_conj_te_or_tf hg'C hg'ne
  · exact hno _ hke
  set w := k * g₁⁻¹ with hw
  have hkt : k * h.t * k⁻¹ = h.t := by rw [h.commute_t_of_mem_L hk]; group
  have hw1 : w * (h.t * h.f) * w⁻¹ = h.t := by
    rw [hw, show k * g₁⁻¹ * (h.t * h.f) * (k * g₁⁻¹)⁻¹ = k * (g₁⁻¹ * (h.t * h.f) * g₁) * k⁻¹ by
      group, hh₁, hkt]
  have hw2 : w * (h.t * h.f * h.e) * w⁻¹ = h.t * h.f := by
    calc w * (h.t * h.f * h.e) * w⁻¹ = k * (g₁⁻¹ * (h.t * h.f * h.e) * g₁) * k⁻¹ := by
          rw [hw]; group
      _ = k * g' * h.t * (k * g')⁻¹ := by rw [← hg't]; group
      _ = h.t * h.f := hkf
  set g := w * α * w⁻¹ with hg
  have hwt : w⁻¹ * h.t * w = h.t * h.f := by
    calc w⁻¹ * h.t * w = w⁻¹ * (w * (h.t * h.f) * w⁻¹) * w := by rw [hw1]
      _ = h.t * h.f := by group
  have hwtfe : w⁻¹ * (h.t * h.f) * w = h.t * h.f * h.e := by
    calc w⁻¹ * (h.t * h.f) * w = w⁻¹ * (w * (h.t * h.f * h.e) * w⁻¹) * w := by rw [hw2]
      _ = h.t * h.f * h.e := by group
  have hgt : g * h.t * g⁻¹ = h.t * h.f := by
    rw [hg, show w * α * w⁻¹ * h.t * (w * α * w⁻¹)⁻¹ = w * (α * (w⁻¹ * h.t * w) * α⁻¹) * w⁻¹ by
      group, hwt, hα1, hw2]
  have hgtf : g * (h.t * h.f) * g⁻¹ = h.t := by
    rw [hg, show w * α * w⁻¹ * (h.t * h.f) * (w * α * w⁻¹)⁻¹ =
      w * (α * (w⁻¹ * (h.t * h.f) * w) * α⁻¹) * w⁻¹ by group, hwtfe, hα2, hw1]
  have hgf : g * h.f * g⁻¹ = h.f := by
    calc g * h.f * g⁻¹ = g * (h.t * h.t) * h.f * g⁻¹ := by rw [h.t_mul_t, mul_one]
      _ = (g * h.t * g⁻¹) * (g * (h.t * h.f) * g⁻¹) := by group
      _ = h.t * h.f * h.t := by rw [hgt, hgtf]
      _ = h.f := by rw [mul_assoc, hft, ← mul_assoc, h.t_mul_t, one_mul]
  have hg't' : g⁻¹ * h.t * g⁻¹⁻¹ = h.t * h.f := by
    rw [inv_inv]
    calc g⁻¹ * h.t * g = g⁻¹ * (g * (h.t * h.f) * g⁻¹) * g := by rw [hgtf]
      _ = h.t * h.f := by group
  have hg'f : g⁻¹ * h.f * g⁻¹⁻¹ = h.f := by
    rw [inv_inv]
    calc g⁻¹ * h.f * g = g⁻¹ * (g * h.f * g⁻¹) * g := by rw [hgf]
      _ = h.f := by group
  have hgX := fun x hx => h.conj_mem_X_of hgt hgf (x := x) hx
  have hgX' : ∀ x ∈ h.C ⊓ centralizer ({h.f} : Set G),
      g⁻¹ * x * g ∈ h.C ⊓ centralizer ({h.f} : Set G) := fun x hx => by
    have := h.conj_mem_X_of hg't' hg'f hx
    rwa [inv_inv] at this
  have hmap : ∀ e' ∈ h.S₁, e' ≠ 1 → ∃ e'' ∈ h.S₁, g * (h.t * e') * g⁻¹ = h.t * e'' := by
    intro e' he' he'1
    obtain ⟨m, hm, hme⟩ := h.exists_conj_e_of_mem_S₁ he' he'1
    have hmt : m * h.t * m⁻¹ = h.t := by rw [h.commute_t_of_mem_L hm]; group
    have hconj : m * g⁻¹ * (g * (h.t * e') * g⁻¹) * (m * g⁻¹)⁻¹ = h.t * h.e := by
      rw [← hme, show m * g⁻¹ * (g * (h.t * e') * g⁻¹) * (m * g⁻¹)⁻¹ =
        (m * h.t * m⁻¹) * (m * e' * m⁻¹) by group, hmt]
    set s' := g * e' * g⁻¹ with hs'
    have hs'S₂ : s' ∈ h.S₂ := h.conj_mem_S₂ hgX hgX' (h12 he')
    set v := h.f * s' with hv
    have hvS₂ : v ∈ h.S₂ := mul_mem hfS₂ hs'S₂
    have hgte : g * (h.t * e') * g⁻¹ = h.t * v := by
      calc g * (h.t * e') * g⁻¹ = (g * h.t * g⁻¹) * (g * e' * g⁻¹) := by group
        _ = h.t * v := by rw [hgt, hv, ← hs', mul_assoc]
    by_cases hv1 : v = 1
    · exfalso
      rw [hv1, mul_one] at hgte
      rw [hgte] at hconj
      exact hno _ hconj
    by_cases hvS₁ : v ∈ h.S₁
    · exact ⟨v, hvS₁, hgte⟩
    · exfalso
      obtain ⟨m', hm', hm'v⟩ := h.exists_conj_f_of_mem_S₂ hvS₂ hvS₁
      have hm't : m' * h.t * m'⁻¹ = h.t := by rw [h.commute_t_of_mem_L hm']; group
      apply hno (m * g⁻¹ * (m'⁻¹ * g₁))
      rw [← hconj, hgte]
      have hm't' : m'⁻¹ * h.t * m' = h.t := by
        calc m'⁻¹ * h.t * m' = m'⁻¹ * (m' * h.t * m'⁻¹) * m' := by rw [hm't]
          _ = h.t := by group
      have h1 : h.t * v = m'⁻¹ * (h.t * h.f) * m' := by
        rw [← hm'v, show m'⁻¹ * (h.t * (m' * v * m'⁻¹)) * m' =
          (m'⁻¹ * h.t * m') * v by group, hm't']
      rw [h1, ← hg₁]
      group
  obtain ⟨e₁, he₁, hge₁⟩ := hmap h.e heS₁ he1
  obtain ⟨e₂, he₂, hge₂⟩ := hmap x₀ hx₀ hx₀1
  have hex₀ : h.e * x₀ ∈ h.S₁ := mul_mem heS₁ hx₀
  have hex₀1 : h.e * x₀ ≠ 1 := fun e => hx₀e (by
    calc x₀ = h.e * (h.e * x₀) := by rw [← mul_assoc, hee, one_mul]
      _ = h.e := by rw [e, mul_one])
  obtain ⟨e₃, he₃, hge₃⟩ := hmap (h.e * x₀) hex₀ hex₀1
  have hx₀t := htL (h12 hx₀)
  have hcomm₁ : h.e * x₀ = x₀ * h.e := hcomm₂ (h12 heS₁) (h12 hx₀)
  have hxx : x₀ * x₀ = 1 := h.mul_self_of_mem_S₂ (h12 hx₀)
  have ht3 : h.t = (h.t * h.e) * (h.t * x₀) * (h.t * (h.e * x₀)) := by
    calc h.t = h.t * (h.t * h.t) * (h.e * h.e) * (x₀ * x₀) := by
          rw [h.t_mul_t, hee, hxx]; group
      _ = (h.t * h.e) * (h.t * x₀) * (h.t * (h.e * x₀)) := by
          rw [show (h.t * h.e) * (h.t * x₀) * (h.t * (h.e * x₀)) =
            h.t * (h.e * h.t) * (x₀ * h.t) * h.e * x₀ by group, het, hx₀t]
          rw [show h.t * (h.t * h.e) * (h.t * x₀) * h.e * x₀ =
            h.t * h.t * h.e * h.t * (x₀ * h.e) * x₀ by group, ← hcomm₁,
            show h.t * h.t * h.e * h.t * (h.e * x₀) * x₀ = h.t * h.t * (h.e * h.t) * h.e * x₀ * x₀
              by group, het]
          group
  have hfin : h.t * h.f = h.t * (e₁ * e₂ * e₃) := by
    rw [← hgt]
    conv_lhs => rw [ht3]
    rw [show g * (h.t * h.e * (h.t * x₀) * (h.t * (h.e * x₀))) * g⁻¹ =
      (g * (h.t * h.e) * g⁻¹) * (g * (h.t * x₀) * g⁻¹) * (g * (h.t * (h.e * x₀)) * g⁻¹) by group,
      hge₁, hge₂, hge₃]
    have h1t := htL (h12 he₁)
    have h2t := htL (h12 he₂)
    calc h.t * e₁ * (h.t * e₂) * (h.t * e₃) = h.t * (e₁ * h.t) * (e₂ * h.t) * e₃ := by group
      _ = h.t * (h.t * e₁) * (h.t * e₂) * e₃ := by rw [h1t, h2t]
      _ = h.t * h.t * e₁ * h.t * e₂ * e₃ := by group
      _ = h.t * h.t * (e₁ * h.t) * e₂ * e₃ := by group
      _ = h.t * h.t * (h.t * e₁) * e₂ * e₃ := by rw [h1t]
      _ = h.t * (h.t * h.t) * e₁ * e₂ * e₃ := by group
      _ = h.t * (e₁ * e₂ * e₃) := by rw [h.t_mul_t]; group
  have hf : h.f = e₁ * e₂ * e₃ := mul_left_cancel hfin
  exact hfS₁ (hf ▸ mul_mem (mul_mem he₁ he₂) he₃)

theorem V12_le_S₁ : h.V .i12 ≤ h.S₁ := h.pull_mono (rootV_le_rootJoin (by decide))

theorem H_le_L : h.H ≤ h.L := h.pull_le_L _

theorem exists_mul_of_mem_center_P_sup_Tsyl {z : G} (hz : z ∈ h.P ⊔ h.Tsyl)
    (hc : ∀ y ∈ h.P ⊔ h.Tsyl, y * z = z * y) : ∃ v ∈ h.V .i12, ∃ c ∈ h.Tsyl, z = v * c := by
  have hTP : h.Tsyl ≤ centralizer (h.P : Set G) := fun _ hc =>
    centralizer_le (fun _ hx => h.P_le_L hx) (mem_inf.1 hc).1
  obtain ⟨p, hp, c, hc', rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hTP hz
  refine ⟨p, h.mem_V12_of_commute_P hp fun w hw => ?_, c, hc', rfl⟩
  have h1 := hc w (mem_sup_left hw)
  have hcw : c * w = w * c := (mem_centralizer_iff.1 (hTP hc') w hw).symm
  calc w * p = w * (p * c) * c⁻¹ := by group
    _ = p * c * w * c⁻¹ := by rw [h1]
    _ = p * w := by rw [mul_assoc p, hcw]; group

theorem sec3_1_of_conj_te {g : G} (hg : g * h.t * g⁻¹ = h.t * h.e) :
    h.Tsyl = zpowers h.t ∧ ∀ v ∈ h.V .i12,
      ∃ n ∈ normalizer ((h.P ⊔ zpowers h.t : Subgroup G) : Set G), n * h.t * n⁻¹ = h.t * v := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set PT := h.P ⊔ h.Tsyl with hPT
  obtain ⟨hPTC, hPT2, hidx⟩ := isSylowOf_iff.1 h.isSylowOf_P_sup_Tsyl
  have heL := h.e_mem_L
  have hPTte : PT ≤ centralizer ({h.t * h.e} : Set G) := by
    refine sup_le (fun p hp => ?_) (fun c hc => ?_)
    · rw [mem_centralizer_singleton_iff]
      have h1 := h.commute_t (h.P_le_C hp)
      have h2 := h.commute_e hp
      calc p * (h.t * h.e) = h.t * (p * h.e) := by rw [← mul_assoc, h1, mul_assoc]
        _ = h.t * h.e * p := by rw [h2, mul_assoc]
    · rw [mem_centralizer_singleton_iff]
      have h1 := h.commute_t (mem_inf.1 hc).2
      have h2 : h.e * c = c * h.e := mem_centralizer_iff.1 (mem_inf.1 hc).1 h.e heL
      calc c * (h.t * h.e) = h.t * (c * h.e) := by rw [← mul_assoc, h1, mul_assoc]
        _ = h.t * h.e * c := by rw [← h2, mul_assoc]
  obtain ⟨n, hn, hnt⟩ := CFSG.Monster.B.Recog.exists_mem_normalizer_conj_eq hPT2 hPTC hPTte hidx
    (isConj_iff.2 ⟨g, hg⟩)
  have hnZ : ∀ u ∈ h.Tsyl, ∃ v ∈ h.V .i12, ∃ c ∈ h.Tsyl, n * u * n⁻¹ = v * c := by
    intro u hu
    refine h.exists_mul_of_mem_center_P_sup_Tsyl
      ((mem_normalizer_iff.1 hn u).1 (mem_sup_right hu)) fun y hy => ?_
    have hy' : n⁻¹ * y * n ∈ PT := by
      have := (mem_normalizer_iff.1 (inv_mem hn) y).1 hy
      rwa [inv_inv] at this
    have hc : u * (n⁻¹ * y * n) = (n⁻¹ * y * n) * u := by
      obtain ⟨p, hp, c, hc, hpc⟩ := exists_mul_of_mem_sup_of_le_centralizer
        (fun _ hc => centralizer_le (fun _ hx => h.P_le_L hx) (mem_inf.1 hc).1) hy'
      rw [hpc]
      have h1 : p * u = u * p := mem_centralizer_iff.1 (mem_inf.1 hu).1 p (h.P_le_L hp)
      have h2 : u * c = c * u := h.kernel_comm hu hc
      calc u * (p * c) = p * (u * c) := by rw [← mul_assoc, ← h1, mul_assoc]
        _ = p * c * u := by rw [h2, mul_assoc]
    calc y * (n * u * n⁻¹) = n * ((n⁻¹ * y * n) * u) * n⁻¹ := by group
      _ = n * (u * (n⁻¹ * y * n)) * n⁻¹ := by rw [hc]
      _ = n * u * n⁻¹ * y := by group
  have he1 : h.e ≠ 1 := fun e1 => by
    have := h.e_f_mem_orderOf.2.2.1
    rw [e1, orderOf_one] at this
    exact absurd this (by norm_num)
  have hT2 : Nat.card h.Tsyl = 2 := by
    by_contra hne
    obtain ⟨K, hK⟩ := IsPGroup.iff_card.1 h.isPGroup_kernel
    have hK' : Nat.card h.Tsyl = 2 ^ K := hK
    have hK2 : 2 ≤ K := by
      rcases K with _ | _ | K
      · exfalso
        rw [pow_zero] at hK'
        have : (⟨h.t, h.t_mem_Tsyl⟩ : h.Tsyl) = 1 :=
          Subsingleton.elim (h := (Nat.card_eq_one_iff_unique.1 hK').1) _ _
        exact h.t_ne_one (congrArg Subtype.val this)
      · exact absurd (by rw [hK', pow_one]) hne
      · omega
    have := h.isCyclic_Tsyl
    obtain ⟨c, hc⟩ := IsCyclic.exists_generator (α := h.Tsyl)
    have hco : orderOf c = 2 ^ K := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hc]
      exact hK'
    obtain ⟨m, hm⟩ := mem_zpowers_iff.1 (hc ⟨h.t, h.t_mem_Tsyl⟩)
    have hmeven : Even m := by
      by_contra hodd
      rw [Int.not_even_iff_odd] at hodd
      have h1 : c ^ (2 * m) = 1 := by
        rw [mul_comm, zpow_mul, hm, zpow_two]
        exact Subtype.ext h.t_mul_t
      have h2 := orderOf_dvd_iff_zpow_eq_one.2 h1
      rw [hco] at h2
      have h3 : (4 : ℕ) ∣ 2 ^ K := by
        have := pow_dvd_pow 2 hK2
        norm_num at this
        exact this
      have h4 : (4 : ℤ) ∣ 2 * m := (Int.natCast_dvd_natCast.2 h3).trans (by exact_mod_cast h2)
      obtain ⟨j, hj⟩ := hodd
      omega
    obtain ⟨j, hj⟩ := hmeven
    set u := ((c ^ j : h.Tsyl) : G) with hu
    have hu2 : u * u = h.t := by
      rw [hu, ← coe_mul, ← zpow_add, ← hj, hm]
    obtain ⟨v, hv, c', hc', hnu⟩ := hnZ u (c ^ j).2
    have hvc : v * c' = c' * v := mem_centralizer_iff.1 (mem_inf.1 hc').1 v (h.pull_le_L _ hv)
    have hvv : v * v = 1 :=
      h.mul_self_of_mem_S₂ (h.S₁_le_S₂_le_S₃_le_S₄_le_S.1 (h.V12_le_S₁ hv))
    have hte : h.t * h.e = c' * c' := by
      have e1 : n * h.t * n⁻¹ = (n * u * n⁻¹) * (n * u * n⁻¹) := by
        rw [← hu2]
        group
      rw [← hnt, e1, hnu]
      calc v * c' * (v * c') = v * (c' * v) * c' := by group
        _ = v * (v * c') * c' := by rw [hvc]
        _ = (v * v) * (c' * c') := by simp only [mul_assoc]
        _ = c' * c' := by rw [hvv, one_mul]
    have heT : h.e ∈ h.Tsyl := by
      have : h.e = h.t⁻¹ * (c' * c') := by rw [← hte]; group
      rw [this]
      exact mul_mem (inv_mem h.t_mem_Tsyl) (mul_mem hc' hc')
    have hmem : h.e ∈ h.L ⊓ centralizer (h.L : Set G) := mem_inf.2 ⟨heL, (mem_inf.1 heT).1⟩
    rw [h.inf_centralizer_eq_bot, mem_bot] at hmem
    exact he1 hmem
  have hTt := h.Tsyl_eq_zpowers hT2
  refine ⟨hTt, fun v hv => ?_⟩
  rw [← hTt]
  by_cases hv1 : v = 1
  · exact ⟨1, one_mem _, by rw [hv1]; group⟩
  obtain ⟨x, hx, hxe⟩ := h.exists_conj_e_of_mem_V12 hv hv1
  have hxL : x ∈ h.L := h.H_le_L hx
  have hxN : x ∈ normalizer (PT : Set G) := by
    refine inf_normalizer_le_normalizer_sup h.P h.Tsyl (mem_inf.2 ⟨h.H_le_normalizer_P hx, ?_⟩)
    exact mem_normalizer_iff.2 fun c => ⟨fun hc => h.conj_mem_Tsyl (h.L_le_C hxL) hc, fun hc => by
      have := h.conj_mem_Tsyl (inv_mem (h.L_le_C hxL)) hc
      rwa [inv_inv, show x⁻¹ * (x * c * x⁻¹) * x = c by group] at this⟩
  refine ⟨x * n, mul_mem hxN hn, ?_⟩
  calc x * n * h.t * (x * n)⁻¹ = x * (n * h.t * n⁻¹) * x⁻¹ := by group
    _ = x * h.t * x⁻¹ * (x * h.e * x⁻¹) := by rw [hnt]; group
    _ = h.t * v := by rw [hxe, h.commute_t_of_mem_L hxL]; group

theorem sec3_1 :
    h.Tsyl = zpowers h.t ∧ (∀ g : G, g * h.t * g⁻¹ ∈ h.C → h.t * (g * h.t * g⁻¹) ∈ h.L) ∧
      ∀ v ∈ h.V .i12, ∃ n ∈ normalizer ((h.P ⊔ zpowers h.t : Subgroup G) : Set G),
        n * h.t * n⁻¹ = h.t * v := by
  have := h.simple
  have hZ := not_isolated_involution_of_nonabelian_simple h.nonab h.ht
  push Not at hZ
  obtain ⟨g, hgc, hgne⟩ := hZ
  have hgC : g⁻¹ * h.t * g⁻¹⁻¹ ∈ h.C := by
    rw [inv_inv]
    exact mem_centralizer_singleton_iff.2 hgc.eq
  have hgne' : g⁻¹ * h.t * g⁻¹⁻¹ ≠ h.t := by rw [inv_inv]; exact hgne
  obtain ⟨x, -, hxe | hxf⟩ := h.exists_conj_te_or_tf hgC hgne'
  · obtain ⟨hT, hN⟩ := h.sec3_1_of_conj_te hxe
    exact ⟨hT, fun g hg => h.mul_conj_mem_L hg, hN⟩
  · obtain ⟨g', hg'⟩ := h.exists_conj_te_of_conj_tf hxf
    obtain ⟨hT, hN⟩ := h.sec3_1_of_conj_te hg'
    exact ⟨hT, fun g hg => h.mul_conj_mem_L hg, hN⟩

end CaseB

end Setup

end CFSG.LocalAnalysis.EvenBN.TwoF4
