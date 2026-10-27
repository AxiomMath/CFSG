module

public import CFSG.GH74.Generic.Context
public import CFSG.GH74.Generic.Centralizer
public import CFSG.GH74.GLS.AssemblyComponents

public section

namespace CFSG.GH74.Generic

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.GH74.Filter.ClassicalOdd CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices Subgroup

@[expose] def Q8Frame (K : Type*) [Group K] : Prop :=
  ∃ φ : Q8 × Q8 →* K, Function.Injective φ ∧
    ∃ w : K, w * w = 1 ∧ ∀ g h : Q8, w * φ (g, h) * w⁻¹ = φ (h, g)

theorem IsSL4Model.q8Frame {K : Type*} [Group K] (h : IsSL4Model K) : Q8Frame K := by
  obtain ⟨z, φ, w, -, -, hφ, -, hww, hsw⟩ := h.exists_q8_frame
  exact ⟨φ, hφ, w, hww, hsw⟩

theorem Q8Frame.of_mulEquiv {K K' : Type*} [Group K] [Group K'] (h : Q8Frame K) (e : K ≃* K') :
    Q8Frame K' := by
  obtain ⟨φ, hφ, w, hww, hsw⟩ := h
  refine ⟨e.toMonoidHom.comp φ, e.injective.comp hφ, e w, ?_, fun g h => ?_⟩
  · rw [← map_mul, hww, map_one]
  · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [← map_inv, ← map_mul, ← map_mul, hsw]

section Frame

variable {G : Type} [Group G] [Finite G]

theorem central_swap_fixed {g : Q8 × Q8} (hc : ∀ a : Q8 × Q8, g * a = a * g)
    (hs : g = (g.2, g.1)) : g = 1 ∨ g = (QuaternionGroup.a 2, QuaternionGroup.a 2) := by
  have h1 : g.1 = 1 ∨ g.1 = QuaternionGroup.a 2 := quaternion_center g.1 (fun y => by
    have := congrArg Prod.fst (hc (y, 1))
    simpa using this)
  have h12 : g.1 = g.2 := congrArg Prod.fst hs
  rcases h1 with h | h
  · left
    exact Prod.ext h (h12 ▸ h)
  · right
    exact Prod.ext h (h12 ▸ h)

theorem frame_xbar_eq (hG : Gen4 G) {x : G} (hx : orderOf x = 2)
    {K : Subgroup (CentralizerBar x)} (φ : Q8 × Q8 →* ↥K) (hφ : Function.Injective φ) (w : ↥K)
    (hsw : ∀ g h : Q8, w * φ (g, h) * w⁻¹ = φ (h, g)) :
    ((φ (QuaternionGroup.a 2, QuaternionGroup.a 2) : ↥K) : CentralizerBar x) = xbar x := by
  let Φ : Q8 × Q8 →* CentralizerBar x := K.subtype.comp φ
  have hΦ : Function.Injective Φ := K.subtype_injective.comp hφ
  obtain ⟨g, hg, hgc⟩ := q8q8_commuting_two_subgroup_le_center (gen4_centralizerBar hG x) Φ hΦ
    (Subgroup.zpowers (xbar x)) (isPGroup_zpowers_of_orderOf_eq_two (orderOf_xbar hx))
    (fun a t ht => commute_of_mem_zpowers_xbar x (Φ a) ht) (xbar x) (Subgroup.mem_zpowers _)
  have hsw' : g = (g.2, g.1) := by
    apply hΦ
    have h1 : (w : CentralizerBar x) * ((φ g : ↥K) : CentralizerBar x) * (w : CentralizerBar x)⁻¹ =
        ((φ (g.2, g.1) : ↥K) : CentralizerBar x) := by
      have := congrArg (fun u : ↥K => (u : CentralizerBar x)) (hsw g.1 g.2)
      simpa using this
    change ((φ g : ↥K) : CentralizerBar x) = ((φ (g.2, g.1) : ↥K) : CentralizerBar x)
    rw [← h1]
    have hg' : ((φ g : ↥K) : CentralizerBar x) = xbar x := hg
    rw [hg']
    have hc : (w : CentralizerBar x) * xbar x = xbar x * (w : CentralizerBar x) :=
      xbar_comm x w
    rw [hc, mul_inv_cancel_right]
  rcases central_swap_fixed hgc hsw' with h | h
  · exfalso
    rw [h, map_one] at hg
    exact xbar_ne_one hx hg.symm
  · rw [h] at hg
    exact hg

theorem frame_centralizer_two_le (hG : Gen4 G) {x : G} (hx : orderOf x = 2)
    {K : Subgroup (CentralizerBar x)} (hfr : Q8Frame ↥K) (T : Subgroup (CentralizerBar x))
    (hT : IsPGroup 2 T) (hTK : T ≤ centralizer (K : Set (CentralizerBar x))) :
    T ≤ Subgroup.zpowers (xbar x) := by
  obtain ⟨φ, hφ, w, hww, hsw⟩ := hfr
  let Φ : Q8 × Q8 →* CentralizerBar x := K.subtype.comp φ
  have hΦ : Function.Injective Φ := K.subtype_injective.comp hφ
  have hxeq := frame_xbar_eq hG hx φ hφ w hsw
  intro t ht
  have hcomm : ∀ (a : Q8 × Q8) (t : CentralizerBar x), t ∈ T → Φ a * t = t * Φ a := fun a t ht =>
    Subgroup.mem_centralizer_iff.1 (hTK ht) (Φ a) (φ a).2
  obtain ⟨g, hg, hgc⟩ := q8q8_commuting_two_subgroup_le_center (gen4_centralizerBar hG x) Φ hΦ T hT
    hcomm t ht
  have hsw' : g = (g.2, g.1) := by
    apply hΦ
    have h1 : (w : CentralizerBar x) * ((φ g : ↥K) : CentralizerBar x) * (w : CentralizerBar x)⁻¹ =
        ((φ (g.2, g.1) : ↥K) : CentralizerBar x) := by
      have := congrArg (fun u : ↥K => (u : CentralizerBar x)) (hsw g.1 g.2)
      simpa using this
    change ((φ g : ↥K) : CentralizerBar x) = ((φ (g.2, g.1) : ↥K) : CentralizerBar x)
    rw [← h1]
    have hg' : ((φ g : ↥K) : CentralizerBar x) = t := hg
    rw [hg']
    have hc : (w : CentralizerBar x) * t = t * (w : CentralizerBar x) :=
      Subgroup.mem_centralizer_iff.1 (hTK ht) (w : CentralizerBar x) w.2
    rw [hc, mul_inv_cancel_right]
  rcases central_swap_fixed hgc hsw' with h | h
  · rw [h, map_one] at hg
    rw [← hg]
    exact Subgroup.one_mem _
  · rw [h] at hg
    have : t = xbar x := by rw [← hg]; exact hxeq
    rw [this]
    exact Subgroup.mem_zpowers _

theorem frame_B2 (hG : Gen4 G) {x : G} (hx : orderOf x = 2) {K : Subgroup (CentralizerBar x)}
    (hKc : IsComponent K) (hfr : Q8Frame ↥K) :
    xbar x ∈ K ∧ layer (CentralizerBar x) = K ∧
      centralizer (K : Set (CentralizerBar x)) = Subgroup.zpowers (xbar x) ∧
      pCore 2 (CentralizerBar x) = Subgroup.zpowers (xbar x) ∧
      fittingSubgroup (CentralizerBar x) = Subgroup.zpowers (xbar x) ∧
      generalizedFitting (CentralizerBar x) = K := by
  obtain ⟨φ, hφ, hw⟩ := hfr
  have hxK : xbar x ∈ K := xbar_mem_of_q8q8 hG hx φ hφ
  have hX : pPrimeCore 2 (CentralizerBar x) = ⊥ :=
    GLS.pPrimeCore_quotient_eq_bot (↥(centralizer ({x} : Set G)))
  have hT : ∀ T : Subgroup (CentralizerBar x), IsPGroup 2 T →
      T ≤ centralizer (K : Set (CentralizerBar x)) → T ≤ Subgroup.zpowers (xbar x) :=
    fun T hT hTK => frame_centralizer_two_le hG hx ⟨φ, hφ, hw⟩ T hT hTK
  have hz2 : xbar x * xbar x = 1 := xbar_mul_self hx
  have hz1 : xbar x ≠ 1 := xbar_ne_one hx
  have hzc := xbar_mem_center x
  obtain ⟨hp, hf, hfs⟩ := fitting_eq_of_centralizer hKc hzc hz2 hz1 hxK hX hT
  exact ⟨hxK, layer_eq_of_two_subgroup_le hKc hz2 hT, centralizer_eq_zpowers hKc hzc hz2 hz1 hX hT,
    hp, hf, hfs⟩

end Frame

end CFSG.GH74.Generic
