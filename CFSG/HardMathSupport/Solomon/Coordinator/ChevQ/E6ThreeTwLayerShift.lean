module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwLineDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwLayerShiftAbs

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Transport

variable {H : Type*} [Group H] (C : Subgroup H)

theorem map_conj_subgroupOf {g : C} {S S' : Subgroup H} (hS : S ≤ C)
    (h : S.map (MulAut.conj (g : H)).toMonoidHom = S') :
    (S.subgroupOf C).map (MulAut.conj g).toMonoidHom = S'.subgroupOf C := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : (y : H) ∈ S := hy
    show ((g * y * g⁻¹ : C) : H) ∈ S'
    rw [← h]
    exact ⟨y, hy', by simp [MulAut.conj_apply]⟩
  · intro hx
    have hx' : (x : H) ∈ S' := hx
    rw [← h] at hx'
    obtain ⟨y, hyS, hyx⟩ := hx'
    refine ⟨⟨y, hS hyS⟩, hyS, ?_⟩
    apply Subtype.ext
    simpa [MulAut.conj_apply] using hyx

theorem map_conj_of_subgroupOf {g : C} {S S' : Subgroup H} (hS : S ≤ C) (hS' : S' ≤ C)
    (h : (S.subgroupOf C).map (MulAut.conj g).toMonoidHom = S'.subgroupOf C) :
    S.map (MulAut.conj (g : H)).toMonoidHom = S' := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : (⟨y, hS hy⟩ : C) ∈ S.subgroupOf C := hy
    have h2 : MulAut.conj g ⟨y, hS hy⟩ ∈ (S.subgroupOf C).map (MulAut.conj g).toMonoidHom :=
      ⟨_, hy', rfl⟩
    rw [h] at h2
    have h3 : ((g * ⟨y, hS hy⟩ * g⁻¹ : C) : H) ∈ S' := h2
    simpa [MulAut.conj_apply] using h3
  · intro hx
    have hx' : (⟨x, hS' hx⟩ : C) ∈ S'.subgroupOf C := hx
    rw [← h] at hx'
    obtain ⟨y, hyS, hyx⟩ := hx'
    refine ⟨y, hyS, ?_⟩
    have := congrArg Subtype.val hyx
    simpa [MulAut.conj_apply] using this

end Transport

section Layer

variable
  {K : Type} [Field K] {σ : K ≃+* K} {h₀ : ModGL TwistTag.E6.tag K}
  {L : Fin 3 → Subgroup (ModGL TwistTag.E6.tag K)} {T : Subgroup (ModGL TwistTag.E6.tag K)}
  {n : ModGL TwistTag.E6.tag K}

theorem twLayer_injective (hL : TwE6ThreeA2Line K σ h₀ L T n) : Function.Injective L := by
  intro i j hij
  by_contra hne
  obtain ⟨a, b, hab⟩ := shiftQs_exists_noncomm (hL.L_quasisimple i)
  apply hab
  have hb : (b : ModGL TwistTag.E6.tag K) ∈ L j := by rw [← hij]; exact b.2
  exact Subtype.ext (hL.L_commute i j hne a.1 a.2 b.1 hb)

theorem twLayer_mem_centralizer {s : twistedE6RootGroup K σ}
    (hs : (s : ModGL TwistTag.E6.tag K) = h₀) {g : twistedE6RootGroup K σ}
    (hg : g ∈ Subgroup.centralizer ({s} : Set (twistedE6RootGroup K σ))) :
    (g : ModGL TwistTag.E6.tag K) ∈ twistedE6RootGroup K σ ⊓ Subgroup.centralizer {h₀} := by
  refine ⟨g.2, ?_⟩
  show (g : ModGL TwistTag.E6.tag K) ∈ Subgroup.centralizer ({h₀} : Set (ModGL TwistTag.E6.tag K))
  rw [Subgroup.mem_centralizer_singleton_iff]
  have := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hg)
  rw [← hs]
  exact this

theorem twLayer_shiftData (hL : TwE6ThreeA2Line K σ h₀ L T n) {s : twistedE6RootGroup K σ}
    (hs : (s : ModGL TwistTag.E6.tag K) = h₀) :
    ShiftData (Subgroup.centralizer ({s} : Set (twistedE6RootGroup K σ)))
      (fun i => (L i).subgroupOf (twistedE6RootGroup K σ))
      (T.subgroupOf (twistedE6RootGroup K σ)) where
  quasi i := CFSG.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe (hL.L_le i))
    (hL.L_quasisimple i)
  comm i j hij x hx y hy := Subtype.ext (hL.L_commute i j hij x.1 hx y.1 hy)
  Tcomm x hx y hy := Subtype.ext (hL.T_comm x.1 hx y.1 hy)
  Tnorm i := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro y
    exact Subgroup.mem_normalizer_iff.mp (hL.T_le_normalizer i ht) (y : ModGL TwistTag.E6.tag K)
  le_C i := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hc : (⟨h₀, hL.h₀_mem_L i⟩ : ↥(L i)) ∈ Subgroup.center ↥(L i) := by
      rw [hL.L_center_eq i]
      exact Subgroup.mem_zpowers h₀
    have := congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨x.1, hx⟩)
    apply Subtype.ext
    show (x : ModGL TwistTag.E6.tag K) * (s : ModGL TwistTag.E6.tag K) =
      (s : ModGL TwistTag.E6.tag K) * x
    rw [hs]
    exact this
  shift g hg := by
    obtain ⟨k, hk⟩ := hL.conj_shift g (twLayer_mem_centralizer hs hg)
    exact ⟨k, fun i => map_conj_subgroupOf _ (hL.L_le i) (hk i)⟩
  zero g hg h0 := by
    have hgc := twLayer_mem_centralizer hs hg
    have hL' : ∀ i, (L i).map (MulAut.conj (g : ModGL TwistTag.E6.tag K)).toMonoidHom = L i :=
      fun i => map_conj_of_subgroupOf _ (hL.L_le i) (hL.L_le i) (h0 i)
    have hmem := hL.shift_zero g hgc hL'
    have e : (T.subgroupOf (twistedE6RootGroup K σ) ⊔
        ⨆ i, (L i).subgroupOf (twistedE6RootGroup K σ)).map (twistedE6RootGroup K σ).subtype =
        T ⊔ ⨆ i, L i := by
      rw [Subgroup.map_sup, Subgroup.map_iSup, Subgroup.subgroupOf_map_subtype,
        inf_eq_left.2 hL.T_le]
      congr 1
      refine iSup_congr fun i => ?_
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 (hL.L_le i)]
    rw [← e] at hmem
    exact (Subgroup.mem_map_iff_mem (twistedE6RootGroup K σ).subtype_injective).1 hmem

theorem twLayer_centralizer_stable {s : twistedE6RootGroup K σ}
    {ε : MulAut (twistedE6RootGroup K σ)} (hcomm : ε * MulAut.conj s = MulAut.conj s * ε) :
    ∀ x ∈ Subgroup.centralizer ({s} : Set (twistedE6RootGroup K σ)),
      ε x ∈ Subgroup.centralizer ({s} : Set (twistedE6RootGroup K σ)) := by
  intro x hx
  have h1 := congrArg (fun f : MulAut (twistedE6RootGroup K σ) => f x) hcomm
  have hx' : s * x * s⁻¹ = x := by
    rw [mul_inv_eq_iff_eq_mul]
    exact (Subgroup.mem_centralizer_singleton_iff.mp hx).symm
  simp only [MulAut.mul_apply, MulAut.conj_apply, hx'] at h1
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h2 : ε x = s * ε x * s⁻¹ := h1
  rw [eq_mul_inv_iff_mul_eq] at h2
  exact h2

theorem twLayer_exists_shift (hL : TwE6ThreeA2Line K σ h₀ L T n) {s : twistedE6RootGroup K σ}
    (hs : (s : ModGL TwistTag.E6.tag K) = h₀) {ε : MulAut (twistedE6RootGroup K σ)}
    (hε3 : ε ^ 3 = 1) (hcomm : ε * MulAut.conj s = MulAut.conj s * ε) :
    ∃ k : Fin 3, ∀ i, ((L i).subgroupOf (twistedE6RootGroup K σ)).map ε.toMonoidHom =
      (L (i + k)).subgroupOf (twistedE6RootGroup K σ) := by
  have hcomm' : ε⁻¹ * MulAut.conj s = MulAut.conj s * ε⁻¹ := by
    have := congrArg (fun f : MulAut (twistedE6RootGroup K σ) => ε⁻¹ * f * ε⁻¹) hcomm
    simp only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left] at this
    simpa [← mul_assoc] using this.symm
  exact (twLayer_shiftData hL hs).exists_shift hε3 (twLayer_centralizer_stable hcomm)
    (twLayer_centralizer_stable hcomm')

theorem twLayer_exists_shift_frames (hL : TwE6ThreeA2Line K σ h₀ L T n)
    {s : twistedE6RootGroup K σ} (hs : (s : ModGL TwistTag.E6.tag K) = h₀)
    {ε : MulAut (twistedE6RootGroup K σ)} (hε3 : ε ^ 3 = 1)
    (hcomm : ε * MulAut.conj s = MulAut.conj s * ε) {Y : Type*} [Group Y]
    (ρ : Fin 3 → Y →* twistedE6RootGroup K σ)
    (hρ : ∀ i, (ρ i).range.map (twistedE6RootGroup K σ).subtype = L i) :
    ∃ k : Fin 3, ∀ i, (ρ i).range.map ε.toMonoidHom = (ρ (i + k)).range := by
  obtain ⟨k, hk⟩ := twLayer_exists_shift hL hs hε3 hcomm
  have hr : ∀ i, (ρ i).range = (L i).subgroupOf (twistedE6RootGroup K σ) := by
    intro i
    rw [← hρ i]
    ext x
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      have : y = x := Subtype.ext hyx
      rwa [this] at hy
  exact ⟨k, fun i => by rw [hr, hr, hk]⟩

end Layer

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
