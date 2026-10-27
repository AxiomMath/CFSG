module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiLayerKernelBasic
public import CFSG.LocalAnalysis.ComponentInitial.RootPairRestriction

public section

namespace CFSG.ProperTwoGeneratedCore.RootCenter

open CFSG.ShultStronglyClosedTI CFSG.LocalAnalysis.ComponentInitial

variable {G M : Type*} [Group G] [Group M]

theorem map_omega₁_eq_of_isElemAbelian {Q : Subgroup G} (hQ : CFSG.Open.IsElemAbelian 2 Q) :
    (CFSG.omega₁ (G := Q) (p := 2)).map Q.subtype = Q := by
  rw [SuzukiLayerKernel.map_omega₁_subtype]
  exact le_antisymm ((Subgroup.closure_le _).2 fun _ hg => hg.1)
    fun g hg => Subgroup.subset_closure ⟨hg, hQ.2 g hg⟩

theorem map_omega₁_map {p : ℕ} (ε : M ≃* G) (P : Subgroup M) :
    ((CFSG.omega₁ (G := P) (p := p)).map P.subtype).map ε.toMonoidHom =
      (CFSG.omega₁ (G := P.map ε.toMonoidHom) (p := p)).map (P.map ε.toMonoidHom).subtype := by
  rw [SuzukiLayerKernel.map_omega₁_subtype, SuzukiLayerKernel.map_omega₁_subtype,
    MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨hy, hyp⟩, rfl⟩
    exact ⟨Subgroup.mem_map_of_mem _ hy, by rw [← map_pow, hyp, map_one]⟩
  · rintro ⟨hx, hxp⟩
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨y, ⟨hy, ε.injective ?_⟩, rfl⟩
    rw [map_pow, map_one]
    exact hxp

theorem congr_conj (ε : M ≃* G) (b : M) :
    MulAut.congr ε (MulAut.conj b) = MulAut.conj (ε b) :=
  MulEquiv.ext fun x => by
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulAut.conj_apply, map_mul, map_inv,
      MulEquiv.apply_symm_apply]

theorem exists_mulEquiv_map_eq [Finite M] {p : ℕ} [Fact p.Prime] (e : G ≃* M) (P : Sylow p M)
    (R : Sylow p G) : ∃ ε : M ≃* G, (P : Subgroup M).map ε.toMonoidHom = R := by
  have : Finite G := Finite.of_equiv _ e.symm.toEquiv
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M P (R.mapSurjective (f := e.toMonoidHom)
    e.surjective)
  refine ⟨(MulAut.conj g).trans e.symm, Subgroup.ext fun x => ?_⟩
  have h : e x ∈ ((g • P : Sylow p M) : Subgroup M) ↔ x ∈ (R : Subgroup G) := by
    rw [hg]
    change e x ∈ (R : Subgroup G).map e.toMonoidHom ↔ _
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  rw [coe_smul_sylow', Subgroup.mem_map_equiv] at h
  rw [Subgroup.mem_map_equiv, ← h]
  rfl

theorem layerKernel_map {p : ℕ} (ε : M ≃* G) (P : Subgroup M)
    (hP : ∀ γ : MulAut M, P.map γ.toMonoidHom = P →
      (∀ v ∈ (CFSG.omega₁ (G := P) (p := p)).map P.subtype, γ v = v) →
      (∀ x ∈ P, x⁻¹ * γ x ∈ (CFSG.omega₁ (G := P) (p := p)).map P.subtype) →
      ∃ b ∈ P, γ = MulAut.conj b)
    (γ : MulAut G) (hγQ : (P.map ε.toMonoidHom).map γ.toMonoidHom = P.map ε.toMonoidHom)
    (hγV : ∀ v ∈ (CFSG.omega₁ (G := P.map ε.toMonoidHom) (p := p)).map
      (P.map ε.toMonoidHom).subtype, γ v = v)
    (hγQV : ∀ x ∈ P.map ε.toMonoidHom, x⁻¹ * γ x ∈
      (CFSG.omega₁ (G := P.map ε.toMonoidHom) (p := p)).map (P.map ε.toMonoidHom).subtype) :
    ∃ b ∈ P.map ε.toMonoidHom, γ = MulAut.conj b := by
  rw [← map_omega₁_map] at hγV hγQV
  set γ₀ := MulAut.congr ε.symm γ with hγ₀
  have hγ₀_apply : ∀ x, γ₀ x = ε.symm (γ (ε x)) := fun x => by
    simp [hγ₀]
  have hmemV : ∀ v, v ∈ (CFSG.omega₁ (G := P) (p := p)).map P.subtype ↔
      ε v ∈ ((CFSG.omega₁ (G := P) (p := p)).map P.subtype).map ε.toMonoidHom := fun v => by
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  have hP0 : P.map γ₀.toMonoidHom = P := by
    ext x
    rw [Subgroup.mem_map_equiv]
    have h := congrArg (fun S : Subgroup G => ε x ∈ S) hγQ
    simp only [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply, eq_iff_iff] at h
    rw [← h]
    simp [hγ₀]
  obtain ⟨b, hb, hγb⟩ := hP γ₀ hP0
    (fun v hv => by
      rw [hγ₀_apply, hγV _ ((hmemV v).1 hv), MulEquiv.symm_apply_apply])
    (fun x hx => by
      rw [hmemV, map_mul, map_inv, hγ₀_apply, MulEquiv.apply_symm_apply]
      exact hγQV _ (Subgroup.mem_map_of_mem _ hx))
  refine ⟨ε b, Subgroup.mem_map_of_mem _ hb, ?_⟩
  rw [← congr_conj, ← hγb]
  exact MulEquiv.ext fun x => by simp [hγ₀_apply, MulAut.congr_apply]

theorem injOn_conj_of_le_stabilizer {Ω : Type*} [MulAction G Ω] [FaithfulSMul G Ω]
    [MulAction.IsPretransitive G Ω] {R : Subgroup G} {ξ : Ω}
    (hR : R ≤ MulAction.stabilizer G ξ) : Set.InjOn MulAut.conj (R : Set G) := by
  intro r hr s hs hrs
  have hc : ∀ g : G, s⁻¹ * r * g = g * (s⁻¹ * r) := fun g => by
    have h := congrArg (fun φ : MulAut G => φ g) hrs
    simp only [MulAut.conj_apply] at h
    calc s⁻¹ * r * g = s⁻¹ * (r * g * r⁻¹) * r := by group
      _ = s⁻¹ * (s * g * s⁻¹) * r := by rw [h]
      _ = g * (s⁻¹ * r) := by group
  have hξ : (s⁻¹ * r) • ξ = ξ := by
    rw [mul_smul, inv_smul_eq_iff, hR hr, hR hs]
  have hfix : ∀ ω : Ω, (s⁻¹ * r) • ω = ω := fun ω => by
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G ξ ω
    rw [smul_smul, hc g, mul_smul, hξ]
  have h1 : s⁻¹ * r = 1 := eq_of_smul_eq_smul fun ω => by rw [hfix ω, one_smul]
  rw [inv_mul_eq_one] at h1
  exact h1.symm

end CFSG.ProperTwoGeneratedCore.RootCenter
