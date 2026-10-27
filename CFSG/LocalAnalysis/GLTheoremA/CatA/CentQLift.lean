module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3LieRes

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement

theorem fixSubgroup_conj_eq_centralizer' {G : Type*} [Group G] (u : G) :
    fixSubgroup (MulAut.conj u) = Subgroup.centralizer ({u} : Set G) := by
  ext x
  rw [mem_fixSubgroup, Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply,
    mul_inv_eq_iff_eq_mul]
  exact eq_comm

theorem cq_glaPComponent_ne_bot {G : Type*} [Group G] {p : ℕ} {X L : Subgroup G}
    (h : GLAPComponent p X L) : L ≠ ⊥ := by
  intro hL
  have h3 := h.2.2.1
  subst hL
  have hbot : ((⊥ : Subgroup G).subgroupOf X).map (QuotientGroup.mk' (GLAPPrimeCore p ↥X)) = ⊥ := by
    rw [Subgroup.bot_subgroupOf, Subgroup.map_bot]
  rw [hbot] at h3
  obtain ⟨-, hsimple⟩ := h3.2.2
  have := hsimple.toNontrivial
  have hss : Subsingleton (↥(⊥ : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X)) ⧸
      Subgroup.center ↥(⊥ : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X))) := inferInstance
  exact (not_subsingleton_iff_nontrivial.2 inferInstance) hss

@[expose] def CentCompQuasi (S : Type) [Group S] [Finite S] (x : S) (r : ℕ) : Prop :=
  ∀ J : Subgroup S, GLAPComponent r (Subgroup.centralizer ({x} : Set S)) J →
    CFSG.Open.IsQuasisimple ↥J

theorem centCompQuasi_of_perfectInLayer {S : Type} [Group S] [Finite S] {x : S} {r : ℕ}
    (h : PerfectInLayer (MulAut.conj x)) : CentCompQuasi S x r := by
  intro J hJ
  rw [← fixSubgroup_conj_eq_centralizer'] at hJ
  exact (glaPComponent_isComponent_of_le_layer hJ (h J hJ.1 (glaPComponent_perfect hJ))).1.2.2

theorem centCompQuasi_of_noPerfect {S : Type} [Group S] [Finite S] {x : S} {r : ℕ}
    (h : ∀ P : Subgroup S, P ≤ Subgroup.centralizer ({x} : Set S) → ⁅P, P⁆ = P → P = ⊥) :
    CentCompQuasi S x r := by
  intro J hJ
  exact absurd (h J hJ.1 (glaPComponent_perfect hJ)) (cq_glaPComponent_ne_bot hJ)

theorem centCompQuasi_one {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hnc : ∃ a b : S, a * b ≠ b * a) (r : ℕ) : CentCompQuasi S 1 r := by
  have h1 : (MulAut.conj (1 : S) : MulAut S) = 1 := map_one _
  exact centCompQuasi_of_perfectInLayer (h1 ▸ perfectInLayer_one hnc)

theorem centCompQuasi_of_mulEquiv {S S' : Type} [Group S] [Finite S] [Group S'] [Finite S']
    (e : S ≃* S') {x : S} {r : ℕ} (hr : r.Prime) (h : CentCompQuasi S' (e x) r) :
    CentCompQuasi S x r := by
  intro J hJ
  have hker : (e : S →* S').ker ≤ Subgroup.center S := by
    rw [(MonoidHom.ker_eq_bot_iff _).2 e.injective]
    exact bot_le
  have hcomm : ∀ s : S, (e : S →* S') (MulAut.conj x s) =
      (MulAut.conj (e x) : MulAut S') ((e : S →* S') s) := fun s => by
    simp [MulAut.conj_apply]
  rw [← fixSubgroup_conj_eq_centralizer'] at hJ
  have hJ' := glaPComponent_map_fixSubgroup (e : S →* S') hker (MulAut.conj x)
    (MulAut.conj (e x)) hcomm e.surjective hr hJ
  rw [fixSubgroup_conj_eq_centralizer'] at hJ'
  have hq := h _ hJ'
  exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
    (J.equivMapOfInjective (e : S →* S') e.injective).symm hq

theorem centQuasi_lift {G : Type} [Group G] [Finite G] {K : Subgroup G} {y : G} (hy : y ∈ K)
    {r : ℕ} (hr : r.Prime)
    (h : CentCompQuasi (↥K ⧸ Subgroup.center ↥K)
      (QuotientGroup.mk (⟨y, hy⟩ : ↥K)) r) :
    ∀ Y : Subgroup G, GLAPComponent r (K ⊓ Subgroup.centralizer ({y} : Set G)) Y →
      CFSG.Open.IsQuasisimple ↥Y := by
  intro Y hY
  let κ : ↥K := ⟨y, hy⟩
  let α₀ : MulAut ↥K := MulAut.conj κ
  let π : ↥K →* (↥K ⧸ Subgroup.center ↥K) := QuotientGroup.mk' (Subgroup.center ↥K)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker ≤ Subgroup.center ↥K := by rw [QuotientGroup.ker_mk']
  let β : MulAut (↥K ⧸ Subgroup.center ↥K) := MulAut.conj (π κ)
  have hαβ : ∀ k, π (α₀ k) = β (π k) := fun k => by
    simp [α₀, β, MulAut.conj_apply, map_mul, map_inv]
  set X : Subgroup ↥K := fixSubgroup α₀ with hX
  have hXmap : X.map K.subtype = K ⊓ Subgroup.centralizer ({y} : Set G) := by
    ext z
    constructor
    · rintro ⟨k, hk, rfl⟩
      have h1 : κ * k * κ⁻¹ = k := hk
      refine ⟨k.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      have h2 := congrArg Subtype.val h1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2
      show (k : G) * y = y * (k : G)
      calc (k : G) * y = (y * (k : G) * y⁻¹) * y := by rw [show y * (k : G) * y⁻¹ = k from h2]
        _ = y * (k : G) := by group
    · rintro ⟨hzK, hzC⟩
      refine ⟨⟨z, hzK⟩, ?_, rfl⟩
      show κ * ⟨z, hzK⟩ * κ⁻¹ = ⟨z, hzK⟩
      apply Subtype.ext
      have hzC' : z * y = y * z := Subgroup.mem_centralizer_singleton_iff.1 hzC
      show y * z * y⁻¹ = z
      calc y * z * y⁻¹ = (z * y) * y⁻¹ := by rw [hzC']
        _ = z := by group
  have hc : ∀ w ∈ X ⊓ K.subtype.ker, ∀ z ∈ X, z * w = w * z := by
    intro w hw z _
    have : w = 1 := Subtype.ext (MonoidHom.mem_ker.1 hw.2)
    rw [this, mul_one, one_mul]
  have hY0 : GLAPComponent r (X.map K.subtype) Y := by rw [hXmap]; exact hY
  obtain ⟨J₁, hJ₁, hJ₁map⟩ := exists_glaPComponent_map_central hr K.subtype hc hY0
  have hJβ : GLAPComponent r (fixSubgroup β) (J₁.map π) :=
    glaPComponent_map_fixSubgroup π hker α₀ β hαβ hπ hr hJ₁
  rw [fixSubgroup_conj_eq_centralizer'] at hJβ
  have hA : CFSG.Open.IsQuasisimple ↥(J₁.map π) := h _ hJβ
  have hperf : Group.IsPerfect ↥J₁ := Subgroup.isPerfect_iff.2 (glaPComponent_perfect hJ₁)
  have hQ1 : CFSG.IsQuasisimple ↥J₁ :=
    isQuasisimple_of_central_cover (π.subgroupMap J₁) (MonoidHom.subgroupMap_surjective π J₁)
      hperf (ker_subgroupMap_le_center π hker J₁)
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).1 hA)
  have hQ1' : CFSG.Open.IsQuasisimple ↥J₁ :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2 hQ1
  have e₂ : ↥J₁ ≃* ↥Y :=
    (J₁.equivMapOfInjective K.subtype K.subtype_injective).trans
      (MulEquiv.subgroupCongr hJ₁map)
  exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e₂ hQ1'

end CFSG.LocalAnalysis.GLTheoremA
