module

public import CFSG.CGT.Timmesfeld75.PaperSteps

public section

namespace CFSG.HardMathSupport.RichardWeiss.Proving

open CFSG.CGT.Timmesfeld75

theorem centralizer_le_normalizer_of_isWC {G : Type*} [Group G] {T : Subgroup G}
    (hT : IsWC T) {z : G} (hzT : z ∈ T) (hz1 : z ≠ 1) :
    Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (T : Set G) := by
  intro g hg
  have hcomm : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := by
    intro a ha b hb
    have := hT.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg Subtype.val this
  have hgz : g * z * g⁻¹ = z := by
    have := Subgroup.mem_centralizer_iff.1 hg z (Set.mem_singleton z)
    rw [← this]
    group
  have hle : conjSubgroup g T ≤ Subgroup.centralizer ({z} : Set G) := by
    intro y hy
    rw [mem_conjSubgroup] at hy
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff.1 hw]
    have hx := hcomm _ hy z hzT
    calc z * y = (g * z * g⁻¹) * y := by rw [hgz]
      _ = g * (z * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * y * g) * z) * g⁻¹ := by rw [hx]
      _ = y * (g * z * g⁻¹) := by group
      _ = y * z := by rw [hgz]
  have heq := (hT.2 z hzT hz1).2 g hle
  exact Subgroup.mem_normalizer_iff_map_conj_eq.2 heq

theorem exists_normal_complement_of_le_center {C : Type*} [Group C] [Finite C] {p : ℕ}
    [Fact p.Prime] (P : Sylow p C) (hP : (P : Subgroup C) ≤ Subgroup.center C) :
    ∃ N : Subgroup C, N.Normal ∧ (P : Subgroup C).IsComplement' N := by
  have hN : Subgroup.normalizer (P : Set C) ≤ Subgroup.centralizer (P : Set C) := by
    intro g _
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact ((Subgroup.mem_center_iff.1 (hP hh)) g).symm
  exact ⟨(MonoidHom.transferSylow P hN).ker, inferInstance,
    (MonoidHom.ker_transferSylow_isComplement' P hN).symm⟩

theorem galoisField_two_one_eq_zero_or_one (c : GaloisField 2 1) : c = 0 ∨ c = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 one_ne_zero]
    norm_num
  by_contra h
  push Not at h
  classical
  have : Fintype (GaloisField 2 1) := Fintype.ofFinite _
  have h3 : ({0, 1, c} : Finset (GaloisField 2 1)).card = 3 :=
    Finset.card_eq_three.2 ⟨0, 1, c, zero_ne_one, fun h0 => h.1 h0.symm, fun h1 => h.2 h1.symm, rfl⟩
  have hle := Finset.card_le_univ ({0, 1, c} : Finset (GaloisField 2 1))
  rw [h3, ← Nat.card_eq_fintype_card, hcard] at hle
  omega

open scoped MatrixGroups in
theorem normalizer_eq_sup_centralizer_of_naturalSL {G : Type} [Group G] [Finite G]
    {T H : Subgroup G} {n : ℕ} (hN : NaturalSL T H n 1)
    (hHN : H ≤ Subgroup.normalizer (T : Set G)) :
    Subgroup.normalizer (T : Set G) = H ⊔ Subgroup.centralizer (T : Set G) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨_, e, φ, hact⟩ := hN
    set F := GaloisField 2 1
    let α : MulAut ↥T := T.normalizerMonoidHom ⟨x, hx⟩
    have hα : ∀ t : ↥T, ((α t : ↥T) : G) = x * t * x⁻¹ := fun t => rfl
    let ψ : Multiplicative (Fin n → F) ≃* Multiplicative (Fin n → F) := φ.symm.trans (α.trans φ)
    let f : (Fin n → F) → (Fin n → F) := fun v => Multiplicative.toAdd (ψ (Multiplicative.ofAdd v))
    have hadd : ∀ v w, f (v + w) = f v + f w := by
      intro v w
      simp only [f, ofAdd_add, map_mul, toAdd_mul]
    have hsmul : ∀ (c : F) (v : Fin n → F), f (c • v) = c • f v := by
      intro c v
      rcases galoisField_two_one_eq_zero_or_one c with rfl | rfl
      · simp only [zero_smul, f, ofAdd_zero, map_one, toAdd_one]
      · simp only [one_smul]
    let fl : (Fin n → F) →ₗ[F] (Fin n → F) :=
      { toFun := f, map_add' := hadd, map_smul' := hsmul }
    have hfl : Function.Bijective fl := by
      constructor
      · intro v w hvw
        have : ψ (Multiplicative.ofAdd v) = ψ (Multiplicative.ofAdd w) :=
          Multiplicative.toAdd.injective hvw
        exact Multiplicative.ofAdd.injective (ψ.injective this)
      · intro w
        refine ⟨Multiplicative.toAdd (ψ.symm (Multiplicative.ofAdd w)), ?_⟩
        show Multiplicative.toAdd (ψ (Multiplicative.ofAdd
          (Multiplicative.toAdd (ψ.symm (Multiplicative.ofAdd w))))) = w
        simp
    let fe : (Fin n → F) ≃ₗ[F] (Fin n → F) := LinearEquiv.ofBijective fl hfl
    set M := LinearMap.toMatrix' fl with hM
    have hdet : M.det = 1 := by
      have hu : IsUnit (LinearMap.det (fe : (Fin n → F) →ₗ[F] (Fin n → F))) :=
        LinearEquiv.isUnit_det' fe
      have hfe : (fe : (Fin n → F) →ₗ[F] (Fin n → F)) = fl := rfl
      rw [hfe, ← LinearMap.det_toMatrix'] at hu
      rcases galoisField_two_one_eq_zero_or_one M.det with h0 | h1
      · rw [← hM, h0] at hu
        exact absurd hu not_isUnit_zero
      · exact h1
    obtain ⟨h, hh⟩ := QuotientGroup.mk_surjective (e.symm ⟨M, hdet⟩)
    have heh : e (QuotientGroup.mk h) = ⟨M, hdet⟩ := by
      have hh' : (QuotientGroup.mk h : ↥H ⧸ T.subgroupOf H) = e.symm ⟨M, hdet⟩ := hh
      rw [hh']
      exact MulEquiv.apply_symm_apply e _
    have hconj : ∀ t : ↥T, (h : G) * t * (h : G)⁻¹ = x * t * x⁻¹ := by
      intro t
      have hmem : (h : G) * t * (h : G)⁻¹ ∈ T :=
        (Subgroup.mem_normalizer_iff.1 (hHN h.2) t).1 t.2
      have h1 := hact h t hmem
      rw [heh] at h1
      have h2 : φ ⟨(h : G) * t * (h : G)⁻¹, hmem⟩ = φ (α t) := by
        rw [h1]
        show Multiplicative.ofAdd (M.mulVec (Multiplicative.toAdd (φ t))) = φ (α t)
        rw [hM, LinearMap.toMatrix'_mulVec]
        show Multiplicative.ofAdd (Multiplicative.toAdd (ψ (Multiplicative.ofAdd
          (Multiplicative.toAdd (φ t))))) = φ (α t)
        simp [ψ]
      have h3 := congrArg Subtype.val (φ.injective h2)
      rw [hα] at h3
      exact h3
    have hc : (h : G)⁻¹ * x ∈ Subgroup.centralizer (T : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      have := hconj ⟨t, ht⟩
      simp only at this
      calc t * ((h : G)⁻¹ * x) = (h : G)⁻¹ * ((h : G) * t * (h : G)⁻¹) * x := by group
        _ = (h : G)⁻¹ * (x * t * x⁻¹) * x := by rw [this]
        _ = (h : G)⁻¹ * x * t := by group
    have hx' : x = (h : G) * ((h : G)⁻¹ * x) := by group
    rw [hx']
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h.2) (Subgroup.mem_sup_right hc)
  · exact sup_le hHN (Subgroup.centralizer_le_normalizer _)

end CFSG.HardMathSupport.RichardWeiss.Proving
