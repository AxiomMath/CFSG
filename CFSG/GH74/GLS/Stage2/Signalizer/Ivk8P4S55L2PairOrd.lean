module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55L2Pair
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55L2PGrp
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55L2Dkn
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55L2Glue

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG L2Dick

section PairOrd

variable {p : ℕ} {Γ : Type} [Group Γ] [Finite Γ] {V : Type} [AddCommGroup V]
  [Module (ZMod p) V] [Module.Finite (ZMod p) V] {ρ : Γ →* (V →ₗ[ZMod p] V)ˣ}
  {K : Subgroup Γ} {a : Γ}


theorem pair_orders (hf : Hyp89 p ρ K a) {r f : ℕ} [hr : Fact r.Prime] (hr2 : r ≠ 2)
    (hrp : r ≠ p) {F₀ : Type} [Field F₀] [Finite F₀] (hF₀ : Nat.card F₀ = r ^ f)
    (e0 : (↥K ⧸ center ↥K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F₀)
    {y : ↥K ⧸ center ↥K} (hy : bAutN K a hf.norm = MulAut.conj y)
    (hno : ∀ E : Subgroup (↥K ⧸ center ↥K), IsPGroup r ↥E →
      (∀ x ∈ E, bAutN K a hf.norm x ∈ E) → E = ⊥)
    {k : Γ} (hk : k ∈ K)
    (hJ : ¬ IsPGroup p ↥(Subgroup.closure ({a, k * a * k⁻¹} : Set Γ))) :
    ∃ (N : Subgroup ↥(Subgroup.closure ({a, k * a * k⁻¹} : Set Γ))) (_ : N.Normal) (F' : Type)
      (_ : Field F') (_ : Finite F')
      (_ : (↥(Subgroup.closure ({a, k * a * k⁻¹} : Set Γ)) ⧸ N) ≃*
        Matrix.SpecialLinearGroup (Fin 2) F'),
      ((∃ n : ℕ, 1 ≤ n ∧ Nat.card F' = p ^ n) ∨ (p = 3 ∧ Nat.card F' = 5)) ∧
      (∀ z ∈ Subgroup.closure ({e0 y, e0 (QuotientGroup.mk ⟨k, hk⟩) * e0 y *
          (e0 (QuotientGroup.mk ⟨k, hk⟩))⁻¹} :
            Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F₀)),
        z ^ 2 = 1 ∨ z ^ 3 = 1 ∨ z ^ 5 = 1) ∧
      ((∃ z ∈ Subgroup.closure ({e0 y, e0 (QuotientGroup.mk ⟨k, hk⟩) * e0 y *
          (e0 (QuotientGroup.mk ⟨k, hk⟩))⁻¹} :
            Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F₀)), z ^ 5 = 1 ∧ z ≠ 1) →
        Nat.card F' = 5) := by
  classical
  have hpp : Fact p.Prime := ⟨hf.prime⟩
  have hcen := center_quot_trivial hf e0
  have hinj := conj_inj_of_centerless hcen
  obtain ⟨yh, c, hyc, hcC, hac⟩ := hf.exists_inner_decomp hy
  obtain ⟨ι, hι1, hι2, hιker⟩ := exists_iota hf hy hcen hk
  obtain ⟨N, hN, -, F', hFf, hFfin, hcardF', ⟨e'⟩⟩ := sl2Quot_of_nonPGroup_pair hf hJ
  let a₀ : ↥(Subgroup.closure ({a, k * a * k⁻¹} : Set Γ)) :=
    ⟨a, Subgroup.subset_closure (Set.mem_insert _ _)⟩
  let b₀ : ↥(Subgroup.closure ({a, k * a * k⁻¹} : Set Γ)) := ⟨k * a * k⁻¹,
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩
  have hgen : Subgroup.closure ({a₀, b₀} : Set ↥(Subgroup.closure ({a, k * a * k⁻¹} : Set Γ))) =
      ⊤ := closure_pair_generates a (k * a * k⁻¹)
  have hya : ι a₀ = y := hι1
  have hyb : ι b₀ = (QuotientGroup.mk ⟨k, hk⟩ : ↥K ⧸ center ↥K) * y *
      (QuotientGroup.mk ⟨k, hk⟩)⁻¹ := hι2
  let ψ : ↥(Subgroup.closure ({a, k * a * k⁻¹} : Set Γ)) →*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) F' :=
    (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F'))).comp
      (e'.toMonoidHom.comp (QuotientGroup.mk' N))
  have hψ : Function.Surjective ψ :=
    (QuotientGroup.mk'_surjective _).comp (e'.surjective.comp (QuotientGroup.mk'_surjective N))
  have hker : (e0.toMonoidHom.comp ι).ker ≤ ψ.ker := by
    intro w hw
    have h1 : ι w = 1 := by
      rw [MonoidHom.mem_ker] at hw
      exact e0.injective (by simpa using hw)
    have h2 : (w : Γ) ∈ centralizer (K : Set Γ) := (hιker w).mp h1
    have hcomm := pair_central yh.2 hcC hk h2 (by rw [← hac]; exact w.2)
    rw [← hac] at hcomm
    have hwc : ∀ x : ↥(Subgroup.closure ({a, k * a * k⁻¹} : Set Γ)), x * w = w * x := by
      intro x
      have := Subgroup.mem_centralizer_singleton_iff.mp (hcomm x.2)
      exact Subtype.ext this
    rw [MonoidHom.mem_ker]
    show QuotientGroup.mk (e' (QuotientGroup.mk w)) = (1 : Matrix.ProjectiveSpecialLinearGroup
      (Fin 2) F')
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
    intro g
    obtain ⟨x, rfl⟩ := e'.surjective.comp (QuotientGroup.mk'_surjective N) g
    show e' (QuotientGroup.mk x) * e' (QuotientGroup.mk w) =
      e' (QuotientGroup.mk w) * e' (QuotientGroup.mk x)
    rw [← map_mul, ← map_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hwc x]
  have hypow : y ^ p = 1 := by
    apply hinj
    rw [map_pow, ← hy, map_one]
    exact hf.bAutN_pow
  have h₁ : (e0.toMonoidHom.comp ι) a₀ ^ p = 1 := by
    show (e0 (ι a₀)) ^ p = 1
    rw [hya, ← map_pow, hypow, map_one]
  have h₂ : (e0.toMonoidHom.comp ι) b₀ ^ p = 1 := by
    show (e0 (ι b₀)) ^ p = 1
    rw [hyb, ← map_pow, conj_pow, hypow, mul_one, mul_inv_cancel, map_one]
  have hnoR : ∀ E : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F₀), IsPGroup r ↥E →
      (∀ x ∈ E, (e0.toMonoidHom.comp ι) a₀ * x * ((e0.toMonoidHom.comp ι) a₀)⁻¹ ∈ E) →
        E = ⊥ := by
    intro E hE hinv
    have hE' : IsPGroup r ↥(E.map e0.symm.toMonoidHom) :=
      hE.of_equiv (E.equivMapOfInjective e0.symm.toMonoidHom e0.symm.injective)
    have hbot := hno _ hE' (by
      rintro _ ⟨x, hx, rfl⟩
      have h3 : bAutN K a hf.norm (e0.symm x) = y * e0.symm x * y⁻¹ := by
        rw [hy]
        rfl
      show bAutN K a hf.norm (e0.symm x) ∈ E.map e0.symm.toMonoidHom
      rw [h3]
      refine ⟨e0 y * x * (e0 y)⁻¹, ?_, ?_⟩
      · have := hinv x hx
        simpa [hya] using this
      · simp)
    exact (Subgroup.map_eq_bot_iff_of_injective E e0.symm.injective).mp hbot
  obtain ⟨hord, hfive⟩ := L2Dick.dickson_orders
    (J := ↥(Subgroup.closure ({a, k * a * k⁻¹} : Set Γ))) hr2 hf.prime hf.odd hrp hF₀ hcardF'
    (e0.toMonoidHom.comp ι) ψ hψ hker hgen h₁ h₂ hnoR
  refine ⟨N, hN, F', hFf, hFfin, e', hcardF', ?_, ?_⟩
  · intro z hz
    have hzr : z ∈ (e0.toMonoidHom.comp ι).range := by
      refine (Subgroup.closure_le _).mpr ?_ hz
      rintro _ (rfl | rfl)
      · exact ⟨a₀, by simp [hya]⟩
      · exact ⟨b₀, by simp [hyb]⟩
    obtain ⟨x, rfl⟩ := hzr
    exact hord x
  · rintro ⟨z, hz, h5, hne⟩
    have hzr : z ∈ (e0.toMonoidHom.comp ι).range := by
      refine (Subgroup.closure_le _).mpr ?_ hz
      rintro _ (rfl | rfl)
      · exact ⟨a₀, by simp [hya]⟩
      · exact ⟨b₀, by simp [hyb]⟩
    obtain ⟨x, rfl⟩ := hzr
    exact hfive ⟨x, h5, hne⟩

theorem pair_comm_of_pgroup (hf : Hyp89 p ρ K a) {r f : ℕ} [hr : Fact r.Prime] (hr2 : r ≠ 2)
    (hrp : r ≠ p) {F₀ : Type} [Field F₀] [Finite F₀] (hF₀ : Nat.card F₀ = r ^ f)
    (e0 : (↥K ⧸ center ↥K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F₀)
    {y : ↥K ⧸ center ↥K} (hy : bAutN K a hf.norm = MulAut.conj y) {k : Γ} (hk : k ∈ K)
    (hJ : IsPGroup p ↥(Subgroup.closure ({a, k * a * k⁻¹} : Set Γ))) :
    e0 y * (e0 (QuotientGroup.mk ⟨k, hk⟩) * e0 y * (e0 (QuotientGroup.mk ⟨k, hk⟩))⁻¹) =
      (e0 (QuotientGroup.mk ⟨k, hk⟩) * e0 y * (e0 (QuotientGroup.mk ⟨k, hk⟩))⁻¹) * e0 y := by
  have hcen := center_quot_trivial hf e0
  obtain ⟨ι, hι1, hι2, -⟩ := exists_iota hf hy hcen hk
  have hp : IsPGroup p ↥(e0.toMonoidHom.comp ι).range :=
    IsPGroup.of_surjective hJ (e0.toMonoidHom.comp ι).rangeRestrict
      (MonoidHom.rangeRestrict_surjective _)
  have h1 : e0 y ∈ (e0.toMonoidHom.comp ι).range :=
    ⟨⟨a, Subgroup.subset_closure (Set.mem_insert _ _)⟩, by simp [hι1]⟩
  have h2 : e0 (QuotientGroup.mk ⟨k, hk⟩) * e0 y * (e0 (QuotientGroup.mk ⟨k, hk⟩))⁻¹ ∈
      (e0.toMonoidHom.comp ι).range :=
    ⟨⟨k * a * k⁻¹, Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩, by
      simp [hι2]⟩
  exact L2Dick.pgroup_comm hr2 hf.prime hf.odd hrp hF₀ _ hp _ h1 _ h2

end PairOrd

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
