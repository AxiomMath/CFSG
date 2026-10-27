module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Frame
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.K28Norm

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup CFSG.Blueprint CFSG.GH74.KGroups.U33

open scoped Pointwise

variable {K : Type} [Group K]

structure U33FrameExtras (x₁ x₂ lam rho : K) (α : MulAut K) : Prop where
  cent_E : ∀ k : K, k * x₁ ^ 2 = x₁ ^ 2 * k → k * (x₁ * x₂) ^ 2 = (x₁ * x₂) ^ 2 * k →
    k ∈ baseGrp x₁ x₂
  cent_base : ∀ k : K, (∀ w ∈ baseGrp x₁ x₂, k * w = w * k) → k ∈ baseGrp x₁ x₂
  norm_base : ∀ k : K, (∀ w ∈ baseGrp x₁ x₂, k * w * k⁻¹ ∈ baseGrp x₁ x₂) →
    k ∈ closure {x₁, x₂, rho, lam}
  aut_cent : ∀ γ : MulAut K, (∀ w ∈ baseGrp x₁ x₂, γ w = w) →
    ∃ w ∈ baseGrp x₁ x₂, γ = MulAut.conj w
  aut_norm : ∀ γ : MulAut K, (∀ w ∈ baseGrp x₁ x₂, γ w ∈ baseGrp x₁ x₂) →
    γ ∈ closure {MulAut.conj x₁, MulAut.conj x₂, MulAut.conj rho, MulAut.conj lam, α}

private theorem baseGrp_map_aut {K : Type} [Group K] (γ : MulAut K) (x₁ x₂ : K) :
    (baseGrp x₁ x₂).map γ.toMonoidHom = baseGrp (γ x₁) (γ x₂) := by
  simp only [baseGrp, MonoidHom.map_closure, Set.image_pair, MulEquiv.coe_toMonoidHom]

private theorem closure_four_map_aut {K : Type} [Group K] (γ : MulAut K) (a b c d : K) :
    (Subgroup.closure ({a, b, c, d} : Set K)).map γ.toMonoidHom =
      Subgroup.closure ({γ a, γ b, γ c, γ d} : Set K) := by
  rw [MonoidHom.map_closure]
  congr 1
  rw [Set.image_insert_eq, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
  simp only [MulEquiv.coe_toMonoidHom]

private theorem conj_mulAut_conj {G : Type*} [Group G] (γ : MulAut G) (w : G) :
    MulAut.conj γ (MulAut.conj w) = MulAut.conj (γ w) := by
  ext x
  simp only [MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply, map_mul, map_inv,
    MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply]

private theorem mem_normalizer_of_forall_conj_mem {G : Type*} [Group G] (W : Subgroup G)
    [Finite W] {g : G} (h : ∀ w ∈ W, g * w * g⁻¹ ∈ W) :
    g ∈ Subgroup.normalizer (W : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_ (le_of_eq ?_)
  · rw [Subgroup.map_le_iff_le_comap]
    intro w hw
    simpa using h w hw
  · exact (Subgroup.card_map_of_injective (MulAut.conj g).injective).symm

theorem U33FrameExtras.map {x₁ x₂ lam rho : K} {α : MulAut K}
    (h : U33FrameExtras x₁ x₂ lam rho α) (γ : MulAut K) :
    U33FrameExtras (γ x₁) (γ x₂) (γ lam) (γ rho) (γ * α * γ⁻¹) := by
  refine { cent_E := ?_, cent_base := ?_, norm_base := ?_, aut_cent := ?_, aut_norm := ?_ }
  · intro k hk1 hk2
    have hk1' : γ.symm k * x₁ ^ 2 = x₁ ^ 2 * γ.symm k := by
      have := congrArg γ.symm hk1
      simpa only [map_mul, map_pow, MulEquiv.symm_apply_apply] using this
    have hk2' : γ.symm k * (x₁ * x₂) ^ 2 = (x₁ * x₂) ^ 2 * γ.symm k := by
      have := congrArg γ.symm hk2
      simpa only [map_mul, map_pow, MulEquiv.symm_apply_apply] using this
    have hmem := Subgroup.mem_map_of_mem γ.toMonoidHom (h.cent_E (γ.symm k) hk1' hk2')
    have hk_eq : γ.toMonoidHom (γ.symm k) = k := by
      simp only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    rw [baseGrp_map_aut, hk_eq] at hmem
    exact hmem
  · intro k hk
    have hk' : ∀ w ∈ baseGrp x₁ x₂, γ.symm k * w = w * γ.symm k := by
      intro w hw
      have hγw : γ w ∈ baseGrp (γ x₁) (γ x₂) := by
        rw [← baseGrp_map_aut]
        exact Subgroup.mem_map_of_mem γ.toMonoidHom hw
      have := congrArg γ.symm (hk (γ w) hγw)
      simpa only [map_mul, MulEquiv.symm_apply_apply] using this
    have hk0 := h.cent_base (γ.symm k) hk'
    have hmem := Subgroup.mem_map_of_mem γ.toMonoidHom hk0
    have hk_eq : γ.toMonoidHom (γ.symm k) = k := by
      simp only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    rw [baseGrp_map_aut, hk_eq] at hmem
    exact hmem
  · intro k hk
    have hk' : ∀ w ∈ baseGrp x₁ x₂, γ.symm k * w * (γ.symm k)⁻¹ ∈ baseGrp x₁ x₂ := by
      intro w hw
      have hγw : γ w ∈ baseGrp (γ x₁) (γ x₂) := by
        rw [← baseGrp_map_aut]
        exact Subgroup.mem_map_of_mem γ.toMonoidHom hw
      have hgoal : γ (γ.symm k * w * (γ.symm k)⁻¹) = k * γ w * k⁻¹ := by
        simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
      have hmem : γ (γ.symm k * w * (γ.symm k)⁻¹) ∈
          (baseGrp x₁ x₂).map γ.toMonoidHom := by
        rw [baseGrp_map_aut, hgoal]
        exact hk (γ w) hγw
      exact (Subgroup.mem_map_iff_mem (f := γ.toMonoidHom) γ.injective).mp hmem
    have hk0 := h.norm_base (γ.symm k) hk'
    have hmem := Subgroup.mem_map_of_mem γ.toMonoidHom hk0
    have hk_eq : γ.toMonoidHom (γ.symm k) = k := by
      simp only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    rw [closure_four_map_aut, hk_eq] at hmem
    exact hmem
  · intro γ' hγ'
    have hfix : ∀ w ∈ baseGrp x₁ x₂, (γ⁻¹ * γ' * γ) w = w := by
      intro w hw
      have hγw : γ w ∈ baseGrp (γ x₁) (γ x₂) := by
        rw [← baseGrp_map_aut]
        exact Subgroup.mem_map_of_mem γ.toMonoidHom hw
      have hw' := hγ' (γ w) hγw
      simp only [MulAut.mul_apply, MulAut.inv_apply, hw', MulEquiv.symm_apply_apply]
    obtain ⟨w₀, hw₀, hconj⟩ := h.aut_cent (γ⁻¹ * γ' * γ) hfix
    refine ⟨γ w₀, ?_, ?_⟩
    · rw [← baseGrp_map_aut]
      exact Subgroup.mem_map_of_mem γ.toMonoidHom hw₀
    · have hγ'eq : γ * (γ⁻¹ * γ' * γ) * γ⁻¹ = γ' := by group
      rw [← hγ'eq, hconj, ← MulAut.conj_apply, conj_mulAut_conj]
  · intro γ' hγ'
    have hstab : ∀ w ∈ baseGrp x₁ x₂, (γ⁻¹ * γ' * γ) w ∈ baseGrp x₁ x₂ := by
      intro w hw
      have hγw : γ w ∈ baseGrp (γ x₁) (γ x₂) := by
        rw [← baseGrp_map_aut]
        exact Subgroup.mem_map_of_mem γ.toMonoidHom hw
      have hkey : (γ⁻¹ * γ' * γ) w = γ.symm (γ' (γ w)) := by
        simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply]
      rw [hkey]
      have hmem : γ (γ.symm (γ' (γ w))) ∈ (baseGrp x₁ x₂).map γ.toMonoidHom := by
        rw [baseGrp_map_aut]
        rw [show γ (γ.symm (γ' (γ w))) = γ' (γ w) by
          simp only [MulEquiv.apply_symm_apply]]
        exact hγ' (γ w) hγw
      exact (Subgroup.mem_map_iff_mem (f := γ.toMonoidHom) γ.injective).mp hmem
    have hmem0 := h.aut_norm (γ⁻¹ * γ' * γ) hstab
    have hmapcl : (Subgroup.closure ({MulAut.conj x₁, MulAut.conj x₂, MulAut.conj rho,
        MulAut.conj lam, α} : Set (MulAut K))).map (MulAut.conj γ).toMonoidHom =
        Subgroup.closure ({MulAut.conj (γ x₁), MulAut.conj (γ x₂), MulAut.conj (γ rho),
          MulAut.conj (γ lam), γ * α * γ⁻¹} : Set (MulAut K)) := by
      rw [MonoidHom.map_closure]
      congr 1
      rw [Set.image_insert_eq, Set.image_insert_eq, Set.image_insert_eq, Set.image_insert_eq,
        Set.image_singleton]
      simp only [MulEquiv.coe_toMonoidHom]
      rw [conj_mulAut_conj, conj_mulAut_conj, conj_mulAut_conj, conj_mulAut_conj,
        MulAut.conj_apply]
    have hγ'eq : (MulAut.conj γ) (γ⁻¹ * γ' * γ) = γ' := by
      rw [MulAut.conj_apply]; group
    rw [← hγ'eq, ← hmapcl]
    exact Subgroup.mem_map_of_mem (MulAut.conj γ).toMonoidHom hmem0

section KLevel


theorem frameExtras_of_model (m : K28.Model28 K) :
    ∃ (x₁ x₂ lam rho : K) (α : MulAut K), U33Frame x₁ x₂ lam rho α ∧
      U33FrameExtras x₁ x₂ lam rho α := by
  obtain ⟨x₁, x₂, lam, rho, α, hx₁, hx₂, hlam, hrho, hα, hf⟩ := frame_of_model m
  have hx₁ε : m.ε x₁ = K28.fx₁ := by rw [hx₁]; simp [K28.Model28.ε]
  have hx₂ε : m.ε x₂ = K28.fx₂ := by rw [hx₂]; simp [K28.Model28.ε]
  have hlamε : m.ε lam = K28.flam := by rw [hlam]; simp [K28.Model28.ε]
  have hrhoε : m.ε rho = K28.frho := by rw [hrho]; simp [K28.Model28.ε]
  have hαι : m.ι α = K28.ftau := by rw [hα]; simp [K28.Model28.ι]
  have hmapW : (baseGrp x₁ x₂).map m.ε = baseGrp K28.fx₁ K28.fx₂ := by
    simp only [baseGrp, MonoidHom.map_closure, Set.image_pair, hx₁ε, hx₂ε]
  have hmapC : (Subgroup.closure ({x₁, x₂, rho, lam} : Set K)).map m.ε =
      Subgroup.closure ({K28.fx₁, K28.fx₂, K28.frho, K28.flam} : Set K28.Pm) := by
    rw [MonoidHom.map_closure]
    congr 1
    rw [Set.image_insert_eq, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
    simp only [hx₁ε, hx₂ε, hrhoε, hlamε]
  refine ⟨x₁, x₂, lam, rho, α, hf, ?_⟩
  refine { cent_E := ?_, cent_base := ?_, norm_base := ?_, aut_cent := ?_, aut_norm := ?_ }
  · intro k hk1 hk2
    have hkfy : m.ε k * K28.fy = K28.fy * m.ε k := by
      change m.ε k * K28.fx₁ ^ 2 = K28.fx₁ ^ 2 * m.ε k
      have := congrArg m.ε hk1
      simpa only [map_mul, map_pow, hx₁ε] using this
    have hkfz : m.ε k * K28.fz = K28.fz * m.ε k := by
      change m.ε k * (K28.fx₁ * K28.fx₂) ^ 2 = (K28.fx₁ * K28.fx₂) ^ 2 * m.ε k
      have := congrArg m.ε hk2
      simpa only [map_mul, map_pow, hx₁ε, hx₂ε] using this
    have hmem : m.ε k ∈ QP.originalSubgroup ⊓
        Subgroup.centralizer ({K28.fy, K28.fz} : Set K28.Pm) := by
      refine Subgroup.mem_inf.mpr ⟨m.ε_mem k, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact hkfy.symm
      · exact hkfz.symm
    rw [K28.cent_E_eq] at hmem
    have hmem' : m.ε k ∈ (baseGrp x₁ x₂).map m.ε := by rwa [hmapW]
    exact (Subgroup.mem_map_iff_mem m.ε_injective).mp hmem'
  · intro k hk
    have hmem : m.ε k ∈ QP.originalSubgroup ⊓
        Subgroup.centralizer (baseGrp K28.fx₁ K28.fx₂ : Set K28.Pm) := by
      refine Subgroup.mem_inf.mpr ⟨m.ε_mem k, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hyW : y ∈ (baseGrp x₁ x₂).map m.ε := by rwa [hmapW]
      obtain ⟨w, hw, hwε⟩ := Subgroup.mem_map.mp hyW
      have hε := congrArg m.ε (hk w hw)
      simp only [map_mul] at hε
      rw [hwε] at hε
      exact hε.symm
    rw [K28.cent_W0_eq] at hmem
    have hmem' : m.ε k ∈ (baseGrp x₁ x₂).map m.ε := by rwa [hmapW]
    exact (Subgroup.mem_map_iff_mem m.ε_injective).mp hmem'
  · intro k hk
    have hconj : ∀ y ∈ baseGrp K28.fx₁ K28.fx₂,
        m.ε k * y * (m.ε k)⁻¹ ∈ baseGrp K28.fx₁ K28.fx₂ := by
      intro y hy
      have hyW : y ∈ (baseGrp x₁ x₂).map m.ε := by rwa [hmapW]
      obtain ⟨w, hw, hwε⟩ := Subgroup.mem_map.mp hyW
      have hmem := Subgroup.mem_map_of_mem m.ε (hk w hw)
      rw [hmapW] at hmem
      rw [← show m.ε (k * w * k⁻¹) = m.ε k * y * (m.ε k)⁻¹ by
        rw [map_mul, map_mul, map_inv, hwε]]
      exact hmem
    have hnorm : m.ε k ∈ Subgroup.normalizer (baseGrp K28.fx₁ K28.fx₂ : Set K28.Pm) :=
      mem_normalizer_of_forall_conj_mem (baseGrp K28.fx₁ K28.fx₂) hconj
    have hmem : m.ε k ∈ QP.originalSubgroup ⊓
        Subgroup.normalizer (baseGrp K28.fx₁ K28.fx₂ : Set K28.Pm) :=
      Subgroup.mem_inf.mpr ⟨m.ε_mem k, hnorm⟩
    rw [K28.norm_W0_eq] at hmem
    have hmem' : m.ε k ∈ (Subgroup.closure ({x₁, x₂, rho, lam} : Set K)).map m.ε := by
      rw [hmapC]; exact hmem
    exact (Subgroup.mem_map_iff_mem m.ε_injective).mp hmem'
  · intro γ' hγ'
    have hcent : m.ι γ' ∈ QA.originalSubgroup ⊓
        Subgroup.centralizer (baseGrp K28.fx₁ K28.fx₂ : Set K28.Pm) := by
      refine Subgroup.mem_inf.mpr ⟨m.ι_mem γ', ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hyW : y ∈ (baseGrp x₁ x₂).map m.ε := by rwa [hmapW]
      obtain ⟨w, hw, hwε⟩ := Subgroup.mem_map.mp hyW
      have hkey : m.ι γ' * y * (m.ι γ')⁻¹ = y := by
        rw [← hwε, ← K28.Model28.ε_apply, hγ' w hw]
      have : y * m.ι γ' = m.ι γ' * y := by
        calc y * m.ι γ' = (m.ι γ' * y * (m.ι γ')⁻¹) * m.ι γ' := by rw [hkey]
          _ = m.ι γ' * y := by group
      exact this
    rw [K28.centA_W0_eq] at hcent
    have hcentW : m.ι γ' ∈ (baseGrp x₁ x₂).map m.ε := by rwa [hmapW]
    obtain ⟨w₀, hw₀, hw₀ε⟩ := Subgroup.mem_map.mp hcentW
    refine ⟨w₀, hw₀, ?_⟩
    apply m.ι_injective
    rw [← hw₀ε, K28.Model28.ι_conj]
  · intro γ' hγ'
    have hconj : ∀ y ∈ baseGrp K28.fx₁ K28.fx₂,
        m.ι γ' * y * (m.ι γ')⁻¹ ∈ baseGrp K28.fx₁ K28.fx₂ := by
      intro y hy
      have hyW : y ∈ (baseGrp x₁ x₂).map m.ε := by rwa [hmapW]
      obtain ⟨w, hw, hwε⟩ := Subgroup.mem_map.mp hyW
      have hmem := Subgroup.mem_map_of_mem m.ε (hγ' w hw)
      rw [hmapW] at hmem
      rw [← show m.ε (γ' w) = m.ι γ' * y * (m.ι γ')⁻¹ by
        rw [K28.Model28.ε_apply, hwε]]
      exact hmem
    have hnorm : m.ι γ' ∈ Subgroup.normalizer (baseGrp K28.fx₁ K28.fx₂ : Set K28.Pm) :=
      mem_normalizer_of_forall_conj_mem (baseGrp K28.fx₁ K28.fx₂) hconj
    have hmem : m.ι γ' ∈ QA.originalSubgroup ⊓
        Subgroup.normalizer (baseGrp K28.fx₁ K28.fx₂ : Set K28.Pm) :=
      Subgroup.mem_inf.mpr ⟨m.ι_mem γ', hnorm⟩
    rw [K28.normA_W0_eq] at hmem
    have hmapA : (Subgroup.closure ({MulAut.conj x₁, MulAut.conj x₂, MulAut.conj rho,
        MulAut.conj lam, α} : Set (MulAut K))).map m.ι =
        Subgroup.closure ({K28.fx₁, K28.fx₂, K28.frho, K28.flam, K28.ftau} : Set K28.Pm) := by
      rw [MonoidHom.map_closure]
      congr 1
      rw [Set.image_insert_eq, Set.image_insert_eq, Set.image_insert_eq, Set.image_insert_eq,
        Set.image_singleton]
      simp only [K28.Model28.ι_conj, hx₁ε, hx₂ε, hrhoε, hlamε, hαι]
    have hmem' : m.ι γ' ∈ (Subgroup.closure ({MulAut.conj x₁, MulAut.conj x₂,
        MulAut.conj rho, MulAut.conj lam, α} : Set (MulAut K))).map m.ι := by
      rw [hmapA]; exact hmem
    exact (Subgroup.mem_map_iff_mem m.ι_injective).mp hmem'

theorem exists_frame_extras_of_psu33 (h : LieModel K .PSU 3 3 1) :
    ∃ (x₁ x₂ lam rho : K) (α : MulAut K), U33Frame x₁ x₂ lam rho α ∧
      U33FrameExtras x₁ x₂ lam rho α := by
  obtain ⟨m⟩ := K28.exists_model28 h
  exact frameExtras_of_model m

theorem exists_frame_extras_of_sylow (h : LieModel K .PSU 3 3 1) (S : Sylow 2 (MulAut K)) :
    ∃ (x₁ x₂ lam rho : K) (α : MulAut K), U33Frame x₁ x₂ lam rho α ∧
      U33FrameExtras x₁ x₂ lam rho α ∧
      m12Grp (MulAut.conj x₁) (MulAut.conj x₂) (MulAut.conj lam) α = (S : Subgroup (MulAut K)) := by
  obtain ⟨m⟩ := K28.exists_model28 h
  haveI hFinAut : Finite (MulAut K) :=
    Finite.of_injective m.Φ.toEquiv.toFun m.Φ.injective
  obtain ⟨x₁, x₂, lam, rho, α, hf, he⟩ := exists_frame_extras_of_psu33 h
  let S₀ : Subgroup (MulAut K) := m12Grp (MulAut.conj x₁) (MulAut.conj x₂) (MulAut.conj lam) α
  have hcardS₀ : Nat.card S₀ = 64 := (U33Frame.m12 h hf).card_m12Grp
  have hfac : (12096 : ℕ).factorization 2 = 6 := by
    have h12096 : (12096 : ℕ) = 2 ^ 6 * 189 := by norm_num
    rw [h12096, Nat.factorization_mul (by positivity) (by norm_num), Finsupp.add_apply,
      Nat.factorization_pow_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]
  have hfacM : (Nat.card (MulAut K)).factorization 2 = 6 := by
    rw [card_aut_of_psu33 h, show 2 * 6048 = 12096 from by norm_num]
    exact hfac
  have hcardAut : Nat.card S₀ = 2 ^ (Nat.card (MulAut K)).factorization 2 := by
    rw [hcardS₀, hfacM]
    norm_num
  let S₀' : Sylow 2 (MulAut K) := Sylow.ofCard S₀ hcardAut
  have hcoeS₀' : (S₀' : Subgroup (MulAut K)) = S₀ := Sylow.coe_ofCard S₀ hcardAut
  obtain ⟨γ, hγ⟩ := MulAction.exists_smul_eq (MulAut K) S₀' S
  have hmapS : S₀.map (MulAut.conj γ).toMonoidHom = (S : Subgroup (MulAut K)) := by
    have h := congrArg (fun T : Sylow 2 (MulAut K) => (T : Set (MulAut K))) hγ
    rw [Sylow.coe_smul] at h
    have hset : (S₀' : Set (MulAut K)) = (S₀ : Set (MulAut K)) := by
      rw [← Sylow.coe_coe S₀', hcoeS₀']
    rw [hset] at h
    apply SetLike.coe_injective
    rw [Subgroup.coe_map]
    have himage : (MulAut.conj γ).toMonoidHom '' (S₀ : Set (MulAut K))
        = (MulAut.conj γ) • (S₀ : Set (MulAut K)) := by
      ext x
      simp only [Set.mem_image, Set.mem_smul_set, MulAut.smul_def,
        MulEquiv.coe_toMonoidHom]
    rw [himage]
    exact h
  refine ⟨γ x₁, γ x₂, γ lam, γ rho, γ * α * γ⁻¹, hf.map γ, he.map γ, ?_⟩
  have hm12eq : m12Grp (MulAut.conj (γ x₁)) (MulAut.conj (γ x₂)) (MulAut.conj (γ lam))
        (γ * α * γ⁻¹)
      = (m12Grp (MulAut.conj x₁) (MulAut.conj x₂) (MulAut.conj lam) α).map
          (MulAut.conj γ).toMonoidHom := by
    change Subgroup.closure
          ({(MulAut.conj (γ x₁)), (MulAut.conj (γ x₂)), (MulAut.conj (γ lam)),
            (γ * α * γ⁻¹)} : Set (MulAut K))
        = (Subgroup.closure
            ({(MulAut.conj x₁), (MulAut.conj x₂), (MulAut.conj lam), α} : Set (MulAut K))).map
              (MulAut.conj γ).toMonoidHom
    rw [MonoidHom.map_closure]
    congr 1
    rw [Set.image_insert_eq, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
    simp only [MulEquiv.coe_toMonoidHom]
    rw [conj_mulAut_conj, conj_mulAut_conj, conj_mulAut_conj, MulAut.conj_apply]
  rw [hm12eq, hmapS]

end KLevel

end CFSG.OddStandard.SmallF3.HarrisU33
