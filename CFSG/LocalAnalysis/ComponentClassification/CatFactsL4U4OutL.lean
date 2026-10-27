module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.LocalAnalysis.ComponentInitial.ScalarSemilinearNormalizer

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

open Matrix
open scoped commutatorElement

theorem commutator_mem_of_closure_eq_top {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    {S : Set G} (hS : Subgroup.closure S = ⊤) (h : ∀ x ∈ S, ∀ y ∈ S, ⁅x, y⁆ ∈ N) (u v : G) :
    ⁅u, v⁆ ∈ N := by
  have key : ∀ x y : G, ⁅x, y⁆ ∈ N ↔
      (QuotientGroup.mk x : G ⧸ N) * QuotientGroup.mk y =
        QuotientGroup.mk y * QuotientGroup.mk x := by
    intro x y
    rw [← QuotientGroup.eq_one_iff, ← commutatorElement_eq_one_iff_mul_comm]
    change QuotientGroup.mk' N ⁅x, y⁆ = 1 ↔ _
    rw [map_commutatorElement]
    rfl
  have h1 : ∀ x ∈ S, ∀ v : G, (QuotientGroup.mk x : G ⧸ N) * QuotientGroup.mk v =
      QuotientGroup.mk v * QuotientGroup.mk x := by
    intro x hx
    have hle : Subgroup.closure S ≤
        (Subgroup.centralizer {(QuotientGroup.mk x : G ⧸ N)}).comap (QuotientGroup.mk' N) := by
      rw [Subgroup.closure_le]
      intro y hy
      rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
      exact ((key x y).1 (h x hx y hy)).symm
    intro v
    have hv := hle (hS ▸ Subgroup.mem_top v)
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff] at hv
    exact hv.symm
  have hle : Subgroup.closure S ≤ (Subgroup.center (G ⧸ N)).comap (QuotientGroup.mk' N) := by
    rw [Subgroup.closure_le]
    intro x hx
    rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_center_iff]
    intro g
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective g
    exact (h1 x hx v).symm
  have hu := hle (hS ▸ Subgroup.mem_top u)
  rw [Subgroup.mem_comap, Subgroup.mem_center_iff] at hu
  exact (key u v).2 (hu (QuotientGroup.mk v)).symm

theorem commutator_mem_range_conj_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (hY : ∀ u v : MulAut Y, ⁅u, v⁆ ∈ (MulAut.conj : Y →* MulAut Y).range) (u v : MulAut X) :
    ⁅u, v⁆ ∈ (MulAut.conj : X →* MulAut X).range := by
  obtain ⟨y, hy⟩ := hY (MulAut.congr e u) (MulAut.congr e v)
  rw [← map_commutatorElement] at hy
  refine ⟨e.symm y, ?_⟩
  ext x
  have h1 := congrArg (fun φ : MulAut Y => φ (e x)) hy
  have h2 : (MulAut.congr e ⁅u, v⁆) (e x) = e (⁅u, v⁆ x) := by
    change e (⁅u, v⁆ (e.symm (e x))) = e (⁅u, v⁆ x)
    rw [MulEquiv.symm_apply_apply]
  simp only [MulAut.conj_apply] at h1
  rw [h2] at h1
  rw [MulAut.conj_apply]
  apply e.injective
  rw [← h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem range_conj_normal (G : Type*) [Group G] :
    ((MulAut.conj : G →* MulAut G).range).Normal where
  conj_mem := by
    rintro _ ⟨g, rfl⟩ α
    refine ⟨α g, MulEquiv.ext fun x => ?_⟩
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]

theorem exists_pow_four_eq_of_pow_odd_eq_one {G : Type*} [Monoid G] {m : ℕ} (hm : Odd m)
    {z : G} (hz : z ^ m = 1) : ∃ e : G, z = e ^ 4 := by
  obtain ⟨t, rfl⟩ := hm
  refine ⟨z ^ ((t + 1) ^ 2), ?_⟩
  rw [← pow_mul, show (t + 1) ^ 2 * 4 = (2 * t + 1) * (2 * t + 3) + 1 by ring, pow_succ,
    pow_mul, hz, one_pow, one_mul]

theorem exists_pow_pow_four_eq_of_pow_odd_eq_one {G : Type*} [Monoid G] {m : ℕ} (hm : Odd m)
    {z : G} (hz : z ^ m = 1) : ∃ k : ℕ, z = (z ^ k) ^ 4 := by
  obtain ⟨t, rfl⟩ := hm
  refine ⟨(t + 1) ^ 2, ?_⟩
  rw [← pow_mul, show (t + 1) ^ 2 * 4 = (2 * t + 1) * (2 * t + 3) + 1 by ring, pow_succ,
    pow_mul, hz, one_pow, one_mul]

namespace LinearOut

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {K : Type*} [Field K] {n : ℕ}

theorem conjAut_mem_range_of_det (A : GL (Fin n) K) (e : Kˣ)
    (he : GeneralLinearGroup.det A = e ^ n) :
    conjAut n K A ∈ (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range := by
  set s := GeneralLinearGroup.scalar (Fin n) e⁻¹ with hs
  have hsc : s ∈ Subgroup.center (GL (Fin n) K) := by
    rw [GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨e⁻¹, rfl⟩
  have hdet : A * s ∈ (GeneralLinearGroup.det : GL (Fin n) K →* Kˣ).ker := by
    rw [MonoidHom.mem_ker, map_mul, he]
    apply Units.ext
    simp [hs]
  rw [← SpecialLinearGroup.range_toGL_eq_ker_det] at hdet
  obtain ⟨g, hg⟩ := hdet
  refine ⟨proj n K g, ?_⟩
  ext x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  change proj n K g * proj n K y * (proj n K g)⁻¹ = conjAut n K A (proj n K y)
  have hgy : g * y * g⁻¹ = CatalogueBHigherLinearAction.slConjugation n K A y := by
    apply SpecialLinearGroup.toGL_injective
    have hcomm : s * SpecialLinearGroup.toGL y = SpecialLinearGroup.toGL y * s :=
      (Subgroup.mem_center_iff.mp hsc _).symm
    rw [CatalogueBHigherLinearAction.toGL_slConjugation, map_mul, map_mul, map_inv, hg,
      _root_.mul_inv_rev, mul_assoc A s, hcomm]
    group
  rw [conjAut_proj, ← map_inv, ← map_mul, ← map_mul, hgy]

theorem det_map (σ : K ≃+* K) (A : GL (Fin n) K) :
    ((GeneralLinearGroup.det (GeneralLinearGroup.map (σ : K →+* K) A) : Kˣ) : K) =
      σ (GeneralLinearGroup.det A : K) := by
  rw [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.val_det_apply,
    show σ (A : Matrix (Fin n) (Fin n) K).det = (σ : K →+* K) (A : Matrix (Fin n) (Fin n) K).det
      from rfl, RingHom.map_det]
  rfl

theorem pow_half_mul_inv_map_eq_one [Fintype K] (hK : Odd (Fintype.card K)) (σ : K ≃+* K)
    {d : K} (hd : d ≠ 0) : (d * (σ d)⁻¹) ^ ((Fintype.card K - 1) / 2) = 1 := by
  set m := (Fintype.card K - 1) / 2 with hmdef
  have hm : Fintype.card K - 1 = 2 * m := by
    obtain ⟨t, ht⟩ := hK
    omega
  have hq := FiniteField.pow_card_sub_one_eq_one d hd
  have hdm : d ^ m = 1 ∨ d ^ m = -1 := by
    have : (d ^ m) ^ 2 = 1 := by rw [← pow_mul, mul_comm, ← hm, hq]
    exact mul_self_eq_one_iff.1 (by rw [← sq]; exact this)
  have hσ : σ (d ^ m) = d ^ m := by
    rcases hdm with h | h <;> rw [h] <;> simp
  rw [mul_pow, inv_pow, ← map_pow, hσ, mul_inv_cancel₀ (pow_ne_zero _ hd)]

theorem det_inverseTranspose' (B : GL (Fin n) K) :
    GeneralLinearGroup.det (GeneralLinearGroup.inverseTranspose B) =
      (GeneralLinearGroup.det B)⁻¹ := by
  refine Units.ext ?_
  rw [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.coe_inverseTranspose, det_transpose,
    ← GeneralLinearGroup.val_det_apply, map_inv]

theorem out_comm_projectiveSL_four [Fintype K] (hK : Fintype.card K % 4 = 3)
    (u v : MulAut (projectiveSL 4 K)) :
    ⁅u, v⁆ ∈ (MulAut.conj : projectiveSL 4 K →* MulAut (projectiveSL 4 K)).range := by
  classical
  set N := (MulAut.conj : projectiveSL 4 K →* MulAut (projectiveSL 4 K)).range with hN
  obtain ⟨-, hgen⟩ := automorphism_generation (K := K) (n := 4) (by norm_num)
  obtain ⟨-, -, hfc, hδδ, hδc, hδf, -⟩ := standard_automorphism_transport (K := K) (n := 4)
  set S : Set (MulAut (projectiveSL 4 K)) :=
    Set.range (conjAut 4 K) ∪ Set.range (fieldAut 4 K) ∪ {dualAut 4 K} with hS
  have hSt : Subgroup.closure S = ⊤ := by
    rw [eq_top_iff]
    intro α _
    obtain ⟨A, σ, ε, -, rfl⟩ := hgen α
    exact mul_mem (mul_mem (Subgroup.subset_closure (Or.inl (Or.inl ⟨A, rfl⟩)))
      (Subgroup.subset_closure (Or.inl (Or.inr ⟨σ, rfl⟩))))
      (pow_mem (Subgroup.subset_closure (show dualAut 4 K ∈ S from Or.inr rfl)) _)
  have hodd : Odd ((Fintype.card K - 1) / 2) := ⟨(Fintype.card K - 3) / 4, by omega⟩
  have hKodd : Odd (Fintype.card K) := ⟨Fintype.card K / 2, by omega⟩
  have hinner : ∀ C : GL (Fin 4) K,
      (GeneralLinearGroup.det C) ^ ((Fintype.card K - 1) / 2) = 1 → conjAut 4 K C ∈ N := by
    intro C hC
    obtain ⟨e, he⟩ := exists_pow_four_eq_of_pow_odd_eq_one hodd hC
    exact conjAut_mem_range_of_det C e he
  have hNn : N.Normal := range_conj_normal _
  have hNsymm : ∀ x y : MulAut (projectiveSL 4 K), ⁅x, y⁆ ∈ N → ⁅y, x⁆ ∈ N := fun x y h => by
    have := inv_mem h
    rwa [commutatorElement_inv] at this
  have hδinv : (dualAut 4 K)⁻¹ = dualAut 4 K := inv_eq_of_mul_eq_one_right hδδ
  have hcc : ∀ A B : GL (Fin 4) K, ⁅conjAut 4 K A, conjAut 4 K B⁆ ∈ N := by
    intro A B
    rw [← map_commutatorElement]
    apply hinner
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm.2 (mul_comm _ _), one_pow]
  have hcf : ∀ (A : GL (Fin 4) K) (σ : K ≃+* K), ⁅conjAut 4 K A, fieldAut 4 K σ⁆ ∈ N := by
    intro A σ
    have h1 : ⁅conjAut 4 K A, fieldAut 4 K σ⁆ =
        conjAut 4 K (A * GeneralLinearGroup.map (σ : K →+* K) A⁻¹) := by
      rw [commutatorElement_def, mul_assoc (conjAut 4 K A), mul_assoc (conjAut 4 K A),
        ← map_inv (conjAut 4 K) A, hfc σ A⁻¹, map_mul]
    rw [h1]
    apply hinner
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, map_mul, Units.val_mul, det_map, map_inv,
      Units.val_inv_eq_inv_val, map_inv₀, Units.val_one]
    exact pow_half_mul_inv_map_eq_one hKodd σ (Units.ne_zero _)
  have hcδ : ∀ A : GL (Fin 4) K, ⁅conjAut 4 K A, dualAut 4 K⁆ ∈ N := by
    intro A
    have h1 : ⁅conjAut 4 K A, dualAut 4 K⁆ =
        conjAut 4 K (A * GeneralLinearGroup.inverseTranspose A⁻¹) := by
      rw [commutatorElement_def, hδinv, mul_assoc (conjAut 4 K A), mul_assoc (conjAut 4 K A),
        ← map_inv (conjAut 4 K) A, hδc A⁻¹, map_mul]
    rw [h1]
    apply hinner
    rw [map_mul, det_inverseTranspose', map_inv, inv_inv, ← sq, ← pow_mul,
      show 2 * ((Fintype.card K - 1) / 2) = Fintype.card K - 1 by omega]
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact FiniteField.pow_card_sub_one_eq_one _ (Units.ne_zero _)
  have hff : ∀ σ τ : K ≃+* K, ⁅fieldAut 4 K σ, fieldAut 4 K τ⁆ ∈ N := by
    intro σ τ
    rw [← map_commutatorElement, commutatorElement_eq_one_iff_mul_comm.2 (ringAut_mul_comm K σ τ),
      map_one]
    exact one_mem N
  have hfδ : ∀ σ : K ≃+* K, ⁅fieldAut 4 K σ, dualAut 4 K⁆ ∈ N := by
    intro σ
    have h1 : ⁅fieldAut 4 K σ, dualAut 4 K⁆ = 1 := by
      rw [commutatorElement_def, hδinv, mul_assoc (fieldAut 4 K σ), mul_assoc (fieldAut 4 K σ),
        ← map_inv (fieldAut 4 K) σ, hδf σ⁻¹, map_inv, mul_inv_cancel]
    rw [h1]
    exact one_mem N
  refine commutator_mem_of_closure_eq_top N hSt ?_ u v
  rintro x ((⟨A, rfl⟩ | ⟨σ, rfl⟩) | hx) y ((⟨B, rfl⟩ | ⟨τ, rfl⟩) | hy)
  · exact hcc A B
  · exact hcf A τ
  · rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact hcδ A
  · exact hNsymm _ _ (hcf B σ)
  · exact hff σ τ
  · rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact hfδ σ
  · rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact hNsymm _ _ (hcδ B)
  · rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact hNsymm _ _ (hfδ τ)
  · rw [Set.mem_singleton_iff] at hx hy
    rw [hx, hy, commutatorElement_self]
    exact one_mem N

end LinearOut

end CFSG.ComponentClassification.CatFactsL4U4
