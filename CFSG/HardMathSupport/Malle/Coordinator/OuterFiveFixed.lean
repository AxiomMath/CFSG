module

public import CFSG.HardMathSupport.Malle.Coordinator.OuterFiveSylow
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.HardMathSupport.Malle.Coordinator

variable {G : Type*} [Group G]

@[expose] def conjAut {M : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (M : Set G)) :
    MulAut M where
  toFun m := ⟨g * m * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg m).mp m.2⟩
  invFun m := ⟨g⁻¹ * m * g, (Subgroup.mem_normalizer_iff''.mp hg m).mp m.2⟩
  left_inv m := by ext; simp [mul_assoc]
  right_inv m := by ext; simp [mul_assoc]
  map_mul' a b := by ext; simp [mul_assoc]

@[simp] theorem conjAut_apply {M : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (M : Set G))
    (m : M) : ((conjAut hg m : M) : G) = g * m * g⁻¹ := rfl

@[expose] def normalizerConj (M : Subgroup G) :
    Subgroup.normalizer (M : Set G) →* MulAut M where
  toFun g := conjAut g.2
  map_one' := by ext; simp
  map_mul' a b := by ext; simp [mul_assoc]

theorem normalizerConj_apply (M : Subgroup G) (g : Subgroup.normalizer (M : Set G)) :
    normalizerConj M g = conjAut g.2 := rfl

theorem mulAut_mul_conj {M : Type*} [Group M] (σ : MulAut M) (m : M) :
    σ * MulAut.conj m = MulAut.conj (σ m) * σ := by
  ext x
  simp [MulAut.conj_apply]

theorem mulAut_smul_smul {M : Type*} [Group M] {p : ℕ} (σ : MulAut M) (m : M) (Q : Sylow p M) :
    σ • (m • Q) = σ m • (σ • Q) := by
  change σ • (MulAut.conj m • Q) = MulAut.conj (σ m) • (σ • Q)
  rw [← mul_smul, ← mul_smul, mulAut_mul_conj]

namespace OuterFiveData

variable {P Z : Subgroup G} {φ : G} (D : OuterFiveData P Z φ)
include D

theorem conjAut_smul_sylow_eq {M : Subgroup G} (hφM : φ ∈ Subgroup.normalizer (M : Set G))
    (Q : Sylow 5 M) (hQ : (Q : Subgroup M) = P.subgroupOf M) : conjAut hφM • Q = Q := by
  apply Sylow.ext
  rw [Sylow.pointwise_smul_def, hQ]
  ext x
  rw [Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Subgroup.mem_subgroupOf] at hy
    exact D.conj_inv_mem _ hy
  · intro hx
    refine ⟨conjAut hφM |>.symm x, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      exact D.conj_mem _ hx
    · exact (conjAut hφM).apply_symm_apply x

theorem card_fixed_mul_card_centralizer [Finite G] {K M : Subgroup G}
    (hPcard : Nat.card P = Nat.card Z * Nat.card Z) (hPM : P ≤ M) (hMK : M ≤ K)
    (hφK : ∀ k ∈ K, φ⁻¹ * k * φ ∈ K) (hCZ : K ⊓ Subgroup.centralizer (Z : Set G) ≤ P)
    (hφM : φ ∈ Subgroup.normalizer (M : Set G)) (hP5 : IsPGroup 5 P)
    (hidx : ¬ 5 ∣ P.relIndex M) :
    Nat.card {Q : Sylow 5 M // conjAut hφM • Q = Q} *
        Nat.card (M ⊓ Subgroup.normalizer (P : Set G) ⊓ Subgroup.centralizer ({φ} : Set G) :
          Subgroup G) =
      Nat.card (M ⊓ Subgroup.centralizer ({φ} : Set G) : Subgroup G) := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set α := conjAut hφM with hα
  let P' : Sylow 5 M := (hP5.comap_subtype (K := M)).toSylow hidx
  have hP' : (P' : Subgroup M) = P.subgroupOf M := rfl
  have hαP' : α • P' = P' := D.conjAut_smul_sylow_eq hφM P' hP'
  have hPset : (P' : Set M) = ((P.subgroupOf M : Subgroup M) : Set M) := rfl
  set R₀ := M ⊓ Subgroup.centralizer ({φ} : Set G) with hR₀
  let ι : R₀ →* M := Subgroup.inclusion inf_le_left
  let _ : MulAction R₀ (Sylow 5 M) := MulAction.compHom _ ι
  have hsmul : ∀ (r : R₀) (Q : Sylow 5 M), r • Q = ι r • Q := fun _ _ => rfl
  have hαι : ∀ r : R₀, α (ι r) = ι r := by
    intro r
    apply Subtype.ext
    rw [conjAut_apply]
    have hr : φ * r = r * φ := Subgroup.mem_centralizer_singleton_iff.mp r.2.2 |>.symm
    show φ * (r : G) * φ⁻¹ = r
    rw [hr]; group
  have horbit : MulAction.orbit R₀ P' = {Q : Sylow 5 M | α • Q = Q} := by
    ext Q
    rw [MulAction.mem_orbit_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨r, rfl⟩
      rw [hsmul, mulAut_smul_smul, hαι, hαP']
    · intro hQ
      obtain ⟨m, rfl⟩ := MulAction.exists_smul_eq M P' Q
      rw [mulAut_smul_smul, hαP'] at hQ
      have hmem : m⁻¹ * α m ∈ Subgroup.normalizer (P' : Set M) := by
        rw [← Sylow.smul_eq_iff_mem_normalizer, mul_smul, hQ, inv_smul_smul]
      rw [hPset, ← Subgroup.subgroupOf_normalizer_eq hPM, Subgroup.mem_subgroupOf] at hmem
      have hmφ : (m : G)⁻¹ * φ * m ∈ Subgroup.normalizer (P : Set G) := by
        have h1 : ((m⁻¹ * α m : M) : G) = (m : G)⁻¹ * (φ * m * φ⁻¹) := by
          simp [hα]
        rw [h1] at hmem
        have := Subgroup.mul_mem _ hmem D.mem_normalizer
        simpa [mul_assoc] using this
      obtain ⟨p, hp, hpc⟩ := D.exists_mul_commute_of_conj_mem_normalizer hPcard hPM hMK hφK hCZ
        hφM hidx m.2 hmφ
      refine ⟨⟨(m : G) * p, M.mul_mem m.2 (hPM hp),
        Subgroup.mem_centralizer_singleton_iff.mpr hpc.symm⟩, ?_⟩
      rw [hsmul]
      have hι : ι ⟨(m : G) * p, M.mul_mem m.2 (hPM hp),
          Subgroup.mem_centralizer_singleton_iff.mpr hpc.symm⟩ = m * ⟨p, hPM hp⟩ := rfl
      rw [hι, mul_smul]
      congr 1
      rw [Sylow.smul_eq_iff_mem_normalizer, hPset]
      exact Subgroup.le_normalizer (by rw [Subgroup.mem_subgroupOf]; exact hp)
  have hstab : (MulAction.stabilizer R₀ P').map R₀.subtype =
      M ⊓ Subgroup.normalizer (P : Set G) ⊓ Subgroup.centralizer ({φ} : Set G) := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨r, hr, rfl⟩
      rw [MulAction.mem_stabilizer_iff, hsmul, Sylow.smul_eq_iff_mem_normalizer, hPset,
        ← Subgroup.subgroupOf_normalizer_eq hPM, Subgroup.mem_subgroupOf] at hr
      exact ⟨⟨r.2.1, hr⟩, r.2.2⟩
    · rintro ⟨⟨hxM, hxN⟩, hxC⟩
      refine ⟨⟨x, hxM, hxC⟩, ?_, rfl⟩
      rw [MulAction.mem_stabilizer_iff, hsmul, Sylow.smul_eq_iff_mem_normalizer, hPset,
        ← Subgroup.subgroupOf_normalizer_eq hPM, Subgroup.mem_subgroupOf]
      exact hxN
  have hidx' := MulAction.index_stabilizer R₀ P'
  rw [horbit] at hidx'
  have hcardset : ({Q : Sylow 5 M | α • Q = Q} : Set (Sylow 5 M)).ncard =
      Nat.card {Q : Sylow 5 M // α • Q = Q} := by
    rw [← Nat.card_coe_set_eq]; rfl
  rw [hcardset] at hidx'
  have hstabcard : Nat.card (MulAction.stabilizer R₀ P') =
      Nat.card (M ⊓ Subgroup.normalizer (P : Set G) ⊓ Subgroup.centralizer ({φ} : Set G) :
        Subgroup G) := by
    rw [← hstab, Subgroup.card_map_of_injective R₀.subtype_injective]
  rw [← hidx', ← hstabcard, Subgroup.index_mul_card]
end OuterFiveData

end CFSG.HardMathSupport.Malle.Coordinator
