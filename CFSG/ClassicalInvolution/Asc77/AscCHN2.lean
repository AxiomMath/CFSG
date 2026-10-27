module

public import CFSG.ClassicalInvolution.GenericLocal.SL2Automorphisms

public section

namespace CFSG.ClassicalInvolution.Asc77

namespace CHN

open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G]

theorem comm_mul_central {a b c d : G} (hcb : c * b = b * c) (hcd : c * d = d * c)
    (hda : d * a⁻¹ = a⁻¹ * d) : ⁅a * c, b * d⁆ = ⁅a, b⁆ := by
  simp only [commutatorElement_def]
  calc a * c * (b * d) * (a * c)⁻¹ * (b * d)⁻¹
      = a * (c * b) * d * (c⁻¹ * a⁻¹) * (d⁻¹ * b⁻¹) := by group
    _ = a * (b * c) * d * (c⁻¹ * a⁻¹) * (d⁻¹ * b⁻¹) := by rw [hcb]
    _ = a * b * (c * d) * (c⁻¹ * a⁻¹) * (d⁻¹ * b⁻¹) := by group
    _ = a * b * (d * c) * (c⁻¹ * a⁻¹) * (d⁻¹ * b⁻¹) := by rw [hcd]
    _ = a * b * d * (c * c⁻¹) * a⁻¹ * (d⁻¹ * b⁻¹) := by group
    _ = a * b * d * a⁻¹ * (d⁻¹ * b⁻¹) := by group
    _ = a * b * (d * a⁻¹) * d⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * d) * d⁻¹ * b⁻¹ := by rw [hda]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem commutes_of_perfect_of_abelian_centralizer {F : Type} [Field F] [Finite F]
    (h4 : 4 ≤ Nat.card F) {K : Subgroup G} (eK : Nonempty (↥K ≃* SL(2, F))) {L : Subgroup G}
    (hL : L ≤ ⁅L, L⁆) (hLN : L ≤ Subgroup.normalizer (K : Set G)) {e : G}
    (heK : e ∈ Subgroup.normalizer (K : Set G)) (hLe : ∀ ℓ ∈ L, ℓ * e = e * ℓ)
    (hC : ∀ k ∈ K, ∀ k' ∈ K, e * k * e⁻¹ = k → e * k' * e⁻¹ = k' → k * k' = k' * k) :
    ∀ x ∈ K, ∀ y ∈ L, x * y = y * x := by
  classical
  obtain ⟨eK⟩ := eK
  have hperf : Group.IsPerfect ↥L :=
    Subgroup.isPerfect_iff.mpr (le_antisymm (Subgroup.commutator_le.mpr fun x hx y hy => by
      rw [commutatorElement_def]
      exact L.mul_mem (L.mul_mem (L.mul_mem hx hy) (L.inv_mem hx)) (L.inv_mem hy)) hL)
  let ψ : ↥L →* MulAut ↥K := K.normalizerMonoidHom.comp (Subgroup.inclusion hLN)
  have hψ : ∀ (ℓ : ↥L) (k : ↥K), ((ψ ℓ k : ↥K) : G) = (ℓ : G) * k * (ℓ : G)⁻¹ := fun ℓ k => rfl
  choose q hq using fun ℓ : ↥L => perfect_action_inner_of_equiv_sl2 h4 eK ψ ℓ
  have heK' : ∀ k : G, k ∈ K → e * k * e⁻¹ ∈ K := fun k hk =>
    (Subgroup.mem_normalizer_iff.mp heK k).mp hk
  have heK'' : ∀ k : G, k ∈ K → e⁻¹ * k * e ∈ K := fun k hk => by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ heK) k).mp hk
    simpa using this
  have hact : ∀ (ℓ : ↥L) (k : G), k ∈ K →
      (ℓ : G) * k * (ℓ : G)⁻¹ = (q ℓ : G) * k * (q ℓ : G)⁻¹ := by
    intro ℓ k hk
    have h1 := hψ ℓ ⟨k, hk⟩
    rw [hq ℓ] at h1
    simpa [MulAut.conj_apply] using h1.symm
  have hcen : ∀ ℓ : ↥L, ∀ k ∈ K, ((q ℓ : G)⁻¹ * (e * (q ℓ : G) * e⁻¹)) * k =
      k * ((q ℓ : G)⁻¹ * (e * (q ℓ : G) * e⁻¹)) := by
    intro ℓ k hk
    have hk₀ : e⁻¹ * k * e ∈ K := heK'' k hk
    have h1 : (ℓ : G) * (e⁻¹ * k * e) * (ℓ : G)⁻¹ = (q ℓ : G) * (e⁻¹ * k * e) * (q ℓ : G)⁻¹ :=
      hact ℓ _ hk₀
    have h2 : (ℓ : G) * k * (ℓ : G)⁻¹ = (q ℓ : G) * k * (q ℓ : G)⁻¹ := hact ℓ k hk
    have hℓe : (ℓ : G) * e = e * (ℓ : G) := hLe ℓ ℓ.2
    have h3 : e * ((ℓ : G) * (e⁻¹ * k * e) * (ℓ : G)⁻¹) * e⁻¹ = (ℓ : G) * k * (ℓ : G)⁻¹ := by
      have e1 : e * ((ℓ : G) * (e⁻¹ * k * e) * (ℓ : G)⁻¹) * e⁻¹ =
          (e * (ℓ : G)) * (e⁻¹ * k * e) * (e * (ℓ : G))⁻¹ := by group
      rw [e1, ← hℓe]
      group
    have h4' : e * ((q ℓ : G) * (e⁻¹ * k * e) * (q ℓ : G)⁻¹) * e⁻¹ =
        (e * (q ℓ : G) * e⁻¹) * k * (e * (q ℓ : G) * e⁻¹)⁻¹ := by group
    have h5 : (q ℓ : G) * k * (q ℓ : G)⁻¹ =
        (e * (q ℓ : G) * e⁻¹) * k * (e * (q ℓ : G) * e⁻¹)⁻¹ := by
      rw [← h4', ← h1, h3, h2]
    have h6 : ((q ℓ : G)⁻¹ * (e * (q ℓ : G) * e⁻¹)) * k *
        ((q ℓ : G)⁻¹ * (e * (q ℓ : G) * e⁻¹))⁻¹ = k := by
      have : ((q ℓ : G)⁻¹ * (e * (q ℓ : G) * e⁻¹)) * k *
          ((q ℓ : G)⁻¹ * (e * (q ℓ : G) * e⁻¹))⁻¹ =
          (q ℓ : G)⁻¹ * ((e * (q ℓ : G) * e⁻¹) * k * (e * (q ℓ : G) * e⁻¹)⁻¹) * (q ℓ : G) := by
        group
      rw [this, ← h5]
      group
    calc ((q ℓ : G)⁻¹ * (e * (q ℓ : G) * e⁻¹)) * k
        = (((q ℓ : G)⁻¹ * (e * (q ℓ : G) * e⁻¹)) * k *
            ((q ℓ : G)⁻¹ * (e * (q ℓ : G) * e⁻¹))⁻¹) *
            ((q ℓ : G)⁻¹ * (e * (q ℓ : G) * e⁻¹)) := by group
      _ = k * ((q ℓ : G)⁻¹ * (e * (q ℓ : G) * e⁻¹)) := by rw [h6]
  have hcomm_e : ∀ ℓ m : ↥L, e * ⁅(q ℓ : G), (q m : G)⁆ * e⁻¹ = ⁅(q ℓ : G), (q m : G)⁆ := by
    intro ℓ m
    set cℓ : G := (q ℓ : G)⁻¹ * (e * (q ℓ : G) * e⁻¹) with hcℓ
    set cm : G := (q m : G)⁻¹ * (e * (q m : G) * e⁻¹) with hcm
    have hcℓK : cℓ ∈ K := K.mul_mem (K.inv_mem (q ℓ).2) (heK' _ (q ℓ).2)
    have hcmK : cm ∈ K := K.mul_mem (K.inv_mem (q m).2) (heK' _ (q m).2)
    have e1 : e * (q ℓ : G) * e⁻¹ = (q ℓ : G) * cℓ := by rw [hcℓ]; group
    have e2 : e * (q m : G) * e⁻¹ = (q m : G) * cm := by rw [hcm]; group
    have hqℓ : (q ℓ : G) ∈ K := (q ℓ).2
    have hqm : (q m : G) ∈ K := (q m).2
    have hconj : e * ⁅(q ℓ : G), (q m : G)⁆ * e⁻¹ =
        ⁅e * (q ℓ : G) * e⁻¹, e * (q m : G) * e⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    rw [hconj, e1, e2]
    exact comm_mul_central (hcen ℓ _ hqm) (hcen ℓ _ hcmK) (hcen m _ (K.inv_mem hqℓ))
  let Cs : Subgroup ↥K := (Subgroup.centralizer ({e} : Set G)).subgroupOf K
  have hCs : ∀ k : ↥K, k ∈ Cs ↔ e * (k : G) * e⁻¹ = k := by
    intro k
    show (k : G) ∈ Subgroup.centralizer ({e} : Set G) ↔ _
    rw [Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      calc e * (k : G) * e⁻¹ = (k : G) * e * e⁻¹ := by rw [h]
        _ = k := by group
    · intro h
      calc (k : G) * e = (e * (k : G) * e⁻¹) * e := by rw [h]
        _ = e * k := by group
  let A : Subgroup (MulAut ↥K) := Cs.map (MulAut.conj : ↥K →* MulAut ↥K)
  have hAcomm : ∀ α ∈ A, ∀ β ∈ A, α * β = β * α := by
    rintro _ ⟨k, hk, rfl⟩ _ ⟨k', hk', rfl⟩
    have := hC k k.2 k' k'.2 ((hCs k).mp hk) ((hCs k').mp hk')
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext this
  have hcommA : ∀ ℓ m : ↥L, ψ ⁅ℓ, m⁆ ∈ A := by
    intro ℓ m
    rw [map_commutatorElement, hq ℓ, hq m, ← map_commutatorElement]
    refine ⟨⁅q ℓ, q m⁆, ?_, rfl⟩
    show ⁅q ℓ, q m⁆ ∈ Cs
    rw [hCs]
    exact hcomm_e ℓ m
  have htopA : commutator ↥L ≤ A.comap ψ := by
    rw [commutator, Subgroup.commutator_le]
    intro ℓ _ m _
    exact hcommA ℓ m
  have hAll : ∀ ℓ : ↥L, ψ ℓ ∈ A := by
    have := hperf.commutator_eq_top
    rw [this] at htopA
    intro ℓ
    exact htopA (Subgroup.mem_top ℓ)
  have hker : ∀ ℓ m : ↥L, ψ ⁅ℓ, m⁆ = 1 := by
    intro ℓ m
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hAcomm _ (hAll ℓ) _ (hAll m))
  have hψ1 : ∀ ℓ : ↥L, ψ ℓ = 1 := by
    have htop : commutator ↥L ≤ ψ.ker := by
      rw [commutator, Subgroup.commutator_le]
      intro ℓ _ m _
      exact hker ℓ m
    have := hperf.commutator_eq_top
    rw [this] at htop
    intro ℓ
    exact htop (Subgroup.mem_top ℓ)
  intro x hx y hy
  have h := congrArg (fun φ : MulAut ↥K => ((φ ⟨x, hx⟩ : ↥K) : G)) (hψ1 ⟨y, hy⟩)
  simp only [hψ, MulAut.one_apply] at h
  calc x * y = (y * x * y⁻¹) * y := by rw [h]
    _ = y * x := by group

end CHN

end CFSG.ClassicalInvolution.Asc77
