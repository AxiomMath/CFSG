module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FDelta

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z : G} {A B : Subgroup G}
  {φ : (Fin 7 → ZMod 2) → G}

theorem Sec4FSetup.pt_none (h : Sec4FSetup t L S z A B φ) : sec4MPt t φ none = t := by
  dsimp only [sec4MPt, sec4MV]
  rw [IsPermModuleVia.map_zero h.data.bdata.perm, mul_one]

theorem Sec4FSetup.realizes_of_mem_A (h : Sec4FSetup t L S z A B φ) {a : G} (ha : a ∈ A) :
    Sec4MRealizes t φ a 1 := by
  intro p
  change a * sec4MPt t φ p * a⁻¹ = sec4MPt t φ p
  have hpA : sec4MPt t φ p ∈ A := sec4MPt_mem_A h.data p
  have hcomm : a * sec4MPt t φ p = sec4MPt t φ p * a := h.A_comm ha hpA
  rw [hcomm]
  group

theorem Sec4FSetup.exists_realizes (h : Sec4FSetup t L S z A B φ) {m : G}
    (hm : m ∈ normalizer (A : Set G)) :
    ∃ σ : Equiv.Perm (Option (Fin 7)), Sec4MRealizes t φ m σ := by
  have hpt : ∀ p : Option (Fin 7), ∃ q : Option (Fin 7),
      m * sec4MPt t φ p * m⁻¹ = sec4MPt t φ q := by
    intro p
    have hconj : ∃ g : G, sec4MPt t φ p = g⁻¹ * t * g :=
      (conj_iff_mem_conjClassIn_top (t := t)).mpr (Sec4FSetup.pt_mem_conj h p)
    obtain ⟨g, hg⟩ := hconj
    have hA : m * sec4MPt t φ p * m⁻¹ ∈ A :=
      (Subgroup.mem_set_normalizer_iff.mp hm (sec4MPt t φ p)).mp (sec4MPt_mem_A h.data p)
    have hconj' : m * sec4MPt t φ p * m⁻¹ ∈ conjClassIn ⊤ t :=
      (conj_iff_mem_conjClassIn_top (t := t)).mp ⟨g * m⁻¹, by rw [hg]; group⟩
    have hmem : m * sec4MPt t φ p * m⁻¹ ∈ Set.range (sec4MPt t φ) := by
      rw [← h.conj_cap_A]
      exact ⟨hconj', hA⟩
    obtain ⟨q, hq⟩ := hmem
    exact ⟨q, hq.symm⟩
  choose f hf using hpt
  have hfinj : Function.Injective f := by
    intro p q hpq
    have hpq' : sec4MPt t φ p = sec4MPt t φ q := by
      have h1 : m * sec4MPt t φ p * m⁻¹ = m * sec4MPt t φ q * m⁻¹ := by
        rw [hf p, hf q, hpq]
      exact mul_left_cancel (mul_right_cancel h1)
    exact sec4MPt_injective h.data hpq'
  refine ⟨Equiv.ofBijective f ((Finite.injective_iff_bijective).mp hfinj), ?_⟩
  intro p
  rw [hf p]
  rfl

noncomputable def Sec4FSetup.actHom (h : Sec4FSetup t L S z A B φ) :
    ↥(normalizer (A : Set G)) →* Equiv.Perm (Option (Fin 7)) where
  toFun m := Classical.choose (h.exists_realizes m.2)
  map_one' := by
    refine Sec4MRealizes.unique h.pt_injective
      (Classical.choose_spec (h.exists_realizes (one_mem (normalizer (A : Set G))))) ?_
    exact Sec4MRealizes.one
  map_mul' m₁ m₂ := by
    refine Sec4MRealizes.unique h.pt_injective
      (Classical.choose_spec (h.exists_realizes (mul_mem m₁.2 m₂.2))) ?_
    exact Sec4MRealizes.mul (Classical.choose_spec (h.exists_realizes m₁.2))
      (Classical.choose_spec (h.exists_realizes m₂.2))

theorem Sec4FSetup.actHom_spec (h : Sec4FSetup t L S z A B φ) (m : ↥(normalizer (A : Set G))) :
    Sec4MRealizes t φ (m : G) (h.actHom m) :=
  Classical.choose_spec (h.exists_realizes m.2)

theorem Sec4FSetup.eq_actHom (h : Sec4FSetup t L S z A B φ) {m : G}
    (hm : m ∈ normalizer (A : Set G)) {σ : Equiv.Perm (Option (Fin 7))}
    (hσ : Sec4MRealizes t φ m σ) : σ = h.actHom ⟨m, hm⟩ :=
  Sec4MRealizes.unique h.pt_injective hσ (h.actHom_spec ⟨m, hm⟩)

theorem Sec4FSetup.mem_centralizer_iff_realizes_one (h : Sec4FSetup t L S z A B φ) {m : G} :
    m ∈ centralizer (A : Set G) ↔ Sec4MRealizes t φ m 1 := by
  constructor
  · intro hm p
    have hcomm : sec4MPt t φ p * m = m * sec4MPt t φ p :=
      Subgroup.mem_centralizer_iff.mp hm _ (sec4MPt_mem_A h.data p)
    change m * sec4MPt t φ p * m⁻¹ = sec4MPt t φ p
    rw [← hcomm]
    group
  · intro hm
    rw [Subgroup.mem_centralizer_iff]
    have hle : A ≤ Subgroup.centralizer ({m} : Set G) := by
      rw [h.A_eq_closure, Subgroup.closure_le]
      rintro _ ⟨p, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      have h1 : m * sec4MPt t φ p * m⁻¹ = sec4MPt t φ p := hm p
      calc sec4MPt t φ p * m = (m * sec4MPt t φ p * m⁻¹) * m := by rw [h1]
        _ = m * sec4MPt t φ p := by group
    intro a ha
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle ha))

theorem Sec4FSetup.realizes_sq (h : Sec4FSetup t L S z A B φ) {y : G} (hy : y * y = 1)
    {σ : Equiv.Perm (Option (Fin 7))} (hσ : Sec4MRealizes t φ y σ) : σ * σ = 1 :=
  Sec4MRealizes.sq_eq_one h.pt_injective hσ hy

end CFSG.OddStandard.SmallF3.Omega
