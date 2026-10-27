module

public import CFSG.ClassicalGroups.Orthogonal.SiegelI4ConcAxis
public import CFSG.ClassicalGroups.Orthogonal.SiegelI4ConcBasic
public import CFSG.ClassicalGroups.Orthogonal.SiegelI4CoplPlane

public section

namespace CFSG.ClassicalGroups.Orthogonal.SiegelRT1

open CFSG.ClassicalGroups.Alternating CFSG.HardMathSupport.Kantor79 QuadraticMap Module

variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {N : Type*} [AddCommGroup N] [Module K N] [FiniteDimensional K N]
  {BN : LinearMap.BilinForm K N}
  {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {hBN : BN.IsAlt} {Qf : QuadraticForm K V} {ρ : Gsp BN →* (V ≃ₗ[K] V)}

section Conc

variable (hs : I4Setting hBN Qf ρ) (hconc : ∀ π, IsPlane BN π → Conc (planeFamily hBN ρ π))
  {ℓ H : Submodule K N}

theorem map_famSpace_of_mem_leviGroup (hH : IsLeviSpace BN ℓ H) {g : Gsp BN}
    (hg : g ∈ leviGroup BN H) :
    (famSpace hBN ρ ℓ).map (ρ g : V →ₗ[K] V) = famSpace hBN ρ ℓ := by
  rw [← famSpace_map, map_lin_eq_of_fixed g fun x hx => leviGroup_fix_line hH hg hx]

theorem exists_levi_hom (hH : IsLeviSpace BN ℓ H) :
    ∃ φ : leviGroup BN H →* (famSpace hBN ρ ℓ ≃ₗ[K] famSpace hBN ρ ℓ),
      ∀ (g : leviGroup BN H) (x : famSpace hBN ρ ℓ), ((φ g x : famSpace hBN ρ ℓ) : V) = ρ g x :=
  ⟨restrictHom (ρ.comp (leviGroup BN H).subtype) (famSpace hBN ρ ℓ)
      fun g => map_famSpace_of_mem_leviGroup hH g.2,
    fun g x => coe_restrictHom_apply _ _ _ g x⟩

include hs hconc

theorem levi_not_trivial_on_famSpace (hℓ : IsLine BN ℓ) (hH : IsLeviSpace BN ℓ H) :
    ¬ ∀ g ∈ leviGroup BN H, ∀ v ∈ famSpace hBN ρ ℓ, ρ g v = v := by
  intro htriv
  apply not_constLine hs hconc hℓ
  intro π π' hπ hπ' hℓπ hℓπ'
  obtain ⟨g, hg, hgπ⟩ := exists_mem_leviGroup_map_eq hBN hH hs.nondegN hπ hℓπ hπ' hℓπ'
  rw [← hgπ, concPt_map]
  exact (map_eq_of_forall_apply_eq fun v hv =>
    htriv g hg v (concPt_le_famSpace hs hconc hℓ hℓπ hv)).symm

theorem conc_finrank_eq_six : finrank K N = 6 := by
  by_contra hne
  have h8 : 8 ≤ finrank K N := by
    obtain ⟨r, hr⟩ := hBN.even_finrank hs.nondegN
    have := hs.dimN
    omega
  have hNpos : 0 < finrank K N := by omega
  have : Nontrivial N := Module.nontrivial_of_finrank_pos hNpos
  obtain ⟨a₁, ha₁⟩ := exists_ne (0 : N)
  obtain ⟨ℓ, hℓ, -⟩ := exists_isLine_of_ne_zero hBN hs.nondegN hs.dimN ha₁
  obtain ⟨H, hH⟩ := exists_isLeviSpace hBN hs.nondegN hℓ
  obtain ⟨φ, hφ⟩ := exists_levi_hom (ρ := ρ) hH
  have hφ1 : φ = 1 :=
    levi_hom_eq_one_of_eight_le hBN hs.nondegN hH hs.card h8
      (finrank_famSpace_isLine_conc hs hconc hℓ) φ
  refine levi_not_trivial_on_famSpace hs hconc hℓ hH fun g hg v hv => ?_
  have := hφ ⟨g, hg⟩ ⟨v, hv⟩
  rw [hφ1] at this
  simpa using this.symm

theorem concPt_injOn (hdim : finrank K N = 6) (hℓ : IsLine BN ℓ) {π π' : Submodule K N}
    (hπ : IsPlane BN π) (hπ' : IsPlane BN π') (hℓπ : ℓ ≤ π) (hℓπ' : ℓ ≤ π')
    (h : concPt hBN ρ π = concPt hBN ρ π') : π = π' := by
  by_contra hne
  obtain ⟨H, hH⟩ := exists_isLeviSpace hBN hs.nondegN hℓ
  obtain ⟨n, hn, hn0, rfl⟩ := exists_isPlane_eq_sup hBN hs.nondegN hH hπ hℓπ
  obtain ⟨n', hn', hn0', rfl⟩ := exists_isPlane_eq_sup hBN hs.nondegN hH hπ' hℓπ'
  have hind : LinearIndependent K ![n, n'] := by
    rw [LinearIndependent.pair_iff' hn0]
    rintro a rfl
    apply hne
    have ha : a ≠ 0 := fun ha => hn0' (by rw [ha, zero_smul])
    rw [Submodule.span_singleton_smul_eq (IsUnit.mk0 a ha)]
  have hstab : ∀ {m : N}, m ∈ BN.orthogonal H →
      ∀ g ∈ leviRoot hBN m, g ∈ stabSub ρ (concPt hBN ρ (ℓ ⊔ Submodule.span K {m})) := by
    intro m hm g hg
    have hfix := map_sup_span_eq_of_mem_leviRoot hBN hH hm hg
    rw [mem_stabSub, ← concPt_map, hfix]
  have hLstab : leviGroup BN H ≤ stabSub ρ (concPt hBN ρ (ℓ ⊔ Submodule.span K {n})) := by
    rw [← leviRoot_sup_eq_leviGroup hBN hs.nondegN hH hdim hn hn' hind]
    refine sup_le (fun g hg => hstab hn g hg) fun g hg => ?_
    have := hstab hn' g hg
    rwa [← h] at this
  have hP1 := finrank_concPt hs hconc hπ
  have hPA := concPt_le_famSpace hs hconc hℓ hℓπ
  obtain ⟨p, hp0, hpP⟩ := exists_ne_zero_span_eq_of_finrank_eq_one hP1
  obtain ⟨φ, hφ⟩ := exists_levi_hom (ρ := ρ) hH
  have hφ1 : φ ≠ 1 := fun h1 => levi_not_trivial_on_famSpace hs hconc hℓ hH fun g hg v hv => by
    have := hφ ⟨g, hg⟩ ⟨v, hv⟩
    rw [h1] at this
    simpa using this.symm
  have hpA : p ∈ famSpace hBN ρ ℓ := hPA (hpP ▸ Submodule.mem_span_singleton_self p)
  refine levi_hom_no_invariant_line hBN hs.nondegN hH hs.card hdim
    (finrank_famSpace_isLine_conc hs hconc hℓ) φ hφ1 ⟨⟨p, hpA⟩, ?_, fun g => ?_⟩
  · intro h0
    exact hp0 (congrArg Subtype.val h0)
  · have h1 := hLstab g.2
    rw [mem_stabSub] at h1
    have h2 : ρ g p ∈ concPt hBN ρ (ℓ ⊔ Submodule.span K {n}) := by
      rw [← h1]
      exact Submodule.mem_map_of_mem (hpP ▸ Submodule.mem_span_singleton_self p)
    rw [hpP] at h2
    obtain ⟨s, hs'⟩ := Submodule.mem_span_singleton.mp h2
    refine ⟨s, Subtype.ext ?_⟩
    rw [hφ g ⟨p, hpA⟩]
    exact hs'.symm

theorem conc_exists_plane_concPt_eq (hdim : finrank K N = 6) (hℓ : IsLine BN ℓ)
    {P : Submodule K V} (hP1 : finrank K P = 1) (hPA : P ≤ famSpace hBN ρ ℓ) :
    ∃ π, IsPlane BN π ∧ ℓ ≤ π ∧ concPt hBN ρ π = P := by
  obtain ⟨H, hH⟩ := exists_isLeviSpace hBN hs.nondegN hℓ
  have hS : Nat.card {π : Submodule K N // IsPlane BN π ∧ ℓ ≤ π} = Nat.card K + 1 :=
    card_isPlane_through hBN hs.nondegN hH hdim
  obtain ⟨s, hs'⟩ := exists_eq_of_injective_points (A := famSpace hBN ρ ℓ)
    (finrank_famSpace_isLine_conc hs hconc hℓ) hS
    (fun s => concPt hBN ρ s.1) (fun s => finrank_concPt hs hconc s.2.1)
    (fun s => concPt_le_famSpace hs hconc hℓ s.2.2)
    (fun s s' h => Subtype.ext (concPt_injOn hs hconc hdim hℓ s.2.1 s'.2.1 s.2.2 s'.2.2 h)) hP1 hPA
  exact ⟨s.1, s.2.1, s.2.2, hs'⟩

end Conc

end CFSG.ClassicalGroups.Orthogonal.SiegelRT1
