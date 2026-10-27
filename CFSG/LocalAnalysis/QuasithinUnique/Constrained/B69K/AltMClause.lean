module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69K.AltStab
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69K.AltSylow
public import CFSG.Quasithin.Background.FFC13D

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped commutatorElement

namespace B69K

open CFSG.Quasithin.B69

theorem conj_inv_mem {G : Type*} [Group G] {H : Subgroup G} [Finite H] {s : G}
    (hs : ∀ v ∈ H, s * v * s⁻¹ ∈ H) : ∀ v ∈ H, s⁻¹ * v * s ∈ H := by
  let f : H → H := fun v => ⟨s * v * s⁻¹, hs v v.2⟩
  have hinj : Function.Injective f := by
    intro a b h
    have h1 : s * (a : G) * s⁻¹ = s * (b : G) * s⁻¹ := congrArg Subtype.val h
    exact Subtype.ext (by simpa using h1)
  have hsurj := Finite.injective_iff_surjective.1 hinj
  intro v hv
  obtain ⟨w, hw⟩ := hsurj ⟨v, hv⟩
  have h1 : s * (w : G) * s⁻¹ = v := congrArg Subtype.val hw
  have h2 : s⁻¹ * v * s = (w : G) := by
    rw [← h1]
    group
  rw [h2]
  exact w.2

section Main

variable {V : Type} [CommGroup V] [Finite V]

theorem mStructure_general {X T M A L : Subgroup (MulAut V)}
    (hmp : MinParabolic X T M) (hO2 : CFSG.Open.pCoreOf 2 X = ⊥)
    (hL : CFSG.Open.IsComponentOf L X) (hAX : A ≤ X)
    (hAc : ∀ L' : Subgroup (MulAut V), CFSG.Open.IsComponentOf L' X → L ≠ L' → ⁅L', A⁆ = ⊥)
    {m : ℕ} (hodd : Odd m) (hm : 7 ≤ m)
    (π' : Equiv.Perm (Fin m) →* ↥(L ⊔ A)) (hπ'i : Function.Injective π')
    (hπ's : Function.Surjective π')
    (hLeq : L = (alternatingGroup (Fin m)).map ((L ⊔ A).subtype.comp π')) :
    ∃ ρ : Equiv.Perm (Fin m), (M ⊓ (L ⊔ A)).subgroupOf (L ⊔ A) =
      (MulAction.stabilizer (Equiv.Perm (Fin m)) (⟨0, by omega⟩ : Fin m)).map
        (π'.comp (MulAut.conj ρ).toMonoidHom) := by
  have hLAX : L ⊔ A ≤ X := sup_le hL.1 hAX
  have hTL : CFSG.QuasithinUnique.IsSylowTwoOf (T ⊓ L) L :=
    A312.isSylowTwoOf_inf_of_subnormal hL.2.1 hmp.isSylow
  set φ : Equiv.Perm (Fin m) →* MulAut V := (L ⊔ A).subtype.comp π' with hφ
  have hφi : Function.Injective φ := fun a b h => hπ'i (Subtype.ext h)
  have hφmem : ∀ σ, φ σ ∈ L ⊔ A := fun σ => (π' σ).2
  have hLφ : ∀ x ∈ L, ∃ τ ∈ alternatingGroup (Fin m), φ τ = x := fun x hx =>
    Subgroup.mem_map.1 (hLeq.le hx)
  set V₀ : Subgroup (Equiv.Perm (Fin m)) := (T ⊓ L).comap φ with hV₀
  have hV₀A : V₀ ≤ alternatingGroup (Fin m) := by
    intro σ hσ
    obtain ⟨τ, hτ, hτσ⟩ := hLφ (φ σ) (hσ : φ σ ∈ T ⊓ L).2
    rwa [← hφi hτσ]
  have hV₀2 : IsPGroup 2 V₀ := hTL.2.1.comap_of_injective φ hφi
  have hV₀idx : ¬ 2 ∣ (V₀.subgroupOf (alternatingGroup (Fin m))).index := by
    have hsurj : Function.Surjective
        ((φ.comp (alternatingGroup (Fin m)).subtype).codRestrict L (fun a => by
          rw [hLeq]; exact ⟨a, a.2, rfl⟩)) := by
      intro x
      obtain ⟨τ, hτ, hτx⟩ := hLφ x x.2
      exact ⟨⟨τ, hτ⟩, Subtype.ext hτx⟩
    have hc : V₀.subgroupOf (alternatingGroup (Fin m)) =
        ((T ⊓ L).subgroupOf L).comap
          ((φ.comp (alternatingGroup (Fin m)).subtype).codRestrict L (fun a => by
            rw [hLeq]; exact ⟨a, a.2, rfl⟩)) := by
      ext a
      have haL : φ (a : Equiv.Perm (Fin m)) ∈ L := by
        rw [hLeq]
        exact ⟨a, a.2, rfl⟩
      simp [hV₀, Subgroup.mem_subgroupOf, haL]
    rw [hc, Subgroup.index_comap_of_surjective _ hsurj]
    exact hTL.2.2
  obtain ⟨p, hp, hpu⟩ := sylow_alt_unique_fixed hodd (by omega) hV₀A hV₀2 hV₀idx
  obtain ⟨s, hs, hsn⟩ := exists_odd_normalizing hodd (by omega) hV₀A hV₀2 hV₀idx
  have hsn' : ∀ v ∈ V₀, s⁻¹ * v * s ∈ V₀ := conj_inv_mem hsn
  have hsp : s p = p := by
    apply hpu
    intro v hv
    have h1 : s⁻¹ * v * s ∈ V₀ := hsn' v hv
    have h2 := hp _ h1
    simp only [Equiv.Perm.mul_apply] at h2
    have h3 : v (s p) = s p := by
      have := congrArg s h2
      simpa using this
    exact h3
  have hStab := stab_le_M hmp hO2 hL (by omega) (by omega) φ hφi hLeq hp hpu
  have hs_in : φ s ∈ M := by
    refine mem_M_of_conj_closed hmp hO2 hL hTL (hLAX (hφmem s)) ?_ ?_ ?_
    · intro y hy
      obtain ⟨τ, -, rfl⟩ := hLφ y hy.2
      have hτ : τ ∈ V₀ := hy
      have h := hsn τ hτ
      have h' : φ (s * τ * s⁻¹) ∈ T ⊓ L := h
      simpa only [map_mul, map_inv] using h'
    · intro y hy
      obtain ⟨τ, -, rfl⟩ := hLφ y hy.2
      have hτ : τ ∈ V₀ := hy
      have h := hsn' τ hτ
      have h' : φ (s⁻¹ * τ * s) ∈ T ⊓ L := h
      simpa only [map_mul, map_inv, inv_inv] using h'
    · intro L' hL' hne z hz
      exact commute_of_mem_sup_of_ne hL hAc hL' hne (hφmem s) z hz
  set R : Subgroup (Equiv.Perm (Fin m)) := M.comap φ with hR
  have hSR : MulAction.stabilizer (Equiv.Perm (Fin m)) p ≤ R := by
    intro σ hσ
    have hσp : σ p = p := MulAction.mem_stabilizer_iff.1 hσ
    show φ σ ∈ M
    by_cases hev : σ ∈ alternatingGroup (Fin m)
    · exact hStab σ hev hσp
    · have h1 : σ * s⁻¹ ∈ alternatingGroup (Fin m) := by
        rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, map_inv]
        have h2 : Equiv.Perm.sign σ ≠ 1 := fun h => hev (Equiv.Perm.mem_alternatingGroup.2 h)
        have h3 : Equiv.Perm.sign s ≠ 1 := fun h => hs (Equiv.Perm.mem_alternatingGroup.2 h)
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
        · exact absurd h h2
        rcases Int.units_eq_one_or (Equiv.Perm.sign s) with h' | h'
        · exact absurd h' h3
        rw [h, h']
        decide
      have hsinv : s⁻¹ p = p := by
        rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq]
        exact hsp.symm
      have h2 : (σ * s⁻¹) p = p := by
        rw [Equiv.Perm.mul_apply, hsinv, hσp]
      have h3 := hStab (σ * s⁻¹) h1 h2
      have h4 : φ σ = φ (σ * s⁻¹) * φ s := by
        rw [← map_mul]
        congr 1
        group
      rw [h4]
      exact M.mul_mem h3 hs_in
  have hRtop : R ≠ ⊤ := by
    intro htop
    apply not_component_le_M hmp hO2 hL
    intro x hx
    obtain ⟨τ, -, rfl⟩ := hLφ x hx
    have : τ ∈ R := htop ▸ Subgroup.mem_top τ
    exact this
  haveI : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.2 (by omega)
  have hcoatom : IsCoatom (MulAction.stabilizer (Equiv.Perm (Fin m)) p) :=
    MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive (Equiv.Perm (Fin m)) p
  have hReq : R = MulAction.stabilizer (Equiv.Perm (Fin m)) p :=
    (hcoatom.le_iff.1 hSR).resolve_left hRtop
  have hσR : ∀ σ : Equiv.Perm (Fin m), φ σ ∈ M ↔ σ p = p := by
    intro σ
    have h : σ ∈ R ↔ σ ∈ MulAction.stabilizer (Equiv.Perm (Fin m)) p := by rw [hReq]
    exact h.trans MulAction.mem_stabilizer_iff
  set a : Fin m := ⟨0, by omega⟩ with ha
  have hρa : Equiv.swap a p a = p := Equiv.swap_apply_left a p
  have hρp : Equiv.swap a p p = a := Equiv.swap_apply_right a p
  have hρρ : Equiv.swap a p * Equiv.swap a p = 1 := Equiv.swap_mul_self a p
  have hρi : (Equiv.swap a p)⁻¹ = Equiv.swap a p := Equiv.swap_inv a p
  refine ⟨Equiv.swap a p, ?_⟩
  ext x
  obtain ⟨σ, rfl⟩ := hπ's x
  constructor
  · intro hx
    have hσ : σ p = p := (hσR σ).1 hx.1
    refine ⟨Equiv.swap a p * σ * Equiv.swap a p, ?_, ?_⟩
    · show (Equiv.swap a p * σ * Equiv.swap a p) a = a
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hρa, hσ, hρp]
    · show π' (MulAut.conj (Equiv.swap a p) (Equiv.swap a p * σ * Equiv.swap a p)) = π' σ
      rw [MulAut.conj_apply]
      have : Equiv.swap a p * (Equiv.swap a p * σ * Equiv.swap a p) * (Equiv.swap a p)⁻¹ =
          (Equiv.swap a p * Equiv.swap a p) * σ := by group
      rw [this, hρρ, one_mul]
  · rintro ⟨τ, hτ, hτσ⟩
    have h1 : MulAut.conj (Equiv.swap a p) τ = σ := hπ'i hτσ
    rw [MulAut.conj_apply, hρi] at h1
    have hτa : τ a = a := MulAction.mem_stabilizer_iff.1 hτ
    have hσp : σ p = p := by
      rw [← h1, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hρp, hτa, hρa]
    exact ⟨(hσR σ).2 hσp, (π' σ).2⟩

end Main

end B69K

end CFSG.Quasithin
