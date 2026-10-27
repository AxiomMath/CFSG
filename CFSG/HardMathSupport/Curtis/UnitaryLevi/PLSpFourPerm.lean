module

public import CFSG.Quasithin.H13.U3S1347P

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open Equiv Equiv.Perm Subgroup

theorem nonempty_inf_centralizer_equiv_of_injective {G G' : Type*} [Group G] [Group G']
    (f : G →* G') (hf : Function.Injective f) (H : Subgroup G) (H' : Subgroup G')
    (hH : H.map f = H') (t : G) :
    Nonempty (↥(H ⊓ centralizer {t}) ≃* ↥(H' ⊓ centralizer {f t})) := by
  have h : (H ⊓ centralizer {t}).map f = H' ⊓ centralizer {f t} := by
    ext x
    constructor
    · rintro ⟨y, ⟨hy, hyc⟩, rfl⟩
      have hy : y ∈ H := hy
      have hyc : y ∈ centralizer {t} := hyc
      refine ⟨hH ▸ Subgroup.mem_map_of_mem _ hy, ?_⟩
      rw [mem_centralizer_singleton_iff] at hyc
      show f y ∈ centralizer {f t}
      rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hyc]
    · rintro ⟨hx, hxc⟩
      obtain ⟨y, hy, rfl⟩ : x ∈ H.map f := hH ▸ hx
      have hy : y ∈ H := hy
      have hxc : f y ∈ centralizer {f t} := hxc
      refine ⟨y, ⟨hy, ?_⟩, rfl⟩
      rw [mem_centralizer_singleton_iff] at hxc
      show y ∈ centralizer {t}
      rw [mem_centralizer_singleton_iff]
      apply hf
      rw [map_mul, map_mul]
      exact hxc
  exact ⟨(Subgroup.equivMapOfInjective _ f hf).trans (MulEquiv.subgroupCongr h)⟩

theorem nonempty_inf_centralizer_equiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    (H : Subgroup G) (H' : Subgroup G') (hH : H.map e.toMonoidHom = H') (t : G) :
    Nonempty (↥(H ⊓ centralizer {t}) ≃* ↥(H' ⊓ centralizer {e t})) :=
  nonempty_inf_centralizer_equiv_of_injective e.toMonoidHom e.injective H H' hH t

theorem map_alternatingGroup_eq (e : Perm (Fin 6) ≃* Perm (Fin 6))
    (h : ∀ x, sign (e x) = sign x) :
    (alternatingGroup (Fin 6)).map e.toMonoidHom = alternatingGroup (Fin 6) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy : y ∈ alternatingGroup (Fin 6) := hy
    rw [mem_alternatingGroup] at hy
    show e y ∈ alternatingGroup (Fin 6)
    rw [mem_alternatingGroup]
    exact (h y).trans hy
  · intro hx
    rw [mem_alternatingGroup] at hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    show e.symm x ∈ alternatingGroup (Fin 6)
    rw [mem_alternatingGroup]
    have := h (e.symm x)
    rw [e.apply_symm_apply] at this
    exact this.symm.trans hx

theorem map_conj_alternatingGroup (g : Perm (Fin 6)) :
    (alternatingGroup (Fin 6)).map (MulAut.conj g).toMonoidHom = alternatingGroup (Fin 6) :=
  map_alternatingGroup_eq (MulAut.conj g) fun x => by
    change sign (g * x * g⁻¹) = sign x
    rw [map_mul, map_mul, map_inv, mul_comm (sign g), mul_assoc, mul_inv_cancel, mul_one]

@[expose] def emb4 : Perm (Fin 4) →* Perm (Fin 6) :=
  ((finSumFinEquiv : Fin 2 ⊕ Fin 4 ≃ Fin 6).permCongrHom).toMonoidHom.comp
    ((Equiv.Perm.sumCongrHom (Fin 2) (Fin 4)).comp (MonoidHom.inr _ _))

@[expose] def lift4 (ρ : Perm (Fin 4)) : Perm (Fin 6) :=
  if sign ρ = 1 then emb4 ρ else emb4 ρ * swap 0 1

theorem lift4_mul : ∀ ρ σ : Perm (Fin 4), lift4 (ρ * σ) = lift4 ρ * lift4 σ := by
  decide +kernel

theorem lift4_mem : ∀ ρ : Perm (Fin 4),
    sign (lift4 ρ) = 1 ∧ lift4 ρ * swap 0 1 = swap 0 1 * lift4 ρ := by
  decide +kernel

theorem lift4_inj : ∀ ρ : Perm (Fin 4), lift4 ρ = 1 → ρ = 1 := by
  decide +kernel

theorem card_alt_inf_centralizer_swap :
    Nat.card ↥(alternatingGroup (Fin 6) ⊓ centralizer {swap (0 : Fin 6) 1}) = 24 := by
  have : Nat.card ↥(alternatingGroup (Fin 6) ⊓ centralizer {swap (0 : Fin 6) 1}) =
      Fintype.card {σ : Perm (Fin 6) // sign σ = 1 ∧ σ * swap 0 1 = swap 0 1 * σ} := by
    rw [← Nat.card_eq_fintype_card]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun σ => ?_)
    simp [mem_alternatingGroup, mem_centralizer_singleton_iff]
  rw [this, Fintype.card_subtype]
  decide +kernel

theorem nonempty_alt_inf_centralizer_swap :
    Nonempty (↥(alternatingGroup (Fin 6) ⊓ centralizer {swap (0 : Fin 6) 1}) ≃*
      Perm (Fin 4)) := by
  let ℓ : Perm (Fin 4) →* Perm (Fin 6) := MonoidHom.mk' lift4 lift4_mul
  let ℓ' : Perm (Fin 4) →*
      ↥(alternatingGroup (Fin 6) ⊓ centralizer {swap (0 : Fin 6) 1}) :=
    ℓ.codRestrict _ fun ρ => ⟨mem_alternatingGroup.mpr (lift4_mem ρ).1,
      mem_centralizer_singleton_iff.mpr (lift4_mem ρ).2⟩
  have hinj : Function.Injective ℓ' := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro ρ hρ
    rw [Subgroup.mem_bot]
    apply lift4_inj
    have h1 : ℓ' ρ = 1 := hρ
    exact congrArg Subtype.val h1
  have hcard : Nat.card ↥(alternatingGroup (Fin 6) ⊓ centralizer {swap (0 : Fin 6) 1}) ≤
      Nat.card (Perm (Fin 4)) := by
    rw [card_alt_inf_centralizer_swap, Nat.card_eq_fintype_card, Fintype.card_perm,
      Fintype.card_fin]
    decide
  exact ⟨(MulEquiv.ofBijective ℓ' (hinj.bijective_of_nat_card_le hcard)).symm⟩

theorem phi_swap_zero_one : CFSG.Quasithin.H13.U3.S6Out.phi (swap 0 1) =
    swap 0 2 * swap 1 3 * swap 4 5 := by
  decide +kernel

theorem odd_involution_conj : ∀ σ : Perm (Fin 6), σ * σ = 1 → sign σ = -1 →
    (∃ g : Perm (Fin 6), g * σ * g⁻¹ = swap 0 1) ∨
      (∃ g : Perm (Fin 6), g * σ * g⁻¹ = swap 0 2 * swap 1 3 * swap 4 5) := by
  decide +kernel

theorem nonempty_alt_inf_centralizer_of_odd_involution (σ : Perm (Fin 6)) (h2 : σ * σ = 1)
    (hs : sign σ = -1) :
    Nonempty (↥(alternatingGroup (Fin 6) ⊓ centralizer {σ}) ≃* Perm (Fin 4)) := by
  obtain ⟨e0⟩ := nonempty_alt_inf_centralizer_swap
  rcases odd_involution_conj σ h2 hs with ⟨g, hg⟩ | ⟨g, hg⟩
  · obtain ⟨e1⟩ := nonempty_inf_centralizer_equiv (MulAut.conj g) _ _
      (map_conj_alternatingGroup g) σ
    have hg' : (MulAut.conj g) σ = swap 0 1 := hg
    rw [hg'] at e1
    exact ⟨e1.trans e0⟩
  · obtain ⟨e1⟩ := nonempty_inf_centralizer_equiv (MulAut.conj g) _ _
      (map_conj_alternatingGroup g) σ
    obtain ⟨e2⟩ := nonempty_inf_centralizer_equiv CFSG.Quasithin.H13.U3.S6Out.phiEquiv _ _
      (map_alternatingGroup_eq _ CFSG.Quasithin.H13.U3.S6Out.sign_phi) (swap 0 1)
    have hg' : (MulAut.conj g) σ = swap 0 2 * swap 1 3 * swap 4 5 := hg
    have hphi : CFSG.Quasithin.H13.U3.S6Out.phiEquiv (swap 0 1) =
        swap 0 2 * swap 1 3 * swap 4 5 := phi_swap_zero_one
    rw [hg'] at e1
    rw [hphi] at e2
    exact ⟨e1.trans (e2.symm.trans e0)⟩

end CFSG.HardMathSupport.Curtis.UnitaryLevi
