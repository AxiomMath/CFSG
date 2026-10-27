module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AltBig.Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.QuasithinUnique.L246C127.AltBig

open Equiv Equiv.Perm Subgroup

variable {α : Type} [Fintype α] [DecidableEq α]

theorem sylApplyInv (σ : Perm α) (z : α) : σ (σ⁻¹ z) = z := by
  rw [← Perm.mul_apply, mul_inv_cancel, Perm.one_apply]

theorem sylInvApply (σ : Perm α) (z : α) : σ⁻¹ (σ z) = z := by
  rw [← Perm.mul_apply, inv_mul_cancel, Perm.one_apply]

theorem exists_fpfInv (hα : Even (Fintype.card α)) : Nonempty (FpfInv α) := by
  obtain ⟨r, hr⟩ := hα
  have hcard : Fintype.card α = Fintype.card (Fin r × Bool) := by
    simp only [hr, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
    omega
  let e : α ≃ Fin r × Bool := Fintype.equivOfCardEq hcard
  let μ' : Perm (Fin r × Bool) :=
    { toFun := fun z => (z.1, !z.2), invFun := fun z => (z.1, !z.2),
      left_inv := fun z => by simp, right_inv := fun z => by simp }
  have hμ'inv : ∀ z, μ' (μ' z) = z := by
    rintro ⟨i, b⟩
    simp [μ']
  have hμ'fpf : ∀ z, μ' z ≠ z := by
    rintro ⟨i, b⟩ h
    cases b <;> simp [μ'] at h
  refine ⟨⟨e.trans (μ'.trans e.symm), ?_, ?_⟩⟩
  · intro x
    simp [hμ'inv]
  · intro x h
    have h' : e.symm (μ' (e x)) = x := h
    have h'' : μ' (e x) = e x := by
      have := congrArg e h'
      simpa using this
    exact hμ'fpf (e x) h''

@[expose] def FpfInv.transport (p : FpfInv α) (σ : Perm α) : FpfInv α where
  μ := σ * p.μ * σ⁻¹
  inv x := by
    simp only [Perm.mul_apply, sylInvApply, sylApplyInv, p.inv]
  fpf x h := by
    apply p.fpf (σ⁻¹ x)
    have h' : σ (p.μ (σ⁻¹ x)) = x := h
    calc p.μ (σ⁻¹ x) = σ⁻¹ (σ (p.μ (σ⁻¹ x))) := (sylInvApply σ _).symm
      _ = σ⁻¹ x := by rw [h']

theorem FpfInv.transport_μ_apply (p : FpfInv α) (σ : Perm α) (x : α) :
    (p.transport σ).μ (σ x) = σ (p.μ x) := by
  change σ (p.μ (σ⁻¹ (σ x))) = σ (p.μ x)
  rw [sylInvApply]

@[expose] def sylPairSub (p : FpfInv α) : Subgroup (Perm α) where
  carrier := {σ | ∀ x, σ x = x ∨ σ x = p.μ x}
  mul_mem' := by
    intro a b ha hb z
    have ha' : ∀ x, a x = x ∨ a x = p.μ x := ha
    have hb' : ∀ x, b x = x ∨ b x = p.μ x := hb
    rcases hb' z with h | h
    · rw [Perm.mul_apply, h]
      exact ha' z
    · rw [Perm.mul_apply, h]
      rcases ha' (p.μ z) with h' | h'
      · exact Or.inr h'
      · exact Or.inl (by rw [h', p.inv])
  one_mem' := fun z => Or.inl rfl
  inv_mem' := by
    intro σ hσ z
    have hσ' : ∀ x, σ x = x ∨ σ x = p.μ x := hσ
    have h1 : σ (σ⁻¹ z) = z := sylApplyInv σ z
    rcases hσ' (σ⁻¹ z) with h | h
    · exact Or.inl (h1.symm.trans h).symm
    · have hz : z = p.μ (σ⁻¹ z) := h1.symm.trans h
      have h2 : p.μ z = σ⁻¹ z := by
        have := congrArg p.μ hz
        rwa [p.inv] at this
      exact Or.inr h2.symm

theorem mem_sylPairSub {p : FpfInv α} {σ : Perm α} :
    σ ∈ sylPairSub p ↔ ∀ x, σ x = x ∨ σ x = p.μ x := Iff.rfl

theorem sylPairSub_mul_self {p : FpfInv α} {σ : Perm α} (hσ : σ ∈ sylPairSub p) :
    σ * σ = 1 := by
  have hσ' := mem_sylPairSub.mp hσ
  ext z
  rw [Perm.mul_apply, Perm.one_apply]
  rcases hσ' z with h | h
  · rw [h, h]
  · rw [h]
    rcases hσ' (p.μ z) with h' | h'
    · exact absurd (σ.injective (h.trans h'.symm)).symm (p.fpf z)
    · rw [h', p.inv]

theorem isPGroup_two_sylPairSub (p : FpfInv α) :
    IsPGroup 2 ↥((sylPairSub p).subgroupOf (alternatingGroup α)) := by
  intro g
  refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
  have hg := sylPairSub_mul_self (Subgroup.mem_subgroupOf.mp g.2)
  simpa [pow_two] using hg

theorem swap_pair_apply (p : FpfInv α) (x z : α) :
    swap x (p.μ x) z = z ∨ swap x (p.μ x) z = p.μ z := by
  by_cases hzx : z = x
  · subst hzx
    exact Or.inr (Equiv.swap_apply_left _ _)
  by_cases hzμ : z = p.μ x
  · subst hzμ
    exact Or.inr (by rw [Equiv.swap_apply_right, p.inv])
  exact Or.inl (Equiv.swap_apply_of_ne_of_ne hzx hzμ)

theorem swap_mem_sylPairSub (p : FpfInv α) (x : α) : swap x (p.μ x) ∈ sylPairSub p :=
  mem_sylPairSub.mpr (swap_pair_apply p x)

theorem swap_mul_swap_mem_alt (p : FpfInv α) (x y : α) :
    swap x (p.μ x) * swap y (p.μ y) ∈ alternatingGroup α := by
  rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul,
    Equiv.Perm.sign_swap (p.fpf x).symm, Equiv.Perm.sign_swap (p.fpf y).symm]
  rfl

theorem swap_mul_swap_mem_sylPairSub (p : FpfInv α) (x y : α) :
    swap x (p.μ x) * swap y (p.μ y) ∈ sylPairSub p :=
  mul_mem (swap_mem_sylPairSub p x) (swap_mem_sylPairSub p y)

theorem exists_contained_of_sylow (hα : Even (Fintype.card α)) {T : Subgroup ↥(alternatingGroup α)}
    (hT : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤) :
    ∃ p : FpfInv α, p.Contained (T.map (alternatingGroup α).subtype) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨p₀⟩ := exists_fpfInv hα
  obtain ⟨S, hBS⟩ := (isPGroup_two_sylPairSub p₀).exists_le_sylow
  have hidx : ¬ 2 ∣ T.index := by
    have := hT.2.2
    rwa [show (T.subgroupOf ⊤).index = T.index from Subgroup.relIndex_top_right T] at this
  let T' : Sylow 2 ↥(alternatingGroup α) := hT.2.1.toSylow hidx
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥(alternatingGroup α) S T'
  have hgT : (S : Subgroup ↥(alternatingGroup α)).map (MulAut.conj g).toMonoidHom = T := by
    have h := congrArg
      (fun Q : Sylow 2 ↥(alternatingGroup α) => (Q : Subgroup ↥(alternatingGroup α))) hg
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at h
    exact h
  refine ⟨p₀.transport (g : Perm α), ?_⟩
  intro x y _ _
  obtain ⟨x₀, rfl⟩ : ∃ x₀, x = (g : Perm α) x₀ :=
    ⟨(g : Perm α)⁻¹ x, (sylApplyInv _ _).symm⟩
  obtain ⟨y₀, rfl⟩ : ∃ y₀, y = (g : Perm α) y₀ :=
    ⟨(g : Perm α)⁻¹ y, (sylApplyInv _ _).symm⟩
  rw [FpfInv.transport_μ_apply p₀ (g : Perm α) x₀, FpfInv.transport_μ_apply p₀ (g : Perm α) y₀,
    Equiv.swap_apply_apply (g : Perm α) x₀ (p₀.μ x₀),
    Equiv.swap_apply_apply (g : Perm α) y₀ (p₀.μ y₀)]
  have key : (g : Perm α) * swap x₀ (p₀.μ x₀) * (g : Perm α)⁻¹ *
      ((g : Perm α) * swap y₀ (p₀.μ y₀) * (g : Perm α)⁻¹) =
      (g : Perm α) * (swap x₀ (p₀.μ x₀) * swap y₀ (p₀.μ y₀)) * (g : Perm α)⁻¹ := by
    simp only [mul_assoc, inv_mul_cancel_left]
  rw [key]
  let u : ↥(alternatingGroup α) :=
    ⟨swap x₀ (p₀.μ x₀) * swap y₀ (p₀.μ y₀), swap_mul_swap_mem_alt p₀ x₀ y₀⟩
  have hu : u ∈ (sylPairSub p₀).subgroupOf (alternatingGroup α) :=
    Subgroup.mem_subgroupOf.mpr (swap_mul_swap_mem_sylPairSub p₀ x₀ y₀)
  have hconj : MulAut.conj g u ∈ T := by
    rw [← hgT]
    exact Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom (hBS hu)
  refine Subgroup.mem_map.mpr ⟨MulAut.conj g u, hconj, ?_⟩
  rfl

end CFSG.QuasithinUnique.L246C127.AltBig
