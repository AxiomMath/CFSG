module

public import CFSG.Fischer.Uniq.Rigidity
public import CFSG.Fischer.Aut.TauGroup

public section

namespace CFSG.Fischer

open CFSG.Blueprint.Fischer

variable {X : Type} [Group X] {E : Set X}

theorem tauGroup_commute_iff (hE : Pair X E) {σ : Equiv.Perm E} (hσ : σ ∈ tauGroup hE)
    (x y : E) : (x : X) * y = y * x ↔ ((σ x : E) : X) * σ y = σ y * σ x := by
  rw [← Pair.tauE_eq_self_iff hE x y, ← Pair.tauE_eq_self_iff hE (σ x) (σ y), ← hσ x y]
  exact σ.injective.eq_iff.symm

@[expose] def stabT (hE : Pair X E) {d : X} (hd : d ∈ E) : Subgroup (tauGroup hE) where
  carrier := {σ | (σ : Equiv.Perm E) ⟨d, hd⟩ = ⟨d, hd⟩}
  one_mem' := rfl
  mul_mem' {σ π} hσ hπ := by
    show (σ : Equiv.Perm E) ((π : Equiv.Perm E) ⟨d, hd⟩) = ⟨d, hd⟩
    rw [show (π : Equiv.Perm E) ⟨d, hd⟩ = ⟨d, hd⟩ from hπ]
    exact hσ
  inv_mem' {σ} hσ := by
    show ((σ : Equiv.Perm E))⁻¹ ⟨d, hd⟩ = ⟨d, hd⟩
    rw [Equiv.Perm.inv_eq_iff_eq]
    exact (show (σ : Equiv.Perm E) ⟨d, hd⟩ = ⟨d, hd⟩ from hσ).symm

theorem stabT_mem_star (hE : Pair X E) {d : X} (hd : d ∈ E) (σ : stabT hE hd)
    {f : X} (hf : f ∈ LocalClass E d) :
    ((((σ : tauGroup hE) : Equiv.Perm E) ⟨f, hf.1⟩ : E) : X) ∈ LocalClass E d := by
  have hσd : ((σ : tauGroup hE) : Equiv.Perm E) ⟨d, hd⟩ = ⟨d, hd⟩ := σ.2
  have hc := (tauGroup_commute_iff hE (σ : tauGroup hE).2 ⟨f, hf.1⟩ ⟨d, hd⟩).1 hf.2.2
  rw [hσd] at hc
  refine ⟨(((σ : tauGroup hE) : Equiv.Perm E) ⟨f, hf.1⟩).2, fun e => hf.2.1 ?_, hc⟩
  have : ((σ : tauGroup hE) : Equiv.Perm E) ⟨f, hf.1⟩ = ((σ : tauGroup hE) : Equiv.Perm E)
      ⟨d, hd⟩ := by rw [hσd]; exact Subtype.ext e
  exact congrArg Subtype.val (Equiv.injective _ this)

@[expose] noncomputable def resStar (hE : Pair X E) {d : X} (hd : d ∈ E) :
    stabT hE hd →* Equiv.Perm (LocalClass E d) where
  toFun σ :=
    { toFun := fun f => ⟨_, stabT_mem_star hE hd σ f.2⟩
      invFun := fun f => ⟨_, stabT_mem_star hE hd σ⁻¹ f.2⟩
      left_inv := fun f => Subtype.ext (by
        show ((((σ⁻¹ : stabT hE hd) : tauGroup hE) : Equiv.Perm E)
          (((σ : tauGroup hE) : Equiv.Perm E) ⟨f, f.2.1⟩) : X) = f
        rw [show ((σ⁻¹ : stabT hE hd) : tauGroup hE) = (σ : tauGroup hE)⁻¹ from rfl]
        simp)
      right_inv := fun f => Subtype.ext (by
        show ((((σ : tauGroup hE) : Equiv.Perm E)
          ((((σ⁻¹ : stabT hE hd) : tauGroup hE) : Equiv.Perm E) ⟨f, f.2.1⟩)) : X) = f
        rw [show ((σ⁻¹ : stabT hE hd) : tauGroup hE) = (σ : tauGroup hE)⁻¹ from rfl]
        simp) }
  map_one' := by ext f; rfl
  map_mul' σ π := by ext f; rfl

theorem resStar_apply (hE : Pair X E) {d : X} (hd : d ∈ E) (σ : stabT hE hd)
    (f : LocalClass E d) :
    ((resStar hE hd σ f : LocalClass E d) : X) =
      (((σ : tauGroup hE) : Equiv.Perm E) ⟨f, f.2.1⟩ : X) := rfl

theorem connected_of_D2 {V : Type*} {G : SimpleGraph V} (r : V)
    (hD2 : ∀ v, v ≠ r → ¬ G.Adj r v → ∃ x, G.Adj r x ∧ G.Adj x v) : G.Connected := by
  have : Nonempty V := ⟨r⟩
  refine (SimpleGraph.connected_iff_exists_forall_reachable G).2 ⟨r, fun v => ?_⟩
  by_cases h0 : v = r
  · rw [h0]
  · by_cases h1 : G.Adj r v
    · exact h1.reachable
    · obtain ⟨x, hrx, hxv⟩ := hD2 v h0 h1
      exact hrx.reachable.trans hxv.reachable

section Bound

variable {P : Type} {M : LocalModel P} (hE : Pair X E) {d : X} (hd : d ∈ E)
  (L : LocalPoints M E d) {𝒮 : Set (Set P)} (h : CoverHyp L 𝒮) (hXi : (M.xi 𝒮).Connected)
  (hmu : ∀ c ∈ E, c * d ≠ d * c → (muSet E d c).Nonempty)
include hE hd L h hXi hmu

theorem Pair.card_ker_resStar_le : Nat.card (resStar hE hd).ker ≤ 2 := by
  have := Pair.finite hE
  set τd : stabT hE hd := ⟨innerTau hE d, by
    show (Pair.conjPerm hE d) ⟨d, hd⟩ = ⟨d, hd⟩
    apply Subtype.ext
    rw [Pair.conjPerm_apply, Pair.inv_eq hE hd, mul_assoc, Pair.mul_self hE hd, mul_one]⟩
  have hsub : ((resStar hE hd).ker : Set (stabT hE hd)) ⊆ {1, τd} := by
    intro σ hσ
    have hstar : ∀ f : E, (f : X) ∈ LocalClass E d →
        (((σ : tauGroup hE) : Equiv.Perm E) f : X) = f := by
      intro f hf
      have := congrArg
        (fun π : Equiv.Perm (LocalClass E d) => ((π ⟨f, hf⟩ : LocalClass E d) : X))
        (MonoidHom.mem_ker.1 hσ)
      exact this
    rcases Pair.rigidity hE hd L h hXi hmu ((σ : tauGroup hE) : Equiv.Perm E)
      (tauGroup_commute_iff hE (σ : tauGroup hE).2) (congrArg Subtype.val σ.2) hstar with
      h1 | h1
    · left
      apply Subtype.ext; apply Subtype.ext
      exact Equiv.ext h1
    · right
      apply Subtype.ext; apply Subtype.ext
      ext x
      rw [h1 x]
      show d * x * d = (Pair.conjPerm hE d x : X)
      rw [Pair.conjPerm_apply, Pair.inv_eq hE hd]
  calc Nat.card (resStar hE hd).ker = ((resStar hE hd).ker : Set (stabT hE hd)).ncard :=
        (Nat.card_coe_set_eq _).symm
    _ ≤ ({1, τd} : Set (stabT hE hd)).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ 2 := (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])

theorem Pair.card_stabT_le {K : Subgroup (Equiv.Perm P)}
    (hK : ∀ σ : stabT hE hd, Equiv.permCongrHom L.χ (resStar hE hd σ) ∈ K) :
    Nat.card (stabT hE hd) ≤ 2 * Nat.card K := by
  have := Pair.finite hE
  have : Finite (Equiv.Perm P) := by
    have : Finite (LocalClass E d) := Subtype.finite
    exact Finite.of_equiv _ (Equiv.permCongr L.χ)
  set ρ := ((Equiv.permCongrHom L.χ : Equiv.Perm (LocalClass E d) ≃* Equiv.Perm P) :
    Equiv.Perm (LocalClass E d) →* Equiv.Perm P).comp (resStar hE hd)
  have hker : ρ.ker = (resStar hE hd).ker := by
    ext σ
    simp only [ρ, MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply, MonoidHom.coe_ofClass,
      MulEquiv.map_eq_one_iff]
  have hrange : ρ.range ≤ K := by
    rintro _ ⟨σ, rfl⟩
    exact hK σ
  have h1 : Nat.card (stabT hE hd) = Nat.card ρ.ker * Nat.card ρ.range := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv, mul_comm,
      ← Subgroup.card_eq_card_quotient_mul_card_subgroup]
  rw [h1, hker]
  exact Nat.mul_le_mul (Pair.card_ker_resStar_le hE hd L h hXi hmu)
    (Subgroup.card_le_of_le hrange)

end Bound

end CFSG.Fischer
