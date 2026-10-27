module

public import CFSG.HardMathSupport.Solomon.Coordinator.L5Lift

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.HardMathSupport.Solomon.Proving

@[expose] def HasTorus (p r : ℕ) (K : Type*) [Group K] (β : MulAut K) : Prop :=
  ∃ E : Subgroup K, IsElemAbelian p E ∧ Nat.card E = p ^ r ∧ E ⊓ Subgroup.center K = ⊥ ∧
    ∀ x ∈ E, β x = x

variable {L S : Type*} [Group L] [Group S] [Finite L] {p r : ℕ} [NeZero r] {Γ : L →* S}

theorem hasTorus_of_torusData (hp : p.Prime) (hΓ : Function.Surjective Γ)
    (hker : Γ.ker = Subgroup.center L) (hodd : Odd (Nat.card (Subgroup.center L)))
    (D : TorusData (Fin r) p S) (hcard : Nat.card (Subgroup.closure (Set.range D.X)) = p ^ r) :
    HasTorus p r L 1 := by
  obtain ⟨E, hE, hEker, hEmap⟩ := exists_cover_torus hp D Γ hΓ hker.le (by rw [hker]; exact hodd)
  refine ⟨E, hE, ?_, by rw [← hker]; exact hEker, fun x _ => rfl⟩
  have hinj : Function.Injective (Γ.domRestrict E) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx' : (x : L) ∈ E ⊓ Γ.ker := ⟨x.2, hx⟩
    rw [hEker, Subgroup.mem_bot] at hx'
    exact Subtype.ext hx'
  rw [← hcard, ← hEmap, ← MonoidHom.domRestrict_range]
  exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv

theorem hasTorus_of_fixData (hp : p.Prime) (hker : Γ.ker = Subgroup.center L)
    (hodd : Odd (Nat.card (Subgroup.center L))) (β : MulAut L)
    (D : TorusData (Fin r) p ↥((autFix β).map Γ))
    (hcard : Nat.card (Subgroup.closure (Set.range D.X)) = p ^ r) : HasTorus p r L β := by
  classical
  let Γ' : ↥(autFix β) →* ↥((autFix β).map Γ) :=
    (Γ.comp (autFix β).subtype).codRestrict ((autFix β).map Γ) (fun x => ⟨x, x.2, rfl⟩)
  have hΓ'apply : ∀ x : ↥(autFix β), ((Γ' x : ↥((autFix β).map Γ)) : S) = Γ x := fun x => rfl
  have hΓ's : Function.Surjective Γ' := by
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hker' : ∀ x : ↥(autFix β), x ∈ Γ'.ker ↔ (x : L) ∈ Γ.ker := by
    intro x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, ← hΓ'apply]
    exact ⟨fun h => by rw [h]; rfl, fun h => Subtype.ext h⟩
  have hZ' : Γ'.ker ≤ Subgroup.center ↥(autFix β) := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hxZ : (x : L) ∈ Subgroup.center L := hker ▸ (hker' x).1 hx
    exact Subgroup.mem_center_iff.1 hxZ y
  have hodd' : Odd (Nat.card Γ'.ker) := by
    have hle : (Γ'.ker.map (autFix β).subtype) ≤ Subgroup.center L := by
      rintro _ ⟨x, hx, rfl⟩
      exact hker ▸ (hker' x).1 hx
    have hdvd : Nat.card Γ'.ker ∣ Nat.card (Subgroup.center L) := by
      rw [← Subgroup.card_map_of_injective (autFix β).subtype_injective]
      exact Subgroup.card_dvd_of_le hle
    exact Odd.of_dvd_nat hodd hdvd
  obtain ⟨E, hE, hEker, hEmap⟩ := exists_cover_torus hp D Γ' hΓ's hZ' hodd'
  refine ⟨E.map (autFix β).subtype, ?_, ?_, ?_, ?_⟩
  · refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨_, ⟨x, hx, rfl⟩⟩ := a
      obtain ⟨_, ⟨y, hy, rfl⟩⟩ := b
      apply Subtype.ext
      show (x : L) * y = y * x
      have := congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
      exact congrArg Subtype.val this
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hE.2 x hx, map_one]
  · have hinj : Function.Injective (Γ'.domRestrict E) := by
      rw [injective_iff_map_eq_one]
      intro x hx
      have hx' : (x : ↥(autFix β)) ∈ E ⊓ Γ'.ker := ⟨x.2, hx⟩
      rw [hEker, Subgroup.mem_bot] at hx'
      exact Subtype.ext hx'
    have h1 : Nat.card (E.map Γ') = Nat.card E := by
      have h2 : (Γ'.domRestrict E).range = E.map Γ' := MonoidHom.domRestrict_range (K := E) Γ'
      have h3 := (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
      rwa [h2] at h3
    rw [hEmap, hcard] at h1
    rw [Subgroup.card_map_of_injective (autFix β).subtype_injective, ← h1]
  · rw [eq_bot_iff]
    rintro _ ⟨⟨x, hx, rfl⟩, hxZ⟩
    have hxk : x ∈ Γ'.ker := (hker' x).2 (by rw [hker]; exact hxZ)
    have : x ∈ E ⊓ Γ'.ker := ⟨hx, hxk⟩
    rw [hEker, Subgroup.mem_bot] at this
    rw [this]
    rfl
  · rintro _ ⟨x, -, rfl⟩
    exact x.2

end CFSG.HardMathSupport.Solomon.Coordinator
