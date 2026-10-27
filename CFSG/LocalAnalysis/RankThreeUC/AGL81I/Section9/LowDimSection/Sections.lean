module

public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.QuotientGroup.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

@[expose] def SimpleSectionsIn (P : (S : Type) → [Group S] → Prop) (X : Type*) [Group X] :
    Prop :=
  ∀ (Y : Subgroup X) (S : Type) [Group S] [IsSimpleGroup S], ¬ IsMulCommutative S →
    ∀ ψ : ↥Y →* S, Function.Surjective ψ → P S

variable {P : (S : Type) → [Group S] → Prop}

theorem map_eq_bot_or_eq_top_of_normal {Y S : Type*} [Group Y] [Group S] [IsSimpleGroup S]
    {ψ : Y →* S} (hψ : Function.Surjective ψ) {N : Subgroup Y} (hN : N.Normal) :
    N.map ψ = ⊥ ∨ N.map ψ = ⊤ :=
  (hN.map ψ hψ).eq_bot_or_eq_top

theorem map_eq_bot_of_isSolvable {Y S : Type*} [Group Y] [Group S] [IsSimpleGroup S]
    (hS : ¬ IsMulCommutative S) {ψ : Y →* S} (hψ : Function.Surjective ψ) {N : Subgroup Y}
    (hN : N.Normal) (hsol : Group.IsSolvable N) : N.map ψ = ⊥ := by
  refine (map_eq_bot_or_eq_top_of_normal hψ hN).resolve_right fun htop => hS ?_
  have hsurj : Function.Surjective (ψ.comp N.subtype) := by
    intro s
    obtain ⟨n, hn, rfl⟩ : s ∈ N.map ψ := htop ▸ Subgroup.mem_top s
    exact ⟨⟨n, hn⟩, rfl⟩
  have := Group.isSolvable_of_surjective hsurj
  exact IsMulCommutative.of_comm (IsSimpleGroup.comm_iff_isSolvable.mpr this)

theorem SimpleSectionsIn.of_ker_le {X' Y : Type*} [Group X'] [Group Y]
    (h : SimpleSectionsIn P X') (g : Y →* X') {S : Type} [Group S] [IsSimpleGroup S]
    (hS : ¬ IsMulCommutative S) (ψ : Y →* S) (hψ : Function.Surjective ψ)
    (hk : g.ker ≤ ψ.ker) : P S :=
  h g.range S hS ((QuotientGroup.lift g.ker ψ hk).comp
      (QuotientGroup.quotientKerEquivRange g).symm.toMonoidHom)
    ((QuotientGroup.lift_surjective_of_surjective g.ker ψ hψ hk).comp
      (QuotientGroup.quotientKerEquivRange g).symm.surjective)

theorem SimpleSectionsIn.of_injective {X X' : Type*} [Group X] [Group X'] (f : X →* X')
    (hf : Function.Injective f) (h : SimpleSectionsIn P X') : SimpleSectionsIn P X := by
  intro Y S _ _ hS ψ hψ
  refine h.of_ker_le (f.comp Y.subtype) hS ψ hψ ?_
  intro x hx
  have hx' : f x = 1 := hx
  have : x = 1 := Subtype.ext (hf (by simpa using hx'))
  simp [this]

theorem SimpleSectionsIn.of_isSolvable_ker {X X' : Type*} [Group X] [Group X'] (f : X →* X')
    (hker : Group.IsSolvable f.ker) (h : SimpleSectionsIn P X') : SimpleSectionsIn P X := by
  intro Y S _ _ hS ψ hψ
  refine h.of_ker_le (f.comp Y.subtype) hS ψ hψ ?_
  have hinj : Function.Injective (fun x : (f.comp Y.subtype).ker =>
      (⟨x.1.1, x.2⟩ : f.ker)) := fun x y hxy => by
    ext; simpa using congrArg Subtype.val hxy
  have := Group.isSolvable_of_isSolvable_injective (f := ⟨⟨fun x : (f.comp Y.subtype).ker =>
      (⟨x.1.1, x.2⟩ : f.ker), rfl⟩, fun _ _ => rfl⟩) hinj
  exact (Subgroup.map_eq_bot_iff _).mp (map_eq_bot_of_isSolvable hS hψ inferInstance this)

theorem SimpleSectionsIn.prod {A B : Type*} [Group A] [Group B] (hA : SimpleSectionsIn P A)
    (hB : SimpleSectionsIn P B) : SimpleSectionsIn P (A × B) := by
  intro W S _ _ hS ψ hψ
  set g := (MonoidHom.snd A B).comp W.subtype
  rcases map_eq_bot_or_eq_top_of_normal hψ (g.normal_ker) with hbot | htop
  · exact hB.of_ker_le g hS ψ hψ ((Subgroup.map_eq_bot_iff _).mp hbot)
  have hsurj : Function.Surjective (ψ.comp g.ker.subtype) := by
    intro s
    obtain ⟨n, hn, rfl⟩ : s ∈ g.ker.map ψ := htop ▸ Subgroup.mem_top s
    exact ⟨⟨n, hn⟩, rfl⟩
  refine hA.of_ker_le ((MonoidHom.fst A B).comp (W.subtype.comp g.ker.subtype)) hS _ hsurj ?_
  intro x hx
  have h2 : (x.1.1 : A × B).2 = 1 := x.2
  have h1 : (x.1.1 : A × B).1 = 1 := hx
  have : x = 1 := Subtype.ext <| Subtype.ext <| Prod.ext h1 h2
  simp [this]

theorem SimpleSectionsIn.of_isMulCommutative {X : Type*} [Group X] [IsMulCommutative X] :
    SimpleSectionsIn P X := by
  intro Y S _ _ hS ψ hψ
  refine absurd ⟨⟨fun a b => ?_⟩⟩ hS
  obtain ⟨x, rfl⟩ := hψ a
  obtain ⟨y, rfl⟩ := hψ b
  rw [← map_mul, ← map_mul]
  congr 1
  ext
  exact mul_comm' (x : X) y

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
