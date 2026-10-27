module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1515D
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15A10GenJ1
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15A10GenJ2

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace A10GenJ2

theorem oddHull_map {X Z : Type} [Group X] [Group Z] (f : X →* Z) (hf : Function.Injective f)
    (L : Subgroup X) : oddHull (L.map f) = (oddHull L).map f := by
  unfold oddHull
  rw [MonoidHom.map_closure]
  congr 1
  ext z
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, hodd⟩
    exact ⟨y, ⟨hy, by rwa [orderOf_injective f hf] at hodd⟩, rfl⟩
  · rintro ⟨y, ⟨hy, hodd⟩, rfl⟩
    exact ⟨⟨y, hy, rfl⟩, by rwa [orderOf_injective f hf]⟩

end A10GenJ2

theorem KA10Gen_holds : KA10Gen := by
  intro Y _ _ Ls P₁ P₂ ⟨e⟩ h₁ h₂ ⟨e₁⟩ h₂'
  let ι : ↥Ls →* Y := Ls.subtype
  let f : ↥Ls →* alternatingGroup (Fin 10) := e.toMonoidHom
  have hι : Function.Injective ι := Subtype.val_injective
  have hf : Function.Injective f := e.injective
  have hP₁ : (P₁.subgroupOf Ls).map ι = P₁ := Subgroup.map_subgroupOf_eq_of_le h₁
  have hP₂ : (P₂.subgroupOf Ls).map ι = P₂ := Subgroup.map_subgroupOf_eq_of_le h₂
  have key : oddHull (P₁.subgroupOf Ls) ⊔ oddHull (P₂.subgroupOf Ls) = ⊤ := by
    have e₁' : ↥((P₁.subgroupOf Ls).map f) ≃* Equiv.Perm (Fin 8) :=
      ((Subgroup.equivMapOfInjective (P₁.subgroupOf Ls) f hf).symm.trans
        (Subgroup.subgroupOfEquivOfLe h₁)).trans e₁
    obtain ⟨a, b, hab, hstab⟩ := alt_ten_exists_stabilizer_le _ ⟨e₁'⟩
    have hshape := A10GenJ2.HasShape.of_mulEquiv (Subgroup.subgroupOfEquivOfLe h₂).symm
      (A10GenJ2.hasShape_of_isTwoFourSFive P₂ h₂')
    have htrans := A10GenJ2.core ((alternatingGroup (Fin 10)).subtype.comp f)
      (Subtype.val_injective.comp hf) (P₂.subgroupOf Ls) hshape
    have htop := alt_ten_sup_eq_top a b hab (oddHull ((P₁.subgroupOf Ls).map f))
      (oddHull ((P₂.subgroupOf Ls).map f))
      (fun σ ha hb => alt_ten_stabilizer_le_closure_odd a b _ hstab σ ha hb)
      (fun i j => by
        obtain ⟨σ, hσ, hσij⟩ := htrans i j
        refine ⟨f σ, ?_, hσij⟩
        rw [A10GenJ2.oddHull_map f hf]
        exact Subgroup.mem_map_of_mem f hσ)
    rw [A10GenJ2.oddHull_map f hf, A10GenJ2.oddHull_map f hf, ← Subgroup.map_sup] at htop
    refine eq_top_iff.2 fun g _ => ?_
    have : f g ∈ (oddHull (P₁.subgroupOf Ls) ⊔ oddHull (P₂.subgroupOf Ls)).map f := by
      rw [htop]; trivial
    obtain ⟨s, hs, hsg⟩ := this
    exact hf hsg ▸ hs
  rw [← hP₁, ← hP₂, A10GenJ2.oddHull_map ι hι, A10GenJ2.oddHull_map ι hι, ← Subgroup.map_sup, key,
    ← MonoidHom.range_eq_map]
  exact Subgroup.range_subtype Ls

end CFSG.LocalAnalysis.RankThreeUC.S15
