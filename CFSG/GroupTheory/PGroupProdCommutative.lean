module

public import CFSG.Quasithin.Background.B682Ambient

public section

namespace CFSG.GroupTheory

open CFSG.Open

variable {X Y A B : Type*} [Group X] [Group Y] [Group A] [Group B]

private theorem isMulCommutative_map_prod_of_isPGroup {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    [Finite A] [Finite B] (hA : CFSG.Open.pRank p (⊤ : Subgroup A) ≤ 1)
    (hB : CFSG.Open.pRank p (⊤ : Subgroup B) ≤ 1)
    (φ : X →* A × B) {R : Subgroup X} (hR : IsPGroup p ↥R) :
    IsMulCommutative ↥(R.map φ) := by
  classical
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  let P₁ : Subgroup A := (R.map φ).map (MonoidHom.fst A B)
  let P₂ : Subgroup B := (R.map φ).map (MonoidHom.snd A B)
  have hP₁p : IsPGroup p ↥P₁ := (hR.map φ).map _
  have hP₂p : IsPGroup p ↥P₂ := (hR.map φ).map _
  have hP₁cyc : IsCyclic ↥P₁ :=
    CFSG.Quasithin.isCyclic_of_pRank_le_one hp2 le_top hP₁p
      ((CFSG.SectionRank.pRank_mono hp.one_lt le_top).trans hA)
  have hP₂cyc : IsCyclic ↥P₂ :=
    CFSG.Quasithin.isCyclic_of_pRank_le_one hp2 le_top hP₂p
      ((CFSG.SectionRank.pRank_mono hp.one_lt le_top).trans hB)
  refine IsMulCommutative.of_comm fun x y => ?_
  apply Subtype.ext
  apply Prod.ext
  · have hx : x.1.1 ∈ P₁ := ⟨x.1, x.2, rfl⟩
    have hy : y.1.1 ∈ P₁ := ⟨y.1, y.2, rfl⟩
    exact congrArg Subtype.val ((IsCyclic.commGroup (α := ↥P₁)).mul_comm
      (⟨x.1.1, hx⟩ : ↥P₁) ⟨y.1.1, hy⟩)
  · have hx : x.1.2 ∈ P₂ := ⟨x.1, x.2, rfl⟩
    have hy : y.1.2 ∈ P₂ := ⟨y.1, y.2, rfl⟩
    exact congrArg Subtype.val ((IsCyclic.commGroup (α := ↥P₂)).mul_comm
      (⟨x.1.2, hx⟩ : ↥P₂) ⟨y.1.2, hy⟩)

private theorem isMulCommutative_of_disjoint_ker_aux (φ : X →* Y) {R : Subgroup X}
    (hdisj : Disjoint R φ.ker) (h : IsMulCommutative ↥(R.map φ)) :
    IsMulCommutative ↥R := by
  let f : ↥R →* ↥(R.map φ) := (φ.domRestrict R).codRestrict (R.map φ) (fun x => ⟨x.1, x.2, rfl⟩)
  have hf : Function.Injective f := by
    intro a b hab
    have hcoe : ((a⁻¹ * b : ↥R) : X) = (a : X)⁻¹ * (b : X) := rfl
    have hmem : ((a⁻¹ * b : ↥R) : X) ∈ φ.ker := by
      rw [MonoidHom.mem_ker, hcoe, map_mul, map_inv]
      have hab' : φ (a : X) = φ (b : X) :=
        congrArg (fun z : ↥(R.map φ) => (z : Y)) hab
      rw [hab', inv_mul_cancel]
    have hmemR : ((a⁻¹ * b : ↥R) : X) ∈ R := (a⁻¹ * b).2
    have h1 : ((a⁻¹ * b : ↥R) : X) = 1 :=
      Subgroup.mem_bot.mp (hdisj.le_bot ⟨hmemR, hmem⟩)
    exact inv_mul_eq_one.mp (Subtype.ext h1)
  refine IsMulCommutative.of_comm fun a b => hf ?_
  calc f (a * b) = f a * f b := map_mul f a b
    _ = f b * f a := h.is_comm.comm (f a) (f b)
    _ = f (b * a) := (map_mul f b a).symm

theorem isMulCommutative_of_isPGroup_of_le_prod {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    [Finite A] [Finite B] (hA : CFSG.Open.pRank p (⊤ : Subgroup A) ≤ 1)
    (hB : CFSG.Open.pRank p (⊤ : Subgroup B) ≤ 1)
    (φ : X →* A × B) {R : Subgroup X} (hR : IsPGroup p ↥R) (hdisj : Disjoint R φ.ker) :
    IsMulCommutative ↥R :=
  isMulCommutative_of_disjoint_ker_aux φ hdisj
    (isMulCommutative_map_prod_of_isPGroup hp hp2 hA hB φ hR)

end CFSG.GroupTheory

end
