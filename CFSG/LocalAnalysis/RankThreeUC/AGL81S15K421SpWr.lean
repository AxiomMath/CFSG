module

public import Mathlib.GroupTheory.RegularWreathProduct

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K421SpWrProof

theorem isCyclic_center_regularWreathProduct_aux1 {D Q : Type} [CommGroup D] [Group Q] (d : D) :
    (⟨fun _ => d, 1⟩ : D ≀ᵣ Q) ∈ Subgroup.center (D ≀ᵣ Q) := by
  rw [Subgroup.mem_center_iff]
  intro g
  ext x <;> simp [mul_comm]

theorem isCyclic_center_regularWreathProduct_aux2 {D Q : Type} [CommGroup D] [Group Q]
    (z : D ≀ᵣ Q) (hz : z ∈ Subgroup.center (D ≀ᵣ Q)) (y : Q) : z.left y = z.left 1 := by
  have h := Subgroup.mem_center_iff.mp hz (⟨1, y⁻¹⟩ : D ≀ᵣ Q)
  have hl := congrFun (congrArg RegularWreathProduct.left h) 1
  simpa using hl

theorem isCyclic_center_regularWreathProduct_aux3 {D Q : Type} [CommGroup D] [Group Q]
    [Nontrivial D] (z : D ≀ᵣ Q) (hz : z ∈ Subgroup.center (D ≀ᵣ Q)) : z.right = 1 := by
  classical
  obtain ⟨d₀, hd₀⟩ := exists_ne (1 : D)
  have h := Subgroup.mem_center_iff.mp hz (⟨Pi.mulSingle (1 : Q) d₀, 1⟩ : D ≀ᵣ Q)
  have h1 : (Pi.mulSingle (1 : Q) d₀ : Q → D) 1 * z.left (1⁻¹ * 1) =
      z.left 1 * (Pi.mulSingle (1 : Q) d₀ : Q → D) (z.right⁻¹ * 1) :=
    congrFun (congrArg RegularWreathProduct.left h) 1
  simp only [inv_one, mul_one, one_mul, Pi.mulSingle_eq_same] at h1
  have h1' : z.left 1 * d₀ = z.left 1 * (Pi.mulSingle (1 : Q) d₀ : Q → D) z.right⁻¹ := by
    rw [mul_comm (z.left 1) d₀]
    exact h1
  have h2 : d₀ = (Pi.mulSingle (1 : Q) d₀ : Q → D) z.right⁻¹ := mul_left_cancel h1'
  by_contra hne
  have h3 : z.right⁻¹ ≠ 1 := inv_ne_one.mpr hne
  have h4 : (Pi.mulSingle (1 : Q) d₀ : Q → D) z.right⁻¹ = 1 :=
    Pi.mulSingle_eq_of_ne (M := fun _ : Q => D) h3 d₀
  rw [h4] at h2
  exact hd₀ h2

theorem isCyclic_center_regularWreathProduct_aux4 {D Q : Type} [CommGroup D] [Group Q]
    [Nontrivial D] (z : D ≀ᵣ Q) (hz : z ∈ Subgroup.center (D ≀ᵣ Q)) :
    z = ⟨fun _ => z.left 1, 1⟩ :=
  RegularWreathProduct.ext (funext fun y => isCyclic_center_regularWreathProduct_aux2 z hz y)
    (isCyclic_center_regularWreathProduct_aux3 z hz)

theorem isCyclic_center_regularWreathProduct {D Q : Type} [CommGroup D] [IsCyclic D] [Nontrivial D]
    [Group Q] [Nontrivial Q] : IsCyclic ↥(Subgroup.center (D ≀ᵣ Q)) := by
  let f : D →* Subgroup.center (D ≀ᵣ Q) :=
    { toFun := fun d => ⟨⟨fun _ => d, 1⟩, isCyclic_center_regularWreathProduct_aux1 d⟩
      map_one' := Subtype.ext (by ext <;> simp)
      map_mul' := fun a b => Subtype.ext (by ext <;> simp [mul_comm]) }
  apply isCyclic_of_surjective f
  rintro ⟨z, hz⟩
  exact ⟨z.left 1, Subtype.ext (isCyclic_center_regularWreathProduct_aux4 z hz).symm⟩

theorem isCyclic_center_wreath_zmod {k : ℕ} (hk : 1 ≤ k) :
    IsCyclic ↥(Subgroup.center (Multiplicative (ZMod (3 ^ k)) ≀ᵣ Multiplicative (ZMod 3))) := by
  haveI : Fact (1 < 3 ^ k) := ⟨one_lt_pow₀ (by norm_num) (by omega)⟩
  haveI : Fact (1 < 3) := ⟨by norm_num⟩
  exact isCyclic_center_regularWreathProduct

theorem isCyclic_center_of_mulEquiv {P W : Type} [Group P] [Group W] (e : P ≃* W)
    (h : IsCyclic ↥(Subgroup.center W)) : IsCyclic ↥(Subgroup.center P) :=
  (MulEquiv.isCyclic (Subgroup.centerCongr e)).mpr h

end K421SpWrProof

end CFSG.LocalAnalysis.RankThreeUC.S15
