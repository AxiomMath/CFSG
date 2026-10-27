module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ClR2E0
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ClR3

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm MulAction CFSG.AGLEmbedding CFSG.Quasithin CFSG.Open CFSG.RankThree.PartTwo
  CFSG.QuasithinUnique
open CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure


open scoped Classical in
@[expose] def EightTenNodeColourFourLam4Small : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G), CFSG.Open.IsKGroup ↥X →
    Asc81bHyp X S → IsWeakSBlock X S L → ∀ m : ℕ, 8 < m →
    ↥(barM (L ⊔ S) L) ⧸ Subgroup.center ↥(barM (L ⊔ S) L) ≃* alternatingGroup (Fin m) →
    NaturalSectionLSL S L m →
    ∀ θ : ↥(L ⊔ S) →* Perm (Fin m), NaturalSectionTheta S L m θ →
    (∀ m' : ↥(L ⊔ S), θ m' = 1 → (m' : G) ∈ S) →
    ∀ (A : Subgroup G) (σ : Perm (Fin m)) (c : Fin m → Bool), IsMaxElemAbelian S A →
      BlockData ((A.subgroupOf (L ⊔ S)).map θ) σ c → ∀ x, (cls c x).card = 4 →
      (∃ z : Fin m, ∀ y, z ≠ y →
        swap z y ∉ (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin m)))) →
      (Nat.card {x : Fin m // ∃ y, x < y ∧
          IsIsoPair (((thompsonJ S).subgroupOf (L ⊔ S)).map θ) x y} = 3 ∨
        5 ≤ Nat.card {x : Fin m // ∃ y, x < y ∧
          IsIsoPair (((thompsonJ S).subgroupOf (L ⊔ S)).map θ) x y}) →
      (∀ y : Fin m, (∀ z, y ≠ z →
          swap y z ∉ (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin m)))) ↔
        c y = true) →
      (Finset.univ.filter fun y : Fin m => c y = true).card = 4 →
      (∀ p q : Fin m, IsIsoPair (((thompsonJ S).subgroupOf (L ⊔ S)).map θ) p q →
        ∀ s : ↥(L ⊔ S), (s : G) ∈ S → θ s p = p ∨ θ s p = q) →
      (∀ z y : Fin m, c z = true → c y = true → y ≠ z → y ≠ σ z →
        swap z y * swap (σ z) (σ y) ∉ (S.subgroupOf (L ⊔ S)).map θ) →
      EightTenOutcomes X S L

theorem eightTenNodeColourFourLam4_of (hE0 : E0Statement) (hE0n : E0NotYStatement)
    (hSmall : EightTenNodeColourFourLam4Small) :
    EightTenNodeColourFourLam4 := by
  intro G _ _ X S L hX hA hL m hm e hN θ hNS hθS A σ c hAm hbd x hx hunm hcnt hiff' hT hfix
  classical
  by_cases hK : ∃ z y : Fin m, c z = true ∧ c y = true ∧ y ≠ z ∧ y ≠ σ z ∧
      swap z y * swap (σ z) (σ y) ∈ (S.subgroupOf (L ⊔ S)).map θ
  swap
  · push Not at hK
    exact hSmall G X S L hX hA hL m hm e hN θ hNS hθS A σ c hAm hbd x hx hunm hcnt hiff' hT hfix
      fun z y hz hy hyz hyσz => hK z y hz hy hyz hyσz
  exfalso
  obtain ⟨z, y, hz, hy, hyz, hyσz, hD2⟩ := hK
  obtain ⟨hSL, hA', hLs, hpS, hkerP, hsh⟩ := theta_node_data hX hA hL hm e hNS
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hbd
  have hbd' : BlockData ((A.subgroupOf (L ⊔ S)).map θ) σ c := ⟨h1, h2, h3, h4, h5, h6⟩
  have hAJ : A ≤ thompsonJ S :=
    le_iSup₂ (f := fun (A : Subgroup G) (_ : IsMaxElemAbelian S A) => A) A hAm
  have hEW : (A.subgroupOf (L ⊔ S)).map θ ≤ ((thompsonJ S).subgroupOf (L ⊔ S)).map θ :=
    Subgroup.map_mono (Subgroup.comap_mono hAJ)
  have hWS : ((thompsonJ S).subgroupOf (L ⊔ S)).map θ ≤ (S.subgroupOf (L ⊔ S)).map θ :=
    Subgroup.map_mono (Subgroup.comap_mono
      (iSup_le fun A => iSup_le fun hA => hA.1 : thompsonJ S ≤ S))
  have hσz : c (σ z) = true := by rw [h4]; exact hz
  have hσy : c (σ y) = true := by rw [h4]; exact hy
  have hzσ : z ≠ σ z := Ne.symm (h1 z)
  have hyσ : y ≠ σ y := Ne.symm (h1 y)
  have hzσy : z ≠ σ y := fun h => hyσz (by rw [h, h2])
  have hσzy : σ z ≠ σ y := fun h => hyz (by
    have := congrArg σ h; rw [h2, h2] at this; exact this.symm)
  have hD1 : swap z (σ z) * swap y (σ y) ∈ (A.subgroupOf (L ⊔ S)).map θ :=
    h6 (Subgroup.subset_closure ⟨z, y, hyz, hyσz, by rw [hy, hz], rfl⟩)
  have hD1S := hWS (hEW hD1)
  have hD3S : swap z (σ y) * swap (σ z) y ∈ (S.subgroupOf (L ⊔ S)).map θ := by
    have := ((S.subgroupOf (L ⊔ S)).map θ).mul_mem hD1S hD2
    rwa [dbl_mul hzσ hyz.symm hzσy hyσz.symm hσzy hyσ] at this
  let Λ : Finset (Fin m) := Finset.univ.filter fun y => c y = true
  have hΛmem : ∀ q, q ∈ Λ ↔ c q = true := fun q => by simp [Λ]
  let e0 : Fin 4 → Fin m := ![z, σ z, y, σ y]
  have he0 : Function.Injective e0 := by
    intro i j hij
    have n1 := hzσ.symm; have n2 := hyz; have n3 := hyσz; have n4 := hzσy.symm
    have n5 := hσzy; have n6 := hyσ.symm; have n7 := hyz.symm; have n8 := hyσz.symm
    have n9 := hzσy; have n10 := hσzy.symm; have n11 := hyσ
    fin_cases i <;> fin_cases j <;> simp only [e0] at hij <;>
      first | rfl | (exfalso; simp at hij; exact absurd hij ‹_›)
  have hsub : ∀ i, e0 i ∈ Λ := by
    intro i
    fin_cases i <;> simp [e0, hΛmem, hz, hy, hσz, hσy]
  have himg : Finset.univ.image e0 = Λ :=
    Finset.eq_of_subset_of_card_le
      (fun q hq => by obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hq; exact hsub i)
      (by rw [Finset.card_image_of_injective _ he0]; simp [Λ, hT])
  have hrange : Set.range e0 = (↑Λ : Set (Fin m)) := by
    rw [← himg]; simp [Finset.coe_image]
  exact false_of_klein_theta hE0 hE0n hX hA hL hm e hNS hθS hunm hfix Λ
    (fun q => by rw [hΛmem, hiff' q]) hT e0 he0 hrange hD1S hD2 hD3S (hEW hD1)

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
