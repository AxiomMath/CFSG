module

public import CFSG.GH74.GLS.C3.Layer1.Th2Leaves
public import CFSG.GH74.GLS.C3.Layer1.Th2Theta
public import CFSG.GH74.GLS.C3.Layer1.Th2Sig8

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG.ABGLocalTools

@[expose] def B_thm2_l74 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x y : G) (K T S : Subgroup G) (ρ : Th2Row),
    Th2Std x y K T S → ρ.holds x y K T S →
      ρ.BT x K T S = {B' : Subgroup G | IsSn ρ.level.n (ρ.Tstar x K T S) B'}

@[expose] def B_thm2_conn : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x y : G) (K T S M : Subgroup G) (ρ : Th2Row)
    (B : Subgroup G), Th2M2 x y K T S M ρ B →
      (ρ ≠ .r4b → ρ ≠ .r4c → ∀ A : Subgroup G, IsE ρ.level.r (ρ.Tstar x K T S) A →
        Th2.RConnN ρ.level.r ρ.level.n (ρ.Tstar x K T S) A B) ∧
      (∀ A : Subgroup G, IsE ρ.level.n (ρ.Tstar x K T S) A →
        Th2.RConnN ρ.level.r ρ.level.n (ρ.Tstar x K T S) A B)

namespace Th2

variable {G : Type} [Group G]

theorem le_Tstar {ρ : Th2Row} {x : G} {K T S B : Subgroup G} (hB : B ∈ ρ.BT x K T S) :
    B ≤ ρ.Tstar x K T S :=
  le_iSup₂ (f := fun (B : Subgroup G) (_ : B ∈ ρ.BT x K T S) => B) B hB

theorem elemAbelian_of_le {A H : Subgroup G} (hA : CFSG.IsElementaryAbelian 2 ↥A)
    (hHA : H ≤ A) : CFSG.IsElementaryAbelian 2 ↥H := by
  obtain ⟨hc, hs⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hA
  exact C3.Layer1.Back.isElementaryAbelian_of_forall (fun u hu v hv => hc u (hHA hu) v (hHA hv))
    (fun u hu => hs u (hHA hu))

theorem level_r_le_n (ℓ : Th2Level) : ℓ.r ≤ ℓ.n := by cases ℓ <;> decide

theorem isE_mono_rank {m n : ℕ} {X A : Subgroup G} (h : IsE n X A) (hmn : m ≤ n) : IsE m X A :=
  ⟨h.1, h.2.1, hmn.trans h.2.2⟩

theorem b_thm2_l82_local [Finite G] {x y : G} {K T S M : Subgroup G} {ρ : Th2Row} {B : Subgroup G}
    (h2110 : B_IG_21_10) (h2 : Th2M2 x y K T S M ρ B)
    (h74 : ρ.BT x K T S = {B' : Subgroup G | IsSn ρ.level.n (ρ.Tstar x K T S) B'})
    (hconn : (ρ ≠ .r4b → ρ ≠ .r4c → ∀ A : Subgroup G,
        IsE ρ.level.r (ρ.Tstar x K T S) A →
          RConnN ρ.level.r ρ.level.n (ρ.Tstar x K T S) A B) ∧
      (∀ A : Subgroup G, IsE ρ.level.n (ρ.Tstar x K T S) A →
        RConnN ρ.level.r ρ.level.n (ρ.Tstar x K T S) A B)) :
    (ρ ≠ .r4b → ρ ≠ .r4c → gammaK 2 (ρ.Tstar x K T S) ρ.level.r ≤ M) ∧
      gammaK 2 (ρ.Tstar x K T S) ρ.level.n ≤ M ∧
      (∀ A : Subgroup G, IsE ρ.level.n (ρ.Tstar x K T S) A →
        gammaK 2 A ρ.level.r ≤ M) ∧
      gammaK 2 B ρ.level.r ≤ M := by
  have hBT := h74
  set ℓ := ρ.level with hℓ
  set X := ρ.Tstar x K T S with hX
  have hS : ∀ B' : Subgroup G, IsSn ℓ.n X B' → IsE ℓ.minRank ⊤ B' ∧ ℓ.IsBal B' := by
    intro B' hB'
    have hmem : B' ∈ ρ.BT x K T S := by rw [hBT]; exact hB'
    exact ⟨⟨le_top, (h2.allIsE B' hmem).2.1, (h2.allIsE B' hmem).2.2⟩, h2.allBal B' hmem⟩
  have hBX : B ≤ X := le_Tstar h2.mem
  have hBE : IsE ℓ.minRank ⊤ B := ⟨le_top, h2.isE.2.1, h2.isE.2.2⟩
  have hrn : ℓ.r ≤ ℓ.n := level_r_le_n ℓ
  have hθ : ∀ A : Subgroup G, IsE ℓ.r X A → RConnN ℓ.r ℓ.n X A B → ℓ.theta A = ℓ.theta B :=
    fun A hA hc => theta_eq_of_conn ℓ b_ig_21_8 h2110 hS hA hc
  have hnorm : ∀ H : Subgroup G, ℓ.theta H = ℓ.theta B → normalizer (H : Set G) ≤ M :=
    fun H hH g hg => h2.le_M (norm_le_of_theta_eq ℓ hH hg)
  have hgen : ∀ j : ℕ, (∀ A : Subgroup G, IsE j X A → ℓ.theta A = ℓ.theta B) →
      gammaK 2 X j ≤ M := by
    intro j hgood
    refine iSup_le fun H => iSup₂_le fun hHX hjH g hg => ?_
    obtain ⟨E, hEH, hEel, hErk⟩ := exists_elemAbelian_pRank H
    have hjE : j ≤ pRank 2 ↥E := hErk.ge.trans' hjH
    have hcgH : cj g H = H := cj_eq_of_mem_normalizer hg
    have hE : IsE j X E := ⟨hEH.trans hHX, hEel, hjE⟩
    have hgE : IsE j X (cj g E) :=
      ⟨(Subgroup.map_mono hEH).trans (hcgH.le.trans hHX), isElementaryAbelian_cj g hEel,
        by rw [pRank_cj]; exact hjE⟩
    have h1 := hgood E hE
    have h2' := hgood (cj g E) hgE
    rw [theta_cj, h1] at h2'
    exact h2.le_M (mem_normalizer_of_cj_eq h2')
  refine ⟨fun h4b h4c => ?_, ?_, ?_, ?_⟩
  · exact hgen ℓ.r fun A hA => hθ A hA (hconn.1 h4b h4c A hA)
  · exact hgen ℓ.n fun A hA => hθ A (isE_mono_rank hA hrn) (hconn.2 A hA)
  · intro A hA
    refine iSup_le fun H => iSup₂_le fun hHA hrH g hg => ?_
    have hHel := elemAbelian_of_le hA.2.1 hHA
    have hHE : IsE ℓ.r X H := ⟨hHA.trans hA.1, hHel, hrH⟩
    have hAr : IsE ℓ.r X A := isE_mono_rank hA hrn
    have hstep : ConnStep ℓ.r ℓ.n X H A := by
      refine ⟨hAr, fun a ha b hb => ?_, ?_⟩
      · exact (C3.Layer1.Back.forall_of_isElementaryAbelian hA.2.1).1 a (hHA ha) b hb
      · by_cases hHAeq : H = A
        · exact Or.inl hHAeq
        · refine Or.inr ?_
          have hsup : H ⊔ A = A := sup_eq_right.2 hHA
          rw [hsup]
          have hAC : A ≤ X ⊓ centralizer (A : Set G) := by
            refine le_inf hA.1 fun a ha => ?_
            rw [Subgroup.mem_centralizer_iff]
            intro c hc
            exact (C3.Layer1.Back.forall_of_isElementaryAbelian hA.2.1).1 c hc a ha
          exact hA.2.2.trans (C3.Layer1.Back.pRank_mono' hAC)
    have hconnA := hconn.2 A hA
    have hHB : RConnN ℓ.r ℓ.n X H B := Relation.ReflTransGen.head hstep hconnA
    exact hnorm H (hθ H hHE hHB) hg
  · refine iSup_le fun H => iSup₂_le fun hHB hrH g hg => ?_
    have hHel := elemAbelian_of_le h2.isE.2.1 hHB
    have hHE : IsE ℓ.r B H := ⟨hHB, hHel, hrH⟩
    exact hnorm H (theta_eq_of_le ℓ b_ig_21_8 h2110 hBE h2.bal hHE) hg

end Th2

open Th2 in
theorem b_thm2_l82_of (h2110 : B_IG_21_10) (h74 : B_thm2_l74) (hconn : B_thm2_conn) :
    B_thm2_l82 := by
  intro G _ _ hG x y K T S M ρ B h2
  exact b_thm2_l82_local h2110 h2
    (h74 G hG x y K T S ρ h2.std h2.row)
    (hconn G hG x y K T S M ρ B h2)

end CFSG.GH74.GLS
