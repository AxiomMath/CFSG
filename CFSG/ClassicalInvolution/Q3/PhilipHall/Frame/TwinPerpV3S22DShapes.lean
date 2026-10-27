module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf93Steps
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitUMuRest
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3S22DOpen
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3S22DRoot
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf11Act
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf19AE
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf81Conn
public import CFSG.ClassicalInvolution.Q3.TL3T25
public import CFSG.ClassicalInvolution.Q3.TL4LinkE2

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12
open CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Uniform
open scoped commutatorElement
open CFSG.ClassicalInvolution.Balance.Bootstrap (trivialOnQuot)
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc.ExitU

section Shapes

variable {n : ℕ}

@[expose] def NoRootOn (X : Type) [Group X] (Φ : Set (Subgroup X)) : Prop :=
  ∀ {A B : Subgroup X} {x₀ : X}, A ∈ Φ → B ∈ omegaNbr Φ A → IsUniqueInvolution A x₀ →
    IsUniqueInvolution B x₀ → x₀ ∉ Subgroup.center X → ∀ α : MulAut X, α * α * (α * α) = 1 →
      (∀ L ∈ Φ, ∃ L' ∈ Φ, L.map α.toMonoidHom = L') → (∀ a ∈ A, α a = a) → (∀ b ∈ B, α b = b) →
        α * α ≠ MulAut.conj x₀

@[expose] def ShapeNoRootE4 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Φ : Set (Subgroup X)), Q8Section X Φ →
    (∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L) → (∀ J ∈ Φ, IsPGroup 2 ↥J) →
    (∀ K ∈ Φ, ∀ z : X, IsUniqueInvolution K z → ¬ TightInO2 z) → TwinOnlyNbr Φ → TwinE4 X →
      NoRootOn X Φ

@[expose] def ShapeNoRootAE7 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Φ : Set (Subgroup X)), Q8Section X Φ →
    (∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L) → Nonempty (TC.Thin.AEIdent Φ 7) → NoRootOn X Φ

@[expose] def ShapeNoRootE64 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Φ : Set (Subgroup X)), Q8Section X Φ →
    (∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L) →
      Nonempty (TC.Thin.AEIdentOn Φ 7 AE.e64Sets AE.e64Sub) → NoRootOn X Φ

section Glue

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem not_mem_center_of_twin_pair (hS : Q8Section X Φ) (h2 : ∀ J ∈ Φ, IsPGroup 2 ↥J)
    (htrans : ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L) {A A' : Subgroup X} (hA : A ∈ Φ)
    (hA' : A' ∈ Φ) (hne : A ≠ A') {x₀ : X} (hxA : IsUniqueInvolution A x₀)
    (hxA' : IsUniqueInvolution A' x₀) (hnb : ∀ M ∈ Φ, M ∈ omegaNbr Φ A → M = A')
    (h3 : 3 ∣ Nat.card X) : x₀ ∉ Subgroup.center X := by
  intro hc
  have hcen : ∀ g : X, g * x₀ * g⁻¹ = x₀ := fun g => by
    rw [Subgroup.mem_center_iff.mp hc g, mul_assoc, mul_inv_cancel, mul_one]
  have hall : ∀ M ∈ Φ, M = A ∨ M = A' := by
    intro M hM
    by_cases hMA : M = A
    · exact Or.inl hMA
    · right
      obtain ⟨g, rfl⟩ := htrans A hA M hM
      have hz : IsUniqueInvolution (conjSub g A) x₀ := by
        have := hxA.conj g
        rwa [hcen g] at this
      exact hnb _ hM (Q3CL.T3.twin_mem_omegaNbr hS.hyp hA hM hMA hxA hz)
  have hAn : A' ≤ Subgroup.normalizer (A : Set X) :=
    Sec6Gen.le_normalizer_of_twin hS.hyp hA' hA hne.symm hxA' hxA
  have hsup : IsPGroup 2 ↥(A' ⊔ A) := (h2 A' hA').to_sup_of_normal_right' (h2 A hA) hAn
  have htop : A' ⊔ A = ⊤ := by
    rw [eq_top_iff, ← hS.gen]
    exact iSup₂_le fun M hM => by
      rcases hall M hM with rfl | rfl
      · exact le_sup_right
      · exact le_sup_left
  rw [htop] at hsup
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hsup
  have hX : Nat.card X = 2 ^ k := by rw [← hk]; exact (Subgroup.card_top (G := X)).symm
  rw [hX] at h3
  exact absurd (Nat.prime_three.dvd_of_dvd_pow h3) (by norm_num)

theorem secMuExclOpen_of_shapes (h4 : Thm4RTwinBelow 3 n) (hlt : Nat.card X < n) (hS : Q8Section X Φ)
    (h2 : ∀ J ∈ Φ, IsPGroup 2 ↥J) {A A' : Subgroup X} (hA : A ∈ Φ) (hA' : A' ∈ Φ) (hne : A ≠ A')
    {x₀ : X} (hxA : IsUniqueInvolution A x₀) (hxA' : IsUniqueInvolution A' x₀)
    (hnb : ∀ M ∈ Φ, M ∈ omegaNbr Φ A → M = A') (hnb' : ∀ M ∈ Φ, M ∈ omegaNbr Φ A' → M = A)
    (h3 : 3 ∣ Nat.card X) {α : MulAut X} (hα4 : α * α * (α * α) = 1)
    (hperm : ∀ L ∈ Φ, ∃ L' ∈ Φ, L.map α.toMonoidHom = L') (hfA : ∀ a ∈ A, α a = a)
    (hfA' : ∀ b ∈ A', α b = b) (hαα : α * α = MulAut.conj x₀)
    (hE4 : ShapeNoRootE4) (h7 : ShapeNoRootAE7) (h64 : ShapeNoRootE64) : SecMuExclOpen X Φ := by
  have hconj : ∃ g : X, conjSub g A = A' := by
    by_contra hnot
    obtain ⟨k, hk⟩ := twin_only_two_group h4 hlt hS hA hA' (h2 A hA) (h2 A' hA') hnb hnb' hnot
    rw [hk] at h3
    exact absurd (Nat.prime_three.dvd_of_dvd_pow h3) (by norm_num)
  have htrans := transitive_of_conj_twin h4 hlt hS hA hA' hnb hnb' hconj
  have hnc := not_mem_center_of_twin_pair hS h2 htrans hA hA' hne hxA hxA' hnb h3
  have hnbr : A' ∈ omegaNbr Φ A := Q3CL.T3.twin_mem_omegaNbr hS.hyp hA hA' hne.symm hxA hxA'
  refine ⟨fun hno hE => ?_, fun _ _ hI => ?_, fun _ _ hI => ?_⟩
  · have hno' : ∀ K ∈ Φ, ∀ z : X, IsUniqueInvolution K z → ¬ TightInO2 z := by
      intro K hK z hz hO
      exact hno ⟨K, hK, z, hz, hO⟩
    have hTO : TwinOnlyNbr Φ :=
      twinOnly_of_trans hS.hyp.conjInvariant htrans hA (fun M hM => hnb M hM.1 hM)
    exact hE4 X Φ hS htrans h2 hno' hTO hE hA hnbr hxA hxA' hnc α hα4 hperm hfA hfA' hαα
  · exact h7 X Φ hS htrans hI hA hnbr hxA hxA' hnc α hα4 hperm hfA hfA' hαα
  · exact h64 X Φ hS htrans hI hA hnbr hxA hxA' hnc α hα4 hperm hfA hfA' hαα

end Glue

section V3s

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem v3SecOpenW_of_shapes {n : ℕ} (_hcit : CIT3Below n) (_hP : TL4.TightBelowRPlus 3 n)
    (h4 : Thm4RTwinBelow 3 n) (hE4 : ShapeNoRootE4) (h7 : ShapeNoRootAE7)
    (h64 : ShapeNoRootE64) : V3SecOpenW n := by
  intro Y _ _ R S t K K' K₃ u₁ u₂ u₃ K₄ hin W hW hKD hK'D hK₃D hu₁ hu₂
  have h3 := v3SecOrder_three_dvd_adapted hin hW hKD hK'D hK₃D hu₁ hu₂
  obtain ⟨hStd, hF, hα, h2g, hno⟩ := hin
  have hd := hStd.datum
  have hΩ := hd.hyp
  have hc2 : IsPGroup 2 (Subgroup.zpowers (u₁ * u₂)) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.sq_12
  obtain ⟨hmem, hmem4⟩ := v3_tq_members hStd hF
  have hS := layer_q8Section hStd.perp hd.sq_12
  have hlt := card_layer_lt hStd.perp hd.mul_ne_one
  have hJ := secImg_mem_secFam hmem
  have hJ' := secImg_mem_secFam hmem4
  have hK₄ := hF.1
  have hp3 := v3_perp_tq hStd hd.hK₃ hK₄ (Ne.symm hF.2.2.2.1) hd.hK₃K hd.hK₃K' hF.2.1 hF.2.2.1
  have hp4 := v3_perp_tq hStd hK₄ hd.hK₃ hF.2.2.2.1 hF.2.1 hF.2.2.1 hd.hK₃K hd.hK₃K'
  have hperp3 := kPerp_datum hStd.perp hd.hK₃.1 hd.hzK₃
  have hnb : ∀ M ∈ TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
      M ∈ omegaNbr (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))
        (secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₃) →
      M = secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₄ := by
    intro M hM hn
    obtain ⟨J, hJq, rfl⟩ := exists_of_mem_secFam hM
    exact TwinLayerGen.secNbr_eq_of_perp hΩ hc2 hmem hJq (K' := K₄)
      (fun J₀ hJ₀ hJ₀p => hp3 J₀ hJ₀ (by rw [hperp3] at *; exact hJ₀p)) hn
  have hnb' : ∀ M ∈ TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
      M ∈ omegaNbr (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))
        (secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₄) →
      M = secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₃ := by
    intro M hM hn
    obtain ⟨J, hJq, rfl⟩ := exists_of_mem_secFam hM
    exact TwinLayerGen.secNbr_eq_of_perp hΩ hc2 hmem4 hJq (K' := K₃)
      (fun J₀ hJ₀ hJ₀p => hp4 J₀ hJ₀ hJ₀p) hn
  have h2all : ∀ M ∈ TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
      IsPGroup 2 ↥M := by
    intro M hM
    obtain ⟨J, hJq, rfl⟩ := exists_of_mem_secFam hM
    exact secImg_isPGroup' (h2g J hJq.1)
  obtain ⟨α, zb, hα4, hperm, hfix3, hfix4, hz3, hz4', hαα⟩ := v3_secRoot hStd hF h2g
  exact secMuExclOpen_of_shapes h4 hlt hS h2all hJ hJ' (v3_secImg_ne hStd hF) hz3 hz4' hnb hnb' h3
    hα4 hperm hfix3 hfix4 hαα hE4 h7 h64

end V3s

end Shapes

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
