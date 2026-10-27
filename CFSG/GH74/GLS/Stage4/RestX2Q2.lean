module

public import CFSG.GH74.GLS.Stage4.RestX2B
public import CFSG.GH74.GLS.Stage4.RestChain3
public import CFSG.GH74.GLS.Stage4.T6Final
public import CFSG.GH74.GLS.Stage4.RestX2Q1
public import CFSG.GH74.GLS.Stage4.RestMirror
public import CFSG.GH74.GLS.Stage4.RestDodecB
public import CFSG.GH74.GLS.Stage4.RestL94
public import CFSG.GH74.GLS.Stage4.RestL92D
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Semidihedral.InvolutionFusion
public import CFSG.CharacterTheory.Semidihedral.Local.LocalNormalizerQuotients
public import CFSG.Dihedral.GorensteinWalter.GLSemilinearDescent
public import CFSG.GH74.GLS.IVK.Defs2
public import CFSG.GH74.GLS.IVK.L2.Hilbert90Core
public import CFSG.GH74.GLS.IVK.L2.Lemma19c
public import CFSG.GH74.GLS.IVK.Lifted.Outer14
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Prop41
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Statements
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.Closed2
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Defs
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Ext
public import CFSG.GH74.GLS.Stage4.RestCases
public import CFSG.GH74.GLS.Stage4.T2LeafC
public import CFSG.GH74.GLS.Stage4.T2OddAut
public import CFSG.GH74.GLS.Stage4.T2P53a
public import CFSG.GroupTheory.ABGLocalTools.PStabilityDefs
public import CFSG.GroupTheory.QuasiDihedralFusion.Basic
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.PrimeComplementQuotientComponents
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.ClassFunction
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremC
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.ZJTheorem
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ConjugatedInvertedSubgroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GW1965RemarkDGroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_19
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.CoprimeActionNontrivialTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseComponentData
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character
public import CFSG.Walter.J1.Inv

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex
  CFSG.GH74.BNPair CFSG.Assembly.LowTwoRank DodecA
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] {D : Ch6Notation G}

structure AllX2Hyp (D : Ch6Notation G) : Prop where
  basics : Ch6Basics D
  K_inter : D.K₁ ⊓ D.K₂ ≤ Subgroup.zpowers D.z
  P_pGroup : IsPGroup D.p ↥D.P
  P_normH : ∀ h ∈ D.H, ∀ x ∈ D.P, h * x * h⁻¹ ∈ D.P
  X₂_central : ∀ x ∈ D.X₂, ∀ y ∈ D.P, x * y = y * x
  X₁_le : D.X₁ ≤ D.P
  inv_R₂ : ∀ y ∈ D.P, D.z * y * D.z⁻¹ = y⁻¹ → y ∈ D.R₂
  R₂_comm : ∀ x ∈ D.R₂, ∀ y ∈ D.R₂, ⁅x, y⁆ ∈ D.X₂
  u_inv₁ : ∀ x ∈ D.X₁, D.u * x * D.u⁻¹ = x⁻¹
  u_inv₁' : ∀ x ∈ D.X₁', D.u * x * D.u⁻¹ = x⁻¹
  u_inv₂ : ∀ x ∈ D.X₂, D.u * x * D.u⁻¹ = x⁻¹
  u_inv₂' : ∀ x ∈ D.X₂', D.u * x * D.u⁻¹ = x⁻¹
  a_conj₁ : D.a * D.z * D.a⁻¹ = D.z * D.u
  a_conj₂ : D.a ^ 2 * D.z * (D.a ^ 2)⁻¹ = D.u

theorem Ch6Basics.z_comm_X₁ (hb : Ch6Basics D) : ∀ x ∈ D.X₁, D.z * x * D.z⁻¹ = x := by
  intro x hx
  have hxK : x ∈ D.K₁ := by rw [hb.K₁_eq]; exact Subgroup.mem_sup_left hx
  have := hb.K_comm x hxK D.z hb.z_mem_K₂
  rw [← this]; group

theorem Ch6Basics.z_comm_X₁' (hb : Ch6Basics D) : ∀ x ∈ D.X₁', D.z * x * D.z⁻¹ = x := by
  intro x hx
  have hxK : x ∈ D.K₁ := by rw [hb.K₁_eq]; exact Subgroup.mem_sup_right hx
  have := hb.K_comm x hxK D.z hb.z_mem_K₂
  rw [← this]; group

theorem Ch6Basics.z_comm_X₂ (hb : Ch6Basics D) : ∀ x ∈ D.X₂, D.z * x * D.z⁻¹ = x := by
  intro x hx
  have hxK : x ∈ D.K₂ := by rw [hb.K₂_eq]; exact Subgroup.mem_sup_left hx
  have := hb.K_comm D.z hb.z_mem_K₁ x hxK
  rw [this]; group

theorem Ch6Basics.z_comm_X₂' (hb : Ch6Basics D) : ∀ x ∈ D.X₂', D.z * x * D.z⁻¹ = x := by
  intro x hx
  have hxK : x ∈ D.K₂ := by rw [hb.K₂_eq]; exact Subgroup.mem_sup_right hx
  have := hb.K_comm D.z hb.z_mem_K₁ x hxK
  rw [this]; group

theorem zu_inv_of {A : Subgroup G} (D : Ch6Notation G) (hzA : ∀ x ∈ A, D.z * x * D.z⁻¹ = x)
    (huA : ∀ x ∈ A, D.u * x * D.u⁻¹ = x⁻¹) : ∀ x ∈ A, (D.z * D.u) * x * (D.z * D.u)⁻¹ = x⁻¹ := by
  intro x hx
  calc (D.z * D.u) * x * (D.z * D.u)⁻¹ = D.z * (D.u * x * D.u⁻¹) * D.z⁻¹ := by group
    _ = D.z * x⁻¹ * D.z⁻¹ := by rw [huA x hx]
    _ = (D.z * x * D.z⁻¹)⁻¹ := by group
    _ = x⁻¹ := by rw [hzA x hx]

theorem Ch6Notation.mirror_u : D.mirror.u = D.a * D.z * D.a⁻¹ := by
  simp [Ch6Notation.u, Ch6Notation.mirror]

theorem AllX2Hyp.mirror (hh : AllX2Hyp D) : AllX2Hyp D.mirror := by
  have hb := hh.basics
  have hzz := hb.z_mul_z
  have hmu : D.mirror.u = D.z * D.u := by rw [Ch6Notation.mirror_u, hh.a_conj₁]
  have hz : D.mirror.z = D.z := rfl
  refine
    { basics := hb.mirror
      K_inter := hh.K_inter
      P_pGroup := hh.P_pGroup
      P_normH := hh.P_normH
      X₂_central := hh.X₂_central
      X₁_le := hh.X₁_le
      inv_R₂ := hh.inv_R₂
      R₂_comm := hh.R₂_comm
      u_inv₁ := ?_
      u_inv₁' := ?_
      u_inv₂ := ?_
      u_inv₂' := ?_
      a_conj₁ := ?_
      a_conj₂ := ?_ }
  · intro x hx; rw [hmu]; exact zu_inv_of D hb.z_comm_X₁ hh.u_inv₁ x hx
  · intro x hx; rw [hmu]; exact zu_inv_of D hb.z_comm_X₁' hh.u_inv₁' x hx
  · intro x hx; rw [hmu]; exact zu_inv_of D hb.z_comm_X₂ hh.u_inv₂ x hx
  · intro x hx; rw [hmu]; exact zu_inv_of D hb.z_comm_X₂' hh.u_inv₂' x hx
  ·
    show D.a⁻¹ * D.z * (D.a⁻¹)⁻¹ = D.z * D.mirror.u
    rw [hmu]
    have : D.z * (D.z * D.u) = D.u := by
      calc D.z * (D.z * D.u) = (D.z * D.z) * D.u := by group
        _ = D.u := by rw [hzz, one_mul]
    rw [this]
    simp [Ch6Notation.u]
  ·
    show (D.a⁻¹) ^ 2 * D.z * ((D.a⁻¹) ^ 2)⁻¹ = D.mirror.u
    rw [hmu]
    have hc : D.a ^ 3 * D.z = D.z * D.a ^ 3 := hb.H_comm _ hb.a_cube _ hb.z_mem_H
    have e : (D.a⁻¹) ^ 2 * D.z * ((D.a⁻¹) ^ 2)⁻¹ = D.a * ((D.a ^ 3)⁻¹ * D.z * D.a ^ 3) * D.a⁻¹ := by group
    rw [e]
    have e2 : (D.a ^ 3)⁻¹ * D.z * D.a ^ 3 = D.z := by
      rw [mul_assoc, ← hc]; group
    rw [e2, hh.a_conj₁]

variable {D : Ch6Notation G}

theorem z_inv_conjBy_a {A : Subgroup G} (hh : AllX2Hyp D) (hzA : ∀ x ∈ A, D.z * x * D.z⁻¹ = x)
    (huA : ∀ x ∈ A, D.u * x * D.u⁻¹ = x⁻¹) :
    (∀ x ∈ conjBy D.a A, D.z * x * D.z⁻¹ = x⁻¹) ∧
      (∀ x ∈ conjBy (D.a ^ 2) A, D.z * x * D.z⁻¹ = x⁻¹) := by
  have hzu := zu_inv_of D hzA huA
  constructor
  · intro x hx
    rw [mem_conjBy_iff] at hx
    have h1 := hzu _ hx
    rw [← hh.a_conj₁] at h1
    have e : D.z * x * D.z⁻¹ = D.a⁻¹ * ((D.a * D.z * D.a⁻¹) * (D.a * x * D.a⁻¹) * (D.a * D.z * D.a⁻¹)⁻¹) * D.a := by group
    rw [e, h1]; group
  · intro x hx
    rw [mem_conjBy_iff] at hx
    have h1 := huA _ hx
    rw [← hh.a_conj₂] at h1
    have e : D.z * x * D.z⁻¹ = (D.a ^ 2)⁻¹ * ((D.a ^ 2 * D.z * (D.a ^ 2)⁻¹) * (D.a ^ 2 * x * (D.a ^ 2)⁻¹) * (D.a ^ 2 * D.z * (D.a ^ 2)⁻¹)⁻¹) * D.a ^ 2 := by group
    rw [e, h1]; group

theorem conjBy_conjBy_a (a : G) (B : Subgroup G) : conjBy a (conjBy a B) = conjBy (a ^ 2) B := by
  rw [← BNPair.conjBy_mul, ← pow_two]

theorem not_mem_pGroup_of_sq {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {P : Subgroup G} (hP : IsPGroup p ↥P)
    {x : G} (hx : x ∈ P) (hx1 : x ≠ 1) (hsq : x * x = 1) : False := by
  obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
  have hk' : x ^ (p ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have h2 : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two]; exact hsq) hx1
  have hdvd : 2 ∣ p ^ k := h2 ▸ orderOf_dvd_of_pow_eq_one hk'
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 (Nat.prime_two.dvd_of_dvd_pow hdvd)
  exact hp2 this.symm

theorem not_both_a2 (hh : AllX2Hyp D) (c4 : conjBy (D.a ^ 2) D.X₂ ≤ D.P)
    (c5 : conjBy (D.a ^ 2) D.X₂' ≤ D.P) : False := by
  have hb := hh.basics
  have hK₂P : conjBy (D.a ^ 2) D.K₂ ≤ D.P := by
    rw [hb.K₂_eq, conjBy_sup']
    exact sup_le c4 c5
  have hzK : (D.a ^ 2)⁻¹ * D.z * D.a ^ 2 ∈ conjBy (D.a ^ 2) D.K₂ := by
    rw [mem_conjBy_iff]
    have e : D.a ^ 2 * ((D.a ^ 2)⁻¹ * D.z * D.a ^ 2) * (D.a ^ 2)⁻¹ = D.z := by group
    rw [e]; exact hb.z_mem_K₂
  refine not_mem_pGroup_of_sq hb.prime hb.p_ne_two hh.P_pGroup (hK₂P hzK) ?_ ?_
  · intro h1
    apply hb.z_ne_one
    have : D.z = D.a ^ 2 * ((D.a ^ 2)⁻¹ * D.z * D.a ^ 2) * (D.a ^ 2)⁻¹ := by group
    rw [this, h1]; group
  · have e : (D.a ^ 2)⁻¹ * D.z * D.a ^ 2 * ((D.a ^ 2)⁻¹ * D.z * D.a ^ 2) =
        (D.a ^ 2)⁻¹ * (D.z * D.z) * D.a ^ 2 := by group
    rw [e, hb.z_mul_z]; group

theorem allX2_cont (hh : AllX2Hyp D) (c1 : conjBy (D.a ^ 2) D.X₁ ≤ D.P) (c2 : conjBy D.a D.X₁' ≤ D.P)
    (c4 : conjBy (D.a ^ 2) D.X₂ ≤ D.P) :
    conjBy D.a D.X₂ ≤ centralizer (D.X₁ : Set G) ∧ conjBy (D.a ^ 2) D.X₂' ≤ centralizer (D.X₁ : Set G) ∧
      conjBy D.a D.X₁' ≤ centralizer (D.X₁ : Set G) ∧ conjBy (D.a ^ 2) D.X₁' ≤ centralizer (D.X₁ : Set G) := by
  have hb := hh.basics
  have hX₁K : D.X₁ ≤ D.K₁ := by rw [hb.K₁_eq]; exact le_sup_left
  have hw₂comm : ∀ y ∈ D.X₁, D.w₂ * y = y * D.w₂ := fun y hy =>
    (hb.K_comm y (hX₁K hy) D.w₂ hb.w₂_mem).symm
  have hA₂ : conjBy D.a D.X₂ ≤ centralizer (D.X₁ : Set G) := by
    intro x' hx'
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hx : (D.a ^ 2)⁻¹ * x' * D.a ^ 2 ∈ D.X₂ := by
      rw [mem_conjBy_iff] at hx'
      have := hb.H_norm_X₂ ((D.a ^ 3)⁻¹) (D.H.inv_mem hb.a_cube) _ hx'
      have e : (D.a ^ 3)⁻¹ * (D.a * x' * D.a⁻¹) * ((D.a ^ 3)⁻¹)⁻¹ = (D.a ^ 2)⁻¹ * x' * D.a ^ 2 := by group
      rwa [e] at this
    have h := centralizes_of_conjBy_le c1 hh.X₂_central _ hx y hy
    have e : D.a ^ 2 * ((D.a ^ 2)⁻¹ * x' * D.a ^ 2) * (D.a ^ 2)⁻¹ = x' := by group
    rw [e] at h
    exact h.symm
  have hA₃ : conjBy (D.a ^ 2) D.X₂' ≤ centralizer (D.X₁ : Set G) := by
    have h1 := conjBy_inv_le_centralizer hw₂comm hA₂
    have e : conjBy D.w₂⁻¹ (conjBy D.a D.X₂) = conjBy (D.a ^ 2) D.X₂' := by
      have := conjBy_w_conjBy_a_pow hb.H_norm_X₂ hb.w₂_normH hb.a_normH hb.a_cube hb.w₂_a 1
      rw [pow_one] at this
      rw [this, conjBy_w₂_X₂ hb]
    rwa [e] at h1
  have hcomm : ∀ x ∈ conjBy D.a D.X₁', ∀ y ∈ conjBy (D.a ^ 2) D.X₁, x * y = y * x := by
    intro x hx y hy
    have hxP := c2 hx
    have hyP := c1 hy
    have hzx : D.z * x * D.z⁻¹ = x⁻¹ :=
      (z_inv_conjBy_a hh hb.z_comm_X₁' hh.u_inv₁').1 x hx
    have hzy : D.z * y * D.z⁻¹ = y⁻¹ :=
      (z_inv_conjBy_a hh hb.z_comm_X₁ hh.u_inv₁).2 y hy
    have hxR := hh.inv_R₂ x hxP hzx
    have hyR := hh.inv_R₂ y hyP hzy
    have hc2 : ⁅x, y⁆ ∈ D.X₂ := hh.R₂_comm x hxR y hyR
    have hr₂N : D.r₂⁻¹ ∈ normalizer (D.H : Set G) :=
      Subgroup.inv_mem _ (mul_mem (mul_mem (Subgroup.inv_mem _ hb.a_normH) hb.w₂_normH) hb.a_normH)
    have hPH : HInv D.H D.P := hh.P_normH
    have hZH : HInv D.H (conjBy D.r₂⁻¹ D.P) := hPH.map_conjBy hr₂N
    have h3 := (hb.act₂.2.2 3 (by norm_num) (by norm_num)).1
    rw [show (6 : ℤ) - 3 = 3 by norm_num] at h3
    have h1' := (hb.act₂.2.2 1 (by norm_num) (by norm_num)).1
    rw [show (6 : ℤ) - 1 = 5 by norm_num] at h1'
    have hY₃Z : D.root 3 ≤ conjBy D.r₂⁻¹ D.P := by
      rw [← h3]
      exact Subgroup.map_mono (show D.root 3 ≤ D.P by rw [root_p3]; exact c2)
    have hY₅Z : D.root 5 ≤ conjBy D.r₂⁻¹ D.P := by
      rw [← h1']
      exact Subgroup.map_mono (show D.root 1 ≤ D.P by rw [root_p1]; exact hh.X₁_le)
    have hxZ : x ∈ conjBy D.r₂⁻¹ D.P := hY₃Z (by rw [root_p3]; exact hx)
    have hyZ : y ∈ conjBy D.r₂⁻¹ D.P := hY₅Z (by rw [root_p5]; exact hy)
    have hcZ : ⁅x, y⁆ ∈ conjBy D.r₂⁻¹ D.P := by
      rw [commutatorElement_def]
      exact (conjBy D.r₂⁻¹ D.P).mul_mem ((conjBy D.r₂⁻¹ D.P).mul_mem
        ((conjBy D.r₂⁻¹ D.P).mul_mem hxZ hyZ) ((conjBy D.r₂⁻¹ D.P).inv_mem hxZ))
        ((conjBy D.r₂⁻¹ D.P).inv_mem hyZ)
    have hirr := (hb.irr_X₂).inf hb.H_norm_X₂ hZH
    have hbot : conjBy D.r₂⁻¹ D.P ⊓ D.X₂ = ⊥ := by
      rcases hirr with h0 | hX
      · exact h0
      · exfalso
        have hX₂Z : D.X₂ ≤ conjBy D.r₂⁻¹ D.P := fun t ht => (inf_eq_right.1 hX) ht
        have h4 := (hb.act₂.2.2 4 (by norm_num) (by norm_num)).1
        rw [show (6 : ℤ) - 4 = 2 by norm_num, root_p4, root_p2] at h4
        have hroot2 : conjBy (D.a ^ 2) D.X₂' ≤ D.P := by
          intro t ht
          rw [← h4, mem_conjBy_iff] at ht
          have h5 := hX₂Z ht
          rw [mem_conjBy_iff] at h5
          have hsq : D.r₂ * D.r₂ ∈ D.H := hb.sq₂
          have h6 := hh.P_normH _ hsq _ h5
          have e : D.r₂ * D.r₂ * (D.r₂⁻¹ * (D.r₂⁻¹ * t * D.r₂⁻¹⁻¹) * D.r₂⁻¹⁻¹) * (D.r₂ * D.r₂)⁻¹ = t := by
            group
          rwa [e] at h6
        exact not_both_a2 hh c4 hroot2
    have h1 : ⁅x, y⁆ = 1 := by
      have : ⁅x, y⁆ ∈ conjBy D.r₂⁻¹ D.P ⊓ D.X₂ := ⟨hcZ, hc2⟩
      rw [hbot] at this
      exact Subgroup.mem_bot.1 this
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  have hA₅ : conjBy (D.a ^ 2) D.X₁' ≤ centralizer (D.X₁ : Set G) := by
    intro x' hx'
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hcc := comm_conjBy₂ hcomm D.a
    have hx'' : x' ∈ conjBy D.a (conjBy D.a D.X₁') := by rw [conjBy_conjBy_a]; exact hx'
    have e3 : conjBy D.a (conjBy (D.a ^ 2) D.X₁) = D.X₁ := by
      have := conjBy_pow_add D.a 1 2 D.X₁
      rw [pow_one] at this
      rw [this]
      exact conjBy_eq_of_mem hb.H_norm_X₁ hb.a_cube
    have hy'' : y ∈ conjBy D.a (conjBy (D.a ^ 2) D.X₁) := by rw [e3]; exact hy
    exact (hcc x' hx'' y hy'').symm
  have hA₄ : conjBy D.a D.X₁' ≤ centralizer (D.X₁ : Set G) := by
    have h1 := conjBy_inv_le_centralizer hw₂comm hA₅
    have e : conjBy D.w₂⁻¹ (conjBy (D.a ^ 2) D.X₁') = conjBy D.a D.X₁' := by
      have := conjBy_w_conjBy_a_pow hb.H_norm_X₁' hb.w₂_normH hb.a_normH hb.a_cube hb.w₂_a 2
      rw [this, conjBy_w₂_X₁' hb, conjBy_pow_mod hb.H_norm_X₁' hb.a_normH hb.a_cube (2 * 2)]
      norm_num
    rwa [e] at h1
  exact ⟨hA₂, hA₃, hA₄, hA₅⟩

end CFSG.GH74.GLS.Stage4.Rest
