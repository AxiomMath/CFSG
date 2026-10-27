module

public import CFSG.CGT.Foote82.T66.CitedBAS
public import CFSG.CGT.Foote82.T66.CertProofsOmegaSixNormalizer
public import CFSG.CGT.Foote82.T66.CertProofsOmegaSixA6Centralizer
public import Certificates.Certificate919005
import CFSG.CGT.Foote82.T66.FaithfulBasic
import CFSG.CGT.Foote82.T66.MC2Arith
import CFSG.Quasithin.Background.G11Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Module.ZMod
import Mathlib.Tactic.Group
public import CFSG.CGT.Foote82.T66.MC1Steps
public import CFSG.CGT.Foote82.T66.Steps
public import CFSG.CGT.PushingUp.BenderBridge
public import CFSG.CGT.PushingUp.BlockOrder
public import CFSG.CGT.PushingUpLit.BHS7.BlockComm
public import CFSG.CGT.PushingUpLit.BHS7.SevenThree
public import CFSG.CGT.PushingUpLit.BHS7.VFacts
public import CFSG.CGT.PushingUpLit.Glue.ModuleTrivial
public import CFSG.Fischer.Classification.Defs
public import CFSG.GroupTheory.ConjugatePairSubnormality
public import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
public import CFSG.LocalAnalysis.AGLEmbedding.Extremal
public import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockInputs
public import CFSG.LocalAnalysis.ComponentClassification.SmallLocalFitting
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellMotion
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Monster.Code.Weights
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.RankThree.PartTwo.Sec19.Item194Used
public import CFSG.RankThree.PartTwo.Sec19.SimsTheoremCTypes
public import CFSG.RankThree.PartTwo.Sec6.Statements
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.CGT.Foote82.BASMax

open Matrix CFSG.ClassicalInvolution.Solomon73.Yamaki CFSG.ClassicalInvolution.Sp62Rec.Z6NA
  CFSG.RankThree.PartTwo CFSG.CGT.Foote82.OmegaSix

local notation "GL6" => GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)
local notation "Mat6" => Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)

theorem maxMatCheck_holds : maxMatCheck () = true :=
  Certificates.certificate919005.1

theorem maxMemCheck_holds : maxMemCheck () = true :=
  Certificates.certificate919005.2.1

theorem crEnumCheck_holds : crEnumCheck () = true :=
  Certificates.certificate919005.2.2.1

theorem maxGen1Check_holds : maxGen1Check () = true :=
  Certificates.certificate919005.2.2.2.1

theorem maxGen2Check_holds : maxGen2Check () = true :=
  Certificates.certificate919005.2.2.2.2.1

theorem maxCosetCheck_holds : maxCosetCheck () = true :=
  Certificates.certificate919005.2.2.2.2.2.1

theorem maxReflCheck_holds : maxReflCheck () = true :=
  Certificates.certificate919005.2.2.2.2.2.2

theorem maxMatCheck_spec :
    cr1Mat * rMat = rMat * cr1Mat ∧ cr2Mat * rMat = rMat * cr2Mat ∧ dc1Mat * dc1Mat = 1 ∧
      dc2Mat * dc2Mat = 1 ∧ ¬ dc1Mat * rMat = rMat * dc1Mat := by
  have h := maxMatCheck_holds
  simp only [maxMatCheck, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    decide_eq_false_iff_not] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem glCode_mul3 (x y z : GL6) :
    glCode (x * y * z) = compA (compA (glCode x) (glCode y)) (glCode z) := by
  rw [isArrCode_glCode.mul, isArrCode_glCode.mul]

theorem exists_of_lookup {A : Mat6}
    (h : ((omegaEnum ()).lookup (marr A)).isSome = true) :
    ∃ x : ↥(omegaMinusTwo 2), ((x : GL6) : Mat6) = A := by
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp h
  obtain ⟨hks, hke⟩ := Enum.lookup_spec hk
  obtain ⟨x, hx⟩ := exists_glArr_eq hks
  exact ⟨x, marr_injective (hx.trans hke)⟩

theorem xor_eq_vcode (t : GL6) {k : ℕ} (hk : k < 64) :
    (glCode t)[k]! ^^^ k = vcode (((t : Mat6) - 1) *ᵥ cvec k) := by
  have hlt : (glCode t)[k]! < 64 := by
    rw [glCode, marr_get _ hk]
    exact vcode_lt _
  rw [sub_one_mulVec_cvec t hk, vcode_cvec _ (Nat.xor_lt_two_pow (n := 6) hlt hk)]

theorem rank1_of_finrank {t : GL6}
    (h : Module.finrank (ZMod 2) ↥(LinearMap.range (mulVecLin ((t : Mat6) - 1))) = 1) :
    rank1 (glCode t) = true := by
  obtain ⟨⟨v, hv⟩, hv0, hall⟩ := finrank_eq_one_iff'.mp h
  have hv0' : v ≠ 0 := fun h0 => hv0 (Subtype.ext h0)
  have h01 : ∀ u, ((t : Mat6) - 1) *ᵥ u = 0 ∨ ((t : Mat6) - 1) *ᵥ u = v := by
    intro u
    obtain ⟨c, hc⟩ := hall ⟨_, LinearMap.mem_range_self (mulVecLin ((t : Mat6) - 1)) u⟩
    have hc' : c • v = ((t : Mat6) - 1) *ᵥ u := congrArg Subtype.val hc
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
    · left
      rw [← hc', zero_smul]
    · right
      rw [← hc', one_smul]
  obtain ⟨u, hu⟩ := hv
  rw [mulVecLin_apply] at hu
  simp only [rank1, List.any_eq_true, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    bne_iff_ne, ne_eq, beq_iff_eq, Bool.or_eq_true]
  refine ⟨vcode v, vcode_lt v, ⟨fun h0 => hv0' ?_, vcode u, vcode_lt u, ?_⟩, fun k hk => ?_⟩
  · rw [← cvec_vcode v, h0]
    decide
  · rw [xor_eq_vcode t (vcode_lt u), cvec_vcode, hu]
  · rw [xor_eq_vcode t hk]
    rcases h01 (cvec k) with h | h
    · left
      rw [h]
      decide
    · right
      rw [h]

theorem genA6_get' :
    ∀ j < (genA6 ()).size,
      (genA6 ())[j]! = glCode ((gen6 j : ↥(omegaMinusTwo 2)) : GL6) :=
  genA6_get

theorem genA6Inv_get :
    ∀ j < (genA6 ()).size,
      (genA6Inv ())[j]! = glCode ((gen6 j : ↥(omegaMinusTwo 2)) : GL6)⁻¹ := by
  intro j hj
  rw [genA6_size] at hj
  rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;> rfl

theorem exists_conj_rGL
    {D : GL6}
    (hD : D ∈ CFSG.PGLModel.orthogonalMinus 2 (ZMod 2) 1 1)
    (hrank : Module.finrank (ZMod 2) ↥(LinearMap.range (mulVecLin ((D : Mat6) - 1))) = 1) :
    ∃ x ∈ omegaMinusTwo 2, x * rGL * x⁻¹ = D := by
  have h := maxReflCheck_holds
  simp only [maxReflCheck, Bool.and_eq_true, Array.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true'] at h
  obtain ⟨htree, hall⟩ := h
  obtain ⟨k, hk, hke⟩ := exists_oEnum hD
  have hx := hall k hk
  rw [← getElem!_pos (oEnum ()).elems k hk, hke] at hx
  rcases hx with hx | hx
  · rw [rank1_of_finrank hrank] at hx
    exact absurd hx (by decide)
  · obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hx
    obtain ⟨his, hie⟩ := Enum.lookup_spec hi
    have htree' : conjTreeOK (reflEnum ()) (genA6 ()) (genA6Inv ()) (glCode rGL) = true := htree
    obtain ⟨g, hg, hge⟩ := exists_conj_of_conjTreeOK isArrCode_glCode genA6_get' genA6Inv_get
      htree' i his
    have hcl : Subgroup.closure ((fun j => ((gen6 j : ↥(omegaMinusTwo 2)) : GL6)) ''
        Set.Iio (genA6 ()).size) ≤ omegaMinusTwo 2 := by
      rw [Subgroup.closure_le]
      rintro _ ⟨j, -, rfl⟩
      exact (gen6 j).2
    exact ⟨g, hcl hg, isArrCode_glCode.injective (hge.trans hie)⟩

theorem closure_eq_omega {gs : Array (Array ℕ)} {E : Enum}
    {s : ℕ → GL6} (hgs : ∀ j < gs.size, gs[j]! = glCode (s j))
    (hs : ∀ j < gs.size, s j ∈ omegaMinusTwo 2) (h : enumOK E gs = true)
    (hsize : E.elems.size = 25920) :
    Subgroup.closure (s '' Set.Iio gs.size) = omegaMinusTwo 2 := by
  have hcard := card_closure_eq_of_enumOK isArrCode_glCode hgs h
  rw [hsize] at hcard
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rw [Subgroup.closure_le]
    rintro _ ⟨j, hj, rfl⟩
    exact hs j hj
  · rw [hcard, MC2.card_omegaMinusTwo_two]

theorem eq_top_of_closure {G : Type*} [Group G] {Ω : Subgroup G} {H : Subgroup ↥Ω} {S : Set G}
    (hS : Subgroup.closure S = Ω) (hSH : ∀ y ∈ S, ∃ h : y ∈ Ω, (⟨y, h⟩ : ↥Ω) ∈ H) : H = ⊤ := by
  have hle : Subgroup.closure S ≤ H.map Ω.subtype := by
    rw [Subgroup.closure_le]
    intro y hy
    obtain ⟨hyΩ, hyH⟩ := hSH y hy
    exact ⟨⟨y, hyΩ⟩, hyH, rfl⟩
  rw [eq_top_iff]
  intro y _
  have hy : (y : G) ∈ Subgroup.closure S := by
    rw [hS]
    exact y.2
  obtain ⟨z, hz, hzy⟩ := hle hy
  have hzy' : z = y := Subtype.ext hzy
  rw [← hzy']
  exact hz

theorem mem_of_coset {H : Subgroup ↥(omegaMinusTwo 2)}
    (hKH : (Subgroup.centralizer ({rGL} : Set GL6)).subgroupOf (omegaMinusTwo 2) ≤ H)
    {g γ : ↥(omegaMinusTwo 2)} (hg : g ∈ H) {x : GL6} (hx : x ∈ omegaMinusTwo 2)
    (hxr : x * rGL = rGL * x) (hγγ : (γ : GL6) * γ = 1)
    (h : x * (g : GL6) * rGL = (γ : GL6) * rGL * γ * (x * g)) : γ ∈ H := by
  have hw : (γ : GL6) * x * g ∈ omegaMinusTwo 2 := mul_mem (mul_mem γ.2 hx) g.2
  have hwr : ((γ : GL6) * x * g) * rGL = rGL * ((γ : GL6) * x * g) := by
    calc ((γ : GL6) * x * g) * rGL = (γ : GL6) * (x * g * rGL) := by group
      _ = (γ : GL6) * ((γ : GL6) * rGL * γ * (x * g)) := by rw [h]
      _ = ((γ : GL6) * γ) * rGL * (γ * x * g) := by group
      _ = rGL * ((γ : GL6) * x * g) := by rw [hγγ, one_mul]
  have hwK : (⟨_, hw⟩ : ↥(omegaMinusTwo 2)) ∈
      (Subgroup.centralizer ({rGL} : Set GL6)).subgroupOf (omegaMinusTwo 2) := by
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
    exact hwr
  have hxK : (⟨x, hx⟩ : ↥(omegaMinusTwo 2)) ∈
      (Subgroup.centralizer ({rGL} : Set GL6)).subgroupOf (omegaMinusTwo 2) := by
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
    exact hxr
  have he : γ = ⟨_, hw⟩ * g⁻¹ * (⟨x, hx⟩ : ↥(omegaMinusTwo 2))⁻¹ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subtype.coe_mk]
    group
  rw [he]
  exact H.mul_mem (H.mul_mem (hKH hwK) (H.inv_mem hg)) (H.inv_mem (hKH hxK))

theorem isCoatom_centralizer_rGL :
    IsCoatom ((Subgroup.centralizer ({rGL} : Set GL6)).subgroupOf (omegaMinusTwo 2)) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := maxMatCheck_spec
  have hmem := maxMemCheck_holds
  simp only [maxMemCheck, Bool.and_eq_true] at hmem
  obtain ⟨⟨⟨m1, m2⟩, m3⟩, m4⟩ := hmem
  obtain ⟨c₁, hc₁⟩ := exists_of_lookup m1
  obtain ⟨c₂, hc₂⟩ := exists_of_lookup m2
  obtain ⟨γ₁, hγ₁⟩ := exists_of_lookup m3
  obtain ⟨γ₂, hγ₂⟩ := exists_of_lookup m4
  have hK : ∀ y : ↥(omegaMinusTwo 2),
      y ∈ (Subgroup.centralizer ({rGL} : Set GL6)).subgroupOf (omegaMinusTwo 2) ↔
        (y : GL6) * rGL = rGL * y := fun y => by
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
  have hc₁r : (c₁ : GL6) * rGL = rGL * c₁ := Units.ext (by
    rw [Units.val_mul, Units.val_mul, hc₁]
    exact h1)
  have hc₂r : (c₂ : GL6) * rGL = rGL * c₂ := Units.ext (by
    rw [Units.val_mul, Units.val_mul, hc₂]
    exact h2)
  have hγ₁γ₁ : (γ₁ : GL6) * γ₁ = 1 := Units.ext (by
    rw [Units.val_mul, hγ₁]
    exact h3)
  have hγ₂γ₂ : (γ₂ : GL6) * γ₂ = 1 := Units.ext (by
    rw [Units.val_mul, hγ₂]
    exact h4)
  have hgsC : ∀ j < (genCr ()).size,
      (genCr ())[j]! = glCode (if j = 0 then (c₁ : GL6) else (c₂ : GL6)) := by
    intro j hj
    rw [show (genCr ()).size = 2 from rfl] at hj
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
    · show marr cr1Mat = marr ((c₁ : GL6) : Mat6)
      rw [hc₁]
    · show marr cr2Mat = marr ((c₂ : GL6) : Mat6)
      rw [hc₂]
  have hCle : Subgroup.closure ((fun j => if j = 0 then (c₁ : GL6) else (c₂ : GL6)) ''
      Set.Iio (genCr ()).size) ≤ omegaMinusTwo 2 ⊓ Subgroup.centralizer ({rGL} : Set GL6) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨j, hj, rfl⟩
    rw [Set.mem_Iio, show (genCr ()).size = 2 from rfl] at hj
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
    · exact Subgroup.mem_inf.2 ⟨c₁.2, Subgroup.mem_centralizer_singleton_iff.2 hc₁r⟩
    · exact Subgroup.mem_inf.2 ⟨c₂.2, Subgroup.mem_centralizer_singleton_iff.2 hc₂r⟩
  have hC : treeOK (crEnum ()) (genCr ()) = true := crEnumCheck_holds
  have htreeC := CFSG.ClassicalInvolution.Sp62Rec.Z6NA.exists_mem_closure_of_treeOK
    isArrCode_glCode hgsC hC
  have hg1 := maxGen1Check_holds
  simp only [maxGen1Check, Bool.and_eq_true, beq_iff_eq] at hg1
  have hgs1 : ∀ j < (genCr1 ()).size, (genCr1 ())[j]! =
      glCode (if j = 0 then (c₁ : GL6) else if j = 1 then (c₂ : GL6) else (γ₁ : GL6)) := by
    intro j hj
    rw [show (genCr1 ()).size = 3 from rfl] at hj
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
    · show marr cr1Mat = marr ((c₁ : GL6) : Mat6)
      rw [hc₁]
    · show marr cr2Mat = marr ((c₂ : GL6) : Mat6)
      rw [hc₂]
    · show marr dc1Mat = marr ((γ₁ : GL6) : Mat6)
      rw [hγ₁]
  have hs1 : ∀ j < (genCr1 ()).size,
      (if j = 0 then (c₁ : GL6) else if j = 1 then (c₂ : GL6) else (γ₁ : GL6)) ∈
        omegaMinusTwo 2 := by
    intro j _
    split_ifs
    · exact c₁.2
    · exact c₂.2
    · exact γ₁.2
  have hgen1 := closure_eq_omega hgs1 hs1 hg1.1 hg1.2
  have hg2 := maxGen2Check_holds
  simp only [maxGen2Check, Bool.and_eq_true, beq_iff_eq] at hg2
  have hgs2 : ∀ j < (genCr2 ()).size, (genCr2 ())[j]! =
      glCode (if j = 0 then (c₁ : GL6) else if j = 1 then (c₂ : GL6) else (γ₂ : GL6)) := by
    intro j hj
    rw [show (genCr2 ()).size = 3 from rfl] at hj
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
    · show marr cr1Mat = marr ((c₁ : GL6) : Mat6)
      rw [hc₁]
    · show marr cr2Mat = marr ((c₂ : GL6) : Mat6)
      rw [hc₂]
    · show marr dc2Mat = marr ((γ₂ : GL6) : Mat6)
      rw [hγ₂]
  have hs2 : ∀ j < (genCr2 ()).size,
      (if j = 0 then (c₁ : GL6) else if j = 1 then (c₂ : GL6) else (γ₂ : GL6)) ∈
        omegaMinusTwo 2 := by
    intro j _
    split_ifs
    · exact c₁.2
    · exact c₂.2
    · exact γ₂.2
  have hgen2 := closure_eq_omega hgs2 hs2 hg2.1 hg2.2
  have hS1 : glCode ((γ₁ : GL6) * rGL * γ₁) = marr (dc1Mat * rMat * dc1Mat) := by
    rw [glCode, Units.val_mul, Units.val_mul, hγ₁]
    rfl
  have hS2 : glCode ((γ₂ : GL6) * rGL * γ₂) = marr (dc2Mat * rMat * dc2Mat) := by
    rw [glCode, Units.val_mul, Units.val_mul, hγ₂]
    rfl
  have hcos := maxCosetCheck_holds
  simp only [maxCosetCheck, Array.all_eq_true, Bool.or_eq_true, beq_iff_eq,
    Array.any_eq_true] at hcos
  refine ⟨fun htop => ?_, fun H hKH => ?_⟩
  ·
    have hγK : γ₁ ∈ (Subgroup.centralizer ({rGL} : Set GL6)).subgroupOf (omegaMinusTwo 2) := by
      rw [htop]
      exact Subgroup.mem_top γ₁
    rw [hK] at hγK
    apply h5
    have h := congrArg Units.val hγK
    rw [Units.val_mul, Units.val_mul, hγ₁] at h
    exact h
  · obtain ⟨g, hgH, hgK⟩ := SetLike.exists_of_lt hKH
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp (lookup_glArr_isSome g)
    obtain ⟨hks, hke⟩ := Enum.lookup_spec hk
    have hc := hcos k hks
    rw [← getElem!_pos (omegaEnum ()).elems k hks, hke] at hc
    rcases hc with hc | ⟨j, hj, hc⟩
    ·
      exfalso
      apply hgK
      rw [hK]
      apply isArrCode_glCode.injective
      rw [isArrCode_glCode.mul, isArrCode_glCode.mul]
      exact hc
    · obtain ⟨x, hx, hxe⟩ := htreeC j hj
      rw [← getElem!_pos (crEnum ()).elems j hj, ← hxe] at hc
      obtain ⟨hxΩ, hxr⟩ := Subgroup.mem_inf.1 (hCle hx)
      rw [Subgroup.mem_centralizer_singleton_iff] at hxr
      rcases hc with hc | hc
      · have hgrp : x * (g : GL6) * rGL = (γ₁ : GL6) * rGL * γ₁ * (x * g) := by
          apply isArrCode_glCode.injective
          rw [isArrCode_glCode.mul ((γ₁ : GL6) * rGL * γ₁), hS1, glCode_mul3,
            isArrCode_glCode.mul x]
          exact hc
        have hγH := mem_of_coset hKH.le hgH hxΩ hxr hγ₁γ₁ hgrp
        refine eq_top_of_closure hgen1 ?_
        rintro _ ⟨i, hi, rfl⟩
        rw [Set.mem_Iio, show (genCr1 ()).size = 3 from rfl] at hi
        rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
        · exact ⟨c₁.2, hKH.le ((hK c₁).2 hc₁r)⟩
        · exact ⟨c₂.2, hKH.le ((hK c₂).2 hc₂r)⟩
        · exact ⟨γ₁.2, hγH⟩
      · have hgrp : x * (g : GL6) * rGL = (γ₂ : GL6) * rGL * γ₂ * (x * g) := by
          apply isArrCode_glCode.injective
          rw [isArrCode_glCode.mul ((γ₂ : GL6) * rGL * γ₂), hS2, glCode_mul3,
            isArrCode_glCode.mul x]
          exact hc
        have hγH := mem_of_coset hKH.le hgH hxΩ hxr hγ₂γ₂ hgrp
        refine eq_top_of_closure hgen2 ?_
        rintro _ ⟨i, hi, rfl⟩
        rw [Set.mem_Iio, show (genCr2 ()).size = 3 from rfl] at hi
        rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
        · exact ⟨c₁.2, hKH.le ((hK c₁).2 hc₁r)⟩
        · exact ⟨c₂.2, hKH.le ((hK c₂).2 hc₂r)⟩
        · exact ⟨γ₂.2, hγH⟩

section Module

open CFSG.Open CFSG.Quasithin.G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

private theorem glv_mul_apply' (a b : GLV V) (v : V) : (a * b) v = a (b v) := rfl

private theorem glv_inv_apply_apply' (a : GLV V) (v : V) : a⁻¹ (a v) = v :=
  a.symm_apply_apply v

private theorem glv_apply_inv_apply' (a : GLV V) (v : V) : a (a⁻¹ v) = v :=
  a.apply_symm_apply v

private theorem apply_mem_commSpace {L : Subgroup (GLV V)} {x : GLV V}
    (hx : x ∈ Subgroup.normalizer (L : Set (GLV V))) {w : V} (hw : w ∈ commSpace L ⊤) :
    x w ∈ commSpace L ⊤ := by
  have hle : commSpace L ⊤ ≤ (commSpace L ⊤).comap (x : V →ₗ[ZMod 2] V) := by
    refine commSpace_le_iff.2 fun k hk u _ => ?_
    show x (k u - u) ∈ commSpace L ⊤
    have e : x (k u - u) = (x * k * x⁻¹) (x u) - x u := by
      rw [map_sub, glv_mul_apply', glv_mul_apply', glv_inv_apply_apply']
    rw [e]
    exact sub_mem_commSpace ((Subgroup.mem_normalizer_iff.1 hx k).1 hk) Submodule.mem_top
  exact hle hw

private theorem apply_mem_fixedSpace {L : Subgroup (GLV V)} {x : GLV V}
    (hx : x ∈ Subgroup.normalizer (L : Set (GLV V))) {w : V} (hw : w ∈ fixedSpace L) :
    x w ∈ fixedSpace L := by
  intro k hk
  have hk' : x⁻¹ * k * x ∈ L := by
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hx) k).1 hk
    simpa using this
  have := hw _ hk'
  rw [glv_mul_apply', glv_mul_apply'] at this
  have h2 := congrArg x this
  rwa [glv_apply_inv_apply'] at h2

private theorem eq_one_or_eq_of_mem_zpowers {G : Type*} [Group G] {e k : G} (he : e * e = 1)
    (hk : k ∈ Subgroup.zpowers e) : k = 1 ∨ k = e := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
  have h2 : e ^ (2 : ℤ) = 1 := by rw [zpow_two, he]
  rw [zpow_eq_zpow_emod n h2]
  rcases Int.emod_two_eq_zero_or_one n with h | h <;> rw [h] <;> simp

theorem injective_alpha {L : Subgroup (GLV V)} {α : ↥L →* ↥(omegaMinusTwo 2)}
    {β : ↥(commSpace L ⊤) →+ (Fin 2 ⊕ Fin 2 ⊕ Fin 2 → ZMod 2)}
    (hβk : ∀ w, β w = 0 ↔ (w : V) ∈ fixedSpace L)
    (hrel : ∀ (ℓ : ↥L) (w w' : ↥(commSpace L ⊤)), (w' : V) = (ℓ : GLV V) w →
      β w' = (((α ℓ : ↥(omegaMinusTwo 2)) : GL6) : Mat6) *ᵥ β w)
    (hf : FaithfulTildeV L) : Function.Injective α := by
  rw [injective_iff_map_eq_one]
  intro ℓ hℓ
  refine Subtype.ext (hf ℓ ℓ.2 fun w hw => ?_)
  have hw' : (ℓ : GLV V) w ∈ commSpace L ⊤ := apply_mem_commSpace (Subgroup.le_normalizer ℓ.2) hw
  have h := hrel ℓ ⟨w, hw⟩ ⟨_, hw'⟩ rfl
  rw [hℓ, OneMemClass.coe_one, Units.val_one, one_mulVec] at h
  have h0 : β (⟨_, hw'⟩ - ⟨w, hw⟩) = 0 := by
    rw [map_sub, h, sub_self]
  exact (hβk _).1 h0

theorem exists_matrix {L : Subgroup (GLV V)}
    {β : ↥(commSpace L ⊤) →+ (Fin 2 ⊕ Fin 2 ⊕ Fin 2 → ZMod 2)} (hβs : Function.Surjective β)
    (hβk : ∀ w, β w = 0 ↔ (w : V) ∈ fixedSpace L) {d : GLV V}
    (hd : d ∈ Subgroup.normalizer (L : Set (GLV V))) (hdd : d * d = 1) :
    ∃ D : GL6, D * D = 1 ∧
      ∀ w w' : ↥(commSpace L ⊤), (w' : V) = d w → β w' = (D : Mat6) *ᵥ β w := by
  let dU : ↥(commSpace L ⊤) → ↥(commSpace L ⊤) := fun w => ⟨d w, apply_mem_commSpace hd w.2⟩
  have hdU_eq : ∀ w₁ w₂, β w₁ = β w₂ → β (dU w₁) = β (dU w₂) := by
    intro w₁ w₂ h
    rw [← sub_eq_zero, ← map_sub, hβk] at h ⊢
    have e : ((dU w₁ - dU w₂ : ↥(commSpace L ⊤)) : V) =
        d ((w₁ - w₂ : ↥(commSpace L ⊤)) : V) := by
      rw [Submodule.coe_sub, Submodule.coe_sub, map_sub]
    rw [e]
    exact apply_mem_fixedSpace hd h
  have hdU_add : ∀ w₁ w₂, dU (w₁ + w₂) = dU w₁ + dU w₂ := fun w₁ w₂ =>
    Subtype.ext (map_add d (w₁ : V) w₂)
  have hdUdU : ∀ w, dU (dU w) = w := fun w => Subtype.ext (by
    show d (d w) = w
    rw [← glv_mul_apply', hdd]
    rfl)
  let w₀ := Function.surjInv hβs
  have hw₀ : ∀ x, β (w₀ x) = x := Function.surjInv_eq hβs
  let f : (Fin 2 ⊕ Fin 2 ⊕ Fin 2 → ZMod 2) → (Fin 2 ⊕ Fin 2 ⊕ Fin 2 → ZMod 2) :=
    fun x => β (dU (w₀ x))
  have hf : ∀ w, f (β w) = β (dU w) := fun w => hdU_eq _ _ (hw₀ (β w))
  have hfadd : ∀ x y, f (x + y) = f x + f y := by
    intro x y
    have h := hf (w₀ x + w₀ y)
    rw [map_add, hw₀, hw₀, hdU_add, map_add] at h
    exact h
  let fA : (Fin 2 ⊕ Fin 2 ⊕ Fin 2 → ZMod 2) →+ (Fin 2 ⊕ Fin 2 ⊕ Fin 2 → ZMod 2) :=
    AddMonoidHom.mk' f hfadd
  let M : Mat6 := LinearMap.toMatrix' (fA.toZModLinearMap 2)
  have hM : ∀ x, M *ᵥ x = f x := fun x => by
    rw [LinearMap.toMatrix'_mulVec]
    rfl
  have hMw : ∀ w, M *ᵥ β w = β (dU w) := fun w => by rw [hM, hf]
  have hMM : M * M = 1 := by
    rw [ext_iff_mulVec]
    intro x
    obtain ⟨w, rfl⟩ := hβs x
    rw [← mulVec_mulVec, hMw, hMw, hdUdU, one_mulVec]
  refine ⟨⟨M, M, hMM, hMM⟩, Units.ext hMM, fun w w' hw' => ?_⟩
  have e : w' = dU w := Subtype.ext hw'
  rw [e]
  exact (hMw w).symm

theorem conj_eq {L : Subgroup (GLV V)} {α : ↥L →* ↥(omegaMinusTwo 2)}
    {β : ↥(commSpace L ⊤) →+ (Fin 2 ⊕ Fin 2 ⊕ Fin 2 → ZMod 2)} (hβs : Function.Surjective β)
    (hrel : ∀ (ℓ : ↥L) (w w' : ↥(commSpace L ⊤)), (w' : V) = (ℓ : GLV V) w →
      β w' = (((α ℓ : ↥(omegaMinusTwo 2)) : GL6) : Mat6) *ᵥ β w)
    {d : GLV V} (hd : d ∈ Subgroup.normalizer (L : Set (GLV V))) (hdd : d * d = 1) {D : GL6}
    (hDD : D * D = 1)
    (hD : ∀ w w' : ↥(commSpace L ⊤), (w' : V) = d w → β w' = (D : Mat6) *ᵥ β w) :
    ∀ ℓ ℓ' : ↥L, (ℓ' : GLV V) = d * ℓ * d⁻¹ →
      D * ((α ℓ : ↥(omegaMinusTwo 2)) : GL6) * D⁻¹ = ((α ℓ' : ↥(omegaMinusTwo 2)) : GL6) := by
  intro ℓ ℓ' hℓ'
  have hDinv : D⁻¹ = D := inv_eq_of_mul_eq_one_right hDD
  have hdinv : d⁻¹ = d := inv_eq_of_mul_eq_one_right hdd
  rw [hDinv]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, ext_iff_mulVec]
  intro v
  obtain ⟨w, rfl⟩ := hβs v
  have hw₁ : d w ∈ commSpace L ⊤ := apply_mem_commSpace hd w.2
  have hw₂ : (ℓ : GLV V) (d w) ∈ commSpace L ⊤ :=
    apply_mem_commSpace (Subgroup.le_normalizer ℓ.2) hw₁
  have hw₃ : d ((ℓ : GLV V) (d w)) ∈ commSpace L ⊤ := apply_mem_commSpace hd hw₂
  rw [← mulVec_mulVec, ← mulVec_mulVec, ← hD w ⟨_, hw₁⟩ rfl, ← hrel ℓ ⟨_, hw₁⟩ ⟨_, hw₂⟩ rfl,
    ← hD ⟨_, hw₂⟩ ⟨_, hw₃⟩ rfl]
  refine hrel ℓ' w ⟨_, hw₃⟩ ?_
  show d ((ℓ : GLV V) (d w)) = (ℓ' : GLV V) w
  rw [hℓ', hdinv]
  rfl

theorem finrank_range_add [Finite V] {L : Subgroup (GLV V)}
    {β : ↥(commSpace L ⊤) →+ (Fin 2 ⊕ Fin 2 ⊕ Fin 2 → ZMod 2)}
    (hβs : Function.Surjective β) (hβk : ∀ w, β w = 0 ↔ (w : V) ∈ fixedSpace L)
    {d : GLV V} (hd : d ∈ Subgroup.normalizer (L : Set (GLV V))) (hdd : d * d = 1) {D : GL6}
    (hD : ∀ w w' : ↥(commSpace L ⊤), (w' : V) = d w → β w' = (D : Mat6) *ᵥ β w) :
    Module.finrank (ZMod 2) ↥(LinearMap.range (mulVecLin ((D : Mat6) - 1))) +
        Module.finrank (ZMod 2) ↥(tildeVBot L) =
      Module.finrank (ZMod 2) ↥(BAS.tvComm L d) := by
  have hTU : BAS.tvComm L d ≤ commSpace L ⊤ :=
    sup_le (commSpace_le_iff.2 fun k hk u hu =>
      (commSpace L ⊤).sub_mem (apply_mem_commSpace ((Subgroup.zpowers_le.2 hd) hk) hu) hu)
      inf_le_right
  let ψ : ↥(BAS.tvComm L d) →ₗ[ZMod 2] (Fin 2 ⊕ Fin 2 ⊕ Fin 2 → ZMod 2) :=
    (β.toZModLinearMap 2).comp (Submodule.inclusion hTU)
  have hψ : ∀ t : ↥(BAS.tvComm L d), ψ t = β ⟨t, hTU t.2⟩ := fun t => rfl
  have hdU : ∀ u ∈ commSpace L ⊤, d u - u ∈ BAS.tvComm L d := fun u hu =>
    Submodule.mem_sup_left (sub_mem_commSpace (Subgroup.mem_zpowers d) hu)
  have hβd : ∀ (u : V) (hu : u ∈ commSpace L ⊤),
      β ⟨d u - u, hTU (hdU u hu)⟩ = ((D : Mat6) - 1) *ᵥ β ⟨u, hu⟩ := by
    intro u hu
    have e : (⟨d u - u, hTU (hdU u hu)⟩ : ↥(commSpace L ⊤)) =
        ⟨d u, apply_mem_commSpace hd hu⟩ - ⟨u, hu⟩ := rfl
    rw [e, map_sub, hD ⟨u, hu⟩ _ rfl, sub_mulVec, one_mulVec]
  have hrange : LinearMap.range ψ = LinearMap.range (mulVecLin ((D : Mat6) - 1)) := by
    apply le_antisymm
    · rintro _ ⟨t, rfl⟩
      rw [hψ]
      obtain ⟨t₁, ht₁, t₂, ht₂, ht⟩ := Submodule.mem_sup.1 t.2
      have hle : commSpace (Subgroup.zpowers d) (commSpace L ⊤) ≤
          ((LinearMap.range (mulVecLin ((D : Mat6) - 1))).comap
            (β.toZModLinearMap 2)).map (commSpace L ⊤).subtype := by
        refine commSpace_le_iff.2 fun k hk u hu => ?_
        rcases eq_one_or_eq_of_mem_zpowers hdd hk with hk1 | hk1
        · rw [hk1, show (1 : GLV V) u = u from rfl, sub_self]
          exact Submodule.zero_mem _
        · rw [hk1]
          exact ⟨⟨d u - u, hTU (hdU u hu)⟩, ⟨β ⟨u, hu⟩, (hβd u hu).symm⟩, rfl⟩
      obtain ⟨w₁, hw₁, hw₁e⟩ := hle ht₁
      have h2 : β ⟨t₂, ht₂.2⟩ = 0 := (hβk _).2 ht₂.1
      have h3 : (⟨t, hTU t.2⟩ : ↥(commSpace L ⊤)) = w₁ + ⟨t₂, ht₂.2⟩ := by
        apply Subtype.ext
        show (t : V) = (w₁ : V) + t₂
        rw [← ht, ← hw₁e]
        rfl
      rw [h3, map_add, h2, add_zero]
      exact hw₁
    · rintro _ ⟨v, rfl⟩
      obtain ⟨⟨u, hu⟩, rfl⟩ := hβs v
      exact ⟨⟨d u - u, hdU u hu⟩, by rw [hψ, mulVecLin_apply, ← hβd u hu]⟩
  have hker : LinearMap.ker ψ = (tildeVBot L).comap (BAS.tvComm L d).subtype := by
    ext t
    rw [LinearMap.mem_ker, hψ, hβk, Submodule.mem_comap, Submodule.subtype_apply]
    exact ⟨fun h => ⟨h, hTU t.2⟩, fun h => h.1⟩
  have hCT : tildeVBot L ≤ BAS.tvComm L d := le_sup_right
  have h := LinearMap.finrank_range_add_finrank_ker ψ
  rw [hrange, hker, (Submodule.comapSubtypeEquivOfLe hCT).finrank_eq] at h
  exact h

private theorem comm_iff_conj_eq {G : Type*} [Group G] (a b : G) :
    a * b = b * a ↔ b * a * b⁻¹ = a := by
  rw [mul_inv_eq_iff_eq_mul, eq_comm]

private theorem conj_comm_iff {G : Type*} [Group G] (x r a : G) :
    x⁻¹ * a * x * r = r * (x⁻¹ * a * x) ↔ x * r * x⁻¹ * a * (x * r * x⁻¹)⁻¹ = a := by
  constructor
  · intro h
    calc x * r * x⁻¹ * a * (x * r * x⁻¹)⁻¹ = x * (r * (x⁻¹ * a * x)) * r⁻¹ * x⁻¹ := by group
      _ = x * (x⁻¹ * a * x * r) * r⁻¹ * x⁻¹ := by rw [h]
      _ = a := by group
  · intro h
    calc x⁻¹ * a * x * r = x⁻¹ * (x * r * x⁻¹ * a * (x * r * x⁻¹)⁻¹) * x * r := by rw [h]
      _ = r * (x⁻¹ * a * x) := by group

theorem isCoatom_of_conj
    {L : Subgroup (GLV V)} {α : ↥L →* ↥(omegaMinusTwo 2)}
    (hα : Function.Bijective α) {d : GLV V} (hd : d ∈ Subgroup.normalizer (L : Set (GLV V)))
    {D x : GL6} (hx : x ∈ omegaMinusTwo 2) (hxD : x * rGL * x⁻¹ = D)
    (hconj : ∀ ℓ ℓ' : ↥L, (ℓ' : GLV V) = d * ℓ * d⁻¹ →
      D * ((α ℓ : ↥(omegaMinusTwo 2)) : GL6) * D⁻¹ = ((α ℓ' : ↥(omegaMinusTwo 2)) : GL6)) :
    IsCoatom ((L ⊓ Subgroup.centralizer ({d} : Set (GLV V))).subgroupOf L) := by
  let φ : ↥L ≃* ↥(omegaMinusTwo 2) :=
    (MulEquiv.ofBijective α hα).trans (MulAut.conj (⟨x, hx⟩ : ↥(omegaMinusTwo 2))⁻¹)
  have hφ : ∀ ℓ : ↥L, ((φ ℓ : ↥(omegaMinusTwo 2)) : GL6) = x⁻¹ * (α ℓ : GL6) * x := by
    intro ℓ
    simp [φ, MulAut.conj_apply]
  have hmem : ∀ ℓ : ↥L, ℓ ∈ (L ⊓ Subgroup.centralizer ({d} : Set (GLV V))).subgroupOf L ↔
      φ ℓ ∈ (Subgroup.centralizer ({rGL} : Set GL6)).subgroupOf (omegaMinusTwo 2) := by
    intro ℓ
    have hℓ'L : d * (ℓ : GLV V) * d⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hd _).1 ℓ.2
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff, hφ,
      conj_comm_iff, hxD, hconj ℓ ⟨_, hℓ'L⟩ rfl, comm_iff_conj_eq]
    constructor
    · rintro ⟨-, h⟩
      have he : (⟨_, hℓ'L⟩ : ↥L) = ℓ := Subtype.ext h
      rw [he]
    · intro h
      exact ⟨ℓ.2, congrArg Subtype.val (hα.1 (Subtype.ext h))⟩
  have hmap : MulEquiv.mapSubgroup φ ((L ⊓ Subgroup.centralizer ({d} : Set (GLV V))).subgroupOf L) =
      (Subgroup.centralizer ({rGL} : Set GL6)).subgroupOf (omegaMinusTwo 2) := by
    ext y
    rw [MulEquiv.coe_mapSubgroup, Subgroup.mem_map_equiv, hmem, MulEquiv.apply_symm_apply]
  rw [← OrderIso.isCoatom_iff (MulEquiv.mapSubgroup φ), hmap]
  exact isCoatom_centralizer_rGL

end Module

end CFSG.CGT.Foote82.BASMax

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11 CFSG.RankThree.PartTwo Matrix

theorem basMaximal_omegaSix
    (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (L : Subgroup (GLV V))
    (hL : IsOmegaMinusModule L 2) (hf : FaithfulTildeV L) (hirr : HasIrrTildeV L)
    (d : GLV V) (hd : d ∈ Subgroup.normalizer (L : Set (GLV V))) (hd2 : orderOf d = 2)
    (htv : Module.finrank (ZMod 2) ↥(BAS.tvComm L d) =
      Module.finrank (ZMod 2) ↥(tildeVBot L) + 1) :
    IsCoatom ((L ⊓ Subgroup.centralizer ({d} : Set (GLV V))).subgroupOf L) := by
  obtain ⟨α, hαs, β, hβs, hβker, hrel⟩ := hL
  have hβk : ∀ w, β w = 0 ↔ (w : V) ∈ fixedSpace L := L13Aux.ker_iff_of_eq hβker
  have hrel' : ∀ (ℓ : ↥L) (w w' : ↥(commSpace L ⊤)), (w' : V) = (ℓ : GLV V) w →
      β w' = (((α ℓ : ↥(omegaMinusTwo 2)) : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) :
        Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) *ᵥ β w := hrel
  have hdd : d * d = 1 := by
    have h := pow_orderOf_eq_one d
    rw [hd2, sq] at h
    exact h
  obtain ⟨D, hDD, hD⟩ := BASMax.exists_matrix hβs hβk hd hdd
  have hconj := BASMax.conj_eq hβs hrel' hd hdd hDD hD
  have hDO : D ∈ CFSG.PGLModel.orthogonalMinus 2 (ZMod 2) 1 1 := by
    refine omegaMinusSixNormalizer_holds D hDD fun y hy => ?_
    obtain ⟨ℓ, hℓ⟩ := hαs ⟨y, hy⟩
    have hℓ'L : d * (ℓ : GLV V) * d⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hd _).1 ℓ.2
    have h := hconj ℓ ⟨_, hℓ'L⟩ rfl
    rw [hℓ] at h
    have h' : D * y * D⁻¹ = ((α ⟨_, hℓ'L⟩ : ↥(omegaMinusTwo 2)) :
        GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) := h
    rw [h']
    exact (α _).2
  have hrank : Module.finrank (ZMod 2) ↥(LinearMap.range (mulVecLin
      ((D : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) - 1))) = 1 := by
    have := BASMax.finrank_range_add hβs hβk hd hdd hD
    omega
  obtain ⟨x, hx, hxD⟩ := BASMax.exists_conj_rGL hDO hrank
  exact BASMax.isCoatom_of_conj ⟨BASMax.injective_alpha hβk hrel' hf, hαs⟩ hd hx hxD hconj

end CFSG.CGT.Foote82
