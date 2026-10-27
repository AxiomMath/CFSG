module

public import CFSG.CGT.Foote82.T66.CitedCaseII
public import CFSG.CGT.Foote82.T66.CertProofsOmegaSixA6Centralizer
public import Certificates.Certificate919121
public import Certificates.Certificate919122
public import Certificates.Certificate919123
import CFSG.HardMathSupport.Timmesfeld.Balance.Alt.AutSix
import CFSG.LocalAnalysis.Asc75.Helpers
import Mathlib.Tactic.Group
import CFSG.LocalAnalysis.Asc75.Conj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.CGT.Foote82

local notation "GL6" => GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)

namespace CaseIIClassAux

open Matrix CFSG.ClassicalInvolution.Solomon73.Yamaki CFSG.CGT.Foote82.OmegaSix
  CFSG.RankThree.PartTwo CFSG.PGLModel
open scoped commutatorElement

theorem omClassCheck_holds : omClassCheck () = true :=
  Certificates.certificate919121.1

theorem centCountCheck_holds : centCountCheck () = true :=
  Certificates.certificate919121.2

theorem reflOrbitCheck_holds : reflOrbitCheck () = true :=
  Certificates.certificate919122.1

theorem a6Check_holds : a6Check () = true :=
  Certificates.certificate919122.2.1

theorem a6CentCheck_holds : a6CentCheck () = true :=
  Certificates.certificate919122.2.2

theorem closureCheck_holds : closureCheck () = true :=
  Certificates.certificate919123

private def sOm (i : ℕ) : GL6 :=
  ((gen6 i : ↥(omegaMinusTwo 2)) : GL6)

private theorem sOm_get :
    ∀ j < (genA6 ()).size, (genA6 ())[j]! = glCode (sOm j) := by
  intro j hj
  rw [genA6_size] at hj
  rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;> rfl

private theorem sOmInv_get :
    ∀ j < (genA6 ()).size, (genA6Inv ())[j]! = glCode (sOm j)⁻¹ := by
  intro j hj
  rw [genA6_size] at hj
  rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;> rfl

private theorem closure_sOm_le :
    Subgroup.closure (sOm '' Set.Iio (genA6 ()).size) ≤ omegaMinusTwo 2 := by
  rw [Subgroup.closure_le]
  rintro _ ⟨j, -, rfl⟩
  exact (gen6 j).2

private theorem exists_conj_of_lookup {EX : Enum} {x t : GL6}
    (htree : conjTreeOK EX (genA6 ()) (genA6Inv ()) (glCode x) = true)
    (h : (EX.lookup (glCode t)).isSome) : ∃ g ∈ omegaMinusTwo 2, g * x * g⁻¹ = t := by
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp h
  obtain ⟨his, hie⟩ := Enum.lookup_spec hi
  obtain ⟨g, hg, hge⟩ := exists_conj_of_conjTreeOK isArrCode_glCode sOm_get sOmInv_get htree i his
  exact ⟨g, closure_sOm_le hg, isArrCode_glCode.injective (hge.trans hie)⟩

private theorem omClassCheck_spec :
    conjTreeOK (omClassA ()) (genA6 ()) (genA6Inv ()) (marr rAMat) = true ∧
      conjTreeOK (omClassB ()) (genA6 ()) (genA6Inv ()) (marr rBMat) = true ∧
      ∀ k (hk : k < (omegaEnum ()).elems.size),
        (!(compA (omegaEnum ()).elems[k] (omegaEnum ()).elems[k] == idA ()) ||
          (omegaEnum ()).elems[k] == idA () ||
          ((omClassA ()).lookup (omegaEnum ()).elems[k]).isSome ||
          ((omClassB ()).lookup (omegaEnum ()).elems[k]).isSome) = true := by
  have h := omClassCheck_holds
  simp only [omClassCheck, Bool.and_eq_true, Array.all_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

private theorem exists_conj_rep_omega
    {X : GL6}
    (hX : X ∈ omegaMinusTwo 2) (hX2 : X * X = 1) (hX1 : X ≠ 1) :
    ∃ g ∈ omegaMinusTwo 2, g * rAGL * g⁻¹ = X ∨ g * rBGL * g⁻¹ = X := by
  obtain ⟨hA, hB, hall⟩ := omClassCheck_spec
  obtain ⟨k, hk, hke⟩ := exists_omegaEnum hX
  have hx := hall k hk
  rw [← getElem!_pos, hke] at hx
  simp only [Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq, beq_eq_false_iff_ne] at hx
  have hsq : compA (glCode X) (glCode X) = idA () := by
    rw [← isArrCode_glCode.mul, hX2, isArrCode_glCode.one]
  have hne : glCode X ≠ idA () := by
    rw [← isArrCode_glCode.one]
    exact fun h => hX1 (isArrCode_glCode.injective h)
  rcases hx with ((hx | hx) | hx) | hx
  · exact absurd hsq hx
  · exact absurd hx hne
  · obtain ⟨g, hg, hgX⟩ := exists_conj_of_lookup (x := rAGL) hA hx
    exact ⟨g, hg, Or.inl hgX⟩
  · obtain ⟨g, hg, hgX⟩ := exists_conj_of_lookup (x := rBGL) hB hx
    exact ⟨g, hg, Or.inr hgX⟩

private theorem card_subtype_eq_count {H : Type*} [Group H] [Finite H] {cd : H → Array ℕ}
    (hc : CFSG.ClassicalInvolution.Sp62Rec.Z6NA.IsArrCode cd) {E : Enum}
    {gs : Array (Array ℕ)} {s : ℕ → H} (hgs : ∀ j < gs.size, gs[j]! = cd (s j))
    (h : enumOK E gs = true) (htop : Subgroup.closure (s '' Set.Iio gs.size) = ⊤)
    (P : Array ℕ → Bool) :
    Nat.card {x : H // P (cd x) = true} =
      Nat.count (fun i => P E.elems[i]! = true) E.elems.size := by
  have htree : treeOK E gs = true := by
    simp only [enumOK, Bool.and_eq_true] at h
    exact h.1.1
  have hnodup : ∀ i < E.elems.size, E.lookup E.elems[i]! = some i := by
    simp only [enumOK, Bool.and_eq_true] at h
    simpa only [nodupOK, allLt_iff, decide_eq_true_eq] using h.2
  choose e he hec using
    CFSG.ClassicalInvolution.Sp62Rec.Z6NA.exists_mem_closure_of_treeOK hc hgs htree
  rw [Nat.count_eq_card_fintype, Fintype.card_eq_nat_card]
  symm
  refine Nat.card_eq_of_bijective
    (fun k : {k : ℕ // k < E.elems.size ∧ P E.elems[k]! = true} =>
      (⟨e k.1 k.2.1, by rw [hec]; exact k.2.2⟩ : {x : H // P (cd x) = true})) ⟨?_, ?_⟩
  · rintro ⟨i, hi, _⟩ ⟨j, hj, _⟩ hij
    have hv : e i hi = e j hj := congrArg Subtype.val hij
    have hc' : E.elems[i]! = E.elems[j]! := by rw [← hec i hi, ← hec j hj, hv]
    have h1 := hnodup i hi
    rw [hc', hnodup j hj] at h1
    exact Subtype.ext (Option.some.inj h1).symm
  · rintro ⟨x, hx⟩
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp
      (CFSG.ClassicalInvolution.Sp62Rec.Z6NA.lookup_isSome_of_mem_closure hc hgs h
        (htop ▸ Subgroup.mem_top x))
    obtain ⟨hks, hke⟩ := Enum.lookup_spec hk
    exact ⟨⟨k, hks, by rw [hke]; exact hx⟩, Subtype.ext (hc.injective ((hec k hks).trans hke))⟩

private theorem commB_glCode (z x : GL6) : commB (glCode z) (glCode x) = true ↔ z * x = x * z := by
  rw [commB, beq_iff_eq, ← isArrCode_glCode.mul, ← isArrCode_glCode.mul]
  exact isArrCode_glCode.injective.eq_iff

private theorem card_inf_centralizer (x : GL6) :
    Nat.card ↥(omegaMinusTwo 2 ⊓ Subgroup.centralizer {x}) = centCount (glCode x) := by
  have htop : Subgroup.closure (gen6 '' Set.Iio (genA6 ()).size) = ⊤ := by
    rw [genA6_size]
    exact closure_gen6
  have h1 := card_subtype_eq_count (isArrCode_glArr (omegaMinusTwo 2)) genA6_get
    omegaEnum_spec.1 htop (fun t => commB t (glCode x))
  refine Eq.trans (Nat.card_congr ?_) h1
  exact {
    toFun := fun w => ⟨⟨w, (Subgroup.mem_inf.mp w.2).1⟩,
      (commB_glCode _ _).mpr
        (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp w.2).2)⟩
    invFun := fun z => ⟨(z.1 : GL6), Subgroup.mem_inf.mpr ⟨z.1.2,
      Subgroup.mem_centralizer_singleton_iff.mpr ((commB_glCode _ _).mp z.2)⟩⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

private theorem centCountCheck_spec :
    centCount (marr rMat) = 720 ∧ centCount (marr rAMat) = 576 ∧ centCount (marr rBMat) = 96 := by
  have h := centCountCheck_holds
  simp only [centCountCheck, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

private theorem card_C_r :
    Nat.card ↥(omegaMinusTwo 2 ⊓ Subgroup.centralizer {rGL}) = 720 := by
  rw [card_inf_centralizer]
  exact centCountCheck_spec.1

private theorem card_C_rA :
    Nat.card ↥(omegaMinusTwo 2 ⊓ Subgroup.centralizer {rAGL}) = 576 := by
  rw [card_inf_centralizer]
  exact centCountCheck_spec.2.1

private theorem card_C_rB :
    Nat.card ↥(omegaMinusTwo 2 ⊓ Subgroup.centralizer {rBGL}) = 96 := by
  rw [card_inf_centralizer]
  exact centCountCheck_spec.2.2

private theorem inf_centralizer_conj {h : GL6} (hh : h ∈ omegaMinusTwo 2) (x : GL6) :
    omegaMinusTwo 2 ⊓ Subgroup.centralizer {h * x * h⁻¹} =
      (omegaMinusTwo 2 ⊓ Subgroup.centralizer {x}).map (MulAut.conj h).toMonoidHom := by
  ext z
  simp only [Subgroup.mem_inf, Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨hz, hzc⟩
    refine ⟨h⁻¹ * z * h, ⟨mul_mem (mul_mem (inv_mem hh) hz) hh, ?_⟩, by group⟩
    calc h⁻¹ * z * h * x = h⁻¹ * (z * (h * x * h⁻¹)) * h := by group
      _ = h⁻¹ * ((h * x * h⁻¹) * z) * h := by rw [hzc]
      _ = x * (h⁻¹ * z * h) := by group
  · rintro ⟨w, ⟨hw, hwc⟩, rfl⟩
    refine ⟨mul_mem (mul_mem hh hw) (inv_mem hh), ?_⟩
    calc h * w * h⁻¹ * (h * x * h⁻¹) = h * (w * x) * h⁻¹ := by group
      _ = h * (x * w) * h⁻¹ := by rw [hwc]
      _ = h * x * h⁻¹ * (h * w * h⁻¹) := by group

private theorem card_inf_centralizer_conj {h : GL6} (hh : h ∈ omegaMinusTwo 2) (x : GL6) :
    Nat.card ↥(omegaMinusTwo 2 ⊓ Subgroup.centralizer {h * x * h⁻¹}) =
      Nat.card ↥(omegaMinusTwo 2 ⊓ Subgroup.centralizer {x}) := by
  rw [inf_centralizer_conj hh, Subgroup.card_map_of_injective (MulAut.conj h).injective]

private theorem subOneCode_lt (t : GL6) {k : ℕ} (hk : k < 64) : subOneCode (glCode t) k < 64 := by
  have h1 : (glCode t)[k]! < 64 := by
    rw [glCode, marr_get _ hk]
    exact vcode_lt _
  exact Nat.xor_lt_two_pow (n := 6) h1 hk

private theorem cdim6_ne_one_of_twoNZ {t : GL6} (h : twoNZ (glCode t) = true) :
    CaseII.cdim6 t ≠ 1 := by
  simp only [twoNZ, List.any_eq_true, List.mem_range, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨i, hi, hi0, j, hj, hj0, hji⟩ := h
  intro hrank
  have hrank' : Module.finrank (ZMod 2) ↥(LinearMap.range (Matrix.mulVecLin
      ((t : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) - 1))) = 1 := hrank
  obtain ⟨v, -, hv⟩ := (finrank_eq_one_iff' (K := ZMod 2) (V := ↥(LinearMap.range
    (Matrix.mulVecLin ((t : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) -
      1))))).mp hrank'
  have key : ∀ k < 64, subOneCode (glCode t) k ≠ 0 →
      cvec (subOneCode (glCode t) k) = (v : Fin 2 ⊕ Fin 2 ⊕ Fin 2 → ZMod 2) := by
    intro k hk hk0
    have hmem : cvec (subOneCode (glCode t) k) ∈ LinearMap.range (Matrix.mulVecLin
        ((t : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) - 1)) :=
      ⟨cvec k, by rw [Matrix.mulVecLin_apply, sub_one_mulVec_cvec t hk]; rfl⟩
    obtain ⟨c, hc⟩ := hv ⟨_, hmem⟩
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
    · rw [zero_smul] at hc
      exact absurd (congrArg Subtype.val hc).symm (cvec_ne_zero (subOneCode_lt t hk) hk0)
    · rw [one_smul] at hc
      exact (congrArg Subtype.val hc).symm
  apply hji
  have := (key j hj hj0).trans (key i hi hi0).symm
  rw [← vcode_cvec _ (subOneCode_lt t hj), this, vcode_cvec _ (subOneCode_lt t hi)]

private theorem cdim6_one : CaseII.cdim6 (1 : GL6) = 0 := by
  show Matrix.rank (((1 : GL6) : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2)
    (ZMod 2)) - 1) = 0
  rw [Units.val_one, sub_self, Matrix.rank_zero]

private theorem exists_refl_conj
    {a : GL6} (ha : a ∈ orthogonalMinus 2 (ZMod 2) 1 1)
    (ha1 : CaseII.cdim6 a = 1) : ∃ h ∈ omegaMinusTwo 2, h * rGL * h⁻¹ = a := by
  have h := reflOrbitCheck_holds
  simp only [reflOrbitCheck, Bool.and_eq_true, Array.all_eq_true] at h
  obtain ⟨hR, hall⟩ := h
  obtain ⟨k, hk, hke⟩ := exists_oEnum ha
  have hx := hall k hk
  rw [← getElem!_pos, hke] at hx
  simp only [Bool.or_eq_true, beq_iff_eq] at hx
  rcases hx with (hx | hx) | hx
  · exact exists_conj_of_lookup (x := rGL) hR hx
  · exfalso
    have h1 : a = 1 := isArrCode_glCode.injective (hx.trans isArrCode_glCode.one.symm)
    rw [h1, cdim6_one] at ha1
    exact absurd ha1 (by norm_num)
  · exact absurd ha1 (cdim6_ne_one_of_twoNZ hx)

private theorem exists_of_isCentInv {y : GL6} {e : Array ℕ}
    (h : isCentInv (omegaEnum ()) (glCode y) e = true) :
    ∃ c ∈ omegaMinusTwo 2 ⊓ Subgroup.centralizer {y}, c * c = 1 ∧ glCode c = e := by
  simp only [isCentInv, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hl, hcomm⟩, hinv⟩ := h
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hl
  obtain ⟨hks, hke⟩ := Enum.lookup_spec hk
  obtain ⟨x, hx⟩ := exists_glArr_eq hks
  have hxc : glCode (x : GL6) = e := hx.trans hke
  refine ⟨x, Subgroup.mem_inf.mpr ⟨x.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩, ?_, hxc⟩
  · rw [← commB_glCode, hxc]
    exact hcomm
  · apply isArrCode_glCode.injective
    rw [isArrCode_glCode.mul, hxc, isArrCode_glCode.one]
    exact hinv

private theorem glCode_commutator {x y : GL6} (hx : x * x = 1) (hy : y * y = 1) :
    glCode ⁅x, y⁆ = commArr (glCode x) (glCode y) := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  rw [commutatorElement_def, hxi, hyi, commArr, isArrCode_glCode.mul, isArrCode_glCode.mul,
    isArrCode_glCode.mul]

private theorem commutator_le_of_relIndex_two {G : Type*} [Group G] {C D : Subgroup G}
    (h : D.relIndex C = 2) : ⁅C, C⁆ ≤ D := by
  rw [Subgroup.commutator_le]
  intro g₁ h₁ g₂ h₂
  have hidx : (D.subgroupOf C).index = 2 := h
  have key : ∀ a b : ↥C, a * b ∈ D.subgroupOf C ↔ (a ∈ D.subgroupOf C ↔ b ∈ D.subgroupOf C) :=
    fun a b => Subgroup.mul_mem_iff_of_index_two hidx
  have hm : ⁅(⟨g₁, h₁⟩ : ↥C), ⟨g₂, h₂⟩⁆ ∈ D.subgroupOf C := by
    rw [commutatorElement_def, key, key, key, inv_mem_iff, inv_mem_iff]
    tauto
  exact Subgroup.mem_subgroupOf.mp hm

private theorem omClassB_tree :
    conjTreeOK (omClassB ()) (genA6 ()) (genA6Inv ()) (marr rBMat) = true :=
  omClassCheck_spec.2.1

private theorem a6_spec :
    (∀ x ∈ ⁅omegaMinusTwo 2 ⊓ Subgroup.centralizer {rGL},
        omegaMinusTwo 2 ⊓ Subgroup.centralizer {rGL}⁆, x * x = 1 → x ≠ 1 →
        ∃ g ∈ omegaMinusTwo 2, g * rBGL * g⁻¹ = x) ∧
      ∃ w₁ ∈ ⁅omegaMinusTwo 2 ⊓ Subgroup.centralizer {rGL},
          omegaMinusTwo 2 ⊓ Subgroup.centralizer {rGL}⁆,
        ∃ w₂ ∈ ⁅omegaMinusTwo 2 ⊓ Subgroup.centralizer {rGL},
          omegaMinusTwo 2 ⊓ Subgroup.centralizer {rGL}⁆,
          ∀ t ∈ orthogonalMinus 2 (ZMod 2) 1 1, t * w₁ = w₁ * t → t * w₂ = w₂ * t →
            t = 1 ∨ t = rGL := by
  have h := a6Check_holds
  simp only [a6Check, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hc, hd1⟩, hd2⟩, henum⟩, hsize⟩, hinvs⟩ := h
  obtain ⟨c, hcC, hc2, hcc⟩ := exists_of_isCentInv (y := rGL) hc
  obtain ⟨d1, hd1C, hd12, hd1c⟩ := exists_of_isCentInv (y := rGL) hd1
  obtain ⟨d2, hd2C, hd22, hd2c⟩ := exists_of_isCentInv (y := rGL) hd2
  set C := omegaMinusTwo 2 ⊓ Subgroup.centralizer {rGL}
  let s : ℕ → GL6 := fun i => if i = 0 then ⁅c, d1⁆ else ⁅c, d2⁆
  have hgs : ∀ j < (a6Gens ()).size, (a6Gens ())[j]! = glCode (s j) := by
    intro j hj
    have h2 : (a6Gens ()).size = 2 := rfl
    rw [h2] at hj
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
    · show commArr (marr a6cMat) (marr a6d1Mat) = glCode ⁅c, d1⁆
      rw [glCode_commutator hc2 hd12, hcc, hd1c]
    · show commArr (marr a6cMat) (marr a6d2Mat) = glCode ⁅c, d2⁆
      rw [glCode_commutator hc2 hd22, hcc, hd2c]
  have hs_mem : ∀ j, s j ∈ ⁅C, C⁆ := by
    intro j
    simp only [s]
    split_ifs
    · exact Subgroup.commutator_mem_commutator hcC hd1C
    · exact Subgroup.commutator_mem_commutator hcC hd2C
  set D := Subgroup.closure (s '' Set.Iio (a6Gens ()).size)
  have hDle : D ≤ ⁅C, C⁆ := by
    rw [Subgroup.closure_le]
    rintro _ ⟨j, -, rfl⟩
    exact hs_mem j
  have hCC : ⁅C, C⁆ ≤ C := by
    rw [Subgroup.commutator_le]
    intro g₁ h₁ g₂ h₂
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂)
  have hcardD : Nat.card D = 360 := by
    rw [card_closure_eq_of_enumOK isArrCode_glCode hgs henum, hsize]
  have hrel : D.relIndex C = 2 := by
    have := Subgroup.relIndex_mul_card (H := D) (K := C)
    rw [inf_of_le_left (hDle.trans hCC), hcardD, card_C_r] at this
    omega
  have hle : ⁅C, C⁆ ≤ D := commutator_le_of_relIndex_two hrel
  refine ⟨fun x hx hx2 hx1 => ?_, s 0, hs_mem 0, s 1, hs_mem 1, fun t ht ht1 ht2 => ?_⟩
  · obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp
      ((CFSG.ClassicalInvolution.Sp62Rec.Z6NA.mem_closure_iff_isSome isArrCode_glCode hgs henum
        x).mp (hle hx))
    obtain ⟨hks, hke⟩ := Enum.lookup_spec hk
    have hx' := hinvs k hks
    rw [← getElem!_pos, hke] at hx'
    simp only [Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq, beq_eq_false_iff_ne] at hx'
    have hsq : compA (glCode x) (glCode x) = idA () := by
      rw [← isArrCode_glCode.mul, hx2, isArrCode_glCode.one]
    have hne : glCode x ≠ idA () := by
      rw [← isArrCode_glCode.one]
      exact fun h => hx1 (isArrCode_glCode.injective h)
    rcases hx' with (hx' | hx') | hx'
    · exact absurd hsq hx'
    · exact absurd hx' hne
    · exact exists_conj_of_lookup (x := rBGL) omClassB_tree hx'
  · have h := a6CentCheck_holds
    simp only [a6CentCheck, Array.all_eq_true] at h
    obtain ⟨k, hk, hke⟩ := exists_oEnum ht
    have hx := h k hk
    rw [← getElem!_pos, hke] at hx
    have hc1 : commB (glCode t) (a6Gens ())[0]! = true := by
      rw [hgs 0 (by decide)]
      exact (commB_glCode _ _).mpr ht1
    have hc2' : commB (glCode t) (a6Gens ())[1]! = true := by
      rw [hgs 1 (by decide)]
      exact (commB_glCode _ _).mpr ht2
    rw [hc1, hc2'] at hx
    simp only [Bool.and_self, Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq] at hx
    rcases hx with hx | hx
    · exact Or.inl (isArrCode_glCode.injective (hx.trans isArrCode_glCode.one.symm))
    · exact Or.inr (isArrCode_glCode.injective hx)

private theorem glCode_pow (x : GL6) (m : ℕ) : glCode (x ^ m) = powA (glCode x) m := by
  induction m with
  | zero =>
    rw [pow_zero, isArrCode_glCode.one]
    rfl
  | succ m ih =>
    rw [pow_succ, isArrCode_glCode.mul, ih]
    rfl

section Closure

variable (S : GL6 → Prop)
  (hmul : ∀ a b, S a → S b → S (a * b))
  (hconj : ∀ c ∈ omegaMinusTwo 2 ⊓ Subgroup.centralizer {rAGL}, c * c = 1 →
    ∀ a, S a → S (c * a * c))

include hmul in
private theorem S_pow {z : GL6} (hz : S z) (m : ℕ) : S (z ^ (m + 1)) := by
  induction m with
  | zero => rwa [zero_add, pow_one]
  | succ m ih =>
    rw [pow_succ]
    exact hmul _ _ ih hz

include hmul in
private theorem powInvol_spec {z : GL6} (hz : S z)
    (h : powInvol (idA ()) (marr rAMat) (glCode z) = true) :
    ∃ u, S u ∧ u * u = 1 ∧ u ≠ 1 ∧ u ≠ rAGL := by
  simp only [powInvol, List.any_eq_true, List.mem_range, Bool.and_eq_true, Bool.not_eq_true',
    beq_iff_eq, beq_eq_false_iff_ne] at h
  obtain ⟨m, -, ⟨h2, h1⟩, hy⟩ := h
  refine ⟨z ^ (m + 1), S_pow S hmul hz m, ?_, ?_, ?_⟩
  · apply isArrCode_glCode.injective
    rw [isArrCode_glCode.mul, glCode_pow, h2, isArrCode_glCode.one]
  · intro h
    apply h1
    rw [← glCode_pow, h, isArrCode_glCode.one]
  · intro h
    apply hy
    rw [← glCode_pow, h]
    rfl

private theorem stepA_spec {c z : GL6} :
    glCode (c * z * c * z ^ 11) = stepA (glCode c) (glCode z) := by
  rw [stepA, isArrCode_glCode.mul, isArrCode_glCode.mul, isArrCode_glCode.mul, glCode_pow]

include hmul hconj in
private theorem S_step {c z : GL6} (hc : c ∈ omegaMinusTwo 2 ⊓ Subgroup.centralizer {rAGL})
    (hc2 : c * c = 1) (hz : S z) : S (c * z * c * z ^ 11) :=
  hmul _ _ (hconj c hc hc2 z hz) (S_pow S hmul hz 10)

include hmul hconj in
private theorem good1_spec {es : List (Array ℕ)}
    (hes : ∀ e ∈ es, ∃ c ∈ omegaMinusTwo 2 ⊓ Subgroup.centralizer {rAGL}, c * c = 1 ∧
      glCode c = e)
    {z : GL6} (hz : S z) (h : good1 (idA ()) (marr rAMat) es (glCode z) = true) :
    ∃ u, S u ∧ u * u = 1 ∧ u ≠ 1 ∧ u ≠ rAGL := by
  simp only [good1, Bool.or_eq_true, List.any_eq_true] at h
  rcases h with h | ⟨e, he, h⟩
  · exact powInvol_spec S hmul hz h
  · obtain ⟨c, hc, hc2, rfl⟩ := hes e he
    rw [← stepA_spec] at h
    exact powInvol_spec S hmul (S_step S hmul hconj hc hc2 hz) h

include hmul hconj in
private theorem good2_spec {es : List (Array ℕ)}
    (hes : ∀ e ∈ es, ∃ c ∈ omegaMinusTwo 2 ⊓ Subgroup.centralizer {rAGL}, c * c = 1 ∧
      glCode c = e)
    {z : GL6} (hz : S z) (h : good2 (idA ()) (marr rAMat) es (glCode z) = true) :
    ∃ u, S u ∧ u * u = 1 ∧ u ≠ 1 ∧ u ≠ rAGL := by
  simp only [good2, Bool.or_eq_true, List.any_eq_true] at h
  rcases h with h | ⟨e, he, h⟩
  · exact good1_spec S hmul hconj hes hz h
  · obtain ⟨c, hc, hc2, rfl⟩ := hes e he
    rw [← stepA_spec] at h
    exact good1_spec S hmul hconj hes (S_step S hmul hconj hc hc2 hz) h

include hmul hconj in
private theorem exists_invol
    {z : GL6} (hz : z ∈ omegaMinusTwo 2 ⊓ Subgroup.centralizer {rAGL}) (hSz : S z)
    (hz1 : z ≠ 1) (hzr : z ≠ rAGL) : ∃ u, S u ∧ u * u = 1 ∧ u ≠ 1 ∧ u ≠ rAGL := by
  have h := closureCheck_holds
  simp only [closureCheck, Bool.and_eq_true, List.all_eq_true, Array.all_eq_true] at h
  obtain ⟨hes, hall⟩ := h
  have hes' : ∀ e ∈ [marr e1Mat, marr e2Mat], ∃ c ∈ omegaMinusTwo 2 ⊓
      Subgroup.centralizer {rAGL}, c * c = 1 ∧ glCode c = e :=
    fun e he => exists_of_isCentInv (y := rAGL) (hes e he)
  obtain ⟨k, hk, hke⟩ := exists_omegaEnum (Subgroup.mem_inf.mp hz).1
  have hx := hall k hk
  rw [← getElem!_pos, hke] at hx
  have hc : commB (glCode z) (glCode rAGL) = true :=
    (commB_glCode _ _).mpr (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hz).2)
  have hc' : commB (glCode z) (marr rAMat) = true := hc
  rw [hc'] at hx
  simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq] at hx
  rcases hx with (hx | hx) | hx
  · exact absurd (isArrCode_glCode.injective (hx.trans isArrCode_glCode.one.symm)) hz1
  · have hx' : glCode z = glCode rAGL := hx
    exact absurd (isArrCode_glCode.injective hx') hzr
  · exact good2_spec S hmul hconj hes' hSz hx

end Closure

private theorem card_alt6 : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

private theorem alt6_eq_top_of_index_le_five (H : Subgroup ↥(alternatingGroup (Fin 6)))
    (hH : H.index ≤ 5) : H = ⊤ := by
  classical
  haveI : IsSimpleGroup ↥(alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by simp)
  by_contra hne
  let φ := MulAction.toPermHom ↥(alternatingGroup (Fin 6)) (↥(alternatingGroup (Fin 6)) ⧸ H)
  have hker : φ.ker = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with h | h
    · exact h
    · exfalso
      apply hne
      refine eq_top_iff.mpr fun g _ => ?_
      have h1 : φ g = 1 := by
        rw [← MonoidHom.mem_ker, h]
        trivial
      have h2 : (QuotientGroup.mk g : ↥(alternatingGroup (Fin 6)) ⧸ H) = QuotientGroup.mk 1 := by
        have := congrArg (fun p : Equiv.Perm (↥(alternatingGroup (Fin 6)) ⧸ H) =>
          p (QuotientGroup.mk (1 : ↥(alternatingGroup (Fin 6))))) h1
        simpa [φ, MulAction.toPermHom_apply, MulAction.toPerm_apply] using this
      have h4 := QuotientGroup.eq.mp h2
      simpa using H.inv_mem h4
  have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hker
  have h1 := Nat.card_le_card_of_injective φ hinj
  have : Fintype (↥(alternatingGroup (Fin 6)) ⧸ H) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card (α := Equiv.Perm (↥(alternatingGroup (Fin 6)) ⧸ H)),
    Fintype.card_perm, ← Nat.card_eq_fintype_card, card_alt6] at h1
  have h2 : Nat.card (↥(alternatingGroup (Fin 6)) ⧸ H) ≤ 5 := hH
  have h3 : (Nat.card (↥(alternatingGroup (Fin 6)) ⧸ H)).factorial ≤ Nat.factorial 5 :=
    Nat.factorial_le h2
  have h5 : Nat.factorial 5 = 120 := rfl
  omega

private theorem conj_injective_alt6 :
    Function.Injective (MulAut.conj : ↥(alternatingGroup (Fin 6)) →*
      MulAut ↥(alternatingGroup (Fin 6))) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  have hc : g ∈ Subgroup.center ↥(alternatingGroup (Fin 6)) := by
    rw [Subgroup.mem_center_iff]
    intro x
    have h1 := congrArg (fun φ : MulAut ↥(alternatingGroup (Fin 6)) => φ x)
      (MonoidHom.mem_ker.mp hg)
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    calc x * g = g * x * g⁻¹ * g := by rw [h1]
      _ = g * x := by group
  rw [alternatingGroup.center_eq_bot (by simp)] at hc
  exact hc

private theorem not_card_range {X : Type*} [Group X] [Finite X]
    (f : X →* MulAut ↥(alternatingGroup (Fin 6))) (hX : Nat.card X = 576)
    (hR : 288 ≤ Nat.card f.range) : False := by
  obtain ⟨hfin, hAut⟩ :=
    CFSG.HardMathSupport.Timmesfeld.Balance.Alt.finite_and_card_mulAut_alternatingGroup_six_le
  have hRidx := Subgroup.card_mul_index f.range
  have hidx : f.range.index ≤ 5 := by
    by_contra hcon
    have hcon' : 6 ≤ f.range.index := by omega
    have : 288 * 6 ≤ Nat.card f.range * f.range.index := Nat.mul_le_mul hR hcon'
    omega
  set φ := (MulAut.conj : ↥(alternatingGroup (Fin 6)) →* MulAut ↥(alternatingGroup (Fin 6)))
  have hcomap : (f.range.comap φ).index ≤ 5 := by
    rw [Subgroup.index_comap]
    calc f.range.relIndex φ.range ≤ f.range.relIndex ⊤ :=
          Subgroup.relIndex_le_of_le_right le_top
            (by rw [Subgroup.relIndex_top_right]; exact Subgroup.index_ne_zero_of_finite)
      _ = f.range.index := Subgroup.relIndex_top_right _
      _ ≤ 5 := hidx
  have htop := alt6_eq_top_of_index_le_five _ hcomap
  have hle : φ.range ≤ f.range := by
    rintro _ ⟨g, rfl⟩
    have : g ∈ f.range.comap φ := htop ▸ Subgroup.mem_top g
    exact this
  have h360 : Nat.card φ.range = 360 := by
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective conj_injective_alt6,
      Subgroup.card_top, card_alt6]
  have hdvd1 : 360 ∣ Nat.card f.range := h360 ▸ Subgroup.card_dvd_of_le hle
  have hdvd2 : Nat.card f.range ∣ 576 := hX ▸ Subgroup.card_range_dvd f
  have := Nat.dvd_trans hdvd1 hdvd2
  norm_num at this

end CaseIIClassAux

open CaseIIClassAux CFSG.CGT.Foote82.OmegaSix CFSG.RankThree.PartTwo CFSG.PGLModel
open scoped commutatorElement

theorem caseIIG1_holds :
    CaseIIG1 := by
  intro a ha _ ha1
  obtain ⟨h, hh, rfl⟩ := exists_refl_conj ha ha1
  refine ⟨?_, ?_, ?_⟩
  · intro b hb _ hb1
    obtain ⟨h', hh', rfl⟩ := exists_refl_conj hb hb1
    exact ⟨h' * h⁻¹, mul_mem hh' (inv_mem hh), by group⟩
  · rw [card_inf_centralizer_conj hh, card_C_r]
  · intro g hg hcomm
    obtain ⟨-, w₁, hw₁, w₂, hw₂, hcent⟩ := a6_spec
    have hmap : ∀ w ∈ ⁅omegaMinusTwo 2 ⊓ Subgroup.centralizer {rGL},
        omegaMinusTwo 2 ⊓ Subgroup.centralizer {rGL}⁆,
        h * w * h⁻¹ ∈ ⁅omegaMinusTwo 2 ⊓ Subgroup.centralizer {h * rGL * h⁻¹},
          omegaMinusTwo 2 ⊓ Subgroup.centralizer {h * rGL * h⁻¹}⁆ := by
      intro w hw
      rw [inf_centralizer_conj hh, ← Subgroup.map_commutator]
      exact ⟨w, hw, rfl⟩
    have key : ∀ w ∈ ⁅omegaMinusTwo 2 ⊓ Subgroup.centralizer {rGL},
        omegaMinusTwo 2 ⊓ Subgroup.centralizer {rGL}⁆,
        h⁻¹ * g * h * w = w * (h⁻¹ * g * h) := by
      intro w hw
      have h1 := hcomm _ (hmap w hw)
      calc h⁻¹ * g * h * w = h⁻¹ * (g * (h * w * h⁻¹)) * h := by group
        _ = h⁻¹ * ((h * w * h⁻¹) * g) * h := by rw [h1]
        _ = w * (h⁻¹ * g * h) := by group
    have hhO := omegaMinusTwo_le_orthogonalMinus hh
    have ht : h⁻¹ * g * h ∈ orthogonalMinus 2 (ZMod 2) 1 1 :=
      mul_mem (mul_mem (inv_mem hhO) hg) hhO
    rcases hcent _ ht (key w₁ hw₁) (key w₂ hw₂) with h1 | h1
    · left
      calc g = h * (h⁻¹ * g * h) * h⁻¹ := by group
        _ = 1 := by rw [h1]; group
    · right
      calc g = h * (h⁻¹ * g * h) * h⁻¹ := by group
        _ = h * rGL * h⁻¹ := by rw [h1]

theorem caseIIG9_holds :
    CaseIIG9 := by
  intro y hy hy2 hcard f hf
  have hyΩ : y ∈ omegaMinusTwo 2 := (Subgroup.mem_inf.mp hy).1
  have hyy : y * y = 1 := by
    have h := pow_orderOf_eq_one y
    rwa [hy2, pow_two] at h
  have hy1 : y ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hy2
    exact absurd hy2 (by norm_num)
  obtain ⟨g, hg, hgy⟩ : ∃ g ∈ omegaMinusTwo 2, g * rAGL * g⁻¹ = y := by
    obtain ⟨g, hg, hA | hB⟩ := exists_conj_rep_omega hyΩ hyy hy1
    · exact ⟨g, hg, hA⟩
    · exfalso
      have h96 : Nat.card ↥(omegaMinusTwo 2 ⊓ Subgroup.centralizer {y}) = 96 := by
        rw [← hB, card_inf_centralizer_conj hg, card_C_rB]
      omega
  have hyK : (⟨y, hy⟩ : ↥(omegaMinusTwo 2 ⊓ Subgroup.centralizer {y})) ∈ f.ker :=
    f.mem_ker.mpr hf
  rcases em (∃ z ∈ f.ker, z ≠ 1 ∧ z ≠ ⟨y, hy⟩) with ⟨z, hzK, hz1, hzy⟩ | hK
  ·
    let S : GL6 → Prop := fun w => ∃ k ∈ f.ker,
      ((k : ↥(omegaMinusTwo 2 ⊓ Subgroup.centralizer {y})) : GL6) = g * w * g⁻¹
    have hmul : ∀ a b, S a → S b → S (a * b) := by
      rintro a b ⟨k₁, hk₁, he₁⟩ ⟨k₂, hk₂, he₂⟩
      refine ⟨k₁ * k₂, mul_mem hk₁ hk₂, ?_⟩
      rw [Subgroup.coe_mul, he₁, he₂]
      group
    have hconj : ∀ c ∈ omegaMinusTwo 2 ⊓ Subgroup.centralizer {rAGL}, c * c = 1 →
        ∀ a, S a → S (c * a * c) := by
      rintro c hc hc2 a ⟨k, hk, he⟩
      have hc' : g * c * g⁻¹ ∈ omegaMinusTwo 2 ⊓ Subgroup.centralizer {y} := by
        rw [← hgy, inf_centralizer_conj hg]
        exact ⟨c, hc, rfl⟩
      have hmem := f.normal_ker.conj_mem k hk ⟨g * c * g⁻¹, hc'⟩
      refine ⟨_, hmem, ?_⟩
      have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc2
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, he]
      calc g * c * g⁻¹ * (g * a * g⁻¹) * (g * c * g⁻¹)⁻¹ = g * (c * a * c⁻¹) * g⁻¹ := by group
        _ = g * (c * a * c) * g⁻¹ := by rw [hci]
    have hz₀ : g⁻¹ * (z : GL6) * g ∈ omegaMinusTwo 2 ⊓ Subgroup.centralizer {rAGL} := by
      have hzΩ : (z : GL6) ∈ omegaMinusTwo 2 := (Subgroup.mem_inf.mp z.2).1
      have hzc : (z : GL6) * y = y * (z : GL6) :=
        Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp z.2).2
      refine Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem (inv_mem hg) hzΩ) hg,
        Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      calc g⁻¹ * (z : GL6) * g * rAGL = g⁻¹ * ((z : GL6) * (g * rAGL * g⁻¹)) * g := by group
        _ = g⁻¹ * ((z : GL6) * y) * g := by rw [hgy]
        _ = g⁻¹ * (y * (z : GL6)) * g := by rw [hzc]
        _ = g⁻¹ * ((g * rAGL * g⁻¹) * (z : GL6)) * g := by rw [hgy]
        _ = rAGL * (g⁻¹ * (z : GL6) * g) := by group
    have hSz : S (g⁻¹ * (z : GL6) * g) := ⟨z, hzK, by group⟩
    have hz₀1 : g⁻¹ * (z : GL6) * g ≠ 1 := by
      intro h
      apply hz1
      apply Subtype.ext
      calc (z : GL6) = g * (g⁻¹ * (z : GL6) * g) * g⁻¹ := by group
        _ = 1 := by rw [h]; group
    have hz₀r : g⁻¹ * (z : GL6) * g ≠ rAGL := by
      intro h
      apply hzy
      apply Subtype.ext
      calc (z : GL6) = g * (g⁻¹ * (z : GL6) * g) * g⁻¹ := by group
        _ = g * rAGL * g⁻¹ := by rw [h]
        _ = y := hgy
    obtain ⟨u, ⟨k, hk, hke⟩, hu2, hu1, hur⟩ := exists_invol S hmul hconj hz₀ hSz hz₀1 hz₀r
    have hkk : k * k = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, hke, Subgroup.coe_one]
      calc g * u * g⁻¹ * (g * u * g⁻¹) = g * (u * u) * g⁻¹ := by group
        _ = 1 := by rw [hu2]; group
    have hk1 : k ≠ 1 := by
      intro h
      apply hu1
      have h' : g * u * g⁻¹ = 1 := by rw [← hke, h, Subgroup.coe_one]
      calc u = g⁻¹ * (g * u * g⁻¹) * g := by group
        _ = 1 := by rw [h']; group
    have hky : (⟨y, hy⟩ : ↥(omegaMinusTwo 2 ⊓ Subgroup.centralizer {y})) ≠ k := by
      intro h
      apply hur
      have h' : g * u * g⁻¹ = g * rAGL * g⁻¹ := by rw [← hke, ← h, hgy]
      calc u = g⁻¹ * (g * u * g⁻¹) * g := by group
        _ = g⁻¹ * (g * rAGL * g⁻¹) * g := by rw [h']
        _ = rAGL := by group
    have hcomm : (⟨y, hy⟩ : ↥(omegaMinusTwo 2 ⊓ Subgroup.centralizer {y})) * k =
        k * ⟨y, hy⟩ := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      exact (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp k.2).2).symm
    have hyy' : (⟨y, hy⟩ : ↥(omegaMinusTwo 2 ⊓ Subgroup.centralizer {y})) * ⟨y, hy⟩ = 1 :=
      Subtype.ext hyy
    have hy1' : (⟨y, hy⟩ : ↥(omegaMinusTwo 2 ⊓ Subgroup.centralizer {y})) ≠ 1 :=
      fun h => hy1 (congrArg Subtype.val h)
    exact CFSG.Asc75.two_le_pRank_of_pair hyy' hkk hcomm hy1' hk1 hky hyK hk
  · exfalso
    have hK' : ∀ z ∈ f.ker, z ≠ 1 → z = ⟨y, hy⟩ :=
      fun z hz h1 => by_contra fun h2 => hK ⟨z, hz, h1, h2⟩
    have hKcard : Nat.card f.ker ≤ 2 := by
      have hinj : Function.Injective
          (fun z : f.ker => decide ((z : ↥(omegaMinusTwo 2 ⊓ Subgroup.centralizer {y})) = 1)) := by
        intro z₁ z₂ h12
        by_cases h1 : (z₁ : ↥(omegaMinusTwo 2 ⊓ Subgroup.centralizer {y})) = 1 <;>
          by_cases h2 : (z₂ : ↥(omegaMinusTwo 2 ⊓ Subgroup.centralizer {y})) = 1
        · exact Subtype.ext (h1.trans h2.symm)
        · simp [h1, h2] at h12
        · simp [h1, h2] at h12
        · exact Subtype.ext ((hK' _ z₁.2 h1).trans (hK' _ z₂.2 h2).symm)
      have := Nat.card_le_card_of_injective _ hinj
      simpa using this
    have hkr := Subgroup.card_ker_mul_card_range f
    rw [hcard] at hkr
    have hpos : 0 < Nat.card f.ker := Nat.card_pos
    have hR : 288 ≤ Nat.card f.range := by
      rcases (by omega : Nat.card f.ker = 1 ∨ Nat.card f.ker = 2) with h | h <;>
        rw [h] at hkr <;> omega
    exact not_card_range f hcard hR

theorem caseIIG12_holds :
    CaseIIG12 := by
  intro a ha _ ha1 y hy hy2 hcard x hx hx2
  obtain ⟨h, hh, rfl⟩ := exists_refl_conj ha ha1
  have hyy : y * y = 1 := by
    have h := pow_orderOf_eq_one y
    rwa [hy2, pow_two] at h
  have hy1 : y ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hy2
    exact absurd hy2 (by norm_num)
  obtain ⟨k, hk, rfl⟩ : ∃ k ∈ omegaMinusTwo 2, k * rBGL * k⁻¹ = y := by
    obtain ⟨k, hk, hA | hB⟩ := exists_conj_rep_omega hy hyy hy1
    · exfalso
      apply hcard
      rw [← hA, card_inf_centralizer_conj hk, card_C_rA]
    · exact ⟨k, hk, hB⟩
  rw [inf_centralizer_conj hh, ← Subgroup.map_commutator] at hx
  obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hx2 ⊢
  have hxx : h * x' * h⁻¹ * (h * x' * h⁻¹) = 1 := by
    have h1 := pow_orderOf_eq_one (h * x' * h⁻¹)
    rwa [hx2, pow_two] at h1
  have hx'2 : x' * x' = 1 := by
    calc x' * x' = h⁻¹ * (h * x' * h⁻¹ * (h * x' * h⁻¹)) * h := by group
      _ = 1 := by rw [hxx]; group
  have hx'1 : x' ≠ 1 := by
    rintro rfl
    rw [mul_one, mul_inv_cancel, orderOf_one] at hx2
    exact absurd hx2 (by norm_num)
  obtain ⟨k', hk', hk'x⟩ := a6_spec.1 x' hx' hx'2 hx'1
  refine ⟨h * k' * k⁻¹, mul_mem (mul_mem hh hk') (inv_mem hk), ?_⟩
  rw [← hk'x]
  group

end CFSG.CGT.Foote82
