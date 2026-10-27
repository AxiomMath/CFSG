module

public import CFSG.Certificates.Kernel.HTD42QSound
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HTD42Gen
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.D4TwoPlane
public import Certificates.Certificate9415
import CFSG.Certificates.Kernel.D4PlaneSound
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.Cover
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport.FamilyProved
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeA3pSurvivor
public import CFSG.LocalAnalysis.AGLEmbedding.GapROneBS
public import CFSG.LocalAnalysis.AGLEmbedding.J3InSitu
public import CFSG.LocalAnalysis.AGLEmbedding.J3MSide
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevOuterD42Spec
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3CoverGenAssembly
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3FourGenData
public import CFSG.LocalAnalysis.AGLEmbedding.MonomialWeightsOne
public import CFSG.LocalAnalysis.AGLEmbedding.ReeData
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264sTD42
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I131T4
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U52
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS03KD264
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.CatalogToCover
public import CFSG.LocalAnalysis.GLTheoremA.S4S.I145GW
public import CFSG.LocalAnalysis.GLTheoremA.S4S.KData
public import CFSG.LocalAnalysis.GLTheoremA.S6.InputsAlt72
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1Frontier3
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotXiCaseLTorus
public import CFSG.Milestones.CL_LIT_Gorenstein_Walter_L_balance
public import CFSG.Quasithin.Recognition.CertTrialityCheckInputs
public import CFSG.RankThree.PartOne.FOCD.G2OddQPlus
public import CFSG.RankThree.PartOne.FOCD.PRank
public import CFSG.RankThree.PartOne.KC.UnitaryDefining
public import CFSG.RankThree.PartOne.N143.LowTwoRankSplit
public import CFSG.RankThree.PartOne.N143.SectionCenter
public import CFSG.RankThree.PartOne.N143.SectionRankBound
public import CFSG.RankThree.PartOne.N143.SectionRankProof
public import CFSG.RankThree.PartOne.N143.SectionRankSplit
public import CFSG.RankThree.PartOne.SEITZ11.G2OddFinal
public import CFSG.RankThree.PartOne.SEITZ7.D4Wire
public import CFSG.RankThree.PartOne.SEITZ7.SlPair
public import CFSG.RankThree.PartOne.SEITZ7.SzPairK
public import CFSG.RankThree.PartTwo.Sec14.Item148Steps
public import CFSG.RankThree.PartTwo.Sec19.SeitzScopeProofExc
public import CFSG.RankThree.PartTwo.Sec19.SeitzScopeProofSec19
public import CFSG.RankThree.PartTwo.Sec19.SeitzScopeProofSec4
public import CFSG.RankThree.PartTwo.Sec19.Step1914Split
public import CFSG.RankThree.PartTwo.Sec4.Item4Res6ProofL364
public import CFSG.RankThree.PartTwo.Sec4.Item4Res6ProofSeitzOther
public import CFSG.RankThree.PartTwo.Sec4.Item4Res6ProofSeitzRest
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434RowsProofSeitzSz

public section

namespace CFSG.KC.HTD42G

open CFSG.Quasithin CFSG.Open CFSG.AGLEmbedding.D4Two CFSG.KC.D4PlaneP CFSG.KC.HTD42Q
open CFSG.RankThree.PartTwo.Sec4.Item434D42 (lineGroup)
open CFSG.AGLEmbedding.ChevOuter (Pr frobPow phiT phiT_pow_three phiT_ne_conj coe_phiT_pow
  toMat_frobPow rep_mul rep_wordP rep_ext rep_one rep_oneP wordAut)
open CFSG.LocalAnalysis.GLTheoremA (card_sup_mul_card_inf_of_le_normalizer)
open CFSG.LocalAnalysis.GLTheoremA.HTD42 (sup_zpowers_card_nine fixed_of_sup_zpowers)

theorem mem_zpowers_cube {G : Type*} [Group G] {x y : G} (hx : x ^ 3 = 1)
    (hy : y ∈ Subgroup.zpowers x) : y = 1 ∨ y = x ∨ y = x * x := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  have h3 : x ^ ((3 : ℕ) : ℤ) = 1 := by rw [zpow_natCast]; exact hx
  have hk := zpow_eq_zpow_emod k h3
  have hr0 : 0 ≤ k % ((3 : ℕ) : ℤ) := Int.emod_nonneg k (by norm_num)
  have hr3 : k % ((3 : ℕ) : ℤ) < 3 := Int.emod_lt_of_pos k (by norm_num)
  rw [hk]
  obtain ⟨r, hr⟩ : ∃ r : ℕ, k % ((3 : ℕ) : ℤ) = r := ⟨(k % ((3 : ℕ) : ℤ)).toNat, by omega⟩
  rw [hr]
  have hr' : r < 3 := by omega
  interval_cases r
  · left; simp
  · right; left; simp
  · right; right; simp [zpow_natCast, pow_two]

theorem mem_sup_zpowers {G : Type*} [Group G] {A : Subgroup G} {ξ : G}
    (hξ : ξ ∈ Subgroup.normalizer (A : Set G)) {x : G} (hx : x ∈ A ⊔ Subgroup.zpowers ξ) :
    ∃ n ∈ A, ∃ k : ℤ, x = n * ξ ^ k := by
  have hk : ∀ k : ℤ, ∀ n ∈ A, ξ ^ k * n * (ξ ^ k)⁻¹ ∈ A := fun k n hn =>
    (Subgroup.mem_normalizer_iff.1 (zpow_mem hξ k) n).1 hn
  let S : Subgroup G :=
    { carrier := {x | ∃ n ∈ A, ∃ k : ℤ, x = n * ξ ^ k}
      mul_mem' := by
        rintro _ _ ⟨n, hn, k, rfl⟩ ⟨m, hm, l, rfl⟩
        refine ⟨n * (ξ ^ k * m * (ξ ^ k)⁻¹), A.mul_mem hn (hk k m hm), k + l, ?_⟩
        rw [zpow_add]
        group
      one_mem' := ⟨1, A.one_mem, 0, by simp⟩
      inv_mem' := by
        rintro _ ⟨n, hn, k, rfl⟩
        refine ⟨ξ ^ (-k) * n⁻¹ * (ξ ^ (-k))⁻¹, hk (-k) _ (A.inv_mem hn), -k, ?_⟩
        group }
  have hle : A ⊔ Subgroup.zpowers ξ ≤ S := by
    refine sup_le (fun n hn => ⟨n, hn, 0, by simp⟩) ?_
    rw [Subgroup.zpowers_le]
    exact ⟨1, A.one_mem, 1, by simp⟩
  exact hle hx

theorem mem_normalizer_of_cube {G : Type*} [Group G] {A : Subgroup G} {ξ : G} (hc : ξ ^ 3 = 1)
    (hcl : ∀ n ∈ A, ξ * n * ξ⁻¹ ∈ A) : ξ ∈ Subgroup.normalizer (A : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨hcl h, fun hm => ?_⟩
  have h3 := hcl _ (hcl _ hm)
  have e : ξ * (ξ * (ξ * h * ξ⁻¹) * ξ⁻¹) * ξ⁻¹ = h := by
    calc _ = ξ ^ 3 * h * (ξ ^ 3)⁻¹ := by simp only [pow_three, mul_assoc, mul_inv_rev]
      _ = h := by rw [hc, one_mul, inv_one, mul_one]
  rwa [e] at h3

theorem factorization_three (hA : Nat.card (MulAut lineGroup) = 3 * 211341312) :
    (Nat.card (MulAut lineGroup)).factorization 3 = 5 := by
  rw [hA]
  have h : (3 * 211341312 : ℕ) = 3 ^ 5 * 2609152 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num)]
  simp only [Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same]
  rw [Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem conj_injective (hZ : Subgroup.center lineGroup = ⊥) :
    Function.Injective (MulAut.conj : lineGroup →* MulAut lineGroup) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hgz : g ∈ Subgroup.center lineGroup := by
    rw [Subgroup.mem_center_iff]
    intro z
    have := congrArg (fun α : MulAut lineGroup => α z) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    exact (mul_inv_eq_iff_eq_mul.1 this).symm
  rw [hZ, Subgroup.mem_bot] at hgz
  exact hgz

theorem inv_fix {β : MulAut lineGroup} {z : lineGroup} (h : β z = z) : β⁻¹ z = z := by
  calc β⁻¹ z = β⁻¹ (β z) := by rw [h]
    _ = z := by rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]

theorem toMat_oneArr' : toMat oneArr = 1 := by
  unfold oneArr
  exact toMat_ofMat 1

theorem wordGL_mem_line (w : List ℕ) (hw : ∀ k ∈ w, k < 18) : wordGL w ∈ lineGroup := by
  unfold wordGL
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
  exact Subgroup.subset_closure ⟨k, hw k hk, rfl⟩

theorem lettersA : ∀ k ∈ wordA, k < 18 := by decide

theorem lettersB : ∀ k ∈ wordB, k < 18 := by decide

def aT : lineGroup := ⟨wordGL wordA, wordGL_mem_line wordA lettersA⟩

def bT : lineGroup := ⟨wordGL wordB, wordGL_mem_line wordB lettersB⟩

def PT : Subgroup lineGroup := Subgroup.closure {aT, bT}

def InnP : Subgroup (MulAut lineGroup) := PT.map MulAut.conj

theorem map_PT : PT.map lineGroup.subtype = sylowGroup := by
  rw [PT, MonoidHom.map_closure, Set.image_pair]
  rfl

theorem InnP_eq : InnP = Subgroup.closure {MulAut.conj aT, MulAut.conj bT} := by
  rw [InnP, PT, MonoidHom.map_closure, Set.image_pair]

theorem card_InnP (hZ : Subgroup.center lineGroup = ⊥) :
    Nat.card InnP = 81 := by
  rw [InnP, Subgroup.card_map_of_injective (conj_injective hZ),
    ← Subgroup.card_map_of_injective (Subgroup.subtype_injective lineGroup), map_PT]
  exact Certificates.certificate9415.1

theorem exists_PT {x : Array GF8} (hx : x ∈ sylowElems) :
    ∃ p ∈ PT, ((p : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) = toMat x := by
  obtain ⟨g, hg, hgx⟩ := exists_mem_of_mem_sylowElems x hx
  rw [← map_PT] at hg
  obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.1 hg
  exact ⟨p, hp, hgx⟩

theorem exists_sylowElems_of_PT {p : lineGroup} (hp : p ∈ PT) :
    ∃ x ∈ sylowElems, ((p : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) = toMat x := by
  have hg : (p : GL (Fin 8) GF8) ∈ sylowGroup := by
    rw [← map_PT]
    exact ⟨p, hp, rfl⟩
  exact exists_sylowElems_eq _ hg

theorem pow_three_of_arr {f : lineGroup} {u : Array GF8}
    (hf : ((f : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) = toMat u)
    (hc : mulArr u (mulArr u u) = oneArr) : f ^ 3 = 1 := by
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, Subgroup.coe_one, Units.val_one]
  rw [hf, pow_three, ← toMat_mulArr, ← toMat_mulArr, hc, toMat_oneArr']

theorem arr_eq_of_eq {f f' : lineGroup} {u v : Array GF8} (hu : u.size = 64) (hv : v.size = 64)
    (hf : ((f : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) = toMat u)
    (hf' : ((f' : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) = toMat v) (h : f = f') :
    u = v :=
  eq_of_toMat_eq hu hv (by rw [← hf, ← hf', h])

theorem rep_conj {A : Array GF8} (hs : A.size = 64) (g : lineGroup)
    (h : toMat A = ((g : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8)) :
    CFSG.AGLEmbedding.ChevOuter.Rep (A, 0) (MulAut.conj g) :=
  ⟨hs, (by decide : 0 < 3), g, h, by simp⟩

theorem fix_of_rep {y : Pr} {β : MulAut lineGroup} (hy : CFSG.AGLEmbedding.ChevOuter.Rep y β)
    {a : Array GF8} (hm : mulArr y.1 (frobPow y.2 a) = mulArr a y.1) (f : lineGroup)
    (hf : ((f : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) = toMat a) : β f = f := by
  obtain ⟨-, -, g, hg, rfl⟩ := hy
  have hmat : toMat y.1 * toMat (frobPow y.2 a) = toMat a * toMat y.1 := by
    rw [← toMat_mulArr, ← toMat_mulArr, hm]
  have hkey : g * (phiT ^ y.2) f = f * g := by
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul]
    rw [coe_phiT_pow, hf, ← toMat_frobPow, ← hg]
    exact hmat
  rw [MulAut.mul_apply, MulAut.conj_apply, hkey, mul_inv_cancel_right]

section Checks

variable {ls : List Nat} (hL : ∀ i < 18, packA (letterArr i) = ls.getD i 0)

include hL

theorem wordAut_cube {w : List ℕ} (h : cubeQ (wordQ ls w) = true) : wordAut w ^ 3 = 1 := by
  have h1 := rep_mul (rep_wordP w) (rep_mul (rep_wordP w) (rep_wordP w))
  rw [cube_wordP hL h] at h1
  rw [pow_three]
  exact rep_ext h1 rep_oneP rfl

theorem wordAut_outer {w : List ℕ} (h : Nat.beq (wordQ ls w).2 2 = true) (g : lineGroup) :
    wordAut w ≠ MulAut.conj g := by
  intro hg
  obtain ⟨-, -, h0, -, he⟩ := rep_wordP w
  rw [frob_wordP hL h, hg] at he
  have hc : phiT ^ 2 = MulAut.conj (h0⁻¹ * g) := by
    rw [map_mul, map_inv, he]
    group
  apply phiT_ne_conj ((h0⁻¹ * g) ^ 2)
  have h4 : phiT = phiT ^ 4 := by
    rw [show 4 = 1 + 3 by norm_num, pow_add, phiT_pow_three, mul_one, pow_one]
  rw [h4, show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hc, ← map_pow]

variable {es : List Nat} (hE : bfsOK (wordP ls wordA) (wordP ls wordB) bfsPar es = true)

include hE

theorem conj_gen {v : List ℕ} (hv : ∀ k ∈ v, k < 18) {i : ℕ}
    (h : eqQ (mulQ (wordQ ls xW) (wordP ls v, 0)) (mulQ (atP es i, 0) (wordQ ls xW)) = true) :
    wordAut xW * MulAut.conj (⟨wordGL v, wordGL_mem_line v hv⟩ : lineGroup) * (wordAut xW)⁻¹ ∈
      InnP := by
  have he := norm_sylow hL hE xW v i h
  obtain ⟨p, hp, hpx⟩ := exists_PT (sylowElemAt_mem i)
  have h1 := rep_mul (rep_wordP xW)
    (rep_conj (size_wordArr v) ⟨wordGL v, wordGL_mem_line v hv⟩ (coe_wordGL v).symm)
  have h2 := rep_mul (rep_conj (size_sylowElemAt i) p hpx.symm) (rep_wordP xW)
  rw [he] at h1
  rw [rep_ext h1 h2 rfl, mul_inv_cancel_right]
  exact Subgroup.mem_map_of_mem _ hp

theorem conj_InnP
    (hnA : eqQ (mulQ (wordQ ls xW) (wordP ls wordA, 0)) (mulQ (atP es 48, 0) (wordQ ls xW)) = true)
    (hnB : eqQ (mulQ (wordQ ls xW) (wordP ls wordB, 0)) (mulQ (atP es 54, 0) (wordQ ls xW)) = true) :
    ∀ n ∈ InnP, wordAut xW * n * (wordAut xW)⁻¹ ∈ InnP := by
  have hle : InnP ≤ InnP.comap (MulAut.conj (wordAut xW)).toMonoidHom := by
    conv_lhs => rw [InnP_eq]
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact conj_gen hL hE lettersA hnA
    · exact conj_gen hL hE lettersB hnB
  intro n hn
  exact hle hn

theorem fix_coset (hZ : Subgroup.center lineGroup = ⊥)
    (hP : planesQ (gensP es) = true)
    (hWa : witAll (wordQ ls xW) (gensP es) (es.take 40) = true)
    (hWb : witAll (wordQ ls xW) (gensP es) (es.drop 40) = true)
    {n : MulAut lineGroup} (hn : n ∈ InnP) (h3 : (n * wordAut xW) ^ 3 = 1) :
    ∃ F : Subgroup lineGroup, IsElemAbelian 3 F ∧ Nat.card F = 9 ∧
      ∀ z ∈ F, (n * wordAut xW) z = z := by
  obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.1 hn
  obtain ⟨x, hx, hpx⟩ := exists_sylowElems_of_PT hp
  have hr := rep_mul (rep_conj (CFSG.AGLEmbedding.D4Two.size_sylowElems x hx) p hpx.symm) (rep_wordP xW)
  have hy3 := rep_mul hr (rep_mul hr hr)
  rw [← pow_three, h3] at hy3
  obtain ⟨q, hq, hfix1, hfix2⟩ := witAll_sylow hL hE hWa hWb x hx _ rfl (rep_one hZ hy3)
  obtain ⟨c1, c2, cm, n1, n2, n21, n2sq⟩ := planes_sylow hL hE hP q hq
  obtain ⟨f1, -, hf1⟩ := exists_PT (sylowElemAt_mem q.1)
  obtain ⟨f2, -, hf2⟩ := exists_PT (sylowElemAt_mem q.2)
  have s1 := size_sylowElemAt q.1
  have s2 := size_sylowElemAt q.2
  have hf1' : f1 ^ 3 = 1 := pow_three_of_arr hf1 c1
  have hf2' : f2 ^ 3 = 1 := pow_three_of_arr hf2 c2
  have hone : ((1 : lineGroup) : GL (Fin 8) GF8) = (1 : GL (Fin 8) GF8) := rfl
  have h1 : (((1 : lineGroup) : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) = toMat oneArr := by
    rw [toMat_oneArr']
    rfl
  have hf1ne : f1 ≠ 1 := fun h => n1 (arr_eq_of_eq s1 size_oneArr hf1 h1 h)
  have hcomm : f1 * f2 = f2 * f1 := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hf1, hf2,
      ← toMat_mulArr, ← toMat_mulArr, cm]
  have hsq : (((f1 * f1 : lineGroup) : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) =
      toMat (mulArr (sylowElemAt q.1) (sylowElemAt q.1)) := by
    rw [Subgroup.coe_mul, Units.val_mul, hf1, toMat_mulArr]
  have hnot : f2 ∉ Subgroup.zpowers f1 := by
    intro hmem
    rcases mem_zpowers_cube hf1' hmem with h | h | h
    · exact n2 (arr_eq_of_eq s2 size_oneArr hf2 h1 h)
    · exact n21 (arr_eq_of_eq s2 s1 hf2 hf1 h)
    · exact n2sq (arr_eq_of_eq s2 (size_mulArr _ _) hf2 hsq h)
  obtain ⟨hcard, hea⟩ := sup_zpowers_card_nine hf1' hf1ne hf2' hcomm hnot
  refine ⟨_, hea, hcard, ?_⟩
  exact fixed_of_sup_zpowers hcomm (MulEquiv.toMonoidHom _) (fix_of_rep hr hfix1 f1 hf1)
    (fix_of_rep hr hfix2 f2 hf2)

end Checks

local notation "ξW" => wordAut xW

theorem card_H (hZ : Subgroup.center lineGroup = ⊥)
    {ξ : MulAut lineGroup} (hn : ξ ∈ Subgroup.normalizer (InnP : Set (MulAut lineGroup)))
    (hc : ξ ^ 3 = 1) (hout : ∀ g : lineGroup, ξ ≠ MulAut.conj g) :
    Nat.card (InnP ⊔ Subgroup.zpowers ξ : Subgroup (MulAut lineGroup)) = 243 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hξ1 : ξ ≠ 1 := fun h => hout 1 (by rw [h, map_one])
  have hcZ : Nat.card (Subgroup.zpowers ξ) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hc hξ1]
  have hinf : Nat.card (InnP ⊓ Subgroup.zpowers ξ : Subgroup (MulAut lineGroup)) = 1 := by
    have hdvd : Nat.card (InnP ⊓ Subgroup.zpowers ξ : Subgroup (MulAut lineGroup)) ∣ 3 := by
      rw [← hcZ]
      exact Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
    · exact h
    · exfalso
      have heq : InnP ⊓ Subgroup.zpowers ξ = Subgroup.zpowers ξ :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h, hcZ])
      have hle : Subgroup.zpowers ξ ≤ InnP := by
        rw [← heq]
        exact inf_le_left
      obtain ⟨p, -, hp⟩ := Subgroup.mem_map.1 (hle (Subgroup.mem_zpowers ξ))
      exact hout p hp.symm
  have hmul := card_sup_mul_card_inf_of_le_normalizer (Subgroup.zpowers_le.2 hn)
  rw [hinf, mul_one, card_InnP hZ, hcZ] at hmul
  omega

theorem fix_H {ls es : List Nat}
    (hL : ∀ i < 18, packA (letterArr i) = ls.getD i 0)
    (hE : bfsOK (wordP ls wordA) (wordP ls wordB) bfsPar es = true)
    (hZ : Subgroup.center lineGroup = ⊥) (hP : planesQ (gensP es) = true)
    (hWa : witAll (wordQ ls xW) (gensP es) (es.take 40) = true)
    (hWb : witAll (wordQ ls xW) (gensP es) (es.drop 40) = true)
    (hc : wordAut xW ^ 3 = 1)
    (hn : wordAut xW ∈ Subgroup.normalizer (InnP : Set (MulAut lineGroup)))
    {β : MulAut lineGroup} (hβ : β ∈ InnP ⊔ Subgroup.zpowers (wordAut xW))
    (hout : ∀ g : lineGroup, β ≠ MulAut.conj g) (h3 : β ^ 3 = 1) :
    ∃ F : Subgroup lineGroup, IsElemAbelian 3 F ∧ Nat.card F = 9 ∧ ∀ z ∈ F, β z = z := by
  obtain ⟨n, hnI, k, rfl⟩ := mem_sup_zpowers hn hβ
  have h3' : wordAut xW ^ (3 : ℤ) = 1 := by simpa using hc
  rw [zpow_eq_zpow_emod k h3'] at hout h3 ⊢
  obtain h | h | h : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  · rw [h, zpow_zero, mul_one] at hout
    obtain ⟨p, -, hp⟩ := Subgroup.mem_map.1 hnI
    exact absurd hp.symm (hout p)
  · rw [h, zpow_one] at h3 ⊢
    exact fix_coset hL hE hZ hP hWa hWb hnI h3
  · rw [h] at h3 ⊢
    have hn' : ξW ^ (-2 : ℤ) * n⁻¹ * (ξW ^ (-2 : ℤ))⁻¹ ∈ InnP :=
      (Subgroup.mem_normalizer_iff.1 (zpow_mem hn (-2)) _).1 (InnP.inv_mem hnI)
    have hinv : (n * ξW ^ (2 : ℤ))⁻¹ = ξW ^ (-2 : ℤ) * n⁻¹ * (ξW ^ (-2 : ℤ))⁻¹ * ξW := by
      calc (n * ξW ^ (2 : ℤ))⁻¹ = ξW ^ (-2 : ℤ) * n⁻¹ * (ξW ^ (-2 : ℤ))⁻¹ * ξW * (ξW ^ 3)⁻¹ := by
            group
        _ = _ := by rw [hc, inv_one, mul_one]
    have h3i : (ξW ^ (-2 : ℤ) * n⁻¹ * (ξW ^ (-2 : ℤ))⁻¹ * ξW) ^ 3 = 1 := by
      rw [← hinv, inv_pow, h3, inv_one]
    obtain ⟨F, hF, hF9, hfix⟩ := fix_coset hL hE hZ hP hWa hWb hn' h3i
    rw [← inv_inv (n * ξW ^ (2 : ℤ)), hinv]
    exact ⟨F, hF, hF9, fun z hz => inv_fix (hfix z hz)⟩

theorem outerFix_of {ls es : List Nat}
    (hL : ∀ i < 18, packA (letterArr i) = ls.getD i 0)
    (hE : bfsOK (wordP ls wordA) (wordP ls wordB) bfsPar es = true)
    (hnA : eqQ (mulQ (wordQ ls xW) (wordP ls wordA, 0)) (mulQ (atP es 48, 0) (wordQ ls xW)) = true)
    (hnB : eqQ (mulQ (wordQ ls xW) (wordP ls wordB, 0)) (mulQ (atP es 54, 0) (wordQ ls xW)) = true)
    (hcX : cubeQ (wordQ ls xW) = true) (hfX : Nat.beq (wordQ ls xW).2 2 = true)
    (hP : planesQ (gensP es) = true)
    (hWa : witAll (wordQ ls xW) (gensP es) (es.take 40) = true)
    (hWb : witAll (wordQ ls xW) (gensP es) (es.drop 40) = true) :
    Subgroup.center lineGroup = ⊥ → Nat.card (MulAut lineGroup) = 3 * 211341312 →
      ∀ α : MulAut lineGroup, (∀ g : lineGroup, α ≠ MulAut.conj g) → α ^ 3 = 1 →
        ∃ F : Subgroup lineGroup, IsElemAbelian 3 F ∧ Nat.card F = 9 ∧ ∀ x ∈ F, α x = x := by
  intro hZ hA α hout h3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc := wordAut_cube hL hcX
  have hn := mem_normalizer_of_cube hc (conj_InnP hL hE hnA hnB)
  have hH := card_H hZ hn hc (wordAut_outer hL hfX)
  let S : Sylow 3 (MulAut lineGroup) :=
    Sylow.ofCard (InnP ⊔ Subgroup.zpowers (wordAut xW)) (by rw [hH, factorization_three hA]; norm_num)
  have hα1 : α ≠ 1 := fun h => hout 1 (by rw [h, map_one])
  have hαP : IsPGroup 3 (Subgroup.zpowers α) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, orderOf_eq_prime h3 hα1]
    norm_num
  obtain ⟨Q, hQ⟩ := hαP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (MulAut lineGroup) S Q
  have hmapeq : ((g • S : Sylow 3 (MulAut lineGroup)) : Subgroup (MulAut lineGroup)) =
      (InnP ⊔ Subgroup.zpowers (wordAut xW)).map (MulAut.conj g).toMonoidHom := by
    rw [Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def, Sylow.coe_ofCard]
    rfl
  have hαg : α ∈ ((g • S : Sylow 3 (MulAut lineGroup)) : Subgroup (MulAut lineGroup)) := by
    rw [hg]
    exact hQ (Subgroup.mem_zpowers α)
  rw [hmapeq] at hαg
  obtain ⟨β, hβ, hβα⟩ := Subgroup.mem_map.1 hαg
  have hαeq : g * β * g⁻¹ = α := by
    rw [← MulAut.conj_apply]
    exact hβα
  have hβout : ∀ h : lineGroup, β ≠ MulAut.conj h := by
    intro h hβh
    apply hout (g h)
    rw [← hαeq, hβh]
    refine MulEquiv.ext fun x => ?_
    simp [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]
  have hβ3 : β ^ 3 = 1 := by
    have h1 : (MulAut.conj g) (β ^ 3) = (MulAut.conj g) 1 := by
      have hβα' : MulAut.conj g β = α := hβα
      rw [map_pow, map_one, hβα', h3]
    exact (MulAut.conj g).injective h1
  obtain ⟨F, hF, hF9, hfix⟩ := fix_H hL hE hZ hP hWa hWb hc hn hβ hβout hβ3
  have hgInj : Function.Injective (MulEquiv.toMonoidHom g) := g.injective
  refine ⟨F.map (MulEquiv.toMonoidHom g), ?_, ?_, ?_⟩
  · have hcommF : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := fun x hx y hy => by
      have := hF.1
      exact CFSG.LocalAnalysis.GLTheoremA.comm_mem_of_isMulCommutative F hx hy
    exact CFSG.LocalAnalysis.GLTheoremA.isElemAbelian_map_of_forall _ hgInj hcommF hF.2
  · rw [Subgroup.card_map_of_injective hgInj, hF9]
  · intro x hx
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hx
    have hinv : g⁻¹ ((MulEquiv.toMonoidHom g) z) = z := by simp
    rw [← hαeq, MulAut.mul_apply, MulAut.mul_apply, hinv, hfix z hz]
    rfl

end CFSG.KC.HTD42G

end
