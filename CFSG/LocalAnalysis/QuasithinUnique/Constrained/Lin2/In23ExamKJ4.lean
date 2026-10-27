module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKFusion
public import CFSG.Sporadic.J4
public import CFSG.Sporadic.J4.QTRankInvProof
public meta import CFSG.Sporadic.J4.QTRankInvNative
public import Certificates.Certificate4017
public import Certificates.Certificate4024
public import Certificates.Certificate4025
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKJ4Inputs
public import Certificates.Certificate4077
public import Certificates.Certificate3084
public import CFSG.Foundations
public import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticTwoKernel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Alt
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Native
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKCover
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKQuot
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Five
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Containment
public import CFSG.LocalAnalysis.QuasithinUnique.K1.Interface
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.Quasithin.Background.A1cModuleCoprime
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3Structure312
public import CFSG.Quasithin.Background.OrderingMax
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.Sporadic.Schreier.J4SSylow
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.Walter.Defs
public import Certificates.Certificate8026Base

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.QuasithinUnique CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT
open CFSG.Blueprint.NativeSporadic (Carrier)

section Abstract

variable {X : Type} [Group X] [Finite X]

theorem E_le_of_stronglyClosed {H E P R₀ : Subgroup X} (hEP : E ≤ P) (hPH : P ≤ H)
    (hP2 : IsPGroup 2 P) (hEn : ∀ h ∈ H, ∀ x ∈ E, h * x * h⁻¹ ∈ E)
    (hE2 : ∀ x ∈ E, x * x = 1)
    (hmin : ∀ D : Subgroup X, D ≤ E → (∀ h ∈ H, ∀ d ∈ D, h * d * h⁻¹ ∈ D) → D = ⊥ ∨ D = E)
    (hcent : ∀ h ∈ H, (∀ x ∈ E, h * x = x * h) → h ∈ E) (hR : R₀ ≤ P) (hne : R₀ ≠ ⊥)
    (hnorm : ∀ u ∈ P, ∀ r ∈ R₀, u * r * u⁻¹ ∈ R₀)
    (hstrong : ∀ r ∈ R₀, r * r = 1 → ∀ g : X, g * r * g⁻¹ ∈ P → g * r * g⁻¹ ∈ R₀) :
    E ≤ R₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent P := hP2.isNilpotent
  have hRn : (R₀.subgroupOf P).Normal := by
    refine ⟨fun x hx y => ?_⟩
    have hx' : (x : X) ∈ R₀ := hx
    show (y : X) * (x : X) * (y : X)⁻¹ ∈ R₀
    exact hnorm y y.2 x hx'
  have hRne : R₀.subgroupOf P ≠ ⊥ := by
    intro hbot
    apply hne
    rw [eq_bot_iff]
    intro a ha
    have : (⟨a, hR ha⟩ : P) ∈ R₀.subgroupOf P := ha
    rw [hbot, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  obtain ⟨c, hc1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hRne)
  have hcR : ((c : P) : X) ∈ R₀ := c.2.1
  have hcP : ((c : P) : X) ∈ P := (c : P).2
  have hcc : ∀ q ∈ P, ((c : P) : X) * q = q * ((c : P) : X) := by
    intro q hq
    have := Subgroup.mem_center_iff.mp c.2.2 ⟨q, hq⟩
    exact (congrArg Subtype.val this).symm
  have hc1' : ((c : P) : X) ≠ 1 := fun h' => hc1 (Subtype.ext (Subtype.ext h'))
  have hcE : ((c : P) : X) ∈ E := hcent _ (hPH hcP) fun x hx => hcc x (hEP hx)
  have hDn : ∀ h ∈ H, ∀ d ∈ R₀ ⊓ E, h * d * h⁻¹ ∈ R₀ ⊓ E := by
    intro h hh d hd
    have hdE : h * d * h⁻¹ ∈ E := hEn h hh d hd.2
    exact ⟨hstrong d hd.1 (hE2 d hd.2) h (hEP hdE), hdE⟩
  have hDne : R₀ ⊓ E ≠ ⊥ := by
    intro hbot
    have : ((c : P) : X) ∈ R₀ ⊓ E := ⟨hcR, hcE⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact hc1' this
  rcases hmin (R₀ ⊓ E) inf_le_right hDn with h | h
  · exact absurd h hDne
  · rw [← h]
    exact inf_le_left

end Abstract

section Data

theorem invGens_check :
    (∀ j < 4, invEs.getD j 0 < 1024 ∧ isInvE (invEs.getD j 0) = true ∧ invCs.getD j 0 < 2048 ∧
      ∃ x ∈ invData, x.1 = invEs.getD j 0 ∧
        invCs.getD j 0 ^^^ actT (tabE (invEs.getD j 0)) (invCs.getD j 0) = x.2.1) ∧
    (∀ i < 4, (∀ j ∈ invWords.getD i [], j < 4) ∧
      compT (kInvTab i)
        (((invWords.getD i []).map fun j => tabE (invEs.getD j 0)).foldr compT idT) = idT) :=
  Certificates.certificate4077

end Data

section J4

@[expose] noncomputable def invEl (j : ℕ) : J := eta uJ 11 (invCs.getD j 0) * Kel (invEs.getD j 0)

theorem invEs_lt {j : ℕ} (hj : j < 4) : invEs.getD j 0 < 1024 := (invGens_check.1 j hj).1

theorem isInvE_invEs {j : ℕ} (hj : j < 4) : isInvE (invEs.getD j 0) = true :=
  (invGens_check.1 j hj).2.1

theorem invEl_mem_P0 {j : ℕ} (hj : j < 4) : invEl j ∈ P0 := eta_mul_Kel_mem (invEs_lt hj)

theorem prod_invEl_mem_P0 (w : List ℕ) (hw : ∀ j ∈ w, j < 4) : (w.map invEl).prod ∈ P0 := by
  refine Subgroup.list_prod_mem _ ?_
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
  exact invEl_mem_P0 (hw j hj)

section WithFacts

variable (hM : MatFacts)
include hM

theorem Acts_invEl {j : ℕ} (hj : j < 4) : Acts (invEl j) (tabE (invEs.getD j 0)) :=
  Acts_eta_mul_Kel hM (invEs_lt hj)

theorem Acts_word : ∀ w : List ℕ, (∀ j ∈ w, j < 4) →
    Acts ((w.map invEl).prod) ((w.map fun j => tabE (invEs.getD j 0)).foldr compT idT)
  | [], _ => by simpa using Acts.one
  | j :: w, h => by
    have := (Acts_invEl hM (h j (List.mem_cons_self ..))).mul
      (Acts_word w (fun x hx => h x (List.mem_cons_of_mem _ hx)))
    simpa using this

theorem Kel_sq_of_mem {x : ℕ × ℕ × List (ℕ × ℕ × ℕ × ℕ)} (hx : x ∈ invData) :
    Kel x.1 * Kel x.1 = eta uJ 11 x.2.1 := by
  obtain ⟨hx1, hq, hKK, -, -⟩ := invOKT_spec (invAllOK_spec x hx)
  apply Mx_injective
  have h1 := congrArg rowsMatrix (eqRows_iff.1 hKK)
  rw [rowsMatrix_mulRows] at h1
  rw [map_mul, Mx_Kel hM hx1, Mx_etaR hM]
  exact h1

theorem eta_mul_Kel_sq {c e : ℕ} (he : e < 1024) (hc : c < 2 ^ 11)
    {x : ℕ × ℕ × List (ℕ × ℕ × ℕ × ℕ)} (hx : x ∈ invData) (hxe : x.1 = e)
    (hq : c ^^^ actT (tabE e) c = x.2.1) :
    (eta uJ 11 c * Kel e) * (eta uJ 11 c * Kel e) = 1 := by
  have hK := Acts_Kel hM he
  have hKel2 : Kel e * Kel e = eta uJ 11 x.2.1 := by
    have := Kel_sq_of_mem hM hx
    rwa [hxe] at this
  have hKc : Kel e * eta uJ 11 c = eta uJ 11 (actT (tabE e) c) * Kel e := by
    have := hK.2 c hc
    rwa [mul_inv_eq_iff_eq_mul] at this
  have hrr : (eta uJ 11 c * Kel e) * (eta uJ 11 c * Kel e) =
      eta uJ 11 (c ^^^ actT (tabE e) c ^^^ x.2.1) := by
    calc (eta uJ 11 c * Kel e) * (eta uJ 11 c * Kel e)
        = eta uJ 11 c * (Kel e * eta uJ 11 c) * Kel e := by group
      _ = eta uJ 11 c * (eta uJ 11 (actT (tabE e) c) * Kel e) * Kel e := by rw [hKc]
      _ = eta uJ 11 c * eta uJ 11 (actT (tabE e) c) * (Kel e * Kel e) := by group
      _ = eta uJ 11 c * eta uJ 11 (actT (tabE e) c) * eta uJ 11 x.2.1 := by rw [hKel2]
      _ = eta uJ 11 (c ^^^ actT (tabE e) c ^^^ x.2.1) := by
        rw [eta_xor (elem_uJ hM) le_rfl, eta_xor (elem_uJ hM) le_rfl]
  rw [hrr, hq, Nat.xor_self, eta_zero]

theorem invEl_sq {j : ℕ} (hj : j < 4) : invEl j * invEl j = 1 := by
  obtain ⟨-, -, hc, x, hx, hxe, hq⟩ := invGens_check.1 j hj
  exact eta_mul_Kel_sq hM (invEs_lt hj) (by simpa using hc) hx hxe hq

theorem invEl_ne_one {j : ℕ} (hj : j < 4) : invEl j ≠ 1 := by
  intro h
  have h1 := Acts_invEl hM hj
  rw [h] at h1
  have h2 := h1.unique hM Acts.one
  have hinv := isInvE_invEs hj
  unfold isInvE at hinv
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hinv
  exact hinv.2 h2

end WithFacts

theorem mem_Eg_of_Acts_idT (hF : J4Facts) {h : J} (hh : h ∈ Hj) (ha : Acts h idT) :
    h ∈ Eg uJ 11 := by
  have hM := hF.mat
  refine centralizer_Hj hM hF h hh (fun y hy => ?_)
  obtain ⟨d, hd, rfl⟩ := (mem_Eg_iff (elem_uJ hM)).1 hy
  have := ha.2 d hd
  rw [actT_idT hd] at this
  calc h * eta uJ 11 d = (h * eta uJ 11 d * h⁻¹) * h := by group
    _ = eta uJ 11 d * h := by rw [this]

theorem P0_isPGroup (hF : J4Facts) : IsPGroup 2 P0 :=
  IsPGroup.of_card (n := 21) (card_P0 hF.mat hF)

theorem isSylowTwoOf_P0 (hF : J4Facts) : IsSylowTwoOf P0 ⊤ := by
  rw [CFSG.QuasithinUnique.K1.isSylowTwoOf_top_iff]
  refine ⟨P0_isPGroup hF, fun hd => ?_⟩
  have h := Subgroup.card_mul_index P0
  rw [card_P0 hF.mat hF] at h
  have h22 : 2 ^ 22 ∣ Nat.card J := by
    rw [← h]
    obtain ⟨m, hm⟩ := hd
    rw [hm]
    exact ⟨m, by ring⟩
  have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (Nat.card_pos (α := J)).ne').1 h22
  rw [card_J_factorization hF] at this
  omega

theorem J4_E_le (hF : J4Facts) {R₀ : Subgroup J} (hR : R₀ ≤ P0) (hne : R₀ ≠ ⊥)
    (hnorm : ∀ u ∈ P0, ∀ r ∈ R₀, u * r * u⁻¹ ∈ R₀)
    (hstrong : ∀ r ∈ R₀, r * r = 1 → ∀ g : J, g * r * g⁻¹ ∈ P0 → g * r * g⁻¹ ∈ R₀) :
    Eg uJ 11 ≤ R₀ := by
  have hM := hF.mat
  refine E_le_of_stronglyClosed (H := Hj) Eg_le_P0 P0_le_Hj (P0_isPGroup hF) ?_ ?_ ?_
    (centralizer_Hj hM hF) hR hne hnorm hstrong
  · exact eg_normalizes (elem_uJ hM) Hj XJ act letters (fun ℓ hℓ c => hX_all hM hℓ c)
      (fun ℓ hℓ => XJ_inv hℓ) Hj_le_closure
  · intro x hx
    obtain ⟨c, -, rfl⟩ := (mem_Eg_iff (elem_uJ hM)).1 hx
    exact eta_sq (elem_uJ hM) c
  · intro D hDE hD
    exact minimal_of_orbits (elem_uJ hM) Hj XJ act letters (fun ℓ hℓ => XJ_mem hℓ)
      (fun ℓ hℓ c => hX_all hM hℓ c) orbits orbit_words orbit_cover orbit_span D hDE hD

theorem invEl_mem (hF : J4Facts) {R₀ : Subgroup J} (hEq : Eg uJ 11 ≤ R₀)
    (hstrong : ∀ r ∈ R₀, r * r = 1 → ∀ g : J, g * r * g⁻¹ ∈ P0 → g * r * g⁻¹ ∈ R₀) {j : ℕ}
    (hj : j < 4) : invEl j ∈ R₀ := by
  have hM := hF.mat
  have hP := invEl_mem_P0 hj
  have key : ∀ c : ℕ, IsConj (eta uJ 11 c) (invEl j) → invEl j ∈ R₀ := by
    intro c hc
    obtain ⟨g, hg⟩ := isConj_iff.1 hc
    have hη : eta uJ 11 c ∈ R₀ := hEq (eta_mem_Eg 11 le_rfl c)
    have := hstrong _ hη (eta_sq (elem_uJ hM) c) g (by rw [hg]; exact hP)
    rwa [hg] at this
  rcases inv_conj_of_mem_P0 hF hP (invEl_sq hM hj) (invEl_ne_one hM hj) with h | h
  · exact key 1 h
  · exact key 3 h

theorem kJ_mem_of_invEl (hF : J4Facts) {R₀ : Subgroup J} (hEq : Eg uJ 11 ≤ R₀)
    (hinv : ∀ j < 4, invEl j ∈ R₀) {i : ℕ} (hi : i < 4) : kJ i ∈ R₀ := by
  have hM := hF.mat
  have hw := (invGens_check.2 i hi).1
  have hPR : ((invWords.getD i []).map invEl).prod ∈ R₀ := by
    refine Subgroup.list_prod_mem _ ?_
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
    exact hinv j (hw j hj)
  have hAct := Acts_word hM (invWords.getD i []) hw
  have hAct2 : Acts ((kJ i)⁻¹ * ((invWords.getD i []).map invEl).prod) idT := by
    have := (Acts_kJ_inv hM hi).mul hAct
    rwa [(invGens_check.2 i hi).2] at this
  have hHj : (kJ i)⁻¹ * ((invWords.getD i []).map invEl).prod ∈ Hj :=
    Hj.mul_mem (Hj.inv_mem (kJ_mem hi)) (P0_le_Hj (prod_invEl_mem_P0 _ hw))
  have hE := mem_Eg_of_Acts_idT hF hHj hAct2
  have key : ∀ x P : J, x = P * (x⁻¹ * P)⁻¹ := fun x P => by group
  rw [key (kJ i) (((invWords.getD i []).map invEl).prod)]
  exact R₀.mul_mem hPR (R₀.inv_mem (hEq hE))

theorem J4_eq_P0 (hF : J4Facts) {R₀ : Subgroup J} (hR : R₀ ≤ P0) (hne : R₀ ≠ ⊥)
    (hnorm : ∀ u ∈ P0, ∀ r ∈ R₀, u * r * u⁻¹ ∈ R₀)
    (hstrong : ∀ r ∈ R₀, r * r = 1 → ∀ g : J, g * r * g⁻¹ ∈ P0 → g * r * g⁻¹ ∈ R₀) :
    R₀ = P0 := by
  have hEq := J4_E_le hF hR hne hnorm hstrong
  have hinv : ∀ j < 4, invEl j ∈ R₀ := fun j hj => invEl_mem hF hEq hstrong hj
  refine le_antisymm hR ?_
  show Subgroup.closure S0 ≤ R₀
  rw [Subgroup.closure_le]
  rintro _ (⟨j, hj, rfl⟩ | ⟨i, hi, rfl⟩)
  · exact hEq (u_mem_Eg hj)
  · exact kJ_mem_of_invEl hF hEq hinv hi

theorem j4_group_strongCardEx : StrongCardEx J 21 := by
  have hF := j4Facts
  refine ⟨P0, isSylowTwoOf_P0 hF, fun R₀ hR hne hnorm hstrong => ?_⟩
  rw [J4_eq_P0 hF hR hne hnorm hstrong]
  exact card_P0 hF.mat hF

theorem j4_native_strongCardEx : StrongCardEx (Carrier .J4) 21 := by
  have : Finite (Carrier .J4) := CFSG.Sporadic.J4.fam_j4_simplicity.1
  exact StrongCardEx.of_mulEquiv (X := Carrier .J4) (Y := J)
    (CFSG.Sporadic.J4.seedEquiv CFSG.Sporadic.J4.j4Facts.mat) j4_group_strongCardEx

end J4

end CFSG.QuasithinUnique.Lin2
