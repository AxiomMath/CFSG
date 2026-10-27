module

public import CFSG.ClassicalInvolution.ModelFacts.LinearAutType
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalPSL
public import CFSG.ClassicalInvolution.RouteD.TypeAFrame
public import CFSG.ClassicalInvolution.RouteD.TypeAModel
public import CFSG.ClassicalInvolution.LBalance.Main
public import CFSG.ClassicalInvolution.Models.LinearFrames
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.PrimeComplementQuotientComponents
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Basic

public section

namespace CFSG.ClassicalInvolution.ModelFacts.LinearAut

open Matrix.SpecialLinearGroup (transvection)
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.RouteD
  CFSG.ComponentClassification.CatalogueBHigherLinearAction
open scoped MatrixGroups Matrix commutatorElement

section OddCore

variable {G : Type*} [Group G]

theorem commutatorElement_mul_mul_central (a b : G) {z w : G} (hz : z ∈ Subgroup.center G)
    (hw : w ∈ Subgroup.center G) : ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
  have h1 : ∀ g, z * g * z⁻¹ = g := fun g => by
    rw [← Subgroup.mem_center_iff.1 hz g, mul_inv_cancel_right]
  have h2 : ∀ g, w * g * w⁻¹ = g := fun g => by
    rw [← Subgroup.mem_center_iff.1 hw g, mul_inv_cancel_right]
  calc ⁅a * z, b * w⁆ = a * (z * (b * w) * z⁻¹) * a⁻¹ * (b * w)⁻¹ := by
        rw [commutatorElement_def]; group
    _ = a * b * (w * a⁻¹ * w⁻¹) * b⁻¹ := by rw [h1]; group
    _ = ⁅a, b⁆ := by rw [h2, commutatorElement_def]

theorem oddCore_eq_bot_of_quasisimple [Finite G] (hG : CFSG.Open.IsQuasisimple G)
    (hZ : Nat.card (Subgroup.center G) = 2) : classicalInvolutionOddCore G = ⊥ := by
  set N := classicalInvolutionOddCore G with hN
  have hodd : Odd (Nat.card N) := CFSG.ComponentClassification.OddCore.odd_card G
  have : IsSimpleGroup (G ⧸ Subgroup.center G) := hG.2
  have hN' : ∀ a b, b ∈ N → a ∈ N → a * b * a⁻¹ ∈ N := fun a b hb ha =>
    (inferInstance : N.Normal).conj_mem b hb a
  have hNmap : (N.map (QuotientGroup.mk' (Subgroup.center G))).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  rcases hNmap.eq_bot_or_eq_top with h | h
  ·
    have hle : N ≤ Subgroup.center G := by
      intro x hx
      have : QuotientGroup.mk' (Subgroup.center G) x ∈ N.map (QuotientGroup.mk' (Subgroup.center G)) :=
        ⟨x, hx, rfl⟩
      rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
      exact this
    have hdvd : Nat.card N ∣ Nat.card (Subgroup.center G) := Subgroup.card_dvd_of_le hle
    rw [hZ] at hdvd
    have h1 : Nat.card N = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
      · exact h1
      · rw [h1] at hodd
        exact absurd hodd (by decide)
    exact (Subgroup.card_eq_one).mp h1
  ·
    exfalso
    have hNZ : N ⊔ Subgroup.center G = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have : QuotientGroup.mk' (Subgroup.center G) x ∈ N.map (QuotientGroup.mk' (Subgroup.center G)) := by
        rw [h]; exact Subgroup.mem_top _
      obtain ⟨y, hy, hyx⟩ := this
      have hmem : y⁻¹ * x ∈ Subgroup.center G := by
        rw [← QuotientGroup.eq]
        exact hyx
      have : x = y * (y⁻¹ * x) := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hy) (Subgroup.mem_sup_right hmem)
    have hcomm : commutator G ≤ N := by
      rw [commutator_def]
      refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
      have ha' : a ∈ N ⊔ Subgroup.center G := by rw [hNZ]; exact Subgroup.mem_top a
      have hb' : b ∈ N ⊔ Subgroup.center G := by rw [hNZ]; exact Subgroup.mem_top b
      obtain ⟨n₁, hn₁, z₁, hz₁, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp ha'
      obtain ⟨n₂, hn₂, z₂, hz₂, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hb'
      rw [commutatorElement_mul_mul_central _ _ hz₁ hz₂, commutatorElement_def]
      exact N.mul_mem (hN' n₁ n₂ hn₂ hn₁) (N.inv_mem hn₂)
    have hNtop : N = ⊤ := by
      rw [eq_top_iff, ← hG.1]
      exact hcomm
    have hZtop : Subgroup.center G ≤ N := hNtop ▸ le_top
    have hdvd : Nat.card (Subgroup.center G) ∣ Nat.card N := Subgroup.card_dvd_of_le hZtop
    rw [hZ] at hdvd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)

end OddCore

section Intrinsic

variable {p f : ℕ} [Fact p.Prime]

theorem isClassicalMember_map_equiv {Y Y' : Type} [Group Y] [Group Y'] {L : Subgroup Y} {z : Y}
    (h : IsClassicalMember p f L z) (φ : Y ≃* Y') :
    IsClassicalMember p f (L.map φ.toMonoidHom) (φ z) where
  orderOf_eq_two := by rw [MulEquiv.orderOf_eq]; exact h.orderOf_eq_two
  mem := Subgroup.mem_map_of_mem _ h.mem
  perfect := by
    have := h.perfect
    exact Group.IsPerfect.map φ.toMonoidHom
  subnormal := by
    have h1 := isSubnormal_comap φ.symm.toMonoidHom h.subnormal
    have e1 : L.comap φ.symm.toMonoidHom = L.map φ.toMonoidHom := by
      ext x
      rw [Subgroup.mem_comap, Subgroup.mem_map_equiv]
      rfl
    have e2 : (Subgroup.centralizer ({z} : Set Y)).comap φ.symm.toMonoidHom =
        Subgroup.centralizer ({φ z} : Set Y') := by
      ext x
      simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom,
        Subgroup.mem_centralizer_singleton_iff]
      constructor
      · intro hx
        have := congrArg φ hx
        simpa using this
      · intro hx
        apply φ.injective
        simpa using hx
    rwa [e1, e2] at h1
  nonempty_equiv := by
    obtain ⟨e'⟩ := h.nonempty_equiv
    let e : L ≃* L.map φ.toMonoidHom := L.equivMapOfInjective φ.toMonoidHom φ.injective
    have hO : (classicalInvolutionOddCore L).map e.toMonoidHom =
        classicalInvolutionOddCore (L.map φ.toMonoidHom) :=
      CFSG.ComponentClassification.OddCore.equiv_invariant e
    exact ⟨(QuotientGroup.congr _ _ e hO).symm.trans e'⟩

theorem oddCore_sl2_eq_bot {F : Type} [Field F] [Finite F] (h2 : (2 : F) ≠ 0)
    (h4 : 4 ≤ Nat.card F) : classicalInvolutionOddCore SL(2, F) = ⊥ := by
  refine oddCore_eq_bot_of_quasisimple (open_isQuasisimple_sl (F := F) (le_refl 2) h4) ?_
  have hne : (1 : SL(2, F)) ≠ -1 := by
    intro h
    have := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F) 0 0) h
    have h' : ((-1 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
        Matrix.scalar (Fin 2) (-1) := CFSG.Semidihedral.OddFieldSL2.minusIdentity_matrix F
    simp only [Matrix.SpecialLinearGroup.coe_one, h'] at this
    simp at this
    apply h2
    linear_combination this
  rw [Nat.card_eq_two_iff]
  refine ⟨⟨1, Subgroup.one_mem _⟩, ⟨-1, (mem_center_sl2_iff _).2 (Or.inr rfl)⟩, ?_, ?_⟩
  · intro h
    exact hne (congrArg Subtype.val h)
  · ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    obtain ⟨x, hx⟩ := x
    rcases (mem_center_sl2_iff x).1 hx with rfl | rfl
    · left; rfl
    · right; rfl

theorem isClassicalMember_of_isLongRootSL2 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {n : ℕ} (hn : 2 ≤ n)
    {L : Subgroup SL(n, GaloisField p f)} {i : SL(n, GaloisField p f)}
    (h : IsLongRootSL2 hn L i) : IsClassicalMember p f L i := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have : NeZero f := ⟨hf⟩
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
  have h2 : (2 : GaloisField p f) ≠ 0 := by
    intro h0
    have : ringChar (GaloisField p f) ∣ 2 := ringChar.dvd (by simpa using h0)
    rw [ringChar.eq (GaloisField p f) p] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp this)
  have h4 : 4 ≤ Nat.card (GaloisField p f) := by rw [hcard]; omega
  have hcl := h.isClassicalSL2 h2
  obtain ⟨e⟩ := hcl.nonempty_mulEquiv
  have hO : classicalInvolutionOddCore L = ⊥ := by
    have h1 : (classicalInvolutionOddCore L).map e.toMonoidHom =
        classicalInvolutionOddCore SL(2, GaloisField p f) :=
      CFSG.ComponentClassification.OddCore.equiv_invariant e
    rw [oddCore_sl2_eq_bot h2 h4] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h1
  refine ⟨hcl.orderOf_eq_two, hcl.mem, hcl.isPerfect h4, ?_, ⟨?_⟩⟩
  · refine isSubnormal_of_normal_subgroupOf hcl.le_centralizer ?_
    rw [Subgroup.normal_subgroupOf_iff hcl.le_centralizer]
    intro l k hl hk
    exact ((Subgroup.mem_normalizer_iff.mp (hcl.centralizer_le_normalizer hk) l).mp hl)
  · exact ((QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot).trans e

theorem isLongRootSL2_map_aut (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {n : ℕ} (hn : 2 ≤ n)
    (α : SL(n, GaloisField p f) ≃* SL(n, GaloisField p f))
    {L : Subgroup SL(n, GaloisField p f)} {i : SL(n, GaloisField p f)} (h : IsLongRootSL2 hn L i) :
    IsLongRootSL2 hn (L.map α.toMonoidHom) (α i) :=
  isLongRootSL2_of_isClassicalMember hp2 hq hn
    (isClassicalMember_map_equiv (isClassicalMember_of_isLongRootSL2 hp2 hq hn h) α)

end Intrinsic

section Frame

variable {p f : ℕ} [Fact p.Prime]

@[expose] def cp (n a : ℕ) (h : a + 2 ≤ n) : Pair n :=
  pr ⟨a, by omega⟩ ⟨a + 1, by omega⟩ (by simp [Fin.ext_iff])

theorem cp_ne {n a b : ℕ} (ha : a + 2 ≤ n) (hb : b + 2 ≤ n) (hab : a ≠ b) :
    cp n a ha ≠ cp n b hb := by
  intro h
  have h1 := congrArg Subtype.val h
  have h2 : (⟨a, by omega⟩ : Fin n) ∈ (cp n b hb).1 := by
    rw [← h1]; simp [cp, pr]
  have h3 : (⟨a + 1, by omega⟩ : Fin n) ∈ (cp n b hb).1 := by
    rw [← h1]; simp [cp, pr]
  simp only [cp, pr, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff] at h2 h3
  omega

theorem coe_zElt_cp {F : Type} [Field F] {n a : ℕ} (h : a + 2 ≤ n) :
    ((zElt F (cp n a h) : SL(n, F)) : Matrix (Fin n) (Fin n) F) = negBlock F n a := by
  rw [coe_zElt, negBlock_eq_zMat h]
  rfl

theorem exists_frame_aut (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {n : ℕ} (hn : 3 ≤ n)
    (α : SL(n, GaloisField p f) ≃* SL(n, GaloisField p f)) :
    ∃ P : SL(n, GaloisField p f), ∀ (a : ℕ) (h : a + 2 ≤ n),
      α (zElt (GaloisField p f) (cp n a h)) = P * zElt (GaloisField p f) (cp n a h) * P⁻¹ := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have : NeZero f := ⟨hf⟩
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
  have h2 : (2 : GaloisField p f) ≠ 0 := by
    intro h0
    have : ringChar (GaloisField p f) ∣ 2 := ringChar.dvd (by simpa using h0)
    rw [ringChar.eq (GaloisField p f) p] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp this)
  set F := GaloisField p f with hFdef
  have hn2 : 2 ≤ n := by omega
  have hLR : ∀ (a : ℕ) (h : a + 2 ≤ n), IsLongRootSL2 hn2 ((Lc F (cp n a h)).map α.toMonoidHom)
      (α (zElt F (cp n a h))) := fun a h =>
    isLongRootSL2_map_aut hp2 hq hn2 α (isLongRootSL2_Lc h2 hn2 (cp n a h))
  let I : ℕ → Matrix (Fin n) (Fin n) F := fun a =>
    if h : a + 2 ≤ n then ((α (zElt F (cp n a h)) : SL(n, F)) : Matrix (Fin n) (Fin n) F) else 1
  have hI : ∀ (a : ℕ) (h : a + 2 ≤ n), I a = ((α (zElt F (cp n a h)) : SL(n, F)) :
      Matrix (Fin n) (Fin n) F) := fun a h => by simp [I, h]
  have hzcomm : ∀ (a b : ℕ) (ha : a + 2 ≤ n) (hb : b + 2 ≤ n),
      zElt F (cp n a ha) * zElt F (cp n b hb) = zElt F (cp n b hb) * zElt F (cp n a ha) := by
    intro a b ha hb
    refine Subtype.ext ?_
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_zElt, coe_zElt]
    exact zMat_mul_comm _ _
  have hchain : IsInvChain I (n - 1) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro a ha
      have h := (by omega : a + 2 ≤ n)
      rw [hI a h, ← Matrix.SpecialLinearGroup.coe_mul, ← map_mul, zElt_mul_self, map_one,
        Matrix.SpecialLinearGroup.coe_one]
    · intro a ha b hb
      have h1 := (by omega : a + 2 ≤ n)
      have h2' := (by omega : b + 2 ≤ n)
      rw [hI a h1, hI b h2', ← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul,
        ← map_mul, ← map_mul, hzcomm a b h1 h2']
    · intro a ha
      have h := (by omega : a + 2 ≤ n)
      rw [hI a h]
      exact (hLR a h).finrank_minusSpace h2
    · intro a ha b hb hab
      have h1 := (by omega : a + 2 ≤ n)
      have h2' := (by omega : b + 2 ≤ n)
      rw [hI a h1, hI b h2']
      refine (spaces_of_commutes h2 (by omega : 3 ≤ n) (hLR a h1) (hLR b h2') ?_ ?_).2.2
      · intro e
        exact cp_ne h1 h2' (by omega) (zElt_injective h2 (α.injective e))
      · refine (commutes_map_iff α.toMonoidHom α.injective).mpr ?_
        refine commutes_Lc_of_disjoint h2 ?_
        rw [Finset.disjoint_left]
        intro x hx hx'
        simp only [cp, pr, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff] at hx hx'
        omega
    · intro a ha
      have h1 := (by omega : a + 2 ≤ n)
      have h2' := (by omega : a + 1 + 2 ≤ n)
      rw [hI a h1, hI (a + 1) h2']
      refine inf_ne_bot_of_not_commutes h2 (hLR a h1) (hLR (a + 1) h2') ?_ ?_
      · show _ * _ = _ * _
        rw [← map_mul, ← map_mul, hzcomm a (a + 1) h1 h2']
      · intro hc
        have := (commutes_map_iff α.toMonoidHom α.injective).mp hc
        exact not_commutes_Lc_overlap h2 (by omega : 3 ≤ n) (i := ⟨a, by omega⟩)
          (j := ⟨a + 1, by omega⟩) (k := ⟨a + 2, by omega⟩) (by simp [Fin.ext_iff])
          (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]) this
    · intro a ha
      have h1 := (by omega : a + 2 ≤ n)
      have h2' := (by omega : a + 1 + 2 ≤ n)
      rw [hI a h1, hI (a + 1) h2']
      intro e
      have := Subtype.ext e
      exact cp_ne h1 h2' (by omega) (zElt_injective h2 (α.injective this))
  obtain ⟨-, P, hP, -⟩ := hchain.exists_frame h2 (by omega : 2 ≤ n - 1)
  refine ⟨P, fun a h => ?_⟩
  have hPa := hP a (by omega)
  rw [hI a h, ← coe_zElt_cp h] at hPa
  have hSL : α (zElt F (cp n a h)) * P = P * zElt F (cp n a h) := Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    exact hPa)
  rw [eq_mul_inv_iff_mul_eq, hSL]

end Frame

section FixSigns

variable {F : Type} [Field F] {n : ℕ}

theorem zElt_pr_mul {i j k : Fin n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    zElt F (pr i j hij) * zElt F (pr j k hjk) = zElt F (pr i k hik) :=
  Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_zElt, coe_zElt, coe_zElt]
    exact zMat_pair_mul hij hjk hik)

theorem fixes_zElt {α : SL(n, F) →* SL(n, F)}
    (hch : ∀ (a : ℕ) (h : a + 2 ≤ n), α (zElt F (cp n a h)) = zElt F (cp n a h)) (T : Pair n) :
    α (zElt F T) = zElt F T := by
  have key : ∀ (d i : ℕ) (hi : i + d + 2 ≤ n),
      α (zElt F (pr ⟨i, by omega⟩ ⟨i + d + 1, by omega⟩ (by simp [Fin.ext_iff]; omega))) =
        zElt F (pr ⟨i, by omega⟩ ⟨i + d + 1, by omega⟩ (by simp [Fin.ext_iff]; omega)) := by
    intro d
    induction d with
    | zero => intro i hi; exact hch i (by omega)
    | succ d ih =>
      intro i hi
      have h1 := ih i (by omega)
      have h2 := hch (i + d + 1) (by omega)
      have e := zElt_pr_mul (F := F) (i := (⟨i, by omega⟩ : Fin n))
        (j := (⟨i + d + 1, by omega⟩ : Fin n)) (k := (⟨i + (d + 1) + 1, by omega⟩ : Fin n))
        (by simp [Fin.ext_iff]; omega) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]; omega)
      rw [← e, map_mul, h1]
      exact congrArg _ h2
  obtain ⟨a, b, hab, hT⟩ := Finset.card_eq_two.mp T.2
  have hT' : T = pr a b hab := Subtype.ext hT
  have hsym : ∀ {a b : Fin n} (hab : a < b), α (zElt F (pr a b hab.ne)) = zElt F (pr a b hab.ne) := by
    intro a b hab
    have := key (b.val - a.val - 1) a.val (by omega)
    have e : (⟨a.val + (b.val - a.val - 1) + 1, by omega⟩ : Fin n) = b := Fin.ext (by simp; omega)
    simpa [e] using this
  rw [hT']
  rcases lt_trichotomy a b with h | h | h
  · exact hsym h
  · exact absurd h hab
  · have e : pr a b hab = pr b a hab.symm := Subtype.ext (Finset.pair_comm a b)
    rw [e]
    exact hsym h

end FixSigns

section Assembly

variable {p f : ℕ} [Fact p.Prime]

local notation "𝔽" => GaloisField p f

theorem exists_aut_form (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {n : ℕ} (hn : 3 ≤ n)
    (α : SL(n, 𝔽) ≃* SL(n, 𝔽)) :
    ∃ (g : GL (Fin n) 𝔽) (φ : 𝔽 ≃+* 𝔽) (ε : Bool), ∀ x : SL(n, 𝔽),
      ((α x : SL(n, 𝔽)) : Matrix (Fin n) (Fin n) 𝔽) =
        (g : Matrix (Fin n) (Fin n) 𝔽) *
          φ.mapMatrix (if ε then (((x⁻¹ : SL(n, 𝔽)) : Matrix (Fin n) (Fin n) 𝔽))ᵀ
            else (x : Matrix (Fin n) (Fin n) 𝔽)) *
          ((g⁻¹ : GL (Fin n) 𝔽) : Matrix (Fin n) (Fin n) 𝔽) := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have : NeZero f := ⟨hf⟩
  have h2 : (2 : 𝔽) ≠ 0 := by
    intro h0
    have : ringChar 𝔽 ∣ 2 := ringChar.dvd (by simpa using h0)
    rw [ringChar.eq 𝔽 p] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp this)
  have hn2 : 2 ≤ n := by omega
  obtain ⟨P, hP⟩ := exists_frame_aut hp2 hq hn α
  let β : SL(n, 𝔽) ≃* SL(n, 𝔽) := α.trans (MulAut.conj P⁻¹)
  have hβx : ∀ x, β x = P⁻¹ * α x * P := fun x => by
    show P⁻¹ * α x * P⁻¹⁻¹ = P⁻¹ * α x * P
    rw [inv_inv]
  have hch : ∀ (a : ℕ) (h : a + 2 ≤ n),
      β.toMonoidHom (zElt 𝔽 (cp n a h)) = zElt 𝔽 (cp n a h) := by
    intro a h
    show β (zElt 𝔽 (cp n a h)) = _
    rw [hβx, hP a h]
    group
  have hz : ∀ T : Pair n, β.toMonoidHom (zElt 𝔽 T) = zElt 𝔽 T := fixes_zElt hch
  have hL : ∀ T : Pair n, ∀ g ∈ Lc 𝔽 T, β.toMonoidHom g ∈ Lc 𝔽 T := by
    intro T g hg
    have h1 := isLongRootSL2_map_aut hp2 hq hn2 β (isLongRootSL2_Lc h2 hn2 T)
    have hzT : β (zElt 𝔽 T) = zElt 𝔽 T := hz T
    rw [hzT] at h1
    have e : (Lc 𝔽 T).map β.toMonoidHom = Lc 𝔽 T := by
      rw [h1.eq_longRootGroup h2, (isLongRootSL2_Lc h2 hn2 T).eq_longRootGroup h2]
    rw [← e]
    exact Subgroup.mem_map_of_mem _ hg
  obtain ⟨g₁, φ, ε, hg₁⟩ := aut_form_of_fixes_signs h2 hn β.toMonoidHom β.injective hz hL
  refine ⟨Matrix.SpecialLinearGroup.toGL P * g₁, φ, ε, fun x => ?_⟩
  have hαx : α x = P * β x * P⁻¹ := by
    rw [hβx]
    group
  have hP1 : (((Matrix.SpecialLinearGroup.toGL P : GL (Fin n) 𝔽)) : Matrix (Fin n) (Fin n) 𝔽) =
      (P : Matrix (Fin n) (Fin n) 𝔽) := rfl
  have hP2 : ((((Matrix.SpecialLinearGroup.toGL P)⁻¹ : GL (Fin n) 𝔽)) :
      Matrix (Fin n) (Fin n) 𝔽) = ((P⁻¹ : SL(n, 𝔽)) : Matrix (Fin n) (Fin n) 𝔽) := rfl
  have e1 := hg₁ x
  rw [MulEquiv.coe_toMonoidHom] at e1
  rw [hαx, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, e1]
  simp only [mul_inv_rev, Units.val_mul, hP1, hP2, Matrix.mul_assoc]

end Assembly

end CFSG.ClassicalInvolution.ModelFacts.LinearAut
