module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma32
public import CFSG.HardMathSupport.Solomon.LocalBalance.GlueTools
public import CFSG.LocalAnalysis.GLTheoremB.PCompLift
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma29Tools
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.GLTheoremB.PCompBasics

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement

@[expose] def IsStronglyBalancedIn (p : ℕ) {X : Type*} [Group X] (B K : Subgroup X) : Prop :=
  ∀ S : Subgroup X, S ≤ Subgroup.normalizer (K : Set X) → Nat.Coprime p (Nat.card S) →
    B ⊓ Subgroup.normalizer (K : Set X) ≤ Subgroup.normalizer (S : Set X) →
      S ≤ Subgroup.centralizer (K : Set X)

@[expose] noncomputable def autOrderIn {X : Type*} [Group X] (B K : Subgroup X) : ℕ :=
  (Subgroup.centralizer (K : Set X)).relIndex (B ⊓ Subgroup.normalizer (K : Set X))

@[expose] def InducesInnerIn {X : Type*} [Group X] (B K : Subgroup X) : Prop :=
  ∀ b ∈ B ⊓ Subgroup.normalizer (K : Set X), ∃ k ∈ K, k⁻¹ * b ∈ Subgroup.centralizer (K : Set X)

@[expose] def Input27_1At (X : Type) [Group X] [Finite X] : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → GLAPPrimeCore p X = ⊥ →
    ∀ K : Subgroup X, GLAPComponent p ⊤ K → IsCatalogGroup (↥K ⧸ Subgroup.center ↥K) →
      ∀ B : Subgroup X, IsSCp p ⊤ B → B ⊓ Subgroup.centralizer (K : Set X) ≠ ⊥ →
        4 ≤ CFSG.Open.pRank p B → GLATwoLocalRank p X ≤ CFSG.Open.pRank p B →
          (4 ≤ CFSG.Open.pRank p B ∧ IsInGOne p B K) ∨ IsStronglyBalancedIn p B K ∨
            (p = 3 ∧ IsLThreeFour (↥K ⧸ Subgroup.center ↥K) ∧ CFSG.Open.pRank 3 B = 4 ∧
              autOrderIn B K = 9 ∧ InducesInnerIn B K) ∨
            (p = 3 ∧ IsHatON ↥K ∧ CFSG.Open.pRank 3 B = 4 ∧ autOrderIn B K = 27) ∨
            (p = 5 ∧ IsFiTwentyTwo ↥K ∧ CFSG.Open.pRank 5 B = 4)

@[expose] def Input27_1 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Input27_1At X

@[expose] def Input27_1K : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → Input27_1At X

theorem input27_1K_of_input27_1 (h : Input27_1) : Input27_1K := fun X _ _ _ => h X

section Bar

variable {G : Type*} [Group G] [Finite G]

theorem mem_normalizer_of_bar {p : ℕ} {C L : Subgroup G} (hL : GLAPComponent p C L)
    {g : G} (hg : g ∈ C)
    (h : QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨g, hg⟩ ∈
      Subgroup.normalizer (barX p C L : Set (↥C ⧸ GLAPPrimeCore p ↥C))) :
    g ∈ Subgroup.normalizer (L : Set G) := by
  rw [mem_normalizer_iff_gLBConj_eq]
  have hC : GLBConj g C = C := mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer hg)
  have hL' : GLAPComponent p C (GLBConj g L) := by
    have := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_gLBConj hL g
    rwa [hC] at this
  refine glaPComponent_unique hL' hL ?_
  set π := QuotientGroup.mk' (GLAPPrimeCore p ↥C) with hπ
  have hmem := Subgroup.mem_normalizer_iff.1 h
  ext z
  simp only [barX, Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨c, hc, rfl⟩
    have hc' : ((⟨g, hg⟩ * c * ⟨g, hg⟩⁻¹ : ↥C) : G) ∈ L := by
      have := mem_gLBConj.1 hc
      simpa using this
    have h1 : π (⟨g, hg⟩ * c * ⟨g, hg⟩⁻¹) ∈ barX p C L :=
      ⟨_, (Subgroup.mem_subgroupOf).2 hc', rfl⟩
    rw [map_mul, map_mul, map_inv] at h1
    exact ((hmem _).2 h1).elim fun c' hc'' => ⟨c', hc''.1, hc''.2⟩
  · rintro ⟨c, hc, rfl⟩
    have h1 : π ⟨g, hg⟩ * π c * (π ⟨g, hg⟩)⁻¹ ∈ barX p C L := (hmem _).1 ⟨c, hc, rfl⟩
    obtain ⟨c', hc', hc'π⟩ := h1
    have hginv : (⟨g⁻¹, inv_mem hg⟩ : ↥C) = (⟨g, hg⟩ : ↥C)⁻¹ := rfl
    refine ⟨⟨g⁻¹, inv_mem hg⟩ * c' * ⟨g⁻¹, inv_mem hg⟩⁻¹, ?_, ?_⟩
    · rw [mem_gLBConj]
      have h2 := (Subgroup.mem_subgroupOf).1 hc'
      have h3 : g * ((⟨g⁻¹, inv_mem hg⟩ * c' * ⟨g⁻¹, inv_mem hg⟩⁻¹ : ↥C) : G) * g⁻¹ = c' := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [h3]
      exact h2
    · rw [map_mul, map_mul, map_inv, hginv, map_inv, hc'π, ← hπ]
      group


theorem isStronglyLocallyOneBalanced_of_bar {p : ℕ} (hp : p.Prime) {b : G} {B L : Subgroup G}
    (hL : GLAPComponent p (Subgroup.centralizer ({b} : Set G)) L)
    (h : IsStronglyBalancedIn p (barX p (Subgroup.centralizer ({b} : Set G)) B)
      (barX p (Subgroup.centralizer ({b} : Set G)) L)) :
    IsStronglyLocallyOneBalanced p B b L := by
  set C := Subgroup.centralizer ({b} : Set G) with hCdef
  intro S hS hcop hBS
  have hSL : S ≤ Subgroup.normalizer (L : Set G) := hS.trans inf_le_left
  have hSC : S ≤ C := hS.trans inf_le_right
  have key := h (barX p C S) (barX_le_normalizer hSL) ?_ ?_
  · refine Subgroup.commutator_le.2 fun l hl s hs => ?_
    have hlC : l ∈ C := hL.1 hl
    have hsC : s ∈ C := hSC hs
    have hx : ⁅l, s⁆ ∈ L := by
      have h1 := (Subgroup.mem_normalizer_iff.1 (hSL hs) l⁻¹).1 (inv_mem hl)
      have : ⁅l, s⁆ = l * (s * l⁻¹ * s⁻¹) := by
        rw [commutatorElement_def]; group
      rw [this]
      exact L.mul_mem hl h1
    have hxC : ⁅l, s⁆ ∈ C := by
      have : ⁅l, s⁆ = l * s * l⁻¹ * s⁻¹ := by rw [commutatorElement_def]
      rw [this]
      exact C.mul_mem (C.mul_mem (C.mul_mem hlC hsC) (C.inv_mem hlC)) (C.inv_mem hsC)
    have hπ1 : QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨⁅l, s⁆, hxC⟩ = 1 := by
      have hs' : QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨s, hsC⟩ ∈ barX p C S :=
        ⟨_, (Subgroup.mem_subgroupOf).2 hs, rfl⟩
      have hl' : QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨l, hlC⟩ ∈ barX p C L :=
        ⟨_, (Subgroup.mem_subgroupOf).2 hl, rfl⟩
      have hc := Subgroup.mem_centralizer_iff.1 (key hs') _ hl'
      have : (⟨⁅l, s⁆, hxC⟩ : ↥C) = ⟨l, hlC⟩ * ⟨s, hsC⟩ * ⟨l, hlC⟩⁻¹ * ⟨s, hsC⟩⁻¹ := by
        apply Subtype.ext
        simp [commutatorElement_def]
      rw [this, map_mul, map_mul, map_mul, map_inv, map_inv, hc]
      group
    have hmem : ⁅l, s⁆ ∈ GLAPPrimeCoreOf p C :=
      ⟨_, (QuotientGroup.eq_one_iff _).1 hπ1, rfl⟩
    rw [← glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hL.2.1]
    exact ⟨hx, hmem⟩
  · have hcard : Nat.card (S.subgroupOf C) = Nat.card S :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSC).toEquiv
    refine Nat.Coprime.coprime_dvd_right ?_ (hcard ▸ hcop)
    exact Subgroup.card_map_dvd _ _
  · rintro y ⟨⟨c, hc, rfl⟩, hy⟩
    have hcB : (c : G) ∈ B := (Subgroup.mem_subgroupOf).1 hc
    have hcn : (c : G) ∈ Subgroup.normalizer (L : Set G) :=
      mem_normalizer_of_bar hL c.2 (by simpa using hy)
    have hcS : (c : G) ∈ Subgroup.normalizer (S : Set G) := hBS ⟨hcB, hcn⟩
    refine barX_le_normalizer (p := p) (C := C) (S := S) (T := B ⊓ Subgroup.normalizer (L : Set G))
      hBS ?_
    exact ⟨c, (Subgroup.mem_subgroupOf).2 ⟨hcB, hcn⟩, rfl⟩


omit [Finite G] in
theorem isPGroup_of_isElemAbelian' {p : ℕ} {B : Subgroup G} (hB : IsElemAbelian p B) :
    IsPGroup p B := CFSG.Open.IsElemAbelian.isPGroup hB

omit [Finite G] in
theorem bClosure_le_of_le {C B L : Subgroup G} (hBC : B ≤ C) (hLC : L ≤ C) : bClosure B L ≤ C := by
  refine iSup₂_le fun g hg y hy => ?_
  have h1 : g * y * g⁻¹ ∈ C := hLC (mem_gLBConj.1 hy)
  have := C.mul_mem (C.mul_mem (C.inv_mem (hBC hg)) h1) (hBC hg)
  simpa [mul_assoc] using this

omit [Finite G] in
theorem le_normalizer_bClosure (B L : Subgroup G) : B ≤ Subgroup.normalizer (bClosure B L : Set G) := by
  have key : ∀ h ∈ B, ∀ y ∈ bClosure B L, h * y * h⁻¹ ∈ bClosure B L := by
    intro h hh y hy
    have : bClosure B L ≤ GLBConj h (bClosure B L) := by
      refine iSup₂_le fun g hg z hz => ?_
      rw [mem_gLBConj]
      have hz' : g * z * g⁻¹ ∈ L := mem_gLBConj.1 hz
      refine (le_iSup₂_of_le (g * h⁻¹) (B.mul_mem hg (B.inv_mem hh)) le_rfl : GLBConj (g * h⁻¹) L ≤
        bClosure B L) ?_
      rw [mem_gLBConj]
      have : g * h⁻¹ * (h * z * h⁻¹) * (g * h⁻¹)⁻¹ = g * z * g⁻¹ := by group
      rw [this]
      exact hz'
    exact mem_gLBConj.1 (this hy)
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key h hh y, fun hy => ?_⟩
  have := key h⁻¹ (B.inv_mem hh) _ hy
  simpa [mul_assoc] using this


omit [Finite G] in
theorem mem_bClosure_bar_of_mem {p : ℕ} {C B L : Subgroup G} (hBC : B ≤ C) (hLC : L ≤ C) {x : G}
    (hx : x ∈ bClosure B L) :
    ∃ hxC : x ∈ C, QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨x, hxC⟩ ∈
      bClosure (barX p C B) (barX p C L) := by
  set π := QuotientGroup.mk' (GLAPPrimeCore p ↥C) with hπ
  set M := bClosure (barX p C B) (barX p C L) with hM
  have hle : bClosure B L ≤ (M.comap π).map C.subtype := by
    refine iSup₂_le fun g hg y hy => ?_
    have hgl : g * y * g⁻¹ ∈ L := mem_gLBConj.1 hy
    have hgC : g ∈ C := hBC hg
    have hyC : y ∈ C := by
      have := C.mul_mem (C.mul_mem (C.inv_mem hgC) (hLC hgl)) hgC
      simpa [mul_assoc] using this
    refine ⟨⟨y, hyC⟩, ?_, rfl⟩
    show π ⟨y, hyC⟩ ∈ M
    have hmem : π ⟨g, hgC⟩ ∈ barX p C B := ⟨⟨g, hgC⟩, (Subgroup.mem_subgroupOf).2 hg, rfl⟩
    have h1 : π ⟨y, hyC⟩ ∈ GLBConj (π ⟨g, hgC⟩) (barX p C L) := by
      rw [mem_gLBConj]
      refine ⟨⟨g * y * g⁻¹, C.mul_mem (C.mul_mem hgC hyC) (C.inv_mem hgC)⟩,
        (Subgroup.mem_subgroupOf).2 hgl, ?_⟩
      have : (⟨g * y * g⁻¹, C.mul_mem (C.mul_mem hgC hyC) (C.inv_mem hgC)⟩ : ↥C) =
          ⟨g, hgC⟩ * ⟨y, hyC⟩ * ⟨g, hgC⟩⁻¹ := rfl
      rw [this, map_mul, map_mul, map_inv]
    exact (le_iSup₂_of_le (π ⟨g, hgC⟩) hmem le_rfl : GLBConj (π ⟨g, hgC⟩) (barX p C L) ≤ M) h1
  obtain ⟨c, hc, hcx⟩ := hle hx
  have hxC : x ∈ C := hcx ▸ c.2
  refine ⟨hxC, ?_⟩
  have : c = ⟨x, hxC⟩ := Subtype.ext hcx
  rw [this] at hc
  exact hc

omit [Finite G] in
theorem bClosure_bar_le {p : ℕ} {C B L : Subgroup G} :
    bClosure (barX p C B) (barX p C L) ≤ barX p C (bClosure B L) := by
  set π := QuotientGroup.mk' (GLAPPrimeCore p ↥C) with hπ
  refine iSup₂_le fun bb hbb z hz => ?_
  obtain ⟨c, hc, rfl⟩ := hbb
  obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore p ↥C) z
  have hz' : π c * π d * (π c)⁻¹ ∈ barX p C L := mem_gLBConj.1 hz
  obtain ⟨l, hl, hlπ⟩ := hz'
  have hcB : (c : G) ∈ B := (Subgroup.mem_subgroupOf).1 hc
  have hlL : (l : G) ∈ L := (Subgroup.mem_subgroupOf).1 hl
  refine ⟨c⁻¹ * l * c, ?_, ?_⟩
  · show ((c⁻¹ * l * c : ↥C) : G) ∈ bClosure B L
    refine (le_iSup₂_of_le (c : G) hcB le_rfl : GLBConj (c : G) L ≤ bClosure B L) ?_
    rw [mem_gLBConj]
    have : (c : G) * ((c⁻¹ * l * c : ↥C) : G) * (c : G)⁻¹ = l := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [this]
    exact hlL
  · rw [map_mul, map_mul, map_inv, hlπ, ← hπ]
    group


theorem inf_le_coreIn {p : ℕ} (hp : p.Prime) {C Ks B : Subgroup G} {k : ℕ}
    (hB : IsElemAbelian p B) (hcard : Nat.card B = p ^ k) (hk : 4 ≤ k) (hBC : B ≤ C)
    (hBK : B ≤ Subgroup.normalizer (Ks : Set G)) :
    Ks ⊓ GLAPPrimeCoreOf p C ≤ coreIn p 3 B Ks := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set O := GLAPPrimeCoreOf p C with hO
  set Nn : Subgroup G := Ks ⊓ O with hNn
  have hBO : B ≤ Subgroup.normalizer (O : Set G) := hBC.trans (le_normalizer_glaPPrimeCoreOf p C)
  have hBN : B ≤ Subgroup.normalizer (Nn : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h1 := Subgroup.mem_normalizer_iff.1 (hBK hg) y
    have h2 := Subgroup.mem_normalizer_iff.1 (hBO hg) y
    simp only [hNn, Subgroup.mem_inf]
    rw [h1, h2]
  have : B.Normalizes Nn := ⟨hBN⟩
  let : MulDistribMulAction ↥B ↥Nn := Subgroup.conjMulDistribMulActionOfLeNormalizer B Nn hBN
  have : CFSG.IsElementaryAbelian p ↥B :=
    { is_comm := hB.1.is_comm
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (by simpa using hB.2 x x.2) }
  have : Nontrivial ↥B := by
    refine Finite.one_lt_card_iff_nontrivial.1 ?_
    rw [hcard]
    exact Nat.one_lt_pow (by omega) hp.one_lt
  have hpN : ¬ p ∣ Nat.card Nn := by
    intro hd
    refine not_dvd_card_glaPPrimeCoreOf hp C (hd.trans ?_)
    exact Subgroup.card_dvd_of_le inf_le_right
  have hgen := CFSG.SolvableHall.coprime_hyperplane_generation (p := p) (A := ↥B) (H := ↥Nn) hpN
  have hfix : ∀ A : Subgroup ↥B, A.index = p → CFSG.fixedPointSubgroup (↥A) ↥Nn ≤
      (coreIn p 3 B Ks).subgroupOf Nn := by
    intro A hA y hy
    set E : Subgroup G := A.map B.subtype with hE
    have hEB : E ≤ B := Subgroup.map_subtype_le A
    have hAcard : Nat.card A = p ^ (k - 1) := by
      have h1 := A.card_mul_index
      rw [hA, hcard] at h1
      have hk1 : p ^ k = p ^ (k - 1) * p := by
        rw [← pow_succ]; congr 1; omega
      rw [hk1] at h1
      exact Nat.eq_of_mul_eq_mul_right hp.pos h1
    have hEcard : Nat.card E = p ^ (k - 1) := by
      rw [hE, Subgroup.card_map_of_injective B.subtype_injective, hAcard]
    have hEel : IsElemAbelian p E :=
      ⟨⟨⟨fun a b => Subtype.ext (elemAbelian_comm hB (hEB a.2) (hEB b.2))⟩⟩,
        fun x hx => hB.2 x (hEB hx)⟩
    have hrank : 3 ≤ CFSG.Open.pRank p E := by
      rw [pRank_eq_of_card hp hEel hEcard]
      omega
    have hyfix : ∀ e ∈ E, (y : G) * e * (y : G)⁻¹ = e := by
      rintro _ ⟨a, ha, rfl⟩
      have h1 := hy ⟨a, ha⟩
      have h2 : (((⟨a, ha⟩ : ↥A) • y : ↥Nn) : G) = (a : G) * y * (a : G)⁻¹ := by
        rw [Subgroup.smul_def]
        exact Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe B Nn a y
      have h3 : (a : G) * y * (a : G)⁻¹ = y := by rw [← h2]; exact congrArg Subtype.val h1
      have h4 : (a : G) * y = y * a := mul_inv_eq_iff_eq_mul.1 h3
      show (y : G) * (a : G) * (y : G)⁻¹ = a
      exact mul_inv_eq_iff_eq_mul.2 h4.symm
    have hyn : (y : G) ∈ Subgroup.normalizer (E : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro z
      constructor
      · intro hz
        rw [hyfix z hz]
        exact hz
      · intro hz
        have hw := hyfix _ hz
        have h5 := congrArg (fun t => (y : G)⁻¹ * t * (y : G)) hw
        have h6 : (y : G)⁻¹ * ((y : G) * ((y : G) * z * (y : G)⁻¹) * (y : G)⁻¹) * y = (y : G) * z * (y : G)⁻¹ := by
          group
        have h7 : (y : G)⁻¹ * ((y : G) * z * (y : G)⁻¹) * y = z := by group
        rw [h6, h7] at h5
        rw [← h5]
        exact hz
    exact (le_iSup₂_of_le E ⟨hEB, hrank⟩ le_rfl : Ks ⊓ Subgroup.normalizer (E : Set G) ≤
      coreIn p 3 B Ks) ⟨y.2.1, hyn⟩
  intro x hx
  have hxN : (⟨x, hx⟩ : ↥Nn) ∈ (⊤ : Subgroup ↥Nn) := Subgroup.mem_top _
  rw [← hgen] at hxN
  have hle : (⨆ (A : Subgroup ↥B) (_ : A.index = p), CFSG.fixedPointSubgroup (↥A) ↥Nn) ≤
      (coreIn p 3 B Ks).subgroupOf Nn :=
    iSup₂_le fun A hA => hfix A hA
  exact (Subgroup.mem_subgroupOf).1 (hle hxN)


omit [Finite G] in
theorem mem_glaPPrimeCoreOf_iff {p : ℕ} {C : Subgroup G} (c : ↥C) :
    (c : G) ∈ GLAPPrimeCoreOf p C ↔ c ∈ GLAPPrimeCore p ↥C :=
  ⟨fun ⟨c', hc', hv⟩ => by
    have : c' = c := Subtype.ext hv
    rwa [this] at hc', fun h => ⟨c, h, rfl⟩⟩

omit [Finite G] in
theorem mk_eq_iff_glaPPrimeCoreOf {p : ℕ} {C : Subgroup G} (c d : ↥C) :
    QuotientGroup.mk' (GLAPPrimeCore p ↥C) c = QuotientGroup.mk' (GLAPPrimeCore p ↥C) d ↔
      (c : G)⁻¹ * (d : G) ∈ GLAPPrimeCoreOf p C := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
    ← mem_glaPPrimeCoreOf_iff]
  rfl

theorem inf_sup_le_of_normalizes {p : ℕ} (hp : p.Prime) {C Ks B : Subgroup G}
    (hB : IsElemAbelian p B) (hBK : B ≤ Subgroup.normalizer (Ks : Set G)) :
    GLAPPrimeCoreOf p C ⊓ (Ks ⊔ B) ≤ Ks := by
  set T : Subgroup G := Ks ⊔ B with hT
  have hTn : T ≤ Subgroup.normalizer (Ks : Set G) := sup_le Subgroup.le_normalizer hBK
  have hKT : Ks ≤ T := le_sup_left
  have hBT : B ≤ T := le_sup_right
  have hKn : (Ks.subgroupOf T).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKT).2 hTn
  set φ := QuotientGroup.mk' (Ks.subgroupOf T) with hφ
  have htop : Ks.subgroupOf T ⊔ B.subgroupOf T = ⊤ := by
    refine Subgroup.map_injective T.subtype_injective ?_
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hKT,
      Subgroup.map_subgroupOf_eq_of_le hBT, Subgroup.map_top, Subgroup.range_subtype]
  have hpow : ∀ t : ↥T, φ t ^ p = 1 := by
    intro t
    have ht : t ∈ Ks.subgroupOf T ⊔ B.subgroupOf T := htop ▸ Subgroup.mem_top t
    have h1 : φ t ∈ (Ks.subgroupOf T ⊔ B.subgroupOf T).map φ := ⟨t, ht, rfl⟩
    rw [Subgroup.map_sup, hφ, QuotientGroup.map_mk'_self, bot_sup_eq] at h1
    obtain ⟨b, hb, hbt⟩ := h1
    rw [← hbt, ← map_pow]
    have : b ^ p = 1 := Subtype.ext (by
      have := hB.2 (b : G) ((Subgroup.mem_subgroupOf).1 hb)
      simpa using this)
    rw [this, map_one]
  rintro r ⟨hrO, hrT⟩
  obtain ⟨c, hc, hcr⟩ := hrO
  set N := GLAPPrimeCore p ↥C with hN
  have hcm : (c : ↥C) ^ Nat.card N = 1 := by
    have := pow_card_eq_one' (G := ↥N) (x := ⟨c, hc⟩)
    exact congrArg Subtype.val this
  have hrm : ((⟨r, hrT⟩ : ↥T)) ^ Nat.card N = 1 := by
    apply Subtype.ext
    have h := congrArg (fun z : ↥C => (z : G)) hcm
    simp only [Subgroup.coe_pow, OneMemClass.coe_one] at h
    have hcr' : (c : G) = r := hcr
    rw [hcr'] at h
    simpa using h
  have h1 : φ ⟨r, hrT⟩ ^ Nat.card N = 1 := by rw [← map_pow, hrm, map_one]
  have h2 := pow_gcd_eq_one.2 ⟨h1, hpow ⟨r, hrT⟩⟩
  have hcop : Nat.Coprime (Nat.card N) p := by
    have : Fact p.Prime := ⟨hp⟩
    exact (CFSG.pPrimeCore_coprime_card (p := p) (G := ↥C)).symm
  rw [hcop, pow_one] at h2
  have h3 : (⟨r, hrT⟩ : ↥T) ∈ Ks.subgroupOf T := (QuotientGroup.eq_one_iff _).1 h2
  exact (Subgroup.mem_subgroupOf).1 h3


theorem exists_mem_normalizer_of_bar {p : ℕ} (hp : p.Prime) {C Ks B E : Subgroup G}
    (hB : IsElemAbelian p B) (hBK : B ≤ Subgroup.normalizer (Ks : Set G)) (hKC : Ks ≤ C)
    (hBC : B ≤ C) (hEB : E ≤ B) {x : G} (hx : x ∈ Ks)
    (h : QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨x, hKC hx⟩ ∈
      Subgroup.normalizer (barX p C E : Set (↥C ⧸ GLAPPrimeCore p ↥C))) :
    ∃ n ∈ Ks ⊓ Subgroup.normalizer (E : Set G), n⁻¹ * x ∈ GLAPPrimeCoreOf p C := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set O := GLAPPrimeCoreOf p C with hO
  set T : Subgroup G := Ks ⊔ B with hT
  have hTC : T ≤ C := sup_le hKC hBC
  have hKT : Ks ≤ T := le_sup_left
  have hBT : B ≤ T := le_sup_right
  have hET : E ≤ T := hEB.trans hBT
  set N0 : Subgroup ↥T := (O ⊓ T).subgroupOf T with hN0
  have hTn : T ≤ Subgroup.normalizer ((O ⊓ T : Subgroup G) : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h1 := Subgroup.mem_normalizer_iff.1 (le_normalizer_glaPPrimeCoreOf p C (hTC ht)) y
    have h2 := Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer ht) y
    simp only [Subgroup.mem_inf]
    rw [h1, h2]
  have hN0n : N0.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).2 hTn
  have hN0p : ¬ p ∣ Nat.card N0 := by
    intro hd
    refine not_dvd_card_glaPPrimeCoreOf hp C (hd.trans ?_)
    rw [hN0, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hEp : IsPGroup p (E.subgroupOf T) :=
    ((isPGroup_of_isElemAbelian' hB).to_le hEB).of_equiv (Subgroup.subgroupOfEquivOfLe hET).symm
  have hfr := normalizer_map_quotient_le N0 hN0p hEp
  have hstar : ∀ t : ↥T, QuotientGroup.mk' N0 t ∈ (E.subgroupOf T).map (QuotientGroup.mk' N0) ↔
      QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨t, hTC t.2⟩ ∈ barX p C E := by
    intro t
    constructor
    · rintro ⟨e, he, hee⟩
      have h1 : e⁻¹ * t ∈ N0 := QuotientGroup.eq.1 hee
      have h2 : ((e : G))⁻¹ * (t : G) ∈ O := ((Subgroup.mem_subgroupOf).1 h1).1
      have h3 := (mk_eq_iff_glaPPrimeCoreOf (p := p) (⟨e, hTC e.2⟩ : ↥C) ⟨t, hTC t.2⟩).2 h2
      rw [← h3]
      exact ⟨⟨e, hTC e.2⟩, (Subgroup.mem_subgroupOf).2 ((Subgroup.mem_subgroupOf).1 he), rfl⟩
    · rintro ⟨c, hc, hct⟩
      have hcE : (c : G) ∈ E := (Subgroup.mem_subgroupOf).1 hc
      have h2 := (mk_eq_iff_glaPPrimeCoreOf (p := p) c ⟨t, hTC t.2⟩).1 hct
      refine ⟨⟨c, hET hcE⟩, (Subgroup.mem_subgroupOf).2 hcE, ?_⟩
      refine QuotientGroup.eq.2 ?_
      exact (Subgroup.mem_subgroupOf).2 ⟨h2, T.mul_mem (T.inv_mem (hET hcE)) t.2⟩
  have hxn : QuotientGroup.mk' N0 (⟨x, hKT hx⟩ : ↥T) ∈
      Subgroup.normalizer (((E.subgroupOf T).map (QuotientGroup.mk' N0) : Subgroup (↥T ⧸ N0)) :
        Set (↥T ⧸ N0)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective y
    have h1 : QuotientGroup.mk' N0 (⟨x, hKT hx⟩ : ↥T) * QuotientGroup.mk t *
        (QuotientGroup.mk' N0 (⟨x, hKT hx⟩ : ↥T))⁻¹ =
        QuotientGroup.mk' N0 (⟨x, hKT hx⟩ * t * ⟨x, hKT hx⟩⁻¹) := by
      rw [map_mul, map_mul, map_inv]
      rfl
    rw [h1]
    change QuotientGroup.mk' N0 t ∈ _ ↔ QuotientGroup.mk' N0 (⟨x, hKT hx⟩ * t * ⟨x, hKT hx⟩⁻¹) ∈ _
    rw [hstar, hstar]
    have := Subgroup.mem_normalizer_iff.1 h (QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨t, hTC t.2⟩)
    rw [this]
    have h2 : (⟨((⟨x, hKT hx⟩ * t * ⟨x, hKT hx⟩⁻¹ : ↥T) : G),
        hTC (⟨x, hKT hx⟩ * t * ⟨x, hKT hx⟩⁻¹ : ↥T).2⟩ : ↥C) =
        ⟨x, hKC hx⟩ * ⟨t, hTC t.2⟩ * ⟨x, hKC hx⟩⁻¹ := rfl
    rw [h2, map_mul, map_mul, map_inv]
  obtain ⟨nT, hnT, hnTx⟩ := hfr hxn
  have hnT' : (nT : G) ∈ Subgroup.normalizer (E : Set G) := by
    have := normalizer_subgroupOf_eq hET
    rw [this] at hnT
    exact (Subgroup.mem_subgroupOf).1 hnT
  have hr : (nT : G)⁻¹ * x ∈ O ⊓ T := by
    have h1 : nT⁻¹ * (⟨x, hKT hx⟩ : ↥T) ∈ N0 := QuotientGroup.eq.1 hnTx
    exact (Subgroup.mem_subgroupOf).1 h1
  have hrK : (nT : G)⁻¹ * x ∈ Ks := inf_sup_le_of_normalizes hp hB hBK hr
  have hnK : (nT : G) ∈ Ks := by
    have : (nT : G) = x * ((nT : G)⁻¹ * x)⁻¹ := by group
    rw [this]
    exact Ks.mul_mem hx (Ks.inv_mem hrK)
  exact ⟨nT, ⟨hnK, hnT'⟩, hr.1⟩


theorem isInGOne_of_bar {p : ℕ} (hp : p.Prime) {C B L : Subgroup G} {k : ℕ}
    (hB : IsElemAbelian p B) (hcard : Nat.card B = p ^ k) (hk : 4 ≤ k) (hBC : B ≤ C)
    (hLC : L ≤ C) (h : IsInGOne p (barX p C B) (barX p C L)) : IsInGOne p B L := by
  set Ks := bClosure B L with hKs
  have hKC : Ks ≤ C := bClosure_le_of_le hBC hLC
  have hBK : B ≤ Subgroup.normalizer (Ks : Set G) := le_normalizer_bClosure B L
  have hBp : IsPGroup p B := isPGroup_of_isElemAbelian' hB
  have hΓK : coreIn p 3 B Ks ≤ Ks := iSup₂_le fun Q _ => inf_le_left
  unfold IsInGOne at h ⊢
  refine le_antisymm ?_ hΓK
  intro x hx
  obtain ⟨hxC, hxbar⟩ := mem_bClosure_bar_of_mem hBC hLC hx
  rw [h] at hxbar
  have hle : coreIn p 3 (barX p C B) (bClosure (barX p C B) (barX p C L)) ≤
      barX p C (coreIn p 3 B Ks) := by
    refine iSup₂_le fun Q hQ y hy => ?_
    obtain ⟨hyM, hyn⟩ := hy
    have hyK := bClosure_bar_le hyM
    obtain ⟨x', hx'K, rfl⟩ := hyK
    obtain ⟨E, hEB, hEQ, hEr⟩ := exists_le_barX_eq hp hBp hBC hQ.1
    have hx'Ks : (x' : G) ∈ Ks := (Subgroup.mem_subgroupOf).1 hx'K
    rw [← hEQ] at hyn
    obtain ⟨n, ⟨hnK, hnE⟩, hnx⟩ := exists_mem_normalizer_of_bar hp hB hBK hKC hBC hEB hx'Ks hyn
    have hnC : n ∈ C := hKC hnK
    have hnΓ : n ∈ coreIn p 3 B Ks :=
      (le_iSup₂_of_le E ⟨hEB, by rw [hEr]; exact hQ.2⟩ le_rfl : Ks ⊓ Subgroup.normalizer (E : Set G)
        ≤ coreIn p 3 B Ks) ⟨hnK, hnE⟩
    have hπ := (mk_eq_iff_glaPPrimeCoreOf (p := p) ⟨n, hnC⟩ x').2 hnx
    exact ⟨⟨n, hnC⟩, (Subgroup.mem_subgroupOf).2 hnΓ, hπ⟩
  obtain ⟨c, hc, hcx⟩ := hle hxbar
  have hcΓ : (c : G) ∈ coreIn p 3 B Ks := (Subgroup.mem_subgroupOf).1 hc
  have h1 := (mk_eq_iff_glaPPrimeCoreOf (p := p) c ⟨x, hxC⟩).1 hcx
  have h2 : (c : G)⁻¹ * x ∈ Ks ⊓ GLAPPrimeCoreOf p C := ⟨Ks.mul_mem (Ks.inv_mem (hΓK hcΓ)) hx, h1⟩
  have h3 := inf_le_coreIn hp hB hcard hk hBC hBK h2
  have : x = (c : G) * ((c : G)⁻¹ * x) := by group
  rw [this]
  exact (coreIn p 3 B Ks).mul_mem hcΓ h3


theorem pCore_le_center_of_isQuasisimple {p : ℕ} (hp : p.Prime) {Q : Type*} [Group Q] [Finite Q]
    (hQ : CFSG.Open.IsQuasisimple Q) : CFSG.pCore p Q ≤ Subgroup.center Q := by
  have : Fact p.Prime := ⟨hp⟩
  have hs : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hQ.2
  have hnab := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian Q hQ
  have hmap : ((CFSG.pCore p Q).map (QuotientGroup.mk' (Subgroup.center Q))).Normal :=
    (CFSG.pCore_normal (p := p) (G := Q)).map _ (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    ((CFSG.pCore p Q).map (QuotientGroup.mk' (Subgroup.center Q))) with h | h
  · intro n hn
    have : QuotientGroup.mk' (Subgroup.center Q) n ∈
        (CFSG.pCore p Q).map (QuotientGroup.mk' (Subgroup.center Q)) := ⟨n, hn, rfl⟩
    rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    exact this
  · exfalso
    have hpg := IsPGroup.map (CFSG.pCore_isPGroup (p := p) (G := Q)) (QuotientGroup.mk' (Subgroup.center Q))
    rw [h] at hpg
    have hpq : IsPGroup p (Q ⧸ Subgroup.center Q) := hpg.of_equiv Subgroup.topEquiv
    have hnil : Group.IsNilpotent (Q ⧸ Subgroup.center Q) := hpq.isNilpotent
    have hctr : Subgroup.center (Q ⧸ Subgroup.center Q) = ⊤ :=
      (IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (Q ⧸ Subgroup.center Q))).resolve_left
        (Group.IsNilpotent.center_ne_bot _)
    obtain ⟨a, b, hab⟩ := hnab
    exact hab ((Subgroup.mem_center_iff.mp (hctr ▸ Subgroup.mem_top a)) b).symm


theorem isQuasisimple_quot_of_component {p : ℕ} (hp : p.Prime) {C L : Subgroup G}
    (hL : GLAPComponent p C L) : CFSG.Open.IsQuasisimple (↥L ⧸ GLAPPrimeCore p ↥L) :=
  CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
    (quotEquivBarX hp hL.1 hL.2.1).symm (show IsComponentOf (barX p C L) ⊤ from hL.2.2.1).2.2

theorem mem_oPrimePOf_iff {p : ℕ} (hp : p.Prime) {L : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple (↥L ⧸ GLAPPrimeCore p ↥L)) {x : G} :
    x ∈ oPrimePOf p L ↔ x ∈ L ∧ ∀ y ∈ L, x * y * x⁻¹ * y⁻¹ ∈ GLAPPrimeCoreOf p L := by
  constructor
  · rintro ⟨x', hx', rfl⟩
    refine ⟨x'.2, fun y hy => ?_⟩
    have hz : QuotientGroup.mk' (GLAPPrimeCore p ↥L) x' ∈ Subgroup.center _ :=
      pCore_le_center_of_isQuasisimple hp hq hx'
    have hcomm := Subgroup.mem_center_iff.1 hz (QuotientGroup.mk' (GLAPPrimeCore p ↥L) ⟨y, hy⟩)
    have h1 : QuotientGroup.mk' (GLAPPrimeCore p ↥L) (x' * ⟨y, hy⟩ * x'⁻¹ * ⟨y, hy⟩⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hcomm]
      group
    exact ⟨_, (QuotientGroup.eq_one_iff _).1 h1, rfl⟩
  · rintro ⟨hx, hc⟩
    exact mem_oPrimePOf_of_forall_commutator_mem hp hx hc


noncomputable def quotOPrimePEquiv {p : ℕ} (hp : p.Prime) {C L : Subgroup G}
    (hL : GLAPComponent p C L) :
    (↥L ⧸ oPrimeP p ↥L) ≃* (↥(barX p C L) ⧸ Subgroup.center ↥(barX p C L)) := by
  have hq := isQuasisimple_quot_of_component hp hL
  let eQ := quotEquivBarX hp hL.1 hL.2.1
  have hle : GLAPPrimeCore p ↥L ≤ oPrimeP p ↥L := fun x hx => by
    show QuotientGroup.mk' (GLAPPrimeCore p ↥L) x ∈ CFSG.pCore p _
    rw [show QuotientGroup.mk' (GLAPPrimeCore p ↥L) x = 1 from (QuotientGroup.eq_one_iff x).2 hx]
    exact one_mem _
  have hmap : (oPrimeP p ↥L).map (QuotientGroup.mk' (GLAPPrimeCore p ↥L)) =
      CFSG.pCore p (↥L ⧸ GLAPPrimeCore p ↥L) :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
  have hpc : CFSG.pCore p (↥L ⧸ GLAPPrimeCore p ↥L) = Subgroup.center (↥L ⧸ GLAPPrimeCore p ↥L) :=
    le_antisymm (pCore_le_center_of_isQuasisimple hp hq) fun z hz =>
      mem_pCore_of_forall_comm_aux hp fun w => Subgroup.mem_center_iff.1 hz w
  have hcen : (CFSG.pCore p (↥L ⧸ GLAPPrimeCore p ↥L)).map eQ.toMonoidHom =
      Subgroup.center ↥(barX p C L) := by
    rw [hpc]
    exact Subgroup.map_center_eq eQ
  exact ((QuotientGroup.quotientQuotientEquivQuotient (GLAPPrimeCore p ↥L) (oPrimeP p ↥L)
    hle).symm.trans (QuotientGroup.quotientMulEquivOfEq hmap)).trans
    (QuotientGroup.congr _ _ eQ hcen)

omit [Finite G] in
theorem isHatON_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsHatON X) : IsHatON Y := by
  obtain ⟨hc, hcard, ⟨f⟩⟩ := h
  have hcen : (Subgroup.center X).map e.toMonoidHom = Subgroup.center Y :=
    Subgroup.map_center_eq e
  refine ⟨?_, ?_, ⟨(QuotientGroup.congr _ _ e hcen).symm.trans f⟩⟩
  · have h1 := congrArg (Subgroup.map e.toMonoidHom) hc
    rw [commutator, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective e.toMonoidHom e.surjective] at h1
    rw [commutator]
    exact h1
  · rw [← hcen, Subgroup.card_map_of_injective e.injective, hcard]

omit [Finite G] in
theorem isLThreeFour_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsLThreeFour X) : IsLThreeFour Y := by
  obtain ⟨K, hK, hf, h4, ⟨f⟩⟩ := h
  exact ⟨K, hK, hf, h4, ⟨e.symm.trans f⟩⟩


omit [Finite G] in
theorem normalizer_le_normalizer_glaPPrimeCoreOf (p : ℕ) (J : Subgroup G) :
    Subgroup.normalizer (J : Set G) ≤ Subgroup.normalizer (GLAPPrimeCoreOf p J : Set G) := by
  intro g hg
  rw [mem_normalizer_iff_gLBConj_eq] at hg ⊢
  rw [← glaPPrimeCoreOf_gLBConj, hg]

theorem mem_inf_normalizer_bar_iff {p : ℕ} {C B L : Subgroup G} (hL : GLAPComponent p C L)
    (y : ↥C ⧸ GLAPPrimeCore p ↥C) :
    y ∈ barX p C B ⊓ Subgroup.normalizer (barX p C L : Set (↥C ⧸ GLAPPrimeCore p ↥C)) ↔
      ∃ c : ↥C, (c : G) ∈ B ⊓ Subgroup.normalizer (L : Set G) ∧
        QuotientGroup.mk' (GLAPPrimeCore p ↥C) c = y := by
  constructor
  · rintro ⟨⟨c, hc, rfl⟩, hy⟩
    exact ⟨c, ⟨(Subgroup.mem_subgroupOf).1 hc, mem_normalizer_of_bar hL c.2 hy⟩, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    refine ⟨⟨c, (Subgroup.mem_subgroupOf).2 hc.1, rfl⟩, ?_⟩
    exact barX_le_normalizer (p := p) (C := C) (S := L) (T := B ⊓ Subgroup.normalizer (L : Set G))
      inf_le_right ⟨c, (Subgroup.mem_subgroupOf).2 hc, rfl⟩

theorem commutator_mem_glaPPrimeCoreOf_iff {p : ℕ} (hp : p.Prime) {C L : Subgroup G}
    (hL : GLAPComponent p C L) {c x : ↥C} (hc : (c : G) ∈ Subgroup.normalizer (L : Set G))
    (hx : (x : G) ∈ L) :
    (x : G) * c * (x : G)⁻¹ * (c : G)⁻¹ ∈ GLAPPrimeCoreOf p L ↔
      QuotientGroup.mk' (GLAPPrimeCore p ↥C) x * QuotientGroup.mk' (GLAPPrimeCore p ↥C) c =
        QuotientGroup.mk' (GLAPPrimeCore p ↥C) c * QuotientGroup.mk' (GLAPPrimeCore p ↥C) x := by
  have hmemL : (x : G) * c * (x : G)⁻¹ * (c : G)⁻¹ ∈ L := by
    have h1 := (Subgroup.mem_normalizer_iff.1 hc (x : G)⁻¹).1 (inv_mem hx)
    have : (x : G) * c * (x : G)⁻¹ * (c : G)⁻¹ = x * ((c : G) * (x : G)⁻¹ * (c : G)⁻¹) := by
      group
    rw [this]
    exact L.mul_mem hx h1
  rw [← glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hL.2.1, Subgroup.mem_inf, and_iff_right hmemL]
  have h2 : (((x * c * x⁻¹ * c⁻¹ : ↥C)) : G) = (x : G) * c * (x : G)⁻¹ * (c : G)⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  have h3 : ∀ z : ↥C, z ∈ GLAPPrimeCore p ↥C ↔ QuotientGroup.mk' (GLAPPrimeCore p ↥C) z = 1 :=
    fun z => (QuotientGroup.eq_one_iff z).symm
  rw [← h2, mem_glaPPrimeCoreOf_iff, h3, map_mul, map_mul, map_mul,
    map_inv, map_inv, ← commutatorElement_def, commutatorElement_eq_one_iff_mul_comm]


theorem mem_centralizerQuot_iff_bar {p : ℕ} (hp : p.Prime) {C L : Subgroup G}
    (hL : GLAPComponent p C L) {c : ↥C} (hc : (c : G) ∈ Subgroup.normalizer (L : Set G)) :
    (c : G) ∈ centralizerQuot L (GLAPPrimeCoreOf p L) ↔
      QuotientGroup.mk' (GLAPPrimeCore p ↥C) c ∈
        Subgroup.centralizer (barX p C L : Set (↥C ⧸ GLAPPrimeCore p ↥C)) := by
  constructor
  · rintro ⟨-, -, hcq⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨x, hx, rfl⟩
    have hx' : (x : G) ∈ L := (Subgroup.mem_subgroupOf).1 hx
    exact (commutator_mem_glaPPrimeCoreOf_iff hp hL hc hx').1 (hcq x hx')
  · intro h
    refine ⟨hc, normalizer_le_normalizer_glaPPrimeCoreOf p L hc, fun x hx => ?_⟩
    refine (commutator_mem_glaPPrimeCoreOf_iff hp hL (x := ⟨x, hL.1 hx⟩) hc hx).2 ?_
    exact Subgroup.mem_centralizer_iff.1 h _ ⟨⟨x, hL.1 hx⟩, (Subgroup.mem_subgroupOf).2 hx, rfl⟩

theorem conj_mem_oPrimePOf {p : ℕ} (hp : p.Prime) {L : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple (↥L ⧸ GLAPPrimeCore p ↥L)) {g x : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) (hx : x ∈ oPrimePOf p L) :
    g * x * g⁻¹ ∈ oPrimePOf p L := by
  obtain ⟨hxL, hcomm⟩ := (mem_oPrimePOf_iff hp hq).1 hx
  refine (mem_oPrimePOf_iff hp hq).2 ⟨(Subgroup.mem_normalizer_iff.1 hg x).1 hxL, fun y hy => ?_⟩
  have hy' : g⁻¹ * y * g ∈ L := by
    refine (Subgroup.mem_normalizer_iff.1 hg (g⁻¹ * y * g)).2 ?_
    have : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
    rw [this]
    exact hy
  have h1 := hcomm _ hy'
  have h2 := (Subgroup.mem_normalizer_iff.1 (normalizer_le_normalizer_glaPPrimeCoreOf p L hg) _).1 h1
  have : g * x * g⁻¹ * y * (g * x * g⁻¹)⁻¹ * y⁻¹ =
      g * (x * (g⁻¹ * y * g) * x⁻¹ * (g⁻¹ * y * g)⁻¹) * g⁻¹ := by group
  rw [this]
  exact h2

theorem centralizerQuot_oPrimePOf_le {p : ℕ} (hp : p.Prime) {L : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple (↥L ⧸ GLAPPrimeCore p ↥L)) {c : G}
    (hc : c ∈ centralizerQuot L (oPrimePOf p L)) :
    c ∈ centralizerQuot L (GLAPPrimeCoreOf p L) := by
  obtain ⟨hcN, -, hcomm⟩ := hc
  have : Group.IsPerfect (↥L ⧸ GLAPPrimeCore p ↥L) := ⟨hq.1⟩
  set γ : ↥(Subgroup.normalizer (L : Set G)) := ⟨c, hcN⟩ with hγ
  have hs : ∀ y : ↥L, ((L.normalizerMonoidHom γ y : ↥L) : G) = c * y * c⁻¹ := fun _ => rfl
  have hcen : ∀ u : ↥L ⧸ GLAPPrimeCore p ↥L, u⁻¹ * (barAut p L γ).toMonoidHom u ∈
      Subgroup.center (↥L ⧸ GLAPPrimeCore p ↥L) := by
    intro u
    induction u using QuotientGroup.induction_on with | H x => ?_
    have hx := hcomm (x : G)⁻¹ (L.inv_mem x.2)
    obtain ⟨w, hw, hwv⟩ := hx
    have hwx : w = x⁻¹ * L.normalizerMonoidHom γ x := by
      apply Subtype.ext
      rw [show ((w : ↥L) : G) = (x : G)⁻¹ * c * ((x : G)⁻¹)⁻¹ * c⁻¹ from hwv]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hs]
      group
    have h1 : (QuotientGroup.mk x)⁻¹ * (barAut p L γ).toMonoidHom (QuotientGroup.mk x) =
        QuotientGroup.mk' (GLAPPrimeCore p ↥L) w := by
      rw [hwx, map_mul, map_inv]
      exact congrArg _ (barAut_mk p L γ x)
    rw [h1]
    exact pCore_le_center_of_isQuasisimple hp hq hw
  have hid := CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_id_of_central_displacement
    (barAut p L γ).toMonoidHom hcen
  refine ⟨hcN, normalizer_le_normalizer_glaPPrimeCoreOf p L hcN, fun x hx => ?_⟩
  have h1 := congrArg (fun φ : (↥L ⧸ GLAPPrimeCore p ↥L) →* (↥L ⧸ GLAPPrimeCore p ↥L) =>
    φ (QuotientGroup.mk ⟨x⁻¹, L.inv_mem hx⟩)) hid
  simp only [MulEquiv.coe_toMonoidHom, MonoidHom.id_apply] at h1
  rw [barAut_mk] at h1
  have h2 := QuotientGroup.eq.1 h1.symm
  refine ⟨_, h2, ?_⟩
  show ((((⟨x⁻¹, L.inv_mem hx⟩ : ↥L)⁻¹ * L.normalizerMonoidHom γ ⟨x⁻¹, L.inv_mem hx⟩ : ↥L)) : G) = _
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, hs]
  group


theorem centralizerQuot_le_oPrimePOf {p : ℕ} (hp : p.Prime) {L : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple (↥L ⧸ GLAPPrimeCore p ↥L)) {c : G}
    (hc : c ∈ centralizerQuot L (GLAPPrimeCoreOf p L)) :
    c ∈ centralizerQuot L (oPrimePOf p L) := by
  obtain ⟨hcN, -, hcomm⟩ := hc
  have hinv : c⁻¹ ∈ Subgroup.normalizer (L : Set G) := inv_mem hcN
  refine ⟨hcN, ?_, fun x hx => ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro z
    refine ⟨fun hz => conj_mem_oPrimePOf hp hq hcN hz, fun hz => ?_⟩
    have := conj_mem_oPrimePOf hp hq hinv hz
    simpa [mul_assoc] using this
  · have h1 := hcomm x hx
    have hL1 : x * c * x⁻¹ * c⁻¹ ∈ L := by
      have h2 := (Subgroup.mem_normalizer_iff.1 hcN x⁻¹).1 (inv_mem hx)
      have : x * c * x⁻¹ * c⁻¹ = x * (c * x⁻¹ * c⁻¹) := by group
      rw [this]
      exact L.mul_mem hx h2
    refine (mem_oPrimePOf_iff hp hq).2 ⟨hL1, fun y hy => ?_⟩
    have hyn := le_normalizer_glaPPrimeCoreOf p L hy
    have h3 := (Subgroup.mem_normalizer_iff.1 hyn (x * c * x⁻¹ * c⁻¹)⁻¹).1 (inv_mem h1)
    have : x * c * x⁻¹ * c⁻¹ * y * (x * c * x⁻¹ * c⁻¹)⁻¹ * y⁻¹ =
        (x * c * x⁻¹ * c⁻¹) * (y * (x * c * x⁻¹ * c⁻¹)⁻¹ * y⁻¹) := by group
    rw [this]
    exact GLAPPrimeCoreOf p L |>.mul_mem h1 h3

theorem mem_centralizerQuot_oPrimePOf_iff {p : ℕ} (hp : p.Prime) {L : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple (↥L ⧸ GLAPPrimeCore p ↥L)) {c : G} :
    c ∈ centralizerQuot L (oPrimePOf p L) ↔ c ∈ centralizerQuot L (GLAPPrimeCoreOf p L) :=
  ⟨centralizerQuot_oPrimePOf_le hp hq, centralizerQuot_le_oPrimePOf hp hq⟩

theorem relIndex_centralizerQuot_eq_autOrderIn {p : ℕ} (hp : p.Prime) {C B L : Subgroup G}
    (hBC : B ≤ C) (hL : GLAPComponent p C L) :
    (centralizerQuot L (GLAPPrimeCoreOf p L)).relIndex (B ⊓ Subgroup.normalizer (L : Set G)) =
      autOrderIn (barX p C B) (barX p C L) := by
  set N : Subgroup G := B ⊓ Subgroup.normalizer (L : Set G) with hN
  have hNC : N ≤ C := inf_le_left.trans hBC
  let f₀ : ↥N →* ↥C ⧸ GLAPPrimeCore p ↥C :=
    (QuotientGroup.mk' (GLAPPrimeCore p ↥C)).comp (Subgroup.inclusion hNC)
  have hrange : f₀.range = barX p C B ⊓ Subgroup.normalizer
      (barX p C L : Set (↥C ⧸ GLAPPrimeCore p ↥C)) := by
    ext y
    rw [mem_inf_normalizer_bar_iff hL, MonoidHom.mem_range]
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨⟨c, hNC c.2⟩, c.2, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨⟨c, hc⟩, rfl⟩
  have hcomap : (Subgroup.centralizer (barX p C L : Set (↥C ⧸ GLAPPrimeCore p ↥C))).comap f₀ =
      (centralizerQuot L (GLAPPrimeCoreOf p L)).subgroupOf N := by
    ext c
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    exact (mem_centralizerQuot_iff_bar hp hL (c := ⟨c, hNC c.2⟩) c.2.2).symm
  unfold autOrderIn
  rw [← hrange, MonoidHom.range_eq_map, ← Subgroup.relIndex_comap, hcomap]
  rw [Subgroup.relIndex_top_right]
  rfl


theorem isCatalogGroup_center_quotient_of_isKGroup {Y : Type*} [Group Y]
    (hY : CFSG.Open.IsKGroup Y) (hq : CFSG.Open.IsQuasisimple Y) :
    IsCatalogGroup (Y ⧸ Subgroup.center Y) := by
  have hsimple : IsSimpleGroup (Y ⧸ Subgroup.center Y) := hq.2
  have hnab : ∃ a b : Y ⧸ Subgroup.center Y, a * b ≠ b * a :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian Y hq
  let e : (↥(⊤ : Subgroup Y) ⧸ (Subgroup.center Y).subgroupOf ⊤) ≃* (Y ⧸ Subgroup.center Y) :=
    QuotientGroup.congr _ _ Subgroup.topEquiv (by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨⟨x, Subgroup.mem_top x⟩, hx, rfl⟩)
  have : ((Subgroup.center Y).subgroupOf ⊤).Normal := Subgroup.Normal.subgroupOf inferInstance ⊤
  have hcat' := hY ⊤ (Subgroup.center Y) le_top (e.isSimpleGroup_congr.2 hsimple)
    (by
      obtain ⟨a, b, hab⟩ := hnab
      exact ⟨e.symm a, e.symm b, fun hc => hab (by simpa using congrArg e hc)⟩)
  obtain ⟨i, ⟨f⟩⟩ := hcat'
  exact ⟨i, ⟨e.symm.trans f⟩⟩

end Bar


theorem lemma31_of_input27_1K (h : Input27_1K) : Lemma31 := by
  intro G _ _ m p hS B hB hsc b hb hb1 L hL
  have hp : p.Prime := hS.prime
  have hp2 : p ≠ 2 := hS.ne_two
  have : Fact p.Prime := ⟨hp⟩
  set C := Subgroup.centralizer ({b} : Set G) with hCdef
  have hBC : B ≤ C := le_centralizer_of_mem hB.1 hb
  have hBp : IsPGroup p B := isPGroup_of_isElemAbelian' hB.1
  have hCtop : C ≠ ⊤ := by
    intro htop
    have hcenter : b ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have : g ∈ C := htop ▸ Subgroup.mem_top g
      exact (Subgroup.mem_centralizer_singleton_iff.1 this)
    have := hS.simple
    have hcbot : Subgroup.center G = ⊥ := by
      rcases (inferInstance : (Subgroup.center G).Normal).eq_bot_or_eq_top with h | h
      · exact h
      · obtain ⟨a, c, hac⟩ := hS.nonabelian
        exact absurd (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top c : c ∈ Subgroup.center G) a)
          hac
    rw [hcbot, Subgroup.mem_bot] at hcenter
    exact hb1 hcenter
  have hN : ¬ p ∣ Nat.card (GLAPPrimeCore p ↥C) :=
    (Nat.Prime.coprime_iff_not_dvd hp).1 CFSG.pPrimeCore_coprime_card
  have hcardB : Nat.card B = p ^ m := by
    have := hB.2.1
    rwa [hS.rank_eq] at this
  have hrankB : CFSG.Open.pRank p B = m := pRank_eq_of_card hp hB.1 hcardB
  have hrankBar : CFSG.Open.pRank p (barX p C B) = m := by
    rw [rank_barX_of_isPGroup hp hBp hBC, hrankB]
  have hm4 : 4 ≤ m := hS.four_le
  have hKcomp : GLAPComponent p (⊤ : Subgroup (↥C ⧸ GLAPPrimeCore p ↥C)) (barX p C L) := by
    have hker : Nat.Coprime p (Nat.card ↥((⊤ : Subgroup ↥C) ⊓
        (QuotientGroup.mk' (GLAPPrimeCore p ↥C)).ker)) := by
      rw [top_inf_eq, QuotientGroup.ker_mk']
      exact CFSG.pPrimeCore_coprime_card
    have := glaPComponent_map hp (QuotientGroup.mk' (GLAPPrimeCore p ↥C)) hker (glaPComponent_top hL)
    rwa [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at this
  have hKq : CFSG.Open.IsQuasisimple ↥(barX p C L) :=
    (show IsComponentOf (barX p C L) ⊤ from hL.2.2.1).2.2
  have hXK : CFSG.Open.IsKGroup (↥C ⧸ GLAPPrimeCore p ↥C) :=
    isKGroup_quotient' (isKGroup_of_isKProper hS.kProper hCtop) _
  have hKcat : IsCatalogGroup (↥(barX p C L) ⧸ Subgroup.center ↥(barX p C L)) :=
    isCatalogGroup_center_quotient_of_isKGroup (isKGroup_subgroup' hXK _) hKq
  have hBsc : IsSCp p ⊤ (barX p C B) :=
    isSCp_map_quotient (GLAPPrimeCore p ↥C) hN (isSCp_subgroupOf hsc hBC)
  have hCBne : barX p C B ⊓ Subgroup.centralizer (barX p C L : Set (↥C ⧸ GLAPPrimeCore p ↥C)) ≠ ⊥ := by
    intro hbot
    have hbC : b ∈ C := hBC hb
    have hmem : QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨b, hbC⟩ ∈
        barX p C B ⊓ Subgroup.centralizer (barX p C L : Set (↥C ⧸ GLAPPrimeCore p ↥C)) := by
      refine ⟨⟨⟨b, hbC⟩, (Subgroup.mem_subgroupOf).2 hb, rfl⟩, ?_⟩
      refine Subgroup.mem_centralizer_iff.2 fun k hk => ?_
      obtain ⟨x, hx, rfl⟩ := hk
      have hxb : (x : G) * b = b * x := by
        have := hL.1 ((Subgroup.mem_subgroupOf).1 hx)
        exact Subgroup.mem_centralizer_singleton_iff.1 this
      show QuotientGroup.mk' (GLAPPrimeCore p ↥C) x *
          QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨b, hbC⟩ =
        QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨b, hbC⟩ * QuotientGroup.mk' (GLAPPrimeCore p ↥C) x
      rw [← map_mul, ← map_mul]
      exact congrArg _ (Subtype.ext hxb)
    rw [hbot, Subgroup.mem_bot] at hmem
    have hinj := injective_barX_comp hp hBp hBC
    have h1 : ((QuotientGroup.mk' (GLAPPrimeCore p ↥C)).comp (B.subgroupOf C).subtype)
        ⟨⟨b, hbC⟩, (Subgroup.mem_subgroupOf).2 hb⟩ =
        ((QuotientGroup.mk' (GLAPPrimeCore p ↥C)).comp (B.subgroupOf C).subtype) 1 := by
      simpa using hmem
    have := hinj h1
    have h2 := congrArg (fun z : ↥(B.subgroupOf C) => ((z : ↥C) : G)) this
    exact hb1 (by simpa using h2)
  have hX := h (↥C ⧸ GLAPPrimeCore p ↥C) hXK p hp hp2 (glaPPrimeCore_quotient_eq_bot hp) (barX p C L)
    hKcomp hKcat (barX p C B) hBsc hCBne (by rw [hrankBar]; exact hm4)
    (by
      rw [hrankBar]
      refine (glaTwoLocalRank_quotient_le hp hp2 (GLAPPrimeCore p ↥C) hN).trans ?_
      refine (CFSG.LocalAnalysis.GLTheoremB.glaTwoLocalRank_subgroup_le hp.one_lt C).trans ?_
      exact hS.rank_eq.le)
  have hq := isQuasisimple_quot_of_component hp hL
  rcases hX with ⟨-, ha⟩ | hb' | ⟨hp3, hL3, hr3, ho9, hin⟩ | ⟨hp3, hON, hr3, ho27⟩ |
    ⟨hp5, hFi, hr5⟩
  · exact Or.inr (Or.inl (isInGOne_of_bar hp hB.1 hcardB hm4 hBC hL.1 ha))
  · exact Or.inl (isStronglyLocallyOneBalanced_of_bar hp hL hb')
  · subst hp3
    have hrk : GLATwoLocalRank 3 G = 4 := hS.rank_eq.trans (hrankBar.symm.trans hr3)
    refine Or.inr (Or.inr (Or.inl ⟨rfl, hrk,
      isLThreeFour_of_mulEquiv (quotOPrimePEquiv hp hL).symm hL3, ?_, ?_⟩))
    · have hsub : (centralizerQuot L (oPrimePOf 3 L)).subgroupOf (B ⊓ Subgroup.normalizer (L : Set G)) =
          (centralizerQuot L (GLAPPrimeCoreOf 3 L)).subgroupOf
            (B ⊓ Subgroup.normalizer (L : Set G)) := by
        ext c
        simp only [Subgroup.mem_subgroupOf]
        exact mem_centralizerQuot_oPrimePOf_iff hp hq
      have : (centralizerQuot L (oPrimePOf 3 L)).relIndex (B ⊓ Subgroup.normalizer (L : Set G)) =
          (centralizerQuot L (GLAPPrimeCoreOf 3 L)).relIndex
            (B ⊓ Subgroup.normalizer (L : Set G)) := by
        unfold Subgroup.relIndex
        rw [hsub]
      rw [this, relIndex_centralizerQuot_eq_autOrderIn hp hBC hL]
      exact ho9
    · intro b' hb'N
      have hb'C : b' ∈ C := hBC hb'N.1
      have hy : QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) ⟨b', hb'C⟩ ∈ barX 3 C B ⊓
          Subgroup.normalizer (barX 3 C L : Set (↥C ⧸ GLAPPrimeCore 3 ↥C)) :=
        (mem_inf_normalizer_bar_iff hL _).2 ⟨⟨b', hb'C⟩, hb'N, rfl⟩
      obtain ⟨k, hk, hkc⟩ := hin _ hy
      obtain ⟨l, hl, rfl⟩ := hk
      have hlL : (l : G) ∈ L := (Subgroup.mem_subgroupOf).1 hl
      refine ⟨l, hlL, ?_⟩
      rw [mem_centralizerQuot_oPrimePOf_iff hp hq]
      have hc : ((l⁻¹ * ⟨b', hb'C⟩ : ↥C) : G) ∈ Subgroup.normalizer (L : Set G) :=
        (Subgroup.normalizer (L : Set G)).mul_mem
          ((Subgroup.normalizer (L : Set G)).inv_mem (Subgroup.le_normalizer hlL)) hb'N.2
      exact (mem_centralizerQuot_iff_bar hp hL hc).2 (by rw [map_mul, map_inv]; exact hkc)
  · subst hp3
    have hrk : GLATwoLocalRank 3 G = 4 := hS.rank_eq.trans (hrankBar.symm.trans hr3)
    refine Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hrk,
      isHatON_of_mulEquiv (quotEquivBarX hp hL.1 hL.2.1).symm hON, ?_⟩)))
    rw [relIndex_centralizerQuot_eq_autOrderIn hp hBC hL]
    exact ho27
  · subst hp5
    have hrk : GLATwoLocalRank 5 G = 4 := hS.rank_eq.trans (hrankBar.symm.trans hr5)
    obtain ⟨f⟩ := hFi
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, hrk,
      ⟨(quotEquivBarX hp hL.1 hL.2.1).trans f⟩⟩)))

theorem lemma31_of_input27_1 (h : Input27_1) : Lemma31 :=
  lemma31_of_input27_1K (input27_1K_of_input27_1 h)

end CFSG.HardMathSupport.Solomon.LocalBalance
