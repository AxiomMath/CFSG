module

public import CFSG.RankThree.PartOne.KE8F.HyperGen
public import CFSG.GroupTheory.PCore.PrimeSetCore
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Input312

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1211

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma1211
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)
open scoped commutatorElement

section Sylow

variable {G : Type} [Group G] [Finite G]

theorem isPGroup_subgroupOf {p : ℕ} {X R : Subgroup G} (hRX : R ≤ X) (hR : IsPGroup p ↥R) :
    IsPGroup p ↥(R.subgroupOf X) :=
  hR.of_equiv (Subgroup.subgroupOfEquivOfLe hRX).symm

theorem exists_sylow_of_isSylowIn {p : ℕ} [Fact p.Prime] {X R : Subgroup G}
    (hR : IsSylowIn p X R) : ∃ S : Sylow p ↥X, (S : Subgroup ↥X).map X.subtype = R := by
  obtain ⟨S, hS⟩ := (isPGroup_subgroupOf hR.1 hR.2.1).exists_le_sylow
  refine ⟨S, hR.2.2 _ (Subgroup.map_subtype_le _) (S.isPGroup'.map _) ?_⟩
  intro r hr
  exact ⟨⟨r, hR.1 hr⟩, hS (Subgroup.mem_subgroupOf.2 hr), rfl⟩

theorem pPrimePCore_le_sup {p : ℕ} [Fact p.Prime] {X R : Subgroup G} (hR : IsSylowIn p X R) :
    pPrimePCore p X ≤ GLAPPrimeCoreOf p X ⊔ R := by
  obtain ⟨S, hS⟩ := exists_sylow_of_isSylowIn hR
  have hπ : Function.Surjective (QuotientGroup.mk' (GLAPPrimeCore p ↥X)) :=
    QuotientGroup.mk'_surjective _
  have hle : CFSG.pCore p (↥X ⧸ GLAPPrimeCore p ↥X) ≤
      (S : Subgroup ↥X).map (QuotientGroup.mk' (GLAPPrimeCore p ↥X)) :=
    CFSG.pCore_isPGroup.le_sylow_of_normal (S.mapSurjective hπ)
  have h2 : (CFSG.pCore p (↥X ⧸ GLAPPrimeCore p ↥X)).comap
      (QuotientGroup.mk' (GLAPPrimeCore p ↥X)) ≤ (S : Subgroup ↥X) ⊔ GLAPPrimeCore p ↥X := by
    refine (Subgroup.comap_mono hle).trans ?_
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
  have h3 := Subgroup.map_mono (f := X.subtype) h2
  rw [Subgroup.map_sup, hS] at h3
  unfold pPrimePCore
  refine h3.trans ?_
  rw [sup_comm]
  exact le_rfl

theorem le_pRank_of_card {p : ℕ} [Fact p.Prime] {H E : Subgroup G} (hEH : E ≤ H)
    (hE : IsElemAbelian p E) {k : ℕ} (hk : Nat.card E = p ^ k) : k ≤ CFSG.Open.pRank p H := by
  unfold CFSG.Open.pRank
  apply le_csSup
  · refine ⟨Nat.card H, ?_⟩
    rintro j ⟨F, hFH, -, hFj⟩
    have h1 : p ^ j ≤ Nat.card H := by
      rw [← hFj]
      exact Subgroup.card_le_of_le hFH
    exact le_trans (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le h1
  · exact ⟨E, hEH, hE, hk⟩

theorem card_gLBConj (g : G) (H : Subgroup G) : Nat.card ↥(GLBConj g H) = Nat.card ↥H := by
  unfold GLBConj
  exact Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective

theorem isPGroup_gLBConj {p : ℕ} (g : G) {H : Subgroup G} (hH : IsPGroup p ↥H) :
    IsPGroup p ↥(GLBConj g H) := by
  unfold GLBConj
  exact hH.map _

theorem isElemAbelian_gLBConj {p : ℕ} (g : G) {H : Subgroup G} (hH : IsElemAbelian p H) :
    IsElemAbelian p (GLBConj g H) := by
  unfold GLBConj
  exact hH.map _

theorem gLBConj_self {g : G} {H : Subgroup G} (hg : g ∈ H) : GLBConj g H = H :=
  gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer hg)

theorem le_cg_of_mem_centerOf {R : Subgroup G} {z : G} (hz : z ∈ centerOf R) : R ≤ Cg z := by
  intro r hr
  rw [Cg, Subgroup.mem_centralizer_iff]
  intro g hg
  rw [Set.mem_singleton_iff] at hg
  rw [hg]
  exact (((mem_centerOf_iff' R z).1 hz).2 r hr).symm

theorem exists_gLBConj_eq {p : ℕ} [Fact p.Prime] {X R S : Subgroup G} (hR : IsSylowIn p X R)
    (hS : IsSylowIn p X S) : ∃ x ∈ X, GLBConj x S = R := by
  obtain ⟨x, hxX, T, hTp, hTX, hRT, hST⟩ := exists_conj_le_pGroup' hR.1 hR.2.1 hS.1 hS.2.1
  have hTR : T = R := hR.2.2 T hTX hTp hRT
  rw [hTR] at hST
  refine ⟨x, hxX, ?_⟩
  have h1 : S ≤ GLBConj x⁻¹ R := by
    have := gLBConj_mono x⁻¹ hST
    rwa [gLBConj_inv_gLBConj] at this
  have h2 : GLBConj x⁻¹ R ≤ X := by
    have := gLBConj_mono x⁻¹ hR.1
    rwa [gLBConj_self (X.inv_mem hxX)] at this
  have h3 : GLBConj x⁻¹ R = S := hS.2.2 _ h2 (isPGroup_gLBConj _ hR.2.1) h1
  rw [← h3, gLBConj_gLBConj_inv]

theorem isSylowIn_inf {p : ℕ} [Fact p.Prime] {X O R : Subgroup G} (hR : IsSylowIn p X R)
    (hOX : O ≤ X) (hXO : X ≤ Subgroup.normalizer (O : Set G)) : IsSylowIn p O (R ⊓ O) := by
  refine ⟨inf_le_right, isPGroup_of_le' hR.2.1 inf_le_left, fun R' hR'O hR'p hle => ?_⟩
  obtain ⟨x, hxX, T, hTp, hTX, hRT, hR'T⟩ :=
    exists_conj_le_pGroup' hR.1 hR.2.1 (hR'O.trans hOX) hR'p
  have hTR : T = R := hR.2.2 T hTX hTp hRT
  rw [hTR] at hR'T
  have hO : GLBConj x O = O := gLBConj_eq_of_mem_normalizer (hXO hxX)
  have h1 : GLBConj x R' ≤ R ⊓ O := by
    refine le_inf hR'T ?_
    have := gLBConj_mono x hR'O
    rwa [hO] at this
  have h2 : Nat.card ↥R' ≤ Nat.card ↥(R ⊓ O) := by
    rw [← card_gLBConj x R']
    exact Subgroup.card_le_of_le h1
  exact (Subgroup.eq_of_le_of_card_ge hle h2).symm

theorem le_sup_normalizer_inf {p : ℕ} [Fact p.Prime] {X O R : Subgroup G} (hR : IsSylowIn p X R)
    (hOX : O ≤ X) (hXO : X ≤ Subgroup.normalizer (O : Set G)) :
    X ≤ O ⊔ Subgroup.normalizer ((R ⊓ O : Subgroup G) : Set G) := by
  intro c hc
  have hS := isSylowIn_inf hR hOX hXO
  have hO : GLBConj c O = O := gLBConj_eq_of_mem_normalizer (hXO hc)
  have hcO : GLBConj c (R ⊓ O) ≤ O := by
    have := gLBConj_mono c (inf_le_right : R ⊓ O ≤ O)
    rwa [hO] at this
  have hcS : IsSylowIn p O (GLBConj c (R ⊓ O)) := by
    refine ⟨hcO, isPGroup_gLBConj c hS.2.1, fun R' hR'O hR'p hle => ?_⟩
    have h1 : GLBConj c⁻¹ R' ≤ X := by
      have := gLBConj_mono c⁻¹ (hR'O.trans hOX)
      rwa [gLBConj_self (X.inv_mem hc)] at this
    have hc' : c⁻¹ ∈ Subgroup.normalizer (O : Set G) := (hXO (X.inv_mem hc))
    have h2 : GLBConj c⁻¹ R' ≤ O := by
      have := gLBConj_mono c⁻¹ hR'O
      rwa [gLBConj_eq_of_mem_normalizer hc'] at this
    have h3 : R ⊓ O ≤ GLBConj c⁻¹ R' := by
      have := gLBConj_mono c⁻¹ hle
      rwa [gLBConj_inv_gLBConj] at this
    have h4 : GLBConj c⁻¹ R' = R ⊓ O := hS.2.2 _ h2 (isPGroup_gLBConj _ hR'p) h3
    rw [← h4, gLBConj_gLBConj_inv]
  obtain ⟨y, hyO, hy⟩ := exists_gLBConj_eq hS hcS
  rw [gLBConj_gLBConj] at hy
  have hn : c * y ∈ Subgroup.normalizer ((R ⊓ O : Subgroup G) : Set G) :=
    mem_normalizer_iff_gLBConj_eq.2 hy
  have hc' : c = (c * y) * y⁻¹ := by group
  rw [hc']
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hn) (Subgroup.mem_sup_left (O.inv_mem hyO))

end Sylow

section PrimeCore

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_glaPPrimeCoreOf (p : ℕ) (X : Subgroup G) :
    X ≤ Subgroup.normalizer ((GLAPPrimeCoreOf p X : Subgroup G) : Set G) := by
  have hn : ((GLAPPrimeCoreOf p X).subgroupOf X).Normal := by
    have e : (GLAPPrimeCoreOf p X).subgroupOf X = CFSG.pPrimeCore p ↥X :=
      Subgroup.comap_map_eq_self_of_injective X.subtype_injective _
    rw [e]
    exact CFSG.pPrimeCore_normal
  exact Subgroup.le_normalizer_of_normal_subgroupOf (Subgroup.map_subtype_le _)

theorem not_dvd_card_glaPPrimeCoreOf {p : ℕ} [Fact p.Prime] (X : Subgroup G) :
    ¬ p ∣ Nat.card ↥(GLAPPrimeCoreOf p X) := by
  have e : Nat.card ↥(GLAPPrimeCoreOf p X) = Nat.card ↥(CFSG.pPrimeCore p ↥X) :=
    Subgroup.card_map_of_injective X.subtype_injective
  rw [e]
  exact (Nat.Prime.coprime_iff_not_dvd Fact.out).1 CFSG.pPrimeCore_coprime_card

theorem glaPPrimeCoreOf_le_of_hyperplanes {X H M : Subgroup G} (hHX : H ≤ X)
    (hH : IsElemAbelian 3 H) (hHc : Nat.card ↥H = 3 ^ 4)
    (hΓ : ∀ D : Subgroup G, D ≤ H → 2 ≤ CFSG.Open.pRank 3 D →
      Subgroup.normalizer (D : Set G) ≤ M) :
    GLAPPrimeCoreOf 3 X ≤ M := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : CFSG.IsElementaryAbelian 3 ↥H := hH.isElementaryAbelian
  haveI : Nontrivial ↥H := by
    rw [← Finite.one_lt_card_iff_nontrivial, hHc]
    norm_num
  have hHV : H ≤ Subgroup.normalizer ((GLAPPrimeCoreOf 3 X : Subgroup G) : Set G) :=
    hHX.trans (le_normalizer_glaPPrimeCoreOf 3 X)
  have hgen := CFSG.RankThree.PartOne.KE8F.le_iSup_hyperplane_centralizers hHV
    (not_dvd_card_glaPPrimeCoreOf X)
  refine hgen.trans (iSup₂_le fun B hB => ?_)
  have hDH : B.map H.subtype ≤ H := Subgroup.map_subtype_le B
  have hBc : Nat.card ↥B = 3 ^ 3 := by
    have h1 := B.card_mul_index
    rw [hB, hHc] at h1
    omega
  have hDc : Nat.card ↥(B.map H.subtype) = 3 ^ 3 := by
    rw [Subgroup.card_map_of_injective H.subtype_injective, hBc]
  have hrank : 2 ≤ CFSG.Open.pRank 3 (B.map H.subtype) :=
    le_trans (by norm_num : 2 ≤ 3) (le_pRank_of_card le_rfl (hH.mono hDH) hDc)
  exact inf_le_right.trans ((Subgroup.centralizer_le_normalizer _).trans (hΓ _ hDH hrank))

end PrimeCore

section Counting

variable {P : Type} [Group P] [Finite P]

theorem commutatorElement_mul_right' (hcl : ∀ x y z : P, ⁅x, y⁆ * z = z * ⁅x, y⁆) (x a b : P) :
    ⁅x, a * b⁆ = ⁅x, a⁆ * ⁅x, b⁆ := by
  have h := hcl x b a⁻¹
  simp only [commutatorElement_def] at h ⊢
  calc x * (a * b) * x⁻¹ * (a * b)⁻¹ = x * a * x⁻¹ * ((x * b * x⁻¹ * b⁻¹) * a⁻¹) := by group
    _ = x * a * x⁻¹ * (a⁻¹ * (x * b * x⁻¹ * b⁻¹)) := by rw [h]
    _ = x * a * x⁻¹ * a⁻¹ * (x * b * x⁻¹ * b⁻¹) := by group

@[expose] def commMap (hcl : ∀ x y z : P, ⁅x, y⁆ * z = z * ⁅x, y⁆) (x : P) : P →* ↥(commutator P) where
  toFun y := ⟨⁅x, y⁆, by
    rw [commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' a b := by
    apply Subtype.ext
    exact commutatorElement_mul_right' hcl x a b

theorem ker_commMap (hcl : ∀ x y z : P, ⁅x, y⁆ * z = z * ⁅x, y⁆) (x : P) :
    (commMap hcl x).ker = Subgroup.centralizer ({x} : Set P) := by
  ext y
  rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hy
    have h1 : ⁅x, y⁆ = 1 := congrArg Subtype.val hy
    exact ((commutatorElement_eq_one_iff_mul_comm).1 h1).symm
  · intro hy
    apply Subtype.ext
    exact (commutatorElement_eq_one_iff_mul_comm).2 hy.symm

theorem card_le_centralizer_mul (hcl : ∀ x y z : P, ⁅x, y⁆ * z = z * ⁅x, y⁆) (x : P) :
    Nat.card P ≤ Nat.card ↥(Subgroup.centralizer ({x} : Set P)) * Nat.card ↥(commutator P) := by
  have h1 := (commMap hcl x).ker.card_mul_index
  rw [Subgroup.index_ker, ker_commMap] at h1
  rw [← h1]
  exact Nat.mul_le_mul_left _ (Subgroup.card_le_card_group _)

theorem card_le_centralizer_inf_mul (hcl : ∀ x y z : P, ⁅x, y⁆ * z = z * ⁅x, y⁆) (x y : P) :
    Nat.card P ≤ Nat.card ↥(Subgroup.centralizer ({x} : Set P) ⊓ Subgroup.centralizer ({y} : Set P)) *
      (Nat.card ↥(commutator P) * Nat.card ↥(commutator P)) := by
  have h1 := ((commMap hcl x).prod (commMap hcl y)).ker.card_mul_index
  rw [Subgroup.index_ker, MonoidHom.ker_prod, ker_commMap, ker_commMap] at h1
  rw [← h1]
  refine Nat.mul_le_mul_left _ ((Subgroup.card_le_card_group _).trans ?_)
  rw [Nat.card_prod]

theorem isElemAbelian_sup_zpowers {U : Subgroup P} (hU : IsElemAbelian 3 U) {w : P}
    (hw3 : w ^ 3 = 1) (hwU : w ∉ U) (hc : ∀ u ∈ U, u * w = w * u) :
    IsElemAbelian 3 (U ⊔ Subgroup.zpowers w) ∧
      Nat.card ↥(U ⊔ Subgroup.zpowers w) = 3 * Nat.card U := by
  have hw1 : w ≠ 1 := fun h => hwU (h ▸ U.one_mem)
  have hc' : ∀ h ∈ U, ∀ k ∈ Subgroup.zpowers w, h * k = k * h := by
    intro h hh k hk
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    exact ((show Commute h w from hc h hh).zpow_right n).eq
  refine ⟨Lemma1111.isElemAbelian_sup hU (Lemma1111.isElemAbelian_zpowers hw3) hc', ?_⟩
  have h := Lemma1111.card_sup_mul_card_inf U (Subgroup.zpowers w) hc'
  rw [Lemma1111.inf_zpowers_trivial hw3 hw1 hwU, Lemma1111.card_zpowers_three hw1 hw3] at h
  omega

theorem isElemAbelian_center (hexp : ∀ x : P, x ^ 3 = 1) : IsElemAbelian 3 (Subgroup.center P) :=
  ⟨⟨⟨fun a b => Subtype.ext ((Subgroup.mem_center_iff.1 b.2 a))⟩⟩, fun x _ => hexp x⟩

theorem extraspecial_of_card (hexp : ∀ x : P, x ^ 3 = 1)
    (hcl : ∀ x y z : P, ⁅x, y⁆ * z = z * ⁅x, y⁆)
    (hab : ∀ U : Subgroup P, IsElemAbelian 3 U → Nat.card U ≤ 27)
    (hd : 3 ^ 4 * Nat.card ↥(commutator P) ≤ Nat.card P) :
    Nat.card P = 3 ^ 5 ∧ commutator P = Subgroup.center P ∧ Nat.card ↥(Subgroup.center P) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP3 : IsPGroup 3 P := fun g => ⟨1, by rw [pow_one]; exact hexp g⟩
  have hc1 : 1 ≤ Nat.card ↥(commutator P) := Nat.card_pos
  have hZel := isElemAbelian_center hexp
  obtain ⟨x, hxZ⟩ : ∃ x : P, x ∉ Subgroup.center P := by
    by_contra hall
    push Not at hall
    have htop : IsElemAbelian 3 (⊤ : Subgroup P) := by
      refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun y _ => hexp y⟩
      exact (Subgroup.mem_center_iff.1 (hall b.1) a.1)
    have h1 := hab ⊤ htop
    rw [Subgroup.card_top] at h1
    omega
  haveI : Nontrivial P := ⟨⟨x, 1, fun h => hxZ (h ▸ Subgroup.one_mem _)⟩⟩
  have hZnt : Nontrivial ↥(Subgroup.center P) := hP3.center_nontrivial
  obtain ⟨kZ, hkZ⟩ := IsPGroup.iff_card.1 (hP3.to_subgroup (Subgroup.center P))
  have hkZ1 : 1 ≤ kZ := by
    by_contra h0
    push Not at h0
    have : kZ = 0 := by omega
    rw [this, pow_zero] at hkZ
    exact (Finite.one_lt_card_iff_nontrivial.2 hZnt).ne' hkZ
  have hxc : ∀ u ∈ Subgroup.center P, u * x = x * u := fun u hu =>
    (Subgroup.mem_center_iff.1 hu x).symm
  obtain ⟨hU1, hU1c⟩ := isElemAbelian_sup_zpowers hZel (hexp x) hxZ hxc
  have hC_ext : ∀ y : P, y ∈ Subgroup.centralizer ({x} : Set P) →
      ∀ u ∈ Subgroup.center P ⊔ Subgroup.zpowers x, u * y = y * u := by
    intro y hy u hu
    have hle : Subgroup.center P ⊔ Subgroup.zpowers x ≤ Subgroup.centralizer ({y} : Set P) := by
      refine sup_le (fun c hc => ?_) (Subgroup.zpowers_le.2 ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_center_iff.1 hc y).symm
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_singleton_iff.1 hy).symm
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hu)
  have hZ3 : Nat.card ↥(Subgroup.center P) = 3 := by
    by_contra hne
    have hkZ2 : 2 ≤ kZ := by
      by_contra h
      push Not at h
      have : kZ = 1 := by omega
      rw [this] at hkZ
      exact hne (by rw [hkZ]; norm_num)
    have h9 : 9 ≤ Nat.card ↥(Subgroup.center P) := by
      rw [hkZ]
      calc 9 = 3 ^ 2 := by norm_num
        _ ≤ 3 ^ kZ := Nat.pow_le_pow_right (by norm_num) hkZ2
    have h27 := hab _ hU1
    have hU27 : Nat.card ↥(Subgroup.center P ⊔ Subgroup.zpowers x) = 27 := by omega
    have hCle : Subgroup.centralizer ({x} : Set P) ≤ Subgroup.center P ⊔ Subgroup.zpowers x := by
      intro y hy
      by_contra hyU
      have h := isElemAbelian_sup_zpowers hU1 (hexp y) hyU (hC_ext y hy)
      have := hab _ h.1
      omega
    have hC27 : Nat.card ↥(Subgroup.centralizer ({x} : Set P)) ≤ 27 :=
      (Subgroup.card_le_of_le hCle).trans hU27.le
    have hidx := card_le_centralizer_mul hcl x
    have : Nat.card P ≤ 27 * Nat.card ↥(commutator P) :=
      hidx.trans (Nat.mul_le_mul_right _ hC27)
    omega
  have hcomZ : commutator P ≤ Subgroup.center P := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [Subgroup.mem_center_iff]
    intro g
    exact (hcl a b g).symm
  have hcom_ne : commutator P ≠ ⊥ := by
    intro hbot
    apply hxZ
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : ⁅g, x⁆ ∈ commutator P := by
      rw [commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top x)
    rw [hbot, Subgroup.mem_bot] at hg
    exact (commutatorElement_eq_one_iff_mul_comm).1 hg
  have hcom3 : Nat.card ↥(commutator P) = 3 := by
    have hdvd : Nat.card ↥(commutator P) ∣ 3 := by
      rw [← hZ3]
      exact Subgroup.card_dvd_of_le hcomZ
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h1
    · exact absurd (Subgroup.eq_bot_of_card_eq _ h1) hcom_ne
    · exact h1
  have hcomEq : commutator P = Subgroup.center P :=
    Subgroup.eq_of_le_of_card_ge hcomZ (by rw [hZ3, hcom3])
  refine ⟨?_, hcomEq, hZ3⟩
  rw [hcom3] at hd
  rw [hZ3] at hU1c
  have hidx := card_le_centralizer_mul hcl x
  rw [hcom3] at hidx
  obtain ⟨y, hyC, hyU⟩ : ∃ y ∈ Subgroup.centralizer ({x} : Set P),
      y ∉ Subgroup.center P ⊔ Subgroup.zpowers x := by
    by_contra hall
    push Not at hall
    have := Subgroup.card_le_of_le (fun y hy => hall y hy :
      Subgroup.centralizer ({x} : Set P) ≤ Subgroup.center P ⊔ Subgroup.zpowers x)
    omega
  obtain ⟨hU2, hU2c⟩ := isElemAbelian_sup_zpowers hU1 (hexp y) hyU (hC_ext y hyC)
  rw [hU1c] at hU2c
  have hCle : Subgroup.centralizer ({x} : Set P) ⊓ Subgroup.centralizer ({y} : Set P) ≤
      Subgroup.center P ⊔ Subgroup.zpowers x ⊔ Subgroup.zpowers y := by
    intro w hw
    by_contra hwU
    have hwc : ∀ u ∈ Subgroup.center P ⊔ Subgroup.zpowers x ⊔ Subgroup.zpowers y,
        u * w = w * u := by
      intro u hu
      have hle : Subgroup.center P ⊔ Subgroup.zpowers x ⊔ Subgroup.zpowers y ≤
          Subgroup.centralizer ({w} : Set P) := by
        refine sup_le (sup_le (fun c hc => ?_) (Subgroup.zpowers_le.2 ?_)) (Subgroup.zpowers_le.2 ?_)
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact (Subgroup.mem_center_iff.1 hc w).symm
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact (Subgroup.mem_centralizer_singleton_iff.1 hw.1).symm
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact (Subgroup.mem_centralizer_singleton_iff.1 hw.2).symm
      exact Subgroup.mem_centralizer_singleton_iff.1 (hle hu)
    have h := isElemAbelian_sup_zpowers hU2 (hexp w) hwU hwc
    have := hab _ h.1
    omega
  have hidx2 := card_le_centralizer_inf_mul hcl x y
  rw [hcom3] at hidx2
  have hC27 := Subgroup.card_le_of_le hCle
  have : Nat.card P ≤ 27 * (3 * 3) := hidx2.trans (Nat.mul_le_mul_right _ (hC27.trans hU2c.le))
  omega

end Counting

section Omega

variable {G : Type} [Group G] [Finite G]

theorem mul_pow_three_eq_one {x y : G} (hx : x ^ 3 = 1) (hy : y ^ 3 = 1)
    (hcx : ⁅y, x⁆ * x = x * ⁅y, x⁆) (hcy : ⁅y, x⁆ * y = y * ⁅y, x⁆) : (x * y) ^ 3 = 1 := by
  set c := ⁅y, x⁆ with hc
  have hyx : y * x = c * (x * y) := by rw [hc, commutatorElement_def]; group
  have hc3 : c ^ 3 = 1 := by
    have e1 : y * x * y⁻¹ = c * x := by rw [hyx]; group
    have e2 : (y * x * y⁻¹) ^ 3 = y * x ^ 3 * y⁻¹ := conj_pow
    rw [e1, hx, mul_one, mul_inv_cancel, (show Commute c x from hcx).mul_pow, hx, mul_one] at e2
    exact e2
  have hxc : ∀ t, x * (c * t) = c * (x * t) := fun t => by rw [← mul_assoc, ← hcx, mul_assoc]
  have hyc : ∀ t, y * (c * t) = c * (y * t) := fun t => by rw [← mul_assoc, ← hcy, mul_assoc]
  have hyx' : ∀ t, y * (x * t) = c * (x * (y * t)) := fun t => by
    rw [← mul_assoc, hyx, mul_assoc, mul_assoc]
  have key : (x * y) ^ 3 = c * (c * (c * (x * (x * (x * (y * (y * y))))))) := by
    have e : (x * y) ^ 3 = x * (y * (x * (y * (x * y)))) := by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [e]
    simp only [hyx', hxc, hyc]
  rw [key]
  have e : c * (c * (c * (x * (x * (x * (y * (y * y))))))) = c ^ 3 * (x ^ 3 * y ^ 3) := by
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  rw [e, hc3, hx, hy, one_mul, one_mul]

theorem mem_omegaOne_three {C : Subgroup G}
    (hcl : ∀ x ∈ C, ∀ y ∈ C, ∀ w ∈ C, ⁅x, y⁆ * w = w * ⁅x, y⁆) {x : G}
    (hx : x ∈ omegaOne 3 C) : x ∈ C ∧ x ^ 3 = 1 := by
  unfold omegaOne at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy => exact hy
  | one => exact ⟨C.one_mem, one_pow 3⟩
  | mul a b _ _ ha hb =>
    exact ⟨C.mul_mem ha.1 hb.1, mul_pow_three_eq_one ha.2 hb.2 (hcl b hb.1 a ha.1 a ha.1)
      (hcl b hb.1 a ha.1 b hb.1)⟩
  | inv a _ ha => exact ⟨C.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩

theorem omegaOne_facts {R₁ R₂ : Subgroup G} (hR₂ : R₂ ≤ R₁)
    (hc : ∀ r ∈ R₁, ∀ x ∈ R₂, ⁅r, x⁆ ∈ R₂ ∧ ∀ w ∈ R₂, ⁅r, x⁆ * w = w * ⁅r, x⁆) :
    (∀ x ∈ omegaOne 3 R₂, x ^ 3 = 1) ∧ omegaOne 3 R₂ ≤ R₁ ∧
      ((omegaOne 3 R₂).subgroupOf R₁).Normal ∧ ⁅R₁, omegaOne 3 R₂⁆ ≤ centerOf (omegaOne 3 R₂) ∧
        ⁅omegaOne 3 R₂, omegaOne 3 R₂⁆ ≤ centerOf (omegaOne 3 R₂) := by
  have hcl : ∀ x ∈ R₂, ∀ y ∈ R₂, ∀ w ∈ R₂, ⁅x, y⁆ * w = w * ⁅x, y⁆ :=
    fun x hx y hy w hw => (hc x (hR₂ hx) y hy).2 w hw
  have hmem := fun x (hx : x ∈ omegaOne 3 R₂) => mem_omegaOne_three hcl hx
  have hle₂ : omegaOne 3 R₂ ≤ R₂ := fun x hx => (hmem x hx).1
  have hle : omegaOne 3 R₂ ≤ R₁ := hle₂.trans hR₂
  have hconj : ∀ r ∈ R₁, ∀ x ∈ omegaOne 3 R₂, r * x * r⁻¹ ∈ omegaOne 3 R₂ := by
    intro r hr x hx
    obtain ⟨hxR₂, hx3⟩ := hmem x hx
    apply Subgroup.subset_closure
    refine ⟨?_, by rw [conj_pow, hx3, mul_one, mul_inv_cancel]⟩
    have e : r * x * r⁻¹ = ⁅r, x⁆ * x := by rw [commutatorElement_def]; group
    rw [e]
    exact R₂.mul_mem (hc r hr x hxR₂).1 hxR₂
  have hcomm : ⁅R₁, omegaOne 3 R₂⁆ ≤ centerOf (omegaOne 3 R₂) := by
    rw [Subgroup.commutator_le]
    intro r hr x hx
    rw [mem_centerOf_iff']
    refine ⟨?_, fun w hw => ((hc r hr x (hle₂ hx)).2 w (hle₂ hw)).symm⟩
    rw [commutatorElement_def]
    exact (omegaOne 3 R₂).mul_mem (hconj r hr x hx) ((omegaOne 3 R₂).inv_mem hx)
  refine ⟨fun x hx => (hmem x hx).2, hle, ⟨fun n hn g => ?_⟩, hcomm,
    (Subgroup.commutator_mono hle le_rfl).trans hcomm⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  exact hconj g g.2 n hn

theorem isExtraspecialThreeFive_of_card {W : Subgroup G} (hexp : ∀ x ∈ W, x ^ 3 = 1)
    (hcl : ⁅W, W⁆ ≤ centerOf W)
    (hab : ∀ U : Subgroup G, U ≤ W → IsElemAbelian 3 U → Nat.card ↥U ≤ 3 ^ 3)
    (hd : 3 ^ 4 * Nat.card ↥⁅W, W⁆ ≤ Nat.card ↥W) : IsExtraspecialThreeFive W := by
  have hexp' : ∀ x : ↥W, x ^ 3 = 1 := fun x => Subtype.ext (by simpa using hexp x x.2)
  have hcl' : ∀ x y z : ↥W, ⁅x, y⁆ * z = z * ⁅x, y⁆ := by
    intro x y z
    apply Subtype.ext
    have hmem : ⁅(x : G), (y : G)⁆ ∈ centerOf W :=
      hcl (Subgroup.commutator_mem_commutator x.2 y.2)
    have h := ((mem_centerOf_iff' W _).1 hmem).2 z z.2
    simp only [Subgroup.coe_mul, commutatorElement_def, Subgroup.coe_inv] at h ⊢
    exact h.symm
  have hab' : ∀ U : Subgroup ↥W, IsElemAbelian 3 U → Nat.card ↥U ≤ 27 := by
    intro U hU
    have h := hab (U.map W.subtype) (Subgroup.map_subtype_le U) (hU.map W.subtype)
    rwa [Subgroup.card_map_of_injective W.subtype_injective] at h
  have hcomm : (commutator ↥W).map W.subtype = ⁅W, W⁆ := Subgroup.map_subtype_commutator W
  have hcard_comm : Nat.card ↥(commutator ↥W) = Nat.card ↥⁅W, W⁆ := by
    rw [← hcomm, Subgroup.card_map_of_injective W.subtype_injective]
  obtain ⟨hc5, hcZ, hZ3⟩ := extraspecial_of_card hexp' hcl' hab' (by rw [hcard_comm]; exact hd)
  refine ⟨hc5, hexp, ?_, ?_⟩
  · rw [← hcomm, hcZ]
    rfl
  · unfold centerOf
    rw [Subgroup.card_map_of_injective W.subtype_injective, hZ3]

end Omega

section Setting

variable {G : Type} [Group G] [Finite G] {m : ℕ} {B M E A N D : Subgroup G}

theorem setting_facts (h : Cex127 G m 3 B M E A N D) (hA3 : CFSG.Open.pRank 3 A = 3)
    (hk : CFSG.Open.pRank 3 (E ⊓ A) = 2) {R₀ : Subgroup G} (hR₀ : IsSylowIn 3 M R₀) :
    IsSylowIn 3 ⊤ R₀ ∧ GLBCore 3 4 R₀ ≤ M ∧
      ∀ H : Subgroup G, IsEkIn 3 4 R₀ H → ∀ D : Subgroup G, D ≤ H → 2 ≤ CFSG.Open.pRank 3 D →
        Subgroup.normalizer (D : Set G) ≤ M := by
  have hF := h.toSec11.toSec10Fails
  have hEA := h.pair
  refine ⟨(lemma104_iv_holds hF hEA hk hR₀).2.2, (lemma104_v_holds hF hEA (Or.inr hA3) hR₀).2,
    fun H hH D hDH hD2 => ?_⟩
  obtain ⟨-, -, A', hA', hHA'⟩ := (lemma104_v_holds hF hEA (Or.inr hA3) hR₀).1 H hH
  have hcore : Subgroup.normalizer (D : Set G) ≤ GLBCore 3 2 A' :=
    le_sSup ⟨D, hDH.trans hHA', hD2, rfl⟩
  exact hcore.trans hA'.2.clause_d

theorem exists_ekIn {R : Subgroup G} (hR : IsSylowIn 3 ⊤ R) {E : Subgroup G} {k : ℕ}
    (hE4 : k ≤ CFSG.Open.pRank 3 E) : ∃ H : Subgroup G, IsEkIn 3 k R H := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E₄, -, hE₄, hE₄c⟩ := exists_elemAbelian_card_pow_of_le_pRank' hE4
  obtain ⟨x, -, T, hTp, -, hRT, hE₄T⟩ :=
    exists_conj_le_pGroup' (le_top : R ≤ ⊤) hR.2.1 (le_top : E₄ ≤ ⊤) hE₄.isPGroup
  have hTR : T = R := hR.2.2 T le_top hTp hRT
  rw [hTR] at hE₄T
  exact ⟨GLBConj x E₄, hE₄T, isElemAbelian_gLBConj x hE₄, by rw [card_gLBConj, hE₄c]⟩

theorem core_le (h : Cex127 G m 3 B M E A N D) (hA3 : CFSG.Open.pRank 3 A = 3)
    (hk : CFSG.Open.pRank 3 (E ⊓ A) = 2) (hE5 : 5 ≤ CFSG.Open.pRank 3 E) {z : G}
    (hz1 : IsPCentralIn 3 M z) :
    GLAPPrimeCoreOf 3 (Cg z) ≤ M ∧ pPrimePCore 3 (Cg z) ≤ M := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨R₀, hR₀M, hzR₀⟩ := hz1
  obtain ⟨hR₀G, -, hΓ⟩ := setting_facts h hA3 hk hR₀M
  have hR₀C : R₀ ≤ Cg z := le_cg_of_mem_centerOf hzR₀
  obtain ⟨H, hH⟩ := exists_ekIn hR₀G (by omega : 4 ≤ CFSG.Open.pRank 3 E)
  have hO : GLAPPrimeCoreOf 3 (Cg z) ≤ M :=
    glaPPrimeCoreOf_le_of_hyperplanes (hH.1.trans hR₀C) hH.2.1 hH.2.2 (hΓ H hH)
  have hR₀S : IsSylowIn 3 (Cg z) R₀ :=
    ⟨hR₀C, hR₀G.2.1, fun R' _ hR'p hle => hR₀G.2.2 R' le_top hR'p hle⟩
  exact ⟨hO, (pPrimePCore_le_sup hR₀S).trans (sup_le hO hR₀M.1)⟩

end Setting

theorem claim1211_OM_holds : Claim1211_OM := by
  intro G _ _ m p B M E A N D h K hK z _ hz1 _
  obtain ⟨hcom, hp3, hE5, -⟩ := hK
  subst hp3
  exact (core_le h hcom.2.1.1 hcom.2.1.2 hE5 hz1).2

theorem claim1211_m3_holds : Claim1211_m3 := by
  intro G _ _ m p B M E A N D h K hK z _ hz1 hz2 R hR _ hRM E' hE'R hE'
  obtain ⟨hcom, hp3, hE5, -⟩ := hK
  subst hp3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hOM⟩ := core_le h hcom.2.1.1 hcom.2.1.2 hE5 hz1
  obtain ⟨R₀, hR₀M, hzR₀⟩ := hz1
  obtain ⟨hR₀G, -, -⟩ := setting_facts h hcom.2.1.1 hcom.2.1.2 hR₀M
  have hR₀S : IsSylowIn 3 (Cg z) R₀ :=
    ⟨le_cg_of_mem_centerOf hzR₀, hR₀G.2.1, fun R' _ hR'p hle => hR₀G.2.2 R' le_top hR'p hle⟩
  obtain ⟨x, -, hx⟩ := exists_gLBConj_eq hR hR₀S
  have hRG : IsSylowIn 3 ⊤ R := hx ▸ isSylowIn_top_gLBConj hR₀G x
  have hRMs : IsSylowIn 3 M R :=
    ⟨hRM, hR.2.1, fun R' _ hR'p hle => hRG.2.2 R' le_top hR'p hle⟩
  have hΓ : GLBCore 3 4 R ≤ M := (setting_facts h hcom.2.1.1 hcom.2.1.2 hRMs).2.1
  by_contra hgt
  push Not at hgt
  obtain ⟨k, hk⟩ := exists_card_eq_pow hE'.isPGroup
  have hk4 : 4 ≤ k := by
    by_contra hk4
    push Not at hk4
    have : 3 ^ k ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hrank : 4 ≤ CFSG.Open.pRank 3 (R ⊓ pPrimePCore 3 (Cg z)) :=
    hk4.trans (le_pRank_of_card hE'R hE' hk)
  have hN0 : Subgroup.normalizer ((R ⊓ pPrimePCore 3 (Cg z) : Subgroup G) : Set G) ≤
      GLBCore 3 4 R :=
    le_sSup ⟨R ⊓ pPrimePCore 3 (Cg z), inf_le_left, hrank, rfl⟩
  have hN := hN0.trans hΓ
  have hOC : pPrimePCore 3 (Cg z) ≤ Cg z := Subgroup.map_subtype_le _
  have hCO : Cg z ≤ Subgroup.normalizer ((pPrimePCore 3 (Cg z) : Subgroup G) : Set G) := by
    have hn : ((pPrimePCore 3 (Cg z)).subgroupOf (Cg z)).Normal := by
      have e : (pPrimePCore 3 (Cg z)).subgroupOf (Cg z) =
          (CFSG.pCore 3 (↥(Cg z) ⧸ GLAPPrimeCore 3 ↥(Cg z))).comap
            (QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cg z))) :=
        Subgroup.comap_map_eq_self_of_injective (Cg z).subtype_injective _
      rw [e]
      infer_instance
    exact Subgroup.le_normalizer_of_normal_subgroupOf hOC
  exact hz2 ((le_sup_normalizer_inf hR hOC hCO).trans (sup_le hOM hN))

section R3

variable {G : Type} [Group G] [Finite G]

theorem critical_comm {R₁ : Subgroup G} {C : Subgroup ↥R₁}
    (hC : CFSG.SectionRank.Ccomm.IsThompsonCritical C) :
    ∀ r ∈ R₁, ∀ x ∈ C.map R₁.subtype, ⁅r, x⁆ ∈ C.map R₁.subtype ∧
      ∀ w ∈ C.map R₁.subtype, ⁅r, x⁆ * w = w * ⁅r, x⁆ := by
  intro r hr x hx
  obtain ⟨x', hx'C, rfl⟩ := Subgroup.mem_map.1 hx
  have hmem : ⁅(⟨r, hr⟩ : ↥R₁), x'⁆ ∈ C ⊓ Subgroup.centralizer (C : Set ↥R₁) :=
    hC.2.2.1 (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) hx'C)
  have hcoe : R₁.subtype ⁅(⟨r, hr⟩ : ↥R₁), x'⁆ = ⁅r, R₁.subtype x'⁆ :=
    map_commutatorElement R₁.subtype _ _
  refine ⟨Subgroup.mem_map.2 ⟨_, hmem.1, hcoe⟩, fun w hw => ?_⟩
  obtain ⟨w', hw'C, rfl⟩ := Subgroup.mem_map.1 hw
  have h := congrArg R₁.subtype (Subgroup.mem_centralizer_iff.1 hmem.2 w' hw'C)
  rw [map_mul, map_mul, hcoe] at h
  exact h.symm

end R3

@[expose] def Claim1211_rank4 : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A N D : Subgroup G} (h : Cex127 G m p B M E A N D)
    {K : Subgroup G} (hK : AlphaData1211 p M E A N K) {z : G} (hz : z ∈ A ∧ z ≠ 1)
    (hz1 : IsPCentralIn p M z) (hz2 : ¬ Cg z ≤ M) {R : Subgroup G} (hR : IsSylowIn 3 (Cg z) R)
    (hAR : A ≤ R) (hRM : R ≤ M) (C : Subgroup ↥(R ⊓ pPrimePCore 3 (Cg z))),
    CFSG.SectionRank.Ccomm.IsThompsonCritical C →
      3 ^ 4 * Nat.card ↥⁅omegaOne 3 (C.map (R ⊓ pPrimePCore 3 (Cg z)).subtype),
          omegaOne 3 (C.map (R ⊓ pPrimePCore 3 (Cg z)).subtype)⁆ ≤
        Nat.card ↥(omegaOne 3 (C.map (R ⊓ pPrimePCore 3 (Cg z)).subtype))

theorem claim1211_R3_of_rank4 (h4 : Claim1211_rank4) : Claim1211_R3 := by
  intro G _ _ m p B M E A N D h K hK z hz hz1 hz2 R hR hAR hRM
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hR₁p : IsPGroup 3 ↥(R ⊓ pPrimePCore 3 (Cg z)) := isPGroup_of_le' hR.2.1 inf_le_left
  obtain ⟨⟨C, hC⟩, -⟩ := CFSG.SectionRank.Ccomm.thompson_critical_subgroup hR₁p
  obtain ⟨hexp, hle, hn, hcomm, hcl⟩ :=
    omegaOne_facts (Subgroup.map_subtype_le C) (critical_comm hC)
  have hm3 := claim1211_m3_holds h hK hz hz1 hz2 hR hAR hRM
  exact ⟨_, hle, hn, isExtraspecialThreeFive_of_card hexp hcl
    (fun U hU hUel => hm3 U (hU.trans hle) hUel) (h4 h hK hz hz1 hz2 hR hAR hRM C hC), hcomm⟩

section TI

variable {G : Type} [Group G] [Finite G]

theorem map_pPrimePCore (p : ℕ) (X : Subgroup G) :
    (CFSG.GH74.GLS.pPrimePCore p ↥X).map X.subtype = pPrimePCore p X := rfl

theorem tI3_of_quotient {X : Subgroup G}
    (hTI : ∀ S T : Sylow 3 (↥X ⧸ CFSG.GH74.GLS.pPrimePCore 3 ↥X), S ≠ T →
      (S : Subgroup (↥X ⧸ CFSG.GH74.GLS.pPrimePCore 3 ↥X)) ⊓ T = ⊥) :
    TI3 X (pPrimePCore 3 X) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro S T hS hT hne x hx
  set O' := CFSG.GH74.GLS.pPrimePCore 3 ↥X with hO'
  set π := QuotientGroup.mk' O' with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective O'
  obtain ⟨S', hS'⟩ := exists_sylow_of_isSylowIn hS
  obtain ⟨T', hT'⟩ := exists_sylow_of_isSylowIn hT
  have hSO : S ⊔ pPrimePCore 3 X = (((S' : Subgroup ↥X).map π).comap π).map X.subtype := by
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.map_sup, hS', map_pPrimePCore]
  have hTO : T ⊔ pPrimePCore 3 X = (((T' : Subgroup ↥X).map π).comap π).map X.subtype := by
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.map_sup, hT', map_pPrimePCore]
  have hne' : S'.mapSurjective hπs ≠ T'.mapSurjective hπs := by
    intro heq
    apply hne
    rw [hSO, hTO]
    have := congrArg (fun P : Sylow 3 (↥X ⧸ O') => (P : Subgroup (↥X ⧸ O'))) heq
    simp only [Sylow.coe_mapSurjective] at this
    rw [this]
  have hbot := hTI _ _ hne'
  simp only [Sylow.coe_mapSurjective] at hbot
  rw [hSO, hTO] at hx
  obtain ⟨⟨y, hyS, hyx⟩, ⟨y', hyT, hy'x⟩⟩ := hx
  have hyy' : y = y' := X.subtype_injective (hyx.trans hy'x.symm)
  subst hyy'
  have hmem : π y ∈ ((S' : Subgroup ↥X).map π) ⊓ ((T' : Subgroup ↥X).map π) := ⟨hyS, hyT⟩
  rw [hbot, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
  rw [← hyx, ← map_pPrimePCore]
  exact Subgroup.mem_map_of_mem _ hmem

end TI

@[expose] def Input_TI_L29 : Prop :=
  ∀ (X : Type) [Group X] [Finite X],
    (IsLpType 2 9 ↥(CFSG.GH74.GLS.oPrimeResidual 3 X) ∨
      IsSL2Nine ↥(CFSG.GH74.GLS.oPrimeResidual 3 X)) →
      ∀ S T : Sylow 3 X, S ≠ T → (S : Subgroup X) ⊓ T = ⊥

@[expose] def Claim1211_L29 : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A N D : Subgroup G} (h : Cex127 G m p B M E A N D)
    {K : Subgroup G} (hK : AlphaData1211 p M E A N K) {z : G} (hz : z ∈ A ∧ z ≠ 1)
    (hz1 : IsPCentralIn p M z) (hz2 : ¬ Cg z ≤ M),
    IsLpType 2 9
        ↥(CFSG.GH74.GLS.oPrimeResidual 3 (↥(Cg z) ⧸ CFSG.GH74.GLS.pPrimePCore 3 ↥(Cg z))) ∨
      IsSL2Nine ↥(CFSG.GH74.GLS.oPrimeResidual 3 (↥(Cg z) ⧸ CFSG.GH74.GLS.pPrimePCore 3 ↥(Cg z)))

theorem claim1211_TI_of_inputs (hL : Claim1211_L29) (hI : Input_TI_L29) : Claim1211_TI := by
  intro G _ _ m p B M E A N D h K hK z hz hz1 hz2
  exact tI3_of_quotient (hI _ (hL h hK hz hz1 hz2))

section SL2

open Matrix

variable {F : Type} [Field F]

theorem three_eq_zero_of_card [Finite F] (hF9 : Nat.card F = 9) : (3 : F) = 0 := by
  haveI := Fintype.ofFinite F
  have h9 : ((Fintype.card F : ℕ) : F) = 0 := FiniteField.cast_card_eq_zero F
  rw [← Nat.card_eq_fintype_card, hF9] at h9
  have : (3 : F) * 3 = 0 := by
    have e : ((9 : ℕ) : F) = 3 * 3 := by norm_num
    rw [← e]
    exact h9
  exact mul_self_eq_zero.1 this

theorem pow_three_of_fixes (h3 : (3 : F) = 0) {g : Matrix (Fin 2) (Fin 2) F} (hdet : g.det = 1)
    {v : Fin 2 → F} (hv : v ≠ 0) (hgv : g *ᵥ v = v) : g ^ 3 = 1 := by
  have hker : (g - 1).det = 0 := by
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    exact ⟨v, hv, by rw [Matrix.sub_mulVec, hgv, Matrix.one_mulVec, sub_self]⟩
  rw [Matrix.det_fin_two] at hdet hker
  simp [Matrix.one_apply] at hker
  have htr : g 0 0 + g 1 1 = 2 := by linear_combination hdet - hker
  have e : g ^ 3 = g * (g * g) := by rw [pow_succ, pow_two, mul_assoc]
  rw [e]
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination (g 0 0 * (g 0 0 + g 1 1 - 2) + 4 * g 0 0 -
      (g 0 0 * g 1 1 - g 0 1 * g 1 0 - 1) - 1) * htr + (-g 0 0 - 2) * hdet + (g 0 0 - 1) * h3
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination (g 0 1 * (g 0 0 + g 1 1 - 2) + 4 * g 0 1) * htr - g 0 1 * hdet +
      g 0 1 * h3
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination (g 1 0 * (g 0 0 + g 1 1 - 2) + 4 * g 1 0) * htr - g 1 0 * hdet +
      g 1 0 * h3
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination (g 1 1 * (g 0 0 + g 1 1 - 2) + 4 * g 1 1 -
      (g 0 0 * g 1 1 - g 0 1 * g 1 0 - 1) - 1) * htr + (-g 1 1 - 2) * hdet + (g 1 1 - 1) * h3

abbrev slAct : MulAction ↥(StatedSL 2 F) (Fin 2 → F) where
  smul g v := (((g : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ v
  one_smul v := by
    change (((1 : ↥(StatedSL 2 F)) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ v = v
    simp
  mul_smul g h v := by
    change (((g * h : ↥(StatedSL 2 F)) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ v =
      ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ
        (((h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ v)
    rw [Matrix.mulVec_mulVec]
    rfl

theorem tI_statedSL [Finite F] (hF9 : Nat.card F = 9) (S T : Sylow 3 ↥(StatedSL 2 F))
    (hST : S ≠ T) : (S : Subgroup ↥(StatedSL 2 F)) ⊓ T = ⊥ := by
  classical
  letI : MulAction ↥(StatedSL 2 F) (Fin 2 → F) := slAct
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 := three_eq_zero_of_card hF9
  have hdvd : 3 ∣ Nat.card (Fin 2 → F) := by
    rw [Nat.card_fun, Nat.card_fin, hF9]
    norm_num
  have hfix0 : ∀ U : Subgroup ↥(StatedSL 2 F), (0 : Fin 2 → F) ∈ MulAction.fixedPoints ↥U (Fin 2 → F) :=
    fun U u => by
      change (((u : ↥(StatedSL 2 F)) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ 0 = 0
      exact Matrix.mulVec_zero _
  obtain ⟨v, hvS, hv0⟩ :=
    S.isPGroup'.exists_fixed_point_of_prime_dvd_card_of_fixed_point (Fin 2 → F) hdvd (hfix0 S)
  obtain ⟨w, hwT, hw0⟩ :=
    T.isPGroup'.exists_fixed_point_of_prime_dvd_card_of_fixed_point (Fin 2 → F) hdvd (hfix0 T)
  have hfixS : ∀ s ∈ (S : Subgroup ↥(StatedSL 2 F)),
      (((s : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ v = v := fun s hs => hvS ⟨s, hs⟩
  have hfixT : ∀ t ∈ (T : Subgroup ↥(StatedSL 2 F)),
      (((t : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ w = w := fun t ht => hwT ⟨t, ht⟩
  have hstab : ∀ u : Fin 2 → F, u ≠ 0 →
      IsPGroup 3 ↥(MulAction.stabilizer ↥(StatedSL 2 F) u) := by
    intro u hu g
    refine ⟨1, ?_⟩
    have hgu : (((g : ↥(StatedSL 2 F)) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ u = u :=
      g.2
    have hdet := CFSG.Open.StatedAPI.det_of_mem_statedSL (g : ↥(StatedSL 2 F)).2
    have h1 := pow_three_of_fixes h3 hdet hu hgu
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    simpa using h1
  by_contra hne
  obtain ⟨g, hg1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have hgv := hfixS g g.2.1
  have hgw := hfixT g g.2.2
  set gm := (((g : ↥(StatedSL 2 F)) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) with hgm
  have e0v : gm 0 0 * v 0 + gm 0 1 * v 1 = v 0 := by
    have := congrFun hgv 0
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have e1v : gm 1 0 * v 0 + gm 1 1 * v 1 = v 1 := by
    have := congrFun hgv 1
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have e0w : gm 0 0 * w 0 + gm 0 1 * w 1 = w 0 := by
    have := congrFun hgw 0
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have e1w : gm 1 0 * w 0 + gm 1 1 * w 1 = w 1 := by
    have := congrFun hgw 1
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  by_cases hD : v 0 * w 1 - v 1 * w 0 = 0
  ·
    have hwv : ∃ c : F, v = c • w := by
      by_cases hw0' : w 0 = 0
      · have hw1 : w 1 ≠ 0 := by
          intro hw1
          apply hw0
          funext i
          fin_cases i
          · exact hw0'.symm
          · exact hw1.symm
        have hv00 : v 0 = 0 := by
          have : v 0 * w 1 = 0 := by rw [hw0'] at hD; linear_combination hD
          exact (mul_eq_zero.1 this).resolve_right hw1
        refine ⟨v 1 / w 1, ?_⟩
        funext i
        fin_cases i
        · simp [hv00, hw0']
        · simp
          field_simp
      · refine ⟨v 0 / w 0, ?_⟩
        funext i
        fin_cases i
        · simp
          field_simp
        · simp
          field_simp
          linear_combination -hD
    obtain ⟨c, hc⟩ := hwv
    have hTv : ∀ t ∈ (T : Subgroup ↥(StatedSL 2 F)),
        (((t : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ v = v := by
      intro t ht
      rw [hc, Matrix.mulVec_smul, hfixT t ht]
    have hv0' : v ≠ 0 := fun h => hv0 h.symm
    have hSU : (S : Subgroup ↥(StatedSL 2 F)) ≤ MulAction.stabilizer ↥(StatedSL 2 F) v :=
      fun s hs => hfixS s hs
    have hTU : (T : Subgroup ↥(StatedSL 2 F)) ≤ MulAction.stabilizer ↥(StatedSL 2 F) v :=
      fun t ht => hTv t ht
    have h1 := S.is_maximal' (hstab v hv0') hSU
    have h2 := T.is_maximal' (hstab v hv0') hTU
    exact hST (Sylow.ext (h1.symm.trans h2))
  ·
    apply hg1
    have h00 : gm 0 0 = 1 := by
      have : (gm 0 0 - 1) * (v 0 * w 1 - v 1 * w 0) = 0 := by
        linear_combination w 1 * e0v - v 1 * e0w
      exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hD)
    have h01 : gm 0 1 = 0 := by
      have : gm 0 1 * (v 0 * w 1 - v 1 * w 0) = 0 := by
        linear_combination v 0 * e0w - w 0 * e0v
      exact (mul_eq_zero.1 this).resolve_right hD
    have h10 : gm 1 0 = 0 := by
      have : gm 1 0 * (v 0 * w 1 - v 1 * w 0) = 0 := by
        linear_combination w 1 * e1v - v 1 * e1w
      exact (mul_eq_zero.1 this).resolve_right hD
    have h11 : gm 1 1 = 1 := by
      have : (gm 1 1 - 1) * (v 0 * w 1 - v 1 * w 0) = 0 := by
        linear_combination v 0 * e1w - w 0 * e1v
      exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hD)
    have hgm1 : gm = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11]
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    simpa [hgm] using hgm1

theorem tI_statedProj [Finite F] (hF9 : Nat.card F = 9)
    (S T : Sylow 3 (StatedProj (StatedSL 2 F))) (hST : S ≠ T) :
    (S : Subgroup (StatedProj (StatedSL 2 F))) ⊓ T = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Z := (StatedScalars (Fin 2) F).subgroupOf (StatedSL 2 F) with hZ
  have hπs : Function.Surjective (QuotientGroup.mk' Z) := QuotientGroup.mk'_surjective Z
  obtain ⟨S₀, hS₀⟩ := Sylow.mapSurjective_surjective hπs 3 S
  obtain ⟨T₀, hT₀⟩ := Sylow.mapSurjective_surjective hπs 3 T
  by_contra hne
  obtain ⟨gb, hgb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have hgS : (gb : StatedProj (StatedSL 2 F)) ∈ (S₀ : Subgroup ↥(StatedSL 2 F)).map
      (QuotientGroup.mk' Z) := by
    rw [← Sylow.coe_mapSurjective hπs, hS₀]
    exact gb.2.1
  have hgT : (gb : StatedProj (StatedSL 2 F)) ∈ (T₀ : Subgroup ↥(StatedSL 2 F)).map
      (QuotientGroup.mk' Z) := by
    rw [← Sylow.coe_mapSurjective hπs, hT₀]
    exact gb.2.2
  obtain ⟨s, hs, hsg⟩ := hgS
  obtain ⟨t, ht, htg⟩ := hgT
  have hζ : s⁻¹ * t ∈ Z := by
    have e : QuotientGroup.mk' Z s = QuotientGroup.mk' Z t := hsg.trans htg.symm
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at e
    exact e
  set ζ := s⁻¹ * t with hζdef
  have hζc : ζ ∈ Subgroup.center ↥(StatedSL 2 F) :=
    CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center (StatedSL 2 F) hζ
  have hζ2 : ζ ^ 2 = 1 := by
    obtain ⟨c, hc⟩ := (Subgroup.mem_subgroupOf.1 hζ : (ζ : GL (Fin 2) F) ∈ StatedScalars (Fin 2) F)
    have hcm : (((ζ : ↥(StatedSL 2 F)) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        Matrix.scalar (Fin 2) (c : F) := by
      rw [← hc]
      rfl
    have hdet := CFSG.Open.StatedAPI.det_of_mem_statedSL ζ.2
    rw [hcm, Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_univ_two] at hdet
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, Subgroup.coe_one, Units.val_one]
    rw [hcm, ← map_pow, pow_two, hdet, map_one]
  obtain ⟨k, hk⟩ := S₀.isPGroup' ⟨s, hs⟩
  obtain ⟨l, hl⟩ := T₀.isPGroup' ⟨t, ht⟩
  have hsk : s ^ (3 ^ k * 3 ^ l) = 1 := by
    have := congrArg Subtype.val hk
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at this
    rw [pow_mul, this, one_pow]
  have htk : t ^ (3 ^ k * 3 ^ l) = 1 := by
    have := congrArg Subtype.val hl
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at this
    rw [mul_comm, pow_mul, this, one_pow]
  have hodd : Odd (3 ^ k * 3 ^ l) := (Odd.pow (by decide)).mul (Odd.pow (by decide))
  obtain ⟨j, hj⟩ := hodd
  have hts : t = s * ζ := by rw [hζdef]; group
  have hζ1 : ζ = 1 := by
    have hcomm : Commute s ζ := Subgroup.mem_center_iff.1 hζc s
    have h1 : ζ ^ (3 ^ k * 3 ^ l) = 1 := by
      have := htk
      rw [hts, hcomm.mul_pow, hsk, one_mul] at this
      exact this
    rw [hj, pow_succ, pow_mul, hζ2, one_pow, one_mul] at h1
    exact h1
  have hst : t = s := by rw [hts, hζ1, mul_one]
  have hs1 : s ≠ 1 := by
    rintro rfl
    apply hgb1
    apply Subtype.ext
    rw [← hsg, map_one]
    rfl
  by_cases hS₀T₀ : S₀ = T₀
  · exact hST (by rw [← hS₀, ← hT₀, hS₀T₀])
  · have hbot := tI_statedSL hF9 S₀ T₀ hS₀T₀
    have hsm : s ∈ (S₀ : Subgroup ↥(StatedSL 2 F)) ⊓ T₀ := ⟨hs, hst ▸ ht⟩
    rw [hbot, Subgroup.mem_bot] at hsm
    exact hs1 hsm

end SL2

section TItransfer

theorem tI_of_mulEquiv {X Y : Type} [Group X] [Group Y] [Finite X] (e : X ≃* Y)
    (hY : ∀ S T : Sylow 3 Y, S ≠ T → (S : Subgroup Y) ⊓ T = ⊥) :
    ∀ S T : Sylow 3 X, S ≠ T → (S : Subgroup X) ⊓ T = ⊥ := by
  intro S T hST
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hinj : Function.Injective e.toMonoidHom := e.injective
  have hsurj : Function.Surjective e.toMonoidHom := e.surjective
  have h1 := hY (S.mapSurjective hsurj) (T.mapSurjective hsurj) (by
    intro heq
    apply hST
    apply Sylow.ext
    have := congrArg (fun P : Sylow 3 Y => (P : Subgroup Y)) heq
    simp only [Sylow.coe_mapSurjective] at this
    exact Subgroup.map_injective hinj this)
  simp only [Sylow.coe_mapSurjective] at h1
  rw [← Subgroup.map_inf_eq _ _ _ hinj] at h1
  exact (Subgroup.map_eq_bot_iff_of_injective _ hinj).1 h1

theorem tI_of_oPrimeResidual {X : Type} [Group X] [Finite X]
    (hY : ∀ S T : Sylow 3 ↥(CFSG.GH74.GLS.oPrimeResidual 3 X), S ≠ T →
      (S : Subgroup ↥(CFSG.GH74.GLS.oPrimeResidual 3 X)) ⊓ T = ⊥) :
    ∀ S T : Sylow 3 X, S ≠ T → (S : Subgroup X) ⊓ T = ⊥ := by
  intro S T hST
  set W := CFSG.GH74.GLS.oPrimeResidual 3 X with hW
  have hle : ∀ P : Sylow 3 X, (P : Subgroup X) ≤ W := by
    intro P x hx
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨x, hx⟩
    apply Subgroup.subset_closure
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  let toW : Sylow 3 X → Sylow 3 ↥W := fun P =>
    { toSubgroup := (P : Subgroup X).subgroupOf W
      isPGroup' := isPGroup_subgroupOf (hle P) P.isPGroup'
      is_maximal' := fun {Q} hQ hle' => by
        have h1 : (P : Subgroup X) ≤ Q.map W.subtype := by
          intro x hx
          exact ⟨⟨x, hle P hx⟩, hle' (Subgroup.mem_subgroupOf.2 hx), rfl⟩
        have h2 := P.is_maximal' (hQ.map W.subtype) h1
        rw [← h2]
        exact (Subgroup.comap_map_eq_self_of_injective W.subtype_injective Q).symm }
  have hmap : ∀ P : Sylow 3 X, ((toW P : Sylow 3 ↥W) : Subgroup ↥W).map W.subtype = P :=
    fun P => Subgroup.map_subgroupOf_eq_of_le (hle P)
  have hne : toW S ≠ toW T := fun heq => hST (Sylow.ext (by rw [← hmap S, ← hmap T, heq]))
  have h1 := hY _ _ hne
  rw [← hmap S, ← hmap T, ← Subgroup.map_inf_eq _ _ _ W.subtype_injective, h1, Subgroup.map_bot]

end TItransfer

theorem input_TI_L29_holds : Input_TI_L29 := by
  intro X _ _ hX
  apply tI_of_oPrimeResidual
  rcases hX with ⟨F, _, _, hF9, ⟨e⟩⟩ | ⟨F, _, _, hF9, ⟨e⟩⟩
  · exact tI_of_mulEquiv e (tI_statedProj hF9)
  · exact tI_of_mulEquiv e (tI_statedSL hF9)

theorem claim1211_TI_of_L29 (hL : Claim1211_L29) : Claim1211_TI :=
  claim1211_TI_of_inputs hL input_TI_L29_holds

@[expose] def Claim1211_noBeta : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A N D : Subgroup G}
    (_ : Cex127 G m p B M E A N D) {K : Subgroup G}, Lemma129Common p M E A N K →
      ((∃ Q : ℕ, p ∣ Q - 1 ∧ IsLpType p Q (barOf p K)) ∨
          (p = 5 ∧ IsSporType .Fi22 (barOf p K))) →
        Lemma129IvBData p N K E A → False

theorem claim1211_alpha_of_inputs (h129 : Lemma129PrintedStatement) (hβ : Claim1211_noBeta) :
    Claim1211_alpha := by
  intro G _ _ m p B M E A N D h
  obtain ⟨K, hK, hα | ⟨htype, hdata⟩⟩ := h129 h
  · exact ⟨K, hK, hα⟩
  · exact (hβ h hK htype hdata).elim

section Constraint

variable {G : Type} [Group G] [Finite G]

theorem isSylowIn_of_isSylowOf {p : ℕ} [Fact p.Prime] {P K : Subgroup G}
    (h : CFSG.ABGLocalTools.IsSylowOf p P K) : IsSylowIn p K P := by
  obtain ⟨Q, rfl⟩ := h
  refine ⟨Subgroup.map_subtype_le _, Q.isPGroup'.map _, fun R' hR'K hR'p hle => ?_⟩
  have h1 : (Q : Subgroup ↥K) ≤ R'.subgroupOf K := fun x hx =>
    Subgroup.mem_subgroupOf.2 (hle ⟨x, hx, rfl⟩)
  have h2 := Q.is_maximal' (isPGroup_subgroupOf hR'K hR'p) h1
  rw [← h2, Subgroup.map_subgroupOf_eq_of_le hR'K]

theorem isSylowIn_top_of_sylow {X : Type} [Group X] {p : ℕ} (S : Sylow p X) :
    IsSylowIn p ⊤ (S : Subgroup X) :=
  ⟨le_top, S.isPGroup', fun _ _ hR'p hle => S.is_maximal' hR'p hle⟩

theorem mem_normalizer_sup_of_normalizes {Y : Type} [Group Y] [Finite Y] {p : ℕ} [Fact p.Prime]
    {Q : Subgroup Y} (hQ : IsPGroup p ↥Q) {y : Y}
    (hy : y ∈ Subgroup.normalizer ((CFSG.pPrimeCore p Y ⊔ Q : Subgroup Y) : Set Y)) :
    y ∈ Subgroup.normalizer (Q : Set Y) ⊔ CFSG.pPrimeCore p Y := by
  have hS : IsSylowIn p (CFSG.pPrimeCore p Y ⊔ Q) Q := isSylowIn_of_isSylowOf
    (CFSG.ABGLocalTools.isSylowOf_sup_of_coprime CFSG.pPrimeCore_coprime_card hQ)
  have hW : GLBConj y (CFSG.pPrimeCore p Y ⊔ Q) = CFSG.pPrimeCore p Y ⊔ Q :=
    gLBConj_eq_of_mem_normalizer hy
  have hW' : GLBConj y⁻¹ (CFSG.pPrimeCore p Y ⊔ Q) = CFSG.pPrimeCore p Y ⊔ Q :=
    gLBConj_eq_of_mem_normalizer (Subgroup.inv_mem _ hy)
  have hS' : IsSylowIn p (CFSG.pPrimeCore p Y ⊔ Q) (GLBConj y Q) := by
    refine ⟨?_, isPGroup_gLBConj y hQ, fun R' hR' hR'p hle => ?_⟩
    · rw [← hW]
      exact gLBConj_mono y le_sup_right
    · have h1 : GLBConj y⁻¹ R' ≤ CFSG.pPrimeCore p Y ⊔ Q := by
        have := gLBConj_mono y⁻¹ hR'
        rwa [hW'] at this
      have h2 : Q ≤ GLBConj y⁻¹ R' := by
        have := gLBConj_mono y⁻¹ hle
        rwa [gLBConj_inv_gLBConj] at this
      have h3 := hS.2.2 _ h1 (isPGroup_gLBConj _ hR'p) h2
      rw [← h3, gLBConj_gLBConj_inv]
  obtain ⟨o, ho, hoeq⟩ := exists_gLBConj_eq hS hS'
  rw [gLBConj_gLBConj] at hoeq
  have hn : y * o ∈ Subgroup.normalizer (Q : Set Y) := mem_normalizer_iff_gLBConj_eq.2 hoeq
  have hoN : o ∈ Subgroup.normalizer (Q : Set Y) ⊔ CFSG.pPrimeCore p Y :=
    (sup_le le_sup_right (Subgroup.le_normalizer.trans le_sup_left)) ho
  have e : y = (y * o) * o⁻¹ := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hn) (Subgroup.inv_mem _ hoN)

end Constraint

section Pullback

variable {Y : Type} [Group Y] [Finite Y] {O : Subgroup Y} [O.Normal] {R' : Subgroup Y}

theorem eq_of_mk_eq (hRO : R' ⊓ O = ⊥) {u v : Y} (hu : u ∈ R') (hv : v ∈ R')
    (h : QuotientGroup.mk' O u = QuotientGroup.mk' O v) : u = v := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h
  have hm : u⁻¹ * v ∈ R' ⊓ O := ⟨R'.mul_mem (R'.inv_mem hu) hv, h⟩
  rw [hRO, Subgroup.mem_bot] at hm
  calc u = u * (u⁻¹ * v) := by rw [hm, mul_one]
    _ = v := by group

theorem card_map_mk_of_le (hRO : R' ⊓ O = ⊥) {U : Subgroup Y} (hUR : U ≤ R') :
    Nat.card ↥(U.map (QuotientGroup.mk' O)) = Nat.card ↥U := by
  have hinj : Function.Injective ((QuotientGroup.mk' O).comp U.subtype) := fun a b hab =>
    Subtype.ext (eq_of_mk_eq hRO (hUR a.2) (hUR b.2) hab)
  have h1 := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  rw [h1, MonoidHom.range_comp, Subgroup.range_subtype]

theorem map_pullback {Ū : Subgroup (Y ⧸ O)} (hŪ : Ū ≤ R'.map (QuotientGroup.mk' O)) :
    (Ū.comap (QuotientGroup.mk' O) ⊓ R').map (QuotientGroup.mk' O) = Ū := by
  apply le_antisymm
  · rintro _ ⟨u, hu, rfl⟩
    exact hu.1
  · intro x hx
    obtain ⟨r, hr, rfl⟩ := hŪ hx
    exact ⟨r, ⟨hx, hr⟩, rfl⟩

theorem card_pullback (hRO : R' ⊓ O = ⊥) {Ū : Subgroup (Y ⧸ O)}
    (hŪ : Ū ≤ R'.map (QuotientGroup.mk' O)) :
    Nat.card ↥(Ū.comap (QuotientGroup.mk' O) ⊓ R') = Nat.card ↥Ū := by
  rw [← card_map_mk_of_le hRO inf_le_right, map_pullback hŪ]

theorem isElemAbelian_pullback (hRO : R' ⊓ O = ⊥) {Ū : Subgroup (Y ⧸ O)}
    (hŪ : IsElemAbelian 3 Ū) : IsElemAbelian 3 (Ū.comap (QuotientGroup.mk' O) ⊓ R') := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun u hu => ?_⟩
  · have hc := congrArg Subtype.val (hŪ.1.is_comm.comm ⟨_, a.2.1⟩ ⟨_, b.2.1⟩)
    simp only [Subgroup.coe_mul] at hc ⊢
    exact eq_of_mk_eq hRO (R'.mul_mem a.2.2 b.2.2) (R'.mul_mem b.2.2 a.2.2)
      (by rw [map_mul, map_mul]; exact hc)
  · have h3 := hŪ.2 _ hu.1
    exact eq_of_mk_eq hRO (R'.pow_mem hu.2 3) R'.one_mem (by rw [map_pow, h3, map_one])

theorem exists_elemAbelian_pullback (hRO : R' ⊓ O = ⊥) {Ū : Subgroup (Y ⧸ O)}
    (hŪ : Ū ≤ R'.map (QuotientGroup.mk' O)) {k : ℕ} (hk : k ≤ CFSG.Open.pRank 3 Ū) :
    ∃ U : Subgroup Y, U ≤ Ū.comap (QuotientGroup.mk' O) ⊓ R' ∧ IsElemAbelian 3 U ∧
      Nat.card ↥U = 3 ^ k := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Vb, hVU, hV, hVc⟩ := exists_elemAbelian_card_pow_of_le_pRank' hk
  refine ⟨Vb.comap (QuotientGroup.mk' O) ⊓ R', inf_le_inf_right _ (Subgroup.comap_mono hVU),
    isElemAbelian_pullback hRO hV, ?_⟩
  rw [card_pullback hRO (hVU.trans hŪ), hVc]

end Pullback

@[expose] def Claim1211_ZR : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A N D : Subgroup G} (h : Cex127 G m p B M E A N D)
    {K : Subgroup G} (hK : AlphaData1211 p M E A N K) {z : G} (hz : z ∈ A ∧ z ≠ 1)
    (hz1 : IsPCentralIn p M z) (hz2 : ¬ Cg z ≤ M) {R : Subgroup G}, IsSylowIn 3 (Cg z) R →
      IsCyclic ↥(centerOf R)

theorem cTilde_isPConstrained_of_inputs (hI : Input24_5) (hZR : Claim1211_ZR) :
    ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A N D : Subgroup G}
      (h : Cex127 G m p B M E A N D) {K : Subgroup G} (hK : AlphaData1211 p M E A N K) {z : G}
      (hz : z ∈ A ∧ z ≠ 1) (hz1 : IsPCentralIn p M z) (hz2 : ¬ Cg z ≤ M),
      CFSG.ABGLocalTools.IsPConstrained 3 (↥(Cg z) ⧸ GLAPPrimeCore 3 ↥(Cg z)) := by
  intro G _ _ m p B M E A N D h K hK z hz hz1 hz2
  have hcyc : ∀ R : Subgroup G, IsSylowIn 3 (Cg z) R → IsCyclic ↥(centerOf R) :=
    fun R hR => hZR h hK hz hz1 hz2 hR
  obtain ⟨hcom, hp3, hE5, -⟩ := hK
  subst hp3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hOM, -⟩ := core_le h hcom.2.1.1 hcom.2.1.2 hE5 hz1
  obtain ⟨R₀, hR₀M, hzR₀⟩ := hz1
  obtain ⟨hR₀G, hΓ4, hΓ⟩ := setting_facts h hcom.2.1.1 hcom.2.1.2 hR₀M
  have hR₀C : R₀ ≤ Cg z := le_cg_of_mem_centerOf hzR₀
  have hR₀S : IsSylowIn 3 (Cg z) R₀ :=
    ⟨hR₀C, hR₀G.2.1, fun R' _ hR'p hle => hR₀G.2.2 R' le_top hR'p hle⟩
  set O : Subgroup ↥(Cg z) := GLAPPrimeCore 3 ↥(Cg z) with hOdef
  set π : ↥(Cg z) →* ↥(Cg z) ⧸ O := QuotientGroup.mk' O with hπdef
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective O
  set R' : Subgroup ↥(Cg z) := R₀.subgroupOf (Cg z) with hR'def
  have hR'p : IsPGroup 3 ↥R' := isPGroup_subgroupOf hR₀C hR₀G.2.1
  have hOc : Nat.Coprime 3 (Nat.card ↥O) := CFSG.pPrimeCore_coprime_card
  have hRO : R' ⊓ O = ⊥ := by
    obtain ⟨k, hk⟩ := hR'p.exists_card_eq
    apply disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard _)
    rw [hk]
    exact Nat.Coprime.pow_left k hOc
  have hR'map : R'.map (Cg z).subtype = R₀ := Subgroup.map_subgroupOf_eq_of_le hR₀C
  have hOM' : O ≤ M.subgroupOf (Cg z) := fun o ho =>
    Subgroup.mem_subgroupOf.2 (hOM ⟨o, ho, rfl⟩)
  have hCne : Cg z ≠ ⊤ := by
    intro htop
    have hzc : z ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ Cg z := htop ▸ Subgroup.mem_top g
      exact Subgroup.mem_centralizer_singleton_iff.1 hg
    rcases h.standing.simple.eq_bot_or_eq_top_of_normal (Subgroup.center G) with hbot | htop'
    · rw [hbot, Subgroup.mem_bot] at hzc
      exact hz.2 hzc
    · obtain ⟨a, b, hab⟩ := h.standing.nonabelian
      have hb : b ∈ Subgroup.center G := htop' ▸ Subgroup.mem_top b
      exact hab (Subgroup.mem_center_iff.1 hb a)
  have hKX : CFSG.Open.IsKGroup (↥(Cg z) ⧸ O) :=
    CFSG.KCore.KGroupNonab.quotient CFSG.Open.isCatalogGroup_isoInvariant
      (CFSG.KCore.KProperNonab.kGroupNonab CFSG.Open.isCatalogGroup_isoInvariant
        h.standing.kProper (Cg z) hCne) O
  have hOX : GLAPPrimeCore 3 (↥(Cg z) ⧸ O) = ⊥ :=
    CFSG.pPrimeCore_quotient_eq_bot (G := ↥(Cg z)) Nat.prime_three
  have hzC : z ∈ Cg z := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hZX : Subgroup.center (↥(Cg z) ⧸ O) ≠ ⊥ := by
    intro hbot
    have hmem : π ⟨z, hzC⟩ ∈ Subgroup.center (↥(Cg z) ⧸ O) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨y, rfl⟩ := hπs g
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.1 y.2
    rw [hbot, Subgroup.mem_bot, hπdef, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
    have hAel : IsElemAbelian 3 A := h.pair.1.2.1.1.1.2.1
    have hz3 : orderOf z = 3 := orderOf_eq_prime (hAel.2 z hz.1) hz.2
    have hdvd := orderOf_dvd_natCard (⟨⟨z, hzC⟩, hmem⟩ : ↥O)
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hz3] at hdvd
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hOc hdvd
  have h5 : 5 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (↥(Cg z) ⧸ O)) := by
    obtain ⟨H₅, hH₅R, hH₅, hH₅c⟩ := exists_ekIn hR₀G (k := 5) hE5
    have hUR : H₅.subgroupOf (Cg z) ≤ R' := Subgroup.subgroupOf_mono _ hH₅R
    have hUc : Nat.card ↥((H₅.subgroupOf (Cg z)).map π) = 3 ^ 5 := by
      rw [card_map_mk_of_le hRO hUR, ← hH₅c]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hH₅R.trans hR₀C)).toEquiv
    exact le_pRank_of_card le_top ((hH₅.subgroupOf _).map π) hUc
  set P : Subgroup (↥(Cg z) ⧸ O) := R'.map π with hPdef
  obtain ⟨S, hS⟩ := exists_sylow_of_isSylowIn hR₀S
  have hSR' : (S : Subgroup ↥(Cg z)) = R' := by
    rw [hR'def, ← hS]
    exact (Subgroup.comap_map_eq_self_of_injective (Cg z).subtype_injective _).symm
  have hPS : IsSylowIn 3 ⊤ P := by
    have := isSylowIn_top_of_sylow (S.mapSurjective hπs)
    rwa [Sylow.coe_mapSurjective, hSR'] at this
  have hPc : IsCyclic ↥(centerOf P) := by
    haveI := hcyc R₀ hR₀S
    have hinj : Function.Injective (π.comp R'.subtype) := fun a b hab =>
      Subtype.ext (eq_of_mk_eq hRO a.2 b.2 hab)
    have hrange : (π.comp R'.subtype).range = P := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    let e₂ : ↥R₀ ≃* ↥P := (Subgroup.subgroupOfEquivOfLe hR₀C).symm.trans
      ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange))
    let e : ↥(centerOf R₀) ≃* ↥(centerOf P) :=
      ((Subgroup.center ↥R₀).equivMapOfInjective R₀.subtype R₀.subtype_injective).symm.trans
        ((Subgroup.centerCongr e₂).trans
          ((Subgroup.center ↥P).equivMapOfInjective P.subtype P.subtype_injective))
    exact isCyclic_of_surjective e.toMonoidHom e.surjective
  rcases hI (↥(Cg z) ⧸ O) 3 hKX Nat.prime_three (by norm_num) hOX hZX h5 P hPS hPc with
    hc | hgen
  · exact hc
  exfalso
  set Mbar : Subgroup (↥(Cg z) ⧸ O) := (M.subgroupOf (Cg z)).map π with hMbar
  have KL : ∀ Qb : Subgroup (↥(Cg z) ⧸ O), Qb ≤ P →
      Subgroup.normalizer (((Qb.comap π ⊓ R').map (Cg z).subtype : Subgroup G) : Set G) ≤ M →
      Subgroup.normalizer (Qb : Set (↥(Cg z) ⧸ O)) ≤ Mbar := by
    intro Qb hQbP hN xb hxb
    obtain ⟨y, rfl⟩ := hπs xb
    have hQ₁p : IsPGroup 3 ↥(Qb.comap π ⊓ R') := hR'p.to_le inf_le_right
    have hW : Qb.comap π = CFSG.pPrimeCore 3 ↥(Cg z) ⊔ (Qb.comap π ⊓ R') := by
      apply le_antisymm
      · intro w hw
        obtain ⟨r, hr, hrw⟩ := hQbP hw
        have hrQ : r ∈ Qb.comap π ⊓ R' :=
          Subgroup.mem_inf.2 ⟨by rw [Subgroup.mem_comap, hrw]; exact hw, hr⟩
        have hro : r⁻¹ * w ∈ O := by
          rw [hπdef, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hrw
          exact hrw
        have e : w = r * (r⁻¹ * w) := by group
        rw [e]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hrQ) (Subgroup.mem_sup_left hro)
      · refine sup_le (fun o ho => ?_) inf_le_left
        rw [Subgroup.mem_comap]
        have : π o = 1 := by
          rw [hπdef, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
          exact ho
        rw [this]
        exact Qb.one_mem
    have hyW : y ∈ Subgroup.normalizer
        ((CFSG.pPrimeCore 3 ↥(Cg z) ⊔ (Qb.comap π ⊓ R') : Subgroup ↥(Cg z)) : Set ↥(Cg z)) := by
      rw [← hW]
      exact Subgroup.le_normalizer_comap π hxb
    have hy := mem_normalizer_sup_of_normalizes hQ₁p hyW
    have hNQ : Subgroup.normalizer (((Qb.comap π ⊓ R') : Subgroup ↥(Cg z)) : Set ↥(Cg z)) ≤
        M.subgroupOf (Cg z) := by
      intro n hn
      rw [Subgroup.mem_subgroupOf]
      exact hN (Subgroup.le_normalizer_map (Cg z).subtype ⟨n, hn, rfl⟩)
    exact ⟨y, (sup_le hNQ hOM') hy, rfl⟩
  have hpbR : ∀ Qb : Subgroup (↥(Cg z) ⧸ O), (Qb.comap π ⊓ R').map (Cg z).subtype ≤ R₀ :=
    fun Qb => (Subgroup.map_mono inf_le_right).trans hR'map.le
  have hpbRank : ∀ Qb : Subgroup (↥(Cg z) ⧸ O), Qb ≤ P → ∀ k : ℕ, k ≤ CFSG.Open.pRank 3 Qb →
      k ≤ CFSG.Open.pRank 3 ((Qb.comap π ⊓ R').map (Cg z).subtype) := by
    intro Qb hQbP k hk
    obtain ⟨U, hU, hUel, hUc⟩ := exists_elemAbelian_pullback hRO hQbP hk
    refine le_pRank_of_card (Subgroup.map_mono hU) (hUel.map _) ?_
    rw [Subgroup.card_map_of_injective (Cg z).subtype_injective, hUc]
  have hΓP : GLBCore 3 4 P ≤ Mbar := by
    unfold GLBCore
    refine sSup_le ?_
    rintro _ ⟨Qb, hQbP, hrk, rfl⟩
    refine KL Qb hQbP ?_
    have hN0 : Subgroup.normalizer
        (((Qb.comap π ⊓ R').map (Cg z).subtype : Subgroup G) : Set G) ≤ GLBCore 3 4 R₀ :=
      le_sSup ⟨_, hpbR Qb, hpbRank Qb hQbP 4 hrk, rfl⟩
    exact hN0.trans hΓ4
  have hΓE : ∀ Eb : Subgroup (↥(Cg z) ⧸ O), IsEkIn 3 4 P Eb → GLBCore 3 2 Eb ≤ Mbar := by
    intro Eb hEb
    unfold GLBCore
    refine sSup_le ?_
    rintro _ ⟨Tb, hTbE, hrk, rfl⟩
    refine KL Tb (hTbE.trans hEb.1) ?_
    have hH : IsEkIn 3 4 R₀ ((Eb.comap π ⊓ R').map (Cg z).subtype) := by
      refine ⟨hpbR Eb, (isElemAbelian_pullback hRO hEb.2.1).map _, ?_⟩
      rw [Subgroup.card_map_of_injective (Cg z).subtype_injective, card_pullback hRO hEb.1,
        hEb.2.2]
    exact hΓ _ hH _ (Subgroup.map_mono (inf_le_inf_right _ (Subgroup.comap_mono hTbE)))
      (hpbRank Tb (hTbE.trans hEb.1) 2 hrk)
  have htop : (⊤ : Subgroup (↥(Cg z) ⧸ O)) ≤ Mbar := by
    rw [hgen]
    exact sup_le hΓP (iSup₂_le hΓE)
  apply hz2
  intro c hc
  obtain ⟨m', hm', hm'eq⟩ := htop (Subgroup.mem_top (π ⟨c, hc⟩))
  have hO' : m'⁻¹ * ⟨c, hc⟩ ∈ O := by
    rw [hπdef, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hm'eq
    exact hm'eq
  have hcM : (⟨c, hc⟩ : ↥(Cg z)) ∈ M.subgroupOf (Cg z) := by
    have e : (⟨c, hc⟩ : ↥(Cg z)) = m' * (m'⁻¹ * ⟨c, hc⟩) := by group
    rw [e]
    exact Subgroup.mul_mem _ hm' (hOM' hO')
  exact Subgroup.mem_subgroupOf.1 hcM

theorem isCyclic_centerOf_of_mulEquiv {G : Type} [Group G] {P Q : Subgroup G} (e : ↥P ≃* ↥Q)
    (h : IsCyclic ↥(centerOf P)) : IsCyclic ↥(centerOf Q) := by
  let e' : ↥(centerOf P) ≃* ↥(centerOf Q) :=
    ((Subgroup.center ↥P).equivMapOfInjective P.subtype P.subtype_injective).symm.trans
      ((Subgroup.centerCongr e).trans
        ((Subgroup.center ↥Q).equivMapOfInjective Q.subtype Q.subtype_injective))
  exact isCyclic_of_surjective e'.toMonoidHom e'.surjective

@[expose] def Claim1211_A0 : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A N D : Subgroup G} (h : Cex127 G m p B M E A N D)
    {K : Subgroup G} (hK : AlphaData1211 p M E A N K),
    ∃ x : G, (∃ k : ℕ, x ^ (3 ^ k) = 1) ∧ x ∈ Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G) ∧
      x ∉ Subgroup.centralizer ((E ⊓ A : Subgroup G) : Set G)

theorem claim1211_ZR_of_A0 (hA0 : Claim1211_A0) : Claim1211_ZR := by
  intro G _ _ m p B M E A N D h K hK z hz hz1 hz2 R hR
  obtain ⟨x, ⟨kx, hxk⟩, hxN, hxC⟩ := hA0 h hK
  obtain ⟨hcom, hp3, hE5, -⟩ := hK
  subst hp3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hF := h.toSec11.toSec10Fails
  have hEA := h.pair
  obtain ⟨R₀, hR₀M, hzR₀⟩ := hz1
  obtain ⟨hR₀G, -, -⟩ := setting_facts h hcom.2.1.1 hcom.2.1.2 hR₀M
  have hR₀S : IsSylowIn 3 (Cg z) R₀ :=
    ⟨le_cg_of_mem_centerOf hzR₀, hR₀G.2.1, fun R' _ hR'p hle => hR₀G.2.2 R' le_top hR'p hle⟩
  obtain ⟨c, -, hc⟩ := exists_gLBConj_eq hR hR₀S
  have hRG : IsSylowIn 3 ⊤ R := hc ▸ isSylowIn_top_gLBConj hR₀G c
  have hEAp : IsPGroup 3 ↥(E ⊔ A) := lemma104_i_holds hF hEA
  obtain ⟨g, -, T, hTp, -, hRT, hEAT⟩ :=
    exists_conj_le_pGroup' (le_top : R ≤ ⊤) hRG.2.1 (le_top : E ⊔ A ≤ ⊤) hEAp
  have hTR : T = R := hRG.2.2 T le_top hTp hRT
  rw [hTR] at hEAT
  have hEARs : E ⊔ A ≤ GLBConj g⁻¹ R := by
    have := gLBConj_mono g⁻¹ hEAT
    rwa [gLBConj_inv_gLBConj] at this
  have hRsG : IsSylowIn 3 ⊤ (GLBConj g⁻¹ R) := isSylowIn_top_gLBConj hRG g⁻¹
  suffices hcyc : IsCyclic ↥(centerOf (GLBConj g⁻¹ R)) by
    have hmap : (GLBConj g⁻¹ R).map (MulAut.conj g⁻¹).toMonoidHom = R :=
      gLBConj_gLBConj_inv g R
    let e : ↥(GLBConj g⁻¹ R) ≃* ↥R :=
      ((GLBConj g⁻¹ R).equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom
        (MulAut.conj g⁻¹).injective).trans (MulEquiv.subgroupCongr hmap)
    exact isCyclic_centerOf_of_mulEquiv e hcyc
  by_contra hnc
  have hZp : IsPGroup 3 ↥(centerOf (GLBConj g⁻¹ R)) :=
    isPGroup_of_le' hRsG.2.1 (Subgroup.map_subtype_le _)
  obtain ⟨V, hVZ, hVel, hVc⟩ : ∃ V : Subgroup G, V ≤ centerOf (GLBConj g⁻¹ R) ∧
      IsElemAbelian 3 V ∧ Nat.card ↥V = 9 := by
    by_contra hnone
    apply hnc
    refine Lemma1211Cyc.input_cyc3_holds _ hZp (fun E' hE' => ?_)
    by_contra hgt
    push Not at hgt
    obtain ⟨j, hj⟩ := hE'.isPGroup.exists_card_eq
    have hj2 : 2 ≤ j := by
      by_contra hj2
      push Not at hj2
      interval_cases j <;> omega
    have hdvd : 3 ^ 2 ∣ Nat.card ↥E' := by
      rw [hj]
      exact pow_dvd_pow 3 hj2
    obtain ⟨H9, hH9⟩ := Sylow.exists_subgroup_card_pow_prime 3 hdvd
    apply hnone
    refine ⟨(H9.map E'.subtype).map (centerOf (GLBConj g⁻¹ R)).subtype,
      Subgroup.map_subtype_le _, ((hE'.mono (Subgroup.map_subtype_le H9)).map _), ?_⟩
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
      Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hH9]
    norm_num
  have hVcomm : ∀ v ∈ V, ∀ r ∈ GLBConj g⁻¹ R, r * v = v * r := fun v hv r hr =>
    ((mem_centerOf_iff' (GLBConj g⁻¹ R) v).1 (hVZ hv)).2 r hr
  have hSC := lemma104_ii_holds hF hEA
  have hVle : ∀ X : Subgroup G, IsSCp 3 ⊤ X → X ≤ GLBConj g⁻¹ R → V ≤ X := by
    intro X hX hXR
    have hsup : IsElemAbelian 3 (V ⊔ X) := Lemma1111.isElemAbelian_sup hVel hX.2.1
      (fun v hv e he => (hVcomm v hv e (hXR he)).symm)
    have := hX.2.2 (V ⊔ X) le_top hsup le_sup_right
    rw [← this]
    exact le_sup_left
  have hVE := hVle E hSC.1 (le_sup_left.trans hEARs)
  have hVA := hVle A hSC.2 (le_sup_right.trans hEARs)
  have hV0 : V = E ⊓ A := by
    have hA0el : IsElemAbelian 3 (E ⊓ A) := hSC.1.2.1.mono inf_le_left
    obtain ⟨j, hj⟩ := hA0el.isPGroup.exists_card_eq
    have hjle : j ≤ 2 := by
      have := le_pRank_of_card le_rfl hA0el hj
      rwa [hcom.2.1.2] at this
    refine Subgroup.eq_of_le_of_card_ge (le_inf hVE hVA) ?_
    rw [hj, hVc]
    calc 3 ^ j ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hjle
      _ = 9 := by norm_num
  have hRsC : GLBConj g⁻¹ R ≤ Subgroup.centralizer ((E ⊓ A : Subgroup G) : Set G) := by
    intro r hr
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    rw [← hV0] at ha
    exact (hVcomm a ha r hr).symm
  have hCN : Subgroup.centralizer ((E ⊓ A : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G) := Subgroup.centralizer_le_normalizer _
  have hRsN : IsSylowIn 3 (Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G)) (GLBConj g⁻¹ R) :=
    ⟨hRsC.trans hCN, hRsG.2.1, fun R' _ hR'p hle => hRsG.2.2 R' le_top hR'p hle⟩
  have hxp : IsPGroup 3 ↥(Subgroup.zpowers x) := by
    intro y
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 y.2
    refine ⟨kx, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxk, one_zpow]
  obtain ⟨n, hnN, S', hS'p, hS'N, hRsS', hxS'⟩ :=
    exists_conj_le_pGroup' hRsN.1 hRsN.2.1 (Subgroup.zpowers_le.2 hxN) hxp
  have hS'eq : S' = GLBConj g⁻¹ R := hRsN.2.2 S' hS'N hS'p hRsS'
  rw [hS'eq] at hxS'
  have hmem : n⁻¹ * x * n ∈ Subgroup.centralizer ((E ⊓ A : Subgroup G) : Set G) := by
    apply hRsC
    apply hxS'
    rw [mem_gLBConj]
    have e : n * (n⁻¹ * x * n) * n⁻¹ = x := by group
    rw [e]
    exact Subgroup.mem_zpowers x
  apply hxC
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have ha' : n⁻¹ * a * n⁻¹⁻¹ ∈ E ⊓ A :=
    (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hnN) a).1 ha
  rw [inv_inv] at ha'
  have hc' := (Subgroup.mem_centralizer_iff.1 hmem) _ ha'
  calc a * x = n * ((n⁻¹ * a * n) * (n⁻¹ * x * n)) * n⁻¹ := by group
    _ = n * ((n⁻¹ * x * n) * (n⁻¹ * a * n)) * n⁻¹ := by rw [hc']
    _ = x * a := by group

theorem cTilde_isPConstrained_of_A0 (hI : Input24_5) (hA0 : Claim1211_A0) :
    ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A N D : Subgroup G}
      (h : Cex127 G m p B M E A N D) {K : Subgroup G} (hK : AlphaData1211 p M E A N K) {z : G}
      (hz : z ∈ A ∧ z ≠ 1) (hz1 : IsPCentralIn p M z) (hz2 : ¬ Cg z ≤ M),
      CFSG.ABGLocalTools.IsPConstrained 3 (↥(Cg z) ⧸ GLAPPrimeCore 3 ↥(Cg z)) := by
  intro G _ _ m p B M E A N D h K hK z hz hz1 hz2
  exact cTilde_isPConstrained_of_inputs hI (claim1211_ZR_of_A0 hA0) h hK hz hz1 hz2

@[expose] def Claim1211_A0bar : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A N D : Subgroup G} (h : Cex127 G m p B M E A N D)
    {K : Subgroup G} (hK : AlphaData1211 p M E A N K),
    ∃ xb : ↥N ⧸ GLAPPrimeCore 3 ↥N, (∃ k : ℕ, xb ^ (3 ^ k) = 1) ∧
      xb ∈ Subgroup.normalizer ((barX 3 N (E ⊓ A) : Subgroup (↥N ⧸ GLAPPrimeCore 3 ↥N)) :
        Set (↥N ⧸ GLAPPrimeCore 3 ↥N)) ∧
      xb ∉ Subgroup.centralizer ((barX 3 N (E ⊓ A) : Subgroup (↥N ⧸ GLAPPrimeCore 3 ↥N)) :
        Set (↥N ⧸ GLAPPrimeCore 3 ↥N))

theorem claim1211_A0_of_A0bar (hb : Claim1211_A0bar) : Claim1211_A0 := by
  intro G _ _ m p B M E A N D h K hK
  obtain ⟨xb, ⟨k, hk⟩, hxN, hxC⟩ := hb h hK
  obtain ⟨hcom, hp3, -, -⟩ := hK
  subst hp3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAel : IsElemAbelian 3 A := h.pair.1.2.1.1.1.2.1
  have hAN : A ≤ N := by
    intro a ha
    apply h.hD
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun d hd => ?_)
    exact congrArg Subtype.val (hAel.1.is_comm.comm ⟨d, h.plane.1 hd⟩ ⟨a, ha⟩)
  have hA₀N : E ⊓ A ≤ N := inf_le_right.trans hAN
  obtain ⟨y, hyx⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥N) xb
  subst hyx
  set O := GLAPPrimeCore 3 ↥N with hOdef
  set π : ↥N →* ↥N ⧸ O := QuotientGroup.mk' O with hπdef
  set A₀' : Subgroup ↥N := (E ⊓ A).subgroupOf N with hA₀'def
  have hA₀p : IsPGroup 3 ↥A₀' := isPGroup_subgroupOf hA₀N ((hAel.mono inf_le_right).isPGroup)
  have hW : (barX 3 N (E ⊓ A)).comap π = CFSG.pPrimeCore 3 ↥N ⊔ A₀' := by
    unfold barX
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_comm]
    rfl
  have hyW : y ∈ Subgroup.normalizer ((CFSG.pPrimeCore 3 ↥N ⊔ A₀' : Subgroup ↥N) : Set ↥N) := by
    rw [← hW]
    exact Subgroup.le_normalizer_comap π hxN
  have hy := mem_normalizer_sup_of_normalizes hA₀p hyW
  obtain ⟨n, hn, o, ho, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hy
  have hπn : π (n * o) = π n := by
    rw [map_mul, show π o = 1 from (QuotientGroup.eq_one_iff o).2 ho, mul_one]
  rw [hπn] at hk hxC
  obtain ⟨a, b, hb3, hord⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos n).ne' 3 (by norm_num)
  have hcop : b.Coprime (orderOf (π n)) := by
    have hdvd : orderOf (π n) ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    rw [hj]
    exact Nat.Coprime.pow_right j ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hb3).symm
  obtain ⟨m', hm'⟩ := exists_pow_eq_self_of_coprime hcop
  have hnbC : n ^ b ∉ Subgroup.centralizer ((A₀' : Subgroup ↥N) : Set ↥N) := by
    intro hc
    apply hxC
    have hc' : π (n ^ b) ∈ Subgroup.centralizer ((barX 3 N (E ⊓ A) :
        Subgroup (↥N ⧸ O)) : Set (↥N ⧸ O)) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨u, hu, rfl⟩
      rw [← map_mul, ← map_mul, (Subgroup.mem_centralizer_iff.1 hc) u hu]
    rw [← hm', ← map_pow]
    exact Subgroup.pow_mem _ hc' m'
  refine ⟨((n ^ b : ↥N) : G), ⟨a, ?_⟩, ?_, ?_⟩
  · rw [← Subgroup.coe_pow, ← pow_mul, mul_comm, ← hord, pow_orderOf_eq_one, Subgroup.coe_one]
  · have h1 : ((n ^ b : ↥N) : G) ∈ (Subgroup.normalizer ((A₀' : Subgroup ↥N) : Set ↥N)).map N.subtype :=
      ⟨n ^ b, Subgroup.pow_mem _ hn b, rfl⟩
    have h2 := Subgroup.le_normalizer_map N.subtype h1
    rwa [hA₀'def, Subgroup.map_subgroupOf_eq_of_le hA₀N] at h2
  · intro hc
    apply hnbC
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.1 hc) (u : G) (Subgroup.mem_subgroupOf.1 hu)

theorem cTilde_isPConstrained_of_A0bar (hI : Input24_5) (hb : Claim1211_A0bar) :
    ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A N D : Subgroup G}
      (h : Cex127 G m p B M E A N D) {K : Subgroup G} (hK : AlphaData1211 p M E A N K) {z : G}
      (hz : z ∈ A ∧ z ≠ 1) (hz1 : IsPCentralIn p M z) (hz2 : ¬ Cg z ≤ M),
      CFSG.ABGLocalTools.IsPConstrained 3 (↥(Cg z) ⧸ GLAPPrimeCore 3 ↥(Cg z)) :=
  cTilde_isPConstrained_of_A0 hI (claim1211_A0_of_A0bar hb)

theorem claim1211_rank4_of_inputs (hI : Input24_5) (hb : Claim1211_A0bar) (h4 : ∀ {G : Type} [Group
    G] [Finite G] {m p : ℕ} {B M E A N D : Subgroup G} (h : Cex127 G m p B M E A N D) {K : Subgroup
    G} (hK : AlphaData1211 p M E A N K) {z : G} (hz : z ∈ A ∧ z ≠ 1) (hz1 : IsPCentralIn p M z) (hz2
    : ¬ Cg z ≤ M), CFSG.ABGLocalTools.IsPConstrained 3 (↥(Cg z) ⧸ GLAPPrimeCore 3 ↥(Cg z)) → ∀ {R :
    Subgroup G} (hR : IsSylowIn 3 (Cg z) R) (hAR : A ≤ R) (hRM : R ≤ M) (C : Subgroup ↥(R ⊓
    pPrimePCore 3 (Cg z))), CFSG.SectionRank.Ccomm.IsThompsonCritical C → 3 ^ 4 * Nat.card
    ↥⁅omegaOne 3 (C.map (R ⊓ pPrimePCore 3 (Cg z)).subtype), omegaOne 3 (C.map (R ⊓ pPrimePCore 3
    (Cg z)).subtype)⁆ ≤ Nat.card ↥(omegaOne 3 (C.map (R ⊓ pPrimePCore 3 (Cg z)).subtype))) :
    Claim1211_rank4 := by
  intro G _ _ m p B M E A N D h K hK z hz hz1 hz2 R hR hAR hRM C hC
  exact h4 h hK hz hz1 hz2 (cTilde_isPConstrained_of_A0bar hI hb h hK hz hz1 hz2) hR hAR hRM C hC

theorem claim1211_L29_of_inputs (hI : Input24_5) (hb : Claim1211_A0bar) (hL : ∀ {G : Type} [Group G]
    [Finite G] {m p : ℕ} {B M E A N D : Subgroup G} (h : Cex127 G m p B M E A N D) {K : Subgroup G}
    (hK : AlphaData1211 p M E A N K) {z : G} (hz : z ∈ A ∧ z ≠ 1) (hz1 : IsPCentralIn p M z) (hz2 :
    ¬ Cg z ≤ M), CFSG.ABGLocalTools.IsPConstrained 3 (↥(Cg z) ⧸ GLAPPrimeCore 3 ↥(Cg z)) → IsLpType
    2 9 ↥(CFSG.GH74.GLS.oPrimeResidual 3 (↥(Cg z) ⧸ CFSG.GH74.GLS.pPrimePCore 3 ↥(Cg z))) ∨
    IsSL2Nine ↥(CFSG.GH74.GLS.oPrimeResidual 3 (↥(Cg z) ⧸ CFSG.GH74.GLS.pPrimePCore 3 ↥(Cg z)))) :
    Claim1211_L29 := by
  intro G _ _ m p B M E A N D h K hK z hz hz1 hz2
  exact hL h hK hz hz1 hz2 (cTilde_isPConstrained_of_A0bar hI hb h hK hz hz1 hz2)

theorem lemma1211_of_subclaims (h129 : Lemma129PrintedStatement) (h1210 : Lemma1210Statement)
    (h4 : Claim1211_rank4) (hL : Claim1211_L29) (hβ : Claim1211_noBeta) : Lemma1211Statement :=
  lemma1211_of_inputs'' h129 h1210 (claim1211_alpha_of_inputs h129 hβ) (claim1211_R3_of_rank4 h4)
    claim1211_m3_holds (claim1211_TI_of_L29 hL) claim1211_OM_holds

theorem lemma1211_of_subclaims' (h129 : Lemma129PrintedStatement) (h1210 : Lemma1210Statement)
    (hI : Input24_5) (hb : Claim1211_A0bar) (h4 : ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E
        A N D : Subgroup G} (h : Cex127 G m p B M E A N D) {K : Subgroup G} (hK : AlphaData1211 p M
        E A N K) {z : G} (hz : z ∈ A ∧ z ≠ 1) (hz1 : IsPCentralIn p M z) (hz2 : ¬ Cg z ≤ M),
        CFSG.ABGLocalTools.IsPConstrained 3 (↥(Cg z) ⧸ GLAPPrimeCore 3 ↥(Cg z)) → ∀ {R : Subgroup G}
        (hR : IsSylowIn 3 (Cg z) R) (hAR : A ≤ R) (hRM : R ≤ M) (C : Subgroup ↥(R ⊓ pPrimePCore 3
        (Cg z))), CFSG.SectionRank.Ccomm.IsThompsonCritical C → 3 ^ 4 * Nat.card ↥⁅omegaOne 3 (C.map
        (R ⊓ pPrimePCore 3 (Cg z)).subtype), omegaOne 3 (C.map (R ⊓ pPrimePCore 3 (Cg z)).subtype)⁆
        ≤ Nat.card ↥(omegaOne 3 (C.map (R ⊓ pPrimePCore 3 (Cg z)).subtype))) (hL : ∀ {G : Type} [Group G]
        [Finite G] {m p : ℕ} {B M E A N D : Subgroup G} (h : Cex127 G m p B M E A N D) {K : Subgroup
        G} (hK : AlphaData1211 p M E A N K) {z : G} (hz : z ∈ A ∧ z ≠ 1) (hz1 : IsPCentralIn p M z)
        (hz2 : ¬ Cg z ≤ M), CFSG.ABGLocalTools.IsPConstrained 3 (↥(Cg z) ⧸ GLAPPrimeCore 3 ↥(Cg z))
        → IsLpType 2 9 ↥(CFSG.GH74.GLS.oPrimeResidual 3 (↥(Cg z) ⧸ CFSG.GH74.GLS.pPrimePCore 3 ↥(Cg
        z))) ∨ IsSL2Nine ↥(CFSG.GH74.GLS.oPrimeResidual 3 (↥(Cg z) ⧸ CFSG.GH74.GLS.pPrimePCore 3
        ↥(Cg z))))
    (hβ : Claim1211_noBeta) : Lemma1211Statement :=
  lemma1211_of_subclaims h129 h1210 (claim1211_rank4_of_inputs hI hb h4)
    (claim1211_L29_of_inputs hI hb hL) hβ

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1211
