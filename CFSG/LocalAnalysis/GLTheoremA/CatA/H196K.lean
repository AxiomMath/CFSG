module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H196Facts
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open scoped commutatorElement
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple catalogIs ambiguousChev)

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance

theorem innerAut_normal (K : Type) [Group K] : (innerAut K).Normal := by
  constructor
  intro n hn g
  obtain ⟨k, rfl⟩ := hn
  refine ⟨g k, ?_⟩
  ext x
  simp [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv]

theorem ker_conj_eq_center (K : Type) [Group K] :
    (MulAut.conj : K →* MulAut K).ker = Subgroup.center K := by
  ext k
  rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
  constructor
  · intro h g
    have := congrArg (fun φ : MulAut K => φ g) h
    simp [MulAut.conj_apply] at this
    exact (mul_inv_eq_iff_eq_mul.1 this).symm
  · intro h
    ext x
    have hx := h x
    simp only [MulAut.conj_apply, MulAut.one_apply]
    rw [← hx]
    group

noncomputable def innerAut_equiv (K : Type) [Group K] :
    ↥(innerAut K) ≃* K ⧸ Subgroup.center K :=
  ((QuotientGroup.quotientMulEquivOfEq (ker_conj_eq_center K)).symm.trans
    (QuotientGroup.quotientKerEquivRange (MulAut.conj : K →* MulAut K))).symm

theorem isSimpleGroup_innerAut {K : Type} [Group K] (hK : CFSG.Open.IsQuasisimple K) :
    IsSimpleGroup ↥(innerAut K) :=
  (MulEquiv.isSimpleGroup_congr (innerAut_equiv K)).2 hK.2

theorem centralizer_innerAut_eq_bot {K : Type} [Group K] (hK : CFSG.Open.IsQuasisimple K) :
    Subgroup.centralizer ((innerAut K : Subgroup (MulAut K)) : Set (MulAut K)) = ⊥ := by
  rw [eq_bot_iff]
  intro φ hφ
  rw [Subgroup.mem_centralizer_iff] at hφ
  have hkey : ∀ k y : K, φ k * y * (φ k)⁻¹ = k * y * k⁻¹ := by
    intro k y
    have h1 := congrArg (fun ψ : MulAut K => ψ (φ.symm y))
      (hφ (MulAut.conj k) ⟨k, rfl⟩)
    simp [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv] at h1
    simpa using h1.symm
  have hcen : ∀ k y : K, (k⁻¹ * φ k) * y = y * (k⁻¹ * φ k) := by
    intro k y
    have e : (k⁻¹ * φ k) * y * (k⁻¹ * φ k)⁻¹ = k⁻¹ * (φ k * y * (φ k)⁻¹) * k := by group
    rw [hkey k y] at e
    have e2 : k⁻¹ * (k * y * k⁻¹) * k = y := by group
    rw [e2] at e
    calc (k⁻¹ * φ k) * y = ((k⁻¹ * φ k) * y * (k⁻¹ * φ k)⁻¹) * (k⁻¹ * φ k) := by group
      _ = y * (k⁻¹ * φ k) := by rw [e]
  set c : K → K := fun k => k⁻¹ * φ k with hc
  have hcmul : ∀ k l : K, c (k * l) = c k * c l := by
    intro k l
    have hc' : (k⁻¹ * φ k) * l⁻¹ = l⁻¹ * (k⁻¹ * φ k) := hcen k l⁻¹
    simp only [hc, map_mul]
    calc (k * l)⁻¹ * (φ k * φ l) = l⁻¹ * (k⁻¹ * φ k) * φ l := by group
      _ = (k⁻¹ * φ k) * l⁻¹ * φ l := by rw [hc']
      _ = _ := by group
  have hc1 : c 1 = 1 := by simp [hc]
  have hcinv : ∀ k : K, c k⁻¹ = (c k)⁻¹ := by
    intro k
    have h := hcmul k k⁻¹
    rw [mul_inv_cancel, hc1] at h
    exact eq_inv_of_mul_eq_one_right h.symm
  let L : Subgroup K :=
    { carrier := {k | c k = 1}
      one_mem' := hc1
      mul_mem' := fun {a b} ha hb => by
        show c (a * b) = 1
        rw [hcmul, show c a = 1 from ha, show c b = 1 from hb, one_mul]
      inv_mem' := fun {a} ha => by
        show c a⁻¹ = 1
        rw [hcinv, show c a = 1 from ha, inv_one] }
  have hcomm : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ ≤ L := by
    rw [Subgroup.commutator_le]
    intro a _ b _
    show c (⁅a, b⁆) = 1
    rw [commutatorElement_def, hcmul, hcmul, hcmul, hcinv, hcinv]
    have hC : c a * c b = c b * c a := hcen (a) (c b)
    calc c a * c b * (c a)⁻¹ * (c b)⁻¹ = c b * c a * (c a)⁻¹ * (c b)⁻¹ := by rw [hC]
      _ = 1 := by group
  have htop : ∀ k : K, c k = 1 := by
    intro k
    have hk : k ∈ (⊤ : Subgroup K) := Subgroup.mem_top k
    have : (⊤ : Subgroup K) ≤ L := by
      rw [← hK.1]
      exact hcomm
    exact this hk
  ext x
  have hx := htop x
  simp only [hc] at hx
  rw [MulAut.one_apply]
  exact (inv_mul_eq_one.1 hx).symm

theorem nonabelian_innerAut {K : Type} [Group K] (hK : CFSG.Open.IsQuasisimple K) :
    ∃ a b : ↥(innerAut K), a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  have hcenter : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ ≤ Subgroup.center K := by
    rw [Subgroup.commutator_le]
    intro a _ b _
    rw [commutatorElement_def, ← ker_conj_eq_center K, MonoidHom.mem_ker]
    have h2 : MulAut.conj a * MulAut.conj b = MulAut.conj b * MulAut.conj a :=
      congrArg Subtype.val (hcon ⟨MulAut.conj a, ⟨a, rfl⟩⟩ ⟨MulAut.conj b, ⟨b, rfl⟩⟩)
    calc MulAut.conj (a * b * a⁻¹ * b⁻¹)
        = MulAut.conj a * MulAut.conj b * (MulAut.conj a)⁻¹ * (MulAut.conj b)⁻¹ := by
          simp [map_mul, map_inv]
      _ = (MulAut.conj b * MulAut.conj a) * (MulAut.conj a)⁻¹ * (MulAut.conj b)⁻¹ := by
          rw [h2]
      _ = 1 := by group
  have htop : (⊤ : Subgroup K) ≤ Subgroup.center K := by
    rw [← hK.1]
    exact hcenter
  haveI : IsSimpleGroup (K ⧸ Subgroup.center K) := hK.2
  obtain ⟨x, y, hxy⟩ := exists_pair_ne (K ⧸ Subgroup.center K)
  apply hxy
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  rw [QuotientGroup.eq]
  exact htop (Subgroup.mem_top _)

theorem isChevOfChar_of_mulEquiv {p : ℕ} {Q R : Type} [Group Q] [Group R] (e : Q ≃* R)
    (h : CFSG.HardMathSupport.Solomon.Coordinator.IsChevOfChar p R) :
    CFSG.HardMathSupport.Solomon.Coordinator.IsChevOfChar p Q := by
  obtain ⟨d, hd, ⟨e0⟩⟩ := h
  exact ⟨d, hd, ⟨e.trans e0⟩⟩

theorem h196CatalogIs_of_mulEquiv {Q R : Type} [Group Q] [Group R] (e : Q ≃* R)
    {P : TauCeti.CFSGIndex → Prop} (h : catalogIs R P) : catalogIs Q P := by
  obtain ⟨d, hd, ⟨e0⟩⟩ := h
  exact ⟨d, hd, ⟨e.trans e0⟩⟩

theorem isChevCases_innerAut {p : ℕ} {K : Type} [Group K] [Finite K] (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : CFSG.Open.IsQuasisimple K) (hch : IsChevSimple p (K ⧸ Subgroup.center K))
    (hF : I196ChevCat p) :
    CFSG.HardMathSupport.Solomon.Coordinator.IsChevOfChar p ↥(innerAut K) ∨
      catalogIs ↥(innerAut K) (ambiguousChev p) := by
  have hs : IsSimpleGroup (K ⧸ Subgroup.center K) := hK.2
  rcases hF hp hp2 (K ⧸ Subgroup.center K) hs hch with h | h
  · exact Or.inl (isChevOfChar_of_mulEquiv (innerAut_equiv K) h)
  · exact Or.inr (h196CatalogIs_of_mulEquiv (innerAut_equiv K) h)

theorem GLAPPrimeCoreOf_eq_map {G : Type} [Group G] (p : ℕ) (X : Subgroup G) :
    GLAPPrimeCoreOf p X = (GLAPPrimeCore p ↥X).map X.subtype := rfl

theorem GLAPPrimeCoreOf_le {G : Type} [Group G] (p : ℕ) (X : Subgroup G) :
    GLAPPrimeCoreOf p X ≤ X := by
  rw [GLAPPrimeCoreOf_eq_map]
  exact Subgroup.map_subtype_le _

theorem GLAPPrimeCoreOf_conj {G : Type} [Group G] (p : ℕ) (X : Subgroup G) {c w : G}
    (hc : c ∈ X) (hw : w ∈ GLAPPrimeCoreOf p X) : c * w * c⁻¹ ∈ GLAPPrimeCoreOf p X := by
  rw [GLAPPrimeCoreOf_eq_map] at hw ⊢
  obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.1 hw
  exact Subgroup.mem_map.2 ⟨(⟨c, hc⟩ : ↥X) * n * (⟨c, hc⟩ : ↥X)⁻¹,
    (GLAPPrimeCore.normal p ↥X).conj_mem n hn _, rfl⟩

theorem not_dvd_card_GLAPPrimeCoreOf {G : Type} [Group G] [Finite G] (p : ℕ) [hp : Fact p.Prime]
    (X : Subgroup G) : ¬ p ∣ Nat.card ↥(GLAPPrimeCoreOf p X) := by
  rw [GLAPPrimeCoreOf_eq_map]
  have hinj : Function.Injective X.subtype := Subtype.val_injective
  have hcard : Nat.card ↥((GLAPPrimeCore p ↥X).map X.subtype) = Nat.card ↥(GLAPPrimeCore p ↥X) :=
    Subgroup.card_map_of_injective hinj
  rw [hcard]
  have hcop : Nat.Coprime p (Nat.card ↥(GLAPPrimeCore p ↥X)) := CFSG.pPrimeCore_coprime_card
  exact (Nat.Prime.coprime_iff_not_dvd hp.out).1 hcop

theorem le_GLAPPrimeCoreOf {G : Type} [Group G] [Finite G] (p : ℕ) [hp : Fact p.Prime]
    {X V : Subgroup G} (hVX : V ≤ X) (hV : ∀ c ∈ X, ∀ v ∈ V, c * v * c⁻¹ ∈ V)
    (hVp : ¬ p ∣ Nat.card ↥V) : V ≤ GLAPPrimeCoreOf p X := by
  rw [GLAPPrimeCoreOf_eq_map]
  set V' : Subgroup ↥X := V.subgroupOf X with hV'
  have hV'n : V'.Normal := by
    constructor
    intro n hn g
    rw [hV', Subgroup.mem_subgroupOf] at hn ⊢
    exact hV g.1 g.2 _ hn
  have hcard : Nat.card ↥V' = Nat.card ↥V :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVX).toEquiv
  have hcop : Nat.Coprime p (Nat.card ↥V') := by
    rw [hcard]
    exact (Nat.Prime.coprime_iff_not_dvd hp.out).2 hVp
  have hle : V' ≤ CFSG.pPrimeCore p ↥X := le_sSup ⟨hV'n, hcop⟩
  intro v hv
  exact Subgroup.mem_map.2 ⟨⟨v, hVX hv⟩, hle (Subgroup.mem_subgroupOf.2 hv), rfl⟩

theorem isPGroup_zpowers {G : Type} [Group G] (p : ℕ) {x : G} (hx : x ^ p = 1) :
    IsPGroup p ↥(Subgroup.zpowers x) := by
  intro g
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 g.2
  refine ⟨1, Subtype.ext ?_⟩
  have hxk : (x ^ k) ^ p = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]
  simp only [pow_one, Subgroup.coe_pow]
  rw [← hk]
  exact hxk

theorem finite_mulAut (K : Type) [Group K] [Finite K] : Finite (MulAut K) :=
  Finite.of_injective (fun φ : MulAut K => (φ : K ≃ K))
    (fun φ ψ h => MulEquiv.ext (fun x => congrArg (fun e : K ≃ K => e x) h))

end CFSG.LocalAnalysis.GLTheoremA
