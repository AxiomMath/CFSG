module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CSevenOneKSField
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K7145Comp
public import CFSG.ThirdParty.BrauerInduction.Background.Group.PDecomposition
public import CFSG.LieType.OutStructure
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open Subgroup
open CFSG.ComponentClassification
open CFSG.ComponentClassification.OuterAutomorphisms
open S15.K7145Proof (outerAction)

variable {X : Type*} [Group X]

@[expose] noncomputable def centerQuotientAction (L : Subgroup X) [L.Normal] :
    X →* MulAut (↥L ⧸ Subgroup.center ↥L) :=
  (PerfectAutomorphisms.centerQuotientHom ↥L).comp (MulAut.conjNormal (H := L))

theorem centerQuotientAction_apply (L : Subgroup X) [L.Normal] (x : X) :
    centerQuotientAction L x =
      PerfectAutomorphisms.centerQuotientHom ↥L (MulAut.conjNormal (H := L) x) := rfl

theorem outerAction_apply (L : Subgroup X) [L.Normal] (x : X) :
    outerAction L x =
      QuotientGroup.mk' (inner (↥L ⧸ Subgroup.center ↥L)) (centerQuotientAction L x) := rfl

theorem conjNormal_eq_conj_mem {L : Subgroup X} [L.Normal] {x : X} (hx : x ∈ L) :
    MulAut.conjNormal (H := L) x = MulAut.conj (⟨x, hx⟩ : ↥L) :=
  MulAut.conjNormal_val (h := ⟨x, hx⟩)

theorem conjNormal_eq_one_iff {L : Subgroup X} [L.Normal] {x : X} :
    MulAut.conjNormal (H := L) x = 1 ↔ x ∈ Subgroup.centralizer (L : Set X) := by
  constructor
  · intro h
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 : ((MulAut.conjNormal (H := L) x) ⟨y, hy⟩) = (1 : MulAut ↥L) ⟨y, hy⟩ := by rw [h]
    have h2 : x * (y : X) * x⁻¹ = (y : X) := by
      simpa only [MulAut.conjNormal_apply, MulAut.one_apply] using
        congrArg (fun z : ↥L => (z : X)) h1
    calc y * x = (x * y * x⁻¹) * x := by rw [h2]
      _ = x * y := by group
  · intro h
    ext y
    simp only [MulAut.conjNormal_apply, MulAut.one_apply, Subgroup.coe_mk, Subgroup.coe_one]
    have hcomm : (y : X) * x = x * (y : X) := Subgroup.mem_centralizer_iff.mp h (y : X) y.2
    rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]

theorem centerQuotientAction_ker (L : Subgroup X) [L.Normal] [Group.IsPerfect ↥L] :
    (centerQuotientAction L).ker = Subgroup.centralizer (L : Set X) := by
  ext x
  rw [MonoidHom.mem_ker, centerQuotientAction_apply]
  have hinj : Function.Injective (PerfectAutomorphisms.centerQuotientHom ↥L) :=
    PerfectAutomorphisms.centerQuotientHom_injective ↥L
  have hiff : PerfectAutomorphisms.centerQuotientHom ↥L (MulAut.conjNormal (H := L) x) = 1 ↔
      MulAut.conjNormal (H := L) x = 1 := by
    rw [← map_one (PerfectAutomorphisms.centerQuotientHom ↥L), hinj.eq_iff]
  rw [hiff, conjNormal_eq_one_iff]

theorem inner_eq_map_centerQuotientAction (L : Subgroup X) [L.Normal] :
    inner (↥L ⧸ Subgroup.center ↥L) = L.map (centerQuotientAction L) := by
  ext a
  constructor
  · rintro ⟨k, rfl⟩
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥L) k
    refine Subgroup.mem_map.mpr ⟨l, l.2, ?_⟩
    rw [centerQuotientAction_apply, conjNormal_eq_conj_mem l.2, centerQuotient_conj]
  · rintro ⟨l, hl, rfl⟩
    rw [centerQuotientAction_apply, conjNormal_eq_conj_mem hl, centerQuotient_conj]
    exact ⟨_, rfl⟩

theorem outerAction_ker_eq_sup_centralizer (L : Subgroup X) [L.Normal] [Group.IsPerfect ↥L] :
    (outerAction L).ker = L ⊔ Subgroup.centralizer (L : Set X) := by
  refine le_antisymm (fun x hx => S15.K7145Proof.mem_sup_centralizer_of_outerAction_eq_one L hx)
    ?_
  intro x hx
  rw [Subgroup.mem_sup_of_normal_right] at hx
  obtain ⟨l, hl, c, hc, rfl⟩ := hx
  have hc1 : outerAction L c = 1 := by
    have hconj : MulAut.conjNormal (H := L) c = 1 := conjNormal_eq_one_iff.mpr hc
    rw [outerAction_apply, centerQuotientAction_apply, hconj, map_one, map_one]
  have hl1 : outerAction L l = 1 := by
    rw [outerAction_apply, centerQuotientAction_apply, conjNormal_eq_conj_mem hl,
      centerQuotient_conj]
    exact (QuotientGroup.eq_one_iff _).mpr ⟨_, rfl⟩
  rw [MonoidHom.mem_ker, map_mul, hl1, hc1, one_mul]

theorem exists_preimage_pow_mem_centralizer {L : Subgroup X} [L.Normal] [Group.IsPerfect ↥L]
    {p k : ℕ} {y : Outer (↥L ⧸ Subgroup.center ↥L)} (hy : y ∈ (outerAction L).range)
    (hyk : y ^ (p ^ k) = 1)
    (hf : ∃ f : MulAut (↥L ⧸ Subgroup.center ↥L),
      QuotientGroup.mk' (inner (↥L ⧸ Subgroup.center ↥L)) f = y ∧ f ^ (p ^ k) = 1) :
    ∃ g : X, outerAction L g = y ∧ g ^ (p ^ k) ∈ Subgroup.centralizer (L : Set X) := by
  obtain ⟨f, hfy, hfk⟩ := hf
  obtain ⟨g₀, hg₀⟩ := MonoidHom.mem_range.mp hy
  have hmem : centerQuotientAction L g₀ * f⁻¹ ∈ inner (↥L ⧸ Subgroup.center ↥L) := by
    rw [← QuotientGroup.eq_one_iff]
    change QuotientGroup.mk' (inner (↥L ⧸ Subgroup.center ↥L))
      (centerQuotientAction L g₀ * f⁻¹) = 1
    rw [map_mul, map_inv, ← outerAction_apply, hg₀, hfy, mul_inv_cancel]
  rw [inner_eq_map_centerQuotientAction L] at hmem
  obtain ⟨l, hl, hlρ⟩ := Subgroup.mem_map.mp hmem
  have hρ : centerQuotientAction L (l⁻¹ * g₀) = f := by
    rw [map_mul, map_inv, hlρ]
    group
  refine ⟨l⁻¹ * g₀, ?_, ?_⟩
  · rw [outerAction_apply, hρ, hfy]
  · rw [← centerQuotientAction_ker L, MonoidHom.mem_ker, map_pow, hρ, hfk]

theorem isPSingular_pow {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] {a : G}
    (h : CFSG.IsPSingular p a) (n : ℕ) : CFSG.IsPSingular p (a ^ n) := by
  obtain ⟨s, hs⟩ := h
  have hdvd : orderOf (a ^ n) ∣ p ^ s := by
    rw [← hs]
    exact orderOf_pow_dvd n
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Fact.out).mp hdvd
  exact ⟨j, hj⟩

theorem pSingular_mem_zpowers {G : Type*} [Group G] (p : ℕ) (a : G) :
    Group.pSingular p a ∈ Subgroup.zpowers a := by
  unfold Group.pSingular
  exact Subgroup.zpow_mem_zpowers a _

theorem isPSingular_mem_zpowers_pSingular {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {q x : G} (hxq : x ∈ Subgroup.zpowers q) (hxs : CFSG.IsPSingular p x) :
    x ∈ Subgroup.zpowers (Group.pSingular p q) := by
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hxq)
  have hcomm : Commute (Group.pSingular p q) (Group.pRegular p q) :=
    Group.pDecomp_commute (p := p) (a := q)
  have hzr : Group.pRegular p q * Group.pSingular p q = q :=
    Group.pDecomp' (p := p) (a := q) (isOfFinOrder_of_finite q)
  have h1 : Group.pSingular p q ^ n * (Group.pRegular p q) ^ n = q ^ n := by
    rw [← hcomm.mul_pow,
      show Group.pSingular p q * Group.pRegular p q = q from hcomm.eq.trans hzr]
  have h2 : (Group.pRegular p q) ^ n * Group.pSingular p q ^ n = q ^ n :=
    (hcomm.pow_pow n n).symm.eq.trans h1
  have hys : CFSG.IsPSingular p (Group.pSingular p q) :=
    Group.isPSingular_pSingular (p := p) (a := q)
  have hr : CFSG.IsPRegular p (Group.pRegular p q) :=
    Group.isPRegular_pRegular (p := p) (a := q) (isOfFinOrder_of_finite q)
  have huniq := Group.pSingular_pRegular_unique (p := p) (a := q ^ n)
    (isOfFinOrder_of_finite (q ^ n)) h1 h2 (isPSingular_pow (p := p) hys n)
    (IsPRegular.pow (p := p) (a := Group.pRegular p q) hr n)
  have hEq : q ^ n = Group.pSingular p q ^ n := by
    rw [huniq.1,
      Group.pSingular_eq_self_of_isPSingular (p := p) (a := q ^ n)
        (isOfFinOrder_of_finite (q ^ n)) hxs]
  rw [hEq]
  simpa using Subgroup.zpow_mem_zpowers (Group.pSingular p q) (n : ℤ)

theorem exists_isSplitCover_of_pGenerator [Finite X] {p k : ℕ} [Fact p.Prime]
    {L : Subgroup X} [L.Normal]
    (hL : CFSG.IsComponent L) (hrk : CFSG.Open.pRank p L = 1)
    {y : Outer (↥L ⧸ Subgroup.center ↥L)} {g : X} (hyord : orderOf y = p ^ k)
    (hgψ : outerAction L g = y)
    (hgC : g ^ (p ^ k) ∈ Subgroup.centralizer (L : Set X))
    (hcov : ∀ x : X, (∃ s : ℕ, orderOf x = p ^ s) →
      outerAction L x ∈ Subgroup.zpowers y) :
    ∃ W : Subgroup X, Subgroup.centralizer (L : Set X) ≤ W ∧
      W ⊓ L ≤ Subgroup.centralizer (L : Set X) ∧
      oPPrimeHull p (⊤ : Subgroup X) ≤ L ⊔ W ∧
      (∃ g ∈ W, (∃ k : ℕ, g ^ (p ^ k) ∈ Subgroup.centralizer (L : Set X)) ∧
        ∀ w ∈ W, ∃ n : ℕ, w * (g ^ n)⁻¹ ∈ Subgroup.centralizer (L : Set X)) ∧
      ∀ w ∈ W, w ^ p ∈ Subgroup.centralizer (L : Set X) →
        ∃ z ∈ L, orderOf z = p ∧ w * z = z * w := by
  haveI : Group.IsPerfect ↥L := hL.1.1
  have hCn : (Subgroup.centralizer (L : Set X)).Normal := inferInstance
  have hLK : L ≤ (outerAction L).ker := by
    rw [outerAction_ker_eq_sup_centralizer L]
    exact le_sup_left
  have hCK : Subgroup.centralizer (L : Set X) ≤ (outerAction L).ker := by
    rw [outerAction_ker_eq_sup_centralizer L]
    exact le_sup_right
  refine ⟨Subgroup.centralizer (L : Set X) ⊔ Subgroup.zpowers g, le_sup_left, ?_, ?_,
    ⟨g, Subgroup.mem_sup_right (Subgroup.mem_zpowers g), ⟨k, hgC⟩, ?_⟩, ?_⟩
  ·
    intro w hw
    obtain ⟨hwW, hwL⟩ := Subgroup.mem_inf.mp hw
    obtain ⟨c, hc, y', hy', hwy'⟩ := Subgroup.mem_sup_of_normal_left.mp hwW
    obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hy')
    have hwL' : c * g ^ n ∈ L := hwy' ▸ hwL
    have hwψ : outerAction L (c * g ^ n) = 1 := MonoidHom.mem_ker.mp (hLK hwL')
    have hcψ : outerAction L c = 1 := MonoidHom.mem_ker.mp (hCK hc)
    have hyn : y ^ n = 1 := by
      rw [map_mul, hcψ, one_mul, map_pow, hgψ] at hwψ
      exact hwψ
    have hdvd : p ^ k ∣ n := by
      rw [← hyord]
      exact orderOf_dvd_iff_pow_eq_one.mpr hyn
    obtain ⟨i, hi⟩ := hdvd
    have hgn : g ^ n ∈ Subgroup.centralizer (L : Set X) := by
      rw [hi, pow_mul]
      exact Subgroup.pow_mem _ hgC i
    rw [← hwy']
    exact Subgroup.mul_mem _ hc hgn
  ·
    rw [oPPrimeHull]
    refine (Subgroup.closure_le (L ⊔ (Subgroup.centralizer (L : Set X) ⊔
      Subgroup.zpowers g))).mpr ?_
    rintro x ⟨-, s, hs⟩
    have hxq : outerAction L x ∈ Subgroup.zpowers y := hcov x ⟨s, hs⟩
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hxq)
    have hker : outerAction L (x * (g ^ n)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_pow, hgψ, ← hn, mul_inv_cancel]
    have h1 : x * (g ^ n)⁻¹ ∈ L ⊔ Subgroup.centralizer (L : Set X) := by
      rw [← outerAction_ker_eq_sup_centralizer L]
      exact MonoidHom.mem_ker.mp hker
    have h2 : L ⊔ Subgroup.centralizer (L : Set X) ≤
        L ⊔ (Subgroup.centralizer (L : Set X) ⊔ Subgroup.zpowers g) :=
      sup_le le_sup_left (le_sup_left.trans le_sup_right)
    have h3 : x = (x * (g ^ n)⁻¹) * g ^ n := by group
    rw [h3]
    refine Subgroup.mul_mem _ (h2 h1) ?_
    exact (le_sup_right : Subgroup.centralizer (L : Set X) ⊔ Subgroup.zpowers g ≤
      L ⊔ (Subgroup.centralizer (L : Set X) ⊔ Subgroup.zpowers g))
      (Subgroup.mem_sup_right (Subgroup.pow_mem _ (Subgroup.mem_zpowers g) n))
  ·
    intro w hw
    obtain ⟨c, hc, y', hy', hwy'⟩ := Subgroup.mem_sup_of_normal_left.mp hw
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hy')
    refine ⟨n, ?_⟩
    rw [← hwy', ← hn, mul_assoc, mul_inv_cancel, mul_one]
    exact hc
  ·
    intro w _ hwC
    have hpL : p ∣ Nat.card L := by
      obtain ⟨E, hEL, -, hcard⟩ := CFSG.SectionRank.exists_pRank (Fact.out : p.Prime).one_lt L
      rw [hrk, pow_one] at hcard
      rw [← hcard]
      exact Subgroup.card_dvd_of_le hEL
    exact SevenOneKS.exists_orderOf_eq_commute_of_pow_mem hpL hwC

theorem exists_splitCover_of_fieldPart [Finite X] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {L : Subgroup X} [L.Normal] (hL : CFSG.IsComponent L)
    (hrk : CFSG.Open.pRank p L = 1)
    (F : Subgroup (MulAut (↥L ⧸ Subgroup.center ↥L)))
    (hFcyc : IsCyclic ↥F)
    (hFbot : F ⊓ inner (↥L ⧸ Subgroup.center ↥L) = ⊥)
    (hFcov : ∀ x : MulAut (↥L ⧸ Subgroup.center ↥L), (∃ k : ℕ, x ^ (p ^ k) = 1) →
      x ∈ inner (↥L ⧸ Subgroup.center ↥L) ⊔ F) :
    ∃ W : Subgroup X, Subgroup.centralizer (L : Set X) ≤ W ∧
      W ⊓ L ≤ Subgroup.centralizer (L : Set X) ∧
      oPPrimeHull p (⊤ : Subgroup X) ≤ L ⊔ W ∧
      (∃ g ∈ W, (∃ k : ℕ, g ^ (p ^ k) ∈ Subgroup.centralizer (L : Set X)) ∧
        ∀ w ∈ W, ∃ n : ℕ, w * (g ^ n)⁻¹ ∈ Subgroup.centralizer (L : Set X)) ∧
      ∀ w ∈ W, w ^ p ∈ Subgroup.centralizer (L : Set X) →
        ∃ z ∈ L, orderOf z = p ∧ w * z = z * w := by
  haveI : Group.IsPerfect ↥L := hL.1.1
  haveI : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hL.1.2.1
  classical
  let π : MulAut (↥L ⧸ Subgroup.center ↥L) →* Outer (↥L ⧸ Subgroup.center ↥L) :=
    QuotientGroup.mk' (inner (↥L ⧸ Subgroup.center ↥L))
  let E : Subgroup (MulAut (↥L ⧸ Subgroup.center ↥L)) :=
    inner (↥L ⧸ Subgroup.center ↥L) ⊔ F
  let E' : Subgroup (Outer (↥L ⧸ Subgroup.center ↥L)) := E.map π
  have hE'eq : E' = F.map π := by
    dsimp only [E', E]
    rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
  have hE'cyc : IsCyclic ↥E' := by
    rw [hE'eq]
    exact isCyclic_of_surjective (π.subgroupMap F) (π.subgroupMap_surjective F)
  have hcover : ∀ x ∈ (outerAction L).range, (∃ s : ℕ, orderOf x = p ^ s) → x ∈ E' := by
    intro x hx hxsing
    obtain ⟨g₀, hg₀⟩ := MonoidHom.mem_range.mp hx
    set z := Group.pSingular p (centerQuotientAction L g₀) with hz
    set r := Group.pRegular p (centerQuotientAction L g₀) with hr
    have hzps : CFSG.IsPSingular p z := Group.isPSingular_pSingular (p := p)
      (a := centerQuotientAction L g₀)
    have hrpr : CFSG.IsPRegular p r :=
      Group.isPRegular_pRegular (p := p) (a := centerQuotientAction L g₀)
        (isOfFinOrder_of_finite _)
    have hzr : r * z = centerQuotientAction L g₀ :=
      Group.pDecomp' (p := p) (a := centerQuotientAction L g₀) (isOfFinOrder_of_finite _)
    have hπz : π z ∈ E' := by
      have hmem : z ∈ E := by
        apply hFcov
        obtain ⟨s, hs⟩ := hzps
        exact ⟨s, by rw [← hs, pow_orderOf_eq_one]⟩
      exact Subgroup.mem_map_of_mem π hmem
    have hx1 : π r * π z = x := by
      rw [← map_mul, hzr, ← outerAction_apply, hg₀]
    have hx2 : π z * π r = x :=
      ((Group.pDecomp_commute (p := p) (a := centerQuotientAction L g₀)).map π).eq.trans hx1
    have huniq := Group.pSingular_pRegular_unique (p := p) (a := x)
      (isOfFinOrder_of_finite x) hx2 hx1
      (CFSG.IsPSingular.map (p := p) (f := π) hzps)
      (CFSG.IsPRegular.map (p := p) (f := π) hrpr)
    have hxsing' : CFSG.IsPSingular p x := ⟨hxsing.choose, hxsing.choose_spec⟩
    have hone : π r = 1 := by
      rw [huniq.2, Group.isPSingular_pRegular_eq_one (p := p) (a := x)
        (isOfFinOrder_of_finite x) hxsing']
    rw [← hx2, hone, mul_one]
    exact hπz
  have hQcyc : IsCyclic ↥(E' ⊓ (outerAction L).range) := Subgroup.isCyclic_of_le inf_le_left
  obtain ⟨q, hq⟩ :=
    (Subgroup.isCyclic_iff_exists_zpowers_eq_top (E' ⊓ (outerAction L).range)).mp hQcyc
  set y : Outer (↥L ⧸ Subgroup.center ↥L) := Group.pSingular p q with hy
  have hyps : CFSG.IsPSingular p y := Group.isPSingular_pSingular (p := p) (a := q)
  obtain ⟨k, hk⟩ := hyps
  have hyQ : y ∈ E' ⊓ (outerAction L).range := by
    rw [← hq, hy]
    exact pSingular_mem_zpowers p q
  have hyk : y ^ (p ^ k) = 1 := by rw [← hk, pow_orderOf_eq_one]
  obtain ⟨f, hfF, hfπ⟩ := Subgroup.mem_map.mp (hE'eq ▸ hyQ.1)
  have hfk : f ^ (p ^ k) = 1 := by
    have h1 : f ^ (p ^ k) ∈ F := Subgroup.pow_mem F hfF _
    have h2 : f ^ (p ^ k) ∈ OuterAutomorphisms.inner (↥L ⧸ Subgroup.center ↥L) := by
      have hmemker : f ^ (p ^ k) ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_pow, hfπ, hyk]
      rwa [show π.ker = OuterAutomorphisms.inner (↥L ⧸ Subgroup.center ↥L) from
        QuotientGroup.ker_mk' _] at hmemker
    have hmem : f ^ (p ^ k) ∈ F ⊓ OuterAutomorphisms.inner (↥L ⧸ Subgroup.center ↥L) :=
      ⟨h1, h2⟩
    rw [hFbot] at hmem
    exact Subgroup.mem_bot.mp hmem
  obtain ⟨g, hgψ, hgC⟩ := exists_preimage_pow_mem_centralizer (L := L) (p := p) (k := k) hyQ.2
    hyk ⟨f, hfπ, hfk⟩
  refine exists_isSplitCover_of_pGenerator hL hrk hk hgψ hgC ?_
  intro x hx
  obtain ⟨s, hs⟩ := hx
  have hxH : outerAction L x ∈ (outerAction L).range := ⟨x, rfl⟩
  have hxord : ∃ t : ℕ, orderOf (outerAction L x) = p ^ t := by
    have hd : orderOf (outerAction L x) ∣ p ^ s := by
      rw [← hs]
      exact orderOf_map_dvd (outerAction L) x
    obtain ⟨t, -, ht⟩ := (Nat.dvd_prime_pow Fact.out).mp hd
    exact ⟨t, ht⟩
  have hxE' : outerAction L x ∈ E' := hcover _ ⟨x, rfl⟩ hxord
  have hxq : outerAction L x ∈ Subgroup.zpowers q := by
    rw [hq]
    exact ⟨hxE', hxH⟩
  exact isPSingular_mem_zpowers_pSingular (q := q) hxq
    (CFSG.IsPSingular.map (p := p) (f := outerAction L) (a := x) ⟨s, hs⟩)

theorem exists_isSplitCover_of_not_dvd_outer [Finite X] {p : ℕ} [Fact p.Prime]
    {L : Subgroup X} [L.Normal] (hL : CFSG.IsComponent L) (hrk : CFSG.Open.pRank p L = 1)
    (hout : ¬ p ∣ Nat.card (Outer (↥L ⧸ Subgroup.center ↥L))) :
    ∃ W : Subgroup X, Subgroup.centralizer (L : Set X) ≤ W ∧
      W ⊓ L ≤ Subgroup.centralizer (L : Set X) ∧
      oPPrimeHull p (⊤ : Subgroup X) ≤ L ⊔ W ∧
      (∃ g ∈ W, (∃ k : ℕ, g ^ (p ^ k) ∈ Subgroup.centralizer (L : Set X)) ∧
        ∀ w ∈ W, ∃ n : ℕ, w * (g ^ n)⁻¹ ∈ Subgroup.centralizer (L : Set X)) ∧
      ∀ w ∈ W, w ^ p ∈ Subgroup.centralizer (L : Set X) →
        ∃ z ∈ L, orderOf z = p ∧ w * z = z * w := by
  haveI : Group.IsPerfect ↥L := hL.1.1
  refine ⟨Subgroup.centralizer (L : Set X), le_rfl, inf_le_left, ?_, ?_, ?_⟩
  ·
    rw [oPPrimeHull]
    refine (Subgroup.closure_le (L ⊔ Subgroup.centralizer (L : Set X))).mpr ?_
    intro x hx
    obtain ⟨-, s, hs⟩ := hx
    have hHp : ¬ p ∣ Nat.card ↥((outerAction L).range) := fun hd =>
      hout (hd.trans (Subgroup.card_subgroup_dvd_card (outerAction L).range))
    have hdvd1 : orderOf (outerAction L x) ∣ p ^ s := by
      rw [← hs]
      exact orderOf_map_dvd (outerAction L) x
    have hdvd2 : orderOf (outerAction L x) ∣ Nat.card ↥((outerAction L).range) :=
      Subgroup.orderOf_dvd_natCard (outerAction L).range ⟨x, rfl⟩
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Fact.out).mp hdvd1
    have hj0 : j = 0 := by
      by_contra hjne
      exact hHp ((dvd_pow_self p hjne).trans (hj ▸ hdvd2))
    have hone : orderOf (outerAction L x) = 1 := by rw [hj, hj0, pow_zero]
    rw [← outerAction_ker_eq_sup_centralizer L]
    exact MonoidHom.mem_ker.mpr (orderOf_eq_one_iff.mp hone)
  ·
    refine ⟨1, Subgroup.one_mem _, ⟨0, ?_⟩, ?_⟩
    · simpa using Subgroup.one_mem (Subgroup.centralizer (L : Set X))
    · intro w hw
      exact ⟨0, by simpa using hw⟩
  ·
    intro w _ hwC
    have hpL : p ∣ Nat.card L := by
      obtain ⟨E, hEL, -, hcard⟩ := CFSG.SectionRank.exists_pRank (Fact.out : p.Prime).one_lt L
      rw [hrk, pow_one] at hcard
      rw [← hcard]
      exact Subgroup.card_dvd_of_le hEL
    exact SevenOneKS.exists_orderOf_eq_commute_of_pow_mem hpL hwC

theorem exists_splitCover_of_cyclicOuter [Finite X] {p : ℕ} [Fact p.Prime]
    {L : Subgroup X} [L.Normal] (hL : CFSG.IsComponent L) (hrk : CFSG.Open.pRank p L = 1)
    (hcyc : IsCyclic (Outer (↥L ⧸ Subgroup.center ↥L)))
    (hlift : ∀ y : Outer (↥L ⧸ Subgroup.center ↥L), (∃ k : ℕ, orderOf y = p ^ k) →
      ∃ f : MulAut (↥L ⧸ Subgroup.center ↥L),
        QuotientGroup.mk' (inner (↥L ⧸ Subgroup.center ↥L)) f = y ∧ orderOf f = orderOf y) :
    ∃ W : Subgroup X, Subgroup.centralizer (L : Set X) ≤ W ∧
      W ⊓ L ≤ Subgroup.centralizer (L : Set X) ∧
      oPPrimeHull p (⊤ : Subgroup X) ≤ L ⊔ W ∧
      (∃ g ∈ W, (∃ k : ℕ, g ^ (p ^ k) ∈ Subgroup.centralizer (L : Set X)) ∧
        ∀ w ∈ W, ∃ n : ℕ, w * (g ^ n)⁻¹ ∈ Subgroup.centralizer (L : Set X)) ∧
      ∀ w ∈ W, w ^ p ∈ Subgroup.centralizer (L : Set X) →
        ∃ z ∈ L, orderOf z = p ∧ w * z = z * w := by
  haveI : Group.IsPerfect ↥L := hL.1.1
  haveI : IsCyclic (Outer (↥L ⧸ Subgroup.center ↥L)) := hcyc
  haveI hHcyc : IsCyclic ↥((outerAction L).range) := Subgroup.isCyclic_of_le le_top
  obtain ⟨q, hq⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top (outerAction L).range).mp hHcyc
  set y : Outer (↥L ⧸ Subgroup.center ↥L) := Group.pSingular p q with hy
  have hyps : CFSG.IsPSingular p y := Group.isPSingular_pSingular (p := p) (a := q)
  obtain ⟨k, hk⟩ := hyps
  have hyH : y ∈ (outerAction L).range := by
    rw [← hq, hy]
    exact pSingular_mem_zpowers p q
  obtain ⟨f, hfπ, hford⟩ := hlift y ⟨k, hk⟩
  have hfk : f ^ (p ^ k) = 1 := by
    rw [← hk, ← hford, pow_orderOf_eq_one]
  obtain ⟨g, hgψ, hgC⟩ := exists_preimage_pow_mem_centralizer (L := L) (p := p) (k := k) hyH
    (by rw [← hk, pow_orderOf_eq_one]) ⟨f, hfπ, hfk⟩
  refine exists_isSplitCover_of_pGenerator hL hrk hk hgψ hgC ?_
  intro x hx
  obtain ⟨s, hs⟩ := hx
  exact isPSingular_mem_zpowers_pSingular (q := q) (by rw [hq]; exact ⟨x, rfl⟩)
    (CFSG.IsPSingular.map (p := p) (f := outerAction L) (a := x) ⟨s, hs⟩)

theorem sevenOneFourSplit_of_I_7_13_2_5
    (h : CFSG.LieType.OutStructure.I_7_13_2_5) :
    SevenOneFourSplit := by
  intro X _ _ hK p hp hp2 L hL hLn hrk
  haveI := hLn
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Group.IsPerfect ↥L := hL.1.1
  haveI : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hL.1.2.1
  have hq : CFSG.Open.IsQuasisimple ↥L := ⟨Group.isPerfect_def.mp hL.1.1, hL.1.2.1⟩
  have hnab := S15.K7145Proof.quotient_center_nonabelian hq
  have hcat := S15.K7145Proof.isCatalogGroup_quotient_center hK L hq
  have hrank := S15.K7145Proof.pRank_quotient_center_le_one hp hp2 L hrk.le
  rcases h (↥L ⧸ Subgroup.center ↥L) inferInstance hnab hcat p hp hp2 hrank with
    hout | ⟨F, _hEnorm, hFcyc, hFbot, _hEindex, hFcov⟩ | ⟨hp3, hcyc, hlift⟩
  · exact exists_isSplitCover_of_not_dvd_outer hL hrk hout
  · exact exists_splitCover_of_fieldPart hp2 hL hrk F hFcyc hFbot hFcov
  ·
    by_cases hpout : p ∣ Nat.card (Outer (↥L ⧸ Subgroup.center ↥L))
    · exact exists_splitCover_of_cyclicOuter hL hrk hcyc hlift
    · exact exists_isSplitCover_of_not_dvd_outer hL hrk hpout

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
