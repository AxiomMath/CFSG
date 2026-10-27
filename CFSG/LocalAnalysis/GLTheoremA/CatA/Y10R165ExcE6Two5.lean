module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE6Two3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcEngine3
public import CFSG.GroupTheory.ElemAbelianRank
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalIsogeny

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE6Two

open Subgroup
open CFSG.Open
open CFSG.SeitzReduction.E6Pilot
open CFSG.LieType.Chevalley
open CFSG.Blueprint.Chevalley
open CFSG.SeitzReduction
open CFSG.LieType.SeitzGeneration
open CFSG.LieType.Steinberg.Minuscule
open CFSG.LieType.Steinberg.Isogeny
open CFSG.RankThree.PartTwo.Census.Exceptional
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


@[expose] def E6TwoLayerData : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (p : ℕ), p.Prime → 3 ≤ p →
    p ∣ Nat.card K + 1 →
    ∃ R3 : Subgroup (adjointGroup .E6 K),
      R3 ≤ a5Levi K ∧ IsElemAbelian p R3 ∧ Nat.card R3 = p ^ 3 ∧
      ∃ z : adjointGroup .E6 K, z ∈ R3 ∧ z ≠ 1 ∧
      ∃ Q : Subgroup (adjointGroup .E6 K),
        Q ≤ a5Levi K ⊓ Subgroup.centralizer ({z} : Set (adjointGroup .E6 K)) ∧
        CFSG.Open.IsQuasisimple ↥Q ∧ p ∣ Nat.card Q ∧
        (Q.subgroupOf (a5Levi K ⊓
          Subgroup.centralizer ({z} : Set (adjointGroup .E6 K)))).Normal

@[expose] def E6TwoFData : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (q : ℕ), q.Prime → q ≠ 2 →
    (q ∣ Nat.card F - 1 ∨ Nat.card F = 2 ∧ q = 3) →
    ∃ F0 : Subgroup ↥(e6Data_valid.minGroup F),
      IsElemAbelian q F0 ∧ Nat.card F0 = q ^ 3 ∧
      F0 ⊓ Subgroup.center ↥(e6Data_valid.minGroup F) = ⊥ ∧
      (∀ x ∈ e6Data_valid.rootGroup F (highRoot .E6) ⊔
          e6Data_valid.rootGroup F (-highRoot .E6),
        F0 ≤ Subgroup.centralizer ({x} : Set ↥(e6Data_valid.minGroup F))) ∧
      F0.map (e6Isogeny F) ≤ Subgroup.normalizer (a5Levi F : Set (adjointGroup .E6 F))

private theorem not_dvd_card_center_e6_two {F : Type} [Field F] [Finite F] [CharP F 2]
    {n p : ℕ} (hcard : Nat.card F = 2 ^ n) (hp : p.Prime)
    (hrk : rk2Ord p n = 2) :
    ¬ p ∣ Nat.card (Subgroup.center ↥(e6Data_valid.minGroup F)) := by
  have hZ : Nat.card (Subgroup.center ↥(e6Data_valid.minGroup F)) =
      Nat.gcd 3 (Nat.card F - 1) :=
    (CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.card_center_e6 F).1
  rw [hZ, hcard]
  by_cases h3 : p = 3
  · subst h3
    have hdiv : 3 ∣ 2 ^ n + 1 :=
      (rk2Ord_eq_two_iff (by norm_num) (by norm_num)).mp hrk
    intro h
    have h1 : 3 ∣ 2 ^ n - 1 := h.trans (Nat.gcd_dvd_right 3 (2 ^ n - 1))
    have h2 : 3 ∣ (2 ^ n + 1) - (2 ^ n - 1) := Nat.dvd_sub hdiv h1
    have h3' : (2 ^ n + 1) - (2 ^ n - 1) = 2 := by
      have := Nat.one_le_two_pow (n := n)
      omega
    rw [h3'] at h2
    norm_num at h2
  · intro h
    have h1 : p ∣ 3 := h.trans (Nat.gcd_dvd_left 3 (2 ^ n - 1))
    exact h3 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h1)

private theorem adjoint_rootGroup_eq_subgroupOf_e6 {K : Type} [Field K] [Finite K]
    {γ : Fin (Tag.rank .E6) → ℤ} (hγ : IsRoot .E6 γ) :
    CFSG.LieType.Steinberg.Adjoint.rootGroup (rootOperatorFamily .E6) K γ =
      (rootSubgroup .E6 K γ).subgroupOf (adjointGroup .E6 K) := by
  have hmap := CFSG.SeitzReduction.E6Pilot.map_subtype_rootGroup_E6 (K := K) hγ
  change (CFSG.LieType.Steinberg.Adjoint.rootGroup (rootOperatorFamily .E6) K γ).map
      (adjointGroup .E6 K).subtype = rootSubgroup .E6 K γ at hmap
  ext g
  constructor
  · intro hg
    rw [Subgroup.mem_subgroupOf]
    have hmem : (g : ModGL .E6 K) ∈
        (CFSG.LieType.Steinberg.Adjoint.rootGroup (rootOperatorFamily .E6) K γ).map
          (adjointGroup .E6 K).subtype := ⟨g, hg, rfl⟩
    rwa [hmap] at hmem
  · intro hg
    rw [Subgroup.mem_subgroupOf] at hg
    have hmem : (g : ModGL .E6 K) ∈
        (CFSG.LieType.Steinberg.Adjoint.rootGroup (rootOperatorFamily .E6) K γ).map
          (adjointGroup .E6 K).subtype := by
      rw [hmap]
      exact hg
    obtain ⟨y, hy, hyg⟩ := Subgroup.mem_map.mp hmem
    have hygg : y = g := Subtype.ext hyg
    simpa [hygg] using hy

private theorem map_rootRankOne_highRoot {F : Type} [Field F] [Finite F] [CharP F 2] :
    (e6Data_valid.rootGroup F (highRoot .E6) ⊔
        e6Data_valid.rootGroup F (-highRoot .E6)).map (e6Isogeny F) =
      (EPilot.highRootSL2 .E6 F).subgroupOf (adjointGroup .E6 F) := by
  rw [Subgroup.map_sup,
    CFSG.ClassicalInvolution.ModelFacts.map_e6Isogeny_rootGroup (k := F)
      (isRoot_highRoot .E6),
    CFSG.ClassicalInvolution.ModelFacts.map_e6Isogeny_rootGroup (k := F)
      (IsRoot.neg (isRoot_highRoot .E6)),
    EPilot.highRootSL2,
    Subgroup.subgroupOf_sup
      (rootSubgroup_le_adjointGroup (highRoot .E6))
      (rootSubgroup_le_adjointGroup (-highRoot .E6))]
  rw [← adjoint_rootGroup_eq_subgroupOf_e6 (isRoot_highRoot .E6),
    ← adjoint_rootGroup_eq_subgroupOf_e6 (IsRoot.neg (isRoot_highRoot .E6))]

private lemma e6Two_setup_data (F : Type) [Field F] [Finite F] [CharP F 2]
    [Finite ↥(e6Data_valid.minGroup F)] (n p : ℕ) (hcard : Nat.card F = 2 ^ n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hrk : rk2Ord p n = 2)
    (hE : E6TwoLayerData) :
    ∃ (R3 : Subgroup (adjointGroup .E6 F)) (z x0 : adjointGroup .E6 F)
      (Q : Subgroup (adjointGroup .E6 F)) (X : Subgroup (adjointGroup .E6 F)),
      R3 ≤ a5Levi F ∧ IsElemAbelian p R3 ∧ Nat.card R3 = p ^ 3 ∧ z ∈ R3 ∧ z ≠ 1 ∧
      Q ≤ a5Levi F ⊓ Subgroup.centralizer ({z} : Set (adjointGroup .E6 F)) ∧
      CFSG.Open.IsQuasisimple ↥Q ∧ p ∣ Nat.card Q ∧
      (Q.subgroupOf (a5Levi F ⊓
        Subgroup.centralizer ({z} : Set (adjointGroup .E6 F)))).Normal ∧
      X ≤ (EPilot.highRootSL2 .E6 F).subgroupOf (adjointGroup .E6 F) ∧ IsCyclic X ∧
      Nat.card X = Nat.card F + 1 ∧ x0 ∈ X ∧ orderOf x0 = p ∧ x0 ≠ 1 ∧
      Subgroup.centralizer ({x0} : Set (adjointGroup .E6 F)) = X ⊔ a5Levi F ∧
      Disjoint X (a5Levi F) := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hpq : p ∣ Nat.card F + 1 := by
    rw [hcard]
    exact (rk2Ord_eq_two_iff hp hp2).mp hrk
  haveI : Finite (adjointGroup .E6 F) := Subtype.finite
  obtain ⟨R3, hR3J, hR3el, hR3card, z, hzR, hz1, Q, hQle, hQq, hpQ, hQn⟩ :=
    hE F p hp hp3 hpq
  obtain ⟨X, hXJ, hXcyc, hXcard⟩ :=
    exists_nonsplit_le_subgroupOf_highRootSL2 (τ := .E6) (K := F)
  have hpX : p ∣ Nat.card ↥X := by
    rw [hXcard]
    exact hpq
  obtain ⟨xX, hxXord⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) p hpX
  let x0 : adjointGroup .E6 F := xX
  have hx0X : x0 ∈ X := xX.2
  have hx0 : orderOf x0 = p := (Subgroup.orderOf_coe xX).trans hxXord
  have hx0ne : x0 ≠ 1 := by
    intro h
    rw [h] at hx0
    rw [orderOf_one] at hx0
    exact hp.ne_one hx0.symm
  obtain ⟨hcentXJ, hdisjXJ, _hXC⟩ :=
    centralizer_subgroupOf_nonsplit_E6_of_orderOf (K := F) (p := p) hp3 hpq hXJ hXcyc
      hXcard hx0X hx0
  exact ⟨R3, z, x0, Q, X, hR3J, hR3el, hR3card, hzR, hz1, hQle, hQq, hpQ, hQn,
    hXJ, hXcyc, hXcard, hx0X, hx0, hx0ne, hcentXJ, hdisjXJ⟩

private lemma e6Two_rank_data (F : Type) [Field F] [Finite F] [CharP F 2]
    [Finite ↥(e6Data_valid.minGroup F)] (n p : ℕ) (hcard : Nat.card F = 2 ^ n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hrk : rk2Ord p n = 2)
    (hbound : ∀ E : Subgroup (adjointGroup .E6 F), IsElemAbelian p E → Nat.card E ≤ p ^ 4)
    {Ã : Subgroup ↥(e6Data_valid.minGroup F)} (hAe : IsElemAbelian p Ã)
    (hmax : CFSG.Open.pRank p (⊤ : Subgroup ↥(e6Data_valid.minGroup F)) ≤
      CFSG.Open.pRank p Ã)
    {A0 : Subgroup (adjointGroup .E6 F)} (hA0el : IsElemAbelian p A0)
    (hA0card : Nat.card A0 = p ^ 4) :
    Nat.card Ã = p ^ 4 ∧ Disjoint Ã (e6Isogeny F).ker ∧
      Set.InjOn (e6Isogeny F) (Ã : Set ↥(e6Data_valid.minGroup F)) ∧
      IsElemAbelian p (Ã.map (e6Isogeny F)) ∧
      Nat.card (Ã.map (e6Isogeny F)) = p ^ 4 ∧
      (e6Isogeny F).ker = Subgroup.center ↥(e6Data_valid.minGroup F) := by
  classical
  have hker : (e6Isogeny F).ker = Subgroup.center ↥(e6Data_valid.minGroup F) :=
    CFSG.LieType.Steinberg.CentralExt.FieldFour.e6Isogeny_ker_eq_center (K := F)
  have hpZ : ¬ p ∣ Nat.card (Subgroup.center ↥(e6Data_valid.minGroup F)) :=
    not_dvd_card_center_e6_two hcard hp hrk
  have hpker : ¬ p ∣ Nat.card (e6Isogeny F).ker := by rwa [hker]
  have hcopker : Nat.Coprime p (Nat.card (e6Isogeny F).ker) :=
    (Nat.Prime.coprime_iff_not_dvd hp).mpr hpker
  have hprank_adj_le : CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup .E6 F)) ≤ 4 :=
    CFSG.SectionRank.pRank_le hp.one_lt fun E _ hEel => hbound E hEel
  have hprank_adj_ge : 4 ≤ CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup .E6 F)) :=
    CFSG.SectionRank.le_pRank hp.one_lt le_top hA0el hA0card
  have hprank_adj : CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup .E6 F)) = 4 :=
    le_antisymm hprank_adj_le hprank_adj_ge
  have hprank_min : CFSG.Open.pRank p (⊤ : Subgroup ↥(e6Data_valid.minGroup F)) = 4 := by
    rw [CFSG.RankThreeCoreUniqueness.Helpers.pRank_top_eq_of_coprime_kernel p hp
      (e6Isogeny F) (e6Isogeny_surjective F) hcopker, hprank_adj]
  rw [hprank_min] at hmax
  have hArank_le : CFSG.Open.pRank p Ã ≤ 4 := by
    rw [← hprank_min]
    exact CFSG.SectionRank.pRank_mono hp.one_lt le_top
  have hArank : CFSG.Open.pRank p Ã = 4 := le_antisymm hArank_le hmax
  have hAcard : Nat.card Ã = p ^ 4 := by
    rw [CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian hp hAe, hArank]
  have hdisj : Disjoint Ã (e6Isogeny F).ker := by
    refine Subgroup.disjoint_of_coprime_natCard ?_
    rw [hAcard, hker]
    exact Nat.Coprime.pow_left 4 ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpZ)
  have hkerA : Ã ⊓ (e6Isogeny F).ker = ⊥ := hdisj.eq_bot
  have hinjOn : Set.InjOn (e6Isogeny F) (Ã : Set ↥(e6Data_valid.minGroup F)) := by
    intro a ha b hb hab
    have hd : (a⁻¹ * b : ↥(e6Data_valid.minGroup F)) ∈ (e6Isogeny F).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hab, inv_mul_cancel]
    have hmem : (a⁻¹ * b : ↥(e6Data_valid.minGroup F)) ∈
        Ã ⊓ (e6Isogeny F).ker := ⟨Ã.mul_mem (Ã.inv_mem ha) hb, hd⟩
    have hbot : (a⁻¹ * b : ↥(e6Data_valid.minGroup F)) = 1 := by
      have h1 : (a⁻¹ * b : ↥(e6Data_valid.minGroup F)) ∈ (⊥ : Subgroup
          ↥(e6Data_valid.minGroup F)) := by
        rwa [← hkerA]
      exact Subgroup.mem_bot.mp h1
    have : b = a := by
      have h := congrArg (fun x : ↥(e6Data_valid.minGroup F) => a * x) hbot
      simpa [mul_assoc] using h
    exact this.symm
  have hmapElem : IsElemAbelian p (Ã.map (e6Isogeny F)) :=
    CFSG.SectionRank.isElemAbelian_map hAe (e6Isogeny F)
  have hmapCard : Nat.card (Ã.map (e6Isogeny F)) = p ^ 4 := by
    rw [CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.PerfectCentral.card_map_eq_of_injOn
      hinjOn, hAcard]
  exact ⟨hAcard, hdisj, hinjOn, hmapElem, hmapCard, hker⟩

private lemma e6Two_conj_lift (F : Type) [Field F] [Finite F] [CharP F 2]
    [Finite ↥(e6Data_valid.minGroup F)] (p : ℕ) (hp : p.Prime)
    (hconj : ∀ A A₀ : Subgroup (adjointGroup .E6 F), IsElemAbelian p A →
      Nat.card A = p ^ 4 → IsElemAbelian p A₀ → Nat.card A₀ = p ^ 4 →
      ∃ g : adjointGroup .E6 F, A.map (MulAut.conj g).toMonoidHom = A₀)
    {Ã : Subgroup ↥(e6Data_valid.minGroup F)} (hAe : IsElemAbelian p Ã)
    (hmapElem : IsElemAbelian p (Ã.map (e6Isogeny F)))
    (hmapCard : Nat.card (Ã.map (e6Isogeny F)) = p ^ 4)
    {A0 : Subgroup (adjointGroup .E6 F)} (hA0el : IsElemAbelian p A0)
    (hA0card : Nat.card A0 = p ^ 4) {x0 z : adjointGroup .E6 F}
    (hx0A0 : x0 ∈ A0) (hzA0 : z ∈ A0) (hx0ne : x0 ≠ 1)
    {X : Subgroup (adjointGroup .E6 F)} {R3 : Subgroup (adjointGroup .E6 F)}
    (hR3J : R3 ≤ a5Levi F) (hzR : z ∈ R3) (hz1 : z ≠ 1) (hx0X : x0 ∈ X)
    (hdisjXJ : Disjoint X (a5Levi F)) :
    ∃ (gH : ↥(e6Data_valid.minGroup F)) (Ã' : Subgroup ↥(e6Data_valid.minGroup F))
      (xH zH : ↥(e6Data_valid.minGroup F)),
      Ã' = Ã.map (MulAut.conj gH).toMonoidHom ∧
      Ã'.map (e6Isogeny F) = A0 ∧
      xH ∈ Ã' ∧ zH ∈ Ã' ∧ e6Isogeny F xH = x0 ∧ e6Isogeny F zH = z ∧
      IsElemAbelian p Ã' ∧ xH ≠ 1 ∧ zH ∉ Subgroup.zpowers xH := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := hconj (Ã.map (e6Isogeny F)) A0 hmapElem hmapCard hA0el hA0card
  obtain ⟨gH, hgH⟩ := e6Isogeny_surjective F g
  let Ã' : Subgroup ↥(e6Data_valid.minGroup F) := Ã.map (MulAut.conj gH).toMonoidHom
  have hπÃ' : Ã'.map (e6Isogeny F) = A0 := by
    have hcomp : (e6Isogeny F).comp (MulAut.conj gH).toMonoidHom =
        (MulAut.conj g).toMonoidHom.comp (e6Isogeny F) := by
      ext a
      simp [MulAut.conj_apply, hgH]
    rw [show Ã' = Ã.map (MulAut.conj gH).toMonoidHom from rfl, Subgroup.map_map,
      hcomp, ← Subgroup.map_map]
    exact hg
  have hx0map : x0 ∈ Ã'.map (e6Isogeny F) := by rwa [hπÃ']
  have hzmap : z ∈ Ã'.map (e6Isogeny F) := by rwa [hπÃ']
  obtain ⟨xH, hxHÃ', hxHπ⟩ := Subgroup.mem_map.mp hx0map
  obtain ⟨zH, hzHÃ', hzHπ⟩ := Subgroup.mem_map.mp hzmap
  have hAe' : IsElemAbelian p Ã' := by
    dsimp [Ã']
    exact CFSG.SectionRank.isElemAbelian_map hAe (MulAut.conj gH).toMonoidHom
  have hxH1 : xH ≠ 1 := by
    intro h
    have h1 : e6Isogeny F xH = 1 := by rw [h, map_one]
    rw [hxHπ] at h1
    exact hx0ne h1
  have hzxH : zH ∉ Subgroup.zpowers xH := by
    intro hz
    have hz' : e6Isogeny F zH ∈ (Subgroup.zpowers xH).map (e6Isogeny F) :=
      Subgroup.mem_map_of_mem (e6Isogeny F) hz
    rw [MonoidHom.map_zpowers, hxHπ, hzHπ] at hz'
    have hzX : z ∈ X := Subgroup.zpowers_le.mpr hx0X hz'
    have hzJ : z ∈ a5Levi F := hR3J hzR
    have hbot : z ∈ (⊥ : Subgroup (adjointGroup .E6 F)) := by
      rw [← hdisjXJ.eq_bot]
      exact ⟨hzX, hzJ⟩
    rw [Subgroup.mem_bot] at hbot
    exact hz1 hbot
  exact ⟨gH, Ã', xH, zH, rfl, hπÃ', hxHÃ', hzHÃ', hxHπ, hzHπ, hAe', hxH1, hzxH⟩

private lemma e6Two_J_data (F : Type) [Field F] [Finite F] [CharP F 2]
    (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (hpq : p ∣ Nat.card F + 1)
    {X : Subgroup (adjointGroup .E6 F)}
    (hXJ : X ≤ (EPilot.highRootSL2 .E6 F).subgroupOf (adjointGroup .E6 F))
    (hXcyc : IsCyclic X) (hXcard : Nat.card X = Nat.card F + 1)
    {x0 : adjointGroup .E6 F} (hx0X : x0 ∈ X) (hx0 : orderOf x0 = p)
    (hcentXJ : Subgroup.centralizer ({x0} : Set (adjointGroup .E6 F)) = X ⊔ a5Levi F) :
    a5Levi F ≤ Subgroup.centralizer ({x0} : Set (adjointGroup .E6 F)) ∧
      ((a5Levi F).subgroupOf
        (Subgroup.centralizer ({x0} : Set (adjointGroup .E6 F)))).Normal ∧
      CFSG.Open.IsQuasisimple ↥(a5Levi F) ∧ p ∣ Nat.card (a5Levi F) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hJx : a5Levi F ≤ Subgroup.centralizer ({x0} : Set (adjointGroup .E6 F)) := by
    rw [hcentXJ]
    exact le_sup_right
  have hJn : ((a5Levi F).subgroupOf
      (Subgroup.centralizer ({x0} : Set (adjointGroup .E6 F)))).Normal :=
    a5Levi_subgroupOf_centralizer_normal (K := F) (p := p) hp3 hpq hXJ hXcyc hXcard
      hx0X hx0
  have hJq : CFSG.Open.IsQuasisimple ↥(a5Levi F) :=
    CFSG.SeitzReduction.E6Pilot.isQuasisimple_open_a5Levi (K := F)
  have hpJ : p ∣ Nat.card (a5Levi F) := dvd_card_a5Levi (K := F) hp hp3 hpq
  exact ⟨hJx, hJn, hJq, hpJ⟩

private lemma e6Two_qSubgroup_data (F : Type) [Field F] [Finite F] [CharP F 2]
    (n p q : ℕ) (hcard : Nat.card F = 2 ^ n)
    (hp : p.Prime) (hp3 : 3 ≤ p) (hq : q.Prime) (hq2 : q ≠ 2)
    (hqdiv : q ∣ 2 ^ n - 1 ∨ n = 1 ∧ q = 3) (hF : E6TwoFData)
    {x0 z : adjointGroup .E6 F} {xH zH : ↥(e6Data_valid.minGroup F)}
    (hxHπ : e6Isogeny F xH = x0) (hzHπ : e6Isogeny F zH = z)
    {X : Subgroup (adjointGroup .E6 F)}
    (hXJ : X ≤ (EPilot.highRootSL2 .E6 F).subgroupOf (adjointGroup .E6 F))
    (hx0X : x0 ∈ X) {Q : Subgroup (adjointGroup .E6 F)}
    (hQle : Q ≤ a5Levi F ⊓ Subgroup.centralizer ({z} : Set (adjointGroup .E6 F)))
    (hQn : (Q.subgroupOf (a5Levi F ⊓
      Subgroup.centralizer ({z} : Set (adjointGroup .E6 F)))).Normal) :
    ∃ F0 : Subgroup ↥(e6Data_valid.minGroup F),
      IsElemAbelian q F0 ∧ Nat.card F0 = q ^ 3 ∧
      F0 ≤ Subgroup.centralizer ({xH} : Set ↥(e6Data_valid.minGroup F)) ∧
      F0 ⊓ (e6Isogeny F).ker = ⊥ ∧ 3 ≤ CFSG.Open.pRank q F0 ∧
      F0.map (e6Isogeny F) ≤ Subgroup.normalizer (a5Levi F : Set (adjointGroup .E6 F)) ∧
      Q ≤ a5Levi F ∧ Q ≤ Subgroup.centralizer ({z} : Set (adjointGroup .E6 F)) ∧
      Q ≤ Subgroup.centralizer ({e6Isogeny F zH} : Set (adjointGroup .E6 F)) ∧
      (Q.subgroupOf (a5Levi F ⊓ Subgroup.centralizer
        ({e6Isogeny F zH} : Set (adjointGroup .E6 F)))).Normal := by
  classical
  have hqdivF : q ∣ Nat.card F - 1 ∨ Nat.card F = 2 ∧ q = 3 := by
    rcases hqdiv with h | ⟨hn1, hq3⟩
    · left
      rwa [hcard]
    · right
      refine ⟨?_, hq3⟩
      rw [hcard, hn1]
      norm_num
  obtain ⟨F0, hF0el, hF0card, hF0disjcenter, hF0cent, hF0norm⟩ :=
    hF F q hq hq2 hqdivF
  have hx0Lmap : x0 ∈ (e6Data_valid.rootGroup F (highRoot .E6) ⊔
      e6Data_valid.rootGroup F (-highRoot .E6)).map (e6Isogeny F) := by
    rw [map_rootRankOne_highRoot]
    exact hXJ hx0X
  obtain ⟨xH0, hxH0L, hxH0π⟩ := Subgroup.mem_map.mp hx0Lmap
  have hF0xH0 : F0 ≤ Subgroup.centralizer
      ({xH0} : Set ↥(e6Data_valid.minGroup F)) := hF0cent xH0 hxH0L
  have hdker : xH * xH0⁻¹ ∈ (e6Isogeny F).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hxHπ, hxH0π, mul_inv_cancel]
  have hdcenter : xH * xH0⁻¹ ∈ Subgroup.center ↥(e6Data_valid.minGroup F) := by
    rw [CFSG.LieType.Steinberg.CentralExt.FieldFour.e6Isogeny_ker_eq_center (K := F)] at hdker
    exact hdker
  have hF0xH : F0 ≤ Subgroup.centralizer
      ({xH} : Set ↥(e6Data_valid.minGroup F)) := by
    intro f hf
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hfxH0 : f * xH0 = xH0 * f :=
      Subgroup.mem_centralizer_singleton_iff.mp (hF0xH0 hf)
    have hfd : f * (xH * xH0⁻¹) = (xH * xH0⁻¹) * f :=
      (Subgroup.mem_center_iff.mp hdcenter) f
    have hdc : xH0 * (xH * xH0⁻¹) = (xH * xH0⁻¹) * xH0 :=
      (Subgroup.mem_center_iff.mp hdcenter) xH0
    have hxeq : xH = xH0 * (xH * xH0⁻¹) := by
      rw [hdc]
      group
    rw [hxeq]
    calc f * (xH0 * (xH * xH0⁻¹)) = (f * xH0) * (xH * xH0⁻¹) := by group
      _ = (xH0 * f) * (xH * xH0⁻¹) := by rw [hfxH0]
      _ = xH0 * (f * (xH * xH0⁻¹)) := by group
      _ = xH0 * ((xH * xH0⁻¹) * f) := by rw [hfd]
      _ = (xH0 * (xH * xH0⁻¹)) * f := by group
  have hF0disj : F0 ⊓ (e6Isogeny F).ker = ⊥ := by
    rw [CFSG.LieType.Steinberg.CentralExt.FieldFour.e6Isogeny_ker_eq_center (K := F)]
    exact hF0disjcenter
  have hF0pRank : 3 ≤ CFSG.Open.pRank q F0 :=
    CFSG.SectionRank.le_pRank (G := ↥(e6Data_valid.minGroup F)) hq.one_lt
      (le_refl F0) hF0el hF0card
  have hQJ : Q ≤ a5Levi F := hQle.trans inf_le_left
  have hQz : Q ≤ Subgroup.centralizer ({z} : Set (adjointGroup .E6 F)) :=
    hQle.trans inf_le_right
  have hQzπ : Q ≤ Subgroup.centralizer
      ({e6Isogeny F zH} : Set (adjointGroup .E6 F)) := by
    rwa [hzHπ]
  have hQnπ : (Q.subgroupOf (a5Levi F ⊓ Subgroup.centralizer
      ({e6Isogeny F zH} : Set (adjointGroup .E6 F)))).Normal := by
    rwa [hzHπ]
  exact ⟨F0, hF0el, hF0card, hF0xH, hF0disj, hF0pRank, hF0norm, hQJ, hQz, hQzπ, hQnπ⟩

theorem e6TwoModel165At_two_of_rankConj
    (F : Type) [Field F] [Finite F] [CharP F 2] (n p q : ℕ)
    (hcard : Nat.card F = 2 ^ n) (hn : 2 ≤ n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hrk : rk2Ord p n = 2)
    (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p)
    (hqdiv : q ∣ 2 ^ n - 1 ∨ n = 1 ∧ q = 3)
    (hbound : ∀ E : Subgroup (adjointGroup .E6 F), IsElemAbelian p E → Nat.card E ≤ p ^ 4)
    (hconj : ∀ A A₀ : Subgroup (adjointGroup .E6 F), IsElemAbelian p A →
      Nat.card A = p ^ 4 → IsElemAbelian p A₀ → Nat.card A₀ = p ^ 4 →
      ∃ g : adjointGroup .E6 F, A.map (MulAut.conj g).toMonoidHom = A₀)
    (hE : E6TwoLayerData) (hF : E6TwoFData) :
    letI : Finite ↥(e6Data_valid.minGroup F) :=
      CFSG.ClassicalInvolution.ModelFacts.ChevAut.finite_minGroup e6Data_valid F
    ∀ Ã : Subgroup ↥(e6Data_valid.minGroup F), IsElemAbelian p Ã →
      (∀ g ∈ Subgroup.centralizer (Ã : Set ↥(e6Data_valid.minGroup F)),
        orderOf g = p → g ∈ Ã) →
      CFSG.Open.pRank p (⊤ : Subgroup ↥(e6Data_valid.minGroup F)) ≤
        CFSG.Open.pRank p Ã →
      3 ≤ CFSG.Open.pRank p Ã →
      Concl165Avoid ↥(e6Data_valid.minGroup F) p q Ã
        (Subgroup.center ↥(e6Data_valid.minGroup F)) := by
  classical
  letI : Finite ↥(e6Data_valid.minGroup F) :=
    CFSG.ClassicalInvolution.ModelFacts.ChevAut.finite_minGroup e6Data_valid F
  letI : Fact p.Prime := ⟨hp⟩
  intro Ã hAe _hASC hmax _hA3
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hpq : p ∣ Nat.card F + 1 := by
    rw [hcard]
    exact (rk2Ord_eq_two_iff hp hp2).mp hrk
  haveI : Finite (adjointGroup .E6 F) := Subtype.finite
  obtain ⟨R3, z, x0, Q, X, hR3J, hR3el, hR3card, hzR, hz1, hQle, hQq, hpQ, hQn,
    hXJ, hXcyc, hXcard, hx0X, hx0, hx0ne, hcentXJ, hdisjXJ⟩ :=
    e6Two_setup_data F n p hcard hp hp2 hrk hE
  let A0 : Subgroup (adjointGroup .E6 F) := modelE6Two x0 R3
  have hmodel := modelE6Two_isElemAbelian (K := F) (p := p) hp3 hpq hXJ hXcyc hXcard
    hx0X hx0 hR3J hR3el hR3card
  have hA0el : IsElemAbelian p A0 := hmodel.1
  have hA0card : Nat.card A0 = p ^ 4 := hmodel.2
  obtain ⟨-, hdisj, -, hmapElem, hmapCard, hker⟩ :=
    e6Two_rank_data F n p hcard hp hp2 hrk hbound hAe hmax hA0el hA0card
  have hx0A0 : x0 ∈ A0 := by
    dsimp [A0, modelE6Two]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers x0)
  have hzA0 : z ∈ A0 := by
    dsimp [A0, modelE6Two]
    exact Subgroup.mem_sup_right hzR
  obtain ⟨gH, Ã', xH, zH, hÃ'def, hπÃ', hxHÃ', hzHÃ', hxHπ, hzHπ, hAe', hxH1, hzxH⟩ :=
    e6Two_conj_lift F p hp hconj hAe hmapElem hmapCard hA0el hA0card hx0A0 hzA0 hx0ne
      hR3J hzR hz1 hx0X hdisjXJ
  obtain ⟨hJx, hJn, hJq, hpJ⟩ :=
    e6Two_J_data F p hp hp3 hpq hXJ hXcyc hXcard hx0X hx0 hcentXJ
  have hJxπ : a5Levi F ≤
      Subgroup.centralizer ({e6Isogeny F xH} : Set (adjointGroup .E6 F)) := by
    rwa [hxHπ]
  have hJnπ : ((a5Levi F).subgroupOf (Subgroup.centralizer
      ({e6Isogeny F xH} : Set (adjointGroup .E6 F)))).Normal := by
    rwa [hxHπ]
  obtain ⟨F0, hF0el, hF0card, hF0xH, hF0disj, hF0pRank, hF0norm, hQJ, hQz,
    hQzπ, hQnπ⟩ :=
    e6Two_qSubgroup_data F n p q hcard hp hp3 hq hq2 hqdiv hF hxHπ hzHπ hXJ hx0X hQle hQn
  have hconcl' : Concl165Avoid ↥(e6Data_valid.minGroup F) p q Ã' (e6Isogeny F).ker :=
    concl165Avoid_of_central_lift hp (e6Isogeny F) (e6Isogeny_surjective F)
      (le_of_eq hker) hAe' hxHÃ' hzHÃ' hxH1 hzxH
      hJxπ hJnπ hJq hpJ hQJ hQzπ hQnπ hQq hpQ
      hF0el hF0xH hF0norm hF0pRank hF0disj
  have hconcl'' : Concl165Avoid ↥(e6Data_valid.minGroup F) p q
      (Ã.map (MulAut.conj gH).toMonoidHom) (e6Isogeny F).ker := hÃ'def ▸ hconcl'
  have hconcl : Concl165Avoid ↥(e6Data_valid.minGroup F) p q Ã (e6Isogeny F).ker :=
    concl165Avoid_of_conj hp hq (MonoidHom.normal_ker (e6Isogeny F)) gH hconcl''
  rw [hker] at hconcl
  exact hconcl

theorem e6TwoModel165At_two
    (F : Type) [Field F] [Finite F] [CharP F 2] (n p q : ℕ)
    (hcard : Nat.card F = 2 ^ n) (hn : 2 ≤ n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hrk : rk2Ord p n = 2)
    (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p)
    (hqdiv : q ∣ 2 ^ n - 1 ∨ n = 1 ∧ q = 3)
    (hp3 : p ≠ 3) (hE : E6TwoLayerData) (hF : E6TwoFData) :
    letI : Finite ↥(e6Data_valid.minGroup F) :=
      CFSG.ClassicalInvolution.ModelFacts.ChevAut.finite_minGroup e6Data_valid F
    ∀ Ã : Subgroup ↥(e6Data_valid.minGroup F), IsElemAbelian p Ã →
      (∀ g ∈ Subgroup.centralizer (Ã : Set ↥(e6Data_valid.minGroup F)),
        orderOf g = p → g ∈ Ã) →
      CFSG.Open.pRank p (⊤ : Subgroup ↥(e6Data_valid.minGroup F)) ≤
        CFSG.Open.pRank p Ã →
      3 ≤ CFSG.Open.pRank p Ã →
      Concl165Avoid ↥(e6Data_valid.minGroup F) p q Ã
        (Subgroup.center ↥(e6Data_valid.minGroup F)) := by
  have hp5 : 5 ≤ p := Nat.Prime.five_le_of_ne_two_of_ne_three hp hp2 hp3
  have hpq : p ∣ Nat.card F + 1 := by
    rw [hcard]
    exact (rk2Ord_eq_two_iff hp hp2).mp hrk
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (adjointGroup .E6 F) := Subtype.finite
  have hS : SylowTorus (adjointGroup .E6 F) p 4 :=
    CFSG.StandardType.ExcFrames.sylowTorus_adjoint_E6_two F hp (by omega)
      (orderOf_natCard_zmod_eq_two hp (by omega) hpq)
  exact e6TwoModel165At_two_of_rankConj F n p q hcard hn hp hp2 hrk hq hq2 hqp hqdiv
    (fun E hE' => hS.rank_le hp hE')
    (fun A A₀ hA hAc hA₀ hA₀c => exists_conj_eq_modelE6Two (K := F) (p := p) hp5 hpq
      hA hAc hA₀ hA₀c) hE hF

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE6Two
