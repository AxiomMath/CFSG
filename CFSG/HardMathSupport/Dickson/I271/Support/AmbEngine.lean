module

public import CFSG.HardMathSupport.Dickson.I271.ChevPBal
public import CFSG.HardMathSupport.Dickson.I271.Support.ChevInner
public import CFSG.HardMathSupport.Dickson.I271.Support.EngineGen
public import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsBase
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_6_PartIIExists

public section

namespace CFSG.HardMathSupport.Dickson.I271.Amb

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.LocalAnalysis.GLTheoremA CFSG.Yardstones.Md0ec50421ce4 CFSG.HardMathSupport.Dickson.I271
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance

section Engine

variable {X : Type} [Group X] [Finite X]

@[expose] def CoreFreeInner (p : ℕ) (K : Subgroup X) : Prop :=
  ∀ x ∈ innerAut (↥K ⧸ Subgroup.center ↥K), orderOf x = p →
    ∀ H : Subgroup (MulAut (↥K ⧸ Subgroup.center ↥K)), innerAut (↥K ⧸ Subgroup.center ↥K) ≤ H →
      GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({x} : Set (MulAut (↥K ⧸ Subgroup.center ↥K)))) = ⊥

@[expose] def NoCompInner (p : ℕ) (K : Subgroup X) : Prop :=
  ∀ β : MulAut (↥K ⧸ Subgroup.center ↥K), β ^ p = 1 → β ≠ 1 →
    β ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (↥K ⧸ Subgroup.center ↥K) →
      GLAPLayer p (fixSubgroup β) = ⊥

theorem coreFree_of_inner_gen {p : ℕ} {K : Subgroup X} (hO : GLAPPrimeCore p ↥K = ⊥)
    (hq : CFSG.Open.IsQuasisimple ↥K) (hCF : CoreFreeInner p K)
    {H : Subgroup (MulAut (barOf p K))} (hH : innerAut (barOf p K) ≤ H)
    {d : MulAut (barOf p K)} (hd : d ∈ innerAut (barOf p K)) (hdp : orderOf d = p) :
    GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({d} : Set (MulAut (barOf p K)))) = ⊥ := by
  set Φ := autBarToQuot p hO with hΦ
  have hΦinj : Function.Injective Φ := autBarToQuot_injective p hO hq.1
  have hinnS : innerAut (↥K ⧸ Subgroup.center ↥K) ≤ H.map Φ := by
    rintro _ ⟨s, rfl⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
    refine ⟨MulAut.conj (barOfEquiv p hO x), hH ⟨_, rfl⟩, ?_⟩
    rw [hΦ, autBarToQuot_conj]
    simp
  obtain ⟨q, rfl⟩ := hd
  have hx : Φ (MulAut.conj q) ∈ innerAut (↥K ⧸ Subgroup.center ↥K) := by
    rw [hΦ, autBarToQuot_conj]
    exact ⟨_, rfl⟩
  have hxord : orderOf (Φ (MulAut.conj q)) = p := by
    rw [orderOf_injective Φ hΦinj]
    exact hdp
  have hS := hCF _ hx hxord (H.map Φ) hinnS
  rw [← map_inf_centralizer_of_injective Φ hΦinj,
    ← map_glaPPrimeCoreOf_of_injective p Φ hΦinj] at hS
  exact (Subgroup.map_eq_bot_iff_of_injective _ hΦinj).1 hS

theorem isCompLocallyBalanced_of_inner_gen {p : ℕ} (hp : p.Prime) {K A : Subgroup X}
    (hq : CFSG.Open.IsQuasisimple ↥K) (hO : GLAPPrimeCore p ↥K = ⊥) (hCF : CoreFreeInner p K)
    (hAN : A ≤ Subgroup.normalizer (K : Set X))
    (hin : ∀ a ∈ A, ∃ k ∈ K, k⁻¹ * a ∈ Subgroup.centralizer (K : Set X)) :
    IsCompLocallyBalanced p 1 A K := by
  intro D hD H hH hDH
  haveI : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card D = p := by simpa using hD.2.2
  have hnt : 1 < Nat.card D := by rw [hcard]; exact hp.one_lt
  obtain ⟨d, hdD, hd1⟩ : ∃ d ∈ D, d ≠ 1 := by
    have : Nontrivial D := Finite.one_lt_card_iff_nontrivial.mp hnt
    obtain ⟨⟨d, hd⟩, hne⟩ := exists_ne (1 : D)
    exact ⟨d, hd, fun h => hne (Subtype.ext h)⟩
  have hdp : orderOf d = p := orderOf_eq_prime (hD.2.1.2 d hdD) hd1
  obtain ⟨γ, hγ, rfl⟩ := hD.1 hdD
  obtain ⟨k, hk, hkc⟩ := hin (γ : X) ((Subgroup.mem_subgroupOf.1 hγ).1)
  have hdinner : barAut p K γ ∈ innerAut (barOf p K) := by
    have := barAut_eq_conj_of_inner (p := p) hk hkc γ.2
    rw [show γ = ⟨(γ : X), γ.2⟩ from rfl, this]
    exact ⟨_, rfl⟩
  have key := coreFree_of_inner_gen hO hq hCF hH hdinner hdp
  unfold localDeltaIn
  refine eq_bot_iff.2 ?_
  exact (iInf_le_of_le (barAut p K γ) (iInf_le_of_le hdD (iInf_le _ hd1))).trans key.le

theorem not_glaPComponent_of_inner_gen {p : ℕ} (hp : p.Prime) {K : Subgroup X}
    (hq : CFSG.Open.IsQuasisimple ↥K) (hNC : NoCompInner p K) {a k : X} (hk : k ∈ K)
    (hc : k⁻¹ * a ∈ Subgroup.centralizer (K : Set X))
    (hkZ : (⟨k, hk⟩ : ↥K) ∉ Subgroup.center ↥K) (hkp : (⟨k, hk⟩ : ↥K) ^ p ∈ Subgroup.center ↥K)
    {J : Subgroup X} (hJ : GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J) :
    False := by
  set k' : ↥K := ⟨k, hk⟩ with hk'
  set π : ↥K →* ↥K ⧸ Subgroup.center ↥K := QuotientGroup.mk' (Subgroup.center ↥K) with hπ
  set α : MulAut ↥K := MulAut.conj k' with hα
  set β : MulAut (↥K ⧸ Subgroup.center ↥K) := MulAut.conj (π k') with hβ
  have hker : π.ker ≤ Subgroup.center ↥K := by rw [hπ, QuotientGroup.ker_mk']
  have hαβ : ∀ y, π (α y) = β (π y) := fun y => by simp [hα, hβ, MulAut.conj_apply]
  have hfix : (K ⊓ Subgroup.centralizer ({a} : Set X)).subgroupOf K = fixSubgroup α := by
    ext y
    rw [Subgroup.mem_subgroupOf, mem_fixSubgroup, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    have hcy : (k⁻¹ * a) * (y : X) = (y : X) * (k⁻¹ * a) :=
      (Subgroup.mem_centralizer_iff.1 hc y y.2).symm
    constructor
    · rintro ⟨-, hy⟩
      apply Subtype.ext
      show k * (y : X) * k⁻¹ = (y : X)
      calc k * (y : X) * k⁻¹ = k * ((k⁻¹ * a) * y) * (k⁻¹ * a)⁻¹ * k⁻¹ := by
            rw [hcy]; group
        _ = a * (y : X) * a⁻¹ := by group
        _ = (y : X) := by rw [← hy]; group
    · intro hy
      refine ⟨y.2, ?_⟩
      have h1 : k * (y : X) * k⁻¹ = (y : X) := congrArg Subtype.val hy
      have hky : k * (y : X) = (y : X) * k := mul_inv_eq_iff_eq_mul.1 h1
      calc (y : X) * a = y * (k * (k⁻¹ * a)) := by group
        _ = (y * k) * (k⁻¹ * a) := by group
        _ = (k * y) * (k⁻¹ * a) := by rw [← hky]
        _ = k * (y * (k⁻¹ * a)) := by group
        _ = k * ((k⁻¹ * a) * y) := by rw [← hcy]
        _ = a * (y : X) := by group
  have hJ' := glaPComponent_subgroupOf hp
    (inf_le_left : K ⊓ Subgroup.centralizer ({a} : Set X) ≤ K) hJ
  rw [hfix] at hJ'
  have hnc := exists_noncomm_of_isQuasisimple hq
  haveI : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hq.2
  have hSz : Subgroup.center (↥K ⧸ Subgroup.center ↥K) = ⊥ := center_eq_bot_of_simple hnc
  have hβp : β ^ p = 1 := by
    rw [hβ, ← map_pow]
    have : π k' ^ p = 1 := by rw [← map_pow]; exact (QuotientGroup.eq_one_iff _).2 hkp
    rw [this, map_one]
  have hβ1 : β ≠ 1 := by
    intro h
    apply hkZ
    have : π k' ∈ Subgroup.center (↥K ⧸ Subgroup.center ↥K) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := DFunLike.congr_fun h g
      simp only [hβ, MulAut.conj_apply, MulAut.one_apply] at this
      exact (mul_inv_eq_iff_eq_mul.1 this).symm
    rw [hSz, Subgroup.mem_bot] at this
    exact (QuotientGroup.eq_one_iff _).1 this
  have hlay := hNC β hβp hβ1 ⟨π k', rfl⟩
  have hmap := map_glaPLayer_fixSubgroup_eq π hker α β hαβ (QuotientGroup.mk'_surjective _) hp
  rw [hlay] at hmap
  have hle : J.subgroupOf K ≤ GLAPLayer p (fixSubgroup α) := le_sSup hJ'
  have hJc : J.subgroupOf K ≤ Subgroup.center ↥K := by
    intro y hy
    have : π y ∈ (GLAPLayer p (fixSubgroup α)).map π := ⟨y, hle hy, rfl⟩
    rw [hmap, Subgroup.mem_bot] at this
    exact hker ((MonoidHom.mem_ker).2 this)
  have hperf := glaPComponent_perfect hJ'
  have hbot : ⁅J.subgroupOf K, J.subgroupOf K⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.2 (hJc.trans (Subgroup.center_le_centralizer _))
  rw [hbot] at hperf
  exact glaPComponent_ne_bot' hJ' hperf.symm

theorem engineInner {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K B : Subgroup X}
    (hcore : GLAPPrimeCore p X = ⊥) (hcomp : GLAPComponent p ⊤ K) (hscp : IsSCp p ⊤ B)
    (hCF : CoreFreeInner p K) (hNC : NoCompInner p K)
    (hBN : B ≤ Subgroup.normalizer (K : Set X)) (hA : InnerNoncyclicIn B K) :
    IsStronglyBalancedIn p B K := by
  obtain ⟨A, hAB, hAnc, hAfaith, hAin⟩ := hA
  haveI : Fact p.Prime := ⟨hp⟩
  have hq : CFSG.Open.IsQuasisimple ↥K := i116e_isQuasisimple hcore hcomp
  have hO : GLAPPrimeCore p ↥K = ⊥ := i271h_primeCore_eq_bot hcore hcomp
  have hBel : IsElemAbelian p B := hscp.2.1
  have hdvd : p ∣ Nat.card K := i116e_dvd_card hp hcore hcomp
  have hSC : IsSCp p (K ⊔ B) B :=
    ⟨le_sup_right, hBel, fun E _ hEel hBE => hscp.2.2 E le_top hEel hBE⟩
  have hAN : A ≤ Subgroup.normalizer (K : Set X) := hAB.trans hBN
  have hloc : IsCompLocallyBalanced p 1 A K :=
    isCompLocallyBalanced_of_inner_gen hp hq hO hCF hAN hAin
  have hno : ∀ a ∈ A, a ≠ 1 → ∀ J : Subgroup X,
      ¬ GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J := by
    intro a ha ha1 J hJ
    obtain ⟨k, hk, hc⟩ := hAin a ha
    have haC : a ∉ Subgroup.centralizer (K : Set X) := fun h =>
      ha1 (by
        have : a ∈ A ⊓ Subgroup.centralizer (K : Set X) := ⟨ha, h⟩
        rw [hAfaith] at this
        exact Subgroup.mem_bot.1 this)
    have hkZ : (⟨k, hk⟩ : ↥K) ∉ Subgroup.center ↥K := by
      intro hz
      apply haC
      have hk1 : k ∈ Subgroup.centralizer (K : Set X) := by
        rw [Subgroup.mem_centralizer_iff]
        intro g hg
        exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨g, hg⟩)
      have : a = k * (k⁻¹ * a) := by group
      rw [this]
      exact Subgroup.mul_mem _ hk1 hc
    have hkp : (⟨k, hk⟩ : ↥K) ^ p ∈ Subgroup.center ↥K := by
      have hap : a ^ p = 1 := hBel.2 a (hAB ha)
      have hcomm : Commute k (k⁻¹ * a) := Subgroup.mem_centralizer_iff.1 hc k hk
      have h1 : k ^ p * (k⁻¹ * a) ^ p = 1 := by
        rw [← hcomm.mul_pow]
        have : k * (k⁻¹ * a) = a := by group
        rw [this, hap]
      have h2 : k ^ p ∈ Subgroup.centralizer (K : Set X) := by
        have : k ^ p = ((k⁻¹ * a) ^ p)⁻¹ := eq_inv_of_mul_eq_one_left h1
        rw [this]
        exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hc p)
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 h2 g g.2)
    exact not_glaPComponent_of_inner_gen hp hq hNC hk hc hkZ hkp hJ
  obtain ⟨a₀, ha₀A, ha₀1⟩ : ∃ a ∈ A, a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hAnc
    haveI : Subsingleton ↥A :=
      ⟨fun x y => Subtype.ext ((hcon x x.2).trans (hcon y y.2).symm)⟩
    exact isCyclic_of_subsingleton
  exact engine_full ⟨hp, hp2, hq, hdvd, hBN, hBel, hSC, hAB, hAnc, hloc, fun a ha ha1 J hJ =>
    (hno a ha ha1 J hJ).elim⟩ ⟨a₀, ha₀A, ha₀1, fun w _ _ _ J hJ => (hno a₀ ha₀A ha₀1 J hJ).elim⟩

end Engine

section Solv

variable {Y : Type} [Group Y]

theorem eq_bot_of_perfect_of_solvable {J S : Subgroup Y} (hS : Group.IsSolvable ↥S) (hJS : J ≤ S)
    (hperf : ⁅J, J⁆ = J) : J = ⊥ := by
  by_contra hne
  have hJ'ne : J.subgroupOf S ≠ ⊥ := by
    intro h0
    apply hne
    rw [← Subgroup.map_subgroupOf_eq_of_le hJS, h0, Subgroup.map_bot]
  have hlt : ⁅J.subgroupOf S, J.subgroupOf S⁆ < J.subgroupOf S :=
    Group.IsSolvable.commutator_lt_of_ne_bot hJ'ne
  have heq : ⁅J.subgroupOf S, J.subgroupOf S⁆ = J.subgroupOf S := by
    apply Subgroup.map_injective (f := S.subtype) S.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hJS]
    exact hperf
  rw [heq] at hlt
  exact lt_irrefl _ hlt

theorem coprime_ker_of_mulEquiv {p : ℕ} {S T : Type} [Group S] [Group T] (e : S ≃* T)
    (X : Subgroup S) : Nat.Coprime p (Nat.card ↥(X ⊓ e.toMonoidHom.ker)) := by
  have hk : e.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff e.toMonoidHom).2 e.injective
  rw [hk, inf_bot_eq, Subgroup.card_bot]
  exact Nat.coprime_one_right p

theorem fixSubgroup_congr {S T : Type} [Group S] [Group T] (e : S ≃* T) (α : MulAut S) :
    fixSubgroup (MulAut.congr e α) = (fixSubgroup α).map e.toMonoidHom := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · intro hy
    rw [mem_fixSubgroup] at hy
    have h2 : e (α (e.symm y)) = y := hy
    refine ⟨e.symm y, ?_, by simp⟩
    rw [mem_fixSubgroup]
    have h3 := congrArg e.symm h2
    simpa using h3
  · rintro ⟨x, hx, rfl⟩
    rw [mem_fixSubgroup] at hx
    rw [mem_fixSubgroup]
    show e (α (e.symm (e x))) = e x
    rw [MulEquiv.symm_apply_apply, hx]

end Solv

end CFSG.HardMathSupport.Dickson.I271.Amb
