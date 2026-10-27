module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBG2Comp
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBExcTri
public import CFSG.RankThree.Chevalley.SteinbergCFTrialityToralMain
public import CFSG.RankThree.Chevalley.SteinbergBLTrialitySplitInner
public import CFSG.RankThree.PartOne.FOC.ExcD4Split
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResExcF4
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResExcTri
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcNum
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieTorus
public import CFSG.RankThree.PartOne.K159.BorelSL
public import CFSG.RankThree.PartOne.KC.SymplecticInnerPlaneCore
public import CFSG.RankThree.PartOne.S11d.FixedFactsTri

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Chevalley.TrialitySplitInner CFSG.RankThree.PartOne.FOC
open CFSG.RankThree.PartOne
open scoped commutatorElement Pointwise

section Generic

theorem oddPCoreInClosure_of_map_quasisimple {C G : Type*} [Group C] [Finite C] [Group G] {p : ℕ}
    (hp : p.Prime) (F : C →* G) (hF : Function.Injective F) (Q : Subgroup G)
    (hQD : Q ≤ F.range) (hQn : ∀ c : C, ∀ q ∈ Q, F c * q * (F c)⁻¹ ∈ Q)
    (hQq : CFSG.IsQuasisimple Q) (hpQ : p ∣ Nat.card Q)
    (W : Subgroup G) (hW : ∀ c : C, (∀ q ∈ Q, F c * q = q * F c) → F c ∈ W)
    (hWodd : Odd (Nat.card W)) : OddPCoreInClosure p C := by
  classical
  set Q' : Subgroup C := Q.comap F with hQ'
  haveI : Q'.Normal := ⟨fun q hq c => by
    rw [hQ', Subgroup.mem_comap] at hq ⊢
    rw [map_mul, map_mul, map_inv]
    exact hQn c _ hq⟩
  have hmap : Q'.map F = Q := by
    rw [hQ', Subgroup.map_comap_eq]
    exact inf_eq_right.2 hQD
  let e : Q' ≃* Q := (Subgroup.equivMapOfInjective Q' F hF).trans (MulEquiv.subgroupCongr hmap)
  have hq : CFSG.IsQuasisimple Q' := CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hQq
  have hcent : Odd (Nat.card (Subgroup.centralizer (Q' : Set C))) := by
    let ψ : Subgroup.centralizer (Q' : Set C) →* W :=
      { toFun := fun c => ⟨F c, hW c fun q hqQ => by
          obtain ⟨q', rfl⟩ : q ∈ F.range := hQD hqQ
          have hq' : q' ∈ Q' := hqQ
          have h1 : (c : C) * q' = q' * c := (Subgroup.mem_centralizer_iff.1 c.2 q' hq').symm
          rw [← map_mul, ← map_mul, h1]⟩
        map_one' := by ext; simp
        map_mul' := fun a b => by ext; simp }
    have hψ : Function.Injective ψ := fun a b h =>
      Subtype.ext (hF (congrArg Subtype.val h))
    exact hWodd.of_dvd_nat (Subgroup.card_dvd_of_injective ψ hψ)
  exact oddPCoreInClosure_of_quasisimple_normal hp Q' hq hcent
    (fun _ => by rw [Nat.card_congr e.toEquiv]; exact hpQ)

theorem mem_zpowers_of_pow_eq_one {G : Type*} [Group G] [Finite G] [IsCyclic G] {p : ℕ}
    (hp : 0 < p) {ζ : G} (hζ : orderOf ζ = p) {a : G} (ha : a ^ p = 1) :
    a ∈ Subgroup.zpowers ζ := by
  classical
  haveI := Fintype.ofFinite G
  have hS := IsCyclic.card_pow_eq_one_le (α := G) hp
  have hsub : (Finset.univ.filter fun y : G => y ∈ Subgroup.zpowers ζ) ⊆
      Finset.univ.filter fun y : G => y ^ p = 1 := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hζ, pow_orderOf_eq_one,
      one_zpow]
  have hT : (Finset.univ.filter fun y : G => y ∈ Subgroup.zpowers ζ).card = p := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card, Nat.card_zpowers, hζ]
  have hle : (Finset.univ.filter fun y : G => y ^ p = 1).card ≤
      (Finset.univ.filter fun y : G => y ∈ Subgroup.zpowers ζ).card := by
    rw [hT]
    exact hS
  have heq := Finset.eq_of_subset_of_card_le hsub hle
  have : a ∈ Finset.univ.filter fun y : G => y ^ p = 1 := by simp [ha]
  rw [← heq] at this
  simpa using this

theorem exists_pow_eq_of_mem_zpowers {G : Type*} [Group G] [Finite G] {ζ a : G}
    (h : a ∈ Subgroup.zpowers ζ) : ∃ n : ℕ, ζ ^ n = a :=
  Submonoid.mem_powers_iff _ _ |>.1 (mem_powers_iff_mem_zpowers.2 h)

theorem orderOf_conj_coe {G : Type*} [Group G] (C : Subgroup G) (x g : C) :
    orderOf ((g * x * g⁻¹ : C) : G) = orderOf x := by
  rw [Subgroup.orderOf_coe]
  exact orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x

theorem oddPCoreInClosure_of_conj_toral {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (C : Subgroup G) (x g : C) (d : G) (hd : ((g * x * g⁻¹ : C) : G) = d)
    (hcase : Odd (Nat.card ↥(C ⊓ Subgroup.centralizer ({d} : Set G))) ∨
      ∃ Q W : Subgroup G,
        ⁅C ⊓ Subgroup.centralizer ({d} : Set G), C ⊓ Subgroup.centralizer ({d} : Set G)⁆ = Q ∧
        CFSG.IsQuasisimple Q ∧ p ∣ Nat.card Q ∧
        (C ⊓ Subgroup.centralizer ({d} : Set G)) ⊓ Subgroup.centralizer (Q : Set G) ≤ W ∧
        Odd (Nat.card W)) :
    OddPCoreInClosure p ↥(Subgroup.centralizer ({x} : Set C)) := by
  classical
  let F : ↥(Subgroup.centralizer ({x} : Set C)) →* G :=
    (C.subtype.comp (MulAut.conj g).toMonoidHom).comp (Subgroup.centralizer ({x} : Set C)).subtype
  have hF : Function.Injective F :=
    (Subtype.val_injective.comp (MulAut.conj g).injective).comp (Subgroup.subtype_injective _)
  have hFrange : F.range = C ⊓ Subgroup.centralizer ({d} : Set G) := by
    have h1 : F.range = (Subgroup.centralizer ({x} : Set C)).map
        (C.subtype.comp (MulAut.conj g).toMonoidHom) := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [h1, ← Subgroup.map_map, map_conj_centralizer_singleton_eq,
      CFSG.RankThree.Chevalley.map_subtype_centralizer_singleton, hd]
  rcases hcase with hodd | ⟨Q, W, hcomm, hQq, hpQ, hW, hWodd⟩
  · refine OddPCoreInClosure.of_odd_card ?_
    have hcard : Nat.card (Subgroup.centralizer ({x} : Set C)) = Nat.card F.range :=
      Nat.card_congr (MonoidHom.ofInjective hF).toEquiv
    rw [hcard, hFrange]
    exact hodd
  · set D := C ⊓ Subgroup.centralizer ({d} : Set G) with hD
    have hQD : Q ≤ D := by
      rw [← hcomm, Subgroup.commutator_le]
      intro u hu v hv
      exact D.mul_mem (D.mul_mem (D.mul_mem hu hv) (D.inv_mem hu)) (D.inv_mem hv)
    have hQn : ∀ c : ↥(Subgroup.centralizer ({x} : Set C)), ∀ q ∈ Q,
        F c * q * (F c)⁻¹ ∈ Q := by
      intro c q hq
      have hFc : F c ∈ D := hFrange ▸ ⟨c, rfl⟩
      have h1 : ⁅F c, q⁆ ∈ Q := by
        rw [← hcomm]
        exact Subgroup.commutator_mem_commutator hFc (hQD hq)
      have h2 : F c * q * (F c)⁻¹ = ⁅F c, q⁆ * q := by
        simp [commutatorElement_def, mul_assoc]
      rw [h2]
      exact Q.mul_mem h1 hq
    refine oddPCoreInClosure_of_map_quasisimple hp F hF Q (hFrange ▸ hQD) hQn hQq hpQ W ?_ hWodd
    intro c hc
    have hFc : F c ∈ D := hFrange ▸ ⟨c, rfl⟩
    exact hW ⟨hFc, Subgroup.mem_centralizer_iff.2 fun q hq => (hc q hq).symm⟩

end Generic

section Tri


theorem oddPCoreInClosure_triality_split {K : Type} [Field K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hpq : p ∣ 2 ^ n - 1)
    {x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom} (hx : orderOf x = p) :
    OddPCoreInClosure p
      ↥(Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ two_ne_zero))
  haveI : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  obtain ⟨hSyl, ⟨e, he⟩, -, hodd, hcases⟩ :=
    triality_split_prime_toral_Sylow_and_centralizers Nat.prime_two hn K hK σ hσ hp hp3 hpq
  have hPx : IsPGroup p (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨g, hg⟩ := hSyl _ hPx
  have hgx : g * x * g⁻¹ ∈ (graphFixedRootTorus TwistTag.D4 K σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := hg ⟨x, Subgroup.mem_zpowers x, rfl⟩
  have hgxH : ((g * x * g⁻¹ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
      ModGL TwistTag.D4.tag K) ∈ graphFixedRootTorus TwistTag.D4 K σ.toRingHom := hgx
  obtain ⟨⟨a', b'⟩, hab⟩ := e.surjective ⟨_, hgxH⟩
  have hab' : (e (a', b') : ModGL TwistTag.D4.tag K) =
      ((g * x * g⁻¹ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
        ModGL TwistTag.D4.tag K) := congrArg Subtype.val hab
  have hordx : orderOf ((g * x * g⁻¹ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
      ModGL TwistTag.D4.tag K) = p := by
    rw [orderOf_conj_coe, hx]
  have hpab : (a', b') ^ p = 1 := by
    apply e.injective
    rw [map_pow, map_one]
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    rw [hab', ← hordx]
    exact pow_orderOf_eq_one _
  have ha'p : a' ^ p = 1 := congrArg Prod.fst hpab
  have hb'p : b' ^ p = 1 := congrArg Prod.snd hpab
  obtain ⟨ζ, hζ, hzζ⟩ := exists_fixedUnit_orderOf_eq Nat.prime_two hn hK σ hσ hp hpq
  have : IsCyclic (trialityFixedField K σ.toRingHom)ˣ := inferInstance
  have : IsCyclic Kˣ := inferInstance
  obtain ⟨v, hv⟩ := exists_pow_eq_of_mem_zpowers
    (mem_zpowers_of_pow_eq_one hp.pos hζ hb'p)
  obtain ⟨u, hu⟩ := exists_pow_eq_of_mem_zpowers
    (mem_zpowers_of_pow_eq_one hp.pos hzζ ha'p)
  have hhe : trialityOuterTorus K σ (trialityFixedUnit K σ ζ ^ u) *
      trialityMiddleTorus K σ (ζ ^ v) =
      ((g * x * g⁻¹ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
        ModGL TwistTag.D4.tag K) := by
    rw [← hab', he, hu, hv]
  have hne1 : trialityOuterTorus K σ (trialityFixedUnit K σ ζ ^ u) *
      trialityMiddleTorus K σ (ζ ^ v) ≠ 1 := by
    rw [hhe]
    intro h1
    have := hordx
    rw [h1, orderOf_one] at this
    exact hp.one_lt.ne this
  obtain ⟨a, hha, hao, hcase⟩ := hcases ζ hζ u v hne1
  have hxa : ((g * x * g⁻¹ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
      ModGL TwistTag.D4.tag K) = rootDiagUnit TwistTag.D4.tag a := by rw [← hha, hhe]
  refine oddPCoreInClosure_of_conj_toral hp _ x g _ hxa ?_
  rcases hcase with ⟨-, hDH⟩ | ⟨α, hα, hα0, -, D, Q, hD, hQ, hDQ, -, hSL3, hSL1, hQq, hcomm, hcent,
    hZH, -, hZodd⟩
  · left
    rw [hDH]
    exact hodd rfl
  · right
    have hq1 : 2 ^ n ≡ 1 [MOD p] := by
      have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      exact ((Nat.modEq_iff_dvd' h1).2 hpq).symm
    have hpL : ∀ L : Type, ∀ m : ℕ, [Field L] → [Finite L] → Nat.card L = (2 ^ n) ^ m → 0 < m →
        Nonempty (SL2 L ≃* Q) → p ∣ Nat.card Q := by
      intro L m _ _ hL hm ⟨eQ⟩
      rw [← Nat.card_congr eQ.toEquiv, ← CFSG.Open.StatedAPI.card_statedSL]
      rw [CFSG.Open.StatedAPI.card_statedSL_two L, hL]
      refine Dvd.dvd.mul_left ?_ _
      have h1 : p ∣ (2 ^ n) ^ m - 1 := by
        have h3 : 1 ≡ (2 ^ n) ^ m [MOD p] := by simpa using (hq1.pow m).symm
        exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ Nat.one_le_two_pow)).1 h3
      have h2 : (2 ^ n) ^ m - 1 ∣ ((2 ^ n) ^ m) ^ 2 - 1 := by
        have hx : 1 ≤ (2 ^ n) ^ m := Nat.one_le_pow _ _ Nat.one_le_two_pow
        refine ⟨(2 ^ n) ^ m + 1, ?_⟩
        zify [hx, Nat.one_le_pow 2 _ hx]
        ring
      exact h1.trans h2
    have hpQ : p ∣ Nat.card Q := by
      rcases card_diagramOrbit_D4 hα with h | h
      · have hk : Nat.card (trialityFixedField K σ.toRingHom) = (2 ^ n) ^ 1 := by
          rw [pow_one]
          exact card_trialityFixedField Nat.prime_two hn hK σ hσ
        exact hpL (trialityFixedField K σ.toRingHom) 1 hk one_pos (hSL1 h)
      · exact hpL K 3 hK (by norm_num) (hSL3 h)
    refine ⟨Q, (Subgroup.center D).map D.subtype, ?_, hQq, hpQ, ?_, ?_⟩
    · rw [← hD]
      exact hcomm
    · rw [← hD]
      exact hcent.le
    · rw [Subgroup.card_map_of_injective D.subtype_injective]
      exact hZodd rfl

end Tri

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
