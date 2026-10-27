module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SFieldCore
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SFieldChief
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82A10TZStar
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10SpCard
public import CFSG.RankThree.Classical.ElemTwoFixedSpaceBound
public import CFSG.RankThree.OddKernel.CentralCoverComponentModels
public import CFSG.LocalAnalysis.GorensteinLyons.LinearThreeAutTwoRank
public import CFSG.GH74.GLS.Stage1.Thm4.L96Sylow

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped commutatorElement

@[expose] def L34ActiveComponentBound : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t a : G), orderOf t = 2 → orderOf a = 2 → t * a = a * t →
    (∀ J : Subgroup G, GSUnbalancingTriple a t J →
      IsL2Type 5 (J ⧸ pPrimeCore 2 J) ∨ IsL2Type 7 (J ⧸ pPrimeCore 2 J) ∨
        IsL34Type (J ⧸ Open.fusionZStar J)) →
    ∀ Y : Subgroup G, Y ≤ oddIn (centralizer ({t} : Set G)) ⊓ centralizer ({a} : Set G) →
    ∀ p : ℕ, p.Prime → p ≠ 2 →
      padicValNat p ((oddIn (centralizer ({a} : Set G))).relIndex Y) ≤
        3 * pRank 2 ↥(centralizer ({t} : Set G) ⊓ centralizer ({a} : Set G))

@[expose] def L3TwoPowChiefFixedPoints : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (P : Subgroup G) (m : ℕ), ⁅P, P⁆ = P → 3 ≤ m →
    Blueprint.LieModel (↥P ⧸ Open.fusionZStar ↥P) .PSL 3 2 m → ⁅oddIn P, P⁆ ≠ ⊥ →
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ∃ E : Subgroup G, E ≤ P ∧ Open.IsElemAbelian 2 E ∧
      Nat.card E = 2 ^ (2 * m) ∧ ∀ u ∈ E, u ≠ 1 →
        2 ^ (2 * m - 1) - 1 ≤
          padicValNat p (Nat.card ↥(⁅oddIn P, P⁆ ⊓ centralizer ({u} : Set G)))

theorem l3TwoPowAutTwoRank_holds :
    ∀ (X : Type) [Group X] [Finite X] (m : ℕ), 1 ≤ m → Blueprint.LieModel X .PSL 3 2 m →
      pRank 2 (MulAut X) ≤ 3 * m + 2 := fun _ _ _ _ hm hX =>
  LocalAnalysis.GorensteinLyons.LinearUnitaryOuter.pRank_mulAut_le_of_lieModel_psl_three hm hX

section Chief

variable {X : Type} [Group X] [Finite X]

theorem exists_conj_of_odd_normal (N : Subgroup X) [N.Normal] (hN : Odd (Nat.card N))
    (hconj : ∀ x y : X ⧸ N, x * x = 1 → x ≠ 1 → y * y = 1 → y ≠ 1 → ∃ g, g * x * g⁻¹ = y)
    {x y : X} (hx : x * x = 1) (hx1 : x ≠ 1) (hy : y * y = 1) (hy1 : y ≠ 1) :
    ∃ g : X, g * x * g⁻¹ = y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' N with hπ
  have hnotN : ∀ z : X, z * z = 1 → z ≠ 1 → z ∉ N := by
    intro z hz hz1 hzN
    have h2 : (⟨z, hzN⟩ : N) ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, pow_two]; exact hz)
    have hdvd : orderOf (⟨z, hzN⟩ : N) ∣ 2 := orderOf_dvd_of_pow_eq_one h2
    have hodd : orderOf (⟨z, hzN⟩ : N) ∣ Nat.card N := orderOf_dvd_natCard _
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact hz1 (congrArg Subtype.val (orderOf_eq_one_iff.mp h))
    · rw [h, ← even_iff_two_dvd] at hodd
      exact (Nat.not_even_iff_odd.mpr hN) hodd
  have hπx : π x * π x = 1 := by rw [← map_mul, hx, map_one]
  have hπy : π y * π y = 1 := by rw [← map_mul, hy, map_one]
  have hπx1 : π x ≠ 1 := fun h => hnotN x hx hx1 ((QuotientGroup.eq_one_iff x).mp h)
  have hπy1 : π y ≠ 1 := fun h => hnotN y hy hy1 ((QuotientGroup.eq_one_iff y).mp h)
  obtain ⟨gbar, hg⟩ := hconj (π x) (π y) hπx hπx1 hπy hπy1
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N gbar
  set x' := g * x * g⁻¹ with hx'
  have hx'2 : x' * x' = 1 := by
    rw [hx']
    calc g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
      _ = 1 := by rw [hx, mul_one, mul_inv_cancel]
  have hπx' : π x' = π y := by rw [hx', map_mul, map_mul, map_inv]; exact hg
  have hpg : ∀ z : X, z * z = 1 → IsPGroup 2 (zpowers z) := by
    intro z hz w
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp w.2
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, Subgroup.coe_pow, ← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      Nat.cast_ofNat, zpow_two, hz, one_zpow, OneMemClass.coe_one]
  have hker : Odd (Nat.card π.ker) := by rw [QuotientGroup.ker_mk']; exact hN
  have hmap : (zpowers x').map π = (zpowers y).map π := by
    rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers, hπx']
  obtain ⟨c, hc⟩ := GH74.Uniqueness.SU.SU4.exists_conj_of_map_eq π hker (hpg x' hx'2) (hpg y hy) hmap
  have hc' : zpowers (c * x' * c⁻¹) = zpowers y := by
    rw [← hc, GH74.Uniqueness.SU.SU4.conjSub, MonoidHom.map_zpowers]
    rfl
  have hmem : c * x' * c⁻¹ ∈ zpowers y := hc' ▸ mem_zpowers _
  have hne : c * x' * c⁻¹ ≠ 1 := by
    intro h
    have : x' = 1 := by
      calc x' = c⁻¹ * (c * x' * c⁻¹) * c := by group
        _ = 1 := by rw [h, mul_one, inv_mul_cancel]
    rw [hx'] at this
    exact hx1 (by
      calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = 1 := by rw [this, mul_one, inv_mul_cancel])
  have hoy : orderOf y = 2 := orderOf_eq_prime (by rw [pow_two]; exact hy) hy1
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hmem
  rw [← zpow_mod_orderOf, hoy] at hk
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · rw [Nat.cast_ofNat, h0, zpow_zero] at hk
    exact absurd hk.symm hne
  · rw [Nat.cast_ofNat, h1, zpow_one] at hk
    refine ⟨c * g, ?_⟩
    rw [hk, hx']
    group

theorem mem_of_representation_eq_one {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    [Group.IsPerfect X] (Z : Subgroup X) [Z.Normal] [Group.IsSolvable Z]
    [IsSimpleGroup (X ⧸ Z)] (ρ : Representation k X V) (hρ : ∃ h : X, ∃ v : V, ρ h v ≠ v)
    {g : X} (hg : ρ g = 1) : g ∈ Z := by
  by_contra hgZ
  set K := MonoidHom.ker ρ with hKdef
  have hgK : g ∈ K := MonoidHom.mem_ker.mpr hg
  have hK : K ⊔ Z = ⊤ := by
    have hn : (K.map (QuotientGroup.mk' Z)).Normal :=
      Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective Z)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K.map (QuotientGroup.mk' Z)) with h | h
    · exfalso
      have h1 : QuotientGroup.mk' Z g ∈ K.map (QuotientGroup.mk' Z) := mem_map_of_mem _ hgK
      rw [h, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact hgZ h1
    · have h2 := congrArg (Subgroup.comap (QuotientGroup.mk' Z)) h
      rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top] at h2
  have : Group.IsPerfect (⊤ : Subgroup X) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.topEquiv (G := X)).symm.toMonoidHom)
      (Subgroup.topEquiv (G := X)).symm.surjective
  have htop : (⊤ : Subgroup X) ≤ K :=
    ClassicalInvolution.LBalanceProof.perfect_le_of_le_sup_solvable ⊤ K Z (by rw [hK])
  obtain ⟨h, v, hv⟩ := hρ
  apply hv
  rw [MonoidHom.mem_ker.mp (htop (mem_top h))]
  rfl

omit [Finite X] in
theorem finrank_ker_conj_sub_one {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (ρ : Representation k X V) (g x : X) :
    Module.finrank k (LinearMap.ker (ρ (g * x * g⁻¹) - 1)) =
      Module.finrank k (LinearMap.ker (ρ x - 1)) := by
  have h1 : (ρ g).comp (ρ g⁻¹) = LinearMap.id := by
    rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]
    rfl
  have h2 : (ρ g⁻¹).comp (ρ g) = LinearMap.id := by
    rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]
    rfl
  let eg : V ≃ₗ[k] V := LinearEquiv.ofLinear (ρ g) (ρ g⁻¹) h1 h2
  have hmap : (LinearMap.ker (ρ x - 1)).map (eg : V →ₗ[k] V) =
      LinearMap.ker (ρ (g * x * g⁻¹) - 1) := by
    ext v
    simp only [Submodule.mem_map, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply,
      sub_eq_zero]
    constructor
    · rintro ⟨w, hw, rfl⟩
      change ρ (g * x * g⁻¹) (ρ g w) = ρ g w
      rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, ← Module.End.mul_apply
        (ρ g⁻¹), ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply, hw]
    · intro hv
      refine ⟨ρ g⁻¹ v, ?_, ?_⟩
      · have := congrArg (ρ g⁻¹) hv
        rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
          ← Module.End.mul_apply (ρ g⁻¹) (ρ g), ← map_mul, inv_mul_cancel, map_one,
          Module.End.one_apply] at this
        exact this
      · change ρ g (ρ g⁻¹ v) = v
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  rw [← hmap, LinearEquiv.finrank_map_eq]

theorem l3TwoPowChiefFixedPoints_of_griess (hGA : Open.GriessAllModelsStatement) :
    L3TwoPowChiefFixedPoints := by
  intro G _ _ P m hperf hm hL hD
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPperf : Group.IsPerfect ↥P := Subgroup.isPerfect_iff.mpr hperf
  have hZO := fusionZStar_eq_fusionOddCore_of_lieModel_psl_three hGA hm hL
  set Z := Open.fusionZStar ↥P with hZdef
  set U := pPrimeCore 2 ↥P with hUdef
  have hZU : Z = U := by rw [hZO, UnbalancingLocal.fusionOddCore_eq_pPrimeCore]
  have hUodd : Odd (Nat.card U) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hZodd : Odd (Nat.card Z) := hZU ▸ hUodd
  have : Group.IsSolvable Z := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hZodd
  have : IsSimpleGroup (↥P ⧸ Z) :=
    CatLeafProof.X10Sp.isSimpleGroup_of_lieModel_psl (by norm_num) hL
  have hZinv : ∀ z : ↥P, z ∈ Z → z * z = 1 → z = 1 := by
    intro z hzZ hz
    have h2 : (⟨z, hzZ⟩ : Z) ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, pow_two]; exact hz)
    have hdvd : orderOf (⟨z, hzZ⟩ : Z) ∣ 2 := orderOf_dvd_of_pow_eq_one h2
    have hodd : orderOf (⟨z, hzZ⟩ : Z) ∣ Nat.card Z := orderOf_dvd_natCard _
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact congrArg Subtype.val (orderOf_eq_one_iff.mp h)
    · rw [h, ← even_iff_two_dvd] at hodd
      exact absurd hodd (Nat.not_even_iff_odd.mpr hZodd)
  obtain ⟨E₀, hE₀, hE₀card⟩ := exists_elemAbelian_card_of_lieModel_psl_three hL
  set π := QuotientGroup.mk' Z with hπ
  have hker : Odd (Nat.card π.ker) := by rw [QuotientGroup.ker_mk']; exact hZodd
  obtain ⟨E₁, hE₁c, hE₁2, hE₁card⟩ := GH74.GLS.Stage1.Thm4.L96.exists_elemAbelian_of_odd_kernel π
    hker E₀ (by rw [MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective Z)]; exact le_top)
    (fun a ha b hb => (isMulCommutative_iff_of_setLike.mp hE₀.1) a ha b hb) hE₀.2
  have hE₁p : IsPGroup 2 E₁ := fun x =>
    ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow]; exact hE₁2 x x.2)⟩
  obtain ⟨k, hk⟩ := hE₁p.exists_card_eq
  have h2m : 2 * m ≤ k := (Nat.pow_le_pow_iff_right (by norm_num)).mp (hE₀card ▸ hk ▸ hE₁card)
  obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime 2 (n := 2 * m)
    (hk ▸ pow_dvd_pow 2 h2m : 2 ^ (2 * m) ∣ Nat.card E₁)
  set E₂ : Subgroup ↥P := H.map E₁.subtype with hE₂
  have hE₂E₁ : E₂ ≤ E₁ := map_subtype_le _
  have hE₂card : Nat.card E₂ = 2 ^ (2 * m) := by
    rw [hE₂, card_map_of_injective E₁.subtype_injective, hH]
  have hE₂ab : Open.IsElemAbelian 2 E₂ :=
    ⟨isMulCommutative_iff_of_setLike.mpr fun a ha b hb => hE₁c a (hE₂E₁ ha) b (hE₂E₁ hb),
      fun a ha => hE₁2 a (hE₂E₁ ha)⟩
  have hE₂sq : ∀ e ∈ E₂, e * e = 1 := fun e he => by rw [← pow_two]; exact hE₂ab.2 e he
  have hconjP : ∀ x y : ↥P, x * x = 1 → x ≠ 1 → y * y = 1 → y ≠ 1 → ∃ g, g * x * g⁻¹ = y :=
    fun x y hx hx1 hy hy1 => exists_conj_of_odd_normal Z hZodd
      (fun x y hx hx1 hy hy1 => exists_conj_of_lieModel_psl_three hL hx hx1 hy hy1) hx hx1 hy hy1
  have hPtop : (⊤ : Subgroup ↥P).map P.subtype = P := by
    rw [← MonoidHom.range_eq_map, range_subtype]
  have hDmap : Subgroup.map P.subtype ⁅U, (⊤ : Subgroup ↥P)⁆ = ⁅oddIn P, P⁆ := by
    rw [map_commutator, hPtop]
    rfl
  have hne : ⁅U, (⊤ : Subgroup ↥P)⁆ ≠ ⊥ := fun h => hD (by rw [← hDmap, h, Subgroup.map_bot])
  have hYperf : ⁅(⊤ : Subgroup ↥P), (⊤ : Subgroup ↥P)⁆ = ⊤ := by
    rw [← commutator_def]
    exact Group.IsPerfect.commutator_eq_top
  obtain ⟨p, hp, hp2, V, _, _, _, ρ, -, hρnt, -, hcount⟩ :=
    Walter86.exists_irreducible_chiefFactor_dvd_card_centralizer (X := ↥P) (U := U) (Y := ⊤)
      hUodd hYperf hne
  have : FiniteDimensional (ZMod p) V := Module.Finite.of_finite
  have hρnt' : ∃ h : ↥P, ∃ v : V, ρ h v ≠ v := by
    obtain ⟨h, -, v, hv⟩ := hρnt
    exact ⟨h, v, hv⟩
  have hfaith : ∀ e ∈ E₂, e ≠ 1 → ρ e ≠ 1 := fun e he he1 hρe =>
    he1 (hZinv e (mem_of_representation_eq_one Z ρ hρnt' hρe) (hE₂sq e he))
  have hd : ∀ e ∈ E₂, ∀ e' ∈ E₂, e ≠ 1 → e' ≠ 1 →
      Module.finrank (ZMod p) (LinearMap.ker (ρ e - 1)) =
        Module.finrank (ZMod p) (LinearMap.ker (ρ e' - 1)) := by
    intro e he e' he' he1 he'1
    obtain ⟨g, hg⟩ := hconjP e e' (hE₂sq e he) he1 (hE₂sq e' he') he'1
    rw [← hg, finrank_ker_conj_sub_one]
  have h2p : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    rcases (Nat.dvd_prime Nat.prime_two).mp h' with h1 | h1
    · exact hp.out.one_lt.ne' h1
    · exact hp2 h1
  have hE₂nt : ∃ e ∈ E₂, ρ e ≠ 1 := by
    have h1 : 1 < Nat.card E₂ := by
      rw [hE₂card]
      exact Nat.one_lt_two_pow (by omega)
    have : Nontrivial E₂ := Finite.one_lt_card_iff_nontrivial.mp h1
    obtain ⟨⟨e, he⟩, he1⟩ := exists_ne (1 : E₂)
    have he1' : e ≠ 1 := fun h => he1 (Subtype.ext h)
    exact ⟨e, he, hfaith e he he1'⟩
  refine ⟨p, hp.out, hp2, E₂.map P.subtype, map_subtype_le _, ?_, ?_, ?_⟩
  · refine ⟨isMulCommutative_iff_of_setLike.mpr ?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, (isMulCommutative_iff_of_setLike.mp hE₂ab.1) a ha b hb]
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow, hE₂ab.2 a ha, map_one]
  · rw [card_map_of_injective P.subtype_injective, hE₂card]
  · rintro _ ⟨e, he, rfl⟩ hu1
    have he1 : e ≠ 1 := fun h => hu1 (by rw [h, map_one])
    have hA := RankThree.Classical.card_div_two_sub_one_le_finrank_ker h2p ρ hE₂ab hE₂nt hd he he1
    have hcnt := hcount e (by rw [pow_two]; exact hE₂sq e he)
    have hcen : (⁅U, (⊤ : Subgroup ↥P)⁆ ⊓ centralizer ({e} : Set ↥P)).map P.subtype =
        ⁅oddIn P, P⁆ ⊓ centralizer ({P.subtype e} : Set G) := by
      rw [← hDmap]
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        refine Subgroup.mem_inf.mpr ⟨mem_map_of_mem _ (Subgroup.mem_inf.mp hy).1, ?_⟩
        rw [mem_centralizer_singleton_iff]
        have := mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hy).2
        exact congrArg Subtype.val this
      · intro hx
        obtain ⟨hx1, hyc⟩ := Subgroup.mem_inf.mp hx
        obtain ⟨y, hy, rfl⟩ := hx1
        refine ⟨y, Subgroup.mem_inf.mpr ⟨hy, ?_⟩, rfl⟩
        rw [mem_centralizer_singleton_iff] at hyc ⊢
        exact Subtype.ext hyc
    have hcard : Nat.card ↥(⁅oddIn P, P⁆ ⊓ centralizer ({P.subtype e} : Set G)) =
        Nat.card ↥(⁅U, (⊤ : Subgroup ↥P)⁆ ⊓ centralizer ({e} : Set ↥P)) := by
      rw [← hcen, card_map_of_injective P.subtype_injective]
    rw [hcard]
    have hne0 : Nat.card ↥(⁅U, (⊤ : Subgroup ↥P)⁆ ⊓ centralizer ({e} : Set ↥P)) ≠ 0 :=
      Nat.card_pos.ne'
    have hv := (padicValNat_dvd_iff_le hne0).mp hcnt
    rw [hE₂card] at hA
    have h2 : 2 ^ (2 * m) / 2 = 2 ^ (2 * m - 1) := by
      rw [show 2 * m = (2 * m - 1) + 1 by omega, pow_succ, Nat.mul_div_cancel _ (by norm_num)]
      congr 1
    omega

end Chief

theorem l3TwoPowChiefFixedPoints_holds :
    L3TwoPowChiefFixedPoints :=
  l3TwoPowChiefFixedPoints_of_griess TBLit.griessMultipliersAllModels_holds

section Assembly

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem iInf_oddIn_le_wGroup {A B : Subgroup G} (hBA : B ≤ A) (hB4 : 4 ≤ Nat.card B)
    (hB2 : ∀ b ∈ B, b * b = 1) :
    (⨅ (b : G) (_ : b ∈ B) (_ : b ≠ 1), oddIn (centralizer ({b} : Set G))) ≤ wGroup A :=
  le_iSup_of_le B (le_iSup_of_le hBA (le_iSup_of_le hB4 (le_iSup_of_le hB2 le_rfl)))

theorem pRank_centralizer_le_of_fieldCore
    (hS : SchreierFor Blueprint.Catalog) (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome)
    (hheld : KProperRelativeB.HeldInput) {t : G} {P : Subgroup G}
    {m : ℕ} (hbase : L34BaseSetting G) (ht2 : orderOf t = 2)
    (hPt : P ≤ centralizer ({t} : Set G))
    (hPc : IsPComponent 2 (P.subgroupOf (centralizer ({t} : Set G))))
    (hPn : (P.subgroupOf (centralizer ({t} : Set G))).Normal) (hm : 1 ≤ m)
    (hL : Blueprint.LieModel (↥P ⧸ Open.fusionZStar ↥P) .PSL 3 2 m)
    (hW : ∀ E : Subgroup G, E ≤ centralizer ({t} : Set G) → Open.IsElemAbelian 2 E →
      8 ≤ Nat.card E → wGroup E = ⊥)
    (hD : ⁅oddIn P, P⁆ ≠ ⊥) :
    pRank 2 ↥(centralizer ({t} : Set G)) ≤ 3 * m + 4 := by
  have hA := l3TwoPowAutTwoRank_holds
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hsimple, hnonab, hK, -, -, -, -, -⟩ := hbase
  have : IsSimpleGroup G := hsimple
  set C := centralizer ({t} : Set G) with hC
  have hCN : C ≤ normalizer (P : Set G) := (normal_subgroupOf_iff_le_normalizer hPt).mp hPn
  set φ : ↥C →* MulAut (↥P ⧸ Open.fusionZStar ↥P) :=
    (GSThmB.A10T.zStarAct P).comp (Subgroup.inclusion hCN) with hφ
  have : Finite (MulAut (↥P ⧸ Open.fusionZStar ↥P)) :=
    Finite.of_injective (fun f : MulAut (↥P ⧸ Open.fusionZStar ↥P) =>
      (f : ↥P ⧸ Open.fusionZStar ↥P → ↥P ⧸ Open.fusionZStar ↥P))
      fun f g h => MulEquiv.ext (congrFun h)
  have himg : pRank 2 (↥C ⧸ φ.ker) ≤ 3 * m + 2 := by
    have hinj : Function.Injective ((φ.range.subtype).comp
        (QuotientGroup.quotientKerEquivRange φ).toMonoidHom) :=
      (Subgroup.subtype_injective _).comp (QuotientGroup.quotientKerEquivRange φ).injective
    exact (RankThree.OddKernel.pRank_le_of_injective (by norm_num) _ hinj).trans
      (hA _ m hm hL)
  have hker : pRank 2 ↥φ.ker ≤ 2 := by
    by_contra hlt
    push Not at hlt
    rw [SectionRank.pRank_eq_open_pRank_top] at hlt
    obtain ⟨E, -, hE, hEc⟩ := SectionRank.exists_pRank (p := 2) (by norm_num) (⊤ : Subgroup ↥φ.ker)
    set E' : Subgroup G := (E.map φ.ker.subtype).map C.subtype with hE'
    have hE'C : E' ≤ C := map_subtype_le _
    have hE'card : Nat.card E' = 2 ^ Open.pRank 2 (⊤ : Subgroup ↥φ.ker) := by
      rw [hE', card_map_of_injective C.subtype_injective,
        card_map_of_injective φ.ker.subtype_injective, hEc]
    have hE'ab : Open.IsElemAbelian 2 E' := by
      have h1 := SectionRank.isElemAbelian_map hE φ.ker.subtype
      exact SectionRank.isElemAbelian_map h1 C.subtype
    have hE'8 : 8 ≤ Nat.card E' := by
      rw [hE'card]
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ Open.pRank 2 (⊤ : Subgroup ↥φ.ker) := Nat.pow_le_pow_right (by norm_num) hlt
    have hWE := hW E' hE'C hE'ab hE'8
    have hE'K : ∀ e ∈ E', e ∈ coreActionKernel P := by
      rintro _ ⟨c, ⟨k, hk, rfl⟩, rfl⟩
      have h1 : φ k = 1 := k.2
      have h2 := (GSThmB.A10T.zStarAct_eq_one_iff hPt hPc (Subgroup.inclusion hCN k)).mp h1
      exact h2
    have hcom := oddCore_le_center_of_wGroup_eq_bot hPt hPc hE'C
      (isMulCommutative_iff_of_setLike.mp hE'ab.1)
      (fun x hx => by rw [← pow_two]; exact hE'ab.2 x hx) (by omega)
      (hE'C.trans hCN) (fun e he => GrS5.conj_mem_oddIn_of_mem_coreActionKernel (hE'K e he))
      hWE
      (fun e he he1 => GrS5.commutator_oddCore_pLayer_le hS hU hheld hK ht2 hPt hPc
        ((mem_centralizer_singleton_iff.mp (hE'C he)).symm)
        (GrS5.centralizer_ne_top_of_not_mem_center (GrS5.not_mem_center_of_ne_one hnonab he1)))
      (Or.inr hE'8)
    apply hD
    rw [eq_bot_iff, commutator_le]
    intro x hx l hl
    rw [mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact hcom x hx l hl
  calc pRank 2 ↥C ≤ pRank 2 ↥φ.ker + pRank 2 (↥C ⧸ φ.ker) :=
        RankThree.OddKernel.pRank_le_add_of_normal Nat.prime_two φ.ker
    _ ≤ 2 + (3 * m + 2) := Nat.add_le_add hker himg
    _ = 3 * m + 4 := by ring

theorem eighteen_mul_add_lt_two_pow (m : ℕ) (hm : 4 ≤ m) : 18 * m + 24 < 2 ^ (2 * m - 1) - 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 4 := ⟨m - 4, by omega⟩
  have key : ∀ k : ℕ, 18 * (k + 4) + 25 < 2 ^ (2 * (k + 4) - 1) := by
    intro k
    induction k with
    | zero => norm_num
    | succ n ih =>
      have e : 2 * (n + 1 + 4) - 1 = (2 * (n + 4) - 1) + 2 := by omega
      rw [e, pow_add]
      omega
  have := key k
  omega

theorem l34FieldCoreOfSignalizer_of_parts
    (hS : SchreierFor Blueprint.Catalog) (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome)
    (hheld : KProperRelativeB.HeldInput) (hC : L34ActiveComponentBound)
    (hF : L3TwoPowChiefFixedPoints) :
    L34FieldCoreOfSignalizer := by
  intro G _ _ t P hset hW
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hbase, ht2, hPt, hPc, hPn, m, hm4, -, hL⟩ := hset
  by_contra hD
  have hperf : ⁅P, P⁆ = P := by
    have h1 := ClassicalInvolution.LBalanceProof.isPerfect_of_isPComponent hPc
    have h2 : Group.IsPerfect ↥P :=
      Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hPt).toMonoidHom)
        (subgroupOfEquivOfLe hPt).surjective
    exact Subgroup.isPerfect_iff.mp h2
  have hrank := pRank_centralizer_le_of_fieldCore hS hU hheld hbase ht2 hPt hPc hPn
    (by omega) hL hW hD
  obtain ⟨p, hp, hp2, E, hEP, hEab, hEcard, hEbd⟩ := hF G P m hperf (by omega) hL hD
  have : Fact p.Prime := ⟨hp⟩
  have ht1 : t ≠ 1 := by
    rintro rfl
    simp at ht2
  have htt : t * t = 1 := by rw [← pow_two, ← ht2, pow_orderOf_eq_one]
  obtain ⟨u, huE, hu1, hut⟩ : ∃ u ∈ E, u ≠ 1 ∧ u ≠ t := by
    by_contra hcon
    push Not at hcon
    have hsub : (E : Set G) ⊆ {1, t} := fun x hx => by
      by_cases h1 : x = 1
      · exact Or.inl h1
      · exact Or.inr (hcon x hx h1)
    have h1 : (E : Set G).ncard ≤ ({1, t} : Set G).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 : ({1, t} : Set G).ncard ≤ 2 := by
      refine (Set.ncard_insert_le _ _).trans ?_
      rw [Set.ncard_singleton]
    have h3 : Nat.card E = (E : Set G).ncard := Nat.card_coe_set_eq _
    have h4 : 2 ^ 8 ≤ 2 ^ (2 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have huP : u ∈ P := hEP huE
  have htu : t * u = u * t := (mem_centralizer_singleton_iff.mp (hPt huP)).symm
  have huu : u * u = 1 := by rw [← pow_two]; exact hEab.2 u huE
  have huo : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact huu) hu1
  have htuo : orderOf (t * u) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [pow_two]
      calc t * u * (t * u) = (t * t) * (u * u) := by
            rw [mul_assoc, ← mul_assoc u t u, ← htu]; group
        _ = 1 := by rw [htt, huu, one_mul]
    · intro h
      exact hut (by
        calc u = t * (t * u) := by rw [← mul_assoc, htt, one_mul]
          _ = t := by rw [h, mul_one])
  have hEtwo : IsElemTwo E :=
    ⟨isMulCommutative_iff_of_setLike.mp hEab.1, fun x hx => by rw [← pow_two]; exact hEab.2 x hx⟩
  have htE : ∀ y ∈ E, t * y = y * t := fun y hy =>
    (mem_centralizer_singleton_iff.mp (hPt (hEP hy))).symm
  have hE8 : 8 ≤ Nat.card E := by
    rw [hEcard]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨A, hAC, hAtwo, hA8, htA, hEA⟩ : ∃ A : Subgroup G, A ≤ centralizer ({t} : Set G) ∧
      IsElemTwo A ∧ 8 ≤ Nat.card A ∧ t ∈ A ∧ E ≤ A := by
    by_cases htE' : t ∈ E
    · exact ⟨E, hEP.trans hPt, hEtwo, hE8, htE', le_rfl⟩
    · obtain ⟨hA2, hAcard⟩ := GrS5.elemTwo_zpowers_sup htt hEtwo htE htE'
      refine ⟨zpowers t ⊔ E, sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl))
        (hEP.trans hPt), hA2, by omega, mem_sup_left (mem_zpowers t), le_sup_right⟩
  have hAab : Open.IsElemAbelian 2 A :=
    ⟨isMulCommutative_iff_of_setLike.mpr hAtwo.1, fun x hx => by rw [pow_two]; exact hAtwo.2 x hx⟩
  have hWA : wGroup A = ⊥ := hW A hAC hAab hA8
  have htnu : t ∉ zpowers u := by
    intro h
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp h
    rw [← zpow_mod_orderOf, huo] at hk
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · rw [Nat.cast_ofNat, h0, zpow_zero] at hk
      exact ht1 hk.symm
    · rw [Nat.cast_ofNat, h1, zpow_one] at hk
      exact hut hk
  have htzu : ∀ y ∈ zpowers u, t * y = y * t := fun y hy => by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
    exact (Commute.zpow_right htu k).eq
  obtain ⟨hF2, hFcard⟩ := GrS5.elemTwo_zpowers_sup htt (isElemTwo_zpowers huu) htzu htnu
  have hF4 : 4 ≤ Nat.card ↥(zpowers t ⊔ zpowers u) := by
    rw [hFcard, Nat.card_zpowers, huo]
  have hFA : zpowers t ⊔ zpowers u ≤ A :=
    sup_le (zpowers_le.mpr htA) (zpowers_le.mpr (hEA huE))
  have hΔ := iInf_oddIn_le_wGroup hFA hF4 hF2.2
  rw [hWA] at hΔ
  have hpow2 : ∀ x : G, orderOf x = 2 → ∀ k : ℤ, x ^ k = 1 ∨ x ^ k = x := by
    intro x hx k
    rw [← zpow_mod_orderOf, hx]
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · left
      rw [Nat.cast_ofNat, h0, zpow_zero]
    · right
      rw [Nat.cast_ofNat, h1, zpow_one]
  have hFmem : ∀ b ∈ zpowers t ⊔ zpowers u, b ≠ 1 → b = t ∨ b = u ∨ b = t * u := by
    intro b hb hb1
    obtain ⟨i, h, hh, rfl⟩ := GrS5.mem_zpowers_sup htzu hb
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hh
    rcases hpow2 t ht2 i with hi | hi <;> rcases hpow2 u huo j with hj | hj <;>
      rw [hi, hj] at hb1 ⊢
    · exact absurd (one_mul 1) hb1
    · exact Or.inr (Or.inl (one_mul u))
    · exact Or.inl (mul_one t)
    · exact Or.inr (Or.inr rfl)
  have hΔ' : ∀ y, y ∈ oddIn (centralizer ({t} : Set G)) → y ∈ oddIn (centralizer ({u} : Set G)) →
      y ∈ oddIn (centralizer ({t * u} : Set G)) → y = 1 := by
    intro y h1 h2 h3
    have hy : y ∈ ⨅ (b : G) (_ : b ∈ zpowers t ⊔ zpowers u) (_ : b ≠ 1),
        oddIn (centralizer ({b} : Set G)) := by
      simp only [mem_iInf]
      intro b hb hb1
      rcases hFmem b hb hb1 with rfl | rfl | rfl
      · exact h1
      · exact h2
      · exact h3
    exact mem_bot.mp (hΔ hy)
  set Y := ⁅oddIn P, P⁆ ⊓ centralizer ({u} : Set G) with hYdef
  have hDP : ⁅oddIn P, P⁆ ≤ oddIn P ⊓ P := by
    rw [commutator_le]
    intro a ha b hb
    have haP : a ∈ P := map_subtype_le _ ha
    refine ⟨?_, P.mul_mem (P.mul_mem (P.mul_mem haP hb) (P.inv_mem haP)) (P.inv_mem hb)⟩
    obtain ⟨a', ha', rfl⟩ := ha
    have h1 : (⁅a', ⟨b, hb⟩⁆ : ↥P) ∈ pPrimeCore 2 ↥P :=
      Subgroup.commutator_le_left (pPrimeCore 2 ↥P) ⊤
        (Subgroup.commutator_mem_commutator ha' (mem_top _))
    exact ⟨_, h1, rfl⟩
  have hDt : ⁅oddIn P, P⁆ ≤ oddIn (centralizer ({t} : Set G)) :=
    (hDP.trans inf_le_left).trans (GSLit.map_pPrimeCore_le_of_isPComponent hPt hPc)
  have hYt : Y ≤ oddIn (centralizer ({t} : Set G)) := inf_le_left.trans hDt
  have hYu : Y ≤ centralizer ({u} : Set G) := inf_le_right
  have hYtu : Y ≤ centralizer ({t * u} : Set G) := by
    intro y hy
    have hyt : y * t = t * y := mem_centralizer_singleton_iff.mp
      (hPt ((hDP.trans inf_le_right) (Subgroup.mem_inf.mp hy).1))
    have hyu : y * u = u * y := mem_centralizer_singleton_iff.mp (hYu hy)
    rw [mem_centralizer_singleton_iff]
    calc y * (t * u) = t * (y * u) := by rw [← mul_assoc, hyt, mul_assoc]
      _ = t * u * y := by rw [hyu, mul_assoc]
  set N0 := oddIn (centralizer ({u} : Set G)) with hN0
  set N1 := oddIn (centralizer ({t * u} : Set G)) with hN1
  have htypes : ∀ (a : G) (J : Subgroup G), GSUnbalancingTriple a t J →
      IsL2Type 5 (J ⧸ pPrimeCore 2 J) ∨ IsL2Type 7 (J ⧸ pPrimeCore 2 J) ∨
        IsL34Type (J ⧸ Open.fusionZStar J) := fun a J hJ => hbase.2.2.2.2.2.2.2 a t J hJ
  have hb0 : padicValNat p (N0.relIndex Y) ≤
      3 * pRank 2 ↥(centralizer ({t} : Set G) ⊓ centralizer ({u} : Set G)) :=
    hC G t u ht2 huo htu (htypes u) Y (le_inf hYt hYu) p hp hp2
  have ht_tu : t * (t * u) = (t * u) * t := by rw [mul_assoc, htu, ← mul_assoc]
  have hb1 : padicValNat p (N1.relIndex (N0 ⊓ Y)) ≤
      3 * pRank 2 ↥(centralizer ({t} : Set G) ⊓ centralizer ({t * u} : Set G)) :=
    hC G t (t * u) ht2 htuo ht_tu (htypes (t * u)) (N0 ⊓ Y)
      (le_inf (inf_le_right.trans hYt) (inf_le_right.trans hYtu)) p hp hp2
  have hmono : ∀ a : G, pRank 2 ↥(centralizer ({t} : Set G) ⊓ centralizer ({a} : Set G)) ≤
      pRank 2 ↥(centralizer ({t} : Set G)) := fun a =>
    RankThree.OddKernel.pRank_le_of_injective (by norm_num) (Subgroup.inclusion inf_le_left)
      (Subgroup.inclusion_injective _)
  have hbot : (N1 ⊓ N0) ⊓ Y = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    exact mem_bot.mpr (hΔ' y (hYt hy.2) hy.1.2 hy.1.1)
  have hY : Nat.card Y = N1.relIndex (N0 ⊓ Y) * N0.relIndex Y := by
    rw [Subgroup.relIndex_inf_mul_relIndex, ← Subgroup.inf_relIndex_right, hbot,
      Subgroup.relIndex_bot_left]
  have hY0 : Nat.card Y ≠ 0 := Nat.card_pos.ne'
  have hne1 : N1.relIndex (N0 ⊓ Y) ≠ 0 := fun h => hY0 (by rw [hY, h, zero_mul])
  have hne0 : N0.relIndex Y ≠ 0 := fun h => hY0 (by rw [hY, h, mul_zero])
  have hval : padicValNat p (Nat.card Y) ≤ 6 * (3 * m + 4) := by
    rw [hY, padicValNat.mul hne1 hne0]
    have := hmono u
    have := hmono (t * u)
    omega
  have hlow : 2 ^ (2 * m - 1) - 1 ≤ padicValNat p (Nat.card Y) := hEbd u huE hu1
  have hnum := eighteen_mul_add_lt_two_pow m hm4
  omega

end Assembly

end CFSG.ComponentClassification.GrSLit.L34Sec5S
