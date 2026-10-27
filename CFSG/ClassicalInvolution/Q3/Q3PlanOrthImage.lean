module

public import CFSG.ClassicalInvolution.Q3.Q3PlanOrthChain
public import CFSG.ClassicalInvolution.SmallOrth.Orth3Split
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.SubnormalPSubgroupLeQCore
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthLift

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open
open scoped MatrixGroups commutatorElement

section Abstract

variable {G : Type*} [Group G]

theorem isSubnormal_unary_of_isSubnormal {X J : Subgroup G} (hX : IsSubnormal X J) :
    (X.subgroupOf J).IsSubnormal :=
  hX.subgroupOf

theorem centralizes_of_isSubnormal_pGroup [Finite G] {J X B : Subgroup G} (hXJ : X ≤ J)
    (hBJ : B ≤ J) (hBn : ∀ g ∈ J, ∀ b ∈ B, g * b * g⁻¹ ∈ B) (hsub : IsSubnormal X J)
    (hX : IsPGroup 3 X)
    (hB : ∀ N : Subgroup G, N ≤ B → (∀ g ∈ J, ∀ n ∈ N, g * n * g⁻¹ ∈ N) → IsPGroup 3 N →
      N = ⊥) :
    ∀ x ∈ X, ∀ b ∈ B, x * b = b * x := by
  set D := CFSG.GorensteinWalter.qCoreOf J 3 with hD
  have hXD : X ≤ D := CFSG.GorensteinWalter.le_qCoreOf_of_isSubnormal_isPGroup J X 3 hXJ
    (isSubnormal_unary_of_isSubnormal hsub) hX
  have hDn : CFSG.GorensteinWalter.IsNormalIn D J := CFSG.GorensteinWalter.qCoreOf_normal_in J 3
  have hDp : IsPGroup 3 D := CFSG.GorensteinWalter.qCoreOf_isPGroup J 3
  have hDB : D ⊓ B = ⊥ := by
    refine hB (D ⊓ B) inf_le_right (fun g hg n hn => ⟨hDn.2 g hg n hn.1, hBn g hg n hn.2⟩) ?_
    exact hDp.to_le inf_le_left
  intro x hx b hb
  have hxD' : x ∈ D := hXD hx
  have hxJ : x ∈ J := hXJ hx
  have hbJ : b ∈ J := hBJ hb
  have hmem : x * b * x⁻¹ * b⁻¹ ∈ D ⊓ B := by
    refine ⟨?_, ?_⟩
    · have h1 : b * x⁻¹ * b⁻¹ ∈ D := hDn.2 b hbJ x⁻¹ (D.inv_mem hxD')
      have : x * b * x⁻¹ * b⁻¹ = x * (b * x⁻¹ * b⁻¹) := by group
      rw [this]
      exact D.mul_mem hxD' h1
    · exact B.mul_mem (hBn x hxJ b hb) (B.inv_mem hb)
  rw [hDB, Subgroup.mem_bot] at hmem
  exact commutatorElement_eq_one_iff_commute.mp hmem

end Abstract

section Orth

open CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalGroups.Orthogonal
  CFSG.ClassicalGroups.Orthogonal.Small QuadraticMap

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}
  {i : V ≃ₗ[F] V}

theorem conj_mem_nP {g n : V ≃ₗ[F] V} (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hg : g * i = i * g) (hn : n ∈ nP Q i) : g * n * g⁻¹ ∈ nP Q i := by
  obtain ⟨hnO, hnc, hnf⟩ := hn
  refine ⟨mul_mem (mul_mem hgO hnO) (inv_mem hgO), ?_, fun v hv => ?_⟩
  · calc g * n * g⁻¹ * i = g * n * (g⁻¹ * i) := by group
      _ = g * n * (i * g⁻¹) := by rw [inv_mul_eq_mul_inv_of hg]
      _ = g * (n * i) * g⁻¹ := by group
      _ = g * (i * n) * g⁻¹ := by rw [hnc]
      _ = (g * i) * n * g⁻¹ := by group
      _ = (i * g) * n * g⁻¹ := by rw [hg]
      _ = i * (g * n * g⁻¹) := by group
  · have hv' : g⁻¹ v ∈ minusSp i := map_mem_minusSp (inv_mul_eq_mul_inv_of hg) hv
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hnf _ hv']
    exact LinearEquiv.apply_inv_apply' g v

theorem minusSp_eq_bot_of_mem_nP (h2 : (2 : F) ≠ 0) (h : i ∈ nP Q i) : minusSp i = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun v hv => ?_
  have h1 : i v = v := h.2.2 v hv
  have h2' : i v = -v := mem_minusSp.mp hv
  have : (2 : F) • v = 0 := by
    rw [two_smul]
    calc v + v = v + -(-v) := by rw [neg_neg]
      _ = -(-v) + v := add_comm _ _
      _ = 0 := by rw [← h2', h1]; exact neg_add_cancel _
  exact (smul_eq_zero.mp this).resolve_left h2

section Block

open CFSG.LocalAnalysis.ComponentInitial

variable (Q) in
@[expose] noncomputable def plusBlockSub (hc : IsCompl (plusSp i) (minusSp i)) :
    Subgroup (V ≃ₗ[F] V) :=
  (elementaryGroup (Q.comp (plusSp i).subtype)).map (orthExtend hc)

theorem mem_plusBlockSub {hc : IsCompl (plusSp i) (minusSp i)} {b : V ≃ₗ[F] V} :
    b ∈ plusBlockSub Q hc ↔
      ∃ φ ∈ elementaryGroup (Q.comp (plusSp i).subtype), orthExtend hc φ = b :=
  Subgroup.mem_map

theorem plusBlockSub_fix {hc : IsCompl (plusSp i) (minusSp i)} {b : V ≃ₗ[F] V}
    (hb : b ∈ plusBlockSub Q hc) {v : V} (hv : v ∈ minusSp i) : b v = v := by
  obtain ⟨φ, -, rfl⟩ := mem_plusBlockSub.mp hb
  have := orthExtend_apply hc φ 0 ⟨v, hv⟩
  simpa using this

theorem plusBlockSub_comm {hc : IsCompl (plusSp i) (minusSp i)} {b : V ≃ₗ[F] V}
    (hb : b ∈ plusBlockSub Q hc) : b * i = i * b := by
  obtain ⟨φ, -, rfl⟩ := mem_plusBlockSub.mp hb
  have hW : i ∈ stabSub (plusSp i) := mem_stabSub_plusSp rfl
  have hW' : i ∈ stabSub (minusSp i) := mem_stabSub_minusSp rfl
  exact (commute_orthExtend_of_commute hc hW hW' (by
    rw [resHom_plusSp hW, one_mul, mul_one])).symm

variable {hc : IsCompl (plusSp i) (minusSp i)}

theorem plusBlockSub_mem_orthogonalGroup
    (horth : ∀ u ∈ plusSp i, ∀ w ∈ minusSp i, polar Q u w = 0) {b : V ≃ₗ[F] V}
    (hb : b ∈ plusBlockSub Q hc) : b ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  obtain ⟨φ, hφ, rfl⟩ := mem_plusBlockSub.mp hb
  exact (orthogonal_complement_elementary_embedding Q hc horth).2.1 φ
    (elementaryGroup_le_orthogonalGroup _ hφ)

theorem plusBlockSub_le_nP (horth : ∀ u ∈ plusSp i, ∀ w ∈ minusSp i, polar Q u w = 0) :
    plusBlockSub Q hc ≤ nP Q i := fun _ hb =>
  ⟨plusBlockSub_mem_orthogonalGroup horth hb, plusBlockSub_comm hb,
    fun _ hv => plusBlockSub_fix hb hv⟩

theorem plusBlockSub_le (h3 : (3 : F) = 0)
    (horth : ∀ u ∈ plusSp i, ∀ w ∈ minusSp i, polar Q u w = 0) {T : Subgroup (V ≃ₗ[F] V)}
    (hT3 : ∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, g * i = i * g → g ^ 3 = 1 → g ∈ T) :
    plusBlockSub Q hc ≤ T := by
  rw [plusBlockSub, Subgroup.map_le_iff_le_comap]
  refine elementaryGroup_le_of_eichler_mem fun u w _ _ => ?_
  rw [Subgroup.mem_comap]
  have hmem : orthExtend hc (eichler (Q.comp (plusSp i).subtype) u w) ∈ plusBlockSub Q hc :=
    ⟨_, eichler_mem_elementaryGroup _ u w, rfl⟩
  refine hT3 _ (plusBlockSub_mem_orthogonalGroup horth hmem) (plusBlockSub_comm hmem) ?_
  rw [← map_pow, Small.eichler_pow_three h3, map_one]

theorem conj_mem_plusBlockSub {g : V ≃ₗ[F] V} (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hg : g * i = i * g) {b : V ≃ₗ[F] V} (hb : b ∈ plusBlockSub Q hc) :
    g * b * g⁻¹ ∈ plusBlockSub Q hc := by
  obtain ⟨φ, hφ, rfl⟩ := mem_plusBlockSub.mp hb
  have hW := mem_stabSub_plusSp hg
  have hW' := mem_stabSub_minusSp hg
  refine ⟨resHom (plusSp i) ⟨g, hW⟩ * φ * (resHom (plusSp i) ⟨g, hW⟩)⁻¹,
    conj_mem_elementaryGroup (resHom_mem_orthogonalGroup hgO hW) hφ, ?_⟩
  exact (conj_orthExtend hc hW hW' φ).symm

theorem eq_bot_of_normal_pGroup_le_plusBlockSub [Finite F] [FiniteDimensional F V]
    (hF : Nat.card F = 3) (hQ : (polarBilin Q).Nondegenerate)
    (horth : ∀ u ∈ plusSp i, ∀ w ∈ minusSp i, polar Q u w = 0) {J N : Subgroup (V ≃ₗ[F] V)}
    (hBJ : plusBlockSub Q hc ≤ J) (hN : N ≤ plusBlockSub Q hc)
    (hNn : ∀ g ∈ J, ∀ n ∈ N, g * n * g⁻¹ ∈ N) (hN3 : IsPGroup 3 N) : N = ⊥ := by
  have hQ' := nondegenerate_comp_subtype hQ hc horth
  let f : ↥(elementaryGroup (Q.comp (plusSp i).subtype)) →* (V ≃ₗ[F] V) :=
    (orthExtend hc).comp (elementaryGroup (Q.comp (plusSp i).subtype)).subtype
  have hfinj : Function.Injective f :=
    (orthogonal_complement_elementary_embedding Q hc horth).1.comp Subtype.val_injective
  let N' : Subgroup ↥(elementaryGroup (Q.comp (plusSp i).subtype)) := N.comap f
  have hfmem : ∀ φ : ↥(elementaryGroup (Q.comp (plusSp i).subtype)), f φ ∈ plusBlockSub Q hc :=
    fun φ => ⟨φ.1, φ.2, rfl⟩
  have : N'.Normal := ⟨fun ψ hψ φ => by
    show f (φ * ψ * φ⁻¹) ∈ N
    rw [map_mul, map_mul, map_inv]
    exact hNn _ (hBJ (hfmem φ)) _ hψ⟩
  have hodd : Odd (Nat.card N') := by
    have : Finite V := Module.finite_of_finite F
    have : Finite (V ≃ₗ[F] V) :=
      Finite.of_injective (fun g : V ≃ₗ[F] V => (g : V → V)) DFunLike.coe_injective
    obtain ⟨k, hk⟩ := hN3.exists_card_eq
    have hd : Nat.card N' ∣ Nat.card N := by
      rw [← Subgroup.card_map_of_injective hfinj]
      exact Subgroup.card_dvd_of_le (Subgroup.map_comap_le f N)
    rw [hk] at hd
    exact Odd.of_dvd_nat (Odd.pow (by decide)) hd
  have hbot := eq_bot_of_odd_normal_of_card_three hF hQ' N' hodd
  rw [eq_bot_iff]
  intro n hn
  obtain ⟨φ, hφ, rfl⟩ := mem_plusBlockSub.mp (hN hn)
  have hφ' : (⟨φ, hφ⟩ : ↥(elementaryGroup (Q.comp (plusSp i).subtype))) ∈ N' := hn
  rw [hbot, Subgroup.mem_bot] at hφ'
  have : φ = 1 := congrArg Subtype.val hφ'
  rw [Subgroup.mem_bot, this, map_one]

end Block

section Core

open CFSG.ComponentClassification.CatalogueBOddQuadratic CFSG.LocalAnalysis.ComponentInitial

variable {hc : IsCompl (plusSp i) (minusSp i)}

theorem blockP_eq_self (h2 : (2 : F) ≠ 0) (hii : i * i = 1)
    {g : ↥(TauCeti.QuadraticMap.orthogonalGroup Q ⊓
      Subgroup.centralizer ({i} : Set (V ≃ₗ[F] V)))} (hg : (g : V ≃ₗ[F] V) ∈ nP Q i) :
    blockP h2 hii g = g := by
  refine LinearEquiv.ext fun x => ?_
  obtain ⟨u, hu, v, hv, rfl⟩ := exists_add_eq h2 hii x
  have hgc : (g : V ≃ₗ[F] V) * i = i * g := comm_of_mem_centralizer g.2.2
  change blockEquiv h2 hii g.1 hgc (u + v) = g.1 (u + v)
  rw [blockEquiv_apply_add h2 hii hgc hu hv, map_add, hg.2.2 v hv]

theorem range_le_nM_of_isSubnormal [Finite F] [FiniteDimensional F V] (hF : Nat.card F = 3)
    (hQ : (polarBilin Q).Nondegenerate) (hi : i ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hii : i * i = 1) (hV : minusSp i ≠ ⊥) (φ : SL(2, ZMod 3) →* (V ≃ₗ[F] V))
    (hφinj : Function.Injective φ) (hφO : ∀ g, φ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hφc : ∀ g, φ g * i = i * φ g) (hφi : φ (-1) = i) {T : Subgroup (V ≃ₗ[F] V)}
    (hsub : IsSubnormal φ.range T)
    (hTC : T ≤ TauCeti.QuadraticMap.orthogonalGroup Q ⊓ Subgroup.centralizer ({i} : Set _))
    (hT3 : ∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, g * i = i * g → g ^ 3 = 1 → g ∈ T)
    (hTE : T ≤ elementaryGroup Q) : φ.range ≤ nM Q i := by
  obtain ⟨h3, h2⟩ := three_eq_zero_two_ne_zero_of_card_eq_three hF
  have hc := isCompl_plusSp_minusSp h2 hii
  have horth : ∀ u ∈ plusSp i, ∀ w ∈ minusSp i, polar Q u w = 0 :=
    fun u hu w hw => polar_plusSp_minusSp h2 hi hu hw
  have : Finite V := Module.finite_of_finite F
  have : Finite (V ≃ₗ[F] V) :=
    Finite.of_injective (fun g : V ≃ₗ[F] V => (g : V → V)) DFunLike.coe_injective
  have hφC : ∀ g, φ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q ⊓
      Subgroup.centralizer ({i} : Set (V ≃ₗ[F] V)) := fun g =>
    ⟨hφO g, Subgroup.mem_centralizer_singleton_iff.mpr (hφc g)⟩
  let P₀ : SL(2, ZMod 3) →* (V ≃ₗ[F] V) :=
    (blockP h2 hii).comp (φ.codRestrict _ hφC)
  let M₀ : SL(2, ZMod 3) →* (V ≃ₗ[F] V) :=
    (blockM h2 hii).comp (φ.codRestrict _ hφC)
  have hP₀nP : ∀ g, P₀ g ∈ nP Q i := fun g => blockP_mem_nP h2 hii hi ⟨φ g, hφC g⟩
  have hM₀nM : ∀ g, M₀ g ∈ nM Q i := fun g => blockM_mem_nM h2 hii hi ⟨φ g, hφC g⟩
  have hPM : ∀ g, P₀ g * M₀ g = φ g := fun g => blockP_mul_blockM h2 hii ⟨φ g, hφC g⟩
  have hAT : φ.range ≤ T := CFSG.ClassicalInvolution.isSubnormal_le hsub
  have hP₀T : ∀ g, P₀ g ∈ T := by
    intro g
    obtain ⟨a, b, c, ha, hb, hc', rfl⟩ := sl2Three_exists_cubes g
    have key : ∀ x : SL(2, ZMod 3), x ^ 3 = 1 → P₀ x ∈ T := fun x hx =>
      hT3 _ (hP₀nP x).1 (hP₀nP x).2.1 (by rw [← map_pow, hx, map_one])
    rw [map_mul, map_mul]
    exact T.mul_mem (T.mul_mem (key a ha) (key b hb)) (key c hc')
  have hYA : sl2ThreeQ8.map P₀ ≤ φ.range := by
    refine le_of_isSubnormal_commutator (X := P₀.range) hsub ?_ ?_ ?_
    · rintro _ ⟨q, -, rfl⟩
      exact hP₀T q
    · rintro _ ⟨g, rfl⟩
      refine ⟨M₀ g, fun y hy => ?_, ?_⟩
      · obtain ⟨q, -, rfl⟩ := hy
        exact nP_comm_nM h2 hii (hP₀nP q) (hM₀nM g)
      · rw [hPM]
        exact ⟨g, rfl⟩
    · have h1 := Subgroup.map_mono (f := P₀) sl2ThreeQ8_le_commutator
      rwa [Subgroup.map_commutator, ← MonoidHom.range_eq_map] at h1
  have hq8 : ∀ q ∈ sl2ThreeQ8, P₀ q = 1 := by
    intro q hq
    by_contra hne
    let e : SL(2, ZMod 3) ≃* φ.range := MonoidHom.ofInjective hφinj
    have hmemN : P₀ q ∈ φ.range ⊓ nP Q i := ⟨hYA ⟨q, hq, rfl⟩, hP₀nP q⟩
    have hnorm : ∀ g ∈ φ.range, ∀ n ∈ φ.range ⊓ nP Q i, g * n * g⁻¹ ∈ φ.range ⊓ nP Q i := by
      rintro _ ⟨a, rfl⟩ n ⟨hnA, hnP⟩
      have hgA : φ a ∈ φ.range := ⟨a, rfl⟩
      exact ⟨φ.range.mul_mem (φ.range.mul_mem hgA hnA) (φ.range.inv_mem hgA),
        conj_mem_nP (hφO a) (hφc a) hnP⟩
    have hneg := neg_one_mem_of_normal e inf_le_left hnorm hmemN hne
    have hie : ((e (-1) : φ.range) : V ≃ₗ[F] V) = i := by
      rw [← hφi]
      rfl
    rw [hie] at hneg
    exact hV (minusSp_eq_bot_of_mem_nP h2 hneg.2)
  have hP₀cube : ∀ g, P₀ g ^ 3 = 1 := fun g => by
    rw [← map_pow]
    exact hq8 _ (pow_three_mem_sl2ThreeQ8 g)
  have hX3 : IsPGroup 3 P₀.range := by
    intro x
    obtain ⟨g, hg⟩ := x.2
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hg]
    exact hP₀cube g
  have hB'T : plusBlockSub Q hc ≤ T := plusBlockSub_le h3 horth hT3
  have hB'P : plusBlockSub Q hc ≤ nP Q i := plusBlockSub_le_nP horth
  have hX'T : P₀.range ≤ T := by
    rintro _ ⟨g, rfl⟩
    exact hP₀T g
  let π : ↥T →* (V ≃ₗ[F] V) := (blockP h2 hii).comp (Subgroup.inclusion hTC)
  have hsubT : IsSubnormal (φ.range.subgroupOf T) ⊤ := by
    have := CFSG.ClassicalInvolution.isSubnormal_subgroupOf hsub T
    rwa [Subgroup.subgroupOf_self] at this
  have hmapX : (φ.range.subgroupOf T).map π = P₀.range := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨g, hg⟩ := Subgroup.mem_subgroupOf.mp ht
      refine ⟨g, ?_⟩
      have : (φ.codRestrict _ hφC g) = Subgroup.inclusion hTC t := Subtype.ext hg
      show blockP h2 hii (φ.codRestrict _ hφC g) = blockP h2 hii (Subgroup.inclusion hTC t)
      rw [this]
    · rintro ⟨g, rfl⟩
      exact ⟨⟨φ g, hAT ⟨g, rfl⟩⟩, Subgroup.mem_subgroupOf.mpr ⟨g, rfl⟩, rfl⟩
  have hsubX : IsSubnormal P₀.range π.range := by
    have := CFSG.ComponentClassification.Components.chain_map π hsubT
    rwa [hmapX, ← MonoidHom.range_eq_map] at this
  have hJle : P₀.range ⊔ plusBlockSub Q hc ≤ π.range := by
    refine sup_le ?_ ?_
    · rw [← hmapX]
      exact Subgroup.map_le_range _ _
    · intro b hb
      refine ⟨⟨b, hB'T hb⟩, ?_⟩
      exact blockP_eq_self h2 hii (g := ⟨b, hTC (hB'T hb)⟩) (hB'P hb)
  have hsubJ : IsSubnormal P₀.range (P₀.range ⊔ plusBlockSub Q hc) := by
    have := CFSG.ClassicalInvolution.ModelFacts.isSubnormal_inf hsubX hJle
    rwa [inf_eq_left.mpr le_sup_left] at this
  have hnormP : ∀ x ∈ nP Q i,
      x ∈ Subgroup.normalizer ((plusBlockSub Q hc : Subgroup (V ≃ₗ[F] V)) : Set (V ≃ₗ[F] V)) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro b
    refine ⟨fun hb => conj_mem_plusBlockSub hx.1 hx.2.1 hb, fun hb => ?_⟩
    have hxi : x⁻¹ * i = i * x⁻¹ := inv_mul_eq_mul_inv_of hx.2.1
    have := conj_mem_plusBlockSub (inv_mem hx.1) hxi hb
    simpa [mul_assoc] using this
  have hBn : ∀ g ∈ P₀.range ⊔ plusBlockSub Q hc, ∀ b ∈ plusBlockSub Q hc,
      g * b * g⁻¹ ∈ plusBlockSub Q hc := by
    have hJN : P₀.range ⊔ plusBlockSub Q hc ≤
        Subgroup.normalizer ((plusBlockSub Q hc : Subgroup (V ≃ₗ[F] V)) : Set (V ≃ₗ[F] V)) := by
      refine sup_le ?_ Subgroup.le_normalizer
      rintro _ ⟨g, rfl⟩
      exact hnormP _ (hP₀nP g)
    intro g hg b hb
    exact (Subgroup.mem_normalizer_iff.mp (hJN hg) b).mp hb
  have hcommX := centralizes_of_isSubnormal_pGroup le_sup_left le_sup_right hBn hsubJ hX3
    (fun N hN hNn hN3 =>
      eq_bot_of_normal_pGroup_le_plusBlockSub hF hQ horth le_sup_right hN hNn hN3)
  have hP₀one : ∀ g, P₀ g = 1 := by
    intro g
    have hxX : P₀ g ∈ P₀.range := ⟨g, rfl⟩
    have hxE : P₀ g ∈ elementaryGroup Q := hTE (hX'T hxX)
    have hxc : P₀ g * i = i * P₀ g := (hP₀nP g).2.1
    have hW := mem_stabSub_plusSp hxc
    have hW' := mem_stabSub_minusSp hxc
    obtain ⟨e, he⟩ := exists_pow_res_eq_one (ν := ⟨P₀ g, hxE⟩) hF hQ hc horth hW hW'
      (fun φ' => Subtype.ext (hcommX _ hxX (orthExtend hc φ'.1) ⟨φ'.1, φ'.2, rfl⟩).symm)
    have hr3 : resHom (plusSp i) ⟨P₀ g, hW⟩ ^ 3 = 1 := by
      rw [← map_pow]
      have : (⟨P₀ g, hW⟩ : stabSub (plusSp i)) ^ 3 = 1 := Subtype.ext (by
        simpa using hP₀cube g)
      rw [this, map_one]
    have hr1 : resHom (plusSp i) ⟨P₀ g, hW⟩ = 1 := by
      have := (pow_gcd_eq_one (a := resHom (plusSp i) ⟨P₀ g, hW⟩) (m := 3) (n := 2 ^ e)).mpr
        ⟨hr3, he⟩
      rwa [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right e (by decide)), pow_one] at this
    refine LinearEquiv.ext fun y => ?_
    obtain ⟨u, hu, v, hv, rfl⟩ := exists_add_eq h2 hii y
    have hxu : P₀ g u = u := by
      have := congrArg (fun r : plusSp i ≃ₗ[F] plusSp i => (r ⟨u, hu⟩ : V)) hr1
      simpa [resHom_apply] using this
    rw [map_add, hxu, (hP₀nP g).2.2 v hv]
    rfl
  rintro _ ⟨g, rfl⟩
  rw [← hPM g, hP₀one g, one_mul]
  exact hM₀nM g

end Core

end Orth

end CFSG.ClassicalInvolution.Q3
