module

public import CFSG.LocalAnalysis.EvenBN.Sp4.OneAxisNormalizer
public import CFSG.LocalAnalysis.EvenBN.Sp4.OneAxisHalfFixed
public import CFSG.LocalAnalysis.SteinbergSFOneAxisElementaryOvergroup
public import CFSG.LocalAnalysis.SteinbergSFOneAxisLocalFusion

public section

namespace CFSG.LocalAnalysis.EvenBN.Sp4

open Subgroup
open CFSG.LocalAnalysis.SymplecticFourStandard
open GomiFusion RootAxisTwoCore OneAxisRadical OneAxisSecond OneAxisHeisenberg
  OneAxisRadicalStructure OneAxisSecondAxis OneAxisWeakClosure
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis CFSG.QuasithinUnique.Fin257

section Model

variable {K : Type} [Field K] [CharP K 2]

theorem axisOne_eq_rootU : axisOne K = rootU K Axis.one :=
  Subgroup.ext fun _ => Iff.rfl

theorem axisTwo_eq_rootU : axisTwo K = rootU K Axis.two :=
  Subgroup.ext fun _ => Iff.rfl

omit [CharP K 2] in
theorem dSp_inv_mem_diagTorus (r s : Kˣ) : Sp4.dSp r⁻¹ s⁻¹ ∈ diagTorus K :=
  ⟨r, s, r.ne_zero, s.ne_zero, by
    rw [Sp4.glMat_dSp]
    simp [Sp4.dSpMat, diagMat]⟩

end Model

namespace OneAxisData

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2] {n : ℕ}
  {φ : L ≃* antiSp K} {TG : Subgroup G} {t : G} {M : Subgroup G}

theorem conj_eq_mul_of_mem_centralizer [Finite G] [Finite K]
    (hO : CFSG.Open.standardComponentOddCore G = ⊥) (hLn : ¬ L.Normal)
    (h : OneAxisData L K n φ TG t M) {g : G} (hgC : g⁻¹ * t * g ∈ centralizer ({t} : Set G)) :
    ∃ l ∈ L, ∃ c ∈ centralizer (L : Set G), g⁻¹ * t * g = l * c := by
  have hS := h.heis.hyp.setup
  have hax : {x : G | ∃ m ∈ normalizer ((pull φ (antiUnipotent K) ⊔ TG : Subgroup G) : Set G),
        x = m⁻¹ * t * m} = {x | ∃ u ∈ pull φ (axisOne K), x = t * u} ∨
      {x : G | ∃ m ∈ normalizer ((pull φ (antiUnipotent K) ⊔ TG : Subgroup G) : Set G),
        x = m⁻¹ * t * m} = {x | ∃ u ∈ pull φ (axisTwo K), x = t * u} :=
    Or.inl (by rw [axisOne_eq_rootU]; exact h.heis.hyp.axis)
  obtain ⟨l, hlL, -, c, hc, hlc⟩ := OneAxisFusion.exists_of_inner hS hgC
    (OneAxisFusion.act_inner hS hO hLn
      (fun w hw h4 h2 k => OneAxisFusion.not_conj_sq hS hax hw h4 h2 k) hgC)
  exact ⟨l, hlL, c, hS.T_le hc, hlc⟩

theorem slice_normalizer [Finite G] [Finite K]
    (hO : CFSG.Open.standardComponentOddCore G = ⊥) (hLn : ¬ L.Normal)
    (h : OneAxisData L K n φ TG t M) (g : G)
    (hg : g⁻¹ * t * g ∈ normalizer (h.T₁ : Set G)) :
    ∃ s ∈ h.V₁, g⁻¹ * t * g = s⁻¹ * t * s := by
  have hS := h.heis.hyp.setup
  by_cases hgT : g⁻¹ * t * g ∈ h.T₁
  · have hmem : g⁻¹ * t * g ∈ {x : G | ∃ g : G, x = g⁻¹ * t * g} ∩ (h.T₁ : Set G) :=
      ⟨⟨g, rfl⟩, hgT⟩
    rw [h.class_slice] at hmem
    exact hmem
  exfalso
  obtain ⟨hTeq, -⟩ := h.T₁_eq
  have hxx : (g⁻¹ * t * g) ^ 2 = 1 := by
    rw [pow_two, show g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g by group, h.t_mul_t]
    group
  obtain ⟨hev, v, d, -, hvC, hv2, hv1, -, hfrob, hw, -, -, -, -, -, -, -, hvd, -⟩ :=
    symplectic_normalizer_quotient_field_involution_representative h.heis.sec.two.two_le
      h.heis.sec.two.card_K L φ t (by rw [pow_two]; exact h.t_mul_t) hS.t_not_mem_L
      (hS.T_le hS.t_mem) hS.cent_le (by rw [inf_comm]; exact h.heis.sec.two.cent_inf) h.V₁
      (fun r s => h.torus_le_normalizer_V₁ (symm_mem_pull.mpr (dSp_inv_mem_diagTorus r s)))
      (by rw [h.V₁_inf_centralizer, pull_eq_map])
      (by rw [← hTeq]; exact h.class_slice)
      (by rw [h.closure_orbit_eq, pull_eq_map]; rfl)
      (g⁻¹ * t * g) (by rw [← hTeq]; exact hg) (h.normalizer_T₁_le hg)
      (by rw [← hTeq]; exact hgT) (by rw [hxx]; exact one_mem _)
  obtain ⟨-, hv₀V, hv₀C, hv₀L⟩ := hw (d⁻¹ * v * d) (Set.mem_insert_of_mem _ rfl)
  have hv₀2 : (d⁻¹ * v * d) ^ 2 = 1 := by
    rw [pow_two, show d⁻¹ * v * d * (d⁻¹ * v * d) = d⁻¹ * (v * v) * d by group, ← pow_two, hv2]
    group
  have hv₀1 : d⁻¹ * v * d ≠ 1 := fun h1 => hv1 (by
    rw [show v = d * (d⁻¹ * v * d) * d⁻¹ by group, h1]
    group)
  have hhalf := (one_axis_half_fixed_series h hev (orderOf_eq_prime hv₀2 hv₀1) hv₀C hv₀V
    hfrob).1
  have hy : d⁻¹ * (g⁻¹ * t * g) * d ∈
      {x : G | (∃ w ∈ h.V₁, x = d⁻¹ * v * d * w) ∧ orderOf x = 2} := by
    refine ⟨⟨(d⁻¹ * v * d)⁻¹ * (d⁻¹ * (g⁻¹ * t * g) * d), ?_, by group⟩, ?_⟩
    · rw [show (d⁻¹ * v * d)⁻¹ * (d⁻¹ * (g⁻¹ * t * g) * d) =
        ((d⁻¹ * (g⁻¹ * t * g) * d)⁻¹ * (d⁻¹ * v * d))⁻¹ by group]
      exact inv_mem hvd
    · have e := MulEquiv.orderOf_eq (MulAut.conj (g * d)⁻¹) t
      rw [MulAut.conj_apply, inv_inv] at e
      rw [show d⁻¹ * (g⁻¹ * t * g) * d = (g * d)⁻¹ * t * (g * d) by group, e, hS.order_t]
  rw [hhalf] at hy
  obtain ⟨w, -, hyw⟩ := hy
  have hv₀conj : d⁻¹ * v * d = (g * d * w⁻¹)⁻¹ * t * (g * d * w⁻¹) := by
    rw [show d⁻¹ * v * d = w * (d⁻¹ * (g⁻¹ * t * g) * d) * w⁻¹ by rw [hyw]; group]
    group
  obtain ⟨l, hlL, c, hc, hlc⟩ :=
    h.conj_eq_mul_of_mem_centralizer hO hLn (g := g * d * w⁻¹) (hv₀conj ▸ hv₀C)
  exact hv₀L ⟨l, hlL, c, hc, hv₀conj.trans hlc⟩

theorem false_of_perfect [Finite G] [Finite K] [Group.IsPerfect G]
    (hO : CFSG.Open.standardComponentOddCore G = ⊥) (hLn : ¬ L.Normal)
    (h : OneAxisData L K n φ TG t M) : False := by
  have hS := h.heis.hyp.setup
  obtain ⟨R, hR⟩ := exists_sylow_pull (G := G) φ
  have hQ : pull φ (antiUnipotent K) ⊔ zpowers t = pull φ (antiUnipotent K) ⊔ TG := by
    rw [h.heis.hyp.T_eq]
  refine false_of_slice hS.order_t hS.cent_le ⟨R, hR⟩ h.isPGroup_T₁ (hQ ▸ le_sup_left)
    h.V₁_le_T₁ ?_ (h.slice_normalizer hO hLn) h.t_not_mem_V₁
    fun W hW hTW hWN => h.isMulCommutative_quot hW hTW hWN
  rw [hQ]
  exact inf_le_right.trans h.normalizer_Q_le

end OneAxisData

section Minor

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem map_minorAut_antiUnipotent :
    (antiUnipotent K).map (minorAut K).toMonoidHom = antiUnipotent K := by
  have hle : (antiUnipotent K).map (minorAut K).toMonoidHom ≤ antiUnipotent K := by
    rintro _ ⟨x, hx, rfl⟩
    exact SymplecticFourOuterSquare.minorAut_mem_antiUnipotent hx
  exact eq_of_le_of_card_ge hle
    (by rw [card_map_of_injective (f := (minorAut K).toMonoidHom) (minorAut K).injective])

theorem comap_minorAut_rootU_one :
    (rootU K Axis.one).comap (minorAut K).toMonoidHom = rootU K Axis.two := by
  change (rootU₁ K).comap (minorAut K).toMonoidHom = rootU₂ K
  rw [rootU₁_eq_map,
    comap_map_eq_self_of_injective (f := (minorAut K).toMonoidHom) (minorAut K).injective]

theorem one_axis_minor_transport {G : Type} [Group G] {L : Subgroup G} (φ : L ≃* antiSp K)
    {P : Subgroup L} (hφP : P.map φ.toMonoidHom = antiUnipotent K) :
    P.map (φ.trans (minorAut K)).toMonoidHom = antiUnipotent K ∧
      ((rootU K Axis.one).comap (φ.trans (minorAut K)).toMonoidHom).map L.subtype =
        ((rootU K Axis.two).comap φ.toMonoidHom).map L.subtype := by
  have e : (φ.trans (minorAut K)).toMonoidHom = (minorAut K).toMonoidHom.comp φ.toMonoidHom :=
    rfl
  refine ⟨?_, ?_⟩
  · rw [e, ← map_map, hφP, map_minorAut_antiUnipotent]
  · rw [e, ← comap_comap, comap_minorAut_rootU_one]

end Minor

theorem false_of_one_axis_one_of_perfect {G : Type} [Group G]
    [Finite G] [Group.IsPerfect G] (hO : CFSG.Open.standardComponentOddCore G = ⊥)
    {L : Subgroup G} (hL : CFSG.Open.standardComponentIsStandard L) (hLn : ¬ L.Normal)
    {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ n)
    (T : Sylow 2 (centralizer (L : Set G)))
    (hT : IsCyclic (T : Subgroup (centralizer (L : Set G))))
    {t : centralizer (L : Set G)} (htT : t ∈ T) (ht : orderOf t = 2)
    (hcore : CFSG.Open.standardComponentOddCore (centralizer ({(t : G)} : Set G)) = ⊥)
    (P : Sylow 2 L) (φ : L ≃* antiSp K)
    (hφP : (P : Subgroup L).map φ.toMonoidHom = antiUnipotent K) :
    let TG := (T : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype
    let PG := (P : Subgroup L).map L.subtype
    let Q := PG ⊔ TG
    let U₁ := ((rootU K Axis.one).comap φ.toMonoidHom).map L.subtype
    {x : G | ∃ m ∈ normalizer (Q : Set G), x = m⁻¹ * t * m} = {x | ∃ u ∈ U₁, x = t * u} →
      False := by
  intro TG PG Q U₁ hone
  obtain ⟨⟨M, hM⟩, hall⟩ := standard_symplectic_four_one_axis_elementary_overgroup_normalizer
    hO hL hLn hn hK T hT htT ht hcore P φ hφP hone
  obtain ⟨hMab, -, -, -, -, -, -, -, ⟨hM₁eq, -, hM₁ab, hM₁card, -, hM₁S, hM₁D, -⟩, -⟩ := hall M hM
  obtain ⟨hMD, hMJ, hMcard, hZM, -⟩ := hM
  rw [hM₁eq] at hM₁ab hM₁card hM₁S hM₁D
  obtain ⟨hM₁n, hM₁t, hM₁sup⟩ := hM₁D
  exact (OneAxisData.of_standard hO hL hLn hn hK T hT htT ht hcore P φ hφP M hone hMJ hMD hMab
    hMcard hZM hM₁ab hM₁card hM₁S ⟨le_sup_left.trans hM₁sup.le, hM₁n, hM₁t, hM₁sup⟩
    ).false_of_perfect hO hLn

theorem false_of_one_axis_of_perfect {G : Type} [Group G]
    [Finite G] [Group.IsPerfect G] (hO : CFSG.Open.standardComponentOddCore G = ⊥)
    {L : Subgroup G} (hL : CFSG.Open.standardComponentIsStandard L) (hLn : ¬ L.Normal)
    {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ n)
    (T : Sylow 2 (centralizer (L : Set G)))
    (hT : IsCyclic (T : Subgroup (centralizer (L : Set G))))
    {t : centralizer (L : Set G)} (htT : t ∈ T) (ht : orderOf t = 2)
    (hcore : CFSG.Open.standardComponentOddCore (centralizer ({(t : G)} : Set G)) = ⊥)
    (P : Sylow 2 L) (φ : L ≃* antiSp K)
    (hφP : (P : Subgroup L).map φ.toMonoidHom = antiUnipotent K) :
    let TG := (T : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype
    let PG := (P : Subgroup L).map L.subtype
    let Q := PG ⊔ TG
    let U₁ := ((rootU K Axis.one).comap φ.toMonoidHom).map L.subtype
    let U₂ := ((rootU K Axis.two).comap φ.toMonoidHom).map L.subtype
    ({x : G | ∃ m ∈ normalizer (Q : Set G), x = m⁻¹ * t * m} = {x | ∃ u ∈ U₁, x = t * u} ∨
      {x : G | ∃ m ∈ normalizer (Q : Set G), x = m⁻¹ * t * m} = {x | ∃ u ∈ U₂, x = t * u}) →
      False := by
  intro TG PG Q U₁ U₂ hone
  rcases hone with h1 | h2
  · exact false_of_one_axis_one_of_perfect hO hL hLn hn hK T hT htT ht hcore P φ hφP h1
  · obtain ⟨hφP', hU⟩ := one_axis_minor_transport φ hφP
    exact false_of_one_axis_one_of_perfect hO hL hLn hn hK T hT htT ht hcore P
      (φ.trans (minorAut K)) hφP' (by rw [hU]; exact h2)

theorem false_of_one_axis {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] {L : Subgroup G} (hL : CFSG.Open.standardComponentIsStandard L)
    {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ n)
    (T : Sylow 2 (centralizer (L : Set G)))
    (hT : IsCyclic (T : Subgroup (centralizer (L : Set G))))
    {t : centralizer (L : Set G)} (htT : t ∈ T) (ht : orderOf t = 2)
    (hcore : CFSG.Open.standardComponentOddCore (centralizer ({(t : G)} : Set G)) = ⊥)
    (P : Sylow 2 L) (φ : L ≃* antiSp K)
    (hφP : (P : Subgroup L).map φ.toMonoidHom = antiUnipotent K) :
    let TG := (T : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype
    let PG := (P : Subgroup L).map L.subtype
    let Q := PG ⊔ TG
    let U₁ := ((rootU K Axis.one).comap φ.toMonoidHom).map L.subtype
    let U₂ := ((rootU K Axis.two).comap φ.toMonoidHom).map L.subtype
    ({x : G | ∃ m ∈ normalizer (Q : Set G), x = m⁻¹ * t * m} = {x | ∃ u ∈ U₁, x = t * u} ∨
      {x : G | ∃ m ∈ normalizer (Q : Set G), x = m⁻¹ * t * m} = {x | ∃ u ∈ U₂, x = t * u}) →
      False := by
  intro TG PG Q U₁ U₂ hone
  have hS := setup_of_standard hL hn hK φ T hT htT ht hcore
  have hLn : ¬ L.Normal := by
    intro hN
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal L with hbot | htop
    · have h1 : ((φ.symm (uElt 1 0 0 0) : L) : G) = 1 :=
        (eq_bot_iff_forall L).mp hbot _ (φ.symm (uElt 1 0 0 0)).2
      rw [OneAxisFusion.coe_symm_eq_one_iff, ← uElt_zero_eq_one] at h1
      exact one_ne_zero (uElt_inj h1).1
    · exact hS.t_not_mem_L ((eq_top_iff' L).mp htop _)
  have hperf : Group.IsPerfect G := by
    refine Group.isPerfect_def.2 ?_
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) with hc | hc
    · exfalso
      have hcomm : ∀ a b : G, a * b = b * a := fun a b => by
        rw [← commutatorElement_eq_one_iff_mul_comm, ← mem_bot, ← hc, _root_.commutator_def]
        exact commutator_mem_commutator (mem_top a) (mem_top b)
      exact hLn ⟨fun l hl g => by rw [hcomm g l, mul_inv_cancel_right]; exact hl⟩
    · exact hc
  have hO : CFSG.Open.standardComponentOddCore G = ⊥ := by
    refine sSup_eq_bot.mpr fun N hN => ?_
    obtain ⟨hNn, hodd⟩ := hN
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hb | htop
    · exact hb
    · exfalso
      rw [htop, card_top] at hodd
      have h2 : 2 ∣ Nat.card G := hS.order_t ▸ orderOf_dvd_natCard (t : G)
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  exact false_of_one_axis_of_perfect hO hL hLn hn hK T hT htT ht hcore P φ hφP hone

end CFSG.LocalAnalysis.EvenBN.Sp4
