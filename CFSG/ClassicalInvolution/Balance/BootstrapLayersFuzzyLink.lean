module

public import CFSG.ClassicalInvolution.Balance.BootstrapLayersFuzzyCanon

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
open CFSG.Assembly.Dichotomy (involutionOddCore)
open CFSG.RankThreeCoreUniqueness.Helpers (finite_perfectResidualOf_isPerfect)
open scoped commutatorElement

section Family

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {a : G}

omit [Finite G] in
theorem conj_eq_of_mem_centralizer_singleton {n : G}
    (hn : n ∈ Subgroup.centralizer ({a} : Set G)) : n * a * n⁻¹ = a := by
  have h := Subgroup.mem_centralizer_singleton_iff.mp hn
  calc n * a * n⁻¹ = a * n * n⁻¹ := by rw [h]
    _ = a := by group

@[expose] def linkMembers (p f : ℕ) [Fact p.Prime] (a : G) : Set (Subgroup G) :=
  {J | (∃ t, IsClassicalMember p f J t) ∧ a ∈ trivialOnQuot J}

@[expose] def residualFamily (a : G) (V : Set (Subgroup G)) : Set (Subgroup G) :=
  {K | ∃ J ∈ V, K = triangleResidual J a}

theorem isSectionMember_triangleResidual {J : Subgroup G} {t : G}
    (hJ : IsClassicalMember p f J t) (ha2 : a * a = 1) (haJ : a ∈ trivialOnQuot J) :
    IsSectionMember p f (Subgroup.centralizer ({a} : Set G)) (triangleResidual J a) t := by
  have h := (axisResidual_single hJ ha2 haJ).isSectionMember hJ
    (finite_perfectResidualOf_isPerfect _)
  simpa only [centralizer_zpowers_eq_singleton'] using h

theorem secData_residualFamily {V : Set (Subgroup G)} (ha2 : a * a = 1) (hne : V.Nonempty)
    (hcls : ∀ J ∈ V, ∃ t, IsClassicalMember p f J t) (hat : ∀ J ∈ V, a ∈ trivialOnQuot J)
    (hconj : ∀ n ∈ Subgroup.centralizer ({a} : Set G), ∀ J ∈ V, conjSub n J ∈ V) :
    SecData p f a (residualFamily a V) := by
  have hmem : ∀ J ∈ V, ∃ t, IsSectionMember p f (Subgroup.centralizer ({a} : Set G))
      (triangleResidual J a) t := fun J hJ => by
    obtain ⟨t, ht⟩ := hcls J hJ
    exact ⟨t, isSectionMember_triangleResidual ht ha2 (hat J hJ)⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨J, hJ⟩ := hne
    exact ⟨triangleResidual J a, J, hJ, rfl⟩
  · rintro K ⟨J, hJ, rfl⟩
    obtain ⟨t, ht⟩ := hmem J hJ
    exact ht.le
  · rintro n hn K ⟨J, hJ, rfl⟩
    exact ⟨conjSub n J, hconj n hn J hJ, (triangleResidual_conjSub J hn).symm⟩
  · rintro K ⟨J, hJ, rfl⟩
    exact hmem J hJ

omit [Finite G] in
theorem triangleResidual_eq_self {M : Subgroup G} (hM : IsClassicalMember p f M a) :
    triangleResidual M a = M := by
  have hMa : M ≤ Subgroup.centralizer ({a} : Set G) := isSubnormal_le hM.subnormal
  have hinf : M ⊓ Subgroup.centralizer ({a} : Set G) = M := inf_eq_left.mpr hMa
  unfold triangleResidual
  rw [hinf]
  exact le_antisymm (Subgroup.map_subtype_le _) (le_perfectResidualOf_of_perfect le_rfl hM.perfect)

theorem mem_trivialOnQuot_iff_centralizes_modOdd {M : Subgroup G} {t : G}
    (hM : IsClassicalMember p f M a) (hq : 5 ≤ p ^ f) (hcan : IsCanonical M a)
    (htC : t ∈ Subgroup.centralizer ({a} : Set G)) :
    t ∈ trivialOnQuot M ↔
      ∀ y ∈ modOdd a M, oddQuotMk a ⟨t, htC⟩ * y = y * oddQuotMk a ⟨t, htC⟩ := by
  refine ⟨fun ht => ?_, mem_trivialOnQuot_of_centralizes_modOdd hM hcan htC⟩
  refine centralizes_modOdd_of_commutator_mem hM hq (I := M) (W := oddCoreIn M)
    (fun x hx => ⟨x, hx, 1, one_mem _, (mul_one x).symm⟩) htC (odd_card_oddCoreIn M)
    (fun m hm => normalizer_oddCoreIn M hm) le_rfl fun m hm => ht.2 m hm

theorem conjSub_mem_linkMembers {n : G} (hn : n ∈ Subgroup.centralizer ({a} : Set G))
    {J : Subgroup G} (hJ : J ∈ linkMembers p f a) : conjSub n J ∈ linkMembers p f a := by
  obtain ⟨⟨t, ht⟩, haJ⟩ := hJ
  refine ⟨⟨n * t * n⁻¹, ht.conj n⟩, ?_⟩
  have h := trivialOnQuot_conjSub haJ n
  rwa [conj_eq_of_mem_centralizer_singleton hn] at h

theorem secData_linkMembers {M : Subgroup G} (hM : IsClassicalMember p f M a) :
    SecData p f a (residualFamily a (linkMembers p f a)) := by
  have cM := isCentralInvolution_of_isClassicalMember hM
  have hMl : M ∈ linkMembers p f a :=
    ⟨⟨a, hM⟩, mem_trivialOnQuot_of_centralizes fun j hj => cM.central j hj⟩
  exact secData_residualFamily cM.sq ⟨M, hMl⟩ (fun J hJ => hJ.1) (fun J hJ => hJ.2)
    fun n hn J hJ => conjSub_mem_linkMembers hn hJ

end Family

section Dichotomy

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Φ : Set (Subgroup G)} {a : G}

namespace SecData

variable (hs : SecData p f a Φ) {K K' : Subgroup G}
include hs

omit [Finite G] in
theorem modOdd_perfect (hK : K ∈ Φ) : ⁅modOdd a K, modOdd a K⁆ = modOdd a K := by
  obtain ⟨z, hz⟩ := hs.member K hK
  exact modOdd_perfect_of_perfect (hs.le K hK) hz.perfect

theorem modOdd_ne_bot (hK : K ∈ Φ) : modOdd a K ≠ ⊥ := by
  obtain ⟨z, hz⟩ := hs.member K hK
  have c := hz.isCentralInvolution
  exact modOdd_ne_bot_of_involution hz.mem (hs.le K hK) c.sq c.ne_one

theorem eq_of_le (D' : LieDecomposition (memberImages Φ a) (memberJoin Φ a)) (hK : K ∈ Φ)
    {i j : D'.ι} (hi : modOdd a K ≤ D'.Q i) (hj : modOdd a K ≤ D'.Q j) : i = j := by
  by_contra hij
  refine hs.modOdd_ne_bot hK ?_
  have hcomm : ⁅modOdd a K, modOdd a K⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro x hx y hy
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact D'.commute i j hij x (hi hx) y (hj hy)
  rw [← hs.modOdd_perfect hK, hcomm]

theorem exists_unique_component (D' : LieDecomposition (memberImages Φ a) (memberJoin Φ a))
    (hK : K ∈ Φ) : ∃! i : D'.ι, modOdd a K ≤ D'.Q i := by
  obtain ⟨i, hi⟩ := D'.exists_le (modOdd a K) ⟨K, ⟨hK, hs.le K hK⟩, rfl⟩
  exact ⟨i, hi, fun j hj => hs.eq_of_le D' hK hj hi⟩

omit [Finite G] in
theorem commutator_mem_oddCore (D' : LieDecomposition (memberImages Φ a) (memberJoin Φ a))
    (hK : K ∈ Φ) (hK' : K' ∈ Φ) {i j : D'.ι} (hij : i ≠ j) (hi : modOdd a K ≤ D'.Q i)
    (hj : modOdd a K' ≤ D'.Q j) : ∀ x ∈ K, ∀ y ∈ K', ⁅x, y⁆ ∈ involutionOddCore a := by
  intro x hx y hy
  rw [involutionOddCore_eq_oddCoreIn]
  have hxC := hs.le K hK hx
  have hyC := hs.le K' hK' hy
  exact (mk_comm_eq_iff (Y := Subgroup.centralizer ({a} : Set G)) hxC hyC).mp
    (D'.commute i j hij _ (hi (oddQuotMk_mem_modOdd hx hxC)) _
      (hj (oddQuotMk_mem_modOdd hy hyC)))

theorem exists_fundamental (D : LocalLieSystemAt p f Φ a) (hK : K ∈ Φ) :
    ∃ (j : Fin D.card) (R : Subgroup (compModel D j).K),
      R ∈ fundamentalSubgroups (D.tag j) (compModel D j).D ∧
        R.map (secComponentHom hs.normalizes D j) = modOdd a K := by
  have hM : K ∈ centMembers Φ a := ⟨hK, hs.le K hK⟩
  set Y := centralizingLayer Φ {a} with hY
  have hMY : K ≤ Y := le_centralizingLayer hM
  have hMfam : modOddIn Y K ∈ localFamily Φ a := ⟨K.subgroupOf Y, ⟨K, hM, hMY, rfl⟩, rfl⟩
  obtain ⟨i, R, hR, hMR⟩ := D.fundamental _ hMfam
  refine ⟨i, R, hR, ?_⟩
  have h1 : (R.map (D.hom i)).map (sectionQuotientHom hs.normalizes) =
      R.map (secComponentHom hs.normalizes D i) := Subgroup.map_map _ _ _
  rw [← h1, ← hMR]
  exact map_sectionQuotientHom_modOddIn hs.normalizes hM

theorem eq_of_map_eq (D : LocalLieSystemAt p f Φ a) (hK : K ∈ Φ) {i j : Fin D.card}
    {R : Subgroup (compModel D i).K} {R' : Subgroup (compModel D j).K}
    (hR : R.map (secComponentHom hs.normalizes D i) = modOdd a K)
    (hR' : R'.map (secComponentHom hs.normalizes D j) = modOdd a K) : i = j := by
  have hM : K ∈ centMembers Φ a := ⟨hK, hs.le K hK⟩
  have hθ := sectionQuotientHom_injective hs.normalizes
  have hmap := map_sectionQuotientHom_modOddIn hs.normalizes hM
  refine eq_of_modOdd_le_map_range_sec hs D hM (i := i) (j := j) ?_ ?_
  · have h1 : (R.map (D.hom i)).map (sectionQuotientHom hs.normalizes) =
        R.map (secComponentHom hs.normalizes D i) := Subgroup.map_map _ _ _
    have h2 : R.map (D.hom i) = modOddIn (centralizingLayer Φ {a}) K :=
      Subgroup.map_injective hθ (h1.trans (hR.trans hmap.symm))
    exact h2 ▸ Subgroup.map_le_range _ _
  · rw [← hR']
    have : (secComponentHom hs.normalizes D j).range =
        (D.hom j).range.map (sectionQuotientHom hs.normalizes) := MonoidHom.range_comp _ _
    rw [← this]
    exact Subgroup.map_le_range _ _

theorem commutator_mem_oddCore_of_fundamental (D : LocalLieSystemAt p f Φ a) {i j : Fin D.card}
    (hij : i ≠ j) (hK : K ∈ Φ) (hK' : K' ∈ Φ) {R : Subgroup (compModel D i).K}
    {R' : Subgroup (compModel D j).K}
    (hR : R.map (secComponentHom hs.normalizes D i) = modOdd a K)
    (hR' : R'.map (secComponentHom hs.normalizes D j) = modOdd a K') :
    ∀ x ∈ K, ∀ y ∈ K', ⁅x, y⁆ ∈ involutionOddCore a := by
  intro x hx y hy
  rw [involutionOddCore_eq_oddCoreIn]
  have hxC := hs.le K hK hx
  have hyC := hs.le K' hK' hy
  have h1 : oddQuotMk a ⟨x, hxC⟩ ∈ R.map (secComponentHom hs.normalizes D i) :=
    hR ▸ oddQuotMk_mem_modOdd hx hxC
  have h2 : oddQuotMk a ⟨y, hyC⟩ ∈ R'.map (secComponentHom hs.normalizes D j) :=
    hR' ▸ oddQuotMk_mem_modOdd hy hyC
  obtain ⟨r, -, hrx⟩ := Subgroup.mem_map.mp h1
  obtain ⟨r', -, hry⟩ := Subgroup.mem_map.mp h2
  refine (mk_comm_eq_iff (Y := Subgroup.centralizer ({a} : Set G)) hxC hyC).mp ?_
  show oddQuotMk a ⟨x, hxC⟩ * oddQuotMk a ⟨y, hyC⟩ =
    oddQuotMk a ⟨y, hyC⟩ * oddQuotMk a ⟨x, hxC⟩
  rw [← hrx, ← hry]
  have key := D.commute i j hij r r'
  exact (map_mul (sectionQuotientHom hs.normalizes) (D.hom i r) (D.hom j r')).symm.trans
    ((congrArg (sectionQuotientHom hs.normalizes) key).trans
      (map_mul (sectionQuotientHom hs.normalizes) (D.hom j r') (D.hom i r)))

end SecData

end Dichotomy

section Component

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Φ : Set (Subgroup G)} {a : G}

theorem centralizes_of_commutator_mem_center_of_perfect {K : Type*} [Group K] {R : Subgroup K}
    (hR : ⁅R, R⁆ = R) {s : K} (hs : ∀ q ∈ R, ⁅s, q⁆ ∈ Subgroup.center K) :
    ∀ q ∈ R, s * q = q * s := by
  have hperf : Group.IsPerfect ↥R := Subgroup.isPerfect_iff.mpr hR
  let φ : ↥R →* ↥(Subgroup.center K) :=
    { toFun := fun q => ⟨⁅s, (q : K)⁆, hs q q.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun a b => by
        apply Subtype.ext
        show ⁅s, (a : K) * (b : K)⁆ = ⁅s, (a : K)⁆ * ⁅s, (b : K)⁆
        have hb := Subgroup.mem_center_iff.mp (hs b b.2) (a : K)
        calc ⁅s, (a : K) * (b : K)⁆ = ⁅s, (a : K)⁆ * ((a : K) * ⁅s, (b : K)⁆ * (a : K)⁻¹) := by
              simp only [commutatorElement_def]
              group
          _ = ⁅s, (a : K)⁆ * ⁅s, (b : K)⁆ := by rw [hb]; group }
  have hker : commutator ↥R ≤ φ.ker := Abelianization.commutator_subset_ker φ
  intro q hq
  have hmem : (⟨q, hq⟩ : ↥R) ∈ φ.ker := hker (by rw [hperf.commutator_eq_top]; trivial)
  have h1 : ⁅s, q⁆ = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hmem)
  exact commutatorElement_eq_one_iff_mul_comm.mp h1

theorem SecData.commutator_mem_oddCore_iff (hs : SecData p f a Φ) (D : LocalLieSystemAt p f Φ a)
    (j : Fin D.card) {K K' : Subgroup G} (hK : K ∈ Φ) (hK' : K' ∈ Φ)
    {R R' : Subgroup (compModel D j).K}
    (hR : R.map (secComponentHom hs.normalizes D j) = modOdd a K)
    (hR' : R'.map (secComponentHom hs.normalizes D j) = modOdd a K') (hRp : ⁅R, R⁆ = R) :
    (∀ x ∈ K, ∀ y ∈ K', ⁅x, y⁆ ∈ involutionOddCore a) ↔ Commutes R R' := by
  set ψ := secComponentHom hs.normalizes D j with hψ
  set C : Subgroup G := Subgroup.centralizer ({a} : Set G) with hC
  constructor
  · intro h r hr r' hr'
    have himg : ∀ r ∈ R, ∀ r' ∈ R', ψ r * ψ r' = ψ r' * ψ r := by
      intro r hr r' hr'
      have h1 : ψ r ∈ modOdd a K := hR ▸ Subgroup.mem_map_of_mem ψ hr
      have h2 : ψ r' ∈ modOdd a K' := hR' ▸ Subgroup.mem_map_of_mem ψ hr'
      obtain ⟨x, hx, hxr⟩ := mem_modOdd_iff.mp h1
      obtain ⟨y, hy, hyr⟩ := mem_modOdd_iff.mp h2
      rw [← hxr, ← hyr]
      refine (mk_comm_eq_iff (Y := C) x.2 y.2).mpr ?_
      have := h (x : G) hx (y : G) hy
      rw [involutionOddCore_eq_oddCoreIn] at this
      exact this
    have hcen : ∀ q ∈ R, ⁅r', q⁆ ∈ Subgroup.center (compModel D j).K := by
      intro q hq
      refine secComponentHom_ker_le_center hs.normalizes D j ?_
      rw [MonoidHom.mem_ker, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (himg q hq r' hr').symm
    exact (centralizes_of_commutator_mem_center_of_perfect hRp hcen r hr).symm
  · intro h x hx y hy
    have hxC := hs.le K hK hx
    have hyC := hs.le K' hK' hy
    have h1 : oddQuotMk a ⟨x, hxC⟩ ∈ R.map ψ := hR ▸ oddQuotMk_mem_modOdd hx hxC
    have h2 : oddQuotMk a ⟨y, hyC⟩ ∈ R'.map ψ := hR' ▸ oddQuotMk_mem_modOdd hy hyC
    obtain ⟨r, hr, hrx⟩ := Subgroup.mem_map.mp h1
    obtain ⟨r', hr', hry⟩ := Subgroup.mem_map.mp h2
    rw [involutionOddCore_eq_oddCoreIn]
    refine (mk_comm_eq_iff (Y := C) hxC hyC).mp ?_
    show oddQuotMk a ⟨x, hxC⟩ * oddQuotMk a ⟨y, hyC⟩ =
      oddQuotMk a ⟨y, hyC⟩ * oddQuotMk a ⟨x, hxC⟩
    rw [← hrx, ← hry, ← map_mul, ← map_mul, h r hr r' hr']

end Component

section Frame

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem exists_axisTriangle_of_residuals_commute_indep {M J N : Subgroup G} {a t u : G}
    (hM : IsClassicalMember p f M a) (hJ : IsClassicalMember p f J t)
    (hN : IsClassicalMember p f N u) (hq : 5 ≤ p ^ f) (hJcan : IsCanonical J t)
    (hNcan : IsCanonical N u) (htM : t ∈ trivialOnQuot M) (huM : u ∈ trivialOnQuot M)
    (haJ : a ∈ trivialOnQuot J) (haN : a ∈ trivialOnQuot N)
    (hJN : ∀ i ∈ triangleResidual J a, ∀ j ∈ triangleResidual N a,
      ⁅i, j⁆ ∈ involutionOddCore a)
    (hind : ∀ x ∈ involutionOddCore a, x * u * x⁻¹ ∉ ({a, t, a * t} : Set G)) :
    ∃ x ∈ involutionOddCore a, AxisTriangle p f M J (conjSub x N) a t (x * u * x⁻¹) ∧
      a ≠ x * u * x⁻¹ ∧ t ≠ x * u * x⁻¹ ∧ a * t ≠ x * u * x⁻¹ := by
  obtain ⟨x, hx, hT⟩ := exists_axisTriangle_of_residuals_commute hM hJ hN hq hJcan hNcan htM huM
    haJ haN hJN
  refine ⟨x, hx, hT, fun h => hind x hx ?_, fun h => hind x hx ?_, fun h => hind x hx ?_⟩
  · rw [← h]
    simp
  · rw [← h]
    simp
  · rw [← h]
    simp

omit [Finite G] in
theorem oddQuotMk_conj_of_mem_oddCoreIn {a x u : G}
    (hx : x ∈ oddCoreIn (Subgroup.centralizer ({a} : Set G)))
    (hu : u ∈ Subgroup.centralizer ({a} : Set G))
    (hxu : x * u * x⁻¹ ∈ Subgroup.centralizer ({a} : Set G)) :
    oddQuotMk a ⟨x * u * x⁻¹, hxu⟩ = oddQuotMk a ⟨u, hu⟩ := by
  have hxC : x ∈ Subgroup.centralizer ({a} : Set G) := oddCoreIn_le _ hx
  have hx1 : oddQuotMk a ⟨x, hxC⟩ = 1 := oddQuotMk_eq_one_of_mem_oddCoreIn hx hxC
  have e : (⟨x * u * x⁻¹, hxu⟩ : ↥(Subgroup.centralizer ({a} : Set G))) =
      ⟨x, hxC⟩ * ⟨u, hu⟩ * ⟨x, hxC⟩⁻¹ := rfl
  rw [e, map_mul, map_mul, map_inv, hx1]
  simp

omit [Finite G] in
theorem conj_notMem_of_oddQuotMk_ne {a t u : G} (haC : a ∈ Subgroup.centralizer ({a} : Set G))
    (htC : t ∈ Subgroup.centralizer ({a} : Set G)) (huC : u ∈ Subgroup.centralizer ({a} : Set G))
    (hua : oddQuotMk a ⟨u, huC⟩ ≠ oddQuotMk a ⟨a, haC⟩)
    (hut : oddQuotMk a ⟨u, huC⟩ ≠ oddQuotMk a ⟨t, htC⟩)
    (huat : oddQuotMk a ⟨u, huC⟩ ≠ oddQuotMk a ⟨a, haC⟩ * oddQuotMk a ⟨t, htC⟩) :
    ∀ x ∈ involutionOddCore a, x * u * x⁻¹ ∉ ({a, t, a * t} : Set G) := by
  intro x hx hmem
  rw [involutionOddCore_eq_oddCoreIn] at hx
  have hxC : x ∈ Subgroup.centralizer ({a} : Set G) := oddCoreIn_le _ hx
  have hxu : x * u * x⁻¹ ∈ Subgroup.centralizer ({a} : Set G) :=
    mul_mem (mul_mem hxC huC) (inv_mem hxC)
  have key := oddQuotMk_conj_of_mem_oddCoreIn hx huC hxu
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h | h | h
  · refine hua (key.symm.trans ?_)
    simp only [h]
  · refine hut (key.symm.trans ?_)
    simp only [h]
  · refine huat (key.symm.trans ?_)
    have hat' : a * t ∈ Subgroup.centralizer ({a} : Set G) := mul_mem haC htC
    have e : oddQuotMk a ⟨x * u * x⁻¹, hxu⟩ = oddQuotMk a ⟨a * t, hat'⟩ := by
      simp only [h]
    rw [e]
    exact map_mul (oddQuotMk a) ⟨a, haC⟩ ⟨t, htC⟩

end Frame

end CFSG.ClassicalInvolution.Balance.Bootstrap
