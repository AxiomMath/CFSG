module

public import CFSG.LocalAnalysis.ComponentClassification.LBalanceAssemblySections
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoSylow
import CFSG.GroupTheory.PRankQuotientLift
import CFSG.GroupTheory.PGroup.PrimePartTransport
import CFSG.LocalAnalysis.SectionRank.GroupRankTransport
import CFSG.GH74.GLS.AssemblyComponents
import CFSG.GroupTheory.PerfectActionCritical
import CFSG.GH74.GLS.Stage2.Final.Thm6.L203Core

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section8

open Subgroup

private theorem simple_factor_data {G : Type*} [Group G] [Finite G] {V : Subgroup G}
    (hVn : V.Normal) (hVne : V ≠ ⊥)
    (hVmin : ∀ K : Subgroup G, K.Normal → K ≤ V → K = ⊥ ∨ K = V)
    (h3V : 3 ∣ Nat.card V) (hnot : ¬ IsSimpleGroup V) :
    ∃ (r : ℕ) (S : Fin r → Subgroup G) (e : ((i : Fin r) → S i) ≃* V)
      (he : ∀ (i : Fin r) (x : (j : Fin r) → S j),
        (∀ j : Fin r, j ≠ i → x j = 1) → (e x : G) = x i)
      (i0 i1 : Fin r), i0 ≠ i1 ∧ (∀ i : Fin r, 3 ∣ Nat.card (S i)) := by
  classical
  obtain ⟨r, S, hr1, hSle, hSsimple, hSconj, hSnorm, e, he⟩ :=
    CFSG.LocalCores.minimal_normal_simple_factors hVn hVne hVmin
  let j0 : Fin r := ⟨0, by omega⟩
  have hr2 : 2 ≤ r := by
    rcases Nat.lt_or_ge r 2 with h | h
    · exfalso
      have hr1' : r = 1 := by omega
      subst hr1'
      have hS0 : IsSimpleGroup (S (default : Fin 1)) := hSsimple default
      have hpi : ((i : Fin 1) → S i) ≃* S (default : Fin 1) :=
        MulEquiv.piUnique (fun i : Fin 1 => S i)
      exact hnot ((MulEquiv.isSimpleGroup_congr (hpi.symm.trans e)).mp hS0)
    · exact h
  let i0 : Fin r := ⟨0, by omega⟩
  let i1 : Fin r := ⟨1, by omega⟩
  have hi : i0 ≠ i1 := by
    intro h
    exact (by decide : (0 : ℕ) ≠ 1) (congrArg Fin.val h)
  have hcardV : Nat.card V = ∏ i, Nat.card (S i) := by
    rw [← Nat.card_congr e.toEquiv, Nat.card_pi]
  have hcard_eq (i : Fin r) : Nat.card (S i) = Nat.card (S j0) := by
    obtain ⟨g, hg⟩ := hSconj i j0
    rw [hg, show CFSG.conjugate (S i) g = (S i).map (MulAut.conj g⁻¹).toMonoidHom from rfl,
      Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
  have h3prod : 3 ∣ ∏ i, Nat.card (S i) := by
    rw [← hcardV]
    exact h3V
  have hprod_eq : ∏ i, Nat.card (S i) = (Nat.card (S j0)) ^ r := by
    rw [Finset.prod_congr rfl (fun i _ => hcard_eq i), Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
  have h3pow : 3 ∣ (Nat.card (S j0)) ^ r := by
    rw [← hprod_eq]
    exact h3prod
  have h3S0 : 3 ∣ Nat.card (S j0) := Nat.prime_three.dvd_of_dvd_pow h3pow
  have h3Si (i : Fin r) : 3 ∣ Nat.card (S i) := by
    rw [hcard_eq i]
    exact h3S0
  exact ⟨r, S, e, he, i0, i1, hi, h3Si⟩

private theorem factor_order_three_data {G : Type*} [Group G] [Finite G]
    {r : ℕ} {S : Fin r → Subgroup G} {V : Subgroup G}
    {e : ((i : Fin r) → S i) ≃* V}
    {he : ∀ (i : Fin r) (x : (j : Fin r) → S j),
      (∀ j : Fin r, j ≠ i → x j = 1) → (e x : G) = x i}
    {i0 i1 : Fin r} (hi : i0 ≠ i1) (h3Si : ∀ i : Fin r, 3 ∣ Nat.card (S i)) :
    ∃ (a : S i0) (b : S i1),
      Commute (a : G) (b : G) ∧ S i0 ⊓ S i1 = ⊥ ∧ orderOf a = 3 ∧ orderOf b = 3 := by
  classical
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := S i0) 3 (h3Si i0)
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := S i1) 3 (h3Si i1)
  have hcomm : Commute (a : G) (b : G) := by
    let xa : (i : Fin r) → S i := Pi.mulSingle (M := fun i : Fin r => S i) i0 a
    let xb : (i : Fin r) → S i := Pi.mulSingle (M := fun i : Fin r => S i) i1 b
    have hx : Commute xa xb := by
      have h := Pi.mulSingle_commute (f := fun i : Fin r => ↥(S i)) hi a b
      simpa only [xa, xb] using h
    have hxa : (∀ j, j ≠ i0 → xa j = 1) := by
      intro j hj
      simp [xa, hj]
    have hxb : (∀ j, j ≠ i1 → xb j = 1) := by
      intro j hj
      simp [xb, hj]
    have hxa' : (e xa : G) = (a : G) := by
      simpa [xa, Pi.mulSingle_eq_same] using he i0 xa hxa
    have hxb' : (e xb : G) = (b : G) := by
      simpa [xb, Pi.mulSingle_eq_same] using he i1 xb hxb
    have hEqV : e xa * e xb = e xb * e xa := by
      rw [← map_mul, ← map_mul, hx.eq]
    have hval := congrArg Subtype.val hEqV
    exact (commute_iff_eq _ _).2 (by simpa [hxa', hxb'] using hval)
  have hinter : S i0 ⊓ S i1 = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have hy0 : y ∈ S i0 := hy.1
    have hy1 : y ∈ S i1 := hy.2
    let y0 : S i0 := ⟨y, hy0⟩
    let y1 : S i1 := ⟨y, hy1⟩
    let x0 : (i : Fin r) → S i := Pi.mulSingle (M := fun i : Fin r => S i) i0 y0
    let x1 : (i : Fin r) → S i := Pi.mulSingle (M := fun i : Fin r => S i) i1 y1
    have hx0 : (∀ j, j ≠ i0 → x0 j = 1) := by
      intro j hj
      simp [x0, hj]
    have hx1 : (∀ j, j ≠ i1 → x1 j = 1) := by
      intro j hj
      simp [x1, hj]
    have he0 : (e x0 : G) = y := by
      simpa [x0, y0, Pi.mulSingle_eq_same] using he i0 x0 hx0
    have he1 : (e x1 : G) = y := by
      simpa [x1, y1, Pi.mulSingle_eq_same] using he i1 x1 hx1
    have hEq : e x0 = e x1 := Subtype.ext (he0.trans he1.symm)
    have hxy : x0 = x1 := e.injective hEq
    have hcoord := congrFun hxy i0
    have hx0i0 : x0 i0 = y0 := by
      simp [x0]
    have hx1i0 : x1 i0 = 1 := by
      simp [x1, hi]
    have hy1' : y0 = 1 := by
      rw [← hx0i0, hcoord, hx1i0]
    simpa [y0] using congrArg Subtype.val hy1'
  exact ⟨a, b, hcomm, hinter, ha, hb⟩

private theorem pRank_two_of_factor_data {G : Type*} [Group G] [Finite G]
    {r : ℕ} {S : Fin r → Subgroup G} {V : Subgroup G}
    {e : ((i : Fin r) → S i) ≃* V}
    {he : ∀ (i : Fin r) (x : (j : Fin r) → S j),
      (∀ j : Fin r, j ≠ i → x j = 1) → (e x : G) = x i}
    {i0 i1 : Fin r} (hi : i0 ≠ i1) (h3Si : ∀ i : Fin r, 3 ∣ Nat.card (S i)) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup G) := by
  classical
  obtain ⟨a, b, hcomm, hinter, ha, hb⟩ :=
    factor_order_three_data (V := V) (e := e) (he := he) (i0 := i0) (i1 := i1) hi h3Si
  have hind : ∀ i j : ℤ, (a : G) ^ i * (b : G) ^ j = 1 → (3 : ℤ) ∣ i ∧ (3 : ℤ) ∣ j := by
    intro i j hij
    have hai : (a : G) ^ i ∈ S i0 := Subgroup.zpow_mem (S i0) a.2 i
    have hbj : (b : G) ^ j ∈ S i1 := Subgroup.zpow_mem (S i1) b.2 j
    have hainv : ((b : G) ^ j)⁻¹ ∈ S i1 := (S i1).inv_mem hbj
    have haeq : (a : G) ^ i = ((b : G) ^ j)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one]
      exact hij
    have ha1 : (a : G) ^ i = 1 := by
      have hmem : (a : G) ^ i ∈ (⊥ : Subgroup G) := by
        rw [← hinter]
        exact ⟨hai, haeq ▸ hainv⟩
      exact Subgroup.mem_bot.mp hmem
    have hb1 : (b : G) ^ j = 1 := by
      have h := hij
      rw [ha1, one_mul] at h
      exact h
    have haL : orderOf (a : G) = 3 := by
      rw [Subgroup.orderOf_coe, ha]
    have hbL : orderOf (b : G) = 3 := by
      rw [Subgroup.orderOf_coe, hb]
    have hi3 : (3 : ℤ) ∣ i := by
      rwa [zpow_eq_one_iff_modEq, Int.modEq_zero_iff_dvd, haL] at ha1
    have hj3 : (3 : ℤ) ∣ j := by
      rwa [zpow_eq_one_iff_modEq, Int.modEq_zero_iff_dvd, hbL] at hb1
    exact ⟨hi3, hj3⟩
  have ha3 : (a : G) ^ 3 = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, Subgroup.orderOf_coe, ha]
  have hb3 : (b : G) ^ 3 = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, Subgroup.orderOf_coe, hb]
  have h2 := CFSG.two_le_pRank_of_commute_independent Nat.prime_three hcomm ha3 hb3 hind
  rwa [CFSG.SectionRank.pRank_eq_open_pRank_top] at h2

private theorem isSimpleGroup_of_minimal_normal {G : Type*} [Group G] [Finite G]
    {V : Subgroup G} (hVn : V.Normal) (hVne : V ≠ ⊥)
    (hVmin : ∀ K : Subgroup G, K.Normal → K ≤ V → K = ⊥ ∨ K = V)
    (h3V : 3 ∣ Nat.card V) (hrank : CFSG.Open.pRank 3 (⊤ : Subgroup G) = 1) :
    IsSimpleGroup V := by
  by_contra hnot
  obtain ⟨r, S, e, he, i0, i1, hi, h3Si⟩ := simple_factor_data hVn hVne hVmin h3V hnot
  have h2 := pRank_two_of_factor_data (V := V) (e := e) (he := he) (i0 := i0) (i1 := i1) hi h3Si
  omega

private theorem le_center_of_abelian_simple {G : Type*} [Group G] [Finite G]
    [Group.IsPerfect G] {V : Subgroup G} (hVn : V.Normal) (hVab : IsMulCommutative V)
    (hVsimple : IsSimpleGroup V) (h3V : 3 ∣ Nat.card V) :
    V ≤ Subgroup.center G := by
  classical
  haveI : IsSimpleGroup V := hVsimple
  haveI : V.Normal := hVn
  letI : CommGroup V := IsMulCommutative.instCommGroup
  have hcardV : Nat.card V = 3 := by
    have hp : Nat.Prime (Nat.card V) := IsSimpleGroup.prime_card
    rcases (Nat.dvd_prime hp).mp h3V with h | h
    · omega
    · exact h.symm
  letI : IsCyclic V := isCyclic_of_prime_card hcardV
  have hP : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = ⊤ := by
    rw [← commutator_def, Group.IsPerfect.commutator_eq_top]
  let φ : G →* MulAut V := MulAut.conjNormal
  have hmap : (⊤ : Subgroup G).map φ = ⊥ :=
    CFSG.GroupTheory.map_eq_bot_of_isPerfect_of_isCyclicTarget φ hP
  intro v hv
  rw [Subgroup.mem_center_iff]
  intro g
  have hg : φ g = 1 := by
    have hmem : φ g ∈ (⊤ : Subgroup G).map φ := Subgroup.mem_map_of_mem φ (Subgroup.mem_top g)
    rwa [hmap] at hmem
  have hfix : φ g ⟨v, hv⟩ = ⟨v, hv⟩ := by rw [hg]; rfl
  have hval : g * (v : G) * g⁻¹ = v := by
    simpa [φ, MulAut.conjNormal_apply, MulAut.conj_apply] using congrArg Subtype.val hfix
  calc
    g * v = (g * v * g⁻¹) * g := by group
    _ = v * g := by rw [hval]

private theorem exists_maximal_normal_of_three_dvd {X : Type} [Group X] [Finite X] {p : ℕ}
    {L : Subgroup X} (h3O : 3 ∣ Nat.card (CFSG.pPrimeCore p ↥L)) :
    ∃ N : Subgroup ↥L,
      N.Normal ∧ N ≤ CFSG.pPrimeCore p ↥L ∧ 3 ∣ N.relIndex (CFSG.pPrimeCore p ↥L) ∧
        (∀ W : Subgroup ↥L, W.Normal → W ≤ CFSG.pPrimeCore p ↥L → N ≤ W → W ≠ N →
          ¬ 3 ∣ W.relIndex (CFSG.pPrimeCore p ↥L)) := by
  classical
  let O : Subgroup ↥L := CFSG.pPrimeCore p ↥L
  let 𝒮 : Set (Subgroup ↥L) := {N | N.Normal ∧ N ≤ O ∧ 3 ∣ N.relIndex O}
  have hbot : (⊥ : Subgroup ↥L) ∈ 𝒮 := by
    refine ⟨inferInstance, bot_le, ?_⟩
    rw [Subgroup.relIndex_bot_left]
    exact h3O
  obtain ⟨N, hNmem, hNmax⟩ := (Set.toFinite 𝒮).exists_maximal ⟨⊥, hbot⟩
  have hNn : N.Normal := hNmem.1
  have hNle : N ≤ O := hNmem.2.1
  have h3N : 3 ∣ N.relIndex O := hNmem.2.2
  refine ⟨N, hNn, hNle, h3N, ?_⟩
  intro W hWn hWle hNW hWne h3W
  have hWmem : W ∈ 𝒮 := ⟨hWn, hWle, h3W⟩
  exact hWne (le_antisymm (hNmax hWmem hNW) hNW)

private theorem exists_minimal_normal_section {X : Type} [Group X] [Finite X] {p : ℕ}
    {L : Subgroup X} {N : Subgroup ↥L} [N.Normal]
    (hNle : N ≤ CFSG.pPrimeCore p ↥L)
    (hNmax : ∀ W : Subgroup ↥L, W.Normal → W ≤ CFSG.pPrimeCore p ↥L → N ≤ W → W ≠ N →
      ¬ 3 ∣ W.relIndex (CFSG.pPrimeCore p ↥L))
    (h3N : 3 ∣ N.relIndex (CFSG.pPrimeCore p ↥L)) :
    ∃ V : Subgroup (↥L ⧸ N),
      V.Normal ∧ V ≤ (CFSG.pPrimeCore p ↥L).map (QuotientGroup.mk' N) ∧ V ≠ ⊥ ∧
        (∀ K : Subgroup (↥L ⧸ N), K.Normal → K ≤ V → K = ⊥ ∨ K = V) ∧
        3 ∣ Nat.card V := by
  classical
  let O : Subgroup ↥L := CFSG.pPrimeCore p ↥L
  let Obar : Subgroup (↥L ⧸ N) := O.map (QuotientGroup.mk' N)
  have hObar_n : Obar.Normal :=
    Subgroup.Normal.map (CFSG.pPrimeCore_normal (p := p)) _ (QuotientGroup.mk'_surjective N)
  have hObar_card : Nat.card Obar = N.relIndex O := by
    rw [CFSG.natCard_map_mk'_eq, Subgroup.relIndex, Subgroup.index_eq_card]
  have h3Obar : 3 ∣ Nat.card Obar := by
    rw [hObar_card]
    exact h3N
  have hObar_ne : Obar ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at h3Obar
    omega
  obtain ⟨V, hVn, hVle, hVne, hVmin⟩ := CFSG.exists_minimal_normal_le Obar hObar_n hObar_ne
  have hVmin' : ∀ K : Subgroup (↥L ⧸ N), K.Normal → K ≤ V → K = ⊥ ∨ K = V := by
    intro K hKn hKV
    by_cases hK : K = ⊥
    · exact Or.inl hK
    · exact Or.inr (hVmin K hKn hKV hK)
  let W : Subgroup ↥L := V.comap (QuotientGroup.mk' N)
  have hWn : W.Normal := Subgroup.Normal.comap hVn (QuotientGroup.mk' N)
  have hNW : N ≤ W := by
    intro n hn
    rw [Subgroup.mem_comap]
    have hmn : (QuotientGroup.mk' N) n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
    rw [hmn]
    exact V.one_mem
  have hWleO : W ≤ O := by
    intro w hw
    rcases Subgroup.mem_map.mp (hVle hw) with ⟨o, ho, hoo⟩
    have hwoN : o⁻¹ * w ∈ N := QuotientGroup.eq.mp hoo
    have : o * (o⁻¹ * w) ∈ O := O.mul_mem ho (hNle hwoN)
    simpa [mul_assoc] using this
  have hWne : W ≠ N := by
    intro hWN
    have hVbot : V = ⊥ := by
      have hmap := Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) V
      have hWNmap : W.map (QuotientGroup.mk' N) = N.map (QuotientGroup.mk' N) := by rw [hWN]
      rw [← hmap, hWNmap]
      exact QuotientGroup.map_mk'_self N
    exact hVne hVbot
  have hWnot : ¬ 3 ∣ W.relIndex O := hNmax W hWn hWleO hNW hWne
  have hprod : N.relIndex W * W.relIndex O = N.relIndex O :=
    Subgroup.relIndex_mul_relIndex N W O hNW hWleO
  have h3NW : 3 ∣ N.relIndex W := by
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp (hprod ▸ h3N) with h | h
    · exact h
    · exact absurd h hWnot
  have hVcard : Nat.card V = N.relIndex W := by
    rw [← Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) V,
      CFSG.natCard_map_mk'_eq, Subgroup.relIndex, Subgroup.index_eq_card]
  exact ⟨V, hVn, hVle, hVne, hVmin', hVcard ▸ h3NW⟩

private theorem perfect_core_image_eq {X : Type} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) {L : Subgroup X} {C : Subgroup ↥L}
    (hLperf : Group.IsPerfect ↥L)
    (hL_eq : (⊤ : Subgroup ↥L) = CFSG.pPrimeCore p ↥L ⊔ C)
    (hLsub : L.IsSubnormal) (J : Subgroup ↥L)
    (hJ : J = (CFSG.perfectResidual ↥C).map C.subtype) :
    (J.map L.subtype).map (QuotientGroup.mk' (CFSG.pPrimeCore p X)) =
      L.map (QuotientGroup.mk' (CFSG.pPrimeCore p X)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Group.IsPerfect ↥L := hLperf
  let O : Subgroup ↥L := CFSG.pPrimeCore p ↥L
  let JX : Subgroup X := J.map L.subtype
  let OX : Subgroup X := O.map L.subtype
  have hOsub : O.IsSubnormal := Subgroup.Normal.isSubnormal (CFSG.pPrimeCore_normal (p := p))
  have hOXsub : OX.IsSubnormal := CFSG.GroupTheory.isSubnormal_map_subtype hOsub hLsub
  have hOXcop : Nat.Coprime p (Nat.card OX) := by
    rw [Subgroup.card_map_of_injective L.subtype_injective]
    exact CFSG.pPrimeCore_coprime_card
  have hOXle : OX ≤ CFSG.pPrimeCore p X :=
    CFSG.GH74.GLS.le_pPrimeCore_of_subnormal p hOXsub hOXcop
  let πX : X →* X ⧸ CFSG.pPrimeCore p X := QuotientGroup.mk' _
  have hOXbot : OX.map πX = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hOXle
  have hLsup : L = OX ⊔ C.map L.subtype := by
    calc L = (⊤ : Subgroup ↥L).map L.subtype := by
          rw [Subgroup.map_top, Subgroup.range_subtype]
      _ = (O ⊔ C).map L.subtype := by rw [hL_eq]
      _ = OX ⊔ C.map L.subtype := Subgroup.map_sup ..
  have hImageL : L.map πX = (C.map L.subtype).map πX := by
    conv_lhs => rw [hLsup]
    rw [Subgroup.map_sup, hOXbot, bot_sup_eq]
  let f : ↥C →* X ⧸ CFSG.pPrimeCore p X := πX.comp (L.subtype.comp C.subtype)
  have hfrange : f.range = (C.map L.subtype).map πX := by
    rw [MonoidHom.range_eq_map]
    change (⊤ : Subgroup ↥C).map (πX.comp (L.subtype.comp C.subtype)) = _
    rw [show πX.comp (L.subtype.comp C.subtype) =
      (πX.comp L.subtype).comp C.subtype from rfl]
    rw [← Subgroup.map_map]
    change ((⊤ : Subgroup ↥C).map C.subtype).map (πX.comp L.subtype) =
      (C.map L.subtype).map πX
    rw [show (⊤ : Subgroup ↥C).map C.subtype = C from by
      rw [Subgroup.map_top, Subgroup.range_subtype]]
    rw [Subgroup.map_map]
  have hfperf : Group.IsPerfect ↥f.range := by
    rw [hfrange, ← hImageL]
    exact Group.IsPerfect.map (H := L) πX
  have hres := CFSG.perfect_residual_transport f
  have hfresTop : CFSG.perfectResidual ↥f.range = ⊤ := by
    apply top_le_iff.mp
    haveI : Group.IsPerfect ↥(⊤ : Subgroup ↥f.range) :=
      Group.IsPerfect.ofSurjective (f := (Subgroup.topEquiv (G := ↥f.range)).symm.toMonoidHom)
        (Subgroup.topEquiv (G := ↥f.range)).symm.surjective
    exact (CFSG.perfect_residual_transport (MonoidHom.id ↥f.range)).2.2 ⊤ ‹_›
  have hJmap : JX.map πX = L.map πX := by
    have h1 : JX.map πX = (CFSG.perfectResidual ↥C).map f := by
      dsimp only [JX]
      rw [hJ, Subgroup.map_map, Subgroup.map_map]
      rfl
    rw [h1, hres.1, hfresTop, Subgroup.map_top, Subgroup.range_subtype]
    exact hfrange.trans hImageL.symm
  exact hJmap

private theorem perfect_core_contradiction {X : Type} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) {L : Subgroup X} {C : Subgroup ↥L} (hCN : C.Normal) (hCne : C ≠ ⊤)
    (hLperf : Group.IsPerfect ↥L)
    (hL_eq : (⊤ : Subgroup ↥L) = CFSG.pPrimeCore p ↥L ⊔ C)
    (hLsub : L.IsSubnormal)
    {K : Subgroup (X ⧸ CFSG.pPrimeCore p X)}
    (hLmap : L.map (QuotientGroup.mk' (CFSG.pPrimeCore p X)) = K)
    (hLmin : ∀ J : Subgroup X, J < L → J.IsSubnormal →
      J.map (QuotientGroup.mk' (CFSG.pPrimeCore p X)) ≠ K) : False := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Group.IsPerfect ↥L := hLperf
  let O : Subgroup ↥L := CFSG.pPrimeCore p ↥L
  let J : Subgroup ↥L := (CFSG.perfectResidual ↥C).map C.subtype
  have hJn : J.Normal := ConjAct.normal_of_characteristic_of_normal
  have hJsub : J.IsSubnormal := Subgroup.Normal.isSubnormal hJn
  let JX : Subgroup X := J.map L.subtype
  have hJXsub : JX.IsSubnormal :=
    CFSG.GroupTheory.isSubnormal_map_subtype hJsub hLsub
  have hJleC : J ≤ C := Subgroup.map_subtype_le _
  have hClt : C < ⊤ := lt_of_le_of_ne le_top hCne
  have hJlt : J < ⊤ := lt_of_le_of_lt hJleC hClt
  have hJXlt : JX < L := by
    refine lt_of_le_of_ne (Subgroup.map_subtype_le _) ?_
    intro hmap
    apply hJlt.ne
    apply Subgroup.map_injective (f := L.subtype) L.subtype_injective
    have htopmap : (⊤ : Subgroup ↥L).map L.subtype = L := by
      rw [Subgroup.map_top, Subgroup.range_subtype]
    rw [show J.map L.subtype = L from hmap, htopmap]
  let πX : X →* X ⧸ CFSG.pPrimeCore p X := QuotientGroup.mk' _
  have hJmap : JX.map πX = L.map πX := by
    have h := perfect_core_image_eq hp hLperf hL_eq hLsub J rfl
    simpa [JX] using h
  exact (hLmin JX hJXlt hJXsub) (hJmap.trans hLmap)

private theorem pRank_top_quotient_eq_one {Y : Type} [Group Y] [Finite Y] {N : Subgroup Y}
    [N.Normal] {V : Subgroup (Y ⧸ N)} (h3V : 3 ∣ Nat.card V)
    (hrankY : CFSG.Open.pRank 3 (⊤ : Subgroup Y) = 1) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (Y ⧸ N)) = 1 := by
  classical
  have hle : CFSG.Open.pRank 3 (⊤ : Subgroup (Y ⧸ N)) ≤ 1 := by
    by_contra h
    have h2 : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (Y ⧸ N)) := by omega
    have h2L : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Y) :=
      CFSG.GroupTheory.two_le_pRank_of_quotient N Nat.prime_three (by norm_num) h2
    rw [hrankY] at h2L
    omega
  have hpos : 0 < CFSG.Open.pRank 3 (⊤ : Subgroup (Y ⧸ N)) := by
    by_contra h
    have h0 : CFSG.Open.pRank 3 (⊤ : Subgroup (Y ⧸ N)) = 0 := by omega
    have h3Lbar : 3 ∣ Nat.card (⊤ : Subgroup (Y ⧸ N)) := by
      rw [Subgroup.card_top]
      exact h3V.trans (Subgroup.card_subgroup_dvd_card V)
    exact (CFSG.GroupTheory.not_dvd_card_of_pRank_eq_zero Nat.prime_three h0) h3Lbar
  omega
private theorem abelian_case_false {Y : Type} [Group Y] [Finite Y] [Group.IsPerfect Y]
    {V : Subgroup Y} (hVn : V.Normal) (hVab : IsMulCommutative V)
    (hVsimple : IsSimpleGroup V) (h3V : 3 ∣ Nat.card V)
    (hrank : CFSG.Open.pRank 3 (⊤ : Subgroup Y) = 1) : False := by
  classical
  have hVcenter : V ≤ Subgroup.center Y :=
    le_center_of_abelian_simple hVn hVab hVsimple h3V
  have h3center : 3 ∣ Nat.card (Subgroup.center Y) :=
    h3V.trans (Subgroup.card_dvd_of_le hVcenter)
  exact (CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.not_dvd_card_center_of_pRank_eq_one
    (q := 3) (by norm_num) hrank) h3center
private theorem nonabelian_case_false {X : Type} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) {L : Subgroup X} {N : Subgroup ↥L} [N.Normal] {V : Subgroup (↥L ⧸ N)}
    (hNle : N ≤ CFSG.pPrimeCore p ↥L)
    (hVn : V.Normal) (hVsimple : IsSimpleGroup V) (hVnab : ¬ IsMulCommutative V)
    (hVle : V ≤ (CFSG.pPrimeCore p ↥L).map (QuotientGroup.mk' N))
    (hSch : CFSG.ComponentClassification.LBalance.SchreierSections X)
    (hLsub : L.IsSubnormal) (hLperf : Group.IsPerfect ↥L)
    {K : Subgroup (X ⧸ CFSG.pPrimeCore p X)}
    (hLmap : L.map (QuotientGroup.mk' (CFSG.pPrimeCore p X)) = K)
    (hLmin : ∀ J : Subgroup X, J < L → J.IsSubnormal →
      J.map (QuotientGroup.mk' (CFSG.pPrimeCore p X)) ≠ K) : False := by
  classical
  let O : Subgroup ↥L := CFSG.pPrimeCore p ↥L
  let Lbar := ↥L ⧸ N
  let Obar : Subgroup Lbar := O.map (QuotientGroup.mk' N)
  let π : ↥L →* Lbar := QuotientGroup.mk' N
  have hVnonab : ∃ a b : V, a * b ≠ b * a := by
    by_contra h
    push Not at h
    exact hVnab (IsMulCommutative.of_comm fun a b => h a b)

  haveI : IsSimpleGroup V := hVsimple
  have hSchV : CFSG.ComponentClassification.LBalance.SchreierSections V :=
    ((hSch.subgroup L).quotient N).subgroup V
  have hOut : Group.IsSolvable (ComponentClassification.OuterAutomorphisms.Outer V) :=
    hSchV.outer_solvable (⊤ : Subgroup V) hVnonab
      (Subgroup.topEquiv (G := V)).toMonoidHom (Subgroup.topEquiv (G := V)).surjective
  have hLV : (⊤ : Subgroup Lbar) ≤ V ⊔ Subgroup.centralizer (V : Set Lbar) := by
    haveI : Group.IsPerfect ↥(⊤ : Subgroup Lbar) :=
      Group.IsPerfect.ofSurjective (f := (Subgroup.topEquiv (G := Lbar)).symm.toMonoidHom)
        (Subgroup.topEquiv (G := Lbar)).symm.surjective
    have hleNorm : (⊤ : Subgroup Lbar) ≤ Subgroup.normalizer (V : Set Lbar) := by
      rw [Subgroup.normalizer_eq_top_iff.mpr hVn]
    exact CFSG.GH74.GLS.Stage2.Final.Thm6.L203.le_sup_centralizer_of_outer_solvable
      (I := V) (Z := ⊤) ‹Group.IsPerfect ↥(⊤ : Subgroup Lbar)› hleNorm hOut
  let Cbar : Subgroup Lbar := Subgroup.centralizer (V : Set Lbar)
  have hCbarN : Cbar.Normal := Subgroup.normal_centralizer
  let C : Subgroup ↥L := Cbar.comap π
  have hCN : C.Normal := Subgroup.Normal.comap hCbarN π
  have hLbarEq : (⊤ : Subgroup Lbar) = Obar ⊔ Cbar := by
    refine le_antisymm ?_ (sup_le le_top le_top)
    exact hLV.trans (sup_le (hVle.trans le_sup_left) le_sup_right)
  have hCne : C ≠ ⊤ := by
    intro hCtop
    have htop : (⊤ : Subgroup ↥L).map π = ⊤ := by
      rw [Subgroup.map_top]
      exact MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective N)
    have hCbarTop : Cbar = ⊤ := by
      have h := congrArg (Subgroup.map π) hCtop
      rw [Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N)] at h
      rwa [htop] at h
    obtain ⟨a, b, hab⟩ := hVnonab
    have hle : V ≤ Cbar := by
      rw [hCbarTop]
      exact le_top
    have hcomm : (b : Lbar) * (a : Lbar) = (a : Lbar) * (b : Lbar) :=
      (Subgroup.mem_centralizer_iff.mp (hle a.2)) b b.2
    exact hab (Subtype.ext hcomm.symm)
  have hcomapO : Obar.comap π = O := by
    change (O.map π).comap π = O
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hNle]
  have hL_eq : (⊤ : Subgroup ↥L) = O ⊔ C := by
    have h := congrArg (Subgroup.comap π) hLbarEq
    rw [← Subgroup.comap_sup_eq π Obar Cbar (QuotientGroup.mk'_surjective N),
      Subgroup.comap_top, hcomapO] at h
    simpa [C] using h
  exact perfect_core_contradiction hp hCN hCne hLperf hL_eq hLsub hLmap hLmin


theorem not_three_dvd_card_pPrimeCore_of_isPComponent {X : Type} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) (hSch : CFSG.ComponentClassification.LBalance.SchreierSections X)
    {L : Subgroup X} (hL : CFSG.IsPComponent p L) (h3 : CFSG.Open.pRank 3 L = 1) :
    ¬ 3 ∣ Nat.card (CFSG.pPrimeCore p ↥L) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra h3O
  by_cases hp3 : p = 3
  · subst hp3
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      (CFSG.pPrimeCore_coprime_card (G := ↥L) (p := 3)) h3O
  obtain ⟨K, hKcomp, hLsub, hLmap, hLmin⟩ := hL
  have hLperf : Group.IsPerfect ↥L :=
    ComponentClassification.CatalogueBAlternating.pComponent_perfect
      ⟨K, hKcomp, hLsub, hLmap, hLmin⟩
  let O : Subgroup ↥L := CFSG.pPrimeCore p ↥L
  obtain ⟨N, hNn, hNle, h3N, hNmax⟩ := exists_maximal_normal_of_three_dvd h3O
  haveI : N.Normal := hNn
  obtain ⟨V, hVn, hVle, hVne, hVmin, h3V⟩ :=
    exists_minimal_normal_section (L := L) (N := N) hNle hNmax h3N
  let Lbar := ↥L ⧸ N
  let Obar : Subgroup Lbar := O.map (QuotientGroup.mk' N)
  let π : ↥L →* Lbar := QuotientGroup.mk' N
  haveI : Group.IsPerfect ↥L := hLperf
  have hLbarPerf : Group.IsPerfect Lbar :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
  haveI : Group.IsPerfect Lbar := hLbarPerf
  have hrankL : CFSG.Open.pRank 3 (⊤ : Subgroup ↥L) = 1 := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact h3
  have hrankLbar : CFSG.Open.pRank 3 (⊤ : Subgroup Lbar) = 1 :=
    pRank_top_quotient_eq_one (N := N) h3V hrankL
  have hVsimple : IsSimpleGroup V :=
    isSimpleGroup_of_minimal_normal hVn hVne hVmin h3V hrankLbar
  by_cases hVab : IsMulCommutative V
  · exact abelian_case_false hVn hVab hVsimple h3V hrankLbar
  · exact nonabelian_case_false hp hNle hVn hVsimple hVab hVle hSch hLsub hLperf hLmap hLmin

end CFSG.LocalAnalysis.AGL81TheoremCD.Section8
