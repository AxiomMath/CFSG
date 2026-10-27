module

public import CFSG.ClassicalInvolution.Q3.Sec13EndDETwin
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G]

structure DE4Hyp (Ω : Set (Subgroup G)) : Prop extends DEHyp Ω where
  twin4 : ∀ K ∈ Ω, (twinSet Ω K).ncard = 4

@[expose] def dew1V (Ω : Set (Subgroup G)) (u : G) : Set (Subgroup G) :=
  {M | M ∈ Ω ∧ IsUniqueInvolution M u}

theorem dew1_involution_mem {Ω : Set (Subgroup G)} (h : DEHyp Ω) {L : Subgroup G} (hL : L ∈ Ω)
    {z : G} (hz : IsUniqueInvolution L z) : z ∈ zGroup Ω :=
  h.mem_zGroup_iff.mpr (Or.inr ⟨L, hL, hz⟩)

theorem dew1_centralizes_of_odd {Ω : Set (Subgroup G)} (h : DEHyp Ω) {x : G}
    (hx : x ∈ Subgroup.centralizer (zGroup Ω : Set G)) {L : Subgroup G} (hL : L ∈ Ω)
    (hxN : x ∈ Subgroup.normalizer (L : Set G)) {m : ℕ} (hxp : x ^ (2 * m + 1) = 1) :
    ∀ y ∈ L, x * y = y * x := by
  obtain ⟨z, hz⟩ := h.exists_isUniqueInvolution hL
  have hxz : x * z = z * x :=
    (Subgroup.mem_centralizer_iff.mp hx z (dew1_involution_mem h hL hz)).symm
  obtain ⟨i, j, hi, hj, hii, hjj, hji, hNF⟩ :=
    exists_q8_gen hz (h.isQuatSub_of_mem hL) (h.card L hL)
  have hQ : Q8Data L z i j := ⟨hz, hi, hj, hii, hjj, hji, hNF⟩
  have hcomm : ∀ w ∈ L, dComm x w = 1 ∨ dComm x w = z := by
    intro w hw
    have hC : dComm x w ∈ L ⊓ Subgroup.centralizer (zGroup Ω : Set G) := by
      refine ⟨dComm_mem hxN hw, ?_⟩
      have e : dComm x w = x * (w * x⁻¹ * w⁻¹) := by unfold dComm; group
      rw [e]
      exact (Subgroup.centralizer (zGroup Ω : Set G)).mul_mem hx
        (h.centralizer_zGroup_normal.conj_mem x⁻¹
          ((Subgroup.centralizer (zGroup Ω : Set G)).inv_mem hx) w)
    rw [h.inf_centralizer_zGroup hL hz] at hC
    exact det_tw_eq_one_or_of_mem_zpowers hz.sq hz.ne_one hC
  have hci : Commute (x ^ 2) i := commute_sq_of_dComm hz hxz (hcomm i hi) rfl
  have hcj : Commute (x ^ 2) j := commute_sq_of_dComm hz hxz (hcomm j hj) rfl
  have hcz : Commute (x ^ 2) z := (show Commute x z from hxz).pow_left 2
  have hsq2 : ∀ y ∈ L, Commute (x ^ 2) y := fun y hy => commute_sq_of_gen hQ hcz hci hcj hy
  have hpow : (x ^ 2) ^ (m + 1) = x := by
    rw [← pow_mul, show 2 * (m + 1) = 2 * m + 1 + 1 by ring, pow_succ, hxp, one_mul]
  intro y hy
  have hxy := (hsq2 y hy).pow_left (m + 1)
  rw [hpow] at hxy
  exact hxy

theorem dew1_eq_one_of_odd_central {Ω : Set (Subgroup G)} (h : DEHyp Ω) {x : G}
    (hx : x ∈ Subgroup.centralizer (zGroup Ω : Set G)) {m : ℕ} (hxp : x ^ (2 * m + 1) = 1)
    (hN : ∀ L ∈ Ω, x ∈ Subgroup.normalizer (L : Set G)) : x = 1 := by
  have hall : pSpan Ω ≤ Subgroup.centralizer ({x} : Set G) := by
    apply pSpan_le
    intro L hL y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (dew1_centralizes_of_odd h hx hL (hN L hL) hxp y hy).symm
  have hcenter : x ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ pSpan Ω := by rw [h.gen]; exact Subgroup.mem_top g
    exact Subgroup.mem_centralizer_singleton_iff.mp (hall hg)
  rw [h.center, Subgroup.mem_bot] at hcenter
  exact hcenter

theorem dew1_conj_mem {Ω : Set (Subgroup G)} (h : DEHyp Ω) {g : G}
    (hg : g ∈ Subgroup.centralizer (zGroup Ω : Set G)) {M : Subgroup G} {u : G}
    (hM : M ∈ dew1V Ω u) : conjSub g M ∈ dew1V Ω u := by
  obtain ⟨hMΩ, hu⟩ := hM
  have hgu : g * u * g⁻¹ = u := by
    have hu' := dew1_involution_mem h hMΩ hu
    have hc := Subgroup.mem_centralizer_iff.mp hg u hu'
    rw [← hc, mul_inv_cancel_right]
  refine ⟨h.hyp.conjInvariant g M hMΩ, ?_⟩
  have hc := hu.conj g
  rwa [hgu] at hc

noncomputable def dew1Act {Ω : Set (Subgroup G)} (h : DEHyp Ω) (u : G) :
    MulAction (Subgroup.centralizer (zGroup Ω : Set G)) (dew1V Ω u) where
  smul g M := ⟨conjSub (g : G) M.1, dew1_conj_mem h g.2 M.2⟩
  one_smul M := Subtype.ext (conjSub_one M.1)
  mul_smul g g' M := Subtype.ext (conjSub_mul (g : G) (g' : G) M.1)

theorem dew1V_eq_twinSet {Ω : Set (Subgroup G)} {K : Subgroup G} (hK : K ∈ Ω) {u : G}
    (hu : IsUniqueInvolution K u) : dew1V Ω u = twinSet Ω K := by
  ext M
  constructor
  · rintro ⟨hM, hMu⟩
    exact ⟨hM, u, hu, hMu⟩
  · rintro ⟨hM, z, hz, hMz⟩
    exact ⟨hM, by rw [hu.eq hz]; exact hMz⟩

theorem dew1_fixed_ncard_modEq {Ω : Set (Subgroup G)} (h : DEHyp Ω)
    (h4 : ∀ K ∈ Ω, (twinSet Ω K).ncard = 4)
    {S : Subgroup G} (hS : S ≤ Subgroup.centralizer (zGroup Ω : Set G)) {p : ℕ} [hp : Fact p.Prime]
    (hSp : IsPGroup p S) {K : Subgroup G} (hK : K ∈ Ω) {u : G} (hu : IsUniqueInvolution K u) :
    ({M | M ∈ dew1V Ω u ∧ ∀ s ∈ S, conjSub s M = M} : Set (Subgroup G)).ncard ≡ 4 [MOD p] := by
  letI : MulAction (Subgroup.centralizer (zGroup Ω : Set G)) (dew1V Ω u) := dew1Act h u
  letI : MulAction S (dew1V Ω u) := MulAction.compHom _ (Subgroup.inclusion hS)
  have hV : (dew1V Ω u).ncard = 4 := by
    rw [dew1V_eq_twinSet hK hu, h4 K hK]
  have hmod := hSp.card_modEq_card_fixedPoints (dew1V Ω u)
  have hfix : Subtype.val '' (MulAction.fixedPoints S (dew1V Ω u)) =
      {M | M ∈ dew1V Ω u ∧ ∀ s ∈ S, conjSub s M = M} := by
    ext M
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨a.2, fun s hs => ?_⟩
      have h1 := ha ⟨s, hs⟩
      have h2 : (⟨s, hs⟩ : S) • a = a := h1
      have h3 := congrArg Subtype.val h2
      exact h3
    · rintro ⟨hM, hs⟩
      refine ⟨⟨M, hM⟩, fun s => ?_, rfl⟩
      apply Subtype.ext
      exact hs s.1 s.2
  have hF : Nat.card (MulAction.fixedPoints S (dew1V Ω u)) =
      ({M | M ∈ dew1V Ω u ∧ ∀ s ∈ S, conjSub s M = M} : Set (Subgroup G)).ncard := by
    rw [← hfix, Set.ncard_image_of_injective _ Subtype.val_injective,
      Nat.card_coe_set_eq]
  have h5 : Nat.card (dew1V Ω u) = 4 := by rw [Nat.card_coe_set_eq]; exact hV
  rw [← hF]
  rw [h5] at hmod
  exact hmod.symm

theorem dew1_normal_of_five_le {Ω : Set (Subgroup G)} (h : DEHyp Ω)
    (h4 : ∀ K ∈ Ω, (twinSet Ω K).ncard = 4)
    {S : Subgroup G} (hS : S ≤ Subgroup.centralizer (zGroup Ω : Set G)) {p : ℕ} [hp : Fact p.Prime]
    (hSp : IsPGroup p S) (hp5 : 5 ≤ p) {K : Subgroup G} (hK : K ∈ Ω) {u : G}
    (hu : IsUniqueInvolution K u) {M : Subgroup G} (hM : M ∈ dew1V Ω u) :
    ∀ s ∈ S, conjSub s M = M := by
  have hmod := dew1_fixed_ncard_modEq h h4 hS hSp hK hu
  have hVc : (dew1V Ω u).ncard = 4 := by rw [dew1V_eq_twinSet hK hu, h4 K hK]
  have hFV : ({M | M ∈ dew1V Ω u ∧ ∀ s ∈ S, conjSub s M = M} : Set (Subgroup G)) ⊆
      dew1V Ω u := fun _ hM' => hM'.1
  have hFle : ({M | M ∈ dew1V Ω u ∧ ∀ s ∈ S, conjSub s M = M} : Set (Subgroup G)).ncard ≤ 4 := by
    rw [← hVc]; exact Set.ncard_le_ncard hFV
  have hkp : ({M | M ∈ dew1V Ω u ∧ ∀ s ∈ S, conjSub s M = M} : Set (Subgroup G)).ncard % p =
      ({M | M ∈ dew1V Ω u ∧ ∀ s ∈ S, conjSub s M = M} : Set (Subgroup G)).ncard :=
    Nat.mod_eq_of_lt (by omega)
  have h4p : 4 % p = 4 := Nat.mod_eq_of_lt (by omega)
  have hmod' := hmod
  unfold Nat.ModEq at hmod'
  rw [hkp, h4p] at hmod'
  have hF4 : ({M | M ∈ dew1V Ω u ∧ ∀ s ∈ S, conjSub s M = M} : Set (Subgroup G)).ncard = 4 := by
    omega
  have heq : ({M | M ∈ dew1V Ω u ∧ ∀ s ∈ S, conjSub s M = M} : Set (Subgroup G)) =
      dew1V Ω u :=
    Set.eq_of_subset_of_ncard_le hFV (by rw [hF4, hVc]) (Set.toFinite _)
  have hMF : M ∈ ({M | M ∈ dew1V Ω u ∧ ∀ s ∈ S, conjSub s M = M} : Set (Subgroup G)) := by
    rw [heq]; exact hM
  exact hMF.2

theorem dew1_three_dichotomy {Ω : Set (Subgroup G)} (h : DEHyp Ω)
    (h4 : ∀ K ∈ Ω, (twinSet Ω K).ncard = 4)
    {S : Subgroup G} (hS : S ≤ Subgroup.centralizer (zGroup Ω : Set G))
    (hSp : IsPGroup 3 S) {K : Subgroup G} (hK : K ∈ Ω) {u : G}
    (hu : IsUniqueInvolution K u) :
    ({M | M ∈ dew1V Ω u ∧ ∀ s ∈ S, conjSub s M = M} : Set (Subgroup G)) = dew1V Ω u ∨
      ({M | M ∈ dew1V Ω u ∧ ∀ s ∈ S, conjSub s M = M} : Set (Subgroup G)).ncard = 1 := by
  have hmod := dew1_fixed_ncard_modEq h h4 hS hSp hK hu
  have hVc : (dew1V Ω u).ncard = 4 := by rw [dew1V_eq_twinSet hK hu, h4 K hK]
  have hFV : ({M | M ∈ dew1V Ω u ∧ ∀ s ∈ S, conjSub s M = M} : Set (Subgroup G)) ⊆
      dew1V Ω u := fun _ hM' => hM'.1
  by_cases hF : ({M | M ∈ dew1V Ω u ∧ ∀ s ∈ S, conjSub s M = M} : Set (Subgroup G)) =
      dew1V Ω u
  · exact Or.inl hF
  · right
    have hlt : ({M | M ∈ dew1V Ω u ∧ ∀ s ∈ S, conjSub s M = M} : Set (Subgroup G)).ncard < 4 := by
      rw [← hVc]
      exact Set.ncard_lt_ncard (hFV.ssubset_of_ne hF)
    have hmod' := hmod
    unfold Nat.ModEq at hmod'
    norm_num at hmod'
    omega

noncomputable def dew1Perm {Ω : Set (Subgroup G)} (h : DEHyp Ω) (u : G) :
    Subgroup.centralizer (zGroup Ω : Set G) →* Equiv.Perm (dew1V Ω u) :=
  letI := dew1Act h u
  MulAction.toPermHom _ _

noncomputable def dew1Psi {Ω : Set (Subgroup G)} (h : DEHyp Ω) :
    Subgroup.centralizer (zGroup Ω : Set G) →* ∀ u : G, Equiv.Perm (dew1V Ω u) :=
  MonoidHom.pi (fun u => dew1Perm h u)

theorem dew1_conj_eq_of_psi {Ω : Set (Subgroup G)} (h : DEHyp Ω)
    {x : Subgroup.centralizer (zGroup Ω : Set G)} (hx : dew1Psi h x = 1) {u : G}
    {M : Subgroup G} (hM : M ∈ dew1V Ω u) : conjSub (x : G) M = M := by
  have h1 : dew1Perm h u x = 1 := congrFun hx u
  have h2 := congrArg (fun σ : Equiv.Perm (dew1V Ω u) => (σ ⟨M, hM⟩).1) h1
  exact h2

theorem dew1_isPGroup_two {Γ : Type} [Group Γ] [Finite Γ] {H : Subgroup Γ}
    (hH : ∀ x ∈ H, Odd (orderOf x) → x = 1) : IsPGroup 2 H := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [IsPGroup.iff_orderOf]
  intro g
  obtain ⟨k, o, ho, hko⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (g : Γ)).ne'
  refine ⟨k, ?_⟩
  have hy : (g : Γ) ^ (2 ^ k) ∈ H := H.pow_mem g.2 _
  have hyodd : Odd (orderOf ((g : Γ) ^ (2 ^ k))) := by
    have hpo : ((g : Γ) ^ (2 ^ k)) ^ o = 1 := by
      rw [← pow_mul, ← hko, pow_orderOf_eq_one]
    exact ho.of_dvd_nat (orderOf_dvd_of_pow_eq_one hpo)
  have hy1 : (g : Γ) ^ (2 ^ k) = 1 := hH _ hy hyodd
  have hdvd : orderOf (g : Γ) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hy1
  rw [hko] at hdvd
  have hpos : 0 < 2 ^ k := by positivity
  have ho1 : o = 1 := by
    have h3 : 2 ^ k * o ∣ 2 ^ k * 1 := by simpa using hdvd
    exact Nat.dvd_one.mp (Nat.dvd_of_mul_dvd_mul_left hpos h3)
  rw [← Subgroup.orderOf_coe, hko, ho1, mul_one]

open scoped commutatorElement in
theorem dew1_isSolvable_pi {η : Type} [Finite η] {Gs : η → Type} [∀ i, Group (Gs i)]
    [∀ i, Group.IsSolvable (Gs i)] : Group.IsSolvable (∀ i, Gs i) := by
  classical
  cases nonempty_fintype η
  choose n hn using fun i => (Group.IsSolvable.solvable (G := Gs i))
  let S : ℕ → Subgroup (∀ i, Gs i) := fun m =>
    { carrier := {x | ∀ i, x i ∈ derivedSeries (Gs i) m}
      mul_mem' := fun ha hb i => (derivedSeries (Gs i) m).mul_mem (ha i) (hb i)
      one_mem' := fun i => (derivedSeries (Gs i) m).one_mem
      inv_mem' := fun ha i => (derivedSeries (Gs i) m).inv_mem (ha i) }
  have key : ∀ m : ℕ, derivedSeries (∀ i, Gs i) m ≤ S m := by
    intro m
    induction m with
    | zero =>
      intro x _ i
      rw [derivedSeries_zero]
      exact Subgroup.mem_top _
    | succ m ih =>
      rw [derivedSeries_succ]
      apply Subgroup.commutator_le.mpr
      intro x hx y hy i
      show ⁅x, y⁆ i ∈ derivedSeries (Gs i) (m + 1)
      rw [derivedSeries_succ]
      exact Subgroup.commutator_mem_commutator (ih hx i) (ih hy i)
  refine ⟨⟨Finset.univ.sup n, le_bot_iff.mp ?_⟩⟩
  intro x hx
  have hxS := key _ hx
  rw [Subgroup.mem_bot]
  funext i
  have hi : derivedSeries (Gs i) (Finset.univ.sup n) = ⊥ := by
    have hle : n i ≤ Finset.univ.sup n := Finset.le_sup (f := n) (Finset.mem_univ i)
    exact le_bot_iff.mp ((derivedSeries_antitone (G := Gs i) hle).trans (hn i).le)
  have := hxS i
  rw [hi, Subgroup.mem_bot] at this
  exact this

theorem dew1_isSolvable_centralizer {Ω : Set (Subgroup G)} (h : DEHyp Ω)
    (h4 : ∀ K ∈ Ω, (twinSet Ω K).ncard = 4) :
    Group.IsSolvable ↥(Subgroup.centralizer (zGroup Ω : Set G)) := by
  classical
  have hcard : ∀ u : G, Nat.card (dew1V Ω u) ≤ 4 := by
    intro u
    by_cases hne : ∃ K ∈ Ω, IsUniqueInvolution K u
    · obtain ⟨K, hK, hKu⟩ := hne
      rw [Nat.card_coe_set_eq, dew1V_eq_twinSet hK hKu, h4 K hK]
    · have hempty : dew1V Ω u = ∅ := by
        ext M
        constructor
        · rintro ⟨hM, hMu⟩
          exact absurd ⟨M, hM, hMu⟩ hne
        · intro hM
          exact hM.elim
      rw [Nat.card_coe_set_eq, hempty]
      simp
  haveI : ∀ u : G, Group.IsSolvable (Equiv.Perm (dew1V Ω u)) := fun u =>
    Equiv.Perm.isSolvable (hcard u)
  haveI : Group.IsSolvable (∀ u : G, Equiv.Perm (dew1V Ω u)) := dew1_isSolvable_pi
  have hker : IsPGroup 2 (dew1Psi h).ker := by
    apply dew1_isPGroup_two
    intro x hx hodd
    obtain ⟨m, hm⟩ := hodd
    have hxp : (x : G) ^ (2 * m + 1) = 1 := by
      rw [← hm]
      have := pow_orderOf_eq_one x
      rw [← Subgroup.coe_pow, this, Subgroup.coe_one]
    have hN : ∀ L ∈ Ω, (x : G) ∈ Subgroup.normalizer (L : Set G) := by
      intro L hL
      obtain ⟨z, hz⟩ := h.exists_isUniqueInvolution hL
      rw [mem_normalizer_iff_conjSub_eq]
      exact dew1_conj_eq_of_psi h (MonoidHom.mem_ker.mp hx) ⟨hL, hz⟩
    have := dew1_eq_one_of_odd_central h x.2 hxp hN
    exact Subtype.ext this
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsSolvable ↥(dew1Psi h).ker := by
    haveI := hker.isNilpotent
    infer_instance
  exact Group.isSolvable_of_ker_le_range (dew1Psi h).ker.subtype (dew1Psi h)
    (le_of_eq (Subgroup.range_subtype _).symm)

theorem dew1_no_big_prime {Ω : Set (Subgroup G)} (h : DEHyp Ω)
    (h4 : ∀ K ∈ Ω, (twinSet Ω K).ncard = 4) {x : G}
    (hx : x ∈ Subgroup.centralizer (zGroup Ω : Set G)) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hxp : x ^ p = 1) : x = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hx1
  have hord : orderOf x = p := orderOf_eq_prime hxp hx1
  have hSle : Subgroup.zpowers x ≤ Subgroup.centralizer (zGroup Ω : Set G) :=
    Subgroup.zpowers_le.mpr hx
  haveI : Fact p.Prime := ⟨hp⟩
  have hSp : IsPGroup p (Subgroup.zpowers x) := by
    apply IsPGroup.of_card
    rw [Nat.card_zpowers, hord, pow_one]
  have hall : ∀ L ∈ Ω, x ∈ Subgroup.normalizer (L : Set G) := by
    intro L hL
    obtain ⟨z, hz⟩ := h.exists_isUniqueInvolution hL
    rw [mem_normalizer_iff_conjSub_eq]
    exact dew1_normal_of_five_le h h4 hSle hSp hp5 hL hz ⟨hL, hz⟩ x (Subgroup.mem_zpowers x)
  have hpo : Odd p := hp.odd_of_ne_two (by omega)
  obtain ⟨m, hm⟩ := hpo
  have hxp' : x ^ (2 * m + 1) = 1 := by rw [← hm]; exact hxp
  exact hx1 (dew1_eq_one_of_odd_central h hx hxp' hall)

theorem dew1_prime_dvd_centralizer {Ω : Set (Subgroup G)} (h : DEHyp Ω)
    (h4 : ∀ K ∈ Ω, (twinSet Ω K).ncard = 4) {p : ℕ} (hp : p.Prime)
    (hpd : p ∣ Nat.card ↥(Subgroup.centralizer (zGroup Ω : Set G))) : p = 2 ∨ p = 3 := by
  by_contra hne
  have h4' : p ≠ 4 := by rintro rfl; norm_num at hp
  have h5 : 5 ≤ p := by have := hp.two_le; omega
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' p hpd
  have hxp : (c : G) ^ p = 1 := by
    have h1 := pow_orderOf_eq_one c
    rw [hc] at h1
    rw [← Subgroup.coe_pow, h1, Subgroup.coe_one]
  have hord : orderOf (c : G) = p := (Subgroup.orderOf_coe c).trans hc
  have h1 := dew1_no_big_prime h h4 c.2 hp h5 hxp
  rw [h1, orderOf_one] at hord
  exact hp.one_lt.ne' hord.symm

open scoped commutatorElement in
theorem dew1_mod_two {N : Subgroup G} [N.Normal] (hQN : pCore 2 G ≤ N)
    (hcomm : ∀ x ∈ N, ∀ y ∈ N, ⁅x, y⁆ ∈ pCore 2 G) {x : G} (hx : x ∈ N) {k : ℕ}
    (hxk : x ^ (2 ^ k) ∈ pCore 2 G) : x ∈ pCore 2 G := by
  classical
  haveI : (pCore 2 G).Normal := CFSG.pCore_normal
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π : G →* G ⧸ pCore 2 G := QuotientGroup.mk' (pCore 2 G) with hπ
  have hcommq : ∀ y ∈ N, ∀ z ∈ N, Commute (π y) (π z) := by
    intro y hy z hz
    have h1 : π ⁅y, z⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr (hcomm y hy z hz)
    rw [map_commutatorElement] at h1
    exact commutatorElement_eq_one_iff_commute.mp h1
  let T : Subgroup G :=
    { carrier := {y | y ∈ N ∧ ∃ j : ℕ, y ^ (2 ^ j) ∈ pCore 2 G}
      mul_mem' := by
        rintro y z ⟨hy, j, hyj⟩ ⟨hz, l, hzl⟩
        refine ⟨N.mul_mem hy hz, j + l, ?_⟩
        rw [← QuotientGroup.eq_one_iff]
        show π ((y * z) ^ (2 ^ (j + l))) = 1
        have hyp : (π y) ^ (2 ^ j) = 1 := by
          rw [← map_pow]; exact (QuotientGroup.eq_one_iff _).mpr hyj
        have hzp : (π z) ^ (2 ^ l) = 1 := by
          rw [← map_pow]; exact (QuotientGroup.eq_one_iff _).mpr hzl
        rw [map_pow, map_mul, (hcommq y hy z hz).mul_pow]
        have e1 : (π y) ^ (2 ^ (j + l)) = 1 := by
          rw [pow_add, pow_mul, hyp, one_pow]
        have e2 : (π z) ^ (2 ^ (j + l)) = 1 := by
          rw [add_comm, pow_add, pow_mul, hzp, one_pow]
        rw [e1, e2, one_mul]
      one_mem' := ⟨N.one_mem, 0, by simpa using (pCore 2 G).one_mem⟩
      inv_mem' := by
        rintro y ⟨hy, j, hyj⟩
        refine ⟨N.inv_mem hy, j, ?_⟩
        rw [inv_pow]
        exact (pCore 2 G).inv_mem hyj }
  have hTn : T.Normal := by
    refine ⟨fun t ht g => ?_⟩
    obtain ⟨ht1, j, hj⟩ := ht
    refine ⟨Subgroup.Normal.conj_mem ‹N.Normal› t ht1 g, j, ?_⟩
    rw [conj_pow]
    exact Subgroup.Normal.conj_mem CFSG.pCore_normal _ hj g
  have hT2 : IsPGroup 2 T := by
    rw [IsPGroup.iff_orderOf]
    intro t
    obtain ⟨_, j, hj⟩ := t.2
    obtain ⟨a, ha⟩ := (IsPGroup.iff_orderOf.mp (CFSG.pCore_isPGroup (p := 2) (G := G)))
      ⟨(t : G) ^ (2 ^ j), hj⟩
    have hu : ((t : G) ^ (2 ^ j)) ^ (2 ^ a) = 1 := by
      have h1 := pow_orderOf_eq_one (⟨(t : G) ^ (2 ^ j), hj⟩ : ↥(pCore 2 G))
      rw [ha] at h1
      have h2 := congrArg Subtype.val h1
      simpa using h2
    have hpow : (t : G) ^ (2 ^ (j + a)) = 1 := by
      rw [pow_add, pow_mul]; exact hu
    obtain ⟨i, -, hi⟩ :=
      (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hpow)
    exact ⟨i, by rw [← Subgroup.orderOf_coe]; exact hi⟩
  have hTQ : T ≤ pCore 2 G := le_sSup ⟨hTn, hT2⟩
  exact hTQ ⟨hx, k, hxk⟩

open scoped commutatorElement in
theorem dew1_exists_R {C Q : Subgroup G} [Q.Normal] (hCn : C.Normal) (hQC : Q ≤ C)
    (hsolv : Group.IsSolvable ↥C) (hne : Q ≠ C) :
    ∃ R : Subgroup G, R.Normal ∧ Q ≤ R ∧ R ≤ C ∧ R ≠ Q ∧
      ∀ x ∈ R, ∀ y ∈ R, ⁅x, y⁆ ∈ Q := by
  classical
  let f : Subgroup G → Subgroup G := fun A => ⁅A, A⁆
  let dser : ℕ → Subgroup G := fun n => f^[n] C
  have hsucc : ∀ n, dser (n + 1) = ⁅dser n, dser n⁆ := fun n => Function.iterate_succ_apply' _ _ _
  have hzero : dser 0 = C := rfl
  have hle : ∀ n, dser n ≤ C := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
      rw [hsucc]
      apply Subgroup.commutator_le.mpr
      intro x hx y hy
      exact C.mul_mem (C.mul_mem (C.mul_mem (ih hx) (ih hy)) (C.inv_mem (ih hx)))
        (C.inv_mem (ih hy))
  have hnorm : ∀ n, (dser n).Normal := by
    intro n
    induction n with
    | zero => exact hCn
    | succ n ih =>
      rw [hsucc]
      haveI := ih
      infer_instance
  have hsol : ∃ m, dser m ≤ Q := by
    obtain ⟨m, hm⟩ := hsolv.solvable
    have hmap : ∀ n, (derivedSeries ↥C n).map C.subtype = dser n := by
      intro n
      induction n with
      | zero =>
        rw [derivedSeries_zero, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
        rfl
      | succ n ih =>
        rw [derivedSeries_succ, Subgroup.map_commutator, ih, hsucc]
    refine ⟨m, ?_⟩
    rw [← hmap m, hm, Subgroup.map_bot]
    exact bot_le
  have hex : ∃ n, dser n ≤ Q := hsol
  let k := Nat.find hex
  have hk : dser k ≤ Q := Nat.find_spec hex
  have hk0 : k ≠ 0 := by
    intro h0
    apply hne
    apply le_antisymm hQC
    have : dser 0 ≤ Q := by rw [← h0]; exact hk
    exact this
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  have hjQ : ¬ dser j ≤ Q := by
    have := Nat.find_min hex (show j < k by omega)
    exact this
  let R : Subgroup G := dser j ⊔ Q
  haveI : (dser j).Normal := hnorm j
  have hRn : R.Normal := inferInstance
  refine ⟨R, hRn, le_sup_right, sup_le (hle j) hQC, ?_, ?_⟩
  · intro hR
    apply hjQ
    exact le_sup_left.trans hR.le
  · intro x hx y hy
    have hπ : ∀ z ∈ R, ∃ a ∈ dser j, ∃ q ∈ Q, z = a * q := fun z hz => by
      obtain ⟨a, ha, q, hq, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hz
      exact ⟨a, ha, q, hq, rfl⟩
    obtain ⟨a, ha, q, hq, rfl⟩ := hπ x hx
    obtain ⟨b, hb, q', hq', rfl⟩ := hπ y hy
    have hk' : dser (j + 1) ≤ Q := by rw [← Nat.succ_eq_add_one, ← hj]; exact hk
    have hab : ⁅a, b⁆ ∈ Q := by
      have h1 : ⁅a, b⁆ ∈ dser (j + 1) := by
        rw [hsucc]; exact Subgroup.commutator_mem_commutator ha hb
      exact hk' h1
    have hπab : (QuotientGroup.mk' Q) ⁅a, b⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr hab
    rw [map_commutatorElement] at hπab
    have hq1 : (QuotientGroup.mk' Q) q = 1 := (QuotientGroup.eq_one_iff q).mpr hq
    have hq1' : (QuotientGroup.mk' Q) q' = 1 := (QuotientGroup.eq_one_iff q').mpr hq'
    rw [← QuotientGroup.eq_one_iff]
    show (QuotientGroup.mk' Q) ⁅a * q, b * q'⁆ = 1
    rw [map_commutatorElement, map_mul, map_mul, hq1, hq1', mul_one, mul_one]
    exact hπab

theorem dew1_sylow_three {R Q : Subgroup G} [R.Normal] [Q.Normal] (hQR : Q ≤ R)
    (hM2 : ∀ x ∈ R, ∀ k : ℕ, x ^ (2 ^ k) ∈ Q → x ∈ Q)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card R → p = 2 ∨ p = 3) (hRQ : Q ≠ R) :
    ∃ P : Sylow 3 R, (∀ r ∈ R, ∃ x ∈ (P : Subgroup R).map R.subtype, ∃ q ∈ Q, r = x * q) ∧
      (P : Subgroup R).map R.subtype ≠ ⊥ := by
  classical
  let Qh : Subgroup R := Q.subgroupOf R
  haveI : Qh.Normal := inferInstance
  have hQidx : ∃ k : ℕ, Qh.index = 3 ^ k := by
    have hne : Qh.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hne ?_⟩
    intro d hd hdvd
    haveI : Fact d.Prime := ⟨hd⟩
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' d (G := R ⧸ Qh) hdvd
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective g
    have hy1 : (QuotientGroup.mk' Qh) (y ^ d) = 1 := by
      rw [map_pow]
      have h1 := pow_orderOf_eq_one (QuotientGroup.mk' Qh y)
      have hg' : orderOf (QuotientGroup.mk' Qh y) = d := hg
      rw [hg'] at h1
      exact h1
    have hyd : y ^ d ∈ Qh := (QuotientGroup.eq_one_iff _).mp hy1
    have hyd' : (y : G) ^ d ∈ Q := by
      have := Subgroup.mem_subgroupOf.mp hyd
      rwa [Subgroup.coe_pow] at this
    have hyQ : (y : G) ∉ Q := by
      intro hyQ
      have hyh : y ∈ Qh := Subgroup.mem_subgroupOf.mpr hyQ
      have h2 : QuotientGroup.mk' Qh y = 1 := (QuotientGroup.eq_one_iff _).mpr hyh
      have hg' : orderOf (QuotientGroup.mk' Qh y) = d := hg
      rw [h2, orderOf_one] at hg'
      exact hd.one_lt.ne' hg'.symm
    have hdR : d ∣ Nat.card R := hdvd.trans (Subgroup.index_dvd_card _)
    rcases hprime d hd hdR with rfl | rfl
    · exfalso
      apply hyQ
      apply hM2 (y : G) y.2 1
      rw [pow_one]
      exact hyd'
    · rfl
  obtain ⟨k, hk⟩ := hQidx
  obtain ⟨P⟩ : Nonempty (Sylow 3 R) := inferInstance
  have hcop : ¬ 3 ∣ (P : Subgroup R).index := P.not_dvd_index
  have hsup : (P : Subgroup R) ⊔ Qh = ⊤ := by
    have h1 : ((P : Subgroup R) ⊔ Qh).index ∣ (P : Subgroup R).index :=
      Subgroup.index_dvd_of_le le_sup_left
    have h2 : ((P : Subgroup R) ⊔ Qh).index ∣ Qh.index :=
      Subgroup.index_dvd_of_le le_sup_right
    have h3 : ¬ 3 ∣ ((P : Subgroup R) ⊔ Qh).index := fun h => hcop (h.trans h1)
    have h4 : Nat.Coprime ((P : Subgroup R) ⊔ Qh).index 3 :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3).symm
    have h5 : Nat.Coprime ((P : Subgroup R) ⊔ Qh).index (3 ^ k) := Nat.Coprime.pow_right k h4
    have h6 : ((P : Subgroup R) ⊔ Qh).index = 1 := Nat.Coprime.eq_one_of_dvd h5 (hk ▸ h2)
    exact Subgroup.index_eq_one.mp h6
  refine ⟨P, ?_, ?_⟩
  · intro r hr
    have hmem : (⟨r, hr⟩ : R) ∈ (P : Subgroup R) ⊔ Qh := by
      rw [hsup]; exact Subgroup.mem_top _
    obtain ⟨x, hx, z, hz, hxz⟩ := Subgroup.mem_sup_of_normal_right.mp hmem
    refine ⟨x.1, Subgroup.mem_map.mpr ⟨x, hx, rfl⟩, z.1, Subgroup.mem_subgroupOf.mp hz, ?_⟩
    have := congrArg Subtype.val hxz
    exact this.symm
  · intro hX
    have hPbot : (P : Subgroup R) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hxm : x.1 ∈ (P : Subgroup R).map R.subtype := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
      rw [hX, Subgroup.mem_bot] at hxm
      rw [Subgroup.mem_bot]
      exact Subtype.ext hxm
    apply hRQ
    apply le_antisymm hQR
    intro r hr
    have hmem : (⟨r, hr⟩ : R) ∈ (P : Subgroup R) ⊔ Qh := by
      rw [hsup]; exact Subgroup.mem_top _
    rw [hPbot, bot_sup_eq] at hmem
    exact Subgroup.mem_subgroupOf.mp hmem

theorem dew1_frattini {R : Subgroup G} [R.Normal] (P : Sylow 3 R) (g : G) :
    ∃ n ∈ Subgroup.normalizer (((P : Subgroup R).map R.subtype : Subgroup G) : Set G),
      ∃ r ∈ R, g = n * r := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := Sylow.normalizer_sup_eq_top P
  have hg : g ∈ Subgroup.normalizer ((P : Subgroup R).map R.subtype) ⊔ R := by
    rw [h]; exact Subgroup.mem_top g
  obtain ⟨n, hn, r, hr, hnr⟩ := Subgroup.mem_sup_of_normal_right.mp hg
  exact ⟨n, hn, r, hr, hnr.symm⟩

open scoped commutatorElement in
theorem dew1_all_members {Ω : Set (Subgroup G)} (h : DEHyp Ω) {R X : Subgroup G}
    (hRC : R ≤ Subgroup.centralizer (zGroup Ω : Set G))
    (hfrat : ∀ g : G, ∃ n ∈ Subgroup.normalizer (X : Set G), ∃ r ∈ R, g = n * r)
    {K₀ : Subgroup G} (hK₀ : K₀ ∈ Ω) {u₀ : G} (hu₀ : IsUniqueInvolution K₀ u₀)
    (hV : ∀ M ∈ dew1V Ω u₀, ∀ x ∈ X, conjSub x M = M) :
    ∀ L ∈ Ω, ∀ x ∈ X, conjSub x L = L := by
  intro L hL x hx
  obtain ⟨g, hg⟩ := h.trans K₀ hK₀ L hL
  obtain ⟨n, hn, r, hr, rfl⟩ := hfrat g
  obtain ⟨z, hz⟩ := h.exists_isUniqueInvolution hL
  have hu₀D : u₀ ∈ zGroup Ω := dew1_involution_mem h hK₀ hu₀
  have hrC : r ∈ Subgroup.centralizer (zGroup Ω : Set G) := hRC hr
  have hcomm : r * u₀ = u₀ * r := (Subgroup.mem_centralizer_iff.mp hrC u₀ hu₀D).symm
  have hzeq : z = n * u₀ * n⁻¹ := by
    have hc := hu₀.conj (n * r)
    rw [hg] at hc
    rw [hz.eq hc]
    calc n * r * u₀ * (n * r)⁻¹ = n * (r * u₀ * r⁻¹) * n⁻¹ := by group
      _ = n * (u₀ * r * r⁻¹) * n⁻¹ := by rw [hcomm]
      _ = n * u₀ * n⁻¹ := by group
  set M := conjSub n⁻¹ L with hMdef
  have hMΩ : M ∈ Ω := h.hyp.conjInvariant n⁻¹ L hL
  have hMu : IsUniqueInvolution M u₀ := by
    have hc := hz.conj n⁻¹
    rw [hzeq] at hc
    have e : n⁻¹ * (n * u₀ * n⁻¹) * n⁻¹⁻¹ = u₀ := by group
    rwa [e] at hc
  have hMV : M ∈ dew1V Ω u₀ := ⟨hMΩ, hMu⟩
  have hLM : L = conjSub n M := by rw [hMdef, conjSub_conjSub_inv]
  have hy : n⁻¹ * x * n ∈ X :=
    (Subgroup.mem_normalizer_iff.mp hn (n⁻¹ * x * n)).mpr
      (by rw [show n * (n⁻¹ * x * n) * n⁻¹ = x by group]; exact hx)
  have hyM : conjSub (n⁻¹ * x * n) M = M := hV M hMV _ hy
  have hx' : x = n * (n⁻¹ * x * n) * n⁻¹ := by group
  rw [hLM]
  rw [hx', conjSub_mul, conjSub_mul, conjSub_inv_conjSub, hyM]

theorem dew1_eq_bot_of_normal_all {Ω : Set (Subgroup G)} (h : DEHyp Ω) {X : Subgroup G}
    (hXC : X ≤ Subgroup.centralizer (zGroup Ω : Set G)) (hX3 : IsPGroup 3 X)
    (hall : ∀ L ∈ Ω, ∀ x ∈ X, conjSub x L = L) : X = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hX3) ⟨x, hx⟩
  have hord : orderOf x = 3 ^ k := by
    have h1 := Subgroup.orderOf_coe (⟨x, hx⟩ : X)
    rw [hk] at h1
    exact h1
  have hodd : Odd (orderOf x) := by
    rw [hord]; exact Odd.pow (by decide)
  obtain ⟨m, hm⟩ := hodd
  have hxp : x ^ (2 * m + 1) = 1 := by rw [← hm]; exact pow_orderOf_eq_one x
  apply dew1_eq_one_of_odd_central h (hXC hx) hxp
  intro L hL
  rw [mem_normalizer_iff_conjSub_eq]
  exact hall L hL x hx

theorem dew1_unique_fixed {Ω : Set (Subgroup G)} (h : DEHyp Ω)
    (h4 : ∀ K ∈ Ω, (twinSet Ω K).ncard = 4) {R X : Subgroup G}
    (hRC : R ≤ Subgroup.centralizer (zGroup Ω : Set G))
    (hXC : X ≤ Subgroup.centralizer (zGroup Ω : Set G)) (hX3 : IsPGroup 3 X) (hXbot : X ≠ ⊥)
    (hfrat : ∀ g : G, ∃ n ∈ Subgroup.normalizer (X : Set G), ∃ r ∈ R, g = n * r)
    {K₀ : Subgroup G} (hK₀ : K₀ ∈ Ω) {u₀ : G} (hu₀ : IsUniqueInvolution K₀ u₀) :
    ∃ K ∈ Ω, IsUniqueInvolution K u₀ ∧ (∀ x ∈ X, conjSub x K = K) ∧
      ∀ K' ∈ Ω, IsUniqueInvolution K' u₀ → (∀ x ∈ X, conjSub x K' = K') → K' = K := by
  rcases dew1_three_dichotomy h h4 hXC hX3 hK₀ hu₀ with hF | hF1
  · exfalso
    apply hXbot
    apply dew1_eq_bot_of_normal_all h hXC hX3
    apply dew1_all_members h hRC hfrat hK₀ hu₀
    intro M hM x hx
    have hMF : M ∈ ({M | M ∈ dew1V Ω u₀ ∧ ∀ s ∈ X, conjSub s M = M} : Set (Subgroup G)) := by
      rw [hF]; exact hM
    exact hMF.2 x hx
  · obtain ⟨K, hK⟩ := Set.ncard_eq_one.mp hF1
    have hKF : K ∈ ({M | M ∈ dew1V Ω u₀ ∧ ∀ s ∈ X, conjSub s M = M} : Set (Subgroup G)) := by
      rw [hK]; rfl
    refine ⟨K, hKF.1.1, hKF.1.2, hKF.2, fun K' hK' hK'u hK'n => ?_⟩
    have hK'F : K' ∈ ({M | M ∈ dew1V Ω u₀ ∧ ∀ s ∈ X, conjSub s M = M} : Set (Subgroup G)) :=
      ⟨⟨hK', hK'u⟩, hK'n⟩
    rw [hK] at hK'F
    exact hK'F

theorem dew1_normalizer_le {Ω : Set (Subgroup G)} (h : DEHyp Ω) {X : Subgroup G} {u₀ : G}
    {K : Subgroup G} (hK : K ∈ Ω) (hKu : IsUniqueInvolution K u₀)
    (hKX : ∀ x ∈ X, conjSub x K = K)
    (huniq : ∀ K' ∈ Ω, IsUniqueInvolution K' u₀ → (∀ x ∈ X, conjSub x K' = K') → K' = K)
    {n : G} (hnC : n ∈ Subgroup.centralizer (zGroup Ω : Set G))
    (hnX : n ∈ Subgroup.normalizer (X : Set G)) :
    n ∈ Subgroup.normalizer (K : Set G) := by
  rw [mem_normalizer_iff_conjSub_eq]
  have hmem : conjSub n K ∈ dew1V Ω u₀ := dew1_conj_mem h hnC ⟨hK, hKu⟩
  have hX : ∀ x ∈ X, conjSub x (conjSub n K) = conjSub n K := by
    intro x hx
    have hy : n⁻¹ * x * n ∈ X :=
      (Subgroup.mem_normalizer_iff.mp hnX (n⁻¹ * x * n)).mpr
        (by rw [show n * (n⁻¹ * x * n) * n⁻¹ = x by group]; exact hx)
    have hx' : x = n * (n⁻¹ * x * n) * n⁻¹ := by group
    rw [hx', conjSub_mul, conjSub_mul, conjSub_inv_conjSub, hKX _ hy]
  exact huniq (conjSub n K) hmem.1 hmem.2 hX

open scoped commutatorElement in
theorem dew1_comm_mem {Ω : Set (Subgroup G)} (h : DEHyp Ω) {R X : Subgroup G}
    (hRC : R ≤ Subgroup.centralizer (zGroup Ω : Set G))
    (hXC : X ≤ Subgroup.centralizer (zGroup Ω : Set G))
    (hfrat : ∀ g : G, ∃ n ∈ Subgroup.normalizer (X : Set G), ∃ r ∈ R, g = n * r)
    (hR : ∀ r ∈ R, ∃ x ∈ X, ∃ q ∈ pCore 2 G, r = x * q)
    {K : Subgroup G} (hK : K ∈ Ω) {u₀ : G} (hu₀ : IsUniqueInvolution K u₀)
    (hKN : ∀ n ∈ Subgroup.centralizer (zGroup Ω : Set G),
      n ∈ Subgroup.normalizer (X : Set G) → n ∈ Subgroup.normalizer (K : Set G))
    {c : G} (hc : c ∈ Subgroup.centralizer (zGroup Ω : Set G)) {k : G} (hk : k ∈ K) :
    c * k * c⁻¹ * k⁻¹ ∈ pCore 2 G := by
  obtain ⟨n, hn, r, hr, hcnr⟩ := hfrat c
  have hrC : r ∈ Subgroup.centralizer (zGroup Ω : Set G) := hRC hr
  have hnC : n ∈ Subgroup.centralizer (zGroup Ω : Set G) := by
    have : n = c * r⁻¹ := by rw [hcnr]; group
    rw [this]
    exact (Subgroup.centralizer (zGroup Ω : Set G)).mul_mem hc
      ((Subgroup.centralizer (zGroup Ω : Set G)).inv_mem hrC)
  obtain ⟨x, hx, q, hq, hrxq⟩ := hR r hr
  have hn'X : n * x ∈ Subgroup.normalizer (X : Set G) :=
    (Subgroup.normalizer (X : Set G)).mul_mem hn (Subgroup.le_normalizer hx)
  have hn'C : n * x ∈ Subgroup.centralizer (zGroup Ω : Set G) :=
    (Subgroup.centralizer (zGroup Ω : Set G)).mul_mem hnC (hXC hx)
  have hn'K : n * x ∈ Subgroup.normalizer (K : Set G) := hKN _ hn'C hn'X
  have hcq : c = (n * x) * q := by rw [hcnr, hrxq]; group
  have ht : (n * x) * k * (n * x)⁻¹ * k⁻¹ ∈ pCore 2 G := by
    have htK : (n * x) * k * (n * x)⁻¹ * k⁻¹ ∈ K := by
      apply K.mul_mem
      · exact (Subgroup.mem_normalizer_iff.mp hn'K k).mp hk
      · exact K.inv_mem hk
    have htC : (n * x) * k * (n * x)⁻¹ * k⁻¹ ∈ Subgroup.centralizer (zGroup Ω : Set G) := by
      have e : (n * x) * k * (n * x)⁻¹ * k⁻¹ = (n * x) * (k * (n * x)⁻¹ * k⁻¹) := by group
      rw [e]
      exact (Subgroup.centralizer (zGroup Ω : Set G)).mul_mem hn'C
        (h.centralizer_zGroup_normal.conj_mem _
          ((Subgroup.centralizer (zGroup Ω : Set G)).inv_mem hn'C) k)
    have hmem := htC
    have hinf := (Subgroup.mem_inf).mpr ⟨htK, htC⟩
    rw [h.inf_centralizer_zGroup hK hu₀] at hinf
    have hu₀Q : u₀ ∈ pCore 2 G := h.zGroup_le_pCore (dew1_involution_mem h hK hu₀)
    exact (Subgroup.zpowers_le.mpr hu₀Q) hinf
  have hq' : (n * x) * q * (n * x)⁻¹ ∈ pCore 2 G :=
    Subgroup.Normal.conj_mem CFSG.pCore_normal q hq (n * x)
  have key : c * k * c⁻¹ * k⁻¹ =
      ((n * x) * q * (n * x)⁻¹ * ((n * x) * k * (n * x)⁻¹ * k⁻¹)) *
        (k * ((n * x) * q * (n * x)⁻¹)⁻¹ * k⁻¹) := by
    rw [hcq]; group
  rw [key]
  apply (pCore 2 G).mul_mem
  · exact (pCore 2 G).mul_mem hq' ht
  · exact Subgroup.Normal.conj_mem CFSG.pCore_normal _ ((pCore 2 G).inv_mem hq') k

open scoped commutatorElement in
theorem dew1_central_mod {Ω : Set (Subgroup G)} (h : DEHyp Ω) {K : Subgroup G} (hK : K ∈ Ω)
    (hcomm : ∀ c ∈ Subgroup.centralizer (zGroup Ω : Set G), ∀ k ∈ K,
      c * k * c⁻¹ * k⁻¹ ∈ pCore 2 G)
    {c : G} (hc : c ∈ Subgroup.centralizer (zGroup Ω : Set G)) (g : G) :
    ⁅c, g⁆ ∈ pCore 2 G := by
  classical
  haveI : (pCore 2 G).Normal := CFSG.pCore_normal
  set π : G →* G ⧸ pCore 2 G := QuotientGroup.mk' (pCore 2 G) with hπ
  let T : Subgroup G := (Subgroup.centralizer ({π c} : Set (G ⧸ pCore 2 G))).comap π
  have hT : pSpan Ω ≤ T := by
    apply pSpan_le
    intro L hL l hl
    obtain ⟨g₀, hg₀⟩ := h.trans K hK L hL
    have hk : g₀⁻¹ * l * g₀ ∈ K := by
      rw [← hg₀] at hl
      exact mem_conjSub_iff.mp hl
    have hcg : g₀⁻¹ * c * g₀ ∈ Subgroup.centralizer (zGroup Ω : Set G) := by
      have := h.centralizer_zGroup_normal.conj_mem c hc g₀⁻¹
      simpa using this
    have hcl : c * l * c⁻¹ * l⁻¹ ∈ pCore 2 G := by
      have e : c * l * c⁻¹ * l⁻¹ = g₀ * ((g₀⁻¹ * c * g₀) * (g₀⁻¹ * l * g₀) *
          (g₀⁻¹ * c * g₀)⁻¹ * (g₀⁻¹ * l * g₀)⁻¹) * g₀⁻¹ := by group
      rw [e]
      exact Subgroup.Normal.conj_mem CFSG.pCore_normal _ (hcomm _ hcg _ hk) g₀
    show π l ∈ Subgroup.centralizer ({π c} : Set (G ⧸ pCore 2 G))
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    have h1 : π ⁅c, l⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr (by
      rw [commutatorElement_def]; exact hcl)
    rw [map_commutatorElement] at h1
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  have hg : g ∈ T := hT (by rw [h.gen]; exact Subgroup.mem_top g)
  have hgT : π c * π g = π g * π c := by
    have := hg
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff] at this
    exact this (π c) (Set.mem_singleton _)
  have h2 : π ⁅c, g⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hgT
  exact (QuotientGroup.eq_one_iff _).mp h2

theorem dew1_index_56 {j m i : ℕ} (hj : 3 ^ j * i = 168 * 3 ^ m) (h3 : ¬ 3 ∣ i) :
    i = 56 ∧ j = m + 1 := by
  have hi0 : i ≠ 0 := by rintro rfl; simp at h3
  have hfac : (3 ^ j * i).factorization 3 = (168 * 3 ^ m).factorization 3 := by rw [hj]
  rw [Nat.factorization_mul (pow_ne_zero _ (by norm_num)) hi0,
    Nat.factorization_mul (by norm_num) (pow_ne_zero _ (by norm_num))] at hfac
  have h168 : (168 : ℕ).factorization 3 = 1 := by
    have : (168 : ℕ) = 3 * 56 := by norm_num
    rw [this, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_self Nat.prime_three,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 56)]
  have hi3 : i.factorization 3 = 0 := Nat.factorization_eq_zero_of_not_dvd h3
  simp only [Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply,
    Nat.Prime.factorization_self Nat.prime_three, smul_eq_mul, mul_one, hi3, h168] at hfac
  have hjm : j = m + 1 := by omega
  subst hjm
  have h2 : 3 ^ (m + 1) * i = 3 ^ (m + 1) * 56 := by rw [hj]; ring
  exact ⟨Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num) _) h2, rfl⟩

open scoped IsMulCommutative in
theorem dew1_central_three_trivial {Γ : Type} [Group Γ] [Finite Γ] {A : Subgroup Γ}
    (hperf : commutator Γ = ⊤) (hAc : ∀ a ∈ A, ∀ g : Γ, a * g = g * a)
    (hA3 : IsPGroup 3 A) (hcard : Nat.card Γ = 168 * Nat.card A) : A = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI hAn : A.Normal := ⟨fun a ha g => by
    have e : g * a * g⁻¹ = a := by rw [← hAc a ha g]; group
    rw [e]; exact ha⟩
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp hA3
  obtain ⟨P⟩ : Nonempty (Sylow 3 Γ) := inferInstance
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card).mp P.isPGroup'
  have hidx : 3 ^ j * (P : Subgroup Γ).index = 168 * 3 ^ m := by
    have h1 := (P : Subgroup Γ).index_mul_card
    rw [hj, hcard, hm, mul_comm] at h1
    exact h1
  obtain ⟨hi56, hjm⟩ := dew1_index_56 hidx P.not_dvd_index
  set Pg : Subgroup Γ := (P : Subgroup Γ) with hPg
  have hAP : A ≤ Pg := IsPGroup.le_sylow_of_normal hA3 P
  have hPcomm : ∀ x y : Pg, x * y = y * x := by
    have hAle : A.subgroupOf Pg ≤ Subgroup.center Pg := by
      intro x hx
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact (hAc (x : Γ) (Subgroup.mem_subgroupOf.mp hx) (y : Γ)).symm
    have hcardA : Nat.card (A.subgroupOf Pg) = 3 ^ m := by
      rw [← hm]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAP).toEquiv
    have hidxA : (A.subgroupOf Pg).index = 3 := by
      have h1 := (A.subgroupOf Pg).index_mul_card
      rw [hcardA, hj, hjm] at h1
      have h2 : (A.subgroupOf Pg).index * 3 ^ m = 3 * 3 ^ m := by
        rw [h1, pow_succ]; ring
      exact Nat.eq_of_mul_eq_mul_right (pow_pos (by norm_num) _) h2
    have hcenter_idx : (Subgroup.center Pg).index ∣ 3 := by
      rw [← hidxA]; exact Subgroup.index_dvd_of_le hAle
    rcases (Nat.dvd_prime Nat.prime_three).mp hcenter_idx with h1 | h1
    · have htop : Subgroup.center Pg = ⊤ := Subgroup.index_eq_one.mp h1
      intro x y
      have hy : y ∈ Subgroup.center Pg := by rw [htop]; exact Subgroup.mem_top y
      exact Subgroup.mem_center_iff.mp hy x
    · haveI : IsCyclic (Pg ⧸ Subgroup.center Pg) := by
        apply isCyclic_of_prime_card (p := 3)
        exact h1
      intro x y
      exact commutative_of_cyclic_center_quotient (QuotientGroup.mk' (Subgroup.center Pg))
        (QuotientGroup.ker_mk' _).le x y
  haveI : IsMulCommutative Pg := ⟨⟨fun a b => hPcomm a b⟩⟩
  let t : Γ →* Pg := MonoidHom.transfer (MonoidHom.id Pg)
  have ht1 : ∀ g : Γ, t g = 1 := by
    have hker : commutator Γ ≤ t.ker := by
      apply Subgroup.commutator_le.mpr
      intro x _ y _
      rw [MonoidHom.mem_ker, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm' _ _)
    intro g
    have hg : g ∈ commutator Γ := by rw [hperf]; exact Subgroup.mem_top g
    exact MonoidHom.mem_ker.mp (hker hg)
  have hpow : ∀ a ∈ A, a ^ 56 = 1 := by
    intro a ha
    have hkey : ∀ (k : ℕ) (g₀ : Γ), g₀⁻¹ * a ^ k * g₀ ∈ Pg → g₀⁻¹ * a ^ k * g₀ = a ^ k := by
      intro k g₀ _
      have hc : a ^ k * g₀ = g₀ * a ^ k := (show Commute a g₀ from hAc a ha g₀).pow_left k
      calc g₀⁻¹ * a ^ k * g₀ = g₀⁻¹ * (a ^ k * g₀) := by group
        _ = g₀⁻¹ * (g₀ * a ^ k) := by rw [hc]
        _ = a ^ k := by group
    have htt := MonoidHom.transfer_eq_pow (MonoidHom.id Pg) a hkey
    have h1 : t a = 1 := ht1 a
    have h2 : (MonoidHom.transfer (MonoidHom.id Pg)) a = 1 := h1
    rw [htt, MonoidHom.id_apply] at h2
    have h3 := congrArg Subtype.val h2
    simp only [Subgroup.coe_one] at h3
    rw [← hi56]
    exact h3
  rw [eq_bot_iff]
  intro a ha
  rw [Subgroup.mem_bot]
  obtain ⟨i, hi⟩ := (IsPGroup.iff_orderOf.mp hA3) ⟨a, ha⟩
  have hord : orderOf a = 3 ^ i := by
    have h1 := Subgroup.orderOf_coe (⟨a, ha⟩ : A)
    rw [hi] at h1
    exact h1
  have hdvd : orderOf a ∣ 56 := orderOf_dvd_of_pow_eq_one (hpow a ha)
  rw [hord] at hdvd
  have hi0 : i = 0 := by
    by_contra hne
    have h3 : 3 ∣ 56 := (dvd_pow_self 3 hne).trans hdvd
    norm_num at h3
  have hord1 : orderOf a = 1 := by rw [hord, hi0, pow_zero]
  exact orderOf_eq_one_iff.mp hord1

open scoped commutatorElement in
theorem dew1_pCore_eq_centralizer {Ω : Set (Subgroup G)} (h : DEHyp Ω)
    (h4 : ∀ K ∈ Ω, (twinSet Ω K).ncard = 4) :
    pCore 2 G = Subgroup.centralizer (zGroup Ω : Set G) := by
  classical
  haveI hQn : (pCore 2 G).Normal := CFSG.pCore_normal
  have hQC : pCore 2 G ≤ Subgroup.centralizer (zGroup Ω : Set G) :=
    h.pCore_le_centralizer_zGroup
  by_contra hne
  have hCn : (Subgroup.centralizer (zGroup Ω : Set G)).Normal := h.centralizer_zGroup_normal
  have hsolv : Group.IsSolvable ↥(Subgroup.centralizer (zGroup Ω : Set G)) :=
    dew1_isSolvable_centralizer h h4
  have hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card ↥(Subgroup.centralizer (zGroup Ω : Set G)) →
      p = 2 ∨ p = 3 := fun p hp hpd => dew1_prime_dvd_centralizer h h4 hp hpd
  obtain ⟨R, hRn, hQR, hRC, hRQ, hRcomm⟩ :=
    dew1_exists_R hCn hQC hsolv hne
  haveI := hRn
  have hM2R : ∀ x ∈ R, ∀ k : ℕ, x ^ (2 ^ k) ∈ pCore 2 G → x ∈ pCore 2 G :=
    fun x hx k hxk => dew1_mod_two hQR hRcomm hx hxk
  have hprimeR : ∀ p : ℕ, p.Prime → p ∣ Nat.card R → p = 2 ∨ p = 3 := fun p hp hpd =>
    hprime p hp (hpd.trans (Subgroup.card_dvd_of_le hRC))
  obtain ⟨P, hR_xq, hXbot⟩ := dew1_sylow_three hQR hM2R hprimeR (Ne.symm hRQ)
  set X : Subgroup G := (P : Subgroup R).map R.subtype with hXdef
  have hXC : X ≤ Subgroup.centralizer (zGroup Ω : Set G) := by
    intro x hx
    obtain ⟨y, _, rfl⟩ := Subgroup.mem_map.mp hx
    exact hRC y.2
  have hX3 : IsPGroup 3 X := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp P.isPGroup'
    apply IsPGroup.of_card (n := n)
    rw [hXdef, Subgroup.card_map_of_injective R.subtype_injective, hn]
  have hfrat : ∀ g : G, ∃ n ∈ Subgroup.normalizer (X : Set G), ∃ r ∈ R, g = n * r :=
    fun g => dew1_frattini P g
  obtain ⟨L₀, hL₀, -⟩ := h.exists_ne
  obtain ⟨u₀, hu₀⟩ := h.exists_isUniqueInvolution hL₀
  obtain ⟨K, hK, hKu, hKX, huniq⟩ :=
    dew1_unique_fixed h h4 hRC hXC hX3 hXbot hfrat hL₀ hu₀
  have hKN : ∀ n ∈ Subgroup.centralizer (zGroup Ω : Set G),
      n ∈ Subgroup.normalizer (X : Set G) → n ∈ Subgroup.normalizer (K : Set G) :=
    fun n hnC hnX => dew1_normalizer_le h hK hKu hKX huniq hnC hnX
  have hcommK : ∀ c ∈ Subgroup.centralizer (zGroup Ω : Set G), ∀ k ∈ K,
      c * k * c⁻¹ * k⁻¹ ∈ pCore 2 G :=
    fun c hc k hk => dew1_comm_mem h hRC hXC hfrat hR_xq hK hKu hKN hc hk
  have hcentral : ∀ c ∈ Subgroup.centralizer (zGroup Ω : Set G), ∀ g : G,
      ⁅c, g⁆ ∈ pCore 2 G :=
    fun c hc g => dew1_central_mod h hK hcommK hc g
  have hM2C : ∀ x ∈ Subgroup.centralizer (zGroup Ω : Set G), ∀ k : ℕ,
      x ^ (2 ^ k) ∈ pCore 2 G → x ∈ pCore 2 G :=
    fun x hx k hxk => dew1_mod_two hQC (fun x hx' y _ => hcentral x hx' y) hx hxk
  let π : G →* G ⧸ pCore 2 G := QuotientGroup.mk' (pCore 2 G)
  let A : Subgroup (G ⧸ pCore 2 G) := (Subgroup.centralizer (zGroup Ω : Set G)).map π
  have hCcard : Nat.card ↥(Subgroup.centralizer (zGroup Ω : Set G)) =
      Nat.card A * Nat.card ↥(pCore 2 G) := by
    let ρ : ↥(Subgroup.centralizer (zGroup Ω : Set G)) →* G ⧸ pCore 2 G :=
      π.comp (Subgroup.centralizer (zGroup Ω : Set G)).subtype
    have hrange : ρ.range = A := by
      ext x
      constructor
      · rintro ⟨c, rfl⟩
        exact Subgroup.mem_map.mpr ⟨c.1, c.2, rfl⟩
      · intro hx
        obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hx
        exact ⟨⟨c, hc⟩, rfl⟩
    have hker : ρ.ker = (pCore 2 G).subgroupOf (Subgroup.centralizer (zGroup Ω : Set G)) := by
      ext c
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      exact QuotientGroup.eq_one_iff _
    have h1 := Subgroup.card_ker_mul_card_range ρ
    rw [hrange, hker] at h1
    have h2 : Nat.card ↥((pCore 2 G).subgroupOf (Subgroup.centralizer (zGroup Ω : Set G))) =
        Nat.card ↥(pCore 2 G) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQC).toEquiv
    rw [h2, mul_comm] at h1
    exact h1.symm
  have hGcard : Nat.card (G ⧸ pCore 2 G) = 168 * Nat.card A := by
    have h1 := (Subgroup.centralizer (zGroup Ω : Set G)).card_mul_index
    rw [h.index_centralizer_zGroup] at h1
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (pCore 2 G)
    have hQpos : 0 < Nat.card ↥(pCore 2 G) := Nat.card_pos
    have h3 : Nat.card (G ⧸ pCore 2 G) * Nat.card ↥(pCore 2 G) =
        (168 * Nat.card A) * Nat.card ↥(pCore 2 G) := by
      rw [← h2, ← h1, hCcard]; ring
    exact Nat.eq_of_mul_eq_mul_right hQpos h3
  have hperf : commutator (G ⧸ pCore 2 G) = ⊤ := by
    have key : Subgroup.map π (commutator G) = commutator (G ⧸ pCore 2 G) := by
      unfold commutator
      rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective _
        (QuotientGroup.mk'_surjective _)]
    rw [eq_top_iff]
    intro x _
    obtain ⟨g', rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 G) x
    rw [← key]
    exact Subgroup.mem_map_of_mem _ (by rw [h.commutator_eq_top]; exact Subgroup.mem_top _)
  have hAc : ∀ a ∈ A, ∀ g : G ⧸ pCore 2 G, a * g = g * a := by
    intro a ha g
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨g', rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 G) g
    have h1 : π ⁅c, g'⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr (hcentral c hc g')
    rw [map_commutatorElement] at h1
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  haveI hAn : A.Normal := ⟨fun a ha g => by
    have e : g * a * g⁻¹ = a := by rw [← hAc a ha g]; group
    rw [e]; exact ha⟩
  have hA3 : IsPGroup 3 A := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hodd : ∀ p : ℕ, p.Prime → p ∣ Nat.card A → p = 3 := by
      intro p hp hpd
      have hpC : p ∣ Nat.card ↥(Subgroup.centralizer (zGroup Ω : Set G)) := by
        rw [hCcard]; exact Dvd.dvd.mul_right hpd _
      rcases hprime p hp hpC with rfl | rfl
      · exfalso
        haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' 2 hpd
        obtain ⟨c, hc, hca⟩ := Subgroup.mem_map.mp a.2
        have hsq : (a : G ⧸ pCore 2 G) ^ 2 = 1 := by
          have h1 := pow_orderOf_eq_one a
          rw [ha] at h1
          have h2 := congrArg Subtype.val h1
          simpa using h2
        have hc2 : c ^ (2 ^ 1) ∈ pCore 2 G := by
          have h3 : π (c ^ (2 ^ 1)) = 1 := by
            rw [pow_one, map_pow, hca]; exact hsq
          exact (QuotientGroup.eq_one_iff _).mp h3
        have hcQ : c ∈ pCore 2 G := hM2C c hc 1 hc2
        have ha1 : (a : G ⧸ pCore 2 G) = 1 := by
          rw [← hca]; exact (QuotientGroup.eq_one_iff c).mpr hcQ
        have ha2 : a = 1 := Subtype.ext ha1
        rw [ha2, orderOf_one] at ha
        norm_num at ha
      · rfl
    obtain ⟨k, hk⟩ : ∃ k, Nat.card ↥A = 3 ^ k :=
      ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne'
        (fun {d} hd hdn => hodd d hd hdn)⟩
    exact IsPGroup.of_card hk
  have hA_bot : A = ⊥ := dew1_central_three_trivial hperf hAc hA3 hGcard
  have hCQ : Subgroup.centralizer (zGroup Ω : Set G) ≤ pCore 2 G := by
    intro c hc
    have h1 : π c ∈ A := Subgroup.mem_map.mpr ⟨c, hc, rfl⟩
    rw [hA_bot, Subgroup.mem_bot] at h1
    exact (QuotientGroup.eq_one_iff c).mp h1
  exact hne (le_antisymm hQC hCQ)

section Dew2

variable {Ω : Set (Subgroup G)}

private theorem dew2_eq_one_or_eq_of_mem_zpowers {z x : G} (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (hx : x ∈ Subgroup.zpowers z) : x = 1 ∨ x = z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hord : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
  have hk : z ^ k = z ^ (k % (orderOf z : ℤ)) := (zpow_mod_orderOf z k).symm
  rw [hord] at hk
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · left
    rw [hk]
    have h0' : k % ((2 : ℕ) : ℤ) = 0 := by exact_mod_cast h0
    rw [h0']
    exact zpow_zero z
  · right
    rw [hk]
    have h1' : k % ((2 : ℕ) : ℤ) = 1 := by exact_mod_cast h1
    rw [h1']
    exact zpow_one z

private theorem dew2_commute_of_basis {e : Fin 3 → G} (hbas : TL4.E8Basis (zGroup Ω) e)
    {u : G} (hu : ∀ k, u * e k = e k * u) : ∀ d ∈ zGroup Ω, u * d = d * u := by
  intro d hd
  obtain ⟨v, rfl⟩ := TL4.exists_e8Coord_eq hbas hd
  have hc : Commute u (e 0) := hu 0
  have h1 : Commute u (e 1) := hu 1
  have h2 : Commute u (e 2) := hu 2
  unfold TL4.e8Coord
  exact ((hc.pow_right _).mul_right (h1.pow_right _)).mul_right (h2.pow_right _)

private theorem dew2_conjSub_commute {x g : G} {M : Subgroup G} (hg : Commute g x)
    (hM : ∀ m ∈ M, Commute m x) : ∀ m ∈ conjSub g M, Commute m x := by
  intro m hm
  rw [mem_conjSub_iff] at hm
  have hn := hM _ hm
  have hg' : Commute g⁻¹ x := hg.inv_left
  have hall : Commute (g * (g⁻¹ * m * g) * g⁻¹) x := (hg.mul_left hn).mul_left hg'
  have e : g * (g⁻¹ * m * g) * g⁻¹ = m := by group
  rwa [e] at hall

private theorem dew2_ncard_nonone (h : DEHyp Ω) :
    ({y : G | y ∈ zGroup Ω ∧ y ≠ 1} : Set G).ncard = 7 := by
  have e : ({y : G | y ∈ zGroup Ω ∧ y ≠ 1} : Set G) =
      Subtype.val '' {x : zGroup Ω | x ≠ 1} := by
    ext y
    constructor
    · rintro ⟨hy, hy1⟩
      exact ⟨⟨y, hy⟩, fun h1 => hy1 (congrArg Subtype.val h1), rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, fun h1 => hx (Subtype.ext h1)⟩
  rw [e, Set.ncard_image_of_injective _ Subtype.val_injective, ← Nat.card_coe_set_eq]
  exact h.card_zGroup_ne_one

private theorem dew2_conj_mem_coset (h : DEHyp Ω) {x : G} (hx : x ∈ pCore 2 G)
    (hxN : ∀ L ∈ Ω, x ∈ Subgroup.normalizer (L : Set G)) (g : G) :
    ∃ d ∈ zGroup Ω, g * x * g⁻¹ = x * d := by
  let T : Subgroup G :=
    { carrier := {g | ∃ d ∈ zGroup Ω, g * x * g⁻¹ = x * d}
      mul_mem' := by
        rintro a b ⟨d, hd, ha⟩ ⟨d', hd', hb⟩
        refine ⟨d * (a * d' * a⁻¹), (zGroup Ω).mul_mem hd
          (h.zGroup_normal.conj_mem d' hd' a), ?_⟩
        calc a * b * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by group
          _ = a * (x * d') * a⁻¹ := by rw [hb]
          _ = (a * x * a⁻¹) * (a * d' * a⁻¹) := by group
          _ = x * d * (a * d' * a⁻¹) := by rw [ha]
          _ = x * (d * (a * d' * a⁻¹)) := by group
      one_mem' := ⟨1, (zGroup Ω).one_mem, by group⟩
      inv_mem' := by
        rintro a ⟨d, hd, ha⟩
        refine ⟨a⁻¹ * d⁻¹ * a, ?_, ?_⟩
        · have := h.zGroup_normal.conj_mem d⁻¹ ((zGroup Ω).inv_mem hd) a⁻¹
          rwa [inv_inv] at this
        · have hd' : d = x⁻¹ * (a * x * a⁻¹) := by rw [ha]; group
          rw [hd']
          group }
  have hQn : (pCore 2 G).Normal := pCore_normal
  have hgen : pSpan Ω ≤ T := by
    refine pSpan_le fun L hL w hw => ?_
    obtain ⟨z, hz⟩ := h.exists_isUniqueInvolution hL
    have hxL : x * w⁻¹ * x⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hxN L hL) w⁻¹).mp (L.inv_mem hw)
    have hδL : w * x * w⁻¹ * x⁻¹ ∈ L := by
      have := L.mul_mem hw hxL
      simpa [mul_assoc] using this
    have hδQ : w * x * w⁻¹ * x⁻¹ ∈ pCore 2 G :=
      (pCore 2 G).mul_mem (hQn.conj_mem x hx w) ((pCore 2 G).inv_mem hx)
    have hδD : w * x * w⁻¹ * x⁻¹ ∈ zGroup Ω := by
      have hI : w * x * w⁻¹ * x⁻¹ ∈ L ⊓ pCore 2 G := ⟨hδL, hδQ⟩
      rw [h.inf_pCore hL hz] at hI
      exact (Subgroup.zpowers_le.mpr (h.mem_zGroup_iff.mpr (Or.inr ⟨L, hL, hz⟩))) hI
    have hdD' : x⁻¹ * (w * x * w⁻¹ * x⁻¹) * x ∈ zGroup Ω := by
      have := h.zGroup_normal.conj_mem _ hδD x⁻¹
      rwa [inv_inv] at this
    show ∃ d ∈ zGroup Ω, w * x * w⁻¹ = x * d
    exact ⟨x⁻¹ * (w * x * w⁻¹ * x⁻¹) * x, hdD', by group⟩
  have hg : g ∈ pSpan Ω := by
    rw [h.gen]
    exact Subgroup.mem_top g
  obtain ⟨d, hd, hgd⟩ := hgen hg
  exact ⟨d, hd, hgd⟩

private theorem dew2_inv_conj_of_commute {y a : G} (hya : Commute y a) : y⁻¹ * a * y = a := by
  calc y⁻¹ * a * y = y⁻¹ * (a * y) := by group
    _ = y⁻¹ * (y * a) := by rw [hya.eq]
    _ = a := by group

private theorem dew2_cube_conj {y : G} (hy3 : orderOf y = 3) (a : G) :
    y⁻¹ * (y⁻¹ * (y⁻¹ * a * y) * y) * y = a := by
  have hyyy : y * y * y = 1 := by
    have h1 := pow_orderOf_eq_one y
    rw [hy3, pow_three'] at h1
    exact h1
  have hinv : y⁻¹ * y⁻¹ * y⁻¹ = 1 := by
    calc y⁻¹ * y⁻¹ * y⁻¹ = (y * y * y)⁻¹ := by group
      _ = 1 := by rw [hyyy, inv_one]
  calc y⁻¹ * (y⁻¹ * (y⁻¹ * a * y) * y) * y = (y⁻¹ * y⁻¹ * y⁻¹) * a * (y * y * y) := by group
    _ = a := by rw [hinv, hyyy, one_mul, mul_one]

private theorem dew2_not_seven_dvd_class (h : DEHyp Ω) {x : G} (hx : x ∈ pCore 2 G)
    (hxN : ∀ L ∈ Ω, x ∈ Subgroup.normalizer (L : Set G)) (hxD : x ∉ zGroup Ω) :
    ¬ 7 ∣ (conjugatesOf x).ncard := by
  classical
  obtain ⟨X, hXdef⟩ : ∃ X : Set G, X = (fun d => x * d) '' (zGroup Ω : Set G) := ⟨_, rfl⟩
  have hmemX : ∀ y, y ∈ X ↔ ∃ d ∈ zGroup Ω, x * d = y := by
    intro y
    rw [hXdef]
    constructor
    · rintro ⟨d, hd, rfl⟩
      exact ⟨d, hd, rfl⟩
    · rintro ⟨d, hd, rfl⟩
      exact ⟨d, hd, rfl⟩
  have hXfin : X.Finite := Set.toFinite X
  have hXc : X.ncard = 8 := by
    rw [hXdef, Set.ncard_image_of_injective _ (mul_right_injective x), ← Nat.card_coe_set_eq]
    exact h.card_zGroup
  have hCX : conjugatesOf x ⊆ X := by
    intro y hy
    obtain ⟨c, hc⟩ := isConj_iff.mp hy
    obtain ⟨d, hd, hcd⟩ := dew2_conj_mem_coset h hx hxN c
    rw [hmemX]
    exact ⟨d, hd, by rw [← hcd]; exact hc⟩
  have hsub_card : (conjugatesOf x).ncard ≤ 8 := by
    rw [← hXc]
    exact Set.ncard_le_ncard hCX hXfin
  have hpos : 0 < (conjugatesOf x).ncard := by
    rw [Set.ncard_pos (Set.toFinite _)]
    exact ⟨x, IsConj.refl x⟩
  intro h7
  have hs7 : (conjugatesOf x).ncard = 7 := by omega
  have hdiff : (X \ conjugatesOf x).ncard = 1 := by
    have := Set.ncard_sdiff_add_ncard_of_subset hCX hXfin
    omega
  obtain ⟨x₁, hx₁⟩ := Set.ncard_eq_one.mp hdiff
  have hx₁mem : x₁ ∈ X \ conjugatesOf x := by
    rw [hx₁]
    exact Set.mem_singleton x₁
  have hcent : ∀ g : G, g * x₁ * g⁻¹ = x₁ := by
    intro g
    have hmem : g * x₁ * g⁻¹ ∈ X \ conjugatesOf x := by
      refine ⟨?_, ?_⟩
      · obtain ⟨d, hd, hxd⟩ := (hmemX x₁).mp hx₁mem.1
        obtain ⟨d', hd', hgd⟩ := dew2_conj_mem_coset h hx hxN g
        rw [hmemX]
        refine ⟨d' * (g * d * g⁻¹), (zGroup Ω).mul_mem hd' (h.zGroup_normal.conj_mem d hd g), ?_⟩
        calc x * (d' * (g * d * g⁻¹)) = (x * d') * (g * d * g⁻¹) := by group
          _ = (g * x * g⁻¹) * (g * d * g⁻¹) := by rw [hgd]
          _ = g * (x * d) * g⁻¹ := by group
          _ = g * x₁ * g⁻¹ := by rw [hxd]
      · intro hc
        apply hx₁mem.2
        obtain ⟨c, hc'⟩ := isConj_iff.mp hc
        refine isConj_iff.mpr ⟨g⁻¹ * c, ?_⟩
        calc g⁻¹ * c * x * (g⁻¹ * c)⁻¹ = g⁻¹ * (c * x * c⁻¹) * g := by group
          _ = g⁻¹ * (g * x₁ * g⁻¹) * g := by rw [hc']
          _ = x₁ := by group
    rw [hx₁] at hmem
    exact hmem
  have hxc : x₁ ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    calc g * x₁ = (g * x₁ * g⁻¹) * g := by group
      _ = x₁ * g := by rw [hcent g]
  rw [h.center, Subgroup.mem_bot] at hxc
  obtain ⟨d, hd, hxd⟩ := (hmemX x₁).mp hx₁mem.1
  apply hxD
  have hxeq : x = d⁻¹ := by
    calc x = x * d * d⁻¹ := by group
      _ = x₁ * d⁻¹ := by rw [hxd]
      _ = d⁻¹ := by rw [hxc, one_mul]
  rw [hxeq]
  exact (zGroup Ω).inv_mem hd

private theorem dew2_seven_dvd_centralizer (h : DEHyp Ω) {x : G} (hx : x ∈ pCore 2 G)
    (hxN : ∀ L ∈ Ω, x ∈ Subgroup.normalizer (L : Set G)) (hxD : x ∉ zGroup Ω) :
    7 ∣ Nat.card (Subgroup.centralizer ({x} : Set G)) := by
  have hcard := Subgroup.card_mul_index (Subgroup.centralizer ({x} : Set G))
  rw [Subgroup.index_centralizer_eq_ncard] at hcard
  have h168 := Subgroup.card_mul_index (Subgroup.centralizer (zGroup Ω : Set G))
  rw [h.index_centralizer_zGroup] at h168
  have h7G : 7 ∣ Nat.card G :=
    Dvd.dvd.trans (by norm_num : (7 : ℕ) ∣ 168) (Dvd.intro_left _ h168)
  rw [← hcard] at h7G
  rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 7)).mp h7G with h1 | h1
  · exact h1
  · exact absurd h1 (dew2_not_seven_dvd_class h hx hxN hxD)

private theorem dew2_exists_order_seven (h : DEHyp Ω) {x : G} (hx : x ∈ pCore 2 G)
    (hxN : ∀ L ∈ Ω, x ∈ Subgroup.normalizer (L : Set G)) (hxD : x ∉ zGroup Ω) :
    ∃ g : G, orderOf g = 7 ∧ g * x = x * g := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 7 (dew2_seven_dvd_centralizer h hx hxN hxD)
  exact ⟨(c : G), (Subgroup.orderOf_coe c).trans hc,
    Subgroup.mem_centralizer_singleton_iff.mp c.2⟩

private theorem dew2_fixed_free (h : DEHyp Ω)
    (hC : Subgroup.centralizer (zGroup Ω : Set G) = pCore 2 G)
    {g : G} (hg7 : orderOf g = 7) {δ : G} (hδ : δ ∈ zGroup Ω) (hδ1 : δ ≠ 1) :
    g * δ * g⁻¹ ≠ δ := by
  intro hfix
  have hcls : conjugatesOf δ = {y : G | y ∈ zGroup Ω ∧ y ≠ 1} := by
    ext y
    constructor
    · intro hy
      obtain ⟨c, hc⟩ := isConj_iff.mp hy
      refine ⟨?_, ?_⟩
      · rw [← hc]
        exact h.zGroup_normal.conj_mem δ hδ c
      · intro h1
        apply hδ1
        calc δ = c⁻¹ * (c * δ * c⁻¹) * c := by group
          _ = c⁻¹ * y * c := by rw [hc]
          _ = 1 := by rw [h1]; group
    · rintro ⟨hyD, hy1⟩
      obtain ⟨L, hL, hyinv⟩ : ∃ L ∈ Ω, IsUniqueInvolution L y := by
        rcases h.mem_zGroup_iff.mp hyD with h1 | h1
        · exact absurd h1 hy1
        · exact h1
      obtain ⟨L', hL', hδinv⟩ : ∃ L' ∈ Ω, IsUniqueInvolution L' δ := by
        rcases h.mem_zGroup_iff.mp hδ with h1 | h1
        · exact absurd h1 hδ1
        · exact h1
      obtain ⟨g', hg'⟩ := h.exists_conj_involution hL' hL hδinv hyinv
      exact isConj_iff.mpr ⟨g', hg'⟩
  have hidx : (Subgroup.centralizer ({δ} : Set G)).index = 7 := by
    rw [Subgroup.index_centralizer_eq_ncard, hcls, dew2_ncard_nonone h]
  have hgC : g ∈ Subgroup.centralizer ({δ} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hfix)
  have h7C : 7 ∣ Nat.card (Subgroup.centralizer ({δ} : Set G)) := by
    have hd := orderOf_dvd_natCard (⟨g, hgC⟩ : Subgroup.centralizer ({δ} : Set G))
    rw [Subgroup.orderOf_mk, hg7] at hd
    exact hd
  have hG : Nat.card G = Nat.card (Subgroup.centralizer ({δ} : Set G)) * 7 := by
    rw [← hidx, Subgroup.card_mul_index]
  have hG2 : Nat.card G = 168 * Nat.card (pCore 2 G) := by
    have hh := Subgroup.card_mul_index (Subgroup.centralizer (zGroup Ω : Set G))
    rw [h.index_centralizer_zGroup, hC] at hh
    rw [← hh]
    ring
  have h7Q : ¬ 7 ∣ Nat.card (pCore 2 G) := by
    intro h7
    haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 7 h7
    have hord : orderOf (c : G) = 7 := (Subgroup.orderOf_coe c).trans hc
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := G)) c
    have hk' : (c : G) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h7k : 7 ∣ 2 ^ k := by
      rw [← hord]
      exact orderOf_dvd_of_pow_eq_one hk'
    have h72 : 7 ∣ 2 := Nat.Prime.dvd_of_dvd_pow (by norm_num) h7k
    norm_num at h72
  omega

private theorem dew2_orbit_surj (h : DEHyp Ω) {g : G} (hg7 : orderOf g = 7)
    (hfree : ∀ δ ∈ zGroup Ω, δ ≠ 1 → g * δ * g⁻¹ ≠ δ) {δ δ' : G}
    (hδ : δ ∈ zGroup Ω) (hδ1 : δ ≠ 1) (hδ' : δ' ∈ zGroup Ω) (hδ'1 : δ' ≠ 1) :
    ∃ k : ℕ, g ^ k * δ * (g ^ k)⁻¹ = δ' := by
  classical
  have hcD : ∀ k : ℕ, g ^ k * δ * (g ^ k)⁻¹ ∈ zGroup Ω := fun k =>
    h.zGroup_normal.conj_mem δ hδ (g ^ k)
  have hc1 : ∀ k : ℕ, g ^ k * δ * (g ^ k)⁻¹ ≠ 1 := by
    intro k hk
    apply hδ1
    calc δ = (g ^ k)⁻¹ * (g ^ k * δ * (g ^ k)⁻¹) * g ^ k := by group
      _ = 1 := by rw [hk]; group
  have hmpow : ∀ m : ℕ, 0 < m → m < 7 → g ^ m * δ * (g ^ m)⁻¹ = δ → False := by
    intro m hm0 hm7 hm
    have hcomm : Commute (g ^ m) δ := mul_inv_eq_iff_eq_mul.mp hm
    have hmod : m ^ 6 % 7 = 1 := by
      interval_cases m <;> norm_num
    have hpow : (g ^ m) ^ (m ^ 5) = g := by
      rw [← pow_mul, show m * m ^ 5 = m ^ 6 by ring, ← pow_mod_orderOf g, hg7, hmod, pow_one]
    have hgc : Commute g δ := by
      have := hcomm.pow_left (m ^ 5)
      rwa [hpow] at this
    exact hfree δ hδ hδ1 (mul_inv_eq_iff_eq_mul.mpr hgc.eq)
  have hinj : ∀ a b : ℕ, a < b → b < 7 →
      g ^ a * δ * (g ^ a)⁻¹ ≠ g ^ b * δ * (g ^ b)⁻¹ := by
    intro a b hab hb heq
    have hb' : g ^ b = g ^ a * g ^ (b - a) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hb'] at heq
    apply hmpow (b - a) (Nat.sub_pos_of_lt hab) (by omega)
    calc g ^ (b - a) * δ * (g ^ (b - a))⁻¹
        = (g ^ a)⁻¹ * (g ^ a * g ^ (b - a) * δ * (g ^ a * g ^ (b - a))⁻¹) * g ^ a := by group
      _ = (g ^ a)⁻¹ * (g ^ a * δ * (g ^ a)⁻¹) * g ^ a := by rw [← heq]
      _ = δ := by group
  have hinjOn : Set.InjOn (fun k : ℕ => g ^ k * δ * (g ^ k)⁻¹)
      ((Finset.range 7 : Finset ℕ) : Set ℕ) := by
    intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact hinj a b hlt hb hab
    · exact hinj b a hgt ha hab.symm
  have hSc : ({y : G | y ∈ zGroup Ω ∧ y ≠ 1} : Set G).ncard = 7 := dew2_ncard_nonone h
  have hTc : ((fun k : ℕ => g ^ k * δ * (g ^ k)⁻¹) '' ((Finset.range 7 : Finset ℕ) : Set ℕ)).ncard
      = 7 := by
    rw [hinjOn.ncard_image, Set.ncard_coe_finset, Finset.card_range]
  have hTS : (fun k : ℕ => g ^ k * δ * (g ^ k)⁻¹) '' ((Finset.range 7 : Finset ℕ) : Set ℕ) ⊆
      {y : G | y ∈ zGroup Ω ∧ y ≠ 1} := by
    rintro _ ⟨k, -, rfl⟩
    exact ⟨hcD k, hc1 k⟩
  have hEq := Set.eq_of_subset_of_ncard_le hTS (by rw [hSc, hTc]) (Set.toFinite _)
  have hδ'T : δ' ∈
      (fun k : ℕ => g ^ k * δ * (g ^ k)⁻¹) '' ((Finset.range 7 : Finset ℕ) : Set ℕ) := by
    rw [hEq]
    exact ⟨hδ', hδ'1⟩
  obtain ⟨k, -, hkeq⟩ := hδ'T
  exact ⟨k, hkeq⟩

private theorem dew2_exists_u (h : DEHyp Ω) {L : Subgroup G} (hL : L ∈ Ω) {t z : G}
    (ht : IsUniqueInvolution L t) (hz : z ∈ zGroup Ω) :
    ∃ u ∈ L, u * u = t ∧ u * z = z * u ∧ ∃ w ∈ L, u * w ≠ w * u := by
  obtain ⟨i, j, hi, hj, hii, hjj, hji, -⟩ :=
    exists_q8_gen ht (h.isQuatSub_of_mem hL) (h.card L hL)
  have ht2 : t * t = 1 := ht.sq
  have ht1 : t ≠ 1 := ht.ne_one
  have htc : ∀ w ∈ L, w * t = t * w := by
    intro w hw
    have := conj_of_mem_mem ht hw (Or.inr rfl)
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this
  have hcancel : ∀ a : G, t * a = a → False := by
    intro a ha
    apply ht1
    have : t * a = 1 * a := by rw [one_mul]; exact ha
    exact mul_right_cancel this
  have hij_ne : i * j ≠ j * i := by
    intro e
    rw [hji] at e
    exact hcancel (i * j) e.symm
  have hzi : dComm z i ∈ Subgroup.zpowers t := h.dComm_mem_zpowers hL ht hz hi
  have hzj : dComm z j ∈ Subgroup.zpowers t := h.dComm_mem_zpowers hL ht hz hj
  have hzi' := dew2_eq_one_or_eq_of_mem_zpowers ht2 ht1 hzi
  have hzj' := dew2_eq_one_or_eq_of_mem_zpowers ht2 ht1 hzj
  have hdN : z ∈ Subgroup.normalizer (L : Set G) := h.dNorm L hL hz
  rcases hzi' with hzi1 | hzit
  · exact ⟨i, hi, hii, (dComm_eq_one_iff.mp hzi1).symm, j, hj, hij_ne⟩
  · rcases hzj' with hzj1 | hzjt
    · exact ⟨j, hj, hjj, (dComm_eq_one_iff.mp hzj1).symm, i, hi, fun e => hij_ne e.symm⟩
    · have hzij : dComm z (i * j) = dComm z i * dComm z j :=
        dComm_mul_right ht hi hj hdN (Or.inr hzjt)
      have hcz : dComm z (i * j) = 1 := by
        rw [hzij, hzit, hzjt, ht2]
      have hsq : i * j * (i * j) = t := by
        calc i * j * (i * j) = i * (j * i) * j := by group
          _ = i * (t * (i * j)) * j := by rw [hji]
          _ = (i * t) * (i * j) * j := by group
          _ = (t * i) * (i * j) * j := by rw [htc i hi]
          _ = t * (i * i) * (j * j) := by group
          _ = t * t * t := by rw [hii, hjj]
          _ = t := by rw [mul_assoc, ht2, mul_one]
      have hnc : i * j * i ≠ i * (i * j) := by
        intro e
        have l : i * j * i = t * t * j := by
          calc i * j * i = i * (j * i) := by group
            _ = i * (t * (i * j)) := by rw [hji]
            _ = (i * t) * (i * j) := by group
            _ = (t * i) * (i * j) := by rw [htc i hi]
            _ = t * (i * i) * j := by group
            _ = t * t * j := by rw [hii]
        have r : i * (i * j) = t * j := by
          calc i * (i * j) = (i * i) * j := by group
            _ = t * j := by rw [hii]
        rw [l, r, mul_assoc] at e
        exact hcancel (t * j) e
      exact ⟨i * j, L.mul_mem hi hj, hsq, (dComm_eq_one_iff.mp hcz).symm, i, hi, hnc⟩

private theorem dew2_normalizes (h : DEHyp Ω) {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω)
    (hKJ : K ≠ J) {z : G} (hz : IsUniqueInvolution K z) {u t : G}
    (huJ : u ∈ J) (hu2 : u * u = t) (ht : IsUniqueInvolution J t)
    (hnc : ∃ w ∈ J, u * w ≠ w * u) (huz : u * z = z * u) :
    u ∈ Subgroup.normalizer (K : Set G) := by
  refine h.hyp.omega5 K hK J hJ hKJ z hz u huJ ?_ ?_ huz
  · intro hall
    obtain ⟨w, hw, hne⟩ := hnc
    exact hne (hall w hw)
  · have hu2' : u ^ 2 = t := by rw [pow_two]; exact hu2
    have hu4 : orderOf u = 2 ^ (1 + 1) := by
      apply orderOf_eq_prime_pow
      · rw [pow_one, hu2']
        exact ht.ne_one
      · rw [show (2 : ℕ) ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, hu2', pow_two, ht.sq]
    exact IsPGroup.of_card (n := 1 + 1) (by rw [Nat.card_zpowers, hu4])

private theorem dew2_exists_dComm (h : DEHyp Ω) {x : G} (hx : x ∈ pCore 2 G) {L : Subgroup G}
    (hL : L ∈ Ω) {z : G} (hz : IsUniqueInvolution L z)
    (hxN : x ∈ Subgroup.normalizer (L : Set G)) :
    ∃ d ∈ zGroup Ω, ∀ k ∈ L, dComm d k = dComm x k := by
  have hmem : ∀ k ∈ L, dComm x k ∈ Subgroup.zpowers z := by
    intro k hk
    have hI : dComm x k ∈ L ⊓ pCore 2 G := by
      refine ⟨dComm_mem hxN hk, ?_⟩
      have e : dComm x k = x * (k * x⁻¹ * k⁻¹) := by unfold dComm; group
      rw [e]
      exact (pCore 2 G).mul_mem hx (pCore_normal.conj_mem x⁻¹ ((pCore 2 G).inv_mem hx) k)
    rw [h.inf_pCore hL hz] at hI
    exact hI
  have hone : ∀ k ∈ L, dComm x k = 1 ∨ dComm x k = z := fun k hk =>
    dew2_eq_one_or_eq_of_mem_zpowers hz.sq hz.ne_one (hmem k hk)
  let φ : L →* Subgroup.zpowers z :=
    { toFun := fun k => ⟨dComm x (k : G), hmem k k.2⟩
      map_one' := Subtype.ext (by simp [dComm])
      map_mul' := fun a b => Subtype.ext (by
        simp only [Subgroup.coe_mul]
        exact dComm_mul_right hz a.2 b.2 hxN (hone b b.2)) }
  have hφz : φ ⟨z, hz.mem⟩ = 1 := Subtype.ext (dComm_z hz hxN)
  obtain ⟨d, hd, hdφ⟩ := h.exists_dComm_eq_hom hL hz φ hφz
  exact ⟨d, hd, fun k hk => hdφ ⟨k, hk⟩⟩

private theorem dew2_fixed_point_false (h : DEHyp Ω)
    (hC : Subgroup.centralizer (zGroup Ω : Set G) = pCore 2 G)
    {y z d : G} (hzD : z ∈ zGroup Ω) (hz1 : z ≠ 1) (hdD : d ∈ zGroup Ω) (hd1 : d ≠ 1)
    (hdz : d ≠ z) (hy3 : orderOf y = 3) (hyz : y * z = z * y) (hyd : y⁻¹ * d * y = d) :
    False := by
  classical
  have hzz : z * z = 1 := h.zGroup_mul_self z hzD
  have hdd : d * d = 1 := h.zGroup_mul_self d hdD
  have hzd_comm : z * d = d * z := h.zGroup_comm z hzD d hdD
  obtain ⟨e, heD, he⟩ := TL4.exists_mem_not_mem (E := zGroup Ω)
    ({1, z, d, z * d} : Finset G) (by
      rw [h.card_zGroup]
      exact lt_of_le_of_lt Finset.card_le_four (by norm_num))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at he
  obtain ⟨he1, hez, hed, hezd⟩ := he
  have hbas : TL4.E8Basis (zGroup Ω) ![z, d, e] :=
    { sq := fun x hx => h.zGroup_mul_self x hx
      card := h.card_zGroup
      mem := fun k => by fin_cases k <;> simp [hzD, hdD, heD]
      ne0 := hz1
      ne1 := ⟨hd1, hdz⟩
      ne2 := ⟨he1, hez, hed, hezd⟩ }
  have hyz' : Commute y z := hyz
  have hcjz : y⁻¹ * z * y = z := dew2_inv_conj_of_commute hyz'
  have hcj_mul : ∀ a b : G, y⁻¹ * (a * b) * y = (y⁻¹ * a * y) * (y⁻¹ * b * y) := by
    intro a b
    group
  have hcjinj : ∀ a b : G, y⁻¹ * a * y = y⁻¹ * b * y → a = b := by
    intro a b hab
    have := congrArg (fun t => y * t * y⁻¹) hab
    simpa using this
  have hPD : y⁻¹ * e * y ∈ zGroup Ω := by
    have := h.zGroup_normal.conj_mem e heD y⁻¹
    rwa [inv_inv] at this
  obtain ⟨v, hv⟩ := TL4.exists_e8Coord_eq hbas hPD
  have hlist : y⁻¹ * e * y = 1 ∨ y⁻¹ * e * y = z ∨ y⁻¹ * e * y = d ∨ y⁻¹ * e * y = z * d ∨
      y⁻¹ * e * y = e ∨ y⁻¹ * e * y = z * e ∨ y⁻¹ * e * y = d * e ∨
      y⁻¹ * e * y = z * d * e := by
    have hval0 : (0 : ZMod 2).val = 0 := rfl
    have hval1 : (1 : ZMod 2).val = 1 := rfl
    rw [← hv]
    rcases TL4.zmod_two_cases (v 0) with h0 | h0 <;>
      rcases TL4.zmod_two_cases (v 1) with h1 | h1 <;>
      rcases TL4.zmod_two_cases (v 2) with h2 | h2 <;>
      simp [TL4.e8Coord, h0, h1, h2, hval0, hval1]
  have hcase : y⁻¹ * e * y = e := by
    rcases hlist with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1
    · exact absurd (hcjinj e 1 (by rw [h1]; group)) he1
    · exact absurd (hcjinj e z (by rw [h1, hcjz])) hez
    · exact absurd (hcjinj e d (by rw [h1, hyd])) hed
    · exact absurd (hcjinj e (z * d) (by rw [h1, hcj_mul, hcjz, hyd])) hezd
    · exact h1
    · exfalso
      have c2 : y⁻¹ * (y⁻¹ * e * y) * y = e := by
        rw [h1, hcj_mul, hcjz, h1, ← mul_assoc, hzz, one_mul]
      have c3 := dew2_cube_conj hy3 e
      rw [c2, h1] at c3
      apply hz1
      have c4 : z * e = 1 * e := by rw [one_mul]; exact c3
      exact mul_right_cancel c4
    · exfalso
      have c2 : y⁻¹ * (y⁻¹ * e * y) * y = e := by
        rw [h1, hcj_mul, hyd, h1, ← mul_assoc, hdd, one_mul]
      have c3 := dew2_cube_conj hy3 e
      rw [c2, h1] at c3
      apply hd1
      have c4 : d * e = 1 * e := by rw [one_mul]; exact c3
      exact mul_right_cancel c4
    · exfalso
      have hzdzd : z * d * (z * d) = 1 := by
        calc z * d * (z * d) = z * (d * z) * d := by group
          _ = z * (z * d) * d := by rw [← hzd_comm]
          _ = (z * z) * (d * d) := by group
          _ = 1 := by rw [hzz, hdd, one_mul]
      have c2 : y⁻¹ * (y⁻¹ * e * y) * y = e := by
        rw [h1, hcj_mul, hcj_mul, hcjz, hyd, h1]
        calc z * d * (z * d * e) = (z * d * (z * d)) * e := by group
          _ = e := by rw [hzdzd, one_mul]
      have c3 := dew2_cube_conj hy3 e
      rw [c2, h1] at c3
      apply hdz
      have c4 : z * d * e = 1 * e := by rw [one_mul]; exact c3
      have c5 : z * d = 1 := mul_right_cancel c4
      calc d = z * (z * d) := by rw [← mul_assoc, hzz, one_mul]
        _ = z := by rw [c5, mul_one]
  have hye : e * y = y * e := by
    calc e * y = y * (y⁻¹ * e * y) := by group
      _ = y * e := by rw [hcase]
  have hyd2 : d * y = y * d := by
    calc d * y = y * (y⁻¹ * d * y) := by group
      _ = y * d := by rw [hyd]
  have hall : ∀ d' ∈ zGroup Ω, y * d' = d' * y := by
    apply dew2_commute_of_basis hbas
    intro k
    fin_cases k
    · exact hyz
    · exact hyd2.symm
    · exact hye.symm
  have hyC : y ∈ Subgroup.centralizer (zGroup Ω : Set G) :=
    Subgroup.mem_centralizer_iff.mpr (fun d' hd' => (hall d' hd').symm)
  rw [hC] at hyC
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := G)) ⟨y, hyC⟩
  have hyk : y ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h3 : 3 ∣ 2 ^ k := by
    rw [← hy3]
    exact orderOf_dvd_of_pow_eq_one hyk
  have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  norm_num at h32

private theorem dew2_order_three (h : DEHyp Ω)
    (hC : Subgroup.centralizer (zGroup Ω : Set G) = pCore 2 G)
    {z t t' : G} (hbas : TL4.E8Basis (zGroup Ω) ![z, t, t'])
    {Lt Lt' : Subgroup G} (hLt : Lt ∈ Ω) (hLt' : Lt' ∈ Ω)
    (ht : IsUniqueInvolution Lt t) (ht' : IsUniqueInvolution Lt' t')
    {u u' : G} (hu : u ∈ Lt) (hu2 : u * u = t) (huz : u * z = z * u)
    (hu' : u' ∈ Lt') (hu'2 : u' * u' = t') (hu'z : u' * z = z * u') :
    ∃ y ∈ Subgroup.closure ({u, u'} : Set G), orderOf y = 3 := by
  classical
  have htD : t ∈ zGroup Ω := hbas.mem 1
  have htD' : t' ∈ zGroup Ω := hbas.mem 2
  have ht1 : t ≠ 1 := hbas.ne1.1
  have ht'1 : t' ≠ 1 := hbas.ne2.1
  have ht't : t' ≠ t := hbas.ne2.2.2.1
  have ht2 : t * t = 1 := h.zGroup_mul_self t htD
  have ht'2 : t' * t' = 1 := h.zGroup_mul_self t' htD'
  have hcomm_tt' : t' * t = t * t' := h.zGroup_comm t' htD' t htD
  have hut : u * t = t * u := by
    have := conj_of_mem_mem ht hu (Or.inr rfl)
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this
  have hu't' : u' * t' = t' * u' := by
    have := conj_of_mem_mem ht' hu' (Or.inr rfl)
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this
  have hnoncomm : ∀ (L : Subgroup G) (s v : G), L ∈ Ω → IsUniqueInvolution L s → v ∈ L →
      v * v = s → (∀ d ∈ zGroup Ω, v * d = d * v) → False := by
    intro L s v hL hs hv hvv hcomm
    have hvC : v ∈ Subgroup.centralizer (zGroup Ω : Set G) :=
      Subgroup.mem_centralizer_iff.mpr (fun d hd => (hcomm d hd).symm)
    rw [hC] at hvC
    have hI : v ∈ L ⊓ pCore 2 G := ⟨hv, hvC⟩
    rw [h.inf_pCore hL hs] at hI
    rcases dew2_eq_one_or_eq_of_mem_zpowers hs.sq hs.ne_one hI with h1 | h1
    · apply hs.ne_one
      rw [h1, mul_one] at hvv
      exact hvv.symm
    · apply hs.ne_one
      rw [h1] at hvv
      exact mul_right_cancel (hvv.trans (one_mul s).symm)
  have hR3 : u * t' * u⁻¹ = t * t' := by
    have hc : dComm t' u ∈ Subgroup.zpowers t := h.dComm_mem_zpowers hLt ht htD' hu
    have hdu : dComm u t' = (dComm t' u)⁻¹ := by unfold dComm; group
    have hc2 : dComm u t' ∈ Subgroup.zpowers t := by
      rw [hdu]
      exact (Subgroup.zpowers t).inv_mem hc
    rcases dew2_eq_one_or_eq_of_mem_zpowers ht2 ht1 hc2 with h1 | h1
    · exfalso
      refine hnoncomm Lt t u hLt ht hu hu2 (dew2_commute_of_basis hbas ?_)
      intro k
      fin_cases k
      · exact huz
      · exact hut
      · exact dComm_eq_one_iff.mp h1
    · have h1' : u * t' * u⁻¹ * t'⁻¹ = t := h1
      calc u * t' * u⁻¹ = (u * t' * u⁻¹ * t'⁻¹) * t' := by group
        _ = t * t' := by rw [h1']
  have hR7 : u' * t * u'⁻¹ = t' * t := by
    have hc : dComm t u' ∈ Subgroup.zpowers t' := h.dComm_mem_zpowers hLt' ht' htD hu'
    have hdu : dComm u' t = (dComm t u')⁻¹ := by unfold dComm; group
    have hc2 : dComm u' t ∈ Subgroup.zpowers t' := by
      rw [hdu]
      exact (Subgroup.zpowers t').inv_mem hc
    rcases dew2_eq_one_or_eq_of_mem_zpowers ht'2 ht'1 hc2 with h1 | h1
    · exfalso
      refine hnoncomm Lt' t' u' hLt' ht' hu' hu'2 (dew2_commute_of_basis hbas ?_)
      intro k
      fin_cases k
      · exact hu'z
      · exact dComm_eq_one_iff.mp h1
      · exact hu't'
    · have h1' : u' * t * u'⁻¹ * t⁻¹ = t' := h1
      calc u' * t * u'⁻¹ = (u' * t * u'⁻¹ * t⁻¹) * t := by group
        _ = t' * t := by rw [h1']
  have hut_c : u * t * u⁻¹ = t := by
    rw [hut]
    group
  have hu't'_c : u' * t' * u'⁻¹ = t' := by
    rw [hu't']
    group
  obtain ⟨w, hw⟩ : ∃ w : G, w = u * u' := ⟨_, rfl⟩
  have hwt : w * t * w⁻¹ = t' := by
    rw [hw]
    calc u * u' * t * (u * u')⁻¹ = u * (u' * t * u'⁻¹) * u⁻¹ := by group
      _ = u * (t' * t) * u⁻¹ := by rw [hR7]
      _ = u * (t * t') * u⁻¹ := by rw [hcomm_tt']
      _ = (u * t * u⁻¹) * (u * t' * u⁻¹) := by group
      _ = t * (t * t') := by rw [hut_c, hR3]
      _ = t' := by rw [← mul_assoc, ht2, one_mul]
  have hwt' : w * t' * w⁻¹ = t * t' := by
    rw [hw]
    calc u * u' * t' * (u * u')⁻¹ = u * (u' * t' * u'⁻¹) * u⁻¹ := by group
      _ = u * t' * u⁻¹ := by rw [hu't'_c]
      _ = t * t' := hR3
  have hw3 : w ^ 3 * t * (w ^ 3)⁻¹ = t := by
    rw [pow_three']
    calc w * w * w * t * (w * w * w)⁻¹ = w * (w * (w * t * w⁻¹) * w⁻¹) * w⁻¹ := by group
      _ = w * (w * t' * w⁻¹) * w⁻¹ := by rw [hwt]
      _ = w * (t * t') * w⁻¹ := by rw [hwt']
      _ = (w * t * w⁻¹) * (w * t' * w⁻¹) := by group
      _ = t' * (t * t') := by rw [hwt, hwt']
      _ = t := by rw [← mul_assoc, hcomm_tt', mul_assoc, ht'2, mul_one]
  have hcomm3 : Commute (w ^ 3) t := mul_inv_eq_iff_eq_mul.mp hw3
  have hord3 : 3 ∣ orderOf w := by
    by_contra hn3
    have hn_pos : 0 < orderOf w := orderOf_pos w
    have hcop : Nat.Coprime 3 (orderOf w) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hn3
    have hn1 : orderOf w ≠ 1 := by
      intro h1
      rw [orderOf_eq_one_iff] at h1
      have : t' = t := by
        rw [h1, inv_one, mul_one, one_mul] at hwt
        exact hwt.symm
      exact ht't this
    have hcomm_w : Commute w t := by
      obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
      have hc' : Commute ((w ^ 3) ^ m) t := hcomm3.pow_left m
      rw [hm] at hc'
      exact hc'
    have hwt_t : w * t * w⁻¹ = t := by
      rw [mul_inv_eq_iff_eq_mul]
      exact hcomm_w.eq
    exact ht't (hwt.symm.trans hwt_t)
  have hwmem : w ∈ Subgroup.closure ({u, u'} : Set G) := by
    rw [hw]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert _ _))
      (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  refine ⟨w ^ (orderOf w / 3), Subgroup.pow_mem _ hwmem _, ?_⟩
  exact orderOf_pow_orderOf_div (orderOf_pos w).ne' hord3

private theorem dew2_centralizes_member (h : DEHyp Ω)
    (hC : Subgroup.centralizer (zGroup Ω : Set G) = pCore 2 G)
    {x : G} (hx : x ∈ pCore 2 G) {L : Subgroup G} (hL : L ∈ Ω) {z : G}
    (hz : IsUniqueInvolution L z) (hxN : x ∈ Subgroup.normalizer (L : Set G))
    {y : G} (hy3 : orderOf y = 3) (hyz : y * z = z * y) (hyx : y * x = x * y)
    (hyN : y ∈ Subgroup.normalizer (L : Set G)) :
    ∀ m ∈ L, m * x = x * m := by
  obtain ⟨d, hd, hdk⟩ := dew2_exists_dComm h hx hL hz hxN
  have hzD : z ∈ zGroup Ω := h.mem_zGroup_iff.mpr (Or.inr ⟨L, hL, hz⟩)
  have hz1 : z ≠ 1 := hz.ne_one
  have hzz : z * z = 1 := h.zGroup_mul_self z hzD
  have hyz' : Commute y z := hyz
  have hcz : ∀ c ∈ Subgroup.zpowers z, y * c * y⁻¹ = c ∧ y⁻¹ * c * y = c := by
    intro c hc
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    have hc' : Commute y (z ^ n) := hyz'.zpow_right n
    exact ⟨by rw [mul_inv_eq_iff_eq_mul]; exact hc'.eq, dew2_inv_conj_of_commute hc'⟩
  have hPD : y⁻¹ * d * y ∈ zGroup Ω := by
    have := h.zGroup_normal.conj_mem d hd y⁻¹
    rwa [inv_inv] at this
  have hA : ∀ k ∈ L, dComm (y⁻¹ * d * y) k = dComm d k := by
    intro k hk
    have hk' : y * k * y⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hyN k).mp hk
    have hxy : y * x * y⁻¹ = x := by
      rw [mul_inv_eq_iff_eq_mul]
      exact hyx
    have h1 : dComm d (y * k * y⁻¹) = dComm x (y * k * y⁻¹) := hdk _ hk'
    have h2 : dComm x (y * k * y⁻¹) = y * dComm x k * y⁻¹ := by
      have e : dComm (y * x * y⁻¹) (y * k * y⁻¹) = y * dComm x k * y⁻¹ := by
        unfold dComm
        group
      rw [hxy] at e
      exact e
    have h3 : dComm d k ∈ Subgroup.zpowers z := h.dComm_mem_zpowers hL hz hd hk
    have h4 : y * dComm d k * y⁻¹ = dComm d k := (hcz _ h3).1
    have h5 : dComm (y⁻¹ * d * y) k = y⁻¹ * dComm d (y * k * y⁻¹) * y := by
      unfold dComm
      group
    rw [h5, h1, h2, ← hdk k hk, h4, (hcz _ h3).2]
  have hP : d * (y⁻¹ * d * y)⁻¹ ∈ Subgroup.zpowers z :=
    h.eq_of_dComm_eq hL hz hPD hd hA
  have hPd : y⁻¹ * d * y = d ∨ y⁻¹ * d * y = z * d := by
    rcases dew2_eq_one_or_eq_of_mem_zpowers hzz hz1 hP with hc | hc
    · left
      calc y⁻¹ * d * y = (d * (y⁻¹ * d * y)⁻¹)⁻¹ * d := by group
        _ = d := by rw [hc]; group
    · right
      calc y⁻¹ * d * y = (d * (y⁻¹ * d * y)⁻¹)⁻¹ * d := by group
        _ = z * d := by rw [hc, inv_eq_of_mul_eq_one_right hzz]
  have hcjd : y⁻¹ * d * y = d := by
    rcases hPd with hPd | hPd
    · exact hPd
    · exfalso
      have hcjz : y⁻¹ * z * y = z := (hcz z (Subgroup.mem_zpowers z)).2
      have c2 : y⁻¹ * (y⁻¹ * d * y) * y = d := by
        calc y⁻¹ * (y⁻¹ * d * y) * y = y⁻¹ * (z * d) * y := by rw [hPd]
          _ = (y⁻¹ * z * y) * (y⁻¹ * d * y) := by group
          _ = z * (z * d) := by rw [hcjz, hPd]
          _ = d := by rw [← mul_assoc, hzz, one_mul]
      have c3 := dew2_cube_conj hy3 d
      rw [c2, hPd] at c3
      apply hz1
      have c4 : z * d * d⁻¹ = d * d⁻¹ := by rw [c3]
      simpa using c4
  have hd01 : d = 1 ∨ d = z := by
    by_contra hne
    push Not at hne
    exact dew2_fixed_point_false h hC hzD hz1 hd hne.1 hne.2 hy3 hyz hcjd
  intro m hm
  have hdm : dComm d m = 1 := by
    rcases hd01 with h1 | h1
    · rw [h1]
      simp [dComm]
    · rw [h1, dComm_eq_one_iff]
      exact (mul_inv_eq_iff_eq_mul.mp (conj_of_mem_mem hz hm (Or.inr rfl))).symm
  have hx1 := hdk m hm
  rw [hdm] at hx1
  exact (dComm_eq_one_iff.mp hx1.symm).symm

private theorem dew2_key (h : DEHyp Ω) (hC : Subgroup.centralizer (zGroup Ω : Set G) = pCore 2 G)
    {x : G} (hx : x ∈ pCore 2 G) (hxN : ∀ L ∈ Ω, x ∈ Subgroup.normalizer (L : Set G))
    (hxD : x ∉ zGroup Ω) {L0 : Subgroup G} (hL0 : L0 ∈ Ω)
    (hxL0 : ∀ m ∈ L0, m * x = x * m) : False := by
  classical
  obtain ⟨z0, hz0⟩ := h.exists_isUniqueInvolution hL0
  have hz0D : z0 ∈ zGroup Ω := h.mem_zGroup_iff.mpr (Or.inr ⟨L0, hL0, hz0⟩)
  obtain ⟨g, hg7, hgx⟩ := dew2_exists_order_seven h hx hxN hxD
  have hgc : Commute g x := hgx
  have hfree : ∀ δ ∈ zGroup Ω, δ ≠ 1 → g * δ * g⁻¹ ≠ δ :=
    fun δ hδ hδ1 => dew2_fixed_free h hC hg7 hδ hδ1
  have htrans : ∀ u ∈ zGroup Ω, u ≠ 1 → ∃ k : ℕ, g ^ k * z0 * (g ^ k)⁻¹ = u :=
    fun u hu hu1 => dew2_orbit_surj h hg7 hfree hz0D hz0.ne_one hu hu1
  have hover : ∀ u ∈ zGroup Ω, u ≠ 1 →
      ∃ L ∈ Ω, IsUniqueInvolution L u ∧ ∀ m ∈ L, m * x = x * m := by
    intro u hu hu1
    obtain ⟨k, hk⟩ := htrans u hu hu1
    refine ⟨conjSub (g ^ k) L0, h.hyp.conjInvariant _ _ hL0, ?_, ?_⟩
    · have := hz0.conj (g ^ k)
      rwa [hk] at this
    · exact dew2_conjSub_commute (Commute.pow_left hgc k) hxL0
  obtain ⟨t, htD, htS⟩ := TL4.exists_mem_not_mem (E := zGroup Ω) ({1, z0} : Finset G) (by
    rw [h.card_zGroup]
    exact lt_of_le_of_lt Finset.card_le_two (by norm_num))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at htS
  obtain ⟨ht1, htz0⟩ := htS
  obtain ⟨t', ht'D, ht'S⟩ := TL4.exists_mem_not_mem (E := zGroup Ω)
    ({1, z0, t, z0 * t} : Finset G) (by
      rw [h.card_zGroup]
      exact lt_of_le_of_lt Finset.card_le_four (by norm_num))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht'S
  obtain ⟨ht'1, ht'z0, ht't, ht'zt⟩ := ht'S
  have hbas : TL4.E8Basis (zGroup Ω) ![z0, t, t'] :=
    { sq := fun x hx => h.zGroup_mul_self x hx
      card := h.card_zGroup
      mem := fun k => by fin_cases k <;> simp [hz0D, htD, ht'D]
      ne0 := hz0.ne_one
      ne1 := ⟨ht1, htz0⟩
      ne2 := ⟨ht'1, ht'z0, ht't, ht'zt⟩ }
  obtain ⟨Lt, hLt, htinv, hLtx⟩ := hover t htD ht1
  obtain ⟨Lt', hLt', ht'inv, hLt'x⟩ := hover t' ht'D ht'1
  obtain ⟨u, huLt, hu2, huz, hunc⟩ := dew2_exists_u h hLt htinv hz0D
  obtain ⟨u', hu'Lt', hu'2, hu'z, hu'nc⟩ := dew2_exists_u h hLt' ht'inv hz0D
  obtain ⟨y, hyC, hy3⟩ :=
    dew2_order_three h hC hbas hLt hLt' htinv ht'inv huLt hu2 huz hu'Lt' hu'2 hu'z
  have hux : u * x = x * u := hLtx u huLt
  have hu'x : u' * x = x * u' := hLt'x u' hu'Lt'
  have hyx : y * x = x * y := by
    have hcl : Subgroup.closure ({u, u'} : Set G) ≤ Subgroup.centralizer ({x} : Set G) := by
      rw [Subgroup.closure_le]
      intro v hv
      rcases hv with rfl | hv
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hux
      · rcases hv with rfl
        exact Subgroup.mem_centralizer_singleton_iff.mpr hu'x
    exact Subgroup.mem_centralizer_singleton_iff.mp (hcl hyC)
  have hyz0 : y * z0 = z0 * y := by
    have hcl : Subgroup.closure ({u, u'} : Set G) ≤ Subgroup.centralizer ({z0} : Set G) := by
      rw [Subgroup.closure_le]
      intro v hv
      rcases hv with rfl | hv
      · exact Subgroup.mem_centralizer_singleton_iff.mpr huz
      · rcases hv with rfl
        exact Subgroup.mem_centralizer_singleton_iff.mpr hu'z
    exact Subgroup.mem_centralizer_singleton_iff.mp (hcl hyC)
  have hyN : ∀ L ∈ Ω, IsUniqueInvolution L z0 → y ∈ Subgroup.normalizer (L : Set G) := by
    intro L hL hLz
    have hne : L ≠ Lt := by
      intro e
      subst e
      exact htz0 (hLz.eq htinv).symm
    have hne' : L ≠ Lt' := by
      intro e
      subst e
      exact ht'z0 (hLz.eq ht'inv).symm
    have hun : u ∈ Subgroup.normalizer (L : Set G) :=
      dew2_normalizes h hL hLt hne hLz huLt hu2 htinv hunc huz
    have hu'n : u' ∈ Subgroup.normalizer (L : Set G) :=
      dew2_normalizes h hL hLt' hne' hLz hu'Lt' hu'2 ht'inv hu'nc hu'z
    have hcl : Subgroup.closure ({u, u'} : Set G) ≤ Subgroup.normalizer (L : Set G) := by
      rw [Subgroup.closure_le]
      intro v hv
      rcases hv with rfl | hv
      · exact hun
      · rcases hv with rfl
        exact hu'n
    exact hcl hyC
  have hV : ∀ L ∈ Ω, IsUniqueInvolution L z0 → ∀ m ∈ L, m * x = x * m := fun L hL hLz =>
    dew2_centralizes_member h hC hx hL hLz (hxN L hL) hy3 hyz0 hyx (hyN L hL hLz)
  have hall : ∀ L ∈ Ω, ∀ m ∈ L, m * x = x * m := by
    intro L hL m hm
    obtain ⟨zL, hzL⟩ := h.exists_isUniqueInvolution hL
    have hzLD : zL ∈ zGroup Ω := h.mem_zGroup_iff.mpr (Or.inr ⟨L, hL, hzL⟩)
    obtain ⟨k, hk⟩ := htrans zL hzLD hzL.ne_one
    have hcomm : Commute (g ^ k) x := Commute.pow_left hgc k
    have hL' : conjSub (g ^ k)⁻¹ L ∈ Ω := h.hyp.conjInvariant _ _ hL
    have hL'z : IsUniqueInvolution (conjSub (g ^ k)⁻¹ L) z0 := by
      have := hzL.conj (g ^ k)⁻¹
      have e : (g ^ k)⁻¹ * zL * (g ^ k)⁻¹⁻¹ = z0 := by
        rw [← hk]
        group
      rwa [e] at this
    have h1 := dew2_conjSub_commute hcomm (hV _ hL' hL'z)
    rw [conjSub_conjSub_inv] at h1
    exact h1 m hm
  have hxc : x ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g'
    have hg' : g' ∈ pSpan Ω := by
      rw [h.gen]
      exact Subgroup.mem_top g'
    have hle : pSpan Ω ≤ Subgroup.centralizer ({x} : Set G) :=
      pSpan_le fun L hL m hm => Subgroup.mem_centralizer_singleton_iff.mpr (hall L hL m hm)
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hg')
  rw [h.center, Subgroup.mem_bot] at hxc
  apply hxD
  rw [hxc]
  exact (zGroup Ω).one_mem

private theorem dew2_main (h : DEHyp Ω) (hC : Subgroup.centralizer (zGroup Ω : Set G) = pCore 2 G)
    {q : G} (hq : q ∈ pCore 2 G) (hqN : ∀ L ∈ Ω, q ∈ Subgroup.normalizer (L : Set G)) :
    q ∈ zGroup Ω := by
  by_contra hqD
  obtain ⟨L0, hL0⟩ : Ω.Nonempty := by
    obtain ⟨L, hL, -⟩ := h.exists_ne
    exact ⟨L, hL⟩
  obtain ⟨z0, hz0⟩ := h.exists_isUniqueInvolution hL0
  obtain ⟨d, hd, hdk⟩ := dew2_exists_dComm h hq hL0 hz0 (hqN L0 hL0)
  have hxL0 : ∀ m ∈ L0, m * (q * d) = (q * d) * m := by
    intro m hm
    have hc : dComm d m ∈ Subgroup.zpowers z0 := h.dComm_mem_zpowers hL0 hz0 hd hm
    have hc' := dew2_eq_one_or_eq_of_mem_zpowers hz0.sq hz0.ne_one hc
    have hm1 : dComm (q * d) m = 1 := by
      rw [dComm_mul_left hz0 (hqN L0 hL0) hc', ← hdk m hm]
      rcases hc' with h1 | h1
      · rw [h1, mul_one]
      · rw [h1, hz0.sq]
    exact (dComm_eq_one_iff.mp hm1).symm
  have hxD : q * d ∉ zGroup Ω := by
    intro hmem
    apply hqD
    have hq' : q = (q * d) * d⁻¹ := by group
    rw [hq']
    exact (zGroup Ω).mul_mem hmem ((zGroup Ω).inv_mem hd)
  have hxQ : q * d ∈ pCore 2 G := (pCore 2 G).mul_mem hq (h.zGroup_le_pCore hd)
  have hxN : ∀ L ∈ Ω, q * d ∈ Subgroup.normalizer (L : Set G) := fun L hL =>
    Subgroup.mul_mem _ (hqN L hL) (h.dNorm L hL hd)
  exact dew2_key h hC hxQ hxN hxD hL0 hxL0

end Dew2

namespace DE4Hyp

variable {Ω : Set (Subgroup G)} (h : DE4Hyp Ω)
include h

theorem centralizer_zGroup_eq_pCore :
    Subgroup.centralizer (zGroup Ω : Set G) = pCore 2 G :=
  (dew1_pCore_eq_centralizer h.toDEHyp h.twin4).symm

theorem exists_pCore_conj_of_mem_twinSet {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ twinSet Ω K) :
    ∃ q ∈ pCore 2 G, conjSub q K = J := by
  haveI : (pCore 2 G).Normal := CFSG.pCore_normal
  obtain ⟨u, hu⟩ := h.exists_isUniqueInvolution hK
  obtain ⟨g, hg, hgK⟩ := h.exists_swap_of_mem_twinSet hK hJ hu
  rw [h.centralizer_eq_sup hK hu, centralizer_zGroup_eq_pCore h, sup_comm] at hg
  obtain ⟨q, hq, n, hn, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hg
  rw [conjSub_mul, mem_normalizer_iff_conjSub_eq.mp hn] at hgK
  exact ⟨q, hq, hgK⟩

theorem mem_zGroup_of_normalizes_all {q : G} (hq : q ∈ pCore 2 G)
    (hqN : ∀ L ∈ Ω, q ∈ Subgroup.normalizer (L : Set G)) : q ∈ zGroup Ω :=
  dew2_main h.toDEHyp h.centralizer_zGroup_eq_pCore hq hqN

end DE4Hyp

end CFSG.ClassicalInvolution.Q3.Sec13
