module

public import CFSG.LieType.Chevalley.CLSOddToralOrdinaryComponentRootFactor
import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ComponentLayerCentralizesSolvableNormalized

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore

open CFSG Subgroup
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

@[expose] def oddClosure (C : Subgroup X) : Subgroup X := closure {g | g ∈ C ∧ Odd (orderOf g)}

omit [Finite X] in
theorem oddClosure_le (C : Subgroup X) : oddClosure C ≤ C := by
  rw [oddClosure, closure_le]
  exact fun g hg => hg.1

theorem le_oddClosure_of_perfect {C Q : Subgroup X} (hQC : Q ≤ C) (hQ : commutator Q = ⊤) :
    Q ≤ oddClosure C := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T := oddClosure C with hT
  have hTC := oddClosure_le C
  set T' := T.subgroupOf C with hT'
  have hTn : T'.Normal := by
    rw [hT', normal_subgroupOf_iff hTC]
    intro t c ht hc
    have hle : T ≤ T.comap (MulAut.conj c).toMonoidHom := by
      rw [hT, oddClosure, closure_le]
      rintro g ⟨hgC, hgo⟩
      refine Subgroup.subset_closure ⟨?_, ?_⟩
      · exact mul_mem (mul_mem hc hgC) (inv_mem hc)
      · change Odd (orderOf (c * g * c⁻¹))
        rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
        exact hgo
    have := hle ht
    simpa using this
  have h2 : IsPGroup 2 (C ⧸ T') := by
    intro g
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos c).ne'
    refine ⟨a, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hT', mem_subgroupOf]
    apply Subgroup.subset_closure
    refine ⟨(c ^ (2 ^ a)).2, ?_⟩
    have hord : orderOf (c ^ (2 ^ a)) = b := by
      rw [orderOf_pow_of_dvd (by positivity) (by rw [hab]; exact Dvd.intro b rfl), hab,
        Nat.mul_div_cancel_left _ (by positivity)]
    rw [Subgroup.orderOf_coe, hord]
    exact hb
  have hsolv : Group.IsSolvable (C ⧸ T') := by
    have := h2.isNilpotent
    infer_instance
  obtain ⟨m, hm⟩ := hsolv.solvable
  let φ : Q →* C ⧸ T' := (QuotientGroup.mk' T').comp (Subgroup.inclusion hQC)
  have hK : ∀ j : ℕ, derivedSeries Q j = ⊤ := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih => rw [derivedSeries_succ, ih, ← _root_.commutator_def, hQ]
  intro q hq
  have hmem : φ ⟨q, hq⟩ ∈ derivedSeries (C ⧸ T') m := by
    apply map_derivedSeries_le_derivedSeries φ m
    exact ⟨⟨q, hq⟩, by rw [hK m]; exact mem_top _, rfl⟩
  rw [hm, mem_bot] at hmem
  have h1 : (Subgroup.inclusion hQC ⟨q, hq⟩ : C) ∈ T' := (QuotientGroup.eq_one_iff _).mp hmem
  rw [hT', mem_subgroupOf] at h1
  exact h1

variable {L : Subgroup X} [L.Normal] {i : X} {R : Subgroup X}
  (hRodd : Odd (Nat.card R)) (hRi : ∀ r ∈ R, r * i = i * r)
  (hRconj : ∀ s ∈ L ⊓ centralizer ({i} : Set X), Odd (orderOf s) → ∀ r ∈ R, s * r * s⁻¹ ∈ R)
include hRodd hRi hRconj

theorem commute_of_isComponentOf {Q : Subgroup X}
    (hQ : Open.IsComponentOf Q (L ⊓ centralizer ({i} : Set X))) {r : X} (hr : r ∈ R) {q : X}
    (hq : q ∈ Q) : r * q = q * r := by
  set C := L ⊓ centralizer ({i} : Set X) with hC
  set T := oddClosure C with hT
  have hTC := oddClosure_le C
  have hRC : ∀ r ∈ R, ∀ c ∈ C, r * c * r⁻¹ ∈ C := by
    intro r hr c hc
    obtain ⟨hcL, hci⟩ := mem_inf.mp hc
    refine mem_inf.mpr ⟨(inferInstance : L.Normal).conj_mem c hcL r, ?_⟩
    rw [mem_centralizer_singleton_iff] at hci ⊢
    have hri := hRi r hr
    have hri' : r⁻¹ * i = i * r⁻¹ := by
      calc r⁻¹ * i = r⁻¹ * (i * r) * r⁻¹ := by group
        _ = r⁻¹ * (r * i) * r⁻¹ := by rw [hri]
        _ = i * r⁻¹ := by group
    calc r * c * r⁻¹ * i = r * c * (i * r⁻¹) := by rw [mul_assoc, hri']
      _ = r * (c * i) * r⁻¹ := by group
      _ = r * (i * c) * r⁻¹ := by rw [hci]
      _ = (r * i) * c * r⁻¹ := by group
      _ = i * (r * c * r⁻¹) := by rw [hri]; group
  have hRT : ∀ r ∈ R, ∀ t ∈ T, r * t * r⁻¹ ∈ T := by
    intro r hr t ht
    have hle : T ≤ T.comap (MulAut.conj r).toMonoidHom := by
      rw [hT, oddClosure, closure_le]
      rintro g ⟨hgC, hgo⟩
      refine Subgroup.subset_closure ⟨hRC r hr g hgC, ?_⟩
      change Odd (orderOf (r * g * r⁻¹))
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
      exact hgo
    have := hle ht
    simpa using this
  have hTR : T ≤ normalizer (R : Set X) := by
    rw [hT, oddClosure, closure_le]
    rintro s ⟨hsC, hso⟩
    rw [SetLike.mem_coe, mem_normalizer_iff]
    intro r'
    refine ⟨fun h => hRconj s hsC hso r' h, fun h => ?_⟩
    have := hRconj s⁻¹ (inv_mem hsC) (by rwa [orderOf_inv]) _ h
    simpa [mul_assoc] using this
  set N := R ⊓ T with hN
  have hNodd : Odd (Nat.card N) := Odd.of_dvd_nat hRodd (card_dvd_of_le inf_le_left)
  have hNsolv : Group.IsSolvable N := CFSG.FeitThompson.isSolvable_of_odd_natCard N hNodd
  have hNC : N ≤ C := inf_le_right.trans hTC
  have hTN : T ≤ normalizer (N : Set X) := by
    intro t ht
    rw [mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      obtain ⟨hnR, hnT⟩ := mem_inf.mp hn
      exact mem_inf.mpr ⟨(mem_normalizer_iff.mp (hTR ht) n).mp hnR,
        mul_mem (mul_mem ht hnT) (inv_mem ht)⟩
    · intro hn
      obtain ⟨hnR, hnT⟩ := mem_inf.mp hn
      refine mem_inf.mpr ⟨(mem_normalizer_iff.mp (hTR ht) n).mpr hnR, ?_⟩
      have := mul_mem (mul_mem (inv_mem ht) hnT) ht
      simpa [mul_assoc] using this
  have hEN : GorensteinWalter.componentLayerOf C ≤ normalizer (N : Set X) := by
    refine sSup_le fun E hE => ?_
    exact (le_oddClosure_of_perfect hE.1 hE.2.2.2.1).trans hTN
  have hcomm := GorensteinWalter.componentLayerOf_centralizes_solvable_of_le_normalizer C N hNC
    hNsolv hEN
  have hQGW : GorensteinWalter.IsComponentOf Q C := by
    obtain ⟨hQC, hQsn, hQqs⟩ := hQ
    refine ⟨hQC, ?_, ?_⟩
    · exact CFSG.LieType.Chevalley.OddToralOrdinary.isSubnormal_subgroupOf_of_assembly
        ((ComponentClassification.AssemblyBPredicates.isSubnormal_iff_open Q C).mpr hQsn)
    · obtain ⟨hcomm', hsimple⟩ := hQqs
      refine ⟨?_, hcomm', hsimple⟩
      by_contra hnt
      rw [not_nontrivial_iff_subsingleton] at hnt
      have : Subsingleton (Q ⧸ center Q) := inferInstance
      exact hsimple.toNontrivial.exists_pair_ne.elim fun a h => h.elim fun b hab =>
        hab (Subsingleton.elim a b)
  have hQE : Q ≤ GorensteinWalter.componentLayerOf C := le_sSup hQGW
  have hQN : ∀ a ∈ Q, ∀ n ∈ N, a * n = n * a := by
    intro a ha n hn
    have h1 : ⁅a, n⁆ ∈ ⁅GorensteinWalter.componentLayerOf C, N⁆ :=
      commutator_mem_commutator (hQE ha) hn
    rw [hcomm, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  have hQT := le_oddClosure_of_perfect hQ.1 hQ.2.2.1
  have hmemN : ∀ a ∈ Q, r * a * r⁻¹ * a⁻¹ ∈ N := by
    intro a ha
    refine mem_inf.mpr ⟨?_, mul_mem (hRT r hr a (hQT ha)) (inv_mem (hQT ha))⟩
    have := (mem_normalizer_iff.mp (hTR (hQT ha)) r⁻¹).mp (inv_mem hr)
    rw [show r * a * r⁻¹ * a⁻¹ = r * (a * r⁻¹ * a⁻¹) by group]
    exact mul_mem hr this
  let φ : Q →* N :=
    { toFun := fun a => ⟨r * a * r⁻¹ * a⁻¹, hmemN a a.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => by
        apply Subtype.ext
        change r * ((a : X) * b) * r⁻¹ * ((a : X) * b)⁻¹ =
          (r * a * r⁻¹ * (a : X)⁻¹) * (r * b * r⁻¹ * (b : X)⁻¹)
        have hc := hQN a a.2 _ (hmemN b b.2)
        calc r * ((a : X) * b) * r⁻¹ * ((a : X) * b)⁻¹ =
            (r * a * r⁻¹ * (a : X)⁻¹) * ((a : X) * (r * b * r⁻¹ * (b : X)⁻¹)) * (a : X)⁻¹ := by
              group
          _ = (r * a * r⁻¹ * (a : X)⁻¹) * ((r * b * r⁻¹ * (b : X)⁻¹) * a) * (a : X)⁻¹ := by
              rw [hc]
          _ = (r * a * r⁻¹ * (a : X)⁻¹) * (r * b * r⁻¹ * (b : X)⁻¹) := by group }
  obtain ⟨m, hm⟩ := hNsolv.solvable
  have hK : ∀ j : ℕ, derivedSeries Q j = ⊤ := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih => rw [derivedSeries_succ, ih, ← _root_.commutator_def, hQ.2.2.1]
  have hmem : φ ⟨q, hq⟩ ∈ derivedSeries N m := by
    apply map_derivedSeries_le_derivedSeries φ m
    exact ⟨⟨q, hq⟩, by rw [hK m]; exact mem_top _, rfl⟩
  rw [hm, mem_bot] at hmem
  have h1 : r * q * r⁻¹ * q⁻¹ = 1 := congrArg Subtype.val hmem
  calc r * q = r * q * r⁻¹ * q⁻¹ * q * r := by group
    _ = q * r := by rw [h1, one_mul]

end CFSG.ComponentClassification.Foote5.OddLieCore
