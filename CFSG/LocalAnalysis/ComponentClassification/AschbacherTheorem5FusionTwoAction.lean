module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5Conjugation
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5Hyp
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5Semisimple

public section

open CFSG.Open

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace FusionTwo

theorem le_center_of_quasisimple {K : Type*} [Group K] (hK : CFSG.Open.IsQuasisimple K)
    (N : Subgroup K)
    [hNn : N.Normal] (hN : Group.IsSolvable N) : N ≤ Subgroup.center K := by
  have : IsSimpleGroup (K ⧸ Subgroup.center K) := hK.2
  have : Group.IsPerfect K := ⟨hK.1⟩
  have hmap : (N.map (QuotientGroup.mk' (Subgroup.center K))).Normal :=
    hNn.map _ (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (N.map (QuotientGroup.mk' (Subgroup.center K))) with h | h
  · rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    exact h
  · exfalso
    have hsurj : Function.Surjective ((QuotientGroup.mk' (Subgroup.center K)).comp N.subtype) := by
      rw [← MonoidHom.range_eq_top, MonoidHom.range_comp, Subgroup.range_subtype, h]
    have : Group.IsSolvable (K ⧸ Subgroup.center K) := Group.isSolvable_of_surjective hsurj
    exact Group.IsPerfect.not_isSolvable (K ⧸ Subgroup.center K) this

theorem commute_of_quasisimple {Q : Type*} [Group Q] {K N : Subgroup Q}
    (hK : CFSG.Open.IsQuasisimple K)
    [hKn : K.Normal] [hNn : N.Normal] (hN : Group.IsSolvable N) :
    ∀ n ∈ N, ∀ x ∈ K, n * x = x * n := by
  have : Group.IsPerfect K := ⟨hK.1⟩
  have hNK : ∀ y ∈ N, ∀ z ∈ K, y ∈ K → y * z = z * y := by
    intro y hy z hz hyK
    have hsolv : Group.IsSolvable (N.subgroupOf K) := by
      let f : N.subgroupOf K →* N :=
        { toFun := fun x => ⟨x.1.1, x.2⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl }
      exact Group.isSolvable_of_isSolvable_injective (f := f) (fun a b hab => by
        have h := congrArg Subtype.val hab
        apply Subtype.ext
        apply Subtype.ext
        exact h)
    have hcen := le_center_of_quasisimple hK (N.subgroupOf K) hsolv
    have hyc : (⟨y, hyK⟩ : K) ∈ Subgroup.center K := hcen hy
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hyc ⟨z, hz⟩).symm)
  have h1 : ⁅⁅N, K⁆, K⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hyN : y ∈ N := Subgroup.commutator_le_left N K hy
    have hyK : y ∈ K := Subgroup.commutator_le_right N K hy
    exact (hNK y hyN z hz hyK).symm
  have h2 : ⁅⁅K, N⁆, K⁆ = ⊥ := by rw [Subgroup.commutator_comm K N]; exact h1
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate h2 h1
  rw [Subgroup.commutator_eq_self, Subgroup.commutator_eq_bot_iff_le_centralizer] at h3
  intro n hn x hx
  exact Subgroup.mem_centralizer_iff.mp (h3 hx) n hn

theorem solvable_normal_le_center {Q : Type*} [Group Q] {Index : Type*}
    (Abar : Index → Subgroup Q) (hsemi : ∀ i, aschbacherThm5IsSemisimple (Abar i))
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ Abar i, ∀ y ∈ Abar j, x * y = y * x)
    (hgen : ⨆ i, Abar i = ⊤) {N : Subgroup Q} [hNn : N.Normal] (hN : Group.IsSolvable N) :
    N ≤ Subgroup.center Q := by
  intro n hn
  rw [Subgroup.mem_center_iff]
  intro g
  suffices hall : (⊤ : Subgroup Q) ≤ Subgroup.centralizer ({n} : Set Q) from
    Subgroup.mem_centralizer_singleton_iff.mp (hall (Subgroup.mem_top g))
  rw [← hgen]
  apply iSup_le
  intro i
  obtain ⟨k, K, -, hK, hKc, hKgen⟩ := hsemi i
  rw [← hKgen]
  apply iSup_le
  intro l x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hKn : (K l).Normal := by
    apply Subgroup.normalizer_eq_top_iff.mp
    apply top_unique
    rw [← hgen]
    apply iSup_le
    intro j
    by_cases hji : j = i
    · subst hji
      rw [← hKgen]
      apply iSup_le
      intro m
      by_cases hml : m = l
      · subst hml
        exact Subgroup.le_normalizer
      · apply le_trans _ (Subgroup.centralizer_le_normalizer _)
        intro y hy
        apply Subgroup.mem_centralizer_iff.mpr
        intro z hz
        exact (hKc m l hml y hy z hz).symm
    · apply le_trans _ (Subgroup.centralizer_le_normalizer _)
      intro y hy
      apply Subgroup.mem_centralizer_iff.mpr
      intro z hz
      exact (hcomm j i hji y hy z ((hK l).1 hz)).symm
  exact (commute_of_quasisimple (hK l).2 hN n hn x hx).symm

theorem eq_of_inv_mul_mem_center {Y : Type*} [Group Y] [Group.IsPerfect Y] (σ : Y →* Y)
    (hσ : ∀ y, y⁻¹ * σ y ∈ Subgroup.center Y) (y : Y) : σ y = y := by
  let f : Y →* Subgroup.center Y :=
    { toFun := fun y => ⟨y⁻¹ * σ y, hσ y⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun x z => by
        apply Subtype.ext
        change (x * z)⁻¹ * σ (x * z) = x⁻¹ * σ x * (z⁻¹ * σ z)
        have hc := Subgroup.mem_center_iff.mp (hσ x) z⁻¹
        rw [map_mul]
        calc (x * z)⁻¹ * (σ x * σ z) = z⁻¹ * (x⁻¹ * σ x) * σ z := by group
          _ = (x⁻¹ * σ x) * z⁻¹ * σ z := by rw [hc]
          _ = x⁻¹ * σ x * (z⁻¹ * σ z) := by group }
  have hker := Abelianization.commutator_subset_ker f
  rw [Group.IsPerfect.commutator_eq_top] at hker
  have hy : f y = 1 := hker (Subgroup.mem_top y)
  have := congrArg Subtype.val hy
  change y⁻¹ * σ y = 1 at this
  rw [inv_mul_eq_one] at this
  exact this.symm

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

theorem conj_mem_core_of_solvable (hyp : Hyp61 G D r Abar) {N : Subgroup G} [hNn : N.Normal]
    (hsolv : Group.IsSolvable (Subgroup.normalizer (D : Set G) ⊓ N : Subgroup G)) {x : G}
    (hxH : x ∈ Subgroup.normalizer (D : Set G)) (hxN : x ∈ N) {d : G} (hd : d ∈ D) :
    d⁻¹ * (x * d * x⁻¹) ∈ aschbacherThm5Core D := by
  set π := QuotientGroup.mk' (aschbacherThm5OddCore D)
  have hNDn : (N.subgroupOf D).Normal := hNn.subgroupOf D
  have hND : ((N.subgroupOf D).map π).Normal := hNDn.map _ (QuotientGroup.mk'_surjective _)
  have hNDsolv : Group.IsSolvable ((N.subgroupOf D).map π) := by
    have hsub : Group.IsSolvable (N.subgroupOf D) := by
      let f : N.subgroupOf D →* (Subgroup.normalizer (D : Set G) ⊓ N : Subgroup G) :=
        { toFun := fun y => ⟨y.1.1, Subgroup.mem_inf.mpr ⟨Subgroup.le_normalizer y.1.2, y.2⟩⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl }
      exact Group.isSolvable_of_isSolvable_injective (f := f) (fun a b hab => by
        have h := congrArg Subtype.val hab
        apply Subtype.ext
        apply Subtype.ext
        exact h)
    exact Group.isSolvable_of_surjective (f := π.subgroupMap (N.subgroupOf D))
      (MonoidHom.subgroupMap_surjective π (N.subgroupOf D))
  have hcen := solvable_normal_le_center Abar hyp.hsemisimple hyp.hcomm hyp.hgen hNDsolv
  have hperf : Group.IsPerfect (D ⧸ aschbacherThm5OddCore D) :=
    quotient_perfect_of_semisimple_factors Abar hyp.hsemisimple hyp.hgen
  set σ := onQuotient D ⟨x, hxH⟩
  have hσ : ∀ q, q⁻¹ * σ q ∈ Subgroup.center (D ⧸ aschbacherThm5OddCore D) := by
    intro q
    obtain ⟨e, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherThm5OddCore D) q
    apply hcen
    refine ⟨e⁻¹ * onD D ⟨x, hxH⟩ e, ?_, ?_⟩
    · change ((e : G))⁻¹ * (x * e * x⁻¹) ∈ N
      have h2 : (e : G)⁻¹ * x * (e : G) ∈ N := by
        simpa using hNn.conj_mem x hxN (e : G)⁻¹
      have : (e : G)⁻¹ * (x * e * x⁻¹) = ((e : G)⁻¹ * x * e) * x⁻¹ := by group
      rw [this]
      exact N.mul_mem h2 (N.inv_mem hxN)
    · rw [map_mul, map_inv, onQuotient_mk]
  have hfix := eq_of_inv_mul_mem_center σ.toMonoidHom hσ
    (QuotientGroup.mk' (aschbacherThm5OddCore D) ⟨d, hd⟩)
  change σ _ = _ at hfix
  rw [onQuotient_mk] at hfix
  have hmem := (QuotientGroup.eq (s := aschbacherThm5OddCore D)).mp hfix.symm
  exact ⟨_, hmem, rfl⟩

omit [Finite G] in
theorem exists_mul_fixed {R O : Subgroup G} (hR : IsPGroup 2 R) (hO : Odd (Nat.card O))
    (hRO : R ≤ Subgroup.normalizer (O : Set G)) {d : G}
    (hd : ∀ x ∈ R, d⁻¹ * (x * d * x⁻¹) ∈ O) :
    ∃ o ∈ O, ∀ x ∈ R, x * (d * o) * x⁻¹ = d * o := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmem : ∀ (x : R) (o : O), d⁻¹ * x * (d * o) * (x : G)⁻¹ ∈ O := by
    intro x o
    have h1 := hd x x.2
    have h2 : (x : G) * o * (x : G)⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.mp (hRO x.2) o).mp o.2
    have : d⁻¹ * x * (d * o) * (x : G)⁻¹ =
        (d⁻¹ * (x * d * (x : G)⁻¹)) * (x * o * (x : G)⁻¹) := by group
    rw [this]
    exact O.mul_mem h1 h2
  let : MulAction R O :=
    { smul := fun x o => ⟨d⁻¹ * x * (d * o) * (x : G)⁻¹, hmem x o⟩
      one_smul := fun o => Subtype.ext (by
        change d⁻¹ * (1 : G) * (d * o) * (1 : G)⁻¹ = o
        group)
      mul_smul := fun x y o => Subtype.ext (by
        change d⁻¹ * ((x : G) * y) * (d * o) * ((x : G) * y)⁻¹ =
          d⁻¹ * x * (d * (d⁻¹ * y * (d * o) * (y : G)⁻¹)) * (x : G)⁻¹
        group) }
  obtain ⟨o, ho⟩ := hR.nonempty_fixed_point_of_prime_not_dvd_card O
    (fun h => (Nat.not_even_iff_odd.mpr hO) (even_iff_two_dvd.mpr h))
  refine ⟨o, o.2, fun x hx => ?_⟩
  have hfix := congrArg Subtype.val (ho ⟨x, hx⟩)
  change d⁻¹ * x * (d * o) * x⁻¹ = o at hfix
  calc x * (d * o) * x⁻¹ = d * (d⁻¹ * x * (d * o) * x⁻¹) := by group
    _ = d * o := by rw [hfix]

theorem core_odd (D : Subgroup G) : Odd (Nat.card (aschbacherThm5Core D)) := by
  change Odd (Nat.card ((aschbacherThm5OddCore D).map D.subtype))
  rw [Subgroup.card_map_of_injective D.subtype_injective]
  exact oddCore_odd D

omit [Finite G] in
theorem core_le (D : Subgroup G) : aschbacherThm5Core D ≤ D :=
  Subgroup.map_subtype_le _

theorem exists_centralizer_cover {R : Subgroup G} (hR : IsPGroup 2 R)
    (hRH : R ≤ Subgroup.normalizer (D : Set G))
    (htriv : ∀ x ∈ R, ∀ d ∈ D, d⁻¹ * (x * d * x⁻¹) ∈ aschbacherThm5Core D) {d : G}
    (hd : d ∈ D) :
    ∃ c ∈ D, (∀ x ∈ R, x * c * x⁻¹ = c) ∧ c⁻¹ * d ∈ aschbacherThm5Core D := by
  have hRO : R ≤ Subgroup.normalizer (aschbacherThm5Core D : Set G) := by
    intro x hx
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (core_conjugate_eq D ⟨x, hRH hx⟩)
  obtain ⟨o, ho, hfix⟩ := exists_mul_fixed hR (core_odd D) hRO (fun x hx => htriv x hx d hd)
  refine ⟨d * o, D.mul_mem hd (core_le D ho), hfix, ?_⟩
  have : (d * o)⁻¹ * d = o⁻¹ := by group
  rw [this]
  exact Subgroup.inv_mem _ ho

end FusionTwo

end CFSG.ComponentClassification.AschbacherTheorem5
