module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreXOneComponent

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

variable {X : Type} [Group X] [Finite X]

theorem isCyclic_of_forall_eq_of_central {X : Type*} [Group X] [Finite X]
    {R : Subgroup X} (hR2 : IsPGroup 2 R)
    (hinv : ∀ a ∈ R, ∀ b ∈ R, orderOf a = 2 → orderOf b = 2 → a = b) {c : X} (hcR : c ∈ R)
    (hcZ : ∀ r ∈ R, Commute r c) (hc4 : orderOf c = 4) : IsCyclic R := by
  have hrank : twoRank R ≤ 1 := by
    rw [twoRank, ← CFSG.RankThreeCoreUniqueness.Helpers.pRank_subgroup_eq_internal_top 2
      (by decide)]
    by_contra hlt
    obtain ⟨a, haR, b, hbR, ha, hb, hab, -⟩ :=
      exists_commuting_involutions_of_two_le_pRank (K := R) (by omega)
    exact hab (hinv a haR b hbR ha hb)
  have hcZ' : (⟨c, hcR⟩ : R) ∈ Subgroup.center R := Subgroup.mem_center_iff.mpr fun r =>
    Subtype.ext (hcZ r r.2).eq
  by_cases hab : ∃ a b : R, a * b ≠ b * a
  · have hZ := CFSG.TwoRankLowerBound.Helpers.center_card_eq_two_of_nonabelian_rank_one_two_group
      R hR2 hrank hab
    have hle := Subgroup.card_le_of_le (Subgroup.zpowers_le.mpr hcZ')
    rw [hZ, Nat.card_zpowers, Subgroup.orderOf_mk, hc4] at hle
    omega
  · push Not at hab
    let : CommGroup R := { (inferInstance : Group R) with mul_comm := hab }
    exact CFSG.TwoRankLowerBound.Helpers.abelian_rank_one_two_group_isCyclic R hR2 hrank

namespace OneComponent

variable {Y : Subgroup X} {e v : X} {L : Subgroup X}

omit [Finite X] in
theorem perfect (hL : OneComponent Y e v L) : commutator L = ⊤ :=
  hL.component.1.1.commutator_eq_top

omit [Finite X] in
theorem simple (hL : OneComponent Y e v L) : IsSimpleGroup (L ⧸ Subgroup.center L) :=
  hL.component.1.2.1

omit [Finite X] in
theorem nonabelian (hL : OneComponent Y e v L) :
    ∃ a b : L ⧸ Subgroup.center L, a * b ≠ b * a :=
  hL.component.1.2.2

theorem center_isPGroup (hL : OneComponent Y e v L) (hc : BaseConfig Y e) :
    IsPGroup 2 (Subgroup.center L) :=
  (component_center_le_twoCore hc.oddCore_eq_bot hL.component).1

theorem eq_of_mem_center (hL : OneComponent Y e v L) (hc : BaseConfig Y e) {c : L}
    (hcZ : c ∈ Subgroup.center L) (h2 : orderOf c = 2) : (c : X) = e :=
  hc.eq_of_mem_twoCore (hL.center_le (Subgroup.mem_map_of_mem _ hcZ))
    (by rw [Subgroup.orderOf_coe]; exact h2)

theorem center_ne_bot (hL : OneComponent Y e v L) (hc : BaseConfig Y e) :
    Subgroup.center L ≠ ⊥ := by
  intro hbot
  have h := hL.mem_center hc
  rw [hbot, Subgroup.mem_bot] at h
  have h2 := hc.order
  rw [show e = 1 from congrArg Subtype.val h, orderOf_one] at h2
  exact absurd h2 (by decide)

theorem center_mem_inf_conj (hL : OneComponent Y e v L) (hc : BaseConfig Y e) (m : X) {c : L}
    (hcZ : c ∈ Subgroup.center L) : (c : X) ∈ Y ⊓ Y.conjBy m⁻¹ :=
  hc.twoCore_le_inf_conj m (hL.center_le (Subgroup.mem_map_of_mem _ hcZ))

theorem center_le_subgroupOf (hL : OneComponent Y e v L) (hc : BaseConfig Y e) :
    Subgroup.center L ≤ Y.subgroupOf L := fun _ hcZ =>
  Subgroup.mem_subgroupOf.mpr (hL.center_mem_inf_conj hc 1 hcZ).1

omit [Finite X] in
theorem subgroupOf_ne_top (hL : OneComponent Y e v L) : Y.subgroupOf L ≠ ⊤ := fun h =>
  hL.not_le fun x hx => by
    have hx' : (⟨x, hx⟩ : L) ∈ Y.subgroupOf L := h ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp hx'

theorem exists_sylow_le (hL : OneComponent Y e v L) (hc : BaseConfig Y e) :
    ∃ S : Sylow 2 L, (S : Subgroup L) ≤ Y.subgroupOf L ∧ ¬ IsCyclic (S : Subgroup L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hPY, -⟩ := hc.sylow
  obtain ⟨S, hS⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal P hL.component.2
  refine ⟨S, fun s hs => Subgroup.mem_subgroupOf.mpr ?_, fun hcyc => ?_⟩
  · have h : (s : X) ∈ (S : Subgroup L).map L.subtype := Subgroup.mem_map_of_mem _ hs
    rw [hS] at h
    exact hPY h.1
  · apply hc.not_isCyclic_sylow_inf P hL.component
    rw [← hS]
    exact isCyclic_of_surjective ((S : Subgroup L).equivMapOfInjective L.subtype
      L.subtype_injective).toMonoidHom (MulEquiv.surjective _)

theorem even_card_quotient (hL : OneComponent Y e v L) (hc : BaseConfig Y e) :
    Even (Nat.card (L ⧸ Subgroup.center L)) := by
  obtain ⟨S, -, hSc⟩ := hL.exists_sylow_le hc
  obtain ⟨s, hsS, hsZ⟩ : ∃ s ∈ (S : Subgroup L), s ∉ Subgroup.center L := by
    by_contra hall
    push Not at hall
    have := hL.center_isCyclic
    exact hSc (Subgroup.isCyclic_of_le (show (S : Subgroup L) ≤ Subgroup.center L from hall))
  obtain ⟨n, hn⟩ := S.isPGroup' ⟨s, hsS⟩
  have hsn : (QuotientGroup.mk' (Subgroup.center L) s) ^ 2 ^ n = 1 := by
    rw [← map_pow, show s ^ 2 ^ n = 1 from by simpa using congrArg Subtype.val hn, map_one]
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hsn)
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hk
    exact hsZ hk
  have hdvd := orderOf_dvd_natCard (QuotientGroup.mk' (Subgroup.center L) s)
  rw [hk] at hdvd
  exact even_iff_two_dvd.mpr ((dvd_pow_self 2 hk0).trans hdvd)

theorem card_quotient_lt (hL : OneComponent Y e v L) (hc : BaseConfig Y e) :
    Nat.card (L ⧸ Subgroup.center L) < Nat.card X := by
  have h1 : 1 < Nat.card (Subgroup.center L) :=
    (Subgroup.one_lt_card_iff_ne_bot _).mpr (hL.center_ne_bot hc)
  have hL' := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center L)
  have hpos : 0 < Nat.card (L ⧸ Subgroup.center L) := Nat.card_pos
  calc Nat.card (L ⧸ Subgroup.center L) < Nat.card (L ⧸ Subgroup.center L) *
        Nat.card (Subgroup.center L) := lt_mul_of_one_lt_right hpos h1
    _ = Nat.card L := hL'.symm
    _ ≤ Nat.card X := Subgroup.card_le_card_group L

omit [Finite X] in
theorem mem_center_of_mem_centralizer {l : L}
    (hl : (l : X) ∈ Subgroup.centralizer (L : Set X)) : l ∈ Subgroup.center L :=
  Subgroup.mem_center_iff.mpr fun g => Subtype.ext
    (Subgroup.mem_centralizer_iff.mp hl g g.2)

theorem eq_one_or_eq_of_card_two (hL : OneComponent Y e v L) (hc : BaseConfig Y e)
    (hZ : Nat.card (Subgroup.center L) = 2) {c : L} (hcZ : c ∈ Subgroup.center L) :
    c = 1 ∨ (c : X) = e := by
  by_cases hc1 : c = 1
  · exact Or.inl hc1
  right
  obtain ⟨y, -, hyu⟩ := (Nat.card_eq_two_iff' (1 : Subgroup.center L)).mp hZ
  have h1 := hyu ⟨c, hcZ⟩ fun h' => hc1 (congrArg Subtype.val h')
  have h2 := hyu ⟨⟨e, hL.mem⟩, hL.mem_center hc⟩ fun h' => by
    have h3 := hc.order
    rw [show e = 1 from congrArg (fun w : Subgroup.center L => ((w : L) : X)) h', orderOf_one]
      at h3
    exact absurd h3 (by decide)
  exact congrArg (fun w : Subgroup.center L => ((w : L) : X)) (h1.trans h2.symm)

theorem not_mem_of_card_two (hL : OneComponent Y e v L) (hc : BaseConfig Y e) (hv : v * v = e)
    (hZ : Nat.card (Subgroup.center L) = 2) : v ∉ L := by
  intro hvL
  have hord := hc.orderOf_eq_four hv
  rcases hL.eq_one_or_eq_of_card_two hc hZ
      (mem_center_of_mem_centralizer (l := ⟨v, hvL⟩) hL.mem_centralizer) with h | h
  · rw [show v = 1 from congrArg Subtype.val h, orderOf_one] at hord
    exact absurd hord (by decide)
  · have h2 := hc.order
    rw [← show v = e from h, hord] at h2
    exact absurd h2 (by decide)

theorem mul_involution_of_card_two (hL : OneComponent Y e v L) (hc : BaseConfig Y e)
    (hv : v * v = e) (hZ : Nat.card (Subgroup.center L) = 2) {a : X} (haL : a ∈ L)
    (ha : a * a = e) : orderOf (v * a) = 2 ∧ v * a ≠ e := by
  have hvL := hL.not_mem_of_card_two hc hv hZ
  have hav : a * v = v * a := Subgroup.mem_centralizer_iff.mp hL.mem_centralizer a haL
  have hva : v * a * (v * a) = 1 := by
    calc v * a * (v * a) = v * (a * v) * a := by group
      _ = v * (v * a) * a := by rw [hav]
      _ = v * v * (a * a) := by group
      _ = 1 := by rw [hv, ha, hc.mul_self]
  have hva1 : v * a ≠ 1 := fun h => hvL (by
    rw [show v = a⁻¹ from eq_inv_of_mul_eq_one_left h]
    exact L.inv_mem haL)
  refine ⟨orderOf_eq_prime (by rw [pow_two]; exact hva) hva1, fun h => hvL ?_⟩
  rw [show v = a from (mul_left_cancel (h.trans hv.symm)).symm]
  exact haL

end OneComponent

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
