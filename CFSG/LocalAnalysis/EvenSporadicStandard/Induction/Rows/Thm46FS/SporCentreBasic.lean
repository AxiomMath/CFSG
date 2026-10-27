module

public import CFSG.Sporadic.SuzOddCore.CompQuot
public import Mathlib.GroupTheory.SpecificGroups.KleinFour
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.EvenSporadicStandard.Induction.SporCentre

open CFSG CFSG.LocalCores Subgroup CFSG.Sporadic.SuzOddCore
open scoped commutatorElement

section TheoremA

variable {E K : Type*} [Group E] [Group K]

theorem map_component_eq (ρ : E →* K) (hρ : Function.Surjective ρ)
    (hker : Group.IsSolvable ρ.ker) {D : Subgroup K} (hDi : D.index = 2)
    (hDs : IsSimpleGroup D) {B : Subgroup E} (hB : IsComponent B) : B.map ρ = D := by
  obtain ⟨hq, hsub⟩ := hB
  have hperf : Group.IsPerfect B := hq.1
  have hnt : Nontrivial B := isQuasisimple_nontrivial hq
  have hBB : ⁅B, B⁆ = B := by
    rw [← Subgroup.map_subtype_commutator, hperf.commutator_eq_top, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hcomm : ⁅B.map ρ, B.map ρ⁆ = B.map ρ := by rw [← Subgroup.map_commutator, hBB]
  have hle : B.map ρ ≤ D := by
    rw [← hcomm]
    exact (Subgroup.commutator_mono le_top le_top).trans (commutator_le_of_index_two hDi)
  have hsubD : ((B.map ρ).subgroupOf D).IsSubnormal := (hsub.map hρ).subgroupOf
  rcases hsubD.eq_bot_or_top_of_isSimpleGroup hDs with h | h
  · exfalso
    have hBk : B ≤ ρ.ker := by
      intro b hb
      rw [MonoidHom.mem_ker]
      have : (⟨ρ b, hle ⟨b, hb, rfl⟩⟩ : D) ∈ (B.map ρ).subgroupOf D := by
        rw [Subgroup.mem_subgroupOf]
        exact ⟨b, hb, rfl⟩
      rw [h, Subgroup.mem_bot] at this
      exact congrArg Subtype.val this
    have : Group.IsSolvable B :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hBk)
    exact Group.IsPerfect.not_isSolvable B this
  · apply le_antisymm hle
    intro d hd
    have : (⟨d, hd⟩ : D) ∈ (B.map ρ).subgroupOf D := h ▸ Subgroup.mem_top _
    rwa [Subgroup.mem_subgroupOf] at this

theorem component_le_centralizer_ker [Finite E] (ρ : E →* K) (hker : Group.IsSolvable ρ.ker)
    {B : Subgroup E} (hB : IsComponent B) : B ≤ centralizer (ρ.ker : Set E) :=
  Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    ((component_solvable_centralizer hker ρ.normal_ker.isSubnormal).1 B hB)

theorem center_map_eq [Finite E] (ρ : E →* K) (hρ : Function.Surjective ρ)
    (hker : Group.IsSolvable ρ.ker) {D : Subgroup K} (hDi : D.index = 2)
    (hDs : IsSimpleGroup D) (hDnc : ∃ a b : D, a * b ≠ b * a) {B : Subgroup E}
    (hB : IsComponent B) : (center B).map B.subtype = B ⊓ ρ.ker := by
  have hBD := map_component_eq ρ hρ hker hDi hDs hB
  have hBc := component_le_centralizer_ker ρ hker hB
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z.2, ?_⟩
    have hzD : ρ z ∈ D := by
      rw [← hBD]
      exact ⟨z, z.2, rfl⟩
    have hc : (⟨ρ z, hzD⟩ : D) ∈ center D := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      have := center_map_le ρ B hz (g : K) (by rw [hBD]; exact g.2)
      exact this.symm
    rw [center_eq_bot_of_simple' hDs hDnc, Subgroup.mem_bot] at hc
    exact congrArg Subtype.val hc
  · rintro ⟨hxB, hxk⟩
    refine ⟨⟨x, hxB⟩, ?_, rfl⟩
    change (⟨x, hxB⟩ : B) ∈ center B
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact (mem_centralizer_iff.1 (hBc g.2) x hxk).symm

theorem commutatorElement_mul_mul {G : Type*} [Group G] {b b' n n' : G} (h1 : Commute n b')
    (h2 : Commute n n') (h3 : Commute n' b) : ⁅b * n, b' * n'⁆ = ⁅b, b'⁆ := by
  have hA : n * (b' * n') = b' * n' * n := (h1.mul_right h2).eq
  have hB : n' * b⁻¹ = b⁻¹ * n' := (h3.inv_right).eq
  simp only [commutatorElement_def, mul_inv_rev]
  calc b * n * (b' * n') * (n⁻¹ * b⁻¹) * (n'⁻¹ * b'⁻¹)
      = b * (n * (b' * n')) * n⁻¹ * b⁻¹ * n'⁻¹ * b'⁻¹ := by group
    _ = b * (b' * n' * n) * n⁻¹ * b⁻¹ * n'⁻¹ * b'⁻¹ := by rw [hA]
    _ = b * b' * (n' * b⁻¹) * n'⁻¹ * b'⁻¹ := by group
    _ = b * b' * (b⁻¹ * n') * n'⁻¹ * b'⁻¹ := by rw [hB]
    _ = b * b' * b⁻¹ * b'⁻¹ := by group

theorem component_eq_commutator [Finite E] (ρ : E →* K) (hρ : Function.Surjective ρ)
    (hker : Group.IsSolvable ρ.ker) (hNab : ∀ x ∈ ρ.ker, ∀ y ∈ ρ.ker, x * y = y * x)
    {D : Subgroup K} (hDi : D.index = 2) (hDs : IsSimpleGroup D) {B : Subgroup E}
    (hB : IsComponent B) : ⁅D.comap ρ, D.comap ρ⁆ = B := by
  have hBD := map_component_eq ρ hρ hker hDi hDs hB
  have hBc := component_le_centralizer_ker ρ hker hB
  have hBB : ⁅B, B⁆ = B := by
    have hperf : Group.IsPerfect B := hB.1.1
    rw [← Subgroup.map_subtype_commutator, hperf.commutator_eq_top, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hBle : B ≤ D.comap ρ := fun b hb => by
    rw [Subgroup.mem_comap, ← hBD]
    exact ⟨b, hb, rfl⟩
  have hdecomp : ∀ x ∈ D.comap ρ, ∃ b ∈ B, ∃ n ∈ ρ.ker, x = b * n := by
    intro x hx
    rw [Subgroup.mem_comap, ← hBD] at hx
    obtain ⟨b, hb, hbx⟩ := hx
    refine ⟨b, hb, b⁻¹ * x, ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hbx, inv_mul_cancel]
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro x hx y hy
    obtain ⟨b, hb, n, hn, rfl⟩ := hdecomp x hx
    obtain ⟨b', hb', n', hn', rfl⟩ := hdecomp y hy
    rw [commutatorElement_mul_mul
      (show Commute n b' from mem_centralizer_iff.1 (hBc hb') n hn)
      (show Commute n n' from hNab n hn n' hn')
      (show Commute n' b from mem_centralizer_iff.1 (hBc hb) n' hn')]
    rw [commutatorElement_def]
    exact B.mul_mem (B.mul_mem (B.mul_mem hb hb') (B.inv_mem hb)) (B.inv_mem hb')
  · calc B = ⁅B, B⁆ := hBB.symm
      _ ≤ ⁅D.comap ρ, D.comap ρ⁆ := Subgroup.commutator_mono hBle hBle

theorem center_map_eq_commutator_inf [Finite E] (ρ : E →* K) (hρ : Function.Surjective ρ)
    (hker : Group.IsSolvable ρ.ker) (hNab : ∀ x ∈ ρ.ker, ∀ y ∈ ρ.ker, x * y = y * x)
    {D : Subgroup K} (hDi : D.index = 2) (hDs : IsSimpleGroup D)
    (hDnc : ∃ a b : D, a * b ≠ b * a) {B : Subgroup E} (hB : IsComponent B) :
    (center B).map B.subtype = ⁅D.comap ρ, D.comap ρ⁆ ⊓ ρ.ker := by
  rw [component_eq_commutator ρ hρ hker hNab hDi hDs hB]
  exact center_map_eq ρ hρ hker hDi hDs hDnc hB

theorem center_eq_bot_of_le [Finite E] (ρ : E →* K) (hρ : Function.Surjective ρ)
    (hker : Group.IsSolvable ρ.ker) {D : Subgroup K} (hDi : D.index = 2)
    (hDs : IsSimpleGroup D) (hDnc : ∃ a b : D, a * b ≠ b * a) {B : Subgroup E}
    (hB : IsComponent B) {L : Subgroup E} (hBL : B ≤ L) (hL : L ⊓ ρ.ker = ⊥) :
    center B = ⊥ := by
  have h := center_map_eq ρ hρ hker hDi hDs hDnc hB
  have h2 : B ⊓ ρ.ker ≤ ⊥ := hL ▸ inf_le_inf_right _ hBL
  rw [le_bot_iff.1 h2] at h
  exact (Subgroup.map_eq_bot_iff_of_injective _ B.subtype_injective).1 h

theorem nonempty_center_equiv_ker [Finite E] (ρ : E →* K) (hρ : Function.Surjective ρ)
    (hker : Group.IsSolvable ρ.ker) (hNab : ∀ x ∈ ρ.ker, ∀ y ∈ ρ.ker, x * y = y * x)
    {D : Subgroup K} (hDi : D.index = 2) (hDs : IsSimpleGroup D)
    (hDnc : ∃ a b : D, a * b ≠ b * a) (h : ρ.ker ≤ ⁅D.comap ρ, D.comap ρ⁆)
    {B : Subgroup E} (hB : IsComponent B) : Nonempty (center B ≃* ρ.ker) := by
  have := center_map_eq_commutator_inf ρ hρ hker hNab hDi hDs hDnc hB
  rw [inf_eq_right.2 h] at this
  exact ⟨((center B).equivMapOfInjective B.subtype B.subtype_injective).trans
    (MulEquiv.subgroupCongr this)⟩

end TheoremA

section Core

theorem eq_top_of_index_le {G : Type*} [Group G] [Finite G] (hperf : Group.IsPerfect G)
    (hs : IsSimpleGroup (G ⧸ center G)) {n : ℕ} (hbig : Nat.factorial n < Nat.card (G ⧸ center G))
    {H : Subgroup G} (hH : H.index ≤ n) : H = ⊤ := by
  have hCnorm : H.normalCore.Normal := H.normalCore_normal
  have hCle : H.normalCore ≤ H := H.normalCore_le
  have hCidx : H.normalCore.index ≤ Nat.factorial n :=
    (H.index_normalCore_le_factorial_index).trans (Nat.factorial_le hH)
  have hCZ : H.normalCore ⊔ center G = ⊤ := by
    have hnorm : (H.normalCore.map (QuotientGroup.mk' (center G))).Normal :=
      Subgroup.Normal.map hCnorm _ (QuotientGroup.mk'_surjective _)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (H.normalCore.map (QuotientGroup.mk' (center G))) with h | h
    · exfalso
      have hCZle : H.normalCore ≤ center G := by
        intro c hc
        have : QuotientGroup.mk' (center G) c ∈ H.normalCore.map (QuotientGroup.mk' (center G)) :=
          ⟨c, hc, rfl⟩
        rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
        exact this
      have h1 : (center G).index ∣ H.normalCore.index := Subgroup.index_dvd_of_le hCZle
      have h2 : 0 < H.normalCore.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
      have h3 := Nat.le_of_dvd h2 h1
      have h4 : (center G).index = Nat.card (G ⧸ center G) := rfl
      omega
    · have := Subgroup.comap_map_eq (QuotientGroup.mk' (center G)) H.normalCore
      rw [h, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
      exact this.symm
  have hZ : ⁅(⊤ : Subgroup G), center G⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro g _
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (Subgroup.mem_center_iff.1 hz g).symm
  have htop : (⊤ : Subgroup G) ≤ H.normalCore := by
    calc (⊤ : Subgroup G) = ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ := hperf.commutator_eq_top.symm
      _ = ⁅(⊤ : Subgroup G), H.normalCore ⊔ center G⁆ := by rw [hCZ]
      _ = ⁅(⊤ : Subgroup G), H.normalCore⁆ ⊔ ⁅(⊤ : Subgroup G), center G⁆ :=
          Subgroup.commutator_sup_left _ _ _
      _ ≤ H.normalCore := by
          rw [hZ, sup_bot_eq]
          exact Subgroup.commutator_le_right _ _
  exact top_le_iff.1 (htop.trans hCle)

end Core

section KleinFour

theorem isKleinFour_of_card_four {H : Type*} [Group H] (h4 : Nat.card H = 4)
    (hsq : ∀ x : H, x ^ 2 = 1) : _root_.IsKleinFour H := by
  refine ⟨h4, ?_⟩
  rcases (Nat.dvd_prime Nat.prime_two).mp (Monoid.exponent_dvd_of_forall_pow_eq_one hsq) with
    h | h
  · have : Subsingleton H := Monoid.exp_eq_one_iff.mp h
    have := Nat.card_of_subsingleton (1 : H)
    omega
  · exact h

theorem isKleinFour_prod_zmod_two :
    _root_.IsKleinFour (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :=
  isKleinFour_of_card_four (by simp [Nat.card_prod]) (by decide)

theorem nonempty_mulEquiv_of_isKleinFour {H : Type*} [Group H] [_root_.IsKleinFour H] :
    Nonempty (H ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) :=
  haveI := isKleinFour_prod_zmod_two
  IsKleinFour.nonempty_mulEquiv

theorem nonempty_mulEquiv_of_card_four {H : Type*} [Group H] (h4 : Nat.card H = 4)
    (hsq : ∀ x : H, x ^ 2 = 1) :
    Nonempty (H ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) :=
  have := isKleinFour_of_card_four h4 hsq
  nonempty_mulEquiv_of_isKleinFour

theorem nonempty_mulEquiv_zmod_four {H : Type*} [Group H] [IsCyclic H] (h4 : Nat.card H = 4) :
    Nonempty (H ≃* Multiplicative (ZMod 4)) :=
  ⟨mulEquivOfCyclicCardEq (by rw [h4]; simp)⟩

end KleinFour

section Transport

theorem nonempty_center_equiv_map {S : Type*} [Group S] {C : Subgroup S} {E : Type*} [Group E]
    (g : C ≃* E) {Q : Subgroup S} (hQC : Q ≤ C) :
    Nonempty (center Q ≃* center ((Q.subgroupOf C).map g.toMonoidHom)) :=
  ⟨Subgroup.centerCongr ((Subgroup.subgroupOfEquivOfLe hQC).symm.trans
    ((Q.subgroupOf C).equivMapOfInjective g.toMonoidHom g.injective))⟩

end Transport

end CFSG.EvenSporadicStandard.Induction.SporCentre
