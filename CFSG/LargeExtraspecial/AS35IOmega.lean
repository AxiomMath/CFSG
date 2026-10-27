module

public import CFSG.LargeExtraspecial.AS35IQuot

public section

namespace CFSG.LargeExtraspecial.Asc22

open Subgroup Asc77

variable {G : Type} [Group G] {N U P : Subgroup G} {z : G}

namespace Hyp

variable (h : Hyp N U P z)
include h

theorem isMulComm_V [Finite G] : IsMulCommutative ↥(genV N z) :=
  ⟨⟨fun a b => Subtype.ext (h.comm_V a.2 b.2)⟩⟩

theorem exists_not_mem_kerV [Finite G] : ∃ a ∈ U ⊔ P, a ∉ kerV N z := by
  by_contra hcon
  push Not at hcon
  apply h.Qb_ne_bot
  rw [eq_bot_iff]
  rintro _ ⟨n, hn, rfl⟩
  rw [mem_bot, piK_eq_one]
  exact hcon _ (mem_subgroupOf.1 hn)

omit h in
theorem conj_eq_iff {g : G} (hg : g ∈ N) : g * z * g⁻¹ = z ↔ g ∈ cenM N z := by
  rw [mem_inf, mem_centralizer_singleton_iff]
  constructor
  · intro h1
    refine ⟨hg, ?_⟩
    calc g * z = g * z * g⁻¹ * g := by group
      _ = z * g := by rw [h1]
  · rintro ⟨-, h1⟩
    rw [h1]
    group

theorem conj_ne_of_ne [Finite G] {a t : G} (ha : a ∈ U ⊔ P) (haK : a ∉ kerV N z)
    (ht : t ∈ conjIn z N) (htz : t ≠ z) : a * t * a⁻¹ ≠ t := by
  intro hat
  obtain ⟨n, hn, rfl⟩ := ht
  have hnM : n⁻¹ ∉ cenM N z := by
    intro hnM
    apply htz
    have := (conj_eq_iff (N.inv_mem hn)).2 hnM
    calc n * z * n⁻¹ = n * (n⁻¹ * z * n⁻¹⁻¹) * n⁻¹ := by rw [this]
      _ = z := by group
  have haN := h.sup_le_N ha
  have hcM : n⁻¹ * a * n⁻¹⁻¹ ∈ cenM N z := by
    refine (conj_eq_iff (N.mul_mem (N.mul_mem (N.inv_mem hn) haN) (N.inv_mem (N.inv_mem hn)))).1 ?_
    calc n⁻¹ * a * n⁻¹⁻¹ * z * (n⁻¹ * a * n⁻¹⁻¹)⁻¹ = n⁻¹ * (a * (n * z * n⁻¹) * a⁻¹) * n := by
          group
      _ = n⁻¹ * (n * z * n⁻¹) * n := by rw [hat]
      _ = z := by group
  have habs := h.absTI
  have h1 := habs.eq_one_of_conj_mem (g := piK N z ⟨n⁻¹, N.inv_mem hn⟩)
    (fun hm => hnM (mem_Mb.1 hm)) (x := piK N z ⟨a, haN⟩) (piK_mem_barOf ha) (by
      rw [← map_inv, ← map_mul, ← map_mul]
      exact piK_mem_barOf hcM)
  exact haK (piK_eq_one.1 h1)

omit h in
theorem card_conjIn [Finite G] : Nat.card (conjIn z N) = ((cenM N z).subgroupOf N).index := by
  let _ := conjMulAction z N
  set z₀ : conjIn z N := ⟨z, self_mem_conjIn z N⟩
  have horb : MulAction.orbit N z₀ = Set.univ := by
    ext ⟨t, n, hn, hnt⟩
    simp only [Set.mem_univ, iff_true]
    refine ⟨⟨n, hn⟩, Subtype.ext ?_⟩
    change n * z * n⁻¹ = t
    exact hnt
  have hstab : MulAction.stabilizer N z₀ = (cenM N z).subgroupOf N := by
    ext n
    rw [MulAction.mem_stabilizer_iff, mem_subgroupOf, ← conj_eq_iff n.2]
    constructor
    · intro h1
      exact congrArg Subtype.val h1
    · intro h1
      exact Subtype.ext h1
  have := MulAction.index_stabilizer N z₀
  rw [horb, Set.ncard_univ, hstab] at this
  exact this.symm

theorem odd_card_conjIn [Finite G] : Odd (Nat.card (conjIn z N)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [card_conjIn]
  obtain ⟨T, hT⟩ := h.syl
  have hTM : (T : Subgroup N) ≤ (cenM N z).subgroupOf N := fun t ht =>
    mem_subgroupOf.2 (mem_inf.2 ⟨t.2, mem_centralizer_singleton_iff.2 (hT t ht)⟩)
  have hdvd := index_dvd_of_le hTM
  have hT2 := T.not_dvd_index
  rw [Nat.odd_iff]
  by_contra h2
  apply hT2
  exact (Nat.dvd_of_mod_eq_zero (by omega)).trans hdvd

theorem one_lt_card_conjIn [Finite G] : 1 < Nat.card (conjIn z N) := by
  obtain ⟨g, hgN, hgz⟩ : ∃ g ∈ N, g ∉ centralizer ({z} : Set G) := by
    by_contra hcon
    push Not at hcon
    exact h.notcen hcon
  have hne : g * z * g⁻¹ ≠ z := fun h1 => hgz (mem_inf.1 ((conj_eq_iff hgN).1 h1)).2
  have : Finite (conjIn z N) := Finite.Set.subset (N : Set G) fun _ ⟨n, hn, hnt⟩ =>
    hnt ▸ N.mul_mem (N.mul_mem hn h.z_mem_N) (N.inv_mem hn)
  rw [Finite.one_lt_card_iff_nontrivial]
  exact ⟨⟨⟨z, self_mem_conjIn z N⟩, ⟨g * z * g⁻¹, conj_mem_conjIn hgN⟩, fun h1 =>
    hne (congrArg Subtype.val h1).symm⟩⟩

theorem eq_of_inv_mul_mem [Finite G] {t t' : G} (ht : t ∈ conjIn z N) (ht' : t' ∈ conjIn z N)
    (hc : t⁻¹ * t' ∈ Asc77.centerIn z N) : t = t' := by
  obtain ⟨n, hn, rfl⟩ := ht
  obtain ⟨n', hn', rfl⟩ := ht'
  set c := (n * z * n⁻¹)⁻¹ * (n' * z * n'⁻¹) with hcdef
  have hcN : ∀ m ∈ N, m * c = c * m := fun m hm =>
    (mem_centralizer_iff.1 (mem_inf.1 hc).2 m hm)
  have hcinvN : ∀ m ∈ N, m * c⁻¹ = c⁻¹ * m := fun m hm => by
    have := hcN m hm
    calc m * c⁻¹ = c⁻¹ * (c * m) * c⁻¹ := by group
      _ = c⁻¹ * (m * c) * c⁻¹ := by rw [this]
      _ = c⁻¹ * m := by group
  set g := n⁻¹ * n' with hg
  have hgN : g ∈ N := N.mul_mem (N.inv_mem hn) hn'
  have hz : g⁻¹ * z * g = z * c⁻¹ := by
    have e1 : n' * z * n'⁻¹ = (n * z * n⁻¹) * c := by rw [hcdef]; group
    have hcn' : n'⁻¹ * c⁻¹ * n' = c⁻¹ := by
      have := hcinvN n'⁻¹ (N.inv_mem hn')
      calc n'⁻¹ * c⁻¹ * n' = c⁻¹ * n'⁻¹ * n' := by rw [this]
        _ = c⁻¹ := by group
    calc g⁻¹ * z * g = n'⁻¹ * (n * z * n⁻¹) * n' := by rw [hg]; group
      _ = n'⁻¹ * ((n' * z * n'⁻¹) * c⁻¹) * n' := by rw [e1]; group
      _ = z * (n'⁻¹ * c⁻¹ * n') := by group
      _ = z * c⁻¹ := by rw [hcn']
  have hgM : g ∈ cenM N z := by
    refine h.mem_M_of_normalizes hgN fun m => ?_
    rw [mem_inf, mem_inf, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨hm, hmz⟩
      refine ⟨N.mul_mem (N.mul_mem hgN hm) (N.inv_mem hgN), ?_⟩
      have hmc := hcinvN m hm
      calc g * m * g⁻¹ * z = g * (m * (g⁻¹ * z * g)) * g⁻¹ := by group
        _ = g * (m * (z * c⁻¹)) * g⁻¹ := by rw [hz]
        _ = g * (m * z * c⁻¹) * g⁻¹ := by group
        _ = g * (z * m * c⁻¹) * g⁻¹ := by rw [hmz]
        _ = g * (z * (m * c⁻¹)) * g⁻¹ := by group
        _ = g * (z * (c⁻¹ * m)) * g⁻¹ := by rw [hmc]
        _ = g * ((z * c⁻¹) * m) * g⁻¹ := by group
        _ = g * ((g⁻¹ * z * g) * m) * g⁻¹ := by rw [hz]
        _ = z * (g * m * g⁻¹) := by group
    · rintro ⟨hm, hmz⟩
      have hmN : m ∈ N := by
        rw [show m = g⁻¹ * (g * m * g⁻¹) * g by group]
        exact N.mul_mem (N.mul_mem (N.inv_mem hgN) hm) hgN
      refine ⟨hmN, ?_⟩
      have hmc := hcinvN m hmN
      have h1 : m * (g⁻¹ * z * g) = (g⁻¹ * z * g) * m := by
        calc m * (g⁻¹ * z * g) = g⁻¹ * ((g * m * g⁻¹) * z) * g := by group
          _ = g⁻¹ * (z * (g * m * g⁻¹)) * g := by rw [hmz]
          _ = (g⁻¹ * z * g) * m := by group
      rw [hz] at h1
      have h2 : m * z * c⁻¹ = z * m * c⁻¹ := by
        calc m * z * c⁻¹ = m * (z * c⁻¹) := by group
          _ = z * c⁻¹ * m := h1
          _ = z * (c⁻¹ * m) := by group
          _ = z * (m * c⁻¹) := by rw [hmc]
          _ = z * m * c⁻¹ := by group
      exact mul_right_cancel h2
  have hgz := (conj_eq_iff hgN).2 hgM
  have hc1 : c = 1 := by
    have : z * c⁻¹ = z := by
      rw [← hz]
      calc g⁻¹ * z * g = g⁻¹ * (g * z * g⁻¹) * g := by rw [hgz]
        _ = z := by group
    have h3 : c⁻¹ = 1 := by
      calc c⁻¹ = z⁻¹ * (z * c⁻¹) := by group
        _ = 1 := by rw [this]; group
    exact inv_eq_one.1 h3
  calc n * z * n⁻¹ = (n * z * n⁻¹) * c := by rw [hc1, mul_one]
    _ = n' * z * n'⁻¹ := by rw [hcdef]; group

omit h in
theorem not_mem_centerIn_of_mem {t : G} (ht : t ∈ conjIn z N) (hz : z ∉ Asc77.centerIn z N) :
    t ∉ Asc77.centerIn z N := by
  intro htC
  apply hz
  obtain ⟨n, hn, rfl⟩ := ht
  have hc := mem_centralizer_iff.1 (mem_inf.1 htC).2 n hn
  have h1 : n * z * n⁻¹ = z := mul_left_cancel (a := n) (by rw [hc]; group)
  rw [h1] at htC
  exact htC

theorem card_conjIn_add_one_mul_le [Finite G] :
    (Nat.card (conjIn z N) + 1) * Nat.card (Asc77.centerIn z N) ≤ Nat.card (genV N z) := by
  classical
  have := h.isMulComm_V
  set C' : Subgroup (genV N z) := (Asc77.centerIn z N).subgroupOf (genV N z) with hC'def
  have hCV : Asc77.centerIn z N ≤ genV N z := inf_le_left
  have hC' : Nat.card C' = Nat.card (Asc77.centerIn z N) :=
    Nat.card_congr (subgroupOfEquivOfLe hCV).toEquiv
  have hcard := card_eq_card_quotient_mul_card_subgroup C'
  let f : conjIn z N → genV N z := fun t => ⟨t, subset_closure t.2⟩
  let F : Option (conjIn z N) → genV N z ⧸ C' := fun o => match o with
    | none => 1
    | some t => ((f t : genV N z) : genV N z ⧸ C')
  have hF1 : ∀ t, ((f t : genV N z) : genV N z ⧸ C') ≠ 1 := by
    intro t h1
    rw [QuotientGroup.eq_one_iff, hC'def, mem_subgroupOf] at h1
    exact not_mem_centerIn_of_mem t.2 h.z_not_mem_centerIn h1
  have hF : Function.Injective F := by
    rintro (_ | t) (_ | t') h1
    · rfl
    · exact absurd h1.symm (hF1 t')
    · exact absurd h1 (hF1 t)
    · have h2 := QuotientGroup.eq.1 h1
      rw [hC'def, mem_subgroupOf] at h2
      have h3 := h.eq_of_inv_mul_mem t.2 t'.2 (by simpa using h2)
      exact congrArg some (Subtype.ext h3)
  have hle := Nat.card_le_card_of_injective F hF
  rw [Finite.card_option] at hle
  rw [hcard, ← hC']
  exact Nat.mul_le_mul_right _ hle

end Hyp

end CFSG.LargeExtraspecial.Asc22
