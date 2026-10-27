module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSTransport

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup

section Sylow

variable {H : Type*} [Group H] [Finite H]

theorem exists_conj_mem_center_sylow {S : Subgroup H}
    (hS : Nat.card S = 2 ^ (Nat.card H).factorization 2) {k : H} (hk2 : k * k = 1) (hk1 : k ≠ 1)
    (hc : 2 ^ (Nat.card H).factorization 2 ∣ Nat.card (centralizer ({k} : Set H))) :
    ∃ g : H, g⁻¹ * k * g ∈ S ∧ ∀ s ∈ S, (g⁻¹ * k * g) * s = s * (g⁻¹ * k * g) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup H := centralizer ({k} : Set H) with hC
  have hkC : k ∈ C := Subgroup.mem_centralizer_singleton_iff.2 rfl
  set kC : C := ⟨k, hkC⟩ with hkCdef
  have hkCcen : kC ∈ Subgroup.center C := by
    rw [Subgroup.mem_center_iff]
    intro c
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 c.2)
  have hord : orderOf kC = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [pow_two]; exact Subtype.ext hk2
    · intro h
      exact hk1 (congrArg Subtype.val h)
  have hZnormal : (Subgroup.zpowers kC).Normal := by
    have : Subgroup.zpowers kC ≤ Subgroup.center C := (Subgroup.zpowers_le).2 hkCcen
    exact Subgroup.normal_of_le_center this
  have hZp : IsPGroup 2 (Subgroup.zpowers kC) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hord]
    norm_num
  obtain ⟨P₀⟩ : Nonempty (Sylow 2 C) := inferInstance
  have hkP₀ : kC ∈ (P₀ : Subgroup C) := by
    have := hZnormal
    exact IsPGroup.le_sylow_of_normal hZp P₀ (Subgroup.mem_zpowers kC)
  set P₁ : Subgroup H := (P₀ : Subgroup C).map C.subtype with hP₁
  have hcardP₁ : Nat.card P₁ = 2 ^ (Nat.card H).factorization 2 := by
    have h1 : Nat.card P₁ = 2 ^ (Nat.card C).factorization 2 := by
      rw [hP₁, Subgroup.card_map_of_injective C.subtype_injective]
      exact P₀.card_eq_multiplicity
    have h2 : (Nat.card H).factorization 2 ≤ (Nat.card C).factorization 2 :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').1 hc
    have h3 : 2 ^ (Nat.card C).factorization 2 ∣ Nat.card H := by
      rw [← h1]; exact P₁.card_subgroup_dvd_card
    have h4 : (Nat.card C).factorization 2 ≤ (Nat.card H).factorization 2 :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').1 h3
    rw [h1, le_antisymm h2 h4]
  let SP : Sylow 2 H := Sylow.ofCard S hS
  let PP : Sylow 2 H := Sylow.ofCard P₁ hcardP₁
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H SP PP
  have hkP : k ∈ P₁ := ⟨kC, hkP₀, rfl⟩
  have hPP : (PP : Subgroup H) = P₁ := rfl
  have hSP : (SP : Subgroup H) = S := rfl
  have hmem : ∀ x : H, x ∈ P₁ ↔ ∃ s ∈ S, g * s * g⁻¹ = x := by
    intro x
    rw [← hPP, ← hg, Sylow.coe_subgroup_smul, hSP, Subgroup.mem_smul_pointwise_iff_exists]
    exact Iff.rfl
  obtain ⟨s, hsS, hsk⟩ := (hmem k).1 hkP
  have hskeq : g⁻¹ * k * g = s := by rw [← hsk]; group
  refine ⟨g, hskeq ▸ hsS, fun s' hs' => ?_⟩
  rw [hskeq]
  have hP₁C : g * s' * g⁻¹ ∈ P₁ := (hmem _).2 ⟨s', hs', rfl⟩
  have hC' : g * s' * g⁻¹ ∈ C := by
    obtain ⟨c, _, hc⟩ := hP₁C
    rw [← hc]
    exact c.2
  have hcomm := Subgroup.mem_centralizer_singleton_iff.1 hC'
  calc s * s' = g⁻¹ * (k * (g * s' * g⁻¹)) * g := by rw [← hsk]; group
    _ = g⁻¹ * ((g * s' * g⁻¹) * k) * g := by rw [hcomm]
    _ = s' * s := by rw [← hsk]; group

end Sylow

section Fusion

variable {Y : Type} [Group Y] [Finite Y]

theorem twoCentralFused_of_sylow {D S : Subgroup Y} (hSD : S ≤ D)
    (hS : Nat.card S = 2 ^ twoAdic D) {ζ : Y}
    (hfuse : ∀ x ∈ S, x * x = 1 → x ≠ 1 → (∀ s ∈ S, x * s = s * x) →
      ∃ c ∈ D, c * ζ * c⁻¹ = x) : TwoCentralFused D := by
  have key : ∀ {k : Y}, k ∈ D → k * k = 1 → k ≠ 1 →
      twoAdic D ≤ twoAdic (D ⊓ centralizer ({k} : Set Y)) → ∃ c ∈ D, c * ζ * c⁻¹ = k := by
    intro k hk hk2 hk1 hkm
    have hkD2 : (⟨k, hk⟩ : D) * ⟨k, hk⟩ = 1 := Subtype.ext hk2
    have hkD1 : (⟨k, hk⟩ : D) ≠ 1 := fun h => hk1 (congrArg Subtype.val h)
    have hSD' : Nat.card (S.subgroupOf D) = 2 ^ (Nat.card D).factorization 2 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSD).toEquiv]
      exact hS
    have hc : 2 ^ (Nat.card D).factorization 2 ∣
        Nat.card (centralizer ({(⟨k, hk⟩ : D)} : Set D)) := by
      rw [← card_inf_centralizer_eq D hk]
      have hpos : Nat.card (D ⊓ centralizer ({k} : Set Y) : Subgroup Y) ≠ 0 := Nat.card_pos.ne'
      exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hpos).2 hkm
    obtain ⟨g, hg1, hg2⟩ := exists_conj_mem_center_sylow hSD' hkD2 hkD1 hc
    have hg1' : ((g⁻¹ * ⟨k, hk⟩ * g : D) : Y) ∈ S := Subgroup.mem_subgroupOf.1 hg1
    have hgk : ((g⁻¹ * ⟨k, hk⟩ * g : D) : Y) = (g : Y)⁻¹ * k * g := rfl
    have hxx : ((g : Y)⁻¹ * k * g) * ((g : Y)⁻¹ * k * g) = 1 := by
      calc ((g : Y)⁻¹ * k * g) * ((g : Y)⁻¹ * k * g) = (g : Y)⁻¹ * (k * k) * g := by group
        _ = 1 := by rw [hk2]; group
    have hx1 : (g : Y)⁻¹ * k * g ≠ 1 := by
      intro h
      apply hk1
      calc k = (g : Y) * ((g : Y)⁻¹ * k * g) * (g : Y)⁻¹ := by group
        _ = 1 := by rw [h]; group
    have hxc : ∀ s ∈ S, ((g : Y)⁻¹ * k * g) * s = s * ((g : Y)⁻¹ * k * g) := by
      intro s hs
      have := hg2 ⟨s, hSD hs⟩ (Subgroup.mem_subgroupOf.2 hs)
      exact congrArg Subtype.val this
    obtain ⟨c, hcD, hcx⟩ := hfuse _ (hgk ▸ hg1') hxx hx1 hxc
    refine ⟨(g : Y) * c, D.mul_mem g.2 hcD, ?_⟩
    calc (g : Y) * c * ζ * ((g : Y) * c)⁻¹ = (g : Y) * (c * ζ * c⁻¹) * (g : Y)⁻¹ := by group
      _ = k := by rw [hcx]; group
  intro k hk k' hk' hk2 hk'2 hk1 hk'1 hkm hk'm
  obtain ⟨c, hc, hck⟩ := key hk hk2 hk1 hkm
  obtain ⟨c', hc', hck'⟩ := key hk' hk'2 hk'1 hk'm
  refine ⟨c' * c⁻¹, D.mul_mem hc' (D.inv_mem hc), ?_⟩
  calc c' * c⁻¹ * k * (c' * c⁻¹)⁻¹ = c' * (c⁻¹ * k * c) * c'⁻¹ := by group
    _ = c' * ζ * c'⁻¹ := by
      congr 2
      rw [← hck]
      group
    _ = k' := hck'

theorem twoAdic_le_of_sylow_centralizer {D S : Subgroup Y} (hSD : S ≤ D)
    (hS : Nat.card S = 2 ^ twoAdic D) {s : Y} (hs : ∀ x ∈ S, x * s = s * x) :
    twoAdic D ≤ twoAdic (D ⊓ centralizer ({s} : Set Y)) := by
  have hle : S ≤ D ⊓ centralizer ({s} : Set Y) := fun x hx =>
    ⟨hSD hx, Subgroup.mem_centralizer_singleton_iff.2 (hs x hx)⟩
  have hdvd : 2 ^ twoAdic D ∣ Nat.card (D ⊓ centralizer ({s} : Set Y) : Subgroup Y) := by
    rw [← hS]
    exact Subgroup.card_dvd_of_le hle
  exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').1 hdvd

end Fusion

section Generation

variable {Y : Type*} [Group Y]

theorem closure_pair_eq_of_simple {x y : Y} (hx2 : x * x = 1) (hy : y ≠ 1)
    (hD : IsSimpleGroup (Subgroup.closure {x, y})) :
    Subgroup.closure {y, x * y * x} = Subgroup.closure {x, y} := by
  set D : Subgroup Y := Subgroup.closure {x, y} with hDdef
  set N : Subgroup Y := Subgroup.closure {y, x * y * x} with hNdef
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hxD : x ∈ D := Subgroup.subset_closure (Set.mem_insert _ _)
  have hyD : y ∈ D := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hND : N ≤ D := by
    rw [hNdef, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact hyD
    · exact D.mul_mem (D.mul_mem hxD hyD) hxD
  have hyN : y ∈ N := Subgroup.subset_closure (Set.mem_insert _ _)
  have hxyx : x * y * x ∈ N := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hconj : ∀ h ∈ N, x * h * x ∈ N := by
    intro h hh
    have hle : N.map (MulAut.conj x).toMonoidHom ≤ N := by
      rw [hNdef, MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨a, ha, rfl⟩
      rcases ha with h | h
      · rw [h]
        show x * y * x⁻¹ ∈ N
        rw [hxinv]
        exact hxyx
      · rw [h]
        show x * (x * y * x) * x⁻¹ ∈ N
        rw [hxinv]
        have : x * (x * y * x) * x = y := by
          calc x * (x * y * x) * x = (x * x) * y * (x * x) := by group
            _ = y := by rw [hx2]; group
        rw [this]
        exact hyN
    have := hle ⟨h, hh, rfl⟩
    simpa [MulAut.conj_apply, hxinv] using this
  have hxnorm : x ∈ Subgroup.normalizer (N : Set Y) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => ?_, fun hh => ?_⟩
    · rw [hxinv]
      exact hconj h hh
    · have := hconj _ hh
      rw [hxinv] at hh
      have e : x * (x * h * x⁻¹) * x = h := by
        rw [hxinv]
        calc x * (x * h * x) * x = (x * x) * h * (x * x) := by group
          _ = h := by rw [hx2]; group
      rwa [e] at this
  have hDnorm : D ≤ Subgroup.normalizer (N : Set Y) := by
    rw [hDdef, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact hxnorm
    · exact Subgroup.le_normalizer hyN
  have hnormal : (N.subgroupOf D).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hND).2 hDnorm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf D) with h | h
  · exfalso
    apply hy
    have : (⟨y, hyD⟩ : D) ∈ N.subgroupOf D := Subgroup.mem_subgroupOf.2 hyN
    rw [h, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  · exact le_antisymm hND (Subgroup.subgroupOf_eq_top.1 h)

end Generation

end CFSG.EvenSporadicStandard.Solomon78
