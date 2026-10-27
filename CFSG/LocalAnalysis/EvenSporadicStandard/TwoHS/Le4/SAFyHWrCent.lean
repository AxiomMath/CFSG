module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyHWrDef
public import Mathlib.GroupTheory.Perm.Centralizer

public section

namespace CFSG.EvenSporadicStandard.TwoHS.SignWr

open Equiv Equiv.Perm Subgroup

theorem involution_cases (x : Perm (Fin 5)) (hx : x * x = 1) :
    (x = 1 ∧ Nat.card (centralizer ({x} : Set (Perm (Fin 5)))) = 120) ∨
    (x ≠ 1 ∧ Nat.card (centralizer ({x} : Set (Perm (Fin 5)))) = 12) ∨
    (x ≠ 1 ∧ Nat.card (centralizer ({x} : Set (Perm (Fin 5)))) = 8 ∧ sign x = 1) := by
  by_cases h1 : x = 1
  · left
    subst h1
    refine ⟨rfl, ?_⟩
    rw [nat_card_centralizer]
    simp [Nat.factorial]
  · right
    have hord : orderOf x = 2 := orderOf_eq_prime (by rwa [pow_two]) h1
    obtain ⟨n, hn⟩ := cycleType_prime_order (σ := x) (by rw [hord]; exact Nat.prime_two)
    rw [hord] at hn
    have hsum : x.cycleType.sum ≤ Fintype.card (Fin 5) := sum_cycleType_le x
    rw [hn, Multiset.sum_replicate, Fintype.card_fin] at hsum
    have h01 : n = 0 ∨ n = 1 := by simp at hsum; omega
    have hc := nat_card_centralizer x
    rw [hn, Fintype.card_fin] at hc
    rcases h01 with rfl | rfl
    · left
      refine ⟨h1, ?_⟩
      simpa [Nat.factorial] using hc
    · right
      refine ⟨h1, ?_, ?_⟩
      · simpa [Nat.factorial] using hc
      · rw [sign_of_cycleType, hn]
        decide

theorem sign_eq_neg_one_of_orderOf_eq_four_of_card_le {α : Type*} [Fintype α] [DecidableEq α]
    (hα : Fintype.card α ≤ 5) {d : Perm α} (h4 : orderOf d = 4) : sign d = -1 := by
  have hm : ∀ n ∈ d.cycleType, n = 2 ∨ n = 4 := by
    intro n hn
    have h1 : n ∣ 4 := h4 ▸ dvd_of_mem_cycleType hn
    have h2 : 2 ≤ n := two_le_of_mem_cycleType hn
    have h3 : n ≤ 4 := Nat.le_of_dvd (by norm_num) h1
    have : n = 2 ∨ n = 3 ∨ n = 4 := by omega
    rcases this with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact absurd h1 (by norm_num)
    · exact Or.inr rfl
  have h4mem : 4 ∈ d.cycleType := by
    by_contra hno
    have : d.cycleType.lcm ∣ 2 := Multiset.lcm_dvd.2 fun n hn => by
      rcases hm n hn with rfl | rfl
      · exact dvd_rfl
      · exact absurd hn hno
    rw [lcm_cycleType, h4] at this
    omega
  obtain ⟨m, hm'⟩ := Multiset.exists_cons_of_mem h4mem
  have hsum : d.cycleType.sum ≤ 5 := (sum_cycleType_le d).trans hα
  rw [hm', Multiset.sum_cons] at hsum
  have hm0 : m = 0 := by
    have hm1 : m.sum ≤ 1 := by omega
    refine Multiset.eq_zero_of_forall_notMem fun n hn => ?_
    have h2 := two_le_of_mem_cycleType (hm' ▸ Multiset.mem_cons_of_mem hn : n ∈ d.cycleType)
    have h3 : n ≤ m.sum := Multiset.le_sum_of_mem hn
    omega
  rw [sign_of_cycleType, hm', hm0]
  simp only [Multiset.sum_cons, Multiset.sum_zero, Multiset.card_cons, Multiset.card_zero]
  exact Odd.neg_one_pow (by decide)

section Counting

variable (a b : Perm (Fin 5))

theorem mk_mem_centralizer {c d : Perm (Fin 5)}
    (hc : c ∈ centralizer ({a} : Set (Perm (Fin 5))))
    (hd : d ∈ centralizer ({b} : Set (Perm (Fin 5)))) :
    mk c d 1 ∈ centralizer ({mk a b 1} : Set Wr) := by
  rw [mem_centralizer_singleton_iff] at hc hd ⊢
  rw [mk_mul_one, mk_mul_one, hc, hd]

theorem coords_mem_centralizer {g : Wr} (hg : g ∈ centralizer ({mk a b 1} : Set Wr))
    (h1 : g.right = 1) :
    g.left 1 ∈ centralizer ({a} : Set (Perm (Fin 5))) ∧
      g.left eps ∈ centralizer ({b} : Set (Perm (Fin 5))) := by
  rw [← mk_eta g, h1, mem_centralizer_singleton_iff, mk_mul_one, mk_mul_one, mk_inj] at hg
  rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  exact ⟨hg.1, hg.2.1⟩

theorem card_mul_le_card_centralizer :
    Nat.card (centralizer ({a} : Set (Perm (Fin 5)))) *
        Nat.card (centralizer ({b} : Set (Perm (Fin 5)))) ≤
      Nat.card (centralizer ({mk a b 1} : Set Wr)) := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective
    (fun p => (⟨mk p.1.1 p.2.1 1, mk_mem_centralizer a b p.1.2 p.2.2⟩ :
      centralizer ({mk a b 1} : Set Wr))) ?_
  rintro ⟨⟨c, hc⟩, ⟨d, hd⟩⟩ ⟨⟨c', hc'⟩, ⟨d', hd'⟩⟩ h
  have h' := congrArg (fun g : centralizer ({mk a b 1} : Set Wr) => (g : Wr)) h
  simp only [mk_inj] at h'
  obtain ⟨rfl, rfl, -⟩ := h'
  rfl

theorem card_centralizer_le :
    Nat.card (centralizer ({mk a b 1} : Set Wr)) ≤
      2 * (Nat.card (centralizer ({a} : Set (Perm (Fin 5)))) *
        Nat.card (centralizer ({b} : Set (Perm (Fin 5))))) := by
  let π : centralizer ({mk a b 1} : Set Wr) →* Multiplicative (ZMod 2) :=
    RegularWreathProduct.rightHom.comp (centralizer ({mk a b 1} : Set Wr)).subtype
  have h1 := π.ker.card_mul_index
  rw [Subgroup.index_ker] at h1
  have h2 : Nat.card π.range ≤ 2 := by
    have := Subgroup.card_le_card_group π.range
    simpa [Nat.card_eq_fintype_card] using this
  have h3 : Nat.card π.ker ≤ Nat.card (centralizer ({a} : Set (Perm (Fin 5)))) *
      Nat.card (centralizer ({b} : Set (Perm (Fin 5)))) := by
    rw [← Nat.card_prod]
    refine Nat.card_le_card_of_injective
      (fun g => (⟨(g.1 : Wr).left 1, (coords_mem_centralizer a b g.1.2 g.2).1⟩,
        ⟨(g.1 : Wr).left eps, (coords_mem_centralizer a b g.1.2 g.2).2⟩)) ?_
    rintro ⟨⟨g, hg⟩, hgπ⟩ ⟨⟨g', hg'⟩, hgπ'⟩ h
    have hr : g.right = 1 := hgπ
    have hr' : g'.right = 1 := hgπ'
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
    have : g = g' := ext3 h.1 h.2 (by rw [hr, hr'])
    subst this
    rfl
  calc Nat.card (centralizer ({mk a b 1} : Set Wr)) = Nat.card π.ker * Nat.card π.range :=
        h1.symm
    _ ≤ (Nat.card (centralizer ({a} : Set (Perm (Fin 5)))) *
          Nat.card (centralizer ({b} : Set (Perm (Fin 5))))) * 2 := Nat.mul_le_mul h3 h2
    _ = _ := by ring

theorem structure_of_card {a b : Perm (Fin 5)} (ha : a * a = 1) (hb : b * b = 1)
    (hne : mk a b 1 ≠ 1) (hc : Nat.card (centralizer ({mk a b 1} : Set Wr)) = 960) :
    (a = 1 ∧ b ≠ 1 ∧ sign b = 1) ∨ (a ≠ 1 ∧ sign a = 1 ∧ b = 1) := by
  have hL := card_mul_le_card_centralizer a b
  have hU := card_centralizer_le a b
  rw [hc] at hL hU
  rcases involution_cases a ha with ⟨rfl, hna⟩ | ⟨ha1, hna⟩ | ⟨ha1, hna, hsa⟩ <;>
    rcases involution_cases b hb with ⟨rfl, hnb⟩ | ⟨hb1, hnb⟩ | ⟨hb1, hnb, hsb⟩
  · exact absurd mk_one_one_one hne
  · rw [hna, hnb] at hL
    omega
  · exact Or.inl ⟨rfl, hb1, hsb⟩
  · rw [hna, hnb] at hL
    omega
  · rw [hna, hnb] at hU
    omega
  · rw [hna, hnb] at hU
    omega
  · exact Or.inr ⟨ha1, hsa, rfl⟩
  · rw [hna, hnb] at hU
    omega
  · rw [hna, hnb] at hU
    omega

end Counting

section Retraction

variable (a : Perm (Fin 5)) (ha : a ≠ 1)

include ha in
theorem right_eq_one_of_mem_centralizer {g : Wr}
    (hg : g ∈ centralizer ({mk a 1 1} : Set Wr)) : g.right = 1 := by
  by_contra hr
  have hr' : g.right = eps := (eq_one_or_eps _).resolve_left hr
  rw [← mk_eta g, hr', mem_centralizer_singleton_iff, mk_mul_one, mk_mul_eps, mk_inj] at hg
  apply ha
  have h1 := hg.1
  simpa using h1.symm

@[expose] def secondCoord : centralizer ({mk a 1 1} : Set Wr) →* Perm (Fin 5) where
  toFun g := (g : Wr).left eps
  map_one' := rfl
  map_mul' g h := by
    have hg := right_eq_one_of_mem_centralizer a ha g.2
    simp [RegularWreathProduct.mul_left, hg]

theorem secondCoord_apply (g : centralizer ({mk a 1 1} : Set Wr)) :
    secondCoord a ha g = (g : Wr).left eps := rfl

theorem inSecond_mem_centralizer (u : Perm (Fin 5)) :
    inSecond u ∈ centralizer ({mk a 1 1} : Set Wr) := by
  rw [mem_centralizer_singleton_iff, inSecond_apply, mk_mul_one, mk_mul_one]
  simp

include ha in
theorem eq_inFirst_of_secondCoord_eq_one {g : centralizer ({mk a 1 1} : Set Wr)}
    (hg : secondCoord a ha g = 1) : (g : Wr) = inFirst ((g : Wr).left 1) := by
  have hr := right_eq_one_of_mem_centralizer a ha g.2
  have hg' : (g : Wr).left eps = 1 := hg
  calc (g : Wr) = mk ((g : Wr).left 1) ((g : Wr).left eps) (g : Wr).right := (mk_eta _).symm
    _ = inFirst ((g : Wr).left 1) := by rw [hg', hr]; rfl

end Retraction

end CFSG.EvenSporadicStandard.TwoHS.SignWr
