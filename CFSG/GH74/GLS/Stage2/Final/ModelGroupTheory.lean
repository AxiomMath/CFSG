module

public import CFSG.GroupTheory.LocalCores.Layer

public section

namespace CFSG.GH74.GLS.Stage2.Final.ModelGT

open Subgroup

theorem normal_le_center_or_top {H : Type*} [Group H] (hH : IsQuasisimple H) (N : Subgroup H)
    [N.Normal] : N ≤ Subgroup.center H ∨ N = ⊤ :=
  (CFSG.LocalCores.quasisimple_normal_subgroups hH inferInstance).symm

theorem normal_odd_eq_bot {H : Type*} [Group H] [Finite H] (hH : IsQuasisimple H)
    (hZ : IsPGroup 2 ↥(Subgroup.center H)) (hev : 2 ∣ Nat.card H) (N : Subgroup H) [N.Normal]
    (hN : Odd (Nat.card N)) : N = ⊥ := by
  rcases normal_le_center_or_top hH N with h | h
  · obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (hZ.to_le h)
    have hn0 : n = 0 := by
      by_contra hne
      have hev2 : Even (2 ^ n) := Nat.even_pow.2 ⟨even_two, hne⟩
      rw [← hn] at hev2
      exact (Nat.not_even_iff_odd.2 hN) hev2
    subst hn0
    exact Subgroup.eq_bot_of_card_eq N (by simpa using hn)
  · exfalso
    rw [h, Subgroup.card_top] at hN
    exact (Nat.not_even_iff_odd.2 hN) (even_iff_two_dvd.2 hev)

theorem closure_two_elements_eq_top {H : Type*} [Group H] (hH : IsQuasisimple H) (x : H)
    (hx : ∃ k : ℕ, x ^ (2 ^ k) = 1) (hxc : x ∉ Subgroup.center H) :
    Subgroup.closure {y : H | ∃ k : ℕ, y ^ (2 ^ k) = 1} = ⊤ := by
  have hnorm : (Subgroup.closure {y : H | ∃ k : ℕ, y ^ (2 ^ k) = 1}).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hle : Subgroup.closure {y : H | ∃ k : ℕ, y ^ (2 ^ k) = 1} ≤
        (Subgroup.closure {y : H | ∃ k : ℕ, y ^ (2 ^ k) = 1}).comap
          (MulAut.conj g).toMonoidHom := by
      rw [Subgroup.closure_le]
      rintro y ⟨k, hk⟩
      refine Subgroup.subset_closure ⟨k, ?_⟩
      show (g * y * g⁻¹) ^ (2 ^ k) = 1
      rw [conj_pow, hk]
      group
    exact hle hn
  rcases normal_le_center_or_top hH (Subgroup.closure {y : H | ∃ k : ℕ, y ^ (2 ^ k) = 1}) with h | h
  · exact absurd (h (Subgroup.subset_closure hx)) hxc
  · exact h

theorem index_two_commutator_le {C : Type*} [Group C] (C₀ : Subgroup C) (h : C₀.index = 2) :
    ⁅(⊤ : Subgroup C), ⊤⁆ ≤ C₀ := by
  have hn : C₀.Normal := Subgroup.normal_of_index_eq_two h
  rw [Subgroup.commutator_le]
  intro a _ b _
  rw [commutatorElement_def]
  simp only [Subgroup.mul_mem_iff_of_index_two h, inv_mem_iff]
  tauto

theorem layer_eq_sup {C : Type*} [Group C] {K₁ K₂ C₀ : Subgroup C} [C₀.Normal]
    (hK₁ : IsComponent K₁) (hK₂ : IsComponent K₂) (hidx : C₀.index = 2)
    (hcomm : ⁅C₀, C₀⁆ ≤ K₁ ⊔ K₂) : layer C = K₁ ⊔ K₂ := by
  refine le_antisymm (sSup_le fun L hL => ?_)
    (sup_le (CFSG.LocalCores.component_le_layer hK₁) (CFSG.LocalCores.component_le_layer hK₂))
  have hLperf : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp hL.1.1
  have hLC₀ : L ≤ C₀ := by
    calc L = ⁅L, L⁆ := hLperf.symm
      _ ≤ ⁅(⊤ : Subgroup C), ⊤⁆ := Subgroup.commutator_mono le_top le_top
      _ ≤ C₀ := index_two_commutator_le C₀ hidx
  calc L = ⁅L, L⁆ := hLperf.symm
    _ ≤ ⁅C₀, C₀⁆ := Subgroup.commutator_mono hLC₀ hLC₀
    _ ≤ K₁ ⊔ K₂ := hcomm

theorem isComponent_subgroupOf {G : Type*} [Group G] {K C₀ C : Subgroup G}
    (hK : IsQuasisimple ↥K) (hKC₀ : K ≤ C₀) (hC₀C : C₀ ≤ C)
    (hn₁ : (K.subgroupOf C₀).Normal) (hn₂ : (C₀.subgroupOf C).Normal) :
    IsComponent (K.subgroupOf C) := by
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe (hKC₀.trans hC₀C)).symm hK, ?_⟩
  refine Subgroup.IsSubnormal.step _ (C₀.subgroupOf C) (fun x hx => hKC₀ hx)
    hn₂.isSubnormal ⟨fun n hn g => ?_⟩
  exact hn₁.conj_mem ⟨(n : G), n.2⟩ hn ⟨(g : G), g.2⟩

theorem mem_of_odd_orderOf_sup {C : Type*} [Group C] [Finite C] {E S : Subgroup C} [E.Normal]
    (hS : IsPGroup 2 ↥S) {x : C} (hx : x ∈ E ⊔ S) (hodd : Odd (orderOf x)) : x ∈ E := by
  obtain ⟨e, he, s, hs, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hx
  suffices hsE : s ∈ E from mul_mem he hsE
  obtain ⟨k, hk⟩ := hS ⟨s, hs⟩
  have hsk : s ^ (2 ^ k) = 1 := congrArg Subtype.val hk
  have h1 : orderOf (((e * s : C) : C ⧸ E)) ∣ orderOf (e * s) :=
    orderOf_map_dvd (QuotientGroup.mk' E) (e * s)
  have h2 : orderOf ((s : C ⧸ E)) ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow, hsk, QuotientGroup.mk_one])
  have h3 : (((e * s : C) : C ⧸ E)) = (s : C ⧸ E) := by
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff e).2 he, one_mul]
  rw [h3] at h1
  have hcop : Nat.Coprime (orderOf (s : C ⧸ E)) (orderOf (e * s)) :=
    Nat.Coprime.coprime_dvd_left h2 (Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hodd))
  exact (QuotientGroup.eq_one_iff s).1 (orderOf_eq_one_iff.1 (hcop.eq_one_of_dvd h1))

theorem sup_eq_top_of_isPGroup_quotient {C : Type*} [Group C] [Finite C] (S : Sylow 2 C)
    (N : Subgroup C) [N.Normal] (hN : IsPGroup 2 (C ⧸ N)) : (S : Subgroup C) ⊔ N = ⊤ := by
  have hT1 : ((S : Subgroup C) ⊔ N).index ∣ (S : Subgroup C).index :=
    Subgroup.index_dvd_of_le le_sup_left
  have hT2 : ((S : Subgroup C) ⊔ N).index ∣ N.index := Subgroup.index_dvd_of_le le_sup_right
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hN
  have hNidx : N.index = 2 ^ n := hn
  rw [hNidx] at hT2
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hT2
  rw [← Subgroup.index_eq_one]
  rcases Nat.eq_zero_or_pos j with rfl | hjpos
  · simpa using hj
  · exfalso
    refine Sylow.not_dvd_index S (dvd_trans ?_ hT1)
    rw [hj]
    exact dvd_pow_self 2 hjpos.ne'

theorem pPrimeCore_eq_of_normal_odd {C : Type*} [Group C] [Finite C] (R : Subgroup C) [R.Normal]
    (hR : Odd (Nat.card R))
    (hmax : ∀ N : Subgroup C, N.Normal → Odd (Nat.card N) → N ≤ R) : pPrimeCore 2 C = R :=
  le_antisymm (sSup_le fun K hK => hmax K hK.1 (Nat.coprime_two_left.1 hK.2))
    (le_sSup ⟨inferInstance, Nat.coprime_two_left.2 hR⟩)

end CFSG.GH74.GLS.Stage2.Final.ModelGT
