module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526Defs
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526A
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526P0b
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15LiftBasic
import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.Bridge

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup
  KFactsPair
open scoped commutatorElement

section Transfer

theorem exists_fixed_point_mul_aux_central {G : Type} [Group G] [Finite G]
    (hG : _root_.commutator G = ⊤) {K : Subgroup G} (hK : K ≤ Subgroup.center G)
    (hidx : K.index = 168) {z : G} (hz : z ∈ K) (hz3 : z ^ 3 = 1) : z = 1 := by
  classical
  haveI hKn : K.Normal := ⟨fun n hn g => by
    have h := Subgroup.mem_center_iff.1 (hK hn) g
    have : g * n * g⁻¹ = n := by rw [h]; group
    rw [this]; exact hn⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : 3 ∣ Nat.card (G ⧸ K) := by
    rw [← Subgroup.index_eq_card, hidx]; norm_num
  obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' (G := G ⧸ K) 3 h3
  let Hc : Subgroup G := (Subgroup.zpowers q).comap (QuotientGroup.mk' K)
  have hHc : Hc.index = 56 := by
    have h1 : Hc.index = (Subgroup.zpowers q).index :=
      Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective K)
    have h2 := Subgroup.index_mul_card (Subgroup.zpowers q)
    rw [Nat.card_zpowers, hq, ← Subgroup.index_eq_card, hidx] at h2
    omega
  have hHcomm : ∀ a b : ↥Hc, a * b = b * a := by
    let f : ↥Hc →* ↥(Subgroup.zpowers q) :=
      ((QuotientGroup.mk' K).comp Hc.subtype).codRestrict (Subgroup.zpowers q) (fun h => h.2)
    haveI : IsCyclic ↥(Subgroup.zpowers q) := inferInstance
    refine commutative_of_cyclic_center_quotient f ?_
    intro h hh
    have hh1 : (QuotientGroup.mk' K) (h : G) = 1 := congrArg Subtype.val hh
    have hhK : (h : G) ∈ K := (QuotientGroup.eq_one_iff (N := K) (h : G)).1 hh1
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.1 (hK hhK) g)
  haveI : IsMulCommutative ↥Hc := ⟨⟨hHcomm⟩⟩
  letI : CommGroup ↥Hc := { (inferInstance : Group ↥Hc) with mul_comm := hHcomm }
  haveI : Hc.FiniteIndex := inferInstance
  let ϕ : ↥Hc →* ↥Hc := MonoidHom.id ↥Hc
  have hV : ϕ.transfer = 1 := by
    have h1 := Abelianization.commutator_subset_ker (ϕ.transfer)
    rw [hG, top_le_iff, MonoidHom.ker_eq_top_iff] at h1
    exact h1
  have hzc : ∀ (k : ℕ) (g₀ : G), g₀⁻¹ * z ^ k * g₀ ∈ Hc → g₀⁻¹ * z ^ k * g₀ = z ^ k := by
    intro k g₀ _
    have h := Subgroup.mem_center_iff.1 ((Subgroup.center G).pow_mem (hK hz) k) g₀
    calc g₀⁻¹ * z ^ k * g₀ = g₀⁻¹ * (z ^ k * g₀) := by group
      _ = g₀⁻¹ * (g₀ * z ^ k) := by rw [h]
      _ = z ^ k := by group
  have hVz := MonoidHom.transfer_eq_pow ϕ z hzc
  rw [hV] at hVz
  have h56 : z ^ 56 = 1 := by
    have h1 := congrArg (fun t : ↥Hc => (t : G)) hVz
    have h2 : z ^ Hc.index = 1 := by simpa [ϕ] using h1.symm
    rwa [hHc] at h2
  have h2 : z ^ 2 = 1 := by
    have : z ^ 56 = (z ^ 3) ^ 18 * z ^ 2 := by group
    rw [this, hz3] at h56
    simpa using h56
  calc z = z ^ 3 * (z ^ 2)⁻¹ := by group
    _ = 1 := by rw [hz3, h2]; simp

end Transfer

section XLevelAux

variable {X : Type} [Group X] [Finite X]

theorem exists_fixed_point_mul_aux_not_centralizes {L N : Subgroup X} (hL : IsC2 L)
    (hN : IsNaturalLThreeTwo L N) (hC : CFSG.pCore 2 X ≤ Subgroup.centralizer (N : Set X))
    {a : X} (ha : a ∈ L) (ha3 : orderOf a = 3) : ∃ n ∈ N, a * n * a⁻¹ ≠ n := by
  by_contra hcon
  push Not at hcon
  have hQ := hL.component.2.2
  let Q := QuotientGroup.mk' (CFSG.pCore 2 X)
  let K₀ : Subgroup X := Subgroup.centralizer (N : Set X) ⊓ L
  have haK : a ∈ K₀ := by
    refine ⟨?_, ha⟩
    show a ∈ Subgroup.centralizer (N : Set X)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have := hcon x hx
    calc x * a = a * x * a⁻¹ * a := by rw [this]
      _ = a * x := by group
  let ψ : ↥L →* ↥(barO2 L) :=
    (Q.comp L.subtype).codRestrict (barO2 L) (fun l => Subgroup.mem_map_of_mem _ l.2)
  have hψs : Function.Surjective ψ := by
    rintro ⟨y, l, hl, rfl⟩
    exact ⟨⟨l, hl⟩, rfl⟩
  have hker : ψ.ker ≤ K₀.subgroupOf L := by
    intro l hl
    have h1 : Q (l : X) = 1 := congrArg Subtype.val hl
    have h2 : (l : X) ∈ CFSG.pCore 2 X := (QuotientGroup.eq_one_iff (l : X)).1 h1
    exact ⟨hC h2, l.2⟩
  have hnorm : (K₀.subgroupOf L).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    refine ⟨?_, L.mul_mem (L.mul_mem g.2 hn.2) (L.inv_mem g.2)⟩
    show ((g * n * g⁻¹ : ↥L) : X) ∈ Subgroup.centralizer (N : Set X)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hgn : ((g⁻¹ : ↥L) : X) ∈ Subgroup.normalizer (N : Set X) := hN.2.2.1 (L.inv_mem g.2)
    have hy : (g : X)⁻¹ * x * (g : X) ∈ N := by
      have := (Subgroup.mem_normalizer_iff.1 hgn x).1 hx
      simpa using this
    have h3 := (Subgroup.mem_centralizer_iff.1 hn.1) _ hy
    show x * (g * n * g⁻¹ : ↥L) = (g * n * g⁻¹ : ↥L) * x
    calc x * ((g : X) * n * (g : X)⁻¹)
        = (g : X) * (((g : X)⁻¹ * x * (g : X)) * n) * (g : X)⁻¹ := by group
      _ = (g : X) * (n * ((g : X)⁻¹ * x * (g : X))) * (g : X)⁻¹ := by rw [h3]
      _ = (g : X) * n * (g : X)⁻¹ * x := by group
  let Kb : Subgroup ↥(barO2 L) := (K₀.subgroupOf L).map ψ
  have hKbn : Kb.Normal := hnorm.map ψ hψs
  have hidx : Kb.index = 168 := by
    have h1 := Subgroup.index_map (K₀.subgroupOf L) ψ
    rw [sup_eq_left.2 hker, MonoidHom.range_eq_top.2 hψs, Subgroup.index_top, mul_one] at h1
    rw [h1]
    have h2 : (K₀.subgroupOf L).index = (Subgroup.centralizer (N : Set X)).relIndex L :=
      Subgroup.inf_relIndex_right _ _
    rw [h2]
    exact hN.2.2.2
  rcases liftOf_central_ext_aux1 hQ hKbn with hcen | htop
  · have hz : ψ ⟨a, ha⟩ ∈ Kb :=
      Subgroup.mem_map_of_mem ψ (show (⟨a, ha⟩ : ↥L) ∈ K₀.subgroupOf L from haK)
    have ha1 : a ^ 3 = 1 := by
      have := pow_orderOf_eq_one a
      rwa [ha3] at this
    have hz3 : (ψ ⟨a, ha⟩) ^ 3 = 1 := by
      rw [← map_pow]
      have : (⟨a, ha⟩ : ↥L) ^ 3 = 1 := Subtype.ext (by simpa using ha1)
      rw [this, map_one]
    have h1 := exists_fixed_point_mul_aux_central hQ.1 hcen hidx hz hz3
    have h2 : Q a = 1 := congrArg Subtype.val h1
    have h3 : a ∈ CFSG.pCore 2 X := (QuotientGroup.eq_one_iff a).1 h2
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := X)) ⟨a, h3⟩
    have hk' : a ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have hdvd : 3 ∣ 2 ^ k := ha3 ▸ orderOf_dvd_of_pow_eq_one hk'
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
    omega
  · rw [htop, Subgroup.index_top] at hidx
    omega

end XLevelAux

section Fixed

theorem exists_fixed_point_mul_aux_fix {Y : Type} [Group Y] [Finite Y] (hY : Nat.card Y = 8)
    {σ : MulAut Y} (hσ : σ ^ 3 = 1) : ∃ y : Y, y ≠ 1 ∧ σ y = y := by
  classical
  haveI := Fintype.ofFinite Y
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : (MulAut.toPerm Y σ) ^ 3 ^ 1 = 1 := by
    rw [pow_one, ← map_pow, hσ, map_one]
  have hmod := Equiv.Perm.card_compl_support_modEq hp
  by_contra hne
  push Not at hne
  have hsub : (MulAut.toPerm Y σ).supportᶜ ⊆ {1} := by
    intro y hy
    rw [Finset.mem_compl, Equiv.Perm.mem_support, not_not] at hy
    by_contra h1
    exact hne y (by simpa using h1) hy
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_singleton] at hcard
  rw [← Nat.card_eq_fintype_card, hY] at hmod
  unfold Nat.ModEq at hmod
  omega

end Fixed

section Bits

variable {Lg G N : Type} [Group Lg] [Group G] [Group N] [Finite N]

theorem exists_fixed_point_mul_aux_bits (ρ : Lg →* MulAut G) (ρ₁ : Lg →* MulAut N)
    (hN8 : Nat.card N = 8) (hr : Nat.card ρ₁.range = 168)
    (j₁ j₂ : N →* G) (hj₁ : Function.Injective j₁) (hj₂ : Function.Injective j₂)
    (hGc : ∀ x y : G, x * y = y * x)
    (hrange : ∀ g : G, ∃ a b, g = j₁ a * j₂ b) (hinf : ∀ a b, j₁ a = j₂ b → j₁ a = 1)
    (hρ₁ : ∀ l a, j₁ (ρ₁ l a) = ρ l (j₁ a)) (hρ₂ : ∀ l b, j₂ (ρ₁ l b) = ρ l (j₂ b))
    (ε : N →* G) (hε : ∀ l n, ε (ρ₁ l n) = ρ l (ε n)) :
    ∃ s t : Bool, ∀ n, ε n = (if s then j₁ n else 1) * (if t then j₂ n else 1) := by
  classical
  haveI : Nontrivial N := Finite.one_lt_card_iff_nontrivial.1 (by rw [hN8]; norm_num)
  obtain ⟨π₁, π₂, hπ⟩ := IsNatSum.fixed_eq_one_aux_proj hGc j₁ j₂ hj₁ hj₂ hrange hinf
  have hdec : ∀ g, g = j₁ (π₁ g) * j₂ (π₂ g) := by
    intro g
    obtain ⟨a, b, rfl⟩ := hrange g
    rw [(hπ a b).1, (hπ a b).2]
  have hπ₁ : ∀ l g, π₁ (ρ l g) = ρ₁ l (π₁ g) := by
    intro l g
    obtain ⟨a, b, rfl⟩ := hrange g
    rw [map_mul, ← hρ₁, ← hρ₂, (hπ _ _).1, (hπ _ _).1]
  have hπ₂ : ∀ l g, π₂ (ρ l g) = ρ₁ l (π₂ g) := by
    intro l g
    obtain ⟨a, b, rfl⟩ := hrange g
    rw [map_mul, ← hρ₁, ← hρ₂, (hπ _ _).2, (hπ _ _).2]
  have h1 : π₁.comp ε = 1 ∨ π₁.comp ε = MonoidHom.id N :=
    IsNatSum.fixed_eq_one_aux_endo_rho ρ₁ hN8 hr (fun l n => by
      show π₁ (ε (ρ₁ l n)) = ρ₁ l (π₁ (ε n))
      rw [hε, hπ₁])
  have h2 : π₂.comp ε = 1 ∨ π₂.comp ε = MonoidHom.id N :=
    IsNatSum.fixed_eq_one_aux_endo_rho ρ₁ hN8 hr (fun l n => by
      show π₂ (ε (ρ₁ l n)) = ρ₁ l (π₂ (ε n))
      rw [hε, hπ₂])
  have e1 : ∀ n, π₁ (ε n) = (if π₁.comp ε = MonoidHom.id N then n else 1) := by
    intro n
    rcases h1 with h1 | h1
    · have hne : π₁.comp ε ≠ MonoidHom.id N := by
        intro h
        rw [h1] at h
        obtain ⟨a, ha⟩ := exists_ne (1 : N)
        have := congrArg (fun f : N →* N => f a) h
        exact ha (by simpa using this.symm)
      rw [if_neg hne]
      simpa using congrArg (fun f : N →* N => f n) h1
    · rw [if_pos h1]
      simpa using congrArg (fun f : N →* N => f n) h1
  have e2 : ∀ n, π₂ (ε n) = (if π₂.comp ε = MonoidHom.id N then n else 1) := by
    intro n
    rcases h2 with h2 | h2
    · have hne : π₂.comp ε ≠ MonoidHom.id N := by
        intro h
        rw [h2] at h
        obtain ⟨a, ha⟩ := exists_ne (1 : N)
        have := congrArg (fun f : N →* N => f a) h
        exact ha (by simpa using this.symm)
      rw [if_neg hne]
      simpa using congrArg (fun f : N →* N => f n) h2
    · rw [if_pos h2]
      simpa using congrArg (fun f : N →* N => f n) h2
  refine ⟨decide (π₁.comp ε = MonoidHom.id N), decide (π₂.comp ε = MonoidHom.id N), fun n => ?_⟩
  calc ε n = j₁ (π₁ (ε n)) * j₂ (π₂ (ε n)) := hdec _
    _ = _ := by
      rw [e1 n, e2 n]
      by_cases hs : π₁.comp ε = MonoidHom.id N <;> by_cases ht : π₂.comp ε = MonoidHom.id N <;>
        simp [hs, ht]

end Bits

section Core

variable {Lg G N : Type} [Group Lg] [Group G] [Group N] [Finite N]

theorem exists_fixed_point_mul_aux_core (ρ : Lg →* MulAut G) (ρ₁ : Lg →* MulAut N)
    (hN8 : Nat.card N = 8) (hr : Nat.card ρ₁.range = 168)
    (j₁ j₂ : N →* G) (hj₁ : Function.Injective j₁) (hj₂ : Function.Injective j₂)
    (hrange : ∀ g : G, ∃ a b, g = j₁ a * j₂ b) (hinf : ∀ a b, j₁ a = j₂ b → j₁ a = 1)
    (hρ₁ : ∀ l a, j₁ (ρ₁ l a) = ρ l (j₁ a)) (hρ₂ : ∀ l b, j₂ (ρ₁ l b) = ρ l (j₂ b))
    (hGc : ∀ x y : G, x * y = y * x) (hG2 : ∀ x : G, x * x = 1)
    (β : MulAut G) (hβc : ∀ l g, β (ρ l g) = ρ l (β g)) (hβ3 : β ^ 3 = 1)
    (l₀ : Lg) (hl₀3 : ρ₁ l₀ ^ 3 = 1) (hl₀ : ∃ n : N, ρ₁ l₀ n ≠ n) :
    ∃ g : G, g ≠ 1 ∧ ρ l₀ (β g) = g := by
  classical
  haveI : Nontrivial N := Finite.one_lt_card_iff_nontrivial.1 (by rw [hN8]; norm_num)
  have hβ3' : ∀ g, β (β (β g)) = g := fun g => by
    have := congrArg (fun f : MulAut G => f g) hβ3
    simpa [pow_succ, MulAut.mul_apply] using this
  have hσ3 : ∀ n, ρ₁ l₀ (ρ₁ l₀ (ρ₁ l₀ n)) = n := fun n => by
    have := congrArg (fun f : MulAut N => f n) hl₀3
    simpa [pow_succ, MulAut.mul_apply] using this
  by_cases hI : ∀ n, β (j₁ n) = j₁ n
  · obtain ⟨n₁, hn₁, hfix⟩ := exists_fixed_point_mul_aux_fix hN8 hl₀3
    refine ⟨j₁ n₁, fun h => hn₁ (hj₁ (by rw [h, map_one])), ?_⟩
    rw [hI, ← hρ₁, hfix]
  push Not at hI
  obtain ⟨n₀, hn₀⟩ := hI
  have hn₀1 : n₀ ≠ 1 := by
    rintro rfl
    exact hn₀ (by rw [map_one, map_one])
  have hx1 : j₁ n₀ ≠ 1 := fun h => hn₀1 (hj₁ (by rw [h, map_one]))
  have hy1 : j₂ n₀ ≠ 1 := fun h => hn₀1 (hj₂ (by rw [h, map_one]))
  have hxy : j₁ n₀ ≠ j₂ n₀ := fun h => hx1 (hinf _ _ h)
  have hb₁ : ∀ l n, (β.toMonoidHom.comp j₁) (ρ₁ l n) = ρ l ((β.toMonoidHom.comp j₁) n) :=
    fun l n => by
      show β (j₁ (ρ₁ l n)) = ρ l (β (j₁ n))
      rw [hρ₁, hβc]
  have hb₂ : ∀ l n, (β.toMonoidHom.comp j₂) (ρ₁ l n) = ρ l ((β.toMonoidHom.comp j₂) n) :=
    fun l n => by
      show β (j₂ (ρ₁ l n)) = ρ l (β (j₂ n))
      rw [hρ₂, hβc]
  obtain ⟨s₁, t₁, h₁⟩ := exists_fixed_point_mul_aux_bits ρ ρ₁ hN8 hr j₁ j₂ hj₁ hj₂ hGc hrange hinf
    hρ₁ hρ₂ _ hb₁
  obtain ⟨s₂, t₂, h₂⟩ := exists_fixed_point_mul_aux_bits ρ ρ₁ hN8 hr j₁ j₂ hj₁ hj₂ hGc hrange hinf
    hρ₁ hρ₂ _ hb₂
  have h₁' : ∀ n, β (j₁ n) = (if s₁ then j₁ n else 1) * (if t₁ then j₂ n else 1) := h₁
  have h₂' : ∀ n, β (j₂ n) = (if s₂ then j₁ n else 1) * (if t₂ then j₂ n else 1) := h₂
  clear h₁ h₂
  obtain ⟨x₀, hx₀⟩ := hl₀
  set w : N := x₀⁻¹ * ρ₁ l₀ x₀ with hw
  have hw1 : w ≠ 1 := by
    intro h
    apply hx₀
    have : ρ₁ l₀ x₀ = x₀ * w := by rw [hw]; group
    rw [this, h, mul_one]
  have hnorm : w * ρ₁ l₀ w * ρ₁ l₀ (ρ₁ l₀ w) = 1 := by
    have e1 : ρ₁ l₀ w = (ρ₁ l₀ x₀)⁻¹ * ρ₁ l₀ (ρ₁ l₀ x₀) := by rw [hw, map_mul, map_inv]
    have e2 : ρ₁ l₀ (ρ₁ l₀ w) = (ρ₁ l₀ (ρ₁ l₀ x₀))⁻¹ * x₀ := by
      rw [e1, map_mul, map_inv, hσ3]
    rw [e2, e1, hw]
    group
  clear_value w
  obtain ⟨w₁, hw₁⟩ : ∃ w₁, w₁ = ρ₁ l₀ w := ⟨_, rfl⟩
  obtain ⟨w₂, hw₂⟩ : ∃ w₂, w₂ = ρ₁ l₀ w₁ := ⟨_, rfl⟩
  have hw₃ : ρ₁ l₀ w₂ = w := by rw [hw₂, hw₁]; exact hσ3 w
  rw [← hw₁, ← hw₂] at hnorm
  have hρ₁' : ∀ n, ρ l₀ (j₁ n) = j₁ (ρ₁ l₀ n) := fun n => (hρ₁ l₀ n).symm
  have hρ₂' : ∀ n, ρ l₀ (j₂ n) = j₂ (ρ₁ l₀ n) := fun n => (hρ₂ l₀ n).symm
  have hN3 : ∀ j : N →* G, j w * j w₁ = j w₂ := by
    intro j
    have h := congrArg j hnorm
    rw [map_mul, map_mul, map_one] at h
    have := eq_inv_of_mul_eq_one_left h
    rw [this]
    exact inv_eq_of_mul_eq_one_right (hG2 _)
  have hN3' : ∀ j : N →* G, j w₁ * j w₂ = j w := by
    intro j
    have h := congrArg j hnorm
    rw [map_mul, map_mul, map_one, mul_assoc] at h
    have := eq_inv_of_mul_eq_one_right h
    rw [this]
    exact inv_eq_of_mul_eq_one_right (hG2 _)
  have hne : ∀ s : N, j₂ w * j₁ s ≠ 1 := by
    intro s h
    have e : j₂ w = j₁ s := by
      calc j₂ w = j₂ w * (j₁ s * j₁ s) := by rw [hG2, mul_one]
        _ = (j₂ w * j₁ s) * j₁ s := by rw [mul_assoc]
        _ = j₁ s := by rw [h, one_mul]
    have hs1 : j₁ s = 1 := hinf s w e.symm
    rw [hs1] at e
    exact hw1 (hj₂ (by rw [e, map_one]))
  cases s₁ <;> cases t₁ <;> cases s₂ <;> cases t₂ <;>
    simp only [Bool.false_eq_true, if_false, if_true, mul_one, one_mul] at h₁' h₂'
  · exact absurd (β.map_eq_one_iff.1 (h₁' n₀)) hx1
  · exact absurd (β.map_eq_one_iff.1 (h₁' n₀)) hx1
  · exact absurd (β.map_eq_one_iff.1 (h₁' n₀)) hx1
  · exact absurd (β.map_eq_one_iff.1 (h₁' n₀)) hx1
  · exact absurd (β.map_eq_one_iff.1 (h₂' n₀)) hy1
  · exact absurd (β.injective ((h₁' n₀).trans (h₂' n₀).symm)) hxy
  · exact absurd (calc j₁ n₀ = β (β (β (j₁ n₀))) := (hβ3' _).symm
      _ = j₂ n₀ := by rw [h₁' n₀, h₂' n₀, h₁' n₀]) hxy
  ·
    refine ⟨j₂ w * j₁ w₁, hne _, ?_⟩
    calc ρ l₀ (β (j₂ w * j₁ w₁)) = ρ l₀ (β (j₂ w) * β (j₁ w₁)) := by rw [map_mul]
      _ = ρ l₀ ((j₁ w * j₂ w) * j₂ w₁) := by rw [h₂', h₁']
      _ = (j₁ w₁ * j₂ w₁) * j₂ w₂ := by
        rw [map_mul, map_mul, hρ₁', hρ₂', hρ₂', ← hw₁, ← hw₂]
      _ = j₁ w₁ * (j₂ w₁ * j₂ w₂) := by rw [mul_assoc]
      _ = j₁ w₁ * j₂ w := by rw [hN3' j₂]
      _ = j₂ w * j₁ w₁ := hGc _ _
  · exact absurd (h₁' n₀) hn₀
  · exact absurd (h₁' n₀) hn₀
  · exact absurd (h₁' n₀) hn₀
  · exact absurd (h₁' n₀) hn₀
  · exact absurd (β.map_eq_one_iff.1 (h₂' n₀)) hy1
  · have e : β (β (j₁ n₀)) = j₁ n₀ := by
      rw [h₁' n₀, map_mul, h₁' n₀, h₂' n₀, mul_assoc, hG2, mul_one]
    have h3 : β (β (β (j₁ n₀))) = β (j₁ n₀) := by rw [e]
    exact absurd (h3.symm.trans (hβ3' _)) hn₀
  ·
    refine ⟨j₂ w * j₁ w₂, hne _, ?_⟩
    calc ρ l₀ (β (j₂ w * j₁ w₂)) = ρ l₀ (β (j₂ w) * β (j₁ w₂)) := by rw [map_mul]
      _ = ρ l₀ (j₁ w * (j₁ w₂ * j₂ w₂)) := by rw [h₂', h₁']
      _ = j₁ w₁ * (j₁ w * j₂ w) := by
        rw [map_mul, map_mul, hρ₁', hρ₁', hρ₂', ← hw₁, hw₃]
      _ = (j₁ w₁ * j₁ w) * j₂ w := by rw [mul_assoc]
      _ = j₁ w₂ * j₂ w := by rw [hGc (j₁ w₁) (j₁ w), hN3 j₁]
      _ = j₂ w * j₁ w₂ := hGc _ _
  · exact absurd (β.injective ((h₁' n₀).trans (h₂' n₀).symm)) hxy

end Core

section Main

variable {X : Type} [Group X] [Finite X]

theorem exists_fixed_point_mul {T : Subgroup X} (hX : GNSetting X T) {Ls : Subgroup (X ⧸ gnC T)}
    {L : Subgroup X} (hLs : IsComponentOf Ls ⊤) (hL : LiftOf T L Ls) (hN : IsNatSum L ⁅L, gnV T⁆)
    {a b : X} (ha : a ∈ L) (ha3 : orderOf a = 3) (hb : b ∈ cMHat L) (hb3 : orderOf b = 3)
    (hab : a * b = b * a) :
    ∃ u ∈ (⁅L, gnV T⁆ : Subgroup X), u ≠ 1 ∧ (a * b) * u = u * (a * b) := by
  classical
  haveI hVn : (gnV T).Normal := Subgroup.normalClosure_normal
  have hUV : ⁅L, gnV T⁆ ≤ gnV T := Subgroup.commutator_le_right L (gnV T)
  have hVea := CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.isElemAbelian_gnV T hX
  have hUc := comm_of_le_gnV hX hUV
  have hU2 : ∀ x ∈ (⁅L, gnV T⁆ : Subgroup X), x * x = 1 := fun x hx => by
    have := hVea.2 x (hUV hx)
    rwa [sq] at this
  have hn : L ≤ Subgroup.normalizer ((⁅L, gnV T⁆ : Subgroup X) : Set X) :=
    IsNatSum.fixed_eq_one_aux_le_normalizer hN
  have hx' : (QuotientGroup.mk' (CFSG.pCore 2 X) b : X ⧸ CFSG.pCore 2 X) ∈
      Subgroup.centralizer (barO2 L : Set (X ⧸ CFSG.pCore 2 X)) := hb
  have hstar : toStar T b ∈ Subgroup.centralizer (Ls : Set (X ⧸ gnC T)) := by
    rw [Subgroup.mem_centralizer_iff, ← hL.2]
    rintro _ ⟨l, hl, rfl⟩
    have hbl : QuotientGroup.mk' (CFSG.pCore 2 X) l ∈ barO2 L := Subgroup.mem_map_of_mem _ hl
    have hcomm := Subgroup.mem_centralizer_iff.1 hx' _ hbl
    have hmk : QuotientGroup.mk' (CFSG.pCore 2 X) (l * b) =
        QuotientGroup.mk' (CFSG.pCore 2 X) (b * l) := by
      rw [map_mul, map_mul]
      exact hcomm
    have hpc : (l * b)⁻¹ * (b * l) ∈ CFSG.pCore 2 X := QuotientGroup.eq.1 hmk
    have hgn : (l * b)⁻¹ * (b * l) ∈ gnC T := pCore_le_gnC hX hpc
    have hc : toStar T (l * b) = toStar T (b * l) := QuotientGroup.eq.2 hgn
    simpa only [map_mul] using hc
  have hbN : b ∈ Subgroup.normalizer ((⁅L, gnV T⁆ : Subgroup X) : Set X) :=
    mem_normalizer_commutator (liftOf_conj hX hLs hL b
      (Subgroup.centralizer_le_normalizer _ hstar))
  have hbc := commute_action_of_mem_cMLStar hL.2 hstar hUV
  have ha1 : a ^ 3 = 1 := by
    have := pow_orderOf_eq_one a
    rwa [ha3] at this
  have hb1 : b ^ 3 = 1 := by
    have := pow_orderOf_eq_one b
    rwa [hb3] at this
  have hab3 : (a * b) ^ 3 = 1 := by
    rw [Commute.mul_pow (show Commute a b from hab), ha1, hb1, one_mul]
  have habN : a * b ∈ Subgroup.normalizer ((⁅L, gnV T⁆ : Subgroup X) : Set X) :=
    Subgroup.mul_mem _ (hn ha) hbN
  generalize hU : (⁅L, gnV T⁆ : Subgroup X) = U at hN hUV hUc hU2 hn hbN hbc habN ⊢
  have hfin : ∀ g : X, (a * b) * g * (a * b)⁻¹ = g → (a * b) * g = g * (a * b) := fun g h => by
    calc (a * b) * g = (a * b) * g * (a * b)⁻¹ * (a * b) := by group
      _ = g * (a * b) := by rw [h]
  obtain ⟨N₁, N₂, hN₁, hsup, h2⟩ := hN
  have hN₁U : N₁ ≤ U := hsup ▸ le_sup_left
  have hn₁ : L ≤ Subgroup.normalizer (N₁ : Set X) := hN₁.2.2.1
  rcases h2 with rfl | ⟨hN₂, hsup_inf, f, hf⟩
  · have hUeq : N₁ = U := by rw [← hsup, sup_bot_eq]
    subst hUeq
    have h8 : Nat.card ↥N₁ = 8 := IsNatSum.card_centralizer_dvd_six_aux_card hN₁
    let c : MulAut ↥N₁ := Subgroup.normalizerMonoidHom N₁ ⟨a * b, habN⟩
    have hc3 : c ^ 3 = 1 := by
      rw [← map_pow]
      have : (⟨a * b, habN⟩ : Subgroup.normalizer (N₁ : Set X)) ^ 3 = 1 :=
        Subtype.ext (by simpa using hab3)
      rw [this, map_one]
    obtain ⟨y, hy1, hyfix⟩ := exists_fixed_point_mul_aux_fix h8 hc3
    refine ⟨y, y.2, fun h => hy1 (Subtype.ext h), hfin _ ?_⟩
    exact congrArg Subtype.val hyfix
  · have hN₂U : N₂ ≤ U := hsup ▸ le_sup_right
    have hn₂ : L ≤ Subgroup.normalizer (N₂ : Set X) := hN₂.2.2.1
    have hN8 : Nat.card ↥N₁ = 8 := IsNatSum.card_centralizer_dvd_six_aux_card hN₁
    have hr : Nat.card (actOn L N₁ hn₁).range = 168 :=
      IsNatSum.card_centralizer_dvd_six_aux_range hN₁
    have hC : CFSG.pCore 2 X ≤ Subgroup.centralizer (N₁ : Set X) :=
      (pCore_le_gnC hX).trans (Subgroup.centralizer_le
        (SetLike.coe_subset_coe.2 (hN₁U.trans (hU ▸ hUV))))
    obtain ⟨n, hnN, hne⟩ :=
      exists_fixed_point_mul_aux_not_centralizes hL.1 hN₁ hC ha ha3
    let j₁ : ↥N₁ →* ↥U := Subgroup.inclusion hN₁U
    let j₂ : ↥N₁ →* ↥U := (Subgroup.inclusion hN₂U).comp f.toMonoidHom
    let β : MulAut ↥U := Subgroup.normalizerMonoidHom U ⟨b, hbN⟩
    have key := exists_fixed_point_mul_aux_core (Lg := ↥L) (G := ↥U) (N := ↥N₁)
      (actOn L U hn) (actOn L N₁ hn₁) hN8 hr j₁ j₂ (Subgroup.inclusion_injective hN₁U)
      ((Subgroup.inclusion_injective hN₂U).comp f.injective) ?_ ?_ ?_ ?_
      (fun x y => Subtype.ext (hUc x x.2 y y.2))
      (fun x => Subtype.ext (hU2 x x.2)) β ?_ ?_ ⟨a, ha⟩ ?_
      ⟨⟨n, hnN⟩, fun h => hne (congrArg Subtype.val h)⟩
    · obtain ⟨g, hg1, hgfix⟩ := key
      refine ⟨(g : X), g.2, fun h => hg1 (Subtype.ext h), hfin _ ?_⟩
      have h1 : a * (b * (g : X) * b⁻¹) * a⁻¹ = g := congrArg Subtype.val hgfix
      calc (a * b) * (g : X) * (a * b)⁻¹ = a * (b * (g : X) * b⁻¹) * a⁻¹ := by group
        _ = g := h1
    ·
      intro g
      have hg : (g : X) ∈ N₁ ⊔ N₂ := hsup ▸ g.2
      obtain ⟨y, hy, z, hz, hyz⟩ := IsNatSum.card_centralizer_dvd_six_aux_mem_sup
        (fun a ha b hb => hUc a (hN₁U ha) b (hN₂U hb)) hg
      refine ⟨⟨y, hy⟩, f.symm ⟨z, hz⟩, Subtype.ext ?_⟩
      show (g : X) = y * (f (f.symm ⟨z, hz⟩) : X)
      rw [MulEquiv.apply_symm_apply]
      exact hyz.symm
    · intro a' b' h
      have h1 : (Subgroup.inclusion hN₁U a' : X) ∈ N₁ ⊓ N₂ := by
        refine ⟨a'.2, ?_⟩
        have : (Subgroup.inclusion hN₁U a' : X) = (f b' : X) := congrArg Subtype.val h
        rw [this]
        exact (f b').2
      rw [hsup_inf] at h1
      exact Subtype.ext (Subgroup.mem_bot.1 h1)
    · exact fun l a' => Subtype.ext rfl
    · exact fun l b' => Subtype.ext (hf l l.2 b' (actOn L N₁ hn₁ l b') rfl)
    · exact fun l g' => Subtype.ext (hbc l l.2 g' g'.2)
    · rw [← map_pow]
      have : (⟨b, hbN⟩ : Subgroup.normalizer (U : Set X)) ^ 3 = 1 :=
        Subtype.ext (by simpa using hb1)
      rw [this, map_one]
    · rw [← map_pow]
      have : (⟨a, ha⟩ : ↥L) ^ 3 = 1 := Subtype.ext (by simpa using ha1)
      rw [this, map_one]

end Main

end CFSG.LocalAnalysis.RankThreeUC.S15
