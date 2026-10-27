module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142NLift

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I142N

open CFSG.Open
open scoped commutatorElement

@[expose] def fixA {A G : Type*} [Group A] [Group G] (ρ : A →* MulAut G) : Subgroup G where
  carrier := {x | ∀ a : A, ρ a x = x}
  one_mem' := fun a => by simp
  mul_mem' := fun {x y} hx hy a => by simp [map_mul, hx a, hy a]
  inv_mem' := fun {x} hx a => by simp [map_inv, hx a]

theorem mem_fixA {A G : Type*} [Group A] [Group G] {ρ : A →* MulAut G} {x : G} :
    x ∈ fixA ρ ↔ ∀ a : A, ρ a x = x := Iff.rfl

section Defect

variable {A G H : Type*} [Group A] [Group G] [Group H]

theorem fixed_comm_of_defect {π : G →* H} (hk : ∀ g : G, π g = 1 → g ∈ Subgroup.center G)
    {ρ : A →* MulAut G} {x x' : G} (hx : ∀ a : A, π (ρ a x) = π x)
    (hx' : ∀ a : A, π (ρ a x') = π x') : ∀ a : A, ρ a ⁅x, x'⁆ = ⁅x, x'⁆ := by
  intro a
  have hk1 : x⁻¹ * ρ a x ∈ Subgroup.center G := hk _ (by rw [map_mul, map_inv, hx a]; simp)
  have hk2 : x'⁻¹ * ρ a x' ∈ Subgroup.center G := hk _ (by rw [map_mul, map_inv, hx' a]; simp)
  have e1 : ρ a x = x * (x⁻¹ * ρ a x) := by group
  have e2 : ρ a x' = x' * (x'⁻¹ * ρ a x') := by group
  rw [map_commutatorElement, e1, e2, comm_mul_central_left hk1, comm_mul_central_right hk2]

theorem mem_fixA_map_iff {π : G →* H} {ρ : A →* MulAut G} {σ : A →* MulAut H}
    (hc : ∀ (a : A) (x : G), π (ρ a x) = σ a (π x)) {y : H} (hy : y ∈ π.range) :
    y ∈ fixA σ ↔ ∃ x : G, π x = y ∧ ∀ a : A, π (ρ a x) = π x := by
  constructor
  · intro hfix
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hy
    refine ⟨x, rfl, fun a => ?_⟩
    rw [hc]
    exact mem_fixA.1 hfix a
  · rintro ⟨x, rfl, hx⟩
    rw [mem_fixA]
    intro a
    rw [← hc]
    exact hx a

theorem commutator_fixA_le_map {π : G →* H} (hk : ∀ g : G, π g = 1 → g ∈ Subgroup.center G)
    {ρ : A →* MulAut G} {σ : A →* MulAut H} (hc : ∀ (a : A) (x : G), π (ρ a x) = σ a (π x)) :
    ⁅fixA σ ⊓ π.range, fixA σ ⊓ π.range⁆ ≤ (fixA ρ).map π := by
  rw [Subgroup.commutator_le]
  intro v hv w hw
  obtain ⟨hv1, hv2⟩ := Subgroup.mem_inf.1 hv
  obtain ⟨hw1, hw2⟩ := Subgroup.mem_inf.1 hw
  obtain ⟨x, rfl, hx⟩ := (mem_fixA_map_iff hc hv2).1 hv1
  obtain ⟨x', rfl, hx'⟩ := (mem_fixA_map_iff hc hw2).1 hw1
  refine Subgroup.mem_map.2 ⟨⁅x, x'⁆, ?_, ?_⟩
  · rw [mem_fixA]
    exact fixed_comm_of_defect hk hx hx'
  · rw [map_commutatorElement]

theorem exists_perfect_core_map [Finite G] (π : G →* H) (n : ℕ) :
    ∀ M : Subgroup G, Nat.card M = n → ⁅M.map π, M.map π⁆ = M.map π →
      ∃ N ≤ M, ⁅N, N⁆ = N ∧ N.map π = M.map π := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro M hMn hperf
    by_cases hM : ⁅M, M⁆ = M
    · exact ⟨M, le_rfl, hM, rfl⟩
    · have hle : ⁅M, M⁆ ≤ M :=
        Subgroup.commutator_le.2 (fun a ha b hb => commutatorElement_mem_of ha hb)
      have hlt : ⁅M, M⁆ < M := lt_of_le_of_ne hle hM
      have hcard : Nat.card (⁅M, M⁆ : Subgroup G) < n := by
        rw [← hMn]
        exact Subgroup.card_lt_of_lt hlt
      have hmapc : Subgroup.map π ⁅M, M⁆ = M.map π := by
        rw [Subgroup.map_commutator]
        exact hperf
      obtain ⟨N, hNM, hN, hNmap⟩ := ih _ hcard (⁅M, M⁆ : Subgroup G) rfl (by rw [hmapc]; exact hperf)
      exact ⟨N, hNM.trans hle, hN, hNmap.trans hmapc⟩

theorem exists_perfect_lift [Finite G] {π : G →* H} {ρ : A →* MulAut G} {σ : A →* MulAut H}
    (hc : ∀ (a : A) (x : G), π (ρ a x) = σ a (π x))
    (hk : ∀ g : G, π g = 1 → g ∈ Subgroup.center G)
    {P : Subgroup H} (hP : P ≤ fixA σ ⊓ π.range) (hPp : ⁅P, P⁆ = P) :
    ∃ Q : Subgroup G, Q ≤ fixA ρ ∧ ⁅Q, Q⁆ = Q ∧ Q.map π = P := by
  have hPr : P ≤ π.range := fun y hy => (Subgroup.mem_inf.1 (hP hy)).2
  set M : Subgroup G := P.comap π with hMdef
  have hMP : M.map π = P := Subgroup.map_comap_eq_self hPr
  have hMfix : ∀ m ∈ M, ∀ a : A, π (ρ a m) = π m := by
    intro m hm a
    have hpm : π m ∈ P := Subgroup.mem_comap.1 hm
    have hfix : π m ∈ fixA σ := (Subgroup.mem_inf.1 (hP hpm)).1
    rw [hc]
    exact mem_fixA.1 hfix a
  have hMle : ⁅M, M⁆ ≤ fixA ρ := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [mem_fixA]
    exact fixed_comm_of_defect hk (hMfix x hx) (hMfix y hy)
  have hperf : ⁅M.map π, M.map π⁆ = M.map π := by
    rw [hMP]
    exact hPp
  obtain ⟨N, hNM, hN, hNmap⟩ := exists_perfect_core_map π _ M rfl hperf
  refine ⟨N, ?_, hN, by rw [hNmap, hMP]⟩
  intro n hn
  have h1 : ⁅N, N⁆ ≤ ⁅M, M⁆ := Subgroup.commutator_mono hNM hNM
  rw [hN] at h1
  exact hMle (h1 hn)

end Defect

section Quotient

variable {A L : Type*} [Group A] [Group L]

theorem sigma_of_quasisimple_mod_center (hL : IsQuasisimple L) (ρ : A →* MulAut L)
    (σ : A →* MulAut (L ⧸ Subgroup.center L))
    (hc : ∀ (a : A) (x : L), QuotientGroup.mk' (Subgroup.center L) (ρ a x) =
      σ a (QuotientGroup.mk' (Subgroup.center L) x))
    (hSig : ∀ P : Subgroup (L ⧸ Subgroup.center L), P ≤ fixA σ → ⁅P, P⁆ = P →
      P ≤ GLALayer (fixA σ)) :
    ∀ P : Subgroup L, P ≤ fixA ρ → ⁅P, P⁆ = P → P ≤ GLALayer (fixA ρ) := by
  intro P hP hPp
  set π : L →* L ⧸ Subgroup.center L := QuotientGroup.mk' (Subgroup.center L) with hπdef
  have hk : ∀ g : L, π g = 1 → g ∈ Subgroup.center L :=
    fun g hg => (QuotientGroup.eq_one_iff g).1 hg
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hrange : π.range = ⊤ := MonoidHom.range_eq_top.2 hπs
  have hPfix : P.map π ≤ fixA σ := by
    rintro _ ⟨p, hp, rfl⟩
    rw [mem_fixA]
    intro a
    have hpfix : ρ a p = p := mem_fixA.1 (hP hp) a
    rw [← hc a p, hpfix]
  have hPperf : ⁅P.map π, P.map π⁆ = P.map π := by
    have h := Subgroup.map_commutator P P π
    rw [hPp] at h
    exact h.symm
  have hPL1 : P.map π ≤ GLALayer (fixA σ) := hSig _ hPfix hPperf
  have hb := commutator_fixA_le_map hk hc
  rw [hrange, inf_top_eq] at hb
  have hfixle : (fixA ρ).map π ≤ fixA σ := by
    rintro _ ⟨w, hw, rfl⟩
    rw [mem_fixA]
    intro a
    have hwfix : ρ a w = w := mem_fixA.1 hw a
    rw [← hc a w, hwfix]
  have hL2 : GLALayer (fixA σ) ≤ GLALayer ((fixA ρ).map π) := by
    refine GLALayer_le_of fun K hK => ?_
    have hKperf : ⁅K, K⁆ = K := comm_self_eq_of_commutator_top hK.2.2.1
    have hKle : K ≤ (fixA ρ).map π := by
      have h1 : ⁅K, K⁆ ≤ ⁅fixA σ, fixA σ⁆ := Subgroup.commutator_mono hK.1 hK.1
      rw [hKperf] at h1
      exact h1.trans hb
    exact le_GLALayer (isComponentOf_of_le hK hKle hfixle)
  have hPL : P.map π ≤ GLALayer ((fixA ρ).map π) := hPL1.trans hL2
  exact le_GLALayer_of_map_le π hk hPp hPL

end Quotient

end CFSG.LocalAnalysis.GLTheoremA.I142N
