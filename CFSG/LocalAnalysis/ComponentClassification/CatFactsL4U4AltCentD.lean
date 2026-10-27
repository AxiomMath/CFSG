module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4AltCentB

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace AltCent

open CFSG Subgroup Equiv Equiv.Perm

theorem comm_swap_of_fix {m : ℕ} {i j : Fin m} {x : Perm (Fin m)} (hi : x i = i) (hj : x j = j) :
    x * swap i j = swap i j * x := by
  rw [mul_swap_eq_swap_mul, hi, hj]

theorem false_of_swap {G : Type} [Group G] [Finite G] {N : Subgroup G} [N.Normal] {n : ℕ}
    (hn : n = 5 ∨ n = 6 ∨ n = 7) (eN : ↥N ≃* alternatingGroup (Fin (n + 4))) (hm5 : 5 ≤ n + 4)
    (hm6 : n + 4 ≠ 6) (hC : centralizer (N : Set G) = ⊥) {α : G} {J : Subgroup G}
    (hJα : J ≤ centralizer ({α} : Set G))
    (hJc : IsComponent (J.subgroupOf (centralizer ({α} : Set G))))
    (eJ : ↥J ⧸ center ↥J ≃* alternatingGroup (Fin n)) {i j : Fin (n + 4)} (hij : i ≠ j)
    (hπ : toPerm eN hm5 hm6 α = swap i j) : False := by
  set ψ := toPerm eN hm5 hm6 with hψ
  have hψinj := toPerm_injective eN hm5 hm6 hC
  set C := centralizer ({α} : Set G) with hCdef
  set A' : Subgroup (Perm (Fin (n + 4))) := altOff {i, j} with hA'
  have hJq : IsQuasisimple ↥J :=
    (LocalAnalysis.ComponentInitial.isQuasisimple_congr (subgroupOfEquivOfLe hJα)).mp hJc.1
  have hJp : ⁅J, J⁆ = J := Subgroup.isPerfect_iff.mp hJq.1
  set X := J.map ψ with hX
  have hXp : ⁅X, X⁆ = X := by rw [hX, ← map_commutator, hJp]
  have hcommα : ∀ {y : G}, y ∈ C → ψ y * swap i j = swap i j * ψ y := by
    intro y hy
    rw [← hπ, ← map_mul, ← map_mul, (mem_centralizer_singleton_iff.mp hy)]
  have hXπ : ∀ x ∈ X, x * swap i j = swap i j * x := by
    rintro _ ⟨y, hy, rfl⟩
    exact hcommα (hJα hy)
  have hXfix := fixes_support_of_perfect hXp hXπ
    (by rw [support_swap hij, Finset.card_pair hij]; norm_num)
  have hXA' : X ≤ A' := fun x hx => mem_altOff
    (fun a ha => hXfix x hx a (by rwa [support_swap hij]))
    (le_alternatingGroup_of_perfect hXp hx)
  set A₀ : Subgroup G := A'.comap ψ ⊓ C with hA₀
  have hJA₀ : J ≤ A₀ := fun x hx => ⟨hXA' ⟨x, hx, rfl⟩, hJα hx⟩
  have hA₀C : A₀ ≤ C := inf_le_right
  have hA'le : A' ≤ A₀.map ψ := by
    intro y hy
    obtain ⟨n₀, -, hn₀⟩ := exists_of_mem_alt eN hm5 hm6
      (show y ∈ alternatingGroup (Fin (n + 4)) from sign_of_mem_altOff hy)
    refine ⟨n₀, mem_inf.mpr ⟨?_, ?_⟩, hn₀⟩
    · show ψ n₀ ∈ A'
      rw [hn₀]
      exact hy
    rw [mem_centralizer_singleton_iff]
    apply hψinj
    rw [map_mul, map_mul, hπ, hn₀]
    exact comm_swap_of_fix (apply_eq_of_mem_altOff hy (a := i) (by simp))
      (apply_eq_of_mem_altOff hy (a := j) (by simp))
  have hA₀map : A₀.map ψ = A' := le_antisymm (map_le_iff_le_comap.mpr inf_le_left) hA'le
  have hA₀simple : IsSimpleGroup ↥A₀ := by
    have : IsSimpleGroup ↥A' := isSimpleGroup_altOff {i, j} (by rw [Finset.card_pair hij]; omega)
    exact (MulEquiv.isSimpleGroup_congr ((equivMapOfInjective A₀ ψ hψinj).trans
      (MulEquiv.subgroupCongr hA₀map))).mpr this
  have hA₀n : (A₀.subgroupOf C).Normal := by
    constructor
    intro a ha c
    rw [mem_subgroupOf] at ha ⊢
    refine ⟨?_, (c * a * c⁻¹).2⟩
    show ψ ((c : G) * a * (c : G)⁻¹) ∈ A'
    rw [map_mul, map_mul, map_inv]
    exact conj_mem_altOff (mem_pair_iff_of_comm hij (hcommα c.2).symm) ha.1
  have hs : ((J.subgroupOf C).subgroupOf (A₀.subgroupOf C)).IsSubnormal := hJc.2.subgroupOf
  have hsimp : IsSimpleGroup ↥(A₀.subgroupOf C) :=
    (MulEquiv.isSimpleGroup_congr (subgroupOfEquivOfLe hA₀C)).mpr hA₀simple
  have hJdvd := card_dvd_of_quot (by omega) eJ
  rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hsimp hs with hb | ht
  ·
    have hJb : J = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hmem : (⟨⟨x, hJα hx⟩, by rw [mem_subgroupOf]; exact hJA₀ hx⟩ : ↥(A₀.subgroupOf C)) ∈
          (J.subgroupOf C).subgroupOf (A₀.subgroupOf C) := by
        rw [mem_subgroupOf, mem_subgroupOf]
        exact hx
      rw [hb, mem_bot] at hmem
      exact mem_bot.mpr (congrArg (fun z : ↥(A₀.subgroupOf C) => ((z : ↥C) : G)) hmem)
    rw [hJb, Subgroup.card_bot] at hJdvd
    have h1 := Nat.le_of_dvd one_pos hJdvd
    rcases hn with rfl | rfl | rfl <;> revert h1 <;> decide
  ·
    have hA₀J : A₀ ≤ J := by
      intro a ha
      have hmem : (⟨⟨a, hA₀C ha⟩, by rw [mem_subgroupOf]; exact ha⟩ : ↥(A₀.subgroupOf C)) ∈
          (J.subgroupOf C).subgroupOf (A₀.subgroupOf C) := by
        rw [ht]
        exact mem_top _
      rw [mem_subgroupOf, mem_subgroupOf] at hmem
      exact hmem
    have hJeq : J = A₀ := le_antisymm hJA₀ hA₀J
    have hJsimple : IsSimpleGroup ↥J :=
      (MulEquiv.isSimpleGroup_congr (MulEquiv.subgroupCongr hJeq)).mpr hA₀simple
    have hZ : center ↥J = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center ↥J) with h | h
      · exact h
      · exfalso
        obtain ⟨-, -, a, b, hab⟩ := hJq
        apply hab
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
        obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
          mem_center_iff.mp (h ▸ mem_top x : x ∈ center ↥J) y]
    have h1 : Nat.card (↥J ⧸ center ↥J) = n.factorial / 2 := by
      have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
      rw [Nat.card_congr eJ.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
        Fintype.card_fin]
    have h2 : Nat.card (↥J ⧸ center ↥J) = Nat.card ↥J :=
      Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hZ).trans
        QuotientGroup.quotientBot).toEquiv
    have h3 : Nat.card ↥J = (n + 2).factorial / 2 := by
      rw [Nat.card_congr (MulEquiv.subgroupCongr hJeq).toEquiv,
        ← card_map_of_injective hψinj, hA₀map, card_altOff _ (by rw [Finset.card_pair hij]; omega),
        Finset.card_pair hij, show n + 4 - 2 = n + 2 by omega]
    have h4 : n.factorial / 2 = (n + 2).factorial / 2 := by rw [← h1, h2, h3]
    rcases hn with rfl | rfl | rfl <;> revert h4 <;> decide

end AltCent

end CFSG.ComponentClassification.CatFactsL4U4
