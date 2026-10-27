module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S14Core
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S13
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S14Lift

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup

theorem X_cube_aux {G : Type} [Group G] [Finite G] (L₁ : Subgroup G) (π : ↥L₁ →* A6)
    (hker : π.ker = center ↥L₁) (hc2 : Nat.card (center ↥L₁) = 2) (x : G) (hxL : x ∈ L₁)
    (hx : orderOf x = 3) (X : Subgroup G) (hXle : X ≤ L₁ ⊓ centralizer ({x} : Set G))
    (hX9 : Nat.card X = 9) : ∀ a ∈ X, a ^ 3 = 1 := by
  intro a ha
  let a' : ↥L₁ := ⟨a, (hXle ha).1⟩
  let x' : ↥L₁ := ⟨x, hxL⟩
  have hxo : orderOf x' = 3 := by rw [Subgroup.orderOf_mk]; exact hx
  have hπx := cover_orderOf hker hc2 hxo
  have hcomm : a' * x' = x' * a' := Subtype.ext (mem_centralizer_singleton_iff.1 (hXle ha).2)
  have hπa : π a' ∈ centralizer ({π x'} : Set A6) := by
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hcomm]
  have h3 : (π a') ^ 3 = 1 := pow_three_of_mem_centralizer hπx _ hπa
  have hk : a' ^ 3 ∈ center ↥L₁ := by
    rw [← hker, MonoidHom.mem_ker, map_pow]
    exact h3
  have h9 : a' ^ 9 = 1 := by
    have : (⟨a, ha⟩ : ↥X) ^ Nat.card ↥X = 1 := pow_card_eq_one'
    rw [hX9] at this
    have h9G : a ^ 9 = 1 := by simpa using congrArg Subtype.val this
    exact Subtype.ext (by simpa [a'] using h9G)
  have hk3 : (a' ^ 3) ^ 3 = 1 := by rw [← pow_mul]; exact h9
  have hk2 := cover_sq hker hc2 hk
  have hkk : a' ^ 3 = 1 := by
    have : (a' ^ 3) ^ 3 = a' ^ 3 := by rw [pow_succ, pow_two, hk2, one_mul]
    rw [← this]; exact hk3
  exact congrArg Subtype.val hkk

theorem s14_of_full (hON : ONan77S5) (hNo : ONanNoSL29Y) (h13 : StepS13Full) : StepS14 := by
  intro G _ _ L t E W z hb a
  by_cases hZ : center ↥a.L₁ = ⊥
  · obtain ⟨q⟩ := a.L₁_A6
    have e1 : ↥a.L₁ ≃* ↥a.L₁ ⧸ center ↥a.L₁ :=
      QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
    exact ⟨{ a with Z_triv := hZ, eL₁ := e1.trans q }⟩
  · exfalso
    have hd8 := a.d8_case
    obtain ⟨hu₁ord, hu₁Cub, -, hu₁conj, hF₀, -, -⟩ := a.d8_props hd8
    have hF : centralizer ({a.ub} : Set G) ⊓ centralizer (a.L₁ : Set G) ⊓
        centralizer ((conjSub t a.L₁ : Subgroup G) : Set G) = a.F₀ := by
      rw [← a.CPE_eq, centralizer_sup_eq_inf, inf_assoc]
    have hub2 : a.ub * a.ub = 1 := by
      have := pow_orderOf_eq_one a.ub
      rwa [a.ub_ord, pow_two] at this
    have hcle : ∀ b ∈ a.L₁, (∀ b' ∈ a.L₁, b * b' = b' * b) → b = 1 ∨ b = a.ub := by
      intro b hb hc
      have hmem : (⟨b, hb⟩ : ↥a.L₁) ∈ center ↥a.L₁ := by
        rw [Subgroup.mem_center_iff]
        intro g
        exact Subtype.ext (hc g g.2).symm
      have := a.Z_le ⟨⟨b, hb⟩, hmem, rfl⟩
      exact eq_one_or_eq_of_mem_zpowers_of_mul_self hub2 this
    have hc2 : Nat.card (center ↥a.L₁) = 2 := by
      obtain ⟨β, hβ⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hZ
      rw [Nat.card_eq_two_iff]
      refine ⟨1, β, ?_, ?_⟩
      · exact fun h => hβ (by simpa using h.symm)
      · ext γ
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
        have hcl : ∀ δ : ↥(center ↥a.L₁), (δ : G) = 1 ∨ (δ : G) = a.ub := by
          intro δ
          refine hcle δ (δ : ↥a.L₁).2 (fun b' hb' => ?_)
          have := (Subgroup.mem_center_iff.1 δ.2) ⟨b', hb'⟩
          exact congrArg Subtype.val this.symm
        have hβ' : ((β : ↥a.L₁) : G) = a.ub := by
          rcases hcl β with h | h
          · exact absurd (Subtype.ext (Subtype.ext h)) hβ
          · exact h
        rcases hcl γ with h | h
        · left; exact Subtype.ext (Subtype.ext h)
        · right; exact Subtype.ext (Subtype.ext (h.trans hβ'.symm))
    obtain ⟨q⟩ := a.L₁_A6
    let π : ↥a.L₁ →* A6 := q.toMonoidHom.comp (QuotientGroup.mk' (center ↥a.L₁))
    have hπ : Function.Surjective π := q.surjective.comp (QuotientGroup.mk'_surjective _)
    have hker : π.ker = center ↥a.L₁ := by
      ext x
      rw [MonoidHom.mem_ker]
      show q (QuotientGroup.mk x) = 1 ↔ _
      rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
    have hper : commutator ↥a.L₁ = ⊤ := a.L₁_comp.2.2.2.1
    obtain ⟨hAut, hrho⟩ := h13 G L t E W z hb a.toPA10
    have hA : AutFacts ↥a.L₁ :=
      ⟨fun x x' hx hx' => cover_trans hAut hπ hker hc2 hper hx hx',
        fun x hx => cover_card_cent hAut hπ hker hc2 hper hx,
        cover_card_aut hAut hπ hker hc2 hper,
        fun m n hm hn h => cover_conj_inj hker hc2 hm hn h⟩
    have hXcomm : ∀ u ∈ a.X, ∀ v ∈ a.X, u * v = v * u := by
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hc := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (G := ↥a.X)
        (by rw [a.X_card]; norm_num)
      intro u hu v hv
      exact congrArg Subtype.val (hc.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
    have hXcube := X_cube_aux a.L₁ π hker hc2 a.x a.x_mem a.x_ord a.X a.X_le a.X_card
    let c : S14Cfg G t :=
      { u := a.ub
        u₁ := a.u₁
        x := a.x
        c₃ := a.c₃
        L₁ := a.L₁
        K₁ := a.K₁
        X := a.X
        pair := PA8.pairData hb a.toPA9.toPA8
        u_ord := a.ub_ord
        u₁_mem := ⟨⟨hu₁Cub, (a.u₁_CPE hd8).1⟩, (a.u₁_CPE hd8).2⟩
        u₁_ord := hu₁ord
        u₁_conj := hu₁conj
        F_eq := hF.trans hF₀
        card_F := by rw [hF]; exact a.F₀_card hd8
        x_mem := a.x_mem
        x_ord := a.x_ord
        X_le := a.X_le
        X_card := a.X_card
        X_three := a.X_three
        X_comm := hXcomm
        X_cube := hXcube
        card_Cy := by rw [← a.x_y]; exact a.card_Cy
        c₃_K₁ := a.c₃_K₁
        c₃_L₁ := a.c₃_L₁
        c₃_ord := a.c₃_ord
        c₃_x := a.c₃_x
        c₃_nx := a.c₃_nx
        K₁_x := a.K₁_x
        K₁_xt := a.K₁_xt
        K₁_K₁t := fun p hp q hq =>
          (mem_centralizer_iff.1 (a.K₁_K₁t hp) (t * q * t⁻¹) ⟨q, hq, rfl⟩).symm
        u₁_S5 := a.u₁_S5
        u₁_K₁t := a.u₁_K₁t
        cent_x_xt := a.cent_x_xt
        rho_range := hrho
        center_le := hcle }
    exact c.false_of_cover hA (c.isKGroupCat_Yq hb.setting.1) hON hNo hper hc2 ⟨q⟩

theorem s14
    (hON : ONan77S5) (hNo : ONanNoSL29Y) : StepS14 :=
  s14_of_full hON hNo s13_full

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
