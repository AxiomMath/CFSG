module

public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.T1b

open CFSG.Open CFSG.SectionRank

theorem outStep_isElemAbelian_of_le {G : Type*} [Group G] {p : ℕ} {E E' : Subgroup G}
    (hE : IsElemAbelian p E) (h : E' ≤ E) : IsElemAbelian p E' := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => hE.2 x (h hx)⟩
  have := hE.1.is_comm.comm (⟨a, h a.2⟩ : E) ⟨b, h b.2⟩
  have h' := congrArg Subtype.val this
  exact Subtype.ext h'

theorem exists_card_pow_of_isElemAbelian {G : Type*} [Group G] [Finite G] {E : Subgroup G}
    (hE : IsElemAbelian 3 E) : ∃ j : ℕ, Nat.card E = 3 ^ j := by
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPG : IsPGroup 3 E := fun g => ⟨1, by
    rw [pow_one]; exact Subtype.ext (hE.2 g g.2)⟩
  exact (IsPGroup.iff_card (G := E)).1 hPG

theorem card_pow_three_eq_one_le {R : Type*} [Group R] [Finite R] [IsCyclic R] :
    Nat.card {r : R // r ^ 3 = 1} ≤ 3 := by
  classical
  have := Fintype.ofFinite R
  have := IsCyclic.card_pow_eq_one_le (α := R) (n := 3) (by norm_num)
  simpa [Nat.card_eq_fintype_card, Fintype.card_subtype] using this

theorem card_le_three_of_elemAbelian_cyclic {R : Type*} [Group R] [Finite R] [IsCyclic R]
    (F : Subgroup R) (hF : IsElemAbelian 3 F) : Nat.card F ≤ 3 := by
  let f : F → {r : R // r ^ 3 = 1} := fun x => ⟨x, hF.2 x x.2⟩
  have hinj : Function.Injective f := fun x y h => by
    have h' := congrArg Subtype.val h
    exact Subtype.ext h'
  exact (Nat.card_le_card_of_injective f hinj).trans card_pow_three_eq_one_le

theorem pRank_le_of_hom_ker {A C : Type*} [Group A] [Finite A] [Group C] (θ : A →* C)
    (hC : ∀ F : Subgroup C, IsElemAbelian 3 F → Nat.card F ≤ 3) :
    pRank 3 (⊤ : Subgroup A) ≤ pRank 3 θ.ker + 1 := by
  refine pRank_le (by norm_num) fun E _ hE => ?_
  set θE : E →* C := θ.comp E.subtype with hθE
  have hcard := Subgroup.card_ker_mul_card_range θE
  have hrange : θE.range = E.map θ := by
    rw [hθE, MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : Nat.card θE.ker = Nat.card (E ⊓ θ.ker : Subgroup A) := by
    have : θE.ker = (E ⊓ θ.ker).subgroupOf E := by
      ext x; simp [hθE, MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    rw [this]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : E ⊓ θ.ker ≤ E)).toEquiv
  rw [hrange, hker] at hcard
  have hE1 : IsElemAbelian 3 (E ⊓ θ.ker : Subgroup A) := outStep_isElemAbelian_of_le hE inf_le_left
  obtain ⟨j, hj⟩ := exists_card_pow_of_isElemAbelian hE1
  have hjle : j ≤ pRank 3 θ.ker := le_pRank (by norm_num) inf_le_right hE1 hj
  have h3 : Nat.card (E.map θ) ≤ 3 := hC _ (isElemAbelian_map hE θ)
  rw [← hcard, hj]
  calc 3 ^ j * Nat.card (E.map θ) ≤ 3 ^ pRank 3 θ.ker * 3 :=
        Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hjle) h3
    _ = 3 ^ (pRank 3 θ.ker + 1) := by rw [pow_succ]

theorem card_le_three_of_elemAbelian_prod {R M : Type*} [Group R] [Finite R] [IsCyclic R]
    [Group M] (hM : ∀ y : M, y ^ 2 = 1) (F : Subgroup (R × M)) (hF : IsElemAbelian 3 F) :
    Nat.card F ≤ 3 := by
  classical
  let f : F → {r : R // r ^ 3 = 1} := fun x => ⟨(x : R × M).1, by
    have := congrArg Prod.fst (hF.2 x x.2)
    simpa using this⟩
  have hinj : Function.Injective f := by
    have hmul : ∀ x y : F, (f x).1 = (f y).1 → x = y := by
      intro x y hxy
      have h3x : (x : R × M).2 ^ 3 = 1 := congrArg Prod.snd (hF.2 x x.2)
      have h3y : (y : R × M).2 ^ 3 = 1 := congrArg Prod.snd (hF.2 y y.2)
      have h2x := hM (x : R × M).2
      have h2y := hM (y : R × M).2
      have hx : (x : R × M).2 = 1 := by
        calc (x : R × M).2 = (x : R × M).2 ^ 3 * ((x : R × M).2 ^ 2)⁻¹ := by group
          _ = 1 := by rw [h3x, h2x]; simp
      have hy : (y : R × M).2 = 1 := by
        calc (y : R × M).2 = (y : R × M).2 ^ 3 * ((y : R × M).2 ^ 2)⁻¹ := by group
          _ = 1 := by rw [h3y, h2y]; simp
      exact Subtype.ext (Prod.ext hxy (hx.trans hy.symm))
    exact fun x y h => hmul x y (congrArg Subtype.val h)
  exact (Nat.card_le_card_of_injective f hinj).trans card_pow_three_eq_one_le

end CFSG.HardMathSupport.Timmesfeld.Tables.T1b
