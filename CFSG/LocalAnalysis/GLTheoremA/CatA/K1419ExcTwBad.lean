module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ExcArith
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcTwistedConfig

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K1419E

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.Chevalley CFSG.RankThree.Classical CFSG.RankThree.PartOne.KD4T
  CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.LocalAnalysis.GLTheoremB
  CFSG.ClassicalInvolution.ModelFacts.Levi CFSG.HardMathSupport.Dickson.Sec6
  CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2

section Bad

variable {G : Type} [Group G]

@[expose] def Bad27 (P : Subgroup G) : Prop :=
  ∃ X Y Z : Subgroup G, X ≤ P ∧ Y ≤ P ∧ Z ≤ P ∧
    (∀ a ∈ X, ∀ b ∈ Y, a * b = b * a) ∧ (∀ a ∈ X, ∀ b ∈ Z, a * b = b * a) ∧
    (∀ a ∈ Y, ∀ b ∈ Z, a * b = b * a) ∧
    (∀ a ∈ X, (∀ b ∈ X, a * b = b * a) → a = 1) ∧
    (∀ a ∈ Y, (∀ b ∈ Y, a * b = b * a) → a = 1) ∧
    (∀ a ∈ Z, (∀ b ∈ Z, a * b = b * a) → a = 1) ∧
    27 ∣ Nat.card X * Nat.card Y * Nat.card Z

theorem Bad27.map_conj {P : Subgroup G} (h : Bad27 P) (g : G) :
    Bad27 (P.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨X, Y, Z, hX, hY, hZ, hXY, hXZ, hYZ, cX, cY, cZ, hn⟩ := h
  have hcomm : ∀ {A B : Subgroup G}, (∀ a ∈ A, ∀ b ∈ B, a * b = b * a) →
      ∀ a ∈ A.map (MulAut.conj g).toMonoidHom, ∀ b ∈ B.map (MulAut.conj g).toMonoidHom,
        a * b = b * a := by
    rintro A B hAB _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ := by group
      _ = g * (y * x) * g⁻¹ := by rw [hAB x hx y hy]
      _ = g * y * g⁻¹ * (g * x * g⁻¹) := by group
  have hcard : ∀ A : Subgroup G, Nat.card (A.map (MulAut.conj g).toMonoidHom) = Nat.card A :=
    fun A => Subgroup.card_map_of_injective (MulAut.conj g).injective
  refine ⟨X.map (MulAut.conj g).toMonoidHom, Y.map (MulAut.conj g).toMonoidHom,
    Z.map (MulAut.conj g).toMonoidHom, Subgroup.map_mono hX, Subgroup.map_mono hY,
    Subgroup.map_mono hZ, hcomm hXY, hcomm hXZ, hcomm hYZ, centerless_map_conj g cX,
    centerless_map_conj g cY, centerless_map_conj g cZ, ?_⟩
  rw [hcard, hcard, hcard]
  exact hn

theorem Bad27.mono {P P' : Subgroup G} (h : P ≤ P') (hB : Bad27 P) : Bad27 P' := by
  obtain ⟨X, Y, Z, hX, hY, hZ, rest⟩ := hB
  exact ⟨X, Y, Z, hX.trans h, hY.trans h, hZ.trans h, rest⟩

theorem not_l3u3_of_bad27 (hF : L3U3Facts) {R : Subgroup G} [Finite R] (hB : Bad27 R)
    (h : L3U3 (↥R ⧸ Subgroup.center ↥R)) : False := by
  obtain ⟨X, Y, Z, hX, hY, hZ, hXY, hXZ, hYZ, cX, cY, cZ, hn⟩ := hB
  let X' : Subgroup ↥R := X.subgroupOf R
  let Y' : Subgroup ↥R := Y.subgroupOf R
  let Z' : Subgroup ↥R := Z.subgroupOf R
  have hcomm : ∀ {A B : Subgroup G}, (∀ a ∈ A, ∀ b ∈ B, a * b = b * a) →
      ∀ a ∈ A.subgroupOf R, ∀ b ∈ B.subgroupOf R, a * b = b * a := by
    intro A B hAB a ha b hb
    exact Subtype.ext (hAB _ ha _ hb)
  have hcl : ∀ {A : Subgroup G}, A ≤ R → (∀ a ∈ A, (∀ b ∈ A, a * b = b * a) → a = 1) →
      ∀ a ∈ A.subgroupOf R, (∀ b ∈ A.subgroupOf R, a * b = b * a) → a = 1 := by
    intro A hA cA a ha hab
    apply Subtype.ext
    refine cA _ ha fun b hb => ?_
    have := hab ⟨b, hA hb⟩ hb
    exact congrArg Subtype.val this
  have hcardA : ∀ {A : Subgroup G}, A ≤ R → Nat.card (A.subgroupOf R) = Nat.card A :=
    fun {A} hA => Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv
  have hdvd := card_mul_dvd_card_centerQuotient X' Y' Z' (hcomm hXY) (hcomm hXZ) (hcomm hYZ)
    (hcl hX cX) (hcl hY cY) (hcl hZ cZ)
  rw [hcardA hX, hcardA hY, hcardA hZ] at hdvd
  exact (hF.order _ h).not_27_dvd (hn.trans hdvd)

end Bad

section Arith

theorem l3u3_three_dvd_sq_sub_one {x : ℕ} (h : ¬ 3 ∣ x) : 3 ∣ x ^ 2 - 1 := by
  have hx : 0 < x := Nat.pos_of_ne_zero (by rintro rfl; exact h (dvd_zero 3))
  have h1 : 1 ≤ x ^ 2 := Nat.one_le_pow _ _ hx
  have h2 : x % 3 = 1 ∨ x % 3 = 2 := by omega
  have h3 : x ^ 2 % 3 = 1 := by
    rcases h2 with h2 | h2 <;> simp [Nat.pow_mod, h2]
  omega

theorem l3u3_not_three_dvd_two_pow (f : ℕ) : ¬ 3 ∣ 2 ^ f := fun h =>
  absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h) (by norm_num)

theorem l3u3_nine_dvd_sixtyFour_pow_sub_one (f : ℕ) : 9 ∣ 64 ^ f - 1 := by
  have h := Nat.sub_dvd_pow_sub_pow 64 1 f
  rw [one_pow] at h
  exact dvd_trans (by norm_num) h

theorem l3u3_twentySeven_dvd_swap (f : ℕ) :
    27 ∣ (2 ^ f) ^ 2 * (((2 ^ f) ^ 2) ^ 2 - 1) * ((2 ^ f) * ((2 ^ f) ^ 2 - 1)) *
      ((2 ^ f) * ((2 ^ f) ^ 2 - 1)) := by
  have h1 : 3 ∣ (2 ^ f) ^ 2 - 1 := l3u3_three_dvd_sq_sub_one (l3u3_not_three_dvd_two_pow f)
  have h2 : 3 ∣ ((2 ^ f) ^ 2) ^ 2 - 1 := l3u3_three_dvd_sq_sub_one fun h =>
    l3u3_not_three_dvd_two_pow f (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h)
  have h3 : 3 ∣ (2 ^ f) * ((2 ^ f) ^ 2 - 1) := Dvd.dvd.mul_left h1 _
  exact mul_dvd_mul (mul_dvd_mul (Dvd.dvd.mul_left h2 _) h3) h3

theorem l3u3_twentySeven_dvd_cycle (f : ℕ) :
    27 ∣ (2 ^ f) ^ 3 * (((2 ^ f) ^ 3) ^ 2 - 1) * ((2 ^ f) * ((2 ^ f) ^ 2 - 1)) := by
  have h1 : 3 ∣ (2 ^ f) ^ 2 - 1 := l3u3_three_dvd_sq_sub_one (l3u3_not_three_dvd_two_pow f)
  have h3 : 3 ∣ (2 ^ f) * ((2 ^ f) ^ 2 - 1) := Dvd.dvd.mul_left h1 _
  have h64 : ((2 ^ f) ^ 3) ^ 2 = 64 ^ f := by
    rw [← pow_mul, ← pow_mul, show (64 : ℕ) = 2 ^ 6 by norm_num, ← pow_mul]
    congr 1
    ring
  have h9 : 9 ∣ ((2 ^ f) ^ 3) ^ 2 - 1 := by
    rw [h64]
    exact l3u3_nine_dvd_sixtyFour_pow_sub_one f
  have h27 := mul_dvd_mul (Dvd.dvd.mul_left h9 ((2 ^ f) ^ 3)) h3
  simpa using h27

end Arith

section Config

variable {τ : Tag} {L : Type} [Field L] [CharP L 2]

theorem bad27_swap_in [IsAlgClosed L] (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {f : ℕ}
    (hf : 1 ≤ f) {βa βb βk βc : Fin τ.rank → ℤ} (cfg : D4Cfg τ βa βb βk βc)
    {F₁ : ModGL τ L →* ModGL τ L}
    (hFa : ∀ A : SL2 L, F₁ (rootSL2 τ L βa A) =
      rootSL2 τ L βb (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 f) A))
    (hFb : ∀ A : SL2 L, F₁ (rootSL2 τ L βb A) =
      rootSL2 τ L βa (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 f) A))
    (hFk : ∀ A : SL2 L, F₁ (rootSL2 τ L βk A) =
      rootSL2 τ L βk (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 f) A))
    (hFc : ∀ A : SL2 L, F₁ (rootSL2 τ L βc A) =
      rootSL2 τ L βc (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 f) A))
    (C : Subgroup (ModGL τ L))
    (hCab : (psiAB hτ cfg.ra cfg.rb cfg.ab f (2 * f)).range ≤ C)
    (hCk : (slHom βk (RingHom.id L) (frobeniusFixedField L 2 f)).range ≤ C)
    (hCc : (slHom βc (RingHom.id L) (frobeniusFixedField L 2 f)).range ≤ C) :
    Bad27 (C ⊓ Up34Chev2.fixSub F₁) := by
  classical
  have hFn := nD4_fixed_swap hτ cfg hFa hFb hFk hFc
  have hnC : nD4 L βa βb βk βc ∈ C := by
    rw [nD4_eq_swap hτ cfg f]
    exact mul_mem (mul_mem (hCc ⟨WSL, rfl⟩) (hCab ⟨WSL, rfl⟩)) (hCk ⟨WSL, rfl⟩)
  obtain ⟨Z, hZfix, hZC, hZc, hZcard, hZa, hZb, hZk⟩ :=
    exists_theta_factor hτ hf cfg F₁ hFc hFn C hnC hCc
  have h22 : 2 ^ (2 * f) = (2 ^ f) ^ 2 := by rw [mul_comm, pow_mul]
  have hΨab_apply := psiAB_apply (L := L) hτ cfg.ra cfg.rb cfg.ab f (2 * f)
  have hΨab_inj := psiAB_injective (L := L) hτ cfg.ra cfg.rb cfg.ab f (2 * f)
  have hΨab_fix : ∀ A, F₁ (psiAB hτ cfg.ra cfg.rb cfg.ab f (2 * f) A) =
      psiAB hτ cfg.ra cfg.rb cfg.ab f (2 * f) A := by
    intro A
    rw [hΨab_apply, map_mul, F_slHom _ hFa, F_slHom _ hFb, RingHom.comp_id]
    have : slHom βa ((iterateFrobenius L 2 f).comp (iterateFrobenius L 2 f))
        (frobeniusFixedField L 2 (2 * f)) A =
        slHom βa (RingHom.id L) (frobeniusFixedField L 2 (2 * f)) A := by
      rw [slHom_apply, slHom_apply, RingHom.comp_assoc, frob_comp_subtype_two, RingHom.id_comp]
    rw [this]
    exact (slHom_commute_gen hτ cfg.ra cfg.rb cfg.ab _ _ _ _ A A).eq.symm
  let Ψk : SL2 (frobeniusFixedField L 2 f) →* ModGL τ L :=
    slHom βk (RingHom.id L) (frobeniusFixedField L 2 f)
  have hΨk_inj : Function.Injective Ψk := slHom_injective _ _ _
  have hΨk_fix : ∀ A, F₁ (Ψk A) = Ψk A := by
    intro A
    change F₁ (slHom βk (RingHom.id L) (frobeniusFixedField L 2 f) A) =
      slHom βk (RingHom.id L) (frobeniusFixedField L 2 f) A
    rw [F_slHom _ hFk, RingHom.comp_id, slHom_frob_one]
  refine ⟨(psiAB hτ cfg.ra cfg.rb cfg.ab f (2 * f)).range, Ψk.range, Z, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨A, rfl⟩
    exact Subgroup.mem_inf.2 ⟨hCab ⟨A, rfl⟩, Up34Chev2.mem_fixSub.2 (hΨab_fix A)⟩
  · rintro _ ⟨A, rfl⟩
    exact Subgroup.mem_inf.2 ⟨hCk ⟨A, rfl⟩, Up34Chev2.mem_fixSub.2 (hΨk_fix A)⟩
  · intro g hg
    exact Subgroup.mem_inf.2 ⟨hZC g hg, Up34Chev2.mem_fixSub.2 (hZfix g hg)⟩
  · rintro _ ⟨A, rfl⟩ _ ⟨B, rfl⟩
    rw [hΨab_apply]
    exact (Commute.mul_left (slHom_commute_gen hτ cfg.ra cfg.rk cfg.ak _ _ _ _ A B)
      (slHom_commute_gen hτ cfg.rb cfg.rk cfg.bk _ _ _ _ A B)).eq
  · rintro _ ⟨A, rfl⟩ g hg
    rw [hΨab_apply]
    exact (Commute.mul_left (show Commute _ g from (hZa g hg _).symm)
      (show Commute _ g from (hZb g hg _).symm)).eq
  · rintro _ ⟨A, rfl⟩ g hg
    exact (show Commute _ g from (hZk g hg _).symm).eq
  · exact centerless_range _ hΨab_inj fun A hA => sl2_eq_one_of_forall_comm hA
  · exact centerless_range _ hΨk_inj fun A hA => sl2_eq_one_of_forall_comm hA
  · exact hZc
  · rw [card_range_of_injective _ hΨab_inj, card_range_of_injective _ hΨk_inj, hZcard,
      card_sl2_frobFixed (by omega : 0 < 2 * f), card_sl2_frobFixed (by omega : 0 < f), h22]
    exact l3u3_twentySeven_dvd_swap f

theorem bad27_cycle_in [IsAlgClosed L] (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {f : ℕ}
    (hf : 1 ≤ f) {βa βb βk βc : Fin τ.rank → ℤ} (cfg : D4Cfg τ βa βb βk βc)
    {F₁ : ModGL τ L →* ModGL τ L}
    (hFa : ∀ A : SL2 L, F₁ (rootSL2 τ L βa A) =
      rootSL2 τ L βb (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 f) A))
    (hFb : ∀ A : SL2 L, F₁ (rootSL2 τ L βb A) =
      rootSL2 τ L βk (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 f) A))
    (hFk : ∀ A : SL2 L, F₁ (rootSL2 τ L βk A) =
      rootSL2 τ L βa (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 f) A))
    (hFc : ∀ A : SL2 L, F₁ (rootSL2 τ L βc A) =
      rootSL2 τ L βc (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 f) A))
    (C : Subgroup (ModGL τ L))
    (hCabk : (psiABK hτ cfg f (3 * f)).range ≤ C)
    (hCc : (slHom βc (RingHom.id L) (frobeniusFixedField L 2 f)).range ≤ C) :
    Bad27 (C ⊓ Up34Chev2.fixSub F₁) := by
  classical
  have hFn := nD4_fixed_cycle hτ cfg hFa hFb hFk hFc
  have hnC : nD4 L βa βb βk βc ∈ C := by
    rw [nD4_eq_cycle hτ cfg f]
    exact mul_mem (hCc ⟨WSL, rfl⟩) (hCabk ⟨WSL, rfl⟩)
  obtain ⟨Z, hZfix, hZC, hZc, hZcard, hZa, hZb, hZk⟩ :=
    exists_theta_factor hτ hf cfg F₁ hFc hFn C hnC hCc
  have h33 : 2 ^ (3 * f) = (2 ^ f) ^ 3 := by rw [mul_comm, pow_mul]
  have hΨ₃_apply := psiABK_apply (L := L) hτ cfg f (3 * f)
  have hΨ₃_inj := psiABK_injective (L := L) hτ cfg f (3 * f)
  have hΨ₃_fix : ∀ A, F₁ (psiABK hτ cfg f (3 * f) A) = psiABK hτ cfg f (3 * f) A := by
    intro A
    rw [hΨ₃_apply, map_mul, map_mul, F_slHom _ hFa, F_slHom _ hFb, F_slHom _ hFk,
      RingHom.comp_id]
    have h3 : slHom βa ((iterateFrobenius L 2 f).comp ((iterateFrobenius L 2 f).comp
        (iterateFrobenius L 2 f))) (frobeniusFixedField L 2 (3 * f)) A =
        slHom βa (RingHom.id L) (frobeniusFixedField L 2 (3 * f)) A := by
      rw [slHom_apply, slHom_apply]
      simp only [RingHom.comp_assoc]
      rw [frob_comp_subtype_three, RingHom.id_comp]
    rw [h3]
    have hba := (slHom_commute_gen hτ cfg.rb cfg.ra (by rw [iform_comm]; exact cfg.ab)
      (iterateFrobenius L 2 f) (RingHom.id L) (frobeniusFixedField L 2 (3 * f))
      (frobeniusFixedField L 2 (3 * f)) A A).eq
    have hka := (slHom_commute_gen hτ cfg.rk cfg.ra (by rw [iform_comm]; exact cfg.ak)
      ((iterateFrobenius L 2 f).comp (iterateFrobenius L 2 f)) (RingHom.id L)
      (frobeniusFixedField L 2 (3 * f)) (frobeniusFixedField L 2 (3 * f)) A A).eq
    calc slHom βb (iterateFrobenius L 2 f) (frobeniusFixedField L 2 (3 * f)) A *
          slHom βk ((iterateFrobenius L 2 f).comp (iterateFrobenius L 2 f))
            (frobeniusFixedField L 2 (3 * f)) A *
          slHom βa (RingHom.id L) (frobeniusFixedField L 2 (3 * f)) A
        = slHom βb (iterateFrobenius L 2 f) (frobeniusFixedField L 2 (3 * f)) A *
          (slHom βk ((iterateFrobenius L 2 f).comp (iterateFrobenius L 2 f))
            (frobeniusFixedField L 2 (3 * f)) A *
          slHom βa (RingHom.id L) (frobeniusFixedField L 2 (3 * f)) A) := by
          simp only [mul_assoc]
      _ = slHom βb (iterateFrobenius L 2 f) (frobeniusFixedField L 2 (3 * f)) A *
          (slHom βa (RingHom.id L) (frobeniusFixedField L 2 (3 * f)) A *
          slHom βk ((iterateFrobenius L 2 f).comp (iterateFrobenius L 2 f))
            (frobeniusFixedField L 2 (3 * f)) A) := by rw [hka]
      _ = slHom βa (RingHom.id L) (frobeniusFixedField L 2 (3 * f)) A *
          slHom βb (iterateFrobenius L 2 f) (frobeniusFixedField L 2 (3 * f)) A *
          slHom βk ((iterateFrobenius L 2 f).comp (iterateFrobenius L 2 f))
            (frobeniusFixedField L 2 (3 * f)) A := by
          rw [← mul_assoc, hba, mul_assoc]
  refine ⟨(psiABK hτ cfg f (3 * f)).range, Z, ⊥, ?_, ?_, bot_le, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨A, rfl⟩
    exact Subgroup.mem_inf.2 ⟨hCabk ⟨A, rfl⟩, Up34Chev2.mem_fixSub.2 (hΨ₃_fix A)⟩
  · intro g hg
    exact Subgroup.mem_inf.2 ⟨hZC g hg, Up34Chev2.mem_fixSub.2 (hZfix g hg)⟩
  · rintro _ ⟨A, rfl⟩ g hg
    rw [hΨ₃_apply]
    exact (Commute.mul_left (Commute.mul_left (show Commute _ g from (hZa g hg _).symm)
      (show Commute _ g from (hZb g hg _).symm)) (show Commute _ g from (hZk g hg _).symm)).eq
  · rintro a _ b hb
    rw [Subgroup.mem_bot.1 hb, mul_one, one_mul]
  · rintro a _ b hb
    rw [Subgroup.mem_bot.1 hb, mul_one, one_mul]
  · exact centerless_range _ hΨ₃_inj fun A hA => sl2_eq_one_of_forall_comm hA
  · exact hZc
  · intro a ha _
    exact Subgroup.mem_bot.1 ha
  · rw [card_range_of_injective _ hΨ₃_inj, hZcard, Subgroup.card_bot,
      card_sl2_frobFixed (by omega : 0 < 3 * f), h33, mul_one]
    exact l3u3_twentySeven_dvd_cycle f

theorem bad27_swap [IsAlgClosed L] (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {f : ℕ}
    (hf : 1 ≤ f) {βa βb βk βc : Fin τ.rank → ℤ} (cfg : D4Cfg τ βa βb βk βc)
    {F₁ : ModGL τ L →* ModGL τ L}
    (hFa : ∀ A : SL2 L, F₁ (rootSL2 τ L βa A) =
      rootSL2 τ L βb (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 f) A))
    (hFb : ∀ A : SL2 L, F₁ (rootSL2 τ L βb A) =
      rootSL2 τ L βa (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 f) A))
    (hFk : ∀ A : SL2 L, F₁ (rootSL2 τ L βk A) =
      rootSL2 τ L βk (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 f) A))
    (hFc : ∀ A : SL2 L, F₁ (rootSL2 τ L βc A) =
      rootSL2 τ L βc (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 f) A)) :
    Bad27 (cfgGroup τ L βa βb βk βc ⊓ Up34Chev2.fixSub F₁) :=
  bad27_swap_in hτ hf cfg hFa hFb hFk hFc _
    (by
      rintro _ ⟨A, rfl⟩
      rw [psiAB_apply]
      exact mul_mem (rootSL2_mem_cfgGroup_a _) (rootSL2_mem_cfgGroup_b _))
    (by
      rintro _ ⟨A, rfl⟩
      exact rootSL2_mem_cfgGroup_k _)
    (by
      rintro _ ⟨A, rfl⟩
      exact rootSL2_mem_cfgGroup_c _)

theorem bad27_cycle [IsAlgClosed L] (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {f : ℕ}
    (hf : 1 ≤ f) {βa βb βk βc : Fin τ.rank → ℤ} (cfg : D4Cfg τ βa βb βk βc)
    {F₁ : ModGL τ L →* ModGL τ L}
    (hFa : ∀ A : SL2 L, F₁ (rootSL2 τ L βa A) =
      rootSL2 τ L βb (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 f) A))
    (hFb : ∀ A : SL2 L, F₁ (rootSL2 τ L βb A) =
      rootSL2 τ L βk (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 f) A))
    (hFk : ∀ A : SL2 L, F₁ (rootSL2 τ L βk A) =
      rootSL2 τ L βa (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 f) A))
    (hFc : ∀ A : SL2 L, F₁ (rootSL2 τ L βc A) =
      rootSL2 τ L βc (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 f) A)) :
    Bad27 (cfgGroup τ L βa βb βk βc ⊓ Up34Chev2.fixSub F₁) :=
  bad27_cycle_in hτ hf cfg hFa hFb hFk hFc _
    (by
      rintro _ ⟨A, rfl⟩
      rw [psiABK_apply]
      exact mul_mem (mul_mem (rootSL2_mem_cfgGroup_a _) (rootSL2_mem_cfgGroup_b _))
        (rootSL2_mem_cfgGroup_k _))
    (by
      rintro _ ⟨A, rfl⟩
      exact rootSL2_mem_cfgGroup_c _)

end Config

end CFSG.LocalAnalysis.GLTheoremA.K1419E

end
