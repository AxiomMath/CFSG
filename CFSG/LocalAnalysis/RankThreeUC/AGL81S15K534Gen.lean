module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K534Group
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.A6Gen

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K534Proof

open Module CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542 CFSG.QuasithinUnique.Setup

section Tail

variable {S : Type*} [AddCommGroup S] [Module (ZMod 2) S] [Finite S]
  {Y A : Subgroup (Module.End (ZMod 2) S)ˣ}

theorem finrank_le_of_generation {m : ℕ} (t : Fin m → (Module.End (ZMod 2) S)ˣ)
    (hgen : ∀ y ∈ Y, y ∈ Subgroup.closure (⋃ i,
      ((A.map (MulAut.conj (t i)).toMonoidHom : Subgroup (Module.End (ZMod 2) S)ˣ) :
        Set (Module.End (ZMod 2) S)ˣ)))
    (hCY : ∀ v : S, (∀ y ∈ Y, (y : Module.End (ZMod 2) S) v = v) → v = 0) :
    Module.finrank (ZMod 2) S ≤ m * (Module.finrank (ZMod 2) S -
      Module.finrank (ZMod 2) ↥(CFSG.LocalAnalysis.CommutingFactor.fixedSub A)) := by
  classical
  let F : Fin m → Submodule (ZMod 2) S := fun i =>
    (CFSG.LocalAnalysis.CommutingFactor.fixedSub A).map
      (↑(LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) S (t i)) : S →ₗ[ZMod 2] S)
  have hcancel : ∀ (u : (Module.End (ZMod 2) S)ˣ) (x : S),
      ((u⁻¹ : (Module.End (ZMod 2) S)ˣ) : Module.End (ZMod 2) S)
        ((u : Module.End (ZMod 2) S) x) = x := by
    intro u x
    rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    rfl
  have hF : (⨅ i, F i) = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_iInf] at hv
    have hvCY : ∀ y ∈ Y, (y : Module.End (ZMod 2) S) v = v := by
      intro y hy
      let Stab : Subgroup (Module.End (ZMod 2) S)ˣ :=
        { carrier := {u | (u : Module.End (ZMod 2) S) v = v}
          mul_mem' := fun {a b} ha hb => by
            show ((a * b : (Module.End (ZMod 2) S)ˣ) : Module.End (ZMod 2) S) v = v
            rw [Units.val_mul, Module.End.mul_apply]
            have ha' : (a : Module.End (ZMod 2) S) v = v := ha
            have hb' : (b : Module.End (ZMod 2) S) v = v := hb
            rw [hb', ha']
          one_mem' := by
            show (((1 : (Module.End (ZMod 2) S)ˣ)) : Module.End (ZMod 2) S) v = v
            simp
          inv_mem' := fun {a} ha => by
            have ha' : (a : Module.End (ZMod 2) S) v = v := ha
            show ((a⁻¹ : (Module.End (ZMod 2) S)ˣ) : Module.End (ZMod 2) S) v = v
            have := hcancel a v
            rwa [ha'] at this }
      have hle : Subgroup.closure (⋃ i,
          ((A.map (MulAut.conj (t i)).toMonoidHom : Subgroup (Module.End (ZMod 2) S)ˣ) :
            Set (Module.End (ZMod 2) S)ˣ)) ≤ Stab := by
        rw [Subgroup.closure_le]
        intro g hg
        obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hg
        obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hi
        obtain ⟨w, hw, hwv⟩ := Submodule.mem_map.1 (hv i)
        have hwv' : ((t i : (Module.End (ZMod 2) S)ˣ) : Module.End (ZMod 2) S) w = v := by
          rw [← hwv]
          show _ = ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) S (t i)) w)
          rw [LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv]
        have hwA : (a : Module.End (ZMod 2) S) w = w :=
          CFSG.LocalAnalysis.CommutingFactor.mem_fixedSub.1 hw a ha
        show (((MulAut.conj (t i)).toMonoidHom a : (Module.End (ZMod 2) S)ˣ) :
          Module.End (ZMod 2) S) v = v
        have e : (MulAut.conj (t i)).toMonoidHom a = t i * a * (t i)⁻¹ := rfl
        rw [e, ← hwv', Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply,
          hcancel, hwA]
      exact hle (hgen y hy)
    exact (Submodule.mem_bot _).2 (hCY v hvCY)
  have hsum := finrank_le_sum_codim F hF
  have hcodim : ∀ i, finrank (ZMod 2) S - finrank (ZMod 2) ↥(F i) =
      finrank (ZMod 2) S -
        finrank (ZMod 2) ↥(CFSG.LocalAnalysis.CommutingFactor.fixedSub A) := fun i => by
    simp only [F]
    rw [LinearEquiv.finrank_map_eq]
  simp only [hcodim, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  exact hsum

end Tail

section TwoGroup

variable {S : Type*} [AddCommGroup S] [Module (ZMod 2) S] [Finite S] [Nontrivial S]

theorem eq_one_of_normal_two_group {D P : Subgroup (Module.End (ZMod 2) S)ˣ}
    (hirr : ∀ N : Submodule (ZMod 2) S,
      (∀ d ∈ D, ∀ v ∈ N, (d : Module.End (ZMod 2) S) v ∈ N) → N = ⊥ ∨ N = ⊤)
    (hP : IsPGroup 2 ↥P) (hconj : ∀ d ∈ D, ∀ c ∈ P, d⁻¹ * c * d ∈ P) :
    ∀ c ∈ P, c = 1 := by
  classical
  set F := CFSG.LocalAnalysis.CommutingFactor.fixedSub P with hF
  have hFinv : ∀ d ∈ D, ∀ v ∈ F, (d : Module.End (ZMod 2) S) v ∈ F := by
    intro d hd v hv
    rw [hF, CFSG.LocalAnalysis.CommutingFactor.mem_fixedSub] at hv ⊢
    intro c hc
    have h1 := hv _ (hconj d hd c hc)
    have e : ((d⁻¹ * c * d : (Module.End (ZMod 2) S)ˣ) : Module.End (ZMod 2) S) v =
        ((d⁻¹ : (Module.End (ZMod 2) S)ˣ) : Module.End (ZMod 2) S)
          ((c : Module.End (ZMod 2) S) ((d : Module.End (ZMod 2) S) v)) :=
      rfl
    rw [e] at h1
    have h2 : (d : Module.End (ZMod 2) S) (((d⁻¹ : (Module.End (ZMod 2) S)ˣ) : Module.End (ZMod 2) S)
        ((c : Module.End (ZMod 2) S) ((d : Module.End (ZMod 2) S) v))) =
        (d : Module.End (ZMod 2) S) v := congrArg _ h1
    rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Module.End.one_apply] at h2
    exact h2
  have hFtop : F = ⊤ := by
    rcases hirr F hFinv with h | h
    · exfalso
      have hmod := hP.card_modEq_card_fixedPoints S
      have hfix : Nat.card (MulAction.fixedPoints ↥P S) = 1 := by
        rw [Nat.card_eq_one_iff_exists]
        refine ⟨⟨0, fun c => ?_⟩, fun x => ?_⟩
        · show ((c : (Module.End (ZMod 2) S)ˣ) : Module.End (ZMod 2) S) 0 = 0
          exact map_zero _
        · apply Subtype.ext
          have hx : (x : S) ∈ F := by
            rw [hF, CFSG.LocalAnalysis.CommutingFactor.mem_fixedSub]
            intro c hc
            exact x.2 ⟨c, hc⟩
          rw [h, Submodule.mem_bot] at hx
          exact hx
      rw [hfix, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hmod
      have hpos : 0 < finrank (ZMod 2) S := Module.finrank_pos
      have h0 : 2 ^ finrank (ZMod 2) S % 2 = 0 := by
        obtain ⟨k, hk⟩ : ∃ k, finrank (ZMod 2) S = k + 1 :=
          ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
        rw [hk, pow_succ]
        simp
      have := hmod
      unfold Nat.ModEq at this
      rw [h0] at this
      norm_num at this
    · exact h
  intro d hd
  apply Units.ext
  refine LinearMap.ext fun v => ?_
  have hv : v ∈ F := by rw [hFtop]; exact Submodule.mem_top
  rw [hF, CFSG.LocalAnalysis.CommutingFactor.mem_fixedSub] at hv
  exact hv d hd

end TwoGroup

section Centralizer

variable {S : Type*} [AddCommGroup S] [Module (ZMod 2) S] [Finite S] [Nontrivial S]
  {Y A : Subgroup (Module.End (ZMod 2) S)ˣ}

theorem mem_of_commute_of_irreducible
    (hirr : ∀ N : Submodule (ZMod 2) S,
      (∀ d ∈ Y ⊔ A, ∀ v ∈ N, (d : Module.End (ZMod 2) S) v ∈ N) → N = ⊥ ∨ N = ⊤)
    (hAN : A ≤ Subgroup.normalizer (Y : Set (Module.End (ZMod 2) S)ˣ))
    (hZ3 : ∀ w ∈ Y, (∀ y ∈ Y, w * y = y * w) → w ^ 3 = 1)
    (hA2 : ∀ a ∈ A, a ^ 2 = 1) :
    ∀ d ∈ Y ⊔ A, (∀ y ∈ Y, d * y = y * d) → d ∈ Y := by
  classical
  have hDN : Y ⊔ A ≤ Subgroup.normalizer (Y : Set (Module.End (ZMod 2) S)ˣ) :=
    sup_le Subgroup.le_normalizer hAN
  set C : Subgroup (Module.End (ZMod 2) S)ˣ :=
    (Y ⊔ A) ⊓ Subgroup.centralizer (Y : Set (Module.End (ZMod 2) S)ˣ) with hC
  have hCcomm : ∀ c ∈ C, ∀ y ∈ Y, y * c = c * y := fun c hc y hy =>
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2 y hy
  have hsqY : ∀ c ∈ C, c * c ∈ Y := by
    intro c hc
    obtain ⟨hcD, -⟩ := Subgroup.mem_inf.mp hc
    have hmem : c ∈ ((Y ⊔ A : Subgroup (Module.End (ZMod 2) S)ˣ) :
        Set (Module.End (ZMod 2) S)ˣ) := hcD
    rw [Subgroup.coe_mul_of_right_le_normalizer_left Y A hAN] at hmem
    obtain ⟨y, hy, a, ha, rfl⟩ := hmem
    have h1 : a * y * a⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp (hAN ha) y).mp hy
    have h2 : a * a = 1 := by rw [← pow_two]; exact hA2 a ha
    have e : y * a * (y * a) = y * (a * y * a⁻¹) * (a * a) := by group
    rw [e, h2, mul_one]
    exact Y.mul_mem hy h1
  have hsqcomm : ∀ c ∈ C, ∀ y ∈ Y, c * c * y = y * (c * c) := by
    intro c hc y hy
    have h := hCcomm c hc y hy
    calc c * c * y = c * (c * y) := by group
      _ = c * (y * c) := by rw [h]
      _ = (c * y) * c := by group
      _ = (y * c) * c := by rw [h]
      _ = y * (c * c) := by group
  have hcube : ∀ c ∈ C, (c * c) ^ 3 = 1 := fun c hc => hZ3 _ (hsqY c hc) (hsqcomm c hc)
  let P : Subgroup (Module.End (ZMod 2) S)ˣ :=
    { carrier := {c | c ∈ C ∧ c * c = 1}
      mul_mem' := fun {c₁ c₂} h₁ h₂ => by
        obtain ⟨hc₁, h11⟩ := h₁
        obtain ⟨hc₂, h22⟩ := h₂
        refine ⟨C.mul_mem hc₁ hc₂, ?_⟩
        set w := c₁ * c₂ * (c₁ * c₂) with hw
        have hwY : w ∈ Y := hsqY _ (C.mul_mem hc₁ hc₂)
        have hw3 : w ^ 3 = 1 := hcube _ (C.mul_mem hc₁ hc₂)
        have hc2w : c₂ * w = w * c₂ := (hCcomm c₂ hc₂ w hwY).symm
        have e1 : c₁ * c₂ * c₁ = w * c₂ := by
          calc c₁ * c₂ * c₁ = c₁ * c₂ * c₁ * (c₂ * c₂) := by rw [h22, mul_one]
            _ = w * c₂ := by rw [hw]; group
        have e2 : (c₁ * c₂ * c₁) * (c₁ * c₂ * c₁) = 1 := by
          calc (c₁ * c₂ * c₁) * (c₁ * c₂ * c₁) = c₁ * c₂ * (c₁ * c₁) * c₂ * c₁ := by group
            _ = c₁ * (c₂ * c₂) * c₁ := by rw [h11, mul_one]; group
            _ = 1 := by rw [h22, mul_one, h11]
        have e3 : (w * c₂) * (w * c₂) = w * w := by
          calc (w * c₂) * (w * c₂) = w * (c₂ * w) * c₂ := by group
            _ = w * (w * c₂) * c₂ := by rw [hc2w]
            _ = w * w * (c₂ * c₂) := by group
            _ = w * w := by rw [h22, mul_one]
        have hww : w * w = 1 := by rw [← e3, ← e1]; exact e2
        calc w = w * (w * w) := by rw [hww, mul_one]
          _ = w ^ 3 := (pow_three w).symm
          _ = 1 := hw3
      one_mem' := ⟨C.one_mem, mul_one 1⟩
      inv_mem' := fun {c} h => ⟨C.inv_mem h.1, by rw [← mul_inv_rev, h.2, inv_one]⟩ }
  have hconjC : ∀ d ∈ Y ⊔ A, ∀ c ∈ C, d⁻¹ * c * d ∈ C := by
    intro d hd c hc
    obtain ⟨hcD, hcY⟩ := Subgroup.mem_inf.mp hc
    refine Subgroup.mem_inf.mpr ⟨(Y ⊔ A).mul_mem ((Y ⊔ A).mul_mem ((Y ⊔ A).inv_mem hd) hcD) hd, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y' hy'
    have h1 : d * y' * d⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp (hDN hd) y').mp hy'
    have h2 := Subgroup.mem_centralizer_iff.mp hcY _ h1
    calc y' * (d⁻¹ * c * d) = d⁻¹ * ((d * y' * d⁻¹) * c) * d := by group
      _ = d⁻¹ * (c * (d * y' * d⁻¹)) * d := by rw [h2]
      _ = d⁻¹ * c * d * y' := by group
  have hconjP : ∀ d ∈ Y ⊔ A, ∀ c ∈ P, d⁻¹ * c * d ∈ P := by
    intro d hd c hc
    refine ⟨hconjC d hd c hc.1, ?_⟩
    calc d⁻¹ * c * d * (d⁻¹ * c * d) = d⁻¹ * (c * c) * d := by group
      _ = 1 := by rw [hc.2]; group
  have hP2 : IsPGroup 2 ↥P := fun c => ⟨1, Subtype.ext (by
    rw [pow_one, pow_two]
    exact c.2.2)⟩
  have hP1 : ∀ c ∈ P, c = 1 := eq_one_of_normal_two_group hirr hP2 hconjP
  intro d hd hcomm
  have hdC : d ∈ C := Subgroup.mem_inf.mpr ⟨hd, Subgroup.mem_centralizer_iff.mpr fun y hy =>
    (hcomm y hy).symm⟩
  have hd3 : d ^ 3 ∈ P := by
    refine ⟨C.pow_mem hdC 3, ?_⟩
    calc d ^ 3 * d ^ 3 = d ^ (3 + 3) := (pow_add d 3 3).symm
      _ = (d * d) ^ 3 := by rw [← sq, ← pow_mul]
      _ = 1 := hcube d hdC
  have hd31 : d ^ 3 = 1 := hP1 _ hd3
  have hdd : d = (d * d)⁻¹ := eq_inv_of_mul_eq_one_left (by
    calc d * (d * d) = d ^ 3 := (pow_three d).symm
      _ = 1 := hd31)
  have hmem : (d * d)⁻¹ ∈ Y := Y.inv_mem (hsqY d hdC)
  rwa [← hdd] at hmem

end Centralizer

section Quotient

open CFSG.ComponentClassification.PerfectAutomorphisms

theorem congr_conj {G H : Type*} [Group G] [Group H] (e : G ≃* H) (g : G) :
    MulAut.congr e (MulAut.conj g) = MulAut.conj (e g) := by
  ext x
  simp [MulAut.congr_apply, MulAut.conj_apply]

end Quotient

section Main

open CFSG.ComponentClassification.PerfectAutomorphisms

variable {S : Type*} [AddCommGroup S] [Module (ZMod 2) S] [Finite S] [Nontrivial S]
  {Y A : Subgroup (Module.End (ZMod 2) S)ˣ}

theorem q3a6_short_gen
    (hirr : ∀ N : Submodule (ZMod 2) S,
      (∀ d ∈ Y ⊔ A, ∀ v ∈ N, (d : Module.End (ZMod 2) S) v ∈ N) → N = ⊥ ∨ N = ⊤)
    (hAN : A ≤ Subgroup.normalizer (Y : Set (Module.End (ZMod 2) S)ˣ))
    (hq : CFSG.Open.IsQuasisimple ↥Y) (hZ : Nat.card (Subgroup.center ↥Y) = 3)
    (e6 : (↥Y ⧸ Subgroup.center ↥Y) ≃* alternatingGroup (Fin 6)) (hA1 : A ≠ ⊥)
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hA2 : ∀ a ∈ A, a ^ 2 = 1) :
    ∃ r m : ℕ, Nat.card A = 2 ^ r ∧ 1 ≤ r ∧ r ≤ 3 ∧ m * r ≤ 6 ∧
      Module.finrank (ZMod 2) S ≤ m * (Module.finrank (ZMod 2) S -
        Module.finrank (ZMod 2) ↥(CFSG.LocalAnalysis.CommutingFactor.fixedSub A)) := by
  classical
  haveI : Group.IsPerfect ↥Y := isPerfect_of_isQuasisimple hq
  have hDN : Y ⊔ A ≤ Subgroup.normalizer (Y : Set (Module.End (ZMod 2) S)ˣ) :=
    sup_le Subgroup.le_normalizer hAN
  have hZ3 : ∀ w ∈ Y, (∀ y ∈ Y, w * y = y * w) → w ^ 3 = 1 := by
    intro w hw hc
    have hcen : (⟨w, hw⟩ : ↥Y) ∈ Subgroup.center ↥Y := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hc g g.2).symm
    exact congrArg Subtype.val (pow_three_eq_one_of_mem_center hZ hcen)
  have hcentr := mem_of_commute_of_irreducible hirr hAN hZ3 hA2
  let Φ := conjOn hDN (MulEquiv.refl ↥Y)
  let π : ↥Y →* alternatingGroup (Fin 6) :=
    e6.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥Y))
  let Ψ : ↥(Y ⊔ A) →* MulAut (alternatingGroup (Fin 6)) :=
    (MulAut.congr e6).toMonoidHom.comp ((centerQuotientHom ↥Y).comp Φ)
  have hΨker : ∀ d : ↥(Y ⊔ A), Ψ d = 1 → ∀ y ∈ Y,
      (d : (Module.End (ZMod 2) S)ˣ) * y = y * d := by
    intro d hd y hy
    have h1 : (centerQuotientHom ↥Y) (Φ d) = 1 :=
      (MulEquiv.map_eq_one_iff (MulAut.congr e6)).1 hd
    have h2 : Φ d = 1 := centerQuotientHom_injective ↥Y (h1.trans (map_one _).symm)
    have h3 := conjOn_symm_coe hDN (MulEquiv.refl ↥Y) d ⟨y, hy⟩
    change ((MulEquiv.refl ↥Y).symm (Φ d ⟨y, hy⟩) : (Module.End (ZMod 2) S)ˣ) = _ at h3
    rw [h2] at h3
    simp only [MulAut.one_apply, MulEquiv.refl_symm, MulEquiv.refl_apply] at h3
    calc (d : (Module.End (ZMod 2) S)ˣ) * y =
        ((d : (Module.End (ZMod 2) S)ˣ) * y * (d : (Module.End (ZMod 2) S)ˣ)⁻¹) * d := by group
      _ = y * d := by rw [← h3]
  have hΨA : ∀ a ∈ A, ∀ h : a ∈ Y ⊔ A, Ψ ⟨a, h⟩ = 1 → a = 1 := by
    intro a ha hmem hΨ1
    have hcomm := hΨker ⟨a, hmem⟩ hΨ1
    have haY : a ∈ Y := hcentr a hmem hcomm
    have ha3 : a ^ 3 = 1 := hZ3 a haY (fun y hy => hcomm y hy)
    have ha2 : a ^ 2 = 1 := hA2 a ha
    have h : a * a ^ 2 = 1 := by rw [← pow_succ']; exact ha3
    calc a = (a ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left h
      _ = 1 := by rw [ha2, inv_one]
  let ιA : ↥A →* ↥(Y ⊔ A) := Subgroup.inclusion le_sup_right
  let ψA : ↥A →* MulAut (alternatingGroup (Fin 6)) := Ψ.comp ιA
  have hψA : Function.Injective ψA := by
    rw [injective_iff_map_eq_one]
    intro a ha
    exact Subtype.ext (hΨA a a.2 _ ha)
  set A' : Subgroup (MulAut (alternatingGroup (Fin 6))) := ψA.range with hA'
  have hcardA' : Nat.card A' = Nat.card A :=
    (Nat.card_congr (MonoidHom.ofInjective hψA).toEquiv).symm
  have hA'ne : A' ≠ ⊥ := by
    intro h
    apply hA1
    rw [← Subgroup.card_eq_one, ← hcardA', h, Subgroup.card_bot]
  have hel : CFSG.IsElementaryAbelian 2 ↥A' := by
    refine (CFSG.Quasithin.BlueprintB2.isElemAbelian_iff_isElementaryAbelian 2).1
      ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨_, ⟨x, rfl⟩⟩ := a
      obtain ⟨_, ⟨y, rfl⟩⟩ := b
      apply Subtype.ext
      show ψA x * ψA y = ψA y * ψA x
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hAc _ x.2 _ y.2)
    · rintro _ ⟨x, rfl⟩
      rw [← map_pow]
      have : x ^ 2 = 1 := Subtype.ext (hA2 _ x.2)
      rw [this, map_one]
  obtain ⟨r, m, hcard, hr1, hr3, hmr, s, hgen⟩ := X3Aut.d4_alt6 A' hA'ne hel
  have hπ : Function.Surjective π := e6.surjective.comp (QuotientGroup.mk'_surjective _)
  choose t ht using fun i => hπ (s i)
  have hΨy : ∀ y : ↥Y, Ψ ⟨(y : (Module.End (ZMod 2) S)ˣ), Subgroup.mem_sup_left y.2⟩ =
      MulAut.conj (π y) := by
    intro y
    have h1 := conjOn_of_mem hDN (MulEquiv.refl ↥Y) y
    change (MulAut.congr e6) ((centerQuotientHom ↥Y)
      (conjOn hDN (MulEquiv.refl ↥Y) ⟨(y : (Module.End (ZMod 2) S)ˣ), _⟩)) = _
    rw [h1]
    simp only [MulEquiv.refl_apply]
    rw [CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_conj, congr_conj]
    rfl
  set H : Subgroup (Module.End (ZMod 2) S)ˣ := Subgroup.closure (⋃ i,
    ((A.map (MulAut.conj ((t i : ↥Y) : (Module.End (ZMod 2) S)ˣ)).toMonoidHom :
      Subgroup (Module.End (ZMod 2) S)ˣ) : Set (Module.End (ZMod 2) S)ˣ)) with hH
  have hΨτ : ∀ i, Ψ ⟨((t i : ↥Y) : (Module.End (ZMod 2) S)ˣ),
      Subgroup.mem_sup_left (t i).2⟩ = MulAut.conj (s i) := by
    intro i
    rw [hΨy, ht]
  have hle : Subgroup.closure (⋃ i, ((A'.map (MulAut.conj (MulAut.conj (s i))).toMonoidHom :
      Subgroup (MulAut (alternatingGroup (Fin 6)))) :
        Set (MulAut (alternatingGroup (Fin 6))))) ≤ (H.subgroupOf (Y ⊔ A)).map Ψ := by
    rw [Subgroup.closure_le]
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
    obtain ⟨q, hq', rfl⟩ := Subgroup.mem_map.1 hi
    obtain ⟨a, rfl⟩ := hq'
    set τ : ↥(Y ⊔ A) := ⟨((t i : ↥Y) : (Module.End (ZMod 2) S)ˣ),
      Subgroup.mem_sup_left (t i).2⟩ with hτ
    refine ⟨τ * ιA a * τ⁻¹, ?_, ?_⟩
    · refine Subgroup.mem_subgroupOf.2 ?_
      refine Subgroup.subset_closure (Set.mem_iUnion.2 ⟨i, Subgroup.mem_map.2 ⟨a, a.2, ?_⟩⟩)
      rfl
    · rw [map_mul, map_mul, map_inv, hΨτ]
      simp [ψA, MulAut.conj_apply]
  have hgenY : ∀ y ∈ Y, y ∈ H := by
    have hsup : (H.comap Y.subtype) ⊔ Subgroup.center ↥Y = ⊤ := by
      rw [eq_top_iff]
      intro y _
      have hyD : (y : (Module.End (ZMod 2) S)ˣ) ∈ Y ⊔ A := Subgroup.mem_sup_left y.2
      have hinn : Ψ ⟨y, hyD⟩ ∈ (MulAut.conj : alternatingGroup (Fin 6) →*
          MulAut (alternatingGroup (Fin 6))).range := ⟨π y, (hΨy y).symm⟩
      obtain ⟨h, hh, hΨh⟩ := Subgroup.mem_map.1 (hle (hgen hinn))
      have hc : Ψ (h⁻¹ * ⟨y, hyD⟩) = 1 := by rw [map_mul, map_inv, hΨh, inv_mul_cancel]
      have hcomm := hΨker _ hc
      have hcD : ((h⁻¹ * ⟨y, hyD⟩ : ↥(Y ⊔ A)) : (Module.End (ZMod 2) S)ˣ) ∈ Y ⊔ A :=
        (h⁻¹ * ⟨y, hyD⟩).2
      have hcY : ((h⁻¹ * ⟨y, hyD⟩ : ↥(Y ⊔ A)) : (Module.End (ZMod 2) S)ˣ) ∈ Y :=
        hcentr _ hcD hcomm
      have hce : ((h⁻¹ * ⟨y, hyD⟩ : ↥(Y ⊔ A)) : (Module.End (ZMod 2) S)ˣ) =
          ((h : ↥(Y ⊔ A)) : (Module.End (ZMod 2) S)ˣ)⁻¹ * y := rfl
      have hhY : ((h : ↥(Y ⊔ A)) : (Module.End (ZMod 2) S)ˣ) ∈ Y := by
        have e : ((h : ↥(Y ⊔ A)) : (Module.End (ZMod 2) S)ˣ) =
            y * (((h⁻¹ * ⟨y, hyD⟩ : ↥(Y ⊔ A)) : (Module.End (ZMod 2) S)ˣ))⁻¹ := by
          rw [hce]; group
        rw [e]
        exact Y.mul_mem y.2 (Y.inv_mem hcY)
      have hz : (⟨_, hcY⟩ : ↥Y) ∈ Subgroup.center ↥Y := by
        rw [Subgroup.mem_center_iff]
        intro g
        exact Subtype.ext (hcomm g g.2).symm
      have hn : (⟨_, hhY⟩ : ↥Y) ∈ H.comap Y.subtype := Subgroup.mem_subgroupOf.1 hh
      have hyn : y = ⟨_, hhY⟩ * ⟨_, hcY⟩ := by
        apply Subtype.ext
        change (y : (Module.End (ZMod 2) S)ˣ) = _ * (_ : (Module.End (ZMod 2) S)ˣ)
        rw [hce]; group
      rw [hyn]
      exact Subgroup.mul_mem_sup hn hz
    have htop := eq_top_of_sup_center_eq_top hq hsup
    intro y hy
    have : (⟨y, hy⟩ : ↥Y) ∈ H.comap Y.subtype := by rw [htop]; trivial
    exact this
  have hCY : ∀ v : S, (∀ y ∈ Y, (y : Module.End (ZMod 2) S) v = v) → v = 0 := by
    let CY : Submodule (ZMod 2) S :=
      { carrier := {v | ∀ y ∈ Y, (y : Module.End (ZMod 2) S) v = v}
        add_mem' := fun {u v} hu hv y hy => by rw [map_add, hu y hy, hv y hy]
        zero_mem' := fun y _ => map_zero _
        smul_mem' := fun c v hv y hy => by rw [map_smul, hv y hy] }
    have hCYinv : ∀ d ∈ Y ⊔ A, ∀ v ∈ CY, (d : Module.End (ZMod 2) S) v ∈ CY := by
      intro d hd v hv y hy
      have h1 : d⁻¹ * y * d⁻¹⁻¹ ∈ Y :=
        (Subgroup.mem_normalizer_iff.1 (hDN ((Y ⊔ A).inv_mem hd)) y).1 hy
      have h2 := hv _ h1
      have e : (y : Module.End (ZMod 2) S) ((d : Module.End (ZMod 2) S) v) =
          (d : Module.End (ZMod 2) S) (((d⁻¹ * y * d⁻¹⁻¹ : (Module.End (ZMod 2) S)ˣ) :
            Module.End (ZMod 2) S) v) := by
        rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← Units.val_mul, ← Units.val_mul]
        congr 2
        group
      rw [e, h2]
    rcases hirr CY hCYinv with h | h
    · intro v hv
      have : v ∈ CY := hv
      rw [h] at this
      exact (Submodule.mem_bot _).1 this
    · exfalso
      obtain ⟨z, -, hz1⟩ := exists_mem_center_ne_one hZ
      apply hz1
      apply Subtype.ext
      apply Units.ext
      refine LinearMap.ext fun v => ?_
      have hv : v ∈ CY := by rw [h]; exact Submodule.mem_top
      exact hv z z.2
  refine ⟨r, m, hcardA' ▸ hcard, hr1, hr3, hmr, ?_⟩
  exact finrank_le_of_generation (fun i => ((t i : ↥Y) : (Module.End (ZMod 2) S)ˣ)) hgenY hCY

end Main

end CFSG.LocalAnalysis.RankThreeUC.S15.K534Proof
