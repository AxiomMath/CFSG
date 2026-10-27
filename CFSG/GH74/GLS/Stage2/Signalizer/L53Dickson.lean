module

public import CFSG.GH74.GLS.Stage2.Signalizer.L53Suzuki
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonTwoTransvectionsClassification

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.L53

open Subgroup Module
open scoped IsMulCommutative

variable {p : ℕ} [Fact p.Prime] {W : Type} [AddCommGroup W] [Module (ZMod p) W]

def klinSub (K : Type) [Semiring K] [Module K W] :
    Subgroup (LinearMap.GeneralLinearGroup (ZMod p) W) where
  carrier := {g | ∀ (k : K) (w : W), (g : Module.End (ZMod p) W) (k • w) =
    k • (g : Module.End (ZMod p) W) w}
  one_mem' := fun k w => rfl
  mul_mem' := by
    intro g g' hg hg' k w
    show (g : Module.End (ZMod p) W) ((g' : Module.End (ZMod p) W) (k • w)) =
      k • (g : Module.End (ZMod p) W) ((g' : Module.End (ZMod p) W) w)
    rw [hg', hg]
  inv_mem' := by
    intro g hg k w
    have h2 : ∀ v : W, (g : Module.End (ZMod p) W) (((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod p) W) :
        Module.End (ZMod p) W) v) = v := by
      intro v
      have h : ((g * g⁻¹ : LinearMap.GeneralLinearGroup (ZMod p) W) : Module.End (ZMod p) W) = 1 := by
        rw [mul_inv_cancel]; rfl
      rw [Units.val_mul] at h
      exact LinearMap.congr_fun h v
    have h3 : ∀ v : W, ((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod p) W) :
        Module.End (ZMod p) W) ((g : Module.End (ZMod p) W) v) = v := by
      intro v
      have h : ((g⁻¹ * g : LinearMap.GeneralLinearGroup (ZMod p) W) : Module.End (ZMod p) W) = 1 := by
        rw [inv_mul_cancel]; rfl
      rw [Units.val_mul] at h
      exact LinearMap.congr_fun h v
    have h1 := hg k (((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod p) W) :
        Module.End (ZMod p) W) w)
    rw [h2] at h1
    have h4 := congrArg (fun v => ((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod p) W) :
        Module.End (ZMod p) W) v) h1
    rw [h3] at h4
    exact h4.symm

@[expose] def repKer {J : Type} [Group J] (ρ : J →* Module.End (ZMod p) W) : Subgroup J :=
  ρ.toHomUnits.ker

theorem mem_repKer {J : Type} [Group J] {ρ : J →* Module.End (ZMod p) W} {j : J} :
    j ∈ repKer ρ ↔ ρ j = 1 := by
  unfold repKer
  rw [MonoidHom.mem_ker]
  exact ⟨fun h => by simpa using congrArg Units.val h, fun h => Units.ext h⟩

@[expose] def Sl2Quot (p : ℕ) (J : Type) [Group J] (C : Subgroup J) : Prop :=
  ∃ (N : Subgroup J) (_ : N.Normal), C ≤ N ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F),
    ((∃ n : ℕ, 1 ≤ n ∧ Nat.card F = p ^ n) ∨ (p = 3 ∧ Nat.card F = 5)) ∧
    Nonempty ((J ⧸ N) ≃* Matrix.SpecialLinearGroup (Fin 2) F)

theorem Sl2Quot.mono {J : Type} [Group J] {C C' : Subgroup J} (h : C ≤ C') {p : ℕ}
    (hC : Sl2Quot p J C') : Sl2Quot p J C := by
  obtain ⟨N, hN, hCN, F, hF, hFin, hcard, hiso⟩ := hC
  exact ⟨N, hN, h.trans hCN, F, hF, hFin, hcard, hiso⟩

theorem sl2_of_irreducible (hp2 : p ≠ 2) [Finite W] {J : Type} [Group J] (a b : J)
    (hgen : Subgroup.closure ({a, b} : Set J) = ⊤) (ρ : J →* Module.End (ZMod p) W)
    (h : SuzukiData (ρ a - 1) (ρ b - 1)) : Sl2Quot p J (repKer ρ) := by
  obtain ⟨K, hKf, hKa, hKm, hKfin, coord, r, hr0, hrk, hcomm, hna, hnb⟩ := suzuki_coord h
  let ρu : J →* LinearMap.GeneralLinearGroup (ZMod p) W := ρ.toHomUnits
  let H : Subgroup (LinearMap.GeneralLinearGroup (ZMod p) W) := ρu.range
  have hKlin : ρu.range ≤ klinSub (p := p) (W := W) K := by
    have hr : ρu.range = (Subgroup.closure ({a, b} : Set J)).map ρu := by
      rw [hgen, MonoidHom.range_eq_map]
    rw [hr, MonoidHom.map_closure, Subgroup.closure_le]
    rintro g ⟨j, hj, rfl⟩
    rcases hj with rfl | rfl
    · intro k w
      have hna' := (hcomm k w).1
      simp only [LinearMap.sub_apply, Module.End.one_apply, smul_sub] at hna'
      exact sub_left_inj.mp hna'
    · intro k w
      have hnb' := (hcomm k w).2
      simp only [LinearMap.sub_apply, Module.End.one_apply, smul_sub] at hnb'
      exact sub_left_inj.mp hnb'
  let f := ρu.rangeRestrict
  let x : ↥(ρu.range) := ⟨ρu a, ⟨a, rfl⟩⟩
  let y : ↥(ρu.range) := ⟨ρu b, ⟨b, rfl⟩⟩
  have hclos : Subgroup.closure ({x, y} : Set ↥(ρu.range)) = ⊤ := by
    have h1 : Subgroup.closure (f '' ({a, b} : Set J)) = ⊤ := by
      rw [← MonoidHom.map_closure, hgen, ← MonoidHom.range_eq_map]
      exact MonoidHom.range_eq_top.mpr (MonoidHom.rangeRestrict_surjective ρu)
    rw [Set.image_pair] at h1
    exact h1
  have hdick := CFSG.Glauberman.Dickson.two_transvections_classification (hpodd := hp2) (V := W)
    (H := ↥(ρu.range)) ρu.range.subtype Subtype.val_injective K
    (fun g k v => hKlin g.2 k v) coord r x y hrk hr0 hclos ?_ ?_
  · rcases hdick with he | ⟨hcard, he⟩
    · obtain ⟨e⟩ := he
      refine ⟨ρu.ker, inferInstance, le_rfl, K, hKf, hKfin, Or.inl ?_,
        ⟨(QuotientGroup.quotientKerEquivRange ρu).trans e⟩⟩
      have hp0 : Nat.card (ZMod p) = p := Nat.card_zmod p
      refine ⟨Module.finrank (ZMod p) K, ?_, ?_⟩
      · have : Module.Finite (ZMod p) K := Module.Finite.of_finite
        exact Module.finrank_pos
      · rw [Module.natCard_eq_pow_finrank (K := ZMod p) (V := K), hp0]
    · obtain ⟨e⟩ := he
      have hp3 : p = 3 := by
        have hdvd : p ∣ 9 := by
          rw [← hcard, Module.natCard_eq_pow_finrank (K := ZMod p) (V := K), Nat.card_zmod]
          have : Module.Finite (ZMod p) K := Module.Finite.of_finite
          exact dvd_pow_self p (Module.finrank_pos (R := ZMod p) (M := K)).ne'
        have h3 : p ∣ 3 := (Fact.out : p.Prime).dvd_of_dvd_pow (show p ∣ 3 ^ 2 by norm_num; exact hdvd)
        exact (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_three).mp h3
      have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
      exact ⟨ρu.ker, inferInstance, le_rfl, ZMod 5, inferInstance, inferInstance,
        Or.inr ⟨hp3, Nat.card_zmod 5⟩, ⟨(QuotientGroup.quotientKerEquivRange ρu).trans e⟩⟩
  · intro a' c
    show coord ((ρ a) (coord.symm (a', c))) = (a' + r * c, c)
    have hxa : (ρ a) (coord.symm (a', c)) =
        coord.symm (a', c) + (ρ a - 1) (coord.symm (a', c)) := by simp
    rw [hxa, map_add, LinearEquiv.apply_symm_apply, hna]
    simp [Prod.mk_add_mk]
  · intro a' c
    show coord ((ρ b) (coord.symm (a', c))) = (a', c + a')
    have hyb : (ρ b) (coord.symm (a', c)) =
        coord.symm (a', c) + (ρ b - 1) (coord.symm (a', c)) := by simp
    rw [hyb, map_add, LinearEquiv.apply_symm_apply, hnb]
    simp [Prod.mk_add_mk]

end CFSG.GH74.GLS.Stage2.Signalizer.L53
