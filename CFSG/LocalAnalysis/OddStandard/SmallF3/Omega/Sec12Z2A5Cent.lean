module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Z2A5Basic
public import CFSG.LocalAnalysis.SeitzReduction.Inheritance
public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.SL2Alt5

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {Y : Type} [Group Y] {τ : Y}

theorem z2a5_sl24 (h : Z2A5Hyp Y τ) :
    ∃ (k : Type) (_ : Field k) (_ : Fintype k), Fintype.card k = 2 ^ 2 ∧
      Nonempty (↥(oTwoRes (centralizer ({τ} : Set Y))) ≃* Matrix.SpecialLinearGroup (Fin 2) k) := by
  let k := GaloisField 2 2
  letI : Field k := inferInstance
  letI : Fintype k := Fintype.ofFinite k
  refine ⟨k, inferInstance, inferInstance, ?_, ?_⟩
  · rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 2 (by norm_num)
  · obtain ⟨e₁⟩ := z2a5_X_equiv h
    obtain ⟨e₂⟩ := CFSG.CGT.PushingUpLit.CGT6.sl2_four_equiv_alt5
    exact ⟨e₁.trans e₂.symm⟩

theorem z2a5_cent_rank [Finite Y] (h : Z2A5Hyp Y τ) :
    ∀ P : Subgroup Y, P ≤ centralizer (oTwoRes (centralizer ({τ} : Set Y)) : Set Y) →
      IsPGroup 2 P → Nat.card P ≤ 2 := by
  intro P hP hPg
  refine CFSG.SeitzReduction.card_le_two_of_forall_le_inf_centralizer
    (K := centralizer (oTwoRes (centralizer ({τ} : Set Y)) : Set Y)) (t := τ)
    (z2a5_mem_cent h) h.1 (fun U _ hUK => ?_) hPg hP
  have hUsub : U ≤ zpowers τ := by
    intro u hu
    have huK : u ∈ centralizer (oTwoRes (centralizer ({τ} : Set Y)) : Set Y) := (hUK hu).1
    have huC : u ∈ centralizer ({τ} : Set Y) := (hUK hu).2
    rcases z2a5_cent_cent h huC (fun x hx => (mem_centralizer_iff.1 huK x hx).symm) with h1 | hτ
    · rw [h1]; exact one_mem _
    · rw [hτ]; exact mem_zpowers τ
  calc Nat.card U ≤ Nat.card (zpowers τ) := Subgroup.card_le_of_le hUsub
    _ = orderOf τ := Nat.card_zpowers τ
    _ = 2 := h.1

theorem z2a5_center (h : Z2A5Hyp Y τ) : center Y = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  have hzC : z ∈ centralizer ({τ} : Set Y) := by
    rw [mem_centralizer_singleton_iff]
    exact (Subgroup.mem_center_iff.1 hz τ).symm
  have hzX : ∀ x ∈ oTwoRes (centralizer ({τ} : Set Y)), z * x = x * z :=
    fun x _ => ((Subgroup.mem_center_iff.1 hz) x).symm
  rcases z2a5_cent_cent h hzC hzX with h1 | hτ
  · exact h1
  · exfalso
    have hzτ : τ ∈ center Y := hτ ▸ hz
    obtain ⟨x, hxX, hxord⟩ := z2a5_exists_inv h
    have hcomm : x * τ = τ * x := mem_centralizer_iff.1 (z2a5_mem_cent h) x hxX
    have hxx : x * x = 1 := by
      have h2 := pow_orderOf_eq_one x
      rw [hxord] at h2
      simpa [pow_two] using h2
    set y : Y := τ * x with hy
    have hyy : y * y = 1 := by
      rw [hy]
      calc τ * x * (τ * x) = τ * (x * τ) * x := by group
        _ = τ * (τ * x) * x := by rw [hcomm]
        _ = (τ * τ) * (x * x) := by group
        _ = 1 := by rw [z2a5_mul_self h, hxx, one_mul]
    have hmem := (h.2.2 y).mpr ⟨x, hxX, hy, hyy⟩
    have hyconj : ∃ g : Y, g ∈ (⊤ : Subgroup Y) ∧ y = g * τ * g⁻¹ := hmem.1
    obtain ⟨g, -, hg⟩ := hyconj
    have hyτ : y = τ := by
      rw [hg, Subgroup.mem_center_iff.1 hzτ g]
      group
    have hx1 : x = 1 := by
      apply mul_left_cancel (a := τ)
      rw [← hy, hyτ, mul_one]
    have hxne : x ≠ 1 := by
      intro hx1'
      rw [hx1', orderOf_one] at hxord
      norm_num at hxord
    exact hxne hx1

theorem z2a5_zstar (h : Z2A5Hyp Y τ) (hO : oddCore Y = ⊥) : CFSG.Open.fusionZStar Y = ⊥ := by
  unfold CFSG.Open.fusionZStar
  have hcore : CFSG.Open.fusionOddCore Y = CFSG.oddCore Y := rfl
  have hbot : CFSG.Open.fusionOddCore Y = (⊥ : Subgroup Y) := by rw [hcore, hO]
  let e : (Y ⧸ CFSG.Open.fusionOddCore Y) ≃* Y :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans
      (QuotientGroup.quotientBot : (Y ⧸ (⊥ : Subgroup Y)) ≃* Y)
  have hcen : Subgroup.center (Y ⧸ CFSG.Open.fusionOddCore Y) = ⊥ := by
    have hmap := Subgroup.map_center_eq e
    rw [z2a5_center h] at hmap
    rw [Subgroup.map_eq_bot_iff] at hmap
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hx1 : (e : (Y ⧸ CFSG.Open.fusionOddCore Y) →* Y) x = 1 := by
      simpa using (hmap hx)
    exact e.injective (by simpa using hx1)
  rw [hcen, MonoidHom.comap_bot, QuotientGroup.ker_mk', hbot]

end CFSG.OddStandard.SmallF3.Omega
