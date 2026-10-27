module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S25FW1
public import CFSG.ClassicalInvolution.AschTight.Hall196Lift
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.ClassicalInvolution.Hat2A7

open Equiv Equiv.Perm CFSG.GorensteinWalter
open scoped MatrixGroups

section PSL

theorem nonempty_mulEquiv_alternatingGroup_five_of_simple {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] (hG : Nat.card G = 60) : Nonempty (G ≃* alternatingGroup (Fin 5)) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨P⟩ : Nonempty (Sylow 5 G) := inferInstance
  have hP : Nat.card P = 5 := by
    rw [Sylow.card_eq_multiplicity, hG, show (60 : ℕ) = 5 * 12 by rfl,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_self (by norm_num),
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    norm_num
  have hnot_normal : ¬ (P : Subgroup G).Normal := fun hN => by
    rcases hN.eq_bot_or_eq_top with h | h
    · rw [h, Subgroup.card_bot] at hP
      omega
    · rw [h, Subgroup.card_top, hG] at hP
      omega
  have hcard : Nat.card (Sylow 5 G) = 6 := by
    have hmod := card_sylow_modEq_one 5 G
    have hdvd : Nat.card (Sylow 5 G) ∣ 12 := by
      have h := P.card_dvd_index
      rwa [(P : Subgroup G).index_eq_card, show Nat.card (G ⧸ (P : Subgroup G)) = 12 by
        have := (P : Subgroup G).card_mul_index
        rw [hP, hG, (P : Subgroup G).index_eq_card] at this
        omega] at h
    have hpos : 0 < Nat.card (Sylow 5 G) := Nat.card_pos
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    have hne1 : Nat.card (Sylow 5 G) ≠ 1 := fun h1 => by
      have : Subsingleton (Sylow 5 G) := (Nat.card_eq_one_iff_unique.mp h1).1
      exact hnot_normal (Sylow.normal_of_subsingleton P)
    unfold Nat.ModEq at hmod
    interval_cases h : Nat.card (Sylow 5 G) <;> simp_all
  have hfaithful : FaithfulSMul G (Sylow 5 G) := by
    let φ := MulAction.toPermHom G (Sylow 5 G)
    rcases (MonoidHom.normal_ker φ).eq_bot_or_eq_top with hk | hk
    · refine ⟨fun {g h} hgh => ?_⟩
      have : φ g = φ h := Equiv.ext hgh
      exact (MonoidHom.ker_eq_bot_iff φ).mp hk this
    · refine absurd ?_ hnot_normal
      rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff]
      intro g _
      have hg : g ∈ φ.ker := hk ▸ Subgroup.mem_top g
      exact Sylow.smul_eq_iff_mem_normalizer.mp
        (congrArg (fun σ : Equiv.Perm (Sylow 5 G) => σ P) hg)
  exact CFSG.Glauberman.Dickson.huppert_II_8_25_transitive_degree_six_order_sixty
    (Ω := Sylow 5 G) inferInstance hcard hG

theorem natCard_psl2_of_card_eq_five {k : Type} [Field k] [Finite k] (h5 : Nat.card k = 5) :
    Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) k) = 60 := by
  let _ := Fintype.ofFinite k
  let _ : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let _ : Fact (2 < 5) := ⟨by norm_num⟩
  let _ : CharP k 5 := charP_of_card_eq_prime_pow (p := 5) (f := 1) (by
    rw [← Nat.card_eq_fintype_card, h5, pow_one])
  have hcenter := CFSG.BenderSuzuki.External.huppert614_card_center_of_neg_one_ne_one (K := k)
    (CharP.neg_one_ne_one k 5)
  have hcard := CFSG.BenderSuzuki.External.huppert614_card_psl_mul_center (K := k)
  rw [h5, hcenter] at hcard
  norm_num at hcard
  omega

theorem nonempty_psl2_equiv_alternating_five {k : Type} [Field k] [Finite k]
    (h5 : Nat.card k = 5) : Nonempty (PSL2 k ≃* alternatingGroup (Fin 5)) := by
  rcases CFSG.BenderSuzuki.External.huppert_blackburn_XI_example_1_3_a k with
    ⟨_, _, _, _, _, _, _, _, _, _, hlarge, _, _⟩
  have : IsSimpleGroup (PSL2 k) := (hlarge (by omega)).1
  exact nonempty_mulEquiv_alternatingGroup_five_of_simple (natCard_psl2_of_card_eq_five h5)

theorem nonempty_psl2_equiv_alternating_four {k : Type} [Field k] [Finite k]
    (h3 : Nat.card k = 3) : Nonempty (PSL2 k ≃* alternatingGroup (Fin 4)) := by
  have : Fintype k := Fintype.ofFinite k
  let eK : ZMod 3 ≃+* k :=
    ZMod.ringEquivOfPrime k Nat.prime_three (by simpa [Nat.card_eq_fintype_card] using h3)
  exact ⟨(psl2RingEquiv eK).symm.trans psl2_three_equiv_alternatingGroup⟩

end PSL

section Fixed

variable {E : Type} [Group E] [Finite E] {π : E →* A7} {z : E}


theorem nonempty_fixedIn_equiv_sl2 {k : Type} [Field k] [Finite k] (hk : ringChar k ≠ 2)
    (h : IsDoubleCoverA7 π z) (α : MulAut E) (e : ↥((fixedIn α ⊤).map π) ≃* PSL2 k) :
    Nonempty (↥(fixedIn α ⊤) ≃* SL(2, k)) := by
  set F : Subgroup E := fixedIn α ⊤ with hF
  have hzF : z ∈ F := ⟨trivial, h.mulAut_apply_z α⟩
  let z' : ↥F := ⟨z, hzF⟩
  let r : ↥F →* ↥(F.map π) :=
    (π.comp F.subtype).codRestrict (F.map π) (fun x => ⟨x, x.2, rfl⟩)
  have hr : Function.Surjective r := by
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  let ρ : ↥F →* PSL2 k := e.toMonoidHom.comp r
  have hρ : Function.Surjective ρ := e.surjective.comp hr
  have hz2 : z' * z' = 1 := Subtype.ext h.sq_eq_one
  have hz'1 : z' ≠ 1 := fun h1 => h.ne_one (congrArg Subtype.val h1)
  have hord : orderOf z' = 2 := orderOf_eq_prime (by rw [sq]; exact hz2) hz'1
  have hrz : r z' = 1 := Subtype.ext ((h.ker_iff z).mpr (Or.inr rfl))
  have hker : ρ.ker = Subgroup.zpowers z' := by
    ext x
    constructor
    · intro hx
      have hx1 : ρ x = 1 := hx
      have hrx : r x = 1 := e.injective (by rw [map_one]; exact hx1)
      have hπx : π x = 1 := congrArg (fun y : ↥(F.map π) => (y : A7)) hrx
      rcases (h.ker_iff x).mp hπx with h1 | h1
      · have : x = 1 := Subtype.ext h1
        rw [this]
        exact one_mem _
      · have : x = z' := Subtype.ext h1
        rw [this]
        exact Subgroup.mem_zpowers z'
    · intro hx
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      rw [MonoidHom.mem_ker, map_zpow, show ρ z' = 1 by
        show e (r z') = 1
        rw [hrz, map_one], one_zpow]
  have huniq : ∀ t : ↥F, orderOf t = 2 → t = z' := by
    intro t ht
    have ht2 : (t : E) * t = 1 := by
      have := pow_orderOf_eq_one t
      rw [ht, sq] at this
      exact congrArg Subtype.val this
    rcases h.eq_one_or_eq_z_of_sq_eq_one ht2 with h1 | h1
    · exfalso
      have : t = 1 := Subtype.ext h1
      rw [this, orderOf_one] at ht
      omega
    · exact Subtype.ext h1
  exact CFSG.ClassicalInvolution.Disconnected.AschTight.Hall196.nonempty_mulEquiv_sl2_of_ker hk ρ
    hρ hker hord huniq

theorem nonempty_fixedIn_equiv_sl2_five [Fact (Nat.Prime 5)] (h : IsDoubleCoverA7 π z)
    (α : MulAut E) (hα : α * α = 1) (hne : α ≠ 1) (hc : (h.autPerm α).cycleType = {2}) :
    Nonempty (↥(fixedIn α ⊤) ≃* SL(2, GaloisField 5 1)) := by
  obtain ⟨e₁⟩ := nonempty_image_equiv_alternating_five h α hα hne hc
  have hcard : Nat.card (GaloisField 5 1) = 5 := by
    rw [GaloisField.card 5 1 (by norm_num)]
    norm_num
  obtain ⟨e₂⟩ := nonempty_psl2_equiv_alternating_five (k := GaloisField 5 1) hcard
  exact nonempty_fixedIn_equiv_sl2 (by rw [ringChar.eq (GaloisField 5 1) 5]; norm_num) h α
    (e₁.trans e₂.symm)

theorem nonempty_fixedIn_equiv_sl2_three (h : IsDoubleCoverA7 π z) (α : MulAut E)
    (hα : α * α = 1) (hne : α ≠ 1) (hc : (h.autPerm α).cycleType = {2, 2, 2}) :
    Nonempty (↥(fixedIn α ⊤) ≃* SL(2, GaloisField 3 1)) := by
  obtain ⟨e₁⟩ := nonempty_image_equiv_alternating_four h α hα hne hc
  have hcard : Nat.card (GaloisField 3 1) = 3 := by
    rw [GaloisField.card 3 1 (by norm_num)]
    norm_num
  obtain ⟨e₂⟩ := nonempty_psl2_equiv_alternating_four (k := GaloisField 3 1) hcard
  exact nonempty_fixedIn_equiv_sl2 (by rw [ringChar.eq (GaloisField 3 1) 3]; norm_num) h α
    (e₁.trans e₂.symm)

end Fixed

end CFSG.ClassicalInvolution.Hat2A7
