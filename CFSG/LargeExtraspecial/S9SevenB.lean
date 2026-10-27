module

public import CFSG.LargeExtraspecial.S9SevenA

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem invariant_of_sup {A B : Subgroup S.O} {W : Submodule (ZMod 2) S.Qt}
    (hA : ∀ x ∈ A, ∀ w ∈ W, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ W)
    (hB : ∀ x ∈ B, ∀ w ∈ W, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ W) :
    ∀ x ∈ A ⊔ B, ∀ w ∈ W, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ W := by
  let K : Subgroup S.O :=
    { carrier := {x | ∀ w ∈ W, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ W ∧
        ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ W}
      mul_mem' := by
        intro x y hx hy w hw
        refine ⟨(hx _ (hy w hw).1).1, ?_⟩
        rw [mul_inv_rev]
        exact (hy _ (hx w hw).2).2
      one_mem' := fun w hw => ⟨hw, hw⟩
      inv_mem' := by
        intro x hx w hw
        refine ⟨(hx w hw).2, ?_⟩
        rw [inv_inv]
        exact (hx w hw).1 }
  have hAK : A ≤ K := fun x hx w hw => ⟨hA x hx w hw, hA _ (inv_mem hx) w hw⟩
  have hBK : B ≤ K := fun x hx w hw => ⟨hB x hx w hw, hB _ (inv_mem hx) w hw⟩
  intro x hx w hw
  exact ((sup_le hAK hBK) hx w hw).1

variable (H : Hyp4 S g) (C : Cons311 S g) (k : S.M)
include H C

omit C in
theorem Ut_mul_eq {X : Subgroup S.O} (hLX : S.Lbar g ≤ X)
    (hLbX : S.Lbar ((k : G) * g) ≤ X) : Ut S ((k : G) * g) X = Ut S g X := by
  have hU0 : ∀ (g' : G) (H' : Hyp4 S g'), Ut S g' X ≠ ⊥ := fun g' H' h0 =>
    cl_conj_z_ne_zero S H'.conj_mem H'.conj_ne ((Submodule.mem_bot _).mp (h0 ▸ cl_mem_Ut X))
  refine le_antisymm (Ut_le_of_invariant (H.mul k) hLbX (fun x hx w hw => apply_mem_Ut hx hw)
    (hU0 g H)) (Ut_le_of_invariant H hLX (fun x hx w hw => apply_mem_Ut hx hw)
    (hU0 _ (H.mul k)))

theorem Ut_le_sup_or_fix {P : Subgroup S.O} (hPX : P ≤ S.Lbar g ⊔ S.Lbar ((k : G) * g))
    (hPn : ∀ x ∈ S.Lbar g ⊔ S.Lbar ((k : G) * g), ∀ p ∈ P, x * p * x⁻¹ ∈ P)
    (hP2 : IsPGroup 2 P) (hLP : S.Lbar g ⊓ P ≠ ⊥) :
    Ut S g (S.Lbar g ⊔ S.Lbar ((k : G) * g)) ≤
        Ut S g (S.Lbar g ⊔ S.Lbar ((k : G) * g)) ⊓ S.clSub (S.QG ⊓ S.Qa g) ⊔
          Ut S g (S.Lbar g ⊔ S.Lbar ((k : G) * g)) ⊓ S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) ∨
      ∀ x ∈ S.Lbar g ⊔ S.Lbar ((k : G) * g), ∀ u ∈ Ut S g (S.Lbar g ⊔ S.Lbar ((k : G) * g)),
        (x : S.Qt ≃ₗ[ZMod 2] S.Qt) u = u := by
  set X := S.Lbar g ⊔ S.Lbar ((k : G) * g) with hX
  have hLX : S.Lbar g ≤ X := le_sup_left
  have hLbX : S.Lbar ((k : G) * g) ≤ X := le_sup_right
  have hiso : ∀ u ∈ Ut S g X, ∀ v ∈ Ut S g X, polar S.q u v = 0 :=
    fun u hu v hv => polar_eq_zero_of_mem_Ut H C hLX hPX hPn hP2 hLP hu hv
  have hUeq := Ut_mul_eq H k hLX hLbX
  have hisob : ∀ u ∈ Ut S ((k : G) * g) X, ∀ v ∈ Ut S ((k : G) * g) X, polar S.q u v = 0 := by
    rw [hUeq]; exact hiso
  set W := Submodule.span (ZMod 2) {v | ∃ l : S.O, (l ∈ S.Lbar g ∨ l ∈ S.Lbar ((k : G) * g)) ∧
    ∃ u ∈ Ut S g X, (l : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u = v} with hW
  have hWU : W ≤ Ut S g X := by
    rw [hW, Submodule.span_le]
    rintro _ ⟨l, hl, u, hu, rfl⟩
    have hlX : l ∈ X := hl.elim (fun h => hLX h) (fun h => hLbX h)
    exact sub_mem (apply_mem_Ut hlX hu) hu
  have hgen : ∀ l, (l ∈ S.Lbar g ∨ l ∈ S.Lbar ((k : G) * g)) → ∀ w ∈ W,
      (l : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ W := by
    intro l hl w hw
    have e : (l : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w + ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) := by abel
    rw [e]
    exact add_mem hw (Submodule.subset_span ⟨l, hl, w, hWU hw, rfl⟩)
  have hWinv := invariant_of_sup (fun x hx w hw => hgen x (Or.inl hx) w hw)
    (fun x hx w hw => hgen x (Or.inr hx) w hw)
  by_cases hW0 : W = ⊥
  · right
    intro x hx u hu
    have hfix : ∀ l, (l ∈ S.Lbar g ∨ l ∈ S.Lbar ((k : G) * g)) → ∀ v ∈ Ut S g X,
        (l : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
      intro l hl v hv
      have hmem : (l : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ W :=
        Submodule.subset_span ⟨l, hl, v, hv, rfl⟩
      rw [hW0, Submodule.mem_bot, sub_eq_zero] at hmem
      exact hmem
    have hF := invariant_of_sup (W := Ut S g X ⊓ fixSub S X)
      (fun y hy w hw => by
        obtain ⟨hwU, hwF⟩ := Submodule.mem_inf.mp hw
        rw [hfix y (Or.inl hy) w hwU]
        exact hw)
      (fun y hy w hw => by
        obtain ⟨hwU, hwF⟩ := Submodule.mem_inf.mp hw
        rw [hfix y (Or.inr hy) w hwU]
        exact hw)
    have hla : ∀ y ∈ X, (y : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
        S.cl (g * S.z * g⁻¹) := by
      let K : Subgroup S.O :=
        { carrier := {y | (y : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
            S.cl (g * S.z * g⁻¹)}
          mul_mem' := fun {y z} hy hz => by
            change (y : S.Qt ≃ₗ[ZMod 2] S.Qt) ((z : S.Qt ≃ₗ[ZMod 2] S.Qt) _) = _
            rw [hz, hy]
          one_mem' := rfl
          inv_mem' := fun {y} hy => by
            change ((y⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) _ = _
            conv_lhs => rw [← hy]
            exact inv_apply_apply_O y _ }
      have hLK : S.Lbar g ≤ K := fun y hy => hfix y (Or.inl hy) _ (cl_mem_Ut X)
      have hLbK : S.Lbar ((k : G) * g) ≤ K := fun y hy => hfix y (Or.inr hy) _ (cl_mem_Ut X)
      exact fun y hy => sup_le hLK hLbK hy
    have hspan : Ut S g X ≤ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) := by
      rw [Ut, Submodule.span_le]
      rintro _ ⟨y, hy, rfl⟩
      rw [hla y hy]
      exact Submodule.mem_span_singleton_self _
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp (hspan hu)
    rw [map_smul, hla x hx]
  · left
    have hle := Ut_le_of_invariant H hLX hWinv hW0
    refine hle.trans ?_
    rw [hW, Submodule.span_le]
    rintro _ ⟨l, hl, u, hu, rfl⟩
    rcases hl with hl | hl
    · exact Submodule.mem_sup_left (apply_sub_mem_Ut_inf_clSub H C hLX hiso hl hu)
    · have hu' : u ∈ Ut S ((k : G) * g) X := by rw [hUeq]; exact hu
      have := apply_sub_mem_Ut_inf_clSub (H.mul k) (C.mul k) hLbX hisob hl hu'
      rw [hUeq] at this
      exact Submodule.mem_sup_right this

theorem card_mul_card_mul_two_pow_finrank_Ut_le {P : Subgroup S.O}
    (hPX : P ≤ S.Lbar g ⊔ S.Lbar ((k : G) * g))
    (hPn : ∀ x ∈ S.Lbar g ⊔ S.Lbar ((k : G) * g), ∀ p ∈ P, x * p * x⁻¹ ∈ P)
    (hP2 : IsPGroup 2 P) (hLP : S.Lbar g ⊓ P ≠ ⊥) :
    Nat.card (S.Lbar g ⊓ P : Subgroup S.O) * Nat.card (S.Lbar ((k : G) * g) ⊓ P : Subgroup S.O) *
      2 ^ finrank (ZMod 2) ↥(Ut S g (S.Lbar g ⊔ S.Lbar ((k : G) * g))) ≤
        2 ^ S.width * 2 ^ S.width := by
  set X := S.Lbar g ⊔ S.Lbar ((k : G) * g) with hX
  have hLX : S.Lbar g ≤ X := le_sup_left
  have hLbX : S.Lbar ((k : G) * g) ≤ X := le_sup_right
  have hUeq := Ut_mul_eq H k hLX hLbX
  have ha := card_inf_mul_two_pow_le H C hLX hPX hPn hP2
  have hb := card_inf_mul_two_pow_le (H.mul k) (C.mul k) hLbX hPX hPn hP2
  rw [hUeq] at hb
  have hLc := C.card_Lbar
  have hLbc := (C.mul k).card_Lbar
  have hca := Subgroup.card_le_of_le (inf_le_left : S.Lbar g ⊓ P ≤ S.Lbar g)
  have hcb := Subgroup.card_le_of_le
    (inf_le_left : S.Lbar ((k : G) * g) ⊓ P ≤ S.Lbar ((k : G) * g))
  rcases Ut_le_sup_or_fix H C k hPX hPn hP2 hLP with hle | hfix
  · rw [← hX] at hle
    have h1 := Submodule.finrank_mono hle
    have h2 := Submodule.finrank_sup_add_finrank_inf_eq
      (Ut S g X ⊓ S.clSub (S.QG ⊓ S.Qa g)) (Ut S g X ⊓ S.clSub (S.QG ⊓ S.Qa ((k : G) * g)))
    have h3 : 2 ^ finrank (ZMod 2) ↥(Ut S g X) ≤
        2 ^ finrank (ZMod 2) ↥(Ut S g X ⊓ S.clSub (S.QG ⊓ S.Qa g)) *
          2 ^ finrank (ZMod 2) ↥(Ut S g X ⊓ S.clSub (S.QG ⊓ S.Qa ((k : G) * g))) := by
      rw [← pow_add]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    calc Nat.card (S.Lbar g ⊓ P : Subgroup S.O) *
          Nat.card (S.Lbar ((k : G) * g) ⊓ P : Subgroup S.O) * 2 ^ finrank (ZMod 2) ↥(Ut S g X)
        ≤ Nat.card (S.Lbar g ⊓ P : Subgroup S.O) *
          Nat.card (S.Lbar ((k : G) * g) ⊓ P : Subgroup S.O) *
          (2 ^ finrank (ZMod 2) ↥(Ut S g X ⊓ S.clSub (S.QG ⊓ S.Qa g)) *
            2 ^ finrank (ZMod 2) ↥(Ut S g X ⊓ S.clSub (S.QG ⊓ S.Qa ((k : G) * g)))) :=
          Nat.mul_le_mul_left _ h3
      _ = (Nat.card (S.Lbar g ⊓ P : Subgroup S.O) *
            2 ^ finrank (ZMod 2) ↥(Ut S g X ⊓ S.clSub (S.QG ⊓ S.Qa g))) *
          (Nat.card (S.Lbar ((k : G) * g) ⊓ P : Subgroup S.O) *
            2 ^ finrank (ZMod 2) ↥(Ut S g X ⊓ S.clSub (S.QG ⊓ S.Qa ((k : G) * g)))) := by ring
      _ ≤ 2 ^ S.width * 2 ^ S.width := Nat.mul_le_mul ha hb
  ·
    rw [← hX] at hfix
    have hle : Ut S g X ≤ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) := by
      rw [Ut, Submodule.span_le]
      rintro _ ⟨y, hy, rfl⟩
      rw [hfix y hy _ (cl_mem_Ut X)]
      exact Submodule.mem_span_singleton_self _
    have h1 := Submodule.finrank_mono hle
    have h2 := finrank_span_singleton (K := ZMod 2) (cl_conj_z_ne_zero S H.conj_mem H.conj_ne)
    have h3 : 2 ^ finrank (ZMod 2) ↥(Ut S g X) ≤ 2 := by
      calc 2 ^ finrank (ZMod 2) ↥(Ut S g X) ≤ 2 ^ 1 :=
            Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 2 := by norm_num
    have hn : 1 ≤ S.width := by have := H.two_lt_width; omega
    have h4 : 2 ^ (S.width - 1) * 2 ^ (S.width - 1) * 2 ≤ 2 ^ S.width * 2 ^ S.width := by
      have e : 2 ^ S.width = 2 ^ (S.width - 1) * 2 := by
        rw [← pow_succ]; congr 1; omega
      rw [e]
      nlinarith [Nat.one_le_two_pow (n := S.width - 1)]
    calc Nat.card (S.Lbar g ⊓ P : Subgroup S.O) *
          Nat.card (S.Lbar ((k : G) * g) ⊓ P : Subgroup S.O) * 2 ^ finrank (ZMod 2) ↥(Ut S g X)
        ≤ 2 ^ (S.width - 1) * 2 ^ (S.width - 1) * 2 := by
          rw [hLc] at hca
          rw [hLbc] at hcb
          exact Nat.mul_le_mul (Nat.mul_le_mul hca hcb) h3
      _ ≤ 2 ^ S.width * 2 ^ S.width := h4

end CFSG.LargeExtraspecial.S9
