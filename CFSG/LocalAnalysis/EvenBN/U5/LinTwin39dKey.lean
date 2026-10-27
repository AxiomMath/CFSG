module

public import CFSG.LocalAnalysis.EvenBN.U5.Sec3ProofNineD
public import CFSG.LocalAnalysis.EvenBN.LinearThree.ModelRadicals

public section

namespace CFSG.LocalAnalysis.EvenBN.U5

namespace LinCase

open Subgroup CFSG.LocalAnalysis.EvenBN.LinearThree
open CFSG.Open (IsElemAbelian)
open scoped commutatorElement

@[expose] def lin39dImg {G : Type*} [Group G] (S E R X : Subgroup G)
    (hEn : ∀ s ∈ S, ∀ e ∈ E, s * e * s⁻¹ ∈ E) (hRS : R ≤ S) : Subgroup G where
  carrier := {y | y ∈ R ∧ ∃ e ∈ E, e * y ∈ X}
  mul_mem' := by
    rintro y₁ y₂ ⟨hy₁, e₁, he₁, hX₁⟩ ⟨hy₂, e₂, he₂, hX₂⟩
    refine ⟨mul_mem hy₁ hy₂, e₁ * (y₁ * e₂ * y₁⁻¹),
      mul_mem he₁ (hEn y₁ (hRS hy₁) e₂ he₂), ?_⟩
    have : e₁ * (y₁ * e₂ * y₁⁻¹) * (y₁ * y₂) = (e₁ * y₁) * (e₂ * y₂) := by group
    rw [this]
    exact mul_mem hX₁ hX₂
  one_mem' := ⟨one_mem R, 1, one_mem E, by simpa using one_mem X⟩
  inv_mem' := by
    rintro y ⟨hy, e, he, hX⟩
    refine ⟨inv_mem hy, y⁻¹ * e⁻¹ * y, ?_, ?_⟩
    · have := hEn y⁻¹ (inv_mem (hRS hy)) e⁻¹ (inv_mem he)
      simpa using this
    · have : y⁻¹ * e⁻¹ * y * y⁻¹ = (e * y)⁻¹ := by group
      rw [this]
      exact inv_mem hX

theorem lin39d_mul_eq {a b A B : ℕ} (ha : a ≤ A) (hb : b ≤ B) (hA : 0 < A) (hB : 0 < B)
    (h : A * B ≤ a * b) : a = A ∧ b = B := by
  constructor
  · by_contra hne
    have hlt : a < A := lt_of_le_of_ne ha hne
    have h1 : a * b ≤ a * B := Nat.mul_le_mul_left a hb
    have h2 : a * B < A * B := Nat.mul_lt_mul_of_pos_right hlt hB
    omega
  · by_contra hne
    have hlt : b < B := lt_of_le_of_ne hb hne
    have h1 : a * b ≤ A * b := Nat.mul_le_mul_right b ha
    have h2 : A * b < A * B := Nat.mul_lt_mul_of_pos_left hlt hA
    omega

section Key

variable {G : Type*} [Group G]

@[expose] def lin39dCentSub (S V C : Subgroup G) (hVS : ∀ v ∈ V, ∀ s ∈ S, v * s = s * v) :
    Subgroup G where
  carrier := {y | y ∈ S ∧ ∀ u ∈ C, ⁅u, y⁆ ∈ V}
  mul_mem' := by
    rintro y₁ y₂ ⟨hy₁S, hy₁⟩ ⟨hy₂S, hy₂⟩
    refine ⟨mul_mem hy₁S hy₂S, fun u hu => ?_⟩
    have hc : y₁ * ⁅u, y₂⁆ * y₁⁻¹ = ⁅u, y₂⁆ := by
      rw [← hVS _ (hy₂ u hu) y₁ hy₁S]
      group
    rw [sec39d_key_comm_mul, hc]
    exact mul_mem (hy₁ u hu) (hy₂ u hu)
  one_mem' := ⟨one_mem S, fun u _ => by simpa using one_mem V⟩
  inv_mem' := by
    rintro y ⟨hyS, hy⟩
    refine ⟨inv_mem hyS, fun u hu => ?_⟩
    have hv := hy u hu
    have e : ⁅u, y⁻¹⁆ = y⁻¹ * ⁅u, y⁆⁻¹ * y := by
      simp only [commutatorElement_def]
      group
    have hc : y⁻¹ * ⁅u, y⁆⁻¹ * y = ⁅u, y⁆⁻¹ := by
      have h1 := hVS _ (inv_mem hv) y hyS
      calc y⁻¹ * ⁅u, y⁆⁻¹ * y = y⁻¹ * (⁅u, y⁆⁻¹ * y) := by group
        _ = y⁻¹ * (y * ⁅u, y⁆⁻¹) := by rw [h1]
        _ = ⁅u, y⁆⁻¹ := by group
    rw [e, hc]
    exact inv_mem hv

end Key

section Key2

variable {G : Type*} [Group G] [Finite G]

theorem lin39d_exists_ne_one {H : Subgroup G} (h : 1 < Nat.card H) : ∃ z ∈ H, z ≠ 1 := by
  by_contra hno
  push Not at hno
  have : H = ⊥ := (Subgroup.eq_bot_iff_forall H).2 hno
  rw [this, Subgroup.card_bot] at h
  omega

theorem lin39d_key_case (q : ℕ) (hq : 2 ≤ q) (S E V R R' R'' W : Subgroup G) (t : G)
    (hVS : ∀ v ∈ V, ∀ s ∈ S, v * s = s * v) (hVE : V ≤ E) (hES : E ≤ S)
    (hEn : ∀ s ∈ S, ∀ e ∈ E, s * e * s⁻¹ ∈ E) (hE2 : ∀ x ∈ E, ∀ y ∈ E, ⁅x, y⁆ ∈ V)
    (hRS : R ≤ S) (hdec : ∀ s ∈ S, ∃ e ∈ E, ∃ y ∈ R, s = e * y)
    (hER : ∀ x ∈ E, x ∈ R → x = 1) (htE : ∀ e ∈ E, t * e * t⁻¹ ∈ E)
    (htV : ∀ v ∈ V, t * v * t⁻¹ ∈ V) (hR'R : R' ≤ R) (hR''R : R'' ≤ R) (hRR : R' ⊔ R'' = R)
    (hcardR' : Nat.card R' = (q ^ 2) ^ 2) (hel' : ∀ x ∈ R', x * x = 1)
    (hz : ∃ z ∈ R' ⊓ R'', z ≠ 1) (hconj : R'.map (MulAut.conj t).toMonoidHom = R'')
    (hH4 : ∀ y ∈ R, y ≠ 1 → y * y = 1 →
      Nat.card (sec39dECent V E (fun v hv e he => hVS v hv e (hES he)) y) ≤ q ^ 10)
    (hW : ∀ u ∈ E, (∀ s ∈ S, ⁅u, s⁆ ∈ V) → u ∈ W) (hcardW : Nat.card W < q ^ 10)
    (X : Subgroup G) (hXS : X ≤ S) (hX2 : ∀ x ∈ X, x * x ∈ V)
    (hX3 : ∀ x ∈ X, ∀ y ∈ X, ⁅x, y⁆ ∈ V) (hcardX : q ^ 14 ≤ Nat.card X)
    (hYR' : ∀ y ∈ R, ∀ e ∈ E, e * y ∈ X → y ∈ R')
    (hnt : ∃ y ∈ R, y ≠ 1 ∧ ∃ e ∈ E, e * y ∈ X) : False := by
  have hV : ∀ v ∈ V, ∀ e ∈ E, v * e = e * v := fun v hv e he => hVS v hv e (hES he)
  have hsq : ∀ y ∈ R, ∀ e ∈ E, e * y ∈ X → y * y = 1 := fun y hy e he hX =>
    sec39d_key_A_inv hVE hEn hRS hER hX2 hy he hX
  obtain ⟨y₁, hy₁R, hy₁1, e₁, he₁, hX₁⟩ := hnt
  have hinf1 : Nat.card (X ⊓ E : Subgroup G) ≤ q ^ 10 :=
    (card_le_of_le (sec39d_key_A_cent hVS hES hE2 hX3 hV he₁ hX₁)).trans
      (hH4 y₁ hy₁R hy₁1 (hsq y₁ hy₁R e₁ he₁ hX₁))
  have hcX := sec39d_key_card_X hXS hdec hYR'
  have hb : Nat.card {y : ↥R' // ∃ e ∈ E, e * y.1 ∈ X} ≤ (q ^ 2) ^ 2 := by
    rw [← hcardR']
    exact Finite.card_subtype_le _
  have hq4 : 0 < (q ^ 2) ^ 2 := by positivity
  have hq10 : 0 < q ^ 10 := by positivity
  have hprod : q ^ 10 * (q ^ 2) ^ 2 ≤
      Nat.card (X ⊓ E : Subgroup G) * Nat.card {y : ↥R' // ∃ e ∈ E, e * y.1 ∈ X} := by
    calc q ^ 10 * (q ^ 2) ^ 2 = q ^ 14 := by ring
      _ ≤ Nat.card X := hcardX
      _ ≤ _ := hcX
  obtain ⟨ha, hbb⟩ := lin39d_mul_eq hinf1 hb hq10 hq4 hprod
  have hall : ∀ y ∈ R', ∃ e ∈ E, e * y ∈ X := by
    intro y hy
    by_contra hno
    have hlt : Nat.card {y : ↥R' // ∃ e ∈ E, e * y.1 ∈ X} < Nat.card ↥R' :=
      Finite.card_subtype_lt (p := fun y : ↥R' => ∃ e ∈ E, e * y.1 ∈ X) (x := ⟨y, hy⟩) hno
    rw [hcardR'] at hlt
    omega
  have hF1 : ∀ y ∈ R', ∀ u ∈ (X ⊓ E : Subgroup G), u ∈ E ∧ ⁅u, y⁆ ∈ V := by
    intro y hy u hu
    obtain ⟨e, he, hX⟩ := hall y hy
    exact sec39d_mem_ECent.1 (sec39d_key_A_cent hVS hES hE2 hX3 hV he hX hu)
  have hF1' : ∀ y ∈ R'', ∀ u ∈ (X ⊓ E : Subgroup G).map (MulAut.conj t).toMonoidHom,
      u ∈ E ∧ ⁅u, y⁆ ∈ V := by
    rintro y hy _ ⟨u₀, hu₀, rfl⟩
    rw [← hconj] at hy
    obtain ⟨y₀, hy₀, rfl⟩ := hy
    obtain ⟨hu₀E, hcomm⟩ := hF1 y₀ hy₀ u₀ hu₀
    have e1 : ⁅t * u₀ * t⁻¹, t * y₀ * t⁻¹⁆ = t * ⁅u₀, y₀⁆ * t⁻¹ := by
      simp only [commutatorElement_def]
      group
    exact ⟨htE u₀ hu₀E, by
      show ⁅t * u₀ * t⁻¹, t * y₀ * t⁻¹⁆ ∈ V
      rw [e1]
      exact htV _ hcomm⟩
  have hcardC' : Nat.card ↥((X ⊓ E : Subgroup G).map (MulAut.conj t).toMonoidHom) = q ^ 10 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj t).injective]
    exact ha
  obtain ⟨z, ⟨hzR', hzR''⟩, hz1⟩ := hz
  have hzR : z ∈ R := hR'R hzR'
  have hEz := hH4 z hzR hz1 (hel' z hzR')
  have hCEz : (X ⊓ E : Subgroup G) ≤
      sec39dECent V E (fun v hv e he => hVS v hv e (hES he)) z :=
    fun u hu => sec39d_mem_ECent.2 (hF1 z hzR' u hu)
  have hC'Ez : (X ⊓ E : Subgroup G).map (MulAut.conj t).toMonoidHom ≤
      sec39dECent V E (fun v hv e he => hVS v hv e (hES he)) z :=
    fun u hu => sec39d_mem_ECent.2 (hF1' z hzR'' u hu)
  have hCeq : (X ⊓ E : Subgroup G) =
      sec39dECent V E (fun v hv e he => hVS v hv e (hES he)) z :=
    Subgroup.eq_of_le_of_card_ge hCEz (by rw [ha]; exact hEz)
  have hC'eq : (X ⊓ E : Subgroup G).map (MulAut.conj t).toMonoidHom =
      sec39dECent V E (fun v hv e he => hVS v hv e (hES he)) z :=
    Subgroup.eq_of_le_of_card_ge hC'Ez (by rw [hcardC']; exact hEz)
  have hCC' : (X ⊓ E : Subgroup G).map (MulAut.conj t).toMonoidHom = (X ⊓ E : Subgroup G) :=
    hC'eq.trans hCeq.symm
  have hR'T : R' ≤ lin39dCentSub S V (X ⊓ E : Subgroup G) hVS := fun y hy =>
    ⟨hRS (hR'R hy), fun u hu => (hF1 y hy u hu).2⟩
  have hR''T : R'' ≤ lin39dCentSub S V (X ⊓ E : Subgroup G) hVS := fun y hy =>
    ⟨hRS (hR''R hy), fun u hu => (hF1' y hy u (by rw [hCC']; exact hu)).2⟩
  have hRT : R ≤ lin39dCentSub S V (X ⊓ E : Subgroup G) hVS := by
    rw [← hRR]
    exact sup_le hR'T hR''T
  have hCS : ∀ u ∈ (X ⊓ E : Subgroup G), ∀ s ∈ S, ⁅u, s⁆ ∈ V := by
    intro u hu s hs
    obtain ⟨e, he, y, hyR, rfl⟩ := hdec s hs
    have huE : u ∈ E := (Subgroup.mem_inf.1 hu).2
    have h1 : ⁅u, e⁆ ∈ V := hE2 u huE e he
    have h2 : ⁅u, y⁆ ∈ V := (hRT hyR).2 u hu
    have e3 : ⁅u, e * y⁆ = ⁅u, e⁆ * (e * ⁅u, y⁆ * e⁻¹) := sec39d_key_comm_mul u e y
    have h4 : e * ⁅u, y⁆ * e⁻¹ = ⁅u, y⁆ := by
      rw [← hV _ h2 e he]
      group
    rw [e3, h4]
    exact mul_mem h1 h2
  have hCW : (X ⊓ E : Subgroup G) ≤ W := fun u hu =>
    hW u (Subgroup.mem_inf.1 hu).2 (hCS u hu)
  have := card_le_of_le hCW
  omega

theorem lin39d_key_abstract (q : ℕ) (hq : 2 ≤ q) (S E V R R₁ R₂ W : Subgroup G) (t : G)
    (ht : t * t = 1) (hVS : ∀ v ∈ V, ∀ s ∈ S, v * s = s * v) (hVE : V ≤ E) (hES : E ≤ S)
    (hEn : ∀ s ∈ S, ∀ e ∈ E, s * e * s⁻¹ ∈ E) (hE2 : ∀ x ∈ E, ∀ y ∈ E, ⁅x, y⁆ ∈ V)
    (hcardE : Nat.card E = q ^ 14) (hRS : R ≤ S) (hdec : ∀ s ∈ S, ∃ e ∈ E, ∃ y ∈ R, s = e * y)
    (hER : ∀ x ∈ E, x ∈ R → x = 1) (htE : ∀ e ∈ E, t * e * t⁻¹ ∈ E)
    (htV : ∀ v ∈ V, t * v * t⁻¹ ∈ V) (hrad : Radicals R R₁ R₂ (q ^ 2))
    (hswap : R₁.map (MulAut.conj t).toMonoidHom = R₂)
    (hH4 : ∀ y ∈ R, y ≠ 1 → y * y = 1 →
      Nat.card (sec39dECent V E (fun v hv e he => hVS v hv e (hES he)) y) ≤ q ^ 10)
    (hW : ∀ u ∈ E, (∀ s ∈ S, ⁅u, s⁆ ∈ V) → u ∈ W) (hcardW : Nat.card W < q ^ 10) :
    ∀ X : Subgroup G, V ≤ X → X ≤ S → (∀ x ∈ X, x * x ∈ V) →
      (∀ x ∈ X, ∀ y ∈ X, ⁅x, y⁆ ∈ V) → q ^ 14 ≤ Nat.card X → X = E := by
  intro X hVX hXS hX2 hX3 hcardX
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hswap' : R₂.map (MulAut.conj t).toMonoidHom = R₁ := by
    rw [← hswap]
    ext z
    constructor
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      show t * (t * w * t⁻¹) * t⁻¹ ∈ R₁
      have : t * (t * w * t⁻¹) * t⁻¹ = w := by
        rw [hti]
        calc t * (t * w * t) * t = (t * t) * w * (t * t) := by group
          _ = w := by rw [ht]; group
      rw [this]
      exact hw
    · intro hz
      refine ⟨t * z * t⁻¹, ⟨z, hz, rfl⟩, ?_⟩
      show t * (t * z * t⁻¹) * t⁻¹ = z
      rw [hti]
      calc t * (t * z * t) * t = (t * t) * z * (t * t) := by group
        _ = z := by rw [ht]; group
  have hV : ∀ v ∈ V, ∀ e ∈ E, v * e = e * v := fun v hv e he => hVS v hv e (hES he)
  have hsq : ∀ y ∈ R, ∀ e ∈ E, e * y ∈ X → y * y = 1 := fun y hy e he hX =>
    sec39d_key_A_inv hVE hEn hRS hER hX2 hy he hX
  have hYbsq : ∀ y ∈ lin39dImg S E R X hEn hRS, y * y = 1 := by
    rintro y ⟨hyR, e, he, hX⟩
    exact hsq y hyR e he hX
  have hYbR : lin39dImg S E R X hEn hRS ≤ R := fun y hy => hy.1
  have hYbel : IsElemAbelian 2 (lin39dImg S E R X hEn hRS) := by
    refine isElemAbelian_of_forall (fun x hx y hy => ?_) (fun x hx => ?_)
    · have h1 : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right (hYbsq _ (mul_mem hx hy))
      have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hYbsq x hx)
      have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hYbsq y hy)
      calc x * y = (x * y)⁻¹ := h1.symm
        _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
        _ = y * x := by rw [hx', hy']
    · rw [pow_two]
      exact hYbsq x hx
  by_cases hnt : ∃ y ∈ R, y ≠ 1 ∧ ∃ e ∈ E, e * y ∈ X
  · exfalso
    have hq2 : 1 < Nat.card ↥(R₁ ⊓ R₂) := by
      rw [hrad.inf_eq, hrad.card_center]
      nlinarith
    obtain ⟨z, hz, hz1⟩ := lin39d_exists_ne_one hq2
    rcases hrad.le_of_elem _ hYbR hYbel with hle | hle
    · exact lin39d_key_case q hq S E V R R₁ R₂ W t hVS hVE hES hEn hE2 hRS hdec hER htE htV
        hrad.le₁ hrad.le₂ hrad.sup_eq (by rw [hrad.card₁]) (fun x hx => by
          rw [← pow_two]; exact hrad.elem₁.2 x hx) ⟨z, hz, hz1⟩ hswap hH4 hW hcardW X hXS hX2 hX3
        hcardX (fun y hy e he hX => hle ⟨hy, e, he, hX⟩) hnt
    · exact lin39d_key_case q hq S E V R R₂ R₁ W t hVS hVE hES hEn hE2 hRS hdec hER htE htV
        hrad.le₂ hrad.le₁ (by rw [sup_comm]; exact hrad.sup_eq) (by rw [hrad.card₂])
        (fun x hx => by rw [← pow_two]; exact hrad.elem₂.2 x hx)
        ⟨z, ⟨hz.2, hz.1⟩, hz1⟩ hswap' hH4 hW hcardW X hXS hX2 hX3 hcardX
        (fun y hy e he hX => hle ⟨hy, e, he, hX⟩) hnt
  · have hXE : X ≤ E := by
      intro x hx
      obtain ⟨e, he, y, hyR, rfl⟩ := hdec x (hXS hx)
      by_cases hy1 : y = 1
      · rw [hy1, mul_one]
        exact he
      · exact (hnt ⟨y, hyR, hy1, e, he, hx⟩).elim
    exact Subgroup.eq_of_le_of_card_ge hXE (by rw [hcardE]; exact hcardX)

end Key2

end LinCase

end CFSG.LocalAnalysis.EvenBN.U5
