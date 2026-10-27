module

public import CFSG.GH74.GLS.Classes
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CharacterTheory.Semidihedral.OddFieldSL2
public import CFSG.GroupTheory.QuaternionCentralizers
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2011.Ad.ClaimG

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank

theorem sl2_sylow_facts {L : Type} [Group L] [Finite L] {q : ℕ} (hL : HasSL2Model L (fun r => r = q))
    (hq : Odd q) (Q : Sylow 2 L) :
    (∀ x ∈ (Q : Subgroup L), (∀ y ∈ (Q : Subgroup L), x * y = y * x) → x * x = 1) ∧
    (∃ a ∈ (Q : Subgroup L), ∃ b ∈ (Q : Subgroup L), a * b ≠ b * a) ∧
    (∀ a b : L, orderOf a = 2 → orderOf b = 2 → a = b) := by
  obtain ⟨F, hF, hFin, hFq, ⟨e'⟩⟩ := hL
  let e : Matrix.SpecialLinearGroup (Fin 2) F ≃* L := (specialLinearGroupEquivStatedSL 2 F).trans e'.symm
  have hodd : Odd (Nat.card F) := hFq ▸ hq
  have hle : (Q : Subgroup L) ≤ e.toMonoidHom.range := by
    intro x _
    exact ⟨e.symm x, by simp⟩
  let P : Sylow 2 (Matrix.SpecialLinearGroup (Fin 2) F) := Q.comapOfInjective e.toMonoidHom e.injective hle
  have hP : (P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) = (Q : Subgroup L).comap e.toMonoidHom :=
    Sylow.coe_comapOfInjective Q e.toMonoidHom e.injective hle
  have hmemP : ∀ x : Matrix.SpecialLinearGroup (Fin 2) F, x ∈ (P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) ↔ e x ∈ (Q : Subgroup L) := by
    intro x
    rw [hP]; rfl
  refine ⟨?_, ?_, ?_⟩
  · intro x hx hxc
    set x' := e.symm x with hx'
    have hx'P : x' ∈ (P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) :=
      (hmemP x').2 (by simpa [hx'] using hx)
    obtain ⟨n, hn3, ⟨f⟩⟩ := Semidihedral.OddFieldSL2.sylow_two_quaternion F hodd P
    have hm2 : 2 ≤ 2 ^ (n - 2) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (n - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : NeZero (2 ^ (n - 2)) := ⟨by positivity⟩
    have hcen := ((GroupTheory.quaternion_centralizers hm2).2.2.1 (f ⟨x', hx'P⟩)).1 (by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨p, rfl⟩ := f.surjective g
      have hpQ : e (p : Matrix.SpecialLinearGroup (Fin 2) F) ∈ (Q : Subgroup L) :=
        (hmemP _).1 p.2
      have h1 := hxc _ hpQ
      have h2 : x' * (p : Matrix.SpecialLinearGroup (Fin 2) F) = (p : Matrix.SpecialLinearGroup (Fin 2) F) * x' := by
        apply e.injective
        rw [map_mul, map_mul, hx']
        simpa using h1
      have h3 : (⟨x', hx'P⟩ : ↥(P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F))) * p =
          p * ⟨x', hx'P⟩ := Subtype.ext h2
      rw [← map_mul, ← map_mul, h3])
    have hsq : f ⟨x', hx'P⟩ * f ⟨x', hx'P⟩ = 1 := by
      rcases hcen with h | h
      · rw [h, QuaternionGroup.a_mul_a, add_zero]
        rfl
      · rw [h, QuaternionGroup.a_mul_a]
        have : ((2 ^ (n - 2) : ℕ) : ZMod (2 * 2 ^ (n - 2))) + ((2 ^ (n - 2) : ℕ) : ZMod (2 * 2 ^ (n - 2))) = 0 := by
          have := ZMod.natCast_self (2 * 2 ^ (n - 2))
          push_cast at this ⊢
          linear_combination this
        rw [this]
        rfl
    have hsq' : (⟨x', hx'P⟩ : ↥(P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F))) * ⟨x', hx'P⟩ = 1 := by
      apply f.injective
      rw [map_mul, map_one]
      exact hsq
    have : x' * x' = 1 := congrArg Subtype.val hsq'
    calc x * x = e (x' * x') := by rw [map_mul, hx']; simp
      _ = 1 := by rw [this, map_one]
  · by_contra hcon
    push Not at hcon
    apply Semidihedral.OddFieldSL2.sylow_two_not_isMulCommutative F hodd P
    rw [isMulCommutative_iff]
    intro a b
    apply Subtype.ext
    apply e.injective
    rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
    exact hcon _ ((hmemP _).1 a.2) _ ((hmemP _).1 b.2)
  · intro a b ha hb
    have hstr := (Semidihedral.OddFieldSL2.odd_field_involution_structure F hodd).2.2.1
    have h1 := (hstr (e.symm a)).1 (by rw [MulEquiv.orderOf_eq]; exact ha)
    have h2 := (hstr (e.symm b)).1 (by rw [MulEquiv.orderOf_eq]; exact hb)
    exact e.symm.injective (h1.trans h2.symm)


theorem mul_self_eq_one_of_card_le_two' {Z : Type*} [Group Z] [Finite Z] (hZ : Nat.card Z ≤ 2) (w : Z) :
    w * w = 1 := by
  have h := pow_card_eq_one' (G := Z) (x := w)
  have hpos : 0 < Nat.card Z := Nat.card_pos
  interval_cases hc : Nat.card Z
  · rw [pow_one] at h; rw [h, one_mul]
  · rw [← sq]; exact h

section Abstract

variable {Cb : Type} [Group Cb] [Finite Cb] {L₁ L₂ : Subgroup Cb} {q : ℕ}



theorem eq_of_card_two {Z : Type} [Group Z] (h : Nat.card Z = 2) {a b : Z} (ha : a ≠ 1) (hb : b ≠ 1) : a = b := by
  obtain ⟨x, y, hxy, hs⟩ := Nat.card_eq_two_iff.1 h
  have hmem : ∀ w : Z, w = x ∨ w = y := fun w => by
    have : w ∈ ({x, y} : Set Z) := by rw [hs]; trivial
    simpa using this
  rcases hmem 1 with h1 | h1 <;> rcases hmem a with ha' | ha' <;> rcases hmem b with hb' | hb'
  · exact absurd (ha'.trans h1.symm) ha
  · exact absurd (ha'.trans h1.symm) ha
  · exact absurd (hb'.trans h1.symm) hb
  · exact ha'.trans hb'.symm
  · exact ha'.trans hb'.symm
  · exact absurd (hb'.trans h1.symm) hb
  · exact absurd (ha'.trans h1.symm) ha
  · exact absurd (ha'.trans h1.symm) ha


theorem comm_of_card_two {Z : Type} [Group Z] (h : Nat.card Z = 2) (a b : Z) : a * b = b * a := by
  by_cases ha : a = 1
  · rw [ha]; simp
  by_cases hb : b = 1
  · rw [hb]; simp
  rw [eq_of_card_two h ha hb]

theorem mem_inf_of_central_sylow (hodd : Odd q) (hsl : HasSL2Model ↥L₁ (fun r => r = q))
    (hcard : Nat.card ↥(L₁ ⊓ L₂) = 2) (Q : Sylow 2 ↥L₁) {l₁ : Cb} (hl₁ : l₁ ∈ L₁) (hl₁4 : l₁ ^ 4 = 1)
    (hcen : ∀ x ∈ (Q : Subgroup ↥L₁), l₁ * (x : Cb) = (x : Cb) * l₁) : l₁ ∈ L₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hZ, -, hinv⟩ := sl2_sylow_facts hsl hodd Q
  set l : ↥L₁ := ⟨l₁, hl₁⟩ with hl
  have hlc : ∀ x ∈ (Q : Subgroup ↥L₁), l * x = x * l := fun x hx => Subtype.ext (hcen x hx)
  have hl4 : l ^ 4 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hl₁4)
  have hlQ : l ∈ (Q : Subgroup ↥L₁) := by
    have hpg : IsPGroup 2 ↥((Q : Subgroup ↥L₁) ⊔ zpowers l) := by
      obtain ⟨a, ha⟩ := Q.isPGroup'.exists_card_eq
      have hord : orderOf l ∣ 2 ^ 2 := orderOf_dvd_of_pow_eq_one (by simpa using hl4)
      obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hord
      have hcomm : ∀ x ∈ (Q : Subgroup ↥L₁), ∀ y ∈ zpowers l, x * y = y * x := by
        intro x hx y hy
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
        exact ((Commute.zpow_right (show Commute x l from (hlc x hx).symm) n)).eq
      have hprod := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (Q : Subgroup ↥L₁) (zpowers l) hcomm).1
      rw [ha, Nat.card_zpowers, hb, ← pow_add] at hprod
      have hdvd : Nat.card ↥((Q : Subgroup ↥L₁) ⊔ zpowers l) ∣ 2 ^ (a + b) :=
        ⟨Nat.card ↥((Q : Subgroup ↥L₁) ⊓ zpowers l), hprod.symm⟩
      obtain ⟨c, -, hc⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
      exact IsPGroup.of_card hc
    have heq := Q.is_maximal' hpg le_sup_left
    rw [← heq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers l)
  have hl2 : l * l = 1 := hZ l hlQ hlc
  by_cases h1 : l = 1
  · have : l₁ = 1 := congrArg Subtype.val h1
    rw [this]; exact L₂.one_mem
  · have hl2' : orderOf l = 2 := orderOf_eq_prime (by rw [pow_two]; exact hl2) h1
    obtain ⟨ζ, hζ1⟩ : ∃ ζ : ↥(L₁ ⊓ L₂), ζ ≠ 1 := by
      have hne : (L₁ ⊓ L₂) ≠ ⊥ := by
        intro hbot
        rw [hbot, Subgroup.card_bot] at hcard
        omega
      exact Subgroup.ne_bot_iff_exists_ne_one.1 hne
    have hζsq : ζ * ζ = 1 := mul_self_eq_one_of_card_le_two' hcard.le ζ
    let ζ' : ↥L₁ := Subgroup.inclusion inf_le_left ζ
    have hζ'1 : ζ' ≠ 1 := by
      intro h
      apply hζ1
      apply Subgroup.inclusion_injective (inf_le_left : L₁ ⊓ L₂ ≤ L₁)
      rw [map_one]
      exact h
    have hζ'sq : ζ' * ζ' = 1 := by rw [← map_mul, hζsq, map_one]
    have hζ'2 : orderOf ζ' = 2 := orderOf_eq_prime (by rw [pow_two]; exact hζ'sq) hζ'1
    have := hinv l ζ' hl2' hζ'2
    have h3 : l₁ = (ζ : Cb) := congrArg (fun w : ↥L₁ => (w : Cb)) this
    rw [h3]
    exact (ζ.2).2

theorem no_swap_of_sylow (hodd : Odd q) (hsl : HasSL2Model ↥L₁ (fun r => r = q))
    (hcard : Nat.card ↥(L₁ ⊓ L₂) = 2) (Q : Sylow 2 ↥L₁) {c : Cb}
    (hfix : ∀ x ∈ (Q : Subgroup ↥L₁), c * (x : Cb) * c⁻¹ = x)
    (hsw : ∀ x ∈ L₁, c * x * c⁻¹ ∈ L₂) : False := by
  obtain ⟨-, ⟨a, ha, b, hb, hab⟩, -⟩ := sl2_sylow_facts hsl hodd Q
  have hmem : ∀ x ∈ (Q : Subgroup ↥L₁), (x : Cb) ∈ L₁ ⊓ L₂ := by
    intro x hx
    refine ⟨x.2, ?_⟩
    have := hsw (x : Cb) x.2
    rwa [hfix x hx] at this
  have h2 : (a : Cb) * (b : Cb) = (b : Cb) * (a : Cb) := by
    have := comm_of_card_two hcard (⟨(a : Cb), hmem a ha⟩ : ↥(L₁ ⊓ L₂)) ⟨(b : Cb), hmem b hb⟩
    exact congrArg (fun w : ↥(L₁ ⊓ L₂) => (w : Cb)) this
  exact hab (Subtype.ext h2)

end Abstract

end CFSG.GH74.GLS.Stage2.Final.Thm6.L2011.Ad.ClaimG
