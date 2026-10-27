module

public import CFSG.GH74.QTGen4.Recog.G23.HSL
public import CFSG.GH74.QTGen4.Recog.G23.P7.OpenLeaves

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Recog.G23.P7

open CFSG.Open CFSG.Quasithin.G23Type CFSG.GH74.QTGen4.Recog.G23 CFSG.CosetTable
open scoped MatrixGroups Pointwise

section Generic

variable {G : Type} [Group G]

theorem stepA_decomp {A B : Subgroup G} (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : G}
    (hx : x ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  let Q : Subgroup G :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, a * b = x}
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
        calc a * a' * (b * b') = a * (a' * b) * b' := by group
          _ = a * (b * a') * b' := by rw [hc a' ha' b hb]
          _ = a * b * (a' * b') := by group
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
        have h2 := congrArg (fun y : G => y⁻¹) (hc a ha b hb)
        simp only [mul_inv_rev] at h2
        rw [mul_inv_rev]
        exact h2.symm }
  have hle : A ⊔ B ≤ Q :=
    sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, mul_one a⟩) (fun b hb => ⟨1, A.one_mem, b, hb, one_mul b⟩)
  exact hle hx

theorem stepA_card_sup (A B : Subgroup G) (hB : B ≤ Subgroup.normalizer (A : Set G))
    (hAB : A ⊓ B = ⊥) : Nat.card ↥(A ⊔ B) = Nat.card A * Nat.card B := by
  have hset : ((A ⊔ B : Subgroup G) : Set G) = (A : Set G) * (B : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left A B hB
  let f : A × B → ↥(A ⊔ B) := fun p => ⟨p.1 * p.2, Subgroup.mul_mem_sup p.1.2 p.2.2⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨a, b⟩ ⟨a', b'⟩ h
      have h' : (a : G) * b = a' * b' := congrArg (fun x : ↥(A ⊔ B) => (x : G)) h
      have key : (a' : G)⁻¹ * a = b' * (b : G)⁻¹ := by
        calc (a' : G)⁻¹ * a = (a' : G)⁻¹ * ((a : G) * b) * (b : G)⁻¹ := by group
          _ = (a' : G)⁻¹ * ((a' : G) * b') * (b : G)⁻¹ := by rw [h']
          _ = b' * (b : G)⁻¹ := by group
      have hmA : (a' : G)⁻¹ * a ∈ A := A.mul_mem (A.inv_mem a'.2) a.2
      have hmB : (a' : G)⁻¹ * a ∈ B := by
        rw [key]; exact B.mul_mem b'.2 (B.inv_mem b.2)
      have h1 : (a' : G)⁻¹ * a = 1 := by
        have : (a' : G)⁻¹ * a ∈ A ⊓ B := ⟨hmA, hmB⟩
        rw [hAB, Subgroup.mem_bot] at this
        exact this
      have h2 : (b' : G) * (b : G)⁻¹ = 1 := by rw [← key, h1]
      have hav : (a : G) = a' := (inv_mul_eq_one.mp h1).symm
      have hbv : (b : G) = b' := (mul_inv_eq_one.mp h2).symm
      exact Prod.ext (Subtype.ext hav) (Subtype.ext hbv)
    · rintro ⟨x, hx⟩
      have hx' : x ∈ (A : Set G) * (B : Set G) := by rw [← hset]; exact hx
      obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hx'
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  calc Nat.card ↥(A ⊔ B) = Nat.card (A × B) := (Nat.card_congr (Equiv.ofBijective f hf)).symm
    _ = Nat.card A * Nat.card B := Nat.card_prod _ _

theorem stepA_eq_one_of_sq_cube {x : G} (h2 : x ^ 2 = 1) (h3 : x ^ 3 = 1) : x = 1 := by
  calc x = x ^ 3 * (x ^ 2)⁻¹ := by group
    _ = 1 := by rw [h3, h2, inv_one, mul_one]

theorem stepA_mem_of_sup {A B : Subgroup G} (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hAB : A ⊓ B = ⊥) (hA3 : ∀ a ∈ A, a ^ 3 = 1) {u : G} (hu : u ∈ A ⊔ B) (hu2 : u * u = 1) :
    u ∈ B := by
  obtain ⟨a, ha, b, hb, rfl⟩ := stepA_decomp hc hu
  have hcomm : a * b * (a * b) = a * a * (b * b) := by
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [← hc a ha b hb]
      _ = a * a * (b * b) := by group
  have h1 : a * a * (b * b) = 1 := hcomm ▸ hu2
  have hBa : a * a ∈ B := by
    have : a * a = (b * b)⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [this]
    exact B.inv_mem (B.mul_mem hb hb)
  have haa : a * a = 1 := by
    have : a * a ∈ A ⊓ B := ⟨A.mul_mem ha ha, hBa⟩
    rw [hAB, Subgroup.mem_bot] at this
    exact this
  have ha1 : a = 1 := stepA_eq_one_of_sq_cube (by rw [pow_two]; exact haa) (hA3 a ha)
  rw [ha1, one_mul]
  exact hb

theorem stepA_mem_zpowers_cases {z b : G} (hz : z * z = 1) (hz1 : z ≠ 1)
    (hb : b ∈ Subgroup.zpowers z) : b = 1 ∨ b = z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  have hz2 : z ^ 2 = 1 := by rw [pow_two]; exact hz
  have hord : orderOf z = 2 := orderOf_eq_prime hz2 hz1
  have hmod : z ^ (k % 2) = z ^ k := by simpa [hord] using zpow_mod_orderOf z k
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [h, zpow_zero] at hmod
    exact hmod.symm
  · right
    rw [h, zpow_one] at hmod
    exact hmod.symm

theorem stepA_inf_zpowers {P : Subgroup G} {z : G} (hP3 : ∀ x ∈ P, x ^ 3 = 1) (hz : z * z = 1)
    (hz1 : z ≠ 1) : P ⊓ Subgroup.zpowers z = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxP, hxz⟩
  rw [Subgroup.mem_bot]
  rcases stepA_mem_zpowers_cases hz hz1 hxz with h | h
  · exact h
  · exfalso
    apply hz1
    have hzP : z ∈ P := h ▸ hxP
    exact stepA_eq_one_of_sq_cube (by rw [pow_two]; exact hz) (hP3 z hzP)

theorem stepA_conj_zpowers {y g : G} (h : g * y * g⁻¹ = y⁻¹) {x : G}
    (hx : x ∈ Subgroup.zpowers y) : g * x * g⁻¹ ∈ Subgroup.zpowers y := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← conj_zpow, h, inv_zpow]
  exact Subgroup.inv_mem _ (Subgroup.zpow_mem_zpowers y k)

theorem stepA_mem_normalizer {y g : G} (h : g * y * g⁻¹ = y⁻¹) :
    g ∈ Subgroup.normalizer (Subgroup.zpowers y : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact stepA_conj_zpowers h
  · intro hx
    have hy : g⁻¹ * y⁻¹ * g = y := by rw [← h]; group
    have h' : g⁻¹ * y * g⁻¹⁻¹ = y⁻¹ := by
      rw [inv_inv]
      calc g⁻¹ * y * g = (g⁻¹ * y⁻¹ * g)⁻¹ := by group
        _ = y⁻¹ := by rw [hy]
    have := stepA_conj_zpowers h' hx
    have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
    rw [e] at this
    exact this

def StepAGood (H : Subgroup G) (z y : G) : Prop :=
  (∀ g : G, g * y = y * g → g ∈ H) ∧
  (∀ g : G, g * y * g⁻¹ = y⁻¹ → g ∈ H) ∧
  (∀ u : G, u ∈ H → u * u = 1 → u ≠ 1 → u * y = y * u → u = z)

theorem stepAGood_of_zpow {H : Subgroup G} {z w : G} (hw : StepAGood H z w) {y : G} {m : ℤ}
    (hm : y ^ m = w) : StepAGood H z y := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    apply hw.1
    rw [← hm]
    exact ((show Commute g y from hg).zpow_right m).eq
  · intro g hg
    apply hw.2.1
    rw [← hm, ← conj_zpow, hg, inv_zpow]
  · intro u hu hu2 hu1 huy
    apply hw.2.2 u hu hu2 hu1
    rw [← hm]
    exact ((show Commute u y from huy).zpow_right m).eq

theorem stepAGood_of_pow {H : Subgroup G} {z w x : G} (hw : StepAGood H z w) (h3 : w ^ 3 = 1)
    {k : ℕ} (hk : k = 1 ∨ k = 2) (hx : x = w ^ k) : StepAGood H z x := by
  rcases hk with rfl | rfl
  · rw [hx, pow_one]; exact hw
  · apply stepAGood_of_zpow hw (m := 2)
    rw [zpow_ofNat, hx]
    calc (w ^ 2) ^ 2 = w * w ^ 3 := by group
      _ = w := by rw [h3, mul_one]

theorem stepAGood_conj {H : Subgroup G} {z h x : G} (hh : h ∈ H)
    (hcomm : ∀ g ∈ H, g * z = z * g) (hy : StepAGood H z (h * x * h⁻¹)) : StepAGood H z x := by
  have hzh : z * h = h * z := (hcomm h hh).symm
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    have hc : h * g * h⁻¹ ∈ H := by
      apply hy.1
      calc h * g * h⁻¹ * (h * x * h⁻¹) = h * (g * x) * h⁻¹ := by group
        _ = h * (x * g) * h⁻¹ := by rw [hg]
        _ = h * x * h⁻¹ * (h * g * h⁻¹) := by group
    have : g = h⁻¹ * (h * g * h⁻¹) * h := by group
    rw [this]
    exact H.mul_mem (H.mul_mem (H.inv_mem hh) hc) hh
  · intro g hg
    have hc : h * g * h⁻¹ ∈ H := by
      apply hy.2.1
      calc h * g * h⁻¹ * (h * x * h⁻¹) * (h * g * h⁻¹)⁻¹ = h * (g * x * g⁻¹) * h⁻¹ := by group
        _ = h * x⁻¹ * h⁻¹ := by rw [hg]
        _ = (h * x * h⁻¹)⁻¹ := by group
    have : g = h⁻¹ * (h * g * h⁻¹) * h := by group
    rw [this]
    exact H.mul_mem (H.mul_mem (H.inv_mem hh) hc) hh
  · intro u hu hu2 hu1 huy
    have hc : h * u * h⁻¹ ∈ H := H.mul_mem (H.mul_mem hh hu) (H.inv_mem hh)
    have hc2 : h * u * h⁻¹ * (h * u * h⁻¹) = 1 := by
      calc h * u * h⁻¹ * (h * u * h⁻¹) = h * (u * u) * h⁻¹ := by group
        _ = 1 := by rw [hu2]; group
    have hc1 : h * u * h⁻¹ ≠ 1 := by
      intro h1
      apply hu1
      calc u = h⁻¹ * (h * u * h⁻¹) * h := by group
        _ = 1 := by rw [h1]; group
    have hcy : h * u * h⁻¹ * (h * x * h⁻¹) = (h * x * h⁻¹) * (h * u * h⁻¹) := by
      calc h * u * h⁻¹ * (h * x * h⁻¹) = h * (u * x) * h⁻¹ := by group
        _ = h * (x * u) * h⁻¹ := by rw [huy]
        _ = h * x * h⁻¹ * (h * u * h⁻¹) := by group
    have hcz := hy.2.2 (h * u * h⁻¹) hc hc2 hc1 hcy
    calc u = h⁻¹ * (h * u * h⁻¹) * h := by group
      _ = h⁻¹ * z * h := by rw [hcz]
      _ = h⁻¹ * (z * h) := by group
      _ = h⁻¹ * (h * z) := by rw [hzh]
      _ = z := by group

end Generic

structure StepAData {G : Type} [Group G] (T H H₁ H₂ M M₁ M₂ Pb Np Nm : Subgroup G)
    (e : Fin 6 → G) : Prop where
  setup : Setup G T H H₁ H₂ M e
  hF : HFacts H H₁ H₂ e
  hO : OneClass e
  loc : Local3 e H H₁ H₂ M₁ M₂ Pb Np Nm
  pb9 : Nat.card Pb = 9

section Specific

variable {G : Type} [Group G] [Finite G]

theorem stepA_rels {H H₁ H₂ : Subgroup G} {e : Fin 6 → G} (hL : HLetters H H₁ H₂ e) :
    e 0 ^ 3 = 1 ∧ e 2 ^ 3 = 1 ∧ e 2 * e 0 = e 0 * e 2 ∧
      (e 0 * e 1) ^ 2 = (e 2 * e 3) ^ 2 ∧ e 4 ^ 2 = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h := hL.rels [(0, true), (0, true), (0, true)] (by simp [g23WordsH])
    simpa [FreeGroup.lift_mk, pow_three, mul_assoc] using h
  · have h := hL.rels [(2, true), (2, true), (2, true)] (by simp [g23WordsH])
    simpa [FreeGroup.lift_mk, pow_three, mul_assoc] using h
  · have h := hL.rels [(0, false), (2, false), (0, true), (2, true)] (by simp [g23WordsH])
    simp [FreeGroup.lift_mk, mul_assoc] at h
    have h' := inv_mul_eq_one.mp h
    calc e 2 * e 0 = e 2 * ((e 2)⁻¹ * (e 0 * e 2)) := by rw [← h']
      _ = e 0 * e 2 := by group
  · have h := hL.rels [(0, true), (1, true), (0, true), (1, true), (3, false), (2, false),
      (3, false), (2, false)] (by simp [g23WordsH])
    have h2 : (e 0 * e 1) ^ 2 * ((e 3)⁻¹ * (e 2)⁻¹) ^ 2 = 1 := by
      simpa [FreeGroup.lift_mk, pow_two, mul_assoc] using h
    rw [eq_inv_of_mul_eq_one_left h2]
    simp only [pow_two, mul_inv_rev, inv_inv]
  · have h := hL.rels [(4, true), (4, true)] (by simp [g23WordsH])
    simpa [FreeGroup.lift_mk, pow_two, mul_assoc] using h

theorem stepA_gen {H H₁ H₂ : Subgroup G} {e : Fin 6 → G} (hL : HLetters H H₁ H₂ e) :
    e 0 ∈ H₁ ∧ e 1 ∈ H₁ ∧ e 2 ∈ H₂ ∧ e 3 ∈ H₂ ∧ e 0 ∈ H ∧ e 2 ∈ H ∧ e 4 ∈ H := by
  have hg : ∀ i : Fin 5, e i.castSucc ∈ H := fun i => by
    rw [← hL.gen]; exact Subgroup.subset_closure ⟨i, rfl⟩
  have h0 : e 0 ∈ H₁ := by rw [← hL.gen₁]; exact Subgroup.subset_closure (by simp)
  have h1 : e 1 ∈ H₁ := by rw [← hL.gen₁]; exact Subgroup.subset_closure (by simp)
  have h2 : e 2 ∈ H₂ := by rw [← hL.gen₂]; exact Subgroup.subset_closure (by simp)
  have h3 : e 3 ∈ H₂ := by rw [← hL.gen₂]; exact Subgroup.subset_closure (by simp)
  exact ⟨h0, h1, h2, h3, hg 0, hg 2, hg 4⟩

theorem stepA_e4_notMem {T H H₁ H₂ M M₁ M₂ Pb Np Nm : Subgroup G} {e : Fin 6 → G}
    (D : StepAData T H H₁ H₂ M M₁ M₂ Pb Np Nm e) : e 4 ∉ H₁ ⊔ H₂ := by
  intro h4
  obtain ⟨g0, g1, g2, g3, -, -, -⟩ := stepA_gen D.setup.lets
  have hHK : H ≤ H₁ ⊔ H₂ := by
    rw [← D.setup.lets.gen]
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact (le_sup_left : H₁ ≤ H₁ ⊔ H₂) g0
    · exact (le_sup_left : H₁ ≤ H₁ ⊔ H₂) g1
    · exact (le_sup_right : H₂ ≤ H₁ ⊔ H₂) g2
    · exact (le_sup_right : H₂ ≤ H₁ ⊔ H₂) g3
    · exact h4
  have hKH : H₁ ⊔ H₂ ≤ H := sup_le D.setup.ctx.one.le_one D.setup.ctx.one.le_two
  have hEq : H₁ ⊔ H₂ = H := le_antisymm hKH hHK
  have hidx := D.setup.ctx.one.index
  rw [hEq, Subgroup.relIndex_self] at hidx
  exact absurd hidx (by norm_num)

theorem stepA_e4_orderOf {T H H₁ H₂ M M₁ M₂ Pb Np Nm : Subgroup G} {e : Fin 6 → G}
    (D : StepAData T H H₁ H₂ M M₁ M₂ Pb Np Nm e) : orderOf (e 4) = 2 := by
  have h4 := (stepA_rels D.setup.lets).2.2.2.2
  have hne : e 4 ≠ 1 := by
    intro h
    apply stepA_e4_notMem D
    rw [h]
    exact Subgroup.one_mem _
  exact orderOf_eq_prime h4 hne

theorem stepA_z_orderOf {T H H₁ H₂ M M₁ M₂ Pb Np Nm : Subgroup G} {e : Fin 6 → G}
    (D : StepAData T H H₁ H₂ M M₁ M₂ Pb Np Nm e) : orderOf (zOf e) = 2 := by
  obtain ⟨c, hc⟩ := isConj_iff.mp (D.hO (e 4) (stepA_e4_orderOf D))
  have h := SemiconjBy.orderOf_eq c (show SemiconjBy c (zOf e) (e 4) by
    unfold SemiconjBy; rw [← hc]; group)
  rw [h, stepA_e4_orderOf D]

theorem stepA_z_sq {T H H₁ H₂ M M₁ M₂ Pb Np Nm : Subgroup G} {e : Fin 6 → G}
    (D : StepAData T H H₁ H₂ M M₁ M₂ Pb Np Nm e) : zOf e * zOf e = 1 := by
  have h := pow_orderOf_eq_one (zOf e)
  rw [stepA_z_orderOf D] at h
  rw [← pow_two]
  exact h

theorem stepA_z_ne_one {T H H₁ H₂ M M₁ M₂ Pb Np Nm : Subgroup G} {e : Fin 6 → G}
    (D : StepAData T H H₁ H₂ M M₁ M₂ Pb Np Nm e) : zOf e ≠ 1 := by
  intro h
  have := stepA_z_orderOf D
  rw [h, orderOf_one] at this
  exact absurd this (by norm_num)

theorem stepA_zH1 {T H H₁ H₂ M M₁ M₂ Pb Np Nm : Subgroup G} {e : Fin 6 → G}
    (D : StepAData T H H₁ H₂ M M₁ M₂ Pb Np Nm e) : zOf e ∈ H₁ := by
  obtain ⟨h0, h1, -⟩ := stepA_gen D.setup.lets
  show (e 0 * e 1) ^ 2 ∈ H₁
  exact H₁.pow_mem (H₁.mul_mem h0 h1) 2

theorem stepA_zH2 {T H H₁ H₂ M M₁ M₂ Pb Np Nm : Subgroup G} {e : Fin 6 → G}
    (D : StepAData T H H₁ H₂ M M₁ M₂ Pb Np Nm e) : zOf e ∈ H₂ := by
  obtain ⟨-, -, h2, h3, -⟩ := stepA_gen D.setup.lets
  show (e 0 * e 1) ^ 2 ∈ H₂
  rw [(stepA_rels D.setup.lets).2.2.2.1]
  exact H₂.pow_mem (H₂.mul_mem h2 h3) 2

theorem stepA_zH {T H H₁ H₂ M M₁ M₂ Pb Np Nm : Subgroup G} {e : Fin 6 → G}
    (D : StepAData T H H₁ H₂ M M₁ M₂ Pb Np Nm e) : zOf e ∈ H :=
  D.setup.ctx.one.le_one (stepA_zH1 D)

theorem stepA_H_iff {T H H₁ H₂ M M₁ M₂ Pb Np Nm : Subgroup G} {e : Fin 6 → G}
    (D : StepAData T H H₁ H₂ M M₁ M₂ Pb Np Nm e) (g : G) : g ∈ H ↔ g * zOf e = zOf e * g := by
  have hzpow : Subgroup.zpowers (zOf e) = H₁ ⊓ H₂ := by
    apply Subgroup.eq_of_le_of_card_ge
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_inf.mpr ⟨stepA_zH1 D, stepA_zH2 D⟩
    · rw [D.setup.ctx.one.card_inf, Nat.card_zpowers, stepA_z_orderOf D]
  have hHc := D.setup.ctx.one.eq_centralizer
  constructor
  · intro hg
    rw [hHc] at hg
    have hz : zOf e ∈ ((H₁ ⊓ H₂ : Subgroup G) : Set G) :=
      Subgroup.mem_inf.mpr ⟨stepA_zH1 D, stepA_zH2 D⟩
    exact ((Subgroup.mem_centralizer_iff.mp hg) (zOf e) hz).symm
  · intro hg
    rw [hHc, Subgroup.mem_centralizer_iff]
    intro x hx
    have hx' : x ∈ Subgroup.zpowers (zOf e) := by
      rw [hzpow]; exact hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx'
    exact ((show Commute (zOf e) g from hg.symm).zpow_left k).eq

theorem stepA_e4_comm {T H H₁ H₂ M M₁ M₂ Pb Np Nm : Subgroup G} {e : Fin 6 → G}
    (D : StepAData T H H₁ H₂ M M₁ M₂ Pb Np Nm e) : e 4 * zOf e = zOf e * e 4 :=
  (stepA_H_iff D (e 4)).mp (by obtain ⟨-, -, -, -, -, -, h4⟩ := stepA_gen D.setup.lets; exact h4)

theorem stepA_t_ne_z {T H H₁ H₂ M M₁ M₂ Pb Np Nm : Subgroup G} {e : Fin 6 → G}
    (D : StepAData T H H₁ H₂ M M₁ M₂ Pb Np Nm e) : e 4 ≠ zOf e := by
  intro h
  apply stepA_e4_notMem D
  rw [h]
  exact (le_sup_left : H₁ ≤ H₁ ⊔ H₂) (stepA_zH1 D)

theorem stepA_closure_pair {t z : G} (ht : t * t = 1) (hz : z * z = 1) (htz : t * z = z * t)
    (ht1 : t ≠ 1) (hz1 : z ≠ 1) (htz' : t ≠ z) :
    (Subgroup.closure ({t, z} : Set G) : Set G) = {1, t, z, t * z} ∧
      Nat.card ↥(Subgroup.closure ({t, z} : Set G)) = 4 := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have hzt : z * t = t * z := htz.symm
  have htz1 : t * z ≠ 1 := by
    intro h
    apply htz'
    have := eq_inv_of_mul_eq_one_left h
    rw [hzi] at this
    exact this
  have h_t_tz : t * (t * z) = z := by rw [← mul_assoc, ht, one_mul]
  have h_z_tz : z * (t * z) = t := by rw [← mul_assoc, hzt, mul_assoc, hz, mul_one]
  have h_tz_t : t * z * t = z := by rw [mul_assoc, hzt, ← mul_assoc, ht, one_mul]
  have h_tz_z : t * z * z = t := by rw [mul_assoc, hz, mul_one]
  have h_tz_tz : t * z * (t * z) = 1 := by
    calc t * z * (t * z) = t * (t * z) * z := by rw [mul_assoc, ← mul_assoc z t z, hzt]; group
      _ = 1 := by rw [h_t_tz, hz]
  have h_inv_tz : (t * z)⁻¹ = t * z := by rw [mul_inv_rev, hti, hzi, hzt]
  have hsub : ∀ x ∈ Subgroup.closure ({t, z} : Set G), x ∈ ({1, t, z, t * z} : Set G) := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · simp
      · simp
    | one => simp
    | mul x y _ _ hx hy =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy ⊢
      rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
        simp [ht, hz, hzt, h_t_tz, h_z_tz, h_tz_t, h_tz_z, h_tz_tz]
    | inv x _ hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      rcases hx with rfl | rfl | rfl | rfl <;> simp [hti, hzi, h_inv_tz]
  have hsup : ∀ x ∈ ({1, t, z, t * z} : Set G), x ∈ Subgroup.closure ({t, z} : Set G) := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  have hS : (Subgroup.closure ({t, z} : Set G) : Set G) = {1, t, z, t * z} :=
    Set.Subset.antisymm (fun x hx => hsub x hx) (fun x hx => hsup x hx)
  refine ⟨hS, ?_⟩
  have h1 : (1 : G) ∉ ({t, z, t * z} : Set G) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun h => ht1 h.symm, fun h => hz1 h.symm, fun h => htz1 h.symm⟩
  have h2 : t ∉ ({z, t * z} : Set G) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    refine ⟨htz', fun h => hz1 ?_⟩
    calc z = t * (t * z) := h_t_tz.symm
      _ = t * t := by rw [← h]
      _ = 1 := ht
  have h3 : z ≠ t * z := by
    intro h
    apply ht1
    calc t = t * (z * z) := by rw [hz, mul_one]
      _ = t * z * z := by rw [mul_assoc]
      _ = z * z := by rw [← h]
      _ = 1 := hz
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, hS, Set.ncard_insert_of_notMem h1,
    Set.ncard_insert_of_notMem h2, Set.ncard_pair h3]

theorem stepA_E {T H H₁ H₂ M M₁ M₂ Pb Np Nm : Subgroup G} {e : Fin 6 → G}
    (D : StepAData T H H₁ H₂ M M₁ M₂ Pb Np Nm e) :
    (Esub e : Set G) = {1, e 4, zOf e, e 4 * zOf e} ∧ Nat.card ↥(Esub e) = 4 :=
  stepA_closure_pair (by rw [← pow_two]; exact (stepA_rels D.setup.lets).2.2.2.2)
    (stepA_z_sq D) (stepA_e4_comm D) (fun h => by
      have := stepA_e4_orderOf D
      rw [h, orderOf_one] at this
      exact absurd this (by norm_num)) (stepA_z_ne_one D) (stepA_t_ne_z D)

theorem stepA_H_elems {T H H₁ H₂ M M₁ M₂ Pb Np Nm : Subgroup G} {e : Fin 6 → G}
    (D : StepAData T H H₁ H₂ M M₁ M₂ Pb Np Nm e) :
    e 0 ∈ H ∧ e 2 ∈ H ∧ e 4 ∈ H := by
  obtain ⟨-, -, -, -, h0, h2, h4⟩ := stepA_gen D.setup.lets
  exact ⟨h0, h2, h4⟩

theorem stepA_P_le_H {T H H₁ H₂ M M₁ M₂ Pb Np Nm : Subgroup G} {e : Fin 6 → G}
    (D : StepAData T H H₁ H₂ M M₁ M₂ Pb Np Nm e) : Psub e ≤ H := by
  obtain ⟨h0, h2, -⟩ := stepA_H_elems D
  unfold Psub
  refine (Subgroup.closure_le _).mpr ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact h0
  · exact h2

theorem stepA_E_le_H {T H H₁ H₂ M M₁ M₂ Pb Np Nm : Subgroup G} {e : Fin 6 → G}
    (D : StepAData T H H₁ H₂ M M₁ M₂ Pb Np Nm e) : Esub e ≤ H := by
  obtain ⟨-, -, h4⟩ := stepA_H_elems D
  unfold Esub
  refine (Subgroup.closure_le _).mpr ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact h4
  · exact stepA_zH D

theorem stepA_Pb_eq {T H H₁ H₂ M M₁ M₂ Pb Np Nm : Subgroup G} {e : Fin 6 → G}
    (D : StepAData T H H₁ H₂ M M₁ M₂ Pb Np Nm e) : Pb = Psub e :=
  (Subgroup.eq_of_le_of_card_ge D.loc.pb.P_le (le_of_eq (by rw [D.pb9, D.hF.card_P]))).symm

theorem stepA_P_inf_E {T H H₁ H₂ M M₁ M₂ Pb Np Nm : Subgroup G} {e : Fin 6 → G}
    (D : StepAData T H H₁ H₂ M M₁ M₂ Pb Np Nm e) : Psub e ⊓ Esub e = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxP, hxE⟩
  rw [Subgroup.mem_bot]
  have hsq : x ^ 2 = 1 := by
    have hxS : x ∈ (Esub e : Set G) := hxE
    rw [(stepA_E D).1] at hxS
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxS
    have hz2 : zOf e ^ 2 = 1 := by rw [pow_two]; exact stepA_z_sq D
    rcases hxS with rfl | rfl | rfl | rfl
    · exact one_pow 2
    · exact (stepA_rels D.setup.lets).2.2.2.2
    · exact hz2
    · rw [Commute.mul_pow (stepA_e4_comm D : Commute (e 4) (zOf e)), (stepA_rels D.setup.lets).2.2.2.2, hz2,
        mul_one]
  exact stepA_eq_one_of_sq_cube hsq (D.hF.elem_P.2 x hxP)

theorem stepA_card_normalizer {T H H₁ H₂ M M₁ M₂ Pb Np Nm : Subgroup G} {e : Fin 6 → G}
    (D : StepAData T H H₁ H₂ M M₁ M₂ Pb Np Nm e) :
    Nat.card (Subgroup.normalizer (Psub e : Set G)) = 36 := by
  have hN : Subgroup.normalizer (Psub e : Set G) = Psub e ⊔ Esub e := by
    rw [D.loc.pb.normalizer_eq, stepA_Pb_eq D]
  have hB : Esub e ≤ Subgroup.normalizer (Psub e : Set G) := by
    rw [hN]; exact le_sup_right
  rw [hN, stepA_card_sup (Psub e) (Esub e) hB (stepA_P_inf_E D), D.hF.card_P, (stepA_E D).2]

theorem stepA_dvd576 {T H H₁ H₂ M M₁ M₂ Pb Np Nm : Subgroup G} {e : Fin 6 → G}
    (D : StepAData T H H₁ H₂ M M₁ M₂ Pb Np Nm e) : 576 ∣ Nat.card G := by
  have h := Subgroup.card_subgroup_dvd_card H
  rwa [D.hF.card_H] at h

theorem stepA_not27 {T H H₁ H₂ M M₁ M₂ Pb Np Nm : Subgroup G} {e : Fin 6 → G}
    (D : StepAData T H H₁ H₂ M M₁ M₂ Pb Np Nm e) : ¬ 27 ∣ Nat.card G := by
  intro h27
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP : Nat.card (Psub e) = 3 ^ 2 := by rw [D.hF.card_P]; norm_num
  have h := Sylow.prime_pow_dvd_card_normalizer (p := 3) (n := 2)
    (by norm_num; exact h27) hP
  rw [stepA_card_normalizer D] at h
  norm_num at h

theorem stepA_P_sylow {T H H₁ H₂ M M₁ M₂ Pb Np Nm : Subgroup G} {e : Fin 6 → G}
    (D : StepAData T H H₁ H₂ M M₁ M₂ Pb Np Nm e) (S : Subgroup G) (hS : IsPGroup 3 S)
    (hPS : Psub e ≤ S) : S = Psub e := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hQ⟩ := hS.exists_le_sylow
  have hn : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have h9 : 3 ^ 2 ∣ Nat.card G := dvd_trans (by norm_num) (stepA_dvd576 D)
  have hA := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hn).mp h9
  have hB : ¬ (3 ≤ (Nat.card G).factorization 3) := by
    intro h
    apply stepA_not27 D
    have h' := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hn).mpr h
    norm_num at h'
    exact h'
  have hfac : (Nat.card G).factorization 3 = 2 := by omega
  have h1 : Nat.card (Q : Subgroup G) = 3 ^ (Nat.card G).factorization 3 :=
    Sylow.card_eq_multiplicity Q
  have hQcard : Nat.card (Q : Subgroup G) = Nat.card (Psub e) := by
    rw [h1, hfac, D.hF.card_P]; norm_num
  have hPQ : Psub e = (Q : Subgroup G) := Subgroup.eq_of_le_of_card_ge (hPS.trans hQ) hQcard.le
  exact le_antisymm (hQ.trans hPQ.ge) hPS

theorem stepA_Np_eq {T H H₁ H₂ M M₁ M₂ Pb Np Nm : Subgroup G} {e : Fin 6 → G}
    (D : StepAData T H H₁ H₂ M M₁ M₂ Pb Np Nm e) : Np = Psub e :=
  stepA_P_sylow D Np D.loc.np.three D.loc.np.P_le

theorem stepA_Nm_eq {T H H₁ H₂ M M₁ M₂ Pb Np Nm : Subgroup G} {e : Fin 6 → G}
    (D : StepAData T H H₁ H₂ M M₁ M₂ Pb Np Nm e) : Nm = Psub e :=
  stepA_P_sylow D Nm D.loc.nm.three D.loc.nm.P_le

theorem stepA_sylow_count {T H H₁ H₂ M M₁ M₂ Pb Np Nm : Subgroup G} {e : Fin 6 → G}
    (D : StepAData T H H₁ H₂ M M₁ M₂ Pb Np Nm e) : Nat.card G / 36 % 3 = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPp : IsPGroup 3 (Psub e) := IsPGroup.of_card (n := 2) (by rw [D.hF.card_P]; norm_num)
  have hdvd : Nat.card (Psub e) * (Psub e).index = Nat.card G := Subgroup.card_mul_index _
  rw [D.hF.card_P] at hdvd
  have hPi : ¬ 3 ∣ (Psub e).index := by
    intro h3
    apply stepA_not27 D
    rw [← hdvd]
    have h27 : 9 * 3 ∣ 9 * (Psub e).index := Nat.mul_dvd_mul_left 9 h3
    norm_num at h27
    exact h27
  have hP'coe : ((IsPGroup.toSylow hPp hPi : Sylow 3 G) : Subgroup G) = Psub e :=
    IsPGroup.toSylow_coe hPp hPi
  have hset : ((IsPGroup.toSylow hPp hPi : Sylow 3 G) : Set G) = (Psub e : Set G) :=
    congrArg (fun K : Subgroup G => (K : Set G)) hP'coe
  have hcount : Nat.card (Sylow 3 G) = (Subgroup.normalizer (Psub e : Set G)).index := by
    rw [Sylow.card_eq_index_normalizer (IsPGroup.toSylow hPp hPi), hset]
  have hidx : (Subgroup.normalizer (Psub e : Set G)).index = Nat.card G / 36 := by
    have h := Subgroup.card_mul_index (Subgroup.normalizer (Psub e : Set G))
    rw [stepA_card_normalizer D] at h
    rw [← h, Nat.mul_div_cancel_left _ (by norm_num)]
  have hmod := card_sylow_modEq_one 3 G
  rw [hcount, hidx] at hmod
  simpa [Nat.ModEq] using hmod

theorem stepA_sylow {T H H₁ H₂ M M₁ M₂ Pb Np Nm : Subgroup G} {e : Fin 6 → G}
    (D : StepAData T H H₁ H₂ M M₁ M₂ Pb Np Nm e) : StepASylow (Nat.card G) := by
  refine ⟨?_, stepA_not27 D, ?_, ?_, ?_, stepA_sylow_count D⟩
  · exact dvd_trans (by norm_num) (stepA_dvd576 D)
  · exact dvd_trans (by norm_num) (stepA_dvd576 D)
  · intro h128
    have hTi : ¬ 2 ∣ T.index := D.setup.ctx.sylow.2
    have hTH : Nat.card T ∣ 576 := by
      have h := Subgroup.card_dvd_of_le D.setup.ctx.tH
      rwa [D.hF.card_H] at h
    have hcop : Nat.Coprime (2 ^ 7) T.index :=
      Nat.Coprime.pow_left 7 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hTi)
    have hdvd := Subgroup.card_mul_index T
    rw [← hdvd] at h128
    have h128' : 2 ^ 7 ∣ Nat.card T * T.index := h128
    have h1 : 2 ^ 7 ∣ Nat.card T := hcop.dvd_of_dvd_mul_right h128'
    have h2 := dvd_trans h1 hTH
    norm_num at h2
  · exact dvd_trans (by norm_num) (stepA_dvd576 D)

theorem stepA_e0_ne_one {T H H₁ H₂ M M₁ M₂ Pb Np Nm : Subgroup G} {e : Fin 6 → G}
    (D : StepAData T H H₁ H₂ M M₁ M₂ Pb Np Nm e) : e 0 ≠ 1 := by
  intro h
  have hle : Psub e ≤ Subgroup.zpowers (e 2) := by
    unfold Psub
    refine (Subgroup.closure_le _).mpr ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · rw [h]; exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _
  have h1 := Subgroup.card_le_of_le hle
  rw [D.hF.card_P, Nat.card_zpowers] at h1
  have hord : orderOf (e 2) ≤ 3 :=
    Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (stepA_rels D.setup.lets).2.1)
  omega

theorem stepA_e2_ne_one {T H H₁ H₂ M M₁ M₂ Pb Np Nm : Subgroup G} {e : Fin 6 → G}
    (D : StepAData T H H₁ H₂ M M₁ M₂ Pb Np Nm e) : e 2 ≠ 1 := by
  intro h
  have hle : Psub e ≤ Subgroup.zpowers (e 0) := by
    unfold Psub
    refine (Subgroup.closure_le _).mpr ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact Subgroup.mem_zpowers _
    · rw [h]; exact Subgroup.one_mem _
  have h1 := Subgroup.card_le_of_le hle
  rw [D.hF.card_P, Nat.card_zpowers] at h1
  have hord : orderOf (e 0) ≤ 3 :=
    Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (stepA_rels D.setup.lets).1)
  omega

theorem stepA_e0_order {T H H₁ H₂ M M₁ M₂ Pb Np Nm : Subgroup G} {e : Fin 6 → G}
    (D : StepAData T H H₁ H₂ M M₁ M₂ Pb Np Nm e) : orderOf (e 0) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime (stepA_rels D.setup.lets).1 (stepA_e0_ne_one D)

theorem stepA_e2_order {T H H₁ H₂ M M₁ M₂ Pb Np Nm : Subgroup G} {e : Fin 6 → G}
    (D : StepAData T H H₁ H₂ M M₁ M₂ Pb Np Nm e) : orderOf (e 2) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime (stepA_rels D.setup.lets).2.1 (stepA_e2_ne_one D)

theorem stepA_card_M1 {T H H₁ H₂ M M₁ M₂ Pb Np Nm : Subgroup G} {e : Fin 6 → G}
    (D : StepAData T H H₁ H₂ M M₁ M₂ Pb Np Nm e) : Nat.card M₁ = 3 := by
  rcases D.loc.cor.cases with h | h | h
  · exact h.1
  · exfalso
    have h2 := h.2
    rw [D.pb9] at h2
    norm_num at h2
  · exfalso
    have h2 := h.2
    rw [D.pb9] at h2
    norm_num at h2

theorem stepA_M1 {T H H₁ H₂ M M₁ M₂ Pb Np Nm : Subgroup G} {e : Fin 6 → G}
    (D : StepAData T H H₁ H₂ M M₁ M₂ Pb Np Nm e) : M₁ = Subgroup.zpowers (e 0) := by
  have hle : Subgroup.zpowers (e 0) ≤ M₁ := by
    have h := (inf_le_left : M₁ ⊓ H ≤ M₁)
    rw [D.loc.v₁.inf_H] at h
    exact h
  exact (Subgroup.eq_of_le_of_card_ge hle
    (le_of_eq (by rw [stepA_card_M1 D, Nat.card_zpowers, stepA_e0_order D]))).symm

theorem stepA_M2 {T H H₁ H₂ M M₁ M₂ Pb Np Nm : Subgroup G} {e : Fin 6 → G}
    (D : StepAData T H H₁ H₂ M M₁ M₂ Pb Np Nm e) : M₂ = Subgroup.zpowers (e 2) := by
  have hcard : Nat.card M₂ = 3 := by
    rw [← D.loc.cor.card_eq]
    exact stepA_card_M1 D
  have hle : Subgroup.zpowers (e 2) ≤ M₂ := by
    have h := (inf_le_left : M₂ ⊓ H ≤ M₂)
    rw [D.loc.v₂.inf_H] at h
    exact h
  exact (Subgroup.eq_of_le_of_card_ge hle
    (le_of_eq (by rw [hcard, Nat.card_zpowers, stepA_e2_order D]))).symm

theorem stepA_v1_le {T H H₁ H₂ M M₁ M₂ Pb Np Nm : Subgroup G} {e : Fin 6 → G}
    (D : StepAData T H H₁ H₂ M M₁ M₂ Pb Np Nm e) : Subgroup.centralizer ({e 0} : Set G) ≤ H := by
  rw [← D.loc.v₁.compl.sup_eq]
  refine sup_le ?_ D.setup.ctx.one.le_two
  rw [stepA_M1 D]
  exact Subgroup.zpowers_le.mpr (stepA_H_elems D).1

theorem stepA_v2_le {T H H₁ H₂ M M₁ M₂ Pb Np Nm : Subgroup G} {e : Fin 6 → G}
    (D : StepAData T H H₁ H₂ M M₁ M₂ Pb Np Nm e) : Subgroup.centralizer ({e 2} : Set G) ≤ H := by
  rw [← D.loc.v₂.compl.sup_eq]
  refine sup_le ?_ D.setup.ctx.one.le_one
  rw [stepA_M2 D]
  exact Subgroup.zpowers_le.mpr (stepA_H_elems D).2.1

theorem stepA_val_neg {K : Subgroup G} (ψ : ↥K ≃* SL(2, ZMod 3)) {x : G} (hx : x ∈ K)
    (hx2 : x * x = 1) (hx1 : x ≠ 1) : (ψ ⟨x, hx⟩).1 = -1 := by
  have hA : ψ ⟨x, hx⟩ * ψ ⟨x, hx⟩ = 1 := by
    rw [← map_mul, show (⟨x, hx⟩ : ↥K) * ⟨x, hx⟩ = 1 from Subtype.ext hx2, map_one]
  have hA1 : ψ ⟨x, hx⟩ ≠ 1 := fun h =>
    hx1 (congrArg Subtype.val (ψ.injective (h.trans (map_one ψ).symm)))
  exact sl_unique_invol _ (ψ ⟨x, hx⟩).2 (congrArg Subtype.val hA) (fun h => hA1 (Subtype.ext h))

theorem stepA_invol_H2 {T H H₁ H₂ M M₁ M₂ Pb Np Nm : Subgroup G} {e : Fin 6 → G}
    (D : StepAData T H H₁ H₂ M M₁ M₂ Pb Np Nm e) {b : G} (hb : b ∈ H₂) (hb2 : b * b = 1)
    (hb1 : b ≠ 1) : b = zOf e := by
  obtain ⟨ψ⟩ := D.setup.ctx.one.iso_two
  have hz2 : zOf e ∈ H₂ := stepA_zH2 D
  have h1 := stepA_val_neg ψ hb hb2 hb1
  have h2 := stepA_val_neg ψ hz2 (stepA_z_sq D) (stepA_z_ne_one D)
  have h3 : ψ ⟨b, hb⟩ = ψ ⟨zOf e, hz2⟩ := Subtype.ext (h1.trans h2.symm)
  exact congrArg Subtype.val (ψ.injective h3)

theorem stepA_invol_H1 {T H H₁ H₂ M M₁ M₂ Pb Np Nm : Subgroup G} {e : Fin 6 → G}
    (D : StepAData T H H₁ H₂ M M₁ M₂ Pb Np Nm e) {b : G} (hb : b ∈ H₁) (hb2 : b * b = 1)
    (hb1 : b ≠ 1) : b = zOf e := by
  obtain ⟨ψ⟩ := D.setup.ctx.one.iso_one
  have hz1' : zOf e ∈ H₁ := stepA_zH1 D
  have h1 := stepA_val_neg ψ hb hb2 hb1
  have h2 := stepA_val_neg ψ hz1' (stepA_z_sq D) (stepA_z_ne_one D)
  have h3 : ψ ⟨b, hb⟩ = ψ ⟨zOf e, hz1'⟩ := Subtype.ext (h1.trans h2.symm)
  exact congrArg Subtype.val (ψ.injective h3)

theorem stepA_comm_zpowers {T H H₁ H₂ M M₁ M₂ Pb Np Nm : Subgroup G} {e : Fin 6 → G}
    (D : StepAData T H H₁ H₂ M M₁ M₂ Pb Np Nm e) {a : G} (ha : a ∈ H) {b : G}
    (hb : b ∈ Subgroup.zpowers (zOf e)) : a * b = b * a := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  exact ((show Commute a (zOf e) from (stepA_H_iff D a).mp ha).zpow_right k).eq

theorem stepAGood_e0 {T H H₁ H₂ M M₁ M₂ Pb Np Nm : Subgroup G} {e : Fin 6 → G}
    (D : StepAData T H H₁ H₂ M M₁ M₂ Pb Np Nm e) : StepAGood H (zOf e) (e 0) := by
  have hC := stepA_v1_le D
  have hzP : Subgroup.zpowers (e 0) ≤ Psub e :=
    Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp [Psub]))
  have hA3 : ∀ a ∈ Subgroup.zpowers (e 0), a ^ 3 = 1 := fun a ha =>
    D.hF.elem_P.2 a (hzP ha)
  have hc : ∀ a ∈ Subgroup.zpowers (e 0), ∀ b ∈ H₂, a * b = b * a := by
    intro a ha b hb
    have hb' : b ∈ Subgroup.centralizer ({e 0} : Set G) ⊓ H := by
      rw [D.hF.cent₁]; exact (le_sup_right : H₂ ≤ Subgroup.zpowers (e 0) ⊔ H₂) hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact ((show Commute b (e 0) from Subgroup.mem_centralizer_singleton_iff.mp hb'.1).zpow_right k).eq.symm
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    exact hC (Subgroup.mem_centralizer_singleton_iff.mpr hg)
  · intro g hg
    have hN := stepA_mem_normalizer hg
    rw [D.loc.v₁.normalizer_eq] at hN
    exact sup_le hC (Subgroup.zpowers_le.mpr (stepA_H_elems D).2.2) hN
  · intro u hu hu2 hu1 huy
    have huC : u ∈ Subgroup.centralizer ({e 0} : Set G) ⊓ H :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr huy, hu⟩
    rw [D.hF.cent₁] at huC
    have huB := stepA_mem_of_sup hc D.hF.disj₁ hA3 huC hu2
    exact stepA_invol_H2 D huB hu2 hu1

theorem stepAGood_e2 {T H H₁ H₂ M M₁ M₂ Pb Np Nm : Subgroup G} {e : Fin 6 → G}
    (D : StepAData T H H₁ H₂ M M₁ M₂ Pb Np Nm e) : StepAGood H (zOf e) (e 2) := by
  have hC := stepA_v2_le D
  have hzP : Subgroup.zpowers (e 2) ≤ Psub e :=
    Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp [Psub]))
  have hA3 : ∀ a ∈ Subgroup.zpowers (e 2), a ^ 3 = 1 := fun a ha =>
    D.hF.elem_P.2 a (hzP ha)
  have hc : ∀ a ∈ Subgroup.zpowers (e 2), ∀ b ∈ H₁, a * b = b * a := by
    intro a ha b hb
    have hb' : b ∈ Subgroup.centralizer ({e 2} : Set G) ⊓ H := by
      rw [D.hF.cent₂]; exact (le_sup_right : H₁ ≤ Subgroup.zpowers (e 2) ⊔ H₁) hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact ((show Commute b (e 2) from Subgroup.mem_centralizer_singleton_iff.mp hb'.1).zpow_right k).eq.symm
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    exact hC (Subgroup.mem_centralizer_singleton_iff.mpr hg)
  · intro g hg
    have hN := stepA_mem_normalizer hg
    rw [D.loc.v₂.normalizer_eq] at hN
    exact sup_le hC (Subgroup.zpowers_le.mpr (stepA_H_elems D).2.2) hN
  · intro u hu hu2 hu1 huy
    have huC : u ∈ Subgroup.centralizer ({e 2} : Set G) ⊓ H :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr huy, hu⟩
    rw [D.hF.cent₂] at huC
    have huB := stepA_mem_of_sup hc D.hF.disj₂ hA3 huC hu2
    exact stepA_invol_H1 D huB hu2 hu1

theorem stepAGood_mix {T H H₁ H₂ M M₁ M₂ Pb Np Nm : Subgroup G} {e : Fin 6 → G}
    (D : StepAData T H H₁ H₂ M M₁ M₂ Pb Np Nm e) : StepAGood H (zOf e) (e 0 * e 2) := by
  have hNp : Np = Psub e := stepA_Np_eq D
  have hCH : Subgroup.centralizer ({e 0 * e 2} : Set G) ≤ H := by
    rw [← D.loc.np.compl.sup_eq, hNp]
    exact sup_le (stepA_P_le_H D) (Subgroup.zpowers_le.mpr (stepA_zH D))
  have hA3 : ∀ a ∈ Psub e, a ^ 3 = 1 := fun a ha => D.hF.elem_P.2 a ha
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    exact hCH (Subgroup.mem_centralizer_singleton_iff.mpr hg)
  · intro g hg
    have hN := stepA_mem_normalizer hg
    rw [D.loc.np.normalizer_eq, hNp] at hN
    exact sup_le (stepA_P_le_H D) (stepA_E_le_H D) hN
  · intro u hu hu2 hu1 huy
    have huC : u ∈ Subgroup.centralizer ({e 0 * e 2} : Set G) ⊓ H :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr huy, hu⟩
    rw [D.hF.centYp] at huC
    have hAB : Psub e ⊓ Subgroup.zpowers (zOf e) = ⊥ :=
      stepA_inf_zpowers hA3 (stepA_z_sq D) (stepA_z_ne_one D)
    have huZ := stepA_mem_of_sup
      (fun a ha b hb => stepA_comm_zpowers D (stepA_P_le_H D ha) hb) hAB hA3 huC hu2
    rcases stepA_mem_zpowers_cases (stepA_z_sq D) (stepA_z_ne_one D) huZ with h | h
    · exact absurd h hu1
    · exact h

theorem stepAGood_mix' {T H H₁ H₂ M M₁ M₂ Pb Np Nm : Subgroup G} {e : Fin 6 → G}
    (D : StepAData T H H₁ H₂ M M₁ M₂ Pb Np Nm e) : StepAGood H (zOf e) (e 0 * (e 2)⁻¹) := by
  have hNm : Nm = Psub e := stepA_Nm_eq D
  have hCH : Subgroup.centralizer ({e 0 * (e 2)⁻¹} : Set G) ≤ H := by
    rw [← D.loc.nm.compl.sup_eq, hNm]
    exact sup_le (stepA_P_le_H D) (Subgroup.zpowers_le.mpr (stepA_zH D))
  have hA3 : ∀ a ∈ Psub e, a ^ 3 = 1 := fun a ha => D.hF.elem_P.2 a ha
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    exact hCH (Subgroup.mem_centralizer_singleton_iff.mpr hg)
  · intro g hg
    have hN := stepA_mem_normalizer hg
    rw [D.loc.nm.normalizer_eq, hNm] at hN
    exact sup_le (stepA_P_le_H D) (stepA_E_le_H D) hN
  · intro u hu hu2 hu1 huy
    have huC : u ∈ Subgroup.centralizer ({e 0 * (e 2)⁻¹} : Set G) ⊓ H :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr huy, hu⟩
    rw [D.hF.centYm] at huC
    have hAB : Psub e ⊓ Subgroup.zpowers (zOf e) = ⊥ :=
      stepA_inf_zpowers hA3 (stepA_z_sq D) (stepA_z_ne_one D)
    have huZ := stepA_mem_of_sup
      (fun a ha b hb => stepA_comm_zpowers D (stepA_P_le_H D ha) hb) hAB hA3 huC hu2
    rcases stepA_mem_zpowers_cases (stepA_z_sq D) (stepA_z_ne_one D) huZ with h | h
    · exact absurd h hu1
    · exact h

theorem stepA_P_form {e0 e2 : G} (hcomm : e2 * e0 = e0 * e2) {x : G}
    (hx : x ∈ Subgroup.closure ({e0, e2} : Set G)) : ∃ m n : ℤ, x = e0 ^ m * e2 ^ n := by
  have hc0 : Commute e0 e2 := hcomm.symm
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨1, 0, by simp⟩
    · exact ⟨0, 1, by simp⟩
  | one => exact ⟨0, 0, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨m, n, rfl⟩ := hx
    obtain ⟨m', n', rfl⟩ := hy
    refine ⟨m + m', n + n', ?_⟩
    have hcom : Commute (e2 ^ n) (e0 ^ m') := ((hc0.symm).zpow_left n).zpow_right m'
    calc e0 ^ m * e2 ^ n * (e0 ^ m' * e2 ^ n') = e0 ^ m * (e2 ^ n * e0 ^ m') * e2 ^ n' := by group
      _ = e0 ^ m * (e0 ^ m' * e2 ^ n) * e2 ^ n' := by rw [hcom.eq]
      _ = e0 ^ (m + m') * e2 ^ (n + n') := by rw [zpow_add, zpow_add]; group
  | inv x _ hx =>
    obtain ⟨m, n, rfl⟩ := hx
    refine ⟨-m, -n, ?_⟩
    have hcom : Commute (e2 ^ (-n)) (e0 ^ (-m)) := ((hc0.symm).zpow_left (-n)).zpow_right (-m)
    calc (e0 ^ m * e2 ^ n)⁻¹ = (e2 ^ n)⁻¹ * (e0 ^ m)⁻¹ := mul_inv_rev _ _
      _ = e2 ^ (-n) * e0 ^ (-m) := by rw [zpow_neg, zpow_neg]
      _ = e0 ^ (-m) * e2 ^ (-n) := hcom.eq

theorem stepAGood_P {T H H₁ H₂ M M₁ M₂ Pb Np Nm : Subgroup G} {e : Fin 6 → G}
    (D : StepAData T H H₁ H₂ M M₁ M₂ Pb Np Nm e) {x : G} (hx : x ∈ Psub e) (hx1 : x ≠ 1) :
    StepAGood H (zOf e) x := by
  obtain ⟨C0, C2, hcomm, -, -⟩ := stepA_rels D.setup.lets
  have hord0 := stepA_e0_order D
  have hord2 := stepA_e2_order D
  obtain ⟨m, n, hxmn⟩ := stepA_P_form hcomm hx
  have hm : e 0 ^ (m % 3) = e 0 ^ m := by
    have h := zpow_mod_orderOf (e 0) m
    rw [hord0] at h
    simpa using h
  have hn : e 2 ^ (n % 3) = e 2 ^ n := by
    have h := zpow_mod_orderOf (e 2) n
    rw [hord2] at h
    simpa using h
  have hx' : x = e 0 ^ (m % 3) * e 2 ^ (n % 3) := by rw [hm, hn, hxmn]
  obtain ⟨a, ha⟩ : ∃ a : ℤ, a = m % 3 := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℤ, b = n % 3 := ⟨_, rfl⟩
  rw [← ha, ← hb] at hx'
  have ha0 : 0 ≤ a := by omega
  have ha3 : a < 3 := by omega
  have hb0 : 0 ≤ b := by omega
  have hb3 : b < 3 := by omega
  have hc0 : Commute (e 0) (e 2) := hcomm.symm
  have hinv2 : (e 2)⁻¹ = e 2 ^ 2 :=
    inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact C2)
  have hinvsq : (e 2)⁻¹ ^ 2 = e 2 := by
    rw [hinv2]
    calc (e 2 ^ 2) ^ 2 = e 2 * e 2 ^ 3 := by group
      _ = e 2 := by rw [C2, mul_one]
  have G0 := stepAGood_e0 D
  have G2 := stepAGood_e2 D
  have GM := stepAGood_mix D
  have GM' := stepAGood_mix' D
  have CM : (e 0 * e 2) ^ 3 = 1 := by rw [hc0.mul_pow, C0, C2, one_mul]
  have CM' : (e 0 * (e 2)⁻¹) ^ 3 = 1 := by
    rw [hc0.inv_right.mul_pow, inv_pow, C0, C2, inv_one, one_mul]
  interval_cases a <;> interval_cases b
  · exfalso
    apply hx1
    simpa using hx'
  · have hx2 : x = e 2 := by simpa using hx'
    rw [hx2]
    exact G2
  · exact stepAGood_of_pow G2 C2 (k := 2) (Or.inr rfl) (by simpa using hx')
  · have hx2 : x = e 0 := by simpa using hx'
    rw [hx2]
    exact G0
  · have hx2 : x = e 0 * e 2 := by simpa using hx'
    rw [hx2]
    exact GM
  · have hx2 : x = e 0 * (e 2)⁻¹ := by
      rw [hinv2]
      simpa using hx'
    rw [hx2]
    exact GM'
  · exact stepAGood_of_pow G0 C0 (k := 2) (Or.inr rfl) (by simpa using hx')
  · have hx2 : x = (e 0 * (e 2)⁻¹) ^ 2 := by
      rw [hc0.inv_right.mul_pow, hinvsq]
      simpa using hx'
    exact stepAGood_of_pow GM' CM' (k := 2) (Or.inr rfl) hx2
  · have hx2 : x = (e 0 * e 2) ^ 2 := by
      rw [hc0.mul_pow]
      simpa using hx'
    exact stepAGood_of_pow GM CM (k := 2) (Or.inr rfl) hx2

theorem stepAGood_of_order3 {T H H₁ H₂ M M₁ M₂ Pb Np Nm : Subgroup G} {e : Fin 6 → G}
    (D : StepAData T H H₁ H₂ M M₁ M₂ Pb Np Nm e) {x : G} (hx : x ∈ H) (h3 : x ^ 3 = 1)
    (h1 : x ≠ 1) : StepAGood H (zOf e) x := by
  obtain ⟨h, hh, hcj⟩ := D.hF.order3 x hx h3 h1
  have hy1 : h * x * h⁻¹ ≠ 1 := by
    intro h'
    apply h1
    calc x = h⁻¹ * (h * x * h⁻¹) * h := by group
      _ = 1 := by rw [h']; group
  exact stepAGood_conj hh (fun g hg => (stepA_H_iff D g).mp hg) (stepAGood_P D hcj hy1)

theorem stepA_special {T H H₁ H₂ M M₁ M₂ Pb Np Nm : Subgroup G} {e : Fin 6 → G}
    (D : StepAData T H H₁ H₂ M M₁ M₂ Pb Np Nm e) : SpecialSet e H := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro x ⟨hxH, hx⟩ g hg
    rcases hx with ⟨h3, h1⟩ | ⟨k, -, -, hpow⟩
    · exact (stepAGood_of_order3 D hxH h3 h1).1 g (Subgroup.mem_centralizer_singleton_iff.mp hg)
    · refine (stepA_H_iff D g).mpr ?_
      have hc : Commute g x := Subgroup.mem_centralizer_singleton_iff.mp hg
      rw [← hpow]
      exact (hc.pow_right k).eq
  · rintro x hx y hy hxy
    obtain ⟨hxH, hx⟩ := hx
    obtain ⟨hyH, hy⟩ := hy
    obtain ⟨g, hg⟩ := isConj_iff.mp hxy
    have hsc : SemiconjBy g x y := by
      unfold SemiconjBy
      rw [← hg]
      group
    have hord := SemiconjBy.orderOf_eq g hsc
    rcases hx with ⟨h3x, h1x⟩ | ⟨k, hk, hordx, hpowx⟩ <;>
      rcases hy with ⟨h3y, h1y⟩ | ⟨m, hm, hordy, hpowy⟩
    ·
      have hGy := stepAGood_of_order3 D hyH h3y h1y
      have hzx : x * zOf e = zOf e * x := (stepA_H_iff D x).mp hxH
      have hz'y : g * zOf e * g⁻¹ * y = y * (g * zOf e * g⁻¹) := by
        rw [← hg]
        calc g * zOf e * g⁻¹ * (g * x * g⁻¹) = g * (zOf e * x) * g⁻¹ := by group
          _ = g * (x * zOf e) * g⁻¹ := by rw [← hzx]
          _ = g * x * g⁻¹ * (g * zOf e * g⁻¹) := by group
      have hz'H : g * zOf e * g⁻¹ ∈ H := hGy.1 _ hz'y
      have hz'2 : g * zOf e * g⁻¹ * (g * zOf e * g⁻¹) = 1 := by
        calc g * zOf e * g⁻¹ * (g * zOf e * g⁻¹) = g * (zOf e * zOf e) * g⁻¹ := by group
          _ = 1 := by rw [stepA_z_sq D]; group
      have hz'1 : g * zOf e * g⁻¹ ≠ 1 := by
        intro h
        apply stepA_z_ne_one D
        calc zOf e = g⁻¹ * (g * zOf e * g⁻¹) * g := by group
          _ = 1 := by rw [h]; group
      have hz'z : g * zOf e * g⁻¹ = zOf e := hGy.2.2 _ hz'H hz'2 hz'1 hz'y
      exact ⟨g, (stepA_H_iff D g).mpr (mul_inv_eq_iff_eq_mul.mp hz'z), hg⟩
    ·
      exfalso
      have hx3 : orderOf x = 3 := orderOf_eq_prime h3x h1x
      rw [hx3, hordy] at hord
      omega
    ·
      exfalso
      have hy3 : orderOf y = 3 := orderOf_eq_prime h3y h1y
      rw [hordx, hy3] at hord
      omega
    ·
      rw [hordx, hordy] at hord
      have hkm : k = m := by omega
      have h1 : g * zOf e * g⁻¹ = zOf e := by
        calc g * zOf e * g⁻¹ = g * x ^ k * g⁻¹ := by rw [hpowx]
          _ = (g * x * g⁻¹) ^ k := conj_pow.symm
          _ = y ^ k := by rw [hg]
          _ = y ^ m := by rw [hkm]
          _ = zOf e := hpowy
      exact ⟨g, (stepA_H_iff D g).mpr (mul_inv_eq_iff_eq_mul.mp h1), hg⟩
  · rintro x ⟨hxH, hx⟩ u _ hux
    rcases hx with ⟨h3, h1⟩ | ⟨k, -, -, hpow⟩
    · exact (stepAGood_of_order3 D hxH h3 h1).2.1 u hux
    · refine (stepA_H_iff D u).mpr ?_
      have h1 : u * zOf e * u⁻¹ = zOf e := by
        calc u * zOf e * u⁻¹ = u * x ^ k * u⁻¹ := by rw [hpow]
          _ = (u * x * u⁻¹) ^ k := conj_pow.symm
          _ = (x⁻¹) ^ k := by rw [hux]
          _ = (x ^ k)⁻¹ := inv_pow x k
          _ = zOf e := by rw [hpow, inv_eq_of_mul_eq_one_right (stepA_z_sq D)]
      exact mul_inv_eq_iff_eq_mul.mp h1
  · intro h hh
    rw [D.setup.ctx.one.eq_centralizer] at hh
    have hz : zOf e ∈ ((H₁ ⊓ H₂ : Subgroup G) : Set G) :=
      Subgroup.mem_inf.mpr ⟨stepA_zH1 D, stepA_zH2 D⟩
    rw [← (Subgroup.mem_centralizer_iff.mp hh) (zOf e) hz, mul_inv_cancel_right]

theorem stepA_main {T H H₁ H₂ M M₁ M₂ Pb Np Nm : Subgroup G} {e : Fin 6 → G}
    (D : StepAData T H H₁ H₂ M M₁ M₂ Pb Np Nm e) : SpecialSet e H ∧ StepASylow (Nat.card G) :=
  ⟨stepA_special D, stepA_sylow D⟩

end Specific

theorem leafStepALocal : LeafStepALocal := by
  intro G _ _ T H H₁ H₂ M e M₁ M₂ Pb Np Nm h hF hO hL hPb
  exact stepA_main ⟨h, hF, hO, hL, hPb⟩

end CFSG.GH74.QTGen4.Recog.G23.P7
