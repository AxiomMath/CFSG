module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD46Sec4
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7C2d

public section

namespace CFSG.ComponentClassification.HSFLit.KD46

open CFSG Subgroup Equiv L2K L2KD

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : L2Data t L}
  {C : A.CaseKD} (S : KDBase A C)

@[expose] def Fus : Prop :=
  ∀ b ∈ S.B, ConjTo t b ↔ b = t ∨ b = t * S.z ∨ b = t * S.k ∨ b = t * S.z * S.k

theorem conjTo_wB_iff' (hO : Fus S) (v : Fin 2 × Fin 2 × Fin 2) :
    ConjTo t (wB S v) ↔ v.2.1 = 1 := by
  have f : ∀ {u : X} {w : Fin 2 × Fin 2 × Fin 2}, u = wB S w → (wB S v = u ↔ v = w) :=
    fun {u w} he => ⟨fun h => wB_injective S (h.trans he), fun h => h ▸ he.symm⟩
  have e1 : t = wB S (0, 1, 0) := by simp [wB]
  have e2 : t * S.z = wB S (1, 1, 0) := by simp [wB, z_comm_t S]
  have e5 : t * S.k = wB S (0, 1, 1) := by simp [wB]
  have e6 : t * S.z * S.k = wB S (1, 1, 1) := by simp [wB, z_comm_t S]
  rw [hO _ (wB_mem S v), f e1, f e2, f e5, f e6]
  clear f e1 e2 e5 e6
  obtain ⟨a, b, c⟩ := v
  revert a b c
  decide

structure Inst where
  yi : X
  ki : X
  ui : X
  spec : (yi = S.y ∧ ki = S.k ∧ ui = S.x * S.y) ∨
    (yi = S.x * S.y ∧ ki = S.z * S.k ∧ ui = S.z * S.y)

@[expose] def inst₁ : Inst S := ⟨S.y, S.k, S.x * S.y, Or.inl ⟨rfl, rfl, rfl⟩⟩

@[expose] def inst₂ : Inst S := ⟨S.x * S.y, S.z * S.k, S.z * S.y, Or.inr ⟨rfl, rfl, rfl⟩⟩

namespace Inst

variable {S} (I : Inst S)

theorem yi_or : I.yi = S.y ∨ I.yi = S.x * S.y := by
  rcases I.spec with ⟨h, -⟩ | ⟨h, -⟩
  · exact Or.inl h
  · exact Or.inr h

theorem yi_mem : I.yi ∈ A.R := by
  rcases I.yi_or with h | h <;> rw [h]
  · exact S.y_mem
  · exact xy_mem S

theorem yi_sq : I.yi ^ 2 = 1 := by
  rcases I.yi_or with h | h <;> rw [h]
  · exact S.y_sq
  · exact xy_sq S

theorem yi_not_mem_B : I.yi ∉ S.B := by
  rcases I.yi_or with h | h <;> rw [h]
  · exact y_not_mem_B S
  · exact xy_not_mem_B S

@[expose] noncomputable def E : Subgroup X := S.E I.yi

theorem z_mem_E : S.z ∈ I.E := mem_E_z S _

theorem yi_mem_E : I.yi ∈ I.E := mem_E_yi S _

theorem t_mem_E : t ∈ I.E := mem_E_t S _

theorem k_mem_E : S.k ∈ I.E := mem_E_k S _

theorem ki_eq : I.ki = S.k ∨ I.ki = S.z * S.k := by
  rcases I.spec with ⟨-, h, -⟩ | ⟨-, h, -⟩
  · exact Or.inl h
  · exact Or.inr h

theorem ki_mem_E : I.ki ∈ I.E := by
  rcases I.ki_eq with h | h <;> rw [h]
  · exact I.k_mem_E
  · exact mul_mem I.z_mem_E I.k_mem_E

theorem ki_mem_B : I.ki ∈ S.B := by
  rcases I.ki_eq with h | h <;> rw [h]
  · exact mem_B_k S
  · exact mul_mem (mem_B_z S) (mem_B_k S)

theorem E_le_T : I.E ≤ A.T := KD46.E_le_T S _ I.yi_mem

theorem E_le_TE : I.E ≤ S.TE := KD46.E_le_TE S I.yi_mem

theorem B_le_E : S.B ≤ I.E := KD46.B_le_E S _

theorem comm {a b : X} (ha : a ∈ I.E) (hb : b ∈ I.E) : a * b = b * a := E_comm S I.yi_mem ha hb

theorem sq_eq_one {a : X} (ha : a ∈ I.E) : a ^ 2 = 1 := E_sq S I.yi_mem I.yi_sq ha

theorem ki_sq : I.ki ^ 2 = 1 := I.sq_eq_one I.ki_mem_E

theorem card_E : Nat.card I.E = 16 := KD46.card_E S I.yi_mem I.yi_sq I.yi_not_mem_B

theorem E_or : I.E = S.E S.y ∨ I.E = S.E (S.x * S.y) := by
  rcases I.yi_or with h | h
  · exact Or.inl (by rw [E, h])
  · exact Or.inr (by rw [E, h])

@[expose] noncomputable def wV (v : V4) : X :=
  S.z ^ (v.1 : ℕ) * I.yi ^ (v.2.1 : ℕ) * t ^ (v.2.2.1 : ℕ) * I.ki ^ (v.2.2.2 : ℕ)

theorem wV_mem (v : V4) : I.wV v ∈ I.E :=
  mul_mem (mul_mem (mul_mem (pow_mem I.z_mem_E _) (pow_mem I.yi_mem_E _)) (pow_mem I.t_mem_E _))
    (pow_mem I.ki_mem_E _)

theorem wV_add (v w : V4) : I.wV (addV v w) = I.wV v * I.wV w := by
  have hc : ∀ {p q : X}, p ∈ I.E → q ∈ I.E → p * q = q * p := fun hp hq => I.comm hp hq
  have hz := I.z_mem_E
  have hy := I.yi_mem_E
  have ht := I.t_mem_E
  have hk := I.ki_mem_E
  obtain ⟨a, b, c, d⟩ := v
  obtain ⟨a', b', c', d'⟩ := w
  simp only [wV, addV]
  rw [pow_fin_add (z_sq S), pow_fin_add I.yi_sq, pow_fin_add (t_sq' (A := A)),
    pow_fin_add I.ki_sq]
  set A' := S.z ^ (a' : ℕ)
  set B := I.yi ^ (b : ℕ)
  set B' := I.yi ^ (b' : ℕ)
  set Cc := t ^ (c : ℕ)
  set C' := t ^ (c' : ℕ)
  set D := I.ki ^ (d : ℕ)
  have hA' : A' ∈ I.E := pow_mem hz _
  have hB : B ∈ I.E := pow_mem hy _
  have hB' : B' ∈ I.E := pow_mem hy _
  have hC : Cc ∈ I.E := pow_mem ht _
  have hC' : C' ∈ I.E := pow_mem ht _
  have hD : D ∈ I.E := pow_mem hk _
  symm
  calc S.z ^ (a : ℕ) * B * Cc * D * (A' * B' * C' * I.ki ^ (d' : ℕ))
      = S.z ^ (a : ℕ) * (B * Cc * D * A') * (B' * C' * I.ki ^ (d' : ℕ)) := by group
    _ = S.z ^ (a : ℕ) * (A' * (B * Cc * D)) * (B' * C' * I.ki ^ (d' : ℕ)) := by
        rw [hc (mul_mem (mul_mem hB hC) hD) hA']
    _ = S.z ^ (a : ℕ) * A' * B * (Cc * D * B') * (C' * I.ki ^ (d' : ℕ)) := by group
    _ = S.z ^ (a : ℕ) * A' * B * (B' * (Cc * D)) * (C' * I.ki ^ (d' : ℕ)) := by
        rw [hc (mul_mem hC hD) hB']
    _ = S.z ^ (a : ℕ) * A' * (B * B') * Cc * (D * C') * I.ki ^ (d' : ℕ) := by group
    _ = S.z ^ (a : ℕ) * A' * (B * B') * Cc * (C' * D) * I.ki ^ (d' : ℕ) := by rw [hc hD hC']
    _ = S.z ^ (a : ℕ) * A' * (B * B') * (Cc * C') * (D * I.ki ^ (d' : ℕ)) := by group

theorem wV_zero : I.wV (0, 0, 0, 0) = 1 := by simp [wV]

theorem eq_wV {e : X} (he : e ∈ I.E) : ∃ v : V4, e = I.wV v := by
  obtain ⟨a, b, c, l, ha, hb, hc, hl, rfl⟩ := eq_of_mem_E S I.yi_mem I.yi_sq he
  rcases I.ki_eq with hk | hk
  · refine ⟨(⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, ⟨l, hl⟩), ?_⟩
    simp only [wV, hk]
  ·
    have hzk : Commute S.z S.k := z_comm_k S
    refine ⟨(⟨a, ha⟩ + ⟨l, hl⟩, ⟨b, hb⟩, ⟨c, hc⟩, ⟨l, hl⟩), ?_⟩
    simp only [wV, hk]
    rw [pow_fin_add (z_sq S), hzk.mul_pow]
    have hzy : Commute S.z (I.yi ^ b * t ^ c) :=
      ((show Commute S.z I.yi from z_comm S I.yi_mem.1).pow_right b).mul_right
        ((show Commute S.z t from z_comm_t S).pow_right c)
    have hzl : S.z ^ l * S.z ^ l = 1 := by
      rw [← pow_add, ← two_mul, pow_mul, z_sq S, one_pow]
    calc S.z ^ a * I.yi ^ b * t ^ c * S.k ^ l
        = S.z ^ a * (S.z ^ l * S.z ^ l) * (I.yi ^ b * t ^ c) * S.k ^ l := by rw [hzl]; group
      _ = S.z ^ a * S.z ^ l * (S.z ^ l * (I.yi ^ b * t ^ c)) * S.k ^ l := by group
      _ = S.z ^ a * S.z ^ l * ((I.yi ^ b * t ^ c) * S.z ^ l) * S.k ^ l := by
          rw [(hzy.pow_left l).eq]
      _ = _ := by group

theorem wV_injective {v w : V4} (h : I.wV v = I.wV w) : v = w := by
  classical
  let f : V4 → I.E := fun v => ⟨I.wV v, I.wV_mem v⟩
  have hsurj : Function.Surjective f := by
    rintro ⟨e, he⟩
    obtain ⟨v, rfl⟩ := I.eq_wV he
    exact ⟨v, rfl⟩
  have hcard : Nat.card V4 = Nat.card I.E := by
    rw [I.card_E, Nat.card_eq_fintype_card]
    rfl
  have hinj : Function.Injective f :=
    (Function.Surjective.bijective_of_nat_card_le hsurj hcard.le).1
  exact hinj (Subtype.ext h)

theorem wV_smul (a : Fin 2) (v : V4) : I.wV (smulV a v) = I.wV v ^ (a : ℕ) := by
  fin_cases a
  · simp [smulV, wV]
  · simp [smulV]

theorem wV_zero_eq (a c d : Fin 2) : ∃ a' : Fin 2, I.wV (a, 0, c, d) = wB S (a', c, d) := by
  rcases I.ki_eq with hk | hk
  · exact ⟨a, by simp [wV, wB, hk]⟩
  · refine ⟨a + d, ?_⟩
    simp only [wV, wB, hk, Fin.val_zero, pow_zero, mul_one]
    rw [pow_fin_add (z_sq S), (show Commute S.z S.k from z_comm_k S).mul_pow]
    have h1 : t ^ (c : ℕ) * S.z ^ (d : ℕ) = S.z ^ (d : ℕ) * t ^ (c : ℕ) :=
      (((show Commute S.z t from z_comm_t S).pow_right c).pow_left d).eq.symm
    calc S.z ^ (a : ℕ) * t ^ (c : ℕ) * (S.z ^ (d : ℕ) * S.k ^ (d : ℕ))
        = S.z ^ (a : ℕ) * (t ^ (c : ℕ) * S.z ^ (d : ℕ)) * S.k ^ (d : ℕ) := by group
      _ = S.z ^ (a : ℕ) * S.z ^ (d : ℕ) * t ^ (c : ℕ) * S.k ^ (d : ℕ) := by rw [h1]; group

omit [Finite X] in
theorem t_conj_of_mem_C {g : X} (hg : g ∈ centralizer ({t} : Set X)) : g * t * g⁻¹ = t := by
  rw [mem_centralizer_singleton_iff.mp hg, mul_inv_cancel_right]

theorem exists_d : ∃ d ∈ normalizer (I.E : Set X) ⊓ centralizer ({t} : Set X),
    d * S.z * d⁻¹ = I.yi ∧ d * I.yi * d⁻¹ = S.z * I.yi ∧ d * I.ki * d⁻¹ = I.ki := by
  obtain ⟨yi, ki, ui, h⟩ := I
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · obtain ⟨g, hgC, hgN, h1, h2, h3⟩ := S.d_y
    exact ⟨g, mem_inf.mpr ⟨hgN, hgC⟩, h1, h2, h3⟩
  · obtain ⟨g, hgC, hgN, h1, h2, h3⟩ := S.d_xy
    exact ⟨g, mem_inf.mpr ⟨hgN, hgC⟩, h1, h2, h3⟩

theorem conjTo_wV_iff (hO : Fus S) (v : V4) : ConjTo t (I.wV v) ↔ v.2.2.1 = 1 := by
  have hB : ∀ a c d : Fin 2, ConjTo t (I.wV (a, 0, c, d)) ↔ c = 1 := by
    intro a c d
    obtain ⟨a', h⟩ := I.wV_zero_eq a c d
    rw [h, conjTo_wB_iff' S hO]
  obtain ⟨a, b, c, d⟩ := v
  rcases Fin.exists_fin_two.mp ⟨b, rfl⟩ with rfl | rfl
  · exact hB a c d
  ·
    obtain ⟨g, hg, hgz, hgy, hgk⟩ := I.exists_d
    have hgt := t_conj_of_mem_C (mem_inf.mp hg).2
    set f := t ^ (c : ℕ) * I.ki ^ (d : ℕ) with hf
    have hgf : g * f * g⁻¹ = f := by
      calc g * f * g⁻¹ = (g * t * g⁻¹) ^ (c : ℕ) * (g * I.ki * g⁻¹) ^ (d : ℕ) := by
            rw [conj_pow, conj_pow, hf]; group
        _ = f := by rw [hgt, hgk]
    have hw1 : I.wV (1, 0, c, d) = S.z * f := by simp [wV, hf, mul_assoc]
    have hconj : ∀ {u v : X} (h : X), h * u * h⁻¹ = v → (ConjTo t u ↔ ConjTo t v) := by
      intro u v h huv
      rw [← huv]
      exact (conjTo_conj_iff t u h).symm
    rw [← hB 1 c d]
    rcases Fin.exists_fin_two.mp ⟨a, rfl⟩ with rfl | rfl
    · have hw : I.wV (0, 1, c, d) = I.yi * f := by simp [wV, hf, mul_assoc]
      rw [hw, hw1]
      refine hconj g⁻¹ ?_
      have h1 : g⁻¹ * I.yi * g = S.z := by
        calc g⁻¹ * I.yi * g = g⁻¹ * (g * S.z * g⁻¹) * g := by rw [hgz]
          _ = S.z := by group
      have h2 : g⁻¹ * f * g = f := by
        calc g⁻¹ * f * g = g⁻¹ * (g * f * g⁻¹) * g := by rw [hgf]
          _ = f := by group
      calc g⁻¹ * (I.yi * f) * g⁻¹⁻¹ = (g⁻¹ * I.yi * g) * (g⁻¹ * f * g) := by group
        _ = S.z * f := by rw [h1, h2]
    · have hw : I.wV (1, 1, c, d) = S.z * I.yi * f := by simp [wV, hf, mul_assoc]
      rw [hw, hw1]
      refine hconj g ?_
      have hyzy : I.yi * (S.z * I.yi) = S.z := by
        calc I.yi * (S.z * I.yi) = S.z * (I.yi * I.yi) := by
              rw [← mul_assoc, ← z_comm S I.yi_mem.1, mul_assoc]
          _ = S.z := by rw [← pow_two, I.yi_sq, mul_one]
      calc g * (S.z * I.yi * f) * g⁻¹ = (g * S.z * g⁻¹) * (g * I.yi * g⁻¹) * (g * f * g⁻¹) := by
            group
        _ = S.z * f := by rw [hgz, hgy, hgf, hyzy]

end Inst

end CFSG.ComponentClassification.HSFLit.KD46
