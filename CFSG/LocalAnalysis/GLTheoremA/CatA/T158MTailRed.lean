module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MRed

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

@[expose] def T158NormConj (Q : TauCeti.CFSGIndex → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ) (K B : Subgroup X) (x₁ x₂ : X) (L₁ L₂ : Subgroup X),
    catalogIs (PSimple p K) Q → T158Hyp p K B x₁ x₂ L₁ L₂ → T158Concl15 p K B x₂ L₁ →
      ∀ (g : X), ∀ b ∈ B, ∀ y : X, g * y * g⁻¹ ∈ K ↔ g * (b * y * b⁻¹) * g⁻¹ ∈ K

@[expose] def T158TailFaith (Q : TauCeti.CFSGIndex → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ) (K B : Subgroup X) (x₁ x₂ : X) (L₁ L₂ : Subgroup X),
    catalogIs (PSimple p K) Q → T158Hyp p K B x₁ x₂ L₁ L₂ → T158Concl15 p K B x₂ L₁ →
      ∀ T : Subgroup X, IsPGroup 2 T → B ≤ Subgroup.normalizer (T : Set X) →
        T ≤ centModSubgroup p K → T = ⊥

@[expose] def T158TailModel (Q : TauCeti.CFSGIndex → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ) (K B : Subgroup X) (x₁ x₂ : X) (L₁ L₂ : Subgroup X),
    catalogIs (PSimple p K) Q → T158Hyp p K B x₁ x₂ L₁ L₂ → T158Concl15 p K B x₂ L₁ →
      ∀ T : Subgroup X, IsPGroup 2 T → T ≤ Subgroup.normalizer (K : Set X) →
        B ≤ Subgroup.normalizer (T : Set X) → (⁅T, B⁆ : Subgroup X) ≤ centModSubgroup p K

section Comm

variable {X : Type} [Group X]

private theorem commutator_le_of_normalizes {T B : Subgroup X} (hBT : B ≤ Subgroup.normalizer (T : Set X)) :
    (⁅T, B⁆ : Subgroup X) ≤ T := by
  rw [Subgroup.commutator_le]
  intro t ht b hb
  have h1 : b * t⁻¹ * b⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp (hBT hb) t⁻¹).mp (T.inv_mem ht)
  rw [commutatorElement_def, mul_assoc, mul_assoc, ← mul_assoc b]
  exact T.mul_mem ht h1

private theorem le_normalizer_commutator {T B : Subgroup X} (hBT : B ≤ Subgroup.normalizer (T : Set X)) :
    B ≤ Subgroup.normalizer ((⁅T, B⁆ : Subgroup X) : Set X) := by
  have hmap : ∀ (H : Subgroup X) (b : X), b ∈ Subgroup.normalizer (H : Set X) →
      H.map (MulAut.conj b).toMonoidHom = H := by
    intro H b hb
    ext y
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hb z).mp hz
    · intro hy
      refine ⟨b⁻¹ * y * b, ?_, by group⟩
      have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hb) y).mp hy
      simpa using h
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have e : (⁅T, B⁆ : Subgroup X).map (MulAut.conj b).toMonoidHom = ⁅T, B⁆ := by
    rw [Subgroup.map_commutator, hmap T b (hBT hb), hmap B b (Subgroup.le_normalizer hb)]
  constructor
  · intro hy
    rw [← e]
    exact ⟨y, hy, rfl⟩
  · intro hy
    rw [← e] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hzy
    have : z = y := mul_left_cancel (mul_right_cancel hzy)
    rwa [← this]

theorem commutator_le_normalizer_of_conj {K T B : Subgroup X}
    (hB : ∀ (g : X), ∀ b ∈ B, ∀ y : X, g * y * g⁻¹ ∈ K ↔ g * (b * y * b⁻¹) * g⁻¹ ∈ K) :
    (⁅T, B⁆ : Subgroup X) ≤ Subgroup.normalizer (K : Set X) := by
  rw [Subgroup.commutator_le]
  intro t _ b hb
  rw [Subgroup.mem_normalizer_iff]
  intro k
  have h1 : k ∈ K ↔ b⁻¹ * k * b ∈ K := by
    have := hB 1 b hb (b⁻¹ * k * b)
    simp only [one_mul, inv_one, mul_one] at this
    rw [this]
    group
  have h2 : b⁻¹ * k * b ∈ K ↔ t * b * t⁻¹ * (b⁻¹ * k * b) * t * b⁻¹ * t⁻¹ ∈ K := by
    have := hB t b hb (t⁻¹ * (b⁻¹ * k * b) * t)
    have e1 : t * (t⁻¹ * (b⁻¹ * k * b) * t) * t⁻¹ = b⁻¹ * k * b := by group
    have e2 : t * (b * (t⁻¹ * (b⁻¹ * k * b) * t) * b⁻¹) * t⁻¹ =
        t * b * t⁻¹ * (b⁻¹ * k * b) * t * b⁻¹ * t⁻¹ := by group
    rw [e1, e2] at this
    exact this
  rw [h1, h2, commutatorElement_def]
  have e3 : t * b * t⁻¹ * (b⁻¹ * k * b) * t * b⁻¹ * t⁻¹ = t * b * t⁻¹ * b⁻¹ * k * (t * b * t⁻¹ * b⁻¹)⁻¹ := by
    group
  rw [e3]

omit [Group X] in
private theorem commutator_commutator_eq_of_coprime [Group X] {T B : Subgroup X}
    (hBT : B ≤ Subgroup.normalizer (T : Set X)) (hcop : Nat.Coprime (Nat.card B) (Nat.card T)) :
    ⁅⁅T, B⁆, B⁆ = ⁅T, B⁆ := by
  classical
  have : Subgroup.Normalizes B T := ⟨hBT⟩
  have h2 : CFSG.commutatorAction₂ (A := ↥B) (G := ↥T) = CFSG.commutatorAction (A := ↥B) (G := ↥T) :=
    CFSG.commutatorAction₂_eq_commutatorAction_of_coprime (G := ↥T) (A := ↥B) hcop
  have hmap : (CFSG.commutatorAction (A := ↥B) (G := ↥T)).map T.subtype = ⁅T, B⁆ :=
    CFSG.commutatorAction_subgroup_conj_map_eq_commutator T B hBT
  have hmap2 : (CFSG.commutatorAction₂ (A := ↥B) (G := ↥T)).map T.subtype ≤ ⁅⁅T, B⁆, B⁆ := by
    let C : Subgroup ↥T := CFSG.commutatorAction (A := ↥B) (G := ↥T)
    let S : Set ↥T := {x : ↥T | ∃ a : ↥B, ∃ h : ↥T, h ∈ C ∧ x = h⁻¹ * (a • h)}
    calc (CFSG.commutatorAction₂ (A := ↥B) (G := ↥T)).map T.subtype =
          (Subgroup.closure S).map T.subtype := rfl
      _ = Subgroup.closure (T.subtype '' S) := by
        simpa using (MonoidHom.map_closure (f := T.subtype) S)
      _ ≤ ⁅⁅T, B⁆, B⁆ := by
        refine (Subgroup.closure_le (K := ⁅⁅T, B⁆, B⁆)).2 ?_
        rintro _ ⟨y, hy, rfl⟩
        rcases hy with ⟨a, h, hhC, rfl⟩
        have hhcomm : (h : X) ∈ ⁅T, B⁆ := by
          rw [← hmap]
          exact Subgroup.mem_map_of_mem T.subtype hhC
        have hcomm : ⁅(h : X)⁻¹, (a : X)⁆ ∈ ⁅⁅T, B⁆, B⁆ :=
          Subgroup.commutator_mem_commutator ((⁅T, B⁆ : Subgroup X).inv_mem hhcomm) a.2
        simpa [commutatorElement_def, Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe,
          hBT, mul_assoc] using hcomm
  refine le_antisymm ?_ fun x hx => ?_
  · exact commutator_le_of_normalizes (le_normalizer_commutator hBT)
  · rw [← hmap, ← h2] at hx
    exact hmap2 hx

end Comm

theorem t158TailOn_of {Q : TauCeti.CFSGIndex → Prop} (hN : T158NormConj Q) (hF : T158TailFaith Q)
    (hM : T158TailModel Q) : T158TailOn Q := by
  intro X _ _ p K B x₁ x₂ L₁ L₂ hQ hh hc T _ hT2 hBT
  have hc0 := hc
  obtain ⟨hp3, -⟩ := hc
  have hBel : IsElemAbelian p B := hh.hyp.1.2.2.1
  have hT₁T : (⁅T, B⁆ : Subgroup X) ≤ T := commutator_le_of_normalizes hBT
  have hT₁2 : IsPGroup 2 (⁅T, B⁆ : Subgroup X) := hT2.to_le hT₁T
  have hBT₁ : B ≤ Subgroup.normalizer ((⁅T, B⁆ : Subgroup X) : Set X) := le_normalizer_commutator hBT
  have hT₁K : (⁅T, B⁆ : Subgroup X) ≤ Subgroup.normalizer (K : Set X) :=
    commutator_le_normalizer_of_conj (hN X p K B x₁ x₂ L₁ L₂ hQ hh hc0)
  have hcop : Nat.Coprime (Nat.card B) (Nat.card T) := by
    subst hp3
    obtain ⟨m, hm⟩ := (isPGroup_of_isElemAbelian hBel).exists_card_eq
    obtain ⟨n, hn⟩ := hT2.exists_card_eq
    rw [hm, hn]
    exact Nat.Coprime.pow m n (by norm_num)
  have hcomm : ⁅⁅T, B⁆, B⁆ = (⁅T, B⁆ : Subgroup X) := commutator_commutator_eq_of_coprime hBT hcop
  have hcent : (⁅T, B⁆ : Subgroup X) ≤ centModSubgroup p K := by
    have := hM X p K B x₁ x₂ L₁ L₂ hQ hh hc0 (⁅T, B⁆) hT₁2 hT₁K hBT₁
    rwa [hcomm] at this
  exact hF X p K B x₁ x₂ L₁ L₂ hQ hh hc0 (⁅T, B⁆) hT₁2 hBT₁ hcent

end CFSG.LocalAnalysis.GLTheoremA.T158

end
