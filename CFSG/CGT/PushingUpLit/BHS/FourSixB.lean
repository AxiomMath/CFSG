module

public import CFSG.CGT.PushingUpLit.BHS.FourSixA

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.RankThree.PartOne CFSG.Open CFSG.LieType.BorelTits
  CFSG.Quasithin.G6

variable {V : Type} [CommGroup V] [Finite V]

@[expose] def SLType (D : Set (Subgroup (MulAut V))) (E : Subgroup (MulAut V)) : Prop :=
  ∃ n : ℕ, 1 ≤ n ∧ IsSLNatSection E (commV E) (commV E ⊓ fixV E) n ∧ commV E ⊔ fixV E = ⊤ ∧
    ∀ B, B ∈ dInter D E ↔ IsSylowOf 2 B E

@[expose] def SymType (M : Subgroup (MulAut V)) (D : Set (Subgroup (MulAut V)))
    (E : Subgroup (MulAut V)) : Prop :=
  ∃ (m : ℕ) (θ : ↥E ≃* Equiv.Perm (Fin m)) (β : ↥(commV E) →* coreMod m),
    Odd m ∧ 3 ≤ m ∧ (∀ x ∈ E, ∀ p ∈ commV E, x p ∈ commV E) ∧ Function.Surjective β ∧
    β.ker = ⊥ ∧
    (∀ (x : ↥E) (p : ↥(commV E)) (hp : (x : MulAut V) p ∈ commV E),
      β ⟨(x : MulAut V) p, hp⟩ = coreAct m (θ x) (β p)) ∧
    commV E ⊔ fixV E = ⊤ ∧
    (∀ B ∈ dInter D E, ∃ i j : Fin m, i ≠ j ∧ ∀ b : ↥E, (b : MulAut V) ∈ B →
      θ b = 1 ∨ θ b = Equiv.swap i j) ∧
    ∃ i₀ : Fin m, ∀ x : ↥E, (x : MulAut V) ∈ M ↔ θ x i₀ = i₀

@[expose] def BHSSymCase : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (P : Subgroup (MulAut V))
    (D : Set (Subgroup (MulAut V))) (T M : Subgroup (MulAut V)),
    Hyp43 P D T M → (∀ v : V, v ^ 2 = 1) → P = ⨆ A ∈ D, A →
    ∀ A ∈ dOut P D M, Nat.card A = 2 →
      SLType D (compGen P D M A) ∨ SymType M D (compGen P D M A)

theorem perm_eq_one_of_central {m : ℕ} (hm : 3 ≤ m) {σ : Equiv.Perm (Fin m)}
    (h : ∀ τ : Equiv.Perm (Fin m), τ * σ = σ * τ) : σ = 1 := by
  refine Equiv.ext fun a => ?_
  rw [Equiv.Perm.one_apply]
  by_contra hne
  have hne' : σ a ≠ a := hne
  obtain ⟨b, hba, hbσ⟩ : ∃ b : Fin m, b ≠ a ∧ b ≠ σ a := by
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ : Finset (Fin m)) ⊆ {a, σ a} := fun x _ => by
      by_cases hx : x = a
      · simp [hx]
      · simp [hcon x hx]
    have := Finset.card_le_card hsub
    have h2 : ({a, σ a} : Finset (Fin m)).card ≤ 2 := Finset.card_le_two
    simp only [Finset.card_univ, Fintype.card_fin] at this
    omega
  have h1 := congrArg (fun f => f a) (h (Equiv.swap a b))
  simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left] at h1
  rw [Equiv.swap_apply_of_ne_of_ne hne' hbσ.symm] at h1
  exact hba (σ.injective h1).symm

omit [Finite V] in
theorem SymType.eq_one_of_central {M : Subgroup (MulAut V)} {D : Set (Subgroup (MulAut V))}
    {E : Subgroup (MulAut V)} (h : SymType M D E) {x : MulAut V} (hx : x ∈ E)
    (hc : ∀ y ∈ E, y * x = x * y) : x = 1 := by
  obtain ⟨m, θ, -, -, hm, -⟩ := h
  have : θ ⟨x, hx⟩ = 1 := by
    refine perm_eq_one_of_central hm fun τ => ?_
    obtain ⟨y, rfl⟩ := θ.surjective τ
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hc y y.2)
  have h1 : (⟨x, hx⟩ : ↥E) = 1 := θ.injective (this.trans (map_one θ).symm)
  exact congrArg Subtype.val h1

omit [Finite V] in
theorem SLType.eq_one_of_central {D : Set (Subgroup (MulAut V))} {E : Subgroup (MulAut V)}
    (h : SLType D E) {x : MulAut V} (hx : x ∈ E) (hc : ∀ y ∈ E, y * x = x * y) : x = 1 := by
  obtain ⟨n, -, hsec, -⟩ := h
  obtain ⟨-, θ, -⟩ := hsec
  have hmem : θ ⟨x, hx⟩ ∈
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := θ.surjective g
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hc y y.2)
  rw [CFSG.Timmesfeld.RankOne.center_SL2_eq_bot] at hmem
  have h1 : (⟨x, hx⟩ : ↥E) = 1 :=
    θ.injective ((Subgroup.mem_bot.1 hmem).trans (map_one θ).symm)
  exact congrArg Subtype.val h1

theorem four_eighteen (hsym : BHSSymCase)
    {P : Subgroup (MulAut V)} {D : Set (Subgroup (MulAut V))} {T M : Subgroup (MulAut V)}
    (h : Hyp43 P D T M) (hV : ∀ v : V, v ^ 2 = 1) (hP : P = ⨆ A ∈ D, A) :
    (∀ A ∈ dOut P D M, SLType D (compGen P D M A) ∨ SymType M D (compGen P D M A)) ∧
    D = dCore P D M ∪ ⋃ A ∈ dOut P D M, dInter D (compGen P D M A) ∧
    (⨆ A ∈ D, A : Subgroup (MulAut V)) =
      (⨆ C ∈ dCore P D M, C) ⊔ ⨆ A ∈ dOut P D M, compGen P D M A ∧
    (∀ A ∈ dOut P D M, ∀ B ∈ dOut P D M, compGen P D M A ≠ compGen P D M B →
      ∀ x ∈ compGen P D M A, ∀ y ∈ compGen P D M B, x * y = y * x) ∧
    (∀ A ∈ dOut P D M, ∀ C ∈ dCore P D M, ∀ x ∈ compGen P D M A, ∀ y ∈ C, x * y = y * x) ∧
    (∀ A ∈ dOut P D M, Disjoint (compGen P D M A) ((⨆ C ∈ dCore P D M, C) ⊔
      ⨆ B ∈ {B | B ∈ dOut P D M ∧ compGen P D M B ≠ compGen P D M A}, compGen P D M B)) ∧
    (∀ A ∈ dOut P D M, ∀ B ∈ dOut P D M, compGen P D M A ≠ compGen P D M B →
      commV (compGen P D M A) ≤ fixV (compGen P D M B)) ∧
    (∀ A ∈ dOut P D M, ∀ C ∈ dCore P D M, commV (compGen P D M A) ≤ fixV C) := by
  have htype : ∀ A ∈ dOut P D M, SLType D (compGen P D M A) ∨ SymType M D (compGen P D M A) := by
    intro A hA
    by_cases h3 : 3 ≤ Nat.card A
    · left
      exact sl_type_of_mem_lamSet h.toHyp41 (compGen_mem_lamSet h hV hA h3)
    · have hA2 : IsPGroup 2 A := isPGroup_of_isElemAbelian2 (h.elemAb A hA.1)
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hA2
      have hbot : A ≠ ⊥ := h.ne_bot A hA.1
      have hcard : Nat.card A = 2 := by
        rcases k with _ | _ | k
        · exact absurd (Subgroup.card_eq_one.1 (by simpa using hk)) hbot
        · simpa using hk
        · exfalso
          apply h3
          rw [hk]
          calc 3 ≤ 2 ^ 2 := by norm_num
            _ ≤ 2 ^ (k + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      exact hsym V P D T M h hV hP A hA hcard
  refine ⟨htype, four_eighteen_struct h fun A hA x hx hc => ?_⟩
  rcases htype A hA with hSL | hSym
  · exact hSL.eq_one_of_central hx hc
  · exact hSym.eq_one_of_central hx hc

end CFSG.CGT.PushingUpLit.BHS
