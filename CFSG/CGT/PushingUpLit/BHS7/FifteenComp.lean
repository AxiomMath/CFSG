module

public import CFSG.CGT.PushingUpLit.BHS5.FiveFive
public import CFSG.CGT.PushingUpLit.BHS.FourSymI

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.BHS
  CFSG.CGT.PushingUpLit.BHS5

theorem le_normalizer_of_comm {G : Type*} [Group G] {K E : Subgroup G}
    (h : ∀ k ∈ K, ∀ e ∈ E, k * e = e * k) : K ≤ Subgroup.normalizer (E : Set G) := by
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have : k * x * k⁻¹ = x := by rw [h k hk x hx]; group
    rw [this]
    exact hx
  · intro hx
    have h1 := h k hk _ hx
    have hx' : x = k * x * k⁻¹ := by
      calc x = k⁻¹ * (k * x * k⁻¹) * k := by group
        _ = k⁻¹ * ((k * x * k⁻¹) * k) := by rw [mul_assoc]
        _ = k⁻¹ * (k * (k * x * k⁻¹)) := by rw [← h1]
        _ = k * x * k⁻¹ := by group
    rw [hx']
    exact hx

variable {V : Type} [CommGroup V]

section Conj

variable {P' M' : Subgroup (MulAut V)} {D : Set (Subgroup (MulAut V))}

theorem ncOut_conjSub_of_dOut {g : MulAut V}
    (hgo : ∀ A ∈ dOut P' D M', conjSub g A ∈ dOut P' D M') {B C : Subgroup (MulAut V)}
    (h : NCOut P' D M' B C) : NCOut P' D M' (conjSub g B) (conjSub g C) := by
  obtain ⟨hB, hC, hBC⟩ := h
  exact ⟨hgo B hB, hgo C hC, nonComm_conjSub g hBC⟩

theorem mem_compOf_conjSub_of_dOut {g : MulAut V}
    (hgo : ∀ A ∈ dOut P' D M', conjSub g A ∈ dOut P' D M') {A B : Subgroup (MulAut V)}
    (h : B ∈ compOf P' D M' A) : conjSub g B ∈ compOf P' D M' (conjSub g A) :=
  Relation.ReflTransGen.lift (conjSub g) (fun _ _ hBC => ncOut_conjSub_of_dOut hgo hBC) _ _ h

theorem conjSub_compGen_of_dOut {g : MulAut V}
    (hgo : ∀ A ∈ dOut P' D M', conjSub g A ∈ dOut P' D M')
    (hgo' : ∀ A ∈ dOut P' D M', conjSub g⁻¹ A ∈ dOut P' D M') {A : Subgroup (MulAut V)} :
    conjSub g (compGen P' D M' A) = compGen P' D M' (conjSub g A) := by
  apply le_antisymm
  · rw [compGen, conjSub, Subgroup.map_iSup]
    refine iSup_le fun B => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hB => ?_
    exact le_iSup₂_of_le (f := fun (X : Subgroup (MulAut V)) (_ : X ∈ compOf P' D M' (conjSub g A))
      => X) _ (mem_compOf_conjSub_of_dOut hgo hB) le_rfl
  · rw [compGen]
    refine iSup₂_le fun B hB => ?_
    have h1 := mem_compOf_conjSub_of_dOut hgo' hB
    rw [← conjSub_mul, inv_mul_cancel, conjSub_one] at h1
    have h2 : B = conjSub g (conjSub g⁻¹ B) := by
      rw [← conjSub_mul, mul_inv_cancel, conjSub_one]
    rw [h2]
    exact conjSub_mono g (le_iSup₂_of_le (f := fun (X : Subgroup (MulAut V))
      (_ : X ∈ compOf P' D M' A) => X) _ h1 le_rfl)

theorem conjSub_mem_dOut {g : MulAut V} (hD : ∀ A ∈ D, conjSub g A ∈ D)
    (hN : ∀ y ∈ P', g * y * g⁻¹ ∈ P') (hM : conjSub g⁻¹ M' = M') {A : Subgroup (MulAut V)}
    (hA : A ∈ dOut P' D M') : conjSub g A ∈ dOut P' D M' := by
  refine ⟨hD A hA.1, fun hcore => hA.2 ⟨hA.1, fun y hy => ?_⟩⟩
  have h1 := hcore.2 (g * y * g⁻¹) (hN y hy)
  rw [conjSub_mul, conjSub_mul, hM] at h1
  exact (conjSub_le_conjSub_iff g).1 h1

theorem conjSub_inf_of_mem {P' M : Subgroup (MulAut V)} {a : MulAut V}
    (haN : a ∈ Subgroup.normalizer (P' : Set (MulAut V))) (haM : a ∈ M) :
    conjSub a (P' ⊓ M) = P' ⊓ M := by
  ext x
  rw [mem_conjSub_iff, Subgroup.mem_inf, Subgroup.mem_inf]
  have h1 := (Subgroup.mem_normalizer_iff.1 haN) (a⁻¹ * x * a)
  constructor
  · rintro ⟨hP, hM⟩
    refine ⟨?_, ?_⟩
    · have := h1.1 hP
      simpa [mul_assoc] using this
    · have := M.mul_mem (M.mul_mem haM hM) (M.inv_mem haM)
      simpa [mul_assoc] using this
  · rintro ⟨hP, hM⟩
    refine ⟨?_, ?_⟩
    · have := h1.2 (by simpa [mul_assoc] using hP)
      exact this
    · exact M.mul_mem (M.mul_mem (M.inv_mem haM) hM) haM

end Conj

@[expose] def IsCompType (E : Subgroup (MulAut V)) : Prop :=
  (∃ D : Set (Subgroup (MulAut V)), SLType2 D E) ∨
    ∃ (M : Subgroup (MulAut V)) (D : Set (Subgroup (MulAut V))), SymType M D E

section Component

variable [Finite V]

theorem component_of_hyp43 {P T M P' M' : Subgroup (MulAut V)}
    {D : Set (Subgroup (MulAut V))} (h : Hyp43 P D T M) (hV : ∀ v : V, v ^ 2 = 1)
    (hP : P = P' ⊔ T) (hP' : P' = ⨆ A ∈ D, A) (hM' : M' = P' ⊓ M) {A₀ : Subgroup (MulAut V)}
    (hA₀ : A₀ ∈ dOut P' D M') :
    A₀ ≤ compGen P' D M' A₀ ∧ compGen P' D M' A₀ ≤ P' ∧
      P' ≤ Subgroup.normalizer (compGen P' D M' A₀ : Set (MulAut V)) ∧
      (SLType2 D (compGen P' D M' A₀) ∨ SymType M' D (compGen P' D M' A₀)) ∧
      ∀ t ∈ T, ∀ X : Subgroup (MulAut V), X ≠ ⊥ → X ≤ compGen P' D M' A₀ → conjSub t X = X →
        conjSub t (compGen P' D M' A₀) = compGen P' D M' A₀ := by
  subst hP'
  subst hM'
  set P' : Subgroup (MulAut V) := ⨆ A ∈ D, A with hP'def
  have hH' : Hyp43 P' D (P' ⊓ T) (P' ⊓ M) := hyp43_gen h hP
  obtain ⟨-, -, hSup, hComm, hCoreComm, hDisj, -, -⟩ := four_eighteen_all hH' hV rfl
  have hD1 : ∀ A ∈ D, A ≤ P' := fun A hA => le_iSup_mem hA
  have hout := hA₀
  refine ⟨le_compGen, iSup₂_le fun B hB => hD1 B (compOf_subset hout hB).1, ?_, ?_, ?_⟩
  ·
    refine hSup.le.trans (sup_le (iSup₂_le fun C hC => ?_) (iSup₂_le fun A hA => ?_))
    · exact le_normalizer_of_comm fun c hc e he => (hCoreComm A₀ hout C hC e he c hc).symm
    · by_cases hEA : compGen P' D (P' ⊓ M) A = compGen P' D (P' ⊓ M) A₀
      · rw [hEA]
        exact Subgroup.le_normalizer
      · exact le_normalizer_of_comm fun k hk e he => hComm A hA A₀ hout hEA k hk e he
  ·
    by_cases h3 : 3 ≤ Nat.card A₀
    · exact Or.inl (slType2_of_card_ge_three hH' hV hout h3)
    · right
      have hA2 : IsPGroup 2 A₀ := isPGroup_of_isElemAbelian2 (hH'.elemAb A₀ hout.1)
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hA2
      have hbot : A₀ ≠ ⊥ := hH'.ne_bot A₀ hout.1
      have hcard : Nat.card A₀ = 2 := by
        rcases k with _ | _ | k
        · exact absurd (Subgroup.card_eq_one.1 (by simpa using hk)) hbot
        · simpa using hk
        · exfalso
          apply h3
          rw [hk]
          calc 3 ≤ 2 ^ 2 := by norm_num
            _ ≤ 2 ^ (k + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      exact bhsSymType V P' D (P' ⊓ T) (P' ⊓ M) hH' hV rfl A₀ hout hcard
  ·
    intro t ht X hX0 hXE hXt
    have hTP : ∀ s ∈ T, s ∈ P := fun s hs => h.syl.1 hs
    have hsN : ∀ s ∈ T, s ∈ Subgroup.normalizer (P' : Set (MulAut V)) := fun s hs =>
      iSup_normalized h.toHyp41 (hTP s hs)
    have hMt : ∀ s ∈ T, conjSub s⁻¹ (P' ⊓ M) = P' ⊓ M := fun s hs =>
      conjSub_inf_of_mem (Subgroup.inv_mem _ (hsN s hs)) (M.inv_mem (h.le_M hs))
    have hgo : ∀ s ∈ T, ∀ A ∈ dOut P' D (P' ⊓ M), conjSub s A ∈ dOut P' D (P' ⊓ M) :=
      fun s hs A hA => conjSub_mem_dOut (fun B hB => h.conj_mem B hB s (hTP s hs))
        (fun y hy => (Subgroup.mem_normalizer_iff.1 (hsN s hs) y).1 hy) (hMt s hs) hA
    have hE : conjSub t (compGen P' D (P' ⊓ M) A₀) = compGen P' D (P' ⊓ M) (conjSub t A₀) :=
      conjSub_compGen_of_dOut (hgo t ht) (hgo t⁻¹ (T.inv_mem ht))
    have hA₁ : conjSub t A₀ ∈ dOut P' D (P' ⊓ M) := hgo t ht A₀ hout
    by_cases heq : compGen P' D (P' ⊓ M) (conjSub t A₀) = compGen P' D (P' ⊓ M) A₀
    · rw [hE, heq]
    · exfalso
      have hle : compGen P' D (P' ⊓ M) (conjSub t A₀) ≤ (⨆ C ∈ dCore P' D (P' ⊓ M), C) ⊔
          ⨆ B ∈ {B | B ∈ dOut P' D (P' ⊓ M) ∧
            compGen P' D (P' ⊓ M) B ≠ compGen P' D (P' ⊓ M) A₀}, compGen P' D (P' ⊓ M) B :=
        le_sup_of_le_right (le_iSup₂_of_le (f := fun (B : Subgroup (MulAut V))
          (_ : B ∈ {B | B ∈ dOut P' D (P' ⊓ M) ∧
            compGen P' D (P' ⊓ M) B ≠ compGen P' D (P' ⊓ M) A₀}) =>
          compGen P' D (P' ⊓ M) B) (conjSub t A₀) ⟨hA₁, heq⟩ le_rfl)
      have hXE1 : X ≤ compGen P' D (P' ⊓ M) (conjSub t A₀) := by
        rw [← hE]
        calc X = conjSub t X := hXt.symm
          _ ≤ conjSub t (compGen P' D (P' ⊓ M) A₀) := conjSub_mono t hXE
      exact hX0 (le_bot_iff.1 (hDisj A₀ hout hXE (hXE1.trans hle)))

end Component

end CFSG.CGT.PushingUpLit.BHS7
