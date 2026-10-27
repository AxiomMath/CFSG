module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Five.Counting

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

open scoped IsMulCommutative

theorem y4a_no_triangle {A : Type} [CommGroup A] (S : Finset A) (hS : S.card = 5)
    (h1 : (1 : A) ∉ S) (hsq : ∀ s ∈ S, s * s = 1) (hprod : ∏ s ∈ S, s = 1) {e₁ e₂ : A}
    (he₁ : e₁ ∈ S) (he₂ : e₂ ∈ S) (hne : e₁ ≠ e₂) : e₁ * e₂ ∉ S := by
  classical
  intro he₃
  have he₃_ne₁ : e₁ * e₂ ≠ e₁ := by
    intro h
    have h2 : e₂ = 1 := mul_left_cancel (a := e₁) (by rw [h, mul_one])
    exact h1 (by simpa [h2] using he₂)
  have he₃_ne₂ : e₁ * e₂ ≠ e₂ := by
    intro h
    have h2 : e₁ = 1 := mul_right_cancel (by rw [h, one_mul])
    exact h1 (by simpa [h2] using he₁)
  have he₂' : e₂ ∈ S.erase e₁ := Finset.mem_erase.mpr ⟨fun h => hne h.symm, he₂⟩
  have he₃' : e₁ * e₂ ∈ (S.erase e₁).erase e₂ :=
    Finset.mem_erase.mpr ⟨he₃_ne₂, Finset.mem_erase.mpr ⟨he₃_ne₁, he₃⟩⟩
  set T : Finset A := ((S.erase e₁).erase e₂).erase (e₁ * e₂) with hTdef
  have hTcard : T.card = 2 := by
    rw [hTdef, Finset.card_erase_of_mem he₃', Finset.card_erase_of_mem he₂',
      Finset.card_erase_of_mem he₁, hS]
  obtain ⟨q, q', hqq', hT⟩ := Finset.card_eq_two.mp hTcard
  have hp1 : e₁ * (∏ s ∈ S.erase e₁, s) = ∏ s ∈ S, s := by
    simpa using Finset.mul_prod_erase S (fun x => x) he₁
  have hp2 : e₂ * (∏ s ∈ (S.erase e₁).erase e₂, s) = ∏ s ∈ S.erase e₁, s := by
    simpa using Finset.mul_prod_erase (S.erase e₁) (fun x => x) he₂'
  have hp3 : (e₁ * e₂) * (∏ s ∈ T, s) = ∏ s ∈ (S.erase e₁).erase e₂, s := by
    rw [hTdef]
    simpa using Finset.mul_prod_erase ((S.erase e₁).erase e₂) (fun x => x) he₃'
  have hprodT : ∏ s ∈ T, s = 1 := by
    have h1' : e₁ * (e₂ * ((e₁ * e₂) * (∏ s ∈ T, s))) = 1 := by
      rw [hp3, hp2, hp1, hprod]
    have hcoef : e₁ * (e₂ * (e₁ * e₂)) = 1 := by
      calc e₁ * (e₂ * (e₁ * e₂)) = (e₁ * e₁) * (e₂ * e₂) := by ac_rfl
        _ = 1 := by rw [hsq e₁ he₁, hsq e₂ he₂, one_mul]
    have hassoc : e₁ * (e₂ * ((e₁ * e₂) * (∏ s ∈ T, s))) =
        (e₁ * (e₂ * (e₁ * e₂))) * (∏ s ∈ T, s) := by ac_rfl
    rw [hassoc, hcoef, one_mul] at h1'
    exact h1'
  have hqq'_prod : q * q' = 1 := by
    rw [hT] at hprodT
    rw [Finset.prod_insert (by simpa using hqq'), Finset.prod_singleton] at hprodT
    exact hprodT
  have hTsub : T ⊆ S := by
    intro x hx
    rw [hTdef] at hx
    exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx))
  have hqS : q ∈ S := hTsub (by rw [hT]; exact Finset.mem_insert_self q {q'})
  have hq_sq : q * q = 1 := hsq q hqS
  exact hqq' (mul_left_cancel (a := q) (by rw [hq_sq, hqq'_prod]))

theorem y4a_fixed_free {G : Type} [Group G] [Finite G] {Y M : Subgroup G} {A B : Set G}
    (hcover : ∀ m ∈ M, m ≠ 1 → m ∈ A ∨ m ∈ B) (hY : Nat.card ↥Y = 960)
    (hA : ∀ c ∈ A, Nat.card ↥(Gx c ⊓ Y) = 96) (hBorb : IsConjOrbit Y B)
    (hB : Nat.card ↥B = 5) : ∀ m ∈ M, (∀ l ∈ Y, l * m * l⁻¹ = m) → m = 1 := by
  intro m hm hfix
  by_contra hne
  have hYle : Y ≤ Gx m := by
    intro l hl
    rw [mem_Gx]
    have h := hfix l hl
    calc m * l = (l * m * l⁻¹) * l := by rw [h]
      _ = l * m := by group
  rcases hcover m hm hne with hmA | hmB
  · have h := hA m hmA
    rw [inf_eq_right.mpr hYle, hY] at h
    exact absurd h (by decide)
  · have h := IsConjOrbit.card_mul_card_stab (K := Y) hBorb hmB
    rw [inf_eq_left.mpr hYle, hB, hY] at h
    exact absurd h (by decide)

theorem y4a_no_pair {G : Type} [Group G] [Finite G] {Y M : Subgroup G} {B : Set G}
    (hM : IsElemTwo 4 M) (hnorm : ∀ l ∈ Y, ∀ m ∈ M, l * m * l⁻¹ ∈ M) (hBM : B ⊆ M)
    (h1B : (1 : G) ∉ B) (hB : Nat.card ↥B = 5) (hBinv : ∀ l ∈ Y, ∀ c ∈ B, l * c * l⁻¹ ∈ B)
    (hfree : ∀ m ∈ M, (∀ l ∈ Y, l * m * l⁻¹ = m) → m = 1) :
    ¬ ∃ E : Subgroup G, E ≤ M ∧ IsElemTwo 2 E ∧ ∀ t ∈ E, t ≠ 1 → t ∈ B := by
  classical
  rintro ⟨E, hEM, hE2, hEB⟩
  haveI : Fintype ↥M := Fintype.ofFinite ↥M
  haveI : IsMulCommutative ↥M := hM.1.1
  set S : Finset ↥M := Finset.univ.filter (fun m => (m : G) ∈ B) with hSdef
  have hScard : S.card = Nat.card ↥B := by
    have h1 : S.card = Fintype.card {m : ↥M // (m : G) ∈ B} := by
      rw [hSdef]
      exact (Fintype.card_subtype (fun m : ↥M => (m : G) ∈ B)).symm
    let eB : {m : ↥M // (m : G) ∈ B} ≃ ↥B :=
      { toFun := fun m => ⟨(m.1 : G), m.2⟩
        invFun := fun b => ⟨⟨(b : G), hBM b.2⟩, b.2⟩
        left_inv := fun m => Subtype.ext (Subtype.ext rfl)
        right_inv := fun b => Subtype.ext rfl }
    rw [h1, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr eB
  have hS_card : S.card = 5 := by rw [hScard, hB]
  have h1S : (1 : ↥M) ∉ S := by
    rw [hSdef]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro h
    exact h1B (by simpa using h)
  have hsq : ∀ s ∈ S, s * s = 1 := by
    intro s hs
    rw [hSdef] at hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
    refine Subtype.ext ?_
    have h2 : (s : G) * (s : G) = 1 := by
      have h := hM.1.2 (s : G) (hBM hs)
      rwa [pow_two] at h
    simpa using h2
  let p : ↥M := ∏ s ∈ S, s
  have hp : p = 1 := by
    have hfix_all : ∀ l ∈ Y, l * (p : G) * l⁻¹ = (p : G) := by
      intro l hl
      let σ : ↥M →* ↥M :=
        ((MulAut.conj l).toMonoidHom.domRestrict M).codRestrict M
          (fun m => hnorm l hl (m : G) m.2)
      let τ : ↥M →* ↥M :=
        ((MulAut.conj l⁻¹).toMonoidHom.domRestrict M).codRestrict M
          (fun m => hnorm l⁻¹ (Y.inv_mem hl) (m : G) m.2)
      have hσ_apply : ∀ m : ↥M, (σ m : G) = l * (m : G) * l⁻¹ := by
        intro m
        simp [σ, MulAut.conj_apply]
      have hτ_apply : ∀ m : ↥M, (τ m : G) = l⁻¹ * (m : G) * (l⁻¹)⁻¹ := by
        intro m
        simp [τ, MulAut.conj_apply]
      have hperm : ∏ s ∈ S, σ s = ∏ s ∈ S, s := by
        refine Finset.prod_nbij' (s := S) (t := S) σ τ ?_ ?_ ?_ ?_ ?_
        · intro a ha
          rw [hSdef] at ha ⊢
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
          rw [hσ_apply]
          exact hBinv l hl (a : G) ha
        · intro b hb
          rw [hSdef] at hb ⊢
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
          rw [hτ_apply]
          exact hBinv l⁻¹ (Y.inv_mem hl) (b : G) hb
        · intro a ha
          refine Subtype.ext ?_
          rw [hτ_apply, hσ_apply]
          group
        · intro b hb
          refine Subtype.ext ?_
          rw [hσ_apply, hτ_apply]
          group
        · intro a ha
          rfl
      have hσp : σ p = p := by
        calc σ p = ∏ s ∈ S, σ s := map_prod σ (fun s : ↥M => s) S
          _ = ∏ s ∈ S, s := hperm
          _ = p := rfl
      have hpk := congrArg (fun x : ↥M => (x : G)) hσp
      rw [hσ_apply p] at hpk
      exact hpk
    have h := hfree (p : G) p.2 hfix_all
    exact Subtype.ext h
  have hprod : ∏ s ∈ S, s = 1 := hp
  haveI : Fintype ↥E := Fintype.ofFinite ↥E
  have hunivE : (Finset.univ : Finset ↥E).card = 4 := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hE2.2]
    decide
  let U : Finset ↥E := (Finset.univ : Finset ↥E).erase 1
  have hUcard : U.card = 3 := by
    change ((Finset.univ : Finset ↥E).erase 1).card = 3
    rw [Finset.card_erase_of_mem (Finset.mem_univ (1 : ↥E)), hunivE]
  have hUne : U.Nonempty := Finset.card_pos.mp (by rw [hUcard]; decide)
  obtain ⟨e₁, he₁U⟩ := hUne
  have he₁ne : e₁ ≠ 1 := (Finset.mem_erase.mp he₁U).1
  let U2 : Finset ↥E := U.erase e₁
  have hU2card : U2.card = 2 := by
    change (U.erase e₁).card = 2
    rw [Finset.card_erase_of_mem he₁U, hUcard]
  have hU2ne : U2.Nonempty := Finset.card_pos.mp (by rw [hU2card]; decide)
  obtain ⟨e₂, he₂U2⟩ := hU2ne
  have he₂ne₁ : e₂ ≠ e₁ := (Finset.mem_erase.mp he₂U2).1
  have he₂U : e₂ ∈ U := (Finset.mem_erase.mp he₂U2).2
  have he₂ne : e₂ ≠ 1 := (Finset.mem_erase.mp he₂U).1
  have he₁ne₂ : e₁ ≠ e₂ := fun h => he₂ne₁ h.symm
  have he₁sq : e₁ * e₁ = 1 := by
    refine Subtype.ext ?_
    have h := hE2.1.2 (e₁ : G) e₁.2
    rwa [pow_two] at h
  have he₃ne : e₁ * e₂ ≠ 1 := by
    intro h
    have h2 : e₂ = e₁ := mul_left_cancel (a := e₁) (by rw [h, he₁sq])
    exact he₂ne₁ h2
  have he₁ne' : (e₁ : G) ≠ 1 := by
    intro h
    exact he₁ne (Subtype.ext (by simpa using h))
  have he₂ne' : (e₂ : G) ≠ 1 := by
    intro h
    exact he₂ne (Subtype.ext (by simpa using h))
  have he₃ne' : ((e₁ * e₂ : ↥E) : G) ≠ 1 := by
    intro h
    exact he₃ne (Subtype.ext (by simpa using h))
  have he₁B : (e₁ : G) ∈ B := hEB (e₁ : G) e₁.2 he₁ne'
  have he₂B : (e₂ : G) ∈ B := hEB (e₂ : G) e₂.2 he₂ne'
  have he₃B : ((e₁ * e₂ : ↥E) : G) ∈ B :=
    hEB ((e₁ * e₂ : ↥E) : G) (e₁ * e₂).2 he₃ne'
  set s₁ : ↥M := ⟨(e₁ : G), hEM e₁.2⟩ with hs₁def
  set s₂ : ↥M := ⟨(e₂ : G), hEM e₂.2⟩ with hs₂def
  set s₃ : ↥M := ⟨((e₁ * e₂ : ↥E) : G), hEM (e₁ * e₂).2⟩ with hs₃def
  have hs₃eq : s₃ = s₁ * s₂ := by
    rw [hs₃def, hs₁def, hs₂def]
    refine Subtype.ext ?_
    simp only [Subgroup.coe_mul]
  have hs₁S : s₁ ∈ S := by
    rw [hSdef, hs₁def]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simpa using he₁B
  have hs₂S : s₂ ∈ S := by
    rw [hSdef, hs₂def]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simpa using he₂B
  have hs₃S : s₃ ∈ S := by
    rw [hSdef, hs₃def]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simpa using he₃B
  have hs₁ne₂ : s₁ ≠ s₂ := by
    intro h
    apply he₁ne₂
    have h2 := congrArg (fun x : ↥M => (x : G)) h
    rw [hs₁def, hs₂def] at h2
    exact Subtype.ext h2
  exact y4a_no_triangle S hS_card h1S hsq hprod hs₁S hs₂S hs₁ne₂ (hs₃eq ▸ hs₃S)

end CFSG.EvenSporadicStandard.HNRecog.Section3
