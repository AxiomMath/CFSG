module

public import CFSG.ClassicalInvolution.ModelFacts.E7ModelTorusFam
public import CFSG.ClassicalInvolution.ModelFacts.ChevAutTorusStdMain

public section

namespace CFSG.ClassicalInvolution.ModelFacts.E7Model

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.ClassicalInvolution.ModelFacts.ChevAut
  CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Minuscule

@[expose] def cvec5 : Fin 5 → (Fin 7 → ℤ) :=
  ![Pi.single 3 1, Pi.single 4 1, Pi.single 5 1, Pi.single 6 1, θE7]

theorem cp5_bound : ∀ γ ∈ rootFinset .E7, ∀ i : Fin 5,
    |cpair (Tag.cartan .E7) (cvec5 i) γ| ≤ 2 := by decide +kernel

theorem cp5_nonzero : ∀ γ ∈ rootFinset .E7, ∃ i : Fin 5,
    cpair (Tag.cartan .E7) (cvec5 i) γ ≠ 0 := by decide +kernel

theorem cp5_sign : ∀ γ ∈ rootFinset .E7, (∀ j, 0 ≤ γ j) ∨ (∀ j, γ j ≤ 0) := by decide +kernel

theorem cp5_neg : ∀ k : Fin 7, ∀ β ∈ rootFinset .E7, (∀ j, β j ≤ 0) →
    (∀ i : Fin 5,
      cpair (Tag.cartan .E7) (cvec5 i) (Pi.single k 1) - cpair (Tag.cartan .E7) (cvec5 i) β = 0 ∨
      cpair (Tag.cartan .E7) (cvec5 i) (Pi.single k 1) - cpair (Tag.cartan .E7) (cvec5 i) β = 4 ∨
      cpair (Tag.cartan .E7) (cvec5 i) (Pi.single k 1) - cpair (Tag.cartan .E7) (cvec5 i) β = -4) →
    False := by decide +kernel

theorem cp5_zero_four :
    cpair (Tag.cartan .E7) (cvec5 0) (Pi.single (4 : Fin 7) 1 : Fin 7 → ℤ) = -1 := by decide

variable {F : Type} [Field F]

theorem zpow_eq_cases [Finite F] (hq : 5 ≤ Nat.card F) {a b : ℤ} (hab : |a - b| ≤ 4)
    (h : ∀ s : Fˣ, s ^ a = s ^ b) : a - b = 0 ∨ a - b = 4 ∨ a - b = -4 := by
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hord : orderOf ζ = Nat.card F - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hζ, Nat.card_units]
  have h1 : ζ ^ (a - b) = 1 := by rw [zpow_sub, h ζ, mul_inv_cancel]
  have h2 : ((Nat.card F - 1 : ℕ) : ℤ) ∣ a - b := by
    rw [← hord]
    exact orderOf_dvd_iff_zpow_eq_one.2 h1
  obtain ⟨k, hk⟩ := h2
  have hq4 : (4 : ℤ) ≤ ((Nat.card F - 1 : ℕ) : ℤ) := by omega
  rw [abs_le] at hab
  have hk1 : -1 ≤ k ∧ k ≤ 1 := by
    constructor <;> by_contra hcon <;> have hcon' := not_le.1 hcon <;> nlinarith
  obtain ⟨hk1, hk2⟩ := hk1
  interval_cases k <;> omega

theorem map_one_units (s : Fˣ) : Units.map ((1 : F ≃+* F) : F →+* F) s = s := by
  ext
  rfl

theorem e7_char_num [Finite F] {p : ℕ} [Fact p.Prime] [CharP F p] (hp2 : p ≠ 2)
    (hq : 5 ≤ Nat.card F) (φ : F ≃+* F)
    (w : (coxeterMatrix (e7Datum F).isFiniteType).Group)
    (hchar : ∀ (i : Fin 5) (s : Fˣ) (δ : Fin (e7Datum F).rank → ℤ), δ ∈ (e7Datum F).roots →
      Units.map (φ : F →+* F) s ^ cpair (e7Datum F).cartan (cvec5 i) δ =
        s ^ cpair (e7Datum F).cartan (cvec5 i) (weylAction (e7Datum F).isFiniteType w δ)) :
    φ = 1 ∧ w = 1 := by
  have hS := torusSetup_E7 F
  have hroot : ∀ k : Fin 7, (Pi.single k 1 : Fin 7 → ℤ) ∈ (e7Datum F).roots := fun k =>
    (RootSystem.ofCartan (e7Datum F).isFiniteType (e7Datum F).divisible).single_mem k
  have hmem : ∀ γ, γ ∈ (e7Datum F).roots → γ ∈ rootFinset .E7 := fun γ hγ => by
    refine mem_rootFinset.2 ?_
    have h1 : γ ∈ roots (e7Datum F).isFiniteType ∅ := roots_empty hS hγ
    exact (roots_eq isFiniteType_cartan_E7).subset h1
  have hφ : φ = 1 := by
    have hwδ := weylAction_mem_roots (e7Datum F).isFiniteType w (hroot 4)
    refine (frob_cong_wt hp2 hq φ (r := 1) (fun _ => 1) (fun _ => -1)
      (fun _ => cpair (e7Datum F).cartan (cvec5 0)
        (weylAction (e7Datum F).isFiniteType w (Pi.single (4 : Fin 7) 1 : Fin 7 → ℤ))) 0 0
      ?_ ?_ rfl rfl ?_).1
    · intro j
      exact cp5_bound _ (hmem _ hwδ) 0
    · intro j hj
      exact absurd (Subsingleton.elim j 0) hj
    · intro s j
      have h := hchar 0 s (Pi.single (4 : Fin 7) 1 : Fin 7 → ℤ) (hroot 4)
      have hd : cpair (e7Datum F).cartan (cvec5 0) (Pi.single (4 : Fin 7) 1 : Fin 7 → ℤ) = -1 :=
        cp5_zero_four
      rw [hd] at h
      simpa using h
  refine ⟨hφ, ?_⟩
  subst hφ
  by_contra hw
  obtain ⟨i, hi⟩ :=
    (coxeterMatrix (e7Datum F).isFiniteType).toCoxeterSystem.exists_rightDescent_of_ne_one hw
  have hht := ht_weylAction_single_neg (D := e7Datum F) hi
  have hβ := weylAction_mem_roots (e7Datum F).isFiniteType w (hroot i)
  have hneg : ∀ j, weylAction (e7Datum F).isFiniteType w (Pi.single i 1) j ≤ 0 := by
    rcases cp5_sign _ (hmem _ hβ) with h | h
    · exfalso
      have : 0 ≤ ht (weylAction (e7Datum F).isFiniteType w (Pi.single i 1)) :=
        Finset.sum_nonneg fun j _ => h j
      omega
    · exact h
  refine cp5_neg i _ (hmem _ hβ) hneg fun i' => ?_
  have hb := cp5_bound (Pi.single i 1) (hmem _ (hroot i)) i'
  have hb' := cp5_bound _ (hmem _ hβ) i'
  refine zpow_eq_cases hq (by rw [abs_le] at hb hb' ⊢; omega) fun s => ?_
  have h := hchar i' s (Pi.single i 1) (hroot i)
  rwa [map_one_units] at h

theorem e7_hc [Finite F] : ∀ γ ∈ (e7Datum F).roots, ∃ i : Fin 5,
    cpair (e7Datum F).cartan (cvec5 i) γ ≠ 0 ∧ |cpair (e7Datum F).cartan (cvec5 i) γ| ≤ 2 := by
  intro γ hγ
  have hS := torusSetup_E7 F
  have hmem : γ ∈ rootFinset .E7 := by
    refine mem_rootFinset.2 ?_
    have h1 : γ ∈ roots (e7Datum F).isFiniteType ∅ := roots_empty hS hγ
    exact (roots_eq isFiniteType_cartan_E7).subset h1
  obtain ⟨i, hi⟩ := cp5_nonzero γ hmem
  exact ⟨i, hi, cp5_bound γ hmem i⟩

end CFSG.ClassicalInvolution.ModelFacts.E7Model
