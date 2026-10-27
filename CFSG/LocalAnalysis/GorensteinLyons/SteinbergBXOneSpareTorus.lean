module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBXClassicalTorus
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBXCentralLift

public section

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup Equiv CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

universe u v w

theorem torus_lift_conclusions {L : Type v} [Group L] [Finite L] {S : Type*} [Group S]
    {M : Type*} [CommGroup M] {n : ℕ} (A : Subgroup (Fin n → M))
    (hAperm : ∀ (σ : Perm (Fin n)) (v : Fin n → M), v ∈ A → v ∘ σ ∈ A) (δ : A →* S)
    (hker : ∀ v : A, δ v = 1 → ∀ j k, (v : Fin n → M) j = (v : Fin n → M) k)
    (W : Fin n → Fin n → S)
    (hW : ∀ (a b : Fin n) (v : A), W a b * δ v * (W a b)⁻¹ =
      δ ⟨v ∘ swap a b, hAperm (swap a b) v v.2⟩)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {ζ : M} (hζ : orderOf ζ = p) {m : ℕ} (hm : m + 1 < n)
    (hτ : ∀ i : Fin m, torusVec ζ ⟨i, by omega⟩ ⟨m, by omega⟩ ∈ A) (π : L →* S)
    (hπ : Function.Surjective π) (hZ : π.ker ≤ center L) :
    CFSG.IsElementaryAbelian p (closure (Set.range fun i => δ ⟨_, hτ i⟩)) ∧
      Nat.card (closure (Set.range fun i => δ ⟨_, hτ i⟩)) = p ^ m ∧
      (∀ x ∈ (closure (Set.range fun i => δ ⟨_, hτ i⟩)).comap π,
        ∀ y ∈ (closure (Set.range fun i => δ ⟨_, hτ i⟩)).comap π, Commute x y) ∧
      (∃ V : Subgroup L, CFSG.IsElementaryAbelian p V ∧ Set.InjOn π V ∧
        V.map π = closure (Set.range fun i => δ ⟨_, hτ i⟩)) ∧
      ∀ (T : Type w) [Group T] [Finite T], IsPGroup 2 T → ∀ α : T →* MulAut L,
        (∀ t, ∀ z ∈ π.ker, α t z ∈ π.ker) →
        (∀ t, ∀ x ∈ (closure (Set.range fun i => δ ⟨_, hτ i⟩)).comap π,
          α t x ∈ (closure (Set.range fun i => δ ⟨_, hτ i⟩)).comap π) →
        (∀ t, ∀ x ∈ (closure (Set.range fun i => δ ⟨_, hτ i⟩)).comap π, π (α t x) = π x) →
        ∃ V : Subgroup L, CFSG.IsElementaryAbelian p V ∧ Set.InjOn π V ∧
          V.map π = closure (Set.range fun i => δ ⟨_, hτ i⟩) ∧ ∀ t, ∀ x ∈ V, α t x = x := by
  obtain ⟨hcp, hc1, hcomm, hind, hinv, hpair⟩ := torus_weyl_hypotheses A hAperm δ hker W hW hp2
    hζ (fun i : Fin m => (⟨i, by omega⟩ : Fin n)) (fun i j h => Fin.ext (by
      have := congrArg Fin.val h
      simpa using this)) ⟨m, by omega⟩ ⟨m + 1, hm⟩
    (fun i h => by
      have := congrArg Fin.val h
      simp only at this
      omega)
    (fun i h => by
      have := congrArg Fin.val h
      simp only at this
      omega)
    (fun h => by
      have := congrArg Fin.val h
      simp only at this
      omega) hτ
  obtain ⟨v, -, -, -, hEA, hcard, hinj, hmap, hab⟩ :=
    exists_lift_of_weyl hp2 π hπ hZ _ hcp hc1 hcomm hind hinv hpair
  rw [Fintype.card_fin] at hcard
  have hcardA : Nat.card (closure (Set.range fun i => δ ⟨_, hτ i⟩)) = p ^ m := by
    rw [← hmap, ← hcard]
    exact Nat.card_image_of_injOn hinj
  have hEA' : CFSG.IsElementaryAbelian p (closure (Set.range fun i => δ ⟨_, hτ i⟩)) := by
    rw [← hmap]
    exact CFSG.IsElementaryAbelian.map π
  refine ⟨hEA', hcardA, hab, ⟨_, hEA, hinj, hmap⟩, fun T _ _ hT α hkerT _ hfix => ?_⟩
  obtain ⟨w, -, -, hwfix, hEA'', -, hinj', hmap'⟩ :=
    exists_fixed_lift_of_weyl hp2 π hπ hZ _ hcp hc1 hcomm hind hinv hpair hT α hkerT hfix
  refine ⟨_, hEA'', hinj', hmap', fun t x hx => ?_⟩
  induction hx using closure_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    exact hwfix t i
  | one => exact map_one _
  | mul y z _ _ hy hz => rw [map_mul, hy, hz]
  | inv y _ hy => rw [map_inv, hy]

section Families

variable (F : Type*) [Field F] (n m : ℕ) (hm : m < n)

@[expose] def linearTorusFamily (ζ : Fˣ) : Fin m → Matrix.ProjectiveSpecialLinearGroup (Fin n) F :=
  fun i => linearTorusClass F n ζ ⟨i, by omega⟩ ⟨m, hm⟩

@[expose] noncomputable def unitaryTorusFamily {ℓ f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData ℓ f K) {ζ : Kˣ} (hζ : h.norm (ζ : K) = 1) : Fin m → unitaryPSU h n :=
  fun i => unitaryTorusClass h n hζ ⟨i, by omega⟩ ⟨m, hm⟩

end Families

theorem linear_torus_lift_conclusions {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {n m : ℕ}
    (hm : m + 1 < n) (F : Type u) [Field F] (L : Type v) [Group L] [Finite L]
    (π : L →* Matrix.ProjectiveSpecialLinearGroup (Fin n) F) (hπ : Function.Surjective π)
    (hZ : π.ker ≤ center L) (ζ : Fˣ) (hζ : orderOf ζ = p) :
    CFSG.IsElementaryAbelian p (closure (Set.range (linearTorusFamily F n m (by omega) ζ))) ∧
      Nat.card (closure (Set.range (linearTorusFamily F n m (by omega) ζ))) = p ^ m ∧
      (∀ x ∈ (closure (Set.range (linearTorusFamily F n m (by omega) ζ))).comap π,
        ∀ y ∈ (closure (Set.range (linearTorusFamily F n m (by omega) ζ))).comap π,
          Commute x y) ∧
      (∃ V : Subgroup L, CFSG.IsElementaryAbelian p V ∧ Set.InjOn π V ∧
        V.map π = closure (Set.range (linearTorusFamily F n m (by omega) ζ))) ∧
      ∀ (T : Type w) [Group T] [Finite T], IsPGroup 2 T → ∀ α : T →* MulAut L,
        (∀ t, ∀ z ∈ π.ker, α t z ∈ π.ker) →
        (∀ t, ∀ x ∈ (closure (Set.range (linearTorusFamily F n m (by omega) ζ))).comap π,
          α t x ∈ (closure (Set.range (linearTorusFamily F n m (by omega) ζ))).comap π) →
        (∀ t, ∀ x ∈ (closure (Set.range (linearTorusFamily F n m (by omega) ζ))).comap π,
          π (α t x) = π x) →
        ∃ V : Subgroup L, CFSG.IsElementaryAbelian p V ∧ Set.InjOn π V ∧
          V.map π = closure (Set.range (linearTorusFamily F n m (by omega) ζ)) ∧
          ∀ t, ∀ x ∈ V, α t x = x :=
  torus_lift_conclusions (prodOneUnits F n) (fun σ _ hv => comp_mem_prodOneUnits σ hv)
    (linearDelta F n) (fun _ hv => linearDelta_eq_one hv) (linearWeyl F n) linearWeyl_conj hp2 hζ
    hm (fun _ => torusVec_mem_prodOneUnits ζ _ _) π hπ hZ

theorem unitary_torus_lift_conclusions {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {n m : ℕ}
    (hm : m + 1 < n) {ℓ f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K) (L : Type v)
    [Group L] [Finite L] (π : L →* unitaryPSU h n) (hπ : Function.Surjective π)
    (hZ : π.ker ≤ center L) (ζ : Kˣ) (hζN : h.norm (ζ : K) = 1) (hζ : orderOf ζ = p) :
    CFSG.IsElementaryAbelian p (closure (Set.range (unitaryTorusFamily n m (by omega) h hζN))) ∧
      Nat.card (closure (Set.range (unitaryTorusFamily n m (by omega) h hζN))) = p ^ m ∧
      (∀ x ∈ (closure (Set.range (unitaryTorusFamily n m (by omega) h hζN))).comap π,
        ∀ y ∈ (closure (Set.range (unitaryTorusFamily n m (by omega) h hζN))).comap π,
          Commute x y) ∧
      (∃ V : Subgroup L, CFSG.IsElementaryAbelian p V ∧ Set.InjOn π V ∧
        V.map π = closure (Set.range (unitaryTorusFamily n m (by omega) h hζN))) ∧
      ∀ (T : Type w) [Group T] [Finite T], IsPGroup 2 T → ∀ α : T →* MulAut L,
        (∀ t, ∀ z ∈ π.ker, α t z ∈ π.ker) →
        (∀ t, ∀ x ∈ (closure (Set.range (unitaryTorusFamily n m (by omega) h hζN))).comap π,
          α t x ∈ (closure (Set.range (unitaryTorusFamily n m (by omega) h hζN))).comap π) →
        (∀ t, ∀ x ∈ (closure (Set.range (unitaryTorusFamily n m (by omega) h hζN))).comap π,
          π (α t x) = π x) →
        ∃ V : Subgroup L, CFSG.IsElementaryAbelian p V ∧ Set.InjOn π V ∧
          V.map π = closure (Set.range (unitaryTorusFamily n m (by omega) h hζN)) ∧
          ∀ t, ∀ x ∈ V, α t x = x :=
  torus_lift_conclusions (normOneProdOne h n) (fun σ _ hv => comp_mem_normOneProdOne h σ hv)
    (unitaryDelta h n) (fun _ hv => unitaryDelta_eq_one h hv) (unitaryWeyl h n)
    (unitaryWeyl_conj h) hp2 hζ hm (fun _ => torusVec_mem_normOneProdOne h hζN _ _) π hπ hZ

theorem classical_central_cover_one_spare_torus_two_group_fixed {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {n : ℕ} (hn : 3 ≤ n) :
    (∀ (F : Type u) [Field F] [Finite F], p ∣ Nat.card F - 1 →
      ∀ (L : Type v) [Group L] [Finite L] (π : L →* Matrix.ProjectiveSpecialLinearGroup (Fin n) F),
        Function.Surjective π → π.ker ≤ center L → ∀ ζ : Fˣ, orderOf ζ = p →
        CFSG.IsElementaryAbelian p
            (closure (Set.range (linearTorusFamily F n (n - 2) (by omega) ζ))) ∧
          Nat.card (closure (Set.range (linearTorusFamily F n (n - 2) (by omega) ζ))) =
            p ^ (n - 2) ∧
          (∀ x ∈ (closure (Set.range (linearTorusFamily F n (n - 2) (by omega) ζ))).comap π,
            ∀ y ∈ (closure (Set.range (linearTorusFamily F n (n - 2) (by omega) ζ))).comap π,
              Commute x y) ∧
          (∃ V : Subgroup L, CFSG.IsElementaryAbelian p V ∧ Set.InjOn π V ∧
            V.map π = closure (Set.range (linearTorusFamily F n (n - 2) (by omega) ζ))) ∧
          ∀ (T : Type w) [Group T] [Finite T], IsPGroup 2 T → ∀ α : T →* MulAut L,
            (∀ t, ∀ z ∈ π.ker, α t z ∈ π.ker) →
            (∀ t, ∀ x ∈ (closure (Set.range (linearTorusFamily F n (n - 2) (by omega) ζ))).comap π,
              α t x ∈ (closure (Set.range (linearTorusFamily F n (n - 2) (by omega) ζ))).comap π) →
            (∀ t, ∀ x ∈ (closure (Set.range (linearTorusFamily F n (n - 2) (by omega) ζ))).comap π,
              π (α t x) = π x) →
            ∃ V : Subgroup L, CFSG.IsElementaryAbelian p V ∧ Set.InjOn π V ∧
              V.map π = closure (Set.range (linearTorusFamily F n (n - 2) (by omega) ζ)) ∧
              ∀ t, ∀ x ∈ V, α t x = x) ∧
    (∀ (ℓ f : ℕ) (K : Type) [Field K] (h : UnitaryFieldData ℓ f K), p ∣ ℓ ^ f + 1 →
      ∀ (L : Type v) [Group L] [Finite L] (π : L →* unitaryPSU h n),
        Function.Surjective π → π.ker ≤ center L → ∀ (ζ : Kˣ) (hζN : h.norm (ζ : K) = 1),
        orderOf ζ = p →
        CFSG.IsElementaryAbelian p
            (closure (Set.range (unitaryTorusFamily n (n - 2) (by omega) h hζN))) ∧
          Nat.card (closure (Set.range (unitaryTorusFamily n (n - 2) (by omega) h hζN))) =
            p ^ (n - 2) ∧
          (∀ x ∈ (closure (Set.range (unitaryTorusFamily n (n - 2) (by omega) h hζN))).comap π,
            ∀ y ∈ (closure (Set.range (unitaryTorusFamily n (n - 2) (by omega) h hζN))).comap π,
              Commute x y) ∧
          (∃ V : Subgroup L, CFSG.IsElementaryAbelian p V ∧ Set.InjOn π V ∧
            V.map π = closure (Set.range (unitaryTorusFamily n (n - 2) (by omega) h hζN))) ∧
          ∀ (T : Type w) [Group T] [Finite T], IsPGroup 2 T → ∀ α : T →* MulAut L,
            (∀ t, ∀ z ∈ π.ker, α t z ∈ π.ker) →
            (∀ t, ∀ x ∈ (closure (Set.range (unitaryTorusFamily n (n - 2) (by omega) h
              hζN))).comap π, α t x ∈
                (closure (Set.range (unitaryTorusFamily n (n - 2) (by omega) h hζN))).comap π) →
            (∀ t, ∀ x ∈ (closure (Set.range (unitaryTorusFamily n (n - 2) (by omega) h
              hζN))).comap π, π (α t x) = π x) →
            ∃ V : Subgroup L, CFSG.IsElementaryAbelian p V ∧ Set.InjOn π V ∧
              V.map π = closure (Set.range (unitaryTorusFamily n (n - 2) (by omega) h hζN)) ∧
              ∀ t, ∀ x ∈ V, α t x = x) :=
  ⟨fun F _ _ _ L _ _ π hπ hZ ζ hζ =>
    linear_torus_lift_conclusions hp2 (by omega) F L π hπ hZ ζ hζ,
    fun _ _ _ _ h _ L _ _ π hπ hZ ζ hζN hζ =>
    unitary_torus_lift_conclusions hp2 (by omega) h L π hπ hZ ζ hζN hζ⟩

end CFSG.LocalAnalysis.GorensteinLyons
