module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.InputLPerm
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.InputLPermCentre
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.InputLDescent
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.InputLDescentCentral
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.InputLShape

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Equiv Equiv.Perm Subgroup

variable {X : Type*} [Group X] [Finite X] {t : X} {Sg V K : Subgroup X}

private lemma pi_ne_one_of_card_fixed_eight {π : Perm (Fin 12)}
    (hf : Fintype.card {x : Fin 12 // π x = x} = 8) : π ≠ 1 := by
  intro h
  rw [h] at hf
  have h12 : Fintype.card {x : Fin 12 // (1 : Perm (Fin 12)) x = x} = 12 :=
    (Fintype.card_congr (Equiv.subtypeUnivEquiv (fun _ : Fin 12 => rfl))).trans
      (Fintype.card_fin 12)
  omega

private theorem card_alt_inf_centralizer_of_eight {π : Perm (Fin 12)}
    (hπ2 : π * π = 1) (h1 : π ≠ 1)
    (hf : Fintype.card {x : Fin 12 // π x = x} = 8) :
    Nat.card (alternatingGroup (Fin 12) ⊓
      Subgroup.centralizer ({π} : Set (Perm (Fin 12))) : Subgroup (Perm (Fin 12))) = 161280 := by
  have hk : Multiset.card π.cycleType = 2 := by
    have h := card_fixed_add_two_mul_card_cycleType (m := 12) hπ2
    omega
  have h2 := two_mul_card_alt_inf_centralizer (m := 12) hπ2 h1
  rw [hf, hk] at h2
  have hprod : (8 : ℕ).factorial * 2 ^ 2 * (2 : ℕ).factorial = 322560 := by decide
  rw [hprod] at h2
  omega

theorem centralizer_le_of_twelve [K.Normal] (hS : SwapShape t Sg V)
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin 12)) {π : Perm (Fin 12)}
    (hπ2 : π * π = 1)
    (hπ : ∀ k : K, toPerm e (MulAut.conjNormal t k) = π * toPerm e k * π⁻¹)
    (hf : Fintype.card {x : Fin 12 // π x = x} = 8) : centralizer ({t} : Set X) ≤ K := by
  have h1 : π ≠ 1 := pi_ne_one_of_card_fixed_eight hf
  have hcardA : Nat.card (alternatingGroup (Fin 12) ⊓
      Subgroup.centralizer ({π} : Set (Perm (Fin 12))) : Subgroup (Perm (Fin 12))) = 161280 :=
    card_alt_inf_centralizer_of_eight hπ2 h1 hf
  have hle := card_range_inf_centralizer_le (toPerm e) (by rw [ker_toPerm]) π hπ
  rw [range_toPerm e] at hle
  rw [hcardA] at hle
  have hup : Nat.card (K ⊓ Subgroup.centralizer ({t} : Set X) : Subgroup X) ≤ 161280 := by
    calc Nat.card (K ⊓ Subgroup.centralizer ({t} : Set X) : Subgroup X)
        ≤ Nat.card (Subgroup.centralizer ({t} : Set X)) :=
          Subgroup.card_le_of_le inf_le_right
      _ = 161280 := SwapShape.card_centralizer hS
  have hEq : (K ⊓ Subgroup.centralizer ({t} : Set X) : Subgroup X) =
      Subgroup.centralizer ({t} : Set X) := by
    refine Subgroup.eq_of_le_of_card_ge inf_le_right ?_
    rw [SwapShape.card_centralizer hS]
    exact hle
  intro c hc
  have hc' : c ∈ (K ⊓ Subgroup.centralizer ({t} : Set X) : Subgroup X) := by
    rw [hEq]; exact hc
  exact hc'.1

theorem exists_lift_of_twelve [K.Normal] (hS : SwapShape t Sg V)
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin 12)) (hZ : Subgroup.center K = ⊥)
    {π : Perm (Fin 12)} (hπ2 : π * π = 1)
    (hπ : ∀ k : K, toPerm e (MulAut.conjNormal t k) = π * toPerm e k * π⁻¹)
    (hf : Fintype.card {x : Fin 12 // π x = x} = 8) {g : Perm (Fin 12)}
    (hg : g ∈ alternatingGroup (Fin 12) ⊓ centralizer ({π} : Set (Perm (Fin 12)))) :
    ∃ k : K, (k : X) ∈ centralizer ({t} : Set X) ∧ toPerm e k = g := by
  have h1 : π ≠ 1 := pi_ne_one_of_card_fixed_eight hf
  have hcardA : Nat.card (alternatingGroup (Fin 12) ⊓
      Subgroup.centralizer ({π} : Set (Perm (Fin 12))) : Subgroup (Perm (Fin 12))) = 161280 :=
    card_alt_inf_centralizer_of_eight hπ2 h1 hf
  have hCK : Subgroup.centralizer ({t} : Set X) ≤ K := centralizer_le_of_twelve hS e hπ2 hπ hf
  have hinj : Function.Injective (toPerm e) := by
    rw [← MonoidHom.ker_eq_bot_iff, ker_toPerm, hZ]
  have hcardC' : Nat.card ((Subgroup.centralizer ({t} : Set X)).subgroupOf K) = 161280 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCK).toEquiv]
    exact SwapShape.card_centralizer hS
  let C' : Subgroup K := (Subgroup.centralizer ({t} : Set X)).subgroupOf K
  let A : Subgroup (Perm (Fin 12)) :=
    alternatingGroup (Fin 12) ⊓ Subgroup.centralizer ({π} : Set (Perm (Fin 12)))
  have hmap_le : C'.map (toPerm e) ≤ A := by
    rintro x ⟨y, hy, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← range_toPerm e]
      exact MonoidHom.mem_range.mpr ⟨y, rfl⟩
    · have hyC : (y : X) ∈ Subgroup.centralizer ({t} : Set X) := hy
      have hyconj : MulAut.conjNormal t y = y := by
        ext
        rw [MulAut.conjNormal_apply]
        have hyC' : (y : X) * t = t * (y : X) :=
          Subgroup.mem_centralizer_singleton_iff.mp hyC
        rw [← hyC']
        simp
      have hconj := hπ y
      rw [hyconj] at hconj
      have hcomm : toPerm e y * π = π * toPerm e y := by
        calc toPerm e y * π = (π * toPerm e y * π⁻¹) * π := by
              conv_lhs => rw [hconj]
          _ = π * toPerm e y := by group
      exact Subgroup.mem_centralizer_singleton_iff.mpr hcomm
  have hcardMap : Nat.card (C'.map (toPerm e)) = 161280 := by
    rw [Subgroup.card_map_of_injective hinj, hcardC']
  have hEq : C'.map (toPerm e) = A := by
    refine Subgroup.eq_of_le_of_card_ge hmap_le ?_
    change Nat.card (alternatingGroup (Fin 12) ⊓
        Subgroup.centralizer ({π} : Set (Perm (Fin 12))) : Subgroup (Perm (Fin 12))) ≤
      Nat.card (C'.map (toPerm e))
    rw [hcardA, hcardMap]
  have hgM : g ∈ C'.map (toPerm e) := by
    rw [hEq]
    change g ∈ alternatingGroup (Fin 12) ⊓
      Subgroup.centralizer ({π} : Set (Perm (Fin 12)))
    exact hg
  rw [Subgroup.mem_map] at hgM
  obtain ⟨k, hk, hkeq⟩ := hgM
  exact ⟨k, hk, hkeq⟩

theorem false_of_twelve [K.Normal] (hS : SwapShape t Sg V)
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin 12)) (hZ : Subgroup.center K = ⊥)
    {π : Perm (Fin 12)} (hπ2 : π * π = 1)
    (hπ : ∀ k : K, toPerm e (MulAut.conjNormal t k) = π * toPerm e k * π⁻¹)
    (hf : Fintype.card {x : Fin 12 // π x = x} = 8) : False := by
  classical
  have hCK : Subgroup.centralizer ({t} : Set X) ≤ K := centralizer_le_of_twelve hS e hπ2 hπ hf
  have hVK : V ≤ K := (SwapShape.v_le_centralizer hS).trans hCK
  let φ : V → Perm (Fin 12) := fun v => toPerm e ⟨(v : X), hVK v.2⟩
  have hφ : ∀ v : V, φ v = 1 ∨ φ v = π := by
    intro v
    have hcomm : ∀ g' ∈ (alternatingGroup (Fin 12) ⊓
        Subgroup.centralizer ({π} : Set (Perm (Fin 12))) : Subgroup (Perm (Fin 12))),
        g' * φ v = φ v * g' := by
      intro g' hg'
      obtain ⟨k', hk'C, hk'eq⟩ := exists_lift_of_twelve hS e hZ hπ2 hπ hf hg'
      have hmul : (⟨(v : X), hVK v.2⟩ : K) * k' = k' * ⟨(v : X), hVK v.2⟩ := by
        apply Subtype.ext
        change (v : X) * (k' : X) = (k' : X) * (v : X)
        exact SwapShape.mul_comm_of_mem_v_of_mem_centralizer hS v.2 hk'C
      have hthis := congrArg (toPerm e) hmul
      simp only [map_mul] at hthis
      rw [hk'eq] at hthis
      exact hthis.symm
    have hcφ : φ v ∈ (alternatingGroup (Fin 12) ⊓
        Subgroup.centralizer ({π} : Set (Perm (Fin 12))) : Subgroup (Perm (Fin 12))) := by
      refine ⟨?_, ?_⟩
      · rw [← range_toPerm e]
        exact MonoidHom.mem_range.mpr ⟨⟨(v : X), hVK v.2⟩, rfl⟩
      · have hvC : (v : X) ∈ Subgroup.centralizer ({t} : Set X) :=
          SwapShape.v_le_centralizer hS v.2
        have hconj : MulAut.conjNormal t ⟨(v : X), hVK v.2⟩ = ⟨(v : X), hVK v.2⟩ := by
          ext
          rw [MulAut.conjNormal_apply]
          have hvC' : (v : X) * t = t * (v : X) :=
            Subgroup.mem_centralizer_singleton_iff.mp hvC
          rw [← hvC']
          simp
        have hπv := hπ ⟨(v : X), hVK v.2⟩
        rw [hconj] at hπv
        have hφv : φ v = π * φ v * π⁻¹ := hπv
        have hcomm' : φ v * π = π * φ v := by
          calc φ v * π = (π * φ v * π⁻¹) * π := by
                conv_lhs => rw [hφv]
            _ = π * φ v := by group
        exact Subgroup.mem_centralizer_singleton_iff.mpr hcomm'
    exact eq_one_or_eq_of_forall_commute hπ2 hf hcφ hcomm
  have hφinj : Function.Injective φ := by
    have hinj : Function.Injective (toPerm e) := by
      rw [← MonoidHom.ker_eq_bot_iff, ker_toPerm, hZ]
    intro u w h
    have hker : (⟨(u : X), hVK u.2⟩ : K) = ⟨(w : X), hVK w.2⟩ := hinj h
    exact Subtype.ext (congrArg (Subtype.val : K → X) hker)
  have hcard_le : Nat.card V ≤ 2 := by
    let f : V → Fin 2 := fun v => if φ v = 1 then 0 else 1
    have hfinj : Function.Injective f := by
      intro u w hfw
      have hu := hφ u
      have hw := hφ w
      by_cases hu1 : φ u = 1
      · have hfwu : f u = 0 := by simp [f, hu1]
        have hfw0 : f w = 0 := by rw [← hfw, hfwu]
        have hw1 : φ w = 1 := by
          by_cases hw1' : φ w = 1
          · exact hw1'
          · exfalso
            have h1' : f w = (1 : Fin 2) := by simp [f, hw1']
            rw [h1'] at hfw0
            exact absurd hfw0 (by decide)
        exact hφinj (by rw [hu1, hw1])
      · have huπ : φ u = π := hu.resolve_left hu1
        have hfu : f u = 1 := by simp [f, hu1]
        have hfw1 : f w = 1 := by rw [← hfw, hfu]
        have hwπ : φ w = π := by
          by_cases hw1' : φ w = 1
          · exfalso
            have h0' : f w = (0 : Fin 2) := by simp [f, hw1']
            rw [h0'] at hfw1
            exact absurd hfw1 (by decide)
          · exact hw.resolve_left hw1'
        exact hφinj (by rw [huπ, hwπ])
    calc Nat.card V ≤ Nat.card (Fin 2) := Nat.card_le_card_of_injective f hfinj
      _ = 2 := by simp
  rw [SwapShape.card_v hS] at hcard_le
  omega

end CFSG.OddStandard.AltStdSec.SwapPartner
