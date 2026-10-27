module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL3Field
public import CFSG.GH74.KGroups.L3EpsBlockLin
public import CFSG.GH74.KGroups.L3EpsLin
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87.P47Fld

open Matrix Subgroup CFSG CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Cover

variable {T : Type} [Group T] {F0 : Type} [Field F0] (ψ : T →* projectiveSL 3 F0)

theorem center_eq_ker (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ center T) :
    center T = ψ.ker := by
  refine le_antisymm (fun x hx => ?_) hker
  rw [MonoidHom.mem_ker]
  have hx' : ψ x ∈ center (projectiveSL 3 F0) := by
    rw [Subgroup.mem_center_iff]
    intro s
    obtain ⟨t, rfl⟩ := hψ s
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hx t]
  rw [CFSG.GH74.KGroups.L3Eps.center_projectiveSL_three_eq_bot (K := F0), Subgroup.mem_bot] at hx'
  exact hx'

theorem two_dvd_card_projectiveSL3 [Finite F0] (h2 : (2 : F0) ≠ 0) :
    2 ∣ Nat.card (projectiveSL 3 F0) := by
  have hord : orderOf (CFSG.GH74.KGroups.L3Eps.tInv : projectiveSL 3 F0) = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact CFSG.GH74.KGroups.L3Eps.tInv_mul_self)
      (CFSG.GH74.KGroups.L3Eps.tInv_ne_one h2)
  rw [← hord]
  exact orderOf_dvd_natCard _

theorem pPrimeCore_eq_ker [Finite T] [Finite F0] (h2 : (2 : F0) ≠ 0) (hψ : Function.Surjective ψ)
    (hodd : Odd (Nat.card ψ.ker)) : pPrimeCore 2 T = ψ.ker := by
  refine le_antisymm ?_ ?_
  · have hS : IsSimpleGroup (projectiveSL 3 F0) := isSimpleGroup_projectiveSL3_fl3 F0
    have hnorm : ((pPrimeCore 2 T).map ψ).Normal :=
      Subgroup.Normal.map (pPrimeCore_normal (p := 2) (G := T)) ψ hψ
    rcases hS.eq_bot_or_eq_top_of_normal ((pPrimeCore 2 T).map ψ) with hbot | htop
    · intro x hx
      have : ψ x ∈ (pPrimeCore 2 T).map ψ := Subgroup.mem_map_of_mem ψ hx
      rw [hbot, Subgroup.mem_bot] at this
      exact this
    · exfalso
      have hsurj : Function.Surjective (ψ.comp (pPrimeCore 2 T).subtype) := by
        intro s
        have : s ∈ (pPrimeCore 2 T).map ψ := by rw [htop]; exact Subgroup.mem_top s
        obtain ⟨x, hx, rfl⟩ := this
        exact ⟨⟨x, hx⟩, rfl⟩
      have hdvd := Subgroup.card_dvd_of_surjective hsurj
      have h2S := (two_dvd_card_projectiveSL3 (F0 := F0) h2).trans hdvd
      have hcop := pPrimeCore_coprime_card (p := 2) (G := T)
      exact absurd (Nat.dvd_gcd (dvd_refl 2) h2S) (by rw [hcop]; decide)
  · exact le_sSup ⟨MonoidHom.normal_ker ψ, Nat.coprime_two_left.2 hodd⟩

end Cover

section Quasi

variable {T : Type} [Group T] [Finite T] {F0 : Type} [Field F0] [Finite F0]
  (ψ : T →* projectiveSL 3 F0)

omit [Finite T] [Finite F0] in
theorem isQuasisimple_of_cover (hT : Group.IsPerfect T) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ center T) : IsQuasisimple T := by
  have hc := center_eq_ker ψ hψ hker
  let e : (T ⧸ center T) ≃* projectiveSL 3 F0 :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)
  have hS : IsSimpleGroup (projectiveSL 3 F0) := isSimpleGroup_projectiveSL3_fl3 F0
  have hSp : Group.IsPerfect (projectiveSL 3 F0) := isPerfect_projectiveSL3_fl3 F0
  refine ⟨hT, e.isSimpleGroup, ?_⟩
  by_contra hcon
  push Not at hcon
  have hcomm : IsMulCommutative (projectiveSL 3 F0) := ⟨⟨fun a b => by
    have := hcon (e.symm a) (e.symm b)
    simpa using congrArg e this⟩⟩
  have : Nontrivial (projectiveSL 3 F0) := hS.toNontrivial
  exact (Group.IsPerfect.not_isMulCommutative (G := projectiveSL 3 F0)) hcomm

@[expose] noncomputable def hatEquiv (h2 : (2 : F0) ≠ 0) (hψ : Function.Surjective ψ)
    (hodd : Odd (Nat.card ψ.ker)) : (T ⧸ pPrimeCore 2 T) ≃* projectiveSL 3 F0 :=
  (QuotientGroup.quotientMulEquivOfEq (pPrimeCore_eq_ker ψ h2 hψ hodd)).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)

theorem lieModel_of_projectiveSL3 {X : Type} [Group X] {p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n)
    (hcard : Nat.card F0 = p ^ n) (e : X ≃* projectiveSL 3 F0) : LieModel X .PSL 3 p n :=
  Or.inl ⟨by decide, ⟨hp, hn, by norm_num, by simp, by simp⟩, F0, inferInstance, inferInstance,
    hcard, ⟨e.trans (CFSG.QuasithinUnique.Id2519.projectiveSLEquivStatedProj 3 F0)⟩⟩

theorem lieModel_hat_of_cover {p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n) (hcard : Nat.card F0 = p ^ n)
    (h2 : (2 : F0) ≠ 0) (hψ : Function.Surjective ψ) (hodd : Odd (Nat.card ψ.ker)) :
    LieModel (T ⧸ pPrimeCore 2 T) .PSL 3 p n :=
  lieModel_of_projectiveSL3 hp hn hcard (hatEquiv ψ h2 hψ hodd)

end Quasi

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87.P47Fld
