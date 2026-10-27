module

public import CFSG.LieType.Steinberg.Bruhat
public import CFSG.LieType.Steinberg.CentralExt.Unipotent
public import CFSG.ClassicalInvolution.ModelFacts.OddCover.Sieg
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.ClassicalInvolution.WeakCT

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.ClassicalInvolution.ModelFacts.OddCover

section Datum

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

theorem commute_of_mem_torus (hext : SteinbergExtras D n H) {x y : K}
    (hx : x ∈ ⨆ i, H i) (hy : y ∈ ⨆ i, H i) : Commute x y := by
  have h1 : ∀ i, ∀ h ∈ H i, ∀ y ∈ ⨆ i, H i, Commute h y := fun i h hh y hy => by
    refine Subgroup.iSup_induction H (C := fun y => Commute h y) hy (fun j z hz => ?_)
      (Commute.one_right h) (fun a b ha hb => ha.mul_right hb)
    exact hext.torus_commute i j h hh z hz
  refine Subgroup.iSup_induction H (C := fun x => Commute x y) hx (fun i h hh => ?_)
    (Commute.one_left y) (fun a b ha hb => ha.mul_left hb)
  exact (h1 i h hh y hy)

theorem pow_eq_one_of_mem_torus (hext : SteinbergExtras D n H) {M : ℕ}
    (hM : ∀ i, ∀ g ∈ H i, g ^ M = 1) {t : K} (ht : t ∈ ⨆ i, H i) : t ^ M = 1 := by
  refine Subgroup.iSup_induction H (C := fun t => t ^ M = 1 ∧ t ∈ ⨆ i, H i) ht
    (fun i g hg => ⟨hM i g hg, Subgroup.mem_iSup_of_mem i hg⟩) ⟨one_pow M, Subgroup.one_mem _⟩
    (fun a b ha hb => ?_) |>.1
  exact ⟨by rw [(commute_of_mem_torus hext ha.2 hb.2).mul_pow, ha.1, hb.1, mul_one],
    Subgroup.mul_mem _ ha.2 hb.2⟩

variable (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
  (weylAction D.isFiniteType) D.roots D.rootGroup n H)
include hct

theorem torus_le_normalizer_posUnipotent :
    (⨆ i, H i) ≤ Subgroup.normalizer (posUnipotent D : Set K) := by
  refine fun t htT => ?_
  have := le_normalizer_iSup₂ (X := D.rootGroup) (P := {γ | γ ∈ D.roots ∧ 0 < ht γ})
    (A := ⨆ i, H i) (fun x hx γ hγ y hy => by
      have h1 : x * y * x⁻¹ ∈ D.rootGroup γ := by
        refine Subgroup.iSup_induction H
          (C := fun t => ∀ y ∈ D.rootGroup γ, t * y * t⁻¹ ∈ D.rootGroup γ) hx
          (fun k h hh y hy => hct.H_conj_mem k γ hγ.1 h hh y hy) (fun y hy => by simpa using hy)
          (fun a b ha hb y hy => ?_) y hy
        have := ha _ (hb y hy)
        rwa [show a * (b * y * b⁻¹) * a⁻¹ = a * b * y * (a * b)⁻¹ by group] at this
      exact Subgroup.mem_iSup_of_mem γ (Subgroup.mem_iSup_of_mem hγ h1))
  exact this htT

theorem borel_le_normalizer_posUnipotent :
    borel D H ≤ Subgroup.normalizer (posUnipotent D : Set K) :=
  sup_le (torus_le_normalizer_posUnipotent hct) Subgroup.le_normalizer

variable (hext : SteinbergExtras D n H)
include hext

theorem normalizer_posUnipotent_le_borel :
    Subgroup.normalizer (posUnipotent D : Set K) ≤ borel D H := by
  intro x hx
  obtain ⟨w, b₁, hb₁, b₂, hb₂, rfl⟩ := exists_mem_bruhatCell hct hext x
  have hw : nrep hct w ∈ Subgroup.normalizer (posUnipotent D : Set K) := by
    have hB := borel_le_normalizer_posUnipotent hct
    have h1 : b₁⁻¹ * (b₁ * nrep hct w * b₂) * b₂⁻¹ ∈
        Subgroup.normalizer (posUnipotent D : Set K) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hB hb₁)) hx)
        (Subgroup.inv_mem _ (hB hb₂))
    simpa [mul_assoc] using h1
  have hw1 : w = 1 := by
    by_contra hne
    obtain ⟨i, hi⟩ := CoxeterSystem.exists_rightDescent_of_ne_one
      ((coxeterMatrix D.isFiniteType).toCoxeterSystem) hne
    set γ : Fin D.rank → ℤ := Pi.single i 1 with hγ
    have hγr : γ ∈ D.roots := (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i
    have hγpos : 0 < ht γ := ht_single_pos i
    have hneg : ht (weylAction D.isFiniteType w γ) < 0 := ht_weylAction_single_neg hi
    have hwr := weylAction_mem_roots D.isFiniteType w hγr
    have hle1 : D.rootGroup (weylAction D.isFiniteType w γ) ≤ posUnipotent D := by
      rw [← actsAs_nrep hct w γ hγr]
      rintro _ ⟨u, hu, rfl⟩
      have hu' : u ∈ posUnipotent D := rootGroup_le_posUnipotent hγr hγpos hu
      have := (Subgroup.mem_normalizer_iff.1 hw u).1 hu'
      simpa using this
    have hle2 : D.rootGroup (weylAction D.isFiniteType w γ) ≤ negUnipotent D :=
      rootGroup_le_negUnipotent hwr hneg
    have hbot : D.rootGroup (weylAction D.isFiniteType w γ) = ⊥ := by
      refine eq_bot_iff.2 ?_
      rw [← hext.posPart_inf_negPart]
      exact le_inf hle1 hle2
    exact hext.ne_bot _ hwr hbot
  subst hw1
  rw [nrep_one, mul_one]
  exact Subgroup.mul_mem _ hb₁ hb₂

theorem not_dvd_index_posUnipotent [Finite K] {p : ℕ} [Fact p.Prime]
    (hX : ∀ γ ∈ D.roots, IsPGroup p (D.rootGroup γ)) {M : ℕ} (hMp : Nat.Coprime p M)
    (hM : ∀ i, ∀ g ∈ H i, g ^ M = 1) : ¬ p ∣ (posUnipotent D).index := by
  classical
  set U := posUnipotent D with hUdef
  have hU : IsPGroup p U := isPGroup_iSup_pos hext hX
  obtain ⟨S, hUS⟩ := hU.exists_le_sylow
  have hB := normalizer_posUnipotent_le_borel hct hext
  have hpel : ∀ x : K, x ∈ Subgroup.normalizer (U : Set K) → (∃ k : ℕ, x ^ p ^ k = 1) → x ∈ U := by
    intro x hx ⟨k, hk⟩
    have hxB : x ∈ U ⊔ ⨆ i, H i := by
      have := hB hx
      rwa [borel, sup_comm] at this
    obtain ⟨u, hu, t, htT, rfl⟩ := (mem_sup_iff_of_normalizes (Q := U) (A := ⨆ i, H i)
      (fun a ha q hq => by
        have := (Subgroup.mem_normalizer_iff.1
          (torus_le_normalizer_posUnipotent hct ha) q).1 hq
        simpa using this) ).1 hxB
    have hpow : ∀ j : ℕ, ∃ u' ∈ U, (u * t) ^ j = u' * t ^ j := by
      intro j
      induction j with
      | zero => exact ⟨1, U.one_mem, by simp⟩
      | succ j ih =>
        obtain ⟨u', hu', h⟩ := ih
        have htj : t ^ j ∈ ⨆ i, H i := Subgroup.pow_mem _ htT j
        have hc : t ^ j * u * (t ^ j)⁻¹ ∈ U := by
          have := (Subgroup.mem_normalizer_iff.1
            (torus_le_normalizer_posUnipotent hct htj) u).1 hu
          simpa using this
        refine ⟨u' * (t ^ j * u * (t ^ j)⁻¹), U.mul_mem hu' hc, ?_⟩
        rw [pow_succ, h]
        group
    obtain ⟨u', hu', hM'⟩ := hpow M
    have htM : t ^ M = 1 := pow_eq_one_of_mem_torus hext hM htT
    rw [htM, mul_one] at hM'
    have hxM : (u * t) ^ M ∈ U := hM' ▸ hu'
    have hcop : IsCoprime (M : ℤ) ((p ^ k : ℕ) : ℤ) :=
      Nat.isCoprime_iff_coprime.2 (Nat.Coprime.pow_right k hMp.symm)
    obtain ⟨a, b, hab⟩ := hcop
    have key : u * t = ((u * t) ^ M) ^ a :=
      calc u * t = (u * t) ^ (a * (M : ℤ) + b * ((p ^ k : ℕ) : ℤ)) := by rw [hab, zpow_one]
        _ = ((u * t) ^ M) ^ a := by
          rw [zpow_add, mul_comm a, zpow_mul, mul_comm b, zpow_mul, zpow_natCast, zpow_natCast,
            hk, one_zpow, mul_one]
    rw [key]
    exact Subgroup.zpow_mem _ hxM a
  have hSU : (S : Subgroup K) ≤ U := by
    by_contra hnot
    have hne : U.subgroupOf (S : Subgroup K) ≠ ⊤ := fun h => hnot (by
      intro x hx
      have : (⟨x, hx⟩ : (S : Subgroup K)) ∈ U.subgroupOf (S : Subgroup K) := by rw [h]; trivial
      exact this)
    have hnil : Group.IsNilpotent ↥(S : Subgroup K) := (S.isPGroup').isNilpotent
    have hlt := Group.normalizerCondition_of_isNilpotent (G := ↥(S : Subgroup K))
      (U.subgroupOf (S : Subgroup K)) (lt_top_iff_ne_top.2 hne)
    obtain ⟨y, hyN, hyU⟩ := IsConcreteLE.exists_of_lt hlt
    have hyN' : (y : K) ∈ Subgroup.normalizer (U : Set K) := by
      rw [Subgroup.mem_normalizer_iff]
      intro u
      have hy' := Subgroup.mem_normalizer_iff.1 hyN
      constructor
      · intro hu
        have := (hy' ⟨u, hUS hu⟩).1 (by simpa [Subgroup.mem_subgroupOf] using hu)
        simpa [Subgroup.mem_subgroupOf] using this
      · intro hu
        have huS : u ∈ (S : Subgroup K) := by
          have h1 : (y : K)⁻¹ * ((y : K) * u * (y : K)⁻¹) * y ∈ (S : Subgroup K) :=
            (S : Subgroup K).mul_mem ((S : Subgroup K).mul_mem ((S : Subgroup K).inv_mem y.2)
              (hUS hu)) y.2
          simpa [mul_assoc] using h1
        have := (hy' ⟨u, huS⟩).2 (by simpa [Subgroup.mem_subgroupOf] using hu)
        simpa [Subgroup.mem_subgroupOf] using this
    obtain ⟨k, hk⟩ := S.isPGroup' y
    have hk' : (y : K) ^ p ^ k = 1 := by
      have := congrArg (fun g : (S : Subgroup K) => (g : K)) hk
      simpa using this
    exact hyU (Subgroup.mem_subgroupOf.2 (hpel y hyN' ⟨k, hk'⟩))
  have hUeq : (S : Subgroup K) = U := le_antisymm hSU hUS
  rw [← hUeq]
  exact S.not_dvd_index

end Datum

end CFSG.ClassicalInvolution.WeakCT
