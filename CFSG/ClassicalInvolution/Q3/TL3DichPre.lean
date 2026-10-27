module

public import CFSG.ClassicalInvolution.Q3.TL3DichComm
public import CFSG.ClassicalInvolution.Q3.TL3S8Std
public import CFSG.ClassicalInvolution.Asc77.AscThmABasic

public section

namespace CFSG.ClassicalInvolution.Q3.TightA

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.LocalCores
open scoped commutatorElement

variable {Y : Type} [Group Y] [Finite Y]

theorem isPGroup_two_of_normal_nilpotent (hO : classicalInvolutionOddCore Y = ⊥)
    {N : Subgroup Y} (hN : N.Normal) (hnil : Group.IsNilpotent ↥N) : IsPGroup 2 ↥N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : N ≤ fittingSubgroup Y := fitting_characteristic.2.2 N hN hnil
  have hF2 : fittingSubgroup Y ≤ pCore 2 Y := by
    rw [fittingSubgroup_eq_iSup_pCore]
    refine iSup_le fun q => ?_
    have hq : (q : ℕ).Prime := Nat.prime_of_mem_primeFactors q.2
    have : Fact (q : ℕ).Prime := ⟨hq⟩
    by_cases hq2 : (q : ℕ) = 2
    · rw [hq2]
    · have hn : (pCore (q : ℕ) Y).Normal := pCore_normal
      have hodd : Odd (Nat.card ↥(pCore (q : ℕ) Y)) := by
        obtain ⟨k, hk⟩ := (pCore_isPGroup : IsPGroup (q : ℕ) (pCore (q : ℕ) Y)).exists_card_eq
        rw [hk]
        exact Odd.pow (hq.odd_of_ne_two hq2)
      have hle : pCore (q : ℕ) Y ≤ classicalInvolutionOddCore Y := le_sSup ⟨hn, hodd⟩
      rw [hO] at hle
      exact hle.trans bot_le
  exact (pCore_isPGroup : IsPGroup 2 (pCore 2 Y)).to_le (hF.trans hF2)

theorem mem_centralizer_layer_of_mem_center {A : Subgroup Y} (hA : CFSG.IsComponent A)
    {z : Y} (hzA : z ∈ A) (hz : ∀ y ∈ A, y * z = z * y) :
    z ∈ Subgroup.centralizer (layer Y : Set Y) := by
  have hle : layer Y ≤ Subgroup.centralizer ({z} : Set Y) := by
    refine sSup_le fun K hK y hy => Subgroup.mem_centralizer_singleton_iff.mpr ?_
    by_cases hKA : K = A
    · subst hKA
      exact (hz y hy)
    · exact (AscThmA.mul_comm_of_ne hK hA hKA hy hzA)
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hy))

omit [Finite Y] in
theorem centerLayer_normal :
    (layer Y ⊓ Subgroup.centralizer (layer Y : Set Y)).Normal := by
  have : (layer Y).Characteristic := layer_characteristic
  infer_instance

theorem centerLayer_isPGroup (hO : classicalInvolutionOddCore Y = ⊥) :
    IsPGroup 2 ↥(layer Y ⊓ Subgroup.centralizer (layer Y : Set Y)) := by
  have hZc : IsMulCommutative ↥(layer Y ⊓ Subgroup.centralizer (layer Y : Set Y)) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mp
      fun y hy h hh => Subgroup.mem_centralizer_iff.mp hy.2 h hh.1
  exact isPGroup_two_of_normal_nilpotent hO centerLayer_normal inferInstance

theorem mem_centerLayer_of_mem_center {A : Subgroup Y} (hA : CFSG.IsComponent A)
    {z : Y} (hzA : z ∈ A) (hz : ∀ y ∈ A, y * z = z * y) :
    z ∈ layer Y ⊓ Subgroup.centralizer (layer Y : Set Y) :=
  ⟨(le_sSup (show A ∈ {K : Subgroup Y | CFSG.IsComponent K} from hA) : A ≤ layer Y) hzA,
    mem_centralizer_layer_of_mem_center hA hzA hz⟩

theorem isPGroup_center_component (hO : classicalInvolutionOddCore Y = ⊥) {A : Subgroup Y}
    (hA : CFSG.IsComponent A) : IsPGroup 2 ↥(Subgroup.center ↥A) := by
  have : (layer Y).Characteristic := layer_characteristic
  set Z : Subgroup Y := layer Y ⊓ Subgroup.centralizer (layer Y : Set Y) with hZ
  have hZn : Z.Normal := by rw [hZ]; infer_instance
  have hZc : IsMulCommutative Z := Subgroup.le_centralizer_iff_isMulCommutative.mp
    fun y hy h hh => Subgroup.mem_centralizer_iff.mp hy.2 h hh.1
  have hZ2 : IsPGroup 2 ↥Z := isPGroup_two_of_normal_nilpotent hO hZn inferInstance
  have hAlay : A ≤ layer Y := le_sSup hA
  have hmap : (Subgroup.center ↥A).map A.subtype ≤ Z := by
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨hAlay z.2, mem_centralizer_layer_of_mem_center hA z.2 fun y hy => ?_⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨y, hy⟩)
  have h2 : IsPGroup 2 ↥((Subgroup.center ↥A).map A.subtype) := hZ2.to_le hmap
  exact h2.of_equiv ((Subgroup.center ↥A).equivMapOfInjective _ A.subtype_injective).symm

end CFSG.ClassicalInvolution.Q3.TightA

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem TightDatum.mem_of_ne_bot (hd : TightDatum R S t) {P : Subgroup Y} (hPR : P ≤ R)
    (hP2 : IsPGroup 2 ↥P) (hP : P ≠ ⊥) : t ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnt : Nontrivial ↥P := (Subgroup.nontrivial_iff_ne_bot P).mpr hP
  obtain ⟨k, hk⟩ := hP2.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact (Finite.one_lt_card_iff_nontrivial.mpr hnt).ne' hk
  have h2 : 2 ∣ Nat.card ↥P := by
    rw [hk]
    exact dvd_pow_self 2 hk0
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := ↥P) 2 h2
  have hu' : orderOf (u : Y) = 2 := by rwa [Subgroup.orderOf_coe]
  have := hd.eq_of_orderOf_eq_two (hPR u.2) hu'
  rw [← this]
  exact u.2

omit [Finite Y] in
theorem TightDatum.S₀_le (_hd : TightDatum R S t) : (S : Subgroup R).map R.subtype ≤ R :=
  Subgroup.map_subtype_le _

theorem TightDatum.S₀_mem_RSet (hd : TightDatum R S t) :
    (S : Subgroup R).map R.subtype ∈ RSet (CoreAssembly.conjClass (tightCore R)) :=
  mem_RSet_of_isSylow2In (CoreAssembly.mem_conjClass_self _) hd.sylow_core

theorem TightDatum.commute_of_normal_two (hd : TightDatum R S t) {N : Subgroup Y}
    (hN : N.Normal) (hN2 : IsPGroup 2 ↥N) (htN : t ∉ N) {s : Y}
    (hs : s ∈ (S : Subgroup R).map R.subtype) {n : Y} (hn : n ∈ N) : s * n = n * s := by
  have hSN : (S : Subgroup R).map R.subtype ⊓ N = ⊥ := by
    by_contra hne
    exact htN (Subgroup.mem_inf.mp (hd.mem_of_ne_bot (inf_le_left.trans hd.S₀_le)
      ((hd.sylow_core.2.1).to_le inf_le_left) hne)).2
  have hcomm := comm613Gen_normal hd.hypOmegaGen hd.S₀_mem_RSet hN hSN
  have hodd : oddCoreOf N = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx2 : IsPGroup 2 ↥(Subgroup.zpowers x) :=
      hN2.to_le (Subgroup.zpowers_le.mpr (oddCoreOf_le_self N hx))
    rw [Subgroup.mem_bot]
    exact eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard N) hx hx2
  rw [hodd, le_bot_iff] at hcomm
  have := Subgroup.commutator_mem_commutator hs hn
  rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
  exact this

theorem q8_cases (x : QuaternionGroup 2) :
    x = 1 ∨ x = QuaternionGroup.a 2 ∨ x * x = QuaternionGroup.a 2 := by
  revert x
  decide

theorem q8_central_sq : QuaternionGroup.a 2 * QuaternionGroup.a 2 = (1 : QuaternionGroup 2) := by
  decide

theorem q8_a2_ne : (QuaternionGroup.a 2 : QuaternionGroup 2) ≠ 1 := by decide

theorem q8_pair :
    (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.a 1 = QuaternionGroup.a 2 ∧
    (QuaternionGroup.xa 0 : QuaternionGroup 2) * QuaternionGroup.xa 0 = QuaternionGroup.a 2 ∧
    (QuaternionGroup.a 1 * QuaternionGroup.xa 0 : QuaternionGroup 2) *
      (QuaternionGroup.a 1 * QuaternionGroup.xa 0) = QuaternionGroup.a 2 := by
  decide

theorem TightDatum.q8_center (hd : TightDatum R S t) (e : ↥(S : Subgroup R) ≃* QuaternionGroup 2) :
    (((e.symm (QuaternionGroup.a 2) : ↥(S : Subgroup R)) : ↥R) : Y) = t := by
  set u : ↥(S : Subgroup R) := e.symm (QuaternionGroup.a 2) with hu
  have hu2 : u * u = 1 := by
    rw [hu, ← map_mul, q8_central_sq, map_one]
  have hu1 : u ≠ 1 := by
    rw [hu]
    intro h
    exact q8_a2_ne (by simpa using congrArg e h)
  have hord : orderOf (((u : ↥R) : Y)) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [pow_two]
      have := congrArg (fun v : ↥(S : Subgroup R) => ((v : ↥R) : Y)) hu2
      simpa using this
    · intro h
      apply hu1
      exact Subtype.ext (Subtype.ext h)
  exact hd.eq_of_orderOf_eq_two (u : ↥R).2 hord

theorem TightDatum.S₀_cases (hd : TightDatum R S t)
    (hq8 : Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup 2)) {s : Y}
    (hs : s ∈ (S : Subgroup R).map R.subtype) : s = 1 ∨ s = t ∨ s * s = t := by
  obtain ⟨e⟩ := hq8
  obtain ⟨x, hx, rfl⟩ := hs
  have hct := hd.q8_center e
  rcases q8_cases (e ⟨x, hx⟩) with h | h | h
  · left
    have : (⟨x, hx⟩ : ↥(S : Subgroup R)) = 1 := e.injective (by rw [h, map_one])
    have := congrArg (fun v : ↥(S : Subgroup R) => ((v : ↥R) : Y)) this
    simpa using this
  · right; left
    have : (⟨x, hx⟩ : ↥(S : Subgroup R)) = e.symm (QuaternionGroup.a 2) := by
      rw [← h, MulEquiv.symm_apply_apply]
    rw [← hct, ← this]
    rfl
  · right; right
    have : (⟨x, hx⟩ : ↥(S : Subgroup R)) * ⟨x, hx⟩ = e.symm (QuaternionGroup.a 2) := by
      rw [← h, ← map_mul, MulEquiv.symm_apply_apply]
    rw [← hct, ← this]
    rfl

theorem TightDatum.exists_S₀_pair (hd : TightDatum R S t)
    (hq8 : Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup 2)) :
    ∃ r₁ ∈ (S : Subgroup R).map R.subtype, ∃ r₂ ∈ (S : Subgroup R).map R.subtype,
      r₁ * r₁ = t ∧ r₂ * r₂ = t ∧ (r₁ * r₂) * (r₁ * r₂) = t := by
  obtain ⟨e⟩ := hq8
  have hct := hd.q8_center e
  obtain ⟨h1, h2, h3⟩ := q8_pair
  set u₁ : ↥(S : Subgroup R) := e.symm (QuaternionGroup.a 1)
  set u₂ : ↥(S : Subgroup R) := e.symm (QuaternionGroup.xa 0)
  refine ⟨((u₁ : ↥R) : Y), ⟨u₁, u₁.2, rfl⟩, ((u₂ : ↥R) : Y), ⟨u₂, u₂.2, rfl⟩, ?_, ?_, ?_⟩
  · have : u₁ * u₁ = e.symm (QuaternionGroup.a 2) := by rw [← h1, map_mul]
    rw [← hct, ← this]
    rfl
  · have : u₂ * u₂ = e.symm (QuaternionGroup.a 2) := by rw [← h2, map_mul]
    rw [← hct, ← this]
    rfl
  · have : (u₁ * u₂) * (u₁ * u₂) = e.symm (QuaternionGroup.a 2) := by
      rw [← h3, map_mul, map_mul]
    rw [← hct, ← this]
    rfl

end CFSG.ClassicalInvolution.Q3
