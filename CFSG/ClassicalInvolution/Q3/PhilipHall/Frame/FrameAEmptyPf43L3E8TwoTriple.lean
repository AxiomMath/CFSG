module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf43L3E8TwoCore
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf5Tz
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf43L3E8Fac

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement

namespace L3E8Cfg

variable {T : Type} [Group T] [Finite T] {K : Subgroup T} {z : T} {J : Subgroup T} {zJ : T}
  {H Q E S : Subgroup T}

theorem exists_member_cent_z (cfg : L3E8Cfg K z J zJ H Q E S) {h : T}
    (hc : z * (h⁻¹ * z * h) = h⁻¹ * z * h * z) (hnot : h⁻¹ * z * h ∉ firstFactor K) :
    ∃ J₁ ∈ CoreAssembly.conjClass K, IsUniqueInvolution J₁ (h⁻¹ * z * h) ∧
      ∃ T₁ : Subgroup T, IsSylow2In T₁ J₁ ∧ T₁ ≤ Subgroup.centralizer ({z} : Set T) := by
  have hΩ : HypOmegaGen (CoreAssembly.conjClass K) := cfg.datum.hyp
  have hΩc : ConjInvariant (CoreAssembly.conjClass K) := hΩ.conjInvariant
  have hKΩ : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  have hz := cfg.datum.unique
  have hhM : h⁻¹ ∈ sigmaNorm K := (sigmaNorm K).inv_mem (cfg.prod_mem_sigmaNorm hc)
  have hzHt : z ∈ firstFactor K := cfg.Q_le_ht (cfg.E_le_Q cfg.z_mem_E)
  have h1Ht : conjSub (1 : T) (firstFactor K) = firstFactor K :=
    conjSub_eq_self_of_mem (Subgroup.one_mem _)
  set w : T := h⁻¹ * z * h with hw
  set F₂ : Subgroup T := conjSub h⁻¹ (firstFactor K) with hF₂
  have hF₂ne : conjSub (1 : T) (firstFactor K) ≠ F₂ := by
    rw [h1Ht]
    exact (cfg.prod_factor_ne hnot).symm
  have hF₂Hs : F₂ ≤ sigmaGen K := cfg.conjSub_firstFactor_le hhM
  have hzN : z ∈ Subgroup.normalizer (F₂ : Set T) :=
    cfg.sigmaGen_le_normalizer_conjSub_firstFactor hhM (cfg.ht_le hzHt)
  have hzF : z ∈ trivialOnQuot F₂ := by
    refine ⟨hzN, fun x hx => ?_⟩
    have hBN : F₂ ≤ Subgroup.normalizer (oddCoreOf (sigmaGen K) : Set T) := fun y hy =>
      mem_normalizer_iff_conjSub_eq.mpr
        (Asc77.T7V.conjSub_oddCoreOf_eq_of_mem_normalizer (Subgroup.le_normalizer (hF₂Hs hy)))
    have hle : oddCoreOf (sigmaGen K) ⊓ F₂ ≤ oddCoreOf F₂ :=
      Sec6Gen.le_oddCoreOf_of_normal inf_le_right
        (fun y hy => mem_normalizer_inf (hBN hy) (Subgroup.le_normalizer hy))
        ((oddCoreOf_odd_natCard _).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left))
    rw [commutatorElement_def]
    exact hle ⟨cfg.factor_comm (Subgroup.one_mem _) hhM hF₂ne (by rw [h1Ht]; exact hzHt) hx,
      F₂.mul_mem ((Subgroup.mem_normalizer_iff.mp hzN x).mp hx) (F₂.inv_mem hx)⟩
  have hK''Ω : conjSub h⁻¹ K ∈ CoreAssembly.conjClass K := hΩc h⁻¹ K hKΩ
  have hwK'' : IsUniqueInvolution (conjSub h⁻¹ K) w := cfg.prod_isUniqueInvolution h
  have hKHt : K ≤ firstFactor K :=
    (le_omegaGen (Relation.ReflTransGen.refl : K ∈ aStar (CoreAssembly.conjClass K) K)).trans
      le_sup_left
  have hK''F₂ : conjSub h⁻¹ K ≤ F₂ := conjSub_mono hKHt
  obtain ⟨T', hT', -⟩ := IsSylow2In.exists_ge (IsPGroup.of_bot : IsPGroup 2 (⊥ : Subgroup T))
    (bot_le : (⊥ : Subgroup T) ≤ conjSub h⁻¹ K)
  have hT'w : T' ≤ Subgroup.normalizer ((Subgroup.zpowers w : Subgroup T) : Set T) := by
    intro t ht
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact Commute.zpow_left (show Commute w t from hwK''.commute_of_mem (hT'.1 ht)) k
  have hzw : z ∈ Subgroup.normalizer ((Subgroup.zpowers w : Subgroup T) : Set T) := by
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_left (show Commute w z from hc.symm) k)
  have hz2 : IsPGroup 2 (Subgroup.zpowers z) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one, pow_one])
  obtain ⟨x, ⟨hxF, hxN⟩, hxc⟩ := AscAET.exists_conj_centralized hz2 hzF hzw hT'.2.1
    (hT'.1.trans hK''F₂) hT'w
  have hxw : x * w * x⁻¹ = w := by
    have hmem : x * w * x⁻¹ ∈ conjSub x (conjSub h⁻¹ K) := conj_mem_conjSub hwK''.mem
    have hzp : x * w * x⁻¹ ∈ Subgroup.zpowers w :=
      (Subgroup.mem_normalizer_iff.mp hxN w).mp (Subgroup.mem_zpowers w)
    have hsq : x * w * x⁻¹ * (x * w * x⁻¹) = 1 := by
      calc x * w * x⁻¹ * (x * w * x⁻¹) = x * (w * w) * x⁻¹ := by group
        _ = 1 := by rw [hwK''.sq]; group
    have hne1 : x * w * x⁻¹ ≠ 1 := fun h1 => hwK''.ne_one (by
      calc w = x⁻¹ * (x * w * x⁻¹) * x := by group
        _ = 1 := by rw [h1]; group)
    have hwK''' : Subgroup.zpowers w ≤ conjSub h⁻¹ K := Subgroup.zpowers_le.mpr hwK''.mem
    rcases hwK''.unique _ (hwK''' hzp) hsq with h1 | h1
    · exact absurd h1 hne1
    · exact h1
  refine ⟨conjSub x (conjSub h⁻¹ K), hΩc x _ hK''Ω, ?_, conjSub x T', hT'.conj x, hxc⟩
  have := hwK''.conj x
  rwa [hxw] at this

theorem exists_twinTriple_prod (cfg : L3E8Cfg K z J zJ H Q E S) {h : T}
    (hne : h⁻¹ * z * h ≠ z) (hc : z * (h⁻¹ * z * h) = h⁻¹ * z * h * z)
    (hnot : h⁻¹ * z * h ∉ firstFactor K) :
    ∃ R : Subgroup T, IsSylow2In R K ∧
      R ≤ Subgroup.centralizer ({z * (h⁻¹ * z * h)} : Set T) ∧
      TwinTriple (TwinDisc.secFam (CoreAssembly.conjClass K) (z * (h⁻¹ * z * h))) := by
  have hΩ : HypOmegaGen (CoreAssembly.conjClass K) := cfg.datum.hyp
  have hKΩ : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  have hz := cfg.datum.unique
  have h2 := TwinADescent3.isPGroup_two_quotient_conjClass cfg.datum.twoGroup
  have ha2 := cfg.prod_isPGroup hne hc
  set w : T := h⁻¹ * z * h with hw
  obtain ⟨K', hK', hK'ne⟩ := cfg.datum.twin
  have hK'Ω : K' ∈ CoreAssembly.conjClass K := hK'.1
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hK'
  obtain ⟨J₁, hJ₁, hwJ₁, T₁, hT₁, hT₁c⟩ := cfg.exists_member_cent_z hc hnot
  have hJ₁K : J₁ ≠ K := fun e => hne (hwJ₁.eq (e ▸ hz))
  have hJ₁K' : J₁ ≠ K' := fun e => hne (hwJ₁.eq (e ▸ hzK'))
  have h8T₁ : 8 ≤ Nat.card T₁ := Sec6Gen.eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hJ₁ hT₁)
  have hT₁N : T₁ ≤ Subgroup.normalizer (K : Set T) :=
    Sec6Gen.le_normalizer_of_le_centralizer hΩ hKΩ hJ₁ hJ₁K.symm hz hT₁.1 hT₁.2.1 (by omega)
      hT₁c
  have hJ₁perp : J₁ ∈ KPerp (CoreAssembly.conjClass K) K :=
    Set.mem_insert_of_mem _ ⟨hJ₁, hJ₁K, T₁, mem_RSet_of_isSylow2In hJ₁ hT₁, hT₁.1, hT₁N⟩
  have hJ₁tw : J₁ ∉ twinSet (CoreAssembly.conjClass K) K := fun hm =>
    hne (hwJ₁.eq (isUniqueInvolution_of_mem_twinSet hz hm))
  have hJ₁set := A7Q.Gen.mem_omegaOfSet_of_mem_kPerp hΩ hKΩ hJ₁perp hJ₁tw
  obtain ⟨-, R, R', T₀, hR, hR', hT₀, -, -, -, hRR', hRT, hR'T⟩ :=
    A7Q.Gen.exists_twinSylow hΩ hKΩ hz hK' hK'ne hJ₁set
  have h8R : 8 ≤ Nat.card R := Sec6Gen.eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hKΩ hR)
  have h8R' : 8 ≤ Nat.card R' :=
    Sec6Gen.eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hK'Ω hR')
  have h8T₀ : 8 ≤ Nat.card T₀ :=
    Sec6Gen.eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hJ₁ hT₀)
  have hzR : z ∈ R := mem_of_isUniqueInvolution_of_isPGroup hz hR.1 hR.2.1 (by omega)
  have hwT₀ : w ∈ T₀ := mem_of_isUniqueInvolution_of_isPGroup hwJ₁ hT₀.1 hT₀.2.1 (by omega)
  have hcomm : ∀ x : T, x * z = z * x → x * w = w * x → x ∈
      Subgroup.centralizer ({z * w} : Set T) := by
    intro x hxz hxw
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * (z * w) = (x * z) * w := by group
      _ = (z * x) * w := by rw [hxz]
      _ = z * (x * w) := by group
      _ = z * (w * x) := by rw [hxw]
      _ = z * w * x := by group
  have hRc : R ≤ Subgroup.centralizer ({z * w} : Set T) := fun x hx =>
    hcomm x (hz.commute_of_mem (hR.1 hx)).symm (hRT x hx w hwT₀)
  have hR'c : R' ≤ Subgroup.centralizer ({z * w} : Set T) := fun x hx =>
    hcomm x (hzK'.commute_of_mem (hR'.1 hx)).symm (hR'T x hx w hwT₀)
  have hT₀z : T₀ ≤ Subgroup.centralizer ({z} : Set T) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hRT z hzR x hx).symm
  have hT₀c : T₀ ≤ Subgroup.centralizer ({z * w} : Set T) := fun x hx =>
    hcomm x (Subgroup.mem_centralizer_singleton_iff.mp (hT₀z hx))
      (hwJ₁.commute_of_mem (hT₀.1 hx)).symm
  have hT₀K : T₀ ≤ Subgroup.normalizer (K : Set T) :=
    Sec6Gen.le_normalizer_of_le_centralizer hΩ hKΩ hJ₁ hJ₁K.symm hz hT₀.1 hT₀.2.1 (by omega) hT₀z
  have hT₀K' : T₀ ≤ Subgroup.normalizer (K' : Set T) :=
    Sec6Gen.le_normalizer_of_le_centralizer hΩ hK'Ω hJ₁ hJ₁K'.symm hzK' hT₀.1 hT₀.2.1 (by omega)
      hT₀z
  have hKtq : K ∈ tqMembers3 (CoreAssembly.conjClass K) (z * w) :=
    ⟨hKΩ, TwinADescent3.mem_tq_of_sylCent hΩ h2 hKΩ ⟨R, hR, hRc⟩⟩
  have hK'tq : K' ∈ tqMembers3 (CoreAssembly.conjClass K) (z * w) :=
    ⟨hK'Ω, TwinADescent3.mem_tq_of_sylCent hΩ h2 hK'Ω ⟨R', hR', hR'c⟩⟩
  have hJ₁tq : J₁ ∈ tqMembers3 (CoreAssembly.conjClass K) (z * w) :=
    ⟨hJ₁, TwinADescent3.mem_tq_of_sylCent hΩ h2 hJ₁ ⟨T₀, hT₀, hT₀c⟩⟩
  exact ⟨R, hR, hRc, TwinDisc.twinTriple_secFam hΩ ha2 hKtq hK'tq hJ₁tq hz hK' hR hR' hT₀ hRc
    hR'c hT₀c hRR' hRT hR'T hT₀K hT₀K'⟩

end L3E8Cfg

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
