module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IBNormProj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IBComb
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IOrd
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic
public import Certificates.Data.ExceptionalSL3

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

structure Sec4IGood (fr : Sec4IFrame Sec4IQ) (R : Subgroup (ProjOrth Sec4IQ)) : Prop where
  sylow : IsSylow2Of R Sec4IOmega
  le : sec4IB0 fr ≤ R
  card_le : ∀ F : Subgroup (ProjOrth Sec4IQ), F ≤ R → CFSG.Open.IsElemAbelian 2 F →
    Nat.card F ≤ 2 ^ 6
  eq_B0 : ∀ F : Subgroup (ProjOrth Sec4IQ), F ≤ R → CFSG.Open.IsElemAbelian 2 F →
    Nat.card F = 2 ^ 6 → F = sec4IB0 fr

private theorem sec4I_elemAbelian_bound (fr : Sec4IFrame Sec4IQ)
    {N : Subgroup (ProjOrth Sec4IQ)} (θ : ↥N →* Equiv.Perm (Fin 7))
    (hθrepr : ∀ x : ↥N, ∃ u : Fin 7 → ZMod 2,
      (x : ProjOrth Sec4IQ) = toProj Sec4IQ (sec4IMono fr (θ x) u))
    (hθsign : ∀ x : ↥N, Equiv.Perm.sign (θ x) = 1)
    (hθker : ∀ x : ↥N, θ x = 1 ↔ (x : ProjOrth Sec4IQ) ∈ sec4IB0 fr)
    {F : Subgroup (ProjOrth Sec4IQ)} (hFN : F ≤ N) (hF : CFSG.Open.IsElemAbelian 2 F) :
    Nat.card F ≤ 2 ^ 6 ∧ (Nat.card F = 2 ^ 6 → F = sec4IB0 fr) := by
  classical
  let Fn : Subgroup ↥N := F.subgroupOf N
  let φ : ↥Fn →* Equiv.Perm (Fin 7) := θ.comp Fn.subtype
  let Fbar : Subgroup (Equiv.Perm (Fin 7)) := Fn.map θ
  have hrange : φ.range = Fbar := by
    change (θ.comp Fn.subtype).range = Fn.map θ
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hcardFn : Nat.card ↥Fn = Nat.card F :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFN).toEquiv
  have hcardprod : Nat.card F = Nat.card Fbar * Nat.card ↥φ.ker := by
    have h := Subgroup.card_ker_mul_card_range φ
    rw [hrange] at h
    rw [← hcardFn, ← h, mul_comm]
  have hFbar_alt : Fbar ≤ alternatingGroup (Fin 7) := by
    intro f hf
    obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.mp hf
    exact Equiv.Perm.mem_alternatingGroup.mpr (hθsign x)
  have hFbar_sq : ∀ f ∈ Fbar, f * f = 1 := by
    intro f hf
    obtain ⟨y, hyFn, rfl⟩ := Subgroup.mem_map.mp hf
    have hy2 : y * y = 1 := by
      apply Subtype.ext
      show (y : ProjOrth Sec4IQ) * (y : ProjOrth Sec4IQ) = 1
      rw [← pow_two]
      exact hF.2 (y : ProjOrth Sec4IQ) hyFn
    rw [← map_mul, hy2, map_one]
  by_cases hbar : Fbar = ⊥
  · have hFB0 : F ≤ sec4IB0 fr := by
      intro y hy
      have hyN : y ∈ N := hFN hy
      have hxker : θ (⟨y, hyN⟩ : ↥N) = 1 := by
        have hmem : θ (⟨y, hyN⟩ : ↥N) ∈ Fbar :=
          Subgroup.mem_map.mpr ⟨⟨y, hyN⟩, hy, rfl⟩
        rw [hbar] at hmem
        simpa using hmem
      exact (hθker ⟨y, hyN⟩).mp hxker
    refine ⟨?_, ?_⟩
    · calc Nat.card F ≤ Nat.card (sec4IB0 fr) :=
            Nat.card_le_card_of_injective (Subgroup.inclusion hFB0)
              (Subgroup.inclusion_injective hFB0)
        _ = 2 ^ 6 := sec4IB0_card fr
    · intro hcard
      exact Subgroup.eq_of_le_of_card_ge hFB0 (by rw [sec4IB0_card fr, hcard])
  · have hex : ∀ x : ↥φ.ker, ∃ v : Fin 7 → ZMod 2, IsEvenVec v ∧
        sec4IPsi fr v = (((x : ↥Fn) : ↥N) : ProjOrth Sec4IQ) := by
      intro x
      have hxk : θ (((x : ↥Fn) : ↥N)) = 1 := x.2
      exact (mem_sec4IB0_iff fr).mp ((hθker _).mp hxk)
    let S : Type := {v : Fin 7 → ZMod 2 // IsEvenVec v ∧ ∀ f ∈ Fbar, permVec f v = v}
    let toS : ↥φ.ker → S := fun x =>
      ⟨Classical.choose (hex x), (Classical.choose_spec (hex x)).1, by
        intro f hf
        obtain ⟨y, hyFn, hyf⟩ := Subgroup.mem_map.mp hf
        rw [← hyf]
        have hvspec := Classical.choose_spec (hex x)
        have hxmem : (((x : ↥Fn) : ↥N) : ProjOrth Sec4IQ) ∈ F := (x : ↥Fn).2
        have hcomm : (y : ProjOrth Sec4IQ) * (((x : ↥Fn) : ↥N) : ProjOrth Sec4IQ) =
            (((x : ↥Fn) : ↥N) : ProjOrth Sec4IQ) * (y : ProjOrth Sec4IQ) := by
          have hcomm := hF.1.is_comm.comm
            (⟨(y : ProjOrth Sec4IQ), hyFn⟩ : ↥F)
            (⟨(((x : ↥Fn) : ↥N) : ProjOrth Sec4IQ), hxmem⟩ : ↥F)
          have hcomm' := congrArg Subtype.val hcomm
          simp only [Subgroup.coe_mul] at hcomm'
          exact hcomm'
        have hcomm' : (y : ProjOrth Sec4IQ) * sec4IPsi fr (Classical.choose (hex x)) =
            sec4IPsi fr (Classical.choose (hex x)) * (y : ProjOrth Sec4IQ) := by
          rw [hvspec.2]; exact hcomm
        have hconj : (y : ProjOrth Sec4IQ) * sec4IPsi fr (Classical.choose (hex x)) *
            (y : ProjOrth Sec4IQ)⁻¹ = sec4IPsi fr (Classical.choose (hex x)) := by
          rw [hcomm', mul_assoc, mul_inv_cancel, mul_one]
        obtain ⟨u, hu⟩ := hθrepr y
        have hconj2 := sec4IPsi_conj_mono fr (θ y) u (Classical.choose (hex x))
        rw [← hu] at hconj2
        have hpsi : sec4IPsi fr (permVec (θ y) (Classical.choose (hex x))) =
            sec4IPsi fr (Classical.choose (hex x)) := by
          rw [← hconj2, hconj]
        exact sec4IPsi_injOn fr (sec4I_isEvenVec_permVec (θ y) hvspec.1) hvspec.1 hpsi⟩
    have htoS_inj : Function.Injective toS := by
      intro x₁ x₂ h
      have hv : Classical.choose (hex x₁) = Classical.choose (hex x₂) :=
        congrArg Subtype.val h
      apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
      have h1 := (Classical.choose_spec (hex x₁)).2
      have h2 := (Classical.choose_spec (hex x₂)).2
      rw [← h1, ← h2, hv]
    have hfixle : Nat.card ↥φ.ker ≤ Nat.card S :=
      Nat.card_le_card_of_injective toS htoS_inj
    have hle32 : Nat.card Fbar * Nat.card ↥φ.ker ≤ 32 := by
      calc Nat.card Fbar * Nat.card ↥φ.ker ≤ Nat.card Fbar * Nat.card S :=
            Nat.mul_le_mul_left _ hfixle
        _ ≤ 32 := sec4I_card_mul_fixEven_le Fbar hFbar_alt hFbar_sq hbar
    refine ⟨?_, ?_⟩
    · rw [hcardprod]; exact le_trans hle32 (by norm_num)
    · intro hcard
      exfalso
      rw [hcardprod] at hcard
      omega

theorem sec4I_exists_good (fr : Sec4IFrame Sec4IQ) :
    ∃ R : Subgroup (ProjOrth Sec4IQ), Sec4IGood fr R := by
  classical
  obtain ⟨θ, hθrepr, hθsign, -, hθker⟩ :=
    sec4I_exists_perm_hom sec4IQ_nondegenerate fr
  have hB0N : sec4IB0 fr ≤ sec4IN sec4IQ_nondegenerate fr :=
    sec4IB0_le_sec4IN sec4IQ_nondegenerate fr
  have hB0pg : IsPGroup 2 ↥((sec4IB0 fr).subgroupOf (sec4IN sec4IQ_nondegenerate fr)) :=
    (IsPGroup.of_card (sec4IB0_card fr)).of_equiv
      (Subgroup.subgroupOfEquivOfLe hB0N).symm
  obtain ⟨T, hB0T⟩ := IsPGroup.exists_le_sylow hB0pg
  let R : Subgroup (ProjOrth Sec4IQ) :=
    (T : Subgroup ↥(sec4IN sec4IQ_nondegenerate fr)).map
      (sec4IN sec4IQ_nondegenerate fr).subtype
  have hRN : R ≤ sec4IN sec4IQ_nondegenerate fr := by
    exact Subgroup.map_subtype_le (T : Subgroup ↥(sec4IN sec4IQ_nondegenerate fr))
  have hRb0 : sec4IB0 fr ≤ R := by
    change sec4IB0 fr ≤
      (T : Subgroup ↥(sec4IN sec4IQ_nondegenerate fr)).map
        (sec4IN sec4IQ_nondegenerate fr).subtype
    rw [← Subgroup.map_subgroupOf_eq_of_le hB0N]
    exact Subgroup.map_mono (f := (sec4IN sec4IQ_nondegenerate fr).subtype) hB0T
  have hRpg : IsPGroup 2 R :=
    (T.isPGroup').of_equiv (Subgroup.equivMapOfInjective
      (T : Subgroup ↥(sec4IN sec4IQ_nondegenerate fr))
      (sec4IN sec4IQ_nondegenerate fr).subtype
      (sec4IN sec4IQ_nondegenerate fr).subtype_injective)
  have hfac : (2 ^ 6 * 2520 : ℕ).factorization 2 = 9 := by decide +kernel
  have hRcardT : Nat.card ↥(T : Subgroup ↥(sec4IN sec4IQ_nondegenerate fr)) = 2 ^ 9 := by
    rw [Sylow.card_eq_multiplicity T, natCard_sec4IN sec4IQ_nondegenerate fr, hfac]
  have hRcard : Nat.card R = 2 ^ 9 := by
    change Nat.card ↥((T : Subgroup ↥(sec4IN sec4IQ_nondegenerate fr)).map
      (sec4IN sec4IQ_nondegenerate fr).subtype) = 2 ^ 9
    rw [Subgroup.card_map_of_injective (sec4IN sec4IQ_nondegenerate fr).subtype_injective]
    exact hRcardT
  have hRomega : R ≤ Sec4IOmega := le_trans hRN inf_le_left
  have hRsyl : IsSylow2Of R Sec4IOmega := by
    refine ⟨hRomega, hRpg, ?_⟩
    intro h2
    have hmul := Subgroup.relIndex_mul_card R Sec4IOmega
    rw [inf_eq_left.2 hRomega] at hmul
    rw [hRcard, natCard_omegaProj_seven sec4IQ_nondegenerate sec4IQ_finrank] at hmul
    have hrel : R.relIndex Sec4IOmega = 8955765 := by omega
    rw [hrel] at h2
    norm_num at h2
  refine ⟨R, hRsyl, hRb0, ?_, ?_⟩
  · intro F hFR hF
    exact (sec4I_elemAbelian_bound fr θ hθrepr hθsign hθker (le_trans hFR hRN) hF).1
  · intro F hFR hF hcard
    exact (sec4I_elemAbelian_bound fr θ hθrepr hθsign hθker (le_trans hFR hRN) hF).2 hcard

end CFSG.OddStandard.SmallF3.Omega
