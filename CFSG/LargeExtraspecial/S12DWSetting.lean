module

public import CFSG.LargeExtraspecial.S12DWCount
public import CFSG.Open.TimmesfeldLargeExtraspecialMilestoneDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LargeExtraspecial.S12Defs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.Open

universe u

theorem s12_timmesfeldIsometries_eq {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (q : QuadraticForm (ZMod 2) V) :
    timmesfeldIsometries q = TauCeti.QuadraticMap.orthogonalGroup q :=
  Subgroup.ext fun _ => TauCeti.QuadraticMap.mem_orthogonalGroup_iff.symm

theorem s12_timmesfeldOmega_eq {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (q : QuadraticForm (ZMod 2) V)
    (hq : (polarBilin q).Nondegenerate) : timmesfeldOmega q = omegaGroup q hq := by
  rw [timmesfeldOmega, ← Subgroup.closure_eq (omegaGroup q hq)]
  congr 1
  ext g
  simp only [Set.mem_ofPred_eq, SetLike.mem_coe, mem_omegaGroup, s12_timmesfeldIsometries_eq,
    commSpace, Module.End.one_eq_id]

theorem s12_polarBilin_nondegenerate {d : ℕ} {q : QuadraticForm (ZMod 2) (Fin d → ZMod 2)}
    (hq : timmesfeldNondegenerate q) : (polarBilin q).Nondegenerate :=
  ⟨fun x hx => hq x fun y => by rw [← polarBilin_apply_apply]; exact hx y,
    fun y hy => hq y fun x => by rw [polar_comm, ← polarBilin_apply_apply]; exact hy x⟩

namespace Setting

variable {G : Type u} [Group G] [Finite G] {S : Setting G}

theorem Xbar12_map_le_omegaGroup (g : G) :
    (S.Xbar12 g).map S.O.subtype ≤ omegaGroup S.q S.q_nondegenerate := by
  rw [Xbar12, MonoidHom.map_closure, closure_le]
  rintro _ ⟨τ, hτ, rfl⟩
  refine ⟨τ.2, ?_⟩
  change Even (finrank (ZMod 2) (commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)))
  rw [(isTypeA_of_mem_Ebar12 hτ).2.2.2.1]
  exact even_two

theorem mbar_equiv_omega_or_isometries {g : G} (hn : 2 ≤ S.width)
    {q : QuadraticForm (ZMod 2) (Fin (2 * S.width) → ZMod 2)} (hq : timmesfeldNondegenerate q)
    (φ : S.Xbar12 g ≃* timmesfeldOmega q) :
    Nonempty (S.Mbar ≃* timmesfeldOmega q) ∨ Nonempty (S.Mbar ≃* timmesfeldIsometries q) := by
  classical
  have hq' := s12_polarBilin_nondegenerate hq
  have hfinV : finrank (ZMod 2) (Fin (2 * S.width) → ZMod 2) = 2 * S.width :=
    Module.finrank_fin_fun _
  have hfinQ : finrank (ZMod 2) S.Qt = 2 * S.width := S.finrank_Qt_eq_two_mul_width
  have : Nontrivial S.Qt := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  have : Nontrivial (Fin (2 * S.width) → ZMod 2) :=
    Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  have hX := Xbar12_map_le_omegaGroup (S := S) g
  have hcardX : Nat.card ((S.Xbar12 g).map S.O.subtype) = Nat.card (omegaGroup q hq') := by
    rw [← Nat.card_congr ((S.Xbar12 g).equivMapOfInjective S.O.subtype
      S.O.subtype_injective).toEquiv, Nat.card_congr φ.toEquiv, s12_timmesfeldOmega_eq q hq']
  have hdvd : Nat.card (omegaGroup q hq') ∣ Nat.card (omegaGroup S.q S.q_nondegenerate) :=
    hcardX ▸ Subgroup.card_dvd_of_le hX
  have hN := S12DW.ncard_eq_of_card_omegaGroup_dvd S.q_nondegenerate hq' hn hfinQ hfinV hdvd
  have hcardVQ : Nat.card (Fin (2 * S.width) → ZMod 2) = Nat.card S.Qt := by
    rw [S12DW.natCard_eq_four_pow hfinV, S12DW.natCard_eq_four_pow hfinQ]
  obtain ⟨L, hL⟩ := CFSG.Fischer.Classification.exists_linearEquiv_of_ncard_eq q S.q
    (S12DW.polar_eq_zero_imp hq') (S12DW.polar_eq_zero_imp S.q_nondegenerate) hcardVQ hN.symm
  let e : q.IsometryEquiv S.q := ⟨L, hL⟩
  have hOO : Nat.card (TauCeti.QuadraticMap.orthogonalGroup q) =
      Nat.card (TauCeti.QuadraticMap.orthogonalGroup S.q) :=
    Nat.card_congr (TauCeti.QuadraticMap.orthogonalGroupCongr e).toEquiv
  have hΩΩ : Nat.card (omegaGroup q hq') = Nat.card (omegaGroup S.q S.q_nondegenerate) := by
    have h1 := S12DW.card_orthogonalGroup_eq hq'
    have h2 := S12DW.card_orthogonalGroup_eq S.q_nondegenerate
    omega
  have hXeq : (S.Xbar12 g).map S.O.subtype = omegaGroup S.q S.q_nondegenerate :=
    Subgroup.eq_of_le_of_card_ge hX (by rw [hcardX, hΩΩ])
  have hXM : (S.Xbar12 g).map S.O.subtype ≤ S.Mbar.map S.O.subtype :=
    Subgroup.map_mono Xbar12_le_Mbar
  have hMO : S.Mbar.map S.O.subtype ≤ S.O := map_subtype_le _
  have hidx := Subgroup.relIndex_mul_relIndex (omegaGroup S.q S.q_nondegenerate)
    (S.Mbar.map S.O.subtype) S.O (hXeq ▸ hXM) hMO
  rw [relIndex_omegaGroup] at hidx
  have h1 : (omegaGroup S.q S.q_nondegenerate).relIndex (S.Mbar.map S.O.subtype) ∣ 2 :=
    ⟨_, hidx.symm⟩
  rcases (Nat.dvd_prime Nat.prime_two).mp h1 with ha | ha
  ·
    left
    have hle : S.Mbar.map S.O.subtype ≤ (S.Xbar12 g).map S.O.subtype :=
      hXeq ▸ Subgroup.relIndex_eq_one.mp ha
    have hMX : S.Mbar ≤ S.Xbar12 g := (Subgroup.map_le_map_iff_of_injective
      S.O.subtype_injective).mp hle
    exact ⟨(MulEquiv.subgroupCongr (le_antisymm hMX Xbar12_le_Mbar)).trans φ⟩
  ·
    right
    rw [ha] at hidx
    have h2 : (S.Mbar.map S.O.subtype).relIndex S.O = 1 := by omega
    have hOM := Subgroup.relIndex_eq_one.mp h2
    have htop : S.Mbar = ⊤ := by
      rw [eq_top_iff]
      intro x _
      obtain ⟨y, hy, hyx⟩ := hOM x.2
      rwa [show y = x from Subtype.ext hyx] at hy
    exact ⟨((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv).trans
      (((TauCeti.QuadraticMap.orthogonalGroupCongr e).symm).trans
        (MulEquiv.subgroupCongr (s12_timmesfeldIsometries_eq q).symm))⟩

end Setting

end CFSG.LargeExtraspecial
