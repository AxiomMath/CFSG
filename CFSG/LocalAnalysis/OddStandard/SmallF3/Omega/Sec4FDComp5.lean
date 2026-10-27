module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FDVocab
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeLowCent
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Basic
public import CFSG.ClassicalInvolution.Balance.Basic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2BlockInr

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private lemma blockHom_snd_apply {s : OGroup Q} (hs : s * s = 1)
    (p : OGroup (Q.restrict (fixSp s)) × OGroup (Q.restrict (commSp s))) (x : commSp s) :
    (((p.2 : commSp s ≃ₗ[ZMod 3] commSp s) x : commSp s) : V) =
      ((blockHom hs p : OGroup Q) : V ≃ₗ[ZMod 3] V) (x : V) := by
  have h := blockHom_apply hs p (0 : fixSp s) x
  simpa using h.symm

private lemma snd_eq_piOrth_of_apply_eq_neg {s g : OGroup Q} (hs : s * s = 1)
    {p : OGroup (Q.restrict (fixSp s)) × OGroup (Q.restrict (commSp s))}
    (hp : blockHom hs p = g)
    (h : ∀ x : commSp s, (g : V ≃ₗ[ZMod 3] V) (x : V) = -(x : V)) :
    p.2 = piOrth (Q.restrict (commSp s)) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  apply Subtype.ext
  rw [blockHom_snd_apply hs p x, hp, h x, coe_piOrth_apply]
  simp

private lemma snd_eq_one_of_apply_eq_self {s g : OGroup Q} (hs : s * s = 1)
    {p : OGroup (Q.restrict (fixSp s)) × OGroup (Q.restrict (commSp s))}
    (hp : blockHom hs p = g)
    (h : ∀ x : commSp s, (g : V ≃ₗ[ZMod 3] V) (x : V) = (x : V)) :
    p.2 = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  apply Subtype.ext
  rw [blockHom_snd_apply hs p x, hp, h x]
  simp

private lemma blockInr_mul_comm_blockHom {s : OGroup Q} (hs : s * s = 1)
    (p : OGroup (Q.restrict (fixSp s)) × OGroup (Q.restrict (commSp s)))
    (hc : p.2 ∈ Subgroup.center (OGroup (Q.restrict (commSp s))))
    (b : OGroup (Q.restrict (commSp s))) :
    blockInr hs b * blockHom hs p = blockHom hs p * blockInr hs b := by
  rw [blockInr_apply, ← map_mul, ← map_mul]
  congr 1
  ext <;> simp [Subgroup.mem_center_iff.mp hc b]

theorem sec4FD_component_omega5 (hQ : Q.Nondegenerate) {t : OGroup Q} (htt : t * t = 1)
    {u s' : OGroup Q} (hu : u ∈ Sec4FDDt hQ t) (hs's' : s' * s' = 1) (hts' : t * s' = s' * t)
    (hneg : commSp s' ≤ commSp t) (h5 : Module.finrank (ZMod 3) (commSp s') = 5)
    (hus' : u * s' = s' * u)
    (hsign : (∀ x ∈ commSp s', (u : V ≃ₗ[ZMod 3] V) x = x) ∨
      (∀ x ∈ commSp s', (u : V ≃ₗ[ZMod 3] V) x = -x))
    (hcen : ∀ g : OGroup Q, g * t = t * g → g * u = u * g → g * s' = s' * g) :
    ∃ K : Subgroup (OGroup Q),
      IsComponentIn K (Sec4FDDt hQ t ⊓ Subgroup.centralizer ({u} : Set (OGroup Q))) ∧
        oddCore ↥K = ⊥ ∧ LieModel ↥K .PSp 2 3 1 := by
  haveI : NeZero (2 : ZMod 3) := ⟨(isUnit_of_invertible (2 : ZMod 3)).ne_zero⟩
  haveI : Finite (OGroup Q) := CFSG.ClassicalInvolution.finite_orthogonalGroup_of_finite
  have hW : (Q.restrict (commSp s')).Nondegenerate := nondegenerate_restrict_commSp hQ hs's'
  let ΩW : Subgroup (OGroup (Q.restrict (commSp s'))) := omegaGroup hW
  let K : Subgroup (OGroup Q) := ΩW.map (blockInr hs's')
  have hU : 2 ≤ Module.finrank (ZMod 3) (commSp s') := by omega
  have ht_mem : t ∈ (blockHom hs's').range := by
    rw [range_blockHom hQ hs's']
    exact Subgroup.mem_centralizer_singleton_iff.mpr hts'
  obtain ⟨pt, hpt⟩ := ht_mem
  have hu_mem : u ∈ (blockHom hs's').range := by
    rw [range_blockHom hQ hs's']
    exact Subgroup.mem_centralizer_singleton_iff.mpr hus'
  obtain ⟨pu, hpu⟩ := hu_mem
  have hpt2 : pt.2 = piOrth (Q.restrict (commSp s')) :=
    snd_eq_piOrth_of_apply_eq_neg hs's' hpt
      (fun x => (mem_commSp_iff htt).mp (hneg x.2))
  have hcomm_t (b : OGroup (Q.restrict (commSp s'))) :
      blockInr hs's' b * t = t * blockInr hs's' b := by
    rw [← hpt]
    exact blockInr_mul_comm_blockHom hs's' pt (by rw [hpt2]; exact piOrth_mem_center) b
  have hcomm_u (b : OGroup (Q.restrict (commSp s'))) :
      blockInr hs's' b * u = u * blockInr hs's' b := by
    rcases hsign with hplus | hminus
    · have hpu2 : pu.2 = 1 :=
        snd_eq_one_of_apply_eq_self hs's' hpu (fun x => hplus x x.2)
      rw [← hpu]
      exact blockInr_mul_comm_blockHom hs's' pu
        (by rw [hpu2]; exact (Subgroup.center _).one_mem) b
    · have hpu2 : pu.2 = piOrth (Q.restrict (commSp s')) :=
        snd_eq_piOrth_of_apply_eq_neg hs's' hpu (fun x => hminus x x.2)
      rw [← hpu]
      exact blockInr_mul_comm_blockHom hs's' pu
        (by rw [hpu2]; exact piOrth_mem_center) b
  have hKH : K ≤ Sec4FDDt hQ t ⊓ Subgroup.centralizer ({u} : Set (OGroup Q)) := by
    rintro k ⟨b, hb, rfl⟩
    exact ⟨(mem_sec4FDDt_iff hQ).mpr
        ⟨blockInr_mem_omegaGroup hQ hs's' hU hb, hcomm_t b⟩,
      Subgroup.mem_centralizer_singleton_iff.mpr (hcomm_u b)⟩
  have hn : (K.subgroupOf (Sec4FDDt hQ t ⊓
      Subgroup.centralizer ({u} : Set (OGroup Q)))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hKH]
    intro k g hk hg
    obtain ⟨b, hb, rfl⟩ := hk
    obtain ⟨hgD, hgu⟩ := Subgroup.mem_inf.mp hg
    have hgt : g * t = t * g := (mem_sec4FDDt_iff hQ).mp hgD |>.2
    have hgu' : g * u = u * g := Subgroup.mem_centralizer_singleton_iff.mp hgu
    have hgs' : g * s' = s' * g := hcen g hgt hgu'
    obtain ⟨c₂, hc₂⟩ := blockInr_conj hQ hs's'
      (Subgroup.mem_centralizer_singleton_iff.mpr hgs') b
    rw [hc₂]
    exact Subgroup.mem_map.mpr
      ⟨c₂ * b * c₂⁻¹, (omegaGroup_normal hW).conj_mem b hb c₂, rfl⟩
  let e : ΩW ≃* K := ΩW.equivMapOfInjective (blockInr hs's') (blockInr_injective hs's')
  have hqK : IsQuasisimple K :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e (isQuasisimple_omegaGroup_five hW h5)
  have hcomp : IsComponentIn K (Sec4FDDt hQ t ⊓
      Subgroup.centralizer ({u} : Set (OGroup Q))) :=
    isComponentIn_of_normal hKH hqK hn
  have hodd : oddCore ↥K = ⊥ := by
    have hle : oddCore ↥K ≤ Subgroup.center ↥K :=
      CFSG.ClassicalInvolution.Balance.oddCore_le_center_of_isQuasisimple
        ⟨hqK.1.commutator_eq_top, hqK.2.1⟩
    have hcard : Nat.card (Subgroup.center ↥K) = 1 := by
      rw [← Nat.card_congr (Subgroup.centerCongr e).toEquiv]
      exact natCard_center_omegaGroup_five hW h5
    have h1 : Nat.card (oddCore ↥K) = 1 := by
      have hd := Subgroup.card_dvd_of_le hle
      rw [Subgroup.eq_bot_of_card_eq (Subgroup.center ↥K) hcard, Subgroup.card_bot] at hd
      exact Nat.dvd_one.mp hd
    exact Subgroup.eq_bot_of_card_eq (oddCore ↥K) h1
  have hlie : LieModel ↥K .PSp 2 3 1 := by
    have hZ : Subgroup.center (omegaGroup hW) = ⊥ :=
      Subgroup.eq_bot_of_card_eq (Subgroup.center (omegaGroup hW))
        (natCard_center_omegaGroup_five hW h5)
    have hΩ : LieModel (omegaGroup hW) .PSp 2 3 1 :=
      (lieModel_quotient_center_omegaGroup_five hW h5).of_mulEquiv
        ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)
    exact LieModel.of_mulEquiv e hΩ
  exact ⟨K, hcomp, hodd, hlie⟩

end CFSG.OddStandard.SmallF3.Omega
