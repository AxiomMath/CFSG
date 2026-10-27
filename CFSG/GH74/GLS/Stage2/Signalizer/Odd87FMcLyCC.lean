module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FMcLy
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87F3CC
public import Certificates.Certificate5160

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.Blueprint CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier
  CFSG.ComponentClassification.RestrictedStd.Spor CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

theorem mcl_outer_cc
    {G : Type} [Group G]
    (e : G ≃* NativeSporadic.McL) (α : MulAut G) (hα2 : α * α = 1) (hα : α ∉ inner G) {x : G}
    (hxo : Odd (orderOf x)) (hxc : ∀ y : G, α y = y → y * x = x * y) : x = 1 := by
  set θ : G ≃* mclP := e.trans mclPermEquiv
  set β : MulAut mclP := transportAut θ α
  have hβ2 : β * β = 1 := transportAut_mul_self θ hα2
  have hβ : β ∉ inner mclP := transportAut_not_mem_inner θ hα
  obtain ⟨w, hwR, hw⟩ := mcl_autModel.surj β
  have hwP : w ∉ mclP := by
    intro hwP
    apply hβ
    refine ⟨⟨w, hwP⟩, MulEquiv.ext fun p => Subtype.ext ?_⟩
    rw [hw p]
    rfl
  have hw2 : w * w = 1 := by
    apply mcl_autModel.inj (w * w) (mclR.mul_mem hwR hwR)
    intro p hp
    have h := congrArg (fun φ : MulAut mclP => ((φ ⟨p, hp⟩ : mclP) : Equiv.Perm (Fin 275))) hβ2
    simp only [MulAut.mul_apply, MulAut.one_apply] at h
    rw [hw, hw] at h
    calc w * w * p = w * (w * p * w⁻¹) * w⁻¹ * (w * w) := by group
      _ = p * (w * w) := by rw [h]
  have hw1 : w ≠ 1 := fun h1 => hwP (h1 ▸ one_mem _)
  have hwo : orderOf w = 2 := orderOf_eq_prime (by rw [sq]; exact hw2) hw1
  obtain ⟨-, -, -, -, hcover, -, -, -⟩ := mcl_involution_centralizers
  obtain ⟨r, hr, g, hg, hwg⟩ := hcover w hwR hwo
  simp only [mclRows, List.mem_cons, List.not_mem_nil, or_false] at hr
  have hwu : w = g * mclU1 * g⁻¹ := by
    rcases hr with rfl | rfl
    · exfalso
      dsimp only at hwg
      apply hwP
      rw [hwg]
      exact mclP.mul_mem (mclP.mul_mem hg mclT0_facts.1) (mclP.inv_mem hg)
    · dsimp only at hwg
      exact hwg
  have hfix := map_fixSub_conjOn mclP β w hw
  rw [hwu, centralizerIn_conj mclP hg] at hfix
  set z : Equiv.Perm (Fin 275) := g⁻¹ * ((θ x : mclP) : Equiv.Perm (Fin 275)) * g with hz
  have hperm : ∀ k < 4, permOK 275 (mclCentTbl (k + 18)) = true := fun k hk =>
    mclY_basic.2.2.2.2.2 k hk
  have hgen : ∀ c ∈ [tp 275 (mclCentTbl 18), tp 275 (mclCentTbl 19), tp 275 (mclCentTbl 20),
      tp 275 (mclCentTbl 21)], z * c = c * z := by
    intro c hc
    have hcm : c ∈ centralizerIn mclP mclU1 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact mclC1Gen_mem (k := 0) (by norm_num)
      · exact mclC1Gen_mem (k := 1) (by norm_num)
      · exact mclC1Gen_mem (k := 2) (by norm_num)
      · exact mclC1Gen_mem (k := 3) (by norm_num)
    have hmem : g * c * g⁻¹ ∈ (CFSG.Sporadic.Schreier.fixSub β).map mclP.subtype := by
      rw [hfix]
      exact ⟨c, hcm, rfl⟩
    obtain ⟨p, hp, hpc⟩ := Subgroup.mem_map.1 hmem
    have hfp : α (θ.symm p) = θ.symm p := by
      apply θ.injective
      have h1 : β p = p := hp
      have h2 : θ (α (θ.symm p)) = p := h1
      rw [h2, MulEquiv.apply_symm_apply]
    have h3 := hxc (θ.symm p) hfp
    have h4 : p * θ x = θ x * p := by
      have := congrArg θ h3
      simpa using this
    have h5 : (g * c * g⁻¹) * ((θ x : mclP) : Equiv.Perm (Fin 275)) =
        ((θ x : mclP) : Equiv.Perm (Fin 275)) * (g * c * g⁻¹) := by
      have := congrArg Subtype.val h4
      simp only [Subgroup.coe_mul] at this
      simpa [← hpc] using this
    calc z * c = g⁻¹ * ((θ x : mclP) : Equiv.Perm (Fin 275)) * (g * c * g⁻¹) * g := by rw [hz]; group
      _ = g⁻¹ * ((g * c * g⁻¹) * ((θ x : mclP) : Equiv.Perm (Fin 275))) * g := by rw [h5]; group
      _ = c * z := by rw [hz]; group
  have hodd : Odd (orderOf z) := by
    have h1 : orderOf z = orderOf (θ x : mclP) := by
      have := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) ((θ x : mclP) : Equiv.Perm (Fin 275))
      simp only [MulAut.conj_apply, inv_inv] at this
      rw [hz, this, Subgroup.orderOf_coe]
    rw [h1, MulEquiv.orderOf_eq]
    exact hxo
  have hgT : List.Forall₂ (Rep 275) [mclCentTbl 18, mclCentTbl 19, mclCentTbl 20, mclCentTbl 21]
      [tp 275 (mclCentTbl 18), tp 275 (mclCentTbl 19), tp 275 (mclCentTbl 20),
        tp 275 (mclCentTbl 21)] :=
    .cons (rep_tp (hperm 0 (by norm_num))) (.cons (rep_tp (hperm 1 (by norm_num)))
      (.cons (rep_tp (hperm 2 (by norm_num))) (.cons (rep_tp (hperm 3 (by norm_num))) .nil)))
  have hz1 : z = 1 :=
    eq_one_of_ccOK (by norm_num) hgT Certificates.certificate5160 hgen hodd
  have : ((θ x : mclP) : Equiv.Perm (Fin 275)) = 1 := by
    have h1 : g * z * g⁻¹ = g * 1 * g⁻¹ := by rw [hz1]
    rw [hz] at h1
    simpa [mul_assoc] using h1
  have h2 : θ x = 1 := Subtype.ext this
  exact θ.injective (by rw [h2, map_one])

theorem mclOuterCC
    (Y : Type) [Group Y]
    (hY : NativeSporadic.IsSporadic Y .McL) : McLOuterCC Y := by
  obtain ⟨e⟩ := hY
  intro α hα2 hα x hxo hxc
  exact mcl_outer_cc e α hα2 hα hxo hxc

theorem cell87_FMcLy_cert :
    Cell87 FMcLy :=
  cell87_FMcLy fun Y _ hY => mclOuterCC Y hY

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
