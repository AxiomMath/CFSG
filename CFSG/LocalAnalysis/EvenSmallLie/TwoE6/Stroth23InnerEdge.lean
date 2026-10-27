module

public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.Stroth23InnerTri
public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.Stroth23InnerE1H

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSmallLie.TwoE6.Stroth23Inner

open Subgroup CFSG.Monster CFSG.Monster.B CFSG.Monster.B.GSide CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Amalgam CFSG.Monster.B.TwoA.Sp8

theorem commute_conj {X : Type*} [Group X] (g : X) {a b : X} (h : Commute a b) :
    Commute (g * a * g⁻¹) (g * b * g⁻¹) := by
  show g * a * g⁻¹ * (g * b * g⁻¹) = g * b * g⁻¹ * (g * a * g⁻¹)
  calc g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
    _ = g * (b * a) * g⁻¹ := by rw [h.eq]
    _ = g * b * g⁻¹ * (g * a * g⁻¹) := by group

@[expose] noncomputable def PS : Subgroup Shat := HS ⊓ cEdgeFix

theorem mem_PS_iff {x : Shat} : x ∈ PS ↔ x ∈ HS ∧ x ∈ cEdgeFix := Iff.rfl

theorem mem_PS_of_mem_commutator (q : commutator P1) :
    ((edgeFixEquivP1.symm (q : P1) : cEdgeFix) : Shat) ∈ PS := by
  refine ⟨(coe_mem_HS_iff (cEdgeFixToH (edgeFixEquivP1.symm (q : P1)))).2
    ((mem_commutator_H_iff cEdgeFix_commutator_index _).2
      ((mem_commutator_cEdgeFix_iff _).2 ?_)), (edgeFixEquivP1.symm (q : P1)).2⟩
  rw [MulEquiv.apply_symm_apply]
  exact q.2

theorem mem_commutator_of_mem_PS {x : Shat} (hx : x ∈ PS) :
    edgeFixEquivP1 ⟨x, (mem_PS_iff.1 hx).2⟩ ∈ commutator P1 :=
  (mem_commutator_cEdgeFix_iff _).1 ((mem_commutator_H_iff cEdgeFix_commutator_index _).1
    ((coe_mem_HS_iff (cEdgeFixToH ⟨x, (mem_PS_iff.1 hx).2⟩)).1 (mem_PS_iff.1 hx).1))

@[expose] noncomputable def ePS : commutator P1 ≃* PS where
  toFun q := ⟨(edgeFixEquivP1.symm (q : P1) : Shat), mem_PS_of_mem_commutator q⟩
  invFun x := ⟨edgeFixEquivP1 ⟨x, (mem_PS_iff.1 x.2).2⟩, mem_commutator_of_mem_PS x.2⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext (Subtype.ext rfl)
  map_mul' _ _ := Subtype.ext (Subtype.ext rfl)

theorem coe_ePS (q : commutator P1) : (((ePS q : PS) : Shat) : Dfull) = ((q : P1) : Dfull) :=
  rfl

theorem PS_ext {x x' : PS} (h : ((x : Shat) : Dfull) = ((x' : Shat) : Dfull)) : x = x' :=
  Subtype.ext (Subtype.ext h)

theorem clabelS_cw0_mem_HS : clabelS cw0 ∈ HS := clabelS_mem_HS_of_adj cgraph_adj_cv0_cw0

@[expose] noncomputable def cS : PS := ⟨clabelS cv0, clabelS_cv0_mem_HS, clabelS_cv0_mem_cEdgeFix⟩

@[expose] noncomputable def wS : PS := ⟨clabelS cw0, clabelS_cw0_mem_HS, clabelS_cw0_mem_cEdgeFix⟩

theorem ePS_cPQ : ePS cPQ = cS := PS_ext coe_lamV0.symm

theorem ePS_xPQ : ePS xPQ = cS * wS :=
  PS_ext (congrArg (fun p : P1 => (p : Dfull)) edgeFixEquivP1_lamV0_mul_lamW0).symm

theorem conj_mem_PS {s : Shat} (hs : s ∈ cEdgeStab) {q : Shat} (hq : q ∈ PS) :
    s * q * s⁻¹ ∈ PS :=
  mem_PS_iff.2 ⟨(conj_mem_HS_iff hs (mem_PS_iff.1 hq).2).2 (mem_PS_iff.1 hq).1,
    Stroth23Inner.conj_mem_cEdgeFix hs (mem_PS_iff.1 hq).2⟩

section Edge

variable {G : Type*} [Group G] {Φ : Shat → G} {g : G}

theorem exists_tau (hΦ : PhiData Φ) (hv : g * Φ (clabelS cv0) * g⁻¹ = Φ (clabelS cw0))
    (hw : g * Φ (clabelS cw0) * g⁻¹ = Φ (clabelS cv0)) {q : Shat} (hq : q ∈ PS) :
    ∃ q' ∈ PS, Φ q' = g * Φ q * g⁻¹ := by
  obtain ⟨hqH, hqA⟩ := mem_PS_iff.1 hq
  have h1 : Commute (Φ q) (Φ (clabelS cw0)) :=
    (hΦ.commute_iff hqH clabelS_cw0_mem_HS).2 ((commute_clabelS_iff_mem cw0 q).2 hqA.2)
  have h2 : Commute (Φ q) (Φ (clabelS cv0)) :=
    (hΦ.commute_iff hqH clabelS_cv0_mem_HS).2 ((commute_clabelS_iff_mem cv0 q).2 hqA.1)
  obtain ⟨q', hq'H, hq'⟩ :=
    hΦ.cent _ ((congrArg (Commute (g * Φ q * g⁻¹)) hw).mp (commute_conj g h1))
  have h3 : Commute (g * Φ q * g⁻¹) (Φ (clabelS cw0)) :=
    (congrArg (Commute (g * Φ q * g⁻¹)) hv).mp (commute_conj g h2)
  have h4 : Commute (Φ q') (Φ (clabelS cw0)) :=
    (congrArg (fun t => Commute t (Φ (clabelS cw0))) hq').mpr h3
  exact ⟨q', mem_PS_iff.2 ⟨hq'H, HS_le hq'H, (commute_clabelS_iff_mem cw0 q').1
    ((hΦ.commute_iff hq'H clabelS_cw0_mem_HS).1 h4)⟩, hq'⟩

theorem tau_mul (hΦ : PhiData Φ) {τ : PS → Shat} (hτPS : ∀ q, τ q ∈ PS)
    (hτ : ∀ q, Φ (τ q) = g * Φ q * g⁻¹) (a b : PS) : τ (a * b) = τ a * τ b := by
  refine hΦ.inj _ (mem_PS_iff.1 (hτPS (a * b))).1 _
    (mul_mem (mem_PS_iff.1 (hτPS a)).1 (mem_PS_iff.1 (hτPS b)).1) ?_
  rw [hτ, hΦ.mul _ (mem_PS_iff.1 (hτPS a)).1 _ (mem_PS_iff.1 (hτPS b)).1, hτ, hτ,
    Subgroup.coe_mul, hΦ.mul _ (mem_PS_iff.1 a.2).1 _ (mem_PS_iff.1 b.2).1]
  group

theorem tau_injective (hΦ : PhiData Φ) {τ : PS → Shat} (hτ : ∀ q, Φ (τ q) = g * Φ q * g⁻¹)
    {a b : PS} (h : τ a = τ b) : a = b := by
  have h1 : g * Φ a * g⁻¹ = g * Φ b * g⁻¹ := by rw [← hτ, ← hτ, h]
  exact Subtype.ext (hΦ.inj _ (mem_PS_iff.1 a.2).1 _ (mem_PS_iff.1 b.2).1
    (mul_left_cancel (mul_right_cancel h1)))

theorem conj_swap_clabelS {s : Shat} (hs0 : cvMul cv0 s = cw0) (hs1 : cvMul cw0 s = cv0) :
    s⁻¹ * clabelS cw0 * s⁻¹⁻¹ = clabelS cv0 ∧ s⁻¹ * clabelS cv0 * s⁻¹⁻¹ = clabelS cw0 := by
  rw [inv_inv, ← GSide.clabelS_cvMul, ← GSide.clabelS_cvMul, hs0, hs1]
  exact ⟨rfl, rfl⟩

theorem PhiData.exists_localData (hΦ : PhiData Φ)
    (hv : g * Φ (clabelS cv0) * g⁻¹ = Φ (clabelS cw0))
    (hw : g * Φ (clabelS cw0) * g⁻¹ = Φ (clabelS cv0)) : ∃ y, LocalData Φ g y := by
  choose τ hτPS hτ using fun q : PS => exists_tau hΦ hv hw q.2
  obtain ⟨s, hs0, hs1⟩ := exists_edge_swap
  have hsE : s⁻¹ ∈ cEdgeStab := inv_mem (swap_mem_cEdgeStab hs0 hs1)
  let αf : PS → PS := fun q => ⟨s⁻¹ * τ q * s⁻¹⁻¹, conj_mem_PS hsE (hτPS q)⟩
  have hαmul : ∀ a b, αf (a * b) = αf a * αf b := fun a b => Subtype.ext (by
    show s⁻¹ * τ (a * b) * s⁻¹⁻¹ = s⁻¹ * τ a * s⁻¹⁻¹ * (s⁻¹ * τ b * s⁻¹⁻¹)
    rw [tau_mul hΦ hτPS hτ]
    group)
  let αh : PS →* PS := MonoidHom.mk' αf hαmul
  have hαinj : Function.Injective αh := fun a b h => by
    have h1 : s⁻¹ * τ a * s⁻¹⁻¹ = s⁻¹ * τ b * s⁻¹⁻¹ := congrArg Subtype.val h
    exact tau_injective hΦ hτ (mul_left_cancel (mul_right_cancel h1))
  let f₁ : commutator P1 →* commutator P1 :=
    ePS.symm.toMonoidHom.comp (αh.comp ePS.toMonoidHom)
  have hf₁inj : Function.Injective f₁ := fun a b h =>
    ePS.injective (hαinj (ePS.symm.injective h))
  let α₁ : MulAut (commutator P1) :=
    MulEquiv.ofBijective f₁ ⟨hf₁inj, Finite.injective_iff_surjective.1 hf₁inj⟩
  have hα₁ : ∀ q, ePS (α₁ q) = αh (ePS q) := fun q => by
    show ePS (ePS.symm (αh (ePS q))) = αh (ePS q)
    exact MulEquiv.apply_symm_apply _ _
  have hτc : τ cS = clabelS cw0 :=
    hΦ.inj _ (mem_PS_iff.1 (hτPS cS)).1 _ clabelS_cw0_mem_HS ((hτ cS).trans hv)
  have hτw : τ wS = clabelS cv0 :=
    hΦ.inj _ (mem_PS_iff.1 (hτPS wS)).1 _ clabelS_cv0_mem_HS ((hτ wS).trans hw)
  have hαc : αh cS = cS := Subtype.ext (by
    show s⁻¹ * τ cS * s⁻¹⁻¹ = clabelS cv0
    rw [hτc]
    exact (conj_swap_clabelS hs0 hs1).1)
  have hαw : αh wS = wS := Subtype.ext (by
    show s⁻¹ * τ wS * s⁻¹⁻¹ = clabelS cw0
    rw [hτw]
    exact (conj_swap_clabelS hs0 hs1).2)
  have hc₁ : α₁ cPQ = cPQ := ePS.injective
    ((hα₁ cPQ).trans ((congrArg αh ePS_cPQ).trans (hαc.trans ePS_cPQ.symm)))
  have hx₁ : α₁ xPQ = xPQ := ePS.injective
    ((hα₁ xPQ).trans ((congrArg αh ePS_xPQ).trans ((map_mul αh cS wS).trans
      ((congrArg₂ (· * ·) hαc hαw).trans ePS_xPQ.symm))))
  obtain ⟨p, hp⟩ := exists_conj_of_mulAut α₁ hx₁ hc₁
  obtain ⟨p', hp'⟩ : ∃ p' : cEdgeFix, p' = edgeFixEquivP1.symm p := ⟨_, rfl⟩
  have key : ∀ q : PS, (αh q : Shat) = (p' : Shat) * q * (p' : Shat)⁻¹ := fun q => by
    apply Subtype.ext
    have e1 : ((αh q : Shat) : Dfull) = (((α₁ (ePS.symm q) : commutator P1) : P1) : Dfull) := by
      rw [← coe_ePS, hα₁, MulEquiv.apply_symm_apply]
    rw [e1, hp, hp']
    rfl
  refine ⟨s * p', { toPhiData := hΦ, swap0 := ?_, swap1 := ?_, conj := ?_ }⟩
  · rw [cvMul_mul, hs0]
    exact mem_vStab.1 p'.2.2
  · rw [cvMul_mul, hs1]
    exact mem_vStab.1 p'.2.1
  · intro q hqH hqA
    have hqS : q ∈ PS := mem_PS_iff.2 ⟨hqH, hqA⟩
    have h3 : s⁻¹ * τ ⟨q, hqS⟩ * s⁻¹⁻¹ = p' * q * (p' : Shat)⁻¹ := key ⟨q, hqS⟩
    have h2 : τ ⟨q, hqS⟩ = s * p' * q * (s * p')⁻¹ := by
      calc τ ⟨q, hqS⟩ = s * (s⁻¹ * τ ⟨q, hqS⟩ * s⁻¹⁻¹) * s⁻¹ := by group
        _ = s * (p' * q * (p' : Shat)⁻¹) * s⁻¹ := by rw [h3]
        _ = s * p' * q * (s * p')⁻¹ := by group
    rw [← h2]
    exact (hτ ⟨q, hqS⟩).symm

end Edge

end CFSG.EvenSmallLie.TwoE6.Stroth23Inner
