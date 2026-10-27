module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3B0AutBound
public import Certificates.Certificate1379103

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81.SuzB0

open Subgroup CFSG.Open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.PSL3Four.Native
  CFSG.ComponentClassification.PSL3Four CFSG.Sporadic.SuzOddCore

@[expose] noncomputable def tauPerm : Equiv.Perm (Fin 1782) := suzWord tauWord

theorem tau_parts :
    lettersOK 3 tauWord = true ∧ permOK 1782 (tauArr ()) = true ∧
      commutesA (tauArr ()) tTab = true ∧
      (∀ i < 6, eqA 1782 (compA 1782 (compA 1782 (tauArr ()) (qArr i)) (invCand 1782 (tauArr ())))
        (compA 1782 qProds[(tauAct i).1]! (tPow (tauAct i).2)) = true) ∧
      notInOK matEnum.tabs (tauMatTab ()) = true := by
  have h := Certificates.certificate1379103
  simp only [tauCheck, Bool.and_eq_true, allBelow_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem tauAct_lt : ∀ i < 6, (tauAct i).1 < 64 ∧ (tauAct i).2 < 2 := by
  decide

theorem colFold_tauAct_lt : ∀ v < 64, colFold (fun i => (tauAct i).1) v < 64 := by
  decide

theorem rep_tauArr :
    Rep 1782 (tauArr ()) tauPerm :=
  rep_suzWord tau_parts.1

theorem tauPerm_comm :
    tauPerm * suzInv 1 = suzInv 1 * tauPerm :=
  (commutesA_iff rep_tauArr rep_tTab).mp tau_parts.2.2.1

theorem tauPerm_conj
    {i : ℕ} (hi : i < 6) :
    tauPerm * qVec (2 ^ i) * tauPerm⁻¹ = qVec (tauAct i).1 * suzInv 1 ^ (tauAct i).2 := by
  rw [qVec_two_pow hi]
  exact eq_of_eqA (rep_compA (rep_compA rep_tauArr (rep_qArr hi))
      (rep_invCand rep_tauArr tau_parts.2.1))
    (rep_compA (rep_qProds (tauAct_lt i hi).1) (rep_tPow (tauAct_lt i hi).2))
    (tau_parts.2.2.2.1 i hi)

theorem tau_facts :
    tauPerm ∈ suzT ∧ tauPerm * suzInv 1 = suzInv 1 * tauPerm ∧
      ∀ i < 6, tauPerm * qVec (2 ^ i) * tauPerm⁻¹ = qVec (tauAct i).1 * suzInv 1 ^ (tauAct i).2 :=
  ⟨suzWord_mem_suzT _, tauPerm_comm, fun _ hi => tauPerm_conj hi⟩

theorem tauMatTab_get {v : ℕ} (hv : v < 64) :
    (tauMatTab ())[v]! = colFold (fun i => (tauAct i).1) v := by
  unfold tauMatTab
  exact getElem!_ofFn' _ hv

theorem tauMatTab_size : (tauMatTab ()).size = 64 := by
  unfold tauMatTab
  exact Array.size_ofFn

theorem tau_not_inner
    (c : ↥(invE 1))
    (hc : ∀ i < 6, (c : Equiv.Perm (Fin 1782)) * qVec (2 ^ i) * (c : Equiv.Perm (Fin 1782))⁻¹ =
      tauPerm * qVec (2 ^ i) * tauPerm⁻¹) : False := by
  have hrep : TabRep (tauMatTab ()) (kappa (rho1 c)) := by
    refine ⟨tauMatTab_size, fun x => ?_⟩
    rw [tauMatTab_get x.2, kappa_apply]
    change _ = ((bitEquiv.symm (coord_qVec.rho invE_le c (bitVec x)) : Fin 64) : ℕ)
    rw [coord_qVec.rho_bitVec invE_le c (w := fun i => (tauAct i).1) (b := fun i => (tauAct i).2)
      (fun i hi => (tauAct_lt i hi).1) (fun i hi => (tauAct_lt i hi).2)
      (fun i hi => (hc i hi).trans (tauPerm_conj hi)) x.2,
      bitEquiv_symm_bitVec (colFold_tauAct_lt x x.2)]
  exact not_mem_of_notInOK kappa_rho1_enumerates tau_parts.2.2.2.2 hrep ⟨rho1 c, ⟨c, rfl⟩, rfl⟩

theorem conj_mem_invE_one
    {g x : Equiv.Perm (Fin 1782)} (hg : g ∈ centT (suzInv 1)) (hx : x ∈ invE 1) :
    g * x * g⁻¹ ∈ invE 1 := by
  rw [invE_eq_centM (by norm_num)] at hx ⊢
  have hgt : Commute g (suzInv 1) := mem_centralizer_singleton_iff.mp hg.1
  have hxt : Commute x (suzInv 1) := mem_centralizer_singleton_iff.mp hx.1
  exact ⟨mem_centralizer_singleton_iff.mpr ((hgt.mul_left hxt).mul_left hgt.inv_left).eq,
    suzT_conj_mem_suzM hg.2 hx.2⟩

theorem invE_one_le_centT :
    invE 1 ≤ centT (suzInv 1) := fun _ hc =>
  ⟨(invE_le_centM (by norm_num) hc).1, mem_suzT_of_mem_suzM (invE_le_centM (by norm_num) hc).2⟩

@[expose] noncomputable def conjE :
    ↥(centT (suzInv 1)) →* MulAut ↥(invE 1) where
  toFun g :=
    { toFun := fun x => ⟨(g : Equiv.Perm (Fin 1782)) * x * (g : Equiv.Perm (Fin 1782))⁻¹,
        conj_mem_invE_one g.2 x.2⟩
      invFun := fun x => ⟨(g : Equiv.Perm (Fin 1782))⁻¹ * x * (g : Equiv.Perm (Fin 1782)), by
        simpa only [inv_inv] using conj_mem_invE_one (inv_mem g.2) x.2⟩
      left_inv := fun x => Subtype.ext (by
        show (g : Equiv.Perm (Fin 1782))⁻¹ * ((g : Equiv.Perm (Fin 1782)) * x *
          (g : Equiv.Perm (Fin 1782))⁻¹) * (g : Equiv.Perm (Fin 1782)) = x
        group)
      right_inv := fun x => Subtype.ext (by
        show (g : Equiv.Perm (Fin 1782)) * ((g : Equiv.Perm (Fin 1782))⁻¹ * x *
          (g : Equiv.Perm (Fin 1782))) * (g : Equiv.Perm (Fin 1782))⁻¹ = x
        group)
      map_mul' := fun x y => Subtype.ext (by
        show (g : Equiv.Perm (Fin 1782)) * ((x : Equiv.Perm (Fin 1782)) * y) *
            (g : Equiv.Perm (Fin 1782))⁻¹ =
          ((g : Equiv.Perm (Fin 1782)) * x * (g : Equiv.Perm (Fin 1782))⁻¹) *
            ((g : Equiv.Perm (Fin 1782)) * y * (g : Equiv.Perm (Fin 1782))⁻¹)
        group) }
  map_one' := MulEquiv.ext fun x => Subtype.ext (by
    show (1 : Equiv.Perm (Fin 1782)) * x * (1 : Equiv.Perm (Fin 1782))⁻¹ = x
    group)
  map_mul' g h := MulEquiv.ext fun x => Subtype.ext (by
    show ((g : Equiv.Perm (Fin 1782)) * h) * x * ((g : Equiv.Perm (Fin 1782)) * h)⁻¹ =
      (g : Equiv.Perm (Fin 1782)) * ((h : Equiv.Perm (Fin 1782)) * x *
        (h : Equiv.Perm (Fin 1782))⁻¹) * (g : Equiv.Perm (Fin 1782))⁻¹
    group)

theorem range_conjE :
    conjE.range = ⊤ := by
  set I := (MulAut.conj : ↥(invE 1) →* MulAut ↥(invE 1)).range with hI
  have hIle : I ≤ conjE.range := by
    rintro _ ⟨c, rfl⟩
    exact ⟨⟨c, invE_one_le_centT c.2⟩, MulEquiv.ext fun x => Subtype.ext rfl⟩
  have hτT : tauPerm ∈ centT (suzInv 1) :=
    ⟨mem_centralizer_singleton_iff.mpr tau_facts.2.1, tau_facts.1⟩
  have hτ : conjE ⟨tauPerm, hτT⟩ ∉ I := by
    rintro ⟨c, hc⟩
    refine tau_not_inner c fun i _ => ?_
    have h := congrArg (fun φ : MulAut ↥(invE 1) =>
      ((φ ⟨qVec (2 ^ i), qVec_mem_invE _⟩ : ↥(invE 1)) : Equiv.Perm (Fin 1782))) hc
    exact h
  have : Finite (MulAut ↥(invE 1)) :=
    Finite.of_injective (fun φ : MulAut ↥(invE 1) => (φ : ↥(invE 1) ≃ ↥(invE 1)))
      fun φ ψ h => MulEquiv.ext fun x => congrFun (congrArg DFunLike.coe h) x
  have hne : I.subgroupOf conjE.range ≠ ⊤ := by
    intro h
    apply hτ
    have hm : (⟨conjE ⟨tauPerm, hτT⟩, ⟨_, rfl⟩⟩ : ↥conjE.range) ∈
        I.subgroupOf conjE.range := by
      rw [h]
      exact mem_top _
    exact mem_subgroupOf.mp hm
  have hidx : 2 ≤ (I.subgroupOf conjE.range).index := by
    have h0 : (I.subgroupOf conjE.range).index ≠ 0 := index_ne_zero_of_finite
    have h1 : (I.subgroupOf conjE.range).index ≠ 1 := fun h => hne (index_eq_one.mp h)
    omega
  have hcard := (I.subgroupOf conjE.range).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hIle).toEquiv, card_range_conj_invE_one] at hcard
  have hAut := card_mulAut_invE_one_le
  exact eq_top_of_le_card _ (by omega)

theorem exists_suzT_of_mulAut_invE_one
    (α : MulAut ↥(invE 1)) :
    ∃ g ∈ suzT, g * suzInv 1 = suzInv 1 * g ∧
      ∀ x : ↥(invE 1), ((α x : ↥(invE 1)) : Equiv.Perm (Fin 1782)) = g * x * g⁻¹ := by
  obtain ⟨g, hg⟩ : α ∈ conjE.range := range_conjE ▸ mem_top α
  refine ⟨g, g.2.2, mem_centralizer_singleton_iff.mp g.2.1, fun x => ?_⟩
  rw [← hg]
  rfl

end CFSG.ComponentClassification.AS81.SuzB0
