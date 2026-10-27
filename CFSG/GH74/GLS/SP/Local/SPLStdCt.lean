module

public import CFSG.GH74.GLS.SP.Local.SPLStd
public import CFSG.GH74.GLS.SP.Local.SPLCtK2
public import CFSG.GH74.GLS.SP.Local.SPLCtA
public import CFSG.GH74.GLS.SP.Local.SPLCtFinal
public import CFSG.GH74.GLS.SP.Local.SPLCtK3
public import CFSG.GH74.GLS.SP.Local.SPLCtNC
public import CFSG.GH74.GLS.SP.Local.SPLCtQuot
public import CFSG.GH74.GLS.SP.Local.SPLCtXN

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.SP
open scoped Pointwise commutatorElement

@[expose] def SPLInPumpStd : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Stage12.Std G → ∀ D₁ : SPLNot1 G,
    SPLSetup D₁.toSPLNot0 → SPL2Set D₁ → SPLPumpAt D₁

@[expose] def SPLInCenIStd : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Stage12.Std G → ∀ D₁ : SPLNot1 G,
    SPLSetup D₁.toSPLNot0 → SPL2Set D₁ → SPLCenIAt D₁

theorem splInCenIStd_of_K1Std
    (hK1 : SPLInPumpStd) : SPLInCenIStd := by
  intro G _ _ hS D₁ hs hset
  have hP : SPLPumpAt D₁ := hK1 G hS D₁ hs hset
  have hK3' : ∀ u : G, SPLCtU D₁ u → SPLCenUAt D₁ u := fun u hu =>
    splInCenU G hS.kps D₁ hs hset u hu.mem_S₁ hu.ord (u_ne_z D₁ hs hu)
      (mem_centralizer_singleton_iff.mp (Ict_le_Ct D₁ hs hu.mem_I)).symm hu.norm
  obtain ⟨u, hud, hA⟩ := ctA_exists D₁ hs hP hK3'
  obtain ⟨T, T₀, T₁, y, hT⟩ := ctT_exists D₁ hs hA hud.U
  exact splCenIAt_of_GW D₁ hs hA hT

theorem splLeafCtStd_of_inputs (hK1 : SPLInPumpStd) (hK2 : SPLInCenIStd) :
    SPLLeafCtStd := by
  intro G _ _ hS D₁ hs hset
  have hP : SPLPumpAt D₁ := hK1 G hS D₁ hs hset
  have hC2 : SPLCenIAt D₁ := hK2 G hS D₁ hs hset
  have hK3' : ∀ u : G, SPLCtU D₁ u → SPLCenUAt D₁ u := fun u hu =>
    splInCenU G hS.kps D₁ hs hset u hu.mem_S₁ hu.ord (u_ne_z D₁ hs hu)
      (mem_centralizer_singleton_iff.mp (Ict_le_Ct D₁ hs hu.mem_I)).symm hu.norm
  obtain ⟨u, hud, hA⟩ := ctA_exists D₁ hs hP hK3'
  obtain ⟨T, T₀, T₁, y, hT⟩ := ctT_exists D₁ hs hA hud.U
  obtain ⟨x, hxY, hxo, hxt, hzx, hYgen, hxn, hT₀eq⟩ := exists_x hs hT
  have hn3 : 3 ≤ D₁.n := three_le_n D₁.toSPLNot0 hs.odd_q hs.q_ge
  have hYT : T₀ ⊔ zpowers y ≤ T := sup_le (T₀_le_T D₁ hT) (zpowers_le.mpr hT.y_mem)
  have hxCt : x ∈ D₁.Ct := hT.T_le (hYT hxY)
  have hxT : x ∈ T := hYT hxY
  have hx2T₀ : x ^ 2 ∈ T₀ := by rw [hT₀eq]; exact Subgroup.mem_sup_left (mem_zpowers _)
  have hxT₀ : x ∉ T₀ := by rw [hT₀eq]; exact hxn
  have hx2cenI : ∀ i ∈ D₁.Ict, x ^ 2 * i = i * x ^ 2 := fun i hi =>
    ((hT.T₀_mem (x ^ 2)).mp hx2T₀).2 i hi
  have hx2cenA : ∀ a ∈ D₁.Act, x ^ 2 * a = a * x ^ 2 := x_sq_cen_A hs hT hxT hzx
  obtain ⟨hcount, hFle⟩ := ct_count hs hA hC2 hud hT
  have hAx := ct_Ax hs hA hud hT hxY hxo hxt
  have hNC := ct_NC D₁ hs hA hFle
  obtain ⟨hN, hquot⟩ := ct_quot D₁ hs hA hT hxY hxT₀ hx2T₀
  obtain ⟨b, hb, hbnorm⟩ := ct_xnorm D₁ hs hset hA hxCt hx2cenI hN hquot
  have hCtJ := ct_J_eq hs hA hC2 hT hYgen hxt hT₀eq
  have hcenI := ct_cenI D₁ hA hC2 hT
  set x' : G := b * x * b⁻¹ with hx'
  have hbCt : b ∈ D₁.Ct := Ict_le_Ct D₁ hs hb
  have hb2 : b * x ^ 2 * b⁻¹ = x ^ 2 := by
    calc b * x ^ 2 * b⁻¹ = x ^ 2 * b * b⁻¹ := by rw [← hx2cenI b hb]
      _ = x ^ 2 := by group
  have hx'2 : x' ^ 2 = x ^ 2 := by rw [hx', conj_pow, hb2]
  have hzb : D₁.z * b = b * D₁.z := z_central_in_K D₁ hs (mem_zpowers D₁.z) b (Ict_le_K D₁ hs hb)
  have htb : D₁.t * b = b * D₁.t := (mem_centralizer_singleton_iff.mp hbCt).symm
  have hx'o : orderOf x' = 2 ^ (D₁.n - 1) := by
    have := MulEquiv.orderOf_eq (MulAut.conj b) x
    rw [MulAut.conj_apply] at this
    rw [hx', this]; exact hxo
  have hx't : x' ^ (2 ^ (D₁.n - 2)) = D₁.t := by
    rw [hx', conj_pow, hxt]
    calc b * D₁.t * b⁻¹ = D₁.t * b * b⁻¹ := by rw [← htb]
      _ = D₁.t := by group
  have hx'Ct : x' ∈ D₁.Ct :=
    D₁.Ct.mul_mem (D₁.Ct.mul_mem hbCt hxCt) (D₁.Ct.inv_mem hbCt)
  have hMeq : D₁.Ict ⊔ zpowers x' = D₁.Ict ⊔ zpowers x := by
    apply le_antisymm
    · refine sup_le le_sup_left (zpowers_le.mpr ?_)
      exact (D₁.Ict ⊔ zpowers x).mul_mem
        ((D₁.Ict ⊔ zpowers x).mul_mem (Subgroup.mem_sup_left hb)
          (Subgroup.mem_sup_right (mem_zpowers x)))
        ((D₁.Ict ⊔ zpowers x).inv_mem (Subgroup.mem_sup_left hb))
    · refine sup_le le_sup_left (zpowers_le.mpr ?_)
      have : x = b⁻¹ * x' * b := by rw [hx']; group
      rw [this]
      exact (D₁.Ict ⊔ zpowers x').mul_mem
        ((D₁.Ict ⊔ zpowers x').mul_mem ((D₁.Ict ⊔ zpowers x').inv_mem (Subgroup.mem_sup_left hb))
          (Subgroup.mem_sup_right (mem_zpowers x')))
        (Subgroup.mem_sup_left hb)
  have hZeq : zpowers (x' ^ 2) = zpowers (x ^ 2) := by rw [hx'2]
  refine ⟨mkD2 D₁ x', rfl, ?_⟩
  refine
    { I_eq := hA.I_eq
      I_der := rfl
      I_L2 := Ict_isL2 D₁ hs
      A_eq := rfl
      A_cyc := hA.A_cyc
      A_card := hcount
      A_inv := Act_inv D₁ hs
      AI_inf := Act_inf_Ict D₁ hs
      AI_comm := hA.AI_comm
      Ct_eq := ?_
      xz_dih := ?_
      x_ord := hx'o
      x_pow := hx't
      x_norm := hbnorm
      x2_cen := ?_
      quot := ?_
      F_eq := hFle
      A_x := ?_
      N_C := hNC
      cen_I := ?_ }
  ·
    show D₁.Ct = D₁.Ict ⊔ D₁.Act ⊔ D₁.F₀ ⊔ zpowers x' ⊔ zpowers D₁.z
    apply le_antisymm
    · rw [hCtJ]
      refine sup_le (sup_le (sup_le (sup_le ?_ ?_) ?_) ?_) ?_
      · exact fun h hh => Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_sup_left
          (Subgroup.mem_sup_left hh)))
      · exact fun h hh => Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_sup_left
          (Subgroup.mem_sup_right hh)))
      · exact fun h hh => Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_sup_right hh))
      · rw [zpowers_le]
        have : x = b⁻¹ * x' * b := by rw [hx']; group
        rw [this]
        exact (D₁.Ict ⊔ D₁.Act ⊔ D₁.F₀ ⊔ zpowers x' ⊔ zpowers D₁.z).mul_mem
          ((D₁.Ict ⊔ D₁.Act ⊔ D₁.F₀ ⊔ zpowers x' ⊔ zpowers D₁.z).mul_mem
            ((D₁.Ict ⊔ D₁.Act ⊔ D₁.F₀ ⊔ zpowers x' ⊔ zpowers D₁.z).inv_mem
              (Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_sup_left
                (Subgroup.mem_sup_left hb)))))
            (Subgroup.mem_sup_left (Subgroup.mem_sup_right (mem_zpowers x'))))
          (Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_sup_left
            (Subgroup.mem_sup_left hb))))
      · exact fun h hh => Subgroup.mem_sup_right hh
    · refine sup_le (sup_le (sup_le (sup_le (Ict_le_Ct D₁ hs) (Act_le_Ct D₁)) (fun f hf => hf.2)) ?_) ?_
      · rw [zpowers_le]; exact hx'Ct
      · rw [zpowers_le]; exact mem_centralizer_singleton_iff.mpr (z_comm_t' D₁ hs)
  ·
    show IVK.IsDihedralOrder ↥(zpowers x' ⊔ zpowers D₁.z) (2 ^ D₁.n)
    exact dihedral_conj_I hs hb (by rw [hYgen]; exact hT.T₀y_dih)
  ·
    show ∀ w ∈ D₁.Ict ⊔ D₁.Act, x' ^ 2 * w = w * x' ^ 2
    intro w hw
    rw [hx'2]
    obtain ⟨i, hi, a, ha, hwe⟩ :=
      mem_sup_of_commute (fun i hi a ha => (hA.AI_comm a ha i hi).symm) hw
    rw [hwe]
    calc x ^ 2 * (i * a) = (x ^ 2 * i) * a := by group
      _ = (i * x ^ 2) * a := by rw [hx2cenI i hi]
      _ = i * (x ^ 2 * a) := by group
      _ = i * (a * x ^ 2) := by rw [hx2cenA a ha]
      _ = (i * a) * x ^ 2 := by group
  ·
    have key : ∀ (M Z : Subgroup G), M = D₁.Ict ⊔ zpowers x → Z = zpowers (x ^ 2) →
        ∃ _ : (Z.subgroupOf M).Normal, IVK.IsPGL2 (↥M ⧸ Z.subgroupOf M) (fun r => r = D₁.q) := by
      intro M Z hM hZ
      subst hM
      subst hZ
      exact ⟨hN, hquot⟩
    exact key (D₁.Ict ⊔ zpowers x') (zpowers (x' ^ 2)) hMeq hZeq
  ·
    show ∀ a ∈ D₁.Act, a * x' = x' * a
    intro a ha
    have hab : a * b = b * a := hA.AI_comm a ha b hb
    have hab' : a * b⁻¹ = b⁻¹ * a := (show Commute a b from hab).inv_right.eq
    rw [hx']
    calc a * (b * x * b⁻¹) = (a * b) * x * b⁻¹ := by group
      _ = b * a * x * b⁻¹ := by rw [hab]
      _ = b * (a * x) * b⁻¹ := by group
      _ = b * (x * a) * b⁻¹ := by rw [hAx a ha]
      _ = b * x * (a * b⁻¹) := by group
      _ = b * x * (b⁻¹ * a) := by rw [hab']
      _ = (b * x * b⁻¹) * a := by group
  ·
    show centralizer (D₁.Ict : Set G) ⊓ D₁.Ct = D₁.Act ⊔ (zpowers (x' ^ 2) ⊔ zpowers D₁.z)
    rw [hx'2, ← hT₀eq, inf_comm]
    exact hcenI

theorem splLeafCtStd_of_K1Std
    (hK1 : SPLInPumpStd) : SPLLeafCtStd :=
  splLeafCtStd_of_inputs hK1 (splInCenIStd_of_K1Std hK1)

theorem spLocalLeafStd_of_K1Std
    (h11 : IVK.Proofs2.IVK_11_1b_nat) (hK1 : SPLInPumpStd) : SPLocalLeafStd :=
  spLocalLeafStd_of_L2_11 h11 (splLeafCtStd_of_K1Std hK1)

theorem sp_compat_Std_of_K1Std
    (hM : SPModelLeaf) (h11 : IVK.Proofs2.IVK_11_1b_nat) (hK1 : SPLInPumpStd) :
    S_stage5_SP_compat_Std :=
  sp_compat_Std_of_localGlueStd (spLocalGlueStd_of_model hM (spLocalLeafStd_of_K1Std h11 hK1))

end CFSG.GH74.GLS.SP.Local
