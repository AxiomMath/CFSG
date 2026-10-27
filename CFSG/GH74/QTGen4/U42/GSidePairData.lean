module

public import CFSG.GH74.QTGen4.U42.GSideB
public import CFSG.GH74.QTGen4.U42.U0CoreE

public section

namespace CFSG.GH74.QTGen4.U42

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.A5Model CFSG.Blueprint
open CFSG.Quasithin.H13 CFSG.Quasithin.H13.A5

variable {G : Type} [Group G] [Finite G] {T L V H I : Subgroup G}

theorem pairData_plain (S : A5.Setting G T L V) (hH : H ∈ S.Hz) (D : Data13515 S H I)
    (hP : _root_.CFSG.GH74.QTGen4.U42.Setting.PlainCase S) :
    ∃ e : ↥(L ⊔ T) ≃* Mof (alternatingGroup (Fin 5)), IsCoords S e ∧
      (∀ m : ↥(L ⊔ T), (m : G) ∈ pCoreOf 2 H ↔ ((e m : Mof _) : Mc) ∈ U0) ∧
      (∀ m : ↥(L ⊔ T), (m : G) ∈ H ↔ ((e m : Mof _) : Mc) ∈ Bc) ∧
      (∀ m : ↥(L ⊔ T), (m : G) ∈ T ↔ ((e m : Mof _) : Mc) ∈ Tc) ∧
      pCoreOf 2 H ≤ ⁅H ⊓ (L ⊔ T), H ⊓ (L ⊔ T)⁆ := by
  classical
  obtain ⟨e, he⟩ := exists_coords_plain S D.V_eq hP
  let M : Subgroup G := L ⊔ T
  let B : Subgroup G := H ⊓ M
  let R : Subgroup G := pCoreOf 2 H
  let f : ↥M →* Mc := (Mof (alternatingGroup (Fin 5))).subtype.comp e.toMonoidHom
  have hf : Function.Injective f := Subtype.coe_injective.comp e.injective
  have hBc : Bc ≤ Mof (alternatingGroup (Fin 5)) := by
    intro x hx
    exact mem_Mof.mpr (Equiv.Perm.mem_alternatingGroup.mpr hx.1)
  have hTc : Tc ≤ Mof (alternatingGroup (Fin 5)) := by
    intro x hx
    exact mem_Mof.mpr (Equiv.Perm.mem_alternatingGroup.mpr (sign_of_InK4 _ hx))
  have hBH (m : ↥M) : (m : G) ∈ H ↔ f m ∈ Bc := by
    have hsign : (f m).right.sign = 1 :=
      Equiv.Perm.mem_alternatingGroup.mp (mem_Mof.mp (e m).2)
    have hfix := mem_H_iff_fix_four S hH D m
    rw [← IsCoords.right he m] at hfix
    change (m : G) ∈ H ↔ (f m).right.sign = 1 ∧ (f m).right 4 = 4
    exact ⟨fun hm => ⟨hsign, hfix.mp hm⟩, fun hm => hfix.mpr hm.2⟩
  have hB (m : ↥M) : f m ∈ Bc ↔ (m : G) ∈ B :=
    ⟨fun hm => ⟨(hBH m).mpr hm, m.2⟩, fun hm => (hBH m).mp hm.1⟩
  have hT (m : ↥M) : f m ∈ Tc ↔ (m : G) ∈ T := by
    change InK4 (((e m : Mof _) : Mc).right) ↔ (m : G) ∈ T
    rw [IsCoords.right he m]
    exact ⟨fun hm => S.mem_T_of_InK4 ⟨(m : G), LT_le_normalizer S m.2⟩ m.2 hm,
      fun hm => hP ⟨(m : G), LT_le_normalizer S m.2⟩ hm⟩
  have hmap {K : Subgroup G} {Kc : Subgroup Mc} (hKM : K ≤ M)
      (hKc : Kc ≤ Mof (alternatingGroup (Fin 5)))
      (hmem : ∀ m : ↥M, f m ∈ Kc ↔ (m : G) ∈ K) :
      (K.subgroupOf M).map f = Kc := by
    apply le_antisymm
    · rintro _ ⟨m, hm, rfl⟩
      exact (hmem m).mpr (Subgroup.mem_subgroupOf.mp hm)
    · intro x hx
      let xM : Mof (alternatingGroup (Fin 5)) := ⟨x, hKc hx⟩
      let m : ↥M := e.symm xM
      have hfm : f m = x := congrArg Subtype.val (e.apply_symm_apply xM)
      exact ⟨m, Subgroup.mem_subgroupOf.mpr ((hmem m).mp (hfm ▸ hx)), hfm⟩
  have hTmap : (T.subgroupOf M).map f = Tc := hmap le_sup_right hTc hT
  have hBmap : (B.subgroupOf M).map f = Bc := hmap inf_le_right hBc hB
  have hcardT : Nat.card T = 64 := by
    calc
      Nat.card T = Nat.card (T.subgroupOf M) :=
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show T ≤ M from le_sup_right)).toEquiv).symm
      _ = Nat.card ((T.subgroupOf M).map f) := (Subgroup.card_map_of_injective hf).symm
      _ = 64 := by rw [hTmap, card_Tc]
  have hTI : T ≤ I := by
    have hcard : Nat.card T ≤ Nat.card ↥(T ⊓ I) := by rw [hcardT, S.card_inf_I hH D]
    have hEq : T ⊓ I = T := Subgroup.eq_of_le_of_card_ge inf_le_left hcard
    rw [← hEq]
    exact inf_le_right
  have hTH : T ≤ H := S.T_le_H hH
  have hRT : R ≤ T := F7.isSylowTwoOf_pCoreOf_le (S.sylow_of_le hTH)
  have hRM : R ≤ M := hRT.trans le_sup_right
  have hRI : R = pCoreOf 2 I := le_antisymm
    (F7.pCoreOf_le_pCoreOf_of_isSylowTwoOf (S.sylow_of_le hTH) hTI D.I_le)
    (F7.pCoreOf_mono_of_le_normalizer D.I_le D.I_normal)
  have hRcard : Nat.card R = 32 := by rw [hRI]; exact D.card_O2_I
  have hRnormal : ∀ h ∈ H, ∀ r ∈ R, h * r * h⁻¹ ∈ R := by
    intro h hh r hr
    exact (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H hh) r).mp hr
  have hVnot : ¬ V ≤ R := by
    intro hVR
    have hconj (h : G) (hh : h ∈ H) : conjSub h V = V := by
      apply Setting.elemAbelian16_eq_V S D.V_eq hP
      · exact F7.isElemAbelian_conjSub S.elemAbelian_V
      · rintro _ ⟨v, hv, rfl⟩
        exact hRT (hRnormal h hh v (hVR hv))
      · rw [conjSub, Subgroup.card_map_of_injective (MulAut.conj h).injective, S.card_V]
    have hHN : H ≤ Subgroup.normalizer (V : Set G) := by
      intro h hh
      rw [Subgroup.mem_normalizer_iff]
      intro v
      constructor
      · intro hv
        have hx : h * v * h⁻¹ ∈ conjSub h V := ⟨v, hv, rfl⟩
        rwa [hconj h hh] at hx
      · intro hv
        have hx : h⁻¹ * (h * v * h⁻¹) * h ∈ conjSub h⁻¹ V :=
          ⟨_, hv, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩
        rw [hconj h⁻¹ (H.inv_mem hh)] at hx
        simpa [mul_assoc] using hx
    exact hH.2.2 (hHN.trans S.NV_le_M)
  let X : Subgroup Mc := (R.subgroupOf M).map f
  have hmem (m : ↥M) : f m ∈ X ↔ (m : G) ∈ R := by
    constructor
    · rintro ⟨a, ha, h⟩
      have ham : a = m := hf h
      exact Subgroup.mem_subgroupOf.mp (ham ▸ ha)
    · intro hm
      exact ⟨m, Subgroup.mem_subgroupOf.mpr hm, rfl⟩
  have hXcard : Nat.card X = 32 := by
    rw [Subgroup.card_map_of_injective hf]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRM).toEquiv).trans hRcard
  have hXT : X ≤ Thc := by
    rintro _ ⟨m, hm, rfl⟩
    have hk : InK4 (f m).right := (hT m).mpr (hRT (Subgroup.mem_subgroupOf.mp hm))
    change InD (f m).right
    rcases hk with h | h | h | h <;> rw [h] <;> decide +kernel
  have hXB : ∀ b ∈ Bc, ∀ x ∈ X, b * x * b⁻¹ ∈ X := by
    intro b hb x hx
    obtain ⟨bP, hbP, hfb⟩ : ∃ bP ∈ B.subgroupOf M, f bP = b := by
      rw [← hBmap] at hb
      exact hb
    obtain ⟨a, ha, rfl⟩ := hx
    refine ⟨bP * a * bP⁻¹, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
    · exact hRnormal (bP : G) (Subgroup.mem_subgroupOf.mp hbP).1 (a : G)
        (Subgroup.mem_subgroupOf.mp ha)
    · simp only [map_mul, map_inv, hfb]
  have hXW : ¬ Wc ≤ X := by
    intro hWX
    apply hVnot
    intro v hv
    apply (hmem ⟨v, V_le_LT S hv⟩).mp
    apply hWX
    change ((e ⟨v, V_le_LT S hv⟩ : Mof _) : Mc) ∈ Wc
    rw [IsCoords.left he v hv]
    exact ⟨_, rfl⟩
  have hX : X = U0 := U0_unique hXT hXcard hXB hXW
  have hRcomm : R ≤ ⁅B, B⁆ := by
    have hcomm : (⁅B.subgroupOf M, B.subgroupOf M⁆).map f = ⁅Bc, Bc⁆ := by
      rw [Subgroup.map_commutator, hBmap]
    have hBsub : (B.subgroupOf M).map M.subtype = B :=
      Subgroup.map_subgroupOf_eq_of_le inf_le_right
    have hcommG : (⁅B.subgroupOf M, B.subgroupOf M⁆).map M.subtype = ⁅B, B⁆ := by
      rw [Subgroup.map_commutator, hBsub]
    intro r hr
    let m : ↥M := ⟨r, hRM hr⟩
    have hm : f m ∈ U0 := by rw [← hX]; exact (hmem m).mpr hr
    have hc : f m ∈ (⁅B.subgroupOf M, B.subgroupOf M⁆).map f := by
      rw [hcomm]
      exact U0_le_comm_Bc hm
    obtain ⟨a, ha, ham⟩ := hc
    have ham' : a = m := hf ham
    have hmcomm : m ∈ ⁅B.subgroupOf M, B.subgroupOf M⁆ := ham' ▸ ha
    have hrcomm : r ∈ (⁅B.subgroupOf M, B.subgroupOf M⁆).map M.subtype := ⟨m, hmcomm, rfl⟩
    rwa [hcommG] at hrcomm
  refine ⟨e, he, ?_, ?_, ?_, hRcomm⟩
  · intro m
    change (m : G) ∈ R ↔ f m ∈ U0
    rw [← hmem m, hX]
  · exact hBH
  · intro m
    exact (hT m).symm

end CFSG.GH74.QTGen4.U42
