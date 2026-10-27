module

public import CFSG.GH74.QTGen4.U42.GSidePairCoreExt
public import CFSG.GH74.QTGen4.U42.CoreFrameBounds

public section

namespace CFSG.GH74.QTGen4.U42

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.A5Model CFSG.Blueprint
open CFSG.Quasithin.H13 CFSG.Quasithin.H13.A5

variable {G : Type} [Group G] [Finite G] {T L V H I : Subgroup G}

theorem card_I_inf_LT (S : A5.Setting G T L V) (hH : H ∈ S.Hz) (D : Data13515 S H I) :
    Nat.card ↥(I ⊓ (L ⊔ T)) = 64 := by
  have hHM : ¬ H ≤ L ⊔ T := by rw [← D.M_eq]; exact hH.2.2
  have hIM : ¬ I ≤ L ⊔ T := fun h =>
    hHM ((H_eq_sup_B S hH D).le.trans (sup_le h inf_le_right))
  have hdvdT : Nat.card ↥(T ⊓ I) ∣ Nat.card ↥(I ⊓ (L ⊔ T)) :=
    Subgroup.card_dvd_of_le (le_inf inf_le_right (inf_le_left.trans le_sup_right))
  have hdvdI : Nat.card ↥(I ⊓ (L ⊔ T)) ∣ Nat.card I := Subgroup.card_dvd_of_le inf_le_left
  rw [S.card_inf_I hH D] at hdvdT
  rw [S.card_I D] at hdvdI
  obtain ⟨k, hk⟩ := hdvdT
  obtain ⟨m, hm⟩ := hdvdI
  have hkm : k * m = 3 := by
    have h64 : 64 * (k * m) = 64 * 3 := by rw [hk] at hm; linarith
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h64
  have hk3 : k ∣ 3 := ⟨m, hkm.symm⟩
  have hkle : k ≤ 3 := Nat.le_of_dvd (by norm_num) hk3
  interval_cases k
  · simp at hkm
  · omega
  · norm_num at hk3
  · exfalso
    have hcard : Nat.card I ≤ Nat.card ↥(I ⊓ (L ⊔ T)) := by rw [S.card_I D]; omega
    have heq : I ⊓ (L ⊔ T) = I := Subgroup.eq_of_le_of_card_ge inf_le_left hcard
    exact hIM (by rw [← heq]; exact inf_le_right)

theorem pairData_extension (S : A5.Setting G T L V) (hH : H ∈ S.Hz) (D : Data13515 S H I)
    (hE : ¬ _root_.CFSG.GH74.QTGen4.U42.Setting.PlainCase S) :
    ∃ e : ↥(L ⊔ T) ≃* Mof (⊤ : Subgroup (Equiv.Perm (Fin 5))), IsCoords S e ∧
      (∀ m : ↥(L ⊔ T), (m : G) ∈ pCoreOf 2 H ↔ ((e m : Mof _) : Mc) ∈ U0) ∧
      (∀ m : ↥(L ⊔ T), (m : G) ∈ H ↔ ((e m : Mof _) : Mc) ∈ Bhc) ∧
      (∀ m : ↥(L ⊔ T), (m : G) ∈ T ↔ ((e m : Mof _) : Mc) ∈ Thc) ∧
      pCoreOf 2 H ≤ ⁅H ⊓ (L ⊔ T), H ⊓ (L ⊔ T)⁆ := by
  classical
  obtain ⟨e, he⟩ := exists_coords_extension S D.V_eq hE
  let M : Subgroup G := L ⊔ T
  let B : Subgroup G := H ⊓ M
  let R : Subgroup G := pCoreOf 2 H
  let f : ↥M →* Mc := (Mof (⊤ : Subgroup (Equiv.Perm (Fin 5)))).subtype.comp e.toMonoidHom
  have hf : Function.Injective f := Subtype.coe_injective.comp e.injective
  have hBc : Bhc ≤ Mof (⊤ : Subgroup (Equiv.Perm (Fin 5))) :=
    fun _ _ => mem_Mof.mpr (Subgroup.mem_top _)
  have hTc : Thc ≤ Mof (⊤ : Subgroup (Equiv.Perm (Fin 5))) :=
    fun _ _ => mem_Mof.mpr (Subgroup.mem_top _)
  have hBH (m : ↥M) : (m : G) ∈ H ↔ f m ∈ Bhc := by
    have hfix := mem_H_iff_fix_four S hH D m
    rw [← IsCoords.right he m] at hfix
    exact hfix
  have hB (m : ↥M) : f m ∈ Bhc ↔ (m : G) ∈ B :=
    ⟨fun hm => ⟨(hBH m).mpr hm, m.2⟩, fun hm => (hBH m).mp hm.1⟩
  have hT (m : ↥M) : f m ∈ Thc ↔ (m : G) ∈ T := by
    change InD (((e m : Mof _) : Mc).right) ↔ (m : G) ∈ T
    rw [IsCoords.right he m]
    exact (mem_T_iff_InD_extension S hE m).symm
  have hmap {K : Subgroup G} {Kc : Subgroup Mc} (hKM : K ≤ M)
      (hKc : Kc ≤ Mof (⊤ : Subgroup (Equiv.Perm (Fin 5))))
      (hmem : ∀ m : ↥M, f m ∈ Kc ↔ (m : G) ∈ K) :
      (K.subgroupOf M).map f = Kc := by
    apply le_antisymm
    · rintro _ ⟨m, hm, rfl⟩
      exact (hmem m).mpr (Subgroup.mem_subgroupOf.mp hm)
    · intro x hx
      let xM : Mof (⊤ : Subgroup (Equiv.Perm (Fin 5))) := ⟨x, hKc hx⟩
      let m : ↥M := e.symm xM
      have hfm : f m = x := congrArg Subtype.val (e.apply_symm_apply xM)
      exact ⟨m, Subgroup.mem_subgroupOf.mpr ((hmem m).mp (hfm ▸ hx)), hfm⟩
  have hTmap : (T.subgroupOf M).map f = Thc := hmap le_sup_right hTc hT
  have hBmap : (B.subgroupOf M).map f = Bhc := hmap inf_le_right hBc hB
  have hTH : T ≤ H := S.T_le_H hH
  have hRT : R ≤ T := F7.isSylowTwoOf_pCoreOf_le (S.sylow_of_le hTH)
  have hRM : R ≤ M := hRT.trans le_sup_right
  have hRnormal : ∀ h ∈ H, ∀ r ∈ R, h * r * h⁻¹ ∈ R := by
    intro h hh r hr
    exact (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H hh) r).mp hr
  have hKB {K : Subgroup G} (hKN : B ≤ Subgroup.normalizer (K : Set G)) :
      ∀ b ∈ Bc, ∀ x ∈ (K.subgroupOf M).map f,
        b * x * b⁻¹ ∈ (K.subgroupOf M).map f := by
    intro b hb x hx
    have hb' : b ∈ (B.subgroupOf M).map f := by rw [hBmap]; exact Bc_le_Bhc hb
    obtain ⟨bP, hbP, hfb⟩ := hb'
    obtain ⟨a, ha, rfl⟩ := hx
    refine ⟨bP * a * bP⁻¹, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp
        (hKN (Subgroup.mem_subgroupOf.mp hbP)) (a : G)).mp (Subgroup.mem_subgroupOf.mp ha)
    · simp only [map_mul, map_inv, hfb]
  let Z : Subgroup G := I ⊓ M
  have hZcard : Nat.card Z = 64 := card_I_inf_LT S hH D
  have hZB : Z ≤ B := le_inf (inf_le_left.trans D.I_le) inf_le_right
  have hZN : B ≤ Subgroup.normalizer (Z : Set G) :=
    F7.le_normalizer_inf (inf_le_left.trans D.I_normal) (inf_le_right.trans Subgroup.le_normalizer)
  have hZtwo : IsPGroup 2 Z := IsPGroup.of_card (n := 6) (hZcard.trans (by norm_num))
  have hZT : Z ≤ T :=
    (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hZB hZN hZtwo).trans
      (F7.isSylowTwoOf_pCoreOf_le (S.sylow_of_le (le_inf hTH le_sup_right)))
  let ZX : Subgroup Mc := (Z.subgroupOf M).map f
  have hZXB : ∀ b ∈ Bc, ∀ x ∈ ZX, b * x * b⁻¹ ∈ ZX := hKB hZN
  have hZXT : ZX ≤ Thc := by
    rintro _ ⟨m, hm, rfl⟩
    exact (hT m).mpr (hZT (Subgroup.mem_subgroupOf.mp hm))
  have hZXK : ZX ≤ Tc := right_InK4 hZXT hZXB
  have hZXcard : Nat.card ZX = 64 := by
    rw [Subgroup.card_map_of_injective hf,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show Z ≤ M from inf_le_right)).toEquiv,
      hZcard]
  have hZXeq : ZX = Tc := Subgroup.eq_of_le_of_card_ge hZXK (by rw [hZXcard, card_Tc])
  let X : Subgroup Mc := (R.subgroupOf M).map f
  have hmem (m : ↥M) : f m ∈ X ↔ (m : G) ∈ R := by
    constructor
    · rintro ⟨a, ha, h⟩
      have ham : a = m := hf h
      exact Subgroup.mem_subgroupOf.mp (ham ▸ ha)
    · intro hm
      exact ⟨m, Subgroup.mem_subgroupOf.mpr hm, rfl⟩
  have hXT : X ≤ Thc := by
    rintro _ ⟨m, hm, rfl⟩
    exact (hT m).mpr (hRT (Subgroup.mem_subgroupOf.mp hm))
  have hXB : ∀ b ∈ Bc, ∀ x ∈ X, b * x * b⁻¹ ∈ X :=
    hKB (inf_le_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H))
  have hXK : X ≤ Tc := right_InK4 hXT hXB
  have hRIle : R ≤ I := by
    intro r hr
    let m : ↥M := ⟨r, hRM hr⟩
    have hm : f m ∈ ZX := by rw [hZXeq]; exact hXK ((hmem m).mpr hr)
    obtain ⟨a, ha, ham⟩ := hm
    have ham' : a = m := hf ham
    have haZ : (m : G) ∈ Z := Subgroup.mem_subgroupOf.mp (ham' ▸ ha)
    exact haZ.1
  have hRI : R = pCoreOf 2 I := le_antisymm
    (fun r hr => F7.pCoreOf_inf_le D.I_le ⟨hr, hRIle hr⟩)
    (F7.pCoreOf_mono_of_le_normalizer D.I_le D.I_normal)
  have hRcard : Nat.card R = 32 := by rw [hRI]; exact D.card_O2_I
  have hXcard : Nat.card X = 32 := by
    rw [Subgroup.card_map_of_injective hf]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRM).toEquiv).trans hRcard
  have hXW : ¬ Wc ≤ X := not_Wc_le_of_card32_normalized_Bc hXT hXB hXcard
  have hX : X = U0 := U0_unique hXT hXcard hXB hXW
  have hRcomm : R ≤ ⁅B, B⁆ := by
    have hcomm : (⁅B.subgroupOf M, B.subgroupOf M⁆).map f = ⁅Bhc, Bhc⁆ := by
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
      exact U0_le_comm_Bhc hm
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
