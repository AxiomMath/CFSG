module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.GoldschmidtM22EndN5c
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.GoldschmidtM22EndN5d
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.GoldschmidtM22EndN5e
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.GoldschmidtM22EndN5f

public section

namespace CFSG.Quasithin.H13.GM22

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3 CFSG.Quasithin

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V : Subgroup G}

namespace KData

variable {g : G} {D : Subgroup G} (hk : KData T L V g D) (h : Hyp6Sec2 G T M L V)
  (P : PsiData T L V 3) (hZ : Nat.card (quasithinOmegaOneCenter T) = 2)

include hk P h hZ in

theorem exists_sylow_three_F4 (h621 : Stmt6_2_1_F4) (h629 : Stmt6_2_9_F4) (h6210 : Stmt6_2_10_F4)
    (h6211 : Stmt6_2_11_F4) (h6212 : Stmt6_2_12_F4) (hT : Nat.card ↥T = 128) :
    ∃ X : Subgroup G, IsSylowIn 3 X (HH T) ∧
      D ⊓ Subgroup.centralizer (X : Set G) = quasithinOmegaOneCenter T := by
  obtain ⟨a, x, haV, haC, hg, ha2, hxK, hx3, hx1, haxa, hxN⟩ := hk.exists_x_F4 h P hZ h6210
  have hxH : x ∈ HH T := hk.K_le_HH hxK
  have hord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hXH : Subgroup.zpowers x ≤ HH T := Subgroup.zpowers_le.mpr hxH
  refine ⟨Subgroup.zpowers x, ⟨hXH, ?_, ?_⟩, ?_⟩
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord]; norm_num)
  · have h1 := Subgroup.relIndex_mul_card (H := Subgroup.zpowers x) (K := HH T)
    rw [inf_eq_left.mpr hXH, Nat.card_zpowers, hord, P.card_HH,
      P.card_CHU_of_caseA_F4 h hZ h629 h6210 h6212 hT] at h1
    omega
  · apply le_antisymm
    · by_contra hne
      set C : Subgroup G := D ⊓ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G)
        with hC
      have hZC : quasithinOmegaOneCenter T ≤ C := fun z hz =>
        ⟨hk.Z_le_D hz, Subgroup.mem_centralizer_iff.mpr fun y hy => Z_central T (hXH hy) hz⟩
      have hlt : quasithinOmegaOneCenter T < C := lt_of_le_not_ge hZC hne
      have hCT : C ≤ T :=
        inf_le_left.trans (hk.D_le_CHU.trans (P.CHU_le_T_F4 h hZ h621 h629 h6210 h6212))
      have haT : (a : G) ∈ T := h.toHyp611.le_T haV
      have hT''T : C ⊔ Subgroup.zpowers (a : G) ≤ T :=
        sup_le hCT (Subgroup.zpowers_le.mpr haT)
      have hT''p : IsPGroup 2 ↥(C ⊔ Subgroup.zpowers (a : G)) := h.sylow.1.to_le hT''T

      have haX : (a : G) ∈ Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
        rw [← conjSubgroup_eq_iff_mem_normalizer]
        have ha1 : (a : G)⁻¹ = (a : G) := by
          rw [inv_eq_iff_mul_eq_one, ← pow_two]
          exact ha2
        unfold conjSubgroup
        rw [MonoidHom.map_zpowers]
        have : (MulAut.conj (a : G)⁻¹).toMonoidHom x = x⁻¹ := by
          rw [ha1]
          have := haxa
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          exact this
        rw [this, Subgroup.zpowers_inv]
      have haD : (a : G) ∈ Subgroup.normalizer (D : Set G) :=
        hk.K_le_normalizer_D (Subgroup.mem_sup_left haV)
      have haCG : (a : G) ∈ Subgroup.normalizer
          (Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) : Set G) := by
        rw [← conjSubgroup_eq_iff_mem_normalizer,
          CFSG.QuasithinUnique.C5.conjSubgroup_centralizer,
          conjSubgroup_eq_iff_mem_normalizer.mpr haX]
      have haC' : (a : G) ∈ Subgroup.normalizer (C : Set G) := by
        rw [Subgroup.mem_normalizer_iff]
        intro y
        have h1 := Subgroup.mem_normalizer_iff.mp haD y
        have h2 := Subgroup.mem_normalizer_iff.mp haCG y
        simp only [hC, Subgroup.mem_inf]
        rw [h1, h2]
      have hT''N : C ⊔ Subgroup.zpowers (a : G) ≤ Subgroup.normalizer (C : Set G) :=
        sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr haC')
      have hT''Z : C ⊔ Subgroup.zpowers (a : G) ≤
          Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
        sup_le (fun y hy => HH_le_normalizer_Z T (hk.D_le_HH (Subgroup.mem_inf.mp hy).1))
          (Subgroup.zpowers_le.mpr (HH_le_normalizer_Z T a.2))
      obtain ⟨c, hcC, hcZ, hcfix⟩ := exists_fixed_mod hT''p le_sup_left hlt hT''N hT''Z
      have hac := hcfix (a : G) (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
      have hcD : c ∈ D := (Subgroup.mem_inf.mp hcC).1
      have hcV0 := hk.comm_a_mem_V0_F4 h P hZ a haV haC hg ha2 h6211 hcD hac
      have hcx : x * c = c * x :=
        Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hcC).2 x (Subgroup.mem_zpowers x)
      have hcV : c ∈ conjSubgroup V x⁻¹ := by
        refine mem_conjSubgroup_iff.mpr ?_
        have : x⁻¹ * c * (x⁻¹)⁻¹ = c := by
          calc x⁻¹ * c * (x⁻¹)⁻¹ = x⁻¹ * (c * x) := by group
            _ = x⁻¹ * (x * c) := by rw [hcx]
            _ = c := by group
        rw [this]
        exact (Subgroup.mem_inf.mp hcV0).1
      have hxinvN : x⁻¹ ∉ Subgroup.normalizer (V : Set G) := fun hN =>
        hxN (by simpa using (Subgroup.normalizer (V : Set G)).inv_mem hN)
      have hZ' := hk.inter_conj_eq_Z P a haV haC hg ((HH T).inv_mem hxH) hxinvN
      exact hcZ (hZ' ▸ ⟨(Subgroup.mem_inf.mp hcV0).1, hcV⟩)
    · intro z hz
      exact ⟨hk.Z_le_D hz, Subgroup.mem_centralizer_iff.mpr fun y hy =>
        Z_central T (hXH hy) hz⟩

end KData

end CFSG.Quasithin.H13.GM22
