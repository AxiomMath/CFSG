module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A2V2

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private theorem y7a_M3_comm (c : Ctx7 G L) (hH : F33Hyp c.s c.e) {x y : G}
    (hx : x ∈ M3 c.s) (hy : y ∈ M3 c.s) : x * y = y * x := by
  haveI : IsMulCommutative ↥(M3 c.s) := (y7a_M3_elemAbelian c hH).1
  exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : ↥(M3 c.s)) ⟨y, hy⟩)

private theorem y7a_M3_comm_E (c : Ctx7 G L) (hH : F33Hyp c.s c.e) {m : G} (hm : m ∈ M3 c.s)
    (he0 : (c.s.fr.a₁ * c.s.fr.b₁ * c.s.fr.a₂) * m =
      m * (c.s.fr.a₁ * c.s.fr.b₁ * c.s.fr.a₂)) :
    ∀ x ∈ c.s.fr.E, m * x = x * m := by
  have hbF : c.s.fr.b₁ * c.s.fr.b₂ ∈ c.s.fr.F := Subgroup.subset_closure (by simp)
  have hzF : c.s.fr.z ∈ c.s.fr.F := Subgroup.subset_closure (by simp)
  have hle : c.s.fr.E ≤ centralizer ({m} : Set G) := by
    change closure ({c.s.fr.b₁ * c.s.fr.b₂, c.s.fr.a₁ * c.s.fr.b₁ * c.s.fr.a₂,
      c.s.fr.z} : Set G) ≤ centralizer ({m} : Set G)
    rw [Subgroup.closure_le]
    intro x hx
    have hx' : x = c.s.fr.b₁ * c.s.fr.b₂ ∨ x = c.s.fr.a₁ * c.s.fr.b₁ * c.s.fr.a₂ ∨
        x = c.s.fr.z := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hx
    refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    rcases hx' with rfl | rfl | rfl
    · exact y7a_M3_comm c hH hm (y7a_F_le_M3 c hbF)
    · exact he0.symm
    · exact y7a_M3_comm c hH hm (y7a_F_le_M3 c hzF)
  intro x hx
  exact (Subgroup.mem_centralizer_iff.mp (hle hx)) m (Set.mem_singleton m)

private theorem y7a_M3_cent_e0_le_V2 (c : Ctx7 G L) (hH : F33Hyp c.s c.e)
    (hF : c.toCtx5.Facts5) (h71 : c.Fact71) :
    M3 c.s ⊓ centralizer ({(c.s.fr.a₁ * c.s.fr.b₁ * c.s.fr.a₂)} : Set G) ≤ V2 c.e := by
  intro m hm
  obtain ⟨hmM3, hmc⟩ := Subgroup.mem_inf.mp hm
  have he0 : (c.s.fr.a₁ * c.s.fr.b₁ * c.s.fr.a₂) * m =
      m * (c.s.fr.a₁ * c.s.fr.b₁ * c.s.fr.a₂) :=
    (Subgroup.mem_centralizer_singleton_iff.mp hmc).symm
  rw [y7a_V2_mem_iff c hH hF h71]
  exact ⟨h71.2.2.2.1 hmM3, y7a_M3_comm_E c hH hmM3 he0,
    fun x hx => y7a_M3_comm c hH hmM3 (y7a_F_le_M3 c hx)⟩

private theorem y7a_F_le_I (c : Ctx7 G L) (hH : F33Hyp c.s c.e) :
    c.s.fr.F ≤ centIn (M2 c.s) c.s.fr.F := by
  intro f hf
  refine Subgroup.mem_inf.mpr ⟨y54_B_le_M2 c.s (y54_F_le_B hH hf), ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro f' hf'
  exact (y54_F_comm hH f hf f' hf').symm

theorem y7a_card_I (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5) :
    Nat.card ↥(centIn (M2 c.s) c.s.fr.F) = 32 := by
  have hcardF : Nat.card ↥c.s.fr.F = 8 := by
    rw [(y54_F_isE3 hH).2]; norm_num
  have hrel : c.s.fr.F.relIndex (centIn (M2 c.s) c.s.fr.F) = 4 := hF.2.2.1.2.2.2.2.1
  have h := Subgroup.relIndex_mul_card (H := c.s.fr.F) (K := centIn (M2 c.s) c.s.fr.F)
  rw [hrel, inf_eq_left.mpr (y7a_F_le_I c hH), hcardF] at h
  omega

theorem y7a_V2_le_I (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    (h71 : c.Fact71) : V2 c.e ≤ centIn (M2 c.s) c.s.fr.F := by
  have hI_le_M3 : centIn (M2 c.s) c.s.fr.F ≤ M3 c.s := hF.2.2.1.2.2.1
  have hM3_le_M6 : M3 c.s ≤ M6 c.e := h71.2.2.2.1
  have hZ_le_M3 : c.s.fr.Z ≤ M3 c.s := by
    rw [SFrame.Z, Subgroup.zpowers_le]
    exact y7a_F_le_M3 c (y54_z_mem_F c.s)
  have he0E : c.s.fr.a₁ * c.s.fr.b₁ * c.s.fr.a₂ ∈ c.s.fr.E :=
    Subgroup.subset_closure (by simp)
  have he0A : c.s.fr.a₁ * c.s.fr.b₁ * c.s.fr.a₂ ∈ c.s.fr.A := s3_E_le_A c.s he0E
  obtain ⟨R, hRle, -, hcard⟩ :=
    y7a_comm_range (V := centIn (M2 c.s) c.s.fr.F) (W := c.s.fr.Z)
      (t := c.s.fr.a₁ * c.s.fr.b₁ * c.s.fr.a₂)
      (fun _ hw _ hw' => y7a_M3_comm c hH (hZ_le_M3 hw) (hZ_le_M3 hw'))
      (fun _ hw _ hv => y7a_M3_comm c hH (hI_le_M3 hv) (hZ_le_M3 hw))
      (by
        intro v hv
        have hvM6 : v ∈ M6 c.e := hM3_le_M6 (hI_le_M3 hv)
        have hvM2 : v ∈ M2 c.s := (Subgroup.mem_inf.mp hv).1
        have hV1 : ⁅v, c.s.fr.a₁ * c.s.fr.b₁ * c.s.fr.a₂⁆ ∈ V1 c.e :=
          h71.2.1.2.2.2.1 (Subgroup.commutator_mem_commutator hvM6
            (Subgroup.mem_sup_left he0A))
        have hcenB : ⁅v, c.s.fr.a₁ * c.s.fr.b₁ * c.s.fr.a₂⁆ ∈ cen c.s.fr.B :=
          y54_C2_comm_V c.toCtx5 hH v (y54_M2_le_C2 c.toCtx5 hH hvM2)
            (c.s.fr.a₁ * c.s.fr.b₁ * c.s.fr.a₂)
            (y54_M2_le_C2 c.toCtx5 hH (y54_B_le_M2 c.s (y56_E_le_B hH he0E)))
        have hA : ⁅v, c.s.fr.a₁ * c.s.fr.b₁ * c.s.fr.a₂⁆ ∈ c.s.fr.A :=
          s3_F_le_A c.s (y54_V_le_F hH hcenB)
        have hmem : ⁅v, c.s.fr.a₁ * c.s.fr.b₁ * c.s.fr.a₂⁆ ∈ c.s.fr.A ⊓ V1 c.e :=
          ⟨hA, hV1⟩
        rw [y7a_A_inf_V (c.y7acfg hH)] at hmem
        simpa [SFrame.Z] using hmem)
  have hZcard : Nat.card ↥(c.s.fr.Z) = 2 := by
    rw [SFrame.Z, Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact y7a_z_sq (c.y7acfg hH))
      (y56_v0 hH).2.2.2.1
  have hRcard : Nat.card ↥R ≤ 2 := (Subgroup.card_le_of_le hRle).trans_eq hZcard
  have hIcard : Nat.card ↥(centIn (M2 c.s) c.s.fr.F) = 32 := y7a_card_I c hH hF
  have hge : 16 ≤ Nat.card ↥(centIn (M2 c.s) c.s.fr.F ⊓
      centralizer ({c.s.fr.a₁ * c.s.fr.b₁ * c.s.fr.a₂} : Set G)) := by
    have h1 : (16 : ℕ) * 2 ≤ Nat.card ↥(centIn (M2 c.s) c.s.fr.F ⊓
        centralizer ({c.s.fr.a₁ * c.s.fr.b₁ * c.s.fr.a₂} : Set G)) * 2 := by
      calc (16 : ℕ) * 2 = 32 := by norm_num
        _ = Nat.card ↥(centIn (M2 c.s) c.s.fr.F) := hIcard.symm
        _ = Nat.card ↥(centIn (M2 c.s) c.s.fr.F ⊓
              centralizer ({c.s.fr.a₁ * c.s.fr.b₁ * c.s.fr.a₂} : Set G)) *
              Nat.card ↥R := hcard
        _ ≤ Nat.card ↥(centIn (M2 c.s) c.s.fr.F ⊓
              centralizer ({c.s.fr.a₁ * c.s.fr.b₁ * c.s.fr.a₂} : Set G)) * 2 :=
              Nat.mul_le_mul_left _ hRcard
    exact Nat.le_of_mul_le_mul_right h1 (by norm_num)
  have hleV2 : centIn (M2 c.s) c.s.fr.F ⊓
      centralizer ({c.s.fr.a₁ * c.s.fr.b₁ * c.s.fr.a₂} : Set G) ≤ V2 c.e := by
    intro m hm
    obtain ⟨hmI, hmc⟩ := Subgroup.mem_inf.mp hm
    exact y7a_M3_cent_e0_le_V2 c hH hF h71
      (Subgroup.mem_inf.mpr ⟨hI_le_M3 hmI, hmc⟩)
  have hV2card : Nat.card ↥(V2 c.e) = 16 := by
    rw [(y7a_V2_data c hH hF h71).1]; norm_num
  have hcardLe : Nat.card ↥(V2 c.e) ≤ Nat.card ↥(centIn (M2 c.s) c.s.fr.F ⊓
      centralizer ({c.s.fr.a₁ * c.s.fr.b₁ * c.s.fr.a₂} : Set G)) := by
    rw [hV2card]; exact hge
  have heq : centIn (M2 c.s) c.s.fr.F ⊓
      centralizer ({c.s.fr.a₁ * c.s.fr.b₁ * c.s.fr.a₂} : Set G) = V2 c.e :=
    Subgroup.eq_of_le_of_card_ge hleV2 hcardLe
  rw [← heq]
  exact inf_le_left

theorem y7a_I_eq (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    (h71 : c.Fact71) : centIn (M2 c.s) c.s.fr.F = c.s.fr.F ⊔ V2 c.e := by
  have hle : c.s.fr.F ⊔ V2 c.e ≤ centIn (M2 c.s) c.s.fr.F :=
    sup_le (y7a_F_le_I c hH) (y7a_V2_le_I c hH hF h71)
  have hV2leM3 : V2 c.e ≤ M3 c.s := by rw [V2]; exact inf_le_left
  have hcomm : ∀ e ∈ c.s.fr.F, ∀ v ∈ V2 c.e, e * v = v * e :=
    fun _ he _ hv => y7a_M3_comm c hH (y7a_F_le_M3 c he) (hV2leM3 hv)
  have hinf : c.s.fr.F ⊓ V2 c.e = cen c.s.fr.B := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hxF, hxV2⟩ := Subgroup.mem_inf.mp hx
      have hx' : x ∈ V2 c.e ⊓ c.s.fr.A := ⟨hxV2, s3_F_le_A c.s hxF⟩
      rwa [y7a_V2_inf_A c hH hF h71] at hx'
    · intro x hx
      exact Subgroup.mem_inf.mpr ⟨y54_V_le_F hH hx, y7a_cenB_le_V2 c hH hF h71 hx⟩
  have hcardF : Nat.card ↥c.s.fr.F = 8 := by rw [(y54_F_isE3 hH).2]; norm_num
  have hV2card : Nat.card ↥(V2 c.e) = 16 := by
    rw [(y7a_V2_data c hH hF h71).1]; norm_num
  have hinfcard : Nat.card ↥(c.s.fr.F ⊓ V2 c.e) = 4 := by rw [hinf, y54_V_card hH]
  have hprod := y7a_card_sup_mul_inf (E := c.s.fr.F) (V := V2 c.e) hcomm
  rw [hinfcard, hcardF, hV2card] at hprod
  have hsupcard : Nat.card ↥(c.s.fr.F ⊔ V2 c.e) = 32 := by omega
  have heq : c.s.fr.F ⊔ V2 c.e = centIn (M2 c.s) c.s.fr.F :=
    Subgroup.eq_of_le_of_card_ge hle (by simp [y7a_card_I c hH hF, hsupcard])
  exact heq.symm

theorem y7a_M2_eq (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    (h71 : c.Fact71) : M2 c.s = c.s.fr.B ⊔ V2 c.e := by
  rw [hF.2.2.1.2.2.2.1, y7a_I_eq c hH hF h71, sup_assoc,
    sup_eq_right.mpr ((y54_F_le_B hH).trans (le_sup_right : c.s.fr.B ≤ V2 c.e ⊔ c.s.fr.B))]
  exact sup_comm _ _

theorem y7a_B_inf_V2 (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    (h71 : c.Fact71) : c.s.fr.B ⊓ V2 c.e = cen c.s.fr.B := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxB, hxV2⟩ := Subgroup.mem_inf.mp hx
    have hxH : x ∈ c.s.H := s3_L_le_H c.s hH.hS ((s3_S_le_L c.s) ((s3_B_le_S c.s) hxB))
    have hxM6 : x ∈ M6 c.e := h71.2.2.2.1 (Subgroup.mem_inf.mp hxV2).1
    have hxA : x ∈ c.s.fr.A := by
      have hx' : x ∈ c.s.H ⊓ M6 c.e := ⟨hxH, hxM6⟩
      rwa [h71.2.1.2.1] at hx'
    have hx'' : x ∈ V2 c.e ⊓ c.s.fr.A := ⟨hxV2, hxA⟩
    rwa [y7a_V2_inf_A c hH hF h71] at hx''
  · intro x hx
    exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx).1, y7a_cenB_le_V2 c hH hF h71 hx⟩

end CFSG.OddStandard.HigherRank.YamadaG23
