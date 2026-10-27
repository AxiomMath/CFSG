module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A2Ab1
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A2CF
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A2CE

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private lemma y7a_M3_comm (c : Ctx7 G L) (hH : F33Hyp c.s c.e) {x y : G}
    (hx : x ∈ M3 c.s) (hy : y ∈ M3 c.s) : x * y = y * x := by
  haveI : IsMulCommutative ↥(M3 c.s) := (y7a_M3_elemAbelian c hH).1
  exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : ↥(M3 c.s)) ⟨y, hy⟩)

private lemma y7a_M3_comm_F (c : Ctx7 G L) (hH : F33Hyp c.s c.e) {m : G}
    (hm : m ∈ M3 c.s) : ∀ x ∈ c.s.fr.F, m * x = x * m :=
  fun x hx => y7a_M3_comm c hH hm (y7a_F_le_M3 c hx)

private lemma y7a_M3_comm_E (c : Ctx7 G L) (hH : F33Hyp c.s c.e) {m : G} (hm : m ∈ M3 c.s)
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

theorem y7a_V2_mem_iff (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    (h71 : c.Fact71) (m : G) :
    m ∈ V2 c.e ↔ m ∈ M6 c.e ∧ (∀ x ∈ c.s.fr.E, m * x = x * m) ∧
      (∀ x ∈ c.s.fr.F, m * x = x * m) := by
  rw [V2, Subgroup.mem_inf, ← y7a_cent_M6_F c hH hF h71, ← y7a_cent_M6_E c hH hF h71]
  simp only [centIn, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨⟨hm6, hFc⟩, -, hEc⟩
    exact ⟨hm6, fun x hx => (hEc x hx).symm, fun x hx => (hFc x hx).symm⟩
  · rintro ⟨hm6, hE, hF'⟩
    exact ⟨⟨hm6, fun x hx => (hF' x hx).symm⟩, hm6, fun x hx => (hE x hx).symm⟩

theorem y7a_cenB_le_V2 (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    (h71 : c.Fact71) : cen c.s.fr.B ≤ V2 c.e := by
  intro m hm
  rw [y7a_V2_mem_iff c hH hF h71]
  have hEF : c.s.fr.E ⊓ c.s.fr.F = cen c.s.fr.B := hH.hLF.fact14.2.2.2.1.2.2.2
  have hmEF : m ∈ c.s.fr.E ⊓ c.s.fr.F := by rwa [hEF]
  obtain ⟨hmE, hmF⟩ := Subgroup.mem_inf.mp hmEF
  exact ⟨y7a_AV1_le_M6 c hH hF (Subgroup.mem_sup_left (s3_E_le_A c.s hmE)),
    fun x hx => y56_E_comm hH m hmE x hx, fun x hx => y54_F_comm hH m hmF x hx⟩

theorem y7a_V2_inf_A (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    (h71 : c.Fact71) : V2 c.e ⊓ c.s.fr.A = cen c.s.fr.B := by
  have hEF : c.s.fr.E ⊓ c.s.fr.F = cen c.s.fr.B := hH.hLF.fact14.2.2.2.1.2.2.2
  apply le_antisymm
  · intro a ha
    obtain ⟨haV2, haA⟩ := Subgroup.mem_inf.mp ha
    obtain ⟨-, hE, hF'⟩ := (y7a_V2_mem_iff c hH hF h71 a).mp haV2
    have haE : a ∈ c.s.fr.E := by
      have h : a ∈ centIn L c.s.fr.E :=
        ⟨s3_A_le_L c.s haA, fun x hx => (hE x hx).symm⟩
      rwa [y56_centIn_L_E hH] at h
    have haF : a ∈ c.s.fr.F := by
      have h : a ∈ centIn L c.s.fr.F :=
        ⟨s3_A_le_L c.s haA, fun x hx => (hF' x hx).symm⟩
      simpa [hH.hLF.fact18.2.2.2.1, f3_zL_eq_bot hH] using h
    rw [← hEF]
    exact ⟨haE, haF⟩
  · intro a ha
    refine Subgroup.mem_inf.mpr ⟨y7a_cenB_le_V2 c hH hF h71 ha, ?_⟩
    rw [← hEF] at ha
    exact s3_F_le_A c.s (Subgroup.mem_inf.mp ha).2

theorem y7a_V2_comm_t (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    (h71 : c.Fact71) : ∀ m ∈ V2 c.e, ⁅m, c.s.t⁆ ∈ cen c.s.fr.B := by
  intro m hm
  obtain ⟨hmM6, hE, hF'⟩ := (y7a_V2_mem_iff c hH hF h71 m).mp hm
  have hEF : c.s.fr.E ⊓ c.s.fr.F = cen c.s.fr.B := hH.hLF.fact14.2.2.2.1.2.2.2
  rw [← hEF]
  exact ⟨y7a_comm_t_E c hH hF hmM6 hE, y7a_comm_t_F c hH hF hmM6 hF'⟩

private lemma y7a_M3_cent_e0_le_V2 (c : Ctx7 G L) (hH : F33Hyp c.s c.e)
    (hF : c.toCtx5.Facts5) (h71 : c.Fact71) :
    M3 c.s ⊓ centralizer ({(c.s.fr.a₁ * c.s.fr.b₁ * c.s.fr.a₂)} : Set G) ≤ V2 c.e := by
  intro m hm
  obtain ⟨hmM3, hmc⟩ := Subgroup.mem_inf.mp hm
  have he0 : (c.s.fr.a₁ * c.s.fr.b₁ * c.s.fr.a₂) * m =
      m * (c.s.fr.a₁ * c.s.fr.b₁ * c.s.fr.a₂) :=
    (Subgroup.mem_centralizer_singleton_iff.mp hmc).symm
  rw [y7a_V2_mem_iff c hH hF h71]
  exact ⟨h71.2.2.2.1 hmM3, y7a_M3_comm_E c hH hmM3 he0, y7a_M3_comm_F c hH hmM3⟩

theorem y7a_V2_data (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    (h71 : c.Fact71) :
    Nat.card ↥(V2 c.e) = 2 ^ 4 ∧ ∃ u ∈ V2 c.e, ⁅u, c.s.t⁆ = c.s.fr.b₁ * c.s.fr.b₂ := by
  have hV23 : V2 c.e ≤ M3 c.s := by rw [V2]; exact inf_le_left
  have hlow : 16 ≤ Nat.card ↥(V2 c.e) := by
    have hWab : ∀ w ∈ V1 c.e, ∀ w' ∈ V1 c.e, w * w' = w' * w :=
      fun w hw w' hw' => y7a_M3_comm c hH (y7a_V1_le_M3 c hw) (y7a_V1_le_M3 c hw')
    have hW : ∀ w ∈ V1 c.e, ∀ v ∈ M3 c.s, v * w = w * v :=
      fun w hw v hv => y7a_M3_comm c hH hv (y7a_V1_le_M3 c hw)
    have hVW : ∀ v ∈ M3 c.s, ⁅v, c.s.fr.a₁ * c.s.fr.b₁ * c.s.fr.a₂⁆ ∈ V1 c.e := fun v hv =>
      h71.2.1.2.2.2.1 (Subgroup.commutator_mem_commutator (h71.2.2.2.1 hv)
        (Subgroup.mem_sup_left (s3_E_le_A c.s (Subgroup.subset_closure (by simp)))))
    obtain ⟨R₁, hR₁le, -, hcard₁⟩ := y7a_comm_range (V := M3 c.s) (W := V1 c.e)
      (t := c.s.fr.a₁ * c.s.fr.b₁ * c.s.fr.a₂) hWab hW hVW
    have hR₁card : Nat.card ↥R₁ ≤ 4 :=
      (Subgroup.card_le_of_le hR₁le).trans_eq (y7a_card_V (c.y7acfg hH))
    have hge : 16 ≤ Nat.card ↥(M3 c.s ⊓ centralizer
        ({c.s.fr.a₁ * c.s.fr.b₁ * c.s.fr.a₂} : Set G)) := by
      have h1 : (16 : ℕ) * 4 ≤ Nat.card ↥(M3 c.s ⊓ centralizer
          ({c.s.fr.a₁ * c.s.fr.b₁ * c.s.fr.a₂} : Set G)) * 4 := by
        calc (16 : ℕ) * 4 = 64 := by norm_num
          _ = Nat.card ↥(M3 c.s) := (y7a_card_M3 c hH).symm
          _ = Nat.card ↥(M3 c.s ⊓ centralizer
                ({c.s.fr.a₁ * c.s.fr.b₁ * c.s.fr.a₂} : Set G)) * Nat.card ↥R₁ := hcard₁
          _ ≤ Nat.card ↥(M3 c.s ⊓ centralizer
                ({c.s.fr.a₁ * c.s.fr.b₁ * c.s.fr.a₂} : Set G)) * 4 :=
              Nat.mul_le_mul_left _ hR₁card
      exact Nat.le_of_mul_le_mul_right h1 (by norm_num)
    exact hge.trans (Subgroup.card_le_of_le (y7a_M3_cent_e0_le_V2 c hH hF h71))
  have hWab₂ : ∀ w ∈ cen c.s.fr.B, ∀ w' ∈ cen c.s.fr.B, w * w' = w' * w :=
    fun w hw w' hw' => y56_E_comm hH w (y56_V_le_E hH hw) w' (y56_V_le_E hH hw')
  have hW₂ : ∀ w ∈ cen c.s.fr.B, ∀ v ∈ V2 c.e, v * w = w * v := fun w hw v hv =>
    y7a_M3_comm c hH (hV23 hv) (hV23 (y7a_cenB_le_V2 c hH hF h71 hw))
  obtain ⟨R₂, hR₂le, hR₂mem, hcard₂⟩ := y7a_comm_range (V := V2 c.e) (W := cen c.s.fr.B)
    (t := c.s.t) hWab₂ hW₂ (y7a_V2_comm_t c hH hF h71)
  have hct : V2 c.e ⊓ centralizer ({c.s.t} : Set G) ≤ cen c.s.fr.B := by
    intro x hx
    obtain ⟨hxV2, hxH⟩ := Subgroup.mem_inf.mp hx
    have hxM6 : x ∈ M6 c.e := h71.2.2.2.1 (hV23 hxV2)
    have hxA : x ∈ c.s.fr.A := by
      have hx' : x ∈ c.s.H ⊓ M6 c.e := ⟨hxH, hxM6⟩
      rwa [h71.2.1.2.1] at hx'
    rw [← y7a_V2_inf_A c hH hF h71]
    exact ⟨hxV2, hxA⟩
  have hctc : Nat.card ↥(V2 c.e ⊓ centralizer ({c.s.t} : Set G)) ≤ 4 :=
    (Subgroup.card_le_of_le hct).trans_eq (y54_V_card hH)
  have hR₂c : Nat.card ↥R₂ ≤ 4 :=
    (Subgroup.card_le_of_le hR₂le).trans_eq (y54_V_card hH)
  have hup : Nat.card ↥(V2 c.e) ≤ 16 := by
    calc Nat.card ↥(V2 c.e)
        = Nat.card ↥(V2 c.e ⊓ centralizer ({c.s.t} : Set G)) * Nat.card ↥R₂ := hcard₂
      _ ≤ 4 * 4 := Nat.mul_le_mul hctc hR₂c
      _ = 16 := by norm_num
  have hfinal : Nat.card ↥(V2 c.e) = 16 := le_antisymm hup hlow
  have ha_eq : Nat.card ↥(V2 c.e ⊓ centralizer ({c.s.t} : Set G)) = 4 := by
    refine le_antisymm hctc ?_
    have h1 : (4 : ℕ) * 4 ≤ Nat.card ↥(V2 c.e ⊓ centralizer ({c.s.t} : Set G)) * 4 := by
      calc (4 : ℕ) * 4 = 16 := by norm_num
        _ = Nat.card ↥(V2 c.e) := hfinal.symm
        _ = Nat.card ↥(V2 c.e ⊓ centralizer ({c.s.t} : Set G)) * Nat.card ↥R₂ := hcard₂
        _ ≤ Nat.card ↥(V2 c.e ⊓ centralizer ({c.s.t} : Set G)) * 4 :=
            Nat.mul_le_mul_left _ hR₂c
    exact Nat.le_of_mul_le_mul_right h1 (by norm_num)
  have hb_eq : Nat.card ↥R₂ = 4 := by
    have h1 : Nat.card ↥(V2 c.e ⊓ centralizer ({c.s.t} : Set G)) * Nat.card ↥R₂ = 16 := by
      rw [← hcard₂, hfinal]
    rw [ha_eq] at h1
    omega
  have hR₂eq : R₂ = cen c.s.fr.B := by
    refine Subgroup.eq_of_le_of_card_ge hR₂le ?_
    rw [y54_V_card hH, hb_eq]
  have hb0 : c.s.fr.b₁ * c.s.fr.b₂ ∈ R₂ := by
    rw [hR₂eq]
    exact (y56_v0 hH).1
  obtain ⟨u, huV2, hu⟩ := (hR₂mem (c.s.fr.b₁ * c.s.fr.b₂)).mp hb0
  exact ⟨by rw [hfinal]; norm_num, u, huV2, hu⟩

end CFSG.OddStandard.HigherRank.YamadaG23
