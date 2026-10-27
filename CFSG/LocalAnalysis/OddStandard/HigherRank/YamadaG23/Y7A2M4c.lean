module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A2Ab4
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A2M4a
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A2M4b

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7a_card_M4_le (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    (h71 : c.Fact71) : Nat.card ↥(M4 c.e) ≤ 64 := by
  have hM46 : M4 c.e ≤ M6 c.e := h71.2.2.2.2
  have hcent : ∀ v ∈ M4 c.e, ∀ x ∈ c.s.fr.E, v * x = x * v := fun v hv x hx =>
    y7a_C4_cent_E c hH v (Subgroup.mem_inf.mp hv).1 x hx
  obtain ⟨R, hRW, -, hcard⟩ := y7a_comm_range (V := M4 c.e) (W := c.s.fr.E) (t := c.s.t)
    (y56_E_comm hH) (fun w hw v hv => hcent v hv w hw)
    (fun v hv => y7a_comm_t_E c hH hF (hM46 hv) (hcent v hv))
  have hE8 : Nat.card ↥c.s.fr.E = 8 := by
    have := (y56_E_isE3 hH).2
    norm_num at this
    exact this
  have hR : Nat.card ↥R ≤ 8 := (Subgroup.card_le_of_le hRW).trans hE8.le
  have hker : M4 c.e ⊓ centralizer ({c.s.t} : Set G) ≤ c.s.fr.E := by
    intro x hx
    obtain ⟨hx4, hxt⟩ := Subgroup.mem_inf.mp hx
    have hxA : x ∈ c.s.fr.A := by
      rw [← h71.2.1.2.1]
      exact Subgroup.mem_inf.mpr ⟨hxt, hM46 hx4⟩
    rw [← y56_centIn_L_E hH]
    exact Subgroup.mem_inf.mpr ⟨s3_A_le_L c.s hxA,
      Subgroup.mem_centralizer_iff.mpr fun e he => (hcent x hx4 e he).symm⟩
  have hK : Nat.card ↥(M4 c.e ⊓ centralizer ({c.s.t} : Set G)) ≤ 8 :=
    (Subgroup.card_le_of_le hker).trans hE8.le
  rw [hcard]
  calc _ ≤ 8 * 8 := Nat.mul_le_mul hK hR
    _ = 64 := by norm_num

theorem y7a_M4_elemAbelian (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    (h71 : c.Fact71) : IsElemAbelian 2 (M4 c.e) := by
  obtain ⟨k, hk, hk3, hfpf⟩ := y7a_exists_k_E hH
  obtain ⟨hkA, hkE⟩ := Subgroup.mem_inf.mp hk
  have hM4pg : IsPGroup 2 (M4 c.e) :=
    (y7a_C6_isPGroup c).to_le (inf_le_left.trans (y7a_C4_le_C6 c hH hF))
  have hUM : c.s.fr.E ⊔ V2 c.e ≤ M4 c.e := y7a_U_le_M4 c hH
  have hnotU := y7a_k_not_norm_U c hH hF h71 hkA hkE hfpf
  have hkM := y7a_k_norm_M4 c hH hkA hkE
  have hcardU := y7a_card_U c hH hF h71
  have hcardM := y7a_card_M4_le c hH hF h71
  have hdvd : Nat.card ↥(c.s.fr.E ⊔ V2 c.e) ∣ Nat.card ↥(M4 c.e) :=
    Subgroup.card_dvd_of_le hUM
  have hne : Nat.card ↥(M4 c.e) ≠ 32 := by
    intro h32
    have hUeq : c.s.fr.E ⊔ V2 c.e = M4 c.e :=
      Subgroup.eq_of_le_of_card_ge hUM (by omega)
    apply hnotU
    intro x hx
    rw [hUeq] at hx ⊢
    exact hkM x hx
  have h64 : Nat.card ↥(M4 c.e) = 64 := by
    rw [hcardU] at hdvd
    obtain ⟨n, hn⟩ := hdvd
    have hpos : 0 < Nat.card ↥(M4 c.e) := Nat.card_pos
    omega
  have hidx : (c.s.fr.E ⊔ V2 c.e).relIndex (M4 c.e) = 2 := by
    have h := Subgroup.relIndex_mul_card (H := c.s.fr.E ⊔ V2 c.e) (K := M4 c.e)
    rw [inf_of_le_left hUM, hcardU, h64] at h
    omega
  exact y7a_elemAbelian_of_k hM4pg hUM (y7a_U_elemAbelian c hH hF h71) hidx hk3 hkM hnotU

end CFSG.OddStandard.HigherRank.YamadaG23
