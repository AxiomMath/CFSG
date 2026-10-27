module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.GoldschmidtM22CaseBIface
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.GoldschmidtM22EndN5e
public import CFSG.Quasithin.H13.GoldschmidtM22CaseBAct
public import CFSG.Quasithin.H13.GoldschmidtM22CaseBSign
public section
namespace CFSG.Quasithin.H13.GM22
open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3 CFSG.Quasithin
variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]
structure BCtx_F4 (T M L V : Subgroup G) (g : G) (D : Subgroup G) where
  hl : M22LemmasG_F4
  h : Hyp6Sec2 G T M L V
  hk : EndN4Concl T L V g D
  P : PsiData T L V 3
  ρ : PermRho V
theorem nonempty_bCtx_F4 {T M L V : Subgroup G} {g : G} {D : Subgroup G} (hl : M22LemmasG_F4)
    (h : Hyp6Sec2 G T M L V) (hk : EndN4Concl T L V g D) : Nonempty (BCtx_F4 T M L V g D) := by
  obtain ⟨P⟩ := endN2_F4 hl.g64 hl.h621 hl.h622 hl.h626 hl.h629 hl.h6210 hl.h6211 hl.h6212 h
    hk.hZS
  obtain ⟨e⟩ := (hl.h622 G T M L V h).1
  obtain ⟨ρ⟩ := nonempty_permRho hk.normalizer_eq e
  exact ⟨⟨hl, h, hk, P, ρ⟩⟩
namespace BCtx_F4
variable {T M L V : Subgroup G} {g : G} {D : Subgroup G} (c : BCtx_F4 T M L V g D)
include c in
theorem hZ : Nat.card (quasithinOmegaOneCenter T) = 2 := (c.hl.h622 G T M L V c.h).2.1
include c in
theorem D_le_T : D ≤ T :=
  c.hk.kData.D_le_CHU.trans
    (c.P.CHU_le_T_F4 c.h c.hZ c.hl.h621 c.hl.h629 c.hl.h6210 c.hl.h6212)
include c in
theorem T_le_N : T ≤ Subgroup.normalizer (V : Set G) := c.h.toHyp611.T_le_normalizer
include c in
theorem L_le_N : L ≤ Subgroup.normalizer (V : Set G) := c.h.toHyp611.L_le_normalizer
include c in
theorem Q_le_T : Subgroup.centralizer (V : Set G) ≤ T := c.hk.centralizer_le_T
include c in
theorem N_le_normalizer_L : Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  rw [c.hk.normalizer_eq]
  exact sup_le Subgroup.le_normalizer (c.h.T_le.trans c.h.normal)
include c in
theorem L_perfect : IsOTwoPerfect L := c.h.faithful.2.1
include c in
theorem Q_two : ∀ q ∈ Subgroup.centralizer (V : Set G), ∃ k : ℕ, q ^ 2 ^ k = 1 := by
  intro q hq
  obtain ⟨k, hk⟩ := c.h.sylow.1 ⟨q, c.Q_le_T hq⟩
  exact ⟨k, congrArg Subtype.val hk⟩
include c in
theorem card_D : Nat.card D = 32 := c.hk.kData.extra.2.1
include c in
theorem D_inf_Q : D ⊓ Subgroup.centralizer (V : Set G) = V ⊓ CHU T L V :=
  le_antisymm (c.hk.kData.D_inf_centralizer_le_F4 c.h c.P c.hZ c.hl.h6210 c.hl.h6211)
    (le_inf (c.hk.kData.V0_le_D) (inf_le_left.trans (V_le_centralizer_V c.h)))
include c in
theorem card_D_inf_Q : Nat.card ↥(D ⊓ Subgroup.centralizer (V : Set G)) = 8 := by
  rw [c.D_inf_Q]
  exact KData.card_V0_F4 c.h c.hl.h6211
include c in
theorem D_comm_Q {p q : G} (hp : p ∈ D) (hq : q ∈ Subgroup.centralizer (V : Set G)) :
    p * q * p⁻¹ * q⁻¹ ∈ V := by
  obtain ⟨v, hv, e, he, rfl⟩ := c.hk.centralizer_eq_mul q hq
  have hpe : p * e = e * p :=
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp he).1 p hp
  have h1 : p * v * p⁻¹ ∈ V := conj_mem (c.T_le_N (c.D_le_T hp)) hv
  have : p * (v * e) * p⁻¹ * (v * e)⁻¹ = (p * v * p⁻¹) * v⁻¹ := by
    calc p * (v * e) * p⁻¹ * (v * e)⁻¹ = (p * v * p⁻¹) * (p * e * p⁻¹) * e⁻¹ * v⁻¹ := by group
      _ = (p * v * p⁻¹) * v⁻¹ := by rw [hpe]; group
  rw [this]
  exact V.mul_mem h1 (V.inv_mem hv)
include c in
theorem exists_odd : ∃ a ∈ D, a ∈ Subgroup.normalizer (V : Set G) ∧
    Equiv.Perm.sign (c.ρ a) = -1 ∧ a ^ 2 = 1 := by
  have hA := c.ρ.exists_eq_of_alternating c.L_le_N c.N_le_normalizer_L c.L_perfect
    c.h.natural.not_le_centralizer
  obtain ⟨a, haX, hs⟩ := c.ρ.exists_odd_of_not_le c.L_le_N hA c.hk.kData.case2.not_le
  obtain ⟨haVg, haN⟩ := Subgroup.mem_inf.mp haX
  have haD : a ∈ D := by
    have h1 : a ∈ conjSubgroup V g ⊓ CHU T L V := by
      rw [← c.hk.kData.conj_inf_normalizer_eq_F4 c.h c.P c.hZ c.hl.h6210 c.hl.h6211]
      exact haX
    exact c.hk.kData.V1_le_D h1
  refine ⟨a, haD, haN, hs, ?_⟩
  have hv : g * a * g⁻¹ ∈ V := mem_conjSubgroup_iff.mp haVg
  have h2 := c.h.toHyp611.isElemAbelian.2 _ hv
  rw [conj_pow] at h2
  simpa using h2
end BCtx_F4
end CFSG.Quasithin.H13.GM22
