module

public import CFSG.GH74.QTGen4.Leaves.Ru14775
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ASetting
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ACSk11
public import CFSG.GH74.QTGen4.Leaves.L14742Lie
public import CFSG.GH74.QTGen4.Leaves.L14742Aut
public import CFSG.Quasithin.H13.L32ACSk6

public section

namespace CFSG.GH74.QTGen4.Leaves.L14742

open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Open CFSG.GH74 CFSG.LieType.BorelTits
open scoped IsMulCommutative

theorem isElemAbelian_conjClosure_le {G : Type} [Group G] {T V L H : Subgroup G}
    (hF : HypF98 T V L (fsuV1 T V) V H)
    (hHle : H ≤ Subgroup.normalizer (fsuV1 T V : Set G))
    (hUab : IsMulCommutative ↥(fsuU T V)) : IsElemAbelian 2 (conjClosure V H) := by
  have hU : IsElemAbelian 2 (fsuU T V) :=
    CFSG.GH74.QTGen4.Ru14775.isElemAbelian_fsuU T V
      (fun v hv => by simpa using hF.elemAbelian.2 v hv) hUab
  have hle : conjClosure V H ≤ fsuU T V := conjClosure_mono le_rfl hHle
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => hU.2 x (hle hx)⟩
  have := hU.1.is_comm.comm ⟨a, hle a.2⟩ ⟨b, hle b.2⟩
  have h2 := congrArg Subtype.val this
  simpa using h2

theorem card_tilde_le_eight {G : Type} [Group G] [Finite G] (hG : Gen4 G) {T V L H : Subgroup G}
    (hF : HypF98 T V L (fsuV1 T V) V H)
    (hHle : H ≤ Subgroup.normalizer (fsuV1 T V : Set G))
    (hUab : IsMulCommutative ↥(fsuU T V)) :
    Nat.card (tildeOf (fsuV1 T V) (conjClosure V H)) ≤ 8 := by
  have hUH := isElemAbelian_conjClosure_le hF hHle hUab
  have h16 := SectionalTwoRankLE.card_le_of_elementary hG _ hUH
  have hV1 : fsuV1 T V ≤ conjClosure V H :=
    hF.V₁_le_Vp.trans ((le_conjClosure _ _))
  have hN : conjClosure V H ≤ Subgroup.normalizer (fsuV1 T V : Set G) := fun u hu =>
    hF.H_normalizes_V₁ (pCoreOf_le 2 H (hF.conjClosure_Vp_le_pCoreOf hu))
  have hrel := relIndex_secImg (A := Subgroup.normalizer (fsuV1 T V : Set G)) (B := fsuV1 T V)
    (T := fsuV1 T V) (H := conjClosure V H) le_rfl hV1 hN
  have hbot : secImg (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V) (fsuV1 T V) = ⊥ :=
    tildeOf_eq_bot_of_le le_rfl
  rw [hbot, Subgroup.relIndex_bot_left] at hrel
  have hmul := Subgroup.relIndex_mul_card (H := fsuV1 T V) (K := conjClosure V H)
  rw [inf_eq_left.2 hV1, hF.card_V₁] at hmul
  change Nat.card (tildeOf (fsuV1 T V) (conjClosure V H)) ≤ 8
  unfold tildeOf
  omega

theorem card_cStar_quot_dvd {G : Type} [Group G] [Finite G] {T V L H K : Subgroup G}
    (hF : HypF98 T V L (fsuV1 T V) V H) (hKH : K ≤ H) :
    Nat.card ((↥K ⧸ (pCoreOf 2 K).subgroupOf K) ⧸ Subgroup.center (↥K ⧸ (pCoreOf 2 K).subgroupOf K)) ∣
      Nat.card (MulAut ↥(tildeOf (fsuV1 T V) (conjClosure V H))) := by
  have hcard := HypF91.card_autOn_tilde hF.toHypF91 (B := K) hKH
  have h1 : Nat.card (autOn (tildeOf (fsuV1 T V) K) (tildeOf (fsuV1 T V) (conjClosure V H))) ∣
      Nat.card (MulAut ↥(tildeOf (fsuV1 T V) (conjClosure V H))) :=
    Subgroup.card_subgroup_dvd_card _
  rw [hcard] at h1
  have hN : K ⊓ pCoreOf 2 H ≤ pCoreOf 2 K := by
    refine le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
      ((pCoreOf_isPGroup (r := 2) H).of_injective _ (Subgroup.inclusion_injective (inf_le_right : K ⊓ pCoreOf 2 H ≤ pCoreOf 2 H)))
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hkH : k ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) := le_normalizer_pCoreOf 2 H (hKH hk)
    have hkK : k ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer hk
    rw [Subgroup.mem_normalizer_iff] at hkH hkK
    simp only [Subgroup.mem_inf, hkH x, hkK x]
  have h2 : ((pCoreOf 2 K).subgroupOf K).index ∣ ((K ⊓ pCoreOf 2 H).subgroupOf K).index :=
    Subgroup.index_dvd_of_le (fun x (hx : x ∈ (K ⊓ pCoreOf 2 H).subgroupOf K) => hN hx)
  have h3 : Nat.card ((↥K ⧸ (pCoreOf 2 K).subgroupOf K) ⧸ Subgroup.center (↥K ⧸ (pCoreOf 2 K).subgroupOf K)) ∣ Nat.card (↥K ⧸ (pCoreOf 2 K).subgroupOf K) :=
    Subgroup.card_quotient_dvd_card _
  have h4 : Nat.card (↥K ⧸ (pCoreOf 2 K).subgroupOf K) = ((pCoreOf 2 K).subgroupOf K).index := rfl
  exact h3.trans (h4 ▸ h2.trans h1)

open CFSG.Quasithin in
theorem false_of_setting147_lieChar2
    {G : Type} [Group G] [Finite G] (hG : Gen4 G)
    {T V L H K : Subgroup G} (hF : HypF98 T V L (fsuV1 T V) V H)
    (hHle : H ≤ Subgroup.normalizer (fsuV1 T V : Set G))
    (hUab : IsMulCommutative ↥(fsuU T V)) (hKH : K ≤ H) {n : ℕ} (hn : 2 ≤ n)
    (hLie : A315.IsLieChar2 n ((↥K ⧸ (pCoreOf 2 K).subgroupOf K) ⧸
      Subgroup.center (↥K ⧸ (pCoreOf 2 K).subgroupOf K))) : False := by
  have h8 := card_tilde_le_eight hG hF hHle hUab
  have hel := HypF91.isElemAbelian_tilde hF.toHypF91
  have hAut := card_mulAut_dvd_168
    (W := ↥(tildeOf (fsuV1 T V) (conjClosure V H)))
    (fun a b => hel.1.is_comm.comm a b)
    (fun a => Subtype.ext (hel.2 a a.2)) h8
  exact not_isLieChar2_of_card_dvd_168 hn hLie ((card_cStar_quot_dvd hF hKH).trans hAut)

open CFSG.Quasithin.H13 CFSG.Quasithin.H13.L32A.C in
theorem lemma14_7_42_F4_holds
    
    (h13322 : Stmt13_3_2_two_F4) (hMod : StmtL32NModule_F4) (h1222 : Stmt12_2_2_F4) :
    Lemma14_7_42_F4 := by
  intro G _ _ T L V H S K hK _ n hn hLie _
  exact (false_of_setting147_lieChar2 CFSG.GH74.QTGen4.Finite4.gen4
    (S.hypF98_F4 h13322 hMod h1222) S.hz.2.1 S.hyp.abelian (fun x hx => le_of_mem_cComp hK hx)
    (by omega) hLie).elim

end CFSG.GH74.QTGen4.Leaves.L14742

end
