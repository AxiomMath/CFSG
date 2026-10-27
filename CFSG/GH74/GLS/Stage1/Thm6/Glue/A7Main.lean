module

public import CFSG.GH74.GLS.Stage1.Thm6.Glue.A7Cbar
public import CFSG.GH74.GLS.Stage1.Thm6.Setup

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Glue

open Subgroup CFSG CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12
  CFSG.GH74.GLS.Stage1.Thm6.Sec12b CFSG.GH74.GLS.Stage1.Thm6.Glue.A7

local notation "S₇" => Equiv.Perm (Fin 7)
local notation "A₇" => alternatingGroup (Fin 7)

section Generic

variable {G : Type} [Group G] {x : G}

theorem card_sup_zpowers_A7 {V : Subgroup G} (hx : x * x = 1) (hxV : x ∉ V)
    (hcomm : ∀ v ∈ V, v * x = x * v) : Nat.card (V ⊔ Subgroup.zpowers x : Subgroup G) =
      2 * Nat.card V := by
  have hpow : ∀ k : ℤ, x ^ k = 1 ∨ x ^ k = x := fun k => by
    rcases A7.zpowers_cases hx (Subgroup.mem_zpowers_iff.2 ⟨k, rfl⟩) with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hcommV : ∀ a ∈ V, ∀ b ∈ Subgroup.zpowers x, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact (Commute.zpow_right (show Commute a x from hcomm a ha) k).eq
  have hrel : V.relIndex (V ⊔ Subgroup.zpowers x) = 2 := by
    have hdvd : V.relIndex (V ⊔ Subgroup.zpowers x) ∣ 2 := by
      rw [Subgroup.relIndex_dvd_two_iff]
      refine ⟨x, mem_sup_right (Subgroup.mem_zpowers x), ?_⟩
      intro b hb
      obtain ⟨v, hv, c, hc, rfl⟩ := (A7.mem_sup_iff_of_comm hcommV).1 hb
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
      rcases hpow k with h1 | h1
      · right; rw [h1, mul_one]; exact hv
      · left
        have : v * x * x = v := by rw [mul_assoc, hx, mul_one]
        rw [h1, this]; exact hv
    have hne : V.relIndex (V ⊔ Subgroup.zpowers x) ≠ 1 := by
      intro h1
      rw [Subgroup.relIndex_eq_one] at h1
      exact hxV (h1 (mem_sup_right (Subgroup.mem_zpowers x)))
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h1
    · exact absurd h1 hne
    · exact h1
  have := Subgroup.relIndex_mul_card V (V ⊔ Subgroup.zpowers x)
  rw [inf_of_le_left le_sup_left, hrel] at this
  omega

theorem ip_P_closed_A7 (x : G) (Kb : Subgroup (CentralizerBar x)) [Kb.Normal] (T : Subgroup G) :
    IP_P_closed x T (Pg x Kb T) := by
  intro c hc v hv hcv
  have hvC : v ∈ Cx x := ((mem_Kg x Kb).1 hv.2).1
  refine ⟨hcv, (mem_Kg x Kb).2 ⟨mul_mem (mul_mem hc hvC) (inv_mem hc), ?_⟩⟩
  rw [pr_mul x (mul_mem hc hvC) (inv_mem hc), pr_mul x hc hvC, pr_inv x hc]
  exact (inferInstance : Kb.Normal).conj_mem _ ((mem_Kg x Kb).1 hv.2).2 _

end Generic

variable {G : Type} [Group G] [Finite G] {x : G} {Kb : Subgroup (CentralizerBar x)} [Kb.Normal]

theorem three_le_pRank_C_A7 (hIVK : IVKA7Facts) (hx : x * x = 1) (hx1 : x ≠ 1)
    (hm : IsA7Model ↥Kb) : 3 ≤ pRank 2 ↥(Cx x) := by
  obtain ⟨eK⟩ := hm
  have hbot : IsPGroup 2 ↥(⊥ : Subgroup G) := IsPGroup.of_card (n := 0) (by simp)
  obtain ⟨T, hT, -⟩ := exists_sylow2_ge hbot (bot_le : (⊥ : Subgroup G) ≤ Cx x)
  obtain ⟨Tp, f, h⟩ := exists_abs hIVK eK hT
  obtain ⟨V, hVP, hV⟩ := h.P_four
  have hxT : x ∈ T := x_mem_of_sylow x hT hx hx1
  have hxQ : x ∈ Qg x Kb T :=
    (h.mem_Q x).2 ⟨hxT, (rho_eq_one_iff x Kb eK x).2 (phig_x_eq_one x Kb)⟩
  have hxV : x ∉ V := by
    intro hxV
    exact hx1 (h.P_inj x (hVP hxV) 1 (Pg x Kb T).one_mem (by rw [h.rho_Q hxQ, h.rho_one]))
  have hVC : V ≤ Cx x := fun g hg => ((mem_Kg x Kb).1 (hVP hg).2).1
  have hcomm : ∀ v ∈ V, v * x = x * v := fun v hv => (mem_Cx x).1 (hVC hv)
  have hxC : x ∈ Cx x := x_mem_Cx x
  have hcommV : ∀ a ∈ V, ∀ b ∈ Subgroup.zpowers x, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact (Commute.zpow_right (show Commute a x from hcomm a ha) k).eq
  have hEC : V ⊔ Subgroup.zpowers x ≤ Cx x := sup_le hVC (Subgroup.zpowers_le.2 hxC)
  have hE : IsElemAb2 (V ⊔ Subgroup.zpowers x) := by
    intro g hg
    obtain ⟨a, ha, b, hb, rfl⟩ := (A7.mem_sup_iff_of_comm hcommV).1 hg
    have hbb := A7.zpowers_sq_one hx b hb
    have haa := (hV.1 a ha).1
    have hab := hcommV a ha b hb
    refine ⟨?_, ?_⟩
    · calc a * b * (a * b) = a * (b * a) * b := by simp only [mul_assoc]
        _ = a * (a * b) * b := by rw [← hab]
        _ = (a * a) * (b * b) := by simp only [mul_assoc]
        _ = 1 := by rw [haa, hbb, mul_one]
    · intro g' hg'
      obtain ⟨a', ha', b', hb', rfl⟩ := (A7.mem_sup_iff_of_comm hcommV).1 hg'
      have h1 : a * a' = a' * a := (hV.1 a ha).2 a' ha'
      have h2 : b * b' = b' * b := by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
        obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb'
        rw [← zpow_add, ← zpow_add, add_comm]
      have h3 : a * b' = b' * a := hcommV a ha b' hb'
      have h4 : a' * b = b * a' := hcommV a' ha' b hb
      calc a * b * (a' * b') = a * (b * a') * b' := by simp only [mul_assoc]
        _ = a * (a' * b) * b' := by rw [h4]
        _ = (a * a') * (b * b') := by simp only [mul_assoc]
        _ = (a' * a) * (b' * b) := by rw [h1, h2]
        _ = a' * (a * b') * b := by simp only [mul_assoc]
        _ = a' * (b' * a) * b := by rw [h3]
        _ = a' * b' * (a * b) := by simp only [mul_assoc]
  have hcard : Nat.card (V ⊔ Subgroup.zpowers x : Subgroup G) = 2 ^ 3 := by
    rw [card_sup_zpowers_A7 hx hxV hcomm, hV.2]; norm_num
  have hEA : ∀ a ∈ (V ⊔ Subgroup.zpowers x).subgroupOf (Cx x),
      a * a = 1 ∧ ∀ b ∈ (V ⊔ Subgroup.zpowers x).subgroupOf (Cx x), a * b = b * a :=
    fun a ha => ⟨Subtype.ext ((hE _ ha).1), fun b hb => Subtype.ext ((hE _ ha).2 _ hb)⟩
  have hcard' : Nat.card ((V ⊔ Subgroup.zpowers x).subgroupOf (Cx x)) = 2 ^ 3 := by
    rw [A7.card_subgroupOf hEC]; exact hcard
  exact le_pRank_of_card (isElementaryAbelian_of_isEA hEA) hcard'

theorem hbase_of_abs {eK : ↥Kb ≃* A₇} {T : Subgroup G} {Tp : Subgroup S₇} {f : S₇}
    (h : Abs (Cx x) T (Pg x Kb T) (Qg x Kb T) (Rd7 x Kb T) (rho x Kb eK) Tp f)
    (hT : IsSylow2In T (Cx x)) {S : Subgroup G} (hsimple : IsSimpleGroup G)
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hx : x * x = 1) (hx1 : x ≠ 1) (hS : IsSylow2In S ⊤)
    (hTS : T = S ⊓ Cx x) (hrank : pRank 2 ↥(Cx x) = 3) (hns : ¬ Group.IsSolvable ↥(Cx x)) :
    HBase G x S T (Pg x Kb T) (Qg x Kb T) (Rd7 x Kb T) (Qg x Kb T) where
  simple := hsimple
  nonabelian := hnonab
  x_sq := hx
  x_ne_one := hx1
  S_sylow := hS
  T_sylow := hT
  T_le_S := hTS ▸ inf_le_left
  extremal := fun s hs hsx => by
    rw [hTS]
    exact ⟨hs, (mem_Cx x).2 hsx⟩
  rank_le := rank2Le_of_pRank_le x hrank.le
  rank_ge := exists_elemAb_eight x hrank
  P_normal := Pg_normal x Kb hT.1
  Q_normal := Qg_normal x Kb hT.1
  Rd_normal := ⟨h.Rd_le_T, fun t ht d hd => by
    have hdT := h.Rd_le_T hd
    have hdA := ((h.mem_Rd d).1 hd).2
    have htC := h.T_le_C ht
    have hdC := h.T_le_C hdT
    refine (h.mem_Rd _).2 ⟨T.mul_mem (T.mul_mem ht hdT) (T.inv_mem ht), ?_⟩
    rw [h.rho_mul (t * d) (mul_mem htC hdC) t⁻¹ (inv_mem htC), h.rho_mul t htC d hdC,
      h.rho_inv t htC]
    exact (inferInstance : (alternatingGroup (Fin 7)).Normal).conj_mem _ hdA _⟩
  PQ_disjoint := Pg_inf_Qg x Kb (conj_injective eK) hT
  PQ_comm := Pg_comm_Qg x Kb hT
  x_mem_Q := (h.mem_Q x).2 ⟨x_mem_of_sylow x hT hx hx1,
    (rho_eq_one_iff x Kb eK x).2 (phig_x_eq_one x Kb)⟩
  R_le_Rd := h.Rd_eq.ge
  R_index_le_two := by rw [h.Rd_eq, Subgroup.relIndex_self]; norm_num
  F_le_T := fun g hg => hg.1
  Q_le_F := le_rfl
  F_inf_Rd := inf_eq_left.2 h.Q_le_Rd
  nonsolv := hns

theorem kfacts_A7 (hIVK : IVKA7Facts) (c : Conf12B G x Kb) (hm : IsA7Model ↥Kb)
    {S U : Subgroup G} (hS : IsSylow2In S ⊤) (hU : IsFour U) (hUn : NormalIn U S)
    (hUC : U ≤ Cx x) (hT : IsSylow2In (S ⊓ Cx x) (Cx x)) :
    KFacts x S (S ⊓ Cx x) (Pg x Kb (S ⊓ Cx x)) (Qg x Kb (S ⊓ Cx x)) (Rd7 x Kb (S ⊓ Cx x))
      (Qg x Kb (S ⊓ Cx x)) U := by
  obtain ⟨eK⟩ := hm
  obtain ⟨Tp, f, h⟩ := exists_abs hIVK eK hT
  have hx2 : x * x = 1 := by
    rw [← pow_two]; exact orderOf_dvd_iff_pow_eq_one.1 (by rw [c.x_order])
  have hx1 : x ≠ 1 := fun h => by
    have := c.x_order
    rw [h, orderOf_one] at this
    omega
  have hrk : Rank2Le (Cx x) 3 := rank2Le_of_pRank_le x c.rankC.le
  have hxT : x ∈ S ⊓ Cx x := x_mem_of_sylow x hT hx2 hx1
  have hxC : ∀ c ∈ Cx x, c * x = x * c := fun c hc => (mem_Cx x).1 hc
  exact
    { base := hbase_of_abs h hT c.simple c.nonabelian hx2 hx1 hS rfl c.rankC c.not_solvable
      hu := ⟨hU, hUn, fun u hu => ⟨hUn.1 hu, hUC hu⟩⟩
      P_four := h.P_four
      outer := ip_outer hIVK hT h hx2 hx1
      cent_four := h.cent_four
      Rd_factor := h.Rd_factor
      Rd_cyclic := h.Rd_cyclic
      P_trans := h.P_trans
      cent_Rd := h.cent_Rd
      cent_P_exp := h.cent_P_exp
      f3 := ip_f3 hIVK hT h
      P_closed := ip_P_closed_A7 x Kb _
      P_conj := fun z hz => ip_P_conj hIVK h hz
      z_V := fun z hz => h.z_V hz
      E8_two := by
        intro hQ hΩ _
        exact h.E8_two hQ hΩ hrk hx2 hx1 hxC hxT
      Rd_dihedral := fun hQ => h.Rd_dihedral hQ hxC
      Rd_fuse := fun hQ => h.Rd_fuse hQ
      T_normal := fun z hz hQ hΩ => h.T_normal hz hQ hΩ hx2 hxT hxC }

end CFSG.GH74.GLS.Stage1.Thm6.Glue
