module

public import CFSG.CGT.PushingUpLit.A78L3.CentL
public import CFSG.CGT.PushingUpLit.A78L3.Swap
public import CFSG.CGT.PushingUpLit.A78T2.Cut
public import CFSG.CGT.PushingUpLit.A78L3.Tori

public section

namespace CFSG.CGT.PushingUpLit.A78L3

open CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.A78 CFSG.CGT.PushingUpLit.A78Sp4
open CFSG.CGT.PushingUpLit.A78T2 (T2Side T2Field T2Loc T2Base)
open CFSG.ABGLocalTools

namespace L3Side

variable {G : Type} [Group G] [Finite G] {L V W T : Subgroup G} {e : ℕ}

theorem t2Side (h : L3Side G L V W T e)
    (hnl : Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (L : Set G))
    (hsyl : IsSylowOf 2 T (Subgroup.normalizer (V : Set G))) :
    T2Side G L V (V ⊓ W) (V ⊔ W) T (Subgroup.normalizer (V : Set G)) e := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨D⟩ := h.nat
  have hLM : L ≤ Subgroup.normalizer (V : Set G) := D.le_normalizer
  exact
    { V_le_L := h.V_le_L
      L_le_M := hLM
      normal_L := (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).2 hnl
      M_eq := rfl
      J_le_L := h.J_le_L
      T_le_M := h.T_le_V
      sylow_T := hsyl
      T_inf_L := h.sylowJ.eq_of_le (le_inf h.J_le_T h.J_le_L) inf_le_right
        (h.pT.to_le inf_le_left)
      trans := fun _ hv hv1 _ hw hw1 => D.exists_conj hv hv1 hw hw1
      cent_L := fun _ hz hz1 => h.cent_L hz hz1 }

end L3Side

namespace L3Pair

variable {G : Type} [Group G] [Finite G] {L₁ L₂ V W T : Subgroup G} {e : ℕ}
  (P : L3Pair G L₁ L₂ V W T e)

include P in
theorem t2Field {S : Subgroup G} {M M₂ : Subgroup G}
    (base : T2Base G V W (V ⊓ W) (V ⊔ W) T S M M₂ e) :
    T2Field G L₁ L₂ V W (V ⊓ W) (V ⊔ W) T S e := by
  obtain ⟨D₁⟩ := P.side₁.nat
  obtain ⟨D₂⟩ := P.side₂.nat
  obtain ⟨fr⟩ := P.side₁.exists_frame D₁
  have hJ : W ⊔ V = V ⊔ W := sup_comm W V
  have hZ : W ⊓ V = V ⊓ W := inf_comm W V
  have hJ' : ∀ {x : G}, x ∉ V ⊔ W → x ∉ W ⊔ V := fun hx => by rwa [hJ]
  exact
    { fixZ := fun x hx hxJ => ⟨P.side₁.fixZ D₁ hx hxJ, by
        have := P.side₂.fixZ D₂ hx (hJ' hxJ)
        rwa [hZ] at this⟩
      card_CJ := fun a ha haJ haa => by
        by_cases haT : a ∈ T
        · have h1 := P.side₁.card_CV D₁ haT haJ haa
          rw [← h1]
          exact Subgroup.card_le_of_le fun v hv => ⟨Subgroup.mem_sup_left hv.1, hv.2⟩
        · obtain ⟨hsV, hsW⟩ := base.swap a ha haT
          exact P.card_CJ_swap fr hsV hsW haa
      exists_inv := fun hTJ => P.side₁.exists_involution D₁ hTJ
      even_e := fun hTJ => by
        obtain ⟨f, hf, hfJ, hff⟩ := P.side₁.exists_involution D₁ hTJ
        exact P.side₁.even_of_involution D₁ hf hfJ hff
      inv_conj := fun f hf hfJ hff x hx hxJ hxx => P.side₁.inv_conj D₁ hf hfJ hff hx hxJ hxx
      card_CJf := fun f hf hfJ hff => P.side₁.card_CJf D₁ hf hfJ hff
      cent_L := fun f hf hfJ hff => P.side₁.centL D₁ hf hfJ hff
      cent_L₂ := fun f hf hfJ hff => by
        have := P.side₂.centL D₂ hf (hJ' hfJ) hff
        rwa [hZ] at this
      types := fun a ha haT haa => by
        obtain ⟨hsV, hsW⟩ := base.swap a ha haT
        exact P.types_swap fr hsV hsW haa }

end L3Pair

theorem t2FromCfg : A78T2.T2FromCfg := by
  intro G _ _ L₁ L₂ T e cfg hns hZ he3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have P := cfg.l3Pair hZ
  obtain ⟨S, hS, hTS⟩ := exists_isSylowOf_ge P.side₁.pT (le_top : T ≤ ⊤)
  have hsw : ∃ s ∈ S, s ∉ T := by
    by_contra hcon
    push Not at hcon
    apply hns
    rw [le_antisymm hTS hcon]
    exact hS
  have base := P.t2Base hS hTS hsw
  obtain ⟨D₁⟩ := P.side₁.nat
  obtain ⟨fr⟩ := P.side₁.exists_frame D₁
  have hs₂ := P.side₂.t2Side cfg.hyg.nl₂ cfg.hyg.sylow₂
  rw [inf_comm (oTwoIn (L₂ ⊔ T)) (oTwoIn (L₁ ⊔ T)),
    sup_comm (oTwoIn (L₂ ⊔ T)) (oTwoIn (L₁ ⊔ T))] at hs₂
  exact ⟨S, _, _,
    { three_le := he3
      simple := cfg.simple
      charTwo := cfg.charTwo
      base := base
      side₁ := P.side₁.t2Side cfg.hyg.nl₁ cfg.hyg.sylow₁
      side₂ := hs₂
      field := P.t2Field base
      coords := ⟨fr.a, fr.b, fr.c, fr.heis, P.tori fr⟩ }⟩

end CFSG.CGT.PushingUpLit.A78L3
