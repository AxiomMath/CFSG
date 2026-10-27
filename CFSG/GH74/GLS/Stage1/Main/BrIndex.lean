module

public import CFSG.GH74.GLS.Stage1.Main.BrBaseTransport
public import CFSG.GH74.GLS.Stage1.Main.BrBaseModel
public import CFSG.GH74.GLS.Stage1.Main.BrModel

public section

namespace CFSG.GH74.GLS.Stage1.Main

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage1.Thm3.Sec4
  CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6 CFSG.GH74.GLS.Stage1.Thm3.Sec7
  CFSG.GH74.GLS.Stage1.Thm3.Sec8 CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.GH74.GLS.Stage1.Thm6.Prod
  CFSG.GH74.GLS.Stage2.Final
open scoped commutatorElement

theorem term7_data (hII : II4_4_4_center) (h41 : Prop4_1) {G : Type} [Group G] [Finite G] {z : G}
    {S : Subgroup G} {q : ℕ} {w : G} (hT : Term7Out G z S q w) :
    ∃ (Gs : Type) (_ : Group Gs) (_ : Finite Gs) (z' t' w' : Gs) (S' : Sylow 2 Gs)
      (E₁ E₂ : Subgroup Gs) (σ : ↥S ≃* ↥(S' : Subgroup Gs)),
      orderOf z' = 2 ∧ (center ↥(S' : Subgroup Gs)).map (S' : Subgroup Gs).subtype = zpowers z' ∧
      z' ∈ (S' : Subgroup Gs) ∧ (∀ x ∈ (S' : Subgroup Gs), x * z' = z' * x) ∧
      Dat410 q z' (S' : Subgroup Gs) t' w' E₁ E₂ ∧ (w' = 1 ↔ w = 1) ∧
      ∀ s : ↥S, ((s : G) ∈ LC z ↔ ((σ s : ↥(S' : Subgroup Gs)) : Gs) ∈ IVK.Ez z') := by
  obtain ⟨K₁, K₂, hs, hodd, h5, hK₁, hK₂, hT7⟩ := hT
  obtain ⟨Gs, iGs, fGs, z', t', w', S', E₁, E₂, hz'o, hcenS', hz'S', hz'c, hC, hD, hww⟩ :=
    exists_term7_model hodd h5 hK₁ hT7
  have hM := m4_of_std hII hs
  have hXC : K₁ ⊔ K₂ ⊔ S ≤ centralizer ({z} : Set G) :=
    sup_le (sup_le hM.K₁_le hM.K₂_le) hs.sylow.le
  have hcomps := comps_of_std4 hII h41 hs
  have hLB := LBar_eq_imgBar hII h41 hs
  have hSp : IsPGroup 2 ↥S := hs.sylow.isPGroup
  have hSOz : ∀ s ∈ S, s ∈ Oz z → s = 1 := fun s hs' hz =>
    eq_one_of_mem_pgroup_oddCore hSp hs' hz
  obtain ⟨ht, hc₁, hc₂, hne, hu₁, hu₂⟩ :=
    model_swap_data h5 hz'o hz'c hD.Ez_eq hD.E₂_eq hD.sl2 hD.inter_E hD.comm_E hD.t_mem hD.t_ord
  obtain ⟨σ, hσ⟩ := exists_sigma_of_compat hXC (fun H hH => isComponent_map_barOf hII hs hH) hcomps hLB hSp hSOz
    hD.Ez_eq hC hc₁ hc₂ hne
  exact ⟨Gs, iGs, fGs, z', t', w', S', E₁, E₂, σ, hz'o, hcenS', hz'S', hz'c, hD, hww, hσ⟩

theorem relIndex_eq_card_of_prod {Gs : Type} [Group Gs] {S' P T : Subgroup Gs} (hP : P ≤ S')
    (hT : T ≤ S') (hnorm : T ≤ normalizer (P : Set Gs)) (hprod : P ⊔ T = S')
    (hinf : P ⊓ T = ⊥) : P.relIndex S' = Nat.card ↥T := by
  have hPn : (P.subgroupOf S').Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hP, ← hprod]
    exact sup_le Subgroup.le_normalizer hnorm
  have hsup : P.subgroupOf S' ⊔ T.subgroupOf S' = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hP hT, hprod]
    exact Subgroup.subgroupOf_self S'
  have h1 := Subgroup.relIndex_sup_left (K := P.subgroupOf S') (H := T.subgroupOf S')
  rw [hsup, Subgroup.relIndex_top_right] at h1
  have h2 : (P.subgroupOf S').relIndex (T.subgroupOf S') = Nat.card ↥(T.subgroupOf S') := by
    have : P.subgroupOf S' ⊓ T.subgroupOf S' = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hx' : (x : Gs) ∈ P ⊓ T := ⟨hx.1, hx.2⟩
      rw [hinf, Subgroup.mem_bot] at hx'
      exact Subgroup.mem_bot.2 (Subtype.ext hx')
    rw [← inf_relIndex_right, this, Subgroup.relIndex_bot_left]
  have h3 : Nat.card ↥(T.subgroupOf S') = Nat.card ↥T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT).toEquiv
  rw [← h3, ← h2, ← h1]
  rfl

theorem card_sup_zpowers_le_four {Gs : Type} [Group Gs] {t w : Gs} (ht : t * t = 1) (hw : w * w = 1)
    (htw : t * w = w * t) : Nat.card ↥(zpowers t ⊔ zpowers w) ≤ 4 := by
  classical
  have hcomm : ∀ a ∈ zpowers t, ∀ b ∈ zpowers w, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact (Commute.zpow_zpow (show Commute t w from htw) k l).eq
  have hsub : ((zpowers t ⊔ zpowers w : Subgroup Gs) : Set Gs) ⊆
      (({1, t, w, t * w} : Finset Gs) : Set Gs) := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ :=
      CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic.mem_sup_of_commute' hcomm hx
    rcases eq_one_or_eq_of_mem_zpowers_sq ht ha with rfl | rfl <;>
      rcases eq_one_or_eq_of_mem_zpowers_sq hw hb with rfl | rfl <;> simp
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset] at h1
  have h2 : (({1, t, w, t * w} : Finset Gs)).card ≤ 4 := Finset.card_le_four
  have h3 : Nat.card ↥(zpowers t ⊔ zpowers w) =
      ((zpowers t ⊔ zpowers w : Subgroup Gs) : Set Gs).ncard := Nat.card_coe_set_eq _
  omega

theorem relIndex_RC_eq (hII : II4_4_4_center) (h41 : Prop4_1) {G : Type} [Group G] [Finite G]
    {z : G} {S : Subgroup G} {q : ℕ} {w : G} (hT : Term7Out G z S q w) :
    ((RC S z).relIndex S = 2 ∧ w = 1) ∨ ((RC S z).relIndex S ≤ 4 ∧ w ≠ 1) := by
  obtain ⟨Gs, iGs, fGs, z', t', w', S', E₁, E₂, σ, hz'o, hcen, hz'S, hz'c, hD, hww, hσ⟩ :=
    term7_data hII h41 hT
  set P : Subgroup Gs := (S' : Subgroup Gs) ⊓ IVK.Ez z' with hP
  set T : Subgroup Gs := zpowers t' ⊔ zpowers w' with hT'
  set ρ : ↥S →* Gs := (S' : Subgroup Gs).subtype.comp σ.toMonoidHom with hρ
  have hρinj : Function.Injective ρ := Subtype.coe_injective.comp σ.injective
  have hR : ((RC S z).subgroupOf S).map ρ = P := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxL : (x : G) ∈ LC z := hx.2
      exact ⟨(σ x).2, (hσ x).1 hxL⟩
    · rintro ⟨hyS, hyE⟩
      obtain ⟨x, hx⟩ := σ.surjective ⟨y, hyS⟩
      have hxy : ((σ x : ↥(S' : Subgroup Gs)) : Gs) = y := by rw [hx]
      refine ⟨x, ⟨x.2, (hσ x).2 (hxy ▸ hyE)⟩, ?_⟩
      exact hxy
  have hS : (⊤ : Subgroup ↥S).map ρ = (S' : Subgroup Gs) := by
    ext y
    constructor
    · rintro ⟨x, -, rfl⟩
      exact (σ x).2
    · intro hy
      obtain ⟨x, hx⟩ := σ.surjective ⟨y, hy⟩
      exact ⟨x, trivial, by simp [hρ, hx]⟩
  have hidx : (RC S z).relIndex S = P.relIndex (S' : Subgroup Gs) := by
    have := Subgroup.relIndex_map_map_of_injective ((RC S z).subgroupOf S) ⊤ hρinj
    rw [hR, hS, Subgroup.relIndex_top_right] at this
    rw [this]
    rfl
  have ht'S : t' ∈ (S' : Subgroup Gs) := hD.t_mem
  have hw'S : w' ∈ (S' : Subgroup Gs) := hD.w_mem
  have hTS : T ≤ (S' : Subgroup Gs) :=
    sup_le (Subgroup.zpowers_le.2 ht'S) (Subgroup.zpowers_le.2 hw'S)
  have hnorm : T ≤ normalizer (P : Set Gs) := hTS.trans (S_le_normalizer_inf hz'c)
  have hprod : P ⊔ T = (S' : Subgroup Gs) := by
    have := hD.prod
    rw [sup_assoc] at this
    exact this.symm
  have hinf : P ⊓ T = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have : x ∈ IVK.Ez z' ⊓ (zpowers t' ⊔ zpowers w') := ⟨hx.1.2, hx.2⟩
    rw [hD.inter] at this
    exact this
  have hcard := relIndex_eq_card_of_prod (inf_le_left : P ≤ (S' : Subgroup Gs)) hTS hnorm hprod hinf
  have hsq1 : t' * t' = 1 := by
    have := pow_orderOf_eq_one t'
    rwa [hD.t_ord, pow_two] at this
  have hsq2 : w' * w' = 1 := by
    rcases hD.w_ord with h | h
    · rw [h, mul_one]
    · have := pow_orderOf_eq_one w'
      rwa [h, pow_two] at this
  by_cases hw : w = 1
  · left
    refine ⟨?_, hw⟩
    have hw1 : w' = 1 := hww.2 hw
    rw [hidx, hcard]
    show Nat.card ↥(zpowers t' ⊔ zpowers w') = 2
    rw [hw1, Subgroup.zpowers_one_eq_bot, sup_bot_eq, Nat.card_zpowers, hD.t_ord]
  · right
    refine ⟨?_, hw⟩
    rw [hidx, hcard]
    exact card_sup_zpowers_le_four hsq1 hsq2 hD.comm

theorem psp4_index_thm (hII : II4_4_4_center) (h41 : Prop4_1) :
    ∀ (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G) (q : ℕ),
      Term7Out G z S q 1 → (RC S z).relIndex S = 2 := by
  intro G _ _ z S q hT
  rcases relIndex_RC_eq hII h41 hT with h | h
  · exact h.1
  · exact absurd rfl h.2

theorem l4nf_index_thm (hII : II4_4_4_center) (h41 : Prop4_1) :
    ∀ (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G) (q : ℕ) (w : G),
      Term7Out G z S q w → (RC S z).relIndex S ≤ 4 := by
  intro G _ _ z S q w hT
  rcases relIndex_RC_eq hII h41 hT with h | h
  · rw [h.1]
    norm_num
  · exact h.1

end CFSG.GH74.GLS.Stage1.Main
