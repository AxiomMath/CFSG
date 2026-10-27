module

public import CFSG.GH74.GLS.Stage2.Final.L26.Main
public import CFSG.GH74.GLS.Stage2.Final.L26.G2Basic
public import CFSG.GH74.GLS.Stage2.Final.L26.G2Three
public import CFSG.GH74.GLS.Stage2.Final.L26.G2Lift

public section

namespace CFSG.GH74.GLS.Stage2.Final.L26

open Subgroup CFSG CFSG.LocalCores CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Final.Thm4
open scoped commutatorElement

section Outer

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S : Subgroup G}

theorem g2_outer (hctx : Stage2Ctx G z k S) (hbase : Stage1Base G z S)
    (hone : ∀ u v : G, orderOf u = 2 → orderOf v = 2 → IsConj u v)
    {r₁ r₂ : ℕ} {L₁ L₂ : Subgroup (CentralizerBar z)} (hsh : G2Shape z S r₁ r₂ L₁ L₂) :
    ∃ (t : G) (htS : t ∈ S), IsConj z t ∧
      toBar z ⟨t, hctx.S_le_Cen htS⟩ * toBar z ⟨t, hctx.S_le_Cen htS⟩ = 1 ∧
      toBar z ⟨t, hctx.S_le_Cen htS⟩ ∈ SBar S z ∧
      (¬ ∃ a ∈ L₁, ∃ c ∈ centralizer (L₁ : Set (CentralizerBar z)),
        toBar z ⟨t, hctx.S_le_Cen htS⟩ = a * c) ∧
      (¬ ∃ a ∈ L₂, ∃ c ∈ centralizer (L₂ : Set (CentralizerBar z)),
        toBar z ⟨t, hctx.S_le_Cen htS⟩ = a * c) := by
  obtain ⟨hodd₁, hodd₂, hg₁, hprod, hm₁, hm₂, -, -, -, hidx, hind₁, hind₂⟩ := hsh
  obtain ⟨hsup, hcomm, hcard⟩ := hprod
  have hz2 : orderOf z = 2 := hctx.orderOf_z
  have hne : RC S z ≠ S := by
    intro h
    rw [h, Subgroup.relIndex_self] at hidx
    omega
  obtain ⟨t, htS, htR, ht2⟩ := hbase.inv_out hne
  have htc : IsConj z t := hone z t hz2 ht2
  have htC : t ∈ Cen z := hctx.S_le_Cen htS
  obtain ⟨y, hy⟩ : ∃ y : CentralizerBar z, y = toBar z ⟨t, htC⟩ := ⟨_, rfl⟩
  have hy2 : y * y = 1 := by
    rw [hy, ← map_mul]
    have h1 : t * t = 1 := by
      have := pow_orderOf_eq_one t
      rwa [ht2, pow_two] at this
    have : (⟨t, htC⟩ : ↥(Cen z)) * ⟨t, htC⟩ = 1 := Subtype.ext h1
    rw [this, map_one]
  have hyS : y ∈ SBar S z := ⟨⟨t, htC⟩, Subgroup.mem_subgroupOf.mpr htS, hy.symm⟩
  have hSR : ∀ s ∈ SBar S z, s ∈ barOf z (RC S z) ∨ y⁻¹ * s ∈ barOf z (RC S z) := by
    rintro s ⟨⟨s', hs'C⟩, hs'S, rfl⟩
    have hs'S' : s' ∈ S := Subgroup.mem_subgroupOf.mp hs'S
    by_cases hsR : s' ∈ RC S z
    · left
      exact ⟨⟨s', hs'C⟩, Subgroup.mem_subgroupOf.mpr hsR, rfl⟩
    · right
      have hidx' : ((RC S z).subgroupOf S).index = 2 := hidx
      have h2 : (⟨t, htS⟩ : ↥S)⁻¹ ∉ (RC S z).subgroupOf S := by
        rw [inv_mem_iff]
        exact fun h => htR (Subgroup.mem_subgroupOf.mp h)
      have h3 : (⟨s', hs'S'⟩ : ↥S) ∉ (RC S z).subgroupOf S := fun h =>
        hsR (Subgroup.mem_subgroupOf.mp h)
      have h1 : (⟨t, htS⟩ : ↥S)⁻¹ * ⟨s', hs'S'⟩ ∈ (RC S z).subgroupOf S := by
        rw [Subgroup.mul_mem_iff_of_index_two hidx']
        exact ⟨fun h => absurd h h2, fun h => absurd h h3⟩
      have h1' : t⁻¹ * s' ∈ RC S z := Subgroup.mem_subgroupOf.mp h1
      refine ⟨⟨t⁻¹ * s', (Cen z).mul_mem ((Cen z).inv_mem htC) hs'C⟩,
        Subgroup.mem_subgroupOf.mpr h1', ?_⟩
      rw [hy, ← map_inv, ← map_mul]
      rfl
  have hRL : barOf z (RC S z) ≤ L₁ ⊔ L₂ := by
    rw [hsup]
    exact barOf_le_LBar (inf_le_right : S ⊓ LC z ≤ LC z)
  have hcomm' : ∀ a ∈ L₂, ∀ b ∈ L₁, a * b = b * a := fun a ha b hb => (hcomm b hb a ha).symm
  have hR₁ : ∀ s ∈ barOf z (RC S z), ∃ a ∈ L₁, ∃ c ∈ centralizer (L₁ : Set (CentralizerBar z)),
      s = a * c := by
    intro s hs
    obtain ⟨a, ha, b, hb, rfl⟩ :=
      CFSG.GH74.GLS.Stage2.Final.L26.exists_mul_of_mem_sup_of_commute hcomm (hRL hs)
    exact ⟨a, ha, b, Subgroup.mem_centralizer_iff.mpr fun g hg => hcomm g hg b hb, rfl⟩
  have hR₂ : ∀ s ∈ barOf z (RC S z), ∃ a ∈ L₂, ∃ c ∈ centralizer (L₂ : Set (CentralizerBar z)),
      s = a * c := by
    intro s hs
    obtain ⟨a, ha, b, hb, rfl⟩ :=
      CFSG.GH74.GLS.Stage2.Final.L26.exists_mul_of_mem_sup_of_commute hcomm (hRL hs)
    exact ⟨b, hb, a, Subgroup.mem_centralizer_iff.mpr fun g hg => hcomm' g hg a ha, hcomm a ha b hb⟩
  have hout₁ := not_mem_mul_centralizer_of_inducedPGL2 hodd₁ hm₁ hind₁ hSR hR₁
  have hout₂ := not_mem_mul_centralizer_of_inducedPGL2 hodd₂ hm₂ hind₂ hSR hR₂
  subst hy
  exact ⟨t, htS, htc, hy2, hyS, hout₁, hout₂⟩

end Outer

section Big

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S : Subgroup G}

theorem lemma26_of_g2_big (hctx : Stage2Ctx G z k S) (hbase : Stage1Base G z S)
    (hone : ∀ u v : G, orderOf u = 2 → orderOf v = 2 → IsConj u v)
    {r₁ r₂ : ℕ} {L₁ L₂ : Subgroup (CentralizerBar z)} (hsh : G2Shape z S r₁ r₂ L₁ L₂) (h3 : 3 < r₂) :
    Lemma26 z S := by
  obtain ⟨t, htS, htc, hy2, hyS, hout₁, hout₂⟩ := g2_outer hctx hbase hone hsh
  obtain ⟨hodd₁, hodd₂, hg₁, hprod, hm₁, hm₂, -, -, h4, -, -, -⟩ := hsh
  obtain ⟨hsup, hcomm, hcard⟩ := hprod
  have hcomm' : ∀ a ∈ L₂, ∀ b ∈ L₁, a * b = b * a := fun a ha b hb => (hcomm b hb a ha).symm
  set y : CentralizerBar z := toBar z ⟨t, hctx.S_le_Cen htS⟩ with hy
  have hnc : ∀ L : Subgroup (CentralizerBar z),
      (¬ ∃ a ∈ L, ∃ c ∈ centralizer (L : Set (CentralizerBar z)), y = a * c) →
      ¬ ∀ a ∈ L, y * a = a * y := by
    intro L hL h
    exact hL ⟨1, L.one_mem, y, Subgroup.mem_centralizer_iff.mpr fun g hg => (h g hg).symm, by simp⟩
  have hc₁ : IsComponent L₁ :=
    isComponent_of_sl2_pair hsup hcomm (LBar_normal z) hodd₁ (by omega) hm₁
  have hc₂ : IsComponent L₂ :=
    isComponent_of_sl2_pair (by rw [sup_comm]; exact hsup) hcomm' (LBar_normal z) hodd₂ (by omega) hm₂
  have hL₁N := le_commutator_of_isComponent hc₁ (hnc L₁ hout₁)
  have hL₂N := le_commutator_of_isComponent hc₂ (hnc L₂ hout₂)
  have hL₁O : L₁ ≤ O2Of ⁅(⊤ : Subgroup (CentralizerBar z)), Subgroup.zpowers y⁆ :=
    le_O2Of_of_perfect hc₁.1.1 hL₁N
  have hL₂O : L₂ ≤ O2Of ⁅(⊤ : Subgroup (CentralizerBar z)), Subgroup.zpowers y⁆ :=
    le_O2Of_of_perfect hc₂.1.1 hL₂N
  have hLbO : LBar z ≤ O2Of ⁅(⊤ : Subgroup (CentralizerBar z)), Subgroup.zpowers y⁆ := by
    rw [← hsup]
    exact sup_le hL₁O hL₂O
  have hFLB : generalizedFitting (CentralizerBar z) = LBar z := (h4 h3).2
  refine lemma26_of_bar hctx htS htc ?_ ?_
  · exact ((le_sup_right : layer (CentralizerBar z) ≤ generalizedFitting (CentralizerBar z)).trans
      hFLB.le).trans (hLbO.trans (Subgroup.map_subtype_le _))
  · intro x hx hxS hxW
    have hw : toBar z ⟨x, hx⟩ ∈ WBar z := ⟨⟨x, hx⟩, Subgroup.mem_subgroupOf.mpr hxW, rfl⟩
    exact hLbO (hFLB ▸ WBar_le_generalizedFitting z hw)

end Big

section Three

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S : Subgroup G}

theorem lemma26_of_g2_three (hctx : Stage2Ctx G z k S) (hbase : Stage1Base G z S)
    (hone : ∀ u v : G, orderOf u = 2 → orderOf v = 2 → IsConj u v)
    {r₁ : ℕ} {L₁ L₂ : Subgroup (CentralizerBar z)} (hsh : G2Shape z S r₁ 3 L₁ L₂) :
    Lemma26 z S := by
  obtain ⟨t, htS, htc, hy2, hyS, hout₁, hout₂⟩ := g2_outer hctx hbase hone hsh
  obtain ⟨hodd₁, hodd₂, hg₁, hprod, hm₁, hm₂, -, h3, -, -, -, hind₂⟩ := hsh
  obtain ⟨hsup, hcomm, hcard⟩ := hprod
  have hcomm' : ∀ a ∈ L₂, ∀ b ∈ L₁, a * b = b * a := fun a ha b hb => (hcomm b hb a ha).symm
  set y : CentralizerBar z := toBar z ⟨t, hctx.S_le_Cen htS⟩ with hy
  have hnc : ∀ L : Subgroup (CentralizerBar z),
      (¬ ∃ a ∈ L, ∃ c ∈ centralizer (L : Set (CentralizerBar z)), y = a * c) →
      ¬ ∀ a ∈ L, y * a = a * y := by
    intro L hL h
    exact hL ⟨1, L.one_mem, y, Subgroup.mem_centralizer_iff.mpr fun g hg => (h g hg).symm, by simp⟩
  have hc₁ : IsComponent L₁ :=
    isComponent_of_sl2_pair hsup hcomm (LBar_normal z) hodd₁ (by omega) hm₁
  have hL₁N := le_commutator_of_isComponent hc₁ (hnc L₁ hout₁)
  have hL₁O : L₁ ≤ O2Of ⁅(⊤ : Subgroup (CentralizerBar z)), Subgroup.zpowers y⁆ :=
    le_O2Of_of_perfect hc₁.1.1 hL₁N
  have hZ₁ : Nat.card (center ↥L₁) = 2 := (sl2_model_facts hodd₁ (by omega) hm₁).2.1
  have hZ₂ : Nat.card (center ↥L₂) = 2 := (sl2_model_center_inv hodd₂ hm₂).1
  have hinf : Nat.card ↥(L₂ ⊓ L₁) = 2 := by rwa [inf_comm]
  have hcen₁ : ∀ a ∈ L₁, (∀ c ∈ L₁, c * a = a * c) → a ∈ L₂ := fun a ha hc =>
    central_mem_of_card_inf hcomm hZ₁ hcard ha hc
  have hcen₂ : ∀ a ∈ L₂, (∀ c ∈ L₂, c * a = a * c) → a ∈ L₁ := fun a ha hc =>
    central_mem_of_card_inf hcomm' hZ₂ hinf ha hc
  have hFΦ : generalizedFitting (CentralizerBar z) ≤ L₁ ⊔ L₂ := by
    rw [(h3 rfl).2, hsup]
    exact Subgroup.map_subtype_le _
  have hsol₂ : Group.IsSolvable ↥L₂ := isSolvable_of_hasSL2Model_three' hm₂
  have hNn : (⁅(⊤ : Subgroup (CentralizerBar z)), Subgroup.zpowers y⁆).Normal :=
    normal_commutator_top _
  have hE : layer (CentralizerBar z) ≤ ⁅(⊤ : Subgroup (CentralizerBar z)), Subgroup.zpowers y⁆ := by
    refine sSup_le fun J hJ => ?_
    rcases CFSG.LocalCores.component_normal_subgroup hJ hNn with h | h
    · exact h
    · exfalso
      have hJle : J ≤ L₁ ⊔ L₂ :=
        (le_sSup hJ : J ≤ layer (CentralizerBar z)).trans (le_sup_right.trans hFΦ)
      have hJc : J ≤ centralizer (L₁ : Set (CentralizerBar z)) := by
        have h1 : ⁅J, L₁⁆ = ⊥ := le_bot_iff.mp (h ▸ Subgroup.commutator_mono le_rfl hL₁N)
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1
      have hJL₂ : J ≤ L₂ := by
        intro j hj
        obtain ⟨a, ha, b, hb, rfl⟩ :=
          CFSG.GH74.GLS.Stage2.Final.L26.exists_mul_of_mem_sup_of_commute hcomm (hJle hj)
        have hac : ∀ c ∈ L₁, c * a = a * c := by
          intro c hc
          have h1 : c * (a * b) = (a * b) * c := Subgroup.mem_centralizer_iff.mp (hJc hj) c hc
          have h2 : b * c = c * b := (hcomm c hc b hb).symm
          have h3' : c * a * b = a * c * b := by
            calc c * a * b = c * (a * b) := by group
              _ = a * b * c := h1
              _ = a * (b * c) := by group
              _ = a * (c * b) := by rw [h2]
              _ = a * c * b := by group
          exact mul_right_cancel h3'
        exact L₂.mul_mem (hcen₁ a ha hac) hb
      have : Group.IsPerfect ↥J := hJ.1.1
      have : Nontrivial ↥J := isQuasisimple_nontrivial hJ.1
      have hsolJ : Group.IsSolvable ↥J :=
        Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hJL₂)
      exact Group.IsPerfect.not_isSolvable ↥J hsolJ
  have hWL₂ : WBar z ≤ L₂ := by
    have := WBar_normal z
    exact le_of_normal_twoGroup_of_two_comps hc₁.1 hcomm hcen₁ (WBar_two_pow z)
      ((WBar_le_generalizedFitting z).trans hFΦ)
  have hL₂card : Nat.card ↥L₂ = 24 := card_eq_of_hasSL2Model_three hm₂
  have := hNn
  have hTn : (O2Of ⁅(⊤ : Subgroup (CentralizerBar z)), Subgroup.zpowers y⁆).Normal :=
    O2Of_normal _
  have hcore := three_case_core hm₂ hind₂ hyS hy2 hout₂
    (T := O2Of ⁅(⊤ : Subgroup (CentralizerBar z)), Subgroup.zpowers y⁆)
    (fun b hb hcen => hL₁O (hcen₂ b hb hcen)) (fun n hn ho => mem_O2Of_of_odd hn ho)
  refine lemma26_of_bar hctx htS htc hE ?_
  intro x hx hxS hxW
  have hw : toBar z ⟨x, hx⟩ ∈ WBar z := ⟨⟨x, hx⟩, Subgroup.mem_subgroupOf.mpr hxW, rfl⟩
  have hwL : toBar z ⟨x, hx⟩ ∈ L₂ := hWL₂ hw
  have h8 : (⟨toBar z ⟨x, hx⟩, hwL⟩ : ↥L₂) ^ 8 = 1 := by
    refine pow_eight_of_two_pow hL₂card _ ?_
    obtain ⟨a, ha⟩ := WBar_two_pow z _ hw
    exact ⟨a, Subtype.ext (by simpa using ha)⟩
  exact hcore _ hwL (by simpa using congrArg Subtype.val h8)

end Three

section Final

theorem g2_data {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}
    (hctx : Stage2Ctx G z Kind.g2 S) : Stage1G2 G z S := by
  have hd := hctx.data
  cases hd with
  | g2 h => exact h

theorem lemma26K_g2 : Lemma26K Kind.g2 := by
  intro G _ _ z S hctx
  have hg := g2_data hctx
  obtain ⟨r₁, r₂, L₁, L₂, hsh⟩ := hg.shape
  have hr₂ : 3 ≤ r₂ := by
    obtain ⟨-, hodd₂, -, -, -, hm₂, -⟩ := hsh
    obtain ⟨F, hF, hFin, hq, -⟩ := hm₂
    have h1 : 1 < Nat.card F := Finite.one_lt_card
    have h2 : Nat.card F = r₂ := hq
    obtain ⟨m, hm⟩ := hodd₂
    omega
  rcases Nat.lt_or_ge 3 r₂ with h | h
  · exact lemma26_of_g2_big hctx hg.base hg.one_class hsh h
  · obtain rfl : r₂ = 3 := by omega
    exact lemma26_of_g2_three hctx hg.base hg.one_class hsh

end Final

end CFSG.GH74.GLS.Stage2.Final.L26
