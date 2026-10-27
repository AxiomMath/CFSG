module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7NPm
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7NJf2

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7n_inf_ne_bot {A M B : Subgroup G} (hA : SimpleSec A M) (hB : B ≤ A)
    (hcard : 168 < Nat.card ↥B) : B ⊓ M ≠ ⊥ := by
  intro hbot
  haveI hN : (M.subgroupOf A).Normal :=
    (Subgroup.normal_subgroupOf_iff hA.le).mpr fun h k hh hk => hA.normal k hk h hh
  let f : ↥B →* (↥A ⧸ M.subgroupOf A) :=
    (QuotientGroup.mk' (M.subgroupOf A)).comp (Subgroup.inclusion hB)
  have hker : f.ker = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hxM : (x : G) ∈ M := by
      have h1 : QuotientGroup.mk' (M.subgroupOf A) (Subgroup.inclusion hB x) = 1 := hx
      have h2 : Subgroup.inclusion hB x ∈ (QuotientGroup.mk' (M.subgroupOf A)).ker :=
        MonoidHom.mem_ker.mpr h1
      rw [QuotientGroup.ker_mk'] at h2
      simpa using Subgroup.mem_subgroupOf.mp h2
    have hxbot : (x : G) ∈ B ⊓ M := ⟨x.2, hxM⟩
    rw [hbot] at hxbot
    exact Subtype.ext (Subgroup.mem_bot.mp hxbot)
  have hq : Nat.card (↥A ⧸ M.subgroupOf A) = 168 := by
    have hcardA := hA.card
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (M.subgroupOf A)] at hcardA
    have hsub : Nat.card ↥(M.subgroupOf A) = Nat.card ↥M :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA.le).toEquiv
    rw [hsub] at hcardA
    exact Nat.mul_right_cancel (Nat.card_pos (α := ↥M)) hcardA
  have hle : Nat.card ↥B ≤ 168 :=
    hq ▸ Nat.card_le_card_of_injective f ((MonoidHom.ker_eq_bot_iff f).mp hker)
  omega

theorem y7n_g_norm_Lam {c : Ctx7 G L} (hH : F33Hyp c.s c.e) (h5 : c.toCtx5.Facts5)
    (h7 : c.Upto79) (hRT : c.s.R ≠ c.s.T) {L1 : Subgroup G} (hL1 : IsCompPre c.s L1) :
    conjSub c.g ⁅L1, L1⁆ = ⁅L1, L1⁆ := by
  have hgM3 : c.g ∈ normalizer (M3 c.s : Set G) := by
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    have h : c.g * m * c.g⁻¹ = m := h5.2.2.2.1 hRT m hm
    have h' : c.g * m = m * c.g := by
      have h2 := congrArg (fun x => x * c.g) h
      simpa [mul_assoc] using h2
    exact h'.symm
  have hgK : c.g ∈ normalizer (K7 c.s : Set G) := y7n_N_M3_le_N_K c.s hgM3
  rcases y7n_perm_Lam hH h7 hL1 hgK with ⟨h1, _⟩ | ⟨h1, _⟩
  · exact h1
  · exfalso
    have h79 : c.Fact79 := h7.2
    have hSimple : SimpleSec L1 (M3 c.s) := y7n_simpleSec_L1 hL1
    have hHle : ⁅L1, L1⁆ ≤ L1 := by
      refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
      rw [commutatorElement_def]
      exact L1.mul_mem (L1.mul_mem (L1.mul_mem ha hb) (L1.inv_mem ha)) (L1.inv_mem hb)
    have hLamcard : Nat.card ↥⁅L1, L1⁆ = 1344 := (y7n_Lam_facts hH h79 hL1).2.2.1
    have hne : ⁅L1, L1⁆ ⊓ M3 c.s ≠ ⊥ :=
      y7n_inf_ne_bot hSimple hHle (by rw [hLamcard]; norm_num)
    obtain ⟨f, hfne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    have hfLam : (f : G) ∈ ⁅L1, L1⁆ := f.2.1
    have hfM3 : (f : G) ∈ M3 c.s := f.2.2
    have hfne' : (f : G) ≠ 1 := fun h => hfne (Subtype.ext h)
    have hgfix : c.g * (f : G) * c.g⁻¹ = (f : G) := h5.2.2.2.1 hRT f hfM3
    have hmem1 : c.g * (f : G) * c.g⁻¹ ∈ conjSub c.g ⁅L1, L1⁆ :=
      (mem_conjSub_iff' c.g ⁅L1, L1⁆ _).mpr ⟨f, hfLam, rfl⟩
    rw [h1, hgfix] at hmem1
    have hmem : (f : G) ∈ ⁅L1, L1⁆ ⊓ conjSub c.s.t ⁅L1, L1⁆ := ⟨hfLam, hmem1⟩
    rw [(h79 L1 hL1).1.2.1] at hmem
    exact hfne' (Subgroup.mem_bot.mp hmem)

end CFSG.OddStandard.HigherRank.YamadaG23
