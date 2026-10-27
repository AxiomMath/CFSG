module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3DHyp1
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3DObj

public noncomputable section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaSec3

open CFSG.Fischer Subgroup CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2
open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open scoped commutatorElement

variable {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* T46} {t : G}

theorem d_A₄_le_A₂ : (sec3DData e t).A₄ ≤ (sec3DData e t).A₂ := toG_ch_le (by decide)

theorem d_A₄_le_A₃ : (sec3DData e t).A₄ ≤ (sec3DData e t).A₃ := toG_ch_le (by decide)

theorem d_A₂_comm : ∀ a ∈ (sec3DData e t).A₂, ∀ b ∈ (sec3DData e t).A₂, a * b = b * a :=
  fun a ha _ hb => mem_centralizer_iff.1 (toG_le_centralizer xComm_spec.1 hb) a ha

theorem d_A₂_sq : ∀ a ∈ (sec3DData e t).A₂, a * a = 1 := by
  intro a ha
  obtain ⟨g, hg, rfl⟩ := mem_toG.1 ha
  rw [← map_mul, show g * g = 1 from
    Subtype.ext (grp_sq_of_comm gensOK_chA2 xComm_spec.1 (by decide) _ hg), map_one]

theorem d_card_A₂ : Nat.card (sec3DData e t).A₂ = 2 ^ 9 := by
  rw [show (sec3DData e t).A₂ = toG e chA2.grp from rfl, card_toG_ch gensOK_chA2, card_chA2]
  norm_num

theorem d_A₃_le_cent_A₄ :
    (sec3DData e t).A₃ ≤ centralizer ((sec3DData e t).A₄ : Set G) :=
  toG_le_centralizer xComm_spec.2.1

theorem d_card_A₃ : Nat.card (sec3DData e t).A₃ = 2 ^ 12 := by
  rw [show (sec3DData e t).A₃ = toG e chA3.grp from rfl, card_toG_ch gensOK_chA3, card_chA3]
  norm_num

theorem d_center_A₃ :
    (sec3DData e t).A₃ ⊓ centralizer ((sec3DData e t).A₃ : Set G) ≤ (sec3DData e t).A₄ :=
  toG_inf_centralizer_le (grp_le_T46 gensOK_chA3) fun g hg _ hc =>
    (zA3_spec g hg).1 fun _ hw => hc _ (wP_mem_grp hw)

theorem d_card_A₄ : Nat.card (sec3DData e t).A₄ = 2 ^ 4 := by
  rw [show (sec3DData e t).A₄ = toG e chA4.grp from rfl, card_toG_ch gensOK_chA4, card_chA4]
  norm_num

theorem d_Λ_le_normalizer : (sec3DData e t).Λ ≤ normalizer ((sec3DData e t).A₄ : Set G) :=
  toG_le_normalizer (grp_le_T46 gensOK_chLam) (grp_le_T46 gensOK_chA4) xNorm_spec.1

theorem d_Λ_le_NA₃ : (sec3DData e t).Λ ≤ normalizer ((sec3DData e t).A₃ : Set G) :=
  toG_le_normalizer (grp_le_T46 gensOK_chLam) (grp_le_T46 gensOK_chA3) xNorm_spec.2.1

theorem d_Sig_le_NA₃ : (sec3DData e t).Sig ≤ normalizer ((sec3DData e t).A₃ : Set G) :=
  toG_le_normalizer (grp_le_T46 gensOK_chSig) (grp_le_T46 gensOK_chA3) xNorm_spec.2.2.1

theorem d_Sig_le_cent_A₄ : (sec3DData e t).Sig ≤ centralizer ((sec3DData e t).A₄ : Set G) :=
  toG_le_centralizer xComm_spec.2.2.2.1

theorem d_Λ_comm_Sig : ∀ l ∈ (sec3DData e t).Λ, ∀ s ∈ (sec3DData e t).Sig, l * s = s * l :=
  fun _ hl s hs => (mem_centralizer_iff.1 (toG_le_centralizer xComm_spec.2.2.2.2.1 hl) s hs).symm

theorem d_A₄_le_comm : (sec3DData e t).A₄ ≤ ⁅(sec3DData e t).A₄, (sec3DData e t).Λ⁆ := by
  refine toG_le_of_prodCheck gensOK_chA4 xWit_spec.1 (by decide) (by decide) fun p hp b hb => ?_
  have hl : ∀ p ∈ a4cData, ∀ b ∈ p.2, (∀ k ∈ b.1, k < 18 ∧ [k] ∈ chA4.gens) ∧
      ∀ k ∈ b.2, k < 18 ∧ [k] ∈ chLam.gens := by decide
  obtain ⟨h1, h2⟩ := hl p hp b hb
  rw [gw_cwW (fun k hk => (h1 k hk).1) (fun k hk => (h2 k hk).1)]
  exact commutator_mem_commutator (gw_mem_ch h1) (gw_mem_ch h2)

theorem d_e_pow : (sec3DData e t).e ^ 3 = 1 := by
  show gw e [4, 17] ^ 3 = 1
  rw [pow_succ, pow_two, ← gw_append, ← gw_append,
    gw_eq_xId (b := []) (by decide) (by decide) (by decide), gw_nil]

theorem d_e_cent_A₄ : (sec3DData e t).e ∈ centralizer ((sec3DData e t).A₄ : Set G) :=
  gw_mem_centralizer_toG (by decide) xComm_spec.2.2.1

theorem d_e_norm_A₃ : (sec3DData e t).e ∈ normalizer ((sec3DData e t).A₃ : Set G) :=
  gw_mem_normalizer_toG gensOK_chA3 (by decide) xNorm_spec.2.2.2.1

theorem d_A₃_cent_e :
    (sec3DData e t).A₃ ⊓ centralizer ({(sec3DData e t).e} : Set G) ≤ (sec3DData e t).A₄ :=
  toG_inf_centralizer_gw_le (by decide) fun g hg _ hc => (zA3_spec g hg).2 hc

end CFSG.EvenSmallLie.UnitarySix.YamadaSec3
