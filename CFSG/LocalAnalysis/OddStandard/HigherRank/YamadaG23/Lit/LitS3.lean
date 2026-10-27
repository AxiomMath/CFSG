module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitS3A
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitS3Card
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitBasic
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitOneJ

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three CFSG.OddStandard.HigherRank.G2Three.Sec1
  CFSG.GH74.GLS
open scoped commutatorElement

variable {Γ : Type} [Group Γ] {Gh Zh Ah : Subgroup Γ} {t : Γ}

theorem lit_s3_comm [Finite Γ] (h : LitGam Gh Zh Ah t)
    (hq : IsQuotIso (normIn Gh Ah) (Gh ⊓ centralizerSection Ah Zh) (Equiv.Perm (Fin 6)))
    (hT : IsQuotIso (Gh ⊓ centralizerSection (Zh ⊔ zpowers t) Zh)
      (Gh ⊓ centralizerSection (Zh ⊔ zpowers t) Zh ⊓ (Gh ⊓ centralizerSection Ah Zh))
      ↥blockStab) :
    ∃ b ∈ Ah, b ∉ Zh ∧ ∀ x ∈ (CFSG.oddCore ↥Gh).map Gh.subtype, x * b = b * x := by
  classical
  let N : Subgroup Γ := (CFSG.oddCore ↥Gh).map Gh.subtype
  have ht2 : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rw [h.ord_t] at this
    simpa [pow_two] using this
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hNodd : Odd (Nat.card N) := by
    rw [Subgroup.card_map_of_injective Gh.subtype_injective]
    exact lit_odd_card_oddCore ↥Gh
  have hGN : ∀ g ∈ Gh, g ∈ normalizer (N : Set Γ) := by
    have fwd : ∀ g ∈ Gh, ∀ x ∈ N, g * x * g⁻¹ ∈ N := by
      intro g hg x hx
      rw [Subgroup.mem_map] at hx ⊢
      obtain ⟨y, hy, rfl⟩ := hx
      exact ⟨⟨g, hg⟩ * y * ⟨g, hg⟩⁻¹,
        (inferInstance : (CFSG.oddCore ↥Gh).Normal).conj_mem y hy ⟨g, hg⟩, rfl⟩
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fwd g hg x, fun hx => ?_⟩
    have hx' := fwd g⁻¹ (Gh.inv_mem hg) (g * x * g⁻¹) hx
    rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at hx'
  have htN : t ∈ normalizer (N : Set Γ) := by
    let c : ↥Gh ≃* ↥Gh :=
      { toFun := fun x => ⟨t * (x : Γ) * t⁻¹,
          (Subgroup.mem_normalizer_iff.mp h.t_G (x : Γ)).mp x.2⟩
        invFun := fun x => ⟨t⁻¹ * (x : Γ) * t⁻¹⁻¹,
          (Subgroup.mem_normalizer_iff.mp ((normalizer (Gh : Set Γ)).inv_mem h.t_G) (x : Γ)).mp x.2⟩
        left_inv := by intro x; apply Subtype.ext; group
        right_inv := by intro x; apply Subtype.ext; group
        map_mul' := by
          intro x y
          apply Subtype.ext
          simp only [Subgroup.coe_mul, Subtype.coe_mk]
          group }
    have hchar : (CFSG.oddCore ↥Gh).comap c.toMonoidHom = CFSG.oddCore ↥Gh :=
      (lit_oddCore_characteristic ↥Gh).fixed c
    have fwdT : ∀ x ∈ N, t * x * t⁻¹ ∈ N := by
      intro x hx
      rw [Subgroup.mem_map] at hx ⊢
      obtain ⟨y, hy, rfl⟩ := hx
      exact ⟨c y, by
        have : y ∈ (CFSG.oddCore ↥Gh).comap c.toMonoidHom := by rw [hchar]; exact hy
        simpa using this, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fwdT x, fun hx => ?_⟩
    have hx' := fwdT (t * x * t⁻¹) hx
    rwa [show t * (t * x * t⁻¹) * t⁻¹ = x by
      calc t * (t * x * t⁻¹) * t⁻¹ = (t * t) * x * (t⁻¹ * t⁻¹) := by group
        _ = x := by rw [ht2, hti, ht2]; simp] at hx'
  obtain ⟨S, hSN, hS2, hSidx, _htS, hStA⟩ := lit_s3_sylow h
  have hnotle : ¬ S ≤ Gh ⊓ centralizerSection (Zh ⊔ zpowers t) Zh :=
    lit_s3_not_le_T h hq hT hSN hS2 hSidx
  obtain ⟨s, hsS, hsTn⟩ := SetLike.not_le_iff_exists.mp hnotle
  have hsG : s ∈ Gh := (hSN hsS).1
  have hsC : s ∉ centralizerSection (Zh ⊔ zpowers t) Zh := fun hsc => hsTn ⟨hsG, hsc⟩
  have hts_notZh : ⁅t, s⁆ ∉ Zh := fun hz =>
    hsC ((lit_mem_T_iff h.Z_central h.Z_le_G h.t_Z hsG).mpr hz)
  have hb_not_Zh : ⁅s, t⁆ ∉ Zh := by
    intro hb
    apply hts_notZh
    rw [(commutatorElement_inv (g₁ := s) (g₂ := t)).symm]
    exact Zh.inv_mem hb
  have hcomm_le_A : ⁅S, zpowers t⁆ ≤ Ah := by
    rw [Subgroup.commutator_le]
    intro s' hs' g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    have hk : t ^ k = 1 ∨ t ^ k = t := by
      have hmod := zpow_mod_orderOf t k
      rw [h.ord_t] at hmod
      rcases Int.emod_two_eq_zero_or_one k with hk0 | hk1
      · left; rw [← hmod]; simp [hk0]
      · right; rw [← hmod]; simp [hk1]
    rcases hk with hk | hk
    · rw [hk, commutatorElement_one_right]; exact Ah.one_mem
    · rw [hk]; exact hStA s' hs'
  have h2 : ∀ b ∈ ⁅S, zpowers t⁆, ∃ k : ℕ, b ^ 2 ^ k = 1 := by
    intro b hb
    obtain ⟨k, hk⟩ := h.sylow.2.1.exists_pow_pow_eq_one (⟨b, hcomm_le_A hb⟩ : ↥Ah)
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hinf : Ah ⊓ N = ⊥ := by
    have hcop : Nat.Coprime (Nat.card Ah) (Nat.card N) := by
      rw [h.card_A, show (64 : ℕ) = 2 ^ 6 by norm_num,
        Nat.coprime_pow_left_iff (by norm_num : 0 < 6)]
      exact Nat.coprime_two_left.mpr hNodd
    exact disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard hcop)
  have hC : ∀ x ∈ N, t * x * t⁻¹ = x → ∀ b ∈ ⁅S, zpowers t⁆, x * b = b * x := by
    intro x hxN htx b hb
    have hbA : b ∈ Ah := hcomm_le_A hb
    have hbG : b ∈ Gh := h.A_le_G hbA
    have hxG : x ∈ Gh := Subgroup.map_subtype_le _ hxN
    have hxT : x ∈ Gh ⊓ centralizerSection (Zh ⊔ zpowers t) Zh := by
      rw [Subgroup.mem_inf]
      refine ⟨hxG, ?_⟩
      rw [lit_mem_T_iff h.Z_central h.Z_le_G h.t_Z hxG]
      have ht1 : ⁅t, x⁆ = 1 := by
        rw [commutatorElement_eq_one_iff_mul_comm]
        have := congrArg (fun z => z * t) htx
        simpa [mul_assoc] using this
      rw [ht1]
      exact Zh.one_mem
    have hxA : x ∈ normalizer (Ah : Set Γ) := h.five_b hxT
    have hcA : ⁅x, b⁆ ∈ Ah := by
      have h1 : x * b * x⁻¹ ∈ Ah := (Subgroup.mem_normalizer_iff.mp hxA b).mp hbA
      have h2 : b⁻¹ ∈ Ah := Ah.inv_mem hbA
      simpa [commutatorElement_def] using Ah.mul_mem h1 h2
    have hcN : ⁅x, b⁆ ∈ N := by
      have hbn : b ∈ normalizer (N : Set Γ) := hGN b hbG
      have hconj : b * x⁻¹ * b⁻¹ ∈ N :=
        (Subgroup.mem_normalizer_iff.mp hbn x⁻¹).mp (N.inv_mem hxN)
      rw [show ⁅x, b⁆ = x * (b * x⁻¹ * b⁻¹) by
        simp only [commutatorElement_def]; group]
      exact N.mul_mem hxN hconj
    have hc1 : ⁅x, b⁆ = 1 := by
      have hmem : ⁅x, b⁆ ∈ Ah ⊓ N := ⟨hcA, hcN⟩
      rw [hinf] at hmem
      exact Subgroup.mem_bot.mp hmem
    exact commutatorElement_eq_one_iff_mul_comm.mp hc1
  have hOneJ := lit_oneJ_comm (N := N) hNodd h.ord_t htN
    (fun s hs => hGN s (hSN hs).1) h2 hC
  exact ⟨⁅s, t⁆, hStA s hsS, hb_not_Zh, fun x hx =>
    hOneJ x hx ⁅s, t⁆ (Subgroup.commutator_mem_commutator hsS (Subgroup.mem_zpowers t))⟩

end CFSG.OddStandard.HigherRank.YamadaG23
