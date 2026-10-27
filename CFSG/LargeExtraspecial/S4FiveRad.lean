module

public import CFSG.LargeExtraspecial.S4FiveBeta
public import CFSG.LargeExtraspecial.OrthoF2SpRadical

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

variable (H : Hyp4 S g) (H11 : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
  (hVQ : ¬ V S g t ≤ S.Qa g)
include H H11 ht ht1 hVQ

theorem mem_clSub_of_beta_aV_eq_zero {y : Vt S g t} (hy : beta H H11 ht ht1 hVQ (aV ht) y = 0) :
    (y : S.Qt) ∈ S.clSub (S.QG ⊓ S.Qa g) := by
  obtain ⟨y', hy'⟩ := exists_t_sub_eq H H11 ht ht1 hVQ y
  rw [beta_apply H H11 ht ht1 hVQ _ _ hy'] at hy
  obtain ⟨w, hwQ, rfl⟩ := S.exists_cl y'
  have hwa : w ∈ S.QG ⊓ centralizer ({g * S.z * g⁻¹} : Set G) :=
    ⟨hwQ, mem_centralizer_singleton_iff.mpr ((S.polar_cl_eq_zero_iff H.conj_mem hwQ).mp hy).symm⟩
  rw [← hy']
  exact H11.comm_le w hwa t ht

theorem beta_aV_eq_zero_iff (y : Vt S g t) :
    beta H H11 ht ht1 hVQ (aV ht) y = 0 ↔ (y : S.Qt) ∈ S.clSub (S.QG ⊓ S.Qa g) := by
  set A : Submodule (ZMod 2) (Vt S g t) := (S.clSub (S.QG ⊓ S.Qa g)).comap (Vt S g t).subtype
    with hA
  set K := LinearMap.ker (beta H H11 ht ht1 hVQ (aV ht)) with hK
  have hKA : K ≤ A := fun y hy => mem_clSub_of_beta_aV_eq_zero H H11 ht ht1 hVQ hy
  have hAne : A ≠ ⊤ := by
    intro htop
    apply hVQ
    rw [V_le_Qa_iff H.conj_mem H.conj_ne]
    intro v hv
    have : (⟨v, hv⟩ : Vt S g t) ∈ A := htop ▸ Submodule.mem_top
    exact this
  have hβ0 : beta H H11 ht ht1 hVQ (aV ht) ≠ 0 := by
    intro h0
    apply aV_ne_zero H ht
    exact (beta_nondegenerate H H11 ht ht1 hVQ).1 _ fun y => by rw [h0, LinearMap.zero_apply]
  have hrange : LinearMap.range (beta H H11 ht ht1 hVQ (aV ht)) = ⊤ := by
    obtain ⟨y, hy⟩ : ∃ y, beta H H11 ht ht1 hVQ (aV ht) y ≠ 0 := by
      by_contra h
      push Not at h
      exact hβ0 (LinearMap.ext h)
    have hy1 := OrthoF2.zmod2_eq_one_of_ne_zero hy
    rw [LinearMap.range_eq_top]
    intro c
    exact ⟨c • y, by rw [map_smul, hy1, smul_eq_mul, mul_one]⟩
  have h1 := LinearMap.finrank_range_add_finrank_ker (beta H H11 ht ht1 hVQ (aV ht))
  rw [hrange, finrank_top, finrank_self, ← hK] at h1
  have h2 : finrank (ZMod 2) A < finrank (ZMod 2) (Vt S g t) := Submodule.finrank_lt hAne
  have h3 := Submodule.finrank_mono hKA
  have hKA' : K = A := Submodule.eq_of_le_of_finrank_le hKA (by omega)
  constructor
  · intro hy
    exact hKA (LinearMap.mem_ker.mpr hy)
  · intro hy
    have : y ∈ K := hKA' ▸ hy
    exact LinearMap.mem_ker.mp this

theorem LmodN_le_spPointRadical :
    LmodN S g t ≤ spPointRadical (beta H H11 ht ht1 hVQ) (aV ht) := by
  intro e he
  have heR := LmodN_le_RmodN ht he
  have hiso := RmodN_le_isometryGroup H H11 ht ht1 hVQ heR
  obtain ⟨s, hs, hes⟩ := he
  have hea : e (aV ht) = aV ht := Subtype.ext (by
    rw [hes]
    exact (mem_fixSub S).mp (by rw [H.fixSub_eq]; exact Submodule.mem_span_singleton_self _) s hs)
  refine ⟨hiso, hea, fun x hx => ?_, fun v => ?_⟩
  · rw [mem_span_singleton_subtype]
    have hxP := (beta_aV_eq_zero_iff H H11 ht ht1 hVQ x).mp hx
    obtain ⟨w, hw, -, hwx⟩ := S.mem_clSub_iff.mp hxP
    have := Lbar_apply_sub_mem_span H.conj_mem hw hs
    rw [hwx] at this
    change ((e x : Vt S g t) : S.Qt) - x ∈ _
    rw [hes]
    exact this
  · have h1 := TauCeti.BilinForm.mem_isometryGroup_iff.mp hiso (aV ht) v
    rw [hea] at h1
    rw [map_sub, h1, sub_self]

theorem aV_mem_perp : (aV ht : S.Qt) ∈ S.clSub (S.QG ⊓ S.Qa g) :=
  (beta_aV_eq_zero_iff H H11 ht ht1 hVQ _).mp (beta_isAlt H H11 ht ht1 hVQ _)

theorem card_LmodN_ge :
    2 ^ (finrank (ZMod 2) (Vt S g t) - 2) ≤ Nat.card (LmodN S g t) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A : Submodule (ZMod 2) (Vt S g t) := LinearMap.ker (beta H H11 ht ht1 hVQ (aV ht)) with hA
  have hAinv : ∀ (e : LmodN S g t) u, u ∈ A → (LmodN S g t).subtype e u ∈ A := by
    intro e u hu
    have h1 := (LmodN_le_spPointRadical H H11 ht ht1 hVQ e.2)
    rw [LinearMap.mem_ker] at hu ⊢
    rw [← h1.2.1, coe_subtype, TauCeti.BilinForm.mem_isometryGroup_iff.mp h1.1]
    exact hu
  set ψ := restrictHom (LmodN S g t).subtype A hAinv with hψ
  have haA : aV ht ∈ A := LinearMap.mem_ker.mpr (beta_isAlt H H11 ht ht1 hVQ _)
  have hψc : ∀ e (u : A), ψ e u - u ∈ (ZMod 2) ∙ (⟨aV ht, haA⟩ : A) := by
    intro e u
    rw [mem_span_singleton_subtype]
    exact (LmodN_le_spPointRadical H H11 ht ht1 hVQ e.2).2.2.1 u
      (LinearMap.mem_ker.mp u.2)
  have hLp : IsPGroup 2 (LmodN S g t) := by
    rw [← range_resL H.conj_mem ht]
    exact (isPGroup_Lbar S H.conj_mem).of_surjective _ (resL H.conj_mem ht).rangeRestrict_surjective
  have : Finite (Vt S g t ≃ₗ[ZMod 2] Vt S g t) := finite_linearEquiv_of_finite
  obtain ⟨hcard, -⟩ := card_range_of_transvections hLp ψ _ hψc
  have hfix : finrank (ZMod 2) (fixSpaceOf ψ.range) ≤ 1 := by
    have hle : fixSpaceOf ψ.range ≤ (ZMod 2) ∙ (⟨aV ht, haA⟩ : A) := by
      intro u hu
      rw [mem_fixSpaceOf_range] at hu
      rw [mem_span_singleton_subtype, mem_span_singleton_subtype]
      change ((u : Vt S g t) : S.Qt) ∈ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹)
      rw [← H.fixSub_eq]
      intro s hs
      have h1 := congrArg (fun w : A => ((w : Vt S g t) : S.Qt))
        (hu ⟨resL H.conj_mem ht ⟨s, hs⟩, (range_resL H.conj_mem ht) ▸ ⟨_, rfl⟩⟩)
      exact h1
    calc finrank (ZMod 2) (fixSpaceOf ψ.range) ≤
          finrank (ZMod 2) ((ZMod 2) ∙ (⟨aV ht, haA⟩ : A)) := Submodule.finrank_mono hle
      _ ≤ 1 := by
          by_cases h0 : (⟨aV ht, haA⟩ : A) = 0
          · rw [h0, Submodule.span_singleton_eq_bot.mpr rfl, finrank_bot]
            exact zero_le_one
          · rw [finrank_span_singleton h0]
  have hβ0 : beta H H11 ht ht1 hVQ (aV ht) ≠ 0 := by
    intro h0
    apply aV_ne_zero H ht
    exact (beta_nondegenerate H H11 ht ht1 hVQ).1 _ fun y => by rw [h0, LinearMap.zero_apply]
  have hrange : LinearMap.range (beta H H11 ht ht1 hVQ (aV ht)) = ⊤ := by
    obtain ⟨y, hy⟩ : ∃ y, beta H H11 ht ht1 hVQ (aV ht) y ≠ 0 := by
      by_contra h
      push Not at h
      exact hβ0 (LinearMap.ext h)
    have hy1 := OrthoF2.zmod2_eq_one_of_ne_zero hy
    rw [LinearMap.range_eq_top]
    intro c
    exact ⟨c • y, by rw [map_smul, hy1, smul_eq_mul, mul_one]⟩
  have hdimA := LinearMap.finrank_range_add_finrank_ker (beta H H11 ht ht1 hVQ (aV ht))
  rw [hrange, finrank_top, finrank_self, ← hA] at hdimA
  have hle := Nat.le_of_dvd Nat.card_pos (Subgroup.card_range_dvd ψ)
  rw [hcard] at hle
  refine le_trans (Nat.pow_le_pow_right (by norm_num) ?_) hle
  omega

theorem card_spPointRadical_le_two_mul :
    Nat.card (spPointRadical (beta H H11 ht ht1 hVQ) (aV ht)) ≤ 2 * Nat.card (LmodN S g t) := by
  rw [card_spPointRadical (beta_isAlt H H11 ht ht1 hVQ) (beta_nondegenerate H H11 ht ht1 hVQ)
    (aV_ne_zero H ht)]
  have h1 := card_LmodN_ge H H11 ht ht1 hVQ
  have h2 : 4 ≤ finrank (ZMod 2) (Vt S g t) ∨ finrank (ZMod 2) (Vt S g t) < 4 := le_or_gt _ _
  have hpos : 1 ≤ finrank (ZMod 2) (Vt S g t) := Nat.one_le_iff_ne_zero.mpr fun h =>
    Vt_ne_bot H ht (Submodule.finrank_eq_zero.mp h)
  have hev := even_finrank_Vt H H11 ht ht1 hVQ
  obtain ⟨k, hk⟩ := hev
  have : finrank (ZMod 2) (Vt S g t) - 1 = (finrank (ZMod 2) (Vt S g t) - 2) + 1 := by omega
  rw [this, pow_succ, mul_comm]
  exact Nat.mul_le_mul_left 2 h1

end CFSG.LargeExtraspecial.S4
