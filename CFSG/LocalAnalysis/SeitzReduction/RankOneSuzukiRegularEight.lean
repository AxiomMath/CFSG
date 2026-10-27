module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiRegularCoords
public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiPartition
public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiEight

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis

namespace SzStart

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem false_of_card_range_eq_168_of_card_sylow
    (h : SzStart G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hT : ¬ ∃ S : Sylow 2 G, (S : Subgroup G) = T) (hf : f = 3)
    (hN : Nat.card (gmsRootConjugateAction (szA L T t) (zpowers t)).range = 168)
    (hs : IsSimpleGroup (gmsRootConjugateAction (szA L T t) (zpowers t)).range) : False := by
  have hD := h.partitionData_of_card_sylow hS2 hT
  obtain ⟨hTeq, hdisj, -, -, -, -, -, hCA, -⟩ := h.facts_of_card_sylow hS2
  obtain ⟨a, ha, hfa, K, _, _, _, hK, d, u, v, κ, -, -, hc, -, -⟩ :=
    h.exists_torusCoords_of_card_sylow hS2
  subst hf
  obtain rfl : a = 1 := by omega
  have hKa : Fintype.card K = 2 ^ (2 * 1 + 1) := hK
  have hK8 : Nat.card K = 8 := by rw [Nat.card_eq_fintype_card, hK]; norm_num
  have hpow : (2 : ℕ) ^ (1 + 1) + 1 = 5 := by norm_num
  have ht := h.mem_centralizer_szT₁
  have ht2 := h.sq_eq_one
  have htT : t ∉ szT₁ L T := fun h1 => by
    have ht1 : t ∈ szT₁ L T ⊓ zpowers t := mem_inf.mpr ⟨h1, mem_zpowers t⟩
    rw [hdisj, mem_bot] at ht1
    have h2 := h.inv
    rw [ht1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have hv_inj : ∀ b ∈ szA₁ (szT₁ L T), ∀ b' ∈ szA₁ (szT₁ L T), v b = v b' → b = b' :=
    fun b hb b' hb' hbb => hc.inj b (szA₁_le _ hb) b' (szA₁_le _ hb')
      (by rw [hc.u_eq_zero_of_mem_szA₁ ha hKa hb, hc.u_eq_zero_of_mem_szA₁ ha hKa hb']) hbb
  obtain ⟨e, he⟩ : ∃ e : gmsRootConjugates (szA L T t) (zpowers t) ≃ K,
      ∀ b (hb : b ∈ szA₁ (szT₁ L T)), e ⟨zpowers (b * t), hD.mem_iff.mpr ⟨b, hb, rfl⟩⟩ = v b :=
    hD.exists_equiv hv_inj (fun β => hc.exists_v_eq ha hKa β)
  set N := (gmsRootConjugateAction (szA L T t) (zpowers t)).range
  set N' : Subgroup (Equiv.Perm K) := N.map e.permCongrHom.toMonoidHom
  have hiso : N ≃* N' := N.equivMapOfInjective _ e.permCongrHom.injective
  have hN' : Nat.card N' = 168 := by rw [← Nat.card_congr hiso.toEquiv, hN]
  have hs' : IsSimpleGroup N' := hiso.symm.isSimpleGroup
  have hform : ∀ x ∈ N', ∃ n : normalizer (szA L T t : Set G), ∃ c ∈ szA₁ (szT₁ L T),
      ∀ b ∈ szA₁ (szT₁ L T), x (v b) = v ((n : G) * b * (n : G)⁻¹ * c) := by
    rintro x ⟨σ, ⟨n, rfl⟩, rfl⟩
    obtain ⟨c, hcA, hnc⟩ := hD.exists_conj_t_eq n.2
    exact ⟨n, c, hcA, fun b hb => hD.permCongr_action_apply he n hcA hnc hb⟩
  have hnA₁ : ∀ n : normalizer (szA L T t : Set G), ∀ b ∈ szA₁ (szT₁ L T),
      (n : G) * b * (n : G)⁻¹ ∈ szA₁ (szT₁ L T) := fun n b hb =>
    (mem_normalizer_iff.mp (hD.normalizer_le n.2) b).mp hb
  have hzero : ∀ (x : Equiv.Perm K) (n : normalizer (szA L T t : Set G)) (c : G),
      (∀ b ∈ szA₁ (szT₁ L T), x (v b) = v ((n : G) * b * (n : G)⁻¹ * c)) → x 0 = v c := by
    intro x n c hxv
    rw [← hc.v_one, hxv 1 (one_mem _), show (n : G) * 1 * (n : G)⁻¹ * c = c by group]
  have haff : ∀ x ∈ N', ∀ β γ : K, x (β + γ) + x 0 = x β + x γ := by
    intro x hx β γ
    obtain ⟨n, c, hcA, hxv⟩ := hform x hx
    obtain ⟨b, hb, rfl⟩ := hc.exists_v_eq ha hKa β
    obtain ⟨b', hb', rfl⟩ := hc.exists_v_eq ha hKa γ
    rw [hzero x n c hxv, ← hc.v_mul_szA₁ ha hKa hb hb', hxv _ (mul_mem hb hb'), hxv _ hb,
      hxv _ hb',
      show (n : G) * (b * b') * (n : G)⁻¹ * c =
        (n : G) * b * (n : G)⁻¹ * ((n : G) * b' * (n : G)⁻¹) * c by group,
      hc.v_mul_szA₁ ha hKa (mul_mem (hnA₁ n b hb) (hnA₁ n b' hb')) hcA,
      hc.v_mul_szA₁ ha hKa (hnA₁ n b hb) (hnA₁ n b' hb'),
      hc.v_mul_szA₁ ha hKa (hnA₁ n b hb) hcA, hc.v_mul_szA₁ ha hKa (hnA₁ n b' hb') hcA]
    ring
  have hsq : ∀ x ∈ N', ∃ ψ : AddAut K, ∀ α : K, x (α ^ 5) - x 0 = ψ α ^ 5 := by
    intro x hx
    obtain ⟨n, c, hcA, hxv⟩ := hform x hx
    have hnT : (n : G) ∈ normalizer ((szT₁ L T ⊔ zpowers t : Subgroup G) : Set G) := by
      have h1 : (n : G) ∈ normalizer (T : Set G) := by
        have h2 := CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer (szA L T t) n.2
        rwa [hCA] at h2
      have key : ∀ m : G, m ∈ normalizer (T : Set G) →
          m ∈ normalizer ((szT₁ L T ⊔ zpowers t : Subgroup G) : Set G) := fun m hm => by
        rwa [← hTeq]
      exact key _ h1
    obtain ⟨ψ, hψ⟩ := hc.exists_addAut_conj ha hKa ht ht2 htT hnT n.2
    refine ⟨ψ, fun α => ?_⟩
    obtain ⟨y, hy, hyu, -⟩ := hc.surj α 0
    have hy2 := (hc.sq hy).2
    rw [hyu, hpow] at hy2
    have hyA : y ^ 2 ∈ szA₁ (szT₁ L T) := hc.sq_mem_szA₁ ha hKa hy
    have hw : (n : G) * y * (n : G)⁻¹ ∈ szT₁ L T ⊔ zpowers t :=
      (mem_normalizer_iff.mp hnT _).mp (mem_sup_left hy)
    obtain ⟨-, hv2⟩ := hc.sq_mem_and_v_sq ha hKa ht ht2 htT hw
    rw [← hy2, hxv _ hyA, hzero x n c hxv, hc.v_mul_szA₁ ha hKa (hnA₁ n _ hyA) hcA,
      add_sub_cancel_right,
      show (n : G) * y ^ 2 * (n : G)⁻¹ = ((n : G) * y * (n : G)⁻¹) ^ 2 by
        simp only [sq]; group,
      hv2, hψ y hy, hyu, hpow]
  exact false_of_affine_card_eq_168_of_sq_equivariant hK8 N' haff hN' hs' hsq

end SzStart

end CFSG.SeitzReduction.RankOne
