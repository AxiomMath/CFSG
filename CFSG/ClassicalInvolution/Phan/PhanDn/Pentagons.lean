module

public import CFSG.ClassicalInvolution.Phan.PhanDn.Solid
public import CFSG.ClassicalInvolution.Phan.PhanDn.Diameter
public import CFSG.ClassicalInvolution.Phan.Geometry.ShortCycleMoves
public import CFSG.LieType.BorelTits.Families

import all CFSG.LieType.Universal.Spin.Forms
import all CFSG.ClassicalInvolution.Phan.PhanDn.Perp
import all CFSG.ClassicalInvolution.Phan.PhanDn.FlipSpace
import all CFSG.ClassicalInvolution.Phan.PhanDn.PointGraph
public import CFSG.ClassicalInvolution.Phan.Geometry.ShortCycles

public section

namespace CFSG.ClassicalInvolution.PhanDn

open QuadraticMap CFSG.LieType.Universal.Spin CFSG.LieType.BorelTits
open CFSG.ClassicalGroups.Unitary
open CFSG.ClassicalInvolution.Phan
open SimpleGraph

variable {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}

theorem cycleHomotopic_pent_of_perp (hσ : IsUnitaryInvolution σ) [Finite K] {q : ℕ}
    (hK : Nat.card K = q ^ 2) (hq : 4 ≤ q)
    (h3 : NullLen (solidWalks σ n) 3) (h4 : NullLen (solidWalks σ n) 4)
    {a b c d e : FlipPt σ n}
    (hab : (flipGraph σ n).Adj a b) (hbc : (flipGraph σ n).Adj b c)
    (hcd : (flipGraph σ n).Adj c d) (hde : (flipGraph σ n).Adj d e)
    (hea : (flipGraph σ n).Adj e a)
    (hac : a.1 ≤ qPerp n K c.1) (had : a.1 ≤ qPerp n K d.1) :
    CycleHomotopic (solidWalks σ n) (pentWalk hab hbc hcd hde hea) .nil := by
  let L := c.1 ⊔ d.1
  have hL : IsFlipLine σ L := hcd.isFlipLine c.2 d.2
  have haL : a.1 ≤ qPerp n K L := by
    rw [qPerp_sup]
    exact le_inf hac had
  obtain ⟨f, hf_mem, hf_ne_c, hf_ne_d, haf⟩ :=
    exists_flipColl_ne hσ hK hq hL a.2 haL c.1 d.1
  obtain ⟨hf_pt, hf_le_L⟩ := hf_mem
  have hf_ne_c' : f ≠ c.1 := hf_ne_c
  have hf_ne_d' : f ≠ d.1 := hf_ne_d
  have hc_mem : c.1 ∈ ptsOn σ L := ⟨c.2, le_sup_left⟩
  have hd_mem : d.1 ∈ ptsOn σ L := ⟨d.2, le_sup_right⟩
  have hfc : FlipColl σ f c.1 := flipColl_of_le_line hL ⟨hf_pt, hf_le_L⟩ hc_mem hf_ne_c'
  have hfd : FlipColl σ f d.1 := flipColl_of_le_line hL ⟨hf_pt, hf_le_L⟩ hd_mem hf_ne_d'
  let f' : FlipPt σ n := ⟨f, hf_pt⟩
  exact cycleHomotopic_pent_nil_of_apex (solidWalks σ n) h3 h4 (f := f')
    hab hbc hcd hde hea hfc hfd haf

private theorem exists_line_perp_point (hσ : IsUnitaryInvolution σ) (hn : 4 ≤ n)
    {a c d : Submodule K (Fin n ⊕ Fin n → K)}
    {α γ δ x : Fin n ⊕ Fin n → K}
    (hαa : a = K ∙ α) (hγc : c = K ∙ γ) (hδd : d = K ∙ δ)
    (hβ : polar (quadPlus n K) α δ ≠ 0)
    (hαq : quadPlus n K α = 0)
    (hxq : quadPlus n K x = 0)
    (hxx : flipHerm σ x x ≠ 0)
    (hxa : x ∈ qPerp n K a) (hxc : x ∈ qPerp n K c) (hxd : x ∈ qPerp n K d)
    (hxdef : x = polar (quadPlus n K) α δ • γ - polar (quadPlus n K) α γ • δ) :
    ∃ L, IsFlipLine σ L ∧ L ≤ qPerp n K a ∧ L ≤ qPerp n K c ∧ L ≤ qPerp n K d := by
  classical
  have hbot : QNondeg (⊥ : Submodule K (Fin n ⊕ Fin n → K)) := by
    change (⊥ : Submodule K (Fin n ⊕ Fin n → K)) ⊓ qPerp n K ⊥ = ⊥
    rw [bot_inf_eq]
  have hbotPlus : QPlus (⊥ : Submodule K (Fin n ⊕ Fin n → K)) := by
    change ∃ T ≤ (⊥ : Submodule K (Fin n ⊕ Fin n → K)), QSing T ∧
      2 * Module.finrank K T = Module.finrank K (⊥ : Submodule K (Fin n ⊕ Fin n → K))
    refine ⟨⊥, le_rfl, ?_, by simp⟩
    intro w hw
    rw [show w = 0 by simpa using hw]
    exact QuadraticMap.map_zero (quadPlus n K)
  have hmem_bot : α ∈ qPerp n K (⊥ : Submodule K (Fin n ⊕ Fin n → K)) := by
    rw [qPerp_bot]
    exact Submodule.mem_top
  have hbot_sup : (⊥ : Submodule K (Fin n ⊕ Fin n → K)) ⊔ K ∙ α ⊔ K ∙ δ =
      K ∙ α ⊔ K ∙ δ := by
    rw [bot_sup_eq]
  have hAd_nd : QNondeg (K ∙ α ⊔ K ∙ δ) := by
    have h := (QNondeg.sup_pair (A := ⊥) (v := α) (w := δ) hbot hmem_bot hαq hβ).1
    rwa [hbot_sup] at h
  have hAd_plus : QPlus (K ∙ α ⊔ K ∙ δ) := by
    have h := QPlus.sup_pair (A := ⊥) hbot hbotPlus hmem_bot hαq hβ
    rwa [hbot_sup] at h
  have hAd_dim : Module.finrank K ↥(K ∙ α ⊔ K ∙ δ) = 2 := by
    have h := (QNondeg.sup_pair (A := ⊥) (v := α) (w := δ) hbot hmem_bot hαq hβ).2
    rw [finrank_bot, zero_add] at h
    rwa [hbot_sup] at h
  have hAd_perp : x ∈ qPerp n K (K ∙ α ⊔ K ∙ δ) := by
    rw [qPerp_sup, Submodule.mem_inf]
    exact ⟨by rwa [hαa] at hxa, by rwa [hδd] at hxd⟩
  let N : Submodule K (Fin n ⊕ Fin n → K) :=
    (K ∙ α ⊔ K ∙ δ) ⊔ K ∙ x ⊔ K ∙ dFlip σ x
  have hN_nd : QNondeg N :=
    (QNondeg.sup_pair (A := K ∙ α ⊔ K ∙ δ) hAd_nd hAd_perp hxq hxx).1
  have hN_plus : QPlus N :=
    QPlus.sup_pair hAd_nd hAd_plus hAd_perp hxq hxx
  have hN_dim : Module.finrank K N = 4 := by
    have h := (QNondeg.sup_pair (A := K ∙ α ⊔ K ∙ δ) hAd_nd hAd_perp hxq hxx).2
    rw [hAd_dim] at h
    exact h
  have hxN : x ∈ N :=
    Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.mem_span_singleton_self x))
  have hdflipN : dFlip σ x ∈ N :=
    Submodule.mem_sup_right (Submodule.mem_span_singleton_self (dFlip σ x))
  have hαN : α ∈ N := by
    refine Submodule.mem_sup_left (Submodule.mem_sup_left ?_)
    exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self α)
  have hδN : δ ∈ N := by
    refine Submodule.mem_sup_left (Submodule.mem_sup_left ?_)
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self δ)
  let C := qPerp n K N
  have hC_nd : QNondeg C := hN_nd.qPerp
  have hC_plus : QPlus C := hN_plus.qPerp hN_nd
  have hC_dim : Module.finrank K C = 2 * n - 4 := by
    have h := finrank_qPerp (n := n) (K := K) N
    rw [hN_dim] at h
    exact Nat.eq_sub_of_add_eq h
  have hC_dim_ge_n : n ≤ Module.finrank K C := by
    rw [hC_dim]
    omega
  have hC_dim_ge_4 : 4 ≤ Module.finrank K C := by
    rw [hC_dim]
    omega
  have hxC : x ∈ qPerp n K C := by
    rw [show C = qPerp n K N from rfl, qPerp_qPerp]
    exact hxN
  have hne : ∃ u ∈ C, ∃ v ∈ C, flipHerm σ u v ≠ 0 :=
    exists_flipHerm_ne_zero_of_le hσ.invol hC_dim_ge_n hxC hxx
  obtain ⟨P, hPC, hPpt⟩ :=
    exists_isFlipflopPt_le_of_qPlus hσ hC_nd hC_plus hC_dim_ge_4 hne
  have hxpt : IsFlipflopPt σ (K ∙ x) :=
    (isFlipflopPt_span_singleton_iff (by rintro rfl; exact hxx (by simp))).mpr
      ⟨hxq, hxx⟩
  have hKx_qPerp_P : K ∙ x ≤ qPerp n K P := by
    intro u hu
    rw [mem_qPerp]
    intro v hv
    obtain ⟨c₁, rfl⟩ := Submodule.mem_span_singleton.mp hu
    have h := (mem_qPerp.mp (hPC hv)) x hxN
    rw [polar_smul_right, polar_comm (quadPlus n K) v x, h, smul_zero]
  have hKx_flipOrth_P : K ∙ x ≤ flipOrth σ P := by
    intro u hu
    rw [mem_flipOrth]
    intro v hv
    obtain ⟨c₁, rfl⟩ := Submodule.mem_span_singleton.mp hu
    have hvN : v ∈ qPerp n K N := hPC hv
    have h := (mem_qPerp.mp hvN) (dFlip σ x) hdflipN
    have h' : flipHerm σ v x = 0 := by
      show polar (quadPlus n K) v (dFlip σ x) = 0
      rwa [polar_comm (quadPlus n K) v (dFlip σ x)]
    have h'' : flipHerm σ x v = 0 := (flipHerm_eq_zero_iff hσ.invol).mpr h'
    rw [flipHerm_smul_right, h', mul_zero]
  have hcoll : FlipColl σ (K ∙ x) P :=
    flipColl_of_orth hσ.invol hxpt hPpt hKx_qPerp_P hKx_flipOrth_P
  have hL : IsFlipLine σ (K ∙ x ⊔ P) := hcoll.isFlipLine hxpt hPpt
  have hγN : γ ∈ N := by
    have hκδN : polar (quadPlus n K) α γ • δ ∈ N := N.smul_mem _ hδN
    have hsumN : x + polar (quadPlus n K) α γ • δ ∈ N := N.add_mem hxN hκδN
    have h := N.smul_mem ((polar (quadPlus n K) α δ)⁻¹) hsumN
    have heq : (polar (quadPlus n K) α δ)⁻¹ •
        (x + polar (quadPlus n K) α γ • δ) = γ := by
      rw [hxdef, smul_add, smul_sub, sub_add_cancel, smul_smul, inv_mul_cancel₀ hβ,
        one_smul]
    rwa [heq] at h
  have hcN : c ≤ N := by
    rw [hγc]
    exact (Submodule.span_singleton_le_iff_mem γ N).mpr hγN
  have hPqa : P ≤ qPerp n K a := by
    have haN : a ≤ N := by
      rw [hαa]
      exact (Submodule.span_singleton_le_iff_mem α N).mpr hαN
    exact le_trans hPC (qPerp_antitone haN)
  have hPqc : P ≤ qPerp n K c := le_trans hPC (qPerp_antitone hcN)
  have hPqd : P ≤ qPerp n K d := by
    have hdN : d ≤ N := by
      rw [hδd]
      exact (Submodule.span_singleton_le_iff_mem δ N).mpr hδN
    exact le_trans hPC (qPerp_antitone hdN)
  refine ⟨K ∙ x ⊔ P, hL, ?_, ?_, ?_⟩
  · exact sup_le ((Submodule.span_singleton_le_iff_mem x _).mpr hxa) hPqa
  · exact sup_le ((Submodule.span_singleton_le_iff_mem x _).mpr hxc) hPqc
  · exact sup_le ((Submodule.span_singleton_le_iff_mem x _).mpr hxd) hPqd



private theorem inf_flipOrth_span_eq_span
    {W : Submodule K (Fin n ⊕ Fin n → K)}
    (hWdim : Module.finrank K ↥W = 2) {x : Fin n ⊕ Fin n → K}
    (hxW : x ∈ W) (hx0 : x ≠ 0) (hxx : flipHerm σ x x = 0)
    (hnot : ¬ W ≤ flipOrth σ (K ∙ x)) :
    W ⊓ flipOrth σ (K ∙ x) = K ∙ x := by
  have hKx_le : K ∙ x ≤ W ⊓ flipOrth σ (K ∙ x) := by
    refine le_inf ?_ ?_
    · exact (Submodule.span_singleton_le_iff_mem x W).mpr hxW
    · exact (Submodule.span_singleton_le_iff_mem x (flipOrth σ (K ∙ x))).mpr
        (mem_flipOrth_span_singleton.mpr hxx)
  have hproper : W ⊓ flipOrth σ (K ∙ x) < W := by
    refine lt_of_le_of_ne inf_le_left ?_
    intro heq
    exact hnot (heq ▸ inf_le_right)
  have hlt : Module.finrank K ↥(W ⊓ flipOrth σ (K ∙ x)) < Module.finrank K ↥W :=
    Submodule.finrank_lt_finrank_of_lt hproper
  rw [hWdim] at hlt
  have hfin_ge : 1 ≤ Module.finrank K ↥(W ⊓ flipOrth σ (K ∙ x)) := by
    have h := Submodule.finrank_mono hKx_le
    rwa [finrank_span_singleton hx0] at h
  have hfin : Module.finrank K ↥(W ⊓ flipOrth σ (K ∙ x)) = 1 := by omega
  exact (Submodule.eq_of_le_of_finrank_eq hKx_le
    (by rw [finrank_span_singleton hx0, hfin])).symm



private theorem qPerp_inf_qPerp_lagrangian {E₀ : Submodule K (Fin n ⊕ Fin n → K)}
    (hE₀ : (quadPlusForm n K).IsLagrangian E₀) (δ : Fin n ⊕ Fin n → K) :
    qPerp n K (E₀ ⊓ qPerp n K (K ∙ δ)) = E₀ ⊔ K ∙ δ := by
  have h : qPerp n K (E₀ ⊔ K ∙ δ) = E₀ ⊓ qPerp n K (K ∙ δ) := by
    rw [qPerp_sup, qPerp_eq_of_isLagrangian hE₀]
  have h' : E₀ ⊔ K ∙ δ = qPerp n K (E₀ ⊓ qPerp n K (K ∙ δ)) := by
    simpa only [qPerp_qPerp] using congrArg (qPerp n K) h
  exact h'.symm

private theorem dFlip_x_notMem (hσ : IsUnitaryInvolution σ)
    {a c d : Submodule K (Fin n ⊕ Fin n → K)} (hcd : FlipColl σ c d)
    (hc : IsFlipflopPt σ c) (hd : IsFlipflopPt σ d)
    {α x : Fin n ⊕ Fin n → K}
    (hαa : a = K ∙ α) (hαq : quadPlus n K α = 0) (hαh : flipHerm σ α α ≠ 0)
    (hx0 : x ≠ 0) (hxq : quadPlus n K x = 0)
    (hxmem_cd : x ∈ c ⊔ d) (hxx : flipHerm σ x x = 0) :
    dFlip σ x ∉ a ⊔ c ⊔ d := by
  have hW : IsFlipflopSub σ (c ⊔ d) := hcd.2
  have hW_total : QSing (c ⊔ d) := hW.total
  have hxW : x ∈ c ⊔ d := hxmem_cd
  intro hmem
  have hmem' : dFlip σ x ∈ a ⊔ (c ⊔ d) := by
    rwa [sup_assoc] at hmem
  obtain ⟨y, hy, ℓ, hℓ, hmem_eq⟩ := Submodule.mem_sup.mp hmem'
  rw [hαa] at hy
  obtain ⟨μ, rfl⟩ := Submodule.mem_span_singleton.mp hy
  have hℓW : ℓ ∈ c ⊔ d := hℓ
  have hμ : μ ≠ 0 := by
    intro hμ0
    have hℓ_eq : dFlip σ x = ℓ := by
      rw [← hmem_eq, hμ0, zero_smul, zero_add]
    have hx_eq : x = dFlip σ ℓ := by
      rw [← hℓ_eq, dFlip_dFlip hσ.invol]
    have hx_orth : x ∈ flipOrth σ (c ⊔ d) := by
      rw [mem_flipOrth]
      intro t ht
      have htℓ : polar (quadPlus n K) t ℓ = 0 := by
        have h := QuadraticMap.map_add (quadPlus n K) t ℓ
        rw [hW_total t ht, hW_total ℓ hℓW,
          hW_total (t + ℓ) ((c ⊔ d).add_mem ht hℓW)] at h
        simpa using h.symm
      rw [hx_eq, flipHerm, dFlip_dFlip hσ.invol, htℓ]
    have hxbot : x ∈ (c ⊔ d) ⊓ flipOrth σ (c ⊔ d) := ⟨hxW, hx_orth⟩
    rw [inf_flipOrth_eq_bot hσ.invol hW] at hxbot
    exact hx0 (by simpa using hxbot)
  have hQ : quadPlus n K (dFlip σ x) = 0 := by
    rw [quadPlus_dFlip, hxq, map_zero]
  have hQℓ : quadPlus n K ℓ = 0 := hW_total ℓ hℓW
  have hαℓ : polar (quadPlus n K) α ℓ = 0 := by
    have h := hQ
    rw [← hmem_eq, QuadraticMap.map_add (quadPlus n K),
      QuadraticMap.map_smul (quadPlus n K), hαq, smul_zero, hQℓ, zero_add,
      zero_add] at h
    rw [polar_smul_left, smul_eq_mul] at h
    exact (mul_eq_zero.mp h).resolve_left hμ
  have hℓx : flipHerm σ ℓ x = 0 := by
    rw [flipHerm, ← hmem_eq, polar_add_right, polar_smul_right,
      polar_comm (quadPlus n K) ℓ α, hαℓ, smul_zero, zero_add]
    exact polar_self_of_singular hQℓ
  have hnot : ¬ (c ⊔ d) ≤ flipOrth σ (K ∙ x) := by
    intro hWle
    have hx_orth : x ∈ flipOrth σ (c ⊔ d) := by
      rw [mem_flipOrth]
      intro t ht
      have h := mem_flipOrth_span_singleton.mp (hWle ht)
      exact (flipHerm_eq_zero_iff hσ.invol).mpr h
    have hxbot : x ∈ (c ⊔ d) ⊓ flipOrth σ (c ⊔ d) := ⟨hxW, hx_orth⟩
    rw [inf_flipOrth_eq_bot hσ.invol hW] at hxbot
    exact hx0 (by simpa using hxbot)
  have hker : (c ⊔ d) ⊓ flipOrth σ (K ∙ x) = K ∙ x :=
    inf_flipOrth_span_eq_span (hcd.isFlipLine hc hd).2 hxW hx0 hxx hnot
  have hℓKx : ℓ ∈ K ∙ x := by
    have hℓ_mem : ℓ ∈ (c ⊔ d) ⊓ flipOrth σ (K ∙ x) := by
      refine ⟨hℓW, ?_⟩
      exact mem_flipOrth_span_singleton.mpr ((flipHerm_eq_zero_iff hσ.invol).mpr hℓx)
    rwa [hker] at hℓ_mem
  obtain ⟨lam, hlam⟩ := Submodule.mem_span_singleton.mp hℓKx
  have hαx : flipHerm σ α x = 0 := by
    rw [flipHerm, ← hmem_eq, polar_add_right, polar_smul_right,
      polar_self_of_singular hαq, hαℓ, smul_zero, zero_add]
  have hαℓ' : flipHerm σ α ℓ = 0 := by
    rw [← hlam, flipHerm_smul_right, hαx, mul_zero]
  have hℓα : flipHerm σ ℓ α = 0 := (flipHerm_eq_zero_iff hσ.invol).mpr hαℓ'
  have hℓℓ : flipHerm σ ℓ ℓ = 0 := by
    rw [← hlam, flipHerm_smul_left, flipHerm_smul_right, hxx, mul_zero, mul_zero]
  have hσx_self : flipHerm σ (dFlip σ x) (dFlip σ x) = 0 := by
    rw [flipHerm_dFlip_dFlip hσ.invol, hxx, map_zero]
  have hexp : flipHerm σ (dFlip σ x) (dFlip σ x) =
      μ * (σ μ * flipHerm σ α α) + μ * flipHerm σ α ℓ +
        σ μ * flipHerm σ ℓ α + flipHerm σ ℓ ℓ := by
    rw [← hmem_eq, flipHerm_add_left, flipHerm_add_right, flipHerm_add_right,
      flipHerm_smul_left, flipHerm_smul_left, flipHerm_smul_right,
      flipHerm_smul_right]
    ring
  rw [hexp] at hσx_self
  simp only [hαℓ', hℓα, hℓℓ, mul_zero, add_zero] at hσx_self
  have hσμ : σ μ ≠ 0 := fun h => hμ ((map_eq_zero_iff σ σ.injective).mp h)
  have hαα0 : flipHerm σ α α = 0 := by
    rcases mul_eq_zero.mp hσx_self with h | h
    · exact absurd h hμ
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' hσμ
      · exact h'
  exact hαh hαα0

private theorem E_le_qPerp_triple
    {a c d : Submodule K (Fin n ⊕ Fin n → K)}
    {α γ δ x : Fin n ⊕ Fin n → K} {E₀ : Submodule K (Fin n ⊕ Fin n → K)}
    (hαa : a = K ∙ α) (hγc : c = K ∙ γ) (hδd : d = K ∙ δ)
    (hβ : polar (quadPlus n K) α δ ≠ 0)
    (hQSing_E₀ : QSing E₀) (hα_mem_E₀ : α ∈ E₀) (hx_mem_E₀ : x ∈ E₀)
    (hxdef : x = polar (quadPlus n K) α δ • γ - polar (quadPlus n K) α γ • δ) :
    E₀ ⊓ qPerp n K (K ∙ δ) ≤ qPerp n K (a ⊔ c ⊔ d) := by
  have hEa : E₀ ⊓ qPerp n K (K ∙ δ) ≤ qPerp n K a := by
    intro v hv
    obtain ⟨hvE₀, -⟩ := Submodule.mem_inf.mp hv
    rw [hαa, mem_qPerp]
    intro u hu
    obtain ⟨c₁, rfl⟩ := Submodule.mem_span_singleton.mp hu
    have h := QuadraticMap.map_add (quadPlus n K) α v
    rw [hQSing_E₀ α hα_mem_E₀, hQSing_E₀ v hvE₀,
      hQSing_E₀ (α + v) (E₀.add_mem hα_mem_E₀ hvE₀)] at h
    have h0 : polar (quadPlus n K) α v = 0 := by simpa using h.symm
    rw [polar_smul_left, h0, smul_zero]
  have hEc : E₀ ⊓ qPerp n K (K ∙ δ) ≤ qPerp n K c := by
    intro v hv
    obtain ⟨hvE₀, hvδ⟩ := Submodule.mem_inf.mp hv
    rw [hγc, mem_qPerp]
    intro u hu
    obtain ⟨c₁, rfl⟩ := Submodule.mem_span_singleton.mp hu
    have hxv : polar (quadPlus n K) x v = 0 := by
      have h := QuadraticMap.map_add (quadPlus n K) x v
      rw [hQSing_E₀ x hx_mem_E₀, hQSing_E₀ v hvE₀,
        hQSing_E₀ (x + v) (E₀.add_mem hx_mem_E₀ hvE₀)] at h
      simpa using h.symm
    have hδv : polar (quadPlus n K) δ v = 0 :=
      (mem_qPerp.mp hvδ) δ (Submodule.mem_span_singleton_self δ)
    have hγv : polar (quadPlus n K) γ v = 0 := by
      have hγ_eq : γ = (polar (quadPlus n K) α δ)⁻¹ •
          (x + polar (quadPlus n K) α γ • δ) := by
        rw [hxdef, smul_add, smul_sub, sub_add_cancel, smul_smul,
          inv_mul_cancel₀ hβ, one_smul]
      rw [hγ_eq, polar_smul_left, polar_add_left, polar_smul_left]
      simp [hxv, hδv]
    rw [polar_smul_left, hγv, smul_zero]
  have hEd : E₀ ⊓ qPerp n K (K ∙ δ) ≤ qPerp n K d := by
    intro v hv
    obtain ⟨-, hvδ⟩ := Submodule.mem_inf.mp hv
    rw [hδd, mem_qPerp]
    intro u hu
    obtain ⟨c₁, rfl⟩ := Submodule.mem_span_singleton.mp hu
    have h := (mem_qPerp.mp hvδ) δ (Submodule.mem_span_singleton_self δ)
    rw [polar_smul_left, h, smul_zero]
  rw [qPerp_sup, qPerp_sup]
  exact le_inf (le_inf hEa hEc) hEd

private theorem exists_w_nonpoint (hσ : IsUnitaryInvolution σ)
    {a c d : Submodule K (Fin n ⊕ Fin n → K)}
    (hcd : FlipColl σ c d) (hc : IsFlipflopPt σ c) (hd : IsFlipflopPt σ d)
    {α γ δ x : Fin n ⊕ Fin n → K}
    (hαa : a = K ∙ α) (hγc : c = K ∙ γ) (hδd : d = K ∙ δ)
    (hαq : quadPlus n K α = 0) (hαh : flipHerm σ α α ≠ 0)
    (hβ : polar (quadPlus n K) α δ ≠ 0)
    (hx0 : x ≠ 0) (hxq : quadPlus n K x = 0)
    (hxa : x ∈ qPerp n K a) (hxmem_cd : x ∈ c ⊔ d)
    (hxx : flipHerm σ x x = 0)
    (hxdef : x = polar (quadPlus n K) α δ • γ - polar (quadPlus n K) α γ • δ) :
    ∃ w, w ∈ qPerp n K (a ⊔ c ⊔ d) ∧ quadPlus n K w = 0 ∧
      flipHerm σ w x ≠ 0 := by
  classical
  let φ : (Fin n ⊕ Fin n → K) →ₗ[K] K :=
    QuadraticMap.polarBilin (quadPlus n K) (dFlip σ x)
  have hφ_ne : ∃ z ∈ qPerp n K (a ⊔ c ⊔ d), φ z ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply dFlip_x_notMem hσ hcd hc hd hαa hαq hαh hx0 hxq hxmem_cd hxx
    rw [← qPerp_qPerp (n := n) (K := K) (a ⊔ c ⊔ d)]
    rw [mem_qPerp]
    intro z hz
    have h := hcon z hz
    rw [QuadraticMap.polarBilin_apply_apply] at h
    rwa [polar_comm (quadPlus n K) z (dFlip σ x)]
  obtain ⟨z, hzS, hzφ⟩ := hφ_ne
  have hαE₀ : α ∈ K ∙ α := Submodule.mem_span_singleton_self α
  have hxE₀ : x ∈ K ∙ x := Submodule.mem_span_singleton_self x
  have hαx_sing : QSing (K ∙ α ⊔ K ∙ x) := by
    have h1 : (quadPlusForm n K).IsTotallySingular (K ∙ α) :=
      QuadForm.isTotallySingular_span_singleton (Φ := quadPlusForm n K) (by
        rw [quadPlusForm_Q]; exact hαq)
    have h2 : (quadPlusForm n K).Q x = 0 := by rwa [quadPlusForm_Q]
    have hxperp : x ∈ qPerp n K (K ∙ α) := by rwa [hαa] at hxa
    exact (qSing_iff_isTotallySingular _).mpr (h1.sup_span hxperp h2)
  obtain ⟨E₀, hE₀_lag, hKαx_le_E₀⟩ :=
    QuadForm.exists_isLagrangian_le (Φ := quadPlusForm n K) (isLagrangian_stdLag n K) hαx_sing
  have hQSing_E₀ : QSing E₀ := (qSing_iff_isTotallySingular E₀).mpr hE₀_lag.1
  have hα_mem_E₀ : α ∈ E₀ := hKαx_le_E₀ (Submodule.mem_sup_left hαE₀)
  have hx_mem_E₀ : x ∈ E₀ := hKαx_le_E₀ (Submodule.mem_sup_right hxE₀)
  have hE_sing : QSing (E₀ ⊓ qPerp n K (K ∙ δ)) := fun v hv =>
    hQSing_E₀ v (Submodule.mem_inf.mp hv).1
  have hEZ : E₀ ⊓ qPerp n K (K ∙ δ) ≤ qPerp n K (a ⊔ c ⊔ d) :=
    E_le_qPerp_triple hαa hγc hδd hβ hQSing_E₀ hα_mem_E₀ hx_mem_E₀ hxdef
  have hZE : qPerp n K (a ⊔ c ⊔ d) ⊓
      qPerp n K (E₀ ⊓ qPerp n K (K ∙ δ)) ≤ E₀ ⊓ qPerp n K (K ∙ δ) := by
    rw [qPerp_inf_qPerp_lagrangian hE₀_lag δ]
    intro v hv
    obtain ⟨hvS, hvE₀δ⟩ := Submodule.mem_inf.mp hv
    obtain ⟨e, he, w, hw, rfl⟩ := Submodule.mem_sup.mp hvE₀δ
    obtain ⟨c₀, rfl⟩ := Submodule.mem_span_singleton.mp hw
    have hα_mem_S : α ∈ a ⊔ c ⊔ d := by
      rw [hαa]
      exact Submodule.mem_sup_left (Submodule.mem_sup_left
        (Submodule.mem_span_singleton_self α))
    have hαv : polar (quadPlus n K) α (e + c₀ • δ) = 0 :=
      (mem_qPerp.mp hvS) α hα_mem_S
    have hαe : polar (quadPlus n K) α e = 0 := by
      have h := QuadraticMap.map_add (quadPlus n K) α e
      rw [hQSing_E₀ α hα_mem_E₀, hQSing_E₀ e he,
        hQSing_E₀ (α + e) (E₀.add_mem hα_mem_E₀ he)] at h
      simpa using h.symm
    rw [polar_add_right, polar_smul_right, hαe, zero_add] at hαv
    have hc₀ : c₀ = 0 := (mul_eq_zero.mp hαv).resolve_right hβ
    rw [hc₀, zero_smul, add_zero] at hvS ⊢
    refine ⟨he, ?_⟩
    change e ∈ qPerp n K (K ∙ δ)
    rw [mem_qPerp]
    intro u hu
    obtain ⟨d₁, rfl⟩ := Submodule.mem_span_singleton.mp hu
    have hδ_mem_S : δ ∈ a ⊔ c ⊔ d := by
      rw [hδd]
      exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self δ)
    have hδe : polar (quadPlus n K) δ e = 0 := (mem_qPerp.mp hvS) δ hδ_mem_S
    rw [polar_smul_left, hδe, smul_zero]
  obtain ⟨w, hwS, hwq, hwφ⟩ :=
    exists_singular_apply_ne_zero hEZ hE_sing hZE φ hzS hzφ
  refine ⟨w, hwS, hwq, ?_⟩
  rw [flipHerm, polar_comm (quadPlus n K) w (dFlip σ x)]
  exact hwφ

private theorem exists_line_perp_nonpoint (hσ : IsUnitaryInvolution σ)
    {a c d : Submodule K (Fin n ⊕ Fin n → K)}
    (hcd : FlipColl σ c d) (hc : IsFlipflopPt σ c) (hd : IsFlipflopPt σ d)
    {α γ δ x : Fin n ⊕ Fin n → K}
    (hαa : a = K ∙ α) (hγc : c = K ∙ γ) (hδd : d = K ∙ δ)
    (hαq : quadPlus n K α = 0) (hαh : flipHerm σ α α ≠ 0)
    (hβ : polar (quadPlus n K) α δ ≠ 0)
    (hx0 : x ≠ 0) (hxq : quadPlus n K x = 0)
    (hxa : x ∈ qPerp n K a) (hxc : x ∈ qPerp n K c) (hxd : x ∈ qPerp n K d)
    (hxmem_cd : x ∈ c ⊔ d) (hxx : flipHerm σ x x = 0)
    (hxdef : x = polar (quadPlus n K) α δ • γ - polar (quadPlus n K) α γ • δ) :
    ∃ L, IsFlipLine σ L ∧ L ≤ qPerp n K a ∧ L ≤ qPerp n K c ∧ L ≤ qPerp n K d := by
  obtain ⟨w, hwS, hwq, hwx⟩ :=
    exists_w_nonpoint hσ hcd hc hd hαa hγc hδd hαq hαh hβ hx0 hxq hxa hxmem_cd hxx hxdef
  have hw_a : w ∈ qPerp n K a :=
    qPerp_antitone (le_trans le_sup_left le_sup_left) hwS
  have hw_c : w ∈ qPerp n K c :=
    qPerp_antitone (le_trans le_sup_right le_sup_left) hwS
  have hw_d : w ∈ qPerp n K d := qPerp_antitone le_sup_right hwS
  have hb_xw : polar (quadPlus n K) x w = 0 := by
    have hx_mem : x ∈ a ⊔ c ⊔ d := by
      have hle : c ⊔ d ≤ a ⊔ c ⊔ d :=
        sup_le (le_trans le_sup_right le_sup_left) le_sup_right
      exact hle hxmem_cd
    exact (mem_qPerp.mp hwS) x hx_mem
  have hLsing : QSing (K ∙ x ⊔ K ∙ w) := by
    have h1 : (quadPlusForm n K).IsTotallySingular (K ∙ x) :=
      QuadForm.isTotallySingular_span_singleton (Φ := quadPlusForm n K) (by
        rw [quadPlusForm_Q]; exact hxq)
    have h2 : (quadPlusForm n K).Q w = 0 := by rwa [quadPlusForm_Q]
    have hwperp : w ∈ qPerp n K (K ∙ x) := by
      rw [mem_qPerp]
      intro u hu
      obtain ⟨c₁, rfl⟩ := Submodule.mem_span_singleton.mp hu
      rw [polar_smul_left, hb_xw, smul_zero]
    exact (qSing_iff_isTotallySingular _).mpr (h1.sup_span hwperp h2)
  have hLnd : ∀ u ∈ K ∙ x ⊔ K ∙ w,
      (∀ v ∈ K ∙ x ⊔ K ∙ w, flipHerm σ u v = 0) → u = 0 := by
    intro u hu hper
    obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := Submodule.mem_sup.mp hu
    obtain ⟨c₁, rfl⟩ := Submodule.mem_span_singleton.mp ha₁
    obtain ⟨d₁, rfl⟩ := Submodule.mem_span_singleton.mp hb₁
    have hwx' : flipHerm σ w x ≠ 0 := hwx
    have hxw : flipHerm σ x w ≠ 0 := fun hzero =>
      hwx ((flipHerm_eq_zero_iff hσ.invol).mp hzero)
    have h1 := hper x (Submodule.mem_sup_left (Submodule.mem_span_singleton_self x))
    have h2 := hper w (Submodule.mem_sup_right (Submodule.mem_span_singleton_self w))
    rw [flipHerm_add_left, flipHerm_smul_left, flipHerm_smul_left, hxx, mul_zero,
      zero_add] at h1
    have hd0 : d₁ = 0 := (mul_eq_zero.mp h1).resolve_right hwx'
    rw [flipHerm_add_left, flipHerm_smul_left, flipHerm_smul_left, hd0, zero_mul,
      add_zero] at h2
    have hc0 : c₁ = 0 := (mul_eq_zero.mp h2).resolve_right hxw
    rw [hc0, hd0]
    simp
  have hw_not : w ∉ K ∙ x := by
    intro hwx'
    obtain ⟨c₁, rfl⟩ := Submodule.mem_span_singleton.mp hwx'
    apply hwx
    rw [flipHerm_smul_left, hxx, mul_zero]
  have hLdim : Module.finrank K ↥(K ∙ x ⊔ K ∙ w) = 2 := by
    rw [Submodule.finrank_sup_span_singleton hw_not, finrank_span_singleton hx0]
  have hL : IsFlipLine σ (K ∙ x ⊔ K ∙ w) := ⟨⟨hLsing, hLnd⟩, hLdim⟩
  refine ⟨K ∙ x ⊔ K ∙ w, hL, ?_, ?_, ?_⟩
  · exact sup_le ((Submodule.span_singleton_le_iff_mem x _).mpr hxa)
      ((Submodule.span_singleton_le_iff_mem w _).mpr hw_a)
  · exact sup_le ((Submodule.span_singleton_le_iff_mem x _).mpr hxc)
      ((Submodule.span_singleton_le_iff_mem w _).mpr hw_c)
  · exact sup_le ((Submodule.span_singleton_le_iff_mem x _).mpr hxd)
      ((Submodule.span_singleton_le_iff_mem w _).mpr hw_d)

private theorem exists_line_perp (hσ : IsUnitaryInvolution σ) (hn : 4 ≤ n)
    {a c d : Submodule K (Fin n ⊕ Fin n → K)}
    (hcd : FlipColl σ c d) (ha : IsFlipflopPt σ a) (hc : IsFlipflopPt σ c)
    (hd : IsFlipflopPt σ d) (had : ¬ a ≤ qPerp n K d) :
    ∃ L, IsFlipLine σ L ∧ L ≤ qPerp n K a ∧ L ≤ qPerp n K c ∧ L ≤ qPerp n K d := by
  classical
  obtain ⟨α, hαa, hαq, hαh⟩ := IsFlipflopPt.exists_eq_span ha
  obtain ⟨γ, hγc, hγq, hγh⟩ := IsFlipflopPt.exists_eq_span hc
  obtain ⟨δ, hδd, hδq, hδh⟩ := IsFlipflopPt.exists_eq_span hd
  let β := polar (quadPlus n K) α δ
  let κ := polar (quadPlus n K) α γ
  let x := β • γ - κ • δ
  have hβ : β ≠ 0 := by
    intro hβ0
    apply had
    rw [hαa, hδd]
    intro u hu
    rw [mem_qPerp]
    intro w hw
    obtain ⟨c₁, rfl⟩ := Submodule.mem_span_singleton.mp hu
    obtain ⟨d₁, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [polar_smul_left, polar_smul_right, polar_comm (quadPlus n K) δ α,
      show polar (quadPlus n K) α δ = 0 from hβ0]
    simp
  have hx0 : x ≠ 0 := by
    intro hx
    have h : β • γ = κ • δ := by
      rw [sub_eq_zero] at hx
      exact hx
    have hγKδ : γ ∈ K ∙ δ := by
      have hβγ : β • γ ∈ K ∙ δ := by
        rw [h]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self δ)
      have hγ_eq : γ = β⁻¹ • (β • γ) := by
        rw [smul_smul, inv_mul_cancel₀ hβ, one_smul]
      rw [hγ_eq]
      exact Submodule.smul_mem _ _ hβγ
    have hle : c ≤ d := by
      rw [hγc, hδd]
      exact (Submodule.span_singleton_le_iff_mem γ (K ∙ δ)).mpr hγKδ
    exact hcd.1 (Submodule.eq_of_le_of_finrank_eq hle (by rw [hc.2, hd.2]))
  have hxmem_cd : x ∈ c ⊔ d := by
    rw [hγc, hδd]
    exact Submodule.sub_mem _
      (Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self γ)))
      (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self δ)))
  have hxq : quadPlus n K x = 0 := hcd.2.total x hxmem_cd
  have hxa : x ∈ qPerp n K a := by
    rw [hαa, mem_qPerp]
    intro w hw
    obtain ⟨c₁, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [polar_smul_left]
    have h : polar (quadPlus n K) α x = 0 := by
      rw [show x = β • γ - κ • δ from rfl, polar_sub_right, polar_smul_right,
        polar_smul_right, polar_comm (quadPlus n K) α γ, polar_comm (quadPlus n K) α δ,
        smul_eq_mul, smul_eq_mul,
        show β = polar (quadPlus n K) α δ from rfl,
        show κ = polar (quadPlus n K) α γ from rfl,
        ← polar_comm (quadPlus n K) γ α, ← polar_comm (quadPlus n K) δ α]
      ring
    rw [h, smul_zero]
  have hxperp_cd : x ∈ qPerp n K (c ⊔ d) := QSing.le_qPerp hcd.2.total hxmem_cd
  have hxc : x ∈ qPerp n K c := qPerp_antitone (le_sup_left : c ≤ c ⊔ d) hxperp_cd
  have hxd : x ∈ qPerp n K d := qPerp_antitone (le_sup_right : d ≤ c ⊔ d) hxperp_cd

  by_cases hxx : flipHerm σ x x = 0
  · exact exists_line_perp_nonpoint hσ hcd hc hd hαa hγc hδd hαq hαh hβ hx0 hxq
      hxa hxc hxd hxmem_cd hxx (by rfl)
  · exact exists_line_perp_point hσ hn hαa hγc hδd hβ hαq hxq hxx hxa hxc hxd (by rfl)

theorem exists_split (hσ : IsUnitaryInvolution σ) [Finite K] {q : ℕ}
    (hK : Nat.card K = q ^ 2) (hq : 4 ≤ q) (hn : 4 ≤ n)
    {a c d : Submodule K (Fin n ⊕ Fin n → K)}
    (hcd : FlipColl σ c d) (ha : IsFlipflopPt σ a) (hc : IsFlipflopPt σ c)
    (hd : IsFlipflopPt σ d) (had : ¬ a ≤ qPerp n K d) :
    ∃ f, IsFlipflopPt σ f ∧ FlipColl σ a f ∧ FlipColl σ d f ∧ f ≤ qPerp n K c := by
  obtain ⟨L, hL, hLa, hLc, hLd⟩ :=
    exists_line_perp hσ hn hcd ha hc hd had
  have haL : a ≤ qPerp n K L := by
    rw [← qPerp_qPerp (n := n) (K := K) a]
    exact qPerp_antitone hLa
  have hdL : d ≤ qPerp n K L := by
    rw [← qPerp_qPerp (n := n) (K := K) d]
    exact qPerp_antitone hLd
  obtain ⟨f, hfL, haf, hdf⟩ := exists_flipColl₂ hσ hK hq hL ha hd haL hdL
  exact ⟨f, hfL.1, haf, hdf, le_trans hfL.2 hLc⟩

private theorem cycleHomotopic_pent_of_not_perp (hσ : IsUnitaryInvolution σ) [Finite K]
    {q : ℕ} (hK : Nat.card K = q ^ 2) (hq : 4 ≤ q) (hn : 4 ≤ n)
    (h3 : NullLen (solidWalks σ n) 3) (h4 : NullLen (solidWalks σ n) 4)
    {a b c d e : FlipPt σ n}
    (hab : (flipGraph σ n).Adj a b) (hbc : (flipGraph σ n).Adj b c)
    (hcd : (flipGraph σ n).Adj c d) (hde : (flipGraph σ n).Adj d e)
    (hea : (flipGraph σ n).Adj e a) (had : ¬ a.1 ≤ qPerp n K d.1) :
    CycleHomotopic (solidWalks σ n) (pentWalk hab hbc hcd hde hea) .nil := by
  obtain ⟨f, hfpt, haf, hdf, hfc⟩ :=
    exists_split hσ hK hq hn hcd a.2 c.2 d.2 had
  let f' : FlipPt σ n := ⟨f, hfpt⟩
  have haf' : (flipGraph σ n).Adj a f' := haf
  have hdf' : (flipGraph σ n).Adj d f' := hdf
  have hfa : (flipGraph σ n).Adj f' a := haf'.symm
  have h2 : CycleHomotopic (solidWalks σ n) (quadWalk hfa.symm hdf'.symm hde hea) .nil :=
    h4 (quadWalk hfa.symm hdf'.symm hde hea) rfl
  by_cases hfb : f' ≤ qPerp n K b.1
  · have h1' : CycleHomotopic (solidWalks σ n)
        (pentWalk hfa hab hbc hcd hdf') .nil :=
      cycleHomotopic_pent_of_perp hσ hK hq h3 h4 hfa hab hbc hcd hdf' hfb hfc
    have h1 : CycleHomotopic (solidWalks σ n) (pentWalk hab hbc hcd hdf' hfa) .nil :=
      cycleHomotopic_pent_rotate (E := solidWalks σ n) hfa hab hbc hcd hdf' h1'
    exact cycleHomotopic_pent_of_split (E := solidWalks σ n) hab hbc hcd hde hea hdf' hfa h1 h2
  · have hbc' : FlipColl σ c.1 b.1 := hbc.symm
    obtain ⟨g, hgpt, hfg, hbg, hgc⟩ :=
      exists_split hσ hK hq hn hbc' hfpt c.2 b.2 hfb
    let g' : FlipPt σ n := ⟨g, hgpt⟩
    have hfg' : (flipGraph σ n).Adj f' g' := hfg
    have hbg' : (flipGraph σ n).Adj b g' := hbg
    have hgf' : (flipGraph σ n).Adj g' f' := hfg'.symm
    have hcg : c.1 ≤ qPerp n K g := by
      rw [← qPerp_qPerp (n := n) (K := K) c.1]
      exact qPerp_antitone hgc
    have hcf : c.1 ≤ qPerp n K f := by
      rw [← qPerp_qPerp (n := n) (K := K) c.1]
      exact qPerp_antitone hfc
    have h1'' : CycleHomotopic (solidWalks σ n)
        (pentWalk hbc.symm hbg' hgf' hdf'.symm hcd.symm) .nil :=
      cycleHomotopic_pent_of_perp hσ hK hq h3 h4 hbc.symm hbg' hgf' hdf'.symm hcd.symm
        hcg hcf
    have hrot1 : CycleHomotopic (solidWalks σ n)
        (pentWalk hbg' hgf' hdf'.symm hcd.symm hbc.symm) .nil :=
      cycleHomotopic_pent_rotate (E := solidWalks σ n) hbc.symm hbg' hgf' hdf'.symm hcd.symm h1''
    have hrot2 : CycleHomotopic (solidWalks σ n)
        (pentWalk hgf' hdf'.symm hcd.symm hbc.symm hbg') .nil :=
      cycleHomotopic_pent_rotate (E := solidWalks σ n) hbg' hgf' hdf'.symm hcd.symm hbc.symm hrot1
    have hrot3 : CycleHomotopic (solidWalks σ n)
        (pentWalk hdf'.symm hcd.symm hbc.symm hbg' hgf') .nil :=
      cycleHomotopic_pent_rotate (E := solidWalks σ n) hgf' hdf'.symm hcd.symm hbc.symm hbg' hrot2
    have h2' : CycleHomotopic (solidWalks σ n)
        (quadWalk hgf'.symm hbg'.symm hab.symm haf') .nil :=
      h4 (quadWalk hgf'.symm hbg'.symm hab.symm haf') rfl
    have hrev : CycleHomotopic (solidWalks σ n)
        (pentWalk hdf'.symm hcd.symm hbc.symm hab.symm haf') .nil :=
      cycleHomotopic_pent_of_split (E := solidWalks σ n) hdf'.symm hcd.symm hbc.symm hab.symm
        haf' hbg' hgf' hrot3 h2'
    have hfa_bcd : CycleHomotopic (solidWalks σ n)
        (pentWalk haf'.symm hab hbc hcd hdf') .nil :=
      cycleHomotopic_pent_reverse (E := solidWalks σ n)
        (fun x c hc => reverse_mem_solidWalks hc) hdf'.symm hcd.symm hbc.symm hab.symm haf' hrev
    have h1 : CycleHomotopic (solidWalks σ n) (pentWalk hab hbc hcd hdf' hfa) .nil :=
      cycleHomotopic_pent_rotate (E := solidWalks σ n) haf'.symm hab hbc hcd hdf' hfa_bcd
    exact cycleHomotopic_pent_of_split (E := solidWalks σ n) hab hbc hcd hde hea hdf' hfa h1 h2

theorem cycleHomotopic_pent (hσ : IsUnitaryInvolution σ) [Finite K] {q : ℕ}
    (hK : Nat.card K = q ^ 2) (hq : 4 ≤ q) (hn : 4 ≤ n)
    (h3 : NullLen (solidWalks σ n) 3) (h4 : NullLen (solidWalks σ n) 4)
    {a b c d e : FlipPt σ n}
    (hab : (flipGraph σ n).Adj a b) (hbc : (flipGraph σ n).Adj b c)
    (hcd : (flipGraph σ n).Adj c d) (hde : (flipGraph σ n).Adj d e)
    (hea : (flipGraph σ n).Adj e a) :
    CycleHomotopic (solidWalks σ n) (pentWalk hab hbc hcd hde hea) .nil := by
  by_cases hd : a.1 ≤ qPerp n K d.1
  · by_cases hc : a.1 ≤ qPerp n K c.1
    · exact cycleHomotopic_pent_of_perp hσ hK hq h3 h4 hab hbc hcd hde hea hc hd
    · exact cycleHomotopic_pent_reverse (E := solidWalks σ n)
        (fun x c hc => reverse_mem_solidWalks hc) hea.symm hde.symm hcd.symm hbc.symm hab.symm
        (cycleHomotopic_pent_of_not_perp hσ hK hq hn h3 h4
          hea.symm hde.symm hcd.symm hbc.symm hab.symm hc)
  · exact cycleHomotopic_pent_of_not_perp hσ hK hq hn h3 h4 hab hbc hcd hde hea hd

theorem nullLen_five_of_nullLen_four (hσ : IsUnitaryInvolution σ) [Finite K] {q : ℕ}
    (hK : Nat.card K = q ^ 2) (hq : 4 ≤ q) (hn : 4 ≤ n)
    (h3 : NullLen (solidWalks σ n) 3) (h4 : NullLen (solidWalks σ n) 4) :
    NullLen (solidWalks σ n) 5 := by
  intro u p hp
  match u, p, hp with
  | _, .nil, hp => simp only [Walk.length_nil] at hp; omega
  | _, .cons _ .nil, hp => simp only [Walk.length_cons, Walk.length_nil] at hp; omega
  | _, .cons _ (.cons _ .nil), hp =>
    simp only [Walk.length_cons, Walk.length_nil] at hp; omega
  | _, .cons _ (.cons _ (.cons _ .nil)), hp =>
    simp only [Walk.length_cons, Walk.length_nil] at hp; omega
  | _, .cons _ (.cons _ (.cons _ (.cons _ .nil))), hp =>
    simp only [Walk.length_cons, Walk.length_nil] at hp; omega
  | _, .cons e1 (.cons e2 (.cons e3 (.cons e4 (.cons e5 .nil)))), _ =>
    exact cycleHomotopic_pent hσ hK hq hn h3 h4 e1 e2 e3 e4 e5
  | _, .cons _ (.cons _ (.cons _ (.cons _ (.cons _ (.cons _ _))))), hp =>
    simp only [Walk.length_cons] at hp
    omega

theorem cycleTrivial_solidWalks_of_nullLen (hσ : IsUnitaryInvolution σ) [Finite K] {q : ℕ}
    (hK : Nat.card K = q ^ 2) (hq : 4 ≤ q) (hn : 4 ≤ n)
    (h3 : NullLen (solidWalks σ n) 3) (h4 : NullLen (solidWalks σ n) 4) :
    CycleTrivial (solidWalks σ n) :=
  cycleTrivial_of_nullLen (E := solidWalks σ n) (flipGraph_connected hσ hK hq hn)
    (flipGraph_ediam_le_two hσ hK hq hn) h3 h4
    (nullLen_five_of_nullLen_four hσ hK hq hn h3 h4)

end CFSG.ClassicalInvolution.PhanDn
