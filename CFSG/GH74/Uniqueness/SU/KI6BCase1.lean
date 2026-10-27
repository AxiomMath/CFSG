module

public import CFSG.GH74.Uniqueness.SU.KI6BCent
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Hall.Basic

public section

namespace CFSG.GH74.Uniqueness.SU.K.R6

open Subgroup CFSG CFSG.Blueprint CFSG.ProperTwoGeneratedCore CFSG.GH74.Uniqueness.SU.K.R3
open scoped Pointwise commutatorElement
open CFSG.LocalCores

variable {H : Type} [Group H] [Finite H] {T : Sylow 2 H} {H₀ : Subgroup H}

theorem Cfg.normal_of_unique (h : Cfg H T H₀) (hFH : generalizedFitting H ⊔ H₀ = ⊤)
    {K₁ : Subgroup H} (hK₁ : IsComponent K₁) (hK₁H : ¬ K₁ ≤ H₀)
    (huniq : ∀ K₂ : Subgroup H, IsComponent K₂ → ¬ K₂ ≤ H₀ → K₂ = K₁) : K₁.Normal := by
  constructor
  intro x hx g
  have hcomp : IsComponent (K₁.map (MulAut.conj g).toMonoidHom) :=
    isComponent_map_mulEquiv (MulAut.conj g) hK₁
  have hnot : ¬ (K₁.map (MulAut.conj g).toMonoidHom ≤ H₀) := by
    intro hle
    apply h.conj_not_le hFH hK₁ hK₁H g
    intro y hy
    exact hle ⟨y, hy, by simp⟩
  have heq := huniq _ hcomp hnot
  have hmem : g * x * g⁻¹ ∈ K₁.map (MulAut.conj g).toMonoidHom := ⟨x, hx, by simp⟩
  rw [heq] at hmem
  exact hmem

omit [Finite H] in
theorem centralizer_normal_of_normal {K : Subgroup H} (hK : K.Normal) :
    (centralizer (K : Set H)).Normal := by
  constructor
  intro n hn g
  rw [Subgroup.mem_centralizer_iff] at hn ⊢
  intro k hk
  have hk' : g⁻¹ * k * g ∈ K := by
    have := hK.conj_mem k hk g⁻¹
    simpa using this
  have h1 := hn _ hk'
  calc k * (g * n * g⁻¹) = g * ((g⁻¹ * k * g) * n) * g⁻¹ := by group
    _ = g * (n * (g⁻¹ * k * g)) * g⁻¹ := by rw [h1]
    _ = (g * n * g⁻¹) * k := by group


theorem Cfg.cent_inf_fitting_le (F : KI6BFacts) (h : Cfg H T H₀)
    (hr : ∀ L : Subgroup H, IsComponent L → Open.pRank 2 L ≤ 1) {t : H} (htc : t ∈ center H)
    (ht2 : orderOf t = 2) {K₁ : Subgroup H} (hK₁ : IsComponent K₁)
    (hoth : ∀ K₂ : Subgroup H, IsComponent K₂ → K₂ ≠ K₁ → K₂ ≤ H₀) :
    centralizer (K₁ : Set H) ⊓ generalizedFitting H ≤ H₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfit : fittingSubgroup H = pCore 2 H := Fitting_eq_pcore H 2 h.odd
  have hdata := component_data F h htc ht2 hK₁ (hr K₁ hK₁)
  set E' : Subgroup H := sSup {K' : Subgroup H | IsComponent K' ∧ K' ≠ K₁} with hE'
  have hE'H : E' ≤ H₀ := sSup_le fun K' hK' => hoth K' hK'.1 hK'.2
  have hE'C : E' ≤ centralizer (K₁ : Set H) := by
    refine sSup_le fun K' hK' x hx => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact components_commute hK₁ hK'.1 (fun h' => hK'.2 h'.symm) k hk x hx
  have hlayer : layer H = K₁ ⊔ E' := by
    apply le_antisymm
    · refine sSup_le fun L hL => ?_
      by_cases hLK : L = K₁
      · rw [hLK]; exact le_sup_left
      · exact le_sup_of_le_right (le_sSup ⟨hL, hLK⟩)
    · exact sup_le (component_le_layer hK₁) (sSup_le fun K' hK' => component_le_layer hK'.1)
  have hQC : pCore 2 H ≤ centralizer (K₁ : Set H) := by
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (h.pCore_comm_layer hq (component_le_layer hK₁ hx)).symm
  have hAC : pCore 2 H ⊔ E' ≤ centralizer (K₁ : Set H) := sup_le hQC hE'C
  have hAH : pCore 2 H ⊔ E' ≤ H₀ := sup_le ((Cfg.pCore_le_T T).trans h.sylow_le) hE'H
  have hF : generalizedFitting H = (pCore 2 H ⊔ E') ⊔ K₁ := by
    rw [generalizedFitting, hfit, hlayer, sup_comm K₁ E', ← sup_assoc]
  intro n ⟨hnC, hnF⟩
  rw [hF] at hnF
  obtain ⟨a, ha, b, hb, rfl⟩ := SU1.mem_sup_of_commute
    (fun a ha b hb => (Subgroup.mem_centralizer_iff.mp (hAC ha) b hb).symm) hnF
  have hbC : b ∈ centralizer (K₁ : Set H) := by
    have h1 : b = a⁻¹ * (a * b) := by group
    rw [h1]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hAC ha)) hnC
  have hbt : b ∈ zpowers t := hdata.2.2.1 b hb (fun k hk =>
    (Subgroup.mem_centralizer_iff.mp hbC k hk).symm)
  exact H₀.mul_mem (hAH ha) (Subgroup.zpowers_le.mpr (h.center_le htc) hbt)


theorem two_le_pRank_cent (F : KI6BFacts) (h : Cfg H T H₀)
    (hr : ∀ L : Subgroup H, IsComponent L → Open.pRank 2 L ≤ 1) {t : H} (htc : t ∈ center H)
    (ht2 : orderOf t = 2) {K : Subgroup H} (hK : IsComponent K) {y x : H} (hyK : y ∈ K)
    (hy4 : orderOf y = 4) (hxT : x ∈ (T : Subgroup H)) (hxC : x ∈ centralizer (K : Set H))
    (hxt : x ∉ zpowers t) : 2 ≤ Open.pRank 2 (zpowers y ⊔ zpowers x) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdata := component_data F h htc ht2 hK (hr K hK)
  have hx2 : ∃ n : ℕ, x ^ (2 ^ n) = 1 := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp T.isPGroup') ⟨x, hxT⟩
    refine ⟨n, ?_⟩
    have h1 := (Subgroup.orderOf_coe (⟨x, hxT⟩ : ↥(T : Subgroup H))).trans hn
    rw [← h1]; exact pow_orderOf_eq_one x
  exact two_le_pRank_of_order_four F h htc ht2 hK (hr K hK) hyK hy4
    (Subgroup.mem_centralizer_iff.mp hxC y hyK) hxt hx2
    (fun g hg1 hg2 => hdata.2.2.1 g (Subgroup.zpowers_le.mpr hyK hg1) (fun k' hk' => by
      have hgc : g ∈ centralizer (K : Set H) := (Subgroup.zpowers_le.mpr hxC) hg2
      exact (Subgroup.mem_centralizer_iff.mp hgc k' hk').symm))

theorem Cfg.centralizer_component_le (F : KI6BFacts) (h : Cfg H T H₀)
    (hr : ∀ L : Subgroup H, IsComponent L → Open.pRank 2 L ≤ 1) {t : H} (htc : t ∈ center H)
    (ht2 : orderOf t = 2) {K₁ : Subgroup H} (hK₁ : IsComponent K₁) (hK₁H : ¬ K₁ ≤ H₀)
    (huniq : ∀ K₂ : Subgroup H, IsComponent K₂ → ¬ K₂ ≤ H₀ → K₂ = K₁) :
    centralizer (K₁ : Set H) ≤ H₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hFH := h.generalizedFitting_sup_eq_top F hr htc ht2
  have hKn := h.normal_of_unique hFH hK₁ hK₁H huniq
  have hoth : ∀ K₂ : Subgroup H, IsComponent K₂ → K₂ ≠ K₁ → K₂ ≤ H₀ := fun K₂ h2 hne => by
    by_contra hnot
    exact hne (huniq K₂ h2 hnot)
  have hNH := h.cent_inf_fitting_le F hr htc ht2 hK₁ hoth
  have hCn : (centralizer (K₁ : Set H)).Normal := centralizer_normal_of_normal hKn
  have hFn : (generalizedFitting H).Normal := generalizedFitting_normal
  set N : Subgroup H := centralizer (K₁ : Set H) ⊓ generalizedFitting H with hNdef
  have hNn : N.Normal := inferInstance
  let P : Sylow 2 ↥N := CFSG.BenderSuzuki.External.hallSylowSubgroupOfNormal T N
  set P' : Subgroup H := (P : Subgroup ↥N).map N.subtype with hP'
  have hP'T : P' ≤ (T : Subgroup H) := by
    rw [hP', CFSG.BenderSuzuki.External.hallSylowSubgroupOfNormal_coe]
    exact Subgroup.map_comap_le _ _
  have hP'N : P' ≤ N := Subgroup.map_subtype_le _
  have hmemP' : ∀ x : H, x ∈ N → x ∈ (T : Subgroup H) → x ∈ P' := by
    intro x hxN hxT
    refine ⟨⟨x, hxN⟩, ?_, rfl⟩
    rw [CFSG.BenderSuzuki.External.hallSylowSubgroupOfNormal_coe]
    exact hxT
  have hfrat := Sylow.normalizer_sup_eq_top P
  obtain ⟨y, hyK, hyT, hy4⟩ := exists_orderFour_mem F h htc ht2 hK₁ (hr K₁ hK₁)
  obtain ⟨x, hxT, hxC, hxF, hxt⟩ := exists_noncentral_cent F h hr htc ht2 hK₁
  have hxP' : x ∈ P' := hmemP' x ⟨hxC, hxF⟩ hxT
  have hrank0 := two_le_pRank_cent F h hr htc ht2 hK₁ hyK hy4 hxT hxC hxt
  have hmono : zpowers y ⊔ zpowers x ≤ P' ⊔ zpowers y :=
    sup_le le_sup_right (le_sup_of_le_left (Subgroup.zpowers_le.mpr hxP'))
  have hrank : 2 ≤ Open.pRank 2 (P' ⊔ zpowers y) :=
    hrank0.trans (SU1.pRank_mono (by norm_num) hmono)
  have hDT : P' ⊔ zpowers y ≤ H₀ :=
    sup_le (hP'T.trans h.sylow_le) (Subgroup.zpowers_le.mpr (h.sylow_le hyT))
  intro c hc
  have hc' : c ∈ normalizer (P' : Set H) ⊔ N := by rw [hfrat]; trivial
  rw [← SetLike.mem_coe, Subgroup.mul_normal] at hc'
  obtain ⟨g, hg, n, hn, hgn⟩ := Set.mem_mul.mp hc'
  have hnC : n ∈ centralizer (K₁ : Set H) := hn.1
  have hgC : g ∈ centralizer (K₁ : Set H) := by
    have : g = c * n⁻¹ := by rw [← hgn]; group
    rw [this]
    exact Subgroup.mul_mem _ hc (Subgroup.inv_mem _ hnC)
  have hgH : g ∈ H₀ := by
    apply two_generated_core_subgroup_normalizer_le T H₀ h.sylow_le h.gamma _ hDT hrank
    apply mem_normalizer_sup_of_centralizes ?_ hg ?_
    · intro a ha b hb
      have hbK : b ∈ K₁ := Subgroup.zpowers_le.mpr hyK hb
      exact (Subgroup.mem_centralizer_iff.mp (hP'N ha).1 b hbK).symm
    · intro b hb
      have hbK : b ∈ K₁ := Subgroup.zpowers_le.mpr hyK hb
      exact (Subgroup.mem_centralizer_iff.mp hgC b hbK).symm
  rw [← hgn]
  exact H₀.mul_mem hgH (hNH hn)

end CFSG.GH74.Uniqueness.SU.K.R6
