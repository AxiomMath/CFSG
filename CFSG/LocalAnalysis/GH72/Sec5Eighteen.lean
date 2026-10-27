module

public import CFSG.LocalAnalysis.GH72.Sec5DTools
public import CFSG.LocalAnalysis.GH72.Sec5Roles
public import CFSG.LocalAnalysis.GH72.Sec5BarType
public import CFSG.LocalAnalysis.GH72.GWTwoExtension

public section

namespace CFSG.GH72

open Subgroup
open scoped Pointwise

namespace G5d

variable {G : Type*} [Group G]

private theorem mem_normalizer_commutator_of_mem {H K : Subgroup G} {g : G}
    (hH : g ∈ normalizer (H : Set G)) (hK : g ∈ normalizer (K : Set G)) :
    g ∈ normalizer ((⁅H, K⁆ : Subgroup G) : Set G) := by
  rw [G4b.mem_normalizer_iff_map_conj_eq'] at hH hK ⊢
  rw [Subgroup.map_commutator, hH, hK]

variable [Finite G]

theorem le_centralizer_of_le_centralizer_commutator {T Q X Y : Subgroup G}
    (hQX : Q ≤ centralizer (X : Set G))
    (hTQ : (T : Set G) * (Q : Set G) = (Q : Set G) * (T : Set G))
    (hYQ : Y ≤ normalizer (Q : Set G))
    (h : Q ⊓ centralizer ((⁅T, X⁆ : Subgroup G) : Set G) = ⊥)
    (hY : Y ≤ centralizer ((⁅T, X⁆ : Subgroup G) : Set G)) : Y ≤ centralizer (Q : Set G) := by
  have hQE : Q ≤ normalizer ((⁅T, X⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator_of_mul_comm hQX hTQ
  intro y hy
  rw [mem_centralizer_iff]
  intro q hq
  have hc : y * q * y⁻¹ * q⁻¹ ∈ Q ⊓ centralizer ((⁅T, X⁆ : Subgroup G) : Set G) := by
    refine ⟨Q.mul_mem ((mem_normalizer_iff.mp (hYQ hy) q).mp hq) (Q.inv_mem hq), ?_⟩
    have h1 : q * y⁻¹ * q⁻¹ ∈ centralizer ((⁅T, X⁆ : Subgroup G) : Set G) :=
      (mem_normalizer_iff.mp (G4b.mem_normalizer_centralizer (hQE hq)) y⁻¹).mp
        ((centralizer _).inv_mem (hY hy))
    have h2 : y * q * y⁻¹ * q⁻¹ = y * (q * y⁻¹ * q⁻¹) := by group
    rw [h2]
    exact (centralizer _).mul_mem (hY hy) h1
  rw [h, mem_bot] at hc
  calc q * y = (y * q * y⁻¹ * q⁻¹)⁻¹ * (y * q) := by group
    _ = y * q := by rw [hc, inv_one, one_mul]

theorem covers_C_inf_normalizer_of_isSylowOf {t : ℕ} [Fact t.Prime] {X T M₀ : Subgroup G}
    {x₁ : G} (hX2 : IsPGroup 2 X) (hXc : X ≤ centralizer (X : Set G)) (hx₁ : x₁ ∈ X)
    (hXT : X ≤ normalizer (T : Set G)) (hT : ABGLocalTools.IsSylowOf t T (O (C x₁)))
    (hM₀ : M₀ ≤ centralizer (X : Set G)) (hOM₀ : O (centralizer (X : Set G)) ≤ M₀) :
    Covers (C x₁ ⊓ normalizer (T : Set G)) M₀ (O (centralizer (X : Set G))) := by
  have hXK : X ≤ C x₁ := fun x hx =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (hXc hx) x₁ hx₁).symm
  have hMK : centralizer (X : Set G) ≤ C x₁ := centralizer_le (Set.singleton_subset_iff.mpr hx₁)
  have hXN : X ≤ normalizer ((C x₁ ⊓ normalizer (T : Set G) : Subgroup G) : Set G) :=
    fun x hx => inf_normalizer_le_normalizer_inf ⟨le_normalizer (hXK hx), le_normalizer (hXT hx)⟩
  have hFr : C x₁ = O (C x₁) ⊔ (C x₁ ⊓ normalizer (T : Set G)) :=
    eq_sup_inf_normalizer_of_isSylowOf (map_subtype_le _) (le_normalizer_O _) hT
  have hcov : Covers (C x₁) M₀ (O (centralizer (X : Set G))) :=
    fun m hm => mem_sup_left ⟨hMK (hM₀ hm), hm⟩
  exact covers_of_eq_O_sup hX2 hXK hXN inf_le_left hFr rfl hM₀ hOM₀ (O_inf_le_O_of_le hMK) hcov

theorem covers_centralizer_inf_normalizer_commutator {t : ℕ} [Fact t.Prime] {X T M₀ : Subgroup G}
    {x₁ : G} (hX2 : IsPGroup 2 X) (hXc : X ≤ centralizer (X : Set G)) (hx₁ : x₁ ∈ X)
    (hXT : X ≤ normalizer (T : Set G)) (hT : ABGLocalTools.IsSylowOf t T (O (C x₁)))
    (hM₀ : M₀ ≤ centralizer (X : Set G)) (hOM₀ : O (centralizer (X : Set G)) ≤ M₀) :
    Covers (centralizer (X : Set G) ⊓ normalizer ((⁅T, X⁆ : Subgroup G) : Set G)) M₀
      (O (centralizer (X : Set G))) := by
  have h := covers_C_inf_normalizer_of_isSylowOf hX2 hXc hx₁ hXT hT hM₀ hOM₀
  unfold Covers at h ⊢
  refine h.trans (sup_le_sup_right ?_ _)
  rintro m ⟨⟨-, hmT⟩, hmM₀⟩
  exact ⟨⟨hM₀ hmM₀, mem_normalizer_commutator_of_mem hmT
    (centralizer_le_normalizer _ (hM₀ hmM₀))⟩, hmM₀⟩

theorem le_O_of_le_centralizer_of_covers {X Y E M₀ M Ms L₀ D : Subgroup G}
    (hM : M = centralizer (X : Set G)) (hMs : Ms = M ⊓ normalizer (E : Set G))
    (hX2 : IsPGroup 2 X) (hXc : X ≤ centralizer (X : Set G)) (hY2 : IsPGroup 2 Y)
    (hYX : Y ≤ centralizer (X : Set G)) (hYc : Y ≤ centralizer (Y : Set G)) (hXY : X ⊓ Y = ⊥)
    (hsyl : ABGLocalTools.IsSylowOf 2 (X ⊔ Y) (centralizer ((X ⊔ Y : Subgroup G) : Set G)))
    (hM₀ : M₀ ≤ M) (hMM₀ : M ≤ normalizer (M₀ : Set G)) (hYM₀ : Y ≤ M₀)
    (hcen : ∀ m ∈ M₀, (∀ m' ∈ M₀, m * m' * m⁻¹ * m'⁻¹ ∈ O M) → m ∈ O M)
    (hYE' : ¬ Y ≤ centralizer (E : Set G))
    (hL₀Ms : L₀ ≤ Ms) (hL₀M₀ : L₀ ≤ M₀) (hYL₀ : Y ≤ L₀ ⊔ O Ms) (hcov : M₀ ≤ L₀ ⊔ O M)
    (hL : ((L₀ ⊔ O Ms).subgroupOf Ms).Normal) (hs : IsSimpleGroup (bar Ms L₀))
    (hO : O Ms ⊓ M₀ ≤ O M)
    (hDM : D ≤ M) (hDE : D ≤ centralizer (E : Set G)) (hD : Odd (Nat.card D)) : D ≤ O M := by
  subst hM
  have hMsM : Ms ≤ centralizer (X : Set G) := by rw [hMs]; exact inf_le_left
  have hMsE : Ms ≤ normalizer (E : Set G) := by rw [hMs]; exact inf_le_right
  have hHZ₀ : Ms ≤ normalizer ((Ms ⊓ centralizer (E : Set G) : Subgroup G) : Set G) :=
    fun g hg => inf_normalizer_le_normalizer_inf
      ⟨le_normalizer hg, G4b.mem_normalizer_centralizer (hMsE hg)⟩
  have hOMs : O Ms ≤ normalizer ((Ms ⊓ centralizer (E : Set G) : Subgroup G) : Set G) :=
    (map_subtype_le _).trans hHZ₀
  rcases le_sup_O_or_commutator_mem_O hL₀Ms inf_le_left hHZ₀ hL hs with h1 | h2
  ·
    exfalso
    apply hYE'
    intro y hy
    obtain ⟨z, hz, o, ho, hzo⟩ := mem_sup_of_le_normalizer hOMs
      ((sup_le h1 le_sup_right) (hYL₀ hy))
    have hy2 : IsPGroup 2 (zpowers (z * o)) := by
      rw [hzo]
      exact hY2.to_le (zpowers_le.mpr hy)
    have := mem_of_mul_mem_of_isPGroup_two hOMs (card_O_odd Ms) hz ho hy2
    rw [hzo] at this
    exact this.2
  ·
    refine le_O_of_commutator_mem_O hX2 hXc hY2 hYX hYc hXY hsyl hM₀ hMM₀ hYM₀ hcen hDM hD ?_
    intro d hd m hm
    have hON : centralizer (X : Set G) ≤ normalizer (O (centralizer (X : Set G)) : Set G) :=
      le_normalizer_O _
    obtain ⟨m', hm', o', ho', rfl⟩ :=
      mem_sup_of_le_normalizer' ((hL₀Ms.trans hMsM).trans hON) (hcov hm)
    have hdM : d ∈ centralizer (X : Set G) := hDM hd
    have hdZ₀ : d ∈ Ms ⊓ centralizer (E : Set G) := by
      refine ⟨?_, hDE hd⟩
      rw [hMs]
      exact ⟨hdM, centralizer_le_normalizer _ (hDE hd)⟩
    have hc1 : d * m' * d⁻¹ * m'⁻¹ ∈ O (centralizer (X : Set G)) := by
      refine hO ⟨h2 d hdZ₀ m' hm', ?_⟩
      exact M₀.mul_mem ((mem_normalizer_iff.mp (hMM₀ hdM) m').mp (hL₀M₀ hm'))
        (M₀.inv_mem (hL₀M₀ hm'))
    have hc2 : d * o' * d⁻¹ * o'⁻¹ ∈ O (centralizer (X : Set G)) :=
      (O _).mul_mem ((mem_normalizer_iff.mp (hON hdM) o').mp ho') ((O _).inv_mem ho')
    have heq : d * (m' * o') * d⁻¹ * (m' * o')⁻¹ =
        (d * m' * d⁻¹ * m'⁻¹) * (m' * (d * o' * d⁻¹ * o'⁻¹) * m'⁻¹) := by group
    rw [heq]
    exact (O _).mul_mem hc1 ((mem_normalizer_iff.mp (hON (hMsM (hL₀Ms hm'))) _).mp hc2)

omit [Finite G] in
theorem pCore_sup_eq_bot_of_inf_centralizer_le {p t : ℕ} [Fact p.Prime] [Fact t.Prime]
    (hpt : p ≠ t) {A P T E Q : Subgroup G} (hP : IsMaxInvIn p A ⊤ P)
    (hAT : A ≤ normalizer (T : Set G)) (hE : IsPGroup t E) (hEPT : E ≤ P ⊔ T)
    (hPTE : P ⊔ T ≤ normalizer (E : Set G)) (hD : P ⊓ centralizer (E : Set G) ≤ Q)
    (h : Q ⊓ centralizer (E : Set G) = ⊥) : CFSG.pCore p ↥(P ⊔ T) = ⊥ := by
  obtain ⟨R, hR⟩ : ∃ R : Subgroup G, R = (CFSG.pCore p ↥(P ⊔ T)).map (P ⊔ T).subtype :=
    ⟨_, rfl⟩
  have hRp : IsPGroup p R := by
    rw [hR]
    exact CFSG.pCore_isPGroup.map _
  have hRPT : R ≤ P ⊔ T := by
    rw [hR]
    exact map_subtype_le _
  have hPTR : P ⊔ T ≤ normalizer (R : Set G) := by
    rw [hR]
    exact le_normalizer.trans (normalizer_le_normalizer_pCore_map p _)
  have hAR : A ≤ normalizer (R : Set G) := by
    intro a ha
    rw [hR]
    exact normalizer_le_normalizer_pCore_map p _ (mem_normalizer_sup (hP.2.2.1 ha) (hAT ha))
  have hRP : R ≤ P := by
    have h2 : IsPGroup p (R ⊔ P : Subgroup G) :=
      IsPGroup.to_sup_of_normal_left' hRp hP.2.1 (le_sup_left.trans hPTR)
    have h3 := hP.2.2.2 (R ⊔ P) le_top h2 (fun a ha => mem_normalizer_sup (hAR ha) (hP.2.2.1 ha))
      le_sup_right
    exact le_sup_left.trans h3.le
  have hRE : R ≤ centralizer (E : Set G) := by
    have hdisj : R ⊓ E = ⊥ := (IsPGroup.disjoint_of_ne p t hpt R E hRp hE).eq_bot
    intro r hr
    rw [mem_centralizer_iff]
    intro e he
    have hc : r * e * r⁻¹ * e⁻¹ ∈ R ⊓ E := by
      refine ⟨?_, ?_⟩
      · have h1 : r * e * r⁻¹ * e⁻¹ = r * (e * r⁻¹ * e⁻¹) := by group
        rw [h1]
        exact R.mul_mem hr ((mem_normalizer_iff.mp (hPTR (hEPT he)) r⁻¹).mp (R.inv_mem hr))
      · exact E.mul_mem ((mem_normalizer_iff.mp (hPTE (hRPT hr)) e).mp he) (E.inv_mem he)
    rw [hdisj, mem_bot] at hc
    calc e * r = (r * e * r⁻¹ * e⁻¹)⁻¹ * (r * e) := by group
      _ = r * e := by rw [hc, inv_one, one_mul]
  have hR1 : R = ⊥ := by
    rw [eq_bot_iff, ← h]
    exact le_inf ((le_inf hRP hRE).trans hD) hRE
  rwa [hR, map_eq_bot_iff_of_injective _ (P ⊔ T).subtype_injective] at hR1

section Inputs

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_section_of_W {H M₀ M Y W : Subgroup G} {q : ℕ} (hM₀M : M₀ ≤ M)
    (hWHM : W ≤ H ⊓ M₀) (hYW : Y ≤ W) (hcovW : Covers W M₀ (O M))
    (hHMW : H ⊓ M₀ ≤ W ⊔ (H ⊓ O M)) (hWn : ((W ⊔ O H).subgroupOf H).Normal)
    (hOW : O H ⊓ W = W ⊓ O M) (hWs : IsL2OrA7 (bar H W) q)
    (hcW : bar H (H ⊓ O M) ≤ centralizer ((bar H W : Subgroup (Bar H)) : Set (Bar H))) :
    O H ⊓ M₀ ≤ O M ∧ ∃ L₀ : Subgroup G, L₀ ≤ H ∧ L₀ ≤ M₀ ∧ Y ≤ L₀ ⊔ O H ∧ M₀ ≤ L₀ ⊔ O M ∧
      ((L₀ ⊔ O H).subgroupOf H).Normal ∧ IsL2OrA7 (bar H L₀) q := by
  have hWH : W ≤ H := hWHM.trans inf_le_left
  have hWM₀ : W ≤ M₀ := hWHM.trans inf_le_right
  refine ⟨?_, W, hWH, hWM₀, hYW.trans le_sup_left,
    hcovW.trans (sup_le_sup_right inf_le_left _), hWn, hWs⟩
  rintro x ⟨hxO, hxM₀⟩
  have hxH : x ∈ H := map_subtype_le _ hxO
  have hWN : W ≤ normalizer ((H ⊓ O M : Subgroup G) : Set G) := fun w hw =>
    inf_normalizer_le_normalizer_inf
      ⟨le_normalizer (hWH hw), le_normalizer_O _ (hM₀M (hWM₀ hw))⟩
  have hx : x ∈ (H ⊓ O M) ⊔ W := by
    rw [sup_comm]
    exact hHMW ⟨hxH, hxM₀⟩
  obtain ⟨o, ho, w, hw, rfl⟩ := mem_sup_of_le_normalizer hWN hx
  set π := QuotientGroup.mk' (CFSG.oddCore H) with hπ
  have h1 : π ⟨o, ho.1⟩ * π ⟨w, hWH hw⟩ = 1 := by
    rw [← map_mul, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    obtain ⟨y, hy, hyx⟩ := hxO
    have : y = ⟨o, ho.1⟩ * ⟨w, hWH hw⟩ := Subtype.ext hyx
    rwa [← this]
  have hwc : π ⟨w, hWH hw⟩ ∈ centralizer ((bar H W : Subgroup (Bar H)) : Set (Bar H)) := by
    have hob : π ⟨o, ho.1⟩ ∈ bar H (H ⊓ O M) :=
      mem_map_of_mem _ (show (⟨o, ho.1⟩ : H) ∈ (H ⊓ O M).subgroupOf H from ho)
    have : π ⟨w, hWH hw⟩ = (π ⟨o, ho.1⟩)⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [this]
    exact (centralizer _).inv_mem (hcW hob)
  have hwb : π ⟨w, hWH hw⟩ ∈ bar H W :=
    mem_map_of_mem _ (show (⟨w, hWH hw⟩ : H) ∈ W.subgroupOf H from hw)
  have hcen : (⟨π ⟨w, hWH hw⟩, hwb⟩ : bar H W) ∈ center (bar H W) := by
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (mem_centralizer_iff.mp hwc g g.2)
  rw [CFSG.GH72.center_eq_bot_of_isL2OrA7 hWs, mem_bot] at hcen
  have hw1 : π ⟨w, hWH hw⟩ = 1 := congrArg Subtype.val hcen
  rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hw1
  have hwO : w ∈ O H ⊓ W := ⟨⟨_, hw1, rfl⟩, hw⟩
  rw [hOW] at hwO
  exact (O M).mul_mem ho.2 hwO.2

end Inputs

end G5d

namespace Sec5Roles

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} (ρ : Sec5Roles G A)

theorem exists_section_of_h1R
    (hHns : QuotIs ρ.M₀ (O ρ.M) (fun L _ => IsL2OrA7 L 5))
    (h1M : ∀ H : Subgroup G, H ≠ ⊤ → A ≤ H → Covers H ρ.M₀ (O ρ.M) →
      ∃ W : Subgroup G, W ≤ H ⊓ ρ.M₀ ∧ ρ.Y ≤ W ∧ Covers W ρ.M₀ (O ρ.M) ∧
        H ⊓ ρ.M₀ ≤ W ⊔ (H ⊓ O ρ.M) ∧ ((W ⊔ O H).subgroupOf H).Normal ∧
        O H ⊓ W = W ⊓ O ρ.M ∧
        (IsL2OrA7 (bar H W) 5 ∨ (bar H W = bar H ρ.Y ∧ IsKleinFour (bar H W))) ∧
        bar H (H ⊓ O ρ.M) ≤ centralizer (bar H W : Set (Bar H)) ∧
        bar H (H ⊓ O ρ.M) ≤ centralizer (bar H A : Set (Bar H)))
    {H : Subgroup G} (hH : H ≠ ⊤) (hAH : A ≤ H) (hcov : Covers H ρ.M₀ (O ρ.M)) :
    O H ⊓ ρ.M₀ ≤ O ρ.M ∧ ∃ L₀ : Subgroup G, L₀ ≤ H ∧ L₀ ≤ ρ.M₀ ∧
      ρ.Y ≤ L₀ ⊔ O H ∧ ρ.M₀ ≤ L₀ ⊔ O ρ.M ∧ ((L₀ ⊔ O H).subgroupOf H).Normal ∧
      IsL2OrA7 (bar H L₀) 5 := by
  obtain ⟨W, hWHM, hYW, hcovW, hHMW, hWn, hOW, -, hcW, -⟩ := h1M H hH hAH hcov
  exact G5d.exists_section_of_W ρ.M₀_le hWHM hYW hcovW hHMW hWn hOW
    (G5d.isL2OrA7_bar_of_covers (hWHM.trans inf_le_left) (hWHM.trans inf_le_right)
      ρ.M₀_le_normalizer_O_M hcovW hOW hHns) hcW

end Sec5Roles

namespace Sec5ConfigR

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {ρ : Sec5Roles G A} {p : ℕ}

theorem inf_O_M_le_Q (𝔠 : Sec5ConfigR ρ p) : 𝔠.P ⊓ O ρ.M ≤ 𝔠.Q := by
  have : Fact p.Prime := ⟨𝔠.hp⟩
  have hA2 : IsPGroup 2 A := ρ.isPGroup_A
  have hXA : ρ.X ≤ A := ρ.X_le_A
  have hAH₀ : A ≤ 𝔠.H₀ := le_sup_right.trans 𝔠.hH₀.1
  have hPH₀ : 𝔠.P ≤ 𝔠.H₀ := le_sup_left.trans 𝔠.hH₀.1
  have hAQ : A ≤ normalizer (𝔠.Q : Set G) := fun a ha =>
    inf_normalizer_le_normalizer_inf ⟨𝔠.hP.2.2.1 ha, le_normalizer_O _ (hAH₀ ha)⟩
  have hQsyl : ABGLocalTools.IsSylowOf p 𝔠.Q (O 𝔠.H₀) :=
    isSylowOf_inf_O_of_isMaxInvIn 𝔠.hp hA2 (hAH₀.trans le_normalizer)
      (IsMaxInvIn.of_le 𝔠.hP hPH₀ le_top)
  exact G5d.inf_O_centralizer_le (Q := 𝔠.Q) (H₁ := 𝔠.H₀ ⊓ normalizer (𝔠.Q : Set G)) rfl rfl
    hPH₀ hQsyl (hA2.to_le hXA) (le_inf (hXA.trans hAH₀) (hXA.trans hAQ)) 𝔠.hH₁.2.2.1

end Sec5ConfigR

open G5d

namespace Sec5ConfigTR

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {ρ : Sec5Roles G A} {p : ℕ}
  {𝔠 : Sec5ConfigR ρ p} (𝔱 : Sec5ConfigTR 𝔠)

theorem lemma_5_18_of
    (h47 : QuotIs ρ.M₀ (O ρ.M) (fun L _ => IsL2OrA7 L 5 ∨ IsKleinFour L) ∧
      CFSG.ABGLocalTools.IsSylowOf 2 ρ.S₂ ρ.M₀ ∧
      ρ.M = ρ.M₀ ⊔ (ρ.M ⊓ normalizer (A : Set G)) ∧
      ρ.M = ρ.M₀ ⊔ (ρ.M ⊓ normalizer (ρ.S₂ : Set G)) ∧
      (∀ x ∈ ρ.X, x ≠ 1 → O2 (C x) = (O2 ρ.M ⊓ O2 (C x)) ⊔ O (C x)) ∧
      (∀ x ∈ ρ.X, x ≠ 1 → ⁅O2 (C x), O2 (C x)⁆ ⊔ O (C x) =
        (ρ.M₀ ⊓ ⁅O2 (C x), O2 (C x)⁆) ⊔ O (C x)))
    (hHns : QuotIs ρ.M₀ (O ρ.M) (fun L _ => IsL2OrA7 L 5))
    (h1M : ∀ H : Subgroup G, H ≠ ⊤ → A ≤ H → Covers H ρ.M₀ (O ρ.M) →
      ∃ W : Subgroup G, W ≤ H ⊓ ρ.M₀ ∧ ρ.Y ≤ W ∧ Covers W ρ.M₀ (O ρ.M) ∧
        H ⊓ ρ.M₀ ≤ W ⊔ (H ⊓ O ρ.M) ∧ ((W ⊔ O H).subgroupOf H).Normal ∧
        O H ⊓ W = W ⊓ O ρ.M ∧
        (IsL2OrA7 (bar H W) 5 ∨ (bar H W = bar H ρ.Y ∧ IsKleinFour (bar H W))) ∧
        bar H (H ⊓ O ρ.M) ≤ centralizer (bar H W : Set (Bar H)) ∧
        bar H (H ⊓ O ρ.M) ≤ centralizer (bar H A : Set (Bar H)))
    (h : 𝔠.Q ⊓ centralizer ((⁅𝔱.T, ρ.X⁆ : Subgroup G) : Set G) = ⊥) :
    CFSG.pCore p (𝔠.P ⊔ 𝔱.T : Subgroup G) = ⊥ := by
  have : Fact p.Prime := ⟨𝔠.hp⟩
  have : Fact 𝔱.t.Prime := ⟨𝔱.ht.1⟩
  have hA2 : IsPGroup 2 A := ρ.isPGroup_A
  have hXA : ρ.X ≤ A := ρ.X_le_A
  have hYA : ρ.Y ≤ A := ρ.Y_le_A
  have hAX : A ≤ centralizer (ρ.X : Set G) := fun a ha =>
    mem_centralizer_iff.mpr fun x hx => ρ.comm (hXA hx) ha
  have hAY : A ≤ centralizer (ρ.Y : Set G) := fun a ha =>
    mem_centralizer_iff.mpr fun y hy => ρ.comm (hYA hy) ha
  have hPX : 𝔠.P ≤ centralizer (ρ.X : Set G) := 𝔱.hXP
  have hQP : 𝔠.Q ≤ 𝔠.P := inf_le_left
  have hAH₀ : A ≤ 𝔠.H₀ := le_sup_right.trans 𝔠.hH₀.1
  have hAQ : A ≤ normalizer (𝔠.Q : Set G) := fun a ha =>
    inf_normalizer_le_normalizer_inf ⟨𝔠.hP.2.2.1 ha, le_normalizer_O _ (hAH₀ ha)⟩
  have hAT : A ≤ normalizer (𝔱.T : Set G) := 𝔱.hT.2.2.1
  have hAE : A ≤ normalizer ((⁅𝔱.T, ρ.X⁆ : Subgroup G) : Set G) := fun a ha =>
    mem_normalizer_commutator_of_mem (hAT ha) (centralizer_le_normalizer _ (hAX ha))
  have hYE' : ¬ ρ.Y ≤ centralizer ((⁅𝔱.T, ρ.X⁆ : Subgroup G) : Set G) := fun hY =>
    𝔠.hH₁.1 (le_centralizer_of_le_centralizer_commutator (hQP.trans hPX) 𝔱.hT.2.2.2.1
      (hYA.trans hAQ) h hY)
  have hE1 : (⁅𝔱.T, ρ.X⁆ : Subgroup G) ≠ ⊥ := by
    intro hbot
    apply hYE'
    rw [hbot]
    intro y _
    rw [mem_centralizer_iff]
    intro e he
    rw [SetLike.mem_coe, mem_bot] at he
    rw [he, one_mul, mul_one]
  have hET : (⁅𝔱.T, ρ.X⁆ : Subgroup G) ≤ 𝔱.T :=
    le_normalizer_iff_commutator_le_left.mp (hXA.trans hAT)
  have hEt : IsPGroup 𝔱.t (⁅𝔱.T, ρ.X⁆ : Subgroup G) := 𝔱.hT.2.1.isPGroup.to_le hET
  have hPTE : 𝔠.P ⊔ 𝔱.T ≤ normalizer ((⁅𝔱.T, ρ.X⁆ : Subgroup G) : Set G) :=
    sup_le (le_normalizer_commutator_of_mul_comm hPX 𝔱.hT.2.2.2.2)
      (normalizer_commutator_ge_left _ _)
  have hcov : Covers (ρ.M ⊓ normalizer ((⁅𝔱.T, ρ.X⁆ : Subgroup G) : Set G)) ρ.M₀ (O ρ.M) :=
    covers_centralizer_inf_normalizer_commutator (hA2.to_le hXA) (hXA.trans hAX) 𝔱.hx₁.1
      (hXA.trans hAT) 𝔱.hT.2.1 ρ.M₀_le ρ.O_M_le_M₀
  have hMstop : ρ.M ⊓ normalizer ((⁅𝔱.T, ρ.X⁆ : Subgroup G) : Set G) ≠ ⊤ := by
    intro htop
    refine ρ.ne_top_of_isPLocal 𝔱.ht.1 𝔱.ht.2.1 ⟨_, hE1, hEt, rfl⟩ (eq_top_iff.mpr ?_)
    rw [← htop]
    exact inf_le_right
  obtain ⟨hO, L₀, hL₀Ms, hL₀M₀, hYL₀, hcovL₀, hL, hs⟩ :=
    ρ.exists_section_of_h1R hHns h1M hMstop (le_inf hAX hAE) hcov
  have hsyl : ABGLocalTools.IsSylowOf 2 (ρ.X ⊔ ρ.Y)
      (centralizer ((ρ.X ⊔ ρ.Y : Subgroup G) : Set G)) := by
    rw [ρ.X_sup_Y]
    exact ρ.isSylowOf_centralizer
  have hDodd : Odd (Nat.card (𝔠.P ⊓ centralizer ((⁅𝔱.T, ρ.X⁆ : Subgroup G) : Set G) :
      Subgroup G)) := by
    obtain ⟨n, hn⟩ := (𝔠.hP.2.1.to_le inf_le_left).exists_card_eq
    rw [hn]
    exact (𝔠.hp.odd_of_ne_two 𝔠.hp2).pow
  have hDO : 𝔠.P ⊓ centralizer ((⁅𝔱.T, ρ.X⁆ : Subgroup G) : Set G) ≤ O ρ.M :=
    le_O_of_le_centralizer_of_covers (X := ρ.X) (Y := ρ.Y) (M := ρ.M) rfl rfl
      (hA2.to_le hXA) (hXA.trans hAX) (hA2.to_le hYA) (hYA.trans hAX) (hYA.trans hAY)
      ρ.X_inf_Y hsyl ρ.M₀_le
      (fun g hg => ρ.normalizer_X_le_normalizer_M₀ (centralizer_le_normalizer _ hg))
      (ρ.Y_le_S₂.trans h47.2.1.le)
      (fun m hm h' => mem_of_commutator_mem_of_quotIs hHns hm h') hYE'
      hL₀Ms hL₀M₀ hYL₀ hcovL₀ hL (isSimpleGroup_of_isL2OrA7 (by norm_num) hs) hO
      (inf_le_left.trans hPX) inf_le_right hDodd
  exact pCore_sup_eq_bot_of_inf_centralizer_le (Ne.symm 𝔱.ht.2.2) 𝔠.hP hAT hEt
    (hET.trans le_sup_right) hPTE (fun g hg => 𝔠.inf_O_M_le_Q ⟨hg.1, hDO hg⟩) h

end Sec5ConfigTR

end CFSG.GH72
