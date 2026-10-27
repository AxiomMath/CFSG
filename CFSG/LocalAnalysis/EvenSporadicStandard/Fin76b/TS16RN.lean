module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RNW
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RNConj
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RNUniq
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RH

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open

structure S16Gen {G : Type} [Group G] (S : Subgroup G) (s z t : G) : Prop where
  hs : s ∈ S
  hzS : z ∈ S
  hs8 : s ^ 8 = 1
  hs4 : s ^ 4 = t
  hz2 : z * z = 1
  hzs : z * s * z⁻¹ = s⁻¹
  hord : orderOf s = 8
  hzns : z ∉ zpowers s
  hgen : ∀ y ∈ S, ∃ i j : ℕ, y = s ^ i * z ^ j

namespace OuterS16Ctx

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  {Q : Sylow 2 G} {x : G} {B : Subgroup G} {β : G} {S : Subgroup G}
  (c : OuterS16Ctx G L z t T E Q x B β S)

include c

theorem sigma_norm_D {s : G} (hS : S16Gen S s z t) {σ : G} (hσz : σ * z = z * σ)
    (hσs : σ * s * σ⁻¹ = s ^ 5) : ∀ d ∈ Dsub s z, σ * d * σ⁻¹ ∈ Dsub s z := by
  have hσz' : σ * z * σ⁻¹ = z := by
    calc σ * z * σ⁻¹ = (z * σ) * σ⁻¹ := by rw [hσz]
      _ = z := by group
  have hle : Dsub s z ≤ (Dsub s z).comap (MulAut.conj σ).toMonoidHom := by
    unfold Dsub
    rw [Subgroup.closure_le]
    rintro y (rfl | rfl)
    · have h1 : σ * (s * s) * σ⁻¹ = s * s := by
        calc σ * (s * s) * σ⁻¹ = (σ * s * σ⁻¹) * (σ * s * σ⁻¹) := by group
          _ = s ^ 5 * s ^ 5 := by rw [hσs]
          _ = s ^ 8 * (s * s) := by group
          _ = s * s := by rw [hS.hs8, one_mul]
      show (MulAut.conj σ).toMonoidHom (s * s) ∈ Dsub s z
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [h1]
      exact a_mem_Dsub
    · have h1 : σ * (s * z) * σ⁻¹ = t * (s * z) := by
        calc σ * (s * z) * σ⁻¹ = (σ * s * σ⁻¹) * (σ * z * σ⁻¹) := by group
          _ = s ^ 5 * z := by rw [hσs, hσz']
          _ = s ^ 4 * (s * z) := by group
          _ = t * (s * z) := by rw [hS.hs4]
      show (MulAut.conj σ).toMonoidHom (s * z) ∈ Dsub s z
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [h1]
      exact mul_mem (t_mem_Dsub hS.hs4) b_mem_Dsub
  intro d hd
  have := hle hd
  simpa [MulAut.conj_apply] using this

theorem sigma_norm_W {s : G} (hS : S16Gen S s z t) {σ : G} (hσ2 : σ * σ = 1) (hσz : σ * z = z * σ)
    (hσs : σ * s * σ⁻¹ = s ^ 5) (hσE : σ ∈ normalizer (E : Set G)) :
    σ ∈ normalizer ((Dsub s z ⊔ E : Subgroup G) : Set G) := by
  have hσi : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσ2
  have key : ∀ w ∈ Dsub s z ⊔ E, σ * w * σ⁻¹ ∈ Dsub s z ⊔ E := by
    have hle : Dsub s z ⊔ E ≤ (Dsub s z ⊔ E).comap (MulAut.conj σ).toMonoidHom := by
      refine sup_le (fun d hd => ?_) (fun e he => ?_)
      · show (MulAut.conj σ).toMonoidHom d ∈ Dsub s z ⊔ E
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        exact mem_sup_left (c.sigma_norm_D hS hσz hσs d hd)
      · show (MulAut.conj σ).toMonoidHom e ∈ Dsub s z ⊔ E
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        exact mem_sup_right ((mem_normalizer_iff.1 hσE e).1 he)
    intro w hw
    have := hle hw
    simpa [MulAut.conj_apply] using this
  rw [mem_normalizer_iff]
  intro w
  constructor
  · exact key w
  · intro hw
    have := key _ hw
    have h2 : σ * (σ * w * σ⁻¹) * σ⁻¹ = w := by
      calc σ * (σ * w * σ⁻¹) * σ⁻¹ = (σ * σ) * w * (σ⁻¹ * σ⁻¹) := by group
        _ = w := by rw [hσ2, hσi, hσ2]; group
    rwa [h2] at this

theorem sigma_not_mem_W {s : G} (hS : S16Gen S s z t) {σ : G} (hσz : σ * z = z * σ)
    (hσL : σ ∉ L ⊔ zpowers z) : σ ∉ Dsub s z ⊔ E := by
  have hcfg := c.hyp.outerE.cfg
  have hELL : E ≤ L := c.hyp.wFacts.E_le
  have hDS : Dsub s z ≤ S := Dsub_le hS.hs hS.hzS
  have hDC : Dsub s z ≤ centralizer (E : Set G) := hDS.trans c.SC
  have hEcD : E ≤ centralizer ((Dsub s z : Subgroup G) : Set G) := fun e he =>
    mem_centralizer_iff.2 fun d hd => (mem_centralizer_iff.1 (hDC hd) e he).symm
  intro hσW
  obtain ⟨d, hd, e, he, hde⟩ := exists_mul_of_mem_sup_comm' hEcD hσW
  have hd' : d = σ * e⁻¹ := by rw [hde]; group
  have hez : e * z = z * e := hcfg.z_comm_of_mem_A (hELL he)
  have hez' : e⁻¹ * z = z * e⁻¹ := by
    calc e⁻¹ * z = e⁻¹ * (z * e) * e⁻¹ := by group
      _ = e⁻¹ * (e * z) * e⁻¹ := by rw [hez]
      _ = z * e⁻¹ := by group
  have hdz : d * z = z * d := by
    rw [hd']
    calc σ * e⁻¹ * z = σ * (e⁻¹ * z) := by group
      _ = σ * (z * e⁻¹) := by rw [hez']
      _ = (σ * z) * e⁻¹ := by group
      _ = (z * σ) * e⁻¹ := by rw [hσz]
      _ = z * (σ * e⁻¹) := by group
  have hnz : z ∉ Dsub s z := z_not_mem_Dsub hS.hz2 hS.hs8 hS.hzs hS.hord hS.hzns
  have htD : t ∈ Dsub s z := t_mem_Dsub hS.hs4
  have htE : t ∈ E := c.hyp.outerE.econfig.t_mem
  rcases c.hyp.centZ d (hDC hd) hdz with h1 | h1 | h1 | h1
  · apply hσL
    rw [h1, one_mul] at hde
    rw [hde]
    exact mem_sup_left (hELL he)
  · exact hnz (h1 ▸ hd)
  · apply hσL
    rw [h1] at hde
    rw [hde]
    exact mem_sup_left (L.mul_mem (hELL htE) (hELL he))
  · apply hnz
    have h2 : t⁻¹ * d ∈ Dsub s z := mul_mem (inv_mem htD) hd
    have h3 : t⁻¹ * d = z := by rw [h1]; group
    rwa [h3] at h2

theorem fusion_in_normW {s : G} (hS : S16Gen S s z t) {σ : G} (hσ2 : σ * σ = 1)
    (hσz : σ * z = z * σ) (hσL : σ ∉ L ⊔ zpowers z) (hσE : σ ∈ normalizer (E : Set G))
    (hσs : σ * s * σ⁻¹ = s ^ 5)
    (h9 : ∀ w ∈ Dsub s z ⊔ E, w * w = 1 → w ≠ 1 → ∃ g : G, g * t * g⁻¹ = w)
    (hE0 : Nonempty (↥E ≃* ↥(centralizer ({σ} : Set G) ⊓ (Dsub s z ⊔ E))))
    (hD0card : Nat.card ↥(centralizer
      ((centralizer ({σ} : Set G) ⊓ (Dsub s z ⊔ E) : Subgroup G) : Set G) ⊓ (Dsub s z ⊔ E)) = 8)
    (hD0gen : ∀ y ∈ centralizer
        ((centralizer ({σ} : Set G) ⊓ (Dsub s z ⊔ E) : Subgroup G) : Set G) ⊓ (Dsub s z ⊔ E),
      y ∈ Subgroup.closure {w | w ∈ centralizer
        ((centralizer ({σ} : Set G) ⊓ (Dsub s z ⊔ E) : Subgroup G) : Set G) ⊓ (Dsub s z ⊔ E) ∧
        w * w = 1})
    {g₀ : G} (hg₀ : g₀ * z * g₀⁻¹ = σ) :
    ∃ g : G, g ∈ normalizer ((Dsub s z ⊔ E : Subgroup G) : Set G) ∧ g * z * g⁻¹ = σ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcfg := c.hyp.outerE.cfg
  have hz2 := hcfg.z_sq
  have ht2 := hcfg.t_sq
  have ht1 := hcfg.t_ne
  have htE : t ∈ E := c.hyp.outerE.econfig.t_mem
  have hELL : E ≤ L := c.hyp.wFacts.E_le
  have hDS : Dsub s z ≤ S := Dsub_le hS.hs hS.hzS
  have hDC : Dsub s z ≤ centralizer (E : Set G) := hDS.trans c.SC
  have hD8 : Nat.card ↥(Dsub s z) = 8 :=
    card_Dsub hS.hs hS.hzS hS.hs8 hS.hz2 hS.hzs hS.hord hS.hzns hS.hgen c.card16
  have htD : t ∈ Dsub s z := t_mem_Dsub hS.hs4
  have hW128 : Nat.card ↥(Dsub s z ⊔ E) = 128 :=
    card_sup_eq hDC c.hyp.outerE.econfig.center ht2 ht1 htD htE hD8 c.hyp.wFacts.card_E
  have hσW := c.sigma_norm_W hS hσ2 hσz hσs hσE
  have hσnW := c.sigma_not_mem_W hS hσz hσL
  set W : Subgroup G := Dsub s z ⊔ E with hWdef
  set E0 : Subgroup G := centralizer ({σ} : Set G) ⊓ W with hE0def
  set D0 : Subgroup G := centralizer (E0 : Set G) ⊓ W with hD0def
  have hE0σ : E0 ≤ centralizer ({σ} : Set G) := inf_le_left
  have hE0W : E0 ≤ W := inf_le_right
  have hD0C : D0 ≤ centralizer (E0 : Set G) := inf_le_left
  have hD0W : D0 ≤ W := inf_le_right
  obtain ⟨g₁, hg₁z, hg₁E⟩ := exists_conj_of_equiv c hE0σ hE0
    (fun w hw h1 h2 => h9 w (hE0W hw) h1 h2) hg₀
  obtain ⟨hS₁2, hS₁C, hS₁max⟩ := conj_max_cent_gen g₁ c.S2 c.SC c.Smax
  rw [hg₁E] at hS₁C hS₁max
  set S₁ : Subgroup G := S.map (MulAut.conj g₁).toMonoidHom with hS₁def
  have hS₁card : Nat.card ↥S₁ = 16 := by
    rw [hS₁def, Subgroup.card_map_of_injective (MulAut.conj g₁).injective]
    exact c.card16
  have hσi : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσ2
  have hσC : σ ∈ centralizer (E0 : Set G) :=
    mem_centralizer_iff.2 fun y hy => mem_centralizer_singleton_iff.1 (hE0σ hy)
  have hσD0 : ∀ d ∈ D0, σ * d * σ⁻¹ ∈ D0 := by
    intro d hd
    refine ⟨?_, (mem_normalizer_iff.1 hσW d).1 (hD0W hd)⟩
    refine mem_centralizer_iff.2 fun y hy => ?_
    have hyσ : y * σ = σ * y := mem_centralizer_singleton_iff.1 (hE0σ hy)
    have hyσ' : y * σ⁻¹ = σ⁻¹ * y := by
      calc y * σ⁻¹ = σ⁻¹ * (σ * y) * σ⁻¹ := by group
        _ = σ⁻¹ * (y * σ) * σ⁻¹ := by rw [hyσ]
        _ = σ⁻¹ * y := by group
    have hyd : y * d = d * y := mem_centralizer_iff.1 (hD0C hd) y hy
    calc y * (σ * d * σ⁻¹) = (y * σ) * d * σ⁻¹ := by group
      _ = (σ * y) * d * σ⁻¹ := by rw [hyσ]
      _ = σ * (y * d) * σ⁻¹ := by group
      _ = σ * (d * y) * σ⁻¹ := by rw [hyd]
      _ = σ * d * (y * σ⁻¹) := by group
      _ = σ * d * (σ⁻¹ * y) := by rw [hyσ']
      _ = σ * d * σ⁻¹ * y := by group
  have hW2 : IsPGroup 2 W := IsPGroup.of_card (n := 7) (by rw [hW128]; norm_num)
  have hD02 : IsPGroup 2 D0 := hW2.to_le hD0W
  have hσnorm : zpowers σ ≤ normalizer (D0 : Set G) := by
    rw [zpowers_le, mem_normalizer_iff]
    intro d
    refine ⟨fun hd => hσD0 d hd, fun hd => ?_⟩
    have h1 := hσD0 _ hd
    have h2 : σ * (σ * d * σ⁻¹) * σ⁻¹ = d := by
      calc σ * (σ * d * σ⁻¹) * σ⁻¹ = (σ * σ) * d * (σ⁻¹ * σ⁻¹) := by group
        _ = d := by rw [hσ2, hσi, hσ2]; group
    rwa [h2] at h1
  set S₀ : Subgroup G := D0 ⊔ zpowers σ with hS₀def
  have hS₀2 : IsPGroup 2 S₀ := hD02.to_sup_of_normal_left' (isPGroup_zpowers_of_sq hσ2) hσnorm
  have hS₀C : S₀ ≤ centralizer (E0 : Set G) := sup_le hD0C (zpowers_le.2 hσC)
  have hσS₀ : σ ∈ S₀ := mem_sup_right (mem_zpowers σ)
  have hS₀card : Nat.card ↥S₀ = 16 := by
    have hle16 : Nat.card ↥S₀ ≤ 16 := by
      rw [← hS₁card]
      exact card_le_of_max hS₁C hS₁2 hS₁max hS₀2 hS₀C
    have hD0S₀ : D0 ≤ S₀ := le_sup_left
    have hdvd : 8 ∣ Nat.card ↥S₀ := by
      rw [← hD0card]
      exact Subgroup.card_dvd_of_le hD0S₀
    have hne : Nat.card ↥S₀ ≠ 8 := by
      intro h8
      have heq : D0 = S₀ := Subgroup.eq_of_le_of_card_ge hD0S₀ (by rw [h8, hD0card])
      apply hσnW
      exact hD0W (heq ▸ hσS₀)
    have hpos : 0 < Nat.card ↥S₀ := Nat.card_pos
    omega
  have hS₀max : ∀ R : Subgroup G, IsPGroup 2 R → R ≤ centralizer (E0 : Set G) → S₀ ≤ R → R ≤ S₀ :=
    maximal_of_card_eq hS₁C hS₁2 hS₁max hS₀C hS₀2 (by rw [hS₀card, hS₁card])
  obtain ⟨c1, hc1C, hc1⟩ := sylow_conj (Θ := centralizer (E0 : Set G)) hS₀C hS₁C hS₀2 hS₁2
    hS₀max hS₁max
  have hσS₁ : σ ∈ S₁ := ⟨z, c.zS, by simp [MulAut.conj_apply, ← hg₁z]⟩
  set g' : G := c1⁻¹ * g₁ with hg'def
  have hS₀S : ∀ y ∈ S₀, g'⁻¹ * y * g' ∈ S := by
    intro y hy
    have h1 : c1 * y * c1⁻¹ ∈ S₁ := (hc1 _).2 (by simpa [mul_assoc] using hy)
    obtain ⟨s2, hs2, hs2eq⟩ := h1
    have hs2eq' : g₁ * s2 * g₁⁻¹ = c1 * y * c1⁻¹ := by
      simpa [MulAut.conj_apply] using hs2eq
    have : g'⁻¹ * y * g' = s2 := by
      calc g'⁻¹ * y * g' = g₁⁻¹ * (c1 * y * c1⁻¹) * g₁ := by rw [hg'def]; group
        _ = g₁⁻¹ * (g₁ * s2 * g₁⁻¹) * g₁ := by rw [hs2eq']
        _ = s2 := by group
    rw [this]
    exact hs2
  have hzc : (g'⁻¹ * g₀) * z * (g'⁻¹ * g₀)⁻¹ ∈ S := by
    have : (g'⁻¹ * g₀) * z * (g'⁻¹ * g₀)⁻¹ = g'⁻¹ * σ * g' := by rw [← hg₀]; group
    rw [this]
    exact hS₀S σ hσS₀
  obtain ⟨s', hs', hs'eq⟩ := c.zconj _ hzc
  set g : G := g' * s' with hgdef
  have hgz : g * z * g⁻¹ = σ := by
    have h1 : g'⁻¹ * σ * g' = s' * z * s'⁻¹ := by rw [← hs'eq, ← hg₀]; group
    calc g * z * g⁻¹ = g' * (s' * z * s'⁻¹) * g'⁻¹ := by rw [hgdef]; group
      _ = g' * (g'⁻¹ * σ * g') * g'⁻¹ := by rw [h1]
      _ = σ := by group
  have hgS₀ : ∀ y ∈ S₀, g⁻¹ * y * g ∈ S := by
    intro y hy
    have h1 := hS₀S y hy
    have : g⁻¹ * y * g = s'⁻¹ * (g'⁻¹ * y * g') * s' := by rw [hgdef]; group
    rw [this]
    exact mul_mem (mul_mem (inv_mem hs') h1) hs'
  have hkey : ∀ e ∈ E, g * e * g⁻¹ = g₁ * e * g₁⁻¹ := by
    intro e he
    have hse : s' * e * s'⁻¹ = e := by
      have := mem_centralizer_iff.1 (c.SC hs') e he
      calc s' * e * s'⁻¹ = (e * s') * s'⁻¹ := by rw [this]
        _ = e := by group
    have hmem : g₁ * e * g₁⁻¹ ∈ E0 := by
      rw [← hg₁E]; exact ⟨e, he, by simp [MulAut.conj_apply]⟩
    have h1 : (g₁ * e * g₁⁻¹) * c1 = c1 * (g₁ * e * g₁⁻¹) :=
      mem_centralizer_iff.1 hc1C _ hmem
    have hc1e : c1⁻¹ * (g₁ * e * g₁⁻¹) * c1 = g₁ * e * g₁⁻¹ := by
      calc c1⁻¹ * (g₁ * e * g₁⁻¹) * c1 = c1⁻¹ * (c1 * (g₁ * e * g₁⁻¹)) := by rw [← h1]; group
        _ = g₁ * e * g₁⁻¹ := by group
    calc g * e * g⁻¹ = c1⁻¹ * (g₁ * (s' * e * s'⁻¹) * g₁⁻¹) * c1 := by rw [hgdef, hg'def]; group
      _ = c1⁻¹ * (g₁ * e * g₁⁻¹) * c1 := by rw [hse]
      _ = g₁ * e * g₁⁻¹ := hc1e
  have hEg : E.map (MulAut.conj g).toMonoidHom = E0 := by
    rw [← hg₁E]
    ext y
    constructor
    · rintro ⟨e, he, rfl⟩
      refine ⟨e, he, ?_⟩
      simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom]
      exact (hkey e he).symm
    · rintro ⟨e, he, rfl⟩
      refine ⟨e, he, ?_⟩
      simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom]
      exact hkey e he
  have hconjz : ∀ k : ℕ, s ^ k * z * (s ^ k)⁻¹ = s ^ (2 * k) * z := by
    intro k
    have h1 : (s ^ k)⁻¹ = s ^ (7 * k) := by
      rw [← inv_pow, inv_s_eq_pow hS.hs8, ← pow_mul, mul_comm]
    have h2 : z * s ^ (7 * k) = s ^ (7 * (7 * k)) * z := z_mul_pow_s hS.hz2 hS.hzs hS.hs8 _
    calc s ^ k * z * (s ^ k)⁻¹ = s ^ k * (z * s ^ (7 * k)) := by rw [h1]; group
      _ = s ^ k * (s ^ (7 * (7 * k)) * z) := by rw [h2]
      _ = s ^ (k + 7 * (7 * k)) * z := by rw [← mul_assoc, ← pow_add]
      _ = s ^ (2 * k) * z := by
        have : k + 7 * (7 * k) = 2 * k + 8 * (6 * k) := by ring
        rw [this, pow_add, pow_mul s 8 (6 * k), hS.hs8, one_pow, mul_one]
  have hD0le : D0 ≤ (Dsub s z).map (MulAut.conj g).toMonoidHom := by
    intro y hy
    have hyc := hD0gen y hy
    refine (Subgroup.closure_le _).2 ?_ hyc
    rintro w ⟨hwD0, hw2⟩
    by_cases hw1 : w = 1
    · rw [hw1]; exact one_mem _
    have hwS₀ : w ∈ S₀ := (le_sup_left : D0 ≤ S₀) hwD0
    have hy'S := hgS₀ w hwS₀
    have hy'2 : (g⁻¹ * w * g) * (g⁻¹ * w * g) = 1 := by
      calc g⁻¹ * w * g * (g⁻¹ * w * g) = g⁻¹ * (w * w) * g := by group
        _ = 1 := by rw [hw2]; group
    have hy'1 : g⁻¹ * w * g ≠ 1 := by
      intro h
      apply hw1
      calc w = g * (g⁻¹ * w * g) * g⁻¹ := by group
        _ = 1 := by rw [h]; group
    have hwW : w ∈ W := hD0W hwD0
    obtain ⟨h, hh⟩ := h9 w hwW hw2 hw1
    have hnot : ∀ k : ℕ, g⁻¹ * w * g ≠ s ^ (2 * k) * z := by
      intro k hk
      have hwz : w = (g * s ^ k) * z * (g * s ^ k)⁻¹ := by
        calc w = g * (g⁻¹ * w * g) * g⁻¹ := by group
          _ = g * (s ^ (2 * k) * z) * g⁻¹ := by rw [hk]
          _ = g * (s ^ k * z * (s ^ k)⁻¹) * g⁻¹ := by rw [hconjz k]
          _ = (g * s ^ k) * z * (g * s ^ k)⁻¹ := by group
      apply hcfg.conj_t_ne_z ((g * s ^ k)⁻¹ * h)
      calc (g * s ^ k)⁻¹ * h * t * ((g * s ^ k)⁻¹ * h)⁻¹
          = (g * s ^ k)⁻¹ * (h * t * h⁻¹) * (g * s ^ k) := by group
        _ = (g * s ^ k)⁻¹ * w * (g * s ^ k) := by rw [hh]
        _ = z := by rw [hwz]; group
    have hy'D : g⁻¹ * w * g ∈ Dsub s z :=
      invol_mem_Dsub hS.hz2 hS.hs8 hS.hs4 hS.hzs hS.hord hS.hgen _ hy'S hy'2 hy'1 hnot
    exact ⟨g⁻¹ * w * g, hy'D, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
  have hDg : (Dsub s z).map (MulAut.conj g).toMonoidHom = D0 :=
    (Subgroup.eq_of_le_of_card_ge hD0le (by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hD8, hD0card])).symm
  have hWg : W.map (MulAut.conj g).toMonoidHom = W := by
    have hle : W.map (MulAut.conj g).toMonoidHom ≤ W := by
      rw [hWdef, Subgroup.map_sup, hDg, hEg]
      exact sup_le hD0W hE0W
    exact Subgroup.eq_of_le_of_card_ge hle (by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])
  refine ⟨g, ?_, hgz⟩
  rw [mem_normalizer_iff]
  intro w
  constructor
  · intro hw
    have : g * w * g⁻¹ ∈ W.map (MulAut.conj g).toMonoidHom := ⟨w, hw, by simp [MulAut.conj_apply]⟩
    rwa [hWg] at this
  · intro hw
    rw [← hWg] at hw
    obtain ⟨w', hw', hw'eq⟩ := hw
    have hww : w' = w := by
      have h1 : g * w' * g⁻¹ = g * w * g⁻¹ := by
        simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hw'eq
      calc w' = g⁻¹ * (g * w' * g⁻¹) * g := by group
        _ = g⁻¹ * (g * w * g⁻¹) * g := by rw [h1]
        _ = w := by group
    rwa [← hww]

end OuterS16Ctx

end CFSG.EvenSporadicStandard.Fin76b
