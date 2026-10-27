module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotZStar
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.NotCentralPrelim

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup CFSG.Open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_iff)
open scoped commutatorElement Pointwise

namespace TrialityD4Data

variable {X : Type*} [Group X] {q : ℕ} (d : TrialityD4Data X q)

theorem exists_conj_eq_φ_pow_of_outer {f : ℕ} (hq : q = 2 ^ f) {α : MulAut X}
    (hα : α ∉ (MulAut.conj : X →* MulAut X).range) (hα2 : orderOf α = 2) :
    Even f ∧ ∃ w : X, α = (MulAut.conj w)⁻¹ * d.φ ^ (3 * f / 2) * MulAut.conj w := by
  have := d.finite
  have := mulAutConj_range_normal (G := X)
  have hsq : α ^ 2 ∈ (MulAut.conj : X →* MulAut X).range := by
    rw [← hα2, pow_orderOf_eq_one]
    exact one_mem _
  obtain ⟨⟨e, rfl⟩, g, hg⟩ := d.even_and_exists_eq_conj_mul hq hα hsq
  obtain ⟨he, hq'⟩ := d.one_le_and_eq_two_pow_two_mul hq
  have h3 : 3 * (e + e) / 2 = 3 * e := by omega
  rw [h3] at hg
  rw [h3]
  refine ⟨⟨e, rfl⟩, ?_⟩
  have hA : zpowers α ≤ (MulAut.conj : X →* MulAut X).range ⊔ zpowers (d.φ ^ (3 * e)) :=
    zpowers_le.2 (by rw [hg]; exact mul_mem_sup ⟨g, rfl⟩ (mem_zpowers _))
  have hα2' : IsPGroup 2 (zpowers α) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hα2, pow_one])
  obtain ⟨a, haA, ha⟩ := d.exists_conj_le_sup_zpowers hq' hα2' hA
  obtain ⟨s, hs, hy | hy⟩ := d.mem_sup_zpowers_φ_pow hq' (ha α (mem_zpowers α))
  · exact absurd ⟨s, hy.symm⟩ (inv_mul_mul_not_mem_range_conj hα)
  obtain ⟨hord, -, hset, -⟩ := d.yamada_3_13_1 (f := 2 * e) ⟨e, two_mul e⟩ hq'
  rw [show 3 * (2 * e) / 2 = 3 * e by omega] at hord hset
  have hφ₀2 : d.φ ^ (3 * e) * d.φ ^ (3 * e) = 1 := by rw [← sq, ← hord, pow_orderOf_eq_one]
  have hφ₀inv : (d.φ ^ (3 * e))⁻¹ = d.φ ^ (3 * e) := inv_eq_of_mul_eq_one_right hφ₀2
  have hmem : a⁻¹ * α * a ∈ {β : MulAut X |
      (∃ s ∈ d.S, β = d.φ ^ (3 * e) * MulAut.conj s) ∧ orderOf β = 2} := by
    refine ⟨⟨(d.φ ^ (3 * e)) s, d.φ_pow_mem_rootChain _ 6 hs, ?_⟩, ?_⟩
    · rw [hy, ← mulAut_mul_conj_mul_inv, hφ₀inv]
      calc MulAut.conj s * d.φ ^ (3 * e) =
            d.φ ^ (3 * e) * d.φ ^ (3 * e) * MulAut.conj s * d.φ ^ (3 * e) := by
              rw [hφ₀2, one_mul]
        _ = _ := by group
    · have h1 := MulEquiv.orderOf_eq (MulAut.conj a⁻¹) α
      rw [MulAut.conj_apply, inv_inv] at h1
      rw [h1, hα2]
  rw [hset] at hmem
  obtain ⟨t', -, hyt⟩ := hmem
  have hb : a * (MulAut.conj t')⁻¹ ∈
      (MulAut.conj : X →* MulAut X).range ⊔ zpowers (d.φ ^ (3 * e)) :=
    mul_mem haA (inv_mem (mem_sup_left ⟨t', rfl⟩))
  rw [← SetLike.mem_coe, Subgroup.normal_mul, Set.mem_mul] at hb
  obtain ⟨_, ⟨w', rfl⟩, z, hz, hbz⟩ := hb
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hz
  have hαb : α = (a * (MulAut.conj t')⁻¹) * d.φ ^ (3 * e) * (a * (MulAut.conj t')⁻¹)⁻¹ := by
    calc α = a * (a⁻¹ * α * a) * a⁻¹ := by group
      _ = (a * (MulAut.conj t')⁻¹) * d.φ ^ (3 * e) * (a * (MulAut.conj t')⁻¹)⁻¹ := by
        rw [hyt]; group
  have hcomm : (d.φ ^ (3 * e)) ^ k * d.φ ^ (3 * e) = d.φ ^ (3 * e) * (d.φ ^ (3 * e)) ^ k :=
    ((Commute.refl (d.φ ^ (3 * e))).zpow_left k).eq
  refine ⟨w'⁻¹, ?_⟩
  rw [hαb, ← hbz, map_inv, inv_inv]
  calc MulAut.conj w' * (d.φ ^ (3 * e)) ^ k * d.φ ^ (3 * e) *
        (MulAut.conj w' * (d.φ ^ (3 * e)) ^ k)⁻¹ =
      MulAut.conj w' * ((d.φ ^ (3 * e)) ^ k * d.φ ^ (3 * e)) * ((d.φ ^ (3 * e)) ^ k)⁻¹ *
        (MulAut.conj w')⁻¹ := by group
    _ = MulAut.conj w' * (d.φ ^ (3 * e) * (d.φ ^ (3 * e)) ^ k) * ((d.φ ^ (3 * e)) ^ k)⁻¹ *
        (MulAut.conj w')⁻¹ := by rw [hcomm]
    _ = MulAut.conj w' * d.φ ^ (3 * e) * (MulAut.conj w')⁻¹ := by group

theorem mem_zSx₄Y_one {z : X} :
    z ∈ d.zSx₄Y 1 ↔ ∃ m f g : d.Γ₀, d.x₄ (m : d.Γ) * d.x₅ f * d.x₆ g = z := by
  constructor
  · rintro ⟨⟨m, f, g⟩, rfl⟩
    refine ⟨m, f, g, ?_⟩
    change d.x₄ (m : d.Γ) * d.x₅ f * d.x₆ g = d.x₄ ((m : d.Γ) * 1) * d.x₅ f * d.x₆ g
    rw [mul_one]
  · rintro ⟨m, f, g, rfl⟩
    refine ⟨Multiplicative.ofAdd (m, f, g), ?_⟩
    change d.x₄ ((m : d.Γ) * 1) * d.x₅ f * d.x₆ g = _
    rw [mul_one]

theorem card_zSx₄Y_one : Nat.card (d.zSx₄Y 1) = q ^ 3 := by
  rw [zSx₄Y, card_range_tripleHom, d.card_Γ₀]
  · ring
  · intro p p' h
    have h' : d.nf (0, 0, 0, (p.1 : d.Γ) * 1, p.2.1, p.2.2) =
        d.nf (0, 0, 0, (p'.1 : d.Γ) * 1, p'.2.1, p'.2.2) := by
      simpa only [nf_apply, d.x₁_zero, d.x₂_zero, d.x₃_zero, one_mul] using h
    have := d.nf_injective h'
    simp only [Prod.mk.injEq, mul_one] at this
    exact Prod.ext (Subtype.ext this.2.2.2.1) (Prod.ext this.2.2.2.2.1 this.2.2.2.2.2)

theorem x₄_one_mem_zSx₄Y : d.x₄ 1 ∈ d.zSx₄Y 1 ∧ d.x₄ 1 ∉ d.Y := by
  refine ⟨d.mem_zSx₄Y_one.2 ⟨1, 0, 0, by rw [d.x₅_zero, d.x₆_zero, mul_one, mul_one]; rfl⟩,
    fun h => one_ne_zero (d.x₄_mem_Y_iff.1 h)⟩

theorem zSx₄Y_one_le : d.zSx₄Y 1 ≤ d.centSx₄Y 1 ∧
    d.zSx₄Y 1 ≤ centralizer (d.centSx₄Y 1 : Set X) := by
  rw [← d.centSx₄Y_inf_centralizer one_ne_zero]
  exact ⟨inf_le_left, inf_le_right⟩

theorem isElemAbelian_zSx₄Y_one : CFSG.Open.IsElemAbelian 2 (d.zSx₄Y 1) :=
  isElemAbelian_range_tripleHom _ _ _ _ _ _
    (prod_add_self_eq_zero d.add_self_Γ₀ d.add_self_Γ₀ d.add_self_Γ₀)

theorem centSx₄Y_le_centralizer : d.centSx₄Y 1 ≤ centralizer ({d.x₄ 1} : Set X) :=
  fun _ hg => mem_centralizer_singleton_iff.2
    (mem_centralizer_iff.1 (mem_inf.1 hg).2 _ (Set.mem_insert _ _)).symm

theorem exists_eq_of_mem_centSx₄Y_one {g : X} (hg : g ∈ d.centSx₄Y 1) :
    ∃ a c : d.Γ, d.tr a = 0 ∧ d.tr c = 0 ∧ ∃ w ∈ d.W, g = d.x₁ a * d.x₃ c * w := by
  obtain ⟨hgS, h2, h1, h3⟩ := d.mem_centSx₄Y_iff.1 hg
  rw [mul_one] at h1 h3
  refine ⟨_, _, h1, h3, d.x₄ (d.nfc g).2.2.2.1 * d.x₅ (d.nfc g).2.2.2.2.1 *
    d.x₆ (d.nfc g).2.2.2.2.2, mul_mem (mul_mem (d.x₄_mem_W _) (d.x₅_mem_W _)) (d.x₆_mem_W _), ?_⟩
  conv_lhs => rw [← d.nf_nfc hgS]
  rw [nf_apply, h2, d.x₂_zero, mul_one]
  group

theorem exists_conj_x₄_one_eq {z : X} (hz : z ∈ d.zSx₄Y 1) (hzY : z ∉ d.Y) :
    ∃ n : X, n ∈ normalizer (d.zSx₄Y 1 : Set X) ∧ n * d.x₄ 1 * n⁻¹ = z := by
  have := d.finite
  obtain ⟨m, f, g, rfl⟩ := d.mem_zSx₄Y_one.1 hz
  have hm : m ≠ 0 := by
    rintro rfl
    exact hzY (mul_mem (mul_mem (by rw [Subfield.coe_zero, d.x₄_zero]; exact one_mem _)
      (d.x₅_mem_Y f)) (d.x₆_mem_Y g))
  have hσ : ∀ l : d.Γ₀, d.σ (l : d.Γ) = l := fun l => apply_coe_fixedSubfield l
  have hm' : (m : d.Γ) ≠ 0 := fun h => hm (Subtype.ext h)
  set h₀ := d.torus (Units.mk0 m hm, 1) with hh₀
  obtain ⟨β, hβ⟩ := d.exists_tr_eq f
  obtain ⟨γ, hγ⟩ := d.exists_tr_eq g
  set n₁ := d.x₁ ((m : d.Γ)⁻¹ * β) with hn₁
  set n₃ := d.x₃ ((m : d.Γ)⁻¹ * γ) with hn₃
  have hZ : ∀ (c : d.Γ₀) (f' g' : d.Γ₀), d.x₄ (c : d.Γ) * d.x₅ f' * d.x₆ g' ∈ d.zSx₄Y 1 :=
    fun c f' g' => d.mem_zSx₄Y_one.2 ⟨c, f', g', rfl⟩
  have hnorm : ∀ n : X, (∀ c f' g' : d.Γ₀,
      n * (d.x₄ (c : d.Γ) * d.x₅ f' * d.x₆ g') * n⁻¹ ∈ d.zSx₄Y 1) →
      n ∈ normalizer (d.zSx₄Y 1 : Set X) := fun n hn =>
    mem_normalizer_fintype fun w hw => by
      obtain ⟨c, f', g', rfl⟩ := d.mem_zSx₄Y_one.1 hw
      exact hn c f' g'
  have hh₀4 : ∀ c : d.Γ₀, h₀ * d.x₄ (c : d.Γ) * h₀⁻¹ = d.x₄ (((m * c : d.Γ₀)) : d.Γ) := by
    intro c
    rw [hh₀, d.torus_x₄]
    congr 1
    simp only [Units.val_one, map_one, mul_one, Units.val_mk0, Subfield.coe_mul]
  have hh₀5 : ∀ c : d.Γ₀, h₀ * d.x₅ c * h₀⁻¹ = d.x₅ (m * c) := by
    intro c
    rw [hh₀, d.torus_x₅]
    congr 1
    have hn : d.nm ((1 : d.Γˣ) : d.Γ) = 1 := by rw [Units.val_one]; exact d.nm_one
    change (m : d.Γ₀) * d.nm ((1 : d.Γˣ) : d.Γ) * c = m * c
    rw [hn, mul_one]
  have hh₀6 : ∀ c : d.Γ₀, h₀ * d.x₆ c * h₀⁻¹ = d.x₆ (m * m * c) := by
    intro c
    rw [hh₀, d.torus_x₆]
    congr 1
    have hn : d.nm ((1 : d.Γˣ) : d.Γ) = 1 := by rw [Units.val_one]; exact d.nm_one
    change (m : d.Γ₀) * m * d.nm ((1 : d.Γˣ) : d.Γ) * c = m * m * c
    rw [hn, mul_one]
  have hconj : ∀ n w₁ w₂ w₃ : X, n * (w₁ * w₂ * w₃) * n⁻¹ =
      (n * w₁ * n⁻¹) * (n * w₂ * n⁻¹) * (n * w₃ * n⁻¹) := fun _ _ _ _ => by group
  have hN₀ : h₀ ∈ normalizer (d.zSx₄Y 1 : Set X) := hnorm _ fun c f' g' => by
    rw [hconj, hh₀4, hh₀5, hh₀6]
    exact hZ _ _ _
  have hx₁4 : ∀ (a : d.Γ) (c : d.Γ₀),
      d.x₁ a * d.x₄ (c : d.Γ) * (d.x₁ a)⁻¹ = d.x₄ (c : d.Γ) * d.x₅ (d.tr (a * c)) := by
    intro a c
    rw [show d.x₁ a * d.x₄ (c : d.Γ) * (d.x₁ a)⁻¹ = ⁅d.x₁ a, d.x₄ (c : d.Γ)⁆ * d.x₄ (c : d.Γ) by
      rw [commutatorElement_def]; group, d.comm₁₄]
    exact (d.commute₄₅ _ _).symm.eq
  have hx₃4 : ∀ (a : d.Γ) (c : d.Γ₀),
      d.x₃ a * d.x₄ (c : d.Γ) * (d.x₃ a)⁻¹ = d.x₄ (c : d.Γ) * d.x₆ (d.tr (a * c)) := by
    intro a c
    rw [show d.x₃ a * d.x₄ (c : d.Γ) * (d.x₃ a)⁻¹ = ⁅d.x₃ a, d.x₄ (c : d.Γ)⁆ * d.x₄ (c : d.Γ) by
      rw [commutatorElement_def]; group, d.comm₃₄]
    exact (d.commute₄₆ _ _).symm.eq
  have hfix : ∀ {n w : X}, Commute n w → n * w * n⁻¹ = w := fun h => by
    rw [h.eq, mul_inv_cancel_right]
  have hN₁ : ∀ a : d.Γ, d.x₁ a ∈ normalizer (d.zSx₄Y 1 : Set X) := fun a =>
    hnorm _ fun c f' g' => by
      rw [hconj, hx₁4, hfix (d.commute₁₅ a f'), hfix (d.commute₁₆ a g'), mul_assoc (d.x₄ _),
        ← d.x₅_add]
      exact hZ _ _ _
  have hN₃ : ∀ a : d.Γ, d.x₃ a ∈ normalizer (d.zSx₄Y 1 : Set X) := fun a =>
    hnorm _ fun c f' g' => by
      rw [hconj, hx₃4, hfix (d.commute₃₅ a f'), hfix (d.commute₃₆ a g'),
        mul_assoc (d.x₄ _) (d.x₆ _), (d.commute₅₆ _ _).symm.eq, ← mul_assoc, mul_assoc _ (d.x₆ _),
        ← d.x₆_add]
      exact hZ _ _ _
  refine ⟨n₃ * n₁ * h₀, mul_mem (mul_mem (hN₃ _) (hN₁ _)) hN₀, ?_⟩
  have e1 : h₀ * d.x₄ 1 * h₀⁻¹ = d.x₄ (m : d.Γ) := by
    have := hh₀4 1
    rwa [Subfield.coe_one, mul_one] at this
  have htr : ∀ e : d.Γ, d.tr ((m : d.Γ)⁻¹ * e * m) = d.tr e := fun e => by
    rw [mul_assoc, mul_comm e, ← mul_assoc, inv_mul_cancel₀ hm', one_mul]
  have e2 : n₁ * d.x₄ (m : d.Γ) * n₁⁻¹ = d.x₄ (m : d.Γ) * d.x₅ f := by
    rw [hn₁, hx₁4, htr, hβ]
  have e3 : n₃ * (d.x₄ (m : d.Γ) * d.x₅ f) * n₃⁻¹ = d.x₄ (m : d.Γ) * d.x₅ f * d.x₆ g := by
    rw [show n₃ * (d.x₄ (m : d.Γ) * d.x₅ f) * n₃⁻¹ =
      (n₃ * d.x₄ (m : d.Γ) * n₃⁻¹) * (n₃ * d.x₅ f * n₃⁻¹) by group, hn₃, hx₃4, htr, hγ,
      hfix (d.commute₃₅ _ f), mul_assoc, (d.commute₅₆ _ _).symm.eq, ← mul_assoc]
  calc n₃ * n₁ * h₀ * d.x₄ 1 * (n₃ * n₁ * h₀)⁻¹ =
      n₃ * (n₁ * (h₀ * d.x₄ 1 * h₀⁻¹) * n₁⁻¹) * n₃⁻¹ := by group
    _ = d.x₄ (m : d.Γ) * d.x₅ f * d.x₆ g := by rw [e1, e2, e3]

end TrialityD4Data

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem exists_conj_mul_mem_L_of_outer (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    {g : G} (hgC : g⁻¹ * t * g ∈ centralizer ({t} : Set G))
    (hout : h.act ⟨g⁻¹ * t * g, hgC⟩ ∉ (MulAut.conj : L →* MulAut L).range) :
    ∃ a : G, a * t * a⁻¹ ≠ t ∧ t * (a * t * a⁻¹) ∈ L := by
  set t' := g⁻¹ * t * g with ht'
  have ht'2 : t' * t' = 1 := by
    calc t' * t' = g⁻¹ * (t * t) * g := by rw [ht']; group
      _ = 1 := by rw [h.t_mul_t, mul_one, inv_mul_cancel]
  set α := h.act ⟨t', hgC⟩ with hα
  have hα2 : orderOf α = 2 := by
    refine orderOf_eq_prime ?_ fun h1 => hout (h1 ▸ one_mem _)
    rw [sq, hα, ← map_mul, show (⟨t', hgC⟩ * ⟨t', hgC⟩ : centralizer ({t} : Set G)) = 1 from
      Subtype.ext ht'2, map_one]
  obtain ⟨-, w, hαw⟩ := d.exists_conj_eq_φ_pow_of_outer rfl hout hα2
  have hfix : ∀ x : L, (d.φ ^ (3 * f / 2)) x = x → α (w⁻¹ * x * w) = w⁻¹ * x * w := by
    intro x hx
    rw [hαw, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply,
      show w * (w⁻¹ * x * w) * w⁻¹ = x by group, hx, ← map_inv, MulAut.conj_apply, inv_inv]
  have hcomm : ∀ x : L, α x = x → t' * (x : G) = x * t' := by
    intro x hx
    have h1 := h.coe_act_apply ⟨t', hgC⟩ x
    rw [← hα, hx] at h1
    calc t' * (x : G) = t' * x * t'⁻¹ * t' := by group
      _ = x * t' := by rw [← h1]
  have hroot : ∀ k : ℕ, (d.φ ^ k) (d.x₂ 1) = d.x₂ 1 ∧ (d.φ ^ k) (d.x₅ 1) = d.x₅ 1 ∧
      (d.φ ^ k) (d.x₆ 1) = d.x₆ 1 := fun k => by
    rw [d.φ_pow_x₂, d.φ_pow_x₅, d.φ_pow_x₆, one_pow]
    exact ⟨rfl, rfl, rfl⟩
  obtain ⟨h2, h5, h6⟩ := hroot (3 * f / 2)
  set a := w⁻¹ * d.x₂ 1 * w with ha
  set b := w⁻¹ * d.x₅ 1 * w with hb
  set s := w⁻¹ * d.x₆ 1 * w with hs
  have hsab : (s : G) = ⁅(a : G), (b : G)⁆ := by
    have e : s = ⁅a, b⁆ := by
      rw [hs, ha, hb, show d.x₆ 1 = ⁅d.x₂ 1, d.x₅ 1⁆ by rw [d.comm₂₅, one_mul]]
      simp only [commutatorElement_def]
      group
    rw [e]
    simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
  have hs1 : s ≠ 1 := fun h1 => by
    have h2 : d.x₆ 1 = 1 := by
      calc d.x₆ 1 = w * s * w⁻¹ := by rw [hs]; group
        _ = 1 := by rw [h1]; group
    exact one_ne_zero (d.x₆_eq_one_iff.1 h2)
  have hs2 : (s : G) * s = 1 := by
    have e : s * s = 1 := by
      calc s * s = w⁻¹ * (d.x₆ 1 * d.x₆ 1) * w := by rw [hs]; group
        _ = 1 := by rw [d.x₆_mul_self, mul_one, inv_mul_cancel]
    exact congrArg Subtype.val e
  have hat : t' * a = a * t' := hcomm _ (hfix _ h2)
  have hbt : t' * b = b * t' := hcomm _ (hfix _ h5)
  have hst : t' * s = s * t' := hcomm _ (hfix _ h6)
  have hconj : ∀ y : G, t' * y = y * t' → g * y * g⁻¹ ∈ centralizer ({t} : Set G) := by
    intro y hy
    rw [mem_centralizer_singleton_iff]
    calc g * y * g⁻¹ * t = g * (y * t') * g⁻¹ := by rw [ht']; group
      _ = g * (t' * y) * g⁻¹ := by rw [hy]
      _ = t * (g * y * g⁻¹) := by rw [ht']; group
  have hsL : g * s * g⁻¹ ∈ L ⊔ (centralizer (L : Set G) ⊓ centralizer ({t} : Set G)) := by
    have e : g * (s : G) * g⁻¹ = ⁅g * a * g⁻¹, g * b * g⁻¹⁆ := by
      rw [hsab]
      simp only [commutatorElement_def]
      group
    rw [e]
    exact h.commutator_le_sup_kernel d (commutator_mem_commutator (hconj _ hat) (hconj _ hbt))
  have hs2' : g * s * g⁻¹ * (g * s * g⁻¹) = 1 := by
    calc g * s * g⁻¹ * (g * s * g⁻¹) = g * ((s : G) * s) * g⁻¹ := by group
      _ = 1 := by rw [hs2, mul_one, mul_inv_cancel]
  have hsLt := h.mem_or_mul_mem_of_mem_sup_kernel hsL hs2'
  have hsC : (s : G) ∈ centralizer ({t} : Set G) := h.L_le_centralizer s.2
  have hβ : h.act ⟨t' * s, mul_mem hgC hsC⟩ = α * MulAut.conj s := by
    rw [show (⟨t' * s, mul_mem hgC hsC⟩ : centralizer ({t} : Set G)) =
      ⟨t', hgC⟩ * ⟨s, hsC⟩ from rfl, map_mul, h.act_of_mem_L s.2]
  have hβout : h.act ⟨t' * s, mul_mem hgC hsC⟩ ∉ (MulAut.conj : L →* MulAut L).range := by
    rw [hβ]
    intro hin
    refine hout ?_
    have := mul_mem hin (inv_mem (⟨s, rfl⟩ : MulAut.conj s ∈ (MulAut.conj : L →* MulAut L).range))
    rwa [mul_inv_cancel_right] at this
  have hβ2 : orderOf (h.act ⟨t' * s, mul_mem hgC hsC⟩) = 2 := by
    refine orderOf_eq_prime ?_ fun h1 => hβout (h1 ▸ one_mem _)
    rw [sq, ← map_mul]
    have : (⟨t' * s, mul_mem hgC hsC⟩ * ⟨t' * s, mul_mem hgC hsC⟩ :
        centralizer ({t} : Set G)) = 1 := Subtype.ext (by
      calc t' * s * (t' * s) = t' * (s * t') * s := by group
        _ = t' * t' * ((s : G) * s) := by rw [← hst]; group
        _ = 1 := by rw [ht'2, hs2, one_mul])
    rw [this, map_one]
  obtain ⟨-, w₁, hβw⟩ := d.exists_conj_eq_φ_pow_of_outer rfl hβout hβ2
  set m₀ := w⁻¹ * w₁ with hm₀
  have hβm : h.act ⟨t' * s, mul_mem hgC hsC⟩ = (MulAut.conj m₀)⁻¹ * α * MulAut.conj m₀ := by
    rw [hβw, hαw, hm₀, map_mul, map_inv]
    group
  set m := (m₀ : G) with hm
  have hmC : m ∈ centralizer ({t} : Set G) := h.L_le_centralizer m₀.2
  have hz : h.act ⟨(m⁻¹ * t' * m)⁻¹ * (t' * s), mul_mem (inv_mem (mul_mem (mul_mem
      (inv_mem hmC) hgC) hmC)) (mul_mem hgC hsC)⟩ = 1 := by
    rw [show (⟨(m⁻¹ * t' * m)⁻¹ * (t' * s), mul_mem (inv_mem (mul_mem (mul_mem (inv_mem hmC) hgC)
      hmC)) (mul_mem hgC hsC)⟩ : centralizer ({t} : Set G)) =
      ((⟨m, hmC⟩ : centralizer ({t} : Set G))⁻¹ * ⟨t', hgC⟩ * ⟨m, hmC⟩)⁻¹ *
        ⟨t' * s, mul_mem hgC hsC⟩ from rfl, map_mul, map_inv, map_mul, map_mul, map_inv, hβm,
      ← hα, h.act_of_mem_L m₀.2]
    group
  have hzC := (h.act_eq_one_iff _).1 hz
  have hzL : (m⁻¹ * t' * m)⁻¹ * (t' * s) ∈ L := by
    have ht'N := h.centralizer_le_normalizer (inv_mem hgC)
    have h1 : t'⁻¹ * m * t'⁻¹⁻¹ ∈ L := (mem_normalizer_iff.1 ht'N m).1 m₀.2
    rw [show (m⁻¹ * t' * m)⁻¹ * (t' * s) = m⁻¹ * (t'⁻¹ * m * t'⁻¹⁻¹) * s by group]
    exact mul_mem (mul_mem (inv_mem m₀.2) h1) s.2
  have hz1 : (m⁻¹ * t' * m)⁻¹ * (t' * s) = 1 := by
    have : (m⁻¹ * t' * m)⁻¹ * (t' * s) ∈ L ⊓ centralizer (L : Set G) := ⟨hzL, hzC⟩
    rwa [h.inf_centralizer_eq_bot, mem_bot] at this
  have hts : t' * s = m⁻¹ * t' * m := (inv_mul_eq_one.1 hz1).symm
  have h2' : g * m⁻¹ * g⁻¹ * t * (g * m⁻¹ * g⁻¹)⁻¹ = t * (g * s * g⁻¹) := by
    calc g * m⁻¹ * g⁻¹ * t * (g * m⁻¹ * g⁻¹)⁻¹ = g * (m⁻¹ * t' * m) * g⁻¹ := by rw [ht']; group
      _ = g * (t' * s) * g⁻¹ := by rw [hts]
      _ = t * (g * s * g⁻¹) := by rw [ht']; group
  refine ⟨g * m⁻¹ * g⁻¹, ?_, ?_⟩
  · intro h1
    refine hs1 (Subtype.ext ?_)
    rw [h2'] at h1
    have h3 : g * s * g⁻¹ = 1 := by
      calc g * s * g⁻¹ = t⁻¹ * (t * (g * s * g⁻¹)) := by group
        _ = 1 := by rw [h1, inv_mul_cancel]
    calc (s : G) = g⁻¹ * (g * s * g⁻¹) * g := by group
      _ = 1 := by rw [h3]; group
  · rw [h2']
    rcases hsLt with h3 | h3
    · rwa [← mul_assoc, h.t_mul_t, one_mul]
    · exact absurd (by rw [← h2'] at h3; exact h3) (h.conj_not_mem_L d (g * m⁻¹ * g⁻¹))

theorem exists_conj_mul_mem_L (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    ∃ a : G, a * t * a⁻¹ ≠ t ∧ t * (a * t * a⁻¹) ∈ L := by
  have := h.simple
  obtain ⟨g, hgC, hgt⟩ :=
    CFSG.SeitzReduction.F4Pilot.exists_conj_ne_mem_centralizer_of_isSimpleGroup h.nonab h.ht
  by_cases hin : h.act ⟨g⁻¹ * t * g, hgC⟩ ∈ (MulAut.conj : L →* MulAut L).range
  · refine ⟨g⁻¹, by rw [inv_inv]; exact hgt, ?_⟩
    rw [inv_inv]
    have hx2 : g⁻¹ * t * g * (g⁻¹ * t * g) = 1 := by
      calc g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
        _ = 1 := by rw [h.t_mul_t, mul_one, inv_mul_cancel]
    refine (h.mem_or_mul_mem_of_mem_sup_kernel ((h.act_mem_range_conj_iff _).1 hin)
      hx2).resolve_left fun hL => h.conj_not_mem_L d g⁻¹ ?_
    rwa [inv_inv]
  · exact h.exists_conj_mul_mem_L_of_outer d hgC hin

theorem exists_conj_eq_mul_x₄ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hY : ∀ a : G, a * t * a⁻¹ ∈ d.Y.map L.subtype ⊔ zpowers t → a * t * a⁻¹ = t) :
    ∃ a : G, a * t * a⁻¹ = t * (d.x₄ 1 : G) := by
  obtain ⟨a, hat, hL⟩ := h.exists_conj_mul_mem_L d
  set x := a * t * a⁻¹ with hx
  set l : L := ⟨t * x, hL⟩ with hl
  have hxl : x = t * (l : G) := by rw [hl]; simp only; rw [← mul_assoc, h.t_mul_t, one_mul]
  have hlt : (l : G) * t = t * l := mem_centralizer_singleton_iff.1 (h.L_le_centralizer l.2)
  have hl1 : l ≠ 1 := fun h1 => hat (by rw [hxl, h1, OneMemClass.coe_one, mul_one])
  have hx2 : x * x = 1 := by
    calc x * x = a * (t * t) * a⁻¹ := by rw [hx]; group
      _ = 1 := by rw [h.t_mul_t, mul_one, mul_inv_cancel]
  have hxt : x * t = t * x := by
    have h1 : t * x * t = t * (t * x) := hlt
    calc x * t = t * (t * x * t) := by rw [← mul_assoc, ← mul_assoc, h.t_mul_t, one_mul]
      _ = t * x := by rw [h1, ← mul_assoc, h.t_mul_t, one_mul]
  have hll : l * l = 1 := Subtype.ext (by
    change t * x * (t * x) = 1
    calc t * x * (t * x) = t * (x * t) * x := by group
      _ = t * t * (x * x) := by rw [hxt]; group
      _ = 1 := by rw [h.t_mul_t, hx2, one_mul])
  have hl2 : orderOf l = 2 := orderOf_eq_prime (by rw [sq]; exact hll) hl1
  obtain ⟨m, hm⟩ := d.involution_conj l hl2
  have hmt : (m : G) * t = t * m := mem_centralizer_singleton_iff.1 (h.L_le_centralizer m.2)
  have hconj : (m : G) * a * t * ((m : G) * a)⁻¹ = t * ((m * l * m⁻¹ : L) : G) := by
    rw [show (m : G) * a * t * ((m : G) * a)⁻¹ = m * x * (m : G)⁻¹ by rw [hx]; group, hxl,
      ← mul_assoc, hmt]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rcases hm with hm | hm
  · exfalso
    rw [hm] at hconj
    have h1 := hY _ (by
      rw [hconj]
      exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left ⟨_, d.x₆_mem_Y 1, rfl⟩))
    rw [hconj] at h1
    have h2 : (d.x₆ 1 : G) = 1 := by
      calc (d.x₆ 1 : G) = t⁻¹ * (t * d.x₆ 1) := by group
        _ = 1 := by rw [h1, inv_mul_cancel]
    exact one_ne_zero (d.x₆_eq_one_iff.1 (Subtype.ext h2))
  · rw [hm] at hconj
    exact ⟨(m : G) * a, hconj⟩

theorem map_commutator_le_sup_kernel (h : Setup G L f t) {q : ℕ} (d : TrialityD4Data L q)
    {K : Subgroup G} {g : G} (hK : K ≤ centralizer ({g * t * g⁻¹} : Set G)) :
    (⁅K, K⁆).map (MulAut.conj g⁻¹).toMonoidHom ≤
      L ⊔ (centralizer (L : Set G) ⊓ centralizer ({t} : Set G)) := by
  rw [map_commutator]
  have hK' := map_conj_le_centralizer hK
  exact (commutator_mono hK' hK').trans (h.commutator_le_sup_kernel d)

theorem eq_inf_sup_zpowers (h : Setup G L f t) {P : Subgroup G} (hP : P ≤ L ⊔ zpowers t)
    (htP : t ∈ P) : P = (P ⊓ L) ⊔ zpowers t := by
  refine le_antisymm (fun x hx => ?_) (sup_le inf_le_left (zpowers_le.2 htP))
  rcases (h.mem_sup_zpowers_iff le_rfl).1 (hP hx) with h1 | h1
  · exact mem_sup_left ⟨hx, h1⟩
  · exact (h.mem_sup_zpowers_iff inf_le_right).2 (Or.inr ⟨mul_mem htP hx, h1⟩)

theorem exists_normalizer_conj_eq_mul_x₄ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hq : 4 ≤ 2 ^ f) {a : G} (ha : a * t * a⁻¹ = t * (d.x₄ 1 : G)) :
    ∃ b ∈ normalizer (((d.zSx₄Y 1).map L.subtype ⊔ zpowers t : Subgroup G) : Set G),
      b * t * b⁻¹ = t * (d.x₄ 1 : G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq2 := d.two_le_q
  set Z := (d.zSx₄Y 1).map L.subtype with hZ
  set X₁ := (d.centSx₄Y 1).map L.subtype with hX₁
  set W' := d.W.map L.subtype ⊔ zpowers t with hW'
  set A := Z ⊔ zpowers t with hA
  set Xt := X₁ ⊔ zpowers t with hXt
  have hX₁L : X₁ ≤ L := map_subtype_le _
  have hZL : Z ≤ L := map_subtype_le _
  have hLt : ∀ l ∈ L, l * t = t * l := fun l hl =>
    mem_centralizer_singleton_iff.1 (h.L_le_centralizer hl)
  obtain ⟨hZX, hZc⟩ := d.zSx₄Y_one_le
  have hWX : d.W ≤ d.centSx₄Y 1 := d.W_le_centSx₄Y 1
  have hx₄t : (d.x₄ 1 : G) * t = t * d.x₄ 1 := hLt _ (d.x₄ 1).2
  have hcent : ∀ x : L, x * d.x₄ 1 = d.x₄ 1 * x →
      (x : G) ∈ centralizer ({a * t * a⁻¹} : Set G) := by
    intro x hx
    rw [ha, mem_centralizer_singleton_iff]
    have hxt := hLt _ x.2
    have hx' : (x : G) * d.x₄ 1 = d.x₄ 1 * x := congrArg Subtype.val hx
    calc (x : G) * (t * d.x₄ 1) = t * ((x : G) * d.x₄ 1) := by rw [← mul_assoc, hxt, mul_assoc]
      _ = t * (d.x₄ 1 * x) := by rw [hx']
      _ = t * d.x₄ 1 * x := by group
  have htt : ∀ x : G, t * (t * x) = x := fun x => by rw [← mul_assoc, h.t_mul_t, one_mul]
  have htcent : t ∈ centralizer ({a * t * a⁻¹} : Set G) := by
    rw [ha, mem_centralizer_singleton_iff, mul_assoc t (d.x₄ 1 : G) t, hx₄t]
  have hXty : Xt ≤ centralizer ({a * t * a⁻¹} : Set G) := by
    refine sup_le ?_ (zpowers_le.2 htcent)
    rintro _ ⟨x, hx, rfl⟩
    exact hcent x (mem_centralizer_singleton_iff.1 (d.centSx₄Y_le_centralizer hx))
  have hW'Xt : W' ≤ Xt := sup_le_sup_right (map_mono hWX) _
  have hAXt : A ≤ Xt := sup_le_sup_right (map_mono hZX) _
  obtain ⟨Q, hQ, hRQ⟩ := h.exists_isSylowOf_le d
  have hW'C := map_conj_le_centralizer (g := a) (hW'Xt.trans hXty)
  obtain ⟨hWab, hWcard⟩ := h.isElemAbelian_W_sup_zpowers d
  have hW'2 : IsPGroup 2 W' := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact hWab.2 x x.2)⟩
  obtain ⟨c, hcC, hc⟩ := exists_conj_le_of_isSylowOf_D4 hQ hW'C (hW'2.map _)
  have hct : c * t = t * c := mem_centralizer_singleton_iff.1 hcC
  set g := a * c with hg
  have hgt : g * t * g⁻¹ = a * t * a⁻¹ := by
    rw [hg]
    calc a * c * t * (a * c)⁻¹ = a * (c * t) * c⁻¹ * a⁻¹ := by group
      _ = a * t * a⁻¹ := by rw [hct]; group
  set κ := (MulAut.conj g⁻¹).toMonoidHom with hκ
  have hκapp : ∀ x, κ x = g⁻¹ * x * g := fun x => by simp [hκ]
  have hκinj : Function.Injective κ := (MulAut.conj g⁻¹).injective
  have hκW'Q : W'.map κ ≤ Q := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 := hc _ ⟨x, hx, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at h1
    rw [hκapp, hg]
    convert h1 using 1
    group
  have hκW'R : W'.map κ ≤ yamadaR d t := by
    rw [← h.rankThompson_eq d hQ.isPGroup hQ.le hRQ]
    unfold rankJr
    have hE := SectionRank.isElemAbelian_map hWab κ
    refine le_iSup₂_of_le (W'.map κ) ⟨hκW'Q, hE.1, ?_⟩ le_rfl
    refine le_antisymm (SectionRank.pRank_mono one_lt_two hκW'Q) ?_
    rw [h.pRank_eq d hQ.le hRQ]
    refine SectionRank.le_pRank one_lt_two le_rfl hE ?_
    rw [card_map_of_injective hκinj, hWcard, ← pow_mul, pow_succ, mul_comm f 5, mul_comm]
  have hRL : yamadaR d t ≤ L ⊔ (centralizer (L : Set G) ⊓ centralizer ({t} : Set G)) :=
    sup_le_sup_right (map_subtype_le _) _
  have hinv : ∀ x : G, κ x ∈ L ⊔ (centralizer (L : Set G) ⊓ centralizer ({t} : Set G)) →
      x * x = 1 → κ x ∈ L ⊔ zpowers t := by
    intro x hx hx2
    have hx2' : κ x * κ x = 1 := by rw [← map_mul, hx2, map_one]
    rcases h.mem_or_mul_mem_of_mem_sup_kernel hx hx2' with h1 | h1
    · exact mem_sup_left h1
    · exact (h.mem_sup_zpowers_iff le_rfl).2 (Or.inr h1)
  have hκW' : ∀ x ∈ W', κ x ∈ L ⊔ zpowers t := fun x hx =>
    hinv x (hRL (hκW'R ⟨x, hx, rfl⟩)) (by rw [← sq]; exact hWab.2 x hx)
  obtain ⟨hx₁', hx₃', -, -⟩ := d.root_mem_commutator_centralizer_x₄_one hq
  set K₂ := (centralizer ({d.x₄ 1} : Set L)).map L.subtype with hK₂
  have hK₂y : K₂ ≤ centralizer ({g * t * g⁻¹} : Set G) := by
    rw [hgt]
    rintro _ ⟨x, hx, rfl⟩
    exact hcent x (mem_centralizer_singleton_iff.1 hx)
  have hcomm₂ := h.map_commutator_le_sup_kernel d hK₂y
  have hκ₁ : ∀ α : d.Γ, d.tr α = 0 → κ (d.x₁ α : G) ∈ L ⊔ zpowers t := fun α hα =>
    hinv _ (hcomm₂ ⟨_, by rw [hK₂, ← map_commutator]; exact ⟨_, hx₁' α hα, rfl⟩, rfl⟩)
      (congrArg Subtype.val (d.x₁_mul_self α))
  have hκ₃ : ∀ α : d.Γ, d.tr α = 0 → κ (d.x₃ α : G) ∈ L ⊔ zpowers t := fun α hα =>
    hinv _ (hcomm₂ ⟨_, by rw [hK₂, ← map_commutator]; exact ⟨_, hx₃' α hα, rfl⟩, rfl⟩)
      (congrArg Subtype.val (d.x₃_mul_self α))
  have hκXt : Xt.map κ ≤ L ⊔ zpowers t := by
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      obtain ⟨α, γ, hα, hγ, w, hw, rfl⟩ := d.exists_eq_of_mem_centSx₄Y_one hx
      simp only [Subgroup.subtype_apply, map_mul]
      exact mul_mem (mul_mem (hκ₁ α hα) (hκ₃ γ hγ)) (hκW' _ (mem_sup_left ⟨w, hw, rfl⟩))
    · rw [map_le_iff_le_comap, zpowers_le]
      exact hκW' t (mem_sup_right (mem_zpowers t))
  have hy₀A : a * t * a⁻¹ ∈ A := by
    rw [ha]
    exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left ⟨_, d.x₄_one_mem_zSx₄Y.1, rfl⟩)
  have hκy : κ (a * t * a⁻¹) = t := by rw [hκapp, ← hgt]; group
  have htκA : t ∈ A.map κ := ⟨_, hy₀A, hκy⟩
  have htκXt : t ∈ Xt.map κ := map_mono hAXt htκA
  set T₀ := Xt.map κ ⊓ L with hT₀
  set Z₀ := A.map κ ⊓ L with hZ₀
  have hXtd := h.eq_inf_sup_zpowers hκXt htκXt
  have hAd := h.eq_inf_sup_zpowers ((map_mono hAXt).trans hκXt) htκA
  have hcardT₀ : Nat.card T₀ = (2 ^ f) ^ 9 := by
    have h1 := h.card_sup_zpowers (E := T₀) inf_le_right
    rw [← hXtd, card_map_of_injective hκinj, h.card_sup_zpowers hX₁L,
      card_map_of_injective L.subtype_injective, d.card_centSx₄Y one_ne_zero] at h1
    omega
  have hcardZ₀ : Nat.card Z₀ = (2 ^ f) ^ 3 := by
    have h1 := h.card_sup_zpowers (E := Z₀) inf_le_right
    rw [← hAd, card_map_of_injective hκinj, h.card_sup_zpowers hZL,
      card_map_of_injective L.subtype_injective, d.card_zSx₄Y_one] at h1
    omega
  have hZ₀T₀ : Z₀ ≤ T₀ := inf_le_inf_right _ (map_mono hAXt)
  have hAXc : ∀ x ∈ A, ∀ y ∈ Xt, x * y = y * x := by
    intro x hx y hy
    have hcomm : ∀ z ∈ Z, ∀ w ∈ X₁, z * w = w * z := by
      rintro _ ⟨z, hz, rfl⟩ _ ⟨w, hw, rfl⟩
      exact congrArg Subtype.val (mem_centralizer_iff.1 (hZc hz) w hw).symm
    rcases (h.mem_sup_zpowers_iff hZL).1 hx with hx' | hx' <;>
      rcases (h.mem_sup_zpowers_iff hX₁L).1 hy with hy' | hy'
    · exact hcomm x hx' y hy'
    · have e := hcomm x hx' _ hy'
      have hxt := hLt x (hZL hx')
      calc x * y = x * (t * (t * y)) := by rw [htt]
        _ = t * (x * (t * y)) := by rw [← mul_assoc, hxt, mul_assoc]
        _ = t * (t * y * x) := by rw [e]
        _ = y * x := by rw [← mul_assoc, htt]
    · have e := hcomm _ hx' y hy'
      have hyt := hLt y (hX₁L hy')
      calc x * y = t * (t * x) * y := by rw [htt]
        _ = t * (y * (t * x)) := by rw [mul_assoc, e]
        _ = y * (t * (t * x)) := by rw [← mul_assoc, ← hyt, mul_assoc]
        _ = y * x := by rw [htt]
    · have e := hcomm _ hx' _ hy'
      have key : ∀ u v : G, t * u ∈ L → u * v = (t * u) * (t * v) := by
        intro u v hu
        have h1 := hLt _ hu
        calc u * v = t * (t * u) * (t * (t * v)) := by rw [htt, htt]
          _ = t * ((t * u) * t) * (t * v) := by group
          _ = t * (t * (t * u)) * (t * v) := by rw [h1]
          _ = (t * t) * (t * u) * (t * v) := by group
          _ = (t * u) * (t * v) := by rw [h.t_mul_t, one_mul]
      rw [key x y (hZL hx'), e, ← key y x (hX₁L hy')]
  have hZ₀c : ∀ z ∈ Z₀, ∀ w ∈ T₀, z * w = w * z := by
    rintro _ ⟨⟨x, hx, rfl⟩, -⟩ _ ⟨⟨y, hy, rfl⟩, -⟩
    rw [← map_mul, ← map_mul, hAXc x hx y hy]
  obtain ⟨hZab, -⟩ := h.isElemAbelian_sup_zpowers hZL
    (SectionRank.isElemAbelian_map d.isElemAbelian_zSx₄Y_one L.subtype)
  have hZ₀sq : ∀ z ∈ Z₀, z * z = 1 := by
    rintro _ ⟨⟨x, hx, rfl⟩, -⟩
    rw [← map_mul, ← sq, hZab.2 x hx, map_one]
  set T' := T₀.comap L.subtype with hT'
  set Z' := Z₀.comap L.subtype with hZ'
  have hcardT' : Nat.card T' = (2 ^ f) ^ 9 := by
    rw [← card_map_of_injective L.subtype_injective, hT', map_comap_eq_self (by
      rw [range_subtype]; exact inf_le_right), hcardT₀]
  have hcardZ' : Nat.card Z' = (2 ^ f) ^ 3 := by
    rw [← card_map_of_injective L.subtype_injective, hZ', map_comap_eq_self (by
      rw [range_subtype]; exact inf_le_right), hcardZ₀]
  have hZ'T' : Z' ≤ T' := comap_mono hZ₀T₀
  have hT'2 : IsPGroup 2 T' :=
    IsPGroup.of_card (n := f * 9) (by rw [hcardT', ← pow_mul])
  obtain ⟨P, hP⟩ := d.exists_sylow_eq_S
  obtain ⟨Q', hQ'⟩ := hT'2.exists_le_sylow
  obtain ⟨l, hl⟩ := MulAction.exists_smul_eq L P Q'
  have hlT : ∀ x ∈ T', l⁻¹ * x * l ∈ d.S := by
    intro x hx
    have hxQ := hQ' hx
    rw [← hl, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hxQ
    obtain ⟨s, hs, hsx⟩ := hxQ
    rw [← hP]
    have : l * s * l⁻¹ = x := by simpa [MulAut.smul_def, MulAut.conj_apply] using hsx
    rw [← this]
    simpa [mul_assoc] using hs
  set T := T'.map (MulAut.conj l⁻¹).toMonoidHom with hTdef
  set Zc := Z'.map (MulAut.conj l⁻¹).toMonoidHom with hZcdef
  have hTS : T ≤ d.S := by
    rintro _ ⟨x, hx, rfl⟩
    simpa using hlT x hx
  have hcardT : Nat.card T = (2 ^ f) ^ 9 := by
    rw [hTdef, card_map_of_injective (MulAut.conj l⁻¹).injective, hcardT']
  have hcardZc : Nat.card Zc = (2 ^ f) ^ 3 := by
    rw [hZcdef, card_map_of_injective (MulAut.conj l⁻¹).injective, hcardZ']
  have hZcT : Zc ≤ T := map_mono hZ'T'
  have hZcc : Zc ≤ centralizer (T : Set L) := by
    rintro _ ⟨z, hz, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨w, hw, rfl⟩
    have e := hZ₀c _ hz _ hw
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have e' : z * w = w * z := Subtype.ext (by simpa using e)
    calc l⁻¹ * w * l⁻¹⁻¹ * (l⁻¹ * z * l⁻¹⁻¹) = l⁻¹ * (w * z) * l⁻¹⁻¹ := by group
      _ = l⁻¹ * (z * w) * l⁻¹⁻¹ := by rw [e']
      _ = l⁻¹ * z * l⁻¹⁻¹ * (l⁻¹ * w * l⁻¹⁻¹) := by group
  have hZcab : CFSG.Open.IsElemAbelian 2 Zc := by
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · exact (mem_centralizer_iff.1 (hZcc x.2) y (hZcT y.2)).symm
    · obtain ⟨z, hz, rfl⟩ := hx
      have e := hZ₀sq _ hz
      have e' : z * z = 1 := Subtype.ext (by simpa using e)
      rw [sq, ← map_mul, e', map_one]
  have h89 : (2 ^ f) ^ 8 < (2 ^ f) ^ 9 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  have h23 : (2 ^ f) ^ 2 < (2 ^ f) ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  obtain ⟨α, -, -, -, hT9, -, -, h₁, -, hh₁⟩ := d.yamada_3_11_4 hTS (by rw [hcardT]; exact h89)
    hZcT hZcc hZcab (by rw [hcardZc]; exact h23)
  have hTα : T = d.centSx₄Y α := hT9 (by rw [hcardT])
  have hZ1 : Zc.map (MulAut.conj h₁).toMonoidHom = d.zSx₄Y 1 := by
    apply Subgroup.eq_of_le_of_card_ge
    · rw [← d.centSx₄Y_inf_centralizer one_ne_zero, ← hh₁]
      rintro _ ⟨z, hz, rfl⟩
      refine ⟨⟨z, hTα ▸ hZcT hz, rfl⟩, mem_centralizer_iff.2 ?_⟩
      rintro _ ⟨y, hy, rfl⟩
      have e := mem_centralizer_iff.1 (hZcc hz) y (hTα ▸ hy)
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc h₁ * y * h₁⁻¹ * (h₁ * z * h₁⁻¹) = h₁ * (y * z) * h₁⁻¹ := by group
        _ = h₁ * (z * y) * h₁⁻¹ := by rw [e]
        _ = h₁ * z * h₁⁻¹ * (h₁ * y * h₁⁻¹) := by group
    · rw [card_map_of_injective (MulAut.conj h₁).injective, hcardZc, d.card_zSx₄Y_one]
  set k : L := h₁ * l⁻¹ with hk
  have hZk : Z₀.map (MulAut.conj (k : G)).toMonoidHom = Z := by
    have e1 : Z₀ = Z'.map L.subtype := by
      rw [hZ', map_comap_eq_self (by rw [range_subtype]; exact inf_le_right)]
    have e2 : Z'.map (MulAut.conj k).toMonoidHom = d.zSx₄Y 1 := by
      rw [← hZ1, hZcdef, map_map]
      congr 1
      ext x
      simp [hk, mul_assoc]
    rw [e1, hZ, ← e2, map_map, map_map]
    congr 1
  have hkt : (k : G) * t = t * k := hLt _ k.2
  have hAk : (A.map κ).map (MulAut.conj (k : G)).toMonoidHom = A := by
    rw [hAd, Subgroup.map_sup, hZk]
    congr 1
    rw [MonoidHom.map_zpowers]
    congr 1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hkt, mul_inv_cancel_right]
  refine ⟨g * (k : G)⁻¹, ?_, ?_⟩
  · have hb' : (k : G) * g⁻¹ ∈ normalizer (A : Set G) :=
      mem_normalizer_of_conj_mem_D4 fun x hx => by
        have h1 : (k : G) * g⁻¹ * x * ((k : G) * g⁻¹)⁻¹ ∈
            (A.map κ).map (MulAut.conj (k : G)).toMonoidHom :=
          ⟨κ x, ⟨x, hx, rfl⟩, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hκapp,
            mul_inv_rev, inv_inv]; group⟩
        rwa [hAk] at h1
    have := inv_mem hb'
    rwa [mul_inv_rev, inv_inv] at this
  · calc g * (k : G)⁻¹ * t * (g * (k : G)⁻¹)⁻¹ = g * ((k : G)⁻¹ * (t * k)) * g⁻¹ := by group
      _ = g * t * g⁻¹ := by rw [← hkt]; group
      _ = t * (d.x₄ 1 : G) := by rw [hgt, ha]

theorem false_of_normalizer_conj (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hY : ∀ a : G, a * t * a⁻¹ ∈ d.Y.map L.subtype ⊔ zpowers t → a * t * a⁻¹ = t) {b : G}
    (hb : b ∈ normalizer (((d.zSx₄Y 1).map L.subtype ⊔ zpowers t : Subgroup G) : Set G))
    (hbt : b * t * b⁻¹ = t * (d.x₄ 1 : G)) : False := by
  set Z := (d.zSx₄Y 1).map L.subtype with hZ
  set A := Z ⊔ zpowers t with hA
  set H := normalizer (A : Set G) with hH
  have hZL : Z ≤ L := map_subtype_le _
  have hYL : d.Y.map L.subtype ≤ L := map_subtype_le _
  have hAi : ∀ x, x ∈ A ↔ x ∈ Z ∨ t * x ∈ Z := fun x => h.mem_sup_zpowers_iff hZL
  have hYi : ∀ x, x ∈ d.Y.map L.subtype ⊔ zpowers t ↔
      x ∈ d.Y.map L.subtype ∨ t * x ∈ d.Y.map L.subtype := fun x => h.mem_sup_zpowers_iff hYL
  have htt : ∀ x : G, t * (t * x) = x := fun x => by rw [← mul_assoc, h.t_mul_t, one_mul]
  have hLt : ∀ l ∈ L, l * t = t * l := fun l hl =>
    mem_centralizer_singleton_iff.1 (h.L_le_centralizer hl)
  have hHA : ∀ k ∈ H, ∀ x ∈ A, k * x * k⁻¹ ∈ A := fun k hk x hx =>
    (mem_normalizer_iff.1 hk x).1 hx
  have htA : t ∈ A := mem_sup_right (mem_zpowers t)
  have hne : ∀ g : G, g * t * g⁻¹ ≠ 1 := fun g h1 => h.t_ne_one (by
    calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group)
  have hcase : ∀ k ∈ H, t * (k * t * k⁻¹) ∈ Z := fun k hk =>
    ((hAi _).1 (hHA k hk t htA)).resolve_left fun hz => h.conj_not_mem_L d k (hZL hz)
  have hYZ : d.Y ≤ d.zSx₄Y 1 := fun y hy => by
    obtain ⟨a₅, a₆, rfl⟩ := d.mem_Y_coords hy
    refine d.mem_zSx₄Y_one.2 ⟨0, a₅, a₆, ?_⟩
    simp only [TrialityD4Data.nf_apply, d.x₁_zero, d.x₂_zero, d.x₃_zero, Subfield.coe_zero,
      d.x₄_zero, one_mul]
  have hx₄ := d.x₄_one_mem_zSx₄Y
  have hfull : ∀ z : L, z ∈ d.zSx₄Y 1 → z ∉ d.Y → ∃ k ∈ H, k * t * k⁻¹ = t * z := by
    intro z hz hzY
    obtain ⟨n, hnZ, hnz⟩ := d.exists_conj_x₄_one_eq hz hzY
    have hnH : (n : G) ∈ H := mem_normalizer_of_conj_mem_D4 fun x hx => by
      rcases (hAi x).1 hx with hx | hx
      · obtain ⟨y, hy, rfl⟩ := hx
        exact mem_sup_left ⟨_, (mem_normalizer_iff.1 hnZ y).1 hy, by simp⟩
      · obtain ⟨y, hy, hyx⟩ := hx
        have e : (n : G) * x * (n : G)⁻¹ = t * ((n * y * n⁻¹ : L) : G) := by
          have hx' : x = t * (y : G) := by rw [show (y : G) = t * x from hyx, htt]
          rw [hx', ← mul_assoc, hLt n n.2]
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          group
        rw [e]
        exact mul_mem htA (mem_sup_left ⟨_, (mem_normalizer_iff.1 hnZ y).1 hy, rfl⟩)
    refine ⟨(n : G) * b, mul_mem hnH hb, ?_⟩
    have hnz' : (n : G) * (d.x₄ 1 : G) * (n : G)⁻¹ = (z : G) := by
      rw [← hnz]
      simp
    calc (n : G) * b * t * ((n : G) * b)⁻¹ = n * (b * t * b⁻¹) * (n : G)⁻¹ := by group
      _ = (n : G) * t * (d.x₄ 1 : G) * (n : G)⁻¹ := by rw [hbt]; group
      _ = t * ((n : G) * (d.x₄ 1 : G) * (n : G)⁻¹) := by rw [hLt n n.2]; group
      _ = t * z := by rw [hnz']
  have hprod : ∀ z ∈ Z, ∃ k₁ ∈ H, ∃ k₂ ∈ H, z = (k₁ * t * k₁⁻¹) * (k₂ * t * k₂⁻¹) := by
    rintro _ ⟨z, hz, rfl⟩
    by_cases hzY : z ∈ d.Y
    · have hx₄z : d.x₄ 1 * z ∉ d.Y := fun h1 => hx₄.2 (by
        have := mul_mem h1 (inv_mem hzY)
        rwa [mul_inv_cancel_right] at this)
      obtain ⟨k₁, hk₁, hk₁e⟩ := hfull _ hx₄.1 hx₄.2
      obtain ⟨k₂, hk₂, hk₂e⟩ := hfull _ (mul_mem hx₄.1 (hYZ hzY)) hx₄z
      refine ⟨k₁, hk₁, k₂, hk₂, ?_⟩
      rw [hk₁e, hk₂e]
      have hx₄t : (d.x₄ 1 : G) * t = t * d.x₄ 1 := hLt _ (d.x₄ 1).2
      simp only [Subgroup.subtype_apply, Subgroup.coe_mul]
      calc (z : G) = t * t * ((d.x₄ 1 : G) * d.x₄ 1 * z) := by
            rw [h.t_mul_t, one_mul, show (d.x₄ 1 : G) * d.x₄ 1 = ((d.x₄ 1 * d.x₄ 1 : L) : G) from
              rfl, d.x₄_mul_self, OneMemClass.coe_one, one_mul]
        _ = t * (t * d.x₄ 1) * d.x₄ 1 * z := by group
        _ = t * (d.x₄ 1 * t) * d.x₄ 1 * z := by rw [hx₄t]
        _ = t * d.x₄ 1 * (t * (d.x₄ 1 * z)) := by group
    · obtain ⟨k₂, hk₂, hk₂e⟩ := hfull _ hz hzY
      refine ⟨1, one_mem _, k₂, hk₂, ?_⟩
      rw [hk₂e, inv_one, mul_one, one_mul, htt]
      rfl
  have hHZ : ∀ k ∈ H, ∀ z ∈ Z, k * z * k⁻¹ ∈ Z := by
    intro k hk z hz
    obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := hprod z hz
    rw [show k * (k₁ * t * k₁⁻¹ * (k₂ * t * k₂⁻¹)) * k⁻¹ =
      ((k * k₁) * t * (k * k₁)⁻¹) * ((k * k₂) * t * (k * k₂)⁻¹) by group]
    have h1 := hcase _ (mul_mem hk hk₁)
    have h2 := hcase _ (mul_mem hk hk₂)
    have e : (k * k₁) * t * (k * k₁)⁻¹ * ((k * k₂) * t * (k * k₂)⁻¹) =
        (t * ((k * k₁) * t * (k * k₁)⁻¹)) * (t * ((k * k₂) * t * (k * k₂)⁻¹)) := by
      have hc : (t * ((k * k₁) * t * (k * k₁)⁻¹)) * t = t * (t * ((k * k₁) * t * (k * k₁)⁻¹)) :=
        hLt _ (hZL h1)
      calc (k * k₁) * t * (k * k₁)⁻¹ * ((k * k₂) * t * (k * k₂)⁻¹) =
          t * (t * ((k * k₁) * t * (k * k₁)⁻¹)) * ((k * k₂) * t * (k * k₂)⁻¹) := by rw [htt]
        _ = (t * ((k * k₁) * t * (k * k₁)⁻¹)) * t * ((k * k₂) * t * (k * k₂)⁻¹) := by rw [← hc]
        _ = _ := by group
    rw [e]
    exact mul_mem h1 h2
  have hty : ∀ k ∈ H, ∀ y : L, y ∈ d.Y → y ≠ 1 →
      k * (t * y) * k⁻¹ ∈ d.Y.map L.subtype ⊔ zpowers t := by
    intro k hk y hy hy1
    have hyZ : (y : G) ∈ Z := ⟨y, hYZ hy, rfl⟩
    have hE := hHA k hk _ (mul_mem htA (mem_sup_left hyZ))
    have hnotZ : k * (t * y) * k⁻¹ ∉ Z := by
      intro hZ'
      have h1 := hHZ _ (inv_mem hk) _ hZ'
      rw [show k⁻¹ * (k * (t * y) * k⁻¹) * k⁻¹⁻¹ = t * y by group] at h1
      exact h.t_not_mem_L (by
        have := mul_mem (hZL h1) (inv_mem y.2)
        rwa [mul_inv_cancel_right] at this)
    obtain ⟨z, hz, hze⟩ := ((hAi _).1 hE).resolve_left hnotZ
    by_cases hzY : z ∈ d.Y
    · exact (hYi _).2 (Or.inr ⟨z, hzY, hze⟩)
    · exfalso
      obtain ⟨k', -, hk'⟩ := hfull z hz hzY
      have h3 : (k⁻¹ * k') * t * (k⁻¹ * k')⁻¹ = t * y := by
        rw [show (k⁻¹ * k') * t * (k⁻¹ * k')⁻¹ = k⁻¹ * (k' * t * k'⁻¹) * k by group, hk']
        simp only [Subgroup.subtype_apply] at hze
        rw [hze, htt]
        group
      have h4 := hY _ (by rw [h3]; exact (hYi _).2 (Or.inr (by rw [htt]; exact ⟨y, hy, rfl⟩)))
      rw [h3] at h4
      exact hy1 (Subtype.ext (by
        calc (y : G) = t⁻¹ * (t * y) := by group
          _ = 1 := by rw [h4, inv_mul_cancel]))
  have hy₁ : d.x₅ 1 ∈ d.Y ∧ d.x₅ 1 ≠ 1 :=
    ⟨d.x₅_mem_Y 1, fun h1 => one_ne_zero (d.x₅_injective (h1.trans d.x₅_zero.symm))⟩
  have hy₂ : d.x₆ 1 ∈ d.Y ∧ d.x₆ 1 ≠ 1 :=
    ⟨d.x₆_mem_Y 1, fun h1 => one_ne_zero (d.x₆_eq_one_iff.1 h1)⟩
  have hy₃ : d.x₅ 1 * d.x₆ 1 ∈ d.Y ∧ d.x₅ 1 * d.x₆ 1 ≠ 1 := by
    refine ⟨mul_mem hy₁.1 hy₂.1, fun h1 => ?_⟩
    have h2 := d.x₄_mem_Y_iff (a := 0)
    have : d.x₅ 1 ∈ d.V := by
      rw [eq_inv_of_mul_eq_one_left h1]
      exact inv_mem (d.x₆_mem_V 1)
    exact one_ne_zero (d.x₅_mem_V_iff.1 this)
  have hall : ∀ k ∈ H, k * t * k⁻¹ = t := by
    intro k hk
    refine hY k ?_
    have e₀ : t = (t * (d.x₅ 1 : G)) * (t * (d.x₆ 1 : G)) * (t * ((d.x₅ 1 * d.x₆ 1 : L) : G)) := by
      set p := (d.x₅ 1 : G) with hp
      set r := (d.x₆ 1 : G) with hr
      have h5 : p * t = t * p := hLt _ (d.x₅ 1).2
      have h6 : r * t = t * r := hLt _ (d.x₆ 1).2
      have h56 : p * r = r * p := congrArg Subtype.val (d.commute₅₆ 1 1).eq
      have h55 : p * p = 1 := congrArg Subtype.val (d.x₅_mul_self 1)
      have h66 : r * r = 1 := congrArg Subtype.val (d.x₆_mul_self 1)
      have e : ((d.x₅ 1 * d.x₆ 1 : L) : G) = p * r := rfl
      rw [e]
      symm
      calc (t * p) * (t * r) * (t * (p * r)) = t * (p * t) * r * t * p * r := by group
        _ = t * (t * p) * r * t * p * r := by rw [h5]
        _ = (t * t) * p * (r * t) * p * r := by group
        _ = (t * t) * p * (t * r) * p * r := by rw [h6]
        _ = (t * t) * (p * t) * r * p * r := by group
        _ = (t * t) * (t * p) * r * p * r := by rw [h5]
        _ = (t * t) * t * p * (r * p) * r := by group
        _ = (t * t) * t * p * (p * r) * r := by rw [← h56]
        _ = (t * t) * t * (p * p) * (r * r) := by group
        _ = t := by rw [h.t_mul_t, h55, h66, one_mul, mul_one, mul_one]
    rw [show k * t * k⁻¹ = k * ((t * (d.x₅ 1 : G)) * (t * (d.x₆ 1 : G)) *
      (t * ((d.x₅ 1 * d.x₆ 1 : L) : G))) * k⁻¹ from by rw [← e₀]]
    rw [show k * ((t * (d.x₅ 1 : G)) * (t * (d.x₆ 1 : G)) * (t * ((d.x₅ 1 * d.x₆ 1 : L) : G))) *
      k⁻¹ = (k * (t * (d.x₅ 1 : G)) * k⁻¹) * (k * (t * (d.x₆ 1 : G)) * k⁻¹) *
        (k * (t * ((d.x₅ 1 * d.x₆ 1 : L) : G)) * k⁻¹) by group]
    exact mul_mem (mul_mem (hty k hk _ hy₁.1 hy₁.2) (hty k hk _ hy₂.1 hy₂.2))
      (hty k hk _ hy₃.1 hy₃.2)
  have h1 := hall b hb
  rw [hbt] at h1
  exact hx₄.2 (by
    have h2 : (d.x₄ 1 : G) = 1 := by
      calc (d.x₄ 1 : G) = t⁻¹ * (t * d.x₄ 1) := by group
        _ = 1 := by rw [h1, inv_mul_cancel]
    rw [show d.x₄ 1 = 1 from Subtype.ext h2]
    exact one_mem _)

theorem exists_conj_mem_Y_sup (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hq : 4 ≤ 2 ^ f) : ∃ a : G, a * t * a⁻¹ ∈ d.Y.map L.subtype ⊔ zpowers t ∧ a * t * a⁻¹ ≠ t := by
  by_contra hcon
  push Not at hcon
  obtain ⟨a, ha⟩ := h.exists_conj_eq_mul_x₄ d hcon
  obtain ⟨b, hb, hbt⟩ := h.exists_normalizer_conj_eq_mul_x₄ d hq ha
  exact h.false_of_normalizer_conj d hcon hb hbt

end Setup

end CFSG.LocalAnalysis.EvenBN.TrialityD4
