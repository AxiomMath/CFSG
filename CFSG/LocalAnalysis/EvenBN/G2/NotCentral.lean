module

public import CFSG.LocalAnalysis.EvenBN.G2.NotCentralPrelim
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotZStar

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_iff)
open scoped commutatorElement

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Main

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem exists_conj_mem_tL_of_outer (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) {g : G} (hgC : g⁻¹ * t * g ∈ centralizer ({t} : Set G))
    (hout : h.act d ⟨g⁻¹ * t * g, hgC⟩ ∉ inner (adjointGroup .G2 K)) :
    ∃ a : G, a * t * a⁻¹ ≠ t ∧ (a * t * a⁻¹ ∈ L ∨ t * (a * t * a⁻¹) ∈ L) := by
  set t' := g⁻¹ * t * g with ht'
  have ht'2 : t' * t' = 1 := by
    calc t' * t' = g⁻¹ * (t * t) * g := by rw [ht']; group
      _ = 1 := by rw [h.t_mul_t, mul_one, inv_mul_cancel]
  set α := h.act d ⟨t', hgC⟩ with hα
  have hα2 : orderOf α = 2 := by
    refine orderOf_eq_prime ?_ fun h1 => hout (h1 ▸ one_mem _)
    rw [sq, hα, ← map_mul, show (⟨t', hgC⟩ * ⟨t', hgC⟩ : centralizer ({t} : Set G)) = 1 from
      Subtype.ext ht'2, map_one]
  obtain hin | ⟨⟨e, he⟩, -⟩ := even_G2_involution_inner_or_canonical_field h.two_le K hK α hα2
  · exact absurd hin hout
  have he1 : 1 ≤ e := by have := h.two_le; omega
  have hK' : Nat.card K = 2 ^ (2 * e) := by rw [hK, he, two_mul]
  obtain ⟨w, ⟨w₀, rfl⟩, hαw⟩ := Model.exists_inner_conj_eq_of_outer hK' he1 hα2 hout
  have hfix : ∀ x : adjointGroup .G2 K, (Model.fieldAut K ^ e) x = x →
      α (w₀⁻¹ * x * w₀) = w₀⁻¹ * x * w₀ := by
    intro x hx
    rw [hαw, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply,
      show w₀ * (w₀⁻¹ * x * w₀) * w₀⁻¹ = x by group, hx, ← map_inv, MulAut.conj_apply, inv_inv]
  have hcomm : ∀ x : adjointGroup .G2 K, α x = x → t' * d.emb x = d.emb x * t' := by
    intro x hx
    have h1 := d.emb_act_apply ⟨t', h.centralizer_le_normalizer hgC⟩ x
    rw [← h.act_apply d ⟨t', hgC⟩, ← hα, hx] at h1
    calc t' * d.emb x = t' * d.emb x * t'⁻¹ * t' := by group
      _ = d.emb x * t' := by rw [← h1]
  have hroot : ∀ s : Fin Tag.G2.rank → ℤ,
      (Model.fieldAut K ^ e) ⟨pinnedX .G2 K s 1, pinnedX_mem_adjointGroup s 1⟩ =
        ⟨pinnedX .G2 K s 1, pinnedX_mem_adjointGroup s 1⟩ := fun s =>
    Subtype.ext (by rw [Model.fieldAut_pow_pinnedX, one_pow])
  set xa : adjointGroup .G2 K := ⟨pinnedX .G2 K g2a 1, pinnedX_mem_adjointGroup g2a 1⟩
  set xb : adjointGroup .G2 K := ⟨pinnedX .G2 K g2b 1, pinnedX_mem_adjointGroup g2b 1⟩
  set xc : adjointGroup .G2 K := ⟨pinnedX .G2 K g2c 1, pinnedX_mem_adjointGroup g2c 1⟩
  have habc : ⁅xa, xb⁆ = xc := by
    refine Subtype.ext ?_
    rw [commutatorElement_def]
    simp only [coe_mul, coe_inv, xa, xb, xc]
    rw [← commutatorElement_def, pinnedX_a_eq_g2N, pinnedX_b_eq_g2N, pinnedX_c_eq_g2N,
      g2N_commutator_coords]
    refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_ <;> ring
  have hxc1 : xc ≠ 1 := fun h1 => by
    have h2 : pinnedX .G2 K g2c 1 = 1 := congrArg Subtype.val h1
    rw [pinnedX_c_eq_g2N, ← g2N_zero] at h2
    exact one_ne_zero (g2N_injective h2).2.2.2.2.2
  have hxc2 : xc * xc = 1 := Subtype.ext (by
    simp only [coe_mul, xc]
    rw [← pinnedX_add, CharTwo.add_self_eq_zero, pinnedX_zero, coe_one])
  set a := d.emb (w₀⁻¹ * xa * w₀) with ha
  set b := d.emb (w₀⁻¹ * xb * w₀) with hb
  set s := d.emb (w₀⁻¹ * xc * w₀) with hs
  have hsab : s = ⁅a, b⁆ := by
    rw [hs, ha, hb, ← map_commutatorElement, ← habc]
    congr 1
    simp only [commutatorElement_def]
    group
  have hs1 : s ≠ 1 := fun h1 => hxc1 (by
    have h2 := d.emb_injective (h1.trans (map_one d.emb).symm)
    calc xc = w₀ * (w₀⁻¹ * xc * w₀) * w₀⁻¹ := by group
      _ = 1 := by rw [h2]; group)
  have hs2 : s * s = 1 := by
    rw [hs, ← map_mul, ← map_one d.emb]
    congr 1
    calc w₀⁻¹ * xc * w₀ * (w₀⁻¹ * xc * w₀) = w₀⁻¹ * (xc * xc) * w₀ := by group
      _ = 1 := by rw [hxc2, mul_one, inv_mul_cancel]
  have hat : t' * a = a * t' := hcomm _ (hfix _ (hroot g2a))
  have hbt : t' * b = b * t' := hcomm _ (hfix _ (hroot g2b))
  have hst : t' * s = s * t' := hcomm _ (hfix _ (hroot g2c))
  have hconj : ∀ y : G, t' * y = y * t' → g * y * g⁻¹ ∈ centralizer ({t} : Set G) := by
    intro y hy
    rw [mem_centralizer_singleton_iff]
    calc g * y * g⁻¹ * t = g * (y * t') * g⁻¹ := by rw [ht']; group
      _ = g * (t' * y) * g⁻¹ := by rw [hy]
      _ = t * (g * y * g⁻¹) := by rw [ht']; group
  have hsL : g * s * g⁻¹ ∈ L ⊔ (centralizer (L : Set G) ⊓ centralizer ({t} : Set G)) := by
    have hmem : (⟨g * s * g⁻¹, hconj s hst⟩ : centralizer ({t} : Set G)) =
        ⁅(⟨g * a * g⁻¹, hconj a hat⟩ : centralizer ({t} : Set G)), ⟨g * b * g⁻¹, hconj b hbt⟩⁆ := by
      refine Subtype.ext ?_
      change g * s * g⁻¹ = ⁅g * a * g⁻¹, g * b * g⁻¹⁆
      rw [hsab]
      simp only [commutatorElement_def]
      group
    refine (h.act_mem_inner_iff d ⟨g * s * g⁻¹, hconj s hst⟩).1 ?_
    rw [hmem, map_commutatorElement]
    exact Model.commutatorElement_mem_inner hK h.two_le _ _
  have hs2' : g * s * g⁻¹ * (g * s * g⁻¹) = 1 := by
    calc g * s * g⁻¹ * (g * s * g⁻¹) = g * (s * s) * g⁻¹ := by group
      _ = 1 := by rw [hs2, mul_one, mul_inv_cancel]
  have hsLt := h.mem_or_mul_mem_of_mem_sup_kernel hsL hs2'
  have hsC : s ∈ centralizer ({t} : Set G) := h.L_le_centralizer (d.emb_mem _)
  have hβ : h.act d ⟨t' * s, mul_mem hgC hsC⟩ = α * MulAut.conj (w₀⁻¹ * xc * w₀) := by
    rw [show (⟨t' * s, mul_mem hgC hsC⟩ : centralizer ({t} : Set G)) =
      ⟨t', hgC⟩ * ⟨d.emb (w₀⁻¹ * xc * w₀), h.L_le_centralizer (d.emb_mem _)⟩ from rfl,
      map_mul, h.act_emb]
  have hβout : h.act d ⟨t' * s, mul_mem hgC hsC⟩ ∉ inner (adjointGroup .G2 K) := by
    rw [hβ]
    intro hin
    refine hout ?_
    have hcin : MulAut.conj (w₀⁻¹ * xc * w₀) ∈
        CFSG.ComponentClassification.OuterAutomorphisms.inner (adjointGroup .G2 K) := ⟨_, rfl⟩
    have := mul_mem hin (inv_mem hcin)
    rwa [mul_inv_cancel_right] at this
  have hβ2 : orderOf (h.act d ⟨t' * s, mul_mem hgC hsC⟩) = 2 := by
    refine orderOf_eq_prime ?_ fun h1 => hβout (h1 ▸ one_mem _)
    rw [sq, ← map_mul]
    have : (⟨t' * s, mul_mem hgC hsC⟩ * ⟨t' * s, mul_mem hgC hsC⟩ :
        centralizer ({t} : Set G)) = 1 := Subtype.ext (by
      calc t' * s * (t' * s) = t' * (s * t') * s := by group
        _ = t' * t' * (s * s) := by rw [← hst]; group
        _ = 1 := by rw [ht'2, hs2, one_mul])
    rw [this, map_one]
  obtain ⟨w', ⟨w₁, rfl⟩, hβw⟩ := Model.exists_inner_conj_eq_of_outer hK' he1 hβ2 hβout
  set m₀ := w₀⁻¹ * w₁ with hm₀
  have hβm : h.act d ⟨t' * s, mul_mem hgC hsC⟩ = (MulAut.conj m₀)⁻¹ * α * MulAut.conj m₀ := by
    rw [hβw, hαw, hm₀, map_mul, map_inv]
    group
  set m := d.emb m₀ with hm
  have hmC : m ∈ centralizer ({t} : Set G) := h.L_le_centralizer (d.emb_mem _)
  have hz : h.act d ⟨(m⁻¹ * t' * m)⁻¹ * (t' * s), mul_mem (inv_mem (mul_mem (mul_mem
      (inv_mem hmC) hgC) hmC)) (mul_mem hgC hsC)⟩ = 1 := by
    rw [show (⟨(m⁻¹ * t' * m)⁻¹ * (t' * s), mul_mem (inv_mem (mul_mem (mul_mem (inv_mem hmC) hgC)
      hmC)) (mul_mem hgC hsC)⟩ : centralizer ({t} : Set G)) =
      ((⟨m, hmC⟩ : centralizer ({t} : Set G))⁻¹ * ⟨t', hgC⟩ * ⟨m, hmC⟩)⁻¹ *
        ⟨t' * s, mul_mem hgC hsC⟩ from rfl, map_mul, map_inv, map_mul, map_mul, map_inv, hβm,
      ← hα, show (⟨m, hmC⟩ : centralizer ({t} : Set G)) =
        ⟨d.emb m₀, h.L_le_centralizer (d.emb_mem m₀)⟩ from rfl, h.act_emb]
    group
  have hzC := (h.act_eq_one_iff d _).1 hz
  have hzL : (m⁻¹ * t' * m)⁻¹ * (t' * s) ∈ L := by
    have ht'N := h.centralizer_le_normalizer (inv_mem hgC)
    have h1 : t'⁻¹ * m * t'⁻¹⁻¹ ∈ L := (mem_normalizer_iff.1 ht'N m).1 (d.emb_mem _)
    rw [show (m⁻¹ * t' * m)⁻¹ * (t' * s) = m⁻¹ * (t'⁻¹ * m * t'⁻¹⁻¹) * s by group]
    exact mul_mem (mul_mem (inv_mem (d.emb_mem _)) h1) (d.emb_mem _)
  have hz1 : (m⁻¹ * t' * m)⁻¹ * (t' * s) = 1 := by
    have : (m⁻¹ * t' * m)⁻¹ * (t' * s) ∈ L ⊓ centralizer (L : Set G) := ⟨hzL, hzC⟩
    rwa [h.inf_centralizer_eq_bot, mem_bot] at this
  have hts : t' * s = m⁻¹ * t' * m := (inv_mul_eq_one.1 hz1).symm
  refine ⟨g * m⁻¹ * g⁻¹, ?_, ?_⟩
  · intro h1
    refine hs1 ?_
    have h2 : g * m⁻¹ * g⁻¹ * t * (g * m⁻¹ * g⁻¹)⁻¹ = t * (g * s * g⁻¹) := by
      calc g * m⁻¹ * g⁻¹ * t * (g * m⁻¹ * g⁻¹)⁻¹ = g * (m⁻¹ * t' * m) * g⁻¹ := by rw [ht']; group
        _ = g * (t' * s) * g⁻¹ := by rw [hts]
        _ = t * (g * s * g⁻¹) := by rw [ht']; group
    rw [h2] at h1
    have h3 : g * s * g⁻¹ = 1 := by
      calc g * s * g⁻¹ = t⁻¹ * (t * (g * s * g⁻¹)) := by group
        _ = 1 := by rw [h1, inv_mul_cancel]
    calc s = g⁻¹ * (g * s * g⁻¹) * g := by group
      _ = 1 := by rw [h3]; group
  · have h2 : g * m⁻¹ * g⁻¹ * t * (g * m⁻¹ * g⁻¹)⁻¹ = t * (g * s * g⁻¹) := by
      calc g * m⁻¹ * g⁻¹ * t * (g * m⁻¹ * g⁻¹)⁻¹ = g * (m⁻¹ * t' * m) * g⁻¹ := by rw [ht']; group
        _ = g * (t' * s) * g⁻¹ := by rw [hts]
        _ = t * (g * s * g⁻¹) := by rw [ht']; group
    rw [h2]
    rcases hsLt with h3 | h3
    · right
      rwa [← mul_assoc, h.t_mul_t, one_mul]
    · left
      exact h3

theorem exists_conj_mem_tL (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) :
    ∃ a : G, a * t * a⁻¹ ≠ t ∧ (a * t * a⁻¹ ∈ L ∨ t * (a * t * a⁻¹) ∈ L) := by
  have := h.simple
  obtain ⟨g, hgC, hgt⟩ :=
    CFSG.SeitzReduction.F4Pilot.exists_conj_ne_mem_centralizer_of_isSimpleGroup h.nonab h.ht
  by_cases hin : h.act d ⟨g⁻¹ * t * g, hgC⟩ ∈ inner (adjointGroup .G2 K)
  · refine ⟨g⁻¹, by rw [inv_inv]; exact hgt, ?_⟩
    rw [inv_inv]
    have hx2 : g⁻¹ * t * g * (g⁻¹ * t * g) = 1 := by
      calc g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
        _ = 1 := by rw [h.t_mul_t, mul_one, inv_mul_cancel]
    exact h.mem_or_mul_mem_of_mem_sup_kernel ((h.act_mem_inner_iff d _).1 hin) hx2
  · exact h.exists_conj_mem_tL_of_outer d hK hgC hin

theorem exists_conj_eq_xv (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hY : ∀ a : G, a * t * a⁻¹ ∈ d.Y ⊔ zpowers t → a * t * a⁻¹ = t) :
    ∃ a : G, a * t * a⁻¹ = d.xv ∨ a * t * a⁻¹ = t * d.xv := by
  obtain ⟨a, hat, hLt⟩ := h.exists_conj_mem_tL d hK
  set x := a * t * a⁻¹ with hx
  have hx2 : x * x = 1 := by
    calc x * x = a * (t * t) * a⁻¹ := by rw [hx]; group
      _ = 1 := by rw [h.t_mul_t, mul_one, mul_inv_cancel]
  have hx1 : x ≠ 1 := fun h1 => h.t_ne_one (by
    calc t = a⁻¹ * x * a := by rw [hx]; group
      _ = 1 := by rw [h1]; group)
  have key : ∀ l : G, l ∈ L → l ≠ 1 → l * l = 1 → (x = l ∨ x = t * l) →
      ∃ a' : G, a' * t * a'⁻¹ = d.xv ∨ a' * t * a'⁻¹ = t * d.xv := by
    intro l hl hl1 hl2 hxl
    obtain ⟨m, hm, hml | hml⟩ :=
      d.exists_conj_xc_or_xv hl (orderOf_eq_prime (by rw [sq]; exact hl2) hl1)
    · exfalso
      have hmt : m * t = t * m := mem_centralizer_singleton_iff.1 (h.L_le_centralizer hm)
      have e : m * a * t * (m * a)⁻¹ = m * x * m⁻¹ := by rw [hx]; group
      have hxcY : d.xc ∈ d.Y := (d.inclusions).1 (d.xv_xc_spec).2.2.2.1
      have hmem : m * a * t * (m * a)⁻¹ ∈ d.Y ⊔ zpowers t := by
        rw [e]
        rcases hxl with h1 | h1
        · rw [h1, hml]
          exact mem_sup_left hxcY
        · rw [h1, show m * (t * l) * m⁻¹ = t * (m * l * m⁻¹) by
            rw [← mul_assoc m t l, hmt]; group, hml]
          exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left hxcY)
      have h2 := hY _ hmem
      rw [e] at h2
      apply hat
      calc x = m⁻¹ * (m * x * m⁻¹) * m := by group
        _ = m⁻¹ * (t * m) := by rw [h2]; group
        _ = t := by rw [← hmt]; group
    · refine ⟨m * a, ?_⟩
      have hmt : m * t = t * m := mem_centralizer_singleton_iff.1 (h.L_le_centralizer hm)
      rw [show m * a * t * (m * a)⁻¹ = m * x * m⁻¹ by rw [hx]; group]
      rcases hxl with h1 | h1
      · left
        rw [h1, hml]
      · right
        rw [h1, show m * (t * l) * m⁻¹ = t * (m * l * m⁻¹) by
          rw [← mul_assoc m t l, hmt]; group, hml]
  rcases hLt with hxL | htxL
  · exact key x hxL hx1 hx2 (Or.inl rfl)
  · have htx : x * t = t * x := by
      have h1 : t * x * t = t * (t * x) := mem_centralizer_singleton_iff.1 (h.L_le_centralizer htxL)
      calc x * t = t * (t * x * t) := by rw [← mul_assoc, ← mul_assoc, h.t_mul_t, one_mul]
        _ = t * x := by rw [h1, ← mul_assoc, h.t_mul_t, one_mul]
    refine key (t * x) htxL (fun h1 => hat ?_) ?_ (Or.inr ?_)
    · calc x = t * (t * x) := by rw [← mul_assoc, h.t_mul_t, one_mul]
        _ = t := by rw [h1, mul_one]
    · calc t * x * (t * x) = t * (x * t) * x := by group
        _ = t * t * (x * x) := by rw [htx]; group
        _ = 1 := by rw [h.t_mul_t, hx2, one_mul]
    · rw [← mul_assoc, h.t_mul_t, one_mul]

theorem exists_normalizer_conj_eq (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    {a : G} (ha : a * t * a⁻¹ = d.xv ∨ a * t * a⁻¹ = t * d.xv) :
    ∃ b ∈ normalizer ((d.W ⊔ zpowers t : Subgroup G) : Set G), b * t * b⁻¹ = a * t * a⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK4 : 4 ≤ Nat.card K := hK ▸ h.four_le
  have hf1 : 1 ≤ f := by have := h.two_le; omega
  set E := d.W ⊔ zpowers t with hE
  set y₀ := a * t * a⁻¹ with hy₀
  obtain ⟨hvW, -, -, -, -, -⟩ := d.xv_xc_spec
  obtain ⟨hEab, hEcard⟩ := h.isElemAbelian_W_sup_zpowers d
  have hWL : d.W ≤ L := d.image_le _
  have hy₀E : y₀ ∈ E := by
    rcases ha with h1 | h1 <;> rw [h1]
    · exact mem_sup_left hvW
    · exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left hvW)
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy => by
    have := hEab.1
    exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : E) ⟨y, hy⟩)
  obtain ⟨hBv, hBW⟩ := d.leviB_spec
  have hBL : d.leviB ≤ L := d.image_le _
  have hBt : ∀ l ∈ d.leviB, l * t = t * l := fun l hl =>
    mem_centralizer_singleton_iff.1 (h.L_le_centralizer (hBL hl))
  have hBy : ∀ l ∈ d.leviB, l * y₀ = y₀ * l := by
    intro l hl
    rcases ha with h1 | h1 <;> rw [h1]
    · exact hBv l hl
    · calc l * (t * d.xv) = t * (l * d.xv) := by rw [← mul_assoc, hBt l hl, mul_assoc]
        _ = t * (d.xv * l) := by rw [hBv l hl]
        _ = t * d.xv * l := by group
  have hBE : ∀ l ∈ d.leviB, ∀ x ∈ E, l * x * l⁻¹ ∈ E := by
    intro l hl x hx
    rcases (h.mem_sup_zpowers_iff hWL).1 hx with hxW | hxW
    · exact mem_sup_left ((mem_normalizer_iff.1 (hBW hl) x).1 hxW)
    · refine (h.mem_sup_zpowers_iff hWL).2 (Or.inr ?_)
      have e : t * (l * x * l⁻¹) = l * (t * x) * l⁻¹ := by
        calc t * (l * x * l⁻¹) = (t * l) * x * l⁻¹ := by group
          _ = (l * t) * x * l⁻¹ := by rw [hBt l hl]
          _ = l * (t * x) * l⁻¹ := by group
      rw [e]
      exact (mem_normalizer_iff.1 (hBW hl) _).1 hxW
  have hEaC : E.map (MulAut.conj a⁻¹).toMonoidHom ≤ centralizer ({t} : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    have hxy := hEcomm x hx y₀ hy₀E
    calc a⁻¹ * x * a * t = a⁻¹ * (x * y₀) * a := by rw [hy₀]; group
      _ = a⁻¹ * (y₀ * x) * a := by rw [hxy]
      _ = t * (a⁻¹ * x * a) := by rw [hy₀]; group
  have hE2 : IsPGroup 2 E := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact hEab.2 x x.2)⟩
  obtain ⟨Q, hQ, hRQ⟩ := h.exists_isSylowOf_le d
  obtain ⟨c, hcC, hc⟩ := exists_conj_le_of_isSylowOf hQ hEaC (hE2.map _)
  have hct : c * t = t * c := mem_centralizer_singleton_iff.1 hcC
  set b₀ := a * c with hb₀
  have hb₀t : b₀⁻¹ * y₀ * b₀ = t := by
    calc b₀⁻¹ * y₀ * b₀ = c⁻¹ * (t * c) := by rw [hb₀, hy₀]; group
      _ = t := by rw [← hct]; group
  set E'' := E.map (MulAut.conj b₀⁻¹).toMonoidHom with hE''
  have hmemE'' : ∀ y, y ∈ E'' ↔ b₀ * y * b₀⁻¹ ∈ E := fun y => by
    rw [hE'', mem_map_conj_iff, inv_inv]
  have hE''Q : E'' ≤ Q := by
    intro y hy
    have h1 := hc (a⁻¹ * (b₀ * y * b₀⁻¹) * a) ⟨_, (hmemE'' y).1 hy, by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩
    rwa [show c⁻¹ * (a⁻¹ * (b₀ * y * b₀⁻¹) * a) * c = y by rw [hb₀]; group] at h1
  obtain ⟨hE''ab, hE''card⟩ := isElemAbelian_map_conj hEab b₀⁻¹
  rw [← hE''] at hE''ab hE''card
  have hE''R : E'' ≤ yamadaR d t := by
    rw [← h.rankThompson_eq d hK hQ.isPGroup hQ.le hRQ]
    refine le_iSup₂_of_le E'' ⟨hE''Q, hE''ab.1, ?_⟩ le_rfl
    refine le_antisymm (SectionRank.pRank_mono one_lt_two hE''Q) ?_
    rw [h.pRank_eq d hK hQ.le hRQ]
    refine SectionRank.le_pRank one_lt_two le_rfl hE''ab ?_
    rw [hE''card, hEcard, hK, ← pow_mul, pow_succ, mul_comm f 3, mul_comm]
  have htE'' : t ∈ E'' := by
    rw [hmemE'']
    rw [show b₀ * t * b₀⁻¹ = y₀ by rw [← hb₀t]; group]
    exact hy₀E
  set K₀ := E'' ⊓ L with hK₀
  have hK₀L : K₀ ≤ L := inf_le_right
  have hE''eq : E'' = K₀ ⊔ zpowers t := by
    apply le_antisymm
    · intro x hx
      have hx2 : x * x = 1 := by rw [← sq]; exact hE''ab.2 x hx
      have hxR := hE''R hx
      rcases h.mem_or_mul_mem_of_mem_sup_kernel (sup_le_sup_right (d.image_le _) _ hxR) hx2 with
        hxL | hxL
      · exact mem_sup_left ⟨hx, hxL⟩
      · exact (h.mem_sup_zpowers_iff hK₀L).2 (Or.inr ⟨mul_mem htE'' hx, hxL⟩)
    · exact sup_le inf_le_left ((zpowers_le).2 htE'')
  have hK₀ab : IsElemAbelian 2 K₀ := by
    have := hE''ab.1
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => hE''ab.2 x (Subgroup.mem_inf.1 hx).1⟩
    have hc : (x : G) * y = y * x := congrArg Subtype.val
      (mul_comm' (⟨x, (Subgroup.mem_inf.1 x.2).1⟩ : E'') ⟨y, (Subgroup.mem_inf.1 y.2).1⟩)
    exact hc
  have hK₀card : Nat.card K₀ = Nat.card K ^ 3 := by
    have h1 := (h.isElemAbelian_sup_zpowers hK₀L hK₀ab).2
    rw [← hE''eq, hE''card, hEcard] at h1
    omega
  have hK₀max : Maximal (fun E₁ : Subgroup G => E₁ ≤ L ∧ CFSG.IsElementaryAbelian 2 E₁) K₀ := by
    refine ⟨⟨hK₀L, isElementaryAbelian_of_isElemAbelian hK₀ab⟩, fun E₁ ⟨hE₁L, hE₁⟩ hK₀E₁ => ?_⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (CFSG.IsElementaryAbelian.isPGroup 2 E₁)
    have hk3 : k ≤ 3 * f := by
      rw [← (d.pRank_S hK hf1).2]
      exact SectionRank.le_pRank one_lt_two hE₁L (isElemAbelian_of_isElementaryAbelian hE₁) hk
    have hle : Nat.card E₁ ≤ Nat.card K₀ := by
      rw [hk, hK₀card, hK, ← pow_mul]
      exact Nat.pow_le_pow_right two_pos (by linarith)
    exact (Subgroup.eq_of_le_of_card_ge hK₀E₁ hle).ge
  set B' := d.leviB.map (MulAut.conj b₀⁻¹).toMonoidHom with hB'
  have hmemB' : ∀ y, y ∈ B' ↔ b₀ * y * b₀⁻¹ ∈ d.leviB := fun y => by
    rw [hB', mem_map_conj_iff, inv_inv]
  have hB'C : B' ≤ centralizer ({t} : Set G) := by
    intro y hy
    rw [mem_centralizer_singleton_iff]
    have h1 := hBy _ ((hmemB' y).1 hy)
    calc y * t = b₀⁻¹ * ((b₀ * y * b₀⁻¹) * y₀) * b₀ := by rw [← hb₀t]; group
      _ = b₀⁻¹ * (y₀ * (b₀ * y * b₀⁻¹)) * b₀ := by rw [h1]
      _ = t * y := by rw [← hb₀t]; group
  have hB'perf : ⁅B', B'⁆ = B' := by rw [hB', ← map_commutator, (d.leviB_perfect hK4).1]
  have hB'L : B' ≤ L := h.perfect_le hB'perf hB'C
  have hB'K₀ : ∀ y ∈ B', ∀ k ∈ K₀, y * k * y⁻¹ ∈ K₀ := by
    intro y hy k hk
    obtain ⟨hk1, hk2⟩ := Subgroup.mem_inf.1 hk
    refine Subgroup.mem_inf.2 ⟨(hmemE'' _).2 ?_,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (hB'L hy) hk2) (Subgroup.inv_mem _ (hB'L hy))⟩
    have h1 := hBE _ ((hmemB' y).1 hy) _ ((hmemE'' k).1 hk1)
    rwa [show b₀ * y * b₀⁻¹ * (b₀ * k * b₀⁻¹) * (b₀ * y * b₀⁻¹)⁻¹ =
      b₀ * (y * k * y⁻¹) * b₀⁻¹ by group] at h1
  obtain ⟨z, hzL, hzX | hzW⟩ := (d.yamada_3_17_1_G hK4).2.2.2 K₀ hK₀max
  ·
    exfalso
    set P := B'.map (MulAut.conj z⁻¹).toMonoidHom with hP
    have hPL : P ≤ L := by
      rintro _ ⟨y, hy, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      exact mul_mem (mul_mem (inv_mem hzL) (hB'L hy)) hzL
    have hPperf : ⁅P, P⁆ = P := by rw [hP, ← map_commutator, hB'perf]
    have hPX : P ≤ normalizer (d.X : Set G) := by
      refine le_normalizer_of_conj_mem fun p hp x hx => ?_
      obtain ⟨y, hy, rfl⟩ := hp
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      have hzx : z * x * z⁻¹ ∈ K₀ := by
        rw [hzX]
        exact ⟨x, hx, rfl⟩
      have h1 := hB'K₀ y hy _ hzx
      rw [hzX, mem_map_conj_iff] at h1
      rwa [show z⁻¹ * (y * (z * x * z⁻¹) * y⁻¹) * z = z⁻¹ * y * z * x * (z⁻¹ * y * z)⁻¹ by
        group] at h1
    have hPbot := d.eq_bot_of_le_normalizer_X hPL hPperf hPX
    rw [hP, Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj z⁻¹).injective, hB',
      Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj b₀⁻¹).injective] at hPbot
    exact (d.leviB_perfect hK4).2 hPbot
  ·
    refine ⟨b₀ * z, mem_normalizer_of_conj_mem fun x hx => ?_, ?_⟩
    · have hzx : z * x * z⁻¹ ∈ E'' := by
        rcases (h.mem_sup_zpowers_iff hWL).1 hx with hxW | hxW
        · have : z * x * z⁻¹ ∈ K₀ := by
            rw [hzW]
            exact ⟨x, hxW, rfl⟩
          exact (Subgroup.mem_inf.1 this).1
        · have h1 : z * (t * x) * z⁻¹ ∈ K₀ := by
            rw [hzW]
            exact ⟨t * x, hxW, rfl⟩
          have hzt : z * t = t * z := mem_centralizer_singleton_iff.1 (h.L_le_centralizer hzL)
          have e : z * x * z⁻¹ = t * (z * (t * x) * z⁻¹) := by
            calc z * x * z⁻¹ = z * (t * (t * x)) * z⁻¹ := by
                  rw [← mul_assoc t t x, h.t_mul_t, one_mul]
              _ = (z * t) * (t * x) * z⁻¹ := by group
              _ = t * (z * (t * x) * z⁻¹) := by rw [hzt]; group
          rw [e]
          exact mul_mem htE'' (Subgroup.mem_inf.1 h1).1
      have h1 := (hmemE'' _).1 hzx
      rwa [show b₀ * (z * x * z⁻¹) * b₀⁻¹ = b₀ * z * x * (b₀ * z)⁻¹ by group] at h1
    · have hzt : z * t = t * z := mem_centralizer_singleton_iff.1 (h.L_le_centralizer hzL)
      calc b₀ * z * t * (b₀ * z)⁻¹ = b₀ * (z * t) * z⁻¹ * b₀⁻¹ := by group
        _ = b₀ * t * b₀⁻¹ := by rw [hzt]; group
        _ = y₀ := by rw [← hb₀t]; group

theorem false_of_normalizer_conj (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hY : ∀ a : G, a * t * a⁻¹ ∈ d.Y ⊔ zpowers t → a * t * a⁻¹ = t) {b : G}
    (hb : b ∈ normalizer ((d.W ⊔ zpowers t : Subgroup G) : Set G))
    (hbt : b * t * b⁻¹ = d.xv ∨ b * t * b⁻¹ = t * d.xv) : False := by
  have hK4 : 4 ≤ Nat.card K := hK ▸ h.four_le
  set E := d.W ⊔ zpowers t with hE
  set H := normalizer (E : Set G) with hH
  have hWL : d.W ≤ L := d.image_le _
  have hYL : d.Y ≤ L := d.image_le _
  have hYW : d.Y ≤ d.W := (d.inclusions).2.2.1
  obtain ⟨hvW, hvY, hv2, hcU, hc1, hc2⟩ := d.xv_xc_spec
  obtain ⟨v₁, v₂, y₂, hv₁W, hv₁Y, hv₂W, hv₂Y, hv₁₂, hy₂Y, hy₂1, hcy₂⟩ := d.exists_xv_mul_xv hK4
  have hcY : d.xc ∈ d.Y := (d.inclusions).1 hcU
  have hEi : ∀ x, x ∈ E ↔ x ∈ d.W ∨ t * x ∈ d.W := fun x => h.mem_sup_zpowers_iff hWL
  have hYi : ∀ x, x ∈ d.Y ⊔ zpowers t ↔ x ∈ d.Y ∨ t * x ∈ d.Y := fun x =>
    h.mem_sup_zpowers_iff hYL
  have htt : ∀ x : G, t * (t * x) = x := fun x => by rw [← mul_assoc, h.t_mul_t, one_mul]
  have hHE : ∀ k ∈ H, ∀ x ∈ E, k * x * k⁻¹ ∈ E := fun k hk x hx =>
    (mem_normalizer_iff.1 hk x).1 hx
  have htE : t ∈ E := mem_sup_right (mem_zpowers t)
  have hWE : ∀ w ∈ d.W, w ∈ E := fun w hw => mem_sup_left hw
  have htWE : ∀ w ∈ d.W, t * w ∈ E := fun w hw => mul_mem htE (hWE w hw)
  have hnY := h.conj_not_mem_Y d hK
  have hLt : ∀ l ∈ L, l * t = t * l := fun l hl =>
    mem_centralizer_singleton_iff.1 (h.L_le_centralizer hl)
  have htW : ∀ w ∈ d.W, t * w ∉ d.W := fun w hw htw => h.t_not_mem_L (hWL (by
    have := mul_mem htw (inv_mem hw)
    rwa [mul_inv_cancel_right] at this))
  have hne : ∀ g : G, g * t * g⁻¹ ≠ 1 := fun g h1 => h.t_ne_one (by
    calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group)
  have hN₀ : ∀ n ∈ L ⊓ normalizer (d.W : Set G), n ∈ H := by
    intro n hn
    obtain ⟨hnL, hnW⟩ := Subgroup.mem_inf.1 hn
    refine mem_normalizer_of_conj_mem fun x hx => ?_
    rcases (hEi x).1 hx with hxW | hxW
    · exact hWE _ ((mem_normalizer_iff.1 hnW x).1 hxW)
    · refine (hEi _).2 (Or.inr ?_)
      have e : t * (n * x * n⁻¹) = n * (t * x) * n⁻¹ := by
        calc t * (n * x * n⁻¹) = (t * n) * x * n⁻¹ := by group
          _ = (n * t) * x * n⁻¹ := by rw [hLt n hnL]
          _ = n * (t * x) * n⁻¹ := by group
      rw [e]
      exact (mem_normalizer_iff.1 hnW _).1 hxW
  have hmove : ∀ w ∈ d.W, w ∉ d.Y → ∀ k ∈ H, ∀ ε : G, ε = 1 ∨ ε = t →
      k * t * k⁻¹ = ε * w → ∀ w' ∈ d.W, w' ∉ d.Y → ∃ k' ∈ H, k' * t * k'⁻¹ = ε * w' := by
    intro w hw hwY k hk ε hε hkw w' hw' hw'Y
    obtain ⟨n, hn, hnw⟩ := d.exists_conj_xv hw hwY
    obtain ⟨n', hn', hnw'⟩ := d.exists_conj_xv hw' hw'Y
    have hεn : ∀ m ∈ L, m * ε = ε * m := fun m hm => by
      rcases hε with rfl | rfl
      · group
      · exact hLt m hm
    refine ⟨n'⁻¹ * n * k, mul_mem (mul_mem (inv_mem (hN₀ n' hn')) (hN₀ n hn)) hk, ?_⟩
    have hnL := (Subgroup.mem_inf.1 hn).1
    have hn'L := (Subgroup.mem_inf.1 hn').1
    calc n'⁻¹ * n * k * t * (n'⁻¹ * n * k)⁻¹ = n'⁻¹ * (n * (ε * w) * n⁻¹) * n' := by
          rw [← hkw]; group
      _ = n'⁻¹ * ((n * ε) * w * n⁻¹) * n' := by group
      _ = n'⁻¹ * (ε * (n * w * n⁻¹)) * n' := by rw [hεn n hnL]; group
      _ = (n'⁻¹ * ε) * (n' * w' * n'⁻¹) * n' := by rw [hnw, hnw']; group
      _ = (ε * n'⁻¹) * (n' * w' * n'⁻¹) * n' := by rw [hεn _ (inv_mem hn'L)]
      _ = ε * w' := by group
  have hcase : ∀ k ∈ H, k * t * k⁻¹ = t ∨ (∃ w ∈ d.W, w ∉ d.Y ∧ k * t * k⁻¹ = t * w) ∨
      (k * t * k⁻¹ ∈ d.W ∧ k * t * k⁻¹ ∉ d.Y) := by
    intro k hk
    rcases (hEi _).1 (hHE k hk t htE) with hW | hW
    · exact Or.inr (Or.inr ⟨hW, hnY k⟩)
    · by_cases hY' : t * (k * t * k⁻¹) ∈ d.Y
      · exact Or.inl (hY k ((hYi _).2 (Or.inr hY')))
      · exact Or.inr (Or.inl ⟨_, hW, hY', (htt _).symm⟩)
  have hP₁full : (∃ k ∈ H, k * t * k⁻¹ = t * d.xv) → ∀ w ∈ d.W, w ∉ d.Y →
      ∃ k ∈ H, k * t * k⁻¹ = t * w := fun ⟨k, hk, hkv⟩ =>
    hmove _ hvW hvY k hk t (Or.inr rfl) hkv
  have hP₂full : (∃ k ∈ H, k * t * k⁻¹ = d.xv) → ∀ w ∈ d.W, w ∉ d.Y →
      ∃ k ∈ H, k * t * k⁻¹ = w := fun ⟨k, hk, hkv⟩ w hw hwY => by
    obtain ⟨k', hk', hk'w⟩ := hmove _ hvW hvY k hk 1 (Or.inl rfl) (by rw [one_mul]; exact hkv)
      w hw hwY
    exact ⟨k', hk', by rw [hk'w, one_mul]⟩
  have hfin : (∀ k ∈ H, k * t * k⁻¹ = t) → False := by
    intro hall
    have hb' := hall b hb
    rcases hbt with h1 | h1
    · rw [h1] at hb'
      exact htW 1 (one_mem _) (by rw [mul_one, ← hb']; exact hvW)
    · rw [h1] at hb'
      have : d.xv = 1 := by
        calc d.xv = t⁻¹ * (t * d.xv) := by group
          _ = 1 := by rw [hb', inv_mul_cancel]
      exact hvY (this ▸ one_mem _)
  by_cases hP₁ : ∃ k ∈ H, k * t * k⁻¹ = t * d.xv <;>
    by_cases hP₂ : ∃ k ∈ H, k * t * k⁻¹ = d.xv
  ·
    refine hfin fun k hk => ?_
    have hout : ∀ z ∈ E, (∀ g : G, g * t * g⁻¹ ≠ z) → k * z * k⁻¹ ∈ d.Y ⊔ zpowers t := by
      intro z hz hzc
      rcases (hEi _).1 (hHE k hk z hz) with hW | hW
      · by_cases hYz : k * z * k⁻¹ ∈ d.Y
        · exact mem_sup_left hYz
        · obtain ⟨k', -, hk'⟩ := hP₂full hP₂ _ hW hYz
          exact absurd (by rw [show (k⁻¹ * k') * t * (k⁻¹ * k')⁻¹ =
            k⁻¹ * (k' * t * k'⁻¹) * k by group, hk']; group) (hzc (k⁻¹ * k'))
      · by_cases hYz : t * (k * z * k⁻¹) ∈ d.Y
        · exact (hYi _).2 (Or.inr hYz)
        · obtain ⟨k', -, hk'⟩ := hP₁full hP₁ _ hW hYz
          rw [htt] at hk'
          exact absurd (by rw [show (k⁻¹ * k') * t * (k⁻¹ * k')⁻¹ =
            k⁻¹ * (k' * t * k'⁻¹) * k by group, hk']; group) (hzc (k⁻¹ * k'))
    have h1 := hout (t * d.xc) (htWE _ (hYW hcY)) fun g hg => hc1 (by
      have := hY g (by rw [hg]; exact (hYi _).2 (Or.inr (by rw [htt]; exact hcY)))
      rw [hg] at this
      calc d.xc = t⁻¹ * (t * d.xc) := by group
        _ = 1 := by rw [this, inv_mul_cancel])
    have h2 := hout d.xc (hWE _ (hYW hcY)) fun g hg => hnY g (hg ▸ hcY)
    refine hY k ?_
    rw [show k * t * k⁻¹ = k * (t * d.xc) * k⁻¹ * (k * d.xc * k⁻¹) by
      rw [show k * (t * d.xc) * k⁻¹ * (k * d.xc * k⁻¹) = k * (t * (d.xc * d.xc)) * k⁻¹ by group,
        hc2, mul_one]]
    exact mul_mem h1 h2
  ·
    have hnW : ∀ k ∈ H, k * t * k⁻¹ ∉ d.W := by
      intro k hk hW
      refine hP₂ ?_
      obtain ⟨k', hk', hk'w⟩ :=
        hmove _ hW (hnY k) k hk 1 (Or.inl rfl) (by rw [one_mul]) _ hvW hvY
      exact ⟨k', hk', by rw [hk'w, one_mul]⟩
    have hprod : ∀ x ∈ E, x ∉ d.W → ∀ x' ∈ E, x' ∉ d.W → x * x' ∈ d.W := by
      intro x hx hxW x' hx' hx'W
      have h1 := ((hEi x).1 hx).resolve_left hxW
      have h2 := ((hEi x').1 hx').resolve_left hx'W
      have e : x * x' = (t * x) * (t * x') := by
        calc x * x' = t * (t * x) * x' := by rw [htt]
          _ = (t * x) * t * x' := by rw [← hLt _ (hWL h1)]
          _ = (t * x) * (t * x') := by group
      rw [e]
      exact mul_mem h1 h2
    have hvt : d.xv * t = t * d.xv := hLt _ (hWL hvW)
    have hHW : ∀ k ∈ H, ∀ w ∈ d.W, k * w * k⁻¹ ∈ d.W := by
      intro k hk w hw
      obtain ⟨k₁, hk₁, k₂, hk₂, hw'⟩ : ∃ k₁ ∈ H, ∃ k₂ ∈ H,
          w = (k₁ * t * k₁⁻¹) * (k₂ * t * k₂⁻¹) := by
        by_cases hwY : w ∈ d.Y
        · obtain ⟨k₁, hk₁, hk₁v⟩ := id hP₁
          have hvwY : d.xv * w ∉ d.Y := fun h1 => hvY (by
            have := mul_mem h1 (inv_mem hwY)
            rwa [mul_inv_cancel_right] at this)
          obtain ⟨k₂, hk₂, hk₂w⟩ := hP₁full hP₁ _ (mul_mem hvW hw) hvwY
          refine ⟨k₁, hk₁, k₂, hk₂, ?_⟩
          rw [hk₁v, hk₂w]
          calc w = t * t * (d.xv * d.xv * w) := by rw [h.t_mul_t, hv2, one_mul, one_mul]
            _ = t * (t * d.xv) * d.xv * w := by group
            _ = t * (d.xv * t) * d.xv * w := by rw [hvt]
            _ = t * d.xv * (t * (d.xv * w)) := by group
        · obtain ⟨k₂, hk₂, hk₂w⟩ := hP₁full hP₁ _ hw hwY
          refine ⟨1, one_mem _, k₂, hk₂, ?_⟩
          rw [hk₂w, inv_one, mul_one, one_mul, htt]
      rw [hw', show k * (k₁ * t * k₁⁻¹ * (k₂ * t * k₂⁻¹)) * k⁻¹ =
        ((k * k₁) * t * (k * k₁)⁻¹) * ((k * k₂) * t * (k * k₂)⁻¹) by group]
      exact hprod _ (hHE _ (mul_mem hk hk₁) t htE) (hnW _ (mul_mem hk hk₁))
        _ (hHE _ (mul_mem hk hk₂) t htE) (hnW _ (mul_mem hk hk₂))
    refine hfin fun k hk => ?_
    have hty : ∀ y ∈ d.Y, y ≠ 1 → k * (t * y) * k⁻¹ ∈ d.Y ⊔ zpowers t := by
      intro y hy hy1
      have hE' := hHE k hk _ (htWE _ (hYW hy))
      have hnotW : k * (t * y) * k⁻¹ ∉ d.W := by
        intro hW
        have h1 := hHW _ (inv_mem hk) _ hW
        rw [show k⁻¹ * (k * (t * y) * k⁻¹) * k⁻¹⁻¹ = t * y by group] at h1
        exact htW y (hYW hy) h1
      have h2 := ((hEi _).1 hE').resolve_left hnotW
      by_cases hY' : t * (k * (t * y) * k⁻¹) ∈ d.Y
      · exact (hYi _).2 (Or.inr hY')
      · exfalso
        obtain ⟨k', -, hk'⟩ := hP₁full hP₁ _ h2 hY'
        rw [htt] at hk'
        have h3 : (k⁻¹ * k') * t * (k⁻¹ * k')⁻¹ = t * y := by
          rw [show (k⁻¹ * k') * t * (k⁻¹ * k')⁻¹ = k⁻¹ * (k' * t * k'⁻¹) * k by group, hk']
          group
        have h4 := hY _ (by rw [h3]; exact (hYi _).2 (Or.inr (by rw [htt]; exact hy)))
        rw [h3] at h4
        exact hy1 (by
          calc y = t⁻¹ * (t * y) := by group
            _ = 1 := by rw [h4, inv_mul_cancel])
    have hYab := d.isElementaryAbelian.2.1
    have hcy : d.xc * y₂ = y₂ * d.xc :=
      congrArg Subtype.val (mul_comm' (⟨d.xc, hcY⟩ : d.Y) ⟨y₂, hy₂Y⟩)
    have hy₂2 : y₂ * y₂ = 1 := by
      rw [← sq]
      exact CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := d.Y) y₂ hy₂Y
    have hct : d.xc * t = t * d.xc := hLt _ (hYL hcY)
    have hyt : y₂ * t = t * y₂ := hLt _ (hYL hy₂Y)
    have e₀ : (t * d.xc) * (t * y₂) * (t * (d.xc * y₂)) = t := by
      calc (t * d.xc) * (t * y₂) * (t * (d.xc * y₂)) =
            t * (d.xc * t) * (y₂ * t) * (d.xc * y₂) := by group
        _ = t * (t * d.xc) * (t * y₂) * (d.xc * y₂) := by rw [hct, hyt]
        _ = t * t * (d.xc * t) * y₂ * (d.xc * y₂) := by group
        _ = t * t * (t * d.xc) * y₂ * (d.xc * y₂) := by rw [hct]
        _ = (t * t) * t * (d.xc * (y₂ * d.xc) * y₂) := by group
        _ = (t * t) * t * (d.xc * (d.xc * y₂) * y₂) := by rw [hcy]
        _ = (t * t) * t * ((d.xc * d.xc) * (y₂ * y₂)) := by group
        _ = t := by rw [h.t_mul_t, hc2, hy₂2, one_mul, one_mul, mul_one]
    have e : k * t * k⁻¹ = (k * (t * d.xc) * k⁻¹) * (k * (t * y₂) * k⁻¹) *
        (k * (t * (d.xc * y₂)) * k⁻¹) := by
      rw [show (k * (t * d.xc) * k⁻¹) * (k * (t * y₂) * k⁻¹) * (k * (t * (d.xc * y₂)) * k⁻¹) =
        k * ((t * d.xc) * (t * y₂) * (t * (d.xc * y₂))) * k⁻¹ by group, e₀]
    refine hY k ?_
    rw [e]
    exact mul_mem (mul_mem (hty _ hcY hc1) (hty _ hy₂Y hy₂1)) (hty _ (mul_mem hcY hy₂Y) hcy₂)
  ·
    obtain ⟨k₀, hk₀, hk₀v⟩ := hP₂
    obtain ⟨k₁, hk₁, hk₁v⟩ := hP₂full ⟨k₀, hk₀, hk₀v⟩ _ hv₁W hv₁Y
    obtain ⟨k₂, hk₂, hk₂v⟩ := hP₂full ⟨k₀, hk₀, hk₀v⟩ _ hv₂W hv₂Y
    have hnot : ∀ k ∈ H, ∀ w ∈ d.W, w ∉ d.Y → k * t * k⁻¹ ≠ t * w := fun k hk w hw hwY hkw =>
      hP₁ (hmove w hw hwY k hk t (Or.inr rfl) hkw _ hvW hvY)
    have hk₁' := mul_mem (inv_mem hk₀) hk₁
    have hk₂' := mul_mem (inv_mem hk₀) hk₂
    have ha : ((k₀⁻¹ * k₁) * t * (k₀⁻¹ * k₁)⁻¹) * ((k₀⁻¹ * k₂) * t * (k₀⁻¹ * k₂)⁻¹) = t := by
      calc ((k₀⁻¹ * k₁) * t * (k₀⁻¹ * k₁)⁻¹) * ((k₀⁻¹ * k₂) * t * (k₀⁻¹ * k₂)⁻¹) =
            k₀⁻¹ * ((k₁ * t * k₁⁻¹) * (k₂ * t * k₂⁻¹)) * k₀ := by group
        _ = k₀⁻¹ * (k₀ * t * k₀⁻¹) * k₀ := by rw [hk₁v, hk₂v, hv₁₂, hk₀v]
        _ = t := by group
    set a₁ := (k₀⁻¹ * k₁) * t * (k₀⁻¹ * k₁)⁻¹ with ha₁
    set a₂ := (k₀⁻¹ * k₂) * t * (k₀⁻¹ * k₂)⁻¹ with ha₂
    have ha₁E := hHE _ hk₁' t htE
    have ha₁2 : a₁ * a₁ = 1 := by
      calc a₁ * a₁ = (k₀⁻¹ * k₁) * (t * t) * (k₀⁻¹ * k₁)⁻¹ := by rw [ha₁]; group
        _ = 1 := by rw [h.t_mul_t, mul_one, mul_inv_cancel]
    have ha₁t : a₁ * t = t * a₁ := by
      have := (h.isElemAbelian_W_sup_zpowers d).1.1
      exact congrArg Subtype.val (mul_comm' (⟨a₁, ha₁E⟩ : E) ⟨t, htE⟩)
    have ha₂' : a₂ = t * a₁ := by
      calc a₂ = (a₁ * a₁) * a₂ := by rw [ha₁2, one_mul]
        _ = a₁ * (a₁ * a₂) := by group
        _ = a₁ * t := by rw [ha]
        _ = t * a₁ := ha₁t
    rcases (hEi a₁).1 ha₁E with hW | hW
    · exact hnot _ hk₂' a₁ hW (hnY _) ha₂'
    · by_cases hY' : t * a₁ ∈ d.Y
      · have h1 : a₁ = t := hY _ ((hYi _).2 (Or.inr hY'))
        refine hne (k₀⁻¹ * k₂) ?_
        rw [← ha₂, ha₂', h1, h.t_mul_t]
      · exact hnot _ hk₁' (t * a₁) hW hY' (htt a₁).symm
  · rcases hbt with h1 | h1
    · exact hP₂ ⟨b, hb, h1⟩
    · exact hP₁ ⟨b, hb, h1⟩

theorem exists_conj_mem_Y_sup (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) :
    ∃ a : G, a * t * a⁻¹ ∈ d.Y ⊔ zpowers t ∧ a * t * a⁻¹ ≠ t := by
  by_contra hcon
  push Not at hcon
  obtain ⟨a, ha⟩ := h.exists_conj_eq_xv d hK hcon
  obtain ⟨b, hb, hbt⟩ := h.exists_normalizer_conj_eq d hK ha
  exact h.false_of_normalizer_conj d hK hcon hb (hbt ▸ ha)

theorem exists_conj_eq_mul_U (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    {u : G} (hu : u ∈ d.U) : ∃ a : G, a * t * a⁻¹ = t * u := by
  by_cases hu1 : u = 1
  · exact ⟨1, by rw [hu1]; group⟩
  obtain ⟨a, haY, hat⟩ := h.exists_conj_mem_Y_sup d hK
  have hYL : d.Y ≤ L := d.image_le _
  rcases (h.mem_sup_zpowers_iff hYL).1 haY with hY | hY
  · exact absurd hY (h.conj_not_mem_Y d hK a)
  set y := t * (a * t * a⁻¹) with hy
  have hy1 : y ≠ 1 := fun h1 => hat (by
    calc a * t * a⁻¹ = t * (t * (a * t * a⁻¹)) := by rw [← mul_assoc, h.t_mul_t, one_mul]
      _ = t := by rw [← hy, h1, mul_one])
  obtain ⟨l, hl, hlU⟩ := d.exists_conj_mem_U_of_mem_Y hY hy1
  have hlU1 : l⁻¹ * y * l ≠ 1 := fun h1 => hy1 (by
    calc y = l * (l⁻¹ * y * l) * l⁻¹ := by group
      _ = 1 := by rw [h1]; group)
  obtain ⟨j, hj, hju⟩ := d.exists_conj_U hlU hlU1 hu hu1
  have hjL := (Subgroup.mem_inf.1 hj).1
  set m := j * l⁻¹ with hm
  have hmL : m ∈ L := mul_mem hjL (inv_mem hl)
  have hmt : m * t = t * m := mem_centralizer_singleton_iff.1 (h.L_le_centralizer hmL)
  refine ⟨m * a, ?_⟩
  have e : a * t * a⁻¹ = t * y := by rw [hy, ← mul_assoc, h.t_mul_t, one_mul]
  calc m * a * t * (m * a)⁻¹ = m * (a * t * a⁻¹) * m⁻¹ := by group
    _ = (m * t) * y * m⁻¹ := by rw [e]; group
    _ = t * (j * (l⁻¹ * y * l) * j⁻¹) := by rw [hmt, hm]; group
    _ = t * u := by rw [hju]

theorem conj_set_normalizer_yamadaR_eq (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) :
    {x | ∃ n ∈ normalizer (yamadaR d t : Set G), n * t * n⁻¹ = x} =
      (fun u => t * u) '' (d.U : Set G) := by
  obtain ⟨-, -, -, hcU, hc1, -⟩ := d.xv_xc_spec
  obtain ⟨a, ha⟩ := h.exists_conj_eq_mul_U d hK hcU
  have hcL : d.xc ∈ L := d.image_le _ hcU
  have htc : ∀ r ∈ yamadaR d t, r * (t * d.xc) = t * d.xc * r := by
    intro r hr
    have hrt : r * t = t * r := mem_centralizer_singleton_iff.1 (h.yamadaR_le_centralizer d hr)
    have hset := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ (S_commute_kernel d t)).2
    have hr' : r ∈ ((yamadaR d t : Subgroup G) : Set G) := hr
    rw [yamadaR, hset] at hr'
    obtain ⟨s, hs, c, hc, rfl⟩ := hr'
    have hc' : c ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hc
    have hsx : s * d.xc = d.xc * s := by
      have h1 := (d.yamada_3_12_centers).1
      have hcZ : d.xc ∈ d.S ⊓ centralizer (d.S : Set G) := by rw [h1]; exact hcU
      exact mem_centralizer_iff.1 (Subgroup.mem_inf.1 hcZ).2 s hs
    have hcx : c * d.xc = d.xc * c := (mem_centralizer_iff.1 (Subgroup.mem_inf.1 hc').1 _ hcL).symm
    beta_reduce at hrt ⊢
    calc s * c * (t * d.xc) = (s * c * t) * d.xc := by group
      _ = t * (s * c) * d.xc := by rw [hrt]
      _ = t * (s * (c * d.xc)) := by group
      _ = t * (s * d.xc * c) := by rw [hcx]; group
      _ = t * (d.xc * s * c) := by rw [hsx]
      _ = t * d.xc * (s * c) := by group
  obtain ⟨n, hn, hnt⟩ := h.exists_normalizer_yamadaR_conj_eq d hK (g := a) (by rw [ha]; exact htc)
  refine h.conj_set_normalizer_yamadaR d hK hn fun h1 => hc1 ?_
  rw [hnt, ha] at h1
  calc d.xc = t⁻¹ * (t * d.xc) := by group
    _ = 1 := by rw [h1, inv_mul_cancel]

theorem centralizer_L_inf (h : Setup G L f t) :
    centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, _, _, _, hK, ⟨d⟩⟩ := h.exists_data
  set T := centralizer (L : Set G) ⊓ centralizer ({t} : Set G) with hT
  obtain ⟨hTcyc, hT2, hTinv, -⟩ := h.kernel
  have hsq : ∀ c ∈ T, c * c ≠ t := by
    intro c hc hct
    obtain ⟨-, -, -, hcU, hc1, -⟩ := d.xv_xc_spec
    have hmem : t * d.xc ∈ (fun u => t * u) '' (d.U : Set G) := ⟨d.xc, hcU, rfl⟩
    rw [← h.conj_set_normalizer_yamadaR_eq d hK] at hmem
    obtain ⟨n, hn, hnt⟩ := hmem
    have hcR : c ∈ yamadaR d t := mem_sup_right hc
    have hcc : ∀ r ∈ yamadaR d t, c * r = r * c := by
      intro r hr
      have hset := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _
        (S_commute_kernel d t)).2
      have hr' : r ∈ ((yamadaR d t : Subgroup G) : Set G) := hr
      rw [yamadaR, hset] at hr'
      obtain ⟨s, hs, c', hc', rfl⟩ := hr'
      beta_reduce
      have hc'' : c' ∈ T := hc'
      rw [← mul_assoc, (S_commute_kernel d t s hs c hc).symm, mul_assoc, h.kernel_comm hc hc'',
        mul_assoc]
    obtain ⟨hnR, hnc⟩ := conj_mem_center_of_mem_normalizer hn hcR hcc
    obtain ⟨u, hu, c', hc', hnuc⟩ := h.exists_mul_of_mem_center_yamadaR d hnR hnc
    have huc : u * c' = c' * u := mem_centralizer_iff.1 (Subgroup.mem_inf.1 hc').1 u
      (d.image_le _ hu)
    have hu2 : u * u = 1 := by
      have := d.isElementaryAbelian.1
      rw [← sq]
      exact CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := d.U) u hu
    have htxT : t * d.xc ∈ T := by
      rw [← hnt, ← hct]
      rw [show n * (c * c) * n⁻¹ = (n * c * n⁻¹) * (n * c * n⁻¹) by group, hnuc]
      rw [show u * c' * (u * c') = u * (c' * u) * c' by group, ← huc,
        show u * (u * c') * c' = (u * u) * (c' * c') by group, hu2, one_mul]
      exact mul_mem hc' hc'
    have hxcT : d.xc ∈ T := by
      have := mul_mem (inv_mem h.t_mem_kernel) htxT
      rwa [inv_mul_cancel_left] at this
    have hxc : d.xc ∈ L ⊓ centralizer (L : Set G) :=
      Subgroup.mem_inf.2 ⟨d.image_le _ hcU, (Subgroup.mem_inf.1 hxcT).1⟩
    rw [h.inf_centralizer_eq_bot, mem_bot] at hxc
    exact hc1 hxc
  have hcard : Nat.card T ≤ 2 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hT2
    by_contra hlt
    push Not at hlt
    have hk2 : 2 ≤ k := by
      by_contra hk2
      push Not at hk2
      interval_cases k <;> simp_all
    obtain ⟨g₀, hg₀⟩ := hTcyc.exists_generator
    have hord : orderOf g₀ = 2 ^ k := by rw [orderOf_eq_card_of_forall_mem_zpowers hg₀, hk]
    have hdvd : 2 ^ (k - 1) ∣ orderOf g₀ := by
      rw [hord]
      exact pow_dvd_pow 2 (Nat.sub_le k 1)
    have ho2 : orderOf (g₀ ^ 2 ^ (k - 1)) = 2 := by
      rw [orderOf_pow_of_dvd (by positivity) hdvd, hord]
      have e : 2 ^ k = 2 ^ (k - 1) * 2 := by rw [← pow_succ]; congr 1; omega
      rw [e, Nat.mul_div_cancel_left 2 (by positivity : 0 < 2 ^ (k - 1))]
    have ht' := hTinv _ (g₀ ^ 2 ^ (k - 1)).2 (by rw [orderOf_coe]; exact ho2)
    have e' : 2 ^ (k - 2) + 2 ^ (k - 2) = 2 ^ (k - 1) := by
      rw [← two_mul, ← pow_succ']; congr 1; omega
    have hc2 : ((g₀ ^ 2 ^ (k - 2) : T) : G) * ((g₀ ^ 2 ^ (k - 2) : T) : G) =
        ((g₀ ^ 2 ^ (k - 1) : T) : G) := by
      rw [← Subgroup.coe_mul, ← pow_add, e']
    exact hsq _ (g₀ ^ 2 ^ (k - 2)).2 (hc2.trans ht')
  have hle : zpowers t ≤ T := (zpowers_le).2 h.t_mem_kernel
  exact (Subgroup.eq_of_le_of_card_ge hle (hcard.trans h.card_zpowers_t.ge)).symm

omit [Finite K] [CharP K 2] in
theorem yamadaR_eq (h : Setup G L f t) (d : G2Data L K) : yamadaR d t = d.S ⊔ zpowers t := by
  rw [yamadaR, h.centralizer_L_inf]

omit [Finite K] in
theorem center_yamadaR (h : Setup G L f t) (d : G2Data L K) :
    yamadaR d t ⊓ centralizer (yamadaR d t : Set G) = d.U ⊔ zpowers t := by
  have hUL : d.U ≤ L := d.image_le _
  apply le_antisymm
  · intro z hz
    obtain ⟨hzR, hzc⟩ := Subgroup.mem_inf.1 hz
    obtain ⟨u, hu, c, hc, rfl⟩ := h.exists_mul_of_mem_center_yamadaR d hzR
      fun r hr => (mem_centralizer_iff.1 hzc r hr).symm
    rw [h.centralizer_L_inf] at hc
    exact mul_mem (mem_sup_left hu) (mem_sup_right hc)
  · have hUS : d.U ≤ d.S := by rw [← (d.yamada_3_12_centers).1]; exact inf_le_left
    have hUC : d.U ≤ centralizer (d.S : Set G) := by
      rw [← (d.yamada_3_12_centers).1]; exact inf_le_right
    refine sup_le (fun u hu => Subgroup.mem_inf.2 ⟨mem_sup_left (hUS hu),
      mem_centralizer_iff.2 fun r hr => ?_⟩) ((zpowers_le).2 (Subgroup.mem_inf.2
        ⟨mem_sup_right h.t_mem_kernel, mem_centralizer_iff.2 fun r hr =>
          mem_centralizer_singleton_iff.1 (h.yamadaR_le_centralizer d hr)⟩))
    have hset := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ (S_commute_kernel d t)).2
    have hr' : r ∈ ((yamadaR d t : Subgroup G) : Set G) := hr
    rw [yamadaR, hset] at hr'
    obtain ⟨s, hs, c, hc, rfl⟩ := hr'
    beta_reduce
    have hc' : c ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hc
    have hsu : s * u = u * s := mem_centralizer_iff.1 (hUC hu) s hs
    have hcu : u * c = c * u := mem_centralizer_iff.1 (Subgroup.mem_inf.1 hc').1 u (hUL hu)
    calc s * c * u = s * (c * u) := by group
      _ = s * (u * c) := by rw [hcu]
      _ = (s * u) * c := by group
      _ = u * (s * c) := by rw [hsu]; group

theorem conj_t_eq_tU (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) :
    {x | ∃ n ∈ normalizer (yamadaR d t : Set G), n * t * n⁻¹ = x} =
        (fun u => t * u) '' (d.U : Set G) ∧
      {x | ∃ n ∈ normalizer ((d.U ⊔ zpowers t : Subgroup G) : Set G), n * t * n⁻¹ = x} =
        (fun u => t * u) '' (d.U : Set G) := by
  refine ⟨h.conj_set_normalizer_yamadaR_eq d hK, ?_⟩
  have hUL : d.U ≤ L := d.image_le _
  have hT := h.centralizer_L_inf
  have hNR : normalizer (yamadaR d t : Set G) ≤
      normalizer ((d.U ⊔ zpowers t : Subgroup G) : Set G) := by
    refine le_normalizer_of_conj_mem fun n hn x hx => ?_
    have hxZ := (h.center_yamadaR d).ge hx
    obtain ⟨hxR, hxc⟩ := Subgroup.mem_inf.1 hxZ
    obtain ⟨hnR, hnc⟩ := conj_mem_center_of_mem_normalizer hn hxR
      fun r hr => (mem_centralizer_iff.1 hxc r hr).symm
    rw [← h.center_yamadaR d]
    exact Subgroup.mem_inf.2 ⟨hnR, mem_centralizer_iff.2 fun r hr => (hnc r hr).symm⟩
  ext x
  constructor
  · rintro ⟨n, hn, rfl⟩
    have htU : t ∈ d.U ⊔ zpowers t := mem_sup_right (mem_zpowers t)
    rcases (h.mem_sup_zpowers_iff hUL).1 ((mem_normalizer_iff.1 hn t).1 htU) with hU | hU
    · exact absurd ((d.inclusions).1 hU) (h.conj_not_mem_Y d hK n)
    · exact ⟨_, hU, by beta_reduce; rw [← mul_assoc, h.t_mul_t, one_mul]⟩
  · intro hx
    rw [← h.conj_set_normalizer_yamadaR_eq d hK] at hx
    obtain ⟨n, hn, rfl⟩ := hx
    exact ⟨n, hNR hn, rfl⟩

end Main

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
