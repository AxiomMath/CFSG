module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma69O
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8H69T

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

namespace OHyp69

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  {β : G} {B : Subgroup G} {S : Subgroup G}
  (h : OHyp69 L z t T E B β S)

include h

theorem X_inv {m : G} (hm : m ∈ normalizer ((S ⊔ E : Subgroup G) : Set G)) {u : G}
    (hu : u ∈ XSet S E z) : m * u * m⁻¹ ∈ XSet S E z := by
  obtain ⟨huU, g, rfl⟩ := hu
  refine ⟨(mem_normalizer_iff.1 hm _).1 huU, m * g, ?_⟩
  group

theorem X_orb {u : G} (hu : u ∈ XSet S E z) :
    ∃ m ∈ normalizer ((S ⊔ E : Subgroup G) : Set G), u = m * z * m⁻¹ := by
  obtain ⟨huU, g, hg⟩ := hu
  obtain ⟨m, hm, hmz⟩ := h.h68 g (hg ▸ huU)
  exact ⟨m, hm, by rw [hmz, hg]⟩

theorem X_reg {u : G} (hu : u ∈ XSet S E z) : cnt (XSet S E z) u = cnt (XSet S E z) z := by
  obtain ⟨m, hm, rfl⟩ := h.X_orb hu
  unfold cnt
  refine ncard_commuting_conj (XSet S E z) m (fun v hv => h.X_inv hm hv) (fun v hv => ?_) z
  exact h.X_inv (inv_mem hm) hv |> fun h' => by simpa using h'

theorem X_props {u : G} (hu : u ∈ XSet S E z) : u ∈ S ⊔ E ∧ u * u = 1 ∧ u ≠ 1 ∧ u ≠ t := by
  obtain ⟨huU, g, rfl⟩ := hu
  refine ⟨huU, ?_, ?_, ?_⟩
  · calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [h.z_sq]; group
  · intro h1
    apply h.z_ne
    calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group
  · exact h.oe.cfg.conj_z_ne_t g

theorem z_mem_X : z ∈ XSet S E z := ⟨mem_sup_left h.zS, 1, by group⟩

theorem zt_mem_X {α : G} (hα : AlphaSpec S z t α) : z * t ∈ XSet S E z := by
  refine ⟨mul_mem (mem_sup_left h.zS) (mem_sup_right h.t_mem_E), α, ?_⟩
  exact (h.alpha_conj_z hα).symm

theorem alpha_not_X {α : G} (hα : AlphaSpec S z t α) : α ∉ XSet S E z := by
  rintro ⟨-, g, hg⟩
  rcases h.h67 g (hg ▸ hα.mem) with h1 | h1
  · exact hα.ne_z (hg.trans h1)
  · exact hα.ne_zt (hg.trans h1)

theorem alpha_t_not_X {α : G} (hα : AlphaSpec S z t α) : α * t ∉ XSet S E z := by
  rintro ⟨-, g, hg⟩
  have hS : α * t ∈ S := mul_mem hα.mem h.t_mem_S
  rcases h.h67 g (hg ▸ hS) with h1 | h1
  · apply hα.ne_zt
    have h2 : α * t = z := hg.trans h1
    calc α = (α * t) * t := by rw [mul_assoc, h.t_sq, mul_one]
      _ = z * t := by rw [h2]
  · apply hα.ne_z
    have h2 : α * t = z * t := hg.trans h1
    exact mul_right_cancel h2

theorem E2_not_X {e : G} (he : e ∈ E2 E t) : e ∉ XSet S E z := by
  rintro ⟨-, g, hg⟩
  obtain ⟨c, hcL, hc⟩ := h.oe.econfig.conj e he.1 he.2.1 he.2.2.1
  apply h.oe.cfg.conj_t_ne_z (g⁻¹ * c)
  calc g⁻¹ * c * t * (g⁻¹ * c)⁻¹ = g⁻¹ * (c * t * c⁻¹) * g := by group
    _ = g⁻¹ * e * g := by rw [← hc]
    _ = z := by rw [hg]; group

theorem ZE_sub_X : blk z (E2 E t) ⊆ XSet S E z := by
  obtain ⟨e₀, he₀E, he₀2, he₀1, he₀t, g, hg⟩ := h.fus
  have he₀' : e₀ ∈ E2 E t := ⟨he₀E, he₀2, he₀1, he₀t⟩
  rintro u ⟨e, he, rfl⟩
  obtain ⟨w, hw, hwe⟩ := h.W_orbit_two he₀E he₀2 he₀1 he₀t he.1 he.2.1 he.2.2.1 he.2.2.2
  refine ⟨mul_mem (mem_sup_left h.zS) (mem_sup_right he.1), w * g, ?_⟩
  have hwz : w * z = z * w := (h.oe.cfg.z_comm_of_mem_A hw.1)
  show z * e = _
  calc z * e = z * (w * e₀ * w⁻¹) := by rw [hwe]
    _ = w * (z * e₀) * w⁻¹ := by
      calc z * (w * e₀ * w⁻¹) = (z * w) * e₀ * w⁻¹ := by group
        _ = (w * z) * e₀ * w⁻¹ := by rw [hwz]
        _ = w * (z * e₀) * w⁻¹ := by group
    _ = w * (g * z * g⁻¹) * w⁻¹ := by rw [hg]
    _ = w * g * z * (w * g)⁻¹ := by group


theorem disj_Zb_ZE : Disjoint (blk z {1, t}) (blk z (E2 E t)) := by
  rw [Set.disjoint_iff_inter_eq_empty, h.blk_inter]
  have : ({1, t} : Set G) ∩ E2 E t = ∅ := by
    ext e
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro he he'
    rcases he with rfl | rfl
    · exact he'.2.2.1 rfl
    · exact he'.2.2.2 rfl
  rw [this]
  ext u
  simp [blk]

theorem disj_z_a {α : G} (hα : AlphaSpec S z t α) {C₁ C₂ : Set G} (h1 : C₁ ⊆ E) (h2 : C₂ ⊆ E) :
    Disjoint (blk z C₁) (blk α C₂) := by
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right h.z_sq
  refine h.blk_disjoint h.zS hα.mem ?_ ?_ h1 h2
  · rw [hzi]
    intro hh
    exact hα.ne_z (by
      calc α = z⁻¹ * (z * α) := by group
        _ = z := by rw [hh, hzi]; group)
  · rw [hzi]
    intro hh
    exact hα.ne_zt (by
      calc α = z⁻¹ * (z * α) := by group
        _ = z * t := by rw [hh, hzi])

theorem disj_z_r {α : G} (hα : AlphaSpec S z t α) {C₁ C₂ : Set G} (h1 : C₁ ⊆ E) (h2 : C₂ ⊆ E) :
    Disjoint (blk z C₁) (blk (α * z) C₂) := by
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right h.z_sq
  have hαt : α * t = t * α := h.t_comm_S α hα.mem
  have hcalc : z⁻¹ * (α * z) = t * α := by
    rw [hzi]
    calc z * (α * z) = (z * α) * z := by group
      _ = (t * (α * z)) * z := by rw [h.z_alpha hα]
      _ = t * (α * (z * z)) := by group
      _ = t * α := by rw [h.z_sq, mul_one]
  refine h.blk_disjoint h.zS (h.alpha_z_mem hα) ?_ ?_ h1 h2
  · rw [hcalc]
    intro hh
    apply hα.ne_t
    calc α = t * (t * α) := by rw [← mul_assoc, h.t_sq, one_mul]
      _ = t * 1 := by rw [hh]
      _ = t := mul_one t
  · rw [hcalc]
    intro hh
    apply hα.ne_one
    exact mul_left_cancel (hh.trans (mul_one t).symm)

theorem disj_a_r {α : G} (hα : AlphaSpec S z t α) {C₁ C₂ : Set G} (h1 : C₁ ⊆ E) (h2 : C₂ ⊆ E) :
    Disjoint (blk α C₁) (blk (α * z) C₂) := by
  have hαi : α⁻¹ = α := inv_eq_of_mul_eq_one_right hα.sq
  have hcalc : α⁻¹ * (α * z) = z := by rw [hαi]; calc α * (α * z) = (α * α) * z := by group
    _ = z := by rw [hα.sq, one_mul]
  refine h.blk_disjoint hα.mem (h.alpha_z_mem hα) ?_ ?_ h1 h2
  · rw [hcalc]; exact h.z_ne
  · rw [hcalc]; exact h.z_ne_t

theorem blk_Zb_sub_X {α : G} (hα : AlphaSpec S z t α) : blk z {1, t} ⊆ XSet S E z := by
  rintro u ⟨e, he, rfl⟩
  rcases he with he | he
  · rw [he]; simpa using h.z_mem_X
  · rw [he]; exact h.zt_mem_X hα

theorem X_decomp {α : G} (hα : AlphaSpec S z t α) :
    XSet S E z = ((blk z {1, t} ∪ blk z (E2 E t)) ∪ (XSet S E z ∩ blk α (E2 E t))) ∪
      (XSet S E z ∩ blk (α * z) (E4 E t)) := by
  ext u
  constructor
  · intro hu
    obtain ⟨huU, hu2, hu1, hut⟩ := h.X_props hu
    rcases h.classify hα huU hu2 hu1 hut with h1 | h1 | h1 | h1 | h1 | h1
    · exact Or.inl (Or.inl (Or.inl h1))
    · exact Or.inl (Or.inl (Or.inr h1))
    · exfalso
      obtain ⟨e, he, rfl⟩ := h1
      change α * e ∈ XSet S E z at hu
      rcases he with he | he
      · rw [he, mul_one] at hu; exact h.alpha_not_X hα hu
      · rw [he] at hu; exact h.alpha_t_not_X hα hu
    · exact Or.inl (Or.inr ⟨hu, h1⟩)
    · exact absurd hu (h.E2_not_X h1)
    · exact Or.inr ⟨hu, h1⟩
  · rintro (((h1 | h1) | ⟨h1, -⟩) | ⟨h1, -⟩)
    · exact h.blk_Zb_sub_X hα h1
    · exact h.ZE_sub_X h1
    · exact h1
    · exact h1


theorem X_eq {α : G} (hα : AlphaSpec S z t α) :
    XSet S E z = (blk z {1, t} ∪ blk z (E2 E t)) ∪ blk (α * z) (E4 E t) := by
  have hinv : ∀ m ∈ normalizer ((S ⊔ E : Subgroup G) : Set G), ∀ u ∈ XSet S E z,
      m * u * m⁻¹ ∈ XSet S E z := fun m hm u hu => h.X_inv hm hu
  have hdAE := h.dich_blk hα.mem (C := E2 E t) (Or.inl rfl) hinv
  have hdAZ := h.dich_blk (h.alpha_z_mem hα) (C := E4 E t) (Or.inr rfl) hinv
  have hdec := h.X_decomp hα
  have hP : XSet S E z ∩ blk α (E2 E t) = blk α (E2 E t) ∨
      XSet S E z ∩ blk α (E2 E t) = ∅ := by
    rcases hdAE with hs | hd
    · exact Or.inl (Set.inter_eq_right.2 hs)
    · exact Or.inr (Set.disjoint_iff_inter_eq_empty.1 hd.symm)
  have hR : XSet S E z ∩ blk (α * z) (E4 E t) = blk (α * z) (E4 E t) ∨
      XSet S E z ∩ blk (α * z) (E4 E t) = ∅ := by
    rcases hdAZ with hs | hd
    · exact Or.inl (Set.inter_eq_right.2 hs)
    · exact Or.inr (Set.disjoint_iff_inter_eq_empty.1 hd.symm)
  have hd1 := h.disj_Zb_ZE
  have hZbAE := h.disj_z_a hα h.E0_sub h.E2_sub
  have hZEAE := h.disj_z_a hα h.E2_sub h.E2_sub
  have hZbAZ := h.disj_z_r hα h.E0_sub h.E4_sub
  have hZEAZ := h.disj_z_r hα h.E2_sub h.E4_sub
  have hAEAZ := h.disj_a_r hα h.E2_sub h.E4_sub
  have hd2 : Disjoint (blk z {1, t} ∪ blk z (E2 E t)) (XSet S E z ∩ blk α (E2 E t)) :=
    Disjoint.union_left (hZbAE.mono_right Set.inter_subset_right)
      (hZEAE.mono_right Set.inter_subset_right)
  have hd3 : Disjoint ((blk z {1, t} ∪ blk z (E2 E t)) ∪ (XSet S E z ∩ blk α (E2 E t)))
      (XSet S E z ∩ blk (α * z) (E4 E t)) :=
    Disjoint.union_left (Disjoint.union_left (hZbAZ.mono_right Set.inter_subset_right)
      (hZEAZ.mono_right Set.inter_subset_right))
      (hAEAZ.mono Set.inter_subset_right Set.inter_subset_right)
  have hcntX : ∀ u, cnt (XSet S E z) u = cnt (blk z {1, t}) u + cnt (blk z (E2 E t)) u +
      cnt (XSet S E z ∩ blk α (E2 E t)) u + cnt (XSet S E z ∩ blk (α * z) (E4 E t)) u := by
    intro u
    conv_lhs => rw [hdec]
    rw [h.cnt_union hd3, h.cnt_union hd2, h.cnt_union hd1]
  obtain ⟨e, heE, he2, he1, het, -⟩ := h.fus
  have he : e ∈ E2 E t := ⟨heE, he2, he1, het⟩
  have hzeX : z * e ∈ XSet S E z := h.ZE_sub_X ⟨e, he, rfl⟩
  have h12 : cnt (XSet S E z) z = 12 := by
    rw [hcntX z, h.T1 hα, h.T2 hα]
    have h3 : cnt (XSet S E z ∩ blk α (E2 E t)) z = 0 := by
      rcases hP with hP | hP <;> rw [hP]
      · exact h.T3 hα
      · exact h.cnt_empty z
    have h4 : cnt (XSet S E z ∩ blk (α * z) (E4 E t)) z = 0 := by
      rcases hR with hR | hR <;> rw [hR]
      · exact h.T4 hα
      · exact h.cnt_empty z
    omega
  have hze : cnt (XSet S E z) (z * e) = 12 := (h.X_reg hzeX).trans h12
  rw [hcntX (z * e), h.T5 hα he, h.T6 hα he] at hze
  rcases hP with hP | hP <;> rcases hR with hR | hR
  · exfalso
    rw [hP, hR, h.T7 hα he, h.T8 hα he] at hze
    omega
  · exfalso
    have hαeX : α * e ∈ XSet S E z := by
      have : α * e ∈ XSet S E z ∩ blk α (E2 E t) := by
        rw [hP]; exact ⟨e, he, rfl⟩
      exact this.1
    have h12' : cnt (XSet S E z) (α * e) = 12 := (h.X_reg hαeX).trans h12
    rw [hcntX (α * e), h.T9 hα he, h.T10 hα he, hP, hR, h.T11 hα he, h.cnt_empty] at h12'
    omega
  · rw [hdec, hP, hR]
    simp
  · exfalso
    rw [hP, hR, h.cnt_empty] at hze
    omega


@[expose] def XiSet {G : Type*} [Group G] (S E : Subgroup G) (α : G) : Set G :=
  {u | ∃ m ∈ normalizer ((S ⊔ E : Subgroup G) : Set G), u = m * α * m⁻¹}

theorem Xi_inv {α m : G} (hm : m ∈ normalizer ((S ⊔ E : Subgroup G) : Set G)) {u : G}
    (hu : u ∈ XiSet S E α) : m * u * m⁻¹ ∈ XiSet S E α := by
  obtain ⟨m', hm', rfl⟩ := hu
  exact ⟨m * m', mul_mem hm hm', by group⟩

theorem Xi_reg {α : G} {u : G} (hu : u ∈ XiSet S E α) :
    cnt (XiSet S E α) u = cnt (XiSet S E α) α := by
  obtain ⟨m, hm, rfl⟩ := hu
  unfold cnt
  refine ncard_commuting_conj (XiSet S E α) m (fun v hv => h.Xi_inv hm hv) (fun v hv => ?_) α
  exact h.Xi_inv (inv_mem hm) hv |> fun h' => by simpa using h'

theorem Xi_disj_X {α : G} (hα : AlphaSpec S z t α) {u : G} (hu : u ∈ XiSet S E α) :
    u ∉ XSet S E z := by
  intro hX
  obtain ⟨m, hm, rfl⟩ := hu
  have := h.X_inv (inv_mem hm) hX
  apply h.alpha_not_X hα
  have e : m⁻¹ * (m * α * m⁻¹) * m⁻¹⁻¹ = α := by group
  rwa [e] at this

theorem alpha_mem_Xi {α : G} (hα : AlphaSpec S z t α) : α ∈ XiSet S E α :=
  ⟨1, one_mem _, by group⟩

theorem Ab_sub_Xi {α : G} (hα : AlphaSpec S z t α) : blk α {1, t} ⊆ XiSet S E α := by
  rintro u ⟨e, he, rfl⟩
  rcases he with he | he
  · rw [he]; simpa using h.alpha_mem_Xi hα
  · rw [he]
    exact ⟨z, h.z_mem_M, (h.z_conj_alpha hα).symm⟩

theorem disj_same {s : G} {C₁ C₂ : Set G} (hC : C₁ ∩ C₂ = ∅) : Disjoint (blk s C₁) (blk s C₂) := by
  rw [Set.disjoint_iff_inter_eq_empty, h.blk_inter, hC]
  ext u
  simp [blk]

theorem disj_a_one {α : G} (hα : AlphaSpec S z t α) {C₁ C₂ : Set G} (h1 : C₁ ⊆ E)
    (h2 : C₂ ⊆ E) : Disjoint (blk α C₁) (blk 1 C₂) := by
  have hαi : α⁻¹ = α := inv_eq_of_mul_eq_one_right hα.sq
  refine h.blk_disjoint hα.mem (one_mem _) ?_ ?_ h1 h2
  · rw [hαi, mul_one]; exact hα.ne_one
  · rw [hαi, mul_one]; exact hα.ne_t

theorem X_card {α : G} (hα : AlphaSpec S z t α) : Set.ncard (XSet S E z) = 32 := by
  rw [h.X_eq hα]
  have hd : Disjoint (blk z {1, t} ∪ blk z (E2 E t)) (blk (α * z) (E4 E t)) :=
    Disjoint.union_left (h.disj_z_r hα h.E0_sub h.E4_sub) (h.disj_z_r hα h.E2_sub h.E4_sub)
  rw [Set.ncard_union_eq hd (Set.toFinite _) (Set.toFinite _),
    Set.ncard_union_eq h.disj_Zb_ZE (Set.toFinite _) (Set.toFinite _)]
  have h1 : Set.ncard (blk z ({1, t} : Set G)) = 2 := by
    unfold blk; rw [ncard_image_mul_left]; exact h.ncard_E0
  have h2 : Set.ncard (blk z (E2 E t)) = 10 := by
    unfold blk; rw [ncard_image_mul_left]; exact h.ef.card_two
  have h3 : Set.ncard (blk (α * z) (E4 E t)) = 20 := by
    unfold blk; rw [ncard_image_mul_left]; exact h.ef.card_four
  rw [h1, h2, h3]

theorem orbit_eq_X : {u : G | ∃ m ∈ normalizer ((S ⊔ E : Subgroup G) : Set G),
    u = m * z * m⁻¹} = XSet S E z := by
  ext u
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨(mem_normalizer_iff.1 hm z).1 (mem_sup_left h.zS), m, rfl⟩
  · intro hu
    exact h.X_orb hu

theorem conj_t_of_M {m : G} (hm : m ∈ normalizer ((S ⊔ E : Subgroup G) : Set G)) :
    m * t * m⁻¹ = t := by
  have hc : ∀ u ∈ S ⊔ E, (m * t * m⁻¹) * u = u * (m * t * m⁻¹) := by
    intro u hu
    have hu' : m⁻¹ * u * m ∈ S ⊔ E := by
      have := (mem_normalizer_iff.1 (inv_mem hm) u).1 hu
      simpa using this
    obtain ⟨e, he, -⟩ := (⟨1, one_mem E, rfl⟩ : ∃ e ∈ E, (1 : G) = 1)
    have htu : t * (m⁻¹ * u * m) = (m⁻¹ * u * m) * t := by
      obtain ⟨s, hs, e, he, hse⟩ := exists_mul_of_mem_sup_of_le_centralizer h.E_le_cent_S hu'
      rw [hse]
      have h1 : t * s = s * t := (h.t_comm_S s hs).symm
      have h2 : t * e = e * t := (h.t_comm_E e he).symm
      calc t * (s * e) = (t * s) * e := by group
        _ = (s * t) * e := by rw [h1]
        _ = s * (t * e) := by group
        _ = s * (e * t) := by rw [h2]
        _ = (s * e) * t := by group
    calc (m * t * m⁻¹) * u = m * (t * (m⁻¹ * u * m)) * m⁻¹ := by group
      _ = m * ((m⁻¹ * u * m) * t) * m⁻¹ := by rw [htu]
      _ = u * (m * t * m⁻¹) := by group
  rcases h.cent_U hc with h1 | h1
  · exfalso
    apply h.t_ne
    calc t = m⁻¹ * (m * t * m⁻¹) * m := by group
      _ = 1 := by rw [h1]; group
  · exact h1

theorem Xi_props {α : G} (hα : AlphaSpec S z t α) {u : G} (hu : u ∈ XiSet S E α) :
    u ∈ S ⊔ E ∧ u * u = 1 ∧ u ≠ 1 ∧ u ≠ t := by
  obtain ⟨m, hm, rfl⟩ := hu
  refine ⟨(mem_normalizer_iff.1 hm α).1 (mem_sup_left hα.mem), ?_, ?_, ?_⟩
  · calc m * α * m⁻¹ * (m * α * m⁻¹) = m * (α * α) * m⁻¹ := by group
      _ = 1 := by rw [hα.sq]; group
  · intro h1
    apply hα.ne_one
    calc α = m⁻¹ * (m * α * m⁻¹) * m := by group
      _ = 1 := by rw [h1]; group
  · intro h1
    apply hα.ne_t
    have h2 := h.conj_t_of_M (inv_mem hm)
    calc α = m⁻¹ * (m * α * m⁻¹) * m := by group
      _ = m⁻¹ * t * m := by rw [h1]
      _ = t := by simpa using h2

theorem Xi_decomp {α : G} (hα : AlphaSpec S z t α) :
    XiSet S E α = (blk α {1, t} ∪ (XiSet S E α ∩ blk 1 (E2 E t))) ∪
      (XiSet S E α ∩ blk α (E2 E t)) := by
  have hXeq := h.X_eq hα
  ext u
  constructor
  · intro hu
    obtain ⟨huU, hu2, hu1, hut⟩ := h.Xi_props hα hu
    have hnX := h.Xi_disj_X hα hu
    rw [hXeq] at hnX
    rcases h.classify hα huU hu2 hu1 hut with h1 | h1 | h1 | h1 | h1 | h1
    · exact absurd (Or.inl (Or.inl h1)) hnX
    · exact absurd (Or.inl (Or.inr h1)) hnX
    · exact Or.inl (Or.inl h1)
    · exact Or.inr ⟨hu, h1⟩
    · exact Or.inl (Or.inr ⟨hu, by rw [h.blk_one]; exact h1⟩)
    · exact absurd (Or.inr h1) hnX
  · rintro ((h1 | ⟨h1, -⟩) | ⟨h1, -⟩)
    · exact h.Ab_sub_Xi hα h1
    · exact h1
    · exact h1

theorem alpha_orbit {α : G} (hα : AlphaSpec S z t α) {m : G}
    (hm : m ∈ normalizer ((S ⊔ E : Subgroup G) : Set G)) :
    m * α * m⁻¹ = α ∨ m * α * m⁻¹ = α * t := by
  have hinv : ∀ m ∈ normalizer ((S ⊔ E : Subgroup G) : Set G), ∀ u ∈ XiSet S E α,
      m * u * m⁻¹ ∈ XiSet S E α := fun m hm u hu => h.Xi_inv hm hu
  have hdEE := h.dich_blk (one_mem S) (C := E2 E t) (Or.inl rfl) hinv
  have hdAE := h.dich_blk hα.mem (C := E2 E t) (Or.inl rfl) hinv
  have hdec := h.Xi_decomp hα
  have hP : XiSet S E α ∩ blk α (E2 E t) = blk α (E2 E t) ∨
      XiSet S E α ∩ blk α (E2 E t) = ∅ := by
    rcases hdAE with hs | hd
    · exact Or.inl (Set.inter_eq_right.2 hs)
    · exact Or.inr (Set.disjoint_iff_inter_eq_empty.1 hd.symm)
  have hR : XiSet S E α ∩ blk 1 (E2 E t) = blk 1 (E2 E t) ∨
      XiSet S E α ∩ blk 1 (E2 E t) = ∅ := by
    rcases hdEE with hs | hd
    · exact Or.inl (Set.inter_eq_right.2 hs)
    · exact Or.inr (Set.disjoint_iff_inter_eq_empty.1 hd.symm)
  have hE0E2 : ({1, t} : Set G) ∩ E2 E t = ∅ := by
    ext e
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro he he'
    rcases he with rfl | rfl
    · exact he'.2.2.1 rfl
    · exact he'.2.2.2 rfl
  have hAbEE := h.disj_a_one hα h.E0_sub h.E2_sub
  have hAbAE : Disjoint (blk α {1, t}) (blk α (E2 E t)) := h.disj_same hE0E2
  have hEEAE : Disjoint (blk 1 (E2 E t)) (blk α (E2 E t)) :=
    (h.disj_a_one hα h.E2_sub h.E2_sub).symm
  have hd2 : Disjoint (blk α {1, t}) (XiSet S E α ∩ blk 1 (E2 E t)) :=
    hAbEE.mono_right Set.inter_subset_right
  have hd3 : Disjoint ((blk α {1, t}) ∪ (XiSet S E α ∩ blk 1 (E2 E t)))
      (XiSet S E α ∩ blk α (E2 E t)) :=
    Disjoint.union_left (hAbAE.mono_right Set.inter_subset_right)
      (hEEAE.mono Set.inter_subset_right Set.inter_subset_right)
  have hcntX : ∀ u, cnt (XiSet S E α) u = cnt (blk α {1, t}) u +
      cnt (XiSet S E α ∩ blk 1 (E2 E t)) u + cnt (XiSet S E α ∩ blk α (E2 E t)) u := by
    intro u
    conv_lhs => rw [hdec]
    rw [h.cnt_union hd3, h.cnt_union hd2]
  obtain ⟨e, heE, he2, he1, het, -⟩ := h.fus
  have he : e ∈ E2 E t := ⟨heE, he2, he1, het⟩
  have heEE : e ∈ blk 1 (E2 E t) := ⟨e, he, one_mul e⟩
  have haeAE : α * e ∈ blk α (E2 E t) := ⟨e, he, rfl⟩
  rcases hP with hP | hP <;> rcases hR with hR | hR
  · exfalso
    have heΞ : e ∈ XiSet S E α := by
      have : e ∈ XiSet S E α ∩ blk 1 (E2 E t) := by rw [hR]; exact heEE
      exact this.1
    have h1 := h.Xi_reg heΞ
    rw [hcntX e, hcntX α, hP, hR, h.T13 hα, h.T14 hα, h.T15 hα, h.T16 hα he, h.T17 hα he,
      h.T18 hα he] at h1
    omega
  · exfalso
    have heΞ : α * e ∈ XiSet S E α := by
      have : α * e ∈ XiSet S E α ∩ blk α (E2 E t) := by rw [hP]; exact haeAE
      exact this.1
    have h1 := h.Xi_reg heΞ
    rw [hcntX (α * e), hcntX α, hP, hR, h.T13 hα, h.T15 hα, h.T19 hα he, h.T11 hα he,
      h.cnt_empty] at h1
    omega
  · exfalso
    have heΞ : e ∈ XiSet S E α := by
      have : e ∈ XiSet S E α ∩ blk 1 (E2 E t) := by rw [hR]; exact heEE
      exact this.1
    have h1 := h.Xi_reg heΞ
    rw [hcntX e, hcntX α, hP, hR, h.T13 hα, h.T14 hα, h.T16 hα he, h.T17 hα he,
      h.cnt_empty] at h1
    omega
  · have hmΞ : m * α * m⁻¹ ∈ XiSet S E α := ⟨m, hm, rfl⟩
    rw [hdec, hP, hR] at hmΞ
    simp only [Set.union_empty] at hmΞ
    obtain ⟨e', he', hee'⟩ := hmΞ
    rcases he' with rfl | rfl
    · left; simpa using hee'.symm
    · right; exact hee'.symm

end OHyp69

end CFSG.EvenSporadicStandard.Fin76b
