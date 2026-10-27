module

public import CFSG.LocalAnalysis.EvenSporadicStandard.SolomonRed.Engine
public import CFSG.LocalAnalysis.EvenSporadicStandard.SolomonRed.Setting

public section

namespace CFSG.EvenSporadicStandard.SolomonRed

open Subgroup CFSG CFSG.LocalCores

variable {K : Type*} [Group K] [Finite K] {z : K} {B : Subgroup K}

omit [Finite K] in
theorem swap_fixed (hz : z * z = 1) {L₁ L₂ : Subgroup K}
    (hcom : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    (hL₂ : L₂ = L₁.map (MulAut.conj z).toMonoidHom) {a : K} (ha : a ∈ L₁) :
    z * (a * (z * a * z⁻¹)) = (a * (z * a * z⁻¹)) * z := by
  have hmem : z * a * z⁻¹ ∈ L₂ := by
    rw [hL₂]
    exact ⟨a, ha, rfl⟩
  have h1 := conj_conj_of_mul_self_eq_one hz a
  have h2 : a * (z * a * z⁻¹) = (z * a * z⁻¹) * a := hcom a ha _ hmem
  apply conj_eq_self_iff.1
  calc z * (a * (z * a * z⁻¹)) * z⁻¹ = (z * a * z⁻¹) * (z * (z * a * z⁻¹) * z⁻¹) := by group
    _ = (z * a * z⁻¹) * a := by rw [h1]
    _ = a * (z * a * z⁻¹) := h2.symm

omit [Finite K] in
theorem swap_ne_one {L₁ L₂ : Subgroup K} (hdisj : L₁ ⊓ L₂ = ⊥)
    (hL₂ : L₂ = L₁.map (MulAut.conj z).toMonoidHom) {a : K} (ha : a ∈ L₁) (ha1 : a ≠ 1) :
    a * (z * a * z⁻¹) ≠ 1 := by
  intro h
  apply ha1
  have hmem : z * a * z⁻¹ ∈ L₂ := by
    rw [hL₂]
    exact ⟨a, ha, rfl⟩
  have : a ∈ L₁ ⊓ L₂ := by
    refine ⟨ha, ?_⟩
    have : a = (z * a * z⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [this]
    exact L₂.inv_mem hmem
  rw [hdisj, mem_bot] at this
  exact this

omit [Finite K] in
theorem swap_commute {L₁ L₂ : Subgroup K} (hdisj : L₁ ⊓ L₂ = ⊥)
    (hcom : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    (hL₂ : L₂ = L₁.map (MulAut.conj z).toMonoidHom) {a b : K} (ha : a ∈ L₁) (hb : b ∈ L₁)
    (h : (a * (z * a * z⁻¹)) * (b * (z * b * z⁻¹)) = (b * (z * b * z⁻¹)) * (a * (z * a * z⁻¹))) :
    a * b = b * a := by
  have hXa : z * a * z⁻¹ ∈ L₂ := by rw [hL₂]; exact ⟨a, ha, rfl⟩
  have hXb : z * b * z⁻¹ ∈ L₂ := by rw [hL₂]; exact ⟨b, hb, rfl⟩
  have hbX : b * (z * a * z⁻¹) = (z * a * z⁻¹) * b := hcom b hb _ hXa
  have haY : a * (z * b * z⁻¹) = (z * b * z⁻¹) * a := hcom a ha _ hXb
  have e1 : (a * (z * a * z⁻¹)) * (b * (z * b * z⁻¹)) =
      (a * b) * ((z * a * z⁻¹) * (z * b * z⁻¹)) := by
    calc (a * (z * a * z⁻¹)) * (b * (z * b * z⁻¹)) = a * ((z * a * z⁻¹) * b) * (z * b * z⁻¹) := by
          group
      _ = a * (b * (z * a * z⁻¹)) * (z * b * z⁻¹) := by rw [hbX]
      _ = (a * b) * ((z * a * z⁻¹) * (z * b * z⁻¹)) := by group
  have e2 : (b * (z * b * z⁻¹)) * (a * (z * a * z⁻¹)) =
      (b * a) * ((z * b * z⁻¹) * (z * a * z⁻¹)) := by
    calc (b * (z * b * z⁻¹)) * (a * (z * a * z⁻¹)) = b * ((z * b * z⁻¹) * a) * (z * a * z⁻¹) := by
          group
      _ = b * (a * (z * b * z⁻¹)) * (z * a * z⁻¹) := by rw [haY]
      _ = (b * a) * ((z * b * z⁻¹) * (z * a * z⁻¹)) := by group
  rw [e1, e2] at h
  have h3 : (b * a)⁻¹ * (a * b) =
      ((z * b * z⁻¹) * (z * a * z⁻¹)) * ((z * a * z⁻¹) * (z * b * z⁻¹))⁻¹ := by
    calc (b * a)⁻¹ * (a * b) = (b * a)⁻¹ * ((a * b) * ((z * a * z⁻¹) * (z * b * z⁻¹))) *
          ((z * a * z⁻¹) * (z * b * z⁻¹))⁻¹ := by group
      _ = ((z * b * z⁻¹) * (z * a * z⁻¹)) * ((z * a * z⁻¹) * (z * b * z⁻¹))⁻¹ := by
          rw [h]; group
  have h4 : (b * a)⁻¹ * (a * b) ∈ L₁ ⊓ L₂ := by
    refine ⟨L₁.mul_mem (L₁.inv_mem (L₁.mul_mem hb ha)) (L₁.mul_mem ha hb), ?_⟩
    rw [h3]
    exact L₂.mul_mem (L₂.mul_mem hXb hXa) (L₂.inv_mem (L₂.mul_mem hXa hXb))
  rw [hdisj, mem_bot] at h4
  exact (inv_mul_eq_one.1 h4).symm

omit [Finite K] in
theorem z_not_mem_layer {L₁ L₂ : Subgroup K} [Finite K] (hL₁ : IsComponent L₁)
    (hL₂ : L₂ = L₁.map (MulAut.conj z).toMonoidHom) (hne : L₂ ≠ L₁) : z ∉ layer K := by
  intro hz
  have hn : z ∈ normalizer (L₁ : Set K) := layer_le_normalizer hL₁ hz
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hn
  exact hne (hL₂.trans hn)

theorem rest_eq_bot (h : Setting K z B) {L₁ : Subgroup K} (hL₁ : IsComponent L₁) :
    Rest K L₁ (L₁.map (MulAut.conj z).toMonoidHom) = ⊥ := by
  have hF := h.fitting_eq_bot
  have hz := h.z_sq
  obtain ⟨L₂, hL₂def⟩ : ∃ L₂ : Subgroup K, L₂ = L₁.map (MulAut.conj z).toMonoidHom := ⟨_, rfl⟩
  rw [← hL₂def]
  have hL₂ : IsComponent L₂ := by rw [hL₂def]; exact isComponent_conj hL₁ z
  obtain ⟨N, hNdef⟩ : ∃ N : Subgroup K, N = L₁ ⊔ L₂ := ⟨_, rfl⟩
  obtain ⟨R, hRdef⟩ : ∃ R : Subgroup K, R = Rest K L₁ L₂ := ⟨_, rfl⟩
  rw [← hRdef]
  have hE : layer K = N ⊔ R := by rw [hNdef, hRdef]; exact layer_eq_sup_rest hL₁ hL₂
  have hRN : R ≤ centralizer (N : Set K) := by
    rw [hNdef, hRdef]; exact rest_le_centralizer hL₁ hL₂
  have hRperf : ⁅R, R⁆ = R := by rw [hRdef]; exact rest_perfect L₁ L₂
  have hRz : ∀ x ∈ R, z * x * z⁻¹ ∈ R := by rw [hRdef]; exact rest_conj hz hL₂def
  have hNz : ∀ x ∈ N, z * x * z⁻¹ ∈ N := by rw [hNdef]; exact sup_conj hz hL₂def
  have hRc : ∀ r ∈ R, ∀ n ∈ N, n * r = r * n := fun r hr n hn =>
    mem_centralizer_iff.1 (hRN hr) n hn
  have hNR : N ⊓ R = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [mem_bot]
    exact center_sup_eq_bot hF hL₁ hL₂ x (by rw [← hNdef]; exact hx.1)
      fun y hy => hRc x hx.2 y (by rw [hNdef]; exact hy)
  have hNle : N ≤ layer K := by rw [hE]; exact le_sup_left
  have hRle : R ≤ layer K := by rw [hE]; exact le_sup_right
  have hEc : (layer K).Characteristic := layer_characteristic
  have hEn : (layer K).Normal := inferInstance
  have hfix : ∀ m ∈ layer K, z * m = m * z →
      ∃ p ∈ N, ∃ q ∈ R, m = p * q ∧ z * p = p * z ∧ z * q = q * z := by
    intro m hm hmz
    rw [hE] at hm
    obtain ⟨n, hn, r, hr, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hRN hm
    obtain ⟨h1, h2⟩ := fixed_decomp hNR hNz hRz hn hr hmz
    exact ⟨n, hn, r, hr, rfl, h1, h2⟩
  by_contra hR1
  have hQex : ∃ q ∈ R, q ≠ 1 ∧ z * q = q * z := by
    by_contra hcon
    push Not at hcon
    have hfix' : ∀ w ∈ R, z * w = w * z → w = 1 := fun w hw hwz => by
      by_contra hw1
      exact hcon w hw hw1 hwz
    exact hR1 (eq_bot_of_isPerfect_of_commute hRperf
      (fixedPointFree_commute_of_mul_self_eq_one hz hRz hfix'))
  have hPex : ∃ p ∈ N, p ≠ 1 ∧ z * p = p * z := by
    obtain ⟨a, ha, b, hb, hab⟩ := component_nonab hF hL₁
    have ha1 : a ≠ 1 := fun h1 => hab (by rw [h1]; simp)
    by_cases hsw : L₂ = L₁
    · have hN : N = L₁ := by rw [hNdef, hsw, sup_idem]
      have hNz' : ∀ x ∈ L₁, z * x * z⁻¹ ∈ L₁ := by rw [← hN]; exact hNz
      by_contra hcon
      push Not at hcon
      have hfix' : ∀ w ∈ L₁, z * w = w * z → w = 1 := fun w hw hwz => by
        by_contra hw1
        exact hcon w (by rw [hN]; exact hw) hw1 hwz
      exact hab (fixedPointFree_commute_of_mul_self_eq_one hz hNz' hfix' a ha b hb)
    · have hne : L₁ ≠ L₂ := fun h1 => hsw h1.symm
      have hcom := component_commute hL₁ hL₂ hne
      have hdisj := component_inf_eq_bot hF hL₁ hL₂ hne
      have hXa : z * a * z⁻¹ ∈ L₂ := by rw [hL₂def]; exact ⟨a, ha, rfl⟩
      refine ⟨a * (z * a * z⁻¹), ?_, swap_ne_one hdisj hL₂def ha ha1,
        swap_fixed hz hcom hL₂def ha⟩
      rw [hNdef]
      exact mul_mem (mem_sup_left ha) (mem_sup_right hXa)
  have hDmem : ∀ x : K, x ∈ centralizer ({z} : Set K) ↔ x * z = z * x := fun x =>
    mem_centralizer_singleton_iff
  have hMnorm : ∀ b ∈ B, ∀ x ∈ layer K ⊓ centralizer ({z} : Set K),
      b * x * b⁻¹ ∈ layer K ⊓ centralizer ({z} : Set K) := by
    intro b hb x hx
    refine ⟨hEn.conj_mem x hx.1 b, ?_⟩
    exact (centralizer ({z} : Set K)).mul_mem ((centralizer ({z} : Set K)).mul_mem
      (h.le_cent hb) hx.2) ((centralizer ({z} : Set K)).inv_mem (h.le_cent hb))
  have hBM : B ≤ layer K ⊓ centralizer ({z} : Set K) := by
    rcases inf_eq_bot_or_le_of_simple h.simple hMnorm with hbot | hle
    · exfalso
      have hMz : ∀ m ∈ layer K ⊓ centralizer ({z} : Set K), m ∈ zpowers z := by
        intro m hm
        apply h.cent m hm.2
        intro b hb
        have h1 : m * b * m⁻¹ * b⁻¹ ∈ B ⊓ (layer K ⊓ centralizer ({z} : Set K)) := by
          refine ⟨B.mul_mem (h.norm m hm.2 b hb) (B.inv_mem hb), ?_⟩
          have h2 : m * b * m⁻¹ * b⁻¹ = m * (b * m⁻¹ * b⁻¹) := by group
          rw [h2]
          exact (layer K ⊓ centralizer ({z} : Set K)).mul_mem hm
            (hMnorm b hb m⁻¹ ((layer K ⊓ centralizer ({z} : Set K)).inv_mem hm))
        rw [hbot, mem_bot] at h1
        calc m * b = (m * b * m⁻¹ * b⁻¹) * b * m := by group
          _ = b * m := by rw [h1]; group
      obtain ⟨p, hpN, hp1, hpz⟩ := hPex
      obtain ⟨q, hqR, hq1, hqz⟩ := hQex
      have hp : p ∈ zpowers z := hMz p ⟨hNle hpN, (hDmem p).2 hpz.symm⟩
      have hq : q ∈ zpowers z := hMz q ⟨hRle hqR, (hDmem q).2 hqz.symm⟩
      rcases (mem_zpowers_iff_of_mul_self_eq_one hz).1 hp with h1 | h1
      · exact hp1 h1
      rcases (mem_zpowers_iff_of_mul_self_eq_one hz).1 hq with h2 | h2
      · exact hq1 h2
      have hzNR : z ∈ N ⊓ R := ⟨h1 ▸ hpN, h2 ▸ hqR⟩
      rw [hNR, mem_bot] at hzNR
      exact h.z_ne hzNR
    · exact hle
  have hPQ : ∀ p ∈ N ⊓ centralizer ({z} : Set K), ∀ q ∈ R ⊓ centralizer ({z} : Set K),
      p * q = q * p := fun p hp q hq => hRc q hq.1 p hp.1
  have hMdec : ∀ m ∈ layer K ⊓ centralizer ({z} : Set K),
      ∃ p ∈ N ⊓ centralizer ({z} : Set K), ∃ q ∈ R ⊓ centralizer ({z} : Set K), m = p * q := by
    intro m hm
    obtain ⟨p, hpN, q, hqR, hmpq, hp, hq⟩ := hfix m hm.1 ((hDmem m).1 hm.2).symm
    exact ⟨p, ⟨hpN, (hDmem p).2 hp.symm⟩, q, ⟨hqR, (hDmem q).2 hq.symm⟩, hmpq⟩
  have hBnorm : ∀ m ∈ layer K ⊓ centralizer ({z} : Set K), ∀ b ∈ B, m * b * m⁻¹ ∈ B :=
    fun m hm b hb => h.norm m hm.2 b hb
  have hPM : N ⊓ centralizer ({z} : Set K) ≤ layer K ⊓ centralizer ({z} : Set K) :=
    inf_le_inf_right _ hNle
  have hQM : R ⊓ centralizer ({z} : Set K) ≤ layer K ⊓ centralizer ({z} : Set K) :=
    inf_le_inf_right _ hRle
  have hBPQ := simple_le_or_le_of_decomposition h.simple h.nonab hBM hPM hQM hPQ hMdec hBnorm
  rcases hBPQ with hBP | hBQ
  ·
    have hQz : ∀ x ∈ R, z * x = x * z → x ∈ zpowers z := by
      intro x hx hxz
      apply h.cent x ((hDmem x).2 hxz.symm)
      intro b hb
      exact (hRc x hx b (hBP hb).1).symm
    obtain ⟨q, hqR, hq1, hqz⟩ := hQex
    rcases (mem_zpowers_iff_of_mul_self_eq_one hz).1 (hQz q hqR hqz) with h1 | h1
    · exact hq1 h1
    have hzR : z ∈ R := h1 ▸ hqR
    by_cases hsw : L₂ = L₁
    · obtain ⟨x, hxR, hxz, hxn⟩ :=
        exists_commute_not_mem_zpowers (Subgroup.isPerfect_iff.2 hRperf) hzR hz h.z_ne
      exact hxn (hQz x hxR hxz.symm)
    · exact z_not_mem_layer hL₁ hL₂def hsw (hRle hzR)
  ·
    have hPz : ∀ x ∈ N, z * x = x * z → x ∈ zpowers z := by
      intro x hx hxz
      apply h.cent x ((hDmem x).2 hxz.symm)
      intro b hb
      exact hRc b (hBQ hb).1 x hx
    obtain ⟨p, hpN, hp1, hpz⟩ := hPex
    rcases (mem_zpowers_iff_of_mul_self_eq_one hz).1 (hPz p hpN hpz) with h1 | h1
    · exact hp1 h1
    have hzN : z ∈ N := h1 ▸ hpN
    by_cases hsw : L₂ = L₁
    · have hN : N = L₁ := by rw [hNdef, hsw, sup_idem]
      have hzL : z ∈ L₁ := by rw [← hN]; exact hzN
      obtain ⟨x, hxL, hxz, hxn⟩ := exists_commute_not_mem_zpowers hL₁.1.1 hzL hz h.z_ne
      exact hxn (hPz x (by rw [hN]; exact hxL) hxz.symm)
    · have hne : L₁ ≠ L₂ := fun h1 => hsw h1.symm
      have hcom := component_commute hL₁ hL₂ hne
      have hdisj := component_inf_eq_bot hF hL₁ hL₂ hne
      obtain ⟨a, ha, b, hb, hab⟩ := component_nonab hF hL₁
      have hXa : z * a * z⁻¹ ∈ L₂ := by rw [hL₂def]; exact ⟨a, ha, rfl⟩
      have hXb : z * b * z⁻¹ ∈ L₂ := by rw [hL₂def]; exact ⟨b, hb, rfl⟩
      have hpa : a * (z * a * z⁻¹) ∈ N := by
        rw [hNdef]; exact mul_mem (mem_sup_left ha) (mem_sup_right hXa)
      have hpb : b * (z * b * z⁻¹) ∈ N := by
        rw [hNdef]; exact mul_mem (mem_sup_left hb) (mem_sup_right hXb)
      have hza := hPz _ hpa (swap_fixed hz hcom hL₂def ha)
      have hzb := hPz _ hpb (swap_fixed hz hcom hL₂def hb)
      apply hab
      apply swap_commute hdisj hcom hL₂def ha hb
      rcases (mem_zpowers_iff_of_mul_self_eq_one hz).1 hza with e1 | e1 <;>
        rcases (mem_zpowers_iff_of_mul_self_eq_one hz).1 hzb with e2 | e2 <;>
        rw [e1, e2] <;> simp

section Diagonal

variable {L₁ L₂ : Subgroup K}

@[expose] def diagHom (z : K) (hcom : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    (hL₂ : L₂ = L₁.map (MulAut.conj z).toMonoidHom) : ↥L₁ →* K where
  toFun s := (s : K) * (z * (s : K) * z⁻¹)
  map_one' := by simp
  map_mul' s t := by
    have hXs : z * (s : K) * z⁻¹ ∈ L₂ := by rw [hL₂]; exact ⟨s, s.2, rfl⟩
    have h1 : (t : K) * (z * (s : K) * z⁻¹) = (z * (s : K) * z⁻¹) * t := hcom t t.2 _ hXs
    calc ((s * t : ↥L₁) : K) * (z * ((s * t : ↥L₁) : K) * z⁻¹)
        = (s : K) * ((t : K) * (z * (s : K) * z⁻¹)) * (z * (t : K) * z⁻¹) := by
          simp only [Subgroup.coe_mul]; group
      _ = (s : K) * ((z * (s : K) * z⁻¹) * t) * (z * (t : K) * z⁻¹) := by rw [h1]
      _ = ((s : K) * (z * (s : K) * z⁻¹)) * ((t : K) * (z * (t : K) * z⁻¹)) := by group

omit [Finite K] in
theorem diagHom_apply (hcom : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    (hL₂ : L₂ = L₁.map (MulAut.conj z).toMonoidHom) (s : ↥L₁) :
    diagHom z hcom hL₂ s = (s : K) * (z * (s : K) * z⁻¹) := rfl

omit [Finite K] in
theorem diagHom_injective (hdisj : L₁ ⊓ L₂ = ⊥) (hcom : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    (hL₂ : L₂ = L₁.map (MulAut.conj z).toMonoidHom) :
    Function.Injective (diagHom z hcom hL₂) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro s hs
  rw [MonoidHom.mem_ker, diagHom_apply] at hs
  have := swap_ne_one hdisj hL₂ s.2
  rw [mem_bot]
  by_contra hne
  exact this (fun h => hne (Subtype.ext h)) hs

omit [Finite K] in
theorem diagHom_range (hz : z * z = 1) (hdisj : L₁ ⊓ L₂ = ⊥)
    (hcom : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    (hL₂ : L₂ = L₁.map (MulAut.conj z).toMonoidHom) :
    (diagHom z hcom hL₂).range = (L₁ ⊔ L₂) ⊓ centralizer ({z} : Set K) := by
  have hL₁ : L₂.map (MulAut.conj z).toMonoidHom = L₁ := by
    rw [hL₂]; exact map_conj_conj hz L₁
  ext m
  constructor
  · rintro ⟨s, rfl⟩
    have hXs : z * (s : K) * z⁻¹ ∈ L₂ := by rw [hL₂]; exact ⟨s, s.2, rfl⟩
    refine ⟨mul_mem (mem_sup_left s.2) (mem_sup_right hXs), ?_⟩
    exact mem_centralizer_singleton_iff.2 (swap_fixed hz hcom hL₂ s.2).symm
  · rintro ⟨hm, hmD⟩
    have hle : L₂ ≤ centralizer (L₁ : Set K) := fun b hb =>
      mem_centralizer_iff.2 fun a ha => hcom a ha b hb
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hle hm
    have hX : z * a * z⁻¹ ∈ L₂ := by rw [hL₂]; exact ⟨a, ha, rfl⟩
    have hY : z * b * z⁻¹ ∈ L₁ := by rw [← hL₁]; exact ⟨b, hb, rfl⟩
    have hfix : z * (a * b) * z⁻¹ = a * b :=
      conj_eq_self_iff.2 (mem_centralizer_singleton_iff.1 hmD).symm
    have h1 : (z * b * z⁻¹) * (z * a * z⁻¹) = a * b := by
      calc (z * b * z⁻¹) * (z * a * z⁻¹) = (z * a * z⁻¹) * (z * b * z⁻¹) := (hcom _ hY _ hX)
        _ = z * (a * b) * z⁻¹ := by group
        _ = a * b := hfix
    have h2 : a⁻¹ * (z * b * z⁻¹) = b * (z * a * z⁻¹)⁻¹ := by
      calc a⁻¹ * (z * b * z⁻¹) = a⁻¹ * ((z * b * z⁻¹) * (z * a * z⁻¹)) * (z * a * z⁻¹)⁻¹ := by
            group
        _ = b * (z * a * z⁻¹)⁻¹ := by rw [h1]; group
    have h3 : a⁻¹ * (z * b * z⁻¹) ∈ L₁ ⊓ L₂ :=
      ⟨L₁.mul_mem (L₁.inv_mem ha) hY, by rw [h2]; exact L₂.mul_mem hb (L₂.inv_mem hX)⟩
    rw [hdisj, mem_bot] at h3
    have h4 : z * b * z⁻¹ = a := (inv_mul_eq_one.1 h3).symm
    have h5 : z * a * z⁻¹ = b := by
      rw [h4] at h1
      exact mul_left_cancel h1
    exact ⟨⟨a, ha⟩, by rw [diagHom_apply, h5]⟩

end Diagonal

omit [Finite K] in
theorem inf_le_zpowers_of_inf_eq_bot (h : Setting K z B) {E : Subgroup K}
    (hEn : ∀ g x : K, x ∈ E → g * x * g⁻¹ ∈ E)
    (hbot : B ⊓ (E ⊓ centralizer ({z} : Set K)) = ⊥) :
    ∀ m ∈ E ⊓ centralizer ({z} : Set K), m ∈ zpowers z := by
  intro m hm
  apply h.cent m hm.2
  intro b hb
  have hbD : b ∈ centralizer ({z} : Set K) := h.le_cent hb
  have hMb : ∀ x ∈ E ⊓ centralizer ({z} : Set K),
      b * x * b⁻¹ ∈ E ⊓ centralizer ({z} : Set K) := fun x hx =>
    ⟨hEn b x hx.1, (centralizer ({z} : Set K)).mul_mem
      ((centralizer ({z} : Set K)).mul_mem hbD hx.2)
      ((centralizer ({z} : Set K)).inv_mem hbD)⟩
  have h1 : m * b * m⁻¹ * b⁻¹ ∈ B ⊓ (E ⊓ centralizer ({z} : Set K)) := by
    refine ⟨B.mul_mem (h.norm m hm.2 b hb) (B.inv_mem hb), ?_⟩
    have h2 : m * b * m⁻¹ * b⁻¹ = m * (b * m⁻¹ * b⁻¹) := by group
    rw [h2]
    exact (E ⊓ centralizer ({z} : Set K)).mul_mem hm
      (hMb m⁻¹ ((E ⊓ centralizer ({z} : Set K)).inv_mem hm))
  rw [hbot, mem_bot] at h1
  calc m * b = (m * b * m⁻¹ * b⁻¹) * b * m := by group
    _ = b * m := by rw [h1]; group

structure FixedData (K : Type*) [Group K] (S : Subgroup K) : Prop where
  normal : S.Normal
  simple : IsSimpleGroup ↥S
  nonab : ∃ a ∈ S, ∃ b ∈ S, a * b ≠ b * a
  cent : centralizer (S : Set K) = ⊥

structure SwapData (K : Type*) [Group K] (z : K) (B S₁ S₂ : Subgroup K) : Prop where
  comp : IsComponent S₁
  conj_eq : S₂ = S₁.map (MulAut.conj z).toMonoidHom
  ne : S₁ ≠ S₂
  comp_cases : ∀ L : Subgroup K, IsComponent L → L = S₁ ∨ L = S₂
  layer_eq : layer K = S₁ ⊔ S₂
  z_not_mem : z ∉ layer K
  inf_eq : layer K ⊓ centralizer ({z} : Set K) = B
  diag : ∀ m ∈ layer K ⊓ centralizer ({z} : Set K), ∃ s ∈ S₁, m = s * (z * s * z⁻¹)
  iso : Nonempty (↥S₁ ≃* ↥B)

theorem dichotomy (h : Setting K z B) :
    (∃ S : Subgroup K, FixedData K S) ∨ ∃ S₁ S₂ : Subgroup K, SwapData K z B S₁ S₂ := by
  have hF := h.fitting_eq_bot
  have hz := h.z_sq
  obtain ⟨L₁, hL₁⟩ := exists_component hF ⟨z, h.z_ne⟩
  obtain ⟨L₂, hL₂def⟩ : ∃ L₂ : Subgroup K, L₂ = L₁.map (MulAut.conj z).toMonoidHom := ⟨_, rfl⟩
  have hL₂ : IsComponent L₂ := by rw [hL₂def]; exact isComponent_conj hL₁ z
  have hR : Rest K L₁ L₂ = ⊥ := by rw [hL₂def]; exact rest_eq_bot h hL₁
  have hE : layer K = L₁ ⊔ L₂ := by rw [layer_eq_sup_rest hL₁ hL₂, hR, sup_bot_eq]
  have hEc : (layer K).Characteristic := layer_characteristic
  have hEn : (layer K).Normal := inferInstance
  have hcentE : centralizer (layer K : Set K) = ⊥ := centralizer_layer_eq_bot hF
  by_cases hsw : L₂ = L₁
  · left
    have hlay : layer K = L₁ := by rw [hE, hsw, sup_idem]
    refine ⟨L₁, ⟨?_, component_isSimple hF hL₁, component_nonab hF hL₁, ?_⟩⟩
    · rw [← hlay]; exact hEn
    · rw [← hlay]; exact hcentE
  · right
    refine ⟨L₁, L₂, ?_⟩
    have hne : L₁ ≠ L₂ := fun h1 => hsw h1.symm
    have hcom := component_commute hL₁ hL₂ hne
    have hdisj := component_inf_eq_bot hF hL₁ hL₂ hne
    have hrange := diagHom_range hz hdisj hcom hL₂def
    have hinj := diagHom_injective hdisj hcom hL₂def
    have hMrange : (diagHom z hcom hL₂def).range = layer K ⊓ centralizer ({z} : Set K) := by
      rw [hrange, hE]
    have hDmem : ∀ x : K, x ∈ centralizer ({z} : Set K) ↔ x * z = z * x := fun x =>
      mem_centralizer_singleton_iff
    have hEnorm : ∀ g x : K, x ∈ layer K → g * x * g⁻¹ ∈ layer K := fun g x hx =>
      hEn.conj_mem x hx g
    have hBM : B ≤ layer K ⊓ centralizer ({z} : Set K) := by
      have hMnorm : ∀ b ∈ B, ∀ x ∈ layer K ⊓ centralizer ({z} : Set K),
          b * x * b⁻¹ ∈ layer K ⊓ centralizer ({z} : Set K) := fun b hb x hx =>
        ⟨hEnorm b x hx.1, (centralizer ({z} : Set K)).mul_mem ((centralizer ({z} : Set K)).mul_mem
          (h.le_cent hb) hx.2) ((centralizer ({z} : Set K)).inv_mem (h.le_cent hb))⟩
      rcases inf_eq_bot_or_le_of_simple h.simple hMnorm with hbot | hle
      · exfalso
        have hMz := inf_le_zpowers_of_inf_eq_bot h hEnorm hbot
        obtain ⟨a, ha, b, hb, hab⟩ := component_nonab hF hL₁
        have hXa : z * a * z⁻¹ ∈ L₂ := by rw [hL₂def]; exact ⟨a, ha, rfl⟩
        have hXb : z * b * z⁻¹ ∈ L₂ := by rw [hL₂def]; exact ⟨b, hb, rfl⟩
        have hpa : a * (z * a * z⁻¹) ∈ layer K ⊓ centralizer ({z} : Set K) := by
          refine ⟨?_, (hDmem _).2 (swap_fixed hz hcom hL₂def ha).symm⟩
          rw [hE]; exact mul_mem (mem_sup_left ha) (mem_sup_right hXa)
        have hpb : b * (z * b * z⁻¹) ∈ layer K ⊓ centralizer ({z} : Set K) := by
          refine ⟨?_, (hDmem _).2 (swap_fixed hz hcom hL₂def hb).symm⟩
          rw [hE]; exact mul_mem (mem_sup_left hb) (mem_sup_right hXb)
        apply hab
        apply swap_commute hdisj hcom hL₂def ha hb
        rcases (mem_zpowers_iff_of_mul_self_eq_one hz).1 (hMz _ hpa) with e1 | e1 <;>
          rcases (mem_zpowers_iff_of_mul_self_eq_one hz).1 (hMz _ hpb) with e2 | e2 <;>
          rw [e1, e2] <;> simp
      · exact hle
    have hMB : layer K ⊓ centralizer ({z} : Set K) ≤ B := by
      have hTn : (B.comap (diagHom z hcom hL₂def)).Normal := by
        refine ⟨fun s hs t => ?_⟩
        rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
        have hts : diagHom z hcom hL₂def t ∈ centralizer ({z} : Set K) := by
          have h0 : diagHom z hcom hL₂def t ∈ (diagHom z hcom hL₂def).range := ⟨t, rfl⟩
          rw [hMrange] at h0
          exact h0.2
        exact h.norm _ hts _ hs
      have := component_isSimple hF hL₁
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (B.comap (diagHom z hcom hL₂def)) with hT | hT
      · exfalso
        have hB1 : ∀ b ∈ B, b = 1 := by
          intro b hb
          have hbM : b ∈ (diagHom z hcom hL₂def).range := by rw [hMrange]; exact hBM hb
          obtain ⟨s, rfl⟩ := hbM
          have hs : s ∈ B.comap (diagHom z hcom hL₂def) := hb
          rw [hT, mem_bot] at hs
          rw [hs, map_one]
        obtain ⟨a, ha, b, hb, hab⟩ := h.nonab
        exact hab (by rw [hB1 a ha, hB1 b hb])
      · intro m hm
        rw [← hMrange] at hm
        obtain ⟨s, rfl⟩ := hm
        have hs : s ∈ B.comap (diagHom z hcom hL₂def) := by rw [hT]; trivial
        exact hs
    have hBeq : layer K ⊓ centralizer ({z} : Set K) = B := le_antisymm hMB hBM
    have hdiag : ∀ m ∈ layer K ⊓ centralizer ({z} : Set K), ∃ s ∈ L₁, m = s * (z * s * z⁻¹) := by
      intro m hm
      rw [← hMrange] at hm
      obtain ⟨s, rfl⟩ := hm
      exact ⟨s, s.2, rfl⟩
    refine ⟨hL₁, hL₂def, hne, ?_, hE, z_not_mem_layer hL₁ hL₂def hsw, hBeq, hdiag, ?_⟩
    · intro L hL
      by_contra hcon
      push Not at hcon
      have hle : L ≤ Rest K L₁ L₂ := le_sSup ⟨hL, hcon.1, hcon.2⟩
      rw [hR, le_bot_iff] at hle
      have hnt : Nontrivial ↥L := isQuasisimple_nontrivial hL.1
      exact ((Subgroup.nontrivial_iff_ne_bot L).1 hnt) hle
    · exact ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr (by rw [hMrange, hBeq]))⟩

end CFSG.EvenSporadicStandard.SolomonRed
