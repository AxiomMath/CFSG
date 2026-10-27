module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterGmsOut

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools

section GmhConjGeneral

variable {G : Type*} [Group G]

theorem gmh_mem_map_conj_iff {D : Subgroup G} {c x : G} :
    x ∈ D.map (MulAut.conj c⁻¹).toMonoidHom ↔ c * x * c⁻¹ ∈ D := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show c * (c⁻¹ * y * c⁻¹⁻¹) * c⁻¹ = y by group]
    exact hy
  · intro hx
    refine ⟨c * x * c⁻¹, hx, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem gmh_exists_commute_conj_eq {D A : Subgroup G} {v d : G} (hv2 : v ^ 2 = 1)
    (hvD : ∀ x ∈ D, v * x * v⁻¹ ∈ D) (hDodd : Odd (Nat.card D)) (hd : d ∈ D)
    (hvA : ∀ a ∈ A, v * a = a * v) (hdA : ∀ a ∈ A, d * a * d⁻¹ ∈ A) :
    ∃ c ∈ D, c * v = v * c ∧ ∀ a ∈ A, c * a * c⁻¹ = d * a * d⁻¹ := by
  have hvv : v * v = 1 := by rw [← sq, hv2]
  have hvinv : v⁻¹ = v := by rw [inv_eq_iff_mul_eq_one, hvv]
  set k := d⁻¹ * (v * d * v⁻¹) with hk
  have hkD : k ∈ D := mul_mem (inv_mem hd) (hvD d hd)
  have hvd : v * d * v⁻¹ = d * k := by rw [hk]; group
  have hvk : v * k * v⁻¹ = k⁻¹ := by
    rw [hk, hvinv]
    calc v * (d⁻¹ * (v * d * v)) * v = v * d⁻¹ * v * d * (v * v) := by group
      _ = v * d⁻¹ * v * d := by rw [hvv, mul_one]
      _ = (d⁻¹ * (v * d * v))⁻¹ := by
          rw [show (d⁻¹ * (v * d * v))⁻¹ = v⁻¹ * d⁻¹ * v⁻¹ * d by group, hvinv]
  have hkA : ∀ a ∈ A, k * a = a * k := by
    intro a ha
    have h1 : v⁻¹ * a * v = a := by rw [mul_assoc, ← hvA a ha, inv_mul_cancel_left]
    have h2 : v * (d * a * d⁻¹) * v⁻¹ = d * a * d⁻¹ := by
      rw [hvA _ (hdA a ha), mul_inv_cancel_right]
    have h3 : k * a * k⁻¹ = a := by
      calc k * a * k⁻¹ = d⁻¹ * (v * (d * (v⁻¹ * a * v) * d⁻¹) * v⁻¹) * d := by rw [hk]; group
        _ = a := by rw [h1, h2]; group
    calc k * a = k * a * k⁻¹ * k := by group
      _ = a * k := by rw [h3]
  have hnodd : Odd (orderOf k) := hDodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard D hkD)
  obtain ⟨j, hj⟩ := hnodd
  have hk2 : k ^ (j + 1) * k ^ (j + 1) = k := by
    rw [← pow_add, show j + 1 + (j + 1) = orderOf k + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  refine ⟨d * k ^ (j + 1), mul_mem hd (pow_mem hkD _), ?_, fun a ha => ?_⟩
  · have hc : v * (d * k ^ (j + 1)) * v⁻¹ = d * k ^ (j + 1) := by
      calc v * (d * k ^ (j + 1)) * v⁻¹ = (v * d * v⁻¹) * (v * k * v⁻¹) ^ (j + 1) := by
            rw [conj_pow]; group
        _ = d * (k * (k ^ (j + 1))⁻¹) := by rw [hvd, hvk, inv_pow]; group
        _ = d * (k ^ (j + 1) * k ^ (j + 1) * (k ^ (j + 1))⁻¹) := by rw [hk2]
        _ = d * k ^ (j + 1) := by group
    calc d * k ^ (j + 1) * v = v * (d * k ^ (j + 1)) * v⁻¹ * v := by rw [hc]
      _ = v * (d * k ^ (j + 1)) := by group
  · have hc : Commute (k ^ (j + 1)) a := (Commute.pow_left (hkA a ha) (j + 1))
    calc d * k ^ (j + 1) * a * (d * k ^ (j + 1))⁻¹ =
        d * (k ^ (j + 1) * a) * (k ^ (j + 1))⁻¹ * d⁻¹ := by group
      _ = d * a * d⁻¹ := by rw [hc.eq]; group

end GmhConjGeneral


theorem U3C1Cartan.gmh_conj {G : Type} [Group G] {L T D : Subgroup G} {d : G}
    (hC : U3C1Cartan L T D d) {c : G} (hc : c ∈ szT₁ L T) :
    U3C1Cartan L T (D.map (MulAut.conj c⁻¹).toMonoidHom) (c⁻¹ * d * c) := by
  have hcA : ∀ b ∈ szA₁ (szT₁ L T), c * b = b * c := fun b hb =>
    mem_centralizer_iff.mp (mem_szA₁.mp hb).2 c hc
  have hcL : c ∈ L := szT₁_le_right L T hc
  have hcT : c ∈ T := szT₁_le_left L T hc
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [gmh_mem_map_conj_iff, show c * (c⁻¹ * d * c) * c⁻¹ = d by group]
    exact hC.mem
  · intro x hx
    rw [gmh_mem_map_conj_iff] at hx
    rw [show x = c⁻¹ * (c * x * c⁻¹) * c by group]
    exact mul_mem (mul_mem (inv_mem hcL) (hC.le hx)) hcL
  · intro x hx
    rw [gmh_mem_map_conj_iff] at hx
    have hcN : c ∈ normalizer (szT₁ L T : Set G) := Subgroup.le_normalizer hc
    rw [show x = c⁻¹ * (c * x * c⁻¹) * c by group]
    exact mul_mem (mul_mem (inv_mem hcN) (hC.le_normalizer hx)) hcN
  · rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxT, hxD⟩ := mem_inf.mp hx
    rw [gmh_mem_map_conj_iff] at hxD
    have h1 : c * x * c⁻¹ ∈ szT₁ L T ⊓ D :=
      mem_inf.mpr ⟨mul_mem (mul_mem hc hxT) (inv_mem hc), hxD⟩
    rw [hC.inf_eq, mem_bot] at h1
    rw [mem_bot]
    calc x = c⁻¹ * (c * x * c⁻¹) * c := by group
      _ = 1 := by rw [h1]; group
  · rw [Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective]
    exact hC.odd
  · intro b hb b' hb' hb1 hb'1
    obtain ⟨n, hn⟩ := hC.trans b hb b' hb' hb1 hb'1
    refine ⟨n, ?_⟩
    have hpow : (c⁻¹ * d * c) ^ n = c⁻¹ * d ^ n * c := by
      have := conj_pow (a := c⁻¹) (b := d) (i := n)
      simpa using this
    have hcb : c * b * c⁻¹ = b := by rw [hcA b hb, mul_inv_cancel_right]
    have hcb' : c⁻¹ * b' * c = b' := by rw [mul_assoc, ← hcA b' hb', inv_mul_cancel_left]
    rw [hpow]
    calc (c⁻¹ * d ^ n * c)⁻¹ * b * (c⁻¹ * d ^ n * c) =
        c⁻¹ * ((d ^ n)⁻¹ * (c * b * c⁻¹) * d ^ n) * c := by group
      _ = b' := by rw [hcb, hn, hcb']
  · intro s hs
    obtain ⟨n₀, hn₀, hn₀D⟩ := hC.conj (c * s * c⁻¹) (mul_mem (mul_mem hcT hs) (inv_mem hcT))
    refine ⟨c⁻¹ * n₀ * c, mul_mem (mul_mem (inv_mem hc) hn₀) hc, fun x hx => ?_⟩
    rw [gmh_mem_map_conj_iff] at hx ⊢
    rw [show c * ((c⁻¹ * n₀ * c)⁻¹ * s * x * ((c⁻¹ * n₀ * c)⁻¹ * s)⁻¹) * c⁻¹ =
      (n₀⁻¹ * (c * s * c⁻¹)) * (c * x * c⁻¹) * (n₀⁻¹ * (c * s * c⁻¹))⁻¹ by group]
    exact hn₀D _ hx

theorem U3Start.gmh_eq_one_of_conj_eq {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ}
    {t : G} {T : Subgroup G} (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {d : G}
    (htr : ∀ b ∈ szA₁ (szT₁ L T), ∀ b' ∈ szA₁ (szT₁ L T), b ≠ 1 → b' ≠ 1 →
      ∃ n : ℕ, (d ^ n)⁻¹ * b * d ^ n = b') {b : G} (hb : b ∈ szA₁ (szT₁ L T))
    (hbd : d⁻¹ * b * d = b) : b = 1 := by
  obtain ⟨-, hA₁card, -⟩ := h.facts_of_card_sylow hS2
  by_contra hb1
  have h2 : 2 < Nat.card (szA₁ (szT₁ L T)) := by
    rw [hA₁card]
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h.two_le
  obtain ⟨b₁, hb₁, b₂, hb₂, h1, h2', h12⟩ := exists_two_ne_one h2
  obtain ⟨b', hb', hb'1, hbb'⟩ : ∃ b' ∈ szA₁ (szT₁ L T), b' ≠ 1 ∧ b' ≠ b := by
    by_cases hb₁b : b₁ = b
    · exact ⟨b₂, hb₂, h2', fun e => h12 (hb₁b.trans e.symm)⟩
    · exact ⟨b₁, hb₁, h1, hb₁b⟩
  obtain ⟨n, hn⟩ := htr b hb b' hb' hb1 hb'1
  have hc : Commute d b := by
    show d * b = b * d
    calc d * b = d * (d⁻¹ * b * d) := by rw [hbd]
      _ = b * d := by group
  have hfix : (d ^ n)⁻¹ * b * d ^ n = b := by
    rw [mul_assoc, ← (hc.pow_left n).eq, inv_mul_cancel_left]
  exact hbb' (hn.symm.trans hfix)

namespace U3C1OuterSwapHigh

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}
  {T R₂ D : Subgroup G} {d : G} {V U U₁ : Subgroup G} {w s : G} {P : Subgroup G}
  (hW : U3C1OuterSwapHigh G L f t T R₂ D d V U U₁ w s P)
include hW

theorem gmh_conj {c : G} (hc : c ∈ szT₁ L T) :
    U3C1OuterSwapHigh G L f t T R₂ (D.map (MulAut.conj c⁻¹).toMonoidHom) (c⁻¹ * d * c) V U U₁
      w s P := by
  have hcU₁ : c ∈ normalizer (U₁ : Set G) := le_normalizer (hW.T₁_le_U₁ hc)
  have hcV : c ∈ normalizer (V : Set G) := hW.level.muOne_T₁_le_normalizer hW.step hc
  have hDconj : ∀ {K : Subgroup G}, D ≤ normalizer (K : Set G) → c ∈ normalizer (K : Set G) →
      D.map (MulAut.conj c⁻¹).toMonoidHom ≤ normalizer (K : Set G) := by
    intro K hDK hcK x hx
    rw [gmh_mem_map_conj_iff] at hx
    rw [show x = c⁻¹ * (c * x * c⁻¹) * c by group]
    exact mul_mem (mul_mem (inv_mem hcK) (hDK hx)) hcK
  exact { hW with
    step := { hW.step with
      cartan := hW.step.cartan.gmh_conj hc
      conf := { hW.step.conf with D_le := hDconj hW.step.conf.D_le hcV } }
    level := { hW.level with D_le := hDconj hW.level.D_le hcU₁ } }

theorem gmh_eq_one_of_normalizes {z : G} (hz : z ∈ szT₁ L T) (hzD : ∀ x ∈ D, z * x * z⁻¹ ∈ D) :
    z = 1 := by
  have h := hW.step.start
  have hS2 := hW.step.card_sylow
  have hC := hW.step.cartan
  obtain ⟨-, -, -, -, hinvT, -, -⟩ := h.facts_of_card_sylow hS2
  have hzd : z * d = d * z := by
    have h1 : z * d * z⁻¹ * d⁻¹ ∈ szT₁ L T ⊓ D := by
      refine mem_inf.mpr ⟨?_, mul_mem (hzD d hC.mem) (inv_mem hC.mem)⟩
      rw [show z * d * z⁻¹ * d⁻¹ = z * (d * z⁻¹ * d⁻¹) by group]
      exact mul_mem hz ((mem_normalizer_iff.mp (hC.le_normalizer hC.mem) _).mp (inv_mem hz))
    rw [hC.inf_eq, mem_bot] at h1
    calc z * d = z * d * z⁻¹ * d⁻¹ * (d * z) := by group
      _ = d * z := by rw [h1, one_mul]
  by_contra hz1
  have hT₁p : IsPGroup 2 (szT₁ L T) := h.isPGroup.to_le (szT₁_le_left L T)
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hT₁p ⟨z, hz⟩
  rw [Subgroup.orderOf_mk] at hk
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hz1 (orderOf_eq_one_iff.mp (by rw [hk, pow_zero]))
  obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
  set z' := z ^ 2 ^ i with hz'
  have hz'2 : z' ^ 2 = 1 := by
    rw [hz', ← pow_mul, ← pow_succ, ← hk, pow_orderOf_eq_one]
  have hz'1 : z' ≠ 1 := pow_ne_one_of_lt_orderOf (by positivity)
    (by rw [hk]; exact Nat.pow_lt_pow_right (by norm_num) (by omega))
  have hz'A : z' ∈ szA₁ (szT₁ L T) := hinvT z' (pow_mem hz _) hz'2
  have hz'd : d⁻¹ * z' * d = z' := by
    rw [hz', mul_assoc, ((Commute.pow_left hzd (2 ^ i))).eq, inv_mul_cancel_left]
  exact hz'1 (h.gmh_eq_one_of_conj_eq hS2 hC.trans hz'A hz'd)

theorem gmh_exists_normalizes : ∃ c ∈ szT₁ L T,
    ∀ x ∈ D.map (MulAut.conj c⁻¹).toMonoidHom,
      (t * w) * x * (t * w)⁻¹ ∈ D.map (MulAut.conj c⁻¹).toMonoidHom := by
  have h := hW.step.start
  have hS2 := hW.step.card_sylow
  have hC := hW.step.cartan
  obtain ⟨-, -, -, hTN₁, -, -, -⟩ := h.start_of_card_sylow hS2
  obtain ⟨-, -, -, hsqT, -, -, -⟩ := h.facts_of_card_sylow hS2
  have hv'T : t * w ∈ T := hW.tw_mem
  have hvv : (t * w) * (t * w) = 1 := by rw [← sq, hW.tw_sq]
  have hvinv : (t * w)⁻¹ = t * w := by rw [inv_eq_iff_mul_eq_one, hvv]
  obtain ⟨n, hn, hnD⟩ := hC.conj (t * w) hv'T
  have hnT : n ∈ T := szT₁_le_left L T hn
  have hm2 : (n⁻¹ * (t * w)) * (n⁻¹ * (t * w)) = 1 := by
    refine hW.gmh_eq_one_of_normalizes ?_ ?_
    · rw [show n⁻¹ * (t * w) * (n⁻¹ * (t * w)) = n⁻¹ * ((t * w) * n⁻¹ * (t * w)⁻¹) by
        rw [hvinv]; group]
      exact mul_mem (inv_mem hn) ((mem_normalizer_iff.mp (hTN₁ hv'T) _).mp (inv_mem hn))
    · intro x hx
      rw [show n⁻¹ * (t * w) * (n⁻¹ * (t * w)) * x * (n⁻¹ * (t * w) * (n⁻¹ * (t * w)))⁻¹ =
        (n⁻¹ * (t * w)) * ((n⁻¹ * (t * w)) * x * (n⁻¹ * (t * w))⁻¹) * (n⁻¹ * (t * w))⁻¹ by
        group]
      exact hnD _ (hnD x hx)
  obtain ⟨W', -, -, hW'card, -, -, -, hW'iff⟩ :=
    h.exists_W_of_card_sylow hS2 hv'T hW.tw_sq hW.tw_not_mem
  have hnW : n⁻¹ ∈ W' := by
    refine (hW'iff _ (inv_mem hn)).mp ?_
    have e1 : (t * w) * n⁻¹ * (t * w)⁻¹ = n := by
      calc (t * w) * n⁻¹ * (t * w)⁻¹ = n * ((n⁻¹ * (t * w)) * (n⁻¹ * (t * w))) := by
            rw [hvinv]; group
        _ = n := by rw [hm2, mul_one]
    rw [e1, inv_inv, ← sq]
    exact hsqT n hn
  obtain ⟨c, hc, hcv⟩ := h.muOneCent_exists_conj_of_mem_W hS2 hv'T hW.tw_sq hW.tw_not_mem
    hW'card hW'iff hnW
  refine ⟨c, hc, fun x hx => ?_⟩
  rw [gmh_mem_map_conj_iff] at hx ⊢
  rw [show c * ((t * w) * x * (t * w)⁻¹) * c⁻¹ =
    (c * (t * w) * c⁻¹) * (c * x * c⁻¹) * (c * (t * w) * c⁻¹)⁻¹ by group, hcv]
  exact hnD _ hx

theorem gmh_exists_torus (hvD : ∀ x ∈ D, (t * w) * x * (t * w)⁻¹ ∈ D) :
    ∃ e ∈ D, e * (t * w) = (t * w) * e ∧
      ∀ a ∈ szA₁ (szT₁ L T), ∀ b ∈ szA₁ (szT₁ L T), a ≠ 1 → b ≠ 1 →
        ∃ n : ℕ, (e ^ n)⁻¹ * a * e ^ n = b := by
  have h := hW.step.start
  have hS2 := hW.step.card_sylow
  have hC := hW.step.cartan
  obtain ⟨-, hvA, -, -⟩ := h.outer_facts_of_card_sylow hS2 hW.tw_mem hW.tw_sq hW.tw_not_mem
  have hdA : ∀ a ∈ szA₁ (szT₁ L T), d * a * d⁻¹ ∈ szA₁ (szT₁ L T) := fun a ha =>
    U3RootCoords.conj_mem_szA₁_of_mem_normalizer (hC.le_normalizer hC.mem) ha
  obtain ⟨e, heD, hev, heA⟩ :=
    gmh_exists_commute_conj_eq hW.tw_sq hvD hC.odd hC.mem hvA hdA
  have heA' : ∀ a ∈ szA₁ (szT₁ L T), e⁻¹ * a * e = d⁻¹ * a * d := by
    intro a ha
    have hda : d⁻¹ * a * d ∈ szA₁ (szT₁ L T) := by
      have := U3RootCoords.conj_mem_szA₁_of_mem_normalizer
        (inv_mem (hC.le_normalizer hC.mem)) ha
      simpa using this
    have h1 := heA _ hda
    rw [show d * (d⁻¹ * a * d) * d⁻¹ = a by group] at h1
    calc e⁻¹ * a * e = e⁻¹ * (e * (d⁻¹ * a * d) * e⁻¹) * e := by rw [h1]
      _ = d⁻¹ * a * d := by group
  have hpow : ∀ n : ℕ, ∀ a ∈ szA₁ (szT₁ L T), (e ^ n)⁻¹ * a * e ^ n = (d ^ n)⁻¹ * a * d ^ n := by
    intro n
    induction n with
    | zero => intro a _; simp
    | succ n ih =>
      intro a ha
      have hda : (d ^ n)⁻¹ * a * d ^ n ∈ szA₁ (szT₁ L T) := by
        have := U3RootCoords.conj_mem_szA₁_of_mem_normalizer
          (inv_mem (pow_mem (hC.le_normalizer hC.mem) n)) ha
        simpa using this
      calc (e ^ (n + 1))⁻¹ * a * e ^ (n + 1) = e⁻¹ * ((e ^ n)⁻¹ * a * e ^ n) * e := by
            rw [pow_succ]; group
        _ = d⁻¹ * ((d ^ n)⁻¹ * a * d ^ n) * d := by rw [ih a ha, heA' _ hda]
        _ = (d ^ (n + 1))⁻¹ * a * d ^ (n + 1) := by rw [pow_succ]; group
  refine ⟨e, heD, hev, fun a ha b hb ha1 hb1 => ?_⟩
  obtain ⟨n, hn⟩ := hC.trans a ha b hb ha1 hb1
  exact ⟨n, by rw [hpow n a ha, hn]⟩

end U3C1OuterSwapHigh

end CFSG.SeitzReduction.RankOne
