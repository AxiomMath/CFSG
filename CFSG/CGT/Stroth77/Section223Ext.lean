module

public import CFSG.CGT.Stroth77.Section223Sylow

public section

namespace CFSG.CGT.Stroth77.S223

variable {G : Type} [Group G]

@[expose] def layer (D Q : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ Q ∧ x ∈ Subgroup.centralizer (D : Set G) ∧ x * x ∈ D ∧
    ∀ y ∈ Q, x⁻¹ * y⁻¹ * x * y ∈ D}
  mul_mem' := by
    rintro a b ⟨haQ, haC, ha2, ha⟩ ⟨hbQ, hbC, hb2, hb⟩
    refine ⟨mul_mem haQ hbQ, mul_mem haC hbC, ?_, fun y hy => ?_⟩
    · have e : a * b * (a * b) = (a * a) * (a⁻¹ * b⁻¹⁻¹ * a * b⁻¹) * (b * b) := by group
      rw [e]
      exact mul_mem (mul_mem ha2 (ha _ (inv_mem hbQ))) hb2
    · have hc := (Subgroup.mem_centralizer_iff.mp hbC) _ (ha y hy)
      have e : (a * b)⁻¹ * y⁻¹ * (a * b) * y =
          (b⁻¹ * ((a⁻¹ * y⁻¹ * a * y) * b)) * (b⁻¹ * y⁻¹ * b * y) := by group
      rw [e, hc, inv_mul_cancel_left]
      exact mul_mem (ha y hy) (hb y hy)
  one_mem' := ⟨one_mem _, one_mem _, by simp, fun y _ => by simp⟩
  inv_mem' := by
    rintro a ⟨haQ, haC, ha2, ha⟩
    refine ⟨inv_mem haQ, inv_mem haC, ?_, fun y hy => ?_⟩
    · rw [← mul_inv_rev]
      exact inv_mem ha2
    · have hc := (Subgroup.mem_centralizer_iff.mp haC) _ (inv_mem (ha y hy))
      have e : a⁻¹⁻¹ * y⁻¹ * a⁻¹ * y = a * (a⁻¹ * y⁻¹ * a * y)⁻¹ * a⁻¹ := by group
      rw [e, ← hc, mul_inv_cancel_right]
      exact inv_mem (ha y hy)

theorem layer_le (D Q : Subgroup G) : layer D Q ≤ Q := fun _ hx => hx.1

theorem le_layer {D Q : Subgroup G} (hDQ : D ≤ Q) (hQC : Q ≤ Subgroup.centralizer (D : Set G)) :
    D ≤ layer D Q := by
  intro d hd
  refine ⟨hDQ hd, hQC (hDQ hd), mul_mem hd hd, fun y hy => ?_⟩
  have hc := (Subgroup.mem_centralizer_iff.mp (hQC hy)) d hd
  rw [show d⁻¹ * y⁻¹ * d * y = d⁻¹ * (y⁻¹ * (d * y)) by group, hc]
  simp

theorem mem_normalizer_layer [Finite G] {D Q : Subgroup G} {g : G}
    (hgD : g ∈ Subgroup.normalizer (D : Set G)) (hgQ : g ∈ Subgroup.normalizer (Q : Set G)) :
    g ∈ Subgroup.normalizer (layer D Q : Set G) := by
  refine mem_normalizer_of_conj_mem fun x hx => ?_
  obtain ⟨hxQ, hxC, hx2, hx⟩ := hx
  refine ⟨(Subgroup.mem_normalizer_iff.mp hgQ x).mp hxQ, ?_, ?_, fun y hy => ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have hd' : g⁻¹ * d * g ∈ D := (Subgroup.mem_normalizer_iff''.mp hgD d).mp hd
    have h1 := (Subgroup.mem_centralizer_iff.mp hxC) _ hd'
    calc d * (g * x * g⁻¹) = g * ((g⁻¹ * d * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * d * g)) * g⁻¹ := by rw [h1]
      _ = g * x * g⁻¹ * d := by group
  · have := (Subgroup.mem_normalizer_iff.mp hgD _).mp hx2
    convert this using 1
    group
  · have hy' : g⁻¹ * y * g ∈ Q := (Subgroup.mem_normalizer_iff''.mp hgQ y).mp hy
    have := (Subgroup.mem_normalizer_iff.mp hgD _).mp (hx _ hy')
    convert this using 1
    group

theorem conj_mem_of_mem_sup_zpowers {K H : Subgroup G} {a g : G}
    (hK : ∀ k ∈ K, g * k * g⁻¹ ∈ H) (ha : g * a * g⁻¹ ∈ H) {y : G}
    (hy : y ∈ K ⊔ Subgroup.zpowers a) : g * y * g⁻¹ ∈ H := by
  have hle : K ⊔ Subgroup.zpowers a ≤ H.comap (MulAut.conj g).toMonoidHom :=
    sup_le (fun k hk => by simpa [MulAut.conj_apply] using hK k hk)
      ((Subgroup.zpowers_le).mpr (by simpa [MulAut.conj_apply] using ha))
  simpa [MulAut.conj_apply] using hle hy

theorem exists_ext_two_four [Finite G] {D Q : Subgroup G} {u r : G} (hQ : IsPGroup 2 Q)
    (hDQ : D < Q) (hQC : Q ≤ Subgroup.centralizer (D : Set G))
    (huD : u ∈ Subgroup.normalizer (D : Set G)) (huQ : u ∈ Subgroup.normalizer (Q : Set G))
    (hrD : r ∈ Subgroup.normalizer (D : Set G)) (hrQ : r ∈ Subgroup.normalizer (Q : Set G))
    (hu2 : u * u = 1) (hur : u * r * u * r = 1)
    (hr3 : r ^ 3 ∈ Subgroup.centralizer (Q : Set G)) :
    ∃ C : Subgroup G, D < C ∧ C ≤ Q ∧
      (Nat.card C = 2 * Nat.card D ∨ Nat.card C = 4 * Nat.card D) ∧
      (∀ x ∈ C, x * x ∈ D) ∧ u ∈ Subgroup.normalizer (C : Set G) ∧
      r ∈ Subgroup.normalizer (C : Set G) := by
  have hDY : D ≤ layer D Q := le_layer hDQ.le hQC
  have hYQ : layer D Q ≤ Q := layer_le D Q
  have huY := mem_normalizer_layer huD huQ
  have hrY := mem_normalizer_layer hrD hrQ
  have hYconj : ∀ {g : G}, g ∈ Subgroup.normalizer (layer D Q : Set G) →
      ∀ y ∈ layer D Q, g⁻¹ * y * g ∈ layer D Q :=
    fun hg y hy => (Subgroup.mem_normalizer_iff''.mp hg y).mp hy
  have hDconj : ∀ {g : G}, g ∈ Subgroup.normalizer (D : Set G) → ∀ k ∈ D, g * k * g⁻¹ ∈ D :=
    fun hg k hk => (Subgroup.mem_normalizer_iff.mp hg k).mp hk
  have hDconj' : ∀ {g : G}, g ∈ Subgroup.normalizer (D : Set G) → ∀ k ∈ D, g⁻¹ * k * g ∈ D :=
    fun hg k hk => (Subgroup.mem_normalizer_iff''.mp hg k).mp hk
  have hcomm : ∀ a ∈ layer D Q, ∀ b ∈ layer D Q, a⁻¹ * b⁻¹ * a * b ∈ D :=
    fun a ha b hb => ha.2.2.2 b hb.1
  have hsq : ∀ a ∈ layer D Q, a * a ∈ D := fun a ha => ha.2.2.1
  have hcent : ∀ a ∈ layer D Q, ∀ k ∈ D, k * a = a * k := fun a ha k hk =>
    Subgroup.mem_centralizer_iff.mp ha.2.1 k hk
  have hNY : ∀ a ∈ layer D Q, a ∈ Subgroup.normalizer (D : Set G) := fun a ha =>
    Subgroup.centralizer_le_normalizer _ ha.2.1
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hu_conj : ∀ x, u * x * u⁻¹ = u⁻¹ * x * u := fun x => by rw [huinv]
  have huu : ∀ x, u⁻¹ * (u⁻¹ * x * u) * u = x := fun x => by
    rw [show u⁻¹ * (u⁻¹ * x * u) * u = (u * u)⁻¹ * x * (u * u) by group, hu2]
    group
  have hru : r * u = u * r⁻¹ := by
    rw [show r * u = u⁻¹ * (u * r * u * r) * r⁻¹ by group, hur, huinv]
    group
  have hr3c : ∀ y ∈ Q, y * (r * (r * r)) = r * (r * r) * y := fun y hy => by
    have h := Subgroup.mem_centralizer_iff.mp hr3 y hy
    rwa [pow_three] at h
  have hrrr : ∀ y ∈ Q, r⁻¹ * (r⁻¹ * (r⁻¹ * y * r) * r) * r = y := fun y hy => by
    calc r⁻¹ * (r⁻¹ * (r⁻¹ * y * r) * r) * r = (r * (r * r))⁻¹ * (y * (r * (r * r))) := by
          group
      _ = (r * (r * r))⁻¹ * (r * (r * r) * y) := by rw [hr3c y hy]
      _ = y := by group
  have hrinv : ∀ y ∈ Q, r * y * r⁻¹ = r⁻¹ * (r⁻¹ * y * r) * r := fun y hy => by
    calc r * y * r⁻¹ = r⁻¹ * r⁻¹ * (r * (r * r) * y) * r⁻¹ := by group
      _ = r⁻¹ * r⁻¹ * (y * (r * (r * r))) * r⁻¹ := by rw [hr3c y hy]
      _ = r⁻¹ * (r⁻¹ * y * r) * r := by group
  obtain ⟨d, hdQ, hdD, hd2, hdc⟩ := exists_mem_sq_comm_mem hQ hDQ le_rfl
    (hQC.trans (Subgroup.centralizer_le_normalizer _)) Subgroup.le_normalizer
  have hdY : d ∈ layer D Q := ⟨hdQ, hQC hdQ, hd2, hdc⟩
  obtain ⟨w, hwY, hwD, hwu⟩ : ∃ w ∈ layer D Q, w ∉ D ∧ w⁻¹ * (u⁻¹ * w * u) ∈ D := by
    by_cases h : d⁻¹ * (u⁻¹ * d * u) ∈ D
    · exact ⟨d, hdY, hdD, h⟩
    · obtain ⟨d', hd'⟩ : ∃ d', d' = u⁻¹ * d * u := ⟨_, rfl⟩
      rw [← hd'] at h
      have hd'Y : d' ∈ layer D Q := hd' ▸ hYconj huY d hdY
      have hud' : u⁻¹ * d' * u = d := by rw [hd']; exact huu d
      refine ⟨d * d', mul_mem hdY hd'Y, fun hD => h ?_, ?_⟩
      · rw [show d⁻¹ * d' = (d * d)⁻¹ * (d * d') by group]
        exact mul_mem (inv_mem hd2) hD
      · have e : u⁻¹ * (d * d') * u = d' * d := by
          rw [show u⁻¹ * (d * d') * u = (u⁻¹ * d * u) * (u⁻¹ * d' * u) by group, hud', ← hd']
        rw [e, show (d * d')⁻¹ * (d' * d) = d'⁻¹ * d⁻¹ * d' * d by group]
        exact hcomm d' hd'Y d hdY
  have hwQ : w ∈ Q := hYQ hwY
  obtain ⟨e₀, he₀D, he₀⟩ : ∃ e₀ ∈ D, u⁻¹ * w * u = w * e₀ := ⟨_, hwu, by group⟩
  obtain ⟨w', hw'⟩ : ∃ w', w' = r⁻¹ * w * r := ⟨_, rfl⟩
  obtain ⟨w'', hw''⟩ : ∃ w'', w'' = r⁻¹ * w' * r := ⟨_, rfl⟩
  have hw'Y : w' ∈ layer D Q := hw' ▸ hYconj hrY w hwY
  have hw''Y : w'' ∈ layer D Q := hw'' ▸ hYconj hrY w' hw'Y
  have hrw'' : r⁻¹ * w'' * r = w := by rw [hw'', hw']; exact hrrr w hwQ
  have hrw : r * w * r⁻¹ = w'' := by rw [hrinv w hwQ, hw'', hw']
  have hrw' : r * w' * r⁻¹ = w := by rw [hw']; group
  have hrw''' : r * w'' * r⁻¹ = w' := by rw [hrinv w'' (hYQ hw''Y), hrw'', hw']
  obtain ⟨e₁, he₁⟩ : ∃ e₁, e₁ = r * e₀ * r⁻¹ := ⟨_, rfl⟩
  have he₁D : e₁ ∈ D := he₁ ▸ hDconj hrD e₀ he₀D
  obtain ⟨e₂, he₂⟩ : ∃ e₂, e₂ = r * e₁ * r⁻¹ := ⟨_, rfl⟩
  have he₂D : e₂ ∈ D := he₂ ▸ hDconj hrD e₁ he₁D
  have hw'u : u⁻¹ * w' * u = w'' * e₁ := by
    calc u⁻¹ * w' * u = (r * u)⁻¹ * w * (r * u) := by rw [hw']; group
      _ = (u * r⁻¹)⁻¹ * w * (u * r⁻¹) := by rw [hru]
      _ = r * (u⁻¹ * w * u) * r⁻¹ := by group
      _ = (r * w * r⁻¹) * (r * e₀ * r⁻¹) := by rw [he₀]; group
      _ = w'' * e₁ := by rw [hrw, he₁]
  have hw''u : u⁻¹ * w'' * u = w' * e₂ := by
    calc u⁻¹ * w'' * u = (r * u)⁻¹ * w' * (r * u) := by rw [hw'']; group
      _ = (u * r⁻¹)⁻¹ * w' * (u * r⁻¹) := by rw [hru]
      _ = r * (u⁻¹ * w' * u) * r⁻¹ := by group
      _ = (r * w'' * r⁻¹) * (r * e₁ * r⁻¹) := by rw [hw'u]; group
      _ = w' * e₂ := by rw [hrw''', he₂]
  have hwN := hNY w hwY
  have hwsq := hsq w hwY
  by_cases hww : w⁻¹ * w' ∈ D
  ·
    have hCY : D ⊔ Subgroup.zpowers w ≤ layer D Q := sup_le hDY (Subgroup.zpowers_le.mpr hwY)
    have hwC : w ∈ D ⊔ Subgroup.zpowers w := Subgroup.mem_sup_right (Subgroup.mem_zpowers w)
    refine ⟨D ⊔ Subgroup.zpowers w, SetLike.lt_iff_le_and_exists.mpr ⟨le_sup_left, w, hwC, hwD⟩,
      hCY.trans hYQ, Or.inl (card_sup_zpowers_two hwN hwsq hwD), fun x hx => hsq x (hCY hx),
      ?_, ?_⟩
    · refine mem_normalizer_of_conj_mem fun y hy => conj_mem_of_mem_sup_zpowers
        (fun k hk => Subgroup.mem_sup_left (hDconj huD k hk)) ?_ hy
      rw [hu_conj, he₀]
      exact mul_mem hwC (Subgroup.mem_sup_left he₀D)
    · have h : r⁻¹ ∈ Subgroup.normalizer ((D ⊔ Subgroup.zpowers w : Subgroup G) : Set G) := by
        refine mem_normalizer_of_conj_mem fun y hy => conj_mem_of_mem_sup_zpowers
          (fun k hk => ?_) ?_ hy
        · rw [inv_inv]
          exact Subgroup.mem_sup_left (hDconj' hrD k hk)
        · rw [inv_inv, ← hw', show w' = w * (w⁻¹ * w') by group]
          exact mul_mem hwC (Subgroup.mem_sup_left hww)
      have := inv_mem h
      rwa [inv_inv] at this
  obtain ⟨s, hs_def⟩ : ∃ s, s = w * w' * w'' := ⟨_, rfl⟩
  have hsY : s ∈ layer D Q := hs_def ▸ mul_mem (mul_mem hwY hw'Y) hw''Y
  by_cases hs : s ∈ D
  ·
    set K := D ⊔ Subgroup.zpowers w with hK
    have hKY : K ≤ layer D Q := sup_le hDY (Subgroup.zpowers_le.mpr hwY)
    have hCY : K ⊔ Subgroup.zpowers w' ≤ layer D Q := sup_le hKY (Subgroup.zpowers_le.mpr hw'Y)
    have hDC : ∀ k ∈ D, k ∈ K ⊔ Subgroup.zpowers w' := fun k hk =>
      Subgroup.mem_sup_left (Subgroup.mem_sup_left hk)
    have hwC : w ∈ K ⊔ Subgroup.zpowers w' :=
      Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers w))
    have hw'C : w' ∈ K ⊔ Subgroup.zpowers w' := Subgroup.mem_sup_right (Subgroup.mem_zpowers w')
    have hw''C : w'' ∈ K ⊔ Subgroup.zpowers w' := by
      rw [show w'' = (w * w')⁻¹ * (w * w' * w'') by group, ← hs_def]
      exact mul_mem (inv_mem (mul_mem hwC hw'C)) (hDC s hs)
    have hw'N : w' ∈ Subgroup.normalizer (K : Set G) := by
      refine mem_normalizer_of_conj_mem fun y hy => conj_mem_of_mem_sup_zpowers
        (fun k hk => ?_) ?_ hy
      · rw [← hcent w' hw'Y k hk, mul_inv_cancel_right]
        exact Subgroup.mem_sup_left hk
      · rw [show w' * w * w'⁻¹ = w * (w⁻¹ * w'⁻¹⁻¹ * w * w'⁻¹) by group]
        exact mul_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers w))
          (Subgroup.mem_sup_left (hcomm w hwY _ (inv_mem hw'Y)))
    have hw'K : w' ∉ K := by
      rw [hK, mem_sup_zpowers_iff hwN hwsq]
      rintro (h | ⟨k, hk, hkw⟩)
      · exact hwD (hrw' ▸ hDconj hrD w' h)
      · apply hww
        rw [hkw, hcent w hwY k hk, inv_mul_cancel_left]
        exact hk
    have hcardK : Nat.card K = 2 * Nat.card D := card_sup_zpowers_two hwN hwsq hwD
    refine ⟨K ⊔ Subgroup.zpowers w', SetLike.lt_iff_le_and_exists.mpr
      ⟨fun k hk => hDC k hk, w, hwC, hwD⟩, hCY.trans hYQ, Or.inr ?_,
      fun x hx => hsq x (hCY hx), ?_, ?_⟩
    · rw [card_sup_zpowers_two hw'N (Subgroup.mem_sup_left (hsq w' hw'Y)) hw'K, hcardK]
      ring
    · refine mem_normalizer_of_conj_mem fun y hy => conj_mem_of_mem_sup_zpowers
        (fun k hk => conj_mem_of_mem_sup_zpowers (fun k' hk' => hDC _ (hDconj huD k' hk')) ?_ hk)
        ?_ hy
      · rw [hu_conj, he₀]
        exact mul_mem hwC (hDC e₀ he₀D)
      · rw [hu_conj, hw'u]
        exact mul_mem hw''C (hDC e₁ he₁D)
    · have h : r⁻¹ ∈ Subgroup.normalizer ((K ⊔ Subgroup.zpowers w' : Subgroup G) : Set G) := by
        refine mem_normalizer_of_conj_mem fun y hy => conj_mem_of_mem_sup_zpowers
          (fun k hk => conj_mem_of_mem_sup_zpowers (fun k' hk' => ?_) ?_ hk) ?_ hy
        · rw [inv_inv]
          exact hDC _ (hDconj' hrD k' hk')
        · rw [inv_inv, ← hw']
          exact hw'C
        · rw [inv_inv, ← hw'']
          exact hw''C
      have := inv_mem h
      rwa [inv_inv] at this
  ·
    have hsN := hNY s hsY
    have hssq := hsq s hsY
    have hCY : D ⊔ Subgroup.zpowers s ≤ layer D Q := sup_le hDY (Subgroup.zpowers_le.mpr hsY)
    have hsC : s ∈ D ⊔ Subgroup.zpowers s := Subgroup.mem_sup_right (Subgroup.mem_zpowers s)
    have hsu : u⁻¹ * s * u = s * ((w''⁻¹ * w'⁻¹ * w'' * w') * (e₀ * e₁ * e₂)) := by
      have hc1 : e₀ * w'' = w'' * e₀ := hcent w'' hw''Y e₀ he₀D
      have hc2 : (e₀ * e₁) * w' = w' * (e₀ * e₁) := hcent w' hw'Y _ (mul_mem he₀D he₁D)
      calc u⁻¹ * s * u = (u⁻¹ * w * u) * (u⁻¹ * w' * u) * (u⁻¹ * w'' * u) := by
            rw [hs_def]; group
        _ = (w * e₀) * (w'' * e₁) * (w' * e₂) := by rw [he₀, hw'u, hw''u]
        _ = w * (e₀ * w'') * e₁ * w' * e₂ := by group
        _ = w * (w'' * e₀) * e₁ * w' * e₂ := by rw [hc1]
        _ = w * w'' * ((e₀ * e₁) * w') * e₂ := by group
        _ = w * w'' * (w' * (e₀ * e₁)) * e₂ := by rw [hc2]
        _ = s * ((w''⁻¹ * w'⁻¹ * w'' * w') * (e₀ * e₁ * e₂)) := by rw [hs_def]; group
    have hsr : r⁻¹ * s * r = s * ((w' * w'')⁻¹ * w⁻¹ * (w' * w'') * w) := by
      calc r⁻¹ * s * r = (r⁻¹ * w * r) * (r⁻¹ * w' * r) * (r⁻¹ * w'' * r) := by
            rw [hs_def]; group
        _ = w' * w'' * w := by rw [← hw', ← hw'', hrw'']
        _ = s * ((w' * w'')⁻¹ * w⁻¹ * (w' * w'') * w) := by rw [hs_def]; group
    refine ⟨D ⊔ Subgroup.zpowers s, SetLike.lt_iff_le_and_exists.mpr ⟨le_sup_left, s, hsC, hs⟩,
      hCY.trans hYQ, Or.inl (card_sup_zpowers_two hsN hssq hs), fun x hx => hsq x (hCY hx),
      ?_, ?_⟩
    · refine mem_normalizer_of_conj_mem fun y hy => conj_mem_of_mem_sup_zpowers
        (fun k hk => Subgroup.mem_sup_left (hDconj huD k hk)) ?_ hy
      rw [hu_conj, hsu]
      exact mul_mem hsC (Subgroup.mem_sup_left (mul_mem (hcomm w'' hw''Y w' hw'Y)
        (mul_mem (mul_mem he₀D he₁D) he₂D)))
    · have h : r⁻¹ ∈ Subgroup.normalizer ((D ⊔ Subgroup.zpowers s : Subgroup G) : Set G) := by
        refine mem_normalizer_of_conj_mem fun y hy => conj_mem_of_mem_sup_zpowers
          (fun k hk => ?_) ?_ hy
        · rw [inv_inv]
          exact Subgroup.mem_sup_left (hDconj' hrD k hk)
        · rw [inv_inv, hsr]
          exact mul_mem hsC (Subgroup.mem_sup_left (hcomm _ (mul_mem hw'Y hw''Y) w hwY))
      have := inv_mem h
      rwa [inv_inv] at this

end CFSG.CGT.Stroth77.S223
