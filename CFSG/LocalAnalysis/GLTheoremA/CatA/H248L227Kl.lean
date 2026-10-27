module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H248L227QK
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H248L227

section Calc

variable {G : Type*} [Group G]

private def cm (a b : G) : G := a * b * a⁻¹ * b⁻¹

private structure Cen (Zc : Subgroup G) : Prop where
  cm_mem : ∀ a b : G, cm a b ∈ Zc
  central : ∀ z ∈ Zc, ∀ g : G, z * g = g * z

private theorem cm_swap (a b : G) : cm b a = (cm a b)⁻¹ := by
  simp [cm, mul_assoc]

private theorem cm_self (a : G) : cm a a = 1 := by simp [cm]

private theorem cm_one_right (a : G) : cm a 1 = 1 := by simp [cm]

private theorem cm_eq_one_iff {a b : G} : cm a b = 1 ↔ a * b = b * a := by
  simp only [cm, mul_inv_eq_one, mul_inv_eq_iff_eq_mul, one_mul]

variable {Zc : Subgroup G}

private theorem Cen.conj_eq (h : Cen Zc) {z : G} (hz : z ∈ Zc) (g : G) : g * z * g⁻¹ = z := by
  rw [← h.central z hz g, mul_inv_cancel_right]

private theorem Cen.cm_mul_right (h : Cen Zc) (a b c : G) :
    cm a (b * c) = cm a b * cm a c := by
  have e : cm a (b * c) = cm a b * (b * cm a c * b⁻¹) := by simp only [cm]; group
  rw [e, h.conj_eq (h.cm_mem a c) b]

private theorem Cen.cm_mul_left (h : Cen Zc) (a b c : G) :
    cm (a * b) c = cm a c * cm b c := by
  have e : cm (a * b) c = (a * cm b c * a⁻¹) * cm a c := by simp only [cm]; group
  rw [e, h.conj_eq (h.cm_mem b c) a]
  exact h.central _ (h.cm_mem b c) _

private theorem Cen.cm_of_mem_left (h : Cen Zc) {z : G} (hz : z ∈ Zc) (b : G) : cm z b = 1 :=
  cm_eq_one_iff.2 (h.central z hz b)

private theorem Cen.cm_of_mem_right (h : Cen Zc) {z : G} (hz : z ∈ Zc) (a : G) : cm a z = 1 :=
  cm_eq_one_iff.2 (h.central z hz a).symm

private theorem Cen.cm_mul_mem_left (h : Cen Zc) {z : G} (hz : z ∈ Zc) (a b : G) :
    cm (a * z) b = cm a b := by
  rw [h.cm_mul_left, h.cm_of_mem_left hz, mul_one]

private theorem Cen.cm_mul_mem_right (h : Cen Zc) {z : G} (hz : z ∈ Zc) (a b : G) :
    cm a (b * z) = cm a b := by
  rw [h.cm_mul_right, h.cm_of_mem_right hz, mul_one]

private def Cen.cmHom (h : Cen Zc) (a : G) : G →* G where
  toFun b := cm a b
  map_one' := cm_one_right a
  map_mul' b c := h.cm_mul_right a b c

private def Cen.Cd (h : Cen Zc) (d : G) : Subgroup G := (h.cmHom d).ker

private theorem Cen.mem_Cd (h : Cen Zc) {d c : G} : c ∈ h.Cd d ↔ cm d c = 1 :=
  MonoidHom.mem_ker

private def Dd (Zc : Subgroup G) (d : G) : Subgroup G := Subgroup.zpowers d ⊔ Zc

private theorem Cen.Zc_le_Cd (h : Cen Zc) (d : G) : Zc ≤ h.Cd d := fun z hz =>
  h.mem_Cd.2 (h.cm_of_mem_right hz d)

private theorem Cen.d_mem_Cd (h : Cen Zc) (d : G) : d ∈ h.Cd d := h.mem_Cd.2 (cm_self d)

private theorem Cen.Dd_le_Cd (h : Cen Zc) (d : G) : Dd Zc d ≤ h.Cd d :=
  sup_le (Subgroup.zpowers_le.2 (h.d_mem_Cd d)) (h.Zc_le_Cd d)

private theorem Cen.cm_Dd_Cd (h : Cen Zc) (d : G) {x c : G} (hx : x ∈ Dd Zc d)
    (hc : c ∈ h.Cd d) : cm x c = 1 := by
  have hle : Dd Zc d ≤ Subgroup.centralizer (h.Cd d : Set G) := by
    refine sup_le (Subgroup.zpowers_le.2 ?_) ?_
    · rw [Subgroup.mem_centralizer_iff]
      intro c hc
      exact (cm_eq_one_iff.1 (h.mem_Cd.1 hc)).symm
    · intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro c _
      exact (h.central z hz c).symm
  have := Subgroup.mem_centralizer_iff.1 (hle hx) c hc
  exact cm_eq_one_iff.2 this.symm

private theorem Cen.card_Cd (h : Cen Zc) {q : ℕ} (hq : q.Prime) (hG : Nat.card G = q ^ 5)
    (hZc : Nat.card Zc = q) {d e : G} (hde : cm d e ≠ 1) : Nat.card (h.Cd d) = q ^ 4 := by
  set R := (h.cmHom d).range
  have hRle : R ≤ Zc := by
    rintro _ ⟨u, rfl⟩
    exact h.cm_mem d u
  have h1 : Nat.card R ∣ q := hZc ▸ Subgroup.card_dvd_of_le hRle
  have h2 : Nat.card R = q := by
    rcases (Nat.dvd_prime hq).1 h1 with h3 | h3
    · exfalso
      have hbot : R = ⊥ := Subgroup.card_eq_one.1 h3
      apply hde
      have hmem : cm d e ∈ R := ⟨e, rfl⟩
      simpa [hbot] using hmem
    · exact h3
  have h3 := Subgroup.card_mul_index (h.cmHom d).ker
  rw [Subgroup.index_ker, h2, hG] at h3
  refine Nat.eq_of_mul_eq_mul_right hq.pos ?_
  show Nat.card (h.cmHom d).ker * q = q ^ 4 * q
  rw [h3]; ring

private theorem card_Dd [Finite G] {q : ℕ} (hq : q.Prime) (hG : Nat.card G = q ^ 5)
    (hZc : Nat.card Zc = q) {d : G} (hd : d ∉ Zc) : q ^ 2 ≤ Nat.card (Dd Zc d) := by
  have hdvd : Nat.card (Dd Zc d) ∣ q ^ 5 := hG ▸ Subgroup.card_subgroup_dvd_card _
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow hq).1 hdvd
  by_contra hlt
  have hk1 : k ≤ 1 := by
    by_contra hk2
    apply hlt
    rw [hk']
    exact Nat.pow_le_pow_right hq.pos (Nat.lt_of_not_le hk2)
  have hle : Nat.card (Dd Zc d) ≤ Nat.card Zc := by
    rw [hk', hZc]
    calc q ^ k ≤ q ^ 1 := Nat.pow_le_pow_right hq.pos hk1
      _ = q := pow_one q
  have heq : Zc = Dd Zc d := Subgroup.eq_of_le_of_card_ge le_sup_right hle
  apply hd
  rw [heq]
  exact Subgroup.mem_sup_left (Subgroup.mem_zpowers d)

private theorem Cen.exists_pow_cm [Finite G] (h : Cen Zc) {q : ℕ} (hq : q.Prime)
    (hZc : Nat.card Zc = q) {d e : G} (hde : cm d e ≠ 1) (u : G) :
    ∃ i : ℕ, (e ^ i)⁻¹ * u ∈ h.Cd d := by
  have hz0 : cm d e ∈ Zc := h.cm_mem d e
  have hle : Subgroup.zpowers (cm d e) ≤ Zc := Subgroup.zpowers_le.2 hz0
  have h1 : Nat.card (Subgroup.zpowers (cm d e)) ∣ q := hZc ▸ Subgroup.card_dvd_of_le hle
  have h2 : Nat.card (Subgroup.zpowers (cm d e)) = q := by
    rcases (Nat.dvd_prime hq).1 h1 with h3 | h3
    · exfalso
      rw [Nat.card_zpowers, orderOf_eq_one_iff] at h3
      exact hde h3
    · exact h3
  have hZeq : Subgroup.zpowers (cm d e) = Zc :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [h2, hZc])
  have hu : cm d u ∈ Submonoid.powers (cm d e) := by
    rw [mem_powers_iff_mem_zpowers, hZeq]
    exact h.cm_mem d u
  obtain ⟨i, hi⟩ := Submonoid.mem_powers_iff _ _ |>.1 hu
  refine ⟨i, ?_⟩
  rw [h.mem_Cd]
  have : cm d ((e ^ i)⁻¹ * u) = (cm d e ^ i)⁻¹ * cm d u := by
    show h.cmHom d ((e ^ i)⁻¹ * u) = _
    rw [map_mul, map_inv, map_pow]; rfl
  rw [this, hi]; simp

end Calc

section Counting

private theorem card_eq_mul_card_range {A B : Type*} [Group A] [Finite A] (K : Subgroup A)
    (f : A → B) (hf : ∀ a a', f a = f a' ↔ a⁻¹ * a' ∈ K) :
    Nat.card A = Nat.card K * Nat.card (Set.range f) := by
  let g : A ⧸ K → B :=
    Quotient.lift f (fun a a' h => (hf a a').2 (QuotientGroup.leftRel_apply.1 h))
  have hg : Function.Injective g := by
    intro x y hxy
    induction x using QuotientGroup.induction_on with | H a =>
    induction y using QuotientGroup.induction_on with | H a' =>
    exact QuotientGroup.eq.2 ((hf a a').1 hxy)
  have hrange : Set.range g = Set.range f := by
    ext b
    constructor
    · rintro ⟨x, rfl⟩
      induction x using QuotientGroup.induction_on with | H a => exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨(a : A ⧸ K), rfl⟩
  calc Nat.card A = Nat.card K * K.index := (Subgroup.card_mul_index K).symm
    _ = Nat.card K * Nat.card (A ⧸ K) := rfl
    _ = Nat.card K * Nat.card (Set.range f) := by
      rw [← hrange]
      exact congrArg _ (Nat.card_congr (Equiv.ofInjective g hg))

end Counting

section Fixed

private theorem exists_fixed {X G : Type*} [Group X] [Group G] [Finite G] {q : ℕ}
    (hq : q.Prime) (γ : X →* MulAut G) (T : Subgroup X) (hT : IsPGroup q T)
    (Zc : Subgroup G) [Zc.Normal] (hZ : ∀ t ∈ T, ∀ z ∈ Zc, γ t z = z)
    (hdiv : q ∣ Nat.card (G ⧸ Zc)) : ∃ d : G, d ∉ Zc ∧ ∀ t ∈ T, d⁻¹ * γ t d ∈ Zc := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hmap : ∀ t ∈ T, Zc ≤ Zc.comap (γ t).toMonoidHom := fun t ht z hz => by
    simpa [hZ t ht z hz] using hz
  letI : MulAction T (G ⧸ Zc) :=
    { smul := fun t x => QuotientGroup.map Zc Zc (γ t).toMonoidHom (hmap t t.2) x
      one_smul := fun x => by
        induction x using QuotientGroup.induction_on with | H g =>
        show QuotientGroup.map Zc Zc (γ ((1 : T) : X)).toMonoidHom (hmap _ (1 : T).2)
          (g : G ⧸ Zc) = g
        simp
      mul_smul := fun s t x => by
        induction x using QuotientGroup.induction_on with | H g =>
        show QuotientGroup.map Zc Zc (γ ((s * t : T) : X)).toMonoidHom (hmap _ (s * t : T).2)
            (g : G ⧸ Zc) =
          QuotientGroup.map Zc Zc (γ s).toMonoidHom (hmap _ s.2)
            (QuotientGroup.map Zc Zc (γ t).toMonoidHom (hmap _ t.2) (g : G ⧸ Zc))
        simp }
  have hfix : (1 : G ⧸ Zc) ∈ MulAction.fixedPoints T (G ⧸ Zc) := by
    rw [MulAction.mem_fixedPoints]
    intro t
    show QuotientGroup.map Zc Zc (γ t).toMonoidHom (hmap t t.2) 1 = 1
    simp
  obtain ⟨b, hb, hne⟩ := hT.exists_fixed_point_of_prime_dvd_card_of_fixed_point (G ⧸ Zc) hdiv hfix
  induction b using QuotientGroup.induction_on with | H d =>
  refine ⟨d, fun hd => hne ?_, fun t ht => ?_⟩
  · exact ((QuotientGroup.eq_one_iff d).2 hd).symm
  · have := (MulAction.mem_fixedPoints.1 hb) ⟨t, ht⟩
    have h2 : QuotientGroup.map Zc Zc (γ t).toMonoidHom (hmap t ht) (d : G ⧸ Zc) = d := this
    rw [QuotientGroup.map_mk] at h2
    exact QuotientGroup.eq.1 h2.symm

end Fixed

section Act

variable {X G : Type*} [Group X] [Group G]

private theorem cm_map (σ : MulAut G) (a b : G) : σ (cm a b) = cm (σ a) (σ b) := by
  simp [cm]

private theorem Cen.inv_conj_eq {Zc : Subgroup G} (h : Cen Zc) {z : G} (hz : z ∈ Zc) (g : G) :
    g⁻¹ * z * g = z := by
  simpa using h.conj_eq hz g⁻¹

private def wv (γ : X →* MulAut G) (e : G) (k : X) : G := γ k e * e⁻¹

private theorem wv_mul_self (γ : X →* MulAut G) (e : G) (k : X) : wv γ e k * e = γ k e := by
  simp [wv]

private structure Fix (γ : X →* MulAut G) (Zc : Subgroup G) (T₁ : Subgroup X) (d e : G)
    (q : ℕ) : Prop where
  cen : Cen Zc
  fixZ : ∀ t ∈ T₁, ∀ z ∈ Zc, γ t z = z
  fixd : ∀ t ∈ T₁, d⁻¹ * γ t d ∈ Zc
  conj : ∀ c ∈ T₁, ∀ a ∈ cen.Cd d, a⁻¹ * γ c a ∈ Dd Zc d
  dec : ∀ u : G, ∃ i : ℕ, (e ^ i)⁻¹ * u ∈ cen.Cd d
  ctr : ∀ g : G, (∀ g' : G, g * g' = g' * g) → g ∈ Zc
  odd : Nat.Coprime 2 q
  exp : ∀ z ∈ Zc, z ^ q = 1

variable {γ : X →* MulAut G} {Zc : Subgroup G} {T₁ : Subgroup X} {d e : G} {q : ℕ}

private theorem Fix.cm_act_eq (F : Fix γ Zc T₁ d e q) {t : X} (ht : t ∈ T₁) (a b : G) :
    cm (γ t a) (γ t b) = cm a b := by
  rw [← cm_map, F.fixZ t ht _ (F.cen.cm_mem a b)]

private theorem Fix.cm_d_act (F : Fix γ Zc T₁ d e q) {t : X} (ht : t ∈ T₁) (b : G) :
    cm d (γ t b) = cm d b := by
  have h1 : γ t d = d * (d⁻¹ * γ t d) := by rw [mul_inv_cancel_left]
  calc cm d (γ t b) = cm (d * (d⁻¹ * γ t d)) (γ t b) :=
        (F.cen.cm_mul_mem_left (F.fixd t ht) d _).symm
    _ = cm (γ t d) (γ t b) := by rw [← h1]
    _ = cm d b := F.cm_act_eq ht d b

private theorem Fix.wv_mem (F : Fix γ Zc T₁ d e q) {k : X} (hk : k ∈ T₁) :
    wv γ e k ∈ F.cen.Cd d := by
  rw [F.cen.mem_Cd]
  have h2 := F.cm_d_act hk e
  rw [← wv_mul_self γ e k, F.cen.cm_mul_right] at h2
  simpa using h2

private theorem Fix.P (F : Fix γ Zc T₁ d e q) {k : X} (hk : k ∈ T₁) {c : G}
    (hc : c ∈ F.cen.Cd d) : cm (γ k c) e = cm (wv γ e k) c * cm c e := by
  have hδ := F.conj k hk c hc
  have hγ : γ k c = c * (c⁻¹ * γ k c) := by rw [mul_inv_cancel_left]
  have h1 : cm (γ k c) (wv γ e k) = cm c (wv γ e k) := by
    conv_lhs => rw [hγ]
    rw [F.cen.cm_mul_left, F.cen.cm_Dd_Cd d hδ (F.wv_mem hk), mul_one]
  have h2 : cm (γ k c) (γ k e) = cm c e := F.cm_act_eq hk c e
  rw [← wv_mul_self γ e k, F.cen.cm_mul_right, h1] at h2
  rw [cm_swap c (wv γ e k)]
  exact eq_inv_mul_of_mul_eq h2

private theorem Fix.mem_Zc_of_Dd (F : Fix γ Zc T₁ d e q) {δ : G} (hδ : δ ∈ Dd Zc d)
    (he : δ * e = e * δ) : δ ∈ Zc := by
  refine F.ctr δ fun g' => ?_
  obtain ⟨i, hi⟩ := F.dec g'
  have h1 : δ * e ^ i = e ^ i * δ := Commute.pow_right (show Commute δ e from he) i
  have h2 : δ * ((e ^ i)⁻¹ * g') = ((e ^ i)⁻¹ * g') * δ :=
    cm_eq_one_iff.1 (F.cen.cm_Dd_Cd d hδ hi)
  calc δ * g' = δ * (e ^ i * ((e ^ i)⁻¹ * g')) := by rw [mul_inv_cancel_left]
    _ = (δ * e ^ i) * ((e ^ i)⁻¹ * g') := by rw [mul_assoc]
    _ = e ^ i * (δ * ((e ^ i)⁻¹ * g')) := by rw [h1, mul_assoc]
    _ = e ^ i * (((e ^ i)⁻¹ * g') * δ) := by rw [h2]
    _ = g' * δ := by rw [← mul_assoc, mul_inv_cancel_left]

private theorem Fix.triv_of_wv_mem (F : Fix γ Zc T₁ d e q) {k : X} (hk : k ∈ T₁)
    (hw : wv γ e k ∈ Zc) (u : G) : u⁻¹ * γ k u ∈ Zc := by
  let M : Submonoid G :=
    { carrier := {u | u⁻¹ * γ k u ∈ Zc}
      one_mem' := by simp
      mul_mem' := fun {u v} hu hv => by
        have hu' : u⁻¹ * γ k u ∈ Zc := hu
        have hv' : v⁻¹ * γ k v ∈ Zc := hv
        have e1 : (u * v)⁻¹ * γ k (u * v) = (v⁻¹ * (u⁻¹ * γ k u) * v) * (v⁻¹ * γ k v) := by
          simp only [map_mul]; group
        show (u * v)⁻¹ * γ k (u * v) ∈ Zc
        rw [e1, F.cen.inv_conj_eq hu']
        exact Zc.mul_mem hu' hv' }
  have heM : e ∈ M := by
    show e⁻¹ * γ k e ∈ Zc
    rw [← wv_mul_self γ e k, ← mul_assoc, F.cen.inv_conj_eq hw]
    exact hw
  have hcM : ∀ c ∈ F.cen.Cd d, c ∈ M := by
    intro c hc
    show c⁻¹ * γ k c ∈ Zc
    have hδ := F.conj k hk c hc
    refine F.mem_Zc_of_Dd hδ ?_
    apply cm_eq_one_iff.1
    have h1 := F.P hk hc
    rw [F.cen.cm_of_mem_left hw, one_mul] at h1
    have hγ : γ k c = c * (c⁻¹ * γ k c) := by rw [mul_inv_cancel_left]
    rw [hγ, F.cen.cm_mul_left] at h1
    exact mul_left_cancel (h1.trans (mul_one (cm c e)).symm)
  obtain ⟨i, hi⟩ := F.dec u
  have := M.mul_mem (M.pow_mem heM i) (hcM _ hi)
  rw [mul_inv_cancel_left] at this
  exact this

private theorem Fix.cm_comp (F : Fix γ Zc T₁ d e q) {s t : X} (hs : s ∈ T₁) (ht : t ∈ T₁) :
    cm (γ (s * t) e) e = cm (wv γ e s) (wv γ e t) * cm (wv γ e t) e * cm (wv γ e s) e := by
  have h1 : γ (s * t) e = γ s (wv γ e t) * (wv γ e s * e) := by
    rw [map_mul, MulAut.mul_apply, ← wv_mul_self γ e t, map_mul, wv_mul_self γ e s]
  rw [h1, F.cen.cm_mul_left, F.cen.cm_mul_left, cm_self, mul_one, F.P hs (F.wv_mem ht)]

private theorem aux_two {a x y : G} (hyx : y * x = x * y) (h : a * x * y = a⁻¹ * y * x) :
    a = a⁻¹ := by
  have h5 : a * (x * y) = a⁻¹ * (x * y) := by
    calc a * (x * y) = a * x * y := (mul_assoc _ _ _).symm
      _ = a⁻¹ * y * x := h
      _ = a⁻¹ * (y * x) := mul_assoc _ _ _
      _ = a⁻¹ * (x * y) := by rw [hyx]
  exact mul_right_cancel h5

private theorem Fix.step6 (F : Fix γ Zc T₁ d e q) {s t : X} (hs : s ∈ T₁) (ht : t ∈ T₁)
    (hκ : ∀ u : G, u⁻¹ * γ (s * t * s⁻¹ * t⁻¹) u ∈ Zc) :
    cm (wv γ e s) (wv γ e t) = 1 := by
  have h1 := hκ (γ (t * s) e)
  have h2 : γ (s * t * s⁻¹ * t⁻¹) (γ (t * s) e) = γ (s * t) e := by
    rw [← MulAut.mul_apply, ← map_mul]
    congr 2
    group
  rw [h2] at h1
  have h3 : γ (s * t) e = γ (t * s) e * ((γ (t * s) e)⁻¹ * γ (s * t) e) := by
    rw [mul_inv_cancel_left]
  have h4 : cm (γ (s * t) e) e = cm (γ (t * s) e) e := by
    conv_lhs => rw [h3]
    exact F.cen.cm_mul_mem_left h1 _ _
  rw [F.cm_comp hs ht, F.cm_comp ht hs, cm_swap (wv γ e s) (wv γ e t)] at h4
  have hyx : cm (wv γ e s) e * cm (wv γ e t) e = cm (wv γ e t) e * cm (wv γ e s) e :=
    F.cen.central _ (F.cen.cm_mem _ _) _
  have h6 := aux_two hyx h4
  have h7 : cm (wv γ e s) (wv γ e t) * cm (wv γ e s) (wv γ e t) = 1 :=
    mul_eq_one_iff_eq_inv.2 h6
  have h8 : orderOf (cm (wv γ e s) (wv γ e t)) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (by rwa [pow_two])
  have h9 : orderOf (cm (wv γ e s) (wv γ e t)) ∣ q :=
    orderOf_dvd_of_pow_eq_one (F.exp _ (F.cen.cm_mem _ _))
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes F.odd h8 h9)

private theorem Fix.iff_w (F : Fix γ Zc T₁ d e q) {s t : X} (hs : s ∈ T₁) (ht : t ∈ T₁) :
    (∀ u : G, u⁻¹ * γ (s⁻¹ * t) u ∈ Zc) ↔ (wv γ e s)⁻¹ * wv γ e t ∈ Zc := by
  have hinv : γ s⁻¹ (γ s e) = e := by
    rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
  constructor
  · intro H
    obtain ⟨z₁, hz₁⟩ : ∃ z₁ : G, z₁ = e⁻¹ * γ (s⁻¹ * t) e := ⟨_, rfl⟩
    have h1 : z₁ ∈ Zc := hz₁ ▸ H e
    have h2 : γ (s⁻¹ * t) e = e * z₁ := by rw [hz₁, mul_inv_cancel_left]
    have h3 : γ t e = γ s e * z₁ := by
      have h5 : t = s * (s⁻¹ * t) := by rw [mul_inv_cancel_left]
      conv_lhs => rw [h5]
      rw [map_mul, MulAut.mul_apply, h2, map_mul, F.fixZ s hs _ h1]
    have h4 : wv γ e t = wv γ e s * z₁ := by
      unfold wv
      rw [h3]
      calc γ s e * z₁ * e⁻¹ = γ s e * (z₁ * e⁻¹) := mul_assoc _ _ _
        _ = γ s e * (e⁻¹ * z₁) := by rw [F.cen.central _ h1 e⁻¹]
        _ = γ s e * e⁻¹ * z₁ := (mul_assoc _ _ _).symm
    rw [h4, inv_mul_cancel_left]
    exact h1
  · intro hz
    obtain ⟨z, hzdef⟩ : ∃ z : G, z = (wv γ e s)⁻¹ * wv γ e t := ⟨_, rfl⟩
    rw [← hzdef] at hz
    have h1 : wv γ e t = wv γ e s * z := by rw [hzdef, mul_inv_cancel_left]
    have h2 : γ t e = z * γ s e := by
      rw [← wv_mul_self γ e t, h1, ← wv_mul_self γ e s,
        ← F.cen.central _ hz (wv γ e s), mul_assoc]
    have hk : s⁻¹ * t ∈ T₁ := T₁.mul_mem (T₁.inv_mem hs) ht
    apply F.triv_of_wv_mem hk
    have h3 : γ (s⁻¹ * t) e = z * e := by
      rw [map_mul, MulAut.mul_apply, h2, map_mul, F.fixZ s⁻¹ (T₁.inv_mem hs) _ hz, hinv]
    have h4 : wv γ e (s⁻¹ * t) = z := by
      show γ (s⁻¹ * t) e * e⁻¹ = z
      rw [h3, mul_inv_cancel_right]
    rw [h4]
    exact hz

end Act

section Main

variable {X G : Type*} [Group X] [Finite X] [Group G] [Finite G]

private theorem main_G {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (Zc : Subgroup G)
    (hexp : ∀ g : G, g ^ q = 1) (hcard : Nat.card G = q ^ 5) (hcZ : Nat.card Zc = q)
    (cen : Cen Zc) (ctr : ∀ g : G, (∀ g' : G, g * g' = g' * g) → g ∈ Zc)
    (hab : ∀ A : Subgroup G, (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → Nat.card A ≤ q ^ 3)
    (γ : X →* MulAut G) (T : Subgroup X) (hT : IsPGroup q T)
    (hTZ : ∀ t ∈ T, ∀ z ∈ Zc, γ t z = z)
    (h2 : ∀ A B : Subgroup G, B ≤ A → (∀ a ∈ A, ∀ b ∈ B, a * b * a⁻¹ ∈ B) →
      (∀ t ∈ T, ∀ a ∈ A, γ t a ∈ A) → (∀ t ∈ T, ∀ b ∈ B, γ t b ∈ B) →
      (∀ a ∈ A, ∀ a' ∈ A, a * a' * a⁻¹ * a'⁻¹ ∈ B) → (∀ a ∈ A, a ^ q ∈ B) →
      Nat.card A ≤ q ^ 2 * Nat.card B →
      ∃ C : Subgroup X, C ≤ T ∧ (∀ c ∈ C, ∀ a ∈ A, a⁻¹ * γ c a ∈ B) ∧
        Nat.card T ≤ q * Nat.card C)
    (K : Subgroup X) (hK : ∀ t, t ∈ K ↔ ∀ u : G, u⁻¹ * γ t u ∈ Zc) :
    Nat.card T ≤ q ^ 4 * Nat.card (T ⊓ K : Subgroup X) ∧
      (Nat.card T = q ^ 4 * Nat.card (T ⊓ K : Subgroup X) →
        ∃ s ∈ T, ∃ t ∈ T, s * t * s⁻¹ * t⁻¹ ∉ K) := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Zc.Normal := Subgroup.normal_of_le_center (fun z hz =>
    Subgroup.mem_center_iff.2 fun g => (cen.central z hz g).symm)
  have hidx : Nat.card (G ⧸ Zc) = q ^ 4 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup Zc
    rw [hcard, hcZ] at h
    exact Nat.eq_of_mul_eq_mul_right hq.pos (by rw [← h]; ring)
  obtain ⟨d, hd, hdT⟩ := exists_fixed hq γ T hT Zc hTZ
    (by rw [hidx]; exact dvd_pow_self q (by norm_num))
  obtain ⟨e, he⟩ : ∃ e : G, cm d e ≠ 1 := by
    by_contra hcon
    exact hd (ctr d fun g' => cm_eq_one_iff.1 (not_not.1 fun hne => hcon ⟨g', hne⟩))
  have hCdcard : Nat.card (cen.Cd d) = q ^ 4 := cen.card_Cd hq hcard hcZ he
  have hDdcard : q ^ 2 ≤ Nat.card (Dd Zc d) := card_Dd hq hcard hcZ hd
  have hH1 : ∀ a ∈ cen.Cd d, ∀ b ∈ Dd Zc d, a * b * a⁻¹ ∈ Dd Zc d := by
    intro a ha b hb
    have : a * b = b * a := (cm_eq_one_iff.1 (cen.cm_Dd_Cd d hb ha)).symm
    rw [this, mul_inv_cancel_right]
    exact hb
  have hH2 : ∀ t ∈ T, ∀ a ∈ cen.Cd d, γ t a ∈ cen.Cd d := by
    intro t ht a ha
    rw [cen.mem_Cd]
    have h1 : γ t d = d * (d⁻¹ * γ t d) := by rw [mul_inv_cancel_left]
    have h3 : cm (γ t d) (γ t a) = cm d a := by
      rw [← cm_map, hTZ t ht _ (cen.cm_mem d a)]
    have h4 : cm (γ t d) (γ t a) = cm d (γ t a) := by
      conv_lhs => rw [h1]
      exact cen.cm_mul_mem_left (hdT t ht) _ _
    rw [← h4, h3]
    exact cen.mem_Cd.1 ha
  have hH3 : ∀ t ∈ T, ∀ b ∈ Dd Zc d, γ t b ∈ Dd Zc d := by
    intro t ht b hb
    have hle : Dd Zc d ≤ (Dd Zc d).comap (γ t).toMonoidHom := by
      refine sup_le (Subgroup.zpowers_le.2 ?_) ?_
      · show γ t d ∈ Dd Zc d
        have h1 : γ t d = d * (d⁻¹ * γ t d) := by rw [mul_inv_cancel_left]
        rw [h1]
        exact (Dd Zc d).mul_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers d))
          (Subgroup.mem_sup_right (hdT t ht))
      · intro z hz
        show γ t z ∈ Dd Zc d
        rw [hTZ t ht z hz]
        exact Subgroup.mem_sup_right hz
    exact hle hb
  obtain ⟨T₁, hT₁T, hconj, hcardT⟩ := h2 (cen.Cd d) (Dd Zc d) (cen.Dd_le_Cd d) hH1 hH2 hH3
    (fun a _ a' _ => Subgroup.mem_sup_right (cen.cm_mem a a'))
    (fun a _ => by rw [hexp a]; exact one_mem _)
    (calc Nat.card (cen.Cd d) = q ^ 2 * q ^ 2 := by rw [hCdcard]; ring
      _ ≤ q ^ 2 * Nat.card (Dd Zc d) := Nat.mul_le_mul_left _ hDdcard)
  have hodd : Nat.Coprime 2 q := (Nat.coprime_primes Nat.prime_two hq).2 (Ne.symm hq2)
  have F : Fix γ Zc T₁ d e q :=
    { cen := cen
      fixZ := fun t ht z hz => hTZ t (hT₁T ht) z hz
      fixd := fun t ht => hdT t (hT₁T ht)
      conj := hconj
      dec := cen.exists_pow_cm hq hcZ he
      ctr := ctr
      odd := hodd
      exp := fun z _ => hexp z }
  let f : T₁ → (cen.Cd d ⧸ Zc.subgroupOf (cen.Cd d)) := fun t =>
    QuotientGroup.mk ⟨wv γ e t, F.wv_mem t.2⟩
  have hf : ∀ a a' : T₁, f a = f a' ↔ a⁻¹ * a' ∈ K.subgroupOf T₁ := by
    intro a a'
    rw [Subgroup.mem_subgroupOf, hK]
    show (QuotientGroup.mk _ : cen.Cd d ⧸ Zc.subgroupOf (cen.Cd d)) = QuotientGroup.mk _ ↔ _
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    exact (F.iff_w a.2 a'.2).symm
  have hcnt := card_eq_mul_card_range (K.subgroupOf T₁) f hf
  have hQcard : Nat.card (cen.Cd d ⧸ Zc.subgroupOf (cen.Cd d)) = q ^ 3 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Zc.subgroupOf (cen.Cd d))
    have h' : Nat.card (Zc.subgroupOf (cen.Cd d)) = q := by
      rw [← hcZ]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (cen.Zc_le_Cd d)).toEquiv
    rw [hCdcard, h'] at h
    exact Nat.eq_of_mul_eq_mul_right hq.pos (by rw [← h]; ring)
  have hrange : Nat.card (Set.range f) ≤ q ^ 3 :=
    hQcard ▸ Nat.card_le_card_of_injective _ Subtype.val_injective
  have hK1 : Nat.card (K.subgroupOf T₁) = Nat.card (T₁ ⊓ K : Subgroup X) := by
    rw [← Subgroup.inf_subgroupOf_left K T₁]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hK2 : Nat.card (T₁ ⊓ K : Subgroup X) ≤ Nat.card (T ⊓ K : Subgroup X) :=
    Subgroup.card_le_of_le (inf_le_inf_right K hT₁T)
  have hA : Nat.card (K.subgroupOf T₁) ≤ Nat.card (T ⊓ K : Subgroup X) := hK1 ▸ hK2
  have hmain : Nat.card T ≤ q ^ 4 * Nat.card (T ⊓ K : Subgroup X) := by
    calc Nat.card T ≤ q * Nat.card T₁ := hcardT
      _ = q * (Nat.card (K.subgroupOf T₁) * Nat.card (Set.range f)) := by rw [hcnt]
      _ ≤ q * (Nat.card (T ⊓ K : Subgroup X) * q ^ 3) :=
          Nat.mul_le_mul_left q (Nat.mul_le_mul hA hrange)
      _ = q ^ 4 * Nat.card (T ⊓ K : Subgroup X) := by ring
  refine ⟨hmain, fun heq => ?_⟩
  have hbpos : 0 < Nat.card (T ⊓ K : Subgroup X) := Nat.card_pos
  have hr : q ^ 3 ≤ Nat.card (Set.range f) := by
    have h1 : q ^ 3 * (q * Nat.card (T ⊓ K : Subgroup X)) ≤
        Nat.card (Set.range f) * (q * Nat.card (T ⊓ K : Subgroup X)) := by
      calc q ^ 3 * (q * Nat.card (T ⊓ K : Subgroup X))
          = q ^ 4 * Nat.card (T ⊓ K : Subgroup X) := by ring
        _ = Nat.card T := heq.symm
        _ ≤ q * Nat.card T₁ := hcardT
        _ = q * (Nat.card (K.subgroupOf T₁) * Nat.card (Set.range f)) := by rw [hcnt]
        _ ≤ q * (Nat.card (T ⊓ K : Subgroup X) * Nat.card (Set.range f)) :=
            Nat.mul_le_mul_left q (Nat.mul_le_mul_right _ hA)
        _ = Nat.card (Set.range f) * (q * Nat.card (T ⊓ K : Subgroup X)) := by ring
    exact Nat.le_of_mul_le_mul_right h1 (Nat.mul_pos hq.pos hbpos)
  have hsurj : Function.Surjective f := by
    intro y
    by_contra hy
    have hy' : y ∉ Set.range f := fun ⟨x, hx⟩ => hy ⟨x, hx⟩
    have hlt := Finite.card_subtype_lt (p := fun z => z ∈ Set.range f) hy'
    rw [hQcard] at hlt
    exact absurd hlt (not_lt.2 hr)
  obtain ⟨c₁, hc₁, c₂, hc₂, hne⟩ : ∃ c₁ ∈ cen.Cd d, ∃ c₂ ∈ cen.Cd d, c₁ * c₂ ≠ c₂ * c₁ := by
    by_contra hcon
    have habel : ∀ a ∈ cen.Cd d, ∀ b ∈ cen.Cd d, a * b = b * a := by
      intro a ha b hb
      by_contra hne
      exact hcon ⟨a, ha, b, hb, hne⟩
    have h1 := hab (cen.Cd d) habel
    rw [hCdcard] at h1
    exact absurd h1 (not_le.2 (Nat.pow_lt_pow_right hq.one_lt (by norm_num)))
  obtain ⟨s, hs⟩ := hsurj (QuotientGroup.mk ⟨c₁, hc₁⟩)
  obtain ⟨t, ht⟩ := hsurj (QuotientGroup.mk ⟨c₂, hc₂⟩)
  by_contra hcon
  have hall : ∀ s ∈ T, ∀ t ∈ T, s * t * s⁻¹ * t⁻¹ ∈ K := by
    intro s hs t ht
    by_contra hn
    exact hcon ⟨s, hs, t, ht, hn⟩
  have h6 := F.step6 s.2 t.2 ((hK _).1 (hall s (hT₁T s.2) t (hT₁T t.2)))
  have h7 : (wv γ e s)⁻¹ * c₁ ∈ Zc := Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 hs)
  have h7' : (wv γ e t)⁻¹ * c₂ ∈ Zc := Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 ht)
  have e1 : c₁ = wv γ e s * ((wv γ e s)⁻¹ * c₁) := by rw [mul_inv_cancel_left]
  have e2 : c₂ = wv γ e t * ((wv γ e t)⁻¹ * c₂) := by rw [mul_inv_cancel_left]
  have h8 : cm c₁ c₂ = cm (wv γ e s) (wv γ e t) := by
    conv_lhs => rw [e1, e2]
    rw [cen.cm_mul_mem_left h7, cen.cm_mul_mem_right h7']
  exact hne (cm_eq_one_iff.1 (h8.trans h6))

end Main

theorem klingen_bound {X : Type} [Group X] [Finite X] {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (U Z : Subgroup X) [U.Normal] [Z.Normal] (hZU : Z ≤ U)
    (hexp : ∀ u ∈ U, u ^ q = 1) (hcl : ∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈ Z)
    (hcU : Nat.card U = q ^ 5) (hcZ : Nat.card Z = q)
    (hZ : ∀ u ∈ U, u ∈ Z ↔ ∀ v ∈ U, u * v = v * u)
    (hab : ∀ A : Subgroup X, A ≤ U → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → Nat.card A ≤ q ^ 3)
    (T : Subgroup X) (hT : IsPGroup q T) (hTZ : ∀ t ∈ T, ∀ z ∈ Z, t * z = z * t)
    (h2 : ∀ A B : Subgroup X, B ≤ A → (∀ a ∈ A, ∀ b ∈ B, a * b * a⁻¹ ∈ B) →
      (∀ t ∈ T, ∀ a ∈ A, t * a * t⁻¹ ∈ A) → (∀ t ∈ T, ∀ b ∈ B, t * b * t⁻¹ ∈ B) →
      (∀ a ∈ A, ∀ a' ∈ A, a * a' * a⁻¹ * a'⁻¹ ∈ B) → (∀ a ∈ A, a ^ q ∈ B) →
      Nat.card A ≤ q ^ 2 * Nat.card B →
      ∃ C : Subgroup X, C ≤ T ∧ (∀ c ∈ C, ∀ a ∈ A, a⁻¹ * (c * a * c⁻¹) ∈ B) ∧
        Nat.card T ≤ q * Nat.card C) :
    Nat.card T ≤ q ^ 4 * Nat.card (T ⊓ quotKer U Z : Subgroup X) ∧
      (Nat.card T = q ^ 4 * Nat.card (T ⊓ quotKer U Z : Subgroup X) →
        ∃ s ∈ T, ∃ t ∈ T, s * t * s⁻¹ * t⁻¹ ∉ quotKer U Z) := by
  have hmemZ : ∀ x : U, x ∈ Z.subgroupOf U ↔ (x : X) ∈ Z := fun x => Subgroup.mem_subgroupOf
  refine main_G (G := U) hq hq2 (Z.subgroupOf U) ?_ hcU
    ((Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZU).toEquiv).trans hcZ) ?_ ?_ ?_
    (MulAut.conjNormal (H := U)) T hT ?_ ?_ (quotKer U Z) ?_
  · intro g
    exact Subtype.ext (by simpa using hexp g g.2)
  · exact
      { cm_mem := fun a b => (hmemZ _).2 (hcl a a.2 b b.2)
        central := fun z hz g =>
          Subtype.ext (((hZ z z.2).1 ((hmemZ z).1 hz)) g g.2) }
  · intro g H
    exact (hmemZ g).2 ((hZ g g.2).2 fun v hv => congrArg Subtype.val (H ⟨v, hv⟩))
  · intro A hA
    have h1 := hab (A.map U.subtype) (Subgroup.map_subtype_le A)
      (by
        rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
        exact congrArg Subtype.val (hA a ha b hb))
    rwa [Subgroup.card_map_of_injective U.subtype_injective] at h1
  · intro t ht z hz
    refine Subtype.ext ?_
    rw [MulAut.conjNormal_apply, hTZ t ht z ((hmemZ z).1 hz), mul_inv_cancel_right]
  · intro A B hBA hBn hTA hTB hcomm hpow hcard
    have k2 : ∀ a ∈ A.map U.subtype, ∀ b ∈ B.map U.subtype, a * b * a⁻¹ ∈ B.map U.subtype := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      exact ⟨a * b * a⁻¹, hBn a ha b hb, rfl⟩
    have k3 : ∀ t ∈ T, ∀ a ∈ A.map U.subtype, t * a * t⁻¹ ∈ A.map U.subtype := by
      rintro t ht _ ⟨a, ha, rfl⟩
      exact ⟨MulAut.conjNormal (H := U) t a, hTA t ht a ha, MulAut.conjNormal_apply t a⟩
    have k4 : ∀ t ∈ T, ∀ b ∈ B.map U.subtype, t * b * t⁻¹ ∈ B.map U.subtype := by
      rintro t ht _ ⟨b, hb, rfl⟩
      exact ⟨MulAut.conjNormal (H := U) t b, hTB t ht b hb, MulAut.conjNormal_apply t b⟩
    have k5 : ∀ a ∈ A.map U.subtype, ∀ a' ∈ A.map U.subtype,
        a * a' * a⁻¹ * a'⁻¹ ∈ B.map U.subtype := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨a', ha', rfl⟩
      exact ⟨a * a' * a⁻¹ * a'⁻¹, hcomm a ha a' ha', rfl⟩
    have k6 : ∀ a ∈ A.map U.subtype, a ^ q ∈ B.map U.subtype := by
      rintro _ ⟨a, ha, rfl⟩
      exact ⟨a ^ q, hpow a ha, rfl⟩
    have k7 : Nat.card (A.map U.subtype) ≤ q ^ 2 * Nat.card (B.map U.subtype) := by
      rw [Subgroup.card_map_of_injective U.subtype_injective,
        Subgroup.card_map_of_injective U.subtype_injective]
      exact hcard
    obtain ⟨C, hCT, hC, hcardC⟩ := h2 (A.map U.subtype) (B.map U.subtype)
      (Subgroup.map_mono hBA) k2 k3 k4 k5 k6 k7
    refine ⟨C, hCT, fun c hc a ha => ?_, hcardC⟩
    obtain ⟨b, hb, hb'⟩ := Subgroup.mem_map.1 (hC c hc (a : X) ⟨a, ha, rfl⟩)
    have hba : b = a⁻¹ * MulAut.conjNormal (H := U) c a :=
      Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply]; exact hb')
    exact hba ▸ hb
  · intro t
    rw [mem_quotKer]
    constructor
    · intro H u
      refine (hmemZ _).2 ?_
      rw [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply]
      exact H u u.2
    · intro H u hu
      have h1 := (hmemZ _).1 (H ⟨u, hu⟩)
      rw [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply] at h1
      exact h1

end CFSG.LocalAnalysis.GLTheoremA.H248L227
