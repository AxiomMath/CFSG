module

public import CFSG.LocalAnalysis.ComponentClassification.HallQ8Struct

public section

namespace CFSG.ComponentClassification.Foote5.HallGen

open CFSG Subgroup CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {c : G}

@[expose] def Qsub (D : Subgroup G) (y' : G) (hN : y' ∈ normalizer (D : Set G))
    (hsq : y' * y' ∈ D) : Subgroup G where
  carrier := {x | x ∈ D ∨ ∃ d ∈ D, x = y' * d}
  one_mem' := Or.inl (one_mem D)
  mul_mem' := by
    have hc : ∀ a ∈ D, y'⁻¹ * a * y' ∈ D := fun a ha => by
      have := (mem_normalizer_iff.mp (inv_mem hN) a).mp ha
      rwa [inv_inv] at this
    rintro a b (ha | ⟨d, hd, rfl⟩) (hb | ⟨e, he, rfl⟩)
    · exact Or.inl (mul_mem ha hb)
    · exact Or.inr ⟨(y'⁻¹ * a * y') * e, mul_mem (hc a ha) he, by group⟩
    · exact Or.inr ⟨d * b, mul_mem hd hb, by group⟩
    · refine Or.inl ?_
      have : y' * d * (y' * e) = (y' * y') * ((y'⁻¹ * d * y') * e) := by group
      rw [this]
      exact mul_mem hsq (mul_mem (hc d hd) he)
  inv_mem' := by
    have hc : ∀ a ∈ D, y'⁻¹ * a * y' ∈ D := fun a ha => by
      have := (mem_normalizer_iff.mp (inv_mem hN) a).mp ha
      rwa [inv_inv] at this
    rintro x (hx | ⟨d, hd, rfl⟩)
    · exact Or.inl (inv_mem hx)
    · exact Or.inr ⟨(y'⁻¹ * d⁻¹ * y') * (y' * y')⁻¹, mul_mem (hc _ (inv_mem hd)) (inv_mem hsq),
        by group⟩

variable {y' : G} {hN : y' ∈ normalizer (D : Set G)} {hsq : y' * y' ∈ D}

omit [Finite G] in
theorem D_le_Qsub : D ≤ Qsub D y' hN hsq := fun _ hx => Or.inl hx

omit [Finite G] in
theorem y_mem_Qsub : y' ∈ Qsub D y' hN hsq := Or.inr ⟨1, one_mem D, (mul_one y').symm⟩

omit [Finite G] in
theorem Qsub_le {S : Subgroup G} (hDS : D ≤ S) (hyS : y' ∈ S) : Qsub D y' hN hsq ≤ S := by
  rintro x (hx | ⟨d, hd, rfl⟩)
  · exact hDS hx
  · exact mul_mem hyS (hDS hd)

theorem card_Qsub_le : Nat.card (Qsub D y' hN hsq) ≤ 2 * Nat.card D := by
  classical
  let f : Qsub D y' hN hsq → D ⊕ D := fun x =>
    if hx : (x : G) ∈ D then Sum.inl ⟨x, hx⟩
    else Sum.inr ⟨y'⁻¹ * x, by
      rcases x.2 with h1 | ⟨d, hd, hxd⟩
      · exact absurd h1 hx
      · rw [hxd, ← mul_assoc, inv_mul_cancel, one_mul]
        exact hd⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    by_cases ha : (a : G) ∈ D <;> by_cases hb : (b : G) ∈ D
    · simpa [f, ha, hb] using hab
    · simp [f, ha, hb] at hab
    · simp [f, ha, hb] at hab
    · simpa [f, ha, hb] using hab
  have := Nat.card_le_card_of_injective f hf
  rw [Nat.card_sum] at this
  omega

omit [Finite G] in
theorem Yrel.conj_shift {u : G} {l : ℤ} (r : Yrel c u y' l) (a m : ℤ) :
    (c ^ a)⁻¹ * (y' * c ^ m) * c ^ a = y' * c ^ (m + 2 * a) := by
  have h1 : (c ^ a)⁻¹ * y' = y' * c ^ a := by
    have := r.inv_conj_zpow_c (-a)
    rw [neg_neg] at this
    calc (c ^ a)⁻¹ * y' = y' * (y'⁻¹ * c ^ (-a) * y') := by rw [← zpow_neg]; group
      _ = y' * c ^ a := by rw [this]
  calc (c ^ a)⁻¹ * (y' * c ^ m) * c ^ a = ((c ^ a)⁻¹ * y') * c ^ m * c ^ a := by group
    _ = y' * c ^ (m + 2 * a) := by
        rw [h1, mul_assoc, mul_assoc, ← zpow_add, ← zpow_add]
        congr 2
        ring

namespace Q8Cfg

omit [Finite G] in
theorem conj_cz_eq (h : Q8Cfg D c) (g : G) : g * cz c * g⁻¹ = cz c := by
  have := h.central g
  calc g * cz c * g⁻¹ = cz c * g * g⁻¹ := by rw [this]
    _ = cz c := by group

omit [Finite G] in
theorem Th_y_c (_h : Q8Cfg D c) {u : G} {l : ℤ} (r : Yrel c u y' l) (hl : Odd l) (hy : Th c y')
    (i : ℤ) : Th c (y' * c ^ i) := by
  have hu : Th c (y' * c ^ l) := by
    have := Th_conj hy u⁻¹
    rwa [inv_inv, r.u_conj_y] at this
  rcases Int.even_or_odd i with ⟨a, ha⟩ | ⟨a, ha⟩
  · have := Th_conj hy (c ^ a)
    rw [← r.y_c_eq a] at this
    rwa [show i = 2 * a by omega]
  · obtain ⟨b, hb⟩ := hl
    have := Th_conj hu (c ^ (a - b))
    have e : (c ^ (a - b))⁻¹ * (y' * c ^ l) * c ^ (a - b) = y' * c ^ i := by
      rw [r.conj_shift]
      congr 2
      omega
    rwa [e] at this

theorem Th_inter_N_le (h : Q8Cfg D c) {S : Subgroup G} (hS : IsSylowOf 2 S ⊤) (hDS : D ≤ S)
    {u : G} (hu : u ∈ D) (huK : u ∉ zpowers c) {l : ℤ} (r : Yrel c u y' l) (hl : Odd l)
    (hy : Th c y') (hyD : y' ∉ D) {y'' : G} (hy''S : y'' ∈ S) (hy'' : Th c y'')
    (hQN : ∀ q ∈ Qsub D y' hN hsq, y'' * q * y''⁻¹ ∈ Qsub D y' hN hsq) :
    y'' ∈ Qsub D y' hN hsq := by
  by_contra hnQ
  have hSN := h.le_normalizer hS.isPGroup hDS
  have hN'' : y'' ∈ normalizer (D : Set G) := hSN hy''S
  have hy''D : y'' ∉ D := fun hD => hnQ (D_le_Qsub hD)
  obtain ⟨l'', hl''⟩ := conj_refl h hN'' hu huK
  obtain ⟨hinv'', hodd''⟩ := struct_inv h hS hDS hy''S hy'' hy''D hu huK hl''
  have r'' : Yrel c u y'' l'' :=
    ⟨hinv'', hl'', Th_sq h hy'', (refl_data h hu huK).1, (refl_data h hu huK).2⟩
  have hx : y'' * y' * y''⁻¹ ∈ Qsub D y' hN hsq := hQN y' y_mem_Qsub
  have hxsq : (y'' * y' * y''⁻¹) * (y'' * y' * y''⁻¹) = cz c := by
    rw [show y'' * y' * y''⁻¹ * (y'' * y' * y''⁻¹) = y'' * (y' * y') * y''⁻¹ by group, r.sq]
    exact h.conj_cz_eq y''
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℤ, y'' * y' * y''⁻¹ = y' * c ^ ρ := by
    rcases hx with hxD | ⟨d, hd, hxd⟩
    · exfalso
      have hxK := sq_cz_mem_K h hxD hxsq
      apply hyD
      have := conj_K' h hN'' hxK
      rw [show y''⁻¹ * (y'' * y' * y''⁻¹) * y'' = y' by group] at this
      exact (zpowers_le.mpr h.mem) this
    · rcases refl_cases h hu huK hd with hK | ⟨i, hi⟩
      · obtain ⟨i, hi⟩ := mem_zpowers_iff.mp hK
        exact ⟨i, by rw [hxd, ← hi]⟩
      · exfalso
        rw [hxd, hi] at hxsq
        have h1 := r.sq_y_c_u i
        rw [mul_assoc y' (c ^ i) u] at h1
        have h2 : cz c * c ^ (l - 2 * i) = cz c := h1.symm.trans hxsq
        have h3 : c ^ (l - 2 * i) = 1 := mul_left_cancel (h2.trans (mul_one (cz c)).symm)
        obtain ⟨b, hb⟩ := hl
        have h4 : c = 1 :=
          eq_one_of_zpow_odd_K h (mem_zpowers c) (⟨b - i, by omega⟩ : Odd (l - 2 * i)) h3
        exact h.c_mul_c_ne_one (by rw [h4, one_mul])
  have hyQ : y' ∈ Qsub D y' hN hsq := y_mem_Qsub
  rcases Int.even_or_odd ρ with ⟨a, ha⟩ | ⟨a, ha⟩
  · have hx₀ : Th c (y' * c ^ a) := Th_y_c h r hl hy a
    have hmem : y' * c ^ a ∈ Qsub D y' hN hsq := Or.inr ⟨c ^ a, zpow_mem h.mem a, rfl⟩
    have hcomm : (y' * c ^ a) * y'' = y'' * (y' * c ^ a) := by
      have : y'' * (y' * c ^ a) * y''⁻¹ = y' * c ^ a := by
        calc y'' * (y' * c ^ a) * y''⁻¹ = (y'' * y' * y''⁻¹) * (y'' * c ^ a * y''⁻¹) := by group
          _ = (y' * c ^ ρ) * c ^ (-a) := by rw [hρ, r''.conj_zpow_c]
          _ = y' * c ^ (ρ + -a) := by rw [mul_assoc, ← zpow_add]
          _ = y' * c ^ a := by rw [show ρ + -a = a by omega]
      exact (mul_inv_eq_iff_eq_mul.mp this).symm
    rcases cc h hS hDS hx₀ hy'' hcomm with e | e
    · exact hnQ (by rw [← e]; exact hmem)
    · have : y'' = (y' * c ^ a)⁻¹ := by rw [e, inv_inv]
      exact hnQ (by rw [this]; exact inv_mem hmem)
  · obtain ⟨b'', hb''⟩ := hodd''
    obtain ⟨b, hb⟩ := hl
    set i : ℤ := a + b'' + 1 with hi
    have hcomm : y'' * (y' * c ^ i * u) * y''⁻¹ = y' * c ^ i * u := by
      calc y'' * (y' * c ^ i * u) * y''⁻¹
          = (y'' * y' * y''⁻¹) * (y'' * c ^ i * y''⁻¹) * (y'' * u * y''⁻¹) := by group
        _ = (y' * c ^ ρ) * c ^ (-i) * (c ^ l'' * u) := by rw [hρ, r''.conj_zpow_c, hl'']
        _ = y' * c ^ (ρ + -i + l'') * u := by group
        _ = y' * c ^ i * u := by rw [show ρ + -i + l'' = i by omega]
    have hsq' : (y' * c ^ i * u) * (y' * c ^ i * u) = cz c * c ^ (l - 2 * i) := r.sq_y_c_u i
    have hc2 : y'' * (cz c * c ^ (l - 2 * i)) * y''⁻¹ = cz c * c ^ (l - 2 * i) := by
      rw [← hsq']
      calc y'' * ((y' * c ^ i * u) * (y' * c ^ i * u)) * y''⁻¹
          = (y'' * (y' * c ^ i * u) * y''⁻¹) * (y'' * (y' * c ^ i * u) * y''⁻¹) := by group
        _ = (y' * c ^ i * u) * (y' * c ^ i * u) := by rw [hcomm]
    have hc3 : y'' * (cz c * c ^ (l - 2 * i)) * y''⁻¹ = cz c * c ^ (-(l - 2 * i)) := by
      calc y'' * (cz c * c ^ (l - 2 * i)) * y''⁻¹
          = (y'' * cz c * y''⁻¹) * (y'' * c ^ (l - 2 * i) * y''⁻¹) := by group
        _ = cz c * c ^ (-(l - 2 * i)) := by rw [h.conj_cz_eq, r''.conj_zpow_c]
    have h4 : c ^ (l - 2 * i) = c ^ (-(l - 2 * i)) := mul_left_cancel (hc2.symm.trans hc3)
    have h5 : c ^ (2 * (l - 2 * i)) = 1 := by
      rw [show 2 * (l - 2 * i) = (l - 2 * i) - (-(l - 2 * i)) by ring, zpow_sub, ← h4,
        mul_inv_cancel]
    have h6 : (c ^ (2 : ℤ)) ^ (l - 2 * i) = 1 := by rw [← zpow_mul]; exact h5
    have h7 : c ^ (2 : ℤ) = 1 :=
      eq_one_of_zpow_odd_K h (zpow_mem (mem_zpowers c) 2)
        (⟨b - i, by omega⟩ : Odd (l - 2 * i)) h6
    exact h.c_mul_c_ne_one (by rw [← zpow_two]; exact h7)

theorem mem_normalizer_of_forall' {Q : Subgroup G} {x : G} (hx : ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) :
    x ∈ normalizer (Q : Set G) := by
  have hmap : Q.map (MulAut.conj x).toMonoidHom = Q := by
    refine eq_of_le_of_card_ge ?_ (card_map_of_injective (MulAut.conj x).injective).ge
    rintro _ ⟨q, hq, rfl⟩
    simpa using hx q hq
  exact mem_normalizer_iff_map_conj_eq.mpr hmap

structure Setup (h : Q8Cfg D c) (S : Subgroup G) (y' u : G) (l : ℤ) : Prop where
  hS : IsSylowOf 2 S ⊤
  hDS : D ≤ S
  hu : u ∈ D
  huK : u ∉ zpowers c
  hyS : y' ∈ S
  hy : Th c y'
  hyD : y' ∉ D
  r : Yrel c u y' l
  hl : Odd l

namespace Setup

variable {h : Q8Cfg D c} {S : Subgroup G} {y' u : G} {l : ℤ} (hs : Setup h S y' u l)
include hs

theorem le_norm : S ≤ normalizer (D : Set G) := h.le_normalizer hs.hS.isPGroup hs.hDS

theorem y_norm : y' ∈ normalizer (D : Set G) := hs.le_norm hs.hyS

omit [Finite G] in
theorem y_sq : y' * y' ∈ D := by
  rw [hs.r.sq]
  exact cz_mem h.mem

@[expose] def Q : Subgroup G := Qsub D y' hs.y_norm hs.y_sq

theorem mem_Q {x : G} : x ∈ hs.Q ↔ x ∈ D ∨ ∃ d ∈ D, x = y' * d := Iff.rfl

theorem D_le_Q : D ≤ hs.Q := D_le_Qsub

theorem y_mem_Q : y' ∈ hs.Q := y_mem_Qsub

theorem Q_le_S : hs.Q ≤ S := Qsub_le hs.hDS hs.hyS

theorem card_Q : Nat.card hs.Q ≤ 2 * Nat.card D := card_Qsub_le

theorem Th_N_le {y'' : G} (hy''S : y'' ∈ S) (hy'' : Th c y'')
    (hQN : ∀ q ∈ hs.Q, y'' * q * y''⁻¹ ∈ hs.Q) : y'' ∈ hs.Q :=
  Th_inter_N_le h hs.hS hs.hDS hs.hu hs.huK hs.r hs.hl hs.hy hs.hyD hy''S hy'' hQN

theorem weak_Q {a : G} (ha : ∀ q ∈ hs.Q, a⁻¹ * q * a ∈ S ⊓ normalizer (hs.Q : Set G)) :
    ∀ q ∈ hs.Q, a⁻¹ * q * a ∈ hs.Q := by
  intro q hq
  have hDa : ∀ d ∈ D, a⁻¹ * d * a ∈ D := fun d hd =>
    h.weak_closed hs.hS.isPGroup hs.hDS (g := a)
      (fun d' hd' => (mem_inf.mp (ha d' (hs.D_le_Q hd'))).1) hd
  have hya := ha y' hs.y_mem_Q
  have hy'a : a⁻¹ * y' * a ∈ hs.Q :=
    hs.Th_N_le (mem_inf.mp hya).1 (Th_conj hs.hy a) fun q hq' =>
      (mem_normalizer_iff.mp (mem_inf.mp hya).2 q).mp hq'
  rcases hq with hqD | ⟨d, hd, rfl⟩
  · exact hs.D_le_Q (hDa q hqD)
  · have : a⁻¹ * (y' * d) * a = (a⁻¹ * y' * a) * (a⁻¹ * d * a) := by group
    rw [this]
    exact mul_mem hy'a (hs.D_le_Q (hDa d hd))

theorem S_le_norm_Q : S ≤ normalizer (hs.Q : Set G) := by
  by_contra hnot
  have hlt : S ⊓ normalizer (hs.Q : Set G) < S := by
    refine lt_of_le_of_ne inf_le_left fun h' => hnot ?_
    intro x hx
    have : x ∈ S ⊓ normalizer (hs.Q : Set G) := by rw [h']; exact hx
    exact (mem_inf.mp this).2
  obtain ⟨x, hxS, hxT, hxN⟩ := FooteLit.exists_mem_normalizer_of_lt hs.hS.isPGroup hlt
  apply hxT
  refine mem_inf.mpr ⟨hxS, ?_⟩
  refine mem_normalizer_of_forall' fun q hq => ?_
  have hqT : q ∈ S ⊓ normalizer (hs.Q : Set G) :=
    mem_inf.mpr ⟨hs.Q_le_S hq, Subgroup.le_normalizer hq⟩
  have h1 : ∀ q' ∈ hs.Q, (x⁻¹)⁻¹ * q' * x⁻¹ ∈ S ⊓ normalizer (hs.Q : Set G) := fun q' hq' => by
    have hq'T : q' ∈ S ⊓ normalizer (hs.Q : Set G) :=
      mem_inf.mpr ⟨hs.Q_le_S hq', Subgroup.le_normalizer hq'⟩
    rw [inv_inv]
    exact (mem_normalizer_iff.mp hxN q').mp hq'T
  have := hs.weak_Q (a := x⁻¹) h1 q hq
  rwa [inv_inv] at this

theorem Th_le_Q {y'' : G} (hy''S : y'' ∈ S) (hy'' : Th c y'') : y'' ∈ hs.Q :=
  hs.Th_N_le hy''S hy'' fun q hq => (mem_normalizer_iff.mp (hs.S_le_norm_Q hy''S) q).mp hq

end Setup

end Q8Cfg

end CFSG.ComponentClassification.Foote5.HallGen
