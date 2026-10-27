module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ClQuadGroup
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ClLambdaDecomp
public import CFSG.HardMathSupport.Cooperstein.Proving.EvenWFixNormalizedOfRealized

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm

theorem dbl_mul {α : Type*} [DecidableEq α] {a b c d : α} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    swap a b * swap c d * (swap a c * swap b d) = swap a d * swap b c := by
  ext i
  simp only [Perm.mul_apply, swap_apply_def]
  split_ifs <;> simp_all

abbrev v0 : Perm (Fin 4) := swap 0 1 * swap 2 3

abbrev IsD8 (a : Perm (Fin 4)) : Prop := a * v0 = v0 * a

theorem isD8_mul : ∀ a b : Perm (Fin 4), IsD8 a → IsD8 b → IsD8 (a * b) := by decide

theorem isD8_inv : ∀ a : Perm (Fin 4), IsD8 a → IsD8 a⁻¹ := by decide

theorem isD8_conj : ∀ g a : Perm (Fin 4), IsD8 g → IsD8 a → IsD8 (g * a * g⁻¹) := by decide

theorem isD8_pow4 : ∀ a : Perm (Fin 4), IsD8 a → a * a * a * a = 1 := by decide

theorem isD8_of_conj : ∀ g : Perm (Fin 4), g * v0 * g⁻¹ ≠ swap 0 2 * swap 1 3 →
    g * v0 * g⁻¹ ≠ swap 0 3 * swap 1 2 → IsD8 g := by decide

theorem isD8_swap01 : IsD8 (swap 0 1 : Perm (Fin 4)) := by decide

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 2000 in
theorem isD8_conj_small : ∀ g : Perm (Fin 4),
    ((¬ ∃ x y z : Fin 4, x ≠ y ∧ y ≠ z ∧ z ≠ x ∧ g x = y ∧ g y = z ∧ g z = x) ∧
      (∀ a b : Fin 4, a ≠ b → g ≠ swap a b) ∧
      g ≠ swap 0 2 * swap 1 3 ∧ g ≠ swap 0 3 * swap 1 2 ∧
      g * g ≠ swap 0 2 * swap 1 3 ∧ g * g ≠ swap 0 3 * swap 1 2) →
    ∀ a : Perm (Fin 4), IsD8 a → a * g * a⁻¹ = g ∨ a * g * a⁻¹ = g⁻¹ := by
  decide

section Frame

variable {Ω : Type*} {e : Fin 4 → Ω}

theorem d8_apply_inv_self (σ : Perm Ω) (x : Ω) : σ (σ⁻¹ x) = x := σ.apply_symm_apply x

theorem d8_inv_apply_self (σ : Perm Ω) (x : Ω) : σ⁻¹ (σ x) = x := σ.symm_apply_apply x

theorem d8_mem_range_of_pure {p : Perm Ω} (hp : ∀ i, i ∉ Set.range e → p i = i) (i : Fin 4) :
    p (e i) ∈ Set.range e := by
  by_contra hn
  exact hn ⟨i, (p.injective (hp _ hn)).symm⟩

theorem d8_exists_frame (he : Function.Injective e) {p : Perm Ω}
    (hp : ∀ i, p (e i) ∈ Set.range e) : ∃ g : Perm (Fin 4), ∀ i, p (e i) = e (g i) := by
  simp only [Set.mem_range] at hp
  choose g hg using hp
  have hinj : Function.Injective g := fun i j hij => by
    have : p (e i) = p (e j) := by rw [← hg i, ← hg j, hij]
    exact he (p.injective this)
  exact ⟨Equiv.ofBijective g (Finite.injective_iff_bijective.1 hinj), fun i => (hg i).symm⟩

theorem d8_frame_inv {p : Perm Ω} {g : Perm (Fin 4)} (h : ∀ i, p (e i) = e (g i)) (i : Fin 4) :
    p⁻¹ (e i) = e (g⁻¹ i) := by
  rw [Perm.inv_eq_iff_eq, h, d8_apply_inv_self]

theorem d8_frame_mul {p q : Perm Ω} {g h : Perm (Fin 4)} (hp : ∀ i, p (e i) = e (g i))
    (hq : ∀ i, q (e i) = e (h i)) (i : Fin 4) : (p * q) (e i) = e ((g * h) i) := by
  rw [Perm.mul_apply, hq, hp]
  rfl

theorem d8_pure_mul {p q : Perm Ω} (hp : ∀ i, i ∉ Set.range e → p i = i)
    (hq : ∀ i, i ∉ Set.range e → q i = i) : ∀ i, i ∉ Set.range e → (p * q) i = i := by
  intro i hi
  rw [Perm.mul_apply, hq i hi, hp i hi]

theorem d8_pure_inv {p : Perm Ω} (hp : ∀ i, i ∉ Set.range e → p i = i) :
    ∀ i, i ∉ Set.range e → p⁻¹ i = i :=
  fun i hi => Perm.inv_eq_iff_eq.2 (hp i hi).symm

theorem d8_pure_conj {h p : Perm Ω} (hh : ∀ i, h (e i) ∈ Set.range e)
    (hp : ∀ i, i ∉ Set.range e → p i = i) : ∀ i, i ∉ Set.range e → (h * p * h⁻¹) i = i := by
  intro x hx
  have hx' : h⁻¹ x ∉ Set.range e := by
    rintro ⟨j, hj⟩
    apply hx
    obtain ⟨k, hk⟩ := hh j
    exact ⟨k, by rw [hk, hj, d8_apply_inv_self]⟩
  rw [Perm.mul_apply, Perm.mul_apply, hp _ hx', d8_apply_inv_self]

theorem d8_commute_of_fix_of_pure {κ u : Perm Ω} (hκ : ∀ i, κ (e i) = e i)
    (hu : ∀ i, i ∉ Set.range e → u i = i) : u * κ = κ * u := by
  ext x
  simp only [Perm.mul_apply]
  by_cases hx : x ∈ Set.range e
  · obtain ⟨i, rfl⟩ := hx
    obtain ⟨j, hj⟩ := d8_mem_range_of_pure hu i
    rw [hκ, ← hj, hκ]
  · have hκx : κ x ∉ Set.range e := by
      rintro ⟨j, hj⟩
      exact hx ⟨j, κ.injective ((hκ j).trans hj)⟩
    rw [hu x hx, hu _ hκx]

@[expose] def d8Frame (e : Fin 4 → Ω) : Subgroup (Perm Ω) where
  carrier := {u | (∀ i, i ∉ Set.range e → u i = i) ∧
    ∃ a : Perm (Fin 4), IsD8 a ∧ ∀ i, u (e i) = e (a i)}
  mul_mem' := by
    rintro u v ⟨hu, a, ha, hua⟩ ⟨hv, b, hb, hvb⟩
    exact ⟨d8_pure_mul hu hv, a * b, isD8_mul a b ha hb, d8_frame_mul hua hvb⟩
  one_mem' := ⟨fun _ _ => rfl, 1, by decide, fun _ => rfl⟩
  inv_mem' := by
    rintro u ⟨hu, a, ha, hua⟩
    exact ⟨d8_pure_inv hu, a⁻¹, isD8_inv a ha, d8_frame_inv hua⟩

theorem mem_d8Frame {u : Perm Ω} : u ∈ d8Frame e ↔
    (∀ i, i ∉ Set.range e → u i = i) ∧ ∃ a : Perm (Fin 4), IsD8 a ∧ ∀ i, u (e i) = e (a i) :=
  Iff.rfl

theorem isPGroup_d8Frame [DecidableEq Ω] (e : Fin 4 → Ω) : IsPGroup 2 (d8Frame e) := by
  rintro ⟨u, hu⟩
  obtain ⟨hu1, a, ha, hua⟩ := hu
  refine ⟨2, Subtype.ext ?_⟩
  show u ^ 2 ^ 2 = 1
  have h4 : u ^ 2 ^ 2 = u * u * u * u := by
    simp only [show (2 : ℕ) ^ 2 = 4 from rfl, pow_succ, pow_zero, one_mul]
  rw [h4]
  refine eq_of_frame (pure_mul' hu1 hu1 hu1 hu1) (fun _ _ => rfl) fun i => ?_
  rw [d8_frame_mul (d8_frame_mul (d8_frame_mul hua hua) hua) hua, isD8_pow4 a ha]
  rfl
where
  pure_mul' {p : Perm Ω} (h1 : ∀ i, i ∉ Set.range e → p i = i) (h2 : ∀ i, i ∉ Set.range e → p i = i)
      (h3 : ∀ i, i ∉ Set.range e → p i = i) (h4 : ∀ i, i ∉ Set.range e → p i = i) :
      ∀ i, i ∉ Set.range e → (p * p * p * p) i = i :=
    d8_pure_mul (d8_pure_mul (d8_pure_mul h1 h2) h3) h4

end Frame

section Main

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem swap_mem_of_d8 {f0 : Fin 4 → Ω} (hf0 : Function.Injective f0) (ω : Perm Ω)
    (hωω : ∀ x, ω (ω x) = x) (W Ss R : Subgroup (Perm Ω)) (hW2 : IsPGroup 2 W) (hWS : W ≤ Ss)
    (hSR : Ss ≤ R) (hAltR : alternatingGroup Ω ≤ R)
    (hωsw : ∀ y, ω y ≠ y → swap y (ω y) ∈ W)
    (hωfix : ∀ w ∈ W, ∀ y, ω y ≠ y → w y = y ∨ w y = ω y)
    (hunm : ∀ y, ω y = y → ∀ q, y ≠ q → swap y q ∉ W)
    (hmemR : ∀ q, q ∈ Set.range f0 ↔ ω q = q) (hex : ∃ p, ω p ≠ p)
    (hD1 : swap (f0 0) (f0 1) * swap (f0 2) (f0 3) ∈ W)
    (hv1 : swap (f0 0) (f0 2) * swap (f0 1) (f0 3) ∉ W)
    (hv2 : swap (f0 0) (f0 3) * swap (f0 1) (f0 2) ∉ W)
    (hLT : ∀ U : Subgroup (Perm Ω), U ≤ Subgroup.normalizer (W : Set (Perm Ω)) → IsPGroup 2 U →
      U ≤ R → (∀ h ∈ Subgroup.normalizer (W : Set (Perm Ω)), h ∈ R → ∀ u ∈ U, h * u * h⁻¹ ∈ U) →
      U ≤ Ss) :
    swap (f0 0) (f0 1) ∈ Ss := by
  classical
  have hsubΛ : ∀ i, ω (f0 i) = f0 i := fun i => (hmemR _).1 ⟨i, rfl⟩
  have hpres : ∀ h ∈ Subgroup.normalizer (W : Set (Perm Ω)), ∀ i, h (f0 i) ∈ Set.range f0 := by
    intro h hh i
    rw [hmemR]
    by_contra hne
    have h1 : h⁻¹ * swap (h (f0 i)) (ω (h (f0 i))) * h⁻¹⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.1 (inv_mem hh) _).1 (hωsw _ hne)
    rw [← swap_apply_apply, d8_inv_apply_self] at h1
    refine hunm (f0 i) (hsubΛ i) (h⁻¹ (ω (h (f0 i)))) (fun h' => hne ?_) h1
    have := congrArg h h'
    rw [d8_apply_inv_self] at this
    exact this.symm
  have hv0frame : ∀ i, (swap (f0 0) (f0 1) * swap (f0 2) (f0 3)) (f0 i) = f0 (v0 i) :=
    fun i => swapProd_frame hf0 0 1 2 3 i
  have hv0off : ∀ i, i ∉ Set.range f0 → (swap (f0 0) (f0 1) * swap (f0 2) (f0 3)) i = i :=
    fun i hi => swapProd_off 0 1 2 3 hi
  have hhD8 : ∀ h ∈ Subgroup.normalizer (W : Set (Perm Ω)), ∃ g : Perm (Fin 4), IsD8 g ∧
      ∀ i, h (f0 i) = f0 (g i) := by
    intro h hh
    obtain ⟨g, hg⟩ := d8_exists_frame hf0 (hpres h hh)
    have hW' : h * (swap (f0 0) (f0 1) * swap (f0 2) (f0 3)) * h⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.1 hh _).1 hD1
    have hpure := d8_pure_conj (hpres h hh) hv0off
    have hfr : ∀ i, (h * (swap (f0 0) (f0 1) * swap (f0 2) (f0 3)) * h⁻¹) (f0 i) =
        f0 ((g * v0 * g⁻¹) i) :=
      d8_frame_mul (d8_frame_mul hg hv0frame) (d8_frame_inv hg)
    refine ⟨g, isD8_of_conj g (fun hc => hv1 ?_) (fun hc => hv2 ?_), hg⟩
    · have : h * (swap (f0 0) (f0 1) * swap (f0 2) (f0 3)) * h⁻¹ =
          swap (f0 0) (f0 2) * swap (f0 1) (f0 3) :=
        eq_of_frame hpure (fun i hi => swapProd_off 0 2 1 3 hi)
          (fun i => by rw [hfr, hc, swapProd_frame hf0])
      rwa [this] at hW'
    · have : h * (swap (f0 0) (f0 1) * swap (f0 2) (f0 3)) * h⁻¹ =
          swap (f0 0) (f0 3) * swap (f0 1) (f0 2) :=
        eq_of_frame hpure (fun i hi => swapProd_off 0 3 1 2 hi)
          (fun i => by rw [hfr, hc, swapProd_frame hf0])
      rwa [this] at hW'
  have hfr : ∀ (q : Perm Ω) (gq : Perm (Fin 4)), (∀ i, i ∉ Set.range f0 → q i = i) →
      (∀ i, q (f0 i) = f0 (gq i)) → ∀ a1 b1 c1 d1 : Fin 4, gq = swap a1 b1 * swap c1 d1 →
      q = swap (f0 a1) (f0 b1) * swap (f0 c1) (f0 d1) :=
    fun q gq hq hqg a1 b1 c1 d1 hgs => eq_of_frame hq (fun i hi => swapProd_off a1 b1 c1 d1 hi)
      (fun i => by rw [hqg, hgs, swapProd_frame hf0])
  have hpureW : ∀ p ∈ W, (∀ i, i ∉ Set.range f0 → p i = i) →
      ∀ u ∈ d8Frame f0, u * p * u⁻¹ ∈ W := by
    intro p hpW hp u hu
    obtain ⟨hu1, a, ha, hua⟩ := hu
    obtain ⟨g, hg⟩ := d8_exists_frame hf0 (d8_mem_range_of_pure hp)
    have c1 : ¬ ∃ x y z : Fin 4, x ≠ y ∧ y ≠ z ∧ z ≠ x ∧ g x = y ∧ g y = z ∧ g z = x := by
      rintro ⟨a1, b1, c1', hab, hbc, hca, e1, e2, e3⟩
      exact not_isPGroup_of_threeCycle hW2 hpW (fun h => hab (hf0 h)) (fun h => hbc (hf0 h))
        (fun h => hca (hf0 h)) (by rw [hg, e1]) (by rw [hg, e2]) (by rw [hg, e3])
    have c2 : ∀ a1 b1 : Fin 4, a1 ≠ b1 → g ≠ swap a1 b1 := by
      intro a1 b1 hab hgs
      have hpeq : p = swap (f0 a1) (f0 b1) :=
        eq_of_frame hp (fun i hi => swap_apply_of_ne_of_ne (fun h => hi ⟨a1, h.symm⟩)
          (fun h => hi ⟨b1, h.symm⟩)) (fun i => by rw [hg, hgs, swap_frame hf0])
      exact hunm (f0 a1) (hsubΛ a1) (f0 b1) (fun h => hab (hf0 h)) (hpeq ▸ hpW)
    have c3 : g ≠ swap 0 2 * swap 1 3 := fun hgs => hv1 (hfr p g hp hg 0 2 1 3 hgs ▸ hpW)
    have c3' : g ≠ swap 0 3 * swap 1 2 := fun hgs => hv2 (hfr p g hp hg 0 3 1 2 hgs ▸ hpW)
    have hpp : p * p ∈ W := W.mul_mem hpW hpW
    have c4 : g * g ≠ swap 0 2 * swap 1 3 := fun hgs =>
      hv1 (hfr (p * p) (g * g) (d8_pure_mul hp hp) (d8_frame_mul hg hg) 0 2 1 3 hgs ▸ hpp)
    have c4' : g * g ≠ swap 0 3 * swap 1 2 := fun hgs =>
      hv2 (hfr (p * p) (g * g) (d8_pure_mul hp hp) (d8_frame_mul hg hg) 0 3 1 2 hgs ▸ hpp)
    have hconj := d8_frame_mul (d8_frame_mul hua hg) (d8_frame_inv hua)
    have hpure' := d8_pure_conj (d8_mem_range_of_pure hu1) hp
    rcases isD8_conj_small g ⟨c1, c2, c3, c3', c4, c4'⟩ a ha with hc | hc
    · have hup : u * p * u⁻¹ = p :=
        eq_of_frame hpure' hp (fun i => by rw [hconj, hc, hg])
      rw [hup]
      exact hpW
    · have hup : u * p * u⁻¹ = p⁻¹ :=
        eq_of_frame hpure' (d8_pure_inv hp) (fun i => by rw [hconj, hc, d8_frame_inv hg])
      rw [hup]
      exact W.inv_mem hpW
  have hUN : d8Frame f0 ≤ Subgroup.normalizer (W : Set (Perm Ω)) := by
    intro u hu
    refine CFSG.HardMathSupport.Cooperstein.Proving.mem_normalizer_of_conj_le fun w hw => ?_
    obtain ⟨κ, hκ, p, hp, rfl⟩ := Classif.eq_matchedK_mul hωω hωsw hωfix hw
    obtain ⟨hpW, hpfix⟩ := Classif.mem_matchedFixed.1 hp
    have hpure : ∀ i, i ∉ Set.range f0 → p i = i :=
      fun i hi => hpfix i (fun h => hi ((hmemR i).2 h))
    have hκfix : ∀ i, κ (f0 i) = f0 i :=
      fun i => Classif.matchedK_fix hωω hκ ((hmemR _).1 ⟨i, rfl⟩)
    have hκW : κ ∈ W := (Subgroup.closure_le W).2 (by rintro _ ⟨q, hq, rfl⟩; exact hωsw q hq) hκ
    have hcomm := d8_commute_of_fix_of_pure hκfix hu.1
    have hsplit : u * (κ * p) * u⁻¹ = κ * (u * p * u⁻¹) := by
      calc u * (κ * p) * u⁻¹ = (u * κ) * p * u⁻¹ := by group
        _ = (κ * u) * p * u⁻¹ := by rw [hcomm]
        _ = κ * (u * p * u⁻¹) := by group
    rw [hsplit]
    exact W.mul_mem hκW (hpureW p hpW hpure u hu)
  obtain ⟨p0, hp0⟩ := hex
  have htp : swap p0 (ω p0) ∈ R := hSR (hWS (hωsw p0 hp0))
  have hUr : d8Frame f0 ≤ R := by
    intro u _
    rcases Int.units_eq_one_or (sign u) with h | h
    · exact hAltR (mem_alternatingGroup.2 h)
    · have hev : u * swap p0 (ω p0) ∈ alternatingGroup Ω := by
        rw [mem_alternatingGroup, Perm.sign_mul, h, sign_swap (fun e => hp0 e.symm)]
        decide
      have := R.mul_mem (hAltR hev) htp
      rwa [mul_assoc, swap_mul_self, mul_one] at this
  have hUnorm : ∀ h ∈ Subgroup.normalizer (W : Set (Perm Ω)), h ∈ R →
      ∀ u ∈ d8Frame f0, h * u * h⁻¹ ∈ d8Frame f0 := by
    intro h hh _ u hu
    obtain ⟨hu1, a, ha, hua⟩ := hu
    obtain ⟨g, hg1, hg⟩ := hhD8 h hh
    exact ⟨d8_pure_conj (hpres h hh) hu1, g * a * g⁻¹, isD8_conj g a hg1 ha,
      d8_frame_mul (d8_frame_mul hg hua) (d8_frame_inv hg)⟩
  have hle := hLT (d8Frame f0) hUN (isPGroup_d8Frame f0) hUr hUnorm
  exact hle ⟨fun i hi => swap_apply_of_ne_of_ne (fun h => hi ⟨0, h.symm⟩)
    (fun h => hi ⟨1, h.symm⟩), swap 0 1, isD8_swap01, fun i => swap_frame hf0 0 1 i⟩

end Main

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
