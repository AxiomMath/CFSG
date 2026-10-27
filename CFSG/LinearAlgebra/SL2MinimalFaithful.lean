module

public import CFSG.LinearAlgebra.SL2MinimalFaithfulZsigmondy
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.SL2MinimalFaithful

variable {J V : Type*} [Group J] [Group V]

@[expose] def fixedPoints (ρ : J →* MulAut V) (X : Subgroup J) : Subgroup V where
  carrier := {v | ∀ u ∈ X, ρ u v = v}
  one_mem' := fun u _ => map_one (ρ u)
  mul_mem' := fun {a b} ha hb u hu => by
    rw [map_mul, ha u hu, hb u hu]
  inv_mem' := fun {a} ha u hu => by
    rw [map_inv, ha u hu]

theorem mem_fixedPoints {ρ : J →* MulAut V} {X : Subgroup J} {v : V} :
    v ∈ fixedPoints ρ X ↔ ∀ u ∈ X, ρ u v = v :=
  Iff.rfl

theorem fixedPoints_anti {ρ : J →* MulAut V} {X Y : Subgroup J} (h : X ≤ Y) :
    fixedPoints ρ Y ≤ fixedPoints ρ X :=
  fun _ hv u hu => hv u (h hu)

theorem fixedPoints_inf (ρ : J →* MulAut V) (X Y : Subgroup J) :
    fixedPoints ρ X ⊓ fixedPoints ρ Y = fixedPoints ρ (X ⊔ Y) := by
  apply le_antisymm
  · rintro v ⟨hX, hY⟩
    have hle : X ⊔ Y ≤ (MulAction.stabilizer (MulAut V) v).comap ρ :=
      sup_le (fun u hu => hX u hu) (fun u hu => hY u hu)
    exact fun u hu => hle hu
  · exact le_inf (fixedPoints_anti le_sup_left) (fixedPoints_anti le_sup_right)

theorem map_fixedPoints_conj (ρ : J →* MulAut V) (X : Subgroup J) (g : J) :
    (fixedPoints ρ X).map (ρ g).toMonoidHom =
      fixedPoints ρ (X.map (MulAut.conj g).toMonoidHom) := by
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩ _ ⟨u, hu, rfl⟩
    change ρ (g * u * g⁻¹) (ρ g v) = ρ g v
    rw [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply, ← MulAut.mul_apply _ (ρ g⁻¹),
      ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply, hv u hu]
  · intro hw
    refine ⟨ρ g⁻¹ w, fun u hu => ?_, ?_⟩
    · have h1 := hw (g * u * g⁻¹) ⟨u, hu, rfl⟩
      rw [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply] at h1
      calc ρ u (ρ g⁻¹ w) = ρ g⁻¹ (ρ g (ρ u (ρ g⁻¹ w))) := by
            rw [← MulAut.mul_apply _ (ρ g⁻¹), ← map_mul, inv_mul_cancel, map_one,
              MulAut.one_apply]
        _ = ρ g⁻¹ w := by rw [h1]
    · change ρ g (ρ g⁻¹ w) = w
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]

theorem exists_dvd_pow_sub_pow [Finite V] {p d ℓ : ℕ} (hp : p.Prime) (hℓ : ℓ.Prime)
    (ρ : J →* MulAut V) {h : J} (hh : orderOf h = ℓ) (hρh : ρ h ≠ 1)
    (hV : Nat.card V = p ^ d) : ∃ e < d, ℓ ∣ p ^ d - p ^ e := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  let K := Subgroup.zpowers h
  let : MulAction K V := MulAction.compHom V (ρ.comp K.subtype)
  have hK : IsPGroup ℓ K := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hh, pow_one])
  have hset : (MulAction.fixedPoints K V) = (fixedPoints ρ K : Set V) := by
    ext v
    rw [MulAction.mem_fixedPoints]
    exact ⟨fun hv u hu => hv ⟨u, hu⟩, fun hv u => hv u u.2⟩
  have hmod := hK.card_modEq_card_fixedPoints V
  rw [hset] at hmod
  change Nat.card V ≡ Nat.card (fixedPoints ρ K) [MOD ℓ] at hmod
  obtain ⟨e, hed, hFe⟩ := (Nat.dvd_prime_pow hp).mp
    (hV ▸ Subgroup.card_subgroup_dvd_card (fixedPoints ρ K))
  have hlt : e < d := by
    refine lt_of_le_of_ne hed fun hde => hρh ?_
    have htop : fixedPoints ρ K = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (by rw [hFe, hV, hde])
    ext v
    have hv : v ∈ fixedPoints ρ K := htop ▸ Subgroup.mem_top v
    exact hv h (Subgroup.mem_zpowers h)
  refine ⟨e, hlt, ?_⟩
  rw [hFe, hV] at hmod
  exact (Nat.modEq_iff_dvd' (Nat.pow_le_pow_right hp.pos hlt.le)).mp hmod.symm

theorem not_dvd_pow_sq_sub_one {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) :
    ¬ p ∣ (p ^ f) ^ 2 - 1 := by
  intro h
  have h1 : p ∣ (p ^ f) ^ 2 := dvd_pow (dvd_pow_self p (by omega)) two_ne_zero
  have h2 : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow _ _ (Nat.pow_pos hp.pos)
  have h3 := Nat.dvd_sub h1 h
  rw [Nat.sub_sub_self h2] at h3
  exact hp.one_lt.ne' (Nat.dvd_one.mp h3)

theorem two_mul_le_of_injective [Finite J] [Finite V] {p f d : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hJ : p ^ f * ((p ^ f) ^ 2 - 1) ∣ Nat.card J)
    (hZ : 2 ≤ f → ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∣ p ^ (2 * f) - 1 ∧
      ∀ k : ℕ, 0 < k → k < 2 * f → ¬ ℓ ∣ p ^ k - 1)
    (ρ : J →* MulAut V) (hρ : Function.Injective ρ) (hV : Nat.card V = p ^ d) :
    2 * f ≤ d := by
  by_contra hd
  push Not at hd
  have hne : ∀ {h : J}, orderOf h ≠ 1 → ρ h ≠ 1 := by
    intro h hh h1
    apply hh
    rw [show h = 1 from hρ (by rw [h1, map_one]), orderOf_one]
  rcases Nat.lt_or_ge f 2 with hf1 | hf2
  · obtain rfl : f = 1 := by omega
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨h, hh⟩ := exists_prime_orderOf_dvd_card' p
      ((dvd_mul_right p _).trans (by simpa using hJ))
    obtain ⟨e, hed, hdvd⟩ := exists_dvd_pow_sub_pow hp hp ρ hh
      (hne (by rw [hh]; exact hp.one_lt.ne')) hV
    obtain rfl : d = 1 := by omega
    obtain rfl : e = 0 := by omega
    rw [pow_one, pow_zero] at hdvd
    have h2 := hp.two_le
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  · obtain ⟨ℓ, hℓ, hℓdvd, hprim⟩ := hZ hf2
    have : Fact ℓ.Prime := ⟨hℓ⟩
    have hℓJ : ℓ ∣ Nat.card J := by
      refine hℓdvd.trans (Dvd.dvd.trans ?_ hJ)
      rw [pow_mul', ← pow_mul, mul_comm f 2, pow_mul]
      exact dvd_mul_left _ _
    obtain ⟨h, hh⟩ := exists_prime_orderOf_dvd_card' ℓ hℓJ
    obtain ⟨e, hed, hdvd⟩ := exists_dvd_pow_sub_pow hp hℓ ρ hh
      (hne (by rw [hh]; exact hℓ.one_lt.ne')) hV
    have hfac : p ^ d - p ^ e = p ^ e * (p ^ (d - e) - 1) := by
      rw [Nat.mul_sub_one, ← pow_add, Nat.add_sub_cancel' hed.le]
    rw [hfac] at hdvd
    have hℓp : ¬ ℓ ∣ p ^ e := by
      intro h'
      have hℓp' : ℓ = p := (Nat.prime_dvd_prime_iff_eq hℓ hp).mp (hℓ.dvd_of_dvd_pow h')
      subst hℓp'
      have h1 : ℓ ∣ ℓ ^ (2 * f) := dvd_pow_self ℓ (by omega)
      have h2 : 1 ≤ ℓ ^ (2 * f) := Nat.one_le_pow _ _ hℓ.pos
      have h3 := Nat.dvd_sub h1 hℓdvd
      rw [Nat.sub_sub_self h2] at h3
      exact hℓ.one_lt.ne' (Nat.dvd_one.mp h3)
    exact hprim (d - e) (by omega) (by omega)
      ((Nat.Coprime.dvd_of_dvd_mul_left ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓp) hdvd))

@[expose] noncomputable def quotientAction (ρ : J →* MulAut V) (W₀ : Subgroup V) [W₀.Normal]
    (hW₀ : ∀ j, W₀.map (ρ j : V →* V) = W₀) : J →* MulAut (V ⧸ W₀) where
  toFun j := QuotientGroup.congr W₀ W₀ (ρ j) (hW₀ j)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H v => rw [QuotientGroup.congr_mk, map_one, MulAut.one_apply, MulAut.one_apply]
  map_mul' j k := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H v =>
      rw [MulAut.mul_apply, QuotientGroup.congr_mk, QuotientGroup.congr_mk,
        QuotientGroup.congr_mk, map_mul, MulAut.mul_apply]

theorem quotientAction_mk (ρ : J →* MulAut V) (W₀ : Subgroup V) [W₀.Normal]
    (hW₀ : ∀ j, W₀.map (ρ j : V →* V) = W₀) (j : J) (v : V) :
    quotientAction ρ W₀ hW₀ j (v : V ⧸ W₀) = ((ρ j v : V) : V ⧸ W₀) :=
  QuotientGroup.congr_mk W₀ W₀ (ρ j) (hW₀ j) v

theorem pow_apply_of_mem (ρ : J →* MulAut V) {j : J} {v c : V}
    (hc : c ∈ fixedPoints ρ ⊤) (hjv : ρ j v = v * c) (k : ℕ) : ρ (j ^ k) v = v * c ^ k := by
  induction k with
  | zero => rw [pow_zero, map_one, MulAut.one_apply, pow_zero, mul_one]
  | succ k ih =>
    rw [pow_succ', map_mul, MulAut.mul_apply, ih, map_mul, hjv, map_pow,
      hc j (Subgroup.mem_top j), mul_assoc, ← pow_succ']

theorem card_fixedPoints_le_of_primitive [Finite J] [Finite V] {p f : ℕ} (hp : p.Prime)
    (hf : 1 ≤ f) (hZ : 2 ≤ f → ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∣ p ^ (2 * f) - 1 ∧
      ∀ k : ℕ, 0 < k → k < 2 * f → ¬ ℓ ∣ p ^ k - 1)
    (hJ : Nat.card J = p ^ f * ((p ^ f) ^ 2 - 1))
    (hcomm : ∀ v w : V, v * w = w * v) (hexp : ∀ v : V, v ^ p = 1)
    (hV : Nat.card V = (p ^ f) ^ 2) (ρ : J →* MulAut V) (hρ : Function.Injective ρ)
    {Q Qs : Subgroup J} (hQ : Nat.card Q = p ^ f) (hQs : Nat.card Qs = p ^ f)
    (hinf : Q ⊓ Qs = ⊥) (hsup : Q ⊔ Qs = ⊤) :
    Nat.card (fixedPoints ρ Q) ≤ p ^ f := by
  have : Fact p.Prime := ⟨hp⟩
  have hq0 : 0 < p ^ f := Nat.pow_pos hp.pos
  have hindex : ∀ {P : Subgroup J}, Nat.card P = p ^ f → ¬ p ∣ P.index := by
    intro P hP
    have h := P.card_mul_index
    rw [hP, hJ] at h
    rw [Nat.eq_of_mul_eq_mul_left hq0 h]
    exact not_dvd_pow_sq_sub_one hp hf
  let SQ : Sylow p J := (IsPGroup.of_card hQ).toSylow (hindex hQ)
  let SQs : Sylow p J := (IsPGroup.of_card hQs).toSylow (hindex hQs)
  have hSQ : (SQ : Subgroup J) = Q := rfl
  have hSQs : (SQs : Subgroup J) = Qs := rfl
  have hW₀ : fixedPoints ρ ⊤ = ⊥ := by
    by_contra hne
    set W₀ := fixedPoints ρ ⊤ with hW₀def
    have : W₀.Normal :=
      ⟨fun n hn g => by rw [hcomm g n, mul_inv_cancel_right]; exact hn⟩
    have hmap : ∀ j, W₀.map (ρ j : V →* V) = W₀ := by
      intro j
      ext v
      constructor
      · rintro ⟨w, hw, rfl⟩
        change ρ j w ∈ W₀
        rw [hw j (Subgroup.mem_top j)]
        exact hw
      · intro hv
        exact ⟨v, hv, hv j (Subgroup.mem_top j)⟩
    set ρ' := quotientAction ρ W₀ hmap
    have hker : ∀ j, ρ' j = 1 → j ^ p = 1 := by
      intro j hj
      apply hρ
      rw [map_one]
      ext v
      have h1 := congrArg (fun φ : MulAut (V ⧸ W₀) => φ (v : V ⧸ W₀)) hj
      simp only [MulAut.one_apply] at h1
      rw [quotientAction_mk, QuotientGroup.eq] at h1
      have hc : (ρ j v)⁻¹ * v ∈ W₀ := h1
      have hc' : v⁻¹ * ρ j v ∈ W₀ := by
        have := W₀.inv_mem hc
        rwa [mul_inv_rev, inv_inv] at this
      have hjv : ρ j v = v * (v⁻¹ * ρ j v) := by group
      rw [pow_apply_of_mem ρ hc' hjv p, hexp, mul_one, MulAut.one_apply]
    have hρ' : Function.Injective ρ' := by
      rw [injective_iff_map_eq_one]
      intro j hj
      have hKp : IsPGroup p ρ'.ker := fun k =>
        ⟨1, Subtype.ext (by rw [pow_one]; exact hker k (MonoidHom.mem_ker.mp k.2))⟩
      have h1 : ρ'.ker ≤ Q := hSQ ▸ hKp.le_sylow_of_normal SQ
      have h2 : ρ'.ker ≤ Qs := hSQs ▸ hKp.le_sylow_of_normal SQs
      have h3 : j ∈ Q ⊓ Qs := ⟨h1 hj, h2 hj⟩
      rwa [hinf, Subgroup.mem_bot] at h3
    obtain ⟨e, he, hWe⟩ := (Nat.dvd_prime_pow hp).mp
      ((hV.trans (pow_mul p f 2).symm) ▸ Subgroup.card_subgroup_dvd_card W₀)
    have he0 : e ≠ 0 := by
      rintro rfl
      exact hne (Subgroup.card_eq_one.mp (by rw [hWe, pow_zero]))
    have hquot : Nat.card (V ⧸ W₀) = p ^ (f * 2 - e) := by
      have h := Subgroup.card_eq_card_quotient_mul_card_subgroup W₀
      rw [hV, ← pow_mul, hWe, ← Nat.sub_add_cancel he, pow_add] at h
      exact (Nat.eq_of_mul_eq_mul_right (Nat.pow_pos hp.pos) h).symm
    have hle := two_mul_le_of_injective hp hf (hJ ▸ dvd_refl _) hZ ρ' hρ' hquot
    omega
  have hconj : Nat.card (fixedPoints ρ Q) = Nat.card (fixedPoints ρ Qs) := by
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq J SQ SQs
    have hQs' : Qs = Q.map (MulAut.conj g).toMonoidHom := by
      rw [← hSQs, ← hg]
      rfl
    rw [hQs', ← map_fixedPoints_conj, Subgroup.card_map_of_injective (ρ g).injective]
  have hAB : fixedPoints ρ Q ⊓ fixedPoints ρ Qs = ⊥ := by
    rw [fixedPoints_inf, hsup, hW₀]
  have hprod : Nat.card (fixedPoints ρ Q) * Nat.card (fixedPoints ρ Qs) ≤ Nat.card V := by
    rw [← Nat.card_prod]
    refine Nat.card_le_card_of_injective (fun x => (x.1 : V) * x.2) ?_
    rintro ⟨a, b⟩ ⟨a', b'⟩ hab
    have hab' : (a : V) * b = a' * b' := hab
    have hmem : (a' : V)⁻¹ * a ∈ fixedPoints ρ Q ⊓ fixedPoints ρ Qs := by
      refine ⟨(fixedPoints ρ Q).mul_mem ((fixedPoints ρ Q).inv_mem a'.2) a.2, ?_⟩
      have h1 : (a' : V)⁻¹ * a = b' * (b : V)⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← hab', mul_inv_cancel_right]
      rw [h1]
      exact (fixedPoints ρ Qs).mul_mem b'.2 ((fixedPoints ρ Qs).inv_mem b.2)
    rw [hAB, Subgroup.mem_bot, inv_mul_eq_one] at hmem
    have hb : (b : V) = b' := by
      rw [← hmem] at hab'
      exact mul_left_cancel hab'
    exact Prod.ext (Subtype.ext hmem.symm) (Subtype.ext hb)
  rw [← hconj, hV, ← sq] at hprod
  exact (Nat.pow_le_pow_iff_left two_ne_zero).mp hprod

theorem card_fixedPoints_le [Finite J] [Finite V] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (hJ : Nat.card J = p ^ f * ((p ^ f) ^ 2 - 1))
    (hcomm : ∀ v w : V, v * w = w * v) (hexp : ∀ v : V, v ^ p = 1)
    (hV : Nat.card V = (p ^ f) ^ 2) (ρ : J →* MulAut V) (hρ : Function.Injective ρ)
    {Q Qs : Subgroup J} (hQ : Nat.card Q = p ^ f) (hQs : Nat.card Qs = p ^ f)
    (hinf : Q ⊓ Qs = ⊥) (hsup : Q ⊔ Qs = ⊤) :
    Nat.card (fixedPoints ρ Q) ≤ p ^ f := by
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  exact card_fixedPoints_le_of_primitive hp hf
    (fun hf2 => exists_primitive_prime_dvd_pow_sub_one hp3 (by omega)) hJ hcomm hexp hV ρ hρ
    hQ hQs hinf hsup

end CFSG.SL2MinimalFaithful
