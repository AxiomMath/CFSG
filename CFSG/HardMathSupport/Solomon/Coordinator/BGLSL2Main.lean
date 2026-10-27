module

public import CFSG.HardMathSupport.Solomon.Coordinator.BGLSL2Aux
public import CFSG.HardMathSupport.Solomon.Coordinator.L514CL2
public import Certificates.Certificate42
public import CFSG.Dihedral.Glauberman.DicksonMaxSubfield
public import CFSG.HardMathSupport.Solomon.Coordinator.BGLSL2Witness

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.BGL

open Matrix CFSG.Glauberman.Dickson
open scoped commutatorElement

variable {E : Type} [Field E] [Finite E]

@[expose] def twoRoot (k : Subfield E) (κ : E) : Subgroup (SpecialLinearGroup (Fin 2) E) :=
  Subgroup.closure ({g | ∃ s ∈ k, g = sl2x s} ∪ {g | ∃ s ∈ k, g = sl2y (κ * s)})

omit [Finite E] in
theorem sl2x_mem_twoRoot (k : Subfield E) (κ : E) {s : E} (hs : s ∈ k) :
    sl2x s ∈ twoRoot k κ :=
  Subgroup.subset_closure (Or.inl ⟨s, hs, rfl⟩)

omit [Finite E] in
theorem sl2y_mem_twoRoot (k : Subfield E) (κ : E) {s : E} (hs : s ∈ k) :
    sl2y (κ * s) ∈ twoRoot k κ :=
  Subgroup.subset_closure (Or.inr ⟨s, hs, rfl⟩)

omit [Finite E] in
theorem trace_x_mul_y (a b : E) :
    ((sl2x a * sl2y b : SpecialLinearGroup (Fin 2) E) : Matrix (Fin 2) (Fin 2) E).trace =
      2 + a * b := by
  simp [sl2x_coe, sl2y_coe, Matrix.trace_fin_two]
  ring

theorem not_dvd_of_dvd_div {p f z : ℕ} (hp : p.Prime) (hf : f ≠ 0)
    (hz : z ∣ (p ^ f - 1) / Nat.gcd (p ^ f - 1) 2 ∨ z ∣ (p ^ f + 1) / Nat.gcd (p ^ f - 1) 2) :
    ¬ p ∣ z := by
  intro hpz
  have hpq : p ∣ p ^ f := dvd_pow_self p hf
  have hq1 : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.pos
  rcases hz with h | h
  · have h1 : z ∣ p ^ f - 1 := h.trans (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _))
    have h2 : p ∣ p ^ f - 1 := hpz.trans h1
    have h3 : p ∣ p ^ f - (p ^ f - 1) := Nat.dvd_sub hpq h2
    have : p ^ f - (p ^ f - 1) = 1 := by omega
    rw [this] at h3
    exact hp.one_lt.ne' (Nat.dvd_one.1 h3)
  · have hg : Nat.gcd (p ^ f - 1) 2 ∣ p ^ f + 1 := by
      have h2 : Nat.gcd (p ^ f - 1) 2 ∣ 2 := Nat.gcd_dvd_right _ _
      rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h | h
      · rw [h]; exact one_dvd _
      · have : 2 ∣ p ^ f - 1 := h ▸ Nat.gcd_dvd_left _ _
        rw [h]; omega
    have h1 : z ∣ p ^ f + 1 := h.trans (Nat.div_dvd_of_dvd hg)
    have h2 : p ∣ p ^ f + 1 := hpz.trans h1
    have h3 : p ∣ 1 := (Nat.dvd_add_right hpq).1 h2
    exact hp.one_lt.ne' (Nat.dvd_one.1 h3)

theorem mem_normal_of_pow_eq_one {G : Type*} [Group G] [Finite G] {p : ℕ} (N C : Subgroup G)
    [N.Normal] (hsup : N ⊔ C = ⊤) (hCp : Nat.Coprime p (Nat.card C)) {h : G} (hp : h ^ p = 1) :
    h ∈ N := by
  obtain ⟨n, hn, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 (hsup ▸ Subgroup.mem_top h)
  have hq : (QuotientGroup.mk (n * c) : G ⧸ N) = QuotientGroup.mk c := by
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n).2 hn, one_mul]
  have h1 : (QuotientGroup.mk c : G ⧸ N) ^ p = 1 := by
    rw [← hq, ← QuotientGroup.mk_pow, hp]; rfl
  have h2 : orderOf (QuotientGroup.mk c : G ⧸ N) ∣ p := orderOf_dvd_of_pow_eq_one h1
  have h3 : orderOf (QuotientGroup.mk c : G ⧸ N) ∣ Nat.card C :=
    (orderOf_dvd_of_pow_eq_one (by
      have hcC : orderOf (⟨c, hc⟩ : C) ∣ Nat.card C := orderOf_dvd_natCard _
      have : (⟨c, hc⟩ : C) ^ Nat.card C = 1 := pow_card_eq_one'
      have := congrArg (fun x : C => (x : G)) this
      simp only [Subgroup.coe_pow, Subgroup.coe_one] at this
      rw [← QuotientGroup.mk_pow, this]; rfl))
  have h4 : orderOf (QuotientGroup.mk c : G ⧸ N) = 1 :=
    Nat.eq_one_of_dvd_coprimes hCp h2 h3
  have h5 : (QuotientGroup.mk c : G ⧸ N) = 1 := orderOf_eq_one_iff.1 h4
  have hcN : c ∈ N := (QuotientGroup.eq_one_iff c).1 h5
  exact N.mul_mem hn hcN

omit [Finite E] in
theorem no_small_orders {p : ℕ} [Fact p.Prime] [CharP E p] (k : Subfield E) {κ : E} (hκ0 : κ ≠ 0)
    (hmax : ∀ K : Subfield E, k ≤ K → κ ∈ K → K = ⊤) (hbig : ∃ x : E, x ^ (p ^ 2) ≠ x)
    (hord : ∀ m ∈ k, ∃ n : ℕ, (n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5) ∧
      (sl2x (1 : E) * sl2y (κ * m)) ^ n ∈ Subgroup.center (SpecialLinearGroup (Fin 2) E)) :
    False := by
  have hfrob : ∀ m ∈ k, (2 + 1 * (κ * m)) ^ (p ^ 2) = 2 + 1 * (κ * m) := by
    intro m hm
    obtain ⟨n, hn, hc⟩ := hord m hm
    have hroots := sl2_trace_roots _ hn hc
    rw [trace_x_mul_y] at hroots
    set t : E := 2 + 1 * (κ * m) with ht
    rcases hroots with h | h | h | h | h | h
    · exact pow_p_sq_of_quadratic (p := p) 0 0 (by simpa using (by rw [h]; ring : t ^ 2 = 0))
    · exact pow_p_sq_of_quadratic (p := p) 0 1 (by push_cast; linear_combination h)
    · exact pow_p_sq_of_quadratic (p := p) 0 2 (by push_cast; linear_combination h)
    · exact pow_p_sq_of_quadratic (p := p) 0 4 (by push_cast; linear_combination h)
    · exact pow_p_sq_of_quadratic (p := p) 1 1 (by push_cast; linear_combination h)
    · exact pow_p_sq_of_quadratic (p := p) (-1) 1 (by push_cast; linear_combination h)
  have h2 : ((2 : E)) ^ (p ^ 2) = 2 := by
    have := map_ofNat (iterateFrobenius E p 2) 2
    simpa [iterateFrobenius_def] using this
  have hexp : ∀ m ∈ k, κ ^ (p ^ 2) * m ^ (p ^ 2) = κ * m := by
    intro m hm
    have := hfrob m hm
    rw [one_mul, add_pow_char_pow, h2, mul_pow] at this
    exact add_left_cancel this
  have hκ : κ ^ (p ^ 2) = κ := by simpa using hexp 1 k.one_mem
  have hk : ∀ m ∈ k, m ^ (p ^ 2) = m := by
    intro m hm
    have := hexp m hm
    rw [hκ] at this
    exact mul_left_cancel₀ hκ0 this
  have hle : k ≤ CFSG.Glauberman.Dickson.MaxSubfield.fixField E p 2 := fun m hm =>
    CFSG.Glauberman.Dickson.MaxSubfield.mem_fixField.2 (hk m hm)
  have hκK : κ ∈ CFSG.Glauberman.Dickson.MaxSubfield.fixField E p 2 :=
    CFSG.Glauberman.Dickson.MaxSubfield.mem_fixField.2 hκ
  have htop := hmax _ hle hκK
  obtain ⟨x, hx⟩ := hbig
  apply hx
  have : x ∈ CFSG.Glauberman.Dickson.MaxSubfield.fixField E p 2 := by rw [htop]; trivial
  exact CFSG.Glauberman.Dickson.MaxSubfield.mem_fixField.1 this

theorem alt4_orders : ∀ a : alternatingGroup (Fin 4), a ^ 2 = 1 ∨ a ^ 3 = 1 := by decide +kernel

theorem perm4_orders : ∀ a : Equiv.Perm (Fin 4), a ^ 2 = 1 ∨ a ^ 3 = 1 ∨ a ^ 4 = 1 := by
  decide +kernel

theorem card_psl2_eq_of_card_eq {F F' : Type} [Field F] [Finite F] [Field F'] [Finite F']
    (h : Nat.card F = Nat.card F') :
    Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) =
      Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F') := by
  have h1 := l514c_card_psl2 (F := F)
  have h2 := l514c_card_psl2 (F := F')
  have e1 : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) =
      Nat.card (CFSG.Open.StatedProj (CFSG.Open.StatedSL 2 F)) :=
    Nat.card_congr (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).toEquiv
  have e2 : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F') =
      Nat.card (CFSG.Open.StatedProj (CFSG.Open.StatedSL 2 F')) :=
    Nat.card_congr (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F').toEquiv
  rw [e1, e2]
  rw [← h] at h2
  have hg : 0 < Nat.gcd 2 (Nat.card F - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  exact Nat.eq_of_mul_eq_mul_right hg (h1.trans h2.symm)

theorem sl2_twoRootGroups_core
    (k : Subfield E) {κ : E} (hκ : κ ∉ k) (hmax : ∀ K : Subfield E, k ≤ K → κ ∈ K → K = ⊤)
    (hk2 : Nat.card k ≠ 2) (hbig : ∃ x : E, x ^ ((ringChar E) ^ 2) ≠ x) :
    twoRoot k κ = ⊤ := by
  classical
  obtain ⟨p, hpc⟩ := CharP.exists E
  have : Fact p.Prime := ⟨CharP.char_is_prime E p⟩
  have hpr : ringChar E = p := ringChar.eq E p
  rw [hpr] at hbig
  have : Fintype E := Fintype.ofFinite E
  obtain ⟨f, -, hf⟩ := FiniteField.card E p
  have hFcard : Nat.card E = p ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hf]
  have hf0 : (f : ℕ) ≠ 0 := f.ne_zero
  have hκ0 : κ ≠ 0 := fun h => hκ (h ▸ k.zero_mem)
  have hp2 := (Fact.out : p.Prime).two_le
  set D := twoRoot k κ with hD
  let π : SpecialLinearGroup (Fin 2) E →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) E :=
    QuotientGroup.mk' _
  set H : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) E) := D.map π with hH
  have hE4 : 4 ≤ Nat.card E := by
    have hk1 : 1 < Nat.card k := Finite.one_lt_card
    have hlt : Nat.card {x // x ∈ k} < Nat.card E :=
      Finite.card_subtype_lt (p := (· ∈ k)) (x := κ) hκ
    have : Nat.card k = Nat.card {x // x ∈ k} := rfl
    omega
  have hsub : ∀ s ∈ k, (QuotientGroup.mk (sl2x s) : Matrix.ProjectiveSpecialLinearGroup (Fin 2) E) ∈ H :=
    fun s hs => ⟨sl2x s, sl2x_mem_twoRoot k κ hs, rfl⟩
  suffices hHtop : H = ⊤ by
    have hs4 : ∃ s : Finset E, s.card = 4 := by
      have : 4 ≤ (Finset.univ : Finset E).card := by
        rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact hE4
      obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq this
      exact ⟨s, hs⟩
    have hperf := (CFSG.LinearGroups.special_linear_isPerfect (K := E) (n := 2) le_rfl
      (Or.inr hs4)).commutator_eq_top
    apply eq_top_of_sup_center hperf
    rw [eq_top_iff]
    intro g _
    have : π g ∈ H := hHtop ▸ Subgroup.mem_top _
    obtain ⟨d, hd, hdg⟩ := this
    have hz : d⁻¹ * g ∈ Subgroup.center (SpecialLinearGroup (Fin 2) E) :=
      QuotientGroup.eq.1 hdg
    have : g = d * (d⁻¹ * g) := by simp
    rw [this]
    exact Subgroup.mul_mem_sup hd hz
  by_contra hHne
  have hx1H : (QuotientGroup.mk (sl2x (1 : E)) : Matrix.ProjectiveSpecialLinearGroup (Fin 2) E) ∈ H :=
    hsub 1 k.one_mem
  have hy1H : (QuotientGroup.mk (sl2y κ) : Matrix.ProjectiveSpecialLinearGroup (Fin 2) E) ∈ H :=
    ⟨sl2y κ, by simpa using sl2y_mem_twoRoot k κ k.one_mem, rfl⟩
  let hx : H := ⟨_, hx1H⟩
  let hy : H := ⟨_, hy1H⟩
  have hnc : hx * hy ≠ hy * hx := fun h =>
    sl2_comm_ne hκ0 (congrArg Subtype.val h)
  have hpE : (p : E) = 0 := CharP.cast_eq_zero E p
  have hxp : ∀ s : E, (QuotientGroup.mk (sl2x s) : Matrix.ProjectiveSpecialLinearGroup (Fin 2) E) ^ p
      = 1 := fun s => by
    rw [← QuotientGroup.mk_pow, sl2x_pow, hpE, zero_mul, sl2x_zero]; rfl
  have hxpH : hx ^ p = 1 := Subtype.ext (hxp 1)
  have hx1 : hx ≠ 1 := by
    intro h
    have h1 : (QuotientGroup.mk (sl2x (1 : E)) : Matrix.ProjectiveSpecialLinearGroup (Fin 2) E) =
        QuotientGroup.mk (sl2x 0) := by
      rw [sl2x_zero]; exact congrArg Subtype.val h
    exact one_ne_zero (sl2x_inj h1)
  have hordx : orderOf hx = p := orderOf_eq_prime hxpH hx1
  have hpdvd : p ∣ Nat.card H := hordx ▸ orderOf_dvd_natCard hx
  let xk : Multiplicative k →* H :=
    { toFun := fun s => ⟨QuotientGroup.mk (sl2x ((Multiplicative.toAdd s : k) : E)),
        hsub _ (Multiplicative.toAdd s).2⟩
      map_one' := Subtype.ext (by
        show (QuotientGroup.mk (sl2x (((0 : k) : E))) : Matrix.ProjectiveSpecialLinearGroup (Fin 2) E) = 1
        rw [show (((0 : k) : E)) = 0 from rfl, sl2x_zero]; rfl)
      map_mul' := fun a b => Subtype.ext (by
        show (QuotientGroup.mk (sl2x (((Multiplicative.toAdd a + Multiplicative.toAdd b : k) : E))) :
          Matrix.ProjectiveSpecialLinearGroup (Fin 2) E) = _
        rw [show (((Multiplicative.toAdd a + Multiplicative.toAdd b : k) : E)) =
          ((Multiplicative.toAdd a : k) : E) + ((Multiplicative.toAdd b : k) : E) from rfl,
          ← sl2x_mul, QuotientGroup.mk_mul]; rfl) }
  have hxk_inj : Function.Injective xk := by
    intro a b hab
    have := sl2x_inj (congrArg Subtype.val hab)
    exact Multiplicative.toAdd.injective (Subtype.ext this)
  have hkH : Nat.card k ∣ Nat.card H := by
    have := Subgroup.card_dvd_of_injective xk hxk_inj
    rwa [Nat.card_congr (Multiplicative.toAdd (α := k))] at this
  have hdih_gen := huppert_II_8_27_dickson_psl2_subgroup_classification_with_subfield
    (F := E) (p := p) (f := (f : ℕ)) hFcard H
  have hgmem : ∀ m ∈ k, (QuotientGroup.mk (sl2x (1 : E) * sl2y (κ * m)) :
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) E) ∈ H := fun m hm =>
    ⟨sl2x 1 * sl2y (κ * m), D.mul_mem (sl2x_mem_twoRoot k κ k.one_mem) (sl2y_mem_twoRoot k κ hm), rfl⟩
  have hcen : ∀ m (hm : m ∈ k) (n : ℕ),
      (⟨QuotientGroup.mk (sl2x (1 : E) * sl2y (κ * m)), hgmem m hm⟩ : H) ^ n = 1 →
        (sl2x (1 : E) * sl2y (κ * m)) ^ n ∈ Subgroup.center (SpecialLinearGroup (Fin 2) E) := by
    intro m hm n hn
    have h1 := congrArg Subtype.val hn
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at h1
    rw [← QuotientGroup.mk_pow] at h1
    exact (QuotientGroup.eq_one_iff _).1 h1
  rcases hdih_gen with h1 | ⟨z, hz, hcard, -⟩ | ⟨z, hz, hcard, -⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ |
    ⟨-, ⟨e⟩⟩ | ⟨m, t, ht1, ht2, N, C, hN, hNe, hNc, hC, hCc, hdis, hsup⟩ |
    ⟨m, hm0, hmf, ⟨e⟩, ⟨W⟩⟩ | ⟨m, hm0, hmf, ⟨e⟩, ⟨W⟩⟩
  · exact hnc (h1.toIsMulCommutative.is_comm.comm hx hy)
  · rw [hFcard] at hz
    rw [hcard] at hpdvd
    exact not_dvd_of_dvd_div (Fact.out : p.Prime) hf0 hz hpdvd
  · rw [hFcard] at hz
    rw [hcard] at hpdvd hkH
    rcases (Nat.Prime.dvd_mul (Fact.out : p.Prime)).1 hpdvd with h2 | hzp
    · have hp2' : p = 2 := (Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).1 h2
      subst hp2'
      have hkE : Nat.card k ∣ Nat.card E := by
        have := AddSubgroup.card_addSubgroup_dvd_card k.toAddSubgroup
        exact this
      rw [hFcard] at hkE
      obtain ⟨e', -, he'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hkE
      have hk1 : 1 < Nat.card k := Finite.one_lt_card
      have he2 : 2 ≤ e' := by
        by_contra hlt
        push Not at hlt
        interval_cases e'
        · rw [pow_zero] at he'; omega
        · rw [pow_one] at he'; exact hk2 he'
      have hk4 : 4 ∣ Nat.card k := by
        rw [he']; exact (pow_dvd_pow 2 he2 : 2 ^ 2 ∣ 2 ^ e')
      have h42 : 4 ∣ 2 * z := hk4.trans hkH
      have hq1 : 1 ≤ 2 ^ (f : ℕ) := Nat.one_le_two_pow
      have h2f : 2 ∣ 2 ^ (f : ℕ) := dvd_pow_self 2 hf0
      have hzodd : Odd z := by
        rcases hz with h | h
        · have hodd : Odd (2 ^ (f : ℕ) - 1) := by
            rw [Nat.odd_iff]; omega
          exact hodd.of_dvd_nat (h.trans (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)))
        · have hodd : Odd (2 ^ (f : ℕ) + 1) := by
            rw [Nat.odd_iff]; omega
          have hg : Nat.gcd (2 ^ (f : ℕ) - 1) 2 ∣ 2 ^ (f : ℕ) + 1 := by
            have hg1 : Nat.gcd (2 ^ (f : ℕ) - 1) 2 = 1 := by
              have h2' : Nat.gcd (2 ^ (f : ℕ) - 1) 2 ∣ 2 := Nat.gcd_dvd_right _ _
              rcases (Nat.dvd_prime Nat.prime_two).1 h2' with h | h
              · exact h
              · exfalso
                have h22 : 2 ∣ 2 ^ (f : ℕ) - 1 := by
                  have := Nat.gcd_dvd_left (2 ^ (f : ℕ) - 1) 2
                  rwa [h] at this
                omega
            rw [hg1]; exact one_dvd _
          exact hodd.of_dvd_nat (h.trans (Nat.div_dvd_of_dvd hg))
      obtain ⟨w, hw⟩ := hzodd
      omega
    · exact not_dvd_of_dvd_div (Fact.out : p.Prime) hf0 hz hzp
  · refine no_small_orders k hκ0 hmax hbig (fun m hm => ?_)
    have key : ∃ n : ℕ, (n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5) ∧
        (⟨QuotientGroup.mk (sl2x (1 : E) * sl2y (κ * m)), hgmem m hm⟩ : H) ^ n = 1 := by
      rcases alt4_orders (e ⟨_, hgmem m hm⟩) with h | h
      · exact ⟨2, Or.inl rfl, e.injective (by rw [map_pow, h, map_one])⟩
      · exact ⟨3, Or.inr (Or.inl rfl), e.injective (by rw [map_pow, h, map_one])⟩
    obtain ⟨n, hn, hn1⟩ := key
    exact ⟨n, hn, hcen m hm n hn1⟩
  · refine no_small_orders k hκ0 hmax hbig (fun m hm => ?_)
    have key : ∃ n : ℕ, (n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5) ∧
        (⟨QuotientGroup.mk (sl2x (1 : E) * sl2y (κ * m)), hgmem m hm⟩ : H) ^ n = 1 := by
      rcases perm4_orders (e ⟨_, hgmem m hm⟩) with h | h | h
      · exact ⟨2, Or.inl rfl, e.injective (by rw [map_pow, h, map_one])⟩
      · exact ⟨3, Or.inr (Or.inl rfl), e.injective (by rw [map_pow, h, map_one])⟩
      · exact ⟨4, Or.inr (Or.inr (Or.inl rfl)), e.injective (by rw [map_pow, h, map_one])⟩
    obtain ⟨n, hn, hn1⟩ := key
    exact ⟨n, hn, hcen m hm n hn1⟩
  · refine no_small_orders k hκ0 hmax hbig (fun m hm => ?_)
    have key : ∃ n : ℕ, (n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5) ∧
        (⟨QuotientGroup.mk (sl2x (1 : E) * sl2y (κ * m)), hgmem m hm⟩ : H) ^ n = 1 := by
      by_cases h1 : e ⟨_, hgmem m hm⟩ = 1
      · exact ⟨2, Or.inl rfl, e.injective (by rw [map_pow, h1, one_pow, map_one])⟩
      · rcases Certificates.certificate42 _ h1 with h | h | h
        · exact ⟨2, Or.inl rfl, e.injective (by rw [map_pow, h, map_one])⟩
        · exact ⟨3, Or.inr (Or.inl rfl), e.injective (by rw [map_pow, h, map_one])⟩
        · exact ⟨5, Or.inr (Or.inr (Or.inr rfl)), e.injective (by rw [map_pow, h, map_one])⟩
    obtain ⟨n, hn, hn1⟩ := key
    exact ⟨n, hn, hcen m hm n hn1⟩
  ·
    have hcop : Nat.Coprime p (Nat.card C) := by
      rw [hCc]
      have h1 : t ∣ p ^ (f : ℕ) - 1 := ht2.trans (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _))
      refine (Nat.Prime.coprime_iff_not_dvd (Fact.out)).2 fun hpt => ?_
      have hpq : p ∣ p ^ (f : ℕ) := dvd_pow_self p hf0
      have hq1 : 1 ≤ p ^ (f : ℕ) := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
      have h3 : p ∣ p ^ (f : ℕ) - (p ^ (f : ℕ) - 1) := Nat.dvd_sub hpq (hpt.trans h1)
      have : p ^ (f : ℕ) - (p ^ (f : ℕ) - 1) = 1 := by omega
      rw [this] at h3
      exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.1 h3)
    have := hN
    have hypH : hy ^ p = 1 := Subtype.ext (by
      show (QuotientGroup.mk (sl2y κ) : Matrix.ProjectiveSpecialLinearGroup (Fin 2) E) ^ p = 1
      rw [← QuotientGroup.mk_pow, sl2y_pow, hpE, zero_mul, sl2y_zero]; rfl)
    have hxN : hx ∈ N := mem_normal_of_pow_eq_one N C hsup hcop hxpH
    have hyN : hy ∈ N := mem_normal_of_pow_eq_one N C hsup hcop hypH
    have := hNe.toIsMulCommutative.is_comm.comm (⟨hx, hxN⟩ : N) ⟨hy, hyN⟩
    exact hnc (congrArg Subtype.val this)
  ·
    have hK : ∀ m' ∈ k, (2 + κ * m') ^ 2 ∈ W.K := fun m' hm' => by
      have := trace_sq_mem_of_witness H W (sl2x 1 * sl2y (κ * m')) (hgmem m' hm')
      rwa [trace_x_mul_y, one_mul] at this
    obtain ⟨hκK, hkK⟩ := kappa_mem_of_sq_mem W.K k hκ0 hK
    have hKtop := hmax W.K hkK hκK
    have hcardK : Nat.card W.K = Nat.card E := by
      rw [hKtop]; exact Nat.card_congr Subfield.topEquiv.toEquiv
    rw [W.card_eq, hFcard] at hcardK
    have hmf' : m = f := Nat.pow_right_injective hp2 hcardK
    apply hHne
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_congr e.toEquiv]
    apply card_psl2_eq_of_card_eq
    rw [GaloisField.card p m hm0, hFcard, hmf']
  ·
    have hK : ∀ m' ∈ k, (2 + κ * m') ^ 2 ∈ W.K := fun m' hm' => by
      have := trace_sq_mem_of_witness H W (sl2x 1 * sl2y (κ * m')) (hgmem m' hm')
      rwa [trace_x_mul_y, one_mul] at this
    obtain ⟨hκK, hkK⟩ := kappa_mem_of_sq_mem W.K k hκ0 hK
    have hKtop := hmax W.K hkK hκK
    have hcardK : Nat.card W.K = Nat.card E := by
      rw [hKtop]; exact Nat.card_congr Subfield.topEquiv.toEquiv
    rw [W.card_eq, hFcard] at hcardK
    have hmf' : m = f := Nat.pow_right_injective hp2 hcardK
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hf0) hmf
    omega

omit [Finite E] in
theorem subfield_eq_of_card_eq {K k : Subfield E} [Finite E] (h : k ≤ K) (hc : Nat.card K = Nat.card k) :
    K = k := by
  have hinj : Function.Injective (Subfield.inclusion h) := (Subfield.inclusion h).injective
  have hbij : Function.Bijective (Subfield.inclusion h) :=
    (Nat.bijective_iff_injective_and_card (Subfield.inclusion h)).2 ⟨hinj, hc.symm⟩
  apply le_antisymm _ h
  intro x hx
  obtain ⟨y, hy⟩ := hbij.2 ⟨x, hx⟩
  have hyx : (y : E) = x := congrArg Subtype.val hy
  rw [← hyx]; exact y.2

theorem hmax_of_card_cube (k : Subfield E) (hk : 2 ≤ Nat.card k)
    (hc : Nat.card E = Nat.card k ^ 3) {κ : E} (hκ : κ ∉ k) :
    ∀ K : Subfield E, k ≤ K → κ ∈ K → K = ⊤ := by
  intro K hkK hκK
  have : Fintype E := Fintype.ofFinite E
  have : Fintype k := Fintype.ofFinite k
  have : Fintype K := Fintype.ofFinite K
  let _ : Algebra k K := (Subfield.inclusion hkK).toAlgebra
  let _ : Algebra K E := (K.subtype).toAlgebra
  have h1 : Nat.card K = Nat.card k ^ Module.finrank k K := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Module.card_eq_pow_finrank (K := k) (V := K)
  have h2 : Nat.card E = Nat.card K ^ Module.finrank K E := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Module.card_eq_pow_finrank (K := K) (V := E)
  rw [h1, ← pow_mul] at h2
  rw [hc] at h2
  have hab : 3 = Module.finrank k K * Module.finrank K E :=
    Nat.pow_right_injective hk h2
  have ha : Module.finrank k K ∣ 3 := ⟨_, hab⟩
  rcases (Nat.dvd_prime Nat.prime_three).1 ha with h | h
  · exfalso
    rw [h, pow_one] at h1
    exact hκ (subfield_eq_of_card_eq hkK h1 ▸ hκK)
  · have hKE : Nat.card K = Nat.card (⊤ : Subfield E) := by
      rw [Nat.card_congr Subfield.topEquiv.toEquiv, h1, h, hc]
    exact (subfield_eq_of_card_eq (le_top : K ≤ ⊤) hKE.symm).symm

theorem sl2_twoRootGroups_gen
    (k : Subfield E) (hc : Nat.card E = Nat.card k ^ 3) (hk2 : Nat.card k ≠ 2) {κ : E}
    (hκ : κ ∉ k) : twoRoot k κ = ⊤ := by
  classical
  have hk1 : 1 < Nat.card k := Finite.one_lt_card
  have hk : 2 ≤ Nat.card k := hk1
  refine sl2_twoRootGroups_core k hκ (hmax_of_card_cube k hk hc hκ) hk2 ?_
  obtain ⟨p, hpc⟩ := CharP.exists E
  have : Fact p.Prime := ⟨CharP.char_is_prime E p⟩
  have hpr : ringChar E = p := ringChar.eq E p
  rw [hpr]
  by_contra hno
  push Not at hno
  have : Fintype E := Fintype.ofFinite E
  have hcard : Nat.card E ≤ p ^ 2 := by
    have hroots : ∀ x : E, x ∈ (Polynomial.X ^ (p ^ 2) - Polynomial.X : Polynomial E).roots.toFinset := by
      intro x
      rw [Multiset.mem_toFinset, Polynomial.mem_roots]
      · simp [hno x]
      · intro h0
        have := congrArg Polynomial.natDegree h0
        rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt (by simp; nlinarith [(Fact.out : p.Prime).two_le])] at this
        simp at this
        have := (Fact.out : p.Prime).two_le
        nlinarith
    have h1 : (Finset.univ : Finset E) ⊆ (Polynomial.X ^ (p ^ 2) - Polynomial.X : Polynomial E).roots.toFinset :=
      fun x _ => hroots x
    calc Nat.card E = (Finset.univ : Finset E).card := by rw [Finset.card_univ, Nat.card_eq_fintype_card]
      _ ≤ _ := Finset.card_le_card h1
      _ ≤ (Polynomial.X ^ (p ^ 2) - Polynomial.X : Polynomial E).roots.card := Multiset.toFinset_card_le _
      _ ≤ (Polynomial.X ^ (p ^ 2) - Polynomial.X : Polynomial E).natDegree := Polynomial.card_roots' _
      _ = p ^ 2 := by
        rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt (by simp; nlinarith [(Fact.out : p.Prime).two_le])]
        simp
  have hpk : p ∣ Nat.card k := by
    have hkE : Nat.card k ∣ Nat.card E := by
      have := AddSubgroup.card_addSubgroup_dvd_card k.toAddSubgroup
      exact this
    obtain ⟨f, -, hf⟩ := FiniteField.card E p
    have hFc : Nat.card E = p ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hf]
    rw [hFc] at hkE
    obtain ⟨e, he, hke⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).1 hkE
    have : e ≠ 0 := by rintro rfl; rw [pow_zero] at hke; omega
    rw [hke]; exact dvd_pow_self p this
  have hp : p ≤ Nat.card k := Nat.le_of_dvd (by omega) hpk
  have h3 : Nat.card k ^ 3 ≤ p ^ 2 := by rw [← hc]; exact hcard
  have h4 : p ^ 2 ≤ Nat.card k ^ 2 := Nat.pow_le_pow_left hp 2
  have h5 : 0 < Nat.card k ^ 2 := by positivity
  have h6 : Nat.card k ^ 3 = Nat.card k * Nat.card k ^ 2 := by ring
  nlinarith

end CFSG.HardMathSupport.Solomon.Coordinator.BGL
