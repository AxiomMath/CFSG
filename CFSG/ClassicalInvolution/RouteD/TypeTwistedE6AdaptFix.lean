module

public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6AdaptReal
public import CFSG.ClassicalInvolution.Models.UnitaryPairs.Intrinsic

public section

namespace CFSG.ClassicalInvolution.RouteD.NonClassical

open Polynomial

section TwoByTwo

variable {K : Type*} [Field K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem rot_pow {r s κ : K} (hr : r ^ p ^ f = r) (hs : s ^ p ^ f = s)
    (hκ : κ ^ ((p ^ f - 1) / 2) = -1) (hodd : p ^ f % 2 = 1) (hrs : r ^ 2 - κ * s ^ 2 = 1) :
    (!![r, κ * s; s, r] : Matrix (Fin 2) (Fin 2) K) ^ (p ^ f + 1) = 1 := by
  set Z : Matrix (Fin 2) (Fin 2) K := !![0, κ; 1, 0] with hZ
  have hY : (!![r, κ * s; s, r] : Matrix (Fin 2) (Fin 2) K) =
      r • (1 : Matrix (Fin 2) (Fin 2) K) + s • Z := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hZ]
    ring
  have hZ2 : Z * Z = κ • (1 : Matrix (Fin 2) (Fin 2) K) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hZ, Matrix.mul_apply, Fin.sum_univ_two]
  have hcomm : Commute (r • (1 : Matrix (Fin 2) (Fin 2) K)) (s • Z) :=
    ((Commute.one_left Z).smul_left r).smul_right s
  obtain ⟨m, hm⟩ : ∃ m, p ^ f = 2 * m + 1 := ⟨(p ^ f) / 2, by omega⟩
  have hmm : (p ^ f - 1) / 2 = m := by omega
  rw [hmm] at hκ
  have hZq : Z ^ (p ^ f) = -Z := by
    rw [hm, pow_succ, pow_mul, sq, hZ2, _root_.smul_pow, one_pow, hκ, neg_smul, one_smul, neg_mul,
      one_mul]
  have hYq : (r • (1 : Matrix (Fin 2) (Fin 2) K) + s • Z) ^ (p ^ f) =
      r • (1 : Matrix (Fin 2) (Fin 2) K) - s • Z := by
    rw [add_pow_char_pow_of_commute p f hcomm, _root_.smul_pow, _root_.smul_pow, one_pow, hr, hs,
      hZq, smul_neg, sub_eq_add_neg]
  rw [hY, pow_succ, hYq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hZ, Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | ring1 | linear_combination hrs

theorem refl_sq {r s κ : K} (hrs : r ^ 2 - κ * s ^ 2 = 1) :
    (!![r, -(κ * s); s, -r] : Matrix (Fin 2) (Fin 2) K) ^ 2 = 1 := by
  rw [sq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | ring1 | linear_combination hrs

end TwoByTwo

section Rep

theorem exists_fixed_rep {K : Type*} [Field K] [Finite K] (σ : K ≃+* K) {p : ℕ} [CharP K p]
    (hp2 : p ≠ 2) {d₁ d₂ c : K} (h₁ : σ d₁ = d₁) (h₂ : σ d₂ = d₂) (hc : σ c = c)
    (hd₁ : d₁ ≠ 0) (hd₂ : d₂ ≠ 0) :
    ∃ x y : K, σ x = x ∧ σ y = y ∧ d₁ * x ^ 2 + d₂ * y ^ 2 = c := by
  classical
  let S : Subfield K := RingHom.eqLocusField (σ : K →+* K) (RingHom.id K)
  have : Fintype S := Fintype.ofFinite S
  have : CharP S p := inferInstance
  have hchar : ringChar S ≠ 2 := by rw [ringChar.eq S p]; exact hp2
  have hodd : Fintype.card S % 2 = 1 := FiniteField.odd_card_of_char_ne_two hchar
  let a₁ : S := ⟨d₁, h₁⟩
  let a₂ : S := ⟨d₂, h₂⟩
  let a₃ : S := ⟨c, hc⟩
  have ha₁ : a₁ ≠ 0 := fun h => hd₁ (congrArg Subtype.val h)
  have ha₂ : a₂ ≠ 0 := fun h => hd₂ (congrArg Subtype.val h)
  have hf : degree (C a₁ * X ^ 2 : S[X]) = 2 := by
    rw [degree_C_mul_X_pow 2 ha₁]; rfl
  have hg : degree (C a₂ * X ^ 2 - C a₃ : S[X]) = 2 := by
    rw [degree_sub_C (by rw [degree_C_mul_X_pow 2 ha₂]; decide), degree_C_mul_X_pow 2 ha₂]; rfl
  obtain ⟨x, y, hxy⟩ := FiniteField.exists_root_sum_quadratic hf hg hodd
  refine ⟨x, y, x.2, y.2, ?_⟩
  simp only [eval_sub, eval_mul, eval_C, eval_pow, eval_X] at hxy
  have := congrArg Subtype.val hxy
  simp at this
  linear_combination this

end Rep

section Kappa

theorem exists_fixed_nonsquare {K : Type*} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = (p ^ f) ^ 2) :
    ∃ κ : K, κ ≠ 0 ∧ κ ^ (p ^ f) = κ ∧ κ ^ ((p ^ f - 1) / 2) = -1 := by
  classical
  have hp := (Fact.out : p.Prime)
  have hq3 : 3 ≤ p ^ f := by
    have h2 : 2 ≤ p := hp.two_le
    have h3 : p ≠ 2 := hp2
    have : 3 ≤ p := by omega
    calc 3 ≤ p := this
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf
  have hqodd : p ^ f % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · rw [Nat.pow_mod, h]; simp
  set q := p ^ f with hqdef
  have hcard : Nat.card Kˣ = q ^ 2 - 1 := by
    rw [Nat.card_units, hK]
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf g = q ^ 2 - 1 := by
    rw [← hcard]; exact orderOf_eq_card_of_forall_mem_zpowers hg
  have hdvd : (q + 1) ∣ orderOf g := by
    rw [hord]
    exact ⟨q - 1, by
      have : q ^ 2 - 1 = (q + 1) * (q - 1) := by
        have : 1 ≤ q := by omega
        zify [this, show 1 ≤ q ^ 2 from Nat.one_le_pow _ _ (by omega)]
        ring
      exact this⟩
  have hord' : orderOf (g ^ (q + 1)) = q - 1 := by
    rw [orderOf_pow_of_dvd (by omega) hdvd, hord]
    have : q ^ 2 - 1 = (q + 1) * (q - 1) := by
      have : 1 ≤ q := by omega
      zify [this, show 1 ≤ q ^ 2 from Nat.one_le_pow _ _ (by omega)]
      ring
    rw [this]
    exact Nat.mul_div_cancel_left _ (by omega)
  set κ : Kˣ := g ^ (q + 1) with hκdef
  have hκ1 : κ ^ (q - 1) = 1 := by rw [← hord']; exact pow_orderOf_eq_one κ
  obtain ⟨m, hm⟩ : ∃ m, q = 2 * m + 1 := ⟨q / 2, by omega⟩
  have hm1 : (q - 1) / 2 = m := by omega
  have hsq : (κ ^ m) ^ 2 = 1 := by
    rw [← pow_mul, show m * 2 = q - 1 by omega, hκ1]
  have hne : κ ^ m ≠ 1 := by
    intro h
    have hdvd' : orderOf κ ∣ m := orderOf_dvd_of_pow_eq_one h
    rw [hord'] at hdvd'
    have := Nat.le_of_dvd (by omega) hdvd'
    omega
  have hsqK : ((κ : K) ^ m) * ((κ : K) ^ m) = 1 := by
    have := congrArg (fun u : Kˣ => (u : K)) hsq
    simpa [sq, ← pow_add, ← two_mul, pow_mul] using this
  have hneK : (κ : K) ^ m ≠ 1 := by
    intro h
    apply hne
    exact Units.ext (by simpa using h)
  have hnegK : (κ : K) ^ m = -1 := by
    rcases mul_self_eq_one_iff.mp hsqK with h | h
    · exact absurd h hneK
    · exact h
  refine ⟨(κ : K), κ.ne_zero, ?_, ?_⟩
  · have : (κ : K) ^ (q - 1) = 1 := by
      have := congrArg (fun u : Kˣ => (u : K)) hκ1
      simpa using this
    calc (κ : K) ^ q = (κ : K) ^ (q - 1) * κ := by
          rw [← pow_succ]; congr 1; omega
      _ = κ := by rw [this, one_mul]
  · rw [hm1]
    exact hnegK

end Kappa

section Plane

variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {m : ℕ}

open CFSG.ClassicalGroups.Unitary CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  Module

theorem exists_aniso_pair {p : ℕ} [CharP K p] (T : RealStr σ m) (hσ : IsUnitaryInvolution σ)
    (hp2 : p ≠ 2) {κ : K} (hκσ : σ κ = κ) {U : Submodule K (Fin m → K)}
    (hU : Nondeg σ U) (hst : T.IsStable U) (hdim : 3 ≤ finrank K U) :
    ∃ a b : Fin m → K, a ∈ U ∧ b ∈ U ∧ T.IsReal a ∧ T.IsReal b ∧ herm σ a b = 0 ∧
      ∃ d : K, d ≠ 0 ∧ σ d = d ∧ herm σ a a = d ∧ herm σ b b = -(κ * d) := by
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
    have := (CharP.cast_eq_zero_iff K p 2).mp this
    have hp : p.Prime := by
      rcases (CharP.char_is_prime_or_zero K p) with h | h
      · exact h
      · subst h
        simp at this
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this
    exact hp2 this
  obtain ⟨e₁, e₂, e₃, ⟨he₁U, he₁R, he₁⟩, ⟨he₂U, he₂R, he₂⟩, ⟨he₃U, he₃R, he₃⟩, h12, h13, h23⟩ :=
    T.exists_real_orth_triple hσ h2 hU hst hdim
  have hd₁ := T.herm_real he₁R he₁R
  have hd₂ := T.herm_real he₂R he₂R
  have hd₃ := T.herm_real he₃R he₃R
  obtain ⟨x, y, hx, hy, hxy⟩ := exists_fixed_rep σ hp2 (d₁ := herm σ e₂ e₂) (d₂ := herm σ e₃ e₃)
    (c := -(κ * herm σ e₁ e₁)) hd₂ hd₃ (by rw [map_neg, map_mul, hκσ, hd₁]) he₂ he₃
  have h21 : herm σ e₂ e₁ = 0 := herm_eq_zero_comm σ hσ.invol h12
  have h31 : herm σ e₃ e₁ = 0 := herm_eq_zero_comm σ hσ.invol h13
  have h32 : herm σ e₃ e₂ = 0 := herm_eq_zero_comm σ hσ.invol h23
  refine ⟨e₁, x • e₂ + y • e₃, he₁U, U.add_mem (U.smul_mem _ he₂U) (U.smul_mem _ he₃U), he₁R,
    ?_, ?_, herm σ e₁ e₁, he₁, hd₁, rfl, ?_⟩
  · unfold RealStr.IsReal
    rw [T.map_add, T.map_smul, T.map_smul, he₂R, he₃R, hx, hy]
  · simp only [herm_add_right, herm_smul_right, h12, h13]
    ring
  · simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, h23, h32, hx, hy]
    linear_combination hxy

end Plane

section Fix

variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {m : ℕ} {p f : ℕ} [Fact p.Prime] [CharP K p]

open CFSG.ClassicalGroups.Unitary CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  Module

omit [Finite K] in
theorem perp_perp_eq (hσ : IsUnitaryInvolution σ) {P : Submodule K (Fin m → K)}
    (hP : Nondeg σ P) : perp σ (perp σ P) = P := by
  have h1 := finrank_add_finrank_herm_perp hσ hP
  have h2 := finrank_add_finrank_herm_perp hσ (nondeg_herm_perp hσ hP)
  symm
  refine Submodule.eq_of_le_of_finrank_eq ?_ (by omega)
  intro w hw t ht
  exact herm_eq_zero_comm σ hσ.invol (ht w hw)

omit [Finite K] in
theorem two_ne_zero_of_char {p : ℕ} [CharP K p] (hp2 : p ≠ 2) : (2 : K) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
  have hdvd := (CharP.cast_eq_zero_iff K p 2).mp h'
  have hp : p.Prime := by
    rcases CharP.char_is_prime_or_zero K p with h | h
    · exact h
    · subst h
      simp at hdvd
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdvd)

omit [Finite K] in
theorem pow_eq_one_of_fix (T : RealStr σ m) (hσ : IsUnitaryInvolution σ)
    (hσq : ∀ c, σ c = c ^ (p ^ f)) (hp2 : p ≠ 2) (hodd : p ^ f % 2 = 1) {κ : K} (hκ0 : κ ≠ 0)
    (hκ : κ ^ ((p ^ f - 1) / 2) = -1) {a b : Fin m → K} {d : K} (hd : d ≠ 0)
    (ha : T.IsReal a) (hb : T.IsReal b) (haa : herm σ a a = d)
    (hbb : herm σ b b = -(κ * d)) (hab : herm σ a b = 0) (y : Module.End K (Fin m → K))
    (hiso : ∀ u w, herm σ (y u) (y w) = herm σ u w)
    (hfix : ∀ w ∈ perp σ (Submodule.span K {a, b}), y w = w)
    (hcomm : ∀ u, y (T.τ u) = T.τ (y u)) : y ^ (p ^ f + 1) = 1 := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_char hp2
  set P : Submodule K (Fin m → K) := Submodule.span K {a, b} with hP
  have hba : herm σ b a = 0 := herm_eq_zero_comm σ hσ.invol hab
  have hbd : herm σ b b ≠ 0 := by
    rw [hbb]
    exact neg_ne_zero.mpr (mul_ne_zero hκ0 hd)
  have had : herm σ a a ≠ 0 := by rw [haa]; exact hd
  have hPnd : Nondeg σ P := by
    have : P = K ∙ a ⊔ K ∙ b := by rw [hP, Submodule.span_insert]
    rw [this]
    exact Nondeg.sup_of_orth hσ (nondeg_span_singleton had) (nondeg_span_singleton hbd)
      (orth_span_singleton_iff.mpr hab)
  have haP : a ∈ P := Submodule.subset_span (Set.mem_insert a {b})
  have hbP : b ∈ P := Submodule.subset_span (by simp)
  have hsplit : P ⊔ perp σ P = ⊤ := by
    have := sup_inf_perp_of_nondeg hσ (finrank K P) rfl hPnd (le_top : P ≤ ⊤)
    simpa using this
  have hyP : ∀ u ∈ P, y u ∈ P := by
    intro u hu
    rw [← perp_perp_eq hσ hPnd]
    intro t ht
    rw [← hfix t ht, hiso]
    exact herm_eq_zero_comm σ hσ.invol (ht u hu)
  obtain ⟨r, s, hya⟩ := Submodule.mem_span_pair.mp (hyP a haP)
  obtain ⟨r', s', hyb⟩ := Submodule.mem_span_pair.mp (hyP b hbP)
  have coef : ∀ (u : Fin m → K) (c e : K), T.τ u = u → u = c • a + e • b → σ c = c ∧ σ e = e := by
    intro u c e hu hce
    have h1 : σ c • a + σ e • b = c • a + e • b := by
      have := hu
      rw [hce, T.map_add, T.map_smul, T.map_smul, ha, hb] at this
      exact this
    have h2a := congrArg (herm σ a) h1
    have h2b := congrArg (herm σ b) h1
    simp only [herm_add_right, herm_smul_right, haa, hab, hba, hbb] at h2a h2b
    constructor
    · have : (σ c - c) * d = 0 := by linear_combination h2a
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hd)
    · have : (σ e - e) * (κ * d) = 0 := by linear_combination -h2b
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right (mul_ne_zero hκ0 hd))
  have hya' : T.τ (y a) = y a := by rw [← hcomm a, ha]
  have hyb' : T.τ (y b) = y b := by rw [← hcomm b, hb]
  obtain ⟨hrσ, hsσ⟩ := coef (y a) r s hya' hya.symm
  obtain ⟨hr'σ, hs'σ⟩ := coef (y b) r' s' hyb' hyb.symm
  have G1 : r ^ 2 - κ * s ^ 2 = 1 := by
    have h := hiso a a
    rw [← hya] at h
    simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, haa, hab, hba, hbb,
      hrσ, hsσ] at h
    apply mul_left_cancel₀ hd
    linear_combination h
  have G2 : r' ^ 2 - κ * s' ^ 2 = -κ := by
    have h := hiso b b
    rw [← hyb] at h
    simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, haa, hab, hba, hbb,
      hr'σ, hs'σ] at h
    apply mul_left_cancel₀ hd
    linear_combination h
  have G3 : r * r' - κ * s * s' = 0 := by
    have h := hiso a b
    rw [← hya, ← hyb] at h
    simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, haa, hab, hba, hbb,
      hrσ, hsσ] at h
    apply mul_left_cancel₀ hd
    linear_combination h
  have E1 : r ^ 2 = 1 + κ * s ^ 2 := by linear_combination G1
  have E2 : r' ^ 2 = κ * s' ^ 2 - κ := by linear_combination G2
  have E3 : r * r' = κ * s * s' := by linear_combination G3
  have hs'2 : s' ^ 2 = r ^ 2 := by
    have h1 : (r * r') ^ 2 = (κ * s * s') ^ 2 := by rw [E3]
    have h2' : (1 + κ * s ^ 2) * (κ * s' ^ 2 - κ) = κ ^ 2 * s ^ 2 * s' ^ 2 := by
      rw [← E1, ← E2]
      linear_combination h1
    have h3 : κ * (s' ^ 2 - r ^ 2) = 0 := by
      rw [E1]
      linear_combination h2'
    have := (mul_eq_zero.mp h3).resolve_left hκ0
    linear_combination this
  have hr'2 : r' ^ 2 = (κ * s) ^ 2 := by
    rw [E2, hs'2]
    linear_combination κ * G1
  have key : (s' = r ∧ r' = κ * s) ∨ (s' = -r ∧ r' = -(κ * s)) := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs'2 with h1 | h1 <;>
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hr'2 with h2' | h2'
    · exact Or.inl ⟨h1, h2'⟩
    · have h3 : (2 * κ) * (r * s) = 0 := by
        rw [h1, h2'] at E3
        linear_combination -E3
      have hrs0 := (mul_eq_zero.mp h3).resolve_left (mul_ne_zero h2 hκ0)
      rcases mul_eq_zero.mp hrs0 with h | h
      · exact Or.inr ⟨by rw [h1, h]; simp, h2'⟩
      · exact Or.inl ⟨h1, by rw [h2', h]; simp⟩
    · have h3 : (2 * κ) * (r * s) = 0 := by
        rw [h1, h2'] at E3
        linear_combination E3
      have hrs0 := (mul_eq_zero.mp h3).resolve_left (mul_ne_zero h2 hκ0)
      rcases mul_eq_zero.mp hrs0 with h | h
      · exact Or.inl ⟨by rw [h1, h]; simp, h2'⟩
      · exact Or.inr ⟨h1, by rw [h2', h]; simp⟩
    · exact Or.inr ⟨h1, h2'⟩
  set Y : Matrix (Fin 2) (Fin 2) K := !![r, r'; s, s'] with hY
  have hr : r ^ p ^ f = r := (hσq r).symm.trans hrσ
  have hs : s ^ p ^ f = s := (hσq s).symm.trans hsσ
  have hYpow : Y ^ (p ^ f + 1) = 1 := by
    rcases key with ⟨h1, h2'⟩ | ⟨h1, h2'⟩
    · rw [hY, h1, h2']
      exact rot_pow hr hs hκ hodd G1
    · rw [hY, h1, h2']
      obtain ⟨n, hn⟩ : ∃ n, p ^ f + 1 = 2 * n := ⟨(p ^ f + 1) / 2, by omega⟩
      rw [hn, pow_mul, refl_sq G1, one_pow]
  let ι : (Fin 2 → K) → (Fin m → K) := fun c => c 0 • a + c 1 • b
  have hyι : ∀ c : Fin 2 → K, y (ι c) = ι (Y.mulVec c) := by
    intro c
    simp only [ι, map_add, map_smul]
    rw [← hya, ← hyb]
    simp [hY, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    module
  have hpowι : ∀ (n : ℕ) (c : Fin 2 → K), (y ^ n) (ι c) = ι ((Y ^ n).mulVec c) := by
    intro n
    induction n with
    | zero => intro c; simp
    | succ n ih =>
      intro c
      rw [pow_succ, Module.End.mul_apply, hyι, ih, Matrix.mulVec_mulVec, ← pow_succ]
  have hpowfix : ∀ (n : ℕ), ∀ w ∈ perp σ P, (y ^ n) w = w := by
    intro n
    induction n with
    | zero => intro w _; simp
    | succ n ih => intro w hw; rw [pow_succ, Module.End.mul_apply, hfix w hw, ih w hw]
  refine LinearMap.ext fun w => ?_
  have hw : w ∈ P ⊔ perp σ P := by rw [hsplit]; trivial
  obtain ⟨u, hu, w', hw', rfl⟩ := Submodule.mem_sup.mp hw
  obtain ⟨c0, c1, rfl⟩ := Submodule.mem_span_pair.mp hu
  have hc : c0 • a + c1 • b = ι ![c0, c1] := by simp [ι]
  rw [map_add, hc, hpowι, hYpow, hpowfix _ w' hw', Matrix.one_mulVec, Module.End.one_apply]

end Fix
