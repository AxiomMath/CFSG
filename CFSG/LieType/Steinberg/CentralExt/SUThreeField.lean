module

public import CFSG.LieType.Steinberg.CentralExt.PSUMultiplier
public import CFSG.LieType.Steinberg.CentralExt.PosLiftGen

public section

open Matrix CFSG.LieType.RootSystem CFSG.LieType.Steinberg CFSG.LieType.Universal
  CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras CFSG.LieType.BorelTits
open scoped commutatorElement

namespace CFSG.LieType.Steinberg.CentralExt.SUClosed

attribute [local instance] TorusLift.centerCommGroup

section General

variable {F : Type} [Field F] {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c) {n : ℕ}

variable (σ) in
@[expose] def IsFullTorus (u : Fin n → Fˣ) : Prop :=
  (∀ s, σ (u s : F) * u (Fin.rev s) = 1) ∧ ∏ s, (u s : F) = 1

variable (σ n) in
abbrev FullTorus : Type := {u : Fin n → Fˣ // IsFullTorus σ u}

@[expose] noncomputable def fullTorusElt (u : FullTorus σ n) : SU σ n :=
  ⟨diagGL u.1, diagGL_mem u.2.1 u.2.2⟩

theorem mat_fullTorusElt (u : FullTorus σ n) :
    mat σ n (fullTorusElt u) = diagonal fun s => (u.1 s : F) :=
  rfl

theorem IsFullTorus.val_rev {u : Fin n → Fˣ} (hu : IsFullTorus σ u) (s : Fin n) :
    (u (Fin.rev s) : F) = (σ (u s : F))⁻¹ :=
  eq_inv_of_mul_eq_one_right (hu.1 s)

theorem unitaryDiag_mul {u v : Fin n → Fˣ} (hu : ∀ s, σ (u s : F) * u (Fin.rev s) = 1)
    (hv : ∀ s, σ (v s : F) * v (Fin.rev s) = 1) (s : Fin n) :
    σ ((u * v) s : F) * (u * v) (Fin.rev s) = 1 := by
  simp only [Pi.mul_apply, Units.val_mul, map_mul]
  calc σ (u s : F) * σ (v s : F) * ((u (Fin.rev s) : F) * (v (Fin.rev s) : F)) =
      (σ (u s : F) * u (Fin.rev s)) * (σ (v s : F) * v (Fin.rev s)) := by ring
    _ = 1 := by rw [hu s, hv s, one_mul]

theorem IsFullTorus.mul {u v : Fin n → Fˣ} (hu : IsFullTorus σ u) (hv : IsFullTorus σ v) :
    IsFullTorus σ (u * v) :=
  ⟨unitaryDiag_mul hu.1 hv.1, by
    simp only [Pi.mul_apply, Units.val_mul, Finset.prod_mul_distrib, hu.2, hv.2, one_mul]⟩

theorem fullTorusElt_comm (u u' : FullTorus σ n) :
    fullTorusElt u' * fullTorusElt u * (fullTorusElt u')⁻¹ = fullTorusElt u := by
  rw [mul_inv_eq_iff_eq_mul]
  apply mat_injective
  rw [map_mul, map_mul, mat_fullTorusElt, mat_fullTorusElt, diagonal_mul_diagonal,
    diagonal_mul_diagonal]
  congr 1
  funext s
  ring

open _root_.Classical in
@[expose] noncomputable def fullChi (u : FullTorus σ n) (γ : Fin (n / 2) → ℤ) : F :=
  if h : ∃ ij : Fin n × Fin n, IsShortPos γ ij.1 ij.2 then
    (u.1 h.choose.1 : F) * (u.1 h.choose.2 : F)⁻¹
  else if h' : ∃ i : Fin n, IsLongPos γ i then
    (u.1 h'.choose : F) * (u.1 (Fin.rev h'.choose) : F)⁻¹
  else 1

theorem fullTorusElt_conj_x (he : Even n) {γ : Fin (n / 2) → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartan n) (divisible n)) (u : FullTorus σ n) (c : F) :
    fullTorusElt u * x hσ γ c * (fullTorusElt u)⁻¹ = x hσ γ (fullChi u γ * c) := by
  classical
  by_cases hs : ∃ ij : Fin n × Fin n, IsShortPos γ ij.1 ij.2
  · rw [fullChi, dite_eq_left hs]
    exact conj_x_short hσ (mat_fullTorusElt u) hs.choose_spec
      (fun c => by rw [x, dite_eq_left hs]) c
  · rcases short_or_long he hγ with h | ⟨k, hk⟩
    · exact absurd h hs
    · have hl : ∃ i : Fin n, IsLongPos γ i := ⟨k, hk⟩
      rw [fullChi, dite_eq_right hs, dite_eq_left hl]
      exact conj_x_long hσ (mat_fullTorusElt u) hl.choose_spec
        (fun c => by rw [x, dite_eq_right hs, dite_eq_left hl]) c

theorem fullChi_eq_one_iff (he : Even n) {γ : Fin (n / 2) → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartan n) (divisible n)) (u : FullTorus σ n) {i j : Fin n}
    (hij : weight n i - weight n j = toStd n γ) : fullChi u γ = 1 ↔ u.1 i = u.1 j := by
  classical
  have key : ∀ a b : Fin n, (u.1 a : F) * (u.1 b : F)⁻¹ = 1 ↔ u.1 a = u.1 b := fun a b => by
    rw [mul_inv_eq_one₀ (Units.ne_zero _), Units.val_inj]
  have hrev : ∀ a b : Fin n, u.1 (Fin.rev a) = u.1 (Fin.rev b) ↔ u.1 a = u.1 b := fun a b => by
    rw [← Units.val_inj, ← Units.val_inj (a := u.1 a), u.2.val_rev, u.2.val_rev, _root_.inv_inj,
      σ.injective.eq_iff]
  by_cases hs : ∃ ij : Fin n × Fin n, IsShortPos γ ij.1 ij.2
  · rw [fullChi, dite_eq_left hs, key]
    have hsp := hs.choose_spec
    rcases eq_of_weight_sub_eq_sub hsp.1 hsp.2.1 hsp.2.2.1 hsp.2.2.2.1
      (hij.trans hsp.2.2.2.2.symm) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · rw [hrev, eq_comm]
  · rcases short_or_long he hγ with h | ⟨k, hk⟩
    · exact absurd h hs
    · have hl : ∃ i : Fin n, IsLongPos γ i := ⟨k, hk⟩
      rw [fullChi, dite_eq_right hs, dite_eq_left hl, key]
      have hlp := hl.choose_spec
      obtain ⟨rfl, rfl⟩ := eq_of_weight_sub_eq_two_smul hlp.1 (hij.trans hlp.2.symm)
      rfl

include hσ in
theorem map_fullChi_of_not_short {γ : Fin (n / 2) → ℤ}
    (hs : ¬ ∃ ij : Fin n × Fin n, IsShortPos γ ij.1 ij.2) (u : FullTorus σ n) :
    σ (fullChi u γ) = fullChi u γ := by
  classical
  rw [fullChi, dite_eq_right hs]
  split_ifs with hl
  · rw [u.2.val_rev, inv_inv, map_mul, hσ, mul_comm]
  · exact map_one σ

variable (σ) in
@[expose] noncomputable def pairDiag (c : Fin n) (l : Fˣ) : Fin n → Fˣ := fun s =>
  if s = c then l else if s = Fin.rev c then (Units.map (σ : F →* F) l)⁻¹ else 1

theorem pairDiag_self (c : Fin n) (l : Fˣ) : pairDiag σ c l c = l := ite_eq_left rfl

theorem coe_pairDiag_rev {c : Fin n} (hc : c ≠ Fin.rev c) (l : Fˣ) :
    (pairDiag σ c l (Fin.rev c) : F) = (σ (l : F))⁻¹ := by
  rw [pairDiag, ite_eq_right (Ne.symm hc), ite_eq_left rfl, Units.val_inv_eq_inv_val, Units.coe_map]
  rfl

theorem pairDiag_of_ne {c s : Fin n} (h1 : s ≠ c) (h2 : s ≠ Fin.rev c) (l : Fˣ) :
    pairDiag σ c l s = 1 := by
  rw [pairDiag, ite_eq_right h1, ite_eq_right h2]

include hσ in
theorem pairDiag_unitary {c : Fin n} (hc : c ≠ Fin.rev c) (l : Fˣ) (s : Fin n) :
    σ (pairDiag σ c l s : F) * pairDiag σ c l (Fin.rev s) = 1 := by
  by_cases h1 : s = c
  · subst h1
    rw [pairDiag_self, coe_pairDiag_rev hc, mul_inv_cancel₀ (by simp)]
  by_cases h2 : s = Fin.rev c
  · subst h2
    rw [coe_pairDiag_rev hc, Fin.rev_rev, pairDiag_self, map_inv₀, hσ, inv_mul_cancel₀ (by simp)]
  have h3 : Fin.rev s ≠ c := fun h => h2 (by rw [← h, Fin.rev_rev])
  have h4 : Fin.rev s ≠ Fin.rev c := fun h => h1 (Fin.rev_injective h)
  rw [pairDiag_of_ne h1 h2, pairDiag_of_ne h3 h4, Units.val_one, map_one, one_mul]

theorem prod_pairDiag {c : Fin n} (hc : c ≠ Fin.rev c) (l : Fˣ) :
    ∏ s, (pairDiag σ c l s : F) = l * (σ (l : F))⁻¹ := by
  rw [Fintype.prod_eq_mul c (Fin.rev c) hc fun s hs => by
    rw [pairDiag_of_ne hs.1 hs.2, Units.val_one], pairDiag_self, coe_pairDiag_rev hc]

theorem pairDiag_rev {c : Fin n} (hc : c ≠ Fin.rev c) (l : Fˣ) :
    pairDiag σ c l (Fin.rev c) = (Units.map (σ : F →* F) l)⁻¹ := by
  rw [pairDiag, ite_eq_right (Ne.symm hc), ite_eq_left rfl]

@[expose] noncomputable def negPair (he : Even n) (c : Fin n) : FullTorus σ n :=
  ⟨pairDiag σ c (-1), pairDiag_unitary hσ (rev_ne_self_of_even he c) (-1), by
    rw [prod_pairDiag (rev_ne_self_of_even he c)]
    simp⟩

@[expose] noncomputable def transferPair (he : Even n) (c d : Fin n) (l : Fˣ) : FullTorus σ n :=
  ⟨pairDiag σ c l * pairDiag σ d l⁻¹, unitaryDiag_mul (pairDiag_unitary hσ
    (rev_ne_self_of_even he c) l) (pairDiag_unitary hσ (rev_ne_self_of_even he d) l⁻¹), by
    simp only [Pi.mul_apply, Units.val_mul, Finset.prod_mul_distrib,
      prod_pairDiag (rev_ne_self_of_even he c), prod_pairDiag (rev_ne_self_of_even he d),
      Units.val_inv_eq_inv_val, map_inv₀]
    have h1 : (l : F) ≠ 0 := Units.ne_zero l
    have h2 : σ (l : F) ≠ 0 := by simp
    field_simp⟩

@[expose] noncomputable def doublePair (he : Even n) (i j f : Fin n) (l : Fˣ) : FullTorus σ n :=
  ⟨(transferPair hσ he i f l).1 * (transferPair hσ he j f l).1,
    (transferPair hσ he i f l).2.mul (transferPair hσ he j f l).2⟩

omit [Field F] in
theorem exists_ne_four (hn : 5 ≤ n) (a b c d : Fin n) :
    ∃ g : Fin n, g ≠ a ∧ g ≠ b ∧ g ≠ c ∧ g ≠ d := by
  classical
  obtain ⟨g, -, hg⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := {a, b, c, d}) (t := Finset.univ)
    (by rw [Finset.card_univ, Fintype.card_fin]; exact lt_of_le_of_lt Finset.card_le_four (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hg
  exact ⟨g, hg.1, hg.2.1, hg.2.2.1, hg.2.2.2⟩

theorem units_ne_map_inv_of_norm_ne_one {μ : Fˣ} (hμ : σ (μ : F) * μ ≠ 1) :
    μ ≠ (Units.map (σ : F →* F) μ)⁻¹ := by
  intro h
  apply hμ
  have h1 := congrArg (fun v : Fˣ => (v : F)) h
  simp only [Units.val_inv_eq_inv_val, Units.coe_map, MonoidHom.coe_ofClass] at h1
  rw [mul_comm]
  exact (mul_eq_one_iff_eq_inv₀ (by simp)).2 h1

theorem neg_one_units_ne_one (hneg : (-1 : F) ≠ 1) : (-1 : Fˣ) ≠ 1 := fun h =>
  hneg (by simpa using congrArg (fun v : Fˣ => (v : F)) h)

theorem negPair_sep (he : Even n) (hneg : (-1 : F) ≠ 1) {i j k l : Fin n} (hik : i ≠ k)
    (hik' : i ≠ Fin.rev k) (hjk : j ≠ k) (hjk' : j ≠ Fin.rev k) (hlk : l ≠ k)
    (hlk' : l ≠ Fin.rev k) :
    (negPair hσ he k).1 i = (negPair hσ he k).1 j ∧
      (negPair hσ he k).1 k ≠ (negPair hσ he k).1 l := by
  simp only [negPair]
  rw [pairDiag_of_ne hik hik', pairDiag_of_ne hjk hjk', pairDiag_self, pairDiag_of_ne hlk hlk']
  exact ⟨rfl, neg_one_units_ne_one hneg⟩

theorem transferPair_sep (he : Even n) {μ : Fˣ} (hμ : σ (μ : F) * μ ≠ 1) {i j k f : Fin n}
    (hik : i ≠ k) (hik' : i ≠ Fin.rev k) (hjk : j ≠ k) (hjk' : j ≠ Fin.rev k) (hif : i ≠ f)
    (hif' : i ≠ Fin.rev f) (hjf : j ≠ f) (hjf' : j ≠ Fin.rev f) (hkf : k ≠ f)
    (hkf' : k ≠ Fin.rev f) :
    (transferPair hσ he k f μ).1 i = (transferPair hσ he k f μ).1 j ∧
      (transferPair hσ he k f μ).1 k ≠ (transferPair hσ he k f μ).1 (Fin.rev k) := by
  have hkf2 : Fin.rev k ≠ f := fun h => hkf' (by rw [← h, Fin.rev_rev])
  have hkf3 : Fin.rev k ≠ Fin.rev f := fun h => hkf (Fin.rev_injective h)
  simp only [transferPair, Pi.mul_apply]
  rw [pairDiag_of_ne hik hik', pairDiag_of_ne hjk hjk', pairDiag_of_ne hif hif',
    pairDiag_of_ne hjf hjf', pairDiag_self, pairDiag_rev (rev_ne_self_of_even he k),
    pairDiag_of_ne hkf hkf', pairDiag_of_ne hkf2 hkf3]
  refine ⟨rfl, ?_⟩
  simp only [mul_one]
  exact units_ne_map_inv_of_norm_ne_one hμ

theorem doublePair_of_left (he : Even n) {i j f s : Fin n} (h1 : s ≠ j) (h2 : s ≠ Fin.rev j)
    (h3 : s ≠ f) (h4 : s ≠ Fin.rev f) (l : Fˣ) :
    (doublePair hσ he i j f l).1 s = pairDiag σ i l s := by
  simp only [doublePair, transferPair, Pi.mul_apply]
  rw [pairDiag_of_ne h3 h4, pairDiag_of_ne h1 h2, mul_one, one_mul, mul_one]

theorem doublePair_of_right (he : Even n) {i j f s : Fin n} (h1 : s ≠ i) (h2 : s ≠ Fin.rev i)
    (h3 : s ≠ f) (h4 : s ≠ Fin.rev f) (l : Fˣ) :
    (doublePair hσ he i j f l).1 s = pairDiag σ j l s := by
  simp only [doublePair, transferPair, Pi.mul_apply]
  rw [pairDiag_of_ne h3 h4, pairDiag_of_ne h1 h2]
  simp only [mul_one, one_mul]

omit [Field F] in
theorem ne_rev_of_ne_rev {i k : Fin n} (h : k ≠ Fin.rev i) : i ≠ Fin.rev k :=
  fun e => h (by rw [e, Fin.rev_rev])

omit [Field F] in
theorem rev_ne_rev_of_ne {i j : Fin n} (h : i ≠ j) : Fin.rev i ≠ Fin.rev j :=
  fun e => h (Fin.rev_injective e)

theorem doublePair_sep (he : Even n) {μ : Fˣ} (hμ : σ (μ : F) * μ ≠ 1) {i j f k l : Fin n}
    (hij : i ≠ j) (hij' : j ≠ Fin.rev i) (hif : f ≠ i) (hif' : f ≠ Fin.rev i) (hjf : f ≠ j)
    (hjf' : f ≠ Fin.rev j)
    (hkl : (k = i ∨ k = j) ∧ (l = Fin.rev i ∨ l = Fin.rev j) ∨
      (k = Fin.rev i ∨ k = Fin.rev j) ∧ (l = i ∨ l = j)) :
    (doublePair hσ he i j f μ).1 i = (doublePair hσ he i j f μ).1 j ∧
      (doublePair hσ he i j f μ).1 k ≠ (doublePair hσ he i j f μ).1 l := by
  have hev := rev_ne_self_of_even he
  have hi : (doublePair hσ he i j f μ).1 i = μ := by
    rw [doublePair_of_left hσ he hij (ne_rev_of_ne_rev hij') hif.symm (ne_rev_of_ne_rev hif'),
      pairDiag_self]
  have hj : (doublePair hσ he i j f μ).1 j = μ := by
    rw [doublePair_of_right hσ he hij.symm hij' hjf.symm (ne_rev_of_ne_rev hjf'), pairDiag_self]
  have hi' : (doublePair hσ he i j f μ).1 (Fin.rev i) = (Units.map (σ : F →* F) μ)⁻¹ := by
    rw [doublePair_of_left hσ he hij'.symm (rev_ne_rev_of_ne hij) hif'.symm
      (rev_ne_rev_of_ne hif.symm), pairDiag_rev (hev i)]
  have hj' : (doublePair hσ he i j f μ).1 (Fin.rev j) = (Units.map (σ : F →* F) μ)⁻¹ := by
    rw [doublePair_of_right hσ he (ne_rev_of_ne_rev hij').symm (rev_ne_rev_of_ne hij.symm)
      hjf'.symm (rev_ne_rev_of_ne hjf.symm), pairDiag_rev (hev j)]
  refine ⟨hi.trans hj.symm, ?_⟩
  have hne := units_ne_map_inv_of_norm_ne_one hμ
  rcases hkl with ⟨rfl | rfl, rfl | rfl⟩ | ⟨rfl | rfl, rfl | rfl⟩
  · rwa [hi, hi']
  · rwa [hi, hj']
  · rwa [hj, hi']
  · rwa [hj, hj']
  · rw [hi', hi]; exact hne.symm
  · rw [hi', hj]; exact hne.symm
  · rw [hj', hi]; exact hne.symm
  · rw [hj', hj]; exact hne.symm

include hσ in
theorem exists_fullTorus_sep (he : Even n) (hn : 6 ≤ n) {μ : Fˣ} (hμ : σ (μ : F) * μ ≠ 1)
    (hneg : (-1 : F) ≠ 1) {i j k l : Fin n} (hij : i ≠ j) (hkl : k ≠ l)
    (h1 : ¬ (k = i ∧ l = j)) (h2 : ¬ (k = Fin.rev j ∧ l = Fin.rev i))
    (h3 : ¬ (k = j ∧ l = i)) (h4 : ¬ (k = Fin.rev i ∧ l = Fin.rev j)) :
    (∃ u : FullTorus σ n, u.1 i = u.1 j ∧ u.1 k ≠ u.1 l) ∨
      (j ≠ Fin.rev i ∧ l = Fin.rev k ∧ k ≠ i ∧ k ≠ Fin.rev i ∧ k ≠ j ∧ k ≠ Fin.rev j) := by
  have hev := rev_ne_self_of_even he
  by_cases hk : k ≠ i ∧ k ≠ Fin.rev i ∧ k ≠ j ∧ k ≠ Fin.rev j
  · obtain ⟨hk1, hk2, hk3, hk4⟩ := hk
    by_cases hl : l = Fin.rev k
    · subst hl
      by_cases hji : j = Fin.rev i
      · obtain ⟨f, hf1, hf2, hf5, hf6⟩ := exists_ne_four (by omega) i (Fin.rev i) k (Fin.rev k)
        have hf3 : f ≠ j := fun h => hf2 (h.trans hji)
        have hf4 : f ≠ Fin.rev j := fun h => hf1 (h.trans (by rw [hji, Fin.rev_rev]))
        exact Or.inl ⟨transferPair hσ he k f μ, transferPair_sep hσ he hμ hk1.symm
          (ne_rev_of_ne_rev hk2) hk3.symm (ne_rev_of_ne_rev hk4) hf1.symm (ne_rev_of_ne_rev hf2)
          hf3.symm (ne_rev_of_ne_rev hf4) hf5.symm (ne_rev_of_ne_rev hf6)⟩
      · exact Or.inr ⟨hji, rfl, hk1, hk2, hk3, hk4⟩
    · exact Or.inl ⟨negPair hσ he k, negPair_sep hσ he hneg hk1.symm (ne_rev_of_ne_rev hk2)
        hk3.symm (ne_rev_of_ne_rev hk4) hkl.symm hl⟩
  left
  by_cases hl : l ≠ i ∧ l ≠ Fin.rev i ∧ l ≠ j ∧ l ≠ Fin.rev j ∧ l ≠ Fin.rev k
  · obtain ⟨hl1, hl2, hl3, hl4, hl5⟩ := hl
    obtain ⟨h5, h6⟩ := negPair_sep hσ he hneg (i := i) (j := j) (k := l) (l := k) hl1.symm
      (ne_rev_of_ne_rev hl2) hl3.symm (ne_rev_of_ne_rev hl4) hkl (ne_rev_of_ne_rev hl5)
    exact ⟨negPair hσ he l, h5, Ne.symm h6⟩
  have hk' : k = i ∨ k = Fin.rev i ∨ k = j ∨ k = Fin.rev j := by
    by_contra h
    push Not at h
    exact hk h
  have hl' : l = i ∨ l = Fin.rev i ∨ l = j ∨ l = Fin.rev j ∨ l = Fin.rev k := by
    by_contra h
    push Not at h
    exact hl h
  clear hk hl
  by_cases hji : j = Fin.rev i
  · subst hji
    exfalso
    rcases hk' with rfl | rfl | rfl | rfl <;> rcases hl' with rfl | rfl | rfl | rfl | rfl <;>
      simp_all
  obtain ⟨f, hf1, hf2, hf3, hf4⟩ := exists_ne_four (by omega) i (Fin.rev i) j (Fin.rev j)
  refine ⟨doublePair hσ he i j f μ, doublePair_sep hσ he hμ hij hji hf1 hf2 hf3 hf4 ?_⟩
  rcases hk' with rfl | rfl | rfl | rfl <;> rcases hl' with rfl | rfl | rfl | rfl | rfl <;>
    simp_all

theorem exists_pos_weight (he : Even n) {γ : Fin (n / 2) → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartan n) (divisible n)) :
    ∃ i j : Fin n, i ≠ j ∧ weight n i - weight n j = toStd n γ := by
  rcases short_or_long he hγ with ⟨⟨i, j⟩, hs⟩ | ⟨i, hl⟩
  · exact ⟨i, j, hs.1, hs.2.2.2.2⟩
  · exact ⟨i, Fin.rev i, hl.1, by rw [weight_rev', sub_neg_eq_add, ← two_nsmul]; exact hl.2⟩

theorem rootMatrix_mul_longRootMatrix_comm {i j k : Fin n} (hki' : k ≠ Fin.rev i) (hkj : k ≠ j)
    (c d : F) :
    rootMatrix σ i j c * longRootMatrix k d = longRootMatrix k d * rootMatrix σ i j c := by
  have h1 : Fin.rev k ≠ i := (ne_rev_of_ne_rev hki').symm
  have h2 : Fin.rev k ≠ Fin.rev j := rev_ne_rev_of_ne hkj
  have e1 : (single i j c : Matrix (Fin n) (Fin n) F) * single k (Fin.rev k) d = 0 :=
    Matrix.single_mul_single_of_ne c i j k (Ne.symm hkj) d
  have e2 : (single (Fin.rev j) (Fin.rev i) (σ c) : Matrix (Fin n) (Fin n) F) *
      single k (Fin.rev k) d = 0 :=
    Matrix.single_mul_single_of_ne _ _ _ _ (Ne.symm hki') d
  have e3 : (single k (Fin.rev k) d : Matrix (Fin n) (Fin n) F) * single i j c = 0 :=
    Matrix.single_mul_single_of_ne _ _ _ _ h1 c
  have e4 : (single k (Fin.rev k) d : Matrix (Fin n) (Fin n) F) *
      single (Fin.rev j) (Fin.rev i) (σ c) = 0 :=
    Matrix.single_mul_single_of_ne _ _ _ _ h2 _
  simp only [rootMatrix, longRootMatrix, add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, e1,
    e2, e3, e4]
  abel

theorem commute_x_short_long {a b : Fin (n / 2) → ℤ} {i j k : Fin n} (hs : IsShortPos a i j)
    (hl : IsLongPos b k) (hki' : k ≠ Fin.rev i) (hkj : k ≠ j) (c d : F) :
    x hσ a c * x hσ b d = x hσ b d * x hσ a c := by
  obtain ⟨i₀, j₀, hs₀, hx⟩ := x_short hσ ⟨(i, j), hs⟩
  obtain ⟨k₀, hl₀, hy⟩ := x_long hσ hl
  have hk : k₀ = k := (eq_of_weight_sub_eq_two_smul hl.1
    (by rw [weight_rev', sub_neg_eq_add, ← two_nsmul, hl₀.2, ← hl.2])).1
  subst hk
  apply mat_injective
  rw [map_mul, map_mul, hx, hy, mat_apply, mat_apply, coe_rootHom, coe_longRootHom, toAdd_ofAdd,
    toAdd_ofAdd]
  rcases eq_of_weight_sub_eq_sub hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1
      (hs₀.2.2.2.2.trans hs.2.2.2.2.symm) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact rootMatrix_mul_longRootMatrix_comm hki' hkj _ _
  · exact rootMatrix_mul_longRootMatrix_comm (by rwa [Fin.rev_rev]) hki' _ _

include hσ in
theorem exists_fullChi_sep (he : Even n) (hn : 6 ≤ n) {μ : Fˣ} (hμ : σ (μ : F) * μ ≠ 1)
    (hneg : (-1 : F) ≠ 1) {a b : Fin (n / 2) → ℤ}
    (ha : a ∈ roots (isFiniteType_cartan n) (divisible n))
    (hb : b ∈ roots (isFiniteType_cartan n) (divisible n)) (ha0 : 0 < ht a) (hb0 : 0 < ht b)
    (hab : a ≠ b) : (∃ u : FullTorus σ n, fullChi u a = 1 ∧ fullChi u b ≠ 1) ∨
      ((∃ u : FullTorus σ n, fullChi u a ≠ 1 ∧ fullChi u b = 1) ∧
        ∀ c d, x hσ a c * x hσ b d = x hσ b d * x hσ a c) := by
  obtain ⟨i, j, hij, hwa⟩ := exists_pos_weight he ha
  obtain ⟨k, l, hkl, hwb⟩ := exists_pos_weight he hb
  have hne : toStd n b ≠ toStd n a := fun h => hab (toStd_inj' h).symm
  have hne' : toStd n b ≠ -toStd n a := fun h => by
    have h0 : toStd n (a + b) = toStd n 0 := by rw [toStd_add', h, toStd_zero', add_neg_cancel]
    have h1 := congrArg ht (toStd_inj' h0)
    rw [ht_add] at h1
    have h3 : ht (0 : Fin (n / 2) → ℤ) = 0 := by simp [ht]
    omega
  have e1 : ¬ (k = i ∧ l = j) := by
    rintro ⟨rfl, rfl⟩
    exact hne (hwb.symm.trans hwa)
  have e2 : ¬ (k = Fin.rev j ∧ l = Fin.rev i) := by
    rintro ⟨rfl, rfl⟩
    exact hne (by rw [← hwb, ← hwa, weight_rev', weight_rev']; abel)
  have e3 : ¬ (k = j ∧ l = i) := by
    rintro ⟨rfl, rfl⟩
    exact hne' (by rw [← hwb, ← hwa]; abel)
  have e4 : ¬ (k = Fin.rev i ∧ l = Fin.rev j) := by
    rintro ⟨rfl, rfl⟩
    exact hne' (by rw [← hwb, ← hwa, weight_rev', weight_rev']; abel)
  rcases exists_fullTorus_sep hσ he hn hμ hneg hij hkl e1 e2 e3 e4 with ⟨u, hu1, hu2⟩ |
    ⟨hji, rfl, hki, hki', hkj, hkj'⟩
  · exact Or.inl ⟨u, (fullChi_eq_one_iff he ha u hwa).2 hu1,
      fun h => hu2 ((fullChi_eq_one_iff he hb u hwb).1 h)⟩
  right
  have hs : IsShortPos a i j :=
    ⟨hij, rev_ne_self_of_even he i, rev_ne_self_of_even he j, hji, hwa⟩
  have hl : IsLongPos b k :=
    ⟨rev_ne_self_of_even he k, by rw [← hwb, weight_rev', sub_neg_eq_add, two_nsmul]⟩
  refine ⟨⟨negPair hσ he i, fun h => ?_, ?_⟩, commute_x_short_long hσ hs hl hki' hkj⟩
  · have h' := (fullChi_eq_one_iff he ha (negPair hσ he i) hwa).1 h
    simp only [negPair] at h'
    rw [pairDiag_self, pairDiag_of_ne hij.symm hji] at h'
    exact neg_one_units_ne_one hneg h'
  · refine (fullChi_eq_one_iff he hb (negPair hσ he i) hwb).2 ?_
    simp only [negPair]
    rw [pairDiag_of_ne hki hki', pairDiag_of_ne (ne_rev_of_ne_rev hki').symm
      (rev_ne_rev_of_ne hki)]

include hσ in
theorem exists_fullChi_ne_one (he : Even n) (hn : 6 ≤ n) {μ : Fˣ} (hμ : σ (μ : F) * μ ≠ 1)
    (hneg : (-1 : F) ≠ 1) {γ : Fin (n / 2) → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartan n) (divisible n)) :
    ∃ u : FullTorus σ n, fullChi u γ ≠ 1 := by
  obtain ⟨k, l, hkl, hw⟩ := exists_pos_weight he hγ
  obtain ⟨f, hf1, hf2, -, -⟩ := exists_ne_four (by omega) k (Fin.rev k) l (Fin.rev l)
  rcases exists_fullTorus_sep hσ he hn hμ hneg (i := f) (j := Fin.rev f)
    (rev_ne_self_of_even he f) hkl (fun h => hf1 h.1.symm)
    (fun h => hf1 (by rw [h.1, Fin.rev_rev])) (fun h => ne_rev_of_ne_rev hf2 h.1)
    (fun h => ne_rev_of_ne_rev hf2 h.1) with ⟨u, -, hu⟩ | h
  · exact ⟨u, fun h => hu ((fullChi_eq_one_iff he hγ u hw).1 h)⟩
  · exact absurd rfl h.1

theorem eq_zero_of_x_eq_one_short {γ : Fin (n / 2) → ℤ}
    (hs : ∃ ij : Fin n × Fin n, IsShortPos γ ij.1 ij.2) {c : F} (h : x hσ γ c = 1) : c = 0 := by
  obtain ⟨i, j, hij, hx⟩ := x_short hσ hs
  have h1 : mat σ n (x hσ γ c) i j = mat σ n 1 i j := by rw [h]
  rwa [hx, mat_apply (rootHom _ _ _ _ _ _), coe_rootHom, toAdd_ofAdd,
    rootMatrix_apply_pq hij.1 hij.2.2.2.1, map_one, one_apply_ne hij.1] at h1

section Lift

variable {E : Type*} [Group E] {π : E →* SU σ n}

variable (π) in
@[expose] def IsFullRootLift (γ : Fin (n / 2) → ℤ) (Y : F → E) : Prop :=
  (∀ s t, Y (s + t) = Y s * Y t) ∧ (∀ s, π (Y s) = x hσ γ s) ∧ (∀ s, x hσ γ s = 1 → Y s = 1) ∧
    ∀ (u : FullTorus σ n) (e : E), π e = fullTorusElt u → ∀ s,
      e * Y s * e⁻¹ = Y (fullChi u γ * s)

variable (hcen : π.ker ≤ Subgroup.center E) (hπ : Function.Surjective π)

include hcen in
theorem commPairing_eq_zero_short_units [Finite F] (he : Even n) (hn : 5 ≤ n)
    (hF4 : Nat.card F ≠ 4) {γ : Fin (n / 2) → ℤ}
    (hs : ∃ ij : Fin n × Fin n, IsShortPos γ ij.1 ij.2) :
    TorusLift.commPairing hcen hπ (x_add hσ γ) = 0 := by
  obtain ⟨i, j, hij, hx⟩ := x_short hσ hs
  obtain ⟨k, hk1, hk2, hk3, hk4⟩ := exists_ne_four hn i (Fin.rev i) j (Fin.rev j)
  obtain ⟨p, _, _⟩ := TorusLift.exists_prime_charP (k := F)
  refine Pairing.pairing_eq_zero_of_units p hF4
    (TorusLift.commPairing_self hcen hπ (x_add hσ γ)) fun v hv s t => ?_
  set u := transferPair hσ he i k (Units.mk0 v hv)
  have hui : (u.1 i : F) = v := by
    simp only [u, transferPair, Pi.mul_apply]
    rw [pairDiag_self, pairDiag_of_ne hk1.symm (ne_rev_of_ne_rev hk2), mul_one, Units.val_mk0]
  have huj : (u.1 j : F) = 1 := by
    simp only [u, transferPair, Pi.mul_apply]
    rw [pairDiag_of_ne hij.1.symm hij.2.2.2.1, pairDiag_of_ne hk3.symm (ne_rev_of_ne_rev hk4),
      mul_one, Units.val_one]
  refine TorusLift.commPairing_smul hcen hπ (x_add hσ γ) (g := fullTorusElt u) (fun c => ?_) s t
  rw [conj_x_short hσ (mat_fullTorusElt u) hij hx, hui, huj, inv_one, mul_one]

include hcen hπ in
theorem exists_isFullRootLift (he : Even n) {γ : Fin (n / 2) → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartan n) (divisible n))
    (h0 : TorusLift.commPairing hcen hπ (x_add hσ γ) = 0) {t₀ : FullTorus σ n}
    (ht₀ : fullChi t₀ γ ≠ 1) : ∃ Y : F → E, IsFullRootLift hσ π γ Y := by
  refine ⟨TorusLift.canonLift hπ (x := x hσ γ) (fullTorusElt t₀) (fullChi t₀ γ),
    TorusLift.canonLift_add hcen hπ (x_add hσ γ) h0 (fullTorusElt_conj_x hσ he hγ t₀) ht₀,
    TorusLift.map_canonLift hπ (x_add hσ γ) (fullTorusElt_conj_x hσ he hγ t₀) ht₀,
    fun s hs => ?_,
    fun t e he' s => TorusLift.conj_canonLift hcen hπ (fullTorusElt_comm t₀ t)
      (fullTorusElt_conj_x hσ he hγ t) he' s⟩
  have h1 : x hσ γ ((fullChi t₀ γ - 1)⁻¹ * s) = 1 := by
    by_cases hsh : ∃ ij : Fin n × Fin n, IsShortPos γ ij.1 ij.2
    · have hs0 := eq_zero_of_x_eq_one_short hσ hsh hs
      rw [hs0] at hs
      rwa [hs0, mul_zero]
    · refine x_mul_eq_one hσ hs ?_
      rw [map_inv₀, map_sub, map_one, map_fullChi_of_not_short hσ hsh]
  have hz : TorusLift.lift hπ (1 : SU σ n) ∈ Subgroup.center E :=
    hcen (by rw [MonoidHom.mem_ker, TorusLift.map_lift])
  show ⁅TorusLift.lift hπ (fullTorusElt t₀),
    TorusLift.lift hπ (x hσ γ ((fullChi t₀ γ - 1)⁻¹ * s))⁆ = 1
  rw [h1, commutatorElement_eq_one_iff_mul_comm]
  exact Subgroup.mem_center_iff.1 hz _

variable (π) in
open _root_.Classical in
@[expose] noncomputable def fullX (γ : Fin (n / 2) → ℤ) : F → E :=
  if h : ∃ Y : F → E, IsFullRootLift hσ π γ Y then h.choose else fun _ => 1

theorem fullX_isFullRootLift {γ : Fin (n / 2) → ℤ} (h : ∃ Y : F → E, IsFullRootLift hσ π γ Y) :
    IsFullRootLift hσ π γ (fullX hσ π γ) := by
  classical
  rw [fullX, dite_eq_left h]
  exact h.choose_spec

end Lift

end General

section Finite

variable {F : Type} [Field F] [Finite F] [CharP F 3] (hF : Nat.card F = (3 ^ 1) ^ 2) {n : ℕ}

omit [Finite F] in
theorem neg_one_ne_one_of_charP_three : (-1 : F) ≠ 1 := by
  intro h
  have h3 : ((2 : ℕ) : F) = 0 := by
    push_cast
    linear_combination -h
  rw [CharP.cast_eq_zero_iff F 3] at h3
  norm_num at h3

include hF in
theorem exists_units_norm_ne_one :
    ∃ μ : Fˣ, unitaryInvolution F 3 1 (μ : F) * μ ≠ 1 := by
  obtain ⟨μ, hμ⟩ := exists_norm_eq_neg_one hF
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hμ
    exact one_ne_zero (neg_eq_zero.1 hμ.symm)
  exact ⟨Units.mk0 μ hμ0, by
    rw [Units.val_mk0, hμ]
    exact neg_one_ne_one_of_charP_three⟩

include hF in
theorem su_three_exists_section_of_pKernel (he : Even n) (hn : 6 ≤ n) {E : Type*}
    [Group E] [Finite E] {π : E →* SU (unitaryInvolution F 3 1) n}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) (hpk : IsPGroup 3 π.ker) :
    ∃ s : SU (unitaryInvolution F 3 1) n →* E, ∀ g, π (s g) = g := by
  have hσ := unitaryInvolution_involutive hF
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hD : (rootDatum hF n).divisible = ∅ := show divisible n = ∅ by
    unfold divisible
    rw [ite_eq_left he]
  have hneg : (-1 : F) ≠ 1 := neg_one_ne_one_of_charP_three
  obtain ⟨μ, hμ⟩ := exists_units_norm_ne_one hF
  have hF4 : Nat.card F ≠ 4 := by
    rw [hF]
    norm_num
  have hspec : ∀ γ ∈ PosLift.posRoots (rootDatum hF n),
      IsFullRootLift hσ π γ (fullX hσ π γ) := by
    intro γ hγ
    have hγr : γ ∈ roots (isFiniteType_cartan n) (divisible n) := hγ.1
    have h0 : TorusLift.commPairing hcen hπ (x_add hσ γ) = 0 := by
      rcases short_or_long he hγr with hs | ⟨k, hk⟩
      · exact commPairing_eq_zero_short_units hσ hcen hπ he (by omega) hF4 hs
      · exact commPairing_eq_zero_long hσ hcen hπ he (by omega) hk
    obtain ⟨t, ht⟩ := exists_fullChi_ne_one hσ he (by omega) hμ hneg hγr
    exact fullX_isFullRootLift hσ (exists_isFullRootLift hσ hcen hπ he hγr h0 ht)
  refine PosLift.exists_section_of_posLift' (isCTGroupDatum hF n (by omega) ζ hζ)
    (steinbergExtras hF n (by omega) ζ hζ) (SUBruhat.bruhatExtras hF (by omega) ζ hζ) hD
    (p := 3) (fun γ hγ => isPGroup_rootGroup hσ (toStd_ne_zero_of_mem_roots hγ))
    (coprime_card_torus hF) hπ hcen hpk (x := x hσ)
    (fun γ hγ g => ⟨fun hg => exists_x_eq_of_mem hσ he hγ.1 hγ.2
      (fun z hz => exists_sub_eq hF hz) hg, fun ⟨c, hc⟩ => hc ▸ x_mem hσ γ c⟩)
    (fun γ _ => x_add hσ γ) (X := fullX hσ π) (fun γ hγ => (hspec γ hγ).1)
    (fun γ hγ => (hspec γ hγ).2.1) (fun γ hγ => (hspec γ hγ).2.2.1)
    (tor := fun u => TorusLift.lift hπ (fullTorusElt u)) (χ := fun u γ => fullChi u γ)
    (fun u γ hγ c => (hspec γ hγ).2.2.2 u _ (TorusLift.map_lift hπ _) c)
    fun a ha b hb hab => ?_
  rcases exists_fullChi_sep hσ he hn hμ hneg ha.1 hb.1 ha.2 hb.2 hab with h |
    ⟨⟨u, hu1, hu2⟩, hxy⟩
  · exact Or.inl h
  right
  intro t c
  rw [PosLift.commute_of_rev_sep hcen (hspec a ha).1 (hspec a ha).2.1 (hspec b hb).2.1 hxy hu1
    (fun s => (hspec a ha).2.2.2 u _ (TorusLift.map_lift hπ _) s)
    (fun s => by rw [(hspec b hb).2.2.2 u _ (TorusLift.map_lift hπ _) s, hu2, one_mul]) t c,
    mul_inv_cancel_right]
  exact Subgroup.mem_iSup_of_mem b (Subgroup.mem_iSup_of_mem ⟨hb, Or.inl rfl⟩
    (CFSG.LieType.Steinberg.xh_mem_chevRoot b c))

include hF in
theorem su_three_exists_section_of_central
    (he : Even n) (hn : 6 ≤ n)
    {E : Type} [Group E] [Finite E] {π : E →* SU (unitaryInvolution F 3 1) n}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) :
    ∃ s : SU (unitaryInvolution F 3 1) n →* E, ∀ g, π (s g) = g :=
  CoprimeSplit.exists_section_of_parts (p := 3) hπ hcen
    (fun _ _ _ _ hπ' hcen' hp' => su_three_exists_section_of_pKernel hF he hn hπ' hcen' hp')
    (fun _ _ _ _ hπ' hcen' hc' => su_exists_section_of_coprime hF he (by omega) hπ' hcen' hc')

open CFSG.Assembly.LowTwoRank in
include hF in
theorem statedSU_three_exists_section_of_central
    (he : Even n) (hn : 6 ≤ n)
    {E : Type} [Group E] [Finite E] {π : E →* StatedSU n (3 ^ 1) F}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) :
    ∃ s : StatedSU n (3 ^ 1) F →* E, ∀ g, π (s g) = g := by
  set ψ := equivStatedSU hF n
  have hker : (ψ.symm.toMonoidHom.comp π).ker = π.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff _ ψ.symm.injective]
  obtain ⟨s, hs⟩ := su_three_exists_section_of_central hF he hn
    (π := ψ.symm.toMonoidHom.comp π) (ψ.symm.surjective.comp hπ) (hker ▸ hcen)
  refine ⟨s.comp ψ.symm.toMonoidHom, fun g => ψ.symm.injective ?_⟩
  exact hs (ψ.symm g)

open CFSG.Assembly.LowTwoRank in
include hF in
theorem psu_three_hopfMultiplier
    (he : Even n) (hn : 6 ≤ n) :
    commutator (StatedProj (StatedSU n (3 ^ 1) F)) = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier (StatedProj (StatedSU n (3 ^ 1) F)) ≃*
        Multiplicative (ZMod (Nat.gcd n (3 ^ 1 + 1)))) := by
  set H := StatedSU n (3 ^ 1) F
  set Z := (StatedScalars (Fin n) F).subgroupOf H
  set q : H →* StatedProj H := QuotientGroup.mk' Z
  have hq' : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hker : q.ker = Z := QuotientGroup.ker_mk' _
  have hZc : Z ≤ Subgroup.center H := fun z hz => by
    have hz' : (z : GL (Fin n) F) ∈ Subgroup.center (GL (Fin n) F) := by
      have h1 := Subgroup.mem_subgroupOf.1 hz
      rwa [StatedScalars, ← Matrix.GeneralLinearGroup.center_eq_range_scalar] at h1
    exact Subgroup.mem_center_iff.2 fun h => Subtype.ext (Subgroup.mem_center_iff.1 hz' h)
  have : Group.IsPerfect H := isPerfect_statedSU hF (by omega)
  have hperf : Group.IsPerfect (StatedProj H) := Group.IsPerfect.ofSurjective hq'
  refine ⟨Group.IsPerfect.commutator_eq_top, ?_⟩
  have : Finite (CFSG.RankThree.PerfectCover.HopfCover (StatedProj H)) :=
    CFSG.RankThree.PerfectCover.finite_hopfCover hperf
  have e1 : CFSG.RankThree.PerfectCover.hopfMultiplier (StatedProj H) ≃* q.ker :=
    MulEquiv.ofBijective _ (SL2Closed.hopfMultiplierToKer_bijective q hq' (hker ▸ hZc)
      fun π hπ hcen => statedSU_three_exists_section_of_central hF he hn hπ hcen)
  have hcard : Nat.card Z = Nat.gcd n (3 ^ 1 + 1) :=
    (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_three hF (by omega)).2.2
  have hcyc : IsCyclic Z := (isCyclic_scalars_statedSU hF (by omega)).1
  rw [← hcard]
  exact ⟨(CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).trans
    (e1.trans ((MulEquiv.subgroupCongr hker).trans (zmodCyclicMulEquiv hcyc).symm))⟩

end Finite

end CFSG.LieType.Steinberg.CentralExt.SUClosed
