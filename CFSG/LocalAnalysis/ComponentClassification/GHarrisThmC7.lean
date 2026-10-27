module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisThmC3
public import Certificates.Certificate22613

public noncomputable section

namespace CFSG.ComponentClassification.GHarris.GL42

open Matrix Subgroup

theorem orbitKs_of_isOrbit {k : ℕ} (hk : k < 70)
    (h : (witAt k).isOrbit = true) : k ∈ orbitKs :=
  Certificates.certificate22613.1 k (List.mem_range.mpr hk) h

theorem a5_words {k : ℕ} (hk : k ∈ orbitKs) :
    a5Idx k < 4 ∧ (∀ e ∈ e0c, e ∈ a5At (a5Idx k)) ∧ (∀ c ∈ conjAt k, c ∈ a5At (a5Idx k)) ∧
      (a5At (a5Idx k)).length = 60 ∧
      ∀ i ∈ List.range 60, wordProd (e0c ++ conjAt k) ((wordsAt k).getD i []) =
        (a5At (a5Idx k)).getD i M4c.one :=
  Certificates.certificate22613.2.1 k hk

theorem a5_iso {j : ℕ} (hj : j < 4) :
    (∀ p q : alternatingGroup (Fin 5), phiA5 j (p * q) = (phiA5 j p).mul (phiA5 j q)) ∧
      (∀ p : alternatingGroup (Fin 5), phiA5 j p = M4c.one → p = 1) ∧
      (∀ p : alternatingGroup (Fin 5), phiA5 j p ∈ a5At j) ∧
      ∀ c ∈ a5At j, ∃ p : alternatingGroup (Fin 5), phiA5 j p = c :=
  Certificates.certificate22613.2.2.1 j (List.mem_range.mpr hj)

theorem a5_pair {k k' : ℕ} (hk : k ∈ orbitKs)
    (hk' : k' ∈ orbitKs) (hne : a5Idx k ≠ a5Idx k') :
    IsOrder4 (wordProd (e0c ++ conjAt k ++ conjAt k') (pairWord k k')) :=
  Certificates.certificate22613.2.2.2.1 k hk k' hk' hne

theorem noFiveSeven_of {a b c d : V4c} (ha : a ∈ rowsW)
    (hb : b ∈ rowsW) : NoFiveSeven ⟨a, b, c, d⟩ :=
  Certificates.certificate22613.2.2.2.2 a ha b hb c (V4c.mem_all c) d (V4c.mem_all d)

theorem eq_one_of_mulVec_eq {A : M4} (h : ∀ v : Fin 4 → ZMod 2, A *ᵥ v = v) : A = 1 := by
  ext i j
  have h1 := congrFun (h (Pi.single j 1)) i
  rw [mulVec_single_one] at h1
  rw [show A i j = A.col j i from rfl, h1, Matrix.one_apply, Pi.single_apply]

theorem exists_fixed_of_pow_seven {M : GL4} (hM : M ^ 7 = 1) :
    ∃ v : Fin 4 → ZMod 2, v ≠ 0 ∧ (M : M4) *ᵥ v = v := by
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  let f : Function.End (Fin 4 → ZMod 2) := fun v => (M : M4) *ᵥ v
  have hpow : ∀ n : ℕ, f ^ n = fun v => ((M ^ n : GL4) : M4) *ᵥ v := by
    intro n
    induction n with
    | zero => funext v; simp [Matrix.one_mulVec]; rfl
    | succ n ih =>
      rw [pow_succ, ih]
      funext v
      change ((M ^ n : GL4) : M4) *ᵥ ((M : M4) *ᵥ v) = _
      rw [Matrix.mulVec_mulVec, pow_succ, Units.val_mul]
  have hf : f ^ 7 ^ 1 = 1 := by
    rw [pow_one, hpow 7, hM]
    funext v
    simp [Matrix.one_mulVec]
    rfl
  have hmod := Equiv.Perm.card_fixedPoints_modEq hf
  by_contra hne
  push Not at hne
  have hfix : Function.fixedPoints f = {0} := by
    ext v
    change f v = v ↔ v ∈ ({0} : Set (Fin 4 → ZMod 2))
    rw [Set.mem_singleton_iff]
    constructor
    · intro hv
      by_contra hv0
      exact hne v hv0 hv
    · rintro rfl
      exact Matrix.mulVec_zero _
  have hcard : Fintype.card (Function.fixedPoints f) = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨0, Matrix.mulVec_zero _⟩, fun ⟨v, hv⟩ => Subtype.ext ?_⟩
    have : v ∈ Function.fixedPoints f := hv
    rw [hfix] at this
    exact this
  rw [hcard] at hmod
  have h16 : Fintype.card (Fin 4 → ZMod 2) = 16 := by
    rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]
    rfl
  rw [h16] at hmod
  exact absurd hmod (by decide)

structure SylE0 (G : Type*) [Group G] where
  ρ : G →* GL4
  inj : Function.Injective ρ
  S : Sylow 2 G
  hS : ∀ y : M4, (∃ x ∈ S, ((ρ x : GL4) : M4) = y) ↔ y ∈ listSet e0c

namespace SylE0

variable {G : Type*} [Group G] (P : SylE0 G)

abbrev mat (g : G) : M4 := ((P.ρ g : GL4) : M4)

theorem mat_mul (x y : G) : P.mat (x * y) = P.mat x * P.mat y := by
  rw [mat, map_mul, Units.val_mul]

theorem mat_one : P.mat 1 = 1 := by
  rw [mat, map_one, Units.val_one]

theorem mat_inj {x y : G} (h : P.mat x = P.mat y) : x = y := P.inj (Units.ext h)

theorem exists_S {e : M4c} (he : e ∈ e0c) : ∃ x ∈ P.S, P.mat x = e.toMat :=
  (P.hS _).mpr ⟨e, he, rfl⟩

theorem exists_e0 {x : G} (hx : x ∈ P.S) : ∃ e ∈ e0c, e.toMat = P.mat x :=
  (P.hS _).mp ⟨x, hx, rfl⟩

theorem mem_S_of_mat {x : G} {e : M4c} (he : e ∈ e0c) (hx : P.mat x = e.toMat) : x ∈ P.S := by
  obtain ⟨s, hs, hse⟩ := P.exists_S he
  rw [P.mat_inj (hse.trans hx.symm)] at hs
  exact hs

theorem sq_S {x : G} (hx : x ∈ P.S) : x * x = 1 := by
  obtain ⟨e, he, hex⟩ := P.exists_e0 hx
  exact P.mat_inj (by rw [P.mat_mul, ← hex, ← M4c.toMat_mul, e0_mul_self e he, M4c.toMat_one,
    P.mat_one])

variable [Finite G]

theorem false_of_order4 {gens : List M4c} (hg : ∀ c ∈ gens, ∃ g, P.mat g = c.toMat)
    {w : List ℕ} (h : IsOrder4 (wordProd gens w)) : False := by
  obtain ⟨h4, h2⟩ := h
  obtain ⟨g, hg'⟩ := exists_wordProd P.ρ hg w
  replace hg' : P.mat g = (wordProd gens w).toMat := hg'
  have hg4 : g ^ 4 = 1 := P.mat_inj (by
    rw [show g ^ 4 = g * g * (g * g) by simp only [pow_succ, pow_zero, one_mul, mul_assoc],
      P.mat_mul, P.mat_mul, hg', ← M4c.toMat_mul, ← M4c.toMat_mul, h4, M4c.toMat_one,
      P.mat_one])
  exact h2 (M4c.toMat_injective (by
    rw [M4c.toMat_mul, ← hg', ← P.mat_mul, mul_self_eq_one_of_pow_four P.S (fun s hs => P.sq_S hs)
      hg4, P.mat_one, M4c.toMat_one]))

theorem false_of_comm {C : List M4c} (hC : ∀ c ∈ C, ∃ g, P.mat g = c.toMat) {n : ℕ}
    (h : WitP C (.comm n)) : False := by
  obtain ⟨hnC, hne, hsq, hcomm⟩ := h
  obtain ⟨g, hg⟩ := hC _ hnC
  have hg2 : g * g = 1 :=
    P.mat_inj (by rw [P.mat_mul, hg, ← M4c.toMat_mul, hsq, M4c.toMat_one, P.mat_one])
  have hgc : ∀ s ∈ P.S, s * g = g * s := by
    intro s hs
    obtain ⟨e, he, hes⟩ := P.exists_e0 hs
    exact P.mat_inj (by rw [P.mat_mul, P.mat_mul, ← hes, hg, ← M4c.toMat_mul, ← M4c.toMat_mul,
      hcomm e he])
  obtain ⟨e, he, heg⟩ := P.exists_e0 (mem_of_comm P.S hg2 hgc)
  exact hne (M4c.toMat_injective (heg.trans hg) ▸ he)

omit [Finite G] in
theorem exists_conj (r : G) :
    ∃ k < 70, (∀ c ∈ conjAt k, ∃ s ∈ P.S, P.mat (r * s * r⁻¹) = c.toMat) ∧
      ∀ s ∈ P.S, ∃ c ∈ conjAt k, c.toMat = P.mat (r * s * r⁻¹) := by
  have hdet : (P.mat r⁻¹).det ≠ 0 := (Matrix.isUnits_det_units (P.ρ r⁻¹)).ne_zero
  obtain ⟨k, hk, hkset⟩ := exists_conjSet_eq hdet 0 (by norm_num)
  have hAinv : (P.mat r⁻¹)⁻¹ = P.mat r := by
    rw [mat, ← Matrix.coe_units_inv, ← map_inv, inv_inv]
  have hconj : ∀ y : G, P.mat (r * y * r⁻¹) = (P.mat r⁻¹)⁻¹ * P.mat y * P.mat r⁻¹ := fun y => by
    rw [hAinv, P.mat_mul, P.mat_mul]
  refine ⟨k, hk, fun c hc => ?_, fun s hs => ?_⟩
  · have hcs : c.toMat ∈ conjSet (P.mat r⁻¹) (conjAt 0) := by
      rw [hkset]
      exact ⟨c, hc, rfl⟩
    obtain ⟨e, he, hec⟩ := hcs
    obtain ⟨s, hs, hse⟩ := P.exists_S he
    exact ⟨s, hs, by rw [hconj, hse, hec]⟩
  · have hmem : P.mat (r * s * r⁻¹) ∈ listSet (conjAt k) := by
      rw [← hkset]
      obtain ⟨e, he, hes⟩ := P.exists_e0 hs
      exact ⟨e, he, by rw [hconj, hes]⟩
    exact hmem

theorem exists_orbit
    (hn : ∃ h : G, ∃ x ∈ P.S, h * x * h⁻¹ ∉ P.S) :
    ∃ h : G, ∃ k ∈ orbitKs, ∃ ws : List (ℕ × List ℕ), k < 70 ∧ witAt k = .orbit ws ∧
      ∀ c ∈ conjAt k, ∃ s ∈ P.S, P.mat (h * s * h⁻¹) = c.toMat := by
  obtain ⟨h, x, hxS, hx⟩ := hn
  obtain ⟨k, hk, hC, hC'⟩ := P.exists_conj h
  have hCm : ∀ c ∈ conjAt k, ∃ g, P.mat g = c.toMat := fun c hc => by
    obtain ⟨s, -, hs⟩ := hC c hc
    exact ⟨_, hs⟩
  have hgens : ∀ c ∈ e0c ++ conjAt k, ∃ g, P.mat g = c.toMat := by
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨s, -, hs⟩ := P.exists_S hc
      exact ⟨s, hs⟩
    · exact hCm c hc
  obtain ⟨c₀, hc₀, hc₀x⟩ := hC' x hxS
  have hc₀e : c₀ ∉ e0c := fun he => hx (P.mem_S_of_mat he hc₀x.symm)
  have hw := conjAt_wit hk
  cases hwk : witAt k with
  | norm =>
    rw [hwk] at hw
    exact absurd (hw.1 c₀ hc₀) hc₀e
  | word w =>
    rw [hwk] at hw
    exact (P.false_of_order4 hgens hw).elim
  | comm n =>
    rw [hwk] at hw
    exact (P.false_of_comm hCm hw).elim
  | orbit ws =>
    exact ⟨h, k, orbitKs_of_isOrbit hk (by rw [hwk]; rfl), ws, hk, hwk, hC⟩

omit [Finite G] in
theorem conj_mem_of_word (L : Subgroup G) (r : G) {gens : List M4c}
    (hex : ∀ c ∈ gens, ∃ g, P.mat g = c.toMat)
    (hgens : ∀ c ∈ gens, ∀ g : G, P.mat g = c.toMat → r * g * r⁻¹ ∈ L) (w : List ℕ) :
    ∀ g : G, P.mat g = (wordProd gens w).toMat → r * g * r⁻¹ ∈ L := by
  unfold wordProd
  suffices h : ∀ A : M4c, ∀ g₀ : G, P.mat g₀ = A.toMat → r * g₀ * r⁻¹ ∈ L →
      ∀ g : G, P.mat g = (w.foldl (fun A i => A.mul (gens.getD i M4c.one)) A).toMat →
        r * g * r⁻¹ ∈ L from
    h _ 1 (by rw [P.mat_one, M4c.toMat_one]) (by rw [mul_one, mul_inv_cancel]; exact one_mem _)
  induction w with
  | nil =>
    intro A g₀ hg₀ hr g hg
    rw [P.mat_inj (hg.trans hg₀.symm)]
    exact hr
  | cons i w ih =>
    intro A g₀ hg₀ hr g hg
    rw [List.foldl_cons] at hg
    obtain ⟨g₁, hg₁, hr₁⟩ : ∃ g₁ : G, P.mat g₁ = (gens.getD i M4c.one).toMat ∧
        r * g₁ * r⁻¹ ∈ L := by
      by_cases hil : i < gens.length
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hil, Option.getD_some]
        obtain ⟨g₁, hg₁⟩ := hex _ (List.getElem_mem hil)
        exact ⟨g₁, hg₁, hgens _ (List.getElem_mem hil) g₁ hg₁⟩
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hil), Option.getD_none]
        exact ⟨1, by rw [P.mat_one, M4c.toMat_one],
          by rw [mul_one, mul_inv_cancel]; exact one_mem _⟩
    refine ih (A.mul (gens.getD i M4c.one)) (g₀ * g₁) (by rw [P.mat_mul, hg₀, hg₁, M4c.toMat_mul])
      ?_ g hg
    rw [show r * (g₀ * g₁) * r⁻¹ = (r * g₀ * r⁻¹) * (r * g₁ * r⁻¹) by group]
    exact mul_mem hr hr₁

omit [Finite G] in
theorem exists_mat_gens {C : List M4c} (hC : ∀ c ∈ C, ∃ g, P.mat g = c.toMat) :
    ∀ c ∈ e0c ++ C, ∃ g, P.mat g = c.toMat := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · obtain ⟨s, -, hs⟩ := P.exists_S hc
    exact ⟨s, hs⟩
  · exact hC c hc

omit [Finite G] in
theorem exists_mat_a5 {k : ℕ} (hk : k ∈ orbitKs)
    (hC : ∀ c ∈ conjAt k, ∃ g, P.mat g = c.toMat) :
    ∀ c ∈ a5At (a5Idx k), ∃ g, P.mat g = c.toMat := by
  intro c hc
  obtain ⟨-, -, -, hlen, hw⟩ := a5_words hk
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
  have h := hw i (List.mem_range.mpr (hlen ▸ hi))
  have hgetD : (a5At (a5Idx k)).getD i M4c.one = (a5At (a5Idx k))[i] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  rw [hgetD] at h
  rw [← h]
  exact exists_wordProd P.ρ (P.exists_mat_gens hC) _

@[expose] def a5Hom (j : ℕ) (hj : j < 4)
    (hmem : ∀ c ∈ a5At j, ∃ g, P.mat g = c.toMat) : alternatingGroup (Fin 5) →* G :=
  MonoidHom.mk' (fun p => (hmem _ ((a5_iso hj).2.2.1 p)).choose) fun p q => P.mat_inj (by
    rw [P.mat_mul, (hmem _ ((a5_iso hj).2.2.1 (p * q))).choose_spec,
      (hmem _ ((a5_iso hj).2.2.1 p)).choose_spec, (hmem _ ((a5_iso hj).2.2.1 q)).choose_spec,
      (a5_iso hj).1 p q, M4c.toMat_mul])

omit [Finite G] in
theorem mat_a5Hom {j : ℕ} (hj : j < 4)
    (hmem : ∀ c ∈ a5At j, ∃ g, P.mat g = c.toMat) (p : alternatingGroup (Fin 5)) :
    P.mat (P.a5Hom j hj hmem p) = (phiA5 j p).toMat :=
  (hmem _ ((a5_iso hj).2.2.1 p)).choose_spec

omit [Finite G] in
theorem a5Hom_injective {j : ℕ} (hj : j < 4)
    (hmem : ∀ c ∈ a5At j, ∃ g, P.mat g = c.toMat) : Function.Injective (P.a5Hom j hj hmem) := by
  rw [injective_iff_map_eq_one]
  intro p hp
  apply (a5_iso hj).2.1 p
  apply M4c.toMat_injective
  rw [← P.mat_a5Hom hj hmem, hp, P.mat_one, M4c.toMat_one]

omit [Finite G] in
theorem mem_range_a5Hom {j : ℕ} (hj : j < 4)
    (hmem : ∀ c ∈ a5At j, ∃ g, P.mat g = c.toMat) {g : G} :
    g ∈ (P.a5Hom j hj hmem).range ↔ ∃ c ∈ a5At j, P.mat g = c.toMat := by
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨phiA5 j p, (a5_iso hj).2.2.1 p, P.mat_a5Hom hj hmem p⟩
  · rintro ⟨c, hc, hg⟩
    obtain ⟨p, rfl⟩ := (a5_iso hj).2.2.2 c hc
    exact ⟨p, P.mat_inj (by rw [P.mat_a5Hom hj hmem, hg])⟩

omit [Finite G] in
theorem gens_mem_a5 {k : ℕ} (hk : k ∈ orbitKs)
    (hmem : ∀ c ∈ a5At (a5Idx k), ∃ g, P.mat g = c.toMat) :
    ∀ c ∈ e0c ++ conjAt k, ∀ g : G, P.mat g = c.toMat →
      g ∈ (P.a5Hom (a5Idx k) (a5_words hk).1 hmem).range := by
  intro c hc g hg
  refine (P.mem_range_a5Hom _ hmem).mpr ⟨c, ?_, hg⟩
  rcases List.mem_append.mp hc with hc | hc
  · exact (a5_words hk).2.1 c hc
  · exact (a5_words hk).2.2.1 c hc

theorem a5_normal {h : G}
    {k : ℕ} (hk : k ∈ orbitKs) (hC : ∀ c ∈ conjAt k, ∃ s ∈ P.S, P.mat (h * s * h⁻¹) = c.toMat)
    (hmem : ∀ c ∈ a5At (a5Idx k), ∃ g, P.mat g = c.toMat) :
    (P.a5Hom (a5Idx k) (a5_words hk).1 hmem).range.Normal := by
  set L := (P.a5Hom (a5Idx k) (a5_words hk).1 hmem).range with hL
  have hCm : ∀ c ∈ conjAt k, ∃ g, P.mat g = c.toMat := fun c hc => by
    obtain ⟨s, -, hs⟩ := hC c hc
    exact ⟨_, hs⟩
  have hA : ∀ r : G, ∀ s ∈ P.S, r * s * r⁻¹ ∈ L := by
    intro r s hs
    obtain ⟨k', hk'70, hC', hC''⟩ := P.exists_conj r
    obtain ⟨c', hc', hc's⟩ := hC'' s hs
    have hC'm : ∀ c ∈ conjAt k', ∃ g, P.mat g = c.toMat := fun c hc => by
      obtain ⟨s, -, hs⟩ := hC' c hc
      exact ⟨_, hs⟩
    refine (P.mem_range_a5Hom _ hmem).mpr ⟨c', ?_, hc's.symm⟩
    have hw := conjAt_wit hk'70
    cases hwk : witAt k' with
    | norm =>
      rw [hwk] at hw
      exact (a5_words hk).2.1 c' (hw.1 c' hc')
    | word w =>
      rw [hwk] at hw
      exact (P.false_of_order4 (P.exists_mat_gens hC'm) hw).elim
    | comm n =>
      rw [hwk] at hw
      exact (P.false_of_comm hC'm hw).elim
    | orbit ws =>
      have hk' : k' ∈ orbitKs := orbitKs_of_isOrbit hk'70 (by rw [hwk]; rfl)
      by_cases hj : a5Idx k = a5Idx k'
      · rw [hj]
        exact (a5_words hk').2.2.1 c' hc'
      · refine (P.false_of_order4 (gens := e0c ++ conjAt k ++ conjAt k') ?_
          (a5_pair hk hk' hj)).elim
        intro c hc
        rcases List.mem_append.mp hc with hc | hc
        · exact P.exists_mat_gens hCm c hc
        · exact hC'm c hc
  have hB : ∀ r : G, ∀ c ∈ e0c ++ conjAt k, ∀ g : G, P.mat g = c.toMat → r * g * r⁻¹ ∈ L := by
    intro r c hc g hg
    rcases List.mem_append.mp hc with hc | hc
    · exact hA r g (P.mem_S_of_mat hc hg)
    · obtain ⟨s, hs, hsc⟩ := hC c hc
      rw [P.mat_inj (hg.trans hsc.symm),
        show r * (h * s * h⁻¹) * r⁻¹ = (r * h) * s * (r * h)⁻¹ by group]
      exact hA (r * h) s hs
  constructor
  intro g hg r
  obtain ⟨c, hc, hgc⟩ := (P.mem_range_a5Hom _ hmem).mp hg
  obtain ⟨-, -, -, hlen, hw⟩ := a5_words hk
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
  have hwi := hw i (List.mem_range.mpr (hlen ▸ hi))
  have hgetD : (a5At (a5Idx k)).getD i M4c.one = (a5At (a5Idx k))[i] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  rw [hgetD] at hwi
  exact P.conj_mem_of_word L r (P.exists_mat_gens hCm) (hB r) _ g (by rw [hgc, ← hwi])

omit [Finite G] in
theorem a5_transitive {k : ℕ}
    (hk : k ∈ orbitKs) (hk70 : k < 70) {ws : List (ℕ × List ℕ)} (hws : witAt k = .orbit ws)
    (hCm : ∀ c ∈ conjAt k, ∃ g, P.mat g = c.toMat)
    (hmem : ∀ c ∈ a5At (a5Idx k), ∃ g, P.mat g = c.toMat) {v : Fin 4 → ZMod 2} (hv : v ≠ 0) :
    ∃ l ∈ (P.a5Hom (a5Idx k) (a5_words hk).1 hmem).range, P.mat l *ᵥ V4c.v0.toVec = v := by
  have hw := conjAt_wit hk70
  rw [hws] at hw
  obtain ⟨hall, hwsP⟩ := hw
  rcases hall (V4c.ofVec v) (V4c.mem_all _) with h0 | ⟨p, hp, hpv⟩
  · exact absurd (by rw [← V4c.toVec_ofVec v, h0, V4c.toVec_zero]) hv
  · obtain ⟨g, hg⟩ := exists_wordProd P.ρ (P.exists_mat_gens hCm) p.2
    refine ⟨g, ?_, ?_⟩
    · have h1 := P.conj_mem_of_word _ 1 (P.exists_mat_gens hCm) (fun c hc g' hg' => by
        rw [one_mul, inv_one, mul_one]
        exact P.gens_mem_a5 hk hmem c hc g' hg') p.2 g hg
      rwa [one_mul, inv_one, mul_one] at h1
    · change ((P.ρ g : GL4) : M4) *ᵥ V4c.v0.toVec = v
      rw [hg, ← M4c.toVec_mulVec, hwsP p hp, hpv, V4c.toVec_ofVec]

end SylE0

end CFSG.ComponentClassification.GHarris.GL42
