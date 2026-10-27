module

public import CFSG.LargeExtraspecial.A2ModSqueeze
public import CFSG.LargeExtraspecial.S63CD4Class
public import CFSG.RankThree.OrthogonalInvolutions.Conjugacy
public import Certificates.Certificate21230
public import Certificates.Certificate21231

public section

namespace CFSG.LargeExtraspecial.A2Mod

open Module CFSG.Quasithin CFSG.LargeExtraspecial.S63 CFSG.RankThree.OrthogonalInvolutions
open CFSG.Sporadic.SmallF2.Native

theorem d4SqueezeCheckZ_eq_true : d4SqueezeCheckZ = true := Certificates.certificate21230

theorem d4SqueezeCheckT_eq_true : d4SqueezeCheckT = true := Certificates.certificate21231

theorem d4GenG_mul_self_of_gensOK (h : gensOK d4Gens = true) {k : ℕ} (hk : k < 8) :
    d4GenG k * d4GenG k = 1 :=
  (mul_self_of_gensOK (gs := d4Gens) (fun _ hk => repE_d4Gens hk) h k hk).2

theorem d4Word_append (l₁ l₂ : List ℕ) : d4Word (l₁ ++ l₂) = d4Word l₁ * d4Word l₂ := by
  simp only [d4Word, List.map_append, List.prod_append]

theorem d4Word_reverse (hinv : ∀ k < 8, d4GenG k * d4GenG k = 1) {l : List ℕ}
    (hl : ∀ k ∈ l, k < 8) : d4Word l.reverse = (d4Word l)⁻¹ := by
  induction l with
  | nil => simp [d4Word]
  | cons k l ih =>
    have hk : d4GenG k = (d4GenG k)⁻¹ :=
      eq_inv_of_mul_eq_one_left (hinv k (hl k List.mem_cons_self))
    rw [List.reverse_cons, d4Word_append, ih fun k' hk' => hl k' (List.mem_cons_of_mem k hk')]
    simp only [d4Word, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      mul_inv_rev]
    rw [← hk]

theorem d4Word_conjProdWord (hinv : ∀ k < 8, d4GenG k * d4GenG k = 1) (base : List ℕ)
    {cs : List (List ℕ)} (hcs : ∀ c ∈ cs, ∀ k ∈ c, k < 8) :
    d4Word (conjProdWord base cs) =
      (cs.map fun c => d4Word c * d4Word base * (d4Word c)⁻¹).prod := by
  induction cs with
  | nil => simp [conjProdWord, d4Word]
  | cons c cs ih =>
    have e : conjProdWord base (c :: cs) = c ++ base ++ c.reverse ++ conjProdWord base cs := by
      simp [conjProdWord]
    rw [e, d4Word_append, d4Word_append, d4Word_append,
      d4Word_reverse hinv (hcs c List.mem_cons_self),
      ih fun c' hc' => hcs c' (List.mem_cons_of_mem c hc'), List.map_cons, List.prod_cons]

theorem d4Word_pow_thirteen {w : List ℕ} (hw : ∀ k ∈ w, k < 8)
    (h : order13R (wordR d4Gens w) = true) : d4Word w ^ 13 = 1 ∧ d4Word w ≠ 1 := by
  rw [order13R, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', beq_eq_false_iff_ne] at h
  have hrep := repE_d4Word hw
  refine ⟨eq_of_repE d4E_injective (h.1 ▸ repE_powRows hrep 13) repE_one, fun h1 => h.2 ?_⟩
  exact (eq_iff_of_repE (validR_d4Word hw) validR_oneR hrep repE_one).2 h1

theorem exists_conj_prod_of_check {base : List ℕ} {cs : List (List ℕ)}
    (hcs : ∀ c ∈ cs, ∀ k ∈ c, k < 8) (hw : ∀ k ∈ conjProdWord base cs, k < 8)
    (h : (gensOK d4Gens && order13R (wordR d4Gens (conjProdWord base cs))) = true) :
    ∃ l : List trialityGroup8, l.length = cs.length ∧
      (l.map fun c => c * d4Word base * c⁻¹).prod ^ 13 = 1 ∧
      (l.map fun c => c * d4Word base * c⁻¹).prod ≠ 1 := by
  rw [Bool.and_eq_true] at h
  have hinv : ∀ k < 8, d4GenG k * d4GenG k = 1 := fun k hk => d4GenG_mul_self_of_gensOK h.1 hk
  refine ⟨cs.map d4Word, List.length_map _, ?_⟩
  rw [List.map_map]
  have e := d4Word_conjProdWord hinv base hcs
  simp only [Function.comp_def] at e ⊢
  rw [← e]
  exact d4Word_pow_thirteen hw h.2

section Squeeze

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem twelve_le_length_mul_finrank_commSpace {G : Type*} [Group G]
    (ρ : G →* (V ≃ₗ[ZMod 2] V)) (hρ : Function.Injective ρ) (x : G) (l : List G)
    (h13 : (l.map fun c => c * x * c⁻¹).prod ^ 13 = 1)
    (h1 : (l.map fun c => c * x * c⁻¹).prod ≠ 1) :
    12 ≤ l.length * finrank (ZMod 2) (commSpace (ρ x)) := by
  classical
  by_contra hlt
  set d : G → G := fun c => c * x * c⁻¹
  set S : Finset G := (l.map d).toFinset
  have hmem : (l.map d).prod ∈ Subgroup.closure (S : Set G) :=
    list_prod_mem fun y hy => Subgroup.subset_closure (by simpa [S] using hy)
  have hconj : ∀ y ∈ S, finrank (ZMod 2) (commSpace (ρ y)) =
      finrank (ZMod 2) (commSpace (ρ x)) := by
    intro y hy
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hy)
    rw [map_mul, map_mul, map_inv, finrank_commSpace_conj]
  have hsum : ∑ y ∈ S, finrank (ZMod 2) (commSpace (ρ y)) ≤
      l.length * finrank (ZMod 2) (commSpace (ρ x)) := by
    rw [Finset.sum_congr rfl hconj, Finset.sum_const, smul_eq_mul]
    exact Nat.mul_le_mul_right _ (by simpa using List.toFinset_card_le (l.map d))
  have h13' : ∀ j, 1 ≤ j → j ≤ 11 → ¬ 13 ∣ 2 ^ j - 1 := by
    intro j hj1 hj
    interval_cases j <;> norm_num
  have hρg := squeeze ρ S hmem (by norm_num) (by norm_num) h13
    fun j hj1 hj => h13' j hj1 (by omega)
  exact h1 (hρ (hρg.trans (map_one ρ).symm))

theorem exists_conj_prod_d4z : ∃ l : List trialityGroup8, l.length = 4 ∧
    (l.map fun c => c * d4z * c⁻¹).prod ^ 13 = 1 ∧ (l.map fun c => c * d4z * c⁻¹).prod ≠ 1 :=
  exists_conj_prod_of_check (base := wordZ) (cs := d4zConjs) (by decide) (by decide)
    d4SqueezeCheckZ_eq_true

theorem exists_conj_prod_d4t : ∃ l : List trialityGroup8, l.length = 2 ∧
    (l.map fun c => c * d4t * c⁻¹).prod ^ 13 = 1 ∧ (l.map fun c => c * d4t * c⁻¹).prod ≠ 1 :=
  exists_conj_prod_of_check (base := wordT) (cs := d4tConjs) (by decide) (by decide)
    d4SqueezeCheckT_eq_true

theorem three_le_finrank_commSpace_d4z (ρ : trialityGroup8 →* (V ≃ₗ[ZMod 2] V))
    (hρ : Function.Injective ρ) : 3 ≤ finrank (ZMod 2) (commSpace (ρ d4z)) := by
  obtain ⟨l, hl, h13, h1⟩ := exists_conj_prod_d4z
  have h := twelve_le_length_mul_finrank_commSpace ρ hρ d4z l h13 h1
  rw [hl] at h
  omega

theorem six_le_finrank_commSpace_d4t (ρ : trialityGroup8 →* (V ≃ₗ[ZMod 2] V))
    (hρ : Function.Injective ρ) : 6 ≤ finrank (ZMod 2) (commSpace (ρ d4t)) := by
  obtain ⟨l, hl, h13, h1⟩ := exists_conj_prod_d4t
  have h := twelve_le_length_mul_finrank_commSpace ρ hρ d4t l h13 h1
  rw [hl] at h
  omega

theorem three_le_finrank_commSpace_of_orderOf_eq_two (ρ : trialityGroup8 →* (V ≃ₗ[ZMod 2] V))
    (hρ : Function.Injective ρ) {s : trialityGroup8} (hs : orderOf s = 2) :
    3 ≤ finrank (ZMod 2) (commSpace (ρ s)) := by
  obtain ⟨c, hc | hc⟩ := exists_conj_of_orderOf_eq_two hs
  · rw [hc, map_mul, map_mul, map_inv, finrank_commSpace_conj]
    exact three_le_finrank_commSpace_d4z ρ hρ
  · rw [hc, map_mul, map_mul, map_inv, finrank_commSpace_conj]
    exact (six_le_finrank_commSpace_d4t ρ hρ).trans' (by norm_num)

end Squeeze

end CFSG.LargeExtraspecial.A2Mod
