module

public import CFSG.HardMathSupport.Foote.E27.UniFusion

public section

namespace CFSG.HardMathSupport.Foote.E27.Uni

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher Subgroup

theorem card_centralizer_le_mul {G : Type*} [Group G] [Finite G] (A : Subgroup G) [A.Normal]
    {k : ℕ} (hk : Nat.card G ≤ k * Nat.card A) (x : G) :
    Nat.card ↥(centralizer ({x} : Set G)) ≤ k * Nat.card ↥(A ⊓ centralizer ({x} : Set G)) := by
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  let ψ : ↥C →* G ⧸ A := (QuotientGroup.mk' A).comp C.subtype
  have h := Subgroup.card_ker_mul_card_range ψ
  have hq : Nat.card (G ⧸ A) ≤ k := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup A
    have hApos : 0 < Nat.card A := Nat.card_pos
    rw [h1] at hk
    exact Nat.le_of_mul_le_mul_right (by simpa [mul_comm] using hk) hApos
  have hr : Nat.card ψ.range ≤ k := (Subgroup.card_le_card_group ψ.range).trans hq
  have hker : Nat.card ψ.ker ≤ Nat.card ↥(A ⊓ C) := by
    refine Nat.card_le_card_of_injective
      (fun y => (⟨(y.1 : G), ?_, y.1.2⟩ : ↥(A ⊓ C))) ?_
    · have := y.2
      rw [MonoidHom.mem_ker] at this
      exact (QuotientGroup.eq_one_iff _).mp this
    · intro y y' hyy
      have h' : ((y : ↥C) : G) = ((y' : ↥C) : G) := by simpa using congrArg Subtype.val hyy
      exact Subtype.ext (Subtype.ext h')
  rw [← h, mul_comm k]
  exact Nat.mul_le_mul hker hr

theorem card_inf_centralizer_le_mul {J : Type*} [Group J] [Finite J] (S A : Subgroup J)
    (hAS : A ≤ S) (hnorm : ∀ s ∈ S, ∀ a ∈ A, s * a * s⁻¹ ∈ A) {k : ℕ}
    (hk : Nat.card ↥S ≤ k * Nat.card ↥A) (x : J) (hx : x ∈ S) :
    Nat.card ↥(S ⊓ centralizer ({x} : Set J)) ≤ k * Nat.card ↥(A ⊓ centralizer ({x} : Set J)) := by
  let AS : Subgroup ↥S := A.subgroupOf S
  have hN : AS.Normal := ⟨fun n hn g => by
    have h1 : (g : J) * (n : J) * (g : J)⁻¹ ∈ A := hnorm g g.2 n hn
    exact h1⟩
  have hAScard : Nat.card ↥AS = Nat.card ↥A := by
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAS).toEquiv
  have h := card_centralizer_le_mul AS (k := k) (by rw [hAScard]; exact hk) ⟨x, hx⟩
  have e1 : Nat.card ↥(centralizer ({(⟨x, hx⟩ : ↥S)} : Set ↥S)) =
      Nat.card ↥(S ⊓ centralizer ({x} : Set J)) := by
    rw [inf_comm, ← centralizer_map_val_eq S x hx,
      Subgroup.card_map_of_injective S.subtype_injective]
  have e2 : Nat.card ↥(AS ⊓ centralizer ({(⟨x, hx⟩ : ↥S)} : Set ↥S)) =
      Nat.card ↥(A ⊓ centralizer ({x} : Set J)) := by
    rw [← Subgroup.card_map_of_injective S.subtype_injective, Subgroup.map_inf_eq _ _ S.subtype
      S.subtype_injective, centralizer_map_val_eq S x hx]
    have hm : AS.map S.subtype ⊓ (centralizer ({x} : Set J) ⊓ S) = A ⊓ centralizer ({x} : Set J) := by
      ext y
      simp only [Subgroup.mem_inf, Subgroup.mem_map, AS, Subgroup.mem_subgroupOf]
      constructor
      · rintro ⟨⟨z, hz, rfl⟩, hc, -⟩
        exact ⟨hz, hc⟩
      · rintro ⟨hy, hc⟩
        exact ⟨⟨⟨y, hAS hy⟩, hy, rfl⟩, hc, hAS hy⟩
    rw [hm]
  rw [e1, e2] at h
  exact h

theorem orbit4 : ∀ σ : Equiv.Perm (Fin 4), σ ^ 3 = 1 → σ ≠ 1 →
    ∃ a b : Fin 4, Function.Bijective ![a, σ a, σ (σ a), b] ∧ σ b = b := by
  decide +kernel

variable {E : Type} [Field E]

theorem eq_of_invariant (hU : UnitaryFieldData 2 1 E) (σ : Equiv.Perm (Fin 4)) (a b : Fin 4)
    (hb : Function.Bijective ![a, σ a, σ (σ a), b]) (e e' : Fin 4 → Eˣ)
    (he : ∀ i, e (σ.symm i) = e i) (he' : ∀ i, e' (σ.symm i) = e' i)
    (hp : ∏ i, e i = 1) (hp' : ∏ i, e' i = 1) (hae : e a = e' a) : e = e' := by
  have key : ∀ f : Fin 4 → Eˣ, (∀ i, f (σ.symm i) = f i) → ∏ i, f i = 1 →
      f (σ a) = f a ∧ f (σ (σ a)) = f a ∧ f b = 1 := by
    intro f hf hpf
    have h1 : f (σ a) = f a := (by simpa using hf (σ a) : f a = f (σ a)).symm
    have h2 : f (σ (σ a)) = f a := by
      have := hf (σ (σ a))
      simp only [Equiv.symm_apply_apply] at this
      rw [← this, h1]
    refine ⟨h1, h2, ?_⟩
    have hprod : ∏ i, f i = ∏ k, f (![a, σ a, σ (σ a), b] k) :=
      (Equiv.prod_comp (Equiv.ofBijective _ hb) f).symm
    simp only [Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Fin.isValue] at hprod
    rw [Fin.prod_univ_four] at hpf
    have h3 := unit_cube hU (f a)
    have : f a * f (σ a) * f (σ (σ a)) * f b = 1 := hprod.symm.trans hpf
    rw [h1, h2, ← pow_three'] at this
    rw [h3, one_mul] at this
    exact this
  obtain ⟨e1, e2, e3⟩ := key e he hp
  obtain ⟨e1', e2', e3'⟩ := key e' he' hp'
  funext i
  obtain ⟨k, rfl⟩ := hb.2 i
  fin_cases k
  · simpa using hae
  · simp only [Fin.isValue, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [e1, e1', hae]
  · simp only [Fin.reduceFinMk, Matrix.cons_val]
    rw [e2, e2', hae]
  · simp only [Fin.reduceFinMk, Matrix.cons_val]
    rw [e3, e3']

variable (hU : UnitaryFieldData 2 1 E)

theorem piU_injective_four : Function.Injective (piU hU 4) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  change (QuotientGroup.mk' (Zsc hU 4)).ker = ⊥
  rw [QuotientGroup.ker_mk']
  exact Zsc_eq_bot_of_coprime hU (by norm_num)

theorem mem_Amono_iff {n : ℕ} (y : primeFormP hU (1 : Matrix (Fin n) (Fin n) E)) :
    y ∈ Amono hU n ↔ ∃ e : ↥(prodKer n E), piU hU n (dgG hU n e) = y := by
  constructor
  · rintro ⟨_, ⟨e, rfl⟩, rfl⟩
    exact ⟨e, rfl⟩
  · rintro ⟨e, rfl⟩
    exact ⟨_, ⟨e, rfl⟩, rfl⟩

theorem invariant_of_comm {n : ℕ} (hinj : Function.Injective (piU hU n)) (e c : ↥(prodKer n E))
    (σ : Equiv.Perm (Fin n))
    (hcomm : piU hU n (dgG hU n c * pmG hU n σ) * piU hU n (dgG hU n e) =
      piU hU n (dgG hU n e) * piU hU n (dgG hU n c * pmG hU n σ)) :
    ∀ i, e.1 (σ.symm i) = e.1 i := by
  rw [← map_mul, ← map_mul] at hcomm
  have h1 := congrArg (fun g : ↥(gramSU hU (1 : Matrix (Fin n) (Fin n) E)) => (g : GL (Fin n) E))
    (hinj hcomm)
  simp only [Subgroup.coe_mul, dgG_val, pmG_val] at h1
  have h3 : (dgHom n E c.1 * pmHom n E σ) * dgHom n E e.1 =
      dgHom n E (c.1 * (e.1 ∘ σ.symm)) * pmHom n E σ := by
    rw [mul_assoc, pm_conj_dg' (E := E) σ e.1, ← mul_assoc, ← map_mul]
  have h4 : dgHom n E e.1 * (dgHom n E c.1 * pmHom n E σ) =
      dgHom n E (e.1 * c.1) * pmHom n E σ := by
    rw [← mul_assoc, ← map_mul]
  rw [h3, h4] at h1
  have h5 := dgHom_injective (mul_right_cancel h1)
  intro i
  have := congrFun h5 i
  simp only [Pi.mul_apply, Function.comp_apply] at this
  have h6 : c.1 i * e.1 (σ.symm i) = c.1 i * e.1 i := by rw [this, mul_comm]
  exact mul_left_cancel h6

theorem card_A_inf_C_le_three (c : ↥(prodKer 4 E)) (σ : Equiv.Perm (Fin 4)) (hσ3 : σ ^ 3 = 1)
    (hσ : σ ≠ 1) :
    Nat.card ↥(Amono hU 4 ⊓ centralizer ({piU hU 4 (dgG hU 4 c * pmG hU 4 σ)} :
      Set (primeFormP hU (1 : Matrix (Fin 4) (Fin 4) E)))) ≤ 3 := by
  have hEfin := hU.finite
  obtain ⟨a, b, hb, -⟩ := orbit4 σ hσ3 hσ
  have hinj := piU_injective_four hU
  have hex : ∀ y : ↥(Amono hU 4 ⊓ centralizer ({piU hU 4 (dgG hU 4 c * pmG hU 4 σ)} :
      Set (primeFormP hU (1 : Matrix (Fin 4) (Fin 4) E)))),
      ∃ e : ↥(prodKer 4 E), piU hU 4 (dgG hU 4 e) = (y : primeFormP hU (1 : Matrix (Fin 4) (Fin 4) E)) :=
    fun y => (mem_Amono_iff hU _).mp y.2.1
  choose eOf heOf using hex
  have hinv : ∀ y, ∀ i, (eOf y).1 (σ.symm i) = (eOf y).1 i := by
    intro y
    refine invariant_of_comm hU hinj (eOf y) c σ ?_
    rw [heOf y]
    have hy2 : (y : primeFormP hU (1 : Matrix (Fin 4) (Fin 4) E)) ∈
        centralizer ({piU hU 4 (dgG hU 4 c * pmG hU 4 σ)} :
          Set (primeFormP hU (1 : Matrix (Fin 4) (Fin 4) E))) := y.2.2
    exact (Subgroup.mem_centralizer_singleton_iff.mp hy2).symm
  rw [← card_units_three hU]
  refine Nat.card_le_card_of_injective (fun y => (eOf y).1 a) ?_
  intro y y' hyy
  have h1 : (eOf y).1 = (eOf y').1 :=
    eq_of_invariant hU σ a b hb _ _ (hinv y) (hinv y') (prod_eq_one_of_mem (eOf y).2)
      (prod_eq_one_of_mem (eOf y').2) hyy
  apply Subtype.ext
  rw [← heOf y, ← heOf y', Subtype.ext h1]

open scoped Pointwise in
theorem exists_mono_of_mem_Smono {n : ℕ} (P : Subgroup (Equiv.Perm (Fin n)))
    {x : primeFormP hU (1 : Matrix (Fin n) (Fin n) E)} (hx : x ∈ Smono hU n P) :
    ∃ (c : ↥(prodKer n E)) (σ : Equiv.Perm (Fin n)), σ ∈ P ∧
      x = piU hU n (dgG hU n c * pmG hU n σ) := by
  have hs' : x ∈ (MS hU n P).map (piU hU n) := hx
  obtain ⟨m, hm, rfl⟩ := hs'
  have hm' : m ∈ (SetLike.coe (AtS hU n)) * (SetLike.coe (PtS hU n P)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ (PtS_le_normalizer hU n P)]
    exact hm
  obtain ⟨a, ha, p, hp, rfl⟩ := hm'
  obtain ⟨c, rfl⟩ := ha
  obtain ⟨σ, hσP, rfl⟩ := hp
  exact ⟨c, σ, hσP, rfl⟩

theorem le_Amono_four (P : Subgroup (Equiv.Perm (Fin 4))) (hP : IsPGroup 3 P)
    (hPc : Nat.card P = 3)
    (hS81 : Nat.card (Smono hU 4 P) = 81) (hA27 : Nat.card (Amono hU 4) = 27)
    (R' : Subgroup (primeFormP hU (1 : Matrix (Fin 4) (Fin 4) E))) (hR : R' ≤ Smono hU 4 P)
    (hcomm : ∀ x ∈ R', ∀ y ∈ R', x * y = y * x) (hcard : Nat.card R' = 27) :
    R' ≤ Amono hU 4 := by
  have hEfin := hU.finite
  have hZ : Nat.card (Zsc hU 4) ≤ 1 := by
    rw [Zsc_eq_bot_of_coprime hU (by norm_num), Subgroup.card_bot]
  obtain ⟨-, -, hAS, hnorm, -, -, -⟩ := monomial_data_of_pgroup hU (by norm_num) P hP 1 hZ
  by_contra hnot
  obtain ⟨x, hxR, hxA⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
  obtain ⟨c, σ, hσP, rfl⟩ := exists_mono_of_mem_Smono hU P (hR hxR)
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    apply hxA
    rw [map_one, mul_one]
    exact ⟨_, ⟨c, rfl⟩, rfl⟩
  have hσ3 : σ ^ 3 = 1 := by
    have := pow_card_eq_one' (G := ↥P) (x := ⟨σ, hσP⟩)
    rw [hPc] at this
    exact congrArg Subtype.val this
  have h3 := card_A_inf_C_le_three hU c σ hσ3 hσ1
  have hle := card_inf_centralizer_le_mul (Smono hU 4 P) (Amono hU 4) hAS hnorm
    (k := 3) (by rw [hS81, hA27]) _ (hR hxR)
  have hR' : R' ≤ Smono hU 4 P ⊓ centralizer ({piU hU 4 (dgG hU 4 c * pmG hU 4 σ)} :
      Set (primeFormP hU (1 : Matrix (Fin 4) (Fin 4) E))) := by
    intro y hy
    refine ⟨hR hy, ?_⟩
    show y ∈ centralizer ({piU hU 4 (dgG hU 4 c * pmG hU 4 σ)} :
      Set (primeFormP hU (1 : Matrix (Fin 4) (Fin 4) E)))
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hcomm _ hxR y hy).symm
  have := Subgroup.card_le_of_le hR'
  omega

def ej (g : Eˣ) (j : Fin 4) : Fin 4 → Eˣ := fun i => if i = j then 1 else g

theorem ej_mem (g : Eˣ) (hg : g ^ 3 = 1) (j : Fin 4) : ej g j ∈ prodKer 4 E := by
  change ∏ i, ej g j i = 1
  fin_cases j <;> simp [ej, Fin.prod_univ_four, ← pow_three', hg]

theorem pm_commute_dg_of_fixed {n : ℕ} (σ : Equiv.Perm (Fin n)) (e : Fin n → Eˣ)
    (h : ∀ i, e (σ.symm i) = e i) : pmHom n E σ * dgHom n E e = dgHom n E e * pmHom n E σ := by
  rw [pm_conj_dg']
  have : e ∘ σ.symm = e := funext h
  rw [this]

noncomputable def rj (g : Eˣ) (hg : g ^ 3 = 1) (j : Fin 4) :
    primeFormP hU (1 : Matrix (Fin 4) (Fin 4) E) :=
  piU hU 4 (dgG hU 4 ⟨ej g j, ej_mem g hg j⟩)

theorem rj_mem_Amono (g : Eˣ) (hg : g ^ 3 = 1) (j : Fin 4) : rj hU g hg j ∈ Amono hU 4 :=
  ⟨_, ⟨⟨ej g j, ej_mem g hg j⟩, rfl⟩, rfl⟩

theorem Smono_le_centralizer_rj (P : Subgroup (Equiv.Perm (Fin 4))) (g : Eˣ) (hg : g ^ 3 = 1)
    (j0 : Fin 4) (hfix : ∀ σ ∈ P, σ j0 = j0) :
    Smono hU 4 P ≤ centralizer ({rj hU g hg j0} : Set (primeFormP hU (1 : Matrix (Fin 4) (Fin 4) E))) := by
  intro x hx
  obtain ⟨c, σ, hσP, rfl⟩ := exists_mono_of_mem_Smono hU P hx
  show _ ∈ centralizer _
  rw [Subgroup.mem_centralizer_singleton_iff]
  rw [rj, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  simp only [Subgroup.coe_mul, dgG_val, pmG_val]
  have hinv : ∀ i, ej g j0 (σ.symm i) = ej g j0 i := by
    intro i
    have hs : σ.symm j0 = j0 := by rw [Equiv.symm_apply_eq]; exact (hfix σ hσP).symm
    by_cases hi : i = j0
    · subst hi; rw [hs]
    · have : σ.symm i ≠ j0 := by
        intro h
        apply hi
        rw [Equiv.symm_apply_eq] at h
        rw [h, hfix σ hσP]
      simp [ej, hi, this]
  have hc := pm_commute_dg_of_fixed σ (ej g j0) hinv
  calc dgHom 4 E c.1 * pmHom 4 E σ * dgHom 4 E (ej g j0) = dgHom 4 E c.1 * (pmHom 4 E σ * dgHom 4 E (ej g j0)) := by rw [mul_assoc]
    _ = dgHom 4 E c.1 * (dgHom 4 E (ej g j0) * pmHom 4 E σ) := by rw [hc]
    _ = dgHom 4 E (c.1 * ej g j0) * pmHom 4 E σ := by rw [← mul_assoc, ← map_mul]
    _ = dgHom 4 E (ej g j0 * c.1) * pmHom 4 E σ := by rw [mul_comm c.1]
    _ = _ := by rw [map_mul, mul_assoc]

theorem good_rj (P : Subgroup (Equiv.Perm (Fin 4))) (hS81 : Nat.card (Smono hU 4 P) = 81)
    (g : Eˣ) (hg : g ^ 3 = 1) (j0 : Fin 4) (hfix : ∀ σ ∈ P, σ j0 = j0) (j : Fin 4) :
    81 ∣ Nat.card ↥(centralizer ({rj hU g hg j} : Set (primeFormP hU (1 : Matrix (Fin 4) (Fin 4) E)))) := by
  have h0 : 81 ∣ Nat.card ↥(centralizer ({rj hU g hg j0} :
      Set (primeFormP hU (1 : Matrix (Fin 4) (Fin 4) E)))) := by
    rw [← hS81]
    exact Subgroup.card_dvd_of_le (Smono_le_centralizer_rj hU P g hg j0 hfix)
  set τ : Equiv.Perm (Fin 4) := Equiv.swap j j0 with hτ
  have hconj : rj hU g hg j = piU hU 4 (pmG hU 4 τ) * rj hU g hg j0 * (piU hU 4 (pmG hU 4 τ))⁻¹ := by
    rw [rj, rj, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, dgG_val, pmG_val]
    rw [pm_conj_dg]
    congr 1
    funext i
    simp only [Function.comp_apply, ej]
    have hsymm : τ.symm = τ := Equiv.symm_swap j j0
    rw [hsymm]
    by_cases hi : i = j
    · subst hi
      simp [hτ]
    · have : τ i ≠ j0 := by
        intro h
        apply hi
        have : τ i = τ j := by rw [h, hτ, Equiv.swap_apply_left]
        exact τ.injective this
      simp [hi, this]
  rw [hconj, card_centralizer_conj']
  exact h0

theorem no_plane (g : Eˣ) (hg : g ^ 3 = 1) (hgo : orderOf g = 3)
    (T' : Subgroup (primeFormP hU (1 : Matrix (Fin 4) (Fin 4) E))) (hT' : Nat.card T' = 9)
    (h0 : rj hU g hg 0 ∈ T') (h1 : rj hU g hg 1 ∈ T') (h2 : rj hU g hg 2 ∈ T') : False := by
  classical
  have hEfin := hU.finite
  have hinj : Function.Injective (fun e : ↥(prodKer 4 E) => piU hU 4 (dgG hU 4 e)) :=
    (piU_injective_four hU).comp (dgG_injective hU)
  let eJ : Fin 4 → ↥(prodKer 4 E) := fun j => ⟨ej g j, ej_mem g hg j⟩
  have hr : ∀ j, rj hU g hg j = piU hU 4 (dgG hU 4 (eJ j)) := fun j => rfl
  let f : Fin 3 × Fin 3 × Fin 3 → ↥T' := fun x =>
    ⟨rj hU g hg 0 ^ x.1.val * rj hU g hg 1 ^ x.2.1.val * rj hU g hg 2 ^ x.2.2.val,
      mul_mem (mul_mem (pow_mem h0 _) (pow_mem h1 _)) (pow_mem h2 _)⟩
  have : Fintype ↥T' := Fintype.ofFinite _
  have hcard : Fintype.card ↥T' < Fintype.card (Fin 3 × Fin 3 × Fin 3) := by
    rw [← Nat.card_eq_fintype_card, hT']
    simp
  obtain ⟨x, y, hxy, hfxy⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  have hJ : rj hU g hg 0 ^ x.1.val * rj hU g hg 1 ^ x.2.1.val * rj hU g hg 2 ^ x.2.2.val =
      rj hU g hg 0 ^ y.1.val * rj hU g hg 1 ^ y.2.1.val * rj hU g hg 2 ^ y.2.2.val :=
    congrArg Subtype.val hfxy
  simp only [hr, ← map_pow, ← map_mul] at hJ
  have hE := hinj hJ
  have hc0 := congrFun (congrArg Subtype.val hE) 0
  have hc1 := congrFun (congrArg Subtype.val hE) 1
  have hc2 := congrFun (congrArg Subtype.val hE) 2
  simp only [eJ, Subgroup.coe_mul, Subgroup.coe_pow, Pi.mul_apply, Pi.pow_apply, ej] at hc0 hc1 hc2
  simp at hc0 hc1 hc2
  rw [← pow_add, ← pow_add, pow_eq_pow_iff_modEq, hgo] at hc0 hc1 hc2
  unfold Nat.ModEq at hc0 hc1 hc2
  have a1 := x.1.isLt
  have a2 := x.2.1.isLt
  have a3 := x.2.2.isLt
  have b1 := y.1.isLt
  have b2 := y.2.1.isLt
  have b3 := y.2.2.isLt
  apply hxy
  have e1 : x.1 = y.1 := Fin.ext (by omega)
  have e2 : x.2.1 = y.2.1 := Fin.ext (by omega)
  have e3 : x.2.2 = y.2.2 := Fin.ext (by omega)
  exact Prod.ext e1 (Prod.ext e2 e3)

theorem card_Amono_four : Nat.card (Amono hU 4) = 27 := by
  have hEfin := hU.finite
  have h1 : Nat.card (AtS hU 4) = 27 := by
    have := Nat.card_range_of_injective (dgG_injective (n := 4) hU)
    exact this.trans (by rw [card_prodKer hU (by norm_num)]; norm_num)
  rw [Amono, Subgroup.card_map_of_injective (piU_injective_four hU)]
  exact h1

theorem hgen_four (P : Subgroup (Equiv.Perm (Fin 4))) (hP : IsPGroup 3 P) (hPc : Nat.card P = 3)
    (hS81 : Nat.card (Smono hU 4 P) = 81) :
    ∀ R' T' : Subgroup (primeFormP hU (1 : Matrix (Fin 4) (Fin 4) E)), R' ≤ Smono hU 4 P →
      (∀ x ∈ R', x ^ 3 = 1) → (∀ x ∈ R', ∀ y ∈ R', x * y = y * x) → Nat.card R' = 27 →
      T' ≤ R' → Nat.card T' = 9 →
      ∃ r ∈ R', r ∉ T' ∧ 81 ∣ Nat.card ↥(centralizer ({r} : Set _)) := by
  intro R' T' hR hexp hcomm hcard hTR hT
  have hEfin := hU.finite
  have hA27 := card_Amono_four hU
  have hRA : R' ≤ Amono hU 4 := le_Amono_four hU P hP hPc hS81 hA27 R' hR hcomm hcard
  have hRA' : R' = Amono hU 4 := Subgroup.eq_of_le_of_card_ge hRA (by rw [hA27, hcard])
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcyc : IsCyclic ↥P := isCyclic_of_prime_card hPc
  obtain ⟨γ, hγ⟩ := hcyc.exists_generator
  have hγ1 : (γ : Equiv.Perm (Fin 4)) ≠ 1 := by
    intro h
    have hγ' : γ = 1 := Subtype.ext h
    have h1 : ∀ x : ↥P, x = 1 := by
      intro x
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hγ x)
      rw [hγ', _root_.one_zpow]
    have : Subsingleton ↥P := ⟨fun a b => (h1 a).trans (h1 b).symm⟩
    have := Nat.card_of_subsingleton (1 : ↥P)
    omega
  have hγ3 : (γ : Equiv.Perm (Fin 4)) ^ 3 = 1 := by
    have := pow_card_eq_one' (G := ↥P) (x := γ)
    rw [hPc] at this
    exact congrArg Subtype.val this
  obtain ⟨a, b, hb, hbfix⟩ := orbit4 (γ : Equiv.Perm (Fin 4)) hγ3 hγ1
  have hfix : ∀ σ ∈ P, σ b = b := by
    intro σ hσ
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hγ ⟨σ, hσ⟩)
    have : σ = (γ : Equiv.Perm (Fin 4)) ^ k := by
      rw [← Subgroup.coe_zpow, hk]
    rw [this]
    exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hbfix k
  obtain ⟨g, hgo'⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Eˣ)
  have hgo : orderOf g = 3 := by rw [hgo', card_units_three hU]
  have hg : g ^ 3 = 1 := unit_cube hU g
  have hgood := good_rj hU P hS81 g hg b hfix
  by_contra hno
  push Not at hno
  have hjT : ∀ j, rj hU g hg j ∈ T' := by
    intro j
    by_contra hj
    exact hno _ (hRA' ▸ rj_mem_Amono hU g hg j) hj (hgood j)
  exact no_plane hU g hg hgo T' hT (hjT 0) (hjT 1) (hjT 2)

end CFSG.HardMathSupport.Foote.E27.Uni

end
