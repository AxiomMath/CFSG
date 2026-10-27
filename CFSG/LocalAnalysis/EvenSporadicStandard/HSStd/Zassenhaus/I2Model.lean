module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.I2Module
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.SpecialSpec
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.SylowTransfer
public import Certificates.Certificate117021

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.I2

open Subgroup CFSG.Open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
  CFSG.Certificates.Native CFSG.RankThree.Native CFSG.Blueprint CFSG.Blueprint.NativeSporadic

@[expose] def HasModel {M : Type*} [Group M] (z : M) (E : Subgroup M) : Prop :=
  ∃ (e : Fin 4 → M) (h r : Fin 2 → M),
    E = Subgroup.closure (Set.range e) ∧ IsElemAbelian 2 E ∧ Nat.card E = 16 ∧ z ∈ E ∧
    (∀ x ∈ E, x ≠ 1 → ∃ a ∈ normalizer (E : Set M), a * z * a⁻¹ = x) ∧
    Subgroup.closure (Set.range h) = normalizer (E : Set M) ∧
    Nat.card (normalizer (E : Set M)) = 11520 ∧ centralizer (E : Set M) = E ∧
    (∀ j i, h j * e i * (h j)⁻¹ = vecE e (rho j i)) ∧
    (∀ i, r 0 * e i * (r 0)⁻¹ = vecE e (kx i)) ∧ (∀ i, r 1 * e i * (r 1)⁻¹ = vecE e (ky i)) ∧
    (∀ j, r j ∈ Subgroup.closure (Set.range h)) ∧ (∀ j, r j * r j ∈ E) ∧
    r 0 * r 1 * (r 0 * r 1) ∈ E

theorem zasE0Gens_size : zasE0Gens.size = 4 := by simp [zasE0Gens, zasEGens]
theorem zasNGens_size : zasNGens.size = 2 := by simp [zasNGens, zasGens]

theorem rep_selA {a : Array ℕ} (ha : validA 100 a = true) (b : ZMod 2) :
    Rep 100 (selA a b) (permOfArr 100 a ^ b.val) := by
  have hb : b = 0 ∨ b = 1 := by revert b; decide
  rcases hb with rfl | rfl
  · simpa [selA] using rep_idA
  · have h1 : (1 : ZMod 2).val = 1 := rfl
    simpa [selA, h1] using rep_of_validA ha

theorem rep_vecEA (hv : ∀ i : Fin 4, validA 100 zasE0Gens[i.1]! = true) (v : Vec) :
    Rep 100 (vecEA v) (vecE (fun i : Fin 4 => permOfArr 100 zasE0Gens[i.1]!) v) := by
  unfold vecEA vecE
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil]
  have h0 : validA 100 zasE0Gens[0]! = true := hv 0
  have h1 : validA 100 zasE0Gens[1]! = true := hv 1
  have h2 : validA 100 zasE0Gens[2]! = true := hv 2
  have h3 : validA 100 zasE0Gens[3]! = true := hv 3
  exact rep_compA (rep_selA h0 _) (rep_compA (rep_selA h1 _)
    (rep_compA (rep_selA h2 _) (rep_compA (rep_selA h3 _) rep_idA)))

theorem range_gens {gs : Array (Array ℕ)} {m : ℕ} (hs : gs.size = m) :
    Set.range (fun i : Fin m => permOfArr 100 gs[i.1]!) = permsA 100 gs := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i.1, by simp [hs], rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨k, by simpa [hs] using hk⟩, rfl⟩

theorem i2_perm_model :
    ∃ E : Subgroup (Equiv.Perm (Fin 100)),
      IsSpecialIn hs100P zasZ0 E ∧
      Subgroup.closure (permsA 100 zasNGens) = normalizer (E : Set (Equiv.Perm (Fin 100))) ⊓ hs100P ∧
      Nat.card (Subgroup.closure (permsA 100 zasNGens)) = 11520 ∧
      ∃ (e : Fin 4 → Equiv.Perm (Fin 100)) (h r : Fin 2 → Equiv.Perm (Fin 100)),
        E = Subgroup.closure (Set.range e) ∧
        Subgroup.closure (Set.range h) = Subgroup.closure (permsA 100 zasNGens) ∧
        (∀ x ∈ Subgroup.closure (permsA 100 zasNGens), (∀ i, x * e i = e i * x) → x ∈ E) ∧
        (∀ j i, h j * e i * (h j)⁻¹ = vecE e (rho j i)) ∧
        (∀ i, r 0 * e i * (r 0)⁻¹ = vecE e (kx i)) ∧ (∀ i, r 1 * e i * (r 1)⁻¹ = vecE e (ky i)) ∧
        (∀ j, r j ∈ Subgroup.closure (permsA 100 zasNGens)) ∧ (∀ j, r j * r j ∈ E) ∧
        r 0 * r 1 * (r 0 * r 1) ∈ E := by
  classical
  obtain ⟨E, hEdef, hNeq, hspec⟩ := zas_special_spec_ext
  have hS : zasSpecialOK = true := Certificates.certificate117002
  simp only [zasSpecialOK, Bool.and_eq_true, beq_iff_eq, and_assoc] at hS
  obtain ⟨-, h1, -, -, -, -, -, h7, h8, -⟩ := hS
  have hall : i2ModelOK = true := Certificates.certificate117021
  simp only [i2ModelOK, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hall
  obtain ⟨c1, c2, c3, v0, v1, m00, m11, m01, n0, n1, cent⟩ := hall
  have hpsE : ∀ p ∈ zasEKeys, p < 100 := fun p hp => List.mem_range.1 hp
  have hpsN : ∀ p ∈ zasNKeys, p < 100 := by
    intro p hp
    simp only [zasNKeys, List.mem_cons, List.not_mem_nil, or_false] at hp
    omega
  obtain ⟨hmemN, hcardN, hvalN⟩ := enumOK_spec hpsN h7
  have hvE : ∀ i : Fin 4, validA 100 zasE0Gens[i.1]! = true := fun i =>
    enumOK_gens_valid h1 (by rw [zasE0Gens_size]; exact i.2)
  have hvH : ∀ j : Fin 2, validA 100 zasNGens[j.1]! = true := fun j =>
    enumOK_gens_valid h7 (by rw [zasNGens_size]; exact j.2)
  have hvR : ∀ j : Fin 2, validA 100 i2R[j.1]! = true := fun j => by
    fin_cases j
    · exact v0
    · exact v1
  set e : Fin 4 → Equiv.Perm (Fin 100) := fun i => permOfArr 100 zasE0Gens[i.1]! with he
  set h : Fin 2 → Equiv.Perm (Fin 100) := fun j => permOfArr 100 zasNGens[j.1]! with hh
  set r : Fin 2 → Equiv.Perm (Fin 100) := fun j => permOfArr 100 i2R[j.1]! with hr
  have hEr : E = Subgroup.closure (Set.range e) := by
    rw [hEdef, he, range_gens zasE0Gens_size]
  have hHr : Subgroup.closure (Set.range h) = Subgroup.closure (permsA 100 zasNGens) := by
    rw [hh, range_gens zasNGens_size]
  have hrepE : ∀ i, Rep 100 zasE0Gens[i.1]! (e i) := fun i => rep_of_validA (hvE i)
  have hrepR : ∀ j, Rep 100 i2R[j.1]! (r j) := fun j => rep_of_validA (hvR j)
  have hmemE : ∀ {t : Array ℕ} {x : Equiv.Perm (Fin 100)}, Rep 100 t x → zasMem zasE0Cert t = true →
      x ∈ E := fun ht hm => by
    rw [hEdef]
    exact enumOK_mem_of_any hpsE h1 ht hm
  have hmemN : ∀ {t : Array ℕ} {x : Equiv.Perm (Fin 100)}, Rep 100 t x → zasMem zasNCert t = true →
      x ∈ Subgroup.closure (permsA 100 zasNGens) := fun ht hm =>
    enumOK_mem_of_any hpsN h7 ht hm
  refine ⟨E, hspec, hNeq, ?_, e, h, r, hEr, hHr, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcardN]; exact h8
  · intro x hx hcomm
    obtain ⟨i, hi, hrx⟩ := enumOK_exists_rep hpsN h7 hx
    have hk := List.all_eq_true.1 cent _ (zasPts_mem hi)
    have hvx : validA 100 zasNCert.pts[i]! = true := hvalN i hi
    have hall' : ∀ k : Fin 4, eqA 100 (compA 100 zasNCert.pts[i]! zasE0Gens[k.1]!)
        (compA 100 zasE0Gens[k.1]! zasNCert.pts[i]!) = true := fun k =>
      (eqA_iff (rep_compA hrx (hrepE k)) (rep_compA (hrepE k) hrx)).2 (hcomm k)
    simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hk
    rcases hk with hk | hk
    · exact absurd hall' hk
    · exact hmemE hrx hk
  · intro j i
    exact (eqA_iff (rep_zasConj (hvH j) (hrepE i)) (rep_vecEA hvE (rho j i))).1 (c1 j i)
  · intro i
    exact (eqA_iff (rep_zasConj (hvR 0) (hrepE i)) (rep_vecEA hvE (kx i))).1 (c2 i)
  · intro i
    exact (eqA_iff (rep_zasConj (hvR 1) (hrepE i)) (rep_vecEA hvE (ky i))).1 (c3 i)
  · intro j
    fin_cases j
    · exact hmemN (hrepR 0) n0
    · exact hmemN (hrepR 1) n1
  · intro j
    fin_cases j
    · exact hmemE (rep_compA (hrepR 0) (hrepR 0)) m00
    · exact hmemE (rep_compA (hrepR 1) (hrepR 1)) m11
  · exact hmemE (rep_compA (rep_compA (hrepR 0) (hrepR 1)) (rep_compA (hrepR 0) (hrepR 1))) m01


theorem hs100_hasModel :
    ∃ (hz : zasZ0 ∈ hs100P) (E : Subgroup ↥hs100P), HasModel (⟨zasZ0, hz⟩ : ↥hs100P) E := by
  classical
  obtain ⟨E, hspec, hNn, hcardN, e, h, r, hEr, hHr, hcent, hh, hr0, hr1, hrN, hr2, hr01⟩ :=
    i2_perm_model
  have hEP : E ≤ hs100P := hspec.1
  have hzP : zasZ0 ∈ hs100P := hEP hspec.2.1
  have hNP : Subgroup.closure (permsA 100 zasNGens) ≤ hs100P := by
    rw [hNn]; exact inf_le_right
  have hspec' := (isSpecialIn_iff hzP hEP).1 hspec
  obtain ⟨hzE', hab', hcard', -, htr'⟩ := hspec'
  have he_mem : ∀ i, e i ∈ hs100P := fun i => hEP (by
    rw [hEr]; exact Subgroup.subset_closure ⟨i, rfl⟩)
  have hh_mem : ∀ j, h j ∈ hs100P := fun j => hNP (by
    rw [← hHr]; exact Subgroup.subset_closure ⟨j, rfl⟩)
  have hr_mem : ∀ j, r j ∈ hs100P := fun j => hNP (hrN j)
  let e' : Fin 4 → ↥hs100P := fun i => ⟨e i, he_mem i⟩
  let h' : Fin 2 → ↥hs100P := fun j => ⟨h j, hh_mem j⟩
  let r' : Fin 2 → ↥hs100P := fun j => ⟨r j, hr_mem j⟩
  have hmapc : ∀ {n : ℕ} (c : Fin n → ↥hs100P),
      (Subgroup.closure (Set.range c)).map hs100P.subtype =
        Subgroup.closure (Set.range fun i => ((c i : ↥hs100P) : Equiv.Perm (Fin 100))) := by
    intro n c
    rw [MonoidHom.map_closure, ← Set.range_comp]
    rfl
  have hcompc : ∀ {n : ℕ} (c : Fin n → ↥hs100P) (K : Subgroup (Equiv.Perm (Fin 100))),
      Subgroup.closure (Set.range fun i => ((c i : ↥hs100P) : Equiv.Perm (Fin 100))) = K →
        Subgroup.closure (Set.range c) = K.subgroupOf hs100P := by
    intro n c K hK
    rw [Subgroup.subgroupOf, ← hK, ← hmapc c]
    exact (Subgroup.comap_map_eq_self_of_injective hs100P.subtype_injective _).symm
  have hE' : E.subgroupOf hs100P = Subgroup.closure (Set.range e') :=
    (hcompc e' E hEr.symm).symm
  have hN' : normalizer ((E.subgroupOf hs100P : Subgroup ↥hs100P) : Set ↥hs100P) =
      (Subgroup.closure (permsA 100 zasNGens)).subgroupOf hs100P := by
    rw [← Subgroup.subgroupOf_normalizer_eq hEP, hNn]
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun hx => ⟨hx, x.2⟩, fun hx => hx.1⟩
  have hH' : Subgroup.closure (Set.range h') =
      (Subgroup.closure (permsA 100 zasNGens)).subgroupOf hs100P :=
    hcompc h' _ hHr
  refine ⟨hzP, E.subgroupOf hs100P, e', h', r', hE', hab', hcard', hzE', htr', ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [hH', hN']
  · rw [hN', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNP).toEquiv, hcardN]
  · apply le_antisymm
    · intro x hx
      have hxN : x ∈ normalizer ((E.subgroupOf hs100P : Subgroup ↥hs100P) : Set ↥hs100P) :=
        Subgroup.centralizer_le_normalizer _ hx
      rw [hN'] at hxN
      refine hcent (x : Equiv.Perm (Fin 100)) hxN fun i => ?_
      have hei : e' i ∈ E.subgroupOf hs100P := by
        rw [hE']; exact Subgroup.subset_closure ⟨i, rfl⟩
      have := (Subgroup.mem_centralizer_iff.1 hx) (e' i) hei
      exact congrArg Subtype.val this.symm
    · intro x hx
      refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
      have := hab'.1
      rw [isMulCommutative_iff_of_setLike] at this
      exact this y hy x hx
  · intro j i
    apply Subtype.ext
    have := map_vecE hs100P.subtype e' (rho j i)
    refine (hh j i).trans ?_
    exact this.symm
  · intro i
    apply Subtype.ext
    exact (hr0 i).trans (map_vecE hs100P.subtype e' (kx i)).symm
  · intro i
    apply Subtype.ext
    exact (hr1 i).trans (map_vecE hs100P.subtype e' (ky i)).symm
  · intro j
    rw [hH']
    exact hrN j
  · intro j
    exact hr2 j
  · exact hr01

theorem HasModel.map {M M' : Type*} [Group M] [Group M'] (σ : M ≃* M') {z : M} {E : Subgroup M}
    (hm : HasModel z E) : HasModel (σ z) (E.map σ.toMonoidHom) := by
  obtain ⟨e, h, r, hE, hab, hcard, hz, htr, hH, hN, hC, hh, hr0, hr1, hrH, hr2, hr01⟩ := hm
  have key : ∀ y : M, σ y ∈ normalizer ((E.map σ.toMonoidHom : Subgroup M') : Set M') ↔
      y ∈ normalizer (E : Set M) := by
    intro y
    rw [mem_normalizer_iff, mem_normalizer_iff]
    constructor
    · intro hy g
      have := hy (σ g)
      simpa only [Subgroup.mem_map_equiv, map_mul, map_inv, MulEquiv.symm_apply_apply] using this
    · intro hy g'
      obtain ⟨g, rfl⟩ := σ.surjective g'
      have := hy g
      simpa only [Subgroup.mem_map_equiv, map_mul, map_inv, MulEquiv.symm_apply_apply] using this
  have hnorm : normalizer ((E.map σ.toMonoidHom : Subgroup M') : Set M') =
      (normalizer (E : Set M)).map σ.toMonoidHom := by
    ext x
    obtain ⟨y, rfl⟩ := σ.surjective x
    rw [key, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  have hmapc : ∀ {n : ℕ} (c : Fin n → M),
      Subgroup.closure (Set.range fun i => σ (c i)) =
        (Subgroup.closure (Set.range c)).map σ.toMonoidHom := by
    intro n c
    rw [MonoidHom.map_closure, ← Set.range_comp]
    rfl
  have hcent0 : centralizer ((E.map σ.toMonoidHom : Subgroup M') : Set M') =
      (centralizer (E : Set M)).map σ.toMonoidHom := by
    ext x
    obtain ⟨y, rfl⟩ := σ.surjective x
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply, Subgroup.mem_centralizer_iff,
      Subgroup.mem_centralizer_iff]
    constructor
    · intro hy g hg
      have := hy (σ g) (Subgroup.mem_map_of_mem _ hg)
      exact σ.injective (by simpa using this)
    · intro hy g' hg'
      obtain ⟨g, hg, rfl⟩ := hg'
      have := hy g hg
      simpa using congrArg σ this
  have hcent : centralizer ((E.map σ.toMonoidHom : Subgroup M') : Set M') =
      E.map σ.toMonoidHom := by rw [hcent0, hC]
  refine ⟨fun i => σ (e i), fun j => σ (h j), fun j => σ (r j), ?_, isElemAbelian_map _ σ.injective hab,
    ?_, Subgroup.mem_map_of_mem _ hz, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hE, hmapc]
  · rw [Subgroup.card_map_of_injective σ.injective, hcard]
  · rintro _ ⟨x, hx, rfl⟩ hne
    obtain ⟨a, ha, hax⟩ := htr x hx (by rintro rfl; exact hne (map_one _))
    refine ⟨σ a, (key a).2 ha, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_inv, ← map_mul, ← map_mul, hax]
  · rw [hmapc, hH, hnorm]
  · rw [hnorm, Subgroup.card_map_of_injective σ.injective, hN]
  · exact hcent
  · intro j i
    rw [← map_inv, ← map_mul, ← map_mul, hh j i]
    exact map_vecE σ.toMonoidHom e _
  · intro i
    rw [← map_inv, ← map_mul, ← map_mul, hr0 i]
    exact map_vecE σ.toMonoidHom e _
  · intro i
    rw [← map_inv, ← map_mul, ← map_mul, hr1 i]
    exact map_vecE σ.toMonoidHom e _
  · intro j
    rw [hmapc]
    exact Subgroup.mem_map_of_mem _ (hrH j)
  · intro j
    rw [← map_mul]
    exact Subgroup.mem_map_of_mem _ (hr2 j)
  · rw [← map_mul, ← map_mul]
    exact Subgroup.mem_map_of_mem _ hr01

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.I2
