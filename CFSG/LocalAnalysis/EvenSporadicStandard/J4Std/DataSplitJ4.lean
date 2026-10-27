module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.Interface
public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.Transport
public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.DataSplitGroup
public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.DataSplitCheck
public import CFSG.Sporadic.J4
public import CFSG.Sporadic.J4.QTOutNorm

public section

namespace CFSG.EvenSporadicStandard.J4Std.DataSplit

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT Matrix

section Basis

variable {G : Type} [Group G] (ι : J →* G)

@[expose] noncomputable def eps (c : Fin 11 → F2) : G := ι (eta uJ 11 (maskOf c))

variable (hM : MatFacts)
include hM

theorem eps_add (c d : Fin 11 → F2) : eps ι (c + d) = eps ι c * eps ι d := by
  simp only [eps, maskOf_add]
  rw [eta_xor (elem_uJ hM) le_rfl, map_mul]

omit hM in
theorem eps_mem (c : Fin 11 → F2) : eps ι c ∈ (Eg uJ 11).map ι :=
  Subgroup.mem_map_of_mem ι (eta_mem_Eg 11 le_rfl _)

theorem eps_inj (hι : Function.Injective ι) : Function.Injective (eps ι) := by
  intro c d h
  exact maskOf_injective (eta_inj hM _ (maskOf_lt c) _ (maskOf_lt d) (hι h))

theorem eps_surj : ∀ u ∈ (Eg uJ 11).map ι, ∃ c, eps ι c = u := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨m, hm, rfl⟩ := (mem_Eg_iff (elem_uJ hM)).1 hx
  refine ⟨vecOfMask m, ?_⟩
  simp only [eps, maskOf_vecOfMask hm]

theorem eps_conj (k : Fin 6) (c : Fin 11 → F2) :
    ι (XJ (letterOf k)) * eps ι c * (ι (XJ (letterOf k)))⁻¹ = eps ι (c ᵥ* Amat k) := by
  have hℓ : letterOf k ∈ letters := letterOf_mem k
  have h1 := hX_all hM hℓ (maskOf c)
  have h3 : vecOfMask (act (letterOf k) (maskOf c)) = vecOfMask (maskOf (c ᵥ* Amat k)) := by
    rw [vecOfMask_maskOf]
    show vecOfMask (rowsXor (letterRow (letterOf k)) 11 (maskOf c)) = _
    rw [vecOfMask_rowsXor, vecOfMask_maskOf]
    rfl
  have key : eta uJ 11 (act (letterOf k) (maskOf c)) = eta uJ 11 (maskOf (c ᵥ* Amat k)) := by
    apply eta_congr_testBit
    intro j hj
    have := congrFun h3 ⟨j, hj⟩
    simp only [vecOfMask] at this
    cases h4 : (act (letterOf k) (maskOf c)).testBit j <;>
      cases h5 : (maskOf (c ᵥ* Amat k)).testBit j <;> simp_all
  unfold eps
  rw [← key, ← h1]
  simp

end Basis

section Main

variable
  {G : Type} [Group G] (ι : J →* G)

theorem Hloc_eq (hι : Function.Injective ι) :
    Hloc ι.range ((Eg uJ 11).map ι) = Hj.map ι := by
  rw [Hloc_map ι hι]
  congr 1
  unfold Hloc
  rw [inf_top_eq]
  exact normalizer_Eg_eq_Hj j4Facts

theorem exists_letterOf_eq {ℓ : ℤ} (hℓ : ℓ ∈ letters) : ∃ k : Fin 6, letterOf k = ℓ := by
  rcases letters_cases hℓ with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, by decide⟩
  · exact ⟨1, by decide⟩
  · exact ⟨2, by decide⟩
  · exact ⟨3, by decide⟩
  · exact ⟨4, by decide⟩
  · exact ⟨5, by decide⟩

theorem comm_of_conj_eq {H : Type*} [Group H] {x y : H} (h : x * y * x⁻¹ = y) :
    x * y = y * x :=
  calc x * y = (x * y * x⁻¹) * x := by group
    _ = y * x := by rw [h]

theorem word_prod_mem_Eg (hM : MatFacts) (hF : J4Facts) {w : List ℤ}
    (hwl : ∀ ℓ ∈ w, ℓ ∈ letters) (htriv : ∀ j < 11, w.foldr act (2 ^ j) = 2 ^ j) :
    (w.map XJ).prod ∈ Eg uJ 11 := by
  have hxH : (w.map XJ).prod ∈ Hj := by
    refine Subgroup.list_prod_mem Hj (fun y hy => ?_)
    obtain ⟨ℓ, hℓ, rfl⟩ := List.mem_map.1 hy
    exact XJ_mem (hwl ℓ hℓ)
  have hu : ∀ j < 11, (w.map XJ).prod * uJ j = uJ j * (w.map XJ).prod := by
    intro j hj
    have h1 := word_conj XJ act w (fun ℓ hℓ c => hX_all hM (hwl ℓ hℓ) c) (2 ^ j)
    rw [htriv j hj, eta_two_pow hj] at h1
    have h2 : (w.map XJ).prod * uJ j * ((w.map XJ).prod)⁻¹ = uJ j := h1
    exact comm_of_conj_eq (x := (w.map XJ).prod) (y := uJ j) h2
  generalize (w.map XJ).prod = x at hxH hu ⊢
  have hcomm : ∀ y ∈ Eg uJ 11, x * y = y * x := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨j, hj, rfl⟩ := hy
      exact hu j hj
    | one => rw [mul_one, one_mul]
    | mul a b _ _ ha hb => rw [← mul_assoc, ha, mul_assoc, hb, mul_assoc]
    | inv a _ ha =>
      calc x * a⁻¹ = a⁻¹ * (a * x) * a⁻¹ := by group
        _ = a⁻¹ * (x * a) * a⁻¹ := by rw [ha]
        _ = a⁻¹ * x := by group
  exact centralizer_Hj hM hF x hxH hcomm

theorem relator_mem_Eg (r : Fin 5) :
    (((splitWordsF r).map letterOf).map XJ).prod ∈ Eg uJ 11 :=
  word_prod_mem_Eg j4Facts.mat j4Facts
    (fun ℓ hℓ => by
      obtain ⟨k, -, rfl⟩ := List.mem_map.1 hℓ
      exact letterOf_mem k)
    (fun j hj => relators_trivial r j hj)

theorem splitData_J4' (hι : Function.Injective ι) :
    SplitData ι.range ((Eg uJ 11).map ι) := by
  intro z W hzW hz2 hzU hzH hzU' hUW hcent hsq hHW hphi hphiS hker
  have hF : J4Facts := j4Facts
  have hM : MatFacts := hF.mat
  have hHeq := Hloc_eq ι hι
  have hE : SplitHyp ((Eg uJ 11).map ι) W z (eps ι) :=
    ⟨hzW, hz2, hzU, hzU', hUW, hcent, hsq, hphi, hphiS, hker, eps_add ι hM,
      eps_inj ι hM hι, eps_mem ι, eps_surj ι hM⟩
  have hgH : ∀ k : Fin 6, ι (XJ (letterOf k)) ∈ Hloc ι.range ((Eg uJ 11).map ι) := by
    intro k
    rw [hHeq]
    exact Subgroup.mem_map_of_mem ι (XJ_mem (letterOf_mem k))
  have hH : ∀ h ∈ Hloc ι.range ((Eg uJ 11).map ι),
      h ∈ Subgroup.closure (Set.range fun k : Fin 6 => ι (XJ (letterOf k))) := by
    intro h hh
    rw [hHeq] at hh
    obtain ⟨x, hx, rfl⟩ := hh
    refine Subgroup.closure_induction
      (p := fun x _ => ι x ∈ Subgroup.closure (Set.range fun k : Fin 6 => ι (XJ (letterOf k))))
      ?_ ?_ ?_ ?_ (Hj_le_closure hx)
    · rintro _ ⟨ℓ, hℓ, rfl⟩
      obtain ⟨k, rfl⟩ := exists_letterOf_eq hℓ
      exact Subgroup.subset_closure ⟨k, rfl⟩
    · rw [map_one]; exact Subgroup.one_mem _
    · intro a b _ _ ha hb
      rw [map_mul]; exact Subgroup.mul_mem _ ha hb
    · intro a _ ha
      rw [map_inv]; exact Subgroup.inv_mem _ ha
  have hw : ∀ r : Fin 5,
      ((splitWordsF r).map fun k => ι (XJ (letterOf k))).prod ∈ (Eg uJ 11).map ι := by
    intro r
    have e : ((splitWordsF r).map fun k => ι (XJ (letterOf k))).prod =
        ι ((((splitWordsF r).map letterOf).map XJ).prod) := by
      rw [map_list_prod, List.map_map, List.map_map]
      rfl
    rw [e]
    exact Subgroup.mem_map_of_mem ι (relator_mem_Eg r)
  exact exists_split_of_gens hE (H := Hloc ι.range ((Eg uJ 11).map ι))
    (g := fun k : Fin 6 => ι (XJ (letterOf k))) (A := Amat)
    (fun h hh u hu => Hloc_conj_mem hh hu) hHW hzH hgH hH (fun k c => eps_conj ι hM k c)
    (words := splitWordsF) hw (Psi := splitPsi) (Cm := splitCm) dual_identity

end Main

end CFSG.EvenSporadicStandard.J4Std.DataSplit

namespace CFSG.EvenSporadicStandard.J4Std

theorem splitData_J4
    {G : Type} [Group G] (ι : CFSG.Sporadic.J4.J →* G) (hι : Function.Injective ι) :
    SplitData ι.range ((CFSG.Sporadic.J4.QT.Eg CFSG.Sporadic.J4.QT.uJ 11).map ι) :=
  DataSplit.splitData_J4' ι hι

end CFSG.EvenSporadicStandard.J4Std
