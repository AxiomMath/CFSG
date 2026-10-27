module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GTS8Lift
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Commute.Defs
public import Mathlib.Algebra.Group.End

public section

namespace CFSG.OddStandard.SmallF3.Omega

local notation "SL23" => Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)

private lemma l34g_conj_closure {E : Type*} [Group E] {it jt ct : E}
    (hct3 : ct ^ 3 = 1) (hctit : ct * it * ct⁻¹ = jt) (hctjt : ct * jt * ct⁻¹ = it * jt) :
    (∀ q ∈ Subgroup.closure ({it, jt} : Set E),
        ct * q * ct⁻¹ ∈ Subgroup.closure ({it, jt} : Set E)) ∧
      (∀ q ∈ Subgroup.closure ({it, jt} : Set E),
        ct⁻¹ * q * ct ∈ Subgroup.closure ({it, jt} : Set E)) := by
  let Q := Subgroup.closure ({it, jt} : Set E)
  change (∀ q ∈ Q, ct * q * ct⁻¹ ∈ Q) ∧ (∀ q ∈ Q, ct⁻¹ * q * ct ∈ Q)
  have hitjt : it * jt = ct * jt * ct⁻¹ := hctjt.symm
  have hctinv : ct⁻¹ = ct ^ 2 := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_succ', hct3]
  constructor
  · intro q hq
    have hle : Q ≤ Q.comap (MulAut.conj ct : E →* E) := by
      change Subgroup.closure ({it, jt} : Set E) ≤
        (Subgroup.closure ({it, jt} : Set E)).comap (MulAut.conj ct : E →* E)
      rw [Subgroup.closure_le]
      intro g hg
      rcases hg with h | h
      · rw [h]
        change ct * it * ct⁻¹ ∈ Q
        rw [hctit]
        exact Subgroup.subset_closure (by simp)
      · rw [h]
        change ct * jt * ct⁻¹ ∈ Q
        rw [← hitjt]
        exact Q.mul_mem (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp))
    have := hle hq
    change ct * q * ct⁻¹ ∈ Q at this
    exact this
  · intro q hq
    have hle : Q ≤ Q.comap (MulAut.conj ct⁻¹ : E →* E) := by
      change Subgroup.closure ({it, jt} : Set E) ≤
        (Subgroup.closure ({it, jt} : Set E)).comap (MulAut.conj ct⁻¹ : E →* E)
      rw [Subgroup.closure_le]
      intro g hg
      rcases hg with h | h
      · rw [h]
        change ct⁻¹ * it * (ct⁻¹)⁻¹ ∈ Q
        rw [inv_inv]
        have h1 : ct⁻¹ * it * ct = it * jt := by
          have hct2inv : (ct ^ 2)⁻¹ = ct := by
            apply inv_eq_of_mul_eq_one_right
            rw [← pow_succ, hct3]
          calc ct⁻¹ * it * ct = ct ^ 2 * it * ct := by rw [hctinv]
            _ = ct ^ 2 * it * (ct ^ 2)⁻¹ := by
                  nth_rewrite 2 [← hct2inv]
                  rfl
            _ = ct * (ct * it * ct⁻¹) * ct⁻¹ := by simp only [pow_two]; group
            _ = ct * jt * ct⁻¹ := by rw [hctit]
            _ = it * jt := hctjt
        rw [h1]
        exact Q.mul_mem (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp))
      · rw [h]
        change ct⁻¹ * jt * (ct⁻¹)⁻¹ ∈ Q
        rw [inv_inv]
        have h2 : ct⁻¹ * jt * ct = it := by rw [← hctit]; group
        rw [h2]
        exact Subgroup.subset_closure (by simp)
    have := hle hq
    change ct⁻¹ * q * (ct⁻¹)⁻¹ ∈ Q at this
    rw [inv_inv] at this
    exact this

private lemma l34g_mem_closure_three {E : Type*} [Group E] {it jt ct : E}
    (hct3 : ct ^ 3 = 1) (hctit : ct * it * ct⁻¹ = jt) (hctjt : ct * jt * ct⁻¹ = it * jt) :
    ∀ z ∈ Subgroup.closure ({it, jt, ct} : Set E),
      ∃ q ∈ Subgroup.closure ({it, jt} : Set E), ∃ c ∈ Subgroup.zpowers ct, z = q * c := by
  obtain ⟨hct_conj, hct_inv_conj⟩ := l34g_conj_closure hct3 hctit hctjt
  let Q := Subgroup.closure ({it, jt} : Set E)
  let C := Subgroup.zpowers ct
  change ∀ z ∈ Subgroup.closure ({it, jt, ct} : Set E), ∃ q ∈ Q, ∃ c ∈ C, z = q * c
  have hitQ : it ∈ Q := Subgroup.subset_closure (by simp)
  have hjtQ : jt ∈ Q := Subgroup.subset_closure (by simp)
  have hctC : ct ∈ C := Subgroup.mem_zpowers ct
  intro z hz
  refine Subgroup.closure_induction_left (s := ({it, jt, ct} : Set E))
    (p := fun z _ => ∃ q ∈ Q, ∃ c ∈ C, z = q * c)
    ⟨1, Q.one_mem, 1, C.one_mem, by simp⟩ ?_ ?_ hz
  · intro g hg w hw ih
    obtain ⟨q, hq, c, hc, rfl⟩ := ih
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with h | h | h
    · rw [h]
      exact ⟨it * q, Q.mul_mem hitQ hq, c, hc, by group⟩
    · rw [h]
      exact ⟨jt * q, Q.mul_mem hjtQ hq, c, hc, by group⟩
    · rw [h]
      exact ⟨ct * q * ct⁻¹, hct_conj q hq, ct * c, C.mul_mem hctC hc, by group⟩
  · intro g hg w hw ih
    obtain ⟨q, hq, c, hc, rfl⟩ := ih
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with h | h | h
    · rw [h]
      exact ⟨it⁻¹ * q, Q.mul_mem (Q.inv_mem hitQ) hq, c, hc, by group⟩
    · rw [h]
      exact ⟨jt⁻¹ * q, Q.mul_mem (Q.inv_mem hjtQ) hq, c, hc, by group⟩
    · rw [h]
      exact ⟨ct⁻¹ * q * ct, hct_inv_conj q hq, ct⁻¹ * c, C.mul_mem (C.inv_mem hctC) hc,
        by group⟩

private lemma l34g_card_closure_three_le_24 {E : Type*} [Group E] [Finite E] {it jt ct : E}
    (hct3 : ct ^ 3 = 1) (hctit : ct * it * ct⁻¹ = jt) (hctjt : ct * jt * ct⁻¹ = it * jt)
    (hit4 : it ^ 4 = 1) (hjt2 : jt ^ 2 = it ^ 2) (hconj : jt * it * jt⁻¹ = it⁻¹) :
    Nat.card (Subgroup.closure ({it, jt, ct} : Set E)) ≤ 24 := by
  let Q := Subgroup.closure ({it, jt} : Set E)
  let C := Subgroup.zpowers ct
  let M := Subgroup.closure ({it, jt, ct} : Set E)
  change Nat.card M ≤ 24
  haveI : Fintype E := Fintype.ofFinite E
  have hQle8 : Nat.card Q ≤ 8 := by
    change Nat.card (Subgroup.closure ({it, jt} : Set E)) ≤ 8
    exact l34g_card_closure_pair_le_eight hit4 hjt2 hconj
  have hCle3 : Nat.card C ≤ 3 := by
    change Nat.card (Subgroup.zpowers ct) ≤ 3
    rw [Nat.card_eq_fintype_card]
    exact card_zpowers_le ct (by norm_num) hct3
  have hdecomp := l34g_mem_closure_three hct3 hctit hctjt
  have hQM : Q ≤ M := by
    change Subgroup.closure ({it, jt} : Set E) ≤ Subgroup.closure ({it, jt, ct} : Set E)
    exact Subgroup.closure_mono (by rintro x (rfl | rfl) <;> simp)
  have hCM : C ≤ M := by
    change Subgroup.zpowers ct ≤ Subgroup.closure ({it, jt, ct} : Set E)
    exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
  have hsurj : Function.Surjective (fun p : Q × C =>
      (⟨p.1.1 * p.2.1, M.mul_mem (hQM p.1.2) (hCM p.2.2)⟩ : M)) := by
    intro z
    obtain ⟨q, hq, c, hc, hqc⟩ := hdecomp z.1 z.2
    exact ⟨(⟨q, hq⟩, ⟨c, hc⟩), Subtype.ext hqc.symm⟩
  have h1 : Nat.card M ≤ Nat.card (Q × C) := Nat.card_le_card_of_surjective _ hsurj
  rw [Nat.card_prod] at h1
  have h3 : Nat.card Q * Nat.card C ≤ 8 * 3 := Nat.mul_le_mul hQle8 hCle3
  omega

private lemma l34g_card_closure_three_ge_24 {E : Type*} [Group E] [Finite E] {it jt ct : E}
    (ρ : E →* SL23) (hρit : ρ it = slI) (hρjt : ρ jt = slJ) (hρct : ρ ct = slC) :
    24 ≤ Nat.card (Subgroup.closure ({it, jt, ct} : Set E)) := by
  let M := Subgroup.closure ({it, jt, ct} : Set E)
  change 24 ≤ Nat.card M
  have hitM : it ∈ M := Subgroup.subset_closure (by simp)
  have hjtM : jt ∈ M := Subgroup.subset_closure (by simp)
  have hctM : ct ∈ M := Subgroup.subset_closure (by simp)
  have hmapM : M.map ρ = ⊤ := by
    rw [eq_top_iff]
    intro g _
    obtain ⟨a, b, t, rfl⟩ := sl23_rep g
    have hI : slI ∈ M.map ρ := ⟨it, hitM, hρit⟩
    have hJ : slJ ∈ M.map ρ := ⟨jt, hjtM, hρjt⟩
    have hC : slC ∈ M.map ρ := ⟨ct, hctM, hρct⟩
    exact (M.map ρ).mul_mem ((M.map ρ).mul_mem ((M.map ρ).pow_mem hI a)
      ((M.map ρ).pow_mem hJ b)) ((M.map ρ).pow_mem hC t)
  have h1 : Nat.card (M.map ρ) ≤ Nat.card M :=
    Nat.card_le_card_of_surjective
      (fun x : M => (⟨ρ x.1, Subgroup.mem_map_of_mem ρ x.2⟩ : M.map ρ)) (by
        rintro ⟨y, hy⟩
        obtain ⟨x, hx, rfl⟩ := hy
        exact ⟨⟨x, hx⟩, rfl⟩)
  rw [hmapM, Subgroup.card_top, sl23_card] at h1
  exact h1

private lemma l34g_sigma_not_mem {E : Type*} [Group E] [Finite E]
    (ρ : E →* SL23) {σ : E} (hσ1 : σ ≠ 1)
    (hker : ∀ e : E, ρ e = 1 ↔ e = 1 ∨ e = σ)
    {it jt ct : E} (hρit : ρ it = slI) (hρjt : ρ jt = slJ) (hρct : ρ ct = slC)
    (hMcard : Nat.card (Subgroup.closure ({it, jt, ct} : Set E)) = 24) :
    σ ∉ Subgroup.closure ({it, jt, ct} : Set E) := by
  intro hσmem
  let M := Subgroup.closure ({it, jt, ct} : Set E)
  have hρσ : ρ σ = 1 := (hker σ).mpr (Or.inr rfl)
  have hitM : it ∈ M := Subgroup.subset_closure (by simp)
  have hjtM : jt ∈ M := Subgroup.subset_closure (by simp)
  have hctM : ct ∈ M := Subgroup.subset_closure (by simp)
  have hmapM : M.map ρ = ⊤ := by
    rw [eq_top_iff]
    intro g _
    obtain ⟨a, b, t, rfl⟩ := sl23_rep g
    have hI : slI ∈ M.map ρ := ⟨it, hitM, hρit⟩
    have hJ : slJ ∈ M.map ρ := ⟨jt, hjtM, hρjt⟩
    have hC : slC ∈ M.map ρ := ⟨ct, hctM, hρct⟩
    exact (M.map ρ).mul_mem ((M.map ρ).mul_mem ((M.map ρ).pow_mem hI a)
      ((M.map ρ).pow_mem hJ b)) ((M.map ρ).pow_mem hC t)
  let ρM : M →* SL23 := ρ.comp M.subtype
  have hρMsurj : Function.Surjective ρM := by
    intro g
    have hg : g ∈ M.map ρ := by rw [hmapM]; exact Subgroup.mem_top g
    obtain ⟨e, he, heq⟩ := hg
    exact ⟨⟨e, he⟩, heq⟩
  have hcardM : Nat.card M = 24 := hMcard
  have hbij : Function.Bijective ρM :=
    (Nat.bijective_iff_surjective_and_card ρM).mpr ⟨hρMsurj, by rw [hcardM, sl23_card]⟩
  have h1 : ρM ⟨σ, hσmem⟩ = ρM 1 := by
    show ρ σ = ρ 1
    rw [hρσ, map_one]
  exact hσ1 (Subtype.ext_iff.mp (hbij.1 h1))

private lemma l34g_odd_mem_closure_three {E : Type*} [Group E]
    (ρ : E →* SL23) {σ : E} (hσ2 : σ * σ = 1) (hσc : ∀ e : E, e * σ = σ * e)
    (hker : ∀ e : E, ρ e = 1 ↔ e = 1 ∨ e = σ)
    {it jt ct : E} (hρit : ρ it = slI) (hρjt : ρ jt = slJ) (hρct : ρ ct = slC)
    (hσM : σ ∉ Subgroup.closure ({it, jt, ct} : Set E)) :
    ∀ e : E, Odd (orderOf e) → e ∈ Subgroup.closure ({it, jt, ct} : Set E) := by
  let M := Subgroup.closure ({it, jt, ct} : Set E)
  have hσM' : σ ∉ M := hσM
  have hitM : it ∈ M := Subgroup.subset_closure (by simp)
  have hjtM : jt ∈ M := Subgroup.subset_closure (by simp)
  have hctM : ct ∈ M := Subgroup.subset_closure (by simp)
  intro e he
  change e ∈ M
  obtain ⟨a, b, t, ha⟩ := sl23_rep (ρ e)
  set n : E := it ^ (a : ℕ) * jt ^ (b : ℕ) * ct ^ (t : ℕ) with hn
  have hnM : n ∈ M := by
    rw [hn]
    exact M.mul_mem (M.mul_mem (M.pow_mem hitM a) (M.pow_mem hjtM b)) (M.pow_mem hctM t)
  have hρn : ρ n = ρ e := by
    rw [hn, map_mul, map_mul, map_pow, map_pow, map_pow, hρit, hρjt, hρct, ← ha]
  have hkere : n⁻¹ * e ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hρn, inv_mul_cancel]
  have hcases : n⁻¹ * e = 1 ∨ n⁻¹ * e = σ := (hker _).mp hkere
  rcases hcases with h | h
  · have : e = n := by
      calc e = n * (n⁻¹ * e) := by group
        _ = n * 1 := by rw [h]
        _ = n := mul_one n
    rw [this]; exact hnM
  · exfalso
    have he_eq : e = n * σ := by
      calc e = n * (n⁻¹ * e) := by group
        _ = n * σ := by rw [h]
    have hcomm : Commute n σ := hσc n
    have hpow : e ^ orderOf e = n ^ orderOf e * σ := by
      calc e ^ orderOf e = (n * σ) ^ orderOf e := by
            nth_rewrite 1 [he_eq]
            rfl
        _ = n ^ orderOf e * σ ^ orderOf e := hcomm.mul_pow (orderOf e)
        _ = n ^ orderOf e * σ := by
              congr 1
              obtain ⟨k, hk⟩ := he
              rw [hk, pow_succ, pow_mul, pow_two, hσ2, one_pow, one_mul]
    rw [pow_orderOf_eq_one] at hpow
    have hσeq : σ = (n ^ orderOf e)⁻¹ := eq_inv_of_mul_eq_one_right hpow.symm
    exact hσM' (hσeq ▸ M.inv_mem (M.pow_mem hnM (orderOf e)))

theorem l34g_not_mem_closure_odd_sl23 {E : Type} [Group E] [Finite E]
    (ρ : E →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) (hρ : Function.Surjective ρ)
    {σ : E} (hσ2 : σ * σ = 1) (hσ1 : σ ≠ 1) (hσc : ∀ e : E, e * σ = σ * e)
    (hker : ∀ e : E, ρ e = 1 ↔ e = 1 ∨ e = σ) :
    σ ∉ Subgroup.closure {e : E | Odd (orderOf e)} := by
  classical
  obtain ⟨ct, it, jt, hρct, hρit, hρjt, hct3, hctit, hit4, hjt2, hconj, hctjt⟩ :=
    l34g_sl23_lifts ρ hρ hσ2 hσ1 hσc hker
  have hMle : Nat.card (Subgroup.closure ({it, jt, ct} : Set E)) ≤ 24 :=
    l34g_card_closure_three_le_24 hct3 hctit hctjt hit4 hjt2 hconj
  have hMge : 24 ≤ Nat.card (Subgroup.closure ({it, jt, ct} : Set E)) :=
    l34g_card_closure_three_ge_24 ρ hρit hρjt hρct
  have hMcard : Nat.card (Subgroup.closure ({it, jt, ct} : Set E)) = 24 :=
    le_antisymm hMle hMge
  have hσM : σ ∉ Subgroup.closure ({it, jt, ct} : Set E) :=
    l34g_sigma_not_mem ρ hσ1 hker hρit hρjt hρct hMcard
  have hodd : ∀ e : E, Odd (orderOf e) → e ∈ Subgroup.closure ({it, jt, ct} : Set E) :=
    l34g_odd_mem_closure_three ρ hσ2 hσc hker hρit hρjt hρct hσM
  intro hσclosure
  have hle : Subgroup.closure {e : E | Odd (orderOf e)} ≤
      Subgroup.closure ({it, jt, ct} : Set E) := by
    rw [Subgroup.closure_le]
    exact fun e he => hodd e he
  exact hσM (hle hσclosure)

end CFSG.OddStandard.SmallF3.Omega
