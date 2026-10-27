module

public import CFSG.LocalAnalysis.ComponentClassification.Layer

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open Subgroup

variable {X : Type*} [Group X] [Finite X]

theorem zpow_notMem_normalizer_of_not_dvd {p : ℕ} (hp : p.Prime) {d : X} (hd : d ^ p = 1)
    {K : Subgroup X} (hdK : d ∉ normalizer (K : Set X)) {s : ℤ} (hs : ¬ (p : ℤ) ∣ s) :
    d ^ s ∉ normalizer (K : Set X) := by
  intro hmem
  have hirr : Irreducible (p : ℤ) := (Nat.prime_iff_prime_int.mp hp).irreducible
  obtain ⟨a, b, hab⟩ : IsCoprime (p : ℤ) s := hirr.coprime_iff_not_dvd.mpr hs
  apply hdK
  have h1 : d = (d ^ s) ^ b := by
    calc d = d ^ (1 : ℤ) := (zpow_one d).symm
      _ = d ^ (a * p + b * s) := by rw [hab]
      _ = (d ^ (p : ℤ)) ^ a * (d ^ s) ^ b := by
          rw [zpow_add, mul_comm a, zpow_mul, mul_comm b, zpow_mul]
      _ = (d ^ s) ^ b := by rw [zpow_natCast, hd, one_zpow, one_mul]
  rw [h1]
  exact zpow_mem hmem b

theorem isComponentOf_map_conj (g : X) {K : Subgroup X} (hK : IsComponentOf K ⊤) :
    IsComponentOf (K.map (MulAut.conj g).toMonoidHom) ⊤ :=
  (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj g) K).mpr hK

theorem commute_conj_of_mem {K : Subgroup X} (hK : IsComponentOf K ⊤) {g : X}
    (hg : g ∉ normalizer (K : Set X)) {a b : X} (ha : a ∈ K) (hb : b ∈ K) :
    Commute a (g * b * g⁻¹) := by
  have hne : K ≠ K.map (MulAut.conj g).toMonoidHom := by
    intro h
    apply hg
    rw [mem_normalizer_iff_map_conj_eq]
    exact h.symm
  have hcomm := CFSG.ComponentClassification.LocalComponents.commute_of_ne K _ hK
    (isComponentOf_map_conj g hK) hne
  have hmem : g * b * g⁻¹ ∈ K.map (MulAut.conj g).toMonoidHom :=
    ⟨b, hb, rfl⟩
  exact (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm ha) _ hmem).symm

theorem list_prod_pow_eq_one {N : ℕ} :
    ∀ l : List X, l.Pairwise Commute → (∀ a ∈ l, a ^ N = 1) → l.prod ^ N = 1
  | [], _, _ => by simp
  | a :: t, hl, ha => by
    rw [List.prod_cons]
    have hc : Commute a t.prod :=
      Commute.list_prod_right t a (fun b hb => (List.pairwise_cons.mp hl).1 b hb)
    rw [hc.mul_pow, ha a List.mem_cons_self,
      list_prod_pow_eq_one t (List.pairwise_cons.mp hl).2
        (fun b hb => ha b (List.mem_cons_of_mem a hb)), one_mul]

theorem exists_diagonal_of_not_mem_normalizer {p : ℕ} (hp : p.Prime) {d x : X} (hd : d ^ p = 1)
    {K : Subgroup X} (hK : IsComponentOf K ⊤) (hdK : d ∉ normalizer (K : Set X)) (hx : x ∈ K) :
    ∃ y : X, y ∈ CFSG.ComponentClassification.Layer.subgroup X ∧ d * y * d⁻¹ = y ∧
      (∀ N : ℕ, x ^ N = 1 → y ^ N = 1) ∧ ∀ g ∈ K, g * y * g⁻¹ = y → g * x * g⁻¹ = x := by
  classical
  set c : ℤ → X := fun i => d ^ i * x * (d ^ i)⁻¹ with hc
  have hcomm0 : ∀ s : ℤ, ¬ (p : ℤ) ∣ s → ∀ g ∈ K, Commute g (c s) := fun s hs g hg =>
    commute_conj_of_mem hK (zpow_notMem_normalizer_of_not_dvd hp hd hdK hs) hg hx
  have hcij : ∀ i j : ℤ, ¬ (p : ℤ) ∣ (j - i) → Commute (c i) (c j) := by
    intro i j hij
    have h := (hcomm0 (j - i) hij x hx).eq
    have hcj : c j = d ^ i * c (j - i) * (d ^ i)⁻¹ := by
      simp only [hc]
      rw [show d ^ j = d ^ i * d ^ (j - i) by rw [← zpow_add]; congr 1; ring]
      group
    show c i * c j = c j * c i
    rw [hcj]
    calc c i * (d ^ i * c (j - i) * (d ^ i)⁻¹)
        = d ^ i * (x * c (j - i)) * (d ^ i)⁻¹ := by simp only [hc]; group
      _ = d ^ i * (c (j - i) * x) * (d ^ i)⁻¹ := by rw [h]
      _ = d ^ i * c (j - i) * (d ^ i)⁻¹ * c i := by simp only [hc]; group
  have hc0 : c 0 = x := by simp [hc]
  have hshift : ∀ i : ℤ, d * c i * d⁻¹ = c (i + 1) := by
    intro i
    simp only [hc]
    rw [zpow_add_one]
    group
  obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.pos; omega⟩
  have hdq : d ^ (q + 1) = 1 := hq ▸ hd
  have hcp : c ((q : ℤ) + 1) = c 0 := by
    simp only [hc]
    rw [← Nat.cast_succ, zpow_natCast, hdq]
    simp
  set t : List X := (List.range q).map (fun i : ℕ => c ((i : ℤ) + 1)) with ht
  have hl : (List.range (q + 1)).map (fun i : ℕ => c (i : ℤ)) = c 0 :: t := by
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    simp [ht, Function.comp_def]
  have hpair : ((List.range (q + 1)).map (fun i : ℕ => c (i : ℤ))).Pairwise Commute := by
    rw [List.pairwise_map]
    refine List.Nodup.pairwise_of_forall_ne (List.nodup_range) ?_
    intro i hi j hj hij
    rw [List.mem_range] at hi hj
    refine hcij i j fun hdvd => hij ?_
    have h0 := Int.eq_zero_of_abs_lt_dvd (m := (p : ℤ)) (x := (j : ℤ) - i) hdvd (by
      rw [abs_lt]; constructor <;> omega)
    omega
  refine ⟨((List.range (q + 1)).map (fun i : ℕ => c (i : ℤ))).prod, ?_, ?_, ?_, ?_⟩
  · refine Subgroup.list_prod_mem _ ?_
    intro a ha
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp ha
    exact CFSG.ComponentClassification.Layer.component_le
      (isComponentOf_map_conj (d ^ (i : ℤ)) hK) ⟨x, hx, rfl⟩
  · have hmap := map_list_prod (MulAut.conj d)
      ((List.range (q + 1)).map (fun i : ℕ => c (i : ℤ)))
    simp only [MulAut.conj_apply] at hmap
    rw [hmap, List.map_map]
    have h1 : ((MulAut.conj d : X → X) ∘ fun i : ℕ => c (i : ℤ)) =
        fun i : ℕ => c ((i : ℤ) + 1) := by
      funext i
      exact hshift (i : ℤ)
    have h2 : (List.range (q + 1)).map (fun i : ℕ => c ((i : ℤ) + 1)) = t ++ [c 0] := by
      rw [List.range_succ, List.map_append, List.map_singleton, hcp]
    rw [h1, h2, hl]
    exact ((List.perm_append_singleton (c 0) t).symm.prod_eq' (hl ▸ hpair)).symm
  · intro N hN
    refine list_prod_pow_eq_one _ hpair ?_
    intro a ha
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp ha
    simp only [hc]
    rw [conj_pow, hN]
    simp
  · intro g hg hgy
    have hr : ∀ a ∈ t, Commute g a := by
      intro a ha
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
      rw [List.mem_range] at hi
      refine hcomm0 _ ?_ g hg
      intro hdvd
      have h0 := Int.eq_zero_of_abs_lt_dvd (m := (p : ℤ)) (x := (i : ℤ) + 1) hdvd (by
        rw [abs_lt]; constructor <;> omega)
      omega
    have hgr : Commute g t.prod := Commute.list_prod_right t g hr
    have h4 : g * t.prod * g⁻¹ = t.prod := by rw [hgr.eq]; group
    rw [hl, List.prod_cons, hc0] at hgy
    have h3 : g * x * g⁻¹ * t.prod = x * t.prod := by
      calc g * x * g⁻¹ * t.prod = g * x * g⁻¹ * (g * t.prod * g⁻¹) := by rw [h4]
        _ = g * (x * t.prod) * g⁻¹ := by group
        _ = x * t.prod := hgy
    exact mul_right_cancel h3

end CFSG.LocalAnalysis.RankFourTheoremC
