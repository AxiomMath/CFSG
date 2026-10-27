module

public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

open Subgroup

theorem splCert_gen_mem {G : Type*} [Group G] (K : Subgroup G) (h1 h2 : G) (hK1 : h1 ∈ K)
    (hK2 : h2 ∈ K) (j : Bool) : (if j then h2 else h1) ∈ K := by
  cases j <;> simp [hK1, hK2]

theorem splCert_mem {G : Type*} [Group G] (h1 h2 : G) (n : ℕ) (s : ℕ → G) (hs0 : s 0 = 1)
    (par : ℕ → ℕ) (gen : ℕ → Bool)
    (hpar : ∀ k, 0 < k → k < n → par k < k ∧ s k = s (par k) * (if gen k then h2 else h1)) :
    ∀ k < n, s k ∈ Subgroup.closure ({h1, h2} : Set G) := by
  have hK1 : h1 ∈ Subgroup.closure ({h1, h2} : Set G) := Subgroup.subset_closure (by simp)
  have hK2 : h2 ∈ Subgroup.closure ({h1, h2} : Set G) := Subgroup.subset_closure (by simp)
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · rw [h0, hs0]
      exact one_mem _
    · obtain ⟨hlt, heq⟩ := hpar k hpos hk
      rw [heq]
      exact mul_mem (ih (par k) hlt (by omega)) (splCert_gen_mem _ h1 h2 hK1 hK2 (gen k))

theorem splCert_pow {G : Type*} [Group G] (g : G) (n : ℕ) (s : ℕ → G) (suc : ℕ → ℕ)
    (hsuc : ∀ k < n, suc k < n ∧ s k * g = s (suc k)) :
    ∀ m : ℕ, ∀ k < n, ∃ k' < n, s k' = s k * g ^ m := by
  intro m
  induction m with
  | zero =>
    intro k hk
    exact ⟨k, hk, by rw [pow_zero, mul_one]⟩
  | succ m ih =>
    intro k hk
    obtain ⟨k', hk', he⟩ := ih k hk
    refine ⟨suc k', (hsuc k' hk').1, ?_⟩
    rw [pow_succ, ← mul_assoc, ← he, (hsuc k' hk').2]

theorem splCert_inv_eq_pow {G : Type*} [Group G] (g : G) (o : ℕ) (ho : 0 < o) (hg : g ^ o = 1) :
    g⁻¹ = g ^ (o - 1) := by
  have h : o - 1 + 1 = o := by omega
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_succ', h, hg]

theorem splCert_cover {G : Type*} [Group G] (h1 h2 : G) (n : ℕ) (s : ℕ → G) (hn : 0 < n)
    (hs0 : s 0 = 1) (o1 o2 : ℕ) (ho1 : 0 < o1) (ho2 : 0 < o2) (hh1 : h1 ^ o1 = 1)
    (hh2 : h2 ^ o2 = 1) (suc1 suc2 : ℕ → ℕ)
    (hsuc : ∀ k < n, suc1 k < n ∧ suc2 k < n ∧ s k * h1 = s (suc1 k) ∧ s k * h2 = s (suc2 k)) :
    ∀ x ∈ Subgroup.closure ({h1, h2} : Set G), ∃ k < n, s k = x := by
  have hR1 := splCert_pow h1 n s suc1 (fun k hk => ⟨(hsuc k hk).1, (hsuc k hk).2.2.1⟩)
  have hR2 := splCert_pow h2 n s suc2 (fun k hk => ⟨(hsuc k hk).2.1, (hsuc k hk).2.2.2⟩)
  have hI1 : h1⁻¹ = h1 ^ (o1 - 1) := splCert_inv_eq_pow h1 o1 ho1 hh1
  have hI2 : h2⁻¹ = h2 ^ (o2 - 1) := splCert_inv_eq_pow h2 o2 ho2 hh2
  intro x hx
  induction hx using Subgroup.closure_induction_right with
  | one => exact ⟨0, hn, hs0⟩
  | mul_right x _ y hy ih =>
    obtain ⟨k, hk, rfl⟩ := ih
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with hy | hy
    · rw [hy]
      exact ⟨suc1 k, (hsuc k hk).1, (hsuc k hk).2.2.1.symm⟩
    · rw [hy]
      exact ⟨suc2 k, (hsuc k hk).2.1, (hsuc k hk).2.2.2.symm⟩
  | mul_inv_cancel x _ y hy ih =>
    obtain ⟨k, hk, rfl⟩ := ih
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with hy | hy
    · rw [hy, hI1]
      exact hR1 (o1 - 1) k hk
    · rw [hy, hI2]
      exact hR2 (o2 - 1) k hk

theorem splCert_cls_of_snd (c : Option (ℕ × ℕ)) (i : ℕ) (h : c.map Prod.snd = some i) :
    ∃ u, c = some (u, i) := by
  cases c with
  | none => simp at h
  | some p =>
    obtain ⟨u, j⟩ := p
    simp at h
    subst h
    exact ⟨u, rfl⟩

theorem splCert_coe_prod {G : Type*} [Group G] (K : Subgroup G) (n : ℕ) (s : ℕ → G)
    (t : ℕ → K) (ht : ∀ k (hk : k < n), (t k : G) = s k) (L : List ℕ) :
    (∀ l ∈ L, l < n) → (((L.map t).prod : K) : G) = (L.map s).prod := by
  induction L with
  | nil =>
    intro _
    simp
  | cons a L ih =>
    intro hL
    simp only [List.map_cons, List.prod_cons, Subgroup.coe_mul]
    rw [ih (fun l hl => hL l (List.mem_cons_of_mem _ hl)), ht a (hL a (by simp))]

theorem splCert_normal_top {G : Type*} [Group G] (K : Subgroup G) (h1 h2 : G)
    (hK1 : h1 ∈ K) (hK2 : h2 ∈ K) (n : ℕ) (s : ℕ → G) (hs0 : s 0 = 1)
    (par : ℕ → ℕ) (gen : ℕ → Bool)
    (hpar : ∀ k, 0 < k → k < n → par k < k ∧ s k = s (par k) * (if gen k then h2 else h1))
    (hmem : ∀ k < n, s k ∈ K) (hcover : ∀ x ∈ K, ∃ k < n, s k = x)
    (r : ℕ) (rep : ℕ → ℕ) (hrep : ∀ i < r, rep i < n)
    (cls : ℕ → Option (ℕ × ℕ))
    (hcls : ∀ k < n, match cls k with
        | none => s k = 1
        | some (u, i) => u < n ∧ i < r ∧ s k * s u = s u * s (rep i))
    (nc : ℕ → Bool → List ℕ)
    (hnc : ∀ i < r, ∀ j : Bool, (∀ l ∈ nc i j, l < n ∧ (cls l).map Prod.snd = some i) ∧
        ((nc i j).map s).prod = (if j then h2 else h1))
    (M : Subgroup K) (hM : M.Normal) (hbot : M ≠ ⊥) : M = ⊤ := by
  obtain ⟨t, ht⟩ : ∃ t : ℕ → K, ∀ k (hk : k < n), (t k : G) = s k :=
    ⟨fun k => if hk : k < n then ⟨s k, hmem k hk⟩ else 1, fun k hk => by simp [hk]⟩
  obtain ⟨g, hg⟩ : ∃ g : Bool → K, ∀ j, (g j : G) = if j then h2 else h1 :=
    ⟨fun j => ⟨if j then h2 else h1, splCert_gen_mem K h1 h2 hK1 hK2 j⟩, fun j => rfl⟩
  obtain ⟨x, hxM, hx1⟩ : ∃ x ∈ M, x ≠ 1 := by
    by_contra hcon
    exact hbot ((Subgroup.eq_bot_iff_forall M).2 fun x hx => by
      by_contra hx1
      exact hcon ⟨x, hx, hx1⟩)
  obtain ⟨k, hk, hkx⟩ := hcover (x : G) x.2
  have htk : t k ∈ M := by
    have e : t k = x := Subtype.ext ((ht k hk).trans hkx)
    rw [e]
    exact hxM
  obtain ⟨u, i, hu, hi, hkey⟩ : ∃ u i, u < n ∧ i < r ∧ s k * s u = s u * s (rep i) := by
    have hck := hcls k hk
    rcases hc : cls k with _ | ⟨u, i⟩
    · simp only [hc] at hck
      exact (hx1 (Subtype.ext (by simp [← hkx, hck]))).elim
    · simp only [hc] at hck
      exact ⟨u, i, hck.1, hck.2.1, hck.2.2⟩
  have hr : rep i < n := hrep i hi
  have htr : t (rep i) ∈ M := by
    have h := hM.conj_mem (t k) htk (t u)⁻¹
    have e : (t u)⁻¹ * t k * (t u)⁻¹⁻¹ = t (rep i) := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv, ht k hk, ht u hu, ht (rep i) hr]
      rw [mul_assoc, hkey, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [e] at h
    exact h
  have up : ∀ l < n, ∀ u' < n, s l * s u' = s u' * s (rep i) → t l ∈ M := by
    intro l hl u' hu' hk'
    have h := hM.conj_mem (t (rep i)) htr (t u')
    have e : t u' * t (rep i) * (t u')⁻¹ = t l := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, ht l hl, ht u' hu', ht (rep i) hr]
      rw [← hk', mul_inv_cancel_right]
    rw [e] at h
    exact h
  have hgM : ∀ j : Bool, g j ∈ M := by
    intro j
    have hL : ∀ l ∈ nc i j, t l ∈ M := by
      intro l hl
      obtain ⟨hln, hlc⟩ := (hnc i hi j).1 l hl
      obtain ⟨u', hu'⟩ := splCert_cls_of_snd (cls l) i hlc
      have hck' := hcls l hln
      simp only [hu'] at hck'
      exact up l hln u' hck'.1 hck'.2.2
    have hprod : ((nc i j).map t).prod ∈ M :=
      Subgroup.list_prod_mem M (fun x hx => by
        obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hx
        exact hL l hl)
    have heq : ((nc i j).map t).prod = g j := by
      apply Subtype.ext
      rw [splCert_coe_prod K n s t ht (nc i j) (fun l hl => ((hnc i hi j).1 l hl).1), hg j]
      exact (hnc i hi j).2
    rw [← heq]
    exact hprod
  have hall : ∀ k, k < n → t k ∈ M := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      rcases Nat.eq_zero_or_pos k with h0 | hpos
      · subst h0
        have e : t 0 = 1 := Subtype.ext (by simp [ht 0 hk, hs0])
        rw [e]
        exact one_mem M
      · obtain ⟨hlt, heq⟩ := hpar k hpos hk
        have e : t k = t (par k) * g (gen k) := by
          apply Subtype.ext
          rw [Subgroup.coe_mul, ht k hk, ht (par k) (by omega), hg (gen k), heq]
        rw [e]
        exact mul_mem (ih (par k) hlt (by omega)) (hgM (gen k))
  rw [Subgroup.eq_top_iff']
  intro y
  obtain ⟨k, hk, hky⟩ := hcover (y : G) y.2
  have e : y = t k := Subtype.ext (by rw [ht k hk, hky])
  rw [e]
  exact hall k hk

theorem splCert_simple {G : Type*} [Group G] (K : Subgroup G) (h1 h2 : G)
    (hK1 : h1 ∈ K) (hK2 : h2 ∈ K) (n : ℕ) (s : ℕ → G) (hs0 : s 0 = 1)
    (par : ℕ → ℕ) (gen : ℕ → Bool)
    (hpar : ∀ k, 0 < k → k < n → par k < k ∧ s k = s (par k) * (if gen k then h2 else h1))
    (hmem : ∀ k < n, s k ∈ K) (hcover : ∀ x ∈ K, ∃ k < n, s k = x)
    (r : ℕ) (rep : ℕ → ℕ) (hrep : ∀ i < r, rep i < n)
    (cls : ℕ → Option (ℕ × ℕ))
    (hcls : ∀ k < n, match cls k with
        | none => s k = 1
        | some (u, i) => u < n ∧ i < r ∧ s k * s u = s u * s (rep i))
    (nc : ℕ → Bool → List ℕ)
    (hnc : ∀ i < r, ∀ j : Bool, (∀ l ∈ nc i j, l < n ∧ (cls l).map Prod.snd = some i) ∧
        ((nc i j).map s).prod = (if j then h2 else h1))
    (hnab : h1 * h2 ≠ h2 * h1) : IsSimpleGroup K := by
  have hne : (⟨h1, hK1⟩ : K) ≠ 1 := by
    intro h
    apply hnab
    have h' : h1 = 1 := by simpa using congrArg Subtype.val h
    rw [h', one_mul, mul_one]
  haveI : Nontrivial K := nontrivial_of_ne (⟨h1, hK1⟩ : K) 1 hne
  refine ⟨?_⟩
  intro M hM
  by_cases hbot : M = ⊥
  · exact Or.inl hbot
  · exact Or.inr (splCert_normal_top K h1 h2 hK1 hK2 n s hs0 par gen hpar hmem hcover r rep
      hrep cls hcls nc hnc M hM hbot)

theorem splCert_not_comm {G : Type*} [Group G] (K : Subgroup G) (h1 h2 : G)
    (hK1 : h1 ∈ K) (hK2 : h2 ∈ K) (hnab : h1 * h2 ≠ h2 * h1) : ¬ IsMulCommutative ↥K := by
  intro hc
  apply hnab
  have h := (isMulCommutative_iff.mp hc) ⟨h1, hK1⟩ ⟨h2, hK2⟩
  simpa using congrArg Subtype.val h

theorem simpleGroup_of_cert {G : Type*} [Group G] (h1 h2 : G) (n : ℕ) (hn : 0 < n) (s : ℕ → G)
    (hs0 : s 0 = 1) (par : ℕ → ℕ) (gen : ℕ → Bool)
    (hpar : ∀ k, 0 < k → k < n → par k < k ∧ s k = s (par k) * (if gen k then h2 else h1))
    (o1 o2 : ℕ) (ho1 : 0 < o1) (ho2 : 0 < o2) (hh1 : h1 ^ o1 = 1) (hh2 : h2 ^ o2 = 1)
    (suc1 suc2 : ℕ → ℕ)
    (hsuc : ∀ k < n, suc1 k < n ∧ suc2 k < n ∧ s k * h1 = s (suc1 k) ∧ s k * h2 = s (suc2 k))
    (r : ℕ) (rep : ℕ → ℕ) (hrep : ∀ i < r, rep i < n)
    (cls : ℕ → Option (ℕ × ℕ))
    (hcls : ∀ k < n, match cls k with
        | none => s k = 1
        | some (u, i) => u < n ∧ i < r ∧ s k * s u = s u * s (rep i))
    (nc : ℕ → Bool → List ℕ)
    (hnc : ∀ i < r, ∀ j : Bool, (∀ l ∈ nc i j, l < n ∧ (cls l).map Prod.snd = some i) ∧
        ((nc i j).map s).prod = (if j then h2 else h1))
    (hnab : h1 * h2 ≠ h2 * h1) :
    IsSimpleGroup ↥(Subgroup.closure ({h1, h2} : Set G)) ∧
      ¬ IsMulCommutative ↥(Subgroup.closure ({h1, h2} : Set G)) ∧
      (∀ k < n, s k ∈ Subgroup.closure ({h1, h2} : Set G)) := by
  have hK1 : h1 ∈ Subgroup.closure ({h1, h2} : Set G) := Subgroup.subset_closure (by simp)
  have hK2 : h2 ∈ Subgroup.closure ({h1, h2} : Set G) := Subgroup.subset_closure (by simp)
  have hmem := splCert_mem h1 h2 n s hs0 par gen hpar
  have hcover := splCert_cover h1 h2 n s hn hs0 o1 o2 ho1 ho2 hh1 hh2 suc1 suc2 hsuc
  exact ⟨splCert_simple _ h1 h2 hK1 hK2 n s hs0 par gen hpar hmem hcover r rep hrep cls hcls nc
      hnc hnab,
    splCert_not_comm _ h1 h2 hK1 hK2 hnab, hmem⟩

theorem three_dvd_card_of_orderOf_three {G : Type*} [Group G] {H : Subgroup G} {g : G}
    (hg : g ∈ H) (h3 : orderOf g = 3) : 3 ∣ Nat.card H := by
  have h := orderOf_dvd_natCard (⟨g, hg⟩ : H)
  rwa [Subgroup.orderOf_mk, h3] at h

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

end
