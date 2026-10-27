module

public import CFSG.GH74.GLS.C3.Layer2.FinModelFactsDataBase

public section

namespace CFSG.GH74.GLS.C3.Layer2.Model

open Equiv Perm CFSG.GH74.GLS.C3.Layer2

namespace Facts

theorem mem_sup_zpowers_iff_mul_self {G : Type*} [Group G] (R : Subgroup G) (a : G) (ha : a * a = 1)
    (hn : ∀ r ∈ R, a * r * a⁻¹ ∈ R) (g : G) :
    g ∈ R ⊔ Subgroup.zpowers a ↔ g ∈ R ∨ g * a ∈ R := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  let K : Subgroup G :=
    { carrier := {g | g ∈ R ∨ g * a ∈ R}
      one_mem' := Or.inl R.one_mem
      mul_mem' := by
        intro x y hx hy
        rcases hx with hx | hx <;> rcases hy with hy | hy
        · exact Or.inl (R.mul_mem hx hy)
        · right
          rw [mul_assoc]
          exact R.mul_mem hx hy
        · right
          have h1 := hn y hy
          have e : x * y * a = (x * a) * (a * y * a⁻¹) := by
            calc x * y * a = x * y * a⁻¹ := by rw [ha']
              _ = x * (a * a) * y * a⁻¹ := by rw [ha, mul_one]
              _ = (x * a) * (a * y * a⁻¹) := by group
          rw [e]
          exact R.mul_mem hx h1
        · left
          have h1 := hn (y * a) hy
          have e : x * y = (x * a) * (a * (y * a) * a⁻¹) := by
            calc x * y = x * (a * a) * y := by rw [ha, mul_one]
              _ = (x * a) * (a * (y * a) * a⁻¹) := by group
          rw [e]
          exact R.mul_mem hx h1
      inv_mem' := by
        intro x hx
        rcases hx with hx | hx
        · exact Or.inl (R.inv_mem hx)
        · right
          have h1 := hn _ (R.inv_mem hx)
          have e : x⁻¹ * a = a * (x * a)⁻¹ * a⁻¹ := by
            calc x⁻¹ * a = x⁻¹ * a⁻¹ := by rw [ha']
              _ = a * (x * a)⁻¹ * a⁻¹ := by group
          rw [e]
          exact h1 }
  have hK : R ⊔ Subgroup.zpowers a = K := by
    apply le_antisymm
    · apply sup_le
      · intro r hr
        exact Or.inl hr
      · rw [Subgroup.zpowers_le]
        exact Or.inr (by rw [ha]; exact R.one_mem)
    · intro g hg
      rcases hg with hg | hg
      · exact Subgroup.mem_sup_left hg
      · have h1 : g * a ∈ R ⊔ Subgroup.zpowers a := Subgroup.mem_sup_left hg
        have h2 : a⁻¹ ∈ R ⊔ Subgroup.zpowers a :=
          Subgroup.mem_sup_right (inv_mem (Subgroup.mem_zpowers a))
        have := mul_mem h1 h2
        simpa using this
  rw [hK]
  exact Iff.rfl

theorem natCard_subgroup_eq_length {m : ℕ} (H : Subgroup (alternatingGroup (Fin m)))
    (L : List (Perm (Fin m))) (hL : L.Nodup)
    (hmem : ∀ z : alternatingGroup (Fin m), z ∈ H ↔ (z : Perm (Fin m)) ∈ L)
    (hlift : ∀ p ∈ L, ∃ z : alternatingGroup (Fin m), (z : Perm (Fin m)) = p) :
    Nat.card H = L.length := by
  classical
  have h1 : Nat.card H = Nat.card (L.toFinset) := by
    refine Nat.card_congr (Equiv.ofBijective
      (fun z => ⟨(z.1 : Perm (Fin m)), by simpa using (hmem z.1).1 z.2⟩) ⟨?_, ?_⟩)
    · intro z w h
      have h' := congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext h')
    · rintro ⟨p, hp⟩
      obtain ⟨z, hz⟩ := hlift p (by simpa using hp)
      exact ⟨⟨z, (hmem z).2 (by rw [hz]; simpa using hp)⟩, Subtype.ext hz⟩
  rw [h1, Nat.card_eq_fintype_card, Fintype.card_coe, List.toFinset_card_of_nodup hL]

theorem etaB_sound {m : ℕ} {K : Type*} [Group K] (φ ψ : K →* Perm (Fin m))
    (hφ : Function.Injective φ) (hψ : Function.Injective ψ)
    (rl cl : List (Perm (Fin m))) (g : Fin 3 → Perm (Fin m)) (y0 : Perm (Fin m))
    (wd : Perm (Fin m) → List (Fin 3)) (ex : Perm (Fin m) → ℕ)
    (hnd : cl.Nodup) (hw : wordsB g cl wd = true) (h : etaB rl cl g y0 wd ex = true)
    (hCl : ∀ x, φ x ∈ cl) (hCl' : ∀ p ∈ cl, ∃ x, φ x = p) (hRl : ∀ x, ψ x ∈ rl)
    (hg : ∀ i, ∃ c, φ c = g i) (h0 : ∀ c, φ c = g 0 → ψ c = y0)
    (hH : ∀ x : K, orderOf x = 2 → numMoved (ψ x) = ex (φ x)) : False := by
  classical
  choose c hc using hg
  have hgc : (⇑φ ∘ c) = g := funext hc
  have key : ∀ x : K, evalWord (fun i => ψ (c i)) (wd (φ x)) = ψ x := by
    intro x
    have h1 : evalWord g (wd (φ x)) = φ x := by
      have := List.all_eq_true.1 hw (φ x) (hCl x)
      simpa using this
    rw [evalWord_eq] at h1
    have h2 : φ (((wd (φ x)).map c).prod) = φ x := by
      rw [map_list_prod, List.map_map, hgc]
      exact h1
    have h3 : ((wd (φ x)).map c).prod = x := hφ h2
    rw [evalWord_eq]
    calc ((wd (φ x)).map (fun i => ψ (c i))).prod
        = ψ (((wd (φ x)).map c).prod) := by
          rw [map_list_prod, List.map_map]; rfl
      _ = ψ x := by rw [h3]
  have hy0 : ψ (c 0) = y0 := h0 _ (hc 0)
  have hyy : (fun i => ψ (c i)) = ![y0, ψ (c 1), ψ (c 2)] := by
    funext i
    fin_cases i <;> simp [hy0]
  have hA : homB (stepsOf wd cl g) (fun i => ψ (c i)) = true := by
    unfold homB stepsOf
    rw [List.all_eq_true]
    intro x hx
    simp only [List.mem_flatMap, List.mem_map, List.mem_finRange, true_and] at hx
    obtain ⟨p, hp, k, rfl⟩ := hx
    obtain ⟨a, rfl⟩ := hCl' p hp
    simp only [decide_eq_true_eq]
    rw [← hc k, flatPerm_eq, ← map_mul, key, key, map_mul]
  have hB : injB cl wd (fun i => ψ (c i)) = true := by
    unfold injB
    apply decide_eq_true
    apply List.Nodup.map_on _ hnd
    intro p hp q hq hpq
    obtain ⟨a, rfl⟩ := hCl' p hp
    obtain ⟨b, rfl⟩ := hCl' q hq
    rw [key, key] at hpq
    rw [hψ hpq]
  have hC : valB (invsOf wd ex cl) (fun i => ψ (c i)) = true := by
    unfold valB invsOf
    rw [List.all_eq_true]
    intro x hx
    simp only [List.mem_map, List.mem_filter, decide_eq_true_eq] at hx
    obtain ⟨p, ⟨hp, hp1, hp2⟩, rfl⟩ := hx
    obtain ⟨a, rfl⟩ := hCl' p hp
    simp only [decide_eq_true_eq]
    rw [key]
    apply hH
    have h1 : a * a = 1 := hφ (by rw [map_mul, map_one]; exact hp1)
    have h2 : a ≠ 1 := fun h => hp2 (by rw [h, map_one])
    exact orderOf_eq_prime (by rw [sq]; exact h1) h2
  unfold etaB at h
  dsimp only at h
  have h1 := List.all_eq_true.1 h (ψ (c 1)) (hRl _)
  have h2 := List.all_eq_true.1 h1 (ψ (c 2)) (hRl _)
  rw [← hyy] at h2
  simp [hA, hB, hC] at h2

end Facts

end CFSG.GH74.GLS.C3.Layer2.Model
