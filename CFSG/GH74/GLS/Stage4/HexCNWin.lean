module

public import CFSG.GH74.GLS.Stage4.HexCSub

public section

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage4.Hex

variable {G : Type} [Group G] {H : Subgroup G} {r₁ r₂ : G} {U : Subgroup G}
  {root : ℤ → Subgroup G}

theorem rgd2_pad_unique (R : RGD2 6 H r₁ r₂ U root) {i j i' j' : ℤ} (hi : 1 ≤ i) (hij : i ≤ j)
    (hj : j ≤ 6) (hi' : 1 ≤ i') (hij' : i' ≤ j') (hj' : j' ≤ 6) {f g : ℤ → G}
    (hf : ∀ k ∈ intList i j, f k ∈ root k) (hg : ∀ k ∈ intList i' j', g k ∈ root k)
    (h : ((intList i j).map f).prod = ((intList i' j').map g).prod) {k : ℤ} (hk1 : 1 ≤ k)
    (hk6 : k ≤ 6) :
    (if i ≤ k ∧ k ≤ j then f k else 1) = (if i' ≤ k ∧ k ≤ j' then g k else 1) := by
  refine R.unique (fun k => if i ≤ k ∧ k ≤ j then f k else 1)
    (fun k => if i' ≤ k ∧ k ≤ j' then g k else 1)
    (fun k hk => ?_) (fun k hk => ?_) ?_ k (mem_intList_iff.2 ⟨hk1, by exact_mod_cast hk6⟩)
  · split_ifs with h'
    · exact hf k (mem_intList_iff.2 h')
    · exact (root k).one_mem
  · split_ifs with h'
    · exact hg k (mem_intList_iff.2 h')
    · exact (root k).one_mem
  · rw [prod_pad (n := 6) hi hij (by exact_mod_cast hj) f,
      prod_pad (n := 6) hi' hij' (by exact_mod_cast hj') g]
    exact h

theorem exists_fun_of_mem_Vsub (R : RGD2 6 H r₁ r₂ U root) {i j : ℤ} (hi : 1 ≤ i) (hj : j ≤ 6)
    {z : G} (hz : z ∈ Vsub root i j) :
    ∃ f : ℤ → G, (∀ k ∈ intList i j, f k ∈ root k) ∧ z = ((intList i j).map f).prod := by
  have h : z ∈ chainProd root (intList i j) := by
    have : z ∈ ((Vsub root i j : Subgroup G) : Set G) := hz
    rwa [Vsub_carrier R hi hj] at this
  exact exists_fun_of_mem_chainProd root _ (nodup_intList _ _) _ h

theorem prod_mem_Vsub (R : RGD2 6 H r₁ r₂ U root) {i j : ℤ} (hi : 1 ≤ i) (hj : j ≤ 6) {f : ℤ → G}
    (hf : ∀ k ∈ intList i j, f k ∈ root k) : ((intList i j).map f).prod ∈ Vsub root i j := by
  have h := list_prod_mem_chainProd root f (intList i j) hf
  have : ((intList i j).map f).prod ∈ ((Vsub root i j : Subgroup G) : Set G) := by
    rw [Vsub_carrier R hi hj]; exact h
  exact this

theorem eq_one_of_mem_Vsub_Vsub (R : RGD2 6 H r₁ r₂ U root) {i j i' j' : ℤ} (hi : 1 ≤ i)
    (hij : i ≤ j) (hj : j ≤ 6) (hi' : 1 ≤ i') (hij' : i' ≤ j') (hj' : j' ≤ 6) (hjl : j < i')
    {z : G} (h1 : z ∈ Vsub root i j) (h2 : z ∈ Vsub root i' j') : z = 1 := by
  obtain ⟨f, hf, rfl⟩ := exists_fun_of_mem_Vsub R hi hj h1
  obtain ⟨g, hg, hz⟩ := exists_fun_of_mem_Vsub R hi' hj' h2
  apply List.prod_eq_one
  intro y hy
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hy
  have hk' := mem_intList_iff.1 hk
  have := rgd2_pad_unique R hi hij hj hi' hij' hj' hf hg hz (k := k) (by omega) (by omega)
  have h' : ¬ (i' ≤ k ∧ k ≤ j') := by omega
  simpa [hk', h'] using this

theorem eq_one_of_mem_root2_Vsub36 (R : RGD2 6 H r₁ r₂ U root) {x : G} (hx : x ∈ root 2)
    (h : x ∈ Vsub root 3 6) : x = 1 :=
  eq_one_of_mem_Vsub_Vsub R (i := 2) (j := 2) (i' := 3) (j' := 6) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (root_le_Vsub (by norm_num) (by norm_num) hx) h

theorem eq_one_of_mem_Vsub23_Vsub56 (R : RGD2 6 H r₁ r₂ U root) {z : G} (h1 : z ∈ Vsub root 2 3)
    (h2 : z ∈ Vsub root 5 6) : z = 1 :=
  eq_one_of_mem_Vsub_Vsub R (i := 2) (j := 3) (i' := 5) (j' := 6) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2

theorem mem_Vsub34_of_mem_Vsub24_Vsub36 (R : RGD2 6 H r₁ r₂ U root) {z : G}
    (h1 : z ∈ Vsub root 2 4) (h2 : z ∈ Vsub root 3 6) : z ∈ Vsub root 3 4 := by
  obtain ⟨f, hf, rfl⟩ := exists_fun_of_mem_Vsub R (by norm_num) (by norm_num) h1
  obtain ⟨g, hg, hz⟩ := exists_fun_of_mem_Vsub R (by norm_num) (by norm_num) h2
  have key := rgd2_pad_unique R (i := 2) (j := 4) (i' := 3) (j' := 6) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hf hg hz (k := 2) (by norm_num)
    (by norm_num)
  have hf2 : f 2 = 1 := by simpa using key
  have hl : intList 2 4 = 2 :: intList 3 4 := intList_cons (by norm_num)
  rw [hl, List.map_cons, List.prod_cons, hf2, one_mul]
  exact prod_mem_Vsub R (by norm_num) (by norm_num) (fun k hk => hf k (by
    rw [hl]; exact List.mem_cons_of_mem _ hk))

theorem exists_mul_of_mem_Vsub25 (R : RGD2 6 H r₁ r₂ U root) {z : G} (h : z ∈ Vsub root 2 5) :
    ∃ y ∈ root 2, ∃ v ∈ Vsub root 3 5, z = y * v := by
  obtain ⟨f, hf, rfl⟩ := exists_fun_of_mem_Vsub R (by norm_num) (by norm_num) h
  have hl : intList 2 5 = 2 :: intList 3 5 := intList_cons (by norm_num)
  refine ⟨f 2, hf 2 (by rw [hl]; exact List.mem_cons_self), ((intList 3 5).map f).prod,
    prod_mem_Vsub R (by norm_num) (by norm_num) (fun k hk => hf k (by
      rw [hl]; exact List.mem_cons_of_mem _ hk)), ?_⟩
  rw [hl, List.map_cons, List.prod_cons]

theorem exists_comp2 (R : RGD2 6 H r₁ r₂ U root) :
    ∃ c : G → G, ∀ z ∈ Vsub root 2 5, c z ∈ root 2 ∧ (c z)⁻¹ * z ∈ Vsub root 3 5 := by
  classical
  have h : ∀ z ∈ Vsub root 2 5, ∃ y : G, y ∈ root 2 ∧ y⁻¹ * z ∈ Vsub root 3 5 := by
    intro z hz
    obtain ⟨y, hy, v, hv, rfl⟩ := exists_mul_of_mem_Vsub25 R hz
    exact ⟨y, hy, by simpa using hv⟩
  choose! c hc using h
  exact ⟨c, hc⟩

end CFSG.GH74.GLS.Stage4.Hex
