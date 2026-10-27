module

public import CFSG.GH74.GLS.SP.GlueDefs
public import CFSG.GH74.GLS.SP.SpRoots

public section

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage4.Hex

section ChainProdFun

variable {X : Type*} [Group X]

theorem exists_fun_of_mem_chainProd (A : ℤ → Subgroup X) :
    ∀ (l : List ℤ), l.Nodup → ∀ x ∈ chainProd A l,
      ∃ f : ℤ → X, (∀ k ∈ l, f k ∈ A k) ∧ x = (l.map f).prod
  | [], _, x, hx => ⟨fun _ => 1, by simp, by simpa [chainProd] using hx⟩
  | k :: l, hnd, x, hx => by
    rw [chainProd_cons, Set.mem_mul] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    have hk : k ∉ l := (List.nodup_cons.1 hnd).1
    obtain ⟨f, hf, rfl⟩ := exists_fun_of_mem_chainProd A l (List.nodup_cons.1 hnd).2 b hb
    refine ⟨Function.update f k a, ?_, ?_⟩
    · intro j hj
      rcases List.mem_cons.1 hj with rfl | hj'
      · simpa using ha
      · have hjk : j ≠ k := fun h => hk (h ▸ hj')
        simpa [Function.update_of_ne hjk] using hf j hj'
    · simp only [List.map_cons, List.prod_cons, Function.update_self]
      congr 1
      congr 1
      apply List.map_congr_left
      intro j hj
      have hjk : j ≠ k := fun h => hk (h ▸ hj)
      simp [Function.update_of_ne hjk]

theorem prod_pad {n : ℕ} {i j : ℤ} (hi : 1 ≤ i) (hij : i ≤ j) (hj : j ≤ n) (f : ℤ → X) :
    ((intList 1 n).map (fun k => if i ≤ k ∧ k ≤ j then f k else 1)).prod =
      ((intList i j).map f).prod := by
  have h1 : intList 1 n = intList 1 (i - 1) ++ (intList i j ++ intList (j + 1) n) := by
    have e1 := intList_append (a := 1) (b := i - 1) (c := n) (by omega) (by omega)
    have e2 := intList_append (a := i) (b := j) (c := n) (by omega) hj
    rw [show i - 1 + 1 = i by omega, ← e2] at e1
    exact e1.symm
  rw [h1, List.map_append, List.map_append, List.prod_append, List.prod_append]
  have hA : ((intList 1 (i - 1)).map (fun k => if i ≤ k ∧ k ≤ j then f k else (1 : X))).prod = 1 := by
    apply List.prod_eq_one
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
    have := mem_intList_iff.1 hk
    have hk' : ¬(i ≤ k ∧ k ≤ j) := by omega
    simp [hk']
  have hC : ((intList (j + 1) n).map (fun k => if i ≤ k ∧ k ≤ j then f k else (1 : X))).prod = 1 := by
    apply List.prod_eq_one
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
    have := mem_intList_iff.1 hk
    have hk' : ¬(i ≤ k ∧ k ≤ j) := by omega
    simp [hk']
  have hB : (intList i j).map (fun k => if i ≤ k ∧ k ≤ j then f k else (1 : X)) =
      (intList i j).map f := by
    apply List.map_congr_left
    intro k hk
    have := mem_intList_iff.1 hk
    simp [this]
  rw [hA, hC, hB, one_mul, mul_one]

end ChainProdFun

section Oct

variable {G : Type*} [Group G] {n : ℕ} {H : Subgroup G} {r₁ r₂ : G} {U : Subgroup G}
  {root : ℤ → Subgroup G}

theorem rgd2_comm_mem (R : RGD2 n H r₁ r₂ U root) {a b : ℤ} (ha : 1 ≤ a) (hab : a < b) (hb : b ≤ n)
    {x y : G} (hx : x ∈ root a) (hy : y ∈ root b) :
    ⁅x, y⁆ ∈ chainProd root (intList (a + 1) (b - 1)) := by
  obtain ⟨V₁, hV₁c, -, hV₁l, -⟩ := R.subgroup (a + 1) b (by omega) (by omega) hb
  obtain ⟨V₂, hV₂c, -, -, hV₂r⟩ := R.subgroup a (b - 1) ha (by omega) (by omega)
  have hyV₁ : y ∈ V₁ := by
    have : y ∈ (V₁ : Set G) := by
      rw [hV₁c]
      exact mem_chainProd_of_mem root (k := b) (mem_intList_iff.2 ⟨by omega, le_rfl⟩) hy
    exact this
  have hxV₂ : x ∈ V₂ := by
    have : x ∈ (V₂ : Set G) := by
      rw [hV₂c]
      exact mem_chainProd_of_mem root (k := a) (mem_intList_iff.2 ⟨le_rfl, by omega⟩) hx
    exact this
  have hz₁ : ⁅x, y⁆ ∈ V₁ := by
    have hx' : x ∈ root (a + 1 - 1) := by simpa using hx
    have := hV₁l (by omega) x hx' y hyV₁
    have e : ⁅x, y⁆ = (x * y * x⁻¹) * y⁻¹ := by simp only [commutatorElement_def]
    rw [e]
    exact V₁.mul_mem this (V₁.inv_mem hyV₁)
  have hz₂ : ⁅x, y⁆ ∈ V₂ := by
    have hy' : y ∈ root (b - 1 + 1) := by simpa using hy
    have := hV₂r (by omega) y hy' x⁻¹ (V₂.inv_mem hxV₂)
    have e : ⁅x, y⁆ = x * (y * x⁻¹ * y⁻¹) := by simp only [commutatorElement_def]; group
    rw [e]
    exact V₂.mul_mem hxV₂ this
  have hz₁' : ⁅x, y⁆ ∈ chainProd root (intList (a + 1) b) := by
    have : ⁅x, y⁆ ∈ (V₁ : Set G) := hz₁
    rwa [hV₁c] at this
  have hz₂' : ⁅x, y⁆ ∈ chainProd root (intList a (b - 1)) := by
    have : ⁅x, y⁆ ∈ (V₂ : Set G) := hz₂
    rwa [hV₂c] at this
  obtain ⟨f₁, hf₁, he₁⟩ := exists_fun_of_mem_chainProd root _ (nodup_intList _ _) _ hz₁'
  obtain ⟨f₂, hf₂, he₂⟩ := exists_fun_of_mem_chainProd root _ (nodup_intList _ _) _ hz₂'
  have key := R.unique (fun k => if a + 1 ≤ k ∧ k ≤ b then f₁ k else 1)
    (fun k => if a ≤ k ∧ k ≤ b - 1 then f₂ k else 1)
    (fun k hk => by
      split_ifs with h
      · exact hf₁ k (mem_intList_iff.2 h)
      · exact (root k).one_mem)
    (fun k hk => by
      split_ifs with h
      · exact hf₂ k (mem_intList_iff.2 h)
      · exact (root k).one_mem)
    (by
      rw [prod_pad (n := n) (by omega) (by omega) hb f₁, prod_pad (n := n) ha (by omega) (by omega) f₂,
        ← he₁, ← he₂]) b (mem_intList_iff.2 ⟨by omega, hb⟩)
  have hfb : f₁ b = 1 := by
    have h1 : a + 1 ≤ b ∧ b ≤ b := ⟨by omega, le_rfl⟩
    have h2 : ¬(a ≤ b ∧ b ≤ b - 1) := by omega
    simpa [h1, h2] using key
  have hsnoc : intList (a + 1) b = intList (a + 1) (b - 1) ++ [b] := intList_snoc (by omega)
  rw [he₁, hsnoc, List.map_append, List.prod_append]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, hfb]
  exact list_prod_mem_chainProd root f₁ _ (fun k hk => hf₁ k (by
    have := mem_intList_iff.1 hk
    exact mem_intList_iff.2 ⟨this.1, by omega⟩))

theorem rgd2_octComm (R : RGD2 n H r₁ r₂ U root) : OctComm root n := by
  intro a b ha hab hb x hx y hy
  have h := rgd2_comm_mem R ha hab hb hx hy
  refine (chainProd_subset_iSup root _ h : _ ∈ ((⨆ k ∈ intList (a + 1) (b - 1), root k :
    Subgroup G) : Set G)) |> fun h' => ?_
  refine (iSup₂_le (fun k hk => ?_) : (⨆ k ∈ intList (a + 1) (b - 1), root k) ≤
    ⨆ c ∈ Set.Ioo a b, root c) h'
  have := mem_intList_iff.1 hk
  exact le_iSup₂_of_le (f := fun c (_ : c ∈ Set.Ioo a b) => root c) k
    (Set.mem_Ioo.2 ⟨by omega, by omega⟩) le_rfl

end Oct

end CFSG.GH74.GLS.Stage4.Hex
