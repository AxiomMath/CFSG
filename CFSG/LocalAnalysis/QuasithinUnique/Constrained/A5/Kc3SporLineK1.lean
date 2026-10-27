module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicBase

public section

namespace CFSG.QuasithinUnique.A5.Kc3SporLine

open CFSG.QuasithinUnique.K1.SporadicPerm

section SGens

variable {Γ : Type} [Group Γ] {n : ℕ} [MulAction Γ (Fin n)]

theorem sGens_of_baseCertS' [Finite Γ] (B : List ℕ) (hB : ∀ b ∈ B, b < n)
    (hbase : ∀ g : Γ, (∀ b ∈ B, act n g b = b) → g = 1) (a b : Γ) (prog : List (ℕ × ℕ))
    (hv : slpValidAux prog 2 = true) (qp : List (ℕ × ℕ)) (zn gn gin hn hin : ℕ)
    (Ts : Array (List ℕ)) (par cl : Array ℕ) (k : ℕ)
    (hcert : BaseCertS n B (slpTabsA (tab n a).toArray (tab n b).toArray prog) qp zn gn gin hn hin
      Ts par cl k) :
    genTabs n (qp.map fun p => (slpElts a b prog).getD p.1 1) =
      qp.map (fun p => (slpTabsA (tab n a).toArray (tab n b).toArray prog)[p.1]!) ∧
    Nat.card (Subgroup.closure {x | x ∈ qp.map fun p => (slpElts a b prog).getD p.1 1}) =
      2 ^ k := by
  obtain ⟨hqp, hz, hg, hgi, hh, hhi, hc⟩ := hcert
  obtain ⟨hinvq, -, -, hEnum, hsize, -⟩ := hc
  set T := slpTabsA (tab n a).toArray (tab n b).toArray prog with hT
  have hinv := slp_foldl_inv (n := n) prog #[a, b] #[(tab n a).toArray, (tab n b).toArray]
    (by simp) (by
      intro i hi
      have hi' : i < 2 := by simpa using hi
      interval_cases i <;> simp) hv
  have hE : ∀ i < T.size, tab n ((slpElts a b prog).getD i 1) = (T[i]!).toList := hinv.2
  have hE' : ∀ i < T.size, (tab n ((slpElts a b prog).getD i 1)).toArray = T[i]! := by
    intro i hi
    rw [hE i hi, Array.toArray_toList]
  have hsg : genTabs n (qp.map fun p => (slpElts a b prog).getD p.1 1) =
      qp.map (fun p => T[p.1]!) := by
    simp only [genTabs, List.map_map]
    apply List.map_congr_left
    intro p hp
    exact hE' p.1 (hqp p hp).1
  have hinv_of : ∀ x y : Γ,
      (∀ q < n, img (tab n y).toArray (img (tab n x).toArray q) = q) → y = x⁻¹ := by
    intro x y hxy
    apply eq_inv_of_mul_eq_one_left
    apply hbase
    intro b hb
    rw [act_mul _ _ (hB b hb)]
    have := hxy b (hB b hb)
    simpa only [img_tab] using this
  have hsgi : genTabsInv n (qp.map fun p => (slpElts a b prog).getD p.1 1) =
      qp.map (fun p => T[p.2]!) := by
    simp only [genTabsInv, List.map_map]
    apply List.map_congr_left
    intro p hp
    have h1 := hE' p.1 (hqp p hp).1
    have h2 := hE' p.2 (hqp p hp).2
    have h3 : (slpElts a b prog).getD p.2 1 = ((slpElts a b prog).getD p.1 1)⁻¹ := by
      apply hinv_of
      intro q hq
      have := hinvq (T[p.1]!, T[p.2]!) (List.mem_map.mpr ⟨p, hp, rfl⟩) q hq
      simpa only [← h1, ← h2] using this
    simp only [Function.comp_apply]
    rw [← h2, h3]
  refine ⟨hsg, ?_⟩
  have hEnum' : BaseEnumOK n B (genTabs n (qp.map fun p => (slpElts a b prog).getD p.1 1))
      (genTabsInv n (qp.map fun p => (slpElts a b prog).getD p.1 1)) Ts par cl := by
    rw [hsg, hsgi]
    simpa only [List.map_map, Function.comp_def] using hEnum
  rw [benum_card hB hbase _ Ts par cl hEnum', hsize]

end SGens

end CFSG.QuasithinUnique.A5.Kc3SporLine
