module

public import CFSG.Certificates.Kernel.Ivk8NormPAb
public import CFSG.Certificates.Kernel.Ivk8NormPCSound

public section

namespace CFSG.KS.Ivk8NormP

open CFSG.Certificates.Kernel.PkEnum CFSG.KS.Ivk8Norm CFSG.KS.PK Subgroup

variable {n : ℕ}

@[expose] noncomputable def witsF (c : VP n) (xs : List (VP n)) : List (ℕ × ℕ) :=
  (subprodsV (xs.map (conjV (invV c)))).tail.map Subtype.val

theorem noP_of_chkPC (hn : n < 16777216) (hw : n + 1 < 2 ^ wd n)
    {G S₀ : Subgroup (Equiv.Perm (Fin n))} (hS₀G : S₀ ≤ G) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {xs : List (VP n)} (hxsF : (xs.all invoV && xs.all fun x => xs.all (commV x)) = true)
    (hxsS : ∀ x ∈ xs, pkp x ∈ S₀) {a b' : VP n} (ha : a ∈ xs) (hb : b' ∈ xs)
    (hkl : kleinOK a b' = true) {c₁ c₂ : VP n} (hc₁ : pkp c₁ ∈ G) (hc₂ : pkp c₂ ∈ G)
    (hconj : (!difV (conjV c₁ a) b' && !difV (conjV c₂ a) (mulV a b')) = true)
    {L : List (VP n)} (hL : ∀ y ∈ G, ∃ y' ∈ L, pkp y' = y) {ps : List ℕ}
    (hps : ∀ y ∈ G, orderOf y = p → p ∈ ps)
    (hchk : chkPC n (wd n) a.1.1 ps [witsF (oneV n) xs, witsF c₁ xs, witsF c₂ xs]
      (L.map fun y => y.1.1) = true)
    {k : ℕ} (hS₀ : ¬ 2 ^ (k + 1) ∣ Nat.card S₀) :
    ∀ P W : Subgroup (Equiv.Perm (Fin n)), P ≤ S₀ → W ≤ G → Nat.card P = 2 ^ k →
      IsPGroup p W → P ≤ normalizer (W : Set (Equiv.Perm (Fin n))) → W = ⊥ := by
  classical
  have hF := hxsF
  simp only [Bool.and_eq_true, List.all_eq_true] at hF
  have hinv : ∀ s ∈ xs.map pkp, s * s = 1 := by
    intro s hs
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hs
    have := eq_of_not_difV (hF.1 x hx)
    rwa [pkp_mulV, pkp_oneV] at this
  have hcomm : ∀ s ∈ xs.map pkp, ∀ t ∈ xs.map pkp, s * t = t * s := by
    intro s hs t ht
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hs
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 ht
    have := eq_of_not_difV (hF.2 x hx y hy)
    rwa [pkp_mulV, pkp_mulV] at this
  obtain ⟨-, -, -, h4, h5, h6⟩ := kleinOK_spec hkl
  have hconj' := hconj
  simp only [Bool.and_eq_true] at hconj'
  have e1 := eq_of_not_difV hconj'.1
  have e2 := eq_of_not_difV hconj'.2
  rw [pkp_conjV] at e1 e2
  rw [pkp_mulV] at e2
  set K : Subgroup (Equiv.Perm (Fin n)) := G ⊓ centralizer {pkp a} with hK
  have hxsH : ∀ x ∈ xs, pkp x ∈ closure {s | s ∈ xs.map pkp} := fun x hx =>
    subset_closure (List.mem_map_of_mem hx)
  refine noP_of_cents_ab hS₀G hp hp2 (xs := xs.map pkp) hinv hcomm ?_ (List.mem_map_of_mem ha)
    (List.mem_map_of_mem hb) h4 h5 h6 (ds := [oneV n, c₁, c₂].map fun c => (pkp c, pkp a, K))
    ?_ ?_ ?_ ?_ hS₀
  · intro s hs
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hs
    exact hxsS x hx
  · intro d hd x hx hxr
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 hd
    rw [hK, mem_inf, mem_centralizer_singleton_iff]
    exact ⟨hx, hxr⟩
  · intro d hd
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · rw [pkp_oneV]
      exact one_mem _
    · exact hc₁
    · exact hc₂
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · exact ⟨_, List.mem_map_of_mem (List.mem_cons_self ..), by rw [pkp_oneV]; group⟩
    · exact ⟨_, List.mem_map_of_mem (List.mem_cons_of_mem _ (List.mem_cons_self ..)), e1⟩
    · exact ⟨_, List.mem_map_of_mem (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..))), e2⟩
  · intro d hd y hy hyo
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hd
    rw [hK, mem_inf, mem_centralizer_singleton_iff] at hy
    obtain ⟨y', hy', rfl⟩ := hL _ hy.1
    have hpp := hps _ hy.1 hyo
    have hcw : witsF c xs ∈ [witsF (oneV n) xs, witsF c₁ xs, witsF c₂ xs] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    exact hN_of_chkPC hn hw hp hxsH c hchk hpp hcw y' hy' hy.2 hyo

end CFSG.KS.Ivk8NormP

end
