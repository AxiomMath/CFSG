module

public import CFSG.Combinatorics.HexagonAlternatingOctagonsThird

public section

open Finset CFSG.Combinatorics.CubicBipartiteMoore CFSG.Combinatorics.HexagonLayers
  CFSG.Combinatorics.HexagonFourEdgePath

namespace CFSG.Combinatorics.HexagonPeriodicPropagation

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {col : G.Coloring Bool} {w : {v : V // col v = false}} {ℓ : Fin 3 → V}
  {p : Fin 3 → Fin 2 → {v : V // col v = false}}
  {z q : {v : V // col v = false} → {v : V // col v = false} → {v : V // col v = false}}
  {c : {v : V // col v = false} → {v : V // col v = false} → Fin 3}
  {ε : {v : V // col v = false} → {v : V // col v = false} → Fin 2}

namespace IsFrame

variable (F : IsFrame G col w ℓ p z q c ε)
  {r : Fin 3 → {v : V // col v = false} → {v : V // col v = false}}
  (hr : ∀ i x, (pointGraph G col).dist w x = 3 → (pointGraph G col).dist w (r i x) = 3 ∧
    (pointGraph G col).Adj x (r i x) ∧ c x (r i x) = i)
include F hr

theorem r_eq {i : Fin 3} {x y : {v : V // col v = false}} (hx : (pointGraph G col).dist w x = 3)
    (hy : (pointGraph G col).dist w y = 3) (hxy : (pointGraph G col).Adj x y) (h : c x y = i) :
    r i x = y :=
  F.unique hx (hr i x hx).1 hy (hr i x hx).2.1 hxy ((hr i x hx).2.2.trans h.symm)

theorem r_invol {i : Fin 3} {x : {v : V // col v = false}} (hx : (pointGraph G col).dist w x = 3) :
    r i (r i x) = x :=
  F.r_eq hr (hr i x hx).1 hx (hr i x hx).2.1.symm
    ((F.symm hx (hr i x hx).1 (hr i x hx).2.1).trans (hr i x hx).2.2)

variable {S : Set {v : V // col v = false}} (hSO : ∀ x ∈ S, (pointGraph G col).dist w x = 3)
  (hSadj : ∀ x ∈ S, ∀ y, (pointGraph G col).dist w y = 3 → (pointGraph G col).Adj x y → y ∈ S)
  (hall : ∀ x : Fin 6 → {v : V // col v = false}, IsHex G col w x → (∀ n, x n ∈ S) →
    IsPeriodic c x)
include hSO hSadj hall

theorem pow_four {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    {x : {v : V // col v = false}} (hxS : x ∈ S) : (r i ∘ r j)^[4] x = x := by
  have hO : ∀ {y}, y ∈ S → (pointGraph G col).dist w y = 3 := fun hy => hSO _ hy
  have hm : ∀ {l : Fin 3} {y}, y ∈ S → r l y ∈ S := fun hy =>
    hSadj _ hy _ (hr _ _ (hO hy)).1 (hr _ _ (hO hy)).2.1
  obtain ⟨x₀, hx₀⟩ : ∃ y, r k x = y := ⟨_, rfl⟩
  obtain ⟨x₂, hx₂⟩ : ∃ y, r i x = y := ⟨_, rfl⟩
  obtain ⟨x₃, hx₃⟩ : ∃ y, r j x₂ = y := ⟨_, rfl⟩
  obtain ⟨x₄, hx₄⟩ : ∃ y, r i x₃ = y := ⟨_, rfl⟩
  obtain ⟨x₅, hx₅⟩ : ∃ y, r j x₄ = y := ⟨_, rfl⟩
  obtain ⟨x₆, hx₆⟩ : ∃ y, r k x₅ = y := ⟨_, rfl⟩
  obtain ⟨u₂, hu₂⟩ : ∃ y, r j x = y := ⟨_, rfl⟩
  obtain ⟨u₃, hu₃⟩ : ∃ y, r i u₂ = y := ⟨_, rfl⟩
  obtain ⟨u₄, hu₄⟩ : ∃ y, r j u₃ = y := ⟨_, rfl⟩
  obtain ⟨u₅, hu₅⟩ : ∃ y, r i u₄ = y := ⟨_, rfl⟩
  obtain ⟨u₆, hu₆⟩ : ∃ y, r k u₅ = y := ⟨_, rfl⟩
  have hS₀ : x₀ ∈ S := hx₀ ▸ hm hxS
  have hS₂ : x₂ ∈ S := hx₂ ▸ hm hxS
  have hS₃ : x₃ ∈ S := hx₃ ▸ hm hS₂
  have hS₄ : x₄ ∈ S := hx₄ ▸ hm hS₃
  have hS₅ : x₅ ∈ S := hx₅ ▸ hm hS₄
  have hS₆ : x₆ ∈ S := hx₆ ▸ hm hS₅
  have hU₂ : u₂ ∈ S := hu₂ ▸ hm hxS
  have hU₃ : u₃ ∈ S := hu₃ ▸ hm hU₂
  have hU₄ : u₄ ∈ S := hu₄ ▸ hm hU₃
  have hU₅ : u₅ ∈ S := hu₅ ▸ hm hU₄
  have hU₆ : u₆ ∈ S := hu₆ ▸ hm hU₅
  have st : ∀ {l : Fin 3} {a b}, a ∈ S → r l a = b → (pointGraph G col).Adj a b ∧ c a b = l :=
    fun ha hb => hb ▸ ⟨(hr _ _ (hO ha)).2.1, (hr _ _ (hO ha)).2.2⟩
  obtain ⟨a10, c10⟩ := st hxS hx₀
  obtain ⟨a12, c12⟩ := st hxS hx₂
  obtain ⟨a23, c23⟩ := st hS₂ hx₃
  obtain ⟨a34, c34⟩ := st hS₃ hx₄
  obtain ⟨a45, c45⟩ := st hS₄ hx₅
  obtain ⟨a56, c56⟩ := st hS₅ hx₆
  obtain ⟨b12, d12⟩ := st hxS hu₂
  obtain ⟨b23, d23⟩ := st hU₂ hu₃
  obtain ⟨b34, d34⟩ := st hU₃ hu₄
  obtain ⟨b45, d45⟩ := st hU₄ hu₅
  obtain ⟨b56, d56⟩ := st hU₅ hu₆
  have c01 : c x₀ x = k := (F.symm (hO hxS) (hO hS₀) a10).trans c10
  have hW := F.seven_third hSO hSadj hall hij hjk hik hS₀ hxS hS₂ hS₃ hS₄ hS₅ hS₆ a10.symm a12
    a23 a34 a45 a56 c01 c12 c23 c34 c45 c56
  have hU := F.seven_third hSO hSadj hall hij.symm hik hjk hS₀ hxS hU₂ hU₃ hU₄ hU₅ hU₆
    a10.symm b12 b23 b34 b45 b56 c01 d12 d23 d34 d45 d56
  obtain ⟨n01, -, -, -, n05, -, -, n13, -, n15, -, -, -, -, -, n34, n35, n36, n45, n46, n56⟩ :=
    F.seven_ne hij hjk hik (hO hS₀) (hO hxS) (hO hS₂) (hO hS₃) (hO hS₄) (hO hS₅) (hO hS₆)
      a10.symm a12 a23 a34 a45 a56 c01 c12 c23 c34 c45 c56
  obtain ⟨-, -, -, -, n05', -, -, n13', -, n15', -, -, -, -, -, -, -, -, -, -, -⟩ :=
    F.seven_ne hij.symm hik hjk (hO hS₀) (hO hxS) (hO hU₂) (hO hU₃) (hO hU₄) (hO hU₅)
      (hO hU₆) a10.symm b12 b23 b34 b45 b56 c01 d12 d23 d34 d45 d56
  have hd := point_dist_eq_iff F.moore.conn col
  have f : ∀ {y : {v : V // col v = false}}, y ∈ S → G.dist (w : V) y = 6 :=
    fun hy => (hd w _ 3).mp (hO hy)
  have hV : ∀ {a b : {v : V // col v = false}}, a ≠ b → (a : V) ≠ b :=
    fun h h' => h (Subtype.ext h')
  obtain ⟨m₀, -, x₀m₀, x₁m₀, Am₀, A4, -⟩ := F.edge (hO hS₀) (hO hxS) a10.symm
  obtain ⟨m₅, N₅, x₅m₅, -, Bm₅, B4, -⟩ := F.edge (hO hS₅) (hO hS₆) a56
  obtain ⟨m₅', -, u₅m₅', -, B'm₅', -⟩ := F.edge (hO hU₅) (hO hU₆) b56
  rw [← hW] at Bm₅
  rw [← hU] at B'm₅'
  have hm5 : ∀ {m : V} {y : {v : V // col v = false}}, y ∈ S → G.Adj (y : V) m →
      G.dist (w : V) m = 3 + 2 := fun hy hym => dist_eq_five_of_adj F.moore col (f hy) hym
  have hcard := card_nbrsAt_succ F.moore.cyc F.moore.conn col F.moore.deg (k := 3)
    (by norm_num) (show G.dist (w : V) (z x₀ x : V) = 3 + 1 from A4)
  have m05 : m₀ ≠ m₅ := fun h => not_three_far_on_line F.moore col (f hS₀) (f hxS) (f hS₅) x₀m₀
    x₁m₀ (by rw [h]; exact x₅m₅) (hV n01) (hV n05) (hV n15)
  have m05' : m₀ ≠ m₅' := fun h => not_three_far_on_line F.moore col (f hS₀) (f hxS) (f hU₅)
    x₀m₀ x₁m₀ (by rw [h]; exact u₅m₅') (hV n01) (hV n05') (hV n15')
  have hm55 : m₅ = m₅' := by
    by_contra hne
    have hsub : ({m₀, m₅, m₅'} : Finset V) ⊆ nbrsAt G (w : V) (z x₀ x : V) (3 + 2) := by
      intro m hm
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rw [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
      rcases hm with rfl | rfl | rfl
      exacts [⟨Am₀, hm5 hS₀ x₀m₀⟩, ⟨Bm₅, hm5 hS₅ x₅m₅⟩, ⟨B'm₅', hm5 hU₅ u₅m₅'⟩]
    have hle := Finset.card_le_card hsub
    rw [hcard, Finset.card_eq_three.mpr ⟨m₀, m₅, m₅', m05, m05', hne, rfl⟩] at hle
    omega
  rw [← hm55] at u₅m₅'
  have hu₅N : (u₅ : V) ∈ G.neighborFinset m₅ := (SimpleGraph.mem_neighborFinset _ _ _).mpr
    u₅m₅'.symm
  rw [N₅] at hu₅N
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu₅N
  have hx5u5 : x₅ = u₅ := by
    rcases hu₅N with h | h | h
    · exact (Subtype.ext h).symm
    ·
      exfalso
      have e : u₅ = x₆ := Subtype.ext h
      have h6u4 : (pointGraph G col).Adj x₆ u₄ := by rw [← e]; exact b45.symm
      have c6u4 : c x₆ u₄ = i := by rw [← e, F.symm (hO hU₄) (hO hU₅) b45]; exact d45
      have n4u : x₄ ≠ u₄ := fun e' =>
        F.no_triangle (hO hS₄) (hO hS₅) (hO hS₆) a45 a56 (by rw [e']; exact h6u4)
      have n3u : x₃ ≠ u₄ := fun e' => F.no_square (hO hS₃) (hO hS₄) (hO hS₅) (hO hS₆) a34 a45
        a56 (by rw [e']; exact h6u4) n35 n46
      have n5u : x₅ ≠ u₄ := fun e' => hik (c6u4.symm.trans (by
        rw [← e', F.symm (hO hS₅) (hO hS₆) a56]
        exact c56))
      have hnd : [x₃, x₄, x₅, x₆, u₄].Nodup :=
        nodup_five n34 n35 n36 n3u n45 n46 n4u n56 n5u h6u4.ne
      obtain ⟨u', ⟨hu', h3u', h4u'⟩, -, hnd6, -⟩ := F.complete hij hjk hik (hO hS₃) (hO hS₄)
        (hO hS₅) (hO hS₆) (hO hU₄) a34 a45 a56 h6u4 hnd c34 c45 c56 c6u4
      have hSu' : u' ∈ S := hSadj _ hS₃ _ hu' h3u'
      have hX : IsHex G col w ![x₃, x₄, x₅, x₆, u₄, u'] := by
        refine ⟨List.nodup_ofFn.mp (by simpa [List.ofFn_succ] using hnd6), fun m => ?_,
          fun m => ?_⟩
        · fin_cases m
          exacts [hO hS₃, hO hS₄, hO hS₅, hO hS₆, hO hU₄, hu']
        · fin_cases m
          exacts [a34, a45, a56, h6u4, h4u', h3u'.symm]
      obtain ⟨a, b, d, -, -, -, hcol⟩ := hall _ hX (by
        intro m
        fin_cases m
        exacts [hS₃, hS₄, hS₅, hS₆, hU₄, hSu'])
      have e1 : c x₄ x₅ = b := hcol 1
      have e4 : c u₄ u' = b := hcol 4
      have hu'3 : u' = u₃ := F.unique (hO hU₄) hu' (hO hU₃) h4u' b34.symm
        (e4.trans (e1.symm.trans (c45.trans (d34.symm.trans
          (F.symm (hO hU₃) (hO hU₄) b34).symm))))
      rw [hu'3] at h3u'
      have n2u3 : x₂ ≠ u₃ := fun e' =>
        F.no_triangle (hO hxS) (hO hS₂) (hO hU₂) a12 (by rw [e']; exact b23.symm) b12.symm
      exact F.no_pentagon (hO hxS) (hO hS₂) (hO hS₃) (hO hU₃) (hO hU₂) a12 a23 h3u' b23.symm
        b12.symm n13 n13' n2u3
    · exfalso
      have h6 := f hU₅
      rw [h] at h6
      omega
  show r i (r j (r i (r j (r i (r j (r i (r j x))))))) = x
  rw [hu₂, hu₃, hu₄, hu₅, ← hx5u5, ← hx₅, F.r_invol hr (hO hS₄), ← hx₄, F.r_invol hr (hO hS₃),
    ← hx₃, F.r_invol hr (hO hS₂), ← hx₂, F.r_invol hr (hO hxS)]

theorem alternating_eight {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    {y : ℕ → {v : V // col v = false}} (hyS : ∀ n ≤ 8, y n ∈ S)
    (hadj : ∀ n < 8, (pointGraph G col).Adj (y n) (y (n + 1)))
    (hcol : ∀ n < 8, c (y n) (y (n + 1)) = if Even n then i else j) :
    y 8 = y 0 ∧ ∀ a < 8, ∀ b < 8, y a = y b → a = b := by
  have hO : ∀ {u}, u ∈ S → (pointGraph G col).dist w u = 3 := fun hu => hSO _ hu
  have step : ∀ n < 8, y (n + 1) = r (if Even n then i else j) (y n) := fun n hn =>
    (F.r_eq hr (hO (hyS n (by omega))) (hO (hyS (n + 1) (by omega))) (hadj n hn)
      (hcol n hn)).symm
  have h80 : y 8 = y 0 := by
    rw [step 7 (by norm_num), step 6 (by norm_num), step 5 (by norm_num), step 4 (by norm_num),
      step 3 (by norm_num), step 2 (by norm_num), step 1 (by norm_num), step 0 (by norm_num)]
    simp only [show Even 0 by decide, show ¬ Even 1 by decide, show Even 2 by decide,
      show ¬ Even 3 by decide, show Even 4 by decide, show ¬ Even 5 by decide,
      show Even 6 by decide, show ¬ Even 7 by decide, ite_true, ite_false]
    exact F.pow_four hr hSO hSadj hall hij.symm hik hjk (hyS 0 (by norm_num))
  refine ⟨h80, ?_⟩
  set ŷ : ℕ → {v : V // col v = false} := fun n => y (n % 8) with hŷ
  have hŷS : ∀ n, ŷ n ∈ S := fun n => hyS _ (Nat.mod_lt _ (by norm_num)).le
  have hpar : ∀ n, (Even (n % 8) ↔ Even n) := by
    intro n
    simp only [Nat.even_iff]
    omega
  have hŷ1 : ∀ n, ŷ (n + 1) = y (n % 8 + 1) := by
    intro n
    show y ((n + 1) % 8) = y (n % 8 + 1)
    by_cases h7 : n % 8 = 7
    · rw [show (n + 1) % 8 = 0 by omega, h7, h80]
    · rw [show (n + 1) % 8 = n % 8 + 1 by omega]
  have hŷadj : ∀ n, (pointGraph G col).Adj (ŷ n) (ŷ (n + 1)) := fun n => by
    rw [hŷ1]
    exact hadj _ (Nat.mod_lt _ (by norm_num))
  have hŷcol : ∀ n, c (ŷ n) (ŷ (n + 1)) = if Even n then i else j := fun n => by
    rw [hŷ1]
    show c (y (n % 8)) (y (n % 8 + 1)) = _
    rw [hcol _ (Nat.mod_lt _ (by norm_num))]
    by_cases h : Even n
    · rw [ite_eq_left ((hpar n).mpr h), ite_eq_left h]
    · rw [ite_eq_right (fun h' => h ((hpar n).mp h')), ite_eq_right h]
  have hcolne : ∀ n, (if Even n then i else j) ≠ (if Even (n + 1) then i else j) := by
    intro n
    rcases Nat.even_or_odd n with h | h
    · rw [ite_eq_left h, ite_eq_right (Nat.not_even_iff_odd.mpr h.add_one)]
      exact hij
    · rw [ite_eq_right (Nat.not_even_iff_odd.mpr h), ite_eq_left h.add_one]
      exact hij.symm
  have L1 : ∀ n, ŷ n ≠ ŷ (n + 1) := fun n => (hŷadj n).ne
  have L2 : ∀ n, ŷ n ≠ ŷ (n + 1 + 1) := by
    intro n e
    have h1 : c (ŷ (n + 1)) (ŷ n) = if Even n then i else j :=
      (F.symm (hO (hŷS n)) (hO (hŷS (n + 1))) (hŷadj n)).trans (hŷcol n)
    have h2 := hŷcol (n + 1)
    rw [← e] at h2
    exact hcolne n (h1.symm.trans h2)
  have L3 : ∀ n, ŷ n ≠ ŷ (n + 1 + 1 + 1) := fun n e =>
    F.no_triangle (hO (hŷS n)) (hO (hŷS (n + 1))) (hO (hŷS (n + 1 + 1))) (hŷadj n)
      (hŷadj (n + 1)) (by rw [e]; exact hŷadj (n + 1 + 1))
  have L4 : ∀ n, ŷ n ≠ ŷ (n + 1 + 1 + 1 + 1) := fun n e =>
    F.no_square (hO (hŷS n)) (hO (hŷS (n + 1))) (hO (hŷS (n + 1 + 1)))
      (hO (hŷS (n + 1 + 1 + 1))) (hŷadj n) (hŷadj (n + 1)) (hŷadj (n + 1 + 1))
      (by rw [e]; exact hŷadj (n + 1 + 1 + 1)) (L2 n) (L2 (n + 1))
  have key : ∀ n d, 1 ≤ d → d ≤ 4 → ŷ n ≠ ŷ (n + d) := by
    intro n d h1 h4
    interval_cases d
    exacts [L1 n, L2 n, L3 n, L4 n]
  have hŷy : ∀ n < 8, ŷ n = y n := fun n hn => by
    show y (n % 8) = y n
    rw [Nat.mod_eq_of_lt hn]
  have hwrap : ∀ a < 8, ŷ (a + 8) = y a := fun a ha => by
    show y ((a + 8) % 8) = y a
    rw [Nat.add_mod_right, Nat.mod_eq_of_lt ha]
  intro a ha b hb hab
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · by_cases hd : b - a ≤ 4
    · exact key a (b - a) (by omega) hd
        (by rw [hŷy a ha, show a + (b - a) = b by omega, hŷy b hb]; exact hab)
    · exact key b (8 - (b - a)) (by omega) (by omega)
        (by rw [hŷy b hb, show b + (8 - (b - a)) = a + 8 by omega, hwrap a ha]; exact hab.symm)
  · by_cases hd : a - b ≤ 4
    · exact key b (a - b) (by omega) hd
        (by rw [hŷy b hb, show b + (a - b) = a by omega, hŷy a ha]; exact hab.symm)
    · exact key a (8 - (a - b)) (by omega) (by omega)
        (by rw [hŷy a ha, show a + (8 - (a - b)) = b + 8 by omega, hwrap b hb]; exact hab)

theorem alternating_orbit {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    {x : {v : V // col v = false}} (hxS : x ∈ S) :
    ∃ Y : Fin 8 → {v : V // col v = false}, Function.Injective Y ∧ Y 0 = x ∧
      (∀ n, (pointGraph G col).Adj (Y n) (Y (n + 1)) ∧
        c (Y n) (Y (n + 1)) = ![i, j, i, j, i, j, i, j] n) ∧
      {u | Relation.ReflTransGen (fun a b => b = r i a ∨ b = r j a) x u} = Set.range Y := by
  have hO : ∀ {u}, u ∈ S → (pointGraph G col).dist w u = 3 := fun hu => hSO _ hu
  let y : ℕ → {v : V // col v = false} := fun n =>
    Nat.rec x (fun m ym => r (if Even m then i else j) ym) n
  have hy0 : y 0 = x := rfl
  have hys : ∀ n, y (n + 1) = r (if Even n then i else j) (y n) := fun n => rfl
  have hyS : ∀ n, y n ∈ S := by
    intro n
    induction n with
    | zero => exact hxS
    | succ m ih => exact hSadj _ ih _ (hr _ _ (hO ih)).1 (by rw [hys]; exact (hr _ _ (hO ih)).2.1)
  have hadj : ∀ n, (pointGraph G col).Adj (y n) (y (n + 1)) := fun n => by
    rw [hys]
    exact (hr _ _ (hO (hyS n))).2.1
  have hcol : ∀ n, c (y n) (y (n + 1)) = if Even n then i else j := fun n => by
    rw [hys]
    exact (hr _ _ (hO (hyS n))).2.2
  obtain ⟨h80, hinj⟩ := F.alternating_eight hr hSO hSadj hall hij hjk hik (fun n _ => hyS n)
    (fun n _ => hadj n) (fun n _ => hcol n)
  let Y : Fin 8 → {v : V // col v = false} := fun n => y n.val
  have hY1 : ∀ n : Fin 8, Y (n + 1) = y (n.val + 1) := by
    intro n
    fin_cases n
    exacts [rfl, rfl, rfl, rfl, rfl, rfl, rfl, h80.symm]
  have hpat : ∀ n : Fin 8, (if Even n.val then i else j) = ![i, j, i, j, i, j, i, j] n := by
    intro n
    fin_cases n <;> simp [Nat.even_iff]
  have hYadj : ∀ n : Fin 8, (pointGraph G col).Adj (Y n) (Y (n + 1)) ∧
      c (Y n) (Y (n + 1)) = ![i, j, i, j, i, j, i, j] n := fun n => by
    rw [hY1]
    exact ⟨hadj n.val, (hcol n.val).trans (hpat n)⟩
  refine ⟨Y, fun a b hab => Fin.ext (hinj a.val a.isLt b.val b.isLt hab), hy0, hYadj, ?_⟩
  have hfwd : ∀ n : Fin 8, Y (n + 1) = r (![i, j, i, j, i, j, i, j] n) (Y n) := fun n =>
    (F.r_eq hr (hO (hyS _)) (hO (hyS _)) (hYadj n).1 (hYadj n).2).symm
  have hbwd : ∀ n : Fin 8, Y (n - 1) = r (![i, j, i, j, i, j, i, j] (n - 1)) (Y n) := by
    intro n
    have h := hfwd (n - 1)
    rw [sub_add_cancel] at h
    rw [h, F.r_invol hr (hO (hyS _))]
  have hcover : ∀ n : Fin 8, (![i, j, i, j, i, j, i, j] n = i ∧
      ![i, j, i, j, i, j, i, j] (n - 1) = j) ∨ (![i, j, i, j, i, j, i, j] n = j ∧
      ![i, j, i, j, i, j, i, j] (n - 1) = i) := by
    intro n
    fin_cases n <;> simp
  have hclosed : ∀ u ∈ Set.range Y, r i u ∈ Set.range Y ∧ r j u ∈ Set.range Y := by
    rintro u ⟨n, rfl⟩
    rcases hcover n with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨⟨n + 1, by rw [hfwd, h1]⟩, ⟨n - 1, by rw [hbwd, h2]⟩⟩
    · exact ⟨⟨n - 1, by rw [hbwd, h2]⟩, ⟨n + 1, by rw [hfwd, h1]⟩⟩
  ext u
  constructor
  · intro hu
    induction hu with
    | refl => exact ⟨0, hy0⟩
    | tail _ hbc ih =>
      rcases hbc with rfl | rfl
      exacts [(hclosed _ ih).1, (hclosed _ ih).2]
  · rintro ⟨⟨n, hn⟩, rfl⟩
    show Relation.ReflTransGen (fun a b => b = r i a ∨ b = r j a) x (y n)
    clear hn
    induction n with
    | zero => exact Relation.ReflTransGen.refl
    | succ m ih =>
      refine Relation.ReflTransGen.tail ih ?_
      rw [hys]
      by_cases h : Even m
      · exact Or.inl (by rw [ite_eq_left h])
      · exact Or.inr (by rw [ite_eq_right h])

end IsFrame

end CFSG.Combinatorics.HexagonPeriodicPropagation
