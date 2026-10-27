module

public import CFSG.Combinatorics.HexagonAlternatingOctagonsSupport

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
include F

theorem seven_ne {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    {x₀ x₁ x₂ x₃ x₄ x₅ x₆ : {v : V // col v = false}} (h₀ : (pointGraph G col).dist w x₀ = 3)
    (h₁ : (pointGraph G col).dist w x₁ = 3) (h₂ : (pointGraph G col).dist w x₂ = 3)
    (h₃ : (pointGraph G col).dist w x₃ = 3) (h₄ : (pointGraph G col).dist w x₄ = 3)
    (h₅ : (pointGraph G col).dist w x₅ = 3) (h₆ : (pointGraph G col).dist w x₆ = 3)
    (h01 : (pointGraph G col).Adj x₀ x₁) (h12 : (pointGraph G col).Adj x₁ x₂)
    (h23 : (pointGraph G col).Adj x₂ x₃) (h34 : (pointGraph G col).Adj x₃ x₄)
    (h45 : (pointGraph G col).Adj x₄ x₅) (h56 : (pointGraph G col).Adj x₅ x₆)
    (c01 : c x₀ x₁ = k) (c12 : c x₁ x₂ = i) (c23 : c x₂ x₃ = j) (c34 : c x₃ x₄ = i)
    (c45 : c x₄ x₅ = j) (c56 : c x₅ x₆ = k) :
    x₀ ≠ x₁ ∧ x₀ ≠ x₂ ∧ x₀ ≠ x₃ ∧ x₀ ≠ x₄ ∧ x₀ ≠ x₅ ∧ x₀ ≠ x₆ ∧ x₁ ≠ x₂ ∧ x₁ ≠ x₃ ∧ x₁ ≠ x₄ ∧
      x₁ ≠ x₅ ∧ x₁ ≠ x₆ ∧ x₂ ≠ x₃ ∧ x₂ ≠ x₄ ∧ x₂ ≠ x₅ ∧ x₂ ≠ x₆ ∧ x₃ ≠ x₄ ∧ x₃ ≠ x₅ ∧
      x₃ ≠ x₆ ∧ x₄ ≠ x₅ ∧ x₄ ≠ x₆ ∧ x₅ ≠ x₆ := by
  have hne : ∀ {a b d : {v : V // col v = false}}, c b a ≠ c b d → a ≠ d :=
    fun h e => h (by rw [e])
  have n02 : x₀ ≠ x₂ := hne (by rw [F.symm h₀ h₁ h01, c01, c12]; exact hik.symm)
  have n13 : x₁ ≠ x₃ := hne (by rw [F.symm h₁ h₂ h12, c12, c23]; exact hij)
  have n24 : x₂ ≠ x₄ := hne (by rw [F.symm h₂ h₃ h23, c23, c34]; exact hij.symm)
  have n35 : x₃ ≠ x₅ := hne (by rw [F.symm h₃ h₄ h34, c34, c45]; exact hij)
  have n46 : x₄ ≠ x₆ := hne (by rw [F.symm h₄ h₅ h45, c45, c56]; exact hjk)
  have n03 : x₀ ≠ x₃ := fun e => F.no_triangle h₀ h₁ h₂ h01 h12 (by rw [e]; exact h23)
  have n14 : x₁ ≠ x₄ := fun e => F.no_triangle h₁ h₂ h₃ h12 h23 (by rw [e]; exact h34)
  have n25 : x₂ ≠ x₅ := fun e => F.no_triangle h₂ h₃ h₄ h23 h34 (by rw [e]; exact h45)
  have n36 : x₃ ≠ x₆ := fun e => F.no_triangle h₃ h₄ h₅ h34 h45 (by rw [e]; exact h56)
  have n04 : x₀ ≠ x₄ := fun e =>
    F.no_square h₀ h₁ h₂ h₃ h01 h12 h23 (by rw [e]; exact h34) n02 n13
  have n15 : x₁ ≠ x₅ := fun e =>
    F.no_square h₁ h₂ h₃ h₄ h12 h23 h34 (by rw [e]; exact h45) n13 n24
  have n26 : x₂ ≠ x₆ := fun e =>
    F.no_square h₂ h₃ h₄ h₅ h23 h34 h45 (by rw [e]; exact h56) n24 n35
  have n05 : x₀ ≠ x₅ := fun e =>
    F.no_pentagon h₀ h₁ h₂ h₃ h₄ h01 h12 h23 h34 (by rw [e]; exact h45) n02 n03 n13
  have n16 : x₁ ≠ x₆ := fun e =>
    F.no_pentagon h₁ h₂ h₃ h₄ h₅ h12 h23 h34 h45 (by rw [e]; exact h56) n13 n14 n24
  have n06 : x₀ ≠ x₆ := by
    intro e
    have h' : c x₀ x₅ = k := by rw [e, F.symm h₅ h₆ h56, c56]
    exact n15 (F.unique h₀ h₁ h₅ h01 (by rw [e]; exact h56.symm) (c01.trans h'.symm))
  exact ⟨h01.ne, n02, n03, n04, n05, n06, h12.ne, n13, n14, n15, n16, h23.ne, n24, n25, n26,
    h34.ne, n35, n36, h45.ne, n46, h56.ne⟩

theorem seven_third {S : Set {v : V // col v = false}}
    (hSO : ∀ x ∈ S, (pointGraph G col).dist w x = 3)
    (hSadj : ∀ x ∈ S, ∀ y, (pointGraph G col).dist w y = 3 → (pointGraph G col).Adj x y → y ∈ S)
    (hall : ∀ x : Fin 6 → {v : V // col v = false}, IsHex G col w x → (∀ n, x n ∈ S) →
      IsPeriodic c x)
    {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    {x₀ x₁ x₂ x₃ x₄ x₅ x₆ : {v : V // col v = false}} (hS₀ : x₀ ∈ S) (hS₁ : x₁ ∈ S)
    (hS₂ : x₂ ∈ S) (hS₃ : x₃ ∈ S) (hS₄ : x₄ ∈ S) (hS₅ : x₅ ∈ S) (hS₆ : x₆ ∈ S)
    (h01 : (pointGraph G col).Adj x₀ x₁) (h12 : (pointGraph G col).Adj x₁ x₂)
    (h23 : (pointGraph G col).Adj x₂ x₃) (h34 : (pointGraph G col).Adj x₃ x₄)
    (h45 : (pointGraph G col).Adj x₄ x₅) (h56 : (pointGraph G col).Adj x₅ x₆)
    (c01 : c x₀ x₁ = k) (c12 : c x₁ x₂ = i) (c23 : c x₂ x₃ = j) (c34 : c x₃ x₄ = i)
    (c45 : c x₄ x₅ = j) (c56 : c x₅ x₆ = k) : z x₀ x₁ = z x₅ x₆ := by
  have hd := point_dist_eq_iff F.moore.conn col
  have hA := point_adj_iff F.moore.conn col
  have h₀ := hSO _ hS₀
  have h₁ := hSO _ hS₁
  have h₂ := hSO _ hS₂
  have h₃ := hSO _ hS₃
  have h₄ := hSO _ hS₄
  have h₅ := hSO _ hS₅
  have h₆ := hSO _ hS₆
  obtain ⟨n01, n02, n03, n04, -, -, n12, n13, n14, -, -, n23, n24, -, -, n34, n35, n36, n45, n46,
    n56⟩ := F.seven_ne hij hjk hik h₀ h₁ h₂ h₃ h₄ h₅ h₆ h01 h12 h23 h34 h45 h56 c01 c12 c23 c34
      c45 c56
  have f : ∀ {x : {v : V // col v = false}}, (pointGraph G col).dist w x = 3 →
      G.dist (w : V) x = 6 := fun hx => (hd w _ 3).mp hx
  have f₀ := f h₀
  have f₁ := f h₁
  have f₂ := f h₂
  have f₃ := f h₃
  have f₄ := f h₄
  have f₅ := f h₅
  have hV : ∀ {a b : {v : V // col v = false}}, a ≠ b → (a : V) ≠ b :=
    fun h h' => h (Subtype.ext h')
  have hle2 : ∀ {a b μ : V}, G.Adj a μ → G.Adj b μ → G.dist a b ≤ 2 := by
    intro a b μ ha hb
    have h := SimpleGraph.dist_le
      (SimpleGraph.Walk.cons ha (SimpleGraph.Walk.cons hb.symm SimpleGraph.Walk.nil))
    simpa using h
  obtain ⟨m₀, N₀, x₀m₀, x₁m₀, Am₀, A4, t2, At2, -, -, -⟩ := F.edge h₀ h₁ h01
  obtain ⟨m₁, -, x₁m₁, x₂m₁, -, -, -, -, -, -, -⟩ := F.edge h₁ h₂ h12
  obtain ⟨m₂, -, x₂m₂, x₃m₂, -, -, -, -, -, -, -⟩ := F.edge h₂ h₃ h23
  obtain ⟨m₃, -, x₃m₃, x₄m₃, -, -, -, -, -, -, -⟩ := F.edge h₃ h₄ h34
  obtain ⟨m₄, -, x₄m₄, x₅m₄, -, -, -, -, -, -, -⟩ := F.edge h₄ h₅ h45
  obtain ⟨m₅, N₅, x₅m₅, x₆m₅, Bm₅, B4, -, Bt2, -, -, -⟩ := F.edge h₅ h₆ h56
  have m01 : m₀ ≠ m₁ := fun h => not_three_far_on_line F.moore col f₀ f₁ f₂ x₀m₀ x₁m₀
    (by rw [h]; exact x₂m₁) (hV n01) (hV n02) (hV n12)
  have m12 : m₁ ≠ m₂ := fun h => not_three_far_on_line F.moore col f₁ f₂ f₃ x₁m₁ x₂m₁
    (by rw [h]; exact x₃m₂) (hV n12) (hV n13) (hV n23)
  have m23 : m₂ ≠ m₃ := fun h => not_three_far_on_line F.moore col f₂ f₃ f₄ x₂m₂ x₃m₂
    (by rw [h]; exact x₄m₃) (hV n23) (hV n24) (hV n34)
  have m34 : m₃ ≠ m₄ := fun h => not_three_far_on_line F.moore col f₃ f₄ f₅ x₃m₃ x₄m₃
    (by rw [h]; exact x₅m₄) (hV n34) (hV n35) (hV n45)
  have m45 : m₄ ≠ m₅ := fun h => not_three_far_on_line F.moore col f₄ f₅ (f h₆) x₄m₄ x₅m₄
    (by rw [h]; exact x₆m₅) (hV n45) (hV n46) (hV n56)
  obtain ⟨y, hy, h3y, c3y⟩ := F.exists_colour h₃ k
  obtain ⟨n, -, x₃n, -, Zn, Z4, -, Zt2, -, -, -⟩ := F.edge h₃ hy h3y
  have ny0 : y ≠ x₀ := fun e =>
    F.no_square h₀ h₁ h₂ h₃ h01 h12 h23 (by rw [← e]; exact h3y) n02 n13
  have ny1 : y ≠ x₁ := fun e => F.no_triangle h₁ h₂ h₃ h12 h23 (by rw [← e]; exact h3y)
  have ny2 : y ≠ x₂ := fun e =>
    hjk (c23.symm.trans ((F.symm h₂ h₃ h23).symm.trans (by rw [← e]; exact c3y)))
  have ny4 : y ≠ x₄ := fun e => hik (c34.symm.trans (by rw [← e]; exact c3y))
  have ny5 : y ≠ x₅ := fun e => F.no_triangle h₃ h₄ h₅ h34 h45 (by rw [← e]; exact h3y.symm)
  have ny6 : y ≠ x₆ := fun e =>
    F.no_square h₃ h₄ h₅ h₆ h34 h45 h56 (by rw [← e]; exact h3y.symm) n35 n46
  have hq1 : q x₀ x₁ = q x₃ y := F.repeat_label h₀ h₁ h₂ h₃ hy h01 h12 h23 h3y
    (nodup_five n01 n02 n03 ny0.symm n12 n13 ny1.symm n23 ny2.symm h3y.ne) (c01.trans c3y.symm)
  have hq2 : q y x₃ = q x₅ x₆ := F.repeat_label hy h₃ h₄ h₅ h₆ h3y.symm h34 h45 h56
    (nodup_five h3y.ne.symm ny4 ny5 ny6 n34 n35 n36 n45 n46 n56)
    (((F.symm h₃ hy h3y).trans c3y).trans c56.symm)
  have hq3 : q y x₃ = q x₃ y :=
    (frame_symm F.moore col F.inj F.root F.line F.ne F.label F.data h₃ hy h3y).2.1
  rw [← hq1] at Zt2
  rw [← hq2, hq3, ← hq1] at Bt2
  obtain ⟨-, -, -, -, dA3⟩ := dist_of_path_six F.moore col Am₀ x₁m₀.symm x₁m₁ x₂m₁.symm x₂m₂
    x₃m₂.symm (fun h => by rw [h] at f₁; omega) m01.symm (hV n12.symm) m12.symm (hV n23.symm)
  obtain ⟨-, -, -, -, dB3⟩ := dist_of_path_six F.moore col Bm₅ x₅m₅.symm x₅m₄ x₄m₄.symm x₄m₃
    x₃m₃.symm (fun h => by rw [h] at f₅; omega) m45 (hV n45) m34 (hV n34)
  have hZ : ∀ {a : V}, G.dist a x₃ = 6 → G.dist a (q x₀ x₁ : V) = 2 →
      G.dist a (z x₃ y : V) = 4 := by
    intro a ha hat
    have han : G.dist a n = 5 := dist_eq_five_of_adj F.moore col ha x₃n
    have hup := F.moore.conn.dist_triangle (u := a) (v := (q x₀ x₁ : V)) (w := (z x₃ y : V))
    rw [SimpleGraph.dist_comm (u := (q x₀ x₁ : V)) (v := (z x₃ y : V))] at hup
    rcases dist_adj F.moore.conn col Zn.symm a with h | h <;> omega
  have hAZ := hZ dA3 At2
  have hBZ := hZ dB3 Bt2
  obtain ⟨μA, AμA, tμA⟩ := exists_adj_adj_of_dist_eq_two F.moore.conn At2
  obtain ⟨μB, BμB, tμB⟩ := exists_adj_adj_of_dist_eq_two F.moore.conn Bt2
  obtain ⟨μZ, ZμZ, tμZ⟩ := exists_adj_adj_of_dist_eq_two F.moore.conn Zt2
  have hμ3 : ∀ {a μ : V}, G.dist (w : V) a = 4 → G.Adj a μ → G.Adj (q x₀ x₁ : V) μ →
      G.dist (w : V) μ = 1 + 2 := by
    intro a μ ha haμ htμ
    rcases dist_adj F.moore.conn col haμ (w : V) with h | h
    · rcases dist_adj F.moore.conn col htμ (w : V) with h' | h' <;> omega
    · omega
  have hAZ' : μA ≠ μZ := fun h => by
    rw [← h] at ZμZ
    have := hle2 AμA ZμZ
    omega
  have hBZ' : μB ≠ μZ := fun h => by
    rw [← h] at ZμZ
    have := hle2 BμB ZμZ
    omega
  have hcard := card_nbrsAt_succ F.moore.cyc F.moore.conn col F.moore.deg (k := 1) (by norm_num)
    (show G.dist (w : V) (q x₀ x₁ : V) = 1 + 1 from t2)
  have hμ : μA = μB := by
    by_contra hne
    have hsub : ({μA, μB, μZ} : Finset V) ⊆ nbrsAt G (w : V) (q x₀ x₁ : V) (1 + 2) := by
      intro μ hμ
      simp only [Finset.mem_insert, Finset.mem_singleton] at hμ
      rw [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
      rcases hμ with rfl | rfl | rfl
      exacts [⟨tμA, hμ3 A4 AμA tμA⟩, ⟨tμB, hμ3 B4 BμB tμB⟩, ⟨tμZ, hμ3 Z4 ZμZ tμZ⟩]
    have hle := Finset.card_le_card hsub
    rw [hcard, Finset.card_eq_three.mpr ⟨μA, μB, μZ, hne, hAZ', hBZ', rfl⟩] at hle
    omega
  rw [← hμ] at BμB
  by_contra hAB
  have hABV : (z x₀ x₁ : V) ≠ z x₅ x₆ := fun h => hAB (Subtype.ext h)
  have htm0 : μA ≠ m₀ := by
    intro h
    have ht : (q x₀ x₁ : V) ∈ G.neighborFinset m₀ := by
      rw [← h]
      exact (SimpleGraph.mem_neighborFinset _ _ _).mpr tμA.symm
    rw [N₀] at ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with h' | h' | h' <;> rw [h'] at t2 <;> omega
  have htm5 : μA ≠ m₅ := by
    intro h
    have ht : (q x₀ x₁ : V) ∈ G.neighborFinset m₅ := by
      rw [← h]
      exact (SimpleGraph.mem_neighborFinset _ _ _).mpr tμA.symm
    rw [N₅] at ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    have f₆ := f h₆
    rcases ht with h' | h' | h' <;> rw [h'] at t2 <;> omega
  obtain ⟨-, -, -, -, d41⟩ := dist_of_path_six F.moore col x₄m₃ x₃m₃.symm x₃m₂ x₂m₂.symm x₂m₁
    x₁m₁.symm (hV n34) m23 (hV n23) m12 (hV n12)
  obtain ⟨-, -, -, -, d4A⟩ := dist_of_path_six F.moore col x₄m₄ x₅m₄.symm x₅m₅ Bm₅.symm BμB
    AμA.symm (hV n45.symm) m45.symm (fun h => by rw [h] at B4; omega) htm5 hABV
  obtain ⟨-, -, d02, -, d03⟩ := dist_of_path_six F.moore col x₀m₀ x₁m₀.symm x₁m₁ x₂m₁.symm x₂m₂
    x₃m₂.symm (hV n01.symm) m01.symm (hV n12.symm) m12.symm (hV n23.symm)
  obtain ⟨-, -, -, -, d05⟩ := dist_of_path_six F.moore col x₀m₀ Am₀.symm AμA BμB.symm Bm₅
    x₅m₅.symm (fun h => by rw [h] at A4; omega) htm0 hABV.symm htm5.symm
    (fun h => by rw [← h] at B4; omega)
  have d4m0 : G.dist (x₄ : V) m₀ = 4 + 1 := dist_eq_five_of_adj F.moore col d41 x₁m₀
  obtain ⟨t₀, m₀t₀, ht₀⟩ := pred_exists F.moore.conn d4m0
  have ht₀N : t₀ ∈ G.neighborFinset m₀ := (SimpleGraph.mem_neighborFinset _ _ _).mpr m₀t₀
  rw [N₀] at ht₀N
  simp only [Finset.mem_insert, Finset.mem_singleton] at ht₀N
  have d40 : G.dist (x₀ : V) x₄ = 4 := by
    rw [SimpleGraph.dist_comm]
    rcases ht₀N with h | h | h
    · rw [← h]
      exact ht₀
    · rw [h] at ht₀
      omega
    · rw [h] at ht₀
      omega
  obtain ⟨α₀, hα4, hα0, -⟩ := exists_unique_lower F.moore col d40
  obtain ⟨α, rfl⟩ : ∃ α : {v : V // col v = false}, (α : V) = α₀ := by
    have h := (even_dist_iff F.moore.conn col (x₀ : V) α₀).mp (by rw [hα0]; decide)
    rw [Bool.coe_iff_coe, x₀.2] at h
    exact ⟨⟨α₀, h.symm⟩, rfl⟩
  obtain ⟨L, x₄L, αL⟩ := exists_adj_adj_of_dist_eq_two F.moore.conn hα4
  have hL3 : L ≠ m₃ := by
    intro h
    rw [h] at αL
    have h1 := hle2 αL x₃m₃
    have h2 := F.moore.conn.dist_triangle (u := (x₀ : V)) (v := (α : V)) (w := (x₃ : V))
    omega
  have hL4 : L ≠ m₄ := by
    intro h
    rw [h] at αL
    have h1 := hle2 αL x₅m₄
    have h2 := F.moore.conn.dist_triangle (u := (x₀ : V)) (v := (α : V)) (w := (x₅ : V))
    omega
  obtain ⟨α', hα', h4α', c4α'⟩ := F.exists_colour h₄ k
  obtain ⟨L', NL', x₄L', α'L', -, z4', -, -, -, -, -⟩ := F.edge h₄ hα' h4α'
  have n3α' : x₃ ≠ α' := fun e =>
    hik (((F.symm h₃ h₄ h34).trans c34).symm.trans (by rw [e]; exact c4α'))
  have n5α' : x₅ ≠ α' := fun e => hjk (c45.symm.trans (by rw [e]; exact c4α'))
  have hm3L' : m₃ ≠ L' := fun h => not_three_far_on_line F.moore col f₃ f₄ (f hα') x₃m₃ x₄m₃
    (by rw [h]; exact α'L') (hV n34) (hV n3α') (hV h4α'.ne)
  have hm4L' : m₄ ≠ L' := fun h => not_three_far_on_line F.moore col f₄ f₅ (f hα') x₄m₄ x₅m₄
    (by rw [h]; exact α'L') (hV n45) (hV h4α'.ne) (hV n5α')
  have hLL' : L = L' := by
    have hN4 : G.neighborFinset (x₄ : V) = {m₃, m₄, L'} :=
      neighborFinset_eq F.moore x₄m₃.symm x₄m₄.symm x₄L'.symm m34 hm3L' hm4L'
    have hLN : L ∈ G.neighborFinset (x₄ : V) := (SimpleGraph.mem_neighborFinset _ _ _).mpr x₄L
    rw [hN4] at hLN
    simp only [Finset.mem_insert, Finset.mem_singleton] at hLN
    rcases hLN with h | h | h
    exacts [absurd h hL3, absurd h hL4, h]
  rw [hLL'] at αL
  have hαN : (α : V) ∈ G.neighborFinset L' := (SimpleGraph.mem_neighborFinset _ _ _).mpr αL.symm
  rw [NL'] at hαN
  simp only [Finset.mem_insert, Finset.mem_singleton] at hαN
  rcases hαN with h | h | h
  ·
    rw [h, SimpleGraph.dist_self] at hα4
    omega
  ·
    obtain rfl : α = α' := Subtype.ext h
    have hSα : α ∈ S := hSadj x₄ hS₄ α hα' h4α'
    have h0α : (pointGraph G col).Adj x₀ α := (hA x₀ α).mpr hα0
    have nα0 : α ≠ x₀ := h0α.ne.symm
    have nα1 : α ≠ x₁ := fun e => by rw [e] at hα4; omega
    have nα2 : α ≠ x₂ := fun e => by rw [e] at hα0; omega
    have hnd6 : [α, x₄, x₃, x₂, x₁, x₀].Nodup := nodup_six h4α'.ne.symm n3α'.symm nα2 nα1 nα0
      n34.symm n24.symm n14.symm n04.symm n23.symm n13.symm n03.symm n12.symm n02.symm n01.symm
    have hX : IsHex G col w ![α, x₄, x₃, x₂, x₁, x₀] := by
      refine ⟨List.nodup_ofFn.mp (by simpa [List.ofFn_succ] using hnd6), fun m => ?_,
        fun m => ?_⟩
      · fin_cases m
        exacts [hα', h₄, h₃, h₂, h₁, h₀]
      · fin_cases m
        exacts [h4α'.symm, h34.symm, h23.symm, h12.symm, h01.symm, h0α]
    obtain ⟨a, b, d, -, -, -, hcol⟩ := hall _ hX (by
      intro m
      fin_cases m
      exacts [hSα, hS₄, hS₃, hS₂, hS₁, hS₀])
    have e0 : c α x₄ = a := hcol 0
    have e3 : c x₂ x₁ = a := hcol 3
    rw [F.symm h₄ hα' h4α', c4α'] at e0
    rw [F.symm h₁ h₂ h12, c12] at e3
    exact hik (e3.trans e0.symm)
  ·
    have hα2 : (pointGraph G col).dist w α = 2 := (hd w α 2).mpr (by rw [h]; exact z4')
    obtain ⟨x₀', hx₀', h00', hz0⟩ := F.exists_edge_of_third h₀ hα2 hα0
    have hc := (F.colour_eq_of_third_eq h₀ hx₀' h00' h₄ hα' h4α' (hz0.trans (Subtype.ext h))).2
    have h01' : x₀' = x₁ := F.unique h₀ hx₀' h₁ h00' h01 (hc.trans (c4α'.trans c01.symm))
    rw [h01'] at hz0
    rw [hz0] at d4A
    omega

end IsFrame

end CFSG.Combinatorics.HexagonPeriodicPropagation
