module

public import CFSG.GH74.Tits83.Octagon
public import CFSG.GH74.Tits83.Section2

public section

namespace CFSG.GH74.Tits83

open scoped commutatorElement Pointwise

universe u

variable {G : Type u} [Group G]

namespace TitsSystem

variable (T : TitsSystem G 8)

theorem t79_lemma1 {k : ℤ} (hk1 : 1 ≤ k) (hk2 : k ≤ 8) {x y : G}
    (hx : x ∈ win T.U k 8) (hy : y ∈ win T.U 1 8)
    (hconj : y * x * y⁻¹ ∈ win T.U 1 (k - 1)) : x = 1 := by
  obtain ⟨z, hz, z', hz', hyz⟩ := T.exists_mul_of_mem_win (a := 1) (c := k - 1) (b := 8)
    (by omega) (by omega) (by omega) hy
  have hz'k : z' ∈ win T.U k 8 := by simpa using hz'
  have hz'x : z' * x * z'⁻¹ ∈ win T.U 1 (k - 1) := by
    have h : z * z' * x * (z * z')⁻¹ ∈ win T.U 1 (k - 1) := by
      simpa [hyz] using hconj
    have hcalc : z' * x * z'⁻¹ = z⁻¹ * (z * z' * x * (z * z')⁻¹) * z := by
      group
    rw [hcalc]
    exact (win T.U 1 (k - 1)).mul_mem
      ((win T.U 1 (k - 1)).mul_mem ((win T.U 1 (k - 1)).inv_mem hz) h) hz
  have hz'x2 : z' * x * z'⁻¹ ∈ win T.U k 8 :=
    (win T.U k 8).mul_mem ((win T.U k 8).mul_mem hz'k hx)
      ((win T.U k 8).inv_mem hz'k)
  have hinter : win T.U 1 (k - 1) ⊓ win T.U k 8 = ⊥ := by
    rw [T.win_inf_win (a := 1) (b := k - 1) (c := k) (d := 8) (by omega)]
    rw [show max 1 k = k by omega, show min (k - 1) 8 = k - 1 by omega]
    exact T.win_eq_bot (by omega)
  have hmem : z' * x * z'⁻¹ ∈ (⊥ : Subgroup G) := by
    rw [← hinter]
    exact ⟨hz'x, hz'x2⟩
  have hz'x1 : z' * x * z'⁻¹ = 1 := by simpa using hmem
  have hx1 : x = z'⁻¹ * (z' * x * z'⁻¹) * z' := by group
  rw [hz'x1] at hx1
  simpa using hx1

private theorem lemma2_eight {i : ℤ} (hi0 : 0 < i) (hi4 : i + 4 < 8) {u v x : G}
    (hu : u ∈ T.U i) (hu1 : u ≠ 1) (hv : v ∈ T.U 8)
    (hx : x ∈ win T.U i 7) (hcomm : u * (v * x) = (v * x) * u) : v = 1 := by
  by_contra hv1
  let v' := T.nu 8 v
  let v'' := T.nu' 8 v
  let m := T.mu 8 v
  have hv'U : v' ∈ T.U 0 := by
    have h := T.nu_mem hv hv1
    have h8 : (8 : ℤ) + ((8 : ℕ) : ℤ) = 0 + 2 * ((8 : ℕ) : ℤ) * 1 := by norm_num
    rw [h8, U_add_two_mul T 0 1] at h
    exact h
  have hv''U : v'' ∈ T.U 0 := by
    have h := T.nu'_mem hv hv1
    have h8 : (8 : ℤ) + ((8 : ℕ) : ℤ) = 0 + 2 * ((8 : ℕ) : ℤ) * 1 := by norm_num
    rw [h8, U_add_two_mul T 0 1] at h
    exact h
  have hm : T.Moves m (fun j => 24 - j) := by
    simpa [m, show (2 * (8 : ℤ) + 8) = 24 by norm_num] using T.moves_mu hv hv1
  let y := m * (v''⁻¹ * x) * m⁻¹
  have hywin : y ∈ win T.U 1 8 := by
    have hmem0 : v''⁻¹ * x ∈ win T.U 0 7 :=
      (win T.U 0 7).mul_mem ((win T.U 0 7).inv_mem (T.U_le_win (by omega) (by omega) hv''U))
        (T.win_mono (by omega) le_rfl hx)
    have hmap := Moves.map_win_refl T hm 0 7
    have hy : y ∈ win T.U (24 - 7) (24 - 0) := by
      rw [← hmap]
      exact ⟨v''⁻¹ * x, hmem0, rfl⟩
    have hy' : y ∈ win T.U (1 + 2 * (8 : ℤ) * 1) (8 + 2 * (8 : ℤ) * 1) := by
      convert hy using 2 <;> norm_num
    exact (T.win_add_two_mul 1 8 1) ▸ hy' 
  have hym : y * m = v' * v * x := by
    simp only [y, m, v', v'', mu]
    group
  have hconj : y * (m * u * m⁻¹) * y⁻¹ = v' * u * v'⁻¹ := by
    have h1 : y * (m * u * m⁻¹) * y⁻¹ = (y * m) * u * (y * m)⁻¹ := by group
    rw [h1, hym]
    have h2 : (v' * v * x) * u * (v' * v * x)⁻¹ =
        v' * ((v * x) * u * (v * x)⁻¹) * v'⁻¹ := by group
    rw [h2]
    have h3 : (v * x) * u * (v * x)⁻¹ = u := by
      rw [← hcomm]
      group
    rw [h3]
  have hmem_mu : m * u * m⁻¹ ∈ T.U (8 - i) := by
    have h := Moves.conj_mem T hm hu
    have h' : m * u * m⁻¹ ∈ T.U ((8 - i) + 2 * (8 : ℤ) * 1) := by
      convert h using 1 <;> ring_nf
    exact (U_add_two_mul T (8 - i) 1) ▸ h' 
  have hmem_win : m * u * m⁻¹ ∈ win T.U (i + 1) 8 :=
    T.U_le_win (by omega) (by omega) hmem_mu
  have hmem_v' : v' * u * v'⁻¹ ∈ win T.U 1 i := by
    have hcomm' : ⁅v', u⁆ ∈ win T.U 1 (i - 1) :=
      T.commutator_mem_win (j := 0) (a := i) (b := i) (by omega) le_rfl (by omega)
        hv'U (T.U_le_win le_rfl le_rfl hu)
    have hform : v' * u * v'⁻¹ = ⁅v', u⁆ * u := by
      simp only [commutatorElement_def]
      group
    rw [hform]
    exact (win T.U 1 i).mul_mem (T.win_mono (by omega) (by omega) hcomm')
      (T.U_le_win (by omega) (by omega) hu)
  have hx1 : m * u * m⁻¹ = 1 :=
    T.t79_lemma1 (k := i + 1) (by omega) (by omega) hmem_win hywin (by
      rw [hconj]
      convert hmem_v' using 1
      ring)
  have hu_eq : u = 1 := by
    have h := congrArg (fun z => m⁻¹ * z * m) hx1
    simpa [mul_assoc] using h
  exact hu1 hu_eq

theorem t79_lemma2 {i j : ℤ} (hij : i + 4 < j) (hji : j < i + 8) {u v x : G}
    (hu : u ∈ T.U i) (hv : v ∈ T.U j) (hx : x ∈ win T.U i (j - 1))
    (hcomm : u * (v * x) = (v * x) * u) : u = 1 ∨ v = 1 := by
  by_cases hu1 : u = 1
  · exact Or.inl hu1
  · right
    let S := T.shift (j - 8)
    have huS : u ∈ S.U (i + 8 - j) := by
      rw [shift_U]
      simpa using hu
    have hvS : v ∈ S.U 8 := by
      rw [shift_U]
      simpa using hv
    have hxS : x ∈ win S.U (i + 8 - j) 7 := by
      rw [win_shift]
      simpa [show i + 8 - j + (j - 8) = i by ring,
        show (7 : ℤ) + (j - 8) = j - 1 by ring] using hx
    have h := lemma2_eight (T := S) (i := i + 8 - j) (by omega) (by omega) huS hu1 hvS hxS
      hcomm
    exact h


private theorem commute_inv_right {a b : G} (h : a * b = b * a) : a * b⁻¹ = b⁻¹ * a := by
  have h1 : b * a⁻¹ = a⁻¹ * b := by
    have := congrArg (fun z => a⁻¹ * z * a⁻¹) h
    simpa [mul_assoc] using this
  have h2 := congrArg Inv.inv h1
  simpa [mul_assoc] using h2

private theorem centralizer_left {i : ℤ} {u y : G} (hu : u ∈ T.U (i + 1)) (hu1 : u ≠ 1)
    (hy : y ∈ win T.U (i + 1) (i + 8)) (hcomm : u * y = y * u) :
    y ∈ win T.U (i + 1) (i + 5) := by
  by_contra hy5
  obtain ⟨P, hP, v, hv, hyv⟩ := T.exists_mul_of_mem_win (a := i + 1) (c := i + 5)
    (b := i + 8) (by omega) (by omega) (by omega) hy
  have hv1 : v ≠ 1 := by
    intro h
    apply hy5
    rw [hyv, h, mul_one]
    exact hP
  have hcomm_inv : u * y⁻¹ = y⁻¹ * u := commute_inv_right hcomm
  by_cases htop : v ∈ win T.U (i + 6) (i + 7)
  · obtain ⟨A, hA, w, hw, hAw⟩ := T.exists_mul_of_mem_win (a := i + 6) (c := i + 6)
      (b := i + 7) (by omega) (by omega) (by omega) htop
    have hA6 : A ∈ T.U (i + 6) := by
      rwa [T.win_self] at hA
    have hw7 : w ∈ T.U (i + 7) := by
      have hw' : w ∈ win T.U (i + 7) (i + 7) := by
        simpa only [show i + 6 + 1 = i + 7 by ring] using hw
      rwa [T.win_self] at hw' 
    by_cases hw1 : w = 1
    · have hinv : y⁻¹ = A⁻¹ * P⁻¹ := by
        rw [hyv, hAw, hw1, mul_one]
        group
      have hc : u * (A⁻¹ * P⁻¹) = (A⁻¹ * P⁻¹) * u := by
        rw [← hinv]
        exact hcomm_inv
      let j₁ : ℤ := i + 6
      have hx₁ : P⁻¹ ∈ win T.U (i + 1) (j₁ - 1) := by
        rw [show j₁ - 1 = i + 5 by dsimp [j₁]; ring]
        exact (win T.U (i + 1) (i + 5)).inv_mem hP
      have h := T.t79_lemma2 (i := i + 1) (j := j₁) (by dsimp [j₁]; omega)
        (by dsimp [j₁]; omega) hu ((T.U (i + 6)).inv_mem hA6) hx₁ hc
      rcases h with hu_eq | hAinv
      · exact hu1 hu_eq
      · have hA1 : A = 1 := inv_eq_one.mp hAinv
        exact hv1 (by rw [hAw, hw1, hA1, mul_one])
    · have hPA : P * A ∈ win T.U (i + 1) (i + 6) :=
        (win T.U (i + 1) (i + 6)).mul_mem
          (T.win_mono le_rfl (by omega) hP) (T.U_le_win (by omega) (by omega) hA6)
      have hinv : y⁻¹ = w⁻¹ * (P * A)⁻¹ := by
        rw [hyv, hAw]
        group
      have hc : u * (w⁻¹ * (P * A)⁻¹) = (w⁻¹ * (P * A)⁻¹) * u := by
        rw [← hinv]
        exact hcomm_inv
      let j₂ : ℤ := i + 7
      have hx₂ : (P * A)⁻¹ ∈ win T.U (i + 1) (j₂ - 1) := by
        rw [show j₂ - 1 = i + 6 by dsimp [j₂]; ring]
        exact (win T.U (i + 1) (i + 6)).inv_mem hPA
      have h := T.t79_lemma2 (i := i + 1) (j := j₂) (by dsimp [j₂]; omega)
        (by dsimp [j₂]; omega) hu ((T.U (i + 7)).inv_mem hw7) hx₂ hc
      rcases h with hu_eq | hwinv
      · exact hu1 hu_eq
      · exact hw1 (inv_eq_one.mp hwinv)
  · have hv6 : v ∈ win T.U (i + 6) (i + 8) := T.win_mono (by omega) le_rfl hv
    obtain ⟨A, hA, w, hw, hAw⟩ := T.exists_mul_of_mem_win (a := i + 6) (c := i + 7)
      (b := i + 8) (by omega) (by omega) (by omega) hv6
    have hw8 : w ∈ T.U (i + 8) := by
      have hw' : w ∈ win T.U (i + 8) (i + 8) := by
        simpa only [show i + 7 + 1 = i + 8 by ring] using hw
      rwa [T.win_self] at hw' 
    have hw1 : w ≠ 1 := by
      intro h
      apply htop
      rw [hAw, h, mul_one]
      exact hA
    have hPA : P * A ∈ win T.U (i + 1) (i + 7) :=
      (win T.U (i + 1) (i + 7)).mul_mem
        (T.win_mono le_rfl (by omega) hP) (T.win_mono (by omega) le_rfl hA)
    have hinv : y⁻¹ = w⁻¹ * (P * A)⁻¹ := by
      rw [hyv, hAw]
      group
    have hc : u * (w⁻¹ * (P * A)⁻¹) = (w⁻¹ * (P * A)⁻¹) * u := by
      rw [← hinv]
      exact hcomm_inv
    let j₃ : ℤ := i + 8
    have hx₃ : (P * A)⁻¹ ∈ win T.U (i + 1) (j₃ - 1) := by
      rw [show j₃ - 1 = i + 7 by dsimp [j₃]; ring]
      exact (win T.U (i + 1) (i + 7)).inv_mem hPA
    have h := T.t79_lemma2 (i := i + 1) (j := j₃) (by dsimp [j₃]; omega)
      (by dsimp [j₃]; omega) hu ((T.U (i + 8)).inv_mem hw8) hx₃ hc
    rcases h with hu_eq | hwinv
    · exact hu1 hu_eq
    · exact hw1 (inv_eq_one.mp hwinv)

private theorem centralizer_right {i : ℤ} {v y : G} (hv : v ∈ T.U (i + 8)) (hv1 : v ≠ 1)
    (hy : y ∈ win T.U (i + 1) (i + 8)) (hcomm : v * y = y * v) :
    y ∈ win T.U (i + 4) (i + 8) := by
  let c : ℤ := 2 * i + 9
  let S := T.refl c
  have hvS : v ∈ S.U (i + 1) := by
    rw [refl_U]
    have h : c - (i + 1) = i + 8 := by
      simp only [c]
      ring
    rw [h]
    exact hv
  have hyS : y ∈ win S.U (i + 1) (i + 8) := by
    rw [win_refl]
    have h1 : c - (i + 8) = i + 1 := by
      simp only [c]
      ring
    have h2 : c - (i + 1) = i + 8 := by
      simp only [c]
      ring
    rw [h1, h2]
    exact hy
  have h := centralizer_left (T := S) (i := i) hvS hv1 hyS hcomm
  rw [win_refl] at h
  have h1 : c - (i + 5) = i + 4 := by
    simp only [c]
    ring
  have h2 : c - (i + 1) = i + 8 := by
    simp only [c]
    ring
  rwa [h1, h2] at h

theorem t79_prop1 {i : ℤ} {u v y : G} (hu : u ∈ T.U (i + 1)) (hu1 : u ≠ 1)
    (hv : v ∈ T.U (i + 8)) (hv1 : v ≠ 1) (hy : y ∈ win T.U (i + 1) (i + 8))
    (huy : u * y = y * u) (hvy : v * y = y * v) :
    ∃ a ∈ T.U (i + 4), ∃ b ∈ T.U (i + 5), y = a * b := by
  have hyl := T.centralizer_left hu hu1 hy huy
  have hyr := T.centralizer_right hv hv1 hy hvy
  have hinter : y ∈ win T.U (i + 4) (i + 5) := by
    have hmem : y ∈ win T.U (i + 1) (i + 5) ⊓ win T.U (i + 4) (i + 8) := ⟨hyl, hyr⟩
    have hEq : win T.U (i + 1) (i + 5) ⊓ win T.U (i + 4) (i + 8) =
        win T.U (i + 4) (i + 5) := by
      rw [T.win_inf_win (a := i + 1) (b := i + 5) (c := i + 4) (d := i + 8) (by omega)]
      rw [show max (i + 1) (i + 4) = i + 4 by omega,
        show min (i + 5) (i + 8) = i + 5 by omega]
    rwa [hEq] at hmem
  obtain ⟨a, ha, b, hb, hab⟩ := T.exists_mul_of_mem_win (a := i + 4) (c := i + 4)
    (b := i + 5) (by omega) (by omega) (by omega) hinter
  have haU : a ∈ T.U (i + 4) := by
    rwa [T.win_self] at ha
  have hbU : b ∈ T.U (i + 5) := by
    have hb' : b ∈ win T.U (i + 5) (i + 5) := by
      simpa only [show i + 4 + 1 = i + 5 by ring] using hb
    rwa [T.win_self] at hb'
  exact ⟨a, haU, b, hbU, hab⟩


private def NoCentralAt (T : TitsSystem G 8) (i : ℤ) : Prop :=
  ∀ x : G, x ≠ 1 →
    x ∈ Subgroup.centralizer (win T.U (i + 1) (i + 8) : Set G) →
    x ∉ T.U (i + 4) ∧ x ∉ T.U (i + 5)

private theorem mem_mid_of_central {i : ℤ} {x : G} (hNo : NoCentralAt T i)
    (hxwin : x ∈ win T.U (i + 1) (i + 8))
    (hxc : x ∈ Subgroup.centralizer (win T.U (i + 1) (i + 8) : Set G)) (hx1 : x ≠ 1) :
    ∃ a ∈ T.U (i + 4), ∃ b ∈ T.U (i + 5), a ≠ 1 ∧ b ≠ 1 ∧ x = a * b := by
  obtain ⟨u, hu, hu1⟩ := Subgroup.exists_mem_ne_one_of_ne_bot (T.ne_bot (i + 1))
  obtain ⟨v, hv, hv1⟩ := Subgroup.exists_mem_ne_one_of_ne_bot (T.ne_bot (i + 8))
  have huy : u * x = x * u :=
    (Subgroup.mem_centralizer_iff.mp hxc) u (T.U_le_win (by omega) (by omega) hu)
  have hvy : v * x = x * v :=
    (Subgroup.mem_centralizer_iff.mp hxc) v (T.U_le_win (by omega) (by omega) hv)
  obtain ⟨a, ha, b, hb, hab⟩ := T.t79_prop1 hu hu1 hv hv1 hxwin huy hvy
  have ha1 : a ≠ 1 := by
    intro h
    have hxU : x ∈ T.U (i + 5) := by
      rw [hab, h, one_mul]
      exact hb
    exact (hNo x hx1 hxc).2 hxU
  have hb1 : b ≠ 1 := by
    intro h
    have hxU : x ∈ T.U (i + 4) := by
      rw [hab, h, mul_one]
      exact ha
    exact (hNo x hx1 hxc).1 hxU
  exact ⟨a, ha, b, hb, ha1, hb1, hab⟩

private theorem noCentralAt_shift {i c : ℤ} {g : G} (hg : T.Moves g (· + c))
    (h : NoCentralAt T i) : NoCentralAt T (i + c) := by
  intro x hx1 hxc
  have hg' : T.Moves g⁻¹ (· - c) := Moves.inv_shift T hg
  let z := g⁻¹ * x * g
  have hz1 : z ≠ 1 := by
    intro hz
    apply hx1
    have hxz : g * z * g⁻¹ = x := by
      simp only [z]
      group
    rw [hz] at hxz
    simpa using hxz.symm
  have hzc : z ∈ Subgroup.centralizer (win T.U (i + 1) (i + 8) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hmap := Moves.map_win_shift T hg (i + 1) (i + 8)
    have hy' : g * y * g⁻¹ ∈ win T.U ((i + c) + 1) ((i + c) + 8) := by
      have hmem : g * y * g⁻¹ ∈ win T.U (i + 1 + c) (i + 8 + c) := by
        rw [← hmap]
        exact ⟨y, hy, rfl⟩
      convert hmem using 2 <;> ring
    have hcomm := (Subgroup.mem_centralizer_iff.mp hxc) (g * y * g⁻¹) hy'
    have := congrArg (fun t => g⁻¹ * t * g) hcomm
    simpa [z, mul_assoc] using this
  have hmem := h z hz1 hzc
  constructor
  · intro hx4
    have hz4 : z ∈ T.U (i + 4) := by
      have h := Moves.conj_mem T hg' hx4
      rw [show ((i + c) + 4) - c = i + 4 by ring] at h
      simpa only [z, inv_inv] using h
    exact hmem.1 hz4
  · intro hx5
    have hz5 : z ∈ T.U (i + 5) := by
      have h := Moves.conj_mem T hg' hx5
      rw [show ((i + c) + 5) - c = i + 5 by ring] at h
      simpa only [z, inv_inv] using h
    exact hmem.2 hz5

private theorem noCentralAt_refl {i c : ℤ} {g : G} (hg : T.Moves g (c - ·))
    (h : NoCentralAt T i) : NoCentralAt T (c - i - 9) := by
  intro x hx1 hxc
  have hg' : T.Moves g⁻¹ (c - ·) := Moves.inv_refl T hg
  let z := g⁻¹ * x * g
  have hz1 : z ≠ 1 := by
    intro hz
    apply hx1
    have hxz : g * z * g⁻¹ = x := by
      simp only [z]
      group
    rw [hz] at hxz
    simpa using hxz.symm
  have hzc : z ∈ Subgroup.centralizer (win T.U (i + 1) (i + 8) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hmap := Moves.map_win_refl T hg (i + 1) (i + 8)
    have hy' : g * y * g⁻¹ ∈ win T.U (c - i - 9 + 1) (c - i - 9 + 8) := by
      have hmem : g * y * g⁻¹ ∈ win T.U (c - (i + 8)) (c - (i + 1)) := by
        rw [← hmap]
        exact ⟨y, hy, rfl⟩
      convert hmem using 2 <;> ring
    have hcomm := (Subgroup.mem_centralizer_iff.mp hxc) (g * y * g⁻¹) hy'
    have := congrArg (fun t => g⁻¹ * t * g) hcomm
    simpa [z, mul_assoc] using this
  have hmem := h z hz1 hzc
  constructor
  · intro hx4
    have hz5 : z ∈ T.U (i + 5) := by
      have h := Moves.conj_mem T hg' hx4
      rw [show c - (c - i - 9 + 4) = i + 5 by ring] at h
      simpa only [z, inv_inv] using h
    exact hmem.2 hz5
  · intro hx5
    have hz4 : z ∈ T.U (i + 4) := by
      have h := Moves.conj_mem T hg' hx5
      rw [show c - (c - i - 9 + 5) = i + 4 by ring] at h
      simpa only [z, inv_inv] using h
    exact hmem.1 hz4


private theorem centralizer_commutator_le {A B : Subgroup G} {y : G}
    (hycent : A ≤ Subgroup.centralizer ({y} : Set G))
    (hBA : B ≤ Subgroup.normalizer (A : Set G)) :
    ⁅B, Subgroup.closure ({y} : Set G)⁆ ≤ Subgroup.centralizer (A : Set G) := by
  have hyA : y ∈ Subgroup.centralizer (A : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact ((Subgroup.mem_centralizer_iff.mp (hycent ha)) y (by simp)).symm
  have hCA : Subgroup.closure ({y} : Set G) ≤ Subgroup.centralizer (A : Set G) := by
    rw [Subgroup.closure_le]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    exact hyA
  have hAC : A ≤ Subgroup.centralizer (Subgroup.closure ({y} : Set G) : Set G) :=
    (Subgroup.le_centralizer_iff (H := A) (K := Subgroup.closure ({y} : Set G))).mpr hCA
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
  refine Subgroup.commutator_commutator_eq_bot_of_rotate
    (H₁ := B) (H₂ := Subgroup.closure ({y} : Set G)) (H₃ := A) ?_ ?_
  · have h : ⁅Subgroup.closure ({y} : Set G), A⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hCA
    rw [h, Subgroup.commutator_bot_left]
  · have hAB : ⁅A, B⁆ ≤ A := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.le_normalizer_iff_commutator_le_right.mp hBA
    have h : ⁅A, B⁆ ≤ Subgroup.centralizer (Subgroup.closure ({y} : Set G) : Set G) :=
      le_trans hAB hAC
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr h

private theorem centralizer_singleton_of_mem {A : Subgroup G} {y : G}
    (hy : y ∈ Subgroup.centralizer (A : Set G)) :
    A ≤ Subgroup.centralizer ({y} : Set G) := by
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  rw [Set.mem_singleton_iff] at hz
  subst z
  exact ((Subgroup.mem_centralizer_iff.mp hy) a ha).symm


private theorem commutator_mem_centralizer_win17 {Y u : G}
    (hY : win T.U 1 7 ≤ Subgroup.centralizer ({Y} : Set G)) (hu : u ∈ T.U 0) :
    ⁅u, Y⁆ ∈ Subgroup.centralizer (win T.U 1 7 : Set G) := by
  have hU0norm : T.U 0 ≤ Subgroup.normalizer (win T.U 1 7 : Set G) := by
    have h := (T.le_normalizer_win (a := 1) (b := 7) (by norm_num)).1
    simpa using h
  have hle := centralizer_commutator_le (A := win T.U 1 7) (B := T.U 0) (y := Y) hY hU0norm
  exact hle (Subgroup.commutator_mem_commutator hu (Subgroup.subset_closure (by simp)))

private theorem eq_one_of_mem_win_central {z : G} (hz : z ∈ win T.U 1 2)
    (hzc : z ∈ Subgroup.centralizer (win T.U 1 7 : Set G)) : z = 1 := by
  let R := T.refl 8
  have hzR : z ∈ win R.U 6 7 := by
    rw [win_refl]
    convert hz using 2 <;> ring
  obtain ⟨u, hu, hu1⟩ := Subgroup.exists_mem_ne_one_of_ne_bot (R.ne_bot 1)
  have huS7 : u ∈ T.U 7 := by
    rw [refl_U] at hu
    simpa using hu
  have hzu : u * z = z * u :=
    (Subgroup.mem_centralizer_iff.mp hzc) u (T.U_le_win (by norm_num) (by norm_num) huS7)
  obtain ⟨X, hX, W, hW, hzXW⟩ := R.exists_mul_of_mem_win (a := 6) (c := 6) (b := 7)
    (by norm_num) (by norm_num) (by norm_num) hzR
  have hX6 : X ∈ R.U 6 := by
    rwa [R.win_self] at hX
  have hW7 : W ∈ R.U 7 := by
    have hW' : W ∈ win R.U (7 : ℤ) 7 := by
      convert hW using 2 <;> norm_num
    rwa [R.win_self] at hW'
  by_cases hW1 : W = 1
  · have hz6 : z ∈ R.U 6 := by
      rw [hzXW, hW1, mul_one]
      exact hX6
    have hcommz : u * (z⁻¹ * 1) = (z⁻¹ * 1) * u := by
      simpa using commute_inv_right hzu
    have h := R.t79_lemma2 (i := 1) (j := 6) (by norm_num) (by norm_num) hu
      ((R.U 6).inv_mem hz6) ((win R.U 1 5).one_mem) hcommz
    rcases h with hu_eq | hzinv
    · exfalso
      exact hu1 hu_eq
    · exact inv_eq_one.mp hzinv
  · have hzinv : z⁻¹ = W⁻¹ * X⁻¹ := by
      rw [hzXW]
      group
    have hcommz : u * (W⁻¹ * X⁻¹) = (W⁻¹ * X⁻¹) * u := by
      rw [← hzinv]
      exact commute_inv_right hzu
    have hxinv : X⁻¹ ∈ win R.U 1 6 :=
      (win R.U 1 6).inv_mem (R.U_le_win (by norm_num) (by norm_num) hX6)
    have h := R.t79_lemma2 (i := 1) (j := 7) (by norm_num) (by norm_num) hu
      ((R.U 7).inv_mem hW7) hxinv hcommz
    rcases h with hu_eq | hWinv
    · exfalso
      exact hu1 hu_eq
    · exfalso
      exact hW1 (inv_eq_one.mp hWinv)


private theorem commutator_central_of_mid (S : TitsSystem G 8) (hNo1 : NoCentralAt S (-1))
    {u v a b : G} (hu : u ∈ S.U 0) (hv : v ∈ S.U 1) (ha : a ∈ S.U 4) (hb : b ∈ S.U 5)
    (hB : a * b ∈ Subgroup.centralizer (win S.U 1 8 : Set G))
    (hu1 : u ≠ 1) (hb1 : b ≠ 1) :
    ⁅u * v, a * b⁆ ∈ win S.U 0 7 ∧
      ⁅u * v, a * b⁆ ∈ Subgroup.centralizer (win S.U 0 7 : Set G) ∧
      ⁅u * v, a * b⁆ ≠ 1 := by
  have hcomm_v : v * (a * b) = (a * b) * v :=
    (Subgroup.mem_centralizer_iff.mp hB) v (S.U_le_win (by norm_num) (by norm_num) hv)
  have hy_eq : ⁅u * v, a * b⁆ = ⁅u, a * b⁆ := by
    rw [commutatorElement_def]
    have h1 : u * v * (a * b) = u * (a * b) * v := by
      calc
        u * v * (a * b) = u * (v * (a * b)) := by group
        _ = u * ((a * b) * v) := by rw [hcomm_v]
        _ = u * (a * b) * v := by group
    calc
      u * v * (a * b) * (u * v)⁻¹ * (a * b)⁻¹ =
          u * (a * b) * v * (v⁻¹ * u⁻¹) * (a * b)⁻¹ := by rw [h1]; group
      _ = u * (a * b) * u⁻¹ * (a * b)⁻¹ := by group
  have hua : ⁅u, a⁆ ∈ win S.U 1 3 :=
    S.commutator_mem_win (j := 0) (a := 4) (b := 4) (by norm_num) le_rfl (by norm_num)
      hu (S.U_le_win le_rfl le_rfl ha)
  have hub : ⁅u, b⁆ ∈ win S.U 1 4 :=
    S.commutator_mem_win (j := 0) (a := 5) (b := 5) (by norm_num) le_rfl (by norm_num)
      hu (S.U_le_win le_rfl le_rfl hb)
  have hy14 : ⁅u * v, a * b⁆ ∈ win S.U 1 4 := by
    have hform : ⁅u, a * b⁆ = ⁅u, a⁆ * (a * ⁅u, b⁆ * a⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [hy_eq, hform]
    have hsecond : a * ⁅u, b⁆ * a⁻¹ ∈ win S.U 1 4 := by
      refine (win S.U 1 4).mul_mem (x := (a * ⁅u, b⁆)) (y := (a⁻¹)) ?_ ?_
      · exact (win S.U 1 4).mul_mem
          (S.U_le_win (a := 1) (b := 4) (k := 4) (by norm_num) (by norm_num) ha) hub
      · exact (win S.U 1 4).inv_mem
          (S.U_le_win (a := 1) (b := 4) (k := 4) (by norm_num) (by norm_num) ha)
    exact (win S.U 1 4).mul_mem
      (S.win_mono (a := 1) (b := 3) (c := 1) (d := 4) (by norm_num) (by norm_num) hua)
      hsecond
  have hywin07 : ⁅u * v, a * b⁆ ∈ win S.U 0 7 :=
    S.win_mono (a := 1) (b := 4) (c := 0) (d := 7) (by norm_num) (by norm_num) hy14
  have hB7 : a * b ∈ Subgroup.centralizer (win S.U 1 7 : Set G) :=
    Subgroup.centralizer_le
      (S.win_mono (a := 1) (b := 7) (c := 1) (d := 8) (by norm_num) (by norm_num)) hB
  have hx'le : win S.U 1 7 ≤ Subgroup.centralizer ({a * b} : Set G) :=
    centralizer_singleton_of_mem hB7
  have hU0norm : S.U 0 ≤ Subgroup.normalizer (win S.U 1 7 : Set G) := by
    have h := (S.le_normalizer_win (a := 1) (b := 7) (by norm_num)).1
    simpa using h
  have hcomm_le := centralizer_commutator_le (A := win S.U 1 7) (B := S.U 0)
    (y := a * b) hx'le hU0norm
  have hy_mem : ⁅u, a * b⁆ ∈ ⁅S.U 0, Subgroup.closure ({a * b} : Set G)⁆ :=
    Subgroup.commutator_mem_commutator hu (Subgroup.subset_closure (by simp))
  have hy_central_W1 : ⁅u * v, a * b⁆ ∈
      Subgroup.centralizer (win S.U 1 7 : Set G) := by
    rw [hy_eq]
    exact hcomm_le hy_mem
  have hyW1le : win S.U 1 7 ≤ Subgroup.centralizer ({⁅u * v, a * b⁆} : Set G) :=
    centralizer_singleton_of_mem hy_central_W1
  have hy1_data : ∀ u1 : G, u1 ∈ S.U 0 →
      ⁅u1, ⁅u * v, a * b⁆⁆ ∈ win S.U 1 3 ∧
        ⁅u1, ⁅u * v, a * b⁆⁆ ∈
          Subgroup.centralizer (win S.U 1 7 : Set G) := by
    intro u1 hu1
    refine ⟨?_, ?_⟩
    · exact S.commutator_mem_win (j := 0) (a := 1) (b := 4) (by norm_num) (by norm_num)
        (by norm_num) hu1 hy14
    · exact commutator_mem_centralizer_win17 (T := S) hyW1le hu1
  have hz_eq_one : ∀ u2 u1 : G, u2 ∈ S.U 0 → u1 ∈ S.U 0 →
      ⁅u2, ⁅u1, ⁅u * v, a * b⁆⁆⁆ = 1 := by
    intro u2 u1 hu2 hu1
    obtain ⟨hy1win, hy1cent⟩ := hy1_data u1 hu1
    have hy1le : win S.U 1 7 ≤
        Subgroup.centralizer ({⁅u1, ⁅u * v, a * b⁆⁆} : Set G) :=
      centralizer_singleton_of_mem hy1cent
    have hzwin : ⁅u2, ⁅u1, ⁅u * v, a * b⁆⁆⁆ ∈ win S.U 1 2 :=
      S.commutator_mem_win (j := 0) (a := 1) (b := 3) (by norm_num) (by norm_num)
        (by norm_num) hu2 hy1win
    have hzcent : ⁅u2, ⁅u1, ⁅u * v, a * b⁆⁆⁆ ∈
        Subgroup.centralizer (win S.U 1 7 : Set G) :=
      commutator_mem_centralizer_win17 (T := S) hy1le hu2
    exact eq_one_of_mem_win_central (T := S) hzwin hzcent
  have hy1_central0 : ∀ u1 : G, u1 ∈ S.U 0 →
      ⁅u1, ⁅u * v, a * b⁆⁆ ∈ Subgroup.centralizer (win S.U 0 7 : Set G) := by
    intro u1 hu1
    obtain ⟨hy1win, hy1cent⟩ := hy1_data u1 hu1
    rw [S.mem_centralizer_win_iff]
    intro k hk0 hk7 w hw
    by_cases hk1 : 1 ≤ k
    · exact (Subgroup.mem_centralizer_iff.mp hy1cent) w (S.U_le_win hk1 hk7 hw)
    · have hk : k = 0 := by omega
      subst hk
      exact commutatorElement_eq_one_iff_mul_comm.mp (hz_eq_one w u1 hw hu1)
  have hy1_eq_one : ∀ u1 : G, u1 ∈ S.U 0 → ⁅u1, ⁅u * v, a * b⁆⁆ = 1 := by
    intro u1 hu1
    by_contra hy1ne
    obtain ⟨hy1win, hy1cent⟩ := hy1_data u1 hu1
    have hy1win07 : ⁅u1, ⁅u * v, a * b⁆⁆ ∈ win S.U 0 7 :=
      S.win_mono (by norm_num) (by norm_num) hy1win
    have hmid := mem_mid_of_central (T := S) (i := -1) hNo1 hy1win07
      (hy1_central0 u1 hu1) hy1ne
    obtain ⟨a3, ha3, b4, hb4, ha31, hb41, hy1ab⟩ := hmid
    have ha3win : a3 ∈ win S.U 1 3 := S.U_le_win (by norm_num) (by norm_num) ha3
    have hb4win : b4 ∈ win S.U 4 4 := S.U_le_win le_rfl le_rfl hb4
    have huniq := S.eq_of_mul_eq_mul (a := 1) (c := 3) (b := 4) (by norm_num)
      (by norm_num) (by norm_num) ha3win hy1win hb4win
      ((win S.U 4 4).one_mem) (by rw [hy1ab, mul_one])
    exact hb41 huniq.2
  have hy_central0 : ⁅u * v, a * b⁆ ∈
      Subgroup.centralizer (win S.U 0 7 : Set G) := by
    rw [S.mem_centralizer_win_iff]
    intro k hk0 hk7 w hw
    by_cases hk1 : 1 ≤ k
    · exact (Subgroup.mem_centralizer_iff.mp hy_central_W1) w (S.U_le_win hk1 hk7 hw)
    · have hk : k = 0 := by omega
      subst hk
      exact commutatorElement_eq_one_iff_mul_comm.mp (hy1_eq_one w hw)
  have hy_ne : ⁅u * v, a * b⁆ ≠ 1 := by
    intro hy1
    have hua_comm : u * (a * b) = (a * b) * u := by
      have h : ⁅u, a * b⁆ = 1 := by
        rwa [← hy_eq]
      exact commutatorElement_eq_one_iff_mul_comm.mp h
    have hab_comm : a * b = b * a := comm_add_one (T := S) ha hb
    have hcomm2 : u * (b * a) = (b * a) * u := by
      rw [← hab_comm]
      exact hua_comm
    have h := S.t79_lemma2 (i := 0) (j := 5) (by norm_num) (by norm_num) hu hb
      (S.U_le_win (by norm_num) (by norm_num) ha) hcomm2
    rcases h with hu_eq | hb_eq
    · exact hu1 hu_eq
    · exact hb1 hb_eq
  exact ⟨hywin07, hy_central0, hy_ne⟩


private theorem noCentralAt_shift_system {i : ℤ} (h : NoCentralAt T (i - 1)) :
    NoCentralAt (T.shift i) (-1) := by
  simpa [NoCentralAt, shift_U, win_shift, add_comm, add_left_comm, add_assoc,
    show i - 1 + 1 = i by ring, show i - 1 + 8 = i + 7 by ring,
    show i - 1 + 4 = i + 3 by ring, show i - 1 + 5 = i + 4 by ring] using h

private theorem noCentralAt_refl_system {i : ℤ} (h : NoCentralAt T (i - 3)) :
    NoCentralAt ((T.shift i).refl 5) (-1) := by
  intro x hx1 hxc
  have hxcT : x ∈ Subgroup.centralizer (win T.U (i - 2) (i + 5) : Set G) := by
    rw [win_refl] at hxc
    rw [win_shift] at hxc
    convert hxc using 2 <;> ring
  have hres := h x hx1 (by
    convert hxcT using 2 <;> ring)
  constructor
  · intro hx3
    apply hres.2
    rw [refl_U] at hx3
    rw [shift_U] at hx3
    convert hx3 using 1 <;> ring
  · intro hx4
    apply hres.1
    rw [refl_U] at hx4
    rw [shift_U] at hx4
    convert hx4 using 1 <;> ring



private theorem prop2_x_decomp {i : ℤ} (hNo0 : NoCentralAt T i)
    (hNoM4 : NoCentralAt T (i - 4)) {z0 : G}
    (hz0win : z0 ∈ win T.U (i + 1) (i + 8))
    (hz0c : z0 ∈ Subgroup.centralizer (win T.U (i + 1) (i + 8) : Set G)) (hz01 : z0 ≠ 1) :
    ∃ x u v a b : G, x ≠ 1 ∧ x ∈ win T.U (i - 3) (i + 4) ∧
      x ∈ Subgroup.centralizer (win T.U (i - 3) (i + 4) : Set G) ∧
      u ∈ T.U i ∧ v ∈ T.U (i + 1) ∧ a ∈ T.U (i + 4) ∧ b ∈ T.U (i + 5) ∧
      u ≠ 1 ∧ b ≠ 1 ∧ x = u * v ∧ z0 = a * b := by
  obtain ⟨g, hg4⟩ := T.exists_moves_shift (-2)
  have hg4' : T.Moves g (· + (-4)) := by simpa using hg4
  let x := g * z0 * g⁻¹
  have hx1 : x ≠ 1 := by
    intro hx
    apply hz01
    have hxz : g * z0 * g⁻¹ = 1 := hx
    have := congrArg (fun t => g⁻¹ * t * g) hxz
    simpa [mul_assoc] using this
  have hxwin : x ∈ win T.U (i - 3) (i + 4) := by
    have hmap := Moves.map_win_shift T hg4' (i + 1) (i + 8)
    have hmem : x ∈ win T.U ((i + 1) + (-4)) ((i + 8) + (-4)) := by
      rw [← hmap]
      exact ⟨z0, hz0win, rfl⟩
    convert hmem using 2 <;> ring
  have hxc_x : x ∈ Subgroup.centralizer (win T.U (i - 3) (i + 4) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hg4inv : T.Moves g⁻¹ (· + 4) := Moves.inv_shift T hg4'
    have hmap := Moves.map_win_shift T hg4inv (i - 3) (i + 4)
    have hy' : g⁻¹ * y * g ∈ win T.U (i + 1) (i + 8) := by
      have hmem : g⁻¹ * y * g ∈ win T.U ((i - 3) + 4) ((i + 4) + 4) := by
        rw [← hmap]
        exact ⟨y, hy, by simp [MulAut.conj_apply]⟩
      convert hmem using 2 <;> ring
    have hcomm := (Subgroup.mem_centralizer_iff.mp hz0c) (g⁻¹ * y * g) hy'
    have := congrArg (fun t => g * t * g⁻¹) hcomm
    simpa [x, mul_assoc] using this
  have hxwin4 : x ∈ win T.U ((i - 4) + 1) ((i - 4) + 8) := by
    convert hxwin using 2 <;> ring
  have hxc4 : x ∈ Subgroup.centralizer (win T.U ((i - 4) + 1) ((i - 4) + 8) : Set G) := by
    convert hxc_x using 2 <;> ring
  obtain ⟨u, hu0, v, hv0, hu1, hv1, hxuv⟩ :=
    mem_mid_of_central (T := T) (i := i - 4) hNoM4 hxwin4 hxc4 hx1
  have hu : u ∈ T.U i := by
    convert hu0 using 1 <;> ring
  have hv : v ∈ T.U (i + 1) := by
    convert hv0 using 1 <;> ring
  obtain ⟨a, ha, b, hb, ha1, hb1, hz0ab⟩ :=
    mem_mid_of_central (T := T) (i := i) hNo0 hz0win hz0c hz01
  exact ⟨x, u, v, a, b, hx1, hxwin, hxc_x, hu, hv, ha, hb, hu1, hb1, hxuv, hz0ab⟩

theorem t79_prop2 (T : TitsSystem G 8) (i : ℤ)
    (hZ : Subgroup.centralizer (win T.U (i + 1) (i + 8) : Set G) ⊓
      win T.U (i + 1) (i + 8) ≠ ⊥) :
    ∃ k : ℤ, (k = i + 4 ∨ k = i + 5) ∧ ∃ x ∈ T.U k, x ≠ 1 ∧
      x ∈ Subgroup.centralizer (win T.U (i + 1) (i + 8) : Set G) := by
  by_contra hno
  have hNo0 : NoCentralAt T i := by
    intro x hx1 hxc
    constructor
    · intro hx4
      exact hno ⟨i + 4, Or.inl rfl, x, hx4, hx1, hxc⟩
    · intro hx5
      exact hno ⟨i + 5, Or.inr rfl, x, hx5, hx1, hxc⟩
  have hNoM4 : NoCentralAt T (i - 4) := by
    obtain ⟨g, hg⟩ := T.exists_moves_shift (-2)
    have hg' : T.Moves g (· + (-4)) := by simpa using hg
    have h := noCentralAt_shift (T := T) hg' hNo0
    rwa [show i + (-4) = i - 4 by ring] at h
  have hNoM1 : NoCentralAt T (i - 1) := by
    obtain ⟨g, hg⟩ := T.exists_moves_refl_of_even (2 * i + 8) ⟨i + 4, by ring⟩
      (⟨4, by norm_num⟩ : Even (8 : ℤ))
    have h := noCentralAt_refl (T := T) hg hNo0
    rwa [show 2 * i + 8 - i - 9 = i - 1 by ring] at h
  have hNoM3 : NoCentralAt T (i - 3) := by
    obtain ⟨g, hg⟩ := T.exists_moves_refl_of_even (2 * i + 6) ⟨i + 3, by ring⟩
      (⟨4, by norm_num⟩ : Even (8 : ℤ))
    have h := noCentralAt_refl (T := T) hg hNo0
    rwa [show 2 * i + 6 - i - 9 = i - 3 by ring] at h
  obtain ⟨z0, hz0inf, hz01⟩ := Subgroup.exists_mem_ne_one_of_ne_bot hZ
  have hz0win : z0 ∈ win T.U (i + 1) (i + 8) := hz0inf.2
  have hz0c : z0 ∈ Subgroup.centralizer (win T.U (i + 1) (i + 8) : Set G) := hz0inf.1
  obtain ⟨x, u, v, a, b, hx1, hxwin, hxc_x, hu, hv, ha, hb, hu1, hb1, hxuv, hz0ab⟩ :=
    prop2_x_decomp (T := T) hNo0 hNoM4 hz0win hz0c hz01

  let S1 := T.shift i
  have hNoS1 : NoCentralAt S1 (-1) := noCentralAt_shift_system (T := T) hNoM1
  have huS1 : u ∈ S1.U 0 := by
    rw [shift_U]
    simpa using hu
  have hvS1 : v ∈ S1.U 1 := by
    rw [shift_U]
    simpa [add_comm] using hv
  have haS1 : a ∈ S1.U 4 := by
    rw [shift_U]
    simpa [add_comm] using ha
  have hbS1 : b ∈ S1.U 5 := by
    rw [shift_U]
    simpa [add_comm] using hb
  have hBS1 : a * b ∈ Subgroup.centralizer (win S1.U 1 8 : Set G) := by
    rw [win_shift]
    rw [← hz0ab]
    convert hz0c using 2 <;> ring
  have hyS1 := commutator_central_of_mid (S := S1) hNoS1 huS1 hvS1 haS1 hbS1 hBS1 hu1 hb1
  have hywin : ⁅u * v, a * b⁆ ∈ win T.U i (i + 7) := by
    have h := hyS1.1
    rw [win_shift] at h
    convert h using 2 <;> ring
  have hycent : ⁅u * v, a * b⁆ ∈
      Subgroup.centralizer (win T.U i (i + 7) : Set G) := by
    have h := hyS1.2.1
    rw [win_shift] at h
    convert h using 2 <;> ring
  let S2 := (T.shift i).refl 5
  have hNoS2 : NoCentralAt S2 (-1) := noCentralAt_refl_system (T := T) hNoM3
  have hbS2 : b ∈ S2.U 0 := by
    rw [refl_U, shift_U]
    convert hb using 1 <;> ring
  have haS2 : a ∈ S2.U 1 := by
    rw [refl_U, shift_U]
    convert ha using 1 <;> ring
  have hvS2 : v ∈ S2.U 4 := by
    rw [refl_U, shift_U]
    convert hv using 1 <;> ring
  have huS2 : u ∈ S2.U 5 := by
    rw [refl_U, shift_U]
    convert hu using 1 <;> ring
  have hb4plus : b ∈ T.U (i + 4 + 1) := by
    convert hb using 1 <;> ring
  have hv1plus : v ∈ T.U (i + 1) := by
    convert hv using 1 <;> ring
  have hcomm_ab : a * b = b * a := comm_add_one (T := T) (j := i + 4) ha hb4plus
  have hcomm_uv : u * v = v * u := comm_add_one (T := T) (j := i) hu hv1plus
  have hAS2 : b * a ∈ Subgroup.centralizer (win S2.U (-3) 4 : Set G) := by
    rw [win_refl, win_shift]
    rw [← hcomm_ab, ← hz0ab]
    convert hz0c using 2 <;> ring
  have hBS2 : v * u ∈ Subgroup.centralizer (win S2.U 1 8 : Set G) := by
    rw [win_refl, win_shift]
    rw [← hcomm_uv]
    rw [← hxuv]
    convert hxc_x using 2 <;> ring
  have hy2S2 := commutator_central_of_mid (S := S2) hNoS2 hbS2 haS2 hvS2 huS2 hBS2 hb1 hu1
  have hy2win : ⁅b * a, v * u⁆ ∈ win T.U (i - 2) (i + 5) := by
    have h := hy2S2.1
    rw [win_refl, win_shift] at h
    convert h using 2 <;> ring
  have hy2cent : ⁅b * a, v * u⁆ ∈
      Subgroup.centralizer (win T.U (i - 2) (i + 5) : Set G) := by
    have h := hy2S2.2.1
    rw [win_refl, win_shift] at h
    convert h using 2 <;> ring
  have hy2ne : ⁅b * a, v * u⁆ ≠ 1 := hy2S2.2.2
  have hy1win : ⁅u * v, a * b⁆ ∈ win T.U ((i - 1) + 1) ((i - 1) + 8) := by
    convert hywin using 2 <;> ring
  have hy1cent : ⁅u * v, a * b⁆ ∈
      Subgroup.centralizer (win T.U ((i - 1) + 1) ((i - 1) + 8) : Set G) := by
    convert hycent using 2 <;> ring
  obtain ⟨a3, ha3, b4, hb4, ha31, hb41, hyab⟩ :=
    mem_mid_of_central (T := T) (i := i - 1) hNoM1 hy1win hy1cent hyS1.2.2
  have ha3' : a3 ∈ T.U (i + 3) := by
    convert ha3 using 1 <;> ring
  have hb4' : b4 ∈ T.U (i + 4) := by
    convert hb4 using 1 <;> ring
  have hy2win' : ⁅b * a, v * u⁆ ∈ win T.U ((i - 3) + 1) ((i - 3) + 8) := by
    convert hy2win using 2 <;> ring
  have hy2cent' : ⁅b * a, v * u⁆ ∈
      Subgroup.centralizer (win T.U ((i - 3) + 1) ((i - 3) + 8) : Set G) := by
    convert hy2cent using 2 <;> ring
  obtain ⟨c1, hc1, d2, hd2, hc11, hd21, hy2cd⟩ :=
    mem_mid_of_central (T := T) (i := i - 3) hNoM3 hy2win' hy2cent' hy2ne
  have hc1' : c1 ∈ T.U (i + 1) := by
    convert hc1 using 1 <;> ring
  have hd2' : d2 ∈ T.U (i + 2) := by
    convert hd2 using 1 <;> ring
  have hy2_eq : ⁅b * a, v * u⁆ = (⁅u * v, a * b⁆)⁻¹ := by
    conv_lhs => rw [← hcomm_ab, ← hcomm_uv]
    exact (commutatorElement_inv (u * v) (a * b)).symm
  have hy2_win12 : ⁅b * a, v * u⁆ ∈ win T.U (i + 1) (i + 2) := by
    rw [hy2cd]
    exact (win T.U (i + 1) (i + 2)).mul_mem
      (T.U_le_win (a := i + 1) (b := i + 2) (k := i + 1) le_rfl (by omega) hc1')
      (T.U_le_win (a := i + 1) (b := i + 2) (k := i + 2) (by omega) le_rfl hd2')
  have hy_win34 : ⁅u * v, a * b⁆ ∈ win T.U (i + 3) (i + 4) := by
    rw [hyab]
    exact (win T.U (i + 3) (i + 4)).mul_mem
      (T.U_le_win (a := i + 3) (b := i + 4) (k := i + 3) le_rfl (by omega) ha3')
      (T.U_le_win (a := i + 3) (b := i + 4) (k := i + 4) (by omega) le_rfl hb4')
  have hy2_win34 : ⁅b * a, v * u⁆ ∈ win T.U (i + 3) (i + 4) := by
    rw [hy2_eq]
    exact (win T.U (i + 3) (i + 4)).inv_mem hy_win34
  have hbot : win T.U (i + 1) (i + 2) ⊓ win T.U (i + 3) (i + 4) = ⊥ := by
    rw [T.win_inf_win (a := i + 1) (b := i + 2) (c := i + 3) (d := i + 4) (by omega)]
    rw [show max (i + 1) (i + 3) = i + 3 by omega,
      show min (i + 2) (i + 4) = i + 2 by omega]
    exact T.win_eq_bot (by omega)
  have hmem : ⁅b * a, v * u⁆ ∈ (⊥ : Subgroup G) := by
    rw [← hbot]
    exact ⟨hy2_win12, hy2_win34⟩
  exact hy2ne (by simpa using hmem)


theorem exists_central_mid (T : TitsSystem G 8)
    (hZ : Subgroup.centralizer (win T.U 1 8 : Set G) ⊓ win T.U 1 8 ≠ ⊥) :
    ∃ k : ℤ, (k = 4 ∨ k = 5) ∧ ∃ x ∈ T.U k, x ≠ 1 ∧
      x ∈ Subgroup.centralizer (win T.U 1 8 : Set G) := by
  simpa using T.t79_prop2 0 hZ

theorem normalized_of_central (T : TitsSystem G 8) {x : G} (hx : x ∈ T.U 4) (hx1 : x ≠ 1)
    (hc : x ∈ Subgroup.centralizer (win T.U 1 8 : Set G)) : T.Normalized := by
  rw [Normalized]
  have hcent0 : x ∈ Subgroup.centralizer (win T.U 0 8 : Set G) := by
    rw [T.mem_centralizer_win_iff]
    intro k hk0 hk8 y hy
    by_cases hk1 : 1 ≤ k
    · exact (Subgroup.mem_centralizer_iff.mp hc) y (T.U_le_win hk1 hk8 hy)
    · have hk : k = 0 := by omega
      subst hk
      by_cases hy1 : y = 1
      · subst hy1
        simp
      · have hu_mem : T.nu' 0 y ∈ T.U ((0 : ℤ) + 8) := T.nu'_mem hy hy1
        have hu8 : T.nu' 0 y ∈ T.U 8 := by
          convert hu_mem using 1 <;> ring
        have hu1 : T.nu' 0 y ≠ 1 := T.nu'_ne_one (by norm_num) hy hy1
        have hux : T.nu' 0 y * x = x * T.nu' 0 y :=
          (Subgroup.mem_centralizer_iff.mp hc) _ (T.U_le_win (by norm_num) (by norm_num) hu8)
        have hm := (T.lemma212_ii' (by norm_num) (i := 8) (j := 4) (by norm_num) hu8 hu1 hx
          hux).1
        have hnu : T.nu 8 (T.nu' 0 y) = y := by
          have h := (T.mu_nu' (by norm_num) (i := 0) hy hy1).2
          convert h using 2 <;> ring
        rw [hnu] at hm
        exact hm.symm
  have hmem : x ∈ Subgroup.centralizer (win T.U 0 8 : Set G) ⊓ T.U 4 := ⟨hcent0, hx⟩
  intro hbot
  rw [hbot] at hmem
  exact hx1 (by simpa using hmem)

theorem normalized_or (T : TitsSystem G 8)
    (hZ : Subgroup.centralizer (win T.U 1 8 : Set G) ⊓ win T.U 1 8 ≠ ⊥) :
    T.Normalized ∨ (T.refl 9).Normalized := by
  obtain ⟨k, hk, x, hxU, hx1, hxc⟩ := T.exists_central_mid hZ
  rcases hk with rfl | rfl
  · exact Or.inl (T.normalized_of_central hxU hx1 hxc)
  · right
    have hxS : x ∈ (T.refl 9).U 4 := by
      rw [refl_U]
      simpa using hxU
    have hcS : x ∈ Subgroup.centralizer (win (T.refl 9).U 1 8 : Set G) := by
      rw [win_refl]
      simpa using hxc
    exact (T.refl 9).normalized_of_central hxS hx1 hcS

end TitsSystem

end CFSG.GH74.Tits83
