module

public import CFSG.GH74.Tits83.Section4A
public import Mathlib.Algebra.Field.IsField
public import Mathlib.Algebra.Ring.MinimalAxioms

public section

namespace CFSG.GH74.Tits83

open CFSG.GH74.BNPair

open scoped commutatorElement Pointwise

universe u

namespace OctFrame

variable {G : Type u} [Group G] {T : TitsSystem G 8}

section Basic

variable (F : OctFrame T)

@[ext] structure K (F : OctFrame T) : Type u where
  val : G
  mem : val ∈ T.U 1

theorem exists_mul (x y : F.K) : ∃ z : F.K, F.xp 4 z.val = ⁅x.val, F.xp 6 y.val⁆ := by
  have hmem : ⁅x.val, F.xp 6 y.val⁆ ∈ T.Uprime 4 :=
    T.lemma33_i F.hT x.mem (F.xp_mem (by decide : Even (6 : ℤ)) y.mem)
  obtain ⟨z, hzU, hz⟩ := (F.xp_bijOn (j := 4) (by decide : Even (4 : ℤ))).surjOn hmem
  exact ⟨⟨z, hzU⟩, hz⟩

noncomputable def mulK (x y : F.K) : F.K := Classical.choose (F.exists_mul x y)

theorem xp_four_mulK (x y : F.K) :
    F.xp 4 (F.mulK x y).val = ⁅x.val, F.xp 6 y.val⁆ :=
  Classical.choose_spec (F.exists_mul x y)

@[expose] noncomputable def alpha (x : F.K) : G := T.mu 1 x.val * F.a

theorem moves_alpha {x : F.K} (hx : x.val ≠ 1) : T.Moves (F.alpha x) (fun j => j) := by
  have hm : T.Moves (T.mu 1 x.val) (fun j => 10 - j) := by
    convert T.moves_mu (i := 1) (n := 8) x.mem hx using 2
    ring
  have hmul : T.Moves (F.alpha x) ((fun j => 10 - j) ∘ (fun j => 10 - j)) :=
    TitsSystem.Moves.mul T hm F.moves_a
  exact TitsSystem.Moves.congr T (π := (fun j => 10 - j) ∘ (fun j => 10 - j)) (π' := fun j => j)
    hmul (fun j => ⟨0, by change j = 10 - (10 - j) + 16 * 0; ring⟩)

theorem alpha_comm_five {x : F.K} (hx : x.val ≠ 1) {y : G} (hy : y ∈ T.U 5) :
    F.alpha x * y = y * F.alpha x := by
  calc F.alpha x * y = T.mu 1 x.val * (F.a * y) := by
        simp only [alpha]
        rw [mul_assoc]
    _ = T.mu 1 x.val * (y * F.a) := by rw [F.a_comm hy]
    _ = (T.mu 1 x.val * y) * F.a := by rw [mul_assoc]
    _ = (y * T.mu 1 x.val) * F.a := by rw [T.mu_one_comm F.hT x.mem hx hy]
    _ = y * (T.mu 1 x.val * F.a) := by rw [mul_assoc]
    _ = y * F.alpha x := rfl

theorem alpha_xp_four {x : F.K} (hx : x.val ≠ 1) (z : F.K) :
    F.alpha x * F.xp 4 z.val * (F.alpha x)⁻¹ = F.xp 4 (F.mulK x z).val := by
  have ha : F.a * F.xp 4 z.val * F.a⁻¹ = F.xp 6 z.val := by
    have h := F.a_conj_xp (j := 4) (by decide : Even (4 : ℤ)) z.mem
    simpa using h
  have hcomm : ⁅x.val, F.xp 6 z.val⁆ =
      T.mu 1 x.val * F.xp 6 z.val * (T.mu 1 x.val)⁻¹ :=
    T.lemma33_i_eq F.hT x.mem hx (F.xp_mem (by decide : Even (6 : ℤ)) z.mem)
  calc F.alpha x * F.xp 4 z.val * (F.alpha x)⁻¹
      = T.mu 1 x.val * (F.a * F.xp 4 z.val * F.a⁻¹) * (T.mu 1 x.val)⁻¹ := by
        simp only [alpha]
        group
    _ = T.mu 1 x.val * F.xp 6 z.val * (T.mu 1 x.val)⁻¹ := by rw [ha]
    _ = ⁅x.val, F.xp 6 z.val⁆ := hcomm.symm
    _ = F.xp 4 (F.mulK x z).val := (F.xp_four_mulK x z).symm

theorem mulK_e1 (x : F.K) : F.mulK x ⟨F.e1, F.e1_mem⟩ = x := by
  ext
  have h : F.xp 4 (F.mulK x ⟨F.e1, F.e1_mem⟩).val = F.xp 4 x.val := by
    rw [F.xp_four_mulK, F.xp_six_e1, ← F.xp_four]
  exact (F.xp_bijOn (j := 4) (by decide : Even (4 : ℤ))).injOn
    (F.mulK x ⟨F.e1, F.e1_mem⟩).mem x.mem h

theorem mulK_one_left (y : F.K) :
    F.mulK ⟨1, (T.U 1).one_mem⟩ y = ⟨1, (T.U 1).one_mem⟩ := by
  ext
  have h : F.xp 4 (F.mulK ⟨1, (T.U 1).one_mem⟩ y).val = F.xp 4 (1 : G) := by
    rw [F.xp_four_mulK, F.xp_one_eq]
    simp [commutatorElement_def]
  exact (F.xp_bijOn (j := 4) (by decide : Even (4 : ℤ))).injOn
    (F.mulK ⟨1, (T.U 1).one_mem⟩ y).mem (T.U 1).one_mem h

theorem mulK_one_right (x : F.K) :
    F.mulK x ⟨1, (T.U 1).one_mem⟩ = ⟨1, (T.U 1).one_mem⟩ := by
  ext
  have h : F.xp 4 (F.mulK x ⟨1, (T.U 1).one_mem⟩).val = F.xp 4 (1 : G) := by
    rw [F.xp_four_mulK, F.xp_one_eq, F.xp_one_eq]
    simp [commutatorElement_def]
  exact (F.xp_bijOn (j := 4) (by decide : Even (4 : ℤ))).injOn
    (F.mulK x ⟨1, (T.U 1).one_mem⟩).mem (T.U 1).one_mem h

theorem mulK_ne_one {x y : F.K} (hx : x.val ≠ 1) (hy : y.val ≠ 1) :
    (F.mulK x y).val ≠ 1 := by
  intro h
  have h1 : ⁅x.val, F.xp 6 y.val⁆ = 1 := by
    rw [← F.xp_four_mulK x y, h]
    exact F.xp_one_eq 4
  have h2 : F.xp 6 y.val = 1 := by
    have heq := T.lemma33_i_eq F.hT x.mem hx (F.xp_mem (by decide : Even (6 : ℤ)) y.mem)
    rw [heq] at h1
    have h3 := congrArg (fun t => (T.mu 1 x.val)⁻¹ * t * T.mu 1 x.val) h1
    simpa [mul_assoc] using h3
  have h4 : F.xp 6 y.val = F.xp 6 (1 : G) := by
    rw [h2, F.xp_one_eq]
  have hy1 : y.val = 1 :=
    (F.xp_bijOn (j := 6) (by decide : Even (6 : ℤ))).injOn y.mem (T.U 1).one_mem h4
  exact hy hy1

theorem alpha_alpha_xp_four {x y : F.K} (hx : x.val ≠ 1) (hy : y.val ≠ 1) :
    F.alpha x * F.alpha y * F.xp 4 F.e1 * (F.alpha x * F.alpha y)⁻¹ =
      F.xp 4 (F.mulK x y).val := by
  calc F.alpha x * F.alpha y * F.xp 4 F.e1 * (F.alpha x * F.alpha y)⁻¹
      = F.alpha x * (F.alpha y * F.xp 4 F.e1 * (F.alpha y)⁻¹) * (F.alpha x)⁻¹ := by
        group
    _ = F.alpha x * F.xp 4 (F.mulK y ⟨F.e1, F.e1_mem⟩).val * (F.alpha x)⁻¹ := by
        rw [show F.alpha y * F.xp 4 F.e1 * (F.alpha y)⁻¹ =
          F.xp 4 (F.mulK y ⟨F.e1, F.e1_mem⟩).val from F.alpha_xp_four hy ⟨F.e1, F.e1_mem⟩]
    _ = F.alpha x * F.xp 4 y.val * (F.alpha x)⁻¹ := by rw [F.mulK_e1]
    _ = F.xp 4 (F.mulK x y).val := F.alpha_xp_four hx y

theorem alpha_mulK_mem {x y : F.K} (hx : x.val ≠ 1) (hy : y.val ≠ 1) :
    (F.alpha (F.mulK x y))⁻¹ * (F.alpha x * F.alpha y) ∈ T.Ctriv := by
  classical
  set z : F.K := F.mulK x y with hzdef
  set g : G := (F.alpha z)⁻¹ * (F.alpha x * F.alpha y) with hgdef
  have hz : z.val ≠ 1 := F.mulK_ne_one hx hy
  set mx : G := T.mu 1 x.val with hmx
  set my : G := T.mu 1 y.val with hmy
  set M : G := T.mu 1 z.val with hM
  set W : G := mx * F.a * my with hW
  have ha_inv : F.a⁻¹ = F.a := by
    calc F.a⁻¹ = F.a⁻¹ * (F.a * F.a) := by rw [F.a_mul_self, mul_one]
      _ = F.a := by group
  have hM2 : M * M = 1 := by
    have h := T.lemma35_ii F.hT (j := 1) (by decide : Odd (1 : ℤ)) z.mem hz
    simpa [M] using h
  have hM_inv : M⁻¹ = M := by
    calc M⁻¹ = M⁻¹ * (M * M) := by rw [hM2, mul_one]
      _ = M := by group
  have hza : (F.alpha z)⁻¹ = F.a * M := by
    change (M * F.a)⁻¹ = F.a * M
    rw [mul_inv_rev, ha_inv, hM_inv]
  have hg_eq : g = F.a * M * W * F.a := by
    rw [hgdef, hza]
    simp only [alpha, W, mx, my]
    group
  have hc5 : ∀ t : G, t ∈ T.U 5 → g * t = t * g := by
    intro t ht
    have hz5 := F.alpha_comm_five hz ht
    have hx5 := F.alpha_comm_five hx ht
    have hy5 := F.alpha_comm_five hy ht
    have hzi : (F.alpha z)⁻¹ * t = t * (F.alpha z)⁻¹ := by
      calc (F.alpha z)⁻¹ * t = (F.alpha z)⁻¹ * (t * F.alpha z) * (F.alpha z)⁻¹ := by
            group
        _ = (F.alpha z)⁻¹ * (F.alpha z * t) * (F.alpha z)⁻¹ := by rw [← hz5]
        _ = t * (F.alpha z)⁻¹ := by group
    have hxy : (F.alpha x * F.alpha y) * t = t * (F.alpha x * F.alpha y) := by
      calc (F.alpha x * F.alpha y) * t = F.alpha x * (F.alpha y * t) := by group
        _ = F.alpha x * (t * F.alpha y) := by rw [hy5]
        _ = (F.alpha x * t) * F.alpha y := by group
        _ = (t * F.alpha x) * F.alpha y := by rw [hx5]
        _ = t * (F.alpha x * F.alpha y) := by group
    rw [hgdef]
    calc (F.alpha z)⁻¹ * (F.alpha x * F.alpha y) * t
        = (F.alpha z)⁻¹ * ((F.alpha x * F.alpha y) * t) := by group
      _ = (F.alpha z)⁻¹ * (t * (F.alpha x * F.alpha y)) := by rw [hxy]
      _ = ((F.alpha z)⁻¹ * t) * (F.alpha x * F.alpha y) := by group
      _ = (t * (F.alpha z)⁻¹) * (F.alpha x * F.alpha y) := by rw [hzi]
      _ = t * ((F.alpha z)⁻¹ * (F.alpha x * F.alpha y)) := by group
  have hfix_e4 : g * F.xp 4 F.e1 * g⁻¹ = F.xp 4 F.e1 := by
    have hz4 : F.alpha z * F.xp 4 (⟨F.e1, F.e1_mem⟩ : F.K).val * (F.alpha z)⁻¹ =
        F.xp 4 z.val := by
      rw [F.alpha_xp_four hz, F.mulK_e1]
    have hxy4 := F.alpha_alpha_xp_four hx hy
    rw [hgdef]
    calc (F.alpha z)⁻¹ * (F.alpha x * F.alpha y) * F.xp 4 F.e1 *
          ((F.alpha z)⁻¹ * (F.alpha x * F.alpha y))⁻¹
        = (F.alpha z)⁻¹ * ((F.alpha x * F.alpha y) * F.xp 4 F.e1 *
            (F.alpha x * F.alpha y)⁻¹) * F.alpha z := by group
      _ = (F.alpha z)⁻¹ * F.xp 4 z.val * F.alpha z := by rw [hxy4, hzdef]
      _ = F.xp 4 F.e1 := by
        have h := congrArg (fun t => (F.alpha z)⁻¹ * t * F.alpha z) hz4
        rw [mul_assoc] at h
        simpa using h.symm
  have hg_moves : T.Moves g (fun j => j) := by
    rw [hgdef]
    have hz_moves : T.Moves (F.alpha z) (fun j => j) := F.moves_alpha hz
    have hz_inv : T.Moves (F.alpha z)⁻¹ (fun j => j) := by
      have hz_shift : T.Moves (F.alpha z) (fun j => j + 0) := by simpa using hz_moves
      simpa using TitsSystem.Moves.inv_shift T (c := 0) hz_shift
    have hxy_moves : T.Moves (F.alpha x * F.alpha y) (fun j => j) := by
      have h := TitsSystem.Moves.mul T (F.moves_alpha hx) (F.moves_alpha hy)
      exact TitsSystem.Moves.congr T (π := (fun j => j) ∘ (fun j => j)) (π' := fun j => j)
        h (fun j => ⟨0, by change j = j + 16 * 0; ring⟩)
    exact TitsSystem.Moves.mul T hz_inv hxy_moves
  have hg_moves' : T.Moves g (fun j => (1 : ℤ) * j + 0) := by simpa using hg_moves
  have he5mem : F.xo 5 F.e1 ∈ T.U 5 :=
    F.xo_mem (j := 5) (by decide : Odd (5 : ℤ)) F.e1_mem
  have he5ne : F.xo 5 F.e1 ≠ 1 := by
    intro h
    have h4 : F.xo 5 F.e1 = F.xo 5 (1 : G) := by rw [h, F.xo_one_eq]
    exact F.e1_ne ((F.xo_bijOn (j := 5) (by decide : Odd (5 : ℤ))).injOn
      F.e1_mem (T.U 1).one_mem h4)
  have hm5 : g * T.mu 5 (F.xo 5 F.e1) = T.mu 5 (F.xo 5 F.e1) * g := by
    have hconj := (T.mu_conj (n := 8) (by norm_num) (g := g) (ε := 1) (c := 0)
      (Or.inl rfl) hg_moves' (i := 5) he5mem he5ne).1
    have hge : g * F.xo 5 F.e1 * g⁻¹ = F.xo 5 F.e1 := by
      rw [hc5 (F.xo 5 F.e1) he5mem]
      group
    rw [hge, show (1 : ℤ) * 5 + 0 = 5 by norm_num] at hconj
    calc g * T.mu 5 (F.xo 5 F.e1) = (g * T.mu 5 (F.xo 5 F.e1) * g⁻¹) * g := by group
      _ = T.mu 5 (F.xo 5 F.e1) * g := by rw [← hconj]
  have he4mem : F.xp 4 F.e1 ∈ T.Uprime 4 :=
    F.xp_mem (j := 4) (by decide : Even (4 : ℤ)) F.e1_mem
  have he4ne : F.xp 4 F.e1 ≠ 1 := by
    intro h
    have h4 : F.xp 4 F.e1 = F.xp 4 (1 : G) := by rw [h, F.xp_one_eq]
    exact F.e1_ne ((F.xp_bijOn (j := 4) (by decide : Even (4 : ℤ))).injOn
      F.e1_mem (T.U 1).one_mem h4)
  have hm4 : g * T.mu 4 (F.xp 4 F.e1) = T.mu 4 (F.xp 4 F.e1) * g := by
    have hconj := (T.mu_conj (n := 8) (by norm_num) (g := g) (ε := 1) (c := 0)
      (Or.inl rfl) hg_moves' (i := 4) (T.Uprime_le 4 he4mem) he4ne).1
    have hge : g * F.xp 4 F.e1 * g⁻¹ = F.xp 4 F.e1 := hfix_e4
    rw [hge, show (1 : ℤ) * 4 + 0 = 4 by norm_num] at hconj
    calc g * T.mu 4 (F.xp 4 F.e1) = (g * T.mu 4 (F.xp 4 F.e1) * g⁻¹) * g := by group
      _ = T.mu 4 (F.xp 4 F.e1) * g := by rw [← hconj]
  have hcomm_rho : Commute g F.rho := by
    show g * F.rho = F.rho * g
    rw [F.rho_eq]
    calc g * (T.mu 5 (F.xo 5 F.e1) * T.mu 4 (F.xp 4 F.e1))
        = (g * T.mu 5 (F.xo 5 F.e1)) * T.mu 4 (F.xp 4 F.e1) := by group
      _ = (T.mu 5 (F.xo 5 F.e1) * g) * T.mu 4 (F.xp 4 F.e1) := by rw [hm5]
      _ = T.mu 5 (F.xo 5 F.e1) * (g * T.mu 4 (F.xp 4 F.e1)) := by group
      _ = T.mu 5 (F.xo 5 F.e1) * (T.mu 4 (F.xp 4 F.e1) * g) := by rw [hm4]
      _ = T.mu 5 (F.xo 5 F.e1) * T.mu 4 (F.xp 4 F.e1) * g := by group
  have he6eq : F.e6 = F.rho * F.xp 4 F.e1 * F.rho⁻¹ := by
    rw [← F.xp_six_e1]
    simpa using (F.rho_zpow_conj_xp (1 : ℤ) 4 F.e1).symm
  have hfix_e6 : g * F.e6 * g⁻¹ = F.e6 := by
    rw [he6eq]
    have hr : g * F.rho * g⁻¹ = F.rho := by
      rw [hcomm_rho.eq]
      group
    have hr' : g * F.rho⁻¹ * g⁻¹ = F.rho⁻¹ := by
      have h := hcomm_rho.eq
      calc g * F.rho⁻¹ * g⁻¹ = (g * F.rho * g⁻¹)⁻¹ := by group
        _ = F.rho⁻¹ := by rw [hr]
    calc g * (F.rho * F.xp 4 F.e1 * F.rho⁻¹) * g⁻¹
        = (g * F.rho * g⁻¹) * (g * F.xp 4 F.e1 * g⁻¹) * (g * F.rho⁻¹ * g⁻¹) := by
          group
      _ = F.rho * F.xp 4 F.e1 * F.rho⁻¹ := by rw [hr, hfix_e4, hr']
  have hodd : ∀ j : ℤ, Odd j → ∀ t : G, t ∈ T.U j → g * t = t * g := by
    intro j hj t ht
    obtain ⟨k, hk⟩ := hj
    set m : ℤ := k - 2 with hm
    have hjm : j = 5 + 2 * m := by rw [hm]; omega
    have ht5 : (F.rho ^ m)⁻¹ * t * F.rho ^ m ∈ T.U 5 := by
      have h := TitsSystem.Moves.conj_mem T (F.moves_rho_zpow (-m)) (j := j) ht
      have hidx : j + 2 * (-m) = 5 := by rw [hjm]; ring
      rw [hidx] at h
      simpa using h
    have hg5 := hc5 _ ht5
    have hgm : Commute g (F.rho ^ m) := hcomm_rho.zpow_right m
    calc g * t = g * (F.rho ^ m * ((F.rho ^ m)⁻¹ * t * F.rho ^ m) *
          (F.rho ^ m)⁻¹) := by group
      _ = (g * F.rho ^ m) * ((F.rho ^ m)⁻¹ * t * F.rho ^ m) * (F.rho ^ m)⁻¹ := by
          group
      _ = (F.rho ^ m * g) * ((F.rho ^ m)⁻¹ * t * F.rho ^ m) * (F.rho ^ m)⁻¹ := by
          rw [hgm.eq]
      _ = F.rho ^ m * (g * ((F.rho ^ m)⁻¹ * t * F.rho ^ m)) * (F.rho ^ m)⁻¹ := by
          group
      _ = F.rho ^ m * (((F.rho ^ m)⁻¹ * t * F.rho ^ m) * g) * (F.rho ^ m)⁻¹ := by
          rw [hg5]
      _ = F.rho ^ m * ((F.rho ^ m)⁻¹ * t * (F.rho ^ m * g)) * (F.rho ^ m)⁻¹ := by
          group
      _ = F.rho ^ m * ((F.rho ^ m)⁻¹ * t * (g * F.rho ^ m)) * (F.rho ^ m)⁻¹ := by
          rw [← hgm.eq]
      _ = t * g := by group
  have hprime4 : ∀ t : G, t ∈ T.Uprime 4 → g * t = t * g := by
    intro t ht
    obtain ⟨u, hu, hxu⟩ := (F.xp_bijOn (j := 4) (by decide : Even (4 : ℤ))).surjOn ht
    have hu1 : g * u * g⁻¹ = u := by
      rw [hodd 1 (by decide : Odd (1 : ℤ)) u hu]
      group
    have hcomm : g * ⁅u, F.e6⁆ * g⁻¹ = ⁅u, F.e6⁆ := by
      rw [conjugate_commutatorElement, hu1, hfix_e6]
    have hval : F.xp 4 u = ⁅u, F.e6⁆ := F.xp_four u
    rw [← hxu, hval]
    calc g * ⁅u, F.e6⁆ = (g * ⁅u, F.e6⁆ * g⁻¹) * g := by group
      _ = ⁅u, F.e6⁆ * g := by rw [hcomm]
  have heven : ∀ j : ℤ, Even j → ∀ t : G, t ∈ T.Uprime j → g * t = t * g := by
    intro j hj t ht
    obtain ⟨k, hk⟩ := hj
    set m : ℤ := k - 2 with hm
    have hjm : j = 4 + 2 * m := by rw [hm]; omega
    have ht4 : (F.rho ^ m)⁻¹ * t * F.rho ^ m ∈ T.Uprime 4 := by
      have hmov : T.Moves (F.rho ^ (-m)) (fun j => 1 * j + (-2 * m)) := by
        simpa [neg_mul] using F.moves_rho_zpow (-m)
      have h := TitsSystem.Moves.conj_mem_Uprime T (Or.inl rfl) hmov (j := j) ht
      have hidx : 1 * j + (-2 * m) = 4 := by rw [hjm]; ring
      rw [hidx] at h
      simpa using h
    have hg4 := hprime4 _ ht4
    have hgm : Commute g (F.rho ^ m) := hcomm_rho.zpow_right m
    calc g * t = g * (F.rho ^ m * ((F.rho ^ m)⁻¹ * t * F.rho ^ m) *
          (F.rho ^ m)⁻¹) := by group
      _ = (g * F.rho ^ m) * ((F.rho ^ m)⁻¹ * t * F.rho ^ m) * (F.rho ^ m)⁻¹ := by
          group
      _ = (F.rho ^ m * g) * ((F.rho ^ m)⁻¹ * t * F.rho ^ m) * (F.rho ^ m)⁻¹ := by
          rw [hgm.eq]
      _ = F.rho ^ m * (g * ((F.rho ^ m)⁻¹ * t * F.rho ^ m)) * (F.rho ^ m)⁻¹ := by
          group
      _ = F.rho ^ m * (((F.rho ^ m)⁻¹ * t * F.rho ^ m) * g) * (F.rho ^ m)⁻¹ := by
          rw [hg4]
      _ = F.rho ^ m * ((F.rho ^ m)⁻¹ * t * (F.rho ^ m * g)) * (F.rho ^ m)⁻¹ := by
          group
      _ = F.rho ^ m * ((F.rho ^ m)⁻¹ * t * (g * F.rho ^ m)) * (F.rho ^ m)⁻¹ := by
          rw [← hgm.eq]
      _ = t * g := by group
  rw [TitsSystem.Ctriv, Subgroup.mem_inf]
  constructor
  · rw [Subgroup.mem_iInf]
    intro k
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact (hodd (2 * k + 1) ⟨k, by ring⟩ t ht).symm
  · rw [Subgroup.mem_iInf]
    intro k
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact (heven (2 * k) ⟨k, by ring⟩ t ht).symm

theorem alpha_comm_mem {x y : F.K} (hx : x.val ≠ 1) (hy : y.val ≠ 1) :
    (F.alpha y * F.alpha x)⁻¹ * (F.alpha x * F.alpha y) ∈ T.Ctriv := by
  classical
  set z : F.K := F.mulK x y with hzdef
  set mx : G := T.mu 1 x.val with hmx
  set my : G := T.mu 1 y.val with hmy
  set M : G := T.mu 1 z.val with hM
  set W : G := mx * F.a * my with hW
  set g : G := (F.alpha z)⁻¹ * (F.alpha x * F.alpha y) with hgdef
  have hx2 : mx * mx = 1 := by
    have h := T.lemma35_ii F.hT (j := 1) (by decide : Odd (1 : ℤ)) x.mem hx
    simpa [mx] using h
  have hy2 : my * my = 1 := by
    have h := T.lemma35_ii F.hT (j := 1) (by decide : Odd (1 : ℤ)) y.mem hy
    simpa [my] using h
  have hz : z.val ≠ 1 := F.mulK_ne_one hx hy
  have hz2 : M * M = 1 := by
    have h := T.lemma35_ii F.hT (j := 1) (by decide : Odd (1 : ℤ)) z.mem hz
    simpa [M] using h
  have ha2 : F.a * F.a = 1 := F.a_mul_self
  have ha_inv : F.a⁻¹ = F.a := by
    calc F.a⁻¹ = F.a⁻¹ * (F.a * F.a) := by rw [ha2, mul_one]
      _ = F.a := by group
  have hmx_inv : mx⁻¹ = mx := by
    calc mx⁻¹ = mx⁻¹ * (mx * mx) := by rw [hx2, mul_one]
      _ = mx := by group
  have hmy_inv : my⁻¹ = my := by
    calc my⁻¹ = my⁻¹ * (my * my) := by rw [hy2, mul_one]
      _ = my := by group
  have hM_inv : M⁻¹ = M := by
    calc M⁻¹ = M⁻¹ * (M * M) := by rw [hz2, mul_one]
      _ = M := by group
  have hgC : g ∈ T.Ctriv := by
    rw [hgdef]
    simpa [hzdef] using F.alpha_mulK_mem hx hy
  have ha_moves : T.Moves F.a (fun j => (-1 : ℤ) * j + 10) := by
    simpa [sub_eq_add_neg, neg_one_mul, add_comm] using F.moves_a
  have haz : F.alpha z = M * F.a := by simp only [alpha, ← hM]
  have hax : F.alpha x = mx * F.a := by simp only [alpha, ← hmx]
  have hay : F.alpha y = my * F.a := by simp only [alpha, ← hmy]
  have hza : (F.alpha z)⁻¹ = F.a * M := by
    rw [haz, mul_inv_rev, ha_inv, hM_inv]
  have hg_eq : g = F.a * M * W * F.a := by
    rw [hgdef, hza]
    simp only [hax, hay, W]
    group
  have hident : F.a * g * F.a⁻¹ = M * W := by
    rw [hg_eq, ha_inv]
    calc F.a * (F.a * M * W * F.a) * F.a
        = (F.a * F.a) * M * W * (F.a * F.a) := by group
      _ = M * W := by rw [ha2, one_mul, mul_one]
  have hMW : M * W ∈ T.Ctriv := by
    have hconj := T.conj_mem_Ctriv (g := F.a) (ε := -1) (c := 10) (Or.inr rfl)
      (by decide : Even (10 : ℤ)) ha_moves hgC
    rwa [hident] at hconj
  have hM_moves : T.Moves M (fun j => (-1 : ℤ) * j + 10) := by
    have h := T.moves_mu (i := 1) (n := 8) z.mem hz
    simpa [M, sub_eq_add_neg, neg_one_mul, add_comm] using h
  have hWM : W * M ∈ T.Ctriv := by
    have hconj := T.conj_mem_Ctriv (g := M) (ε := -1) (c := 10) (Or.inr rfl)
      (by decide : Even (10 : ℤ)) hM_moves hMW
    have hident' : M * (M * W) * M⁻¹ = W * M := by
      rw [hM_inv, ← mul_assoc M M W, hz2, one_mul]
    rwa [hident'] at hconj
  have hW2 : W * W ∈ T.Ctriv := by
    have h : W * W = (W * M) * (M * W) := by
      calc W * W = W * (M * M) * W := by rw [hz2]; group
        _ = (W * M) * (M * W) := by group
    rw [h]
    exact (T.Ctriv).mul_mem hWM hMW
  have hBA : F.alpha y * F.alpha x = W⁻¹ * F.a := by
    simp only [alpha, W, ← hmx, ← hmy, mul_inv_rev, ha_inv, hmx_inv, hmy_inv]
    group
  have hAB : F.alpha x * F.alpha y = W * F.a := by
    simp only [alpha, W, ← hmx, ← hmy]
    group
  have hfinal : (F.alpha y * F.alpha x)⁻¹ * (F.alpha x * F.alpha y) =
      F.a * (W * W) * F.a⁻¹ := by
    rw [hBA, hAB, mul_inv_rev, ha_inv, inv_inv]
    group
  rw [hfinal]
  exact T.conj_mem_Ctriv (g := F.a) (ε := -1) (c := 10) (Or.inr rfl)
    (by decide : Even (10 : ℤ)) ha_moves hW2

theorem mulK_comm (x y : F.K) : F.mulK x y = F.mulK y x := by
  by_cases hx1 : x.val = 1
  · have hx : x = ⟨1, (T.U 1).one_mem⟩ := by ext; exact hx1
    simp only [hx, F.mulK_one_left, F.mulK_one_right]
  by_cases hy1 : y.val = 1
  · have hy : y = ⟨1, (T.U 1).one_mem⟩ := by ext; exact hy1
    simp only [hy, F.mulK_one_left, F.mulK_one_right]
  · set g : G := (F.alpha y * F.alpha x)⁻¹ * (F.alpha x * F.alpha y) with hgdef
    have hg : g ∈ T.Ctriv := by
      rw [hgdef]
      exact F.alpha_comm_mem hx1 hy1
    have he4mem : F.xp 4 F.e1 ∈ T.Uprime 4 :=
      F.xp_mem (j := 4) (by decide : Even (4 : ℤ)) F.e1_mem
    have hge4 : g * F.xp 4 F.e1 * g⁻¹ = F.xp 4 F.e1 := by
      have h := T.Ctriv_comm_Uprime hg (j := 4) (by decide : Even (4 : ℤ)) he4mem
      calc g * F.xp 4 F.e1 * g⁻¹ = F.xp 4 F.e1 * g * g⁻¹ := by rw [h]
        _ = F.xp 4 F.e1 := by group
    have hxy := F.alpha_alpha_xp_four hx1 hy1
    have hyx := F.alpha_alpha_xp_four hy1 hx1
    have hα : F.alpha x * F.alpha y = (F.alpha y * F.alpha x) * g := by
      rw [hgdef]
      group
    have hval : F.xp 4 (F.mulK x y).val = F.xp 4 (F.mulK y x).val := by
      rw [← hxy, ← hyx, hα]
      calc (F.alpha y * F.alpha x * g) * F.xp 4 F.e1 *
            (F.alpha y * F.alpha x * g)⁻¹
          = (F.alpha y * F.alpha x) * (g * F.xp 4 F.e1 * g⁻¹) *
              (F.alpha y * F.alpha x)⁻¹ := by group
        _ = (F.alpha y * F.alpha x) * F.xp 4 F.e1 * (F.alpha y * F.alpha x)⁻¹ := by
            rw [hge4]
    ext
    exact (F.xp_bijOn (j := 4) (by decide : Even (4 : ℤ))).injOn
      (F.mulK x y).mem (F.mulK y x).mem hval

theorem mulK_assoc (x y z : F.K) :
    F.mulK (F.mulK x y) z = F.mulK x (F.mulK y z) := by
  by_cases hx1 : x.val = 1
  · have hx : x = ⟨1, (T.U 1).one_mem⟩ := by ext; exact hx1
    simp only [hx, F.mulK_one_left]
  by_cases hy1 : y.val = 1
  · have hy : y = ⟨1, (T.U 1).one_mem⟩ := by ext; exact hy1
    simp only [hy, F.mulK_one_left, F.mulK_one_right]
  by_cases hz1 : z.val = 1
  · have hz : z = ⟨1, (T.U 1).one_mem⟩ := by ext; exact hz1
    simp only [hz, F.mulK_one_right]
  set A : F.K := F.mulK x y with hAdef
  set B : F.K := F.mulK y z with hBdef
  have hA : A.val ≠ 1 := by
    rw [hAdef]; exact F.mulK_ne_one hx1 hy1
  have hB : B.val ≠ 1 := by
    rw [hBdef]; exact F.mulK_ne_one hy1 hz1
  set g : G := (F.alpha A)⁻¹ * (F.alpha x * F.alpha y) with hgdef
  have hgC : g ∈ T.Ctriv := by
    rw [hgdef, hAdef]
    exact F.alpha_mulK_mem hx1 hy1
  have hα : F.alpha x * F.alpha y = F.alpha A * g := by
    rw [hgdef]
    group
  have hz4mem : F.xp 4 z.val ∈ T.Uprime 4 :=
    F.xp_mem (j := 4) (by decide : Even (4 : ℤ)) z.mem
  have hg4 : g⁻¹ * F.xp 4 z.val * g = F.xp 4 z.val := by
    have h := T.Ctriv_comm_Uprime hgC (j := 4) (by decide : Even (4 : ℤ)) hz4mem
    calc g⁻¹ * F.xp 4 z.val * g = g⁻¹ * (F.xp 4 z.val * g) := by group
      _ = g⁻¹ * (g * F.xp 4 z.val) := by rw [h]
      _ = F.xp 4 z.val := by group
  have hg4' : g * F.xp 4 z.val * g⁻¹ = F.xp 4 z.val := by
    calc g * F.xp 4 z.val * g⁻¹ = g * (g⁻¹ * F.xp 4 z.val * g) * g⁻¹ := by
          rw [hg4]
      _ = F.xp 4 z.val := by group
  have hAz : F.xp 4 (F.mulK A z).val =
      F.alpha x * F.alpha y * F.xp 4 z.val * (F.alpha x * F.alpha y)⁻¹ := by
    rw [← F.alpha_xp_four hA z, hα]
    have h : (F.alpha A * g) * F.xp 4 z.val * (F.alpha A * g)⁻¹ =
        F.alpha A * F.xp 4 z.val * (F.alpha A)⁻¹ := by
      calc (F.alpha A * g) * F.xp 4 z.val * (F.alpha A * g)⁻¹
          = F.alpha A * (g * F.xp 4 z.val * g⁻¹) * (F.alpha A)⁻¹ := by group
        _ = F.alpha A * F.xp 4 z.val * (F.alpha A)⁻¹ := by rw [hg4']
    exact h.symm
  have hxB : F.xp 4 (F.mulK x B).val =
      F.alpha x * F.alpha y * F.xp 4 z.val * (F.alpha x * F.alpha y)⁻¹ := by
    rw [← F.alpha_xp_four hx1 B, ← F.alpha_xp_four hy1 z]
    group
  ext
  exact (F.xp_bijOn (j := 4) (by decide : Even (4 : ℤ))).injOn
    (F.mulK A z).mem (F.mulK x B).mem (by rw [hAz, hxB])

theorem mulK_add (x y z : F.K) :
    F.mulK x ⟨y.val * z.val, (T.U 1).mul_mem y.mem z.mem⟩ =
      ⟨(F.mulK x y).val * (F.mulK x z).val,
        (T.U 1).mul_mem (F.mulK x y).mem (F.mulK x z).mem⟩ := by
  set w : F.K := ⟨y.val * z.val, (T.U 1).mul_mem y.mem z.mem⟩ with hw
  have hL : F.xp 4 (F.mulK x w).val =
      ⁅x.val, F.xp 6 y.val⁆ * ⁅x.val, F.xp 6 z.val⁆ := by
    rw [F.xp_four_mulK]
    have hw6 : F.xp 6 w.val = F.xp 6 y.val * F.xp 6 z.val := by
      rw [hw]
      exact F.xp_mul y.mem z.mem 6
    rw [hw6, commutatorElement_mul_right_eq_mul_conj]
    have hc : ⁅x.val, F.xp 6 z.val⁆ * F.xp 6 y.val =
        F.xp 6 y.val * ⁅x.val, F.xp 6 z.val⁆ :=
      T.Uprime_comm (j := 4) (k := 6) (by norm_num) (by norm_num)
        (T.lemma33_i F.hT x.mem (F.xp_mem (j := 6) (by decide : Even (6 : ℤ)) z.mem))
        (T.Uprime_le 6 (F.xp_mem (j := 6) (by decide : Even (6 : ℤ)) y.mem))
    calc ⁅x.val, F.xp 6 y.val⁆ * F.xp 6 y.val * ⁅x.val, F.xp 6 z.val⁆ *
          (F.xp 6 y.val)⁻¹
        = ⁅x.val, F.xp 6 y.val⁆ * (F.xp 6 y.val * ⁅x.val, F.xp 6 z.val⁆) *
            (F.xp 6 y.val)⁻¹ := by group
      _ = ⁅x.val, F.xp 6 y.val⁆ * (⁅x.val, F.xp 6 z.val⁆ * F.xp 6 y.val) *
            (F.xp 6 y.val)⁻¹ := by rw [← hc]
      _ = ⁅x.val, F.xp 6 y.val⁆ * ⁅x.val, F.xp 6 z.val⁆ := by group
  have hR : F.xp 4 (⟨(F.mulK x y).val * (F.mulK x z).val,
      (T.U 1).mul_mem (F.mulK x y).mem (F.mulK x z).mem⟩ : F.K).val =
      ⁅x.val, F.xp 6 y.val⁆ * ⁅x.val, F.xp 6 z.val⁆ := by
    rw [F.xp_mul (F.mulK x y).mem (F.mulK x z).mem 4,
      F.xp_four_mulK x y, F.xp_four_mulK x z]
  ext
  exact (F.xp_bijOn (j := 4) (by decide : Even (4 : ℤ))).injOn
    (F.mulK x w).mem
    ((T.U 1).mul_mem (F.mulK x y).mem (F.mulK x z).mem) (by rw [hL, hR])

theorem exists_mulK_eq_e1 {y : F.K} (hy : y.val ≠ 1) :
    ∃ x : F.K, F.mulK x y = ⟨F.e1, F.e1_mem⟩ := by
  have hT2 : (T.shift (-2)).Normalized :=
    F.hT.shift (show Even (-2 : ℤ) from ⟨-1, by norm_num⟩)
  have hy6mem : F.xp 6 y.val ∈ T.Uprime 6 :=
    F.xp_mem (j := 6) (by decide : Even (6 : ℤ)) y.mem
  have hy6ne : F.xp 6 y.val ≠ 1 := by
    intro h
    have h4 : F.xp 6 y.val = F.xp 6 (1 : G) := by rw [h, F.xp_one_eq]
    exact hy ((F.xp_bijOn (j := 6) (by decide : Even (6 : ℤ))).injOn
      y.mem (T.U 1).one_mem h4)
  have hv2 : F.xp 6 y.val ∈ (T.shift (-2)).Uprime 8 := by
    rw [TitsSystem.Uprime_shift]
    simpa using hy6mem
  have hv2ne : F.xp 6 y.val ≠ 1 := hy6ne
  have he4mem : F.xp 4 F.e1 ∈ T.Uprime 4 :=
    F.xp_mem (j := 4) (by decide : Even (4 : ℤ)) F.e1_mem
  have he4_2 : F.xp 4 F.e1 ∈ (T.shift (-2)).Uprime 6 := by
    rw [TitsSystem.Uprime_shift]
    simpa using he4mem
  obtain ⟨u, hu2, hux⟩ := TitsSystem.lemma39_surj (T := T.shift (-2)) hT2 hv2 hv2ne he4_2
  have hu : u ∈ T.U 1 := by
    rw [shift_U] at hu2
    simpa using hu2
  refine ⟨⟨u, hu⟩, ?_⟩
  ext
  exact (F.xp_bijOn (j := 4) (by decide : Even (4 : ℤ))).injOn
    (F.mulK ⟨u, hu⟩ y).mem F.e1_mem (by
      rw [F.xp_four_mulK, hux])

@[expose]
def addK {F' : OctFrame T} (x y : F'.K) : F'.K :=
  ⟨x.val * y.val, (T.U 1).mul_mem x.mem y.mem⟩

@[expose]
def zeroK {F' : OctFrame T} : F'.K := ⟨1, (T.U 1).one_mem⟩

@[expose]
def negK {F' : OctFrame T} (x : F'.K) : F'.K :=
  ⟨x.val⁻¹, (T.U 1).inv_mem x.mem⟩

@[expose]
def oneK {F' : OctFrame T} : F'.K := ⟨F'.e1, F'.e1_mem⟩

@[expose, instance_reducible]
noncomputable def commRingK {F' : OctFrame T} : CommRing F'.K :=
  letI : Add F'.K := ⟨addK⟩
  letI : Zero F'.K := ⟨zeroK⟩
  letI : Neg F'.K := ⟨negK⟩
  letI : Mul F'.K := ⟨F'.mulK⟩
  letI : One F'.K := ⟨oneK⟩
  CommRing.ofMinimalAxioms
    (fun x y z => by
      show addK (addK x y) z = addK x (addK y z)
      ext
      simp only [addK]
      group)
    (fun x => by
      show addK zeroK x = x
      ext
      simp [addK, zeroK])
    (fun x => by
      show addK (negK x) x = zeroK
      ext
      simp [addK, negK, zeroK])
    (fun x y z => by
      show F'.mulK (F'.mulK x y) z = F'.mulK x (F'.mulK y z)
      exact F'.mulK_assoc x y z)
    (fun x y => by
      show F'.mulK x y = F'.mulK y x
      exact F'.mulK_comm x y)
    (fun x => by
      show F'.mulK oneK x = x
      rw [F'.mulK_comm]
      exact F'.mulK_e1 x)
    (fun x y z => by
      show F'.mulK x (addK y z) = addK (F'.mulK x y) (F'.mulK x z)
      exact F'.mulK_add x y z)

noncomputable instance : Field F.K :=
  letI : CommRing F.K := commRingK
  IsField.toField (by
    refine ⟨?_, ?_, ?_⟩
    · refine ⟨0, 1, ?_⟩
      intro h
      have hval : (0 : F.K).val = (1 : F.K).val := congrArg K.val h
      have hval' : (1 : G) = F.e1 := hval
      exact F.e1_ne hval'.symm
    · intro x y
      show F.mulK x y = F.mulK y x
      exact F.mulK_comm x y
    · intro a ha
      have hav : a.val ≠ 1 := by
        intro h
        apply ha
        ext
        change a.val = (1 : G)
        exact h
      obtain ⟨b, hb⟩ := F.exists_mulK_eq_e1 hav
      refine ⟨b, ?_⟩
      show F.mulK a b = oneK
      rw [F.mulK_comm, hb]
      rfl)

theorem val_add (x y : F.K) : (x + y).val = x.val * y.val := rfl

theorem val_zero : (0 : F.K).val = 1 := rfl

theorem val_one : (1 : F.K).val = F.e1 := rfl

theorem mul_def (x y : F.K) : x * y = F.mulK x y := rfl

theorem val_eq_one_iff {x : F.K} : x.val = 1 ↔ x = 0 := by
  constructor
  · intro h
    ext
    simpa [val_zero] using h
  · intro h
    rw [h, val_zero]

theorem comm_xo_xp {j : ℤ} (hj : Even j) (x y : F.K) :
    ⁅F.xo (j - 3) x.val, F.xp (j + 2) y.val⁆ = F.xp j (x * y).val := by
  obtain ⟨m, hm⟩ := hj
  set k : ℤ := m - 2 with hk
  have hj4 : j = 4 + 2 * k := by rw [hk]; omega
  have hj3 : j - 3 = 1 + 2 * k := by omega
  have hj2 : j + 2 = 6 + 2 * k := by omega
  have hxo : F.xo (j - 3) x.val = F.rho ^ k * F.xo 1 x.val * (F.rho ^ k)⁻¹ := by
    simpa [hj3] using (F.rho_zpow_conj_xo k 1 x.val).symm
  have hxp : F.xp (j + 2) y.val = F.rho ^ k * F.xp 6 y.val * (F.rho ^ k)⁻¹ := by
    simpa [hj2] using (F.rho_zpow_conj_xp k 6 y.val).symm
  have hxpj : F.xp j (x * y).val = F.rho ^ k * F.xp 4 (x * y).val * (F.rho ^ k)⁻¹ := by
    simpa [hj4] using (F.rho_zpow_conj_xp k 4 (x * y).val).symm
  have hxy : ⁅x.val, F.xp 6 y.val⁆ = F.xp 4 (x * y).val := by
    rw [F.mul_def x y]
    exact (F.xp_four_mulK x y).symm
  rw [hxo, hxp, hxpj, ← conjugate_commutatorElement, F.xo_one, hxy]

theorem comm_xo_xp' {j : ℤ} (hj : Even j) (x y : F.K) :
    ⁅F.xo (j + 3) x.val, F.xp (j - 2) y.val⁆ = F.xp j (x * y).val := by
  have hbase : ⁅F.xo 9 x.val, F.xp 4 y.val⁆ = F.xp 6 (x * y).val := by
    have h4 : ⁅F.xo 1 x.val, F.xp 6 y.val⁆ = F.xp 4 (x * y).val := by
      simpa using F.comm_xo_xp (j := 4) (by decide : Even (4 : ℤ)) x y
    have hconj := congrArg (fun t => F.a * t * F.a⁻¹) h4
    have hxo := F.a_conj_xo (j := 1) (by decide : Odd (1 : ℤ)) x.mem
    have hxp6 := F.a_conj_xp (j := 6) (by decide : Even (6 : ℤ)) y.mem
    have hxp4 := F.a_conj_xp (j := 4) (by decide : Even (4 : ℤ)) (x * y).mem
    rw [conjugate_commutatorElement, hxo, hxp6, hxp4] at hconj
    simpa using hconj
  obtain ⟨m, hm⟩ := hj
  set k : ℤ := m - 3 with hk
  have hj6 : j = 6 + 2 * k := by rw [hk]; omega
  have hj9 : j + 3 = 9 + 2 * k := by omega
  have hj4 : j - 2 = 4 + 2 * k := by omega
  have hxo : F.xo (j + 3) x.val = F.rho ^ k * F.xo 9 x.val * (F.rho ^ k)⁻¹ := by
    simpa [hj9] using (F.rho_zpow_conj_xo k 9 x.val).symm
  have hxp : F.xp (j - 2) y.val = F.rho ^ k * F.xp 4 y.val * (F.rho ^ k)⁻¹ := by
    simpa [hj4] using (F.rho_zpow_conj_xp k 4 y.val).symm
  have hxpj : F.xp j (x * y).val = F.rho ^ k * F.xp 6 (x * y).val * (F.rho ^ k)⁻¹ := by
    simpa [hj6] using (F.rho_zpow_conj_xp k 6 (x * y).val).symm
  rw [hxo, hxp, hxpj, ← conjugate_commutatorElement, hbase]

end Basic

end OctFrame

end CFSG.GH74.Tits83
