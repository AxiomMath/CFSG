module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII2010Late10

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameSimple FrameCore)
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.Q3T6D
open Out
open scoped commutatorElement MatrixGroups Pointwise

section Std


variable {G : Type} [Group G] [Finite G] [FrameCore G] {Ω : Set (Subgroup G)}
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

theorem Std20Frame.isSylow2In_S_centralizer (d : Std20Frame K K' J S R R' W V z t) :
    IsSylow2In (S : Subgroup G) (Subgroup.centralizer ({z} : Set G)) :=
  ⟨d.hSz, S.isPGroup', fun _ _ hV' hle => S.is_maximal' hV' hle⟩

theorem Std20Frame.odd_index_centralizer (d : Std20Frame K K' J S R R' W V z t) :
    Odd (Subgroup.centralizer ({z} : Set G)).index := by
  have h1 := Subgroup.index_dvd_of_le d.hSz
  have h2 : ¬ 2 ∣ (S : Subgroup G).index := S.not_dvd_index
  have h3 : ¬ 2 ∣ (Subgroup.centralizer ({z} : Set G)).index := fun h => h2 (h.trans h1)
  exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h3)

theorem Std20Frame.exists_conj_into_S (d : Std20Frame K K' J S R R' W V z t) {c : G}
    (hc : c ∈ Subgroup.centralizer ({z} : Set G)) (hc2 : IsPGroup 2 ↥(Subgroup.zpowers c)) :
    ∃ y ∈ Subgroup.centralizer ({z} : Set G), y * c * y⁻¹ ∈ (S : Subgroup G) := by
  obtain ⟨P', hP', hcP'⟩ := IsSylow2In.exists_ge hc2 (Subgroup.zpowers_le.mpr hc)
  obtain ⟨y, hy, hyP⟩ := Sec6Gen.exists_conjSub_eq_of_isSylow2In hP' d.isSylow2In_S_centralizer
  refine ⟨y, hy, ?_⟩
  rw [← hyP]
  exact conj_mem_conjSub (hcP' (Subgroup.mem_zpowers c))

theorem Std20Frame.swap_fusion [FrameSimple G] (d : Std20Frame K K' J S R R' W V z t)
    (hnc : ∃ x y : G, x * y ≠ y * x) {b : G} (hb : b ∈ (S : Subgroup G))
    (hbK : conjSub b K = K') (hb4 : (b * b) * (b * b) = 1) :
    (∃ (n : ℕ) (h c : G), Odd n ∧ c ∈ (S : Subgroup G) ∧ conjSub c K = K ∧
        c = h⁻¹ * b ^ n * h) ∨
      (∃ (h c : G), c ∈ (S : Subgroup G) ∧ conjSub c K ≠ K ∧ c = h⁻¹ * (b * b) * h) := by
  classical
  have hne := d.ne
  have h1 : ∀ g ∈ Subgroup.centralizer ({z} : Set G), conjSub g K = K ∨ conjSub g K = K' :=
    fun g hg => d.late_conj_K hg
  have h2 : ∀ g ∈ Subgroup.centralizer ({z} : Set G), conjSub g K' = K ∨ conjSub g K' = K' :=
    fun g hg => d.late_conj_K' hg
  obtain ⟨ϕ, hϕ⟩ : ∃ ϕ : ↥(Subgroup.centralizer ({z} : Set G)) →* Multiplicative (ZMod 2),
      ∀ c : ↥(Subgroup.centralizer ({z} : Set G)), ϕ c = 1 ↔ conjSub (c : G) K = K :=
    ⟨swapHom hne h1 h2, swapHom_eq_one_iff hne h1 h2⟩
  have hbC : b ∈ Subgroup.centralizer ({z} : Set G) := d.hSz hb
  have hb2 : IsPGroup 2 (Subgroup.zpowers b) := S.isPGroup'.to_le (Subgroup.zpowers_le.mpr hb)
  have hϕb : ϕ ⟨b, hbC⟩ ≠ 1 := by
    rw [Ne, hϕ]
    show conjSub b K ≠ K
    rw [hbK]
    exact hne
  obtain ⟨g, n, hg, hneq⟩ :=
    CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge.exists_fusion_of_noIndexTwo
      (FrameSimple.noIndexTwo d.nonabelian) d.odd_index_centralizer ϕ hbC hb2 hϕb
  have hb4' : b ^ 4 = 1 := by
    rw [show b ^ 4 = (b * b) * (b * b) by simp only [pow_succ, pow_zero, one_mul, mul_assoc]]
    exact hb4
  set c₀ : G := g⁻¹ * b ^ n * g with hc₀
  have hc₀4 : c₀ ^ 4 = 1 := by
    have h : c₀ = (MulAut.conj g⁻¹) (b ^ n) := by simp [hc₀]
    rw [h, ← map_pow, ← pow_mul, mul_comm, pow_mul, hb4', one_pow, map_one]
  obtain ⟨y, hyC, hyS⟩ := d.exists_conj_into_S hg (T3CII.isPGroup_zpowers_of_pow_four hc₀4)
  set c : G := y * c₀ * y⁻¹ with hc
  have hcC : c ∈ Subgroup.centralizer ({z} : Set G) := by
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ hyC hg) (Subgroup.inv_mem _ hyC)
  have hϕc : ϕ ⟨c, hcC⟩ = ϕ ⟨c₀, hg⟩ := by
    have : (⟨c, hcC⟩ : ↥(Subgroup.centralizer ({z} : Set G))) =
        ⟨y, hyC⟩ * ⟨c₀, hg⟩ * ⟨y, hyC⟩⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv]
    generalize ϕ ⟨y, hyC⟩ = a
    generalize ϕ ⟨c₀, hg⟩ = b
    revert a b
    decide
  have hcconj : ∀ w : G, y * (g⁻¹ * w * g) * y⁻¹ = (g * y⁻¹)⁻¹ * w * (g * y⁻¹) := by
    intro w
    group
  rcases Nat.even_or_odd n with hn | hn
  ·
    have hc1 : ϕ ⟨c₀, hg⟩ ≠ 1 := fun h => hneq (h.trans (z2_pow_even _ _ hn).symm)
    have hϕc1 : ϕ ⟨c, hcC⟩ ≠ 1 := by rw [hϕc]; exact hc1
    obtain ⟨m, r, hr, hnm⟩ : ∃ m r : ℕ, r < 4 ∧ n = 4 * m + r :=
      ⟨n / 4, n % 4, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod n 4).symm⟩
    have hbn : b ^ n = b ^ r := by rw [hnm, pow_add, pow_mul, hb4', one_pow, one_mul]
    have hr2 : r = 0 ∨ r = 2 := by
      obtain ⟨k, hk⟩ := hn
      omega
    rcases hr2 with rfl | rfl
    · exfalso
      apply hc1
      have h0 : c₀ = 1 := by rw [hc₀, hbn]; group
      have h' : (⟨c₀, hg⟩ : ↥(Subgroup.centralizer ({z} : Set G))) = 1 := Subtype.ext h0
      rw [h', map_one]
    · right
      refine ⟨g * y⁻¹, c, hyS, fun h => hϕc1 ((hϕ ⟨c, hcC⟩).mpr h), ?_⟩
      rw [hc, hc₀, hbn, hcconj, pow_two]
  · left
    refine ⟨n, g * y⁻¹, c, hn, hyS, ?_, ?_⟩
    · have h0 : ϕ ⟨c₀, hg⟩ = 1 := by
        by_contra h
        apply hneq
        have hb' : ϕ ⟨b, hbC⟩ ^ n = ϕ ⟨b, hbC⟩ := z2_pow_odd _ _ hn
        exact (z2_eq_of_ne_one h hϕb).trans hb'.symm
      exact (hϕ ⟨c, hcC⟩).mp (hϕc.trans h0)
    · rw [hc, hc₀, hcconj]

theorem Std20Frame.r10b_four (d : Std20Frame K K' J S R R' W V z t)
    (c8 : Concl20_8 S K' R) (h8 : Nat.card R = 8) {s : G} (hsS : s ∈ (S : Subgroup G))
    (hsX : s ∈ sec20X (CoreAssembly.conjClass K) z K K') (hs2 : s * s ≠ 1)
    (hs4 : (s * s) * (s * s) = 1) : s * s = z ∨ s ∈ W := by
  obtain ⟨b, hbS, hbK, hb2⟩ := d.late_exists_b h8 c8
  have hz2 := d.viol.hzK.sq
  have hz1 := d.viol.hzK.ne_one
  have ht2 := d.viol.hzJ.sq
  have ht1 := d.viol.hzJ.ne_one
  have hbz : b * z * b⁻¹ = z := d.late_S_act_z hbS
  obtain ⟨u, r, v₀, t₀, T, hh⟩ := d.late_exists_hex
  have hd := hh.hd
  have hu4 : orderOf u = 4 := by
    have := hd.card
    omega
  have huu : u * u = z := by
    have h := hd.z_eq
    rw [hu4] at h
    simpa [pow_two] using h
  have DR : Q8Dat R z u r :=
    { hu := hd.U_le_R (Subgroup.mem_zpowers u)
      hr := hd.r_mem
      hu2 := huu
      hr2 := hd.sq_r
      hru := hd.conj_u
      hrn := hd.r_not_mem
      hcover := hd.cover }
  have huW : u ∈ W := hd.u_memW
  have hRR'mem : ∀ x : G, x ∈ R' ↔ b⁻¹ * x * b ∈ R := by
    intro x
    rw [d.late_R'_eq, d.late_R_eq, Subgroup.mem_inf, Subgroup.mem_inf, ← hbK, mem_conjSub_iff]
    have : x ∈ (S : Subgroup G) ↔ b⁻¹ * x * b ∈ (S : Subgroup G) := by
      constructor
      · intro hx
        exact S.mul_mem (S.mul_mem (S.inv_mem hbS) hx) hbS
      · intro hx
        have := S.mul_mem (S.mul_mem hbS hx) (S.inv_mem hbS)
        simpa [mul_assoc] using this
    rw [this]
  have hu₀R' : b * u * b⁻¹ ∈ R' := (hRR'mem _).mpr (by
    have : b⁻¹ * (b * u * b⁻¹) * b = u := by group
    rw [this]
    exact DR.hu)
  have hr₀R' : b * r * b⁻¹ ∈ R' := (hRR'mem _).mpr (by
    have : b⁻¹ * (b * r * b⁻¹) * b = r := by group
    rw [this]
    exact DR.hr)
  have DR₀ : Q8Dat R' z (b * u * b⁻¹) (b * r * b⁻¹) :=
    { hu := hu₀R'
      hr := hr₀R'
      hu2 := by
        calc b * u * b⁻¹ * (b * u * b⁻¹) = b * (u * u) * b⁻¹ := by group
          _ = z := by rw [huu]; exact hbz
      hr2 := by
        calc b * r * b⁻¹ * (b * r * b⁻¹) = b * (r * r) * b⁻¹ := by group
          _ = z := by rw [DR.hr2]; exact hbz
      hru := by
        calc b * r * b⁻¹ * (b * u * b⁻¹) * (b * r * b⁻¹)⁻¹
            = b * (r * u * r⁻¹) * b⁻¹ := by group
          _ = b * u⁻¹ * b⁻¹ := by rw [DR.hru]
          _ = (b * u * b⁻¹)⁻¹ := by group
      hrn := by
        intro h
        apply DR.hrn
        obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp h
        rw [conj_zpow] at hj
        have hj' : u ^ j = r := by
          have := congrArg (fun y => b⁻¹ * y * b) hj
          simpa [mul_assoc] using this
        rw [← hj']
        exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers u) j
      hcover := by
        intro x hx
        have hx' : b⁻¹ * x * b ∈ R := (hRR'mem x).mp hx
        have hxe : x = b * (b⁻¹ * x * b) * b⁻¹ := by group
        rcases DR.hcover _ hx' with h | ⟨y, hy, h⟩
        · left
          obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp h
          refine Subgroup.mem_zpowers_iff.mpr ⟨j, ?_⟩
          rw [conj_zpow, hj]
          rw [hxe]
          rw [← hj]
          group
        · right
          obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hy
          refine ⟨(b * u * b⁻¹) ^ j, Subgroup.mem_zpowers_iff.mpr ⟨j, rfl⟩, ?_⟩
          rw [conj_zpow, hj, hxe, h]
          group }
  have hbbW : b * b ∈ W := by
    rcases hb2 with h | h
    · rw [h]
      exact d.late_t_mem_W
    · rw [h]
      exact W.mul_mem d.late_z_mem_W d.late_t_mem_W
  obtain ⟨hut', hbt⟩ := d.late_swap_sq_data hbS hbK hbbW hd.u_mem huu
  have hzu : z * u = u * z := by rw [← huu]; group
  have hu₀W : b * u * b⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (d.hWN hbS) u).mp huW
  obtain ⟨u₂, DR', hut, hu₂W⟩ : ∃ u₂ : G, Q8Dat R' z u₂ (b * r * b⁻¹) ∧ u * u₂ = t ∧ u₂ ∈ W := by
    rcases hut' with h | h
    · exact ⟨_, DR₀, h, hu₀W⟩
    · refine ⟨(b * u * b⁻¹)⁻¹, DR₀.inv hz2, ?_, W.inv_mem hu₀W⟩
      have h1 : (b * u * b⁻¹)⁻¹ = z * (b * u * b⁻¹) := by
        apply inv_eq_of_mul_eq_one_right
        calc b * u * b⁻¹ * (z * (b * u * b⁻¹))
            = (b * u * b⁻¹) * ((b * u * b⁻¹) * (b * u * b⁻¹)) * (b * u * b⁻¹) := by
              rw [DR₀.hu2]
              group
          _ = ((b * u * b⁻¹) * (b * u * b⁻¹)) * ((b * u * b⁻¹) * (b * u * b⁻¹)) := by group
          _ = 1 := by rw [DR₀.hu2, hz2]
      rw [h1]
      calc u * (z * (b * u * b⁻¹)) = (u * z) * (b * u * b⁻¹) := by group
        _ = (z * u) * (b * u * b⁻¹) := by rw [hzu]
        _ = z * (u * (b * u * b⁻¹)) := by group
        _ = z * (z * t) := by rw [h]
        _ = t := by rw [← mul_assoc, hz2, one_mul]
  have hVcyc : IsCyclic ↥V := by
    obtain ⟨R₀, -, -, hc, -⟩ := d.hV
    exact hc
  have hV4 : Nat.card V = 4 := by
    have := Q3T6.Gen612.natCard_eq_two_mul_of_mem_USet d.late_hΩ d.hV d.late_mem_K d.hR
    omega
  obtain ⟨v, hvV, hv4, hv2, hvgen⟩ := exists_gen_of_cyclic_card_four hVcyc hV4
  have hvt : v * v = t := sq_eq_of_involution hv4 hv2 (hvgen t d.htV) ht2 ht1
  have hvW : v ∈ W := d.hVW hvV
  have hvS : v ∈ (S : Subgroup G) := d.hVS hvV
  have hWc := d.late_hWc
  have hvu : v * u = u * v := hWc v hvW u huW
  have hvu₂ : v * u₂ = u₂ * v := hWc v hvW u₂ hu₂W
  have hvR : ∀ x ∈ R, v * x * v⁻¹ ∈ R := by
    intro x hx
    rw [d.late_R_eq] at hx ⊢
    exact ⟨(Subgroup.mem_normalizer_iff.mp (d.late_W_le_N_K hvW) x).mp hx.1,
      S.mul_mem (S.mul_mem hvS hx.2) (S.inv_mem hvS)⟩
  have hvR' : ∀ x ∈ R', v * x * v⁻¹ ∈ R' := by
    intro x hx
    rw [d.late_R'_eq] at hx ⊢
    exact ⟨(Subgroup.mem_normalizer_iff.mp (d.late_W_le_N_K' hvW) x).mp hx.1,
      S.mul_mem (S.mul_mem hvS hx.2) (S.inv_mem hvS)⟩
  have hbt' : b⁻¹ * t * b = t := by
    calc b⁻¹ * t * b = b⁻¹ * (b * t * b⁻¹) * b := by rw [hbt]
      _ = t := by group
  have hrt₂ : b * r * b⁻¹ * t * (b * r * b⁻¹)⁻¹ = t * z := by
    calc b * r * b⁻¹ * t * (b * r * b⁻¹)⁻¹ = b * (r * (b⁻¹ * t * b) * r⁻¹) * b⁻¹ := by group
      _ = b * (r * t * r⁻¹) * b⁻¹ := by rw [hbt']
      _ = b * (t * z) * b⁻¹ := by rw [hh.hrt]
      _ = (b * t * b⁻¹) * (b * z * b⁻¹) := by group
      _ = t * z := by rw [hbt, hbz]
  have hsRV : s ∈ R ⊔ R' ⊔ V := by
    rw [← frame_SX d c8]
    exact ⟨hsS, hsX⟩
  obtain ⟨q, hq, w, hw, rfl⟩ :=
    Sec6Gen.exists_mul_of_mem_sup_of_le_normalizer d.late_V_le_N_RR' hsRV
  obtain ⟨x, hx, x', hx', rfl⟩ :=
    Sec6Gen.exists_mul_of_mem_sup_of_le_normalizer d.late_R'_le_N_R hq
  obtain ⟨k, rfl⟩ := hvgen w hw
  exact order_four_abstract hz2 hz1 ht2 DR DR' (fun x hx y hy => d.late_R_R'_comm hx hy) hvR
    hvR' hvu hvu₂ hvt hut hh.hrt hrt₂ huW hu₂W hvW ⟨x, hx, x', hx', k, rfl⟩ hs2 hs4

theorem Std20Frame.r10b_not_conj_swap (d : Std20Frame K K' J S R R' W V z t) {b c h : G}
    (hb : b ∈ (S : Subgroup G)) (hbK : conjSub b K = K')
    (hb2 : b * b = t ∨ b * b = z * t) (hb4 : b ^ 4 = 1) (hc2 : c * c ≠ 1)
    (hc4 : (c * c) * (c * c) = 1) (hcN : conjSub c K = K) (hcM : c * c = z ∨ c ∈ W) {n : ℕ}
    (hn : Odd n) (hbc : b ^ n = h * c * h⁻¹) : False := by
  obtain ⟨L₀, hL₀Ω, hL₀i, hcL₀⟩ : ∃ L₀ ∈ CoreAssembly.conjClass K,
      IsUniqueInvolution L₀ (c * c) ∧ conjSub c L₀ = L₀ := by
    rcases hcM with hcc | hW
    · exact ⟨K, d.late_mem_K, hcc ▸ d.viol.hzK, hcN⟩
    · obtain ⟨m, -, hme, hmem⟩ := d.late_W_four_mem hW hc2 hc4
      obtain ⟨hL₁, hL₂, -, hL₁i, hL₂i⟩ := d.late_member_data m
      rcases hmem with h' | h'
      · exact ⟨conjSub m K, hL₁, hme ▸ hL₁i, conjSub_eq_self_of_mem h'⟩
      · exact ⟨conjSub m K', hL₂, hme ▸ hL₂i, conjSub_eq_self_of_mem h'⟩
  have hL₁Ω : conjSub h L₀ ∈ CoreAssembly.conjClass K := d.hyp.conjInvariant h L₀ hL₀Ω
  have hbb : b * b = h * (c * c) * h⁻¹ := by
    rw [← pow_odd_mul_self hb4 hn, hbc]
    group
  have hL₁i : IsUniqueInvolution (conjSub h L₀) (b * b) := by
    rw [hbb]
    exact hL₀i.conj h
  have hbnN : b ^ n ∈ Subgroup.normalizer ((conjSub h L₀ : Subgroup G) : Set G) := by
    rw [mem_normalizer_iff_conjSub_eq, hbc, conjSub_mul (h * c) h⁻¹, conjSub_inv_conjSub,
      conjSub_mul, hcL₀]
  have hbN : b ∈ Subgroup.normalizer ((conjSub h L₀ : Subgroup G) : Set G) := by
    have h1 : (b ^ n) ^ n = b := by
      obtain ⟨k, rfl⟩ := hn
      rw [← pow_mul, show (2 * k + 1) * (2 * k + 1) = 4 * (k * k + k) + 1 by ring, pow_add,
        pow_mul, hb4, one_pow, one_mul, pow_one]
    rw [← h1]
    exact Subgroup.pow_mem _ hbnN n
  have ha₀ : b * b = z ∨ b * b = t ∨ b * b = z * t := by
    rcases hb2 with h' | h'
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr h')
  obtain ⟨m₀, -, hme₀⟩ := d.late_exists_m ha₀
  have hL := d.late_members_of_inv hme₀ hL₁Ω hL₁i
  have hσa : b * (b * b) * b⁻¹ = b * b := by group
  exact d.late_swap_not_N_member hb hbK hσa hme₀ ha₀ hL (mem_normalizer_iff_conjSub_eq.mp hbN)

theorem Std20Frame.r10b_SX_le_N (d : Std20Frame K K' J S R R' W V z t) :
    (S : Subgroup G) ⊓ sec20X (CoreAssembly.conjClass K) z K K' ≤
      Subgroup.normalizer (K : Set G) :=
  inf_le_right.trans (frameX_le_N d)

end Std

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
