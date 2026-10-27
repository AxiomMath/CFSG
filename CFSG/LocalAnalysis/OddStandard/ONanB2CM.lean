module

public import Certificates.Certificate6149

public section

namespace CFSG.OddStandard.ONanRec.CM

open Subgroup
open scoped commutatorElement

theorem b2Facts_cert : B2Facts :=
  Certificates.certificate6149.1

theorem chain_facts
    {g : Equiv.Perm (Fin 480)} (hg : g ∈ M480) :
    ((∀ i : Fin 6, genPerm i * g = g * genPerm i) → g = 1 ∨ g = fP) ∧
      (g * r1P = r1P * g → g * r2P = r2P * g →
        ∃ i j k l, i < 3 ∧ j < 3 ∧ k < 4 ∧ l < 2 ∧ g = r1P ^ i * r2P ^ j * (zP ^ k * dP ^ l)) ∧
      (g * zP = zP * g → g * dP = dP * g → g * g * (g * g) = 1 → g * g ≠ 1 →
        ∃ i j k l, i < 3 ∧ j < 3 ∧ (k = 1 ∨ k = 3) ∧ l < 2 ∧
          g = r1P ^ i * r2P ^ j * yP ^ k * fP ^ l) :=
  Certificates.certificate6149.2 g hg

theorem mem_of_mem_closure_of_mul_right {M : Type*} [Group M] [Finite M] {X : Set M}
    {P : M → Prop} (h1 : P 1) (hmul : ∀ x, P x → ∀ s ∈ X, P (x * s)) {g : M}
    (hg : g ∈ Subgroup.closure X) : P g := by
  have hinv : ∀ s ∈ X, s⁻¹ ∈ Submonoid.closure X := by
    intro s hs
    have hpos := orderOf_pos s
    have e : s⁻¹ = s ^ (orderOf s - 1) := by
      rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, Nat.sub_add_cancel hpos,
        pow_orderOf_eq_one]
    rw [e]
    exact Submonoid.pow_mem _ (Submonoid.subset_closure hs) _
  have hle : (Subgroup.closure X).toSubmonoid ≤ Submonoid.closure X := by
    rw [Subgroup.closure_toSubmonoid, Submonoid.closure_le]
    rintro x (hx | hx)
    · exact Submonoid.subset_closure hx
    · have := hinv x⁻¹ hx
      rwa [inv_inv] at this
  have hg' : g ∈ Submonoid.closure X := hle hg
  clear hg
  induction hg' using Submonoid.closure_induction_right with
  | one => exact h1
  | mul_right x _ s hs ih => exact hmul x ih s hs

theorem mem_closure_pair_iff {M : Type*} [Group M] {a b : M} (ha : a ^ 3 = 1) (hb : b ^ 3 = 1)
    (hab : a * b = b * a) (x : M) :
    x ∈ Subgroup.closure ({a, b} : Set M) ↔ ∃ i j, i < 3 ∧ j < 3 ∧ x = a ^ i * b ^ j := by
  have hc : Commute a b := hab
  have hmod : ∀ (c : M), c ^ 3 = 1 → ∀ n : ℕ, c ^ n = c ^ (n % 3) := by
    intro c hc3 n
    conv_lhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul, hc3, one_pow, one_mul]
  constructor
  · intro hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact ⟨1, 0, by norm_num, by norm_num, by simp⟩
      · exact ⟨0, 1, by norm_num, by norm_num, by simp⟩
    | one => exact ⟨0, 0, by norm_num, by norm_num, by simp⟩
    | mul x y _ _ hx hy =>
      obtain ⟨i, j, hi, hj, rfl⟩ := hx
      obtain ⟨i', j', hi', hj', rfl⟩ := hy
      refine ⟨(i + i') % 3, (j + j') % 3, Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num), ?_⟩
      rw [← hmod a ha, ← hmod b hb, pow_add, pow_add]
      have h1 : b ^ j * a ^ i' = a ^ i' * b ^ j := (hc.pow_pow i' j).symm.eq
      calc a ^ i * b ^ j * (a ^ i' * b ^ j') = a ^ i * (b ^ j * a ^ i') * b ^ j' := by group
        _ = a ^ i * (a ^ i' * b ^ j) * b ^ j' := by rw [h1]
        _ = a ^ i * a ^ i' * (b ^ j * b ^ j') := by group
    | inv x _ hx =>
      obtain ⟨i, j, hi, hj, rfl⟩ := hx
      refine ⟨(3 - i) % 3, (3 - j) % 3, Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num), ?_⟩
      rw [← hmod a ha, ← hmod b hb]
      have hai : (a ^ i)⁻¹ = a ^ (3 - i) := by
        rw [inv_eq_iff_mul_eq_one, ← pow_add, Nat.add_sub_cancel' hi.le, ha]
      have hbj : (b ^ j)⁻¹ = b ^ (3 - j) := by
        rw [inv_eq_iff_mul_eq_one, ← pow_add, Nat.add_sub_cancel' hj.le, hb]
      rw [mul_inv_rev, hai, hbj]
      exact (hc.pow_pow (3 - i) (3 - j)).symm.eq
  · rintro ⟨i, j, -, -, rfl⟩
    exact mul_mem (pow_mem (subset_closure (by simp)) i) (pow_mem (subset_closure (by simp)) j)

theorem commutator_comm_of_conj {M : Type*} [Group M] {z a b : M}
    (ha : a * z * a⁻¹ = z ∨ a * z * a⁻¹ = z⁻¹) (hb : b * z * b⁻¹ = z ∨ b * z * b⁻¹ = z⁻¹) :
    ⁅a, b⁆ * z = z * ⁅a, b⁆ := by
  have key : ∀ x : M, (x * z * x⁻¹ = z ∨ x * z * x⁻¹ = z⁻¹) →
      ∃ ε : ℤ, ε * ε = 1 ∧ ∀ n : ℤ, x * z ^ n * x⁻¹ = z ^ (ε * n) ∧
        x⁻¹ * z ^ n * x = z ^ (ε * n) := by
    intro x hx
    have hconj : ∀ (y w : M) (n : ℤ), y * w ^ n * y⁻¹ = (y * w * y⁻¹) ^ n := fun y w n =>
      (conj_zpow).symm
    rcases hx with hx | hx
    · refine ⟨1, by norm_num, fun n => ⟨?_, ?_⟩⟩
      · rw [hconj, hx, one_mul]
      · have hx' : x⁻¹ * z * x⁻¹⁻¹ = z := by
          calc x⁻¹ * z * x⁻¹⁻¹ = x⁻¹ * (x * z * x⁻¹) * x := by rw [hx, inv_inv]
            _ = z := by group
        rw [show x⁻¹ * z ^ n * x = x⁻¹ * z ^ n * x⁻¹⁻¹ by rw [inv_inv], hconj, hx', one_mul]
    · refine ⟨-1, by norm_num, fun n => ⟨?_, ?_⟩⟩
      · rw [hconj, hx, ← zpow_neg_one, ← zpow_mul]
      · have hx' : x⁻¹ * z * x⁻¹⁻¹ = z⁻¹ := by
          calc x⁻¹ * z * x⁻¹⁻¹ = x⁻¹ * (x * z * x⁻¹)⁻¹ * x := by rw [hx, inv_inv, inv_inv]
            _ = z⁻¹ := by group
        rw [show x⁻¹ * z ^ n * x = x⁻¹ * z ^ n * x⁻¹⁻¹ by rw [inv_inv], hconj, hx',
          ← zpow_neg_one, ← zpow_mul]
  obtain ⟨ε, hε, hεa⟩ := key a ha
  obtain ⟨δ, hδ, hδb⟩ := key b hb
  have e : ⁅a, b⁆ * z * ⁅a, b⁆⁻¹ = z := by
    rw [commutatorElement_def]
    calc a * b * a⁻¹ * b⁻¹ * z * (a * b * a⁻¹ * b⁻¹)⁻¹ =
        a * (b * (a⁻¹ * (b⁻¹ * z ^ (1 : ℤ) * b) * a) * b⁻¹) * a⁻¹ := by group
      _ = z ^ (ε * (δ * (ε * (δ * 1)))) := by
        rw [(hδb 1).2, (hεa _).2, (hδb _).1, (hεa _).1]
      _ = z := by
        rw [show ε * (δ * (ε * (δ * 1))) = (ε * ε) * (δ * δ) by ring, hε, hδ]
        simp
  calc ⁅a, b⁆ * z = ⁅a, b⁆ * z * ⁅a, b⁆⁻¹ * ⁅a, b⁆ := by group
    _ = z * ⁅a, b⁆ := by rw [e]

theorem lettersOK_cert : cmLettersOK = true :=
  lettersOK_of cmModelCheck_cert

@[expose] noncomputable def yM : M480 :=
  ⟨yP, mem_M480_wordPerm lettersOK_cert lt12_yW⟩

@[expose] noncomputable def zM : M480 :=
  ⟨zP, mem_M480_wordPerm lettersOK_cert lt12_zW⟩

@[expose] noncomputable def dM : M480 :=
  ⟨dP, mem_M480_wordPerm lettersOK_cert lt12_dW⟩

@[expose] noncomputable def fM : M480 :=
  ⟨fP, mem_M480_wordPerm lettersOK_cert lt12_fW⟩

@[expose] noncomputable def gM : M480 :=
  ⟨gP, mem_M480_wordPerm lettersOK_cert lt12_gW⟩

@[expose] noncomputable def r1M : M480 :=
  ⟨r1P, mem_M480_wordPerm lettersOK_cert lt12_r1W⟩

@[expose] noncomputable def r2M : M480 :=
  ⟨r2P, mem_M480_wordPerm lettersOK_cert lt12_r2W⟩

@[expose] noncomputable def tM (l : List ℕ) : M480 :=
  ⟨tPerm l, mem_M480_wordPerm lettersOK_cert (lt12_tWord l)⟩

@[expose] noncomputable def genM (i : Fin 6) : M480 := ⟨genPerm i, subset_closure ⟨i, rfl⟩⟩

@[expose] noncomputable def R1M : Subgroup M480 :=
  closure {r1M, r2M}

@[expose] noncomputable def T0M : Subgroup M480 :=
  closure {yM, dM, gM}

@[simp] theorem coe_yM : (yM : Equiv.Perm (Fin 480)) = yP := rfl
@[simp] theorem coe_zM : (zM : Equiv.Perm (Fin 480)) = zP := rfl
@[simp] theorem coe_dM : (dM : Equiv.Perm (Fin 480)) = dP := rfl
@[simp] theorem coe_fM : (fM : Equiv.Perm (Fin 480)) = fP := rfl
@[simp] theorem coe_gM : (gM : Equiv.Perm (Fin 480)) = gP := rfl
@[simp] theorem coe_r1M : (r1M : Equiv.Perm (Fin 480)) = r1P :=
  rfl
@[simp] theorem coe_r2M : (r2M : Equiv.Perm (Fin 480)) = r2P :=
  rfl
@[simp] theorem coe_tM (l : List ℕ) :
    (tM l : Equiv.Perm (Fin 480)) = tPerm l := rfl

theorem le_of_gens {H : Subgroup (Equiv.Perm (Fin 480))} (h : ∀ i : Fin 6, genPerm i ∈ H) :
    M480 ≤ H :=
  (closure_le H).2 (Set.range_subset_iff.2 h)

theorem fM_comm (m : M480) :
    m * fM = fM * m := by
  have hle : M480 ≤ centralizer ({fP} : Set (Equiv.Perm (Fin 480))) :=
    le_of_gens fun i => mem_centralizer_singleton_iff.2 (b2Facts_cert.fP_comm i)
  exact Subtype.ext (mem_centralizer_singleton_iff.1 (hle m.2))

theorem center_M480 (m : M480)
    (hm : ∀ m' : M480, m' * m = m * m') : m = 1 ∨ m = fM := by
  rcases (chain_facts m.2).1 fun i => congrArg Subtype.val (hm (genM i)) with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

theorem zM_sq : zM * zM = fM :=
  Subtype.ext b2Facts_cert.zP_sq

theorem zM_four : zM ^ 4 = 1 :=
  Subtype.ext (by simpa using b2Facts_cert.zP_four)

theorem fM_sq : fM * fM = 1 := by
  rw [← zM_sq, ← zM_four]
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]

theorem zM_sq_ne : zM * zM ≠ 1 :=
  fun h => b2Facts_cert.zP_sq_ne (congrArg Subtype.val h)

theorem commutator_le_centralizer_zM :
    commutator M480 ≤ centralizer ({zM} : Set M480) := by
  have hsign : ∀ m : M480, m * zM * m⁻¹ = zM ∨ m * zM * m⁻¹ = zM⁻¹ := by
    let N : Subgroup (Equiv.Perm (Fin 480)) :=
      { carrier := {x | x * zP * x⁻¹ = zP ∨ x * zP * x⁻¹ = zP⁻¹}
        one_mem' := Or.inl (by group)
        mul_mem' := by
          rintro x y (hx | hx) (hy | hy)
          · left
            calc x * y * zP * (x * y)⁻¹ = x * (y * zP * y⁻¹) * x⁻¹ := by group
              _ = zP := by rw [hy, hx]
          · right
            calc x * y * zP * (x * y)⁻¹ = (x * (y * zP * y⁻¹)⁻¹ * x⁻¹)⁻¹ := by group
              _ = zP⁻¹ := by rw [hy, inv_inv, hx]
          · right
            calc x * y * zP * (x * y)⁻¹ = x * (y * zP * y⁻¹) * x⁻¹ := by group
              _ = zP⁻¹ := by rw [hy, hx]
          · left
            calc x * y * zP * (x * y)⁻¹ = (x * (y * zP * y⁻¹)⁻¹ * x⁻¹)⁻¹ := by group
              _ = zP := by rw [hy, inv_inv, hx, inv_inv]
        inv_mem' := by
          rintro x (hx | hx)
          · left
            calc x⁻¹ * zP * x⁻¹⁻¹ = x⁻¹ * (x * zP * x⁻¹) * x := by rw [hx, inv_inv]
              _ = zP := by group
          · right
            calc x⁻¹ * zP * x⁻¹⁻¹ = x⁻¹ * (x * zP * x⁻¹)⁻¹ * x := by rw [hx, inv_inv, inv_inv]
              _ = zP⁻¹ := by group }
    have hle : M480 ≤ N := le_of_gens fun i => b2Facts_cert.conj_zP i
    intro m
    rcases hle m.2 with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  rw [commutator_def, Subgroup.commutator_le]
  intro a _ b _
  rw [mem_centralizer_singleton_iff]
  exact commutator_comm_of_conj (hsign a) (hsign b)

theorem r1M_cube : r1M ^ 3 = 1 :=
  Subtype.ext (by simpa using b2Facts_cert.r1P_cube)

theorem r2M_cube : r2M ^ 3 = 1 :=
  Subtype.ext (by simpa using b2Facts_cert.r2P_cube)

theorem rM_comm :
    r1M * r2M = r2M * r1M :=
  Subtype.ext b2Facts_cert.r_comm

theorem mem_R1M_iff (m : M480) :
    m ∈ R1M ↔ ∃ i j, i < 3 ∧ j < 3 ∧ m = r1M ^ i * r2M ^ j :=
  mem_closure_pair_iff r1M_cube r2M_cube rM_comm m

theorem rM_inj {i j i' j' : ℕ}
    (hi : i < 3) (hj : j < 3) (hi' : i' < 3) (hj' : j' < 3)
    (h : r1M ^ i * r2M ^ j = r1M ^ i' * r2M ^ j') : i = i' ∧ j = j' :=
  b2Facts_cert.r_inj i j i' j' hi hj hi' hj' (by simpa using congrArg Subtype.val h)

theorem yM_r1M :
    yM * r1M * yM⁻¹ = r2M ^ 2 :=
  Subtype.ext (by simpa using b2Facts_cert.y_r1)

theorem yM_r2M :
    yM * r2M * yM⁻¹ = r1M :=
  Subtype.ext (by simpa using b2Facts_cert.y_r2)

theorem yM_irred {i j : ℕ}
    (hi : i < 3) (hj : j < 3) (h0 : ¬ (i = 0 ∧ j = 0)) :
    yM * (r1M ^ i * r2M ^ j) * yM⁻¹ ≠ 1 ∧
      yM * (r1M ^ i * r2M ^ j) * yM⁻¹ ≠ r1M ^ i * r2M ^ j ∧
      yM * (r1M ^ i * r2M ^ j) * yM⁻¹ ≠ r1M ^ i * r2M ^ j * (r1M ^ i * r2M ^ j) := by
  obtain ⟨h1, h2, h3⟩ := b2Facts_cert.irred i j hi hj h0
  refine ⟨fun e => h1 ?_, fun e => h2 ?_, fun e => h3 ?_⟩ <;>
    simpa using congrArg Subtype.val e

theorem zM_r :
    zM * r1M = r1M * zM ∧ zM * r2M = r2M * zM ∧ dM * r1M = r1M * dM ∧ dM * r2M = r2M * dM :=
  ⟨Subtype.ext b2Facts_cert.z_r1, Subtype.ext b2Facts_cert.z_r2, Subtype.ext b2Facts_cert.d_r1,
    Subtype.ext b2Facts_cert.d_r2⟩

theorem dM_sq : dM * dM = 1 :=
  Subtype.ext b2Facts_cert.dP_sq

theorem dM_zM :
    dM * zM * dM = zM⁻¹ :=
  Subtype.ext (by simpa using b2Facts_cert.d_z)

theorem dM_ne_zM_pow {k : ℕ}
    (hk : k < 4) : dM ≠ zM ^ k :=
  fun e => b2Facts_cert.d_notin k hk (by simpa using congrArg Subtype.val e)

theorem yM_four : yM ^ 4 = 1 :=
  Subtype.ext (by simpa using b2Facts_cert.yP_four)

theorem yM_sq_ne : yM * yM ≠ 1 :=
  fun e => b2Facts_cert.yP_sq_ne (congrArg Subtype.val e)

theorem centralizer_R1M (m : M480)
    (h1 : m * r1M = r1M * m) (h2 : m * r2M = r2M * m) :
    ∃ i j k l, i < 3 ∧ j < 3 ∧ k < 4 ∧ l < 2 ∧ m = r1M ^ i * r2M ^ j * (zM ^ k * dM ^ l) := by
  obtain ⟨i, j, k, l, hi, hj, hk, hl, he⟩ :=
    (chain_facts m.2).2.1 (congrArg Subtype.val h1) (congrArg Subtype.val h2)
  exact ⟨i, j, k, l, hi, hj, hk, hl, Subtype.ext (by simpa using he)⟩

theorem centralizer_S0M (m : M480)
    (h1 : m * zM = zM * m) (h2 : m * dM = dM * m) (h4 : m * m * (m * m) = 1) (h2' : m * m ≠ 1) :
    ∃ i j k l, i < 3 ∧ j < 3 ∧ (k = 1 ∨ k = 3) ∧ l < 2 ∧
      m = r1M ^ i * r2M ^ j * yM ^ k * fM ^ l := by
  obtain ⟨i, j, k, l, hi, hj, hk, hl, he⟩ :=
    (chain_facts m.2).2.2 (congrArg Subtype.val h1) (congrArg Subtype.val h2)
      (congrArg Subtype.val h4) (fun e => h2' (Subtype.ext e))
  exact ⟨i, j, k, l, hi, hj, hk, hl, Subtype.ext (by simpa using he)⟩

theorem tM_nil : tM [] = 1 :=
  Subtype.ext (by simp [tM, tPerm, tWord, wordPerm])

theorem tM_cons (k : ℕ) (l : List ℕ) :
    tM (k :: l) = ⟨wordPerm tGens[k]!, mem_M480_wordPerm lettersOK_cert (lt12_tGens k)⟩ *
      tM l :=
  Subtype.ext (by simp only [tM, tPerm, tWord, List.flatMap_cons, wordPerm_append]; rfl)

theorem tM_mem_T0M : ∀ l : List ℕ, tM l ∈ T0M
  | [] => by rw [tM_nil]; exact one_mem _
  | k :: l => by
    rw [tM_cons]
    refine mul_mem ?_ (tM_mem_T0M l)
    match k with
    | 0 => exact subset_closure (Or.inl (Subtype.ext rfl))
    | 1 => exact subset_closure (Or.inr (Or.inl (Subtype.ext rfl)))
    | 2 => exact subset_closure (Or.inr (Or.inr (Subtype.ext rfl)))
    | k + 3 =>
      have : (⟨wordPerm tGens[k + 3]!, mem_M480_wordPerm lettersOK_cert (lt12_tGens (k + 3))⟩ :
          M480) = 1 := Subtype.ext (by simp [tGens, show (default : List ℕ) = [] from rfl, wordPerm])
      rw [this]
      exact one_mem _

theorem mem_T0M_iff (m : M480) :
    m ∈ T0M ↔ ∃ l ∈ tIdx, m = tM l := by
  constructor
  · intro hm
    refine mem_of_mem_closure_of_mul_right (P := fun m => ∃ l ∈ tIdx, m = tM l)
      ⟨[], by decide, tM_nil.symm⟩ ?_ hm
    rintro x ⟨l, hl, rfl⟩ s hs
    have key : ∀ w ∈ tGens, ∀ hw : wordPerm w ∈ M480, s = ⟨wordPerm w, hw⟩ →
        ∃ l' ∈ tIdx, tM l * s = tM l' := by
      intro w hw hwM hs'
      obtain ⟨l', hl', he⟩ := b2Facts_cert.t_closed l hl w hw
      exact ⟨l', hl', Subtype.ext (by rw [hs']; exact he)⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl
    · exact key yW (by simp [tGens]) _ rfl
    · exact key dW (by simp [tGens]) _ rfl
    · exact key gW (by simp [tGens]) _ rfl
  · rintro ⟨l, -, rfl⟩
    exact tM_mem_T0M l

theorem card_T0M :
    Nat.card T0M = 64 := by
  classical
  have hnd : (tIdx.map tM).Nodup := by
    have := b2Facts_cert.t_nodup
    rw [show tIdx.map tPerm = (tIdx.map tM).map Subtype.val by rw [List.map_map]; rfl] at this
    exact this.of_map _
  have hset : (T0M : Set M480) = ((tIdx.map tM).toFinset : Set M480) := by
    ext m
    rw [SetLike.mem_coe, mem_T0M_iff, Finset.mem_coe, List.mem_toFinset, List.mem_map]
    exact ⟨fun ⟨l, hl, he⟩ => ⟨l, hl, he.symm⟩, fun ⟨l, hl, he⟩ => ⟨l, hl, he.symm⟩⟩
  rw [← SetLike.coe_sort_coe, hset, Nat.card_coe_set_eq, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup hnd, List.length_map]
  rfl

theorem mem_normalizer_closure_of_conj {M : Type*} [Group M] {X : Set M} {s : M}
    (h1 : ∀ x ∈ X, s * x * s⁻¹ ∈ closure X) (h2 : ∀ x ∈ X, s⁻¹ * x * s ∈ closure X) :
    s ∈ normalizer (closure X : Set M) := by
  have key : ∀ t : M, (∀ x ∈ X, t * x * t⁻¹ ∈ closure X) →
      ∀ h ∈ closure X, t * h * t⁻¹ ∈ closure X := by
    intro t ht h hh
    have hle : (closure X).map (MulAut.conj t).toMonoidHom ≤ closure X := by
      rw [MonoidHom.map_closure, closure_le]
      rintro _ ⟨x, hx, rfl⟩
      exact ht x hx
    exact hle ⟨h, hh, rfl⟩
  rw [mem_normalizer_iff]
  intro h
  refine ⟨key s h1 h, fun hs => ?_⟩
  have h2' : ∀ x ∈ X, s⁻¹ * x * s⁻¹⁻¹ ∈ closure X := fun x hx => by
    rw [inv_inv]
    exact h2 x hx
  have := key s⁻¹ h2' _ hs
  have e : s⁻¹ * (s * h * s⁻¹) * s⁻¹⁻¹ = h := by group
  rwa [e] at this

theorem card_R1M :
    Nat.card R1M = 9 := by
  let f : Fin 3 × Fin 3 → R1M := fun p =>
    ⟨r1M ^ p.1.val * r2M ^ p.2.val, (mem_R1M_iff _).2 ⟨_, _, p.1.2, p.2.2, rfl⟩⟩
  have hf : Function.Bijective f := by
    refine ⟨fun p q hpq => ?_, fun x => ?_⟩
    · have h := congrArg Subtype.val hpq
      obtain ⟨h1, h2⟩ := rM_inj p.1.2 p.2.2 q.1.2 q.2.2 h
      exact Prod.ext (Fin.ext h1) (Fin.ext h2)
    · obtain ⟨i, j, hi, hj, he⟩ := (mem_R1M_iff x).1 x.2
      exact ⟨(⟨i, hi⟩, ⟨j, hj⟩), Subtype.ext he.symm⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf)]
  simp

theorem T0M_le_normalizer :
    T0M ≤ normalizer (R1M : Set M480) := by
  have hgen : ∀ s ∈ tGens, ∀ hs : wordPerm s ∈ M480,
      (⟨wordPerm s, hs⟩ : M480) ∈ normalizer (R1M : Set M480) := by
    intro s hs hsM
    have hrr : ∀ r ∈ ({r1M, r2M} : Set M480), (⟨wordPerm s, hsM⟩ : M480) * r *
        (⟨wordPerm s, hsM⟩ : M480)⁻¹ ∈ R1M ∧
        (⟨wordPerm s, hsM⟩ : M480)⁻¹ * r * (⟨wordPerm s, hsM⟩ : M480) ∈ R1M := by
      intro r hr
      have hrw : ∃ w ∈ [r1W, r2W], (r : Equiv.Perm (Fin 480)) = wordPerm w := by
        rcases hr with rfl | rfl
        · exact ⟨r1W, by simp, rfl⟩
        · exact ⟨r2W, by simp, rfl⟩
      obtain ⟨w, hw, hrw⟩ := hrw
      obtain ⟨⟨i, j, hi, hj, h1⟩, ⟨i', j', hi', hj', h2⟩⟩ := b2Facts_cert.t_norm s hs w hw
      refine ⟨(mem_R1M_iff _).2 ⟨i, j, hi, hj, Subtype.ext ?_⟩,
        (mem_R1M_iff _).2 ⟨i', j', hi', hj', Subtype.ext ?_⟩⟩
      · simpa [hrw] using h1
      · simpa [hrw] using h2
    exact mem_normalizer_closure_of_conj (fun r hr => (hrr r hr).1) (fun r hr => (hrr r hr).2)
  rw [T0M, closure_le]
  intro s hs
  rcases hs with rfl | rfl | rfl
  · exact hgen yW (by simp [tGens]) _
  · exact hgen dW (by simp [tGens]) _
  · exact hgen gW (by simp [tGens]) _

theorem yM_mem_T0M : yM ∈ T0M := subset_closure (Or.inl rfl)

theorem dM_mem_T0M : dM ∈ T0M :=
  subset_closure (Or.inr (Or.inl rfl))

theorem gM_mem_T0M : gM ∈ T0M :=
  subset_closure (Or.inr (Or.inr rfl))

theorem zM_eq : zM = gM⁻¹ * dM * gM * dM := by
  apply Subtype.ext
  simp only [coe_zM, Subgroup.coe_mul, Subgroup.coe_inv, coe_gM, coe_dM, zP, gP, dP]
  have h11 : wordPerm [11] = (wordPerm [10])⁻¹ := by
    rw [← wordPerm_inv lettersOK_cert (by decide : ∀ c ∈ [10], c < 12)]
    rfl
  rw [show zW = [11] ++ [6] ++ [10] ++ [6] from rfl, wordPerm_append, wordPerm_append,
    wordPerm_append, h11]
  rfl

theorem zM_mem_T0M : zM ∈ T0M := by
  rw [zM_eq]
  exact mul_mem (mul_mem (mul_mem (inv_mem gM_mem_T0M) dM_mem_T0M) gM_mem_T0M) dM_mem_T0M

theorem fM_mem_T0M : fM ∈ T0M := by
  rw [← zM_sq]
  exact mul_mem zM_mem_T0M zM_mem_T0M

theorem T0M_cent {m : M480}
    (hm : m ∈ T0M) (hz : m * zM = zM * m) (hd : m * dM = dM * m) :
    ∃ k l, k < 4 ∧ l < 2 ∧ m = yM ^ k * fM ^ l := by
  obtain ⟨t, ht, rfl⟩ := (mem_T0M_iff m).1 hm
  obtain ⟨k, l, hk, hl, he⟩ := b2Facts_cert.t_cent t ht (by simpa using congrArg Subtype.val hz)
    (by simpa using congrArg Subtype.val hd)
  exact ⟨k, l, hk, hl, Subtype.ext (by simpa using he)⟩

theorem T0M_quot {l : ℕ}
    (hl : l < 2) {m : M480} (hm : m ∈ T0M) (hsq : ∃ n < 4, m * m = (yM * fM ^ l) ^ n) :
    ∃ k e n, k < 4 ∧ e < 2 ∧ n < 4 ∧ m = zM ^ k * dM ^ e * (yM * fM ^ l) ^ n := by
  obtain ⟨t, ht, rfl⟩ := (mem_T0M_iff m).1 hm
  have hw : wordPerm (if l = 0 then yW else yW ++ fW) = yP * fP ^ l := by
    split_ifs with h0
    · subst h0
      simp [yP]
    · obtain rfl : l = 1 := by omega
      rw [wordPerm_append]
      simp [yP, fP]
  have hwmem : (if l = 0 then yW else yW ++ fW) ∈ [yW, yW ++ fW] := by
    split_ifs <;> simp
  obtain ⟨n, hn, hsq⟩ := hsq
  obtain ⟨k, e, n', hk, he, hn', h⟩ := b2Facts_cert.t_quot _ hwmem t ht
    ⟨n, hn, by rw [hw]; simpa using congrArg Subtype.val hsq⟩
  refine ⟨k, e, n', hk, he, hn', Subtype.ext ?_⟩
  rw [hw] at h
  simpa using h

theorem fM_pow_two :
    fM ^ 2 = 1 := by
  rw [sq, fM_sq]

theorem yfM_pow (l n : ℕ) :
    (yM * fM ^ l) ^ n = yM ^ n * fM ^ (l * n) := by
  have hc0 : Commute yM fM := fM_comm yM
  rw [(hc0.pow_right l).mul_pow, ← pow_mul]

theorem yfM_four (l : ℕ) :
    (yM * fM ^ l) ^ 4 = 1 := by
  rw [yfM_pow, yM_four, one_mul, pow_mul',
    show fM ^ 4 = 1 by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, fM_pow_two, one_pow], one_pow]

theorem yfM_sq_ne (l : ℕ) :
    (yM * fM ^ l) * (yM * fM ^ l) ≠ 1 := by
  rw [← sq, yfM_pow, pow_mul', fM_pow_two, one_pow, mul_one, sq]
  exact yM_sq_ne

end CFSG.OddStandard.ONanRec.CM
