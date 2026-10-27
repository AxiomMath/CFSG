module

public import CFSG.Certificates.Kernel.GMS78RuSM.MulCode
import CFSG.Certificates.Kernel.GMS78RuP.Basic

public section

namespace CFSG.KC.GMS.SM

open CFSG.KLie.CT CFSG.KC.Loop CFSG.GMS78Ru CFSG.GMS78RuSim CFSG.GMS78RuQ CFSG.GMS78RuS

private theorem allN_iff (n : Nat) (f : Nat → Bool) : allN n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero _), fun _ => rfl⟩
  | succ n ih =>
    have : allN (n + 1) f = andB (f n) (allN n f) := rfl
    rw [this, P117.andB_iff, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
      · exact h2 i h
      · exact h1
    · exact fun h => ⟨h n (Nat.lt_succ_self n), fun i hi => h i (Nat.lt_succ_of_lt hi)⟩

private theorem sZipAll_cons (g : Nat → Nat → Bool) (u : Nat) (U K : List Nat) :
    sZipAll g (u :: U) K = andB (g u (K.getD 0 0)) (sZipAll g U K.tail) := by
  cases K <;> rfl

private theorem sZipAll_iff (g : Nat → Nat → Bool) :
    ∀ (U K : List Nat), sZipAll g U K = true ↔
      ∀ i < U.length, g (U.getD i 0) (K.getD i 0) = true
  | [], K => ⟨fun _ i hi => absurd hi (Nat.not_lt_zero _), fun _ => rfl⟩
  | u :: U, K => by
    rw [sZipAll_cons, P117.andB_iff, sZipAll_iff g U K.tail]
    constructor
    · rintro ⟨h0, h⟩ i hi
      cases i with
      | zero => exact h0
      | succ i =>
        have := h i (Nat.lt_of_succ_lt_succ hi)
        cases K <;> simpa using this
    · intro h
      refine ⟨h 0 (Nat.succ_pos _), fun i hi => ?_⟩
      have := h (i + 1) (Nat.succ_lt_succ hi)
      cases K <;> simpa using this

private theorem sAllPairs_iff (f : Nat → Nat → Nat → Nat → Bool) (U K : List Nat) :
    sAllPairs f U K = true ↔ ∀ i < U.length, ∀ j < U.length,
      f (U.getD i 0) (K.getD i 0) (U.getD j 0) (K.getD j 0) = true := by
  unfold sAllPairs
  simp only [sZipAll_iff]

private theorem mem_getD {L : List Nat} {u : Nat} (hu : u ∈ L) :
    ∃ i < L.length, L.getD i 0 = u := by
  obtain ⟨i, hi, h⟩ := List.mem_iff_getElem.1 hu
  exact ⟨i, hi, by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; exact h⟩

private theorem getD_mem {L : List Nat} {i : Nat} (hi : i < L.length) : L.getD i 0 ∈ L := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  exact List.getElem_mem hi

private theorem bf {b : Bool} (h : ¬ b = true) : b = false := by simpa using h

private theorem sKey_eq (m : Nat → Nat → Nat) (u : Nat) : ∀ n : Nat,
    sKey m n u =
      ((List.range n).filter fun p => m p u == m u p).length +
      (16384 * ((List.range n).filter fun p => m p u == m u p).countP (fun p => m p p == u) +
        2 ^ 28 * ((List.range n).filter fun p => m p u == m u p).countP
          (fun p => m p p == 256))
  | 0 => rfl
  | n + 1 => by
    have e : sKey m (n + 1) u = strictN (sKey m n u) fun a =>
        Bool.rec (motive := fun _ => Nat) a
          ((fun s => Nat.add a (Nat.add 1 (Nat.add
            (Nat.shiftLeft (Bool.rec (motive := fun _ => Nat) 0 1 (Nat.beq s u)) 14)
            (Nat.shiftLeft (Bool.rec (motive := fun _ => Nat) 0 1 (Nat.beq s 256)) 28)))) (m n n))
          (Nat.beq (m n u) (m u n)) := rfl
    rw [e, P117.strictN_eq, sKey_eq m u n, List.range_succ, List.filter_append]
    by_cases h : (m n u == m u n) = true
    · have h' : Nat.beq (m n u) (m u n) = true := h
      rw [h']
      simp only [List.filter_cons, List.filter_nil, h, if_true, List.length_append,
        List.countP_append, List.countP_cons, List.countP_nil, List.length_cons, List.length_nil]
      by_cases h1 : (m n n == u) = true <;> by_cases h2 : (m n n == 256) = true
      · have a1 : Nat.beq (m n n) u = true := h1
        have a2 : Nat.beq (m n n) 256 = true := h2
        rw [a1, a2]; simp only [h1, h2]; simp [Nat.shiftLeft_eq]; omega
      · have a1 : Nat.beq (m n n) u = true := h1
        have a2 : Nat.beq (m n n) 256 = false := bf h2
        rw [a1, a2]; simp only [h1, h2]; simp [Nat.shiftLeft_eq]; omega
      · have a1 : Nat.beq (m n n) u = false := bf h1
        have a2 : Nat.beq (m n n) 256 = true := h2
        rw [a1, a2]; simp only [h1, h2]; simp [Nat.shiftLeft_eq]; omega
      · have a1 : Nat.beq (m n n) u = false := bf h1
        have a2 : Nat.beq (m n n) 256 = false := bf h2
        rw [a1, a2]; simp only [h1, h2]; simp [Nat.shiftLeft_eq]; omega
    · have h' : Nat.beq (m n u) (m u n) = false := bf h
      rw [h']
      simp only [List.filter_cons, List.filter_nil, h, Bool.false_eq_true, if_false, List.append_nil]

private theorem key_read (k N R1 R2 : Nat) (hN : N < 16384) (h1 : R1 < 16384) (h2 : R2 < 16384)
    (h : N + (16384 * R1 + 2 ^ 28 * R2) = kKeyPart k) :
    kN k = N ∧ kR1 k = R1 ∧ kR2 k = R2 := by
  have hk : kKeyPart k = k % 2 ^ 42 := Nat.and_two_pow_sub_one_eq_mod k 42
  have e0 : kN k = k % 2 ^ 14 := Nat.and_two_pow_sub_one_eq_mod k 14
  have e1 : kR1 k = (k / 2 ^ 14) % 2 ^ 14 := by
    have s : Nat.shiftRight k 14 = k / 2 ^ 14 := Nat.shiftRight_eq_div_pow k 14
    change Nat.land (Nat.shiftRight k 14) 16383 = _
    rw [s]
    exact Nat.and_two_pow_sub_one_eq_mod _ 14
  have e2 : kR2 k = (k / 2 ^ 28) % 2 ^ 14 := by
    have s : Nat.shiftRight k 28 = k / 2 ^ 28 := Nat.shiftRight_eq_div_pow k 28
    change Nat.land (Nat.shiftRight k 28) 16383 = _
    rw [s]
    exact Nat.and_two_pow_sub_one_eq_mod _ 14
  rw [hk] at h
  refine ⟨?_, ?_, ?_⟩ <;> omega

variable {gA : Array (Fin 8)} {dA : Array (Nat × Fin 8)} {dct : List Lin8} {ε : Bool}
  {GT : List (List Nat)} {DPR : List Nat} {LIN DM DO : Nat}

private theorem inv_eq (hT : sTabs gA dA dct ε GT DPR LIN DM DO) :
    sInvs (mul16K GT DPR LIN DM DO) 2048 = Gen.inv16G gA dA dct ε := by
  unfold sInvs Gen.inv16G
  rw [P117.sFilter_eq]
  refine List.filter_congr fun u hu => ?_
  have hu' := List.mem_range.1 hu
  rw [mul16K_eq hT hu' hu']
  simp only [P117.andB_eq, P117.notB_eq, P117.beq_eq, bne, Bool.and_assoc]

private theorem key_eq (hT : sTabs gA dA dct ε GT DPR LIN DM DO) {u : Nat} (hu : u < 2048)
    {k : Nat}
    (hk : Nat.beq (sKey (mul16K GT DPR LIN DM DO) 2048 u) (kKeyPart k) = true) :
    kN k = (Gen.key16G gA dA dct ε u).2.1 ∧ kR1 k = (Gen.key16G gA dA dct ε u).2.2.1 ∧
      kR2 k = (Gen.key16G gA dA dct ε u).2.2.2 := by
  have hk' := Nat.eq_of_beq_eq_true hk
  rw [sKey_eq] at hk'
  have hC : ((List.range 2048).filter fun p =>
      mul16K GT DPR LIN DM DO p u == mul16K GT DPR LIN DM DO u p) =
      Gen.cent16G gA dA dct ε u := by
    unfold Gen.cent16G
    refine List.filter_congr fun p hp => ?_
    have hp' := List.mem_range.1 hp
    rw [mul16K_eq hT hp' hu, mul16K_eq hT hu hp']
  rw [hC] at hk'
  have hmem : ∀ p ∈ Gen.cent16G gA dA dct ε u, p < 2048 := fun p hp =>
    List.mem_range.1 (List.mem_filter.1 hp).1
  have hR1 : (Gen.cent16G gA dA dct ε u).countP
      (fun p => mul16K GT DPR LIN DM DO p p == u) =
      Gen.cntR16G gA dA dct ε (Gen.cent16G gA dA dct ε u) u := by
    unfold Gen.cntR16G
    refine List.countP_congr fun p hp => ?_
    rw [mul16K_eq hT (hmem p hp) (hmem p hp)]
  have hR2 : (Gen.cent16G gA dA dct ε u).countP
      (fun p => mul16K GT DPR LIN DM DO p p == 256) =
      Gen.cntR16G gA dA dct ε (Gen.cent16G gA dA dct ε u) 256 := by
    unfold Gen.cntR16G
    refine List.countP_congr fun p hp => ?_
    rw [mul16K_eq hT (hmem p hp) (hmem p hp)]
  rw [hR1, hR2] at hk'
  have hlen : (Gen.cent16G gA dA dct ε u).length ≤ 2048 := by
    unfold Gen.cent16G
    exact (List.length_filter_le _ _).trans (by simp)
  have l1 : Gen.cntR16G gA dA dct ε (Gen.cent16G gA dA dct ε u) u ≤
      (Gen.cent16G gA dA dct ε u).length := List.countP_le_length
  have l2 : Gen.cntR16G gA dA dct ε (Gen.cent16G gA dA dct ε u) 256 ≤
      (Gen.cent16G gA dA dct ε u).length := List.countP_le_length
  simp only [Gen.key16G]
  clear hC hmem hR1 hR2 hk
  generalize (Gen.cent16G gA dA dct ε u).length = N at hk' hlen l1 l2 ⊢
  generalize Gen.cntR16G gA dA dct ε (Gen.cent16G gA dA dct ε u) u = R1 at hk' l1 ⊢
  generalize Gen.cntR16G gA dA dct ε (Gen.cent16G gA dA dct ε u) 256 = R2 at hk' l2 ⊢
  exact key_read k N R1 R2 (by omega) (by omega) (by omega) hk'

private theorem wit_sound (hT : sTabs gA dA dct ε GT DPR LIN DM DO) {u : Nat} (hu : u < 2048)
    {p w : Nat} (hp : p < 2048) (hw : w < 2048)
    (hc : mul16K GT DPR LIN DM DO p u = mul16K GT DPR LIN DM DO u p)
    (hpp : Nat.beq (mul16K GT DPR LIN DM DO p p) 0 = false)
    (hww : Nat.beq (mul16K GT DPR LIN DM DO w u)
      (mul16K GT DPR LIN DM DO (mul16K GT DPR LIN DM DO u (mul16K GT DPR LIN DM DO p p)) w) =
      true) : Gen.conjSq16G gA dA dct ε u = true := by
  have hlt := mul16G_lt hT
  have e1 : mul16K GT DPR LIN DM DO p p = Gen.mul16G gA dA dct ε p p := mul16K_eq hT hp hp
  have e2 : mul16K GT DPR LIN DM DO u (Gen.mul16G gA dA dct ε p p) =
      Gen.mul16G gA dA dct ε u (Gen.mul16G gA dA dct ε p p) := mul16K_eq hT hu (hlt _ _)
  have e3 : mul16K GT DPR LIN DM DO (Gen.mul16G gA dA dct ε u (Gen.mul16G gA dA dct ε p p)) w =
      Gen.mul16G gA dA dct ε (Gen.mul16G gA dA dct ε u (Gen.mul16G gA dA dct ε p p)) w :=
    mul16K_eq hT (hlt _ _) hw
  have e4 : mul16K GT DPR LIN DM DO w u = Gen.mul16G gA dA dct ε w u := mul16K_eq hT hw hu
  rw [mul16K_eq hT hp hu, mul16K_eq hT hu hp] at hc
  rw [e1] at hpp hww
  rw [e2, e3, e4] at hww
  unfold Gen.conjSq16G
  refine List.any_eq_true.2 ⟨p, ?_, ?_⟩
  · unfold Gen.cent16G
    exact List.mem_filter.2 ⟨List.mem_range.2 hp, by simp [hc]⟩
  · have h0 : (Gen.mul16G gA dA dct ε p p == 0) = false := hpp
    rw [Bool.and_eq_true]
    refine ⟨by simp [bne, h0], List.any_eq_true.2 ⟨w, List.mem_range.2 hw, ?_⟩⟩
    exact hww

private theorem all_range {n : Nat} {f g : Nat → Bool} (h : allN n f = true)
    (hfg : ∀ i < n, f i = true → g i = true) : (List.range n).all g = true := by
  rw [List.all_eq_true]
  intro i hi
  exact hfg i (List.mem_range.1 hi) (((allN_iff n f).1 h) i (List.mem_range.1 hi))

private theorem all_map_key (KG : Nat → Nat × Nat × Nat × Nat) (INVL : List Nat)
    (P : Nat × Nat × Nat × Nat → Bool) :
    ((INVL.map KG).all P = true) ↔ ∀ i < INVL.length, P (KG (INVL.getD i 0)) = true := by
  rw [List.all_eq_true]
  constructor
  · intro h i hi
    exact h _ (List.mem_map.2 ⟨_, getD_mem hi, rfl⟩)
  · intro h a ha
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 ha
    obtain ⟨i, hi, rfl⟩ := mem_getD hu
    exact h i hi

theorem check16_sound (gA : Array (Fin 8)) (dA : Array (Nat × Fin 8)) (dct : List Lin8) (ε : Bool)
    (GT : List (List Nat)) (DPR : List Nat) (LIN DM DO : Nat) (INVL KEYL : List Nat)
    (hT : sTabs gA dA dct ε GT DPR LIN DM DO)
    (hI : INVL = sInvs (mul16K GT DPR LIN DM DO) 2048)
    (hK : ∀ i < INVL.length, Nat.beq (sKey (mul16K GT DPR LIN DM DO) 2048 (INVL.getD i 0))
      (kKeyPart (KEYL.getD i 0)) = true)
    (hF : kFin16 (mul16K GT DPR LIN DM DO) INVL KEYL = true) :
    Gen.check16G gA dA dct ε = true := by
  have hlt := mul16G_lt hT
  have hI' : INVL = Gen.inv16G gA dA dct ε := hI.trans (inv_eq hT)
  have hmemI : ∀ u ∈ INVL, u < 2048 := by
    intro u hu
    rw [hI'] at hu
    unfold Gen.inv16G at hu
    exact List.mem_range.1 (List.mem_filter.1 hu).1
  have hrd := fun i (hi : i < INVL.length) =>
    key_eq hT (hmemI _ (getD_mem hi)) (hK i hi)
  unfold kFin16 at hF
  simp only [P117.andB_iff] at hF
  obtain ⟨-, h1, h2, h3, h4, h5⟩ := hF
  unfold Gen.check16G
  rw [← hI']
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [all_map_key]
    intro i hi
    rw [all_map_key]
    intro j hj
    have h := (sAllPairs_iff _ _ _).1 h1 i hi j hj
    obtain ⟨a1, a2, a3⟩ := hrd i hi
    obtain ⟨b1, b2, b3⟩ := hrd j hj
    rw [a1, a2, a3, b1, b2, b3] at h
    simp only [P117.orB_eq, P117.notB_eq, P117.andB_eq, P117.beq_eq] at h
    simpa [bne, Bool.and_assoc] using h
  · rw [all_map_key]
    intro i hi
    have h := (sZipAll_iff _ _ _).1 h2 i hi
    obtain ⟨a1, a2, a3⟩ := hrd i hi
    by_cases hc : (Gen.key16G gA dA dct ε (INVL.getD i 0)).2.1 = 128
    · rw [a1, hc] at h
      have hu := hmemI _ (getD_mem hi)
      rw [P117.orB_eq, Bool.or_eq_true] at h
      rcases h with h | h
      · simp [P117.notB_eq] at h
      · simp only [P117.andB_iff, P117.notB_iff, P117.blt_eq, decide_eq_true_eq] at h
        obtain ⟨hp, hw, hc', hpp, hww⟩ := h
        have := wit_sound hT hu hp hw (Nat.eq_of_beq_eq_true hc') hpp hww
        try dsimp only
        rw [Bool.or_eq_true]
        exact Or.inr this
    · have : ((Gen.key16G gA dA dct ε (INVL.getD i 0)).2.1 != 128) = true := by simpa using hc
      try dsimp only
      rw [this, Bool.true_or]
  · have s : ∀ x, Nat.shiftRight x 9 = x / 512 := fun x => Nat.shiftRight_eq_div_pow x 9
    refine all_range h3 fun p hp hf => ?_
    have hp' : p < 2048 := hp
    try dsimp only at hf ⊢
    rw [mul16K_eq hT hp' hp', mul16K_eq hT (by decide) (hlt _ _), s] at hf
    exact hf
  · have s : ∀ x, Nat.shiftRight x 9 = x / 512 := fun x => Nat.shiftRight_eq_div_pow x 9
    rw [all_map_key]
    intro i hi
    have h := (sZipAll_iff _ _ _).1 h4 i hi
    obtain ⟨a1, a2, a3⟩ := hrd i hi
    rw [a1] at h
    simp only [Gen.key16G] at h ⊢
    simp only [P117.orB_eq, P117.notB_eq, P117.beq_eq, s] at h
    simpa [bne] using h
  · refine all_range h5 fun p hp hf => ?_
    have hp' : p < 2048 := hp
    try dsimp only at hf ⊢
    rw [mul16K_eq hT hp' (by decide), mul16K_eq hT (by decide) hp'] at hf
    exact hf

end CFSG.KC.GMS.SM

end
