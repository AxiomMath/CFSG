module

public import CFSG.LieType.Chevalley.RootOps.Poly
public import CFSG.LieType.Steinberg.Adjoint.Group

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.PlanesTwo

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley.RootWalk

abbrev BM : Type := List ℕ

section Vectors

variable (K : Type) [Field K]

@[expose] noncomputable def vecOfBits (n : ℕ) : RootModule Tag.D4 K :=
  ∑ p ∈ Finset.range 28, if n.testBit p then posVec Tag.D4 K p else 0

variable {K}

theorem vecOfBits_zero : vecOfBits K 0 = 0 := by
  simp [vecOfBits]

theorem vecOfBits_xor (h2 : (2 : K) = 0) (m n : ℕ) :
    vecOfBits K (m ^^^ n) = vecOfBits K m + vecOfBits K n := by
  have hvv : ∀ v : RootModule Tag.D4 K, v + v = 0 := fun v => by
    rw [← two_smul K v, h2, zero_smul]
  unfold vecOfBits
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Nat.testBit_xor]
  cases m.testBit p <;> cases n.testBit p <;> simp [hvv]

theorem vecOfBits_two_pow {p : ℕ} (hp : p < 28) : vecOfBits K (2 ^ p) = posVec Tag.D4 K p := by
  unfold vecOfBits
  rw [Finset.sum_eq_single p]
  · simp
  · intro b _ hb
    rw [Nat.testBit_two_pow]
    simp [Ne.symm hb]
  · intro h
    exact absurd (Finset.mem_range.2 hp) h

end Vectors

section Matrices

variable (K : Type) [Field K]

@[expose] noncomputable def bitOp (M : BM) : Module.End K (RootModule Tag.D4 K) :=
  ∑ c ∈ Finset.range 28, (posCoord Tag.D4 K c).smulRight (vecOfBits K (M.getD c 0))

variable {K}

theorem bitOp_posVec (M : BM) {c : ℕ} (hc : c < 28) :
    bitOp K M (posVec Tag.D4 K c) = vecOfBits K (M.getD c 0) := by
  have hc' : c < dim Tag.D4 := hc
  rw [bitOp, LinearMap.sum_apply, Finset.sum_eq_single c]
  · rw [LinearMap.smulRight_apply, posCoord_posVec hc', if_pos rfl, one_smul]
  · intro b _ hb
    rw [LinearMap.smulRight_apply, posCoord_posVec hc', if_neg hb, zero_smul]
  · intro h
    exact absurd (Finset.mem_range.2 hc) h

theorem getD_range_map (f : ℕ → ℕ) {c : ℕ} (hc : c < 28) :
    ((List.range 28).map f).getD c 0 = f c := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hc]
  rfl

@[expose] def idBM : BM :=
  (List.range 28).map fun c => 2 ^ c

theorem bitOp_idBM : bitOp K idBM = 1 := by
  refine ext_posVec fun c hc => ?_
  have hc' : c < 28 := hc
  rw [bitOp_posVec _ hc', idBM, getD_range_map _ hc', vecOfBits_two_pow hc']
  rfl

@[expose] def badd (A B : BM) : BM :=
  (List.range 28).map fun c => A.getD c 0 ^^^ B.getD c 0

theorem bitOp_badd (h2 : (2 : K) = 0) (A B : BM) :
    bitOp K (badd A B) = bitOp K A + bitOp K B := by
  refine ext_posVec fun c hc => ?_
  have hc' : c < 28 := hc
  rw [bitOp_posVec _ hc', LinearMap.add_apply, bitOp_posVec _ hc', bitOp_posVec _ hc', badd,
    getD_range_map _ hc', vecOfBits_xor h2]

end Matrices

section Entries

variable {K : Type} [Field K]

@[expose] def parityCol (c : ℕ) : List Entry → ℕ
  | [] => 0
  | e :: L => if e.1 = c ∧ e.2.2 % 2 = 1 then parityCol c L ^^^ 2 ^ e.2.1 else parityCol c L

@[expose] def ofEntries (L : List Entry) : BM :=
  (List.range 28).map fun c => parityCol c L

theorem intCast_eq_of_two (h2 : (2 : K) = 0) (z : ℤ) :
    (z : K) = if z % 2 = 1 then 1 else 0 := by
  have hz : z = z % 2 + z / 2 * 2 := (Int.emod_add_ediv_mul z 2).symm
  have hmod : z % 2 = 0 ∨ z % 2 = 1 := Int.emod_two_eq z
  have hcast : (z : K) = ((z % 2 : ℤ) : K) := by
    conv_lhs => rw [hz]
    rw [Int.cast_add, Int.cast_mul, Int.cast_ofNat, h2, mul_zero, add_zero]
  rw [hcast]
  rcases hmod with h | h <;> rw [h] <;> simp

theorem entriesOp_posVec_eq (h2 : (2 : K) = 0) {L : List Entry}
    (hL : ∀ e ∈ L, e.2.1 < 28) {c : ℕ} (hc : c < 28) :
    entriesOp Tag.D4 K L (posVec Tag.D4 K c) = vecOfBits K (parityCol c L) := by
  have hc' : c < dim Tag.D4 := hc
  induction L with
  | nil => simp [parityCol, vecOfBits_zero]
  | cons e L ih =>
    have hL' : ∀ f ∈ L, f.2.1 < 28 := fun f hf => hL f (List.mem_cons_of_mem _ hf)
    have he : e.2.1 < 28 := hL e (List.mem_cons_self ..)
    rw [entriesOp_cons, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smulRight_apply,
      posCoord_posVec hc', ih hL', intCast_eq_of_two h2]
    simp only [parityCol]
    by_cases hec : e.1 = c <;> by_cases hz : e.2.2 % 2 = 1
    · simp only [hec, hz, and_self, if_true, one_smul, vecOfBits_xor h2, vecOfBits_two_pow he]
      exact add_comm _ _
    · simp [hec, hz]
    · simp [hec, hz]
    · simp [hec, hz]

theorem entriesOp_eq_bitOp (h2 : (2 : K) = 0) {L : List Entry} (hL : ∀ e ∈ L, e.2.1 < 28) :
    entriesOp Tag.D4 K L = bitOp K (ofEntries L) := by
  refine ext_posVec fun c hc => ?_
  have hc' : c < 28 := hc
  rw [entriesOp_posVec_eq h2 hL hc', bitOp_posVec _ hc', ofEntries, getD_range_map _ hc']

end Entries

section Roots

variable {K : Type} [Field K]

@[expose] def rootBM (a : ℕ) : BM :=
  badd idBM (badd (ofEntries (entries Tag.D4 a 1))
    (badd (ofEntries (entries Tag.D4 a 2)) (ofEntries (entries Tag.D4 a 3))))

theorem entries_rows_lt {a : ℕ} (ha : a < 24) {k : ℕ} (hk : k ∈ [1, 2, 3]) :
    ∀ e ∈ entries Tag.D4 a k, e.2.1 < 28 := by
  have h := validEntries_of_validB (validB_of_allValid (RootOps.dataChecks Tag.D4).valid
    (a := a) ha hk)
  exact fun e he => (h e he).2

@[expose] def rootTab : List BM := [
  [1, 2, 20, 8, 16, 32, 576, 128, 273, 512, 1024, 67584, 4096, 139264, 16384, 36864, 65536,
    131072, 262144, 8912896, 1048576, 2359296, 5242880, 8388608, 16777216, 50331648, 67108864,
    134217728],
  [1, 2, 36, 8, 16, 32, 2112, 128, 256, 66048, 1058, 2048, 4096, 532480, 16384, 32768, 65536,
    8519680, 266240, 524288, 1048576, 2129920, 4194304, 8388608, 17825792, 37748736, 67108864,
    134217728],
  [65, 66, 4, 72, 528, 2080, 64, 8320, 256, 512, 1024, 2048, 4164, 8192, 16384, 33024, 65536,
    131072, 263168, 524288, 1064960, 2097152, 4194304, 75497472, 16777216, 33554432, 67108864,
    167772160],
  [1, 2, 132, 8, 16, 32, 8256, 128, 256, 131584, 1024, 526336, 4096, 8192, 16520, 32768, 8454144,
    131072, 262144, 524288, 1052672, 2097152, 4227072, 8388608, 17039360, 35651584, 67108864,
    134217728],
  [1, 2, 260, 8, 273, 32, 64, 128, 256, 576, 1024, 2048, 36864, 8192, 16384, 32768, 67584, 139264,
    2359296, 524288, 5242880, 2097152, 4194304, 8912896, 50331648, 33554432, 67108864, 134217728],
  [513, 514, 516, 520, 16, 65568, 64, 131200, 320, 512, 1024, 2048, 4112, 8192, 16384, 33285,
    65536, 131072, 262144, 67633152, 1048576, 2098176, 4210688, 8388608, 16777216, 33554432,
    67108864, 150994944],
  [1, 2, 1028, 8, 16, 1058, 64, 128, 256, 512, 1024, 2112, 266240, 8192, 16384, 2129920, 66048,
    131072, 262144, 532480, 17825792, 2097152, 37748736, 8519680, 16777216, 33554432, 67108864,
    134217728],
  [2049, 2050, 2052, 2056, 65552, 32, 64, 524416, 256, 512, 1088, 2048, 4128, 8192, 16384, 32768,
    65536, 67239936, 264198, 524288, 1048576, 2097408, 4194304, 8388608, 16793600, 33554432,
    67108864, 138412032],
  [4097, 4098, 4, 4104, 16, 32, 4164, 128, 33024, 528, 263168, 2080, 4096, 8320, 1064960, 32768,
    65536, 131072, 262144, 524288, 1048576, 2097152, 4194304, 8388608, 16777216, 167772160,
    75497472, 134217728],
  [8193, 8194, 8196, 8200, 131088, 524320, 64, 128, 256, 512, 1024, 2048, 4224, 8192, 16448,
    32768, 67174400, 131072, 262144, 524288, 1056780, 2097152, 4194560, 8388608, 16778240,
    33554432, 67108864, 136314880],
  [1, 2, 16388, 8, 16, 32, 64, 16520, 256, 512, 1024, 2048, 1052672, 8256, 16384, 4227072, 65536,
    131584, 17039360, 526336, 1048576, 35651584, 4194304, 8454144, 16777216, 33554432, 67108864,
    134217728],
  [32769, 32770, 32772, 32776, 4112, 32, 320, 128, 256, 33285, 2098176, 2048, 4096, 8192, 4210688,
    32768, 65568, 131200, 262144, 524288, 1048576, 2097152, 4194304, 8388608, 150994944, 33554432,
    67633152, 134217728],
  [65537, 65538, 4, 65544, 16, 32, 64, 8388736, 2304, 512, 1536, 2048, 4096, 67117056, 16384,
    32800, 65536, 131072, 262160, 524288, 1048576, 2162695, 4194304, 8388608, 16777216, 33570816,
    67108864, 135266304],
  [131073, 131074, 4, 131080, 16, 8388640, 64, 128, 8448, 512, 1024, 67110912, 4096, 8192, 16896,
    32896, 65536, 131072, 262144, 524288, 1048592, 2097152, 4325389, 8388608, 16777216, 33555456,
    67108864, 134479872],
  [262145, 262146, 262148, 262152, 16, 4128, 1088, 128, 2097408, 512, 1024, 264198, 4096, 8192,
    16793600, 32768, 65552, 131072, 262144, 524416, 1048576, 2097152, 138412032, 8388608,
    16777216, 33554432, 67239936, 134217728],
  [524289, 524290, 4, 524296, 8388624, 32, 64, 128, 256, 67109376, 9216, 2048, 4096, 8192, 18432,
    32768, 65536, 131072, 262272, 524288, 1048608, 2097152, 4194304, 8388608, 17301518, 33554688,
    67108864, 134250496],
  [1048577, 1048578, 1048580, 1048584, 16, 32, 16448, 4224, 4194560, 512, 16778240, 2048, 4096,
    1056780, 16384, 32768, 65536, 131088, 262144, 524320, 1048576, 136314880, 4194304, 8388608,
    16777216, 33554432, 67174400, 134217728],
  [2097153, 2097154, 4, 2097160, 262160, 32800, 64, 128, 256, 1536, 1024, 2304, 4096, 8192,
    33570816, 32768, 2162695, 131072, 262144, 524288, 135266304, 2097152, 4194304, 8388736,
    16777216, 33554432, 67117056, 134217728],
  [4194305, 4194306, 4, 4194312, 1048592, 32, 64, 32896, 256, 16896, 33555456, 2048, 4096, 8448,
    16384, 32768, 65536, 4325389, 134479872, 524288, 1048576, 2097152, 4194304, 8388640, 16777216,
    33554432, 67110912, 134217728],
  [8388609, 8388610, 8388612, 8388616, 16, 32, 67108928, 128, 524544, 512, 132096, 2048, 4096,
    8192, 81920, 32768, 65536, 131072, 262144, 524288, 1048576, 2097280, 4194336, 8388608,
    16777232, 41943055, 67108864, 134221824],
  [16777217, 16777218, 4, 16777224, 16, 1048608, 64, 262272, 33554688, 512, 1024, 18432, 4096,
    9216, 16384, 134250496, 65536, 131072, 262144, 17301518, 1048576, 2097152, 4194304, 8388624,
    16777216, 33554432, 67109376, 134217728],
  [33554433, 33554434, 33554436, 33554440, 16777232, 4194336, 64, 2097280, 256, 512, 1024, 2048,
    134221824, 8192, 16384, 32768, 81920, 132096, 262144, 524544, 1048576, 2097152, 4194304,
    41943055, 16777216, 33554432, 67108928, 134217728],
  [1, 2, 67108868, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 8392704, 8192, 16384, 557056, 65536,
    131072, 393216, 524288, 1114112, 2105344, 4196352, 8388608, 16777728, 33554496, 67108864,
    201326603],
  [1, 2, 134217732, 8, 16, 32, 33554496, 128, 256, 16777728, 1024, 4196352, 4096, 2105344, 16384,
    32768, 1114112, 393216, 262144, 557056, 1048576, 2097152, 4194304, 8392704, 16777216,
    33554432, 201326603, 134217728]]

theorem rootTab_eq : (List.range 24).map rootBM = rootTab := by
  decide +kernel

theorem rootTab_getD {a : ℕ} (ha : a < 24) : rootTab.getD a [] = rootBM a := by
  rw [← rootTab_eq, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ha]
  rfl

@[expose] def rt (a : ℕ) : Fin Tag.D4.rank → ℤ :=
  Tag.D4.rootCertificate.root a

theorem endHom_xPar_rootBM (h2 : (2 : K) = 0) {a : ℕ} (ha : a < 24) :
    endHom K (xPar (rootOperatorFamily Tag.D4) (rt a) (1 : K)) = bitOp K (rootBM a) := by
  have hroot : IsRoot Tag.D4 (rt a) := isRoot_rootCertificate_root ha
  rw [endHom_xPar, RootOperatorFamily'.eltOr_of_isRoot _ _ hroot]
  have hpos : rootPos (⟨rt a, hroot⟩ : Root Tag.D4) = a := rootPos_rootAt ha
  simp only [RootOperatorFamily.elt, one_pow, one_smul, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add]
  change dataD Tag.D4 K ⟨rt a, hroot⟩ 0 + dataD Tag.D4 K ⟨rt a, hroot⟩ 1 +
    dataD Tag.D4 K ⟨rt a, hroot⟩ 2 + dataD Tag.D4 K ⟨rt a, hroot⟩ 3 = _
  simp only [dataD, hpos, show (1 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 0 by omega,
    show (3 : ℕ) ≠ 0 by omega, show (1 : ℕ) ≤ 3 by omega, show (2 : ℕ) ≤ 3 by omega, le_refl,
    ↓reduceIte]
  rw [entriesOp_eq_bitOp h2 (entries_rows_lt ha (by simp)),
    entriesOp_eq_bitOp h2 (entries_rows_lt ha (by simp)),
    entriesOp_eq_bitOp h2 (entries_rows_lt ha (by simp)), rootBM, bitOp_badd h2,
    bitOp_badd h2, bitOp_badd h2, bitOp_idBM]
  abel

end Roots

section NatMatrices

variable (K : Type) [Field K]

@[expose] noncomputable def natOp (M : ℕ) : Module.End K (RootModule Tag.D4 K) :=
  ∑ i ∈ Finset.range 28, ∑ j ∈ Finset.range 28,
    if M.testBit (28 * i + j) then (posCoord Tag.D4 K j).smulRight (posVec Tag.D4 K i) else 0

variable {K}

theorem natOp_posVec (M : ℕ) {c : ℕ} (hc : c < 28) :
    natOp K M (posVec Tag.D4 K c) =
      ∑ i ∈ Finset.range 28, if M.testBit (28 * i + c) then posVec Tag.D4 K i else 0 := by
  have hc' : c < dim Tag.D4 := hc
  rw [natOp, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.sum_apply, Finset.sum_eq_single c]
  · split_ifs
    · rw [LinearMap.smulRight_apply, posCoord_posVec hc', if_pos rfl, one_smul]
    · rfl
  · intro b _ hb
    split_ifs
    · rw [LinearMap.smulRight_apply, posCoord_posVec hc', if_neg hb, zero_smul]
    · rfl
  · intro h
    exact absurd (Finset.mem_range.2 hc) h

theorem bitOp_eq_natOp {A : BM} {M : ℕ}
    (h : ∀ c < 28, ∀ i < 28, (A.getD c 0).testBit i = M.testBit (28 * i + c)) :
    bitOp K A = natOp K M := by
  refine ext_posVec fun c hc => ?_
  have hc' : c < 28 := hc
  rw [bitOp_posVec _ hc', natOp_posVec _ hc', vecOfBits]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [h c hc' i (Finset.mem_range.1 hi)]

@[expose] def rowOf (M j : ℕ) : ℕ :=
  (M >>> (28 * j)) % 2 ^ 28

@[expose] def xorRows (M : ℕ) : List ℕ → ℕ
  | [] => 0
  | j :: js => rowOf M j ^^^ xorRows M js

@[expose] def lmulAux (M : ℕ) : List (List ℕ) → ℕ → ℕ
  | [], _ => 0
  | r :: S, i => (xorRows M r <<< (28 * i)) ^^^ lmulAux M S (i + 1)

@[expose] def lmul (S : List (List ℕ)) (M : ℕ) : ℕ :=
  lmulAux M S 0

@[expose] def idN : ℕ :=
  ((List.range 28).map fun i => 2 ^ (29 * i)).sum

@[expose] def xorAll : List Bool → Bool
  | [] => false
  | b :: bs => xor b (xorAll bs)

theorem testBit_rowOf (M j : ℕ) {c : ℕ} (hc : c < 28) :
    (rowOf M j).testBit c = M.testBit (28 * j + c) := by
  rw [rowOf, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  simp [hc]

theorem xorRows_lt (M : ℕ) (r : List ℕ) : xorRows M r < 2 ^ 28 := by
  induction r with
  | nil => simp [xorRows]
  | cons j r ih => exact Nat.xor_lt_two_pow (Nat.mod_lt _ (by positivity)) ih

theorem testBit_xorRows (M : ℕ) (r : List ℕ) {c : ℕ} (hc : c < 28) :
    (xorRows M r).testBit c = xorAll (r.map fun j => M.testBit (28 * j + c)) := by
  induction r with
  | nil => simp [xorRows, xorAll]
  | cons j r ih => rw [xorRows, Nat.testBit_xor, ih, testBit_rowOf M j hc]; rfl

theorem testBit_lmulAux (M : ℕ) (S : List (List ℕ)) (i₀ : ℕ) {i c : ℕ} (hc : c < 28) :
    (lmulAux M S i₀).testBit (28 * i + c) =
      if i₀ ≤ i then (xorRows M (S.getD (i - i₀) [])).testBit c else false := by
  induction S generalizing i₀ with
  | nil =>
    simp only [lmulAux, Nat.zero_testBit, List.getD_nil, xorRows]
    split_ifs <;> rfl
  | cons r S ih =>
    rw [lmulAux, Nat.testBit_xor, ih, Nat.testBit_shiftLeft]
    rcases lt_trichotomy i i₀ with hlt | heq | hgt
    · have h1 : ¬28 * i₀ ≤ 28 * i + c := by omega
      simp [h1, show ¬i₀ ≤ i by omega, show ¬i₀ + 1 ≤ i by omega]
    · subst heq
      have h1 : 28 * i + c - 28 * i = c := by omega
      simp [h1, show ¬i + 1 ≤ i by omega]
    · have h1 : 28 * i₀ ≤ 28 * i + c := by omega
      have h2 : (xorRows M r).testBit (28 * i + c - 28 * i₀) = false :=
        Nat.testBit_lt_two_pow ((xorRows_lt M r).trans_le (Nat.pow_le_pow_right (by norm_num)
          (by omega)))
      have h3 : i - i₀ = (i - (i₀ + 1)) + 1 := by omega
      simp [h1, h2, show i₀ ≤ i by omega, show i₀ + 1 ≤ i by omega, h3]

theorem testBit_lmul (S : List (List ℕ)) (M : ℕ) {i c : ℕ} (hc : c < 28) :
    (lmul S M).testBit (28 * i + c) =
      xorAll ((S.getD i []).map fun j => M.testBit (28 * j + c)) := by
  rw [lmul, testBit_lmulAux M S 0 hc, if_pos (Nat.zero_le i), Nat.sub_zero,
    testBit_xorRows M _ hc]

theorem testBit_idN : ∀ j < 28, ∀ c < 28, idN.testBit (28 * j + c) = decide (j = c) := by
  decide +kernel

theorem ite_xor_eq_add (h2 : (2 : K) = 0) (a b : Bool) (v : RootModule Tag.D4 K) :
    (if xor a b then v else 0) = (if a then v else 0) + (if b then v else 0) := by
  have hvv : v + v = 0 := by rw [← two_smul K v, h2, zero_smul]
  cases a <;> cases b <;> simp [hvv]

theorem sum_xorAll (h2 : (2 : K) = 0) (M c : ℕ) (r : List ℕ) (hr : ∀ j ∈ r, j < 28)
    (v : RootModule Tag.D4 K) :
    ∑ j ∈ Finset.range 28, (if M.testBit (28 * j + c) then
        (if xorAll (r.map fun j' => decide (j' = j)) then v else 0) else 0) =
      if xorAll (r.map fun j => M.testBit (28 * j + c)) then v else 0 := by
  induction r with
  | nil => simp [xorAll]
  | cons j₀ r ih =>
    have hj₀ : j₀ < 28 := hr j₀ (by simp)
    simp only [List.map_cons, xorAll]
    rw [ite_xor_eq_add h2, ← ih fun j hj => hr j (List.mem_cons_of_mem _ hj)]
    have e : ∀ j, (if M.testBit (28 * j + c) then
        ((if decide (j₀ = j) then v else 0) + (if xorAll (r.map fun j' => decide (j' = j)) then
          v else 0)) else 0) =
        (if M.testBit (28 * j + c) then (if decide (j₀ = j) then v else 0) else 0) +
          (if M.testBit (28 * j + c) then
            (if xorAll (r.map fun j' => decide (j' = j)) then v else 0) else 0) := by
      intro j
      split_ifs <;> simp
    simp only [ite_xor_eq_add h2, e, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single j₀]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · intro h
      exact absurd (Finset.mem_range.2 hj₀) h

theorem natOp_lmul (h2 : (2 : K) = 0) {S : List (List ℕ)} (hS : ∀ r ∈ S, ∀ j ∈ r, j < 28)
    (M : ℕ) : natOp K (lmul S M) = natOp K (lmul S idN) * natOp K M := by
  have hS' : ∀ i, ∀ j ∈ S.getD i [], j < 28 := by
    intro i j hj
    rw [List.getD_eq_getElem?_getD] at hj
    rcases hSi : S[i]? with _ | r
    · rw [hSi] at hj; simp at hj
    · rw [hSi] at hj
      exact hS r (List.mem_of_getElem? hSi) j hj
  refine ext_posVec fun c hc => ?_
  have hc' : c < 28 := hc
  rw [Module.End.mul_apply, natOp_posVec _ hc', natOp_posVec _ hc', map_sum]
  simp only [apply_ite (natOp K (lmul S idN)), map_zero]
  have e1 : ∀ j ∈ Finset.range 28, (if M.testBit (28 * j + c) then
      natOp K (lmul S idN) (posVec Tag.D4 K j) else 0) =
      ∑ i ∈ Finset.range 28, (if M.testBit (28 * j + c) then
        (if xorAll ((S.getD i []).map fun j' => decide (j' = j)) then posVec Tag.D4 K i else 0)
          else 0) := by
    intro j hj
    have hj' := Finset.mem_range.1 hj
    rw [natOp_posVec _ hj']
    split_ifs
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [testBit_lmul _ _ hj',
        List.map_congr_left fun j' hj'' => testBit_idN j' (hS' i j' hj'') j hj']
    · simp
  rw [Finset.sum_congr rfl e1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_xorAll h2 M c _ (hS' i), testBit_lmul _ _ hc']

end NatMatrices

section NatRoots

variable {K : Type} [Field K]

@[expose] def rootRows : List (List (List ℕ)) := [
  [[0, 8], [1], [2], [3], [2, 4, 8], [5], [6], [7], [8], [6, 9], [10], [11], [12, 15], [13], [14],
    [15], [11, 16], [13, 17], [18, 21], [19], [20, 22], [21], [22], [19, 23], [24, 25], [25], [26],
    [27]],
  [[0], [1, 10], [2], [3], [4], [2, 5, 10], [6], [7], [8], [9], [10], [6, 11], [12, 18], [13],
    [14], [15, 21], [9, 16], [17], [18], [13, 19], [20, 24], [21], [22, 25], [17, 23], [24], [25],
    [26], [27]],
  [[0], [1], [2, 12], [3], [4], [5], [0, 1, 3, 6, 12], [7], [8, 15], [4, 9], [10, 18], [5, 11],
    [12], [7, 13], [14, 20], [15], [16], [17], [18], [19], [20], [21], [22], [23], [24], [25, 27],
    [23, 26], [27]],
  [[0], [1], [2], [3, 14], [4], [5], [6], [2, 7, 14], [8], [9], [10], [11], [12, 20], [6, 13],
    [14], [15, 22], [16], [9, 17], [18, 24], [11, 19], [20], [21, 25], [22], [16, 23], [24], [25],
    [26], [27]],
  [[0, 4], [1], [2], [3], [4], [5], [6, 9], [7], [2, 4, 8], [9], [10], [11, 16], [12], [13, 17],
    [14], [12, 15], [16], [17], [18], [19, 23], [20], [18, 21], [20, 22], [23], [24], [24, 25],
    [26], [27]],
  [[0, 15], [1], [2, 15], [3], [4, 12], [5], [6, 8], [7], [8], [0, 1, 2, 3, 9, 15], [10, 21], [11],
    [12], [13], [14, 22], [15], [5, 16], [7, 17], [18], [19], [20], [21], [22], [23], [24, 27],
    [25], [19, 26], [27]],
  [[0], [1, 5], [2], [3], [4], [5], [6, 11], [7], [8], [9, 16], [2, 5, 10], [11], [12], [13, 19],
    [14], [15], [16], [17, 23], [12, 18], [19], [20], [15, 21], [22], [23], [20, 24], [22, 25],
    [26], [27]],
  [[0], [1, 18], [2, 18], [3], [4], [5, 12], [6, 10], [7], [8, 21], [9], [10], [0, 1, 2, 3, 11,
    18], [12], [13], [14, 24], [15], [4, 16], [17], [18], [7, 19], [20], [21], [22, 27], [23],
    [24], [25], [17, 26], [27]],
  [[0], [1], [2, 6], [3], [4, 9], [5, 11], [6], [7, 13], [8], [9], [10], [11], [0, 1, 3, 6, 12],
    [13], [14], [8, 15], [16], [17], [10, 18], [19], [14, 20], [21], [22], [23, 26], [24], [25],
    [26], [25, 27]],
  [[0], [1], [2, 20], [3, 20], [4], [5], [6, 14], [7, 12], [8, 22], [9], [10, 24], [11], [12], [0,
    1, 2, 3, 13, 20], [14], [15], [16], [4, 17], [18], [5, 19], [20], [21, 27], [22], [23], [24],
    [25], [16, 26], [27]],
  [[0], [1], [2], [3, 7], [4], [5], [6, 13], [7], [8], [9, 17], [10], [11, 19], [12], [13], [2, 7,
    14], [15], [16, 23], [17], [18], [19], [12, 20], [21], [15, 22], [23], [18, 24], [21, 25],
    [26], [27]],
  [[0, 9], [1], [2, 9], [3], [4], [5, 16], [6], [7, 17], [6, 8], [9], [10], [11], [4, 12], [13],
    [14], [0, 1, 2, 3, 9, 15], [16], [17], [18], [19, 26], [20], [10, 21], [14, 22], [23], [24],
    [25], [26], [24, 27]],
  [[0, 21], [1, 21], [2, 21], [3], [4, 18], [5, 15], [6], [7], [8], [9, 10], [10], [8, 11], [12],
    [13], [14, 25], [15], [0, 1, 3, 16, 21], [17], [18], [19], [20, 27], [21], [22], [7, 23], [24],
    [25], [13, 26], [27]],
  [[0, 22], [1], [2, 22], [3, 22], [4, 20], [5], [6], [7, 15], [8], [9, 14], [10, 25], [11], [12],
    [8, 13], [14], [15], [16], [0, 1, 3, 17, 22], [18, 27], [19], [20], [21], [22], [5, 23], [24],
    [25], [11, 26], [27]],
  [[0], [1, 11], [2, 11], [3], [4, 16], [5], [6], [7, 19], [8], [9], [6, 10], [11], [5, 12], [13],
    [14], [15], [16], [17, 26], [0, 1, 2, 3, 11, 18], [19], [20], [8, 21], [22], [23], [14, 24],
    [25], [26], [22, 27]],
  [[0], [1, 24], [2, 24], [3, 24], [4], [5, 20], [6], [7, 18], [8, 25], [9], [10], [11, 14], [12],
    [10, 13], [14], [15, 27], [16], [17], [18], [0, 1, 3, 19, 24], [20], [21], [22], [4, 23], [24],
    [25], [9, 26], [27]],
  [[0], [1], [2, 13], [3, 13], [4, 17], [5, 19], [6], [7], [8], [9], [10], [11], [7, 12], [13], [6,
    14], [15], [16, 26], [17], [18], [19], [0, 1, 2, 3, 13, 20], [21], [8, 22], [23], [10, 24],
    [25], [26], [21, 27]],
  [[0, 16], [1, 16], [2, 16], [3], [4], [5], [6], [7, 23], [8, 11], [9], [9, 10], [11], [12], [13,
    26], [14], [5, 15], [16], [17], [4, 18], [19], [20], [0, 1, 3, 16, 21], [22], [23], [24], [14,
    25], [26], [20, 27]],
  [[0, 17], [1], [2, 17], [3, 17], [4], [5, 23], [6], [7], [8, 13], [9], [10], [11, 26], [12],
    [13], [9, 14], [7, 15], [16], [17], [18], [19], [4, 20], [21], [0, 1, 3, 17, 22], [23], [24],
    [10, 25], [26], [18, 27]],
  [[0, 25], [1, 25], [2, 25], [3, 25], [4, 24], [5, 22], [6], [7, 21], [8], [9], [10], [11], [12,
    27], [13], [14], [15], [14, 16], [10, 17], [18], [8, 19], [20], [21], [22], [0, 1, 2, 3, 23,
    25], [24], [25], [6, 26], [27]],
  [[0], [1, 19], [2, 19], [3, 19], [4, 23], [5], [6], [7], [8], [9, 26], [10, 13], [11], [12],
    [13], [11, 14], [15], [16], [17], [7, 18], [19], [5, 20], [21], [22], [23], [0, 1, 3, 19, 24],
    [8, 25], [26], [15, 27]],
  [[0, 23], [1, 23], [2, 23], [3, 23], [4], [5], [6, 26], [7], [8, 19], [9], [10, 17], [11], [12],
    [13], [14, 16], [15], [16], [17], [18], [19], [20], [7, 21], [5, 22], [23], [4, 24], [0, 1, 2,
    3, 23, 25], [26], [12, 27]],
  [[0, 27], [1, 27], [2], [3, 27], [4], [5], [6, 25], [7], [8], [9, 24], [10], [11, 22], [12], [13,
    21], [14], [15], [16, 20], [17, 18], [18], [15, 19], [20], [21], [22], [12, 23], [24], [25],
    [2, 26, 27], [27]],
  [[0, 26], [1, 26], [2], [3, 26], [4], [5], [6], [7], [8], [9], [10], [11], [12, 23], [13], [14],
    [15, 19], [16], [17], [17, 18], [19], [16, 20], [13, 21], [11, 22], [23], [9, 24], [6, 25],
    [26], [2, 26, 27]]]

theorem rootRows_lt : ∀ a < 24, ∀ r ∈ rootRows.getD a [], ∀ j ∈ r, j < 28 := by
  decide +kernel

theorem rootRows_spec : ∀ a < 24, ∀ c < 28, ∀ i < 28,
    ((rootTab.getD a []).getD c 0).testBit i =
      (lmul (rootRows.getD a []) idN).testBit (28 * i + c) := by
  decide +kernel

theorem endHom_xPar_natOp (h2 : (2 : K) = 0) {a : ℕ} (ha : a < 24) :
    endHom K (xPar (rootOperatorFamily Tag.D4) (rt a) (1 : K)) =
      natOp K (lmul (rootRows.getD a []) idN) := by
  rw [endHom_xPar_rootBM h2 ha, ← rootTab_getD ha]
  exact bitOp_eq_natOp (rootRows_spec a ha)

end NatRoots

section Words

variable (K : Type) [Field K]

@[expose] noncomputable def wordG (w : List ℕ) : adjointGroup Tag.D4 K :=
  (w.map fun a => xPar (rootOperatorFamily Tag.D4) (rt a) (1 : K)).prod

@[expose] def wordN : List ℕ → ℕ
  | [] => idN
  | a :: w => lmul (rootRows.getD a []) (wordN w)

variable {K}

theorem wordG_nil : wordG K [] = 1 := rfl

theorem wordG_cons (a : ℕ) (w : List ℕ) :
    wordG K (a :: w) = xPar (rootOperatorFamily Tag.D4) (rt a) (1 : K) * wordG K w := by
  simp [wordG]

theorem wordG_append (v w : List ℕ) : wordG K (v ++ w) = wordG K v * wordG K w := by
  simp [wordG]

theorem natOp_idN : natOp K idN = 1 := by
  refine ext_posVec fun c hc => ?_
  have hc' : c < 28 := hc
  rw [natOp_posVec _ hc', Finset.sum_eq_single c]
  · rw [testBit_idN c hc' c hc']
    simp
  · intro b hb hbc
    rw [testBit_idN b (Finset.mem_range.1 hb) c hc', decide_eq_false hbc]
    rfl
  · intro h
    exact absurd (Finset.mem_range.2 hc') h

theorem endHom_wordG (h2 : (2 : K) = 0) {w : List ℕ} (hw : ∀ a ∈ w, a < 24) :
    endHom K (wordG K w) = natOp K (wordN w) := by
  induction w with
  | nil => rw [wordG_nil, map_one, wordN, natOp_idN]
  | cons a w ih =>
    have ha : a < 24 := hw a (by simp)
    rw [wordG_cons, map_mul, endHom_xPar_natOp h2 ha,
      ih fun b hb => hw b (List.mem_cons_of_mem _ hb), wordN,
      natOp_lmul h2 (rootRows_lt a ha) (wordN w)]

theorem wordG_eq_of_wordN_eq (h2 : (2 : K) = 0) {v w : List ℕ} (hv : ∀ a ∈ v, a < 24)
    (hw : ∀ a ∈ w, a < 24) (h : wordN v = wordN w) : wordG K v = wordG K w := by
  apply endHom_injective
  rw [endHom_wordG h2 hv, endHom_wordG h2 hw, h]

theorem lmulAux_lt (M : ℕ) (S : List (List ℕ)) (i : ℕ) :
    lmulAux M S i < 2 ^ (28 * (i + S.length)) := by
  induction S generalizing i with
  | nil => simp [lmulAux]
  | cons r S ih =>
    rw [lmulAux]
    refine Nat.xor_lt_two_pow ?_ ?_
    · rw [Nat.shiftLeft_eq]
      calc xorRows M r * 2 ^ (28 * i) < 2 ^ 28 * 2 ^ (28 * i) :=
            Nat.mul_lt_mul_of_pos_right (xorRows_lt M r) (by positivity)
        _ = 2 ^ (28 * (i + 1)) := by rw [← pow_add]; ring_nf
        _ ≤ 2 ^ (28 * (i + (r :: S).length)) :=
            Nat.pow_le_pow_right (by norm_num) (by rw [List.length_cons]; omega)
    · have := ih (i + 1)
      calc lmulAux M S (i + 1) < 2 ^ (28 * (i + 1 + S.length)) := this
        _ = 2 ^ (28 * (i + (r :: S).length)) := by rw [List.length_cons, add_assoc, add_comm 1]

theorem rootRows_length : ∀ a < 24, (rootRows.getD a []).length = 28 := by
  decide +kernel

theorem idN_lt : idN < 2 ^ (28 * (0 + 28)) := by
  decide +kernel

theorem wordN_lt {w : List ℕ} (hw : ∀ a ∈ w, a < 24) : wordN w < 2 ^ (28 * (0 + 28)) := by
  cases w with
  | nil => exact idN_lt
  | cons a w =>
    rw [wordN, lmul]
    have := lmulAux_lt (wordN w) (rootRows.getD a []) 0
    rwa [rootRows_length a (hw a (by simp))] at this

theorem posCoord_natOp {M p c : ℕ} (hp : p < 28) (hc : c < 28) :
    posCoord Tag.D4 K p (natOp K M (posVec Tag.D4 K c)) =
      if M.testBit (28 * p + c) then 1 else 0 := by
  rw [natOp_posVec _ hc, map_sum, Finset.sum_eq_single p]
  · split_ifs
    · rw [posCoord_posVec (show p < dim Tag.D4 from hp), if_pos rfl]
    · exact map_zero _
  · intro b hb hbp
    split_ifs
    · rw [posCoord_posVec (show b < dim Tag.D4 from Finset.mem_range.1 hb), if_neg (Ne.symm hbp)]
    · exact map_zero _
  · intro h
    exact absurd (Finset.mem_range.2 hp) h

set_option exponentiation.threshold 800 in
theorem eq_of_natOp_eq {M M' : ℕ} (hM : M < 2 ^ (28 * (0 + 28)))
    (hM' : M' < 2 ^ (28 * (0 + 28))) (h : natOp K M = natOp K M') : M = M' := by
  refine Nat.eq_of_testBit_eq fun n => ?_
  by_cases hn : n < 28 * (0 + 28)
  · have hp : n / 28 < 28 := by omega
    have hc : n % 28 < 28 := Nat.mod_lt _ (by norm_num)
    have hn' : n = 28 * (n / 28) + n % 28 := (Nat.div_add_mod n 28).symm
    have e := congrArg (fun f => posCoord Tag.D4 K (n / 28) (f (posVec Tag.D4 K (n % 28)))) h
    simp only [posCoord_natOp hp hc] at e
    rw [hn']
    cases h1 : M.testBit (28 * (n / 28) + n % 28) <;>
      cases h2 : M'.testBit (28 * (n / 28) + n % 28) <;> rw [h1, h2] at e <;>
      first
      | rfl
      | exact absurd e (by simp)
  · have hn2 : 28 * (0 + 28) ≤ n := Nat.le_of_not_lt hn
    rw [Nat.testBit_lt_two_pow (hM.trans_le (Nat.pow_le_pow_right (by norm_num) hn2)),
      Nat.testBit_lt_two_pow (hM'.trans_le (Nat.pow_le_pow_right (by norm_num) hn2))]

theorem wordN_eq_of_wordG_eq (h2 : (2 : K) = 0) {v w : List ℕ} (hv : ∀ a ∈ v, a < 24)
    (hw : ∀ a ∈ w, a < 24) (h : wordG K v = wordG K w) : wordN v = wordN w := by
  have e := congrArg (endHom K) h
  rw [endHom_wordG h2 hv, endHom_wordG h2 hw] at e
  exact eq_of_natOp_eq (wordN_lt hv) (wordN_lt hw) e

end Words

end CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.PlanesTwo
