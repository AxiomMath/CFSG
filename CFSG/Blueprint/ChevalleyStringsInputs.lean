module

public import CFSG.Blueprint.ChevalleyRoots
public import Certificates.Certificate113

public section

namespace CFSG.Blueprint.Chevalley

theorem sum_cartan_mul_single (τ : Tag) (i : Fin τ.rank) :
    ∑ j, τ.cartan i j * (Pi.single i 1 : Fin τ.rank → ℤ) j = 2 := by
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj])
    (fun h => absurd (Finset.mem_univ i) h)]
  simp [τ.cartan_self]

theorem sum_cartan_mul_reflect (τ : Tag) (i : Fin τ.rank) (v : Fin τ.rank → ℤ) :
    ∑ j, τ.cartan i j * reflect τ i v j = -∑ j, τ.cartan i j * v j := by
  have h : ∀ j, τ.cartan i j * reflect τ i v j = τ.cartan i j * v j -
      (∑ l, τ.cartan i l * v l) * (τ.cartan i j * (Pi.single i 1 : Fin τ.rank → ℤ) j) := by
    intro j
    simp only [reflect, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [Finset.sum_congr rfl (fun j _ => h j), Finset.sum_sub_distrib, ← Finset.mul_sum,
    sum_cartan_mul_single]
  ring

theorem reflect_reflect (τ : Tag) (i : Fin τ.rank) (v : Fin τ.rank → ℤ) :
    reflect τ i (reflect τ i v) = v := by
  conv_lhs => rw [reflect, sum_cartan_mul_reflect]
  rw [reflect]
  ext j
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

@[expose] def reflectHom (τ : Tag) (i : Fin τ.rank) : (Fin τ.rank → ℤ) →+ (Fin τ.rank → ℤ) where
  toFun := reflect τ i
  map_zero' := by simp [reflect]
  map_add' u v := by
    simp only [reflect, Pi.add_apply, mul_add, Finset.sum_add_distrib, add_smul]
    abel

theorem reflectHom_apply (τ : Tag) (i : Fin τ.rank) (v : Fin τ.rank → ℤ) :
    reflectHom τ i v = reflect τ i v :=
  rfl

@[expose] def reflectEquiv (τ : Tag) (i : Fin τ.rank) : (Fin τ.rank → ℤ) ≃+ (Fin τ.rank → ℤ) :=
  { reflectHom τ i with
    invFun := reflect τ i
    left_inv := reflect_reflect τ i
    right_inv := reflect_reflect τ i }

theorem isRoot_reflect_iff {τ : Tag} (i : Fin τ.rank) {v : Fin τ.rank → ℤ} :
    IsRoot τ (reflect τ i v) ↔ IsRoot τ v :=
  ⟨fun h => reflect_reflect τ i v ▸ .reflect i h, fun h => .reflect i h⟩

theorem IsRoot.exists_addMonoidHom_eq_single {τ : Tag} {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) :
    ∃ (j : Fin τ.rank) (f : (Fin τ.rank → ℤ) →+ (Fin τ.rank → ℤ)), f α = Pi.single j 1 := by
  induction hα with
  | basis j => exact ⟨j, AddMonoidHom.id _, rfl⟩
  | reflect i _ ih =>
    obtain ⟨j, f, hf⟩ := ih
    exact ⟨j, f.comp (reflectHom τ i), by simp [reflectHom_apply, reflect_reflect, hf]⟩

theorem IsRoot.eq_one_or_neg_one_of_eq_smul {τ : Tag} {α β : Fin τ.rank → ℤ} {m : ℤ}
    (hα : IsRoot τ α) (h : α = m • β) : m = 1 ∨ m = -1 := by
  obtain ⟨j, f, hf⟩ := hα.exists_addMonoidHom_eq_single
  have hj : m * f β j = 1 := by
    have := congrFun hf j
    rw [h, map_zsmul] at this
    simpa using this
  exact Int.eq_one_or_neg_one_of_mul_eq_one hj

theorem isRoot_smul_single_iff {τ : Tag} (i : Fin τ.rank) (m : ℤ) :
    IsRoot τ (m • Pi.single i 1) ↔ m = 1 ∨ m = -1 := by
  refine ⟨fun h => h.eq_one_or_neg_one_of_eq_smul rfl, ?_⟩
  rintro (rfl | rfl)
  · simpa using isRoot_single τ i
  · simpa using isRoot_neg_single τ i

theorem single_ne_neg_single {τ : Tag} (i : Fin τ.rank) :
    (Pi.single i 1 : Fin τ.rank → ℤ) ≠ -Pi.single i 1 := by
  intro h
  have := congrFun h i
  simp at this

structure StringData (τ : Tag) where
  maxHeight : ℕ
  maxCoord : ℕ
  buckets : List (List ℕ)
  strings : List ℕ

namespace StringData

variable {τ : Tag} (S : StringData τ) (C : RootCertificate τ)

@[expose] def bucket (v : Fin τ.rank → ℤ) : List ℕ :=
  if 0 ≤ height v + S.maxHeight ∧ height v + S.maxHeight ≤ 2 * S.maxHeight then
    S.buckets.getD (height v + S.maxHeight).toNat []
  else []

@[expose] def memDec (v : Fin τ.rank → ℤ) : Bool :=
  (S.bucket v).any fun k => List.ofFn (C.root k) == List.ofFn v

@[expose] def up (k : ℕ) (i : Fin τ.rank) : ℕ :=
  S.strings.getD k 0 / 16 ^ (i : ℕ) % 16 / 4

@[expose] def down (k : ℕ) (i : Fin τ.rank) : ℕ :=
  S.strings.getD k 0 / 16 ^ (i : ℕ) % 16 % 4

@[expose] def window : List ℤ :=
  (List.range (2 * (2 * S.maxCoord + 1) + 1)).map fun n : ℕ => (n : ℤ) - (2 * S.maxCoord + 1)

@[expose] def checkBuckets : Bool :=
  (List.range C.roots.length).all fun k => (S.bucket (C.root k)).contains k

@[expose] def checkBucketBounds : Bool :=
  S.buckets.all fun l => l.all fun k => decide (k < C.roots.length)

@[expose] def checkCoords : Bool :=
  (List.range C.roots.length).all fun k =>
    (List.finRange τ.rank).all fun j => decide (|C.root k j| ≤ (S.maxCoord : ℤ))

@[expose] def checkStrings : Bool :=
  (List.range C.roots.length).all fun k => (List.finRange τ.rank).all fun i =>
    (List.ofFn (C.root k) == List.ofFn (Pi.single i 1 : Fin τ.rank → ℤ)) ||
      (List.ofFn (C.root k) == List.ofFn (-Pi.single i 1 : Fin τ.rank → ℤ)) ||
      (decide (S.up k i + S.down k i ≤ 3) &&
        S.window.all fun m => S.memDec C (C.root k + m • Pi.single i 1) ==
          decide (-(S.down k i : ℤ) ≤ m ∧ m ≤ S.up k i))

@[expose] def check : Bool :=
  S.checkBuckets C && S.checkBucketBounds C && S.checkCoords C && S.checkStrings C

variable {S C}

theorem mem_of_mem_getD {l : List (List ℕ)} {n k : ℕ} (h : k ∈ l.getD n []) :
    ∃ x ∈ l, k ∈ x := by
  rw [List.getD_eq_getElem?_getD] at h
  cases hx : l[n]? with
  | none => simp [hx] at h
  | some x =>
    rw [hx] at h
    exact ⟨x, List.mem_of_getElem? hx, h⟩

theorem memDec_iff (hC : C.check = true) (hS : S.check C = true) {v : Fin τ.rank → ℤ} :
    S.memDec C v = true ↔ IsRoot τ v := by
  simp only [check, Bool.and_eq_true] at hS
  obtain ⟨⟨⟨hb, hbb⟩, -⟩, -⟩ := hS
  simp only [checkBuckets, List.all_eq_true, List.mem_range, List.contains_iff_mem] at hb
  simp only [checkBucketBounds, List.all_eq_true, decide_eq_true_eq] at hbb
  constructor
  · intro h
    simp only [memDec, List.any_eq_true, beq_iff_eq] at h
    obtain ⟨k, hk, hkv⟩ := h
    rw [← RootCertificate.eq_of_ofFn_beq (beq_iff_eq.2 hkv)]
    refine RootCertificate.isRoot_root hC k ?_
    simp only [bucket] at hk
    split_ifs at hk with hr
    · obtain ⟨x, hx, hkx⟩ := mem_of_mem_getD hk
      exact hbb x hx k hkx
    · simp at hk
  · intro hv
    obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq hC hv
    simp only [memDec, List.any_eq_true, beq_iff_eq]
    exact ⟨k, hb k hk, rfl⟩

end StringData

@[expose] def g2StringData : StringData .G2 where
  maxHeight := 5
  maxCoord := 3
  buckets := [[10], [6], [11], [9], [2, 5], [], [0, 1], [4], [8], [3], [7]]
  strings := [192, 4, 48, 52, 145, 1, 193, 1, 96, 100, 4, 144]

@[expose] def f4StringData : StringData .F4 where
  maxHeight := 11
  maxCoord := 4
  buckets := [[46], [42], [38], [47], [34, 45], [29, 41], [23, 28, 37], [20, 32, 33], [14, 26, 27],
    [12, 18, 19], [4, 6, 9, 11], [], [0, 1, 2, 3], [5, 8, 10], [7, 16, 17], [13, 24, 25],
    [15, 21, 31], [22, 36], [30, 40], [44], [35], [39], [43]]
  strings := [64, 2052, 16448, 1024, 16, 2065, 513, 33284, 17684, 4112, 4416, 256, 580, 33345,
    10241, 8196, 17665, 5140, 5441, 17424, 10260, 32784, 8257, 32769, 5121, 20740, 5380, 16705,
    8256, 32788, 10256, 20801, 16644, 21505, 33344, 576, 21520, 21524, 2064, 20, 16640, 20800, 65,
    1, 5376, 5120, 4, 17664]

@[expose] def d4StringData : StringData .D4 where
  maxHeight := 5
  maxCoord := 2
  buckets := [[23], [21], [17, 18, 20], [11, 14, 16], [4, 6, 8, 10], [], [0, 1, 2, 3], [5, 7, 9],
    [12, 13, 15], [19], [22]]
  strings := [1024, 1024, 16452, 1024, 256, 16705, 256, 16660, 4113, 4420, 256, 5140, 16401, 4161,
    5185, 4116, 17425, 4164, 16404, 5137, 16449, 16708, 256, 1024]

@[expose] def e6StringData : StringData .E6 where
  maxHeight := 11
  maxCoord := 3
  buckets := [[71], [69], [67], [64, 65], [59, 60, 63], [53, 54, 57], [46, 47, 50, 51],
    [37, 38, 41, 42, 45], [27, 30, 31, 34, 36], [17, 19, 22, 24, 26], [6, 8, 10, 12, 14, 16], [],
    [0, 1, 2, 3, 4, 5], [7, 9, 11, 13, 15], [18, 20, 21, 23, 25], [28, 29, 32, 33, 35],
    [39, 40, 43, 44], [48, 49, 52], [55, 56, 58], [61, 62], [66], [68], [70]]
  strings := [1024, 16384, 16388, 263232, 4210688, 262144, 256, 16641, 4096, 267280, 4097, 266564,
    65808, 4265024, 1052672, 1130496, 65536, 5124, 266305, 82240, 262420, 4260880, 82961, 4260164,
    1327376, 1053760, 4460544, 81940, 262161, 4259905, 66625, 1311040, 4276500, 1049616, 1311761,
    1048900, 4210960, 65604, 1310740, 4276241, 1048641, 1315905, 4194624, 4198404, 1065236,
    4195345, 1314884, 4194324, 4199425, 1064977, 1064961, 4199489, 1314820, 1065220, 4198468,
    4194560, 1315841, 4276225, 65540, 1049600, 4276484, 1310976, 66561, 262145, 4260864, 262404,
    82176, 267264, 4160, 16400, 16, 64]

@[expose] def e7StringData : StringData .E7 where
  maxHeight := 17
  maxCoord := 4
  buckets := [[125], [123], [121], [119], [116, 117], [112, 113], [107, 108, 109], [101, 102, 103],
    [94, 95, 96, 100], [86, 87, 88, 92], [77, 78, 79, 83, 84], [67, 68, 69, 73, 74],
    [56, 57, 61, 62, 63, 66], [44, 45, 48, 49, 53, 55], [32, 35, 36, 39, 41, 43],
    [20, 22, 25, 27, 29, 31], [7, 9, 11, 13, 15, 17, 19], [], [0, 1, 2, 3, 4, 5, 6],
    [8, 10, 12, 14, 16, 18], [21, 23, 24, 26, 28, 30], [33, 34, 37, 38, 40, 42],
    [46, 47, 50, 51, 52, 54], [58, 59, 60, 64, 65], [70, 71, 72, 75, 76], [80, 81, 82, 85],
    [89, 90, 91, 93], [97, 98, 99], [104, 105, 106], [110, 111], [114, 115], [118], [120], [122],
    [124]]
  strings := [1024, 16384, 16388, 263232, 4210688, 67371008, 4194304, 256, 16641, 4096, 267280,
    4097, 266564, 65808, 4265024, 1052672, 68239360, 16842752, 18087936, 1048576, 5124, 266305,
    82240, 262420, 4260880, 82961, 4260164, 1327376, 68162624, 21237760, 16859136, 71368704, 81940,
    262161, 4259905, 66625, 1311040, 4276500, 68158480, 1311761, 68157764, 20988176, 16782400,
    67375104, 65604, 1310740, 4276241, 68157505, 1315905, 20971840, 4198404, 68174100, 16778256,
    20972561, 16777540, 67125520, 1314884, 20971540, 4199425, 68173841, 16777281, 1064961,
    20976705, 67109184, 68423684, 16793876, 67109905, 1065220, 20975684, 67108884, 4194560,
    68424705, 16793617, 21053441, 67114049, 67174404, 17043460, 1049600, 21053700, 67113028,
    68419840, 67175425, 17044481, 17039361, 67190785, 21037060, 21038080, 17039620, 67191044,
    67191040, 17039616, 21038081, 68419585, 1048580, 17044480, 67175424, 68419844, 67113024,
    21053696, 1049601, 4194305, 16793616, 68424704, 4194564, 67108880, 20975680, 1065216, 16777280,
    68173840, 4199424, 20971536, 1314880, 68157504, 4276240, 1310736, 65600, 4259904, 262160,
    81936, 266304, 5120, 16640, 260, 1025, 1, 4]

@[expose] def e8StringData : StringData .E8 where
  maxHeight := 29
  maxCoord := 6
  buckets := [[239], [237], [235], [233], [231], [229], [226, 227], [222, 223], [218, 219],
    [214, 215], [209, 210, 211], [203, 204, 205], [196, 197, 198, 199], [188, 189, 190, 191],
    [180, 181, 182, 183], [172, 173, 174, 175], [163, 164, 165, 166, 167],
    [153, 154, 155, 156, 157], [142, 143, 144, 145, 146, 152], [130, 131, 132, 133, 134, 140],
    [118, 119, 120, 121, 127, 128], [106, 107, 108, 109, 114, 115],
    [93, 94, 95, 96, 101, 102, 103], [79, 80, 81, 86, 87, 88, 92], [65, 66, 70, 71, 72, 76, 78],
    [51, 52, 55, 56, 60, 62, 64], [37, 40, 41, 44, 46, 48, 50], [23, 25, 28, 30, 32, 34, 36],
    [8, 10, 12, 14, 16, 18, 20, 22], [], [0, 1, 2, 3, 4, 5, 6, 7], [9, 11, 13, 15, 17, 19, 21],
    [24, 26, 27, 29, 31, 33, 35], [38, 39, 42, 43, 45, 47, 49], [53, 54, 57, 58, 59, 61, 63],
    [67, 68, 69, 73, 74, 75, 77], [82, 83, 84, 85, 89, 90, 91], [97, 98, 99, 100, 104, 105],
    [110, 111, 112, 113, 116, 117], [122, 123, 124, 125, 126, 129], [135, 136, 137, 138, 139, 141],
    [147, 148, 149, 150, 151], [158, 159, 160, 161, 162], [168, 169, 170, 171],
    [176, 177, 178, 179], [184, 185, 186, 187], [192, 193, 194, 195], [200, 201, 202],
    [206, 207, 208], [212, 213], [216, 217], [220, 221], [224, 225], [228], [230], [232], [234],
    [236], [238]]
  strings := [1024, 16384, 16388, 263232, 4210688, 67371008, 1077936128, 67108864, 256, 16641,
    4096, 267280, 4097, 266564, 65808, 4265024, 1052672, 68239360, 16842752, 1091829760, 269484032,
    289406976, 16777216, 5124, 266305, 82240, 262420, 4260880, 82961, 4260164, 1327376, 68162624,
    21237760, 1090600960, 339804160, 269746176, 1141899264, 81940, 262161, 4259905, 66625, 1311040,
    4276500, 68158480, 1311761, 68157764, 20988176, 1090524224, 335810560, 268517376, 1078001664,
    65604, 1310740, 4276241, 68157505, 1315905, 20971840, 4198404, 68174100, 1090520080, 20972561,
    1090519364, 335560976, 268440640, 1074008064, 1314884, 20971540, 4199425, 68173841, 1090519105,
    1064961, 20976705, 335544640, 68423684, 1090535700, 268436496, 335545361, 268435780,
    1073758480, 1065220, 20975684, 335544340, 4194560, 68424705, 1090535441, 268435521, 21053441,
    335549505, 1073742144, 67174404, 1090785284, 268452116, 1073742865, 1049600, 21053700,
    335548484, 1073741844, 68419840, 67175425, 1090786305, 268451857, 17039361, 335626241,
    1073747009, 1094778884, 268701700, 21038080, 17039620, 335626500, 1073745988, 67191040,
    1090781440, 1094779905, 268702721, 336855041, 1073823745, 1074790404, 272695300, 17044480,
    335610880, 336855300, 1073824004, 67113024, 1094795520, 268697856, 1074791425, 272696321,
    272629761, 1075052545, 336592900, 16793616, 336860160, 1073808384, 272630020, 1075052804,
    67108880, 1094717504, 1074807040, 272711936, 336593921, 1094713345, 16777220, 16777280,
    336609296, 272634880, 1075057664, 1094713604, 1094713360, 1075056704, 272633920, 336609536,
    16778241, 67108865, 336592960, 272711696, 1074806800, 1094718464, 67109124, 1075052560,
    272629776, 1073807424, 336859200, 16793856, 272695360, 1074790464, 268697616, 1094795280,
    67113984, 1073823760, 336855056, 335609920, 17043520, 268701760, 1094778944, 1090781200,
    67190800, 1073746944, 335626256, 17039376, 21037120, 268452096, 1090785344, 67174464, 68419600,
    1073742084, 335549440, 21053456, 1048640, 268436481, 1090535680, 68423744, 4194320, 1073741825,
    335544580, 20976640, 1064976, 268435460, 1090520065, 68174080, 4198464, 335544321, 20971780,
    1315840, 1090519044, 68158465, 4276480, 20971521, 1310980, 66560, 68157444, 4260865, 262400,
    1310721, 82180, 4259844, 267265, 81921, 4164, 266244, 16401, 5185, 20, 16660, 65, 1041, 320,
    324, 1040, 16656, 5184, 266240, 81920, 4259840, 1310720, 68157440, 20971520, 1090519040,
    335544320, 268435456, 1073741824]
namespace StringData

variable {τ : Tag} {S : StringData τ} {C : RootCertificate τ}

theorem abs_le_maxCoord (hC : C.check = true) (hS : S.check C = true) {v : Fin τ.rank → ℤ}
    (hv : IsRoot τ v) (j : Fin τ.rank) : |v j| ≤ S.maxCoord := by
  simp only [check, Bool.and_eq_true] at hS
  obtain ⟨⟨-, hc⟩, -⟩ := hS
  simp only [checkCoords, List.all_eq_true, List.mem_range, List.mem_finRange, true_implies,
    decide_eq_true_eq] at hc
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq hC hv
  exact hc k hk j

theorem mem_window {m : ℤ} (h : |m| ≤ 2 * S.maxCoord + 1) : m ∈ S.window := by
  have h' := abs_le.1 h
  refine List.mem_map.2 ⟨(m + (2 * S.maxCoord + 1)).toNat, List.mem_range.2 ?_, ?_⟩
  · omega
  · omega

theorem isRoot_root_add_iff (hC : C.check = true) (hS : S.check C = true) {k : ℕ}
    (hk : k < C.roots.length) (i : Fin τ.rank) (hne : C.root k ≠ Pi.single i 1)
    (hne' : C.root k ≠ -Pi.single i 1) :
    S.up k i + S.down k i ≤ 3 ∧ ∀ m : ℤ,
      IsRoot τ (C.root k + m • Pi.single i 1) ↔ -(S.down k i : ℤ) ≤ m ∧ m ≤ S.up k i := by
  have hS' := hS
  simp only [check, Bool.and_eq_true] at hS'
  obtain ⟨-, hs⟩ := hS'
  simp only [checkStrings, List.all_eq_true, List.mem_range, List.mem_finRange, true_implies,
    Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hs
  rcases hs k hk i with (h | h) | ⟨h3, hw⟩
  · exact absurd (List.ofFn_injective h) hne
  · exact absurd (List.ofFn_injective h) hne'
  refine ⟨h3, fun m => ?_⟩
  by_cases hm : |m| ≤ 2 * S.maxCoord + 1
  · rw [← memDec_iff hC hS]
    have := hw m (mem_window hm)
    rw [this]
    simp
  · rw [not_le] at hm
    have hc1 : 1 ≤ (S.maxCoord : ℤ) := by
      have := abs_le_maxCoord hC hS (isRoot_single τ i) i
      simpa using this
    constructor
    · intro hr
      have hb := abs_le_maxCoord hC hS hr i
      have hb' := abs_le_maxCoord hC hS (RootCertificate.isRoot_root hC k hk) i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at hb
      rw [abs_le] at hb hb'
      rw [lt_abs] at hm
      omega
    · rintro ⟨h1, h2⟩
      rw [lt_abs] at hm
      omega

end StringData

@[expose] def Tag.stringData : (τ : Tag) → StringData τ
  | .G2 => g2StringData
  | .F4 => f4StringData
  | .D4 => d4StringData
  | .E6 => e6StringData
  | .E7 => e7StringData
  | .E8 => e8StringData

theorem sSup_setOf_le (p : ℕ) : sSup {k : ℕ | k ≤ p} = p := by
  rw [show {k : ℕ | k ≤ p} = Set.Iic p from rfl, csSup_Iic]

theorem stringUp_single (τ : Tag) (i : Fin τ.rank) : stringUp τ i (Pi.single i 1) = 0 := by
  have : {k : ℕ | IsRoot τ (Pi.single i 1 + (k : ℤ) • Pi.single i 1)} = {k : ℕ | k ≤ 0} := by
    ext k
    simp only [Set.mem_ofPred_eq]
    rw [show (Pi.single i 1 : Fin τ.rank → ℤ) + (k : ℤ) • Pi.single i 1 =
      ((1 : ℤ) + k) • Pi.single i 1 by rw [add_smul, one_smul], isRoot_smul_single_iff]
    omega
  rw [stringUp, this, sSup_setOf_le]

theorem csSup_zero_two : sSup ({0, 2} : Set ℕ) = 2 := by
  rw [csSup_pair]
  rfl

theorem stringDown_single (τ : Tag) (i : Fin τ.rank) : stringDown τ i (Pi.single i 1) = 2 := by
  have : {k : ℕ | IsRoot τ (Pi.single i 1 - (k : ℤ) • Pi.single i 1)} = {0, 2} := by
    ext k
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    rw [show (Pi.single i 1 : Fin τ.rank → ℤ) - (k : ℤ) • Pi.single i 1 =
      ((1 : ℤ) - k) • Pi.single i 1 by rw [sub_smul, one_smul], isRoot_smul_single_iff]
    omega
  rw [stringDown, this, csSup_zero_two]

theorem stringUp_neg_single (τ : Tag) (i : Fin τ.rank) : stringUp τ i (-Pi.single i 1) = 2 := by
  have : {k : ℕ | IsRoot τ (-Pi.single i 1 + (k : ℤ) • Pi.single i 1)} = {0, 2} := by
    ext k
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    rw [show -(Pi.single i 1 : Fin τ.rank → ℤ) + (k : ℤ) • Pi.single i 1 =
      ((-1 : ℤ) + k) • Pi.single i 1 by rw [add_smul, neg_one_smul], isRoot_smul_single_iff]
    omega
  rw [stringUp, this, csSup_zero_two]

theorem stringDown_neg_single (τ : Tag) (i : Fin τ.rank) :
    stringDown τ i (-Pi.single i 1) = 0 := by
  have : {k : ℕ | IsRoot τ (-Pi.single i 1 - (k : ℤ) • Pi.single i 1)} = {k : ℕ | k ≤ 0} := by
    ext k
    simp only [Set.mem_ofPred_eq]
    rw [show -(Pi.single i 1 : Fin τ.rank → ℤ) - (k : ℤ) • Pi.single i 1 =
      ((-1 : ℤ) - k) • Pi.single i 1 by rw [sub_smul, neg_one_smul], isRoot_smul_single_iff]
    omega
  rw [stringDown, this, sSup_setOf_le]

theorem reflect_add_smul_single (τ : Tag) (i : Fin τ.rank) (α : Fin τ.rank → ℤ) (k : ℤ) :
    reflect τ i (α + k • Pi.single i 1) =
      α - ((∑ j, τ.cartan i j * α j) + k) • Pi.single i 1 := by
  have hs : ∑ j, τ.cartan i j * (α + k • (Pi.single i 1 : Fin τ.rank → ℤ)) j =
      (∑ j, τ.cartan i j * α j) + 2 * k := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib]
    rw [show ∑ j, τ.cartan i j * (k * (Pi.single i 1 : Fin τ.rank → ℤ) j) =
      k * ∑ j, τ.cartan i j * (Pi.single i 1 : Fin τ.rank → ℤ) j by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring,
      sum_cartan_mul_single]
    ring
  rw [reflect, hs]
  ext j
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

end CFSG.Blueprint.Chevalley
