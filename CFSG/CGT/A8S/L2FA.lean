module

public import CFSG.CGT.A8S.L2Alpha

public section

namespace CFSG.CGT.A8S.L2

open CFSG.CosetTable CFSG.CGT.A8S.N0

@[expose] def isInvNotT (c : ℕ) : Bool := Nat.beq (cmul c c) 2184 && !isTc c

@[expose] def faData : List (ℕ × ℕ × Bool) :=
  [(672, 2024, false), (674, 2025, true), (677, 2025, false), (679, 2024, true),
   (992, 1256, false), (995, 1256, true), (997, 1257, false), (998, 1257, true),
   (1288, 3056, false), (1289, 3058, true), (1294, 3058, false), (1295, 3056, true),
   (1336, 880, false), (1339, 1264, true), (1341, 880, true), (1342, 881, false),
   (1712, 888, false), (1714, 889, true), (1717, 888, true), (1719, 889, false),
   (1864, 2488, false), (1865, 2490, true), (1870, 2488, true), (1871, 2490, false),
   (2128, 3544, false), (2131, 3545, false), (2132, 3545, true), (2135, 3544, true),
   (2200, 784, false), (2202, 785, false), (2204, 784, true), (2206, 785, true),
   (2216, 1952, false), (2218, 1953, true), (2220, 1953, false), (2222, 1952, true),
   (2232, 816, false), (2234, 817, true), (2236, 816, true), (2238, 817, false),
   (2248, 3400, false), (2249, 3402, false), (2252, 3402, true), (2253, 3400, true),
   (2416, 1272, false), (2419, 1272, true), (2420, 1273, true), (2423, 1273, false),
   (2440, 1120, false), (2441, 1120, true), (2444, 1122, false), (2445, 1122, true),
   (2472, 1248, false), (2475, 1248, true), (2476, 1249, false), (2479, 1249, true),
   (2504, 1128, false), (2505, 1128, true), (2508, 1130, true), (2509, 1130, false),
   (2696, 2184, false), (2697, 2188, false), (2698, 2184, true), (2699, 2188, true),
   (2760, 2440, false), (2761, 2442, false), (2766, 2440, true), (2767, 2442, true),
   (3208, 2768, false), (3209, 2772, true), (3210, 2772, false), (3211, 2768, true),
   (3224, 848, false), (3226, 849, false), (3229, 848, true), (3231, 849, true),
   (3664, 856, false), (3667, 857, false), (3669, 856, true), (3670, 2456, true),
   (3720, 2200, false), (3721, 2204, true), (3722, 2200, true), (3723, 2204, false)]

@[expose] def faOK (c : ℕ) (p : ℕ × ℕ × Bool) : Bool :=
  Nat.beq p.1 c && validC p.2.1 &&
    Nat.beq (cmul p.2.1 (if p.2.2 then 2698 else 2696)) (cmul c p.2.1)

theorem fa_check : allCodes.all (fun c => !isInvNotT c || faData.any (faOK c)) = true := by
  decide +kernel

theorem avc_xa : avc (PresentedGroup.of 0) = 2696 := by
  rw [← mkW_single, avc_mk]
  decide +kernel

theorem inv_classA8 (x : PG 5 relsN0A8) (hx : x * x = 1)
    (hxT : x ∉ T0) : ∃ n : PG 5 relsN0A8, n * b0 * n⁻¹ = x ∨ n * alphaA8 b0 * n⁻¹ = x := by
  have h := List.all_eq_true.1 fa_check (avc x) (avc_mem_allCodes x)
  have hinv : isInvNotT (avc x) = true := by
    simp only [isInvNotT, Bool.and_eq_true, Nat.beq_eq, Bool.not_eq_true']
    refine ⟨by rw [← avc_mul, hx, avc_one], ?_⟩
    rw [Bool.eq_false_iff]
    intro h'
    exact hxT ((mem_T0_iff x).2 h')
  rw [hinv] at h
  simp only [Bool.not_true, Bool.false_or, List.any_eq_true] at h
  obtain ⟨⟨c', m, b⟩, -, hp⟩ := h
  simp only [faOK, Bool.and_eq_true, Nat.beq_eq] at hp
  obtain ⟨⟨-, hv⟩, he⟩ := hp
  obtain ⟨n, rfl⟩ := exists_avc_eq_of_validC hv
  refine ⟨n, ?_⟩
  cases b
  · right
    rw [alphaA8_b0]
    have e : n * PresentedGroup.of 0 = x * n := mul_eq_mul_of_cmul (by rw [avc_xa]; exact he)
    rw [e, mul_inv_cancel_right]
  · left
    have e : n * b0 = x * n := mul_eq_mul_of_cmul (by rw [avc_b0]; exact he)
    rw [e, mul_inv_cancel_right]

end CFSG.CGT.A8S.L2
