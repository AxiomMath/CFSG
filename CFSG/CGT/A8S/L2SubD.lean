module

public import CFSG.CGT.A8S.L2Sub

public section

namespace CFSG.CGT.A8S.L2

open CFSG.CosetTable CFSG.CGT.A8S.N0

theorem mem_normalizer_of_conj_mem {H : Type*} [Group H] [Finite H] {K : Subgroup H} {x : H}
    (h : ∀ b ∈ K, x * b * x⁻¹ ∈ K) : x ∈ Subgroup.normalizer (K : Set H) := by
  rw [Subgroup.mem_normalizer_iff]
  intro b
  refine ⟨h b, fun hb => ?_⟩
  let F : K → K := fun c => ⟨x * c * x⁻¹, h c c.2⟩
  have hF : Function.Injective F := fun c c' e => Subtype.ext (by
    have e' : x * (c : H) * x⁻¹ = x * c' * x⁻¹ := congrArg Subtype.val e
    simpa using e')
  obtain ⟨c, hc⟩ := Finite.injective_iff_surjective.1 hF ⟨_, hb⟩
  have e : x * (c : H) * x⁻¹ = x * b * x⁻¹ := congrArg Subtype.val hc
  have e' : (c : H) = b := by simpa using e
  rw [← e']
  exact c.2

abbrev D0 : Subgroup (PG 5 relsN0A8) := Subgroup.normalizer (B0 : Set (PG 5 relsN0A8))

@[expose] def normB0c (c : ℕ) : Bool :=
  b0Codes.all fun s => b0Codes.any fun s' => Nat.beq (cmul c s) (cmul s' c)

theorem normB0c_of_mem {x : PG 5 relsN0A8} (hx : x ∈ D0) :
    normB0c (avc x) = true := by
  simp only [normB0c, List.all_eq_true, List.any_eq_true, Nat.beq_eq]
  intro s hs
  obtain ⟨b, hb, rfl⟩ := exists_mem_B0 hs
  have hc : x * b * x⁻¹ ∈ B0 := (Subgroup.mem_normalizer_iff.1 hx b).1 hb
  refine ⟨avc (x * b * x⁻¹), (mem_B0_iff _).1 hc, ?_⟩
  rw [← avc_mul, ← avc_mul, inv_mul_cancel_right]

theorem mem_D0_of_normB0c {x : PG 5 relsN0A8}
    (h : normB0c (avc x) = true) : x ∈ D0 := by
  have := finite_pg_relsN0A8
  refine mem_normalizer_of_conj_mem fun b hb => ?_
  simp only [normB0c, List.all_eq_true, List.any_eq_true, Nat.beq_eq] at h
  obtain ⟨s', hs', he⟩ := h _ ((mem_B0_iff b).1 hb)
  obtain ⟨z, hz, rfl⟩ := exists_mem_B0 hs'
  rw [mul_eq_mul_of_cmul he, mul_inv_cancel_right]
  exact hz

@[expose] def d0Codes : List ℕ :=
  [2184, 3160, 2717, 3792, 2645, 3789, 3211, 2765, 2205, 3674, 2133, 3283, 2139, 3740, 3157,
   2257, 3277, 3722, 3282, 2134, 3163, 2699, 2255, 2771, 3668, 2764, 3741, 2137, 3721, 3279,
   3794, 2650, 3228, 2698, 2254, 2718, 3795, 2646, 3675, 2207, 3671, 2770, 3788, 2649, 3156,
   2256, 2185, 2769, 3670, 3231, 2647, 2186, 2767, 2258, 2252, 2697, 2206, 3790, 3208, 2187,
   2766, 3673, 2135, 3720, 3210, 2132, 3159, 2136, 3278, 3161, 2716, 3209, 3230, 2651, 3672,
   3162, 2719, 2259, 3276, 3280, 3743, 3158, 3281, 2648, 2138, 2768, 3793, 2644, 3742, 3791,
   3723, 2696, 2253, 3669, 2204, 3229]

theorem d0Codes_complete : allCodes.all (fun c => !normB0c c || d0Codes.contains c) = true := by
  decide +kernel

theorem d0Codes_sound : d0Codes.all (fun c => validC c && normB0c c) = true := by decide +kernel

theorem avc_mem_d0Codes {x : PG 5 relsN0A8} (hx : x ∈ D0) :
    avc x ∈ d0Codes := by
  have h := List.all_eq_true.1 d0Codes_complete (avc x) (avc_mem_allCodes x)
  rw [normB0c_of_mem hx] at h
  simpa using h

theorem exists_mem_D0 {c : ℕ} (hc : c ∈ d0Codes) :
    ∃ x ∈ D0, avc x = c := by
  have h := List.all_eq_true.1 d0Codes_sound c hc
  simp only [Bool.and_eq_true] at h
  obtain ⟨x, rfl⟩ := exists_avc_eq_of_validC h.1
  exact ⟨x, mem_D0_of_normB0c h.2, rfl⟩

theorem forall_D0 {p : ℕ → Bool} (h : d0Codes.all p = true)
    {x : PG 5 relsN0A8} (hx : x ∈ D0) : p (avc x) = true :=
  List.all_eq_true.1 h _ (avc_mem_d0Codes hx)

end CFSG.CGT.A8S.L2
