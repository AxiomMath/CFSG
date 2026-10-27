module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdBasic

public section

namespace CFSG.QuasithinUnique.Id2519

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

section Dihedral

theorem dihedral_two_involutions (m : ℕ) (hm : 2 ≤ m) :
    ∃ a b : DihedralGroup (2 * m), a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b ∧ a * a = 1 ∧ b * b = 1 ∧
      a * b = b * a := by
  have : NeZero (2 * m) := ⟨by omega⟩
  have h2m : ((2 * m : ℕ) : ZMod (2 * m)) = 0 := ZMod.natCast_self _
  have hmm : ((m : ℕ) : ZMod (2 * m)) + (m : ZMod (2 * m)) = 0 := by
    rw [← Nat.cast_add, ← two_mul, h2m]
  have hneg : -((m : ℕ) : ZMod (2 * m)) = (m : ZMod (2 * m)) := by
    rw [neg_eq_iff_add_eq_zero]; exact hmm
  refine ⟨DihedralGroup.r (m : ZMod (2 * m)), DihedralGroup.sr 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    rw [DihedralGroup.one_def] at h
    have h1 : (m : ZMod (2 * m)) = 0 := DihedralGroup.r.inj h
    rw [ZMod.natCast_eq_zero_iff] at h1
    have := Nat.le_of_dvd (by omega) h1
    omega
  · intro h
    rw [DihedralGroup.one_def] at h
    cases h
  · intro h
    cases h
  · simp [DihedralGroup.r_mul_r, hmm]
  · simp
  · simp [DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r, hneg]

end Dihedral

section Semidihedral

theorem semidihedral_two_involutions :
    ∃ a b : SemidihedralGroup 4, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b ∧ a * a = 1 ∧ b * b = 1 ∧
      a * b = b * a := by
  have hr8 : orderOf (CFSG.Semidihedral.r 4) = 8 := by
    rw [CFSG.Semidihedral.orderOf_r 4 (by norm_num)]
    norm_num [CFSG.Semidihedral.modulus]
  have hs2 : orderOf (CFSG.Semidihedral.s 4) = 2 := CFSG.Semidihedral.orderOf_s 4 (by norm_num)
  set r := CFSG.Semidihedral.r 4 with hrdef
  set s := CFSG.Semidihedral.s 4 with hsdef
  have hconj : s * r * s⁻¹ = r ^ 3 := by
    have := CFSG.Semidihedral.s_conj_r 4
    simpa using this
  have hr8' : r ^ 8 = 1 := by rw [← hr8]; exact pow_orderOf_eq_one r
  have hs2' : s ^ 2 = 1 := by
    have h := pow_orderOf_eq_one s
    rw [hs2] at h
    exact h
  refine ⟨r ^ 4, s, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact pow_ne_one_of_lt_orderOf (by norm_num) (by rw [hr8]; norm_num)
  · intro h
    rw [h, orderOf_one] at hs2
    omega
  · intro h
    have hsmem : s ∈ Subgroup.zpowers r := by
      rw [← h]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers r) _
    have htop : Subgroup.zpowers r = ⊤ := by
      rw [eq_top_iff, ← PresentedGroup.closure_range_of (semidihedralRels 4), Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact Subgroup.mem_zpowers r
      · exact hsmem
    have hcard := CFSG.Semidihedral.card 4 (by norm_num)
    have : Nat.card (Subgroup.zpowers r) = 8 := by rw [Nat.card_zpowers, hr8]
    rw [htop, Subgroup.card_top, hcard] at this
    omega
  · rw [← pow_add]; simpa using (show r ^ (4 + 4) = 1 from hr8')
  · rw [← sq]; exact hs2'
  · have h1 : s * r ^ 4 * s⁻¹ = (r ^ 3) ^ 4 := by
      rw [← hconj, conj_pow]
    have h2 : (r ^ 3) ^ 4 = r ^ 4 := by
      rw [← pow_mul]
      calc r ^ (3 * 4) = r ^ 8 * r ^ 4 := by rw [← pow_add]
        _ = r ^ 4 := by rw [hr8', one_mul]
    rw [h2] at h1
    have := congrArg (fun y => y * s) h1
    simp only [inv_mul_cancel_right] at this
    exact this.symm

end Semidihedral

section Shape

variable {G : Type} [Group G]

theorem exists_two_involutions_of_shape {X : Subgroup G} (hX2 : IsPGroup 2 X)
    (hshape : IsDihedralOrSemidihedralShape X) :
    ∃ a b : G, a ∈ X ∧ b ∈ X ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b ∧ a * a = 1 ∧ b * b = 1 ∧
      a * b = b * a := by
  have key : ∀ (a b : ↥X), a ≠ 1 → b ≠ 1 → a ≠ b → a * a = 1 → b * b = 1 → a * b = b * a →
      ∃ a b : G, a ∈ X ∧ b ∈ X ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b ∧ a * a = 1 ∧ b * b = 1 ∧
        a * b = b * a := by
    intro a b ha1 hb1 hab haa hbb hc
    refine ⟨a, b, a.2, b.2, fun h => ha1 (Subtype.ext h), fun h => hb1 (Subtype.ext h),
      fun h => hab (Subtype.ext h), congrArg Subtype.val haa, congrArg Subtype.val hbb,
      congrArg Subtype.val hc⟩
  rcases hshape with ⟨n, hn, ⟨e⟩⟩ | e
  · have hD : IsPGroup 2 (DihedralGroup n) := hX2.of_equiv e
    have : NeZero n := ⟨by omega⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hD (DihedralGroup.r 1)
    rw [DihedralGroup.orderOf_r_one] at hk
    have hk2 : 2 ≤ k := by
      by_contra hlt
      push Not at hlt
      interval_cases k <;> omega
    obtain ⟨m, hm⟩ : ∃ m, n = 2 * m := ⟨2 ^ (k - 1), by
      rw [hk]
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk2
      rw [show 2 + j - 1 = j + 1 by omega, pow_succ]
      ring⟩
    subst hm
    have hm2 : 2 ≤ m := by omega
    obtain ⟨a, b, ha1, hb1, hab, haa, hbb, hc⟩ := dihedral_two_involutions m hm2
    refine key (e.symm a) (e.symm b) ?_ ?_ ?_ ?_ ?_ ?_
    · intro h; apply ha1; simpa using congrArg e h
    · intro h; apply hb1; simpa using congrArg e h
    · intro h; apply hab; simpa using congrArg e h
    · rw [← map_mul, haa, map_one]
    · rw [← map_mul, hbb, map_one]
    · rw [← map_mul, ← map_mul, hc]
  · obtain ⟨e⟩ := e
    obtain ⟨a, b, ha1, hb1, hab, haa, hbb, hc⟩ := semidihedral_two_involutions
    refine key (e.symm a) (e.symm b) ?_ ?_ ?_ ?_ ?_ ?_
    · intro h; apply ha1; simpa using congrArg e h
    · intro h; apply hb1; simpa using congrArg e h
    · intro h; apply hab; simpa using congrArg e h
    · rw [← map_mul, haa, map_one]
    · rw [← map_mul, hbb, map_one]
    · rw [← map_mul, ← map_mul, hc]

theorem exists_four_of_shape {X : Subgroup G} (hX2 : IsPGroup 2 X)
    (hshape : IsDihedralOrSemidihedralShape X) :
    ∃ E : Subgroup G, E ≤ X ∧ IsFourSubgroup E := by
  obtain ⟨a, b, ha, hb, ha1, hb1, hab, haa, hbb, hc⟩ := exists_two_involutions_of_shape hX2 hshape
  refine ⟨Subgroup.closure {a, b}, ?_, isFourSubgroup_closure_pair haa hbb hc ha1 hb1 hab⟩
  rw [Subgroup.closure_le]
  rintro x (rfl | hx)
  · exact ha
  · rw [Set.mem_singleton_iff.mp hx]; exact hb

end Shape

end CFSG.QuasithinUnique.Id2519
