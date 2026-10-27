module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Out1L12Gen
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Out1L12Norm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Out1L12Quot
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Lemma32to34
public import CFSG.GF2Type.Aschbacher1976Common.DihedralEvenRank

public section

namespace CFSG.OddStandard.SmallF3.Omega

variable {S : Type} [Group S]

theorem aor_l12_end [Finite S] (hS : IsPGroup 2 S) {t u : S} (h : L12Main S t u)
    (P : Subgroup S) : ∃ s : Finset S, s.card ≤ 3 ∧ Subgroup.closure (s : Set S) = P := by
  haveI hUnorm : (Subgroup.zpowers u).Normal := aor_l12_normal hS h
  let U : Subgroup S := Subgroup.zpowers u
  let Q := S ⧸ U
  let tbar : Q := (t : Q)
  let A : Subgroup Q := Subgroup.centralizer ({tbar} : Set Q)
  have hQp : IsPGroup 2 Q := hS.to_quotient U
  have hA : Nat.card A = 4 := aor_l12_quot_card h
  have hAab : IsMulCommutative A :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (by rw [hA]; norm_num)
  have hC : Subgroup.centralizer (A : Set Q) = A := by
    apply le_antisymm
    · intro q hq
      rw [Subgroup.mem_centralizer_iff] at hq
      change q ∈ Subgroup.centralizer ({tbar} : Set Q)
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hq tbar (by
        change tbar ∈ Subgroup.centralizer ({tbar} : Set Q)
        exact Subgroup.mem_centralizer_singleton_iff.mpr rfl)).symm
    · intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact congrArg Subtype.val (hAab.is_comm.comm ⟨b, hb⟩ ⟨a, ha⟩)
  have hQ2 : ∀ H : Subgroup Q, ∃ s : Finset Q, s.card ≤ 2 ∧
      Subgroup.closure (s : Set Q) = H := by
    intro H
    rcases HarrisU33.lemma33 hQp A hA hC with
      htop | ⟨m, hm, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨m, hm, ⟨e⟩⟩
    · have hcardQ : Nat.card Q = 4 := by
        rw [← Subgroup.card_top (G := Q), ← htop]
        exact hA
      have hle : Nat.card Q ≤ 2 ^ 2 := by rw [hcardQ]; norm_num
      exact aor_gen_of_card_le (k := 2) hle H
    · haveI : NeZero (2 ^ m) := ⟨pow_ne_zero m two_ne_zero⟩
      exact CFSG.GF2Type.Aschbacher1976Common.twoGen_of_mulEquiv e
        (CFSG.GF2Type.Aschbacher1976Common.twoGen_dihedral (2 ^ m)) H
    · exact CFSG.GF2Type.Aschbacher1976Common.twoGen_of_mulEquiv e
        (CFSG.GF2Type.Aschbacher1976Common.twoGen_semidihedral n hn) H
    · exfalso
      have ht2 : t ^ 2 = 1 := by
        simpa [h.coord.ord_t] using pow_orderOf_eq_one t
      have htbar2 : tbar ^ 2 = 1 := by
        have hmap := map_pow (QuotientGroup.mk' U) t 2
        rw [ht2, map_one] at hmap
        exact hmap.symm
      haveI : NeZero (2 ^ m) := ⟨pow_ne_zero m two_ne_zero⟩
      have hx : (e tbar) ^ 2 = 1 := by
        rw [← map_pow, htbar2, map_one]
      have hcentral : ∀ y : QuaternionGroup (2 ^ m), e tbar * y = y * e tbar :=
        fun y => aor_quat_central (e tbar) hx y
      have htopA : A = ⊤ := by
        rw [eq_top_iff]
        intro q _
        change q ∈ Subgroup.centralizer ({tbar} : Set Q)
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hq := hcentral (e q)
        rw [← map_mul, ← map_mul] at hq
        exact (e.injective hq).symm
      have hcardQ4 : Nat.card Q = 4 := by
        rw [← Subgroup.card_top (G := Q), ← htopA]
        exact hA
      have hcardQuat : Nat.card Q = Nat.card (QuaternionGroup (2 ^ m)) :=
        Nat.card_congr e.toEquiv
      have hge : 8 ≤ Nat.card (QuaternionGroup (2 ^ m)) := by
        rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
        have h2 : 2 ≤ 2 ^ m := by
          calc (2 : ℕ) = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
        omega
      omega
  exact aor_gen_of_quot U hQ2 P

end CFSG.OddStandard.SmallF3.Omega
