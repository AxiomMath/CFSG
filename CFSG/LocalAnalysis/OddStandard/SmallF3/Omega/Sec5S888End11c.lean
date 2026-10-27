module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888PH5
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888PH6
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888End4h
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888End11b

public section

open CFSG.Open CFSG.Goldschmidt CFSG.GH74.GLS.Th2.P412 Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

theorem pocket_of_hyp (hGold : GoldStmt) (hN11a : S_N11a) (hN11b : S_N11b) (hN11c : S_N11c)
    {H : Type} [Group H] [Finite H] {z : H} {K : Fin 4 → Subgroup H} {T : Subgroup H}
    (hP : PocketHyp z K T) (hz : z ∈ center H) :
    ∃ (P : Subgroup H) (p n : ℕ) (_ : Fact p.Prime), z ∈ P ∧ P.IsSubnormal ∧ 0 < n ∧
      (p ^ n % 8 = 3 ∨ p ^ n % 8 = 5) ∧ IsSL2qMod P p n := by
  classical
  have hz2 : orderOf z = 2 := by
    apply orderOf_eq_prime
    · simpa [pow_two] using hP.quad.z_sq
    · exact hP.quad.z_ne
  haveI hznorm : (zpowers z).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le_of_mem hz)
  let α : H →* H ⧸ zpowers z := QuotientGroup.mk' (zpowers z)
  have hαsurj : Function.Surjective α := QuotientGroup.mk'_surjective _
  have hS : PlaneSetup z K α := ⟨hP.quad, hαsurj, QuotientGroup.ker_mk' _⟩
  haveI : Finite (H ⧸ zpowers z) := Finite.of_surjective α hαsurj
  obtain ⟨T', hT'⟩ := hP.sylow
  let S : Sylow 2 (H ⧸ zpowers z) := T'.mapSurjective hS.surj
  have hST : (S : Subgroup (H ⧸ zpowers z)) = T.map α := by
    change (T'.mapSurjective hS.surj : Subgroup (H ⧸ zpowers z)) = T.map α
    rw [Sylow.coe_mapSurjective, hT']
  rcases xlevel_dichotomy hGold hN11a hN11b hN11c
      (xdata_of_hyp hS hP S hST) (A := fun i => (K i).map α)
      (fun i => map_K_le_normalizer hS i) (fun i => map_K_subnormal hS hP i) with
    ⟨Nn, hNn, hoddNn, hsubNn⟩ | hB
  · haveI : Nn.Normal := hNn
    obtain ⟨P, hzP, hPsub, hSL⟩ :=
      caseA_pocket hz hz2 α hS.surj hS.ker (K := K 0) (hP.quad.iso 0) (hP.quad.z_mem 0)
        hoddNn (hsubNn 0)
    exact ⟨P, 3, 1, Fact.mk Nat.prime_three, hzP, hPsub, by norm_num,
      Or.inl (by norm_num), hSL⟩
  · obtain ⟨Ob, hOb, B, i, p, n, hpFact, hoddOb, hOB, hBsub, hWB, hpOdd, hn, h5, h8, ⟨e⟩⟩ := hB
    haveI : Ob.Normal := hOb
    haveI : Fact p.Prime := hpFact
    have hp2 : p ≠ 2 := by
      rintro rfl
      obtain ⟨k, hk⟩ := hpOdd
      omega
    obtain ⟨a, ha, b, hb, hab⟩ := exists_comm_pair hP.quad i
    have haB : α a ∈ B := hWB (Subgroup.mem_map_of_mem α ha)
    have hbB : α b ∈ B := hWB (Subgroup.mem_map_of_mem α hb)
    obtain ⟨P, hzP, hPsub, hSL⟩ :=
      caseB_pocket hz hz2 α hS.surj hS.ker hoddOb hOB hBsub hp2 h5 e haB hbB hab
    exact ⟨P, p, n, hpFact, hzP, hPsub, hn, h8, hSL⟩

end CFSG.OddStandard.SmallF3.Omega
