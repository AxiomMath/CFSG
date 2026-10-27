module

public import CFSG.ClassicalInvolution.Q3.TL4MF163U3F
public import CFSG.ClassicalInvolution.Q3.TL4MF163U3H
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5L5U5
public import CFSG.ClassicalInvolution.Q3.TL4ExitDichA
public import CFSG.ClassicalInvolution.Q3.TL4MF163LU
public import CFSG.ClassicalInvolution.Q3.TL4MF163U3B

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.MF163.U3

open CFSG CFSG.ClassicalInvolution Matrix CFSG.ClassicalInvolution.Q3.TA3
  CFSG.ClassicalInvolution.Q3.TA3.Q5GL2 CFSG.ClassicalInvolution.Q3.TA3.Q5U3
open CFSG.LocalAnalysis.ComponentInitial CFSG.GH74.GLS.IVK.Proofs2 CFSG.RankThree.CentralCover
  CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartTwo.KFacts
open scoped MatrixGroups

theorem concl163Syl_ge_five {X : Type} [Group X] [Finite X] {R : Subgroup X} {S : Sylow 2 R}
    {z : X}
    (hD : TightDatum R S z) (hq8 : Nonempty ((S : Subgroup R) ≃* QuaternionGroup 2))
    {N : Subgroup X} [N.Normal] [IsSimpleGroup N] (hC : Subgroup.centralizer (N : Set X) = ⊥)
    {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f)
    (e : ↥N ≃* StatedProj (StatedSU 3 (p ^ f) K)) : TL4.Concl163Syl R S z := by
  classical
  have : Finite K := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP K p := h.charP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K p]; exact hp2)
  have hq2 : 2 < p ^ f := by omega
  have hO : Nobq.OutTwoCyclic N := outTwoCyclic_PSU (n := 3)
    ⟨⟨h.prime, h.one_le, le_rfl, fun he => by
      have := congrArg Prod.snd he
      simp only at this
      omega⟩, K, inferInstance, inferInstance, h.card_eq_sq, ⟨e⟩⟩
    ((by decide : Odd 3).of_dvd_nat (Nat.gcd_dvd_left 3 _))
  obtain ⟨hzN, -⟩ := TightDatum.exists_cyclic4_of_outTwoCyclic hD hC hO
  obtain ⟨c, hcS, hcN, hc4⟩ := MF163.exists_cyclic4_mem_sylow hq8 hC hO
  have hcR : c ∈ R := Subgroup.map_subtype_le _ hcS
  obtain ⟨c₀, π, hrange, hk, hπ1, hπ⟩ := exists_frame_formula h hp2 e hzN hD.order
  obtain ⟨E, hE⟩ := exists_std_equiv h e c₀ hπ
  have hπN : ∀ A, π A ∈ N := fun A => by
    have hA : π A ∈ π.range := ⟨A, rfl⟩
    rw [hrange] at hA
    exact hA.1
  have hcs := slCentScalar_GU2 h
  obtain ⟨eJ⟩ := nonempty_slPart_equiv h
  have hF₀card := LieType.Steinberg.card_fixedSubfield h.card_eq_sq
  have hF₀ : Odd (Nat.card (LieType.Steinberg.fixedSubfield K p f)) := by
    rw [hF₀card]
    exact (h.prime.odd_of_ne_two hp2).pow
  have h4 : 4 ≤ Nat.card (LieType.Steinberg.fixedSubfield K p f) := by rw [hF₀card]; omega
  have hRJ := TA3.TightDatum.le_centralizer_of_gl2 hD hrange hk hF₀ h4 eJ
  have hZN : Subgroup.center N = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center N) with h0 | h0
    · exact h0
    · exfalso
      have hzC : z ∈ Subgroup.centralizer (N : Set X) := by
        rw [Subgroup.mem_centralizer_iff]
        intro n hn
        exact congrArg Subtype.val
          (Subgroup.mem_center_iff.mp (h0 ▸ Subgroup.mem_top (⟨z, hzN⟩ : N)) ⟨n, hn⟩)
      rw [hC, Subgroup.mem_bot] at hzC
      have := hD.order
      rw [hzC, orderOf_one] at this
      omega
  have hZ : ∀ y : unitaryPSU h 3, (∀ w, w * y = y * w) → y = 1 := by
    intro y hy
    have hy' : E.symm y ∈ Subgroup.center N := Subgroup.mem_center_iff.mpr fun w => by
      apply E.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hy (E w)
    rw [hZN, Subgroup.mem_bot] at hy'
    rw [← E.apply_symm_apply y, hy', map_one]
  obtain ⟨Ac, hAc, cl, hcl⟩ := MF163.exists_scalar_of_mem hD hrange hk hcs hF₀ h4 eJ hcR hcN
  have hc2 : c * c = z := by
    refine hD.eq_of_orderOf_eq_two (R.mul_mem hcR hcR) ?_
    rw [← sq, orderOf_pow' c (by norm_num), hc4]
    rfl
  set N1 : ↥(GU2Stated (p ^ f) K) := ⟨-1, neg_one_mem_GU2 h⟩ with hN1
  have hker : π (Ac * Ac * N1⁻¹) = 1 := by
    rw [map_mul, map_mul, map_inv, hAc, hπ1, hc2, mul_inv_cancel]
  obtain ⟨ω, hω3, hω⟩ := hk _ hker
  set Al : ↥(GU2Stated (p ^ f) K) := Ac * (Ac * Ac * N1⁻¹) with hAl
  have hπAl : π Al = c := by rw [hAl, map_mul, hker, mul_one, hAc]
  have hAlGL : (Al : GL (Fin 2) K) = GeneralLinearGroup.scalar (Fin 2) (cl * ω) := by
    rw [hAl, Subgroup.coe_mul, hcl, hω, map_mul]
  have hl2 : ((cl * ω : Kˣ) : K) ^ 2 = -1 := by
    have e00 := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K) 0 0) hω
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hcl, hN1, Units.val_mul,
      GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at e00
    simp [Matrix.mul_apply, Fin.sum_univ_two] at e00
    have hω3' : (ω : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hω3, Units.val_one]
    rw [Units.val_mul]
    linear_combination -(ω : K) ^ 2 * e00 - hω3'
  have hlu : h.bar ((cl * ω : Kˣ) : K) * ((cl * ω : Kˣ) : K) = 1 := by
    have hu := (Lemma41aU3.mem_GU2Stated_iff h).mp Al.2
    rw [hAlGL, GeneralLinearGroup.coe_scalar] at hu
    have := congrFun (congrFun hu 0) 0
    simpa [Matrix.scalar_apply, Matrix.mul_apply, Fin.sum_univ_two] using this
  have hEc : E ⟨c, hcN⟩ = ((Lemma41aU3.blkU h Al : unitarySU p f K 3) : unitaryPSU h 3) := by
    rw [← hE Al (hπN Al)]
    congr 1
    exact Subtype.ext hπAl.symm
  obtain ⟨eS⟩ := hq8
  set ιQ : QuaternionGroup 2 →* X :=
    R.subtype.comp ((S : Subgroup R).subtype.comp eS.symm.toMonoidHom) with hιQ
  have hιQi : Function.Injective ιQ :=
    R.subtype_injective.comp (Subtype.val_injective.comp eS.symm.injective)
  have hιQR : ∀ q, ιQ q ∈ R := fun q => ((eS.symm q : (S : Subgroup R)) : R).2
  have hιQz : ιQ (QuaternionGroup.a 2) = z := by
    refine hD.eq_of_orderOf_eq_two (hιQR _) ?_
    rw [orderOf_injective ιQ hιQi]
    exact orderOf_eq_prime (by decide) (by decide)
  obtain ⟨q₀, hq₀N, hq₀⟩ :=
    MF163.exists_quat_not_mem hD hrange hk hcs hF₀ h4 eJ ιQ hιQi hιQR (hιQz ▸ hzN)
  set σ := ιQ q₀ with hσ
  have hσR : σ ∈ R := hιQR q₀
  have hσS : σ ∈ (S : Subgroup R).map R.subtype := ⟨_, (eS.symm q₀).2, rfl⟩
  have hσ2 : σ * σ = z := by rw [hσ, ← map_mul, hq₀, hιQz]
  set s : MulAut (unitaryPSU h 3) := MulAut.congr E (MulAut.conjNormal σ) with hs
  have hEz : E ⟨z, hzN⟩ = ((Lemma41aU3.blkU h N1 : unitarySU p f K 3) : unitaryPSU h 3) := by
    rw [← hE N1 (hπN N1)]
    congr 1
    exact Subtype.ext hπ1.symm
  have hs2 : s * s = MulAut.conj ((Lemma41aU3.blkU h N1 : unitarySU p f K 3) : unitaryPSU h 3) := by
    rw [hs, ← map_mul, ← map_mul, hσ2, congr_conjNormal_of_mem E hzN, hEz]
  have hni : ∀ g : unitarySU p f K 3, s ≠ MulAut.conj (g : unitaryPSU h 3) := by
    intro g hg
    set n := E.symm (g : unitaryPSU h 3) with hn
    have h1 : MulAut.conjNormal (H := N) σ = MulAut.conjNormal (n : X) := by
      apply (MulAut.congr E).injective
      rw [← hs, hg, congr_conjNormal_of_mem E n.2]
      congr 1
      rw [hn, Subtype.coe_eta, MulEquiv.apply_symm_apply]
    have h2 : (n : X)⁻¹ * σ ∈ Subgroup.centralizer (N : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      have := congrArg (fun φ : MulAut N => ((φ ⟨m, hm⟩ : N) : X)) h1
      simp only [MulAut.conjNormal_apply] at this
      calc m * ((n : X)⁻¹ * σ) = (n : X)⁻¹ * ((n : X) * m * (n : X)⁻¹) * σ := by group
        _ = (n : X)⁻¹ * σ * m := by rw [← this]; group
    rw [hC, Subgroup.mem_bot, inv_mul_eq_one] at h2
    exact hq₀N (h2 ▸ n.2)
  obtain ⟨x, hxu, hx2, hx3⟩ := exists_norm_one_gen h h5
  have hx0 : x ≠ 0 := fun h0 => by simp [h0] at hxu
  set Dx : ↥(GU2Stated (p ^ f) K) := ⟨_, dx_mem h hxu hx0⟩ with hDx
  set Wm : ↥(GU2Stated (p ^ f) K) := ⟨_, w_mem h⟩ with hWm
  have hfixJ : ∀ A : ↥(GU2Stated (p ^ f) K), GeneralLinearGroup.det (A : GL (Fin 2) K) = 1 →
      s ((Lemma41aU3.blkU h A : unitarySU p f K 3) : unitaryPSU h 3) =
        ((Lemma41aU3.blkU h A : unitarySU p f K 3) : unitaryPSU h 3) := by
    intro A hA
    have hσA : σ * π A = π A * σ :=
      (Subgroup.mem_centralizer_iff.mp (hRJ hσR) (π A) ⟨A, mem_slPart.mpr hA, rfl⟩).symm
    rw [← hE A (hπN A), hs]
    exact congr_conjNormal_fix E (hπN A) hσA
  have hfx := hfixJ Dx (det_mk2 _ _ _ _ (dx_det hx0))
  have hfw := hfixJ Wm (det_mk2 _ _ _ _ w_det)
  obtain ⟨M, m, m', hsM, hM⟩ := sigma_form h hq2 hs2 hni hxu hx2 hx3 (coe_blkU_dx h hxu hx0)
    (coe_blkU_w h) hfx hfw
  refine MF163.concl163Syl_of_aut hC E fun b hb2 hbK => ?_
  have hbc := hbK c hcS
  rw [congr_conjNormal_of_mem E hcN] at hbc
  have hbfix := fix_of_comm_conj hZ hbc
  rw [hEc] at hbfix
  obtain ⟨G, hbG, z1, z2, z3, z4⟩ :=
    block_of_inv h hq2 h2 hb2 hl2 hlu (coe_blkU_scalar h hAlGL hl2) hbfix
  have hbs := hbK σ hσS
  rw [← hs, hsM, hbG] at hbs
  obtain ⟨A, hdetA, hGA⟩ := blk_of_comm h z1 z2 z3 z4 hM hbs
  have hbA : b = MulAut.congr E (MulAut.conjNormal (π A)) := by
    rw [congr_conjNormal_of_mem E (hπN A), hE A (hπN A), hbG, hGA]
  have hA2 : π A * π A = 1 := by
    set y := E ⟨π A * π A, mul_mem (hπN A) (hπN A)⟩ with hy
    have h1 : MulAut.conj y = 1 := by
      rw [hy, ← congr_conjNormal_of_mem E, map_mul, map_mul, ← hbA, hb2]
    have h3 : y = 1 := hZ y fun w => by
      have := congrArg (fun φ : MulAut (unitaryPSU h 3) => φ w) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc w * y = y * w * y⁻¹ * y := by rw [this]
        _ = y * w := by group
    have h4 : (⟨π A * π A, mul_mem (hπN A) (hπN A)⟩ : N) = 1 := E.map_eq_one_iff.mp h3
    exact congrArg Subtype.val h4
  rcases MF163.eq_of_mul_self_eq_one_of_mem hk h2 (N1 := N1) rfl ⟨A, mem_slPart.mpr hdetA, rfl⟩
    hA2 with h0 | h0
  · left
    rw [hbA, h0, map_one, map_one]
  · right
    rw [hbA, h0, hπ1]

theorem concl163_ge_five {X : Type} [Group X] [Finite X] {R : Subgroup X} {S : Sylow 2 R} {z : X}
    (hD : TightDatum R S z) (hq8 : Nonempty ((S : Subgroup R) ≃* QuaternionGroup 2))
    {N : Subgroup X} [N.Normal] [IsSimpleGroup N] (hC : Subgroup.centralizer (N : Set X) = ⊥)
    {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f)
    (e : ↥N ≃* StatedProj (StatedSU 3 (p ^ f) K)) : TL4.Concl163 R z :=
  MF163.Concl163Syl.concl163 (concl163Syl_ge_five hD hq8 hC h hp2 h5 e)

end CFSG.ClassicalInvolution.Q3.TL4.MF163.U3
