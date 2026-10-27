module

public import CFSG.CGT.Stroth77.Extension22FourC4

public section

namespace CFSG.CGT.Stroth77

variable {S : Type*} [Group S] [Finite S] {B C S' : Subgroup S} {m : ℕ}

theorem fourB_eq_bot_of_m_zero {D : StrothTypeData B (StrothTypeIndex.t100 0)} :
    fourB D = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  obtain ⟨z, hz⟩ := (mem_fourB_iff D).mp hx
  have hz4 : (4 : ℕ) • z = 0 := by
    rw [← addOrderOf_dvd_iff_nsmul_eq_zero]
    have h := addOrderOf_dvd_natCard z
    rw [natCard_torus] at h
    convert h using 1
    rw [show (StrothTypeIndex.t100 0).k 0 = 0 from by
        simpa [StrothTypeIndex.k] using k100_zero 0,
      show (StrothTypeIndex.t100 0).k 1 = 1 from by
        simpa [StrothTypeIndex.k] using k100_one 0,
      show (StrothTypeIndex.t100 0).k 2 = 1 from by
        simpa [StrothTypeIndex.k] using k100_two 0]
    norm_num
  have hec : D.ec x = 0 := hz ▸ hz4
  exact D.ec_injective (by simpa using hec)

theorem phiR_fixed_eq_zero_of_m_zero {x : Torus (Type100.k 0)}
    (h : (Type100.action 0).φρ x = x) : x = 0 := by
  obtain ⟨a, b, c, rfl⟩ := torus_eq_zsmul_gens (Type100.k 0) x
  rw [type100_rho_apply_gens] at h
  have h2 := congrFun h 2
  rw [gens_apply_two (k := Type100.k 0) (a := a - 2 * c) (b := -c) (c := b - c),
    gens_apply_two (k := Type100.k 0) (a := a) (b := b) (c := c)] at h2
  have hb2 : ((b : ℤ) : ZMod (2 ^ Type100.k 0 2)) = 0 := by
    rw [Int.cast_sub] at h2
    have hb2' : ((b : ℤ) : ZMod (2 ^ Type100.k 0 2)) =
        2 * ((c : ℤ) : ZMod (2 ^ Type100.k 0 2)) := by
      calc ((b : ℤ) : ZMod (2 ^ Type100.k 0 2))
          = ((b : ℤ) : ZMod (2 ^ Type100.k 0 2)) - ((c : ℤ) : ZMod (2 ^ Type100.k 0 2)) +
              ((c : ℤ) : ZMod (2 ^ Type100.k 0 2)) := by ring
        _ = ((c : ℤ) : ZMod (2 ^ Type100.k 0 2)) +
              ((c : ℤ) : ZMod (2 ^ Type100.k 0 2)) := by rw [h2]
        _ = 2 * ((c : ℤ) : ZMod (2 ^ Type100.k 0 2)) := by ring
    have h2eq : (2 : ZMod (2 ^ Type100.k 0 2)) = 0 := by
      rw [show Type100.k 0 2 = 1 from k100_two 0]
      decide
    rw [hb2', h2eq, zero_mul]
  have hb1 : ((b : ℤ) : ZMod (2 ^ Type100.k 0 1)) = 0 := by
    have hk : Type100.k 0 2 = Type100.k 0 1 := by rw [k100_two, k100_one]
    exact hk ▸ hb2
  have h1 := congrFun h 1
  rw [gens_apply_one (k := Type100.k 0) (a := a - 2 * c) (b := -c) (c := b - c),
    gens_apply_one (k := Type100.k 0) (a := a) (b := b) (c := c)] at h1
  have hc1 : ((c : ℤ) : ZMod (2 ^ Type100.k 0 1)) = 0 := by
    have hc1' : -((c : ℤ) : ZMod (2 ^ Type100.k 0 1)) =
        ((b : ℤ) : ZMod (2 ^ Type100.k 0 1)) := by
      simpa using h1
    rw [hb1] at hc1'
    simpa using hc1'
  have hc2 : ((c : ℤ) : ZMod (2 ^ Type100.k 0 2)) = 0 := by
    have hk : Type100.k 0 1 = Type100.k 0 2 := by rw [k100_two, k100_one]
    exact hk ▸ hc1
  have h0 : a • gen (Type100.k 0) 0 = 0 := by
    rw [zsmul_gen_eq_zero, show Type100.k 0 0 = 0 from k100_zero 0]
    change ((a : ℤ) : ZMod 1) = 0
    exact Subsingleton.elim _ _
  have h1z : b • gen (Type100.k 0) 1 = 0 := by
    rw [zsmul_gen_eq_zero]
    exact hb1
  have h2z : c • gen (Type100.k 0) 2 = 0 := by
    rw [zsmul_gen_eq_zero]
    exact hc2
  rw [h0, h1z, h2z, zero_add, zero_add]

theorem t100_fixed_rho_t_mod_four_of_mem_zero
    {D : StrothTypeData B (StrothTypeIndex.t100 0)} {y : B}
    (hρ : conjBy D.ρ_mem y * y⁻¹ ∈ fourB D) :
    y ∈ fourB D := by
  rw [fourB_eq_bot_of_m_zero] at hρ
  have hρy : conjBy D.ρ_mem y = y := by
    have hmem : conjBy D.ρ_mem y * y⁻¹ = 1 := by simpa using hρ
    exact mul_inv_eq_one.mp hmem
  have hfix : D.ec y = 0 := by
    have h := D.ρ_conj y
    rw [hρy] at h
    exact phiR_fixed_eq_zero_of_m_zero h.symm
  have hy : y = 1 := D.ec_injective (by rw [hfix, D.ec_one])
  rw [hy]
  exact (fourB D).one_mem

theorem not_isCyclic_quotient_four {m : ℕ}
    (hB : HasStrothType B (StrothTypeIndex.t100 m))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 4 * Nat.card B)
    (hL : hB.data.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') :
    letI : (B.subgroupOf C).Normal :=
      Subgroup.normal_of_le_center (subgroupOf_le_center hBC hC)
    ¬ IsCyclic (C ⧸ B.subgroupOf C) := by
  letI : (B.subgroupOf C).Normal :=
    Subgroup.normal_of_le_center (subgroupOf_le_center hBC hC)
  intro hcycQ
  classical
  let D := hB.data
  have hcomm : ∀ x y : C, x * y = y * x :=
    comm_of_le_centralizer_of_cyclic_quotient hBC hC hcycQ
  letI : CommGroup C := { mul_comm := hcomm }
  obtain ⟨q₀, hq₀⟩ := hcycQ.exists_generator
  obtain ⟨z, hzq⟩ := QuotientGroup.mk'_surjective (B.subgroupOf C) q₀
  let q : C ⧸ B.subgroupOf C := QuotientGroup.mk' (B.subgroupOf C) z
  have hQcard : Nat.card (C ⧸ B.subgroupOf C) = 4 :=
    card_quotient_four hBC hC hrel
  have hq_gen : Subgroup.zpowers q = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hqq : q = q₀ := hzq
    rw [hqq]
    exact hq₀ y
  have hq_order : orderOf q = 4 := by
    rw [orderOf_eq_card_of_zpowers_eq_top hq_gen, hQcard]
  have hq4 : q ^ 4 = 1 := by
    rw [← hq_order]
    exact pow_orderOf_eq_one q
  have hz4H : z ^ 4 ∈ B.subgroupOf C := by
    have h : QuotientGroup.mk' (B.subgroupOf C) (z ^ 4) = 1 := by
      simpa [q, map_pow] using hq4
    exact (QuotientGroup.eq_one_iff _).mp h
  have hz4B : (z : S) ^ 4 ∈ B := by
    have := Subgroup.mem_subgroupOf.mp hz4H
    simpa using this
  have hq2 : q ^ 2 ≠ 1 := by
    intro h
    have hdvd : orderOf q ∣ 2 := (orderOf_dvd_iff_pow_eq_one).mpr h
    rw [hq_order] at hdvd
    norm_num at hdvd
  have hAutSq : ∀ σ : MulAut (C ⧸ B.subgroupOf C), σ * σ = 1 := by
    intro σ
    have hcard : Nat.card (MulAut (C ⧸ B.subgroupOf C)) = 2 := by
      rw [IsCyclic.card_mulAut (C ⧸ B.subgroupOf C), hQcard]
      decide
    have h : orderOf σ ∣ 2 := by
      rw [← hcard]
      exact orderOf_dvd_natCard σ
    simpa [pow_two] using (orderOf_dvd_iff_pow_eq_one).mp h
  have huvC : D.uv ∈ Subgroup.normalizer C := hL D.uv_mem_L
  have htC : D.t ∈ Subgroup.normalizer C := hL D.t_mem_L
  have hρC : D.ρ ∈ Subgroup.normalizer C := hL D.ρ_mem_L
  let Auv : MulAut (C ⧸ B.subgroupOf C) := conjByAutQuotient D.uv huvC D.uv_mem
  let At : MulAut (C ⧸ B.subgroupOf C) := conjByAutQuotient D.t htC D.t_mem
  let Ar : MulAut (C ⧸ B.subgroupOf C) := conjByAutQuotient D.ρ hρC D.ρ_mem
  have hAuv_sq : Auv * Auv = 1 := by
    have h := conjByAutQuotient_pow D.uv huvC D.uv_mem 2
    simpa [pow_two, D.uv_sq, conjByAutQuotient_one] using h.symm
  have hAt_sq : At * At = 1 := by
    have h := conjByAutQuotient_pow D.t htC D.t_mem 2
    simpa [pow_two, D.t_sq, conjByAutQuotient_one] using h.symm
  have hAr_cube : Ar ^ 3 = 1 := by
    have h := conjByAutQuotient_pow D.ρ hρC D.ρ_mem 3
    have hρ3 : D.ρ * (D.ρ * D.ρ) = 1 := by
      rw [← mul_assoc]
      exact D.rho_cube
    simpa [pow_three, mul_assoc, hρ3, conjByAutQuotient_one] using h.symm
  have hcomp1 : (conjByHom D.ρ hρC).comp (conjByHom D.uv huvC) =
      (conjByHom D.t htC).comp (conjByHom D.ρ hρC) := by
    have h1 := conjByHom_mul D.uv D.ρ huvC hρC
    have h2 := conjByHom_mul D.ρ D.t hρC htC
    have h3 : conjByHom (D.uv * D.ρ) (Subgroup.mul_mem _ huvC hρC) =
        conjByHom (D.ρ * D.t) (Subgroup.mul_mem _ hρC htC) :=
      conjByHom_mul_eq huvC hρC hρC htC D.uv_rho
    calc (conjByHom D.ρ hρC).comp (conjByHom D.uv huvC)
        = conjByHom (D.uv * D.ρ) (Subgroup.mul_mem _ huvC hρC) := h1.symm
      _ = conjByHom (D.ρ * D.t) (Subgroup.mul_mem _ hρC htC) := h3
      _ = (conjByHom D.t htC).comp (conjByHom D.ρ hρC) := h2
  have hcomp2 : (conjByHom D.ρ hρC).comp (conjByHom D.t htC) =
      (conjByHom D.t htC).comp ((conjByHom D.uv huvC).comp (conjByHom D.ρ hρC)) := by
    have h1 := conjByHom_mul D.t D.ρ htC hρC
    have h2 := conjByHom_mul (D.ρ * D.uv) D.t (Subgroup.mul_mem _ hρC huvC) htC
    have h3 := conjByHom_mul D.ρ D.uv hρC huvC
    have h4 : conjByHom (D.t * D.ρ) (Subgroup.mul_mem _ htC hρC) =
        conjByHom ((D.ρ * D.uv) * D.t) (Subgroup.mul_mem _ (Subgroup.mul_mem _ hρC huvC) htC) :=
      conjByHom_mul_eq htC hρC (Subgroup.mul_mem _ hρC huvC) htC D.t_rho
    calc (conjByHom D.ρ hρC).comp (conjByHom D.t htC)
        = conjByHom (D.t * D.ρ) (Subgroup.mul_mem _ htC hρC) := h1.symm
      _ = conjByHom ((D.ρ * D.uv) * D.t)
            (Subgroup.mul_mem _ (Subgroup.mul_mem _ hρC huvC) htC) := h4
      _ = (conjByHom D.t htC).comp (conjByHom (D.ρ * D.uv)
            (Subgroup.mul_mem _ hρC huvC)) := h2
      _ = (conjByHom D.t htC).comp ((conjByHom D.uv huvC).comp (conjByHom D.ρ hρC)) := by
            rw [h3]
  have hAr : Ar = 1 := by
    have hsq := hAutSq Ar
    calc Ar = Ar * 1 := (mul_one Ar).symm
      _ = Ar * (Ar * Ar) := by rw [hsq]
      _ = Ar * Ar * Ar := by rw [← mul_assoc]
      _ = Ar ^ 3 := by rw [pow_three, mul_assoc]
      _ = 1 := hAr_cube
  have hAuv_Ar : Ar * Auv = At * Ar := by
    apply MulEquiv.ext
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      simp only [Ar, Auv, At, MulAut.mul_apply, conjByAutQuotient_apply_mk]
      exact congrArg QuotientGroup.mk (by simpa using DFunLike.congr_fun hcomp1 x)
  have hAt_Ar : Ar * At = At * Auv * Ar := by
    apply MulEquiv.ext
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      simp only [Ar, Auv, At, MulAut.mul_apply, conjByAutQuotient_apply_mk]
      exact congrArg QuotientGroup.mk
        (by simpa [MonoidHom.comp_apply] using DFunLike.congr_fun hcomp2 x)
  have hAuv_eq_At : Auv = At := by
    simpa [hAr] using hAuv_Ar
  have hAuv : Auv = 1 := by
    have h := hAt_Ar
    rw [hAr] at h
    have h' : At = At * Auv := by simpa using h
    have h'' : At * At = At * (At * Auv) := congrArg (fun x => At * x) h'
    rw [← mul_assoc] at h''
    have h''' : (1 : MulAut (C ⧸ B.subgroupOf C)) = Auv := by
      simpa [hAt_sq] using h''
    exact h'''.symm
  have hAt : At = 1 := hAuv_eq_At.symm.trans hAuv
  obtain ⟨bρ, hbρ⟩ := exists_mul_of_conjByAutQuotient_eq_one hρC D.ρ_mem hAr z
  obtain ⟨bt, hbt⟩ := exists_mul_of_conjByAutQuotient_eq_one htC D.t_mem hAt z
  have hcommρ : Commute (z : S) (bρ : S) := by
    have h := mul_comm (⟨(z : S), z.2⟩ : C) ⟨(bρ : S), hBC bρ.2⟩
    exact congrArg Subtype.val h
  have hcommt : Commute (z : S) (bt : S) := by
    have h := mul_comm (⟨(z : S), z.2⟩ : C) ⟨(bt : S), hBC bt.2⟩
    exact congrArg Subtype.val h
  have hρfix : conjBy D.ρ_mem (⟨(z : S) ^ 4, hz4B⟩ : B) *
      (⟨(z : S) ^ 4, hz4B⟩ : B)⁻¹ ∈ fourB D :=
    conjBy_pow_four_mem_fourB D.ρ_mem z bρ hz4B hbρ hcommρ
  have htfix : conjBy D.t_mem (⟨(z : S) ^ 4, hz4B⟩ : B) *
      (⟨(z : S) ^ 4, hz4B⟩ : B)⁻¹ ∈ fourB D :=
    conjBy_pow_four_mem_fourB D.t_mem z bt hz4B hbt hcommt
  have hcases : (⟨(z : S) ^ 4, hz4B⟩ : B) ∈ fourB D ∨
      (⟨(z : S) ^ 4, hz4B⟩ : B) * D.c ^ (-2 : ℤ) ∈ fourB D := by
    rcases Nat.eq_zero_or_pos m with hm0 | hpos
    · subst hm0
      exact Or.inl (t100_fixed_rho_t_mod_four_of_mem_zero hρfix)
    · exact t100_fixed_rho_t_mod_four_of_mem (m := m) (D := D) hpos hρfix htfix
  rcases hcases with hy4 | hyc2
  · obtain ⟨s, hs⟩ := exists_pow_four_of_mem_fourB D hy4
    let sC : C := ⟨s, hBC s.2⟩
    let yC : C := ⟨(z : S) ^ 4, hBC hz4B⟩
    have hz4C : z ^ 4 = yC := by ext; rfl
    have hsC4 : sC ^ 4 = yC := by
      apply Subtype.ext
      simpa [sC, yC] using congrArg (fun x : B => (x : S)) hs
    let wC : C := z * sC⁻¹
    have hw4 : wC ^ 4 = 1 := by
      calc wC ^ 4 = z ^ 4 * (sC ^ 4)⁻¹ := by
            rw [show wC = z * sC⁻¹ from rfl, mul_pow, inv_pow]
        _ = yC * yC⁻¹ := by rw [hz4C, hsC4]
        _ = 1 := mul_inv_cancel yC
    let winv : C := wC ^ 2
    have hwinv2 : winv * winv = 1 := by
      have h : winv * winv = wC ^ 4 := by
        show (wC ^ 2) * (wC ^ 2) = wC ^ 4
        group
      rw [h, hw4]
    have hwinvS2 : (winv : S) * (winv : S) = 1 := by
      simpa using congrArg (fun x : C => (x : S)) hwinv2
    have hwinv_notB : (winv : S) ∉ B := by
      intro hmem
      have hmemH : winv ∈ B.subgroupOf C := Subgroup.mem_subgroupOf.mpr hmem
      have h1 : QuotientGroup.mk' (B.subgroupOf C) winv = 1 :=
        (QuotientGroup.eq_one_iff winv).mpr hmemH
      have hmkw : QuotientGroup.mk' (B.subgroupOf C) wC = q := by
        have hs1 : QuotientGroup.mk' (B.subgroupOf C) sC = 1 :=
          (QuotientGroup.eq_one_iff sC).mpr (Subgroup.mem_subgroupOf.mpr s.2)
        rw [show wC = z * sC⁻¹ from rfl, map_mul, map_inv, hs1]
        simp [q]
      have hq2eq : q ^ 2 = 1 := by
        rw [← hmkw, ← map_pow]
        simpa [winv] using h1
      exact hq2 hq2eq
    exact hwinv_notB (hH (winv : S) (hcS winv.2) hwinvS2 (hC winv.2))
  · obtain ⟨s, hs⟩ := exists_pow_four_of_mem_fourB D hyc2
    let sC : C := ⟨s, hBC s.2⟩
    let yC : C := ⟨(z : S) ^ 4, hBC hz4B⟩
    let cC : C := ⟨D.c, hBC D.c.2⟩
    have hz4C : z ^ 4 = yC := by ext; rfl
    have hsC4 : sC ^ 4 = yC * cC ^ (-2 : ℤ) := by
      apply Subtype.ext
      simpa [sC, yC, cC] using congrArg (fun x : B => (x : S)) hs
    let wC : C := z * sC⁻¹
    have hw4 : wC ^ 4 = cC ^ 2 := by
      calc wC ^ 4 = z ^ 4 * (sC ^ 4)⁻¹ := by
            rw [show wC = z * sC⁻¹ from rfl, mul_pow, inv_pow]
        _ = yC * (yC * cC ^ (-2 : ℤ))⁻¹ := by rw [hz4C, hsC4]
        _ = cC ^ 2 := by
            have hcinv : (cC ^ (-2 : ℤ))⁻¹ = cC ^ 2 := by
              simpa using (zpow_neg cC (-2 : ℤ)).symm
            rw [mul_inv_rev, hcinv]
            calc yC * (cC ^ 2 * yC⁻¹) = (yC * cC ^ 2) * yC⁻¹ := by rw [mul_assoc]
              _ = (cC ^ 2 * yC) * yC⁻¹ := by rw [mul_comm yC (cC ^ 2)]
              _ = cC ^ 2 * (yC * yC⁻¹) := by rw [mul_assoc]
              _ = cC ^ 2 := by rw [mul_inv_cancel, mul_one]
    let winv : C := wC ^ 2 * cC⁻¹
    have hwinv2 : winv * winv = 1 := by
      have hcomm : Commute (wC ^ 2) (cC⁻¹) := (Commute.all wC cC).pow_left 2 |>.inv_right
      have h : winv * winv = wC ^ 4 * cC ^ (-2 : ℤ) := by
        rw [show winv * winv = (wC ^ 2 * cC⁻¹) ^ 2 by rw [pow_two]]
        rw [hcomm.mul_pow 2, ← pow_mul, inv_pow]
        norm_num
      rw [h, hw4, zpow_neg]
      group
    have hwinvS2 : (winv : S) * (winv : S) = 1 := by
      simpa using congrArg (fun x : C => (x : S)) hwinv2
    have hwinv_notB : (winv : S) ∉ B := by
      intro hmem
      have hmemH : winv ∈ B.subgroupOf C := Subgroup.mem_subgroupOf.mpr hmem
      have h1 : QuotientGroup.mk' (B.subgroupOf C) winv = 1 :=
        (QuotientGroup.eq_one_iff winv).mpr hmemH
      have hmkw : QuotientGroup.mk' (B.subgroupOf C) wC = q := by
        have hs1 : QuotientGroup.mk' (B.subgroupOf C) sC = 1 :=
          (QuotientGroup.eq_one_iff sC).mpr (Subgroup.mem_subgroupOf.mpr s.2)
        rw [show wC = z * sC⁻¹ from rfl, map_mul, map_inv, hs1]
        simp [q]
      have hc1 : QuotientGroup.mk' (B.subgroupOf C) cC = 1 :=
        (QuotientGroup.eq_one_iff cC).mpr (Subgroup.mem_subgroupOf.mpr D.c.2)
      have hq2eq : q ^ 2 = 1 := by
        have hwinv : QuotientGroup.mk' (B.subgroupOf C) winv = q ^ 2 := by
          rw [show winv = wC ^ 2 * cC⁻¹ from rfl, map_mul, map_pow, map_inv, hmkw, hc1]
          simp
        rw [← hwinv]
        exact h1
      exact hq2 hq2eq
    exact hwinv_notB (hH (winv : S) (hcS winv.2) hwinvS2 (hC winv.2))

end CFSG.CGT.Stroth77
