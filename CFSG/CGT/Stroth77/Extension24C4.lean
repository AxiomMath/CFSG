module

public import CFSG.CGT.Stroth77.Extension24Basic
public import CFSG.CGT.Stroth77.Extension22FourC4

public section

namespace CFSG.CGT.Stroth77

variable {S : Type*} [Group S] [Finite S] {B C S' : Subgroup S}

section QuotientAction

variable [hN : (B.subgroupOf C).Normal]

theorem exists_mul_of_conjByAutQuotient_eq_one_Idx4
    (hcomm : ∀ x y : C, x * y = y * x) {g : S} (hgC : g ∈ Subgroup.normalizer C)
        (hgB : g ∈ Subgroup.normalizer B)
    (hA : conjByAutQuotient g hgC hgB = 1) (x : C) :
    ∃ b : B, g⁻¹ * (x : S) * g = (x : S) * (b : S) := by
  classical
  let aC : C := conjByHom g hgC x
  have haC : (aC : S) = g⁻¹ * (x : S) * g := by
    simp [aC, conjByHom, conjBy]
  have hmk : QuotientGroup.mk' (B.subgroupOf C) aC = QuotientGroup.mk' (B.subgroupOf C) x := by
    have h := congrArg (fun σ : MulAut (C ⧸ B.subgroupOf C) =>
      σ (QuotientGroup.mk' (B.subgroupOf C) x)) hA
    simpa [aC, conjByAutQuotient_apply_mk] using h
  have hbH : aC⁻¹ * x ∈ B.subgroupOf C := QuotientGroup.eq.mp hmk
  have hb : aC * x⁻¹ ∈ B.subgroupOf C := by
    have h' : aC * x⁻¹ = (aC⁻¹ * x)⁻¹ := by
      calc aC * x⁻¹ = x⁻¹ * aC := hcomm _ _
        _ = (aC⁻¹ * x)⁻¹ := by rw [mul_inv_rev, inv_inv]
    rw [h']
    exact (B.subgroupOf C).inv_mem hbH
  refine ⟨⟨aC * x⁻¹, hb⟩, ?_⟩
  change g⁻¹ * (x : S) * g = (x : S) * ((aC * x⁻¹ : C) : S)
  rw [← haC]
  have hCeq : aC = x * (aC * x⁻¹) := by
    calc aC = aC * (x⁻¹ * x) := by group
      _ = (aC * x⁻¹) * x := by group
      _ = x * (aC * x⁻¹) := by rw [hcomm (aC * x⁻¹) x]
  simpa using congrArg (fun y : C => (y : S)) hCeq

omit hN in
theorem not_isCyclic_quotient_t300_of_data {n : ℕ}
    [hN : (B.subgroupOf C).Normal]
    (D : StrothTypeData B (StrothTypeIndex.t300 n))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 4 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') :
    ¬ IsCyclic (C ⧸ B.subgroupOf C) := by
  intro hcycQ
  classical
  have hcomm : ∀ x y : C, x * y = y * x :=
    comm_of_le_centralizer_of_cyclic_quotient hBC hC hcycQ
  let : CommGroup C := { mul_comm := hcomm }
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
  obtain ⟨bρ, hbρ⟩ := exists_mul_of_conjByAutQuotient_eq_one_Idx4 hcomm hρC D.ρ_mem hAr z
  obtain ⟨bt, hbt⟩ := exists_mul_of_conjByAutQuotient_eq_one_Idx4 hcomm htC D.t_mem hAt z
  have hcommρ : Commute (z : S) (bρ : S) := by
    have h := hcomm (⟨(z : S), z.2⟩ : C) ⟨(bρ : S), hBC bρ.2⟩
    exact congrArg Subtype.val h
  have hcommt : Commute (z : S) (bt : S) := by
    have h := hcomm (⟨(z : S), z.2⟩ : C) ⟨(bt : S), hBC bt.2⟩
    exact congrArg Subtype.val h
  have hρfix : conjBy D.ρ_mem (⟨(z : S) ^ 4, hz4B⟩ : B) *
      (⟨(z : S) ^ 4, hz4B⟩ : B)⁻¹ ∈ fourB D :=
    conjBy_pow_four_mem_fourB D.ρ_mem z bρ hz4B hbρ hcommρ
  have htfix : conjBy D.t_mem (⟨(z : S) ^ 4, hz4B⟩ : B) *
      (⟨(z : S) ^ 4, hz4B⟩ : B)⁻¹ ∈ fourB D :=
    conjBy_pow_four_mem_fourB D.t_mem z bt hz4B hbt hcommt
  have hy4 : (⟨(z : S) ^ 4, hz4B⟩ : B) ∈ fourB D :=
    t300_fixed_rho_t_mod_four_of_mem D hρfix htfix
  obtain ⟨s, hs⟩ := exists_pow_four_of_mem_fourB D hy4
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

theorem not_isCyclic_quotient_t300 {n : ℕ}
    [hN : (B.subgroupOf C).Normal]
    (hB : HasStrothType B (StrothTypeIndex.t300 n))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 4 * Nat.card B)
    (hL : hB.data.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') :
    ¬ IsCyclic (C ⧸ B.subgroupOf C) :=
  not_isCyclic_quotient_t300_of_data hB.data hBC hC hrel hL hH hcS

end QuotientAction

end CFSG.CGT.Stroth77
