module

public import CFSG.CGT.PushingUpLit.SolKR2.FirstHalfB
public import CFSG.CGT.PushingUpLit.SolKR2.FirstCore
public import CFSG.CGT.PushingUpLit.SolKR2.Lines

public section

namespace CFSG.CGT.PushingUpLit.SolKR2

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n.Tim78
open CFSG.RankThree.GF2n (conjSubgroup_mul conjSubgroup_eq_self_iff isTI_conjSubgroup)
open CFSG.RankThree.PartTwo (omegaOneSub omegaOneSub_le)

variable {G : Type} [Group G]

theorem conj_mul_of_mul_self {x : G} (hx : x * x = 1) (p q : G) :
    x * (p * q) * x = (x * p * x) * (x * q * x) := by
  calc x * (p * q) * x = x * p * 1 * q * x := by group
    _ = x * p * (x * x) * q * x := by rw [hx]
    _ = (x * p * x) * (x * q * x) := by group

theorem commute_of_mul_B₀ {B₀ : Subgroup G} (hB₀c : ∀ x ∈ B₀, ∀ y ∈ B₀, x * y = y * x)
    (hB₀2 : ∀ b ∈ B₀, b * b = 1) {a d u : G} (ha : a * a = 1) (hd : d * d = 1)
    (haB : ∀ b ∈ B₀, a * b = b * a) (hdB : ∀ b ∈ B₀, d * b = b * d)
    (hau : a * u * a * u⁻¹ ∈ B₀) (hdu : d * u * d * u⁻¹ ∈ B₀) :
    (a * d * a * d) * u = u * (a * d * a * d) := by
  have hab : ∀ b ∈ B₀, a * b * a = b := fun b hb => by
    rw [haB b hb, mul_assoc, ha, mul_one]
  have hdb : ∀ b ∈ B₀, d * b * d = b := fun b hb => by
    rw [hdB b hb, mul_assoc, hd, mul_one]
  set ba := a * u * a * u⁻¹ with hba
  set bd := d * u * d * u⁻¹ with hbd
  have e_a : a * u * a = ba * u := by rw [hba]; group
  have e_d : d * u * d = bd * u := by rw [hbd]; group
  have s1 : a * (d * u * d) * a = bd * (ba * u) := by
    rw [e_d, conj_mul_of_mul_self ha, hab bd hdu, e_a]
  have s2 : d * (a * (d * u * d) * a) * d = ba * u := by
    rw [s1, conj_mul_of_mul_self hd, hdb bd hdu, conj_mul_of_mul_self hd, hdb ba hau, e_d]
    calc bd * (ba * (bd * u)) = (bd * ba * bd) * u := by group
      _ = (ba * (bd * bd)) * u := by rw [hB₀c bd hdu ba hau]; group
      _ = ba * u := by rw [hB₀2 bd hdu, mul_one]
  have s3 : a * (d * (a * (d * u * d) * a) * d) * a = u := by
    rw [s2, conj_mul_of_mul_self ha, hab ba hau, e_a]
    calc ba * (ba * u) = (ba * ba) * u := by group
      _ = u := by rw [hB₀2 ba hau, one_mul]
  have hz : (a * d * a * d) * u * (d * a * d * a) = u := by
    have : (a * d * a * d) * u * (d * a * d * a) = a * (d * (a * (d * u * d) * a) * d) * a := by
      group
    rw [this, s3]
  have hzz : (a * d * a * d) * (d * a * d * a) = 1 := by
    calc (a * d * a * d) * (d * a * d * a) = a * d * a * (d * d) * a * d * a := by group
      _ = a * d * (a * a) * d * a := by rw [hd, mul_one]; group
      _ = a * (d * d) * a := by rw [ha, mul_one]; group
      _ = 1 := by rw [hd, mul_one, ha]
  rw [eq_inv_of_mul_eq_one_right hzz, mul_inv_eq_iff_eq_mul] at hz
  exact hz

section Config

variable [Finite G] {M B : Subgroup G}

theorem core31_of_ord (h : R2 M B) {m g' : G}
    (hord : ∀ a ∈ conjSubgroup m (omegaOneSub B), a ≠ 1 → ∀ d ∈ conjSubgroup g' (omegaOneSub B),
      d ≠ 1 → orderOf (a * d) = 4) :
    Core31 (conjSubgroup g' (omegaTwoSub B)) (m * g'⁻¹) := by
  have hΩ : omegaOneSub (conjSubgroup (m * g'⁻¹) (conjSubgroup g' (omegaTwoSub B))) =
      conjSubgroup m (omegaOneSub B) := by
    rw [← conjSubgroup_mul, inv_mul_cancel_right, Pair.omegaOne_conj_U h m]
  exact
    { comm := Pair.comm_conj_U h g'
      two := (Pair.isPGroup_U h).map (MulAut.conj g').toMonoidHom
      ti := isTI_conjSubgroup h.s3hyp.ti g'
      exp := Pair.pow_four_conj h g'
      exp_ne := Pair.exists_sq_ne_conj h g'
      card4 := by rw [Pair.omegaOne_conj_U h g', Pair.card_conj_B0 h g']
      ord := fun α' hα' hα1' β hβ hβ1 => by
        rw [hΩ] at hα'
        rw [Pair.omegaOne_conj_U h g'] at hβ
        exact hord α' hα' hα1' β hβ hβ1 }

omit [Finite G] in
theorem omegaOne_conj_conj (h : R2 M B) (m g' : G) :
    omegaOneSub (conjSubgroup (m * g'⁻¹) (conjSubgroup g' (omegaTwoSub B))) =
      conjSubgroup m (omegaOneSub B) := by
  rw [← conjSubgroup_mul, inv_mul_cancel_right, Pair.omegaOne_conj_U h m]

omit [Finite G] in
theorem omegaTwoSub_ne_bot (h : R2 M B) : omegaTwoSub B ≠ ⊥ := by
  intro hbot
  apply h.omegaOne_ne_bot
  rw [eq_bot_iff]
  have := Pair.B0_le_U h
  rwa [hbot] at this

end Config

section Cert

variable
  [Finite G] {M B : Subgroup G}

theorem commute_comm_lam (h : R2 M B) {A D : Subgroup G} (hA : A ∈ Lam M B) (hD : D ∈ Lam M B)
    {a d : G} (ha : a ∈ A) (hd : d ∈ D) {u : G} (hu : u ∈ omegaTwoSub B) :
    u * (a * d * a⁻¹ * d⁻¹) = (a * d * a⁻¹ * d⁻¹) * u := by
  have haa := Lam.mul_self h hA a ha
  have hdd := Lam.mul_self h hD d hd
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have hdi : d⁻¹ = d := inv_eq_of_mul_eq_one_right hdd
  have h1 := comm_U_mem_B0 h hA ha hu
  have h2 := comm_U_mem_B0 h hD hd hu
  rw [hai] at h1
  rw [hdi] at h2
  rw [hai, hdi]
  exact (commute_of_mul_B₀ (fun p hp q hq => h.H.comm p (omegaOneSub_le B hp) q
    (omegaOneSub_le B hq)) (fun b hb => Pair.sq_B0 h hb) haa hdd
    (fun b hb => R2.comm_B0 h hA a ha b hb) (fun b hb => R2.comm_B0 h hD d hd b hb) h1 h2).symm

theorem eq_U_of_data31 (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    (hW : R2Weak) (h : R2 M B) {m g' α x : G}
    (hA : conjSubgroup m (omegaOneSub B) ∈ Lam M B)
    (hD : conjSubgroup g' (omegaOneSub B) ∈ Lam M B)
    (D31 : Data31 (conjSubgroup g' (omegaTwoSub B)) (m * g'⁻¹) α x) :
    conjSubgroup x (conjSubgroup g' (omegaTwoSub B)) = omegaTwoSub B := by
  set V := conjSubgroup g' (omegaTwoSub B) with hV
  have hΩ := omegaOne_conj_conj h m g'
  have hΩV : omegaOneSub V = conjSubgroup g' (omegaOneSub B) := Pair.omegaOne_conj_U h g'
  obtain ⟨β, hβ, hβ1⟩ := D31.core.exists_ne_one_omega 1
  rw [conjSubgroup_one] at hβ
  have hαA : α ∈ conjSubgroup m (omegaOneSub B) := by rw [← hΩ]; exact D31.mem
  have hβD : β ∈ conjSubgroup g' (omegaOneSub B) := by rw [← hΩV]; exact hβ
  have hzC₀ : α * β * α⁻¹ * β⁻¹ ∈ omegaOneSub (conjSubgroup x V) := D31.comm_α_β hCen hU hβ
  have hz1 : α * β * α⁻¹ * β⁻¹ ≠ 1 := D31.comm_ne_one D31.mem D31.ne_one hβ hβ1
  have hzC : α * β * α⁻¹ * β⁻¹ ∈ conjSubgroup x V := omegaOneSub_le _ hzC₀
  have hUN : omegaTwoSub B ≤ Subgroup.normalizer (conjSubgroup x V : Set G) := fun u hu =>
    CFSG.RankThree.GF2n.Tim77.mem_normalizer_of_commute_of_isTI
      (isTI_conjSubgroup D31.core.ti x) hzC hz1 (commute_comm_lam h hA hD hαA hβD hu)
  have hUC : ∀ u ∈ omegaTwoSub B, ∀ c ∈ conjSubgroup x V, u * c = c * u := by
    by_contra hnc
    have hset : Setup210 (omegaTwoSub B) (conjSubgroup x V) :=
      { comm := Pair.comm_U h
        two := Pair.isPGroup_U h
        exp_ne := Pair.exists_sq_ne h
        ti := h.s3hyp.ti
        conj := ⟨x * g', by rw [hV, conjSubgroup_mul]⟩
        ne_bot := by
          rw [inf_of_le_left hUN]
          exact omegaTwoSub_ne_bot h }
    have P : NCPair (omegaTwoSub B) (conjSubgroup x V) :=
      ⟨hset, fun u hu => pow_four_of_mem_omegaTwoSub h.H.comm hu, hnc⟩
    have hnrm := P.nrm_eq hCen hU
    have hle : omegaTwoSub B ≤ nrm (omegaTwoSub B) (conjSubgroup x V) := le_inf le_rfl hUN
    rw [hnrm, h.omegaOne_omegaTwo] at hle
    exact Pair.B0_ne_U h (le_antisymm (Pair.B0_le_U h) hle)
  have hle2 : conjSubgroup (x * g') (omegaTwoSub B) ≤
      Subgroup.centralizer (omegaTwoSub B : Set G) := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hcC : c ∈ conjSubgroup x V := by rw [hV, ← conjSubgroup_mul]; exact hc
    exact hUC u hu c hcC
  have hfin := hW G M B h (x * g') hle2
  rw [hV, ← conjSubgroup_mul]
  exact hfin

theorem r2FirstCore_of (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    (hW : R2Weak) : R2FirstCore := by
  intro G _ _ M B h S A D hA hD hAS hDS hord
  obtain ⟨m, rfl⟩ := Lam.exists_conj hA
  obtain ⟨g', rfl⟩ := Lam.exists_conj hD
  have K := core31_of_ord h hord
  obtain ⟨α, hα, hα1, hncα, x, hx, hxC⟩ := K.exists_data31 hCen hU
  have D31 : Data31 (conjSubgroup g' (omegaTwoSub B)) (m * g'⁻¹) α x :=
    ⟨K, hα, hα1, hncα, hx, hxC⟩
  have hC := eq_U_of_data31 hCen hU hW h hA hD D31
  have hΩ := omegaOne_conj_conj h m g'
  have hΩV : omegaOneSub (conjSubgroup g' (omegaTwoSub B)) =
      conjSubgroup g' (omegaOneSub B) := Pair.omegaOne_conj_U h g'
  have h1 := FirstHalf.commutator_eq_B0 hCen hU h D31 hC
  have h2 := FirstHalf.sup_eq_sup_U hCen hU hW h D31 hC (by rw [hΩ]; exact hA)
  rw [hΩ, hΩV] at h1 h2
  exact ⟨h1, h2⟩

end Cert

end CFSG.CGT.PushingUpLit.SolKR2
