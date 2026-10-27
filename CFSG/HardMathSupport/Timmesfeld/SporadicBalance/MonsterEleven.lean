module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterElevenLocal
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ElevenSteps
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ElevenFusion
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureSporMEleven
public import Certificates.Certificate16955
public import Certificates.Certificate41508
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Reduction

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterEleven

open CFSG.Monster CFSG.Monster.B CFSG.Monster.AxisCount CFSG.AGLEmbedding.Norton.MON5_7
  CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.Visible CFSG.Monster.Generated
  CFSG.Monster.B.Rep4371 CFSG.Monster.Existence CFSG.Monster.Griess
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterEbar
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterElevenLocal
  CFSG.AGLEmbedding.Norton.Gen11 CFSG.AGLEmbedding.Norton.MON11_13 CFSG.YGroups.Y443
  CFSG.YGroups.Y443Native

theorem gw_powL' (k : ℕ) (w : List Native.Gen) : gw (powL k w) = gw w ^ k :=
  Subtype.ext (by simpa using wordLin_powL k w)


theorem movesSome_ne_one {w : List Native.Gen} (h : movesSome w = true) : gw w ≠ 1 := by
  unfold movesSome at h
  simp only [Bool.or_eq_true] at h
  rcases h with (h | h) | h <;> exact gw_ne_one_of_moveCheck h

theorem eleven_data_facts :
    gw gen11W2 * gw gen11W1 = gw gen11W0 ^ 4 * gw gen11W1 ^ 4 * gw gen11W2 ∧
      gw gen11W0 * gw wW = gw wW * gw gen11W0 ∧
      gw hwW * gw wW = gw tW * gw hwW ∧
      gw htwW * gw twW = gw tW * gw htwW ∧
      gw w0W ^ 3 = 1 ∧
      gw gen11W0 * gw w0W = gw w0W * gw gen11W0 ∧
      gw tW * gw w0W = gw w0W * gw tW ∧
      gw gen11W0 * gw e0W = gw e0W * gw gen11W0 ∧
      gw w0W ≠ 1 ∧ gw commW ≠ 1 := by
  have h := Certificates.certificate16955
  unfold elevenDataCheck at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hagree, hm0⟩, hm1⟩ := h
  have hp := agreeAll_sound hagree
  have p : ∀ i, (hi : i < elevenPairs.length) → gw (elevenPairs[i]).1 = gw (elevenPairs[i]).2 :=
    fun i hi => hp _ (List.getElem_mem hi)
  have p0 := p 0 (by decide)
  have p1 := p 1 (by decide)
  have p2 := p 2 (by decide)
  have p3 := p 3 (by decide)
  have p4 := p 4 (by decide)
  have p5 := p 5 (by decide)
  have p6 := p 6 (by decide)
  have p7 := p 7 (by decide)
  simp only [elevenPairs, List.getElem_cons_zero, List.getElem_cons_succ, gw_append, gw_powL',
    gw_nil] at p0 p1 p2 p3 p4 p5 p6 p7
  refine ⟨?_, p1, p2, p3, p4, p5, p6, p7, movesSome_ne_one hm0, movesSome_ne_one hm1⟩
  rw [p0, mul_assoc]

theorem gw_two_rho (P Q : Model.Pauli) :
    gw [Native.Gen.rho P, Native.Gen.rho Q] = rhoG (Model.Pauli.mul P Q) := by
  rw [show [Native.Gen.rho P, Native.Gen.rho Q] = [Native.Gen.rho P] ++ [Native.Gen.rho Q] from rfl,
    gw_append, rhoG_mul]
  rfl

@[expose] def pW : Model.Pauli := Model.Pauli.mul (false, 1374, 2577) (false, 0, 1599)

@[expose] def pE : Model.Pauli := Model.Pauli.mul (false, 1036, 655) (false, 0, 3364)

theorem gw_wW : gw wW = rhoG pW := gw_two_rho _ _

theorem gw_e0W : gw e0W = rhoG pE := gw_two_rho _ _

theorem gw_tW : gw tW = xGmat := rhoG_z_eq_xGmat

theorem w_facts : gw wW * gw wW = 1 ∧ gw wW ≠ 1 ∧ gw wW ≠ xGmat ∧ xGmat * gw wW = gw wW * xGmat ∧
    gw twW = xGmat * gw wW := by
  rw [gw_wW, ← rhoG_z_eq_xGmat]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← rhoG_mul, show Model.Pauli.mul pW pW = (false, 0, 0) by decide, rhoG_one]
  · intro h
    rw [← rhoG_one] at h
    exact absurd (eq_of_rhoG_eq (by decide) (by decide) h) (by decide)
  · intro h
    exact absurd (eq_of_rhoG_eq (by decide) (by decide) h) (by decide)
  · rw [← rhoG_mul, ← rhoG_mul, show Model.Pauli.mul pW (true, 0, 0) = Model.Pauli.mul (true, 0, 0) pW
      by decide]
  · rw [show twW = [Native.Gen.rho (true, 1374, 2577), Native.Gen.rho (false, 0, 1599)] from rfl,
      gw_two_rho, ← rhoG_mul]
    congr 1

theorem e0_facts : gw e0W * gw e0W = 1 ∧ ((gw e0W : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) ∈ rhoQ ∧
    gw e0W * xGmat = xGmat * gw e0W := by
  rw [gw_e0W, ← rhoG_z_eq_xGmat]
  refine ⟨?_, ?_, ?_⟩
  · rw [← rhoG_mul, show Model.Pauli.mul pE pE = (false, 0, 0) by decide, rhoG_one]
  · rw [coe_rhoG]
    exact mem_rhoQ.2 ⟨_, rfl⟩
  · rw [← rhoG_mul, ← rhoG_mul, show Model.Pauli.mul (true, 0, 0) pE = Model.Pauli.mul pE (true, 0, 0)
      by decide]

theorem comm_aux {G : Type*} [Group G] {e w : G} (he : e * e = 1) (hw : w ^ 3 = 1)
    (h : w * e = e * w) : e * w * e * w ^ 2 = 1 := by
  calc e * w * e * w ^ 2 = e * (w * e) * w ^ 2 := by group
    _ = e * (e * w) * w ^ 2 := by rw [h]
    _ = (e * e) * w ^ 3 := by group
    _ = 1 := by rw [he, hw, one_mul]

theorem gw_commW : gw commW = gw e0W * gw w0W * gw e0W * gw w0W ^ 2 := by
  unfold commW
  rw [gw_append, gw_append, gw_append, gw_powL']
  simp only [mul_assoc]

theorem w0_e0_ne : gw w0W * gw e0W ≠ gw e0W * gw w0W := fun h =>
  eleven_data_facts.2.2.2.2.2.2.2.2.2 (gw_commW.trans
    (comm_aux e0_facts.1 eleven_data_facts.2.2.2.2.1 h))

theorem xGmat_mul_self : xGmat * xGmat = 1 := by
  rw [← pow_two, ← orderOf_xGmat, pow_orderOf_eq_one]

theorem xGmat_ne_one : xGmat ≠ 1 := fun h => by
  have := orderOf_xGmat
  rw [h, orderOf_one] at this
  norm_num at this

theorem exists_transporter {v c : Gmat} (hc : c * v = xGmat * c)
    (hvx : v * gw gen11W0 = gw gen11W0 * v) :
    ∃ m : Gmat, m * v * m⁻¹ = xGmat ∧ ∃ k : ℕ, m * gw gen11W0 * m⁻¹ = gw gen11W0 ^ k := by
  have hcv : c * v * c⁻¹ = xGmat := by rw [hc, mul_inv_cancel_right]
  set x' := c * gw gen11W0 * c⁻¹ with hx'
  have hx'C : x' ∈ cent xGmat := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← hcv]
    calc x' * (c * v * c⁻¹) = c * (gw gen11W0 * v) * c⁻¹ := by rw [hx']; group
      _ = c * (v * gw gen11W0) * c⁻¹ := by rw [hvx]
      _ = c * v * c⁻¹ * x' := by rw [hx']; group
  have hox' : orderOf x' = 11 := by
    rw [hx', show c * gw gen11W0 * c⁻¹ = (MulAut.conj c) (gw gen11W0) by simp [MulAut.conj_apply],
      MulEquiv.orderOf_eq, orderOf_x11]
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨g, k, hg⟩ := exists_conj_pow_of_factorization_eq_one factorization_cent_xGmat_eleven
    orderOf_x11H (y := ⟨x', hx'C⟩) (by rw [← Subgroup.orderOf_coe]; exact hox')
  have hg' : x' = (g : Gmat) * gw gen11W0 ^ k * (g : Gmat)⁻¹ := congrArg Subtype.val hg
  have hgt : (g : Gmat) * xGmat = xGmat * (g : Gmat) :=
    (Subgroup.mem_centralizer_singleton_iff.1 g.2)
  refine ⟨(g : Gmat)⁻¹ * c, ?_, k, ?_⟩
  · calc (g : Gmat)⁻¹ * c * v * ((g : Gmat)⁻¹ * c)⁻¹ = (g : Gmat)⁻¹ * (c * v * c⁻¹) * (g : Gmat) := by
          group
      _ = xGmat := by
          rw [hcv]
          calc (g : Gmat)⁻¹ * xGmat * (g : Gmat) = (g : Gmat)⁻¹ * ((g : Gmat) * xGmat) := by
                rw [hgt, mul_assoc]
            _ = xGmat := by group
  · calc (g : Gmat)⁻¹ * c * gw gen11W0 * ((g : Gmat)⁻¹ * c)⁻¹ = (g : Gmat)⁻¹ * x' * (g : Gmat) := by
          rw [hx']; group
      _ = gw gen11W0 ^ k := by rw [hg']; group

theorem gLAPPrimeCoreOf_x11_eq_bot
    (hodd : Odd (Nat.card (CFSG.Open.GLAPPrimeCoreOf 11 (Subgroup.centralizer ({gw gen11W0} : Set Gmat))))) :
    CFSG.Open.GLAPPrimeCoreOf 11 (Subgroup.centralizer ({gw gen11W0} : Set Gmat)) = ⊥ := by
  obtain ⟨hy3, hxw, hcw, hctw, h3, hw0x, hw0t, he0x, hw01, -⟩ := eleven_data_facts
  obtain ⟨hww, hw1, hwt, htw, htw'⟩ := w_facts
  obtain ⟨-, he0E, he0t⟩ := e0_facts
  rw [gw_tW] at hcw hctw hw0t
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hcore := gLAPPrimeCoreOf_x11_inf_xGmat_eq_bot hodd (w₀ := gw w0W) (e₀ := gw e0W)
    (Subgroup.mem_centralizer_singleton_iff.2 hw0t.symm) hw0x.symm (orderOf_eq_prime h3 hw01)
    (Subgroup.mem_centralizer_singleton_iff.2 he0t) he0E he0x.symm w0_e0_ne
  refine gLAPPrimeCoreOf_eq_bot_of_four orderOf_x11 hodd xGmat_mul_self hww htw xGmat_ne_one hw1 hwt
    (Subgroup.mem_centralizer_singleton_iff.1 x11_mem_cent).symm hxw.symm hcore ?_
  rintro v (rfl | rfl)
  · exact exists_transporter hcw hxw.symm
  · refine exists_transporter (c := gw htwW) (by rw [← htw']; exact hctw) ?_
    calc xGmat * gw wW * gw gen11W0 = xGmat * (gw wW * gw gen11W0) := by rw [mul_assoc]
      _ = xGmat * (gw gen11W0 * gw wW) := by rw [hxw]
      _ = gw gen11W0 * (xGmat * gw wW) := by
          rw [← mul_assoc, ← mul_assoc, (Subgroup.mem_centralizer_singleton_iff.1 x11_mem_cent).symm]

theorem oPrimeCoreTrivialAt_eleven_Gmat_of
    (hG : (Nat.card Gmat).factorization 11 = 2)
    (hinv : ∀ u : Gmat, orderOf u = 2 →
      (Nat.card (Subgroup.centralizer ({u} : Set Gmat))).factorization 11 ≤ 1)
    (hpure : ∀ A : Subgroup Gmat, (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → (∀ a ∈ A, a ^ 2 = 1) →
      8 ≤ Nat.card A → ∃ u ∈ A, IsConj xGmat u) :
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.OPrimeCoreTrivialAt 11 Gmat := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have : Finite Gmat := Nat.finite_of_card_ne_zero (by
    intro h; rw [h] at hG; simp at hG)
  have hodd : ∀ s : Gmat, orderOf s = 11 →
      Odd (Nat.card (CFSG.Open.GLAPPrimeCoreOf 11 (Subgroup.centralizer ({s} : Set Gmat)))) :=
    fun s hs => odd_card_gLAPPrimeCoreOf_eleven hs (exists_eleven_subgroup_of_factorization hG hinv hs)
      hpure (fun x hx hxt => card_centralizer_xGmat_inf_lt hx hxt)
  have hx11 := gLAPPrimeCoreOf_x11_eq_bot (hodd _ orderOf_x11)
  obtain ⟨hx, hy, hxy, hx1, h3, h4, -, -⟩ := eleven_gw_facts
  have hy3 := eleven_data_facts.1
  have hrot := CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.eleven_rot_fact
    Certificates.certificate41508
  have hc : Commute (gw gen11W0) (gw gen11W1) := hxy
  intro s hs
  obtain ⟨g, k, hgk⟩ := exists_conj_pow_of_eleven_lines (x₃ := gw gen11W2) (x₄ := gw gen11W3) hx hy
    hxy (by rw [h3, mul_inv_cancel_right, ((hc.pow_pow 6 3).symm).eq])
    (by rw [hy3, mul_inv_cancel_right]) (by rw [h4, mul_inv_cancel_right])
    (by rw [hrot, mul_inv_cancel_right]) hx1 hG hs
  have hk1 : gw gen11W0 ^ k ≠ 1 := by
    intro h1
    rw [h1, mul_one, mul_inv_cancel] at hgk
    rw [hgk, orderOf_one] at hs
    norm_num at hs
  rw [eq_bot_iff]
  intro n hn
  have h1 := conj_mem_gLAPPrimeCoreOf_conj (m := g⁻¹) (by norm_num : Nat.Prime 11) hn
  have hs' : g⁻¹ * s * g⁻¹⁻¹ = gw gen11W0 ^ k := by rw [hgk]; group
  rw [hs', centralizer_pow_eq_of_prime orderOf_x11 hk1, hx11, Subgroup.mem_bot] at h1
  rw [Subgroup.mem_bot]
  have := congrArg (fun a => g * a * g⁻¹) h1
  simpa [mul_assoc] using this

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterEleven
