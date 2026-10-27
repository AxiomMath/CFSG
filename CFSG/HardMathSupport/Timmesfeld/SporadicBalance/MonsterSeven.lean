module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterSevenKit
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterSevenClasses
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1Seven
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7.SevenFacts
public import Certificates.Certificate13638
public import Certificates.Certificate13639

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.Monster.Generated
  CFSG.Monster.Existence CFSG.Monster.B CFSG.Monster.Spin CFSG.YGroups.Y443
  CFSG.YGroups.Y443Native CFSG.AGLEmbedding.Norton.MON5_7 CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.HardMathSupport.Timmesfeld.Coordinator

section Helpers

variable {G : Type*} [Group G]

theorem conj_eq_inv_of_mul_eq_one {r v : G} (hv : v * v = 1) (h : r * v * r * v = 1) :
    v * r * v⁻¹ = r⁻¹ := by
  rw [inv_eq_of_mul_eq_one_right hv]
  apply eq_inv_of_mul_eq_one_right
  rw [← h]
  group

theorem comm_mul_of_conj_eq_inv {f u v : G} (hu : u * f * u⁻¹ = f⁻¹) (hv : v * f * v⁻¹ = f⁻¹) :
    f * (u * v) = (u * v) * f := by
  have h : (u * v) * f * (u * v)⁻¹ = f := by
    calc (u * v) * f * (u * v)⁻¹ = u * (v * f * v⁻¹) * u⁻¹ := by group
      _ = u * f⁻¹ * u⁻¹ := by rw [hv]
      _ = (u * f * u⁻¹)⁻¹ := by group
      _ = f := by rw [hu, inv_inv]
  calc f * (u * v) = ((u * v) * f * (u * v)⁻¹) * (u * v) := by rw [h]
    _ = (u * v) * f := by group

theorem not_mem_zpowers_of_ne_pow {a b : G} {n : ℕ} (hn : a ^ n = 1) (hn0 : 0 < n)
    (h : ∀ k : ℕ, b ≠ a ^ k) : b ∉ Subgroup.zpowers a := by
  intro hb
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
  apply h (Int.toNat (k % n))
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn0.ne'
  rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ hn')]
  conv_lhs => rw [← Int.emod_add_mul_ediv k n]
  rw [zpow_add, zpow_mul, zpow_natCast, hn, one_zpow, mul_one]

theorem gLAPPrimeCoreOf_eq_bot_of_isConj' {p : ℕ} {s₀ s : G} (hs : IsConj s₀ s)
    (h : GLAPPrimeCoreOf p (Subgroup.centralizer ({s₀} : Set G)) = ⊥) :
    GLAPPrimeCoreOf p (Subgroup.centralizer ({s} : Set G)) = ⊥ := by
  obtain ⟨c, hc⟩ := isConj_iff.1 hs
  set ψ := (MulAut.conj c).toMonoidHom with hψ
  have hψi : Function.Injective ψ := (MulAut.conj c).injective
  have hmap := map_glaPPrimeCoreOf_of_injective p ψ hψi (Subgroup.centralizer ({s₀} : Set G))
  have hcen := map_inf_centralizer_of_injective ψ hψi ⊤ s₀
  rw [top_inf_eq, Subgroup.map_top_of_surjective _ (MulAut.conj c).surjective,
    top_inf_eq] at hcen
  have hψs : ψ s₀ = s := by
    rw [hψ, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hc]
  rw [hcen, hψs] at hmap
  rw [← hmap, h, Subgroup.map_bot]

end Helpers

theorem gw_ne_of_sepCheck {w₁ w₂ : List Native.Gen} {v : Native.DVec}
    (h : sepCheck w₁ w₂ v = true) : gw w₁ ≠ gw w₂ := by
  unfold sepCheck at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hv₁, hv₂⟩, hm⟩ := h
  have h₁ : ∀ g ∈ w₁, g.validB = true := fun g hg => List.all_eq_true.1 hv₁ g hg
  have h₂ : ∀ g ∈ w₂, g.validB = true := fun g hg => List.all_eq_true.1 hv₂ g hg
  obtain ⟨k, hk, hne⟩ := EdgeNoncomm.moveCheckAux_spec hm
  intro heq
  have e : wordLin w₁ (interp v) = wordLin w₂ (interp v) := by
    have := congrArg (fun g : Gmat => (g : SpaceB ≃ₗ[ℚ] SpaceB) (interp v)) heq
    simpa using this
  rw [← evalWord_sound w₁ h₁ v, ← evalWord_sound w₂ h₂ v] at e
  have hcf := EdgeNoncomm.cf_eq_of_interp_eq e hk
  apply hne
  unfold cf at hcf
  have h2 : (2 : ℚ) ^ (Native.evalWord w₁ v).e ≠ 0 := pow_ne_zero _ (by norm_num)
  have h3 : (2 : ℚ) ^ (Native.evalWord w₂ v).e ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [div_eq_div_iff h2 h3] at hcf
  exact_mod_cast hcf

theorem tG_eq_xGmat : tG = xGmat := by
  apply Subtype.ext
  show wordLin [Native.Gen.rho (true, 0, 0)] = CFSG.Monster.Generated.xmat
  have h : Rep4371.pauliQ (true, 0, 0) = zQ := by
    unfold Rep4371.pauliQ zQ
    congr 1
    simp [Rep4371.toSC, SpinCoord.z, Rep4371.boolZ, Rep4371.toC_zero, Rep4371.toD_zero]
  rw [wordLin_cons, wordLin_nil, one_mul, Native.Gen.toLin_rho, h]
  rfl

theorem orderOf_tG : orderOf tG = 2 := by
  rw [tG_eq_xGmat]
  exact orderOf_xGmat

theorem isTwoBCentralizer_tG :
    IsTwoBCentralizer tG := by
  rw [tG_eq_xGmat]
  exact isTwoBCentralizer_Gmat xGmat (IsConj.refl _)

theorem conj_tG_facts
    {u h : Gmat}
    (hc : h * u = tG * h) :
    orderOf u = 2 ∧ u * u = 1 ∧ IsTwoBCentralizer u := by
  have e : u = MulAut.conj h⁻¹ tG := by
    rw [MulAut.conj_apply]
    calc u = h⁻¹ * (h * u) := by group
      _ = h⁻¹ * (tG * h) := by rw [hc]
      _ = h⁻¹ * tG * h⁻¹⁻¹ := by group
  have ho : orderOf u = 2 := by rw [e, MulEquiv.orderOf_eq, orderOf_tG]
  refine ⟨ho, ?_, ?_⟩
  · rw [← sq, ← ho]
    exact pow_orderOf_eq_one u
  · apply isTwoBCentralizer_Gmat
    rw [← tG_eq_xGmat]
    refine isConj_iff.2 ⟨h⁻¹, ?_⟩
    rw [e, MulAut.conj_apply]

section Norton


theorem tG_inv_eq : tG⁻¹ = tG := inv_eq_of_mul_eq_one_right tG_sq

theorem dG_tG_comm' : dG * tG = tG * dG := by
  calc dG * tG = (tG * dG * tG) * tG := by rw [tG_dG]
    _ = tG * dG * (tG * tG) := by rw [mul_assoc]
    _ = tG * dG := by rw [tG_sq, mul_one]

theorem orderOf_dG : orderOf dG = 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact orderOf_eq_prime dG_pow dG_ne_one

theorem orderOf_zG : orderOf zG = 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact orderOf_eq_prime zG_pow zG_ne_one

theorem tG_zG_inv : tG * zG * tG⁻¹ = zG⁻¹ := by
  rw [tG_inv_eq]
  exact tG_zG

end Norton

theorem gLAPPrimeCoreOf_dG :
    GLAPPrimeCoreOf 7 (Subgroup.centralizer ({dG} : Set Gmat)) = ⊥ := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨hA, hmb, hmtb⟩ := Certificates.certificate13638
  have hrel := agreeAll_sound hA
  have r1 : dG * gw m7bW = gw m7bW * dG := by
    have := hrel (m7bW ++ dW, dW ++ m7bW) (by simp [m7APairs])
    simpa [gw_append, dG] using this
  have r2 : gw m7hbW * gw m7bW = tG * gw m7hbW := by
    have := hrel (m7bW ++ m7hbW, m7hbW ++ tW) (by simp [m7APairs])
    simpa [gw_append, tG] using this
  have r3 : gw m7htbW * (tG * gw m7bW) = tG * gw m7htbW := by
    have := hrel (m7bW ++ tW ++ m7htbW, m7htbW ++ tW) (by simp [m7APairs])
    simpa [gw_append, tG, mul_assoc] using this
  have r4 : gw m7rbW ^ 7 = 1 := by
    have := hrel (powL 7 m7rbW, []) (by simp [m7APairs])
    simpa [gw_powL_eq, gw_nil] using this
  have r5 : dG * gw m7rbW = gw m7rbW * dG := by
    have := hrel (m7rbW ++ dW, dW ++ m7rbW) (by simp [m7APairs])
    simpa [gw_append, dG] using this
  have r6 : gw m7rbW * gw m7bW * gw m7rbW * gw m7bW = 1 := by
    have := hrel (m7bW ++ m7rbW ++ m7bW ++ m7rbW, []) (by simp [m7APairs])
    simpa [gw_append, gw_nil, mul_assoc] using this
  have r7 : gw m7rtbW ^ 7 = 1 := by
    have := hrel (powL 7 m7rtbW, []) (by simp [m7APairs])
    simpa [gw_powL_eq, gw_nil] using this
  have r8 : dG * gw m7rtbW = gw m7rtbW * dG := by
    have := hrel (m7rtbW ++ dW, dW ++ m7rtbW) (by simp [m7APairs])
    simpa [gw_append, dG] using this
  have r9 : gw m7rtbW * (tG * gw m7bW) * gw m7rtbW * (tG * gw m7bW) = 1 := by
    have := hrel (m7bW ++ tW ++ m7rtbW ++ m7bW ++ tW ++ m7rtbW, []) (by simp [m7APairs])
    simpa [gw_append, gw_nil, tG, mul_assoc] using this
  obtain ⟨hob, hbb, hB⟩ := conj_tG_facts r2
  obtain ⟨hotb, htbtb, hTB⟩ := conj_tG_facts r3
  have hrb : orderOf (gw m7rbW) = 7 := orderOf_eq_prime r4 (gw_ne_one_of_moveCheck hmb)
  have hrtb : orderOf (gw m7rtbW) = 7 := orderOf_eq_prime r7 (gw_ne_one_of_moveCheck hmtb)
  exact gLAPPrimeCoreOf_eq_bot_of_twoB_four (Fact.out) (by norm_num) oPrimeCoreTrivialAt_seven_Co1
    orderOf_dG dG_tG_comm'.symm r1.symm orderOf_tG hob hotb isTwoBCentralizer_tG hB hTB
    dG_zG_comm.symm orderOf_zG tG_zG_inv r5.symm hrb (conj_eq_inv_of_mul_eq_one hbb r6)
    r8.symm hrtb (conj_eq_inv_of_mul_eq_one htbtb r9)

theorem gLAPPrimeCoreOf_zG :
    GLAPPrimeCoreOf 7 (Subgroup.centralizer ({zG} : Set Gmat)) = ⊥ := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨hB, hsep⟩ := Certificates.certificate13639
  have hrel := agreeAll_sound hB
  have r1 : zG * gw m7wW = gw m7wW * zG := by
    have := hrel (m7wW ++ zW, zW ++ m7wW) (by simp [m7BPairs])
    simpa [gw_append, zG] using this
  have r2 : dG * gw m7wW * dG * gw m7wW = 1 := by
    have := hrel (m7wW ++ dW ++ m7wW ++ dW, []) (by simp [m7BPairs])
    simpa [gw_append, gw_nil, dG, mul_assoc] using this
  have r3 : xG * gw m7wW * xG * gw m7wW = 1 := by
    have := hrel (m7wW ++ xW ++ m7wW ++ xW, []) (by simp [m7BPairs])
    simpa [gw_append, gw_nil, xG, mul_assoc] using this
  have r4 : gw m7hwW * gw m7wW = tG * gw m7hwW := by
    have := hrel (m7wW ++ m7hwW, m7hwW ++ tW) (by simp [m7BPairs])
    simpa [gw_append, tG] using this
  have r5 : gw m7hwtW * (gw m7wW * tG) = tG * gw m7hwtW := by
    have := hrel (tW ++ m7wW ++ m7hwtW, m7hwtW ++ tW) (by simp [m7BPairs])
    simpa [gw_append, tG, mul_assoc] using this
  have r6 : (zG * eG) * gw m7wW * (zG * eG) * gw m7wW = 1 := by
    have := hrel (m7wW ++ eW ++ zW ++ m7wW ++ eW ++ zW, []) (by simp [m7BPairs])
    simpa [gw_append, gw_nil, zG, eG, mul_assoc] using this
  have r7 : gw m7e2W ^ 7 = 1 := by
    have := hrel (powL 7 m7e2W, []) (by simp [m7BPairs])
    simpa [gw_powL_eq, gw_nil] using this
  have r8 : zG * gw m7e2W = gw m7e2W * zG := by
    have := hrel (m7e2W ++ zW, zW ++ m7e2W) (by simp [m7BPairs])
    simpa [gw_append, zG] using this
  have r9 : gw m7e2W * gw m7wW * gw m7e2W * gw m7wW = 1 := by
    have := hrel (m7wW ++ m7e2W ++ m7wW ++ m7e2W, []) (by simp [m7BPairs])
    simpa [gw_append, gw_nil, mul_assoc] using this
  have r10 : gw m7e2W * tG * gw m7e2W * tG = 1 := by
    have := hrel (tW ++ m7e2W ++ tW ++ m7e2W, []) (by simp [m7BPairs])
    simpa [gw_append, gw_nil, tG, mul_assoc] using this
  have r11 : gw m7e2W * (zG * eG) = (zG * eG) * gw m7e2W := by
    have := hrel (eW ++ zW ++ m7e2W, m7e2W ++ eW ++ zW) (by simp [m7BPairs])
    simpa [gw_append, zG, eG, mul_assoc] using this
  have rsep : gw m7e2W * dG ≠ dG * gw m7e2W := by
    have := gw_ne_of_sepCheck hsep
    simpa [gw_append, dG] using this
  obtain ⟨how, hww, hW⟩ := conj_tG_facts r4
  obtain ⟨-, -, hWT⟩ := conj_tG_facts r5
  have htt : tG * tG = 1 := tG_sq
  have hwd : gw m7wW * dG * (gw m7wW)⁻¹ = dG⁻¹ := conj_eq_inv_of_mul_eq_one hww r2
  have hwx : gw m7wW * xG * (gw m7wW)⁻¹ = xG⁻¹ := conj_eq_inv_of_mul_eq_one hww r3
  have hwe₁ : gw m7wW * (zG * eG) * (gw m7wW)⁻¹ = (zG * eG)⁻¹ := conj_eq_inv_of_mul_eq_one hww r6
  have hwe₂ : gw m7wW * gw m7e2W * (gw m7wW)⁻¹ = (gw m7e2W)⁻¹ := conj_eq_inv_of_mul_eq_one hww r9
  have hte₂ : tG * gw m7e2W * tG⁻¹ = (gw m7e2W)⁻¹ := conj_eq_inv_of_mul_eq_one htt r10
  have hze : zG * eG = eG * zG := zG_eG_comm
  have hte₁ : tG * (zG * eG) * tG⁻¹ = (zG * eG)⁻¹ := by
    have h1 : tG * (zG * eG) * tG⁻¹ = (tG * zG * tG) * (tG * eG * tG) := by
      rw [tG_inv_eq]
      calc tG * (zG * eG) * tG = tG * zG * (tG * tG) * eG * tG := by rw [htt]; group
        _ = (tG * zG * tG) * (tG * eG * tG) := by group
    rw [h1, tG_zG, tG_eG, ← mul_inv_rev, hze]
  have hox : orderOf xG = 7 := by
    refine orderOf_eq_prime xG_pow ?_
    have := xG_ne_dG_pow 0
    rwa [pow_zero] at this
  have he₁ : (zG * eG) ^ 7 = 1 := by
    rw [(Commute.mul_pow hze 7), zG_pow, eG_pow, one_mul]
  have hoe₁ : orderOf (zG * eG) = 7 := by
    refine orderOf_eq_prime he₁ ?_
    intro h1
    apply eG_ne_zG_pow 6
    have h3 : zG ^ 6 = zG⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact zG_pow)
    rw [h3]
    exact eq_inv_of_mul_eq_one_right h1
  have hne₂ : gw m7e2W ≠ 1 := by
    intro h1
    apply rsep
    rw [h1, one_mul, mul_one]
  have hoe₂ : orderOf (gw m7e2W) = 7 := orderOf_eq_prime r7 hne₂
  have hmem : ∀ f : Gmat, f * zG = zG * f → gw m7wW * f * (gw m7wW)⁻¹ = f⁻¹ → f ^ 7 = 1 →
      f ∈ zConjClosure zG (gw m7wW) := fun f hfz hwf hf7 =>
    mem_zConjClosure_of_inv (k := 3) hww hfz hwf hf7
  have hd₁ : dG * (zG * eG) = (zG * eG) * dG := by
    rw [← mul_assoc, dG_zG_comm, mul_assoc, dG_eG_comm, mul_assoc]
  have hi₃₄ : gw m7e2W ∉ Subgroup.zpowers (zG * eG) := by
    intro hm
    apply rsep
    have hd : dG ∈ Subgroup.centralizer (Subgroup.zpowers (zG * eG) : Set Gmat) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
      exact (Commute.zpow_left (show Commute (zG * eG) dG from hd₁.symm) k).eq
    exact (Subgroup.mem_centralizer_iff.1 hd) _ hm
  have hi₁₂ : xG ∉ Subgroup.zpowers dG :=
    not_mem_zpowers_of_ne_pow dG_pow (by norm_num) xG_ne_dG_pow
  have hCoP : ∀ P : Subgroup CFSG.Blueprint.NativeSporadic.Co1, Nat.card P = 7 ^ 2 →
      IsPGroup 7 ↥(Subgroup.centralizer (P : Set CFSG.Blueprint.NativeSporadic.Co1)) :=
    fun P hP => isPGroup_centralizer_of_card_eq_49_Co1 P (by rw [hP]; norm_num)
  exact gLAPPrimeCoreOf_eq_bot_of_twoB_dihedral (Fact.out) (by norm_num)
    oPrimeCoreTrivialAt_seven_Co1 hCoP orderOf_zG how r1.symm hW dG_zG_comm orderOf_dG hwd
    orderOf_tG tG_zG_inv isTwoBCentralizer_tG hWT
    (hmem dG dG_zG_comm hwd dG_pow) (hmem xG zG_xG_comm.symm hwx xG_pow)
    (hmem _ (by rw [mul_assoc, ← hze]) hwe₁ he₁) (hmem _ r8.symm hwe₂ r7)
    orderOf_dG hox hoe₁ hoe₂ dG_xG_comm r11.symm hi₁₂ hi₃₄ dG_tG_comm' xG_tG_comm
    (comm_mul_of_conj_eq_inv hwe₁ hte₁) (comm_mul_of_conj_eq_inv hwe₂ hte₂)

theorem oPrimeCoreTrivialAt_seven_Gmat_of_classes
    (hcl : MonsterSevenClasses dG zG) :
    OPrimeCoreTrivialAt 7 Gmat := by
  intro s hs
  rcases hcl s hs with h | h
  · exact gLAPPrimeCoreOf_eq_bot_of_isConj' h.symm gLAPPrimeCoreOf_dG
  · exact gLAPPrimeCoreOf_eq_bot_of_isConj' h.symm gLAPPrimeCoreOf_zG

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
