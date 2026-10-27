module

public import CFSG.LargeExtraspecial.AS35QCoFrL
public import CFSG.LargeExtraspecial.AS35TPSym
public import CFSG.Sporadic.Co2Smith.CCensusCheck
public import CFSG.LargeExtraspecial.BridgeSetting
public import CFSG.Sporadic.Co2Smith.GlAssembly

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35QCo

open Module Subgroup CFSG.RankThree.OrthogonalInvolutions CFSG.Sporadic.Co2Smith

variable {G : Type} [Group G] [Finite G] (S : Setting G)

theorem eq_one_of_mem_cg (hS : S.SixHyp) (hsp : S.Asc512SpSix) (hfix : fixL S = ⊥) {c : S.O}
    (hcC : c ∈ centralizer S.DbarAsc) (hc : c ^ 2 = 1 ∨ c ^ 3 = 1) : c = 1 := by
  have := finite_Qt S
  have hq := S.q_nondegenerate
  have hV := finrank_eq_eight S hsp.1
  obtain ⟨x, hxL, hx7, hx1⟩ := exists_seven S hsp
  have hx := seven_hyp S hsp.1 hx7 hx1
  obtain ⟨hF2, -, -⟩ := hx.finrank_fixSpace
  have hcomm : ∀ g ∈ S.LbarAsc, g * c = c * g := fun g hg => commute_of_mem_centralizer S hcC hg
  have hlin : ∀ g ∈ S.LbarAsc, (g : S.Qt ≃ₗ[ZMod 2] S.Qt) * (c : S.Qt ≃ₗ[ZMod 2] S.Qt) =
      (c : S.Qt ≃ₗ[ZMod 2] S.Qt) * g := fun g hg => by
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hcomm g hg]
  have hcx : (c : S.Qt ≃ₗ[ZMod 2] S.Qt) * x = x * c := (hlin x hxL).symm
  have hFinf : fixSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊓ commSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥ :=
    fixSpace_inf_commSpace ⟨3, rfl⟩ hx.pow
  by_contra hc1
  have hC1 : (c : S.Qt ≃ₗ[ZMod 2] S.Qt) ≠ 1 := fun h => hc1 (Subtype.ext h)
  have hcne := commSpace_ne_bot hC1
  have hbot : ∀ U : Submodule (ZMod 2) S.Qt, U ≤ fixL S → finrank (ZMod 2) U = 0 := fun U hU => by
    rw [hfix, le_bot_iff] at hU
    rw [hU, finrank_bot]
  rcases hc with hc2 | hc3
  ·
    have hcc : (c : S.Qt ≃ₗ[ZMod 2] S.Qt) * c = 1 := by
      rw [← Subgroup.coe_mul, ← pow_two, hc2]
      rfl
    have hle := hx.commSpace_le_fixSpace hcx (Or.inl hcc)
    have hle' := Submodule.finrank_mono hle
    rw [hF2] at hle'
    have h2 : finrank (ZMod 2) (commSpace (c : S.Qt ≃ₗ[ZMod 2] S.Qt)) ≠ 2 := by
      intro h
      have heq : commSpace (c : S.Qt ≃ₗ[ZMod 2] S.Qt) = fixSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt) :=
        Submodule.eq_of_le_of_finrank_eq hle (by rw [h, hF2])
      have h1 : fixSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤ commSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
        rw [← heq, commSpace_eq_orthogonal hq hx.isom, ← heq,
          ← fixSpace_eq_orthogonal hq (isom S c)]
        exact commSpace_le_fixSpace hcc
      have h0 : fixSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥ := by
        rw [← hFinf]
        exact le_antisymm (le_inf le_rfl h1) inf_le_left
      rw [h0, finrank_bot] at hF2
      exact absurd hF2 (by norm_num)
    have h1 : finrank (ZMod 2) (commSpace (c : S.Qt ≃ₗ[ZMod 2] S.Qt)) = 1 := by omega
    apply hcne
    apply hbot
    intro u hu g hg
    by_cases hu0 : u = 0
    · rw [hu0, map_zero]
    · refine Frame.eq_of_finrank_eq_one h1 (apply_mem_commSpace (hlin g hg) hu) hu ?_ hu0
      intro h
      exact hu0 ((g : S.Qt ≃ₗ[ZMod 2] S.Qt).injective (h.trans (map_zero _).symm))
  ·
    have hc3' : (c : S.Qt ≃ₗ[ZMod 2] S.Qt) ^ 3 = 1 := by
      rw [← Subgroup.coe_pow, hc3]
      rfl
    have hle := hx.commSpace_le_fixSpace hcx (Or.inr hc3')
    have hle' := Submodule.finrank_mono hle
    rw [hF2] at hle'
    have hev : finrank (ZMod 2) (commSpace (c : S.Qt ≃ₗ[ZMod 2] S.Qt)) % 2 = 0 := by
      have h1 := mod_two_of_pow_three hc3' (W := ⊤) (fun _ _ => Submodule.mem_top)
      rw [top_inf_eq, finrank_top, hV] at h1
      have h2 := finrank_commSpace_add_finrank_fixSpace (c : S.Qt ≃ₗ[ZMod 2] S.Qt)
      rw [hV] at h2
      omega
    have hU2 : finrank (ZMod 2) (commSpace (c : S.Qt ≃ₗ[ZMod 2] S.Qt)) = 2 := by omega
    have hnd : commSpace (c : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊓
        LinearMap.BilinForm.orthogonal S.q.polarBilin (commSpace (c : S.Qt ≃ₗ[ZMod 2] S.Qt)) =
          ⊥ := by
      rw [← fixSpace_eq_orthogonal hq (isom S c), inf_comm]
      exact fixSpace_inf_commSpace ⟨1, rfl⟩ hc3'
    have hD : ∀ a ∈ S.DbarAsc, ∀ u ∈ commSpace (c : S.Qt ≃ₗ[ZMod 2] S.Qt),
        (a : S.Qt ≃ₗ[ZMod 2] S.Qt) u = u := fun a ha u hu =>
      eq_of_isTypeA (isTypeA_of_mem_dbar S hS ha) hU2 hnd
        (fun v hv => apply_mem_commSpace (hlin a (subset_closure ha)) hv) hu
    apply hcne
    exact hbot _ fun u hu g hg => fixed_of_mem_lbar S hD hg u hu

theorem cg_trivial (hS : S.SixHyp) (hst : S.Asc512Standing) (hsp : S.Asc512SpSix)
    (hfix : fixL S = ⊥) {c : S.O} (hc : c ∈ S.Mbar ⊓ centralizer S.DbarAsc) : c = 1 := by
  set Cg : Subgroup S.O := S.Mbar ⊓ centralizer S.DbarAsc with hCg
  have : Finite Cg := inferInstance
  have hF : CFSG.generalizedFitting Cg = ⊥ := by
    rw [eq_bot_iff]
    intro f hf
    rw [mem_bot]
    have hd := orderOf_dvd_natCard (⟨f, hf⟩ : CFSG.generalizedFitting Cg)
    rw [Subgroup.orderOf_mk] at hd
    have hle := (Nat.le_of_dvd Nat.card_pos hd).trans hst.fstar_card
    have hpos := orderOf_pos f
    have hpow := pow_orderOf_eq_one f
    have h123 : orderOf f = 1 ∨ orderOf f = 2 ∨ orderOf f = 3 := by omega
    rcases h123 with h | h | h
    · exact orderOf_eq_one_iff.mp h
    · rw [h] at hpow
      exact Subtype.ext (eq_one_of_mem_cg S hS hsp hfix (mem_inf.mp f.2).2
        (Or.inl (by rw [← Subgroup.coe_pow, hpow]; rfl)))
    · rw [h] at hpow
      exact Subtype.ext (eq_one_of_mem_cg S hS hsp hfix (mem_inf.mp f.2).2
        (Or.inr (by rw [← Subgroup.coe_pow, hpow]; rfl)))
  have hcen := CFSG.centralizer_generalizedFitting_le Cg
  rw [hF] at hcen
  have hmem : (⟨c, hc⟩ : Cg) ∈ centralizer ((⊥ : Subgroup Cg) : Set Cg) :=
    mem_centralizer_iff.mpr fun h hh => by
      rw [SetLike.mem_coe, mem_bot] at hh
      rw [hh, one_mul, mul_one]
  have h1 := hcen hmem
  rw [mem_bot] at h1
  exact congrArg Subtype.val h1

theorem mbar_eq_lbar (hS : S.SixHyp) (hst : S.Asc512Standing) (hsp : S.Asc512SpSix)
    (θ : S.LbarAsc ≃* Sp62) (hfix : fixL S = ⊥) : S.Mbar = S.LbarAsc := by
  refine le_antisymm (fun m hm => ?_) (lbar_le_mbar S)
  obtain ⟨l, hl, hconj⟩ := exists_conj_eq S hst θ hm
  have hc : l⁻¹ * m ∈ S.Mbar ⊓ centralizer S.DbarAsc := by
    refine ⟨S.Mbar.mul_mem (S.Mbar.inv_mem (lbar_le_mbar S hl)) hm,
      mem_centralizer_iff.mpr fun a ha => ?_⟩
    have e := hconj a (subset_closure ha)
    calc a * (l⁻¹ * m) = l⁻¹ * (l * a * l⁻¹) * m := by group
      _ = l⁻¹ * (m * a * m⁻¹) * m := by rw [e]
      _ = l⁻¹ * m * a := by group
  have h1 := cg_trivial S hS hst hsp hfix hc
  rw [inv_mul_eq_one] at h1
  rw [← h1]
  exact hl

theorem exists_noncomm (hsp : S.Asc512SpSix) : ∃ a b : G, a * b ≠ b * a := by
  have := finite_Qt S
  have hV := finrank_eq_eight S hsp.1
  have : Nontrivial S.Qt := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  obtain ⟨v, hv⟩ := exists_ne (0 : S.Qt)
  obtain ⟨w, hw⟩ : ∃ w, QuadraticMap.polar S.q v w ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (S.q_nondegenerate.1 v fun w => by
      rw [QuadraticMap.polarBilin_apply_apply]
      exact h w)
  obtain ⟨a, rfl⟩ := S.exists_toQt v
  obtain ⟨b, rfl⟩ := S.exists_toQt w
  refine ⟨((a : S.M) : G), ((b : S.M) : G), fun h => hw ((S.polar_q_toQt_eq_zero_iff a b).mpr ?_)⟩
  exact Subtype.ext (Subtype.ext h)

theorem fixSpace_sq_le {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {X : V ≃ₗ[ZMod 2] V}
    (hX5 : X ^ 5 = 1) : fixSpace (X ^ 2) ≤ fixSpace X := by
  intro v hv
  rw [mem_fixSpace] at hv ⊢
  have e : X = (X ^ 2) ^ 3 := by rw [← pow_mul, show 2 * 3 = 5 + 1 from rfl, pow_succ, hX5, one_mul]
  rw [e, pow_succ, pow_succ, pow_one, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hv, hv, hv]

theorem timmesfeldCo2Hyp_of (hS : S.SixHyp) (hsp : S.Asc512SpSix) (htop : S.zGen = ⊤)
    (e : S.Mbar ≃* Sp62) {X : S.O} (hXM : X ∈ S.Mbar) (hX5 : X ^ 5 = 1) (hX1 : X ≠ 1)
    (hfix : fixSpace (X : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥) : TimmesfeldCo2Hyp G S.z where
  simple := by
    have h := hS.simple
    rw [htop] at h
    exact (Subgroup.topEquiv (G := G)).symm.isSimpleGroup
  noncomm := exists_noncomm S hsp
  orderOf_eq := S.orderOf_z
  extraspecial := Bridge.timmesfeldIsExtraspecial_fstar S
  card := by rw [Bridge.card_fstar S, hsp.1]
  quotient := by
    obtain ⟨φ, hφs, hφk⟩ := Bridge.quotientIso_Mbar S
    refine ⟨e.toMonoidHom.comp φ, e.surjective.comp hφs, ?_⟩
    rw [← hφk]
    ext m
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
  spin := by
    obtain ⟨m₀, hm₀⟩ := hXM
    have hQ : m₀ ^ 5 ∈ S.Q := S.mem_Q_of_ρ_eq_one (by rw [map_pow, hm₀, hX5])
    have hcardQ : Nat.card S.Q = 512 := by
      rw [S.card_Q_eq, hsp.1]
      norm_num
    have h512 : (m₀ ^ 5) ^ 512 = 1 := by
      have h := pow_card_eq_one' (x := (⟨m₀ ^ 5, hQ⟩ : S.Q))
      rw [hcardQ] at h
      exact congrArg Subtype.val h
    obtain ⟨m, hmdef⟩ : ∃ m : S.M, m = m₀ ^ 512 := ⟨_, rfl⟩
    have hm5 : m ^ 5 = 1 := by rw [hmdef, ← pow_mul, mul_comm, pow_mul, h512]
    have hρm : S.ρ m = X ^ 2 := by
      rw [hmdef, map_pow, hm₀, pow_eq_pow_mod 512 hX5]
    have hX2 : X ^ 2 ≠ 1 := fun h => hX1 (by
      calc X = (X ^ 2) ^ 3 := by
            rw [← pow_mul, show 2 * 3 = 5 + 1 from rfl, pow_succ, hX5, one_mul]
        _ = 1 := by rw [h, one_pow])
    have hm1 : m ≠ 1 := fun h => hX2 (by rw [← hρm, h, map_one])
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    refine ⟨m, orderOf_eq_prime hm5 hm1, fun y hy hyc => ?_⟩
    rw [← Bridge.Q_eq_timmesfeldFStar S] at hy
    have hconj : S.toQt (CFSG.RankThree.Literature.FSmith.conjAut S.normal m ⟨y, hy⟩) =
        S.toQt ⟨y, hy⟩ := by
      rcases hyc with h | h
      · congr 1
        apply Subtype.ext
        rw [CFSG.RankThree.Literature.FSmith.conjAut_apply]
        exact h
      · have e2 : CFSG.RankThree.Literature.FSmith.conjAut S.normal m ⟨y, hy⟩ =
            ⟨y, hy⟩ * S.zQ := by
          apply Subtype.ext
          rw [CFSG.RankThree.Literature.FSmith.conjAut_apply, h]
          rfl
        rw [e2, S.toQt_mul, (S.toQt_eq_zero_iff' S.zQ).mpr (Or.inr rfl), add_zero]
    have hfx : S.toQt ⟨y, hy⟩ ∈ fixSpace ((X : S.Qt ≃ₗ[ZMod 2] S.Qt) ^ 2) := by
      rw [mem_fixSpace, ← Subgroup.coe_pow, ← hρm, S.ρ_toQt]
      exact hconj
    have h0 := fixSpace_sq_le (by rw [← Subgroup.coe_pow, hX5]; rfl) hfx
    rw [hfix, Submodule.mem_bot, S.toQt_eq_zero_iff'] at h0
    rcases h0 with h0 | h0
    · left
      exact congrArg Subtype.val h0
    · right
      exact congrArg Subtype.val h0

theorem zGen_co2_of
    (hSym : S14.Asc512SymStmt) (hP : S14.Asc512PbarStmt)
    (hCo2 : ∀ (X : Type) [Group X] [Finite X] (t : X), TimmesfeldCo2Hyp X t →
      Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.Co2))
    (hS : S.SixHyp) (hst : S.Asc512Standing) (hsp : S.Asc512SpSix) :
    Nonempty (S.zGen ≃* CFSG.Blueprint.NativeSporadic.Co2) := by
  obtain ⟨θ⟩ := exists_lbar_equiv S hS hst hsp
  have hX := fixSpace_frameL_X S hS hst hsp hSym hP θ
  obtain ⟨x, hxL, hxX⟩ := frameL_X_mem S θ
  have hfixx : fixSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥ := by rw [hxX]; exact hX
  have hfixL : fixL S = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [← hfixx]
    exact mem_fixSpace.mpr (hv x hxL)
  have hML := mbar_eq_lbar S hS hst hsp θ hfixL
  have htop : S.zGen = ⊤ := S.zGen_eq_top_of_fixSpace hS fun v hv => by
    have hmem : v ∈ fixSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt) :=
      mem_fixSpace.mpr (hv x (lbar_le_mbar S hxL))
    rw [hfixx] at hmem
    exact (Submodule.mem_bot _).mp hmem
  have hX5 : x ^ 5 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, hxX]
    exact (frameL S θ).x₅)
  have hX1 : x ≠ 1 := fun h => frS_eight_ne_one (kappa_injective S θ (by
    change (frameL S θ).X = kappa S θ 1
    rw [← hxX, h, map_one]
    rfl))
  have hT := timmesfeldCo2Hyp_of S hS hsp htop ((MulEquiv.subgroupCongr hML).trans θ)
    (lbar_le_mbar S hxL) hX5 hX1 hfixx
  obtain ⟨f⟩ := hCo2 G S.z hT
  exact ⟨((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv).trans f⟩

end CFSG.LargeExtraspecial.AS35QCo

namespace CFSG.LargeExtraspecial.S14

open CFSG.Sporadic.Co2Smith


theorem asc512Co2Branch (hSym : Asc512SymStmt) (hP : Asc512PbarStmt) : Asc512Co2Branch :=
  fun hG1 _ _ _ S hS hst hsp => AS35QCo.zGen_co2_of S hSym hP
    (smith_co2_of_residual ccCensus_check (smithGlobalResidual_of_G1 hG1)) hS hst hsp

end CFSG.LargeExtraspecial.S14
