module

public import CFSG.LargeExtraspecial.S12Eight
public import CFSG.LargeExtraspecial.S12EightB
public import CFSG.LargeExtraspecial.S12EightC
public import CFSG.LargeExtraspecial.S12Gen

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

universe u

namespace Setting

variable {G : Type u} [Group G] [Finite G] (S : Setting G)

theorem s12_finrank_fix_le_two {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) {L₀ : Subgroup S.O} {x : S.O} (hx : x ∈ S.Lbar g)
    (hxx : x * x = 1) (hsplit : ∀ ℓ ∈ S.Lbar g, ℓ ∈ L₀ ∨ x * ℓ ∈ L₀) :
    finrank (ZMod 2) (S.clSub (S.QG ⊓ S.Qa g) ⊓
      ⨅ ℓ : L₀, fixSpace ((ℓ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) : Submodule (ZMod 2) S.Qt) ≤ 2 := by
  set U := S.clSub (S.QG ⊓ S.Qa g) ⊓ ⨅ ℓ : L₀, fixSpace ((ℓ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
  set ã := S.cl (g * S.z * g⁻¹)
  have hmemU : ∀ {v}, v ∈ U ↔ v ∈ S.clSub (S.QG ⊓ S.Qa g) ∧
      ∀ ℓ ∈ L₀, ((ℓ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
    intro v
    simp only [U, Submodule.mem_inf, Submodule.mem_iInf, mem_fixSpace, Subtype.forall]
  have hxW : ∀ v ∈ S.clSub (S.QG ⊓ S.Qa g), (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ (ZMod 2) ∙ ã := by
    intro v hv
    obtain ⟨w, hwX, hwQ, rfl⟩ := S.mem_clSub_iff.mp hv
    obtain ⟨y, hy, rfl⟩ := S.s12_mem_Lbar.mp hx
    rw [S.ρ_cl _ hwQ]
    change S.cl (y * w * y⁻¹) - S.cl w ∈ _
    rcases S.s12_conj_L0_eq_or hy hwX.2 with h | h
    · rw [h, sub_self]
      exact Submodule.zero_mem _
    · rw [h, S.cl_mul haQ hwQ, add_sub_cancel_right]
      exact Submodule.mem_span_singleton_self _
  set φ := ((x : S.Qt →ₗ[ZMod 2] S.Qt) - 1).domRestrict U
  have hrange : LinearMap.range φ ≤ (ZMod 2) ∙ ã := by
    rintro _ ⟨u, rfl⟩
    exact hxW u (hmemU.mp u.2).1
  have hker : (LinearMap.ker φ).map U.subtype ≤ (ZMod 2) ∙ ã := by
    rintro _ ⟨u, hu, rfl⟩
    have hxu : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) u = u := by
      have := LinearMap.mem_ker.mp hu
      simp only [φ, LinearMap.domRestrict_apply, LinearMap.sub_apply] at this
      exact sub_eq_zero.mp this
    obtain ⟨hu1, hu2⟩ := hmemU.mp u.2
    obtain ⟨w, hwX, hwQ, hwe⟩ := S.mem_clSub_iff.mp hu1
    have hfix : ∀ y ∈ S.L0 g, S.cl (y * w * y⁻¹) = S.cl w := by
      intro y hy
      have hρ : S.ρ ⟨y, S.L0_le_M g hy⟩ ∈ S.Lbar g := S.s12_mem_Lbar.mpr ⟨y, hy, rfl⟩
      have hc := S.ρ_cl ⟨y, S.L0_le_M g hy⟩ hwQ
      refine hc.symm.trans ?_
      rw [hwe]
      rcases hsplit _ hρ with h | h
      · exact hu2 _ h
      · have e1 := hu2 _ h
        rw [Subgroup.coe_mul, LinearEquiv.mul_apply] at e1
        have hx' : ∀ v, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = v := by
          intro v
          rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, hxx]
          rfl
        have := congrArg (x : S.Qt ≃ₗ[ZMod 2] S.Qt) e1
        rw [hx', hxu] at this
        exact this
    show (u : S.Qt) ∈ _
    rcases S.mem_of_cl_fixed_by_L0 haQ hne hwX hfix with h | h | h | h
    · rw [← hwe, h, S.cl_one]
      exact Submodule.zero_mem _
    · rw [← hwe, h]
      exact Submodule.mem_span_singleton_self _
    · rw [← hwe, h, S.cl_z]
      exact Submodule.zero_mem _
    · rw [← hwe, h, S.cl_mul S.z_mem_QG haQ, S.cl_z, zero_add]
      exact Submodule.mem_span_singleton_self _
  have h1 := LinearMap.finrank_range_add_finrank_ker φ
  have h2 : finrank (ZMod 2) (LinearMap.range φ) ≤ 1 :=
    (Submodule.finrank_mono hrange).trans (S.s12_finrank_span_singleton_le ã)
  have h3 : finrank (ZMod 2) (LinearMap.ker φ) ≤ 1 := by
    have e := Submodule.finrank_map_subtype_eq U (LinearMap.ker φ)
    have := (Submodule.finrank_mono hker).trans (S.s12_finrank_span_singleton_le ã)
    omega
  omega

theorem s12_card_le_two_mul {L L₀ : Subgroup S.O} {x : S.O}
    (hsplit : ∀ ℓ ∈ L, ℓ ∈ L₀ ∨ x * ℓ ∈ L₀) : Nat.card L ≤ 2 * Nat.card L₀ := by
  have hsub : (L : Set S.O) ⊆ (L₀ : Set S.O) ∪ (fun y => x⁻¹ * y) '' (L₀ : Set S.O) := by
    intro ℓ hℓ
    rcases hsplit ℓ hℓ with h | h
    · exact Or.inl h
    · exact Or.inr ⟨x * ℓ, h, by group⟩
  calc Nat.card L = (L : Set S.O).ncard := (Nat.card_coe_set_eq _)
    _ ≤ ((L₀ : Set S.O) ∪ (fun y => x⁻¹ * y) '' (L₀ : Set S.O)).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ (L₀ : Set S.O).ncard + ((fun y => x⁻¹ * y) '' (L₀ : Set S.O)).ncard :=
        Set.ncard_union_le _ _
    _ = (L₀ : Set S.O).ncard + (L₀ : Set S.O).ncard := by
        rw [Set.ncard_image_of_injective _ (mul_right_injective x⁻¹)]
    _ = 2 * Nat.card L₀ := by
        have e : (L₀ : Set S.O).ncard = Nat.card L₀ := (Nat.card_coe_set_eq _).symm
        rw [e, two_mul]

theorem s12_eight_caseB {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (hn : 4 ≤ S.width) {t : S.O} (ht : t ∈ S.Lbar g)
    (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) {z : S.O} (hz : z ∈ S.CXbar12 g)
    (hz1 : z ≠ 1) (hz0 : fixSpace (z : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥) (hz3 : z ^ 3 = 1)
    (hzρ : S.M) (hzρe : S.ρ hzρ = z) {x : S.O} (hx : x ∈ S.Lbar g)
    (hxz : x * z * x⁻¹ = z ^ 2)
    (hbQa : ((hzρ : G) * g) * S.z * ((hzρ : G) * g)⁻¹ ∉ S.Qa g) : False := by
  have hn3 : 3 ≤ S.width := by omega
  set g' := (hzρ : G) * g with hg'
  set a := g * S.z * g⁻¹ with ha
  set b := g' * S.z * g'⁻¹ with hb
  obtain ⟨hbQ, hbne⟩ := S.s12_conj_mem haQ hne hzρ
  set ã := S.cl a
  set tb := S.cl b
  have hbcl : tb = (z : S.Qt ≃ₗ[ZMod 2] S.Qt) ã := by
    rw [← hzρe, S.ρ_cl hzρ haQ]
    show S.cl b = _
    rw [hb, hg', S.s12_mul_conj_z]
  have ha0 := S.s12_cl_ne_zero_of_conj haQ hne
  have hb0 := S.s12_cl_ne_zero_of_conj hbQ hbne
  have hab : tb ≠ ã := by
    rw [hbcl]
    intro e
    have : ã ∈ fixSpace (z : S.Qt ≃ₗ[ZMod 2] S.Qt) := mem_fixSpace.mpr e
    rw [hz0] at this
    exact ha0 ((Submodule.mem_bot _).mp this)
  have haQb : a ∉ S.Qa g' := by
    intro h
    apply hbQa
    have e1 : ((hzρ : G)⁻¹ * g') * S.z * ((hzρ : G)⁻¹ * g')⁻¹ = a := by rw [hg', ha]; group
    have e2 : (hzρ : G)⁻¹ * g' = g := by rw [hg']; group
    have h' : ((hzρ : G)⁻¹ * g') * S.z * ((hzρ : G)⁻¹ * g')⁻¹ ∈ S.Qa g' := by rw [e1]; exact h
    have hne' : ((hzρ : G)⁻¹ * g') * S.z * ((hzρ : G)⁻¹ * g')⁻¹ ≠ g' * S.z * g'⁻¹ := by
      rw [e1]
      intro e
      exact hab (by show S.cl b = S.cl a; rw [show b = a from e.symm])
    have := S.s12_mem_Qa_symm (g := g') (hzρ : G)⁻¹ h' hne'
    rwa [e2] at this
  have hxx : x * x = 1 := by
    have : IsElementaryAbelian 2 (S.Lbar g) := S.isElementaryAbelian_Lbar haQ
    have := elemPow_eq_one_of_isElementaryAbelian (p := 2) _ hx
    rwa [pow_two] at this
  set L₀ := S.Lbar g ⊓ centralizer ({z} : Set S.O) with hL₀
  have hL₀b : ∀ ℓ ∈ L₀, ℓ ∈ S.Lbar g' := by
    intro ℓ hℓ
    rw [hg', S.s12_Lbar_mul, hzρe]
    refine ⟨ℓ, hℓ.1, ?_⟩
    have hc : ℓ * z = z * ℓ := mem_centralizer_singleton_iff.mp hℓ.2
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← hc]
    group
  have hsplit : ∀ ℓ ∈ S.Lbar g, ℓ ∈ L₀ ∨ x * ℓ ∈ L₀ := by
    intro ℓ hℓ
    rcases conj_eq_or_CXbar12 haQ hne hn3 ht htA hz hz1 hz3 (S.Lbar_le_Mbar g hℓ) with h | h
    · left
      refine ⟨hℓ, mem_centralizer_singleton_iff.mpr ?_⟩
      calc ℓ * z = ℓ * z * ℓ⁻¹ * ℓ := by group
        _ = z * ℓ := by rw [h]
    · right
      refine ⟨(S.Lbar g).mul_mem hx hℓ, mem_centralizer_singleton_iff.mpr ?_⟩
      have e : (x * ℓ) * z * (x * ℓ)⁻¹ = z := by
        calc (x * ℓ) * z * (x * ℓ)⁻¹ = x * (ℓ * z * ℓ⁻¹) * x⁻¹ := by group
          _ = (x * z * x⁻¹) ^ 2 := by rw [h, conj_pow]
          _ = z := by rw [hxz, ← pow_mul, show 2 * 2 = 3 + 1 by rfl, pow_succ, hz3, one_mul]
      calc x * ℓ * z = (x * ℓ) * z * (x * ℓ)⁻¹ * (x * ℓ) := by group
        _ = z * (x * ℓ) := by rw [e]
  set Wa := S.clSub (S.QG ⊓ S.Qa g) with hWa
  set U₀ := S.clSub (S.QG ⊓ S.Qa g ⊓ S.Qa g') with hU₀
  have hU₀Wa : U₀ ≤ Wa := S.clSub_mono fun w hw => hw.1
  have hU₀fix : ∀ ℓ ∈ L₀, ∀ v ∈ U₀, (ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
    intro ℓ hℓ v hv
    obtain ⟨w, hw, -, rfl⟩ := S.mem_clSub_iff.mp hv
    exact S.s12_Lbar_fix_inf haQ hne hbQ (Ne.symm hab) hℓ.1 (hL₀b ℓ hℓ) hw
  have hzb : S.z ∈ S.Qa g' := S.z_mem_Qa_of_mem_QG rfl hbQ hbne
  have hza : S.z ∈ S.Qa g := S.z_mem_Qa_of_mem_QG rfl haQ hne
  have haU₀ : ã ∉ U₀ := by
    intro h
    obtain ⟨w, hw, hwQ, hwe⟩ := S.mem_clSub_iff.mp h
    rcases (S.cl_eq_cl_iff hwQ haQ).mp hwe with h1 | h1
    · exact haQb (h1 ▸ hw.2)
    · exact haQb (by rw [h1]; exact (S.Qa g').mul_mem hw.2 hzb)
  have htbU₀ : tb ∉ U₀ := by
    intro h
    obtain ⟨w, hw, hwQ, hwe⟩ := S.mem_clSub_iff.mp h
    have h1' : b = w ∨ b = w * S.z := (S.cl_eq_cl_iff hwQ hbQ).mp hwe
    rcases h1' with h1 | h1
    · exact hbQa (h1 ▸ hw.1.2)
    · exact hbQa (by rw [h1]; exact (S.Qa g).mul_mem hw.1.2 hza)
  have habU₀ : ã + tb ∉ U₀ := by
    intro h
    obtain ⟨w, hw, hwQ, hwe⟩ := S.mem_clSub_iff.mp h
    rw [show ã + tb = S.cl (a * b) from (S.cl_mul haQ hbQ).symm] at hwe
    have habQ : a * b ∈ S.QG := S.QG.mul_mem haQ hbQ
    have habQa : a * b ∈ S.Qa g := by
      rcases (S.cl_eq_cl_iff hwQ habQ).mp hwe with h1 | h1
      · exact h1 ▸ hw.1.2
      · rw [h1]; exact (S.Qa g).mul_mem hw.1.2 hza
    apply hbQa
    have : b = a⁻¹ * (a * b) := by group
    rw [this]
    exact (S.Qa g).mul_mem ((S.Qa g).inv_mem (S.conjBy g).z_mem_QG) habQa
  have hdimU₀ : finrank (ZMod 2) U₀ ≤ 1 := by
    have hle := S.s12_finrank_fix_le_two haQ hne (L₀ := L₀) hx hxx hsplit
    set U := Wa ⊓ ⨅ ℓ : L₀, fixSpace ((ℓ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) with hU
    have hmemU : ∀ {v}, v ∈ Wa → (∀ ℓ ∈ L₀, ((ℓ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) → v ∈ U := by
      intro v hv hfix
      refine Submodule.mem_inf.mpr ⟨hv, Submodule.mem_iInf _ |>.mpr fun ℓ => ?_⟩
      exact mem_fixSpace.mpr (hfix ℓ ℓ.2)
    have hsub : U₀ ⊔ (ZMod 2) ∙ ã ≤ U := by
      refine sup_le (fun v hv => hmemU (hU₀Wa hv) fun ℓ hℓ => hU₀fix ℓ hℓ v hv) ?_
      rw [Submodule.span_singleton_le_iff_mem]
      exact hmemU (S.s12_cl_a_mem_clSub haQ) fun ℓ hℓ => S.s12_Lbar_apply_cl_a haQ hℓ.1
    have hinf : U₀ ⊓ (ZMod 2) ∙ ã = ⊥ := by
      rw [eq_bot_iff]
      rintro v ⟨hv1, hv2⟩
      rcases OrthoF2.mem_span_singleton_iff.mp hv2 with h | h
      · rw [h]; exact Submodule.zero_mem _
      · exact absurd (h ▸ hv1) haU₀
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq U₀ ((ZMod 2) ∙ ã)
    rw [hinf, finrank_bot, add_zero, finrank_span_singleton ha0] at h1
    have h2 := Submodule.finrank_mono hsub
    omega
  have haW : ã ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) := (S.timmesfeld_12_6 haQ hne ht htA).1
  have htX : t ∈ S.Xbar12 g := subset_Xbar12 (mem_Ebar12_of_mem_Lbar ht htA)
  have hbW : tb ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    rw [hbcl]
    exact CXbar12_apply_mem htX hz haW
  have hWspan : Submodule.span (ZMod 2) {ã, tb} = commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) :=
    s12_span_pair_eq htA.2.2.2.1 haW hbW ha0 hb0 hab.symm
  set Y := LinearMap.BilinForm.orthogonal S.q.polarBilin (Submodule.span (ZMod 2) {ã, tb})
    with hY
  have hYmem : ∀ v, v ∈ Y ↔ polar S.q ã v = 0 ∧ polar S.q tb v = 0 := fun v =>
    OrthoF2.mem_orthogonal_span_pair_iff
  have hsubU₀ : ∀ ℓ ∈ L₀, ∀ v ∈ Y, (ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ U₀ := by
    intro ℓ hℓ v hv
    obtain ⟨x', hx'Q, rfl⟩ := S.exists_cl v
    obtain ⟨h1, h2⟩ := (hYmem _).mp hv
    have hx'a := (S.polar_cl_eq_zero_iff haQ hx'Q).mp h1
    have hx'b := (S.polar_cl_eq_zero_iff hbQ hx'Q).mp h2
    exact S.s12_Lbar_apply_sub_mem_inf haQ hne hℓ.1 (hL₀b ℓ hℓ) hx'Q hx'a.symm hx'b.symm
  have hfixY : ∀ ℓ ∈ L₀, ∀ v ∈ Y, (ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
    intro ℓ hℓ
    by_cases hb0' : U₀ = ⊥
    · intro v hv
      have := hsubU₀ ℓ hℓ v hv
      rw [hb0'] at this
      exact sub_eq_zero.mp ((Submodule.mem_bot _).mp this)
    · obtain ⟨w, hwU, hw0⟩ := (Submodule.ne_bot_iff _).mp hb0'
      have hspan : U₀ = (ZMod 2) ∙ w := by
        symm
        refine Submodule.eq_of_le_of_finrank_eq
          ((Submodule.span_singleton_le_iff_mem _ _).mpr hwU) ?_
        rw [finrank_span_singleton hw0]
        have : 0 < finrank (ZMod 2) U₀ :=
          Nat.pos_of_ne_zero fun h => hb0' (Submodule.finrank_eq_zero.mp h)
        omega
      obtain ⟨w', hw', hw'Q, hw'e⟩ := S.mem_clSub_iff.mp hwU
      have hwY : w ∈ Y := by
        rw [hYmem, ← hw'e]
        refine ⟨(S.polar_cl_eq_zero_iff haQ hw'Q).mpr ?_, (S.polar_cl_eq_zero_iff hbQ hw'Q).mpr ?_⟩
        · exact S.QG_inf_Qa_comm hne ⟨haQ, (S.conjBy g).z_mem_QG⟩ hw'.1
        · exact S.QG_inf_Qa_comm hbne ⟨hbQ, (S.conjBy g').z_mem_QG⟩ ⟨hw'.1.1, hw'.2⟩
      have hqw : S.q w = 0 := S.s12_q_clSub_QG_inf_Qa hne (hU₀Wa hwU)
      obtain ⟨v₀, hv₀Y, hv₀⟩ : ∃ v₀ ∈ Y, polar S.q v₀ w ≠ 0 := by
        by_contra hc
        push Not at hc
        have hwYY : w ∈ LinearMap.BilinForm.orthogonal S.q.polarBilin Y := by
          rw [LinearMap.BilinForm.mem_orthogonal_iff]
          intro v hv
          exact hc v hv
        rw [hY, LinearMap.BilinForm.orthogonal_orthogonal S.q_nondegenerate S.polarBilin_isRefl,
          Submodule.mem_span_pair] at hwYY
        obtain ⟨c₁, c₂, hcw⟩ := hwYY
        rcases OrthoF2.zmod2_eq_zero_or_eq_one c₁ with rfl | rfl <;>
          rcases OrthoF2.zmod2_eq_zero_or_eq_one c₂ with rfl | rfl
        · simp at hcw
          exact hw0 hcw.symm
        · simp at hcw
          exact htbU₀ (hcw ▸ hwU)
        · simp at hcw
          exact haU₀ (hcw ▸ hwU)
        · simp at hcw
          exact habU₀ (hcw ▸ hwU)
      intro v hv
      exact s12_fix_of_apply_sub_mem_span ℓ.2 hqw hv₀Y hv₀
        (fun v hv => hspan ▸ hsubU₀ ℓ hℓ v hv) v hv
  have htY : ∀ v ∈ Y, (t : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
    intro v hv
    have hfs := fixSpace_eq_orthogonal_commSpace_of_mem S.q_nondegenerate t.2
    have : v ∈ fixSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) := by rw [hfs, ← hWspan]; exact hv
    exact mem_fixSpace.mp this
  have hqa : S.q ã = 0 := (S.q_cl_eq_zero_iff haQ).mpr (S.s12_conj_z_sq g)
  have hqb : S.q tb = 0 := (S.q_cl_eq_zero_iff hbQ).mpr (S.s12_conj_z_sq g')
  have hpol : polar S.q ã tb = 0 := s12_polar_eq_zero_of_mem_commSpace htA haW hbW
  have hli : LinearIndependent (ZMod 2) ![ã, tb] :=
    OrthoF2.linearIndependent_pair_iff.mpr ⟨ha0, hb0, hab.symm⟩
  have heich : ∀ y : S.O, y ≠ 1 → (∀ v ∈ Y, (y : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) →
      (y : S.Qt ≃ₗ[ZMod 2] S.Qt) = CFSG.ClassicalGroups.Orthogonal.eichler S.q ã tb := by
    intro y hy1 hyY
    have hy1' : (y : S.Qt ≃ₗ[ZMod 2] S.Qt) ≠ 1 := fun e => hy1 (Subtype.ext e)
    have hfix : ∀ v, polar S.q ã v = 0 → polar S.q tb v = 0 →
        (y : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := fun v h1 h2 => hyY v ((hYmem v).mpr ⟨h1, h2⟩)
    obtain ⟨-, hc, -, -⟩ := timmesfeld_12_2 S.q_nondegenerate y.2 hy1' hli hqa hqb hpol hfix
    rcases eq_one_or_eq_eichler_of_totallySingular S.q_nondegenerate hli hqa hqb hpol y.2 hc.le
      hfix with e | e
    · exact absurd e hy1'
    · exact e
  have ht1 : t ≠ 1 := fun e => htA.2.1 (by rw [e]; rfl)
  have hL₀t : ∀ ℓ ∈ L₀, ℓ ≠ 1 → ℓ = t := fun ℓ hℓ hℓ1 =>
    Subtype.ext ((heich ℓ hℓ1 (hfixY ℓ hℓ)).trans (heich t ht1 htY).symm)
  have hcard0 : Nat.card L₀ ≤ 2 := s12_card_le_two_of_forall_eq L₀ fun x hx y hy hx1 hy1 =>
    (hL₀t x hx hx1).trans (hL₀t y hy hy1).symm
  have hcard := S.s12_card_le_two_mul (L := S.Lbar g) hsplit
  have hge := S.card_Lbar_ge haQ hne
  have h8 : 2 ^ 3 ≤ 2 ^ (S.width - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

end Setting

end CFSG.LargeExtraspecial
