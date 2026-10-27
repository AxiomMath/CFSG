module

public import CFSG.LargeExtraspecial.AS35MSixEightC
public import CFSG.LargeExtraspecial.AS35HSixEightD
public import CFSG.LargeExtraspecial.AS35HSixEightE

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module CFSG.RankThree.OrthogonalInvolutions CQuotE

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

theorem sixSeven_dataE (ih : S14.AschbacherBelow (Nat.card G)) (hS : S.SixHyp)
    (h65 : S.SixFiveConcl) (h67 : S14.AschbacherSixSevenMbarStmt) {r t s : G}
    (hr : r ∈ S.DSet) (ht : t ∈ S.DSet) (hs : s ∈ S.DSet) (hrM : r ∈ S.M) (htM : t ∈ S.M)
    (hsM : s ∈ S.M) (h3 : orderOf (r * t) = 3)
    (hrs : S.ρ ⟨r, hrM⟩ * S.ρ ⟨s, hsM⟩ = S.ρ ⟨s, hsM⟩ * S.ρ ⟨r, hrM⟩)
    (hrs' : S.ρ ⟨r, hrM⟩ ≠ S.ρ ⟨s, hsM⟩)
    (hts : S.ρ ⟨t, htM⟩ * S.ρ ⟨s, hsM⟩ = S.ρ ⟨s, hsM⟩ * S.ρ ⟨t, htM⟩)
    (hts' : S.ρ ⟨t, htM⟩ ≠ S.ρ ⟨s, hsM⟩) :
    ∃ (hE : S.DescentSet (S.EOdd (r * t) : Set G) (r * t))
      (hfixne : fixSpace (S.rhoL hE.x_mem_M) ≠ ⊥)
      (hcent : S.QuotCentHypE (S.EOdd (r * t) : Set G))
      (hO2 : S.QuotOTwoHypE (S.EOdd (r * t) : Set G)),
      (∀ e ∈ (S.EOdd (r * t) : Set G), t * e * t⁻¹ ∈ (S.EOdd (r * t) : Set G)) ∧
      (∀ e ∈ (S.EOdd (r * t) : Set G), t⁻¹ * e * t ∈ (S.EOdd (r * t) : Set G)) ∧
      (S.quotE hE h3 hfixne hcent hO2).width + 2 = S.width ∧
        (S.quotE hE h3 hfixne hcent hO2).AschTwo := by
  have hxM : r * t ∈ S.M := S.M.mul_mem hrM htM
  have hx3 : (r * t) ^ 3 = 1 := pow_three_of_orderOf h3
  have hsr : s * r = r * s := (S.fiveThirteen hS h65 hr hs hrM hsM hrs hrs').symm
  have hst : s * t = t * s := (S.fiveThirteen hS h65 ht hs htM hsM hts hts').symm
  have hxs : r * t * s = s * (r * t) := by
    rw [mul_assoc, ← hst, ← mul_assoc, ← hsr, mul_assoc]
  have hfix := S.commSpace_le_fixSpace_rt h65 hr hs ht hrM hsM htM hrs hrs' hts hts'
  obtain ⟨-, hnc⟩ := S.exists_conj_eq_z_of_sixEightE hxM hx3 hsM hxs hfix hS hs
  obtain ⟨hE, htE, htE', hfixne, hcent, hO2, hdim⟩ :=
    S.sixSevenE_hyps hS h65 h67 hr ht hrM htM h3
  have hn4 := h65.four_le_width
  have hw := S.two_mul_quotE_width hE h3 hfixne hcent hO2
  refine ⟨hE, hfixne, hcent, hO2, htE, htE', by omega, ?_⟩
  exact S.quotE_aschTwo hE h3 hfixne hcent hO2 ih (by omega) hS.weak hS.zInOTwo hnc

omit [Finite G] in
theorem XCxE_le_centralizer {E : Set G} {x t : G} (hE : S.DescentSet E x)
    (h : ∀ c : Cx E, t * ((c : G) * S.z * (c : G)⁻¹) = (c : G) * S.z * (c : G)⁻¹ * t)
    {w : Cx E} (hw : w ∈ S.XCxE hE) : (w : G) * t = t * w := by
  have hle : S.XCxE hE ≤ (centralizer ({t} : Set G)).comap (Cx E).subtype := by
    rw [XCxE, closure_le]
    rintro _ ⟨c, rfl⟩
    rw [SetLike.mem_coe, mem_comap, mem_centralizer_singleton_iff]
    exact (h c).symm
  exact mem_centralizer_singleton_iff.mp (hle hw)

theorem mkQ_eq_one_of_sixEightTwoE {E : Set G} {x d : G} (hE : S.DescentSet E x)
    (hx3 : orderOf x = 3) (hfixne : fixSpace (S.rhoL hE.x_mem_M) ≠ ⊥)
    (hcent : S.QuotCentHypE E) (hO2 : S.QuotOTwoHypE E)
    (hA2 : (S.quotE hE hx3 hfixne hcent hO2).AschTwo)
    (hXa : ∀ w ∈ S.XCxE hE, (w : G) * (d⁻¹ * S.z * d) = d⁻¹ * S.z * d * w)
    {K : Subgroup S.O} (f : S.XCxE hE →* K)
    (hf : ∀ w : S.XCxE hE, ∃ hwM : d * ((w : Cx E) : G) * d⁻¹ ∈ S.M,
      ((f w : K) : S.O) = S.ρ ⟨d * ((w : Cx E) : G) * d⁻¹, hwM⟩)
    {w : S.XCxE hE} (hw : f w ∈ center K) : mkQ E (w : Cx E) = 1 := by
  have hcomm : ∀ w' : S.XCxE hE, (w : Cx E) * w' = w' * w := by
    intro w'
    have h2 := mem_center_iff.mp hw (f w')
    have h3 : f (w * w' * w⁻¹ * w'⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← h2]
      group
    obtain ⟨hcM, hc⟩ := hf (w * w' * w⁻¹ * w'⁻¹)
    have h4 : S.ρ ⟨d * (((w * w' * w⁻¹ * w'⁻¹ : S.XCxE hE) : Cx E) : G) * d⁻¹, hcM⟩ = 1 := by
      rw [← hc]
      exact congrArg Subtype.val h3
    rw [S.ρ_eq_one_iff] at h4
    have hNbot : (S.Qa d⁻¹).comap (Cx E).subtype ⊓ S.XCxE hE = ⊥ := by
      refine S.eq_bot_of_normal_two_XCxE hE hx3 hfixne hcent hO2 hA2 inf_le_right ?_ ?_
      · intro u hu n hn
        refine mem_inf.mpr ⟨?_, mul_mem (mul_mem hu (mem_inf.mp hn).2) (inv_mem hu)⟩
        have hua : (u : G) * (d⁻¹ * S.z * d⁻¹⁻¹) = d⁻¹ * S.z * d⁻¹⁻¹ * u := by
          rw [inv_inv]
          exact hXa u hu
        exact S.conj_mem_Qa_of_commute_asc hua (mem_inf.mp hn).1
      · exact (((S.conjBy d⁻¹).isPGroup_QG.comap_of_injective (Cx E).subtype
          (Cx E).subtype_injective).to_le inf_le_left)
    have h5 : ((w * w' * w⁻¹ * w'⁻¹ : S.XCxE hE) : Cx E) ∈
        (S.Qa d⁻¹).comap (Cx E).subtype ⊓ S.XCxE hE := by
      refine mem_inf.mpr ⟨?_, (w * w' * w⁻¹ * w'⁻¹).2⟩
      change ((((w * w' * w⁻¹ * w'⁻¹ : S.XCxE hE) : Cx E)) : G) ∈ S.Qa d⁻¹
      rw [S.mem_Qa_iff_inv_conj_mem, inv_inv]
      exact h4
    rw [hNbot, mem_bot] at h5
    simp only [coe_mul, coe_inv] at h5
    calc (w : Cx E) * w' = (w : Cx E) * w' * (w : Cx E)⁻¹ * (w' : Cx E)⁻¹ * (w' * w) := by
          group
      _ = w' * w := by rw [h5, one_mul]
  have hmap := S.map_XCxE hE hx3 hfixne hcent hO2
  have hwL : mkQ E (w : Cx E) ∈ (S.quotE hE hx3 hfixne hcent hO2).zGen := by
    rw [← hmap]
    exact ⟨(w : Cx E), w.2, rfl⟩
  refine (S.quotE hE hx3 hfixne hcent hO2).eq_one_of_mem_center_zGen hA2 hwL ?_
  intro l' hl'
  rw [← hmap] at hl'
  obtain ⟨w', hw', rfl⟩ := hl'
  rw [← map_mul, ← map_mul, hcomm ⟨w', hw'⟩]

theorem exists_XCxE_conj_eq (hU : S14.AschTwoAutStmt) {E : Set G} {x : G}
    (hE : S.DescentSet E x) (hx3 : orderOf x = 3) (hfixne : fixSpace (S.rhoL hE.x_mem_M) ≠ ⊥)
    (hcent : S.QuotCentHypE E) (hO2 : S.QuotOTwoHypE E)
    (hw : 2 ≤ (S.quotE hE hx3 hfixne hcent hO2).width)
    (hA2 : (S.quotE hE hx3 hfixne hcent hO2).AschTwo) (c : Cx E) :
    ∃ l ∈ S.XCxE hE, c * S.zCxE hE * c⁻¹ = l * S.zCxE hE * l⁻¹ := by
  obtain ⟨l₁, hl₁, hl₁e⟩ := (hU _ _ hw hA2).2.1 (mkQ E c)
  rw [← S.map_XCxE hE hx3 hfixne hcent hO2] at hl₁
  obtain ⟨l, hlX, rfl⟩ := hl₁
  rw [quotE_z, zQuotE, ← CQuotE.mkQ_conj, ← CQuotE.mkQ_conj] at hl₁e
  exact ⟨l, hlX, eq_of_mkQ_eq (S.conj_zCxE_sq hE c) (S.conj_zCxE_sq hE l) hl₁e⟩

theorem exists_rho_eq_of_sixEightTwoE (hS : S.SixHyp) (h65 : S.SixFiveConcl)
    (hU : S14.AschTwoAutStmt) {E : Set G} {x d : G} (hE : S.DescentSet E x)
    (hx3 : orderOf x = 3) (hfixne : fixSpace (S.rhoL hE.x_mem_M) ≠ ⊥)
    (hcent : S.QuotCentHypE E) (hO2 : S.QuotOTwoHypE E)
    (hwidth : (S.quotE hE hx3 hfixne hcent hO2).width + 2 = S.width)
    (hA2 : (S.quotE hE hx3 hfixne hcent hO2).AschTwo)
    (hXa : ∀ w ∈ S.XCxE hE, (w : G) * (d⁻¹ * S.z * d) = d⁻¹ * S.z * d * w)
    (hYD : ∀ w ∈ S.XCxE hE, d * (w : G) * d⁻¹ ∈ closure S.DSet)
    (hd0 : d * S.z * d⁻¹ ∈ S.DSet) {e : G} (he : e ∈ S.DSet) :
    ∃ w ∈ S.XCxE hE, ∃ hwM : d * (w : G) * d⁻¹ ∈ S.M,
      S.ρ ⟨d * (w : G) * d⁻¹, hwM⟩ = S.ρ ⟨e, S.mem_M_of_mem_ESet hS.sixFour he.1⟩ := by
  have hS4 := hS.sixFour
  have hwM : ∀ w : S.XCxE hE, d * ((w : Cx E) : G) * d⁻¹ ∈ S.M := by
    intro w
    rw [S.mem_M_iff]
    have h1 := hXa w w.2
    calc d * ((w : Cx E) : G) * d⁻¹ * S.z =
        d * (((w : Cx E) : G) * (d⁻¹ * S.z * d)) * d⁻¹ := by group
      _ = d * ((d⁻¹ * S.z * d) * ((w : Cx E) : G)) * d⁻¹ := by rw [h1]
      _ = S.z * (d * ((w : Cx E) : G) * d⁻¹) := by group
  obtain ⟨K, hK⟩ : ∃ K : Subgroup S.O, K = closure S.DbarAsc := ⟨_, rfl⟩
  have hfK : ∀ w : S.XCxE hE, S.ρ ⟨d * ((w : Cx E) : G) * d⁻¹, hwM w⟩ ∈ K := fun w => by
    rw [hK]
    exact S.mem_closure_DbarAsc_of_mem_closure hS4 (hYD w w.2) (hwM w)
  obtain ⟨f, hf⟩ : ∃ f : S.XCxE hE →* K,
      ∀ w, ((f w : K) : S.O) = S.ρ ⟨d * ((w : Cx E) : G) * d⁻¹, hwM w⟩ := by
    refine ⟨MonoidHom.codRestrict (({
        toFun := fun w : S.XCxE hE => S.ρ ⟨d * ((w : Cx E) : G) * d⁻¹, hwM w⟩
        map_one' := by
          rw [← map_one S.ρ]
          congr 1
          exact Subtype.ext (by simp)
        map_mul' := fun a b => by
          rw [← map_mul]
          congr 1
          exact Subtype.ext (by simp only [coe_mul]; group) } : S.XCxE hE →* S.O)) K hfK,
      fun w => rfl⟩
  have hker : ((QuotientGroup.mk' (center K)).comp f).ker ≤
      ((mkQ E).comp (S.XCxE hE).subtype).ker := by
    intro w hw
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hw
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
    exact S.mkQ_eq_one_of_sixEightTwoE hE hx3 hfixne hcent hO2 hA2 hXa f
      (fun w => ⟨hwM w, hf w⟩) hw
  have hψrange : ((mkQ E).comp (S.XCxE hE).subtype).range =
      (S.quotE hE hx3 hfixne hcent hO2).zGen := by
    rw [MonoidHom.range_comp, range_subtype, S.map_XCxE hE hx3 hfixne hcent hO2]
  have hcardle : Nat.card ((mkQ E).comp (S.XCxE hE).subtype).range ≤
      Nat.card ((QuotientGroup.mk' (center K)).comp f).range := by
    rw [← Subgroup.index_ker, ← Subgroup.index_ker]
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Subgroup.index_dvd_of_le hker)
  have hn4 := h65.four_le_width
  obtain ⟨epsu⟩ := h65.psu
  have hP : Nat.card (K ⧸ center K) = Nat.card (CFSG.Open.timmesfeldPSU S.width) := by
    subst hK
    exact Nat.card_congr epsu.toEquiv
  have hU3 := (hU _ (S.quotE hE hx3 hfixne hcent hO2) (by omega) hA2).2.2
  rw [hwidth] at hU3
  have hcard : Nat.card (K ⧸ center K) ≤
      Nat.card ((QuotientGroup.mk' (center K)).comp f).range :=
    calc Nat.card (K ⧸ center K) = Nat.card (CFSG.Open.timmesfeldPSU S.width) := hP
      _ ≤ Nat.card (S.quotE hE hx3 hfixne hcent hO2).zGen := hU3
      _ = Nat.card ((mkQ E).comp (S.XCxE hE).subtype).range :=
          (congrArg (fun H : Subgroup (GQ E) => Nat.card H) hψrange).symm
      _ ≤ _ := hcardle
  have hzX : S.zCxE hE ∈ S.XCxE hE := subset_closure ⟨1, by group⟩
  have hd0M := S.mem_M_of_mem_ESet hS4 hd0.1
  have hd0K : S.ρ ⟨d * S.z * d⁻¹, hd0M⟩ ∈ K := by
    rw [hK]
    exact subset_closure (S.ρ_mem_DbarAsc hd0 hd0M)
  have hd0f : (⟨S.ρ ⟨d * S.z * d⁻¹, hd0M⟩, hd0K⟩ : K) ∈ f.range := by
    refine ⟨⟨S.zCxE hE, hzX⟩, Subtype.ext ?_⟩
    rw [hf]
    rfl
  have heM := S.mem_M_of_mem_ESet hS4 he.1
  obtain ⟨g, hgK, hge⟩ := h65.conj _ (S.ρ_mem_DbarAsc hd0 hd0M) _ (S.ρ_mem_DbarAsc he heM)
  obtain ⟨w, hw⟩ := conj_mem_range_of_card_le f hcard ⟨g, hK ▸ hgK⟩ hd0f
  refine ⟨(w : Cx E), w.2, hwM w, ?_⟩
  have h1 := congrArg Subtype.val hw
  rw [hf] at h1
  rw [h1]
  simpa using hge

end Setting

end CFSG.LargeExtraspecial
