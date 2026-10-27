module

public import CFSG.ClassicalInvolution.Q3.Q3T7F25M1
public import CFSG.ClassicalInvolution.Asc77.AscT7ERNoFour
public import CFSG.ClassicalInvolution.Asc77.AscT7ERConj
public import CFSG.ClassicalInvolution.Asc77.AscT7DRQuat

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false
namespace CFSG.ClassicalInvolution.T7F25

section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace T7C
open CFSG.ClassicalInvolution.Asc77.T7C
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
theorem mem_of_isSylow2In (hΩ : HypOmegaMod Ω) {K R : Subgroup G} {z : G}
    (hK : K ∈ Ω) (hR : IsSylow2In R K) (hz : IsUniqueInvolution K z) : z ∈ R := by
  obtain ⟨x, hx, o⟩ := P25.exists_orderOf_eq_four_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hK hR)
  rw [← T7A.sq_eq_of_orderOf_four hz (hR.1 hx) o]
  exact R.mul_mem hx hx
theorem exists_normal_zpowers_order_four (hΩ : HypOmegaMod Ω) {K R : Subgroup G}
    {z : G} (hK : K ∈ Ω) (hR : IsSylow2In R K) (hz : IsUniqueInvolution K z) :
    ∃ u ∈ R, orderOf u = 4 ∧ ∀ r ∈ R, r * u * r⁻¹ ∈ Subgroup.zpowers u := by
  have hzR : z ∈ R := mem_of_isSylow2In hΩ hK hR hz
  have huniq : IsUniqueInvolution R z :=
    ⟨hzR, hz.ne_one, hz.sq, fun y hy hy2 => hz.unique y (hR.1 hy) hy2⟩
  have h8 : 8 ≤ Nat.card R := hΩ.eight_le_of_mem_RSet (mem_RSet_of_isSylow2In hK hR)
  obtain ⟨A, hAR, hAcyc, hA4, hAinv⟩ := exists_invariant_cyclic_order_four hR.2.1 le_rfl
    (fun q hq => conjSub_eq_self_of_mem hq) huniq (by omega)
  obtain ⟨g, hg⟩ := hAcyc.exists_generator
  have hgord : orderOf g = 4 := (orderOf_eq_card_of_forall_mem_zpowers hg).trans hA4
  refine ⟨(g : G), hAR g.2, by rw [Subgroup.orderOf_coe]; exact hgord, fun r hr => ?_⟩
  have h1 : r * (g : G) * r⁻¹ ∈ conjSub r A := conj_mem_conjSub g.2
  rw [hAinv r hr] at h1
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨_, h1⟩)
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩
end T7C

@[expose] def C25_RS : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z : G), Hyp23Setting Ω K K' z → ∀ W ∈ WSet Ω, z ∈ W → (∀ W' ∈ WSet Ω, MuIsoE4 Ω W') →
      ∃ (S : Sylow 2 G) (R R' : Subgroup G),
        (R ∈ RSet Ω ∧ R ≤ K ∧ R ≤ (S : Subgroup G)) ∧
        (R' ∈ RSet Ω ∧ R' ≤ K' ∧ R' ≤ (S : Subgroup G)) ∧
        ∀ X ∈ RSet Ω, X ≤ (S : Subgroup G) → X = R ∨ X = R'
end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Asc77.T7C2
open scoped commutatorElement

@[expose] def C25_20 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 Ω K K' W S R R' z t u₁ u₂ →
      Nat.card ↥(S : Subgroup G) = 4 * Nat.card ↥(R ⊔ R') →
        ∃ s t' : G, s ∈ (S : Subgroup G) ∧ t' ∈ (S : Subgroup G) ∧ (∃ g : G, g * z * g⁻¹ = t') ∧
          conjSub t' R = R' ∧ s * s = 1 ∧ s * t' = t' * s ∧ conjSub s R = R ∧
          (∃ r ∈ R, ⁅s, r⁆ ∉ T7DR.squaresSub R) ∧
          Subgroup.closure (((R ⊔ R' : Subgroup G) : Set G) ∪ {s, t'}) = (S : Subgroup G)
end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace T7D
open CFSG.ClassicalInvolution.Asc77.T7D
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

theorem ctx_of_stand {K : Subgroup G} (hs : AscStand Ω K) (hW : W ∈ WSet Ω) :
    Q3.Q3CL.Thompson.Ctx Ω W :=
  ⟨hs.hyp, hW,
    hs.key W hW, hs.aEmpty⟩
theorem exists_rep (hΩ : HypOmegaMod Ω) (hW : W ∈ WSet Ω)
    {K R : Subgroup G} (hK : K ∈ Ω) (hRK : IsSylow2In R K) (hRD : R ∈ DSet Ω W) :
    ∃ ρ : Thompson.Rep Ω W, ρ.K = K ∧ ρ.R = R := by
  obtain ⟨-, -, -, -, hcard⟩ := Q3.Q3CL.Thompson.inf_W_of_mem_D hΩ hW hRD hK hRK
  have hnle : ¬ R ≤ W := by
    intro hle
    rw [inf_eq_left.mpr hle] at hcard
    have : 0 < Nat.card ↥R := Nat.card_pos
    omega
  obtain ⟨r, hr, hrW⟩ := Set.not_subset.mp hnle
  exact ⟨⟨K, R, r, hK, hRD, hRK, hr, hrW⟩, rfl, rfl⟩

theorem exists_sylow_frame {K K' : Subgroup G} {z : G} (hs : Hyp23Setting Ω K K' z)
    (hW : W ∈ WSet Ω) (hzW : z ∈ W) :
    ∃ (S : Sylow 2 G) (R R' : Subgroup G), W ≤ (S : Subgroup G) ∧ IsSylow2In R K ∧
      IsSylow2In R' K' ∧ R ≤ (S : Subgroup G) ∧ R' ≤ (S : Subgroup G) := by
  have hst : AscStand Ω K := hs.stand
  have hΩ : HypOmegaMod Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have hK' : K' ∈ Ω := hs.hK'.1
  have hz : IsUniqueInvolution K z := hs.hz
  have hz' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hs.hK'
  have hW2 : IsPGroup 2 W := Thompson.isPGroup_of_mem_WSet hW
  have hWab := Q3.Q3CL.Thompson.commutes_of_mem_WSet hΩ hW
  have hWC : W ≤ Subgroup.centralizer ({z} : Set G) := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hWab w hw z hzW)
  obtain ⟨T, hT, hWT⟩ := IsSylow2In.exists_ge hW2 hWC
  have hR : IsSylow2In (T ⊓ K) K :=
    AscP1Nine3.isSylow2In_inf_of_isSubnormal hT (hst.subn _ hK hz)
  have hR' : IsSylow2In (T ⊓ K') K' :=
    AscP1Nine3.isSylow2In_inf_of_isSubnormal hT (hst.subn _ hK' hz')
  obtain ⟨S, hTS⟩ := hT.2.1.exists_le_sylow
  exact ⟨S, T ⊓ K, T ⊓ K', hWT.trans hTS, hR, hR', inf_le_left.trans hTS,
    inf_le_left.trans hTS⟩
end T7D

theorem c25_RS_proved : C25_RS := by
  intro G _ _ Ω K K' z hs W hW hzW hE4
  have hst : AscStand Ω K := hs.stand
  have hΩ : HypOmegaMod Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have hK' : K' ∈ Ω := hs.hK'.1
  have hKK' : K' ≠ K := hs.hne
  obtain ⟨S, R, R', hWS, hR, hR', hRS, hR'S⟩ := T7D.exists_sylow_frame hs hW hzW
  have hRK : K ⊓ (S : Subgroup G) = R :=
    hR.eq_of_le S.isPGroup'.to_inf_right inf_le_left (le_inf hR.1 hRS)
  have hRK' : K' ⊓ (S : Subgroup G) = R' :=
    hR'.eq_of_le S.isPGroup'.to_inf_right inf_le_left (le_inf hR'.1 hR'S)
  refine ⟨S, R, R', ⟨mem_RSet_of_isSylow2In hK hR, hR.1, hRS⟩,
    ⟨mem_RSet_of_isSylow2In hK' hR', hR'.1, hR'S⟩, ?_⟩
  intro X hX hXS
  obtain ⟨J, hJ, hXJ⟩ := exists_isSylow2In_of_mem_RSet hX
  by_cases hJK : J = K
  · subst hJK
    left
    have hXle : X ≤ J ⊓ (S : Subgroup G) := le_inf hXJ.1 hXS
    rw [hRK] at hXle
    exact (hXJ.eq_of_le hR.2.1 hR.1 hXle).symm
  by_cases hJK' : J = K'
  · subst hJK'
    right
    have hXle : X ≤ J ⊓ (S : Subgroup G) := le_inf hXJ.1 hXS
    rw [hRK'] at hXle
    exact (hXJ.eq_of_le hR'.2.1 hR'.1 hXle).symm
  exfalso
  have hc : Q3.Q3CL.Thompson.Ctx Ω W := T7D.ctx_of_stand hst hW
  have hRD : R ∈ DSet Ω W :=
    Q3.Q3CL.Thompson.mem_DSet_of_le_sylow hΩ hW hWS (mem_RSet_of_isSylow2In hK hR) hRS
  have hXD : X ∈ DSet Ω W := Q3.Q3CL.Thompson.mem_DSet_of_le_sylow hΩ hW hWS hX hXS
  obtain ⟨ρ, hρK, hρR⟩ := T7D.exists_rep hΩ hW hK hR hRD
  obtain ⟨σ, hσK, hσR⟩ := T7D.exists_rep hΩ hW hJ hXJ hXD
  have hcomm : ρ.img * σ.img = σ.img * ρ.img := by
    have := T7D.muGroup_comm_of_E4 (hE4 W hW) ⟨ρ.img, T7D.rep_img_mem ρ⟩ ⟨σ.img, T7D.rep_img_mem σ⟩
    exact congrArg Subtype.val this
  have hne : ρ.K ≠ σ.K := by
    rw [hρK, hσK]
    exact fun h => hJK h.symm
  have hnbr : σ.K ∈ omegaNbr Ω ρ.K := P25.omega_of_comm hc ρ σ hne hcomm
  rw [hρK, hσK] at hnbr
  have hperp : J ∈ KPerp Ω K := Set.mem_insert_of_mem _ hnbr
  rw [hs.perp] at hperp
  rcases hperp with h | h
  · exact hJK h
  · exact hJK' h
end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace T7ER
open CFSG.ClassicalInvolution.Asc77.T7ER
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem omegaStarNbr_subset_omegaNbr_of_E4 {K K₁ : Subgroup G} (hs : AscStand Ω K)
    {W₀ : Subgroup G} (hW₀ : W₀ ∈ WSet Ω) (hE4 : ∀ W' ∈ WSet Ω, MuIsoE4 Ω W') (hK₁ : K₁ ∈ Ω) :
    omegaStarNbr Ω K₁ ⊆ omegaNbr Ω K₁ := by
  intro J hJ
  by_contra hnot
  have hΩ : HypOmegaMod Ω := hs.hyp
  obtain ⟨W, hW, R, hR, T, hT, hRK, hTJ⟩ :=
    Thompson.exists_W_of_mem_omegaStarNbr hΩ hK₁ hJ
  have hJΩ : J ∈ Ω := hJ.1
  obtain ⟨ρ, hρK, hρR⟩ := T7D.exists_rep hΩ hW hK₁ hRK hR
  obtain ⟨σ, hσK, hσR⟩ := T7D.exists_rep hΩ hW hJΩ hTJ hT
  have hc : Q3.Q3CL.Thompson.Ctx Ω W := T7D.ctx_of_stand hs hW
  have hne : ρ.K ≠ σ.K := by
    rw [hρK, hσK]
    exact fun h => hJ.2.1 h.symm
  have hnot' : σ.K ∉ omegaNbr Ω ρ.K := by
    rw [hρK, hσK]
    exact hnot
  have hncomm := hc.noncomm ρ σ hne hnot'
  have hab : ∀ a b : ↥(muGroup Ω W), a * b = b * a := fun a b =>
    T7D.muGroup_comm_of_E4 (hE4 W hW) a b
  exact hncomm (congrArg Subtype.val
    (hab ⟨ρ.img, T7D.rep_img_mem ρ⟩ ⟨σ.img, T7D.rep_img_mem σ⟩))
end T7ER
end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace T7ER
open CFSG.ClassicalInvolution.Asc77.T7ER
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' : Subgroup G} {z : G}

theorem not_le_centralizer_of_mem_USet (hs : Hyp23Setting Ω K K' z) {W₀ : Subgroup G}
    (hW₀ : W₀ ∈ WSet Ω) (hE4 : ∀ W' ∈ WSet Ω, MuIsoE4 Ω W') {J : Subgroup G} (hJ : J ∈ Ω)
    (hJt : J ∉ twinSet Ω K) {V : Subgroup G} (hV : V ∈ USet Ω) (hVJ : V ≤ J) :
    ¬ V ≤ Subgroup.centralizer ({z} : Set G) := by
  intro hVC
  have hst : AscStand Ω K := hs.stand
  have hΩ : HypOmegaMod Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have hKt : K ∈ twinSet Ω K := ⟨hK, z, hs.hz, hs.hz⟩
  have hKJ : K ≠ J := fun h => hJt (h ▸ hKt)
  have hV2 : IsPGroup 2 V := hΩ.isPGroup_of_mem_USet hV
  obtain ⟨-, -, -, -, -, -, -, -, hV4⟩ := hΩ.exists_data_of_mem_USet hV
  have hVN : V ≤ Subgroup.normalizer (K : Set G) :=
    hΩ.le_normalizer_of_le_centralizer hK hJ hKJ hs.hz hVJ hV2 (by omega) hVC
  have hstar : J ∈ omegaStarNbr Ω K := ⟨hJ, hKJ.symm, V, hV, hVJ, hVN⟩
  have hnbr := omegaStarNbr_subset_omegaNbr_of_E4 hst hW₀ hE4 hK hstar
  have hperp : J ∈ KPerp Ω K := Set.mem_insert_of_mem _ hnbr
  rw [hs.perp] at hperp
  rcases hperp with h | h
  · exact hKJ h.symm
  · exact hJt (h ▸ hs.hK')

theorem not_commute_of_orderOf_four (hs : Hyp23Setting Ω K K' z) {W₀ : Subgroup G}
    (hW₀ : W₀ ∈ WSet Ω) (hE4 : ∀ W' ∈ WSet Ω, MuIsoE4 Ω W') {J : Subgroup G} (hJ : J ∈ Ω)
    (hJt : J ∉ twinSet Ω K) {x : G} (hx : x ∈ J) (hx4 : orderOf x = 4) : z * x ≠ x * z := by
  intro hxz
  have hst : AscStand Ω K := hs.stand
  have hΩ : HypOmegaMod Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  obtain ⟨tJ, htJ⟩ := hΩ.exists_uniqueInvolution hJ
  have hxx : x * x = tJ := T7A.sq_eq_of_orderOf_four htJ hx hx4
  have hxC : x ∈ J ⊓ Subgroup.centralizer ({z} : Set G) :=
    ⟨hx, Subgroup.mem_centralizer_singleton_iff.mpr hxz.symm⟩
  have hx2 : IsPGroup 2 (Subgroup.zpowers x) := by
    refine IsPGroup.of_card (n := 2) ?_
    rw [Nat.card_zpowers, hx4]
    norm_num
  obtain ⟨V, hV, hxV⟩ := IsSylow2In.exists_ge hx2
    (Subgroup.zpowers_le.mpr hxC : Subgroup.zpowers x ≤ J ⊓ Subgroup.centralizer ({z} : Set G))
  have hxVm : x ∈ V := hxV (Subgroup.mem_zpowers x)
  have htV : tJ ∈ V := hxx ▸ V.mul_mem hxVm hxVm
  have hVJ : V ≤ J := hV.1.trans inf_le_left
  have hVC : V ≤ Subgroup.centralizer ({z} : Set G) := hV.1.trans inf_le_right
  have hnot2 : V ≠ Subgroup.zpowers tJ := by
    intro hVt
    rw [hVt] at hxVm
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxVm
    have h1 : x * x = 1 := by
      rw [← hk, ← zpow_add, ← two_mul, zpow_mul]
      have h2 : tJ ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact htJ.sq
      rw [h2, one_zpow]
    have h3 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h1)
    rw [hx4] at h3
    omega
  rcases l6_2 G Ω hΩ K hK z hs.hz J hJ hJt tJ htJ V hV htV with
    h | h | h | h
  · exact hnot2 h.1
  · exact hnot2 h.1
  · exact not_le_centralizer_of_mem_USet hs hW₀ hE4 hJ hJt h.1 hVJ hVC
  · have hVsyl : IsSylow2In V J := T7C.isSylow2In_of_mem_RSet_of_le hΩ hJ h.1 hVJ
    obtain ⟨U, hUV, hUc, hUcard⟩ := (hΩ.isQuatSub_of_mem_RSet h.1).exists_cyclic_index_two
    exact not_le_centralizer_of_mem_USet hs hW₀ hE4 hJ hJt
      (mem_USet_of_natCard hJ hVsyl hUV hUc hUcard) (hUV.trans hVJ) (hUV.trans hVC)

theorem not_commute_of_conj (hs : Hyp23Setting Ω K K' z) {W₀ : Subgroup G}
    (hW₀ : W₀ ∈ WSet Ω) (hE4 : ∀ W' ∈ WSet Ω, MuIsoE4 Ω W') {J : Subgroup G} (hJ : J ∈ Ω) {a : G}
    (ha : IsUniqueInvolution J a) {y : G} (hya : y * z * y⁻¹ ≠ a) {x : G} (hx : x ∈ J)
    (hx4 : orderOf x = 4) : (y * z * y⁻¹) * x ≠ x * (y * z * y⁻¹) := by
  intro hc
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hJ' : conjSub y⁻¹ J ∈ Ω := hΩ.conjInvariant y⁻¹ J hJ
  have ha' : IsUniqueInvolution (conjSub y⁻¹ J) (y⁻¹ * a * y⁻¹⁻¹) := ha.conj y⁻¹
  have hne : y⁻¹ * a * y⁻¹⁻¹ ≠ z := by
    intro h
    apply hya
    have : a = y * z * y⁻¹ := by
      have h2 : y * (y⁻¹ * a * y⁻¹⁻¹) * y⁻¹ = a := by group
      rw [← h2, h]
    exact this.symm
  have hx' : y⁻¹ * x * y ∈ conjSub y⁻¹ J := by
    have := conj_mem_conjSub (n := y⁻¹) hx
    simpa [mul_assoc] using this
  have hord : orderOf (y⁻¹ * x * y) = 4 := by
    have h := MulEquiv.orderOf_eq (MulAut.conj y⁻¹) x
    simp only [MulAut.conj_apply, inv_inv] at h
    rw [h, hx4]
  have hcomm : z * (y⁻¹ * x * y) = (y⁻¹ * x * y) * z := by
    calc z * (y⁻¹ * x * y) = y⁻¹ * ((y * z * y⁻¹) * x) * y := by group
      _ = y⁻¹ * (x * (y * z * y⁻¹)) * y := by rw [hc]
      _ = (y⁻¹ * x * y) * z := by group
  exact not_commute_of_orderOf_four hs hW₀ hE4 hJ' (not_mem_twinSet_of_ne hs.hz ha' hne) hx'
    hord hcomm
end T7ER
end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace T7ER
open CFSG.ClassicalInvolution.Asc77.T7ER
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' : Subgroup G} {z : G}

theorem conjSub_eq_of_centralizes (hs : Hyp23Setting Ω K K' z) {u : G} (hu : u * z = z * u) :
    conjSub u K = K ∨ conjSub u K = K' := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hmem : conjSub u K ∈ twinSet Ω K := by
    refine ⟨hΩ.conjInvariant u K hK, z, hs.hz, ?_⟩
    have := hs.hz.conj u
    have hz : u * z * u⁻¹ = z := by rw [hu]; group
    rwa [hz] at this
  rw [hs.twinSet_eq] at hmem
  exact hmem

theorem normalizes_iff_of_centralizes (hs : Hyp23Setting Ω K K' z) {u : G}
    (hu : u * z = z * u) : conjSub u K = K ↔ conjSub u K' = K' := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hK' : K' ∈ Ω := hs.hK'.1
  have hne : K' ≠ K := hs.hne
  have hz' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hs.hz hs.hK'
  have hmem' : conjSub u K' ∈ twinSet Ω K := by
    refine ⟨hΩ.conjInvariant u K' hK', z, hs.hz, ?_⟩
    have := hz'.conj u
    have hz : u * z * u⁻¹ = z := by rw [hu]; group
    rwa [hz] at this
  rw [hs.twinSet_eq] at hmem'
  constructor
  · intro h
    rcases hmem' with h' | h'
    · exact absurd (conjSub_injective u (h.trans h'.symm)) hne.symm
    · exact h'
  · intro h
    rcases conjSub_eq_of_centralizes hs hu with h' | h'
    · exact h'
    · exact absurd (conjSub_injective u (h.trans h'.symm)) hne
end T7ER
end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace T7ER
open CFSG.ClassicalInvolution.Asc77.T7ER
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ : G}

theorem exists_notNormalizing_conj (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {g : G}
    (hg : g * z * g⁻¹ = t) (hRt : conjSub t R = R) :
    ∃ s' : G, s' * s' = 1 ∧ s' * z = z * s' ∧ (∃ y : G, y * z * y⁻¹ = s') ∧
      conjSub s' K ≠ K := by
  have hs : Hyp23Setting Ω K K' z := hyp.std.setting
  have hst : AscStand Ω K := hs.stand
  have hΩ : HypOmegaMod Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have hK' : K' ∈ Ω := hs.hK'.1
  have hKK' : K' ≠ K := hs.hne
  have hz : IsUniqueInvolution K z := hs.hz
  have hz' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hs.hK'
  have hW₀ : W ∈ WSet Ω := hyp.hW
  have hE4 := hyp.hE4
  have hRsyl : IsSylow2In R K := T7C.isSylow2In_of_mem_RSet_of_le hΩ hK hyp.hR.1 hyp.hR.2.1
  have hR'syl : IsSylow2In R' K' :=
    T7C.isSylow2In_of_mem_RSet_of_le hΩ hK' hyp.hR'.1 hyp.hR'.2.1
  have hRS : R ≤ (S : Subgroup G) := hyp.hR.2.2
  have hR'S : R' ≤ (S : Subgroup G) := hyp.hR'.2.2
  have hc : Commutes R R' := hΩ.commutes_of_twin_of_isPGroup hK hK' hKK'.symm hz hz'
    (hRsyl.1) (hR'syl.1) (S.isPGroup'.to_le (sup_le hRS hR'S))
  have hRq : IsQuatSub R := hΩ.isQuatSub_of_mem_RSet hyp.hR.1
  have hR'q : IsQuatSub R' := hΩ.isQuatSub_of_mem_RSet hyp.hR'.1
  have hzR : IsUniqueInvolution R z :=
    ⟨T7C.mem_of_isSylow2In hΩ hK hRsyl hz, hz.ne_one, hz.sq,
      fun y hy hy2 => hz.unique y (hRsyl.1 hy) hy2⟩
  have hzR' : IsUniqueInvolution R' z :=
    ⟨T7C.mem_of_isSylow2In hΩ hK' hR'syl hz', hz.ne_one, hz.sq,
      fun y hy hy2 => hz'.unique y (hR'syl.1 hy) hy2⟩
  have hRR'inf : Nat.card ↥(R ⊓ R') ≤ 2 :=
    hΩ.card_le_two_of_le_inf hK hK' hKK'.symm
      (hRsyl.2.1.to_le (inf_le_left : R ⊓ R' ≤ R)) (inf_le_left.trans hRsyl.1)
      (inf_le_right.trans hR'syl.1)
  have hinf : ∀ y ∈ R, y ∈ R' → orderOf y ≠ 4 := by
    intro y hyR hyR' hy4
    have hle : Subgroup.zpowers y ≤ R ⊓ R' := Subgroup.zpowers_le.mpr ⟨hyR, hyR'⟩
    have h1 := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, hy4] at h1
    omega
  obtain ⟨htS, htz, -⟩ := hyp.ht
  have ht2 : t * t = 1 := by
    rw [← hg]
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hz.sq]; group
  have hRt' : conjSub t R' = R' := by
    have hmem : conjSub t R' ∈ RSet Ω := RSet.conj hΩ.conjInvariant hyp.hR'.1 t
    have hle : conjSub t R' ≤ (S : Subgroup G) := by
      intro x hx
      rw [mem_conjSub_iff] at hx
      have h1 : t * (t⁻¹ * x * t) * t⁻¹ ∈ (S : Subgroup G) :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ htS (hR'S hx)) (Subgroup.inv_mem _ htS)
      simpa [mul_assoc] using h1
    rcases hyp.hRS _ hmem hle with h | h
    · exfalso
      have h1 : conjSub t (conjSub t R') = conjSub t R := by rw [h]
      have h2 : conjSub t (conjSub t R') = R' := by
        rw [← conjSub_mul]
        have : t * t = 1 := ht2
        rw [this, conjSub_one]
      rw [h2, hRt] at h1

      have hRR' : R = R' := h1.symm
      have : Nat.card ↥R ≤ 2 := by
        have := hΩ.card_le_two_of_le_inf hK hK' hKK'.symm hRsyl.2.1 hRsyl.1
          (hRR' ▸ hR'syl.1)
        exact this
      have := hRq.eight_le
      omega
    · exact h
  have htR : ∀ r ∈ R, t * r * t⁻¹ ∈ R := fun r hr => by
    have := conj_mem_conjSub (n := t) hr
    rwa [hRt] at this
  have htR' : ∀ r ∈ R', t * r * t⁻¹ ∈ R' := fun r hr => by
    have := conj_mem_conjSub (n := t) hr
    rwa [hRt'] at this
  have hfix : ∀ {J : Subgroup G} {a : G}, J ∈ Ω → IsUniqueInvolution J a →
      (∀ y : G, y * z * y⁻¹ = t → t ≠ a → ∀ x ∈ J, orderOf x = 4 → t * x * t⁻¹ ≠ x) := by
    intro J a hJ ha y hy hta x hx hx4 h
    have := not_commute_of_conj hs hW₀ hE4 hJ ha (y := y) (by rw [hy]; exact hta) hx hx4
    rw [hy] at this
    apply this
    have h1 := congrArg (fun w => w * t) h
    simpa [mul_assoc] using h1
  have hfixR : ∀ x ∈ R, orderOf x = 4 → t * x * t⁻¹ ≠ x :=
    fun x hx hx4 => hfix hK hz g hg htz x (hRsyl.1 hx) hx4
  have hfixR' : ∀ x ∈ R', orderOf x = 4 → t * x * t⁻¹ ≠ x :=
    fun x hx hx4 => hfix hK' hz' g hg htz x (hR'syl.1 hx) hx4
  obtain ⟨x, c₁, ω, hc₁R, hc₁4, hωc₁, hω2, htω, hω1, hωz, hxt⟩ :=
    exists_twisted_conj hRq hR'q hzR hzR' hc hinf ht2 htR htR' hfixR hfixR'
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2

  have hs2 : (t * ω) * (t * ω) = 1 := by
    calc (t * ω) * (t * ω) = (t * (ω * t)) * ω := by group
      _ = (t * (t * ω)) * ω := by rw [htω]
      _ = (t * t) * (ω * ω) := by group
      _ = 1 := by rw [ht2, hω2]; group
  have hst : (t * ω) * t = t * (t * ω) := by
    calc (t * ω) * t = t * (ω * t) := by group
      _ = t * (t * ω) := by rw [htω]
  have hsne : t * ω ≠ t := by
    intro h
    apply hω1
    have := congrArg (fun w => t⁻¹ * w) h
    simpa using this
  obtain ⟨hsy⟩ : Nonempty (∃ y : G, y * z * y⁻¹ = t * ω) := by
    refine ⟨⟨x⁻¹ * g, ?_⟩⟩
    calc x⁻¹ * g * z * (x⁻¹ * g)⁻¹ = x⁻¹ * (g * z * g⁻¹) * x := by group
      _ = x⁻¹ * t * x := by rw [hg]
      _ = t * ω := hxt
  have hts : t * (t * ω) = ω := by
    calc t * (t * ω) = (t * t) * ω := by group
      _ = ω := by rw [ht2]; group
  have hnotz : ¬ ∃ y : G, y * z * y⁻¹ = t * (t * ω) := by
    rintro ⟨y, hy⟩
    rw [hts] at hy
    have := not_commute_of_conj hs hW₀ hE4 hK hz (y := y) (by rw [hy]; exact hωz)
      (hRsyl.1 hc₁R) hc₁4
    rw [hy] at this
    exact this hωc₁
  have hnotN : conjSub (t * ω) (conjSub g K) ≠ conjSub g K := by
    intro hN
    have hJt : conjSub g K ∈ Ω := hΩ.conjInvariant g K hK
    have htJ : IsUniqueInvolution (conjSub g K) t := by
      have := hz.conj g
      rwa [hg] at this
    have hsN : t * ω ∈ Subgroup.normalizer ((conjSub g K : Subgroup G) : Set G) :=
      mem_normalizer_iff_conjSub_eq.mpr hN
    obtain ⟨Rt, hRtsyl, hRtinv⟩ := T3.exists_sylow_normalized (isPGroup_zpowers_of_sq hs2)
      (Subgroup.zpowers_le.mpr hsN)
    have hRtmem : Rt ∈ RSet Ω := mem_RSet_of_isSylow2In hJt hRtsyl
    have hRtq : IsQuatSub Rt := hΩ.isQuatSub_of_mem_RSet hRtmem
    have htRt : t ∈ Rt := T7C.mem_of_isSylow2In hΩ hJt hRtsyl htJ
    have hzRt : IsUniqueInvolution Rt t :=
      ⟨htRt, htJ.ne_one, htJ.sq, fun y hy hy2 => htJ.unique y (hRtsyl.1 hy) hy2⟩
    have hsRt : conjSub (t * ω) Rt = Rt := hRtinv _ (Subgroup.mem_zpowers _)
    have hbR : ∀ r ∈ Rt, (t * ω) * r * (t * ω)⁻¹ ∈ Rt := fun r hr => by
      have := conj_mem_conjSub (n := t * ω) hr
      rwa [hsRt] at this
    have hfixt : ∀ r ∈ Rt, orderOf r = 4 → (t * ω) * r * (t * ω)⁻¹ ≠ r := by
      intro r hr hr4 h
      obtain ⟨y, hy⟩ := hsy
      have := not_commute_of_conj hs hW₀ hE4 hJt htJ (y := y) (by rw [hy]; exact hsne)
        (hRtsyl.1 hr) hr4
      rw [hy] at this
      apply this
      have h1 := congrArg (fun w => w * (t * ω)) h
      simpa [mul_assoc] using h1
    obtain ⟨ρ, hρ, hρs⟩ := exists_conj_eq_mul_inv hRtq hzRt hs2 hbR hfixt
    apply hnotz
    obtain ⟨y, hy⟩ := hsy
    refine ⟨ρ⁻¹ * y, ?_⟩
    calc ρ⁻¹ * y * z * (ρ⁻¹ * y)⁻¹ = ρ⁻¹ * (y * z * y⁻¹) * ρ := by group
      _ = ρ⁻¹ * (t * ω) * ρ := by rw [hy]
      _ = ρ⁻¹ * ((t * ω) * ρ * (t * ω)⁻¹) * (t * ω) := by group
      _ = ρ⁻¹ * (ρ * t) * (t * ω) := by rw [hρs]
      _ = t * (t * ω) := by group

  refine ⟨g⁻¹ * (t * ω) * g, ?_, ?_, ?_, ?_⟩
  · calc g⁻¹ * (t * ω) * g * (g⁻¹ * (t * ω) * g) = g⁻¹ * ((t * ω) * (t * ω)) * g := by group
      _ = 1 := by rw [hs2]; group
  · have hzg : z = g⁻¹ * t * g := by rw [← hg]; group
    calc g⁻¹ * (t * ω) * g * z = g⁻¹ * ((t * ω) * t) * g := by rw [hzg]; group
      _ = g⁻¹ * (t * (t * ω)) * g := by rw [hst]
      _ = z * (g⁻¹ * (t * ω) * g) := by rw [hzg]; group
  · obtain ⟨y, hy⟩ := hsy
    refine ⟨g⁻¹ * y, ?_⟩
    calc g⁻¹ * y * z * (g⁻¹ * y)⁻¹ = g⁻¹ * (y * z * y⁻¹) * g := by group
      _ = g⁻¹ * (t * ω) * g := by rw [hy]
  · intro hN
    apply hnotN
    have h1 : conjSub (g * (g⁻¹ * (t * ω) * g)) K = conjSub ((t * ω) * g) K := by
      congr 1; group
    rw [conjSub_mul, hN, conjSub_mul] at h1
    exact h1.symm
end T7ER
end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected

theorem c25_2_t_proved : C25_2_t := by
  intro G _ _ Ω K K' W S R R' z t u₁ u₂ hyp
  have hs : Hyp23Setting Ω K K' z := hyp.std.setting
  have hst : AscStand Ω K := hs.stand
  have hΩ : HypOmegaMod Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have hK' : K' ∈ Ω := hs.hK'.1
  have hKK' : K' ≠ K := hs.hne
  have hRsyl : IsSylow2In R K := T7C.isSylow2In_of_mem_RSet_of_le hΩ hK hyp.hR.1 hyp.hR.2.1
  have hRS : R ≤ (S : Subgroup G) := hyp.hR.2.2
  obtain ⟨htS, htz, g, hg⟩ := hyp.ht
  have hmem : conjSub t R ∈ RSet Ω := RSet.conj hΩ.conjInvariant hyp.hR.1 t
  have hle : conjSub t R ≤ (S : Subgroup G) := by
    intro x hx
    rw [mem_conjSub_iff] at hx
    have h1 : t * (t⁻¹ * x * t) * t⁻¹ ∈ (S : Subgroup G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ htS (hRS hx)) (Subgroup.inv_mem _ htS)
    simpa [mul_assoc] using h1
  rcases hyp.hRS _ hmem hle with hRt | hRt
  · obtain ⟨s', hs'2, hs'z, ⟨y, hy⟩, hs'K⟩ := T7ER.exists_notNormalizing_conj hyp hg hRt
    obtain ⟨c, hcz, hcS⟩ := T7ER.exists_conj_mem_sylow_of_centralizes S hyp.hzS hs'2 hs'z
    refine ⟨c⁻¹ * s' * c, hcS, ⟨c⁻¹ * y, ?_⟩, ?_⟩
    · calc c⁻¹ * y * z * (c⁻¹ * y)⁻¹ = c⁻¹ * (y * z * y⁻¹) * c := by group
        _ = c⁻¹ * s' * c := by rw [hy]
    · have hmem' : conjSub (c⁻¹ * s' * c) R ∈ RSet Ω :=
        RSet.conj hΩ.conjInvariant hyp.hR.1 _
      have hle' : conjSub (c⁻¹ * s' * c) R ≤ (S : Subgroup G) := by
        intro x hx
        rw [mem_conjSub_iff] at hx
        have h1 : (c⁻¹ * s' * c) * ((c⁻¹ * s' * c)⁻¹ * x * (c⁻¹ * s' * c)) * (c⁻¹ * s' * c)⁻¹ ∈
            (S : Subgroup G) :=
          Subgroup.mul_mem _ (Subgroup.mul_mem _ hcS (hRS hx)) (Subgroup.inv_mem _ hcS)
        simpa [mul_assoc] using h1
      rcases hyp.hRS _ hmem' hle' with h | h
      · exfalso

        have hKt : conjSub (c⁻¹ * s' * c) K = K := by
          by_contra hne
          have hK2 : conjSub (c⁻¹ * s' * c) K ∈ Ω := hΩ.conjInvariant _ K hK
          have hRK : R ≤ conjSub (c⁻¹ * s' * c) K := h ▸ conjSub_mono hRsyl.1
          have := hΩ.card_le_two_of_le_inf hK hK2 (Ne.symm hne) hRsyl.2.1 hRsyl.1 hRK
          have h8 := (hΩ.isQuatSub_of_mem_RSet hyp.hR.1).eight_le
          omega
        have h1 : conjSub s' (conjSub c K) = conjSub c K := by
          have h2 : conjSub (c * (c⁻¹ * s' * c)) K = conjSub (s' * c) K := by
            congr 1; group
          rw [conjSub_mul, hKt, conjSub_mul] at h2
          exact h2.symm
        rcases T7ER.conjSub_eq_of_centralizes hs hcz with h3 | h3
        · rw [h3] at h1
          exact hs'K h1
        · rw [h3] at h1
          exact hs'K ((T7ER.normalizes_iff_of_centralizes hs hs'z).mpr h1)
      · exact h
  · exact ⟨t, htS, ⟨g, hg⟩, hRt⟩
end Asc77
end
end CFSG.ClassicalInvolution.T7F25
