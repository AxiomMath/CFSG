module

public import CFSG.GH74.GLS.C3.Layer1.St1PumpL2
public import CFSG.GH74.GLS.C3.Layer1.St1PumpGen
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.IG327Proof
public import CFSG.GH74.E2.Shapes
public import CFSG.GH74.GLS.TwoThin.G.Reduction
public import CFSG.GH74.GLS.C3.Layer1.St1Prop51

public section

namespace CFSG.GH74.GLS.C3.Layer1.PumpCalc

open scoped commutatorElement

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin
  CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial

section Defs

variable {G : Type} [Group G]

abbrev bar (u : G) (X : Subgroup G) : Subgroup (barQ ↥(centralizer ({u} : Set G))) :=
  (X.subgroupOf (centralizer ({u} : Set G))).map (barMk ↥(centralizer ({u} : Set G)))

@[expose] def sbar {u : G} (z : G) (hz : z ∈ centralizer ({u} : Set G)) :
    barQ ↥(centralizer ({u} : Set G)) :=
  barMk ↥(centralizer ({u} : Set G)) ⟨z, hz⟩

structure IsLam (z u : G) (J Λ : Subgroup G) : Prop where
  le : Λ ≤ J ⊓ centralizer ({u} : Set G)
  layer : pLayerOf 2 (J ⊓ centralizer ({u} : Set G)) = Λ
  pc : IsPCompIn 2 (J ⊓ centralizer ({u} : Set G)) Λ
  uniq : ∀ L : Subgroup G, IsPCompIn 2 (J ⊓ centralizer ({u} : Set G)) L → L = Λ
  pcW : IsPCompIn 2 (centralizer ({z} : Set G) ⊓ centralizer ({u} : Set G)) Λ
  twoElt : ∀ g ∈ J ⊓ centralizer ({u} : Set G), (∃ n : ℕ, g ^ (2 ^ n) = 1) → g ∈ Λ
  cover : ∀ k ∈ J, ∃ l ∈ Λ, ∃ o ∈ pPrimeCoreOf 2 J, k = l * o

end Defs

section Basic

variable {G : Type} [Group G] {z u q : G} {J H Λ X : Subgroup G}

theorem map_conj_bar_of_normalizes (hq : q ∈ centralizer ({u} : Set G))
    (hqX : q ∈ normalizer (X : Set G)) :
    (bar u X).map (MulAut.conj (sbar q hq)).toMonoidHom = bar u X := by
  set Y' := centralizer ({u} : Set G) with hY'
  ext w
  constructor
  · rintro ⟨_, ⟨m, hm, rfl⟩, rfl⟩
    have hmX : (m : G) ∈ X := Subgroup.mem_subgroupOf.mp hm
    have hq1 : q * (m : G) * q⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hqX _).mp hmX
    refine ⟨⟨q, hq⟩ * m * ⟨q, hq⟩⁻¹, Subgroup.mem_subgroupOf.mpr hq1, ?_⟩
    simp [sbar, map_mul]
  · rintro ⟨m, hm, rfl⟩
    have hmX : (m : G) ∈ X := Subgroup.mem_subgroupOf.mp hm
    have hq1 : q⁻¹ * (m : G) * q ∈ X := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hqX) _).mp hmX
      simpa using this
    refine ⟨_, ⟨⟨q, hq⟩⁻¹ * m * ⟨q, hq⟩, Subgroup.mem_subgroupOf.mpr hq1, rfl⟩, ?_⟩
    simp [sbar, map_mul]
    group

variable [Finite G]

theorem exists_isLam (hu : orderOf u = 2) (hJ : IsPCompIn 2 (centralizer ({z} : Set G)) J)
    (huJ : u ∈ centralizerSection J (pPrimeCoreOf 2 J)) : ∃ Λ : Subgroup G, IsLam z u J Λ := by
  obtain ⟨Λ, hle, hlay, hpc, huniq, hpcW, h2el, hcov⟩ := pumpup_cover hu hJ huJ
  exact ⟨Λ, ⟨hle, hlay, hpc, huniq, hpcW, h2el, hcov⟩⟩

theorem orderOf_sbar (hz : orderOf z = 2) (hzu : z ∈ centralizer ({u} : Set G)) :
    orderOf (sbar z hzu) = 2 := by
  have h := orderOf_barMk (Y := ↥(centralizer ({u} : Set G))) (s := ⟨z, hzu⟩)
    (orderOf_mk_centralizer hzu hz)
  exact h

theorem bar_le_of_stable (hlt : PumpUpLT 2 z J u H) (hΛ : IsLam z u J Λ)
    (hzH : z ∈ normalizer (H : Set G)) : bar u Λ ≤ bar u H := by
  have hz : orderOf z = 2 := hlt.1.1
  have hzY : z ∈ centralizer ({u} : Set G) := mem_centralizer_symm hlt.2.2.1
  set Y' := centralizer ({u} : Set G) with hY'
  have hso : orderOf (⟨z, hzY⟩ : ↥Y') = 2 := orderOf_mk_centralizer hzY hz
  have hΛC := le_centralizer_mk (isPCompIn_two_iff.mp hΛ.pcW).1 hzY
  have hΛ2 := isTwoComponent_centralizer_mk hΛ.pcW hzY
  obtain ⟨hΛE, hJsub, L, hL, hcases, hLJ, hLsJ, hiff⟩ := pumpupY_structure hso hΛC hΛ2
  obtain ⟨hK'2, hK'J⟩ := isTwoComponent_of_isPCompIn_pumpUp hΛ.layer hΛE hlt.2.2.2.2
  have himg := (hiff _ hK'2).mp hK'J
  have hs2 : orderOf (sbar z hzY) = 2 := orderOf_sbar hz hzY
  have hsinv : (barMk ↥Y' ⟨z, hzY⟩)⁻¹ = barMk ↥Y' ⟨z, hzY⟩ := inv_eq_self_of_orderOf_eq_two hs2
  have hMstab := map_conj_bar_of_normalizes (u := u) (X := H) hzY hzH
  have hMeq : bar u H = (H.subgroupOf Y').map (barMk ↥Y') := rfl
  have hLstab : conjSub (barMk ↥Y' ⟨z, hzY⟩)⁻¹ L = L := by
    rw [hsinv]
    rcases himg with h | h
    · have : bar u H = L := h
      rw [← this]
      exact hMstab
    · have hh : bar u H = conjSub (barMk ↥Y' ⟨z, hzY⟩)⁻¹ L := h
      rw [hsinv] at hh
      have h2 : conjSub (barMk ↥Y' ⟨z, hzY⟩) (conjSub (barMk ↥Y' ⟨z, hzY⟩) L) = L := by
        have := conjSub_conjSub_of_inv_eq hsinv L
        rwa [hsinv] at this
      have h3 : (conjSub (barMk ↥Y' ⟨z, hzY⟩) L).map (MulAut.conj (sbar z hzY)).toMonoidHom =
          conjSub (barMk ↥Y' ⟨z, hzY⟩) L := by
        rw [← hh]
        exact hMstab
      exact h3.symm.trans h2
  have hHL : bar u H = L := by
    rcases himg with h | h
    · exact h
    · exact h.trans hLstab
  rcases hcases with ⟨-, hΛL⟩ | ⟨hne, -⟩
  · rw [hHL]
    exact hΛL
  · exact absurd hLstab hne

theorem isComponent_bar (hH : IsPCompIn 2 (centralizer ({u} : Set G)) H) :
    CFSG.IsComponent (bar u H) :=
  isComponent_map_barMk (isPCompIn_two_iff.mp hH).2

theorem kBar_equiv_bar (hH : IsPCompIn 2 (centralizer ({u} : Set G)) H) :
    Nonempty (kBar H ≃* ↥(bar u H)) := by
  obtain ⟨e1⟩ := hat_equiv_subgroupOf hH.1
  obtain ⟨e2⟩ := hat_equiv_map
    (Components.mathlib_subnormal_of_chain (isPCompIn_two_iff.mp hH).2.1 Subgroup.IsSubnormal.top)
  exact ⟨e1.trans e2⟩

theorem isTwoComponent_lam (hΛ : IsLam z u J Λ) :
    TwoComponents.IsTwoComponent
      ((Λ.subgroupOf (centralizer ({u} : Set G))).subgroupOf
        ((centralizer ({z} : Set G) ⊓ centralizer ({u} : Set G)).subgroupOf
          (centralizer ({u} : Set G)))) :=
  isTwoComponent_subgroupOf_subgroupOf (isPCompIn_two_iff.mp hΛ.pcW).1 inf_le_right
    (isPCompIn_two_iff.mp hΛ.pcW).2

theorem lam_perfect_Y (hΛ : IsLam z u J Λ) :
    ⁅Λ.subgroupOf (centralizer ({u} : Set G)), Λ.subgroupOf (centralizer ({u} : Set G))⁆ =
      Λ.subgroupOf (centralizer ({u} : Set G)) := by
  have hle := (isPCompIn_two_iff.mp hΛ.pcW).1
  exact commutator_self_of_isTwoComponent
    (fun a ha => Subgroup.mem_subgroupOf.mpr (hle (Subgroup.mem_subgroupOf.mp ha)))
    (isTwoComponent_lam hΛ)

theorem lam_ne_bot_Y (hΛ : IsLam z u J Λ) :
    Λ.subgroupOf (centralizer ({u} : Set G)) ≠ ⊥ := by
  have hle := (isPCompIn_two_iff.mp hΛ.pcW).1
  exact ne_bot_of_isTwoComponent (isTwoComponent_lam hΛ)

theorem bar_lam_perfect (hΛ : IsLam z u J Λ) : ⁅bar u Λ, bar u Λ⁆ = bar u Λ := by
  unfold bar
  rw [← Subgroup.map_commutator, lam_perfect_Y hΛ]

theorem bar_lam_ne_bot (hΛ : IsLam z u J Λ) : bar u Λ ≠ ⊥ :=
  map_barMk_ne_bot_of_perfect (lam_perfect_Y hΛ) (lam_ne_bot_Y hΛ)

omit [Finite G] in
theorem bar_lam_le_centralizer (hzY : z ∈ centralizer ({u} : Set G)) (hΛ : IsLam z u J Λ) :
    ∀ w ∈ bar u Λ, sbar z hzY * w * (sbar z hzY)⁻¹ = w := by
  rintro _ ⟨m, hm, rfl⟩
  have hmz : (m : G) ∈ centralizer ({z} : Set G) :=
    (isPCompIn_two_iff.mp hΛ.pcW).1 (Subgroup.mem_subgroupOf.mp hm) |>.1
  have hc : (m : G) * z = z * (m : G) := mem_centralizer_singleton_iff.mp hmz
  have : (⟨z, hzY⟩ : ↥(centralizer ({u} : Set G))) * m * ⟨z, hzY⟩⁻¹ = m := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc z * (m : G) * z⁻¹ = (m : G) * z * z⁻¹ := by rw [hc]
      _ = m := by group
  simp only [sbar]
  rw [← map_inv, ← map_mul, ← map_mul, this]

theorem perfect_subgroupOf_eq_bot {K : Type*} [Group K] {A B : Subgroup K} (hAB : A ≤ B)
    (hA : ⁅A, A⁆ = A) (hsolv : Group.IsSolvable ↥(A.subgroupOf B)) : A = ⊥ := by
  by_contra hne
  have hperf : ⁅A.subgroupOf B, A.subgroupOf B⁆ = A.subgroupOf B := by
    apply Subgroup.map_injective B.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hAB, hA]
  have hnt : Nontrivial ↥(A.subgroupOf B) := by
    rw [Subgroup.nontrivial_iff_ne_bot]
    intro hbot
    apply hne
    have := congrArg (Subgroup.map B.subtype) hbot
    rwa [Subgroup.map_subgroupOf_eq_of_le hAB, Subgroup.map_bot] at this
  have h1 := Group.IsSolvable.commutator_lt_top_of_nontrivial ↥(A.subgroupOf B)
  have h2 : commutator ↥(A.subgroupOf B) = ⊤ := by
    have : Group.IsPerfect ↥(A.subgroupOf B) := Subgroup.isPerfect_iff.mpr hperf
    exact Group.IsPerfect.commutator_eq_top
  rw [h2] at h1
  exact lt_irrefl _ h1

theorem sbar_central (hlt : PumpUpLT 2 z J u H) (hΛ : IsLam z u J Λ)
    (hzY : z ∈ centralizer ({u} : Set G)) (hzH : z ∈ normalizer (H : Set G))
    (hL : HasL2Model ↥(bar u H) IsFM9) :
    ∀ l ∈ bar u H, sbar z hzY * l * (sbar z hzY)⁻¹ = l := by
  by_contra hcon
  push Not at hcon
  obtain ⟨l₀, hl₀, hne⟩ := hcon
  have hs2 : orderOf (sbar z hzY) = 2 := orderOf_sbar hlt.1.1 hzY
  have hsq : sbar z hzY * sbar z hzY = 1 := by
    have := pow_orderOf_eq_one (sbar z hzY)
    rwa [hs2, pow_two] at this
  have hMstab := map_conj_bar_of_normalizes (u := u) (X := H) hzY hzH
  have hN : sbar z hzY ∈ normalizer ((bar u H : Subgroup _) : Set _) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hMstab
  let σ := conjAut hN
  have hσ : ∀ l, σ (σ l) = l := by
    intro l
    apply Subtype.ext
    show sbar z hzY * (sbar z hzY * (l : _) * (sbar z hzY)⁻¹) * (sbar z hzY)⁻¹ = l
    calc sbar z hzY * (sbar z hzY * (l : _) * (sbar z hzY)⁻¹) * (sbar z hzY)⁻¹
        = (sbar z hzY * sbar z hzY) * (l : _) * (sbar z hzY * sbar z hzY)⁻¹ := by group
      _ = l := by rw [hsq]; group
  have hσ1 : ∃ l, σ l ≠ l := ⟨⟨l₀, hl₀⟩, fun h => hne (congrArg Subtype.val h)⟩
  have hΛL := bar_le_of_stable hlt hΛ hzH
  have hF : ∀ l ∈ (bar u Λ).subgroupOf (bar u H), σ l = l := by
    intro l hl
    apply Subtype.ext
    exact bar_lam_le_centralizer hzY hΛ (l : _) (Subgroup.mem_subgroupOf.mp hl)
  have hsolv := PumpL2.solvable_of_fixed_fm9 hL σ hσ hσ1 _ hF
  exact bar_lam_ne_bot hΛ (perfect_subgroupOf_eq_bot hΛL (bar_lam_perfect hΛ) hsolv)

theorem exists_noncomm_of_isQuasisimple' {K : Type} [Group K] (hK : CFSG.IsQuasisimple K) :
    ∃ a b : K, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := hK.2.2
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  refine ⟨a', b', fun h => hab ?_⟩
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h]

theorem stable_trivial (hlt : PumpUpLT 2 z J u H) (hΛ : IsLam z u J Λ)
    (hzY : z ∈ centralizer ({u} : Set G)) (hzH : z ∈ normalizer (H : Set G))
    (hcen : ∀ l ∈ bar u H, sbar z hzY * l * (sbar z hzY)⁻¹ = l)
    (hsimple : IsSimpleGroup ↥(bar u H)) :
    Nonempty (kBar H ≃* kBar J) ∧ (∀ q ∈ CxK z J, u * q = q * u → q ∈ CxK u H) ∧
      z ∈ CxK u H := by
  have hu : orderOf u = 2 := hlt.2.1.1
  have hz : orderOf z = 2 := hlt.1.1
  have hH : IsPCompIn 2 (centralizer ({u} : Set G)) H := hlt.2.1.2.2
  have hJ : IsPCompIn 2 (centralizer ({z} : Set G)) J := hlt.1.2.2
  set Y' := centralizer ({u} : Set G) with hY'
  have hΛJ : Λ ≤ J := hΛ.le.trans inf_le_left
  have hΛY : Λ ≤ Y' := hΛ.le.trans inf_le_right
  have hHY : H ≤ Y' := hH.1
  have hH2 : TwoComponents.IsTwoComponent (H.subgroupOf Y') := (isPCompIn_two_iff.mp hH).2
  have hΛL := bar_le_of_stable hlt hΛ hzH
  have hso : orderOf (⟨z, hzY⟩ : ↥Y') = 2 := orderOf_mk_centralizer hzY hz
  have hEq : bar u Λ = bar u H := by
    have hΛC := le_centralizer_mk (isPCompIn_two_iff.mp hΛ.pcW).1 hzY
    have hΛ2 := isTwoComponent_centralizer_mk hΛ.pcW hzY
    have hmap2 := isTwoComponent_map_barMk hso hΛC hΛ2
    have hsubC : ((bar u Λ).subgroupOf (centralizer ({sbar z hzY} : Set _))).IsSubnormal :=
      Components.mathlib_subnormal_of_chain hmap2.1 Subgroup.IsSubnormal.top
    have hHC : bar u H ≤ centralizer ({sbar z hzY} : Set _) := fun l hl =>
      mem_centralizer_singleton_iff.mpr (by
        have := hcen l hl
        calc l * sbar z hzY = sbar z hzY * l * (sbar z hzY)⁻¹ * sbar z hzY := by rw [this]
          _ = sbar z hzY * l := by group)
    have hsubH := isSubnormal_inf_subgroupOf hsubC hHC
    have hqs : CFSG.IsQuasisimple ↥(bar u H) :=
      (AssemblyBPredicates.isQuasisimple_iff_native _).1
        (assembly_isQuasisimple_of_isComponent (isComponent_bar hH))
    rcases LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hqs hsubH with
      htop | hcent
    · refine le_antisymm hΛL fun l hl => ?_
      have : (⟨l, hl⟩ : ↥(bar u H)) ∈ (bar u Λ).subgroupOf (bar u H) := by rw [htop]; trivial
      exact Subgroup.mem_subgroupOf.mp this
    · exfalso
      refine bar_lam_ne_bot hΛ ?_
      have hc : ⁅bar u Λ, bar u Λ⁆ = ⊥ := by
        rw [Subgroup.commutator_le.mpr (fun a ha b hb => ?_) |> fun h => (le_bot_iff.mp h)]
        have h1 := hcent (Subgroup.mem_subgroupOf.mpr ha : (⟨a, hΛL ha⟩ : ↥(bar u H)) ∈
          (bar u Λ).subgroupOf (bar u H))
        have h2 := Subgroup.mem_center_iff.mp h1 ⟨b, hΛL hb⟩
        have h3 : b * a = a * b := congrArg Subtype.val h2
        rw [Subgroup.mem_bot, commutatorElement_def]
        calc a * b * a⁻¹ * b⁻¹ = (a * b) * (b * a)⁻¹ := by group
          _ = 1 := by rw [h3]; group
      rw [← bar_lam_perfect hΛ, hc]
  obtain ⟨φ, hφs, hφo, hφρ⟩ := exists_phi hΛJ hΛY hΛ.cover
  have hsimpleΛ : IsSimpleGroup ↥(bar u Λ) := by
    have e := (MulEquiv.subgroupCongr hEq)
    exact e.isSimpleGroup
  have hJq : CFSG.IsQuasisimple (kBar J) := isQuasisimple_hat hJ
  have hφinj : Function.Injective φ := by
    rcases (IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker) with h | h
    · exact (MonoidHom.ker_eq_bot_iff φ).mp h
    · exfalso
      obtain ⟨a, b, hab⟩ := exists_noncomm_of_isQuasisimple' hJq
      obtain ⟨a', rfl⟩ := hφs a
      obtain ⟨b', rfl⟩ := hφs b
      apply hab
      have h1 : φ a' = 1 := by
        have : a' ∈ φ.ker := by rw [h]; trivial
        exact this
      have h2 : φ b' = 1 := by
        have : b' ∈ φ.ker := by rw [h]; trivial
        exact this
      rw [h1, h2]
  have hφb : Function.Bijective φ := ⟨hφinj, hφs⟩
  obtain ⟨e⟩ := kBar_equiv_bar hH
  have hπz : ∀ m ∈ H.subgroupOf Y', barMk ↥Y' (⟨z, hzY⟩ * m * ⟨z, hzY⟩⁻¹) = barMk ↥Y' m := by
    intro m hm
    have hmL : barMk ↥Y' m ∈ bar u H := ⟨m, hm, rfl⟩
    have := hcen _ hmL
    simpa [sbar, map_mul] using this
  have hzC : z ∈ centralizerSection H (pPrimeCoreOf 2 H) :=
    mem_centralizerSection_of_map_eq hHY hH2 hzY hπz
  refine ⟨⟨e.trans ((MulEquiv.subgroupCongr hEq.symm).trans (MulEquiv.ofBijective φ hφb))⟩, ?_,
    Subgroup.mem_inf.mpr ⟨hzY, hzC⟩⟩
  intro q hq huq
  have hqs : q ∈ centralizerSection J (pPrimeCoreOf 2 J) := hq.2
  have hqY : q ∈ Y' := by
    rw [hY', Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff.mp hg]
    exact huq
  have hqX : q ∈ normalizer ((J ⊓ Y' : Subgroup G) : Set G) :=
    TwoThin.mem_normalizer_inf hqs.1 (Subgroup.le_normalizer hqY)
  have hΛq : ∀ a ∈ Λ, q * a * q⁻¹ ∈ Λ := fun a ha =>
    conj_mem_of_unique_isPCompIn hΛ.pc hΛ.uniq hqX ha
  have hstar : ∀ (a : G) (ha : a ∈ Λ),
      barMk ↥Y' (⟨q, hqY⟩ * ⟨a, hΛY ha⟩ * ⟨q, hqY⟩⁻¹) = barMk ↥Y' ⟨a, hΛY ha⟩ := by
    intro a ha
    have haq : q * a * q⁻¹ ∈ Λ := hΛq a ha
    have hbΛ : q * a * q⁻¹ * a⁻¹ ∈ Λ := mul_mem haq (inv_mem ha)
    have hbO : q * a * q⁻¹ * a⁻¹ ∈ pPrimeCoreOf 2 J := by
      have := inv_mem (hqs.2.2 a (hΛJ ha))
      simpa [commutatorElement_def, mul_assoc] using this
    have h1 : hatMap hΛJ ⟨q * a * q⁻¹ * a⁻¹, hbΛ⟩ = 1 := (hatMap_eq_one_iff hΛJ _).mpr hbO
    have h2 := hφρ _ hbΛ
    rw [h1] at h2
    have h3 : (⟨barMk ↥Y' ⟨q * a * q⁻¹ * a⁻¹, hΛY hbΛ⟩,
        ⟨⟨_, hΛY hbΛ⟩, Subgroup.mem_subgroupOf.mpr hbΛ, rfl⟩⟩ : ↥(bar u Λ)) = 1 :=
      hφinj (h2.trans (map_one φ).symm)
    have h4 : barMk ↥Y' ⟨q * a * q⁻¹ * a⁻¹, hΛY hbΛ⟩ = 1 := congrArg Subtype.val h3
    have h5 : (⟨q * a * q⁻¹ * a⁻¹, hΛY hbΛ⟩ : ↥Y') =
        ⟨q, hqY⟩ * ⟨a, hΛY ha⟩ * ⟨q, hqY⟩⁻¹ * ⟨a, hΛY ha⟩⁻¹ := rfl
    rw [h5, map_mul, mul_eq_one_iff_eq_inv, ← map_inv] at h4
    rw [h4]
    simp
  have hπ : ∀ m ∈ H.subgroupOf Y', barMk ↥Y' (⟨q, hqY⟩ * m * ⟨q, hqY⟩⁻¹) = barMk ↥Y' m := by
    intro m hm
    have hmL : barMk ↥Y' m ∈ bar u Λ := by
      rw [hEq]
      exact ⟨m, hm, rfl⟩
    obtain ⟨a', ha', hmm⟩ := hmL
    have ha'Λ : (a' : G) ∈ Λ := Subgroup.mem_subgroupOf.mp ha'
    have h1 := hstar a' ha'Λ
    have e1 : barMk ↥Y' (⟨q, hqY⟩ * m * ⟨q, hqY⟩⁻¹) =
        barMk ↥Y' ⟨q, hqY⟩ * barMk ↥Y' m * (barMk ↥Y' ⟨q, hqY⟩)⁻¹ := by simp [map_mul]
    have e2 : barMk ↥Y' (⟨q, hqY⟩ * a' * ⟨q, hqY⟩⁻¹) =
        barMk ↥Y' ⟨q, hqY⟩ * barMk ↥Y' a' * (barMk ↥Y' ⟨q, hqY⟩)⁻¹ := by simp [map_mul]
    rw [e1, ← hmm, ← e2]
    exact h1
  have hcs := mem_centralizerSection_of_map_eq hHY hH2 hqY hπ
  show q ∈ centralizer ({u} : Set G) ⊓ centralizerSection H (pPrimeCoreOf 2 H)
  exact Subgroup.mem_inf.mpr ⟨hqY, hcs⟩

omit [Finite G] in
theorem conj_mem_cSec {g c : G} {J : Subgroup G} (hg : g ∈ normalizer (J : Set G))
    (hc : c ∈ centralizerSection J (pPrimeCoreOf 2 J)) :
    g * c * g⁻¹ ∈ centralizerSection J (pPrimeCoreOf 2 J) := by
  obtain ⟨hcJ, hcO, hcomm⟩ := hc
  have hgO : g ∈ normalizer (pPrimeCoreOf 2 J : Set G) := mem_normalizer_pPrimeCoreOf hg
  refine ⟨mul_mem (mul_mem hg hcJ) (inv_mem hg), mul_mem (mul_mem hgO hcO) (inv_mem hgO),
    fun k hk => ?_⟩
  have hk' : g⁻¹ * k * g ∈ J := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) k).mp hk
    simpa using this
  have h1 := hcomm _ hk'
  have e : ⁅k, g * c * g⁻¹⁆ = g * ⁅g⁻¹ * k * g, c⁆ * g⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [e]
  have := (Subgroup.mem_normalizer_iff.mp hgO _).mp h1
  exact this

theorem barMk_eq_one_of_mem_pPrimeCoreOf {Y' H : Subgroup G} (hHY : H ≤ Y')
    (hsub : (H.subgroupOf Y').IsSubnormal) {k : G} (hk : k ∈ pPrimeCoreOf 2 H) (hkY : k ∈ Y') :
    barMk ↥Y' ⟨k, hkY⟩ = 1 := by
  rw [pPrimeCoreOf_eq_map_subgroupOf hHY] at hk
  obtain ⟨y₁, hy₁, hy₁k⟩ := hk
  obtain ⟨m, hm, hmy⟩ := hy₁
  have hmker : m ∈ ((QuotientGroup.mk' (pPrimeCore 2 ↥Y')).comp (H.subgroupOf Y').subtype).ker := by
    rw [ker_restrict_eq_pPrimeCore hsub]
    exact hm
  have h1 : barMk ↥Y' (m : ↥Y') = 1 := hmker
  have h2 : (⟨k, hkY⟩ : ↥Y') = (m : ↥Y') := by
    apply Subtype.ext
    exact ((congrArg Subtype.val hmy).trans hy₁k).symm
  rw [h2]
  exact h1

theorem map_eq_of_mem_cSec {u q : G} {H : Subgroup G}
    (hH : IsPCompIn 2 (centralizer ({u} : Set G)) H)
    (hq : q ∈ centralizer ({u} : Set G)) (hqH : q ∈ centralizerSection H (pPrimeCoreOf 2 H)) :
    ∀ m ∈ H.subgroupOf (centralizer ({u} : Set G)),
      barMk ↥(centralizer ({u} : Set G)) (⟨q, hq⟩ * m * ⟨q, hq⟩⁻¹) =
        barMk ↥(centralizer ({u} : Set G)) m := by
  intro m hm
  have hsub : (H.subgroupOf (centralizer ({u} : Set G))).IsSubnormal :=
    Components.mathlib_subnormal_of_chain (isPCompIn_two_iff.mp hH).2.1 Subgroup.IsSubnormal.top
  have hmH : (m : G) ∈ H := Subgroup.mem_subgroupOf.mp hm
  have h1 := hqH.2.2 _ hmH
  have hcY : ⁅(m : G), q⁆ ∈ centralizer ({u} : Set G) := by
    simp only [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem m.2 hq) (inv_mem m.2)) (inv_mem hq)
  have h2 := barMk_eq_one_of_mem_pPrimeCoreOf hH.1 hsub h1 hcY
  have h3 : (⟨⁅(m : G), q⁆, hcY⟩ : ↥(centralizer ({u} : Set G))) =
      m * ⟨q, hq⟩ * m⁻¹ * ⟨q, hq⟩⁻¹ := rfl
  rw [h3] at h2
  simp only [map_mul, map_inv] at h2
  rw [map_mul, map_mul, map_inv]
  generalize barMk ↥(centralizer ({u} : Set G)) m = a at h2 ⊢
  generalize barMk ↥(centralizer ({u} : Set G)) ⟨q, hq⟩ = b at h2 ⊢
  have h5 : a * b * a⁻¹ = b := mul_inv_eq_one.mp h2
  have h4 : a * b = b * a := by
    calc a * b = (a * b * a⁻¹) * a := by group
      _ = b * a := by rw [h5]
  calc b * a * b⁻¹ = (a * b) * b⁻¹ := by rw [h4]
    _ = a := by group

theorem gsFixedLayer_le_sup_conjugate_of_pumpup
    (hlt : PumpUpLT 2 z J u H) :
    CFSG.ComponentClassification.UnbalancedGS.gsFixedLayer J u ≤ H ⊔ conjugate H z := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Y : Subgroup G := centralizer ({u} : Set G)
  have hMY : H ≤ Y := hlt.2.1.2.2.1
  have hzY : z ∈ Y := mem_centralizer_symm hlt.2.2.1
  have hMaY : conjugate H z ≤ Y := by
    intro y hy
    rw [CFSG.ComponentClassification.UnbalancedLayer.mem_conjugate_iff] at hy
    have h1 : z⁻¹ * (z * y * z⁻¹) * z ∈ Y :=
      Y.mul_mem (Y.mul_mem (Y.inv_mem hzY) (hMY hy)) hzY
    rwa [show z⁻¹ * (z * y * z⁻¹) * z = y by group] at h1
  obtain ⟨Λ, hΛ⟩ := exists_isLam hlt.2.1.1 hlt.1.2.2 hlt.2.2.2.1
  have hΛY : Λ ≤ Y := hΛ.le.trans inf_le_right
  let s : Y := ⟨z, hzY⟩
  have hso : orderOf s = 2 := orderOf_mk_centralizer hzY hlt.1.1
  have hΛC : Λ.subgroupOf Y ≤ centralizer ({s} : Set Y) :=
    le_centralizer_mk hΛ.pcW.1 hzY
  have hΛ2 : TwoComponents.IsTwoComponent
      ((Λ.subgroupOf Y).subgroupOf (centralizer ({s} : Set Y))) :=
    isTwoComponent_centralizer_mk hΛ.pcW hzY
  obtain ⟨hΛE, -, L, hL, hcases, -, -, hiff⟩ :=
    pumpupY_structure (s := s) (Λ := Λ.subgroupOf Y) hso hΛC hΛ2
  obtain ⟨hM2, hMJ⟩ := isTwoComponent_of_isPCompIn_pumpUp hΛ.layer hΛE hlt.2.2.2.2
  have himp := (hiff (H.subgroupOf Y) hM2).mp hMJ
  have ht2 : orderOf (barMk Y s) = 2 := orderOf_barMk hso
  have htinv : (barMk Y s)⁻¹ = barMk Y s := inv_eq_self_of_orderOf_eq_two ht2
  have hconjH : ((conjugate H z).subgroupOf Y).map (barMk Y) =
      conjSub (barMk Y s)⁻¹ ((H.subgroupOf Y).map (barMk Y)) := by
    rw [← CFSG.ComponentClassification.UnbalancedLayer.conjugate_subgroupOf_eq H Y s,
      CFSG.ComponentClassification.UnbalancedLayer.map_conjugate]
    rfl
  have hsupH : ((H.subgroupOf Y ⊔ (conjugate H z).subgroupOf Y)).map (barMk Y) =
      L ⊔ conjSub (barMk Y s)⁻¹ L := by
    rw [Subgroup.map_sup, hconjH]
    rcases himp with h | h
    · rw [h]
    · rw [h]
      rw [conjSub_conjSub_of_inv_eq htinv L, sup_comm]
  have hΛbar : (Λ.subgroupOf Y).map (barMk Y) ≤
      L ⊔ conjSub (barMk Y s)⁻¹ L := by
    rcases hcases with ⟨-, hle⟩ | ⟨-, hAB, hle⟩
    · exact hle.trans le_sup_left
    · refine hle.trans ?_
      rintro _ ⟨k, rfl⟩
      exact swapDiag_mem_sup hAB k
  have hΛbar' : (Λ.subgroupOf Y).map (barMk Y) ≤
      ((H.subgroupOf Y ⊔ (conjugate H z).subgroupOf Y)).map (barMk Y) := by
    rw [hsupH]
    exact hΛbar
  have hΛY_sup : Λ.subgroupOf Y ≤
      (H.subgroupOf Y ⊔ (conjugate H z).subgroupOf Y) ⊔ pPrimeCore 2 Y := by
    intro l hl
    have hmap : barMk Y l ∈
        ((H.subgroupOf Y ⊔ (conjugate H z).subgroupOf Y)).map (barMk Y) :=
      hΛbar' (Subgroup.mem_map_of_mem _ hl)
    obtain ⟨k, hk, hkl⟩ := Subgroup.mem_map.mp hmap
    have hdiff : l * k⁻¹ ∈ pPrimeCore 2 Y := by
      apply (QuotientGroup.eq_one_iff (N := pPrimeCore 2 Y) (l * k⁻¹)).mp
      have hkl' : QuotientGroup.mk' (pPrimeCore 2 Y) k =
          QuotientGroup.mk' (pPrimeCore 2 Y) l := hkl
      show QuotientGroup.mk' (pPrimeCore 2 Y) (l * k⁻¹) = 1
      rw [map_mul, map_inv, ← hkl', mul_inv_cancel]
    rw [show l = (l * k⁻¹) * k by group]
    exact mul_mem (Subgroup.mem_sup_right hdiff) (Subgroup.mem_sup_left hk)
  have hΛperf : ⁅Λ, Λ⁆ = Λ := by
    rw [← hΛ.layer, CFSG.GH74.GLS.Stage1.Thm2.Recip.IG327B.pLayerOf_eq_map' 2 (J ⊓ Y),
      ← Subgroup.map_commutator, CFSG.ComponentClassification.UnbalancedCorr.pLayer_two_isPerfect]
  have hΛY_perf : ⁅Λ.subgroupOf Y, Λ.subgroupOf Y⁆ = Λ.subgroupOf Y := by
    apply Subgroup.map_injective Y.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hΛY, hΛperf]
  have hNnorm : pPrimeCore 2 Y ≤
      normalizer ((H.subgroupOf Y ⊔ (conjugate H z).subgroupOf Y : Subgroup Y) : Set Y) := by
    have hMp : IsPComponent 2 (H.subgroupOf Y) := hlt.2.1.2.2.2
    have hMaP : IsPComponent 2 ((conjugate H z).subgroupOf Y) := by
      rw [← CFSG.ComponentClassification.UnbalancedLayer.conjugate_subgroupOf_eq H Y s]
      exact CFSG.ComponentClassification.UnbalancedLayer.isPComponent_conjugate hMp s
    have h1 : pPrimeCore 2 Y ≤ normalizer (H.subgroupOf Y : Set Y) :=
      CFSG.ComponentClassification.UnbalancedLayer.pPrimeCore_le_normalizer hMp
    have h2 : pPrimeCore 2 Y ≤ normalizer ((conjugate H z).subgroupOf Y : Set Y) :=
      CFSG.ComponentClassification.UnbalancedLayer.pPrimeCore_le_normalizer hMaP
    exact (le_inf h1 h2).trans (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have hNodd : Odd (Nat.card (pPrimeCore 2 Y)) := odd_card_pPrimeCore Y
  have hΛY_M : Λ.subgroupOf Y ≤ H.subgroupOf Y ⊔ (conjugate H z).subgroupOf Y :=
    CFSG.ComponentClassification.UnbalancedLayer.le_of_perfect_le_sup_of_odd
      (K := H.subgroupOf Y ⊔ (conjugate H z).subgroupOf Y) (R := pPrimeCore 2 Y)
      (T := Λ.subgroupOf Y) hNodd hNnorm (Subgroup.isPerfect_iff.mpr hΛY_perf) hΛY_sup
  have hgs : CFSG.ComponentClassification.UnbalancedGS.gsFixedLayer J u = Λ := by
    unfold CFSG.ComponentClassification.UnbalancedGS.gsFixedLayer
    rw [← CFSG.GH74.GLS.Stage1.Thm2.Recip.IG327B.pLayerOf_eq_map' 2 (J ⊓ Y)]
    exact hΛ.layer
  rw [hgs]
  intro l hl
  have hlY : l ∈ Y := hΛY hl
  have hmem : (⟨l, hlY⟩ : Y) ∈ H.subgroupOf Y ⊔ (conjugate H z).subgroupOf Y :=
    hΛY_M (Subgroup.mem_subgroupOf.mpr hl)
  rw [← Subgroup.subgroupOf_sup hMY hMaY] at hmem
  exact Subgroup.mem_subgroupOf.mp hmem

theorem gsUnbalancingTriple_pumpup
    {x : G} (hU : CFSG.ComponentClassification.UnbalancedLayer.GSUnbalancingTriple z x J)
    (hlt : PumpUpLT 2 z J u H) (hux : u * x = x * u) :
    CFSG.ComponentClassification.UnbalancedLayer.GSUnbalancingTriple u x H := by
  have hzu : z * u = u * z := (mem_centralizer_singleton_iff.mp hlt.2.2.1).symm
  have huJ : u ∈ normalizer (J : Set G) := hlt.2.2.2.1.1
  have hJb : ∀ j ∈ J, j⁻¹ * u⁻¹ * j * u ∈ (pPrimeCore 2 J).map J.subtype := by
    intro j hj
    have hu_inv : u⁻¹ = u := inv_eq_self_of_orderOf_eq_two hlt.2.1.1
    have h := hlt.2.2.2.1.2.2 j⁻¹ (J.inv_mem hj)
    simpa [pPrimeCoreOf, commutatorElement_def, inv_inv, hu_inv] using h
  exact CFSG.ComponentClassification.UnbalancedLayer.unbalancing_orbit_containment_transfer
    hU hlt.2.1.1 hzu hux huJ hJb hlt.2.1.2.2.1 hlt.2.1.2.2.2
    (gsFixedLayer_le_sup_conjugate_of_pumpup hlt)

theorem unbal_pumpup {y : G} (hu : IsUnbalancingTriple z y J)
    (hlt : PumpUpLT 2 z J u H) (huy : u * y = y * u) : IsUnbalancingTriple u y H := by
  have hGS := CFSG.GH74.GLS.IsUnbalancingTriple.gsUnbalancingTriple hu
  exact CFSG.GH74.GLS.isUnbalancingTriple_of_gsUnbalancingTriple
    (gsUnbalancingTriple_pumpup hGS hlt huy)

theorem eq_of_perfect_subnormal {K : Type*} [Group K] {A D : Subgroup K} (hAD : A ≤ D)
    (hDq : CFSG.IsQuasisimple ↥D) (hA : ⁅A, A⁆ = A) (hne : A ≠ ⊥)
    (hsub : (A.subgroupOf D).IsSubnormal) : A = D := by
  rcases LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hDq hsub with htop | hcent
  · refine le_antisymm hAD fun d hd => ?_
    have : (⟨d, hd⟩ : ↥D) ∈ A.subgroupOf D := by rw [htop]; trivial
    exact Subgroup.mem_subgroupOf.mp this
  · exfalso
    apply hne
    have hc : ⁅A, A⁆ = ⊥ := by
      refine le_bot_iff.mp (Subgroup.commutator_le.mpr fun a ha b hb => ?_)
      have h1 := hcent (Subgroup.mem_subgroupOf.mpr ha : (⟨a, hAD ha⟩ : ↥D) ∈ A.subgroupOf D)
      have h2 := Subgroup.mem_center_iff.mp h1 ⟨b, hAD hb⟩
      have h3 : b * a = a * b := congrArg Subtype.val h2
      rw [Subgroup.mem_bot, commutatorElement_def]
      calc a * b * a⁻¹ * b⁻¹ = (a * b) * (b * a)⁻¹ := by group
        _ = 1 := by rw [h3]; group
    rw [← hA, hc]

theorem equiv_quotient_center_of_surjective {Q S : Type} [Group Q] [Group S]
    (hQ : CFSG.IsQuasisimple Q) (hS : IsSimpleGroup S) (φ : Q →* S)
    (hφ : Function.Surjective φ) : Nonempty (S ≃* Q ⧸ center Q) := by
  have := hS.toNontrivial
  have hker : φ.ker ≤ center Q := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hQ (N := φ.ker) inferInstance with h | h
    · exfalso
      obtain ⟨s, hs⟩ := exists_ne (1 : S)
      obtain ⟨q, rfl⟩ := hφ s
      apply hs
      have : q ∈ φ.ker := by rw [h]; trivial
      exact this
    · exact h
  let ψ₀ : Q ⧸ φ.ker →* Q ⧸ center Q :=
    QuotientGroup.map φ.ker (center Q) (MonoidHom.id Q) (fun x hx => hker hx)
  let e : Q ⧸ φ.ker ≃* S := QuotientGroup.quotientKerEquivOfSurjective φ hφ
  let ψ : S →* Q ⧸ center Q := ψ₀.comp e.symm.toMonoidHom
  have hψq : ∀ q : Q, ψ (φ q) = (q : Q ⧸ center Q) := by
    intro q
    have h1 : e.symm (φ q) = (q : Q ⧸ φ.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    simp only [ψ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h1]
    rfl
  have hψs : Function.Surjective ψ := by
    intro x
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨φ q, hψq q⟩
  have hψi : Function.Injective ψ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ψ.ker with h | h
    · exact (MonoidHom.ker_eq_bot_iff ψ).mp h
    · exfalso
      have := hQ.2.1.toNontrivial
      obtain ⟨x, hx⟩ := exists_ne (1 : Q ⧸ center Q)
      obtain ⟨s, rfl⟩ := hψs x
      apply hx
      have : s ∈ ψ.ker := by rw [h]; trivial
      exact this
  exact ⟨MulEquiv.ofBijective ψ ⟨hψi, hψs⟩⟩

theorem kBar_equiv_quotient_of_diag (hlt : PumpUpLT 2 z J u H) (hΛ : IsLam z u J Λ)
    (hzY : z ∈ centralizer ({u} : Set G)) (hdiag : z ∉ normalizer (H : Set G))
    (hJs : IsSimpleGroup (kBar J)) :
    Nonempty (kBar J ≃* ↥(bar u H) ⧸ center ↥(bar u H)) := by
  have hz : orderOf z = 2 := hlt.1.1
  have hH : IsPCompIn 2 (centralizer ({u} : Set G)) H := hlt.2.1.2.2
  set Y' := centralizer ({u} : Set G) with hY'
  have hΛJ : Λ ≤ J := hΛ.le.trans inf_le_left
  have hΛY : Λ ≤ Y' := hΛ.le.trans inf_le_right
  have hso : orderOf (⟨z, hzY⟩ : ↥Y') = 2 := orderOf_mk_centralizer hzY hz
  have hΛC := le_centralizer_mk (isPCompIn_two_iff.mp hΛ.pcW).1 hzY
  have hΛ2 := isTwoComponent_centralizer_mk hΛ.pcW hzY
  obtain ⟨hΛE, hJsub, L', hL', hcases, hLJ, hLsJ, hiff⟩ := pumpupY_structure hso hΛC hΛ2
  obtain ⟨hK'2, hK'J⟩ := isTwoComponent_of_isPCompIn_pumpUp hΛ.layer hΛE hlt.2.2.2.2
  have himg := (hiff _ hK'2).mp hK'J
  have hs2 : orderOf (sbar z hzY) = 2 := orderOf_sbar hz hzY
  have hsinv : (barMk ↥Y' ⟨z, hzY⟩)⁻¹ = barMk ↥Y' ⟨z, hzY⟩ := inv_eq_self_of_orderOf_eq_two hs2
  obtain ⟨hne, hAB, hΛΔ⟩ : conjSub (barMk ↥Y' ⟨z, hzY⟩)⁻¹ L' ≠ L' ∧
      ∃ hAB : ⁅L', conjSub (barMk ↥Y' ⟨z, hzY⟩)⁻¹ L'⁆ = ⊥,
        (Λ.subgroupOf Y').map (barMk ↥Y') ≤ (swapDiag hAB).range := by
    rcases hcases with ⟨hst, -⟩ | h2
    · exfalso
      apply hdiag
      have hHL : bar u H = L' := by
        rcases himg with h | h
        · exact h
        · exact h.trans hst
      refine mem_normalizer_of_map_normalizes hH.1 hK'2 hzY ?_
      have h1 : ((H.subgroupOf Y').map (barMk ↥Y')) = L' := hHL
      rw [h1]
      rw [hsinv] at hst
      exact hst
    · exact h2
  obtain ⟨-, hΔC, -, -, -, hΔq, -, -, -, -, -, ⟨eΔ⟩⟩ :=
    swapped_quasisimple_fixed_central_product (t := barMk ↥Y' ⟨z, hzY⟩) hs2
      (assembly_isQuasisimple_of_isComponent hL') hAB
  have hΔcent : (swapDiag hAB).range ≤ centralizer ({sbar z hzY} : Set _) :=
    hΔC.trans inf_le_right
  have hmap2 := isTwoComponent_map_barMk hso hΛC hΛ2
  have hsubC : ((bar u Λ).subgroupOf (centralizer ({sbar z hzY} : Set _))).IsSubnormal :=
    Components.mathlib_subnormal_of_chain hmap2.1 Subgroup.IsSubnormal.top
  have hsubΔ := isSubnormal_inf_subgroupOf hsubC hΔcent
  have hΔq' : CFSG.IsQuasisimple ↥(swapDiag hAB).range :=
    (AssemblyBPredicates.isQuasisimple_iff_native _).1 hΔq
  have hEq : bar u Λ = (swapDiag hAB).range :=
    eq_of_perfect_subnormal hΛΔ hΔq' (bar_lam_perfect hΛ) (bar_lam_ne_bot hΛ) hsubΔ
  obtain ⟨φ, hφs, hφo, hφρ⟩ := exists_phi hΛJ hΛY hΛ.cover
  have hqΛ : CFSG.IsQuasisimple ↥(bar u Λ) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (MulEquiv.subgroupCongr hEq.symm) hΔq'
  obtain ⟨eJ⟩ := equiv_quotient_center_of_surjective hqΛ hJs φ hφs
  have e4 : Nonempty (↥L' ⧸ center ↥L' ≃* ↥(bar u H) ⧸ center ↥(bar u H)) := by
    rcases himg with h | h
    · exact ⟨GH74.E2.centerQuotientEquiv (MulEquiv.subgroupCongr (show L' = bar u H from h.symm))⟩
    · have h' : bar u H = conjSub (barMk ↥Y' ⟨z, hzY⟩)⁻¹ L' := h
      exact ⟨GH74.E2.centerQuotientEquiv
        (((MulAut.conj (barMk ↥Y' ⟨z, hzY⟩)⁻¹).subgroupMap L').trans
          (MulEquiv.subgroupCongr h'.symm))⟩
  obtain ⟨e4⟩ := e4
  exact ⟨eJ.trans ((GH74.E2.centerQuotientEquiv (MulEquiv.subgroupCongr hEq)).trans
    (eΔ.trans e4))⟩

structure C2Facts : Prop where
  fm9 : ∀ (L : Type) [Group L] [Finite L], TwoThin.Gen4Comp L → InC2 L → InU2 L →
    ¬ IsL34Quotient L → HasL2Model L IsFM9
  centre : ∀ (L : Type) [Group L] [Finite L], TwoThin.Gen4Comp L → InC2 L → center L ≠ ⊥ →
    ∀ (S : Type) [Group S] [Finite S], InU2 S → ¬ IsL34Quotient S → ¬ Nonempty (S ≃* L ⧸ center L)

theorem stable_pumpup (hr4 : pRank 2 G = 4) (hgen4 : CFSG.GH74.Gen4 G) (T7 : St1Thm7 G)
    (hC2 : C2Facts) (hJU2 : InU2 (kBar J)) (hJno : ¬ IsL34Quotient (kBar J))
    (hJs : IsSimpleGroup (kBar J)) (hlt : PumpUpLT 2 z J u H) (hΛ : IsLam z u J Λ) :
    z ∈ normalizer (H : Set G) := by
  by_contra hdiag
  have hu2 : orderOf u = 2 := hlt.2.1.1
  have hH : IsPCompIn 2 (centralizer ({u} : Set G)) H := hlt.2.1.2.2
  have hzY : z ∈ centralizer ({u} : Set G) := mem_centralizer_symm hlt.2.2.1
  have hLc : CFSG.IsComponent (bar u H) := isComponent_bar hH
  have hC : InC2 ↥(bar u H) := T7 u hu2 (bar u H) hLc
  have hP : TwoThin.Gen4Comp ↥(bar u H) :=
    TwoThin.gen4Comp_of_gen4Cen (TwoThin.gen4Cen_barQ hgen4 hu2) _
  obtain ⟨e⟩ := kBar_equiv_bar hH
  by_cases hcen : center ↥(bar u H) = ⊥
  · have hq : CFSG.IsQuasisimple (kBar H) := isQuasisimple_hat hH
    have hcenH : center (kBar H) = ⊥ := by
      have h1 := Subgroup.map_center_eq e
      rw [hcen] at h1
      exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h1
    exact hdiag (PumpGen.mem_normalizer_of_centerless hr4 ⟨hu2, hH⟩ hq hcenH hzY)
  · obtain ⟨eq⟩ := kBar_equiv_quotient_of_diag hlt hΛ hzY hdiag hJs
    exact hC2.centre _ hP hC hcen (kBar J) hJU2 hJno ⟨eq⟩

end Basic

section Close

variable {G : Type} [Group G] [Finite G]

theorem isSimple_of_hasL2Model {L : Type} [Group L] (h : HasL2Model L IsFM9) :
    IsSimpleGroup L := by
  obtain ⟨p, f, hp, hf, hq, hlie⟩ := h
  have hmodel : HasL2Model L (fun r => r = p ^ f) := ⟨p, f, hp, hf, rfl, hlie⟩
  obtain ⟨F₀, _, _, e0, hF₀, -⟩ := IVK.Proofs2.exists_l2Field_of_hasL2Model hq hmodel
  exact IVK.Proofs2.isSimpleGroup_of_l2 hF₀ e0

theorem center_eq_bot_of_isSimple {Q : Type} [Group Q] (hs : IsSimpleGroup Q)
    (hq : CFSG.IsQuasisimple Q) : center Q = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center Q) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := exists_noncomm_of_isQuasisimple' hq
    apply hab
    have ha : a ∈ center Q := by rw [h]; trivial
    exact (Subgroup.mem_center_iff.mp ha b).symm

theorem hasL2Model_bar (hgen4 : CFSG.GH74.Gen4 G) (T7 : St1Thm7 G) (hC2 : C2Facts) {u : G}
    (hu2 : orderOf u = 2) {H : Subgroup G} (hH : IsPCompIn 2 (centralizer ({u} : Set G)) H)
    (hU2 : InU2 (kBar H)) (hno : ¬ IsL34Quotient (kBar H)) :
    HasL2Model ↥(bar u H) IsFM9 := by
  obtain ⟨e⟩ := kBar_equiv_bar hH
  have hC : InC2 ↥(bar u H) := T7 u hu2 (bar u H) (isComponent_bar hH)
  have hP : TwoThin.Gen4Comp ↥(bar u H) :=
    TwoThin.gen4Comp_of_gen4Cen (TwoThin.gen4Cen_barQ hgen4 hu2) _
  exact hC2.fm9 _ hP hC (inU2_of_mulEquiv e hU2)
    (fun h => hno (TwoThin.isL34Quotient_of_mulEquiv e.symm h))

theorem hasL2Model_kBar (hgen4 : CFSG.GH74.Gen4 G) (T7 : St1Thm7 G) (hC2 : C2Facts) {u : G}
    (hu2 : orderOf u = 2) {H : Subgroup G} (hH : IsPCompIn 2 (centralizer ({u} : Set G)) H)
    (hU2 : InU2 (kBar H)) (hno : ¬ IsL34Quotient (kBar H)) : HasL2Model (kBar H) IsFM9 := by
  obtain ⟨e⟩ := kBar_equiv_bar hH
  exact TwoThin.hasL2Model_of_mulEquiv e.symm (hasL2Model_bar hgen4 T7 hC2 hu2 hH hU2 hno)

theorem isTerminallyUnbalancing_of_maximal_twoPartCard {y z : G} {J : Subgroup G}
    (hu : IsUnbalancingTriple z y J)
    (hstep : ∀ (u : G) (H : Subgroup G), PumpUpLT 2 z J u H → u * y = y * u →
      (z ∈ normalizer (H : Set G) ∧ Nonempty (kBar H ≃* kBar J)) ∧
        (∀ q ∈ CxK z J, u * q = q * u → q ∈ CxK u H) ∧ IsUnbalancingTriple u y H)
    (hmax : ∀ (u : G) (H : Subgroup G), PumpUpLT 2 z J u H → u * y = y * u →
      IsUnbalancingTriple u y H → pRank 2 ↥(CxK z J) ≤ pRank 2 ↥(CxK u H) →
        twoPartCard (CxK u H) ≤ twoPartCard (CxK z J)) :
    IsTerminallyUnbalancing z y J := by
  refine ⟨hu, ?_, ?_⟩
  ·
    intro u _ huC huy H hlt
    exact (hstep u H hlt huy).1
  ·
    intro Q hQ u huQ hu2 hucQ huy H hlt
    obtain ⟨-, hR3, hunb⟩ := hstep u H hlt huy
    have hQle : Q ≤ CxK u H := fun q hq => hR3 q (hQ.le hq) (hucQ q hq)
    have hQrk : pRank 2 ↥Q = pRank 2 ↥(CxK z J) := pRank_eq_of_isSylowOf hQ
    have hrkH : pRank 2 ↥(CxK z J) ≤ pRank 2 ↥(CxK u H) := by
      rw [← hQrk]
      exact Bg.pRank_subgroup_mono one_lt_two hQle
    have hle := hmax u H hlt huy hunb hrkH
    have hcardQ : Nat.card ↥Q = 2 ^ (Nat.card ↥(CxK z J)).factorization 2 := hQ.card_eq
    have hle' : 2 ^ (Nat.card ↥(CxK u H)).factorization 2 ≤
        2 ^ (Nat.card ↥(CxK z J)).factorization 2 := hle
    have hdvd : Nat.card ↥Q ∣ Nat.card ↥(CxK u H) := Subgroup.card_dvd_of_le hQle
    rw [hcardQ] at hdvd
    have hC'ne : Nat.card ↥(CxK u H) ≠ 0 := Nat.card_pos.ne'
    have hge : (Nat.card ↥(CxK z J)).factorization 2 ≤ (Nat.card ↥(CxK u H)).factorization 2 :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hC'ne).mp hdvd
    have hle2 : (Nat.card ↥(CxK u H)).factorization 2 ≤ (Nat.card ↥(CxK z J)).factorization 2 :=
      (Nat.pow_le_pow_iff_right (by norm_num)).mp hle'
    refine CFSG.ABGLocalTools.isSylowOf_of_card hQle ?_
    rw [hcardQ]
    exact congrArg (2 ^ ·) (le_antisymm hge hle2)

theorem no_unbalancing_triple_of_rank_two (hr4 : pRank 2 G = 4) (hgen4 : CFSG.GH74.Gen4 G)
    (T7 : St1Thm7 G) (hC2 : C2Facts)
    (hU2 : ∀ (z y : G) (J : Subgroup G), IsUnbalancingTriple z y J →
      InU2 (kBar J) ∧ ¬ IsL34Quotient (kBar J))
    (hL29 : ∀ (z y : G) (J : Subgroup G), IsTerminallyUnbalancing z y J →
      pRank 2 ↥(CxK z J) = 1)
    {x y : G} {K : Subgroup G} (hu : IsUnbalancingTriple x y K)
    (h2 : 2 ≤ pRank 2 ↥(CxK x K)) : False := by
  classical
  have : Finite (Subgroup G) :=
    Finite.of_injective (fun K : Subgroup G => (K : Set G)) SetLike.coe_injective
  let F : Set (G × Subgroup G) :=
    {p | IsUnbalancingTriple p.1 y p.2 ∧ 2 ≤ pRank 2 ↥(CxK p.1 p.2)}
  have hne : F.Nonempty := ⟨(x, K), hu, h2⟩
  obtain ⟨⟨z, J⟩, ⟨hzJ, hrk⟩, hmax⟩ :=
    Set.exists_max_image F (fun p => twoPartCard (CxK p.1 p.2)) (Set.toFinite _) hne
  have hJc : IsPCompIn 2 (centralizer ({z} : Set G)) J := hzJ.1.2
  have hz2 : orderOf z = 2 := hzJ.1.1
  obtain ⟨hJU2, hJno⟩ := hU2 z y J hzJ
  have hL2J : HasL2Model (kBar J) IsFM9 := hasL2Model_kBar hgen4 T7 hC2 hz2 hJc hJU2 hJno
  have hJs : IsSimpleGroup (kBar J) := isSimple_of_hasL2Model hL2J
  have htriv : ∀ u : G, orderOf u = 2 → u ∈ CxK z J → u * y = y * u → ∀ H : Subgroup G,
      PumpUpLT 2 z J u H →
        (z ∈ normalizer (H : Set G) ∧ Nonempty (kBar H ≃* kBar J)) ∧
        (∀ q ∈ CxK z J, u * q = q * u → q ∈ CxK u H) ∧ IsUnbalancingTriple u y H := by
    intro u hu2 huC huy H hlt
    obtain ⟨Λ, hΛ⟩ := exists_isLam hu2 hJc huC.2
    have hzH := stable_pumpup hr4 hgen4 T7 hC2 hJU2 hJno hJs hlt hΛ
    have hunb := unbal_pumpup hzJ hlt huy
    obtain ⟨hHU2, hHno⟩ := hU2 u y H hunb
    have hL2H : HasL2Model ↥(bar u H) IsFM9 :=
      hasL2Model_bar hgen4 T7 hC2 hu2 hlt.2.1.2.2 hHU2 hHno
    have hzY : z ∈ centralizer ({u} : Set G) := mem_centralizer_symm hlt.2.2.1
    have hcen := sbar_central hlt hΛ hzY hzH hL2H
    obtain ⟨hR2, hR3, -⟩ := stable_trivial hlt hΛ hzY hzH hcen (isSimple_of_hasL2Model hL2H)
    exact ⟨⟨hzH, hR2⟩, hR3, hunb⟩
  have hstep : ∀ (u : G) (H : Subgroup G), PumpUpLT 2 z J u H → u * y = y * u →
      (z ∈ normalizer (H : Set G) ∧ Nonempty (kBar H ≃* kBar J)) ∧
      (∀ q ∈ CxK z J, u * q = q * u → q ∈ CxK u H) ∧ IsUnbalancingTriple u y H := by
    intro u H hlt huy
    exact htriv u hlt.2.1.1 ⟨hlt.2.2.1, hlt.2.2.2.1⟩ huy H hlt
  have hmaxterm : ∀ (u : G) (H : Subgroup G), PumpUpLT 2 z J u H → u * y = y * u →
      IsUnbalancingTriple u y H → pRank 2 ↥(CxK z J) ≤ pRank 2 ↥(CxK u H) →
        twoPartCard (CxK u H) ≤ twoPartCard (CxK z J) := by
    intro u H hlt huy hunb' hrank
    exact hmax (u, H) ⟨hunb', hrk.trans hrank⟩
  have hterm : IsTerminallyUnbalancing z y J :=
    isTerminallyUnbalancing_of_maximal_twoPartCard hzJ hstep hmaxterm
  have h1 := hL29 z y J hterm
  have hrk' : 2 ≤ pRank 2 ↥(CxK z J) := hrk
  omega

end Close

end CFSG.GH74.GLS.C3.Layer1.PumpCalc
