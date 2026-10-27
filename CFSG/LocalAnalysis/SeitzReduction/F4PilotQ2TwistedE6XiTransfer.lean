module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2E6UniqueMain
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotXiCaseL
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueStep3Xi

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
open CFSG.LieType.Ree (ReeTag)
open CFSG.SeitzReduction.EPilot (normalizerQuotMulAut)
open CFSG.Quasithin (perfectCore)

section General

theorem perfectCore_centralizer_subgroupOf_eq {G : Type*} [Group G] [Finite G] {H X : Subgroup G}
    (hXH : X ≤ H) (hEH : centralizerPerfectCore X ≤ H) :
    perfectCore (centralizer ((X.subgroupOf H : Subgroup H) : Set H)) =
      (centralizerPerfectCore X).subgroupOf H := by
  apply Subgroup.map_injective H.subtype_injective
  rw [← perfectCore_inf_centralizer_eq_map hXH, subgroupOf_map_subtype, inf_of_le_left hEH]
  refine le_antisymm ?_ ?_
  · exact le_centralizerPerfectCore (CFSG.Quasithin.perfectCore_perfect _)
      ((CFSG.Quasithin.perfectCore_le _).trans inf_le_right)
  · exact CFSG.Quasithin.le_perfectCore_of_perfect
      (le_inf hEH (centralizerPerfectCore_le_centralizer X)) (commutator_centralizerPerfectCore X)

theorem map_quotAut_perfectCore_centralizer {M : Type*} [Group M] [Finite M]
    (ψ : MulAut (M ⧸ center M)) {A B : Subgroup M}
    (h : (A.map (QuotientGroup.mk' (center M))).map ψ.toMonoidHom =
      B.map (QuotientGroup.mk' (center M))) :
    ((perfectCore (centralizer (A : Set M))).map (QuotientGroup.mk' (center M))).map
        ψ.toMonoidHom =
      (perfectCore (centralizer (B : Set M))).map (QuotientGroup.mk' (center M)) := by
  rw [map_perfectCore_centralizer_mk, map_perfectCore_centralizer_mk,
    CFSG.Quasithin.map_perfectCore, map_centralizer_mulEquiv, h]

theorem card_dvd_card_center_mul_card_map {H Q : Type*} [Group H] [Group Q] [Finite H]
    (f : H →* Q) (hf : f.ker ≤ center H) (S : Subgroup H) :
    Nat.card S ∣ Nat.card (center S) * Nat.card (S.map f) := by
  have h1 : Nat.card (f.domRestrict S).ker * Nat.card (f.domRestrict S).range = Nat.card S := by
    rw [← Subgroup.index_ker]
    exact Subgroup.card_mul_index _
  rw [MonoidHom.domRestrict_range] at h1
  have h2 : (f.domRestrict S).ker ≤ center S := by
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.domRestrict_apply] at hx
    have hx' : (x : H) ∈ center H := hf hx
    rw [mem_center_iff]
    intro y
    exact Subtype.ext ((mem_center_iff.1 hx') y)
  rw [← h1]
  exact mul_dvd_mul_right (Subgroup.card_dvd_of_le h2) _

end General

section Transfer


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K ReeTag.F4.prime]

theorem mem_normalizer_or_dvd_of_quotAut_map_eq_two (hK : Nat.card K = 2)
    (e : L ≃* adjointGroup .F4 K) (X₀ : Subgroup (adjointGroup .F4 K)) {G₀ : Subgroup G}
    (hG₀ : G₀ = centralizerPerfectCore (subgroupToG e X₀) ⊔ L) {g : G}
    (hgL : L.map (MulAut.conj g⁻¹).toMonoidHom ≤ G₀) (ψ : MulAut (G₀ ⧸ center G₀))
    (hψ : ((L.subgroupOf G₀).map (QuotientGroup.mk' (center G₀))).map ψ.toMonoidHom =
      ((L.map (MulAut.conj g⁻¹).toMonoidHom).subgroupOf G₀).map
        (QuotientGroup.mk' (center G₀))) :
    g ∈ normalizer (G₀ : Set G) ∨
      Nat.card (centralizerPerfectCore (subgroupToG e X₀)) ∣
        Nat.card (center (centralizerPerfectCore (subgroupToG e X₀))) *
          Nat.card (centralizerPerfectCore (subgroupToG (e.trans (graphAutF4 K).symm) X₀)) := by
  have : Finite (ModGL .F4 K) := finite_modGL
  set E := centralizerPerfectCore (subgroupToG e X₀) with hEdef
  have hLG₀ : L ≤ G₀ := hG₀ ▸ le_sup_right
  have hEG₀ : E ≤ G₀ := hG₀ ▸ le_sup_left
  have hG₀p : Group.IsPerfect G₀ := by
    rw [hG₀]
    exact Subgroup.isPerfect_iff.2 (commutator_twoE6Span e X₀)
  set π := QuotientGroup.mk' (center G₀) with hπ
  set Ls := L.map (MulAut.conj g⁻¹).toMonoidHom with hLs
  set ι₀ : adjointGroup .F4 K →* G₀ := (Subgroup.inclusion hLG₀).comp e.symm.toMonoidHom
    with hι₀
  set cg : L ≃* Ls := L.equivMapOfInjective _ (MulAut.conj g⁻¹).injective with hcg
  set ιs : adjointGroup .F4 K →* G₀ :=
    (Subgroup.inclusion hgL).comp (cg.toMonoidHom.comp e.symm.toMonoidHom) with hιs
  have hι₀_apply : ∀ x, ((ι₀ x : G₀) : G) = ((e.symm x : L) : G) := fun x => rfl
  have hιs_apply : ∀ x, ((ιs x : G₀) : G) = g⁻¹ * ((e.symm x : L) : G) * g := by
    intro x
    change (MulAut.conj g⁻¹) ((e.symm x : L) : G) = _
    simp only [MulAut.conj_apply, inv_inv]
  have hcenL : ∀ x : adjointGroup .F4 K, (e.symm x : L) ∈ center L → x = 1 := by
    intro x hx
    have h1 : e (e.symm x) ∈ center (adjointGroup .F4 K) :=
      (MulEquivClass.apply_mem_center_iff e).2 hx
    rwa [MulEquiv.apply_symm_apply, center_adjointGroup_eq_bot, mem_bot] at h1
  have hπ1 : ∀ z : G₀, π z = 1 → ∀ w : G₀, (w : G) * z = z * w := by
    intro z hz w
    have hzc : z ∈ center G₀ := (QuotientGroup.eq_one_iff z).1 hz
    exact congrArg Subtype.val ((mem_center_iff.1 hzc) w)
  set α' : adjointGroup .F4 K →* G₀ ⧸ center G₀ := ψ.toMonoidHom.comp (π.comp ι₀) with hα'
  set β' : adjointGroup .F4 K →* G₀ ⧸ center G₀ := π.comp ιs with hβ'
  have hα'inj : Function.Injective α' := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, hα', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff] at hx
    refine (Subgroup.mem_bot).2 (hcenL x (mem_center_iff.2 fun l => Subtype.ext ?_))
    exact hπ1 (ι₀ x) hx (Subgroup.inclusion hLG₀ l)
  have hβ'inj : Function.Injective β' := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    refine (Subgroup.mem_bot).2 (hcenL x (mem_center_iff.2 fun l => Subtype.ext ?_))
    have h1 := hπ1 (ιs x) hx (Subgroup.inclusion hgL (cg l))
    rw [Subgroup.coe_inclusion, hιs_apply] at h1
    change (MulAut.conj g⁻¹) (l : G) * _ = _ * (MulAut.conj g⁻¹) (l : G) at h1
    simp only [MulAut.conj_apply, inv_inv] at h1
    change (l : G) * ((e.symm x : L) : G) = ((e.symm x : L) : G) * l
    calc (l : G) * ((e.symm x : L) : G) =
          g * ((g⁻¹ * l * g) * (g⁻¹ * ((e.symm x : L) : G) * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * ((e.symm x : L) : G) * g) * (g⁻¹ * l * g)) * g⁻¹ := by rw [h1]
      _ = ((e.symm x : L) : G) * l := by group
  have hι₀range : ι₀.range = L.subgroupOf G₀ := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact mem_subgroupOf.2 (e.symm y).2
    · intro hx
      exact ⟨e ⟨x, mem_subgroupOf.1 hx⟩, Subtype.ext (by rw [hι₀_apply, e.symm_apply_apply])⟩
  have hιsrange : ιs.range = Ls.subgroupOf G₀ := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact mem_subgroupOf.2 (cg (e.symm y)).2
    · intro hx
      obtain ⟨l, hl, hlx⟩ := mem_subgroupOf.1 hx
      refine ⟨e ⟨l, hl⟩, Subtype.ext ?_⟩
      rw [hιs_apply, e.symm_apply_apply, ← hlx]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have hrange : α'.range = β'.range := by
    have h1 : α'.range = ((π.comp ι₀).range).map ψ.toMonoidHom := MonoidHom.range_comp _ _
    have h2 : (π.comp ι₀).range = ι₀.range.map π := MonoidHom.range_comp _ _
    have h3 : β'.range = ιs.range.map π := MonoidHom.range_comp _ _
    rw [h1, h2, h3, hι₀range, hιsrange]
    exact hψ
  set Θ : MulAut (adjointGroup .F4 K) := (MonoidHom.ofInjective hα'inj).trans
    ((MulEquiv.subgroupCongr hrange).trans (MonoidHom.ofInjective hβ'inj).symm) with hΘdef
  have hΘ : ∀ x, β' (Θ x) = α' x := by
    intro x
    rw [hΘdef, MulEquiv.trans_apply, MulEquiv.trans_apply, MonoidHom.apply_ofInjective_symm]
    rfl
  have hK' : Nat.card K = 2 ^ 1 := by rw [hK, pow_one]
  obtain ⟨-, hnf, -⟩ := even_F4_exact_automorphism_normal_form le_rfl K hK'
  obtain ⟨⟨c₀, m⟩, hcm, -⟩ := hnf Θ
  set c : adjointGroup .F4 K := c₀ with hc
  have hΘx : ∀ z, Θ z = c * (graphAutF4 K ^ (m : ℕ)) z * c⁻¹ := by
    intro z
    rw [hcm]
    rfl
  have hm2 : (m : ℕ) < 2 := m.2
  generalize (m : ℕ) = n at hΘx hm2
  set a : G := ((e.symm c : L) : G) with ha
  set y : G := g⁻¹ * a with hy
  have hιsΘ : ∀ z, ((ιs (Θ z) : G₀) : G) =
      y * ((e.symm ((graphAutF4 K ^ n) z) : L) : G) * y⁻¹ := by
    intro z
    rw [hιs_apply, hΘx, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, hy, ha]
    group
  set A : Subgroup G₀ := X₀.map ι₀ with hA
  set B : Subgroup G₀ := (X₀.map Θ.toMonoidHom).map ιs with hB
  have hAB : (A.map π).map ψ.toMonoidHom = B.map π := by
    simp only [hA, hB, Subgroup.map_map]
    congr 1
    ext x
    exact (hΘ x).symm
  have hcore := map_quotAut_perfectCore_centralizer ψ hAB
  have hXmap : subgroupToG e X₀ = A.map G₀.subtype := by
    rw [subgroupToG, Subgroup.map_map, hA, Subgroup.map_map]
    rfl
  have hAX : (subgroupToG e X₀).subgroupOf G₀ = A := by
    rw [hXmap]
    exact Subgroup.comap_map_eq_self_of_injective G₀.subtype_injective A
  have hXG₀ : subgroupToG e X₀ ≤ G₀ := by
    rw [hXmap]
    exact map_subtype_le A
  have hEcore : perfectCore (centralizer (A : Set G₀)) = E.subgroupOf G₀ := by
    rw [← hAX]
    exact perfectCore_centralizer_subgroupOf_eq hXG₀ hEG₀
  rw [hEcore] at hcore
  set P : Subgroup G₀ := perfectCore (centralizer (B : Set G₀)) with hPdef
  have hPle : P.map G₀.subtype ≤
      (centralizerPerfectCore (subgroupToG e (X₀.map (graphAutF4 K ^ n).toMonoidHom))).map
        (MulAut.conj y).toMonoidHom := by
    rw [map_centralizerPerfectCore]
    refine le_centralizerPerfectCore ?_ ?_
    · rw [← map_commutator, CFSG.Quasithin.perfectCore_perfect]
    · rintro _ ⟨p, hp, rfl⟩
      rw [mem_centralizer_iff]
      rintro _ ⟨_, ⟨_, ⟨_, ⟨z, hz, rfl⟩, rfl⟩, rfl⟩, rfl⟩
      have hzB : ιs (Θ z) ∈ B := ⟨Θ z, ⟨z, hz, rfl⟩, rfl⟩
      have h1 := mem_centralizer_iff.1 (CFSG.Quasithin.perfectCore_le _ hp) _ hzB
      have h2 := congrArg Subtype.val h1
      simp only [Subgroup.coe_mul] at h2
      rw [hιsΘ] at h2
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_subtype]
      exact h2
  interval_cases n
  ·
    left
    have hX0 : X₀.map (graphAutF4 K ^ 0).toMonoidHom = X₀ := by
      rw [pow_zero]
      exact Subgroup.map_id X₀
    rw [hX0] at hPle
    have htop₀ : E.subgroupOf G₀ ⊔ L.subgroupOf G₀ = ⊤ := by
      apply Subgroup.map_injective G₀.subtype_injective
      rw [Subgroup.map_sup, subgroupOf_map_subtype, subgroupOf_map_subtype, inf_of_le_left hEG₀,
        inf_of_le_left hLG₀, ← MonoidHom.range_eq_map, range_subtype]
      exact hG₀.symm
    have hH : (P ⊔ Ls.subgroupOf G₀).map π = ⊤ := by
      have h1 : (⊤ : Subgroup (G₀ ⧸ center G₀)) = ((⊤ : Subgroup G₀).map π).map ψ.toMonoidHom := by
        rw [Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective _),
          Subgroup.map_top_of_surjective _ ψ.surjective]
      rw [eq_top_iff, h1, ← htop₀, Subgroup.map_sup, Subgroup.map_sup, hcore, hψ,
        ← Subgroup.map_sup]
    have hHtop : P ⊔ Ls.subgroupOf G₀ = ⊤ := by
      have hsup : (P ⊔ Ls.subgroupOf G₀) ⊔ center G₀ = ⊤ := by
        have h1 := Subgroup.comap_map_eq π (P ⊔ Ls.subgroupOf G₀)
        rw [hH, Subgroup.comap_top, hπ, QuotientGroup.ker_mk'] at h1
        exact h1.symm
      exact eq_top_of_sup_center_eq_top_of_perfect' hsup
    have hLsle : Ls ≤ G₀.map (MulAut.conj y).toMonoidHom := by
      rintro _ ⟨l, hl, rfl⟩
      have haL : a ∈ L := (e.symm c).2
      refine ⟨a⁻¹ * l * a, hLG₀ (mul_mem (mul_mem (inv_mem haL) hl) haL), ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hy]
      group
    have hEle : E.map (MulAut.conj y).toMonoidHom ≤ G₀.map (MulAut.conj y).toMonoidHom :=
      Subgroup.map_mono hEG₀
    have hG₀le : G₀ ≤ G₀.map (MulAut.conj y).toMonoidHom := by
      intro x hx
      have hxH : (⟨x, hx⟩ : G₀) ∈ P ⊔ Ls.subgroupOf G₀ := hHtop ▸ mem_top _
      have hxmap : x ∈ (P ⊔ Ls.subgroupOf G₀).map G₀.subtype := ⟨⟨x, hx⟩, hxH, rfl⟩
      rw [Subgroup.map_sup, subgroupOf_map_subtype] at hxmap
      exact (sup_le (hPle.trans hEle) (inf_le_left.trans hLsle)) hxmap
    have heq : G₀.map (MulAut.conj y).toMonoidHom = G₀ :=
      (Subgroup.eq_of_le_of_card_ge hG₀le
        (le_of_eq (Subgroup.card_map_of_injective (MulAut.conj y).injective))).symm
    have hyN : y ∈ normalizer (G₀ : Set G) := mem_normalizer_iff_map_conj_toMonoidHom.2 heq
    have haN : a ∈ normalizer (G₀ : Set G) := le_normalizer (hLG₀ (e.symm c).2)
    have hg : g = a * y⁻¹ := by
      rw [hy]
      group
    rw [hg]
    exact mul_mem haN (inv_mem hyN)
  ·
    right
    have hX1 : subgroupToG e (X₀.map (graphAutF4 K ^ 1).toMonoidHom) =
        subgroupToG (e.trans (graphAutF4 K).symm) X₀ := by
      simp only [subgroupToG, Subgroup.map_map]
      congr 1
    rw [hX1] at hPle
    have h1 : Nat.card ((E.subgroupOf G₀).map π) = Nat.card (P.map π) := by
      rw [← hcore]
      exact (Subgroup.card_map_of_injective ψ.injective).symm
    have h2 : Nat.card (P.map π) ∣ Nat.card P := natCard_map_dvd π P
    have h3 : Nat.card P ∣
        Nat.card (centralizerPerfectCore (subgroupToG (e.trans (graphAutF4 K).symm) X₀)) := by
      have := Subgroup.card_dvd_of_le hPle
      rwa [Subgroup.card_map_of_injective G₀.subtype_injective,
        Subgroup.card_map_of_injective (MulAut.conj y).injective] at this
    have h4 := card_dvd_card_center_mul_card_map π (QuotientGroup.ker_mk' _).le (E.subgroupOf G₀)
    have h5 : Nat.card (E.subgroupOf G₀) = Nat.card E :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEG₀).toEquiv
    have h6 : Nat.card (center (E.subgroupOf G₀)) = Nat.card (center E) :=
      Nat.card_congr (Subgroup.centerCongr (Subgroup.subgroupOfEquivOfLe hEG₀)).toEquiv
    rw [h5, h6, h1] at h4
    exact h4.trans (mul_dvd_mul_left _ (h2.trans h3))

theorem mem_normalizer_or_dvd_of_eta_conjugate_two (hK : Nat.card K = 2)
    (e : L ≃* adjointGroup .F4 K) (X₀ : Subgroup (adjointGroup .F4 K)) {G₀ : Subgroup G}
    (hG₀ : G₀ = centralizerPerfectCore (subgroupToG e X₀) ⊔ L) {t : G} (ht : orderOf t = 2)
    (hZ : Odd (Nat.card (center G₀))) {X : Type*} [Group X] (e₀ : G₀ ⧸ center G₀ ≃* X)
    (η : MulAut X) (htN : t ∈ normalizer (G₀ : Set G))
    (h₀ : G₀ ⊓ centralizer ({t} : Set G) = L ∧
      ∃ φ : MulAut X, φ * normalizerQuotMulAut e₀ ⟨t, htN⟩ * φ⁻¹ = η)
    (g : G) (htM : t ∈ normalizer (CFSG.conjugate G₀ g⁻¹ : Set G))
    (hM : CFSG.conjugate G₀ g⁻¹ ⊓ centralizer ({t} : Set G) = L ∧
      ∃ φ : MulAut X, φ * normalizerQuotMulAut
        ((E6Pilot.coverConjugateQuotientCenterEquiv G₀ g⁻¹).symm.trans e₀) ⟨t, htM⟩ * φ⁻¹ = η) :
    g ∈ normalizer (G₀ : Set G) ∨
      Nat.card (centralizerPerfectCore (subgroupToG e X₀)) ∣
        Nat.card (center (centralizerPerfectCore (subgroupToG e X₀))) *
          Nat.card (centralizerPerfectCore (subgroupToG (e.trans (graphAutF4 K).symm) X₀)) := by
  obtain ⟨hC₀, φ₀, hφ₀⟩ := h₀
  obtain ⟨hCM, φM, hφM⟩ := hM
  set χ := E6Pilot.coverConjugateQuotientCenterEquiv G₀ g⁻¹ with hχ
  set eM := χ.symm.trans e₀ with heM
  have hZM : Odd (Nat.card (center (CFSG.conjugate G₀ g⁻¹))) := by
    rw [E6Pilot.card_center_conjugate]
    exact hZ
  have hfix₀ := fixSubgroup_eq_map_of_inf_eq hZ e₀ ht htN hC₀
  have hfixM := fixSubgroup_eq_map_of_inf_eq hZM eM ht htM hCM
  have hmap₀ := map_eqLocus_eq_of_conj hφ₀
  have hmapM := map_eqLocus_eq_of_conj hφM
  set ψ : MulAut (G₀ ⧸ center G₀) := ((e₀.trans φ₀).trans φM.symm).trans e₀.symm with hψ
  have hLM : L ≤ CFSG.conjugate G₀ g⁻¹ := by
    intro x hx
    have h1 : x ∈ CFSG.conjugate G₀ g⁻¹ ⊓ centralizer ({t} : Set G) := by
      rw [hCM]
      exact hx
    exact h1.1
  have hgL : L.map (MulAut.conj g⁻¹).toMonoidHom ≤ G₀ := by
    rintro _ ⟨l, hl, rfl⟩
    have h1 := hLM hl
    rw [mem_conjugate_iff_of_mul] at h1
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h1
  refine mem_normalizer_or_dvd_of_quotAut_map_eq_two hK e X₀ hG₀ hgL ψ ?_
  rw [← map_coverConjugateQuotientCenterEquiv_symm g]
  apply Subgroup.map_injective (f := e₀.toMonoidHom) e₀.injective
  have hmap₀' : (E6Pilot.fixSubgroup (normalizerQuotMulAut e₀ ⟨t, htN⟩)).map φ₀.toMonoidHom =
      E6Pilot.fixSubgroup η := hmap₀
  have hφM' : (E6Pilot.fixSubgroup η).map φM.symm.toMonoidHom =
      E6Pilot.fixSubgroup (normalizerQuotMulAut eM ⟨t, htM⟩) := by
    change (η.toMonoidHom.eqLocus (MonoidHom.id X)).map φM.symm.toMonoidHom = _
    rw [← hmapM, Subgroup.map_map]
    have : φM.symm.toMonoidHom.comp φM.toMonoidHom = MonoidHom.id X :=
      MonoidHom.ext fun x => φM.symm_apply_apply x
    rw [this, Subgroup.map_id]
    rfl
  have hL1 : (((L.subgroupOf G₀).map (QuotientGroup.mk' (center G₀))).map
        ψ.toMonoidHom).map e₀.toMonoidHom =
      (((L.subgroupOf G₀).map
        (e₀.toMonoidHom.comp (QuotientGroup.mk' (center G₀)))).map
          φ₀.toMonoidHom).map φM.symm.toMonoidHom := by
    simp only [Subgroup.map_map]
    congr 1
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hψ, MulEquiv.trans_apply,
      MulEquiv.apply_symm_apply]
  have hR1 : (((L.subgroupOf (CFSG.conjugate G₀ g⁻¹)).map
        (QuotientGroup.mk' (center (CFSG.conjugate G₀ g⁻¹)))).map
          χ.symm.toMonoidHom).map e₀.toMonoidHom =
      (L.subgroupOf (CFSG.conjugate G₀ g⁻¹)).map
        (eM.toMonoidHom.comp (QuotientGroup.mk' (center (CFSG.conjugate G₀ g⁻¹)))) := by
    simp only [Subgroup.map_map]
    rfl
  rw [hL1, hR1, ← hfixM, ← hfix₀, hmap₀', hφM']

end Transfer

end CFSG.SeitzReduction.F4Pilot
