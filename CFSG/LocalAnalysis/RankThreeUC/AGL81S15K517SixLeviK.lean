module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K517SixLevi
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.ParabLevi
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParK
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K517Six

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime CFSG.AGLEmbeddingD2.ParabLevi
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

section General

theorem pow_mem_of_mem_sup_normalizer {G : Type*} [Group G] {N T' : Subgroup G}
    (hT : T' ≤ Subgroup.normalizer (N : Set G)) {M : ℕ} (hTM : ∀ t ∈ T', t ^ M = 1) {a : G}
    (ha : a ∈ N ⊔ T') : a ^ M ∈ N := by
  have hNT : N ⊔ T' ≤ Subgroup.normalizer (N : Set G) := sup_le Subgroup.le_normalizer hT
  haveI : (N.subgroupOf (N ⊔ T')).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2 hNT
  obtain ⟨x, hx, t, ht, rfl⟩ : ∃ x ∈ N, ∃ t ∈ T', a = x * t := by
    have h := ha
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hT, Set.mem_mul] at h
    obtain ⟨x, hx, t, ht, e⟩ := h
    exact ⟨x, hx, t, ht, e.symm⟩
  set q := QuotientGroup.mk' (N.subgroupOf (N ⊔ T')) with hq
  have htm : t ∈ N ⊔ T' := Subgroup.mem_sup_right ht
  have hxm : x ∈ N ⊔ T' := Subgroup.mem_sup_left hx
  have hqa : q ⟨x * t, ha⟩ = q ⟨t, htm⟩ := by
    have : (⟨x * t, ha⟩ : ↥(N ⊔ T')) = ⟨x, hxm⟩ * ⟨t, htm⟩ := rfl
    rw [this, map_mul]
    have hx1 : q ⟨x, hxm⟩ = 1 := by
      rw [hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact (Subgroup.mem_subgroupOf).2 hx
    rw [hx1, one_mul]
  have h1 : q (⟨x * t, ha⟩ ^ M) = 1 := by
    rw [map_pow, hqa, ← map_pow]
    have : (⟨t, htm⟩ : ↥(N ⊔ T')) ^ M = 1 := Subtype.ext (hTM t ht)
    rw [this, map_one]
  rw [hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact (Subgroup.mem_subgroupOf).1 h1

end General

section K

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K} {M : ℕ}

theorem torus_pow_eq_one (hext : SteinbergExtras D n H) (hM : ∀ i, ∀ g ∈ H i, g ^ M = 1) :
    ∀ t ∈ ⨆ i, H i, t ^ M = 1 := by
  intro t ht
  have hT := isMulCommutative_torus hext
  have key : t ∈ ⨆ i, H i ∧ t ^ M = 1 := by
    refine Subgroup.iSup_induction H (C := fun x => x ∈ ⨆ i, H i ∧ x ^ M = 1) ht
      (fun i x hx => ⟨Subgroup.mem_iSup_of_mem i hx, hM i x hx⟩) ⟨one_mem _, one_pow _⟩ ?_
    rintro x y ⟨hx, hx1⟩ ⟨hy, hy1⟩
    refine ⟨mul_mem hx hy, ?_⟩
    have hc : Commute x y := congrArg Subtype.val (hT.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    rw [hc.mul_pow, hx1, hy1, one_mul]
  exact key.2

variable (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
  (weylAction D.isFiniteType) D.roots D.rootGroup n H) (hext : SteinbergExtras D n H)

include hct hext in
theorem parJ_le_normalizer_leviRad (J : Set (Fin D.rank)) :
    parJ D H J ≤ Subgroup.normalizer (leviRad D J : Set K) :=
  sup_le (borel_le_normalizer_leviRad hct hext) (iSup₂_le fun _ hi =>
    rankOne_le_normalizer_leviRad hext hi)

include hct in
theorem parJ_le_normalizer_unipJ (J : Set (Fin D.rank)) :
    parJ D H J ≤ Subgroup.normalizer (unipJ D J : Set K) := by
  rw [parJ_eq_sup]
  exact sup_le Subgroup.le_normalizer (torus_le_normalizer_unipJ hct J)

include hct in
theorem unipJ_eq_leviRad_sup_leviM (J : Set (Fin D.rank)) :
    unipJ D J = leviRad D J ⊔ leviM D J :=
  le_antisymm (sup_le (posUnipotent_le_leviRad_sup_leviM hct) le_sup_right)
    (sup_le (leviRad_le_posUnipotent.trans le_sup_left) le_sup_right)

include hext in
theorem leviM_le_normalizer_leviRad (J : Set (Fin D.rank)) :
    leviM D J ≤ Subgroup.normalizer (leviRad D J : Set K) :=
  iSup₂_le fun _ hi => rankOne_le_normalizer_leviRad hext hi

include hct hext in
theorem exists_mul_of_mem_unipJ (J : Set (Fin D.rank)) {x : K} (hx : x ∈ unipJ D J) :
    ∃ u ∈ leviRad D J, ∃ y ∈ leviM D J, x = u * y := by
  rw [unipJ_eq_leviRad_sup_leviM hct J, ← SetLike.mem_coe,
    Subgroup.coe_mul_of_right_le_normalizer_left _ _ (leviM_le_normalizer_leviRad hext J),
    Set.mem_mul] at hx
  obtain ⟨u, hu, y, hy, e⟩ := hx
  exact ⟨u, hu, y, hy, e.symm⟩

include hct hext in
theorem pow_mem_unipJ_of_mem_parJ (hM : ∀ i, ∀ g ∈ H i, g ^ M = 1) (J : Set (Fin D.rank))
    {x : K} (hx : x ∈ parJ D H J) : x ^ M ∈ unipJ D J := by
  rw [parJ_eq_sup] at hx
  exact pow_mem_of_mem_sup_normalizer (torus_le_normalizer_unipJ hct J)
    (torus_pow_eq_one hext hM) hx

include hext in
theorem leviM_gen (hp : ∀ γ ∈ D.roots, IsPGroup 2 (D.rootGroup γ)) (J : Set (Fin D.rank))
    (P : Subgroup K) (hP : ∀ x ∈ leviM D J, (∃ k : ℕ, x ^ 2 ^ k = 1) → x ∈ P) :
    leviM D J ≤ P := by
  refine iSup₂_le fun i hi => ?_
  have hα : (Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i
  have hα' : (-Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem _ hα
  unfold rankOne
  refine sup_le (fun x hx => ?_) (fun x hx => ?_)
  · obtain ⟨k, hk⟩ := hp _ hα ⟨x, hx⟩
    exact hP x (rankOne_le_leviM hi (Subgroup.mem_sup_left hx)) ⟨k, congrArg Subtype.val hk⟩
  · obtain ⟨k, hk⟩ := hp _ hα' ⟨x, hx⟩
    exact hP x (rankOne_le_leviM hi (Subgroup.mem_sup_right hx)) ⟨k, congrArg Subtype.val hk⟩

end K

section Main

variable {K Y : Type*} [Group K] [Finite K] [Group Y] {D : UniversalRootDatum K}
  {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {π : K →* Y} {M : ℕ}

theorem exists_mulEquiv_leviM (hbq : BorelQuotient D n H π M) {J : Set (Fin D.rank)}
    {Xt : Subgroup K} (hU : unipJ D J ≤ Xt) (hP : Xt ≤ parJ D H J) (ψ : K →* Y)
    (hker : ∀ x, ψ x = 1 → x ∈ Subgroup.center K) {A' : Subgroup Y} (hA' : Xt.map ψ = A')
    (hMs : IsSimpleGroup ↥(leviM D J)) (hMnc : ¬ IsMulCommutative ↥(leviM D J))
    (hM2 : ¬ IsPGroup 2 ↥(leviM D J)) :
    Nonempty (↥(pElementSubgroup 2 (⊤ : Subgroup (↥A' ⧸ CFSG.pCore 2 ↥A'))) ≃*
      ↥(leviM D J)) := by
  subst hA'
  exact exists_mulEquiv_of_levi_map ψ hker (U := leviRad D J) (N := unipJ D J) (M := leviM D J)
    hbq.odd (by rw [unipJ_eq_leviRad_sup_leviM hbq.ct J]; exact le_sup_left) hU le_sup_right
    (isPGroup_leviRad hbq.extras hbq.pGroup) (hP.trans (parJ_le_normalizer_leviRad hbq.ct hbq.extras J))
    (hP.trans (parJ_le_normalizer_unipJ hbq.ct J))
    (fun _ hx => exists_mul_of_mem_unipJ hbq.ct hbq.extras J hx)
    (fun x hx => pow_mem_unipJ_of_mem_parJ hbq.ct hbq.extras hbq.torus_pow J (hP hx))
    hMs hMnc hM2 (fun P hP => leviM_gen hbq.extras hbq.pGroup J P hP)

end Main

end CFSG.LocalAnalysis.RankThreeUC.S15.K517Six
