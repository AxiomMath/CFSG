module

public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusNodeRoots

public section

namespace CFSG.AGLEmbedding.ToralCensus

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.AGLEmbedding.ParabPrime CFSG.AGLEmbedding.LieOut

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

theorem weylAction_three_single_left {a i : Fin D.rank} (h1 : D.cartan a i = -1)
    (h2 : D.cartan i a = -1) :
    weylAction D.isFiniteType ((coxeterMatrix D.isFiniteType).toCoxeterSystem.simple a *
      (coxeterMatrix D.isFiniteType).toCoxeterSystem.simple i) (Pi.single a 1) =
      Pi.single i 1 := by
  rw [weylAction_mul_apply, single_eq_pair_left a i, weylAction_simple_pair_right,
    weylAction_simple_pair_left, h1, h2, single_eq_pair_right a i]
  norm_num

theorem weylAction_three_single {a i b : Fin D.rank} (h1 : D.cartan a i = -1)
    (h3 : D.cartan a b = 0) :
    weylAction D.isFiniteType ((coxeterMatrix D.isFiniteType).toCoxeterSystem.simple a *
      (coxeterMatrix D.isFiniteType).toCoxeterSystem.simple i) (Pi.single b 1) =
      Pi.single b 1 - D.cartan i b • Pi.single i 1 - D.cartan i b • Pi.single a 1 := by
  rw [weylAction_mul_apply, weylAction_simple, weylAction_simple, reflection_apply_coroot _ i,
    coroot_single, reflection_apply_coroot _ a, map_sub, map_zsmul, coroot_single, coroot_single,
    h1, h3]
  simp only [smul_eq_mul, mul_neg, mul_one, zero_sub, neg_neg]

theorem commutes_rankOne_three
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) {a i b : Fin D.rank} (hab : a ≠ b) (h1 : D.cartan a i = -1)
    (h2 : D.cartan i a = -1) (h3 : D.cartan a b = 0) :
    Commutes (rankOne D.rootGroup i)
      ((rankOne D.rootGroup b).map (MulAut.conj (n a * n i)).toMonoidHom) := by
  have hx := (actsAs_n hct a).mul (actsAs_n hct i)
  have hLi : (rankOne D.rootGroup a).map (MulAut.conj (n a * n i)).toMonoidHom =
      rankOne D.rootGroup i := by
    rw [rankOne_map_conj_eq hx a, weylAction_three_single_left h1 h2]
    rfl
  rw [← hLi]
  exact (commutes_rankOne_of_cartan_eq_zero hext hab h3).map _

theorem rootGroup_neg_not_le
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) {A : Subgroup K} (hBA : borel D H ≤ A) {k : Fin D.rank}
    (hk : k ∉ negIndices D A) {x : K} {w : (coxeterMatrix D.isFiniteType).Group}
    (hx : ActsAs D x w) {m : Fin D.rank}
    (hpos : 0 < weylAction D.isFiniteType w (Pi.single m 1) k) :
    ¬ D.rootGroup (-weylAction D.isFiniteType w (Pi.single m 1)) ≤ A := by
  intro hle
  set β := weylAction D.isFiniteType w (Pi.single m 1) with hβ
  have hβr : β ∈ D.roots := weylAction_mem_roots D.isFiniteType w
    ((RootSystem.ofCartan D.isFiniteType D.divisible).single_mem m)
  have hβr' : -β ∈ D.roots := (RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem _ hβr
  have hAN : A ≤ Subgroup.normalizer (radical D k : Set K) := by
    rw [eq_borel_sup_rankOne hct hext hBA]
    refine sup_le (borel_le_normalizer_radical hct hext k) (iSup₂_le fun i hi => ?_)
    exact rankOne_le_normalizer_radical hext fun e => hk (e ▸ hi)
  have hy := (hx.mul (actsAs_n hct m)).mul hx.inv
  have hyA : x * n m * x⁻¹ ∈ A := by
    have hyL : x * n m * x⁻¹ ∈ (rankOne D.rootGroup m).map (MulAut.conj x).toMonoidHom :=
      ⟨n m, hct.n_mem m, rfl⟩
    rw [rankOne_map_conj_eq hx m] at hyL
    exact sup_le ((rootGroup_le_borel hβr (ht_pos_of_coord hβr hpos)).trans hBA) hle hyL
  have hswap : weylAction D.isFiniteType
      (w * (coxeterMatrix D.isFiniteType).toCoxeterSystem.simple m * w⁻¹) β = -β := by
    rw [hβ, weylAction_mul_apply, weylAction_mul_apply, weylAction_inv_apply_apply,
      weylAction_simple_single, map_neg]
  have hR : D.rootGroup (-β) ≤ radical D k := by
    rw [← hswap, ← hy β hβr]
    rintro _ ⟨z, hz, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 (hAN hyA) z).1 (rootGroup_le_radical hβr hpos hz)
  have hneg : ht (-β) < 0 := by
    rw [ht_neg]
    have := ht_pos_of_coord hβr hpos
    omega
  have h2 : D.rootGroup (-β) ≤ posUnipotent D ⊓ negUnipotent D :=
    le_inf (hR.trans (radical_le_posUnipotent k)) (rootGroup_le_negUnipotent hβr' hneg)
  rw [posUnipotent_inf_negUnipotent hext] at h2
  exact hext.ne_bot _ hβr' (le_bot_iff.1 h2)

theorem map_rankOne_conj_not_le
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) {Y : Type*} [Group Y] {π : K →* Y} {J : Subgroup Y}
    (hBJ : (borel D H).map π ≤ J) {k : Fin D.rank} (hk : k ∉ negIndices D (J.comap π))
    {x : K} {w : (coxeterMatrix D.isFiniteType).Group} (hx : ActsAs D x w) {m : Fin D.rank}
    (hpos : 0 < weylAction D.isFiniteType w (Pi.single m 1) k) :
    ¬ ((rankOne D.rootGroup m).map (MulAut.conj x).toMonoidHom).map π ≤ J := by
  intro hle
  refine rootGroup_neg_not_le hct hext (fun b hb => hBJ ⟨b, hb, rfl⟩) hk hx hpos fun y hy => ?_
  have hyL : y ∈ (rankOne D.rootGroup m).map (MulAut.conj x).toMonoidHom := by
    rw [rankOne_map_conj_eq hx m]
    exact Subgroup.mem_sup_right hy
  exact hle ⟨y, hyL, rfl⟩

theorem map_rankOne_conj_perfect {Y : Type*} [Group Y] (π : K →* Y) (x : K) {m : Fin D.rank}
    (hm : ⁅rankOne D.rootGroup m, rankOne D.rootGroup m⁆ = rankOne D.rootGroup m) :
    ⁅((rankOne D.rootGroup m).map (MulAut.conj x).toMonoidHom).map π,
      ((rankOne D.rootGroup m).map (MulAut.conj x).toMonoidHom).map π⁆ =
      ((rankOne D.rootGroup m).map (MulAut.conj x).toMonoidHom).map π := by
  rw [← Subgroup.map_commutator, ← Subgroup.map_commutator, hm]

end CFSG.AGLEmbedding.ToralCensus
