module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.MComp
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.WeakClosed
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.Borel
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.TorusData
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Quot

public section

open Subgroup
open scoped MatrixGroups

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools CFSG.AGLEmbedding
open CFSG.LocalAnalysis.RankThreeTheoremC (weaklyClosed_map_mk centralizer_mk_le_map
  exists_perfect_le_map_eq isMulCommutative_sylow_quotient)

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}

theorem movesHyperplanes_map {H G' : Type*} [Group H] [Group G'] {p : ℕ} (f : H →* G')
    (hf : Function.Injective f) {V : Subgroup H} {σ : H} (hσ : MovesHyperplanes p V σ) :
    MovesHyperplanes p (V.map f) (f σ) := by
  obtain ⟨hσN, hmove⟩ := hσ
  refine ⟨le_normalizer_map f ⟨σ, hσN, rfl⟩, fun j hj1 hj3 D hD hDc => ?_⟩
  have hDr : D ≤ f.range := hD.trans (map_le_range f V)
  have hDV : D.comap f ≤ V := fun v hv => by
    obtain ⟨w, hw, hwv⟩ := hD hv
    exact hf hwv ▸ hw
  have h1 : Nat.card (D.comap f) = Nat.card D := by
    rw [← card_map_of_injective hf, map_comap_eq_self hDr]
  have hcard : Nat.card V = p * Nat.card (D.comap f) := by
    calc Nat.card V = Nat.card (V.map f) := (card_map_of_injective hf).symm
      _ = p * Nat.card D := hDc
      _ = p * Nat.card (D.comap f) := by rw [h1]
  obtain ⟨h, hh, hhσ⟩ := hmove j hj1 hj3 (D.comap f) hDV hcard
  refine ⟨f h, hh, fun hmem => hhσ ?_⟩
  rw [mem_comap, map_mul, map_mul, map_inv, map_pow]
  exact hmem

theorem fr_exists_torus [Fact p.Prime] (hG : FrobGlobal G) (hl : FrobLocal p P M x) :
    ∃ t : G, MovesHyperplanes p (frU P x) t := by
  obtain ⟨n, hn3, ⟨e⟩, hU, hUe, hUc⟩ := fr_layer_rank hG hl
  obtain ⟨U₀, σ₀, hU₀c, -, -, hσ₀⟩ := psl2_torus_data_hyperplane p hl.p5 n hn3
  set L := layerOf x
  set f₀ : PSL(2, GaloisField p n) →* G := L.subtype.comp e.symm.toMonoidHom
  have hf₀inj : Function.Injective f₀ := L.subtype_injective.comp e.symm.injective
  have hU₁ : IsSylowOf p (U₀.map f₀) L := by
    refine isSylowOf_of_card ?_ ?_
    · rintro _ ⟨u, -, rfl⟩
      exact (e.symm u).2
    · rw [card_map_of_injective hf₀inj, hU₀c, ← hU.card_eq, hUc]
  obtain ⟨k, hkL, hk⟩ := hU₁.exists_mem_conj hU
  set f : PSL(2, GaloisField p n) →* G := (MulAut.conj k).toMonoidHom.comp f₀ with hf
  have hfinj : Function.Injective f := (MulAut.conj k).injective.comp hf₀inj
  have hfU : U₀.map f = frU P x := by
    ext y
    rw [hk y, hf, ← map_map]
    constructor
    · rintro ⟨z, hz, rfl⟩
      change k⁻¹ * (k * z * k⁻¹) * k ∈ _
      rwa [show k⁻¹ * (k * z * k⁻¹) * k = z by group]
    · intro hy
      exact ⟨k⁻¹ * y * k, hy, by simp [mul_assoc]⟩
  have h := movesHyperplanes_map f hfinj hσ₀
  rw [hfU] at h
  exact ⟨f σ₀, h⟩

theorem movesHyperplanes_map_mk [Fact p.Prime] {U : Subgroup G} (hUM : U ≤ M) (hUp : IsPGroup p U)
    {t : G} (htM : t ∈ M) (ht : MovesHyperplanes p U t) :
    MovesHyperplanes p ((U.subgroupOf M).map (QuotientGroup.mk' (primeComplementCore (G := M) p)))
      (QuotientGroup.mk' (primeComplementCore (G := M) p) ⟨t, htM⟩) := by
  have hp : p.Prime := Fact.out
  obtain ⟨htN, htmove⟩ := ht
  set O := primeComplementCore (G := M) p with hO
  have hUp' : IsPGroup p (U.subgroupOf M) := hUp.comap_subtype
  have htN' : (⟨t, htM⟩ : M) ∈ normalizer ((U.subgroupOf M : Subgroup M) : Set M) :=
    mem_normalizer_iff.mpr fun m => by
      simp only [mem_subgroupOf, coe_mul, coe_inv]
      exact mem_normalizer_iff.mp htN m
  refine ⟨le_normalizer_map _ ⟨_, htN', rfl⟩, fun j hj1 hj3 D hD hDc => ?_⟩
  have hD₀ := map_comap_inf_eq (QuotientGroup.mk' O) hD
  have hcU : Nat.card ((U.subgroupOf M).map (QuotientGroup.mk' O)) = Nat.card U := by
    rw [card_map_mk_of_isPGroup hp O (primeComplementCore_coprime p) hUp']
    exact Nat.card_congr (subgroupOfEquivOfLe hUM).toEquiv
  have hcD : Nat.card ((D.comap (QuotientGroup.mk' O) ⊓ U.subgroupOf M).map M.subtype) =
      Nat.card D := by
    rw [card_map_of_injective M.subtype_injective, ← card_map_mk_of_isPGroup hp O
      (primeComplementCore_coprime p) (hUp'.to_le inf_le_right), hD₀]
  obtain ⟨_, ⟨d, hd, rfl⟩, hdt⟩ := htmove j hj1 hj3
    ((D.comap (QuotientGroup.mk' O) ⊓ U.subgroupOf M).map M.subtype)
    (by rintro _ ⟨d, hd, rfl⟩; exact hd.2) (by rw [hcD, ← hcU]; exact hDc)
  refine ⟨QuotientGroup.mk' O d, (mem_inf.mp hd).1, fun h => hdt ⟨(⟨t, htM⟩ : M) ^ j * d *
    ((⟨t, htM⟩ : M) ^ j)⁻¹, mem_inf.mpr ⟨?_, ?_⟩, rfl⟩⟩
  · rw [mem_comap, map_mul, map_mul, map_inv, map_pow]
    exact h
  · exact (mem_normalizer_iff.mp (pow_mem htN' j) d).mp (mem_inf.mp hd).2

theorem fr_MComp [Fact p.Prime] (hK : FrobKFacts) (hG : FrobGlobal G) (hl : FrobLocal p P M x)
    (hxM : x ∈ M) {K : Subgroup (M ⧸ primeComplementCore (G := M) p)}
    (hKc : IsComponentOf K ⊤) :
    K.Normal ∧ center K = ⊥ ∧
      QuotientGroup.mk' (primeComplementCore (G := M) p) ⟨x, hxM⟩ ∈ K ∧
      (∀ R : Sylow p K, IsCyclic (R : Subgroup K)) ∧
      ((frU P x).subgroupOf M).map (QuotientGroup.mk' (primeComplementCore (G := M) p)) ≤
        centralizer (K : Set _) ∧
      ∀ K' : Subgroup (M ⧸ primeComplementCore (G := M) p), IsComponentOf K' ⊤ → K' = K := by
  have hp : p.Prime := Fact.out
  obtain ⟨n, hn3, ⟨e⟩, hUsyl, hUe, hUc⟩ := fr_layer_rank hG hl
  set O : Subgroup M := primeComplementCore (G := M) p with hO
  set U : Subgroup G := frU P x with hU
  have hMtop : M ≠ ⊤ := fr_M_ne_top hl
  have hUM : U ≤ M := frU_le_M hl
  have hxo : orderOf (⟨x, hxM⟩ : M) = p := by
    rw [Subgroup.orderOf_mk]
    exact hl.point.elem.2.1
  have hxo' : orderOf (QuotientGroup.mk' O ⟨x, hxM⟩) = p :=
    orderOf_mk_of_coprime hp O (primeComplementCore_coprime p) hxo
  have hab := isMulCommutative_sylow_quotient (N := M) fun _ hQ => fr_pGroup_abelian hl _ hQ
  have hUpG : IsPGroup p U := elementary_isPGroup p U hUe
  have hUp : IsPGroup p (U.subgroupOf M) := hUpG.comap_subtype
  have hU1 : U ≠ ⊥ := frU_ne_bot hG hl
  obtain ⟨t, htmove⟩ := fr_exists_torus hG hl
  have htM : t ∈ M := by
    obtain ⟨htN, -⟩ := htmove
    exact fr_normalizer_le hG hl le_rfl hU1 htN
  have hperf : ∀ J : Subgroup (M ⧸ O),
      J ≤ centralizer ({QuotientGroup.mk' O ⟨x, hxM⟩} : Set (M ⧸ O)) → ⁅J, J⁆ = J → J = ⊥ := by
    intro J hJ hJp
    obtain ⟨A, hAC, rfl, hAp⟩ :=
      exists_perfect_le_map_eq _ (hJ.trans (centralizer_mk_le_map hp hxo)) hJp
    have hAS : A.map M.subtype ≤ M ⊓ normalizer ((layerOf x : Subgroup G) : Set G) := by
      rintro _ ⟨a, ha, rfl⟩
      exact ⟨a.2, fr_layer_normal_in_centralizer x (mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp (hAC ha))))⟩
    have := fr_solvable_inf_normalizer hG hl
    have : Group.IsSolvable (A.map M.subtype) := Group.isSolvable_of_isSolvable_injective
      (f := inclusion hAS) (inclusion_injective hAS)
    have : Group.IsPerfect (A.map M.subtype) :=
      isPerfect_iff.mpr (by rw [← map_commutator, hAp])
    have hA : A.map M.subtype = ⊥ := by
      by_contra hne
      have : Nontrivial (A.map M.subtype) := (nontrivial_iff_ne_bot _).mpr hne
      exact Group.IsPerfect.not_isSolvable (A.map M.subtype) inferInstance
    rw [(map_eq_bot_iff_of_injective _ M.subtype_injective).mp hA, Subgroup.map_bot]
  have := hUe.1
  have hUe' : IsElemAbelian p (U.subgroupOf M) :=
    ⟨IsMulCommutative.of_comm fun a b =>
      Subtype.ext (Subtype.ext (setLike_mul_comm (s := U) a.2 b.2)),
      fun a ha => Subtype.ext (by rw [coe_pow, coe_one]; exact hUe.2 _ ha)⟩
  have hUbarc : Nat.card ((U.subgroupOf M).map (QuotientGroup.mk' O)) = p ^ n := by
    rw [card_map_mk_of_isPGroup hp O (primeComplementCore_coprime p) hUp, ← hUc]
    exact Nat.card_congr (subgroupOfEquivOfLe hUM).toEquiv
  have hUbarx : (U.subgroupOf M).map (QuotientGroup.mk' O) ≤
      centralizer ({QuotientGroup.mk' O ⟨x, hxM⟩} : Set (M ⧸ O)) := by
    rintro _ ⟨u, hu, rfl⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext (mem_centralizer_iff.mp (fr_x_mem_Z0 hl).2 _ hu.2))
  exact frobMComp_holds hK.weak hK.inner
    ⟨hl.p5, primeComplementCore_quotient_eq_bot p,
      (catalogSimpleSections_of_isKProper hG.kProper M hMtop).quotient O, hab,
      (fun h => by
        rw [h, orderOf_one] at hxo'
        exact hp.one_lt.ne hxo'),
      (by simpa only [hxo'] using pow_orderOf_eq_one (QuotientGroup.mk' O ⟨x, hxM⟩)),
      weaklyClosed_map_mk hxo hab (fun Q hxQ g hg => fr_weakly_closed hl Q hxQ g hg), hperf,
      CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hUe' _, hUbarc, hUbarx,
      movesHyperplanes_map_mk hUM hUpG htM htmove⟩ hKc

end CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius
