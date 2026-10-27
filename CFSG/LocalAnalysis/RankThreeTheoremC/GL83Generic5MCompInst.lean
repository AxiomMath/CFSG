module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Ctx
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5KFacts
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5MComp
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5BorelSolv
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Quot
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Setup2
import CFSG.LocalAnalysis.RankThreeTheoremC.Psl2TorusData
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerTwoGroups

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools CFSG.AGLEmbedding Subgroup
open scoped MatrixGroups

theorem GL83Generic5MComp.map_moves_of_injective {H G : Type*} [Group H] [Group G] {p : ℕ}
    (f : H →* G) (hf : Function.Injective f) {V : Subgroup H} {σ : H}
    (hσ : σ ∈ normalizer (V : Set H))
    (hmove : ∀ D : Subgroup H, D ≤ V → Nat.card D = p → ∃ d ∈ D, σ * d * σ⁻¹ ∉ D) :
    f σ ∈ normalizer ((V.map f : Subgroup G) : Set G) ∧
      ∀ D : Subgroup G, D ≤ V.map f → Nat.card D = p → ∃ d ∈ D, f σ * d * (f σ)⁻¹ ∉ D := by
  refine ⟨le_normalizer_map f ⟨σ, hσ, rfl⟩, fun D hD hDc => ?_⟩
  have hDr : D ≤ f.range := hD.trans (map_le_range f V)
  obtain ⟨d, hd, hdσ⟩ := hmove (D.comap f)
    (fun v hv => by
      obtain ⟨w, hw, hwv⟩ := hD hv
      exact hf hwv ▸ hw)
    (by rw [← card_map_of_injective hf, map_comap_eq_self hDr, hDc])
  refine ⟨f d, hd, fun h => hdσ ?_⟩
  rw [mem_comap, map_mul, map_mul, map_inv]
  exact h

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}

theorem gen5_exists_torus (hG : Gen5Global G) (hl : Gen5Local G p P M x) :
    ∃ t ∈ normalizer ((gen5U (P : Subgroup G) x : Subgroup G) : Set G),
      ∀ D : Subgroup G, D ≤ gen5U (P : Subgroup G) x → Nat.card D = p →
        ∃ d ∈ D, t * d * t⁻¹ ∉ D := by
  have : Fact p.Prime := ⟨gen5_prime hl⟩
  obtain ⟨e⟩ := gen5_psl hG hl
  obtain ⟨U₀, -, σ₀, hU₀c, -, -, -, -, hσ₀N, hσ₀, -⟩ := psl2_torus_data p (gen5_five_le hG hl)
  set L := gen5L x
  set f₀ : PSL(2, GaloisField p 2) →* G := L.subtype.comp e.symm.toMonoidHom
  have hf₀inj : Function.Injective f₀ := L.subtype_injective.comp e.symm.injective
  have hU₁ : IsSylowOf p (U₀.map f₀) L := by
    refine isSylowOf_of_card ?_ ?_
    · rintro _ ⟨u, -, rfl⟩
      exact (e.symm u).2
    · rw [card_map_of_injective hf₀inj, hU₀c,
        factorization_card_of_mulEquiv_psl (GaloisField.card p 2 (by norm_num)) e]
  obtain ⟨k, hkL, hk⟩ := hU₁.exists_mem_conj (gen5_sylow hG hl)
  set f : PSL(2, GaloisField p 2) →* G := (MulAut.conj k).toMonoidHom.comp f₀ with hf
  have hfinj : Function.Injective f := (MulAut.conj k).injective.comp hf₀inj
  have hfU : U₀.map f = gen5U (P : Subgroup G) x := by
    ext y
    rw [hk y, hf, ← map_map]
    constructor
    · rintro ⟨z, hz, rfl⟩
      change k⁻¹ * (k * z * k⁻¹) * k ∈ _
      rwa [show k⁻¹ * (k * z * k⁻¹) * k = z by group]
    · intro hy
      exact ⟨k⁻¹ * y * k, hy, by simp [mul_assoc]⟩
  obtain ⟨hN, hmove⟩ := GL83Generic5MComp.map_moves_of_injective f hfinj hσ₀N hσ₀
  rw [hfU] at hN hmove
  exact ⟨f σ₀, hN, hmove⟩

theorem gen5_MComp (hG : Gen5Global G) (hK : GL83Generic5KFacts) (hl : Gen5Local G p P M x)
    (hxM : x ∈ M) {K : Subgroup (M ⧸ primeComplementCore (G := M) p)}
    (hKc : IsComponentOf K ⊤) :
    K.Normal ∧ center K = ⊥ ∧
      QuotientGroup.mk' (primeComplementCore (G := M) p) ⟨x, hxM⟩ ∈ K ∧
      (∀ R : Sylow p K, IsCyclic (R : Subgroup K)) ∧
      ((gen5U (P : Subgroup G) x).subgroupOf M).map
        (QuotientGroup.mk' (primeComplementCore (G := M) p)) ≤ centralizer (K : Set _) ∧
      ∀ K' : Subgroup (M ⧸ primeComplementCore (G := M) p), IsComponentOf K' ⊤ → K' = K := by
  have hp := gen5_prime hl
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hUe, hUc⟩ := gen5_U_elemAbelian hG hl
  set O : Subgroup M := primeComplementCore (G := M) p
  set U : Subgroup G := gen5U (P : Subgroup G) x
  have hMtop : M ≠ ⊤ := by
    have := hG.setting.simple
    exact CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top hG.setting.nonab hl.core.1.1
  have hUM : U ≤ M := inf_le_left.trans (sylow_le_of_isCoreMaxLocal hG.setting hl.sigma hl.core).1
  obtain ⟨-, hx1, hxp, -, -⟩ := hl.generic.2.1
  have hxo : orderOf (⟨x, hxM⟩ : M) = p := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime hxp hx1
  have hxo' : orderOf (QuotientGroup.mk' O ⟨x, hxM⟩) = p :=
    orderOf_mk_of_coprime hp O (primeComplementCore_coprime p) hxo
  have hab := isMulCommutative_sylow_quotient (N := M) fun _ hQ => (gen5_pgroup hG hl hQ).1
  have hUp : IsPGroup p (U.subgroupOf M) :=
    (elementary_isPGroup p U hUe).comap_subtype
  have hU1 : U ≠ ⊥ := fun h => by
    rw [h, card_bot] at hUc
    have := hp.one_lt
    nlinarith
  obtain ⟨t, htN, htmove⟩ := gen5_exists_torus hG hl
  have htM : t ∈ M := gen5_normalizer_le hG hl le_rfl hU1 htN
  have hperf : ∀ J : Subgroup (M ⧸ O),
      J ≤ centralizer ({QuotientGroup.mk' O ⟨x, hxM⟩} : Set (M ⧸ O)) → ⁅J, J⁆ = J → J = ⊥ := by
    intro J hJ hJp
    obtain ⟨A, hAC, rfl, hAp⟩ :=
      exists_perfect_le_map_eq _ (hJ.trans (centralizer_mk_le_map hp hxo)) hJp
    have hAS : A.map M.subtype ≤ M ⊓ normalizer ((gen5L x : Subgroup G) : Set G) := by
      rintro _ ⟨a, ha, rfl⟩
      exact ⟨a.2, gen5_centralizer_le_normalizer x (mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp (hAC ha))))⟩
    have := gen5_solvable_inf_normalizer hG hl
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
  have hUbarc : Nat.card ((U.subgroupOf M).map (QuotientGroup.mk' O)) = p ^ 2 := by
    rw [card_map_mk_of_isPGroup hp O (primeComplementCore_coprime p) hUp, ← hUc]
    exact Nat.card_congr (subgroupOfEquivOfLe hUM).toEquiv
  have hUbarx : (U.subgroupOf M).map (QuotientGroup.mk' O) ≤
      centralizer ({QuotientGroup.mk' O ⟨x, hxM⟩} : Set (M ⧸ O)) := by
    rintro _ ⟨u, hu, rfl⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext (mem_centralizer_iff.mp (gen5_Z hG hl).1 _ hu.2))
  have htN' : (⟨t, htM⟩ : M) ∈ normalizer ((U.subgroupOf M : Subgroup M) : Set M) :=
    mem_normalizer_iff.mpr fun m => by
      simp only [mem_subgroupOf, coe_mul, coe_inv]
      exact mem_normalizer_iff.mp htN m
  have hσmove : ∀ D : Subgroup (M ⧸ O), D ≤ (U.subgroupOf M).map (QuotientGroup.mk' O) →
      Nat.card D = p → ∃ d ∈ D, QuotientGroup.mk' O ⟨t, htM⟩ * d *
        (QuotientGroup.mk' O ⟨t, htM⟩)⁻¹ ∉ D := by
    intro D hD hDc
    have hD₀ := map_comap_inf_eq (QuotientGroup.mk' O) hD
    obtain ⟨_, ⟨d, hd, rfl⟩, hdt⟩ := htmove ((D.comap (QuotientGroup.mk' O) ⊓
      U.subgroupOf M).map M.subtype) (by rintro _ ⟨d, hd, rfl⟩; exact hd.2)
      (by rw [card_map_of_injective M.subtype_injective, ← card_map_mk_of_isPGroup hp O
        (primeComplementCore_coprime p) (hUp.to_le inf_le_right), hD₀, hDc])
    refine ⟨QuotientGroup.mk' O d, (mem_inf.mp hd).1, fun h => hdt ⟨⟨t, htM⟩ * d * ⟨t, htM⟩⁻¹,
      mem_inf.mpr ⟨?_, (mem_normalizer_iff.mp htN' d).mp (mem_inf.mp hd).2⟩, rfl⟩⟩
    rw [mem_comap, map_mul, map_mul, map_inv]
    exact h
  exact gl83Generic5MComp_holds hK.weakClosure hK.innerAction (gen5_five_le hG hl)
    (primeComplementCore_quotient_eq_bot p)
    ((catalogSimpleSections_of_isKProper hG.setting.kProper M hMtop).quotient O)
    (pRank_top_quotient_le hp fun _ hQ => (gen5_pgroup hG hl hQ).2) hab
    (fun h => by
      rw [h, orderOf_one] at hxo'
      exact hp.one_lt.ne hxo')
    (by simpa only [hxo'] using pow_orderOf_eq_one (QuotientGroup.mk' O ⟨x, hxM⟩))
    (weaklyClosed_map_mk hxo hab (gen5_weakly_closed hG hl)) hperf
    (CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hUe' _) hUbarc hUbarx
    (le_normalizer_map _ ⟨_, htN', rfl⟩) hσmove hKc

end CFSG.LocalAnalysis.RankThreeTheoremC
