module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Ctx
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Quot
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Setup2
import CFSG.SignalizerFunctorTheorem.Inheritance.TransportA.Fitting

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G]

theorem map_rankThreeLayer_le (e : G ≃* G) (H : Subgroup G) :
    (rankThreeLayer H).map e.toMonoidHom ≤ rankThreeLayer (H.map e.toMonoidHom) := by
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun L hL => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  exact le_sSup (CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map e hL)

theorem normalizer_le_normalizer_rankThreeLayer (H : Subgroup G) :
    normalizer (H : Set G) ≤ normalizer ((rankThreeLayer H : Subgroup G) : Set G) := by
  have key : ∀ g ∈ normalizer (H : Set G), ∀ y ∈ rankThreeLayer H,
      g * y * g⁻¹ ∈ rankThreeLayer H := by
    intro g hg y hy
    have hH : H.map (MulAut.conj g).toMonoidHom = H :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
    have h := map_rankThreeLayer_le (MulAut.conj g) H ⟨y, hy, rfl⟩
    rwa [hH] at h
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  refine fun y => ⟨key g hg y, fun hy => ?_⟩
  simpa [mul_assoc] using key g⁻¹ (inv_mem hg) _ hy

theorem isSolvable_of_layer_quotient_eq_bot {X : Type*} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] (hO : Group.IsSolvable (primeComplementCore (G := X) p))
    (hlayer : CFSG.layer (X ⧸ primeComplementCore (G := X) p) = ⊥)
    (hab : ∀ S : Sylow p (X ⧸ primeComplementCore (G := X) p),
      IsMulCommutative (S : Subgroup (X ⧸ primeComplementCore (G := X) p)))
    (S : Sylow p X) (hN : Group.IsSolvable (normalizer ((S : Subgroup X) : Set X))) :
    Group.IsSolvable X := by
  set O := primeComplementCore (G := X) p with hOdef
  have hcore : primeComplementCore (G := X ⧸ O) p = ⊥ := primeComplementCore_quotient_eq_bot p
  have hchar : centralizer (CFSG.pCore p (X ⧸ O) : Set (X ⧸ O)) ≤ CFSG.pCore p (X ⧸ O) :=
    CFSG.isCharacteristicP_of_pPrimeCore_eq_bot_of_layer_eq_bot (X ⧸ O) p hcore hlayer
  set Sbar : Sylow p (X ⧸ O) := S.mapSurjective (QuotientGroup.mk'_surjective O) with hSbar
  have hQS : CFSG.pCore p (X ⧸ O) ≤ (Sbar : Subgroup (X ⧸ O)) :=
    CFSG.pCore_isPGroup.le_sylow_of_normal Sbar
  have : IsMulCommutative (Sbar : Subgroup (X ⧸ O)) := hab Sbar
  have hSQ : (Sbar : Subgroup (X ⧸ O)) ≤ CFSG.pCore p (X ⧸ O) := by
    refine le_trans (fun s hs => ?_) hchar
    rw [mem_centralizer_iff]
    intro q hq
    exact setLike_mul_comm (hQS hq) hs
  have hnormal : (Sbar : Subgroup (X ⧸ O)).Normal := by
    rw [le_antisymm hSQ hQS]
    infer_instance
  have htop : (⊤ : Subgroup X) ≤ O ⊔ normalizer ((S : Subgroup X) : Set X) := by
    have h := CFSG.AGLEmbedding.comap_normalizer_map_le_sup Fact.out O
      (primeComplementCore_coprime p) S.isPGroup'
    rwa [← Sylow.coe_mapSurjective (QuotientGroup.mk'_surjective O), ← hSbar,
      normalizer_eq_top, Subgroup.comap_top] at h
  have hsurj : Function.Surjective
      ((QuotientGroup.mk' O).comp (normalizer ((S : Subgroup X) : Set X)).subtype) := by
    intro y
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective O y
    have ha : a ∈ ((O ⊔ normalizer ((S : Subgroup X) : Set X) : Subgroup X) : Set X) :=
      htop (Subgroup.mem_top a)
    rw [Subgroup.normal_mul, Set.mem_mul] at ha
    obtain ⟨o, ho, n, hn, rfl⟩ := ha
    refine ⟨⟨n, hn⟩, ?_⟩
    simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype]
    have h1 : QuotientGroup.mk' O o = 1 := (QuotientGroup.eq_one_iff o).mpr ho
    rw [map_mul, h1, one_mul]
  have : Group.IsSolvable (X ⧸ O) := Group.isSolvable_of_surjective hsurj
  exact Group.isSolvable_of_subgroup_quotient O

section Gen5

variable [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}

theorem gen5_normalizer_sylow_le_normalizer (hG : Gen5Global G) (hl : Gen5Local G p P M x) :
    normalizer ((P : Subgroup G) : Set G) ≤ normalizer ((gen5L x : Subgroup G) : Set G) := by
  intro g hg
  have hgx : g * x * g⁻¹ ∈ (P : Subgroup G) :=
    (Subgroup.mem_normalizer_iff.mp hg x).mp hl.generic.1
  have hCC : centralizer ({g * x * g⁻¹} : Set G) = centralizer ({x} : Set G) := by
    rw [← centralizer_closure, ← zpowers_eq_closure, gen5_weakly_closed_P hG hl hgx,
      zpowers_eq_closure, centralizer_closure]
  have hC : g ∈ normalizer ((centralizer ({x} : Set G) : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro c
    conv_rhs => rw [← hCC]
    rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
    have e1 : g * c * g⁻¹ * (g * x * g⁻¹) = g * (c * x) * g⁻¹ := by group
    have e2 : g * x * g⁻¹ * (g * c * g⁻¹) = g * (x * c) * g⁻¹ := by group
    rw [e1, e2, mul_left_inj, mul_right_inj]
  exact normalizer_le_normalizer_rankThreeLayer _ hC

theorem gen5_isSolvable (hG : Gen5Global G) (hl : Gen5Local G p P M x)
    (hO : Group.IsSolvable (rankThreePrimeCore p M))
    (hN : Group.IsSolvable ↥(M ⊓ normalizer ((gen5L x : Subgroup G) : Set G)))
    (hlayer : CFSG.layer (M ⧸ primeComplementCore (G := M) p) = ⊥) : Group.IsSolvable M := by
  have : Fact p.Prime := ⟨gen5_prime hl⟩
  have hPM : (P : Subgroup G) ≤ M := (sylow_le_of_isCoreMaxLocal hG.setting hl.sigma hl.core).1
  have hO' : Group.IsSolvable (primeComplementCore (G := M) p) := by
    rw [rankThreePrimeCore_eq_map_primeComplementCore] at hO
    exact Group.isSolvable_of_isSolvable_injective
      (f := ((primeComplementCore (G := M) p).equivMapOfInjective M.subtype
        M.subtype_injective).toMonoidHom) (MulEquiv.injective _)
  refine isSolvable_of_layer_quotient_eq_bot hO' hlayer
    (isMulCommutative_sylow_quotient fun Q hQ => (gen5_pgroup hG hl hQ).1) (P.subtype hPM) ?_
  have hmap : (normalizer (((P.subtype hPM : Sylow p M) : Subgroup M) : Set M)).map M.subtype ≤
      M ⊓ normalizer ((gen5L x : Subgroup G) : Set G) := by
    rintro _ ⟨n, hn, rfl⟩
    refine ⟨n.2, gen5_normalizer_sylow_le_normalizer hG hl ?_⟩
    have h := Subgroup.le_normalizer_map M.subtype ⟨n, hn, rfl⟩
    rwa [Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le hPM] at h
  exact Group.isSolvable_of_isSolvable_injective
    (f := (Subgroup.inclusion hmap).comp
      ((normalizer _).equivMapOfInjective M.subtype M.subtype_injective).toMonoidHom)
    ((Subgroup.inclusion_injective hmap).comp (MulEquiv.injective _))

end Gen5

end CFSG.LocalAnalysis.RankThreeTheoremC
