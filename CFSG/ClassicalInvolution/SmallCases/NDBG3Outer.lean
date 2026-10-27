module

public import CFSG.ClassicalInvolution.SmallCases.NDBG3Aut
public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterGen
public import CFSG.ClassicalInvolution.Asc77.AscT3UG2D4

public section

namespace CFSG.ClassicalInvolution.NDB.NDBG3

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Steinberg.Adjoint CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Asc77.FrameVertex CFSG.ClassicalInvolution.ModelFacts.Orth15
  CFSG.Assembly.LowTwoRank

theorem inducedImage_closure_pair {S H : Type} [Group S] [Group H] (ψ : S →* H) (a b : S) :
    inducedImage ψ.range (Subgroup.closure ({ψ a, ψ b} : Set H)) =
      Subgroup.closure ({innerHom ψ a, innerHom ψ b} : Set ↥(inducedAutOn ψ.range)) := by
  set N := Subgroup.normalizer (ψ.range : Set H)
  let ψ' : S →* ↥N := ψ.codRestrict N fun s => mem_normalizer_range ψ s
  have h1 : Subgroup.closure ({ψ a, ψ b} : Set H) =
      ((Subgroup.closure ({a, b} : Set S)).map ψ').map N.subtype := by
    rw [Subgroup.map_map, MonoidHom.map_closure, Set.image_pair]
    rfl
  have h2 : (((Subgroup.closure ({a, b} : Set S)).map ψ').map N.subtype).subgroupOf N =
      (Subgroup.closure ({a, b} : Set S)).map ψ' :=
    Subgroup.comap_map_eq_self_of_injective N.subtype_injective _
  unfold inducedImage
  rw [h1, h2, Subgroup.map_map, MonoidHom.map_closure, Set.image_pair]
  rfl

theorem exists_conj_xElement_of_fund {K : Type} [Field K] {R : Subgroup ↥(adjointGroup .G2 K)}
    (hR : R ∈ fundamentalSubgroups .G2 (g2Datum K)) :
    ∃ (h : ↥(adjointGroup .G2 K)) (j : Fin Tag.G2.rank), ∀ c : K, h * xElement j c * h⁻¹ ∈ R := by
  obtain ⟨g₀, γ, hγ, rfl⟩ := hR
  have hroot : IsRoot .G2 γ := by
    rcases hγ with h | ⟨-, h⟩ | ⟨h, -⟩
    · exact mem_adjDatum_roots.1 h.1
    · exact mem_adjDatum_roots.1 h
    · exact absurd h (by decide)
  obtain ⟨j, ε, m, hε, hm, hc⟩ :=
    (rootOperatorFamily .G2).exists_eltUnit_eq_conj K ⟨γ, hroot⟩
  have hm' : m ∈ adjointGroup .G2 K := (Subgroup.closure_le _).2
    (Set.range_subset_iff.2 fun i => weylElt_mem_adjointGroup i 1) hm
  have hεε : ∀ c : K, (ε : K) * ((ε : K) * c) = c := fun c => by
    rcases hε with rfl | rfl <;> simp
  refine ⟨g₀ * ⟨m, hm'⟩, j, fun c => ?_⟩
  have hmem : xPar (rootOperatorFamily .G2) γ ((ε : K) * c) ∈ (g2Datum K).rootGroup γ :=
    xPar_mem hroot _
  have heq : xPar (rootOperatorFamily .G2) γ ((ε : K) * c) =
      ⟨m, hm'⟩ * xElement j c * (⟨m, hm'⟩ : ↥(adjointGroup .G2 K))⁻¹ := by
    rw [xPar_of_isRoot hroot]
    apply Subtype.ext
    rw [RootOperatorFamily.coe_eltElement, hc, hεε]
    rfl
  rw [heq] at hmem
  refine ⟨_, Subgroup.mem_sup_left hmem, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group


theorem twinOuterAlpha_g2_three {e : ℕ} (he : 2 ≤ e) : TwinOuterAlpha 3 e .G2 0 := by
  intro H _ _ ψ R R' x x' hpair v hvR hvR' hv4 hv2 hv2x
  have hq : 5 ≤ 3 ^ e := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) he)
  have hadm : StatedLieAdmissible .G2 0 3 e := ⟨Nat.prime_three, by omega, rfl, by omega⟩
  obtain ⟨hperf, hZ, -, -⟩ := T3CII.T3U.g2d4_model_facts (p := 3) (f := e) (by norm_num) hq
    (Or.inl rfl) trivial hadm (Or.inl rfl)
  have hK : Nat.card (GaloisField 3 e) = 3 ^ e := GaloisField.card 3 e (by omega)
  let π := MonoidHom.id (modelUniv .G2 0 3 e Fact.out).K
  have hπ : Function.Surjective π := Function.surjective_id
  have hπk : π.ker = Subgroup.center (modelUniv .G2 0 3 e Fact.out).K := by
    rw [hZ]
    exact MonoidHom.ker_id
  have hfix : ∀ r ∈ R, outerAction ψ hpair.ker π hπ hπk v (π r) = π r := fun r hr => by
    apply (outerEquiv ψ hpair.ker π hπ hπk).injective
    apply Subtype.ext
    rw [outerAction_apply, outerEquiv_apply, hvR r hr]
    group
  obtain ⟨h, j, hRj⟩ := exists_conj_xElement_of_fund (K := GaloisField 3 e) hpair.mem
  have hex : ∃ b : (modelUniv .G2 0 3 e Fact.out).K,
      outerAction ψ hpair.ker π hπ hπk v = MulAut.conj b :=
    isInner_of_fix_xElement he hK _ h j fun c => hfix _ (hRj c)
  obtain ⟨b, hb⟩ := hex
  have hvb : v = innerHom ψ b := by
    have h1 : outerAction ψ hpair.ker π hπ hπk ((innerHom ψ b)⁻¹ * v) = 1 := by
      rw [map_mul, map_inv, outerAction_innerHom, hb]
      exact inv_mul_cancel _
    exact (inv_mul_eq_one.mp (eq_one_of_outerAction_eq_one ψ hpair.ker π hπ hπk h1)).symm
  subst hvb
  have hinj : Function.Injective ψ :=
    (MonoidHom.ker_eq_bot_iff ψ).1 (le_bot_iff.1 (hpair.ker.trans hZ.le))
  have hcen : ∀ g, innerHom ψ g = 1 → g = 1 := fun g hg => by
    have := (innerHom_spec ψ hpair.ker).1 g hg
    rwa [hZ, Subgroup.mem_bot] at this
  have hb4 : b * b * (b * b) = 1 := hcen _ (by simpa only [map_mul] using hv4)
  have hbx : b * x = x * b := by
    have e1 := hvR x hpair.hx
    rw [← map_mul, ← map_mul] at e1
    have := hcen (b * x * (x * b)⁻¹) (by rw [map_mul, map_inv, e1, mul_inv_cancel])
    exact mul_inv_eq_one.mp this
  have hbb1 : ψ (b * b) ≠ 1 := fun h1 => hv2 (by
    rw [← map_mul, hinj (h1.trans (map_one ψ).symm), map_one])
  have hbbx : ψ x ≠ ψ (b * b) := fun h1 => hv2x (by rw [← map_mul, ← hinj h1])
  have hx1 : ψ x ≠ 1 := fun h1 => hpair.hx1 (hinj (h1.trans (map_one ψ).symm))
  have hx2 : ψ x * ψ x = 1 := by rw [← map_mul, hpair.hx2, map_one]
  have hbb2 : ψ (b * b) * ψ (b * b) = 1 := by rw [← map_mul, hb4, map_one]
  have hcomm : ψ x * ψ (b * b) = ψ (b * b) * ψ x := by
    rw [← map_mul, ← map_mul]
    congr 1
    calc x * (b * b) = (x * b) * b := by group
      _ = b * x * b := by rw [hbx]
      _ = b * (x * b) := by group
      _ = b * (b * x) := by rw [hbx]
      _ = b * b * x := by group
  rw [← map_mul, ← inducedImage_closure_pair]
  refine T3CII.T3U.alphaOf_inducedImage_eq_bot_of_g2d4 (p := 3) (f := e) (by norm_num) hq
    (Or.inl rfl) trivial hadm (Or.inl rfl) ψ hpair.ker
    (Balance.Bootstrap.card_closure_pair_eq_four hx2 hbb2 hx1 hbb1 hbbx hcomm) (fun a ha => ?_)
    ((Subgroup.closure_le _).2 ?_)
  · refine Balance.Bootstrap.mul_self_eq_one_of_mem_closure ?_ ?_ ha
    · rintro z (rfl | rfl)
      · exact hx2
      · exact hbb2
    · rintro z (rfl | rfl) w (rfl | rfl)
      · rfl
      · exact hcomm
      · exact hcomm.symm
      · rfl
  · rintro _ (rfl | rfl)
    · exact ⟨x, rfl⟩
    · exact ⟨b * b, rfl⟩

end CFSG.ClassicalInvolution.NDB.NDBG3
