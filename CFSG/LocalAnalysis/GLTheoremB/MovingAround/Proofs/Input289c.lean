module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Input289b2
public import CFSG.Quasithin.Vol2.F134LieD4Cells
public import CFSG.LieType.Chevalley.RootWeightOptimalParabolic
public import CFSG.LieType.Chevalley.OrdinaryRootCentralizerGeneration
public import CFSG.LieType.Chevalley.EvenTrialityTorusCoordinates
public import CFSG.LieType.Chevalley.GraphFixedSimpleBruhat
public import CFSG.LieType.Chevalley.FoldedWeylIdentification
public import CFSG.LieType.Chevalley.GraphFixedBorelCoreCenter
public import CFSG.Timmesfeld.Orders.ExceptionalTwistedUnipotent

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Input289c

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Model

variable {F : Type} [Field F]

theorem exists_normalizer_le_graphFixedParabolic [Finite F] [CharP F 2] (σ : F ≃+* F)
    (hσ : σ ^ TwistTag.D4.order = 1) {S : Subgroup (ModGL TwistTag.D4.tag F)}
    (hSC : S ≤ graphFixedRootGroup TwistTag.D4 F σ.toRingHom) (hS2 : IsPGroup 2 S) (hS : S ≠ ⊥) :
    ∃ g ∈ graphFixedRootGroup TwistTag.D4 F σ.toRingHom,
      ∃ J : Set (Fin TwistTag.D4.foldedTag.rank), J ≠ Set.univ ∧
        ∀ x ∈ graphFixedRootGroup TwistTag.D4 F σ.toRingHom ⊓
            Subgroup.normalizer (S : Set (ModGL TwistTag.D4.tag F)),
          g⁻¹ * x * g ∈ graphFixedParabolic TwistTag.D4 F σ.toRingHom J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := finite_modGL (τ := TwistTag.D4.tag) (K := F)
  obtain ⟨M, -, -, -, Fl, -, -, ⟨g, hg, l, hl, hl1, hgl⟩, hdom, -⟩ :=
    RootWeightDatum.root_p_subgroup_optimal_parabolic_containment
      (RootWeightDatum.fixed TwistTag.D4 σ hσ : RootWeightDatum F) 2 S hSC hS2 hS
  obtain ⟨hJ, -, hN, hset, -⟩ := hdom g hg l hl hl1 hgl
  obtain ⟨g', rfl⟩ : ∃ g' : ModGL TwistTag.D4.tag F, g' = g := ⟨g, rfl⟩
  set J : Set (Fin TwistTag.D4.foldedTag.rank) :=
    (RootWeightDatum.fixed TwistTag.D4 σ hσ : RootWeightDatum F).face l
  change {x : ModGL TwistTag.D4.tag F | x ∈ graphFixedRootGroup TwistTag.D4 F σ.toRingHom ∧
      ∀ c : ℝ, (Fl c).map (x : Module.End F (RootModule TwistTag.D4.tag F)) = Fl c} =
    ((graphFixedParabolic TwistTag.D4 F σ.toRingHom J).map (MulAut.conj g').toMonoidHom :
      Set (ModGL TwistTag.D4.tag F)) at hset
  refine ⟨g', hg, J, hJ, fun x hx => ?_⟩
  have hmem := (Set.ext_iff.1 hset x).1 ⟨(Subgroup.mem_inf.1 hx).1, hN x hx⟩
  rw [SetLike.mem_coe, Subgroup.mem_map_equiv, MulAut.conj_symm_apply] at hmem
  exact hmem

variable {σ : F →+* F}

theorem exists_conj_torus_eq_mul (hσ : Function.Surjective σ) {b t : ModGL TwistTag.D4.tag F}
    (hb : b ∈ graphFixedRootBorel TwistTag.D4 F σ)
    (ht : t ∈ graphFixedRootTorus TwistTag.D4 F σ) :
    ∃ u ∈ graphFixedPosUnipotent TwistTag.D4 F σ, b * t * b⁻¹ = u * t := by
  have hb' : b ∈ (graphFixedRootBorel TwistTag.D4 F σ : Set (ModGL TwistTag.D4.tag F)) := hb
  rw [graphFixedRootBorel_eq_mul hσ] at hb'
  obtain ⟨s, hs, u, hu, rfl⟩ := hb'
  have hst : Commute s t := graphFixedRootTorus_mul_comm hs ht
  have htN := graphFixedRootTorus_le_normalizer_graphFixedPosUnipotent ht
  have hsN := graphFixedRootTorus_le_normalizer_graphFixedPosUnipotent hs
  refine ⟨s * (u * (t * u⁻¹ * t⁻¹)) * s⁻¹, ?_, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.1 hsN _).1
      (mul_mem hu ((Subgroup.mem_normalizer_iff.1 htN _).1 (inv_mem hu)))
  · have h1 : t * s⁻¹ = s⁻¹ * t := hst.inv_left.eq.symm
    calc s * u * t * (s * u)⁻¹ = s * u * (t * u⁻¹ * t⁻¹) * (t * s⁻¹) := by group
      _ = s * u * (t * u⁻¹ * t⁻¹) * (s⁻¹ * t) := by rw [h1]
      _ = s * (u * (t * u⁻¹ * t⁻¹)) * s⁻¹ * t := by group

theorem eq_one_of_mul_pow_two_pow [Finite F] (hF : Nat.card F = 64)
    {u z : ModGL TwistTag.D4.tag F} (hu : u ∈ graphFixedPosUnipotent TwistTag.D4 F σ)
    (hz : z ∈ graphFixedRootTorus TwistTag.D4 F σ) {k : ℕ} (h : (u * z) ^ (2 ^ k) = 1) :
    z = 1 := by
  obtain ⟨u', hu', e⟩ := exists_mul_pow_eq_mul_pow hu
    (graphFixedRootTorus_le_normalizer_graphFixedPosUnipotent hz) (2 ^ k)
  rw [h] at e
  have hz1 : z ^ (2 ^ k) = 1 := by
    have e' : z ^ (2 ^ k) * 1 = 1 * u'⁻¹ := by
      rw [mul_one, one_mul]
      exact eq_inv_of_mul_eq_one_right e.symm
    exact (graphFixedRoot_mul_unique (pow_mem hz _) (one_mem _) (one_mem _) (inv_mem hu') e').1
  have hzT : z ∈ torusGroup TwistTag.D4.tag F :=
    (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hz).1).1
  have hz63 : z ^ (Nat.card F - 1) = 1 :=
    pow_card_sub_one_eq_one_of_mem_diagonalGroup (torusGroup_le_diagonalGroup hzT)
  rw [hF] at hz63
  have h1 : orderOf z ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hz1
  have h2 : orderOf z ∣ 63 := orderOf_dvd_of_pow_eq_one hz63
  have h3 : orderOf z ∣ Nat.gcd (2 ^ k) 63 := Nat.dvd_gcd h1 h2
  have hg : Nat.gcd (2 ^ k) 63 = 1 := Nat.Coprime.pow_left k (by norm_num)
  rw [hg, Nat.dvd_one, orderOf_eq_one_iff] at h3
  exact h3

theorem four_pow_mod_three (n : ℕ) : (2 ^ 2) ^ n % 3 = 1 := by
  rw [Nat.pow_mod]
  norm_num

theorem not_three_dvd_index_graphFixedRootTorus [Finite F] (σ : F ≃+* F)
    (hF : Nat.card F = (2 ^ 2) ^ 3) (hσc : ∀ c, σ c = c ^ (2 ^ 2))
    (b : Fin TwistTag.D4.foldedTag.rank) :
    ¬ 3 ∣ ((graphFixedRootTorus TwistTag.D4 F σ.toRingHom).subgroupOf
      (graphFixedParabolic TwistTag.D4 F σ.toRingHom {b})).index := by
  have : Finite (ModGL TwistTag.D4.tag F) := finite_modGL
  have hσ : Function.Surjective σ.toRingHom := σ.surjective
  have hHP : graphFixedRootTorus TwistTag.D4 F σ.toRingHom ≤
      graphFixedParabolic TwistTag.D4 F σ.toRingHom {b} :=
    graphFixedRootTorus_le_graphFixedRootBorel.trans
      (graphFixedRootBorel_le_graphFixedParabolic _ _ _ {b})
  have hP := CFSG.Quasithin.F134.LieD4.card_graphFixedParabolic_singleton hσ b
  have hB := CFSG.Timmesfeld.ExceptionalOrders.card_graphFixedRootBorel
    (t := TwistTag.D4) (K := F) hσ
  have hq := CFSG.Timmesfeld.ExceptionalOrders.card_orbitField (t := TwistTag.D4) Nat.prime_two
    (by norm_num : 1 ≤ 2) hF (σ := σ.toRingHom) hσc
  have hU := CFSG.Timmesfeld.ExceptionalOrders.card_graphFixedPosUnipotent hσ hq
  have hR := CFSG.Quasithin.F134.LieD4.card_graphFixedInversionUnipotent_D4 σ (n := 2)
    (by norm_num) hF hσc b
  have hidx := Subgroup.index_mul_card ((graphFixedRootTorus TwistTag.D4 F σ.toRingHom).subgroupOf
    (graphFixedParabolic TwistTag.D4 F σ.toRingHom {b}))
  have hcard : Nat.card ((graphFixedRootTorus TwistTag.D4 F σ.toRingHom).subgroupOf
      (graphFixedParabolic TwistTag.D4 F σ.toRingHom {b})) =
        Nat.card (graphFixedRootTorus TwistTag.D4 F σ.toRingHom) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHP).toEquiv
  rw [hcard, hP, hB, hU, hR] at hidx
  set I := ((graphFixedRootTorus TwistTag.D4 F σ.toRingHom).subgroupOf
    (graphFixedParabolic TwistTag.D4 F σ.toRingHom {b})).index
  set h := Nat.card (graphFixedRootTorus TwistTag.D4 F σ.toRingHom)
  set N := {α : Fin TwistTag.D4.tag.rank → ℤ | IsRoot TwistTag.D4.tag α ∧ 0 < height α}.ncard
  set m := (TwistTag.D4.orbit b).card
  have hH0 : 0 < h := Nat.card_pos
  have hI : I = (2 ^ 2) ^ N * (1 + (2 ^ 2) ^ m) := by
    apply Nat.eq_of_mul_eq_mul_left hH0
    rw [mul_comm h I, hidx]
    ring
  rw [hI, Nat.dvd_iff_mod_eq_zero, Nat.mul_mod, four_pow_mod_three, Nat.add_mod,
    four_pow_mod_three]
  norm_num

theorem mem_of_card_eq_nine (σ : F ≃+* F)
    (e : (Fˣ × (trialityFixedField F σ.toRingHom)ˣ) ≃*
      graphFixedRootTorus TwistTag.D4 F σ.toRingHom)
    {E : Subgroup (ModGL TwistTag.D4.tag F)}
    (hEH : E ≤ graphFixedRootTorus TwistTag.D4 F σ.toRingHom) (hE9 : Nat.card E = 9)
    (hE3 : ∀ x ∈ E, x ^ 3 = 1) {a : Fˣ} {c : (trialityFixedField F σ.toRingHom)ˣ}
    (ha : a ^ 3 = 1) (hc : c ^ 3 = 1) : (e (a, c) : ModGL TwistTag.D4.tag F) ∈ E := by
  classical
  have key : ∀ x : E, (e.symm ⟨x, hEH x.2⟩) ^ 3 = 1 := by
    intro x
    rw [← map_pow]
    have : (⟨(x : ModGL TwistTag.D4.tag F), hEH x.2⟩ :
        graphFixedRootTorus TwistTag.D4 F σ.toRingHom) ^ 3 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hE3 x x.2)
    rw [this, map_one]
  let f : E → rootsOfUnity 3 F × rootsOfUnity 3 (trialityFixedField F σ.toRingHom) := fun x =>
    (⟨(e.symm ⟨x, hEH x.2⟩).1, (mem_rootsOfUnity 3 _).2 (by
        have := congrArg (MonoidHom.fst _ _) (key x)
        rwa [map_pow, map_one] at this)⟩,
      ⟨(e.symm ⟨x, hEH x.2⟩).2, (mem_rootsOfUnity 3 _).2 (by
        have := congrArg (MonoidHom.snd _ _) (key x)
        rwa [map_pow, map_one] at this)⟩)
  have hf : Function.Injective f := by
    intro x y hxy
    simp only [f, Prod.mk.injEq, Subtype.mk.injEq] at hxy
    have h1 : e.symm ⟨x, hEH x.2⟩ = e.symm ⟨y, hEH y.2⟩ := Prod.ext hxy.1 hxy.2
    have h2 := e.symm.injective h1
    have h3 := congrArg Subtype.val h2
    exact Subtype.ext h3
  have hcard : Nat.card (rootsOfUnity 3 F × rootsOfUnity 3 (trialityFixedField F σ.toRingHom)) ≤
      Nat.card E := by
    rw [Nat.card_prod, hE9]
    have h1 := card_rootsOfUnity F 3
    have h2 := card_rootsOfUnity (trialityFixedField F σ.toRingHom) 3
    calc _ ≤ 3 * 3 := Nat.mul_le_mul h1 h2
      _ = 9 := by norm_num
  obtain ⟨x, hx⟩ := (hf.bijective_of_nat_card_le hcard).2
    (⟨a, (mem_rootsOfUnity 3 _).2 ha⟩, ⟨c, (mem_rootsOfUnity 3 _).2 hc⟩)
  simp only [f, Prod.mk.injEq, Subtype.mk.injEq] at hx
  have h1 : e.symm ⟨x, hEH x.2⟩ = (a, c) := Prod.ext hx.1 hx.2
  have h2 : (⟨x, hEH x.2⟩ : graphFixedRootTorus TwistTag.D4 F σ.toRingHom) = e (a, c) := by
    rw [← h1, MulEquiv.apply_symm_apply]
  rw [← h2]
  exact x.2

theorem trialityMiddleTorus_one (σ : F ≃+* F) : trialityMiddleTorus F σ 1 = 1 := by
  rw [trialityMiddleTorus, map_one, torusElt_one]

theorem trialityOuterTorus_mem [Finite F] [CharP F 2] (σ : F ≃+* F) (hσ3 : σ ^ 3 = 1) (a : Fˣ) :
    trialityOuterTorus F σ a ∈ graphFixedRootTorus TwistTag.D4 F σ.toRingHom := by
  obtain ⟨-, ⟨e, he⟩, -⟩ := even_triality_faithful_torus_coordinates F σ hσ3
  have h := (e (a, 1)).2
  rw [he, trialityMiddleTorus_one, mul_one] at h
  exact h

theorem trialityNorm_eq_one (σ : F ≃+* F) (hσ3 : σ ^ 3 = 1) (hσc : ∀ c, σ c = c ^ (2 ^ 2))
    {a : Fˣ} (ha : a ^ 3 = 1) : trialityNorm σ hσ3 a = 1 := by
  have ha' : (a : F) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, ha, Units.val_one]
  have h1 := coe_trialityNorm hσ3 a
  rw [coe_trialityFixedUnit] at h1
  simp only [hσc] at h1
  have h2 : (a : F) * (a : F) ^ (2 ^ 2) * ((a : F) ^ (2 ^ 2)) ^ (2 ^ 2) = 1 := by
    calc (a : F) * (a : F) ^ (2 ^ 2) * ((a : F) ^ (2 ^ 2)) ^ (2 ^ 2) = ((a : F) ^ 3) ^ 7 := by
          ring
      _ = 1 := by rw [ha', one_pow]
  rw [h2] at h1
  exact Units.ext (Subtype.ext h1)

theorem conj_trialityOuterTorus_of_mem_relWeylTwist [Finite F] [CharP F 2] (σ : F ≃+* F)
    (hσ3 : σ ^ 3 = 1) (hσc : ∀ c, σ c = c ^ (2 ^ 2)) {w : WeylGroup TwistTag.D4.tag}
    (hw : w ∈ relWeylTwist TwistTag.D4) :
    ∀ a : Fˣ, a ^ 3 = 1 → ∃ a' : Fˣ, a' ^ 3 = 1 ∧
      canonicalRep (coxeterSystem TwistTag.D4.tag) F w * trialityOuterTorus F σ a *
        (canonicalRep (coxeterSystem TwistTag.D4.tag) F w)⁻¹ = trialityOuterTorus F σ a' := by
  obtain ⟨-, -, hoo, -, -, hmo⟩ := even_triality_faithful_torus_coordinates F σ hσ3
  have hcases : ∀ b : Fin TwistTag.D4.foldedTag.rank, b = ⟨0, by decide⟩ ∨ b = ⟨1, by decide⟩ := by
    decide
  have hgen : ∀ b : Fin TwistTag.D4.foldedTag.rank, ∀ a : Fˣ, a ^ 3 = 1 → ∃ a' : Fˣ, a' ^ 3 = 1 ∧
      canonicalRep (coxeterSystem TwistTag.D4.tag) F (TwistTag.D4.orbitReflection b) *
        trialityOuterTorus F σ a *
          (canonicalRep (coxeterSystem TwistTag.D4.tag) F (TwistTag.D4.orbitReflection b))⁻¹ =
        trialityOuterTorus F σ a' := by
    intro b a ha
    rcases hcases b with rfl | rfl
    · exact ⟨a⁻¹, by rw [inv_pow, ha, inv_one], hoo a⟩
    · refine ⟨a, ha, ?_⟩
      have h := hmo a
      rw [trialityNorm_eq_one σ hσ3 hσc ha, trialityMiddleTorus_one, mul_one] at h
      exact h
  rw [relWeylTwist_eq_closure TwistTag.D4] at hw
  induction hw using Subgroup.closure_induction'' with
  | mem x hx =>
    obtain ⟨b, rfl⟩ := hx
    exact hgen b
  | inv_mem x hx =>
    obtain ⟨b, rfl⟩ := hx
    rw [TwistTag.orbitReflection_inv]
    exact hgen b
  | one =>
    intro a ha
    exact ⟨a, ha, by rw [canonicalRep_one, one_mul, inv_one, mul_one]⟩
  | mul x y hx hy ihx ihy =>
    intro a ha
    have hx' : x ∈ relWeylTwist TwistTag.D4 := by rw [relWeylTwist_eq_closure]; exact hx
    have hy' : y ∈ relWeylTwist TwistTag.D4 := by rw [relWeylTwist_eq_closure]; exact hy
    obtain ⟨h, hh, hxy⟩ := exists_canonicalRep_mul_eq (K := F) (σ := σ.toRingHom) hx' hy'
    obtain ⟨a₁, ha₁, e₁⟩ := ihy a ha
    obtain ⟨a₂, ha₂, e₂⟩ := ihx a₁ ha₁
    refine ⟨a₂, ha₂, ?_⟩
    have hn : canonicalRep (coxeterSystem TwistTag.D4.tag) F (x * y) =
        canonicalRep (coxeterSystem TwistTag.D4.tag) F x *
          canonicalRep (coxeterSystem TwistTag.D4.tag) F y * h⁻¹ := by
      rw [hxy, mul_inv_cancel_right]
    have hc : h⁻¹ * trialityOuterTorus F σ a * h = trialityOuterTorus F σ a := by
      rw [mul_assoc, graphFixedRootTorus_mul_comm (trialityOuterTorus_mem σ hσ3 a) hh,
        inv_mul_cancel_left]
    rw [hn]
    calc canonicalRep (coxeterSystem TwistTag.D4.tag) F x *
          canonicalRep (coxeterSystem TwistTag.D4.tag) F y * h⁻¹ * trialityOuterTorus F σ a *
            (canonicalRep (coxeterSystem TwistTag.D4.tag) F x *
              canonicalRep (coxeterSystem TwistTag.D4.tag) F y * h⁻¹)⁻¹ =
        canonicalRep (coxeterSystem TwistTag.D4.tag) F x *
          (canonicalRep (coxeterSystem TwistTag.D4.tag) F y * (h⁻¹ * trialityOuterTorus F σ a * h) *
            (canonicalRep (coxeterSystem TwistTag.D4.tag) F y)⁻¹) *
          (canonicalRep (coxeterSystem TwistTag.D4.tag) F x)⁻¹ := by group
      _ = trialityOuterTorus F σ a₂ := by rw [hc, e₁, e₂]

theorem conj_trialityOuterTorus_of_mem [Finite F] [CharP F 2] (σ : F ≃+* F) (hσ3 : σ ^ 3 = 1)
    (hF : Nat.card F = 64) (hσc : ∀ c, σ c = c ^ (2 ^ 2)) {g : ModGL TwistTag.D4.tag F}
    (hg : g ∈ graphFixedRootGroup TwistTag.D4 F σ.toRingHom) {a : Fˣ} (ha : a ^ 3 = 1)
    (hH : g * trialityOuterTorus F σ a * g⁻¹ ∈ graphFixedRootTorus TwistTag.D4 F σ.toRingHom) :
    ∃ a' : Fˣ, a' ^ 3 = 1 ∧ g * trialityOuterTorus F σ a * g⁻¹ = trialityOuterTorus F σ a' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hσ : Function.Surjective σ.toRingHom := σ.surjective
  have hg' : g ∈ (graphFixedRootGroup TwistTag.D4 F σ.toRingHom :
      Set (ModGL TwistTag.D4.tag F)) := hg
  rw [graphFixedRootGroup_eq_iUnion hσ] at hg'
  obtain ⟨⟨w, hw⟩, hgw⟩ := Set.mem_iUnion.1 hg'
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := mem_graphFixedRootBruhatCell.1 hgw
  obtain ⟨a', ha', hconj⟩ := conj_trialityOuterTorus_of_mem_relWeylTwist σ hσ3 hσc hw a ha
  refine ⟨a', ha', ?_⟩
  set n := canonicalRep (coxeterSystem TwistTag.D4.tag) F w with hn
  set t := trialityOuterTorus F σ a with ht
  set t'' := trialityOuterTorus F σ a' with ht''
  have htH : t ∈ graphFixedRootTorus TwistTag.D4 F σ.toRingHom := trialityOuterTorus_mem σ hσ3 a
  have ht''H : t'' ∈ graphFixedRootTorus TwistTag.D4 F σ.toRingHom :=
    trialityOuterTorus_mem σ hσ3 a'
  generalize ht'def : b₁ * n * b₂ * t * (b₁ * n * b₂)⁻¹ = t' at hH ⊢
  obtain ⟨u₂, hu₂, e₂⟩ := exists_conj_torus_eq_mul hσ hb₂ htH
  obtain ⟨u₁, hu₁, e₁⟩ := exists_conj_torus_eq_mul hσ (inv_mem hb₁) hH
  rw [inv_inv] at e₁
  have h1 : b₁⁻¹ * t' * b₁ = n * (b₂ * t * b₂⁻¹) * n⁻¹ := by rw [← ht'def]; group
  rw [e₁, e₂] at h1
  have h2 : n * (u₂ * t) * n⁻¹ = (n * u₂ * n⁻¹) * t'' := by rw [← hconj]; group
  rw [h2] at h1
  have key : n * u₂ * n⁻¹ = u₁ * (t' * t''⁻¹) := by
    rw [← mul_assoc, h1, mul_inv_cancel_right]
  have hU2 : IsPGroup 2 (graphFixedPosUnipotent TwistTag.D4 F σ.toRingHom) :=
    (isPGroup_posUnipotent 2 TwistTag.D4.tag).to_le
      (inf_le_left : graphFixedPosUnipotent TwistTag.D4 F σ.toRingHom ≤ _)
  obtain ⟨k, hk⟩ := hU2 ⟨u₂, hu₂⟩
  have hk' : u₂ ^ (2 ^ k) = 1 := by
    have := congrArg Subtype.val hk
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
  have hpow : (u₁ * (t' * t''⁻¹)) ^ (2 ^ k) = 1 := by
    rw [← key, conj_pow, hk', mul_one, mul_inv_cancel]
  have hz := eq_one_of_mul_pow_two_pow hF hu₁ (mul_mem hH (inv_mem ht''H)) hpow
  exact mul_inv_eq_one.1 hz

theorem eq_bot_of_forall_conj [Finite F] (σ : F ≃+* F) (hF : Nat.card F = (2 ^ 2) ^ 3)
    (hσc : ∀ c, σ c = c ^ (2 ^ 2)) {D S : Subgroup (ModGL TwistTag.D4.tag F)}
    (hDC : D ≤ graphFixedRootGroup TwistTag.D4 F σ.toRingHom)
    (hSC : S ≤ graphFixedRootGroup TwistTag.D4 F σ.toRingHom)
    (hD9 : Nat.card D = 9) (hD3 : ∀ x ∈ D, x ^ 3 = 1)
    (hconj : ∀ x ∈ D, ∀ y ∈ D, x ≠ 1 → y ≠ 1 →
      ∃ g ∈ graphFixedRootGroup TwistTag.D4 F σ.toRingHom, g * x * g⁻¹ = y)
    (hS2 : IsPGroup 2 S) (hDS : D ≤ Subgroup.normalizer (S : Set (ModGL TwistTag.D4.tag F))) :
    S = ⊥ := by
  have : Finite (ModGL TwistTag.D4.tag F) := finite_modGL
  have : Fintype F := Fintype.ofFinite F
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hF64 : Nat.card F = 64 := by rw [hF]; norm_num
  have : CharP F 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (k := 6) (by norm_num) (by rw [hF]; norm_num)
  have hσ3 : σ ^ 3 = 1 := by
    refine RingEquiv.ext fun c => ?_
    change σ (σ (σ c)) = c
    have hc : c ^ 64 = c := by rw [← hF64, Nat.card_eq_fintype_card, FiniteField.pow_card]
    rw [hσc, hσc, hσc, ← pow_mul, ← pow_mul]
    norm_num
    exact hc
  set C := graphFixedRootGroup TwistTag.D4 F σ.toRingHom with hC
  by_contra hS
  obtain ⟨g, hg, J, hJ, hgJ⟩ := exists_normalizer_le_graphFixedParabolic σ hσ3 hSC hS2 hS
  have hcases : ∀ a : Fin TwistTag.D4.foldedTag.rank, a = ⟨0, by decide⟩ ∨ a = ⟨1, by decide⟩ := by
    decide
  obtain ⟨b, hJb⟩ : ∃ b : Fin TwistTag.D4.foldedTag.rank, J ⊆ {b} := by
    obtain ⟨a₀, ha₀⟩ : ∃ a, a ∉ J := by
      by_contra h
      push Not at h
      exact hJ (Set.eq_univ_of_forall h)
    rcases hcases a₀ with rfl | rfl
    · refine ⟨⟨1, by decide⟩, fun x hx => ?_⟩
      rcases hcases x with rfl | rfl
      · exact absurd hx ha₀
      · exact Set.mem_singleton _
    · refine ⟨⟨0, by decide⟩, fun x hx => ?_⟩
      rcases hcases x with rfl | rfl
      · exact Set.mem_singleton _
      · exact absurd hx ha₀
  have hPJ : graphFixedParabolic TwistTag.D4 F σ.toRingHom J ≤
      graphFixedParabolic TwistTag.D4 F σ.toRingHom {b} :=
    ((fixed_standard_parabolic_cells TwistTag.D4 F σ).2.2.2.1 J {b}).2 hJb
  have hPC : graphFixedParabolic TwistTag.D4 F σ.toRingHom {b} ≤ C :=
    graphFixedParabolic_le _ _ _ {b}
  set D' := D.map (MulAut.conj g⁻¹).toMonoidHom with hD'
  have hD'P : D' ≤ graphFixedParabolic TwistTag.D4 F σ.toRingHom {b} := by
    rintro _ ⟨d, hd, rfl⟩
    have h := hgJ d (Subgroup.mem_inf.2 ⟨hDC hd, hDS hd⟩)
    have e : (MulAut.conj g⁻¹).toMonoidHom d = g⁻¹ * d * g := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [e]
    exact hPJ h
  have hD'9 : Nat.card D' = 9 := by
    rw [hD', Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hD9]
  have hD'3 : IsPGroup 3 D' := IsPGroup.of_card (n := 2) (by rw [hD'9]; norm_num)
  obtain ⟨y, hyP, hyH⟩ := exists_conj_le_of_not_dvd_index hD'P hD'3
    (not_three_dvd_index_graphFixedRootTorus σ hF hσc b)
  set E := D'.map (MulAut.conj y).toMonoidHom with hE
  have hE9 : Nat.card E = 9 := by
    rw [hE, Subgroup.card_map_of_injective (MulAut.conj y).injective, hD'9]
  set c₀ := y * g⁻¹ with hc₀
  have hc₀C : c₀ ∈ C := mul_mem (hPC hyP) (inv_mem hg)
  have hmemE : ∀ x, x ∈ E ↔ ∃ d ∈ D, c₀ * d * c₀⁻¹ = x := by
    intro x
    constructor
    · rintro ⟨_, ⟨d, hd, rfl⟩, rfl⟩
      refine ⟨d, hd, ?_⟩
      simp only [hc₀, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    · rintro ⟨d, hd, rfl⟩
      refine ⟨_, ⟨d, hd, rfl⟩, ?_⟩
      simp only [hc₀, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  have hE3 : ∀ x ∈ E, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨d, hd, rfl⟩ := (hmemE x).1 hx
    rw [conj_pow, hD3 d hd, mul_one, mul_inv_cancel]
  obtain ⟨-, ⟨e, he⟩, -⟩ := even_triality_faithful_torus_coordinates F σ hσ3
  have hcardU : Nat.card Fˣ = 63 := by rw [Nat.card_units, hF64]
  obtain ⟨a₀, ha₀⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) 3
    (by rw [hcardU]; norm_num)
  have ha₀3 : a₀ ^ 3 = 1 := by rw [← ha₀]; exact pow_orderOf_eq_one a₀
  have ha₀1 : a₀ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ha₀
    norm_num at ha₀
  have ha₀3' : (a₀ : F) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, ha₀3, Units.val_one]
  have ha₀k : (a₀ : F) ∈ trialityFixedField F σ.toRingHom := by
    rw [mem_trialityFixedField]
    change σ (a₀ : F) = a₀
    rw [hσc]
    calc (a₀ : F) ^ (2 ^ 2) = (a₀ : F) ^ 3 * (a₀ : F) := by ring
      _ = (a₀ : F) := by rw [ha₀3', one_mul]
  set ω : (trialityFixedField F σ.toRingHom)ˣ := Units.mk0 ⟨a₀, ha₀k⟩
    (fun h => a₀.ne_zero (congrArg Subtype.val h)) with hω
  have hω3 : ω ^ 3 = 1 := by
    refine Units.ext (Subtype.ext ?_)
    simp only [hω, Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one, SubmonoidClass.mk_pow,
      OneMemClass.coe_one]
    exact ha₀3'
  have hω1 : ω ≠ 1 := by
    intro h
    apply ha₀1
    have := congrArg (fun u : (trialityFixedField F σ.toRingHom)ˣ =>
      ((u : trialityFixedField F σ.toRingHom) : F)) h
    simp only [hω, Units.val_mk0, Units.val_one, OneMemClass.coe_one] at this
    exact Units.ext this
  have hx₁E : (e (a₀, 1) : ModGL TwistTag.D4.tag F) ∈ E :=
    mem_of_card_eq_nine σ e hyH hE9 hE3 ha₀3 (one_pow 3)
  have hx₂E : (e (1, ω) : ModGL TwistTag.D4.tag F) ∈ E :=
    mem_of_card_eq_nine σ e hyH hE9 hE3 (one_pow 3) hω3
  have hx₁ : (e (a₀, 1) : ModGL TwistTag.D4.tag F) = trialityOuterTorus F σ a₀ := by
    rw [he, trialityMiddleTorus_one, mul_one]
  have hne : ∀ p, p ≠ 1 → (e p : ModGL TwistTag.D4.tag F) ≠ 1 := by
    intro p hp h
    apply hp
    apply e.injective
    rw [map_one]
    exact Subtype.ext h
  have hx₁1 : (e (a₀, 1) : ModGL TwistTag.D4.tag F) ≠ 1 :=
    hne _ fun h => ha₀1 (congrArg Prod.fst h)
  have hx₂1 : (e (1, ω) : ModGL TwistTag.D4.tag F) ≠ 1 :=
    hne _ fun h => hω1 (congrArg Prod.snd h)
  obtain ⟨d₁, hd₁, hd₁x⟩ := (hmemE _).1 hx₁E
  obtain ⟨d₂, hd₂, hd₂x⟩ := (hmemE _).1 hx₂E
  have hd₁1 : d₁ ≠ 1 := by
    rintro rfl
    apply hx₁1
    rw [← hd₁x]
    group
  have hd₂1 : d₂ ≠ 1 := by
    rintro rfl
    apply hx₂1
    rw [← hd₂x]
    group
  obtain ⟨g', hg'C, hg'⟩ := hconj d₁ hd₁ d₂ hd₂ hd₁1 hd₂1
  have hcC : c₀ * g' * c₀⁻¹ ∈ C := mul_mem (mul_mem hc₀C hg'C) (inv_mem hc₀C)
  have hcx : c₀ * g' * c₀⁻¹ * trialityOuterTorus F σ a₀ * (c₀ * g' * c₀⁻¹)⁻¹ =
      (e (1, ω) : ModGL TwistTag.D4.tag F) := by
    rw [← hx₁, ← hd₁x, ← hd₂x, ← hg']
    group
  have hH : c₀ * g' * c₀⁻¹ * trialityOuterTorus F σ a₀ * (c₀ * g' * c₀⁻¹)⁻¹ ∈
      graphFixedRootTorus TwistTag.D4 F σ.toRingHom := by
    rw [hcx]
    exact (e (1, ω)).2
  obtain ⟨a', -, ha'eq⟩ := conj_trialityOuterTorus_of_mem σ hσ3 hF64 hσc hcC ha₀3 hH
  rw [hcx] at ha'eq
  have h1 : e (1, ω) = e (a', 1) :=
    Subtype.ext (by rw [ha'eq, he, trialityMiddleTorus_one, mul_one])
  exact hω1 (congrArg Prod.snd (e.injective h1))

end Model

theorem inner3D44_holds :
    Input289b.Inner3D44 := by
  intro K _ _ hcat D J hDel hD9 hDJ hJ S hS2 hDS
  have hconjK := Input289b.conj_of_isLThreeFour hDel hD9 hDJ hJ
  obtain ⟨⟨x0, hv⟩, hd, ⟨e⟩⟩ := hcat
  obtain ⟨q, rfl, hqp, hq2⟩ := Input289b.is3D44_cases' hd
  have hmod := CFSG.TauCetiBridge.Even.twistedModel_of_bridgeEven
    CFSG.TauCetiBridge.Even.twistedBridgeEven_trialityD4 q hv hqp (by decide) e
  rw [hqp, hq2] at hmod
  obtain ⟨kf, _, _, σ, hkf, hσ, ⟨eC⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card .D4 Nat.prime_two (by norm_num) hmod
  have hkf' : Nat.card kf = (2 ^ 2) ^ 3 := hkf
  set C := graphFixedRootGroup TwistTag.D4 kf σ.toRingHom with hC
  set φ : K →* ModGL TwistTag.D4.tag kf := C.subtype.comp eC.toMonoidHom with hφ
  have hφinj : Function.Injective φ := Subtype.val_injective.comp eC.injective
  have hφC : ∀ k, φ k ∈ C := fun k => (eC k).2
  have hbot := eq_bot_of_forall_conj σ hkf' hσ (D := D.map φ) (S := S.map φ)
    (by rintro _ ⟨d, -, rfl⟩; exact hφC d)
    (by rintro _ ⟨s, -, rfl⟩; exact hφC s)
    (by rw [Subgroup.card_map_of_injective hφinj, hD9])
    (by rintro _ ⟨d, hd, rfl⟩; rw [← map_pow, hDel.2 d hd, map_one])
    (by
      rintro _ ⟨d₁, hd₁, rfl⟩ _ ⟨d₂, hd₂, rfl⟩ h1 h2
      have h1' : d₁ ≠ 1 := fun h => h1 (by rw [h, map_one])
      have h2' : d₂ ≠ 1 := fun h => h2 (by rw [h, map_one])
      obtain ⟨g, hg⟩ := hconjK d₁ hd₁ d₂ hd₂ h1' h2'
      exact ⟨φ g, hφC g, by rw [← map_inv, ← map_mul, ← map_mul, hg]⟩)
    (hS2.map φ)
    ((Subgroup.map_mono hDS).trans (Subgroup.le_normalizer_map φ))
  exact (Subgroup.map_eq_bot_iff_of_injective S hφinj).1 hbot

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Input289c
