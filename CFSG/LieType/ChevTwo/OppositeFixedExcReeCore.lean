module

public import CFSG.LieType.ChevTwo.OppositeFixedExcTwisted
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogLargeReeNormalForm

public section

namespace CFSG.LieType.ChevTwo.Semi

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.EvenOddRadical CFSG.Open CFSG.LieType.BorelTits CFSG.LieType.Ree

@[expose] def reeAset : Option (Fin ReeTag.F4.fixedOrbitCount) → Set (Fin ReeTag.F4.tag.rank)
  | none => ∅
  | some j => ReeTag.F4.fixedOrbitSet j

theorem reeAset_perm (j : Option (Fin ReeTag.F4.fixedOrbitCount)) (i : Fin ReeTag.F4.tag.rank) :
    ReeTag.F4.perm i ∈ reeAset j ↔ i ∈ reeAset j := by
  rcases j with _ | j
  · simp [reeAset]
  · simp only [reeAset]
    rw [ReeTag.mem_fixedOrbitSet, ReeTag.mem_fixedOrbitSet, ReeTag.fixedOrbitIndex_perm]

theorem oppositeFixedAt_of_family_pred {K' : Type} [Group K'] [Finite K'] {ι : Type*}
    (QJ PJ : ι → Subgroup K') (hQJ2 : ∀ j, IsPGroup 2 (QJ j))
    (hPJ : ∀ j, PJ j ≤ Subgroup.normalizer ((QJ j : Subgroup K') : Set K'))
    (hstd : ∀ Q : Subgroup K', Q ≠ ⊥ → IsPGroup 2 Q → ∃ (g : K') (j : ι),
      (∀ x ∈ Subgroup.normalizer (Q : Set K'), g⁻¹ * x * g ∈ PJ j) ∧
        ∀ q ∈ Q, g⁻¹ * q * g ∈ QJ j)
    (Pr : Subgroup (MulAut K') → Prop)
    (hPr : ∀ (g : K') (R : Subgroup (MulAut K')), Pr R →
      Pr (R.map (MulAut.conj (MulAut.conj g⁻¹)).toMonoidHom))
    (hcore : ∀ (j : ι) (p : ℕ), p.Prime → p ≠ 2 → ∀ R : Subgroup (MulAut K'), IsPGroup p R →
      Pr R → (∀ α ∈ R, (QJ j).map α.toMonoidHom = QJ j) →
        Subgroup.normalizer ((QJ j : Subgroup K') : Set K') = PJ j →
          autCentralizer R ≤ PJ j → autCentralizer R ⊓ QJ j = ⊥) :
    ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ R : Subgroup (MulAut K'), IsPGroup p R → Pr R →
      ∀ Q : Subgroup K', OppositeFixedAt R Q := by
  intro p hp hp2 R hR hPrR Q hQ0 hQ2 hcore' hne hRQ hC
  obtain ⟨g, j, hN, hQ⟩ := hstd Q hQ0 hQ2
  obtain ⟨hQ', hNQ⟩ := std_position g hcore' (hQJ2 j) (hPJ j) hN hQ
  set γ : MulAut K' := MulAut.conj g⁻¹ with hγ
  set R' : Subgroup (MulAut K') := R.map (MulAut.conj γ).toMonoidHom with hR'
  have hR'p : IsPGroup p R' := hR.map _
  have hPrR' : Pr R' := hPr g R hPrR
  have hQmap : Q.map γ.toMonoidHom = QJ j := hQ'
  have hQR' : ∀ α' ∈ R', (QJ j).map α'.toMonoidHom = QJ j := by
    rintro _ ⟨α, hα, rfl⟩
    have e : ((MulAut.conj γ).toMonoidHom α).toMonoidHom.comp γ.toMonoidHom =
        γ.toMonoidHom.comp α.toMonoidHom := by
      ext x; simp [MulAut.conj_apply]
    rw [← hQmap, Subgroup.map_map, e, ← Subgroup.map_map, hRQ α hα]
  have hC' : autCentralizer R' ≤ PJ j := by
    intro x hx
    have hx' : γ⁻¹ x ∈ autCentralizer R := by
      intro α hα
      have h := hx ((MulAut.conj γ).toMonoidHom α) ⟨α, hα, rfl⟩
      have h2 : γ (α (γ⁻¹ x)) = x := by simpa [MulAut.conj_apply] using h
      calc α (γ⁻¹ x) = γ⁻¹ (γ (α (γ⁻¹ x))) := by simp
        _ = γ⁻¹ x := by rw [h2]
    have hN' : γ⁻¹ x ∈ Subgroup.normalizer (Q : Set K') := hC hx'
    have h3 : x ∈ Subgroup.normalizer ((Q.map γ.toMonoidHom : Subgroup K') : Set K') := by
      rw [← Subgroup.map_equiv_normalizer_eq Q γ]
      exact ⟨γ⁻¹ x, hN', by simp⟩
    rw [hQmap, hNQ] at h3
    exact h3
  have key := hcore j p hp hp2 R' hR'p hPrR' hQR' hNQ hC'
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨hzC, hzQ⟩ := Subgroup.mem_inf.1 hz
  have hz1 : γ z ∈ autCentralizer R' ⊓ QJ j := by
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rintro _ ⟨α, hα, rfl⟩
      have h := hzC α hα
      change (γ * α * γ⁻¹) (γ z) = γ z
      rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply, h]
    · rw [← hQmap]
      exact Subgroup.mem_map_of_mem _ hzQ
  rw [key] at hz1
  exact Subgroup.mem_bot.2 ((MulEquiv.map_eq_one_iff γ).1 (Subgroup.mem_bot.1 hz1))

section Cert


theorem ree_scale_pos (t : ReeTag) (i : Fin t.tag.rank) : 0 < t.scale i := by
  unfold ReeTag.scale
  split_ifs
  · cases t <;> decide
  · exact one_pos

theorem reeDualRoot_neg {t : ReeTag} {γ : Fin t.tag.rank → ℤ} (hγ : IsRoot t.tag γ) :
    t.dualRoot (-γ) = -t.dualRoot γ := by
  funext j
  have hdvd : t.quadForm γ ∣ 2 * t.dualMapInt γ j :=
    Int.dvd_of_emod_eq_zero ((ReeTag.rootDualityCheck_spec hγ).2.1 j)
  have h1 : t.dualMapInt (-γ) j = -t.dualMapInt γ j := by
    simp [ReeTag.dualMapInt]
  simp only [ReeTag.dualRoot, Pi.neg_apply, h1, ReeTag.quadForm_neg]
  rw [mul_neg, Int.neg_ediv_of_dvd hdvd]

theorem reeDualRoot_apply_eq_zero_iff (t : ReeTag) {γ : Fin t.tag.rank → ℤ}
    (hγ : IsRoot t.tag γ) (j : Fin t.tag.rank) :
    t.dualRoot γ j = 0 ↔ γ (t.perm.symm j) = 0 := by
  obtain ⟨c, hc⟩ := Int.dvd_of_emod_eq_zero ((ReeTag.rootDualityCheck_spec hγ).2.1 j)
  have hq := ReeTag.quadForm_ne_zero hγ
  have hs : (t.scale (t.perm.symm j) : ℤ) ≠ 0 := by
    have := ree_scale_pos t (t.perm.symm j)
    exact_mod_cast this.ne'
  have h2 : t.dualRoot γ j = c := by
    simp only [ReeTag.dualRoot]
    rw [hc, Int.mul_ediv_cancel_left _ hq]
  rw [h2]
  have h3 : 2 * t.dualMapInt γ j = t.quadForm γ * c := hc
  simp only [ReeTag.dualMapInt] at h3
  constructor
  · rintro rfl
    rw [mul_zero] at h3
    have h4 : (t.scale (t.perm.symm j) : ℤ) * γ (t.perm.symm j) = 0 := by linarith
    rcases mul_eq_zero.1 h4 with h | h
    · exact absurd h hs
    · exact h
  · intro h
    rw [h, mul_zero, mul_zero] at h3
    rcases mul_eq_zero.1 h3.symm with h' | h'
    · exact absurd h' hq
    · exact h'

theorem reeDualRoot_mem_radicalRoots {A : Set (Fin ReeTag.F4.tag.rank)}
    (hA : ∀ i, ReeTag.F4.perm i ∈ A ↔ i ∈ A) {γ : Fin ReeTag.F4.tag.rank → ℤ}
    (hγ : γ ∈ parabolicRadicalRoots ReeTag.F4.tag A) :
    ReeTag.F4.dualRoot γ ∈ parabolicRadicalRoots ReeTag.F4.tag A := by
  obtain ⟨hr, hpos, i, hi, hγi⟩ := mem_parabolicRadicalRoots_iff.1 hγ
  refine mem_parabolicRadicalRoots_iff.2 ⟨ReeTag.isRoot_dualRoot hr,
    (ReeTag.height_dualRoot_pos_iff hr).2 hpos, ReeTag.F4.perm i, fun h => hi ((hA i).1 h), ?_⟩
  rw [ne_eq, reeDualRoot_apply_eq_zero_iff ReeTag.F4 hr, Equiv.symm_apply_apply]
  exact hγi

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}

theorem reeAut_mem_rootSpan {S : Set (Fin ReeTag.F4.tag.rank → ℤ)}
    (hS : ∀ γ ∈ S, IsRoot ReeTag.F4.tag γ ∧ ReeTag.F4.dualRoot γ ∈ S)
    {x : ↥(adjointGroup ReeTag.F4.tag K)}
    (hx : (x : ModGL ReeTag.F4.tag K) ∈ rootSpan ReeTag.F4.tag K S) :
    ((ReeTag.F4.finiteReeAut K a x : ↥(adjointGroup ReeTag.F4.tag K)) : ModGL ReeTag.F4.tag K) ∈
      rootSpan ReeTag.F4.tag K S := by
  have h := ReeTag.map_finiteReeAut_rootSpan_le (t := ReeTag.F4) (K := K) (a := a) hS
  exact Subgroup.mem_subgroupOf.1 (h (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hx)))

theorem reeAut_mem_parabolicRadical {A : Set (Fin ReeTag.F4.tag.rank)}
    (hA : ∀ i, ReeTag.F4.perm i ∈ A ↔ i ∈ A) {x : ↥(adjointGroup ReeTag.F4.tag K)}
    (hx : (x : ModGL ReeTag.F4.tag K) ∈ parabolicRadical ReeTag.F4.tag K A) :
    ((ReeTag.F4.finiteReeAut K a x : ↥(adjointGroup ReeTag.F4.tag K)) : ModGL ReeTag.F4.tag K) ∈
      parabolicRadical ReeTag.F4.tag K A :=
  reeAut_mem_rootSpan (a := a) (S := parabolicRadicalRoots ReeTag.F4.tag A)
    (fun γ hγ => ⟨(mem_parabolicRadicalRoots_iff.1 hγ).1, reeDualRoot_mem_radicalRoots hA hγ⟩) hx

theorem reeAut_mem_oppRadical {A : Set (Fin ReeTag.F4.tag.rank)}
    (hA : ∀ i, ReeTag.F4.perm i ∈ A ↔ i ∈ A) {x : ↥(adjointGroup ReeTag.F4.tag K)}
    (hx : (x : ModGL ReeTag.F4.tag K) ∈ oppRadical ReeTag.F4.tag K A) :
    ((ReeTag.F4.finiteReeAut K a x : ↥(adjointGroup ReeTag.F4.tag K)) : ModGL ReeTag.F4.tag K) ∈
      oppRadical ReeTag.F4.tag K A :=
  reeAut_mem_rootSpan (a := a) (S := oppRadicalRoots ReeTag.F4.tag A)
    (fun γ hγ => ⟨isRoot_of_mem_oppRadicalRoots hγ, by
      show -(ReeTag.F4.dualRoot γ) ∈ parabolicRadicalRoots ReeTag.F4.tag A
      rw [← reeDualRoot_neg (isRoot_of_mem_oppRadicalRoots hγ)]
      exact reeDualRoot_mem_radicalRoots hA hγ⟩) hx

variable (K) in
@[expose] def leviGens (A : Set (Fin ReeTag.F4.tag.rank)) : Set (ModGL ReeTag.F4.tag K) :=
  Set.range (fun p : Fin ReeTag.F4.tag.rank × Kˣ => torusElt ReeTag.F4.tag K p.1 p.2) ∪
    {g | ∃ j ∈ A, ∃ c : K, g = xUnit ReeTag.F4.tag K j c ∨ g = yUnit ReeTag.F4.tag K j c}

theorem parabolicLevi_eq_closure (A : Set (Fin ReeTag.F4.tag.rank)) :
    parabolicLevi ReeTag.F4.tag K A = Subgroup.closure (leviGens K A) := by
  rw [leviGens, Subgroup.closure_union]
  rfl

theorem reeAut_mem_parabolicLevi {A : Set (Fin ReeTag.F4.tag.rank)}
    (hA : ∀ i, ReeTag.F4.perm i ∈ A ↔ i ∈ A) {x : ↥(adjointGroup ReeTag.F4.tag K)}
    (hx : (x : ModGL ReeTag.F4.tag K) ∈ parabolicLevi ReeTag.F4.tag K A) :
    ((ReeTag.F4.finiteReeAut K a x : ↥(adjointGroup ReeTag.F4.tag K)) : ModGL ReeTag.F4.tag K) ∈
      parabolicLevi ReeTag.F4.tag K A := by
  have hclG : Subgroup.closure (leviGens K A) ≤ adjointGroup ReeTag.F4.tag K := by
    rw [← parabolicLevi_eq_closure]
    exact parabolicLevi_le_adjointGroup _ K A
  have key : ∀ g, g ∈ Subgroup.closure (leviGens K A) →
      ∀ hgG : g ∈ adjointGroup ReeTag.F4.tag K,
      ((ReeTag.F4.finiteReeAut K a ⟨g, hgG⟩ : ↥(adjointGroup ReeTag.F4.tag K)) :
        ModGL ReeTag.F4.tag K) ∈ Subgroup.closure (leviGens K A) := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      intro hgG
      rcases hg with ⟨⟨i, u⟩, rfl⟩ | ⟨j, hj, c, rfl | rfl⟩
      · change ((ReeTag.F4.finiteReeAut K a (torusElement ReeTag.F4.tag K i u) :
          ↥(adjointGroup ReeTag.F4.tag K)) : ModGL ReeTag.F4.tag K) ∈ _
        rw [ReeTag.finiteReeAut_eq_reeAut, ReeTag.reeAut_torusElement]
        exact Subgroup.subset_closure
          (Or.inl ⟨(ReeTag.F4.perm i, u ^ ReeTag.F4.relationExponent a i), rfl⟩)
      · change ((ReeTag.F4.finiteReeAut K a (xElement j c) :
          ↥(adjointGroup ReeTag.F4.tag K)) : ModGL ReeTag.F4.tag K) ∈ _
        rw [ReeTag.finiteReeAut_xElement]
        exact Subgroup.subset_closure (Or.inr ⟨ReeTag.F4.perm j, (hA j).2 hj, _, Or.inl rfl⟩)
      · change ((ReeTag.F4.finiteReeAut K a (yElement j c) :
          ↥(adjointGroup ReeTag.F4.tag K)) : ModGL ReeTag.F4.tag K) ∈ _
        rw [ReeTag.finiteReeAut_yElement]
        exact Subgroup.subset_closure (Or.inr ⟨ReeTag.F4.perm j, (hA j).2 hj, _, Or.inr rfl⟩)
    | one =>
      intro hgG
      have e : (⟨1, hgG⟩ : ↥(adjointGroup ReeTag.F4.tag K)) = 1 := rfl
      rw [e, map_one, Subgroup.coe_one]
      exact one_mem _
    | mul g h hgc hhc ihg ihh =>
      intro hgG
      have hg' : g ∈ adjointGroup ReeTag.F4.tag K := hclG hgc
      have hh' : h ∈ adjointGroup ReeTag.F4.tag K := hclG hhc
      have e : (⟨g * h, hgG⟩ : ↥(adjointGroup ReeTag.F4.tag K)) = ⟨g, hg'⟩ * ⟨h, hh'⟩ := rfl
      rw [e, map_mul, Subgroup.coe_mul]
      exact mul_mem (ihg hg') (ihh hh')
    | inv g hgc ihg =>
      intro hgG
      have hg' : g ∈ adjointGroup ReeTag.F4.tag K := hclG hgc
      have e : (⟨g⁻¹, hgG⟩ : ↥(adjointGroup ReeTag.F4.tag K)) = (⟨g, hg'⟩)⁻¹ := rfl
      rw [e, map_inv, Subgroup.coe_inv]
      exact inv_mem (ihg hg')
  rw [parabolicLevi_eq_closure] at hx ⊢
  exact key _ hx x.2

theorem reeGamma_decomp {A : Set (Fin ReeTag.F4.tag.rank)}
    (hA : ∀ i, ReeTag.F4.perm i ∈ A ↔ i ∈ A) {g : ModGL ReeTag.F4.tag K}
    (hgP : g ∈ parabolicSubgroup ReeTag.F4.tag K A) (hgΓ : g ∈ ReeTag.F4.reeGamma K a) :
    ∃ q ∈ parabolicRadical ReeTag.F4.tag K A ⊓ ReeTag.F4.reeGamma K a,
      ∃ m ∈ parabolicLevi ReeTag.F4.tag K A ⊓ ReeTag.F4.reeGamma K a, q * m = g := by
  obtain ⟨hgG, hgF⟩ := ReeTag.mem_reeGamma.1 hgΓ
  obtain ⟨-, -, -, -, -, -, hdec, -⟩ := parabolic_root_radical_Levi_factors ReeTag.F4.tag K A
  obtain ⟨⟨q, m⟩, ⟨hq, hm, hqm⟩, huniq⟩ := hdec g hgP
  have hqm' : g = q * m := hqm
  have hqG : q ∈ adjointGroup ReeTag.F4.tag K := rootSpan_le_adjointGroup K _ hq
  have hmG : m ∈ adjointGroup ReeTag.F4.tag K := parabolicLevi_le_adjointGroup _ K A hm
  have hqmG : (⟨q, hqG⟩ : ↥(adjointGroup ReeTag.F4.tag K)) * ⟨m, hmG⟩ = ⟨g, hgG⟩ :=
    Subtype.ext hqm'.symm
  have hprod : ReeTag.F4.finiteReeAut K a ⟨q, hqG⟩ * ReeTag.F4.finiteReeAut K a ⟨m, hmG⟩ =
      ⟨g, hgG⟩ := by
    rw [← map_mul, hqmG, hgF]
  have hFq := reeAut_mem_parabolicRadical (a := a) hA (x := ⟨q, hqG⟩) hq
  have hFm := reeAut_mem_parabolicLevi (a := a) hA (x := ⟨m, hmG⟩) hm
  have hu := huniq ((ReeTag.F4.finiteReeAut K a ⟨q, hqG⟩ : ↥(adjointGroup ReeTag.F4.tag K)),
    (ReeTag.F4.finiteReeAut K a ⟨m, hmG⟩ : ↥(adjointGroup ReeTag.F4.tag K)))
    ⟨hFq, hFm, (congrArg Subtype.val hprod).symm⟩
  have h1 : ReeTag.F4.finiteReeAut K a ⟨q, hqG⟩ = ⟨q, hqG⟩ :=
    Subtype.ext (congrArg Prod.fst hu)
  have h2 : ReeTag.F4.finiteReeAut K a ⟨m, hmG⟩ = ⟨m, hmG⟩ :=
    Subtype.ext (congrArg Prod.snd hu)
  exact ⟨q, Subgroup.mem_inf.2 ⟨hq, ReeTag.mem_reeGamma.2 ⟨hqG, h1⟩⟩, m,
    Subgroup.mem_inf.2 ⟨hm, ReeTag.mem_reeGamma.2 ⟨hmG, h2⟩⟩, hqm'.symm⟩

theorem conjAct_reeAut_fix {s : GamL ReeTag.F4.tag K} (hs : s.left ∈ ReeTag.F4.reeGamma K a)
    {x : ↥(adjointGroup ReeTag.F4.tag K)}
    (hx : conjAct ReeTag.F4.tag K s (x : ModGL ReeTag.F4.tag K) = x) :
    conjAct ReeTag.F4.tag K s
      ((ReeTag.F4.finiteReeAut K a x : ↥(adjointGroup ReeTag.F4.tag K)) : ModGL ReeTag.F4.tag K) =
      ((ReeTag.F4.finiteReeAut K a x : ↥(adjointGroup ReeTag.F4.tag K)) : ModGL ReeTag.F4.tag K) := by
  obtain ⟨hsG, hsF⟩ := ReeTag.mem_reeGamma.1 hs
  have hcomm := ReeTag.finiteReeAut_frobeniusTwist (t := ReeTag.F4) (K := K) (a := a)
    (s.right : K →+* K) x
  have hxe : (⟨s.left, hsG⟩ : ↥(adjointGroup ReeTag.F4.tag K)) *
      frobeniusTwist ReeTag.F4.tag K (s.right : K →+* K) x * (⟨s.left, hsG⟩)⁻¹ = x := by
    refine Subtype.ext ?_
    have h := hx
    rw [conjAct_apply] at h
    exact h
  have h2 : (⟨s.left, hsG⟩ : ↥(adjointGroup ReeTag.F4.tag K)) *
      frobeniusTwist ReeTag.F4.tag K (s.right : K →+* K) (ReeTag.F4.finiteReeAut K a x) *
        (⟨s.left, hsG⟩)⁻¹ = ReeTag.F4.finiteReeAut K a x := by
    have h := congrArg (fun y => ReeTag.F4.finiteReeAut K a y) hxe
    simp only [map_mul, map_inv, hsF, hcomm] at h
    exact h
  rw [conjAct_apply]
  exact congrArg Subtype.val h2

variable (a) in
@[expose] def UniqueNormalFormRee (R : Subgroup (MulAut ↥(ReeTag.F4.reeGamma K a))) : Prop :=
  ∀ α ∈ R, ∃! gδ : ↥(ReeTag.F4.reeGamma K a) × RingAut K,
    ∀ h : ↥(ReeTag.F4.reeGamma K a),
      ((α h : ↥(ReeTag.F4.reeGamma K a)) : ModGL ReeTag.F4.tag K) =
        (gδ.1 : ModGL ReeTag.F4.tag K) *
          Units.map (entrywiseHom (gδ.2 : K →+* K)) (h : ModGL ReeTag.F4.tag K) *
            (gδ.1 : ModGL ReeTag.F4.tag K)⁻¹

theorem fieldAut_mem_reeGamma (σ : RingAut K) {g : ModGL ReeTag.F4.tag K}
    (hg : g ∈ ReeTag.F4.reeGamma K a) : fieldAutHom ReeTag.F4.tag K σ g ∈ ReeTag.F4.reeGamma K a :=
  ReeTag.exactEntrywiseAut_mem_reeGamma σ hg

section LiftRee

variable {R : Subgroup (MulAut ↥(ReeTag.F4.reeGamma K a))} (hNF : UniqueNormalFormRee a R)

@[expose] noncomputable def liftRee (α : ↥R) : GamL ReeTag.F4.tag K :=
  ⟨((hNF α.1 α.2).choose.1 : ModGL ReeTag.F4.tag K), (hNF α.1 α.2).choose.2⟩

theorem liftRee_left_mem (α : ↥R) : (liftRee hNF α).left ∈ ReeTag.F4.reeGamma K a :=
  (hNF α.1 α.2).choose.1.2

theorem liftRee_spec (α : ↥R) (h : ↥(ReeTag.F4.reeGamma K a)) :
    ((α.1 h : ↥(ReeTag.F4.reeGamma K a)) : ModGL ReeTag.F4.tag K) =
      conjAct ReeTag.F4.tag K (liftRee hNF α) (h : ModGL ReeTag.F4.tag K) := by
  rw [conjAct_apply]
  exact (hNF α.1 α.2).choose_spec.1 h

theorem liftRee_unique (α : ↥R) (g : GamL ReeTag.F4.tag K)
    (hg : g.left ∈ ReeTag.F4.reeGamma K a)
    (hspec : ∀ h : ↥(ReeTag.F4.reeGamma K a),
      ((α.1 h : ↥(ReeTag.F4.reeGamma K a)) : ModGL ReeTag.F4.tag K) =
        conjAct ReeTag.F4.tag K g (h : ModGL ReeTag.F4.tag K)) :
    liftRee hNF α = g := by
  have h : (hNF α.1 α.2).choose = ((⟨g.left, hg⟩ : ↥(ReeTag.F4.reeGamma K a)), g.right) :=
    (hNF α.1 α.2).unique (hNF α.1 α.2).choose_spec.1 (fun h => by
      rw [hspec h, conjAct_apply])
  refine SemidirectProduct.ext ?_ ?_
  · exact congrArg (fun p : ↥(ReeTag.F4.reeGamma K a) × RingAut K =>
      (p.1 : ModGL ReeTag.F4.tag K)) h
  · exact congrArg (fun p : ↥(ReeTag.F4.reeGamma K a) × RingAut K => p.2) h

theorem liftRee_one : liftRee hNF 1 = 1 :=
  liftRee_unique hNF 1 1 (one_mem _) fun h => by
    rw [Subgroup.coe_one, map_one, MulAut.one_apply]
    rfl

theorem liftRee_mul (α β : ↥R) : liftRee hNF (α * β) = liftRee hNF α * liftRee hNF β := by
  refine liftRee_unique hNF _ _ ?_ fun h => ?_
  · change (liftRee hNF α).left *
      fieldAutHom ReeTag.F4.tag K (liftRee hNF α).right (liftRee hNF β).left ∈ _
    exact mul_mem (liftRee_left_mem hNF α)
      (fieldAut_mem_reeGamma _ (liftRee_left_mem hNF β))
  · rw [Subgroup.coe_mul, MulAut.mul_apply, liftRee_spec hNF α, liftRee_spec hNF β, map_mul,
      MulAut.mul_apply]

@[expose] noncomputable def liftHomRee : ↥R →* GamL ReeTag.F4.tag K where
  toFun := liftRee hNF
  map_one' := liftRee_one hNF
  map_mul' := liftRee_mul hNF

theorem liftHomRee_injective : Function.Injective (liftHomRee hNF) := fun α β h => by
  refine Subtype.ext (MulEquiv.ext fun x => Subtype.ext ?_)
  rw [liftRee_spec hNF α, liftRee_spec hNF β]
  exact congrArg (fun s => conjAct ReeTag.F4.tag K s (x : ModGL ReeTag.F4.tag K)) h

end LiftRee

theorem autCentralizer_inf_radRee_eq_bot (hK : Nat.card K = 2 ^ (2 * a + 1))
    (hDual : ∀ {A : Set (Fin Tag.F4.rank)} {S : Subgroup (GamL Tag.F4 K)},
      (∀ s ∈ S, s.left ∈ adjointGroup Tag.F4 K ∧ s.left ∈ parabolicLevi Tag.F4 K A) →
        Odd (Nat.card S) → ∀ {u : ModGL Tag.F4 K}, u ∈ parabolicRadical Tag.F4 K A → u ≠ 1 →
          (∀ s ∈ S, conjAct Tag.F4 K s u = u) →
            ∃ v ∈ oppRadical Tag.F4 K A, v ≠ 1 ∧ ∀ s ∈ S, conjAct Tag.F4 K s v = v)
    {A : Set (Fin ReeTag.F4.tag.rank)} (hA : ∀ i, ReeTag.F4.perm i ∈ A ↔ i ∈ A)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {R : Subgroup (MulAut ↥(ReeTag.F4.reeGamma K a))} (hR : IsPGroup p R)
    (hNF : UniqueNormalFormRee a R)
    (hQR : ∀ α ∈ R, ((parabolicRadical ReeTag.F4.tag K A).subgroupOf
        (ReeTag.F4.reeGamma K a)).map α.toMonoidHom =
      (parabolicRadical ReeTag.F4.tag K A).subgroupOf (ReeTag.F4.reeGamma K a))
    (hNQ : Subgroup.normalizer (((parabolicRadical ReeTag.F4.tag K A).subgroupOf
        (ReeTag.F4.reeGamma K a) : Subgroup ↥(ReeTag.F4.reeGamma K a)) :
          Set ↥(ReeTag.F4.reeGamma K a)) =
      (parabolicSubgroup ReeTag.F4.tag K A).subgroupOf (ReeTag.F4.reeGamma K a))
    (hC : autCentralizer R ≤
      (parabolicSubgroup ReeTag.F4.tag K A).subgroupOf (ReeTag.F4.reeGamma K a)) :
    autCentralizer R ⊓ (parabolicRadical ReeTag.F4.tag K A).subgroupOf
      (ReeTag.F4.reeGamma K a) = ⊥ := by
  classical
  have hfinM : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  haveI hK2 : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  have : Fact p.Prime := ⟨hp⟩
  by_contra hne
  obtain ⟨⟨w₁, hw⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  obtain ⟨hwC, hwQ⟩ := Subgroup.mem_inf.1 hw
  have hw1' : (w₁ : ModGL ReeTag.F4.tag K) ≠ 1 := fun h => hw1 (Subtype.ext (Subtype.ext h))
  obtain ⟨hQAP, -, -, -, hQM, -, -, -⟩ := parabolic_root_radical_Levi_factors ReeTag.F4.tag K A
  have hΓG : ReeTag.F4.reeGamma K a ≤ adjointGroup ReeTag.F4.tag K :=
    fun g hg => (ReeTag.mem_reeGamma.1 hg).1
  set T : Subgroup (GamL ReeTag.F4.tag K) := (liftHomRee hNF).range with hT
  have hTcard : Nat.card T = Nat.card R :=
    (Nat.card_congr (MonoidHom.ofInjective (liftHomRee_injective hNF)).toEquiv).symm
  have hRodd : Nat.card R % 2 = 1 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hR
    rw [hk]
    exact Nat.odd_iff.1 ((hp.eq_two_or_odd'.resolve_left hp2).pow)
  have hTodd : ¬ 2 ∣ Nat.card T := by
    rw [hTcard]; exact Nat.two_dvd_ne_zero.2 hRodd
  have hTP : ∀ s ∈ T, s.left ∈ parabolicSubgroup ReeTag.F4.tag K A ⊓ ReeTag.F4.reeGamma K a := by
    rintro _ ⟨α, rfl⟩
    have hs := liftRee_left_mem hNF α
    have hmem := left_mem_normalizer (Cg := ReeTag.F4.reeGamma K a)
      (Qg := parabolicRadical ReeTag.F4.tag K A) (fun σ h hh => fieldAut_mem_reeGamma σ hh)
      (fun σ h hh => fieldAut_mem_parabolicRadical σ hh) (hQR α.1 α.2) hs (liftRee_spec hNF α)
    rw [hNQ] at hmem
    exact Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.1 hmem, hs⟩
  obtain ⟨y₀, hy₀, hyM⟩ := exists_conj_into_complement
    (parabolicSubgroup ReeTag.F4.tag K A ⊓ ReeTag.F4.reeGamma K a)
    (parabolicRadical ReeTag.F4.tag K A ⊓ ReeTag.F4.reeGamma K a)
    (parabolicLevi ReeTag.F4.tag K A ⊓ ReeTag.F4.reeGamma K a)
    ((isPGroup_posUnipotent 2 ReeTag.F4.tag).to_le
      (inf_le_left.trans (parabolicRadical_le_posUnipotent A)))
    (fun x hx => Subgroup.mem_inf.2 ⟨hQAP (Subgroup.mem_inf.1 hx).1, (Subgroup.mem_inf.1 hx).2⟩)
    (fun x hx y hy => Subgroup.mem_inf.2 ⟨
      (Subgroup.mem_normalizer_iff.1 (parabolicSubgroup_le_normalizer_parabolicRadical A
        (Subgroup.mem_inf.1 hx).1) y).1 (Subgroup.mem_inf.1 hy).1,
      mul_mem (mul_mem (Subgroup.mem_inf.1 hx).2 (Subgroup.mem_inf.1 hy).2)
        (inv_mem (Subgroup.mem_inf.1 hx).2)⟩)
    (fun σ h hh => Subgroup.mem_inf.2 ⟨fieldAut_mem_parabolicSubgroup σ (Subgroup.mem_inf.1 hh).1,
      fieldAut_mem_reeGamma σ (Subgroup.mem_inf.1 hh).2⟩)
    (fun σ h hh => Subgroup.mem_inf.2 ⟨fieldAut_mem_parabolicLevi σ (Subgroup.mem_inf.1 hh).1,
      fieldAut_mem_reeGamma σ (Subgroup.mem_inf.1 hh).2⟩)
    (fun σ h hh => Subgroup.mem_inf.2 ⟨fieldAut_mem_parabolicRadical σ (Subgroup.mem_inf.1 hh).1,
      fieldAut_mem_reeGamma σ (Subgroup.mem_inf.1 hh).2⟩)
    (le_bot_iff.1 ((inf_le_inf inf_le_left inf_le_left).trans hQM.le))
    (fun g hg => reeGamma_decomp hA (Subgroup.mem_inf.1 hg).1 (Subgroup.mem_inf.1 hg).2)
    hTP hTodd
  set y : GamL ReeTag.F4.tag K := SemidirectProduct.inl y₀ with hy
  set S : Subgroup (GamL ReeTag.F4.tag K) := T.map (MulAut.conj y).toMonoidHom with hS
  have hSM : ∀ s ∈ S, s.left ∈ parabolicLevi ReeTag.F4.tag K A ⊓ ReeTag.F4.reeGamma K a := by
    rintro _ ⟨s, hs, rfl⟩
    exact hyM s hs
  have hSodd : Odd (Nat.card S) := by
    rw [hS, Subgroup.card_map_of_injective (MulAut.conj y).injective, hTcard]
    exact Nat.odd_iff.2 hRodd
  have hconjy : ∀ g : ModGL ReeTag.F4.tag K, conjAct _ K y g = y₀ * g * y₀⁻¹ := fun g => by
    rw [hy, conjAct_inl, MulAut.conj_apply]
  have hconjyinv : ∀ g : ModGL ReeTag.F4.tag K, conjAct _ K y⁻¹ g = y₀⁻¹ * g * y₀ := fun g => by
    rw [map_inv, hy, conjAct_inl, ← map_inv, MulAut.conj_apply, inv_inv]
  have hu : (w₁ : ModGL ReeTag.F4.tag K) ∈ parabolicRadical ReeTag.F4.tag K A :=
    Subgroup.mem_subgroupOf.1 hwQ
  have hy₀A : y₀ ∈ parabolicRadical ReeTag.F4.tag K A := (Subgroup.mem_inf.1 hy₀).1
  have hy₀P : y₀ ∈ parabolicSubgroup ReeTag.F4.tag K A := hQAP hy₀A
  have hu' : y₀ * (w₁ : ModGL ReeTag.F4.tag K) * y₀⁻¹ ∈ parabolicRadical ReeTag.F4.tag K A :=
    mul_mem (mul_mem hy₀A hu) (inv_mem hy₀A)
  have hu'1 : y₀ * (w₁ : ModGL ReeTag.F4.tag K) * y₀⁻¹ ≠ 1 := fun h => hw1' (by
    have := congrArg (fun z => y₀⁻¹ * z * y₀) h
    simpa [mul_assoc] using this)
  have hfixT : ∀ s ∈ T, conjAct ReeTag.F4.tag K s (w₁ : ModGL ReeTag.F4.tag K) = w₁ := by
    rintro _ ⟨α, rfl⟩
    change conjAct _ K (liftRee hNF α) _ = _
    rw [← liftRee_spec hNF α, hwC α.1 α.2]
  have hfix : ∀ s ∈ S, conjAct ReeTag.F4.tag K s
      (y₀ * (w₁ : ModGL ReeTag.F4.tag K) * y₀⁻¹) = y₀ * (w₁ : ModGL ReeTag.F4.tag K) * y₀⁻¹ := by
    rintro _ ⟨s, hs, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have h1 : conjAct _ K y⁻¹ (y₀ * (w₁ : ModGL ReeTag.F4.tag K) * y₀⁻¹) = w₁ := by
      rw [hconjyinv]; group
    rw [conjAct_conj, h1, hfixT s hs, hconjy]
  obtain ⟨v, hvQ, hv1, hvfix⟩ := hDual (A := A) (S := S)
    (fun s hs => ⟨hΓG (Subgroup.mem_inf.1 (hSM s hs)).2, (Subgroup.mem_inf.1 (hSM s hs)).1⟩)
    hSodd hu' hu'1 hfix
  have hvG : v ∈ adjointGroup ReeTag.F4.tag K := rootSpan_le_adjointGroup K _ hvQ
  set X : Subgroup (ModGL ReeTag.F4.tag K) :=
    oppRadical ReeTag.F4.tag K A ⊓ fixSub S with hX
  have hX2 : IsPGroup 2 X :=
    (isPGroup_negUnipotent (K := K) ReeTag.F4.tag).to_le
      (inf_le_left.trans (oppRadical_le_negUnipotent A))
  have hX2' : IsPGroup 2 (X.subgroupOf (adjointGroup ReeTag.F4.tag K)) := hX2.comap_subtype
  have hXne : X.subgroupOf (adjointGroup ReeTag.F4.tag K) ≠ ⊥ := by
    intro h
    have hmem : (⟨v, hvG⟩ : ↥(adjointGroup ReeTag.F4.tag K)) ∈
        X.subgroupOf (adjointGroup ReeTag.F4.tag K) :=
      Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨hvQ, hvfix⟩)
    rw [h, Subgroup.mem_bot] at hmem
    exact hv1 (congrArg Subtype.val hmem)
  have hf : ∀ x ∈ X.subgroupOf (adjointGroup ReeTag.F4.tag K),
      (ReeTag.F4.finiteReeAut K a).toMonoidHom x ∈
        X.subgroupOf (adjointGroup ReeTag.F4.tag K) := by
    intro x hx
    obtain ⟨hxQ, hxS⟩ := Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hx)
    refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨reeAut_mem_oppRadical (a := a) hA hxQ,
      fun s hs => ?_⟩)
    exact conjAct_reeAut_fix (a := a) (Subgroup.mem_inf.1 (hSM s hs)).2 (hxS s hs)
  have hff : ∀ x ∈ X.subgroupOf (adjointGroup ReeTag.F4.tag K),
      (ReeTag.F4.finiteReeAut K a).toMonoidHom ((ReeTag.F4.finiteReeAut K a).toMonoidHom x) = x := by
    intro x _
    have h := ReeTag.finiteReeAut_mul_self (t := ReeTag.F4) (K := K) (a := a) hK
    exact congrArg (fun m : MulAut ↥(adjointGroup ReeTag.F4.tag K) => m x) h
  obtain ⟨w, hwX, hw1'', hwF⟩ := exists_fixed_ne_one (X := X.subgroupOf (adjointGroup
    ReeTag.F4.tag K)) hX2' hXne (ReeTag.F4.finiteReeAut K a).toMonoidHom hf hff
  obtain ⟨hwQ', hwS⟩ := Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hwX)
  have hwΓ : (w : ModGL ReeTag.F4.tag K) ∈ ReeTag.F4.reeGamma K a :=
    ReeTag.mem_reeGamma.2 ⟨w.2, hwF⟩
  have hw1''' : (w : ModGL ReeTag.F4.tag K) ≠ 1 := fun h => hw1'' (Subtype.ext h)
  have hy₀Γ : y₀ ∈ ReeTag.F4.reeGamma K a := (Subgroup.mem_inf.1 hy₀).2
  have hwC' : y₀⁻¹ * (w : ModGL ReeTag.F4.tag K) * y₀ ∈ ReeTag.F4.reeGamma K a :=
    mul_mem (mul_mem (inv_mem hy₀Γ) hwΓ) hy₀Γ
  have hwfix : ∀ s ∈ T, conjAct ReeTag.F4.tag K s (y₀⁻¹ * (w : ModGL ReeTag.F4.tag K) * y₀) =
      y₀⁻¹ * (w : ModGL ReeTag.F4.tag K) * y₀ := by
    intro s hs
    have h := hwS _ (Subgroup.mem_map_of_mem (MulAut.conj y).toMonoidHom hs)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
    rw [conjAct_conj, hconjyinv, hconjy] at h
    calc conjAct ReeTag.F4.tag K s (y₀⁻¹ * (w : ModGL ReeTag.F4.tag K) * y₀) =
        y₀⁻¹ * (y₀ * conjAct ReeTag.F4.tag K s (y₀⁻¹ * (w : ModGL ReeTag.F4.tag K) * y₀) *
          y₀⁻¹) * y₀ := by group
      _ = y₀⁻¹ * (w : ModGL ReeTag.F4.tag K) * y₀ := by rw [h]
  have hwcent : (⟨y₀⁻¹ * (w : ModGL ReeTag.F4.tag K) * y₀, hwC'⟩ :
      ↥(ReeTag.F4.reeGamma K a)) ∈ autCentralizer R := by
    intro α hα
    refine Subtype.ext ?_
    rw [liftRee_spec hNF ⟨α, hα⟩]
    exact hwfix _ ⟨⟨α, hα⟩, rfl⟩
  have hwP : y₀⁻¹ * (w : ModGL ReeTag.F4.tag K) * y₀ ∈ parabolicSubgroup ReeTag.F4.tag K A :=
    Subgroup.mem_subgroupOf.1 (hC hwcent)
  have hvP : (w : ModGL ReeTag.F4.tag K) ∈ parabolicSubgroup ReeTag.F4.tag K A := by
    have e : (w : ModGL ReeTag.F4.tag K) =
        y₀ * (y₀⁻¹ * (w : ModGL ReeTag.F4.tag K) * y₀) * y₀⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem hy₀P hwP) (inv_mem hy₀P)
  have h0 := Subgroup.mem_inf.2 ⟨hvP, hwQ'⟩
  rw [parabolicSubgroup_inf_oppRadical] at h0
  exact hw1''' (Subgroup.mem_bot.1 h0)

theorem oppositeFixedAt_reeGamma (hK : Nat.card K = 2 ^ (2 * a + 1))
    (hDual : ∀ {A : Set (Fin Tag.F4.rank)} {S : Subgroup (GamL Tag.F4 K)},
      (∀ s ∈ S, s.left ∈ adjointGroup Tag.F4 K ∧ s.left ∈ parabolicLevi Tag.F4 K A) →
        Odd (Nat.card S) → ∀ {u : ModGL Tag.F4 K}, u ∈ parabolicRadical Tag.F4 K A → u ≠ 1 →
          (∀ s ∈ S, conjAct Tag.F4 K s u = u) →
            ∃ v ∈ oppRadical Tag.F4 K A, v ≠ 1 ∧ ∀ s ∈ S, conjAct Tag.F4 K s v = v)
    {ι : Type} (A : ι → Set (Fin Tag.F4.rank)) (hA : ∀ j i, ReeTag.F4.perm i ∈ A j ↔ i ∈ A j)
    (hstd : ∀ Q : Subgroup ↥(ReeTag.F4.reeGamma K a), Q ≠ ⊥ → IsPGroup 2 Q →
      ∃ (g : ↥(ReeTag.F4.reeGamma K a)) (j : ι),
        (∀ x ∈ Subgroup.normalizer (Q : Set ↥(ReeTag.F4.reeGamma K a)),
          g⁻¹ * x * g ∈ (parabolicSubgroup Tag.F4 K (A j)).subgroupOf (ReeTag.F4.reeGamma K a)) ∧
        ∀ q ∈ Q, g⁻¹ * q * g ∈
          (parabolicRadical Tag.F4 K (A j)).subgroupOf (ReeTag.F4.reeGamma K a))
    (Pr : Subgroup (MulAut ↥(ReeTag.F4.reeGamma K a)) → Prop)
    (hPr : ∀ (g : ↥(ReeTag.F4.reeGamma K a)) (R : Subgroup (MulAut ↥(ReeTag.F4.reeGamma K a))),
      Pr R → Pr (R.map (MulAut.conj (MulAut.conj g⁻¹)).toMonoidHom))
    (hNF : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ R : Subgroup (MulAut ↥(ReeTag.F4.reeGamma K a)),
      IsPGroup p R → Pr R → UniqueNormalFormRee a R) :
    ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ R : Subgroup (MulAut ↥(ReeTag.F4.reeGamma K a)),
      IsPGroup p R → Pr R → ∀ Q : Subgroup ↥(ReeTag.F4.reeGamma K a), OppositeFixedAt R Q := by
  classical
  haveI hfinM : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  haveI hK2 : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  refine oppositeFixedAt_of_family_pred
    (fun j => (parabolicRadical ReeTag.F4.tag K (A j)).subgroupOf (ReeTag.F4.reeGamma K a))
    (fun j => (parabolicSubgroup ReeTag.F4.tag K (A j)).subgroupOf (ReeTag.F4.reeGamma K a))
    (fun j => ?_) (fun j => ?_) hstd Pr hPr (fun j p hp hp2 R hR hPrR hQR hNQ hC => ?_)
  · have h2 : IsPGroup 2 (parabolicRadical ReeTag.F4.tag K (A j)) :=
      (isPGroup_posUnipotent (K := K) 2 ReeTag.F4.tag).to_le
        (parabolicRadical_le_posUnipotent (A j))
    exact h2.comap_subtype
  · intro x hx
    have hx0 : (x : ModGL ReeTag.F4.tag K) ∈ parabolicSubgroup ReeTag.F4.tag K (A j) := hx
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hx' := parabolicSubgroup_le_normalizer_parabolicRadical (A j) hx0
    simp only [Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.1 hx' _
  · exact autCentralizer_inf_radRee_eq_bot hK hDual (A := A j) (hA j) hp hp2 hR
      (hNF p hp hp2 R hR hPrR) hQR hNQ hC

theorem oppositeFixed_reeGamma_of_normalForm (hK : Nat.card K = 2 ^ (2 * a + 1))
    (hDual : ∀ {A : Set (Fin Tag.F4.rank)} {S : Subgroup (GamL Tag.F4 K)},
      (∀ s ∈ S, s.left ∈ adjointGroup Tag.F4 K ∧ s.left ∈ parabolicLevi Tag.F4 K A) →
        Odd (Nat.card S) → ∀ {u : ModGL Tag.F4 K}, u ∈ parabolicRadical Tag.F4 K A → u ≠ 1 →
          (∀ s ∈ S, conjAct Tag.F4 K s u = u) →
            ∃ v ∈ oppRadical Tag.F4 K A, v ≠ 1 ∧ ∀ s ∈ S, conjAct Tag.F4 K s v = v)
    (hstd : ∀ Q : Subgroup ↥(ReeTag.F4.reeGamma K a), Q ≠ ⊥ → IsPGroup 2 Q →
      ∃ (g : ↥(ReeTag.F4.reeGamma K a)) (j : Option (Fin ReeTag.F4.fixedOrbitCount)),
        (∀ x ∈ Subgroup.normalizer (Q : Set ↥(ReeTag.F4.reeGamma K a)),
          g⁻¹ * x * g ∈
            (parabolicSubgroup Tag.F4 K (reeAset j)).subgroupOf (ReeTag.F4.reeGamma K a)) ∧
        ∀ q ∈ Q, g⁻¹ * q * g ∈
          (parabolicRadical Tag.F4 K (reeAset j)).subgroupOf (ReeTag.F4.reeGamma K a))
    (hNF : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ R : Subgroup (MulAut ↥(ReeTag.F4.reeGamma K a)),
      IsPGroup p R → UniqueNormalFormRee a R) :
    OppositeFixed ↥(ReeTag.F4.reeGamma K a) :=
  fun p hp hp2 R hR Q => oppositeFixedAt_reeGamma hK hDual reeAset reeAset_perm hstd (fun _ => True)
    (fun _ _ _ => trivial) (fun p hp hp2 R hR _ => hNF p hp hp2 R hR) p hp hp2 R hR trivial Q

theorem uniqueNormalFormRee_of_large (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (R : Subgroup (MulAut ↥(ReeTag.F4.reeGamma K a))) : UniqueNormalFormRee a R := by
  obtain ⟨-, hNF, -⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.large_Ree_full_inner_field_automorphism_normal_form
      a ha K hK
  intro α _
  obtain ⟨⟨x, β⟩, hα, huniq⟩ := hNF α
  refine ⟨(x, β), fun h => ?_, fun p hp => huniq p (MulEquiv.ext fun h => Subtype.ext ?_)⟩
  · rw [hα]
    rfl
  · rw [hp h]
    rfl

theorem oppositeFixed_reeGamma (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (hDual : ∀ {A : Set (Fin Tag.F4.rank)} {S : Subgroup (GamL Tag.F4 K)},
      (∀ s ∈ S, s.left ∈ adjointGroup Tag.F4 K ∧ s.left ∈ parabolicLevi Tag.F4 K A) →
        Odd (Nat.card S) → ∀ {u : ModGL Tag.F4 K}, u ∈ parabolicRadical Tag.F4 K A → u ≠ 1 →
          (∀ s ∈ S, conjAct Tag.F4 K s u = u) →
            ∃ v ∈ oppRadical Tag.F4 K A, v ≠ 1 ∧ ∀ s ∈ S, conjAct Tag.F4 K s v = v)
    (hstd : ∀ Q : Subgroup ↥(ReeTag.F4.reeGamma K a), Q ≠ ⊥ → IsPGroup 2 Q →
      ∃ (g : ↥(ReeTag.F4.reeGamma K a)) (j : Option (Fin ReeTag.F4.fixedOrbitCount)),
        (∀ x ∈ Subgroup.normalizer (Q : Set ↥(ReeTag.F4.reeGamma K a)),
          g⁻¹ * x * g ∈
            (parabolicSubgroup Tag.F4 K (reeAset j)).subgroupOf (ReeTag.F4.reeGamma K a)) ∧
        ∀ q ∈ Q, g⁻¹ * q * g ∈
          (parabolicRadical Tag.F4 K (reeAset j)).subgroupOf (ReeTag.F4.reeGamma K a)) :
    OppositeFixed ↥(ReeTag.F4.reeGamma K a) :=
  oppositeFixed_reeGamma_of_normalForm hK hDual hstd
    (fun _ _ _ R _ => uniqueNormalFormRee_of_large ha hK R)

end Cert

end CFSG.LieType.ChevTwo.Semi
