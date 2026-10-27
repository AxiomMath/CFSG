module

public import CFSG.LieType.Chevalley.GraphFixedBorelCoreCenter
public import CFSG.LieType.Chevalley.GraphFixedMinimalBorel
public import CFSG.LieType.Chevalley.SylowOpposition

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley
open scoped Pointwise

theorem exists_mul_pow_eq_mul_pow {G : Type*} [Group G] {U : Subgroup G} {u h : G} (hu : u ∈ U)
    (hh : h ∈ Subgroup.normalizer (U : Set G)) (n : ℕ) : ∃ u' ∈ U, (u * h) ^ n = u' * h ^ n := by
  induction n with
  | zero => exact ⟨1, one_mem _, by rw [pow_zero, pow_zero, one_mul]⟩
  | succ n ih =>
    obtain ⟨u', hu', e⟩ := ih
    refine ⟨u' * (h ^ n * u * (h ^ n)⁻¹), mul_mem hu'
      ((Subgroup.mem_normalizer_iff.1 (pow_mem hh n) u).1 hu), ?_⟩
    rw [pow_succ (u * h) n, e]
    group

theorem mem_normalizer_of_mem_normalizer_subgroupOf {G : Type*} [Group G] {U C : Subgroup G}
    (hUC : U ≤ C) {x : C} (hx : x ∈ Subgroup.normalizer ((U.subgroupOf C : Subgroup C) : Set C)) :
    (x : G) ∈ Subgroup.normalizer (U : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro m
  by_cases hm : m ∈ C
  · exact (Subgroup.mem_normalizer_iff.1 hx) ⟨m, hm⟩
  · refine iff_of_false (fun h => hm (hUC h)) fun h => hm ?_
    have e : m = (x : G)⁻¹ * ((x : G) * m * (x : G)⁻¹) * (x : G) := by group
    rw [e]
    exact mul_mem (mul_mem (inv_mem x.2) (hUC h)) x.2

theorem not_dvd_index_of_forall_pow_mem {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {P : Subgroup G} (hP : IsPGroup p P) {m : ℕ} (hm : ¬ p ∣ m)
    (h : ∀ x ∈ Subgroup.normalizer (P : Set G), x ^ m ∈ P) : ¬ p ∣ P.index := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hP
  have hmod := Sylow.card_quotient_normalizer_modEq_card_quotient hn
  intro hdvd
  have h1 : p ∣ Nat.card (Subgroup.normalizer (P : Set G) ⧸
      P.subgroupOf (Subgroup.normalizer (P : Set G))) :=
    (Nat.ModEq.dvd_iff hmod dvd_rfl).2 hdvd
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' p h1
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  have hx : (x : Subgroup.normalizer (P : Set G) ⧸
      P.subgroupOf (Subgroup.normalizer (P : Set G))) ^ m = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact h _ x.2
  exact hm (hy ▸ orderOf_dvd_of_pow_eq_one hx)

section Finite

variable {K : Type} [Field K] [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]

theorem not_dvd_natCard_sub_one : ¬ p ∣ Nat.card K - 1 := fun h => by
  have h3 := Nat.dvd_sub (prime_dvd_card (K := K) p) h
  rw [Nat.sub_sub_self Nat.card_pos] at h3
  exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.1 h3)

omit [Fact p.Prime] in
theorem isPGroup_posUnipotent
    (τ : Tag) : IsPGroup p (posUnipotent τ K) := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hcard⟩ := FiniteField.card K p
  refine IsPGroup.of_card
    (n := (n : ℕ) * {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α}.ncard) ?_
  rw [card_posUnipotent, Nat.card_eq_fintype_card, hcard, ← pow_mul]

variable {t : TwistTag} {σ : K →+* K}

omit [Fact p.Prime] in
theorem isPGroup_graphFixedPosUnipotent_subgroupOf :
    IsPGroup p ((graphFixedPosUnipotent t K σ).subgroupOf (graphFixedRootGroup t K σ)) :=
  ((isPGroup_posUnipotent p t.tag).to_le
    (inf_le_left : graphFixedPosUnipotent t K σ ≤ _)).of_equiv
      (Subgroup.subgroupOfEquivOfLe (graphFixedPosUnipotent_le_graphFixedRootGroup t K σ)).symm

omit [CharP K p] in
theorem pow_card_sub_one_mem_graphFixedPosUnipotent
    (hσ : Function.Surjective σ)
    {b : ModGL t.tag K} (hb : b ∈ graphFixedRootBorel t K σ) :
    b ^ (Nat.card K - 1) ∈ graphFixedPosUnipotent t K σ := by
  have hb' : b ∈ (graphFixedRootBorel t K σ : Set (ModGL t.tag K)) := hb
  rw [graphFixedRootBorel_eq_mul' hσ] at hb'
  obtain ⟨u, hu, h, hh, rfl⟩ := hb'
  obtain ⟨u', hu', e⟩ := exists_mul_pow_eq_mul_pow hu
    (graphFixedRootTorus_le_normalizer_graphFixedPosUnipotent hh) (Nat.card K - 1)
  have hhT : h ∈ torusGroup t.tag K := (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hh).1).1
  rw [e, pow_card_sub_one_eq_one_of_mem_diagonalGroup (torusGroup_le_diagonalGroup hhT), mul_one]
  exact hu'

theorem not_dvd_index_graphFixedPosUnipotent
    (hσ : Function.Surjective σ) :
    ¬ p ∣ ((graphFixedPosUnipotent t K σ).subgroupOf (graphFixedRootGroup t K σ)).index := by
  have := finite_modGL (τ := t.tag) (K := K)
  have hUC := graphFixedPosUnipotent_le_graphFixedRootGroup t K σ
  refine not_dvd_index_of_forall_pow_mem (isPGroup_graphFixedPosUnipotent_subgroupOf p)
    (not_dvd_natCard_sub_one (K := K) p) fun x hx => ?_
  rw [Subgroup.mem_subgroupOf]
  have hxB : (x : ModGL t.tag K) ∈ graphFixedRootBorel t K σ := by
    rw [← graphFixedRootGroup_inf_normalizer_graphFixedPosUnipotent hσ]
    exact Subgroup.mem_inf.2 ⟨x.2, mem_normalizer_of_mem_normalizer_subgroupOf hUC hx⟩
  exact pow_card_sub_one_mem_graphFixedPosUnipotent hσ hxB

end Finite

variable {t : TwistTag} {K : Type} [Field K] {σ : K →+* K}

theorem graphFixedRootBorel_le_normalizer_graphFixedPosUnipotent :
    graphFixedRootBorel t K σ ≤
      Subgroup.normalizer (graphFixedPosUnipotent t K σ : Set (ModGL t.tag K)) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer graphFixedPosUnipotent_le_graphFixedRootBorel).1
    graphFixedPosUnipotent_subgroupOf_graphFixedRootBorel_normal

theorem graphFixedPosUnipotent_inf_graphFixedNegUnipotent :
    graphFixedPosUnipotent t K σ ⊓ graphFixedNegUnipotent t K σ = ⊥ :=
  eq_bot_iff.2 ((inf_le_inf_right _ graphFixedPosUnipotent_le_graphFixedRootBorel).trans
    graphFixedRootBorel_inf_graphFixedNegUnipotent.le)

theorem orbitX_one_ne_one
    (a : Fin t.foldedTag.rank) : (orbitX t K σ a 1 : ModGL t.tag K) ≠ 1 :=
  fun h => one_ne_zero (orbitX_injective σ a ((Subtype.ext h).trans (orbitX_zero t σ a).symm))

theorem graphFixedPosUnipotent_inf_map_conj_eq_bot_iff
    {w₀ : WeylGroup t.tag}
    (hw₀ : ∀ w, (coxeterSystem t.tag).length w ≤ (coxeterSystem t.tag).length w₀)
    {w : WeylGroup t.tag} (hw : w ∈ relWeylTwist t) {g : ModGL t.tag K}
    (hg : g ∈ graphFixedRootBruhatCell t K σ w) :
    graphFixedPosUnipotent t K σ ⊓
        (graphFixedPosUnipotent t K σ).map (MulAut.conj g).toMonoidHom = ⊥ ↔ w = w₀ := by
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_graphFixedRootBruhatCell.1 hg
  have hBN := graphFixedRootBorel_le_normalizer_graphFixedPosUnipotent (t := t) (K := K) (σ := σ)
  have hred : graphFixedPosUnipotent t K σ ⊓ (graphFixedPosUnipotent t K σ).map
      (MulAut.conj (b * canonicalRep (coxeterSystem t.tag) K w * b')).toMonoidHom =
      (graphFixedPosUnipotent t K σ ⊓ (graphFixedPosUnipotent t K σ).map
        (MulAut.conj (canonicalRep (coxeterSystem t.tag) K w)).toMonoidHom).map
          (MulAut.conj b).toMonoidHom := by
    rw [map_conj_mul, map_conj_mul, map_conj_eq_of_mem_normalizer (hBN hb'),
      Subgroup.map_inf_eq _ _ _ (MulAut.conj b).injective, map_conj_eq_of_mem_normalizer (hBN hb)]
  rw [hred, Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj b).injective]
  have h₀ := reversesSigns_of_forall_length_le hw₀
  constructor
  · intro hbot
    by_contra hne
    have hv : w₀ * w⁻¹ ∈ relWeylTwist t :=
      mul_mem (mem_relWeylTwist_of_forall_length_le hw₀) (inv_mem hw)
    have hv1 : w₀ * w⁻¹ ≠ 1 := fun h => hne (mul_inv_eq_one.1 h).symm
    obtain ⟨a, ha⟩ := exists_forall_height_smul_single_neg t hv hv1
    have hpos : ∀ i ∈ t.orbit a, 0 < height (w⁻¹ • (Pi.single i 1 : Fin t.tag.rank → ℤ)) :=
      fun i hi => by
        have h1 := ha i hi
        rw [mul_smul] at h1
        rcases IsRoot.height_pos_or_neg (IsRoot.smul (isRoot_single _ i) w⁻¹) with h | h
        · exact h
        · have := h₀.height_smul_pos (IsRoot.smul (isRoot_single _ i) w⁻¹) h
          omega
    have hn : canonicalRep (coxeterSystem t.tag) K w ∈ twistedFixedGroup t K σ :=
      canonicalRep_mem_twistedFixedGroup t K σ ((mem_relWeylTwist t).1 hw)
    have htrans : (rootSpan t.tag K ((fun α => w⁻¹ • α) '' simpleOrbitRoots t a) ⊓
        twistedFixedGroup t K σ).map
          (MulAut.conj (canonicalRep (coxeterSystem t.tag) K w)).toMonoidHom =
        rootSpan t.tag K (simpleOrbitRoots t a) ⊓ twistedFixedGroup t K σ := by
      rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj _).injective,
        (canonical_weyl_root_transport t.tag K).1 w _ ?_, Set.image_image,
        map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hn)]
      · simp only [smul_inv_smul, Set.image_id']
      · rintro _ ⟨_, ⟨i, -, rfl⟩, rfl⟩
        exact IsRoot.smul (isRoot_single _ i) _
    have hle : rootSpan t.tag K ((fun α => w⁻¹ • α) '' simpleOrbitRoots t a) ⊓
        twistedFixedGroup t K σ ≤ graphFixedPosUnipotent t K σ :=
      inf_le_inf_right _ (rootSpan_mono (by
        rintro _ ⟨_, ⟨i, hi, rfl⟩, rfl⟩
        exact ⟨IsRoot.smul (isRoot_single _ i) _, hpos i hi⟩))
    have hx : (orbitX t K σ a 1 : ModGL t.tag K) ∈ graphFixedPosUnipotent t K σ ⊓
        (graphFixedPosUnipotent t K σ).map
          (MulAut.conj (canonicalRep (coxeterSystem t.tag) K w)).toMonoidHom := by
      refine Subgroup.mem_inf.2 ⟨orbitX_mem_graphFixedPosUnipotent t σ a 1,
        Subgroup.map_mono hle ?_⟩
      rw [htrans]
      exact orbitX_mem t σ a 1
    rw [hbot, Subgroup.mem_bot] at hx
    exact orbitX_one_ne_one a hx
  · rintro rfl
    rw [map_conj_graphFixedPosUnipotent hw₀]
    exact graphFixedPosUnipotent_inf_graphFixedNegUnipotent

theorem exceptional_fixed_Sylow_opposition
    (t : TwistTag) (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] (σ : K ≃+* K) (w₀ : WeylGroup t.tag)
    (hw₀ : ∀ w, (coxeterSystem t.tag).length w ≤ (coxeterSystem t.tag).length w₀) :
    (∃ P : Sylow p (graphFixedRootGroup t K σ.toRingHom),
      (P : Subgroup (graphFixedRootGroup t K σ.toRingHom)) =
        (graphFixedPosUnipotent t K σ.toRingHom).subgroupOf
          (graphFixedRootGroup t K σ.toRingHom)) ∧
    (∃ P : Sylow p (graphFixedRootGroup t K σ.toRingHom),
      (P : Subgroup (graphFixedRootGroup t K σ.toRingHom)) =
        (graphFixedNegUnipotent t K σ.toRingHom).subgroupOf
          (graphFixedRootGroup t K σ.toRingHom)) ∧
    graphFixedPosUnipotent t K σ.toRingHom ⊓ graphFixedNegUnipotent t K σ.toRingHom = ⊥ ∧
    (∀ S : Sylow p (graphFixedRootGroup t K σ.toRingHom),
      (graphFixedPosUnipotent t K σ.toRingHom).subgroupOf
          (graphFixedRootGroup t K σ.toRingHom) ⊓ S = ⊥ ↔
        ∃ u ∈ (graphFixedPosUnipotent t K σ.toRingHom).subgroupOf
            (graphFixedRootGroup t K σ.toRingHom),
          (S : Subgroup (graphFixedRootGroup t K σ.toRingHom)) =
            ((graphFixedNegUnipotent t K σ.toRingHom).subgroupOf
              (graphFixedRootGroup t K σ.toRingHom)).map (MulAut.conj u).toMonoidHom) ∧
    (∀ w ∈ relWeylTwist t, ∀ g ∈ graphFixedRootBruhatCell t K σ.toRingHom w,
      graphFixedPosUnipotent t K σ.toRingHom ⊓
          (graphFixedPosUnipotent t K σ.toRingHom).map (MulAut.conj g).toMonoidHom = ⊥ ↔
        w = w₀) ∧
    ∀ α : MulAut (graphFixedRootGroup t K σ.toRingHom),
      ∃ (c : graphFixedRootGroup t K σ.toRingHom)
        (β : MulAut (graphFixedRootGroup t K σ.toRingHom)),
        ((graphFixedPosUnipotent t K σ.toRingHom).subgroupOf
            (graphFixedRootGroup t K σ.toRingHom)).map β.toMonoidHom =
          (graphFixedPosUnipotent t K σ.toRingHom).subgroupOf
            (graphFixedRootGroup t K σ.toRingHom) ∧
        ((graphFixedNegUnipotent t K σ.toRingHom).subgroupOf
            (graphFixedRootGroup t K σ.toRingHom)).map β.toMonoidHom =
          (graphFixedNegUnipotent t K σ.toRingHom).subgroupOf
            (graphFixedRootGroup t K σ.toRingHom) ∧
        α = MulAut.conj c * β := by
  have hσ : Function.Surjective σ.toRingHom := σ.surjective
  have := finite_modGL (τ := t.tag) (K := K)
  have hUC := graphFixedPosUnipotent_le_graphFixedRootGroup t K σ.toRingHom
  have hVC := graphFixedNegUnipotent_le_graphFixedRootGroup t K σ.toRingHom
  have hn₀ : canonicalRep (coxeterSystem t.tag) K w₀ ∈ graphFixedRootGroup t K σ.toRingHom :=
    canonicalRep_mem_graphFixedRootGroup (mem_relWeylTwist_of_forall_length_le hw₀)
  have hUp := isPGroup_graphFixedPosUnipotent_subgroupOf p (t := t) (σ := σ.toRingHom)
  have hUi := not_dvd_index_graphFixedPosUnipotent p (t := t) hσ
  have hPU := IsPGroup.toSylow_coe hUp hUi
  set PU : Sylow p (graphFixedRootGroup t K σ.toRingHom) := hUp.toSylow hUi
  set n₀ : graphFixedRootGroup t K σ.toRingHom := ⟨_, hn₀⟩ with hn₀def
  have hPV : ((n₀ • PU : Sylow p (graphFixedRootGroup t K σ.toRingHom)) :
      Subgroup (graphFixedRootGroup t K σ.toRingHom)) =
        (graphFixedNegUnipotent t K σ.toRingHom).subgroupOf
          (graphFixedRootGroup t K σ.toRingHom) := by
    rw [coe_smul_sylow_eq_map, hPU, map_conj_subgroupOf hUC, hn₀def,
      map_conj_graphFixedPosUnipotent hw₀]
  set PV : Sylow p (graphFixedRootGroup t K σ.toRingHom) := n₀ • PU
  set UC := (graphFixedPosUnipotent t K σ.toRingHom).subgroupOf
    (graphFixedRootGroup t K σ.toRingHom) with hUCdef
  set VC := (graphFixedNegUnipotent t K σ.toRingHom).subgroupOf
    (graphFixedRootGroup t K σ.toRingHom) with hVCdef
  have hUV : UC ⊓ VC = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    have h : (x : ModGL t.tag K) ∈
        graphFixedPosUnipotent t K σ.toRingHom ⊓ graphFixedNegUnipotent t K σ.toRingHom :=
      Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx).1, (Subgroup.mem_inf.1 hx).2⟩
    rw [graphFixedPosUnipotent_inf_graphFixedNegUnipotent, Subgroup.mem_bot] at h
    exact Subgroup.mem_bot.2 (Subtype.ext h)
  have hkey : ∀ S : Sylow p (graphFixedRootGroup t K σ.toRingHom), UC ⊓ S = ⊥ →
      ∃ u ∈ UC, (S : Subgroup (graphFixedRootGroup t K σ.toRingHom)) =
        VC.map (MulAut.conj u).toMonoidHom := by
    intro S hS
    obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (graphFixedRootGroup t K σ.toRingHom) PU S
    have hSc : (S : Subgroup (graphFixedRootGroup t K σ.toRingHom)) =
        UC.map (MulAut.conj c).toMonoidHom := by
      rw [← hc, coe_smul_sylow_eq_map, hPU]
    rw [hSc, map_conj_subgroupOf hUC] at hS ⊢
    have hamb : graphFixedPosUnipotent t K σ.toRingHom ⊓
        (graphFixedPosUnipotent t K σ.toRingHom).map
          (MulAut.conj (c : ModGL t.tag K)).toMonoidHom = ⊥ := by
      refine eq_bot_iff.2 fun x hx => ?_
      have hxC : x ∈ graphFixedRootGroup t K σ.toRingHom := hUC (Subgroup.mem_inf.1 hx).1
      have h : (⟨x, hxC⟩ : graphFixedRootGroup t K σ.toRingHom) ∈
          UC ⊓ ((graphFixedPosUnipotent t K σ.toRingHom).map
            (MulAut.conj (c : ModGL t.tag K)).toMonoidHom).subgroupOf
              (graphFixedRootGroup t K σ.toRingHom) :=
        Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx).1, (Subgroup.mem_inf.1 hx).2⟩
      rw [hS, Subgroup.mem_bot] at h
      exact Subgroup.mem_bot.2 (congrArg Subtype.val h)
    have hcell : (c : ModGL t.tag K) ∈
        ⋃ w : relWeylTwist t, graphFixedRootBruhatCell t K σ.toRingHom w := by
      rw [← graphFixedRootGroup_eq_iUnion hσ]
      exact c.2
    obtain ⟨⟨w, hw⟩, hcw⟩ := Set.mem_iUnion.1 hcell
    obtain rfl := (graphFixedPosUnipotent_inf_map_conj_eq_bot_iff hw₀ hw hcw).1 hamb
    obtain ⟨b, hb, b', hb', hbb⟩ := mem_graphFixedRootBruhatCell.1 hcw
    have hb'' : b ∈ (graphFixedPosUnipotent t K σ.toRingHom : Set (ModGL t.tag K)) *
        (graphFixedRootTorus t K σ.toRingHom : Set (ModGL t.tag K)) := by
      rw [← graphFixedRootBorel_eq_mul' hσ]
      exact hb
    obtain ⟨u, hu, h, hh, rfl⟩ := hb''
    have hmapc : (graphFixedPosUnipotent t K σ.toRingHom).map
        (MulAut.conj (c : ModGL t.tag K)).toMonoidHom =
          (graphFixedNegUnipotent t K σ.toRingHom).map (MulAut.conj u).toMonoidHom := by
      rw [← hbb, map_conj_mul, map_conj_mul, map_conj_eq_of_mem_normalizer
        (graphFixedRootBorel_le_normalizer_graphFixedPosUnipotent hb'),
        map_conj_graphFixedPosUnipotent hw₀, map_conj_mul, map_conj_eq_of_mem_normalizer
        (graphFixedRootTorus_le_normalizer_graphFixedNegUnipotent hh)]
    refine ⟨⟨u, hUC hu⟩, hu, ?_⟩
    rw [hmapc, map_conj_subgroupOf hVC]
  have hkey' : ∀ S : Sylow p (graphFixedRootGroup t K σ.toRingHom),
      (∃ u ∈ UC, (S : Subgroup (graphFixedRootGroup t K σ.toRingHom)) =
        VC.map (MulAut.conj u).toMonoidHom) → UC ⊓ S = ⊥ := by
    rintro S ⟨u, hu, hS⟩
    rw [hS, ← map_conj_self hu, ← Subgroup.map_inf_eq _ _ _ (MulAut.conj u).injective, hUV,
      Subgroup.map_bot]
  have hAut : ∀ α : MulAut (graphFixedRootGroup t K σ.toRingHom),
      ∃ (c : graphFixedRootGroup t K σ.toRingHom)
        (β : MulAut (graphFixedRootGroup t K σ.toRingHom)),
        UC.map β.toMonoidHom = UC ∧ VC.map β.toMonoidHom = VC ∧ α = MulAut.conj c * β := by
    intro α
    obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (graphFixedRootGroup t K σ.toRingHom) PU (α • PU)
    have hαU : UC.map α.toMonoidHom = UC.map (MulAut.conj c).toMonoidHom := by
      rw [← hPU, ← coe_mulAut_smul_sylow, ← coe_smul_sylow_eq_map, hc]
    set α₁ := (MulAut.conj c)⁻¹ * α with hα₁
    have hα₁U : UC.map α₁.toMonoidHom = UC := by
      rw [map_mulAut_mul, hαU, ← map_mulAut_mul, inv_mul_cancel, map_mulAut_one]
    have hS : UC ⊓ ((α₁ • PV : Sylow p (graphFixedRootGroup t K σ.toRingHom)) :
        Subgroup (graphFixedRootGroup t K σ.toRingHom)) = ⊥ := by
      rw [coe_mulAut_smul_sylow, hPV, ← hα₁U, ← Subgroup.map_inf_eq _ _ _ α₁.injective, hUV,
        Subgroup.map_bot]
    obtain ⟨u, hu, hu'⟩ := hkey _ hS
    rw [coe_mulAut_smul_sylow, hPV] at hu'
    refine ⟨c * u, (MulAut.conj u)⁻¹ * α₁, ?_, ?_, ?_⟩
    · rw [map_mulAut_mul, hα₁U, ← map_inv, map_conj_self (inv_mem hu)]
    · rw [map_mulAut_mul, hu', ← map_mulAut_mul, inv_mul_cancel, map_mulAut_one]
    · rw [hα₁, map_mul]
      group
  exact ⟨⟨PU, hPU⟩, ⟨PV, hPV⟩, graphFixedPosUnipotent_inf_graphFixedNegUnipotent,
    fun S => ⟨hkey S, hkey' S⟩,
    fun w hw g hg => graphFixedPosUnipotent_inf_map_conj_eq_bot_iff hw₀ hw hg, hAut⟩

end CFSG.LieType.Chevalley
