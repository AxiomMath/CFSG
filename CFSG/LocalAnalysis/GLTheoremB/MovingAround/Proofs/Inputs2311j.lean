module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2311g2
public import CFSG.LieType.SeitzGeneration.ExcHigh.E7SevenWeyl
public import CFSG.LieType.SeitzGeneration.ExcHigh.E7FrameDatum
public import CFSG.LieType.SeitzGeneration.ExcHigh.E7SplitTorus
public import CFSG.LieType.SeitzGeneration.ExcHigh.E7TorusFrame
public import CFSG.LieType.SeitzGeneration.ExcHigh.TwE6FiveMain
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2311i

public section

open scoped MatrixGroups

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311j

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.ExcHigh TauCeti CFSG.Open
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311c (UniPlaneGen UniSeitzPlanes)

section Unipotent

theorem exists_pow_char_eq_one_of_mem_unipotent
    {τ : Tag} {K : Type} [Field K] [Finite K] {ℓ : ℕ} [CharP K ℓ] {G : Subgroup (ModGL τ K)} (y : G)
    (hy : (y : ModGL τ K) ∈ posUnipotent τ K ∨ (y : ModGL τ K) ∈ negUnipotent τ K) :
    ∃ m : ℕ, y ^ (ℓ ^ m) = 1 := by
  obtain ⟨-, hP, -, hN⟩ := (CFSG.Blueprint.Chevalley.positive_root_triangularity.{0, 0} τ).2 K ℓ
  rcases hy with h | h
  · obtain ⟨m, hm⟩ := hP ⟨_, h⟩
    exact ⟨m, Subtype.ext (by simpa using congrArg Subtype.val hm)⟩
  · obtain ⟨m, hm⟩ := hN ⟨_, h⟩
    exact ⟨m, Subtype.ext (by simpa using congrArg Subtype.val hm)⟩

theorem two_ne_zero_of_charP_odd {k : Type} [Field k] {ℓ : ℕ} [CharP k ℓ] (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) :
    (2 : k) ≠ 0 := by
  intro h
  have h2 : ((2 : ℕ) : k) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff k ℓ] at h2
  have hle := Nat.le_of_dvd (by norm_num) h2
  have := hℓ.two_le
  omega

end Unipotent

section TwE6ThreeFour

open CFSG.HardMathSupport.Lang.AnisoE6 CFSG.RankThree.E6

set_option linter.unusedSectionVars false


variable {k K : Type} [Field k] [Finite k] [Field K] [Finite K] [Algebra k K]

theorem twE6ThreeUniNative_odd (σ : K ≃+* K) {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (hk : Nat.card k = ℓ ^ f) (hK : Nat.card K = (ℓ ^ f) ^ 2) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ}
    [hpF : Fact p.Prime] (hp5 : 5 ≤ p) (he : orderOf (((ℓ ^ f : ℕ)) : ZMod p) = 3)
    (E₀ : Subgroup ↥(twistedE6RootGroup K σ)) (hE₀p : ∀ x ∈ E₀, x ^ p = 1)
    (hE₀c : Nat.card E₀ = p ^ 2) :
    Subgroup.closure {k | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x ∧ ∃ m : ℕ, k ^ (ℓ ^ m) = 1} = ⊤ := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hp : p.Prime := hpF.out
  haveI : CharP K ℓ := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    hℓ (k := 2 * f) (by omega) (by rw [hK, ← pow_mul, mul_comm])
  haveI : CharP k ℓ := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    hℓ (k := f) hf hk
  have hfix : ∀ c : k, σ (algebraMap k K c) = algebraMap k K c := by
    intro c
    rw [hσ, ← hk, ← map_pow]
    congr 1
    haveI : Fintype k := Fintype.ofFinite k
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.pow_card c
  have hp' : p ∣ Nat.card k ^ 2 + Nat.card k + 1 := by
    rw [hk]
    exact CFSG.HardMathSupport.Lang.AnisoE6.dvd_sq_add_add_one_of_orderOf_eq_three hp he
  have hTG : SylowTorus (twistedE6RootGroup K σ) p 2 :=
    sylowTorus_twistedE6_three hℓ hf K hK σ hσ hp he
  have hTΓ : SylowTorus (twistedFixedGroup TwistTag.E6 k (RingHom.id k)) p 2 :=
    (sylowTorus_F4_three k hp (by omega) hp').of_mulEquiv (e6FixedF4EquivAll k).symm
  have hinj := phiG_injective σ hfix
  obtain ⟨e, ⟨γ, hγ, rfl⟩, heord, hecomm⟩ := exists_e1 (K := K) (algebraMap k K) hp'
  set γΓ : twistedFixedGroup TwistTag.E6 k (RingHom.id k) := ⟨γ, hγ⟩ with hγΓ
  have hordγ : orderOf γΓ = p := by
    rw [← Subgroup.orderOf_coe, show (γΓ : ModGL TwistTag.E6.tag k) = γ from rfl,
      ← orderOf_injective (baseChangeGL (algebraMap k K)) (baseChangeGL_injective _) γ]
    exact heord
  obtain ⟨EΓ, hEΓ, hEΓc, hγE⟩ := exists_plane_containing_of_sylowTorus hTΓ hordγ
  set ι := phiG σ hfix with hιdef
  set EH : Subgroup (twistedE6RootGroup K σ) := EΓ.map ι with hEHdef
  have hEH : IsElemAbelian p EH :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hEΓ ι
  have hEHc : Nat.card EH = p ^ 2 := by
    rw [hEHdef, Subgroup.card_map_of_injective hinj, hEΓc]
  obtain ⟨g, hg⟩ := exists_conj_eq_of_sylowTorus hTG
    (Inputs2311i.isElemAbelian_of_exponent_card_sq hE₀p hE₀c) hE₀c hEH hEHc
  have hk3 : 3 ≤ Nat.card k := by
    rw [hk]
    have h3 : 3 ≤ ℓ := by
      have := hℓ.two_le
      omega
    calc 3 ≤ ℓ := h3
      _ = ℓ ^ 1 := (pow_one ℓ).symm
      _ ≤ ℓ ^ f := Nat.pow_le_pow_right hℓ.pos hf
  have hclΓ : Subgroup.closure {x : twistedFixedGroup TwistTag.E6 k (RingHom.id k) |
      ∃ y ∈ EΓ, y ≠ 1 ∧ Commute x y ∧ ∃ m : ℕ, x ^ (ℓ ^ m) = 1} = ⊤ := by
    refine Inputs2311i.uniClosure_eq_top_of_mulEquiv (e6FixedF4EquivAll k) ?_
    have hF₁p : ∀ x ∈ EΓ.map (e6FixedF4EquivAll k).toMonoidHom, x ^ p = 1 := by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hEΓ.2 x hx, map_one]
    have hF₁c : Nat.card (EΓ.map (e6FixedF4EquivAll k).toMonoidHom) = p ^ 2 := by
      rw [Subgroup.card_map_of_injective (f := (e6FixedF4EquivAll k).toMonoidHom)
        (e6FixedF4EquivAll k).injective, hEΓc]
    have h := Inputs2311g.f4Phi3UniNative k hk3 hp hp5 (by rw [hk]; exact he) _ hF₁p hF₁c
    rw [ringChar.eq k ℓ] at h
    exact h
  set M := Subgroup.closure {x : twistedE6RootGroup K σ | ∃ y ∈ EH, y ≠ 1 ∧ Commute x y ∧
    ∃ m : ℕ, x ^ (ℓ ^ m) = 1} with hM
  have hH : ∀ x, ι x ∈ M := by
    intro x
    have hx : x ∈ Subgroup.closure {x : twistedFixedGroup TwistTag.E6 k (RingHom.id k) |
        ∃ y ∈ EΓ, y ≠ 1 ∧ Commute x y ∧ ∃ m : ℕ, x ^ (ℓ ^ m) = 1} := by
      rw [hclΓ]
      exact Subgroup.mem_top x
    have hle : (Subgroup.closure {x : twistedFixedGroup TwistTag.E6 k (RingHom.id k) |
        ∃ y ∈ EΓ, y ≠ 1 ∧ Commute x y ∧ ∃ m : ℕ, x ^ (ℓ ^ m) = 1}).map ι ≤ M := by
      rw [MonoidHom.map_closure]
      refine Subgroup.closure_mono ?_
      rintro _ ⟨z, ⟨y, hy, hy1, hzy, m, hm⟩, rfl⟩
      exact ⟨ι y, ⟨y, hy, rfl⟩, fun h => hy1 (hinj (h.trans (map_one _).symm)), hzy.map ι, m,
        by rw [← map_pow, hm, map_one]⟩
    exact hle ⟨x, hx, rfl⟩
  set eG : twistedE6RootGroup K σ := ι γΓ with heGdef
  have heG : eG ∈ EH := ⟨γΓ, hγE, rfl⟩
  have heG1 : eG ≠ 1 := by
    intro h
    have h1 : orderOf eG = p := by
      rw [heGdef, orderOf_injective ι hinj γΓ, hordγ]
    rw [h, orderOf_one] at h1
    exact hp.one_lt.ne h1
  have hcomm : ∀ i, (i = e6Index 0 ∨ i = e6Index 2 ∨ i = e6Index 4 ∨ i = e6Index 5) →
      ∀ d : K, Commute (eG : ModGL TwistTag.E6.tag K) (xUnit Tag.E6 K i d) ∧
        Commute (eG : ModGL TwistTag.E6.tag K) (yUnit Tag.E6 K i d) :=
    hecomm
  have hgen : ∀ y : twistedE6RootGroup K σ,
      Commute (y : ModGL TwistTag.E6.tag K) (eG : ModGL TwistTag.E6.tag K) →
        (∃ m : ℕ, y ^ (ℓ ^ m) = 1) → y ∈ M :=
    fun y hy hy2 => Subgroup.subset_closure ⟨eG, heG, heG1, Subtype.ext hy.eq, hy2⟩
  have hsub : ∀ x : twistedE6RootGroup K σ, x ∈ M →
      (x : ModGL TwistTag.E6.tag K) ∈ M.map (twistedE6RootGroup K σ).subtype :=
    fun x hx => ⟨x, hx, rfl⟩
  have hmemX : ∀ (a : Fin TwistTag.E6.foldedTag.rank)
      (c : orbitField TwistTag.E6 K σ.toRingHom a),
      (orbitX TwistTag.E6 K σ.toRingHom a c : ModGL TwistTag.E6.tag K) ∈
        M.map (twistedE6RootGroup K σ).subtype ∧
      (orbitY TwistTag.E6 K σ.toRingHom a c : ModGL TwistTag.E6.tag K) ∈
        M.map (twistedE6RootGroup K σ).subtype := by
    intro a c
    have hXG : (orbitX TwistTag.E6 K σ.toRingHom a c : ModGL TwistTag.E6.tag K) ∈
        twistedE6RootGroup K σ :=
      graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
        (orbitX_mem_graphFixedPosUnipotent _ _ _ _)
    have hYG : (orbitY TwistTag.E6 K σ.toRingHom a c : ModGL TwistTag.E6.tag K) ∈
        twistedE6RootGroup K σ :=
      graphFixedNegUnipotent_le_graphFixedRootGroup _ _ _
        (orbitY_mem_graphFixedNegUnipotent _ _ _ _)
    have hX2 := exists_pow_char_eq_one_of_mem_unipotent (ℓ := ℓ) (G := twistedE6RootGroup K σ) ⟨_, hXG⟩
      (Or.inl (Subgroup.mem_inf.1 (orbitX_mem_graphFixedPosUnipotent _ σ.toRingHom a c)).1)
    have hY2 := exists_pow_char_eq_one_of_mem_unipotent (ℓ := ℓ) (G := twistedE6RootGroup K σ) ⟨_, hYG⟩
      (Or.inr (Subgroup.mem_inf.1 (orbitY_mem_graphFixedNegUnipotent _ σ.toRingHom a c)).1)
    obtain ⟨a, ha⟩ := a
    have ha4 : a < 4 := ha
    interval_cases a
    · have h := commute_orbitXY_short σ.toRingHom (e := (eG : ModGL TwistTag.E6.tag K)) hcomm
        ⟨0, ha⟩ (Or.inl rfl) c
      exact ⟨hsub ⟨_, hXG⟩ (hgen ⟨_, hXG⟩ h.1.symm hX2),
        hsub ⟨_, hYG⟩ (hgen ⟨_, hYG⟩ h.2.symm hY2)⟩
    · have h := commute_orbitXY_short σ.toRingHom (e := (eG : ModGL TwistTag.E6.tag K)) hcomm
        ⟨1, ha⟩ (Or.inr rfl) c
      exact ⟨hsub ⟨_, hXG⟩ (hgen ⟨_, hXG⟩ h.1.symm hX2),
        hsub ⟨_, hYG⟩ (hgen ⟨_, hYG⟩ h.2.symm hY2)⟩
    · have hc : σ.toRingHom (c : K) = c := by
        have := mem_orbitField.1 c.2
        rwa [card_orbit_two, pow_one] at this
      have hcc : (c : K) ^ Nat.card k = c := by
        rw [hk, ← hσ]
        exact hc
      obtain ⟨c', hc'⟩ := CFSG.LieType.Chevalley.mem_range_algebraMap_of_pow_card_eq (k := k) hcc
      have hxm := xyUnit_mem_fixed_of_orbitWord_eq k ⟨1, by decide⟩ (e6Index 3) orbitWord_f4_one c'
      refine ⟨⟨ι ⟨xUnit Tag.E6 k (e6Index 3) c', hxm.1⟩, hH _, ?_⟩,
        ⟨ι ⟨yUnit Tag.E6 k (e6Index 3) c', hxm.2⟩, hH _, ?_⟩⟩
      · show baseChangeGL (algebraMap k K) (xUnit Tag.E6 k (e6Index 3) c') = _
        rw [baseChangeGL_xUnit, hc', coe_orbitX_two]
      · show baseChangeGL (algebraMap k K) (yUnit Tag.E6 k (e6Index 3) c') = _
        rw [baseChangeGL_yUnit, hc', coe_orbitY_two]
    · have hc : σ.toRingHom (c : K) = c := by
        have := mem_orbitField.1 c.2
        rwa [card_orbit_three, pow_one] at this
      have hcc : (c : K) ^ Nat.card k = c := by
        rw [hk, ← hσ]
        exact hc
      obtain ⟨c', hc'⟩ := CFSG.LieType.Chevalley.mem_range_algebraMap_of_pow_card_eq (k := k) hcc
      have hxm := xyUnit_mem_fixed_of_orbitWord_eq k ⟨0, by decide⟩ (e6Index 1) orbitWord_f4_zero c'
      refine ⟨⟨ι ⟨xUnit Tag.E6 k (e6Index 1) c', hxm.1⟩, hH _, ?_⟩,
        ⟨ι ⟨yUnit Tag.E6 k (e6Index 1) c', hxm.2⟩, hH _, ?_⟩⟩
      · show baseChangeGL (algebraMap k K) (xUnit Tag.E6 k (e6Index 1) c') = _
        rw [baseChangeGL_xUnit, hc', coe_orbitX_three]
      · show baseChangeGL (algebraMap k K) (yUnit Tag.E6 k (e6Index 1) c') = _
        rw [baseChangeGL_yUnit, hc', coe_orbitY_three]
  have hG : twistedE6RootGroup K σ ≤ M.map (twistedE6RootGroup K σ).subtype := by
    have hgen' := graphFixedRootGroup_eq_iSup_orbitRankOneGroup (t := TwistTag.E6)
      (σ := σ.toRingHom) σ.surjective
    refine (le_of_eq hgen').trans (iSup_le fun a => (Subgroup.closure_le _).2 ?_)
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    exacts [(hmemX a c).1, (hmemX a c).2]
  have hmain : M = ⊤ := by
    refine (Subgroup.eq_top_iff' _).2 fun x => ?_
    obtain ⟨y, hy, hyx⟩ := hG x.2
    have : y = x := Subtype.ext hyx
    exact this ▸ hy
  refine CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311f.uniClosure_eq_top_of_conj g ?_
  rw [hg]
  exact hmain

theorem twE6FourUniNative_odd (σ : K ≃+* K) {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (hk : Nat.card k = ℓ ^ f) (hK : Nat.card K = (ℓ ^ f) ^ 2) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ}
    [hpF : Fact p.Prime] (hp5 : 5 ≤ p) (he : orderOf (((ℓ ^ f : ℕ)) : ZMod p) = 4)
    (E₀ : Subgroup ↥(twistedE6RootGroup K σ)) (hE₀p : ∀ x ∈ E₀, x ^ p = 1)
    (hE₀c : Nat.card E₀ = p ^ 2) :
    Subgroup.closure {k | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x ∧ ∃ m : ℕ, k ^ (ℓ ^ m) = 1} = ⊤ := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hp : p.Prime := hpF.out
  haveI : CharP K ℓ := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    hℓ (k := 2 * f) (by omega) (by rw [hK, ← pow_mul, mul_comm])
  haveI : CharP k ℓ := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    hℓ (k := f) hf hk
  have hfix : ∀ c : k, σ (algebraMap k K c) = algebraMap k K c := by
    intro c
    rw [hσ, ← hk, ← map_pow]
    congr 1
    haveI : Fintype k := Fintype.ofFinite k
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.pow_card c
  have hp' : p ∣ Nat.card k ^ 2 + 1 := by
    rw [hk]
    exact CFSG.LieType.SeitzGeneration.dvd_sq_add_one_of_orderOf_eq_four hp he
  have hTG : SylowTorus (twistedE6RootGroup K σ) p 2 :=
    sylowTorus_twistedE6_four hℓ hf K hK σ hσ hp he
  have hTΓ : SylowTorus (twistedFixedGroup TwistTag.E6 k (RingHom.id k)) p 2 :=
    (sylowTorus_F4_four k hp (by omega) hp').of_mulEquiv (e6FixedF4EquivAll k).symm
  have hinj := phiG_injective σ hfix
  obtain ⟨e, ⟨γ, hγ, rfl⟩, heord, hecomm⟩ := exists_e4 (K := K) (algebraMap k K) hp'
  set γΓ : twistedFixedGroup TwistTag.E6 k (RingHom.id k) := ⟨γ, hγ⟩ with hγΓ
  have hordγ : orderOf γΓ = p := by
    rw [← Subgroup.orderOf_coe, show (γΓ : ModGL TwistTag.E6.tag k) = γ from rfl,
      ← orderOf_injective (baseChangeGL (algebraMap k K)) (baseChangeGL_injective _) γ]
    exact heord
  obtain ⟨EΓ, hEΓ, hEΓc, hγE⟩ := exists_plane_containing_of_sylowTorus hTΓ hordγ
  set ι := phiG σ hfix with hιdef
  set EH : Subgroup (twistedE6RootGroup K σ) := EΓ.map ι with hEHdef
  have hEH : IsElemAbelian p EH :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hEΓ ι
  have hEHc : Nat.card EH = p ^ 2 := by
    rw [hEHdef, Subgroup.card_map_of_injective hinj, hEΓc]
  obtain ⟨g, hg⟩ := exists_conj_eq_of_sylowTorus hTG
    (Inputs2311i.isElemAbelian_of_exponent_card_sq hE₀p hE₀c) hE₀c hEH hEHc
  have hclΓ : Subgroup.closure {x : twistedFixedGroup TwistTag.E6 k (RingHom.id k) |
      ∃ y ∈ EΓ, y ≠ 1 ∧ Commute x y ∧ ∃ m : ℕ, x ^ (ℓ ^ m) = 1} = ⊤ := by
    refine Inputs2311i.uniClosure_eq_top_of_mulEquiv (e6FixedF4EquivAll k) ?_
    have hF₁p : ∀ x ∈ EΓ.map (e6FixedF4EquivAll k).toMonoidHom, x ^ p = 1 := by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hEΓ.2 x hx, map_one]
    have hF₁c : Nat.card (EΓ.map (e6FixedF4EquivAll k).toMonoidHom) = p ^ 2 := by
      rw [Subgroup.card_map_of_injective (f := (e6FixedF4EquivAll k).toMonoidHom)
        (e6FixedF4EquivAll k).injective, hEΓc]
    have h := Inputs2311g.f4Phi4UniNative k (two_ne_zero_of_charP_odd hℓ hℓ2) p hp5 hp' _ hF₁p hF₁c
    rw [ringChar.eq k ℓ] at h
    exact h
  set M := Subgroup.closure {x : twistedE6RootGroup K σ | ∃ y ∈ EH, y ≠ 1 ∧ Commute x y ∧
    ∃ m : ℕ, x ^ (ℓ ^ m) = 1} with hM
  have hH : ∀ x, ι x ∈ M := by
    intro x
    have hx : x ∈ Subgroup.closure {x : twistedFixedGroup TwistTag.E6 k (RingHom.id k) |
        ∃ y ∈ EΓ, y ≠ 1 ∧ Commute x y ∧ ∃ m : ℕ, x ^ (ℓ ^ m) = 1} := by
      rw [hclΓ]
      exact Subgroup.mem_top x
    have hle : (Subgroup.closure {x : twistedFixedGroup TwistTag.E6 k (RingHom.id k) |
        ∃ y ∈ EΓ, y ≠ 1 ∧ Commute x y ∧ ∃ m : ℕ, x ^ (ℓ ^ m) = 1}).map ι ≤ M := by
      rw [MonoidHom.map_closure]
      refine Subgroup.closure_mono ?_
      rintro _ ⟨z, ⟨y, hy, hy1, hzy, m, hm⟩, rfl⟩
      exact ⟨ι y, ⟨y, hy, rfl⟩, fun h => hy1 (hinj (h.trans (map_one _).symm)), hzy.map ι, m,
        by rw [← map_pow, hm, map_one]⟩
    exact hle ⟨x, hx, rfl⟩
  set eG : twistedE6RootGroup K σ := ι γΓ with heGdef
  have heG : eG ∈ EH := ⟨γΓ, hγE, rfl⟩
  have heG1 : eG ≠ 1 := by
    intro h
    have h1 : orderOf eG = p := by
      rw [heGdef, orderOf_injective ι hinj γΓ, hordγ]
    rw [h, orderOf_one] at h1
    exact hp.one_lt.ne h1
  have hcomm : ∀ i, (i = e6Index 0 ∨ i = e6Index 5) →
      ∀ d : K, Commute (eG : ModGL TwistTag.E6.tag K) (xUnit Tag.E6 K i d) ∧
        Commute (eG : ModGL TwistTag.E6.tag K) (yUnit Tag.E6 K i d) :=
    hecomm
  have hgen : ∀ y : twistedE6RootGroup K σ,
      Commute (y : ModGL TwistTag.E6.tag K) (eG : ModGL TwistTag.E6.tag K) →
        (∃ m : ℕ, y ^ (ℓ ^ m) = 1) → y ∈ M :=
    fun y hy hy2 => Subgroup.subset_closure ⟨eG, heG, heG1, Subtype.ext hy.eq, hy2⟩
  have hsub : ∀ x : twistedE6RootGroup K σ, x ∈ M →
      (x : ModGL TwistTag.E6.tag K) ∈ M.map (twistedE6RootGroup K σ).subtype :=
    fun x hx => ⟨x, hx, rfl⟩
  have hnΓ : nElt TwistTag.E6.tag k ωwWord ∈ twistedFixedGroup TwistTag.E6 k (RingHom.id k) :=
    nElt_flatten_mem k ωwFold
  set nΓ : twistedFixedGroup TwistTag.E6 k (RingHom.id k) := ⟨_, hnΓ⟩ with hnΓdef
  set nG : twistedE6RootGroup K σ := ι nΓ with hnGdef
  have hnG : (nG : ModGL TwistTag.E6.tag K) = nElt TwistTag.E6.tag K ωwWord :=
    baseChangeGL_nElt (algebraMap k K) Tag.E6 ωwWord
  have hmemX : ∀ (a : Fin TwistTag.E6.foldedTag.rank)
      (c : orbitField TwistTag.E6 K σ.toRingHom a),
      (orbitX TwistTag.E6 K σ.toRingHom a c : ModGL TwistTag.E6.tag K) ∈
        M.map (twistedE6RootGroup K σ).subtype ∧
      (orbitY TwistTag.E6 K σ.toRingHom a c : ModGL TwistTag.E6.tag K) ∈
        M.map (twistedE6RootGroup K σ).subtype := by
    intro a c
    have hXG : (orbitX TwistTag.E6 K σ.toRingHom a c : ModGL TwistTag.E6.tag K) ∈
        twistedE6RootGroup K σ :=
      graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
        (orbitX_mem_graphFixedPosUnipotent _ _ _ _)
    have hYG : (orbitY TwistTag.E6 K σ.toRingHom a c : ModGL TwistTag.E6.tag K) ∈
        twistedE6RootGroup K σ :=
      graphFixedNegUnipotent_le_graphFixedRootGroup _ _ _
        (orbitY_mem_graphFixedNegUnipotent _ _ _ _)
    have hX2 := exists_pow_char_eq_one_of_mem_unipotent (ℓ := ℓ) (G := twistedE6RootGroup K σ) ⟨_, hXG⟩
      (Or.inl (Subgroup.mem_inf.1 (orbitX_mem_graphFixedPosUnipotent _ σ.toRingHom a c)).1)
    have hY2 := exists_pow_char_eq_one_of_mem_unipotent (ℓ := ℓ) (G := twistedE6RootGroup K σ) ⟨_, hYG⟩
      (Or.inr (Subgroup.mem_inf.1 (orbitY_mem_graphFixedNegUnipotent _ σ.toRingHom a c)).1)
    obtain ⟨a, ha⟩ := a
    have ha4 : a < 4 := ha
    interval_cases a
    · have h := commute_orbitXY_zero σ.toRingHom (e := (eG : ModGL TwistTag.E6.tag K)) hcomm c
      exact ⟨hsub ⟨_, hXG⟩ (hgen ⟨_, hXG⟩ h.1.symm hX2),
        hsub ⟨_, hYG⟩ (hgen ⟨_, hYG⟩ h.2.symm hY2)⟩
    ·
      obtain ⟨hX1, hY1⟩ := orbitXY_one_mem_rootSpan σ.toRingHom c
      have hcS0 : ∀ γ ∈ S₀, ∀ c : K, Commute (eG : ModGL TwistTag.E6.tag K)
          (pinnedX Tag.E6 K γ c) := by
        intro γ hγ c
        rcases hγ with rfl | rfl | rfl | rfl
        · rw [pinnedX_single]; exact (hcomm _ (Or.inl rfl) c).1
        · rw [pinnedX_neg_single]; exact (hcomm _ (Or.inl rfl) c).2
        · rw [pinnedX_single]; exact (hcomm _ (Or.inr rfl) c).1
        · rw [pinnedX_neg_single]; exact (hcomm _ (Or.inr rfl) c).2
      have hconj : ∀ z : twistedE6RootGroup K σ,
          (z : ModGL TwistTag.E6.tag K) ∈ rootSpan Tag.E6 K S₂ → (∃ m : ℕ, z ^ (ℓ ^ m) = 1) →
            z ∈ M := by
        intro z hz hz2
        set y : twistedE6RootGroup K σ := nG⁻¹ * z * nG with hy
        have hy' : (y : ModGL TwistTag.E6.tag K) ∈ rootSpan Tag.E6 K S₀ := by
          have e : (y : ModGL TwistTag.E6.tag K) =
              (nElt TwistTag.E6.tag K ωwWord)⁻¹ * (z : ModGL TwistTag.E6.tag K) *
                nElt TwistTag.E6.tag K ωwWord := by
            rw [hy]
            simp only [Subgroup.coe_mul, Subgroup.coe_inv, hnG]
          rw [e]
          exact nElt_inv_conj_mem_rootSpan K ωwWord ωw_inv_S₂ hz
        have hyc := commute_of_forall_pinnedX K hcS0 hy'
        have hy2 : ∃ m : ℕ, y ^ (ℓ ^ m) = 1 := by
          obtain ⟨m, hm⟩ := hz2
          refine ⟨m, ?_⟩
          rw [hy, show nG⁻¹ * z * nG = nG⁻¹ * z * nG⁻¹⁻¹ by rw [inv_inv], conj_pow, inv_inv, hm,
            mul_one, inv_mul_cancel]
        have hycl : y ∈ M := hgen y hyc.symm hy2
        have : z = nG * y * nG⁻¹ := by rw [hy]; group
        rw [this]
        exact mul_mem (mul_mem (hH nΓ) hycl) (inv_mem (hH nΓ))
      exact ⟨hsub ⟨_, hXG⟩ (hconj ⟨_, hXG⟩ hX1 hX2), hsub ⟨_, hYG⟩ (hconj ⟨_, hYG⟩ hY1 hY2)⟩
    · have hc : σ.toRingHom (c : K) = c := by
        have := mem_orbitField.1 c.2
        rwa [card_orbit_two, pow_one] at this
      have hcc : (c : K) ^ Nat.card k = c := by
        rw [hk, ← hσ]
        exact hc
      obtain ⟨c', hc'⟩ := CFSG.LieType.Chevalley.mem_range_algebraMap_of_pow_card_eq (k := k) hcc
      have hxm := xyUnit_mem_fixed_of_orbitWord_eq k ⟨1, by decide⟩ (e6Index 3) orbitWord_f4_one c'
      refine ⟨⟨ι ⟨xUnit Tag.E6 k (e6Index 3) c', hxm.1⟩, hH _, ?_⟩,
        ⟨ι ⟨yUnit Tag.E6 k (e6Index 3) c', hxm.2⟩, hH _, ?_⟩⟩
      · show baseChangeGL (algebraMap k K) (xUnit Tag.E6 k (e6Index 3) c') = _
        rw [baseChangeGL_xUnit, hc', coe_orbitX_two]
      · show baseChangeGL (algebraMap k K) (yUnit Tag.E6 k (e6Index 3) c') = _
        rw [baseChangeGL_yUnit, hc', coe_orbitY_two]
    · have hc : σ.toRingHom (c : K) = c := by
        have := mem_orbitField.1 c.2
        rwa [card_orbit_three, pow_one] at this
      have hcc : (c : K) ^ Nat.card k = c := by
        rw [hk, ← hσ]
        exact hc
      obtain ⟨c', hc'⟩ := CFSG.LieType.Chevalley.mem_range_algebraMap_of_pow_card_eq (k := k) hcc
      have hxm := xyUnit_mem_fixed_of_orbitWord_eq k ⟨0, by decide⟩ (e6Index 1) orbitWord_f4_zero c'
      refine ⟨⟨ι ⟨xUnit Tag.E6 k (e6Index 1) c', hxm.1⟩, hH _, ?_⟩,
        ⟨ι ⟨yUnit Tag.E6 k (e6Index 1) c', hxm.2⟩, hH _, ?_⟩⟩
      · show baseChangeGL (algebraMap k K) (xUnit Tag.E6 k (e6Index 1) c') = _
        rw [baseChangeGL_xUnit, hc', coe_orbitX_three]
      · show baseChangeGL (algebraMap k K) (yUnit Tag.E6 k (e6Index 1) c') = _
        rw [baseChangeGL_yUnit, hc', coe_orbitY_three]
  have hG : twistedE6RootGroup K σ ≤ M.map (twistedE6RootGroup K σ).subtype := by
    have hgen' := graphFixedRootGroup_eq_iSup_orbitRankOneGroup (t := TwistTag.E6)
      (σ := σ.toRingHom) σ.surjective
    refine (le_of_eq hgen').trans (iSup_le fun a => (Subgroup.closure_le _).2 ?_)
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    exacts [(hmemX a c).1, (hmemX a c).2]
  have hmain : M = ⊤ := by
    refine (Subgroup.eq_top_iff' _).2 fun x => ?_
    obtain ⟨y, hy, hyx⟩ := hG x.2
    have : y = x := Subtype.ext hyx
    exact this ▸ hy
  refine CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311f.uniClosure_eq_top_of_conj g ?_
  rw [hg]
  exact hmain

end TwE6ThreeFour

section TwE6ThreeFourCat

open CFSG.LieType.Chevalley.E6GraphLevi

set_option linter.unusedSectionVars false


theorem uniSeitzPlanes_twE6ThreeFour_inner_odd :
    UniSeitzPlanes fun d p E => InnerPlane d p E ∧ 5 ≤ p ∧ ¬ NormalizesRSubgroup d E ∧
      ∃ q : PrimePower, d.1 = .twistedE6 q ∧ q.p ≠ 2 ∧
        (orderOf ((q.card : ℕ) : ZMod p) = 3 ∨ orderOf ((q.card : ℕ) : ZMod p) = 4) := by
  rintro ⟨d, hv⟩ p hp hp2 hpd _ E hE hc ⟨hin, hp5, hn, q, hq, hq2, hord⟩
  obtain rfl : d = .twistedE6 q := hq
  obtain ⟨K, _, σ, hK, hσ, ⟨e⟩⟩ := exists_catEquiv_twistedE6 q hv
  have hKfin : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]; exact pow_ne_zero _ (pow_ne_zero _ q.prime_p.ne_zero))
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hZ : Subgroup.center ↥(twistedE6RootGroup K σ) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  have hinj := conj_injective_of_mulEquiv e (conj_injective_of_center_eq_bot hZ)
  have hf := q.exponent_pos
  have hord' : orderOf (((q.p ^ q.exponent : ℕ)) : ZMod p) = 3 ∨
      orderOf (((q.p ^ q.exponent : ℕ)) : ZMod p) = 4 := by
    rw [← PrimePower.card_def]
    exact hord
  haveI : CharP K q.p := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    q.prime_p (k := 2 * q.exponent) (by omega) (by rw [hK, ← pow_mul, mul_comm])
  have hk : Nat.card (GaloisField q.p q.exponent) = q.p ^ q.exponent := GaloisField.card q.p _ hf.ne'
  obtain ⟨ι₀⟩ := CFSG.HardMathSupport.Lang.AnisoE6.nonempty_ringHom_of_card_sq (ℓ := q.p) (f := q.exponent)
    hk hK
  letI : Algebra (GaloisField q.p q.exponent) K := ι₀.toAlgebra
  show UniPlaneGen (LieTypeIndex.twistedE6 q).characteristic E
  rw [LieTypeIndex.characteristic_twistedE6]
  refine CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311f.uniPlaneGen_of_native_uniClosure
    (p := p) (r := q.p) e hinj (fun E₀ h1 h2 _ => ?_) hE hc hin ?_
  · rcases hord' with h3 | h4
    · exact twE6ThreeUniNative_odd (k := GaloisField q.p q.exponent) σ q.prime_p hq2 hf hk hK hσ hp5 h3
        E₀ h1 h2
    · exact twE6FourUniNative_odd (k := GaloisField q.p q.exponent) σ q.prime_p hq2 hf hk hK hσ hp5 h4
        E₀ h1 h2
  · rintro ⟨R, hR1, hRp, hRn⟩
    exact hn ⟨R, hR1, by rw [LieTypeIndex.characteristic_twistedE6]; exact hRp, hRn⟩

end TwE6ThreeFourCat

section E8Eight

open CFSG.HardMathSupport.Lang.AnisoF4 CFSG.HardMathSupport.Lang.AnisoE8 CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.ModelFacts.OrthAut CFSG.ComponentClassification.CatLeafProof

set_option linter.unusedSectionVars false


theorem rootGroupE8_pow_ringChar_odd {K : Type} [Field K] {γ : Fin (Tag.rank .E8) → ℤ}
    (hγ : IsRoot .E8 γ) {y : adjointGroup .E8 K}
    (hy : y ∈ (CFSG.LieType.Steinberg.Adjoint.e8Datum K).rootGroup γ) : y ^ ringChar K = 1 := by
  obtain ⟨c, rfl⟩ := (CFSG.LieType.Steinberg.Adjoint.mem_rootGroup_iff hγ y).1 hy
  exact Inputs2311g.xPar_pow_ringChar_eq_one _ γ c

theorem e8EightUniNative_odd (K : Type) [Field K] [Finite K] (hK2 : ringChar K ≠ 2) {p : ℕ}
    [hpF : Fact p.Prime] (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 8)
    (E₀ : Subgroup (adjointGroup .E8 K)) (hE₀p : ∀ x ∈ E₀, x ^ p = 1) (hE₀c : Nat.card E₀ = p ^ 2) :
    Subgroup.closure {k | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x ∧ ∃ m : ℕ, k ^ (ringChar K ^ m) = 1} = ⊤ := by
  have hfam := exists_e8D8_family K
  obtain ⟨Ψ, hker, hrange⟩ := exists_psi_D8_E8_of_family hfam
  obtain ⟨ρ, hρ, hcomm, hψ⟩ := hfam
  have hp2 : p ≠ 2 := ne_two_of_orderOf_eq_eight hpF.out he
  have hpq : p ∣ Nat.card K ^ 4 + 1 := dvd_pow_four_add_one_of_orderOf_eq_eight hpF.out he
  have hpK : ¬ p ∣ Nat.card K := not_dvd_of_orderOf_eq_eight hpF.out he
  have hpq1 : ¬ p ∣ Nat.card K - 1 := not_dvd_pred_of_orderOf_eq_eight hpF.out Nat.card_pos he
  have hp5 : 5 ≤ p := by
    have h8 : 8 ∣ p - 1 := by
      have hq0 : ((Nat.card K : ℕ) : ZMod p) ≠ 0 := fun h =>
        hpK ((ZMod.natCast_eq_zero_iff _ _).1 h)
      exact he ▸ ZMod.orderOf_dvd_card_sub_one hq0
    have := hpF.out.two_le
    obtain ⟨k, hk⟩ := h8
    rcases k with _ | k
    · omega
    · omega
  obtain ⟨e, heA, heo, hec⟩ := exists_e1_E8_eight_of_family hp2 hpq ρ hρ hcomm hψ
  have hle : (⨆ k : Fin 7, e8D8Chain K k.castSucc) ≤ ⨆ k, e8D8Chain K k :=
    iSup_le fun k => le_iSup (e8D8Chain K) k.castSucc
  have heX : e ∈ ⨆ k, e8D8Chain K k := hle heA
  obtain ⟨g, hgX, hge⟩ :=
    exists_conj_plane_d8_of_family ⟨ρ, hρ, hcomm, hψ⟩ he heX heo E₀ hE₀p hE₀c
  have hE₁p : ∀ x ∈ E₀.map (MulAut.conj g).toMonoidHom, x ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hE₀p x hx, map_one]
  have hE₁c : Nat.card (E₀.map (MulAut.conj g).toMonoidHom) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hE₀c]
  have he1 : e ≠ 1 := by
    intro h
    rw [h, orderOf_one] at heo
    exact hpF.out.one_lt.ne heo
  refine CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311f.uniClosure_eq_top_of_conj g ?_
  apply eq_top_of_d8Chain_le_of_delta_le
  · exact CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311f.iSup_d8Chain_le_uniClosure_of_ne hK2
      hpF.out hp5 hpK hpq1 Ψ hker hrange _ hgX hE₁p hE₁c
  · have hδ : IsRoot .E8 e8Delta := isRoot_e8Delta
    have hδ' : IsRoot .E8 (-e8Delta) := by
      rw [RootCertificate.isRoot_iff (Tag.rootCertificate_check .E8)]
      decide +kernel
    refine sup_le ?_ ?_
    · intro y hy
      exact Subgroup.subset_closure ⟨e, hge, he1, (hec y (Subgroup.mem_sup_left hy)).symm, 1,
        by rw [pow_one]; exact rootGroupE8_pow_ringChar_odd hδ hy⟩
    · intro y hy
      exact Subgroup.subset_closure ⟨e, hge, he1, (hec y (Subgroup.mem_sup_right hy)).symm, 1,
        by rw [pow_one]; exact rootGroupE8_pow_ringChar_odd hδ' hy⟩

theorem uniSeitzPlanes_E8_eight_inner_odd :
    UniSeitzPlanes fun d p E => InnerPlane d p E ∧
      (∃ q : PrimePower, d.1 = .E8 q ∧ orderOf ((q.card : ℕ) : ZMod p) = 8) ∧
      d.1.characteristic ≠ 2 ∧ ¬ NormalizesRSubgroup d E := by
  rintro ⟨d, hv⟩ p hp hp2 hpd _ E hE hc ⟨hin, ⟨q, hq, h8⟩, hch, hn⟩
  obtain rfl : d = .E8 q := hq
  haveI : Fact p.Prime := ⟨hp⟩
  exact CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311f.uniPlaneGen_E8_of_native hv hch
    (fun K _ _ hKq hK2 E₀ h1 h2 _ => e8EightUniNative_odd K hK2 (by rw [hKq]; exact h8) E₀ h1 h2) hE hc hin hn

end E8Eight

section SpinOdd

open CFSG.HardMathSupport.Lang.AnisoF4 CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.ModelFacts.OrthAut CFSG.ComponentClassification.CatLeafProof

set_option linter.unusedSectionVars false

theorem closure_uniCen_spinPlus_odd {K : Type} [Field K] [Finite K] (hK2 : ringChar K ≠ 2) {n : ℕ}
    (hn : 4 ≤ n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpK : ¬ p ∣ Nat.card K)
    (hpq1 : ¬ p ∣ Nat.card K - 1) (F : Subgroup (spinGroup (quadPlus n K))) (hF : IsElemAbelian p F)
    (hc : Nat.card F = p ^ 2) :
    Subgroup.closure {g | ∃ x ∈ F, x ≠ 1 ∧ Commute g x ∧ ∃ m : ℕ, g ^ (ringChar K ^ m) = 1} = ⊤ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hn3 : 3 ≤ n := by omega
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨m, hℓ, hm⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  have hK : Nat.card K = ringChar K ^ (m : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hm
  haveI : NeZero n := ⟨by omega⟩
  have : Nonempty (Fin n ⊕ Fin n) := ⟨Sum.inl ⟨0, by omega⟩⟩
  have : Finite (spinGroup (quadPlus n K)) :=
    CFSG.ClassicalInvolution.ModelFacts.finite_spinGroup_of_ker _ coe_ker_spinMatrix_quadPlus
  obtain ⟨hπsurj, hcomap, hZ⟩ := spinToStatedProj_quadPlus (n := n) (K := K) hn3
  set π := spinToStatedProj (quadPlus n K) (range_spinMatrix_quadPlus hn3) with hπdef
  have hcen : ¬ p ∣ Nat.card (Subgroup.center (spinGroup (quadPlus n K))) :=
    not_dvd_card_center_spin_of_not_dvd_pred (quadPlus n K) (range_spinMatrix_quadPlus hn3)
      hZ hcomap
      (fun x hx => spin_mul_self_eq_one ((mem_ker_spinMatrix_quadPlus_iff x).mp hx)) hp2 hpq1
  have hrq1 : ¬ ringChar K ∣ Nat.card K - 1 := by
    intro hd
    have h1 : ringChar K ∣ Nat.card K := by rw [hK]; exact dvd_pow_self _ m.ne_zero
    have hq1 : 1 ≤ Nat.card K := Nat.card_pos
    have h3 : ringChar K ∣ Nat.card K - (Nat.card K - 1) := Nat.dvd_sub h1 hd
    rw [show Nat.card K - (Nat.card K - 1) = 1 by omega] at h3
    exact hℓ.one_lt.ne' (Nat.dvd_one.mp h3)
  have hrcen : ¬ ringChar K ∣ Nat.card (Subgroup.center (spinGroup (quadPlus n K))) :=
    not_dvd_card_center_spin_of_not_dvd_pred (quadPlus n K) (range_spinMatrix_quadPlus hn3)
      hZ hcomap
      (fun x hx => spin_mul_self_eq_one ((mem_ker_spinMatrix_quadPlus_iff x).mp hx)) hK2 hrq1
  have hπcop : ¬ p ∣ Nat.card π.ker := by
    intro hd
    apply hcen
    have : Nat.card π.ker ∣ Nat.card (Subgroup.center (spinGroup (quadPlus n K))) := by
      rw [hZ]
    exact hd.trans this
  have hrcop : (Nat.card π.ker).Coprime (ringChar K) := by
    have h' : ¬ ringChar K ∣ Nat.card π.ker := by
      intro hd
      apply hrcen
      have : Nat.card π.ker ∣ Nat.card (Subgroup.center (spinGroup (quadPlus n K))) := by
        rw [hZ]
      exact hd.trans this
    exact ((Nat.Prime.coprime_iff_not_dvd hℓ).2 h').symm
  have hperf : ⁅(⊤ : Subgroup (spinGroup (quadPlus n K))), ⊤⁆ = ⊤ :=
    (isPerfect_spinGroup_quadPlus hn3).commutator_eq_top
  have hEbarea : IsElemAbelian p (F.map π) := hF.map π
  have hcardEbar : Nat.card (F.map π) = p ^ 2 := by
    rw [CFSG.LieType.SeitzGeneration.ExcHigh.card_map_eq_of_disjoint_ker π
      (disjoint_ker_of_exponent π hπcop hF.2), hc]
  have hmodel := CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311d.orthU3_plusPlanes (r := n) hn hp hp2
    hpK hK2 (F.map π) hEbarea hcardEbar
  have hG := CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311f.uniClosure_eq_top_of_quotient π hπsurj
    hZ.le hπcop hrcop hperf F hF.2 hmodel
  rw [eq_top_iff, ← hG]
  refine Subgroup.closure_mono ?_
  rintro g ⟨x, hx, hx1, hg, hgr⟩
  exact ⟨x, hx, hx1, hg, 1, by rw [pow_one]; exact hgr⟩

theorem closure_pow_eq_top_of_quasisimple_of_range {B G : Type} [Group B] [Group G] [Finite B] {r : ℕ}
    [hr : Fact r.Prime] (hB : CFSG.IsQuasisimple B) (Ψ : B →* G) {x : G} (hx : x ∈ Ψ.range) (hx1 : x ≠ 1)
    (hxr : x ^ r = 1) : Subgroup.closure {b : B | ∃ n : ℕ, b ^ (r ^ n) = 1} = ⊤ := by
  obtain ⟨s, rfl⟩ := hx
  obtain ⟨s', -, ⟨m, hm⟩, hs'⟩ := Inputs2311g.exists_rElement_lift_of_pow Ψ hr.out s (n := 1)
    (by rw [pow_one]; exact hxr)
  have hs'1 : s' ≠ 1 := fun h => hx1 (by rw [← hs', h, map_one])
  have hdvd : r ∣ Nat.card B := by
    have ho : orderOf s' ∣ r ^ m := orderOf_dvd_of_pow_eq_one hm
    obtain ⟨j, -, hjeq⟩ := (Nat.dvd_prime_pow hr.out).1 ho
    have hj0 : j ≠ 0 := by
      intro h0
      rw [h0, pow_zero] at hjeq
      exact hs'1 (orderOf_eq_one_iff.1 hjeq)
    have : r ∣ orderOf s' := by rw [hjeq]; exact dvd_pow_self r hj0
    exact this.trans (orderOf_dvd_natCard s')
  have hq : CFSG.IsQuasisimple ↥(⊤ : Subgroup B) := CFSG.IsQuasisimple.of_mulEquiv Subgroup.topEquiv hB
  have hle := CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311f.le_closure_pow_of_quasisimple
    (G := B) (X := ⊤) (r := r) hq (by rw [Subgroup.card_top]; exact hdvd)
  rw [eq_top_iff]
  intro y _
  refine Subgroup.closure_mono ?_ (hle (Subgroup.mem_top y))
  rintro z ⟨-, n, hn⟩
  exact ⟨n, hn⟩

end SpinOdd

section CatOdd

set_option linter.unusedSectionVars false


theorem uniPlaneGen_cat_odd {τ : Tag} {c : PrimePower → LieTypeIndex}
    (hB : CFSG.TauCetiBridge.Even.UntwistedBridgeAll τ c) (hchar : ∀ q, (c q).characteristic = q.p)
    {q : PrimePower} (hv : (c q).Valid) (hq2 : q.p ≠ 2) {p : ℕ}
    (hnat : ∀ (K : Type) [Field K] [Finite K], Nat.card K = q.card → ringChar K ≠ 2 →
      ∀ E₀ : Subgroup ↥(adjointGroup τ K), (∀ x ∈ E₀, x ^ p = 1) → Nat.card E₀ = p ^ 2 →
        ¬ NormalizesRGroup (ringChar K) E₀ →
        Subgroup.closure {k | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x ∧ ∃ m : ℕ, k ^ (ringChar K ^ m) = 1} = ⊤)
    {E : Subgroup (MulAut (Cat ⟨c q, hv⟩))} (hE : IsElemAbelian p E) (hc : Nat.card E = p ^ 2)
    (hin : InnerPlane ⟨c q, hv⟩ p E) (hn : ¬ NormalizesRSubgroup ⟨c q, hv⟩ E) :
    UniPlaneGen (c q).characteristic E := by
  obtain ⟨K, _, _, hKq, hKchar, ⟨e⟩⟩ := exists_catEquiv_adjointGroup hB q hv
  have hring : ringChar K = q.p := ringChar.eq K q.p
  have hK2 : ringChar K ≠ 2 := by rw [hring]; exact hq2
  have h := CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311f.uniPlaneGen_of_native_uniClosure
    (p := p) (r := ringChar K) e
    (conj_injective_of_mulEquiv e (conj_injective_of_center_eq_bot center_adjointGroup_eq_bot))
    (fun E₀ h1 h2 h3 => hnat K hKq hK2 E₀ h1 h2 h3) hE hc hin ?_
  · rw [hring] at h
    rw [hchar]
    exact h
  · rintro ⟨R, hR1, hRp, hRn⟩
    refine hn ⟨R, hR1, ?_, hRn⟩
    rw [hchar, ← hring]
    exact hRp

end CatOdd

section E7TwoOdd

open CFSG.HardMathSupport.Lang.AnisoF4 CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.ModelFacts.OrthAut CFSG.ComponentClassification.CatLeafProof

set_option linter.unusedSectionVars false


theorem exists_rootElement_mem_e7D6Group (K : Type) [Field K] :
    ∃ x ∈ e7D6Group K, x ≠ 1 ∧ x ^ ringChar K = 1 := by
  refine ⟨CFSG.LieType.Steinberg.Adjoint.xPar (rootOperatorFamily .E7) (Pi.single (e7D6Node 0) 1) (1 : K),
    ?_, ?_, Inputs2311g.xPar_pow_ringChar_eq_one _ _ 1⟩
  · refine Subgroup.mem_iSup_of_mem 0 (Subgroup.mem_sup_left ?_)
    exact CFSG.LieType.Steinberg.Adjoint.xPar_mem (isRoot_single _ _) 1
  · intro h
    have h0 := CFSG.LieType.Steinberg.Adjoint.xPar_zero (F := rootOperatorFamily .E7) (K := K)
      (Pi.single (e7D6Node 0) 1)
    exact one_ne_zero (CFSG.LieType.Steinberg.Adjoint.xPar_injective (isRoot_single _ _) (h.trans h0.symm))

theorem e7A1D6_le_uniClosure_odd {K : Type} [Field K] [Finite K] (hK2 : ringChar K ≠ 2) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card K + 1)
    (F : Subgroup (adjointGroup .E7 K)) (hF : F ≤ e7A1D6 K) (hFp : ∀ x ∈ F, x ^ p = 1)
    (hFc : Nat.card F = p ^ 2) :
    e7A1D6 K ≤ Subgroup.closure {g | ∃ x ∈ F, x ≠ 1 ∧ Commute g x ∧
      ∃ m : ℕ, g ^ (ringChar K ^ m) = 1} := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨m, hℓ, -⟩ := FiniteField.card K (ringChar K)
  haveI : Fact (ringChar K).Prime := ⟨hℓ⟩
  have hpK : ¬ p ∣ Nat.card K := by
    intro hd
    have h1 : p ∣ 1 := (Nat.dvd_add_right hd).mp hpq
    exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
  have hpq1 : ¬ p ∣ Nat.card K - 1 := by
    intro hd
    have hq1 : 1 ≤ Nat.card K := Nat.card_pos
    have h3 : p ∣ (Nat.card K + 1) - (Nat.card K - 1) := Nat.dvd_sub hpq hd
    have e : (Nat.card K + 1) - (Nat.card K - 1) = 2 := by omega
    rw [e] at h3
    have := Nat.le_of_dvd (by norm_num) h3
    omega
  have hpK0 : (p : K) ≠ 0 :=
    CFSG.LieType.SeitzGeneration.ExcHigh.natCast_ne_zero_of_not_dvd_card hp hpK
  have hn3 : 3 ≤ 6 := by norm_num
  have : Nonempty (Fin 6 ⊕ Fin 6) := ⟨Sum.inl 0⟩
  have : Finite (spinGroup (quadPlus 6 K)) :=
    CFSG.ClassicalInvolution.ModelFacts.finite_spinGroup_of_ker _ coe_ker_spinMatrix_quadPlus
  obtain ⟨Ψ, hker, hrange⟩ := exists_psi_D6_E7 K
  obtain ⟨ρ, hρi, hρr⟩ := exists_sl2_hom_rootPairE7 (K := K)
    CFSG.ComponentClassification.CatLeafProof.isRoot_e7Theta
  have hcentr : e7D6Group K ≤ Subgroup.centralizer
      (rootPairE7 K CFSG.ComponentClassification.CatLeafProof.e7Theta : Set (adjointGroup .E7 K)) := by
    refine iSup_le fun k => ?_
    intro y hy x hx
    obtain ⟨h1, h2, h3, h4, h5⟩ := e7Theta_orth k
    exact CFSG.ComponentClassification.CatLeafProof.commutes_rootPair_of_noG2 (K := K)
      CFSG.LieType.Steinberg.Adjoint.noG2_E7 CFSG.ComponentClassification.CatLeafProof.isRoot_e7Theta
      (isRoot_single _ _) h1 h2 h3 h4 h5 x hx y hy
  have hcomm : ∀ (a : SL(2, K)) (t : spinGroup (quadPlus 6 K)), Commute (ρ a) (Ψ t) := by
    intro a t
    have hx : ρ a ∈ rootPairE7 K CFSG.ComponentClassification.CatLeafProof.e7Theta := hρr ▸ ⟨a, rfl⟩
    have hy : Ψ t ∈ e7D6Group K := hrange ▸ ⟨t, rfl⟩
    exact Subgroup.mem_centralizer_iff.1 (hcentr hy) _ hx
  let ψ : SL(2, K) × spinGroup (quadPlus 6 K) →* adjointGroup .E7 K :=
    MonoidHom.noncommCoprod ρ Ψ hcomm
  have hrangeψ : ψ.range = e7A1D6 K := by
    rw [MonoidHom.noncommCoprod_range, hρr, hrange, e7A1D6, sup_comm]
  obtain ⟨hπsurj, hcomap, hZ⟩ := spinToStatedProj_quadPlus (n := 6) (K := K) hn3
  have hcen : ¬ p ∣ Nat.card (Subgroup.center (spinGroup (quadPlus 6 K))) :=
    not_dvd_card_center_spin_of_not_dvd_pred (quadPlus 6 K) (range_spinMatrix_quadPlus hn3)
      hZ hcomap
      (fun x hx => spin_mul_self_eq_one ((mem_ker_spinMatrix_quadPlus_iff x).mp hx)) hp2 hpq1
  have hψker : ¬ p ∣ Nat.card ψ.ker := by
    intro hd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hd
    obtain ⟨⟨a, s⟩, hxk⟩ := x
    have hxk' : ρ a * Ψ s = 1 := hxk
    have hxp : (a, s) ^ p = 1 := by
      have := pow_orderOf_eq_one (⟨(a, s), hxk⟩ : ψ.ker)
      rw [hx] at this
      exact congrArg Subtype.val this
    have hap : a ^ p = 1 := congrArg Prod.fst hxp
    have hsp : s ^ p = 1 := congrArg Prod.snd hxp
    have hacent : a ∈ Subgroup.center SL(2, K) := by
      rw [Subgroup.mem_center_iff]
      intro b
      have h1 : ρ a = (Ψ s)⁻¹ := eq_inv_of_mul_eq_one_left hxk'
      have h2 : Commute (ρ b) (ρ a) := by
        rw [h1]
        exact (hcomm b s).inv_right
      apply hρi
      rw [map_mul, map_mul]
      exact h2.eq
    obtain ⟨c, hc, hca⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hacent
    simp only [Fintype.card_fin] at hc
    have ha2 : a * a = 1 := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, ← hca, ← map_mul, ← pow_two, hc, map_one,
        Matrix.SpecialLinearGroup.coe_one]
    have ha1 : a = 1 := by
      have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).2 (by omega)
      have hd2 : orderOf a ∣ Nat.gcd 2 p :=
        Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one (by rwa [pow_two])) (orderOf_dvd_of_pow_eq_one hap)
      rw [hcop] at hd2
      exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 hd2)
    have hΨs : Ψ s = 1 := by
      rw [ha1, map_one, one_mul] at hxk'
      exact hxk'
    have hs1 : s = 1 :=
      eq_one_of_pow_eq_one_of_not_dvd hcen (hker (MonoidHom.mem_ker.2 hΨs)) hsp
    have hx1 : (⟨(a, s), hxk⟩ : ψ.ker) = 1 := Subtype.ext (Prod.ext ha1 hs1)
    rw [hx1, orderOf_one] at hx
    exact hp.one_lt.ne hx
  obtain ⟨x₀, hx₀, hx₀1, hx₀r⟩ := exists_rootElement_mem_e7D6Group K
  have hBr : Subgroup.closure {b : spinGroup (quadPlus 6 K) | ∃ n : ℕ, b ^ (ringChar K ^ n) = 1} = ⊤ :=
    closure_pow_eq_top_of_quasisimple_of_range (isQuasisimple_spinGroup_quadPlus hn3) Ψ
      (hrange ▸ hx₀) hx₀1 hx₀r
  have hH : ∀ F' : Subgroup (SL(2, K) × spinGroup (quadPlus 6 K)), IsElemAbelian p F' →
      Nat.card F' = p ^ 2 → Subgroup.closure {h | ∃ x ∈ F', x ≠ 1 ∧ Commute h x ∧
        ∃ n : ℕ, h ^ (ringChar K ^ n) = 1} = ⊤ :=
    fun F' hF' hc' => CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311h.closure_uniCen_prod_of_plane
      (fun F'' hF'' => card_le_of_isElemAbelian_specialLinear_two hpK0 hF'')
      (Inputs2311g.closure_pow_ringChar_SL_eq_top 2 K) hBr
      (fun F'' hF'' hc'' => closure_uniCen_spinPlus_odd hK2 (by norm_num) hp hp2 hpK hpq1 F'' hF'' hc'')
      F' hF' hc'
  have h := CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311h.range_le_uniClosure_of_cover ψ hψker hH F
    (hrangeψ ▸ hF) hFp hFc
  rwa [hrangeψ] at h

theorem e7TwoSylowSeven_holds_j : E7TwoSylowSeven :=
  e7TwoSylowSeven_of_frame_inputs e7SevenPlaneWeyl_holds e7SevenFrameDatum_holds e7SplitTorusNonSimple_holds
    e7TorusNormalizesFrame_holds

theorem e7TwoUniNative_odd (K : Type) [Field K] [Finite K] (hK2 : ringChar K ≠ 2) (p : ℕ)
    [hpF : Fact p.Prime] (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card K + 1)
    (E₀ : Subgroup (adjointGroup .E7 K)) (hE₀p : ∀ x ∈ E₀, x ^ p = 1) (hE₀c : Nat.card E₀ = p ^ 2)
    (hN : ¬ NormalizesRGroup (ringChar K) E₀) :
    Subgroup.closure {k | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x ∧ ∃ m : ℕ, k ^ (ringChar K ^ m) = 1} = ⊤ := by
  have hodd : Odd (Nat.card K) := by
    have : Fintype K := Fintype.ofFinite K
    obtain ⟨m, hℓ, hm⟩ := FiniteField.card K (ringChar K)
    rw [Nat.card_eq_fintype_card, hm]
    exact Odd.pow (hℓ.odd_of_ne_two hK2)
  have hSyl : ∃ g : adjointGroup .E7 K, E₀.map (MulAut.conj g).toMonoidHom ≤ e7FrameGroup K := by
    rcases (by omega : p = 5 ∨ p = 6 ∨ p = 7 ∨ p = 8 ∨ p = 9 ∨ p = 10 ∨ 11 ≤ p) with
      rfl | h | rfl | h | h | h | h11
    · exact e7TwoSylowFive_of_odd K hodd hpq E₀ hE₀p hE₀c hN
    · subst h; exact absurd hpF.out (by norm_num)
    · exact e7TwoSylowSeven_holds_j K hpq E₀ hE₀p hE₀c hN
    · subst h; exact absurd hpF.out (by norm_num)
    · subst h; exact absurd hpF.out (by norm_num)
    · subst h; exact absurd hpF.out (by norm_num)
    · exact e7TwoSylow K p h11 hpq E₀ hE₀p hE₀c
  exact CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311f.uniClosure_eq_top_of_two_conj (p := p)
    (e7A1D6 K) (e7FrameGroup K)
    (weylWordElt .E7 K e7Word) e7FrameGroup_le_e7A1D6 e7FrameGroup_le_conj_e7A1D6
    (fun M hX hn => eq_top_of_e7A1D6_le_of_conj_le M hX hn)
    (fun E hE hEp hEc => e7A1D6_le_uniClosure_odd hK2 hpF.out hp5 hpq E hE hEp hEc) E₀ hE₀p hE₀c hSyl

theorem uniSeitzPlanes_E7Two_inner_odd :
    UniSeitzPlanes fun d p E => InnerPlane d p E ∧ 5 ≤ p ∧
      (∃ q : PrimePower, d.1 = .E7 q ∧ orderOf ((q.card : ℕ) : ZMod p) = 2) ∧
      d.1.characteristic ≠ 2 ∧ ¬ NormalizesRSubgroup d E := by
  rintro ⟨d, hv⟩ p hp hp2 hpd _ E hE hc ⟨hin, hp5, ⟨q, hq, h2⟩, hch, hn⟩
  obtain rfl : d = .E7 q := hq
  have hq2 : q.p ≠ 2 := by simpa using hch
  haveI : Fact p.Prime := ⟨hp⟩
  refine uniPlaneGen_cat_odd CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e7
    LieTypeIndex.characteristic_E7 hv hq2 ?_ hE hc hin hn
  intro K _ _ hKq hK2 E₀ hE₀p hE₀c hN
  exact e7TwoUniNative_odd K hK2 p hp5
    (by rw [hKq]; exact Inputs2311h.dvd_add_one_of_orderOf_eq_two_even hp h2) E₀ hE₀p hE₀c hN

end E7TwoOdd

section TwE6TwoOdd

open CFSG.LieType.Chevalley.E6GraphLevi CFSG.LieType.Universal CFSG.LieType.Universal.Spin

set_option linter.unusedSectionVars false

theorem closure_pow_eq_top_of_quasisimple_of_dvd_j {B : Type} [Group B] [Finite B] {r : ℕ} [Fact r.Prime]
    (hB : CFSG.IsQuasisimple B) (hdvd : r ∣ Nat.card B) :
    Subgroup.closure {b : B | ∃ n : ℕ, b ^ (r ^ n) = 1} = ⊤ := by
  have hq : CFSG.IsQuasisimple ↥(⊤ : Subgroup B) := CFSG.IsQuasisimple.of_mulEquiv Subgroup.topEquiv hB
  have hle := CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311f.le_closure_pow_of_quasisimple
    (G := B) (X := ⊤) (r := r) hq (by rw [Subgroup.card_top]; exact hdvd)
  rw [eq_top_iff]
  intro y _
  refine Subgroup.closure_mono ?_ (hle (Subgroup.mem_top y))
  rintro z ⟨-, n, hn⟩
  exact ⟨n, hn⟩

theorem closure_pow_unitarySL_eq_top_j {K : Type} [Field K] [Finite K] {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ ℓ ^ f) :
    Subgroup.closure {b : unitarySL σ | ∃ n : ℕ, b ^ (ℓ ^ n) = 1} = ⊤ := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData ℓ f K :=
    ⟨hℓ, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  haveI : CharP K ℓ := hU.charP
  set e := CFSG.LieType.SeitzGeneration.ExcHigh.TwSU6.unitarySLEquivStated (p := ℓ) hK hσ with he
  have hq2 : ((6 : ℕ), ℓ ^ f) ≠ (3, 2) := fun h => by
    have := (Prod.mk.inj h).1
    omega
  have hqs := (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (F := K) (p := ℓ) (f := f)
    (n := 6) hK (by norm_num) hq2).1
  have hB : CFSG.IsQuasisimple (unitarySL σ) := CFSG.IsQuasisimple.of_mulEquiv e hqs
  have hfin : Finite (unitarySL σ) := Finite.of_equiv _ e.symm.toEquiv
  have hcard := CFSG.GH74.GLS.Stage2.Final.ModelOrd.card_statedSU_int hU (n := 6) (by norm_num)
  have hdvdZ : (ℓ : ℤ) ∣ (Nat.card ↥(CFSG.Open.StatedSU 6 (ℓ ^ f) K) : ℤ) := by
    rw [hcard]
    refine Dvd.dvd.mul_right (dvd_pow ?_ (by norm_num)) _
    rw [Nat.cast_pow]
    exact dvd_pow_self (ℓ : ℤ) (by omega)
  have hdvd : ℓ ∣ Nat.card (unitarySL σ) := by
    rw [Nat.card_congr e.toEquiv]
    exact Int.natCast_dvd_natCast.1 hdvdZ
  exact closure_pow_eq_top_of_quasisimple_of_dvd_j hB hdvd

theorem uniClosure_unitarySL_eq_top_odd {K : Type} [Field K] [Finite K] {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ ℓ ^ f)
    {p : ℕ} (hp : p.Prime) (hpq : p ∣ ℓ ^ f + 1) (F : Subgroup (unitarySL σ))
    (hF : IsElemAbelian p F) (hc : Nat.card F = p ^ 2) :
    Subgroup.closure {g : unitarySL σ | ∃ x ∈ F, x ≠ 1 ∧ Commute g x ∧ ∃ n : ℕ, g ^ (ℓ ^ n) = 1} = ⊤ := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData ℓ f K :=
    ⟨hℓ, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  haveI : CharP K ℓ := hU.charP
  set e := CFSG.LieType.SeitzGeneration.ExcHigh.TwSU6.unitarySLEquivStated (p := ℓ) hK hσ with he
  have hq : ℓ ^ f ≠ 2 := by
    intro h2
    have h2' : 2 ∣ ℓ ^ f := by rw [h2]
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hℓ).1 (Nat.prime_two.dvd_of_dvd_pow h2')
    exact hℓ2 this.symm
  have hcomm : ∀ x ∈ F.map e.toMonoidHom, ∀ y ∈ F.map e.toMonoidHom, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg _ (congrArg Subtype.val (hF.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
  have hexp : ∀ x ∈ F.map e.toMonoidHom, x ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hF.2 x hx, map_one]
  have hcard : Nat.card (F.map e.toMonoidHom) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective e.injective, hc]
  have h := CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311d.uniClosure_unitarySU_of_dvd_add_one
    (n := 5) hU hp hpq hq (F.map e.toMonoidHom) hcomm hexp hcard
  rw [ringChar.eq K ℓ] at h
  have hmap := congrArg (Subgroup.map e.symm.toMonoidHom) h
  rw [Subgroup.map_top_of_surjective _ e.symm.surjective, MonoidHom.map_closure] at hmap
  rw [eq_top_iff, ← hmap, Subgroup.closure_le]
  rintro _ ⟨g, ⟨_, ⟨x, hx, rfl⟩, hx1, hgx, hg2⟩, rfl⟩
  refine Subgroup.subset_closure ⟨x, hx, fun h1 => hx1 (by rw [h1, map_one]), ?_, 1, ?_⟩
  · have h1 : e.symm g * e.symm (e x) = e.symm (e x) * e.symm g := by
      rw [← map_mul, ← map_mul]
      exact congrArg _ hgx
    show e.symm g * x = x * e.symm g
    simpa using h1
  · rw [pow_one]
    change e.symm g ^ ℓ = 1
    rw [← map_pow, hg2, map_one]


theorem exists_rElement_mem_d4Group_j {K : Type} [Field K] (σ : K →+* K) :
    ∃ x ∈ d4Group σ, x ≠ 1 ∧ x ^ ringChar (RingHom.eqLocusField σ (RingHom.id K)) = 1 := by
  obtain ⟨Y, hY1, hYr⟩ := Inputs2311g.exists_sl2_rElement_ne_one (RingHom.eqLocusField σ (RingHom.id K))
  refine ⟨d4Rho σ 0 Y, Subgroup.mem_iSup_of_mem 0 ⟨Y, rfl⟩, ?_, ?_⟩
  · intro h
    exact hY1 (d4Rho_injective σ 0 (h.trans (map_one _).symm))
  · rw [← map_pow, hYr, map_one]

theorem twE6TwoUniNative_odd (K : Type) [Field K] [Finite K] (σ : K ≃+* K) {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 2) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ}
    [hpF : Fact p.Prime] (hp5 : 5 ≤ p) (hpq : p ∣ ℓ ^ f + 1) (E₀ : Subgroup ↥(twistedE6RootGroup K σ))
    (hE₀p : ∀ x ∈ E₀, x ^ p = 1) (hE₀c : Nat.card E₀ = p ^ 2) :
    Subgroup.closure {k | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x ∧ ∃ m : ℕ, k ^ (ℓ ^ m) = 1} = ⊤ := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hK' : Nat.card K = ℓ ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData ℓ f K := ⟨hℓ, hf, hK'⟩
  haveI : CharP K ℓ := hU.charP
  set σ' : K →+* K := σ.toRingHom with hσ'def
  have hσ' : ∀ c, σ' c = c ^ (ℓ ^ f) := hσ
  have hkcard : Nat.card (RingHom.eqLocusField σ' (RingHom.id K)) = ℓ ^ f :=
    CFSG.RankThree.Chevalley.card_eqLocusField_of_pow hℓ hf hK hσ'
  haveI : CharP (RingHom.eqLocusField σ' (RingHom.id K)) ℓ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ hf hkcard
  have hringk : ringChar (RingHom.eqLocusField σ' (RingHom.id K)) = ℓ := ringChar.eq _ ℓ
  have hq2 : 2 ≤ ℓ ^ f := Nat.one_lt_pow (by omega) hℓ.one_lt
  have hpk : ¬ p ∣ Nat.card (RingHom.eqLocusField σ' (RingHom.id K)) := by
    rw [hkcard]
    intro h
    have h1 : p ∣ ℓ ^ f + 1 - ℓ ^ f := Nat.dvd_sub hpq h
    rw [show ℓ ^ f + 1 - ℓ ^ f = 1 by omega] at h1
    exact hpF.out.one_lt.ne' (Nat.dvd_one.1 h1)
  have hpk1 : ¬ p ∣ Nat.card (RingHom.eqLocusField σ' (RingHom.id K)) - 1 := by
    rw [hkcard]
    intro h
    have h1 : p ∣ ℓ ^ f + 1 - (ℓ ^ f - 1) := Nat.dvd_sub hpq h
    rw [show ℓ ^ f + 1 - (ℓ ^ f - 1) = 2 by omega] at h1
    have := Nat.le_of_dvd (by norm_num) h1
    omega
  have hp3 : p ≠ 3 := by omega
  haveI : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  obtain ⟨ψ₁, hk₁, -, hX₁⟩ := CFSG.LieType.SeitzGeneration.ExcHigh.TwFive.twE6SU6Cover_five K σ ℓ f hℓ hf hK hσ
    p hp5 hpq
  obtain ⟨Ψ, hΨker, hΨrange⟩ := exists_psi_d4 hℓ hf σ' hkcard
  haveI := finite_spinPlus_four (RingHom.eqLocusField σ' (RingHom.id K))
  have hcen := not_dvd_card_center_spinPlus_four hpF.out hp5 hpk1
  have hcomm : ∀ t x, Commute (torusG σ' t) (Ψ x) := fun t x => by
    have hmem : Ψ x ∈ d4Group σ' := by
      rw [d4Group, ← hΨrange]
      exact ⟨x, rfl⟩
    exact torusG_commute_d4Group σ' t (Ψ x) hmem
  set ψ₂ := MonoidHom.noncommCoprod (torusG σ') Ψ hcomm with hψ₂
  have hk₂ : ¬ p ∣ Nat.card ψ₂.ker :=
    not_dvd_card_ker_noncommCoprod_tw hpF.out _ _ hcomm (not_dvd_card_ker_torusG σ' hpF.out hp3) hΨker
      hcen
  have hdr : d4Group σ' ≤ ψ₂.range := by
    rw [d4Group, ← hΨrange]
    rintro _ ⟨x, rfl⟩
    refine ⟨(1, x), ?_⟩
    change torusG σ' 1 * Ψ x = Ψ x
    rw [map_one, one_mul]
  have htr : (torusG σ').range ≤ ψ₂.range := by
    rintro _ ⟨t, rfl⟩
    refine ⟨(t, 1), ?_⟩
    change torusG σ' t * Ψ 1 = torusG σ' t
    rw [map_one, mul_one]
  have hP₂ : frameTorusGroup σ' ≤ ψ₂.range := by
    refine sup_le (iSup_le fun i => ?_) htr
    fin_cases i
    · exact (le_iSup (fun i => (d4Rho σ' i).range) 0).trans hdr
    · exact (le_iSup (fun i => (d4Rho σ' i).range) 2).trans hdr
    · exact (le_iSup (fun i => (d4Rho σ' i).range) 3).trans hdr
    · exact (frameHom_three_le_d4Group σ').trans hdr
  have hP₁ : frameTorusGroup σ' ≤ ψ₁.range := le_sup_left.trans hX₁
  obtain ⟨g, hg⟩ : ∃ g : ↥(twistedE6RootGroup K σ),
      E₀.map (MulAut.conj g).toMonoidHom ≤ frameTorusGroup σ' := by
    rcases (by omega : p = 5 ∨ p = 6 ∨ 7 ≤ p) with rfl | rfl | hp7
    ·
      obtain ⟨e₂⟩ := CFSG.LieType.SeitzGeneration.ExcHigh.TwFive.exists_mulEquiv_sl2_su2 (K := K) hK σ' hσ'
      let θ : SL(2, RingHom.eqLocusField σ' (RingHom.id K)) × unitarySL σ' ≃*
          CFSG.ClassicalGroups.UnitaryFlag.unitarySU ℓ f K 2 ×
            CFSG.ClassicalGroups.UnitaryFlag.unitarySU ℓ f K 6 :=
        e₂.prodCongr (CFSG.LieType.SeitzGeneration.ExcHigh.TwSU6.unitarySLEquivStated hK hσ')
      obtain ⟨Ew, hEwe, hEwc, hEwle⟩ := CFSG.LieType.SeitzGeneration.ExcHigh.TwFive.exists_elemAbelian_six hℓ hf K
        hK σ hσ hpq
      have hEwr : Ew ≤ ψ₁.range := hEwle.trans hP₁
      obtain ⟨Ew', hEw'e, hEw'm, hEw'c⟩ := CFSG.LieType.SeitzGeneration.ExcHigh.TwFive.exists_lift_of_le_range ψ₁
        hk₁ hEwr hEwe
      have hord := CFSG.LieType.SeitzGeneration.ExcHigh.TwFive.five_hord hℓ hf hK σ hσ hpq
      have hcomm₀ : ∀ a ∈ E₀, ∀ b ∈ E₀, a * b = b * a := by
        intro a ha b hb
        let _ : CommGroup E₀ := IsPGroup.commGroupOfCardEqPrimeSq hE₀c
        exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : E₀) ⟨b, hb⟩)
      have hE₀e : IsElemAbelian 5 E₀ :=
        ⟨IsMulCommutative.of_comm fun a b => Subtype.ext (hcomm₀ a a.2 b b.2), hE₀p⟩
      obtain ⟨g, E', hE'e, hE'm⟩ := CFSG.LieType.SeitzGeneration.ExcHigh.TwFive.exists_conj_lift_elemAbelian ψ₁ hk₁
        hord E₀ hE₀e
      obtain ⟨c, hc⟩ := CFSG.LieType.SeitzGeneration.ExcHigh.TwFive.exists_conj_le_toral_of_equiv hU hpq θ Ew' hEw'e
        (hEw'c.trans hEwc) E' hE'e
      refine ⟨(ψ₁ c)⁻¹ * g, ?_⟩
      rintro y ⟨e, he, rfl⟩
      have h1 : g * e * g⁻¹ ∈ E₀.map (MulAut.conj g).toMonoidHom :=
        ⟨e, he, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
      rw [← hE'm] at h1
      obtain ⟨y', hy', hy'e⟩ := h1
      obtain ⟨z, hz, hzy⟩ := hc hy'
      have hzψ : ψ₁ z ∈ Ew := hEw'm ▸ ⟨z, hz, rfl⟩
      have hψ : g * e * g⁻¹ = ψ₁ c * ψ₁ z * (ψ₁ c)⁻¹ := by
        rw [← hy'e, ← hzy]
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
      have hconj : (MulAut.conj ((ψ₁ c)⁻¹ * g)).toMonoidHom e = ψ₁ z := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev, inv_inv]
        calc (ψ₁ c)⁻¹ * g * e * (g⁻¹ * ψ₁ c) = (ψ₁ c)⁻¹ * (g * e * g⁻¹) * ψ₁ c := by group
          _ = ψ₁ z := by rw [hψ]; group
      rw [hconj]
      exact hEwle hzψ
    · exact absurd hpF.out (by norm_num)
    · have hpq' : p ∣ Nat.card (RingHom.eqLocusField σ' (RingHom.id K)) + 1 := by
        rw [hkcard]
        exact hpq
      exact exists_conj_le_frame_torus (frameHom σ') (frameHom_injective σ')
        (fun i j hij A B => frameHom_commute σ' hij A B) (torusG σ').range
        (fun a ha i y => by
          obtain ⟨t, rfl⟩ := ha
          exact torusG_commute_frame _ (frameHom_mem_rootPair σ') t i y)
        hp5 hpq' (factorization_card_le_frame_torusG hℓ hf K hK σ hσ hpF.out hp7 hpq) E₀ hE₀p
  refine CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311f.uniClosure_eq_top_of_conj g ?_
  set E₁ := E₀.map (MulAut.conj g).toMonoidHom with hE₁
  have hE₁p : ∀ x ∈ E₁, x ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hE₀p x hx, map_one]
  have hE₁c : Nat.card E₁ = p ^ 2 := by
    rw [hE₁, Subgroup.card_map_of_injective (MulAut.conj g).injective, hE₀c]
  set M := Subgroup.closure {k | ∃ x ∈ E₁, x ≠ 1 ∧ Commute k x ∧ ∃ m : ℕ, k ^ (ℓ ^ m) = 1} with hM
  have hpk0 := natCast_ne_zero_of_not_dvd_card hpF.out hpk
  have hBr₁ : Subgroup.closure {b : unitarySL σ' | ∃ n : ℕ, b ^ (ℓ ^ n) = 1} = ⊤ :=
    closure_pow_unitarySL_eq_top_j hℓ hf hK hσ'
  have hSL : Subgroup.closure {g : SL(2, RingHom.eqLocusField σ' (RingHom.id K)) |
      ∃ m : ℕ, g ^ (ℓ ^ m) = 1} = ⊤ := by
    have h := Inputs2311g.closure_pow_ringChar_SL_eq_top 2 (RingHom.eqLocusField σ' (RingHom.id K))
    rw [hringk] at h
    exact h
  have hH₁ : ∀ F : Subgroup (SL(2, RingHom.eqLocusField σ' (RingHom.id K)) × unitarySL σ'),
      IsElemAbelian p F → Nat.card F = p ^ 2 →
        Subgroup.closure {h | ∃ x ∈ F, x ≠ 1 ∧ Commute h x ∧ ∃ n : ℕ, h ^ (ℓ ^ n) = 1} = ⊤ :=
    fun F hF hc => CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311h.closure_uniCen_prod_of_plane
      (fun F' hF' => card_le_of_isElemAbelian_specialLinear_two hpk0 hF') hSL hBr₁
      (fun F' hF' hc' => uniClosure_unitarySL_eq_top_odd hℓ hℓ2 hf hK hσ' hpF.out hpq F' hF' hc') F hF hc
  have hM₁ : ψ₁.range ≤ M :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311h.range_le_uniClosure_of_cover ψ₁ hk₁ hH₁ E₁
      (hg.trans hP₁) hE₁p hE₁c
  obtain ⟨x₀, hx₀, hx₀1, hx₀r⟩ := exists_rElement_mem_d4Group_j σ'
  rw [hringk] at hx₀r
  have hBr₂ : Subgroup.closure {b : spinGroup (Spin.quadPlus 4 (RingHom.eqLocusField σ' (RingHom.id K))) |
      ∃ n : ℕ, b ^ (ℓ ^ n) = 1} = ⊤ :=
    closure_pow_eq_top_of_quasisimple_of_range (isQuasisimple_spinGroup_quadPlus (by norm_num)) Ψ
      (by rw [hΨrange]; exact hx₀) hx₀1 hx₀r
  have hk2 : ringChar (RingHom.eqLocusField σ' (RingHom.id K)) ≠ 2 := by rw [hringk]; exact hℓ2
  have hspin : ∀ F' : Subgroup (spinGroup (Spin.quadPlus 4 (RingHom.eqLocusField σ' (RingHom.id K)))),
      IsElemAbelian p F' → Nat.card F' = p ^ 2 →
        Subgroup.closure {b | ∃ x ∈ F', x ≠ 1 ∧ Commute b x ∧ ∃ n : ℕ, b ^ (ℓ ^ n) = 1} = ⊤ := by
    intro F' hF' hc'
    have h := closure_uniCen_spinPlus_odd hk2 (by norm_num) hpF.out (by omega) hpk hpk1 F' hF' hc'
    rw [hringk] at h
    exact h
  have hM₂ := Inputs2311i.map_le_uniClosure_of_cover ψ₂ hk₂ _
    (fun F hF hc => Inputs2311i.range_inr_le_uniClosure_prod hBr₂ hspin F hF hc)
    E₁ (hg.trans hP₂) hE₁p hE₁c
  have hd4M : d4Group σ' ≤ M := by
    rw [d4Group, ← hΨrange]
    rintro _ ⟨x, rfl⟩
    have h1 : ψ₂ ((MonoidHom.inr _ _) x) = Ψ x := by
      change torusG σ' 1 * Ψ x = Ψ x
      rw [map_one, one_mul]
    rw [← h1]
    exact hM₂ ⟨(MonoidHom.inr _ _) x, ⟨x, rfl⟩, rfl⟩
  have hX₁' : ∀ y : ↥(graphFixedRootGroup TwistTag.E6 K σ'),
      y ∈ leviRootGroups σ' → y ∈ ψ₁.range := fun y hy => hX₁ (Subgroup.mem_sup_right hy)
  refine eq_top_of_orbitRankOneGroup_le M fun a => ?_
  refine le_map_subtype_of_mem (orbitRankOneGroup_le_graphFixedRootGroup' _ _) fun y hy => ?_
  match a, hy with
  | ⟨0, _⟩, hy =>
    exact hM₁ (hX₁' y (Subgroup.mem_subgroupOf.2
      (Subgroup.mem_sup_left (Subgroup.mem_sup_left hy))))
  | ⟨1, _⟩, hy =>
    exact hM₁ (hX₁' y (Subgroup.mem_subgroupOf.2
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right hy))))
  | ⟨2, _⟩, hy =>
    exact hM₁ (hX₁' y (Subgroup.mem_subgroupOf.2 (Subgroup.mem_sup_right hy)))
  | ⟨3, _⟩, hy =>
    obtain ⟨A, hA⟩ := orbitRankOneGroup_le_range_rankOneFix σ' orbCenter orbCenter_card hy
    have hyeq : y = centerHom σ' A := Subtype.ext hA.symm
    rw [hyeq]
    exact hd4M (Subgroup.mem_iSup_of_mem 1 ⟨A, rfl⟩)
  | ⟨n + 4, h⟩, _ => exact absurd h (by change ¬ n + 4 < 4; omega)

end TwE6TwoOdd

section TwE6TwoCatOdd

set_option linter.unusedSectionVars false


theorem uniSeitzPlanes_twE6Two_inner_odd :
    UniSeitzPlanes fun d p E => InnerPlane d p E ∧ 5 ≤ p ∧ ¬ NormalizesRSubgroup d E ∧
      ∃ q : PrimePower, d.1 = .twistedE6 q ∧ q.p ≠ 2 ∧ p ∣ q.card + 1 := by
  rintro ⟨d, hv⟩ p hp hp2 hpd _ E hE hc ⟨hin, hp5, hn, q, hq, hq2, hpq⟩
  obtain rfl : d = .twistedE6 q := hq
  obtain ⟨K, _, σ, hK, hσ, ⟨e⟩⟩ := exists_catEquiv_twistedE6 q hv
  have hKfin : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]; exact pow_ne_zero _ (pow_ne_zero _ q.prime_p.ne_zero))
  haveI : Fact p.Prime := ⟨hp⟩
  have hZ : Subgroup.center ↥(twistedE6RootGroup K σ) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  have hinj := conj_injective_of_mulEquiv e (conj_injective_of_center_eq_bot hZ)
  have hpq' : p ∣ q.p ^ q.exponent + 1 := by
    rw [← PrimePower.card_def]
    exact hpq
  show UniPlaneGen (LieTypeIndex.twistedE6 q).characteristic E
  rw [LieTypeIndex.characteristic_twistedE6]
  refine CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311f.uniPlaneGen_of_native_uniClosure
    (p := p) (r := q.p) e hinj (fun E₀ h1 h2 _ => twE6TwoUniNative_odd K σ q.prime_p hq2 q.exponent_pos hK hσ hp5
      hpq' E₀ h1 h2) hE hc hin ?_
  rintro ⟨R, hR1, hRp, hRn⟩
  exact hn ⟨R, hR1, by rw [LieTypeIndex.characteristic_twistedE6]; exact hRp, hRn⟩

end TwE6TwoCatOdd

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311j
