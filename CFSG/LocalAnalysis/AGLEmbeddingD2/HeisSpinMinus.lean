module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.SquareSpinMinus
public import CFSG.LocalAnalysis.AGLEmbeddingD2.HeisEngine
public import CFSG.LocalAnalysis.AGLEmbeddingD2.PartStab
import CFSG.Timmesfeld.RankTwo.LevisBRankOne

public section

namespace CFSG.AGLEmbeddingD2.HeisSpinMinus

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.Steinberg CFSG.AGLEmbeddingD2.ParabLevi
  CFSG.LieType.CurtisTits CFSG.AGLEmbedding.ParabPrime CFSG.LieType.RootSystem
  CFSG.AGLEmbedding.ToralCensus CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbeddingD2.HeisEngine
  CFSG.AGLEmbeddingD2.SquareSpinMinus

section SL2

variable {k : Type} [Field k]

theorem sl2Lower_sq [CharP k 2] (c : k) : (sl2Lower c) ^ 2 = 1 := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, coe_sl2Lower]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two]
  grind

theorem sl2Upper_sq [CharP k 2] (c : k) : (sl2Upper c) ^ 2 = 1 := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, coe_sl2Upper]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two]
  grind

theorem sl2Upper_ne_one : sl2Upper (1 : k) ≠ 1 := by
  intro h
  have := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) k =>
    (A : Matrix (Fin 2) (Fin 2) k) 0 1) h
  simp [coe_sl2Upper] at this

theorem sl2_upper_lower_pow_five [CharP k 2] {ω : k} (hω : ω ^ 2 + ω + 1 = 0) :
    (sl2Upper (1 : k) * sl2Lower ω) ^ 5 = 1 := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_mul, coe_sl2Upper,
    coe_sl2Lower]
  simp only [pow_succ, pow_zero, one_mul, Matrix.mul_fin_two, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> grind

theorem exists_root_of_card_eq_four_pow [Finite k] {m : ℕ} (h : Nat.card k = 4 ^ m) :
    ∃ ω : k, ω ^ 2 + ω + 1 = 0 := by
  have h3 : 3 ∣ Nat.card k - 1 := by
    rw [h]
    simpa using Nat.sub_dvd_pow_sub_pow 4 1 m
  obtain ⟨ω, hω⟩ := SquareLinear.exists_orderOf_eq_three h3
  have h1 : (ω : k) ^ 3 = 1 := by
    have := congrArg Units.val (show ω ^ 3 = 1 by rw [← hω, pow_orderOf_eq_one])
    simpa using this
  have hne : (ω : k) ≠ 1 := by
    intro h'
    have : ω = 1 := Units.ext h'
    rw [this, orderOf_one] at hω
    omega
  have : ((ω : k) - 1) * ((ω : k) ^ 2 + ω + 1) = 0 := by linear_combination h1
  exact ⟨ω, (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)⟩

theorem exists_hom_of_rankOneRels' {G : Type*} [Group G] [Finite k] (R : RankOneRels G k) :
    ∃ Θ : Matrix.SpecialLinearGroup (Fin 2) k →* G,
      (∀ a, Θ (sl2Upper a) = R.x a) ∧ ∀ a, Θ (sl2Lower a) = R.y a := by
  set P := CFSG.Timmesfeld.RankTwo.rankOneRelsProd (CFSG.SectionRank.EvenCover.sl2Rels k) R
    with hP
  have hinj : Set.InjOn (MonoidHom.fst (M := Matrix.SpecialLinearGroup (Fin 2) k) (N := G)) P.sub :=
    P.injOn_sub (MonoidHom.fst _ _) (MonoidHom.id _) Function.injective_id (fun _ => rfl)
      (fun _ => rfl)
  have hmap : P.sub.map (MonoidHom.fst _ _) = ⊤ := by
    rw [eq_top_iff]
    intro g _
    have hg := Sp.mem_closure_sl2 g
    rw [RankOneRels.sub, MonoidHom.map_closure, Set.image_union]
    convert hg using 3
    · ext g
      simp [P, CFSG.Timmesfeld.RankTwo.rankOneRelsProd, CFSG.SectionRank.EvenCover.sl2Rels_x]
    · ext g
      simp [P, CFSG.Timmesfeld.RankTwo.rankOneRelsProd, CFSG.SectionRank.EvenCover.sl2Rels_y]
  let f : P.sub →* Matrix.SpecialLinearGroup (Fin 2) k := (MonoidHom.fst _ _).comp P.sub.subtype
  have hf : Function.Bijective f := by
    refine ⟨fun a b hab => Subtype.ext (hinj a.2 b.2 hab), fun g => ?_⟩
    have hg : g ∈ P.sub.map (MonoidHom.fst _ _) := by rw [hmap]; exact Subgroup.mem_top g
    obtain ⟨p, hp, rfl⟩ := hg
    exact ⟨⟨p, hp⟩, rfl⟩
  let e := MulEquiv.ofBijective f hf
  refine ⟨(MonoidHom.snd _ _).comp (P.sub.subtype.comp e.symm.toMonoidHom), fun a => ?_,
    fun a => ?_⟩
  · have hx : e.symm (sl2Upper a) = ⟨P.x a, P.x_mem_sub a⟩ :=
      e.symm_apply_eq.2 (Subtype.ext rfl)
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hx]
    rfl
  · have hy : e.symm (sl2Lower a) = ⟨P.y a, P.y_mem_sub a⟩ :=
      e.symm_apply_eq.2 (Subtype.ext rfl)
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hy]
    rfl

end SL2

section Real

variable {K : Type*} [Group K]

@[expose] def HasRealFive (D : UniversalRootDatum K) (i : Fin D.rank) : Prop :=
  ∃ x ∈ D.rootGroup (Pi.single i 1), ∃ y ∈ D.rootGroup (-Pi.single i 1),
    x ^ 2 = 1 ∧ y ^ 2 = 1 ∧ (x * y) ^ 5 = 1 ∧ x ≠ 1

theorem mul_ne_one_of_rootGroups {D : UniversalRootDatum K} {n : Fin D.rank → K}
    {H : Fin D.rank → Subgroup K} (hext : SteinbergExtras D n H) {i : Fin D.rank} {x y : K}
    (hx : x ∈ D.rootGroup (Pi.single i 1)) (hy : y ∈ D.rootGroup (-Pi.single i 1)) (hx1 : x ≠ 1)
    (hx2 : x ^ 2 = 1) : x * y ≠ 1 := by
  intro h
  have h4 : x = y := by
    rw [eq_inv_of_mul_eq_one_right h, inv_eq_of_mul_eq_one_right (by rw [← pow_two, hx2])]
  have hα : (Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i
  have hα' : (-Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem _ hα
  have hxU : x ∈ posUnipotent D := rootGroup_le_posUnipotent hα (ht_single_pos i) hx
  have hyU : y ∈ negUnipotent D := rootGroup_le_negUnipotent hα' (by
    rw [ht_neg]
    have := ht_single_pos (D := D) i
    omega) hy
  have hmem : x ∈ posUnipotent D ⊓ negUnipotent D := ⟨hxU, h4 ▸ hyU⟩
  rw [posUnipotent_inf_negUnipotent hext, Subgroup.mem_bot] at hmem
  exact hx1 hmem

theorem HasRealFive.realOver {D : UniversalRootDatum K} {n : Fin D.rank → K}
    {H : Fin D.rank → Subgroup K} (hext : SteinbergExtras D n H) {i : Fin D.rank}
    (h : HasRealFive D i) {Y : Type*} [Group Y] {π : K →* Y} {J : Subgroup Y}
    (hL : rankOne D.rootGroup i ≤ J.comap π) : RealOver 5 π (rankOne D.rootGroup i) J := by
  obtain ⟨x, hx, y, hy, hx2, hy2, h5, hx1⟩ := h
  have hxL : x ∈ rankOne D.rootGroup i := le_sup_left (a := D.rootGroup (Pi.single i 1)) hx
  have hyL : y ∈ rankOne D.rootGroup i := le_sup_right (b := D.rootGroup (-Pi.single i 1)) hy
  refine RealOver.of_involutions' (by decide) hxL hyL hx2 hy2 h5
    (mul_ne_one_of_rootGroups hext hx hy hx1 hx2) ?_
  rw [map_mul]
  exact mul_mem (hL hxL) (hL hyL)

theorem HasSL2Node.hasRealFive {D : UniversalRootDatum K} {i : Fin D.rank} {F : Type} [Field F]
    [CharP F 2] {ω : F} (hω : ω ^ 2 + ω + 1 = 0) (h : HasSL2Node D i F) : HasRealFive D i := by
  obtain ⟨φ, hφ, hx, hy⟩ := h
  refine ⟨φ (sl2Upper 1), hx 1, φ (sl2Lower ω), hy ω, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, sl2Upper_sq, map_one]
  · rw [← map_pow, sl2Lower_sq, map_one]
  · rw [← map_mul, ← map_pow, sl2_upper_lower_pow_five hω, map_one]
  · intro h1
    exact sl2Upper_ne_one (hφ (h1.trans (map_one φ).symm))

end Real

section Minus

variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
  (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)

include hirr in
theorem hasRealFive_spinMinus_short {k : Fin (n - 1)} (hk : ¬k.val + 1 < n - 1) :
    HasRealFive (minusDatum n hirr) k := by
  have := fact_shortField hirr
  have := finite_shortField (b := b) (c := c)
  have : CharP (ShortField b c) 2 :=
    charP_of_injective_algebraMap (algebraMap F (ShortField b c)).injective 2
  obtain ⟨f, -, hcard⟩ := exists_card_eq_two_pow F
  obtain ⟨ω, hω⟩ : ∃ ω : ShortField b c, ω ^ 2 + ω + 1 = 0 :=
    exists_root_of_card_eq_four_pow (m := f) (by
      rw [CFSG.LieType.Steinberg.CentralExt.SpinMinusClosed.card_shortField, hcard, ← pow_mul,
        mul_comm, pow_mul]
      norm_num)
  obtain ⟨Θ, hU, hL⟩ := exists_hom_of_rankOneRels' (shortRels n hirr k)
  refine ⟨(shortRels n hirr k).x 1, (mem_minusRootGroup_single_iff hirr hk _).2 ⟨1, rfl⟩,
    (shortRels n hirr k).y ω, (mem_minusRootGroup_neg_single_iff hirr hk _).2 ⟨ω, rfl⟩,
    ?_, ?_, ?_, fun h => ?_⟩
  · rw [pow_two, ← RankOneRels.x_add, CharTwo.add_self_eq_zero, RankOneRels.x_zero]
  · rw [pow_two, ← RankOneRels.y_add, CharTwo.add_self_eq_zero, RankOneRels.y_zero]
  · rw [← hU 1, ← hL ω, ← map_mul, ← map_pow, sl2_upper_lower_pow_five hω, map_one]
  · exact one_ne_zero (shortRels_x_injective hirr k (h.trans (RankOneRels.x_zero _).symm))

include hirr in
theorem hasRealFive_spinMinus (hω : ∃ ω : F, ω ^ 2 + ω + 1 = 0) (i : Fin (n - 1)) :
    HasRealFive (minusDatum n hirr) i := by
  by_cases hk : i.val + 1 < n - 1
  · obtain ⟨ω, hω⟩ := hω
    exact HasSL2Node.hasRealFive hω (hasSL2Node_spinMinus_long hirr hk)
  · exact hasRealFive_spinMinus_short hirr hk

end Minus

section Torus

variable {n : ℕ} {F : Type} [Field F] {b c : F}

theorem exists_torus_pow (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {r : ℕ} (hr : r ≠ 1) {ω : Fˣ}
    (hω : orderOf ω = r) (k : Fin (n - 1)) : ∃ x ∈ minusTorus n hirr k, x ^ r = 1 ∧ x ≠ 1 := by
  have hωr : ω ^ r = 1 := by rw [← hω, pow_orderOf_eq_one]
  have hω1 : ω ≠ 1 := fun h => hr (by rw [h, orderOf_one] at hω; exact hω.symm)
  by_cases hk : k.val + 1 < n - 1
  · refine ⟨(minusFrame n b c).longTorus (succ_ne_of_lt n hk) true false ω, ?_, ?_, ?_⟩
    · rw [minusTorus_of_lt n hirr hk]
      exact ⟨ω, rfl⟩
    · rw [← map_pow, hωr, map_one]
    · intro h
      rw [HypFrame.longTorus_apply] at h
      have := SpinFrame.longSL2_injective (minusFrame n b c).toHypFrame (succ_ne_of_lt n hk) true
        false (h.trans (map_one _).symm)
      exact hω1 (eq_one_of_diagSL2_eq_one this)
  · refine ⟨(minusFrame n b c).shortTorus k true ω, ?_, ?_, ?_⟩
    · rw [minusTorus_of_not_lt n hirr hk, minusFrame_shortTorus_eq n hirr k ω]
      exact shortTorusElt_mem n hirr k (smul_ne_zero ω.ne_zero planeOne_ne_zero)
    · rw [← map_pow, hωr, map_one]
    · intro h
      rw [OddFrame.shortTorus_apply] at h
      have := SpinOdd.shortSL2_injective (minusFrame n b c) k true (h.trans (map_one _).symm)
      exact hω1 (eq_one_of_diagSL2_eq_one this)

variable [Finite F]

theorem three_le_pRank_five_of_torus (hn : 4 ≤ n) (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {Y : Type} [Group Y] [Finite Y] [Finite (spinGroup (quadMinus n F b c))]
    {π : spinGroup (quadMinus n F b c) →* Y} {M : ℕ} {J : Subgroup Y}
    (hb : BorelQuotient (minusDatum n hirr) (minusWeyl n hirr) (minusTorus n hirr) π M)
    (hBJ : borel (minusDatum n hirr) (minusTorus n hirr) ≤ J.comap π)
    (hπ5 : Nat.Coprime 5 (Nat.card π.ker)) (h5 : 5 ∣ Nat.card F - 1) :
    3 ≤ CFSG.Open.pRank 5 J := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h : 5 ∣ Nat.card Fˣ := by rw [Nat.card_units]; exact h5
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' 5 h
  obtain ⟨x, hxH, hx5, hx1⟩ := exists_torus_pow hirr (n := n) (by norm_num) hω
    (⟨0, by omega⟩ : Fin (n - 1))
  obtain ⟨y, hyH, hy5, hy1⟩ := exists_torus_pow hirr (n := n) (by norm_num) hω
    (⟨1, by omega⟩ : Fin (n - 1))
  obtain ⟨z, hzH, hz5, hz1⟩ := exists_torus_pow hirr (n := n) (by norm_num) hω
    (⟨2, by omega⟩ : Fin (n - 1))
  exact three_le_pRank_of_torus hb.extras hπ5 hBJ
    (a := (⟨0, by omega⟩ : Fin (n - 1))) (b := (⟨1, by omega⟩ : Fin (n - 1)))
    (c := (⟨2, by omega⟩ : Fin (n - 1)))
    (fun h => absurd (congrArg Fin.val h) (by simp)) (fun h => absurd (congrArg Fin.val h)
      (by simp)) (fun h => absurd (congrArg Fin.val h) (by simp)) hxH hyH hzH hx5 hy5 hz5 hx1 hy1
    hz1

end Torus

section B3

variable {n : ℕ} {F : Type} [Field F] {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)

theorem three_le_pRank_five_of_orth {Y : Type*} [Group Y]
    {π : spinGroup (quadMinus n F b c) →* Y} {M : ℕ} {J : Subgroup Y}
    (hb : BorelQuotient (minusDatum n hirr) (minusWeyl n hirr) (minusTorus n hirr) π M)
    (hBJ : borel (minusDatum n hirr) (minusTorus n hirr) ≤ J.comap π)
    (hr : ∀ i, HasRealFive (minusDatum n hirr) i)
    {X : Type*} [Group X] [Finite X] (ρ : X →* Y) (hρ : Function.Surjective ρ)
    (hρker : ρ.ker ≤ Subgroup.center X) {x y z : Fin (minusDatum n hirr).rank}
    (hxy : x.val + 2 ≤ y.val) (hyz : y.val + 2 ≤ z.val)
    (hx : x ∈ negIndices (minusDatum n hirr) (J.comap π))
    (hy : y ∈ negIndices (minusDatum n hirr) (J.comap π))
    (hz : z ∈ negIndices (minusDatum n hirr) (J.comap π)) :
    3 ≤ CFSG.Open.pRank 5 (J.comap ρ) := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hext := hb.extras
  have hne : ∀ {u v : Fin (minusDatum n hirr).rank}, u.val + 2 ≤ v.val → u ≠ v :=
    fun {u v} h h' => by rw [h'] at h; omega
  exact three_le_pRank_of_triple (by decide) hb.ker_central ρ hρ hρker
    (commutes_rankOne_of_cartan_eq_zero hext (hne hxy) (cartan_minusDatum_eq_zero hirr hxy))
    (commutes_rankOne_of_cartan_eq_zero hext (hne (by omega : x.val + 2 ≤ z.val))
      (cartan_minusDatum_eq_zero hirr (by omega)))
    (commutes_rankOne_of_cartan_eq_zero hext (hne hyz) (cartan_minusDatum_eq_zero hirr hyz))
    ((hr x).realOver hext (rankOne_le_of_mem_negIndices hBJ hx))
    ((hr y).realOver hext (rankOne_le_of_mem_negIndices hBJ hy))
    ((hr z).realOver hext (rankOne_le_of_mem_negIndices hBJ hz))

theorem three_le_pRank_five_of_B3 {Y : Type*} [Group Y]
    {π : spinGroup (quadMinus n F b c) →* Y} {M : ℕ} {J : Subgroup Y}
    (hb : BorelQuotient (minusDatum n hirr) (minusWeyl n hirr) (minusTorus n hirr) π M)
    (hBJ : borel (minusDatum n hirr) (minusTorus n hirr) ≤ J.comap π)
    (hr : ∀ i, HasRealFive (minusDatum n hirr) i)
    {X : Type*} [Group X] [Finite X] (ρ : X →* Y) (hρ : Function.Surjective ρ)
    (hρker : ρ.ker ≤ Subgroup.center X) {p l s : Fin (minusDatum n hirr).rank}
    (hpl : p.val + 1 = l.val) (hls : l.val + 1 = s.val) (hs : s.val + 2 = n)
    (hp : p ∈ negIndices (minusDatum n hirr) (J.comap π))
    (hl : l ∈ negIndices (minusDatum n hirr) (J.comap π))
    (hs' : s ∈ negIndices (minusDatum n hirr) (J.comap π)) :
    3 ≤ CFSG.Open.pRank 5 (J.comap ρ) := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hct := hb.ct
  have hext := hb.extras
  have hps : p ≠ s := fun h => by rw [h] at hpl; omega
  have hx := ((actsAs_n hct l).mul (actsAs_n hct s)).mul (actsAs_n hct l)
  have hβ := toStdB_weylAction_w hirr hpl hls hs
  have hxJ : π (minusWeyl n hirr l * minusWeyl n hirr s * minusWeyl n hirr l) ∈ J := by
    have hL : ∀ k ∈ negIndices (minusDatum n hirr) (J.comap π), π (minusWeyl n hirr k) ∈ J :=
      fun k hk => rankOne_le_of_mem_negIndices hBJ hk (hct.n_mem k)
    rw [map_mul, map_mul]
    exact mul_mem (mul_mem (hL l hl) (hL s hs')) (hL l hl)
  have hRp := (hr p).realOver hext (rankOne_le_of_mem_negIndices hBJ hp)
  refine three_le_pRank_of_triple (by decide) hb.ker_central ρ hρ hρker
    (commutes_rankOne_of_cartan_eq_zero hext hps
      (cartan_minusDatum_eq_zero hirr (i := p) (j := s) (by omega)))
    (commutes_rankOne_map_conj hext hx p p (linIndepPair_p hirr hpl hβ)
      (by simpa using openCone_p_eq_empty hirr hpl hβ (Or.inl rfl))
      (by simpa using openCone_p_eq_empty hirr hpl hβ (Or.inr rfl)))
    (commutes_rankOne_map_conj hext hx s p (linIndepPair_s hirr hpl hls hs hβ)
      (by simpa using openCone_s_eq_empty hirr hpl hls hs hβ (Or.inl rfl))
      (by simpa using openCone_s_eq_empty hirr hpl hls hs hβ (Or.inr rfl)))
    hRp ((hr s).realOver hext (rankOne_le_of_mem_negIndices hBJ hs')) (hRp.conj hxJ)

end B3

section Matrices

variable {F : Type} [Field F]

@[expose] def matX : Matrix (Fin 4) (Fin 4) F := !![1, 1, 0, 0; 0, 1, 0, 0; 0, 1, 1, 1; 0, 0, 0, 1]

@[expose] def matY : Matrix (Fin 4) (Fin 4) F := !![1, 0, 0, 0; 1, 1, 1, 0; 0, 0, 1, 0; 0, 0, 1, 1]

@[expose] def matM : Matrix (Fin 4) (Fin 4) F := !![0, 1, 1, 0; 1, 1, 1, 0; 1, 1, 1, 1; 0, 0, 1, 1]

@[expose] def matM2 : Matrix (Fin 4) (Fin 4) F := !![0, 0, 0, 1; 0, 1, 1, 1; 0, 1, 0, 0; 1, 1, 0, 0]

@[expose] def matM4 : Matrix (Fin 4) (Fin 4) F := !![1, 1, 0, 0; 1, 1, 1, 1; 0, 1, 1, 1; 0, 1, 1, 0]

@[expose] def transv (i j : Fin 4) (t : F) : Matrix (Fin 4) (Fin 4) F :=
  1 + t • Matrix.single i j (1 : F)

theorem matX_eq : transv 0 1 (1 : F) * transv 2 3 1 * transv 2 1 1 = matX := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matX, transv, Matrix.mul_apply, Matrix.single_apply, Fin.sum_univ_four]

theorem matY_eq : transv 1 2 (1 : F) * transv 1 0 1 * transv 3 2 1 = matY := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matY, transv, Matrix.mul_apply, Matrix.single_apply, Fin.sum_univ_four]

variable [CharP F 2]

theorem matX_sq : (matX : Matrix (Fin 4) (Fin 4) F) ^ 2 = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  rw [pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matX, Matrix.mul_apply, Fin.sum_univ_four] <;> grind

theorem matY_sq : (matY : Matrix (Fin 4) (Fin 4) F) ^ 2 = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  rw [pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matY, Matrix.mul_apply, Fin.sum_univ_four] <;> grind

theorem matX_mul_matY : (matX : Matrix (Fin 4) (Fin 4) F) * matY = matM := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matX, matY, matM, Matrix.mul_apply, Fin.sum_univ_four] <;>
    grind

theorem matM_sq : (matM : Matrix (Fin 4) (Fin 4) F) * matM = matM2 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matM, matM2, Matrix.mul_apply, Fin.sum_univ_four] <;> grind

theorem matM2_sq : (matM2 : Matrix (Fin 4) (Fin 4) F) * matM2 = matM4 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matM2, matM4, Matrix.mul_apply, Fin.sum_univ_four] <;>
    grind

theorem matM_pow_five : (matM : Matrix (Fin 4) (Fin 4) F) ^ 5 = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have h : (matM : Matrix (Fin 4) (Fin 4) F) ^ 5 = matM2 * matM2 * matM := by
    rw [show (5 : ℕ) = 2 + 2 + 1 from rfl, pow_succ, pow_add, pow_two, matM_sq]
  rw [h, matM2_sq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matM, matM4, Matrix.mul_apply, Fin.sum_univ_four] <;> grind

omit [CharP F 2] in
theorem matM_ne_one : (matM : Matrix (Fin 4) (Fin 4) F) ≠ 1 := by
  intro h
  have := congrArg (fun A : Matrix (Fin 4) (Fin 4) F => A 0 0) h
  simp [matM] at this

end Matrices

section Chain

variable {n : ℕ} {F : Type} [Field F] {b c : F}

@[expose] def Intertw (p : Fin 4 → Fin (n - 1)) (g : spinGroup (quadMinus n F b c))
    (A : Matrix (Fin 4) (Fin 4) F) : Prop :=
  ∀ (w : Vm n F) (a : Fin 4), spinAction (quadMinus n F b c) g w (.inl (p a)) =
    (A.mulVec fun j => w (.inl (p j))) a

variable {p : Fin 4 → Fin (n - 1)}

theorem Intertw.one : Intertw (b := b) (c := c) p 1 1 := by
  intro w a
  simp

theorem Intertw.mul {g h : spinGroup (quadMinus n F b c)} {A B : Matrix (Fin 4) (Fin 4) F}
    (hg : Intertw p g A) (hh : Intertw p h B) : Intertw p (g * h) (A * B) := by
  intro w a
  rw [map_mul, LinearEquiv.mul_apply, hg, ← Matrix.mulVec_mulVec]
  congr 2
  funext j
  exact hh w j

theorem Intertw.pow {g : spinGroup (quadMinus n F b c)} {A : Matrix (Fin 4) (Fin 4) F}
    (hg : Intertw p g A) (m : ℕ) : Intertw p (g ^ m) (A ^ m) := by
  induction m with
  | zero => simpa using Intertw.one
  | succ m ih => rw [pow_succ, pow_succ]; exact ih.mul hg

theorem Intertw.longRoot (hp : Function.Injective p) {i j : Fin 4} (hij : i ≠ j) (t : F) :
    Intertw p ((minusFrame n b c).longRoot (hp.ne hij) true false (.ofAdd t)) (transv i j t) := by
  intro w a
  rw [spinAction_longRoot_apply_tf]
  have h1 : (Sum.inl (p a) : Idx n) ≠ .inr (.inl (p j)) := by simp
  simp only [transv, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    Matrix.single_mulVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hp.eq_iff, Sum.inl.injEq, h1,
    ite_false, mul_zero, sub_zero, one_mul]
  by_cases hai : a = i <;> simp [hai]

@[expose] def chain (x₀ : ℕ) (hx : x₀ + 5 ≤ n) (j : Fin 4) : Fin (n - 1) :=
  ⟨x₀ + j.val, by have := j.isLt; omega⟩

theorem chain_val (x₀ : ℕ) (hx : x₀ + 5 ≤ n) (j : Fin 4) : (chain x₀ hx j).val = x₀ + j.val :=
  rfl

theorem chain_injective (x₀ : ℕ) (hx : x₀ + 5 ≤ n) : Function.Injective (chain x₀ hx) := by
  intro i j h
  have := congrArg Fin.val h
  rw [chain_val, chain_val] at this
  exact Fin.ext (by omega)

theorem eq_one_of_intertw_one [Finite F] [CharP F 2] (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {g : spinGroup (quadMinus n F b c)}
    (hg : g ∈ actsIn (spinAction (quadMinus n F b c))
        ((eCoords n (Finset.univ.image p) ∪ fCoords n (Finset.univ.image p) : Finset (Idx n)) :
          Set (Idx n)) ⊓
      stabSub (spinAction (quadMinus n F b c)) (eCoords n (Finset.univ.image p) : Set (Idx n)) ⊓
      stabSub (spinAction (quadMinus n F b c)) (fCoords n (Finset.univ.image p) : Set (Idx n)))
    (h : Intertw p g 1) : g = 1 := by
  refine eq_one_of_fix_eCoords hirr (Finset.univ.image p) hg.1.1 hg.2 fun u hu => ?_
  have hgu : spinAction (quadMinus n F b c) g u ∈
      supp F (eCoords n (Finset.univ.image p) : Set (Idx n)) := (hg.1.2 u hu).1
  funext a
  by_cases ha : a ∈ eCoords n (Finset.univ.image p)
  · obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hl
    simpa using h u j
  · rw [hgu a ha, hu a ha]

theorem longRoot_pos_mem_rankOne (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {k j : Fin (n - 1)}
    (hk : k.val + 1 < n - 1) (hj : j.val = k.val + 1) (hkj : k ≠ j) (t : F) :
    (minusFrame n b c).longRoot hkj true false (.ofAdd t) ∈
      rankOne (minusDatum n hirr).rootGroup k := by
  obtain rfl : j = ⟨k.val + 1, hk⟩ := Fin.ext hj
  have hmem : (minusFrame n b c).longRoot (succ_ne_of_lt n hk) true false (.ofAdd t) ∈
      minusRootGroup n hirr (Pi.single k 1) := by
    rw [minusRootGroup_single_of_lt n hirr hk]
    exact ⟨_, rfl⟩
  exact le_sup_left (a := (minusDatum n hirr).rootGroup (Pi.single k 1)) hmem

theorem longRoot_neg_mem_rankOne (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {k j : Fin (n - 1)}
    (hk : k.val + 1 < n - 1) (hj : j.val = k.val + 1) (hjk : j ≠ k) (t : F) :
    (minusFrame n b c).longRoot hjk true false (.ofAdd t) ∈
      rankOne (minusDatum n hirr).rootGroup k := by
  obtain rfl : j = ⟨k.val + 1, hk⟩ := Fin.ext hj
  have hmem : (minusFrame n b c).longRoot (succ_ne_of_lt n hk).symm true false (.ofAdd t) ∈
      minusRootGroup n hirr (-Pi.single k 1) := by
    rw [minusRootGroup_neg_single_of_lt n hirr hk]
    exact ⟨_, rfl⟩
  exact le_sup_right (b := (minusDatum n hirr).rootGroup (-Pi.single k 1)) hmem

theorem exists_involutions_chain [Finite F] [CharP F 2] (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {x₀ : ℕ} (hx : x₀ + 5 ≤ n) :
    ∃ u ∈ leviM (minusDatum n hirr) {k : Fin (n - 1) | x₀ ≤ k.val ∧ k.val ≤ x₀ + 2},
      ∃ v ∈ leviM (minusDatum n hirr) {k : Fin (n - 1) | x₀ ≤ k.val ∧ k.val ≤ x₀ + 2},
        u ^ 2 = 1 ∧ v ^ 2 = 1 ∧ (u * v) ^ 5 = 1 ∧ u * v ≠ 1 := by
  have hp := chain_injective (n := n) x₀ hx
  set p := chain x₀ hx with hpdef
  have hv0 : (p 0).val = x₀ := rfl
  have hv1 : (p 1).val = x₀ + 1 := rfl
  have hv2 : (p 2).val = x₀ + 2 := rfl
  have hv3 : (p 3).val = x₀ + 3 := rfl
  set S : Finset (Fin (n - 1)) := Finset.univ.image p with hS
  have hmemS : ∀ i, p i ∈ S := fun i => Finset.mem_image_of_mem p (Finset.mem_univ i)
  set I₀ : Set (Fin (n - 1)) := {k | x₀ ≤ k.val ∧ k.val ≤ x₀ + 2} with hI₀
  have hL : ∀ k : Fin (n - 1), x₀ ≤ k.val → k.val ≤ x₀ + 2 →
      rankOne (minusDatum n hirr).rootGroup k ≤ leviM (minusDatum n hirr) I₀ := fun k h1 h2 =>
    rankOne_le_leviM (D := minusDatum n hirr) (I := I₀) ⟨h1, h2⟩
  set x₁ := (minusFrame n b c).longRoot (hp.ne (by decide : (0 : Fin 4) ≠ 1)) true false
    (.ofAdd (1 : F)) with hx₁
  set x₂ := (minusFrame n b c).longRoot (hp.ne (by decide : (1 : Fin 4) ≠ 2)) true false
    (.ofAdd (1 : F)) with hx₂
  set x₃ := (minusFrame n b c).longRoot (hp.ne (by decide : (2 : Fin 4) ≠ 3)) true false
    (.ofAdd (1 : F)) with hx₃
  set y₁ := (minusFrame n b c).longRoot (hp.ne (by decide : (1 : Fin 4) ≠ 0)) true false
    (.ofAdd (1 : F)) with hy₁
  set y₂ := (minusFrame n b c).longRoot (hp.ne (by decide : (2 : Fin 4) ≠ 1)) true false
    (.ofAdd (1 : F)) with hy₂
  set y₃ := (minusFrame n b c).longRoot (hp.ne (by decide : (3 : Fin 4) ≠ 2)) true false
    (.ofAdd (1 : F)) with hy₃
  have mx₁ : x₁ ∈ leviM (minusDatum n hirr) I₀ := hL (p 0) (by omega) (by omega)
    (longRoot_pos_mem_rankOne hirr (by omega) (by omega) _ 1)
  have mx₂ : x₂ ∈ leviM (minusDatum n hirr) I₀ := hL (p 1) (by omega) (by omega)
    (longRoot_pos_mem_rankOne hirr (by omega) (by omega) _ 1)
  have mx₃ : x₃ ∈ leviM (minusDatum n hirr) I₀ := hL (p 2) (by omega) (by omega)
    (longRoot_pos_mem_rankOne hirr (by omega) (by omega) _ 1)
  have my₁ : y₁ ∈ leviM (minusDatum n hirr) I₀ := hL (p 0) (by omega) (by omega)
    (longRoot_neg_mem_rankOne hirr (by omega) (by omega) _ 1)
  have my₂ : y₂ ∈ leviM (minusDatum n hirr) I₀ := hL (p 1) (by omega) (by omega)
    (longRoot_neg_mem_rankOne hirr (by omega) (by omega) _ 1)
  have my₃ : y₃ ∈ leviM (minusDatum n hirr) I₀ := hL (p 2) (by omega) (by omega)
    (longRoot_neg_mem_rankOne hirr (by omega) (by omega) _ 1)
  set G : Subgroup (spinGroup (quadMinus n F b c)) :=
    actsIn (spinAction (quadMinus n F b c))
        ((eCoords n S ∪ fCoords n S : Finset (Idx n)) : Set (Idx n)) ⊓
      stabSub (spinAction (quadMinus n F b c)) (eCoords n S : Set (Idx n)) ⊓
      stabSub (spinAction (quadMinus n F b c)) (fCoords n S : Set (Idx n)) with hG
  have gx₁ : x₁ ∈ G := longRoot_mem_actsLevi S _ (hmemS _) (hmemS _) 1
  have gx₂ : x₂ ∈ G := longRoot_mem_actsLevi S _ (hmemS _) (hmemS _) 1
  have gx₃ : x₃ ∈ G := longRoot_mem_actsLevi S _ (hmemS _) (hmemS _) 1
  have gy₁ : y₁ ∈ G := longRoot_mem_actsLevi S _ (hmemS _) (hmemS _) 1
  have gy₂ : y₂ ∈ G := longRoot_mem_actsLevi S _ (hmemS _) (hmemS _) 1
  have gy₃ : y₃ ∈ G := longRoot_mem_actsLevi S _ (hmemS _) (hmemS _) 1
  have ix₁ : Intertw p x₁ (transv 0 1 1) := Intertw.longRoot hp (by decide) 1
  have ix₂ : Intertw p x₂ (transv 1 2 1) := Intertw.longRoot hp (by decide) 1
  have ix₃ : Intertw p x₃ (transv 2 3 1) := Intertw.longRoot hp (by decide) 1
  have iy₁ : Intertw p y₁ (transv 1 0 1) := Intertw.longRoot hp (by decide) 1
  have iy₂ : Intertw p y₂ (transv 2 1 1) := Intertw.longRoot hp (by decide) 1
  have iy₃ : Intertw p y₃ (transv 3 2 1) := Intertw.longRoot hp (by decide) 1
  have hu : Intertw p (x₁ * x₃ * y₂) matX := by
    have := (ix₁.mul ix₃).mul iy₂
    rwa [matX_eq] at this
  have hv : Intertw p (x₂ * y₁ * y₃) matY := by
    have := (ix₂.mul iy₁).mul iy₃
    rwa [matY_eq] at this
  have gu : x₁ * x₃ * y₂ ∈ G := mul_mem (mul_mem gx₁ gx₃) gy₂
  have gv : x₂ * y₁ * y₃ ∈ G := mul_mem (mul_mem gx₂ gy₁) gy₃
  refine ⟨x₁ * x₃ * y₂, mul_mem (mul_mem mx₁ mx₃) my₂, x₂ * y₁ * y₃,
    mul_mem (mul_mem mx₂ my₁) my₃, ?_, ?_, ?_, ?_⟩
  · refine eq_one_of_intertw_one hirr (pow_mem gu 2) ?_
    have := hu.pow 2
    rwa [matX_sq] at this
  · refine eq_one_of_intertw_one hirr (pow_mem gv 2) ?_
    have := hv.pow 2
    rwa [matY_sq] at this
  · refine eq_one_of_intertw_one hirr (pow_mem (mul_mem gu gv) 5) ?_
    have := (hu.mul hv).pow 5
    rwa [matX_mul_matY, matM_pow_five] at this
  · intro h
    have hI := hu.mul hv
    rw [h, matX_mul_matY] at hI
    have := hI (Pi.single (.inl (p 0)) 1) 1
    simp [hp.eq_iff, matM, Matrix.mulVec, dotProduct, Pi.single_apply] at this

end Chain

section Triples

variable {n : ℕ} {F : Type} [Field F] {b c : F}
  (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)

theorem realOver_chain [Finite F] [CharP F 2] {Y : Type*} [Group Y]
    {π : spinGroup (quadMinus n F b c) →* Y} {J : Subgroup Y}
    (hBJ : borel (minusDatum n hirr) (minusTorus n hirr) ≤ J.comap π) {x₀ : ℕ} (hx : x₀ + 5 ≤ n)
    (hI : ∀ k : Fin (n - 1), x₀ ≤ k.val → k.val ≤ x₀ + 2 →
      k ∈ negIndices (minusDatum n hirr) (J.comap π)) :
    RealOver 5 π (leviM (minusDatum n hirr) {k : Fin (n - 1) | x₀ ≤ k.val ∧ k.val ≤ x₀ + 2})
      J := by
  obtain ⟨u, hu, v, hv, hu2, hv2, h5, h1⟩ := exists_involutions_chain hirr hx
  have hle : leviM (minusDatum n hirr) {k : Fin (n - 1) | x₀ ≤ k.val ∧ k.val ≤ x₀ + 2} ≤
      J.comap π :=
    iSup₂_le fun (k : Fin (n - 1)) hk => rankOne_le_of_mem_negIndices hBJ (hI k hk.1 hk.2)
  refine RealOver.of_involutions' (by decide) hu hv hu2 hv2 h5 h1 ?_
  rw [map_mul]
  exact mul_mem (hle hu) (hle hv)

theorem commutes_chain_chain
    (hext : SteinbergExtras (minusDatum n hirr) (minusWeyl n hirr) (minusTorus n hirr))
    {x y : ℕ} (hxy : x + 4 ≤ y) :
    Commutes (leviM (minusDatum n hirr) {k : Fin (n - 1) | x ≤ k.val ∧ k.val ≤ x + 2})
      (leviM (minusDatum n hirr) {k : Fin (n - 1) | y ≤ k.val ∧ k.val ≤ y + 2}) := by
  refine commutes_iSup_iSup fun i hi j hj => ?_
  have hij : i.val + 2 ≤ j.val := by have := hi.2; have := hj.1; omega
  exact commutes_rankOne_of_cartan_eq_zero hext (fun h => by rw [h] at hij; omega)
    (cartan_minusDatum_eq_zero hirr hij)

theorem commutes_chain_rankOne
    (hext : SteinbergExtras (minusDatum n hirr) (minusWeyl n hirr) (minusTorus n hirr))
    {x : ℕ} {s : Fin (n - 1)} (hxs : x + 4 ≤ s.val) :
    Commutes (leviM (minusDatum n hirr) {k : Fin (n - 1) | x ≤ k.val ∧ k.val ≤ x + 2})
      (rankOne (minusDatum n hirr).rootGroup s) := by
  have h := commutes_iSup_iSup (I := {k : Fin (n - 1) | x ≤ k.val ∧ k.val ≤ x + 2})
    (J := ({s} : Set (Fin (n - 1)))) (L := fun i => rankOne (minusDatum n hirr).rootGroup i)
    (fun i hi j hj => by
      have hij : i.val + 2 ≤ j.val := by
        have := hi.2
        rw [Set.mem_singleton_iff] at hj
        rw [hj]
        omega
      exact commutes_rankOne_of_cartan_eq_zero hext (fun h => by rw [h] at hij; omega)
        (cartan_minusDatum_eq_zero hirr hij))
  have e : (⨆ j ∈ ({s} : Set (Fin (n - 1))), rankOne (minusDatum n hirr).rootGroup j) =
      rankOne (minusDatum n hirr).rootGroup s := by simp
  rw [e] at h
  exact h

theorem three_le_pRank_five_of_chains [Finite F] [CharP F 2] {Y : Type*} [Group Y]
    {π : spinGroup (quadMinus n F b c) →* Y} {M : ℕ} {J : Subgroup Y}
    (hb : BorelQuotient (minusDatum n hirr) (minusWeyl n hirr) (minusTorus n hirr) π M)
    (hBJ : borel (minusDatum n hirr) (minusTorus n hirr) ≤ J.comap π)
    {X : Type*} [Group X] [Finite X] (ρ : X →* Y) (hρ : Function.Surjective ρ)
    (hρker : ρ.ker ≤ Subgroup.center X) {x : ℕ} (hx : x + 13 ≤ n)
    (hI : ∀ k : Fin (n - 1), (x ≤ k.val ∧ k.val ≤ x + 2) ∨ (x + 4 ≤ k.val ∧ k.val ≤ x + 6) ∨
      (x + 8 ≤ k.val ∧ k.val ≤ x + 10) → k ∈ negIndices (minusDatum n hirr) (J.comap π)) :
    3 ≤ CFSG.Open.pRank 5 (J.comap ρ) := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact three_le_pRank_of_triple (by decide) hb.ker_central ρ hρ hρker
    (commutes_chain_chain hirr hb.extras (x := x) (y := x + 4) le_rfl)
    (commutes_chain_chain hirr hb.extras (x := x) (y := x + 8) (by omega))
    (commutes_chain_chain hirr hb.extras (x := x + 4) (y := x + 8) le_rfl)
    (realOver_chain hirr hBJ (x₀ := x) (by omega) fun k h1 h2 => hI k (Or.inl ⟨h1, h2⟩))
    (realOver_chain hirr hBJ (x₀ := x + 4) (by omega) fun k h1 h2 =>
      hI k (Or.inr (Or.inl ⟨h1, h2⟩)))
    (realOver_chain hirr hBJ (x₀ := x + 8) (by omega) fun k h1 h2 =>
      hI k (Or.inr (Or.inr ⟨h1, h2⟩)))

theorem three_le_pRank_five_of_chains_short [Finite F] [CharP F 2] {Y : Type*} [Group Y]
    {π : spinGroup (quadMinus n F b c) →* Y} {M : ℕ} {J : Subgroup Y}
    (hb : BorelQuotient (minusDatum n hirr) (minusWeyl n hirr) (minusTorus n hirr) π M)
    (hBJ : borel (minusDatum n hirr) (minusTorus n hirr) ≤ J.comap π)
    {X : Type*} [Group X] [Finite X] (ρ : X →* Y) (hρ : Function.Surjective ρ)
    (hρker : ρ.ker ≤ Subgroup.center X) {x : ℕ} (hx : x + 10 ≤ n) {s : Fin (n - 1)}
    (hs : s.val + 2 = n)
    (hI : ∀ k : Fin (n - 1), (x ≤ k.val ∧ k.val ≤ x + 2) ∨ (x + 4 ≤ k.val ∧ k.val ≤ x + 6) →
      k ∈ negIndices (minusDatum n hirr) (J.comap π))
    (hsI : s ∈ negIndices (minusDatum n hirr) (J.comap π)) :
    3 ≤ CFSG.Open.pRank 5 (J.comap ρ) := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hs1 : ¬ s.val + 1 < n - 1 := by omega
  exact three_le_pRank_of_triple (by decide) hb.ker_central ρ hρ hρker
    (commutes_chain_chain hirr hb.extras (x := x) (y := x + 4) le_rfl)
    (commutes_chain_rankOne hirr hb.extras (x := x) (by omega))
    (commutes_chain_rankOne hirr hb.extras (x := x + 4) (by omega))
    (realOver_chain hirr hBJ (x₀ := x) (by omega) fun k h1 h2 => hI k (Or.inl ⟨h1, h2⟩))
    (realOver_chain hirr hBJ (x₀ := x + 4) (by omega) fun k h1 h2 => hI k (Or.inr ⟨h1, h2⟩))
    ((hasRealFive_spinMinus_short hirr hs1).realOver hb.extras
      (rankOne_le_of_mem_negIndices hBJ hsI))

end Triples

section Runs

variable {n : ℕ}

@[expose] def nodeIn (I : Set (Fin (n - 1))) (k : ℕ) : Prop :=
  ∃ h : k < n - 1, (⟨k, h⟩ : Fin (n - 1)) ∈ I

open scoped Classical in
@[expose] noncomputable def runStart (I : Set (Fin (n - 1))) : ℕ → ℕ
  | 0 => 0
  | k + 1 => if nodeIn I k then runStart I k else k + 1

variable (I : Set (Fin (n - 1)))

theorem runStart_succ_of_nodeIn {k : ℕ} (h : nodeIn I k) : runStart I (k + 1) = runStart I k := by
  classical
  simp [runStart, h]

theorem runStart_le (k : ℕ) : runStart I k ≤ k := by
  induction k with
  | zero => simp [runStart]
  | succ k ih =>
    classical
    by_cases h : nodeIn I k
    · rw [runStart_succ_of_nodeIn I h]
      omega
    · simp [runStart, h]

theorem nodeIn_of_runStart_le {k i : ℕ} (hi : runStart I k ≤ i) (hik : i < k) : nodeIn I i := by
  classical
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases h : nodeIn I k
    · rw [runStart_succ_of_nodeIn I h] at hi
      by_cases hik' : i < k
      · exact ih hi hik'
      · have : i = k := by omega
        rw [this]
        exact h
    · have : runStart I (k + 1) = k + 1 := by simp [runStart, h]
      omega

open scoped Classical in
@[expose] noncomputable def merged (I : Set (Fin (n - 1))) (k : ℕ) : Bool :=
  decide (nodeIn I (n - 2)) && decide (runStart I k = runStart I (n - 2))

@[expose] noncomputable def lab (I : Set (Fin (n - 1))) : Idx n → ℕ × Bool
  | .inl l => (runStart I l.val, false)
  | .inr (.inl l) => (runStart I l.val, !merged I l.val)
  | .inr (.inr _) => (runStart I (n - 2), false)

theorem lab_long {I : Set (Fin (n - 1))} {k : Fin (n - 1)} (hk : k ∈ I) (hk1 : k.val + 1 < n - 1) :
    lab I (.inl k) = lab I (.inl ⟨k.val + 1, hk1⟩) ∧
      lab I (.inr (.inl k)) = lab I (.inr (.inl ⟨k.val + 1, hk1⟩)) := by
  have h : nodeIn I k.val := ⟨k.isLt, hk⟩
  have h1 := runStart_succ_of_nodeIn I h
  simp only [lab, merged]
  rw [h1]
  exact ⟨rfl, rfl⟩

theorem lab_short {I : Set (Fin (n - 1))} {k : Fin (n - 1)} (hk : k ∈ I)
    (hk1 : ¬ k.val + 1 < n - 1) :
    lab I (.inl k) = lab I (.inr (.inl k)) ∧ lab I (.inl k) = lab I (.inr (.inr 0)) ∧
      lab I (.inl k) = lab I (.inr (.inr 1)) := by
  classical
  have hkv : k.val = n - 2 := by have := k.isLt; omega
  have hs : nodeIn I (n - 2) := ⟨by omega, by
    have : (⟨n - 2, by omega⟩ : Fin (n - 1)) = k := Fin.ext hkv.symm
    rw [this]
    exact hk⟩
  simp [lab, merged, hkv, hs]

theorem lab_plane (I : Set (Fin (n - 1))) : lab I (.inr (.inr 0)) = lab I (.inr (.inr 1)) := rfl

theorem card_fiber_eq {κ : Type} [DecidableEq κ] (lab : Idx n → κ) (k : κ) :
    Fintype.card {i : Idx n // lab i = k} =
      (Finset.univ.filter fun l : Fin (n - 1) => lab (.inl l) = k).card +
      (Finset.univ.filter fun l : Fin (n - 1) => lab (.inr (.inl l)) = k).card +
      (Finset.univ.filter fun t : Fin 2 => lab (.inr (.inr t)) = k).card := by
  rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_sum_type, Fintype.sum_sum_type,
    ← add_assoc, ← Finset.card_filter, ← Finset.card_filter, ← Finset.card_filter]

theorem card_fiber_le (I : Set (Fin (n - 1))) {P₀ P₁ : ℕ}
    (hP0 : ∀ j : ℕ, (Finset.univ.filter fun l : Fin (n - 1) => runStart I l.val = j).card ≤ P₀)
    (hP1 : nodeIn I (n - 2) → (Finset.univ.filter fun l : Fin (n - 1) =>
      runStart I l.val = runStart I (n - 2)).card ≤ P₁) (k : ℕ × Bool) :
    Fintype.card {i : Idx n // lab I i = k} ≤ max (2 * P₁ + 2) (P₀ + 2) := by
  classical
  rw [card_fiber_eq]
  obtain ⟨j, β⟩ := k
  have hA : (Finset.univ.filter fun l : Fin (n - 1) => lab I (.inl l) = (j, β)).card ≤
      (Finset.univ.filter fun l : Fin (n - 1) => runStart I l.val = j).card := by
    apply Finset.card_le_card
    intro l hl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, lab, Prod.mk.injEq] at hl ⊢
    exact hl.1
  have hB : (Finset.univ.filter fun l : Fin (n - 1) => lab I (.inr (.inl l)) = (j, β)).card ≤
      (Finset.univ.filter fun l : Fin (n - 1) => runStart I l.val = j).card := by
    apply Finset.card_le_card
    intro l hl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, lab, Prod.mk.injEq] at hl ⊢
    exact hl.1
  have hC : (Finset.univ.filter fun t : Fin 2 => lab I (.inr (.inr t)) = (j, β)).card ≤ 2 := by
    calc _ ≤ (Finset.univ : Finset (Fin 2)).card := Finset.card_filter_le _ _
      _ = 2 := by simp
  have h1 := hP0 j
  have hm1 : 2 * P₁ + 2 ≤ max (2 * P₁ + 2) (P₀ + 2) := le_max_left _ _
  have hm2 : P₀ + 2 ≤ max (2 * P₁ + 2) (P₀ + 2) := le_max_right _ _
  cases β
  · by_cases hm : nodeIn I (n - 2) ∧ j = runStart I (n - 2)
    · obtain ⟨hs, rfl⟩ := hm
      have h2 := hP1 hs
      omega
    · have hB0 : (Finset.univ.filter fun l : Fin (n - 1) =>
          lab I (.inr (.inl l)) = (j, false)).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro l _ h
        simp only [lab, merged, Prod.mk.injEq] at h
        obtain ⟨h1, h2⟩ := h
        apply hm
        simp only [Bool.not_eq_false', Bool.and_eq_true, decide_eq_true_eq] at h2
        exact ⟨h2.1, h1.symm.trans h2.2⟩
      omega
  · have hA0 : (Finset.univ.filter fun l : Fin (n - 1) => lab I (.inl l) = (j, true)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro l _ h
      simp [lab] at h
    have hC0 : (Finset.univ.filter fun t : Fin 2 =>
        lab I (.inr (.inr t)) = (j, true)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro l _ h
      simp [lab] at h
    omega

theorem card_runClass_le (I : Set (Fin (n - 1))) {m : ℕ}
    (hno : ∀ x : ℕ, ¬ ∀ i, x ≤ i → i < x + m → nodeIn I i) (j : ℕ) :
    (Finset.univ.filter fun l : Fin (n - 1) => runStart I l.val = j).card ≤ m := by
  classical
  refine le_trans (Finset.card_le_card_of_injOn (fun l => l.val - j) (t := Finset.range m) ?_ ?_)
    (by simp)
  · intro l hl
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hl
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    push Not at h
    apply hno j
    intro i hi1 hi2
    exact nodeIn_of_runStart_le I (by omega : runStart I l.val ≤ i) (by omega : i < l.val)
  · intro l hl l' hl' h
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hl hl'
    have h1 := runStart_le I l.val
    have h2 := runStart_le I l'.val
    exact Fin.ext (by simp only at h; omega)

theorem card_runClass_short_le (I : Set (Fin (n - 1))) {P₁ : ℕ}
    (hrs : n - 1 ≤ runStart I (n - 2) + P₁) :
    (Finset.univ.filter fun l : Fin (n - 1) =>
      runStart I l.val = runStart I (n - 2)).card ≤ P₁ := by
  classical
  refine le_trans (Finset.card_le_card_of_injOn (fun l => l.val - runStart I (n - 2))
    (t := Finset.range P₁) ?_ ?_) (by simp)
  · intro l hl
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hl
    simp only [Finset.coe_range, Set.mem_Iio]
    have := l.isLt
    have := runStart_le I l.val
    omega
  · intro l hl l' hl' h
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hl hl'
    have h1 := runStart_le I l.val
    have h2 := runStart_le I l'.val
    exact Fin.ext (by simp only at h; omega)

end Runs

section Block

variable {n : ℕ} {F : Type} [Field F] {b c : F} {κ : Type} (lab : Idx n → κ)

theorem isPartDiag_longRoot {i j : Fin (n - 1)} (hij : i ≠ j)
    (h1 : lab (.inl i) = lab (.inl j)) (h2 : lab (.inr (.inl i)) = lab (.inr (.inl j))) (t : F) :
    PartStab.IsPartDiag lab
      (mat n ((minusFrame n b c).longRoot hij true false (.ofAdd t))) := by
  intro a e hae
  rw [mat_longRoot_apply]
  have hne : a ≠ e := fun h => hae (h ▸ rfl)
  have e1 : (if a = e then (1 : F) else 0) = 0 := by simp [hne]
  have e2 : (if minusPos n j (!false) = e then (1 : F) else 0) *
      (if a = minusPos n i true then 1 else 0) = 0 := by
    by_cases h : minusPos n j (!false) = e ∧ a = minusPos n i true
    · exfalso
      obtain ⟨rfl, rfl⟩ := h
      exact hae h1
    · rw [not_and_or] at h
      rcases h with h | h
      · simp only [h, ite_false, zero_mul]
      · simp only [h, ite_false, mul_zero]
  have e3 : (if minusPos n i (!true) = e then (1 : F) else 0) *
      (if a = minusPos n j false then 1 else 0) = 0 := by
    by_cases h : minusPos n i (!true) = e ∧ a = minusPos n j false
    · exfalso
      obtain ⟨rfl, rfl⟩ := h
      exact hae h2.symm
    · rw [not_and_or] at h
      rcases h with h | h
      · simp only [h, ite_false, zero_mul]
      · simp only [h, ite_false, mul_zero]
  rw [e1, e2, e3]
  simp

theorem isPartDiag_twShortRoot (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (k : Fin (n - 1))
    (h1 : lab (.inl k) = lab (.inr (.inl k))) (h2 : lab (.inl k) = lab (.inr (.inr 0)))
    (h3 : lab (.inl k) = lab (.inr (.inr 1))) (s : Bool) (p : Fin 2 → F) :
    PartStab.IsPartDiag lab (mat n (twShortRoot n hirr k s (.ofAdd p))) := by
  have hblock : ∀ x : Idx n, (x = minusPos n k true ∨ x = minusPos n k false ∨
      ∃ t, x = .inr (.inr t)) → lab x = lab (.inl k) := by
    rintro x (rfl | rfl | ⟨t, rfl⟩)
    · rfl
    · exact h1.symm
    · fin_cases t
      · exact h2.symm
      · exact h3.symm
  have hmp : ∀ x : Idx n, x = minusPos n k (!s) → (x = minusPos n k true ∨
      x = minusPos n k false ∨ ∃ t, x = .inr (.inr t)) := by
    rintro x rfl
    cases s
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  have hmq : ∀ x : Idx n, x = minusPos n k s → (x = minusPos n k true ∨
      x = minusPos n k false ∨ ∃ t, x = .inr (.inr t)) := by
    rintro x rfl
    cases s
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl rfl
  intro a e hae
  rw [mat_twShortRoot_apply]
  have hne : a ≠ e := fun h => hae (h ▸ rfl)
  by_cases hBa : a = minusPos n k true ∨ a = minusPos n k false ∨ ∃ t, a = .inr (.inr t)
  · have hBe : ¬ (e = minusPos n k true ∨ e = minusPos n k false ∨ ∃ t, e = .inr (.inr t)) :=
      fun hBe => hae ((hblock a hBa).trans (hblock e hBe).symm)
    have hmpe : minusPos n k (!s) ≠ e := fun h => hBe (hmp e h.symm)
    have hpol : QuadraticMap.polar (quadMinus n F b c) (Pi.single e 1) (planeVec n p) = 0 :=
      polar_single_planeVec_of_ne n (fun t he => hBe (Or.inr (Or.inr ⟨t, he⟩))) p
    simp [hne, hmpe, hpol]
  · have hamq : a ≠ minusPos n k s := fun h => hBa (hmq a h)
    have hpv : planeVec n p a = 0 := by
      rcases a with l | l | t
      · rfl
      · rfl
      · exact absurd (Or.inr (Or.inr ⟨t, rfl⟩)) hBa
    simp [hne, hamq, hpv]

theorem torus_sup_leviM_le_partStab [DecidableEq κ] [Finite F]
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (I : Set (Fin (n - 1)))
    (hlong : ∀ k ∈ I, ∀ hk : k.val + 1 < n - 1, lab (.inl k) = lab (.inl ⟨k.val + 1, hk⟩) ∧
      lab (.inr (.inl k)) = lab (.inr (.inl ⟨k.val + 1, hk⟩)))
    (hshort : ∀ k ∈ I, ¬ k.val + 1 < n - 1 → lab (.inl k) = lab (.inr (.inl k)) ∧
      lab (.inl k) = lab (.inr (.inr 0)) ∧ lab (.inl k) = lab (.inr (.inr 1)))
    (hplane : lab (.inr (.inr 0)) = lab (.inr (.inr 1))) :
    (⨆ k, minusTorus n hirr k) ⊔ leviM (minusDatum n hirr) I ≤
      (PartStab.partStab F lab).comap (spinMatrix (quadMinus n F b c)) := by
  refine sup_le (iSup_le fun k => ?_) (iSup₂_le fun (k : Fin (n - 1)) hk => ?_)
  · intro g hg
    rw [Subgroup.mem_comap, PartStab.mem_partStab]
    have hD := blockDiag_mat_of_mem_minusTorus n hirr k hg
    intro a e hae
    by_contra h0
    have hne : a ≠ e := fun h => hae (h ▸ rfl)
    obtain ⟨⟨t, rfl⟩, ⟨t', rfl⟩⟩ := hD a e hne h0
    apply hae
    fin_cases t <;> fin_cases t'
    · rfl
    · exact hplane
    · exact hplane.symm
    · rfl
  · by_cases hk1 : k.val + 1 < n - 1
    · obtain ⟨h1, h2⟩ := hlong k hk hk1
      refine sup_le ?_ ?_
      · change minusRootGroup n hirr (Pi.single k 1) ≤ _
        rw [minusRootGroup_single_of_lt n hirr hk1]
        rintro _ ⟨x, rfl⟩
        rw [Subgroup.mem_comap, PartStab.mem_partStab]
        exact isPartDiag_longRoot lab (succ_ne_of_lt n hk1) h1 h2 x.toAdd
      · change minusRootGroup n hirr (-Pi.single k 1) ≤ _
        rw [minusRootGroup_neg_single_of_lt n hirr hk1]
        rintro _ ⟨x, rfl⟩
        rw [Subgroup.mem_comap, PartStab.mem_partStab]
        exact isPartDiag_longRoot lab (succ_ne_of_lt n hk1).symm h1.symm h2.symm x.toAdd
    · obtain ⟨h1, h2, h3⟩ := hshort k hk hk1
      refine sup_le ?_ ?_
      · change minusRootGroup n hirr (Pi.single k 1) ≤ _
        rw [minusRootGroup_single_of_not_lt n hirr hk1]
        rintro _ ⟨x, rfl⟩
        rw [Subgroup.mem_comap, PartStab.mem_partStab]
        exact isPartDiag_twShortRoot lab hirr k h1 h2 h3 true x.toAdd
      · change minusRootGroup n hirr (-Pi.single k 1) ≤ _
        rw [minusRootGroup_neg_single_of_not_lt n hirr hk1]
        rintro _ ⟨x, rfl⟩
        rw [Subgroup.mem_comap, PartStab.mem_partStab]
        exact isPartDiag_twShortRoot lab hirr k h1 h2 h3 false x.toAdd

theorem isMulCommutative_of_le_comap_partStab [DecidableEq κ] [Finite F] [CharP F 2]
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {f : ℕ} (hF : Nat.card F = 2 ^ f)
    (hfm : ∀ k : κ, (Odd f ∧ Fintype.card {i // lab i = k} < 20) ∨
      (f % 4 = 2 ∧ Fintype.card {i // lab i = k} < 10) ∨
      (4 ∣ f ∧ Fintype.card {i // lab i = k} < 5))
    {Q : Subgroup (spinGroup (quadMinus n F b c))}
    (hQ : Q ≤ (PartStab.partStab F lab).comap (spinMatrix (quadMinus n F b c)))
    (hQp : IsPGroup 5 Q) : IsMulCommutative Q := by
  have hall : ∀ (k : κ) (P : Subgroup (GL {i // lab i = k} F)), IsPGroup 5 P →
      IsMulCommutative P := fun k P hP =>
    PartStab.isMulCommutative_of_isPGroup_five_GL_fintype hF (hfm k) P hP
  have hQ' : Q.map (spinMatrix (quadMinus n F b c)) ≤ PartStab.partStab F lab :=
    Subgroup.map_le_iff_le_comap.2 hQ
  have hQp' : IsPGroup 5 (Q.map (spinMatrix (quadMinus n F b c))) := hQp.map _
  have h := PartStab.isMulCommutative_of_le_partStab lab hall hQ' hQp'
  have hinj : Function.Injective (spinMatrix (quadMinus n F b c)) :=
    (MonoidHom.ker_eq_bot_iff _).1 (ker_spinMatrix_quadMinus_eq_bot hirr CharTwo.two_eq_zero)
  refine ⟨⟨fun x y => ?_⟩⟩
  have hc := h.is_comm.comm
    (⟨spinMatrix (quadMinus n F b c) x, Subgroup.mem_map_of_mem _ x.2⟩ :
      Q.map (spinMatrix (quadMinus n F b c)))
    ⟨spinMatrix (quadMinus n F b c) y, Subgroup.mem_map_of_mem _ y.2⟩
  have h2 : spinMatrix (quadMinus n F b c) (x : spinGroup (quadMinus n F b c)) *
      spinMatrix (quadMinus n F b c) (y : spinGroup (quadMinus n F b c)) =
      spinMatrix (quadMinus n F b c) (y : spinGroup (quadMinus n F b c)) *
        spinMatrix (quadMinus n F b c) (x : spinGroup (quadMinus n F b c)) :=
    congrArg Subtype.val hc
  apply Subtype.ext
  apply hinj
  rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
  exact h2

end Block

set_option linter.unusedVariables false in
theorem three_le_pRank_five_spinMinus {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hn : 4 ≤ n) {Y : Type} [Group Y]
    [Finite Y] (e : Y ≃* StatedProj (StatedOmega (StatedQuadMinus n F b c))) {X : Type}
    [Group X] [Finite X] (ρ : X →* Y) (hρ : Function.Surjective ρ)
    (hρker : ρ.ker ≤ Subgroup.center X) (hρ5 : Nat.Coprime 5 (Nat.card ρ.ker)) (T : Sylow 2 Y)
    (J : Subgroup Y) (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J) (hJ : J ≠ ⊤)
    (P : Subgroup Y) (hPJ : P ≤ J) (hP : IsPGroup 5 P) (hPc : ¬ IsMulCommutative P) :
    3 ≤ CFSG.Open.pRank 5 (J.comap ρ) := by
  classical
  have := Fintype.ofFinite F
  have hfin : Finite (spinGroup (quadMinus n F b c)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadMinus hirr)
  obtain ⟨f, -, hf⟩ := FiniteField.card F 2
  have hfc : Nat.card F = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hf]
  have hb := borelQuotient_spinMinus hirr hn e
  obtain ⟨π', hb', hker', hBJ⟩ := SquareGeneric.BorelQuotient.exists_conj_parab hb T hNJ
  have hπ5 : Nat.Coprime 5 (Nat.card π'.ker) := by
    rw [hker', ker_comp_spinToStatedProj_eq_bot hn hirr e]
    simp
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  by_cases h4 : 4 ∣ (f : ℕ)
  ·
    obtain ⟨m, hm⟩ := h4
    have h5 : 5 ∣ Nat.card F - 1 := by
      have h16 : Nat.card F = 16 ^ m := by rw [hfc, hm, pow_mul]; norm_num
      rw [h16]
      have := Nat.sub_dvd_pow_sub_pow 16 1 m
      rw [one_pow] at this
      exact (by norm_num : 5 ∣ 16 - 1).trans this
    exact (three_le_pRank_five_of_torus hn hirr hb' hBJ hπ5 h5).trans
      (pRank_le_pRank_comap_of_coprime hρ hρ5 J)
  · by_contra hlt
    obtain ⟨Q, hQle, hQ5, hQc⟩ :=
      exists_nonabelian_le_torus_sup_leviM hb' hBJ (by norm_num) hPJ hP hPc
    set I : Set (Fin (n - 1)) := negIndices (minusDatum n hirr) (J.comap π') with hI
    have hQ : Q ≤ (PartStab.partStab F (lab I)).comap (spinMatrix (quadMinus n F b c)) :=
      hQle.trans (torus_sup_leviM_le_partStab (lab I) hirr I (fun k hk hk1 => lab_long hk hk1)
        (fun k hk hk1 => lab_short hk hk1) (lab_plane I))
    rcases Nat.even_or_odd (f : ℕ) with hfe | hfo
    ·
      obtain ⟨k, hk⟩ := hfe
      have hmod : (f : ℕ) % 4 = 2 := by omega
      have hq4 : Nat.card F = 4 ^ k := by rw [hfc, hk, ← two_mul, pow_mul]; norm_num
      have hr : ∀ i, HasRealFive (minusDatum n hirr) i :=
        hasRealFive_spinMinus hirr (exists_root_of_card_eq_four_pow hq4)
      have hno : ∀ x : ℕ, ¬ ∀ i, x ≤ i → i < x + 5 → nodeIn I i := by
        intro x hx
        obtain ⟨h0, m0⟩ := hx x le_rfl (by omega)
        obtain ⟨h2, m2⟩ := hx (x + 2) (by omega) (by omega)
        obtain ⟨h4', m4⟩ := hx (x + 4) (by omega) (by omega)
        exact hlt (three_le_pRank_five_of_orth hirr hb' hBJ hr ρ hρ hρker
          (x := ⟨x, h0⟩) (y := ⟨x + 2, h2⟩) (z := ⟨x + 4, h4'⟩) (by simp) (by simp) m0 m2 m4)
      have hrs : nodeIn I (n - 2) → n - 1 ≤ runStart I (n - 2) + 2 := by
        intro hs
        by_contra hcon
        push Not at hcon
        obtain ⟨hs1, ms⟩ := hs
        obtain ⟨h1, m1⟩ := nodeIn_of_runStart_le I (k := n - 2) (i := n - 4) (by omega) (by omega)
        obtain ⟨h2, m2⟩ := nodeIn_of_runStart_le I (k := n - 2) (i := n - 3) (by omega) (by omega)
        exact hlt (three_le_pRank_five_of_B3 hirr hb' hBJ hr ρ hρ hρker (p := ⟨n - 4, h1⟩)
          (l := ⟨n - 3, h2⟩) (s := ⟨n - 2, hs1⟩) (by simp; omega) (by simp; omega)
          (by simp; omega) m1 m2 ms)
      refine hQc (isMulCommutative_of_le_comap_partStab (lab I) hirr hfc
        (fun k => Or.inr (Or.inl ⟨hmod, ?_⟩)) hQ hQ5)
      exact lt_of_le_of_lt (card_fiber_le I (card_runClass_le I hno)
        (fun hs => card_runClass_short_le I (hrs hs)) k) (by norm_num)
    ·
      have hno : ∀ x : ℕ, ¬ ∀ i, x ≤ i → i < x + 11 → nodeIn I i := by
        intro x hx
        have hmem : ∀ k : Fin (n - 1), x ≤ k.val → k.val ≤ x + 10 → k ∈ I := fun k h1 h2 =>
          (hx k.val h1 (by omega)).2
        by_cases hx13 : x + 13 ≤ n
        · exact hlt (three_le_pRank_five_of_chains hirr hb' hBJ ρ hρ hρker hx13 (fun k hk =>
            hmem k (by omega) (by omega)))
        · have hxn : x + 12 = n := by
            have := (hx (x + 10) (by omega) (by omega)).1
            omega
          obtain ⟨hs1, ms⟩ := hx (x + 10) (by omega) (by omega)
          exact hlt (three_le_pRank_five_of_chains_short hirr hb' hBJ ρ hρ hρker (x := x)
            (by omega) (s := ⟨x + 10, hs1⟩) (by simp; omega)
            (fun k hk => hmem k (by omega) (by omega)) ms)
      have hrs : nodeIn I (n - 2) → n - 1 ≤ runStart I (n - 2) + 8 := by
        intro hs
        by_contra hcon
        push Not at hcon
        obtain ⟨hs1, ms⟩ := hs
        refine hlt (three_le_pRank_five_of_chains_short hirr hb' hBJ ρ hρ hρker
          (x := runStart I (n - 2)) (by omega) (s := ⟨n - 2, hs1⟩) (by simp; omega)
          (fun k hk => ?_) ms)
        have := k.isLt
        exact (nodeIn_of_runStart_le I (k := n - 2) (i := k.val)
          (by omega) (by omega)).2
      refine hQc (isMulCommutative_of_le_comap_partStab (lab I) hirr hfc
        (fun k => Or.inl ⟨hfo, ?_⟩) hQ hQ5)
      exact lt_of_le_of_lt (card_fiber_le I (card_runClass_le I hno)
        (fun hs => card_runClass_short_le I (hrs hs)) k) (by norm_num)

end CFSG.AGLEmbeddingD2.HeisSpinMinus
