module

public import CFSG.Quasithin.Vol2.Ch11SecEK1C
public import CFSG.Quasithin.Vol2.Ch11SecEK1E
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15InnerSemi
public import CFSG.Quasithin.Background.G64Realize

public section

namespace CFSG.Quasithin.BinaryNaturalSL

open CFSG.Assembly.LowTwoRank
open scoped Matrix

private theorem exists_coordinates_three {W : Type} [CommGroup W]
    {H : Subgroup (MulAut W)} {n : ℕ}
    (hH : BinaryNaturalSL H ⊤ ⊥ 3 n) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      ∃ (π : ↥(StatedSL 3 K) →* ↥H) (e : W ≃* Multiplicative (Fin 3 → K)),
        (FFModel.nat (StatedSL 3 K)).RealizesVia H ⊤ ⊥ π ∧
        Function.Surjective π ∧
        ∀ (γ : ↥(StatedSL 3 K)) (w : W),
          e (((π γ : ↥H) : MulAut W) w) = Multiplicative.ofAdd
            (((γ : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
              Multiplicative.toAdd (e w)) := by
  classical
  obtain ⟨K, hKfield, hKfin, hKcard, π, hreal⟩ := hH
  letI : Field K := hKfield
  letI : Finite K := hKfin
  obtain ⟨E, hE⟩ := G64.RealizesVia.exists_secEquiv
    (D := FFModel.nat (StatedSL 3 K)) rfl hreal
  let e : W ≃* Multiplicative (Fin 3 → K) :=
    E.trans (Subgroup.topEquiv : ↥(FFModel.nat (StatedSL 3 K)).sec ≃*
      (FFModel.nat (StatedSL 3 K)).Amb)
  refine ⟨K, hKfield, hKfin, hKcard, π, e, hreal, hreal.1, fun γ w => ?_⟩
  change ((E (((π γ : ↥H) : MulAut W) w) : ↥(FFModel.nat (StatedSL 3 K)).sec) :
      (FFModel.nat (StatedSL 3 K)).Amb) = Multiplicative.ofAdd
    (((γ : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
      Multiplicative.toAdd ((E w : ↥(FFModel.nat (StatedSL 3 K)).sec) :
        (FFModel.nat (StatedSL 3 K)).Amb))
  exact hE γ w

private theorem pow_two_eq_one_of_coordinates {K : Type} [Field K] [CharP K 2]
    (w : Multiplicative (Fin 3 → K)) : w ^ 2 = 1 := by
  obtain ⟨x, rfl⟩ := Multiplicative.ofAdd.surjective w
  have hx : x + x = 0 := by
    funext i
    exact CharTwo.add_self_eq_zero (x i)
  rw [pow_two]
  show Multiplicative.ofAdd x * Multiplicative.ofAdd x = 1
  rw [show Multiplicative.ofAdd x * Multiplicative.ofAdd x = Multiplicative.ofAdd (x + x)
    from rfl, hx]
  rfl

private theorem isSylowTwoOf_map_of_sylow {W : Type} [CommGroup W]
    {H : Subgroup (MulAut W)} [Finite ↥H]
    (S : Sylow 2 ↥H) :
    CFSG.QuasithinUnique.IsSylowTwoOf (S.map H.subtype) H := by
  refine ⟨?_, S.isPGroup'.map H.subtype, ?_⟩
  · intro p hp
    obtain ⟨s, -, rfl⟩ := Subgroup.mem_map.mp hp
    exact s.2
  · have hsub : (S.map H.subtype).subgroupOf H = (S : Subgroup ↥H) := by
      ext x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
      constructor
      · rintro ⟨s, hs, hxs⟩
        have hx : s = x := Subtype.ext hxs
        exact hx ▸ hs
      · intro hx
        exact ⟨x, hx, rfl⟩
    rw [hsub]
    exact S.not_dvd_index

theorem mem_of_fixed_sylow_three {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {n : ℕ}
    (hH : BinaryNaturalSL H ⊤ ⊥ 3 n) (hn : 2 ≤ n) (S : Sylow 2 ↥H) {Y : Subgroup W}
    (hYS : ∀ s ∈ (S : Subgroup ↥H), ∀ y ∈ Y, (s : MulAut W) y = y) (hY : Nat.card Y = 2 ^ n)
    {w : W} (hw : ∀ s ∈ (S : Subgroup ↥H), (s : MulAut W) w = w) : w ∈ Y := by
  classical
  obtain ⟨K, hKfield, hKfin, hKcard, π, e, hreal, -, hact⟩ := exists_coordinates_three hH
  letI : Field K := hKfield
  letI : Finite K := hKfin
  haveI : CharP K 2 :=
    CFSG.Quasithin.Vol2.KGNat.charP_two_of_card (by omega) hKcard
  haveI : Finite ↥H := Finite.of_surjective π hreal.1
  have hW2 : ∀ w : W, w ^ 2 = 1 := by
    intro w
    refine e.map_eq_one_iff.mp ?_
    rw [map_pow]
    exact pow_two_eq_one_of_coordinates (e w)
  let P : Subgroup (MulAut W) := S.map H.subtype
  have hP : CFSG.QuasithinUnique.IsSylowTwoOf P H := isSylowTwoOf_map_of_sylow S
  obtain ⟨U₁, U₂, U₃, hU₁, -, -, -, -, -, -, -⟩ :=
    CFSG.Quasithin.Vol2.KGNat.factFlagSL3_holds K n hn hKcard W hW2 H ⊥ π hreal P hP
  have hcardU₁ : Nat.card U₁ = 2 ^ n := by
    have h := hU₁.2.2.1
    rwa [Subgroup.relIndex_bot_left, pow_one] at h
  have hfixedU₁ : ∀ x : W, (∀ p ∈ P, p x = x) → x ∈ U₁ :=
    CFSG.Quasithin.Vol2.Ch11.SecE.factFixPointSL3_holds K n hn hKcard W hW2 H π hreal P hP U₁ hU₁
  have hYle : Y ≤ U₁ := by
    intro y hy
    exact hfixedU₁ y fun p hp => by
      obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hp
      exact hYS s hs y hy
  have hYU : Y = U₁ := Subgroup.eq_of_le_of_card_ge hYle (le_of_eq (by rw [hcardU₁, hY]))
  rw [hYU]
  exact hfixedU₁ w fun p hp => by
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hp
    exact hw s hs

private theorem action_smul_scalar {W : Type} [CommGroup W] {K : Type} [Field K]
    {H : Subgroup (MulAut W)}
    {π : ↥(StatedSL 3 K) →* ↥H} {e : W ≃* Multiplicative (Fin 3 → K)}
    (hπ : Function.Surjective π)
    (hact : ∀ (γ : ↥(StatedSL 3 K)) (w : W),
      e (((π γ : ↥H) : MulAut W) w) = Multiplicative.ofAdd
        (((γ : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
          Multiplicative.toAdd (e w)))
    (s : ↥H) {y : W} (hy : (s : MulAut W) y = y) (c : K) :
    (s : MulAut W) (e.symm (Multiplicative.ofAdd (c • Multiplicative.toAdd (e y)))) =
      e.symm (Multiplicative.ofAdd (c • Multiplicative.toAdd (e y))) := by
  obtain ⟨γ, hγ⟩ := hπ s
  apply e.injective
  have h1 : e ((s : MulAut W)
      (e.symm (Multiplicative.ofAdd (c • Multiplicative.toAdd (e y))))) =
      Multiplicative.ofAdd
        (((γ : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
          (c • Multiplicative.toAdd (e y))) := by
    rw [← hγ]
    simpa using hact γ (e.symm (Multiplicative.ofAdd (c • Multiplicative.toAdd (e y))))
  rw [h1, Matrix.mulVec_smul]
  have h3 : (((γ : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
      Multiplicative.toAdd (e y)) = Multiplicative.toAdd (e ((s : MulAut W) y)) := by
    rw [← hγ]
    exact (congrArg Multiplicative.toAdd (hact γ y)).symm
  rw [h3, hy]
  simp

private noncomputable def coordAddEquiv {W : Type} [CommGroup W] {K : Type} [Field K]
    (e : W ≃* Multiplicative (Fin 3 → K)) (f : MulAut W) :
    (Fin 3 → K) ≃+ (Fin 3 → K) where
  toFun := fun x => Multiplicative.toAdd (e (f (e.symm (Multiplicative.ofAdd x))))
  invFun := fun x => Multiplicative.toAdd (e (f⁻¹ (e.symm (Multiplicative.ofAdd x))))
  left_inv := fun x => by simp
  right_inv := fun x => by simp
  map_add' := fun x y => by
    have h : Multiplicative.ofAdd (x + y) =
        Multiplicative.ofAdd x * Multiplicative.ofAdd y := rfl
    rw [h, map_mul, map_mul, map_mul]
    rfl

private theorem coordAddEquiv_iterate {W : Type} [CommGroup W] {K : Type} [Field K]
    (e : W ≃* Multiplicative (Fin 3 → K)) (f : MulAut W) :
    ∀ (m : ℕ) (x : Fin 3 → K),
      ((coordAddEquiv e f)^[m]) x = Multiplicative.toAdd
        (e ((f ^ m) (e.symm (Multiplicative.ofAdd x)))) := by
  intro m
  induction m with
  | zero => intro x; simp
  | succ m ih =>
      intro x
      rw [Function.iterate_succ_apply', ih]
      have ha : coordAddEquiv e f (Multiplicative.toAdd
          (e ((f ^ m) (e.symm (Multiplicative.ofAdd x))))) =
          Multiplicative.toAdd (e (f ((f ^ m) (e.symm (Multiplicative.ofAdd x))))) := by
        simp [coordAddEquiv]
      rw [ha, pow_succ', MulAut.mul_apply]

private theorem coordAddEquiv_iterate_eq_id {W : Type} [CommGroup W] {K : Type} [Field K]
    (e : W ≃* Multiplicative (Fin 3 → K)) (f : MulAut W) {k : ℕ}
    (hf : f ^ (2 ^ k) = 1) : ((coordAddEquiv e f)^[2 ^ k]) = id := by
  funext x
  rw [coordAddEquiv_iterate e f (2 ^ k) x, hf]
  simp

private theorem smul_mem_of_fixed_sylow {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {n : ℕ}
    (hH : BinaryNaturalSL H ⊤ ⊥ 3 n) (hn : 2 ≤ n) (S : Sylow 2 ↥H) {Y : Subgroup W}
    (hYS : ∀ s ∈ (S : Subgroup ↥H), ∀ y ∈ Y, (s : MulAut W) y = y) (hY : Nat.card Y = 2 ^ n)
    {K : Type} [Field K] {π : ↥(StatedSL 3 K) →* ↥H}
    {e : W ≃* Multiplicative (Fin 3 → K)} (hπ : Function.Surjective π)
    (hact : ∀ (γ : ↥(StatedSL 3 K)) (w : W),
      e (((π γ : ↥H) : MulAut W) w) = Multiplicative.ofAdd
        (((γ : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
          Multiplicative.toAdd (e w))) :
    ∀ y ∈ Y, ∀ c : K,
      e.symm (Multiplicative.ofAdd (c • Multiplicative.toAdd (e y))) ∈ Y := by
  intro y hy c
  refine mem_of_fixed_sylow_three hH hn S hYS hY ?_
  intro s hs
  exact action_smul_scalar hπ hact s (hYS s hs y hy) c

private theorem exists_fixed_vector {W : Type} [CommGroup W] [Finite W]
    {K : Type} [Field K] {Y : Subgroup W} {n : ℕ}
    (hY : Nat.card Y = 2 ^ n) (hn : 2 ≤ n)
    (e : W ≃* Multiplicative (Fin 3 → K)) (f : MulAut W) (hfix : ∀ y ∈ Y, f y = y) :
    ∃ (y : Y) (v : Fin 3 → K), v ≠ 0 ∧ v = Multiplicative.toAdd (e (y : W)) ∧
      coordAddEquiv e f v = v := by
  have hYgt : 1 < Nat.card Y := by
    rw [hY]
    calc 1 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  letI : Fintype Y := Fintype.ofFinite Y
  have hYgt' : 1 < Fintype.card Y := by
    rwa [Nat.card_eq_fintype_card] at hYgt
  obtain ⟨y, hyne⟩ := Fintype.exists_ne_of_one_lt_card hYgt' (1 : Y)
  have hyY : (y : W) ∈ Y := y.2
  have hy1 : (y : W) ≠ 1 := fun h => hyne (Subtype.ext h)
  let v : Fin 3 → K := Multiplicative.toAdd (e (y : W))
  have hv : v ≠ 0 := by
    intro h0
    apply hy1
    apply e.injective
    rw [map_one, ← ofAdd_toAdd (e (y : W))]
    change Multiplicative.ofAdd v = 1
    rw [h0]
    rfl
  have hfixv : coordAddEquiv e f v = v := by
    dsimp [coordAddEquiv, v]
    rw [MulEquiv.symm_apply_apply, hfix (y : W) hyY]
  exact ⟨y, v, hv, rfl, hfixv⟩

private theorem normalizes_specialLinear {W : Type} [CommGroup W]
    {H : Subgroup (MulAut W)} {K : Type} [Field K]
    {π : ↥(StatedSL 3 K) →* ↥H} {e : W ≃* Multiplicative (Fin 3 → K)}
    (hπ : Function.Surjective π)
    (hact : ∀ (γ : ↥(StatedSL 3 K)) (w : W),
      e (((π γ : ↥H) : MulAut W) w) = Multiplicative.ofAdd
        (((γ : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
          Multiplicative.toAdd (e w)))
    {f : MulAut W} (hnorm : ∀ h ∈ H, f * h * f⁻¹ ∈ H) :
    ∀ g : Matrix.SpecialLinearGroup (Fin 3) K,
      ∃ g' : Matrix.SpecialLinearGroup (Fin 3) K, ∀ v : Fin 3 → K,
        coordAddEquiv e f ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ v) =
          (g' : Matrix (Fin 3) (Fin 3) K) *ᵥ coordAddEquiv e f v := by
  intro g
  let γ : ↥(StatedSL 3 K) := specialLinearGroupEquivStatedSL 3 K g
  have hγcoe : ((γ : Matrix.GeneralLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = (g : Matrix (Fin 3) (Fin 3) K) :=
    specialLinearGroupEquivStatedSL_coe 3 K g
  have hh : f * ((π γ : ↥H) : MulAut W) * f⁻¹ ∈ H := hnorm _ (π γ).2
  obtain ⟨γ', hγ'⟩ := hπ ⟨f * ((π γ : ↥H) : MulAut W) * f⁻¹, hh⟩
  let g' : Matrix.SpecialLinearGroup (Fin 3) K :=
    (specialLinearGroupEquivStatedSL 3 K).symm γ'
  have hg'coe : ((γ' : Matrix.GeneralLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = (g' : Matrix (Fin 3) (Fin 3) K) := by
    simpa [g'] using specialLinearGroupEquivStatedSL_coe 3 K g'
  refine ⟨g', fun v => ?_⟩
  have h1 : e.symm (Multiplicative.ofAdd ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ v)) =
      ((π γ : ↥H) : MulAut W) (e.symm (Multiplicative.ofAdd v)) := by
    apply e.injective
    rw [MulEquiv.apply_symm_apply, hact γ (e.symm (Multiplicative.ofAdd v)), hγcoe]
    simp
  calc coordAddEquiv e f ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ v)
      = Multiplicative.toAdd (e (f (e.symm (Multiplicative.ofAdd
          ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ v))))) := rfl
    _ = Multiplicative.toAdd (e (f (((π γ : ↥H) : MulAut W)
          (e.symm (Multiplicative.ofAdd v))))) := by
        rw [h1]
    _ = Multiplicative.toAdd (e ((f * ((π γ : ↥H) : MulAut W) * f⁻¹)
          (f (e.symm (Multiplicative.ofAdd v))))) := by
        simp [MulAut.mul_apply]
    _ = Multiplicative.toAdd (e (((π γ' : ↥H) : MulAut W)
          (f (e.symm (Multiplicative.ofAdd v))))) := by rw [hγ']
    _ = (g' : Matrix (Fin 3) (Fin 3) K) *ᵥ coordAddEquiv e f v := by
        rw [hact γ', hg'coe]
        rfl

private theorem exists_linear_of_semilinear {W : Type} [CommGroup W]
    {K : Type} [Field K] [Finite K] {n : ℕ}
    {e : W ≃* Multiplicative (Fin 3 → K)} {f : MulAut W} {Y : Subgroup W}
    (hYscale : ∀ y ∈ Y, ∀ c : K,
      e.symm (Multiplicative.ofAdd (c • Multiplicative.toAdd (e y))) ∈ Y)
    (hfix : ∀ y ∈ Y, f y = y) (hn : 2 ≤ n) (hKcard : Nat.card K = 2 ^ n)
    {y : Y} {v : Fin 3 → K} (hv : v ≠ 0) (hvdef : v = Multiplicative.toAdd (e (y : W)))
    (hfixv : coordAddEquiv e f v = v)
    (hnormSL : ∀ g : Matrix.SpecialLinearGroup (Fin 3) K,
      ∃ g' : Matrix.SpecialLinearGroup (Fin 3) K, ∀ v : Fin 3 → K,
        coordAddEquiv e f ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ v) =
          (g' : Matrix (Fin 3) (Fin 3) K) *ᵥ coordAddEquiv e f v) :
    ∃ L : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K),
      ∀ x : Fin 3 → K, L x = coordAddEquiv e f x := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 :=
    CFSG.Quasithin.Vol2.KGNat.charP_two_of_card (by omega) hKcard
  have hFcard : Fintype.card K = 2 ^ n := by
    rwa [Nat.card_eq_fintype_card] at hKcard
  obtain ⟨μ, hμ⟩ :=
    CFSG.LocalAnalysis.RankThreeUC.S15.semilinear_of_normalizes hn hFcard
      (coordAddEquiv e f) hnormSL
  have hμeq : ∀ c : K, μ c = c := by
    intro c
    have h1 : coordAddEquiv e f (c • v) = c • v := by
      have hz : e.symm (Multiplicative.ofAdd (c • Multiplicative.toAdd (e (y : W)))) ∈ Y :=
        hYscale (y : W) y.2 c
      have hz' : f (e.symm (Multiplicative.ofAdd (c • v))) =
          e.symm (Multiplicative.ofAdd (c • v)) := by
        rw [hvdef]
        exact hfix _ hz
      dsimp [coordAddEquiv] at hz' ⊢
      rw [hz']
      simp
    have h2 : coordAddEquiv e f (c • v) = μ c • coordAddEquiv e f v := hμ c v
    rw [hfixv, h1] at h2
    exact (smul_left_injective K hv h2).symm
  refine ⟨(coordAddEquiv e f).toLinearEquiv ?_, fun x => rfl⟩
  intro c x
  rw [hμ c x, hμeq c]

private theorem det_eq_one_of_iterate_eq_one {K : Type} [Field K] [Finite K] {n k : ℕ}
    (hn : 0 < n) (hKcard : Nat.card K = 2 ^ n)
    (L : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (hLpow : L ^ (2 ^ k) = 1) :
    LinearEquiv.det L = 1 := by
  apply Units.ext
  have hodd : Odd (2 ^ n - 1) := CFSG.Timmesfeld.Orders.odd_two_pow_sub_one hn
  have hcop : Nat.Coprime (2 ^ k) (2 ^ n - 1) :=
    (Nat.coprime_two_left.mpr hodd).pow_left k
  have hd : (LinearEquiv.det L : K) ^ (2 ^ k) = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, hLpow, map_one]
    rfl
  exact CFSG.Quasithin.Vol2.Ch11.SecE.EK1.eq_one_of_pow_coprime (n := n) (m := 2 ^ k)
    hKcard (by positivity) hcop hd

private theorem exists_linear_det_one {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {n : ℕ}
    (hH : BinaryNaturalSL H ⊤ ⊥ 3 n) (hn : 2 ≤ n) (S : Sylow 2 ↥H) {Y : Subgroup W}
    (hYS : ∀ s ∈ (S : Subgroup ↥H), ∀ y ∈ Y, (s : MulAut W) y = y) (hY : Nat.card Y = 2 ^ n)
    {K : Type} [Field K] [Finite K] (hKcard : Nat.card K = 2 ^ n)
    {π : ↥(StatedSL 3 K) →* ↥H} {e : W ≃* Multiplicative (Fin 3 → K)}
    (hπ : Function.Surjective π)
    (hact : ∀ (γ : ↥(StatedSL 3 K)) (w : W),
      e (((π γ : ↥H) : MulAut W) w) = Multiplicative.ofAdd
        (((γ : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
          Multiplicative.toAdd (e w)))
    {f : MulAut W} (hnorm : ∀ h ∈ H, f * h * f⁻¹ ∈ H)
    (hf2 : ∃ k : ℕ, f ^ (2 ^ k) = 1) (hfix : ∀ y ∈ Y, f y = y) :
    ∃ L : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K),
      (∀ w : W, L (Multiplicative.toAdd (e w)) = Multiplicative.toAdd (e (f w))) ∧
      LinearEquiv.det L = 1 := by
  classical
  obtain ⟨k, hfpow⟩ := hf2
  have hYscale := smul_mem_of_fixed_sylow hH hn S hYS hY hπ hact
  obtain ⟨y, v, hv, hvdef, hfixv⟩ := exists_fixed_vector hY hn e f hfix
  have hnormSL := normalizes_specialLinear hπ hact hnorm
  obtain ⟨L, hLapply⟩ :=
    exists_linear_of_semilinear (y := y) hYscale hfix hn hKcard hv hvdef hfixv hnormSL
  have hLfun : (⇑L : (Fin 3 → K) → (Fin 3 → K)) = coordAddEquiv e f := by
    funext x
    exact hLapply x
  have hLpow : L ^ (2 ^ k) = 1 := by
    apply LinearEquiv.ext
    intro x
    rw [LinearEquiv.coe_pow, hLfun]
    change ((coordAddEquiv e f)^[2 ^ k]) x = x
    rw [coordAddEquiv_iterate_eq_id e f hfpow]
    rfl
  have hLdet : LinearEquiv.det L = 1 :=
    det_eq_one_of_iterate_eq_one (by omega) hKcard L hLpow
  refine ⟨L, fun w => ?_, hLdet⟩
  rw [hLapply]
  simp [coordAddEquiv]

theorem mem_of_normalizes_three {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {n : ℕ}
    (hH : BinaryNaturalSL H ⊤ ⊥ 3 n) (hn : 2 ≤ n) (S : Sylow 2 ↥H) {Y : Subgroup W}
    (hYS : ∀ s ∈ (S : Subgroup ↥H), ∀ y ∈ Y, (s : MulAut W) y = y) (hY : Nat.card Y = 2 ^ n)
    {f : MulAut W} (hnorm : ∀ h ∈ H, f * h * f⁻¹ ∈ H) (hf2 : ∃ k : ℕ, f ^ (2 ^ k) = 1)
    (hfix : ∀ y ∈ Y, f y = y) : f ∈ H := by
  classical
  obtain ⟨K, hKfield, hKfin, hKcard, π, e, hreal, hπ, hact⟩ := exists_coordinates_three hH
  letI : Field K := hKfield
  letI : Finite K := hKfin
  obtain ⟨L, hLapply, hLdet⟩ :=
    exists_linear_det_one hH hn S hYS hY hKcard hπ hact hnorm hf2 hfix
  let M : Matrix (Fin 3) (Fin 3) K := LinearMap.toMatrix' L.toLinearMap
  have hMdet : M.det = 1 := by
    rw [LinearMap.det_toMatrix', ← LinearEquiv.coe_det L, hLdet]
    rfl
  let A : Matrix.SpecialLinearGroup (Fin 3) K := ⟨M, hMdet⟩
  let γ : ↥(StatedSL 3 K) := specialLinearGroupEquivStatedSL 3 K A
  have hγcoe : ((γ : Matrix.GeneralLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = M :=
    specialLinearGroupEquivStatedSL_coe 3 K A
  have hfπ : ((π γ : ↥H) : MulAut W) = f := by
    ext w
    apply e.injective
    rw [hact γ w, hγcoe]
    rw [show M *ᵥ Multiplicative.toAdd (e w) =
        Multiplicative.toAdd (e (f w)) from ?_]
    · rfl
    rw [show M *ᵥ Multiplicative.toAdd (e w) = L (Multiplicative.toAdd (e w)) from
      LinearMap.toMatrix'_mulVec L.toLinearMap _, hLapply w]
  rw [← hfπ]
  exact (π γ).2

end CFSG.Quasithin.BinaryNaturalSL

end
