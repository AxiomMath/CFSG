module

public import CFSG.GH74.Filter.Lie.ZModTwo
public import CFSG.GH74.Filter.Statements
public import CFSG.GH74.Filter.Witness
public import CFSG.LocalAnalysis.SectionRank.ExceptionalModels

public section

namespace CFSG.GH74.Filter.Lie

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Open CFSG.SectionRank CFSG.LieType.Chevalley
  CFSG.LieType.BorelTits

theorem eq_one_of_prod_five {G : Type*} [Group G] {A : Fin 5 → Subgroup G} (hind : iSupIndep A)
    {a : Fin 5 → G} (ha : ∀ i, a i ∈ A i) (h : a 0 * a 1 * a 2 * a 3 * a 4 = 1) :
    ∀ i, a i = 1 := by
  have hmem : ∀ i j, j ≠ i → a j ∈ ⨆ (k : Fin 5) (_ : k ≠ i), A k := fun i j hj =>
    (le_iSup₂_of_le (f := fun (k : Fin 5) (_ : k ≠ i) => A k) j hj le_rfl) (ha j)
  have key : ∀ i, a i ∈ ⨆ (k : Fin 5) (_ : k ≠ i), A k → a i = 1 := fun i hi => by
    have := (hind i).le_bot ⟨ha i, hi⟩
    exact (Subgroup.mem_bot).1 this
  intro i
  apply key i
  match i with
  | 0 =>
    have e : a 0 = (a 1 * a 2 * a 3 * a 4)⁻¹ := by
      calc a 0 = a 0 * a 1 * a 2 * a 3 * a 4 * (a 1 * a 2 * a 3 * a 4)⁻¹ := by group
        _ = _ := by rw [h, one_mul]
    rw [e]
    exact inv_mem (mul_mem (mul_mem (mul_mem (hmem _ _ (by decide)) (hmem _ _ (by decide)))
      (hmem _ _ (by decide))) (hmem _ _ (by decide)))
  | 1 =>
    have e : a 1 = (a 0)⁻¹ * (a 2 * a 3 * a 4)⁻¹ := by
      calc a 1 = (a 0)⁻¹ * (a 0 * a 1 * a 2 * a 3 * a 4) * (a 2 * a 3 * a 4)⁻¹ := by group
        _ = _ := by rw [h, mul_one]
    rw [e]
    exact mul_mem (inv_mem (hmem _ _ (by decide)))
      (inv_mem (mul_mem (mul_mem (hmem _ _ (by decide)) (hmem _ _ (by decide)))
        (hmem _ _ (by decide))))
  | 2 =>
    have e : a 2 = (a 0 * a 1)⁻¹ * (a 3 * a 4)⁻¹ := by
      calc a 2 = (a 0 * a 1)⁻¹ * (a 0 * a 1 * a 2 * a 3 * a 4) * (a 3 * a 4)⁻¹ := by group
        _ = _ := by rw [h, mul_one]
    rw [e]
    exact mul_mem (inv_mem (mul_mem (hmem _ _ (by decide)) (hmem _ _ (by decide))))
      (inv_mem (mul_mem (hmem _ _ (by decide)) (hmem _ _ (by decide))))
  | 3 =>
    have e : a 3 = (a 0 * a 1 * a 2)⁻¹ * (a 4)⁻¹ := by
      calc a 3 = (a 0 * a 1 * a 2)⁻¹ * (a 0 * a 1 * a 2 * a 3 * a 4) * (a 4)⁻¹ := by group
        _ = _ := by rw [h, mul_one]
    rw [e]
    exact mul_mem (inv_mem (mul_mem (mul_mem (hmem _ _ (by decide)) (hmem _ _ (by decide)))
      (hmem _ _ (by decide)))) (inv_mem (hmem _ _ (by decide)))
  | 4 =>
    have e : a 4 = (a 0 * a 1 * a 2 * a 3)⁻¹ := by
      calc a 4 = (a 0 * a 1 * a 2 * a 3)⁻¹ * (a 0 * a 1 * a 2 * a 3 * a 4) := by group
        _ = _ := by rw [h, mul_one]
    rw [e]
    exact inv_mem (mul_mem (mul_mem (mul_mem (hmem _ _ (by decide)) (hmem _ _ (by decide)))
      (hmem _ _ (by decide))) (hmem _ _ (by decide)))

abbrev d4Vec5 : Fin 5 → Fin TwistTag.D4.tag.rank → ℤ :=
  ![([2] : List (Fin 4)).foldr (reflect _) (Pi.single (0 : Fin 4) 1),
    ([2] : List (Fin 4)).foldr (reflect _) (Pi.single (1 : Fin 4) 1),
    ([2] : List (Fin 4)).foldr (reflect _) (Pi.single (3 : Fin 4) 1),
    Pi.single (2 : Fin 4) 1,
    ([2, 3, 1, 2] : List (Fin 4)).foldr (reflect _) (Pi.single (0 : Fin 4) 1)]

@[expose] def d4SepWords5 : Fin 5 → List (Fin TwistTag.D4.tag.rank) :=
  ![([2, 0] : List (Fin 4)), ([2, 1] : List (Fin 4)), ([2, 3] : List (Fin 4)),
    ([2] : List (Fin 4)), ([2, 1, 0, 2, 3, 2, 1, 0] : List (Fin 4))]

@[expose] def d4ThetaWord : List (Fin TwistTag.D4.tag.rank) := ([2, 3, 1, 2] : List (Fin 4))

theorem d4_pair_check5 : ∀ i j : Fin 5, i ≠ j →
    pairCheck _ (d4Vec5 i) (d4Vec5 j) = true := by
  decide +kernel

theorem d4_sep_check5 : ∀ i : Fin 5,
    height ((d4SepWords5 i).foldr (reflect TwistTag.D4.tag) (d4Vec5 i)) < 0 ∧
      ∀ j, i ≠ j → 0 < height ((d4SepWords5 i).foldr (reflect TwistTag.D4.tag) (d4Vec5 j)) := by
  decide +kernel

theorem d4_theta_fixed : List.ofFn (permLattice TwistTag.D4.perm (d4Vec5 4)) =
    List.ofFn (d4Vec5 4) := by
  decide +kernel

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem le_pRank_commutator_twistFixed_D4_five
    (σ : K →+* K) {m : ℕ}
    (hK : Nat.card K = 2 ^ m) (hσ : Function.Surjective σ) (hσ3 : ∀ c, σ (σ (σ c)) = c)
    {u : Kˣ} (hu : (u : K) ^ 2 ≠ 1) :
    m + 2 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup (commutator (twistFixed .D4 K σ))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set τ := TwistTag.D4.tag
  set s₂ : WeylGroup τ := (coxeterSystem τ).wordProd d4S2Word
  set n := nrep τ K s₂
  have hs₂ : weylTwist .D4 s₂ = s₂ := weylTwist_wordProd_eq (ω := d4S2Word) d4_s2_fixed
  set α : Fin 5 → Root τ := ![s₂ • simpleRoot τ d4i0, s₂ • simpleRoot τ d4i1,
    s₂ • simpleRoot τ d4i3, simpleRoot τ d4i2,
    (coxeterSystem τ).wordProd d4ThetaWord • simpleRoot τ d4i0]
  have hαv : ∀ j, (α j).1 = d4Vec5 j := by
    intro j
    match j with
    | 0 =>
      change ((coxeterSystem τ).wordProd d4S2Word • simpleRoot τ d4i0).1 = _
      rw [coe_smul_root, wordProd_smul]; rfl
    | 1 =>
      change ((coxeterSystem τ).wordProd d4S2Word • simpleRoot τ d4i1).1 = _
      rw [coe_smul_root, wordProd_smul]; rfl
    | 2 =>
      change ((coxeterSystem τ).wordProd d4S2Word • simpleRoot τ d4i3).1 = _
      rw [coe_smul_root, wordProd_smul]; rfl
    | 3 => rfl
    | 4 =>
      change ((coxeterSystem τ).wordProd d4ThetaWord • simpleRoot τ d4i0).1 = _
      rw [coe_smul_root, wordProd_smul]; rfl
  have hpc : ∀ i j, i ≠ j → pairCheck τ (α i).1 (α j).1 = true := fun i j hij => by
    rw [hαv, hαv]; exact d4_pair_check5 i j hij
  have hposα : ∀ j, 0 < height (α j).1 := fun j => by
    have := hpc j (j + 1) (by omega)
    simp only [pairCheck, Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1.1.1.1.1
  have hind : iSupIndep fun j => (nativeRootSubgroups τ K).X (α j) :=
    iSupIndep_X_of_separated (K := K) α hposα
      (fun j => (coxeterSystem τ).wordProd (d4SepWords5 j))
      (fun j => by rw [wordProd_smul, hαv]; exact (d4_sep_check5 j).1)
      (fun i j hij => by rw [wordProd_smul, hαv]; exact (d4_sep_check5 i).2 j hij)
  have hcX : ∀ i j, i ≠ j → ∀ x ∈ (nativeRootSubgroups τ K).X (α i),
      ∀ y ∈ (nativeRootSubgroups τ K).X (α j), Commute x y := fun i j hij x hx y hy =>
    commute_of_mem_X_of_pairCheck (hpc i j hij) hx hy
  have hconjX : ∀ (k : Fin τ.rank) (c : K), n * xElement k c * n⁻¹ ∈
      (nativeRootSubgroups τ K).X (s₂ • simpleRoot τ k) := fun k c => by
    rw [← eltElement_simpleRoot]
    exact nrep_conj_mem_X s₂ ((rootOperatorFamily τ).eltElement_mem_rootSubgroup _ _)
  have hx0 : ∀ c, n * xElement d4i0 c * n⁻¹ ∈ (nativeRootSubgroups τ K).X (α 0) :=
    hconjX d4i0
  have hx1 : ∀ c, n * xElement d4i1 c * n⁻¹ ∈ (nativeRootSubgroups τ K).X (α 1) :=
    hconjX d4i1
  have hx3 : ∀ c, n * xElement d4i3 c * n⁻¹ ∈ (nativeRootSubgroups τ K).X (α 2) :=
    hconjX d4i3
  have hx2 : ∀ c, xElement (τ := τ) d4i2 c ∈ (nativeRootSubgroups τ K).X (α 3) :=
    fun c => xElement_mem_X _ c
  have hxθ : ∀ c, (rootOperatorFamily τ).eltElement (α 4) c ∈
      (nativeRootSubgroups τ K).X (α 4) :=
    fun c => (rootOperatorFamily τ).eltElement_mem_rootSubgroup _ _
  have hc01 : ∀ a b : K, Commute (xElement (τ := τ) d4i0 a) (xElement d4i1 b) :=
    fun a b => commute_of_mem_simple (by decide) (by decide) (xElement_mem_X _ _)
      (xElement_mem_X _ _)
  have hc03 : ∀ a b : K, Commute (xElement (τ := τ) d4i0 a) (xElement d4i3 b) :=
    fun a b => commute_of_mem_simple (by decide) (by decide) (xElement_mem_X _ _)
      (xElement_mem_X _ _)
  have hc13 : ∀ a b : K, Commute (xElement (τ := τ) d4i1 a) (xElement d4i3 b) :=
    fun a b => commute_of_mem_simple (by decide) (by decide) (xElement_mem_X _ _)
      (xElement_mem_X _ _)
  set y : K → adjointGroup τ K := fun c =>
    xElement d4i0 c * xElement d4i1 (σ c) * xElement d4i3 (σ (σ c))
  have hy_add : ∀ c d, y (c + d) = y c * y d := by
    intro c d
    simp only [y, map_add, xElement_add]
    have e1 := (hc01 d (σ c)).eq
    have e2 := (hc03 d (σ (σ c))).eq
    have e3 := (hc13 (σ d) (σ (σ c))).eq
    set A := xElement (τ := τ) (K := K) d4i0 c
    set A' := xElement (τ := τ) (K := K) d4i0 d
    set B := xElement (τ := τ) (K := K) d4i1 (σ c)
    set B' := xElement (τ := τ) (K := K) d4i1 (σ d)
    set C := xElement (τ := τ) (K := K) d4i3 (σ (σ c))
    set C' := xElement (τ := τ) (K := K) d4i3 (σ (σ d))
    calc A * A' * (B * B') * (C * C') = A * (A' * B) * B' * C * C' := by group
      _ = A * (B * A') * B' * C * C' := by rw [e1]
      _ = A * B * A' * (B' * C) * C' := by group
      _ = A * B * A' * (C * B') * C' := by rw [e3]
      _ = A * B * (A' * C) * B' * C' := by group
      _ = A * B * (C * A') * B' * C' := by rw [e2]
      _ = A * B * C * (A' * B' * C') := by group
  have hyF : ∀ c, twistC .D4 K σ (y c) = y c := by
    intro c
    simp only [y, map_mul, twistC_xElement, d4_perm_0, d4_perm_1, d4_perm_3, hσ3]
    have e1 := (hc01 c (σ c)).eq
    have e2 := (hc03 c (σ (σ c))).eq
    calc xElement (τ := τ) d4i1 (σ c) * xElement d4i3 (σ (σ c)) * xElement d4i0 c
        = xElement d4i1 (σ c) * (xElement d4i3 (σ (σ c)) * xElement d4i0 c) := by group
      _ = xElement d4i1 (σ c) * (xElement d4i0 c * xElement d4i3 (σ (σ c))) := by rw [e2]
      _ = (xElement d4i1 (σ c) * xElement d4i0 c) * xElement d4i3 (σ (σ c)) := by group
      _ = (xElement d4i0 c * xElement d4i1 (σ c)) * xElement d4i3 (σ (σ c)) := by rw [e1]
  set Y : Multiplicative K →* adjointGroup τ K :=
    { toFun := fun c => y (Multiplicative.toAdd c)
      map_one' := by simp only [y, toAdd_one, map_zero, xElement_zero, mul_one]
      map_mul' := fun c d => hy_add _ _ }
  set Z : Multiplicative K →* adjointGroup τ K := (MulAut.conj n).toMonoidHom.comp Y
  set ι : Multiplicative (ZMod 2) →* Multiplicative K :=
    (ZMod.castHom (dvd_refl 2) K).toAddMonoidHom.toMultiplicative
  have hι : Function.Injective ι := fun a b h =>
    Multiplicative.toAdd.injective (ZMod.castHom_injective K (Multiplicative.ofAdd.injective h))
  set X2 : Multiplicative (ZMod 2) →* adjointGroup τ K :=
    (rootHom (simpleRoot τ d4i2)).comp ι
  set Xθ : Multiplicative (ZMod 2) →* adjointGroup τ K := (rootHom (α 4)).comp ι
  have hZ : ∀ c : Multiplicative K, Z c = n * xElement d4i0 (Multiplicative.toAdd c) * n⁻¹ *
      (n * xElement d4i1 (σ (Multiplicative.toAdd c)) * n⁻¹) *
      (n * xElement d4i3 (σ (σ (Multiplicative.toAdd c))) * n⁻¹) := fun c => by
    change n * y (Multiplicative.toAdd c) * n⁻¹ = _
    simp only [y]
    group
  have hX2 : ∀ c' : Multiplicative (ZMod 2), X2 c' = xElement (τ := τ) d4i2
      (ZMod.castHom (dvd_refl 2) K (Multiplicative.toAdd c')) := fun c' =>
    eltElement_simpleRoot _ _
  have hXθ : ∀ b : Multiplicative (ZMod 2), Xθ b = (rootOperatorFamily τ).eltElement (α 4)
      (ZMod.castHom (dvd_refl 2) K (Multiplicative.toAdd b)) := fun b => rfl
  have hZX2 : ∀ c c', Commute (Z c) (X2 c') := by
    intro c c'
    rw [hZ, hX2]
    have h3 := hx2 (ZMod.castHom (dvd_refl 2) K (Multiplicative.toAdd c'))
    exact ((hcX 0 3 (by decide) _ (hx0 _) _ h3).mul_left
      (hcX 1 3 (by decide) _ (hx1 _) _ h3)).mul_left (hcX 2 3 (by decide) _ (hx3 _) _ h3)
  have hZXθ : ∀ c b, Commute (Z c) (Xθ b) := by
    intro c b
    rw [hZ, hXθ]
    have h4 := hxθ (ZMod.castHom (dvd_refl 2) K (Multiplicative.toAdd b))
    exact ((hcX 0 4 (by decide) _ (hx0 _) _ h4).mul_left
      (hcX 1 4 (by decide) _ (hx1 _) _ h4)).mul_left (hcX 2 4 (by decide) _ (hx3 _) _ h4)
  have hX2Xθ : ∀ c' b, Commute (X2 c') (Xθ b) := by
    intro c' b
    rw [hX2, hXθ]
    exact hcX 3 4 (by decide) _ (hx2 _) _ (hxθ _)
  set Ψ : Multiplicative K × Multiplicative (ZMod 2) →* adjointGroup τ K :=
    Z.noncommCoprod X2 hZX2
  have hΨXθ : ∀ (a : Multiplicative K × Multiplicative (ZMod 2)) (b : Multiplicative (ZMod 2)),
      Commute (Ψ a) (Xθ b) := fun a b => by
    rw [MonoidHom.noncommCoprod_apply]
    exact (hZXθ _ _).mul_left (hX2Xθ _ _)
  set Ψ' : (Multiplicative K × Multiplicative (ZMod 2)) × Multiplicative (ZMod 2) →*
      adjointGroup τ K := Ψ.noncommCoprod Xθ hΨXθ
  have hΨ'apply : ∀ c c' b, Ψ' ((c, c'), b) = Z c * X2 c' * Xθ b := fun _ _ _ => rfl
  have hΨ' : Function.Injective Ψ' := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨⟨c, c'⟩, b⟩ h
    rw [MonoidHom.mem_ker, hΨ'apply, hZ, hX2, hXθ] at h
    have h4 := eq_one_of_prod_five (A := fun j => (nativeRootSubgroups τ K).X (α j)) hind
      (a := ![n * xElement d4i0 (Multiplicative.toAdd c) * n⁻¹,
        n * xElement d4i1 (σ (Multiplicative.toAdd c)) * n⁻¹,
        n * xElement d4i3 (σ (σ (Multiplicative.toAdd c))) * n⁻¹,
        xElement (τ := τ) d4i2 (ZMod.castHom (dvd_refl 2) K (Multiplicative.toAdd c')),
        (rootOperatorFamily τ).eltElement (α 4)
          (ZMod.castHom (dvd_refl 2) K (Multiplicative.toAdd b))])
      (fun j => by
        match j with
        | 0 => exact hx0 _
        | 1 => exact hx1 _
        | 2 => exact hx3 _
        | 3 => exact hx2 _
        | 4 => exact hxθ _) h
    have ha0 : n * xElement d4i0 (Multiplicative.toAdd c) * n⁻¹ = 1 := h4 0
    have ha3 : xElement (τ := τ) d4i2
        (ZMod.castHom (dvd_refl 2) K (Multiplicative.toAdd c')) = 1 := h4 3
    have ha4 : (rootOperatorFamily τ).eltElement (α 4)
        (ZMod.castHom (dvd_refl 2) K (Multiplicative.toAdd b)) = 1 := h4 4
    rw [mul_inv_eq_one, mul_eq_left] at ha0
    have hc : Multiplicative.toAdd c = 0 :=
      xElement_injective _ (ha0.trans (xElement_zero _).symm)
    have hc' : ZMod.castHom (dvd_refl 2) K (Multiplicative.toAdd c') = 0 :=
      xElement_injective _ (ha3.trans (xElement_zero _).symm)
    have hb : ZMod.castHom (dvd_refl 2) K (Multiplicative.toAdd b) = 0 :=
      eltElement_injective (α 4) (ha4.trans ((rootOperatorFamily τ).eltElement_zero (α 4)).symm)
    rw [Subgroup.mem_bot, Prod.mk_eq_one, Prod.mk_eq_one]
    exact ⟨⟨hc, Multiplicative.toAdd.injective ((ZMod.castHom_injective K)
      (hc'.trans (map_zero _).symm))⟩, Multiplicative.toAdd.injective ((ZMod.castHom_injective K)
      (hb.trans (map_zero _).symm))⟩
  have hU : ∀ x ∈ (nativeData τ K).U, twistC .D4 K σ x = x → x ∈ twistDerived .D4 K σ :=
    d4_U_le_twistDerived hσ hσ3 hu
  have hUα : ∀ j, (nativeRootSubgroups τ K).X (α j) ≤ (nativeData τ K).U := fun j =>
    RootGroupData.X_le_U (D := nativeData τ K) (hposα j)
  have hθfix : rootTwist .D4 (α 4) = α 4 := Subtype.ext (by
    have h := List.ofFn_injective d4_theta_fixed
    rw [← hαv 4] at h
    exact h)
  have hθ1 : ∀ z : ZMod 2, twistC .D4 K σ ((rootOperatorFamily τ).eltElement (α 4)
      (ZMod.castHom (dvd_refl 2) K z)) = (rootOperatorFamily τ).eltElement (α 4)
      (ZMod.castHom (dvd_refl 2) K z) := by
    intro z
    rcases zmod_two_eq_zero_or_one z with rfl | rfl
    · rw [map_zero, RootOperatorFamily.eltElement_zero, map_one]
    · rw [map_one]
      exact twistC_eltElement_one_charTwo σ hθfix
  have hn : twistC .D4 K σ n = n := by rw [twistC_nrep, hs₂]
  have hFZ : ∀ c, twistC .D4 K σ (Z c) = Z c := fun c => by
    change twistC .D4 K σ (n * y (Multiplicative.toAdd c) * n⁻¹) =
      n * y (Multiplicative.toAdd c) * n⁻¹
    rw [map_mul, map_mul, map_inv, hn, hyF]
  have hF2 : ∀ c', twistC .D4 K σ (X2 c') = X2 c' := fun c' => by
    rw [hX2, twistC_xElement, d4_perm_2, ringHom_zmod_cast]
  have hFθ : ∀ b, twistC .D4 K σ (Xθ b) = Xθ b := fun b => by
    rw [hXθ]
    exact hθ1 _
  have hrange : Ψ'.range ≤ twistDerived .D4 K σ := by
    rintro _ ⟨⟨⟨c, c'⟩, b⟩, rfl⟩
    rw [hΨ'apply]
    refine hU _ ?_ ?_
    · rw [hZ, hX2, hXθ]
      exact mul_mem (mul_mem (mul_mem (mul_mem (hUα 0 (hx0 _)) (hUα 1 (hx1 _)))
        (hUα 2 (hx3 _))) (hUα 3 (hx2 _))) (hUα 4 (hxθ _))
    · rw [map_mul, map_mul, hFZ c, hF2 c', hFθ b]
  have hpow : ∀ a : (Multiplicative K × Multiplicative (ZMod 2)) × Multiplicative (ZMod 2),
      a ^ 2 = 1 := fun a => by
    refine Prod.ext (Prod.ext ?_ ?_) ?_
    · change Multiplicative.ofAdd (2 • Multiplicative.toAdd a.1.1) = 1
      rw [nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
      rfl
    · exact multiplicative_zmod_two_sq _
    · exact multiplicative_zmod_two_sq _
  refine le_pRank_of_commutator (p := 2) hΨ' hrange (fun a b => mul_comm a b) hpow
    (k := m + 2) (by
    rw [Nat.card_prod, Nat.card_prod,
      show Nat.card (Multiplicative K) = Nat.card K from Nat.card_congr Multiplicative.toAdd, hK,
      show Nat.card (Multiplicative (ZMod 2)) = 2 from by
        rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]]
    ring)

theorem five_le_pRank_of_trialityD4Model_two
    {S : Type} [Group S] [Finite S] {f : ℕ}
    (hf : 1 ≤ f) (h : TwistedChevalleyModel S .D4 (2 ^ f)) :
    5 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup S) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, _, _, _, σ, hK, hσ, hσc, hfr, ⟨u, hu⟩, ⟨e⟩⟩ := twistedModel_data hf h
  have hσ3 : ∀ c, σ (σ (σ c)) = c := fun c => by
    rw [hσc, hσc, hσc, ← pow_mul, ← pow_mul, show 2 ^ f * (2 ^ f * 2 ^ f) = Nat.card K by
      rw [hK]; change _ = 2 ^ (f * 3); ring, hfr]
  have := Finite.of_equiv _ e.toEquiv
  rw [pRank_top_eq_of_mulEquiv (by norm_num) e,
    pRank_twistedDerivedQuotient σ hσ (d4_U_le_twistDerived hσ hσ3 hu)]
  by_cases hf2 : 2 ≤ f
  · have h1 := le_pRank_commutator_twistFixed_D4 σ hK hσ hσ3 hu
    change f * 3 + 1 ≤ _ at h1
    omega
  · have hf1 : f = 1 := by omega
    subst hf1
    have h1 := le_pRank_commutator_twistFixed_D4_five σ (m := 1 * 3) hK hσ hσ3 hu
    omega

end CFSG.GH74.Filter.Lie

namespace CFSG.GH74.Filter

open CFSG.GH74.Filter.Lie
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Open CFSG.SectionRank CFSG.LieType.Chevalley
  CFSG.LieType.BorelTits

theorem t_3D4_even
    : S_3D4_even := by
  intro G _ _ f h
  obtain ⟨⟨-, hf, -⟩, hm⟩ := h
  exact not_gen4_of_twoRank (five_le_pRank_of_trialityD4Model_two hf hm)

end CFSG.GH74.Filter
