module

public import CFSG.LieType.Chevalley.RootRank
public import CFSG.LieType.Chevalley.TwistPerfect

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.Open CFSG.SectionRank

variable {τ : Tag} {K : Type} [Field K]

theorem nrep_conj_mem_X
    (w : WeylGroup τ) {α : Root τ} {x : adjointGroup τ K}
    (hx : x ∈ (rootOperatorFamily τ).rootSubgroup K α) :
    nrep τ K w * x * (nrep τ K w)⁻¹ ∈ (rootOperatorFamily τ).rootSubgroup K (w • α) := by
  obtain ⟨c, rfl⟩ := (rootOperatorFamily τ).mem_rootSubgroup.1 hx
  obtain ⟨ε, -, hε⟩ := exists_conj_nrep (K := K) w α
  rw [hε c]
  exact (rootOperatorFamily τ).eltElement_mem_rootSubgroup _ _

theorem ringHom_zmod_cast (σ : K →+* K) {p : ℕ} [CharP K p] (c : ZMod p) :
    σ (ZMod.castHom (dvd_refl p) K c) = ZMod.castHom (dvd_refl p) K c :=
  DFunLike.congr_fun (RingHom.ext_zmod (σ.comp (ZMod.castHom (dvd_refl p) K))
    (ZMod.castHom (dvd_refl p) K)) c

theorem le_pRank_of_commutator
    {t : TwistTag} [Finite K] {σ : K →+* K} {A : Type*} [Group A]
    {Ψ : A →* adjointGroup t.tag K} (hΨ : Function.Injective Ψ)
    (hrange : Ψ.range ≤ twistDerived t K σ) {p k : ℕ} [hp : Fact p.Prime]
    (hcomm : ∀ a b : A, a * b = b * a) (hpow : ∀ a : A, a ^ p = 1) (hA : Nat.card A = p ^ k) :
    k ≤ pRank p (⊤ : Subgroup (commutator (twistFixed t K σ))) := by
  set Γ := twistFixed t K σ
  have hΓ : ∀ a, Ψ a ∈ Γ := fun a => Subgroup.map_subtype_le _ (hrange ⟨a, rfl⟩)
  set Ψ₁ : A →* Γ := Ψ.codRestrict Γ hΓ
  have hΓ' : ∀ a, Ψ₁ a ∈ commutator Γ := fun a => by
    obtain ⟨h, hh, he⟩ := hrange ⟨a, rfl⟩
    have : Ψ₁ a = h := Subtype.ext he.symm
    rw [this]
    exact hh
  set Ψ₂ : A →* commutator Γ := Ψ₁.codRestrict (commutator Γ) hΓ'
  have hinj : Function.Injective Ψ₂ := fun a b h => hΨ (by
    have := congrArg (fun x : commutator Γ => ((x : Γ) : adjointGroup t.tag K)) h
    exact this)
  exact le_pRank_of_injective hp.out.one_lt hcomm hpow hA Ψ₂ hinj le_top

theorem eq_one_of_prod_four {G : Type*} [Group G] {A : Fin 4 → Subgroup G} (hind : iSupIndep A)
    {a : Fin 4 → G} (ha : ∀ i, a i ∈ A i) (h : a 0 * a 1 * a 2 * a 3 = 1) : ∀ i, a i = 1 := by
  have hmem : ∀ i j, j ≠ i → a j ∈ ⨆ (k : Fin 4) (_ : k ≠ i), A k := fun i j hj =>
    (le_iSup₂_of_le (f := fun (k : Fin 4) (_ : k ≠ i) => A k) j hj le_rfl) (ha j)
  have key : ∀ i, a i ∈ ⨆ (k : Fin 4) (_ : k ≠ i), A k → a i = 1 := fun i hi => by
    have := (hind i).le_bot ⟨ha i, hi⟩
    exact (Subgroup.mem_bot).1 this
  intro i
  apply key i
  match i with
  | 0 =>
    have e : a 0 = (a 1 * a 2 * a 3)⁻¹ := by
      calc a 0 = a 0 * a 1 * a 2 * a 3 * (a 1 * a 2 * a 3)⁻¹ := by group
        _ = _ := by rw [h, one_mul]
    rw [e]
    exact inv_mem (mul_mem (mul_mem (hmem _ _ (by decide)) (hmem _ _ (by decide)))
      (hmem _ _ (by decide)))
  | 1 =>
    have e : a 1 = (a 0)⁻¹ * (a 2 * a 3)⁻¹ := by
      calc a 1 = (a 0)⁻¹ * (a 0 * a 1 * a 2 * a 3) * (a 2 * a 3)⁻¹ := by group
        _ = _ := by rw [h, mul_one]
    rw [e]
    exact mul_mem (inv_mem (hmem _ _ (by decide)))
      (inv_mem (mul_mem (hmem _ _ (by decide)) (hmem _ _ (by decide))))
  | 2 =>
    have e : a 2 = (a 0 * a 1)⁻¹ * (a 3)⁻¹ := by
      calc a 2 = (a 0 * a 1)⁻¹ * (a 0 * a 1 * a 2 * a 3) * (a 3)⁻¹ := by group
        _ = _ := by rw [h, mul_one]
    rw [e]
    exact mul_mem (inv_mem (mul_mem (hmem _ _ (by decide)) (hmem _ _ (by decide))))
      (inv_mem (hmem _ _ (by decide)))
  | 3 =>
    have e : a 3 = (a 0 * a 1 * a 2)⁻¹ := by
      calc a 3 = (a 0 * a 1 * a 2)⁻¹ * (a 0 * a 1 * a 2 * a 3) := by group
        _ = _ := by rw [h, mul_one]
    rw [e]
    exact inv_mem (mul_mem (mul_mem (hmem _ _ (by decide)) (hmem _ _ (by decide)))
      (hmem _ _ (by decide)))

section E6

@[expose] def e6FixWords : Fin 4 → List (Fin TwistTag.E6.tag.rank) :=
  ![([] : List (Fin 6)), ([2, 4] : List (Fin 6)), ([0, 5, 2, 4] : List (Fin 6)),
    ([1, 3, 2, 4, 3, 1, 0, 5, 2, 4] : List (Fin 6))]

@[expose] def e6SepWords : Fin 4 → List (Fin TwistTag.E6.tag.rank) :=
  ![([3] : List (Fin 6)), ([4, 3, 2, 3, 4] : List (Fin 6)),
    ([5, 4, 3, 2, 0, 2, 3, 4, 5] : List (Fin 6)),
    ([1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1] : List (Fin 6))]

abbrev e6Fix : Fin TwistTag.E6.tag.rank := (3 : Fin 6)

abbrev e6Vec (j : Fin 4) : Fin TwistTag.E6.tag.rank → ℤ :=
  (e6FixWords j).foldr (reflect _) (Pi.single e6Fix 1)

theorem e6_fixWords_check : ∀ j : Fin 4, ∀ k : Fin TwistTag.E6.tag.rank,
    ((e6FixWords j).map TwistTag.E6.perm).foldr (reflect TwistTag.E6.tag) (Pi.single k 1) =
      (e6FixWords j).foldr (reflect TwistTag.E6.tag) (Pi.single k 1) := by
  decide +kernel

theorem e6_pair_check : ∀ i j : Fin 4, i ≠ j → pairCheck _ (e6Vec i) (e6Vec j) = true := by
  decide +kernel

theorem e6_sep_check : ∀ i : Fin 4,
    height ((e6SepWords i).foldr (reflect TwistTag.E6.tag) (e6Vec i)) < 0 ∧
      ∀ j, i ≠ j → 0 < height ((e6SepWords i).foldr (reflect TwistTag.E6.tag) (e6Vec j)) := by
  decide +kernel

theorem e6Fix_perm : TwistTag.E6.perm e6Fix = e6Fix := by decide

variable [Finite K] (σ : K →+* K)

theorem four_le_pRank_commutator_twistFixed_E6
    {p : ℕ} [hp : Fact p.Prime] [CharP K p]
    (hσ : Function.Surjective σ) (hσ2 : ∀ c, σ (σ c) = c) {u : Kˣ} (hu : (u : K) ^ 2 ≠ 1) :
    4 ≤ pRank p (⊤ : Subgroup (commutator (twistFixed .E6 K σ))) := by
  set τ := TwistTag.E6.tag
  set w : Fin 4 → WeylGroup τ := fun j => (coxeterSystem τ).wordProd (e6FixWords j)
  set α : Fin 4 → Root τ := fun j => w j • simpleRoot τ e6Fix
  have hαv : ∀ j, (α j).1 = e6Vec j := fun j => by
    change (w j • simpleRoot τ e6Fix).1 = _
    rw [coe_smul_root, wordProd_smul]
    rfl
  have hw : ∀ j, weylTwist .E6 (w j) = w j := fun j =>
    weylTwist_wordProd_eq (e6_fixWords_check j)
  set ι : Multiplicative (ZMod p) →* Multiplicative K :=
    (ZMod.castHom (dvd_refl p) K).toAddMonoidHom.toMultiplicative
  have hι : Function.Injective ι := (ZMod.castHom_injective K).comp Multiplicative.toAdd.injective
    |> fun h => Multiplicative.ofAdd.injective.comp h
  set ϕ : Fin 4 → Multiplicative (ZMod p) →* adjointGroup τ K := fun j =>
    ((MulAut.conj (nrep τ K (w j))).toMonoidHom.comp (rootHom (simpleRoot τ e6Fix))).comp ι
  have hϕX : ∀ j, (ϕ j).range ≤ (rootOperatorFamily τ).rootSubgroup K (α j) := by
    rintro j _ ⟨c, rfl⟩
    exact nrep_conj_mem_X (w j) ((rootOperatorFamily τ).eltElement_mem_rootSubgroup _ _)
  have hcomm : Pairwise fun i j => ∀ x y : Multiplicative (ZMod p), Commute (ϕ i x) (ϕ j y) := by
    intro i j hij x y
    have hc : pairCheck τ (α i).1 (α j).1 = true := by
      rw [hαv, hαv]
      exact e6_pair_check i j hij
    exact commute_of_mem_X_of_pairCheck hc (hϕX i ⟨x, rfl⟩) (hϕX j ⟨y, rfl⟩)
  have hind : iSupIndep fun j => (ϕ j).range := by
    refine (iSupIndep_X_of_separated (K := K) α (fun j => ?_)
      (fun j => (coxeterSystem τ).wordProd (e6SepWords j)) (fun j => ?_)
      (fun i j hij => ?_)).mono hϕX
    · have := (e6_pair_check j (j + 1) (by omega)); rw [← hαv] at this
      simp only [pairCheck, Bool.and_eq_true, decide_eq_true_eq] at this
      exact this.1.1.1.1.1
    · rw [wordProd_smul, hαv]; exact (e6_sep_check j).1
    · rw [wordProd_smul, hαv]; exact (e6_sep_check i).2 j hij
  have hinj : ∀ j, Function.Injective (ϕ j) := fun j =>
    ((MulAut.conj _).injective.comp (rootHom_injective _)).comp hι
  set Ψ := MonoidHom.noncommPiCoprod ϕ hcomm
  have hΨ : Function.Injective Ψ := MonoidHom.injective_noncommPiCoprod_of_iSupIndep _ hind hinj
  have hU : ∀ x ∈ (nativeData τ K).U, twistC .E6 K σ x = x → x ∈ twistDerived .E6 K σ :=
    e6_U_le_twistDerived hσ hσ2 hu
  have hmem : ∀ j c, ϕ j c ∈ twistDerived .E6 K σ := by
    intro j c
    refine hU _ ?_ ?_
    · exact RootGroupData.X_le_U (D := nativeData τ K) (by
        change 0 < height (α j).1
        rw [hαv]
        have := e6_pair_check j (j + 1) (by omega)
        simp only [pairCheck, Bool.and_eq_true, decide_eq_true_eq] at this
        exact this.1.1.1.1.1) (hϕX j ⟨c, rfl⟩)
    · change twistC .E6 K σ (nrep τ K (w j) * (rootOperatorFamily τ).eltElement
        (simpleRoot τ e6Fix) (ZMod.castHom (dvd_refl p) K (Multiplicative.toAdd c)) *
        (nrep τ K (w j))⁻¹) = nrep τ K (w j) * (rootOperatorFamily τ).eltElement
        (simpleRoot τ e6Fix) (ZMod.castHom (dvd_refl p) K (Multiplicative.toAdd c)) *
        (nrep τ K (w j))⁻¹
      rw [eltElement_simpleRoot, map_mul, map_mul, map_inv, twistC_nrep, hw, twistC_xElement,
        e6Fix_perm, ringHom_zmod_cast]
  have hrange : Ψ.range ≤ twistDerived .E6 K σ := by
    rw [MonoidHom.noncommPiCoprod_range]
    exact iSup_le fun j => by rintro _ ⟨c, rfl⟩; exact hmem j c
  exact le_pRank_of_commutator hΨ hrange (fun a b => mul_comm a b) (fun a => funext fun j => by
    change Multiplicative.ofAdd (p • Multiplicative.toAdd (a j)) = 1
    rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    rfl) (by
    rw [Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      show Nat.card (Multiplicative (ZMod p)) = p from by
        rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]])

end E6

section D4

abbrev d4Vec : Fin 4 → Fin TwistTag.D4.tag.rank → ℤ :=
  ![([2] : List (Fin 4)).foldr (reflect _) (Pi.single (0 : Fin 4) 1),
    ([2] : List (Fin 4)).foldr (reflect _) (Pi.single (1 : Fin 4) 1),
    ([2] : List (Fin 4)).foldr (reflect _) (Pi.single (3 : Fin 4) 1),
    Pi.single (2 : Fin 4) 1]

@[expose] def d4SepWords : Fin 4 → List (Fin TwistTag.D4.tag.rank) :=
  ![([2, 0] : List (Fin 4)), ([2, 1] : List (Fin 4)), ([2, 3] : List (Fin 4)),
    ([2] : List (Fin 4))]

theorem d4_pair_check : ∀ i j : Fin 4, i ≠ j → pairCheck _ (d4Vec i) (d4Vec j) = true := by
  decide +kernel

theorem d4_sep_check : ∀ i : Fin 4,
    height ((d4SepWords i).foldr (reflect TwistTag.D4.tag) (d4Vec i)) < 0 ∧
      ∀ j, i ≠ j → 0 < height ((d4SepWords i).foldr (reflect TwistTag.D4.tag) (d4Vec j)) := by
  decide +kernel

theorem d4_s2_fixed : ∀ k : Fin TwistTag.D4.tag.rank,
    (([2] : List (Fin 4)).map TwistTag.D4.perm).foldr (reflect TwistTag.D4.tag) (Pi.single k 1) =
      ([2] : List (Fin 4)).foldr (reflect TwistTag.D4.tag) (Pi.single k 1) := by
  decide +kernel


abbrev d4i0 : Fin TwistTag.D4.tag.rank := (0 : Fin 4)
abbrev d4i1 : Fin TwistTag.D4.tag.rank := (1 : Fin 4)
abbrev d4i2 : Fin TwistTag.D4.tag.rank := (2 : Fin 4)
abbrev d4i3 : Fin TwistTag.D4.tag.rank := (3 : Fin 4)

@[expose] def d4S2Word : List (Fin TwistTag.D4.tag.rank) := ([2] : List (Fin 4))

theorem d4_perm_0 : TwistTag.D4.perm d4i0 = d4i1 := by decide
theorem d4_perm_1 : TwistTag.D4.perm d4i1 = d4i3 := by decide
theorem d4_perm_3 : TwistTag.D4.perm d4i3 = d4i0 := by decide
theorem d4_perm_2 : TwistTag.D4.perm d4i2 = d4i2 := by decide

variable [Finite K] (σ : K →+* K)

theorem le_pRank_commutator_twistFixed_D4
    {p f : ℕ} [hp : Fact p.Prime] [CharP K p]
    (hK : Nat.card K = p ^ f) (hσ : Function.Surjective σ) (hσ3 : ∀ c, σ (σ (σ c)) = c)
    {u : Kˣ} (hu : (u : K) ^ 2 ≠ 1) :
    f + 1 ≤ pRank p (⊤ : Subgroup (commutator (twistFixed .D4 K σ))) := by
  set τ := TwistTag.D4.tag
  set s₂ : WeylGroup τ := (coxeterSystem τ).wordProd d4S2Word
  set n := nrep τ K s₂
  have hs₂ : weylTwist .D4 s₂ = s₂ := weylTwist_wordProd_eq (ω := d4S2Word) d4_s2_fixed
  set α : Fin 4 → Root τ := ![s₂ • simpleRoot τ d4i0, s₂ • simpleRoot τ d4i1,
    s₂ • simpleRoot τ d4i3, simpleRoot τ d4i2]
  have hαv : ∀ j, (α j).1 = d4Vec j := by
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
  have hpc : ∀ i j, i ≠ j → pairCheck τ (α i).1 (α j).1 = true := fun i j hij => by
    rw [hαv, hαv]; exact d4_pair_check i j hij
  have hposα : ∀ j, 0 < height (α j).1 := fun j => by
    have := hpc j (j + 1) (by omega)
    simp only [pairCheck, Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1.1.1.1.1
  have hind : iSupIndep fun j => (nativeRootSubgroups τ K).X (α j) :=
    iSupIndep_X_of_separated (K := K) α hposα
      (fun j => (coxeterSystem τ).wordProd (d4SepWords j))
      (fun j => by rw [wordProd_smul, hαv]; exact (d4_sep_check j).1)
      (fun i j hij => by rw [wordProd_smul, hαv]; exact (d4_sep_check i).2 j hij)
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
  set ι : Multiplicative (ZMod p) →* Multiplicative K :=
    (ZMod.castHom (dvd_refl p) K).toAddMonoidHom.toMultiplicative
  have hι : Function.Injective ι := fun a b h =>
    Multiplicative.toAdd.injective (ZMod.castHom_injective K (Multiplicative.ofAdd.injective h))
  set X2 : Multiplicative (ZMod p) →* adjointGroup τ K :=
    (rootHom (simpleRoot τ d4i2)).comp ι
  have hZ : ∀ c : Multiplicative K, Z c = n * xElement d4i0 (Multiplicative.toAdd c) * n⁻¹ *
      (n * xElement d4i1 (σ (Multiplicative.toAdd c)) * n⁻¹) *
      (n * xElement d4i3 (σ (σ (Multiplicative.toAdd c))) * n⁻¹) := fun c => by
    change n * y (Multiplicative.toAdd c) * n⁻¹ = _
    simp only [y]
    group
  have hX2 : ∀ c' : Multiplicative (ZMod p), X2 c' = xElement (τ := τ) d4i2
      (ZMod.castHom (dvd_refl p) K (Multiplicative.toAdd c')) := fun c' =>
    eltElement_simpleRoot _ _
  have hZX2 : ∀ c c', Commute (Z c) (X2 c') := by
    intro c c'
    rw [hZ, hX2]
    have h3 := hx2 (ZMod.castHom (dvd_refl p) K (Multiplicative.toAdd c'))
    exact ((hcX 0 3 (by decide) _ (hx0 _) _ h3).mul_left
      (hcX 1 3 (by decide) _ (hx1 _) _ h3)).mul_left (hcX 2 3 (by decide) _ (hx3 _) _ h3)
  set Ψ : Multiplicative K × Multiplicative (ZMod p) →* adjointGroup τ K :=
    Z.noncommCoprod X2 hZX2
  have hΨ : Function.Injective Ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨c, c'⟩ h
    rw [MonoidHom.mem_ker, MonoidHom.noncommCoprod_apply, hZ, hX2] at h
    have h4 := eq_one_of_prod_four (A := fun j => (nativeRootSubgroups τ K).X (α j)) hind
      (a := ![n * xElement d4i0 (Multiplicative.toAdd c) * n⁻¹,
        n * xElement d4i1 (σ (Multiplicative.toAdd c)) * n⁻¹,
        n * xElement d4i3 (σ (σ (Multiplicative.toAdd c))) * n⁻¹,
        xElement (τ := τ) d4i2 (ZMod.castHom (dvd_refl p) K (Multiplicative.toAdd c'))])
      (fun j => by
        match j with
        | 0 => exact hx0 _
        | 1 => exact hx1 _
        | 2 => exact hx3 _
        | 3 => exact hx2 _) h
    have ha0 : n * xElement d4i0 (Multiplicative.toAdd c) * n⁻¹ = 1 := h4 0
    have ha3 : xElement (τ := τ) d4i2
        (ZMod.castHom (dvd_refl p) K (Multiplicative.toAdd c')) = 1 := h4 3
    rw [mul_inv_eq_one, mul_eq_left] at ha0
    have hc : Multiplicative.toAdd c = 0 :=
      xElement_injective _ (ha0.trans (xElement_zero _).symm)
    have hc' : ZMod.castHom (dvd_refl p) K (Multiplicative.toAdd c') = 0 :=
      xElement_injective _ (ha3.trans (xElement_zero _).symm)
    rw [Subgroup.mem_bot, Prod.mk_eq_one]
    exact ⟨hc, Multiplicative.toAdd.injective ((ZMod.castHom_injective K)
      (hc'.trans (map_zero _).symm))⟩
  have hU : ∀ x ∈ (nativeData τ K).U, twistC .D4 K σ x = x → x ∈ twistDerived .D4 K σ :=
    d4_U_le_twistDerived hσ hσ3 hu
  have hUα : ∀ j, (nativeRootSubgroups τ K).X (α j) ≤ (nativeData τ K).U := fun j =>
    RootGroupData.X_le_U (D := nativeData τ K) (hposα j)
  have hrange : Ψ.range ≤ twistDerived .D4 K σ := by
    rintro _ ⟨⟨c, c'⟩, rfl⟩
    rw [MonoidHom.noncommCoprod_apply, hZ, hX2]
    refine hU _ ?_ ?_
    · exact mul_mem (mul_mem (mul_mem (hUα 0 (hx0 _)) (hUα 1 (hx1 _))) (hUα 2 (hx3 _)))
        (hUα 3 (hx2 _))
    · have hn : twistC .D4 K σ n = n := by rw [twistC_nrep, hs₂]
      rw [← hZ, ← hX2]
      change twistC .D4 K σ (n * y (Multiplicative.toAdd c) * n⁻¹ * X2 c') =
        n * y (Multiplicative.toAdd c) * n⁻¹ * X2 c'
      rw [hX2, map_mul, map_mul, map_mul, map_inv, hn, hyF, twistC_xElement, d4_perm_2,
        ringHom_zmod_cast]
  have := le_pRank_of_commutator hΨ hrange (fun a b => mul_comm a b) (fun a => Prod.ext (by
      change Multiplicative.ofAdd (p • Multiplicative.toAdd a.1) = 1
      rw [nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
      rfl) (by
      change Multiplicative.ofAdd (p • Multiplicative.toAdd a.2) = 1
      rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
      rfl)) (k := f + 1) (by
    rw [Nat.card_prod,
      show Nat.card (Multiplicative K) = Nat.card K from Nat.card_congr Multiplicative.toAdd, hK,
      show Nat.card (Multiplicative (ZMod p)) = p from by
        rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod], pow_succ])
  exact this

end D4

end CFSG.LieType.Chevalley
