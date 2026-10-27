module

public import CFSG.LieType.Ree.ReePerfect
public import CFSG.LieType.Chevalley.G2Rank

public section

namespace CFSG.LieType.Ree

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open CFSG.SectionRank ReeTag

namespace ReeTag

variable (t : ReeTag)

theorem perm_mem_longSet_of_not_mem (i : Fin t.tag.rank) (hi : i ∉ t.longSet) :
    t.perm i ∈ t.longSet := by
  revert i
  cases t <;> decide

theorem relationExponent_mul_perm
    (a : ℕ) (i : Fin t.tag.rank) :
    t.relationExponent a i * t.relationExponent a (t.perm i) = t.prime ^ (2 * a + 1) := by
  by_cases hi : i ∈ t.longSet
  · have h := (t.perm_long i hi).1
    simp only [relationExponent, hi, h, ↓reduceIte]
    rw [← pow_add]
    congr 1
    ring
  · have h := t.perm_mem_longSet_of_not_mem i hi
    simp only [relationExponent, hi, h, ↓reduceIte]
    rw [← pow_add]
    congr 1
    ring

variable {K : Type} [Field K] [Finite K] [CharP K t.prime] (a : ℕ)

theorem reeAut_reeAut
    (hK : Nat.card K = t.prime ^ (2 * a + 1)) (g : adjointGroup t.tag K) :
    t.reeAut K a (t.reeAut K a g) = g := by
  have hpow : ∀ c : K, c ^ t.prime ^ (2 * a + 1) = c := fun c => by
    have := Fintype.ofFinite K
    rw [← hK, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card c
  have h : (t.reeAut K a).toMonoidHom.comp (t.reeAut K a).toMonoidHom = MonoidHom.id _ := by
    refine adjointGroup_hom_ext (fun i c => ?_) (fun i c => ?_)
    · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, reeAut_xElement, perm_perm,
        MonoidHom.id_apply]
      rw [← pow_mul, relationExponent_mul_perm, hpow]
    · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, reeAut_yElement, perm_perm,
        MonoidHom.id_apply]
      rw [← pow_mul, relationExponent_mul_perm, hpow]
  exact DFunLike.congr_fun h g

end ReeTag

section G2

noncomputable abbrev sr₁
    : Root Tag.G2 := g2Root [0, 1, 0, 1] 1
noncomputable abbrev sr₂
    : Root Tag.G2 := g2Root [1, 0, 1] 0
noncomputable abbrev sr₃
    : Root Tag.G2 := g2Root [0, 1] 1
noncomputable abbrev sr₄
    : Root Tag.G2 := g2Root [1] 0

theorem sr₁_val :
    sr₁.1 = g2Vec [0, 1, 0, 1] 1 := val_inv_smul_simpleRoot _ _
theorem sr₂_val :
    sr₂.1 = g2Vec [1, 0, 1] 0 := val_inv_smul_simpleRoot _ _
theorem sr₃_val :
    sr₃.1 = g2Vec [0, 1] 1 := val_inv_smul_simpleRoot _ _
theorem sr₄_val :
    sr₄.1 = g2Vec [1] 0 := val_inv_smul_simpleRoot _ _

theorem smallRee_pairChecks :
    pairCheck .G2 (g2Vec [0, 1, 0, 1] 1) (g2Vec [1, 0, 1] 0) = true ∧
      pairCheck .G2 (g2Vec [0, 1, 0, 1] 1) (g2Vec [1] 0) = true ∧
      pairCheck .G2 (g2Vec [1, 0, 1] 0) (g2Vec [0, 1] 1) = true ∧
      pairCheck .G2 (g2Vec [1, 0, 1] 0) (g2Vec [1] 0) = true ∧
      pairCheck .G2 (g2Vec [0, 1] 1) (g2Vec [1] 0) = true := by
  decide +kernel

theorem smallRee_dual :
    List.ofFn (ReeTag.G2.dualRoot (g2Vec [0, 1, 0, 1] 1)) = List.ofFn (g2Vec [1] 0) ∧
      List.ofFn (ReeTag.G2.dualRoot (g2Vec [0, 1] 1)) = List.ofFn (g2Vec [1, 0, 1] 0) := by
  decide +kernel

theorem smallRee_certVals :
    List.ofFn (Tag.G2.rootCertificate.root 4) = List.ofFn (g2Vec [0, 1, 0, 1] 1) ∧
      List.ofFn (Tag.G2.rootCertificate.root 8) = List.ofFn (g2Vec [0, 1] 1) ∧
      List.ofFn (Tag.G2.rootCertificate.root 7) = List.ofFn (g2Vec [1, 0, 1] 0) := by
  decide +kernel

theorem smallRee_repCheck : RootOps.repCheck .G2 4 8 [(1, 1, 7, 3)] = true := by decide +kernel

theorem dualRootOf_sr₁ :
    ReeTag.G2.dualRootOf sr₁ = sr₄ := Subtype.ext (by
  change ReeTag.G2.dualRoot sr₁.1 = sr₄.1
  rw [sr₁_val, sr₄_val]
  exact List.ofFn_injective smallRee_dual.1)

theorem dualRootOf_sr₃ :
    ReeTag.G2.dualRootOf sr₃ = sr₂ := Subtype.ext (by
  change ReeTag.G2.dualRoot sr₃.1 = sr₂.1
  rw [sr₃_val, sr₂_val]
  exact List.ofFn_injective smallRee_dual.2)

variable {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem commute_sr₁_sr₃
    [CharP K 3] {x y : adjointGroup .G2 K}
    (hx : x ∈ (rootOperatorFamily .G2).rootSubgroup K sr₁)
    (hy : y ∈ (rootOperatorFamily .G2).rootSubgroup K sr₃) : Commute x y := by
  obtain ⟨c, rfl⟩ := (rootOperatorFamily _).mem_rootSubgroup.1 hx
  obtain ⟨d, rfl⟩ := (rootOperatorFamily _).mem_rootSubgroup.1 hy
  have h := commutator_eltElement_of_repCheck (τ := .G2) (K := K) RootOps.g2_allValid
    smallRee_repCheck (by decide) (α := sr₁) (β := sr₃)
    (RootOps.rootPos_eq (by decide) (by
      rw [sr₁_val]; exact List.ofFn_injective smallRee_certVals.1))
    (RootOps.rootPos_eq (by decide) (by
      rw [sr₃_val]; exact List.ofFn_injective smallRee_certVals.2.1)) c d
  have h3 : ((3 : ℤ) : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3
  rw [h3, zero_mul, zero_mul, RootOperatorFamily.eltElement_zero] at h
  calc _ = (rootOperatorFamily .G2).eltElement sr₁ c * (rootOperatorFamily .G2).eltElement sr₃ d *
        ((rootOperatorFamily .G2).eltElement sr₁ c)⁻¹ *
        ((rootOperatorFamily .G2).eltElement sr₃ d)⁻¹ *
        ((rootOperatorFamily .G2).eltElement sr₃ d * (rootOperatorFamily .G2).eltElement sr₁ c) :=
        by group
    _ = _ := by rw [h, one_mul]

theorem le_pRank_of_reeDerived
    {t : ReeTag} [CharP K t.prime] {a : ℕ} {A : Type*} [Group A]
    {Ψ : A →* adjointGroup t.tag K} (hΨ : Function.Injective Ψ)
    (hrange : Ψ.range ≤ reeDerived t K a) {p k : ℕ} [hp : Fact p.Prime]
    (hcomm : ∀ x y : A, x * y = y * x) (hpow : ∀ x : A, x ^ p = 1) (hA : Nat.card A = p ^ k) :
    k ≤ pRank p (⊤ : Subgroup (commutator (reeFixed t K a))) := by
  have hΓ : ∀ x, Ψ x ∈ reeFixed t K a := fun x => Subgroup.map_subtype_le _ (hrange ⟨x, rfl⟩)
  have hΓ' : ∀ x, Ψ.codRestrict _ hΓ x ∈ commutator (reeFixed t K a) := fun x => by
    obtain ⟨h, hh, he⟩ := hrange ⟨x, rfl⟩
    have : Ψ.codRestrict _ hΓ x = h := Subtype.ext he.symm
    rw [this]
    exact hh
  refine le_pRank_of_injective hp.out.one_lt hcomm hpow hA
    ((Ψ.codRestrict _ hΓ).codRestrict _ hΓ') (fun x y h => hΨ ?_) le_top
  exact congrArg (fun z : commutator (reeFixed t K a) =>
    ((z : reeFixed t K a) : adjointGroup t.tag K)) h

theorem two_mul_le_pRank_commutator_reeFixed_G2
    [CharP K ReeTag.G2.prime] {a : ℕ} (ha : 1 ≤ a)
    (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    2 * (2 * a + 1) ≤ pRank 3 (⊤ : Subgroup (commutator (reeFixed .G2 K a))) := by
  have : CharP K 3 := ‹CharP K ReeTag.G2.prime›
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let F : adjointGroup Tag.G2 K ≃* adjointGroup Tag.G2 K := ReeTag.G2.reeAut K a
  have hFF : ∀ g, F (F g) = g := ReeTag.G2.reeAut_reeAut a hK
  obtain ⟨c12, c14, c23, c24, c34⟩ := smallRee_pairChecks
  rw [← sr₁_val, ← sr₂_val] at c12
  rw [← sr₁_val, ← sr₄_val] at c14
  rw [← sr₂_val, ← sr₃_val] at c23
  rw [← sr₂_val, ← sr₄_val] at c24
  rw [← sr₃_val, ← sr₄_val] at c34
  let X := fun r : Root Tag.G2 => (rootOperatorFamily Tag.G2).rootSubgroup K r
  have hC12 : ∀ x ∈ X sr₁, ∀ y ∈ X sr₂, Commute x y := fun x hx y hy =>
    commute_of_mem_X_of_pairCheck c12 hx hy
  have hC14 : ∀ x ∈ X sr₁, ∀ y ∈ X sr₄, Commute x y := fun x hx y hy =>
    commute_of_mem_X_of_pairCheck c14 hx hy
  have hC23 : ∀ x ∈ X sr₂, ∀ y ∈ X sr₃, Commute x y := fun x hx y hy =>
    commute_of_mem_X_of_pairCheck c23 hx hy
  have hC24 : ∀ x ∈ X sr₂, ∀ y ∈ X sr₄, Commute x y := fun x hx y hy =>
    commute_of_mem_X_of_pairCheck c24 hx hy
  have hC34 : ∀ x ∈ X sr₃, ∀ y ∈ X sr₄, Commute x y := fun x hx y hy =>
    commute_of_mem_X_of_pairCheck c34 hx hy
  have hC13 : ∀ x ∈ X sr₁, ∀ y ∈ X sr₃, Commute x y := fun x hx y hy =>
    commute_sr₁_sr₃ hx hy
  have hm : ∀ (r : Root Tag.G2) (c : Multiplicative K), rootHom r c ∈ X r := fun _ _ =>
    (rootOperatorFamily _).eltElement_mem_rootSubgroup _ _
  have hF₁ : ∀ c : Multiplicative K, F (rootHom sr₁ c) ∈ X sr₄ := fun c => by
    have := ReeTag.reeAut_mem_X (t := .G2) a (hm sr₁ c)
    rwa [dualRootOf_sr₁] at this
  have hF₃ : ∀ c : Multiplicative K, F (rootHom sr₃ c) ∈ X sr₂ := fun c => by
    have := ReeTag.reeAut_mem_X (t := .G2) a (hm sr₃ c)
    rwa [dualRootOf_sr₃] at this
  let ψ₃ : Multiplicative K × Multiplicative K →* adjointGroup Tag.G2 K :=
    (rootHom sr₃).noncommCoprod (F.toMonoidHom.comp (rootHom sr₃)) fun x y =>
      (hC23 _ (hF₃ y) _ (hm sr₃ x)).symm
  let ψ₂ : Multiplicative K × (Multiplicative K × Multiplicative K) →* adjointGroup Tag.G2 K :=
    (F.toMonoidHom.comp (rootHom sr₁)).noncommCoprod ψ₃ fun x yz => by
      change Commute (F (rootHom sr₁ x)) (rootHom sr₃ yz.1 * F (rootHom sr₃ yz.2))
      exact (hC34 _ (hm sr₃ yz.1) _ (hF₁ x)).symm.mul_right (hC24 _ (hF₃ yz.2) _ (hF₁ x)).symm
  let Φ : Multiplicative K × (Multiplicative K × (Multiplicative K × Multiplicative K)) →*
      adjointGroup Tag.G2 K :=
    (rootHom sr₁).noncommCoprod ψ₂ fun x yzw => by
      change Commute (rootHom sr₁ x)
        (F (rootHom sr₁ yzw.1) * (rootHom sr₃ yzw.2.1 * F (rootHom sr₃ yzw.2.2)))
      exact (hC14 _ (hm sr₁ x) _ (hF₁ _)).mul_right
        ((hC13 _ (hm sr₁ x) _ (hm sr₃ _)).mul_right (hC12 _ (hm sr₁ x) _ (hF₃ _)))
  let Ψ : Multiplicative K × Multiplicative K →* adjointGroup Tag.G2 K :=
    Φ.comp ((MonoidHom.fst _ _).prod ((MonoidHom.fst _ _).prod
      ((MonoidHom.snd _ _).prod (MonoidHom.snd _ _))))
  have hΨ : ∀ c d, Ψ (c, d) =
      rootHom sr₁ c * (F (rootHom sr₁ c) * (rootHom sr₃ d * F (rootHom sr₃ d))) :=
    fun _ _ => rfl
  have hinj : Function.Injective Ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨c, d⟩ h
    rw [MonoidHom.mem_ker, hΨ] at h
    have hcomm : Commute (rootHom sr₁ c)
        (F (rootHom sr₁ c) * (rootHom sr₃ d * F (rootHom sr₃ d))) :=
      (hC14 _ (hm sr₁ c) _ (hF₁ c)).mul_right
        ((hC13 _ (hm sr₁ c) _ (hm sr₃ d)).mul_right (hC12 _ (hm sr₁ c) _ (hF₃ d)))
    have hy := eq_of_reverse_prod_eq (K := K) g2LongWord isReduced_G2_alternating
      [1, rootHom sr₁ c, F (rootHom sr₃ d), rootHom sr₃ d, F (rootHom sr₁ c), 1]
      [1, 1, 1, 1, 1, 1]
      (by
        rw [wordRoots_g2LongWord]
        exact .cons (one_mem _) (.cons (hm sr₁ c) (.cons (hF₃ d) (.cons (hm sr₃ d)
          (.cons (hF₁ c) (.cons (one_mem _) .nil))))))
      (by
        rw [wordRoots_g2LongWord]
        exact .cons (one_mem _) (.cons (one_mem _) (.cons (one_mem _) (.cons (one_mem _)
          (.cons (one_mem _) (.cons (one_mem _) .nil))))))
      (by
        have e : [1, rootHom sr₁ c, F (rootHom sr₃ d), rootHom sr₃ d, F (rootHom sr₁ c),
            (1 : adjointGroup Tag.G2 K)].reverse.prod =
            F (rootHom sr₁ c) * (rootHom sr₃ d * F (rootHom sr₃ d)) * rootHom sr₁ c := by
          simp [mul_assoc]
        rw [e, ← hcomm.eq, h]
        simp)
    simp only [List.cons.injEq] at hy
    obtain ⟨-, hc, -, hd, -, -⟩ := hy
    rw [Subgroup.mem_bot, Prod.mk_eq_one]
    exact ⟨rootHom_injective _ (hc.trans (map_one _).symm),
      rootHom_injective _ (hd.trans (map_one _).symm)⟩
  have hXU : ∀ r ∈ wordRoots g2LongWord, ∀ x ∈ X r, x ∈ (nativeData Tag.G2 K).U :=
    fun r hr _ hx => RootGroupData.X_le_U (D := nativeData Tag.G2 K)
      (wordRoots_spec g2LongWord isReduced_G2_alternating r hr).1 hx
  have hU : ∀ c d, Ψ (c, d) ∈ (nativeData Tag.G2 K).U := fun c d => by
    rw [hΨ]
    refine mul_mem (hXU sr₁ ?_ _ (hm sr₁ c)) (mul_mem (hXU sr₄ ?_ _ (hF₁ c))
      (mul_mem (hXU sr₃ ?_ _ (hm sr₃ d)) (hXU sr₂ ?_ _ (hF₃ d)))) <;>
    · rw [wordRoots_g2LongWord]; simp
  have hfix : ∀ c d, Ψ (c, d) ∈ reeFixed .G2 K a := fun c d => by
    change F (Ψ (c, d)) = Ψ (c, d)
    rw [hΨ]
    rw [map_mul, map_mul, map_mul, hFF, hFF, ← mul_assoc, ← (hC14 _ (hm sr₁ c) _ (hF₁ c)).eq,
      mul_assoc, (hC23 _ (hF₃ d) _ (hm sr₃ d)).eq]
  refine le_pRank_of_reeDerived (t := .G2) hinj ?_ (fun x y => mul_comm x y) (fun x => ?_) ?_
  · rintro _ ⟨⟨c, d⟩, rfl⟩
    exact reeFixed_U_le_derived .G2 K a ha hK _ (hU c d) (hfix c d)
  · have hx : ∀ z : Multiplicative K, z ^ 3 = 1 := fun z => by
      change Multiplicative.ofAdd (3 • Multiplicative.toAdd z) = 1
      rw [nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
      rfl
    exact Prod.ext (hx _) (hx _)
  · rw [Nat.card_prod,
      show Nat.card (Multiplicative K) = Nat.card K from Nat.card_congr Multiplicative.toAdd, hK]
    ring

end G2

end CFSG.LieType.Ree
