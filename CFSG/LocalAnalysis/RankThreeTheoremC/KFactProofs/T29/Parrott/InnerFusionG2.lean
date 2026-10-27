module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.InnerFusionBasic
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie7Proof
public import CFSG.RankThree.PartTwo.Sec11.Item1118Res3ProofSL2

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.InnerFusion

open CFSG.Open Subgroup TauCeti CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.LieType.HighestRoot
open CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof (g2ShortSL2 g2LongSL2 g2Short_commute_g2Long)


section SL2

variable (K : Type) [Field K]

@[expose] def sl2Three : SL2 K := ⟨!![0, -1; 1, -1], by simp [Matrix.det_fin_two]⟩

@[expose] def sl2Upper : SL2 K := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩

variable {K}

theorem sl2Three_pow_three : sl2Three K ^ 3 = 1 := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_pow]
  fin_cases i <;> fin_cases j <;>
    simp [sl2Three, pow_succ, Matrix.mul_apply, Fin.sum_univ_two]

theorem sl2Three_ne_one : sl2Three K ≠ 1 := by
  intro h
  have h00 := congrArg (fun A : SL2 K => (A : Matrix (Fin 2) (Fin 2) K) 0 0) h
  simp [sl2Three] at h00

theorem sl2Three_mul_sl2Upper_ne : sl2Three K * sl2Upper K ≠ sl2Upper K * sl2Three K := by
  intro h
  have h00 := congrArg (fun A : SL2 K => (A : Matrix (Fin 2) (Fin 2) K) 0 0) h
  simp only [Matrix.SpecialLinearGroup.coe_mul] at h00
  simp [sl2Three, sl2Upper, Matrix.mul_apply, Fin.sum_univ_two] at h00

theorem map_sl2Three (σ : K →+* K) : Matrix.SpecialLinearGroup.map σ (sl2Three K) = sl2Three K := by
  ext i j
  rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
  fin_cases i <;> fin_cases j <;> simp [sl2Three]

theorem three_ne_zero_of_ringChar [Finite K] (h : ringChar K ≠ 3) : (3 : K) ≠ 0 := by
  intro h0
  have : CharP K (ringChar K) := ringChar.charP K
  have hp : (ringChar K).Prime := by
    rcases CharP.char_is_prime_or_zero K (ringChar K) with hp | hp
    · exact hp
    · exact absurd hp (CharP.char_ne_zero_of_finite K (ringChar K))
  have hd : ringChar K ∣ 3 := (CharP.cast_eq_zero_iff K (ringChar K) 3).1 (by exact_mod_cast h0)
  exact h ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hd)

end SL2

section Root


variable {K : Type} [Field K]

theorem rootSL2_mem_adjointGroup_G2 {β : Fin Tag.G2.rank → ℤ} (hβ : IsRoot .G2 β) (A : SL2 K) :
    rootSL2 .G2 K β A ∈ adjointGroup .G2 K := by
  have h : rootSL2 .G2 K β A ∈ (rootSL2 .G2 K β).range := ⟨A, rfl⟩
  rw [range_rootSL2_of_isRoot hβ] at h
  exact sup_le (rootSubgroup_le_adjointGroup β) (rootSubgroup_le_adjointGroup (-β)) h

@[expose] noncomputable def g2RootElt {β : Fin Tag.G2.rank → ℤ} (hβ : IsRoot .G2 β) (A : SL2 K) :
    adjointGroup .G2 K :=
  ⟨rootSL2 .G2 K β A, rootSL2_mem_adjointGroup_G2 hβ A⟩

theorem g2RootElt_mul {β : Fin Tag.G2.rank → ℤ} (hβ : IsRoot .G2 β) (A B : SL2 K) :
    g2RootElt hβ (A * B) = g2RootElt hβ A * g2RootElt hβ B :=
  Subtype.ext (map_mul _ A B)

theorem g2RootElt_inv {β : Fin Tag.G2.rank → ℤ} (hβ : IsRoot .G2 β) (A : SL2 K) :
    g2RootElt hβ A⁻¹ = (g2RootElt hβ A)⁻¹ :=
  Subtype.ext (map_inv _ A)

theorem g2RootElt_pow {β : Fin Tag.G2.rank → ℤ} (hβ : IsRoot .G2 β) (A : SL2 K) (n : ℕ) :
    g2RootElt hβ (A ^ n) = g2RootElt hβ A ^ n :=
  Subtype.ext (by rw [Subgroup.coe_pow]; exact map_pow _ A n)

theorem g2RootElt_injective {β : Fin Tag.G2.rank → ℤ} (hβ : IsRoot .G2 β) :
    Function.Injective (g2RootElt (K := K) hβ) := fun A B h =>
  rootSL2_injective_of_field β (congrArg Subtype.val h)

theorem exists_g2RootElt_eq {β : Fin Tag.G2.rank → ℤ} (hβ : IsRoot .G2 β)
    {y : adjointGroup .G2 K}
    (hy : (y : ModGL .G2 K) ∈ rootSubgroup .G2 K β ⊔ rootSubgroup .G2 K (-β)) :
    ∃ B : SL2 K, g2RootElt hβ B = y := by
  rw [← range_rootSL2_of_isRoot hβ] at hy
  obtain ⟨B, hB⟩ := hy
  exact ⟨B, Subtype.ext hB⟩

theorem g2RootElt_mem_short (A : SL2 K) : g2RootElt isRoot_g2δ A ∈ g2ShortSL2 K := by
  show rootSL2 .G2 K g2δ A ∈ rootSubgroup .G2 K g2δ ⊔ rootSubgroup .G2 K (-g2δ)
  rw [← range_rootSL2_of_isRoot isRoot_g2δ]
  exact ⟨A, rfl⟩

theorem g2RootElt_mem_long (A : SL2 K) :
    g2RootElt (isRoot_single .G2 g2l) A ∈ g2LongSL2 K := by
  show rootSL2 .G2 K g2e0 A ∈ rootSubgroup .G2 K g2e0 ⊔ rootSubgroup .G2 K (-g2e0)
  rw [← range_rootSL2_of_isRoot (isRoot_single .G2 g2l)]
  exact ⟨A, rfl⟩

@[expose] noncomputable def g2ShortThree (K : Type) [Field K] : adjointGroup .G2 K :=
  g2RootElt isRoot_g2δ (sl2Three K)

@[expose] noncomputable def g2LongThree (K : Type) [Field K] : adjointGroup .G2 K :=
  g2RootElt (isRoot_single .G2 g2l) (sl2Three K)

@[expose] noncomputable def g2Plane (K : Type) [Field K] : Subgroup (adjointGroup .G2 K) :=
  zpowers (g2ShortThree K) ⊔ zpowers (g2LongThree K)

theorem g2ShortThree_pow_three : g2ShortThree K ^ 3 = 1 := by
  rw [g2ShortThree, ← g2RootElt_pow, sl2Three_pow_three]
  exact Subtype.ext (map_one _)

theorem g2LongThree_pow_three : g2LongThree K ^ 3 = 1 := by
  rw [g2LongThree, ← g2RootElt_pow, sl2Three_pow_three]
  exact Subtype.ext (map_one _)

theorem orderOf_g2ShortThree : orderOf (g2ShortThree K) = 3 := by
  refine orderOf_eq_three g2ShortThree_pow_three fun h => sl2Three_ne_one (K := K) ?_
  apply g2RootElt_injective isRoot_g2δ
  rw [← g2ShortThree, h]
  exact (Subtype.ext (map_one _)).symm

theorem orderOf_g2LongThree : orderOf (g2LongThree K) = 3 := by
  refine orderOf_eq_three g2LongThree_pow_three fun h => sl2Three_ne_one (K := K) ?_
  apply g2RootElt_injective (isRoot_single .G2 g2l)
  rw [← g2LongThree, h]
  exact (Subtype.ext (map_one _)).symm

theorem exists_conj_eq_g2RootElt [Finite K] (h3 : (3 : K) ≠ 0) {β : Fin Tag.G2.rank → ℤ}
    (hβ : IsRoot .G2 β) {y : adjointGroup .G2 K}
    (hy : (y : ModGL .G2 K) ∈ rootSubgroup .G2 K β ⊔ rootSubgroup .G2 K (-β)) (hy3 : y ^ 3 = 1)
    (hy1 : y ≠ 1) : ∃ c : adjointGroup .G2 K, c * y * c⁻¹ = g2RootElt hβ (sl2Three K) := by
  obtain ⟨B, rfl⟩ := exists_g2RootElt_eq hβ hy
  have hB3 : B ^ 3 = 1 := g2RootElt_injective hβ (by
    rw [g2RootElt_pow, hy3]
    exact (Subtype.ext (map_one _)).symm)
  have hB1 : B ≠ 1 := fun h => hy1 (by rw [h]; exact Subtype.ext (map_one _))
  obtain ⟨C, hC⟩ := CFSG.RankThree.PartTwo.Sec11.Item1118Res3Proof.exists_conj_of_pow_three h3 hB3
    hB1 sl2Three_pow_three sl2Three_ne_one
  refine ⟨g2RootElt hβ C, ?_⟩
  rw [← g2RootElt_inv, ← g2RootElt_mul, ← g2RootElt_mul, hC]

end Root

section Plane


variable {K : Type} [Field K]

theorem entrywiseAdjointAut_g2RootElt (σ : K ≃+* K) {β : Fin Tag.G2.rank → ℤ}
    (hβ : IsRoot .G2 β) {A : SL2 K} (hA : Matrix.SpecialLinearGroup.map σ.toRingHom A = A) :
    entrywiseAdjointAut .G2 σ (g2RootElt hβ A) = g2RootElt hβ A := by
  apply Subtype.ext
  rw [coe_entrywiseAdjointAut]
  show Units.map (entrywiseHom σ.toRingHom) (rootSL2 .G2 K β A) = rootSL2 .G2 K β A
  rw [entrywise_rootSL2_of_field, hA]

theorem g2ShortThree_commute : g2ShortThree K * g2LongThree K = g2LongThree K * g2ShortThree K :=
  g2Short_commute_g2Long (g2RootElt_mem_short _) (g2RootElt_mem_long _)

theorem not_mem_short_of_mem_long [Finite K] (h3 : (3 : K) ≠ 0) {y : adjointGroup .G2 K}
    (hyS : y ∈ g2ShortSL2 K) (hyM : y ∈ g2LongSL2 K) (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) : False := by
  obtain ⟨B, rfl⟩ := exists_g2RootElt_eq isRoot_g2δ hyS
  have hB3 : B ^ 3 = 1 := g2RootElt_injective isRoot_g2δ (by
    rw [g2RootElt_pow, hy3]
    exact (Subtype.ext (map_one _)).symm)
  have hB1 : B ≠ 1 := fun h => hy1 (by rw [h]; exact Subtype.ext (map_one _))
  have hcen : ∀ C : SL2 K, C * B = B * C := fun C => g2RootElt_injective isRoot_g2δ (by
    rw [g2RootElt_mul, g2RootElt_mul]
    exact g2Short_commute_g2Long (g2RootElt_mem_short C) hyM)
  obtain ⟨C, hC⟩ := CFSG.RankThree.PartTwo.Sec11.Item1118Res3Proof.exists_conj_of_pow_three h3 hB3
    hB1 sl2Three_pow_three sl2Three_ne_one
  have hBA : B = sl2Three K := by
    rw [← hC, hcen C, mul_inv_cancel_right]
  apply sl2Three_mul_sl2Upper_ne (K := K)
  rw [← hBA]
  exact (hcen (sl2Upper K)).symm

theorem g2LongThree_not_mem [Finite K] (h3 : (3 : K) ≠ 0) :
    g2LongThree K ∉ zpowers (g2ShortThree K) := fun h =>
  not_mem_short_of_mem_long h3 (Subgroup.zpowers_le.2 (g2RootElt_mem_short _) h)
    (g2RootElt_mem_long _) g2LongThree_pow_three (ne_one_of_orderOf_three orderOf_g2LongThree)

theorem isElemAbelian_g2Plane : IsElemAbelian 3 (g2Plane K) :=
  isElemAbelian_sup_zpowers g2ShortThree_pow_three g2LongThree_pow_three g2ShortThree_commute

theorem card_g2Plane [Finite K] (h3 : (3 : K) ≠ 0) : Nat.card (g2Plane K) = 9 := by
  have : Finite (adjointGroup .G2 K) := Subtype.finite
  exact card_sup_zpowers_eq_nine orderOf_g2ShortThree g2LongThree_pow_three (g2LongThree_not_mem h3)
    g2ShortThree_commute

theorem entrywiseAdjointAut_fix_g2Plane (σ : K ≃+* K) :
    ∀ e ∈ g2Plane K, entrywiseAdjointAut .G2 σ e = e :=
  fixed_of_mem_sup_zpowers (entrywiseAdjointAut_g2RootElt σ _ (map_sl2Three _))
    (entrywiseAdjointAut_g2RootElt σ _ (map_sl2Three _))

end Plane

section Conj


variable {K : Type} [Field K]

theorem g2_exists_conj_short_or_long [Finite K] (hK3 : ringChar K ≠ 3) {z : adjointGroup .G2 K}
    (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) :
    ∃ g : adjointGroup .G2 K, g * z * g⁻¹ ∈ g2ShortSL2 K ∨ g * z * g⁻¹ ∈ g2LongSL2 K := by
  by_cases h3 : 3 ∣ Nat.card K + 1
  · obtain ⟨K₂, _, _, hdeg, σ, hσ⟩ :=
      CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding.exists_quadratic_frobenius_all K
    have : Finite K₂ := (CFSG.RankThree.QuadraticSL2.quadratic_frobenius hdeg σ hσ).1
    obtain ⟨M⟩ := CFSG.RankThree.PartTwo.Sec11.KS11Lie7Proof.nonempty_qPlusModel hdeg hσ
    exact CFSG.RankThree.PartTwo.Sec11.KS11Lie7Proof.exists_conj_short_or_long M hdeg hσ h3 hz3
      hz1
  · have hK4 : 4 ≤ Nat.card K := by
      have : Fintype K := Fintype.ofFinite K
      obtain ⟨n, hp, hn⟩ := FiniteField.card K (ringChar K)
      have hK : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
      have h3K : ¬ 3 ∣ Nat.card K := fun h => hK3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three
        hp).1 (Nat.prime_three.dvd_of_dvd_pow (hK ▸ h))).symm
      have h2 : 2 ≤ Nat.card K := by
        rw [hK]
        exact hp.two_le.trans (Nat.le_self_pow n.pos.ne' _)
      omega
    exact CFSG.RankThree.PartTwo.Sec11.KS11Lie7Proof.g2ThreeConjSL2_holds K hK3 hK4 z hz3 hz1

theorem exists_conj_eq_g2Three [Finite K] (hK3 : ringChar K ≠ 3) {x : adjointGroup .G2 K}
    (hx : orderOf x = 3) :
    ∃ g, g * x * g⁻¹ = g2ShortThree K ∨ g * x * g⁻¹ = g2LongThree K := by
  have h3 := three_ne_zero_of_ringChar hK3
  obtain ⟨g, hg⟩ := g2_exists_conj_short_or_long hK3 (pow_three_eq_one_of_orderOf hx)
    (ne_one_of_orderOf_three hx)
  have hy3 : (g * x * g⁻¹) ^ 3 = 1 := by
    rw [← orderOf_conj_eq g x] at hx
    exact pow_three_eq_one_of_orderOf hx
  have hy1 : g * x * g⁻¹ ≠ 1 := by
    rw [← orderOf_conj_eq g x] at hx
    exact ne_one_of_orderOf_three hx
  have hconj : ∀ c : adjointGroup .G2 K, c * (g * x * g⁻¹) * c⁻¹ = (c * g) * x * (c * g)⁻¹ :=
    fun c => by group
  rcases hg with hS | hM
  · obtain ⟨c, hc⟩ := exists_conj_eq_g2RootElt h3 isRoot_g2δ (Subgroup.mem_comap.1 hS) hy3 hy1
    exact ⟨c * g, Or.inl (by rw [← hconj, hc]; rfl)⟩
  · obtain ⟨c, hc⟩ := exists_conj_eq_g2RootElt h3 (isRoot_single .G2 g2l)
      (Subgroup.mem_comap.1 hM) hy3 hy1
    exact ⟨c * g, Or.inr (by rw [← hconj, hc]; rfl)⟩

theorem exists_conj_mem_g2Plane [Finite K] (hK3 : ringChar K ≠ 3) {x : adjointGroup .G2 K}
    (hx : orderOf x = 3) : ∃ g, g * x * g⁻¹ ∈ g2Plane K := by
  obtain ⟨g, hg | hg⟩ := exists_conj_eq_g2Three hK3 hx
  · exact ⟨g, by rw [hg]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)⟩
  · exact ⟨g, by rw [hg]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)⟩

theorem fusesIntoFixedE9_entrywise_G2 [Finite K] (hK3 : ringChar K ≠ 3) (σ : K ≃+* K) :
    FusesIntoFixedE9 (entrywiseAdjointAut .G2 σ) :=
  fusesIntoFixedE9_of_reps isElemAbelian_g2Plane (card_g2Plane (three_ne_zero_of_ringChar hK3))
    (entrywiseAdjointAut_fix_g2Plane σ) fun _ hx => exists_conj_mem_g2Plane hK3 hx

end Conj

section Descent


variable {K : Type} [Field K]

theorem g2_exists_conj_entrywise_of_nf {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f)
    (hNF : ∀ α : MulAut (adjointGroup .G2 K), ∃! gσ : adjointGroup .G2 K × (K ≃+* K),
      ∀ h : adjointGroup .G2 K, (α h : ModGL .G2 K) = (gσ.1 : ModGL .G2 K) *
        Units.map (entrywiseHom gσ.2.toRingHom) (h : ModGL .G2 K) * (gσ.1 : ModGL .G2 K)⁻¹)
    (Θ : MulAut (adjointGroup .G2 K) →* (K ≃+* K))
    (hΘ : ∀ (α : MulAut (adjointGroup .G2 K)) (g : adjointGroup .G2 K) (σ : K ≃+* K),
      (∀ h : adjointGroup .G2 K, (α h : ModGL .G2 K) = (g : ModGL .G2 K) *
        Units.map (entrywiseHom σ.toRingHom) (h : ModGL .G2 K) * (g : ModGL .G2 K)⁻¹) →
      Θ α = σ)
    (hker : Θ.ker = (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)).range)
    (α : MulAut (adjointGroup .G2 K)) (hα3 : α ^ 3 = 1)
    (hαo : α ∉ (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)).range) :
    ∃ (δ : MulAut (adjointGroup .G2 K)) (σ : K ≃+* K),
      δ * α * δ⁻¹ = entrywiseAdjointAut .G2 σ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨x, σ⟩, hxσ, -⟩ := hNF α
  have hΘα : Θ α = σ := hΘ α x σ hxσ
  have hασ : α = MulAut.conj x * entrywiseAdjointAut .G2 σ := by
    refine MulEquiv.ext fun h => Subtype.ext ?_
    rw [hxσ h, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, coe_entrywiseAdjointAut]
  have hσ3 : σ ^ 3 = 1 := by rw [← hΘα, ← map_pow, hα3, map_one]
  have hσ1 : σ ≠ 1 := fun h => hαo (by
    rw [← hker]
    exact (MonoidHom.mem_ker).2 (hΘα.trans h))
  have hα1 : α ≠ 1 := fun h => hαo ⟨1, by rw [map_one, h]⟩
  have hαord : orderOf (MulAut.conj x * entrywiseAdjointAut .G2 σ) = 3 := by
    rw [← hασ]
    exact orderOf_eq_prime hα3 hα1
  obtain ⟨-, δ, hδ⟩ := exists_conj_eq_entrywiseAdjointAut_of_orderOf .G2 hℓ hf K hK
    Nat.prime_three x σ (orderOf_eq_prime hσ3 hσ1) hαord
  exact ⟨δ, σ, by rw [hασ]; exact hδ⟩

theorem g2_exists_conj_entrywise {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f)
    (hf2 : ℓ = 2 → 2 ≤ f) (hK : Nat.card K = ℓ ^ f) (α : MulAut (adjointGroup .G2 K))
    (hα3 : α ^ 3 = 1)
    (hαo : α ∉ (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)).range) :
    ∃ (δ : MulAut (adjointGroup .G2 K)) (σ : K ≃+* K),
      δ * α * δ⁻¹ = entrywiseAdjointAut .G2 σ := by
  by_cases h2 : ℓ = 2
  · subst h2
    obtain ⟨hNF, Θ, hΘ, -, hker, -⟩ :=
      CFSG.ComponentClassification.UnbalancedCatalog.even_G2_exact_automorphism_normal_form
        (hf2 rfl) K hK
    exact g2_exists_conj_entrywise_of_nf Nat.prime_two hf hK hNF Θ hΘ hker α hα3 hαo
  · obtain ⟨hNF, Θ, hΘ, -, hker, -⟩ :=
      odd_F4_and_nonexceptional_G2_automorphism_normal_form hℓ h2 hf K hK .G2
        (Or.inr ⟨rfl, hℓ3⟩)
    exact g2_exists_conj_entrywise_of_nf hℓ hf hK hNF Θ hΘ hker α hα3 hαo

end Descent

section Family


theorem innerFusionE9At_G2 (q : PrimePower) (hv : (LieTypeIndex.G2 q).Valid) (hch : q.p ≠ 3) :
    InnerFusionE9At ⟨.G2 q, hv⟩ := by
  obtain ⟨K, _, _, hK, hKchar, ⟨e⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
    CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 q hv
  have hq3 : 3 ≤ q.card :=
    (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  have hK' : Nat.card K = q.p ^ q.exponent := hK.trans (PrimePower.card_def q)
  have hK3 : ringChar K ≠ 3 := by rw [ringChar.eq K q.p]; exact hch
  have hf2 : q.p = 2 → 2 ≤ q.exponent := fun h2 => by
    by_contra hlt
    have h1 : q.exponent = 1 := by have := q.exponent_pos; omega
    rw [PrimePower.card_def, h1, h2] at hq3
    omega
  refine innerFusionE9At_of_model e fun α hα3 hαo => ?_
  obtain ⟨δ, σ, hδ⟩ := g2_exists_conj_entrywise q.prime_p hch q.exponent_pos hf2 hK' α hα3 hαo
  refine FusesIntoFixedE9.of_conj δ ?_
  rw [hδ]
  exact fusesIntoFixedE9_entrywise_G2 hK3 σ

end Family

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.InnerFusion
