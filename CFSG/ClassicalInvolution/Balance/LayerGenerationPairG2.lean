module

public import CFSG.ClassicalInvolution.Balance.LayerGenerationHybrid
public import CFSG.ClassicalInvolution.Balance.LayerGenerationShortTwistedAssembly
public import CFSG.ClassicalInvolution.Balance.LayerGenerationShortTwistedD4
public import CFSG.LieType.Chevalley.OddG2ToralInvolutionComponents
import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalSpin

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups

section Involution

variable {K : Type} [Field K]

theorem unit_eq_one_or_neg_one_of_sq_eq_one {u : Kˣ} (hu : u ^ 2 = 1) : u = 1 ∨ u = -1 := by
  have h : (u : K) * u = 1 := by rw [← Units.val_mul, ← sq, hu, Units.val_one]
  rcases mul_self_eq_one_iff.1 h with h1 | h1
  · exact Or.inl (Units.ext (by simp [h1]))
  · exact Or.inr (Units.ext (by simp [h1]))

theorem neg_one_eq_HSL : (-1 : SL2 K) = HSL (-1) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [HSL]

end Involution

section Kernels

variable {K : Type} [Field K] [Finite K]

theorem g2_toral_data (hK : Odd (Nat.card K)) {a : Fin Tag.G2.rank → Kˣ}
    (ha : ∀ i, a i = 1 ∨ a i = -1) (hne : a ≠ 1) :
    ∃ α β : Fin Tag.G2.rank → ℤ,
      ((a = ![-1, 1] ∧ α = ![0, 1] ∧ β = ![2, 3]) ∨ (a = ![1, -1] ∧ α = ![1, 0] ∧ β = ![1, 2]) ∨
        (a = ![-1, -1] ∧ α = ![1, 1] ∧ β = ![1, 3])) ∧
      rootCharKernel a = {α, -α, β, -β} ∧
      rootSpan .G2 K (rootCharKernel a) =
        (rootSubgroup .G2 K α ⊔ rootSubgroup .G2 K (-α)) ⊔
          (rootSubgroup .G2 K β ⊔ rootSubgroup .G2 K (-β)) ∧
      ⁅rootSubgroup .G2 K α ⊔ rootSubgroup .G2 K (-α),
        rootSubgroup .G2 K β ⊔ rootSubgroup .G2 K (-β)⁆ = ⊥ ∧
      rootSpan .G2 K (rootCharKernel a) ≤ toralCentralizer .G2 K a ∧
      ((rootSpan .G2 K (rootCharKernel a)).subgroupOf (toralCentralizer .G2 K a)).Normal ∧
      derivedSeries (toralCentralizer .G2 K a ⧸
        (rootSpan .G2 K (rootCharKernel a)).subgroupOf (toralCentralizer .G2 K a)) 2 = ⊥ := by
  obtain ⟨-, -, hcases, hker, -⟩ := odd_G2_toral_involution_fixed_p_components K hK a ha
  have hcase : (a = ![-1, 1] ∨ a = ![1, -1] ∨ a = ![-1, -1]) := by
    rcases hcases with h | h | h | h
    · exact absurd h hne
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  rcases hcase with h | h | h
  · obtain ⟨h1, -, h3, h4, -, -, -, h8, h9, -, h11⟩ := hker ![0, 1] ![2, 3] (Or.inl ⟨h, rfl, rfl⟩)
    exact ⟨_, _, Or.inl ⟨h, rfl, rfl⟩, h1, h3, h4, h8, h9, h11⟩
  · obtain ⟨h1, -, h3, h4, -, -, -, h8, h9, -, h11⟩ :=
      hker ![1, 0] ![1, 2] (Or.inr (Or.inl ⟨h, rfl, rfl⟩))
    exact ⟨_, _, Or.inr (Or.inl ⟨h, rfl, rfl⟩), h1, h3, h4, h8, h9, h11⟩
  · obtain ⟨h1, -, h3, h4, -, -, -, h8, h9, -, h11⟩ :=
      hker ![1, 1] ![1, 3] (Or.inr (Or.inr ⟨h, rfl, rfl⟩))
    exact ⟨_, _, Or.inr (Or.inr ⟨h, rfl, rfl⟩), h1, h3, h4, h8, h9, h11⟩

theorem g2_eq_of_mem_rootCharKernel (hK : Odd (Nat.card K)) {a c : Fin Tag.G2.rank → Kˣ}
    (ha : ∀ i, a i = 1 ∨ a i = -1) (hc : ∀ i, c i = 1 ∨ c i = -1) (hna : a ≠ 1) (hnc : c ≠ 1)
    {γ : Fin Tag.G2.rank → ℤ} (hγa : γ ∈ rootCharKernel a) (hγc : γ ∈ rootCharKernel c) :
    a = c := by
  obtain ⟨α, β, hca, hka, -⟩ := g2_toral_data hK ha hna
  obtain ⟨α', β', hcc, hkc, -⟩ := g2_toral_data hK hc hnc
  rw [hka] at hγa
  rw [hkc] at hγc
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hγa hγc
  rcases hca with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    rcases hcc with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    first
    | rfl
    | (exfalso
       rcases hγa with rfl | rfl | rfl | rfl <;> rcases hγc with h | h | h | h <;>
         first
         | exact absurd (congrFun h (0 : Fin 2)) (by decide)
         | exact absurd (congrFun h (1 : Fin 2)) (by decide))

theorem ringChar_ne_two_of_odd_nat_card (hK : Odd (Nat.card K)) : ringChar K ≠ 2 := fun h => by
  classical
  have : Fintype K := Fintype.ofFinite K
  have h2 := FiniteField.even_card_iff_char_two.1 h
  rw [← Nat.card_eq_fintype_card] at h2
  exact (Nat.not_even_iff_odd.2 hK) (Nat.even_iff.2 h2)

theorem torusElt_neg_one_conj_eq_rootDiagUnit (hK : Odd (Nat.card K))
    {a : Fin Tag.G2.rank → Kˣ} (ha : ∀ i, a i = 1 ∨ a i = -1) (hne : a ≠ 1)
    {γ : Fin Tag.G2.rank → ℤ} (hγ : γ ∈ rootCharKernel a) {w : WeylGroup .G2}
    {i : Fin Tag.G2.rank} (hw : w • (Pi.single i 1 : Fin Tag.G2.rank → ℤ) = γ) :
    canonicalRep (coxeterSystem .G2) K w * torusElt .G2 K i (-1) *
      (canonicalRep (coxeterSystem .G2) K w)⁻¹ = rootDiagUnit .G2 a := by
  have hK2 := ringChar_ne_two_of_odd_nat_card hK
  set b : Fin Tag.G2.rank → Kˣ := fun j => (-1 : Kˣ) ^ Tag.G2.cartan i j with hb
  have hbsq : ∀ j, b j ^ 2 = 1 := fun j => by
    simp only [hb]
    rcases Int.even_or_odd (Tag.G2.cartan i j) with h | h
    · simp [Even.neg_one_zpow h]
    · simp [Odd.neg_one_zpow h]
  have h1 : torusElt .G2 K i (-1) = rootDiagUnit .G2 b := torusElt_eq_rootDiagUnit i (-1)
  rw [h1, canonicalRep_conj_rootDiagUnit]
  set c := weylTuple w b with hc
  have hcsign : ∀ j, c j = 1 ∨ c j = -1 := fun j =>
    unit_eq_one_or_neg_one_of_sq_eq_one (weylTuple_sq_eq_one hbsq w j)
  have hcχ : rootChar c γ = 1 := by
    rw [hc, rootChar_weylTuple, ← hw, inv_smul_smul]
    have h2 := rootChar_nsmul_single b i 1
    rw [one_smul, pow_one] at h2
    rw [h2]
    simp [hb, Tag.cartan_self]
  have hcne : c ≠ 1 := by
    intro hc1
    have h2 : canonicalRep (coxeterSystem .G2) K w * rootDiagUnit .G2 b *
        (canonicalRep (coxeterSystem .G2) K w)⁻¹ = 1 := by
      rw [canonicalRep_conj_rootDiagUnit, ← hc, hc1, rootDiagUnit_one]
    have h3 : rootDiagUnit .G2 b = (1 : ModGL .G2 K) := by
      rwa [mul_inv_eq_one, mul_eq_left] at h2
    have h4 : simpleRootSL2 .G2 K i (-1) = simpleRootSL2 .G2 K i 1 := by
      rw [neg_one_eq_HSL, simpleRootSL2_HSL, h1, h3, map_one]
    have h5 := simpleRootSL2_injective hK2 i h4
    have h6 := congrArg (fun A : SL2 K => (A : Matrix (Fin 2) (Fin 2) K) 0 0) h5
    exact Ring.neg_one_ne_one_of_char_ne_two hK2 (by simpa using h6)
  rw [g2_eq_of_mem_rootCharKernel hK hcsign ha hcne hne ⟨hγ.1, hcχ⟩ hγ]

end Kernels

section RankOne

variable {τ : Tag} {K : Type} [Field K]

theorem exists_hom_of_isRoot (hK : ringChar K ≠ 2) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    ∃ (w : WeylGroup τ) (i : Fin τ.rank) (φ : SL2 K →* ModGL τ K),
      w • (Pi.single i 1 : Fin τ.rank → ℤ) = γ ∧ Function.Injective φ ∧
      φ.range = rootSubgroup τ K γ ⊔ rootSubgroup τ K (-γ) ∧
      φ (-1) = canonicalRep (coxeterSystem τ) K w * torusElt τ K i (-1) *
        (canonicalRep (coxeterSystem τ) K w)⁻¹ := by
  obtain ⟨w, i, hw⟩ := isRoot_iff_exists_smul_single.1 hγ
  refine ⟨w, i, (MulAut.conj (canonicalRep (coxeterSystem τ) K w)).toMonoidHom.comp
    (simpleRootSL2 τ K i), hw, ?_, ?_, ?_⟩
  · exact (MulAut.conj _).injective.comp (simpleRootSL2_injective hK i)
  · rw [MonoidHom.range_comp, range_simpleRootSL2, map_conj_canonicalRep_closure_xUnit_yUnit hw]
  · simp [neg_one_eq_HSL, simpleRootSL2_HSL]

end RankOne

section Derived

variable {X T : Type*} [Group X] [Group T]

theorem map_le_derivedSeries_of_perfect (f : X →* T) {P : Subgroup X} (hP : ⁅P, P⁆ = P) (n : ℕ) :
    P.map f ≤ derivedSeries T n := by
  induction n with
  | zero => simp [derivedSeries_zero]
  | succ n ih =>
    calc P.map f = (⁅P, P⁆).map f := by rw [hP]
      _ = ⁅P.map f, P.map f⁆ := Subgroup.map_commutator _ _ _
      _ ≤ ⁅derivedSeries T n, derivedSeries T n⁆ := Subgroup.commutator_mono ih ih
      _ = derivedSeries T (n + 1) := (derivedSeries_succ _ _).symm

theorem le_ker_of_isPerfect_of_derivedSeries_eq_bot (π : X →* T) {n : ℕ}
    (hT : derivedSeries T n = ⊥) {P : Subgroup X} (hP : ⁅P, P⁆ = P) : P ≤ π.ker := fun x hx => by
  have h := map_le_derivedSeries_of_perfect π hP n (Subgroup.mem_map_of_mem π hx)
  rw [hT, Subgroup.mem_bot] at h
  exact h

theorem le_of_isPerfect_of_derivedSeries_eq_bot {G : Type*} [Group G] {S X : Subgroup G}
    (hN : (S.subgroupOf X).Normal) (hD : derivedSeries (X ⧸ S.subgroupOf X) 2 = ⊥)
    {P : Subgroup G} (hPX : P ≤ X) (hperf : ⁅P, P⁆ = P) : P ≤ S := by
  have := hN
  have hmap : (P.subgroupOf X).map X.subtype = P := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hPX]
  have hperf' : ⁅P.subgroupOf X, P.subgroupOf X⁆ = P.subgroupOf X :=
    Subgroup.map_injective X.subtype_injective (by
      rw [Subgroup.map_commutator, hmap, hperf])
  have hle := le_ker_of_isPerfect_of_derivedSeries_eq_bot
    (QuotientGroup.mk' (S.subgroupOf X)) hD hperf'
  rw [QuotientGroup.ker_mk'] at hle
  intro y hy
  exact (Subgroup.mem_subgroupOf.1 (hle (Subgroup.mem_subgroupOf.2 hy) : (⟨y, hPX hy⟩ : X) ∈
    S.subgroupOf X))

end Derived

section Central

variable {K : Type} [Field K] [Finite K]

theorem eq_one_or_eq_rootDiagUnit_of_central (hK : Odd (Nat.card K))
    {a : Fin Tag.G2.rank → Kˣ} (ha : ∀ i, a i = 1 ∨ a i = -1) (hne : a ≠ 1)
    {P : Subgroup (ModGL .G2 K)} (hP : P ≤ toralCentralizer .G2 K a) (hperf : ⁅P, P⁆ = P)
    {c : ModGL .G2 K} (hc : c ∈ P) (hcP : ∀ y ∈ P, c * y = y * c) :
    c = 1 ∨ c = rootDiagUnit .G2 a := by
  obtain ⟨α, β, -, hker, hS, hcomm, hSX, hnorm, hD⟩ := g2_toral_data hK ha hne
  have hK2 := ringChar_ne_two_of_odd_nat_card hK
  have hPS : P ≤ rootSpan .G2 K (rootCharKernel a) :=
    le_of_isPerfect_of_derivedSeries_eq_bot hnorm hD hP hperf
  have hα : α ∈ rootCharKernel a := by
    rw [hker]
    exact Or.inl rfl
  have hβ : β ∈ rootCharKernel a := by
    rw [hker]
    exact Or.inr (Or.inr (Or.inl rfl))
  obtain ⟨wα, iα, φα, hwα, hinjα, hrangeα, hnegα⟩ := exists_hom_of_isRoot hK2 hα.1
  obtain ⟨wβ, iβ, φβ, hwβ, hinjβ, hrangeβ, hnegβ⟩ := exists_hom_of_isRoot hK2 hβ.1
  have hxα := hnegα.trans (torusElt_neg_one_conj_eq_rootDiagUnit hK ha hne hα hwα)
  have hxβ := hnegβ.trans (torusElt_neg_one_conj_eq_rootDiagUnit hK ha hne hβ hwβ)
  have hmemα : ∀ A, φα A ∈ rootSubgroup .G2 K α ⊔ rootSubgroup .G2 K (-α) := fun A => by
    rw [← hrangeα]
    exact ⟨A, rfl⟩
  have hmemβ : ∀ A, φβ A ∈ rootSubgroup .G2 K β ⊔ rootSubgroup .G2 K (-β) := fun A => by
    rw [← hrangeβ]
    exact ⟨A, rfl⟩
  have hmul : ∀ (x y : ModGL .G2 K), x ∈ rootSubgroup .G2 K α ⊔ rootSubgroup .G2 K (-α) →
      y ∈ rootSubgroup .G2 K β ⊔ rootSubgroup .G2 K (-β) → x * y = y * x := fun x y hx hy =>
    (Subgroup.mem_centralizer_iff.1 (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm hx) y
      hy).symm
  refine eq_one_or_eq_of_isPerfect_of_le_iSup_range (F := fun _ : Bool => K)
    (fun j => cond j φα φβ) ?_ (rootDiagUnit .G2 a) ?_ ?_ ?_ ?_ hperf hc hcP
  · intro j
    cases j
    exacts [hinjβ, hinjα]
  · intro j
    cases j
    exacts [hxβ, hxα]
  · rw [← rootDiagUnit_mul]
    have : a * a = 1 := funext fun j => by rcases ha j with h | h <;> simp [h]
    rw [this, rootDiagUnit_one]
  · intro i j hij A B
    cases i <;> cases j
    · exact absurd rfl hij
    · exact (hmul _ _ (hmemα B) (hmemβ A)).symm
    · exact hmul _ _ (hmemα A) (hmemβ B)
    · exact absurd rfl hij
  · rw [iSup_bool_eq]
    show P ≤ (φα.range ⊔ φβ.range)
    rw [hrangeα, hrangeβ, ← hS]
    exact hPS

theorem g2_eq_one_or_eq_of_central_in_perfect (hK : Odd (Nat.card K))
    {t : ↥(adjointGroup .G2 K)} (ht : t * t = 1) (ht1 : t ≠ 1)
    {P : Subgroup ↥(adjointGroup .G2 K)} (hPt : ∀ r ∈ P, t * r = r * t) (hperf : ⁅P, P⁆ = P)
    {c : ↥(adjointGroup .G2 K)} (hc : c ∈ P) (hcP : ∀ r ∈ P, c * r = r * c) :
    c = 1 ∨ c = t := by
  obtain ⟨g, b, hb, hgb⟩ :=
    ModelFacts.exists_conj_eq_rootDiagUnit_of_involution (Or.inl rfl) hK t ht
  have hb1 : b ≠ 1 := by
    rintro rfl
    rw [rootDiagUnit_one] at hgb
    apply ht1
    have h1 : g * t * g⁻¹ = 1 := Subtype.ext hgb
    rwa [mul_inv_eq_one, mul_eq_left] at h1
  set ι : ↥(adjointGroup .G2 K) →* ModGL .G2 K := (adjointGroup .G2 K).subtype with hι
  set Q : Subgroup (ModGL .G2 K) := (P.map (MulAut.conj g).toMonoidHom).map ι with hQ
  have hQperf : ⁅Q, Q⁆ = Q := by
    rw [hQ, ← Subgroup.map_commutator, ← Subgroup.map_commutator, hperf]
  have hconj_mem : ∀ r ∈ P, ι (g * r * g⁻¹) ∈ Q := fun r hr => ⟨_, ⟨r, hr, rfl⟩, rfl⟩
  have hQX : Q ≤ toralCentralizer .G2 K b := by
    rintro _ ⟨_, ⟨r, hr, rfl⟩, rfl⟩
    refine mem_toralCentralizer.2 ⟨(g * r * g⁻¹).2, ?_⟩
    have hcomm : (g * t * g⁻¹) * (g * r * g⁻¹) = (g * r * g⁻¹) * (g * t * g⁻¹) := by
      calc g * t * g⁻¹ * (g * r * g⁻¹) = g * (t * r) * g⁻¹ := by group
        _ = g * (r * t) * g⁻¹ := by rw [hPt r hr]
        _ = g * r * g⁻¹ * (g * t * g⁻¹) := by group
    rw [← hgb]
    exact mul_inv_eq_iff_eq_mul.2 (congrArg Subtype.val hcomm)
  have hcent : ∀ y ∈ Q, ι (g * c * g⁻¹) * y = y * ι (g * c * g⁻¹) := by
    rintro _ ⟨_, ⟨r, hr, rfl⟩, rfl⟩
    show ι (g * c * g⁻¹) * ι (g * r * g⁻¹) = ι (g * r * g⁻¹) * ι (g * c * g⁻¹)
    rw [← map_mul, ← map_mul]
    congr 1
    calc g * c * g⁻¹ * (g * r * g⁻¹) = g * (c * r) * g⁻¹ := by group
      _ = g * (r * c) * g⁻¹ := by rw [hcP r hr]
      _ = g * r * g⁻¹ * (g * c * g⁻¹) := by group
  rcases eq_one_or_eq_rootDiagUnit_of_central hK hb hb1 hQX hQperf (hconj_mem c hc) hcent with
    h | h
  · left
    have h1 : g * c * g⁻¹ = 1 := Subtype.ext h
    rwa [mul_inv_eq_one, mul_eq_left] at h1
  · right
    have h1 : g * c * g⁻¹ = g * t * g⁻¹ := Subtype.ext (h.trans hgb.symm)
    exact mul_left_cancel (mul_right_cancel h1)

end Central

section Main

open CFSG.Assembly.LowTwoRank

variable {p e : ℕ} [Fact p.Prime]

theorem layerGenerationPairAt_g2 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) {n : ℕ}
    (hadm : StatedLieAdmissible .G2 n p e) : LayerGenerationPairAt .G2 n p e Fact.out := by
  obtain ⟨hodd, -⟩ := ModelFacts.card_galoisField_facts hp2 hq
  refine layerGenerationPairAt_of_shared_central Fact.out center_adjointGroup_eq_bot ?_
  intro R₁ hR₁ R₂ hR₂ c₁ hc₁ c₂ hc₂ hz₁ hz₂ hx₁₂ hx₂₁ hsq₁ hsq₂ hn₁ hn₂
  have hperf : ⁅R₂, R₂⁆ = R₂ :=
    le_antisymm (Subgroup.commutator_le.mpr fun _ hx _ hy =>
      R₂.mul_mem (R₂.mul_mem (R₂.mul_mem hx hy) (R₂.inv_mem hx)) (R₂.inv_mem hy))
      (ModelFacts.fundPerfect_core .G2 n p e hp2 trivial hadm (by omega) R₂ hR₂)
  rcases g2_eq_one_or_eq_of_central_in_perfect (K := GaloisField p e) hodd hsq₁ hn₁ hx₂₁ hperf hc₂
    hz₂ with h | h
  · exact absurd h hn₂
  · exact h.symm

theorem LayerGenerationHybrid.of_commuting_remaining
    (hB : ∀ (t : StatedLieTag) (n e : ℕ), t ≠ .G2 → t ≠ .trialityD4 → Generic.IsFundTag t →
      StatedLieAdmissible t n p e → p ≠ 2 → 5 ≤ p ^ e →
        ModelFacts.CommutingFundamentalGeneration p t n e) :
    LayerGenerationHybrid p := by
  intro t n e hfund hadm hp2 h5
  by_cases h1 : t = .G2
  · subst h1
    exact Or.inl (layerGenerationPairAt_g2 hp2 h5 hadm)
  by_cases h2 : t = .trialityD4
  · subst h2
    exact Or.inl (layerGenerationPairAt_trialityD4 Fact.out hp2 h5 hadm)
  exact Or.inr ⟨h1, h2, hB t n e h1 h2 hfund hadm hp2 h5⟩

end Main

end CFSG.ClassicalInvolution.Balance.Bootstrap
