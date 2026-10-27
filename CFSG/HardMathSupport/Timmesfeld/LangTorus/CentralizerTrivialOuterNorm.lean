module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialPoly
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CyclicNormCentralizer
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigidTools
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterFieldCore
public import CFSG.RankThree.Chevalley.SteinbergBIRootSL2Tools
public import CFSG.RankThree.PartOne.KE.A1SL2

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Classical
open scoped MatrixGroups

set_option linter.unusedSectionVars false

theorem outer_list_prod_mul {G H : Type*} [Monoid G] [Monoid H] (f : ℕ → G →* H) :
    ∀ l : List ℕ, l.Nodup → (∀ j ∈ l, ∀ k ∈ l, j ≠ k → ∀ x y, Commute (f j x) (f k y)) →
      ∀ x y : G, (l.map fun j => f j (x * y)).prod =
        (l.map fun j => f j x).prod * (l.map fun j => f j y).prod
  | [], _, _, x, y => by simp
  | j :: l, hnd, hc, x, y => by
    have hnd' := List.nodup_cons.1 hnd
    have ih := outer_list_prod_mul f l hnd'.2 (fun a ha b hb hab =>
      hc a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb) hab) x y
    have hjy : Commute (f j y) (l.map fun k => f k x).prod := by
      refine Commute.list_prod_right _ _ fun b hb => ?_
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hb
      exact (hc k (List.mem_cons_of_mem _ hk) j List.mem_cons_self
        (fun h => hnd'.1 (h ▸ hk)) x y).symm
    simp only [List.map_cons, List.prod_cons]
    rw [ih, map_mul, mul_assoc, ← mul_assoc (f j y), hjy.eq]
    simp only [mul_assoc]

theorem outer_prod_flatMap {α M : Type*} [Monoid M] (l : List α) (f : α → List M) :
    (l.flatMap f).prod = (l.map fun a => (f a).prod).prod := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.flatMap_cons, List.prod_append, ih, List.map_cons, List.prod_cons]

section Norm

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)

theorem outer_commute_conj_pinnedX_of_prod (hτ : τ ≠ .G2) (hq3 : 3 ≤ S.D.q) {K : Subfield L}
    [Fintype K] {n : ℕ} (hn : 0 < n) (hK : Fintype.card K = S.D.q ^ n)
    (hQ4 : 4 ≤ S.D.q ^ n) (ks : List ℕ) (hnd : ks.Nodup) (h0 : 0 ∈ ks)
    (hks : ∀ k ∈ ks, k < n) (g : ModGL τ L) {δ : Fin τ.rank → ℤ} (hδ : IsRoot τ δ)
    (z : ModGL τ L)
    (h : ∀ t : K, Commute z ((ks.map fun N =>
      iterHom S.D.step N (g * pinnedX τ L δ (t : L) * g⁻¹)).prod)) :
    ∀ c : L, Commute z (g * pinnedX τ L δ c * g⁻¹) := by
  classical
  have hdata := fun N : ℕ => exists_factor_data S hτ (RingHom.id L) g hδ N
  choose aN bN aN' bN' haN haN' hrkN hE1 hE2 using hdata
  have hsq : ∀ (x : L) (k : ℕ), x ^ (2 * k) = (x ^ k) ^ 2 := fun x k => by
    rw [← pow_mul, mul_comm]
  have hmain : ∀ t : K,
      (z : Module.End L (RootModule τ L)) * evAt (K.subtype t) (prodList S.D.q aN bN ks) =
        evAt (K.subtype t) (prodList S.D.q aN bN ks) * (z : Module.End L (RootModule τ L)) := by
    intro t
    have hR : evAt (t : L) (prodList S.D.q aN bN ks) =
        (ks.map fun N => ((iterHom S.D.step N (g * pinnedX τ L δ (t : L) * g⁻¹) : ModGL τ L) :
          Module.End L (RootModule τ L))).prod := by
      rw [evAt_prodList]
      congr 1
      refine List.map_congr_left fun N _ => ?_
      rw [hE1 N (t : L), hsq]
    have hf := congrArg (fun x : ModGL τ L => (x : Module.End L (RootModule τ L))) (h t).eq
    simp only [Units.val_mul] at hf
    rw [units_coe_list_prod] at hf
    show _ * evAt (t : L) _ = evAt (t : L) _ * _
    rw [hR]
    exact hf
  obtain ⟨hza, hzb⟩ := commute_coeff_one_two K.subtype hq3 hn hK hQ4 ks hnd h0 hks aN bN
    (z : Module.End L (RootModule τ L)) hmain
  intro c
  have hform := hE1 0 c
  rw [iterHom_zero, pow_zero, pow_one] at hform
  generalize g * pinnedX τ L δ c * g⁻¹ = W at hform ⊢
  show z * W = W * z
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, hform]
  simp only [mul_add, add_mul, mul_one, one_mul, mul_smul_comm, smul_mul_assoc, hza, hzb]

theorem outer_map_uSL {K K' : Type*} [Field K] [Field K'] (f : K →+* K') (c : K) :
    Matrix.SpecialLinearGroup.map f (uSL c) = uSL (f c) := by
  apply Subtype.ext
  ext a b
  fin_cases a <;> fin_cases b <;> simp [coe_uSL]

theorem outer_map_vSL {K K' : Type*} [Field K] [Field K'] (f : K →+* K') (c : K) :
    Matrix.SpecialLinearGroup.map f (vSL c) = vSL (f c) := by
  apply Subtype.ext
  ext a b
  fin_cases a <;> fin_cases b <;> simp [coe_vSL]

theorem outer_exists_theta {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} (i : KernelComponent χ)
    {φ₁ : ModGL τ L →* ModGL τ L}
    {γ : Fin τ.rank → ℤ} {m : ℕ} (hm : 0 < m)
    (β : ℕ → Fin τ.rank → ℤ) (hβΨ : ∀ j, β j ∈ componentRoots χ i)
    (hβ : ∀ j < m, ∀ B, φ₁^[j] (rootSL2 τ L γ B) ∈ rootRankOneGroup τ L (β j))
    (hcomm₁ : ∀ j l, j < m → l < m → j ≠ l → ∀ x ∈ rootRankOneGroup τ L (β j),
      ∀ y ∈ rootRankOneGroup τ L (β l), Commute x y)
    (σm : L ≃+* L) (X : GL (Fin 2) L)
    (hret : ∀ B, φ₁^[m] (rootSL2 τ L γ B) =
      rootSL2 τ L γ (conjSL X (Matrix.SpecialLinearGroup.map σm.toRingHom B)))
    (P : GL (Fin 2) L) (hP : P * Matrix.GeneralLinearGroup.map σm.toRingHom P⁻¹ = X) :
    ∃ θ : SL(2, fixSubfield σm) →* ModGL τ L,
      (∀ A, θ A = ((List.range m).map fun j => φ₁^[j] (rootSL2 τ L γ
        (conjSL P (Matrix.SpecialLinearGroup.map (algebraMap (fixSubfield σm) L) A)))).prod) ∧
      (∀ A, φ₁ (θ A) = θ A) ∧ ∀ A, θ A ∈ rootSpan τ L (componentRoots χ i) := by
  classical
  have hQle : ∀ {δ : Fin τ.rank → ℤ}, δ ∈ componentRoots χ i →
      rootRankOneGroup τ L δ ≤ rootSpan τ L (componentRoots χ i) := by
    intro δ hδ
    rw [rootRankOneGroup, range_rootSL2_of_isRoot (isRoot_of_mem_componentRoots hδ)]
    exact sup_le (rootSubgroup_le_rootSpan hδ)
      (rootSubgroup_le_rootSpan ((isRootComponent_componentRoots i).neg_mem _ hδ))
  have hfixK : ∀ c, σm.toRingHom c = c ↔ c ∈ Set.range (algebraMap (fixSubfield σm) L) := by
    intro c
    constructor
    · intro h
      exact ⟨⟨c, h⟩, rfl⟩
    · rintro ⟨d, rfl⟩
      exact d.2
  set ιK : fixSubfield σm →+* L := algebraMap (fixSubfield σm) L with hιK
  let f₀ : SL(2, fixSubfield σm) →* ModGL τ L :=
    (rootSL2 τ L γ).comp ((conjSL P).comp (Matrix.SpecialLinearGroup.map ιK))
  have hf₀ : ∀ A, f₀ A = rootSL2 τ L γ (conjSL P (Matrix.SpecialLinearGroup.map ιK A)) :=
    fun A => rfl
  let fj : ℕ → SL(2, fixSubfield σm) →* ModGL τ L := fun j => (iterHom φ₁ j).comp f₀
  have hfj : ∀ j A, fj j A = φ₁^[j] (f₀ A) := fun j A => iterHom_eq_iterate φ₁ j _
  have hfjQ : ∀ j < m, ∀ A, fj j A ∈ rootRankOneGroup τ L (β j) := fun j hj A => by
    rw [hfj]
    exact hβ j hj _
  have hcommf : ∀ j ∈ List.range m, ∀ k ∈ List.range m, j ≠ k →
      ∀ x y, Commute (fj j x) (fj k y) := fun j hj k hk hjk x y =>
    hcomm₁ j k (List.mem_range.1 hj) (List.mem_range.1 hk) hjk _
      (hfjQ j (List.mem_range.1 hj) x) _ (hfjQ k (List.mem_range.1 hk) y)
  let θ : SL(2, fixSubfield σm) →* ModGL τ L :=
    { toFun := fun A => ((List.range m).map fun j => fj j A).prod
      map_one' := by simp
      map_mul' := fun A B => outer_list_prod_mul fj (List.range m) List.nodup_range hcommf
        A B }
  have hθ : ∀ A, θ A = ((List.range m).map fun j => fj j A).prod := fun A => rfl
  have hθS : ∀ A, θ A ∈ rootSpan τ L (componentRoots χ i) := fun A =>
    Subgroup.list_prod_mem _ fun x hx => by
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
      exact hQle (hβΨ j) (hfjQ j (List.mem_range.1 hj) A)
  have hfm : ∀ A, fj m A = fj 0 A := by
    intro A
    rw [hfj, hfj, Function.iterate_zero, id_eq, hf₀, hret, ← hP]
    congr 1
    exact (sl2_twistedFixed_iff σm.toRingHom hfixK P _).2 ⟨_, ⟨A, rfl⟩, rfl⟩
  have hθfix : ∀ A, φ₁ (θ A) = θ A := by
    intro A
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have h1 : φ₁ (θ A) = ((List.range (m' + 1)).map fun j => fj (j + 1) A).prod := by
      rw [hθ, map_list_prod, List.map_map]
      rfl
    have h2 : ((List.range (m' + 1)).map fun j => fj (j + 1) A).prod =
        ((List.range m').map fun j => fj (j + 1) A).prod * fj 0 A := by
      rw [List.range_succ, List.map_append, List.prod_append, List.map_singleton,
        List.prod_singleton, hfm]
    have h3 : θ A = fj 0 A * ((List.range m').map fun j => fj (j + 1) A).prod := by
      rw [hθ, List.range_succ_eq_map, List.map_cons, List.prod_cons, List.map_map]
      rfl
    have hc0 : Commute (fj 0 A) ((List.range m').map fun j => fj (j + 1) A).prod :=
      Commute.list_prod_right _ _ fun b hb => by
        obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hb
        have hj' := List.mem_range.1 hj
        exact hcommf 0 (List.mem_range.2 (by omega)) (j + 1) (List.mem_range.2 (by omega))
          (by omega) A A
    rw [h1, h2, h3, hc0.eq]
  refine ⟨θ, fun A => ?_, hθfix, hθS⟩
  rw [hθ]
  congr 1
  exact List.map_congr_left fun j _ => hfj j A

@[expose] def OuterPinned (φ₁ : ModGL τ L →* ModGL τ L) (g : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ)
    (Q : ℕ) : Prop :=
  ∀ β, IsRoot τ β → IsRoot τ (g β) ∧
    ∃ μ : L, μ ≠ 0 ∧ ∀ t : L, φ₁ (pinnedX τ L β t) = pinnedX τ L (g β) (μ * t ^ Q)

omit [IsAlgClosed L] in
theorem OuterPinned.comp {φ₁ φ₂ : ModGL τ L →* ModGL τ L}
    {g₁ g₂ : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ} {Q₁ Q₂ : ℕ} (h₁ : OuterPinned φ₁ g₁ Q₁)
    (h₂ : OuterPinned φ₂ g₂ Q₂) :
    OuterPinned (φ₂.comp φ₁) (g₂ ∘ g₁) (Q₁ * Q₂) := by
  intro β hβ
  obtain ⟨hg₁, μ₁, hμ₁, h1⟩ := h₁ β hβ
  obtain ⟨hg₂, μ₂, hμ₂, h2⟩ := h₂ _ hg₁
  refine ⟨hg₂, μ₂ * μ₁ ^ Q₂, mul_ne_zero hμ₂ (pow_ne_zero _ hμ₁), fun t => ?_⟩
  rw [MonoidHom.comp_apply, h1, h2, Function.comp_apply, mul_pow, ← pow_mul, mul_assoc]

omit [IsAlgClosed L] in
theorem OuterPinned.iterate {φ₁ : ModGL τ L →* ModGL τ L} {g : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ}
    {Q : ℕ} (h : OuterPinned φ₁ g Q) : ∀ n : ℕ, OuterPinned (iterHom φ₁ n) (g^[n]) (Q ^ n)
  | 0 => fun β hβ => ⟨hβ, 1, one_ne_zero, fun t => by simp⟩
  | n + 1 => by
    have h' := (OuterPinned.iterate h n).comp h
    intro β hβ
    obtain ⟨hg, μ, hμ, hf⟩ := h' β hβ
    refine ⟨by rw [Function.iterate_succ']; exact hg, μ, hμ, fun t => ?_⟩
    rw [Function.iterate_succ', pow_succ]
    exact hf t

theorem commute_component_fixed
    {tau : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup tau L p) {a : Fin tau.rank → Lˣ}
    (hT : rootDiagUnit tau a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    {s : ℕ} [NeZero s]
    (hs : (S.ρ : (Fin tau.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom a) i =
      componentRoots (rootCharHom a) i)
    (hmin : ∀ k, 0 < k → k < s →
      (S.ρ : (Fin tau.rank → ℤ) → _)^[k] '' componentRoots (rootCharHom a) i ≠
        componentRoots (rootCharHom a) i)
    (z : ModGL tau L) (hzF : S.D.step z = z)
    (hzN : ∀ j : KernelComponent (rootCharHom a),
      z ∈ Subgroup.normalizer (rootSpan tau L (componentRoots (rootCharHom a) j) : Set _))
    (hcomm : ∀ x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i, Commute z x)
    {C : Type*} [Group C] (hC : Group.IsPerfect C)
    (theta : C →* (outerOrbitFamily S hT i hs hmin).S 0)
    (hThetaF : ∀ c, iterHom S.D.step s
        (theta c : ModGL tau L) = theta c) :
    ∀ c, Commute z (theta c : ModGL tau L) := by
  have hPN : ∀ k : ZMod s, z ∈ Subgroup.normalizer
      ((outerOrbitFamily S hT i hs hmin).S k : Set (ModGL tau L)) := by
    intro k
    rw [outerOrbitFamily_S]
    obtain ⟨j, hj⟩ := outer_iterate_image_component S hT i k.val
    rw [← hj]
    exact hzN j
  exact (outerOrbitFamily S hT i hs hmin).commute_of_norm_comp hC theta hzF hPN
    (fun c => hcomm _ (outer_norm_mem_rationalComponent S hT i hs hmin hC theta hThetaF c))

theorem commute_conj_pinnedX_of_outer_prod
    {tau : Tag} {L : Type} [Field L] [IsAlgClosed L] (hG2 : tau ≠ .G2)
    {phi : ModGL tau L →* ModGL tau L}
    {f : (Fin tau.rank → ℤ) → Fin tau.rank → ℤ} {Q : ℕ}
    (hpin : OuterPinned phi f Q) (hQ : 3 ≤ Q)
    {K : Type} [Field K] [Fintype K] (incl : K →+* L)
    {m : ℕ} (hm : 0 < m) (hCard : Fintype.card K = Q ^ m) (h4 : 4 ≤ Q ^ m)
    (u z : ModGL tau L) {gamma : Fin tau.rank → ℤ} (hgamma : IsRoot tau gamma)
    (hcomm : ∀ t : K, Commute z (((List.range m).map fun j =>
      iterHom phi j (u * pinnedX tau L gamma (incl t) * u⁻¹)).prod)) :
    ∀ c : L, Commute z (u * pinnedX tau L gamma c * u⁻¹) := by
  classical
  have hData : ∀ j : ℕ, ∃ a b : Module.End L (RootModule tau L),
      ∀ t : L, ((iterHom phi j (u * pinnedX tau L gamma t * u⁻¹) : ModGL tau L) :
        Module.End L (RootModule tau L)) = 1 + (t ^ (Q ^ j)) • a + (t ^ (Q ^ j)) ^ 2 • b := by
    intro j
    obtain ⟨hfj, mu, hmu, hmuX⟩ := (hpin.iterate j) gamma hgamma
    obtain ⟨a, b, ha, hRank, hExpand⟩ := conj_map_pinnedX_expand
      hG2 (RingHom.id L) (iterHom phi j u) hmu (f^[j] gamma)
    refine ⟨a, b, fun t => ?_⟩
    rw [map_mul, map_mul, map_inv, hmuX]
    have hE := hExpand (t ^ (Q ^ j))
    have hId : ∀ x : ModGL tau L, Units.map (entrywiseHom (RingHom.id L)) x = x :=
      fun x => Units.ext (entrywise_id _)
    simpa only [hId, RingHom.id_apply] using hE
  choose as bs hExpand using hData
  have hPoly : ∀ t : K,
      (z : Module.End L (RootModule tau L)) * evAt (incl t) (prodList Q as bs (List.range m)) =
      evAt (incl t) (prodList Q as bs (List.range m)) * (z : Module.End L (RootModule tau L)) := by
    intro t
    have hE : evAt (incl t) (prodList Q as bs (List.range m)) =
        ((List.range m).map fun j =>
          ((iterHom phi j (u * pinnedX tau L gamma (incl t) * u⁻¹) : ModGL tau L) :
            Module.End L (RootModule tau L))).prod := by
      rw [evAt_prodList]
      congr 1
      apply List.map_congr_left
      intro j hj
      have hPower : (incl t) ^ (2 * Q ^ j) = ((incl t) ^ (Q ^ j)) ^ 2 := by
        rw [← pow_mul, Nat.mul_comm 2]
      rw [hPower]
      exact (hExpand j (incl t)).symm
    have h := congrArg (fun x : ModGL tau L => (x : Module.End L (RootModule tau L)))
      (hcomm t).eq
    simp only [Units.val_mul, units_coe_list_prod] at h
    rw [hE]
    exact h
  obtain ⟨hA, hB⟩ := commute_coeff_one_two incl hQ hm hCard h4 (List.range m)
    List.nodup_range (List.mem_range.mpr hm) (fun j hj => List.mem_range.mp hj)
    as bs (z : Module.End L (RootModule tau L)) hPoly
  intro c
  have hE := hExpand 0 c
  rw [iterHom_zero, pow_zero, pow_one] at hE
  apply Units.ext
  change (z : Module.End L (RootModule tau L)) *
      ((u * pinnedX tau L gamma c * u⁻¹ : ModGL tau L) : Module.End L (RootModule tau L)) =
    ((u * pinnedX tau L gamma c * u⁻¹ : ModGL tau L) : Module.End L (RootModule tau L)) *
      (z : Module.End L (RootModule tau L))
  rw [hE]
  simp only [mul_add, add_mul, mul_one, one_mul, mul_smul_comm, smul_mul_assoc, hA, hB]

theorem outer_commute_of_orbit_of_field_or_fixed (hτ : τ ≠ .G2) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    {z₀ : ModGL τ L}
    (hz₀ : ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
      z₀ * g * z₀⁻¹ ∈ rootSpan τ L (componentRoots (rootCharHom a) i))
    {φ₁ : ModGL τ L →* ModGL τ L}
    (hφ₁ : ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
      iterHom S.D.step (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))
        (z₀ * g * z₀⁻¹) = z₀ * φ₁ g * z₀⁻¹)
    (hφ₁S : ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
      φ₁ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i))
    {γ : Fin τ.rank → ℤ} (hγ : γ ∈ componentRoots (rootCharHom a) i) {m : ℕ} (hm : 0 < m)
    (hQ4 : 4 ≤ S.D.q ^ (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) * m))
    (β : ℕ → Fin τ.rank → ℤ) (hβΨ : ∀ j, β j ∈ componentRoots (rootCharHom a) i)
    (hβ : ∀ j < m, ∀ B, φ₁^[j] (rootSL2 τ L γ B) ∈ rootRankOneGroup τ L (β j))
    (hcomm₁ : ∀ j l, j < m → l < m → j ≠ l → ∀ x ∈ rootRankOneGroup τ L (β j),
      ∀ y ∈ rootRankOneGroup τ L (β l), Commute x y)
    (σm : L ≃+* L) (hσm : ∀ c, σm c = c ^ (S.D.q ^
      (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) * m)))
    (X : GL (Fin 2) L)
    (hret : ∀ B, φ₁^[m] (rootSL2 τ L γ B) =
      rootSL2 τ L γ (conjSL X (Matrix.SpecialLinearGroup.map σm.toRingHom B)))
    (P : GL (Fin 2) L) (hP : P * Matrix.GeneralLinearGroup.map σm.toRingHom P⁻¹ = X)
    (z : ModGL τ L)
    (hCase : 3 ≤ S.D.q ∨
      (S.D.step z = z ∧
        (∀ j : KernelComponent (rootCharHom a), z ∈ Subgroup.normalizer
          (rootSpan τ L (componentRoots (rootCharHom a) j) : Set _)) ∧
        ∃ f, OuterPinned φ₁ f
          (S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) ∧
          3 ≤ S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)))
    (hcomm : ∀ x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i, Commute z x) :
    ∀ B : SL2 L, Commute z (z₀ * rootSL2 τ L γ B * z₀⁻¹) := by
  classical
  obtain ⟨hs0, hs, hmin⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hsdef
  have : NeZero s := ⟨hs0.ne'⟩
  have hP0 : (outerOrbitFamily S hT i hs hmin).S 0 =
      rootSpan τ L (componentRoots (rootCharHom a) i) := by
    rw [outerOrbitFamily_S, ZMod.val_zero]
    simp only [Function.iterate_zero, id_eq, Set.image_id']
  have hγr : IsRoot τ γ := isRoot_of_mem_componentRoots hγ
  have hQle : ∀ {δ : Fin τ.rank → ℤ}, δ ∈ componentRoots (rootCharHom a) i →
      rootRankOneGroup τ L δ ≤ rootSpan τ L (componentRoots (rootCharHom a) i) := by
    intro δ hδ
    rw [rootRankOneGroup, range_rootSL2_of_isRoot (isRoot_of_mem_componentRoots hδ)]
    exact sup_le (rootSubgroup_le_rootSpan hδ)
      (rootSubgroup_le_rootSpan ((isRootComponent_componentRoots i).neg_mem _ hδ))
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  have : Fact r.Prime := ⟨hr⟩
  have hsm : 0 < s * m := Nat.mul_pos hs0 hm
  have hesm : 0 < e * (s * m) := Nat.mul_pos he hsm
  have hσm' : ∀ c, σm c = c ^ (r ^ (e * (s * m))) := fun c => by rw [hσm, hq, ← pow_mul]
  obtain ⟨hfinset, hcardset⟩ := ncard_pow_eq_self (L := L) r (e * (s * m)) hesm
  have hset : (fixSubfield σm : Set L) = {c : L | c ^ (r ^ (e * (s * m))) = c} := by
    ext c
    show c ∈ fixSubfield σm ↔ _
    rw [mem_fixSubfield, hσm']
    rfl
  have hfinK : Finite (fixSubfield σm) := by
    have h1 : (fixSubfield σm : Set L).Finite := by rw [hset]; exact hfinset
    exact h1.to_subtype
  have hKcard : Nat.card (fixSubfield σm) = r ^ (e * (s * m)) := by
    have h1 : Nat.card (fixSubfield σm) = (fixSubfield σm : Set L).ncard :=
      Nat.card_coe_set_eq (fixSubfield σm : Set L)
    rw [h1, hset, hcardset]
  let : Fintype (fixSubfield σm) := Fintype.ofFinite _
  have hKcard' : Fintype.card (fixSubfield σm) = S.D.q ^ (s * m) := by
    rw [← Nat.card_eq_fintype_card, hKcard, hq, ← pow_mul]
  have hQ4m : 4 ≤ S.D.q ^ (s * m) := hQ4
  have hperf : Group.IsPerfect (SL(2, fixSubfield σm)) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card _
      (by rw [Nat.card_eq_fintype_card, hKcard']; exact hQ4m)
  obtain ⟨θ, hθ, hθfix, hθS⟩ := outer_exists_theta i hm β hβΨ hβ hcomm₁ σm X hret P hP
  set ιK : fixSubfield σm →+* L := algebraMap (fixSubfield σm) L with hιK
  let f₀ : SL(2, fixSubfield σm) →* ModGL τ L :=
    (rootSL2 τ L γ).comp ((conjSL P).comp (Matrix.SpecialLinearGroup.map ιK))
  have hf₀ : ∀ A, f₀ A = rootSL2 τ L γ (conjSL P (Matrix.SpecialLinearGroup.map ιK A)) :=
    fun A => rfl
  have hf₀S : ∀ A, f₀ A ∈ rootSpan τ L (componentRoots (rootCharHom a) i) := fun A =>
    hQle hγ ⟨_, rfl⟩
  let θ₁ : SL(2, fixSubfield σm) →* (outerOrbitFamily S hT i hs hmin).S 0 :=
    ((MulAut.conj z₀).toMonoidHom.comp θ).codRestrict _ fun A => by
      rw [hP0]
      exact hz₀ _ (hθS A)
  have hθ₁ : ∀ A, ((θ₁ A : (outerOrbitFamily S hT i hs hmin).S 0) : ModGL τ L) =
      z₀ * θ A * z₀⁻¹ := fun A => rfl
  have hθ₁fix : ∀ A, iterHom S.D.step s ((θ₁ A : (outerOrbitFamily S hT i hs hmin).S 0) :
      ModGL τ L) = θ₁ A := fun A => by
    rw [hθ₁, hφ₁ _ (hθS A), hθfix]
  have hzN : ∀ A, Commute z ((outerOrbitFamily S hT i hs hmin).norm (θ₁ A)) := fun A =>
    hcomm _ (outer_norm_mem_rationalComponent S hT i hs hmin hperf θ₁ hθ₁fix A)
  have hiterS : ∀ j, ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
      φ₁^[j] g ∈ rootSpan τ L (componentRoots (rootCharHom a) i) := by
    intro j
    induction j with
    | zero => exact fun g hg => hg
    | succ j ih =>
      intro g hg
      rw [Function.iterate_succ_apply']
      exact hφ₁S _ (ih g hg)
  have hiter : ∀ j, ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
      z₀ * φ₁^[j] g * z₀⁻¹ = iterHom S.D.step (s * j) (z₀ * g * z₀⁻¹) := by
    intro j
    induction j with
    | zero => intro g _; simp
    | succ j ih =>
      intro g hg
      rw [Function.iterate_succ_apply', ← hφ₁ _ (hiterS j g hg), ih g hg, ← iterHom_add,
        show s * (j + 1) = s + s * j by ring]
  set ks : List ℕ := (Finset.univ : Finset (ZMod s)).toList.flatMap
    fun κ => (List.range m).map fun j => κ.val + s * j with hks
  have hnorm : ∀ A, ((outerOrbitFamily S hT i hs hmin).norm (θ₁ A) : ModGL τ L) =
      (ks.map fun N => iterHom S.D.step N (z₀ * f₀ A * z₀⁻¹)).prod := by
    intro A
    have hy : z₀ * θ A * z₀⁻¹ = ((List.range m).map fun j =>
        iterHom S.D.step (s * j) (z₀ * f₀ A * z₀⁻¹)).prod := by
      calc z₀ * θ A * z₀⁻¹ = MulAut.conj z₀ (θ A) := rfl
        _ = ((List.range m).map fun j => MulAut.conj z₀ (φ₁^[j] (f₀ A))).prod := by
          rw [hθ, map_list_prod, List.map_map]
          rfl
        _ = _ := by
          congr 1
          refine List.map_congr_left fun j _ => ?_
          rw [MulAut.conj_apply, hiter j _ (hf₀S A)]
    rw [norm_eq_list_prod, hθ₁, hy, hks, List.map_flatMap, outer_prod_flatMap]
    congr 1
    refine List.map_congr_left fun κ _ => ?_
    rw [map_list_prod, List.map_map, List.map_map]
    congr 1
    refine List.map_congr_left fun j _ => ?_
    simp only [Function.comp_apply]
    rw [← iterHom_add]
  have hksl : ∀ N ∈ ks, N < s * m := by
    intro N hN
    rw [hks, List.mem_flatMap] at hN
    obtain ⟨κ, -, hN⟩ := hN
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hN
    have h1 := ZMod.val_lt κ
    have h2 := List.mem_range.1 hj
    nlinarith
  have h0 : 0 ∈ ks := by
    rw [hks, List.mem_flatMap]
    exact ⟨0, Finset.mem_toList.2 (Finset.mem_univ _),
      List.mem_map.2 ⟨0, List.mem_range.2 hm, by simp⟩⟩
  have hnd : ks.Nodup := by
    rw [hks]
    refine List.nodup_flatMap.2 ⟨fun κ _ => List.Nodup.map (fun j₁ j₂ h => ?_) List.nodup_range,
      ?_⟩
    · have h' : s * j₁ = s * j₂ := by omega
      exact Nat.eq_of_mul_eq_mul_left hs0 h'
    · refine (List.Pairwise.imp (fun {κ₁ κ₂} hne => ?_)) (Finset.nodup_toList _)
      rw [Function.onFun, List.disjoint_left]
      intro N h1 h2
      obtain ⟨j₁, -, rfl⟩ := List.mem_map.1 h1
      obtain ⟨j₂, -, e⟩ := List.mem_map.1 h2
      apply hne
      apply ZMod.val_injective
      have := congrArg (· % s) e
      simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (ZMod.val_lt _)] at this
      exact this.symm
  obtain ⟨P', hP'⟩ := exists_sl2_conjSL P
  set g' : ModGL τ L := z₀ * rootSL2 τ L γ P' with hg'
  have hconjB : ∀ B : SL2 L, z₀ * rootSL2 τ L γ (conjSL P B) * z₀⁻¹ =
      g' * rootSL2 τ L γ B * g'⁻¹ := fun B => by
    rw [hP', map_mul, map_mul, map_inv, hg']
    group
  set ε : ℤ := (pinnedData τ γ).2.2 with hε
  have hεε : ∀ c : L, ε • ε • c = c := by
    intro c
    rcases pinnedSign_eq τ γ with h | h <;> rw [hε, h] <;> simp
  obtain ⟨η, hη, hv⟩ := exists_rootSL2_vSL_eq (K := L) hγr
  have hηK : η ∈ fixSubfield σm := sq_eq_one_fixed σm hη
  have hup : ∀ t : fixSubfield σm, z₀ * f₀ (uSL (ε • t)) * z₀⁻¹ =
      g' * pinnedX τ L γ (t : L) * g'⁻¹ := by
    intro t
    rw [hf₀, outer_map_uSL, hconjB, rootSL2_uSL_eq, map_zsmul, ← hε, hεε]
    rfl
  have hlow : ∀ t : fixSubfield σm, z₀ * f₀ (vSL (⟨η, hηK⟩ * t)) * z₀⁻¹ =
      g' * pinnedX τ L (-γ) (t : L) * g'⁻¹ := by
    intro t
    rw [hf₀, outer_map_vSL, hconjB, hv, map_mul]
    have e : η * (ιK ⟨η, hηK⟩ * ιK t) = (t : L) := by
      change η * (η * (t : L)) = t
      rw [← mul_assoc, hη, one_mul]
    rw [e]
  have hCommRoots :
      (∀ c, Commute z (g' * pinnedX τ L γ c * g'⁻¹)) ∧
      (∀ c, Commute z (g' * pinnedX τ L (-γ) c * g'⁻¹)) := by
    rcases hCase with hq3 | ⟨hzF, hzNall, f, hpin, hQ3⟩
    ·
      have hU := outer_commute_conj_pinnedX_of_prod S hτ hq3 hsm hKcard' hQ4m ks hnd h0 hksl g' hγr
        z fun t => by
          have h := hzN (uSL (ε • t))
          rw [hnorm, show (fun N => iterHom S.D.step N (z₀ * f₀ (uSL (ε • t)) * z₀⁻¹)) =
            fun N => iterHom S.D.step N (g' * pinnedX τ L γ (t : L) * g'⁻¹) from
              funext fun N => by rw [hup]] at h
          exact h
      have hL := outer_commute_conj_pinnedX_of_prod S hτ hq3 hsm hKcard' hQ4m ks hnd h0 hksl g'
        (IsRoot.neg hγr) z fun t => by
          have h := hzN (vSL (⟨η, hηK⟩ * t))
          rw [hnorm, show (fun N => iterHom S.D.step N (z₀ * f₀ (vSL (⟨η, hηK⟩ * t)) * z₀⁻¹)) =
            fun N => iterHom S.D.step N (g' * pinnedX τ L (-γ) (t : L) * g'⁻¹) from
              funext fun N => by rw [hlow]] at h
          exact h
      exact ⟨hU, hL⟩
    · have hthetaC : ∀ A, Commute z (z₀ * θ A * z₀⁻¹) := fun A => by
        have h := commute_component_fixed S hT i hs hmin z hzF hzNall hcomm
          hperf θ₁ hθ₁fix A
        rw [hθ₁] at h
        exact h
      have hthetaU : ∀ t : fixSubfield σm, Commute z
          (((List.range m).map fun j =>
            iterHom φ₁ j (rootSL2 τ L γ (conjSL P
              (Matrix.SpecialLinearGroup.map ιK (uSL (ε • t)))))).prod |>
            fun x => z₀ * x * z₀⁻¹) := by
        intro t
        have h := hthetaC (uSL (ε • t))
        rw [hθ] at h
        simpa only [← iterHom_eq_iterate] using h
      have hprodU : ∀ t : fixSubfield σm, Commute (z₀⁻¹ * z * z₀)
          (((List.range m).map fun j =>
            iterHom φ₁ j (rootSL2 τ L γ (conjSL P
              (Matrix.SpecialLinearGroup.map ιK (uSL (ε • t)))))).prod) := by
        intro t
        have h := (Commute.conj_iff (h := z₀⁻¹)).mpr (hthetaU t)
        simpa only [inv_inv, inv_mul_cancel_left, mul_inv_cancel_right, mul_assoc, inv_mul_cancel, mul_one] using h
      have huF : ∀ t : fixSubfield σm, rootSL2 τ L γ
          (conjSL P (Matrix.SpecialLinearGroup.map ιK (uSL (ε • t)))) =
          rootSL2 τ L γ P' * pinnedX τ L γ (t : L) * (rootSL2 τ L γ P')⁻¹ := by
        intro t
        rw [outer_map_uSL, hP', map_mul, map_mul, map_inv, rootSL2_uSL_eq,
          map_zsmul, ← hε, hεε]
        rfl
      have hU0 := commute_conj_pinnedX_of_outer_prod hτ hpin hQ3 ιK hm
        (by simpa only [pow_mul] using hKcard') (by simpa only [pow_mul] using hQ4m) (rootSL2 τ L γ P') (z₀⁻¹ * z * z₀) hγr
        (fun t => by have h := hprodU t; simp only [huF] at h; exact h)
      have hU : ∀ c, Commute z (g' * pinnedX τ L γ c * g'⁻¹) := by
        intro c
        have h := (Commute.conj_iff (h := z₀)).mpr (hU0 c)
        simpa [hg', mul_assoc] using h
      have hprodL : ∀ t : fixSubfield σm, Commute (z₀⁻¹ * z * z₀)
          (((List.range m).map fun j => iterHom φ₁ j (rootSL2 τ L γ
            (conjSL P (Matrix.SpecialLinearGroup.map ιK (vSL (⟨η, hηK⟩ * t)))))).prod) := by
        intro t
        have h := hthetaC (vSL (⟨η, hηK⟩ * t))
        rw [hθ] at h
        have h' := (Commute.conj_iff (h := z₀⁻¹)).mpr h
        simpa [mul_assoc, ← iterHom_eq_iterate] using h'
      have hvF : ∀ t : fixSubfield σm, rootSL2 τ L γ
          (conjSL P (Matrix.SpecialLinearGroup.map ιK (vSL (⟨η, hηK⟩ * t)))) =
          rootSL2 τ L γ P' * pinnedX τ L (-γ) (t : L) * (rootSL2 τ L γ P')⁻¹ := by
        intro t
        rw [outer_map_vSL, hP', map_mul, map_mul, map_inv, hv, map_mul]
        have e : η * (ιK ⟨η, hηK⟩ * ιK t) = (t : L) := by
          change η * (η * (t : L)) = t
          rw [← mul_assoc, hη, one_mul]
        rw [e]
      have hL0 := commute_conj_pinnedX_of_outer_prod hτ hpin hQ3 ιK hm
        (by simpa only [pow_mul] using hKcard') (by simpa only [pow_mul] using hQ4m) (rootSL2 τ L γ P') (z₀⁻¹ * z * z₀) (IsRoot.neg hγr)
        (fun t => by have h := hprodL t; simp only [hvF] at h; exact h)
      have hL : ∀ c, Commute z (g' * pinnedX τ L (-γ) c * g'⁻¹) := by
        intro c
        have h := (Commute.conj_iff (h := z₀)).mpr (hL0 c)
        simpa [hg', mul_assoc] using h
      exact ⟨hU, hL⟩
  obtain ⟨hU, hL⟩ := hCommRoots
  have hall : ∀ B : SL2 L, Commute z (g' * rootSL2 τ L γ B * g'⁻¹) := by
    intro B
    have hB : B ∈ Subgroup.closure (Set.range (sl2Upper L) ∪ Set.range (sl2Lower L)) := by
      rw [sl2_closure_upper_lower]
      exact Subgroup.mem_top B
    induction hB using Subgroup.closure_induction with
    | mem B hB =>
      rcases hB with ⟨t, rfl⟩ | ⟨t, rfl⟩
      · change Commute z (g' * rootSL2 τ L γ (uSL t) * g'⁻¹)
        rw [rootSL2_uSL_eq]
        exact hU _
      · change Commute z (g' * rootSL2 τ L γ (vSL t) * g'⁻¹)
        rw [hv]
        exact hL _
    | one => simp
    | mul B C _ _ hB hC =>
      rw [map_mul, show g' * (rootSL2 τ L γ B * rootSL2 τ L γ C) * g'⁻¹ =
        (g' * rootSL2 τ L γ B * g'⁻¹) * (g' * rootSL2 τ L γ C * g'⁻¹) by group]
      exact hB.mul_right hC
    | inv B _ hB =>
      rw [map_inv, show g' * (rootSL2 τ L γ B)⁻¹ * g'⁻¹ = (g' * rootSL2 τ L γ B * g'⁻¹)⁻¹ by
        group]
      exact hB.inv_right
  intro B
  have h := hall (P'⁻¹ * B * P')
  have e : g' * rootSL2 τ L γ (P'⁻¹ * B * P') * g'⁻¹ = z₀ * rootSL2 τ L γ B * z₀⁻¹ := by
    rw [map_mul, map_mul, map_inv, hg']
    group
  rwa [e] at h

end Norm

end CFSG.HardMathSupport.Timmesfeld.LangTorus
