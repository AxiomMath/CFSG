module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2E6RelayBlock
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2TwistedE6RelayOut
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2E6ChainTwLong

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear mem_blockSpecialLinear pairEmbed)
open CFSG.SeitzReduction.SymplecticPilot (zThreeSL)
open CFSG.LieType.Steinberg.TwistedE6 (fixedGroup)
open CFSG.LieType.Universal.Unitary (antidiag)
open CFSG.Timmesfeld.LieEmbed (c3ToF4)
open CFSG.LieType.Ree (ReeTag)
open CFSG.Assembly.LowTwoRank (StatedSp)
open scoped MatrixGroups

local instance f4PilotQ2TwistedE6RelayBlockNeZeroRankF4 : NeZero Tag.F4.rank := ⟨by decide⟩

section Matrix

variable {F : Type} [Field F] {n : ℕ}

theorem relayTw_eq_one_of_commute [Finite F] (hF : Nat.card F = 4) {I : Finset (Fin n)}
    (hI : I.card = 4) {x : SpecialLinearGroup (Fin n) F} (hx : x ∈ blockSpecialLinear I)
    {i i' j j' : Fin n} (hii : i ≠ i') (hjj : j ≠ j') (hij : i ≠ j) (hj'i' : j' ≠ i')
    (hij' : i ≠ j') (hcov : ∀ y ∈ I, y = i ∨ y = i' ∨ y = j ∨ y = j')
    (h1 : x * SpecialLinearGroup.transvection hii 1 = SpecialLinearGroup.transvection hii 1 * x)
    (h2 : x * SpecialLinearGroup.transvection hii.symm 1 =
      SpecialLinearGroup.transvection hii.symm 1 * x)
    (h3 : x * SpecialLinearGroup.transvection hjj 1 = SpecialLinearGroup.transvection hjj 1 * x)
    (h4 : x * SpecialLinearGroup.transvection hjj.symm 1 =
      SpecialLinearGroup.transvection hjj.symm 1 * x) {d : F}
    (h5 : x * (SpecialLinearGroup.transvection hij 1 * SpecialLinearGroup.transvection hj'i' d) =
      (SpecialLinearGroup.transvection hij 1 * SpecialLinearGroup.transvection hj'i' d) * x) :
    x = 1 := by
  obtain ⟨c1, d1⟩ := relay_col_of_commute_transvection hii h1
  obtain ⟨c2, -⟩ := relay_col_of_commute_transvection hii.symm h2
  obtain ⟨c3, d3⟩ := relay_col_of_commute_transvection hjj h3
  obtain ⟨c4, -⟩ := relay_col_of_commute_transvection hjj.symm h4
  have hx' : ∀ p q, (p ∉ I ∨ q ∉ I) →
      (x : Matrix (Fin n) (Fin n) F) p q = (1 : Matrix (Fin n) (Fin n) F) p q := hx
  have h5' : ((x : Matrix (Fin n) (Fin n) F) *
      ((SpecialLinearGroup.transvection hij (1 : F) : Matrix (Fin n) (Fin n) F) *
        (SpecialLinearGroup.transvection hj'i' d : Matrix (Fin n) (Fin n) F))) i j =
      (((SpecialLinearGroup.transvection hij (1 : F) : Matrix (Fin n) (Fin n) F) *
        (SpecialLinearGroup.transvection hj'i' d : Matrix (Fin n) (Fin n) F)) *
          (x : Matrix (Fin n) (Fin n) F)) i j :=
    congrArg (fun y : SpecialLinearGroup (Fin n) F => (y : Matrix (Fin n) (Fin n) F) i j) h5
  have hdet0 : (x : Matrix (Fin n) (Fin n) F).det = 1 := x.2
  set X : Matrix (Fin n) (Fin n) F := (x : Matrix (Fin n) (Fin n) F) with hX
  have hcol : ∀ q p, p ≠ q → X p q = 0 := by
    intro q p hpq
    by_cases hq : q ∈ I
    · rcases hcov q hq with rfl | rfl | rfl | rfl
      · exact c1 p hpq
      · exact c2 p hpq
      · exact c3 p hpq
      · exact c4 p hpq
    · rw [hx' p q (Or.inr hq), one_apply_ne hpq]
  have hrow : ∀ (A : Matrix (Fin n) (Fin n) F) (p q : Fin n), (X * A) p q = X p p * A p q := by
    intro A p q
    rw [Matrix.mul_apply, Finset.sum_eq_single p
      (fun r _ hr => by rw [hcol r p (Ne.symm hr), zero_mul])
      (fun h => absurd (Finset.mem_univ p) h)]
  have hcolm : ∀ (A : Matrix (Fin n) (Fin n) F) (p q : Fin n), (A * X) p q = A p q * X q q := by
    intro A p q
    rw [Matrix.mul_apply, Finset.sum_eq_single q
      (fun r _ hr => by rw [hcol q r hr, mul_zero])
      (fun h => absurd (Finset.mem_univ q) h)]
  set Sm : Matrix (Fin n) (Fin n) F :=
    (SpecialLinearGroup.transvection hij (1 : F) : Matrix (Fin n) (Fin n) F) *
      (SpecialLinearGroup.transvection hj'i' d : Matrix (Fin n) (Fin n) F) with hSm
  have hSij : Sm i j = 1 := by
    rw [hSm, SpecialLinearGroup.transvection_coe,
      SpecialLinearGroup.transvection_coe, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
      Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, single_mul_single_of_ne (h := hjj)]
    simp [Matrix.add_apply, one_apply_ne hij, Ne.symm hij']
  have hlm : X i i = X j j := by
    have e5 := h5'
    rw [hrow, hcolm, hSij, mul_one, one_mul] at e5
    exact e5
  set lam := X i i with hlam
  have hdiagI : ∀ p ∈ I, X p p = lam := by
    intro p hp
    rcases hcov p hp with rfl | rfl | rfl | rfl
    · rfl
    · exact d1.symm
    · exact hlm.symm
    · rw [← d3, ← hlm]
  have hdiagC : ∀ p, p ∉ I → X p p = 1 := fun p hp => by
    rw [hx' p p (Or.inl hp), one_apply_eq]
  have hdiag : X = diagonal (fun p => X p p) := by
    ext p q
    by_cases hpq : p = q
    · subst hpq
      rw [diagonal_apply_eq]
    · rw [hcol q p hpq, diagonal_apply_ne _ hpq]
  have hdet : lam ^ 4 = 1 := by
    have h0 : X.det = 1 := hdet0
    rw [hdiag, det_diagonal, ← Finset.prod_mul_prod_compl I,
      Finset.prod_congr rfl hdiagI, Finset.prod_const, hI,
      Finset.prod_eq_one (fun p hp => hdiagC p (Finset.mem_compl.1 hp)), mul_one] at h0
    exact h0
  have hlam0 : lam ≠ 0 := fun h0 => by
    rw [h0, zero_pow (by norm_num)] at hdet
    exact zero_ne_one hdet
  have hlam3 : lam ^ 3 = 1 := by
    have h3 := pow_card_eq_one' (G := Fˣ) (x := Units.mk0 lam hlam0)
    rw [Nat.card_units, hF] at h3
    have := congrArg Units.val h3
    simpa using this
  have hlam1 : lam = 1 := by
    calc lam = lam ^ 4 * (lam ^ 3)⁻¹ := by field_simp
      _ = 1 := by rw [hdet, hlam3, inv_one, mul_one]
  apply Subtype.ext
  change X = 1
  rw [hdiag]
  ext p q
  by_cases hpq : p = q
  · subst hpq
    rw [diagonal_apply_eq, one_apply_eq]
    by_cases hp : p ∈ I
    · rw [hdiagI p hp, hlam1]
    · exact hdiagC p hp
  · rw [diagonal_apply_ne _ hpq, one_apply_ne hpq]

end Matrix

section Setting


variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} (h : UnitaryFieldData 2 f F)
  {G : Type} [Group G] [Finite G]

omit [Finite F] [CharP F 2] [Finite G] in
theorem barSU6_mem_relayTwBlock {I : Finset (Fin 6)} {g : uGroup6 h}
    (hg : g ∈ relayTwBlock h I) : barSU6 h g ∈ relayTwBlock h I := by
  rw [mem_relayTwBlock] at hg ⊢
  intro p q hpq
  rw [coe_barSU6, Matrix.map_apply, hg p q hpq]
  by_cases hpq' : p = q
  · subst hpq'
    rw [one_apply_eq, map_one]
  · rw [one_apply_ne hpq', map_zero]

theorem chainSU6_conj_eq_barSU6 {t : G}
    {ΦX : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes →* G}
    (hconj : ∀ x y : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes,
      (y : fixedGroup F h.barEquiv.toRingHom) = sigmaHat h.barEquiv.toRingHom x →
        t * ΦX x * t⁻¹ = ΦX y)
    (g : uGroup6 h) : t * chainSU6 h ΦX g * t⁻¹ = chainSU6 h ΦX (barSU6 h g) := by
  rw [chainSU6_apply, chainSU6_apply]
  apply hconj
  rw [coe_twParamEquiv, coe_twParamEquiv, sigmaHat_twParamHom]

theorem chainSU6_injOn_relayTwBlock
    {ΦX : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes →* G}
    (hker : ΦX.ker ≤ center (twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes))
    {I : Finset (Fin 6)} {a : Fin 6} (ha : a ∉ I) {g g' : uGroup6 h}
    (hg : g ∈ relayTwBlock h I) (hg' : g' ∈ relayTwBlock h I)
    (e : chainSU6 h ΦX g = chainSU6 h ΦX g') : g = g' := by
  have hm : g * g'⁻¹ ∈ relayTwBlock h I := mul_mem hg (inv_mem hg')
  have hm1 : chainSU6 h ΦX (g * g'⁻¹) = 1 := by rw [map_mul, map_inv, e, mul_inv_cancel]
  have hc := mem_center_of_chainSU6_eq_one h hker hm1
  obtain ⟨c, -, -, hcg⟩ := center_gramSU_le_normOneScalars h (isPrimeFormGram_graphGram6 F)
    (by norm_num) (by omega) hc
  have haa := (mem_relayTwBlock h).1 hm a a (Or.inl ha)
  rw [hcg, GeneralLinearGroup.coe_scalar, one_apply_eq] at haa
  have hc1 : c = 1 := Units.ext (by simpa using haa)
  have h1 : g * g'⁻¹ = 1 := by
    apply Subtype.ext
    rw [hcg, hc1, map_one]
    rfl
  exact mul_inv_eq_one.1 h1

end Setting

section Edge


variable {F : Type} [Field F] [Finite F] [CharP F 2] (h : UnitaryFieldData 2 1 F)
  {K : Type} [Field K] [Finite K] [CharP K 2] {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem relayTw_mem_alignedSubgroup_of_edge {e : L ≃* adjointGroup .F4 K}
    {ε : h.fixedField ≃+* K} {t : G} (ht : t ∈ centralizer (L : Set G))
    {ΦX : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes →* G}
    {X₀ : Subgroup (adjointGroup .F4 K)}
    (hr : ΦX.range = centralizerPerfectCore (subgroupToG e X₀))
    (hker : ΦX.ker ≤ center (twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes))
    (hconj : ∀ x y : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes,
      (y : fixedGroup F h.barEquiv.toRingHom) = sigmaHat h.barEquiv.toRingHom x →
        t * ΦX x * t⁻¹ = ΦX y)
    (hn : IsLeviNormalizedU h ε e ΦX) {a b : Fin 6} (hab : a ≠ b)
    {β : Fin (Tag.rank .F4) → ℤ} {τ : Fin 3 → ℤ} (hτβ : c3ToF4 τ = β)
    (hτ : ∀ d : h.fixedField, gramSUToSL h _ (uEmbed6 h (Sp.x 3 h.fixedField τ d)) =
      SpecialLinearGroup.transvection hab (d : F))
    (hτ' : ∀ d : h.fixedField, gramSUToSL h _ (uEmbed6 h (Sp.x 3 h.fixedField (-τ) d)) =
      SpecialLinearGroup.transvection hab.symm (d : F))
    {σ : Fin 4 ⊕ Fin 2 ≃ Fin 6} {J' : Matrix (Fin 2) (Fin 2) F}
    (hJ : (blockSwapJ 6 3 : Matrix (Fin 6) (Fin 6) F) =
      reindex σ σ (fromBlocks (antidiag 4) 0 0 J'))
    (hl : ∀ i, σ (Sum.inl i) ∈ ({a, b} : Finset (Fin 6))ᶜ)
    (hr' : ∀ j, σ (Sum.inr j) ∉ ({a, b} : Finset (Fin 6))ᶜ)
    {i i' j j' : Fin 6} (hii : i ≠ i') (hjj : j ≠ j') (hij : i ≠ j) (hj'i' : j' ≠ i')
    (hij' : i ≠ j') (hcov : ∀ y ∈ ({a, b} : Finset (Fin 6))ᶜ, y = i ∨ y = i' ∨ y = j ∨ y = j')
    (hmi : i ∈ ({a, b} : Finset (Fin 6))ᶜ) (hmi' : i' ∈ ({a, b} : Finset (Fin 6))ᶜ)
    (hmj : j ∈ ({a, b} : Finset (Fin 6))ᶜ) (hmj' : j' ∈ ({a, b} : Finset (Fin 6))ᶜ)
    {s₁ s₂ s₃ s₄ s₅ : StatedSp 3 h.fixedField} {d : F}
    (hs₁ : gramSUToSL h _ (uEmbed6 h s₁) = SpecialLinearGroup.transvection hii 1)
    (hs₂ : gramSUToSL h _ (uEmbed6 h s₂) = SpecialLinearGroup.transvection hii.symm 1)
    (hs₃ : gramSUToSL h _ (uEmbed6 h s₃) = SpecialLinearGroup.transvection hjj 1)
    (hs₄ : gramSUToSL h _ (uEmbed6 h s₄) = SpecialLinearGroup.transvection hjj.symm 1)
    (hs₅ : gramSUToSL h _ (uEmbed6 h s₅) =
      SpecialLinearGroup.transvection hij 1 * SpecialLinearGroup.transvection hj'i' d)
    {g₀ : uGroup6 h} (hg₀ : g₀ ∈ relayTwBlock h ({a, b} : Finset (Fin 6))ᶜ)
    (hg₀' : barSU6 h g₀ ≠ g₀)
    {α' : relayTwBlock h ({a, b} : Finset (Fin 6))ᶜ →* G} (hα' : Function.Injective α')
    (hα'r : α'.range ≤
      centralizerPerfectCore (subgroupToG e X₀ ⊔ subgroupToG e (zpowers (chainZ K β))))
    (hα'S : ∀ x : relayTwBlock h ({a, b} : Finset (Fin 6))ᶜ,
      (x : uGroup6 h) ∈ ({uEmbed6 h s₁, uEmbed6 h s₂, uEmbed6 h s₃, uEmbed6 h s₄, uEmbed6 h s₅} :
        Set (uGroup6 h)) → α' x = chainSU6 h ΦX x)
    {M : Subgroup (uGroup6 h)} (hM : M ≤ relayTwBlock h ({a, b} : Finset (Fin 6))ᶜ)
    {S : Subgroup G} (hS : S ≤ M.map (chainSU6 h ΦX)) {v : adjointGroup .F4 K}
    (hv : ∀ x : relayTwBlock h ({a, b} : Finset (Fin 6))ᶜ, (x : uGroup6 h) ∈ M →
      Commute ((e.symm v : L) : G) (α' x)) :
    v ∈ alignedSubgroup e S := by
  have hF : Nat.card F = 4 := by rw [h.card]; norm_num
  set E := centralizerPerfectCore (subgroupToG e X₀ ⊔ subgroupToG e (zpowers (chainZ K β)))
    with hE
  set α : (relayTwBlock h ({a, b} : Finset (Fin 6))ᶜ) →* G :=
    (chainSU6 h ΦX).comp (relayTwBlock h ({a, b} : Finset (Fin 6))ᶜ).subtype with hαdef
  have haI : a ∉ ({a, b} : Finset (Fin 6))ᶜ := by
    rw [Finset.mem_compl, not_not]
    exact Finset.mem_insert_self a _
  have hαinj : Function.Injective α := fun x y hxy =>
    Subtype.ext (chainSU6_injOn_relayTwBlock h hker haI x.2 y.2 hxy)
  have : Finite (relayTwBlock h ({a, b} : Finset (Fin 6))ᶜ) := Finite.of_injective _ hαinj
  have hx : ∀ c : K, chainSU6 h ΦX (uEmbed6 h (Sp.x 3 h.fixedField τ (ε.symm c))) =
      ((e.symm (Adjoint.f4Par K β c) : L) : G) := by
    intro c
    rw [chainSU6_apply, hn, levi6Hom_x_alignTw, hτβ, ε.apply_symm_apply]
  have hx' : ∀ c : K, chainSU6 h ΦX (uEmbed6 h (Sp.x 3 h.fixedField (-τ) (ε.symm c))) =
      ((e.symm (Adjoint.f4Par K (-β) c) : L) : G) := by
    intro c
    rw [chainSU6_apply, hn, levi6Hom_x_alignTw, map_neg, hτβ, ε.apply_symm_apply]
  set c' := uEmbed6 h (Sp.x 3 h.fixedField τ 1 * Sp.x 3 h.fixedField (-τ) 1) with hc'def
  have hc' : gramSUToSL h _ c' = pairEmbed hab (zThreeSL (K := F)) := by
    rw [hc'def, map_mul, map_mul, hτ, hτ', OneMemClass.coe_one, pairEmbed_zThreeSL_eq]
  have hcZ : chainSU6 h ΦX c' ∈ subgroupToG e (zpowers (chainZ K β)) := by
    have e1 : chainSU6 h ΦX c' = ((e.symm (chainZ K β) : L) : G) := by
      rw [hc'def, map_mul, map_mul, show (1 : h.fixedField) = ε.symm 1 from (map_one _).symm,
        hx, hx', chainZ, map_mul, Subgroup.coe_mul]
    rw [e1]
    exact ⟨_, ⟨chainZ K β, mem_zpowers _, rfl⟩, rfl⟩
  have hEle : E ≤ α.range := by
    intro y hy
    obtain ⟨m, hm, hmB⟩ :=
      exists_chainSU6_eq_of_mem_centralizerPerfectCore h hr hker hab hc' hcZ y hy
    exact ⟨⟨m, hmB⟩, hm⟩
  have hcardE : Nat.card α.range ≤ Nat.card E := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hαinj).toEquiv,
      Nat.card_congr (MonoidHom.ofInjective hα').toEquiv]
    exact Subgroup.card_le_of_le hα'r
  have hαr : α.range = E := (Subgroup.eq_of_le_of_card_ge hEle hcardE).symm
  have χ : E ≃* (relayTwBlock h ({a, b} : Finset (Fin 6))ᶜ) :=
    (MulEquiv.subgroupCongr hαr.symm).trans (MonoidHom.ofInjective hαinj).symm
  have hOut2 : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer E) = 2 :=
    natCard_outer_of_mulEquiv_relayTwBlock h hJ hl hr' χ
  have hcard4 : ({a, b} : Finset (Fin 6))ᶜ.card = 4 := by
    rw [Finset.card_compl, Finset.card_pair hab, Fintype.card_fin]
  have hLmem : ∀ s : StatedSp 3 h.fixedField, chainSU6 h ΦX (uEmbed6 h s) ∈ L := by
    intro s
    rw [chainSU6_apply, hn, levi6Hom, MonoidHom.comp_apply, Subgroup.coe_subtype]
    exact SetLike.coe_mem _
  have hb1 : gramSUToSL h _ (uEmbed6 h s₁) ∈ blockSpecialLinear ({a, b} : Finset (Fin 6))ᶜ := by
    rw [hs₁]; exact LinearPilot.transvection_mem_blockSpecialLinear hii hmi hmi' 1
  have hb2 : gramSUToSL h _ (uEmbed6 h s₂) ∈ blockSpecialLinear ({a, b} : Finset (Fin 6))ᶜ := by
    rw [hs₂]; exact LinearPilot.transvection_mem_blockSpecialLinear hii.symm hmi' hmi 1
  have hb3 : gramSUToSL h _ (uEmbed6 h s₃) ∈ blockSpecialLinear ({a, b} : Finset (Fin 6))ᶜ := by
    rw [hs₃]; exact LinearPilot.transvection_mem_blockSpecialLinear hjj hmj hmj' 1
  have hb4 : gramSUToSL h _ (uEmbed6 h s₄) ∈ blockSpecialLinear ({a, b} : Finset (Fin 6))ᶜ := by
    rw [hs₄]; exact LinearPilot.transvection_mem_blockSpecialLinear hjj.symm hmj' hmj 1
  have hb5 : gramSUToSL h _ (uEmbed6 h s₅) ∈ blockSpecialLinear ({a, b} : Finset (Fin 6))ᶜ := by
    rw [hs₅]
    exact mul_mem (LinearPilot.transvection_mem_blockSpecialLinear hij hmi hmj 1)
      (LinearPilot.transvection_mem_blockSpecialLinear hj'i' hmj' hmi' d)
  set Γ : Set (relayTwBlock h ({a, b} : Finset (Fin 6))ᶜ) :=
    {⟨_, hb1⟩, ⟨_, hb2⟩, ⟨_, hb3⟩, ⟨_, hb4⟩, ⟨_, hb5⟩} with hΓ
  set S₀ : Subgroup G := (closure Γ).map α with hS₀
  have hS₀E : S₀ ≤ E := hαr ▸ Subgroup.map_le_range α _
  have hS₀L : S₀ ≤ L := by
    rw [hS₀, Subgroup.map_le_iff_le_comap, closure_le]
    intro x hx
    rw [hΓ] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> exact hLmem _
  have hC : ∀ x ∈ E, (∀ s ∈ S₀, x * s = s * x) → x = 1 := by
    intro x hx hcomm
    rw [← hαr] at hx
    obtain ⟨y, rfl⟩ := hx
    have key : ∀ (s : StatedSp 3 h.fixedField)
        (hsB : gramSUToSL h _ (uEmbed6 h s) ∈ blockSpecialLinear ({a, b} : Finset (Fin 6))ᶜ),
        (⟨uEmbed6 h s, hsB⟩ : (relayTwBlock h ({a, b} : Finset (Fin 6))ᶜ)) ∈ Γ →
          gramSUToSL h _ (y : uGroup6 h) * gramSUToSL h _ (uEmbed6 h s) =
            gramSUToSL h _ (uEmbed6 h s) * gramSUToSL h _ (y : uGroup6 h) := by
      intro s hsB hsΓ
      have hmem : α ⟨uEmbed6 h s, hsB⟩ ∈ S₀ := Subgroup.mem_map_of_mem α (subset_closure hsΓ)
      have h1 := hcomm _ hmem
      rw [← map_mul, ← map_mul] at h1
      have h2 := congrArg Subtype.val (hαinj h1)
      rw [← map_mul, ← map_mul]
      exact congrArg (gramSUToSL h _) h2
    have k1 := key s₁ hb1 (by rw [hΓ]; simp)
    have k2 := key s₂ hb2 (by rw [hΓ]; simp)
    have k3 := key s₃ hb3 (by rw [hΓ]; simp)
    have k4 := key s₄ hb4 (by rw [hΓ]; simp)
    have k5 := key s₅ hb5 (by rw [hΓ]; simp)
    rw [hs₁] at k1
    rw [hs₂] at k2
    rw [hs₃] at k3
    rw [hs₄] at k4
    rw [hs₅] at k5
    have hy1 : gramSUToSL h _ (y : uGroup6 h) = 1 :=
      relayTw_eq_one_of_commute hF hcard4 y.2 hii hjj hij hj'i' hij' hcov k1 k2 k3 k4 k5
    have hy : y = 1 := by
      apply Subtype.ext
      apply gramSUToSL_injective h _
      rw [hy1, OneMemClass.coe_one, map_one]
    rw [hy, map_one]
  have hagree : ∀ x : (relayTwBlock h ({a, b} : Finset (Fin 6))ᶜ), α x ∈ S₀ → α' x = α x := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hx
    have hyx' : y = x := hαinj hyx
    subst hyx'
    have hle : closure Γ ≤ MonoidHom.eqLocus α' α := by
      rw [closure_le]
      intro z hz
      show α' z = α z
      apply hα'S z
      rw [hΓ] at hz
      rcases hz with rfl | rfl | rfl | rfl | rfl <;> simp
    exact hle hy
  have hJL : subgroupToG e X₀ ⊔ subgroupToG e (zpowers (chainZ K β)) ≤ L :=
    sup_le (relay_subgroupToG_le e _) (relay_subgroupToG_le e _)
  have hJ1 : ∀ y ∈ subgroupToG e X₀ ⊔ subgroupToG e (zpowers (chainZ K β)), t * y = y * t :=
    fun y hy => (mem_centralizer_iff.1 ht y (hJL hy)).symm
  have hJ2 : ∀ y ∈ subgroupToG e X₀ ⊔ subgroupToG e (zpowers (chainZ K β)),
      t⁻¹ * y = y * t⁻¹ :=
    fun y hy => (mem_centralizer_iff.1 (inv_mem ht) y (hJL hy)).symm
  have htE : ∀ x ∈ E, t * x * t⁻¹ ∈ E := fun x hx => relay_conj_mem_centralizerPerfectCore hJ1 hx
  have htE' : ∀ x ∈ E, t⁻¹ * x * t ∈ E := fun x hx => by
    have h1 := relay_conj_mem_centralizerPerfectCore hJ2 hx
    rwa [inv_inv] at h1
  have htS : ∀ s ∈ S₀, t * s * t⁻¹ = s := fun s hs => by
    rw [← mem_centralizer_iff.1 ht s (hS₀L hs), mul_inv_cancel_right]
  have htm' : ∃ x ∈ E, t * x * t⁻¹ ≠ x := by
    refine ⟨chainSU6 h ΦX g₀, hαr ▸ ⟨⟨g₀, hg₀⟩, rfl⟩, ?_⟩
    rw [chainSU6_conj_eq_barSU6 h hconj]
    intro heq
    exact hg₀' (chainSU6_injOn_relayTwBlock h hker haI (barSU6_mem_relayTwBlock h hg₀) hg₀ heq)
  have hrig := eq_or_eq_conj_of_agree hS₀E hC
    (fun α₁ α₂ h₁ h₂ => relayTw_mul_inv_mem_inner hOut2 α₁ α₂ h₁ h₂) htE htE' htS htm'
    hαinj hα' hαr hα'r hagree
  have hvt : Commute ((e.symm v : L) : G) t := mem_centralizer_iff.1 ht _ (e.symm v).2
  rw [alignedSubgroup, Subgroup.mem_comap, mem_centralizer_iff]
  intro s hs
  obtain ⟨k, hkM, rfl⟩ := hS hs
  have hc := commute_of_eq_or_eq_conj hrig hvt (x := ⟨k, hM hkM⟩) (hv ⟨k, hM hkM⟩ hkM)
  exact hc.eq.symm

end Edge

end CFSG.SeitzReduction.F4Pilot
