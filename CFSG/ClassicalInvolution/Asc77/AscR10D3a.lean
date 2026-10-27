module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Asc77.AscT3TypedClass
public import CFSG.ClassicalInvolution.AschTight.Sec6GenAPI
public import CFSG.ClassicalInvolution.Uniform.UHypOmegaGen

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Steinberg CFSG.LieType.BorelTits
open CFSG.ClassicalInvolution.Models (suMat)
open scoped MatrixGroups commutatorElement

section Central

theorem commutatorElement_mul_central {G : Type} [Group G] {a b k₁ k₂ : G}
    (h₁ : k₁ ∈ Subgroup.center G) (h₂ : k₂ ∈ Subgroup.center G) :
    ⁅k₁ * a, k₂ * b⁆ = ⁅a, b⁆ := by
  have e1 := Subgroup.mem_center_iff.mp h₁
  have e2 := Subgroup.mem_center_iff.mp h₂
  simp only [commutatorElement_def, mul_inv_rev]
  calc k₁ * a * (k₂ * b) * (a⁻¹ * k₁⁻¹) * (b⁻¹ * k₂⁻¹)
      = k₁ * (a * k₂) * b * a⁻¹ * k₁⁻¹ * b⁻¹ * k₂⁻¹ := by group
    _ = k₁ * (k₂ * a) * b * a⁻¹ * k₁⁻¹ * b⁻¹ * k₂⁻¹ := by rw [e2 a]
    _ = (k₁ * k₂) * (a * b * a⁻¹) * k₁⁻¹ * b⁻¹ * k₂⁻¹ := by group
    _ = (k₁ * k₂) * (a * b * a⁻¹ * k₁⁻¹) * b⁻¹ * k₂⁻¹ := by group
    _ = (k₁ * k₂) * (k₁⁻¹ * (a * b * a⁻¹)) * b⁻¹ * k₂⁻¹ := by
        have : a * b * a⁻¹ * k₁⁻¹ = k₁⁻¹ * (a * b * a⁻¹) := by
          have := e1 (a * b * a⁻¹)
          calc a * b * a⁻¹ * k₁⁻¹ = k₁⁻¹ * (k₁ * (a * b * a⁻¹)) * k₁⁻¹ := by group
            _ = k₁⁻¹ * ((a * b * a⁻¹) * k₁) * k₁⁻¹ := by rw [← this]
            _ = k₁⁻¹ * (a * b * a⁻¹) := by group
        rw [this]
    _ = (k₁ * k₂ * k₁⁻¹) * (a * b * a⁻¹) * b⁻¹ * k₂⁻¹ := by group
    _ = (k₂) * (a * b * a⁻¹) * b⁻¹ * k₂⁻¹ := by
        congr 3
        calc k₁ * k₂ * k₁⁻¹ = k₁ * (k₂ * k₁⁻¹) := by group
          _ = k₁ * (k₁⁻¹ * k₂) := by rw [← (Subgroup.mem_center_iff.mp
                ((Subgroup.center G).inv_mem h₁) k₂)]
          _ = k₂ := by group
    _ = a * b * a⁻¹ * b⁻¹ := by
        have e3 := e2 (a * b * a⁻¹ * b⁻¹)
        calc k₂ * (a * b * a⁻¹) * b⁻¹ * k₂⁻¹ = k₂ * (a * b * a⁻¹ * b⁻¹) * k₂⁻¹ := by group
          _ = (a * b * a⁻¹ * b⁻¹) * k₂ * k₂⁻¹ := by rw [← e3]
          _ = a * b * a⁻¹ * b⁻¹ := by group

theorem conj_eq_of_normalizes_image {M X : Type} [Group M] [Group X] (ψ : M →* X)
    (hker : ψ.ker ≤ Subgroup.center M) {R : Subgroup M}
    (hinj : ∀ r ∈ R, ∀ s ∈ R, ψ r = ψ s → r = s) {x y cR c : M} (hx : x ∈ R) (hy : y ∈ R)
    (hcR : ⁅x, y⁆ = cR) (hN : ∀ r ∈ R, ∃ r' ∈ R, ψ r' = ψ c * ψ r * (ψ c)⁻¹)
    (hz : ψ c * ψ cR * (ψ c)⁻¹ = ψ cR) : c * cR * c⁻¹ = cR := by
  have hcR_mem : cR ∈ R := by
    rw [← hcR, commutatorElement_def]
    exact R.mul_mem (R.mul_mem (R.mul_mem hx hy) (R.inv_mem hx)) (R.inv_mem hy)
  have key : ∀ r ∈ R, ∃ r' ∈ R, ψ r' = ψ c * ψ r * (ψ c)⁻¹ ∧
      ∃ κ ∈ Subgroup.center M, c * r * c⁻¹ = κ * r' := by
    intro r hr
    obtain ⟨r', hr', hψ⟩ := hN r hr
    refine ⟨r', hr', hψ, c * r * c⁻¹ * r'⁻¹, hker ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hψ]
    group
  obtain ⟨x', hx', hψx, κ₁, hκ₁, hxe⟩ := key x hx
  obtain ⟨y', hy', hψy, κ₂, hκ₂, hye⟩ := key y hy
  have h1 : c * cR * c⁻¹ = ⁅c * x * c⁻¹, c * y * c⁻¹⁆ := by
    have := map_commutatorElement (MulAut.conj c).toMonoidHom x y
    simpa [MulAut.conj_apply, hcR] using this
  rw [h1, hxe, hye, commutatorElement_mul_central hκ₁ hκ₂]
  have hmem : ⁅x', y'⁆ ∈ R := by
    rw [commutatorElement_def]
    exact R.mul_mem (R.mul_mem (R.mul_mem hx' hy') (R.inv_mem hx')) (R.inv_mem hy')
  apply hinj _ hmem _ hcR_mem
  have e1 : ψ ⁅x', y'⁆ = ⁅ψ x', ψ y'⁆ := map_commutatorElement ψ x' y'
  have e2 : ψ cR = ⁅ψ x, ψ y⁆ := by rw [← hcR, map_commutatorElement]
  rw [e1, hψx, hψy]
  have e3 : ⁅ψ c * ψ x * (ψ c)⁻¹, ψ c * ψ y * (ψ c)⁻¹⁆ = ψ c * ⁅ψ x, ψ y⁆ * (ψ c)⁻¹ := by
    have := map_commutatorElement (MulAut.conj (ψ c)) (ψ x) (ψ y)
    simp only [MulAut.conj_apply] at this
    exact this.symm
  rw [e3, ← e2, hz]

theorem neg_one_eq_commutator_sl2 {F : Type} [Field F] [Finite F] (hF : Nat.card F = 3) :
    ∃ A B : SL(2, F), ⁅A, B⁆ = (-1 : SL(2, F)) := by
  have h3 : (3 : F) = 0 := by
    have h : Nat.card F • (1 : F) = 0 := card_nsmul_eq_zero'
    rw [hF] at h
    simpa using h
  obtain ⟨A, hA⟩ : ∃ A : SL(2, F), (A : Matrix (Fin 2) (Fin 2) F) = !![0, -1; 1, 0] :=
    ⟨⟨_, by simp [Matrix.det_fin_two]⟩, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : SL(2, F), (B : Matrix (Fin 2) (Fin 2) F) = !![1, 1; 1, -1] :=
    ⟨⟨_, by simp [Matrix.det_fin_two]; linear_combination (-1 : F) * h3⟩, rfl⟩
  have hAi : ((A⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; -1, 0] := by
    rw [Matrix.SpecialLinearGroup.coe_inv, hA, Matrix.adjugate_fin_two]
    simp
  have hBi : ((B⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![-1, -1; -1, 1] := by
    rw [Matrix.SpecialLinearGroup.coe_inv, hB, Matrix.adjugate_fin_two]
    simp
  refine ⟨A, B, ?_⟩
  apply Subtype.ext
  rw [commutatorElement_def]
  simp only [Matrix.SpecialLinearGroup.coe_mul, hA, hB, hAi, hBi, Matrix.SpecialLinearGroup.coe_neg,
    Matrix.SpecialLinearGroup.coe_one, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> linear_combination (1 : F) * h3

end Central

section Kernel

theorem comp_injective_of_center_bot {G M X : Type} [Group G] [Group M] [Group X] (θ : G →* M)
    (ψ : M →* X) (hθ : θ.ker ≤ Subgroup.center G) (hψ : ψ.ker ≤ Subgroup.center M)
    (hZ : Subgroup.center G = ⊥) : Function.Injective (ψ.comp θ) := by
  rw [injective_iff_map_eq_one]
  intro c hc
  have hc' : θ c ∈ Subgroup.center M := hψ (by simpa using hc)
  have hcomm : ∀ h : G, c * h = h * c := by
    intro h
    have h1 : θ (c * h * c⁻¹ * h⁻¹) = 1 := by
      have := Subgroup.mem_center_iff.mp hc' (θ h)
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      calc θ c * θ h * (θ c)⁻¹ * (θ h)⁻¹ = (θ h * θ c) * (θ c)⁻¹ * (θ h)⁻¹ := by rw [this]
        _ = 1 := by group
    have h2 : c * h * c⁻¹ * h⁻¹ ∈ Subgroup.center G := hθ (MonoidHom.mem_ker.mpr h1)
    rw [hZ, Subgroup.mem_bot] at h2
    calc c * h = c * h * c⁻¹ * h⁻¹ * h * c := by group
      _ = h * c := by rw [h2]; group
  have hcz : c ∈ Subgroup.center G := Subgroup.mem_center_iff.mpr fun h => (hcomm h).symm
  rw [hZ, Subgroup.mem_bot] at hcz
  exact hcz

theorem center_sl3_eq_bot {F : Type} [Field F] [Finite F] (hF : Nat.card F = 3) :
    Subgroup.center SL(3, F) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  rw [Matrix.SpecialLinearGroup.mem_center_iff] at hA
  obtain ⟨r, hr, hAr⟩ := hA
  rw [Subgroup.mem_bot]
  have : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = 3 := by rw [← Nat.card_eq_fintype_card]; exact hF
  have h1 : r ^ 3 = r := by rw [← hcard]; exact FiniteField.pow_card r
  have hr3 : r ^ Fintype.card (Fin 3) = 1 := hr
  simp only [Fintype.card_fin] at hr3
  have hr1 : r = 1 := by rw [← h1]; exact hr3
  subst hr1
  apply Subtype.ext
  rw [← hAr]
  simp

theorem center_su3_eq_bot {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
    (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f = 3) :
    Subgroup.center (Su K p f 3) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  obtain ⟨u, hu⟩ := exists_scalar_of_mem_center
    (CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hK) (le_refl 3) hz
  have hdet : ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := z.2.1
  rw [hu] at hdet
  simp [Matrix.scalar_apply, Matrix.det_diagonal] at hdet
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 9 := by
    rw [← Nat.card_eq_fintype_card, hK, hq]
    norm_num
  have h1 : (u : K) ^ 9 = u := by rw [← hcard]; exact FiniteField.pow_card (u : K)
  have h3 : (u : K) ^ 9 = 1 := by
    calc (u : K) ^ 9 = ((u : K) ^ 3) ^ 3 := by ring
      _ = 1 := by rw [hdet]; simp
  have hu1 : (u : K) = 1 := by rw [← h1, h3]
  have h2 : ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [hu, hu1]; simp
  exact Subtype.ext (Units.ext h2)

end Kernel

section Centralizer

theorem linear_centralizer_comm_of_injective {F : Type} [Field F] [Finite F] (h2 : (2 : F) ≠ 0)
    {X : Type} [Group X] (θ : SL(3, F) →* X) (hinj : Function.Injective θ) {x y : X}
    (hx : x ∈ θ.range) (hy : y ∈ θ.range)
    (hxc : ∀ s ∈ WeakCT.B12 F, x * θ s = θ s * x) (hyc : ∀ s ∈ WeakCT.B12 F, y * θ s = θ s * y) :
    x * y = y * x := by
  obtain ⟨g, rfl⟩ := hx
  obtain ⟨g', rfl⟩ := hy
  have key : ∀ g₀ : SL(3, F), (∀ s ∈ WeakCT.B12 F, θ g₀ * θ s = θ s * θ g₀) →
      (g₀ : Matrix (Fin 3) (Fin 3) F) * embPair 2 (Phan.rotMat : Matrix (Fin 2) (Fin 2) F) =
        embPair 2 Phan.rotMat * (g₀ : Matrix (Fin 3) (Fin 3) F) := by
    intro g₀ hc
    have hs := hc (WeakCT.blockSL F 3 2 0 (by omega) WeakCT.rotSL) ⟨WeakCT.rotSL, rfl⟩
    have e : g₀ * WeakCT.blockSL F 3 2 0 (by omega) WeakCT.rotSL =
        WeakCT.blockSL F 3 2 0 (by omega) WeakCT.rotSL * g₀ :=
      hinj (by rw [map_mul, map_mul]; exact hs)
    have e2 := congrArg (fun z : SL(3, F) => (z : Matrix (Fin 3) (Fin 3) F)) e
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_blockSL_zero] at e2
    exact e2
  have hmat := commute_of_commute_embPair_rot h2 (key g hxc) (key g' hyc)
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (by simpa using hmat)

theorem unitary_centralizer_comm_of_injective {K : Type} [Field K] [Finite K] {p f : ℕ}
    [Fact p.Prime] [CharP K p] (h2 : (2 : K) ≠ 0) {X : Type} [Group X]
    (θ : Su K p f 3 →* X) (hinj : Function.Injective θ) {x y : X}
    (hx : x ∈ θ.range) (hy : y ∈ θ.range)
    (hxc : ∀ s ∈ B12 K p f, x * θ s = θ s * x) (hyc : ∀ s ∈ B12 K p f, y * θ s = θ s * y) :
    x * y = y * x := by
  obtain ⟨g, rfl⟩ := hx
  obtain ⟨g', rfl⟩ := hy
  have key : ∀ g₀ : Su K p f 3, (∀ s ∈ B12 K p f, θ g₀ * θ s = θ s * θ g₀) →
      suMat g₀ * embPair 2 (Phan.rotMat : Matrix (Fin 2) (Fin 2) K) =
        embPair 2 Phan.rotMat * suMat g₀ := by
    intro g₀ hc
    have hs := hc (embSUid (unitaryInvolution K p f) 2 (Phan.rotSU (unitaryInvolution K p f)))
      ⟨_, rfl⟩
    have e : g₀ * embSUid (unitaryInvolution K p f) 2 (Phan.rotSU (unitaryInvolution K p f)) =
        embSUid (unitaryInvolution K p f) 2 (Phan.rotSU (unitaryInvolution K p f)) * g₀ :=
      hinj (by rw [map_mul, map_mul]; exact hs)
    have e2 := congrArg suMat e
    simp only [Models.suMat_mul] at e2
    exact e2
  have hmat := commute_of_commute_embPair_rot h2 (key g hxc) (key g' hyc)
  rw [← map_mul, ← map_mul]
  congr 1
  exact Models.suMat_injective (by rw [Models.suMat_mul, Models.suMat_mul]; exact hmat)

end Centralizer

section Inj

theorem injOn_of_natCard_map {M X : Type} [Group M] [Group X] [Finite M] (ψ : M →* X)
    {R : Subgroup M} (h : Nat.card R = Nat.card (R.map ψ)) :
    ∀ r ∈ R, ∀ s ∈ R, ψ r = ψ s → r = s := by
  have hsurj : Function.Surjective (ψ.subgroupMap R) := ψ.subgroupMap_surjective R
  have hbij : Function.Bijective (ψ.subgroupMap R) :=
    hsurj.bijective_of_nat_card_le h.le
  intro r hr s hs hrs
  have := hbij.1 (a₁ := ⟨r, hr⟩) (a₂ := ⟨s, hs⟩) (Subtype.ext hrs)
  exact congrArg Subtype.val this

end Inj

section Twin

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem not_commutative_of_classical3 {L : Subgroup X} {z : X} (h : Q3.IsClassicalMember3 L z)
    (hcomm : ∀ a b : L, a * b = b * a) : False := by
  obtain ⟨e⟩ := h.nonempty_equiv
  apply Q3.sl2Three_not_comm (fun a b => ?_)
  obtain ⟨a', ha'⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore L) (e.symm a)
  obtain ⟨b', hb'⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore L) (e.symm b)
  apply e.symm.injective
  rw [map_mul, map_mul, ← ha', ← hb', ← map_mul, ← map_mul, hcomm a' b']

theorem oddCoreOf_eq_bot_of_card (hΩ : HypOmegaModU (.sl2 3 1) Φ)
    (hcard : ∀ L ∈ Φ, Nat.card L = 24) {L : Subgroup X} (hL : L ∈ Φ) : oddCoreOf L = ⊥ := by
  obtain ⟨z, hz⟩ := hΩ.classical L hL
  obtain ⟨e⟩ := (hz.toQ3 (by norm_num)).nonempty_equiv
  have hq : Nat.card (↥L ⧸ classicalInvolutionOddCore ↥L) = 24 := by
    rw [Nat.card_congr e.toEquiv]
    exact natCard_sl2Three
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (classicalInvolutionOddCore ↥L)
  rw [hq, hcard L hL] at h1
  have h2 : Nat.card (classicalInvolutionOddCore ↥L) = 1 := by omega
  have hO : classicalInvolutionOddCore ↥L = ⊥ := Subgroup.eq_bot_of_card_eq _ h2
  unfold oddCoreOf
  rw [hO, Subgroup.map_bot]

theorem quotViol_false_of_centralizer_comm3 (hΩ : HypOmegaModU (.sl2 3 1) Φ)
    (hcard : ∀ L ∈ Φ, Nat.card L = 24) {K J : Subgroup X} {z j a : X}
    (h : QuotViol Φ K J z j a) {W : Subgroup X} (hKW : K ≤ W) (hJW : J ≤ W)
    (hcomm : ∀ x ∈ W, ∀ y ∈ W, (∀ u ∈ K, x * u = u * x) → (∀ u ∈ K, y * u = u * y) →
      x * y = y * x) : False := by
  have hΩg : HypOmegaGen Φ := hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) hΩ
  set K' : Subgroup X := conjSub a J with hK'
  have hK'Φ : K' ∈ Φ := hΩ.conjInvariant a J h.mem_right
  have hzK' : IsUniqueInvolution K' z := by
    have := h.hj.conj a
    rwa [h.haj] at this
  have haW : a ∈ W := (sup_le hKW hJW) (T3Typed.mem_sup_of_mem_pairNormalizers h.ha)
  have hK'W : K' ≤ W := by
    intro x hx
    rw [hK', mem_conjSub_iff] at hx
    have : a * (a⁻¹ * x * a) * a⁻¹ ∈ W :=
      W.mul_mem (W.mul_mem haW (hJW hx)) (W.inv_mem haW)
    simpa [mul_assoc] using this
  have hKK' : K ≠ K' := fun e => h.hne e.symm
  have hc := Sec6Gen.comm_le_oddCore_of_twin hΩg h.mem_left hK'Φ hKK' h.hz hzK'
  rw [oddCoreOf_eq_bot_of_card hΩ hcard h.mem_left, bot_inf_eq, le_bot_iff] at hc
  have hcK : ∀ x ∈ K', ∀ u ∈ K, x * u = u * x := by
    intro x hx u hu
    have hmem : ⁅u, x⁆ ∈ ⁅K, K'⁆ := Subgroup.commutator_mem_commutator hu hx
    rw [hc, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hmem.symm
  obtain ⟨zz, hzz⟩ := hΩ.classical K' hK'Φ
  refine not_commutative_of_classical3 (hzz.toQ3 (by norm_num)) fun x y => ?_
  exact Subtype.ext (hcomm x (hK'W x.2) y (hK'W y.2) (hcK x x.2) (hcK y y.2))

end Twin

end CFSG.ClassicalInvolution.Asc77.T3CII
