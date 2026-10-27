module

public import CFSG.ClassicalInvolution.Q3.Q3T8C262Type
public import CFSG.ClassicalInvolution.Q3.Q3T7SectC
public import CFSG.ClassicalInvolution.Q3.Q3MTModel5
public import CFSG.ClassicalInvolution.Asc77.AscT8W19
public import CFSG.ClassicalInvolution.Q3.Q3WASAut
public import CFSG.ClassicalInvolution.Q3.Q3TPSModel
public import CFSG.ClassicalInvolution.Q3.Q3MTOrth
public import CFSG.ClassicalInvolution.Q3.Q3TZMax
public import CFSG.ClassicalInvolution.Asc77.AscIHSectKB
public import CFSG.ClassicalInvolution.Asc77.AscIHSectKC
public import CFSG.ClassicalInvolution.Asc77.AscC25J12
public import CFSG.ClassicalInvolution.Asc77.AscC25J13
public import CFSG.ClassicalInvolution.Asc77.AscT8RFinal
public import CFSG.ClassicalInvolution.Asc77.AscT8ThmEight
public import CFSG.ClassicalInvolution.Asc77.AscT8V16
public import CFSG.ClassicalInvolution.Asc77.AscT8V2
public import CFSG.ClassicalInvolution.Asc77.AscT8W10
public import CFSG.ClassicalInvolution.Asc77.AscT8W14
public import CFSG.ClassicalInvolution.Asc77.WP2Branch
public import CFSG.ClassicalInvolution.Q3.Q3CLNine3
public import CFSG.ClassicalInvolution.Q3.Q3CPOmega
public import CFSG.ClassicalInvolution.Q3.Q3MTDatum
public import CFSG.ClassicalInvolution.Q3.Q3T7Stmt
public import CFSG.ClassicalInvolution.Q3.Q3T8P1Seven
public import CFSG.ClassicalInvolution.Q3.Q3ZFraStd
public import CFSG.ClassicalInvolution.Uniform.U3IH8
public import CFSG.Sporadic.J4.QT2LocProof

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Asc77 CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

@[expose] def E4SecGen3 : Prop :=
  ∀ n : ℕ, CITBelowT (.sl2 3 1) n → IH8T 3 1 n →
    ∀ (X : Type) [Group X] [Finite X], Nat.card X < n →
      ∀ Φ : Set (Subgroup X), HypOmegaModU (.sl2 3 1) Φ → classicalInvolutionOddCore X = ⊥ →
        omegaGen Φ = ⊤ → (∀ L ∈ Φ, AEmpty Φ L) → (∀ K ∈ Φ, ∀ K' ∈ twinSet Φ K, K' = K) →
          ¬ T3.DStarConnected Φ →
            ∀ A ∈ Φ, ∀ B ∈ omegaNbr Φ A, ∀ x x' : X, IsUniqueInvolution A x →
              IsUniqueInvolution B x' → x * x' ∈ Subgroup.center X →
                ∀ σ : MulAut X, σ * σ = 1 → σ x' = x' →
                  (∀ k ∈ A, σ k * k⁻¹ ∈ oddCoreOf A) → (∀ k ∈ B, σ k ∈ B) →
                  (¬ ∀ k ∈ B, σ k * k⁻¹ ∈ oddCoreOf B) →
                    Subgroup.closure ({g | σ g = g} ∪ {g | x' * g = g * x'} ∪
                      {g | σ (x' * g * x'⁻¹) = g}) = ⊤

@[expose] def Ih8D4Star3 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Φ : Set (Subgroup X)), HypOmegaModU (.sl2 3 1) Φ →
    Nonempty (Ih8Model 3 1 Φ .POmegaPlus 4 1) → T3.DStarConnected Φ

namespace E4G3

section Gen3Ratio

variable {S Y : Type*} [Group S] [Group Y]

theorem fix_of_gen3 (ψ : S →* Y) (hker : ψ.ker ≤ Subgroup.center S)
    (hk3 : ∀ z ∈ ψ.ker, z ^ 3 = 1 → z = 1) (α : S →* S) {P : Subgroup S}
    (hP : ModelFacts.Gen3 P) (h : ∀ r ∈ P, ψ (α r) = ψ r) : ∀ r ∈ P, α r = r := by
  obtain ⟨T, hTP, hT3, hPT⟩ := hP
  have hle : Subgroup.closure T ≤ MonoidHom.eqLocus α (MonoidHom.id S) := by
    rw [Subgroup.closure_le]
    intro s hs
    show α s = s
    have hc : α s * s⁻¹ ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h s (hTP hs), mul_inv_cancel]
    have hcc : Commute (α s * s⁻¹) s := (Subgroup.mem_center_iff.mp (hker hc) s).symm
    have h3 : (α s * s⁻¹) ^ 3 = 1 := by
      have e1 : α s = (α s * s⁻¹) * s := by group
      have e2 : (α s) ^ 3 = 1 := by rw [← map_pow, hT3 s hs, map_one]
      rw [e1, hcc.mul_pow, hT3 s hs, mul_one] at e2
      exact e2
    exact mul_inv_eq_one.mp (hk3 _ hc h3)
  intro r hr
  exact hle (hPT hr)

end Gen3Ratio

section Pair


structure E4Pair3 {S Y : Type} [Group S] [Group Y] (ψ : S →* Y) (R R' : Subgroup S) (y y' : S) :
    Prop where
  surj : Function.Surjective ψ
  ker : ψ.ker ≤ Subgroup.center S
  ker3 : ∀ z ∈ ψ.ker, z ^ 3 = 1 → z = 1
  perf : Group.IsPerfect S
  ne : R ≠ R'
  comm : Commutes R R'
  hy : y ∈ R
  hy2 : y * y = 1
  hy1 : y ≠ 1
  hy' : y' ∈ R'
  hy'2 : y' * y' = 1
  hy'1 : y' ≠ 1
  cen : y * y' ∈ Subgroup.center S
  cy : ∀ r ∈ R, y * r = r * y
  cy' : ∀ r ∈ R', y' * r = r * y'

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem e4_pair_of_model3 (hΦ : HypOmegaModU (.sl2 3 1) Φ) {t : StatedLieTag} {k e : ℕ}
    (M : Ih8Model 3 1 Φ t k e) (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4)
    (hnpsl : ¬ (t = .PSL ∧ k = 2)) (hSperf : Group.IsPerfect (modelUniv t k 3 e Fact.out).K)
    {A B : Subgroup X} (hA : A ∈ Φ) (hB : B ∈ omegaNbr Φ A) {x x' : X}
    (hxA : IsUniqueInvolution A x) (hxB : IsUniqueInvolution B x')
    (hcen : x * x' ∈ Subgroup.center X) :
    ∃ (R R' : Subgroup (modelUniv t k 3 e Fact.out).K) (y y' : (modelUniv t k 3 e Fact.out).K),
      R ∈ M.cls ∧ R' ∈ M.cls ∧ A = R.map M.ψ ∧ B = R'.map M.ψ ∧ M.ψ y = x ∧ M.ψ y' = x' ∧
        E4Pair3 M.ψ R R' y y' := by
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  obtain ⟨R, hR, hAR⟩ := (M.mem_iff A).mp hA
  obtain ⟨R', hR', hBR⟩ := (M.mem_iff B).mp hB.1
  have hcomm : Commutes R R' :=
    Q3MT.commutes_of_omegaNbr3 M hΦ hG2 hD4 hR hR' (by rw [← hAR, ← hBR]; exact hB)
  have hodd := M.natCard_galoisField_odd hp2
  obtain ⟨eR⟩ := M.cls_equiv_sl2 hp2 hG2 hD4 hR
  obtain ⟨eR'⟩ := M.cls_equiv_sl2 hp2 hG2 hD4 hR'
  have hinj : ∀ R₀ : Subgroup (modelUniv t k 3 e Fact.out).K, R₀ ∈ M.cls →
      ∀ a ∈ R₀, ∀ b ∈ R₀, M.ψ a = M.ψ b → a = b := by
    intro R₀ hR₀ a ha b hb hab
    have h1 : a * b⁻¹ = 1 := M.injOn_fund hnpsl (M.cls_sub hR₀) (a * b⁻¹)
      (R₀.mul_mem ha (R₀.inv_mem hb)) (by rw [map_mul, map_inv, hab, mul_inv_cancel])
    exact mul_inv_eq_one.mp h1
  have hψy : M.ψ (sl2Inv eR) = x := by
    have hmem : M.ψ (sl2Inv eR) ∈ A := by
      rw [hAR]
      exact Subgroup.mem_map_of_mem _ (sl2Inv_mem eR)
    have hsq : M.ψ (sl2Inv eR) * M.ψ (sl2Inv eR) = 1 := by
      rw [← map_mul, sl2Inv_mul_self hodd eR, map_one]
    rcases hxA.unique _ hmem hsq with h | h
    · exact absurd (hinj R hR _ (sl2Inv_mem eR) 1 R.one_mem (by rw [h, map_one]))
        (sl2Inv_ne_one hodd eR)
    · exact h
  have hψy' : M.ψ (sl2Inv eR') = x' := by
    have hmem : M.ψ (sl2Inv eR') ∈ B := by
      rw [hBR]
      exact Subgroup.mem_map_of_mem _ (sl2Inv_mem eR')
    have hsq : M.ψ (sl2Inv eR') * M.ψ (sl2Inv eR') = 1 := by
      rw [← map_mul, sl2Inv_mul_self hodd eR', map_one]
    rcases hxB.unique _ hmem hsq with h | h
    · exact absurd (hinj R' hR' _ (sl2Inv_mem eR') 1 R'.one_mem (by rw [h, map_one]))
        (sl2Inv_ne_one hodd eR')
    · exact h
  refine ⟨R, R', sl2Inv eR, sl2Inv eR', hR, hR', hAR, hBR, hψy, hψy', ?_⟩
  refine ⟨M.surj, M.ker_le_center, ih8Model_ker_pow_three M hD4, hSperf, ?_, hcomm, sl2Inv_mem eR,
    sl2Inv_mul_self hodd eR, sl2Inv_ne_one hodd eR, sl2Inv_mem eR', sl2Inv_mul_self hodd eR',
    sl2Inv_ne_one hodd eR', ?_, fun r hr => sl2Inv_commute eR hr,
    fun r hr => sl2Inv_commute eR' hr⟩
  · intro h
    exact hB.2.1 (by rw [hBR, ← h, ← hAR])
  · exact CFSG.ClassicalInvolution.Asc77.T8V.mem_center_of_map_mem_center hSperf M.ψ
      M.ker_le_center (by rw [map_mul, hψy, hψy']; exact hcen)

end Pair

section SL4

open CFSG.ClassicalInvolution.Asc77.T8W (negTwo closure_fix_eq_top sl4_inner_case sl4_graph_case
  twin_std_y')
open CFSG.ClassicalInvolution.Models (longRootSet)
open scoped Matrix

local notation "𝔽₃" => GaloisField 3 1


theorem sl4_gen_std3 {Y : Type} [Group Y] (ψ : SL(4, 𝔽₃) →* Y) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center SL(4, 𝔽₃)) (hk3 : ∀ z ∈ ψ.ker, z ^ 3 = 1 → z = 1)
    (hSperf : Group.IsPerfect SL(4, 𝔽₃)) (σ : MulAut Y) (hσ2 : ∀ x, σ (σ x) = x)
    (h0 : ∀ r ∈ (WeakCT.blockSL 𝔽₃ 4 2 0 (by norm_num)).range, σ (ψ r) = ψ r)
    (hnt : ∃ r ∈ (WeakCT.blockSL 𝔽₃ 4 2 2 (by norm_num)).range, σ (ψ r) ≠ ψ r) :
    Subgroup.closure ({g | σ g = g} ∪
      {g | σ (ψ (negTwo 𝔽₃) * g * (ψ (negTwo 𝔽₃))⁻¹) = g}) = ⊤ := by
  classical
  have h2 : (2 : 𝔽₃) ≠ 0 := ModelFacts.two_ne_zero_galoisField 1 (by norm_num)
  obtain ⟨α, g, φ, ε, hlift, hmat⟩ :=
    Q3W.linearAutClassification3 (n := 4) (by norm_num) Y ψ hψ hker σ
  have hα0 : ∀ r ∈ (WeakCT.blockSL 𝔽₃ 4 2 0 (by norm_num)).range, α r = r := by
    refine fix_of_gen3 ψ hker hk3 α ?_ (fun r hr => by rw [hlift, h0 r hr])
    have := (ModelFacts.gen3_top_sl2 (F := 𝔽₃)).map (WeakCT.blockSL 𝔽₃ 4 2 0 (by norm_num))
    rwa [← MonoidHom.range_eq_map] at this
  have hα2 : ∀ x, α (α x) = x := by
    have := CFSG.ClassicalInvolution.Asc77.T8V.eq_of_central_ratio (α.comp α) (P := ⊤)
      (CFSG.ClassicalInvolution.Asc77.T8V.top_le_commutator_of_perfect hSperf) (fun x _ =>
        hker (by
          rw [MonoidHom.mem_ker, map_mul, map_inv, MonoidHom.comp_apply, hlift, hlift, hσ2,
            mul_inv_cancel]))
    intro x
    simpa using this x (Subgroup.mem_top x)
  have hblock2 : (∀ r ∈ (WeakCT.blockSL 𝔽₃ 4 2 2 (by norm_num)).range, α r = r) → False := by
    intro h
    obtain ⟨r, hr, hne⟩ := hnt
    exact hne (by rw [← hlift, h r hr])
  have hGGi : (g : Matrix (Fin 4) (Fin 4) 𝔽₃) *
      ((g⁻¹ : GL (Fin 4) 𝔽₃) : Matrix (Fin 4) (Fin 4) 𝔽₃) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hGiG : ((g⁻¹ : GL (Fin 4) 𝔽₃) : Matrix (Fin 4) (Fin 4) 𝔽₃) *
      (g : Matrix (Fin 4) (Fin 4) 𝔽₃) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hdet : (g : Matrix (Fin 4) (Fin 4) 𝔽₃).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).ne_zero
  cases ε
  · have hmat' : ∀ x : SL(4, 𝔽₃),
        ((α x : SL(4, 𝔽₃)) : Matrix (Fin 4) (Fin 4) 𝔽₃) =
          (g : Matrix (Fin 4) (Fin 4) 𝔽₃) * φ.mapMatrix (x : Matrix (Fin 4) (Fin 4) 𝔽₃) *
            ((g⁻¹ : GL (Fin 4) 𝔽₃) : Matrix (Fin 4) (Fin 4) 𝔽₃) := fun x => by
      simpa using hmat x
    rcases sl4_inner_case h2 α _ _ hGGi hGiG hdet φ hmat' hα2 hα0 with h | ⟨Mgl, h₁, h₂⟩
    · exact absurd h hblock2
    · exact closure_fix_eq_top ψ hψ σ α hlift (negTwo _) Mgl h₁ h₂
  · have hmat' : ∀ x : SL(4, 𝔽₃),
        ((α x : SL(4, 𝔽₃)) : Matrix (Fin 4) (Fin 4) 𝔽₃) =
          (g : Matrix (Fin 4) (Fin 4) 𝔽₃) * φ.mapMatrix
            (((x⁻¹ : SL(4, 𝔽₃)) : Matrix (Fin 4) (Fin 4) 𝔽₃))ᵀ *
              ((g⁻¹ : GL (Fin 4) 𝔽₃) : Matrix (Fin 4) (Fin 4) 𝔽₃) := fun x => by
      simpa using hmat x
    exact absurd (sl4_graph_case h2 α _ _ hGGi hGiG hdet φ hmat' hα2 hα0) hblock2

theorem sl4_gen_of_pair3 {Y : Type} [Group Y] (ψ : SL(4, 𝔽₃) →* Y)
    {R R' : Subgroup SL(4, 𝔽₃)} {y y' : SL(4, 𝔽₃)} (hP : E4Pair3 ψ R R' y y')
    (hR : R ∈ longRootSet (K := 𝔽₃) (show 2 ≤ 4 by norm_num))
    (hR' : R' ∈ longRootSet (K := 𝔽₃) (show 2 ≤ 4 by norm_num))
    (σ : MulAut Y) (hσ2 : ∀ x, σ (σ x) = x) (hσR : ∀ r ∈ R, σ (ψ r) = ψ r)
    (hσnt : ∃ r ∈ R', σ (ψ r) ≠ ψ r) :
    Subgroup.closure ({g | σ g = g} ∪ {g | σ (ψ y' * g * (ψ y')⁻¹) = g}) = ⊤ := by
  classical
  have h2 : (2 : 𝔽₃) ≠ 0 := ModelFacts.two_ne_zero_galoisField 1 (by norm_num)
  have hc : y' * y⁻¹ ∈ Subgroup.center SL(4, 𝔽₃) := by
    have := hP.cen
    have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hP.hy2
    rw [hyi, ← hP.comm y hP.hy y' hP.hy']
    exact this
  obtain ⟨g, hRg, hR'g, hy'g⟩ := twin_std_y' h2 hR hR' hP.ne hP.hy hP.hy2 hP.hy1 hP.hy' hP.hy'2
    hP.hy'1 hc
  set ψ₀ : SL(4, 𝔽₃) →* Y := ψ.comp (MulAut.conj g).toMonoidHom with hψ₀
  have hψ₀s : Function.Surjective ψ₀ := hP.surj.comp (MulAut.conj g).surjective
  have hker₀ : ψ₀.ker ≤ Subgroup.center SL(4, 𝔽₃) := by
    intro x hx
    have h1 : g * x * g⁻¹ ∈ Subgroup.center SL(4, 𝔽₃) := hP.ker hx
    have h2' := (Subgroup.center SL(4, 𝔽₃)).normal_of_characteristic.conj_mem
      (g * x * g⁻¹) h1 g⁻¹
    simpa [mul_assoc] using h2'
  have hk3₀ : ∀ z ∈ ψ₀.ker, z ^ 3 = 1 → z = 1 := by
    intro z hz hz3
    have h1 : g * z * g⁻¹ ∈ ψ.ker := hz
    have h2' : (g * z * g⁻¹) ^ 3 = 1 := by
      rw [conj_pow, hz3]
      group
    have h3 := hP.ker3 _ h1 h2'
    calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
      _ = 1 := by rw [h3]; group
  have h0 : ∀ r ∈ (WeakCT.blockSL 𝔽₃ 4 2 0 (by norm_num)).range, σ (ψ₀ r) = ψ₀ r := by
    intro r hr
    apply hσR
    rw [hRg]
    exact ⟨r, hr, rfl⟩
  have hnt : ∃ r ∈ (WeakCT.blockSL 𝔽₃ 4 2 2 (by norm_num)).range, σ (ψ₀ r) ≠ ψ₀ r := by
    obtain ⟨r', hr', hne⟩ := hσnt
    rw [hR'g] at hr'
    obtain ⟨r, hr, rfl⟩ := hr'
    exact ⟨r, hr, hne⟩
  have key := sl4_gen_std3 ψ₀ hψ₀s hker₀ hk3₀ hP.perf σ hσ2 h0 hnt
  have hψ₀y : ψ₀ (negTwo 𝔽₃) = ψ y' := by
    rw [hy'g]
    simp [hψ₀, MulAut.conj_apply]
  rw [hψ₀y] at key
  exact key

end SL4

section SL4Tag

open CFSG.ClassicalInvolution.Models (longRootSet)

local notation "𝔽₃" => GaloisField 3 1


variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem e4_gen_sl43 (hΦ : HypOmegaModU (.sl2 3 1) Φ) (M : Ih8Model 3 1 Φ .PSL 4 1)
    {A B : Subgroup X} (hA : A ∈ Φ) (hB : B ∈ omegaNbr Φ A) {x x' : X}
    (hxA : IsUniqueInvolution A x) (hxB : IsUniqueInvolution B x')
    (hcen : x * x' ∈ Subgroup.center X) (σ : MulAut X) (hσ2 : σ * σ = 1)
    (hσA : ∀ k ∈ A, σ k * k⁻¹ ∈ oddCoreOf A)
    (hσnt : ¬ ∀ k ∈ B, σ k * k⁻¹ ∈ oddCoreOf B) :
    Subgroup.closure ({g | σ g = g} ∪ {g | x' * g = g * x'} ∪
      {g | σ (x' * g * x'⁻¹) = g}) = ⊤ := by
  have hG2 : StatedLieTag.PSL ≠ .G2 := by decide
  have hD4 : StatedLieTag.PSL ≠ .trialityD4 := by decide
  have hnpsl : ¬ (StatedLieTag.PSL = .PSL ∧ (4 : ℕ) = 2) := by simp
  have hSperf : Group.IsPerfect (modelUniv .PSL 4 3 1 Fact.out).K :=
    Group.isPerfect_def.2 (ModelFacts.modelClauseZero .PSL 4 3 1 Fact.out trivial M.admissible).1.1
  have hex := exactMembers_of_ih8Model M hΦ hG2 hD4
  obtain ⟨R, R', y, y', hR, hR', hAR, hBR, hy, hy', hP⟩ :=
    e4_pair_of_model3 hΦ M hG2 hD4 hnpsl hSperf hA hB hxA hxB hcen
  have hA0 : oddCoreOf A = ⊥ := oddCoreOf_eq_bot_of_exact hex hA
  have hB0 : oddCoreOf B = ⊥ := oddCoreOf_eq_bot_of_exact hex hB.1
  have hRl := CFSG.ClassicalInvolution.RouteD.fundamentalSubgroups_psl_subset (m := 3)
    (by norm_num) (M.cls_sub hR)
  have hRl' := CFSG.ClassicalInvolution.RouteD.fundamentalSubgroups_psl_subset (m := 3)
    (by norm_num) (M.cls_sub hR')
  subst hAR hBR hy hy'
  have hσ2' : ∀ z, σ (σ z) = z := fun z => by
    have := congrArg (fun τ : MulAut X => τ z) hσ2
    simpa using this
  have hσR : ∀ r ∈ R, σ (M.ψ r) = M.ψ r := by
    intro r hr
    have h := hσA (M.ψ r) (Subgroup.mem_map_of_mem _ hr)
    rw [hA0, Subgroup.mem_bot, mul_inv_eq_one] at h
    exact h
  have hσnt' : ∃ r ∈ R', σ (M.ψ r) ≠ M.ψ r := by
    by_contra hcon
    push Not at hcon
    apply hσnt
    rintro k ⟨r, hr, rfl⟩
    rw [hB0, Subgroup.mem_bot, mul_inv_eq_one]
    exact hcon r hr
  have key := sl4_gen_of_pair3 M.ψ hP hRl hRl' σ hσ2' hσR hσnt'
  rw [eq_top_iff] at key ⊢
  refine key.trans (Subgroup.closure_mono ?_)
  intro g hg
  rcases hg with hg | hg
  · exact Or.inl (Or.inl hg)
  · exact Or.inr hg

end SL4Tag

section Sp4

open Matrix CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainU
  CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterSp4
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_apply mat_elt_positiveLong
  mat_elt_negativeLong)
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)
open CFSG.ClassicalInvolution.Asc77.T8W (sp4_shape_one sp4_entries diagonal_commute_blockMat
  swapMat swapMat_symp comm_of_conj_conj)

local notation "𝔽₃" => GaloisField 3 1

theorem sp4_no_sigma3 {Y : Type} [Group Y] (ψ : StatedSp 2 𝔽₃ →* Y)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center (StatedSp 2 𝔽₃))
    (hperf : Group.IsPerfect (StatedSp 2 𝔽₃)) (k : Fin 2) (σ : MulAut Y)
    (hσ2 : ∀ x, σ (σ x) = x) (h0 : ∀ r ∈ (longBlock 𝔽₃ 2 k).range, σ (ψ r) = ψ r)
    (hnt : ∃ r ∈ (longBlock 𝔽₃ 2 (Fin.rev k)).range, σ (ψ r) ≠ ψ r) : False := by
  classical
  have h2 : (2 : 𝔽₃) ≠ 0 := ModelFacts.two_ne_zero_galoisField 1 (by norm_num)
  obtain ⟨A, τ, hAτ⟩ := Q3TPS.exists_semilinear_lift3 ψ hker σ hσ2
    (fun x => by rw [MonoidHom.range_eq_top.mpr hψ]; exact Subgroup.mem_top _)
  obtain ⟨α, hαdef⟩ : ∃ α : MulAut (StatedSp 2 𝔽₃),
      ∀ g, α g = conjSp 2 𝔽₃ A (fieldSp 2 𝔽₃ τ g) :=
    ⟨conjSp 2 𝔽₃ A * fieldSp 2 𝔽₃ τ, fun g => rfl⟩
  have hlift : ∀ x, ψ (α x) = σ (ψ x) := fun x => by rw [hαdef]; exact (hAτ x).symm
  have hk3 : ∀ z ∈ ψ.ker, z ^ 3 = 1 → z = 1 := by
    intro z hz hz3
    have hz2 : z * z = 1 := mul_self_eq_one_of_mem_center (by norm_num) (hker hz)
    calc z = z ^ 3 * (z * z)⁻¹ := by group
      _ = 1 := by rw [hz3, hz2]; group
  have hfix : ∀ r ∈ (longBlock 𝔽₃ 2 k).range, α r = r := by
    refine fix_of_gen3 ψ hker hk3 α.toMonoidHom ?_ (fun r hr => by
      show ψ (α r) = ψ r
      rw [hlift, h0 r hr])
    have := (ModelFacts.gen3_top_sl2 (F := 𝔽₃)).map (longBlock 𝔽₃ 2 k)
    rwa [← MonoidHom.range_eq_map] at this
  have hu : ∀ t : 𝔽₃,
      ((A : GL (Fin 2 ⊕ Fin 2) 𝔽₃) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) 𝔽₃) *
          Matrix.transvection (Sum.inl k) (Sum.inr k) (τ t) =
        Matrix.transvection (Sum.inl k) (Sum.inr k) t *
          ((A : GL (Fin 2 ⊕ Fin 2) 𝔽₃) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) 𝔽₃) := by
    intro t
    have hg := hfix (longBlock 𝔽₃ 2 k (sl2Upper t)) ⟨_, rfl⟩
    have := rel_of_fixed A τ _ ((hαdef _).symm.trans hg)
    rwa [longBlock_sl2Upper, mat_elt_positiveLong, map_transvection] at this
  have hl : ∀ t : 𝔽₃,
      ((A : GL (Fin 2 ⊕ Fin 2) 𝔽₃) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) 𝔽₃) *
          Matrix.transvection (Sum.inr k) (Sum.inl k) (τ t) =
        Matrix.transvection (Sum.inr k) (Sum.inl k) t *
          ((A : GL (Fin 2 ⊕ Fin 2) 𝔽₃) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) 𝔽₃) := by
    intro t
    have hg := hfix (longBlock 𝔽₃ 2 k (sl2Lower t)) ⟨_, rfl⟩
    have := rel_of_fixed A τ _ ((hαdef _).symm.trans hg)
    rwa [longBlock_sl2Lower, mat_elt_negativeLong, map_transvection] at this
  have hdet : ((A : GL (Fin 2 ⊕ Fin 2) 𝔽₃) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) 𝔽₃).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (A : GL (Fin 2 ⊕ Fin 2) 𝔽₃).isUnit).ne_zero
  obtain ⟨hτ1, a, ha, r1, r2, c1, c2, d1, d2⟩ := sp4_shape_one τ _ hdet k hu hl
  subst hτ1
  have := hperf
  have hα2 : ∀ g, α (α g) = g := by
    have := lift_comp_self_eq_id (θ := ψ) hker (σ := σ) hσ2 (α := α.toMonoidHom) hlift
    intro g
    simpa using DFunLike.congr_fun this g
  have hαrefl : ∀ g, α g = conjSp 2 𝔽₃ A g := fun g => by
    rw [hαdef, show fieldSp 2 𝔽₃ (RingEquiv.refl 𝔽₃) = 1 from map_one _]
    rfl
  set Am : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) 𝔽₃ :=
    ((A : GL (Fin 2 ⊕ Fin 2) 𝔽₃) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) 𝔽₃) with hAm
  set w : StatedSp 2 𝔽₃ := ofSymplecticMat (swapMat (F := 𝔽₃)) swapMat_symp with hw
  have hsw : Am * Am * swapMat = swapMat * (Am * Am) := by
    have h := congrArg (fun g : StatedSp 2 𝔽₃ => (g : GL (Fin 2 ⊕ Fin 2) 𝔽₃)) (hα2 w)
    simp only [hαrefl, coe_conjSp] at h
    have h' := congrArg
      (fun g : GL (Fin 2 ⊕ Fin 2) 𝔽₃ => (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) 𝔽₃))
      (comm_of_conj_conj _ _ h)
    have hwm : ((w : GL (Fin 2 ⊕ Fin 2) 𝔽₃) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) 𝔽₃) =
        swapMat := rfl
    simp only [Units.val_mul, hwm] at h'
    exact h'
  obtain ⟨μ, hμ⟩ := mem_gsp.mp A.2
  obtain ⟨hoff, hpq⟩ := sp4_entries h2 k _ ha r1 r2 c1 c2 d1 d2 ⟨μ, hμ⟩ hsw
  have hdiag : Am = Matrix.diagonal (fun c => Am c c) := by
    ext c e
    by_cases hce : c = e
    · subst hce
      simp
    · rw [Matrix.diagonal_apply_ne _ hce]
      exact hoff c e hce
  have hcomm : ∀ M : Matrix (Fin 2) (Fin 2) 𝔽₃,
      Am * CFSG.LieType.Steinberg.Sp.blockMat (Sum.inl (Fin.rev k)) (Sum.inr (Fin.rev k)) M =
        CFSG.LieType.Steinberg.Sp.blockMat (Sum.inl (Fin.rev k)) (Sum.inr (Fin.rev k)) M * Am := by
    intro M
    have := diagonal_commute_blockMat (fun c => Am c c) (p := Sum.inl (Fin.rev k))
      (q := Sum.inr (Fin.rev k)) hpq M
    rwa [← hdiag] at this
  have hfix' : ∀ r ∈ (longBlock 𝔽₃ 2 (Fin.rev k)).range, α r = r := by
    rintro _ ⟨y, rfl⟩
    rw [hαrefl]
    apply Subtype.ext
    rw [coe_conjSp]
    have hc : (A : GL (Fin 2 ⊕ Fin 2) 𝔽₃) *
        ((longBlock 𝔽₃ 2 (Fin.rev k) y : StatedSp 2 𝔽₃) : GL (Fin 2 ⊕ Fin 2) 𝔽₃) =
        ((longBlock 𝔽₃ 2 (Fin.rev k) y : StatedSp 2 𝔽₃) : GL (Fin 2 ⊕ Fin 2) 𝔽₃) *
          (A : GL (Fin 2 ⊕ Fin 2) 𝔽₃) := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul]
      have := hcomm (y : Matrix (Fin 2) (Fin 2) 𝔽₃)
      rw [← mat_longBlock] at this
      exact this
    exact mul_inv_eq_iff_eq_mul.mpr hc
  obtain ⟨r, hr, hne⟩ := hnt
  exact hne (by rw [← hlift, hfix' r hr])

end Sp4

section Sp4Tag

open CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterSp4 (twin_std_sp)

local notation "𝔽₃" => GaloisField 3 1


variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem e4_gen_sp3 (hΦ : HypOmegaModU (.sl2 3 1) Φ) (M : Ih8Model 3 1 Φ .PSp 2 1)
    {A B : Subgroup X} (hA : A ∈ Φ) (hB : B ∈ omegaNbr Φ A) {x x' : X}
    (hxA : IsUniqueInvolution A x) (hxB : IsUniqueInvolution B x')
    (hcen : x * x' ∈ Subgroup.center X) (σ : MulAut X) (hσ2 : σ * σ = 1)
    (hσA : ∀ k ∈ A, σ k * k⁻¹ ∈ oddCoreOf A)
    (hσnt : ¬ ∀ k ∈ B, σ k * k⁻¹ ∈ oddCoreOf B) : False := by
  have hG2 : StatedLieTag.PSp ≠ .G2 := by decide
  have hD4 : StatedLieTag.PSp ≠ .trialityD4 := by decide
  have hnpsl : ¬ (StatedLieTag.PSp = .PSL ∧ (2 : ℕ) = 2) := by simp
  have hSperf : Group.IsPerfect (modelUniv .PSp 2 3 1 Fact.out).K :=
    Group.isPerfect_def.2 (ModelFacts.modelClauseZero .PSp 2 3 1 Fact.out trivial M.admissible).1.1
  have hex := exactMembers_of_ih8Model M hΦ hG2 hD4
  obtain ⟨R, R', y, y', hR, hR', hAR, hBR, hy, hy', hP⟩ :=
    e4_pair_of_model3 hΦ M hG2 hD4 hnpsl hSperf hA hB hxA hxB hcen
  have hA0 : oddCoreOf A = ⊥ := oddCoreOf_eq_bot_of_exact hex hA
  have hB0 : oddCoreOf B = ⊥ := oddCoreOf_eq_bot_of_exact hex hB.1
  have h2 : (2 : 𝔽₃) ≠ 0 := ModelFacts.two_ne_zero_galoisField 1 (by norm_num)
  have hRl := (ModelFacts.fund_iff_isLongRootSp2 M.admissible h2 R).mp (M.cls_sub hR)
  have hRl' := (ModelFacts.fund_iff_isLongRootSp2 M.admissible h2 R').mp (M.cls_sub hR')
  subst hAR hBR hy hy'
  have hσ2' : ∀ z, σ (σ z) = z := fun z => by
    have := congrArg (fun τ : MulAut X => τ z) hσ2
    simpa using this
  have hσR : ∀ r ∈ R, σ (M.ψ r) = M.ψ r := by
    intro r hr
    have h := hσA (M.ψ r) (Subgroup.mem_map_of_mem _ hr)
    rw [hA0, Subgroup.mem_bot, mul_inv_eq_one] at h
    exact h
  have hσnt' : ∃ r ∈ R', σ (M.ψ r) ≠ M.ψ r := by
    by_contra hcon
    push Not at hcon
    apply hσnt
    rintro k ⟨r, hr, rfl⟩
    rw [hB0, Subgroup.mem_bot, mul_inv_eq_one]
    exact hcon r hr
  have hc : y' * y⁻¹ ∈ Subgroup.center (StatedSp 2 𝔽₃) := by
    have := hP.cen
    have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hP.hy2
    rw [hyi, ← hP.comm y hP.hy y' hP.hy']
    exact this
  obtain ⟨g, k, hRg, hR'g⟩ := twin_std_sp h2 hRl hRl' hP.ne hP.hy hP.hy2 hP.hy1 hP.hy' hP.hy'2
    hP.hy'1 hc
  set ψ₀ : StatedSp 2 𝔽₃ →* X := M.ψ.comp (MulAut.conj g).toMonoidHom with hψ₀
  have hψ₀s : Function.Surjective ψ₀ := hP.surj.comp (MulAut.conj g).surjective
  have hker₀ : ψ₀.ker ≤ Subgroup.center (StatedSp 2 𝔽₃) := by
    intro z hz
    have h1 : g * z * g⁻¹ ∈ Subgroup.center (StatedSp 2 𝔽₃) := hP.ker hz
    have h2' := (Subgroup.center (StatedSp 2 𝔽₃)).normal_of_characteristic.conj_mem
      (g * z * g⁻¹) h1 g⁻¹
    simpa [mul_assoc] using h2'
  have h0 : ∀ r ∈ (CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlock 𝔽₃ 2 k).range,
      σ (ψ₀ r) = ψ₀ r := by
    intro r hr
    apply hσR
    rw [hRg]
    exact ⟨r, hr, rfl⟩
  have hnt₀ : ∃ r ∈ (CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlock 𝔽₃ 2
      (Fin.rev k)).range, σ (ψ₀ r) ≠ ψ₀ r := by
    obtain ⟨r', hr', hne⟩ := hσnt'
    rw [hR'g] at hr'
    obtain ⟨r, hr, rfl⟩ := hr'
    exact ⟨r, hr, hne⟩
  exact sp4_no_sigma3 ψ₀ hψ₀s hker₀ hP.perf k σ hσ2' h0 hnt₀

end Sp4Tag

section Tag


variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem e4_tag3D {n : ℕ} (hn : CITBelowT (.sl2 3 1) n) (hih : IH8T 3 1 n) (hlt : Nat.card X < n)
    (hΦ : HypOmegaModU (.sl2 3 1) Φ) (hO : classicalInvolutionOddCore X = ⊥)
    (hgen : omegaGen Φ = ⊤) (hA : ∀ L ∈ Φ, AEmpty Φ L) (hdisc : ¬ DConnected Φ)
    {A B : Subgroup X} (hAΦ : A ∈ Φ) (hB : B ∈ omegaNbr Φ A) :
    ∃ (t : StatedLieTag) (k : ℕ), ((t = .PSp ∧ k = 2) ∨ (t = .PSL ∧ k = 4) ∨ (t = .PSU ∧ k = 4) ∨
      (t = .POmegaOdd ∧ k = 3) ∨ (t = .POmegaPlus ∧ k = 4) ∨ (t = .POmegaMinus ∧ k = 4)) ∧
      Nonempty (Ih8Model 3 1 Φ t k 1) := by
  classical
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hne : Φ.Nonempty := ⟨A, hAΦ⟩
  have hedge : dAdj Φ A B := Or.inl hB
  rcases dConnected_or_transitive3 hih.thm4 hlt hΦ hO hA with hc | htrans
  · exact absurd hc hdisc
  obtain ⟨D, hcard⟩ := Q3T7.exists_omegaLieU_sect hn hlt hΦ hO hgen htrans hne
  let i : Fin D.card := ⟨0, by omega⟩
  rcases D.valid i with ⟨t, k, e, ht, hadm, he, hc⟩ | ⟨h3, hc | hc⟩
  · obtain ⟨M⟩ : Nonempty (Ih8Model 3 1 Φ t k e) :=
      ⟨Q3T7.toIh8ModelSect D hΦ hgen hcard i ht hadm he hc⟩
    by_cases hG2d4 : t = .G2 ∨ t = .trialityD4
    · exfalso
      have : IsSimpleGroup X := M.isSimpleGroup_of_g2d4 hp2 hG2d4
      rcases ih8G2D4EdgeU_proved X Φ hΦ hA htrans t k e ⟨M⟩ hG2d4 with h' | h'
      · exact h' A hAΦ B hB.1 hedge
      · exact hdisc h'
    have hG2 : t ≠ .G2 := fun h => hG2d4 (Or.inl h)
    have hD4 : t ≠ .trialityD4 := fun h => hG2d4 (Or.inr h)
    have hef : e = 1 := he.resolve_right fun h => hD4 h.1
    subst hef
    by_cases h3' : (t = .PSL ∧ k = 3) ∨ (t = .PSU ∧ k = 3)
    · exfalso
      have : IsSimpleGroup X := Q3T7.isSimpleGroup_of_ih8Model_three M h3'
      exact ih8ThreeU_proved X Φ hΦ htrans t k 1 ⟨M⟩ h3' A hAΦ B hB.1 hedge
    have hA1 : ¬ (t = .PSL ∧ k = 2) := by
      rintro ⟨rfl, rfl⟩
      exact hadm.2.2.2.2 (by simp)
    rcases tag_casesU hp2 ht hadm hG2 hD4 with hconn | hsmall
    · exact absurd (dConnected_of_connectedU M hΦ hne hG2 hD4 hconn) hdisc
    rcases hsmall with ⟨rfl, hk⟩ | ⟨rfl, hk⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hk2 : 2 ≤ k := hadm.2.2.1
      have : k = 2 ∨ k = 3 ∨ k = 4 := by omega
      rcases this with rfl | rfl | rfl
      · exact absurd ⟨rfl, rfl⟩ hA1
      · exact absurd (Or.inl ⟨rfl, rfl⟩) h3'
      · exact ⟨.PSL, 4, Or.inr (Or.inl ⟨rfl, rfl⟩), ⟨M⟩⟩
    · have hk3 : 3 ≤ k := hadm.2.2.1
      have : k = 3 ∨ k = 4 := by omega
      rcases this with rfl | rfl
      · exact absurd (Or.inr ⟨rfl, rfl⟩) h3'
      · exact ⟨.PSU, 4, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)), ⟨M⟩⟩
    · exact ⟨.PSp, 2, Or.inl ⟨rfl, rfl⟩, ⟨M⟩⟩
    · exact ⟨.POmegaOdd, 3, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))), ⟨M⟩⟩
    · exact ⟨.POmegaPlus, 4, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))), ⟨M⟩⟩
    · exact ⟨.POmegaMinus, 4, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))), ⟨M⟩⟩
  · exfalso
    exact Q3T7.dEdgeless_of_top_mem3 htrans
      (Q3T7.top_mem_of_sl23_component_sect D hne hgen hcard i hc) A hAΦ B hB.1 hedge
  · exfalso
    obtain ⟨e⟩ := Q3T7.exists_mulEquiv_m11_sect D hgen hcard i hc
    exact dEdgeless_of_mulEquiv_m11 e hΦ (D.card_eq h3) A hAΦ B hB.1 hedge

theorem e4_tag3 {n : ℕ} (hn : CITBelowT (.sl2 3 1) n) (hih : IH8T 3 1 n) (hlt : Nat.card X < n)
    (hΦ : HypOmegaModU (.sl2 3 1) Φ) (hO : classicalInvolutionOddCore X = ⊥)
    (hgen : omegaGen Φ = ⊤) (hA : ∀ L ∈ Φ, AEmpty Φ L) (hdisc : ¬ T3.DStarConnected Φ)
    {A B : Subgroup X} (hAΦ : A ∈ Φ) (hB : B ∈ omegaNbr Φ A) :
    ∃ (t : StatedLieTag) (k : ℕ), ((t = .PSp ∧ k = 2) ∨ (t = .PSL ∧ k = 4) ∨ (t = .PSU ∧ k = 4) ∨
      (t = .POmegaOdd ∧ k = 3) ∨ (t = .POmegaPlus ∧ k = 4) ∨ (t = .POmegaMinus ∧ k = 4)) ∧
      Nonempty (Ih8Model 3 1 Φ t k 1) := by
  have hΩg := hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) hΦ
  exact e4_tag3D hn hih hlt hΦ hO hgen hA (fun hc => hdisc fun K hK L hL =>
    Q3T6.Mu.dComp_subset_dstarComp hΩg K (hc K hK L hL)) hAΦ hB

end Tag

section Star


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem dstarConnected_of_gens3 {t : StatedLieTag} {k e : ℕ} (M : Ih8Model 3 1 Ω t k e)
    (hΩ : HypOmegaModU (.sl2 3 1) Ω) (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4) {ι : Type}
    (L : ι → Subgroup (modelUniv t k 3 e Fact.out).K) (i₀ : ι) (hL : ∀ i, L i ∈ M.cls)
    (hgen : ⨆ i, L i = ⊤) (hcomp : ∀ i, (L i).map M.ψ ∈ dstarComp Ω ((L i₀).map M.ψ)) :
    T3.DStarConnected Ω := by
  have hK : (L i₀).map M.ψ ∈ Ω := M.map_mem (hL i₀)
  refine dstarConnected_of_generators hΩ.conjInvariant (M.exists_conj_of_fund hG2 hD4) hK ?_
  rw [eq_top_iff]
  have h1 : (⨆ i, (L i).map M.ψ) = ⊤ := by
    rw [← Subgroup.map_iSup, hgen, Subgroup.map_top, MonoidHom.range_eq_top.mpr M.surj]
  rw [← h1]
  exact iSup_le fun i => le_iSup₂_of_le _ (hcomp i) le_rfl

theorem dstarConnected_psu43 (hΩ : HypOmegaModU (.sl2 3 1) Ω) (M : Ih8Model 3 1 Ω .PSU 4 1) :
    T3.DStarConnected Ω := by
  by_cases hne : Ω.Nonempty
  swap
  · intro K hK
    exact absurd ⟨K, hK⟩ hne
  have hD4 : (StatedLieTag.PSU) ≠ .trialityD4 := by decide
  have hG2 : (StatedLieTag.PSU) ≠ .G2 := by decide
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hK : Nat.card (GaloisField 3 (2 * 1)) = (3 ^ 1) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul 3 1 le_rfl
  have hq2 : (3 : ℕ) ^ 1 ≠ 2 := by norm_num
  obtain ⟨φ, hφ⟩ := RouteD.psu_model_equiv hp2 M.admissible
  let nd : Fin 3 → Subgroup (modelUniv .PSU 4 3 1 Fact.out).K := fun i =>
    (Phan.standardU (GaloisField 3 (2 * 1)) 3 1 3 i).map φ.symm.toMonoidHom
  have hfund : ∀ i, nd i ∈ fundamentalSubgroups .PSU (modelUniv .PSU 4 3 1 Fact.out).D := by
    intro i
    show (Phan.standardU (GaloisField 3 (2 * 1)) 3 1 3 i).map φ.symm.toMonoidHom ∈ _
    rw [hφ, muTab_map_equiv_symm_map]
    exact ⟨_, Models.isLongRootSU2_range_blockEmb hK hp2 (by omega : (i : ℕ) + 2 ≤ 3 + 1)⟩
  have hmem : ∀ i, nd i ∈ M.cls := fun i => M.fund_subset_cls hne hG2 hD4 (hfund i)
  have hgen : ⨆ i, nd i = ⊤ := by
    have h1 := (Phan.weakPhanA_standard hK hq2 3).gen
    show ⨆ i, (Phan.standardU (GaloisField 3 (2 * 1)) 3 1 3 i).map φ.symm.toMonoidHom = ⊤
    rw [← Subgroup.map_iSup, h1]
    exact Subgroup.map_top_of_surjective _ φ.symm.surjective
  have hpair : ∀ i j : Fin 3, (j : ℕ) = i + 1 →
      dstarAdj Ω ((nd i).map M.ψ) ((nd j).map M.ψ) := by
    intro i j hij
    have hW := (Phan.weakPhanA_standard hK hq2 3).pair i j hij
    have hW' := Models.unitaryBlockStandardPair_map hW φ.symm.toMonoidHom φ.symm.injective
    exact Q3MT.dstarAdj_unitary3 M hΩ hG2 hD4 (hmem i) (hmem j) hW'
  have h01 := hpair 0 1 rfl
  have h12 := hpair 1 2 rfl
  refine dstarConnected_of_gens3 M hΩ hG2 hD4 nd 0 hmem hgen fun i => ?_
  fin_cases i
  · exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single h01
  · exact (Relation.ReflTransGen.single h01).tail h12

end Star

section Hub

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
  CFSG.LieType.Steinberg CFSG.LieType.BorelTits QuadraticMap
open CFSG.ClassicalInvolution.ModelFacts (spinCtx3_pOmegaPlus exists_spin_conj
  finrank_perp_add_four map_longSL2_range map_conj_map La_range_eq_map_conj longestFundamental
  fundamentalSubgroups_subset_longest)
open CFSG.ClassicalInvolution.Models.OrthogonalPairs (IsFundamental)
open CFSG.ClassicalInvolution.Phan (UnitaryBlockStandardPair)
open CFSG.ClassicalInvolution.Asc77.Hub (hubFrame hub_unitaryPair hub_ne_std)
open CFSG.LieType.CurtisTits (rankOne)
open CFSG.ClassicalInvolution.Asc77 (nodeSub nodeSub_mem_fund iSup_nodeSub
  modelUniv_pOmegaPlus_four)

local notation "𝔽₃" => GaloisField 3 1


theorem exists_hub_node3 :
    ∃ H : Subgroup (spinGroup (quadPlus 4 𝔽₃)),
      H ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 𝔽₃ (by norm_num)) ∧
      ∀ k : Fin 4, H ≠ rankOne (plusDatum 4 𝔽₃ (by norm_num)).rootGroup k ∧
        ∃ W, UnitaryBlockStandardPair (GaloisField 3 (2 * 1)) 3 1 W H
          (rankOne (plusDatum 4 𝔽₃ (by norm_num)).rootGroup k) := by
  classical
  have hn3 : 3 ≤ 4 := by norm_num
  have S := spinCtx3_pOmegaPlus (p := 3) (n := 4) (e := 1) le_rfl (by norm_num)
  have hodd : Odd (Nat.card 𝔽₃) := S.odd_card
  have h2 : (2 : 𝔽₃) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  have : Invertible (2 : 𝔽₃) := invertibleOfNonzero h2
  have hcard : Nat.card 𝔽₃ = 3 ^ 1 := S.card_eq
  have hneg : ¬ IsSquare (-1 : 𝔽₃) := by
    have : Fintype 𝔽₃ := Fintype.ofFinite _
    rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card, hcard]
    omega
  obtain ⟨a₀, b₀, hab₀⟩ := CharP.sq_add_sq 𝔽₃ 3 (-1)
  have hab : (a₀ : 𝔽₃) * a₀ + (b₀ : 𝔽₃) * b₀ = -1 := by
    have := hab₀
    push_cast at this
    linear_combination this
  have h4 : (4 : 𝔽₃) ≠ 0 := by
    have : (4 : 𝔽₃) = 2 * 2 := by norm_num
    rw [this]
    exact mul_ne_zero h2 h2
  have hw : 4 * (4 : 𝔽₃)⁻¹ = 1 := mul_inv_cancel₀ h4
  set a : 𝔽₃ := (a₀ : 𝔽₃) with ha
  set b : 𝔽₃ := (b₀ : 𝔽₃) with hb
  set w : 𝔽₃ := 4⁻¹ with hwdef
  have hij₀ : (0 : Fin 4) ≠ 1 := by decide
  set fr₀ := (plusFrame 4 𝔽₃ hn3).toFrame hij₀ true false with hfr₀
  have hperp : 2 ≤ Module.finrank 𝔽₃ fr₀.perp := by
    have := finrank_perp_add_four fr₀
    have hdim : Module.finrank 𝔽₃ (Fin 4 ⊕ Fin 4 → 𝔽₃) = 8 := by
      simp
    omega
  obtain ⟨x, hx⟩ := exists_spin_conj hodd (nondegenerate_polarBilin_quadPlus 4 𝔽₃)
    fr₀ (hubFrame a b w hab hw) hperp
  have hnode : ∀ k : Fin 4, rankOne (plusDatum 4 𝔽₃ hn3).rootGroup k =
      ((plusFrame 4 𝔽₃ hn3).longSL2 (rootIdxD_ne 4 (by omega) k) true (rootSignD 4 k)).range :=
    fun k => PlusCT.rankOne_plusRootGroup hn3 k
  have hnodefund : ∀ k : Fin 4, rankOne (plusDatum 4 𝔽₃ hn3).rootGroup k ∈
      fundamentalSubgroups .POmegaPlus (plusDatum 4 𝔽₃ hn3) := fun k =>
    nodeSub_mem_fund 3 1 k
  set R₀ := ((plusFrame 4 𝔽₃ hn3).longSL2 hij₀ true false).range with hR₀
  have hR₀fund : R₀ ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 𝔽₃ hn3) := by
    have := hnodefund 0
    rw [hnode 0] at this
    exact this
  have hHfund : conjSub x R₀ ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 𝔽₃ hn3) :=
    CFSG.ClassicalInvolution.RouteD.conjSub_mem_fundamentalSubgroups hR₀fund x
  have hHmap : (conjSub x R₀).map (spinAction (quadPlus 4 𝔽₃)) =
      (hubFrame a b w hab hw).La.range := by
    unfold conjSub
    rw [map_conj_map, hR₀, map_longSL2_range]
    exact (La_range_eq_map_conj hx).symm
  refine ⟨conjSub x R₀, hHfund, ?_⟩
  intro k
  have hkfund := hnodefund k
  rw [hnode k] at hkfund ⊢
  set hijk := rootIdxD_ne 4 (by omega) k with hijkdef
  set tk := rootSignD 4 k with htk
  have hRmap := map_longSL2_range (plusFrame 4 𝔽₃ hn3) hijk true tk
  have hHlong := fundamentalSubgroups_subset_longest (by decide) (by decide) _ hHfund
  have hRlong := fundamentalSubgroups_subset_longest (by decide) (by decide) _ hkfund
  have hpair := hub_unitaryPair (K' := GaloisField 3 (2 * 1)) (f := 1) hcard S.card_eq' hodd hneg
    hn3 a b w hab hw hijk true tk
  have hpair' : UnitaryBlockStandardPair (GaloisField 3 (2 * 1)) 3 1
      ((hubFrame a b w hab hw).La.range ⊔
        ((plusFrame 4 𝔽₃ hn3).toFrame hijk true tk).La.range)
      ((conjSub x R₀).map (spinAction (quadPlus 4 𝔽₃)))
      (((plusFrame 4 𝔽₃ hn3).longSL2 hijk true tk).range.map
        (spinAction (quadPlus 4 𝔽₃))) := by
    rw [hHmap, hRmap]
    exact hpair
  refine ⟨?_, S.unitary_of_map hHlong hRlong ⟨_, hpair'⟩⟩
  intro hHR
  refine hub_ne_std hn3 a b w hab hw hijk true tk
    (IsFundamental.involution_unique hodd (L := (hubFrame a b w hab hw).La.range)
      ⟨_, rfl, rfl⟩ ?_)
  rw [← hHmap, hHR, hRmap]
  exact ⟨_, rfl, rfl⟩

end Hub

section D4Star

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
open CFSG.ClassicalInvolution.Phan (UnitaryBlockStandardPair)
open CFSG.LieType.CurtisTits (rankOne)
open CFSG.ClassicalInvolution.Asc77 (nodeSub nodeSub_mem_fund iSup_nodeSub
  modelUniv_pOmegaPlus_four)

local notation "𝔽₃" => GaloisField 3 1


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem exists_hub_node3_of_eq (M₀ : LieUniversal)
    (hM₀ : M₀ = ⟨spinGroup (quadPlus 4 𝔽₃), plusDatum 4 𝔽₃ (by norm_num)⟩) :
    ∃ H : Subgroup M₀.K, H ∈ fundamentalSubgroups .POmegaPlus M₀.D ∧
      ∀ k : Fin M₀.D.rank, H ≠ rankOne M₀.D.rootGroup k ∧
        ∃ W, UnitaryBlockStandardPair (GaloisField 3 (2 * 1)) 3 1 W H
          (rankOne M₀.D.rootGroup k) := by
  subst hM₀
  exact exists_hub_node3

theorem dstarConnected_spin8plus3 (hΩ : HypOmegaModU (.sl2 3 1) Ω)
    (M : Ih8Model 3 1 Ω .POmegaPlus 4 1) : T3.DStarConnected Ω := by
  by_cases hne : Ω.Nonempty
  swap
  · intro K hK
    exact absurd ⟨K, hK⟩ hne
  have hD4 : (StatedLieTag.POmegaPlus) ≠ .trialityD4 := by decide
  have hG2 : (StatedLieTag.POmegaPlus) ≠ .G2 := by decide
  obtain ⟨H, hHfund, hall⟩ := exists_hub_node3_of_eq (modelUniv .POmegaPlus 4 3 1 Fact.out)
    (modelUniv_pOmegaPlus_four 3 1 (by norm_num))
  have hHcls : H ∈ M.cls := M.fund_subset_cls hne hG2 hD4 hHfund
  have hmem : ∀ i, nodeSub 3 1 i ∈ M.cls := fun i =>
    M.fund_subset_cls hne hG2 hD4 (nodeSub_mem_fund 3 1 i)
  refine dstarConnected_of_gens3 M hΩ hG2 hD4 (fun o : Option (Fin 4) => o.elim H (nodeSub 3 1))
    none (fun o => ?_) ?_ (fun o => ?_)
  · cases o
    · exact hHcls
    · exact hmem _
  · rw [eq_top_iff, ← iSup_nodeSub 3 1]
    exact iSup_le fun k => le_iSup (fun o : Option (Fin 4) => o.elim H (nodeSub 3 1)) (some k)
  · cases o
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single
        (Q3MT.dstarAdj_unitary3 M hΩ hG2 hD4 hHcls (hmem _) (hall _).2.choose_spec)

end D4Star

section Twin

open CFSG.ClassicalInvolution.G2D4Models (conjStabilizer mem_conjStabilizer_iff)
open CFSG.ClassicalInvolution.RouteD.TwinY (TwinDatumOn)
open CFSG.ClassicalInvolution.RouteD (ModelFund)
open CFSG.ClassicalInvolution.Phan (UnitaryBlockStandardPair)


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem dstarConnected_of_twin3 {t : StatedLieTag} {k : ℕ} (M : Ih8Model 3 1 Ω t k 1)
    (hΩ : HypOmegaModU (.sl2 3 1) Ω) (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4)
    (hmax : Q3TZ.TwinPairMax3 t k)
    (hunit : ∃ R₁ ∈ ModelFund 3 t k 1, ∃ R₂ ∈ ModelFund 3 t k 1,
      ∃ W, UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W R₁ R₂)
    {R R' : Subgroup (modelUniv t k 3 1 Fact.out).K} {x x' : (modelUniv t k 3 1 Fact.out).K}
    (hd : TwinDatumOn t (modelUniv t k 3 1 Fact.out) R R' x x')
    (hR : R ∈ M.cls) (hR' : R' ∈ M.cls) : T3.DStarConnected Ω := by
  classical
  have hΩg := hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) hΩ
  have hAΩ : R.map M.ψ ∈ Ω := M.map_mem hR
  have hne : Ω.Nonempty := ⟨_, hAΩ⟩
  have hK3 : Nat.card (GaloisField 3 2) = (3 ^ 1) ^ 2 := by
    rw [GaloisField.card 3 2 (by norm_num)]; norm_num
  obtain ⟨R₁, hR₁, R₂, hR₂, W, hW⟩ := hunit
  have hR₁c : R₁ ∈ M.cls := M.fund_subset_cls hne hG2 hD4 hR₁
  have hR₂c : R₂ ∈ M.cls := M.fund_subset_cls hne hG2 hD4 hR₂
  obtain ⟨g, hg⟩ : ∃ g : (modelUniv t k 3 1 Fact.out).K, R = conjSub g R₁ :=
    ModelFacts.fundamentalSingleClass t k 3 1 Fact.out
      (ih8_isFundTag_mf M.isFundTag) M.admissible hG2 hD4 R₁ (M.cls_sub hR₁c) R (M.cls_sub hR)
  have hJc : conjSub g R₂ ∈ M.cls := M.cls_conj R₂ hR₂c g
  have hWJ : UnitaryBlockStandardPair (GaloisField 3 2) 3 1 (conjSub g W) R (conjSub g R₂) := by
    have := Models.unitaryBlockStandardPair_map hW (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective
    rw [hg]
    exact this
  have hAdj : dstarAdj Ω (R.map M.ψ) ((conjSub g R₂).map M.ψ) :=
    Q3MT.dstarAdj_unitary3 M hΩ hG2 hD4 hR hJc hWJ
  have hJcomp : (conjSub g R₂).map M.ψ ∈ dstarComp Ω (R.map M.ψ) :=
    Relation.ReflTransGen.single hAdj
  have hBcomp : R'.map M.ψ ∈ dstarComp Ω (R.map M.ψ) := by
    have hnb : R'.map M.ψ ∈ omegaNbr Ω (R.map M.ψ) :=
      (Q3MT.omegaNbr_iff3 M hΩ hG2 hD4 hR hR').mpr ⟨hd.ne, hd.comm⟩
    exact Relation.ReflTransGen.single
      ⟨M.map_mem hR', Or.inl (Q3T6.Mu.omegaNbr_subset_omegaStarNbr hΩg _ hnb)⟩
  let N : Subgroup (modelUniv t k 3 1 Fact.out).K := (sigmaStarNorm Ω (R.map M.ψ)).comap M.ψ
  have hCN : conjStabilizer ({R, R'} : Set (Subgroup (modelUniv t k 3 1 Fact.out).K)) ≤ N := by
    intro g' hg'
    have h1 : conjSub g' R ∈ ({R, R'} : Set (Subgroup (modelUniv t k 3 1 Fact.out).K)) :=
      (mem_conjStabilizer_iff.mp hg' R).mpr (Or.inl rfl)
    refine T7A.mem_sigmaStarNorm_of_conj hΩ.conjInvariant hAΩ ?_
    have h3 : conjSub (M.ψ g') (R.map M.ψ) = (conjSub g' R).map M.ψ :=
      (map_conj_eq_conjSub_map M.ψ g' R).symm
    rw [h3]
    rcases h1 with h | h
    · rw [h]
      exact Relation.ReflTransGen.refl
    · rw [Set.mem_singleton_iff.mp h]
      exact hBcomp
  have hJN : conjSub g R₂ ≤ N := fun j hj =>
    le_sigmaStarNorm_of_mem_dstarComp hΩ.conjInvariant hAΩ hJcomp (Subgroup.mem_map_of_mem _ hj)
  have hJC : ¬ conjSub g R₂ ≤
      conjStabilizer ({R, R'} : Set (Subgroup (modelUniv t k 3 1 Fact.out).K)) := by
    intro hJC
    have hgen := ih8Model_gen3 M hG2 hD4 hJc
    have hnorm : conjSub g R₂ ≤ Subgroup.normalizer (R : Set (modelUniv t k 3 1 Fact.out).K) := by
      obtain ⟨S, hSJ, hS3, hJS⟩ := hgen
      refine hJS.trans ((Subgroup.closure_le _).2 fun s hs => ?_)
      have hsC := mem_conjStabilizer_iff.mp (hJC (hSJ hs))
      have h1 := (hsC R).mpr (Or.inl rfl)
      have h2 := (hsC R').mpr (Or.inr rfl)
      have hs3 : s ^ 3 = 1 := hS3 s hs
      refine ih8_mem_normalizer_of_conjSub_eq ?_
      by_contra hne'
      have hR'eq : conjSub s R = R' := by
        rcases h1 with h | h
        · exact absurd h hne'
        · exact Set.mem_singleton_iff.mp h
      have hRR : conjSub s R' = R := by
        rcases h2 with h | h
        · exact h
        · exfalso
          apply hd.ne
          have h' := hR'eq.trans (Set.mem_singleton_iff.mp h).symm
          calc R = conjSub s⁻¹ (conjSub s R) := (conjSub_inv_conjSub s R).symm
            _ = conjSub s⁻¹ (conjSub s R') := by rw [h']
            _ = R' := conjSub_inv_conjSub s R'
      apply hd.ne
      have h3 : conjSub (s * s * s) R = R := by
        rw [show s * s * s = 1 by rw [← pow_three', hs3]]
        exact conjSub_one R
      rw [conjSub_mul, conjSub_mul, hR'eq, hRR, hR'eq] at h3
      exact h3.symm
    refine Q3W.not_commutes_self_modelFund3 M.isFundTag M.admissible hG2 hD4 (M.cls_sub hJc)
      fun a ha b hb => ?_
    exact Q3MT.UnitaryBlockStandardPair.comm_of_normalizes3 hK3 (by norm_num) hWJ ha hb
      (hnorm ha) (hnorm hb)
  have hcoatom := hmax R R' x x' hd
  have hlt : conjStabilizer ({R, R'} : Set (Subgroup (modelUniv t k 3 1 Fact.out).K)) < N :=
    lt_of_le_of_ne hCN fun h => hJC (h ▸ hJN)
  have hN : N = ⊤ := hcoatom.2 N hlt
  refine T3.dstarConnected_of_pivot hAΩ fun B hB => ?_
  obtain ⟨g'', hg''⟩ := M.exists_conj_of_fund hG2 hD4 _ hAΩ B hB
  obtain ⟨κ, rfl⟩ := M.surj g''
  have hκ : M.ψ κ ∈ sigmaStarNorm Ω (R.map M.ψ) := by
    have : κ ∈ N := by rw [hN]; trivial
    exact this
  have h1 := (mem_sigmaStarNorm_iff.mp hκ (R.map M.ψ)).mp Relation.ReflTransGen.refl
  rwa [hg''] at h1

end Twin

section SpinStar

open CFSG.ClassicalInvolution.RouteD.TwinY (TwinDatumOn)


variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem dstarConnected_spin_of_pair3 (hΦ : HypOmegaModU (.sl2 3 1) Φ) {t : StatedLieTag} {k : ℕ}
    (M : Ih8Model 3 1 Φ t k 1) (htag : (t = .POmegaOdd ∧ k = 3) ∨ (t = .POmegaMinus ∧ k = 4))
    {A B : Subgroup X} (hA : A ∈ Φ) (hB : B ∈ omegaNbr Φ A) {x x' : X}
    (hxA : IsUniqueInvolution A x) (hxB : IsUniqueInvolution B x')
    (hcen : x * x' ∈ Subgroup.center X) : T3.DStarConnected Φ := by
  have hG2 : t ≠ .G2 := by rcases htag with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
  have hD4 : t ≠ .trialityD4 := by rcases htag with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
  have hnpsl : ¬ (t = .PSL ∧ k = 2) := by
    rintro ⟨h1, -⟩
    rcases htag with ⟨h2, -⟩ | ⟨h2, -⟩ <;> exact absurd (h1.symm.trans h2) (by decide)
  have hSperf : Group.IsPerfect (modelUniv t k 3 1 Fact.out).K :=
    Group.isPerfect_def.2
      (ModelFacts.modelClauseZero t k 3 1 Fact.out (ih8_isFundTag_mf M.isFundTag)
        M.admissible).1.1
  obtain ⟨R, R', y, y', hR, hR', -, -, -, -, hP⟩ :=
    E4G3.e4_pair_of_model3 hΦ M hG2 hD4 hnpsl hSperf hA hB hxA hxB hcen
  have hd : TwinDatumOn t (modelUniv t k 3 1 Fact.out) R R' y y' :=
    ⟨M.cls_sub hR, M.cls_sub hR', hP.ne, hP.comm, hP.hy, hP.hy', hP.cy, hP.cy', hP.hy1, hP.hy'1, by
      rw [inv_eq_of_mul_eq_one_right hP.hy'2]
      exact hP.cen⟩
  rcases htag with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact E4G3.dstarConnected_of_twin3 M hΦ hG2 hD4 Q3TZ.twinPairMax3_odd3
      Q3W.exists_unitaryPair_odd3 hd hR hR'
  · exact E4G3.dstarConnected_of_twin3 M hΦ hG2 hD4 Q3TZ.twinPairMax3_minus4
      Q3W.exists_unitaryPair_minus3 hd hR hR'

end SpinStar

end E4G3

section Final


theorem ih8D4Star3 : Ih8D4Star3 := fun _ _ _ _ hΦ ⟨M⟩ => E4G3.dstarConnected_spin8plus3 hΦ M

theorem e4SecGen3 : E4SecGen3 := by
  intro n hn hih X _ _ hlt Φ hΦ hO hgen hA _ hdisc A hAΦ B hB x x' hxA hxB hcen σ hσ2 _ hσA _ hσnt
  obtain ⟨t, k, htag, ⟨M⟩⟩ := E4G3.e4_tag3 hn hih hlt hΦ hO hgen hA hdisc hAΦ hB
  rcases htag with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | h4 | ⟨rfl, rfl⟩ | h6
  · exact (E4G3.e4_gen_sp3 hΦ M hAΦ hB hxA hxB hcen σ hσ2 hσA hσnt).elim
  · exact E4G3.e4_gen_sl43 hΦ M hAΦ hB hxA hxB hcen σ hσ2 hσA hσnt
  · exact absurd (E4G3.dstarConnected_psu43 hΦ M) hdisc
  · exact absurd (E4G3.dstarConnected_spin_of_pair3 hΦ M (Or.inl h4) hAΦ hB hxA hxB hcen) hdisc
  · exact absurd (E4G3.dstarConnected_spin8plus3 hΦ M) hdisc
  · exact absurd (E4G3.dstarConnected_spin_of_pair3 hΦ M (Or.inr h6) hAΦ hB hxA hxB hcen) hdisc

end Final

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
