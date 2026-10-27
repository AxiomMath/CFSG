module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34PushUp
public import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowContainment

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

theorem L34Squeeze.exists_isSylowTwoOf_normalized {p : ℕ} (hp : p.Prime) {A X : Subgroup G}
    (hA : IsPGroup p A) (hX : Nat.Coprime p (Nat.card X))
    (hAX : A ≤ Subgroup.normalizer (X : Set G)) :
    ∃ V : Subgroup G, IsSylowTwoOf V X ∧ A ≤ Subgroup.normalizer (V : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : MulDistribMulAction A X := MulDistribMulAction.compHom X (Subgroup.inclusion hAX)
  have hsmul : ∀ (a : A) (x : X), ((a • x : X) : G) = a * x * (a : G)⁻¹ := fun _ _ => rfl
  obtain ⟨P₂, -, hPinv⟩ := CFSG.SignalizerFunctor.Helpers.invariant_sylow_containing p 2 hp
    Nat.prime_two hA hX (⊥ : Subgroup X) IsPGroup.of_bot (fun a x hx => by
      rw [Subgroup.mem_bot] at hx ⊢
      rw [hx, smul_one])
  set V := (P₂ : Subgroup X).map X.subtype with hVdef
  have hconj : ∀ b ∈ A, ∀ y ∈ V, b * y * b⁻¹ ∈ V := by
    rintro b hb _ ⟨x, hx, rfl⟩
    have hmem := Subgroup.smul_mem_pointwise_smul x (⟨b, hb⟩ : A) (P₂ : Subgroup X) hx
    rw [← Sylow.pointwise_smul_def, hPinv ⟨b, hb⟩] at hmem
    exact ⟨_, hmem, hsmul _ _⟩
  refine ⟨V, ⟨Subgroup.map_subtype_le _, P₂.isPGroup'.map X.subtype, ?_⟩, ?_⟩
  · have hsub : V.subgroupOf X = (P₂ : Subgroup X) :=
      Subgroup.comap_map_eq_self_of_injective X.subtype_injective _
    rw [hsub]
    exact Sylow.not_dvd_index P₂
  · intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro g
    refine ⟨fun hg => hconj a ha g hg, fun hg => ?_⟩
    have := hconj a⁻¹ (A.inv_mem ha) _ hg
    simpa [mul_assoc] using this

variable {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.twoCore_inf_twoCore_ne_bot_of_le (hd : D1OneSmallData p P M H R Rbar K)
    (hQH : pCoreOf 2 M ≤ H) : pCoreOf 2 M ⊓ pCoreOf 2 H ≠ ⊥ := by
  intro hbot
  have hSM : pCoreOf 2 H ≤ M := hd.cfg.ext.toD1Escape.twoCore_le
  have hMQ : M ≤ Subgroup.normalizer (pCoreOf 2 M : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M
  have hHS : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hcomm : pCoreOf 2 M ≤ Subgroup.centralizer (pCoreOf 2 H : Set G) := by
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hc1 : q * s * q⁻¹ * s⁻¹ ∈ pCoreOf 2 H :=
      (pCoreOf 2 H).mul_mem ((Subgroup.mem_normalizer_iff.mp (hHS (hQH hq)) s).mp hs)
        ((pCoreOf 2 H).inv_mem hs)
    have hc2 : q * s * q⁻¹ * s⁻¹ ∈ pCoreOf 2 M := by
      have h1 : s * q⁻¹ * s⁻¹ ∈ pCoreOf 2 M :=
        (Subgroup.mem_normalizer_iff.mp (hMQ (hSM hs)) q⁻¹).mp ((pCoreOf 2 M).inv_mem hq)
      have h2 := (pCoreOf 2 M).mul_mem hq h1
      simpa only [mul_assoc] using h2
    have hc : q * s * q⁻¹ * s⁻¹ ∈ pCoreOf 2 M ⊓ pCoreOf 2 H := ⟨hc2, hc1⟩
    rw [hbot, Subgroup.mem_bot] at hc
    calc s * q = (q * s * q⁻¹ * s⁻¹)⁻¹ * (q * s) := by group
      _ = q * s := by rw [hc, inv_one, one_mul]
  have hQS : pCoreOf 2 M ≤ pCoreOf 2 H := fun q hq =>
    hd.cfg.glob.charTwo H hd.cfg.ext.maxTwoLocal_H.1 ⟨hQH hq, hcomm hq⟩
  apply twoLocal_pCoreOf_ne_bot hd.cfg.ext.maxTwoLocal_M.1
  rw [eq_bot_iff, ← hbot]
  exact le_inf le_rfl hQS

@[expose] def D1SmallPushUpL34 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)), D1OneSmallData p P M H R Rbar K →
    ∀ z : G, D1SmallCZElt p H R K z → D1CzB0 p R z →
    p = 3 → IsLinThreeFour K → ¬ D1SmallOuterR p H Rbar K →
    Subgroup.centralizer ({z} : Set G) ≤ H →
    ∀ V : Subgroup G, IsSylowTwoOf V (GLBPrimeCore p (H ⊓ M)) →
      R ≤ Subgroup.normalizer (V : Set G) →
    ∃ C : Subgroup G, C ≤ V ∧ C ≠ ⊥ ∧ (C.subgroupOf V).Characteristic ∧
      (∀ h ∈ H, ∃ a ∈ H ⊓ Subgroup.normalizer (C : Set G), ∃ b ∈ H ⊓ M, h = a * b) ∧
      (∀ t ∈ d1LiftX p H R K, t ≠ 1 → ∀ s ∈ d1LiftX p H R K, s ≠ 1 →
        ∃ n ∈ (H ⊓ Subgroup.normalizer (C : Set G)) ⊓ Subgroup.normalizer (R : Set G),
          n * z * n⁻¹ = z ∧ (∀ x ∈ d1LiftX p H R K, n * x * n⁻¹ ∈ d1LiftX p H R K) ∧
          n * t * n⁻¹ = s)

theorem D1OneSmallData.false_of_hasPrimeConstraint_of_pushUp (hPU : D1SmallPushUpL34)
    (hβ : KFactBeta) (hα : KFactAlphaW) (h2 : D1CaseTwo) (h3 : D1CaseThree)
    (hUE : KFactUPrimeExc) (hOrb : KFactSmallOrbits) (hExp : KFactSmallSylowExp)
    (hOut : KFactSmallOutPPrime) (hSh3 : KFactSmallSylowShapeThree) (hO : KFactSmallThreeOrders)
    (hNO : KFactL34NotOrthogonal) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hd : D1OneSmallData p P M H R Rbar K) {z : G} (hz : D1SmallCZElt p H R K z)
    (hB0 : D1CzB0 p R z) (hp3 : p = 3) (hL : IsLinThreeFour K)
    (hOR : ¬ D1SmallOuterR p H Rbar K)
    (hV : Subgroup.normalizer
      (pCoreOf 2 (GLBPrimeCore p (Subgroup.centralizer ({z} : Set G))) : Set G) ≤ H)
    (hS : pCoreOf 2 (H ⊓ M) ≠ pCoreOf 2 H) (hcon : HasPrimeConstraint (G := M) p) : False := by
  subst hp3
  have hp : Nat.Prime 3 := Nat.prime_three
  have hCz : Subgroup.centralizer ({z} : Set G) ≤ H :=
    (le_normalizer_glbPrimeCore 3 _).trans
      ((CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _).trans hV)
  obtain ⟨V, hsyl, hRV⟩ := L34Squeeze.exists_isSylowTwoOf_normalized hp hd.cfg.ext.isPGroup
    (glbPrimeCore_coprime 3 (H ⊓ M))
    (hd.cfg.ext.le_inf.trans (le_normalizer_glbPrimeCore 3 (H ⊓ M)))
  obtain ⟨C, hCV, hC1, hchar, hJM, htr⟩ :=
    hPU G 3 P M H R Rbar K hd z hz hB0 rfl hL hOR hCz V hsyl hRV
  have hQH : pCoreOf 2 M ≤ H :=
    (hd.normalizer_twoCore_inf_eq_ib hUE hO hNO h93 hD2 rfl hL hS).2.2.2.trans
      ((RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 (H ⊓ M)).trans inf_le_left)
  exact hd.false_of_pushingUp_l34 hβ hα h2 h3 hUE hOrb hExp hOut hSh3 hO hz hB0 rfl hL hOR hCz
    (hd.twoCore_inf_twoCore_ne_bot_of_le hQH) hcon hsyl hRV hCV hC1 hchar inf_le_left hJM htr
    inf_le_right

end CFSG.AGLEmbedding
