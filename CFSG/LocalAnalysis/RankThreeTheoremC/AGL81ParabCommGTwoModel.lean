module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommGTwoChev
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommGTwoSL2
import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusNodeEscape
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrG2
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGTwoBlock
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGTwoData
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGTwoNode

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.GTwo

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime CFSG.RankThree.PartTwo.KFacts
open scoped commutatorElement

section Core

variable {G : Type*} [Group G]

theorem pCoreOf_le (A : Subgroup G) : CFSG.Open.pCoreOf 2 A ≤ A := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2

theorem isPGroup_pCoreOf (A : Subgroup G) : IsPGroup 2 (CFSG.Open.pCoreOf 2 A) :=
  CFSG.pCore_isPGroup.map A.subtype

theorem conj_mem_pCoreOf {A : Subgroup G} {a o : G} (ha : a ∈ A)
    (ho : o ∈ CFSG.Open.pCoreOf 2 A) : a * o * a⁻¹ ∈ CFSG.Open.pCoreOf 2 A := by
  obtain ⟨o', ho', rfl⟩ := ho
  refine ⟨⟨a, ha⟩ * o' * ⟨a, ha⟩⁻¹, (CFSG.pCore_normal (p := 2) (G := ↥A)).conj_mem _ ho' _, ?_⟩
  simp

theorem le_pCoreOf {A N : Subgroup G} (hNA : N ≤ A) (hN : ∀ a ∈ A, ∀ n ∈ N, a * n * a⁻¹ ∈ N)
    (h2 : IsPGroup 2 N) : N ≤ CFSG.Open.pCoreOf 2 A := by
  have hnorm : (N.subgroupOf A).Normal := ⟨fun n hn a => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hN a a.2 n hn⟩
  have hle : N.subgroupOf A ≤ CFSG.pCore 2 ↥A := le_sSup ⟨hnorm, h2.comap_subtype⟩
  intro n hn
  exact ⟨⟨n, hNA hn⟩, hle (by rwa [Subgroup.mem_subgroupOf]), rfl⟩

@[expose] def centMod (A M O : Subgroup G) (hO : ∀ a ∈ A, ∀ o ∈ O, a * o * a⁻¹ ∈ O) :
    Subgroup G where
  carrier := {g | g ∈ A ∧ ∀ s ∈ M, g * s * g⁻¹ * s⁻¹ ∈ O}
  one_mem' := ⟨A.one_mem, fun s _ => by simpa using O.one_mem⟩
  mul_mem' := fun {g h} hg hh => ⟨A.mul_mem hg.1 hh.1, fun s hs => by
    have e : g * h * s * (g * h)⁻¹ * s⁻¹ =
        g * (h * s * h⁻¹ * s⁻¹) * g⁻¹ * (g * s * g⁻¹ * s⁻¹) := by group
    rw [e]
    exact O.mul_mem (hO g hg.1 _ (hh.2 s hs)) (hg.2 s hs)⟩
  inv_mem' := fun {g} hg => ⟨A.inv_mem hg.1, fun s hs => by
    have e : g⁻¹ * s * g⁻¹⁻¹ * s⁻¹ = g⁻¹ * (g * s * g⁻¹ * s⁻¹)⁻¹ * g⁻¹⁻¹ := by group
    rw [e]
    exact hO _ (A.inv_mem hg.1) _ (O.inv_mem (hg.2 s hs))⟩

theorem mem_centMod {A M O : Subgroup G} {hO : ∀ a ∈ A, ∀ o ∈ O, a * o * a⁻¹ ∈ O} {g : G} :
    g ∈ centMod A M O hO ↔ g ∈ A ∧ ∀ s ∈ M, g * s * g⁻¹ * s⁻¹ ∈ O :=
  Iff.rfl

theorem mem_centMod_of_mem {A M O : Subgroup G} {hO : ∀ a ∈ A, ∀ o ∈ O, a * o * a⁻¹ ∈ O}
    (hOA : O ≤ A) (hMA : M ≤ A) {u : G} (hu : u ∈ O) : u ∈ centMod A M O hO := by
  refine ⟨hOA hu, fun s hs => ?_⟩
  have e : u * s * u⁻¹ * s⁻¹ = u * (s * u⁻¹ * s⁻¹) := by group
  rw [e]
  exact O.mul_mem hu (hO s (hMA hs) _ (O.inv_mem hu))

end Core


variable {K : Type} [Field K]

theorem rankOne_simple [Finite K] [CharP K 2] (h4 : 4 ≤ Nat.card K) (i : Fin (Tag.rank .G2)) :
    IsSimpleGroup ↥(rankOne (g2Datum K).rootGroup i) ∧
      ∃ a b : ↥(rankOne (g2Datum K).rootGroup i), a * b ≠ b * a := by
  obtain ⟨eL⟩ := CFSG.AGLEmbedding.LeviBlock.nonempty_sl2_mulEquiv_rankOne_g2 (F := K) i
  have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) K) := sl2_isSimpleGroup h4
  exact ⟨eL.symm.isSimpleGroup, ⟨eL (sl2Upper 1 * sl2Lower 1), eL (sl2Upper 1), fun h =>
    sl2_upper_lower_not_commute (eL.injective (by simpa [map_mul] using h))⟩⟩

theorem exists_sl2_param (i : Fin (Tag.rank .G2)) :
    ∃ φ : Matrix.SpecialLinearGroup (Fin 2) K →* adjointGroup .G2 K, Function.Injective φ ∧
      (∀ c, φ (sl2Upper c) = xPar (rootOperatorFamily .G2) (Pi.single i 1) c) ∧
      φ.range = rankOne (g2Datum K).rootGroup i := by
  obtain ⟨φ, hφ, hx, hy⟩ := g2_exists_sl2_hom (K := K) i
  have hx' : ∀ c, φ (sl2Upper c) = xPar (rootOperatorFamily .G2) (Pi.single i 1) c :=
    fun c => (hx c).trans (xPar_simple i c).symm
  have hy' : ∀ c, φ (sl2Lower c) = xPar (rootOperatorFamily .G2) (-Pi.single i 1) c :=
    fun c => (hy c).trans (xPar_neg_simple i c).symm
  have hr := rankOne_eq_range_of_sl2
    (adjDatum_isParametrization (F := rootOperatorFamily .G2) (K := K)
      (RootSystem.ofCartan (g2Datum K).isFiniteType (g2Datum K).divisible)
      (adjDatum_roots (rootOperatorFamily .G2) K)) hx' hy'
  exact ⟨φ, hφ, hx', hr.symm⟩

theorem xPar_mem_rankOne (i : Fin (Tag.rank .G2)) (c : K) :
    xPar (rootOperatorFamily .G2) (Pi.single i 1) c ∈ rankOne (g2Datum K).rootGroup i :=
  le_sup_left (a := (g2Datum K).rootGroup (Pi.single i 1)) (xPar_mem (isRoot_single .G2 i) c)

variable [Finite K] [CharP K 2]

theorem exists_conj_mul_g2FieldHom {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f)
    (α : MulAut (adjointGroup .G2 K)) :
    ∃ (g : adjointGroup .G2 K) (σ : K ≃+* K), α = MulAut.conj g * g2FieldHom K σ := by
  obtain ⟨⟨g, σ⟩, hgσ, -⟩ :=
    (CFSG.ComponentClassification.UnbalancedCatalog.even_G2_exact_automorphism_normal_form hf K
      hK).1 α
  exact ⟨g, σ, (forall_eq_iff_eq_conj_mul_g2FieldHom α g σ).1 hgσ⟩

theorem exists_mem_conj_mul {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f)
    {A : Subgroup (adjointGroup .G2 K)} (hBA : borel (g2Datum K) (torus (τ := .G2) K) ≤ A)
    {α : MulAut (adjointGroup .G2 K)} (hA : ∀ a ∈ A, α a ∈ A) :
    ∃ g ∈ A, ∃ σ : K ≃+* K, α = MulAut.conj g * g2FieldHom K σ := by
  haveI : Finite ↥(adjointGroup .G2 K) := generated_group_finite .G2 _
  obtain ⟨g, σ, rfl⟩ := exists_conj_mul_g2FieldHom hf hK α
  refine ⟨g, mem_of_mem_normalizer_of_borel_le hBA
    (Subgroup.mem_normalizer_fintype fun a ha => ?_), σ, rfl⟩
  have h1 : (g2FieldHom K σ)⁻¹ a ∈ A := by
    rw [← map_inv]
    exact g2FieldHom_mem_of_borel_le σ⁻¹ hBA ha
  have h2 := hA _ h1
  rwa [MulAut.mul_apply, MulAut.apply_inv_self, MulAut.conj_apply] at h2

theorem eq_one_of_conj_mul_mem (h4 : 4 ≤ Nat.card K) {A : Subgroup (adjointGroup .G2 K)}
    (hBA : borel (g2Datum K) (torus (τ := .G2) K) ≤ A) {i : Fin (Tag.rank .G2)}
    (hI : negIndices (g2Datum K) A = {i}) {g : adjointGroup .G2 K} (hg : g ∈ A) (σ : K ≃+* K)
    (hW : ∀ s ∈ rankOne (g2Datum K).rootGroup i,
      g * g2FieldHom K σ s * g⁻¹ * s⁻¹ ∈ CFSG.Open.pCoreOf 2 A) : σ = 1 := by
  haveI : Finite ↥(adjointGroup .G2 K) := generated_group_finite .G2 _
  have hB := borelQuotient_g2 (CFSG.AGLEmbedding.ParabAutIrr.adjointQuotientEquiv K).symm
  set M := rankOne (g2Datum K).rootGroup i with hMdef
  set U := posUnipotentExcept (g2Datum K) i with hUdef
  set T := ⨆ k, torus (τ := .G2) K k with hTdef
  set O := CFSG.Open.pCoreOf 2 A with hOdef
  obtain ⟨hMs, hnc⟩ := rankOne_simple h4 i
  have hMA : M ≤ A := rankOne_le_of_mem_negIndices hBA (by rw [hI]; rfl)
  have hUA : U ≤ A := CFSG.AGLEmbedding.LeviBlock.posUnipotentExcept_le_of_borel_le hBA i
  have hAU := CFSG.AGLEmbedding.LeviBlock.le_normalizer_posUnipotentExcept_of_negIndices_eq hB
    hBA hI
  have hUO : U ≤ O := le_pCoreOf hUA
    (fun a ha n hn => (Subgroup.mem_normalizer_iff.1 (hAU ha) n).1 hn)
    (CFSG.AGLEmbedding.LeviBlock.isPGroup_posUnipotentExcept hB i)
  have hMO : M ⊓ O = ⊥ := CFSG.AGLEmbedding.LeviBlock.inf_eq_bot_of_simple_of_isPGroup hnc
    (fun m hm => Subgroup.mem_normalizer_fintype fun o ho => conj_mem_pCoreOf (hMA hm) ho)
    (isPGroup_pCoreOf A)
  have hTA : T ≤ A := (le_sup_left (b := posUnipotent (g2Datum K))).trans hBA
  have hTN : T ≤ Subgroup.normalizer ((M ⊔ U : Subgroup (adjointGroup .G2 K)) :
      Set (adjointGroup .G2 K)) := fun t ht =>
    CFSG.AGLEmbedding.ParabAutIrr.mem_normalizer_sup (iSup_torus_le_normalizer_rankOne hB.ct i ht)
      (CFSG.AGLEmbedding.ToralCensus.iSup_torus_le_normalizer_posUnipotentExcept hB.ct i ht)
  have hMU : M ≤ Subgroup.normalizer (U : Set (adjointGroup .G2 K)) :=
    rankOne_le_normalizer_posUnipotentExcept hB.ct hB.extras i
  have hg' : g ∈ ((T ⊔ (M ⊔ U) : Subgroup (adjointGroup .G2 K)) : Set (adjointGroup .G2 K)) :=
    CFSG.AGLEmbedding.LeviBlock.le_torus_sup_of_negIndices_eq hB hBA hI hg
  rw [Subgroup.coe_mul_of_left_le_normalizer_right T (M ⊔ U) hTN] at hg'
  obtain ⟨t, ht, w, hw, rfl⟩ := hg'
  have hw' : w ∈ ((M ⊔ U : Subgroup (adjointGroup .G2 K)) : Set (adjointGroup .G2 K)) := hw
  rw [Subgroup.coe_mul_of_left_le_normalizer_right M U hMU] at hw'
  obtain ⟨m, hm, u, hu, rfl⟩ := hw'
  obtain ⟨lam, hlam⟩ := exists_torus_conj_xPar i (T.inv_mem ht)
  obtain ⟨φ, hφ, hφx, hφr⟩ := exists_sl2_param (K := K) i
  have hm' : m ∈ φ.range := by rw [hφr]; exact hm
  obtain ⟨m', rfl⟩ := hm'
  set x : K → adjointGroup .G2 K := xPar (rootOperatorFamily .G2) (Pi.single i 1) with hxdef
  have key : ∀ c : K, φ m' * x (σ c) * (φ m')⁻¹ = x (lam * c) := by
    intro c
    have htA : t ∈ A := hTA ht
    have huO : u ∈ O := hUO hu
    have hxσA : x (σ c) ∈ A := hMA (xPar_mem_rankOne i (σ c))
    have hE := hW (x c) (xPar_mem_rankOne i c)
    rw [g2FieldHom_xPar] at hE
    have hE' := conj_mem_pCoreOf (A.inv_mem htA) hE
    have hq : u * x (σ c) * u⁻¹ * (x (σ c))⁻¹ ∈ O := by
      have e : u * x (σ c) * u⁻¹ * (x (σ c))⁻¹ = u * (x (σ c) * u⁻¹ * (x (σ c))⁻¹) := by group
      rw [e]
      exact O.mul_mem huO (conj_mem_pCoreOf hxσA (O.inv_mem huO))
    have hq' := conj_mem_pCoreOf (hMA hm) hq
    have hyz : φ m' * x (σ c) * (φ m')⁻¹ * (t⁻¹ * x c * t⁻¹⁻¹)⁻¹ ∈ O := by
      have e : φ m' * x (σ c) * (φ m')⁻¹ * (t⁻¹ * x c * t⁻¹⁻¹)⁻¹ =
          (φ m' * (u * x (σ c) * u⁻¹ * (x (σ c))⁻¹) * (φ m')⁻¹)⁻¹ *
            (t⁻¹ * (t * (φ m' * u) * x (σ c) * (t * (φ m' * u))⁻¹ * (x c)⁻¹) * t⁻¹⁻¹) := by
        group
      rw [e]
      exact O.mul_mem (O.inv_mem hq') hE'
    have hyzM : φ m' * x (σ c) * (φ m')⁻¹ * (t⁻¹ * x c * t⁻¹⁻¹)⁻¹ ∈ M := by
      rw [hlam c]
      exact M.mul_mem (M.mul_mem (M.mul_mem hm (xPar_mem_rankOne i _)) (M.inv_mem hm))
        (M.inv_mem (xPar_mem_rankOne i _))
    have h1 : φ m' * x (σ c) * (φ m')⁻¹ * (t⁻¹ * x c * t⁻¹⁻¹)⁻¹ = 1 := by
      have := (show _ ∈ M ⊓ O from ⟨hyzM, hyz⟩)
      rwa [hMO, Subgroup.mem_bot] at this
    rw [← hlam c]
    exact mul_inv_eq_one.mp h1
  have hsl : ∀ s : K, m' * sl2Upper (σ s) * m'⁻¹ = sl2Upper ((lam : K) * s) := fun s =>
    hφ (by rw [map_mul, map_mul, map_inv, hφx, hφx, key s])
  exact eq_refl_of_conj_sl2Upper σ m' lam hsl

theorem commutator_mem_of_centMod (h4 : 4 ≤ Nat.card K) {A : Subgroup (adjointGroup .G2 K)}
    (hBA : borel (g2Datum K) (torus (τ := .G2) K) ≤ A) {i : Fin (Tag.rank .G2)}
    (hI : negIndices (g2Datum K) A = {i}) {g₁ g₂ : adjointGroup .G2 K} (hg₁ : g₁ ∈ A)
    (hg₂ : g₂ ∈ A)
    (hW₁ : ∀ s ∈ rankOne (g2Datum K).rootGroup i, g₁ * s * g₁⁻¹ * s⁻¹ ∈ CFSG.Open.pCoreOf 2 A)
    (hW₂ : ∀ s ∈ rankOne (g2Datum K).rootGroup i, g₂ * s * g₂⁻¹ * s⁻¹ ∈ CFSG.Open.pCoreOf 2 A) :
    ⁅g₁, g₂⁆ ∈ posUnipotentExcept (g2Datum K) i := by
  haveI : Finite ↥(adjointGroup .G2 K) := generated_group_finite .G2 _
  have hB := borelQuotient_g2 (CFSG.AGLEmbedding.ParabAutIrr.adjointQuotientEquiv K).symm
  set M := rankOne (g2Datum K).rootGroup i with hMdef
  set U := posUnipotentExcept (g2Datum K) i with hUdef
  set O := CFSG.Open.pCoreOf 2 A with hOdef
  obtain ⟨hMs, hnc⟩ := rankOne_simple h4 i
  have hMA : M ≤ A := rankOne_le_of_mem_negIndices hBA (by rw [hI]; rfl)
  have hUA : U ≤ A := CFSG.AGLEmbedding.LeviBlock.posUnipotentExcept_le_of_borel_le hBA i
  have hAU := CFSG.AGLEmbedding.LeviBlock.le_normalizer_posUnipotentExcept_of_negIndices_eq hB
    hBA hI
  have hUO : U ≤ O := le_pCoreOf hUA
    (fun a ha n hn => (Subgroup.mem_normalizer_iff.1 (hAU ha) n).1 hn)
    (CFSG.AGLEmbedding.LeviBlock.isPGroup_posUnipotentExcept hB i)
  have hMO : M ⊓ O = ⊥ := CFSG.AGLEmbedding.LeviBlock.inf_eq_bot_of_simple_of_isPGroup hnc
    (fun m hm => Subgroup.mem_normalizer_fintype fun o ho => conj_mem_pCoreOf (hMA hm) ho)
    (isPGroup_pCoreOf A)
  have hO : ∀ a ∈ A, ∀ o ∈ O, a * o * a⁻¹ ∈ O := fun a ha o ho => conj_mem_pCoreOf ha ho
  have hc : ⁅g₁, g₂⁆ ∈ centMod A M O hO := by
    rw [commutatorElement_def]
    have h₁ : g₁ ∈ centMod A M O hO := ⟨hg₁, hW₁⟩
    have h₂ : g₂ ∈ centMod A M O hO := ⟨hg₂, hW₂⟩
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ h₁ h₂)
      (Subgroup.inv_mem _ h₁)) (Subgroup.inv_mem _ h₂)
  have hMU : M ≤ Subgroup.normalizer (U : Set (adjointGroup .G2 K)) :=
    rankOne_le_normalizer_posUnipotentExcept hB.ct hB.extras i
  have hk : ⁅g₁, g₂⁆ ∈ ((M ⊔ U : Subgroup (adjointGroup .G2 K)) : Set (adjointGroup .G2 K)) :=
    CFSG.AGLEmbedding.LeviBlock.commutator_mem_of_negIndices_eq hB hBA hI hg₁ hg₂
  rw [Subgroup.coe_mul_of_left_le_normalizer_right M U hMU] at hk
  obtain ⟨m, hm, u, hu, hmu⟩ := hk
  have hmc : m ∈ centMod A M O hO := by
    have e : m = ⁅g₁, g₂⁆ * u⁻¹ := by rw [← hmu, mul_inv_cancel_right]
    rw [e]
    exact Subgroup.mul_mem _ hc (Subgroup.inv_mem _ (mem_centMod_of_mem (pCoreOf_le A) hMA
      (hUO hu)))
  have hcen : (⟨m, hm⟩ : ↥M) ∈ Subgroup.center ↥M := by
    rw [Subgroup.mem_center_iff]
    intro s
    have h1 : m * s * m⁻¹ * (s : adjointGroup .G2 K)⁻¹ ∈ M ⊓ O :=
      ⟨M.mul_mem (M.mul_mem (M.mul_mem hm s.2) (M.inv_mem hm)) (M.inv_mem s.2), hmc.2 s s.2⟩
    rw [hMO, Subgroup.mem_bot] at h1
    apply Subtype.ext
    have h2 : m * s * m⁻¹ = s := mul_inv_eq_one.mp h1
    simp only [Subgroup.coe_mul]
    calc (s : adjointGroup .G2 K) * m = m * s * m⁻¹ * m := by rw [h2]
      _ = m * s := by group
  have hZ : Subgroup.center ↥M = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥M) with h | h
    · exact h
    · obtain ⟨a, b, hab⟩ := hnc
      exact absurd (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top a) b).symm hab
  rw [hZ, Subgroup.mem_bot] at hcen
  have hm1 : m = 1 := congrArg Subtype.val hcen
  rw [← hmu, hm1]
  simpa using hu

theorem g2_model_comm {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f)
    {A : Subgroup (adjointGroup .G2 K)} (hBA : borel (g2Datum K) (torus (τ := .G2) K) ≤ A)
    {i : Fin (Tag.rank .G2)} (hI : negIndices (g2Datum K) A = {i})
    {α₁ α₂ : MulAut (adjointGroup .G2 K)} (hA₁ : ∀ a ∈ A, α₁ a ∈ A) (hA₂ : ∀ a ∈ A, α₂ a ∈ A)
    (hW₁ : ∀ s ∈ rankOne (g2Datum K).rootGroup i, α₁ s * s⁻¹ ∈ CFSG.Open.pCoreOf 2 A)
    (hW₂ : ∀ s ∈ rankOne (g2Datum K).rootGroup i, α₂ s * s⁻¹ ∈ CFSG.Open.pCoreOf 2 A)
    (hodd : Odd (orderOf ⁅α₁, α₂⁆)) : ⁅α₁, α₂⁆ = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hB := borelQuotient_g2 (CFSG.AGLEmbedding.ParabAutIrr.adjointQuotientEquiv K).symm
  obtain ⟨g₁, hg₁, σ₁, rfl⟩ := exists_mem_conj_mul hf hK hBA hA₁
  obtain ⟨g₂, hg₂, σ₂, rfl⟩ := exists_mem_conj_mul hf hK hBA hA₂
  have hσ₁ : σ₁ = 1 := eq_one_of_conj_mul_mem h4 hBA hI hg₁ σ₁ fun s hs => by
    simpa [MulAut.conj_apply] using hW₁ s hs
  have hσ₂ : σ₂ = 1 := eq_one_of_conj_mul_mem h4 hBA hI hg₂ σ₂ fun s hs => by
    simpa [MulAut.conj_apply] using hW₂ s hs
  subst hσ₁ hσ₂
  simp only [map_one, mul_one] at hW₁ hW₂ hodd ⊢
  have hu := commutator_mem_of_centMod h4 hBA hI hg₁ hg₂
    (fun s hs => by simpa [MulAut.conj_apply] using hW₁ s hs)
    (fun s hs => by simpa [MulAut.conj_apply] using hW₂ s hs)
  rw [← map_commutatorElement] at hodd ⊢
  obtain ⟨k, hk⟩ := CFSG.AGLEmbedding.LeviBlock.isPGroup_posUnipotentExcept hB i ⟨_, hu⟩
  have hk' : (MulAut.conj ⁅g₁, g₂⁆) ^ 2 ^ k = 1 := by
    rw [← map_pow, show ⁅g₁, g₂⁆ ^ 2 ^ k = 1 from congrArg Subtype.val hk, map_one]
  have hdvd := orderOf_dvd_of_pow_eq_one hk'
  have hcop : Nat.Coprime (orderOf (MulAut.conj ⁅g₁, g₂⁆)) (2 ^ k) :=
    Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hodd)
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop hdvd)

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.GTwo
