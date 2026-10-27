module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sylow5OmegaE8Defs
public import CFSG.LieType.SeitzGeneration.ExcTorusE8Twenty

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sylow5Omega

open CFSG.Open CFSG.Blueprint.Chevalley

section Witness

open CFSG.Blueprint CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.SeitzGeneration
open CFSG.LieType.AlgebraicGroups (exceptional_all_characteristic_field_Lang_surjectivity)
open scoped Matrix

private theorem prod_zpow_eq_zpow_sum_e8w {G ι : Type*} [CommGroup G] (ξ : G) (s : Finset ι)
    (f : ι → ℤ) : ∏ i ∈ s, ξ ^ f i = ξ ^ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add]

private theorem rootChar_zpow_dotProduct {τ : Tag} {K : Type} [Field K] (ζ : Kˣ)
    (x v : Fin τ.rank → ℤ) : rootChar (fun i => ζ ^ x i) v = ζ ^ (x ⬝ᵥ v) := by
  simp only [rootChar, ← zpow_mul, dotProduct]
  exact prod_zpow_eq_zpow_sum_e8w ζ Finset.univ _

private theorem zpow_eq_zpow_of_five_dvd {G : Type*} [Group G] {ζ : G} (hζ : ζ ^ (5 : ℤ) = 1)
    {m m' : ℤ} (h : (5 : ℤ) ∣ m - m') : ζ ^ m = ζ ^ m' := by
  obtain ⟨k, hk⟩ := h
  rw [show m = m' + 5 * k by linarith, zpow_add, zpow_mul, hζ, one_zpow, mul_one]

private theorem weyl_pow_smul_eq {τ : Tag} {w : WeylGroup τ}
    {A : Matrix (Fin τ.rank) (Fin τ.rank) ℤ} (hw : ∀ u, w • u = A *ᵥ u) (k : ℕ)
    (u : Fin τ.rank → ℤ) : (w ^ k) • u = (A ^ k) *ᵥ u := by
  induction k generalizing u with
  | zero => simp
  | succ k ih => rw [pow_succ, mul_smul, hw, ih, pow_succ, Matrix.mulVec_mulVec]

private theorem weyl_eq_one_of_mulVec
    {τ : Tag} {w : WeylGroup τ} {A : Matrix (Fin τ.rank) (Fin τ.rank) ℤ}
    (hw : ∀ u, w • u = A *ᵥ u) (hA : A = 1) : w = 1 := by
  refine eq_one_of_forall_height_pos fun i => ?_
  rw [hw, hA, Matrix.one_mulVec, CFSG.LieType.Chevalley.height_single]
  exact one_pos

private theorem canonicalRep_pow_conj_rootDiagUnit
    {τ : Tag} {K : Type} [Field K] (w : WeylGroup τ) (k : ℕ)
    (b : Fin τ.rank → Kˣ) :
    canonicalRep (coxeterSystem τ) K w ^ k * rootDiagUnit τ b *
        (canonicalRep (coxeterSystem τ) K w ^ k)⁻¹ = rootDiagUnit τ (weylTuple (w ^ k) b) := by
  induction k generalizing b with
  | zero => simp [weylTuple_one]
  | succ k ih =>
    rw [pow_succ, pow_succ, ← weylTuple_weylTuple, ← ih, ← canonicalRep_conj_rootDiagUnit]
    group

private theorem units_map_entrywise_rootDiagUnit {τ : Tag} {K : Type} [Field K] (σ : K →+* K)
    (a : Fin τ.rank → Kˣ) :
    Units.map (entrywiseHom σ) (rootDiagUnit τ a) =
      rootDiagUnit τ fun i => Units.map σ.toMonoidHom (a i) :=
  Units.ext (CFSG.LieType.Chevalley.entrywise_rootDiag σ a)

private theorem map_weylTuple_e8w {τ : Tag} {K : Type} [Field K] (σ : K →+* K)
    (w : WeylGroup τ) (b : Fin τ.rank → Kˣ) :
    (fun i => Units.map σ.toMonoidHom (weylTuple w b i)) =
      weylTuple w fun i => Units.map σ.toMonoidHom (b i) :=
  funext fun _ => map_rootChar σ b _

private theorem weylTuple_pow_e8w {τ : Tag} {K : Type} [Field K] (w : WeylGroup τ)
    (b : Fin τ.rank → Kˣ) (k : ℕ) : weylTuple w b ^ k = weylTuple w (b ^ k) := by
  funext i
  simp only [weylTuple, rootChar, Pi.pow_apply, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]

private theorem weylTuple_one_tuple {τ : Tag} {K : Type} [Field K] (w : WeylGroup τ) :
    weylTuple w (1 : Fin τ.rank → Kˣ) = 1 := by
  funext i
  simp [weylTuple, rootChar]

private theorem pow_sub_one_eq_one_of_fixed
    {τ : Tag} {L : Type} [Field L] (Fr : L →+* L) {q : ℕ}
    (hFr : ∀ c, Fr c = c ^ q) (hq : 1 ≤ q) {h : ModGL τ L} (hh : h ∈ torusGroup τ L)
    (hfix : Units.map (entrywiseHom Fr) h = h) : h ^ (q - 1) = 1 := by
  obtain ⟨t, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
  rw [units_map_entrywise_rootDiagUnit] at hfix
  have ht := rootDiagUnit_injective (τ := τ) (K := L) hfix
  have ht' : t ^ (q - 1) = 1 := by
    funext i
    have h1 := congrFun ht i
    rw [CTTorus.map_units_eq_pow hFr] at h1
    have h3 : t i ^ (q - 1) * t i = 1 * t i := by
      rw [← pow_succ, Nat.sub_add_cancel hq, h1, one_mul]
    simpa using mul_right_cancel h3
  calc rootDiagUnit τ t ^ (q - 1) = rootDiagUnit τ (t ^ (q - 1)) :=
        ((rootDiagUnitHom τ L).map_pow t (q - 1)).symm
    _ = 1 := by rw [ht', rootDiagUnit_one]

private theorem vecMul_e8Twenty_pow (v : List ℤ) (k : ℕ) :
    toVec Tag.E8.rank v ᵥ* wordMat Tag.E8 e8TwentyWord ^ k =
      toVec Tag.E8.rank (lmulVecT Tag.E8.rank (lpow Tag.E8.rank e8TwentyMat k) v) := by
  rw [toVec_lmulVecT, toMat_lpow, ← e8Twenty_wordMat, Matrix.mulVec_transpose]

private theorem e8w_check2a : ∀ i : Fin Tag.E8.rank,
    (toVec Tag.E8.rank (lmulVecT Tag.E8.rank (lpow Tag.E8.rank e8TwentyMat 5)
      [0, 0, 0, 1, 4, 2, 2, 1]) i - 2 * toVec Tag.E8.rank [0, 0, 0, 1, 4, 2, 2, 1] i) % 5 = 0 := by
  decide +kernel

private theorem e8w_check2b :
    (toVec Tag.E8.rank (lmulVecT Tag.E8.rank (lpow Tag.E8.rank e8TwentyMat 4)
      [0, 0, 0, 1, 4, 2, 2, 1]) 2 - toVec Tag.E8.rank [0, 0, 0, 1, 4, 2, 2, 1] 2) % 5 ≠ 0 := by
  decide +kernel

private theorem e8w_check3a : ∀ i : Fin Tag.E8.rank,
    (toVec Tag.E8.rank (lmulVecT Tag.E8.rank (lpow Tag.E8.rank e8TwentyMat 5)
      [0, 0, 0, 1, 4, 3, 1, 1]) i - 3 * toVec Tag.E8.rank [0, 0, 0, 1, 4, 3, 1, 1] i) % 5 = 0 := by
  decide +kernel

private theorem e8w_check3b :
    (toVec Tag.E8.rank (lmulVecT Tag.E8.rank (lpow Tag.E8.rank e8TwentyMat 4)
      [0, 0, 0, 1, 4, 3, 1, 1]) 2 - toVec Tag.E8.rank [0, 0, 0, 1, 4, 3, 1, 1] 2) % 5 ≠ 0 := by
  decide +kernel

section Core


private theorem canonicalRep_pow_mem_torusGroup {τ : Tag} {L : Type} [Field L] {w : WeylGroup τ}
    {k : ℕ} (hk : w ^ k = 1) : canonicalRep (coxeterSystem τ) L w ^ k ∈ torusGroup τ L := by
  have hmem := CFSG.LieType.Chevalley.canonicalRep_mem_monomialSubgroup (τ := τ) L w
  have hn : canonicalRep (coxeterSystem τ) L w ^ k ∈ monomialSubgroup τ L := pow_mem hmem k
  obtain ⟨ρ, -, hρ, -, -, hρker⟩ := (Weyl_normalizer_quotient τ L).2.1
  have hcan : ρ ⟨_, hmem⟩ = w := (hρ _).unique (mapsRootLines_canonicalRep w)
  have hker : (⟨_, hn⟩ : monomialSubgroup τ L) ∈ ρ.ker := by
    have h1 : (⟨_, hn⟩ : monomialSubgroup τ L) = ⟨_, hmem⟩ ^ k := Subtype.ext (by simp)
    rw [MonoidHom.mem_ker, h1, map_pow, hcan, hk]
  rw [hρker, Subgroup.mem_subgroupOf] at hker
  exact hker

private theorem lang_conjugator_any (τ : Tag) {ℓ f : ℕ} [Fact ℓ.Prime] (hf : 1 ≤ f) (L : Type)
    [Field L] [IsAlgClosed L] [CharP L ℓ] {n : ModGL τ L} (hn : n ∈ adjointGroup τ L) :
    ∃ g0 : ModGL τ L, g0 ∈ adjointGroup τ L ∧
      Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g0 = g0 * n := by
  obtain ⟨S, hS, hLang⟩ := (exceptional_all_characteristic_field_Lang_surjectivity ℓ L f hf).1 τ
  obtain ⟨g, hg⟩ := hLang ⟨n, hn⟩
  refine ⟨(g : ModGL τ L), g.2, ?_⟩
  rw [← hS g]
  have h1 : S g = g * ⟨n, hn⟩ := by rw [hg, mul_inv_cancel_left]
  rw [h1]
  rfl

private theorem e8Witness_core (F : Type) [Field F] [Finite F] (r : ℤ)
    (hqr : (5 : ℤ) ∣ (Nat.card F : ℤ) - r) (h5 : ¬ 5 ∣ Nat.card F) (e : ℕ)
    (he1 : Nat.card F - 1 ∣ e) (he5 : e % 5 = 1) (x : Fin Tag.E8.rank → ℤ)
    (hx5 : ∀ i, (5 : ℤ) ∣ (x ᵥ* wordMat Tag.E8 e8TwentyWord ^ 5) i - r * x i)
    (i0 : Fin Tag.E8.rank)
    (hx4 : ¬ (5 : ℤ) ∣ (x ᵥ* wordMat Tag.E8 e8TwentyWord ^ 4) i0 - x i0) :
    ∃ (E : Subgroup (adjointGroup Tag.E8 F)) (g : adjointGroup Tag.E8 F),
      IsElemAbelian 5 E ∧ g ^ 5 = 1 ∧ (∀ x ∈ E, g * x * g⁻¹ ∈ E) ∧ ∃ x ∈ E, g * x ≠ x * g := by
  classical
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨f, hℓ, hf⟩ := FiniteField.card F (ringChar F)
  have : Fact (ringChar F).Prime := ⟨hℓ⟩
  have hq : Nat.card F = ringChar F ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hf
  have : CharP F (ringChar F) := ringChar.charP F
  let L := AlgebraicClosure F
  have : CharP L (ringChar F) := charP_of_injective_algebraMap (algebraMap F L).injective _
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed F
  let Fr : L →+* L := iterateFrobenius L (ringChar F) (f : ℕ)
  have hFr : ∀ c, Fr c = c ^ Nat.card F := fun c => by
    rw [hq]
    exact iterateFrobenius_def (ringChar F) (f : ℕ) c
  have hq1 : 1 ≤ Nat.card F := Nat.card_pos
  have : NeZero ((5 : ℕ) : F) := ⟨fun h0 => h5 (by
    have h1 : ringChar F ∣ 5 := ringChar.dvd h0
    have h2 : ringChar F = 5 := (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_five).1 h1
    rw [hq, h2]
    exact dvd_pow_self 5 f.ne_zero)⟩
  obtain ⟨ζ0, hζ0⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure F) 5
  obtain ⟨ζ, hζ⟩ : ∃ ζ : Lˣ, IsPrimitiveRoot ζ 5 := ⟨_, hζ0.isUnit_unit (by norm_num)⟩
  have hζ5 : ζ ^ (5 : ℤ) = 1 := by exact_mod_cast hζ.zpow_eq_one
  have hFrζ : Units.map Fr.toMonoidHom ζ = ζ ^ Nat.card F := CTTorus.map_units_eq_pow hFr ζ
  obtain ⟨wh, hwh⟩ := IsWeylMatrix.of_word Tag.E8 e8TwentyWord
  have hwh20 : wh ^ 20 = 1 := weyl_eq_one_of_mulVec (weyl_pow_smul_eq hwh 20) e8Twenty_pow
  have hwh4e : wh ^ (4 * e) = wh ^ 4 := by
    rw [show 4 * e = 4 + 20 * (e / 5) by omega, pow_add, pow_mul, hwh20, one_pow, mul_one]
  obtain ⟨nu, hnu⟩ : ∃ nu : ModGL Tag.E8 L, nu = canonicalRep (coxeterSystem Tag.E8) L wh :=
    ⟨_, rfl⟩
  have hnuC : nu ∈ adjointGroup Tag.E8 L := by
    rw [hnu]; exact canonicalRep_mem_adjointGroup (coxeterSystem Tag.E8) L wh
  have hΦnu : Units.map (entrywiseHom Fr) nu = nu := by
    rw [hnu]; exact frobenius_canonicalRep Fr wh
  have hconj : ∀ (k : ℕ) (b : Fin Tag.E8.rank → Lˣ),
      nu ^ k * rootDiagUnit Tag.E8 b * (nu ^ k)⁻¹ = rootDiagUnit Tag.E8 (weylTuple (wh ^ k) b) := by
    rw [hnu]; exact canonicalRep_pow_conj_rootDiagUnit wh
  have hnu20 : (nu ^ 20) ^ (Nat.card F - 1) = 1 := by
    have hT : nu ^ 20 ∈ torusGroup Tag.E8 L := by
      rw [hnu]; exact canonicalRep_pow_mem_torusGroup hwh20
    refine pow_sub_one_eq_one_of_fixed Fr hFr hq1 hT ?_
    rw [map_pow, hΦnu]
  obtain ⟨g0, hg0C, hg0⟩ :=
    lang_conjugator_any Tag.E8 (ℓ := ringChar F) (f := (f : ℕ)) f.pos L (pow_mem hnuC 5)
  have hΦg0 : Units.map (entrywiseHom Fr) g0 = g0 * nu ^ 5 := hg0
  have ha_fix : weylTuple (wh ^ 5) (fun i => Units.map Fr.toMonoidHom (ζ ^ x i)) =
      fun i => ζ ^ x i := by
    have h := (mem_twistedFixedTuples_iff (w := wh ^ 5) (Fr := Fr)
      (a := fun i => ζ ^ x i)).2 fun u => by
        have hpow : (ζ ^ Nat.card F) ^ (x ⬝ᵥ u) = ζ ^ ((Nat.card F : ℤ) * (x ⬝ᵥ u)) := by
          rw [zpow_mul, zpow_natCast]
        rw [weyl_pow_smul_eq hwh 5 u, rootChar_zpow_dotProduct, rootChar_zpow_dotProduct,
          map_zpow, hFrζ, hpow, Matrix.dotProduct_mulVec]
        refine zpow_eq_zpow_of_five_dvd hζ5 ?_
        have key : (x ᵥ* wordMat Tag.E8 e8TwentyWord ^ 5) ⬝ᵥ u - (Nat.card F : ℤ) * (x ⬝ᵥ u) =
            (x ᵥ* wordMat Tag.E8 e8TwentyWord ^ 5 - r • x) ⬝ᵥ u -
              ((Nat.card F : ℤ) - r) * (x ⬝ᵥ u) := by
          rw [sub_dotProduct, smul_dotProduct, smul_eq_mul]
          ring
        rw [key]
        refine dvd_sub (Finset.dvd_sum fun i _ => dvd_mul_of_dvd_left ?_ _)
          (dvd_mul_of_dvd_left hqr _)
        simpa [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using hx5 i
    exact h
  have ha_exp : (fun i => ζ ^ x i) ^ 5 = (1 : Fin Tag.E8.rank → Lˣ) := by
    funext i
    simp only [Pi.pow_apply, Pi.one_apply]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, hζ.zpow_eq_one, one_zpow]
  have ha_nc : weylTuple (wh ^ 4) (fun i => ζ ^ x i) ≠ fun i => ζ ^ x i := by
    intro heq
    have h1 := congrArg (fun b => rootChar b ((wh ^ 4) • (Pi.single i0 1 : Fin Tag.E8.rank → ℤ)))
      heq
    simp only [rootChar_weylTuple, inv_smul_smul] at h1
    rw [weyl_pow_smul_eq hwh 4, rootChar_zpow_dotProduct, rootChar_zpow_dotProduct,
      Matrix.dotProduct_mulVec, dotProduct_single, dotProduct_single, mul_one, mul_one] at h1
    apply hx4
    have h2 : ζ ^ ((x ᵥ* wordMat Tag.E8 e8TwentyWord ^ 4) i0 - x i0) = 1 := by
      rw [zpow_sub, ← h1, mul_inv_cancel]
    exact_mod_cast (hζ.zpow_eq_one_iff_dvd _).1 h2
  obtain ⟨S, hmemS⟩ : ∃ S : Subgroup (Fin Tag.E8.rank → Lˣ), ∀ b, b ∈ S ↔
      (weylTuple (wh ^ 5) (fun i => Units.map Fr.toMonoidHom (b i)) = b ∧ b ^ 5 = 1) :=
    ⟨twistedFixedTuples (wh ^ 5) Fr ⊓ (powMonoidHom 5 : (Fin Tag.E8.rank → Lˣ) →* _).ker,
      fun b => by
        rw [Subgroup.mem_inf, MonoidHom.mem_ker, powMonoidHom_apply]
        exact Iff.rfl⟩
  obtain ⟨a, haS, ha_nc⟩ : ∃ a, a ∈ S ∧ weylTuple (wh ^ 4) a ≠ a :=
    ⟨_, (hmemS _).2 ⟨ha_fix, ha_exp⟩, ha_nc⟩
  have hSinv : ∀ b ∈ S, weylTuple (wh ^ 4) b ∈ S := by
    intro b hb
    obtain ⟨hb1, hb2⟩ := (hmemS b).1 hb
    refine (hmemS _).2 ⟨?_, ?_⟩
    · rw [map_weylTuple_e8w, weylTuple_weylTuple, (Commute.pow_pow_self wh 5 4).eq,
        ← weylTuple_weylTuple, hb1]
    · rw [weylTuple_pow_e8w, hb2, weylTuple_one_tuple]
  have hS5 : ∀ b ∈ S, ∀ i, b i ∈ rootsOfUnity 5 L := fun b hb i => by
    rw [mem_rootsOfUnity]
    simpa using congrFun ((hmemS b).1 hb).2 i
  have hSfin : Finite S :=
    Finite.of_injective
      (fun b : S => fun i => (⟨(b : Fin Tag.E8.rank → Lˣ) i, hS5 b b.2 i⟩ : rootsOfUnity 5 L))
      (fun b b' h => Subtype.ext (funext fun i => congrArg Subtype.val (congrFun h i)))
  obtain ⟨φ, hφ, hφinj⟩ : ∃ φ : (Fin Tag.E8.rank → Lˣ) →* ModGL Tag.E8 L,
      (∀ b, φ b = g0 * rootDiagUnit Tag.E8 b * g0⁻¹) ∧ Function.Injective φ :=
    ⟨(MulAut.conj g0).toMonoidHom.comp (rootDiagUnitHom Tag.E8 L), fun b => rfl,
      (MulAut.conj g0).injective.comp rootDiagUnit_injective⟩
  set E0 : Subgroup (ModGL Tag.E8 L) := S.map φ with hE0
  have hE0C : E0 ≤ adjointGroup Tag.E8 L := by
    rintro _ ⟨b, -, rfl⟩
    rw [hφ]
    exact mul_mem (mul_mem hg0C (torusGroup_le_adjointGroup' (rootDiagUnit_mem_torusGroup b)))
      (inv_mem hg0C)
  have hE0F : ∀ y ∈ E0, Units.map (entrywiseHom Fr) y = y := by
    rintro _ ⟨b, hb, rfl⟩
    rw [hφ, map_mul, map_mul, map_inv, hΦg0, units_map_entrywise_rootDiagUnit]
    calc g0 * nu ^ 5 * rootDiagUnit Tag.E8 (fun i => Units.map Fr.toMonoidHom (b i)) *
          (g0 * nu ^ 5)⁻¹
        = g0 * (nu ^ 5 * rootDiagUnit Tag.E8 (fun i => Units.map Fr.toMonoidHom (b i)) *
          (nu ^ 5)⁻¹) * g0⁻¹ := by group
      _ = g0 * rootDiagUnit Tag.E8 b * g0⁻¹ := by rw [hconj, ((hmemS b).1 hb).1]
  have hE0comm : ∀ y1 ∈ E0, ∀ y2 ∈ E0, y1 * y2 = y2 * y1 := by
    rintro _ ⟨b1, -, rfl⟩ _ ⟨b2, -, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm b1 b2]
  have hE0exp : ∀ y ∈ E0, y ^ 5 = 1 := by
    rintro _ ⟨b, hb, rfl⟩
    rw [← map_pow, ((hmemS b).1 hb).2, map_one]
  have hE0fin : Finite E0 := Finite.of_surjective (φ.subgroupMap S) (φ.subgroupMap_surjective S)
  set g5 : ModGL Tag.E8 L := g0 * nu ^ (4 * e) * g0⁻¹ with hg5
  have hg5C : g5 ∈ adjointGroup Tag.E8 L :=
    mul_mem (mul_mem hg0C (pow_mem hnuC _)) (inv_mem hg0C)
  have hg5F : Units.map (entrywiseHom Fr) g5 = g5 := by
    rw [hg5, map_mul, map_mul, map_inv, hΦg0, map_pow, hΦnu]
    group
  have hg5pow : g5 ^ 5 = 1 := by
    rw [hg5, conj_pow, ← pow_mul, show 4 * e * 5 = 20 * e by ring, pow_mul]
    obtain ⟨k, hk⟩ := he1
    rw [hk, pow_mul, hnu20, one_pow, mul_one, mul_inv_cancel]
  have hg5act : ∀ b, g5 * φ b * g5⁻¹ = φ (weylTuple (wh ^ 4) b) := by
    intro b
    rw [hφ, hφ, hg5]
    calc g0 * nu ^ (4 * e) * g0⁻¹ * (g0 * rootDiagUnit Tag.E8 b * g0⁻¹) *
          (g0 * nu ^ (4 * e) * g0⁻¹)⁻¹
        = g0 * (nu ^ (4 * e) * rootDiagUnit Tag.E8 b * (nu ^ (4 * e))⁻¹) * g0⁻¹ := by group
      _ = g0 * rootDiagUnit Tag.E8 (weylTuple (wh ^ 4) b) * g0⁻¹ := by rw [hconj, hwh4e]
  have hg5norm : ∀ y ∈ E0, g5 * y * g5⁻¹ ∈ E0 := by
    rintro _ ⟨b, hb, rfl⟩
    rw [hg5act]
    exact ⟨_, hSinv b hb, rfl⟩
  have hrat : ∀ (X : Subgroup (ModGL Tag.E8 L)) [Finite X], X ≤ adjointGroup Tag.E8 L →
      (∀ y ∈ X, Units.map (entrywiseHom Fr) y = y) →
      X ≤ (adjointGroup Tag.E8 F).map (baseChangeGL (algebraMap F L)) := by
    intro X _ hXC hXF
    exact Subgroup.relIndex_eq_one.1 (Nat.dvd_one.1
      (finite_fixed_subgroup_rational (K := F) 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) Fr hFr X hXC
        hXF).1)
  have hE0rat := hrat E0 hE0C hE0F
  have hzfin : Finite (Subgroup.zpowers g5) :=
    (isOfFinOrder_iff_pow_eq_one.2 ⟨5, by norm_num, hg5pow⟩).finite_zpowers
  have hzrat := hrat (Subgroup.zpowers g5) (Subgroup.zpowers_le.2 hg5C) (by
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    rw [map_zpow, hg5F])
  obtain ⟨ι, hι, hrange⟩ : ∃ ι : adjointGroup Tag.E8 F →* ModGL Tag.E8 L, Function.Injective ι ∧
      ι.range = (adjointGroup Tag.E8 F).map (baseChangeGL (algebraMap F L)) :=
    ⟨(baseChangeGL (algebraMap F L)).comp (adjointGroup Tag.E8 F).subtype,
      (baseChangeGL_injective _).comp (Subgroup.subtype_injective _), by
        rw [MonoidHom.range_comp, Subgroup.range_subtype]⟩
  rw [← hrange] at hE0rat hzrat
  obtain ⟨g, hg⟩ := hzrat (Subgroup.mem_zpowers g5)
  obtain ⟨x0, hx0⟩ := hE0rat (⟨a, haS, rfl⟩ : φ a ∈ E0)
  refine ⟨E0.comap ι, g, ⟨IsMulCommutative.of_comm fun u v => ?_, fun u hu => ?_⟩, ?_,
    fun u hu => ?_, x0, ?_, fun h => ?_⟩
  · apply Subtype.ext
    apply hι
    rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
    exact hE0comm _ u.2 _ v.2
  · apply hι
    rw [map_pow, map_one]
    exact hE0exp _ hu
  · apply hι
    rw [map_pow, hg, hg5pow, map_one]
  · show ι (g * u * g⁻¹) ∈ E0
    rw [map_mul, map_mul, map_inv, hg]
    exact hg5norm _ hu
  · show ι x0 ∈ E0
    rw [hx0]
    exact ⟨a, haS, rfl⟩
  · have h1 : g5 * φ a = φ a * g5 := by
      have := congrArg ι h
      rwa [map_mul, map_mul, hg, hx0] at this
    have h2 : g5 * φ a * g5⁻¹ = φ a := by rw [h1, mul_inv_cancel_right]
    rw [hg5act] at h2
    exact ha_nc (hφinj h2)

end Core

end Witness

theorem e8Witness_holds :
    E8Witness := by
  intro F _ _ hord
  have hq2 : 1 < Nat.card F := Finite.one_lt_card
  have hy : ((Nat.card F : ℕ) : ZMod 5) = 2 ∨ ((Nat.card F : ℕ) : ZMod 5) = 3 := by
    have h4 : ((Nat.card F : ℕ) : ZMod 5) ^ 4 = 1 := by
      have := pow_orderOf_eq_one ((Nat.card F : ℕ) : ZMod 5)
      rwa [hord] at this
    have h2 : ((Nat.card F : ℕ) : ZMod 5) ^ 2 ≠ 1 := fun h2 => by
      have := orderOf_dvd_of_pow_eq_one h2
      rw [hord] at this
      norm_num at this
    generalize ((Nat.card F : ℕ) : ZMod 5) = y at h4 h2 ⊢
    revert y
    decide
  have hq5 : Nat.card F % 5 = 2 ∨ Nat.card F % 5 = 3 := by
    rcases hy with h | h
    · left
      have := congrArg ZMod.val h
      rw [ZMod.val_natCast] at this
      exact this
    · right
      have := congrArg ZMod.val h
      rw [ZMod.val_natCast] at this
      exact this
  rcases hq5 with h | h
  · refine e8Witness_core F 2 (by omega) (by omega) (Nat.card F - 1) dvd_rfl (by omega)
      (CFSG.RankThree.Lattice.toVec Tag.E8.rank [0, 0, 0, 1, 4, 2, 2, 1]) (fun i => ?_) 2 ?_
    · rw [vecMul_e8Twenty_pow]
      exact Int.dvd_of_emod_eq_zero (e8w_check2a i)
    · rw [vecMul_e8Twenty_pow]
      exact fun hd => e8w_check2b (Int.emod_eq_zero_of_dvd hd)
  · refine e8Witness_core F 3 (by omega) (by omega) (3 * (Nat.card F - 1)) (dvd_mul_left _ _)
      (by omega) (CFSG.RankThree.Lattice.toVec Tag.E8.rank [0, 0, 0, 1, 4, 3, 1, 1])
      (fun i => ?_) 2 ?_
    · rw [vecMul_e8Twenty_pow]
      exact Int.dvd_of_emod_eq_zero (e8w_check3a i)
    · rw [vecMul_e8Twenty_pow]
      exact fun hd => e8w_check3b (Int.emod_eq_zero_of_dvd hd)

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sylow5Omega
