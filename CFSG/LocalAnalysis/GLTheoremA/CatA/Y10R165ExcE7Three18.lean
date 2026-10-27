module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE7Three19
public import CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7.FrameLines
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE7Three13
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE7Three3

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE7Three

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KA5L CFSG.RankThree.Classical2 CFSG.Open
  CFSG.RankThree.PartOne.KLR CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.E6
  CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7
open scoped Matrix MatrixGroups Pointwise

@[expose] def e7T3ZAVec : Fin Tag.E7.rank → ℤ := toVec Tag.E7.rank [2, 0, -1, 0, 0, 0, 0]

@[expose] def e7T3ZDVec : Fin Tag.E7.rank → ℤ := toVec Tag.E7.rank [1, 1, 0, -1, 0, 1, -1]

def e7T3ZA (α : Fin Tag.E7.rank → ℤ) : ℤ := ∑ i, α i * e7T3ZAVec i

def e7T3ZD (α : Fin Tag.E7.rank → ℤ) : ℤ := ∑ i, α i * e7T3ZDVec i

@[expose] def e7T3ZColumn {p : ℕ} (ε : ℤ) (q : ZMod p) : Fin Tag.E7.rank → ZMod p :=
  (fun i => (e7T3ZAVec i : ZMod p)) + ((ε : ZMod p) * q) • (fun i => (e7T3ZDVec i : ZMod p))

theorem e7T3W_transpose_mulVec_ZAVec :
    e7T3W.transpose *ᵥ e7T3ZAVec = -e7T3ZDVec := by
  decide +kernel

theorem e7T3W_transpose_mulVec_ZDVec :
    e7T3W.transpose *ᵥ e7T3ZDVec = e7T3ZAVec - e7T3ZDVec := by
  decide +kernel

private theorem map_mulVec_intCast {p : ℕ} (M : Matrix (Fin Tag.E7.rank) (Fin Tag.E7.rank) ℤ)
    (v : Fin Tag.E7.rank → ℤ) :
    (fun i => ((M *ᵥ v) i : ZMod p)) =
      (M.map (Int.cast : ℤ → ZMod p)) *ᵥ (fun i => (v i : ZMod p)) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Int.cast_sum, Int.cast_mul]

theorem e7T3ZColumn_eigen {p : ℕ} {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {q : ZMod p}
    (hq : q ^ 2 + (ε : ZMod p) * q + 1 = 0) :
    ((ε • e7T3W).map (Int.cast : ℤ → ZMod p)).transpose *ᵥ e7T3ZColumn ε q =
      q • e7T3ZColumn ε q := by
  have hε2 : (ε : ZMod p) * (ε : ZMod p) = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hA : ((e7T3W.map (Int.cast : ℤ → ZMod p)).transpose) *ᵥ
      (fun i => (e7T3ZAVec i : ZMod p)) = -(fun i => (e7T3ZDVec i : ZMod p)) := by
    rw [← Matrix.transpose_map, ← map_mulVec_intCast, e7T3W_transpose_mulVec_ZAVec]
    funext i
    simp
  have hD : ((e7T3W.map (Int.cast : ℤ → ZMod p)).transpose) *ᵥ
      (fun i => (e7T3ZDVec i : ZMod p)) =
        (fun i => (e7T3ZAVec i : ZMod p)) - (fun i => (e7T3ZDVec i : ZMod p)) := by
    rw [← Matrix.transpose_map, ← map_mulVec_intCast, e7T3W_transpose_mulVec_ZDVec]
    funext i
    simp
  have hsm : ((ε • e7T3W).map (Int.cast : ℤ → ZMod p)) =
      (ε : ZMod p) • (e7T3W.map (Int.cast : ℤ → ZMod p)) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
    push_cast
    ring
  have key : ∀ a d : Fin Tag.E7.rank → ZMod p,
      (ε : ZMod p) • (-d + ((ε : ZMod p) * q) • (a - d)) =
        q • (a + ((ε : ZMod p) * q) • d) := by
    intro a d
    funext i
    simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, smul_eq_mul]
    have h1 : (↑ε : ZMod p) * (-d i + ↑ε * q * (a i - d i)) =
        ↑ε * (-d i) + ↑ε * (↑ε * q) * (a i - d i) := by ring
    rw [h1]
    exact e7T3_eigen_coord hε2 hq _ _
  rw [e7T3ZColumn, hsm, Matrix.transpose_smul, Matrix.smul_mulVec, Matrix.mulVec_add,
    Matrix.mulVec_smul, hA, hD]
  exact key _ _

theorem mem_fixedCharTuples_e7T3ZTuple {p : ℕ} [NeZero p] {L : Type} [Field L]
    {Fr : L →+* L} {q₀ : ℕ} (hFr : ∀ c, Fr c = c ^ q₀) {ζ : Lˣ}
    (hζ : IsPrimitiveRoot ζ p) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hq : (q₀ : ZMod p) ^ 2 + (ε : ZMod p) * (q₀ : ZMod p) + 1 = 0) :
    (fun i => ζ ^ (e7T3ZColumn ε (q₀ : ZMod p) i).val) ∈
      fixedCharTuples (ε • e7T3W) Fr := by
  rw [e7T3_mem_fixed_iff_ker hFr,
    CFSG.RankThree.Classical2.zetaPow_mem_ker_monomialHom_iff hζ]
  have hmap : (((Matrix.scalar (Fin Tag.E7.rank) (q₀ : ℤ) - ε • e7T3W)).transpose).map
      (Int.cast : ℤ → ZMod p) =
      Matrix.scalar (Fin Tag.E7.rank) (q₀ : ZMod p) -
        ((ε • e7T3W).map (Int.cast : ℤ → ZMod p)).transpose := by
    ext i j
    simp only [Matrix.map_apply, Matrix.scalar_apply, Matrix.transpose_apply,
      Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Int.cast_sub, Int.cast_mul,
      Matrix.diagonal_apply]
    by_cases h : i = j
    · subst h
      simp
    · simp [h, Ne.symm h]
  have hsmul : (Matrix.scalar (Fin Tag.E7.rank) (q₀ : ZMod p)) *ᵥ
      e7T3ZColumn ε (q₀ : ZMod p) = (q₀ : ZMod p) • e7T3ZColumn ε (q₀ : ZMod p) := by
    ext i
    rw [Matrix.scalar_apply, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
  rw [hmap, Matrix.sub_mulVec, hsmul, e7T3ZColumn_eigen hε hq, sub_self]

@[expose] def e7T3A2List : List (List ℤ) :=
  (e7StdRoots [1, 3]).map (lmulVec Tag.E7.rank (e7wl e7T3CertA5.w))

theorem e7T3A2Roots_eq_image :
    ∀ γ : Fin Tag.E7.rank → ℤ,
      γ ∈ e7T3A2Roots ↔ ∃ l ∈ e7StdRoots [1, 3], toVec Tag.E7.rank l = γ := by
  have h1 : ∀ l ∈ e7StdRoots [1, 3], toVec Tag.E7.rank l ∈ e7T3A2Roots := by
    decide +kernel
  have h2 : ∀ γ ∈ e7T3A2Roots, ∃ l ∈ e7StdRoots [1, 3], toVec Tag.E7.rank l = γ := by
    decide +kernel
  intro γ
  exact ⟨h2 γ, fun ⟨l, hl, hlγ⟩ => hlγ ▸ h1 l hl⟩

theorem e7T3A5SubA2_eq_image :
    e7T3A5SubA2 = {α | ∃ l ∈ e7T3A2List, α = toVec Tag.E7.rank l} := by
  ext α
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    obtain ⟨l, hl, rfl⟩ := (e7T3A2Roots_eq_image γ).1
      (mem_parabolicRoots_iff_mem_e7T3A2Roots.1 hγ)
    exact ⟨lmulVec Tag.E7.rank (e7wl e7T3CertA5.w) l,
      List.mem_map.2 ⟨l, hl, rfl⟩, by simp only [e7T3A5Transport, wordProd_smul_toVec7]⟩
  · rintro ⟨l, hl, rfl⟩
    obtain ⟨l₀, hl₀, rfl⟩ := List.mem_map.1 hl
    exact ⟨toVec Tag.E7.rank l₀,
      mem_parabolicRoots_iff_mem_e7T3A2Roots.2 ((e7T3A2Roots_eq_image _).2 ⟨l₀, hl₀, rfl⟩),
      by simp only [e7T3A5Transport, wordProd_smul_toVec7]⟩

theorem e7T3ZA_norm_mem (l : List ℤ) (hl : l ∈ Tag.E7.artifactRoots) :
    let α := toVec Tag.E7.rank l
    e7T3ZA α * e7T3ZA α - e7T3ZA α * e7T3ZD α + e7T3ZD α * e7T3ZD α ∈
      ({0, 1, 3} : Finset ℤ) := by
  revert l
  decide +kernel

theorem e7T3ZA_eq_zero_iff_charVal_eq_zero {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) {q : ZMod p} (hq : q ^ 2 + (ε : ZMod p) * q + 1 = 0)
    {α : Fin Tag.E7.rank → ℤ} (hα : IsRoot Tag.E7 α) :
    charVal (e7T3ZColumn ε q) α = 0 ↔ e7T3ZA α = 0 ∧ e7T3ZD α = 0 := by
  constructor
  · intro h0
    have hnorm := e7T3ZA_norm_mem (List.ofFn α) (isRoot_iff_mem_artifactRoots.1 hα)
    rw [toVec_ofFn] at hnorm
    rw [e7T3ZColumn, CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Three.charVal_column_add,
      charVal_smul_col, charVal_intVec, charVal_intVec] at h0
    change (e7T3ZA α : ZMod p) + (ε : ZMod p) * q * (e7T3ZD α : ZMod p) = 0 at h0
    exact e7T3XA_eq_zero_of_charVal_eq_zero hp hp3 hε hq hnorm h0
  · rintro ⟨hA, hD⟩
    rw [e7T3ZColumn, CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Three.charVal_column_add,
      charVal_smul_col, charVal_intVec, charVal_intVec]
    change (e7T3ZA α : ZMod p) + (ε : ZMod p) * q * (e7T3ZD α : ZMod p) = 0
    rw [hA, hD]
    simp

theorem e7T3ZA_eq_zero_iff_mem (l : List ℤ) (hl : l ∈ e7T3CertA5.rootList) :
    (e7T3ZA (toVec Tag.E7.rank l) = 0 ∧ e7T3ZD (toVec Tag.E7.rank l) = 0) ↔
      l ∈ e7T3A2List := by
  revert l
  decide +kernel

private theorem rootDiagUnit_pow_tuple {L : Type} [Field L] (b : Fin Tag.E7.rank → Lˣ) (n : ℕ) :
    rootDiagUnit .E7 (b ^ n) = rootDiagUnit .E7 b ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, rootDiagUnit_one]
  | succ n ih => rw [pow_succ, pow_succ, rootDiagUnit_mul, ih]

private theorem rootDiagUnit_zpow_tuple {L : Type} [Field L] (b : Fin Tag.E7.rank → Lˣ) (k : ℤ) :
    rootDiagUnit .E7 (b ^ k) = rootDiagUnit .E7 b ^ k := by
  change (rootDiagUnitHom .E7 L) (b ^ k) = ((rootDiagUnitHom .E7 L) b) ^ k
  exact map_zpow _ _ _

private theorem rootChar_inv_tuple {L : Type} [Field L] (b : Fin Tag.E7.rank → Lˣ)
    (u : Fin Tag.E7.rank → ℤ) :
    rootChar (b⁻¹) u = (rootChar b u)⁻¹ := by
  have h := CTTorus.rootChar_mul b b⁻¹ u
  rw [mul_inv_cancel, CTTorus.rootChar_one] at h
  exact eq_inv_of_mul_eq_one_right h.symm

private theorem rootChar_zpow_tuple {L : Type} [Field L] (b : Fin Tag.E7.rank → Lˣ) (k : ℤ)
    (u : Fin Tag.E7.rank → ℤ) :
    rootChar (b ^ k) u = rootChar b u ^ k := by
  have hnat : ∀ n : ℕ, rootChar (b ^ (n : ℤ)) u = rootChar b u ^ (n : ℤ) := by
    intro n
    rw [zpow_natCast, rootChar_pow_apply, zpow_natCast]
  obtain ⟨n, hn | hn⟩ := Int.eq_nat_or_neg k
  · subst hn; simpa using hnat n
  · subst hn
    rw [_root_.zpow_neg, rootChar_inv_tuple (b ^ (n : ℤ)), hnat n, _root_.zpow_neg]

private theorem exists_fixedCharTuple_eq {K : Type} [Field K] [Finite K]
    {ℓ f p : ℕ} [Fact ℓ.Prime] {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L]
    [CharP L ℓ] {ε : ℤ} (F : E7ThreeFrame K L ℓ f p ε)
    {Ã : Subgroup (adjointGroup Tag.E7 K)} (hA : IsElemAbelian p Ã)
    (hAcard : p ^ 3 ≤ Nat.card Ã) [Finite ↥(adjointGroup Tag.E7 K)]
    (hAfix : ∀ y ∈ Ã, F.g0⁻¹ * adjEmb Tag.E7 K L y * F.g0 ∈
      twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))))
    (hK : Nat.card K = ℓ ^ f) (hf : 1 ≤ f) (hp : p.Prime) (hp3 : 3 < p)
    (hε : ε = 1 ∨ ε = -1)
    (hq : (Nat.card K : ZMod p) ^ 2 + (ε : ZMod p) * (Nat.card K : ZMod p) + 1 = 0)
    {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ p) :
    ∃ z ∈ Ã, F.g0⁻¹ * adjEmb Tag.E7 K L (z : adjointGroup Tag.E7 K) * F.g0 =
      rootDiagUnit Tag.E7 (fun i => ζ ^ (e7T3ZColumn ε (Nat.card K : ZMod p) i).val) := by
  classical
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  haveI : NeZero p := ⟨hp.ne_zero⟩
  set q₀ : ZMod p := (Nat.card K : ZMod p) with hq₀
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by rw [iterateFrobenius_def, hK]
  have hℓq : ℓ ∣ Nat.card K := by rw [hK]; exact dvd_pow_self _ (by omega)
  set bx : Fin Tag.E7.rank → Lˣ := fun i => ζ ^ (e7T3XColumn ε q₀ i).val with hbxdef
  set bz : Fin Tag.E7.rank → Lˣ := fun i => ζ ^ (e7T3ZColumn ε q₀ i).val with hbzdef
  have hbzmem : bz ∈ fixedCharTuples (ε • e7T3W) Fr :=
    mem_fixedCharTuples_e7T3ZTuple hFr hζ hε (by simpa [hq₀] using hq)
  have hbzpow : ∀ i, bz i ^ p = 1 := fun i => by
    change (ζ ^ (e7T3ZColumn ε q₀ i).val) ^ p = 1
    rw [← pow_mul, mul_comm, pow_mul, IsPrimitiveRoot.pow_eq_one hζ, one_pow]
  have hex : ∀ y : ↥Ã, ∃ b : Fin Tag.E7.rank → Lˣ,
      b ∈ fixedCharTuples (ε • e7T3W) Fr ∧ (∀ i, b i ^ p = 1) ∧
        rootDiagUnit .E7 b = psiC F.g0 1 (y : adjointGroup Tag.E7 K) := by
    intro y
    have hy : psiC F.g0 1 (y : adjointGroup Tag.E7 K) ∈
        twistedTorusOf F.n (Units.map (entrywiseHom Fr)) := by
      rw [psiC_apply]
      simpa using hAfix y.1 y.2
    rw [F.hT] at hy
    obtain ⟨b, hb, hbz⟩ := Subgroup.mem_map.1 hy
    refine ⟨b, hb, fun i => ?_, hbz⟩
    have hyp : (y : adjointGroup Tag.E7 K) ^ p = 1 := hA.2 y.1 y.2
    have hψ : psiC F.g0 1 ((y : adjointGroup Tag.E7 K) ^ p) = 1 := by rw [hyp, map_one]
    rw [map_pow] at hψ
    have hbz' : rootDiagUnit .E7 b = psiC F.g0 1 (y : adjointGroup Tag.E7 K) := hbz
    have hb1 : rootDiagUnit .E7 (b ^ p) = rootDiagUnit .E7 (1 : Fin Tag.E7.rank → Lˣ) := by
      rw [rootDiagUnit_one, rootDiagUnit_pow_tuple, hbz', hψ]
    have hbp : b ^ p = 1 := rootDiagUnit_injective (K := L) hb1
    simpa using congrFun hbp i
  choose b hbmem hbpow hbspec using hex
  have hbinj : Function.Injective b := by
    intro y y' h
    have h1 : psiC F.g0 1 (y : adjointGroup Tag.E7 K) =
        psiC F.g0 1 (y' : adjointGroup Tag.E7 K) := by
      rw [← hbspec y, ← hbspec y', h]
    exact Subtype.ext (psiC_injective F.g0 1 h1)
  set Kp : Type := {b : Fin Tag.E7.rank → Lˣ //
    b ∈ fixedCharTuples (ε • e7T3W) Fr ∧ ∀ i, b i ^ p = 1} with hKp
  have hKpcard : Nat.card Kp = p ^ 3 :=
    natCard_e7T3_fixedPTorsion hp hp3 hε L Fr hℓq hFr hq
  haveI : Finite Kp := Nat.finite_of_card_ne_zero (by rw [hKpcard]; positivity)
  let g : ↥Ã → Kp := fun y => ⟨b y, hbmem y, hbpow y⟩
  have hginj : Function.Injective g := fun y y' h =>
    hbinj (congrArg Subtype.val h)
  have hcardA : Nat.card ↥Ã = p ^ 3 := by
    refine le_antisymm ?_ hAcard
    calc Nat.card ↥Ã ≤ Nat.card Kp := Nat.card_le_card_of_injective g hginj
      _ = p ^ 3 := hKpcard
  haveI : Finite ↥Ã := Subtype.finite
  haveI : Fintype ↥Ã := Fintype.ofFinite _
  haveI : Fintype Kp := Fintype.ofFinite _
  have hAcard' : Fintype.card ↥Ã = p ^ 3 := by
    rw [← Nat.card_eq_fintype_card]; exact hcardA
  have hKpcard' : Fintype.card Kp = p ^ 3 := by
    rw [← Nat.card_eq_fintype_card]; exact hKpcard
  have himg : Finset.univ.image g = (Finset.univ : Finset Kp) := by
    refine Finset.eq_of_subset_of_card_le (fun x _ => Finset.mem_univ x) ?_
    rw [Finset.card_image_of_injective _ hginj, Finset.card_univ, Finset.card_univ,
      hAcard', hKpcard']
  have hbzKp : (⟨bz, hbzmem, hbzpow⟩ : Kp) ∈ (Finset.univ : Finset Kp) :=
    Finset.mem_univ _
  rw [← himg] at hbzKp
  obtain ⟨z, -, hz⟩ := Finset.mem_image.1 hbzKp
  have hzb : b z = bz := congrArg Subtype.val hz
  have hzraw : F.g0⁻¹ * adjEmb Tag.E7 K L (z : adjointGroup Tag.E7 K) * F.g0 =
      rootDiagUnit Tag.E7 bz := by
    rw [← hzb, hbspec z, psiC_apply]
    simp
  exact ⟨z, z.2, hzraw⟩

private theorem secondPoint_not_mem_zpowers {K : Type} [Field K] [Finite K]
    {ℓ f p : ℕ} [Fact ℓ.Prime] {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L]
    [CharP L ℓ] {ε : ℤ} (F : E7ThreeFrame K L ℓ f p ε) (hp : p.Prime) (hp3 : 3 < p)
    (hε : ε = 1 ∨ ε = -1) {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ p)
    {q₀ : ZMod p} (hq0ne : q₀ ≠ 0) (hq : q₀ ^ 2 + (ε : ZMod p) * q₀ + 1 = 0)
    {bx : Fin Tag.E7.rank → Lˣ}
    (hkerbx : rootCharKernel bx =
      {α | ∃ l ∈ e7T3CertA5.rootList, α = toVec Tag.E7.rank l})
    {x z : adjointGroup Tag.E7 K}
    (hzraw : F.g0⁻¹ * adjEmb Tag.E7 K L z * F.g0 =
      rootDiagUnit Tag.E7 (fun i => ζ ^ (e7T3ZColumn ε q₀ i).val))
    (hψx : psiC F.g0 1 x = rootDiagUnit Tag.E7 bx) :
    z ∉ Subgroup.zpowers x := by
  classical
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  set bz : Fin Tag.E7.rank → Lˣ := fun i => ζ ^ (e7T3ZColumn ε q₀ i).val with hbzdef
  intro hzmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hzmem
  have hψz : psiC F.g0 1 (z : adjointGroup Tag.E7 K) = rootDiagUnit .E7 bz := by
    rw [psiC_apply]; simpa using hzraw
  have hbz_eq : bz = bx ^ k := by
    have h1 : rootDiagUnit .E7 bz = rootDiagUnit .E7 (bx ^ k) := by
      rw [← hψz, ← hk, map_zpow, hψx, ← rootDiagUnit_zpow_tuple]
    exact rootDiagUnit_injective h1
  have he6root : IsRoot Tag.E7 (toVec Tag.E7.rank [0, 0, 0, 0, 0, 0, 1]) :=
    isRoot_toVec (by decide +kernel)
  have he6mem : [0, 0, 0, 0, 0, 0, 1] ∈ e7T3CertA5.rootList := by decide +kernel
  have hxbe6 : toVec Tag.E7.rank [0, 0, 0, 0, 0, 0, 1] ∈ rootCharKernel bx := by
    rw [hkerbx]; exact ⟨_, he6mem, rfl⟩
  have hzbe6 : toVec Tag.E7.rank [0, 0, 0, 0, 0, 0, 1] ∈ rootCharKernel bz := by
    rw [rootCharKernel, Set.mem_setOf_eq, hbz_eq]
    refine ⟨he6root, ?_⟩
    rw [rootChar_zpow_tuple, hxbe6.2, _root_.one_zpow]
  have h0 : charVal (e7T3ZColumn ε q₀) (toVec Tag.E7.rank [0, 0, 0, 0, 0, 0, 1]) = 0 :=
    (rootChar_zetaPow_eq_one_iff_charVal hζ (e7T3ZColumn ε q₀) _).1 hzbe6.2
  rw [e7T3ZColumn, CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Three.charVal_column_add,
    charVal_smul_col, charVal_intVec, charVal_intVec] at h0
  change (e7T3ZA (toVec Tag.E7.rank [0, 0, 0, 0, 0, 0, 1]) : ZMod p) + (ε : ZMod p) * q₀ *
    (e7T3ZD (toVec Tag.E7.rank [0, 0, 0, 0, 0, 0, 1]) : ZMod p) = 0 at h0
  rw [show e7T3ZA (toVec Tag.E7.rank [0, 0, 0, 0, 0, 0, 1]) = 0 from by decide +kernel,
    show e7T3ZD (toVec Tag.E7.rank [0, 0, 0, 0, 0, 0, 1]) = -1 from by decide +kernel] at h0
  have hεu : (ε : ZMod p) ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  have hmul : (ε : ZMod p) * q₀ = 0 := by linear_combination -h0
  rcases mul_eq_zero.1 hmul with h | h
  · exact absurd h hεu
  · exact hq0ne h

theorem exists_selection_secondPoint_explicit {K : Type} [Field K] [Finite K]
    {ℓ f p : ℕ} [Fact ℓ.Prime] {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L]
    [CharP L ℓ] {ε : ℤ} (F : E7ThreeFrame K L ℓ f p ε) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (hp3 : 3 < p) (hε : ε = 1 ∨ ε = -1)
    (hpf : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + ε * (Nat.card K : ℤ) + 1)
    {Ã : Subgroup (adjointGroup Tag.E7 K)} (hA : IsElemAbelian p Ã)
    (hAcard : p ^ 3 ≤ Nat.card Ã) [Finite ↥(adjointGroup Tag.E7 K)]
    (hAfix : ∀ y ∈ Ã, F.g0⁻¹ * adjEmb Tag.E7 K L y * F.g0 ∈
      twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))))
    {x : adjointGroup Tag.E7 K} (hx : x ∈ Ã) {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ p)
    (hxcol : F.g0⁻¹ * adjEmb Tag.E7 K L x * F.g0 =
      rootDiagUnit Tag.E7 (fun i => ζ ^ (e7T3XColumn ε (Nat.card K : ZMod p) i).val)) :
    ∃ z ∈ Ã, z ∉ Subgroup.zpowers x ∧
      F.g0⁻¹ * adjEmb Tag.E7 K L z * F.g0 =
        rootDiagUnit Tag.E7 (fun i => ζ ^ (e7T3ZColumn ε (Nat.card K : ZMod p) i).val) ∧
      ∀ α, IsRoot Tag.E7 α →
        ((α ∈ rootCharKernel (fun i => ζ ^ (e7T3ZColumn ε (Nat.card K : ZMod p) i).val) ∧
          α ∈ rootCharKernel (fun i => ζ ^ (e7T3XColumn ε (Nat.card K : ZMod p) i).val)) ↔
          α ∈ e7T3A5SubA2) := by
  classical
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  set q₀ : ZMod p := (Nat.card K : ZMod p) with hq₀
  have hq : q₀ ^ 2 + (ε : ZMod p) * q₀ + 1 = 0 := by
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd
      ((Nat.card K : ℤ) ^ 2 + ε * (Nat.card K : ℤ) + 1) p).2 hpf
    simpa [hq₀, sq] using h
  have hq0ne : q₀ ≠ 0 := by
    intro h0
    have h1 : (1 : ZMod p) = 0 := by simpa [h0] using hq
    exact one_ne_zero h1
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by rw [iterateFrobenius_def, hK]
  have hℓq : ℓ ∣ Nat.card K := by rw [hK]; exact dvd_pow_self _ (by omega)
  set bx : Fin Tag.E7.rank → Lˣ := fun i => ζ ^ (e7T3XColumn ε q₀ i).val with hbxdef
  set bz : Fin Tag.E7.rank → Lˣ := fun i => ζ ^ (e7T3ZColumn ε q₀ i).val with hbzdef
  have hbzmem : bz ∈ fixedCharTuples (ε • e7T3W) Fr :=
    mem_fixedCharTuples_e7T3ZTuple hFr hζ hε hq
  have hbzpow : ∀ i, bz i ^ p = 1 := fun i => by
    change (ζ ^ (e7T3ZColumn ε q₀ i).val) ^ p = 1
    rw [← pow_mul, mul_comm, pow_mul, IsPrimitiveRoot.pow_eq_one hζ, one_pow]
  obtain ⟨z, hzA, hzraw⟩ :=
    exists_fixedCharTuple_eq F hA hAcard hAfix hK hf hp hp3 hε hq hζ
  have hψx : psiC F.g0 1 x = rootDiagUnit .E7 bx := by
    rw [psiC_apply]; simpa [hbxdef] using hxcol
  have hkerbx : rootCharKernel bx =
      {α | ∃ l ∈ e7T3CertA5.rootList, α = toVec Tag.E7.rank l} :=
    rootCharKernel_e7T3XColumn hp hp3 hζ hε hq
  have hA2sub : e7T3A2List ⊆ e7T3CertA5.rootList := by decide +kernel
  have hne : e7T3A2List ≠ e7T3CertA5.rootList := by decide +kernel
  have hker : ∀ α, IsRoot Tag.E7 α →
      ((α ∈ rootCharKernel bz ∧ α ∈ rootCharKernel bx) ↔ α ∈ e7T3A5SubA2) := by
    intro α hα
    constructor
    · rintro ⟨hzb', hxb⟩
      rw [hkerbx] at hxb
      obtain ⟨l, hl, rfl⟩ := hxb
      rw [rootCharKernel, Set.mem_setOf_eq] at hzb'
      obtain ⟨-, h1⟩ := hzb'
      have h0 : charVal (e7T3ZColumn ε q₀) (toVec Tag.E7.rank l) = 0 :=
        (rootChar_zetaPow_eq_one_iff_charVal hζ (e7T3ZColumn ε q₀) _).1 h1
      have hmemS := (e7T3ZA_eq_zero_iff_mem l hl).1
        ((e7T3ZA_eq_zero_iff_charVal_eq_zero hp hp3 hε hq
          (isRoot_toVec (e7T3CertA5_good.2.2.1 l hl))).1 h0)
      rw [e7T3A5SubA2_eq_image]
      exact ⟨l, hmemS, rfl⟩
    · intro hS
      rw [e7T3A5SubA2_eq_image] at hS
      obtain ⟨l, hl, rfl⟩ := hS
      have hl5 := hA2sub hl
      have hAD := (e7T3ZA_eq_zero_iff_mem l hl5).2 hl
      have hroot := isRoot_toVec (e7T3CertA5_good.2.2.1 l hl5)
      refine ⟨?_, ?_⟩
      · rw [rootCharKernel, Set.mem_setOf_eq]
        exact ⟨hroot, (rootChar_zetaPow_eq_one_iff_charVal hζ (e7T3ZColumn ε q₀) _).2
          ((e7T3ZA_eq_zero_iff_charVal_eq_zero hp hp3 hε hq hroot).2 hAD)⟩
      · rw [hkerbx]
        exact ⟨l, hl5, rfl⟩
  exact ⟨z, hzA, secondPoint_not_mem_zpowers F hp hp3 hε hζ hq0ne hq hkerbx hzraw hψx,
    hzraw, hker⟩

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE7Three
