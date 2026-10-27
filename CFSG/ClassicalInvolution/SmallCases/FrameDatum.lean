module

public import CFSG.ClassicalInvolution.SmallCases.LocalDatumRank
public import CFSG.ClassicalInvolution.SmallCases.SmallWeylFour
public import CFSG.ClassicalInvolution.Balance.FrameIndex.Pairing

public section

namespace CFSG.ClassicalInvolution

open scoped IsMulCommutative
open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.SmallWeyl

variable {F : Type*} [Field F] {G : Type*} [Group G] {Ω : Set (Subgroup G)} {A : Subgroup G}
  {S : Set (Subgroup G)}

private theorem zmod_two_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x
  decide

namespace RankFrame

variable (Fr : RankFrame F Ω A S)

include Fr

theorem comm_of_mem {x y : G} (hx : x ∈ A) (hy : y ∈ A) : x * y = y * x := by
  have h1 := Fr.elem (x * y) (A.mul_mem hx hy)
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right (Fr.elem x hx)
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right (Fr.elem y hy)
  have hxyi : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right h1
  calc x * y = (x * y)⁻¹ := hxyi.symm
    _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
    _ = y * x := by rw [hxi, hyi]

theorem isMulCommutative : IsMulCommutative ↥A :=
  ⟨⟨fun x y => Subtype.ext (Fr.comm_of_mem x.2 y.2)⟩⟩

theorem exists_isUniqueInvolution {K : Subgroup G} (hK : K ∈ S) : ∃ z, IsUniqueInvolution K z := by
  have := Fr.finite
  obtain ⟨φ, rfl, hD⟩ := Fr.inSigma hK
  exact ⟨_, hD.isUniqueInvolution Fr.odd⟩

theorem axisChar_mul {K : Subgroup G} (hK : K ∈ S) {x y : G} (hx : x ∈ A) (hy : y ∈ A) :
    axisChar A K (x * y) = axisChar A K x + axisChar A K y := by
  obtain ⟨a, haA, haN, hsplit⟩ := (Fr.inSigma hK).exists_split
  by_cases h1 : x ∈ axisSub A K <;> by_cases h2 : y ∈ axisSub A K
  · have h3 : x * y ∈ axisSub A K := (axisSub A K).mul_mem h1 h2
    rw [axisChar_of_mem h3, axisChar_of_mem h1, axisChar_of_mem h2]
    rfl
  · have h3 : x * y ∉ axisSub A K := fun h => h2 (by
      have := (axisSub A K).mul_mem ((axisSub A K).inv_mem h1) h
      simpa using this)
    rw [axisChar_of_not_mem h3, axisChar_of_mem h1, axisChar_of_not_mem h2]
    simp
  · have h3 : x * y ∉ axisSub A K := fun h => h1 (by
      have := (axisSub A K).mul_mem h ((axisSub A K).inv_mem h2)
      simpa using this)
    rw [axisChar_of_not_mem h3, axisChar_of_not_mem h1, axisChar_of_mem h2]
    simp
  · have hxa : x * a ∈ axisSub A K := (hsplit x hx).resolve_left h1
    have hya : y * a ∈ axisSub A K := (hsplit y hy).resolve_left h2
    have h3 : x * y ∈ axisSub A K := by
      have h4 := (axisSub A K).mul_mem hxa hya
      have e1 : x * a * (y * a) = x * y := by
        calc x * a * (y * a) = x * (a * y) * a := by group
          _ = x * (y * a) * a := by rw [Fr.comm_of_mem haA hy]
          _ = x * y * (a * a) := by group
          _ = x * y := by rw [Fr.elem a haA, mul_one]
      rwa [e1] at h4
    rw [axisChar_of_mem h3, axisChar_of_not_mem h1, axisChar_of_not_mem h2]
    decide

theorem conj_inv_of_not_mem_axis {K : Subgroup G} (hK : K ∈ S) {zK : G}
    (hzK : IsUniqueInvolution K zK) {w : G} (hw : w ∈ normPart K A) (hw' : w ∉ centPart K A)
    {e : G} (he : e ∈ A) (hn : e ∉ axisSub A K) : w⁻¹ * e * w = e * zK := by
  have := Fr.finite
  have h1 : w * e * w⁻¹ = e * zK :=
    (Fr.inSigma hK).conj_eq_mul_of_not_mem_axis Fr.odd hzK hw hw' he hn
  have h2 : w * w = zK := (Fr.inSigma hK).sq_eq_of_mem Fr.odd hzK hw hw'
  have h4 : w⁻¹ * zK * w = zK := by
    rw [← h2]
    group
  have h5 : w⁻¹ * (e * zK) * w = e := by
    rw [← h1]
    group
  have h6 : w⁻¹ * (e * zK) * w = (w⁻¹ * e * w) * (w⁻¹ * zK * w) := by group
  rw [h6, h4] at h5
  calc w⁻¹ * e * w = (w⁻¹ * e * w) * (zK * zK) := by rw [hzK.sq, mul_one]
    _ = ((w⁻¹ * e * w) * zK) * zK := (mul_assoc _ _ _).symm
    _ = e * zK := by rw [h5]

theorem axisChar_conjSub {K L : Subgroup G} (hK : K ∈ S) (hL : L ∈ S) {zK : G}
    (hzK : IsUniqueInvolution K zK) {w : G} (hw : w ∈ normPart K A) (hw' : w ∉ centPart K A)
    {e : G} (he : e ∈ A) :
    axisChar A (conjSub w L) e = axisChar A L e + axisChar A L zK * axisChar A K e := by
  have := Fr.finite
  have hwN : w ∈ Subgroup.normalizer (A : Set G) := (mem_normPart_iff.mp hw).2
  have hzKA : zK ∈ A := Fr.mem_of_isUniqueInvolution hK hzK
  have key : e ∈ axisSub A (conjSub w L) ↔ w⁻¹ * e * w ∈ axisSub A L := by
    rw [axisSub_conjSub hwN L, mem_conjSub_iff]
  have h1 : axisChar A (conjSub w L) e = axisChar A L (w⁻¹ * e * w) := by
    by_cases h : w⁻¹ * e * w ∈ axisSub A L
    · rw [axisChar_of_mem h, axisChar_of_mem (key.mpr h)]
    · rw [axisChar_of_not_mem h, axisChar_of_not_mem (fun h' => h (key.mp h'))]
  rw [h1]
  by_cases he' : e ∈ axisSub A K
  · have h2 : w⁻¹ * e * w = e := by
      have := InSigma.conj_eq_of_mem_axis (K.inv_mem (normPart_le_left K A hw)) he'
      simpa using this
    rw [h2, axisChar_of_mem he', mul_zero, add_zero]
  · rw [Fr.conj_inv_of_not_mem_axis hK hzK hw hw' he he', Fr.axisChar_mul hL he hzKA,
      axisChar_of_not_mem he', mul_one]

theorem mem_axisSub_of_isUniqueInvolution {K : Subgroup G} (hK : K ∈ S) {z : G}
    (hz : IsUniqueInvolution K z) : z ∈ axisSub A K := by
  have := Fr.finite
  exact (Fr.inSigma hK).unique_involution_mem_axis Fr.odd hz

@[expose] noncomputable def zOf (K : ↥S) : G := Classical.choose (Fr.exists_isUniqueInvolution K.2)

theorem isUniqueInvolution_zOf (K : ↥S) : IsUniqueInvolution (K : Subgroup G) (Fr.zOf K) :=
  Classical.choose_spec (Fr.exists_isUniqueInvolution K.2)

theorem zOf_mem (K : ↥S) : Fr.zOf K ∈ A :=
  Fr.mem_of_isUniqueInvolution K.2 (Fr.isUniqueInvolution_zOf K)

theorem zOf_mem_axisSub (K : ↥S) : Fr.zOf K ∈ axisSub A (K : Subgroup G) :=
  Fr.mem_axisSub_of_isUniqueInvolution K.2 (Fr.isUniqueInvolution_zOf K)

theorem not_commutes_of_pairingAdj {K L : Subgroup G} (hL : L ∈ S) (h : PairingAdj A K L) :
    ¬ Commutes K L := by
  obtain ⟨z, hz, hzn⟩ := h
  intro hc
  apply hzn
  exact mem_axisSub_iff.mpr ⟨Fr.mem_of_isUniqueInvolution hL hz,
    fun k hk => hc k hk z hz.mem⟩

theorem not_pairingAdj_self {K : Subgroup G} (hK : K ∈ S) : ¬ PairingAdj A K K := by
  rintro ⟨z, hz, hzn⟩
  exact hzn (Fr.mem_axisSub_of_isUniqueInvolution hK hz)

theorem isLine_cases {K L : Subgroup G} (hK : K ∈ S) (hL : L ∈ S) (hne : K ≠ L)
    (hl : IsLine A K L) {zK zL : G} (hzK : IsUniqueInvolution K zK)
    (hzL : IsUniqueInvolution L zL) :
    (zL ∈ axisSub A K ∧ zK ∈ axisSub A L ∧ zL = zK ∧
        ∃ M ∈ S, M ≠ K ∧ M ≠ L ∧ IsUniqueInvolution M zL) ∨
      (zL ∉ axisSub A K ∧ zK ∉ axisSub A L) := by
  have := Fr.finite
  obtain ⟨wK, hwK, hwK', wL, hwL, hwL', hswap, -⟩ := hl.swap
  have hzKE : zK ∈ A := Fr.mem_of_isUniqueInvolution hK hzK
  have hzLE : zL ∈ A := Fr.mem_of_isUniqueInvolution hL hzL
  have hwKN : wK ∈ Subgroup.normalizer (A : Set G) := (mem_normPart_iff.mp hwK).2
  have hwLN : wL ∈ Subgroup.normalizer (A : Set G) := (mem_normPart_iff.mp hwL).2
  have hKs := Fr.inSigma hK
  have hLs := Fr.inSigma hL
  have heq : wK * zL * wK⁻¹ = wL * zK * wL⁻¹ := by
    have a1 := hzL.conj wK
    have a2 := hzK.conj wL
    rw [hswap] at a1
    exact a1.eq a2
  by_cases h1 : zL ∈ axisSub A K <;> by_cases h2 : zK ∈ axisSub A L
  · left
    have e1 : wK * zL * wK⁻¹ = zL :=
      InSigma.conj_eq_of_mem_axis (E := A) (K := K) (normPart_le_left K A hwK) h1
    have e2 : wL * zK * wL⁻¹ = zK :=
      InSigma.conj_eq_of_mem_axis (E := A) (K := L) (normPart_le_left L A hwL) h2
    have hzz : zL = zK := by rw [← e1, ← e2, heq]
    refine ⟨h1, h2, hzz, conjSub wK L, Fr.conj_mem hwKN hL, ?_, ?_, ?_⟩
    · exact conjSub_ne_of_ne (normPart_le_left K A hwK) hne
    · intro h
      rw [hswap] at h
      exact conjSub_ne_of_ne (normPart_le_left L A hwL) hne.symm h
    · have := hzL.conj wK
      rwa [e1] at this
  · exfalso
    have e1 : wK * zL * wK⁻¹ = zL :=
      InSigma.conj_eq_of_mem_axis (E := A) (K := K) (normPart_le_left K A hwK) h1
    have e2 : wL * zK * wL⁻¹ = zK * zL :=
      hLs.conj_eq_mul_of_not_mem_axis Fr.odd hzL hwL hwL' hzKE h2
    rw [e1, e2] at heq
    apply hzK.ne_one
    have : zK * zL = 1 * zL := by rw [← heq, one_mul]
    exact mul_right_cancel this
  · exfalso
    have e1 : wK * zL * wK⁻¹ = zL * zK :=
      hKs.conj_eq_mul_of_not_mem_axis Fr.odd hzK hwK hwK' hzLE h1
    have e2 : wL * zK * wL⁻¹ = zK :=
      InSigma.conj_eq_of_mem_axis (E := A) (K := L) (normPart_le_left L A hwL) h2
    rw [e1, e2] at heq
    apply hzL.ne_one
    have : zL * zK = 1 * zK := by rw [heq, one_mul]
    exact mul_right_cancel this
  · right
    exact ⟨h1, h2⟩

theorem pairingSymmetric (hA2 : A2Dichotomy A S) : PairingSymmetric A S := by
  intro K hK L hL h
  have hne : K ≠ L := by
    rintro rfl
    exact Fr.not_pairingAdj_self hK h
  have hnc := Fr.not_commutes_of_pairingAdj hL h
  have hl : IsLine A K L := (hA2 K hK L hL hne).resolve_left hnc
  obtain ⟨zK, hzK⟩ := Fr.exists_isUniqueInvolution hK
  obtain ⟨zL, hzL⟩ := Fr.exists_isUniqueInvolution hL
  have h' : zL ∉ axisSub A K := (pairingAdj_iff hzL).mp h
  rcases Fr.isLine_cases hK hL hne hl hzK hzL with ⟨h1, -⟩ | ⟨-, h2⟩
  · exact absurd h1 h'
  · exact (pairingAdj_iff hzK).mpr h2

theorem pairingAdj_iff_not_commutes (hA2 : A2Dichotomy A S) (hfib : FibreLE2 S)
    {K L : Subgroup G} (hK : K ∈ S) (hL : L ∈ S) (hne : K ≠ L) :
    PairingAdj A K L ↔ ¬ Commutes K L := by
  refine ⟨Fr.not_commutes_of_pairingAdj hL, fun hnc => ?_⟩
  have hl : IsLine A K L := (hA2 K hK L hL hne).resolve_left hnc
  obtain ⟨zK, hzK⟩ := Fr.exists_isUniqueInvolution hK
  obtain ⟨zL, hzL⟩ := Fr.exists_isUniqueInvolution hL
  rw [pairingAdj_iff hzL]
  rcases Fr.isLine_cases hK hL hne hl hzK hzL with ⟨-, -, hzz, M, hM, hMK, hML, hzM⟩ | ⟨h1, -⟩
  · exfalso
    have hzK' : IsUniqueInvolution K zL := by rwa [hzz]
    rcases hfib zL K hK L hL M hM hzK' hzL hzM with h | h | h
    · exact hne h
    · exact hMK h.symm
    · exact hML h.symm
  · exact h1

theorem pairingConnected (hA2 : A2Dichotomy A S) (hfib : FibreLE2 S)
    (hconn : NonCommConnected S) : PairingConnected A S := by
  intro K L
  have h := (SimpleGraph.reachable_iff_reflTransGen _ _).mp (hconn.preconnected K L)
  refine Relation.ReflTransGen.mono (fun K' L' hadj => ?_) K L h
  obtain ⟨hne, hnc⟩ := nonCommGraph_adj.mp hadj
  exact (Fr.pairingAdj_iff_not_commutes hA2 hfib K'.2 L'.2 (fun h => hne (Subtype.ext h))).mpr hnc

@[expose] noncomputable def chiOf [IsMulCommutative ↥A] (K : ↥S) : Additive ↥A →+ ZMod 2 where
  toFun x := axisChar A K ((Additive.toMul x : ↥A) : G)
  map_zero' := axisChar_of_mem (axisSub A (K : Subgroup G)).one_mem
  map_add' x y := Fr.axisChar_mul K.2 (Additive.toMul x).2 (Additive.toMul y).2

@[expose] noncomputable def datum [IsMulCommutative ↥A] (K : ↥S) : Datum (Additive ↥A) where
  vec := Additive.ofMul ⟨Fr.zOf K, Fr.zOf_mem K⟩
  form := Fr.chiOf K
  vec_ne_zero := fun h => (Fr.isUniqueInvolution_zOf K).ne_one
    (congrArg (fun x : Additive ↥A => ((Additive.toMul x : ↥A) : G)) h)
  form_ne_zero := fun h => by
    obtain ⟨a, haA, ha⟩ := (Fr.inSigma K.2).exists_mem_not_mem_axis
    have h1 := congrArg (fun f : Additive ↥A →+ ZMod 2 => f (Additive.ofMul ⟨a, haA⟩)) h
    simp only [chiOf, AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.zero_apply] at h1
    exact ha (axisChar_eq_zero_iff.mp h1)
  form_vec := axisChar_of_mem (Fr.zOf_mem_axisSub K)

variable [IsMulCommutative ↥A]

theorem datum_pair (K L : ↥S) :
    (Fr.datum K).pair (Fr.datum L) = axisChar A K (Fr.zOf L) := rfl

theorem datum_adj_iff (K L : ↥S) :
    (Fr.datum K).Adj (Fr.datum L) ↔
      Fr.zOf L ∉ axisSub A (K : Subgroup G) ∧ Fr.zOf K ∉ axisSub A (L : Subgroup G) := by
  have key : ∀ (X Y : ↥S), (Fr.datum X).pair (Fr.datum Y) = 1 ↔
      Fr.zOf Y ∉ axisSub A (X : Subgroup G) := fun X Y => by
    rw [datum_pair]
    constructor
    · intro h hmem
      rw [axisChar_of_mem hmem] at h
      exact zero_ne_one h
    · exact fun h => axisChar_of_not_mem h
  exact and_congr (key K L) (key L K)

theorem exists_conj_datum (K L : ↥S) : ∃ w ∈ (K : Subgroup G), ∃ M : ↥S,
    (M : Subgroup G) = conjSub w L ∧ (Fr.datum K).conj (Fr.datum L) = Fr.datum M := by
  have := Fr.finite
  obtain ⟨w, hw, hw'⟩ := (Fr.inSigma K.2).exists_mem_normPart_not_mem_centPart Fr.odd Fr.five
  have hwN : w ∈ Subgroup.normalizer (A : Set G) := (mem_normPart_iff.mp hw).2
  obtain ⟨M, hM⟩ : ∃ M : ↥S, (M : Subgroup G) = conjSub w L :=
    ⟨⟨conjSub w L, Fr.conj_mem hwN L.2⟩, rfl⟩
  have hzM : Fr.zOf M = w * Fr.zOf L * w⁻¹ := by
    have h := (Fr.isUniqueInvolution_zOf L).conj w
    rw [← hM] at h
    exact (Fr.isUniqueInvolution_zOf M).eq h
  refine ⟨w, normPart_le_left (K : Subgroup G) A hw, M, hM, Datum.ext ?_ ?_⟩
  · by_cases h : Fr.zOf L ∈ axisSub A (K : Subgroup G)
    · have h1 : Fr.zOf M = Fr.zOf L := by
        rw [hzM]
        exact InSigma.conj_eq_of_mem_axis (E := A) (K := (K : Subgroup G))
          (normPart_le_left (K : Subgroup G) A hw) h
      have hp : ¬ (Fr.datum K).pair (Fr.datum L) = 1 := by
        rw [datum_pair, axisChar_of_mem h]
        exact zero_ne_one
      simp only [Datum.conj, hp, ↓reduceIte, add_zero]
      exact congrArg Additive.ofMul (Subtype.ext h1.symm)
    · have h1 : Fr.zOf M = Fr.zOf L * Fr.zOf K := by
        rw [hzM]
        exact (Fr.inSigma K.2).conj_eq_mul_of_not_mem_axis Fr.odd (Fr.isUniqueInvolution_zOf K)
          hw hw' (Fr.zOf_mem L) h
      have hp : (Fr.datum K).pair (Fr.datum L) = 1 := by
        rw [datum_pair]
        exact axisChar_of_not_mem h
      simp only [Datum.conj, hp, ↓reduceIte]
      exact congrArg Additive.ofMul (Subtype.ext h1.symm)
  · ext x
    obtain ⟨e, rfl⟩ := Additive.ofMul.surjective x
    have h1 := Fr.axisChar_conjSub K.2 L.2 (Fr.isUniqueInvolution_zOf K) hw hw' e.2
    rw [← hM] at h1
    have hq : (Fr.datum L).pair (Fr.datum K) = axisChar A (L : Subgroup G) (Fr.zOf K) := rfl
    show axisChar A (L : Subgroup G) (e : G) + _ = axisChar A (M : Subgroup G) (e : G)
    rw [h1]
    by_cases hq1 : axisChar A (L : Subgroup G) (Fr.zOf K) = 1
    · have : (Fr.datum L).pair (Fr.datum K) = 1 := by rw [hq, hq1]
      simp only [this, ↓reduceIte, hq1, one_mul]
      rfl
    · have h0 : axisChar A (L : Subgroup G) (Fr.zOf K) = 0 := by
        rcases zmod_two_cases (axisChar A (L : Subgroup G) (Fr.zOf K)) with h | h
        · exact h
        · exact absurd h hq1
      have : ¬ (Fr.datum L).pair (Fr.datum K) = 1 := by rw [hq, h0]; exact zero_ne_one
      simp [this, h0]

theorem datum_conj (K L : ↥S) : ∃ M : ↥S, (Fr.datum K).conj (Fr.datum L) = Fr.datum M := by
  obtain ⟨-, -, M, -, h⟩ := Fr.exists_conj_datum K L
  exact ⟨M, h⟩

theorem datum_pair_symm (hA2 : A2Dichotomy A S) (K L : ↥S) :
    (Fr.datum K).pair (Fr.datum L) = (Fr.datum L).pair (Fr.datum K) := by
  have hsym := Fr.pairingSymmetric hA2
  rw [datum_pair, datum_pair]
  by_cases h : Fr.zOf L ∈ axisSub A (K : Subgroup G)
  · rw [axisChar_of_mem h]
    symm
    rw [axisChar_eq_zero_iff]
    by_contra h'
    have h1 : PairingAdj A (L : Subgroup G) (K : Subgroup G) :=
      (pairingAdj_iff (Fr.isUniqueInvolution_zOf K)).mpr h'
    have h2 := hsym L L.2 K K.2 h1
    exact ((pairingAdj_iff (Fr.isUniqueInvolution_zOf L)).mp h2) h
  · have h1 : PairingAdj A (K : Subgroup G) (L : Subgroup G) :=
      (pairingAdj_iff (Fr.isUniqueInvolution_zOf L)).mpr h
    have h2 := hsym K K.2 L L.2 h1
    have h3 := (pairingAdj_iff (Fr.isUniqueInvolution_zOf K)).mp h2
    rw [axisChar_of_not_mem h, axisChar_of_not_mem h3]

@[expose] noncomputable def dataFinset [Finite ↥A] : Finset (Datum (Additive ↥A)) :=
  (Set.toFinite (Set.range Fr.datum)).toFinset

theorem mem_dataFinset [Finite ↥A] {p : Datum (Additive ↥A)} :
    p ∈ Fr.dataFinset ↔ ∃ K : ↥S, Fr.datum K = p := by
  simp [dataFinset]

theorem dataFinset_nonempty [Finite ↥A] (hS : S.Nonempty) : Fr.dataFinset.Nonempty := by
  obtain ⟨K, hK⟩ := hS
  exact ⟨Fr.datum ⟨K, hK⟩, Fr.mem_dataFinset.mpr ⟨⟨K, hK⟩, rfl⟩⟩

theorem dataFinset_isSymm [Finite ↥A] (hA2 : A2Dichotomy A S) : IsSymm Fr.dataFinset := by
  intro p hp q hq
  obtain ⟨K, rfl⟩ := Fr.mem_dataFinset.mp hp
  obtain ⟨L, rfl⟩ := Fr.mem_dataFinset.mp hq
  exact Fr.datum_pair_symm hA2 K L

theorem dataFinset_isClosed [Finite ↥A] : IsClosed Fr.dataFinset := by
  intro p hp q hq
  obtain ⟨K, rfl⟩ := Fr.mem_dataFinset.mp hp
  obtain ⟨L, rfl⟩ := Fr.mem_dataFinset.mp hq
  obtain ⟨M, hM⟩ := Fr.datum_conj K L
  rw [hM]
  exact Fr.mem_dataFinset.mpr ⟨M, rfl⟩

theorem dataFinset_isConn [Finite ↥A] (hA2 : A2Dichotomy A S) (hfib : FibreLE2 S)
    (hconn : NonCommConnected S) : IsConn Fr.dataFinset := by
  have hsym := Fr.pairingSymmetric hA2
  have hPC := Fr.pairingConnected hA2 hfib hconn
  intro p hp q hq
  obtain ⟨K, rfl⟩ := Fr.mem_dataFinset.mp hp
  obtain ⟨L, rfl⟩ := Fr.mem_dataFinset.mp hq
  refine (hPC K L).lift Fr.datum fun a b hab => ?_
  refine ⟨Fr.mem_dataFinset.mpr ⟨a, rfl⟩, Fr.mem_dataFinset.mpr ⟨b, rfl⟩, ?_⟩
  rw [datum_adj_iff]
  exact ⟨(pairingAdj_iff (Fr.isUniqueInvolution_zOf b)).mp hab,
    (pairingAdj_iff (Fr.isUniqueInvolution_zOf a)).mp (hsym a a.2 b b.2 hab)⟩

omit [IsMulCommutative ↥A] in
theorem additive_add_self (x : Additive ↥A) : x + x = 0 := by
  have := Fr.elem (Additive.toMul x : ↥A) (Additive.toMul x : ↥A).2
  apply Additive.toMul.injective
  apply Subtype.ext
  simpa using this

theorem datum_classification_two [Finite ↥A] (hcard : Nat.card A = 4) (hS : S.Nonempty)
    (hA2 : A2Dichotomy A S) (hfib : FibreLE2 S) (hconn : NonCommConnected S) :
    Fr.dataFinset.card = 1 ∨ (Fr.dataFinset.card = 3 ∧ ∀ p ∈ Fr.dataFinset, ∀ q ∈ Fr.dataFinset,
      p ≠ q → p.Adj q) :=
  rootSet_classification_two Fr.additive_add_self
    (by rw [Nat.card_congr Additive.toMul]; exact hcard) _ (Fr.dataFinset_nonempty hS)
    (Fr.dataFinset_isSymm hA2) Fr.dataFinset_isClosed (Fr.dataFinset_isConn hA2 hfib hconn)

theorem datum_classification_three [Finite ↥A] (hcard : Nat.card A = 8) (hS : S.Nonempty)
    (hA2 : A2Dichotomy A S) (hfib : FibreLE2 S) (hconn : NonCommConnected S) :
    Fr.dataFinset.card = 1 ∨ (Fr.dataFinset.card = 3 ∧ ∀ p ∈ Fr.dataFinset, ∀ q ∈ Fr.dataFinset,
      p ≠ q → p.Adj q) ∨ (Fr.dataFinset.card = 6 ∧ ∀ p ∈ Fr.dataFinset,
        ∃! q, q ∈ Fr.dataFinset ∧ q ≠ p ∧ ¬ p.Adj q) :=
  rootSet_classification_three Fr.additive_add_self
    (by rw [Nat.card_congr Additive.toMul]; exact hcard) _ (Fr.dataFinset_nonempty hS)
    (Fr.dataFinset_isSymm hA2) Fr.dataFinset_isClosed (Fr.dataFinset_isConn hA2 hfib hconn)

theorem datum_classification_four [Finite ↥A] (hcard : Nat.card A = 16) (hS : S.Nonempty)
    (hA2 : A2Dichotomy A S) (hfib : FibreLE2 S) (hconn : NonCommConnected S) :
    Fr.dataFinset.card = 1 ∨ (Fr.dataFinset.card = 3 ∧ ∀ p ∈ Fr.dataFinset, ∀ q ∈ Fr.dataFinset,
      p ≠ q → p.Adj q) ∨ (Fr.dataFinset.card = 6 ∧ ∀ p ∈ Fr.dataFinset,
        ∃! q, q ∈ Fr.dataFinset ∧ q ≠ p ∧ ¬ p.Adj q) ∨
      (Fr.dataFinset.card = 10 ∧ ∀ p ∈ Fr.dataFinset,
        Set.ncard {q | q ∈ Fr.dataFinset ∧ q ≠ p ∧ ¬ p.Adj q} = 3) ∨
      (Fr.dataFinset.card = 12 ∧ ∀ p ∈ Fr.dataFinset,
        Set.ncard {q | q ∈ Fr.dataFinset ∧ q ≠ p ∧ ¬ p.Adj q} = 3) ∨
      (Fr.dataFinset.card = 15 ∧ ∀ p ∈ Fr.dataFinset,
        Set.ncard {q | q ∈ Fr.dataFinset ∧ q ≠ p ∧ ¬ p.Adj q} = 6) :=
  rootSet_classification_four Fr.additive_add_self
    (by rw [Nat.card_congr Additive.toMul]; exact hcard) _ (Fr.dataFinset_nonempty hS)
    (Fr.dataFinset_isSymm hA2) Fr.dataFinset_isClosed (Fr.dataFinset_isConn hA2 hfib hconn)

end RankFrame

end CFSG.ClassicalInvolution
