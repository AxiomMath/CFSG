module

public import CFSG.ClassicalInvolution.SmallCases.FrameDatum
public import CFSG.ClassicalInvolution.SmallCases.SmallWeylStar

public section

namespace CFSG.ClassicalInvolution

open scoped IsMulCommutative
open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.SmallWeyl

variable {F : Type*} [Field F] {G : Type*} [Group G] {Ω : Set (Subgroup G)} {A : Subgroup G}
  {S : Set (Subgroup G)}

section Data

variable {B : Type*} [AddCommGroup B]

theorem exists_path_of_valency_one {R : Finset (Datum B)} (hcard : R.card = 6)
    (hval : ∀ p ∈ R, ∃! q, q ∈ R ∧ q ≠ p ∧ ¬ p.Adj q) :
    ∃ x₀ ∈ R, ∃ x₁ ∈ R, ∃ x₂ ∈ R, x₁.Adj x₀ ∧ x₁.Adj x₂ ∧ ¬ x₀.Adj x₂ ∧ x₀ ≠ x₂ := by
  classical
  have hne : R.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨x₁, hx₁⟩ := hne
  obtain ⟨x₁', ⟨h1R, h1ne, h1na⟩, h1uniq⟩ := hval x₁ hx₁
  have hbig : ((R.erase x₁).erase x₁').Nonempty := by
    rw [← Finset.card_pos]
    have h1 := Finset.pred_card_le_card_erase (s := R) (a := x₁)
    have h2 := Finset.pred_card_le_card_erase (s := R.erase x₁) (a := x₁')
    omega
  obtain ⟨x₀, hx₀⟩ := hbig
  simp only [Finset.mem_erase] at hx₀
  obtain ⟨hx₀1', hx₀1, hx₀R⟩ := hx₀
  have a₀ : x₁.Adj x₀ := by
    by_contra hna
    exact hx₀1' (h1uniq x₀ ⟨hx₀R, hx₀1, hna⟩)
  obtain ⟨x₂, ⟨h2R, h2ne, h2na⟩, -⟩ := hval x₀ hx₀R
  have a₂ : x₁.Adj x₂ := by
    by_contra hna
    by_cases hx₂1 : x₂ = x₁
    · exact h2na (hx₂1 ▸ a₀.symm)
    · have hx₂1' : x₂ = x₁' := h1uniq x₂ ⟨h2R, hx₂1, hna⟩
      obtain ⟨y, -, hyuniq⟩ := hval x₁' h1R
      have h3 : x₁ = y := hyuniq x₁ ⟨hx₁, h1ne.symm, fun h => h1na h.symm⟩
      have h4 : x₀ = y := hyuniq x₀ ⟨hx₀R, hx₀1', fun h => h2na (hx₂1' ▸ h.symm)⟩
      exact hx₀1 (h4.trans h3.symm)
  exact ⟨x₀, hx₀R, x₁, hx₁, x₂, h2R, a₀, a₂, h2na, h2ne.symm⟩

end Data

namespace RankFrame

variable (Fr : RankFrame F Ω A S) [IsMulCommutative ↥A]

include Fr

omit [IsMulCommutative ↥A] in
theorem exists_not_commutes (hconn : NonCommConnected S) {K : Subgroup G} (hK : K ∈ S) :
    ∃ L ∈ S, K ≠ L ∧ ¬ Commutes K L := by
  obtain ⟨K₁, hK₁, L₁, hL₁, hne⟩ := Fr.two_le
  obtain ⟨L, hL, hLK⟩ : ∃ L ∈ S, L ≠ K := by
    by_cases h : K₁ = K
    · exact ⟨L₁, hL₁, fun e => hne (h.trans e.symm)⟩
    · exact ⟨K₁, hK₁, h⟩
  obtain ⟨w⟩ := hconn.preconnected ⟨K, hK⟩ ⟨L, hL⟩
  cases w with
  | nil => exact absurd rfl hLK
  | cons hadj _ =>
    obtain ⟨hne', hnc⟩ := nonCommGraph_adj.mp hadj
    exact ⟨_, Subtype.property _, fun e => hne' (Subtype.ext e), hnc⟩

theorem datum_adj_iff_not_commutes (hA2 : A2Dichotomy A S) (hfib : FibreLE2 S) {K L : ↥S}
    (hne : K ≠ L) : (Fr.datum K).Adj (Fr.datum L) ↔ ¬ Commutes (K : Subgroup G) L := by
  rw [datum_adj_iff]
  constructor
  · rintro ⟨h1, -⟩
    exact Fr.not_commutes_of_pairingAdj L.2
      ((pairingAdj_iff (Fr.isUniqueInvolution_zOf L)).mpr h1)
  · intro hnc
    have h1 : PairingAdj A (K : Subgroup G) (L : Subgroup G) :=
      (Fr.pairingAdj_iff_not_commutes hA2 hfib K.2 L.2 (fun h => hne (Subtype.ext h))).mpr hnc
    have h2 : PairingAdj A (L : Subgroup G) (K : Subgroup G) :=
      (Fr.pairingAdj_iff_not_commutes hA2 hfib L.2 K.2 (fun h => hne (Subtype.ext h.symm))).mpr
        (fun h => hnc h.symm)
    exact ⟨(pairingAdj_iff (Fr.isUniqueInvolution_zOf L)).mp h1,
      (pairingAdj_iff (Fr.isUniqueInvolution_zOf K)).mp h2⟩

theorem ne_of_adj {K L : ↥S} (h : (Fr.datum K).Adj (Fr.datum L)) : K ≠ L := by
  rintro rfl
  exact absurd h.1 (by rw [Datum.pair_self]; exact zero_ne_one)

theorem coe_ne_of_adj {K L : ↥S} (h : (Fr.datum K).Adj (Fr.datum L)) :
    (K : Subgroup G) ≠ (L : Subgroup G) := fun e => Fr.ne_of_adj h (Subtype.ext e)

theorem commutes_of_not_adj (hA2 : A2Dichotomy A S) (hfib : FibreLE2 S) {K L : ↥S}
    (hne : K ≠ L) (h : ¬ (Fr.datum K).Adj (Fr.datum L)) : Commutes (K : Subgroup G) L := by
  by_contra hc
  exact h ((Fr.datum_adj_iff_not_commutes hA2 hfib hne).mpr hc)

structure IsChainThree (K₀ K₁ K₂ : ↥S) : Prop where
  adj₀ : (Fr.datum K₁).Adj (Fr.datum K₀)
  adj₂ : (Fr.datum K₁).Adj (Fr.datum K₂)
  nadj : ¬ (Fr.datum K₀).Adj (Fr.datum K₂)
  ne : Fr.datum K₀ ≠ Fr.datum K₂

structure IsStarFour (K₀ K₁ K₂ K₃ : ↥S) : Prop where
  adj₀ : (Fr.datum K₁).Adj (Fr.datum K₀)
  adj₂ : (Fr.datum K₁).Adj (Fr.datum K₂)
  adj₃ : (Fr.datum K₁).Adj (Fr.datum K₃)
  nadj₀₂ : ¬ (Fr.datum K₀).Adj (Fr.datum K₂)
  nadj₀₃ : ¬ (Fr.datum K₀).Adj (Fr.datum K₃)
  nadj₂₃ : ¬ (Fr.datum K₂).Adj (Fr.datum K₃)
  ne₀₂ : Fr.datum K₀ ≠ Fr.datum K₂
  ne₀₃ : Fr.datum K₀ ≠ Fr.datum K₃
  ne₂₃ : Fr.datum K₂ ≠ Fr.datum K₃

theorem exists_isChainThree [Finite ↥A] (hcard : Nat.card A = 8) (hS : S.Nonempty)
    (hA2 : A2Dichotomy A S) (hfib : FibreLE2 S) (hconn : NonCommConnected S)
    (hd : Fr.dataFinset.card = 6) : ∃ K₀ K₁ K₂ : ↥S, Fr.IsChainThree K₀ K₁ K₂ := by
  rcases Fr.datum_classification_three hcard hS hA2 hfib hconn with h | ⟨h, -⟩ | ⟨-, hval⟩
  · omega
  · omega
  · obtain ⟨x₀, hx₀, x₁, hx₁, x₂, hx₂, a₀, a₂, n, hne⟩ := exists_path_of_valency_one hd hval
    obtain ⟨K₀, rfl⟩ := Fr.mem_dataFinset.mp hx₀
    obtain ⟨K₁, rfl⟩ := Fr.mem_dataFinset.mp hx₁
    obtain ⟨K₂, rfl⟩ := Fr.mem_dataFinset.mp hx₂
    exact ⟨K₀, K₁, K₂, a₀, a₂, n, hne⟩

theorem exists_isStarFour [Finite ↥A] (hcard : Nat.card A = 16) (hS : S.Nonempty)
    (hA2 : A2Dichotomy A S) (hfib : FibreLE2 S) (hconn : NonCommConnected S)
    (hd : Fr.dataFinset.card = 12) : ∃ K₀ K₁ K₂ K₃ : ↥S, Fr.IsStarFour K₀ K₁ K₂ K₃ := by
  obtain ⟨c, hc, a, ha, b, hb, d, hd', e1, e2, e3, hab, had, hbd, n1, n2, n3⟩ :=
    (rootSet_triStar_four Fr.additive_add_self
      (by rw [Nat.card_congr Additive.toMul]; exact hcard) _ (Fr.dataFinset_nonempty hS)
      (Fr.dataFinset_isSymm hA2) Fr.dataFinset_isClosed
      (Fr.dataFinset_isConn hA2 hfib hconn)).1 hd
  obtain ⟨K₁, rfl⟩ := Fr.mem_dataFinset.mp hc
  obtain ⟨K₀, rfl⟩ := Fr.mem_dataFinset.mp ha
  obtain ⟨K₂, rfl⟩ := Fr.mem_dataFinset.mp hb
  obtain ⟨K₃, rfl⟩ := Fr.mem_dataFinset.mp hd'
  exact ⟨K₀, K₁, K₂, K₃, e1, e2, e3, n1, n2, n3, hab, had, hbd⟩

@[expose] def DatumInjective : Prop := ∀ K L : ↥S, Fr.datum K = Fr.datum L → K = L

theorem datumInjective_of_card_le [Finite ↥A] [Finite ↥S]
    (h : Nat.card ↥S ≤ Fr.dataFinset.card) : Fr.DatumInjective := by
  have hcard : Fr.dataFinset.card = Nat.card (Set.range Fr.datum) := by
    unfold dataFinset
    exact (Set.ncard_eq_toFinset_card _ (Set.toFinite _)).symm.trans (Nat.card_coe_set_eq _).symm
  have hbij : (Set.rangeFactorization Fr.datum).Bijective :=
    (Set.rangeFactorization_surjective (f := Fr.datum)).bijective_of_nat_card_le (by omega)
  intro K L hKL
  exact hbij.1 (Subtype.ext hKL)

theorem datumInjective_of_fibre (hfib : FibreLE2 S)
    (h : ∀ K : ↥S, ∃ L : ↥S, Fr.zOf L = Fr.zOf K ∧ Fr.datum L ≠ Fr.datum K) :
    Fr.DatumInjective := by
  intro K K' hKK'
  by_contra hne
  obtain ⟨L, hLz, hLd⟩ := h K
  have hz' : Fr.zOf K' = Fr.zOf K := by
    have := congrArg (fun p : Datum (Additive ↥A) => ((Additive.toMul p.vec : ↥A) : G)) hKK'
    exact this.symm
  rcases hfib (Fr.zOf K) K K.2 K' K'.2 L L.2 (Fr.isUniqueInvolution_zOf K)
    (hz' ▸ Fr.isUniqueInvolution_zOf K') (hLz ▸ Fr.isUniqueInvolution_zOf L) with h1 | h1 | h1
  · exact hne (Subtype.ext h1)
  · have e : K = L := Subtype.ext h1
    exact hLd (by rw [e])
  · have e : K' = L := Subtype.ext h1
    exact hLd (by rw [← e, ← hKK'])

@[expose] noncomputable def dataIn [Finite ↥A] (V : Subgroup G) : Finset (Datum (Additive ↥A)) :=
  by classical exact Fr.dataFinset.filter fun x => ∃ M : ↥S, (M : Subgroup G) ≤ V ∧ Fr.datum M = x

theorem mem_dataIn [Finite ↥A] {V : Subgroup G} {x : Datum (Additive ↥A)} :
    x ∈ Fr.dataIn V ↔ ∃ M : ↥S, (M : Subgroup G) ≤ V ∧ Fr.datum M = x := by
  classical
  unfold dataIn
  rw [Finset.mem_filter, Fr.mem_dataFinset]
  constructor
  · exact fun h => h.2
  · rintro ⟨M, hM, rfl⟩
    exact ⟨⟨M, rfl⟩, M, hM, rfl⟩

theorem dataIn_subset [Finite ↥A] (V : Subgroup G) : Fr.dataIn V ⊆ Fr.dataFinset := by
  classical
  intro x hx
  exact (Finset.mem_filter.mp hx).1

theorem dataIn_isSymm [Finite ↥A] (hA2 : A2Dichotomy A S) (V : Subgroup G) :
    IsSymm (Fr.dataIn V) :=
  fun p hp q hq => Fr.dataFinset_isSymm hA2 p (Fr.dataIn_subset V hp) q (Fr.dataIn_subset V hq)

theorem dataIn_isClosed [Finite ↥A] (V : Subgroup G) : IsClosed (Fr.dataIn V) := by
  intro p hp q hq
  obtain ⟨K, hKV, rfl⟩ := Fr.mem_dataIn.mp hp
  obtain ⟨L, hLV, rfl⟩ := Fr.mem_dataIn.mp hq
  obtain ⟨w, hw, M, hM, hd⟩ := Fr.exists_conj_datum K L
  rw [hd]
  refine Fr.mem_dataIn.mpr ⟨M, ?_, rfl⟩
  rw [hM]
  intro x hx
  rw [mem_conjSub_iff] at hx
  have h1 := V.mul_mem (V.mul_mem (hKV hw) (hLV hx)) (V.inv_mem (hKV hw))
  have h2 : x = w * (w⁻¹ * x * w) * w⁻¹ := by group
  rw [h2]
  exact V.mul_mem (V.mul_mem (hKV hw) (hLV hx)) (V.inv_mem (hKV hw))

theorem le_of_isChainThree [Finite ↥A] (hcard : Nat.card A = 8) (hA2 : A2Dichotomy A S)
    (hinj : Fr.DatumInjective) (hd : Fr.dataFinset.card = 6) {V : Subgroup G} {K₀ K₁ K₂ : ↥S}
    (h : Fr.IsChainThree K₀ K₁ K₂) (h₀ : (K₀ : Subgroup G) ≤ V) (h₁ : (K₁ : Subgroup G) ≤ V)
    (h₂ : (K₂ : Subgroup G) ≤ V) : ∀ K ∈ S, K ≤ V := by
  have hR := rootSet_eq_of_chain_three Fr.additive_add_self
    (by rw [Nat.card_congr Additive.toMul]; exact hcard) hd (Fr.dataIn_subset V)
    (Fr.dataIn_isSymm hA2 V) (Fr.dataIn_isClosed V) (x₀ := Fr.datum K₀) (x₁ := Fr.datum K₁)
    (x₂ := Fr.datum K₂) (Fr.mem_dataIn.mpr ⟨K₀, h₀, rfl⟩) (Fr.mem_dataIn.mpr ⟨K₁, h₁, rfl⟩)
    (Fr.mem_dataIn.mpr ⟨K₂, h₂, rfl⟩) h.adj₀ h.adj₂ h.nadj h.ne
  intro K hK
  have hmem : Fr.datum ⟨K, hK⟩ ∈ Fr.dataFinset := Fr.mem_dataFinset.mpr ⟨_, rfl⟩
  rw [← hR] at hmem
  obtain ⟨M, hMV, hMd⟩ := Fr.mem_dataIn.mp hmem
  have hMK : M = ⟨K, hK⟩ := hinj M ⟨K, hK⟩ hMd
  rw [hMK] at hMV
  exact hMV

theorem le_of_isStarFour [Finite ↥A] (hcard : Nat.card A = 16) (hA2 : A2Dichotomy A S)
    (hinj : Fr.DatumInjective) (hd : Fr.dataFinset.card = 12) {V : Subgroup G} {K₀ K₁ K₂ K₃ : ↥S}
    (h : Fr.IsStarFour K₀ K₁ K₂ K₃) (h₀ : (K₀ : Subgroup G) ≤ V) (h₁ : (K₁ : Subgroup G) ≤ V)
    (h₂ : (K₂ : Subgroup G) ≤ V) (h₃ : (K₃ : Subgroup G) ≤ V) : ∀ K ∈ S, K ≤ V := by
  have hR := rootSet_eq_of_star_four Fr.additive_add_self
    (by rw [Nat.card_congr Additive.toMul]; exact hcard) hd (Fr.dataIn_subset V)
    (Fr.dataIn_isSymm hA2 V) (Fr.dataIn_isClosed V) (x₀ := Fr.datum K₀) (x₁ := Fr.datum K₁)
    (x₂ := Fr.datum K₂) (x₃ := Fr.datum K₃) (Fr.mem_dataIn.mpr ⟨K₀, h₀, rfl⟩)
    (Fr.mem_dataIn.mpr ⟨K₁, h₁, rfl⟩) (Fr.mem_dataIn.mpr ⟨K₂, h₂, rfl⟩)
    (Fr.mem_dataIn.mpr ⟨K₃, h₃, rfl⟩) h.adj₀ h.adj₂ h.adj₃ h.nadj₀₂ h.nadj₀₃ h.nadj₂₃ h.ne₀₂
    h.ne₀₃ h.ne₂₃
  intro K hK
  have hmem : Fr.datum ⟨K, hK⟩ ∈ Fr.dataFinset := Fr.mem_dataFinset.mpr ⟨_, rfl⟩
  rw [← hR] at hmem
  obtain ⟨M, hMV, hMd⟩ := Fr.mem_dataIn.mp hmem
  have hMK : M = ⟨K, hK⟩ := hinj M ⟨K, hK⟩ hMd
  rw [hMK] at hMV
  exact hMV

end RankFrame

end CFSG.ClassicalInvolution
