module

public import CFSG.Quasithin.H13.U3E61
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3SixAction

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.SteinbergCB Module
open scoped IsMulCommutative

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem u3_E61_maximality_and_uniqueness_F4 (h1332 : Stmt13_3_2_F4) {T L V : Subgroup G} {z : G}
    (hH : QTH13 G T L) (hF : QTU3InternalFrame T L V z) :
    InM T (normalizer (L : Set G)) ∧
      IsUniqueM (normalizer ((T ⊓ centralizer (V : Set G) : Subgroup G) : Set G) ⊓
        (normalizer (L : Set G) ⊓ normalizer (V : Set G))) (normalizer (L : Set G)) := by
  obtain ⟨-, -, -, ⟨hMmax, hLT, huniq⟩, -⟩ :=
    u3_original_local_maximality_and_unique_normalizer_of_1332_F4 h1332 hH
  obtain ⟨-, -, -, -, -, -, hLV, hTV, -, -, hTC, -, -⟩ := hF
  have hX : L ⊔ T ≤ normalizer ((T ⊓ centralizer (V : Set G) : Subgroup G) : Set G) ⊓
      (normalizer (L : Set G) ⊓ normalizer (V : Set G)) := by
    refine le_inf ?_ (le_inf hLT (sup_le hLV hTV))
    rw [hTC]
    exact LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T)
  exact ⟨⟨hMmax, le_sup_right.trans hLT⟩, ⟨hMmax, inf_le_right.trans inf_le_left⟩,
    fun M' hM' => huniq M' hM'.1 (hX.trans hM'.2)⟩

theorem u3_E61_F4 (h1332 : Stmt13_3_2_F4) {T L V : Subgroup G} {z : G} (hH : QTH13 G T L)
    (hF : QTU3InternalFrame T L V z) : E6.HypE61 T (normalizer (L : Set G)) V := by
  obtain ⟨hinM, huniq⟩ := u3_E61_maximality_and_uniqueness_F4 h1332 hH hF
  obtain ⟨-, -, hTIM, -, -⟩ := u3_selected_local_normalizer_and_TI_of_1332_F4 h1332 hH hF
  obtain ⟨hTL, hVT, hVe, hV64, -, -, -, hTV, -, -, -, -, -⟩ := hF
  have hV1 : V ≠ ⊥ := by
    intro h
    rw [h, card_bot] at hV64
    norm_num at hV64
  refine
    { simple := hH.simple
      nonabelian := hH.nonabelian
      qtke := hH.qtke
      sylow := hH.sylow
      inM := hinM
      ne_bot := hV1
      isElemAbelian := ⟨hVe.toIsMulCommutative, fun x hx =>
        elemPow_eq_one_of_isElementaryAbelian (A := V) x hx⟩
      le := hVT
      normal := hTV
      tiSet := ⟨hVT.trans hTL, fun g hg hgN => ?_⟩
      unique := huniq }
  rw [conjSubgroup_eq_conjugate]
  rcases hTIM g hg with h | h
  · exfalso
    apply hgN
    rw [mem_normalizer_iff]
    intro x
    rw [← mem_conjugate_iff', h]
  · exact h

theorem u3_hyperplane_centralizer_eq_F4
    (h1332 : Stmt13_3_2_F4) {T L V : Subgroup G} {z : G}
    (hH : QTH13 G T L) (hU3 : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1)
    (hF : QTU3InternalFrame T L V z) {W : Subgroup G} (hWV : W ≤ V) (hW2 : W.relIndex V = 2) :
    normalizer (L : Set G) ⊓ centralizer (W : Set G) =
        normalizer (L : Set G) ⊓ centralizer (V : Set G) ∧
      twoPrimeResidual (normalizer (L : Set G) ⊓ centralizer (W : Set G)) ≤
        normalizer (L : Set G) ⊓ centralizer (V : Set G) := by
  have hVe : IsElementaryAbelian 2 V := hF.2.2.1
  have hV64 : Nat.card V = 64 := hF.2.2.2.1
  obtain ⟨-, -, hTIM, -, -⟩ := u3_selected_local_normalizer_and_TI_of_1332_F4 h1332 hH hF
  obtain ⟨-, b, -, -, -, hprof⟩ := u3_six_action_profile_producer_F4 h1332 G T L V z hH hU3 hF
  have hW1 : W ≠ ⊥ := ne_bot_of_relIndex_eq_two hWV hW2 (by rw [hV64]; norm_num)
  have hWcard : Nat.card W * 2 = 64 := by
    have h1 := card_mul_relIndex hWV
    rw [hW2, hV64] at h1
    exact h1
  have heq : normalizer (L : Set G) ⊓ centralizer (W : Set G) =
      normalizer (L : Set G) ⊓ centralizer (V : Set G) := by
    refine le_antisymm (fun m ⟨hmM, hmW⟩ => ⟨hmM, ?_⟩)
      (inf_le_inf_left _ (Subgroup.centralizer_le hWV))

    have hmV : m ∈ normalizer (V : Set G) := by
      rcases hTIM m hmM with h | h
      · rw [mem_normalizer_iff]
        intro x
        rw [← mem_conjugate_iff', h]
      · exfalso
        apply hW1
        rw [eq_bot_iff, ← h]
        intro w hw
        refine ⟨hWV hw, mem_conjugate_iff'.2 ?_⟩
        rw [← (mem_centralizer_iff.1 hmW) w hw, mul_inv_cancel_right]
        exact hWV hw
    set n : normalizer (V : Set G) := ⟨m, hmV⟩
    set e := u3ConjLin V (normalizer (V : Set G)) le_rfl n with he
    have hm2 : m ^ 2 ∈ centralizer (V : Set G) :=
      sq_mem_centralizer_of_index_two (fun v hv => elemPow_eq_one_of_isElementaryAbelian v hv)
        hWV hW2 hmV hmW
    have he2 : e ^ 2 = 1 := by
      rw [he, ← map_pow]
      exact (u3ConjLin_eq_one_iff (n ^ 2)).2 hm2
    by_contra hmC
    have he1 : e ≠ 1 := fun h => hmC ((u3ConjLin_eq_one_iff n).1 h)
    have hord : orderOf e = 2 := orderOf_eq_prime he2 he1
    have hrank := hprof.2.2.2.2.1 e ⟨n, rfl⟩ hord
    have hcard := two_pow_linRank_mul_card (hH := (le_rfl : normalizer (V : Set G) ≤ _)) n
    have hWC : W ≤ V ⊓ centralizer ({(n : G)} : Set G) := fun w hw =>
      ⟨hWV hw, mem_centralizer_singleton_iff.2 ((mem_centralizer_iff.1 hmW) w hw)⟩
    have h1 := Subgroup.card_le_of_le hWC
    have h2 : 2 ^ 2 ≤ 2 ^ linRank e := Nat.pow_le_pow_right (by norm_num) hrank
    rw [hV64] at hcard
    have h3 : 2 ^ linRank e * Nat.card W ≤ 64 :=
      hcard ▸ Nat.mul_le_mul_left _ h1
    nlinarith
  refine ⟨heq, ?_⟩
  rw [← heq]
  exact iInf₂_le _ ⟨le_rfl, le_normalizer, by rw [relIndex_self]; norm_num⟩

theorem u3_hyperplane_centralizer_F4
    (h1332 : Stmt13_3_2_F4) (h311 : Theorem311Stmt)
    {T L V : Subgroup G} {z : G} (hH : QTH13 G T L)
    (hU3 : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) (hF : QTU3InternalFrame T L V z)
    {W : Subgroup G} (hWV : W ≤ V) (hW2 : W.relIndex V = 2) :
    centralizer (W : Set G) ≤ normalizer (L : Set G) := by
  have hVe : IsElementaryAbelian 2 V := hF.2.2.1
  have hV64 : Nat.card V = 64 := hF.2.2.2.1
  have hLV : L ≤ normalizer (V : Set G) := hF.2.2.2.2.2.2.1
  have hTV : T ≤ normalizer (V : Set G) := hF.2.2.2.2.2.2.2.1
  have hVz : V ⊓ centralizer (T : Set G) = zpowers z := hF.2.2.2.2.2.2.2.2.2.2.2.1
  have hz2 : orderOf z = 2 := hF.2.2.2.2.2.2.2.2.2.2.2.2
  have hTL : T ≤ normalizer (L : Set G) := hF.1
  obtain ⟨htrans, b, hbn, -, hbinv, -⟩ :=
    u3_six_action_profile_producer_F4 h1332 G T L V z hH hU3 hF
  have : Finite (Additive V) := inferInstanceAs (Finite V)
  have : FiniteDimensional (ZMod 2) (Additive V) := Module.Finite.of_finite
  have hzVT : z ∈ V ⊓ centralizer (T : Set G) := by rw [hVz]; exact mem_zpowers z
  have hzV : z ∈ V := hzVT.1
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hz2
    exact absurd hz2 (by norm_num)

  have hWcard : Nat.card W * 2 = 64 := by
    have h1 := card_mul_relIndex hWV
    rw [hW2, hV64] at h1
    exact h1
  have hW' : 2 * Nat.card (subOf V W) = Nat.card (Additive V) := by
    rw [card_subOf, inf_of_le_right hWV]
    change 2 * Nat.card W = Nat.card V
    omega
  obtain ⟨v, hv0, hvW⟩ := exists_eq_orth_of_card hbn hW'
  set z' : G := ((Additive.toMul v : V) : G) with hz'
  have hz'V : z' ∈ V := (Additive.toMul v).2
  have hz'1 : z' ≠ 1 := by
    intro h
    apply hv0
    apply Additive.toMul.injective
    exact Subtype.ext h
  obtain ⟨l, hl, hlz⟩ := htrans z hzV hz1 z' hz'V hz'1

  set W₅ := CFSG.conjugate W l⁻¹ with hW₅
  have hlV := hLV hl
  have hlV' : l⁻¹ ∈ normalizer (V : Set G) := inv_mem hlV
  have hmemW₅ : ∀ x : G, x ∈ W₅ ↔ ∃ hx : x ∈ V,
      b (Additive.ofMul ⟨z, hzV⟩) (Additive.ofMul ⟨x, hx⟩) = 0 := by
    intro x
    rw [hW₅, mem_conjugate_iff', inv_inv]
    constructor
    · intro hx
      have hxV : x ∈ V := by
        have h1 := (mem_normalizer_iff.1 hlV (l⁻¹ * x * l)).1 (hWV hx)
        rwa [show l * (l⁻¹ * x * l) * l⁻¹ = x by group] at h1
      refine ⟨hxV, ?_⟩
      have h1 := (hvW (Additive.ofMul ⟨l⁻¹ * x * l, hWV hx⟩)).1 (mem_subOf.2 hx)
      have hv : v = Additive.ofMul ⟨l⁻¹ * z * l, by rw [hlz]; exact hz'V⟩ := by
        apply Additive.toMul.injective
        apply Subtype.ext
        exact hlz.symm
      rw [hv] at h1
      have h2 := form_conj_eq hbinv hlV' hzV hxV
      simp only [inv_inv] at h2
      rw [← h2]
      exact h1
    · rintro ⟨hxV, hx⟩
      have hxV' : l⁻¹ * x * l ∈ V := by
        have h1 := (mem_normalizer_iff.1 hlV' x).1 hxV
        rwa [inv_inv] at h1
      have h1 : b v (Additive.ofMul ⟨l⁻¹ * x * l, hxV'⟩) = 0 := by
        have hv : v = Additive.ofMul ⟨l⁻¹ * z * l, by rw [hlz]; exact hz'V⟩ := by
          apply Additive.toMul.injective
          apply Subtype.ext
          exact hlz.symm
        rw [hv]
        have h2 := form_conj_eq hbinv hlV' hzV hxV
        simp only [inv_inv] at h2
        rw [h2]
        exact hx
      exact mem_subOf.1 ((hvW _).2 h1)
  have hW₅V : W₅ ≤ V := fun x hx => ((hmemW₅ x).1 hx).1
  have hW₅card : Nat.card W₅ = Nat.card W := card_conjugate W l⁻¹
  have hW₅2 : W₅.relIndex V = 2 := by
    have h1 := card_mul_relIndex hW₅V
    rw [hW₅card, hV64] at h1
    have hpos : 0 < Nat.card W := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans hWcard.symm)
  have hW₅1 : W₅ ≠ ⊥ := ne_bot_of_relIndex_eq_two hW₅V hW₅2 (by rw [hV64]; norm_num)

  have hTW₅ : T ≤ normalizer (W₅ : Set G) := by
    intro t ht
    have htV := hTV ht
    have htz : t * z * t⁻¹ = z := by
      rw [(mem_centralizer_iff.1 hzVT.2) t ht, mul_inv_cancel_right]
    rw [mem_normalizer_iff]
    intro x
    rw [hmemW₅, hmemW₅]
    constructor
    · rintro ⟨hxV, hx⟩
      refine ⟨(mem_normalizer_iff.1 htV x).1 hxV, ?_⟩
      have h2 := form_conj_eq hbinv htV hzV hxV
      have h3 : (⟨t * z * t⁻¹, (mem_normalizer_iff.1 htV z).1 hzV⟩ : V) = ⟨z, hzV⟩ :=
        Subtype.ext htz
      rw [h3] at h2
      rw [h2]
      exact hx
    · rintro ⟨hxV, hx⟩
      have hxV' : x ∈ V := by
        have h1 := (mem_normalizer_iff.1 htV x).2 hxV
        exact h1
      refine ⟨hxV', ?_⟩
      have h2 := form_conj_eq hbinv htV hzV hxV'
      have h3 : (⟨t * z * t⁻¹, (mem_normalizer_iff.1 htV z).1 hzV⟩ : V) = ⟨z, hzV⟩ :=
        Subtype.ext htz
      rw [h3] at h2
      rw [← h2]
      exact hx

  have hres := (u3_hyperplane_centralizer_eq_F4 h1332 hH hU3 hF hW₅V hW₅2).2
  have hCW₅ : centralizer (W₅ : Set G) ≤ normalizer (L : Set G) :=
    E6.e6_13 h311 (u3_E61_F4 h1332 hH hF) hW₅V hW₅1 hres hTW₅

  intro c hc
  have hlc : l * c * l⁻¹ ∈ centralizer (W₅ : Set G) := by
    rw [mem_centralizer_iff]
    intro x hx
    have hx' : l⁻¹ * x * l ∈ W := by
      have := SetLike.mem_coe.1 hx
      rw [hW₅, mem_conjugate_iff', inv_inv] at this
      exact this
    have h1 := (mem_centralizer_iff.1 hc) _ hx'
    calc x * (l * c * l⁻¹) = l * ((l⁻¹ * x * l) * c) * l⁻¹ := by group
      _ = l * (c * (l⁻¹ * x * l)) * l⁻¹ := by rw [h1]
      _ = l * c * l⁻¹ * x := by group
  have hlM : l ∈ normalizer (L : Set G) := le_normalizer hl
  have h1 := hCW₅ hlc
  have h2 : l⁻¹ * (l * c * l⁻¹) * l ∈ normalizer (L : Set G) :=
    (normalizer (L : Set G)).mul_mem
      ((normalizer (L : Set G)).mul_mem ((normalizer (L : Set G)).inv_mem hlM) h1) hlM
  rwa [show l⁻¹ * (l * c * l⁻¹) * l = c by group] at h2

end CFSG.Quasithin.H13.U3
