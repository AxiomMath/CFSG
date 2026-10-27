module

public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2A7C_Defs
import CFSG.Quasithin.Background.B2Thompson
import CFSG.Quasithin.Background.Equivariance
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2A7_Struct

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup Equiv
  CFSG.RankThree.PartTwo.KFacts.KP2 CFSG.Quasithin
open scoped Pointwise

theorem a7o_exists_apply_zero (y : Fin 7) :
    ∃ g ∈ (vOne ⊔ vTwo : Subgroup (Perm (Fin 7))), g 0 = y := by
  have h1 : ∀ m : Fin 4, vOneF m ∈ (vOne ⊔ vTwo : Subgroup (Perm (Fin 7))) :=
    fun m => mem_sup_left ⟨m, rfl⟩
  have h2 : ∀ m : Fin 4, vTwoF m ∈ (vOne ⊔ vTwo : Subgroup (Perm (Fin 7))) :=
    fun m => mem_sup_right ⟨m, rfl⟩
  fin_cases y
  · exact ⟨1, one_mem _, rfl⟩
  · exact ⟨vTwoF 1, h2 1, by decide +kernel⟩
  · exact ⟨vTwoF 2, h2 2, by decide +kernel⟩
  · exact ⟨vOneF 3 * vTwoF 3, mul_mem (h1 3) (h2 3), by decide +kernel⟩
  · exact ⟨vOneF 2 * vTwoF 3, mul_mem (h1 2) (h2 3), by decide +kernel⟩
  · exact ⟨vOneF 1 * vTwoF 3, mul_mem (h1 1) (h2 3), by decide +kernel⟩
  · exact ⟨vTwoF 3, h2 3, by decide +kernel⟩

theorem a7o_isPretransitive :
    MulAction.IsPretransitive ↥(vOne ⊔ vTwo : Subgroup (Perm (Fin 7))) (Fin 7) := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨g, hg, hgx⟩ := a7o_exists_apply_zero x
  obtain ⟨h, hh, hhy⟩ := a7o_exists_apply_zero y
  refine ⟨⟨h * g⁻¹, mul_mem hh (inv_mem hg)⟩, ?_⟩
  change (h * g⁻¹) x = y
  rw [Perm.mul_apply, ← hgx]
  simp only [Perm.coe_inv, symm_apply_apply, hhy]

theorem a7o_isThreeCycle : ((vOneF 1 * vTwoF 1) ^ 2).IsThreeCycle := by
  have h3 : ((vOneF 1 * vTwoF 1) ^ 2) ^ 3 = 1 := by decide +kernel
  have h1 : (vOneF 1 * vTwoF 1) ^ 2 ≠ 1 := by decide +kernel
  have hs : ((vOneF 1 * vTwoF 1) ^ 2).support.card = 3 := by decide +kernel
  change Perm.cycleType _ = {3}
  rw [cycleType_of_pow_three h3 h1, hs]
  rfl

theorem a7o_alternatingGroup_le_sup : alternatingGroup (Fin 7) ≤ vOne ⊔ vTwo := by
  have := a7o_isPretransitive
  have h7 : (Nat.card (Fin 7)).Prime := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num
  have h1 : vOneF 1 ∈ vOne := ⟨1, rfl⟩
  have h2 : vTwoF 1 ∈ vTwo := ⟨1, rfl⟩
  exact Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem
    (MulAction.IsPreprimitive.of_prime_card h7) a7o_isThreeCycle
    (pow_mem (mul_mem (mem_sup_left h1) (mem_sup_right h2)) 2)

theorem a7o_eq_two_or_four {n : ℕ} (h : n ∣ 4) (h1 : n ≠ 1) : n = 2 ∨ n = 4 := by
  have h4 : n ≤ 4 := Nat.le_of_dvd (by norm_num) h
  interval_cases n <;> omega

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem a7o_map_eq_one_iff {D H V : Subgroup G} {ι : ↥H →* Perm (Fin 7)}
    (hF : A7Frame D H V ι) (h : ↥H) : ι h = 1 ↔ (h : G) ∈ a7K H := by
  rw [← MonoidHom.mem_ker, hF.ker_eq, a7K]
  exact (mem_map_iff_mem H.subtype_injective).symm

theorem a7o_le_pCoreOf {D H V : Subgroup G} {ι : ↥H →* Perm (Fin 7)} (hF : A7Frame D H V ι)
    {T : Subgroup G} (hTK : T ≤ a7K H) (hT : IsPGroup 2 T) : T ≤ pCoreOf 2 H := by
  have hTN : T ≤ normalizer (pCoreOf 2 H : Set G) := hTK.trans ((a7K_le H).trans hF.H_norm.ge)
  have h := hF.sylow.eq_of_le le_sup_right (sup_le hTK hF.sylow.le)
    (hT.to_sup_of_normal_right' hF.sylow.isPGroup hTN)
  exact le_sup_left.trans h.le

theorem a7o_card_eq {D H V : Subgroup G} {ι : ↥H →* Perm (Fin 7)} (hF : A7Frame D H V ι)
    {X : Subgroup G} (hXH : X ≤ H) (hX : IsPGroup 2 X) :
    Nat.card X =
      Nat.card ((X.subgroupOf H).map ι) * Nat.card (X ⊓ pCoreOf 2 H : Subgroup G) := by
  have hXK : X ⊓ a7K H = X ⊓ pCoreOf 2 H :=
    le_antisymm (le_inf inf_le_left (a7o_le_pCoreOf hF inf_le_right (hX.to_le inf_le_left)))
      (inf_le_inf_left X hF.sylow.le)
  have hker : X.subgroupOf H ⊓ ι.ker = (X ⊓ pCoreOf 2 H).subgroupOf H := by
    ext h
    rw [mem_inf, mem_subgroupOf, MonoidHom.mem_ker, a7o_map_eq_one_iff hF, mem_subgroupOf,
      ← hXK, mem_inf]
  rw [← Nat.card_congr (subgroupOfEquivOfLe hXH).toEquiv,
    card_eq_card_map_mul_card_inf_ker ι (X.subgroupOf H), hker,
    Nat.card_congr (subgroupOfEquivOfLe (inf_le_left.trans hXH)).toEquiv]

omit [Finite G] in
theorem a7o_W_le (H : Subgroup G) :
    a7W H ≤ pCoreOf 2 H ⊓ centralizer (pCoreOf 2 H : Set G) :=
  (closure_le _).mpr fun _ hx => hx.1

omit [Finite G] in
theorem a7o_isElemAbelian {H R : Subgroup G} (hR : R ≤ a7W H) : IsElemAbelian 2 R := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => sq_eq_one_of_mem_omegaOneCenter _ (hR hx)⟩
  exact mem_centralizer_iff.mp (a7o_W_le H (hR b.2)).2 _ (a7o_W_le H (hR a.2)).1

omit [Finite G] in
theorem a7o_le_centralizer_W (H : Subgroup G) : pCoreOf 2 H ≤ centralizer (a7W H : Set G) :=
  le_centralizer_iff.mp ((a7o_W_le H).trans inf_le_right)

theorem a7o_card_le {H S R B : Subgroup G} {k : ℕ} (hRW : R ≤ a7W H) (hRS : R ≤ S)
    (hB : IsMaxElemAbelian S B)
    (hBc : Nat.card B ≤ k * Nat.card (B ⊓ pCoreOf 2 H : Subgroup G)) :
    Nat.card R ≤ k * Nat.card (R ⊓ centralizer (B : Set G) : Subgroup G) := by
  have key := card_le_relIndex_mul_card (a7o_isElemAbelian hRW) hRS hB
  have h1 := relIndex_mul_card (B ⊓ centralizer (R : Set G)) B
  rw [inf_of_le_left inf_le_left] at h1
  have hSR : pCoreOf 2 H ≤ centralizer (R : Set G) :=
    (a7o_le_centralizer_W H).trans (centralizer_le hRW)
  have h2 : Nat.card (B ⊓ pCoreOf 2 H : Subgroup G) ≤
      Nat.card (B ⊓ centralizer (R : Set G) : Subgroup G) :=
    card_le_of_le (inf_le_inf_left B hSR)
  have hidx : (B ⊓ centralizer (R : Set G)).relIndex B ≤ k := by
    refine Nat.le_of_mul_le_mul_right ?_ (Nat.card_pos (α := ↥(B ⊓ centralizer (R : Set G))))
    rw [h1]
    exact hBc.trans (Nat.mul_le_mul_left k h2)
  exact key.trans (Nat.mul_le_mul_right _ hidx)

theorem a7o_isMaxElemAbelian_iff {S V : Subgroup G} (hSV : S ≤ V)
    (h : ∀ A, IsMaxElemAbelian V A → A ≤ S) (B : Subgroup G) :
    IsMaxElemAbelian V B ↔ IsMaxElemAbelian S B := by
  constructor
  · intro hB
    exact ⟨h B hB, hB.2.1, fun C hC hCe => hB.2.2 C (hC.trans hSV) hCe⟩
  · intro hB
    obtain ⟨B₀, hB₀⟩ := exists_isMaxElemAbelian V
    exact ⟨hB.1.trans hSV, hB.2.1, fun C hC hCe =>
      (hB₀.2.2 C hC hCe).trans (hB.2.2 B₀ (h B₀ hB₀) hB₀.2.1)⟩

theorem a7o_thompsonJ_ne_bot {V : Subgroup G} (h2 : 2 ∣ Nat.card V) : thompsonJ V ≠ ⊥ := by
  obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' 2 h2
  obtain ⟨A, hA⟩ := exists_isMaxElemAbelian V
  have hvG : orderOf (v : G) = 2 := (orderOf_coe v).trans hv
  have hcard : Nat.card (zpowers (v : G)) = 2 := by rw [Nat.card_zpowers, hvG]
  have hZ : IsElemAbelian 2 (zpowers (v : G)) := by
    refine ⟨inferInstance, fun x hx => ?_⟩
    have := pow_card_eq_one' (G := zpowers (v : G)) (x := ⟨x, hx⟩)
    rw [hcard] at this
    exact congrArg Subtype.val this
  have hle := hA.2.2 _ (zpowers_le.mpr v.2) hZ
  intro hJ
  have hA1 : A = ⊥ := le_bot_iff.mp (hJ ▸ le_iSup₂_of_le (f := fun (B : Subgroup G)
    (_ : IsMaxElemAbelian V B) => B) A hA le_rfl)
  rw [hA1, card_bot, hcard] at hle
  omega

theorem a7o_exists_not_le {D H V : Subgroup G} {ι : ↥H →* Perm (Fin 7)}
    (hF : A7Frame D H V ι) : ∃ A, IsMaxElemAbelian V A ∧ ¬ A ≤ pCoreOf 2 H := by
  by_contra hcon
  push Not at hcon
  have hJ : thompsonJ V = thompsonJ (pCoreOf 2 H) := by
    simp only [thompsonJ, a7o_isMaxElemAbelian_iff hF.S_le hcon]
  have hY0 : thompsonJ V ≠ ⊥ := by
    refine a7o_thompsonJ_ne_bot ?_
    rw [hF.card_V]
    exact dvd_mul_of_dvd_left (by norm_num) _
  have hHY : H ≤ normalizer (thompsonJ V : Set G) := by
    rw [hJ]
    exact hF.H_norm.ge.trans (normalizer_le_normalizer_thompsonJ _)
  apply hF.noCover (thompsonJ V) (iSup₂_le fun B hB => hB.1) hY0
    (normalizer_le_normalizer_thompsonJ V)
  rw [inf_eq_left.mpr hHY, subgroupOf_self, ← MonoidHom.range_eq_map]
  exact hF.A7_le

theorem A7Frame.exists_offender {D H V : Subgroup G} {ι : ↥H →* Perm (Fin 7)}
    (hF : A7Frame D H V ι) {R : Subgroup G} (hRW : R ≤ a7W H)
    (hrank : ∀ a ∈ V, a ^ 2 = 1 → a ∉ pCoreOf 2 H →
      4 * Nat.card (R ⊓ centralizer ({a} : Set G) : Subgroup G) ≤ Nat.card R) :
    ∃ A : Subgroup G, CFSG.Quasithin.IsMaxElemAbelian V A ∧
      (A.subgroupOf H).map ι = vOne := by
  obtain ⟨A, hA, hAS⟩ := a7o_exists_not_le hF
  have hcard := a7o_card_eq hF (hA.1.trans hF.V_le) (hF.V_two.to_le hA.1)
  have hle : (A.subgroupOf H).map ι ≤ vOne :=
    (map_mono (subgroupOf_mono H hA.1)).trans hF.V_img.le
  have hdvd : Nat.card ((A.subgroupOf H).map ι) ∣ 4 := card_vOne ▸ card_dvd_of_le hle
  have hne : Nat.card ((A.subgroupOf H).map ι) ≠ 1 := by
    intro h1
    rw [h1, one_mul] at hcard
    exact hAS (inf_eq_left.mp (eq_of_le_of_card_ge inf_le_left hcard.le))
  rcases a7o_eq_two_or_four hdvd hne with h2 | h4
  · exfalso
    obtain ⟨a, haA, haS⟩ := IsConcreteLE.not_le_iff_exists.mp hAS
    have hRV : R ≤ V := hRW.trans (((a7o_W_le H).trans inf_le_left).trans hF.S_le)
    have hb := a7o_card_le (k := 2) hRW hRV hA (by rw [hcard, h2])
    have hC : Nat.card (R ⊓ centralizer (A : Set G) : Subgroup G) ≤
        Nat.card (R ⊓ centralizer ({a} : Set G) : Subgroup G) :=
      card_le_of_le (inf_le_inf_left R (centralizer_le (Set.singleton_subset_iff.mpr haA)))
    have hr := hrank a (hA.1 haA) (hA.2.1.2 a haA) haS
    have hpos : 0 < Nat.card (R ⊓ centralizer ({a} : Set G) : Subgroup G) := Nat.card_pos
    omega
  · exact ⟨A, hA, eq_of_le_of_card_ge hle (by rw [card_vOne, h4])⟩

omit [Finite G] in
theorem a7o_le_of_map {D H V : Subgroup G} {ι : ↥H →* Perm (Fin 7)} (hF : A7Frame D H V ι)
    {J L : Subgroup G} (hJH : J ≤ H) (hJι : (J.subgroupOf H).map ι = alternatingGroup (Fin 7))
    (hJK : J ⊓ a7K H ≤ pCoreOf 2 H) (hSL : pCoreOf 2 H ≤ L) (hLJ : L ≤ J ⊔ pCoreOf 2 H)
    (hLι : alternatingGroup (Fin 7) ≤ (L.subgroupOf H).map ι) : J ≤ L := by
  have hJS : ((J ⊔ pCoreOf 2 H : Subgroup G) : Set G) = (J : Set G) * (pCoreOf 2 H : Set G) :=
    coe_mul_of_left_le_normalizer_right J _ (hJH.trans hF.H_norm.ge)
  intro j hj
  have hjH := hJH hj
  have hjA : ι ⟨j, hjH⟩ ∈ (L.subgroupOf H).map ι :=
    hLι (hJι ▸ mem_map_of_mem ι (show (⟨j, hjH⟩ : ↥H) ∈ J.subgroupOf H from hj))
  obtain ⟨l, hlL, hl⟩ := mem_map.mp hjA
  have hK : j * (l : G)⁻¹ ∈ a7K H := by
    have h1 : ι (⟨j, hjH⟩ * l⁻¹) = 1 := by rw [map_mul, map_inv, hl, mul_inv_cancel]
    exact (a7o_map_eq_one_iff hF _).mp h1
  have hJS' : j * (l : G)⁻¹ ∈ ((J ⊔ pCoreOf 2 H : Subgroup G) : Set G) :=
    mul_mem (mem_sup_left hj) (inv_mem (hLJ (mem_subgroupOf.mp hlL)))
  rw [hJS] at hJS'
  obtain ⟨j', hj', s, hs, hjs⟩ := hJS'
  have hj'K : j' ∈ a7K H := by
    have : j' = j * (l : G)⁻¹ * s⁻¹ := by rw [← hjs]; group
    rw [this]
    exact mul_mem hK (inv_mem (hF.sylow.le hs))
  have hS : j * (l : G)⁻¹ ∈ pCoreOf 2 H := hjs ▸ mul_mem (hJK ⟨hj', hj'K⟩) hs
  simpa using mul_mem (hSL hS) (mem_subgroupOf.mp hlL)

omit [Finite G] in
theorem a7o_alternatingGroup_le_map {H : Subgroup G} {ι : ↥H →* Perm (Fin 7)}
    {A L : Subgroup G} (hAι : (A.subgroupOf H).map ι = vOne) {y : ↥H} (hy : ι y = rFour)
    (hAL : A ≤ L) (hA'L : A.map (MulAut.conj (y : G)).toMonoidHom ≤ L) :
    alternatingGroup (Fin 7) ≤ (L.subgroupOf H).map ι := by
  refine a7o_alternatingGroup_le_sup.trans (sup_le ?_ ?_)
  · rw [← hAι]
    exact map_mono (subgroupOf_mono H hAL)
  · intro τ hτ
    rw [← map_conj_rFour_vOne, ← hAι] at hτ
    obtain ⟨σ, hσ, rfl⟩ := mem_map.mp hτ
    obtain ⟨a, ha, rfl⟩ := mem_map.mp hσ
    refine ⟨y * a * y⁻¹, hA'L ⟨(a : G), ha, rfl⟩, ?_⟩
    simp [hy, MulAut.conj_apply]

omit [Finite G] in
theorem a7o_inf_centralizer_le {H J A B : Subgroup G} (hJ : J ≤ pCoreOf 2 H ⊔ A ⊔ B) :
    centralizer (A : Set G) ⊓ centralizer (B : Set G) ⊓ a7W H ≤
      a7W H ⊓ centralizer (J : Set G) := by
  rintro w ⟨⟨hwA, hwB⟩, hwW⟩
  refine ⟨hwW, ?_⟩
  have hz : ∀ X : Subgroup G, w ∈ centralizer (X : Set G) →
      X ≤ centralizer (zpowers w : Set G) :=
    fun X hX => le_centralizer_iff.mp (zpowers_le.mpr hX)
  exact zpowers_le.mp (le_centralizer_iff.mp
    (hJ.trans (sup_le (sup_le (hz _ (a7o_W_le H hwW).2) (hz _ hwA)) (hz _ hwB))))

theorem a7o_card_le_sixteen {W A B : Subgroup G}
    (hA : Nat.card W ≤ 4 * Nat.card (W ⊓ centralizer (A : Set G) : Subgroup G))
    (hB : Nat.card W ≤ 4 * Nat.card (W ⊓ centralizer (B : Set G) : Subgroup G)) :
    Nat.card W ≤
      16 * Nat.card (centralizer (A : Set G) ⊓ centralizer (B : Set G) ⊓ W : Subgroup G) := by
  have hidx : ∀ X : Subgroup G, Nat.card W ≤ 4 * Nat.card (W ⊓ X : Subgroup G) →
      X.relIndex W ≤ 4 := by
    intro X hX
    have h1 := relIndex_mul_card X W
    rw [inf_comm] at h1
    exact Nat.le_of_mul_le_mul_right (h1.le.trans hX) Nat.card_pos
  have h16 : (centralizer (A : Set G) ⊓ centralizer (B : Set G)).relIndex W ≤ 16 :=
    relIndex_inf_le.trans ((Nat.mul_le_mul (hidx _ hA) (hidx _ hB)).trans le_rfl)
  rw [← relIndex_mul_card (centralizer (A : Set G) ⊓ centralizer (B : Set G)) W]
  exact Nat.mul_le_mul_right _ h16

theorem A7Frame.card_a7W_le {D H V : Subgroup G} {ι : ↥H →* Perm (Fin 7)}
    (hF : A7Frame D H V ι) {J A : Subgroup G} (hJH : J ≤ H)
    (hJι : (J.subgroupOf H).map ι = alternatingGroup (Fin 7)) (hJK : J ⊓ a7K H ≤ pCoreOf 2 H)
    (hVJ : V ≤ J ⊔ pCoreOf 2 H) (hA : CFSG.Quasithin.IsMaxElemAbelian V A)
    (hAι : (A.subgroupOf H).map ι = vOne) :
    Nat.card (a7W H) ≤ 16 * Nat.card (a7W H ⊓ centralizer (J : Set G) : Subgroup G) := by
  have hWS : a7W H ≤ pCoreOf 2 H := (a7o_W_le H).trans inf_le_left
  have hcardA : Nat.card A = 4 * Nat.card (A ⊓ pCoreOf 2 H : Subgroup G) := by
    rw [a7o_card_eq hF (hA.1.trans hF.V_le) (hF.V_two.to_le hA.1), hAι, card_vOne]
  obtain ⟨y, hyJ, hy⟩ := mem_map.mp (hJι.ge (Perm.mem_alternatingGroup.mpr rFour_spec.1))
  have hxS : (pCoreOf 2 H).map (MulAut.conj (y : G)).toMonoidHom = pCoreOf 2 H :=
    map_conj_eq_of_mem_normalizer (hF.H_norm.ge y.2)
  have hxJ : (J ⊔ pCoreOf 2 H).map (MulAut.conj (y : G)).toMonoidHom = J ⊔ pCoreOf 2 H := by
    rw [Subgroup.map_sup, map_conj_eq_of_mem_normalizer (le_normalizer (mem_subgroupOf.mp hyJ)),
      hxS]
  have hcardA' : Nat.card (A.map (MulAut.conj (y : G)).toMonoidHom) =
      4 * Nat.card (A.map (MulAut.conj (y : G)).toMonoidHom ⊓ pCoreOf 2 H : Subgroup G) := by
    rw [← hxS, ← map_inf _ _ _ (MulAut.conj (y : G)).injective, card_map_mulEquiv,
      card_map_mulEquiv, hcardA]
  have h1 := a7o_card_le (H := H) le_rfl (hWS.trans hF.S_le) hA hcardA.le
  have h2 := a7o_card_le (H := H) le_rfl (hWS.trans (hxS.ge.trans (map_mono hF.S_le)))
    ((isMaxElemAbelian_map_mulEquiv _).mpr hA) hcardA'.le
  have hL : J ≤ pCoreOf 2 H ⊔ A ⊔ A.map (MulAut.conj (y : G)).toMonoidHom :=
    a7o_le_of_map hF hJH hJι hJK (le_sup_left.trans le_sup_left)
      (sup_le (sup_le le_sup_right (hA.1.trans hVJ))
        ((map_mono (hA.1.trans hVJ)).trans hxJ.le))
      (a7o_alternatingGroup_le_map hAι hy (le_sup_right.trans le_sup_left) le_sup_right)
  exact (a7o_card_le_sixteen h1 h2).trans
    (Nat.mul_le_mul_left 16 (card_le_of_le (a7o_inf_centralizer_le hL)))

end CFSG.LocalAnalysis.RankThreeTheoremC
