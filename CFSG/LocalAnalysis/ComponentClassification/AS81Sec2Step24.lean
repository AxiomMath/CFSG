module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step21

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FieldFourCover LinearFlag
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Sec2

omit [Finite G] in
theorem sq_mem_and_commutator_mem_of_sup {Y W K : Subgroup G}
    (hKc : Y ⊔ W ≤ centralizer (K : Set G)) (hYW : Y ≤ normalizer (W : Set G))
    (hYc : ∀ y ∈ Y, ∀ y' ∈ Y, y * y' = y' * y) (hY2 : ∀ y ∈ Y, y * y = 1)
    (hWc : ∀ w ∈ W, ∀ w' ∈ W, w * w' = w' * w) (hW2 : ∀ w ∈ W, w * w = 1)
    (hc : ∀ y ∈ Y, ∀ w ∈ W, y⁻¹ * w⁻¹ * y * w ∈ K) {a b : G} (ha : a ∈ Y ⊔ W)
    (hb : b ∈ Y ⊔ W) : a * a ∈ K ∧ a * b * a⁻¹ * b⁻¹ ∈ K := by
  have hN : (K.subgroupOf (Y ⊔ W)).Normal := ⟨fun n hn x => by
    rw [mem_subgroupOf] at hn ⊢
    have h := mem_centralizer_iff.mp (hKc x.2) n hn
    have h' : (x : G) * n * (x : G)⁻¹ = n := by rw [← h, mul_inv_cancel_right]
    simpa [h'] using hn⟩
  have hπ : ∀ x : ↥(Y ⊔ W), QuotientGroup.mk' (K.subgroupOf (Y ⊔ W)) x = 1 ↔ (x : G) ∈ K :=
    fun x => by rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf]
  have hπeq : ∀ x y : ↥(Y ⊔ W), QuotientGroup.mk' (K.subgroupOf (Y ⊔ W)) x =
      QuotientGroup.mk' (K.subgroupOf (Y ⊔ W)) y ↔ ((x⁻¹ * y : ↥(Y ⊔ W)) : G) ∈ K := fun x y => by
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, mem_subgroupOf]
  have hdec : ∀ a ∈ Y ⊔ W, ∃ y : ↥(Y ⊔ W), ∃ w : ↥(Y ⊔ W), (y : G) ∈ Y ∧ (w : G) ∈ W ∧
      a = y * w := by
    intro a ha
    have ha' : a ∈ ((Y ⊔ W : Subgroup G) : Set G) := ha
    rw [coe_mul_of_left_le_normalizer_right Y W hYW] at ha'
    obtain ⟨y, hy, w, hw, rfl⟩ := ha'
    exact ⟨⟨y, mem_sup_left hy⟩, ⟨w, mem_sup_right hw⟩, hy, hw, rfl⟩
  set π := QuotientGroup.mk' (K.subgroupOf (Y ⊔ W))
  have hcYW : ∀ y w : ↥(Y ⊔ W), (y : G) ∈ Y → (w : G) ∈ W → Commute (π y) (π w) := by
    intro y w hy hw
    show π y * π w = π w * π y
    rw [← map_mul, ← map_mul, hπeq]
    have := K.inv_mem (hc y hy w hw)
    simpa [mul_assoc] using this
  have hcYY : ∀ y y' : ↥(Y ⊔ W), (y : G) ∈ Y → (y' : G) ∈ Y → Commute (π y) (π y') := by
    intro y y' hy hy'
    show π y * π y' = π y' * π y
    rw [← map_mul, ← map_mul, show y * y' = y' * y from Subtype.ext (hYc y hy y' hy')]
  have hcWW : ∀ w w' : ↥(Y ⊔ W), (w : G) ∈ W → (w' : G) ∈ W → Commute (π w) (π w') := by
    intro w w' hw hw'
    show π w * π w' = π w' * π w
    rw [← map_mul, ← map_mul, show w * w' = w' * w from Subtype.ext (hWc w hw w' hw')]
  have hsq : ∀ x : ↥(Y ⊔ W), (x : G) * x = 1 → π x * π x = 1 := by
    intro x hx
    rw [← map_mul, hπ]
    show (x : G) * x ∈ K
    rw [hx]
    exact K.one_mem
  obtain ⟨y₁, w₁, hy₁, hw₁, rfl⟩ := hdec a ha
  obtain ⟨y₂, w₂, hy₂, hw₂, rfl⟩ := hdec b hb
  obtain ⟨h1, h2⟩ := mul_mul_eq_one_and_commutator_eq_one (hsq y₁ (hY2 _ hy₁))
    (hsq w₁ (hW2 _ hw₁)) (hcYW y₁ w₁ hy₁ hw₁) (hcYW y₁ w₂ hy₁ hw₂) (hcYW y₂ w₁ hy₂ hw₁)
    (hcYY y₁ y₂ hy₁ hy₂) (hcWW w₁ w₂ hw₁ hw₂)
  refine ⟨(hπ (y₁ * w₁ * (y₁ * w₁))).mp ?_,
    (hπ (y₁ * w₁ * (y₂ * w₂) * (y₁ * w₁)⁻¹ * (y₂ * w₂)⁻¹)).mp ?_⟩
  · simp only [map_mul]
    exact h1
  · simp only [map_mul, map_inv]
    exact h2

theorem eq_or_eq_of_card_sixteen {A T H H₁ H₂ : Subgroup G} (hq : CFSG.Open.IsQuasisimple ↥A)
    (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A))) (hTsyl : IsSylowOf 2 T A)
    (hH : H ≤ T) (hHe : IsElemAbelian 2 H) (hH16 : Nat.card H = 16)
    (hH₁ : H₁ ≤ T) (hH₁e : IsElemAbelian 2 H₁) (hH₁16 : Nat.card H₁ = 16)
    (hH₂ : H₂ ≤ T) (hH₂e : IsElemAbelian 2 H₂) (hH₂16 : Nat.card H₂ = 16) (hne : H₁ ≠ H₂) :
    H = H₁ ∨ H = H₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c⟩ := nonempty_l34Cover_of_odd hq hL hodd
  have hO := oddCore_le_center hq.1 hq.2
  obtain ⟨T₀, hT₀⟩ := hTsyl
  have hTA : T ≤ A := hT₀ ▸ map_subtype_le _
  obtain ⟨φ, -, hφk, hφT⟩ := c.exists_std hO T₀
  have hkerodd : Odd (Nat.card φ.ker) := by rw [hφk]; exact hodd
  have hTsub : T.subgroupOf A = T₀ := by
    rw [← hT₀]
    exact comap_map_eq_self_of_injective A.subtype_injective _
  have hT₀2 : IsPGroup 2 (T₀ : Subgroup ↥A) := T₀.2
  have hrad : ∀ X : Subgroup G, X ≤ T → IsElemAbelian 2 X → Nat.card X = 16 →
      ∃ i : Fin 2, (X.subgroupOf A).map φ = projRad c.k i := by
    intro X hXT hX hX16
    have hX₀T : X.subgroupOf A ≤ T₀ := fun x hx => hTsub ▸ (hXT (mem_subgroupOf.mp hx))
    have hX₀ : IsPGroup 2 (X.subgroupOf A) := hT₀2.to_le hX₀T
    have h2 : ∀ x ∈ (X.subgroupOf A).map φ, x ^ 2 = 1 := by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, show x ^ 2 = 1 from Subtype.ext (by simpa using hX.2 _ (mem_subgroupOf.mp hx)),
        map_one]
    have h16 : Nat.card ((X.subgroupOf A).map φ) = 16 := by
      rw [card_map_of_isPGroup φ hkerodd hX₀, ← hX16]
      exact Nat.card_congr (subgroupOfEquivOfLe (hXT.trans hTA)).toEquiv
    have hU : (X.subgroupOf A).map φ ≤ projUnip c.k := hφT ▸ map_mono hX₀T
    rcases eq_projRad_of_le_projUnip c.card_k hU h2 h16 with h0 | h1
    · exact ⟨0, h0⟩
    · exact ⟨1, h1⟩
  have key : ∀ X Y : Subgroup G, X ≤ T → Y ≤ T →
      (X.subgroupOf A).map φ ≤ (Y.subgroupOf A).map φ → X ≤ Y := by
    intro X Y hXT hYT h x hx
    have hxA : x ∈ A := hTA (hXT hx)
    obtain ⟨y, hy, hyx⟩ := h ⟨⟨x, hxA⟩, hx, rfl⟩
    have hyT₀ : y ∈ (T₀ : Subgroup ↥A) := hTsub ▸ (hYT (mem_subgroupOf.mp hy))
    have hxT₀ : (⟨x, hxA⟩ : ↥A) ∈ (T₀ : Subgroup ↥A) := hTsub ▸ (hXT hx)
    rw [eq_of_map_eq_of_isPGroup φ hkerodd hT₀2 hyT₀ hxT₀ hyx] at hy
    exact hy
  have hinj : ∀ X Y : Subgroup G, X ≤ T → Y ≤ T →
      (X.subgroupOf A).map φ = (Y.subgroupOf A).map φ → X = Y := fun X Y hXT hYT h =>
    le_antisymm (key X Y hXT hYT h.le) (key Y X hYT hXT h.ge)
  obtain ⟨i, hi⟩ := hrad H hH hHe hH16
  obtain ⟨i₁, hi₁⟩ := hrad H₁ hH₁ hH₁e hH₁16
  obtain ⟨i₂, hi₂⟩ := hrad H₂ hH₂ hH₂e hH₂16
  have hi₁₂ : i₁ ≠ i₂ := fun h => hne (hinj H₁ H₂ hH₁ hH₂ (by rw [hi₁, hi₂, h]))
  have hfin : ∀ a b c : Fin 2, b ≠ c → a = b ∨ a = c := by decide
  rcases hfin i i₁ i₂ hi₁₂ with rfl | rfl
  · exact Or.inl (hinj H H₁ hH hH₁ (by rw [hi, hi₁]))
  · exact Or.inr (hinj H H₂ hH hH₂ (by rw [hi, hi₂]))

end Sec2

section Frame

variable {A R : Subgroup G} {g : G} {E F : Subgroup G}

theorem Frame.symm (hF : Frame G A A R g E F) : Frame G A A R g F E where
  base := hF.base
  le := hF.le
  quasisimple := hF.quasisimple
  typeA₁ := hF.typeA₁
  sylowR := hF.sylowR
  elemR := hF.elemR
  cardR := hF.cardR
  not_mem := hF.not_mem
  comm := hF.comm
  conj_le := hF.conj_le
  E_le := hF.F_le
  F_le := hF.E_le
  R_le_E := hF.R_le_F
  R_le_F := hF.R_le_E
  elemE := hF.elemF
  elemF := hF.elemE
  cardE := hF.cardF
  cardF := hF.cardE
  ne := hF.ne.symm
  inf_eq := by rw [inf_comm]; exact hF.inf_eq
  inf_eq_center := by rw [inf_comm, sup_comm]; exact hF.inf_eq_center
  sylow := by rw [sup_comm]; exact hF.sylow

theorem Frame.commutator_mem_sec2Z (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A))
    (hodd : Odd (Nat.card (center ↥A))) {e f : G} (he : e ∈ E) (hf : f ∈ F) :
    e * f * e⁻¹ * f⁻¹ ∈ sec2Z A E F := by
  have hRA : R ≤ centralizer (A : Set G) := hF.sylowR.le
  have hFE := hF.F_le_normalizer hL hodd
  have hEF := hF.symm.F_le_normalizer hL hodd
  rw [hF.sec2Z_eq]
  refine ⟨⟨?_, F.mul_mem ((mem_normalizer_iff.mp (hEF he) f).mp hf) (F.inv_mem hf)⟩, ?_⟩
  · have := E.mul_mem he ((mem_normalizer_iff.mp (hFE hf) e⁻¹).mp (E.inv_mem he))
    simpa [mul_assoc] using this
  · obtain ⟨a, ha, r, hr, rfl⟩ := exists_eq_mul_of_le_sup hRA hF.R_le_E hF.E_le he
    obtain ⟨b, hb, r', hr', rfl⟩ := exists_eq_mul_of_le_sup hRA hF.R_le_F hF.F_le hf
    have h1 : r * b = b * r := (mem_centralizer_iff.mp (hRA hr) b hb.2).symm
    have h2 : r' * a⁻¹ = a⁻¹ * r' :=
      (mem_centralizer_iff.mp (hRA hr') a⁻¹ (A.inv_mem ha.2)).symm
    have h3 : r * r' = r' * r :=
      congrArg Subtype.val (hF.elemR.1.is_comm.comm ⟨r, hr⟩ ⟨r', hr'⟩)
    have heq : a * r * (b * r') * (a * r)⁻¹ * (b * r')⁻¹ = a * b * a⁻¹ * b⁻¹ := by
      calc a * r * (b * r') * (a * r)⁻¹ * (b * r')⁻¹
          = a * (r * b) * r' * r⁻¹ * a⁻¹ * r'⁻¹ * b⁻¹ := by group
        _ = a * (b * r) * r' * r⁻¹ * a⁻¹ * r'⁻¹ * b⁻¹ := by rw [h1]
        _ = a * b * (r * r') * r⁻¹ * a⁻¹ * r'⁻¹ * b⁻¹ := by group
        _ = a * b * (r' * r) * r⁻¹ * a⁻¹ * r'⁻¹ * b⁻¹ := by rw [h3]
        _ = a * b * (r' * a⁻¹) * r'⁻¹ * b⁻¹ := by group
        _ = a * b * (a⁻¹ * r') * r'⁻¹ * b⁻¹ := by rw [h2]
        _ = a * b * a⁻¹ * b⁻¹ := by group
    rw [heq]
    exact A.mul_mem (A.mul_mem (A.mul_mem ha.2 hb.2) (A.inv_mem ha.2)) (A.inv_mem hb.2)

theorem exists_mem_point_le_inf (h11 : Step11) {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (hF : Frame G A A R g E F)
    (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A))) {x : G}
    (hx : x ∈ E ⊓ F) (hxA : x ∉ A) : ∃ Q ∈ pointsIn R E, Q ≤ E ⊓ F ∧ x ∈ Q := by
  classical
  have := Fintype.ofFinite ↥(pointsIn R E)
  have hKte := AS76b.tightlyEmbedded_centralizer hF.base.hyp.standard
  have hR := hF.sylowR
  have hRA : R ≤ centralizer (A : Set G) := hR.le
  have hRA1 : R ⊓ A = ⊥ := inf_eq_bot_of_odd_center hRA hR.isPGroup hodd
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hF.elemE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hptA : ∀ Q ∈ pointsIn R E, Q ⊓ A = ⊥ := fun Q hQ => by
    by_cases hQR : Q = R
    · rw [hQR]
      exact hRA1
    · exact inf_eq_bot_of_mem_pointsIn_frame h11 hE16 hF hL hodd Q hQ hQR
  set lF : Finset ↥(pointsIn R E) := {Q : ↥(pointsIn R E) | (Q : Subgroup G) ≤ E ⊓ F}.toFinset
  set t : ↥(pointsIn R E) → Finset G := fun Q =>
    ((Q : Subgroup G) : Set G).toFinite.toFinset.erase 1
  set SF : Finset G := (((E ⊓ F : Subgroup G) : Set G) \ (A : Set G)).toFinite.toFinset
  have hsub : lF.biUnion t ⊆ SF := by
    intro y hy
    simp only [lF, t, Finset.mem_biUnion, Set.mem_toFinset, Set.mem_ofPred_eq, Finset.mem_erase,
      Set.Finite.mem_toFinset, SetLike.mem_coe] at hy
    obtain ⟨Q, hQl, hy1, hyQ⟩ := hy
    simp only [SF, Set.Finite.mem_toFinset, Set.mem_sdiff, SetLike.mem_coe]
    refine ⟨hQl hyQ, fun hyA => hy1 ?_⟩
    have : y ∈ (Q : Subgroup G) ⊓ A := ⟨hyQ, hyA⟩
    rwa [hptA Q Q.2, mem_bot] at this
  have hdisj : (lF : Set ↥(pointsIn R E)).PairwiseDisjoint t := by
    intro Q _ Q' _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro y hy hy'
    simp only [t, Finset.mem_erase, Set.Finite.mem_toFinset, SetLike.mem_coe] at hy hy'
    have hbot := inf_eq_bot_of_mem_pointsIn hKte hR hcomm Q.2 Q'.2 (fun h => hne (Subtype.ext h))
    have : y ∈ (Q : Subgroup G) ⊓ Q' := ⟨hy.2, hy'.2⟩
    rw [hbot, mem_bot] at this
    exact hy.1 this
  have hcardt : ∀ Q ∈ lF, (t Q).card = 3 := fun Q _ => by
    simp only [t]
    rw [Finset.card_erase_of_mem (by simp), ← Set.ncard_eq_toFinset_card,
      (Nat.card_coe_set_eq _).symm]
    obtain ⟨-, y, hy⟩ := Q.2
    change Nat.card (Q : Subgroup G) - 1 = 3
    rw [hy, rightConjugate_card, hF.cardR]
  have hlF : lF.card = 4 := by
    have h := card_points_le_inf h11 hE16 hF hL hodd
    rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card'] at h
    exact h
  have hSF : SF.card = 12 := by
    simp only [SF]
    rw [← Set.ncard_eq_toFinset_card, ← Set.sdiff_inter_self_eq_sdiff,
      Set.ncard_sdiff Set.inter_subset_right]
    have h1 : ((E ⊓ F : Subgroup G) : Set G).ncard = 16 := by
      rw [← Nat.card_coe_set_eq]
      exact hF.card_inf
    have h2 : ((A : Set G) ∩ ((E ⊓ F : Subgroup G) : Set G)).ncard = 4 := by
      rw [Set.inter_comm, ← Nat.card_coe_set_eq]
      have := hF.card_sec2Z hodd
      rw [hF.sec2Z_eq] at this
      exact this
    omega
  have hcard : (lF.biUnion t).card = lF.card * 3 := by
    rw [Finset.card_biUnion hdisj, Finset.sum_const_nat hcardt]
  have heq : lF.biUnion t = SF := Finset.eq_of_subset_of_card_le hsub (by omega)
  have hxSF : x ∈ SF := by
    simp only [SF, Set.Finite.mem_toFinset, Set.mem_sdiff, SetLike.mem_coe]
    exact ⟨hx, hxA⟩
  rw [← heq] at hxSF
  simp only [lF, t, Finset.mem_biUnion, Set.mem_toFinset, Set.mem_ofPred_eq, Finset.mem_erase,
    Set.Finite.mem_toFinset, SetLike.mem_coe] at hxSF
  obtain ⟨Q, hQ, -, hxQ⟩ := hxSF
  exact ⟨Q, Q.2, hQ, hxQ⟩

theorem mem_of_mem_normalizer_of_not_le
    (h11 : Step11) {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (hF : Frame G A A R g E F)
    (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A))) {f : G} (hf : f ∈ F)
    {Q : Subgroup G} (hQ : Q ∈ pointsIn R E) (hQEF : ¬ Q ≤ E ⊓ F)
    (hfQ : f ∈ normalizer (Q : Set G)) : f ∈ E := by
  obtain ⟨hD, -⟩ := exists_pointsData h11 hE16 hF hL hodd
  have hFcomm : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hF.elemF.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hZEA : sec2Z A E F ≤ E ⊓ A := by
    rw [hF.sec2Z_eq]
    exact fun z hz => ⟨hz.1.1, hz.2⟩
  have hbot : Q ⊓ (E ⊓ F) = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [mem_bot]
    by_contra hy1
    have hyA : y ∉ A := fun h => hy1 (by
      have : y ∈ Q ⊓ (E ⊓ A) := ⟨hy.1, hQ.1 hy.1, h⟩
      rwa [hD.inf_H Q hQ, mem_bot] at this)
    obtain ⟨Q', hQ', hQ'EF, hyQ'⟩ := exists_mem_point_le_inf h11 hE16 hF hL hodd hy.2 hyA
    have hne : Q ≠ Q' := fun h => hQEF (h ▸ hQ'EF)
    have hm : y ∈ Q ⊓ Q' := ⟨hy.1, hyQ'⟩
    rw [hD.disj Q hQ Q' hQ' hne, mem_bot] at hm
    exact hy1 hm
  have hfq : ∀ q ∈ Q, q * f = f * q := by
    intro q hq
    have h1 : f * q * f⁻¹ * q⁻¹ ∈ Q ⊓ (E ⊓ A) := by
      refine ⟨Q.mul_mem ((mem_normalizer_iff.mp hfQ q).mp hq) (Q.inv_mem hq), hZEA ?_⟩
      have := (sec2Z A E F).inv_mem (hF.commutator_mem_sec2Z hL hodd (hQ.1 hq) hf)
      simpa [mul_assoc] using this
    rw [hD.inf_H Q hQ, mem_bot] at h1
    exact (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h1)).symm
  have hQ4 : Nat.card Q = 4 := by
    obtain ⟨-, y, hy⟩ := hQ
    rw [hy, rightConjugate_card, hF.cardR]
  have hN : E ⊓ F ≤ normalizer (Q : Set G) := fun k hk => centralizer_le_normalizer _
    (mem_centralizer_iff.mpr fun q hq => hD.comm q (hQ.1 hq) k hk.1)
  have hsup : Q ⊔ (E ⊓ F) = E := by
    refine eq_of_le_of_card_ge (sup_le hQ.1 inf_le_left) ?_
    have h := card_sup_mul_card_inf (H := Q) (R := E ⊓ F) hN
    rw [hbot, card_bot, mul_one, hQ4, hF.card_inf] at h
    rw [hF.cardE]
    omega
  have hle : E ≤ centralizer ({f} : Set G) := by
    rw [← hsup]
    exact sup_le (fun q hq => mem_centralizer_singleton_iff.mpr (hfq q hq))
      (fun k hk => mem_centralizer_singleton_iff.mpr (hFcomm k hk.2 f hf))
  exact mem_of_mem_centralizer_of_frame hF hL hodd f
    (mem_centralizer_iff.mpr fun e he => mem_centralizer_singleton_iff.mp (hle he)) 1
    (by rw [pow_one]; exact hF.elemF.2 f hf)

theorem sec2P_le_centralizer_inf
    (h11 : Step11) {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true)
    (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A))
    (hodd : Odd (Nat.card (center ↥A))) :
    sec2P E ≤ centralizer ((E ⊓ A : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hD, -⟩ := exists_pointsData h11 hE16 hF hL hodd
  have hR := hF.sylowR
  have hRA : R ≤ centralizer (A : Set G) := hR.le
  have hRA1 : R ⊓ A = ⊥ := inf_eq_bot_of_odd_center hRA hR.isPGroup hodd
  have hEA16 : Nat.card (E ⊓ A : Subgroup G) = 16 := by
    have := card_eq_card_inf_mul hRA hF.R_le_E hF.E_le hRA1
    rw [hF.cardE, hF.cardR] at this
    omega
  have hEP : E ⊓ A ≤ sec2P E := inf_le_left.trans
    (Sec2.le_sec2P (isPGroup_two_of_isElemAbelian hF.elemE) le_normalizer le_rfl)
  have hPN : sec2P E ≤ normalizer ((E ⊓ A : Subgroup G) : Set G) :=
    (Sec2.sec2P_le E).trans hD.normalizer_le_normalizer
  have hne : E ⊓ A ≠ ⊥ := fun h => by
    rw [h, card_bot] at hEA16
    omega
  obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    (Sec2.inf_centerIn_ne_bot' (Sec2.isPGroup_sec2P E) hEP hPN hne)
  obtain ⟨haEA, -, haC⟩ := a.2
  have ha1' : (a : G) ≠ 1 := fun h => ha1 (Subtype.ext h)
  intro p hp
  rw [mem_centralizer_iff]
  intro b hb
  by_cases hb1 : b = 1
  · rw [hb1, one_mul, mul_one]
  obtain ⟨n, hn, rfl⟩ := exists_conj_eq_of_card_sixteen hF.base.hyp.standard.1 hL hodd
    inf_le_right (AS76b.IsElemAbelian.mono hF.elemE inf_le_left) hEA16 haEA hb ha1' hb1
  have hnE : n ∈ normalizer (E : Set G) := mem_normalizer_of_mem_inf hF hn
  have hq : n⁻¹ * p * n ∈ sec2P E := by
    have := (mem_normalizer_iff.mp (Sec2.normalizer_le_normalizer_sec2P E (inv_mem hnE)) p).mp hp
    simpa using this
  have hc := mem_centralizer_iff.mp haC _ hq
  calc n * (a : G) * n⁻¹ * p = n * ((a : G) * (n⁻¹ * p * n)) * n⁻¹ := by group
    _ = n * ((n⁻¹ * p * n) * a) * n⁻¹ := by rw [← hc]
    _ = p * (n * a * n⁻¹) := by group

theorem mem_centralizerMod_of_mem_sec2P
    (h11 : Step11) {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (hF : Frame G A A R g E F)
    (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A))) {p f : G}
    (hp : p ∈ sec2P E) (hf : f ∈ F) :
    f⁻¹ * p * f * p⁻¹ ∈ centralizerMod (sec2P E) (R ⊔ sec2Z A E F) (sec2Z A E F) := by
  obtain ⟨hD, T, hT⟩ := exists_pointsData h11 hE16 hF hL hodd
  have hCE := mem_of_mem_centralizer_of_frame hF hL hodd
  have hFN := hF.F_le_normalizer hL hodd
  have hFcomm : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hF.elemF.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hpN := Sec2.sec2P_le E hp
  by_cases hfE : f ∈ E
  · refine le_centralizerMod hF ?_
    have := E.mul_mem (E.inv_mem hfE) ((mem_normalizer_iff.mp hpN f).mp hfE)
    simpa [mul_assoc] using this
  have hf2 : f * f = 1 := by rw [← sq]; exact hF.elemF.2 f hf
  have hfinv : f⁻¹ = f := inv_eq_of_mul_eq_one_left hf2
  have hu : f⁻¹ * p * f ∈ sec2P E := by
    have := (mem_normalizer_iff.mp
      (Sec2.normalizer_le_normalizer_sec2P E (hFN (F.inv_mem hf))) p).mp hp
    simpa using this
  set x := f⁻¹ * p * f * p⁻¹ with hx
  have hxP : x ∈ sec2P E := (sec2P E).mul_mem hu ((sec2P E).inv_mem hp)
  have hfx : f * x * f⁻¹ = x⁻¹ := by
    rw [hx]
    calc f * (f⁻¹ * p * f * p⁻¹) * f⁻¹ = p * f * p⁻¹ * f⁻¹ := by group
      _ = p * f⁻¹ * p⁻¹ * f := by rw [hfinv]
      _ = (f⁻¹ * p * f * p⁻¹)⁻¹ := by group
  have hxx : x * x ∈ E := (hD.sq_mem_and_commutator_mem hT hCE hxP hxP).1
  have hxN := Sec2.sec2P_le E hxP
  have hQ : rightConjugate R x⁻¹ ∈ pointsIn R E :=
    rightConjugate_mem_pointsIn hD.self_mem (inv_mem hxN)
  have hfQ : f ∈ normalizer (rightConjugate R x⁻¹ : Set G) := by
    refine Sec2.mem_normalizer_of_forall_conj_mem fun y hy => ?_
    rw [mem_rightConjugate_iff, inv_inv] at hy ⊢
    obtain ⟨r, hr, rfl⟩ : ∃ r ∈ R, x * r * x⁻¹ = y := ⟨x⁻¹ * y * x, hy, by group⟩
    have hfr : f * r * f⁻¹ = r := by
      rw [hFcomm f hf r (hF.R_le_F hr), mul_inv_cancel_right]
    have hcomm := hD.comm _ hxx _ (hD.R_le hr)
    have key : x⁻¹ * (f * (x * r * x⁻¹) * f⁻¹) * x = r := by
      calc x⁻¹ * (f * (x * r * x⁻¹) * f⁻¹) * x
          = x⁻¹ * ((f * x * f⁻¹) * (f * r * f⁻¹) * (f * x * f⁻¹)⁻¹) * x := by group
        _ = x⁻¹ * (x⁻¹ * r * x⁻¹⁻¹) * x := by rw [hfx, hfr]
        _ = (x * x)⁻¹ * (r * (x * x)) := by group
        _ = (x * x)⁻¹ * (x * x * r) := by rw [hcomm]
        _ = r := by group
    rw [key]
    exact hr
  have hle : rightConjugate R x⁻¹ ≤ E ⊓ F := by
    by_contra hnot
    exact hfE (mem_of_mem_normalizer_of_not_le h11 hE16 hF hL hodd hf hQ hnot hfQ)
  have h := mem_centralizerMod_of_rightConjugate_le h11 hE16 hF hL hodd
    ((sec2P E).inv_mem hxP) hle
  simpa using (centralizerMod (sec2P E) (R ⊔ sec2Z A E F) (sec2Z A E F)).inv_mem h

theorem sec2P_le_normalizer_sec2S
    (h11 : Step11) {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true)
    (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A))
    (hodd : Odd (Nat.card (center ↥A))) :
    sec2P E ≤ normalizer (sec2S A R E F : Set G) := by
  obtain ⟨hD, T, hT⟩ := exists_pointsData h11 hE16 hF hL hodd
  have hCE := mem_of_mem_centralizer_of_frame hF hL hodd
  intro p hp
  have h : sec2S A R E F ≤ (sec2S A R E F).comap (MulAut.conj p).toMonoidHom := by
    refine sup_le (fun f hf => ?_) (fun c hc => ?_)
    · show p * f * p⁻¹ ∈ sec2S A R E F
      have h1 := mem_centralizerMod_of_mem_sec2P h11 hE16 hF hL hodd hp hf
      rw [show p * f * p⁻¹ = f * (f⁻¹ * p * f * p⁻¹) by group]
      exact (sec2S A R E F).mul_mem (mem_sup_left hf) (mem_sup_right h1)
    · show p * c * p⁻¹ ∈ sec2S A R E F
      have hcP := (mem_centralizerMod.mp hc).1
      have h1 := (hD.sq_mem_and_commutator_mem hT hCE ((sec2P E).inv_mem hcP) hp).2
      rw [show p * c * p⁻¹ = c * (c⁻¹ * p * c⁻¹⁻¹ * p⁻¹) by group]
      exact mem_sup_right ((centralizerMod _ _ _).mul_mem hc (le_centralizerMod hF h1))
  exact Sec2.mem_normalizer_of_forall_conj_mem fun s hs => h hs

theorem sec2S_le_normalizer
    (h11 : Step11) {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true)
    (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A))
    (hodd : Odd (Nat.card (center ↥A))) : sec2S A R E F ≤ normalizer (F : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hD, T, hT⟩ := exists_pointsData h11 hE16 hF hL hodd
  have hCE := mem_of_mem_centralizer_of_frame hF hL hodd
  have hPR := sec2P_inf_normalizer_eq hD hT hCE (isPGroup_two_of_isElemAbelian hF.elemE)
  obtain ⟨-, -, hCEF⟩ := centralizerMod_facts h11 hE16 hF hL hodd
  have hR := hF.sylowR
  have hRA : R ≤ centralizer (A : Set G) := hR.le
  have hRA1 : R ⊓ A = ⊥ := inf_eq_bot_of_odd_center hRA hR.isPGroup hodd
  have hREF : R ≤ E ⊓ F := hF.inf_eq ▸ le_sup_left
  have hFcomm : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hF.elemF.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hFN := hF.F_le_normalizer hL hodd
  refine sup_le le_normalizer fun c hc => ?_
  have hcP := (mem_centralizerMod.mp hc).1
  have hcN := Sec2.sec2P_le E hcP
  have hfc : ∀ f ∈ F, f⁻¹ * c * f * c⁻¹ ∈ E := by
    intro f hf
    have hwP : f⁻¹ * c * f * c⁻¹ ∈ sec2P E := by
      have := (mem_normalizer_iff.mp
        (Sec2.normalizer_le_normalizer_sec2P E (hFN (F.inv_mem hf))) c).mp hcP
      exact (sec2P E).mul_mem (by simpa using this) ((sec2P E).inv_mem hcP)
    refine hPR.le ⟨hwP, Sec2.mem_normalizer_of_forall_conj_mem fun r hr => ?_⟩
    have hq : c⁻¹ * r * c ∈ E ⊓ F := by
      have := (mem_normalizer_iff.mp (inv_mem (hCEF hc)) r).mp (hREF hr)
      simpa using this
    have h1 : f * (c⁻¹ * r * c) * f⁻¹ = c⁻¹ * r * c := by
      rw [hFcomm f hf _ hq.2, mul_inv_cancel_right]
    have h2 : f⁻¹ * r * f = r := by
      rw [mul_assoc, ← hFcomm f hf r (hF.R_le_F hr), inv_mul_cancel_left]
    have heq : f⁻¹ * c * f * c⁻¹ * r * (f⁻¹ * c * f * c⁻¹)⁻¹ = r := by
      calc f⁻¹ * c * f * c⁻¹ * r * (f⁻¹ * c * f * c⁻¹)⁻¹
          = f⁻¹ * c * (f * (c⁻¹ * r * c) * f⁻¹) * c⁻¹ * f := by group
        _ = f⁻¹ * c * (c⁻¹ * r * c) * c⁻¹ * f := by rw [h1]
        _ = f⁻¹ * r * f := by group
        _ = r := h2
    rw [heq]
    exact hr
  set V := rightConjugate F c⁻¹ with hVdef
  have hmemV : ∀ v, v ∈ V ↔ c⁻¹ * v * c ∈ F := fun v => by
    rw [hVdef, mem_rightConjugate_iff, inv_inv]
  have hVEF : V ≤ E ⊔ F := by
    intro v hv
    rw [hmemV] at hv
    have h1 := hfc _ hv
    rw [show v = (c⁻¹ * v * c) * ((c⁻¹ * v * c)⁻¹ * c * (c⁻¹ * v * c) * c⁻¹) by group]
    exact mul_mem (mem_sup_right hv) (mem_sup_left h1)
  have hRV : R ≤ V := by
    intro r hr
    rw [hmemV]
    have := (mem_normalizer_iff.mp (inv_mem (hCEF hc)) r).mp (hREF hr)
    exact (by simpa using this : c⁻¹ * r * c ∈ E ⊓ F).2
  have hV64 : Nat.card V = 64 := by rw [hVdef, rightConjugate_card, hF.cardF]
  have hVe : IsElemAbelian 2 V := AS76b.isElemAbelian_rightConjugate hF.elemF c⁻¹
  have hVAR : V ≤ A ⊔ R := hVEF.trans (sup_le hF.E_le hF.F_le)
  have hVA16 : Nat.card (V ⊓ A : Subgroup G) = 16 := by
    have := card_eq_card_inf_mul hRA hRV hVAR hRA1
    rw [hV64, hF.cardR] at this
    omega
  have hEA16 : Nat.card (E ⊓ A : Subgroup G) = 16 := by
    have := card_eq_card_inf_mul hRA hF.R_le_E hF.E_le hRA1
    rw [hF.cardE, hF.cardR] at this
    omega
  have hFA16 : Nat.card (F ⊓ A : Subgroup G) = 16 := by
    have := card_eq_card_inf_mul hRA hF.R_le_F hF.F_le hRA1
    rw [hF.cardF, hF.cardR] at this
    omega
  have hEAFA : E ⊓ A ≠ F ⊓ A := by
    intro h
    apply hF.ne
    rw [eq_inf_sup_of_le_sup hRA hF.R_le_E hF.E_le, eq_inf_sup_of_le_sup hRA hF.R_le_F hF.F_le, h]
  obtain ⟨-, hDA, -⟩ := sylow_sup_structure hRA hR.isPGroup hF.sylow
  rcases Sec2.eq_or_eq_of_card_sixteen hF.base.hyp.standard.1 hL hodd hDA
      (inf_le_inf_right A hVEF) (AS76b.IsElemAbelian.mono hVe inf_le_left) hVA16
      (inf_le_inf_right A le_sup_left) (AS76b.IsElemAbelian.mono hF.elemE inf_le_left) hEA16
      (inf_le_inf_right A le_sup_right) (AS76b.IsElemAbelian.mono hF.elemF inf_le_left) hFA16
      hEAFA with h | h
  ·
    exfalso
    apply hF.ne
    have hVE : V = E := by
      rw [eq_inf_sup_of_le_sup hRA hRV hVAR, h, ← eq_inf_sup_of_le_sup hRA hF.R_le_E hF.E_le]
    have hFV : F = rightConjugate V c := by
      rw [hVdef, rightConjugate_mul, inv_mul_cancel, rightConjugate_one]
    rw [hFV, hVE]
    exact ((rightConjugate_eq_self_iff E c).mpr hcN).symm
  ·
    have hVF : V = F := by
      rw [eq_inf_sup_of_le_sup hRA hRV hVAR, h, ← eq_inf_sup_of_le_sup hRA hF.R_le_F hF.F_le]
    have : c⁻¹ ∈ normalizer (F : Set G) := (rightConjugate_eq_self_iff F c⁻¹).mp hVF
    simpa using inv_mem this

theorem sec2S_eq_sup_rightConjugate
    (h11 : Step11) {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (hF : Frame G A A R g E F)
    (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A))) {h : G}
    (hh : h ∈ sec2P E) (hhC : h ∉ centralizerMod (sec2P E) (R ⊔ sec2Z A E F) (sec2Z A E F)) :
    F ⊓ rightConjugate F h = sec2Z A E F ∧ F ⊔ rightConjugate F h = sec2S A R E F := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hD, T, hT⟩ := exists_pointsData h11 hE16 hF hL hodd
  have hCE := mem_of_mem_centralizer_of_frame hF hL hodd
  have htr := exists_mem_sec2P_rightConjugate_eq h11 hE16 hF hL hodd
  have hPS := sec2P_le_normalizer_sec2S h11 hE16 hF hL hodd
  have hSF := sec2S_le_normalizer h11 hE16 hF hL hodd
  have hPZ := sec2P_le_centralizer_inf h11 hE16 hF hL hodd
  have hFcomm : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hF.elemF.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hhN := Sec2.sec2P_le E hh
  have hZ := hF.sec2Z_eq
  have hFS : F ≤ sec2S A R E F := le_sup_left
  have hmemF' : ∀ x, x ∈ rightConjugate F h ↔ h * x * h⁻¹ ∈ F := fun x =>
    mem_rightConjugate_iff F h x
  have hF'S : rightConjugate F h ≤ sec2S A R E F := by
    intro x hx
    rw [hmemF'] at hx
    have := (mem_normalizer_iff.mp (hPS ((sec2P E).inv_mem hh)) _).mp (hFS hx)
    simpa [mul_assoc] using this
  have hinf : F ⊓ rightConjugate F h = sec2Z A E F := by
    refine le_antisymm (fun x hx => ?_) (fun z hz => ?_)
    · have hxF : x ∈ F := hx.1
      have hxF' : h * x * h⁻¹ ∈ F := (hmemF' x).mp hx.2
      have hxE : x ∈ E := by
        by_contra hxE
        have hyE : h * x * h⁻¹ ∉ E := fun hy => hxE (by
          have := (mem_normalizer_iff.mp (inv_mem hhN) _).mp hy
          simpa [mul_assoc] using this)
        have hQ : rightConjugate R h ∈ pointsIn R E :=
          rightConjugate_mem_pointsIn hD.self_mem hhN
        have hxQ : x ∈ normalizer (rightConjugate R h : Set G) := by
          refine Sec2.mem_normalizer_of_forall_conj_mem fun q hq => ?_
          rw [mem_rightConjugate_iff] at hq ⊢
          have hyR : h * x * h⁻¹ ∈ normalizer (R : Set G) := centralizer_le_normalizer _
            (mem_centralizer_iff.mpr fun r hr => hFcomm r (hF.R_le_F hr) _ hxF')
          have := (mem_normalizer_iff.mp hyR _).mp hq
          have heq : h * (x * q * x⁻¹) * h⁻¹ =
              h * x * h⁻¹ * (h * q * h⁻¹) * (h * x * h⁻¹)⁻¹ := by group
          rw [heq]
          exact this
        have hQEF : rightConjugate R h ≤ E ⊓ F := by
          by_contra hnot
          exact hxE (mem_of_mem_normalizer_of_not_le h11 hE16 hF hL hodd hxF hQ hnot hxQ)
        exact hhC (mem_centralizerMod_of_rightConjugate_le h11 hE16 hF hL hodd hh hQEF)
      have hyEF : h * x * h⁻¹ ∈ E ⊓ F := ⟨(mem_normalizer_iff.mp hhN x).mp hxE, hxF'⟩
      by_cases hxA : x ∈ A
      · rw [hZ]
        exact ⟨⟨hxE, hxF⟩, hxA⟩
      exfalso
      have hyA : h * x * h⁻¹ ∉ A := fun hyA => hxA (by
        have hc := mem_centralizer_iff.mp (hPZ ((sec2P E).inv_mem hh)) _ ⟨hyEF.1, hyA⟩
        have hxy : x = h * x * h⁻¹ := by
          calc x = h⁻¹ * (h * x * h⁻¹) * h := by group
            _ = h * x * h⁻¹ * h⁻¹ * h := by rw [← hc]
            _ = h * x * h⁻¹ := by group
        rw [hxy]
        exact hyA)
      obtain ⟨Q', hQ', hQ'EF, hxQ'⟩ :=
        exists_mem_point_le_inf h11 hE16 hF hL hodd ⟨hxE, hxF⟩ hxA
      obtain ⟨Q'', hQ'', hQ''EF, hyQ''⟩ := exists_mem_point_le_inf h11 hE16 hF hL hodd hyEF hyA
      have hxQ'' : x ∈ rightConjugate Q'' h := (mem_rightConjugate_iff Q'' h x).mpr hyQ''
      have hQQ : Q' = rightConjugate Q'' h := by
        by_contra hne
        have hm : x ∈ Q' ⊓ rightConjugate Q'' h := ⟨hxQ', hxQ''⟩
        rw [hD.disj _ hQ' _ (rightConjugate_mem_pointsIn hQ'' hhN) hne, mem_bot] at hm
        exact hxA (by rw [hm]; exact A.one_mem)
      obtain ⟨p, hp, rfl⟩ := htr Q'' hQ''
      have hpC := mem_centralizerMod_of_rightConjugate_le h11 hE16 hF hL hodd hp hQ''EF
      have hphC := mem_centralizerMod_of_rightConjugate_le h11 hE16 hF hL hodd
        ((sec2P E).mul_mem hp hh) (by rw [← rightConjugate_mul, ← hQQ]; exact hQ'EF)
      apply hhC
      have := (centralizerMod _ _ _).mul_mem ((centralizerMod _ _ _).inv_mem hpC) hphC
      simpa using this
    · have hzEFA : z ∈ E ⊓ F ⊓ A := by rw [← hZ]; exact hz
      refine ⟨hzEFA.1.2, (hmemF' z).mpr ?_⟩
      have hc := mem_centralizer_iff.mp (hPZ hh) z ⟨hzEFA.1.1, hzEFA.2⟩
      rw [← hc, mul_inv_cancel_right]
      exact hzEFA.1.2
  refine ⟨hinf, ?_⟩
  have hF'N : rightConjugate F h ≤ normalizer (F : Set G) := hF'S.trans hSF
  have hcard := card_sup_mul_card_inf (H := F) (R := rightConjugate F h) hF'N
  rw [hinf, hF.card_sec2Z hodd, rightConjugate_card, hF.cardF] at hcard
  have hS := (isElemQuot_sec2S h11 hE16 hF hL hodd).2
  have hScard : Nat.card (sec2S A R E F) = 16 * 64 := by
    have h1 := relIndex_mul_card E (sec2S A R E F)
    rw [inf_eq_left.mpr hS.1, hS.2.1, hF.cardE] at h1
    exact h1.symm
  exact eq_of_le_of_card_ge (sup_le hFS hF'S) (by omega)

theorem exists_mem_sec2P_not_mem_centralizerMod
    (h11 : Step11) {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (hF : Frame G A A R g E F)
    (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A))) :
    ∃ h ∈ sec2P E, h ∉ centralizerMod (sec2P E) (R ⊔ sec2Z A E F) (sec2Z A E F) := by
  obtain ⟨-, hCidx, -⟩ := centralizerMod_facts h11 hE16 hF hL hodd
  have hPq := isElemQuot_sec2P h11 hE16 hF hL hodd
  refine IsConcreteLE.not_le_iff_exists.mp fun hle => ?_
  have hCP : centralizerMod (sec2P E) (R ⊔ sec2Z A E F) (sec2Z A E F) ≤ sec2P E :=
    fun c hc => (mem_centralizerMod.mp hc).1
  rw [le_antisymm hCP hle, hPq.2.1] at hCidx
  omega

theorem exists_mem_centralizerMod_not_mem
    (h11 : Step11) {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (hF : Frame G A A R g E F)
    (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A))) :
    ∃ c ∈ centralizerMod (sec2P E) (R ⊔ sec2Z A E F) (sec2Z A E F), c ∉ E := by
  obtain ⟨-, hCidx, -⟩ := centralizerMod_facts h11 hE16 hF hL hodd
  refine IsConcreteLE.not_le_iff_exists.mp fun hle => ?_
  rw [relIndex_eq_one.mpr hle] at hCidx
  omega

theorem sq_mem_and_commutator_mem_sec2Z
    (h11 : Step11) {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (hF : Frame G A A R g E F)
    (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A))) {a b : G}
    (ha : a ∈ sec2S A R E F) (hb : b ∈ sec2S A R E F) :
    a * a ∈ sec2Z A E F ∧ a * b * a⁻¹ * b⁻¹ ∈ sec2Z A E F := by
  obtain ⟨h, hh, hhC⟩ := exists_mem_sec2P_not_mem_centralizerMod h11 hE16 hF hL hodd
  obtain ⟨hinf, hsup⟩ := sec2S_eq_sup_rightConjugate h11 hE16 hF hL hodd hh hhC
  have hPS := sec2P_le_normalizer_sec2S h11 hE16 hF hL hodd
  have hSF := sec2S_le_normalizer h11 hE16 hF hL hodd
  have hFcomm : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hF.elemF.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hF2 : ∀ x ∈ F, x * x = 1 := fun x hx => by rw [← sq]; exact hF.elemF.2 x hx
  have hF'e := AS76b.isElemAbelian_rightConjugate hF.elemF h
  have hF'comm : ∀ x ∈ rightConjugate F h, ∀ y ∈ rightConjugate F h, x * y = y * x :=
    fun x hx y hy => congrArg Subtype.val (hF'e.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hF'2 : ∀ x ∈ rightConjugate F h, x * x = 1 := fun x hx => by
    rw [← sq]; exact hF'e.2 x hx
  have hSF' : sec2S A R E F ≤ normalizer (rightConjugate F h : Set G) := by
    intro s hs
    refine Sec2.mem_normalizer_of_forall_conj_mem fun w hw => ?_
    rw [mem_rightConjugate_iff] at hw ⊢
    have hhs : h * s * h⁻¹ ∈ sec2S A R E F := (mem_normalizer_iff.mp (hPS hh) s).mp hs
    have := (mem_normalizer_iff.mp (hSF hhs) _).mp hw
    have heq : h * (s * w * s⁻¹) * h⁻¹ =
        h * s * h⁻¹ * (h * w * h⁻¹) * (h * s * h⁻¹)⁻¹ := by group
    rw [heq]
    exact this
  have hZF' : sec2Z A E F ≤ rightConjugate F h := by rw [← hinf]; exact inf_le_right
  have hZF : sec2Z A E F ≤ F := by rw [← hinf]; exact inf_le_left
  have hFS : F ≤ sec2S A R E F := le_sup_left
  rw [← hsup] at ha hb
  refine Sec2.sq_mem_and_commutator_mem_of_sup ?_
    ((le_sup_left.trans hsup.le).trans hSF') hFcomm hF2 hF'comm hF'2 ?_ ha hb
  · exact sup_le (fun f hf => mem_centralizer_iff.mpr fun z hz => hFcomm z (hZF hz) f hf)
      (fun w hw => mem_centralizer_iff.mpr fun z hz => hF'comm z (hZF' hz) w hw)
  · intro f hf w hw
    rw [← hinf]
    have hwS : w ∈ sec2S A R E F := by rw [← hsup]; exact mem_sup_right hw
    refine ⟨?_, ?_⟩
    · have h1 := (mem_normalizer_iff.mp (hSF (inv_mem hwS)) f).mp hf
      have h2 := F.mul_mem (F.inv_mem hf) h1
      simpa [mul_assoc] using h2
    · have h1 := (mem_normalizer_iff.mp (hSF' (inv_mem (hFS hf))) w⁻¹).mp (inv_mem hw)
      have h2 := (rightConjugate F h).mul_mem h1 hw
      simpa [mul_assoc] using h2

theorem commutator_sec2S_eq
    (h11 : Step11) {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true)
    (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A))
    (hodd : Odd (Nat.card (center ↥A))) : ⁅sec2S A R E F, sec2S A R E F⁆ = sec2Z A E F := by
  obtain ⟨hD, T, hT⟩ := exists_pointsData h11 hE16 hF hL hodd
  have hCE := mem_of_mem_centralizer_of_frame hF hL hodd
  have hPR := sec2P_inf_normalizer_eq hD hT hCE (isPGroup_two_of_isElemAbelian hF.elemE)
  refine le_antisymm (commutator_le.mpr fun a ha b hb => ?_) fun z hz => ?_
  · rw [commutatorElement_def]
    exact (sq_mem_and_commutator_mem_sec2Z h11 hE16 hF hL hodd ha hb).2
  obtain ⟨c, hc, hcE⟩ := exists_mem_centralizerMod_not_mem h11 hE16 hF hL hodd
  have hcP := (mem_centralizerMod.mp hc).1
  have hcc := (mem_centralizerMod.mp hc).2.2
  have hcN := Sec2.sec2P_le E hcP
  set φ : ↥R → ↥(sec2Z A E F) := fun r => ⟨(r : G)⁻¹ * c⁻¹ * r * c, hcc r (mem_sup_left r.2)⟩
  have hinj : Function.Injective φ := by
    intro r₁ r₂ h
    have h' : (r₁ : G)⁻¹ * c⁻¹ * r₁ * c = (r₂ : G)⁻¹ * c⁻¹ * r₂ * c := congrArg Subtype.val h
    have h2 : c⁻¹ * (r₂ : G) * c = (r₂ : G) * ((r₁ : G)⁻¹ * c⁻¹ * r₁ * c) := by
      rw [h']
      group
    have hu : c * ((r₂ : G) * (r₁ : G)⁻¹) * c⁻¹ = (r₂ : G) * (r₁ : G)⁻¹ := by
      have hu' : c⁻¹ * ((r₂ : G) * (r₁ : G)⁻¹) * c = (r₂ : G) * (r₁ : G)⁻¹ := by
        calc c⁻¹ * ((r₂ : G) * (r₁ : G)⁻¹) * c
            = (c⁻¹ * (r₂ : G) * c) * (c⁻¹ * (r₁ : G) * c)⁻¹ := by group
          _ = (r₂ : G) * ((r₁ : G)⁻¹ * c⁻¹ * r₁ * c) * (c⁻¹ * (r₁ : G) * c)⁻¹ := by rw [h2]
          _ = (r₂ : G) * (r₁ : G)⁻¹ := by group
      calc c * ((r₂ : G) * (r₁ : G)⁻¹) * c⁻¹
          = c * (c⁻¹ * ((r₂ : G) * (r₁ : G)⁻¹) * c) * c⁻¹ := by rw [hu']
        _ = (r₂ : G) * (r₁ : G)⁻¹ := by group
    by_contra hne
    have hu1 : (r₂ : G) * (r₁ : G)⁻¹ ≠ 1 := fun h1 =>
      hne (Subtype.ext (mul_inv_eq_one.mp h1).symm)
    have huR : (r₂ : G) * (r₁ : G)⁻¹ ∈ R := R.mul_mem r₂.2 (R.inv_mem r₁.2)
    have hRc : rightConjugate R c = R := by
      by_contra hne'
      have hm : (r₂ : G) * (r₁ : G)⁻¹ ∈ rightConjugate R c ⊓ R := by
        refine ⟨(mem_rightConjugate_iff R c _).mpr ?_, huR⟩
        rw [hu]
        exact huR
      rw [hD.disj _ (rightConjugate_mem_pointsIn hD.self_mem hcN) _ hD.self_mem hne',
        mem_bot] at hm
      exact hu1 hm
    exact hcE (hPR.le ⟨hcP, (rightConjugate_eq_self_iff R c).mp hRc⟩)
  have hbij := hinj.bijective_of_nat_card_le (le_of_eq (by rw [hF.card_sec2Z hodd, hF.cardR]))
  obtain ⟨r, hr⟩ := hbij.2 ⟨z, hz⟩
  have hzr : z = (r : G)⁻¹ * c⁻¹ * r * c := (congrArg Subtype.val hr).symm
  have hES : E ≤ sec2S A R E F := (le_centralizerMod hF).trans le_sup_right
  have hcS : c ∈ sec2S A R E F := (le_sup_right : _ ≤ sec2S A R E F) hc
  have := commutator_mem_commutator (H₁ := sec2S A R E F) (H₂ := sec2S A R E F)
    (inv_mem (hES (hF.R_le_E r.2))) (inv_mem hcS)
  rw [hzr]
  simpa [commutatorElement_def] using this

theorem centerIn_sec2S_eq
    (h11 : Step11) {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true)
    (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A))
    (hodd : Odd (Nat.card (center ↥A))) : centerIn (sec2S A R E F) = sec2Z A E F := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hD, T, hT⟩ := exists_pointsData h11 hE16 hF hL hodd
  have hCE := mem_of_mem_centralizer_of_frame hF hL hodd
  have hPZ := sec2P_le_centralizer_inf h11 hE16 hF hL hodd
  have hZ := hF.sec2Z_eq
  have hFcomm : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hF.elemF.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hES : E ≤ sec2S A R E F := (le_centralizerMod hF).trans le_sup_right
  have hFS : F ≤ sec2S A R E F := le_sup_left
  have hS := (isElemQuot_sec2S h11 hE16 hF hL hodd).2
  have hS2 : IsPGroup 2 (sec2S A R E F) := by
    have h1 := relIndex_mul_card E (sec2S A R E F)
    rw [inf_eq_left.mpr hS.1, hS.2.1, hF.cardE] at h1
    exact IsPGroup.of_card (n := 10) (by rw [← h1]; norm_num)
  refine le_antisymm (fun x hx => ?_) (fun z hz => ?_)
  · obtain ⟨hxS, hxC⟩ := hx
    have hxE : x ∈ E := by
      obtain ⟨n, hn⟩ := hS2 ⟨x, hxS⟩
      exact hCE x (mem_centralizer_iff.mpr fun e he => mem_centralizer_iff.mp hxC e (hES he)) n
        (by simpa using congrArg Subtype.val hn)
    have hxA : x ∈ A := by
      by_contra hxA
      obtain ⟨Q, hQ, hxQ⟩ := hD.cover x hxE (fun h => hxA h.2)
      obtain ⟨c, hc, hcE⟩ := exists_mem_centralizerMod_not_mem h11 hE16 hF hL hodd
      have hcP := (mem_centralizerMod.mp hc).1
      have hcN := Sec2.sec2P_le E hcP
      have hcS : c ∈ sec2S A R E F := (le_sup_right : _ ≤ sec2S A R E F) hc
      have hQQ : rightConjugate Q c⁻¹ = Q := by
        by_contra hne
        have hm : x ∈ rightConjugate Q c⁻¹ ⊓ Q := by
          refine ⟨(mem_rightConjugate_iff Q c⁻¹ x).mpr ?_, hxQ⟩
          have hcx := mem_centralizer_iff.mp hxC c hcS
          rw [inv_inv, mul_assoc, ← hcx, inv_mul_cancel_left]
          exact hxQ
        rw [hD.disj _ (rightConjugate_mem_pointsIn hQ (inv_mem hcN)) _ hQ hne, mem_bot] at hm
        exact hxA (by rw [hm]; exact A.one_mem)
      have hfix : pointsAction R E ⟨c, hcN⟩ ⟨Q, hQ⟩ = ⟨Q, hQ⟩ :=
        Subtype.ext (by rw [coe_pointsAction_apply]; exact hQQ)
      exact hcE (hD.mem_of_apply_eq hT hCE (p := ⟨c, hcN⟩) hcP hfix)
    have hxEF : x ∈ E ⊓ F := by
      rw [hF.inf_eq_center]
      refine ⟨mem_sup_left hxE, ?_⟩
      show x ∈ centralizer ((E ⊔ F : Subgroup G) : Set G)
      have hle : E ⊔ F ≤ centralizer ({x} : Set G) := sup_le
        (fun e he => mem_centralizer_singleton_iff.mpr (hD.comm e he x hxE))
        (fun f hf => mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hxC f (hFS hf)))
      exact mem_centralizer_iff.mpr fun y hy => mem_centralizer_singleton_iff.mp (hle hy)
    rw [hZ]
    exact ⟨hxEF, hxA⟩
  · have hzEFA : z ∈ E ⊓ F ⊓ A := by rw [← hZ]; exact hz
    refine ⟨hES hzEFA.1.1, ?_⟩
    show z ∈ centralizer ((sec2S A R E F : Subgroup G) : Set G)
    have hle : sec2S A R E F ≤ centralizer ({z} : Set G) := sup_le
      (fun f hf => mem_centralizer_singleton_iff.mpr (hFcomm f hf z hzEFA.1.2))
      (fun c hc => mem_centralizer_singleton_iff.mpr
        (mem_centralizer_iff.mp (hPZ (mem_centralizerMod.mp hc).1) z ⟨hzEFA.1.1, hzEFA.2⟩).symm)
    exact mem_centralizer_iff.mpr fun y hy => mem_centralizer_singleton_iff.mp (hle hy)

end Frame

theorem step24_of (h11 : Step11)
    {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) : Step24 := by
  intro G _ _ A R g E F hS
  exact ⟨hS.frame.card_sec2Z hS.odd, centerIn_sec2S_eq h11 hE16 hS.frame hS.type hS.odd,
    commutator_sec2S_eq h11 hE16 hS.frame hS.type hS.odd,
    fun s hs => (sq_mem_and_commutator_mem_sec2Z h11 hE16 hS.frame hS.type hS.odd hs hs).1⟩

end CFSG.ComponentClassification.AS81
