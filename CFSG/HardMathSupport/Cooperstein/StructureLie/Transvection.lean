module

public import CFSG.HardMathSupport.Cooperstein.StructureLie.Nodes
import CFSG.HardMathSupport.Cooperstein.Coordinator.Setting

public section

namespace CFSG.HardMathSupport.Cooperstein.StructureLie

open CFSG CFSG.RankThree.PartTwo
open scoped commutatorElement
open CFSG.AGLEmbedding (Asc81bHyp IsWeakSBlock barM IsClassicalTwoOrG2 blockV)

section Aux

variable {G : Type} [Group G]

theorem mem_or_exists_of_mem_zpowers_sup {C : Subgroup G} {s : G}
    (hn : s ∈ Subgroup.normalizer (C : Set G)) (hs2 : s ^ 2 ∈ C) {b : G}
    (hb : b ∈ Subgroup.zpowers s ⊔ C) : b ∈ C ∨ ∃ c ∈ C, b = s * c := by
  have hle : Subgroup.zpowers s ≤ Subgroup.normalizer (C : Set G) := by
    rw [Subgroup.zpowers_le]; exact hn
  have hco := Subgroup.coe_mul_of_left_le_normalizer_right (Subgroup.zpowers s) C hle
  have hb' : b ∈ ((Subgroup.zpowers s ⊔ C : Subgroup G) : Set G) := hb
  rw [hco] at hb'
  obtain ⟨x, hx, c, hc, rfl⟩ := hb'
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hk : ∀ k : ℤ, s ^ (2 * k) ∈ C := fun k => by
    rw [zpow_mul, zpow_ofNat]; exact zpow_mem hs2 k
  rcases Int.even_or_odd' i with ⟨k, rfl | rfl⟩
  · exact Or.inl (C.mul_mem (hk k) hc)
  · right
    refine ⟨s ^ (2 * k) * c, C.mul_mem (hk k) hc, ?_⟩
    show s ^ (2 * k + 1) * c = s * (s ^ (2 * k) * c)
    rw [zpow_add_one, ← (Commute.self_zpow s (2 * k)).eq, mul_assoc]

theorem card_commutator_zpowers_eq_two [Finite G] (V : Subgroup G) (s : G)
    (hab : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v) (hn : ∀ v ∈ V, s * v * s⁻¹ ∈ V)
    (hs2 : ∀ v ∈ V, s ^ 2 * v = v * s ^ 2) (hns : ∃ v ∈ V, s * v ≠ v * s)
    (hcard : Nat.card V ≤ 2 * Nat.card ↥(V ⊓ Subgroup.centralizer ({s} : Set G))) :
    Nat.card ↥⁅V, Subgroup.zpowers s⁆ = 2 := by
  have hcomm : ∀ x y : G, ⁅x, y⁆ = x * (y * x * y⁻¹)⁻¹ := fun x y => by
    simp [commutatorElement_def, mul_assoc]
  let f : V →* G := MonoidHom.mk' (fun v : V => ⁅(v : G), s⁆) (by
    intro v w
    simp only [hcomm]
    have hu := hn v v.2
    have ht := hn w w.2
    have key : s * ((v : G) * w) * s⁻¹ = (s * v * s⁻¹) * (s * w * s⁻¹) := by group
    simp only [Subgroup.coe_mul]
    rw [key, mul_inv_rev]
    have h1 := hab ((w : G) * (s * w * s⁻¹)⁻¹) (V.mul_mem w.2 (V.inv_mem ht))
      (s * v * s⁻¹)⁻¹ (V.inv_mem hu)
    calc (v : G) * w * ((s * w * s⁻¹)⁻¹ * (s * v * s⁻¹)⁻¹)
        = v * (w * (s * w * s⁻¹)⁻¹) * (s * v * s⁻¹)⁻¹ := by group
      _ = v * ((s * v * s⁻¹)⁻¹ * (w * (s * w * s⁻¹)⁻¹)) := by rw [mul_assoc, h1]
      _ = _ := by group)
  have hf : ∀ v : V, f v = ⁅(v : G), s⁆ := fun v => rfl
  have hact : ∀ g ∈ Subgroup.zpowers s, ∀ v ∈ V, ⁅v, g⁆ = 1 ∨ ⁅v, g⁆ = ⁅v, s⁆ := by
    intro g hg v hv
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    have hc : ∀ (k : ℤ) (w : G), w ∈ V → s ^ (2 * k) * w * (s ^ (2 * k))⁻¹ = w := by
      intro k w hw
      have : Commute (s ^ 2) w := hs2 w hw
      have h2 := (this.zpow_left k).eq
      rw [zpow_mul, zpow_ofNat, h2]; group
    rcases Int.even_or_odd' i with ⟨k, rfl | rfl⟩
    · left
      rw [hcomm, hc k v hv]; group
    · right
      rw [hcomm v (s ^ (2 * k + 1)), hcomm v s, zpow_add_one]
      have : s ^ (2 * k) * s * (v : G) * (s ^ (2 * k) * s)⁻¹ =
          s ^ (2 * k) * (s * v * s⁻¹) * (s ^ (2 * k))⁻¹ := by group
      rw [this, hc k _ (hn v hv)]
  have hrange : ⁅V, Subgroup.zpowers s⁆ = f.range := by
    refine le_antisymm ?_ ?_
    · rw [Subgroup.commutator_def]
      refine Subgroup.closure_le _ |>.mpr ?_
      rintro _ ⟨v, hv, g, hg, rfl⟩
      rcases hact g hg v hv with h | h
      · rw [h]; exact f.range.one_mem
      · rw [h]; exact ⟨⟨v, hv⟩, rfl⟩
    · rintro _ ⟨v, rfl⟩
      rw [hf]
      exact Subgroup.commutator_mem_commutator v.2 (Subgroup.mem_zpowers s)
  rw [hrange]
  have hker : (V ⊓ Subgroup.centralizer ({s} : Set G)).subgroupOf V ≤ f.ker := by
    intro v hv
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff] at hv
    rw [MonoidHom.mem_ker, hf, commutatorElement_eq_one_iff_mul_comm]
    exact hv.2
  have hkc : Nat.card ↥(V ⊓ Subgroup.centralizer ({s} : Set G)) ≤ Nat.card f.ker := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_left : V ⊓ Subgroup.centralizer ({s} : Set G) ≤ V)).toEquiv]
    exact Subgroup.card_le_of_le hker
  have hprod : Nat.card f.range * Nat.card f.ker = Nat.card V := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
    exact (Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker).symm
  have hpos : 0 < Nat.card f.ker := Nat.card_pos
  have hle : Nat.card f.range ≤ 2 := by
    by_contra h
    push Not at h
    have : 2 * Nat.card f.ker < Nat.card f.range * Nat.card f.ker :=
      Nat.mul_lt_mul_of_pos_right h hpos
    omega
  have hge : 1 < Nat.card f.range := by
    rw [Subgroup.one_lt_card_iff_ne_bot, Ne, Subgroup.eq_bot_iff_forall]
    push Not
    obtain ⟨v, hv, hne⟩ := hns
    refine ⟨f ⟨v, hv⟩, ⟨⟨v, hv⟩, rfl⟩, ?_⟩
    rw [hf, Ne, commutatorElement_eq_one_iff_mul_comm]
    exact fun h => hne h.symm
  omega

theorem le_normalizer_inf_centralizer {W V : Subgroup G} (hW : W ≤ Subgroup.normalizer (V : Set G)) :
    W ≤ Subgroup.normalizer ((W ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := by
  have key : ∀ g ∈ W, ∀ x ∈ W ⊓ Subgroup.centralizer (V : Set G),
      g * x * g⁻¹ ∈ W ⊓ Subgroup.centralizer (V : Set G) := by
    intro g hg x hx
    refine ⟨W.mul_mem (W.mul_mem hg hx.1) (W.inv_mem hg), Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro v hv
    have hv' : g⁻¹ * v * g ∈ V := by
      have := (Subgroup.mem_normalizer_iff.mp (hW (W.inv_mem hg)) v).mp hv
      simpa using this
    have h := Subgroup.mem_centralizer_iff.mp hx.2 _ hv'
    calc v * (g * x * g⁻¹) = g * ((g⁻¹ * v * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * v * g)) * g⁻¹ := by rw [h]
      _ = _ := by group
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key g hg x hx, fun hx => ?_⟩
  have h := key g⁻¹ (W.inv_mem hg) _ hx
  have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
  rwa [e] at h

end Aux

section Main

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding

theorem eightEightTransvection : EightEightTransvection := by
  intro G _ _ X S L hX hA hL _ hSO
  obtain ⟨s, hsS, hS, hs2, hsL⟩ := hSO
  have hSL := Coordinator.le_normalizer_of_isWeakSBlock hX hA hL
  obtain ⟨A, hAmax, hAQ⟩ := Coordinator.exists_isMaxElemAbelian_not_le hA hL hSL
  have hAS : A ≤ S := hAmax.1
  have hA1 := Coordinator.not_le_centralizer_blockV_of_not_le hA hL hSL hAS hAQ
  have hV : IsElemAbelian 2 (blockV S L) :=
    CFSG.AGLEmbedding.isElemAbelian_omegaOneCenterOf (pCoreOf 2 (L ⊔ S))
  have hVS := Coordinator.blockV_le hA hL hSL
  have hVN : L ⊔ S ≤ Subgroup.normalizer (blockV S L : Set G) :=
    AscTenThree.le_normalizer_omegaOneCenterOf_twoCore (L ⊔ S)
  have hCn := le_normalizer_inf_centralizer hVN
  have hsn := hCn (Subgroup.mem_sup_right hsS)
  have hdich : ∀ b ∈ S, b ∈ (L ⊔ S) ⊓ Subgroup.centralizer (blockV S L : Set G) ∨
      ∃ c ∈ (L ⊔ S) ⊓ Subgroup.centralizer (blockV S L : Set G), b = s * c :=
    fun b hb => mem_or_exists_of_mem_zpowers_sup hsn hs2 (hS hb)
  have hCle : (L ⊔ S) ⊓ Subgroup.centralizer (blockV S L : Set G) ≤
      Subgroup.centralizer (blockV S L : Set G) := inf_le_right
  obtain ⟨a, haA, haV⟩ : ∃ a ∈ A, a ∉ Subgroup.centralizer (blockV S L : Set G) := by
    by_contra h
    push Not at h
    exact hA1 h
  obtain ⟨c0, hc0, hac⟩ := (hdich a (hAS haA)).resolve_left fun h => haV h.2
  have hidx : ∀ b ∈ A, b ∈ Subgroup.centralizer (blockV S L : Set G) ∨
      a⁻¹ * b ∈ Subgroup.centralizer (blockV S L : Set G) := by
    intro b hb
    rcases hdich b (hAS hb) with h | ⟨c, hc, rfl⟩
    · exact Or.inl h.2
    · refine Or.inr ?_
      have : a⁻¹ * (s * c) = c0⁻¹ * c := by rw [hac]; group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hCle hc0)) (hCle hc)
  have hrel : ((A ⊓ Subgroup.centralizer (blockV S L : Set G)).relIndex A) ≤ 2 := by
    unfold Subgroup.relIndex Subgroup.index
    have hsurj : Function.Surjective (fun i : Bool =>
        (QuotientGroup.mk (if i then (⟨a, haA⟩ : A) else 1) :
          A ⧸ (A ⊓ Subgroup.centralizer (blockV S L : Set G)).subgroupOf A)) := by
      intro q
      induction q using QuotientGroup.induction_on with | _ b =>
      rcases hidx b b.2 with h | h
      · refine ⟨false, ?_⟩
        simp only [Bool.false_eq_true, ite_false]
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        exact ⟨by simp, by simpa using h⟩
      · refine ⟨true, ?_⟩
        simp only [ite_true]
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        exact ⟨A.mul_mem (A.inv_mem haA) b.2, h⟩
    calc _ ≤ Nat.card Bool := Nat.card_le_card_of_surjective _ hsurj
      _ = 2 := by simp
  have hoff := CFSG.Quasithin.card_le_relIndex_mul_card hV hVS hAmax
  have hsub : (blockV S L ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) ≤
      blockV S L ⊓ Subgroup.centralizer ({s} : Set G) := by
    rintro v ⟨hv, hvA⟩
    refine ⟨hv, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have h1 : a * v = v * a := Subgroup.mem_centralizer_iff.mp hvA a haA
    have h2 : v * c0 = c0 * v := Subgroup.mem_centralizer_iff.mp (hCle hc0) v hv
    rw [hac] at h1
    have h3 : v * s * c0 = s * v * c0 := by
      calc v * s * c0 = v * (s * c0) := by group
        _ = s * c0 * v := h1.symm
        _ = s * (c0 * v) := by group
        _ = s * (v * c0) := by rw [h2]
        _ = s * v * c0 := by group
    exact mul_right_cancel h3
  have hcard : Nat.card (blockV S L) ≤ 2 * Nat.card ↥(blockV S L ⊓
      Subgroup.centralizer ({s} : Set G)) :=
    hoff.trans ((Nat.mul_le_mul hrel (Subgroup.card_le_of_le hsub)))
  have := hV.1
  have hns : ∃ v ∈ blockV S L, s * v ≠ v * s := by
    by_contra h
    push Not at h
    apply hsL
    refine Subgroup.mem_sup_right ⟨Subgroup.mem_sup_right hsS, ?_⟩
    exact Subgroup.mem_centralizer_iff.mpr fun v hv => (h v hv).symm
  refine ⟨s, hsS, hS, hsL, card_commutator_zpowers_eq_two (blockV S L) s
    (fun v hv w hw => setLike_mul_comm hv hw)
    (fun v hv => (Subgroup.mem_normalizer_iff.mp (hVN (Subgroup.mem_sup_right hsS)) v).mp hv)
    (fun v hv => (Subgroup.mem_centralizer_iff.mp (hCle hs2) v hv).symm) hns hcard⟩

end Main

end CFSG.HardMathSupport.Cooperstein.StructureLie
