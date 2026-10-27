module

public import CFSG.ClassicalInvolution.Balance.TheoremQNormalizer
public import CFSG.ClassicalInvolution.Generic.Frame
public import CFSG.ClassicalInvolution.Reduction
import CFSG.ClassicalInvolution.PerfectCase.Basic

public section

namespace CFSG.ClassicalInvolution

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Balance
open scoped commutatorElement MatrixGroups

section Predicate

variable {G : Type*} [Group G]

theorem conjInvariant_conjugateSet (J : Subgroup G) : ConjInvariant (conjugateSet J) := by
  rintro n K ⟨g, rfl⟩
  refine ⟨g * n⁻¹, ?_⟩
  show (J.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj n).toMonoidHom = _
  rw [map_map_conj]
  simp

@[expose] def HasEFrameRank4 (J : Subgroup G) : Prop :=
  ∃ (F : Type) (_ : Field F) (E : Subgroup G),
    ToralFrame F (conjugateSet J) E (sigmaSet F (conjugateSet J) E) ∧
    NonCommConnected (sigmaSet F (conjugateSet J) E) ∧
    IsSaturated F (conjugateSet J) (sigmaSet F (conjugateSet J) E) ∧ 16 ≤ Nat.card E

end Predicate

section Closure

variable {G : Type*} [Group G]

theorem closure_pair_subset {a b : G} (hab : a * b = b * a) (ha : a * a = 1) (hb : b * b = 1) :
    (Subgroup.closure ({a, b} : Set G) : Set G) ⊆ {1, a, b, a * b} := by
  have hba : b * a = a * b := hab.symm
  have h1 : a * b * a = b := by rw [mul_assoc, hba, ← mul_assoc, ha, one_mul]
  have h2 : a * b * b = a := by rw [mul_assoc, hb, mul_one]
  have h3 : a * (a * b) = b := by rw [← mul_assoc, ha, one_mul]
  have h4 : b * (a * b) = a := by rw [← mul_assoc, hba, mul_assoc, hb, mul_one]
  have h5 : a * b * (a * b) = 1 := by
    rw [mul_assoc, ← mul_assoc b, hba, ← mul_assoc, ← mul_assoc, ha, one_mul, hb]
  have hia : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hib : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hiab : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right h5
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx => rcases hx with rfl | rfl <;> simp
  | one => simp
  | mul x y _ _ hx hy =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy ⊢
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      simp only [ha, hb, hba, h1, h2, h3, h4, h5, one_mul, mul_one, true_or, or_true]
  | inv x _ hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with rfl | rfl | rfl | rfl <;>
      simp only [inv_one, hia, hib, hiab, true_or, or_true]

theorem card_closure_pair_le {a b : G} (hab : a * b = b * a) (ha : a * a = 1) (hb : b * b = 1) :
    Nat.card (Subgroup.closure ({a, b} : Set G)) ≤ 4 := by
  classical
  have hsub := closure_pair_subset hab ha hb
  have h1 : Nat.card (Subgroup.closure ({a, b} : Set G)) =
      ((Subgroup.closure ({a, b} : Set G) : Set G)).ncard := Nat.card_coe_set_eq _
  rw [h1]
  refine (Set.ncard_le_ncard hsub (Set.toFinite _)).trans ?_
  have h2 : ({1, a, b, a * b} : Set G) = ↑({1, a, b, a * b} : Finset G) := by simp
  rw [h2, Set.ncard_coe_finset]
  exact Finset.card_le_four

theorem isPGroup_two_of_mul_self_eq_one {H : Subgroup G} (h : ∀ x ∈ H, x * x = 1) :
    IsPGroup 2 H := by
  intro x
  refine ⟨1, ?_⟩
  apply Subtype.ext
  simpa [pow_two] using h x x.2

theorem exists_card_eight_of_isElemAbelian [Finite G] {L : Subgroup G} (hL : IsElemAbelian 2 L)
    (h8 : 8 ≤ Nat.card L) {a b : G} (ha : a ∈ L) (hb : b ∈ L) :
    ∃ E₀ : Subgroup G, E₀ ≤ L ∧ IsElemAbelian 2 E₀ ∧ Nat.card E₀ = 8 ∧ a ∈ E₀ ∧ b ∈ E₀ := by
  have hsq : ∀ x ∈ L, x * x = 1 := fun x hx => by
    have := hL.2 x hx
    rwa [pow_two] at this
  obtain ⟨m, hm⟩ := (isPGroup_two_of_mul_self_eq_one hsq).exists_card_eq
  have h8L : 2 ^ 3 ∣ Nat.card L := by
    rw [hm] at h8 ⊢
    refine Nat.pow_dvd_pow 2 ?_
    by_contra hlt
    have : 2 ^ m ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hab : a * b = b * a := congrArg Subtype.val (hL.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  set V : Subgroup G := Subgroup.closure ({a, b} : Set G) with hV
  have hVL : V ≤ L := by
    rw [hV, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact ha
    · exact hb
  have hV8 : Nat.card V ∣ 2 ^ 3 := by
    obtain ⟨k, hk⟩ := (isPGroup_two_of_mul_self_eq_one fun x hx => hsq x (hVL hx)).exists_card_eq
    have h4 : Nat.card V ≤ 4 := card_closure_pair_le hab (hsq a ha) (hsq b hb)
    rw [hk] at h4 ⊢
    refine Nat.pow_dvd_pow 2 ?_
    by_contra hlt
    have : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨E₀, hcard, hVE₀, hE₀L⟩ :=
    Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_two hV8 h8L hVL
  exact ⟨E₀, hE₀L, CFSG.SignalizerFunctor.Helpers.elementary_abelian_of_le 2 hL hE₀L,
    by rw [hcard]; norm_num, hVE₀ (Subgroup.subset_closure (by simp)),
    hVE₀ (Subgroup.subset_closure (by simp))⟩

theorem exists_card_eight_of_relIndex_two [Finite G] {A L : Subgroup G} (hA : IsElemAbelian 2 A)
    (hLA : L ≤ A) (hrel : L.relIndex A = 2) (h16 : 16 ≤ Nat.card A) {a b : G} (ha : a ∈ L)
    (hb : b ∈ L) :
    ∃ E₀ : Subgroup G, E₀ ≤ L ∧ IsElemAbelian 2 E₀ ∧ Nat.card E₀ = 8 ∧ a ∈ E₀ ∧ b ∈ E₀ := by
  have hAL : Nat.card A = 2 * Nat.card L := by
    have h1 := (L.subgroupOf A).card_mul_index
    rw [Subgroup.relIndex] at hrel
    rw [hrel, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLA).toEquiv] at h1
    omega
  exact exists_card_eight_of_isElemAbelian
    (CFSG.SignalizerFunctor.Helpers.elementary_abelian_of_le 2 hA hLA) (by omega) ha hb

end Closure

section Frame

variable {G : Type*} [Group G] {F : Type*} [Field F] {Ω : Set (Subgroup G)} {E : Subgroup G}
  {S : Set (Subgroup G)}

theorem toralFrame_mul_comm (Fr : ToralFrame F Ω E S) {x y : G} (hx : x ∈ E) (hy : y ∈ E) :
    x * y = y * x := by
  have h1 := Fr.elem (x * y) (E.mul_mem hx hy)
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right (Fr.elem x hx)
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right (Fr.elem y hy)
  have hxyi : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right h1
  calc x * y = (x * y)⁻¹ := hxyi.symm
    _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
    _ = y * x := by rw [hxi, hyi]

theorem toralFrame_isElemAbelian (Fr : ToralFrame F Ω E S) : IsElemAbelian 2 E :=
  ⟨⟨⟨fun x y => Subtype.ext (toralFrame_mul_comm Fr x.2 y.2)⟩⟩, fun x hx => by
    rw [pow_two]
    exact Fr.elem x hx⟩

theorem toralFrame_isQuasisimple (Fr : ToralFrame F Ω E S) {L : Subgroup G} (hL : L ∈ S) :
    CFSG.Open.IsQuasisimple L := by
  have := Fr.finite
  obtain ⟨φ, rfl, hD⟩ := Fr.inSigma hL
  have h4 : 4 ≤ Nat.card F := by have := Fr.five; omega
  let e : SL(2, F) ≃* φ.range := MonoidHom.ofInjective hD.inj
  exact Components.quasisimple_of_equiv e.symm (isQuasisimple_specialLinearGroup_two h4)

theorem commutator_eq_top_of_mem_frame (Fr : ToralFrame F Ω E S) {L : Subgroup G} (hL : L ∈ S) :
    commutator L = ⊤ :=
  (toralFrame_isQuasisimple Fr hL).1

theorem ne_bot_of_mem_frame (Fr : ToralFrame F Ω E S) {L : Subgroup G} (hL : L ∈ S) : L ≠ ⊥ := by
  have : Nontrivial L := Quasisimple.nontrivial (toralFrame_isQuasisimple Fr hL)
  exact (Subgroup.nontrivial_iff_ne_bot L).mp this

section Finite

variable [Finite G]

theorem isQuasisimple_oddCoreQuotient_of_mem_frame (Fr : ToralFrame F Ω E S) {L : Subgroup G}
    (hL : L ∈ S) :
    CFSG.Open.IsQuasisimple (L ⧸ componentClassificationOddCore L) := by
  have hq := toralFrame_isQuasisimple Fr hL
  exact Quasisimple.central_quotient hq _ (oddCore_le_center_of_isQuasisimple hq)

theorem exists_card_eight_of_frame (Fr : ToralFrame F Ω E S) (h16 : 16 ≤ Nat.card E)
    {L₀ : Subgroup G} (hL₀ : L₀ ∈ S) {z₀ t : G} (hz₀ : IsUniqueInvolution L₀ z₀)
    (ht : t ∈ axisSub E L₀) :
    ∃ E₀ : Subgroup G, E₀ ≤ axisSub E L₀ ∧ IsElemAbelian 2 E₀ ∧ Nat.card E₀ = 8 ∧ z₀ ∈ E₀ ∧
      t ∈ E₀ := by
  have := Fr.finite
  have hrel : (axisSub E L₀).relIndex E = 2 := by
    obtain ⟨φ, rfl, hD⟩ := Fr.inSigma hL₀
    exact hD.index_two
  exact exists_card_eight_of_relIndex_two (toralFrame_isElemAbelian Fr) inf_le_left hrel h16
    ((Fr.inSigma hL₀).unique_involution_mem_axis Fr.odd hz₀) ht

theorem exists_data_of_frame (Fr : ToralFrame F Ω E S) (h16 : 16 ≤ Nat.card E)
    {L₀ : Subgroup G} (hL₀ : L₀ ∈ S) {z₀ : G} (hz₀ : IsUniqueInvolution L₀ z₀) :
    ∃ (t : G) (E₀ : Subgroup G), E₀ ≤ axisSub E L₀ ∧ IsElemAbelian 2 E₀ ∧ Nat.card E₀ = 8 ∧
      z₀ ∈ E₀ ∧ t ∈ E₀ ∧ t ≠ 1 ∧ t ≠ z₀ := by
  have := Fr.finite
  have hz₀L : z₀ ∈ axisSub E L₀ := (Fr.inSigma hL₀).unique_involution_mem_axis Fr.odd hz₀
  obtain ⟨E₀, hE₀L, hE₀, hcard, hz₀E, -⟩ := exists_card_eight_of_frame Fr h16 hL₀ hz₀ hz₀L
  by_contra hcon
  push Not at hcon
  have hsub : (E₀ : Set G) ⊆ {1, z₀} := by
    intro x hx
    by_cases h1 : x = 1
    · simp [h1]
    · right
      exact hcon x E₀ hE₀L hE₀ hcard hz₀E hx h1
  have h2 : Nat.card E₀ ≤ 2 := by
    have h1 : Nat.card E₀ = (E₀ : Set G).ncard := Nat.card_coe_set_eq _
    rw [h1]
    refine (Set.ncard_le_ncard hsub (Set.toFinite _)).trans ?_
    exact (Set.ncard_insert_le _ _).trans (by simp)
  omega

theorem HasEFrameRank4.exists_data {J : Subgroup G} (h : HasEFrameRank4 J) :
    ∃ (E E₀ L₀ : Subgroup G) (z₀ t : G), L₀ ∈ conjugateSet J ∧ IsUniqueInvolution L₀ z₀ ∧
      16 ≤ Nat.card E ∧ IsElemAbelian 2 E ∧ E₀ ≤ E ∧ IsElemAbelian 2 E₀ ∧ Nat.card E₀ = 8 ∧
      z₀ ∈ E₀ ∧ t ∈ E₀ ∧ t ≠ 1 ∧ t ≠ z₀ ∧ L₀ ≤ Subgroup.centralizer (E₀ : Set G) ∧
      commutator L₀ = ⊤ ∧ L₀ ≠ ⊥ ∧
      CFSG.Open.IsQuasisimple (L₀ ⧸ componentClassificationOddCore L₀) := by
  obtain ⟨F, _, E, Fr, -, -, h16⟩ := h
  obtain ⟨L₀, hL₀, -⟩ := Fr.exists_ne
  obtain ⟨z₀, hz₀⟩ := Fr.exists_isUniqueInvolution hL₀
  obtain ⟨t, E₀, hE₀L, hE₀, hcard, hz₀E, htE, ht1, htz⟩ := exists_data_of_frame Fr h16 hL₀ hz₀
  refine ⟨E, E₀, L₀, z₀, t, Fr.subset hL₀, hz₀, h16, toralFrame_isElemAbelian Fr,
    hE₀L.trans inf_le_left, hE₀, hcard, hz₀E, htE, ht1, htz, fun l hl => ?_,
    commutator_eq_top_of_mem_frame Fr hL₀, ne_bot_of_mem_frame Fr hL₀,
    isQuasisimple_oddCoreQuotient_of_mem_frame Fr hL₀⟩
  rw [Subgroup.mem_centralizer_iff]
  intro e he
  exact ((mem_axisSub_iff.mp (hE₀L he)).2 l hl).symm

end Finite

end Frame

section Application

variable {G : Type} [Group G] [Finite G] {F : Type*} [Field F] {Ω : Set (Subgroup G)}
  {E : Subgroup G} {S : Set (Subgroup G)}

theorem isQuasisimple_of_frame (Fr : ToralFrame F Ω E S) (h16 : 16 ≤ Nat.card E)
    (hΔ : ∀ Φ ∈ signalizerFunctorEk 2 2 E, deltaCore Φ = ⊥)
    {L₀ : Subgroup G} (hL₀ : L₀ ∈ S) {z₀ t : G} (hz₀ : IsUniqueInvolution L₀ z₀)
    (hsub : IsSubnormal L₀ (Subgroup.centralizer ({z₀} : Set G)))
    (ht : t ∈ axisSub E L₀) {K : Subgroup G} (hKC : K ≤ Subgroup.centralizer ({t} : Set G))
    (hK : TwoComponents.IsTwoComponent (K.subgroupOf (Subgroup.centralizer ({t} : Set G))))
    (hL₀K : L₀ ≤ K)
    (hB : ∀ f ∈ axisSub E L₀, f ≠ 1 →
      ∀ M : Subgroup ↥(imageModOddCore f (Subgroup.centralizer {t} ⊓ Subgroup.centralizer {f})),
        TwoComponents.IsTwoComponent M → CFSG.Open.IsQuasisimple M ∨
          ⁅M.map (imageModOddCore f (Subgroup.centralizer {t} ⊓ Subgroup.centralizer {f})).subtype,
            imageModOddCore f L₀⁆ = ⊥) :
    CFSG.Open.IsQuasisimple K := by
  obtain ⟨E₀, hE₀L, hE₀, hcard, hz₀E, htE⟩ := exists_card_eight_of_frame Fr h16 hL₀ hz₀ ht
  have hE₀E : E₀ ≤ E := hE₀L.trans inf_le_left
  have hE₀C : E₀ ≤ Subgroup.centralizer ({t} : Set G) := fun e he => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact toralFrame_mul_comm Fr (hE₀E he) (hE₀E htE)
  have hL₀E : L₀ ≤ Subgroup.centralizer (E₀ : Set G) := fun l hl => by
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact ((mem_axisSub_iff.mp (hE₀L he)).2 l hl).symm
  have hL₀t : L₀ ≤ Subgroup.centralizer ({t} : Set G) := fun l hl => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (mem_axisSub_iff.mp ht).2 l hl
  exact isQuasisimple_of_isTwoComponent_of_layer_of_centralizes hKC hK hE₀C hE₀ hcard hL₀K hL₀E
    (commutator_eq_top_of_mem_frame Fr hL₀) (ne_bot_of_mem_frame Fr hL₀)
    (deltaCore_eq_bot_of_le hE₀E hΔ)
    (isSubnormal_inf_centralizer_of_isSubnormal hz₀E (le_inf hL₀t hL₀E) hsub)
    (isQuasisimple_oddCoreQuotient_of_mem_frame Fr hL₀) fun f hf hf1 => hB f (hE₀L hf) hf1

theorem isQuasisimple_of_frame_of_bInclusion (Fr : ToralFrame F Ω E S) (h16 : 16 ≤ Nat.card E)
    (hΔ : ∀ Φ ∈ signalizerFunctorEk 2 2 E, deltaCore Φ = ⊥)
    {L₀ : Subgroup G} (hL₀ : L₀ ∈ S) {z₀ t : G} (hz₀ : IsUniqueInvolution L₀ z₀)
    (hsub : IsSubnormal L₀ (Subgroup.centralizer ({z₀} : Set G)))
    (ht : t ∈ axisSub E L₀) (ht1 : t ≠ 1) {K : Subgroup G}
    (hKC : K ≤ Subgroup.centralizer ({t} : Set G))
    (hK : TwoComponents.IsTwoComponent (K.subgroupOf (Subgroup.centralizer ({t} : Set G))))
    (hL₀K : L₀ ≤ K)
    (hinc : ∀ f ∈ axisSub E L₀, f ≠ 1 → CentralTwoBInclusion.Property
      (↥(Subgroup.centralizer {f}) ⧸ componentClassificationOddCore ↥(Subgroup.centralizer {f}))) :
    CFSG.Open.IsQuasisimple K := by
  obtain ⟨E₀, hE₀L, hE₀, hcard, hz₀E, htE⟩ := exists_card_eight_of_frame Fr h16 hL₀ hz₀ ht
  have hE₀E : E₀ ≤ E := hE₀L.trans inf_le_left
  have hL₀E : L₀ ≤ Subgroup.centralizer (E₀ : Set G) := fun l hl => by
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact ((mem_axisSub_iff.mp (hE₀L he)).2 l hl).symm
  have hL₀t : L₀ ≤ Subgroup.centralizer ({t} : Set G) := fun l hl => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (mem_axisSub_iff.mp ht).2 l hl
  exact isQuasisimple_of_isTwoComponent_of_bInclusion_of_centralizes htE ht1 hKC hK hE₀ hcard hL₀K
    hL₀E (commutator_eq_top_of_mem_frame Fr hL₀) (ne_bot_of_mem_frame Fr hL₀)
    (deltaCore_eq_bot_of_le hE₀E hΔ)
    (isSubnormal_inf_centralizer_of_isSubnormal hz₀E (le_inf hL₀t hL₀E) hsub)
    (isQuasisimple_oddCoreQuotient_of_mem_frame Fr hL₀) fun f hf hf1 => hinc f (hE₀L hf) hf1

theorem isQuasisimple_of_frame_of_twoBalancedWrt (Fr : ToralFrame F Ω E S)
    (h16 : 16 ≤ Nat.card E) (hB2 : TwoBalancedWrt E)
    (hO : componentClassificationOddCore G = ⊥) (hGen : FusionGenerated E)
    {L₀ : Subgroup G} (hL₀ : L₀ ∈ S) {z₀ t : G} (hz₀ : IsUniqueInvolution L₀ z₀)
    (hsub : IsSubnormal L₀ (Subgroup.centralizer ({z₀} : Set G)))
    (ht : t ∈ axisSub E L₀) {K : Subgroup G} (hKC : K ≤ Subgroup.centralizer ({t} : Set G))
    (hK : TwoComponents.IsTwoComponent (K.subgroupOf (Subgroup.centralizer ({t} : Set G))))
    (hL₀K : L₀ ≤ K)
    (hB : ∀ f ∈ axisSub E L₀, f ≠ 1 →
      ∀ M : Subgroup ↥(imageModOddCore f (Subgroup.centralizer {t} ⊓ Subgroup.centralizer {f})),
        TwoComponents.IsTwoComponent M → CFSG.Open.IsQuasisimple M ∨
          ⁅M.map (imageModOddCore f (Subgroup.centralizer {t} ⊓ Subgroup.centralizer {f})).subtype,
            imageModOddCore f L₀⁆ = ⊥) :
    CFSG.Open.IsQuasisimple K :=
  isQuasisimple_of_frame Fr h16
    (fun Φ hΦ => deltaCore_eq_bot_of_fusionGenerated (toralFrame_isElemAbelian Fr) h16 hB2 hO hGen
      Φ hΦ) hL₀ hz₀ hsub ht hKC hK hL₀K hB

theorem isQuasisimple_of_frame_of_twoBalancedWrt_of_bInclusion (Fr : ToralFrame F Ω E S)
    (h16 : 16 ≤ Nat.card E) (hB2 : TwoBalancedWrt E)
    (hO : componentClassificationOddCore G = ⊥) (hGen : FusionGenerated E)
    {L₀ : Subgroup G} (hL₀ : L₀ ∈ S) {z₀ t : G} (hz₀ : IsUniqueInvolution L₀ z₀)
    (hsub : IsSubnormal L₀ (Subgroup.centralizer ({z₀} : Set G)))
    (ht : t ∈ axisSub E L₀) (ht1 : t ≠ 1) {K : Subgroup G}
    (hKC : K ≤ Subgroup.centralizer ({t} : Set G))
    (hK : TwoComponents.IsTwoComponent (K.subgroupOf (Subgroup.centralizer ({t} : Set G))))
    (hL₀K : L₀ ≤ K)
    (hinc : ∀ f ∈ axisSub E L₀, f ≠ 1 → CentralTwoBInclusion.Property
      (↥(Subgroup.centralizer {f}) ⧸ componentClassificationOddCore ↥(Subgroup.centralizer {f}))) :
    CFSG.Open.IsQuasisimple K :=
  isQuasisimple_of_frame_of_bInclusion Fr h16
    (fun Φ hΦ => deltaCore_eq_bot_of_fusionGenerated (toralFrame_isElemAbelian Fr) h16 hB2 hO hGen
      Φ hΦ) hL₀ hz₀ hsub ht ht1 hKC hK hL₀K hinc

end Application

end CFSG.ClassicalInvolution
