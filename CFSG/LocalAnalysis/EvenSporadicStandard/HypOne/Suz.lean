module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.SuzTransport
public import CFSG.Sporadic.SmallOddCore.TableFacts
public import CFSG.Sporadic.SuzOddCore.OddCore
public import CFSG.Sporadic.SuzOddCore.SmallAut
public import Certificates.Certificate24432

public section

namespace CFSG.EvenSporadicStandard.HypOne.Suz

open CFSG.Blueprint CFSG.Blueprint.NativeSporadic Subgroup
open CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977
open CFSG.ComponentClassification.M12Cover CFSG.Sporadic.Schreier
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore (AutModel tp rep_tp rep_invT commTT_iff co2Rep_natArr_iff
  rep_arrayMap_ofNat)
open CFSG.Sporadic.SuzOddCore (suzM suzT suzV suzInv suzEquivM suzConjT suzConjT_apply
  suzConjT_bijective suzConjT_injective suzT_conj_mem_suzM suzM_le_suzT suzM_centralizer
  suzT_card suzM_card_chain suzT_semidirect suzV_sq suzV_conj_mem mem_suzT_iff suzInv_mem_suzT
  rep_suzInv rep_v inM_iff invT_check suzT_involution_class suzM_involution_class invD invE
  invD_not_le_M invD_eq_centT invE_eq_centM card_invD card_invE centT centM invFullOrders
  invInnerOrders CTUC_Suz_all_involution_centralizers_odd_core_free)

theorem mem_suzM_of_siftM
    {T : Table} {g : Equiv.Perm (Fin 1782)} (hT : Rep 1782 T g) (h : siftM T = true) :
    g ∈ suzM :=
  (inM_iff (co2Rep_natArr_iff.2 hT)).1 h

theorem suz_index_two :
    ∀ x ∈ suzT, x ∉ suzM → ∀ y ∈ suzT, y ∉ suzM → x⁻¹ * y ∈ suzM := by
  rw [← suzT_semidirect.2]
  exact index_two_of_normalizing (by rw [sq]; exact suzV_sq) fun p hp => suzV_conj_mem hp

theorem exists_comm_not_mem
    {i : ℕ} (hi : i < 4) :
    ∃ z ∈ suzT, z ∉ suzM ∧ z * suzInv i = suzInv i * z := by
  obtain ⟨z, hz, hzM⟩ := IsConcreteLE.not_le_iff_exists.1 (invD_not_le_M hi)
  rw [invD_eq_centT hi, centT, mem_inf, mem_centralizer_singleton_iff] at hz
  exact ⟨z, hz.2, hzM, hz.1⟩

theorem exists_suzM_conj
    {i : ℕ} (hi : i < 4)
    {c : Equiv.Perm (Fin 1782)} (hc : c ∈ suzT) :
    ∃ g ∈ suzM, c * suzInv i * c⁻¹ = g * suzInv i * g⁻¹ := by
  obtain ⟨z, hz, hzM, hzt⟩ := exists_comm_not_mem hi
  exact exists_conj_of_index_two suz_index_two hz hzM hzt hc

theorem cover_suzM :
    ∀ v ∈ suzM, orderOf v = 2 → ∃ r ∈ [suzInv 0, suzInv 1], ∃ c ∈ suzM, v = c * r * c⁻¹ := by
  intro v hv h2
  obtain ⟨c, hc, h | h⟩ := suzM_involution_class hv h2
  · obtain ⟨g, hg, e⟩ := exists_suzM_conj (i := 0) (by norm_num) hc
    exact ⟨suzInv 0, List.mem_cons_self, g, hg, by rw [← h, e]⟩
  · obtain ⟨g, hg, e⟩ := exists_suzM_conj (i := 1) (by norm_num) hc
    exact ⟨suzInv 1, by simp, g, hg, by rw [← h, e]⟩

theorem cover_suzT :
    ∀ v ∈ suzT, orderOf v = 2 → ∃ r ∈ [suzInv 0, suzInv 1, suzInv 2, suzInv 3],
      ∃ c ∈ suzT, v = c * r * c⁻¹ := by
  intro v hv h2
  obtain ⟨i, ⟨hi, c, hc, e⟩, -⟩ := suzT_involution_class hv h2
  refine ⟨suzInv i, ?_, c, hc, e.symm⟩
  interval_cases i <;> simp

theorem card_centralizerIn_suzM
    {i : ℕ} (hi : i < 4) :
    Nat.card ↥(centralizerIn suzM (suzInv i)) = invInnerOrders.getD i 0 := by
  rw [show centralizerIn suzM (suzInv i) = invE i by
    rw [invE_eq_centM hi, centM, centralizerIn, inf_comm], card_invE hi]

theorem fourClassesLarge_rows :
    (∀ v ∈ suzM, orderOf v = 2 → FourClassesLarge ↥(centralizerIn suzM v)) ∧
      ∀ v ∈ suzT, orderOf v = 2 → FourClassesLarge ↥(centralizerIn suzT v) := by
  obtain ⟨fM0, fM1, fT, -, -⟩ := Certificates.certificate24432
  have fT0 := fT 0 (by norm_num)
  have fT1 := fT 1 (by norm_num)
  have fT2 := fT 2 (by norm_num)
  have fT3 := fT 3 (by norm_num)
  refine ⟨fourClassesLarge_centralizerIn_of_reps suzM _ cover_suzM fun r hr => ?_,
    fourClassesLarge_centralizerIn_of_reps suzT _ cover_suzT fun r hr => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact fM0
    · exact fM1
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact fT0
    · exact fT1
    · exact fT2
    · exact fT3

theorem center_suzM :
    Subgroup.center suzM = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have : (z : Equiv.Perm (Fin 1782)) ∈
      Subgroup.centralizer (suzM : Set (Equiv.Perm (Fin 1782))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨g, hg⟩)
  rw [suzM_centralizer, Subgroup.mem_bot] at this
  exact Subgroup.mem_bot.2 (Subtype.ext this)

theorem autModel :
    AutModel suzM suzT where
  le := suzM_le_suzT
  conj_mem := fun _ hx _ hp => suzT_conj_mem_suzM hx hp
  surj := fun α => by
    obtain ⟨t, ht⟩ := suzConjT_bijective.2 α
    refine ⟨t, t.2, fun p => ?_⟩
    have := congrArg (fun β : MulAut suzM => ((β p : suzM) : Equiv.Perm (Fin 1782))) ht
    simpa [suzConjT_apply] using this.symm
  inj := fun x hx hc => by
    have h1 : suzConjT ⟨x, hx⟩ = suzConjT 1 := by
      refine MulEquiv.ext fun m => Subtype.ext ?_
      have h2 : x * (m : Equiv.Perm (Fin 1782)) * x⁻¹ = (m : Equiv.Perm (Fin 1782)) := by
        rw [hc m m.2]
        group
      rw [suzConjT_apply, map_one, MulAut.one_apply]
      exact h2
    exact congrArg Subtype.val (suzConjT_injective h1)

@[expose] noncomputable def autEquiv :
    suzT ≃* MulAut suzM :=
  MulEquiv.ofBijective suzConjT suzConjT_bijective

theorem autEquiv_apply
    (x : suzT) (p : suzM) :
    ((autEquiv x p : suzM) : Equiv.Perm (Fin 1782)) = x * p * (x : Equiv.Perm (Fin 1782))⁻¹ :=
  suzConjT_apply x p

theorem card_suzT_le :
    Nat.card suzT ≤ 2 * Nat.card suzM := by
  rw [suzT_card, suzM_card_chain]

theorem hypothesisOne_native :
    HypothesisOne NativeSporadic.Suz := by
  obtain ⟨hP, hR⟩ := fourClassesLarge_rows
  exact hypothesisOne_of_outTwo suzEquivM center_suzM autModel autEquiv card_suzT_le
    (fun τ hτ h2 => (CTUC_Suz_all_involution_centralizers_odd_core_free τ hτ h2).1) hP hR

theorem hasElemAbelianEight_native :
    HasElemAbelianEight NativeSporadic.Suz := by
  exact HasElemAbelianEight.of_mulEquiv suzEquivM.symm Certificates.certificate24432.2.2.2.1

theorem cover_outer
    {τ : Equiv.Perm (Fin 1782)} (hτ : τ ∈ suzT) (h2 : orderOf τ = 2) (hτM : τ ∉ suzM) :
    ∃ i, (i = 2 ∨ i = 3) ∧ ∃ g ∈ suzM, τ = g * suzInv i * g⁻¹ := by
  obtain ⟨i, ⟨hi, c, hc, e⟩, -⟩ := suzT_involution_class hτ h2
  have hiM : suzInv i ∉ suzM := fun h => hτM (e ▸ suzT_conj_mem_suzM hc h)
  obtain ⟨g, hg, e'⟩ := exists_suzM_conj hi hc
  refine ⟨i, ?_, g, hg, by rw [← e, e']⟩
  have h0 : suzInv 0 ∈ suzM := (inM_iff (rep_suzInv (by norm_num))).1 invT_check.2.1
  have h1 : suzInv 1 ∈ suzM := (inM_iff (rep_suzInv (by norm_num))).1 invT_check.2.2.1
  interval_cases i
  · exact absurd h0 hiM
  · exact absurd h1 hiM
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem foursGroupCondition_native :
    CFSG.EvenSmallLie.FoursGroupCondition NativeSporadic.Suz := by
  have hw := Certificates.certificate24432.2.2.2.2
  obtain ⟨l2, hl2, hl2'⟩ := hw 2 List.mem_cons_self
  obtain ⟨l3, hl3, hl3'⟩ := hw 3 (by simp)
  refine foursGroupCondition_of_outTwo suzEquivM center_suzM suzM_le_suzT autEquiv
    autEquiv_apply [⟨suzInv 2, suzInv_mem_suzT 2⟩, ⟨suzInv 3, suzInv_mem_suzT 3⟩]
    (fun τ hτ hτM => ?_) (fun ρ hρ => ?_)
  · obtain ⟨i, hi | hi, g, hg, e⟩ := cover_outer τ.2 hτ hτM
    · exact ⟨⟨suzInv 2, suzInv_mem_suzT 2⟩, List.mem_cons_self, g, hg, hi ▸ e⟩
    · exact ⟨⟨suzInv 3, suzInv_mem_suzT 3⟩, by simp, g, hg, hi ▸ e⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hρ
    rcases hρ with rfl | rfl
    · exact ⟨l2, hl2, hl2'⟩
    · exact ⟨l3, hl3, hl3'⟩

theorem rowData_of_isSporadic
    {Y : Type} [Group Y] [Finite Y] (h : IsSporadic Y .Suz) : Finkelstein77.RowData Y := by
  obtain ⟨e⟩ := h
  have hI : HypothesisOne Y :=
    CFSG.EvenSmallLie.hypothesisOne_of_mulEquiv e.symm hypothesisOne_native
  exact rowData_of_hasElemAbelianEight hI
    (HasElemAbelianEight.of_mulEquiv e.symm hasElemAbelianEight_native)

theorem foursGroupCondition_of_isSporadic
    {Y : Type} [Group Y] (h : IsSporadic Y .Suz) : CFSG.EvenSmallLie.FoursGroupCondition Y := by
  obtain ⟨e⟩ := h
  exact CFSG.EvenSmallLie.FoursGroupCondition.of_mulEquiv e.symm foursGroupCondition_native

theorem fullRowData_of_isSporadic
    {Y : Type} [Group Y] [Finite Y] (h : IsSporadic Y .Suz) : FullRowData Y :=
  ⟨rowData_of_isSporadic h, foursGroupCondition_of_isSporadic h⟩

end CFSG.EvenSporadicStandard.HypOne.Suz
