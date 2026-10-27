module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodInner
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.SeitzRows.E8Five

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Foote.Coordinator.SplitFrame
  CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
  CFSG.HardMathSupport.Timmesfeld.LocalTwo.SeitzRows
open scoped MatrixGroups

theorem perfectCentralizerPlanes_of_twoFrames {G : Type} {M₁ M₂ : Type*}
    [Group G] [Group M₁] [Group M₂]
    [Finite G] [Finite M₁] [Finite M₂] {p : ℕ} [hp : Fact p.Prime]
    (ψA : M₁ →* G) (ψB : M₂ →* G) (hA : Function.Injective ψA) (hB : Function.Injective ψB)
    (hcomm : ∀ x y, Commute (ψA x) (ψB y))
    (hcycA : ∀ g : M₁, orderOf g = p → IsCyclic (Subgroup.centralizer ({g} : Set M₁)))
    (hcycB : ∀ g : M₂, orderOf g = p → IsCyclic (Subgroup.centralizer ({g} : Set M₂)))
    (hAB : ¬ p ∣ Nat.card ↥(ψA.range ⊓ ψB.range))
    (hcard : (Nat.card G).factorization p =
      (Nat.card M₁).factorization p + (Nat.card M₂).factorization p)
    (hperf₂ : Group.IsPerfect M₂) (hp₂ : p ∣ Nat.card M₂) :
    PerfectCentralizerPlanes p G := by
  intro E hE hEcard
  obtain ⟨g, a, b, ha, _, hEq⟩ :=
    exists_conj_plane_of_twoFrames ψA ψB hA hB hcomm hcycA hcycB hAB hcard E hE.2 hEcard
  have hmem : ψA a ∈ E.map (MulAut.conj g).toMonoidHom := by
    rw [hEq]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers (ψA a))
  obtain ⟨x, hxE, hx⟩ := Subgroup.mem_map.1 hmem
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [map_one] at hx
    have ha1 : a = 1 := hA (by simpa using hx.symm)
    exact hp.out.ne_one (by rw [← ha, ha1, orderOf_one])
  have hx'' : MulAut.conj g x = ψA a := hx
  have hx' : x = MulAut.conj g⁻¹ (ψA a) := by
    rw [← hx'']
    simp only [MulAut.conj_apply, inv_inv]
    group
  refine ⟨x, hxE, hx1, ψB.range.map (MulAut.conj g⁻¹).toMonoidHom, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hz
    obtain ⟨y, rfl⟩ := hw
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hy : Commute (ψA a) (ψB y) := hcomm a y
    calc MulAut.conj g⁻¹ (ψB y) * x
        = MulAut.conj g⁻¹ (ψB y) * MulAut.conj g⁻¹ (ψA a) := by rw [hx']
      _ = MulAut.conj g⁻¹ (ψB y * ψA a) := by rw [map_mul]
      _ = MulAut.conj g⁻¹ (ψA a * ψB y) := by rw [hy.eq]
      _ = MulAut.conj g⁻¹ (ψA a) * MulAut.conj g⁻¹ (ψB y) := by rw [map_mul]
      _ = x * MulAut.conj g⁻¹ (ψB y) := by rw [hx']
  · haveI : Group.IsPerfect M₂ := hperf₂
    haveI : Group.IsPerfect ψB.range := Group.IsPerfect.range ψB
    exact Subgroup.isPerfect_iff.1
      (Group.IsPerfect.map (H := ψB.range) (MulAut.conj g⁻¹).toMonoidHom)
  · have hcardB : Nat.card ↥ψB.range = Nat.card M₂ :=
      (Nat.card_congr (MonoidHom.ofInjective hB).toEquiv).symm
    rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hcardB]
    exact hp₂


theorem exists_twoFrames_adjointE8_five (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = 5) :
    ∃ ψA ψB : SL(5, K) →* adjointGroup Tag.E8 K,
      Function.Injective ψA ∧ Function.Injective ψB ∧ (∀ x y, Commute (ψA x) (ψB y)) ∧
      ¬ p ∣ Nat.card ↥(ψA.range ⊓ ψB.range) ∧
      (Nat.card (adjointGroup Tag.E8 K)).factorization p =
        (Nat.card SL(5, K)).factorization p + (Nat.card SL(5, K)).factorization p := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  have : Finite (ModGL Tag.E8 K) := finite_modGL
  obtain ⟨ψA, ψB, hA, hB, hcomm, hrange⟩ := exists_splitFrame_E8 K
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hp11 : 11 ≤ p := eleven_le_of_orderOf_eq_five hp hord
  have hcard : (Nat.card (adjointGroup Tag.E8 K)).factorization p =
      (Nat.card SL(5, K)).factorization p + (Nat.card SL(5, K)).factorization p := by
    rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp,
      CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E8,
      padicValNat_ordE8_of_orderOf_eq_five hp (by omega) hq2 hord,
      padicValNat_card_SL_of_orderOf_eq K hp (by norm_num)
        (by rw [← Nat.card_eq_fintype_card]; exact hord), Nat.card_eq_fintype_card]
    ring
  have hAG : ∀ x, ψA x ∈ adjointGroup Tag.E8 K := fun x => by
    have h : ψA x ∈ ψA.range ⊔ ψB.range := Subgroup.mem_sup_left ⟨x, rfl⟩
    rw [hrange] at h
    exact rootSpan_le_adjointGroup K _ h
  have hBG : ∀ x, ψB x ∈ adjointGroup Tag.E8 K := fun x => by
    have h : ψB x ∈ ψA.range ⊔ ψB.range := Subgroup.mem_sup_right ⟨x, rfl⟩
    rw [hrange] at h
    exact rootSpan_le_adjointGroup K _ h
  let ψA' : SL(5, K) →* adjointGroup Tag.E8 K := ψA.codRestrict (adjointGroup Tag.E8 K) hAG
  let ψB' : SL(5, K) →* adjointGroup Tag.E8 K := ψB.codRestrict (adjointGroup Tag.E8 K) hBG
  have hA' : Function.Injective ψA' := fun x y h => hA (congrArg Subtype.val h)
  have hB' : Function.Injective ψB' := fun x y h => hB (congrArg Subtype.val h)
  have hcomm' : ∀ x y, Commute (ψA' x) (ψB' y) := fun x y => Subtype.ext (hcomm x y).eq
  have hAB : ¬ p ∣ Nat.card ↥(ψA'.range ⊓ ψB'.range) := by
    intro hdvd
    have hle : ψA'.range ⊓ ψB'.range ≤ (Subgroup.center SL(5, K)).map ψA' := by
      rintro z ⟨⟨c, rfl⟩, hcB⟩
      exact ⟨c, Subgroup.mem_center_iff.2 fun x =>
        (commute_of_frame_mem_range hA' hcomm' hcB x).eq, rfl⟩
    have h1 := Subgroup.card_le_of_le hle
    rw [Subgroup.card_map_of_injective hA'] at h1
    have h2 := CFSG.HardMathSupport.Foote.Proving.natCard_center_SL_le (Fin 5) K
    have h3 : p ≤ Nat.card ↥(ψA'.range ⊓ ψB'.range) := Nat.le_of_dvd Nat.card_pos hdvd
    simp only [Fintype.card_fin] at h2
    omega
  exact ⟨ψA', ψB', hA', hB', hcomm', hAB, hcard⟩

theorem perfectCentralizerPlanes_adjointGroup_E8_five (K : Type) [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = 5) :
    PerfectCentralizerPlanes p (adjointGroup Tag.E8 K) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  have : Finite (ModGL Tag.E8 K) := finite_modGL
  obtain ⟨ψA, ψB, hA, hB, hcomm, hAB, hcard⟩ := exists_twoFrames_adjointE8_five K hp hord
  refine perfectCentralizerPlanes_of_twoFrames ψA ψB hA hB hcomm ?_ ?_ hAB hcard ?_ ?_
  · exact fun g hg => isCyclic_centralizer_of_orderOf_eq K hp (by norm_num)
      (by rw [← Nat.card_eq_fintype_card]; exact hord) hg
  · exact fun g hg => isCyclic_centralizer_of_orderOf_eq K hp (by norm_num)
      (by rw [← Nat.card_eq_fintype_card]; exact hord) hg
  · exact (isQuasisimple_SL (K := K) (n := 5) (by norm_num)).1
  · exact p_dvd_card_SL_of_orderOf_eq (n := 5) hp (by norm_num) hord

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
