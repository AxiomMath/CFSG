module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.U4Tab5
public import CFSG.Milestones.ASVolI.F429.One
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U4Tab4

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.HardMathSupport.Solomon.LocalBalance
open scoped commutatorElement

theorem isGenLie_U4two_of_catalogIs {S : Type} [Group S] (h : catalogIs S S9.isU4two) :
    CFSG.ASVolI.ChF.IsGenLie S CFSG.ASVolI.ChF.GLKind.U4 2 1 := by
  obtain ⟨q, hv, hq, ⟨e⟩⟩ := lieIndex_isU4two h
  obtain ⟨h1, h2⟩ := primePower_eq_of_card_eq Nat.prime_two (s := 1) (by norm_num)
    (hq.trans (by norm_num))
  have hm := lieModel_twistedA' 3 q hv e
  rw [h1, h2] at hm
  obtain ⟨-, K, FK, FinK, hK, ⟨e'⟩⟩ := hm.statedClassicalModel (by decide)
  exact ⟨Nat.prime_two, le_rfl, K, FK, FinK, hK, ⟨e'⟩⟩

theorem mulAut_eq_one_of_central {Q : Type} [Group Q] (hperf : commutator Q = ⊤) (u : MulAut Q)
    (hu : ∀ g : Q, g⁻¹ * u g ∈ Subgroup.center Q) : u = 1 := by
  let z : Q →* Subgroup.center Q :=
    { toFun := fun g => ⟨g⁻¹ * u g, hu g⟩
      map_one' := by
        ext
        simp
      map_mul' := by
        intro a b
        ext
        show (a * b)⁻¹ * u (a * b) = (a⁻¹ * u a) * (b⁻¹ * u b)
        have hc := Subgroup.mem_center_iff.1 (hu a) b⁻¹
        rw [map_mul, mul_inv_rev]
        calc b⁻¹ * a⁻¹ * (u a * u b) = b⁻¹ * (a⁻¹ * u a) * u b := by group
          _ = (a⁻¹ * u a) * b⁻¹ * u b := by rw [hc]
          _ = a⁻¹ * u a * (b⁻¹ * u b) := by group }
  have hker : commutator Q ≤ z.ker := by
    refine Subgroup.commutator_le.2 (fun a _ b _ => ?_)
    rw [MonoidHom.mem_ker]
    have h1 : z ⁅a, b⁆ = ⁅z a, z b⁆ := map_commutatorElement z a b
    rw [h1, commutatorElement_eq_one_iff_mul_comm]
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.1 (z a).2 (z b : Q)).symm
  have hz : ∀ g : Q, z g = 1 := by
    intro g
    have hg : g ∈ z.ker := by
      have : (⊤ : Subgroup Q) ≤ z.ker := by
        rw [← hperf]
        exact hker
      exact this (Subgroup.mem_top g)
    exact (MonoidHom.mem_ker).1 hg
  ext g
  have hg := congrArg Subtype.val (hz g)
  have h1 : g⁻¹ * u g = 1 := by
    simpa [z] using hg
  show u g = g
  calc u g = g * (g⁻¹ * u g) := by group
    _ = g := by rw [h1, mul_one]

theorem mulAut_quot_injective {Q : Type} [Group Q] (hperf : commutator Q = ⊤) :
    Function.Injective (fun v : MulAut Q =>
      (QuotientGroup.congr (Subgroup.center Q) (Subgroup.center Q) v
        (Subgroup.map_center_eq v) : MulAut (Q ⧸ Subgroup.center Q))) := by
  intro v w hvw
  have hpt : ∀ g : Q, (QuotientGroup.mk (v g) : Q ⧸ Subgroup.center Q) =
      QuotientGroup.mk (w g) := by
    intro g
    have := congrArg (fun φ : MulAut (Q ⧸ Subgroup.center Q) => φ (QuotientGroup.mk g)) hvw
    simpa [QuotientGroup.congr_mk] using this
  have hu : ∀ h : Q, h⁻¹ * (v⁻¹ * w) h ∈ Subgroup.center Q := by
    intro h
    have hc : (v h)⁻¹ * w h ∈ Subgroup.center Q := (QuotientGroup.eq).1 (hpt h)
    have key : (v⁻¹ * w) h = h * (v⁻¹ ((v h)⁻¹ * w h)) := by
      have e1 : v⁻¹ (v h) = h := by simp
      show v⁻¹ (w h) = h * (v⁻¹ ((v h)⁻¹ * w h))
      rw [map_mul, map_inv, e1]
      group
    rw [key, inv_mul_cancel_left]
    exact aut_mem_center v⁻¹ hc
  have hone : v⁻¹ * w = 1 := mulAut_eq_one_of_central hperf (v⁻¹ * w) hu
  exact inv_mul_eq_one.1 hone

theorem card_mulAut_le_of_quot {Q : Type} [Group Q] [Finite Q] (hperf : commutator Q = ⊤) :
    Nat.card (MulAut Q) ≤ Nat.card (MulAut (Q ⧸ Subgroup.center Q)) :=
  Nat.card_le_card_of_injective _ (mulAut_quot_injective hperf)

theorem index_innerAut_le_of_quot {Q : Type} [Group Q] [Finite Q] (hQ : CFSG.Open.IsQuasisimple Q) :
    (innerAut Q).index ≤ (innerAut (Q ⧸ Subgroup.center Q)).index := by
  haveI : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hQ.2
  obtain ⟨e⟩ := innerAut_mulEquiv_quot Q
  have hIQ : Nat.card (innerAut Q) = Nat.card (Q ⧸ Subgroup.center Q) :=
    (Nat.card_congr e.toEquiv).symm
  have hIS : Nat.card (innerAut (Q ⧸ Subgroup.center Q)) ≤ Nat.card (Q ⧸ Subgroup.center Q) := by
    have hsurj : Function.Surjective
        ((MulAut.conj : (Q ⧸ Subgroup.center Q) →* MulAut (Q ⧸ Subgroup.center Q)).rangeRestrict) :=
      MonoidHom.rangeRestrict_surjective _
    exact Nat.card_le_card_of_surjective _ hsurj
  have hSpos : 0 < Nat.card (Q ⧸ Subgroup.center Q) := Nat.card_pos
  have h1 := Subgroup.card_mul_index (innerAut Q)
  have h2 := Subgroup.card_mul_index (innerAut (Q ⧸ Subgroup.center Q))
  rw [hIQ] at h1
  refine Nat.le_of_mul_le_mul_left ?_ hSpos
  calc Nat.card (Q ⧸ Subgroup.center Q) * (innerAut Q).index = Nat.card (MulAut Q) := h1
    _ ≤ Nat.card (MulAut (Q ⧸ Subgroup.center Q)) := card_mulAut_le_of_quot hQ.1
    _ = Nat.card (innerAut (Q ⧸ Subgroup.center Q)) * (innerAut (Q ⧸ Subgroup.center Q)).index :=
      h2.symm
    _ ≤ Nat.card (Q ⧸ Subgroup.center Q) * (innerAut (Q ⧸ Subgroup.center Q)).index :=
      Nat.mul_le_mul_right _ hIS

theorem index_innerAut_of_quot_two {Q : Type} [Group Q] [Finite Q] (hQ : CFSG.Open.IsQuasisimple Q)
    (h2 : (innerAut (Q ⧸ Subgroup.center Q)).index = 2) :
    ∃ a b : ℕ, (innerAut Q).index = 2 ^ a * 3 ^ b := by
  have hle := index_innerAut_le_of_quot hQ
  rw [h2] at hle
  have hpos : (innerAut Q).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rcases (by omega : (innerAut Q).index = 1 ∨ (innerAut Q).index = 2) with h | h
  · exact ⟨0, 0, by simp [h]⟩
  · exact ⟨1, 0, by simp [h]⟩

theorem isGenLie_U5two_of_catalogIs {S : Type} [Group S] (h : catalogIs S S9.isU5two) :
    CFSG.ASVolI.ChF.IsGenLie S CFSG.ASVolI.ChF.GLKind.U5 2 1 := by
  obtain ⟨q, hv, hq, ⟨e⟩⟩ := lieIndex_isU5two h
  obtain ⟨h1, h2⟩ := primePower_eq_of_card_eq Nat.prime_two (s := 1) (by norm_num)
    (hq.trans (by norm_num))
  have hm := lieModel_twistedA' 4 q hv e
  rw [h1, h2] at hm
  rcases hm.toBlueprint (by decide) with ⟨-, -, K, FK, FinK, hcard, ⟨e'⟩⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · exact ⟨Nat.prime_two, le_rfl, K, FK, FinK, hcard, ⟨e'⟩⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)

theorem U4OutS_u4two : ∀ (Q : Type) [Group Q] [Finite Q], CFSG.Open.IsQuasisimple Q →
    GLAPPrimeCore 3 Q = ⊥ → catalogIs (Q ⧸ Subgroup.center Q) S9.isU4two →
      ∃ a b : ℕ, (innerAut Q).index = 2 ^ a * 3 ^ b := by
  intro Q _ _ hQ _ hZ
  exact index_innerAut_of_quot_two hQ (CFSG.ASVolI.burnsideF429_card_outer_U4two (isGenLie_U4two_of_catalogIs hZ))

theorem U5OutS_u5two : ∀ (Q : Type) [Group Q] [Finite Q], CFSG.Open.IsQuasisimple Q →
    GLAPPrimeCore 3 Q = ⊥ → catalogIs (Q ⧸ Subgroup.center Q) S9.isU5two →
      ∃ a b : ℕ, (innerAut Q).index = 2 ^ a * 3 ^ b := by
  intro Q _ _ hQ _ hZ
  exact index_innerAut_of_quot_two hQ (CFSG.ASVolI.burnsideF429_card_outer_U5two (isGenLie_U5two_of_catalogIs hZ))

@[expose] def U4OutRest : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], CFSG.Open.IsQuasisimple Q → GLAPPrimeCore 3 Q = ⊥ →
    catalogIs (Q ⧸ Subgroup.center Q) (fun i => S9.isTableU4 i ∧ ¬ S9.isU4two i ∧ ¬ S9.isU5two i) →
      ∃ a b : ℕ, (innerAut Q).index = 2 ^ a * 3 ^ b

theorem u4OutS_of_rest (h : U4OutRest) : U4OutS := by
  intro Q _ _ hQ hO hcat
  by_cases h2 : catalogIs (Q ⧸ Subgroup.center Q) S9.isU4two
  · exact U4OutS_u4two Q hQ hO h2
  by_cases h5 : catalogIs (Q ⧸ Subgroup.center Q) S9.isU5two
  · exact U5OutS_u5two Q hQ hO h5
  refine h Q hQ hO ?_
  obtain ⟨i, hi, e⟩ := hcat
  exact ⟨i, ⟨hi, fun h' => h2 ⟨i, h', e⟩, fun h' => h5 ⟨i, h', e⟩⟩, e⟩

theorem u4TableAt_of_residual (G : Type) [Group G] [Finite G] (hInn : U4InnRest) (hOut : U4OutRest) :
    U4TableAt G :=
  u4TableAt_of_S G ⟨u4InnS_of_rest hInn, u4OutS_of_rest hOut⟩

end CFSG.LocalAnalysis.GLTheoremA.CatB

end
