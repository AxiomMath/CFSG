module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Gen2318

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open
  CFSG.TauCetiBridge.Even


namespace Gen2318OutAux

theorem transport_mem_range {S C : Type} [Group S] [Group C] (e : S ≃* C)
    (H : ∀ β : MulAut C, β ^ 3 = 1 → β ∈ (MulAut.conj : C →* MulAut C).range)
    (E : Subgroup (MulAut S)) (hE : ∀ x ∈ E, x ^ 3 = 1) :
    E ≤ (MulAut.conj : S →* MulAut S).range := by
  intro α hα
  have h3 : MulAut.congr e α ^ 3 = 1 := by
    rw [← map_pow, hE α hα, map_one]
  obtain ⟨c, hc⟩ := H _ h3
  refine ⟨e.symm c, MulEquiv.ext fun s => ?_⟩
  have hx := congrArg (fun φ : MulAut C => φ (e s)) hc
  simp only [MulAut.conj_apply, MulAut.congr_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply] at hx
  have hy : e.symm (c * e s * c⁻¹) = α s := by
    rw [hx, MulEquiv.symm_apply_apply]
  rw [← hy]
  simp only [map_mul, map_inv, MulEquiv.symm_apply_apply, MulAut.conj_apply]

theorem mem_of_pow_three_eq_one {G : Type} [Group G] (I : Subgroup G)
    (hN : ∀ φ : G, ∀ c ∈ I, φ * c * φ⁻¹ ∈ I) (x : G)
    (hcov : ∀ y : G, y ∈ I ∨ ∃ c ∈ I, y = c * x) (α : G) (hα : α ^ 3 = 1) : α ∈ I := by
  have hx : x ∈ I ∨ x ^ 2 ∈ I := by
    rcases hcov (x ^ 2) with h | ⟨c, hc, h⟩
    · exact Or.inr h
    · left
      have hxc : x = c := by
        calc x = x ^ 2 * x⁻¹ := by group
          _ = c * x * x⁻¹ := by rw [h]
          _ = c := by group
      rw [hxc]
      exact hc
  rcases hcov α with hαI | ⟨c, hc, hαc⟩
  · exact hαI
  · rcases hx with hxI | hx2
    · rw [hαc]
      exact I.mul_mem hc hxI
    · have hxI : x ∈ I := by
        have e1 : x * c * x⁻¹ ∈ I := hN x c hc
        have e2 : x ^ 2 * c * (x ^ 2)⁻¹ ∈ I := hN (x ^ 2) c hc
        have hid3 : c * (x * c * x⁻¹) * (x ^ 2 * c * (x ^ 2)⁻¹) * x ^ 3 = (c * x) ^ 3 := by
          rw [pow_three (c * x)]
          group
        have key : c * (x * c * x⁻¹) * (x ^ 2 * c * (x ^ 2)⁻¹) * x ^ 3 = 1 := by
          rw [hid3, ← hαc, hα]
        have h3 : x ^ 3 = (c * (x * c * x⁻¹) * (x ^ 2 * c * (x ^ 2)⁻¹))⁻¹ :=
          eq_inv_of_mul_eq_one_right key
        have hx3 : x ^ 3 ∈ I := by
          rw [h3]
          exact I.inv_mem (I.mul_mem (I.mul_mem hc e1) e2)
        have hxeq : x = (x ^ 2)⁻¹ * x ^ 3 := by group
        rw [hxeq]
        exact I.mul_mem (I.inv_mem hx2) hx3
      rw [hαc]
      exact I.mul_mem hc hxI

noncomputable def adjointEquiv (τ : Tag) (K : Type) [Field K] [Finite K] :
    AdjointQuotient τ K ≃* adjointGroup τ K :=
  (QuotientGroup.quotientMulEquivOfEq (center_adjointGroup_eq_bot (τ := τ) (K := K))).trans
    QuotientGroup.quotientBot

theorem f4_inner_of_cube_one
    (β : MulAut (adjointGroup CFSG.LieType.Ree.ReeTag.F4.tag (GaloisField 2 2)))
    (hβ : β ^ 3 = 1) :
    β ∈ (MulAut.conj : adjointGroup CFSG.LieType.Ree.ReeTag.F4.tag (GaloisField 2 2) →*
      MulAut (adjointGroup CFSG.LieType.Ree.ReeTag.F4.tag (GaloisField 2 2))).range := by
  haveI : CharP (GaloisField 2 2) CFSG.LieType.Ree.ReeTag.F4.prime :=
    (inferInstance : CharP (GaloisField 2 2) 2)
  have hKcard : Nat.card (GaloisField 2 2) = 2 ^ 2 := GaloisField.card 2 2 (by norm_num)
  obtain ⟨-, hB, ⟨Θ, hΘ, -, hker⟩, -⟩ :=
    even_F4_exact_automorphism_normal_form (f := 2) (by norm_num) (GaloisField 2 2) hKcard
  obtain ⟨⟨g, k⟩, hgk⟩ := (hB β).exists
  have hΘβ := hΘ β g (k : ℕ) hgk
  have h3 : Θ β ^ 3 = 1 := by rw [← map_pow, hβ, map_one]
  rw [hΘβ, ← ofAdd_nsmul, ofAdd_eq_one] at h3
  have key : ∀ x : ZMod 4, (3 : ℕ) • x = 0 → x = 0 := by decide
  have hk0 : ((k : ℕ) : ZMod (2 * 2)) = 0 := key _ h3
  have hΘ1 : Θ β = 1 := by
    rw [hΘβ, hk0, ofAdd_zero]
  have hmem : β ∈ Θ.ker := MonoidHom.mem_ker.2 hΘ1
  rw [hker] at hmem
  exact hmem

theorem e6_inner_of_cube_one (β : MulAut (adjointGroup Tag.E6 (ZMod 2))) (hβ : β ^ 3 = 1) :
    β ∈ (MulAut.conj : adjointGroup Tag.E6 (ZMod 2) →*
      MulAut (adjointGroup Tag.E6 (ZMod 2))).range := by
  classical
  obtain ⟨-, hB, hA⟩ :=
    ordinary_E_exact_automorphism_normal_form Tag.E6 (Or.inl rfl) (ZMod 2)
  have hunit : ∀ a : Fin Tag.E6.rank → (ZMod 2)ˣ, a = 1 := fun a => funext fun i => by
    have hz : ∀ z : ZMod 2, z ≠ 0 → z = 1 := by decide
    exact Units.ext (hz _ (a i).ne_zero)
  have hσ1 : ∀ σ : ZMod 2 ≃+* ZMod 2, σ.toRingHom = RingHom.id (ZMod 2) :=
    fun σ => RingHom.ext_zmod _ _
  have hid : ∀ (σ : ZMod 2 ≃+* ZMod 2) (h : ModGL Tag.E6 (ZMod 2)),
      Units.map (entrywiseHom σ.toRingHom) h = h := fun σ h => by
    rw [hσ1 σ]
    exact Units.ext (entrywise_id _)
  obtain ⟨x, -, hx⟩ := hB 1 (RingEquiv.refl (ZMod 2)) ⟨1, by decide⟩
  have hxQ : ∀ h : adjointGroup Tag.E6 (ZMod 2),
      ((x h : adjointGroup Tag.E6 (ZMod 2)) : ModGL Tag.E6 (ZMod 2)) =
        exactQ Tag.E6 (ZMod 2) 1 * (h : ModGL Tag.E6 (ZMod 2)) *
          (exactQ Tag.E6 (ZMod 2) 1)⁻¹ := by
    intro h
    rw [hx h, rootDiagUnit_one, hid, inv_one, mul_one, one_mul]
  have hcov : ∀ α : MulAut (adjointGroup Tag.E6 (ZMod 2)),
      ∃ g : adjointGroup Tag.E6 (ZMod 2),
        α = MulAut.conj g ∨ α = MulAut.conj g * x := by
    intro α
    obtain ⟨g, a, σ, ε, hα⟩ := hA α
    have ha : a = 1 := hunit a
    subst ha
    have hε : (ε : ℕ) = 0 ∨ (ε : ℕ) = 1 := by
      have hlt : (ε : ℕ) < 2 := ε.isLt
      omega
    rcases hε with hε | hε
    · refine ⟨g, Or.inl (MulEquiv.ext fun h => Subtype.ext ?_)⟩
      rw [hα h]
      simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv, hε, exactQ_zero,
        rootDiagUnit_one, hid, one_mul, mul_one, inv_one, mul_assoc]
    · refine ⟨g, Or.inr (MulEquiv.ext fun h => Subtype.ext ?_)⟩
      rw [hα h]
      simp only [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv, hxQ,
        hε, rootDiagUnit_one, hid, one_mul, mul_one, inv_one, mul_assoc]
  set I : Subgroup (MulAut (adjointGroup Tag.E6 (ZMod 2))) :=
    (MulAut.conj : adjointGroup Tag.E6 (ZMod 2) →*
      MulAut (adjointGroup Tag.E6 (ZMod 2))).range with hI
  have hN : ∀ φ : MulAut (adjointGroup Tag.E6 (ZMod 2)), ∀ c ∈ I, φ * c * φ⁻¹ ∈ I := by
    rintro φ c ⟨g, rfl⟩
    refine ⟨φ g, MulEquiv.ext fun h => ?_⟩
    simp [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv]
  have hcov' : ∀ y : MulAut (adjointGroup Tag.E6 (ZMod 2)),
      y ∈ I ∨ ∃ c ∈ I, y = c * x := by
    intro y
    obtain ⟨g, hg | hg⟩ := hcov y
    · exact Or.inl ⟨g, hg.symm⟩
    · exact Or.inr ⟨MulAut.conj g, ⟨g, rfl⟩, hg⟩
  exact mem_of_pow_three_eq_one I hN x hcov' β hβ

theorem f4_case (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.F4 q).Valid)
    (hq : IsTwoPow q 2) {S : Type} [Group S]
    (eS : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨TauCeti.LieTypeIndex.F4 q, hv⟩)
    (E : Subgroup (MulAut S)) (hE : IsElemAbelian 3 E) :
    E ≤ (MulAut.conj : S →* MulAut S).range := by
  obtain ⟨hq2, hqe⟩ := hq
  have hKcard : Nat.card (GaloisField 2 2) = 2 ^ 2 := GaloisField.card 2 2 (by norm_num)
  have hqcard : q.card = 2 ^ 2 := by
    rw [TauCeti.PrimePower.card_def, hq2, hqe]
  obtain ⟨eB⟩ := (chevalleyBridgesEven).f4 q hv hq2 (GaloisField 2 2)
    (hKcard.trans hqcard.symm)
  let e : S ≃* adjointGroup CFSG.LieType.Ree.ReeTag.F4.tag (GaloisField 2 2) :=
    (eS.trans eB.symm).trans (adjointEquiv Tag.F4 (GaloisField 2 2))
  exact transport_mem_range e (fun β hβ => f4_inner_of_cube_one β hβ) E (fun x hx => hE.2 x hx)

theorem e6_case (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E6 q).Valid)
    (hq : IsTwoPow q 1) {S : Type} [Group S]
    (eS : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨TauCeti.LieTypeIndex.E6 q, hv⟩)
    (E : Subgroup (MulAut S)) (hE : IsElemAbelian 3 E) :
    E ≤ (MulAut.conj : S →* MulAut S).range := by
  obtain ⟨hq2, hqe⟩ := hq
  have hKcard : Nat.card (ZMod 2) = 2 := by
    rw [Nat.card_eq_fintype_card, ZMod.card]
  have hqcard : q.card = 2 := by
    rw [TauCeti.PrimePower.card_def, hq2, hqe, pow_one]
  obtain ⟨eB⟩ := (chevalleyBridgesEven).e6 q hv hq2 (ZMod 2) (hKcard.trans hqcard.symm)
  let e : S ≃* adjointGroup Tag.E6 (ZMod 2) :=
    (eS.trans eB.symm).trans (adjointEquiv Tag.E6 (ZMod 2))
  exact transport_mem_range e (fun β hβ => e6_inner_of_cube_one β hβ) E (fun x hx => hE.2 x hx)

end Gen2318OutAux

theorem gen2318OutThreePrime_holds : Gen2318OutThreePrime := by
  intro S _ _ d hd hS E hE
  obtain ⟨eS⟩ := hS
  obtain ⟨d1, hv⟩ := d
  have key : (∃ q : TauCeti.PrimePower, d1 = TauCeti.LieTypeIndex.F4 q ∧ IsTwoPow q 2) ∨
      (∃ q : TauCeti.PrimePower, d1 = TauCeti.LieTypeIndex.E6 q ∧ IsTwoPow q 1) := by
    cases d1 with
    | F4 q => exact Or.inl ⟨q, rfl, hd⟩
    | E6 q => exact Or.inr ⟨q, rfl, hd⟩
    | _ => simp [IsOutThreePrimeIndex] at hd
  rcases key with ⟨q, rfl, hq⟩ | ⟨q, rfl, hq⟩
  · exact Gen2318OutAux.f4_case q hv hq eS E hE
  · exact Gen2318OutAux.e6_case q hv hq eS E hE

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
