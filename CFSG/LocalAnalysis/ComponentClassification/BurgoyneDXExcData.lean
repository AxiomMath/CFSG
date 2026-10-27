module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXExcBlk
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXExcQuat
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXExcNormal
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXParity
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCOIdent

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.DX

open Module Matrix CFSG Subgroup CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.Burgoyne.O
open scoped MatrixGroups

variable {F : Type} [Field F] [Finite F] {p : ℕ} [Fact p.Prime] [CharP F p]

variable (F) in
abbrev spinGL : Sp8 F →* GL (Fin (2 * 4)) F := (matrixDerived (Q8 F)).subtype.comp (spinM F)

omit [Finite F] [Fact p.Prime] [CharP F p] in
theorem spinGL_eq_one_iff (x : Sp8 F) : spinGL F x = 1 ↔ x = 1 ∨ x = negOne8 F := by
  rw [← mem_ker_spinM_iff F x, MonoidHom.mem_ker]
  constructor
  · intro h
    exact Subtype.ext h
  · intro h
    exact congrArg Subtype.val h

omit [Fact p.Prime] in
theorem excData_of_lift (hp2 : p ≠ 2) {R : GL (Fin (2 * 4)) F}
    (hRQ : matrixDerived (Q8 F) ≤ matrixDerived (oQ R)) {L : Type} [Group L] [Finite L]
    (α : Sp8 F →* L) (hα : Function.Surjective α) (hker : α.ker ≤ center (Sp8 F))
    (hker2 : IsPGroup 2 α.ker) {X Q : Subgroup L} (hQX : Q ≤ X)
    (hQc : IsPComponent 2 (Q.subgroupOf X)) {k : Type} [Field k] [Finite k]
    (hk : ringChar k ≠ 2) (e : Q ⧸ pPrimeCore 2 Q ≃* SL(2, k)) {c : L}
    (hcZ : c ∈ center L) (hcQ : c ∈ Q) (hc2 : orderOf c = 2)
    (hb : negOne8 F ∈ ⁅Q.comap α, Q.comap α⁆) (hbc : α (negOne8 F) = c) :
    ExcData R (⁅Q.comap α, Q.comap α⁆.map (spinGL F)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : (2 : F) ≠ 0 := two_ne_zero8 F hp2
  have hQQ : ⁅Q, Q⁆ = Q := C.commutator_eq_of_isPComponent hQX hQc
  set T := ⁅Q.comap α, Q.comap α⁆ with hT
  have key := perfectLift_spec α hα hker hker2 hQQ hk e
  obtain ⟨huniq, x, hx, y, hy, hxx, hyy, hxy, hx1, hxb, hy1, hyb, hyx, hyxb⟩ :=
    exists_quaternion α hα hker hker2 hQQ hk e hcZ hcQ hc2 hb hbc
  have hspin1 : spinGL F (negOne8 F) = 1 := (spinGL_eq_one_iff _).2 (Or.inr rfl)
  have hlift : ∀ u ∈ T.map (spinGL F), u * u = 1 → u ≠ 1 →
      ∃ z ∈ T, spinGL F z = u ∧ z * z = negOne8 F := by
    rintro _ ⟨z, hz, rfl⟩ huu hu1
    refine ⟨z, hz, rfl, ?_⟩
    rw [← map_mul] at huu
    rcases (spinGL_eq_one_iff _).1 huu with h | h
    · exfalso
      by_cases hz1 : z = 1
      · exact hu1 (by rw [hz1, map_one])
      · exact hu1 (by rw [huniq z hz h hz1, hspin1])
    · exact h
  have hdetM : ∀ u ∈ T.map (spinGL F), ((u : GL (Fin (2 * 4)) F) :
      Matrix (Fin (2 * 4)) (Fin (2 * 4)) F).det = 1 := by
    rintro _ ⟨z, -, rfl⟩
    exact C.det_eq_one_of_mem_commutator (spinM F z).2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨z, -, rfl⟩
    exact hRQ (spinM F z).2
  · rw [← Subgroup.map_commutator, key.2.1]
  · intro u hu huu hu1
    obtain ⟨z, hz, rfl, hzz⟩ := hlift u hu huu hu1
    have hzz' : spinM F (z * z) = 1 := by
      rw [hzz]
      exact negOne8_mem_ker_spinM F
    have hinv : ((spinGL F z : GL (Fin (2 * 4)) F) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) F) *
        (spinGL F z : GL (Fin (2 * 4)) F) = 1 := by
      rw [← Units.val_mul, huu, Units.val_one]
    have hev : Even (finrank F (negE ((spinGL F z : GL (Fin (2 * 4)) F) :
        Matrix (Fin (2 * 4)) (Fin (2 * 4)) F))) := by
      have hd := CFSG.GH74.Generic.involution_det h2 _ hinv
      rw [hdetM _ ⟨z, hz, rfl⟩] at hd
      have hne : (-1 : F) ≠ 1 := fun h => h2 (by linear_combination -h)
      exact (neg_one_pow_eq_one_iff_even hne).1 hd.symm
    exact (mul_self_eq_negOne8_iff hp2 z hzz' rfl hev).1 hzz
  ·
    have hx' : spinGL F x ≠ 1 := fun h => ((spinGL_eq_one_iff x).1 h).elim hx1 hxb
    have hy' : spinGL F y ≠ 1 := fun h => ((spinGL_eq_one_iff y).1 h).elim hy1 hyb
    refine ⟨spinGL F x, ⟨x, hx, rfl⟩, spinGL F y, ⟨y, hy, rfl⟩, ?_, ?_, hx', hy', ?_, ?_⟩
    · rw [← map_mul, hxx, hspin1]
    · rw [← map_mul, hyy, hspin1]
    · intro h
      have h1 : spinGL F (x⁻¹ * y) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
      rcases (spinGL_eq_one_iff _).1 h1 with h' | h'
      · exact hyx (inv_mul_eq_one.1 h').symm
      · apply hyxb
        have h3 : y = x * negOne8 F := by rw [← h', mul_inv_cancel_left]
        rw [h3, (mem_center_iff.1 (negOne8_mem_center F) x)]
    · have h1 : spinGL F (x * y * x⁻¹ * y⁻¹) = 1 := by rw [hxy, hspin1]
      rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
      have h3 := mul_inv_eq_one.1 h1
      rw [mul_inv_eq_iff_eq_mul] at h3
      exact h3
  ·
    intro N hNM hN ⟨u, huN, huu, hu1⟩
    obtain ⟨z₀, hz₀, hz₀u, hz₀z₀⟩ := hlift u (hNM huN) huu hu1
    have hTQ : ∀ z ∈ T, α z ∈ Q := fun z hz =>
      (Subgroup.commutator_le_self (Q.comap α) hz : z ∈ Q.comap α)
    set αT : T →* Q := (α.comp T.subtype).codRestrict Q fun z => hTQ z z.2 with hαT
    have hαTinj : Function.Injective αT := by
      intro a b hab
      have h' : α (a : Sp8 F) = α (b : Sp8 F) := congrArg Subtype.val hab
      apply Subtype.ext
      have := key.2.2 ((a : Sp8 F) * (b : Sp8 F)⁻¹) (mul_mem a.2 (inv_mem b.2))
        (by rw [map_mul, map_inv, h', mul_inv_cancel])
      exact mul_inv_eq_one.mp this
    have hαTsurj : Function.Surjective αT := by
      rintro ⟨q, hq⟩
      have hq' : q ∈ T.map α := by rw [key.1]; exact hq
      obtain ⟨z, hz, rfl⟩ := hq'
      exact ⟨⟨z, hz⟩, rfl⟩
    set ι : T ≃* Q := MulEquiv.ofBijective αT ⟨hαTinj, hαTsurj⟩ with hι
    set eQ : ↥(Q.subgroupOf X) ≃* Q := subgroupOfEquivOfLe hQX with heQ
    set ψ : ↥(Q.subgroupOf X) →* GL (Fin (2 * 4)) F :=
      (spinGL F).comp (T.subtype.comp (ι.symm.toMonoidHom.comp eQ.toMonoidHom)) with hψ
    have hψM : ∀ q, ψ q ∈ T.map (spinGL F) := fun q => ⟨_, (ι.symm (eQ q)).2, rfl⟩
    set N' := N.comap ψ with hN'
    have hN'n : N'.Normal := by
      refine ⟨fun a ha b => ?_⟩
      rw [hN', Subgroup.mem_comap] at ha ⊢
      rw [map_mul, map_mul, map_inv]
      have h1 := hN.conj_mem ⟨ψ a, hNM ha⟩ (mem_subgroupOf.2 ha) ⟨ψ b, hψM b⟩
      rw [mem_subgroupOf] at h1
      exact h1
    set g : ↥(Q.subgroupOf X) := eQ.symm (ι ⟨z₀, hz₀⟩) with hg
    have hψeq : ∀ q, ψ q = spinGL F ((ι.symm (eQ q) : T) : Sp8 F) := fun q => rfl
    have hgN : g ∈ N' := by
      rw [hN', Subgroup.mem_comap, hψeq, hg, MulEquiv.apply_symm_apply,
        MulEquiv.symm_apply_apply]
      change spinGL F z₀ ∈ N
      rw [hz₀u]
      exact huN
    set e' := (C.quotientPPrimeCoreEquiv eQ).trans e with he'
    have he'g : e' (QuotientGroup.mk g) = e (QuotientGroup.mk (ι ⟨z₀, hz₀⟩)) := by
      have hgq : eQ g = ι ⟨z₀, hz₀⟩ := by rw [hg, MulEquiv.apply_symm_apply]
      rw [he', MulEquiv.trans_apply, ← hgq]
      rfl
    have hιc : ι ⟨z₀, hz₀⟩ * ι ⟨z₀, hz₀⟩ = ⟨c, hcQ⟩ := by
      rw [← map_mul]
      apply Subtype.ext
      change α (z₀ * z₀) = c
      rw [hz₀z₀, hbc]
    have hec : e (QuotientGroup.mk ⟨c, hcQ⟩) = -1 := by
      apply sl2_eq_neg_one_of_mul_self hk
      · rw [← map_mul, ← QuotientGroup.mk_mul]
        have hcc : (⟨c, hcQ⟩ : Q) * ⟨c, hcQ⟩ = 1 := by
          apply Subtype.ext
          change c * c = 1
          rw [← pow_two, ← hc2, pow_orderOf_eq_one]
        rw [hcc, QuotientGroup.mk_one, map_one]
      · intro h
        rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff] at h
        have hdvd : orderOf (⟨⟨c, hcQ⟩, h⟩ : pPrimeCore 2 Q) ∣ Nat.card (pPrimeCore 2 Q) :=
          orderOf_dvd_natCard _
        rw [Subgroup.orderOf_mk, ← Subgroup.orderOf_coe] at hdvd
        change orderOf c ∣ _ at hdvd
        rw [hc2] at hdvd
        exact absurd (Nat.Coprime.coprime_dvd_right hdvd pPrimeCore_coprime_card) (by norm_num)
    have hgc : e' (QuotientGroup.mk g) ∉ center SL(2, k) := by
      intro hcen
      have hsq := C.sq_eq_one_of_mem_center_SL hcen
      rw [he'g, pow_two, ← map_mul, ← QuotientGroup.mk_mul, hιc, hec] at hsq
      have e00 := congrArg (fun A : SL(2, k) => (A : Matrix (Fin 2) (Fin 2) k) 0 0) hsq
      simp at e00
      apply Ring.two_ne_zero hk
      linear_combination -e00
    have htop := eq_top_of_normal hQc hk e' hN'n hgN hgc
    refine le_antisymm hNM ?_
    rintro _ ⟨z, hz, rfl⟩
    have hq : eQ.symm (ι ⟨z, hz⟩) ∈ N' := htop ▸ mem_top _
    rw [hN', Subgroup.mem_comap, hψeq, MulEquiv.apply_symm_apply,
      MulEquiv.symm_apply_apply] at hq
    exact hq

end CFSG.ComponentClassification.Burgoyne.DX
