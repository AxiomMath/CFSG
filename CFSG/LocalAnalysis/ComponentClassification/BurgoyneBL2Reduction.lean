module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBInputs
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCData
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrTwoLocalTools
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBFinal

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.B

open CFSG Subgroup CFSG.ComponentClassification.TBLit
open scoped MatrixGroups

theorem eq_one_of_forall_mul_inv_mem_center {L : Type*} [Group L] [Group.IsPerfect L]
    (s : MulAut L) (h : ∀ x, x⁻¹ * s x ∈ center L) : s = 1 := by
  let f : L →* center L :=
    { toFun := fun x => ⟨x⁻¹ * s x, h x⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => by
        apply Subtype.ext
        change (x * y)⁻¹ * s (x * y) = x⁻¹ * s x * (y⁻¹ * s y)
        have hc := mem_center_iff.1 (h x) y⁻¹
        rw [map_mul, mul_inv_rev]
        calc y⁻¹ * x⁻¹ * (s x * s y) = y⁻¹ * (x⁻¹ * s x) * s y := by group
          _ = x⁻¹ * s x * y⁻¹ * s y := by rw [hc]
          _ = x⁻¹ * s x * (y⁻¹ * s y) := by group }
  have hker : f.ker = ⊤ := by
    rw [eq_top_iff, ← (inferInstance : Group.IsPerfect L).commutator_eq_top]
    exact Abelianization.commutator_subset_ker f
  ext x
  have hx : f x = 1 := by
    rw [← MonoidHom.mem_ker, hker]
    exact mem_top x
  have hx' : x⁻¹ * s x = 1 := congrArg Subtype.val hx
  change s x = x
  rw [inv_mul_eq_one] at hx'
  exact hx'.symm

theorem exists_inducedAut {L S : Type*} [Group L] [Group S] (π : L →* S)
    (hπ : Function.Surjective π) (hker : π.ker = center L) (s : MulAut L) :
    ∃ v : MulAut S, ∀ x, v (π x) = π (s x) := by
  let e : L ⧸ center L ≃* S := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective π hπ)
  have he : ∀ x, e (QuotientGroup.mk x) = π x := fun x => rfl
  have hZ : (center L).map s.toMonoidHom = center L :=
    Subgroup.characteristic_iff_map_eq.1 inferInstance s
  let s' : L ⧸ center L ≃* L ⧸ center L := QuotientGroup.congr _ _ s hZ
  refine ⟨e.symm.trans (s'.trans e), fun x => ?_⟩
  change e (s' (e.symm (π x))) = π (s x)
  rw [← he x, MulEquiv.symm_apply_apply]
  rfl

theorem exists_L2_component_of_propBHypII {L : Type} [Group L] [Finite L] (hL : IsQuasisimple L)
    {S : Type} [Group S] [Finite S] (π : L →* S) (hπ : Function.Surjective π)
    (hker : π.ker = center L) {c : L} (hc : PropBHypII L c) :
    ∃ v : MulAut S, orderOf v = 2 ∧ ∃ R : Subgroup S, R ≤ autFixed v ∧
      IsPComponent 2 (R.subgroupOf (autFixed v)) ∧
      ∃ (p n : ℕ) (_ : Fact p.Prime), p ≠ 2 ∧ 0 < n ∧
        ∃ (N : Subgroup R) (_ : N.Normal), Odd (Nat.card N) ∧
          Nonempty (R ⧸ N ≃* PSL(2, GaloisField p n)) := by
  obtain ⟨s, hs2, Q, hQs, hQc, ⟨p, n, hp, hp2, hn, ⟨e⟩⟩, hcZ, hcQ, hc2⟩ := hc
  have : Group.IsPerfect L := hL.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF2 : (2 : GaloisField p n) ≠ 0 := C.two_ne_zero_galoisField hp2
  have hπZ : ∀ {x : L}, π x = 1 ↔ x ∈ center L := fun {x} => by
    rw [← MonoidHom.mem_ker, hker]
  obtain ⟨v, hv⟩ := exists_inducedAut π hπ hker s
  have hs : s ^ 2 = 1 := hs2 ▸ pow_orderOf_eq_one s
  have hv2 : orderOf v = 2 := by
    refine orderOf_eq_prime ?_ fun h1 => ?_
    · ext y
      obtain ⟨x, rfl⟩ := hπ y
      rw [pow_two, MulAut.mul_apply, hv, hv, ← MulAut.mul_apply, ← pow_two, hs]
      rfl
    · have hs1 : s = 1 := eq_one_of_forall_mul_inv_mem_center s fun x => by
        rw [← hπZ, map_mul, map_inv, ← hv, h1]
        exact inv_mul_cancel _
      rw [hs1, orderOf_one] at hs2
      exact absurd hs2 (by norm_num)
  set H := autFixed s with hH
  set R := Q.map π with hR
  have hfix : ∀ {x : L}, x ∈ H → π x ∈ autFixed v := fun {x} hx => by
    change v (π x) = π x
    rw [hv]
    exact congrArg π hx
  have hRv : R ≤ autFixed v := by
    rintro _ ⟨x, hx, rfl⟩
    exact hfix (hQs hx)
  set H₁ := H.map π with hH₁
  have hH₁v : H₁ ≤ autFixed v := by
    rintro _ ⟨x, hx, rfl⟩
    exact hfix hx
  let πH : H →* H₁ := (π.comp H.subtype).codRestrict H₁ fun h => ⟨h, h.2, rfl⟩
  have hπHs : Function.Surjective πH := by
    rintro ⟨_, ⟨h, hh, rfl⟩⟩
    exact ⟨⟨h, hh⟩, rfl⟩
  have hπHc : πH.ker ≤ center H := by
    intro x hx
    have hx' : π x = 1 := congrArg Subtype.val hx
    rw [hπZ] at hx'
    exact mem_center_iff.2 fun y => Subtype.ext (mem_center_iff.1 hx' y)
  have hR₁ : IsPComponent 2 (R.subgroupOf H₁) := by
    have h := CatalogueBCentralQuotient.pComponent_map 2 πH hπHs hπHc (Q.subgroupOf H) hQc
    have heq : (Q.subgroupOf H).map πH = R.subgroupOf H₁ := by
      ext ⟨y, hy⟩
      simp only [mem_map, mem_subgroupOf, hR]
      constructor
      · rintro ⟨⟨x, hxH⟩, hxQ, hxy⟩
        exact ⟨x, hxQ, congrArg Subtype.val hxy⟩
      · rintro ⟨x, hxQ, rfl⟩
        exact ⟨⟨x, hQs hxQ⟩, hxQ, rfl⟩
    rwa [heq] at h
  have hnorm : (H₁.subgroupOf (autFixed v)).Normal := by
    refine ⟨fun a ha b => ?_⟩
    rw [mem_subgroupOf] at ha ⊢
    obtain ⟨h, hh, hha⟩ := ha
    obtain ⟨y, hy⟩ := hπ b
    have hyfix : π (s y) = π y := by rw [← hv, hy]; exact b.2
    have hz : y⁻¹ * s y ∈ center L := by
      rw [← hπZ, map_mul, map_inv, hyfix, inv_mul_cancel]
    refine ⟨y * h * y⁻¹, ?_, ?_⟩
    · change s (y * h * y⁻¹) = y * h * y⁻¹
      have hsh : s h = h := hh
      have hsy : s y = y * (y⁻¹ * s y) := by group
      rw [map_mul, map_mul, map_inv, hsh, hsy]
      have hc := mem_center_iff.1 hz h
      calc y * (y⁻¹ * s y) * h * (y * (y⁻¹ * s y))⁻¹ =
            y * ((y⁻¹ * s y) * h) * (y⁻¹ * s y)⁻¹ * y⁻¹ := by group
        _ = y * (h * (y⁻¹ * s y)) * (y⁻¹ * s y)⁻¹ * y⁻¹ := by rw [hc]
        _ = y * h * y⁻¹ := by group
    · rw [map_mul, map_mul, map_inv, hy, hha]
      rfl
  have hRc : IsPComponent 2 (R.subgroupOf (autFixed v)) :=
    UnbalancedCorr.isPComponent_subgroupOf_of_isSubnormal (map_mono hQs) hH₁v
      hnorm.isSubnormal hR₁
  let πQ : Q →* R := (π.comp Q.subtype).codRestrict R fun q => ⟨q, q.2, rfl⟩
  have hπQs : Function.Surjective πQ := by
    rintro ⟨_, ⟨x, hx, rfl⟩⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  let ψ : Q →* PSL(2, GaloisField p n) :=
    (QuotientGroup.mk' (center SL(2, GaloisField p n))).comp
      (e.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 Q)))
  have hψs : Function.Surjective ψ :=
    (QuotientGroup.mk'_surjective _).comp (e.surjective.comp (QuotientGroup.mk'_surjective _))
  have hcen : ∀ x : Q, (x : L) ∈ center L →
      e (QuotientGroup.mk x) ∈ center SL(2, GaloisField p n) := by
    intro x hx
    rw [mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective (pPrimeCore 2 Q))) g
    change e (QuotientGroup.mk y) * e (QuotientGroup.mk x) =
      e (QuotientGroup.mk x) * e (QuotientGroup.mk y)
    have hxy : y * x = x * y := Subtype.ext (mem_center_iff.1 hx y)
    rw [← map_mul, ← map_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hxy]
  have hle : πQ.ker ≤ ψ.ker := by
    intro x hx
    have hx' : π x = 1 := congrArg Subtype.val hx
    rw [hπZ] at hx'
    rw [MonoidHom.mem_ker]
    change QuotientGroup.mk (e (QuotientGroup.mk x)) = 1
    rw [QuotientGroup.eq_one_iff]
    exact hcen x hx'
  let φ : R →* PSL(2, GaloisField p n) := (QuotientGroup.lift πQ.ker ψ hle).comp
    (QuotientGroup.quotientKerEquivOfSurjective πQ hπQs).symm.toMonoidHom
  have hφ : ∀ x, φ (πQ x) = ψ x := fun x => by
    change QuotientGroup.lift πQ.ker ψ hle
      ((QuotientGroup.quotientKerEquivOfSurjective πQ hπQs).symm (πQ x)) = ψ x
    rw [show (QuotientGroup.quotientKerEquivOfSurjective πQ hπQs).symm (πQ x) =
      QuotientGroup.mk x from (MulEquiv.symm_apply_eq _).2 rfl]
    rfl
  have hφs : Function.Surjective φ := by
    intro y
    obtain ⟨x, rfl⟩ := hψs y
    exact ⟨πQ x, hφ x⟩
  set c' : Q := ⟨c, hcQ⟩ with hc'
  have hc'2 : orderOf c' = 2 := by rw [Subgroup.orderOf_mk]; exact hc2
  have hc'O := C.not_mem_pPrimeCore_of_orderOf hc'2
  have hec : e (QuotientGroup.mk c') = -1 := by
    have hcc : c' * c' = 1 := by
      have := pow_orderOf_eq_one c'
      rwa [hc'2, pow_two] at this
    have hsq : e (QuotientGroup.mk c') * e (QuotientGroup.mk c') = 1 := by
      rw [← map_mul, ← QuotientGroup.mk_mul, hcc, QuotientGroup.mk_one, map_one]
    rcases C.eq_one_or_eq_neg_one hF2 _ hsq with h1 | h1
    · exfalso
      rw [map_eq_one_iff _ e.injective, QuotientGroup.eq_one_iff] at h1
      exact hc'O h1
    · exact h1
  have hker' : φ.ker ≤ (pPrimeCore 2 Q).map πQ := by
    intro r hr
    obtain ⟨x, rfl⟩ := hπQs r
    rw [MonoidHom.mem_ker, hφ] at hr
    change QuotientGroup.mk (e (QuotientGroup.mk x)) = 1 at hr
    rw [QuotientGroup.eq_one_iff] at hr
    rcases C.eq_one_or_eq_neg_one hF2 _ (by
      rw [← pow_two]; exact C.sq_eq_one_of_mem_center_SL hr) with h1 | h1
    · rw [map_eq_one_iff _ e.injective, QuotientGroup.eq_one_iff] at h1
      exact ⟨x, h1, rfl⟩
    · rw [← hec] at h1
      have h1' := QuotientGroup.eq.1 (e.injective h1)
      refine ⟨c'⁻¹ * x, ?_, ?_⟩
      · have := inv_mem h1'
        rwa [mul_inv_rev, inv_inv] at this
      · rw [map_mul, map_inv]
        have hπc : πQ c' = 1 := Subtype.ext ((hπZ).2 hcZ)
        rw [hπc, inv_one, one_mul]
  refine ⟨v, hv2, R, hRv, hRc, p, n, hp, hp2, hn, φ.ker, inferInstance, ?_,
    ⟨QuotientGroup.quotientKerEquivOfSurjective φ hφs⟩⟩
  have hodd : Odd (Nat.card ((pPrimeCore 2 Q).map πQ)) :=
    Odd.of_dvd_nat C.odd_card_pPrimeCore (Subgroup.card_map_dvd _ _)
  exact Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le hker')

variable {J : Type} [Group J] [Finite J] (K : Subgroup J) [K.Normal]

theorem exists_socle_quotient (hq : IsQuasisimple (K ⧸ pPrimeCore 2 K))
    (hsimple : IsSimpleGroup (GeneralizedFitting.subgroup (rhoZ K).range))
    (hnab : ∃ a b : GeneralizedFitting.subgroup (rhoZ K).range, a * b ≠ b * a) :
    ∃ q : K ⧸ pPrimeCore 2 K →* GeneralizedFitting.subgroup (rhoZ K).range,
      Function.Surjective q ∧ q.ker = center (K ⧸ pPrimeCore 2 K) := by
  have hrange := liftHom_range_eq K hq hsimple hnab
  refine ⟨(liftHom K).codRestrict _ fun x => hrange ▸ ⟨x, rfl⟩, ?_, ?_⟩
  · rintro ⟨y, hy⟩
    rw [← hrange] at hy
    obtain ⟨x, rfl⟩ := hy
    exact ⟨x, rfl⟩
  · rw [← ker_liftHom K hq]
    ext x
    simp only [MonoidHom.mem_ker]
    exact Subtype.ext_iff

theorem exists_L2_component_of_propBHyp {t : J} {Y : Subgroup J} {c : K ⧸ pPrimeCore 2 K}
    (hH : PropBHyp J K t Y c) :
    ∃ v : MulAut (GeneralizedFitting.subgroup (rhoZ K).range), orderOf v = 2 ∧
      ∃ R : Subgroup (GeneralizedFitting.subgroup (rhoZ K).range), R ≤ autFixed v ∧
        IsPComponent 2 (R.subgroupOf (autFixed v)) ∧
        ∃ (p n : ℕ) (_ : Fact p.Prime), p ≠ 2 ∧ 0 < n ∧
          ∃ (N : Subgroup R) (_ : N.Normal), Odd (Nat.card N) ∧
            Nonempty (R ⧸ N ≃* PSL(2, GaloisField p n)) := by
  have hq : IsQuasisimple (K ⧸ pPrimeCore 2 K) := hH.1
  have hsimple : IsSimpleGroup (GeneralizedFitting.subgroup (rhoZ K).range) := hH.2.1.1
  have hnab : ∃ a b : GeneralizedFitting.subgroup (rhoZ K).range, a * b ≠ b * a := hH.2.1.2.1
  have hII : PropBHypII (K ⧸ pPrimeCore 2 K) c := by
    obtain ⟨s, hs2, -, -, Q, hQs, hQc, hQiso, hcZ, hcQ, hc2, -⟩ := hH.2.2.2.2.2
    exact ⟨s, hs2, Q, hQs, hQc, hQiso, hcZ, hcQ, hc2⟩
  obtain ⟨q, hqs, hqk⟩ := exists_socle_quotient K hq hsimple hnab
  have : Finite (GeneralizedFitting.subgroup (rhoZ K).range) := Finite.of_surjective q hqs
  exact exists_L2_component_of_propBHypII hq q hqs hqk hII

end CFSG.ComponentClassification.Burgoyne.B
