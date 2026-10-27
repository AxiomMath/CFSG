module

public import CFSG.ClassicalInvolution.Asc77.AscFusionParity
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSASwappedCentralProduct
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.ClassicalInvolution.Asc77.AscFusion

open CFSG

variable {H : Type} [Group H] [Finite H]

@[expose] noncomputable def oddQuotAut (σ : MulAut H) : MulAut (H ⧸ pPrimeCore 2 H) :=
  QuotientGroup.congr _ _ σ
    (Subgroup.characteristic_iff_map_eq.mp (pPrimeCore_characteristic (p := 2)) σ)

omit [Finite H] in
theorem oddQuotAut_mk (σ : MulAut H) (x : H) :
    oddQuotAut σ (x : H ⧸ pPrimeCore 2 H) = ((σ x : H) : H ⧸ pPrimeCore 2 H) := rfl

@[expose] def fixSub (σ : MulAut H) : Subgroup H :=
  MonoidHom.eqLocus σ.toMonoidHom (MonoidHom.id H)

omit [Finite H] in
theorem mem_fixSub {σ : MulAut H} {x : H} : x ∈ fixSub σ ↔ σ x = x := Iff.rfl

theorem odd_card_pPrimeCore (H : Type) [Group H] [Finite H] : Odd (Nat.card (pPrimeCore 2 H)) :=
  (Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := H)))

theorem exists_fixed_lift (σ : MulAut H) (hσ : ∀ x, σ (σ x) = x) {y : H ⧸ pPrimeCore 2 H}
    (hy : oddQuotAut σ y = y) :
    ∃ x : H, (x : H ⧸ pPrimeCore 2 H) = y ∧ σ x = x := by
  obtain ⟨x₀, rfl⟩ := QuotientGroup.mk_surjective y
  let F := {x : H // (x : H ⧸ pPrimeCore 2 H) = (x₀ : H ⧸ pPrimeCore 2 H)}
  have hcard : Nat.card F = Nat.card (QuotientGroup.mk' (pPrimeCore 2 H)).ker :=
    Nat.card_congr ((QuotientGroup.mk' (pPrimeCore 2 H)).fiberEquivKer x₀)
  rw [QuotientGroup.ker_mk'] at hcard
  have hF : Finite F := inferInstance
  have hodd : Odd (Nat.card F) := hcard ▸ odd_card_pPrimeCore H
  let φ : F → F := fun x => ⟨σ x, by
    have h1 := congrArg (oddQuotAut σ) x.2
    rw [oddQuotAut_mk] at h1
    exact h1.trans hy⟩
  have hφ : Function.Involutive φ := fun x => Subtype.ext (hσ x)
  obtain ⟨x, hx⟩ := exists_fixedPoint_of_involutive hodd hφ
  exact ⟨x, x.2, congrArg Subtype.val hx⟩

open scoped commutatorElement

theorem exists_perfect_lift_fixed (σ : MulAut H) (hσ : ∀ x, σ (σ x) = x)
    {T : Subgroup (H ⧸ pPrimeCore 2 H)} (hTperf : ⁅T, T⁆ = T)
    (hTfix : ∀ y ∈ T, oddQuotAut σ y = y)
    (hTnorm : ∀ y : H ⧸ pPrimeCore 2 H, oddQuotAut σ y = y → ∀ t ∈ T, y * t * y⁻¹ ∈ T) :
    ∃ L : Subgroup H, L ≤ fixSub σ ∧ ⁅L, L⁆ = L ∧
      L.map (QuotientGroup.mk' (pPrimeCore 2 H)) = T ∧
      (L.subgroupOf (fixSub σ)).IsSubnormal ∧
      ∀ x ∈ fixSub σ, IsPGroup 2 (Subgroup.zpowers x) →
        QuotientGroup.mk' (pPrimeCore 2 H) x ∈ T → x ∈ L := by
  classical
  set π : H →* H ⧸ pPrimeCore 2 H := QuotientGroup.mk' (pPrimeCore 2 H) with hπ
  set F : Subgroup H := fixSub σ with hF
  let πF : ↥F →* H ⧸ pPrimeCore 2 H := π.comp F.subtype
  let ΛF : Subgroup ↥F := T.comap πF
  have hπF : ∀ x : ↥F, oddQuotAut σ (πF x) = πF x := fun x => by
    have hx : σ (x : H) = x := x.2
    show oddQuotAut σ ((x : H) : H ⧸ pPrimeCore 2 H) = ((x : H) : H ⧸ pPrimeCore 2 H)
    rw [oddQuotAut_mk, hx]
  have hΛn : ΛF.Normal := ⟨fun x hx h => by
    have := hTnorm (πF h) (hπF h) (πF x) hx
    simpa [ΛF, Subgroup.mem_comap, map_mul, map_inv] using this⟩
  let f : ↥ΛF →* ↥T := (πF.comp ΛF.subtype).codRestrict T (fun x => x.2)
  have hf : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hxy, hxσ⟩ := exists_fixed_lift σ hσ (hTfix y hy)
    refine ⟨⟨⟨x, hxσ⟩, by simpa [ΛF, Subgroup.mem_comap, πF, hπ] using hxy ▸ hy⟩, ?_⟩
    apply Subtype.ext
    simpa [f, πF, hπ] using hxy
  have : Group.IsPerfect ↥T := Subgroup.isPerfect_iff.mpr hTperf
  have hder : ∀ n, (derivedSeries ↥ΛF n).map f = ⊤ := fun n => by
    rw [map_derivedSeries_eq hf n, Group.IsPerfect.derivedSeries_eq_top]
  obtain ⟨n, hn⟩ : ∃ n, derivedSeries ↥ΛF (n + 1) = derivedSeries ↥ΛF n := by
    obtain ⟨a, b, hab, hEq⟩ := Finite.exists_ne_map_eq_of_infinite
      (fun k : ℕ => derivedSeries ↥ΛF k)
    wlog hlt : a < b generalizing a b
    · exact this b a hab.symm hEq.symm (lt_of_le_of_ne (not_lt.mp hlt) hab.symm)
    refine ⟨a, le_antisymm (derivedSeries_antitone ↥ΛF (Nat.le_succ a)) ?_⟩
    calc derivedSeries ↥ΛF a = derivedSeries ↥ΛF b := hEq
      _ ≤ derivedSeries ↥ΛF (a + 1) := derivedSeries_antitone ↥ΛF hlt
  set W : Subgroup ↥ΛF := derivedSeries ↥ΛF n with hW
  have hWperf : ⁅W, W⁆ = W := by
    rw [← derivedSeries_succ]
    exact hn
  have hWn : W.Normal := inferInstance
  refine ⟨(W.map ΛF.subtype).map F.subtype, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    exact (w : ↥F).2
  · rw [← Subgroup.map_commutator, ← Subgroup.map_commutator, hWperf]
  · calc ((W.map ΛF.subtype).map F.subtype).map π
        = W.map (T.subtype.comp f) := by
          simp only [Subgroup.map_map]
          congr 1
      _ = (W.map f).map T.subtype := (Subgroup.map_map _ _ _).symm
      _ = T := by rw [hder n, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  · rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective F.subtype_injective]
    exact Subgroup.IsSubnormal.trans' hWn.isSubnormal hΛn.isSubnormal
  ·
    intro x hxF hx2 hxT
    have hxΛ : (⟨x, hxF⟩ : ↥F) ∈ ΛF := hxT
    set x' : ↥ΛF := ⟨⟨x, hxF⟩, hxΛ⟩ with hx'
    have hWf : W.map f = ⊤ := hder n
    have hodd : Odd (Nat.card (↥ΛF ⧸ W)) := by
      let φ : ↥f.ker →* ↥ΛF ⧸ W := (QuotientGroup.mk' W).comp f.ker.subtype
      have hφ : Function.Surjective φ := by
        intro c
        obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective c
        have hl : f l ∈ W.map f := by rw [hWf]; trivial
        obtain ⟨w, hw, hwl⟩ := hl
        refine ⟨⟨l * w⁻¹, ?_⟩, ?_⟩
        · rw [MonoidHom.mem_ker, map_mul, map_inv, hwl, mul_inv_cancel]
        · show (QuotientGroup.mk' W) (l * w⁻¹) = (l : ↥ΛF ⧸ W)
          have hw1 : QuotientGroup.mk' W w = 1 := (QuotientGroup.eq_one_iff w).mpr hw
          rw [map_mul, map_inv, hw1, inv_one, mul_one]
          rfl
      have hdvd : Nat.card (↥ΛF ⧸ W) ∣ Nat.card f.ker := Subgroup.card_dvd_of_surjective hφ
      have hker : ∀ k : ↥f.ker, (((k : ↥ΛF) : ↥F) : H) ∈ pPrimeCore 2 H := by
        intro k
        have h1 := congrArg Subtype.val (MonoidHom.mem_ker.mp k.2)
        exact (QuotientGroup.eq_one_iff _).mp h1
      let g : ↥f.ker →* ↥(pPrimeCore 2 H) :=
        (F.subtype.comp (ΛF.subtype.comp f.ker.subtype)).codRestrict _ hker
      have hg : Function.Injective g := by
        intro a b hab
        have := congrArg Subtype.val hab
        exact Subtype.ext (Subtype.ext (Subtype.ext this))
      have hodd' : Odd (Nat.card f.ker) :=
        Odd.of_dvd_nat (odd_card_pPrimeCore H) (Subgroup.card_dvd_of_injective g hg)
      exact Odd.of_dvd_nat hodd' hdvd
    have hx'W : x' ∈ W := by
      obtain ⟨k, hk⟩ := hx2.exists_card_eq
      have hox : orderOf x = 2 ^ k := by rw [← Nat.card_zpowers]; exact hk
      have hox' : orderOf x' = 2 ^ k := by
        rw [← hox, ← Subgroup.orderOf_coe x', ← Subgroup.orderOf_coe (x' : ↥F)]
      have h1 : orderOf (QuotientGroup.mk' W x') ∣ 2 ^ k :=
        hox' ▸ orderOf_map_dvd (QuotientGroup.mk' W) x'
      have h2 : orderOf (QuotientGroup.mk' W x') ∣ Nat.card (↥ΛF ⧸ W) := orderOf_dvd_natCard _
      have hcop : Nat.Coprime (2 ^ k) (Nat.card (↥ΛF ⧸ W)) :=
        Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
      have h3 : orderOf (QuotientGroup.mk' W x') = 1 :=
        Nat.eq_one_of_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd h1 h2)
      exact (QuotientGroup.eq_one_iff x').mp (orderOf_eq_one_iff.mp h3)
    exact ⟨(x' : ↥F), ⟨x', hx'W, rfl⟩, rfl⟩

theorem isQuasisimple_of_mulEquiv {G K : Type*} [Group G] [Group K] (e : G ≃* K)
    (h : CFSG.IsQuasisimple K) : CFSG.IsQuasisimple G :=
  CFSG.ComponentClassification.CatalogueBAlternating.quasisimple_iff_native.mpr
    (CFSG.ComponentClassification.Components.quasisimple_of_equiv e
      (CFSG.ComponentClassification.CatalogueBAlternating.quasisimple_iff_native.mp h))

theorem isQuasisimple_oddQuot_of_lift {L : Subgroup H} {T : Subgroup (H ⧸ pPrimeCore 2 H)}
    (hL : L.map (QuotientGroup.mk' (pPrimeCore 2 H)) = T) (hT : CFSG.IsQuasisimple T)
    (hcore : pPrimeCore 2 T = ⊥) : CFSG.IsQuasisimple (L ⧸ pPrimeCore 2 L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π : H →* H ⧸ pPrimeCore 2 H := QuotientGroup.mk' (pPrimeCore 2 H) with hπ
  let φ : ↥L →* ↥T := (π.comp L.subtype).codRestrict T
    (fun x => hL ▸ ⟨x, x.2, rfl⟩)
  have hφ : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    rw [← hL] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩
  have hker : pPrimeCore 2 L = φ.ker := by
    apply le_antisymm
    · intro x hx
      have h1 : φ x ∈ (pPrimeCore 2 L).map φ := ⟨x, hx, rfl⟩
      have h2 := map_pPrimeCore_le φ hφ h1
      rw [hcore] at h2
      exact h2
    · have hkn : φ.ker.Normal := MonoidHom.normal_ker φ
      have hle : φ.ker.map L.subtype ≤ pPrimeCore 2 H := by
        rintro _ ⟨x, hx, rfl⟩
        have h3 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
        exact (QuotientGroup.eq_one_iff _).mp h3
      have hcard : Nat.card φ.ker ∣ Nat.card (pPrimeCore 2 H) := by
        rw [← Subgroup.card_map_of_injective L.subtype_injective]
        exact Subgroup.card_dvd_of_le hle
      have hcop : Nat.Coprime 2 (Nat.card φ.ker) :=
        Nat.Coprime.coprime_dvd_right hcard pPrimeCore_coprime_card
      exact le_sSup ⟨hkn, hcop⟩
  exact isQuasisimple_of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ)) hT

theorem exists_diagonal_lift' (σ : MulAut H) (hσ : ∀ x, σ (σ x) = x) {A₀ B₀ : Subgroup H}
    (hAB : A₀.map σ.toMonoidHom = B₀) (hsup : A₀ ⊔ B₀ = ⊤)
    (hcomm : ∀ x ∈ A₀, ∀ y ∈ B₀, ⁅x, y⁆ ∈ pPrimeCore 2 H)
    (hA : CFSG.IsQuasisimple (A₀.map (QuotientGroup.mk' (pPrimeCore 2 H))))
    (hAcore : pPrimeCore 2 (A₀.map (QuotientGroup.mk' (pPrimeCore 2 H))) = ⊥) :
    ∃ L : Subgroup H, L ≤ fixSub σ ∧ ⁅L, L⁆ = L ∧ CFSG.IsQuasisimple (L ⧸ pPrimeCore 2 L) ∧
      (L.subgroupOf (fixSub σ)).IsSubnormal ∧
      (∀ x ∈ A₀, ∃ ℓ ∈ L, (ℓ : H ⧸ pPrimeCore 2 H) = ((x * σ x : H) : H ⧸ pPrimeCore 2 H)) ∧
      ∀ g ∈ fixSub σ, IsPGroup 2 (Subgroup.zpowers g) →
        (∃ x ∈ A₀, (g : H ⧸ pPrimeCore 2 H) = ((x * σ x : H) : H ⧸ pPrimeCore 2 H)) → g ∈ L := by
  classical
  set π : H →* H ⧸ pPrimeCore 2 H := QuotientGroup.mk' (pPrimeCore 2 H) with hπ
  set σ' : MulAut (H ⧸ pPrimeCore 2 H) := oddQuotAut σ with hσ'
  have hσ'σ' : ∀ y : H ⧸ pPrimeCore 2 H, σ' (σ' y) = y := by
    intro y
    induction y using QuotientGroup.induction_on with
    | H x => simp only [hσ', oddQuotAut_mk, hσ]
  set A : Subgroup (H ⧸ pPrimeCore 2 H) := A₀.map π with hAdef
  set B : Subgroup (H ⧸ pPrimeCore 2 H) := B₀.map π with hBdef
  have hAB' : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    have h1 := hcomm x hx y hy
    have h2 : π ⁅x, y⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr h1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h2
    exact h2
  have hAσ : A.map σ'.toMonoidHom = B := by
    rw [hAdef, hBdef, Subgroup.map_map, ← hAB, Subgroup.map_map]
    congr 1
  have hBσ : B.map σ'.toMonoidHom = A := by
    rw [← hAσ, Subgroup.map_map]
    have : σ'.toMonoidHom.comp σ'.toMonoidHom = MonoidHom.id _ := by
      ext y; exact hσ'σ' y
    rw [this, Subgroup.map_id]
  have hKtop : A ⊔ B = ⊤ := by
    rw [hAdef, hBdef, ← Subgroup.map_sup, hsup, Subgroup.map_top_of_surjective _
      (QuotientGroup.mk'_surjective _)]
  let α : ↥(A ⊔ B) ≃* ↥(A ⊔ B) :=
    (MulEquiv.subgroupCongr hKtop).trans (Subgroup.topEquiv.trans (σ'.trans
      (Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hKtop.symm))))
  have hαval : ∀ k : ↥(A ⊔ B), ((α k : ↥(A ⊔ B)) : H ⧸ pPrimeCore 2 H) =
      σ' (k : H ⧸ pPrimeCore 2 H) := fun k => rfl
  have hα : ∀ k : ↥(A ⊔ B), α (α k) = k := fun k => by
    apply Subtype.ext
    rw [hαval, hαval, hσ'σ']
  have hσA : ∀ x ∈ A, σ' x ∈ B := fun x hx => (SetLike.ext_iff.mp hAσ _).mp ⟨x, hx, rfl⟩
  have hσB : ∀ x ∈ B, σ' x ∈ A := fun x hx => (SetLike.ext_iff.mp hBσ _).mp ⟨x, hx, rfl⟩
  have hαA : (A.subgroupOf (A ⊔ B)).map α.toMonoidHom = B.subgroupOf (A ⊔ B) := by
    ext k
    constructor
    · rintro ⟨k', hk', rfl⟩
      show ((α k' : ↥(A ⊔ B)) : H ⧸ pPrimeCore 2 H) ∈ B
      rw [hαval]
      exact hσA _ hk'
    · intro hk
      exact ⟨α k, hσB _ hk, hα k⟩
  let C : Subgroup ↥(A ⊔ B) := MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id _)
  have hC : ∀ k, k ∈ C ↔ α k = k := fun k => Iff.rfl
  obtain ⟨-, hDcen, -, δ, hδ, -, hΔqs, hCdec, -, hcoreΔ, -, -, -, -, -, -⟩ :=
    CFSG.ComponentClassification.UnbalancedGS.swapped_central_product_fixed_layer A B hAB' hA
      hAcore α hα hαA C hC
  set T : Subgroup (H ⧸ pPrimeCore 2 H) := δ.range.map (A ⊔ B).subtype with hT
  have hΔle : δ.range ≤ C := by
    rw [hCdec]
    exact le_sup_left
  have hTperf : ⁅T, T⁆ = T := by
    have h1 : ⁅δ.range, δ.range⁆ = δ.range :=
      Subgroup.isPerfect_iff.mp hΔqs.1
    rw [hT, ← Subgroup.map_commutator, h1]
  have hTfix : ∀ y ∈ T, σ' y = y := by
    rintro _ ⟨d, hd, rfl⟩
    have h1 := (hC d).mp (hΔle hd)
    have h2 := congrArg Subtype.val h1
    rw [hαval] at h2
    exact h2
  have hTnorm : ∀ y : H ⧸ pPrimeCore 2 H, σ' y = y → ∀ t ∈ T, y * t * y⁻¹ ∈ T := by
    intro y hy t ht
    have hyK : y ∈ A ⊔ B := by
      rw [hKtop]
      exact Subgroup.mem_top y
    have hyC : (⟨y, hyK⟩ : ↥(A ⊔ B)) ∈ C := by
      rw [hC]
      exact Subtype.ext (by rw [hαval]; exact hy)
    have hnorm : C ≤ Subgroup.normalizer (δ.range : Set ↥(A ⊔ B)) := by
      rw [hCdec]
      refine sup_le Subgroup.le_normalizer ?_
      intro z hz
      rw [Subgroup.mem_normalizer_iff]
      intro d
      have hzc : ((z : ↥(A ⊔ B)) : H ⧸ pPrimeCore 2 H) ∈ A ⊓ B := hz.1
      have hcomm' := hDcen _ hzc (d : H ⧸ pPrimeCore 2 H) d.2
      have : (z : ↥(A ⊔ B)) * d * (z : ↥(A ⊔ B))⁻¹ = d := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
        rw [hcomm', mul_inv_cancel_right]
      rw [this]
    obtain ⟨d, hd, rfl⟩ := ht
    have := (Subgroup.mem_normalizer_iff.mp (hnorm hyC) d).mp hd
    exact ⟨_, this, rfl⟩
  obtain ⟨L, hLfix, hLperf, hLmap, hLsub, hL2⟩ :=
    exists_perfect_lift_fixed σ hσ hTperf hTfix hTnorm
  have hTqs : CFSG.IsQuasisimple T :=
    isQuasisimple_of_mulEquiv
      (δ.range.equivMapOfInjective (A ⊔ B).subtype (A ⊔ B).subtype_injective).symm hΔqs
  have hTcore : pPrimeCore 2 T = ⊥ := by
    have e := δ.range.equivMapOfInjective (A ⊔ B).subtype (A ⊔ B).subtype_injective
    have h1 := pPrimeCore_map_iso 2 e
    rw [hcoreΔ, Subgroup.map_bot] at h1
    exact h1.symm
  have hdiagT : ∀ x ∈ A₀, π x * σ' (π x) ∈ T := by
    intro x hx
    have hxA : π x ∈ A := ⟨x, hx, rfl⟩
    let u : ↥A := ⟨π x, hxA⟩
    refine ⟨δ u, ⟨u, rfl⟩, ?_⟩
    rw [hδ u]
    simp [hαval, u]
  refine ⟨L, hLfix, hLperf, isQuasisimple_oddQuot_of_lift hLmap hTqs hTcore, hLsub, ?_, ?_⟩
  · intro x hx
    have hdiag := hdiagT x hx
    rw [← hLmap] at hdiag
    obtain ⟨ℓ, hℓ, hℓx⟩ := hdiag
    refine ⟨ℓ, hℓ, ?_⟩
    show π ℓ = π (x * σ x)
    rw [map_mul]
    exact hℓx.trans rfl
  · intro g hgF hg2 ⟨x, hx, hgx⟩
    refine hL2 g hgF hg2 ?_
    have h1 := hdiagT x hx
    have h2 : π g = π x * σ' (π x) := by
      have h3 : π g = ((g : H) : H ⧸ pPrimeCore 2 H) := rfl
      rw [h3, hgx, QuotientGroup.mk_mul]
      rfl
    rw [h2]
    exact h1

theorem exists_diagonal_lift (σ : MulAut H) (hσ : ∀ x, σ (σ x) = x) {A₀ B₀ : Subgroup H}
    (hAB : A₀.map σ.toMonoidHom = B₀) (hsup : A₀ ⊔ B₀ = ⊤)
    (hcomm : ∀ x ∈ A₀, ∀ y ∈ B₀, ⁅x, y⁆ ∈ pPrimeCore 2 H)
    (hA : CFSG.IsQuasisimple (A₀.map (QuotientGroup.mk' (pPrimeCore 2 H))))
    (hAcore : pPrimeCore 2 (A₀.map (QuotientGroup.mk' (pPrimeCore 2 H))) = ⊥) :
    ∃ L : Subgroup H, L ≤ fixSub σ ∧ ⁅L, L⁆ = L ∧ CFSG.IsQuasisimple (L ⧸ pPrimeCore 2 L) ∧
      (L.subgroupOf (fixSub σ)).IsSubnormal ∧
      ∀ x ∈ A₀, ∃ ℓ ∈ L, (ℓ : H ⧸ pPrimeCore 2 H) = ((x * σ x : H) : H ⧸ pPrimeCore 2 H) := by
  obtain ⟨L, h1, h2, h3, h4, h5, -⟩ := exists_diagonal_lift' σ hσ hAB hsup hcomm hA hAcore
  exact ⟨L, h1, h2, h3, h4, h5⟩

end CFSG.ClassicalInvolution.Asc77.AscFusion
