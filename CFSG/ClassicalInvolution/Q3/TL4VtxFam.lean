module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge.CentQuotGen
public import CFSG.ClassicalInvolution.Q3.TL4Conn278Quot
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

namespace Vtx

variable {A B : Type} [Group A] [Group B]

theorem oddCoreOf_map_of_inj (φ : A →* B) (hφ : Function.Injective φ) (H : Subgroup A) :
    oddCoreOf (H.map φ) = (oddCoreOf H).map φ := by
  let e := Subgroup.equivMapOfInjective H φ hφ
  have h1 := CFSG.ComponentClassification.OddCore.equiv_invariant e
  have hcomp : (H.map φ).subtype.comp e.toMonoidHom = φ.comp H.subtype := by
    ext x
    rfl
  unfold oddCoreOf
  change (componentClassificationOddCore ↥(H.map φ)).map (H.map φ).subtype =
    (((componentClassificationOddCore ↥H).map H.subtype).map φ)
  rw [← h1, Subgroup.map_map, Subgroup.map_map, hcomp]

theorem closure_twoElts_map (φ : A →* B) {K : Subgroup A}
    (hK : Subgroup.closure {x : A | x ∈ K ∧ IsPGroup 2 (Subgroup.zpowers x)} = K) :
    Subgroup.closure {x : B | x ∈ K.map φ ∧ IsPGroup 2 (Subgroup.zpowers x)} = K.map φ := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro x hx
    exact hx.1
  · conv_lhs => rw [← hK]
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨x, ⟨hxK, hx2⟩, rfl⟩
    refine Subgroup.subset_closure ⟨⟨x, hxK, rfl⟩, ?_⟩
    rw [← MonoidHom.map_zpowers]
    exact hx2.map _

variable [Finite A] [Finite B]

theorem hypOmegaGen_map_of_inj (φ : A →* B) (hφ : Function.Injective φ) {Λ : Set (Subgroup A)}
    (hΛ : HypOmegaGen Λ)
    (h2 : ∀ K ∈ Λ, Subgroup.closure {x : A | x ∈ K ∧ IsPGroup 2 (Subgroup.zpowers x)} = K)
    (hinv : ConjInvariant ((fun K : Subgroup A => K.map φ) '' Λ)) :
    HypOmegaGen ((fun K : Subgroup A => K.map φ) '' Λ) := by
  have hinj : ∀ K : Subgroup A, ∀ x ∈ K, φ x = 1 → x = 1 :=
    fun _ x _ hx => hφ (hx.trans φ.map_one.symm)
  refine
    { conjInvariant := hinv
      omega1 := ?_
      omega2 := ?_
      omega3 := ?_
      omega4 := ?_
      omega5 := ?_ }
  · rintro _ ⟨K, hK, rfl⟩
    obtain ⟨⟨z, hz⟩, P, hP, hPnc⟩ := hΛ.omega1 K hK
    refine ⟨⟨φ z, isUniqueInvolution_map_of_injOn φ (hinj K) hz⟩, P.map φ,
      isSylow2In_map_of_injOn φ (hinj K) hP, fun hc => hPnc ?_⟩
    let e := Subgroup.equivMapOfInjective P φ hφ
    exact ⟨⟨fun a b => e.injective (by rw [map_mul, map_mul]; exact hc.is_comm.comm _ _)⟩⟩
  · rintro _ ⟨K, hK, rfl⟩
    exact Or.inl (closure_twoElts_map φ (h2 K hK))
  · rintro _ ⟨K, hK, rfl⟩ _ ⟨J, hJ, rfl⟩ Pb Qb hPb hQb
    obtain ⟨P, hP, -⟩ := IsSylow2In.exists_ge (P := K) (IsPGroup.of_bot (p := 2)) bot_le
    obtain ⟨Q', hQ, -⟩ := IsSylow2In.exists_ge (P := J) (IsPGroup.of_bot (p := 2)) bot_le
    obtain ⟨g, -, hg⟩ :=
      Thompson.exists_conj_of_isSylow2In (isSylow2In_map_of_injOn φ (hinj K) hP) hPb
    obtain ⟨g', -, hg'⟩ :=
      Thompson.exists_conj_of_isSylow2In (isSylow2In_map_of_injOn φ (hinj J) hQ) hQb
    have e1 : Nat.card ↥Pb = Nat.card ↥P := by
      rw [← hg, conjSub, Subgroup.card_map_of_injective (MulAut.conj g).injective,
        Subgroup.card_map_of_injective hφ]
    have e2 : Nat.card ↥Qb = Nat.card ↥Q' := by
      rw [← hg', conjSub, Subgroup.card_map_of_injective (MulAut.conj g').injective,
        Subgroup.card_map_of_injective hφ]
    rw [e1, e2]
    exact hΛ.omega3 K hK J hJ P Q' hP hQ
  · rintro _ ⟨K, hK, rfl⟩ _ ⟨J, hJ, rfl⟩ hne
    have hKJ : K ≠ J := fun h => hne (by rw [h])
    obtain ⟨h1, h2'⟩ := hΛ.omega4 K hK J hJ hKJ
    have hcard : Nat.card ↥(K.map φ ⊓ J.map φ) = Nat.card ↥(K ⊓ J) := by
      rw [← Subgroup.map_inf_eq _ _ _ hφ, Subgroup.card_map_of_injective hφ]
    rw [hcard]
    refine ⟨h1, fun hv => ?_⟩
    rw [← Subgroup.map_commutator, oddCoreOf_map_of_inj φ hφ, oddCoreOf_map_of_inj φ hφ,
      ← Subgroup.map_inf_eq _ _ _ hφ]
    exact Subgroup.map_mono (h2' hv)
  · rintro _ ⟨K, hK, rfl⟩ _ ⟨J, hJ, rfl⟩ hne zb hzb vb hvb hnc hv2 hvz
    have hKJ : K ≠ J := fun h => hne (by rw [h])
    obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution hΛ hK
    have hzz : φ z = zb := (isUniqueInvolution_map_of_injOn φ (hinj K) hz).eq hzb
    obtain ⟨v, hvJ, rfl⟩ := hvb
    have hnc' : ¬ ∀ w ∈ J, v * w = w * v := fun h => hnc (by
      rintro _ ⟨w, hw, rfl⟩
      rw [← map_mul, ← map_mul, h w hw])
    have hv2' : IsPGroup 2 (Subgroup.zpowers v) := by
      rw [← MonoidHom.map_zpowers] at hv2
      let e := Subgroup.equivMapOfInjective (Subgroup.zpowers v) φ hφ
      exact hv2.of_injective e.toMonoidHom e.injective
    have hvz' : v * z = z * v := hφ (by rw [map_mul, map_mul, hzz]; exact hvz)
    have hN := hΛ.omega5 K hK J hJ hKJ z hz v hvJ hnc' hv2' hvz'
    rw [mem_normalizer_iff_conjSub_eq] at hN ⊢
    rw [← AscQuot.map_conjSub, hN]

noncomputable def mapEquivOfInf (ψ : A →* B) {K : Subgroup A} (hK : ψ.ker ⊓ K = ⊥) :
    ↥K ≃* ↥(K.map ψ) :=
  MulEquiv.ofBijective (ψ.subgroupMap K) ⟨by
    intro a b hab
    have h1 : ψ (a : A) = ψ (b : A) := congrArg Subtype.val hab
    have h2 : (a : A)⁻¹ * b ∈ ψ.ker ⊓ K :=
      ⟨MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, h1, inv_mul_cancel]),
        K.mul_mem (K.inv_mem a.2) b.2⟩
    rw [hK, Subgroup.mem_bot] at h2
    exact Subtype.ext (inv_mul_eq_one.mp h2), ψ.subgroupMap_surjective K⟩

theorem TypeRFam.map {r : ℕ} {Λ : Set (Subgroup A)} (h : TypeRFam r Λ) (ψ : A →* B)
    (hkc : ψ.ker ≤ Subgroup.center A) (hkK : ∀ K ∈ Λ, ψ.ker ⊓ K = ⊥)
    (hinv : ∀ g : B, ∀ K ∈ Λ, ∃ K' ∈ Λ, conjSub g (K.map ψ) = K'.map ψ)
    (htight : ∀ K ∈ Λ, ∀ z : A, IsUniqueInvolution K z → ∀ g : B, g * ψ z = ψ z * g →
      g ∈ Subgroup.normalizer ((K.map ψ : Subgroup B) : Set B))
    (htwin : ∀ K ∈ Λ, ∀ K' ∈ Λ, ∀ z z' : A, IsUniqueInvolution K z →
      IsUniqueInvolution K' z' → ψ z = ψ z' → K = K') :
    TypeRFam r ((fun K : Subgroup A => K.map ψ) '' Λ) := by
  have hinjOn : ∀ K ∈ Λ, ∀ x ∈ K, ψ x = 1 → x = 1 := fun K hK x hx h1 => by
    have hmem : x ∈ ψ.ker ⊓ K := ⟨h1, hx⟩
    rwa [hkK K hK, Subgroup.mem_bot] at hmem
  have hQ : HypOmegaGen ((fun K : Subgroup A => K.map (QuotientGroup.mk' ψ.ker)) '' Λ) :=
    PhilipHall.QuaternionBridge.CentQ.quotient_hypOmegaGen h.hyp ψ.ker hkc fun K hK => by
      rw [hkK K hK, Subgroup.card_bot]
      exact odd_one
  have hι : ∀ K : Subgroup A,
      (K.map (QuotientGroup.mk' ψ.ker)).map (QuotientGroup.kerLift ψ) = K.map ψ := by
    intro K
    rw [Subgroup.map_map]
    congr 1
  have himg : (fun K' => K'.map (QuotientGroup.kerLift ψ)) ''
      ((fun K : Subgroup A => K.map (QuotientGroup.mk' ψ.ker)) '' Λ) =
      (fun K : Subgroup A => K.map ψ) '' Λ := by
    rw [Set.image_image]
    exact Set.image_congr fun K _ => hι K
  have hcl : ConjInvariant ((fun K : Subgroup A => K.map ψ) '' Λ) := by
    rintro g _ ⟨K, hK, rfl⟩
    obtain ⟨K', hK', e⟩ := hinv g K hK
    exact ⟨K', hK', e.symm⟩
  have hyp : HypOmegaGen ((fun K : Subgroup A => K.map ψ) '' Λ) := by
    rw [← himg]
    refine hypOmegaGen_map_of_inj _ (QuotientGroup.kerLift_injective ψ) hQ ?_ (himg ▸ hcl)
    rintro _ ⟨K, hK, rfl⟩
    exact closure_twoElts_map _ (h.closure_twoElts hK)
  have hzK : ∀ K ∈ Λ, ∀ z, IsUniqueInvolution K z → IsUniqueInvolution (K.map ψ) (ψ z) :=
    fun K hK _ hz => isUniqueInvolution_map_of_injOn ψ (hinjOn K hK) hz
  have hquat : ∀ K ∈ Λ, ∀ Pb : Subgroup B, IsSylow2In Pb (K.map ψ) →
      Nonempty (↥Pb ≃* QuaternionGroup (2 ^ (r - 2))) := by
    intro K hK Pb hPb
    obtain ⟨P, hP, -⟩ := IsSylow2In.exists_ge (P := K) (IsPGroup.of_bot (p := 2)) bot_le
    obtain ⟨e⟩ := h.quat K hK P hP
    obtain ⟨g, -, hg⟩ := Thompson.exists_conj_of_isSylow2In
      (isSylow2In_map_of_injOn ψ (hinjOn K hK) hP) hPb
    subst hg
    have hPK : ψ.ker ⊓ P = ⊥ := eq_bot_iff.mpr ((inf_le_inf_left _ hP.1).trans (hkK K hK).le)
    exact ⟨(((P.map ψ).equivMapOfInjective (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).symm.trans (mapEquivOfInf ψ hPK).symm).trans e⟩
  have htwo : ∀ K ∈ Λ, IsPGroup 2 (↥(K.map ψ) ⧸ classicalInvolutionOddCore ↥(K.map ψ)) := by
    intro K hK
    let e := mapEquivOfInf ψ (hkK K hK)
    exact (h.twoGroup K hK).of_equiv
      (QuotientGroup.congr _ _ e (CFSG.ComponentClassification.OddCore.equiv_invariant e))
  refine
    { hyp := hyp
      cls := ⟨?_, ?_⟩
      twoGroup := ?_
      quat := ?_
      tight := ?_
      noTwins := ?_ }
  · rintro _ ⟨K, hK, rfl⟩
    obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution h.hyp hK
    have hz' := hzK K hK z hz
    refine ⟨ψ z, hz'.mem, orderOf_eq_prime (by rw [pow_two]; exact hz'.sq) hz'.ne_one, ?_⟩
    have hle : K.map ψ ≤ Subgroup.centralizer ({ψ z} : Set B) := by
      rintro _ ⟨x, hx, rfl⟩
      have hxz := Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer hK hz hx)
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, hxz, map_mul]
    have hn : ((K.map ψ).subgroupOf (Subgroup.centralizer ({ψ z} : Set B))).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hle]
      intro g hg
      exact htight K hK z hz g (Subgroup.mem_centralizer_singleton_iff.mp hg)
    exact IsSubnormal.step hle hn (IsSubnormal.refl _)
  · rintro _ ⟨K, hK, rfl⟩ u a b hu hu2 huu ha hb hau hbu
    obtain ⟨P, hP, -⟩ := IsSylow2In.exists_ge (P := K.map ψ) (IsPGroup.of_bot (p := 2)) bot_le
    obtain ⟨e⟩ := hquat K hK P hP
    have : NeZero (2 ^ (r - 2)) := ⟨pow_ne_zero _ (by norm_num)⟩
    exact commOdd_of_quat (htwo K hK) hP e hu hu2 huu ha hb hau hbu
  · rintro _ ⟨K, hK, rfl⟩
    exact htwo K hK
  · rintro _ ⟨K, hK, rfl⟩ Pb hPb
    exact hquat K hK Pb hPb
  · rintro _ ⟨K, hK, rfl⟩ w hw g hg
    obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution h.hyp hK
    obtain rfl : w = ψ z := hw.eq (hzK K hK z hz)
    exact htight K hK z hz g (Subgroup.mem_centralizer_singleton_iff.mp hg)
  · rintro _ ⟨K, hK, rfl⟩ _ ⟨⟨K', hK', rfl⟩, w, hw, hw'⟩
    obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution h.hyp hK
    obtain ⟨z', hz'⟩ := Sec6Gen.exists_uniqueInvolution h.hyp hK'
    have e1 : w = ψ z := hw.eq (hzK K hK z hz)
    have e2 : w = ψ z' := hw'.eq (hzK K' hK' z' hz')
    rw [htwin K hK K' hK' z z' hz hz' (e1.symm.trans e2)]

end Vtx

end CFSG.ClassicalInvolution.Q3.TL4
