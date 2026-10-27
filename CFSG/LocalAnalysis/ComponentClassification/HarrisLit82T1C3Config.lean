module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1C3Bar
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitElemAb
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Solomon
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1C3Tools2
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1FourGroup

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Assembly.LowTwoRank CFSG.ComponentClassification.UnbalancedLayer
open CFSG.LieType.Universal.Spin CliffordAlgebra
open scoped MatrixGroups

structure C3Inputs : Prop where
  ci : GSLit.ClassicalInvolutionInput
  ga : TBLit.GriessMultipliersAllModels
  ident : Harris81Lemma35IdentFact
  known : KnownRow
  solomon : Solomon74SpinSevenAsUsed
  l410 : Harris82Lemma410Rest
  u1 : Harris82Lemma411U1
  u2 : Harris82Lemma411U2
  u3 : Harris82Lemma411U3
  u4 : Harris82Lemma411U4
  l51e : Harris82Lemma51e
  l58 : Harris82Lemma58Spin7

structure C3Config (G : Type) [Group G] [Finite G] (z : G) (L : Subgroup G) (p f : ℕ) :
    Prop where
  simple : IsSimpleGroup G
  nonab : ∃ a b : G, a * b ≠ b * a
  kProper : Assembly.KProper Blueprint.Catalog G
  notCat : ¬ Blueprint.Catalog G
  hz : orderOf z = 2
  hL : IsTwoComponentIn L (centralizer {z})
  hzL : z ∈ L
  hp : p.Prime
  hp2 : p ≠ 2
  h5 : 5 ≤ p ^ f
  hcov : IsCoverOf .POmegaOdd 3 p f 2 (↥L ⧸ pPrimeCore 2 ↥L)
  hM : IsMTypeSchur p ↥L

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem centralizer_ne_top_of_simple [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    {z : G} (hz : orderOf z = 2) : centralizer ({z} : Set G) ≠ ⊤ := by
  intro htop
  have hZ : center G = ⊥ := CatLeaf.center_eq_bot_of_simple hnonab
  have hzc : z ∈ center G := by
    rw [mem_center_iff]
    intro g
    have hg : g ∈ centralizer ({z} : Set G) := htop ▸ mem_top g
    exact mem_centralizer_singleton_iff.mp hg
  rw [hZ, mem_bot] at hzc
  rw [hzc, orderOf_one] at hz
  exact absurd hz (by norm_num)

theorem one_le_of_five_le_pow {p k : ℕ} (h5 : 5 ≤ p ^ k) : 1 ≤ k :=
  Nat.pos_of_ne_zero fun h => by simp [h] at h5

variable {z : G} {L : Subgroup G} {p f : ℕ}

theorem C3Config.pumpdown_Q (h : C3Config G z L p f) {τ : G} (hτ : orderOf τ = 2)
    (hτQ : τ ∈ coreActionKernel L) :
    IsTwoComponentIn (centralizerResidual L τ) (centralizer {z} ⊓ centralizer {τ}) ∧
      Nonempty (↥(centralizerResidual L τ) ⧸ pPrimeCore 2 ↥(centralizerResidual L τ) ≃* Bar L) ∧
      ∀ w ∈ L, w ∈ centralizer {τ} → (∃ n : ℕ, w ^ 2 ^ n = 1) → w ∈ centralizerResidual L τ := by
  have htN : τ ∈ normalizer (L : Set G) := (mem_coreActionKernel.mp hτQ).1
  have htriv : barAction L ⟨τ, htN⟩ = 1 :=
    MonoidHom.mem_ker.mp ((mem_ker_barAction L ⟨τ, htN⟩).mpr hτQ)
  have ht2 : IsPGroup 2 (zpowers τ) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hτ, pow_one])
  obtain ⟨hJ, he⟩ := pumpdown h.hL htN ht2 htriv
  exact ⟨hJ, he, fun w hwL hwτ ⟨n, hn⟩ =>
    mem_centralizerResidual_of_two_pow htN ht2 h.hL.2.2.2.1 htriv hwL hwτ hn⟩

theorem C3Config.mem_pumpdown_Q (h : C3Config G z L p f) {τ : G} (hτ : orderOf τ = 2)
    (hτQ : τ ∈ coreActionKernel L) (hτz : τ ∈ centralizer {z}) : z ∈ centralizerResidual L τ :=
  (h.pumpdown_Q hτ hτQ).2.2 z h.hzL
    (mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hτz).symm)
    ⟨1, by rw [pow_one, ← h.hz, pow_orderOf_eq_one]⟩

section Certified


theorem false_of_fourGroup (hI : C3Inputs) [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hK : Assembly.KProper Blueprint.Catalog G)
    (hcat : ¬ Blueprint.Catalog G) {z₁ z₂ : G} (hz₁ : orderOf z₁ = 2) (hz₂ : orderOf z₂ = 2)
    (hne : z₁ ≠ z₂) (hc : z₁ * z₂ = z₂ * z₁) {L₁ L₂ : Subgroup G}
    (hL₁ : IsTwoComponentIn L₁ (centralizer {z₁} ⊓ centralizer {z₂}))
    (hL₂ : IsTwoComponentIn L₂ (centralizer {z₁} ⊓ centralizer {z₂})) (hz₁L : z₁ ∈ L₁)
    (hz₂L : z₂ ∈ L₂) {p k r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ k)
    (hsl : IsSLTwoOver (p ^ k) (↥L₁ ⧸ pPrimeCore 2 ↥L₁)) (h5r : 5 ≤ p ^ r)
    (hM₂ : IsMTypeSchur p ↥L₂)
    (hcov₂ : IsCoverOf .POmegaOdd 3 p r 2 (↥L₂ ⧸ pPrimeCore 2 ↥L₂)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz₁1 : z₁ ≠ 1 := fun h => by rw [h, orderOf_one] at hz₁; exact absurd hz₁ (by norm_num)
  have hz₂1 : z₂ ≠ 1 := fun h => by rw [h, orderOf_one] at hz₂; exact absurd hz₂ (by norm_num)
  have hz₁sq : z₁ ^ 2 = 1 := hz₁ ▸ pow_orderOf_eq_one z₁
  have hz₂sq : z₂ ^ 2 = 1 := hz₂ ▸ pow_orderOf_eq_one z₂
  set W := zpowers z₁ ⊔ zpowers z₂ with hWdef
  have hW4 : Nat.card W = 4 :=
    (FooteLit.isKleinFour_sup_zpowers hz₁sq hz₂sq hz₁1 hz₂1 hne.symm hc).card_four
  have hcomm : ∀ x ∈ zpowers z₁, ∀ y ∈ zpowers z₂, x * y = y * x := by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy
    exact (Commute.zpow_zpow (show Commute z₁ z₂ from hc) i j).eq
  have hW2 : ∀ a ∈ W, a * a = 1 := fun a ha => by
    rw [← sq]
    exact FooteLit.sq_eq_one_of_mem_sup (fun x hx => FooteLit.sq_eq_one_of_mem_zpowers hz₁sq hx)
      (fun x hx => FooteLit.sq_eq_one_of_mem_zpowers hz₂sq hx) hcomm a ha
  have hz₁W : z₁ ∈ W := mem_sup_left (mem_zpowers z₁)
  have hz₂W : z₂ ∈ W := mem_sup_right (mem_zpowers z₂)
  have hz₂n : z₂ ∉ zpowers z₁ := fun h =>
    (T23.eq_one_or_eq_of_mem_zpowers (hW2 z₁ hz₁W) h).elim hz₂1 hne.symm
  obtain ⟨-, -, -, hCW⟩ := L35.centralizer_eq_inf hW2 hW4 hz₁W hz₁1 hz₂W hz₂n
  have hL₁W : IsTwoComponentIn L₁ (centralizer (W : Set G)) := hCW ▸ hL₁
  have hL₂W : IsTwoComponentIn L₂ (centralizer (W : Set G)) := hCW ▸ hL₂
  obtain ⟨hKc, hL₁K, hL₂K, -, hz₂K, hz₂Z⟩ := fourGroup_slTwo hI.ci hI.ga hI.ident hnonab hK hcat
    hW2 hW4 hz₁W hz₂W hz₁1 hz₂1 hne hL₁W hL₂W hz₁L hz₂L hp hp2 (one_le_of_five_le_pow h5) h5 hsl
  set K := GSThmB.conjClosure L₁ (GSThmB.layerIn (centralizer {z₁})) with hKdef
  have hKtop : K ≠ ⊤ := fun h => centralizer_ne_top_of_simple hnonab hz₁ (top_unique (h ▸ hKc.1))
  have hle : K ⊓ centralizer {z₂} ≤ centralizer {z₁} ⊓ centralizer {z₂} :=
    inf_le_inf_right _ hKc.1
  have hL₂K' : IsTwoComponentIn L₂ (K ⊓ centralizer {z₂}) :=
    ⟨le_inf hL₂K (hL₂.1.trans inf_le_right), L219.isSubnormal_subgroupOf_of_le hle hL₂.2.1,
      hL₂.2.2⟩
  have hL₁K' : IsTwoComponentIn L₁ (K ⊓ centralizer {z₂}) :=
    ⟨le_inf hL₁K (hL₁.1.trans inf_le_right), L219.isSubnormal_subgroupOf_of_le hle hL₁.2.1,
      hL₁.2.2⟩
  have hI₂ : InductionTypeField p ↥L₂ := ⟨r, one_le_of_five_le_pow h5r, .inl hcov₂⟩
  have hch := isSimpleChevalleyOver_of_knownRow hI.known hK hKtop hKc.2.2 hz₂K hz₂ hL₂K' hz₂L
    hp hp2 hM₂ hI₂
  have hz₁K : z₁ ∈ K := hL₁K hz₁L
  have hz₁c : (⟨z₁, hz₁K⟩ : ↥K) ∈ center ↥K := mem_center_of_le_centralizer hKc.1 hz₁K
  have hz₁' : orderOf (⟨z₁, hz₁K⟩ : ↥K) = 2 := by rw [Subgroup.orderOf_mk]; exact hz₁
  have hz₂' : orderOf (⟨z₂, hz₂K⟩ : ↥K) = 2 := by rw [Subgroup.orderOf_mk]; exact hz₂
  let e₁ : ↥(L₁.subgroupOf K) ≃* ↥L₁ := subgroupOfEquivOfLe hL₁K
  let e₂ : ↥(L₂.subgroupOf K) ≃* ↥L₂ := subgroupOfEquivOfLe hL₂K
  have hsl' : IsSLTwoOver (p ^ k) (↥(L₁.subgroupOf K) ⧸ pPrimeCore 2 ↥(L₁.subgroupOf K)) :=
    isSLTwoOver_of_mulEquiv' (QuotientGroup.congr _ _ e₁.symm (pPrimeCore_map_iso 2 e₁.symm)) hsl
  have hcov₂' : IsCoverOf .POmegaOdd 3 p r 2
      (↥(L₂.subgroupOf K) ⧸ pPrimeCore 2 ↥(L₂.subgroupOf K)) :=
    isCoverOf_of_mulEquiv (QuotientGroup.congr _ _ e₂.symm (pPrimeCore_map_iso 2 e₂.symm)) hcov₂
  exact hI.l58 ↥K hKc.2.2 p hp hp2 hch ⟨z₁, hz₁K⟩ ⟨z₂, hz₂K⟩ hz₁' hz₁c hz₂' hz₂Z
    (L₁.subgroupOf K) (L₂.subgroupOf K) (isTwoComponentIn_subgroupOf_inf hz₂K hL₁K')
    (isTwoComponentIn_subgroupOf_inf hz₂K hL₂K') hz₁L hz₂L k h5 hsl' r h5r hcov₂'

theorem C3Config.false_of_slTwo (hI : C3Inputs) (h : C3Config G z L p f) {j : G}
    (hj : orderOf j = 2) (hjz : j ∈ centralizer {z}) (hjL : j ∉ L) {J : Subgroup G}
    (hJ : IsTwoComponentIn J (centralizer {z} ⊓ centralizer {j})) (hjJ : j ∈ J) {r : ℕ}
    (h5r : 5 ≤ p ^ r) (hsl : IsSLTwoOver (p ^ r) (↥J ⧸ pPrimeCore 2 ↥J)) : False := by
  have := h.simple
  rcases lemma221 hj hjz hJ hjJ h.hL with hle | hle
  · exact hjL (hle hjJ)
  · have hjQ : j ∈ coreActionKernel L := hle hjJ
    obtain ⟨hJ', ⟨e⟩, -⟩ := h.pumpdown_Q hj hjQ
    have hzJ' := h.mem_pumpdown_Q hj hjQ hjz
    have hzj : j * z = z * j := mem_centralizer_singleton_iff.mp hjz
    have hne : j ≠ z := fun he => hjL (he ▸ h.hzL)
    exact false_of_fourGroup hI h.nonab h.kProper h.notCat hj h.hz hne hzj
      (inf_comm (centralizer {z}) (centralizer {j}) ▸ hJ)
      (inf_comm (centralizer {z}) (centralizer {j}) ▸ hJ') hjJ hzJ' h.hp h.hp2 h5r hsl h.h5
      (isMTypeSchur_of_bar_equiv h.hM hJ'.2.2 e.symm) (isCoverOf_of_mulEquiv e.symm h.hcov)

theorem C3Config.eq_of_isCoverOf (hI : C3Inputs) (h : C3Config G z L p f) {L' : Subgroup G}
    (hL' : IsTwoComponentIn L' (centralizer {z}))
    (hcov' : IsCoverOf .POmegaOdd 3 p f 2 (↥L' ⧸ pPrimeCore 2 ↥L')) : L' = L := by
  by_contra hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hcomp, -, ⟨E⟩⟩ := hatIn_spec hL'
  obtain ⟨K, _, _, hK, -, hp, hp2, ⟨e₁⟩⟩ := nonempty_mulEquiv_spinOdd h.h5 hcov'
  let e : ↥(hatIn z L') ≃* spinGroup (quadOdd 3 K) := E.symm.trans e₁
  have hodd : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
  have h2K : (2 : K) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K hodd
  have : Invertible (2 : K) := invertibleOfNonzero h2K
  obtain ⟨-, t, -, -, -, -, -, ht2, htZ, -⟩ := spinSeven_lemma410c (K := K) hp hp2 hK h.h5
  set û : MBar z := ((e.symm t : ↥(hatIn z L')) : MBar z) with hû
  have hûL' : û ∈ hatIn z L' := (e.symm t).2
  have hû2 : orderOf û = 2 := by rw [hû, Subgroup.orderOf_coe, MulEquiv.orderOf_eq]; exact ht2
  have hûZ : (⟨û, hûL'⟩ : ↥(hatIn z L')) ∉ center ↥(hatIn z L') := fun hc => htZ (by
    have h1 := (mem_center_mulEquiv_iff e (e.symm t)).mpr hc
    rwa [MulEquiv.apply_symm_apply] at h1)
  set ν := spinGroup.negOne (quadOdd 3 K) (nondegenerate_quadOdd 3 K).ne_zero with hν
  have hνc : ν ∈ center (spinGroup (quadOdd 3 K)) := by
    rw [center_spinGroup_quadOdd h2K le_rfl]
    exact mem_zpowers _
  have hwc : (⟨((e.symm ν : ↥(hatIn z L')) : MBar z), (e.symm ν).2⟩ : ↥(hatIn z L')) ∈
      center ↥(hatIn z L') := by
    rw [← mem_center_mulEquiv_iff e]
    simpa using hνc
  have hw1 : ((e.symm ν : ↥(hatIn z L')) : MBar z) ≠ 1 := by
    intro h1
    apply spinGroup.negOne_ne_one (quadOdd 3 K) (nondegenerate_quadOdd 3 K).ne_zero
    have h3 : e.symm ν = 1 := Subtype.ext h1
    rw [← hν, ← e.apply_symm_apply ν, h3, map_one]
  obtain ⟨-, Y₂, -, -, ⟨hY₂, -, hs₂, hûY₂⟩, -⟩ := spinSeven_three_in hp hp2 hK h.h5 e hûL' hû2 hûZ
    (e.symm ν).2 hwc hw1
  have hY₂' : IsTwoComponentIn Y₂ (centralizer {û}) := by
    have h1 := isTwoComponentIn_inf_of_subnormal (le_top : hatIn z L' ≤ ⊤) hcomp.1.subgroupOf
      (centralizer {û}) hY₂
    rwa [top_inf_eq] at h1
  obtain ⟨u', hu'2, hu'1, hu'mk⟩ := T23.exists_involution_lift (H := ↥(centralizer ({z} : Set G)))
    (a := û) (by have h1 := pow_orderOf_eq_one û; rwa [hû2, sq] at h1)
    (fun h1 => by rw [h1, orderOf_one] at hû2; exact absurd hû2 (by norm_num))
  have hu : orderOf (u' : G) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime (by rw [sq, hu'2]) hu'1
  have huz : (u' : G) ∈ centralizer ({z} : Set G) := u'.2
  have hûmk : (QuotientGroup.mk ⟨(u' : G), huz⟩ : MBar z) = û := hu'mk
  have huL : (u' : G) ∉ L := by
    intro huL
    have hûL : û ∈ hatIn z L := hûmk ▸ mk_mem_hatIn huL huz
    apply hûZ
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (hatIn_commute h.hL hL' (Ne.symm hne) hûL g.2).symm
  rw [← hûmk] at hY₂'
  obtain ⟨J, hJ, hmem, -, ⟨eJ⟩⟩ := lift_twoComponent huz hu hY₂'
  have huJ : (u' : G) ∈ J := hmem _ huz (mem_centralizer_singleton_iff.mpr rfl)
    ⟨1, by rw [pow_one, hu]⟩ (by rw [hûmk]; exact hûY₂)
  exact h.false_of_slTwo hI hu huz huL hJ huJ h.h5
    (isSLTwoOver_quot_of_equiv hp hp2 (one_le_of_five_le_pow h.h5) h.h5 eJ hs₂)

theorem C3Config.normal (hI : C3Inputs) (h : C3Config G z L p f) :
    (L.subgroupOf (centralizer {z})).Normal := by
  rw [normal_subgroupOf_iff h.hL.1]
  intro l g hl hg
  have hgz : g * z * g⁻¹ = z := by
    rw [mem_centralizer_singleton_iff.mp hg, mul_inv_cancel_right]
  have h2 : (centralizer ({z} : Set G)).map (MulAut.conj g).toMonoidHom = centralizer {z} := by
    rw [map_centralizer_singleton_mulEquiv, MulAut.conj_apply, hgz]
  have hLg : IsTwoComponentIn (L.map (MulAut.conj g).toMonoidHom) (centralizer {z}) := by
    have h1 := L35.isTwoComponentIn_map_of_injective (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective h.hL
    rwa [h2] at h1
  let eg : ↥L ≃* ↥(L.map (MulAut.conj g).toMonoidHom) :=
    L.equivMapOfInjective _ (MulAut.conj g).injective
  have heq := h.eq_of_isCoverOf hI hLg
    (isCoverOf_of_mulEquiv (QuotientGroup.congr _ _ eg (pPrimeCore_map_iso 2 eg)) h.hcov)
  rw [← heq]
  exact ⟨l, hl, rfl⟩

theorem C3Config.characteristic (hI : C3Inputs) (h : C3Config G z L p f) :
    (L.subgroupOf (centralizer {z})).Characteristic := by
  rw [characteristic_iff_map_eq]
  intro φ
  have hL'c : IsTwoComponent (L.subgroupOf (centralizer {z})) :=
    (isTwoComponent_iff_isPComponent _).mpr ((isTwoComponentIn_iff h.hL.1).mp h.hL)
  have hφc : IsTwoComponent ((L.subgroupOf (centralizer {z})).map φ.toMonoidHom) :=
    ⟨Subgroup.IsSubnormal.map (f := φ.toMonoidHom) φ.surjective hL'c.1,
      isTwoQuasisimple_of_mulEquiv
        ((L.subgroupOf (centralizer {z})).equivMapOfInjective _ φ.injective) hL'c.2⟩
  have hG : IsTwoComponentIn (((L.subgroupOf (centralizer {z})).map φ.toMonoidHom).map
      (centralizer {z}).subtype) (centralizer {z}) :=
    T23.isTwoComponentIn_map_subtype hφc
  let ε : ↥L ≃* ↥(((L.subgroupOf (centralizer {z})).map φ.toMonoidHom).map
      (centralizer {z}).subtype) :=
    ((subgroupOfEquivOfLe h.hL.1).symm.trans
      ((L.subgroupOf (centralizer {z})).equivMapOfInjective _ φ.injective)).trans
      (((L.subgroupOf (centralizer {z})).map φ.toMonoidHom).equivMapOfInjective _
        (centralizer {z}).subtype_injective)
  have heq := h.eq_of_isCoverOf hI hG
    (isCoverOf_of_mulEquiv (QuotientGroup.congr _ _ ε (pPrimeCore_map_iso 2 ε)) h.hcov)
  apply map_injective (centralizer ({z} : Set G)).subtype_injective
  rw [heq, subgroupOf_map_subtype, inf_eq_left.mpr h.hL.1]

end Certified

end CFSG.ComponentClassification.HarrisLit.T1
