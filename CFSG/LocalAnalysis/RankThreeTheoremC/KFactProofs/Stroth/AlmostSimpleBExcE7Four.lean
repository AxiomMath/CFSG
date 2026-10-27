module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBExcE7Card
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBExcE7Gen
public import CFSG.RankThree.PartOne.KE.E7FourStab

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open Matrix CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge TauCeti CFSG.RankThree.Chevalley
  CFSG.RankThree.Lattice CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KE
  CFSG.RankThree.LocalRank CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KD4L
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsChevIndexTwo)

open scoped Matrix MatrixGroups commutatorElement

section Fixed

variable {L : Type} [Field L]

theorem e7F4S0Set_isRoot :
    ∀ α ∈ e7F4S0Set, IsRoot .E7 α := by
  intro α hα
  have e : e7F4S0Set = ({e7F4α, -e7F4α} ∪ {e7F4β, -e7F4β} ∪ {e7F4γ, -e7F4γ} :
      Set (Fin Tag.E7.rank → ℤ)) := e7F4_S0_eq
  rw [e] at hα
  obtain ⟨hα₀, hβ₀, hγ₀⟩ := e7F4_S0_isRoot
  rcases hα with ((rfl | rfl) | (rfl | rfl)) | (rfl | rfl)
  · exact hα₀
  · exact IsRoot.neg hα₀
  · exact hβ₀
  · exact IsRoot.neg hβ₀
  · exact hγ₀
  · exact IsRoot.neg hγ₀

theorem e7F4S0Set_fixed :
    ∀ α ∈ e7F4S0Set, e7F4W *ᵥ α = α := by
  intro α hα
  have e : e7F4S0Set = ({e7F4α, -e7F4α} ∪ {e7F4β, -e7F4β} ∪ {e7F4γ, -e7F4γ} :
      Set (Fin Tag.E7.rank → ℤ)) := e7F4_S0_eq
  rw [e] at hα
  obtain ⟨hwα, hwβ, hwγ⟩ := e7F4_S0_fixed
  rcases hα with ((rfl | rfl) | (rfl | rfl)) | (rfl | rfl)
  · exact hwα
  · rw [Matrix.mulVec_neg, hwα]
  · exact hwβ
  · rw [Matrix.mulVec_neg, hwβ]
  · exact hwγ
  · rw [Matrix.mulVec_neg, hwγ]

theorem e7F4S0Set_subset_kernel_of_pow
    {Fr : L →+* L} {q m : ℕ} (hFr : ∀ x, Fr x = x ^ q) (hq : 0 < q) (hcop : Nat.Coprime m (q - 1))
    {b : Fin Tag.E7.rank → Lˣ} (hb : b ∈ fixedCharTuples e7F4W Fr) (hbm : ∀ i, b i ^ m = 1) :
    e7F4S0Set ⊆ rootCharKernel b := fun α hα =>
  ⟨e7F4S0Set_isRoot α hα, rootChar_eq_one_of_fixed_root hFr hq hb (e7F4S0Set_fixed α hα) hbm hcop⟩

omit [Field L] in
theorem not_dvd_sub_one_of_dvd_sq_add_one {p q : ℕ} (hp3 : 3 < p) (hq : 0 < q)
    (hpq : (p : ℤ) ∣ (q : ℤ) ^ 2 + 1) : ¬ p ∣ q - 1 := by
  intro h
  have h1 : (p : ℤ) ∣ (q : ℤ) - 1 := by
    have := Int.natCast_dvd_natCast.2 h
    rwa [Nat.cast_sub hq] at this
  have h2 : (p : ℤ) ∣ 2 := by
    have e : (2 : ℤ) = ((q : ℤ) ^ 2 + 1) - ((q : ℤ) - 1) * ((q : ℤ) + 1) := by ring
    rw [e]
    exact dvd_sub hpq (Dvd.dvd.mul_right h1 _)
  have h3 : p ∣ 2 := by exact_mod_cast h2
  have := Nat.le_of_dvd two_pos h3
  omega

end Fixed

section Special

variable {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] {p : ℕ}
  {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]


theorem e7_four_special_core (hD4 : D4TranspositionLayer Tag.E7) (F : E7FourFrame K L ℓ f p)
    (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ (ℓ ^ f) ^ 2 + 1) (hstab : E7StabHyp F.n (iterateFrobenius L ℓ f) p)
    {x : adjointGroup .E7 K} (hx : orderOf x = p) (c : adjointGroup .E7 K)
    (hh : F.g0⁻¹ * adjEmb .E7 K L (c * x * c⁻¹) * F.g0 ∈
      twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))))
    {b : Fin Tag.E7.rank → Lˣ}
    (hbh : rootDiagUnit .E7 b = F.g0⁻¹ * adjEmb .E7 K L (c * x * c⁻¹) * F.g0)
    (cert : D4A1Cert) (hcert : cert ∈ e7F4Certs)
    (hker : rootCharKernel b = e7F4S0Set ∪ classSetL7 e7F4Rows cert.cls) :
    ∃ ψ : Subgroup.centralizer ({x} : Set (adjointGroup .E7 K)) →* ModGL .E7 L,
      Function.Injective ψ ∧
      (∀ y, ψ y = F.g0⁻¹ * adjEmb .E7 K L (c * (y : adjointGroup .E7 K) * c⁻¹) * F.g0) ∧
      (∀ y, ψ y ∈ torusGroup .E7 L ⊔ rootSpan .E7 L (rootCharKernel b)) ∧
      (∀ y, ψ y ∈ Subgroup.normalizer
        (rootSpan .E7 L {toVec Tag.E7.rank cert.r, -toVec Tag.E7.rank cert.r} :
          Set (ModGL .E7 L))) ∧
      ({toVec Tag.E7.rank cert.r, -toVec Tag.E7.rank cert.r} ⊆ e7F4S0Set) ∧
      IsRoot .E7 (toVec Tag.E7.rank cert.r) ∧
      ∃ PD : Subgroup (ModGL .E7 L), PD ≤ ψ.range ∧ CFSG.IsQuasisimple PD ∧
        (∀ d : Subgroup.centralizer ({x} : Set (adjointGroup .E7 K)), ∀ u ∈ PD,
          ψ d * u * (ψ d)⁻¹ ∈ PD) ∧ (∃ w ∈ PD, orderOf w = p) ∧
        ∀ y ∈ torusGroup .E7 L ⊔ rootSpan .E7 L (rootCharKernel b),
          (∀ u ∈ PD, y * u = u * y) →
            ∃ h ∈ torusGroup .E7 L,
              ∃ z ∈ rootSpan .E7 L {toVec Tag.E7.rank cert.r, -toVec Tag.E7.rank cert.r},
                y = h * z := by
  classical
  have hτ : Tag.E7 = .D4 ∨ Tag.E7 = .E6 ∨ Tag.E7 = .E7 ∨ Tag.E7 = .E8 :=
    Or.inr (Or.inr (Or.inl rfl))
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact iterateFrobenius_def ℓ f c
  have hgood := e7F4_certs_good cert hcert
  obtain ⟨hr, hrS, hSigma, horth, hfix, u, hu, hcertw⟩ := D4A1Cert.sound hgood
  obtain ⟨-, -, -, -, -, -, -, hab, ha, hbl, -⟩ := hgood
  have hnC : F.n ∈ adjointGroup .E7 L := monomialSubgroup_le_adjointGroup' F.hnm
  obtain ⟨PD, hPD, hfac, hsl⟩ := e7_d4_swap_factor hD4 hf hK
    ((coxeterSystem Tag.E7).wordProd cert.w) F.n F.hnm hnC cert.a cert.b hab
    (by rcases ha with h | h | h <;> simp [h]) (by rcases hbl with h | h | h <;> simp [h])
    (by rw [F.hnW]; exact ⟨u, hu, hcertw⟩)
  have hordPD : ∃ w ∈ PD, orderOf w = p :=
    exists_orderOf_swap_layer hf hp hp2 hpq ((coxeterSystem Tag.E7).wordProd cert.w) F.n F.hnm
      cert.a cert.b hab (by rcases ha with h | h | h <;> simp [h])
      (by rcases hbl with h | h | h <;> simp [h]) (by rw [F.hnW]; exact ⟨u, hu, hcertw⟩) PD hPD
  have hkerS : rootCharKernel b = e7D4Set cert ∪ {toVec Tag.E7.rank cert.r,
      -toVec Tag.E7.rank cert.r} := hker.trans hSigma
  have hroots : ∀ α ∈ e7D4Set cert, IsRoot Tag.E7 α := by
    rintro _ ⟨α, hα, rfl⟩
    exact IsRoot.smul hα.1 _
  have hrootsA : ∀ α ∈ ({toVec Tag.E7.rank cert.r, -toVec Tag.E7.rank cert.r} :
      Set (Fin Tag.E7.rank → ℤ)), IsRoot Tag.E7 α := by
    intro α hα
    rcases hα with rfl | rfl
    exacts [hr, IsRoot.neg hr]
  have horth' : ∀ α ∈ e7D4Set cert, ∀ β ∈ ({toVec Tag.E7.rank cert.r,
      -toVec Tag.E7.rank cert.r} : Set (Fin Tag.E7.rank → ℤ)),
        α ⬝ᵥ (Tag.E7.symmetrizedCartan *ᵥ β) = 0 := by
    intro α hα β hβ
    rcases hβ with rfl | rfl
    · exact horth α hα
    · rw [Matrix.mulVec_neg, dotProduct_neg, horth α hα, neg_zero]
  have hS : ∀ α ∈ rootCharKernel b, IsRoot Tag.E7 α := fun α hα => hα.1
  have hSn : ∀ α ∈ rootCharKernel b, -α ∈ rootCharKernel b := fun α hα =>
    ⟨IsRoot.neg hα.1, by rw [rootChar_neg', hα.2, inv_one]⟩
  have hHN := torus_sup_union_le_normalizers (L := L) hτ hroots hrootsA horth'
  have hPQ : PD ≤ rootSpan .E7 L (rootCharKernel b) := by
    rw [hkerS, rootSpan_union_eq]
    exact (hfac.le_root ()).trans le_sup_left
  obtain ⟨ψ, hψinj, hψ, hψHQ, hψR, hψadj, hPψ, hψnorm⟩ := e7_perx_core_of_stab Fr hFr F.n F.g0
    F.hg0C F.hg0 F.hperf hp hstab hx c hbh hh rfl hS hSn (P := fun _ : Unit => PD)
    (fun _ => hfac.finite ()) (fun _ => hfac.quasi ()) (fun _ => hPQ) (fun _ => hfac.le_fix ())
    (fun _ => hfac.le_adj ()) (fun _ y hy hyR u hu => by
      rw [hkerS] at hy
      exact hfac.norm () y (hHN hy).1 hyR u hu)
  refine ⟨ψ, hψinj, hψ, hψHQ, fun y => ?_, ?_, hr, PD, hPψ (), hfac.quasi (), hψnorm (), hordPD,
    fun y hy hc => ?_⟩
  · have h1 := hψHQ y
    rw [hkerS] at h1
    exact (hHN h1).2
  · intro α hα
    rcases hα with rfl | rfl
    · exact hrS
    · exact e7F4_S0_neg _ hrS
  · rw [hkerS] at hy
    obtain ⟨⟨h, hH, -, z, hz, hyz⟩, -⟩ := ThetaFree.one_sided hτ hroots hrootsA horth'
      hfac.thetaFree hfac.le_root hy fun i u hu => hc u hu
    exact ⟨h, hH, z, hz, hyz⟩

end Special

section Main

variable {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] {p : ℕ}
  {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]


theorem pElem_centralizes (F : E7FourFrame K L ℓ f p) (hK : Nat.card K = ℓ ^ f) (hp : p.Prime)
    (hp3 : 3 < p) (hpq : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + 1) {x : adjointGroup .E7 K}
    (S : Sylow p (Subgroup.centralizer ({x} : Set (adjointGroup .E7 K)))) (c : adjointGroup .E7 K)
    (hc : ∀ a ∈ (S : Subgroup (Subgroup.centralizer ({x} : Set (adjointGroup .E7 K)))).map
        (Subgroup.centralizer ({x} : Set (adjointGroup .E7 K))).subtype,
      F.g0⁻¹ * adjEmb .E7 K L (c * a * c⁻¹) * F.g0 ∈
        twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))))
    (ψ : Subgroup.centralizer ({x} : Set (adjointGroup .E7 K)) →* ModGL .E7 L)
    (hψ : ∀ y, ψ y = F.g0⁻¹ * adjEmb .E7 K L (c * (y : adjointGroup .E7 K) * c⁻¹) * F.g0)
    (R : Set (Fin Tag.E7.rank → ℤ)) (hR : R ⊆ e7F4S0Set)
    (hN : ∀ y, ψ y ∈ Subgroup.normalizer (rootSpan .E7 L R : Set (ModGL .E7 L))) :
    ∀ y, (∃ k : ℕ, y ^ p ^ k = 1) →
      ψ y ∈ Subgroup.centralizer (rootSpan .E7 L R : Set (ModGL .E7 L)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hFr : ∀ c, iterateFrobenius L ℓ f c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact iterateFrobenius_def ℓ f c
  have hq : 0 < Nat.card K := Nat.card_pos
  have hnd : ¬ p ∣ Nat.card K - 1 := not_dvd_sub_one_of_dvd_sq_add_one hp3 hq hpq
  intro y hy
  refine map_mem_centralizer_of_pElem hp S ψ (rootSpan .E7 L R) hN (fun s hs => ?_) hy
  have h1 : ψ s ∈ twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) := by
    rw [hψ s]
    exact hc _ ⟨s, hs, rfl⟩
  rw [F.hT] at h1
  obtain ⟨b', hb', hb'e⟩ := h1
  have hbe : rootDiagUnit .E7 b' = ψ s := hb'e
  obtain ⟨k, hk⟩ := S.isPGroup' ⟨s, hs⟩
  have hsk : s ^ p ^ k = 1 := congrArg Subtype.val hk
  have hpow : rootDiagUnit .E7 b' ^ p ^ k = 1 := by rw [hbe, ← map_pow, hsk, map_one]
  have hbm : ∀ i, b' i ^ p ^ k = 1 := by
    have h2 : b' ^ p ^ k = 1 := by
      apply rootDiagUnit_injective (τ := Tag.E7) (K := L)
      have h3 : rootDiagUnit .E7 (b' ^ p ^ k) = rootDiagUnit .E7 b' ^ p ^ k :=
        map_pow (rootDiagUnitHom .E7 L) b' _
      rw [h3, hpow]
      exact (map_one (rootDiagUnitHom .E7 L)).symm
    exact fun i => congrFun h2 i
  have hcop : Nat.Coprime (p ^ k) (Nat.card K - 1) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 hnd)
  have hsub : R ⊆ rootCharKernel b' :=
    hR.trans (e7F4S0Set_subset_kernel_of_pow hFr hq hcop hb' hbm)
  have hle := rootSpan_le_centralizer (K := L) b' hsub
  refine Subgroup.mem_centralizer_iff.2 fun g hg => ?_
  have := Subgroup.mem_centralizer_singleton_iff.1 (hle hg)
  rw [← hbe]
  exact this

end Main

section Odd


theorem oddPCoreInClosure_E7_four (K : Type) [Field K] [Finite K] {f : ℕ} [CharP K 2]
    (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + 1) {x : adjointGroup .E7 K} (hx : orderOf x = p) :
    OddPCoreInClosure p ↥(Subgroup.centralizer ({x} : Set (adjointGroup .E7 K))) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype K := Fintype.ofFinite K
  let L := AlgebraicClosure K
  haveI : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  obtain ⟨F⟩ := exists_e7FourFrame K hf hK hp hp3 hpq L
  have hstab := e7_stabHyp F hK hp hp3 hpq
  have hD4 : D4TranspositionLayer Tag.E7 := d4TranspositionLayer_E7
  have hp2 : p ≠ 2 := by omega
  have hpq' : p ∣ (2 ^ f) ^ 2 + 1 := by
    have h1 : (p : ℤ) ∣ ((Nat.card K ^ 2 + 1 : ℕ) : ℤ) := by exact_mod_cast hpq
    have h2 := Int.natCast_dvd_natCast.1 h1
    rwa [hK] at h2
  have hxC : x ∈ Subgroup.centralizer ({x} : Set (adjointGroup .E7 K)) :=
    Subgroup.mem_centralizer_singleton_iff.2 rfl
  obtain ⟨S, hxS⟩ : ∃ S : Sylow p (Subgroup.centralizer ({x} : Set (adjointGroup .E7 K))),
      (⟨x, hxC⟩ : Subgroup.centralizer ({x} : Set (adjointGroup .E7 K))) ∈ (S : Subgroup _) := by
    have hpg : IsPGroup p (Subgroup.zpowers
        (⟨x, hxC⟩ : Subgroup.centralizer ({x} : Set (adjointGroup .E7 K)))) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, pow_one, ← Subgroup.orderOf_coe]
      exact hx
    obtain ⟨S, hS⟩ := hpg.exists_le_sylow
    exact ⟨S, hS (Subgroup.mem_zpowers _)⟩
  have hpS : IsPGroup p ((S : Subgroup (Subgroup.centralizer ({x} : Set (adjointGroup .E7 K)))).map
      (Subgroup.centralizer ({x} : Set (adjointGroup .E7 K))).subtype) :=
    S.isPGroup'.map _
  obtain ⟨c, hc⟩ := F.hconj _ hpS
  have hh : F.g0⁻¹ * adjEmb .E7 K L (c * x * c⁻¹) * F.g0 ∈
      twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L 2 f))) :=
    hc x ⟨⟨x, hxC⟩, hxS, rfl⟩
  have hΦ : ((Nat.card K : ℕ) : ZMod p) ^ 2 + 1 = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((Nat.card K : ℤ) ^ 2 + 1) p).2 hpq
    simpa using this
  have hFr : ∀ c, iterateFrobenius L 2 f c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact iterateFrobenius_def 2 f c
  obtain ⟨b, hb, hap, hb1, hbh, -⟩ := e7_perx_prelim F hp hx c hh
  have hkind : rootCharKernel b = e7F4S0Set ∨ ∃ cert ∈ e7F4Certs,
      rootCharKernel b = e7F4S0Set ∪ classSetL7 e7F4Rows cert.cls := by
    rcases e7F4_kernel_structure (iterateFrobenius L 2 f) hFr hp hp3 hΦ hb hap hb1 with
      h | ⟨cert, hcert, h, -⟩
    · exact Or.inl h
    · exact Or.inr ⟨cert, hcert, h⟩
  rcases hkind with hker | ⟨cert, hcert, hker⟩
  ·
    have hS0 : ∀ α ∈ e7F4S0Set, IsRoot Tag.E7 α := e7F4S0Set_isRoot
    have hSn : ∀ α ∈ e7F4S0Set, -α ∈ e7F4S0Set := e7F4_S0_neg
    obtain ⟨ψ, hψinj, hψ, hψHQ, -⟩ := e7_perx_core_of_stab (iterateFrobenius L 2 f) hFr F.n F.g0
      F.hg0C F.hg0 F.hperf hp hstab hx c hbh hh hker hS0 hSn
      (P := fun e : Empty => (e.elim : Subgroup (ModGL .E7 L))) (fun e => e.elim)
      (fun e => e.elim) (fun e => e.elim) (fun e => e.elim) (fun e => e.elim) (fun e => e.elim)
    have hN : ∀ y, ψ y ∈ Subgroup.normalizer (rootSpan .E7 L e7F4S0Set : Set (ModGL .E7 L)) :=
      fun y =>
        sup_le (CFSG.RankThree.PartOne.KE.torusGroup_le_normalizer_rootSpan hS0)
          Subgroup.le_normalizer (hψHQ y)
    have hX := pElem_centralizes F hK hp hp3 hpq S c hc ψ hψ e7F4S0Set Set.Subset.rfl hN
    refine oddPCoreInClosure_of_closure ψ hψinj
      (Subgroup.centralizer (rootSpan .E7 L e7F4S0Set : Set (ModGL .E7 L))) hX
      (ψ.range ⊓ torusGroup .E7 L) (fun y hy => ?_) (odd_card_range_inf_torus ψ)
    exact Subgroup.mem_inf.2 ⟨⟨y, rfl⟩, centTorus_S0 (ψ y) (hψHQ y) hy⟩
  ·
    obtain ⟨ψ, hψinj, hψ, hψHQ, hN, hsub, hr, PD, hPDψ, hPDq, hPDn, hPDord, hone⟩ :=
      e7_four_special_core hD4 F hf hK hp hp2 hpq' hstab hx c hh hbh cert hcert hker
    have hX := pElem_centralizes F hK hp hp3 hpq S c hc ψ hψ
      {toVec Tag.E7.rank cert.r, -toVec Tag.E7.rank cert.r} hsub hN
    have hpPD : p ∣ Nat.card PD := by
      obtain ⟨w, hw, hwo⟩ := hPDord
      have h1 : orderOf (⟨w, hw⟩ : PD) = p := by
        rw [← Subgroup.orderOf_coe]
        exact hwo
      rw [← h1]
      exact orderOf_dvd_natCard _
    refine oddPCoreInClosure_of_closure_quasisimple hp ψ hψinj PD hPDψ hPDn hPDq hpPD
      (Subgroup.centralizer (rootSpan .E7 L
        {toVec Tag.E7.rank cert.r, -toVec Tag.E7.rank cert.r} : Set (ModGL .E7 L))) hX
      (ψ.range ⊓ torusGroup .E7 L) (fun y hcomm hyX => ?_) (odd_card_range_inf_torus ψ)
    obtain ⟨h, hH, z, hz, hyz⟩ := hone (ψ y) (hψHQ y) hcomm
    refine Subgroup.mem_inf.2 ⟨⟨y, rfl⟩, centTorus_pair hr (ψ y) ?_ hyX⟩
    rw [hyz]
    exact mul_mem (Subgroup.mem_sup_left hH) (Subgroup.mem_sup_right hz)

end Odd

section Final


theorem chevTwoPClosureOddE7Four_holds : ChevTwoPClosureOddE7Four := by
  intro p hp hp2 L _ _ hs hnab hrk hSE d hF hdi ⟨e⟩
  obtain ⟨d, hv⟩ := d
  cases d with
  | E7 q =>
    have hq2 : q.p = 2 := hdi
    have hord : orderOf ((q.card : ℕ) : ZMod p) = 4 := hF
    have hp3 : 3 < p := by
      haveI : Fact p.Prime := ⟨hp⟩
      have hne : ((q.card : ℕ) : ZMod p) ≠ 0 := by
        intro h0
        rw [h0, orderOf_zero] at hord
        omega
      have hdvd := ZMod.orderOf_dvd_card_sub_one hne
      rw [hord] at hdvd
      have := Nat.le_of_dvd (by have := hp.two_le; omega) hdvd
      omega
    obtain ⟨K, _, _, hK, hchK, ⟨eK⟩⟩ :=
      exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e7 q hv
    haveI : CharP K 2 := hq2 ▸ hchK
    have hK2 : Nat.card K = 2 ^ q.exponent := by rw [hK, PrimePower.card_def, hq2]
    have hpq : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + 1 := by
      have h1 : p ∣ Nat.card K ^ 2 + 1 := by
        rw [hK]
        exact dvd_of_orderOf_four hp hord
      have h2 := Int.natCast_dvd_natCast.2 h1
      push_cast at h2
      exact h2
    let θ : L ≃* adjointGroup Tag.E7 K := e.trans eK
    refine PClosureOdd.of_mulEquiv θ.symm ?_
    intro d hd1 hdp
    haveI : Fact p.Prime := ⟨hp⟩
    exact oddPCoreInClosure_E7_four K q.exponent_pos hK2 hp hp3 hpq (orderOf_eq_prime hdp hd1)
  | A _ _ => exact absurd hF (by simp [LieFamilyE7Four])
  | twistedA _ _ => exact absurd hF (by simp [LieFamilyE7Four])
  | B _ _ => exact absurd hF (by simp [LieFamilyE7Four])
  | C _ _ => exact absurd hF (by simp [LieFamilyE7Four])
  | D _ _ => exact absurd hF (by simp [LieFamilyE7Four])
  | twistedD _ _ => exact absurd hF (by simp [LieFamilyE7Four])
  | E6 _ => exact absurd hF (by simp [LieFamilyE7Four])
  | E8 _ => exact absurd hF (by simp [LieFamilyE7Four])
  | F4 _ => exact absurd hF (by simp [LieFamilyE7Four])
  | G2 _ => exact absurd hF (by simp [LieFamilyE7Four])
  | twistedE6 _ => exact absurd hF (by simp [LieFamilyE7Four])
  | trialityD4 _ => exact absurd hF (by simp [LieFamilyE7Four])
  | suzuki _ => exact absurd hF (by simp [LieFamilyE7Four])
  | reeG2 _ => exact absurd hF (by simp [LieFamilyE7Four])
  | reeF4 _ => exact absurd hF (by simp [LieFamilyE7Four])
  | tits => exact absurd hF (by simp [LieFamilyE7Four])

end Final

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
