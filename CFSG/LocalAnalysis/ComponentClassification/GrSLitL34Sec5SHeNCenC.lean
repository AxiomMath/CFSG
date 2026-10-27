module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SHeNEight

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

namespace HeNT

open HeDM

variable {X : Type} [Group X] [Finite X]


theorem oddCore_central_of_swap (hS : SchreierFor Blueprint.Catalog)
    (hUO : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hIC : L34InvolutionCentralizerFact) {L : Subgroup X} (hset : HeldEndSetting X L) {a u : X}
    {M : Subgroup X} (ha : orderOf a = 2) (hLa : L ≤ centralizer ({a} : Set X))
    (hLc : IsPComponent 2 (L.subgroupOf (centralizer ({a} : Set X)))) (hu : HeldTwoA L u)
    (hMu : M ≤ centralizer ({u} : Set X))
    (hMp : IsPComponent 2 (M.subgroupOf (centralizer ({u} : Set X))))
    (hne : conjugate M a ≠ M) (hfix : gsFixedLayer (M ⊔ conjugate M a) a = gsFixedLayer L u)
    (hc : ∀ x ∈ (pPrimeCore 2 ↥M).map M.subtype, ∀ m ∈ M, x * m = m * x) {w : X}
    {c : X} (hw2 : orderOf w = 2) (hc2 : orderOf c = 2) (hcw : c * w = w * c) {N : Subgroup X}
    (hNw : N ≤ centralizer ({w} : Set X))
    (hNp : IsPComponent 2 (N.subgroupOf (centralizer ({w} : Set X))))
    (hNne : conjugate N c ≠ N) (hNfix : gsFixedLayer (N ⊔ conjugate N c) c = M) :
    ∀ x ∈ (pPrimeCore 2 ↥N).map N.subtype, ∀ n ∈ N, x * n = n * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hHS, -, -, -, -⟩ := id hset
  obtain ⟨hsimp, hnab, hK, -, hLB, -, -⟩ := id hHS
  have hcc : c * c = 1 := by rw [← pow_two, ← hc2, pow_orderOf_eq_one]
  set Cw := centralizer ({w} : Set X) with hCw
  set N₂ := conjugate N c with hN₂
  have hcC : c ∈ Cw := mem_centralizer_singleton_iff.mpr hcw
  obtain ⟨hN₂w, hN₂p⟩ := UGSChain.conjugate_isPComponent_centralizer hcw hNw hNp
  have hMC : M ≤ Cw := by
    rw [← hNfix]
    exact (gsFixedLayer_le_inf _ c).trans (inf_le_left.trans (sup_le hNw hN₂w))
  obtain ⟨B, hBM, hBe, hB8, hWB, V, hVB, hV4, hVZ⟩ :=
    exists_eight_of_pair hIC hset ha hLa hLc hu hMu hMp hne hfix hc hw2 hMC
  have hBC : B ≤ Cw := hBM.trans hMC
  set c' : ↥Cw := ⟨c, hcC⟩ with hc'
  have hc'c' : c' * c' = 1 := Subtype.ext hcc
  set N' := N.subgroupOf Cw with hN'
  set N₂' := N₂.subgroupOf Cw with hN₂'
  have hN'N₂' : ∀ m ∈ N', c' * m * c'⁻¹ ∈ N₂' := by
    intro m hm
    show c * (m : X) * c⁻¹ ∈ N₂
    rw [hN₂, UnbalancedLayer.mem_conjugate_iff,
      show c * (c * (m : X) * c⁻¹) * c⁻¹ = (c * c) * m * (c * c)⁻¹ by group, hcc]
    simpa using mem_subgroupOf.mp hm
  have hN₂'N' : ∀ n ∈ N₂', c' * n * c'⁻¹ ∈ N' := fun n hn => by
    show c * (n : X) * c⁻¹ ∈ N
    exact UnbalancedLayer.mem_conjugate_iff.mp (mem_subgroupOf.mp hn)
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥Cw) with hπ
  set A := N'.map π with hA
  set Bq := N₂'.map π with hBq
  set α := π c' with hα
  have hOQ : pPrimeCore 2 (↥Cw ⧸ pPrimeCore 2 ↥Cw) = ⊥ := pPrimeCore_quotient_pPrimeCore_eq_bot 2
  have hAp : IsPComponent 2 A := isPComponent_map hNp
  have hBp : IsPComponent 2 Bq := isPComponent_map hN₂p
  have hAc := HeldFix.isComponent_of_isPComponent hOQ hAp
  have hBc := HeldFix.isComponent_of_isPComponent hOQ hBp
  have hAB : A ≠ Bq := by
    intro h
    have h1 : N' = N₂' := GSThmB.OddQuot.eq_of_map_eq π GSThmB.OddQuot.not_two_dvd_card_ker
      (X := ⊤) le_top le_top (CatalogueBPrimeJoin.pComponent_restrict_overgroup 2 hNp le_top)
      (CatalogueBPrimeJoin.pComponent_restrict_overgroup 2 hN₂p le_top) h
    apply hNne
    rw [hN', hN₂', subgroupOf_inj, inf_of_le_left hNw, inf_of_le_left hN₂w] at h1
    exact h1.symm
  have hcomm : ∀ x ∈ A, ∀ y ∈ Bq, x * y = y * x := by
    rcases LocalCores.distinct_components_commute hAc hBc with h | h
    · exact absurd h hAB
    · intro x hx y hy
      have hmem : x * y * x⁻¹ * y⁻¹ ∈ ⁅A, Bq⁆ := commutator_mem_commutator hx hy
      rw [h, mem_bot] at hmem
      calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
        _ = y * x := by rw [hmem, one_mul]
  have hαA : ∀ x ∈ A, α * x * α⁻¹ ∈ Bq := by
    rintro _ ⟨m, hm, rfl⟩
    exact ⟨c' * m * c'⁻¹, hN'N₂' m hm, by simp [hα]⟩
  have hαB : ∀ y ∈ Bq, α * y * α⁻¹ ∈ A := by
    rintro _ ⟨n, hn, rfl⟩
    exact ⟨c' * n * c'⁻¹, hN₂'N' n hn, by simp [hα]⟩
  have hαα : α * α = 1 := by rw [hα, ← map_mul, hc'c', map_one]
  have hAq : IsQuasisimple ↥A := hAc.1
  set M' := M.subgroupOf Cw with hM'
  have hKC : N ⊔ N₂ ≤ Cw := sup_le hNw hN₂w
  have hK' : (N ⊔ N₂).subgroupOf Cw = N' ⊔ N₂' := subgroupOf_sup hNw hN₂w
  have hM'eq : gsFixedLayer (N' ⊔ N₂') c' = M' := by
    rw [← hK', gsFixedLayer_subgroupOf hcC hKC, hNfix]
  have hE2 : IsPGroup 2 (zpowers c') := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime (by rw [pow_two]; exact hc'c') (fun h => by
      have := congrArg Subtype.val h
      simp only [hc', OneMemClass.coe_one] at this
      rw [this, orderOf_one] at hc2
      norm_num at hc2)
  have hEN : zpowers c' ≤ normalizer ((N' ⊔ N₂' : Subgroup ↥Cw) : Set ↥Cw) := by
    have hle : ∀ y ∈ N' ⊔ N₂', c' * y * c'⁻¹ ∈ N' ⊔ N₂' := by
      have h : N' ⊔ N₂' ≤ (N' ⊔ N₂').comap (MulAut.conj c').toMonoidHom :=
        sup_le (fun m hm => mem_sup_right (hN'N₂' m hm)) (fun n hn => mem_sup_left (hN₂'N' n hn))
      intro y hy
      exact h hy
    rw [zpowers_le, mem_normalizer_iff]
    intro y
    refine ⟨hle y, fun h => ?_⟩
    have h1 := hle _ h
    rwa [show c' * (c' * y * c'⁻¹) * c'⁻¹ = (c' * c') * y * (c' * c')⁻¹ by group, hc'c',
      one_mul, inv_one, mul_one] at h1
  have hMb : M'.map π = gsFixedLayer (A ⊔ Bq) α := by
    have h := GSThmB.OddQuot.map_fixedLayer hE2 hEN
    rw [fixedLayer_zpowers, hM'eq, Subgroup.map_sup, MonoidHom.map_zpowers,
      fixedLayer_zpowers] at h
    exact h
  set U' := V.subgroupOf Cw with hU'
  set Vb := U'.map π with hVb
  have hU'M : U' ≤ (Open.fusionZStar ↥M').map M'.subtype := by
    intro y hy
    obtain ⟨t, ht, hty⟩ := hVZ (show (y : X) ∈ V from hy)
    let ψ : ↥M' ≃* ↥M := subgroupOfEquivOfLe hMC
    have hcomap := GSThmB.OddQuot.comap_fusionZStar_of_surjective ψ.toMonoidHom ψ.surjective
      (by rw [show ψ.toMonoidHom.ker = ⊥ from (MonoidHom.ker_eq_bot_iff _).mpr ψ.injective,
        card_bot]; norm_num)
    refine ⟨ψ.symm t, ?_, ?_⟩
    · rw [← hcomap]
      show ψ (ψ.symm t) ∈ Open.fusionZStar ↥M
      rw [MulEquiv.apply_symm_apply]
      exact ht
    · apply Subtype.ext
      exact hty
  have hVb' : Vb ≤ (Open.fusionZStar ↥(M'.map π)).map (M'.map π).subtype := by
    let f : ↥M' →* ↥(M'.map π) := (π.comp M'.subtype).codRestrict _ fun t =>
      mem_map_of_mem π t.2
    have hf : Function.Surjective f := by
      rintro ⟨q, t, ht, rfl⟩
      exact ⟨⟨t, ht⟩, rfl⟩
    have hfk : ¬ 2 ∣ Nat.card f.ker := by
      let g : f.ker →* pPrimeCore 2 ↥Cw :=
        (M'.subtype.comp f.ker.subtype).codRestrict (pPrimeCore 2 ↥Cw) fun k => by
          have h1 : f (k : M') = 1 := k.2
          exact (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val h1)
      have hg : Function.Injective g := fun k₁ k₂ h => by
        have h' := congrArg (fun x : pPrimeCore 2 ↥Cw => (x : ↥Cw)) h
        exact Subtype.ext (Subtype.ext h')
      have hodd : Odd (Nat.card (pPrimeCore 2 ↥Cw)) :=
        Nat.coprime_two_left.mp pPrimeCore_coprime_card
      exact Nat.not_even_iff_odd.mpr (hodd.of_dvd_nat (Subgroup.card_dvd_of_injective g hg)) ∘
        even_iff_two_dvd.mpr
    have hcomap := GSThmB.OddQuot.comap_fusionZStar_of_surjective f hf hfk
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨t, ht, hty⟩ := hU'M hy
    refine ⟨f t, ?_, ?_⟩
    · rw [← hcomap] at ht
      exact ht
    · rw [← hty]
      rfl
  rw [hMb] at hVb'
  set B' := B.subgroupOf Cw with hB'
  have hB'p : IsPGroup 2 B' := hBe.isPGroup.comap_of_injective Cw.subtype Cw.subtype_injective
  have hB'e : IsElemTwo (B'.map π) := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨x₁, hx₁, rfl⟩ _ ⟨y₁, hy₁, rfl⟩
      rw [← map_mul, ← map_mul, show x₁ * y₁ = y₁ * x₁ from Subtype.ext (hBe.1 _ hx₁ _ hy₁)]
    · rintro _ ⟨x₁, hx₁, rfl⟩
      rw [← map_mul, show x₁ * x₁ = 1 from Subtype.ext (hBe.2 _ hx₁), map_one]
  have hB'card : Nat.card (B'.map π) = 8 := by
    rw [GSThmB.OddQuot.card_map_of_isPGroup hB'p, hB',
      Nat.card_congr (subgroupOfEquivOfLe hBC).toEquiv, hB8]
  have hB'M : B'.map π ≤ gsFixedLayer (A ⊔ Bq) α := by
    rw [← hMb]
    exact map_mono fun r hr => mem_subgroupOf.mpr (hBM (mem_subgroupOf.mp hr))
  have hVbB : Vb ≤ B'.map π :=
    map_mono fun r hr => mem_subgroupOf.mpr (hVB (mem_subgroupOf.mp hr))
  have hVb4 : Nat.card Vb = 4 := by
    have hU'p : IsPGroup 2 U' :=
      (hBe.isPGroup.to_le hVB).comap_of_injective Cw.subtype Cw.subtype_injective
    rw [hVb, GSThmB.OddQuot.card_map_of_isPGroup hU'p, hU',
      Nat.card_congr (subgroupOfEquivOfLe (hVB.trans hBC)).toEquiv, hV4]
  obtain ⟨Eb, hEbe, hEb8, -, hEbA, hEbB'⟩ :=
    HeDG.exists_elem_eight hαα hcomm hαA hαB hAq hB'M hB'e hB'card hVbB hVb4 hVb'
  have hEbB : ∀ r ∈ B', ∀ e' ∈ Eb, π r * e' = e' * π r := fun r hr e' he' =>
    hEbB' (π r) (mem_map_of_mem π hr) e' he'
  obtain ⟨Z, hZB, hZE, hZe, hZcard⟩ := HeDL.exists_lift_centralizing hB'p hEbe hEbB
  have hZN : ∀ z ∈ Z, z ∈ normalizer (N' : Set ↥Cw) ∧
      ∀ m ∈ N', z * m * z⁻¹ * m⁻¹ ∈ (pPrimeCore 2 ↥N').map N'.subtype := by
    intro z hz
    apply HeDL.normalizes_of_central hNp
    intro m hm
    have hzE : π z ∈ Eb := hZE ▸ mem_map_of_mem π hz
    exact hEbA _ hzE _ (mem_map_of_mem π hm)
  set E := Z.map Cw.subtype with hE
  have hEu : E ≤ Cw := map_subtype_le _
  have hEe : IsElemTwo E := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨x₁, hx₁, rfl⟩ _ ⟨y₁, hy₁, rfl⟩
      exact congrArg Subtype.val (hZe.1 _ hx₁ _ hy₁)
    · rintro _ ⟨x₁, hx₁, rfl⟩
      exact congrArg Subtype.val (hZe.2 _ hx₁)
  have hE8 : 8 ≤ Nat.card E := by
    rw [hE, card_map_of_injective Cw.subtype_injective, hZcard]
    exact hEb8
  have hENN : E ≤ normalizer (N : Set X) := by
    rintro _ ⟨z, hz, rfl⟩
    have hzN := (hZN z hz).1
    rw [mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have h1 := (mem_normalizer_iff.mp hzN ⟨y, hNw hy⟩).mp (mem_subgroupOf.mpr hy)
      exact mem_subgroupOf.mp h1
    · intro hy
      have hyC : y ∈ Cw := by
        have h2 := mul_mem (mul_mem (inv_mem z.2) (hNw hy)) z.2
        have h3 : ((z : ↥Cw) : X)⁻¹ * (Cw.subtype z * y * (Cw.subtype z)⁻¹) * z = y := by
          simp only [coe_subtype]
          group
        rwa [h3] at h2
      have h1 := (mem_normalizer_iff.mp hzN ⟨y, hyC⟩).mpr (mem_subgroupOf.mpr hy)
      exact mem_subgroupOf.mp h1
  have hEcen : ∀ e' ∈ E, ∀ l ∈ N, e' * l * e'⁻¹ * l⁻¹ ∈ (pPrimeCore 2 ↥N).map N.subtype := by
    rintro _ ⟨z, hz, rfl⟩ l hl
    have h1 := (hZN z hz).2 ⟨l, hNw hl⟩ (mem_subgroupOf.mpr hl)
    have h2 := mem_map_of_mem Cw.subtype h1
    rw [GSThmB.B5a.map_oddCoreIn_subgroupOf Cw N, inf_of_le_right hNw] at h2
    exact h2
  have hGW := gwTwoBalanced_of_locallyTwoBalanced solomonCommutingCoreInput hLB
  have hEB : ∀ x₁ ∈ E, ∀ y₁ ∈ B, x₁ * y₁ = y₁ * x₁ := by
    rintro _ ⟨z, hz, rfl⟩ y₁ hy₁
    have h1 := mem_centralizer_iff.mp (hZB hz) ⟨y₁, hBC hy₁⟩ (mem_subgroupOf.mpr hy₁)
    exact (congrArg Subtype.val h1).symm
  have hWE : wGroup E = ⊥ := by
    rw [wGroup_eq_of_commute hGW (hEe.isAbelianTwoOfRank hE8)
      (hBe.isAbelianTwoOfRank (by omega)) hEB]
    exact hWB
  have hbal : ∀ e' ∈ E, e' ≠ 1 →
      ⁅(pPrimeCore 2 ↥N).map N.subtype ⊓ centralizer ({e'} : Set X),
        (pLayer ↥(N ⊓ centralizer ({e'} : Set X)) 2).map
          (N ⊓ centralizer ({e'} : Set X)).subtype⁆ ≤
      (pPrimeCore 2 ↥(centralizer ({e'} : Set X))).map (centralizer ({e'} : Set X)).subtype :=
    fun e' he' he1 => GrS5.commutator_oddCore_pLayer_le hS hUO hheld hK hw2 hNw hNp
      (mem_centralizer_singleton_iff.mp (hEu he')).symm (HeKC.centralizer_ne_top hsimp hnab he1)
  exact oddCore_le_center_of_wGroup_eq_bot hNw hNp hEu hEe.1 hEe.2 (by omega) hENN hEcen hWE
    hbal (Or.inr hE8)

end HeNT

end CFSG.ComponentClassification.GrSLit
