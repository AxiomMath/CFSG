module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeDMain
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeDE
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeDGOmega

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

namespace HeDG

open HeDM

theorem central_of_diagonal
    (hS : SchreierFor Blueprint.Catalog)
    (hUO : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    {X : Type} [Group X] [Finite X] {L : Subgroup X} (hset : HeldSetting X L)
    (hW : ∀ A : Subgroup X, A ≤ normalizer (L : Set X) → IsFourGroup A → wGroup A = ⊥)
    {a u : X} {T M : Subgroup X} (ha : orderOf a = 2) (hLa : L ≤ centralizer ({a} : Set X))
    (huL : u ∈ L) (huu : u * u = 1) (hu1 : u ≠ 1) (hTL : T ≤ L)
    (hTau : T ≤ centralizer ({a} : Set X) ⊓ centralizer ({u} : Set X))
    (hTp : IsPComponent 2 (T.subgroupOf (centralizer ({a} : Set X) ⊓ centralizer ({u} : Set X))))
    (hMu : M ≤ centralizer ({u} : Set X))
    (hMp : IsPComponent 2 (M.subgroupOf (centralizer ({u} : Set X))))
    (hne : conjugate M a ≠ M) (hfix : gsFixedLayer (M ⊔ conjugate M a) a = T) :
    ∀ x ∈ (pPrimeCore 2 ↥M).map M.subtype, ∀ m ∈ M, x * m = m * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hsimp, hnab, hK, -, hLB, -, ⟨e⟩⟩ := id hset
  have haa : a * a = 1 := by rw [← pow_two, ← ha, pow_orderOf_eq_one]
  have hu2 : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact huu) hu1
  have hau : a * u = u * a := (mem_centralizer_singleton_iff.mp (hLa huL)).symm
  have hZX : ∀ x : X, x ≠ 1 → centralizer ({x} : Set X) ≠ ⊤ := by
    intro x hx htop
    have hcen : center X = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center X) with h | h
      · exact h
      · exfalso
        obtain ⟨y, z, hyz⟩ := hnab
        have hy : y ∈ center X := h ▸ mem_top y
        exact hyz (mem_center_iff.mp hy z).symm
    have hxc : x ∈ center X := mem_center_iff.mpr fun g =>
      (mem_centralizer_singleton_iff.mp (htop ▸ mem_top g : g ∈ centralizer ({x} : Set X)))
    rw [hcen, mem_bot] at hxc
    exact hx hxc
  obtain ⟨B, hBT, hBe, hB8, V₀, hV₀B, hV₀4, hV₀Z⟩ :=
    HeDE.exists_eight_le_center hLa e huL huu hu1 hTL hTau hTp
  set C := centralizer ({u} : Set X) with hC
  set N := conjugate M a with hN
  have haC : a ∈ C := mem_centralizer_singleton_iff.mpr hau
  obtain ⟨hNu, hNp⟩ := UGSChain.conjugate_isPComponent_centralizer hau hMu hMp
  have hTC : T ≤ C := hTau.trans inf_le_right
  have hBC : B ≤ C := hBT.trans hTC
  set a' : ↥C := ⟨a, haC⟩ with ha'
  have ha'a' : a' * a' = 1 := Subtype.ext haa
  set M' := M.subgroupOf C with hM'
  set N' := N.subgroupOf C with hN'
  have hM'N' : ∀ m ∈ M', a' * m * a'⁻¹ ∈ N' := by
    intro m hm
    show a * (m : X) * a⁻¹ ∈ N
    rw [hN, UnbalancedLayer.mem_conjugate_iff,
      show a * (a * (m : X) * a⁻¹) * a⁻¹ = (a * a) * m * (a * a)⁻¹ by group, haa]
    simpa using mem_subgroupOf.mp hm
  have hN'M' : ∀ n ∈ N', a' * n * a'⁻¹ ∈ M' := fun n hn => by
    show a * (n : X) * a⁻¹ ∈ M
    exact UnbalancedLayer.mem_conjugate_iff.mp (mem_subgroupOf.mp hn)
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥C) with hπ
  set A := M'.map π with hA
  set Bq := N'.map π with hBq
  set α := π a' with hα
  have hOQ : pPrimeCore 2 (↥C ⧸ pPrimeCore 2 ↥C) = ⊥ := pPrimeCore_quotient_pPrimeCore_eq_bot 2
  have hAp : IsPComponent 2 A := isPComponent_map hMp
  have hBp : IsPComponent 2 Bq := isPComponent_map hNp
  have hAc := HeldFix.isComponent_of_isPComponent hOQ hAp
  have hBc := HeldFix.isComponent_of_isPComponent hOQ hBp
  have hAB : A ≠ Bq := by
    intro h
    have h1 : M' = N' := GSThmB.OddQuot.eq_of_map_eq π GSThmB.OddQuot.not_two_dvd_card_ker
      (X := ⊤) le_top le_top (CatalogueBPrimeJoin.pComponent_restrict_overgroup 2 hMp le_top)
      (CatalogueBPrimeJoin.pComponent_restrict_overgroup 2 hNp le_top) h
    apply hne
    rw [hM', hN', subgroupOf_inj, inf_of_le_left hMu, inf_of_le_left hNu] at h1
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
    exact ⟨a' * m * a'⁻¹, hM'N' m hm, by simp [hα]⟩
  have hαB : ∀ y ∈ Bq, α * y * α⁻¹ ∈ A := by
    rintro _ ⟨n, hn, rfl⟩
    exact ⟨a' * n * a'⁻¹, hN'M' n hn, by simp [hα]⟩
  have hαα : α * α = 1 := by rw [hα, ← map_mul, ha'a', map_one]
  have hAq : IsQuasisimple ↥A := hAc.1
  set T' := T.subgroupOf C with hT'
  have hKC : M ⊔ N ≤ C := sup_le hMu hNu
  have hK' : (M ⊔ N).subgroupOf C = M' ⊔ N' := subgroupOf_sup hMu hNu
  have hT'eq : gsFixedLayer (M' ⊔ N') a' = T' := by
    rw [← hK', gsFixedLayer_subgroupOf haC hKC, hfix]
  have hE2 : IsPGroup 2 (zpowers a') := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime (by rw [pow_two]; exact ha'a') (fun h => by
      have := congrArg Subtype.val h
      simp only [ha', OneMemClass.coe_one] at this
      rw [this, orderOf_one] at ha
      norm_num at ha)
  have hEN : zpowers a' ≤ normalizer ((M' ⊔ N' : Subgroup ↥C) : Set ↥C) := by
    have hle : ∀ y ∈ M' ⊔ N', a' * y * a'⁻¹ ∈ M' ⊔ N' := by
      have h : M' ⊔ N' ≤ (M' ⊔ N').comap (MulAut.conj a').toMonoidHom :=
        sup_le (fun m hm => mem_sup_right (hM'N' m hm)) (fun n hn => mem_sup_left (hN'M' n hn))
      intro y hy
      exact h hy
    rw [zpowers_le, mem_normalizer_iff]
    intro y
    refine ⟨hle y, fun h => ?_⟩
    have h1 := hle _ h
    rwa [show a' * (a' * y * a'⁻¹) * a'⁻¹ = (a' * a') * y * (a' * a')⁻¹ by group, ha'a',
      one_mul, inv_one, mul_one] at h1
  have hTb : T'.map π = gsFixedLayer (A ⊔ Bq) α := by
    have h := GSThmB.OddQuot.map_fixedLayer hE2 hEN
    rw [fixedLayer_zpowers, hT'eq, Subgroup.map_sup, MonoidHom.map_zpowers,
      fixedLayer_zpowers] at h
    exact h
  set U' := V₀.subgroupOf C with hU'
  set V := U'.map π with hV
  have hU'T : U' ≤ (Open.fusionZStar ↥T').map T'.subtype := by
    intro y hy
    obtain ⟨t, ht, hty⟩ := hV₀Z (show (y : X) ∈ V₀ from hy)
    let ψ : ↥T' ≃* ↥T := subgroupOfEquivOfLe hTC
    have hcomap := GSThmB.OddQuot.comap_fusionZStar_of_surjective ψ.toMonoidHom ψ.surjective
      (by rw [show ψ.toMonoidHom.ker = ⊥ from (MonoidHom.ker_eq_bot_iff _).mpr ψ.injective,
        card_bot]; norm_num)
    refine ⟨ψ.symm t, ?_, ?_⟩
    · rw [← hcomap]
      show ψ (ψ.symm t) ∈ Open.fusionZStar ↥T
      rw [MulEquiv.apply_symm_apply]
      exact ht
    · apply Subtype.ext
      exact hty
  have hV' : V ≤ (Open.fusionZStar ↥(T'.map π)).map (T'.map π).subtype := by
    let f : ↥T' →* ↥(T'.map π) := (π.comp T'.subtype).codRestrict _ fun t =>
      mem_map_of_mem π t.2
    have hf : Function.Surjective f := by
      rintro ⟨q, t, ht, rfl⟩
      exact ⟨⟨t, ht⟩, rfl⟩
    have hfk : ¬ 2 ∣ Nat.card f.ker := by
      let g : f.ker →* pPrimeCore 2 ↥C :=
        (T'.subtype.comp f.ker.subtype).codRestrict (pPrimeCore 2 ↥C) fun k => by
          have h1 : f (k : T') = 1 := k.2
          exact (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val h1)
      have hg : Function.Injective g := fun k₁ k₂ h => by
        have h' := congrArg (fun x : pPrimeCore 2 ↥C => (x : ↥C)) h
        exact Subtype.ext (Subtype.ext h')
      have hodd : Odd (Nat.card (pPrimeCore 2 ↥C)) :=
        Nat.coprime_two_left.mp pPrimeCore_coprime_card
      exact Nat.not_even_iff_odd.mpr (hodd.of_dvd_nat (Subgroup.card_dvd_of_injective g hg)) ∘
        even_iff_two_dvd.mpr
    have hcomap := GSThmB.OddQuot.comap_fusionZStar_of_surjective f hf hfk
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨t, ht, hty⟩ := hU'T hy
    refine ⟨f t, ?_, ?_⟩
    · rw [← hcomap] at ht
      exact ht
    · rw [← hty]
      rfl
  rw [hTb] at hV'
  set B' := B.subgroupOf C with hB'
  have hB'p : IsPGroup 2 B' := hBe.isPGroup.comap_of_injective C.subtype C.subtype_injective
  have hB'e : IsElemTwo (B'.map π) := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨x₁, hx₁, rfl⟩ _ ⟨y₁, hy₁, rfl⟩
      rw [← map_mul, ← map_mul, show x₁ * y₁ = y₁ * x₁ from Subtype.ext (hBe.1 _ hx₁ _ hy₁)]
    · rintro _ ⟨x₁, hx₁, rfl⟩
      rw [← map_mul, show x₁ * x₁ = 1 from Subtype.ext (hBe.2 _ hx₁), map_one]
  have hB'card : Nat.card (B'.map π) = 8 := by
    rw [GSThmB.OddQuot.card_map_of_isPGroup hB'p, hB',
      Nat.card_congr (subgroupOfEquivOfLe hBC).toEquiv, hB8]
  have hB'T : B'.map π ≤ gsFixedLayer (A ⊔ Bq) α := by
    rw [← hTb]
    exact map_mono fun r hr => mem_subgroupOf.mpr (hBT (mem_subgroupOf.mp hr))
  have hVB : V ≤ B'.map π :=
    map_mono fun r hr => mem_subgroupOf.mpr (hV₀B (mem_subgroupOf.mp hr))
  have hV4 : Nat.card V = 4 := by
    have hU'p : IsPGroup 2 U' :=
      (hBe.isPGroup.to_le hV₀B).comap_of_injective C.subtype C.subtype_injective
    rw [hV, GSThmB.OddQuot.card_map_of_isPGroup hU'p, hU',
      Nat.card_congr (subgroupOfEquivOfLe (hV₀B.trans hBC)).toEquiv, hV₀4]
  obtain ⟨Eb, hEbe, hEb8, -, hEbA, hEbB'⟩ :=
    HeDG.exists_elem_eight hαα hcomm hαA hαB hAq hB'T hB'e hB'card hVB hV4 hV'
  have hEbB : ∀ r ∈ B', ∀ e' ∈ Eb, π r * e' = e' * π r := fun r hr e' he' =>
    hEbB' (π r) (mem_map_of_mem π hr) e' he'
  obtain ⟨Z, hZB, hZE, hZe, hZcard⟩ := HeDL.exists_lift_centralizing hB'p hEbe hEbB
  have hZM : ∀ z ∈ Z, z ∈ normalizer (M' : Set ↥C) ∧
      ∀ m ∈ M', z * m * z⁻¹ * m⁻¹ ∈ (pPrimeCore 2 ↥M').map M'.subtype := by
    intro z hz
    apply HeDL.normalizes_of_central hMp
    intro m hm
    have hzE : π z ∈ Eb := hZE ▸ mem_map_of_mem π hz
    exact hEbA _ hzE _ (mem_map_of_mem π hm)
  set E := Z.map C.subtype with hE
  have hEu : E ≤ C := map_subtype_le _
  have hEe : IsElemTwo E := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨x₁, hx₁, rfl⟩ _ ⟨y₁, hy₁, rfl⟩
      exact congrArg Subtype.val (hZe.1 _ hx₁ _ hy₁)
    · rintro _ ⟨x₁, hx₁, rfl⟩
      exact congrArg Subtype.val (hZe.2 _ hx₁)
  have hE8 : 8 ≤ Nat.card E := by
    rw [hE, card_map_of_injective C.subtype_injective, hZcard]
    exact hEb8
  have hEN : E ≤ normalizer (M : Set X) := by
    rintro _ ⟨z, hz, rfl⟩
    have hzN := (hZM z hz).1
    rw [mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have h1 := (mem_normalizer_iff.mp hzN ⟨y, hMu hy⟩).mp (mem_subgroupOf.mpr hy)
      exact mem_subgroupOf.mp h1
    · intro hy
      have hyC : y ∈ C := by
        have h2 := mul_mem (mul_mem (inv_mem z.2) (hMu hy)) z.2
        have h3 : ((z : ↥C) : X)⁻¹ * (C.subtype z * y * (C.subtype z)⁻¹) * z = y := by
          simp only [coe_subtype]
          group
        rwa [h3] at h2
      have h1 := (mem_normalizer_iff.mp hzN ⟨y, hyC⟩).mpr (mem_subgroupOf.mpr hy)
      exact mem_subgroupOf.mp h1
  have hEcen : ∀ e' ∈ E, ∀ l ∈ M, e' * l * e'⁻¹ * l⁻¹ ∈ (pPrimeCore 2 ↥M).map M.subtype := by
    rintro _ ⟨z, hz, rfl⟩ l hl
    have h1 := (hZM z hz).2 ⟨l, hMu hl⟩ (mem_subgroupOf.mpr hl)
    have h2 := mem_map_of_mem C.subtype h1
    rw [GSThmB.B5a.map_oddCoreIn_subgroupOf C M, inf_of_le_right hMu] at h2
    exact h2
  have hGW := gwTwoBalanced_of_locallyTwoBalanced solomonCommutingCoreInput hLB
  have hEB : ∀ x₁ ∈ E, ∀ y₁ ∈ B, x₁ * y₁ = y₁ * x₁ := by
    rintro _ ⟨z, hz, rfl⟩ y₁ hy₁
    have h1 := mem_centralizer_iff.mp (hZB hz) ⟨y₁, hBC hy₁⟩ (mem_subgroupOf.mpr hy₁)
    exact (congrArg Subtype.val h1).symm
  have hWB : wGroup B = ⊥ :=
    HeUV.wGroup_eq_bot_of_le hW hBe ((hBT.trans hTL).trans le_normalizer)
  have hWE : wGroup E = ⊥ := by
    rw [wGroup_eq_of_commute hGW (hEe.isAbelianTwoOfRank hE8)
      (hBe.isAbelianTwoOfRank (by omega)) hEB]
    exact hWB
  have hbal : ∀ e' ∈ E, e' ≠ 1 →
      ⁅(pPrimeCore 2 ↥M).map M.subtype ⊓ centralizer ({e'} : Set X),
        (pLayer ↥(M ⊓ centralizer ({e'} : Set X)) 2).map
          (M ⊓ centralizer ({e'} : Set X)).subtype⁆ ≤
      (pPrimeCore 2 ↥(centralizer ({e'} : Set X))).map (centralizer ({e'} : Set X)).subtype :=
    fun e' he' he1 => GrS5.commutator_oddCore_pLayer_le hS hUO hheld hK hu2 hMu hMp
      (mem_centralizer_singleton_iff.mp (hEu he')).symm (hZX e' he1)
  exact oddCore_le_center_of_wGroup_eq_bot hMu hMp hEu hEe.1 hEe.2 (by omega) hEN hEcen hWE
    hbal (Or.inr hE8)

end HeDG

theorem heldUDiagonalMeetStep_of_inputs
    (hS : SchreierFor Blueprint.Catalog)
    (hUO : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput) :
    HeldUDiagonalMeetStep := by
  intro X _ _ L hset hW a u U T M ha hLa _ hUL hUf hu hu1 hTL hTau hTp _ _ hMu hMp hne hfix _
  exact HeDG.central_of_diagonal hS hUO hheld hset hW ha hLa (hUL hu)
    ((HeDM.isElemTwo_of_isFourGroup hUf).1.2 u hu) hu1 hTL hTau hTp hMu hMp hne hfix

end CFSG.ComponentClassification.GrSLit
