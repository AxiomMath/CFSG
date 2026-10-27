module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4End43N
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitTwoComp
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeStd
public import CFSG.GH74.Uniqueness.Bender.AutFixed

public section

namespace CFSG.ComponentClassification.GrSLit.GrS4

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.GH74.Uniqueness.Bender

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
@[expose] noncomputable def heldQuotConj (K : Subgroup G) :
    ↥(normalizer (K : Set G)) →* MulAut (↥K ⧸ pPrimeCore 2 ↥K) :=
  Semidihedral.Principal.CoprimeFixedPoint.quotientAction
    (LocalAnalysis.ComponentInitial.normalizerConjHom K) (pPrimeCore 2 ↥K) fun a n hn => by
      have h := Subgroup.characteristic_iff_map_eq.mp
        (inferInstance : (pPrimeCore 2 ↥K).Characteristic)
        (LocalAnalysis.ComponentInitial.normalizerConjHom K a)
      rw [← h]
      exact ⟨n, hn, rfl⟩

omit [Finite G] in
theorem odd_card_sup_held {A B : Subgroup G} (hBA : B ≤ normalizer (A : Set G))
    (hA : Odd (Nat.card A)) (hB : Odd (Nat.card B)) : Odd (Nat.card (A ⊔ B : Subgroup G)) := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hBA
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hBA
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient B A hBA
  rw [sup_comm, Subgroup.card_eq_card_quotient_mul_card_subgroup (A.subgroupOf (B ⊔ A)),
    ← Nat.card_congr e.toEquiv,
    Nat.card_congr (subgroupOfEquivOfLe (le_sup_right : A ≤ B ⊔ A)).toEquiv]
  exact (Odd.of_dvd_nat hB (Subgroup.card_quotient_dvd_card _)).mul hA

theorem exists_isPComponent_of_surjective {Q : Type} [Group Q] [IsSimpleGroup Q]
    (hQ : ∃ x y : Q, x * y ≠ y * x) (hQ2 : Even (Nat.card Q)) {C H : Subgroup G} (hHC : H ≤ C)
    (hsub : (H.subgroupOf C).IsSubnormal) (ψ : ↥H →* Q) (hψ : Function.Surjective ψ)
    (hodd : Odd (Nat.card ψ.ker)) :
    ∃ L : Subgroup G, L ≤ H ∧ IsPComponent 2 (L.subgroupOf C) ∧
      Nonempty (↥L ⧸ pPrimeCore 2 ↥L ≃* Q) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite Q := Finite.of_surjective ψ hψ
  obtain ⟨-, -, hPperf, -, hsolv, -⟩ := perfect_residual_characterization (G := ↥H)
  set P : Subgroup ↥H := perfectResidual ↥H with hP
  have hPQ : P.map ψ = ⊤ := by
    have hn : (P.map ψ).Normal := (inferInstance : P.Normal).map ψ hψ
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (P.map ψ) with h | h
    · exfalso
      have hle : P ≤ ψ.ker := (Subgroup.map_eq_bot_iff _).mp h
      have hs : Group.IsSolvable (↥H ⧸ ψ.ker) := (hsolv ψ.ker).mpr hle
      set eQ := QuotientGroup.quotientKerEquivOfSurjective ψ hψ
      have hs' : Group.IsSolvable Q := by
        have := hs
        exact Group.isSolvable_of_surjective (f := eQ.toMonoidHom) eQ.surjective
      obtain ⟨x, y, hxy⟩ := hQ
      exact hxy ((IsSimpleGroup.comm_iff_isSolvable).mpr hs' x y)
    · exact h
  set L : Subgroup G := P.map H.subtype with hL
  have hLH : L ≤ H := map_subtype_le P
  set eL : ↥P ≃* ↥L := P.equivMapOfInjective H.subtype H.subtype_injective with heL
  set ι : ↥L →* ↥H := P.subtype.comp eL.symm.toMonoidHom with hι
  set φ : ↥L →* Q := ψ.comp ι with hφ
  have hφs : Function.Surjective φ := by
    intro q
    obtain ⟨p, hp, rfl⟩ : q ∈ P.map ψ := hPQ ▸ mem_top q
    refine ⟨eL ⟨p, hp⟩, ?_⟩
    simp only [hφ, hι, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply, Subgroup.coe_subtype]
  have hφodd : Odd (Nat.card φ.ker) := by
    have hιi : Function.Injective ι := P.subtype_injective.comp eL.symm.injective
    have hle : φ.ker.map ι ≤ ψ.ker := by
      rintro _ ⟨y, hy, rfl⟩
      exact hy
    rw [← Subgroup.card_map_of_injective hιi]
    exact hodd.of_dvd_nat (Subgroup.card_dvd_of_le hle)
  have hcore : pPrimeCore 2 ↥L = φ.ker := by
    apply le_antisymm
    · have hn : ((pPrimeCore 2 ↥L).map φ).Normal := (pPrimeCore_normal (p := 2)).map φ hφs
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((pPrimeCore 2 ↥L).map φ) with h | h
      · exact (Subgroup.map_eq_bot_iff _).mp h
      · exfalso
        have h1 : Nat.card Q ∣ Nat.card (pPrimeCore 2 ↥L) := by
          have := card_map_dvd (pPrimeCore 2 ↥L) φ
          rwa [h, card_top] at this
        have hodd' : Odd (Nat.card (pPrimeCore 2 ↥L)) :=
          Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := ↥L))
        exact (Nat.not_even_iff_odd.mpr (hodd'.of_dvd_nat h1)) hQ2
    · exact le_sSup ⟨φ.normal_ker, Nat.coprime_two_left.mpr hφodd⟩
  have e : ↥L ⧸ pPrimeCore 2 ↥L ≃* Q :=
    (QuotientGroup.quotientMulEquivOfEq hcore).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφs)
  have hLC : L ≤ C := hLH.trans hHC
  have hHL : ∀ h ∈ H, ∀ l ∈ L, h * l * h⁻¹ ∈ L := by
    intro h hh l hl
    obtain ⟨p, hp, rfl⟩ := mem_map.mp hl
    exact ⟨_, (inferInstance : P.Normal).conj_mem p hp ⟨h, hh⟩, rfl⟩
  have hsubL : (L.subgroupOf C).IsSubnormal := by
    refine IsSubnormal.step _ (H.subgroupOf C) (subgroupOf_mono C hLH) hsub ?_
    rw [normal_subgroupOf_iff_le_normalizer (subgroupOf_mono C hLH)]
    intro c hc
    rw [mem_normalizer_iff]
    intro y
    simp only [mem_subgroupOf, coe_mul, coe_inv]
    refine ⟨fun hy => hHL _ (mem_subgroupOf.mp hc) _ hy, fun hy => ?_⟩
    have := hHL _ (inv_mem (mem_subgroupOf.mp hc)) _ hy
    simpa only [inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using this
  have hperf : Group.IsPerfect ↥L := by
    have : Group.IsPerfect ↥P := hPperf
    exact Group.IsPerfect.ofSurjective (f := eL.toMonoidHom) eL.surjective
  refine ⟨L, hLH, (HarrisLit.isTwoComponentIn_iff hLC).mp ⟨hLC, hsubL, hperf, ?_⟩, ⟨e⟩⟩
  exact LocalCores.isQuasisimple_of_mulEquiv e.symm (isQuasisimple_of_simple_nonab hQ)

theorem card_inf_centralizer_eq {K : Subgroup G} {a : G} (ha : a ∈ normalizer (K : Set G))
    (haa : a * a = 1) :
    Nat.card ↥(K ⊓ centralizer ({a} : Set G)) =
      Nat.card ↥(autFixed (heldQuotConj K ⟨a, ha⟩)) *
        Nat.card ↥(oddIn K ⊓ centralizer ({a} : Set G)) := by
  set D : Subgroup G := K ⊓ centralizer ({a} : Set G) with hD
  set f : ↥D →* ↥K ⧸ pPrimeCore 2 ↥K :=
    (QuotientGroup.mk' (pPrimeCore 2 ↥K)).comp (Subgroup.inclusion inf_le_left) with hf
  have hrange : f.range = autFixed (heldQuotConj K ⟨a, ha⟩) := by
    ext q
    constructor
    · rintro ⟨y, rfl⟩
      have hy : (y : G) * a = a * y := mem_centralizer_singleton_iff.mp (mem_inf.mp y.2).2
      have e1 : LocalAnalysis.ComponentInitial.normalizerConjHom K ⟨a, ha⟩
          (Subgroup.inclusion inf_le_left y) = Subgroup.inclusion inf_le_left y := by
        apply Subtype.ext
        change a * (y : G) * a⁻¹ = y
        rw [← hy, mul_inv_cancel_right]
      change ((LocalAnalysis.ComponentInitial.normalizerConjHom K ⟨a, ha⟩
        (Subgroup.inclusion inf_le_left y) : ↥K) : ↥K ⧸ pPrimeCore 2 ↥K) = _
      rw [e1]
      rfl
    · intro hq
      obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
      have hk : (k : G)⁻¹ * (a * k * a⁻¹) ∈ oddIn K := by
        have h1 : ((k⁻¹ * LocalAnalysis.ComponentInitial.normalizerConjHom K ⟨a, ha⟩ k : ↥K)) ∈
            pPrimeCore 2 ↥K := QuotientGroup.eq.mp hq.symm
        exact ⟨_, h1, rfl⟩
      obtain ⟨o, ho, hko⟩ := exists_commute_mul_mem (odd_card_map_pPrimeCore K) haa hk
      obtain ⟨o', ho', rfl⟩ := mem_map.mp ho
      refine ⟨⟨k * o', mul_mem k.2 o'.2, mem_centralizer_singleton_iff.mpr hko.symm⟩, ?_⟩
      change QuotientGroup.mk (k * o') = QuotientGroup.mk k
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr ho', mul_one]
  have hker : f.ker.map D.subtype = oddIn K ⊓ centralizer ({a} : Set G) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨⟨Subgroup.inclusion inf_le_left z, (QuotientGroup.eq_one_iff _).mp hz, rfl⟩,
        (mem_inf.mp z.2).2⟩
    · rintro ⟨⟨k, hk, rfl⟩, hya⟩
      refine ⟨⟨k, mem_inf.mpr ⟨k.2, hya⟩⟩, ?_, rfl⟩
      change QuotientGroup.mk' _ (Subgroup.inclusion _ _) = 1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hk
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hrange,
    ← hker, Subgroup.card_map_of_injective D.subtype_injective]

end CFSG.ComponentClassification.GrSLit.GrS4
