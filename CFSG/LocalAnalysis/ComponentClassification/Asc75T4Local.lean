module

public import CFSG.LocalAnalysis.ComponentClassification.Asc75T4Pair
public import CFSG.LocalAnalysis.ComponentClassification.Asc75T4StepA

public section

namespace CFSG.ComponentClassification.Asc75T4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding
open scoped Pointwise

section General

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem card_sup_mul_card_inf {X N : Subgroup G} (hXN : X ≤ normalizer (N : Set G)) :
    Nat.card (X ⊔ N : Subgroup G) * Nat.card (X ⊓ N : Subgroup G) = Nat.card X * Nat.card N := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hXN
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hXN
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient X N hXN
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf X)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf (X ⊔ N))
  have h3 : Nat.card (N.subgroupOf X) = Nat.card (X ⊓ N : Subgroup G) := by
    rw [← Subgroup.card_map_of_injective X.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_comm]
  have h4 : Nat.card (N.subgroupOf (X ⊔ N)) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  rw [h2, h4, h1, h3, Nat.card_congr e.toEquiv]
  ring

omit [Finite G] in
theorem eq_bot_of_dvd_four_of_odd {H : Subgroup G} (h4 : Nat.card H ∣ 4)
    (hodd : Odd (Nat.card H)) : H = ⊥ := by
  rw [← card_eq_one]
  exact ((Nat.coprime_two_right.mpr hodd).pow_right 2).eq_one_of_dvd (by simpa using h4)

omit [Finite G] in
theorem HasFourGroup.two_le_pRank [Finite G] {X : Subgroup G} (h : HasFourGroup X) :
    2 ≤ CFSG.Open.pRank 2 X := by
  obtain ⟨E, hEX, hE, hE4⟩ := h
  have hinv : ∀ e ∈ E, e⁻¹ = e := fun e he => by
    rw [inv_eq_iff_mul_eq_one, ← pow_two, hE e he]
  refine CFSG.SectionRank.le_pRank one_lt_two hEX ⟨⟨⟨fun a b => ?_⟩⟩, hE⟩ (by rw [hE4]; norm_num)
  apply Subtype.ext
  rw [coe_mul, coe_mul, ← hinv _ (mul_mem a.2 b.2), mul_inv_rev, hinv _ a.2, hinv _ b.2]

omit [Finite G] in
theorem HasFourGroup.of_le_sup [Finite G] {X O E : Subgroup G} (hO : Odd (Nat.card O))
    (hXO : X ≤ normalizer (O : Set G)) (hEO : E ≤ normalizer (O : Set G)) (hEXO : E ≤ X ⊔ O)
    (hE : ∀ e ∈ E, e ^ 2 = 1) (hE4 : Nat.card E = 4) : HasFourGroup X := by
  set F := X ⊓ (E ⊔ O) with hF
  have hFO : F ≤ normalizer (O : Set G) := inf_le_left.trans hXO
  have hFOeq : F ⊔ O = E ⊔ O := by
    refine le_antisymm (sup_le inf_le_right le_sup_right) (sup_le ?_ le_sup_right)
    intro e he
    have h1 : e ∈ (X : Set G) * O := by
      rw [← coe_mul_of_left_le_normalizer_right X O hXO]
      exact hEXO he
    obtain ⟨x, hx, o, ho, rfl⟩ := Set.mem_mul.mp h1
    have hxF : x ∈ F := by
      refine ⟨hx, ?_⟩
      have : x = (x * o) * o⁻¹ := by group
      rw [this]
      exact mul_mem (mem_sup_left he) (mem_sup_right (inv_mem ho))
    exact mul_mem (mem_sup_left hxF) (mem_sup_right ho)
  have hEO1 : E ⊓ O = ⊥ := eq_bot_of_dvd_four_of_odd (hE4 ▸ card_dvd_of_le inf_le_left)
    (hO.of_dvd_nat (card_dvd_of_le inf_le_right))
  have hcardEO := card_sup_mul_card_inf hEO
  rw [hEO1, card_bot, mul_one, hE4] at hcardEO
  have hcardFO := card_sup_mul_card_inf hFO
  rw [hFOeq, hcardEO] at hcardFO
  have hOpos : 0 < Nat.card O := Nat.card_pos
  have hFcard : Nat.card F = 4 * Nat.card (F ⊓ O : Subgroup G) := by
    apply Nat.eq_of_mul_eq_mul_right hOpos
    rw [← hcardFO]
    ring
  have h4F : 2 ^ 2 ∣ Nat.card F := by
    rw [hFcard]
    exact Dvd.intro _ rfl
  obtain ⟨F₂, hF₂card, -, hF₂F⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_two
    (H := (⊥ : Subgroup G)) (L := F) (by simp) h4F bot_le
  have hF₂4 : Nat.card F₂ = 4 := by simpa using hF₂card
  have hF₂O : F₂ ⊓ O = ⊥ := eq_bot_of_dvd_four_of_odd (hF₂4 ▸ card_dvd_of_le inf_le_left)
    (hO.of_dvd_nat (card_dvd_of_le inf_le_right))
  refine ⟨F₂, hF₂F.trans inf_le_left, fun f hf => ?_, hF₂4⟩
  have hfEO : f ∈ (E : Set G) * O := by
    rw [← coe_mul_of_left_le_normalizer_right E O hEO]
    exact (hF₂F hf).2
  obtain ⟨e, he, o, ho, hfeo⟩ := Set.mem_mul.mp hfEO
  have he' : e⁻¹ = e := by rw [inv_eq_iff_mul_eq_one, ← pow_two, hE e he]
  have hsq : f ^ 2 ∈ O := by
    have h1 : f ^ 2 = (e * o * e⁻¹) * o := by
      rw [← hfeo, he']
      simp only [pow_two, mul_assoc]
    rw [h1]
    exact mul_mem ((mem_normalizer_iff.mp (hEO he) o).mp ho) ho
  have hmem : f ^ 2 ∈ F₂ ⊓ O := ⟨pow_mem hf 2, hsq⟩
  rw [hF₂O] at hmem
  exact hmem

omit [Finite G] in
theorem exists_mem_centralizer_of_commutator [Finite G] {T O : Subgroup G} (hT : IsPGroup 2 T)
    (hO : Odd (Nat.card O)) (hTO : T ≤ normalizer (O : Set G)) {k : G}
    (hk : k ∈ normalizer (O : Set G)) (hc : ∀ t ∈ T, t * k * t⁻¹ * k⁻¹ ∈ O) :
    ∃ c ∈ centralizer (T : Set G), c⁻¹ * k ∈ O := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let α : T →* MulAut G := MulAut.conj.comp T.subtype
  let S : Set G := {x | k⁻¹ * x ∈ O}
  have hk' : k⁻¹ ∈ normalizer (O : Set G) := inv_mem hk
  have hS : ∀ t : T, ∀ x ∈ S, α t x ∈ S := by
    intro t x hx
    have hx' : k⁻¹ * x ∈ O := hx
    show k⁻¹ * ((t : G) * x * (t : G)⁻¹) ∈ O
    have h1 : k⁻¹ * ((t : G) * k * (t : G)⁻¹ * k⁻¹) * k⁻¹⁻¹ ∈ O :=
      (mem_normalizer_iff.mp hk' _).mp (hc t t.2)
    have h2 : (t : G) * (k⁻¹ * x) * (t : G)⁻¹ ∈ O := (mem_normalizer_iff.mp (hTO t.2) _).mp hx'
    have h3 : k⁻¹ * ((t : G) * x * (t : G)⁻¹) =
        (k⁻¹ * ((t : G) * k * (t : G)⁻¹ * k⁻¹) * k⁻¹⁻¹) * ((t : G) * (k⁻¹ * x) * (t : G)⁻¹) := by
      group
    rw [h3]
    exact mul_mem h1 h2
  have hcard : ¬ 2 ∣ Nat.card S := by
    have he : Nat.card S = Nat.card O := Nat.card_congr
      { toFun := fun x => ⟨k⁻¹ * x.1, x.2⟩
        invFun := fun o => ⟨k * o.1, by simp [S]⟩
        left_inv := fun x => Subtype.ext (by simp)
        right_inv := fun o => Subtype.ext (by simp) }
    rw [he]
    exact hO.not_two_dvd_nat
  obtain ⟨c, hcS, hfix⟩ :=
    CFSG.Semidihedral.Principal.CoprimeFixedPoint.exists_fixed_of_invariant 2 hT α S hS hcard
  refine ⟨c, mem_centralizer_iff.mpr fun t ht => ?_, ?_⟩
  · have h := hfix ⟨t, ht⟩
    change t * c * t⁻¹ = c at h
    calc t * c = t * c * t⁻¹ * t := by group
      _ = c * t := by rw [h]
  · have : c⁻¹ * k = (k⁻¹ * c)⁻¹ := by group
    rw [this]
    exact inv_mem hcS

omit [Finite G] in
theorem le_inf_centralizer_sup [Finite G] {K T O : Subgroup G} (hT : IsPGroup 2 T)
    (hO : Odd (Nat.card O)) (hOK : O ≤ K) (hKO : K ≤ normalizer (O : Set G))
    (hTO : T ≤ normalizer (O : Set G)) (hc : ∀ t ∈ T, ∀ k ∈ K, t * k * t⁻¹ * k⁻¹ ∈ O) :
    K ≤ (K ⊓ centralizer (T : Set G)) ⊔ O := by
  intro k hk
  obtain ⟨c, hcT, hcO⟩ :=
    exists_mem_centralizer_of_commutator hT hO hTO (hKO hk) fun t ht => hc t ht k hk
  have hcK : c ∈ K := by
    have : c = k * (c⁻¹ * k)⁻¹ := by group
    rw [this]
    exact mul_mem hk (inv_mem (hOK hcO))
  have : k = c * (c⁻¹ * k) := by group
  rw [this]
  exact mul_mem (mem_sup_left ⟨hcK, hcT⟩) (mem_sup_right hcO)

@[expose] def CoversLayer (X A : Subgroup G) : Prop :=
  twoPrimeLayerIn A ≤ (twoPrimeLayerIn A ⊓ centralizer (X : Set G)) ⊔ oddCoreIn A

theorem coversLayer_of_commutator {X A : Subgroup G} (hX : IsPGroup 2 X)
    (hXA : X ≤ normalizer (A : Set G))
    (hc : ∀ x ∈ X, ∀ k ∈ twoPrimeLayerIn A, x * k * x⁻¹ * k⁻¹ ∈ oddCoreIn A) :
    CoversLayer X A := by
  refine le_inf_centralizer_sup hX (odd_card_oddCoreIn A) ?_ ?_
    (hXA.trans (normalizer_le_normalizer_oddCoreIn A)) hc
  · rw [← oddCoreIn_twoPrimeLayerIn A]
    exact oddCoreIn_le _
  · exact (twoPrimeLayerIn_le A).trans (normalIn_le_normalizer (oddCoreIn_normalIn A))

theorem isSemisimpleQ_inf_centralizer {X A : Subgroup G} (h : CoversLayer X A) :
    IsSemisimpleQ (twoPrimeLayerIn A ⊓ centralizer (X : Set G)) :=
  isSemisimpleQ_of_le_sup inf_le_left (by rw [oddCoreIn_twoPrimeLayerIn]; exact h)
    (isSemisimpleQ_twoPrimeLayerIn A)

theorem hasFourGroup_inf_centralizer {X A : Subgroup G} (h : CoversLayer X A)
    (h4 : HasFourGroup (twoPrimeLayerIn A)) :
    HasFourGroup (twoPrimeLayerIn A ⊓ centralizer (X : Set G)) := by
  obtain ⟨E, hEK, hE, hE4⟩ := h4
  have hKO : twoPrimeLayerIn A ≤ normalizer (oddCoreIn A : Set G) :=
    (twoPrimeLayerIn_le A).trans (normalIn_le_normalizer (oddCoreIn_normalIn A))
  exact HasFourGroup.of_le_sup (odd_card_oddCoreIn A) (inf_le_left.trans hKO) (hEK.trans hKO)
    (hEK.trans h) hE hE4

theorem inf_normalizer_le_normalizer_inf_centralizer (X A : Subgroup G) :
    centralizer (X : Set G) ⊓ normalizer (A : Set G) ≤
      normalizer ((twoPrimeLayerIn A ⊓ centralizer (X : Set G) : Subgroup G) : Set G) := by
  intro m ⟨hmC, hmN⟩
  have h1 := normalizer_le_normalizer_twoPrimeLayerIn A hmN
  have h2 : m ∈ normalizer (centralizer (X : Set G) : Set G) := le_normalizer hmC
  rw [mem_normalizer_iff] at h1 h2 ⊢
  intro y
  rw [mem_inf, mem_inf, h1 y, h2 y]

omit [Finite G] in
theorem map_subtype_subgroupOf_of_le {X M : Subgroup G} (hXM : X ≤ M) :
    (X.subgroupOf M).map M.subtype = X := by
  rw [subgroupOf_map_subtype, inf_of_le_left hXM]

theorem twoPrimeLayerIn_subgroupOf_map {X M : Subgroup G} (hXM : X ≤ M) :
    (twoPrimeLayerIn (X.subgroupOf M)).map M.subtype = twoPrimeLayerIn X := by
  rw [← twoPrimeLayerIn_map M.subtype M.subtype_injective, map_subtype_subgroupOf_of_le hXM]

theorem oddCoreIn_subgroupOf_map {X M : Subgroup G} (hXM : X ≤ M) :
    (oddCoreIn (X.subgroupOf M)).map M.subtype = oddCoreIn X := by
  rw [← oddCoreIn_map M.subtype M.subtype_injective, map_subtype_subgroupOf_of_le hXM]

theorem twoPrimeLayerIn_top_map (M : Subgroup G) :
    (twoPrimeLayerIn (⊤ : Subgroup M)).map M.subtype = twoPrimeLayerIn M := by
  rw [← twoPrimeLayerIn_map M.subtype M.subtype_injective, ← MonoidHom.range_eq_map,
    range_subtype]

omit [Finite G] in
theorem normalIn_map_iff {G' : Type*} [Group G'] {f : G →* G'} (hf : Function.Injective f)
    {N X : Subgroup G} : NormalIn (N.map f) (X.map f) ↔ NormalIn N X := by
  constructor
  · intro h
    refine normalIn_of_le_normalizer ((map_le_map_iff_of_injective hf).mp h.1) fun x hx => ?_
    have h1 := normalIn_le_normalizer h (mem_map_of_mem f hx)
    rw [mem_normalizer_iff] at h1 ⊢
    intro y
    have h2 := h1 (f y)
    rw [mem_map_iff_mem hf, ← map_inv, ← map_mul, ← map_mul, mem_map_iff_mem hf] at h2
    exact h2
  · intro h
    refine normalIn_of_le_normalizer (map_mono h.1) ?_
    rintro _ ⟨x, hx, rfl⟩
    have h1 := normalIn_le_normalizer h hx
    rw [mem_normalizer_iff] at h1 ⊢
    intro y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨x * z * x⁻¹, (h1 z).mp hz, by rw [map_mul, map_mul, map_inv]⟩
    · rintro ⟨z, hz, hzy⟩
      refine ⟨x⁻¹ * z * x, ?_, ?_⟩
      · have := (h1 (x⁻¹ * z * x)).mpr (by rwa [show x * (x⁻¹ * z * x) * x⁻¹ = z by group])
        exact this
      · rw [map_mul, map_mul, map_inv, hzy]
        group

theorem pRank_map_subtype {M : Subgroup G} (Y : Subgroup M) :
    CFSG.Open.pRank 2 (Y.map M.subtype) = CFSG.Open.pRank 2 Y := by
  refine le_antisymm ?_ (CFSG.SectionRank.pRank_le_map one_lt_two M.subtype M.subtype_injective Y)
  obtain ⟨E, hEY, hE, hcard⟩ := CFSG.SectionRank.exists_pRank one_lt_two (Y.map M.subtype)
  have hEM : E ≤ M := hEY.trans (map_subtype_le Y)
  refine CFSG.SectionRank.le_pRank one_lt_two (E := E.subgroupOf M) ?_ ?_ ?_
  · intro y hy
    obtain ⟨y', hy', hyy⟩ := hEY hy
    rwa [show y = y' from Subtype.ext hyy.symm]
  · refine ⟨⟨⟨fun x y => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩
    · have h := congrArg Subtype.val (hE.1.is_comm.comm ⟨x.1.1, x.2⟩ ⟨y.1.1, y.2⟩)
      simpa using h
    · simpa using hE.2 _ hx
  · rw [Nat.card_congr (subgroupOfEquivOfLe hEM).toEquiv, hcard]

omit [Finite G] in
theorem tightlyEmbedded_subgroupOf {A M X : Subgroup G} (hA : TightlyEmbedded A) (hXA : X ≤ A)
    (hXM : X ≤ M) (hX : Even (Nat.card X)) (hN : M ⊓ normalizer (A : Set G) ≤
      normalizer (X : Set G)) : TightlyEmbedded (X.subgroupOf M) := by
  refine ⟨by rwa [Nat.card_congr (subgroupOfEquivOfLe hXM).toEquiv], fun m hm => ?_⟩
  have hmX : (m : G) ∉ normalizer (X : Set G) := by
    intro h
    apply hm
    rw [← subgroupOf_normalizer_eq hXM]
    exact h
  have hmA : (m : G) ∉ normalizer (A : Set G) := fun h => hmX (hN ⟨m.2, h⟩)
  have hmap : ((X.subgroupOf M) ⊓ rightConjugate (X.subgroupOf M) m).map M.subtype =
      X ⊓ rightConjugate X m := by
    ext y
    constructor
    · rintro ⟨z, ⟨hz1, hz2⟩, rfl⟩
      refine ⟨hz1, (mem_rightConjugate_iff X m z).mpr ?_⟩
      have := (mem_rightConjugate_iff _ m z).mp hz2
      exact this
    · rintro ⟨hy1, hy2⟩
      refine ⟨⟨y, hXM hy1⟩, ⟨hy1, (mem_rightConjugate_iff _ m _).mpr ?_⟩, rfl⟩
      exact (mem_rightConjugate_iff X m y).mp hy2
  rw [← card_map_of_injective M.subtype_injective, hmap]
  have hodd := hA.2 m hmA
  exact hodd.of_dvd_nat (card_dvd_of_le (inf_le_inf hXA
    (fun y hy => (mem_rightConjugate_iff A m y).mpr (hXA ((mem_rightConjugate_iff X m y).mp hy)))))

end General

@[expose] def Thm4Below (n : ℕ) : Prop :=
  ∀ (H : Type) [Group H] [Finite H], Nat.card H < n → ∀ Q : Subgroup H, TightlyEmbedded Q →
    twoPrimeLayerIn Q ≠ oddCoreIn Q → Thm4Conclusion Q

variable {G : Type} [Group G] [Finite G]

theorem eq_or_normalizes_of_coversLayer_of_normalIn {A B X : Subgroup G}
    (hA : TightlyEmbedded A) (hB : TightlyEmbedded B)
    (hAB : Even (Nat.card (A ⊓ B : Subgroup G)) → A = B) (hIAB : CaseIPair A B)
    (hIBA : CaseIPair B A) (hA4 : HasFourGroup (twoPrimeLayerIn A))
    (hB4 : HasFourGroup (twoPrimeLayerIn B)) (hXA : CoversLayer X A) (hXB : CoversLayer X B)
    (hNA : NormalIn (twoPrimeLayerIn A ⊓ centralizer (X : Set G))
      (twoPrimeLayerIn (centralizer (X : Set G))))
    (hNB : NormalIn (twoPrimeLayerIn B ⊓ centralizer (X : Set G))
      (twoPrimeLayerIn (centralizer (X : Set G)))) :
    A = B ∨ (twoPrimeLayerIn B ≤ normalizer (A : Set G) ∧
      twoPrimeLayerIn A ≤ normalizer (B : Set G)) :=
  eq_or_normalizes_of_normalIn hA hB hAB hIAB hIBA
    (inf_le_left.trans (twoPrimeLayerIn_le A)) (inf_le_left.trans (twoPrimeLayerIn_le B))
    hNA hNB (isSemisimpleQ_inf_centralizer hXA) (hasFourGroup_inf_centralizer hXA hA4)
    (hasFourGroup_inf_centralizer hXB hB4)

end CFSG.ComponentClassification.Asc75T4
