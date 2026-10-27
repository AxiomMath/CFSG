module

public import CFSG.LocalAnalysis.AGLEmbedding.ZZPrimeDefs
import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CanonicalCoprimePreimages

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers

section Perfect

variable {Y : Type*} [Group Y] [Finite Y]

theorem coprime_card_of_surjective_of_perfect {X : Type*} [Group X] {J : Subgroup Y} {q : ℕ}
    (hJ : ∀ V : Subgroup Y, V ≤ J → ⁅V, V⁆ = V → q.Coprime (Nat.card V))
    (ψ : ↥J →* X) (hψ : Function.Surjective ψ) (B : Subgroup X) (hB : ⁅B, B⁆ = B) :
    q.Coprime (Nat.card B) := by
  have hBp : Group.IsPerfect B := Subgroup.isPerfect_iff.mpr hB
  set R₀ := perfectResidualOf (B.comap ψ)
  have hR₀ : R₀.map ψ = B := finite_canonical_perfect_preimage_image_eq ψ hψ B hBp
  have hR₀p : ⁅R₀, R₀⁆ = R₀ :=
    Subgroup.isPerfect_iff.mp (finite_perfectResidualOf_isPerfect (B.comap ψ))
  have hV : q.Coprime (Nat.card (R₀.map J.subtype)) :=
    hJ _ (Subgroup.map_subtype_le _) (by rw [← Subgroup.map_commutator, hR₀p])
  rw [Subgroup.card_map_of_injective J.subtype_injective] at hV
  rw [← hR₀]
  exact Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd R₀ ψ) hV

theorem coprime_factorial_of_surjective {J : Subgroup Y} {q n : ℕ} (hq : q.Prime) (hq5 : 5 ≤ q)
    (hJ : ∀ V : Subgroup Y, V ≤ J → ⁅V, V⁆ = V → q.Coprime (Nat.card V))
    (ψ : ↥J →* Equiv.Perm (Fin n)) (hψ : Function.Surjective ψ) : q.Coprime n.factorial := by
  rw [Nat.Prime.coprime_iff_not_dvd hq, hq.dvd_factorial]
  intro hqn
  have h5 : 5 ≤ Nat.card (Fin n) := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hA := coprime_card_of_surjective_of_perfect hJ ψ hψ (alternatingGroup (Fin n))
    (commutator_alternatingGroup_eq_self h5)
  have hAc := two_mul_nat_card_alternatingGroup (α := Fin n)
  rw [Nat.card_perm, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin] at hAc
  have hqf : q ∣ n.factorial := hq.dvd_factorial.mpr hqn
  rw [← hAc] at hqf
  rcases (Nat.Prime.dvd_mul hq).mp hqf with h | h
  · have := Nat.le_of_dvd (by norm_num) h
    omega
  · exact (Nat.Prime.coprime_iff_not_dvd hq).mp hA h

theorem coprime_card_of_coprime_card_quotient_pCore_two {J : Subgroup Y} {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) (h : q.Coprime (Nat.card (↥J ⧸ CFSG.pCore 2 ↥J))) :
    q.Coprime (Nat.card J) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥J)]
  refine Nat.Coprime.mul_right h ?_
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥J))
  rw [hk]
  exact Nat.Coprime.pow_right k ((Nat.coprime_primes hq Nat.prime_two).mpr hq2)

theorem coprime_card_of_quotient_perm {J : Subgroup Y} {q n : ℕ} (hq : q.Prime) (hq5 : 5 ≤ q)
    (hJ : ∀ V : Subgroup Y, V ≤ J → ⁅V, V⁆ = V → q.Coprime (Nat.card V))
    (e : ↥J ⧸ CFSG.pCore 2 ↥J ≃* Equiv.Perm (Fin n)) : q.Coprime (Nat.card J) := by
  refine coprime_card_of_coprime_card_quotient_pCore_two hq (by omega) ?_
  rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
  exact coprime_factorial_of_surjective hq hq5 hJ
    (e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥J)))
    (e.surjective.comp (QuotientGroup.mk'_surjective _))

theorem coprime_card_of_quotient_perm_prod {J : Subgroup Y} {q r m : ℕ} (hq : q.Prime)
    (hq5 : 5 ≤ q) (hJ : ∀ V : Subgroup Y, V ≤ J → ⁅V, V⁆ = V → q.Coprime (Nat.card V))
    (e : ↥J ⧸ CFSG.pCore 2 ↥J ≃* (Equiv.Perm (Fin r) × Equiv.Perm (Fin m))) :
    q.Coprime (Nat.card J) := by
  refine coprime_card_of_coprime_card_quotient_pCore_two hq (by omega) ?_
  rw [Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_perm, Nat.card_perm,
    Nat.card_eq_fintype_card (α := Fin r), Nat.card_eq_fintype_card (α := Fin m),
    Fintype.card_fin, Fintype.card_fin]
  have hs : Function.Surjective (e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥J))) :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  exact Nat.Coprime.mul_right
    (coprime_factorial_of_surjective hq hq5 hJ
      ((MonoidHom.fst _ _).comp (e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥J))))
      (Prod.fst_surjective.comp hs))
    (coprime_factorial_of_surjective hq hq5 hJ
      ((MonoidHom.snd _ _).comp (e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥J))))
      (Prod.snd_surjective.comp hs))

theorem coprime_card_of_le_range_of_perfect {X : Type*} [Group X] {J : Subgroup Y} {q : ℕ}
    (hJ : ∀ V : Subgroup Y, V ≤ J → ⁅V, V⁆ = V → q.Coprime (Nat.card V))
    (ψ : ↥J →* X) (B : Subgroup X) (hBr : B ≤ ψ.range) (hB : ⁅B, B⁆ = B) :
    q.Coprime (Nat.card B) := by
  have hB' : ⁅B.subgroupOf ψ.range, B.subgroupOf ψ.range⁆ = B.subgroupOf ψ.range := by
    apply Subgroup.map_injective ψ.range.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hBr, hB]
  have h := coprime_card_of_surjective_of_perfect hJ ψ.rangeRestrict ψ.rangeRestrict_surjective
    (B.subgroupOf ψ.range) hB'
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBr).toEquiv] at h

end Perfect

section Bar

variable {G : Type} [Group G] [Finite G]

theorem coprime_card_of_le_barM_of_perfect {M X : Subgroup G} (hXM : X ≤ M) {q : ℕ}
    (hX : ∀ V : Subgroup G, V ≤ X → ⁅V, V⁆ = V → q.Coprime (Nat.card V))
    {B : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hB : B ≤ barM M X) (hBp : ⁅B, B⁆ = B) :
    q.Coprime (Nat.card B) := by
  set ψ : ↥X →* ↥M ⧸ CFSG.pCore 2 ↥M :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp (Subgroup.inclusion hXM)
  have hr : ψ.range = barM M X := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    rfl
  exact coprime_card_of_le_range_of_perfect hX ψ B (hr ▸ hB) hBp

theorem coprime_card_of_nineThreeSix {M S L : Subgroup G} {q : ℕ} (hq : q.Prime)
    (hq5 : 5 ≤ q) (hJ : ∀ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
      V ≤ barM M (Subgroup.normalizer (S : Set G) ⊓ L) → ⁅V, V⁆ = V → q.Coprime (Nat.card V))
    (h6 : NineThreeSix M S L ∨ NineThreeSeven M S L) :
    q.Coprime (Nat.card (barM M (Subgroup.normalizer (S : Set G) ⊓ L))) := by
  rcases h6 with ⟨-, n, -, ⟨e⟩⟩ | ⟨-, n, -, ⟨e⟩⟩ <;>
    exact coprime_card_of_quotient_perm hq hq5 hJ e

omit [Finite G] in
theorem coprime_card_of_nineThreeFour {M S L : Subgroup G} {q : ℕ} (hq : q.Prime) (hq5 : 5 ≤ q)
    (h4 : NineThreeFour M S L) :
    q.Coprime (Nat.card (barM M (Subgroup.normalizer (S : Set G) ⊓ L))) := by
  obtain ⟨-, hZ, -, -, ⟨e⟩⟩ := h4
  set Lb := barM M L
  set P := barM M (Subgroup.normalizer (S : Set G) ⊓ L)
  have hPL : P ≤ Lb := barM_mono inf_le_right
  set P' : Subgroup ↥Lb := P.subgroupOf Lb
  set φ : ↥P' →* ↥Lb ⧸ Subgroup.center ↥Lb :=
    (QuotientGroup.mk' (Subgroup.center ↥Lb)).comp P'.subtype
  have hrange : φ.range = P'.map (QuotientGroup.mk' (Subgroup.center ↥Lb)) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hcard : Nat.card P' = Nat.card φ.ker * Nat.card φ.range := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  have hker : Nat.card φ.ker ∣ 3 := by
    rw [← hZ]
    have hle : φ.ker.map P'.subtype ≤ Subgroup.center ↥Lb := by
      rintro _ ⟨x, hx, rfl⟩
      have h1 : QuotientGroup.mk' (Subgroup.center ↥Lb) (x : ↥Lb) = 1 := hx
      exact (QuotientGroup.eq_one_iff _).mp h1
    have := Subgroup.card_dvd_of_le hle
    rwa [Subgroup.card_map_of_injective P'.subtype_injective] at this
  have hS4 : Nat.card φ.range = 24 := by
    rw [hrange, Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    rfl
  have h72 : Nat.card P ∣ 72 := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPL).toEquiv, hcard, hS4]
    exact Nat.mul_dvd_mul_right hker 24
  refine Nat.Coprime.coprime_dvd_right h72 ?_
  rw [Nat.Prime.coprime_iff_not_dvd hq]
  intro hdvd
  have h72' : (72 : ℕ) = 2 ^ 3 * 3 ^ 2 := by norm_num
  rw [h72'] at hdvd
  rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | h
  · have := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h)
    omega
  · have := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp (hq.dvd_of_dvd_pow h)
    omega

theorem coprime_card_of_nineThreeEight {M S L : Subgroup G} {q : ℕ} (hq : q.Prime)
    (hq5 : 5 ≤ q) (hJ : ∀ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
      V ≤ barM M (Subgroup.normalizer (S : Set G) ⊓ L) → ⁅V, V⁆ = V → q.Coprime (Nat.card V))
    (h8 : NineThreeEight M S L) :
    q.Coprime (Nat.card (barM M (Subgroup.normalizer (S : Set G) ⊓ L))) := by
  obtain ⟨-, N, r, -, -, -, -, -, -, φ, -, -⟩ := h8
  exact coprime_card_of_quotient_perm_prod hq hq5 hJ φ

theorem coprime_card_of_nineThreeTwo (hKP : KFactParabolicPrime) {M S L : Subgroup G}
    (hLc : IsComponentOf (barM M L) ⊤) (h2 : NineThreeTwo M S L)
    (hns : ¬ IsSylowTwoOf (barM M (S ⊓ L)) (barM M L)) {q : ℕ} (hq : q.Prime) (hq5 : 5 ≤ q)
    (hperf : ∀ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
      V ≤ barM M (Subgroup.normalizer (S : Set G) ⊓ L) → ⁅V, V⁆ = V → q.Coprime (Nat.card V)) :
    q.Coprime (Nat.card (barM M (Subgroup.normalizer (S : Set G) ⊓ L))) := by
  obtain ⟨hcl, ⟨hJL, T, hT, hNT⟩, hO⟩ := h2
  set Lb := barM M L
  set Jb := barM M (Subgroup.normalizer (S : Set G) ⊓ L)
  have hT₁ := isSylowTwoOf_subgroupOf_top_of_isSylowTwoOf hT
  have hN : Subgroup.normalizer ((T.subgroupOf Lb : Subgroup ↥Lb) : Set ↥Lb) ≤
      Jb.subgroupOf Lb := fun z hz =>
    Subgroup.mem_subgroupOf.mpr (hNT ⟨z.2, coe_mem_normalizer_of_subgroupOf hT.1 hz⟩)
  have hne : Jb.subgroupOf Lb ≠
      Subgroup.normalizer ((T.subgroupOf Lb : Subgroup ↥Lb) : Set ↥Lb) := by
    intro heq
    have hJN : Jb ≤ Subgroup.normalizer (T : Set _) := fun j hj => by
      refine coe_mem_normalizer_of_subgroupOf (x := ⟨j, hJL hj⟩) hT.1 ?_
      rw [← heq]
      exact Subgroup.mem_subgroupOf.mpr hj
    have hTJ : T ≤ Jb := fun t ht => hNT ⟨hT.1 ht, Subgroup.le_normalizer ht⟩
    have hTO : T ≤ barM M (S ⊓ L) := by
      rw [hO]
      exact normal_pGroup_le_pCoreOf 2 T Jb hTJ
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hTJ).mpr hJN) hT.2.1
    refine hns ⟨barM_mono inf_le_right,
      by rw [hO]; exact CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 Jb,
      fun hd => hT.2.2 ?_⟩
    exact hd.trans (Subgroup.relIndex_dvd_of_le_left Lb hTO)
  have hperf' : ∀ U : Subgroup ↥Lb, U ≤ Jb.subgroupOf Lb → ⁅U, U⁆ = U →
      q.Coprime (Nat.card U) := by
    intro U hU hUp
    have h1 := hperf (U.map Lb.subtype) (fun x hx => by
        obtain ⟨u, hu, rfl⟩ := hx
        exact Subgroup.mem_subgroupOf.mp (hU hu))
      (by rw [← Subgroup.map_commutator, hUp])
    rwa [Subgroup.card_map_of_injective Lb.subtype_injective] at h1
  have h := hKP ↥Lb hLc.2.2 hcl (T.subgroupOf Lb) (Jb.subgroupOf Lb) hT₁ hN hne q hq hq5 hperf'
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJL).toEquiv] at h

end Bar

end CFSG.AGLEmbedding
