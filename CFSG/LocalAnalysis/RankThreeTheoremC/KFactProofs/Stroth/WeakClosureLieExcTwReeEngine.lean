module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcTwReeLift
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcTwMove
public import CFSG.RankThree.PartOne.K128.ReeSector

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.RF4 CFSG.RankThree.PartOne.KLR CFSG.RankThree.PartOne.KEXC
  CFSG.RankThree.PartOne.K128
open scoped commutatorElement Matrix

section Group

variable {G : Type} [Group G]

theorem tw_mem_normalizer_sylow_of_comm [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    {T : Subgroup G} (hT : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x) (hPT : (P : Subgroup G) ≤ T) {c : G}
    (hc : c ∈ Subgroup.normalizer (T : Set G)) :
    c ∈ Subgroup.normalizer ((P : Subgroup G) : Set G) := by
  have key : ∀ {c : G}, c ∈ Subgroup.normalizer (T : Set G) →
      ∀ s ∈ (P : Subgroup G), c * s * c⁻¹ ∈ (P : Subgroup G) := by
    intro c hc s hs
    have hzT : c * s * c⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.1 hc s).1 (hPT hs)
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨s, hs⟩
    have hsk : s ^ p ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hzk : (c * s * c⁻¹) ^ p ^ k = 1 := by
      rw [conj_pow, hsk]
      simp
    exact tw_mem_sylow_of_commute P hzk fun t ht => hT t (hPT ht) _ hzT
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key hc x hx, fun hx => ?_⟩
  have h := key (inv_mem hc) _ hx
  simpa [mul_assoc] using h

theorem tw_normalizerMovesLines_of_comm [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    {T : Subgroup G} (hT : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x) (hPT : (P : Subgroup G) ≤ T)
    {c₁ c₂ : G} (h₁ : c₁ ∈ Subgroup.normalizer (T : Set G))
    (h₂ : c₂ ∈ Subgroup.normalizer (T : Set G))
    (hfpf : ∀ x ∈ (P : Subgroup G), x ^ p = 1 → ⁅c₁, c₂⁆ * x * ⁅c₁, c₂⁆⁻¹ = x → x = 1) :
    NormalizerMovesLines p (P : Subgroup G) := by
  intro A hAP hA
  rcases exists_not_normalizes_of_commutator_fpf (E := A) (A := A) le_rfl hA (c₁ := c₁)
    (c₂ := c₂) (fun x hx hxu => hfpf x (hAP hx) (tw_pow_eq_one_of_card_eq_prime hA hx) hxu) with
    h | h
  · exact ⟨c₁, tw_mem_normalizer_sylow_of_comm P hT hPT h₁, h⟩
  · exact ⟨c₂, tw_mem_normalizer_sylow_of_comm P hT hPT h₂, h⟩

end Group

section Torus

variable {τ : Tag} {L : Type} [Field L]

theorem weylTuple_eq_inv_of_neg {u : WeylGroup τ} (hu : ∀ x : Fin τ.rank → ℤ, u⁻¹ • x = -x)
    (b : Fin τ.rank → Lˣ) : weylTuple u b = b⁻¹ := by
  funext i
  have h1 : weylTuple u b i = rootChar b (u⁻¹ • (Pi.single i 1 : Fin τ.rank → ℤ)) := rfl
  rw [h1, hu, ← neg_one_zsmul, rootChar_zsmul, CTTorus.rootChar_single, zpow_neg_one]
  rfl

theorem tuple_eq_one_of_inv {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {b : Fin τ.rank → Lˣ}
    (hb : b = b⁻¹) (hbp : ∀ i, b i ^ p = 1) : b = 1 := by
  funext i
  have h1 : b i = (b i)⁻¹ := congrFun hb i
  have h2 : b i ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 1 [h1]
    exact inv_mul_cancel _
  have h3 : orderOf (b i) ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  have h4 : orderOf (b i) ∣ p := orderOf_dvd_of_pow_eq_one (hbp i)
  rcases (Nat.dvd_prime hp).1 h4 with h | h
  · exact orderOf_eq_one_iff.1 h
  · rw [h] at h3
    exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h3) hp2

end Torus

section Ree

variable {K : Type} [Field K] [Finite K]
  [CharP K ReeTag.F4.prime] {a : ℕ} {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L]
  [CharP L 2]

theorem exists_sylow_moves_lines_ree (D : ReeFrameData K L a) (w : WeylGroup ReeTag.F4.tag)
    (hdet : (1 - (2 ^ a : ℤ) • (reeB * weylMat w⁻¹)).det ≠ 0) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (E : Subgroup (ModGL ReeTag.F4.tag L)) (hET : E ≤ torusGroup ReeTag.F4.tag L)
    (hER : E ≤ twistedFixed D.F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w)) {k : ℕ}
    (hEcard : Nat.card E = p ^ k)
    (hk : (Nat.card (ReeTag.F4.reeGamma K a)).factorization p ≤ k)
    {u₁ u₂ : WeylGroup ReeTag.F4.tag} (h₁ : w * ReeTag.F4.weylPerm u₁ = u₁ * w)
    (h₂ : w * ReeTag.F4.weylPerm u₂ = u₂ * w)
    (hu : ∀ x : Fin ReeTag.F4.tag.rank → ℤ, ⁅u₁, u₂⁆⁻¹ • x = -x) :
    ∃ P : Sylow p (ReeTag.F4.reeGamma K a),
      NormalizerMovesLines p (P : Subgroup (ReeTag.F4.reeGamma K a)) := by
  classical
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  haveI : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  haveI : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  set n := canonicalRep (coxeterSystem ReeTag.F4.tag) L w with hn
  set R := twistedFixed D.F n with hR
  obtain ⟨Ψ, hΨ⟩ := exists_hom_reeGamma D w R.subtype Subtype.val_injective
    (le_of_eq (Subgroup.range_subtype R))
  obtain ⟨y₁, hm₁, hR₁, hA₁⟩ := exists_reeFrob_lift D.isFrob w hdet h₁
  obtain ⟨y₂, hm₂, hR₂, hA₂⟩ := exists_reeFrob_lift D.isFrob w hdet h₂
  let r₁ : R := ⟨y₁, hR₁⟩
  let r₂ : R := ⟨y₂, hR₂⟩
  let T' : Subgroup R := (torusGroup ReeTag.F4.tag L).subgroupOf R
  have hT'comm : ∀ x ∈ T', ∀ y ∈ T', x * y = y * x := fun x hx y hy =>
    Subtype.ext (torusGroup_mul_comm (Subgroup.mem_subgroupOf.1 hx)
      (Subgroup.mem_subgroupOf.1 hy))
  have hconj : ∀ (y : R) (u : WeylGroup ReeTag.F4.tag), TwActsAs (y : ModGL ReeTag.F4.tag L) u →
      ∀ x : R, x ∈ T' → y * x * y⁻¹ ∈ T' := by
    intro y u hy x hx
    obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (Subgroup.mem_subgroupOf.1 hx)
    rw [Subgroup.mem_subgroupOf]
    show (y : ModGL ReeTag.F4.tag L) * (x : ModGL ReeTag.F4.tag L) *
      (y : ModGL ReeTag.F4.tag L)⁻¹ ∈ torusGroup ReeTag.F4.tag L
    rw [hb, hy b]
    exact rootDiagUnit_mem_torusGroup _
  let S' : Subgroup R := E.subgroupOf R
  have hS'T : S' ≤ T' := fun x hx =>
    Subgroup.mem_subgroupOf.2 (hET (Subgroup.mem_subgroupOf.1 hx))
  have hS'card : Nat.card S' = p ^ k := by
    rw [← hEcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hER).toEquiv
  let P₀ : Subgroup (ReeTag.F4.reeGamma K a) := S'.map Ψ
  have hP₀card : Nat.card P₀ = p ^ k := by
    rw [Subgroup.card_map_of_injective hΨ, hS'card]
  have hk' : k ≤ (Nat.card (ReeTag.F4.reeGamma K a)).factorization p := by
    have hdvd : p ^ k ∣ Nat.card (ReeTag.F4.reeGamma K a) := by
      rw [← hP₀card]
      exact Subgroup.card_subgroup_dvd_card P₀
    exact (Nat.Prime.pow_dvd_iff_le_factorization Fact.out Nat.card_pos.ne').1 hdvd
  have hP₀syl : Nat.card P₀ = p ^ (Nat.card (ReeTag.F4.reeGamma K a)).factorization p := by
    rw [hP₀card]
    congr 1
    omega
  let P : Sylow p (ReeTag.F4.reeGamma K a) := Sylow.ofCard P₀ hP₀syl
  have hPeq : (P : Subgroup (ReeTag.F4.reeGamma K a)) = P₀ := Sylow.coe_ofCard P₀ hP₀syl
  refine ⟨P, ?_⟩
  let T : Subgroup (ReeTag.F4.reeGamma K a) := T'.map Ψ
  have hTcomm : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hT'comm x hx y hy]
  have hPT : (P : Subgroup (ReeTag.F4.reeGamma K a)) ≤ T := by
    rw [hPeq]
    exact Subgroup.map_mono hS'T
  have hnorm : ∀ (y : R) (u : WeylGroup ReeTag.F4.tag),
      TwActsAs (y : ModGL ReeTag.F4.tag L) u → Ψ y ∈ Subgroup.normalizer (T : Set _) := by
    intro y u hy
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨y * x * y⁻¹, hconj y u hy x hx, by simp [map_mul, map_inv]⟩
    · rintro ⟨x, hx, hxz⟩
      refine ⟨y⁻¹ * x * y, ?_, ?_⟩
      · have := hconj y⁻¹ u⁻¹ (by simpa using hy.inv) x hx
        simpa using this
      · have : Ψ (y⁻¹ * x * y) = (Ψ y)⁻¹ * Ψ x * Ψ y := by simp [map_mul, map_inv]
        rw [this, hxz]
        group
  refine tw_normalizerMovesLines_of_comm P hTcomm hPT (hnorm r₁ u₁ hA₁) (hnorm r₂ u₂ hA₂) ?_
  intro x hx hxp hfix
  rw [hPeq] at hx
  obtain ⟨x', hx'S, rfl⟩ := hx
  have hcomm : ⁅Ψ r₁, Ψ r₂⁆ = Ψ ⁅r₁, r₂⁆ := by
    simp [commutatorElement_def, map_mul, map_inv]
  rw [hcomm] at hfix
  have hfix' : ⁅r₁, r₂⁆ * x' * ⁅r₁, r₂⁆⁻¹ = x' :=
    hΨ (by simpa [map_mul, map_inv] using hfix)
  have hxp' : x' ^ p = 1 := hΨ (by rw [map_pow, hxp, map_one])
  have hx'T : (x' : ModGL ReeTag.F4.tag L) ∈ torusGroup ReeTag.F4.tag L :=
    hET (Subgroup.mem_subgroupOf.1 hx'S)
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hx'T
  have hA : TwActsAs (⁅y₁, y₂⁆ : ModGL ReeTag.F4.tag L) ⁅u₁, u₂⁆ := hA₁.commutator hA₂
  have h1 : ⁅y₁, y₂⁆ * (x' : ModGL ReeTag.F4.tag L) * ⁅y₁, y₂⁆⁻¹ = (x' : ModGL ReeTag.F4.tag L) := by
    have := congrArg Subtype.val hfix'
    simpa [commutatorElement_def] using this
  rw [hb, hA b] at h1
  have h2 : weylTuple ⁅u₁, u₂⁆ b = b := CFSG.LieType.Chevalley.rootDiagUnit_injective h1
  rw [weylTuple_eq_inv_of_neg hu b] at h2
  have hbp : ∀ i, b i ^ p = 1 := by
    have hpow : rootDiagUnit ReeTag.F4.tag (b ^ p) = rootDiagUnit ReeTag.F4.tag b ^ p :=
      map_pow (rootDiagUnitHom ReeTag.F4.tag L) b p
    have h3 : (x' : ModGL ReeTag.F4.tag L) ^ p = 1 := by
      have := congrArg Subtype.val hxp'
      simpa using this
    rw [hb, ← hpow, ← rootDiagUnit_one (K := L)] at h3
    have := CFSG.LieType.Chevalley.rootDiagUnit_injective h3
    intro i
    exact congrFun this i
  have hb1 : b = 1 := tuple_eq_one_of_inv Fact.out hp2 h2.symm hbp
  have : x' = 1 := by
    apply Subtype.ext
    rw [hb, hb1, rootDiagUnit_one]
    rfl
  rw [this, map_one]

end Ree

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross
