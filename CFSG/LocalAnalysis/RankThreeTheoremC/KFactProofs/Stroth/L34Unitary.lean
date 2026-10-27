module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34Proved
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.L34Embed
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.L34UnitarySpec
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.L34Exp3
import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCCore
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.Permutable

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup CFSG.ABGLocalTools
open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbeddingD2 CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
open CFSG.RankThree.PartTwo.KFacts.L34
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.PSL3Four

namespace KFactProofs.Stroth.L34Unitary

private theorem isRankThreeL34_iff_index {K : Type} [Group K] :
    IsRankThreeL34 K ↔ ∃ d : TauCeti.ValidLieTypeIndex, IsL34Index d ∧
      Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group) := by
  constructor
  · rintro ⟨q, hq2, hqe, hv, he⟩
    exact ⟨⟨.A 2 q, hv⟩, ⟨q, hq2, hqe, rfl⟩, he⟩
  · rintro ⟨⟨d, hv⟩, ⟨q, hq2, hqe, hd⟩, he⟩
    simp only at hd
    subst hd
    exact ⟨q, hq2, hqe, hv, he⟩

private theorem part_one_aux {X : Type} [Group X] [Finite X] {K : Subgroup X} [K.Normal]
    (hC : centralizer (K : Set X) = ⊥) (hL : IsRankThreeL34 ↥K) {T : Subgroup X}
    (hTc : Nat.card T = 9) (hTK : T ≤ K) {O : Subgroup X} (hcop : Nat.Coprime 3 (Nat.card O))
    (hTO : T ≤ normalizer (O : Set X)) :
    Nat.card O ≤ 2 ∧ ∀ β ∈ O, β * β = 1 ∧ ∀ t ∈ T, β * t = t * β := by
  obtain ⟨d, hd, ⟨e⟩⟩ := isRankThreeL34_iff_index.1 hL
  obtain ⟨F, _, hF, ⟨ψ⟩⟩ := exists_equiv_projectiveSL_of_l34Index hd e
  let θ : X →* MulAut ↥K := MulAut.conjNormal
  have hθ : Function.Injective θ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hmem : g ∈ Subgroup.centralizer (K : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have h3 : ((MulAut.conjNormal g : MulAut ↥K) ⟨k, hk⟩ : X) = g * k * g⁻¹ :=
        MulAut.conjNormal_apply g ⟨k, hk⟩
      have h2 : g * k * g⁻¹ = k := by
        rw [← h3]
        have := congrArg (fun α : MulAut ↥K => ((α ⟨k, hk⟩ : ↥K) : X)) hg
        exact this
      calc k * g = g * k * g⁻¹ * g := by rw [h2]
        _ = g * k := by group
    rw [hC] at hmem
    exact hmem
  let Ψ : X →* MulAut (projectiveSL 3 F) := (MulAut.congr ψ).toMonoidHom.comp θ
  have hΨ : Function.Injective Ψ := (MulAut.congr ψ).injective.comp hθ
  have hΨapp : ∀ (g : X) (k : ↥K), Ψ g (ψ k) = ψ (MulAut.conjNormal g k) := by
    intro g k
    show (MulAut.congr ψ (MulAut.conjNormal g)) (ψ k) = _
    rw [MulAut.congr_apply]
    simp
  let X' : Subgroup (MulAut (projectiveSL 3 F)) := O.map Ψ
  have hX'card : Nat.card X' = Nat.card O := Subgroup.card_map_of_injective hΨ
  have h3X' : ¬ 3 ∣ Nat.card X' := by
    rw [hX'card]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hcop
  let E : Subgroup (projectiveSL 3 F) := (T.subgroupOf K).map ψ.toMonoidHom
  have hEc : Nat.card E = 9 := by
    rw [Subgroup.card_map_of_injective ψ.injective, ← hTc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTK).toEquiv
  have hEX : ∀ e ∈ E, MulAut.conj e ∈ normalizer (X' : Set (MulAut (projectiveSL 3 F))) := by
    rintro _ ⟨k, hk, rfl⟩
    have hkT : (k : X) ∈ T := hk
    have h1 : (k : X) ∈ normalizer (O : Set X) := hTO hkT
    have h2 : Ψ (k : X) ∈ normalizer (X' : Set (MulAut (projectiveSL 3 F))) :=
      Subgroup.le_normalizer_map Ψ (Subgroup.mem_map_of_mem Ψ h1)
    have h3 : Ψ (k : X) = MulAut.conj (ψ k) := by
      show MulAut.congr ψ (MulAut.conjNormal (k : X)) = _
      rw [MulAut.conjNormal_val]
      ext y
      simp [MulAut.congr_apply, MulAut.conj_apply]
    rw [h3] at h2
    exact h2
  have hmem : ∀ β ∈ O, Ψ β ∈ X' := fun β hβ => Subgroup.mem_map_of_mem Ψ hβ
  rcases eq_bot_or_eq_zpowers_graphField hF hEc h3X' hEX with hbot | ⟨τ, hτ, hτ1, hτ2, -, hτE⟩
  ·
    have hOb : O = ⊥ := by
      have : O.map Ψ = ⊥ := hbot
      rwa [Subgroup.map_eq_bot_iff_of_injective _ hΨ] at this
    refine ⟨by rw [hOb, Subgroup.card_bot]; norm_num, fun β hβ => ?_⟩
    rw [hOb, Subgroup.mem_bot] at hβ
    subst hβ
    exact ⟨by simp, fun t _ => by simp⟩
  · have hord : orderOf τ = 2 := orderOf_eq_prime (by rw [sq]; exact hτ2) hτ1
    have hz : ∀ z ∈ X', z = 1 ∨ z = τ := by
      intro z hz
      have hz' : z ∈ Subgroup.zpowers τ := by rw [← hτ]; exact hz
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz'
      rw [← zpow_mod_orderOf, hord]
      rcases Int.emod_two_eq_zero_or_one n with h | h
      · left
        simp [h]
      · right
        simp [h]
    refine ⟨?_, fun β hβ => ?_⟩
    · rw [← hX'card, hτ, Nat.card_zpowers, hord]
    · rcases hz _ (hmem β hβ) with h1 | h1
      · have hβ1 : β = 1 := hΨ (by rw [h1, map_one])
        subst hβ1
        exact ⟨by simp, fun t _ => by simp⟩
      · refine ⟨hΨ (by rw [map_mul, h1, hτ2, map_one]), fun t ht => ?_⟩
        have hψt : ψ ⟨t, hTK ht⟩ ∈ E := ⟨⟨t, hTK ht⟩, ht, rfl⟩
        have h2 := hτE _ hψt
        rw [← h1, hΨapp] at h2
        have h4 : (MulAut.conjNormal β : MulAut ↥K) ⟨t, hTK ht⟩ = ⟨t, hTK ht⟩ := ψ.injective h2
        have h5 : β * t * β⁻¹ = t := by
          have := congrArg (fun z : ↥K => (z : X)) h4
          simpa [MulAut.conjNormal_apply] using this
        calc β * t = β * t * β⁻¹ * β := by group
          _ = t * β := by rw [h5]

private theorem part_one {X : Type} [Group X] [Finite X] {K : Subgroup X} [K.Normal]
    (hC : centralizer (K : Set X) = ⊥) (hL : IsRankThreeL34 ↥K) {T : Subgroup X}
    (hT : IsElemAbelian 3 T) (hTc : Nat.card T = 3 ^ 2) (hTK : T ≤ K) :
    Nat.card (rankThreePrimeCore 3 (rankThreeGamma 1 3 T)) ≤ 2 ∧
      ∀ β ∈ rankThreePrimeCore 3 (rankThreeGamma 1 3 T), β * β = 1 ∧ ∀ t ∈ T, β * t = t * β := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hrank : 1 ≤ CFSG.Open.pRank 3 T :=
    (show 1 ≤ 2 by norm_num).trans (CFSG.SectionRank.le_pRank (by norm_num) le_rfl hT hTc)
  have hNΓ : normalizer (T : Set X) ≤ rankThreeGamma 1 3 T := le_sSup ⟨T, le_rfl, hrank, rfl⟩
  obtain ⟨-, hΓO, hcop⟩ :=
    CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec 3 (rankThreeGamma 1 3 T)
  exact part_one_aux hC hL (by rw [hTc]; norm_num) hTK hcop
    ((Subgroup.le_normalizer.trans hNΓ).trans hΓO)

private theorem part_two
    {X : Type} [Group X] [Finite X] {K : Subgroup X} [K.Normal]
    (hC : centralizer (K : Set X) = ⊥) (hL : IsRankThreeL34 ↥K) {T : Subgroup X}
    (hTc : Nat.card T = 9) (hTK : T ≤ K) {β : X} (hβ1 : β ≠ 1) (hββ : β * β = 1)
    (hβT : ∀ t ∈ T, β * t = t * β) {S₀ : Subgroup X} (hS₀K : S₀ ≤ K) (hS₀ : IsSylowOf 2 S₀ K)
    {u : X} (huT : u ∈ T) (hu3 : orderOf u = 3) (huS₀ : u ∈ normalizer (S₀ : Set X))
    {D : Subgroup X} (hDK : D ≤ K) (hND : normalizer (S₀ : Set X) ⊓ K ≤ D)
    (hβD : β ∈ normalizer (D : Set X)) : D = K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ε, ψ, hψinj, hψR, hψK⟩ := KFactProofs.Stroth.L34Embed.exists_embedding_R hC hL
  obtain ⟨u₀, E₀, hu₀E, hE₀S, hE₀c, hu₀1, hspec⟩ := l34Unitary_spec
  have hKcard : Nat.card K = 20160 := by
    rw [Nat.card_congr ε.toEquiv]
    exact card_S
  have hfac3 : (Nat.card K).factorization 3 = 2 := by
    rw [hKcard, Nat.factorization_def _ Nat.prime_three,
      show (20160 : ℕ) = 3 ^ 2 * 2240 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by norm_num)]
  have hfac2 : (Nat.card K).factorization 2 = 6 := by
    rw [hKcard, Nat.factorization_def _ Nat.prime_two,
      show (20160 : ℕ) = 2 ^ 6 * 315 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by norm_num)]
  let ι : ↥K →* Equiv.Perm (Fin 42) := S.subtype.comp ε.toMonoidHom
  have hιinj : Function.Injective ι := Subtype.val_injective.comp ε.injective
  have hιψ : ∀ k : ↥K, ψ (k : X) = ι k := hψK
  have hιS : ∀ k : ↥K, ι k ∈ S := fun k => (ε k).2
  have hιε : ∀ x (hx : x ∈ S), ι (ε.symm ⟨x, hx⟩) = x := by
    intro x hx
    simp [ι]
  let E' : Subgroup ↥K := E₀.comap ι
  have hE'map : E'.map ι = E₀ := by
    apply le_antisymm (Subgroup.map_comap_le _ _)
    intro x hx
    refine ⟨ε.symm ⟨x, hE₀S hx⟩, ?_, hιε x (hE₀S hx)⟩
    show ι (ε.symm ⟨x, hE₀S hx⟩) ∈ E₀
    rw [hιε x (hE₀S hx)]
    exact hx
  have hE'c : Nat.card E' = 9 := by
    rw [← Subgroup.card_map_of_injective hιinj, hE'map, hE₀c]
  let TK : Subgroup ↥K := T.subgroupOf K
  have hTKc : Nat.card TK = 9 := by
    rw [← hTc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTK).toEquiv
  have hSylTK : IsSylowOf 3 TK ⊤ :=
    isSylowOf_of_card le_top (by rw [Subgroup.card_top, hfac3, hTKc]; norm_num)
  have hSylE' : IsSylowOf 3 E' ⊤ :=
    isSylowOf_of_card le_top (by rw [Subgroup.card_top, hfac3, hE'c]; norm_num)
  obtain ⟨s, -, hs⟩ := hSylTK.exists_mem_conj hSylE'
  let uK : ↥K := ⟨u, hTK huT⟩
  have huK : uK ∈ TK := huT
  have huK1 : uK ≠ 1 := by
    intro h
    have : u = 1 := congrArg Subtype.val h
    rw [this, orderOf_one] at hu3
    omega
  let u'' : ↥K := ε.symm ⟨u₀, hE₀S hu₀E⟩
  have hu''ι : ι u'' = u₀ := hιε u₀ (hE₀S hu₀E)
  have hu''E : u'' ∈ E' := by
    show ι u'' ∈ E₀
    rw [hu''ι]
    exact hu₀E
  have hu''1 : u'' ≠ 1 := by
    intro h
    rw [h, map_one] at hu''ι
    exact hu₀1 hu''ι.symm
  have hsuE : s * uK * s⁻¹ ∈ E' := by
    refine (hs _).2 ?_
    rw [show s⁻¹ * (s * uK * s⁻¹) * s = uK by group]
    exact huK
  have hsu1 : s * uK * s⁻¹ ≠ 1 := by
    intro h
    apply huK1
    calc uK = s⁻¹ * (s * uK * s⁻¹) * s := by group
      _ = 1 := by rw [h]; group
  have hE'Sylow : Nat.card E' = 3 ^ (Nat.card ↥K).factorization 3 := by
    rw [hE'c, hfac3]
    norm_num
  obtain ⟨n, hn, hnu⟩ := kFactL34SylowTransitive ↥K hL (Sylow.ofCard E' hE'Sylow)
    (s * uK * s⁻¹) u'' hsuE hu''E hsu1 hu''1
  have hnE : ∀ x : ↥K, x ∈ E' ↔ n * x * n⁻¹ ∈ E' := Subgroup.mem_normalizer_iff.1 hn
  set c : ↥K := n * s with hc
  have hcu : c * uK * c⁻¹ = u'' := by
    rw [hc]
    calc n * s * uK * (n * s)⁻¹ = n * (s * uK * s⁻¹) * n⁻¹ := by group
      _ = u'' := hnu
  have hconjK : ∀ y : ↥K, (c : X) * (y : X) * (c : X)⁻¹ = ((c * y * c⁻¹ : ↥K) : X) := by
    intro y
    simp
  let φ : X →* Equiv.Perm (Fin 42) := ψ.comp (MulAut.conj (c : X)).toMonoidHom
  have hφ : ∀ x : X, φ x = ψ ((c : X) * x * (c : X)⁻¹) := fun x => rfl
  have hφinj : Function.Injective φ := hψinj.comp (MulAut.conj (c : X)).injective
  have hφK : ∀ k : ↥K, φ (k : X) ∈ S := by
    intro k
    rw [hφ, hconjK, hιψ]
    exact hιS _
  have hφu : φ u = u₀ := by
    rw [hφ]
    have : (c : X) * u * (c : X)⁻¹ = ((c * uK * c⁻¹ : ↥K) : X) := hconjK uK
    rw [this, hcu, hιψ, hu''ι]
  have hφT : ∀ e ∈ E₀, ∃ t ∈ T, φ t = e := by
    intro e he
    let e' : ↥K := ε.symm ⟨e, hE₀S he⟩
    have he'ι : ι e' = e := hιε e (hE₀S he)
    have he'E : e' ∈ E' := by
      show ι e' ∈ E₀
      rw [he'ι]
      exact he
    have he'' : n⁻¹ * e' * n ∈ E' := by
      rw [hnE, show n * (n⁻¹ * e' * n) * n⁻¹ = e' by group]
      exact he'E
    have ht' : s⁻¹ * (n⁻¹ * e' * n) * s ∈ TK := (hs _).1 he''
    refine ⟨((s⁻¹ * (n⁻¹ * e' * n) * s : ↥K) : X), ht', ?_⟩
    rw [hφ, hconjK, show c * (s⁻¹ * (n⁻¹ * e' * n) * s) * c⁻¹ = e' by rw [hc]; group, hιψ, he'ι]
  have hφcomm : ∀ e ∈ E₀, φ β * e = e * φ β := by
    intro e he
    obtain ⟨t, ht, rfl⟩ := hφT e he
    rw [← map_mul, ← map_mul, hβT t ht]
  have hφβ1 : φ β ≠ 1 := fun h => hβ1 (hφinj (by rw [h, map_one]))
  have hφββ : φ β * φ β = 1 := by rw [← map_mul, hββ, map_one]
  have hS₀c : Nat.card S₀ = 64 := by
    rw [hS₀.card_eq, hfac2]
    norm_num
  have hVS : S₀.map φ ≤ S := by
    rintro _ ⟨x, hx, rfl⟩
    exact hφK ⟨x, hS₀K hx⟩
  have hVc : Nat.card (S₀.map φ) = 64 := by
    rw [Subgroup.card_map_of_injective hφinj, hS₀c]
  have hVu : ∀ v ∈ S₀.map φ, u₀ * v * u₀⁻¹ ∈ S₀.map φ := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨u * x * u⁻¹, (Subgroup.mem_normalizer_iff.1 huS₀ x).1 hx, ?_⟩
    rw [map_mul, map_mul, map_inv, hφu]
  have hDS : D.map φ ≤ S := by
    rintro _ ⟨x, hx, rfl⟩
    exact hφK ⟨x, hDK hx⟩
  have hu₀D : u₀ ∈ D.map φ :=
    ⟨u, hND (Subgroup.mem_inf.2 ⟨huS₀, hTK huT⟩), hφu⟩
  have hVD : S₀.map φ ≤ D.map φ := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, hND (Subgroup.mem_inf.2 ⟨Subgroup.le_normalizer hx, hS₀K hx⟩), rfl⟩
  have hβD' : ∀ x ∈ D.map φ, φ β * x * (φ β)⁻¹ ∈ D.map φ := by
    rintro _ ⟨d, hd, rfl⟩
    refine ⟨β * d * β⁻¹, (Subgroup.mem_normalizer_iff.1 hβD d).1 hd, ?_⟩
    rw [map_mul, map_mul, map_inv]
  have hDeq : D.map φ = S :=
    hspec (φ β) (hψR _) hφβ1 hφββ hφcomm _ _ hVS hVc hVu hDS hu₀D hVD hβD'
  refine Subgroup.eq_of_le_of_card_ge hDK ?_
  rw [hKcard, ← card_S, ← hDeq]
  exact (Subgroup.card_map_of_injective hφinj).le

end KFactProofs.Stroth.L34Unitary

open KFactProofs.Stroth.L34Unitary in
theorem kFactL34Unitary :
    KFactL34Unitary := by
  intro X _ _ K hKn hC hL T hT hTc hTK
  haveI := hKn
  obtain ⟨hcard, hβ⟩ := part_one hC hL hT hTc hTK
  refine ⟨hcard, fun β hβO => ⟨(hβ β hβO).2, fun hβ1 S₀ hSK hS u huT hu3 huS D hDK hND hβD => ?_⟩⟩
  exact part_two hC hL (by rw [hTc]; norm_num) hTK hβ1 (hβ β hβO).1 (hβ β hβO).2 hSK hS huT hu3
    huS hDK hND hβD

end CFSG.LocalAnalysis.RankThreeTheoremC
