module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointCase2Comp
import CFSG.LocalAnalysis.RankFourTheoremC.PPointCase2Y
import CFSG.LocalAnalysis.RankFourTheoremC.PPointAutRank
import CFSG.LocalAnalysis.RankFourTheoremC.PPointEndgameAux
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Quot
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Reduced3

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankFourTheoremC Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

structure Case2DataTwo (Y : Type) [Group Y] [Finite Y] (x : Y) (Z : Subgroup Y) (S : Set Y)
    (O : Subgroup Y) : Prop where
  base : Case2Hyp Y x
  isElemAbelian : IsElemAbelian 3 Z
  card_eq : ∃ n : ℕ, 2 ≤ n ∧ Nat.card Z = 3 ^ n
  le_centralizer : Z ≤ centralizer ({x} : Set Y)
  centralizes : ∀ s ∈ S, s * x * s⁻¹ = x
  normalizes : ∀ s ∈ S, ∀ z ∈ Z, s * z * s⁻¹ ∈ Z
  irreducible : ∀ D : Subgroup Y, D ≤ Z → (∀ s ∈ S, ∀ d ∈ D, s * d * s⁻¹ ∈ D) → D = ⊥ ∨ D = Z
  coprime : ¬ 3 ∣ Nat.card O
  normalizes_O : centralizer ({x} : Set Y) ≤ normalizer (O : Set Y)
  normalizes_ZO : centralizer ({x} : Set Y) ≤ normalizer ((Z ⊔ O : Subgroup Y) : Set Y)

theorem Case2DataTwo.le_pCore {Y : Type} [Group Y] [Finite Y] {x : Y} {Z : Subgroup Y}
    {S : Set Y} {O : Subgroup Y} (hd : Case2DataTwo Y x Z S O) (hInn : KFactInnerAction)
    (hWC : KFactWeakClosure) (hK3 : KFactOutCyclic) : Z ≤ CFSG.pCore 3 Y := by
  by_contra hZ
  have hZcomm : IsMulCommutative Z := hd.isElemAbelian.1
  have hZab : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a := fun a ha b hb => setLike_mul_comm ha hb
  have hZ3 : IsPGroup 3 Z := elementary_isPGroup 3 Z hd.isElemAbelian
  have hZpow : ∀ a : Z, a ^ 3 = 1 := fun a =>
    Subtype.ext (by simpa using hd.isElemAbelian.2 a a.2)
  obtain ⟨K, hK, hZK⟩ := hd.base.exists_component_not_centralized hZ3 hZ
  have hZN : ∀ z ∈ Z, z ∈ normalizer (K : Set Y) := fun z hz =>
    hd.base.mem_normalizer_of_pow_three hK (hd.isElemAbelian.2 z hz)
  have hxN : x ∈ normalizer (K : Set Y) :=
    hd.base.mem_normalizer_of_pow_three hK hd.base.pow_eq_one
  have hxC : x ∉ centralizer (K : Set Y) := by
    intro hxC
    refine hZK (hd.base.centralizes_of_le_centralizer hZab hZN hd.coprime hd.le_centralizer
      hd.normalizes_O hd.normalizes_ZO hK fun k hk => ?_)
    exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hxC k hk)
  obtain ⟨Q, hxQ, P, hP, hP1, r, hrQK, hc, hro⟩ := hd.base.exists_decomp hInn hK hxN hxC
  have hPc : IsCyclic (P : Subgroup K) := hd.base.isCyclic_of_decomp hWC hK hxQ hP hrQK hc hro
  have hxK : x ∈ K := hd.base.mem_of_decomp hK hxQ hP hP1 hPc hrQK hc hro
  have hrank : CFSG.Open.pRank 3 (⊤ : Subgroup K) ≤ 1 := by
    rw [← CFSG.PreuniquenessRankFour.Helpers.pRank_sylow_eq_globalRank 3 Nat.prime_three P]
    exact CFSG.LocalAnalysis.RankFourTheoremC.pRank_le_one_of_isCyclic Nat.prime_three hPc
  have hSN : ∀ s ∈ S, s ∈ normalizer (K : Set Y) := fun s hs =>
    hd.base.mem_normalizer_of_mem hK hxK (hd.centralizes s hs)
  have hKZ : center K = ⊥ := hd.base.center_eq_bot hK
  obtain ⟨hsimple, hnonab⟩ := isSimpleGroup_of_isComponentOf_of_center_eq_bot hK hKZ
  have hcat := hd.base.catalog.simple_subgroup K hsimple hnonab
  have hout : CFSG.Open.pRank 3 (⊤ : Subgroup (Outer K)) ≤ 1 :=
    hK3 K hsimple hnonab hcat 3 Nat.prime_three (by norm_num) P hPc
  obtain ⟨n, hn2, hcardZ⟩ := hd.card_eq
  have hinv : ∀ s ∈ S, ∀ d ∈ Z ⊓ centralizer (K : Set Y),
      s * d * s⁻¹ ∈ Z ⊓ centralizer (K : Set Y) := by
    intro s hs d hdd
    refine ⟨hd.normalizes s hs d hdd.1, mem_centralizer_iff.mpr fun k hk => ?_⟩
    have hk' : s⁻¹ * k * s ∈ K := by
      have := (mem_normalizer_iff.mp (Subgroup.inv_mem _ (hSN s hs)) k).mp hk
      simpa using this
    have h1 := mem_centralizer_iff.mp hdd.2 _ hk'
    calc k * (s * d * s⁻¹) = s * ((s⁻¹ * k * s) * d) * s⁻¹ := by group
      _ = s * (d * (s⁻¹ * k * s)) * s⁻¹ := by rw [h1]
      _ = s * d * s⁻¹ * k := by group
  have hCZ : Z ⊓ centralizer (K : Set Y) = ⊥ := by
    rcases hd.irreducible (Z ⊓ centralizer (K : Set Y)) inf_le_left hinv with hD | hD
    · exact hD
    · exact absurd (inf_eq_left.mp hD) hZK
  obtain ⟨α, hα⟩ : ∃ α : Z →* MulAut K, ∀ (z : Z) (k : K),
      ((α z k : K) : Y) = (z : Y) * (k : Y) * (z : Y)⁻¹ :=
    ⟨K.normalizerMonoidHom.comp (Subgroup.inclusion fun z hz => hZN z hz), fun z k => rfl⟩
  have hinj : Function.Injective α := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro u hu
    have hu' : (u : Y) ∈ Z ⊓ centralizer (K : Set Y) := ⟨u.2, mem_centralizer_iff.mpr fun k hk => by
      have h1 : (((α u) ⟨k, hk⟩ : K) : Y) = (((1 : MulAut K) ⟨k, hk⟩ : K) : Y) :=
        congrArg (fun φ : MulAut K => ((φ ⟨k, hk⟩ : K) : Y)) (MonoidHom.mem_ker.mp hu)
      rw [hα] at h1
      change (u : Y) * k * (u : Y)⁻¹ = k at h1
      calc k * (u : Y) = (u : Y) * k * (u : Y)⁻¹ * (u : Y) := by rw [h1]
        _ = (u : Y) * k := by group⟩
    rw [hCZ, mem_bot] at hu'
    exact mem_bot.mpr (Subtype.ext hu')
  obtain ⟨β, hβ⟩ : ∃ β : Z →* Outer K, ∀ z, β z = QuotientGroup.mk' (inner K) (α z) :=
    ⟨(QuotientGroup.mk' (inner K)).comp α, fun z => rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : Subgroup Y, D = β.ker.map Z.subtype := ⟨_, rfl⟩
  have hmemD : ∀ z : Z, (z : Y) ∈ D ↔ β z = 1 := by
    intro z
    rw [hD, Subgroup.mem_map]
    constructor
    · rintro ⟨u, hu, hzu⟩
      have : u = z := Subtype.ext hzu
      rw [← this]
      exact MonoidHom.mem_ker.mp hu
    · intro h
      exact ⟨z, MonoidHom.mem_ker.mpr h, rfl⟩
  have hDZ : D ≤ Z := by
    rw [hD]
    exact Subgroup.map_subtype_le _
  have hDinv : ∀ s ∈ S, ∀ d ∈ D, s * d * s⁻¹ ∈ D := by
    intro s hs d hdD
    have hdZ : d ∈ Z := hDZ hdD
    obtain ⟨u, hu⟩ : ∃ u : Z, (u : Y) = d := ⟨⟨d, hdZ⟩, rfl⟩
    obtain ⟨u', hu'⟩ : ∃ u' : Z, (u' : Y) = s * d * s⁻¹ :=
      ⟨⟨s * d * s⁻¹, hd.normalizes s hs d hdZ⟩, rfl⟩
    obtain ⟨σ, hσ⟩ : ∃ σ : MulAut K, ∀ k : K, ((σ k : K) : Y) = s * (k : Y) * s⁻¹ :=
      ⟨K.normalizerMonoidHom ⟨s, hSN s hs⟩, fun k => rfl⟩
    have hβu : β u = 1 := (hmemD u).mp (by rw [hu]; exact hdD)
    have hcomm : α u' * σ = σ * α u := by
      refine MulEquiv.ext fun k => Subtype.ext ?_
      calc (((α u' * σ) k : K) : Y) = ((α u' (σ k) : K) : Y) := rfl
        _ = (u' : Y) * ((σ k : K) : Y) * (u' : Y)⁻¹ := hα u' (σ k)
        _ = s * ((u : Y) * k * (u : Y)⁻¹) * s⁻¹ := by rw [hu', hσ, hu]; group
        _ = s * ((α u k : K) : Y) * s⁻¹ := by rw [hα]
        _ = ((σ (α u k) : K) : Y) := (hσ _).symm
        _ = (((σ * α u) k : K) : Y) := rfl
    have hβu' : β u' = 1 := by
      have e1 : QuotientGroup.mk' (inner K) (α u) = 1 := (hβ u).symm.trans hβu
      have e2 : QuotientGroup.mk' (inner K) (α u') * QuotientGroup.mk' (inner K) σ =
          1 * QuotientGroup.mk' (inner K) σ := by
        rw [← map_mul, hcomm, map_mul, e1, mul_one, one_mul]
      rw [hβ]
      exact mul_right_cancel e2
    rw [← hu']
    exact (hmemD u').mpr hβu'
  have hDne : D ≠ ⊥ := by
    intro hbot
    have hβinj : Function.Injective β := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro u hu
      have hD1 : (u : Y) ∈ D := (hmemD u).mpr (MonoidHom.mem_ker.mp hu)
      rw [hbot, mem_bot] at hD1
      exact mem_bot.mpr (Subtype.ext hD1)
    have hle : n ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (Outer K)) :=
      CFSG.SectionRank.le_pRank_of_injective (p := 3) (by norm_num) (fun a b => mul_comm' a b)
        hZpow hcardZ β hβinj le_top
    omega
  have hDZeq : D = Z := (hd.irreducible D hDZ hDinv).resolve_left hDne
  have hβ1 : ∀ z : Z, β z = 1 := fun z => (hmemD z).mp (by rw [hDZeq]; exact z.2)
  have hinner : ∀ z : Z, α z ∈ inner K := fun z =>
    (QuotientGroup.eq_one_iff _).mp ((hβ z).symm.trans (hβ1 z))
  have hle : α.range ≤ inner K := by
    rintro _ ⟨z, rfl⟩
    exact hinner z
  have hge : n ≤ CFSG.Open.pRank 3 (inner K) :=
    CFSG.SectionRank.le_pRank_of_injective (p := 3) (by norm_num) (fun a b => mul_comm' a b)
      hZpow hcardZ α hinj hle
  have hle2 : CFSG.Open.pRank 3 (inner K) ≤ CFSG.Open.pRank 3 (⊤ : Subgroup K) := by
    have e1 : inner K = (⊤ : Subgroup K).map (MulAut.conj : K →* MulAut K) :=
      MonoidHom.range_eq_map _
    rw [e1, CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective 3 Nat.prime_three _
      (CFSG.LocalAnalysis.RankFourTheoremC.conj_injective_of_center_eq_bot hKZ)]
  omega

theorem case2Hyp_quotient_of_isKProper {G : Type} [Group G] [Finite G]
    (hK : CFSG.Open.IsKProper G) {P : Sylow 3 G} (hPab : IsMulCommutative (P : Subgroup G))
    {M : Subgroup G} (hMtop : M ≠ ⊤) {x : G} (hxM : x ∈ M) (hxo : orderOf x = 3)
    (hwc : ∀ g : G, (zpowers x).map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup G) →
      (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers x) :
    Case2Hyp (M ⧸ primeComplementCore (G := M) 3)
      (QuotientGroup.mk' (primeComplementCore (G := M) 3) ⟨x, hxM⟩) := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  set O : Subgroup M := primeComplementCore (G := M) 3
  have hxo' : orderOf (⟨x, hxM⟩ : M) = 3 := by
    rw [Subgroup.orderOf_mk]
    exact hxo
  have hxo'' : orderOf (QuotientGroup.mk' O ⟨x, hxM⟩) = 3 :=
    CFSG.AGLEmbedding.orderOf_mk_of_coprime hp O (primeComplementCore_coprime 3) hxo'
  have hab : ∀ S : Sylow 3 (M ⧸ O), IsMulCommutative (S : Subgroup (M ⧸ O)) :=
    isMulCommutative_sylow_quotient (N := M) fun _ hQ =>
      CFSG.LocalAnalysis.RankFourTheoremC.isMulCommutative_of_isPGroup hPab hQ
  exact
    { core_eq_bot := primeComplementCore_quotient_eq_bot 3
      catalog := (CFSG.AGLEmbedding.catalogSimpleSections_of_isKProper hK M hMtop).quotient O
      abelian := hab
      ne_one := fun h => by
        rw [h, orderOf_one] at hxo''
        omega
      pow_eq_one := by simpa only [hxo''] using pow_orderOf_eq_one (QuotientGroup.mk' O ⟨x, hxM⟩)
      weakClosed := fun Q hxQ g hg => weaklyClosed_map_mk hxo' hab
        (fun Q' hxQ' g' hg' =>
          CFSG.LocalAnalysis.RankFourTheoremC.weakClosed_sylow hwc Q' hxQ' g' hg') Q hxQ g hg }

end CFSG.LocalAnalysis.RankThreeTheoremC
