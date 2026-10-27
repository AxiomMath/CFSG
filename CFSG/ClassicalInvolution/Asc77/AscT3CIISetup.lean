module

public import CFSG.ClassicalInvolution.Asc77.AscT3CIIX
public import CFSG.ClassicalInvolution.Asc77.AscT3CIIHexStmt
public import CFSG.ClassicalInvolution.AschTight.HypOmegaGenMod
public import CFSG.ClassicalInvolution.AschTight.Sec7L713F
public import CFSG.ClassicalInvolution.AschTight.Sec6Gen64Ex

public section

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

section Data

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem exists_hexagon_data (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {K J : Subgroup G} {z j : G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hz : IsUniqueInvolution K z)
    (hj : IsUniqueInvolution J j) (hstar : J ∈ omegaStarNbr Ω K) (hnot : J ∉ omegaNbr Ω K)
    (hA : ∀ g ∈ pairNormalizers K J z j, conjSub g K ≠ J) :
    ∃ (v : G) (K' : Subgroup G), Subgroup.zpowers v ∈ USet Ω ∧ Subgroup.zpowers v ≤ J ∧
      IsSylow2In (Subgroup.zpowers v) (J ⊓ Subgroup.centralizer ({z} : Set G)) ∧
      K' ≠ K ∧ twinSet Ω K = {K, K'} ∧ v * v ∈ K ⊔ K' := by
  have hΩG := AschTight.hypOmegaGen_of_mod hp hq hΩ
  obtain ⟨u, v, R, T, c⟩ := AschTight.Sec6Gen.exists_cfg64 hΩG hK hJ hz hj hstar hnot
  have hInA : AschTight.InA Ω K J := ⟨hstar, hnot, z, j, hz, hj, fun ⟨g, hg, hgK⟩ => hA g hg hgK⟩
  obtain ⟨-, -, ⟨Kstar, hKs, htw, -, hvv, -, -⟩, ⟨-, -, hVsyl⟩, -⟩ :=
    AschTight.Sec6Gen.l6_4ThreeGenAll G Ω hΩG K hK J hJ hInA z j hz hj _ _ rfl rfl u v c.hU
      c.hUK c.hV c.hVJ c.hUV R T c.hR c.hT c.huR c.hvT c.hRN c.hTN
  exact ⟨v, Kstar, c.hV, c.hVJ, hVsyl, hKs, htw, hvv⟩

end Data

section Sylow

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K K' V₀ : Subgroup G} {z : G}

omit [Finite G] in
theorem le_centralizer_of_isUniqueInvolution (hz : IsUniqueInvolution K z) :
    K ≤ Subgroup.centralizer ({z} : Set G) := fun _ hw =>
  Subgroup.mem_centralizer_singleton_iff.mpr (hz.commute_of_mem hw).symm

theorem exists_sylow_setup (hΩ : ConjInvariant Ω) (hz : IsUniqueInvolution K z)
    (hz' : IsUniqueInvolution K' z) (htw : twinSet Ω K = {K, K'}) (hne : K' ≠ K)
    (hKN : K ≤ Subgroup.normalizer (K' : Set G)) (hK'N : K' ≤ Subgroup.normalizer (K : Set G))
    (hV₀2 : IsPGroup 2 V₀) (hV₀C : V₀ ≤ Subgroup.centralizer ({z} : Set G)) :
    ∃ S : Sylow 2 G, V₀ ≤ (S : Subgroup G) ∧ IsSylow2In (K ⊓ (S : Subgroup G)) K ∧
      IsSylow2In (K' ⊓ (S : Subgroup G)) K' := by
  have hCN := le_normalizer_sup_pair hΩ hz htw hne
  have hM : K ⊔ K' ≤ Subgroup.centralizer ({z} : Set G) :=
    sup_le (le_centralizer_of_isUniqueInvolution hz) (le_centralizer_of_isUniqueInvolution hz')
  obtain ⟨Q, hQ, hV₀Q⟩ := IsSylow2In.exists_ge hV₀2 hV₀C
  obtain ⟨S, hQS⟩ := hQ.2.1.exists_le_sylow
  have h1 := Disconnected.AschTight.Sec7.isSylow2In_inf_of_normal hQ hM hCN
  refine ⟨S, hV₀Q.trans hQS, ?_, ?_⟩
  · have hKN' : K ⊔ K' ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hK'N
    have h2 := Disconnected.AschTight.Sec7.isSylow2In_inf_of_normal h1 le_sup_left hKN'
    have hle : (Q ⊓ (K ⊔ K')) ⊓ K ≤ K ⊓ (S : Subgroup G) :=
      le_inf inf_le_right (inf_le_left.trans (inf_le_left.trans hQS))
    have h3 := h2.eq_of_le (S.isPGroup'.to_le inf_le_right) inf_le_left hle
    rw [h3]
    exact h2
  · have hKN' : K ⊔ K' ≤ Subgroup.normalizer (K' : Set G) := sup_le hKN Subgroup.le_normalizer
    have h2 := Disconnected.AschTight.Sec7.isSylow2In_inf_of_normal h1 le_sup_right hKN'
    have hle : (Q ⊓ (K ⊔ K')) ⊓ K' ≤ K' ⊓ (S : Subgroup G) :=
      le_inf inf_le_right (inf_le_left.trans (inf_le_left.trans hQS))
    have h3 := h2.eq_of_le (S.isPGroup'.to_le inf_le_right) inf_le_left hle
    rw [h3]
    exact h2

theorem rset_inf_sylow (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω) (hK : K ∈ Ω)
    (hz : IsUniqueInvolution K z) (htw : twinSet Ω K = {K, K'})
    (nbr : ∀ L ∈ omegaNbr Ω K, L ∈ twinSet Ω K) (S : Sylow 2 G)
    (hR : IsSylow2In (K ⊓ (S : Subgroup G)) K) (hR' : IsSylow2In (K' ⊓ (S : Subgroup G)) K') :
    ∀ T ∈ RSet Ω, T ≤ (S : Subgroup G) → T = K ⊓ (S : Subgroup G) ∨ T = K' ⊓ (S : Subgroup G) := by
  intro T hT hTS
  by_cases hTR : T = K ⊓ (S : Subgroup G)
  · exact Or.inl hTR
  refine Or.inr ?_
  have hRset : K ⊓ (S : Subgroup G) ∈ RSet Ω := mem_RSet_of_isSylow2In hK hR
  have h8R := hΩ.eight_le_of_mem_RSet hp hRset
  have hzR : z ∈ K ⊓ (S : Subgroup G) := mem_of_isPGroup hz hR.1 hR.2.1 (by omega)
  obtain ⟨L, hLΩ, hTL⟩ := exists_isSylow2In_of_mem_RSet hT
  have hcomm := l6_7_proved p f hp hq G Ω hΩ S T hT _ hRset hTS inf_le_right hTR
  have hTc : T ≤ Subgroup.centralizer ({z} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm x hx z hzR)
  have h8T := hΩ.eight_le_of_mem_RSet hp hT
  by_cases hLK : L = K
  · subst hLK
    exact absurd (hTL.eq_of_le hR.2.1 hR.1 (le_inf hTL.1 hTS)).symm hTR
  have hTN : T ≤ Subgroup.normalizer (K : Set G) :=
    hΩ.le_normalizer_of_le_centralizer hp hq hK hLΩ (Ne.symm hLK) hz hTL.1 hTL.2.1 (by omega) hTc
  have hLmem : L ∈ twinSet Ω K := nbr L ⟨hLΩ, hLK, T, hT, hTL.1, hTN⟩
  rw [htw] at hLmem
  rcases hLmem with h | h
  · exact absurd h hLK
  · subst h
    exact (hTL.eq_of_le hR'.2.1 hR'.1 (le_inf hTL.1 hTS)).symm

omit [Finite G] in
theorem sylow_le_centralizer (hΩ : ConjInvariant Ω) (hz : IsUniqueInvolution K z)
    (hz' : IsUniqueInvolution K' z) (S : Sylow 2 G)
    (hR : IsSylow2In (K ⊓ (S : Subgroup G)) K) (hR' : IsSylow2In (K' ⊓ (S : Subgroup G)) K')
    (hRset : K ⊓ (S : Subgroup G) ∈ RSet Ω) (hzR : z ∈ K ⊓ (S : Subgroup G))
    (hzR' : z ∈ K' ⊓ (S : Subgroup G))
    (hrset : ∀ T ∈ RSet Ω, T ≤ (S : Subgroup G) →
      T = K ⊓ (S : Subgroup G) ∨ T = K' ⊓ (S : Subgroup G)) :
    (S : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := by
  intro s hs
  have hRu : IsUniqueInvolution (K ⊓ (S : Subgroup G)) z :=
    ⟨hzR, hz.ne_one, hz.sq, fun y hy hy2 => hz.unique y (hR.1 hy) hy2⟩
  have hRu' : IsUniqueInvolution (K' ⊓ (S : Subgroup G)) z :=
    ⟨hzR', hz'.ne_one, hz'.sq, fun y hy hy2 => hz'.unique y (hR'.1 hy) hy2⟩
  have hconj : conjSub s (K ⊓ (S : Subgroup G)) ∈ RSet Ω := RSet.conj hΩ hRset s
  have hle : conjSub s (K ⊓ (S : Subgroup G)) ≤ (S : Subgroup G) :=
    conjSub_le_of_le_of_mem inf_le_right hs
  have hszs : s * z * s⁻¹ = z := by
    rcases hrset _ hconj hle with h | h
    · exact hRu.conj_eq h
    · have := hRu.conj s
      rw [h] at this
      exact this.eq hRu'
  rw [Subgroup.mem_centralizer_singleton_iff]
  rw [mul_inv_eq_iff_eq_mul] at hszs
  exact hszs

theorem exists_W_setup (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω) (S : Sylow 2 G) :
    ∃ η : Set (Subgroup G), η ∈ etaSet Ω (S : Subgroup G) ∧
      (∀ s ∈ (S : Subgroup G), ∀ U ∈ η, conjSub s U ∈ η) ∧
      (⨆ U ∈ η, U) ∈ WSet Ω ∧ (⨆ U ∈ η, U) ≤ (S : Subgroup G) ∧
      (S : Subgroup G) ≤ Subgroup.normalizer ((⨆ U ∈ η, U : Subgroup G) : Set G) := by
  obtain ⟨η, hη, hinv⟩ := (l6_9_proved p f hp hq G Ω hΩ S).1
  refine ⟨η, hη, hinv, ⟨η, ⟨S, hη, hinv⟩, rfl⟩, iSup₂_le fun U hU => (hη.1 hU).2, ?_⟩
  intro s hs
  exact mem_normalizer_of_conjSub_le (conjSub_iSup_le' (hinv s hs))

end Sylow

variable {p f : ℕ} [Fact p.Prime]

theorem sec20Setup_of (hn : OmegaNbrTwin p f) : Sec20Setup p f := by
  intro G _ _ _ K J z t a g h
  have hp := h.branch.odd
  have hq := h.branch.five
  have hΩ : HypOmegaMod p f (CoreAssembly.conjClass K) := h.hyp
  have hKΩ : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  have hJΩ : J ∈ CoreAssembly.conjClass K := h.viol.mem
  have hzK := h.viol.hzK
  have hzJ := h.viol.hzJ
  obtain ⟨v, Ks, hVU, hVJ, hVsyl, -, htw, hvv⟩ :=
    exists_hexagon_data hp hq hΩ hKΩ hJΩ hzK hzJ h.viol.star h.viol.not_nbr h.viol.no_conj
  set K' : Subgroup G := conjSub a J with hK'
  have hK'Ω : K' ∈ CoreAssembly.conjClass K := hΩ.conjInvariant a J hJΩ
  have hzK' : IsUniqueInvolution K' z := by
    have := hzJ.conj a
    rwa [h.haz] at this
  have hK'tw : K' ∈ twinSet (CoreAssembly.conjClass K) K := ⟨hK'Ω, z, hzK, hzK'⟩
  have hK's : K' = Ks := by
    rw [htw] at hK'tw
    rcases hK'tw with h1 | h1
    · exact absurd h1 h.hne
    · exact h1
  have htw' : twinSet (CoreAssembly.conjClass K) K = {K, K'} := by rw [htw, hK's]
  have hvv' : v * v ∈ K ⊔ K' := by rw [hK's]; exact hvv
  have hV2 : IsPGroup 2 (Subgroup.zpowers v) := hΩ.isPGroup_of_mem_USet hp hVU
  obtain ⟨-, -, -, -, -, -, hVc, -, h4V⟩ := hΩ.exists_data_of_mem_USet hp hVU
  have htV : t ∈ Subgroup.zpowers v :=
    mem_of_isPGroup hzJ hVJ hV2 (by omega)
  have htKK : t ∈ K ⊔ K' := by
    obtain ⟨w, hw, hww⟩ := exists_sq_eq_of_cyclic hzJ hVJ hVc hV2 h4V
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    rw [← hww, ← (Commute.refl v).mul_zpow]
    exact Subgroup.zpow_mem _ hvv' k
  have hswap : ∃ g' ∈ Subgroup.centralizer ({z} : Set G), conjSub g' K = K' :=
    ⟨g, Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp h.hgz), h.hg⟩
  have hKN : K ≤ Subgroup.normalizer (K' : Set G) :=
    hΩ.le_normalizer_of_twin hKΩ hK'Ω (Ne.symm h.hne) hzK hzK'
  have hK'N : K' ≤ Subgroup.normalizer (K : Set G) :=
    hΩ.le_normalizer_of_twin hK'Ω hKΩ h.hne hzK' hzK
  obtain ⟨S, hVS, hR, hR'⟩ := exists_sylow_setup hΩ.conjInvariant hzK hzK' htw' h.hne hKN hK'N hV2
    (hVsyl.1.trans inf_le_right)
  have hRset : K ⊓ (S : Subgroup G) ∈ RSet (CoreAssembly.conjClass K) :=
    mem_RSet_of_isSylow2In hKΩ hR
  have hrset := rset_inf_sylow hp hq hΩ hKΩ hzK htw' (hn G K J z t a g h) S hR hR'
  have h8 := hΩ.eight_le_of_mem_RSet hp hRset
  have hzR : z ∈ K ⊓ (S : Subgroup G) := mem_of_isPGroup hzK hR.1 hR.2.1 (by omega)
  have hRset' : K' ⊓ (S : Subgroup G) ∈ RSet (CoreAssembly.conjClass K) :=
    mem_RSet_of_isSylow2In hK'Ω hR'
  have h8' := hΩ.eight_le_of_mem_RSet hp hRset'
  have hzR' : z ∈ K' ⊓ (S : Subgroup G) := mem_of_isPGroup hzK' hR'.1 hR'.2.1 (by omega)
  have hSz := sylow_le_centralizer hΩ.conjInvariant hzK hzK' S hR hR' hRset hzR hzR' hrset
  obtain ⟨η, hηS, hinv, hW, hWS, hWN⟩ := exists_W_setup hp hq hΩ S
  have hηS' : ∀ V ∈ η, V ≤ (S : Subgroup G) := fun V hV => (hηS.1 hV).2
  have hVW : Subgroup.zpowers v ≤ ⨆ U ∈ η, U := by
    obtain ⟨V', ⟨hV'η, hcase⟩, -⟩ := l6_8 p f hp hq G (CoreAssembly.conjClass K) hΩ S
      (Subgroup.zpowers v) hVU hVS η ⟨S, hηS, hinv⟩ hηS'
    rcases hcase with h1 | h1
    · rw [h1]
      exact le_iSup₂ (f := fun U (_ : U ∈ η) => U) V' hV'η
    · exfalso
      have hle : Subgroup.zpowers v ⊔ V' ≤ (S : Subgroup G) := sup_le hVS (hηS' V' hV'η)
      rcases hrset _ h1 hle with h2 | h2
      · have hmem : t ∈ Subgroup.zpowers v ⊔ V' := Subgroup.mem_sup_left htV
        rw [h2] at hmem
        have htK : t ∈ K := (Subgroup.mem_inf.mp hmem).1
        rcases hzK.unique t htK hzJ.sq with h3 | h3
        · exact hzJ.ne_one h3
        · exact h.viol.ne_involution hΩ hKΩ h3
      · have hmem : t ∈ Subgroup.zpowers v ⊔ V' := Subgroup.mem_sup_left htV
        rw [h2] at hmem
        have htK : t ∈ K' := (Subgroup.mem_inf.mp hmem).1
        rcases hzK'.unique t htK hzJ.sq with h3 | h3
        · exact hzJ.ne_one h3
        · exact h.viol.ne_involution hΩ hKΩ h3
  exact ⟨K', S, K ⊓ (S : Subgroup G), K' ⊓ (S : Subgroup G), ⨆ U ∈ η, U, Subgroup.zpowers v,
    ⟨h.branch, h.hyp, h.below, h.ih, h.viol, h.hne, htw', hswap, htKK, h.star, hSz, hR,
      inf_le_right, hR', inf_le_right, hrset, hW, hWS, hWN, hVU, hVS, hVW, htV⟩⟩

end CFSG.ClassicalInvolution.Asc77.T3CII
