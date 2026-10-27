module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockDefs
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGroups
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockNormal
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockTargets
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimUnitaryLie
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockThreeFivesGroup

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.QuasithinUnique

theorem card_mem_of_hasLeviBlocks {Q : Type} [Group Q] [Finite Q] {𝒯 : Set ℕ}
    (hQ : HasLeviBlocks Q 𝒯) {N : Subgroup Q} [hNn : N.Normal] {T : Type} [Group T] [Finite T]
    [IsSimpleGroup T] (hT : ∃ a b : T, a * b ≠ b * a) (f : ↥N →* T)
    (hf : Function.Surjective f) : Nat.card T ∈ 𝒯 := by
  obtain ⟨k, G, _, _, S, β, hker, hpi, hcomm, hS, hT𝒯⟩ := hQ
  set βN : ↥N →* ↥(N.map β) := (β.comp N.subtype).codRestrict (N.map β)
    (fun n => ⟨n, n.2, rfl⟩) with hβN
  have hβNs : Function.Surjective βN := by
    rintro ⟨_, ⟨n, hn, rfl⟩⟩
    exact ⟨⟨n, hn⟩, rfl⟩
  have hk : βN.ker ≤ f.ker := by
    have h2 : IsPGroup 2 βN.ker := by
      intro n
      have hn : (n : ↥N).1 ∈ β.ker := by
        have := congrArg Subtype.val (MonoidHom.mem_ker.mp n.2)
        exact MonoidHom.mem_ker.mpr this
      obtain ⟨e, he⟩ := hker ⟨_, hn⟩
      refine ⟨e, Subtype.ext (Subtype.ext ?_)⟩
      have := congrArg Subtype.val he
      simpa using this
    have : (βN.ker.map f).Normal := (MonoidHom.normal_ker βN).map f hf
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (βN.ker.map f) with h | h
    · exact (Subgroup.map_eq_bot_iff _).mp h
    · exfalso
      refine LeviBlock.not_isPGroup_two_of_simple hT fun t => ?_
      have ht : t ∈ βN.ker.map f := h ▸ Subgroup.mem_top t
      obtain ⟨n, hn, rfl⟩ := ht
      obtain ⟨e, he⟩ := h2 ⟨n, hn⟩
      exact ⟨e, by rw [← map_pow]; exact (congrArg (fun x => f x.1) he).trans (map_one f)⟩
  obtain ⟨f', hf', -⟩ := LeviBlock.exists_factor βN hβNs f hf hk
  have hNX : N.map β ≤ β.range := Subgroup.map_le_range β N
  have hNn' : β.range ≤ Subgroup.normalizer ((N.map β : Subgroup _) : Set _) := by
    rintro _ ⟨q, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact ⟨q * n * q⁻¹, hNn.conj_mem n hn q, by simp⟩
    · intro hy
      obtain ⟨n, hn, hne⟩ := hy
      refine ⟨q⁻¹ * n * q, by simpa using hNn.conj_mem n hn q⁻¹, ?_⟩
      rw [map_mul, map_mul, hne, map_inv]
      group
  obtain ⟨j, hj, hcard⟩ := exists_block_of_normal_section hpi hcomm hS hNX hNn' hT f' hf'
  exact hcard ▸ hT𝒯 j hj

theorem card_mem_of_section {Y : Type} [Group Y] [Finite Y] {L P : Subgroup Y} (hPL : P ≤ L)
    {K : Type} [Group K] [Finite K] (ρ : K →* ↥L) (hρ : Function.Surjective ρ) {𝒯 : Set ℕ}
    (hQ : HasLeviBlocks ↥((P.subgroupOf L).comap ρ) 𝒯) {O W : Subgroup Y} (hOP : O ≤ P)
    (hPO : P ≤ Subgroup.normalizer (O : Set Y)) (hO3 : Nat.Coprime 3 (Nat.card O))
    (hWP : W ≤ P) (hPWO : P ≤ Subgroup.normalizer ((W ⊔ O : Subgroup Y) : Set Y))
    {U : Type} [Group U] [Finite U] [IsSimpleGroup U] (hU : ∃ a b : U, a * b ≠ b * a)
    (h3U : 3 ∣ Nat.card U) (ψ : ↥W →* U) (hψ : Function.Surjective ψ) : Nat.card U ∈ 𝒯 := by
  set O' := O.subgroupOf P with hO'
  set W' := W.subgroupOf P with hW'
  have hO'n : O'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hOP).mpr hPO
  have hN'n : (W' ⊔ O').Normal := by
    rw [hO', hW', ← Subgroup.subgroupOf_sup hWP hOP]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (sup_le hWP hOP)).mpr hPWO
  set ψ' : ↥W' →* U := ψ.comp (Subgroup.subgroupOfEquivOfLe hWP).toMonoidHom with hψ'd
  have hψ' : Function.Surjective ψ' := hψ.comp (MulEquiv.surjective _)
  have hkill : O'.subgroupOf W' ≤ ψ'.ker := by
    have := hO'n
    have : ((O'.subgroupOf W').map ψ').Normal :=
      (inferInstance : (O'.subgroupOf W').Normal).map ψ' hψ'
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((O'.subgroupOf W').map ψ') with h | h
    · exact (Subgroup.map_eq_bot_iff _).mp h
    · exfalso
      have h1 := Subgroup.card_map_dvd (O'.subgroupOf W') ψ'
      rw [h, Subgroup.card_top] at h1
      have h2 : Nat.card (O'.subgroupOf W') ∣ Nat.card O := by
        have := Subgroup.card_dvd_of_le (show (O'.subgroupOf W').map W'.subtype ≤ O' from by
          rintro _ ⟨x, hx, rfl⟩; exact hx)
        rw [Subgroup.card_map_of_injective W'.subtype_injective] at this
        exact this.trans (by rw [hO', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOP).toEquiv])
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
        (Nat.Coprime.coprime_dvd_right (h1.trans h2) hO3) h3U
  set e₂ := QuotientGroup.quotientInfEquivProdNormalQuotient W' O' with he₂
  set ψq : ↥W' ⧸ O'.subgroupOf W' →* U := QuotientGroup.lift _ ψ' hkill with hψq
  set f₀ : ↥(W' ⊔ O') →* U :=
    (ψq.comp e₂.symm.toMonoidHom).comp (QuotientGroup.mk' (O'.subgroupOf (W' ⊔ O'))) with hf₀
  have hf₀ : Function.Surjective f₀ := by
    intro u
    obtain ⟨w, rfl⟩ := hψ' u
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (O'.subgroupOf (W' ⊔ O'))
      (e₂ (QuotientGroup.mk w))
    refine ⟨y, ?_⟩
    rw [hf₀, MonoidHom.comp_apply, MonoidHom.comp_apply, hy]
    simp [hψq]
  set Q := (P.subgroupOf L).comap ρ with hQd
  set ρQ : ↥Q →* ↥P :=
    { toFun := fun q => ⟨((ρ q : ↥L) : Y), Subgroup.mem_subgroupOf.mp q.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp } with hρQ
  have hρQs : Function.Surjective ρQ := by
    rintro ⟨p, hp⟩
    obtain ⟨k, hk⟩ := hρ ⟨p, hPL hp⟩
    refine ⟨⟨k, ?_⟩, ?_⟩
    · show ρ k ∈ P.subgroupOf L
      rw [hk]
      exact Subgroup.mem_subgroupOf.mpr hp
    · ext
      simp [hρQ, hk]
  set Ñ := (W' ⊔ O').comap ρQ with hÑ
  have : Ñ.Normal := hN'n.comap ρQ
  set g : ↥Ñ →* U := f₀.comp (ρQ.subgroupComap (W' ⊔ O')) with hg
  have hg' : Function.Surjective g := by
    intro u
    obtain ⟨⟨y, hy⟩, rfl⟩ := hf₀ u
    obtain ⟨q, rfl⟩ := hρQs y
    exact ⟨⟨q, hy⟩, rfl⟩
  exact card_mem_of_hasLeviBlocks hQ hU g hg'

theorem su38At_of_levi {Y : Type} [Group Y] [Finite Y] {L P : Subgroup Y} (hPL : P ≤ L)
    (h : ∃ (K : Type) (_ : Group K) (_ : Finite K) (ρ : K →* ↥L) (𝒯 : Set ℕ),
      Function.Surjective ρ ∧ HasLeviBlocks ↥((P.subgroupOf L).comap ρ) 𝒯 ∧ 5515776 ∉ 𝒯) :
    ∀ (O W : Subgroup Y), O ≤ P → P ≤ Subgroup.normalizer (O : Set Y) →
      Nat.Coprime 3 (Nat.card O) → W ≤ P →
      P ≤ Subgroup.normalizer ((W ⊔ O : Subgroup Y) : Set Y) → ⁅W, W⁆ = W →
      ∀ (d : TauCeti.ValidLieTypeIndex) (ψ : ↥W →* CatGroup d), IsUThreeEightIndex d →
        Function.Surjective ψ → 3 ^ 7 ∣ Nat.card P := by
  intro O W hOP hPO hO3 hWP hPWO _ d ψ hd hψ
  exfalso
  obtain ⟨K, _, _, ρ, 𝒯, hρ, hQ, h𝒯⟩ := h
  have hd' := hd
  obtain ⟨q, hqp, -, hdq⟩ := hd'
  have : IsSimpleGroup (CatGroup d) := unitaryTarget_isSimpleGroup ⟨q, hqp, hdq⟩
  have : Finite (CatGroup d) := Finite.of_surjective ψ hψ
  have hnc : ∃ a b : CatGroup d, a * b ≠ b * a :=
    ThreeFives.exists_noncomm_of_simple inferInstance
      (by rw [LeviBlock.card_catGroup_u38 hd]; norm_num)
  have := card_mem_of_section hPL ρ hρ hQ hOP hPO hO3 hWP hPWO hnc
    (by rw [LeviBlock.card_catGroup_u38 hd]; norm_num) ψ hψ
  rw [LeviBlock.card_catGroup_u38 hd] at this
  exact h𝒯 this

theorem leviU42At_of_levi {Y : Type} [Group Y] [Finite Y] {L P : Subgroup Y} (hPL : P ≤ L)
    (h : ∃ (K : Type) (_ : Group K) (_ : Finite K) (ρ : K →* ↥L) (𝒯 : Set ℕ),
      Function.Surjective ρ ∧ HasLeviBlocks ↥((P.subgroupOf L).comap ρ) 𝒯 ∧ 25920 ∉ 𝒯) :
    LeviU42At L P := by
  intro _ O W hOP hPO hO3 hWP hPWO _ _ d ψ hd hψ _ _
  exfalso
  obtain ⟨K, _, _, ρ, 𝒯, hρ, hQ, h𝒯⟩ := h
  obtain ⟨hcard, hsimp⟩ := LeviBlock.catGroup_u42_facts hd
  have : Finite (CatGroup d) := Finite.of_surjective ψ hψ
  have hnc : ∃ a b : CatGroup d, a * b ≠ b * a :=
    ThreeFives.exists_noncomm_of_simple hsimp (by rw [hcard]; norm_num)
  have := card_mem_of_section hPL ρ hρ hQ hOP hPO hO3 hWP hPWO hnc
    (by rw [hcard]; norm_num) ψ hψ
  rw [hcard] at this
  exact h𝒯 this

end CFSG.AGLEmbedding
