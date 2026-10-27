module

public import CFSG.CGT.Foote82.BridgeG
public import CFSG.CGT.Foote82.FModule
public import CFSG.CGT.Foote82.OddCover
public import CFSG.CGT.Foote82.Statements
public import CFSG.CGT.Foote82.Thm66
import CFSG.CGT.Foote82.FPrime

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11 CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec19.SimsTheoremC
open scoped commutatorElement
open Matrix

variable {G : Type} [Group G] [Finite G]

namespace TheoremG

variable {J₂ X : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  (lin : TildeULin J₂ X V)

theorem img_mono {A B : Subgroup G} (h : A ≤ B) : lin.img A ≤ lin.img B :=
  Subgroup.map_mono fun _ hx => h hx

theorem ρ_inclusion_mem_img (hJX : J₂ ≤ X) (j : ↥J₂) :
    lin.ρ (Subgroup.inclusion hJX j) ∈ lin.img J₂ :=
  Subgroup.mem_map.mpr ⟨Subgroup.inclusion hJX j, Subgroup.mem_subgroupOf.mpr j.2, rfl⟩

theorem mem_blockQ_of_mem_pCore {J : Subgroup G} {j : ↥J} (hj : j ∈ CFSG.pCore 2 ↥J) :
    (j : G) ∈ blockQ J :=
  Subgroup.mem_map.mpr ⟨j, hj, rfl⟩

end TheoremG

namespace TildeULin

variable {J₁ J₂ X : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  (lin : TildeULin J₂ X V)

theorem eq_of_img_le_img {H : Subgroup G} (hJ : IsFooteBlock H J₂) (hJX : J₂ ≤ X)
    (hJ₁J₂ : J₁ ≤ J₂) (hU : blockU J₁ = ⁅blockQ J₂, J₁⁆) (hle : lin.img J₂ ≤ lin.img J₁) :
    J₁ = J₂ := by
  let ρb := lin.ρbar hJ hJX
  let A : Subgroup (↥J₂ ⧸ CFSG.pCore 2 ↥J₂) :=
    (J₁.subgroupOf J₂).map (QuotientGroup.mk' (CFSG.pCore 2 ↥J₂))
  have hmem : ∀ p : ↥J₂ ⧸ CFSG.pCore 2 ↥J₂, p ∈ A ⊔ ρb.ker := by
    intro p
    obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective p
    obtain ⟨x, hx, hxj⟩ := Subgroup.mem_map.mp (hle (TheoremG.ρ_inclusion_mem_img lin hJX j))
    have hxJ₁ : (x : G) ∈ J₁ := Subgroup.mem_subgroupOf.mp hx
    let j₁ : ↥J₂ := ⟨(x : G), hJ₁J₂ hxJ₁⟩
    have hj₁ : (QuotientGroup.mk j₁ : ↥J₂ ⧸ CFSG.pCore 2 ↥J₂) ∈ A :=
      Subgroup.mem_map.mpr ⟨j₁, Subgroup.mem_subgroupOf.mpr hxJ₁, rfl⟩
    have hk : (QuotientGroup.mk j₁ : ↥J₂ ⧸ CFSG.pCore 2 ↥J₂)⁻¹ * QuotientGroup.mk j ∈ ρb.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, lin.ρbar_mk, lin.ρbar_mk, inv_mul_eq_one]
      exact hxj
    simpa using Subgroup.mul_mem_sup hj₁ hk
  have hAZ : A ⊔ Subgroup.center (↥J₂ ⧸ CFSG.pCore 2 ↥J₂) = ⊤ :=
    eq_top_iff.mpr fun p _ => sup_le_sup_left (lin.ker_ρbar_le_center hJ hJX) A (hmem p)
  haveI hAn : A.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hAZ]
    exact sup_le Subgroup.le_normalizer (Subgroup.center_le_normalizer _)
  have hAtop : A = ⊤ :=
    eq_top_iff.mpr (hJ.quasisimple.1 ▸
      Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hAZ inferInstance)
  have hdecomp : ∀ j : ↥J₂, ∃ j₁ : ↥J₂, (j₁ : G) ∈ J₁ ∧ j₁⁻¹ * j ∈ CFSG.pCore 2 ↥J₂ := by
    intro j
    obtain ⟨j₁, hj₁, hj₁j⟩ := Subgroup.mem_map.mp
      (hAtop ▸ Subgroup.mem_top (QuotientGroup.mk j : ↥J₂ ⧸ CFSG.pCore 2 ↥J₂))
    exact ⟨j₁, Subgroup.mem_subgroupOf.mp hj₁, QuotientGroup.eq.mp hj₁j⟩
  have hQn : blockQ J₂ ≤ Subgroup.normalizer (J₁ : Set G) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_right, ← hU]
    exact blockU_le_self J₁
  haveI hN : (J₁.subgroupOf J₂).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨j₁, hj₁, hq⟩ := hdecomp g
    have hqn : (((j₁⁻¹ * g : ↥J₂) : G) * n * ((j₁⁻¹ * g : ↥J₂) : G)⁻¹) ∈ J₁ :=
      (Subgroup.mem_normalizer_iff.mp (hQn (TheoremG.mem_blockQ_of_mem_pCore hq)) n).mp
        (Subgroup.mem_subgroupOf.mp hn)
    rw [Subgroup.mem_subgroupOf]
    have : ((g * n * g⁻¹ : ↥J₂) : G) =
        (j₁ : G) * ((((j₁⁻¹ * g : ↥J₂) : G) * n * ((j₁⁻¹ * g : ↥J₂) : G)⁻¹)) * (j₁ : G)⁻¹ := by
      simp [mul_assoc]
    rw [this]
    exact J₁.mul_mem (J₁.mul_mem hj₁ hqn) (J₁.inv_mem hj₁)
  have hPg : IsPGroup 2 (↥J₂ ⧸ J₁.subgroupOf J₂) := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨j₁, hj₁, hq⟩ := hdecomp g
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥J₂)) ⟨_, hq⟩
    refine ⟨k, ?_⟩
    have hmk : (QuotientGroup.mk g : ↥J₂ ⧸ J₁.subgroupOf J₂) = QuotientGroup.mk (j₁⁻¹ * g) := by
      rw [← one_mul (QuotientGroup.mk (j₁⁻¹ * g) : ↥J₂ ⧸ J₁.subgroupOf J₂),
        ← (QuotientGroup.eq_one_iff j₁).mpr (Subgroup.mem_subgroupOf.mpr hj₁),
        ← QuotientGroup.mk_mul, mul_inv_cancel_left]
    rw [hmk, ← QuotientGroup.mk_pow]
    have : (j₁⁻¹ * g) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    rw [this, QuotientGroup.mk_one]
  have htop := hJ.residual (J₁.subgroupOf J₂) hPg
  refine le_antisymm hJ₁J₂ fun j hj => ?_
  have : (⟨j, hj⟩ : ↥J₂) ∈ J₁.subgroupOf J₂ := htop ▸ Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.mp this

theorem ker_ρbar_eq_bot_of_equiv {H : Subgroup G} {M : Type} [Group M] (hJ : IsFooteBlock H J₂)
    (hJX : J₂ ≤ X) (φ : ↥(lin.img J₂) ≃* M)
    (hcover : ∀ η : (↥J₂ ⧸ CFSG.pCore 2 ↥J₂) →* M, Function.Surjective η →
      η.ker ≤ Subgroup.center (↥J₂ ⧸ CFSG.pCore 2 ↥J₂) → Odd (Nat.card η.ker) → η.ker = ⊥) :
    (lin.ρbar hJ hJX).ker = ⊥ := by
  let ρb := lin.ρbar hJ hJX
  have hmem : ∀ p, ρb p ∈ lin.img J₂ := fun p => by
    rw [← lin.range_ρbar hJ hJX]
    exact MonoidHom.mem_range.mpr ⟨p, rfl⟩
  let r : (↥J₂ ⧸ CFSG.pCore 2 ↥J₂) →* ↥(lin.img J₂) := ρb.codRestrict _ hmem
  let η : (↥J₂ ⧸ CFSG.pCore 2 ↥J₂) →* M := φ.toMonoidHom.comp r
  have hker : η.ker = ρb.ker := by
    ext p
    simp only [MonoidHom.mem_ker, η, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff _ φ.injective]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hsurj : Function.Surjective η := by
    intro m
    obtain ⟨e, rfl⟩ := φ.surjective m
    have he : (e : GLV V) ∈ ρb.range := by
      rw [lin.range_ρbar hJ hJX]
      exact e.2
    obtain ⟨p, hp⟩ := he
    refine ⟨p, ?_⟩
    simp only [η, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    congr 1
    exact Subtype.ext hp
  have := hcover η hsurj (hker ▸ lin.ker_ρbar_le_center hJ hJX)
    (hker ▸ lin.odd_card_ker_ρbar hJ hJX)
  rwa [hker] at this

theorem exists_alpha_beta {H : Subgroup G} {M M' : Type} [Group M] [AddGroup M']
    (hJ : IsFooteBlock H J₂) (hJX : J₂ ≤ X) (φ : ↥(lin.img J₂) ≃* M) (ψ : V ≃+ M')
    (hker : (lin.ρbar hJ hJX).ker = ⊥) :
    ∃ α : ↥J₂ →* M, Function.Surjective α ∧ α.ker = CFSG.pCore 2 ↥J₂ ∧
      ∃ β : ↥(blockU J₂) →* Multiplicative M', Function.Surjective β ∧
        β.ker = (blockZ J₂).subgroupOf (blockU J₂) ∧
        ∀ (ℓ : ↥J₂) (u v : ↥(blockU J₂)), (v : G) = (ℓ : G) * (u : G) * (ℓ : G)⁻¹ →
          ∃ e : ↥(lin.img J₂), φ e = α ℓ ∧
            Multiplicative.toAdd (β v) =
              ψ ((e : GLV V) (ψ.symm (Multiplicative.toAdd (β u)))) := by
  let r : ↥J₂ →* ↥(lin.img J₂) :=
    (lin.ρ.comp (Subgroup.inclusion hJX)).codRestrict _ (TheoremG.ρ_inclusion_mem_img lin hJX)
  refine ⟨φ.toMonoidHom.comp r, ?_, ?_, ψ.toMultiplicative.toMonoidHom.comp lin.π, ?_, ?_, ?_⟩
  · intro m
    obtain ⟨e, rfl⟩ := φ.surjective m
    obtain ⟨x, hx, hxe⟩ := Subgroup.mem_map.mp e.2
    refine ⟨⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩, ?_⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    congr 1
    exact Subtype.ext hxe
  · ext j
    rw [MonoidHom.mem_ker]
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, map_eq_one_iff _ φ.injective]
    constructor
    · intro h
      have h2 : lin.ρ (Subgroup.inclusion hJX j) = 1 := congrArg Subtype.val h
      have h4 : (QuotientGroup.mk j : ↥J₂ ⧸ CFSG.pCore 2 ↥J₂) ∈ (lin.ρbar hJ hJX).ker := by
        rw [MonoidHom.mem_ker, lin.ρbar_mk]
        exact h2
      rw [hker] at h4
      exact (QuotientGroup.eq_one_iff j).mp (Subgroup.mem_bot.mp h4)
    · intro hj
      have h3 : (QuotientGroup.mk j : ↥J₂ ⧸ CFSG.pCore 2 ↥J₂) = 1 :=
        (QuotientGroup.eq_one_iff j).mpr hj
      refine Subtype.ext ?_
      change lin.ρ (Subgroup.inclusion hJX j) = 1
      rw [← lin.ρbar_mk hJ hJX j, h3, map_one]
  · intro w
    obtain ⟨u, hu⟩ := lin.surj (ψ.toMultiplicative.symm w)
    exact ⟨u, by simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hu,
      MulEquiv.apply_symm_apply]⟩
  · ext u
    rw [MonoidHom.mem_ker, ← lin.ker_eq, MonoidHom.mem_ker]
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff _ ψ.toMultiplicative.injective]
  · intro ℓ u v huv
    refine ⟨⟨lin.ρ (Subgroup.inclusion hJX ℓ), TheoremG.ρ_inclusion_mem_img lin hJX ℓ⟩, rfl, ?_⟩
    have hspec := lin.spec (Subgroup.inclusion hJX ℓ) u v huv
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    show ψ (Multiplicative.toAdd (lin.π v)) =
      ψ (lin.ρ (Subgroup.inclusion hJX ℓ) (ψ.symm (ψ (Multiplicative.toAdd (lin.π u)))))
    rw [hspec, ψ.symm_apply_apply]

theorem kProper_img (hK : CFSG.Assembly.KProper CFSG.Assembly.InCatalog G) (A : Subgroup G) :
    CFSG.Assembly.KProper CFSG.Assembly.InCatalog ↥(lin.img A) :=
  CFSG.ComponentClassification.CatalogueKProper.of_surjective
    (CFSG.ComponentClassification.CatalogueKProper.subgroup
      (CFSG.ComponentClassification.CatalogueKProper.subgroup hK X) (A.subgroupOf X))
    (lin.ρ.subgroupMap (A.subgroupOf X)) (lin.ρ.subgroupMap_surjective (A.subgroupOf X))

theorem isAltNaturalType_of_isAltHeartFor {H : Subgroup G} (hJ : IsFooteBlock H J₂) (hJX : J₂ ≤ X)
    {N : ℕ} (hN : 8 ≤ N) (h : IsAltHeartFor (lin.img J₂) N) : IsAltNaturalType J₂ N := by
  obtain ⟨φ, ψ, hφψ⟩ := h
  have hker := lin.ker_ρbar_eq_bot_of_equiv hJ hJX φ
    (fun η hη hK hodd => ker_eq_bot_of_odd_alt hJ.quasisimple.1 hN η hη hK hodd)
  obtain ⟨α, hαs, hαk, β, hβs, hβk, hβ⟩ :=
    lin.exists_alpha_beta hJ hJX φ ψ hker
  refine ⟨α, hαs, hαk, β, hβs, hβk, fun ℓ u v huv x hx => ?_⟩
  obtain ⟨e, he, hβv⟩ := hβ ℓ u v huv
  refine hβv.trans ?_
  rw [← he]
  exact hφψ e _ x (by rw [ψ.apply_symm_apply]; exact hx)

theorem isOmegaMinusType_two_of_isOmegaMinusFor {H : Subgroup G} (hJ : IsFooteBlock H J₂)
    (hJX : J₂ ≤ X) (h : IsOmegaMinusFor (lin.img J₂) 2)
    (hcover : ∀ η : (↥J₂ ⧸ CFSG.pCore 2 ↥J₂) →* ↥(omegaMinusTwo 2), Function.Surjective η →
      η.ker ≤ Subgroup.center (↥J₂ ⧸ CFSG.pCore 2 ↥J₂) → Odd (Nat.card η.ker) → η.ker = ⊥) :
    IsOmegaMinusType J₂ 2 := by
  obtain ⟨φ, ψ, hφψ⟩ := h
  have hker := lin.ker_ρbar_eq_bot_of_equiv hJ hJX φ hcover
  have key : ∀ (e : ↥(lin.img J₂)) (w : Fin 2 ⊕ Fin 2 ⊕ Fin 2 → ZMod 2),
      ψ ((e : GLV V) (ψ.symm w)) =
        ((φ e : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) :
          Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) *ᵥ w :=
    fun e w => by simpa using hφψ e (ψ.symm w)
  obtain ⟨α, hαs, hαk, β, hβs, hβk, hβ⟩ := lin.exists_alpha_beta hJ hJX φ ψ.toAddEquiv hker
  refine ⟨α, hαs, hαk, β, hβs, hβk, fun ℓ u v huv => ?_⟩
  obtain ⟨e, he, hβv⟩ := hβ ℓ u v huv
  refine hβv.trans ?_
  rw [← he]
  exact key e _

end TildeULin

theorem isFType_of_footeArrow_of_thm66F_of_multiplier
    (hM : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier ↥(omegaMinusTwo 2)) ∣ 2)
    (h66 : Thm66F) (hK : CFSG.Assembly.KProper CFSG.Assembly.InCatalog G) {J₁ J₂ : Subgroup G}
    (h1 : IsFooteBlock J₁ J₁) (h2 : IsFooteBlock J₂ J₂) (hne : J₁ ≠ J₂)
    (harr : FooteArrow J₁ J₂) (hF : IsFPrimeType J₁) : IsFType J₂ := by
  obtain ⟨hJ₁J₂, hU, T, hT, hTN, hcomp⟩ := harr
  have hJX : J₂ ≤ J₂ ⊔ T := le_sup_left
  have hX : J₂ ⊔ T ≤ Subgroup.normalizer (J₂ : Set G) := sup_le Subgroup.le_normalizer hTN
  obtain ⟨V, _, _, _, ⟨lin⟩⟩ := exists_tildeULin h2 hX
  have hJ₁X : J₁ ≤ J₂ ⊔ T := hJ₁J₂.trans hJX
  have hset := lin.setup6Irr_img h1 h2 hJ₁J₂ hU hT hTN hcomp
  have hmod := lin.isFPrimeModule_img h1 h2 hJ₁J₂ hJ₁X hU hF
  have hlayer := lin.layerIn_img h2 hT hTN
  rcases h66 V _ _ _ (lin.kProper_img hK _) hset hmod with hLG | ⟨n, k, hn, hk, -, hAlt⟩ | ⟨-, hΩ⟩
  · exact absurd (lin.eq_of_img_le_img h2 hJX hJ₁J₂ hU
      (by rw [hLG]; exact TheoremG.img_mono lin hJX)) hne
  · rw [hlayer] at hAlt
    exact Or.inl ⟨n + 2 * k, by omega,
      lin.isAltNaturalType_of_isAltHeartFor h2 hJX (by omega) hAlt⟩
  · rw [hlayer] at hΩ
    exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨2, le_rfl, lin.isOmegaMinusType_two_of_isOmegaMinusFor h2 hJX hΩ
        fun η hη hZ hodd =>
          ker_eq_bot_of_odd_omegaMinus_of_card_dvd hM h2.quasisimple.1 η hη hZ hodd⟩)))

theorem isFooteBlock_self_of_inFooteB' {J : Subgroup G} (hJ : InFooteB J) : IsFooteBlock J J := by
  obtain ⟨S, -, hS⟩ := hJ
  exact ⟨le_rfl, .refl J, hS.residual, hS.quasisimple, hS.chief⟩

theorem footeSevenSharpF_of_thm66F_of_multiplier
    (hM : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier ↥(omegaMinusTwo 2)) ∣ 2)
    (h66 : Thm66F) : FooteSevenSharpF := by
  intro G _ _ hs hnab hK hc he3 J₁ J₂ hJ₁ hJ₂ hne harr hF
  exact isFType_of_footeArrow_of_thm66F_of_multiplier hM h66 hK
    (isFooteBlock_self_of_inFooteB' hJ₁) (isFooteBlock_self_of_inFooteB' hJ₂) hne harr
    (fPrimeOfEvenRankThree G hs hnab hK hc he3 J₁ hJ₁ hF)

theorem footeSevenSharpF_of_thm66F
    (h66 : Thm66F) : FooteSevenSharpF :=
  footeSevenSharpF_of_thm66F_of_multiplier (dvd_of_eq card_hopfMultiplier_omegaMinusTwo) h66

end CFSG.CGT.Foote82
