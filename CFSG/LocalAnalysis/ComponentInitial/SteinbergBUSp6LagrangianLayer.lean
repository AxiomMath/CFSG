module

public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUSp6LagrangianStatements
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUSp6LagrangianTools
public import CFSG.LocalAnalysis.QuasithinUnique.QTKECore
public import CFSG.LocalAnalysis.QuasithinUnique.Setting

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank RadicalLabels FusionOrbits
open LinearMap (BilinForm)

variable {G : Type} [Group G] {L : Subgroup G}
  {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {b : BilinForm (ZMod 2) V}
  (φ : L ≃* bilinIsometryGroup b) {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V}
  (he : IsSymplecticBasis b e) (z : G)

@[expose] def sp6LeviHom (hLX : ∀ g, leviHom φ he g ∈ sp6X φ he z) :
    GL (Fin 3) (ZMod 2) →* Sp6F φ he z :=
  (sp6πX φ he z).comp ((leviHom φ he).codRestrict (sp6X φ he z) hLX)

theorem sp6Levi_eq (hLX : ∀ g, leviHom φ he g ∈ sp6X φ he z) (g : GL (Fin 3) (ZMod 2)) :
    sp6Levi φ he z g = sp6LeviHom φ he z hLX g :=
  dite_eq_left (hLX g)

theorem sp6a_eq (hzX : z ∈ sp6X φ he z) : sp6a φ he z = QuotientGroup.mk ⟨z, hzX⟩ :=
  dite_eq_left hzX

theorem sp6_leviHom_mem (hN₂X : sp6N₂ φ e z ≤ sp6X φ he z) (hzC : z ∈ centralizer (L : Set G))
    (hz : orderOf z = 2) (g : GL (Fin 3) (ZMod 2)) : leviHom φ he g ∈ sp6X φ he z :=
  hN₂X (leviHom_mem_normalizer_radSub φ he hzC hz g)

theorem sp6_centralizer_facts (hz : orderOf z = 2) (hLX : ∀ g, leviHom φ he g ∈ sp6X φ he z)
    (hzX : z ∈ sp6X φ he z)
    (ψ : Multiplicative (ZMod 2) × GL (Fin 3) (ZMod 2) ≃*
      centralizer {(QuotientGroup.mk ⟨z, hzX⟩ : Sp6F φ he z)})
    (hψ : ∀ (s : ZMod 2) (g : GL (Fin 3) (ZMod 2))
      (h : z ^ s.val * leviHom φ he g ∈ sp6X φ he z),
      (ψ (Multiplicative.ofAdd s, g) : Sp6F φ he z) = QuotientGroup.mk ⟨_, h⟩) :
    orderOf (sp6a φ he z) = 2 ∧ Function.Injective (sp6LeviHom φ he z hLX) ∧
      (sp6LeviHom φ he z hLX).range = sp6JL φ he z ∧
      sp6JL φ he z ≤ centralizer {sp6a φ he z} ∧ zpowers (sp6a φ he z) ⊓ sp6JL φ he z = ⊥ ∧
      zpowers (sp6a φ he z) ⊔ sp6JL φ he z = centralizer {sp6a φ he z} := by
  rw [sp6a_eq φ he z hzX]
  set ι := sp6LeviHom φ he z hLX
  have hι : ∀ g, ι g = QuotientGroup.mk ⟨leviHom φ he g, hLX g⟩ := fun g => rfl
  have h0 : ∀ g, (ψ (1, g) : Sp6F φ he z) = ι g := by
    intro g
    have h' : z ^ (0 : ZMod 2).val * leviHom φ he g ∈ sp6X φ he z := by
      rw [ZMod.val_zero, pow_zero, one_mul]
      exact hLX g
    have := hψ 0 g h'
    rw [ofAdd_zero] at this
    rw [this, hι]
    exact congrArg _ (Subtype.ext (by simp))
  have hpow : ∀ s : ZMod 2, (ψ (Multiplicative.ofAdd s, 1) : Sp6F φ he z) =
      (QuotientGroup.mk ⟨z, hzX⟩ : Sp6F φ he z) ^ s.val := by
    intro s
    have h' : z ^ s.val * leviHom φ he 1 ∈ sp6X φ he z := by
      rw [map_one, mul_one]
      exact pow_mem hzX _
    rw [hψ s 1 h', ← QuotientGroup.mk_pow]
    exact congrArg _ (Subtype.ext (by simp))
  have h1 : (ψ (Multiplicative.ofAdd 1, 1) : Sp6F φ he z) = QuotientGroup.mk ⟨z, hzX⟩ := by
    rw [hpow, show (1 : ZMod 2).val = 1 from rfl, pow_one]
  have ha2 : (QuotientGroup.mk ⟨z, hzX⟩ : Sp6F φ he z) ^ 2 = 1 := by
    rw [← QuotientGroup.mk_pow]
    have : (⟨z, hzX⟩ : sp6X φ he z) ^ 2 = 1 := Subtype.ext (by
      rw [SubgroupClass.coe_pow, ← hz, pow_orderOf_eq_one]
      rfl)
    rw [this, QuotientGroup.mk_one]
  have ha1 : (QuotientGroup.mk ⟨z, hzX⟩ : Sp6F φ he z) ≠ 1 := by
    intro h
    have hψ1 : ψ (Multiplicative.ofAdd 1, 1) = ψ 1 := by
      apply Subtype.ext
      rw [map_one ψ]
      exact h1.trans h
    have := congrArg Prod.fst (ψ.injective hψ1)
    exact absurd (ofAdd_eq_one.mp this) (by decide)
  have hinj : Function.Injective ι := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hψ1 : ψ (1, g) = ψ 1 := by
      apply Subtype.ext
      rw [map_one ψ]
      exact (h0 g).trans hg
    exact congrArg Prod.snd (ψ.injective hψ1)
  have hrange : ι.range = sp6JL φ he z := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨⟨leviHom φ he g, hLX g⟩, mem_subgroupOf.mpr ⟨g, rfl⟩, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨g, hg⟩ := mem_subgroupOf.mp hy
      exact ⟨g, by rw [hι]; exact congrArg _ (Subtype.ext hg)⟩
  have hJC : sp6JL φ he z ≤ centralizer {(QuotientGroup.mk ⟨z, hzX⟩ : Sp6F φ he z)} := by
    rw [← hrange]
    rintro _ ⟨g, rfl⟩
    rw [← h0]
    exact (ψ (1, g)).2
  refine ⟨orderOf_eq_prime ha2 ha1, hinj, hrange, hJC, ?_, ?_⟩
  · rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx1
    rw [SetLike.mem_coe, ← hrange] at hx2
    obtain ⟨g, hg⟩ := hx2
    have hak : (QuotientGroup.mk ⟨z, hzX⟩ : Sp6F φ he z) ^ k =
        (ψ ((Multiplicative.ofAdd (1 : ZMod 2), 1) ^ k) : Sp6F φ he z) := by
      rw [map_zpow, SubgroupClass.coe_zpow, h1]
    have hψk : ψ ((Multiplicative.ofAdd (1 : ZMod 2), 1) ^ k) = ψ (1, g) :=
      Subtype.ext (by rw [← hak, h0, hg])
    have hg1 : g = 1 := (congrArg Prod.snd (ψ.injective hψk)).symm.trans (_root_.one_zpow k)
    rw [mem_bot, ← hg, hg1, map_one ι]
  · apply le_antisymm
    · exact sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)) hJC
    · intro c hc
      obtain ⟨⟨s, g⟩, hp⟩ := ψ.surjective ⟨c, hc⟩
      have hc' : (⟨c, hc⟩ : ↥(centralizer {(QuotientGroup.mk ⟨z, hzX⟩ : Sp6F φ he z)})) =
          ψ (s, 1) * ψ (1, g) := by
        rw [← map_mul, Prod.mk_mul_mk, mul_one, one_mul, hp]
      have hc'' : c = (ψ (s, 1) : Sp6F φ he z) * ψ (1, g) := congrArg Subtype.val hc'
      rw [hc'', h0]
      refine mul_mem_sup ?_ (by rw [← hrange]; exact ⟨g, rfl⟩)
      obtain ⟨t, rfl⟩ : ∃ t : ZMod 2, Multiplicative.ofAdd t = s := ⟨s.toAdd, rfl⟩
      rw [hpow]
      exact pow_mem (mem_zpowers _) _

theorem sp6X_ne_top (hsimple : IsSimpleGroup G) (hnonab : ∃ x y : G, x * y ≠ y * x)
    (hcard : Nat.card (sp6C₂ φ he z) = 4096) (hab : IsMulCommutative (sp6C₂ φ he z)) :
    sp6X φ he z ≠ ⊤ := by
  intro htop
  have := hsimple
  have : (sp6C₂ φ he z).Normal := normalizer_eq_top_iff.mp htop
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (sp6C₂ φ he z) with h | h
  · rw [h, card_bot] at hcard
    norm_num at hcard
  · obtain ⟨x, y, hxy⟩ := hnonab
    have hx : x ∈ sp6C₂ φ he z := by
      rw [h]
      exact mem_top x
    have hy : y ∈ sp6C₂ φ he z := by
      rw [h]
      exact mem_top y
    exact hxy (congrArg Subtype.val (hab.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))

theorem sp6_kernel_facts [Finite G] (hK₃ : Odd (Nat.card (sp6K φ he z)))
    (hK₄ : ∀ g ∈ sp6X φ he z, ∀ k ∈ sp6K φ he z, g * k * g⁻¹ ∈ sp6K φ he z)
    (κ : sp6X φ he z →* MulAut (sp6C₂ φ he z))
    (hκ₁ : ∀ (x : sp6X φ he z) (c : sp6C₂ φ he z),
      ((κ x c : sp6C₂ φ he z) : G) = x * c * (x : G)⁻¹)
    (hκ₂ : κ.ker = (sp6C₂ φ he z ⊔ sp6K φ he z).subgroupOf (sp6X φ he z)) :
    sp6KBar φ he z ≤ sp6Ro φ he z ∧
    ((sp6Ro φ he z).comap (sp6πX φ he z)).Normal ∧
    (sp6C₂ φ he z).subgroupOf (sp6X φ he z) ≤ (sp6Ro φ he z).comap (sp6πX φ he z) ∧
    ((sp6Ro φ he z).comap (sp6πX φ he z)).map (sp6πX φ he z) = sp6Ro φ he z ∧
    ((sp6πX φ he z).comp ((sp6Ro φ he z).comap (sp6πX φ he z)).subtype).ker =
      ((sp6C₂ φ he z).subgroupOf (sp6X φ he z)).subgroupOf
        ((sp6Ro φ he z).comap (sp6πX φ he z)) ∧
    (∃ κF : Sp6F φ he z →* MulAut (sp6C₂ φ he z),
      (∀ (x : sp6X φ he z) (c : sp6C₂ φ he z),
        ((κF (sp6πX φ he z x) c : sp6C₂ φ he z) : G) = x * c * (x : G)⁻¹) ∧
      κF.ker = sp6KBar φ he z ∧
      (κF.comp (sp6Ro φ he z).subtype).ker = (sp6KBar φ he z).subgroupOf (sp6Ro φ he z)) ∧
    (sp6KBar φ he z).Normal ∧ ((sp6C₂ φ he z ⊔ sp6K φ he z).subgroupOf (sp6X φ he z)).Normal ∧
    ∀ [(sp6KBar φ he z).Normal]
      [((sp6C₂ φ he z ⊔ sp6K φ he z).subgroupOf (sp6X φ he z)).Normal],
      (∃ eK : ↥(sp6X φ he z) ⧸ (sp6C₂ φ he z ⊔ sp6K φ he z).subgroupOf (sp6X φ he z) ≃*
          Sp6F φ he z ⧸ sp6KBar φ he z,
        ∀ x : sp6X φ he z, eK (QuotientGroup.mk x) = QuotientGroup.mk (sp6πX φ he z x)) ∧
      CFSG.pPrimeCore 2 (Sp6F φ he z ⧸ sp6KBar φ he z) =
        (sp6Ro φ he z).map (QuotientGroup.mk' (sp6KBar φ he z)) := by
  have hCX : sp6C₂ φ he z ≤ sp6X φ he z := le_normalizer
  have hKX : sp6K φ he z ≤ sp6X φ he z :=
    (map_subtype_le _).trans (centralizer_le_normalizer _)
  have hker : (sp6πX φ he z).ker = (sp6C₂ φ he z).subgroupOf (sp6X φ he z) :=
    QuotientGroup.ker_mk' _
  have hKn : ((sp6K φ he z).subgroupOf (sp6X φ he z)).Normal := ⟨fun n hn g => by
    rw [mem_subgroupOf] at hn ⊢
    exact hK₄ g g.2 n hn⟩
  have hKBn : (sp6KBar φ he z).Normal := hKn.map _ (QuotientGroup.mk'_surjective _)
  have hmapC : ((sp6C₂ φ he z).subgroupOf (sp6X φ he z)).map (sp6πX φ he z) = ⊥ :=
    (Subgroup.map_eq_bot_iff _).mpr hker.ge
  have hmapCK : ((sp6C₂ φ he z ⊔ sp6K φ he z).subgroupOf (sp6X φ he z)).map (sp6πX φ he z) =
      sp6KBar φ he z := by
    rw [subgroupOf_sup hCX hKX, Subgroup.map_sup, hmapC, bot_sup_eq]
    rfl
  have hKBodd : Nat.Coprime 2 (Nat.card (sp6KBar φ he z)) := by
    rw [Nat.coprime_two_left]
    refine Odd.of_dvd_nat ?_ (card_map_dvd _ _)
    rwa [Nat.card_congr (subgroupOfEquivOfLe hKX).toEquiv]
  have hKBR : sp6KBar φ he z ≤ sp6Ro φ he z := le_sSup ⟨hKBn, hKBodd⟩
  have hCK : (sp6C₂ φ he z).subgroupOf (sp6X φ he z) ≤
      (sp6C₂ φ he z ⊔ sp6K φ he z).subgroupOf (sp6X φ he z) :=
    subgroupOf_mono _ le_sup_left
  have hκC : (sp6C₂ φ he z).subgroupOf (sp6X φ he z) ≤ κ.ker := hκ₂ ▸ hCK
  have hκF : (QuotientGroup.lift _ κ hκC).ker = sp6KBar φ he z := by
    rw [QuotientGroup.ker_lift, hκ₂]
    exact hmapCK
  refine ⟨hKBR, (inferInstance : (sp6Ro φ he z).Normal).comap _, ?_,
    map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _, ?_,
    ⟨QuotientGroup.lift _ κ hκC, fun x c => hκ₁ x c, hκF, ?_⟩, hKBn, hκ₂ ▸ κ.normal_ker, ?_⟩
  · intro x hx
    have h1 : sp6πX φ he z x = 1 := MonoidHom.mem_ker.mp (by rw [hker]; exact hx)
    rw [mem_comap, h1]
    exact one_mem _
  · have h : ((sp6πX φ he z).comp ((sp6Ro φ he z).comap (sp6πX φ he z)).subtype).ker =
        (sp6πX φ he z).ker.subgroupOf ((sp6Ro φ he z).comap (sp6πX φ he z)) := rfl
    rw [h, hker]
  · have h : ((QuotientGroup.lift _ κ hκC).comp (sp6Ro φ he z).subtype).ker =
        (QuotientGroup.lift _ κ hκC).ker.subgroupOf (sp6Ro φ he z) := rfl
    rw [h, hκF]
  · intro _ _
    refine ⟨⟨(QuotientGroup.quotientQuotientEquivQuotient _ _ hCK).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hmapCK), fun x => ?_⟩,
      SteinbergBU.pPrimeCore_two_quotient_eq_map _ hKBR⟩
    rw [MulEquiv.trans_apply, QuotientGroup.quotientQuotientEquivQuotient_symm_mk]
    rfl

theorem sp6_lagrangian_layer_conclusion_of
    (hD : CFSG.LocalAnalysis.SteinbergBV.DirectSimpleInvolutionCentralizerLayerStmt) [Finite G]
    (hsimple : IsSimpleGroup G) (hnonab : ∃ x y : G, x * y ≠ y * x)
    (hKP : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    (hzC : z ∈ centralizer (L : Set G)) (hz : orderOf z = 2) (V₁ : Subgroup G)
    (hcard : Nat.card (sp6C₂ φ he z) = 4096) (hC₂ : IsElementaryAbelian 2 (sp6C₂ φ he z))
    (hN₂X : sp6N₂ φ e z ≤ sp6X φ he z) (hV₁X : V₁ ≤ sp6X φ he z)
    (hrel : (sp6C₂ φ he z).relIndex (V₁ ⊔ sp6C₂ φ he z) = 32) (hzX : z ∈ sp6X φ he z)
    (ψ : Multiplicative (ZMod 2) × GL (Fin 3) (ZMod 2) ≃*
      centralizer {(QuotientGroup.mk ⟨z, hzX⟩ : Sp6F φ he z)})
    (hψ : ∀ (s : ZMod 2) (g : GL (Fin 3) (ZMod 2))
      (h : z ^ s.val * leviHom φ he g ∈ sp6X φ he z),
      (ψ (Multiplicative.ofAdd s, g) : Sp6F φ he z) = QuotientGroup.mk ⟨_, h⟩)
    (hsyl : ∀ S : Sylow 2 (Sp6F φ he z), (QuotientGroup.mk ⟨z, hzX⟩ : Sp6F φ he z) ∈ S →
      ∃ y ∈ S, y * (QuotientGroup.mk ⟨z, hzX⟩ : Sp6F φ he z) ≠
        (QuotientGroup.mk ⟨z, hzX⟩ : Sp6F φ he z) * y)
    (hK₃ : Odd (Nat.card (sp6K φ he z)))
    (hK₄ : ∀ g ∈ sp6X φ he z, ∀ k ∈ sp6K φ he z, g * k * g⁻¹ ∈ sp6K φ he z)
    (κ : sp6X φ he z →* MulAut (sp6C₂ φ he z))
    (hκ₁ : ∀ (x : sp6X φ he z) (c : sp6C₂ φ he z),
      ((κ x c : sp6C₂ φ he z) : G) = x * c * (x : G)⁻¹)
    (hκ₂ : κ.ker = (sp6C₂ φ he z ⊔ sp6K φ he z).subgroupOf (sp6X φ he z)) :
    Sp6LagrangianLayerConclusion φ he z V₁ := by
  have hLX := sp6_leviHom_mem φ he z hN₂X hzC hz
  obtain ⟨ha2, hinj, hrange, hJC, hinf, hsup⟩ := sp6_centralizer_facts φ he z hz hLX hzX ψ hψ
  have hXne := sp6X_ne_top φ he z hsimple hnonab hcard hC₂.toIsMulCommutative
  have hKX := CFSG.QuasithinUnique.isKGroupCat_of_kProper hKP hXne
  have hKF : CFSG.SectionRank.IsKGroupCat (Sp6F φ he z) := hKX.quotient _
  let eJ : GL (Fin 3) (ZMod 2) ≃* sp6JL φ he z :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  have hJs : IsSimpleGroup (sp6JL φ he z) := by
    have := isSimpleGroup_GL_three_two
    exact eJ.symm.isSimpleGroup
  have hJn : ∃ x y : sp6JL φ he z, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := SteinbergBU.exists_mul_ne_mul_GL_three_two
    exact ⟨eJ x, eJ y, fun h => hxy (eJ.injective (by rw [map_mul, map_mul, h]))⟩
  have hJ4 : ∃ E : Subgroup (Sp6F φ he z), E ≤ sp6JL φ he z ∧
      CFSG.IsElementaryAbelian 2 E ∧ Nat.card E = 4 := by
    obtain ⟨E, hE, hEa, hEc⟩ := SteinbergBU.exists_four_subgroup_of_injective hinj
    exact ⟨E, hrange ▸ hE, hEa, hEc⟩
  have ha := sp6a_eq φ he z hzX
  have hsylA : ∀ S : Sylow 2 (Sp6F φ he z), sp6a φ he z ∈ S →
      ∃ s ∈ S, s * sp6a φ he z ≠ sp6a φ he z * s := by
    rw [ha]
    exact hsyl
  obtain ⟨⟨hR1, hR2, hR3⟩, ⟨hθ1, hθ2, hθ3⟩, ⟨hY1, hY2, hY3⟩, ⟨hc1, hc2, hc3⟩, hsylY,
      ⟨hst1, hst2, hst3, hst4⟩, ⟨hl1, hl2, -, hl4, hl5, hl6, hl7⟩, ⟨hq1, hq2⟩,
      ⟨hQ1, hQ2, hQ3, hQ4, hQ5, hQ6, hQ7⟩, -, -, hfit⟩ :=
    hD (Sp6F φ he z) hKF (sp6JL φ he z) hJs hJn hJ4 (sp6a φ he z) ha2 hJC hinf hsup hsylA
  have haC : sp6a φ he z ∈ centralizer {sp6a φ he z} := mem_centralizer_singleton_iff.mpr rfl
  have ha1 : sp6a φ he z ≠ 1 := fun h => by
    rw [h, orderOf_one] at ha2
    exact absurd ha2 (by norm_num)
  have haBar : orderOf (sp6aBar φ he z) = 2 := by
    apply orderOf_eq_prime
    · change sp6θ φ he z (sp6a φ he z) ^ 2 = 1
      rw [← map_pow, ← ha2, pow_orderOf_eq_one, map_one]
    · intro h
      exact ha1 (hθ2 haC (one_mem _) (h.trans (map_one _).symm))
  have hcardP : Nat.card (((V₁ ⊔ sp6C₂ φ he z).subgroupOf (sp6X φ he z)).map
      (sp6πX φ he z)) = 32 := by
    have hker : (sp6πX φ he z).ker = (sp6C₂ φ he z).subgroupOf (sp6X φ he z) :=
      QuotientGroup.ker_mk' _
    rw [← Subgroup.relIndex_ker, hker, relIndex_subgroupOf (sup_le hV₁X le_normalizer), hrel]
  have hP2 : IsPGroup 2 (((V₁ ⊔ sp6C₂ φ he z).subgroupOf (sp6X φ he z)).map (sp6πX φ he z)) :=
    IsPGroup.of_card (n := 5) (by rw [hcardP]; norm_num)
  have hcardY : Nat.card ((((V₁ ⊔ sp6C₂ φ he z).subgroupOf (sp6X φ he z)).map
      (sp6πX φ he z)).map (sp6θ φ he z)) = 32 := by
    have hinjP : Set.InjOn (sp6θ φ he z)
        (((V₁ ⊔ sp6C₂ φ he z).subgroupOf (sp6X φ he z)).map (sp6πX φ he z)) := hθ3 _ hP2
    rw [← hcardP, ← SetLike.coe_sort_coe, Subgroup.coe_map, Nat.card_image_of_injOn hinjP,
      SetLike.coe_sort_coe]
  have hθι : Function.Injective ((sp6θ φ he z).comp (sp6LeviHom φ he z hLX)) := by
    intro g g' h
    apply hinj
    exact hθ1 (by rw [SetLike.mem_coe, ← hrange]; exact ⟨g, rfl⟩)
      (by rw [SetLike.mem_coe, ← hrange]; exact ⟨g', rfl⟩) h
  have hθrange : ((sp6θ φ he z).comp (sp6LeviHom φ he z hLX)).range = sp6JLBar φ he z := by
    rw [MonoidHom.range_comp, hrange]
    rfl
  let κ' : GL (Fin 3) (ZMod 2) ≃* sp6JLBar φ he z :=
    (MonoidHom.ofInjective hθι).trans (MulEquiv.subgroupCongr hθrange)
  have hκ' : ∀ g, (κ' g : Sp6Y φ he z) = sp6θ φ he z (sp6Levi φ he z g) := fun g => by
    rw [sp6Levi_eq φ he z hLX]
    rfl
  have hxor : Xor (Sp6LayerSimple φ he z) (Sp6LayerTwoFactor φ he z) :=
    SteinbergBU.xor_layer_alternatives_of (fun g => sp6θ φ he z (sp6Levi φ he z g)) κ' hκ'
      hl5 hl6
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9⟩ := sp6_kernel_facts φ he z hK₃ hK₄ κ hκ₁ hκ₂
  exact ⟨hXne, hKX, ⟨hzX, ha⟩, ⟨hLX, sp6Levi_eq φ he z hLX⟩,
    ⟨sp6LeviHom φ he z hLX, fun g => (sp6Levi_eq φ he z hLX g).symm, hinj, hrange⟩, hKF, hY1,
    hY2, hR1, hR2, hR3, hθ1, hθ2, hθ3, ha2, hJC, hinf, hsup, haBar, hc1, hc2, hc3, hY3, hl1,
    hl2, hP2.map _, hcardY, hsylY, hst1, hst2, hst3, hst4, hl4, hl5, hxor, hl7, hq1, hq2, hQ1,
    hQ2, hQ3, hQ4, hQ5, hQ6, hQ7, hfit, k1, k2, k3, k4, k5, k6, k7, k8, k9⟩

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64
