module

public import CFSG.LocalAnalysis.EvenBN.G2.SeriesP
import CFSG.LocalAnalysis.EvenBN.GMSK.SL2Facts
import CFSG.LocalAnalysis.EvenBN.Common.SL2TorusThree
import CFSG.LocalAnalysis.EvenBN.Common.SL2TorusFour
import CFSG.LocalAnalysis.ComponentInitial.BasicFacts

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.LocalAnalysis.EvenBN.Common (CosetData)
open CFSG.LocalAnalysis.SymplecticFourStandard.BothTrivialClosure (BarM barMap barSub)
open CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialLayer (ExactClosure)
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase (centerMod centralizerMod IsQuotientIso)
open scoped commutatorElement Pointwise MatrixGroups

namespace SeriesN2Aux

section Abstract

open CFSG.LocalAnalysis.EvenBN.Common.RankOneLayerRadical
  (prod_eq_top_of_diag field_eq_top_of_frobenius)

theorem sl2_center_trivial {k : Type} [Field k] [Fintype k] [CharP k 2]
    (hk4 : 4 ≤ Fintype.card k) (a : SL(2, k)) (ha : ∀ x : SL(2, k), x * a = a * x) :
    a = 1 := by
  haveI : IsSimpleGroup SL(2, k) :=
    CFSG.LocalAnalysis.EvenBN.GMSK.sl2_isSimpleGroup CharTwo.two_eq_zero hk4
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center SL(2, k)) with h | h
  · have : a ∈ center SL(2, k) := mem_center_iff.2 ha
    rw [h] at this
    exact mem_bot.1 this
  · exfalso
    obtain ⟨x, y, hxy⟩ := CFSG.LocalAnalysis.EvenBN.GMSK.sl2_exists_mul_ne (K := k)
    have : x ∈ center SL(2, k) := h ▸ mem_top x
    exact hxy (mem_center_iff.1 this y).symm

theorem prod_normal_swap {k : Type} [Field k] [Fintype k] [CharP k 2]
    (hk4 : 4 ≤ Fintype.card k) {T : Subgroup (SL(2, k) × SL(2, k))}
    (hn : ∀ x ∈ T, ∀ g : SL(2, k) × SL(2, k), g * x * g⁻¹ ∈ T)
    (hs : ∀ x ∈ T, x.swap ∈ T) : T = ⊥ ∨ T = ⊤ := by
  haveI : IsSimpleGroup SL(2, k) :=
    CFSG.LocalAnalysis.EvenBN.GMSK.sl2_isSimpleGroup CharTwo.two_eq_zero hk4
  set H : Subgroup SL(2, k) := T.comap (MonoidHom.inl SL(2, k) SL(2, k)) with hH
  have hHn : H.Normal := ⟨fun a ha g => by
    have := hn (a, 1) ha (g, 1)
    show (g * a * g⁻¹, (1 : SL(2, k))) ∈ T
    simpa using this⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H with hb | ht
  · left
    have key : ∀ a b : SL(2, k), (a, b) ∈ T → a = 1 := by
      intro a b hab
      refine sl2_center_trivial hk4 a fun x => ?_
      have h1 := hn (a, b) hab (x, 1)
      have h2 := mul_mem h1 (inv_mem hab)
      have h3 : (x * a * x⁻¹ * a⁻¹, (1 : SL(2, k))) ∈ T := by simpa using h2
      have h4 : x * a * x⁻¹ * a⁻¹ ∈ H := h3
      rw [hb, mem_bot] at h4
      exact commutatorElement_eq_one_iff_mul_comm.1 (by rw [commutatorElement_def]; exact h4)
    rw [eq_bot_iff]
    rintro ⟨a, b⟩ hab
    have ha := key a b hab
    have hb' := key b a (hs _ hab)
    rw [mem_bot, ha, hb']
    rfl
  · right
    rw [eq_top_iff]
    rintro ⟨a, b⟩ -
    have h1 : (a, (1 : SL(2, k))) ∈ T := by
      have : a ∈ H := ht ▸ mem_top a
      exact this
    have h2 : ((1 : SL(2, k)), b) ∈ T := by
      have : b ∈ H := ht ▸ mem_top b
      have h' : (b, (1 : SL(2, k))) ∈ T := this
      exact hs _ h'
    have := mul_mem h1 h2
    simpa using this

theorem eq_bot_or_top_of_equiv {N H : Type*} [Group N] [Group H] (ψ : N ≃* H) {C : Subgroup N}
    (h : C.map ψ.toMonoidHom = ⊥ ∨ C.map ψ.toMonoidHom = ⊤) : C = ⊥ ∨ C = ⊤ := by
  rcases h with h | h
  · left
    rw [eq_bot_iff]
    intro c hc
    have : ψ c ∈ C.map ψ.toMonoidHom := ⟨c, hc, rfl⟩
    rw [h, mem_bot] at this
    exact mem_bot.2 (ψ.injective (by rw [this, map_one]))
  · right
    rw [eq_top_iff]
    intro c _
    have : ψ c ∈ C.map ψ.toMonoidHom := h ▸ mem_top _
    obtain ⟨c', hc', hcc⟩ := this
    exact (ψ.injective hcc) ▸ hc'

theorem eq_bot_or_eq_normalClosure {M : Type} [Group M] {A : Subgroup M} {k : Type} [Field k]
    [Finite k] [CharP k 2] {α : A ≃* SL(2, k)} {τ : M} {V : Subgroup M} {n : ℕ} (hn : 2 ≤ n)
    (hk : Nat.card k = 2 ^ n) (hex : ExactClosure A α τ V n) {C : Subgroup M}
    (hCN : C ≤ normalClosure (A : Set M))
    (hCn : ∀ c ∈ C, ∀ y ∈ normalClosure (A : Set M), y * c * y⁻¹ ∈ C)
    (hCτ : ∀ c ∈ C, τ⁻¹ * c * τ ∈ C) : C = ⊥ ∨ C = normalClosure (A : Set M) := by
  classical
  haveI := Fintype.ofFinite k
  have hk' : Fintype.card k = 2 ^ n := by rw [← Nat.card_eq_fintype_card]; exact hk
  have hk4 : 4 ≤ Fintype.card k :=
    hk' ▸ (Nat.pow_le_pow_right (by norm_num) hn : 2 ^ 2 ≤ 2 ^ n)
  obtain ⟨-, -, -, -, hxor⟩ := hex
  set N := normalClosure (A : Set M) with hN
  have hNnorm : ∀ x ∈ N, ∀ y : M, y * x * y⁻¹ ∈ N := fun x hx y =>
    (normalClosure_normal (s := (A : Set M))).conj_mem x hx y
  set C' : Subgroup N := C.subgroupOf N with hC'
  have hC'n : ∀ c ∈ C', ∀ y : N, y * c * y⁻¹ ∈ C' := fun c hc y => by
    rw [mem_subgroupOf] at hc ⊢
    exact hCn _ hc _ y.2
  have fin : C' = ⊥ ∨ C' = ⊤ → C = ⊥ ∨ C = N := by
    rintro (h | h)
    · left
      rw [eq_bot_iff]
      intro c hc
      have : (⟨c, hCN hc⟩ : N) ∈ C' := mem_subgroupOf.2 hc
      rw [h, mem_bot] at this
      exact mem_bot.2 (congrArg Subtype.val this)
    · right
      refine le_antisymm hCN fun c hc => ?_
      have : (⟨c, hc⟩ : N) ∈ C' := h ▸ mem_top _
      exact mem_subgroupOf.1 this
  refine fin ?_
  rcases hxor with ⟨⟨ψ, -, hψτ⟩, -⟩ | ⟨⟨k₂, hF, hFin, hk₂, ψ, -, -⟩, -⟩
  · refine eq_bot_or_top_of_equiv ψ (prod_normal_swap hk4 ?_ ?_)
    · rintro _ ⟨c, hc, rfl⟩ g
      obtain ⟨y, rfl⟩ := ψ.surjective g
      exact ⟨y * c * y⁻¹, hC'n c hc y, by simp⟩
    · rintro _ ⟨c, hc, rfl⟩
      have hc' : τ⁻¹ * (c : M) * τ ∈ N := by
        simpa using hNnorm (c : M) c.2 τ⁻¹
      have hcC : τ⁻¹ * (c : M) * τ ∈ C := hCτ _ (mem_subgroupOf.1 hc)
      refine ⟨⟨τ⁻¹ * (c : M) * τ, hc'⟩, mem_subgroupOf.2 hcC, ?_⟩
      exact (hψτ c ⟨τ⁻¹ * (c : M) * τ, hc'⟩ rfl)
  · have hk₂' : Fintype.card k₂ = 2 ^ (2 * n) := by rw [hk₂, ← pow_mul, mul_comm]
    have h2 : (2 : k₂) = 0 := CFSG.LocalAnalysis.EvenBN.GMSK.two_eq_zero_of_card (by omega) hk₂'
    have h4 : 4 ≤ Fintype.card k₂ := by
      rw [hk₂']
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
    haveI : IsSimpleGroup SL(2, k₂) :=
      CFSG.LocalAnalysis.EvenBN.GMSK.sl2_isSimpleGroup h2 h4
    have hnorm : (C'.map ψ.toMonoidHom).Normal := ⟨by
      rintro _ ⟨c, hc, rfl⟩ g
      obtain ⟨y, rfl⟩ := ψ.surjective g
      exact ⟨y * c * y⁻¹, hC'n c hc y, by simp⟩⟩
    exact eq_bot_or_top_of_equiv ψ (IsSimpleGroup.eq_bot_or_eq_top_of_normal _)

theorem sup_eq_of_exactClosure {M : Type} [Group M] [Finite M] {A : Subgroup M} {k : Type}
    [Field k] [Finite k] [CharP k 2] {α : A ≃* SL(2, k)} {τ : M} {V : Subgroup M} {n : ℕ}
    (hn : 2 ≤ n) (hcard : Nat.card k = 2 ^ n) (hτ : τ ∈ normalizer (V : Set M))
    (hex : ExactClosure A α τ V n) : V ⊔ A = normalClosure (A : Set M) := by
  classical
  have : Fintype k := Fintype.ofFinite k
  have hk : Fintype.card k = 2 ^ n := by rw [← Nat.card_eq_fintype_card]; exact hcard
  have hAN : A ≤ normalClosure (A : Set M) := fun a ha => subset_normalClosure ha
  set N := normalClosure (A : Set M) with hN
  obtain ⟨-, -, hVN, ⟨P, hP⟩, hxor⟩ := hex
  refine le_antisymm (sup_le hVN hAN) ?_
  set T : Subgroup N := (V ⊔ A).subgroupOf N with hT
  have hTA : ∀ x : N, (x : M) ∈ A → x ∈ T := fun x hx => mem_subgroupOf.2 (mem_sup_right hx)
  have hxV : ∀ x ∈ (P : Subgroup N), (x : M) ∈ V := by
    intro x hx
    rw [← hP]
    exact ⟨x, hx, rfl⟩
  have hPT : ∀ x ∈ (P : Subgroup N), x ∈ T := fun x hx => mem_subgroupOf.2 (mem_sup_left (hxV x hx))
  suffices hTtop : T = ⊤ by
    intro x hx
    have : (⟨x, hx⟩ : N) ∈ T := hTtop ▸ mem_top _
    exact mem_subgroupOf.1 this
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hxor with ⟨hPr, -⟩ | ⟨hF, -⟩
  ·
    obtain ⟨ψ, hψA, -⟩ := hPr
    have hdiag : ∀ g : SL(2, k), (g, g) ∈ T.map ψ.toMonoidHom := by
      intro g
      refine ⟨⟨((α.symm g : A) : M), hAN (α.symm g).2⟩, hTA _ (α.symm g).2, ?_⟩
      have := hψA (α.symm g) ⟨((α.symm g : A) : M), hAN (α.symm g).2⟩ rfl
      rw [MulEquiv.apply_symm_apply] at this
      exact this
    have hVcard : Nat.card ((P : Subgroup N).map ψ.toMonoidHom) = (2 ^ n) ^ 2 := by
      rw [Subgroup.card_map_of_injective ψ.injective, Common.card_sylow_two_eq_prod ψ P,
        hcard]
    have htop := prod_eq_top_of_diag hn hk hdiag
      ((P.isPGroup').map ψ.toMonoidHom) hVcard
      (Subgroup.map_mono (fun x hx => hPT x hx))
    refine eq_top_iff.2 fun x _ => ?_
    have hx : ψ x ∈ T.map ψ.toMonoidHom := htop ▸ mem_top _
    obtain ⟨y, hy, hyx⟩ := hx
    exact (ψ.injective hyx) ▸ hy
  ·
    obtain ⟨k₂, hk₂F, hk₂Fin, hk₂, ψ, hψτ, hψA⟩ := hF
    have hk₂' : Nat.card k₂ = 2 ^ (2 * n) := by
      rw [Nat.card_eq_fintype_card, hk₂, ← pow_mul, mul_comm]
    have : CharP k₂ 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by have := hn; omega) hk₂'
    have hVcard : Nat.card ((P : Subgroup N).map ψ.toMonoidHom) = Nat.card k₂ := by
      rw [Subgroup.card_map_of_injective ψ.injective, Common.card_sylow_two_eq ψ P]
    have hσ : ∀ v ∈ (P : Subgroup N).map ψ.toMonoidHom,
        Matrix.SpecialLinearGroup.map (iterateFrobenius k₂ 2 n) v ∈
          (P : Subgroup N).map ψ.toMonoidHom := by
      rintro _ ⟨x, hxP, rfl⟩
      have hyN : τ⁻¹ * (x : M) * τ ∈ N := by
        have := (normalClosure_normal (s := (A : Set M))).conj_mem (x : M) x.2 τ⁻¹
        simpa using this
      have hyV : τ⁻¹ * (x : M) * τ ∈ V := by
        have := (mem_normalizer_iff.1 (inv_mem hτ) (x : M)).1 (hxV x hxP)
        simpa using this
      have hyP : (⟨τ⁻¹ * (x : M) * τ, hyN⟩ : N) ∈ (P : Subgroup N) := by
        rw [← hP] at hyV
        obtain ⟨y', hy'P, hy'⟩ := hyV
        have : y' = ⟨τ⁻¹ * (x : M) * τ, hyN⟩ := Subtype.ext hy'
        exact this ▸ hy'P
      refine ⟨_, hyP, ?_⟩
      have hσψ := hψτ x ⟨τ⁻¹ * (x : M) * τ, hyN⟩ rfl
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
      exact hσψ
    have htop := field_eq_top_of_frobenius hk₂ (T := T.map ψ.toMonoidHom)
      (V := (P : Subgroup N).map ψ.toMonoidHom)
      (fun g hg => by
        obtain ⟨x, hx, rfl⟩ := (hψA g).2 hg
        exact ⟨x, hTA x hx, rfl⟩)
      hVcard (Subgroup.map_mono (fun x hx => hPT x hx)) hσ
    refine eq_top_iff.2 fun x _ => ?_
    have hx : ψ x ∈ T.map ψ.toMonoidHom := htop ▸ mem_top _
    obtain ⟨y, hy, hyx⟩ := hx
    exact (ψ.injective hyx) ▸ hy

end Abstract

section Generic

variable {G : Type*} [Group G]

theorem mem_normalizer_commutator_self {H : Subgroup G} {g : G}
    (hg : g ∈ normalizer (H : Set G)) : g ∈ normalizer (⁅H, H⁆ : Subgroup G) := by
  have key : ∀ g ∈ normalizer (H : Set G), ∀ x ∈ ⁅H, H⁆, g * x * g⁻¹ ∈ ⁅H, H⁆ := by
    intro g hg x hx
    have hle : ⁅H, H⁆ ≤ (⁅H, H⁆).comap (MulAut.conj g).toMonoidHom := by
      refine commutator_le.2 fun a ha b hb => ?_
      simp only [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [conjugate_commutatorElement]
      exact commutator_mem_commutator ((mem_normalizer_iff.1 hg a).1 ha)
        ((mem_normalizer_iff.1 hg b).1 hb)
    exact hle hx
  rw [mem_normalizer_iff]
  intro x
  refine ⟨key g hg x, fun hx => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hx
  rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at this

theorem conj_mem_centralizer_of_mem_normalizer {Y : Subgroup G} {n z : G}
    (hn : n ∈ normalizer (Y : Set G)) (hz : z ∈ centralizer (Y : Set G)) :
    n * z * n⁻¹ ∈ centralizer (Y : Set G) := by
  rw [mem_centralizer_iff]
  intro y hy
  have hy' : n⁻¹ * y * n ∈ Y := by
    have := (mem_normalizer_iff.1 (inv_mem hn) y).1 hy
    simpa using this
  have e := mem_centralizer_iff.1 hz _ hy'
  calc y * (n * z * n⁻¹) = n * ((n⁻¹ * y * n) * z) * n⁻¹ := by group
    _ = n * (z * (n⁻¹ * y * n)) * n⁻¹ := by rw [e]
    _ = n * z * n⁻¹ * y := by group

end Generic

section Local

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem K₂_le_normalizer (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaK₂ d ≤ normalizer (yamadaM₆ d t : Set G) :=
  (commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb) :
      yamadaK₂ d ≤ L ⊓ normalizer (d.Y : Set G)).trans
    (h.normalizer_L_le_yamadaD₇_M₆ hW d hK hQ).2

theorem N₂_le_normalizer_M₆ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaN₂ d t ≤ normalizer (yamadaM₆ d t : Set G) :=
  yamadaN₂_le_normalizer d t (K₂_le_normalizer hW h d hK hQ)

theorem conj_mem_N₂ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) {g n : G}
    (hg : g ∈ normalizer (yamadaM₆ d t : Set G)) (hn : n ∈ yamadaN₂ d t) :
    g * n * g⁻¹ ∈ yamadaN₂ d t :=
  (Common.RankOneLayerRadical.normal_subgroupOf_normalClosureInNormalizer
    (K₂_le_normalizer hW h d hK hQ)).conj_mem ⟨n, N₂_le_normalizer_M₆ hW h d hK hQ hn⟩
    (mem_subgroupOf.2 hn) ⟨g, hg⟩

theorem P_le_normalizer_M₆ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaP d t ≤ normalizer (yamadaM₆ d t : Set G) := by
  obtain ⟨-, hPR₈, -, -, -, -, -⟩ := h.yamadaP_facts hW d hK hQ
  obtain ⟨-, ⟨-, hR₈M⟩⟩ := h.yamada_5_56 hW d hK hQ
  exact hPR₈.trans hR₈M

theorem t_mem_normalizer_M₆ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    t ∈ normalizer (yamadaM₆ d t : Set G) :=
  ((h.yamada_5_44_1 hW d hK hQ).1).2.1

theorem normalizer_M₆_le_normalizer_Y₂ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    normalizer (yamadaM₆ d t : Set G) ≤ normalizer (yamadaY₂ d t : Set G) := by
  intro g hg
  have := mem_normalizer_commutator_self hg
  rwa [(h.yamada_5_55_1 hW d hK hQ).2.2] at this

theorem P_le_N₂ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d)
    {α : ↥(yamadaBarK₂ d t) ≃* SL(2, K)}
    (hex : ExactClosure (yamadaBarK₂ d t) α (yamadaT₂ d t) (yamadaBarP₂ d t) f) :
    yamadaP d t ≤ yamadaN₂ d t := by
  intro p hp
  have hPN := P_le_normalizer_M₆ hW h d hK hQ
  have h1 : barMap (yamadaM₆ d t) ⟨p, hPN hp⟩ ∈ yamadaBarP₂ d t :=
    ⟨⟨p, hPN hp⟩, mem_subgroupOf.2 hp, rfl⟩
  have h2 := hex.2.2.1 h1
  rw [← barSub_yamadaN₂ d t (K₂_le_normalizer hW h d hK hQ)] at h2
  exact (CFSG.LocalAnalysis.SymplecticFourStandard.BothTrivialClosure.mem_barSub_iff
    (yamadaM₆_le_yamadaN₂ d t) ⟨p, hPN hp⟩).1 h2

theorem eq_M₆_or_eq_N₂ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d)
    {α : ↥(yamadaBarK₂ d t) ≃* SL(2, K)}
    (hex : ExactClosure (yamadaBarK₂ d t) α (yamadaT₂ d t) (yamadaBarP₂ d t) f)
    {Z : Subgroup G} (hMZ : yamadaM₆ d t ≤ Z) (hZN : Z ≤ yamadaN₂ d t)
    (hZn : ∀ n ∈ yamadaN₂ d t, ∀ z ∈ Z, n * z * n⁻¹ ∈ Z)
    (hZt : ∀ z ∈ Z, t * z * t⁻¹ ∈ Z) : Z = yamadaM₆ d t ∨ Z = yamadaN₂ d t := by
  have hKN := K₂_le_normalizer hW h d hK hQ
  have hN₂ := N₂_le_normalizer_M₆ hW h d hK hQ
  have ht := t_mem_normalizer_M₆ hW h d hK hQ
  have hbar := barSub_yamadaN₂ d t hKN
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_mul_t
  have key := eq_bot_or_eq_normalClosure (C := barSub (yamadaM₆ d t) Z)
    h.two_le hK hex ?_ ?_ ?_
  · rcases key with hb | hb
    · left
      refine le_antisymm (fun z hz => ?_) hMZ
      have : barMap (yamadaM₆ d t) ⟨z, hN₂ (hZN hz)⟩ ∈ barSub (yamadaM₆ d t) Z :=
        ⟨⟨z, hN₂ (hZN hz)⟩, mem_subgroupOf.2 hz, rfl⟩
      rw [hb, Subgroup.mem_bot] at this
      exact CFSG.LocalAnalysis.SymplecticFourStandard.BothTrivialClosure.barMap_eq_one_iff.1 this
    · right
      refine le_antisymm hZN (fun n hn => ?_)
      have h1 : barMap (yamadaM₆ d t) ⟨n, hN₂ hn⟩ ∈ barSub (yamadaM₆ d t) (yamadaN₂ d t) :=
        ⟨⟨n, hN₂ hn⟩, mem_subgroupOf.2 hn, rfl⟩
      rw [hbar, ← hb] at h1
      exact (CFSG.LocalAnalysis.SymplecticFourStandard.BothTrivialClosure.mem_barSub_iff hMZ
        ⟨n, hN₂ hn⟩).1 h1
  · rw [← hbar]
    exact Subgroup.map_mono fun x hx => mem_subgroupOf.2 (hZN (mem_subgroupOf.1 hx))
  · intro c hc y hy
    rw [← hbar] at hy
    obtain ⟨z, hz, rfl⟩ := hc
    obtain ⟨n, hn, rfl⟩ := hy
    refine ⟨n * z * n⁻¹, mem_subgroupOf.2 (hZn _ (mem_subgroupOf.1 hn) _ (mem_subgroupOf.1 hz)),
      by simp⟩
  · intro c hc
    obtain ⟨z, hz, rfl⟩ := hc
    rw [yamadaT₂_eq d ht]
    refine ⟨⟨t, ht⟩⁻¹ * z * ⟨t, ht⟩, mem_subgroupOf.2 ?_, by simp⟩
    have := hZt _ (mem_subgroupOf.1 hz)
    simpa [htinv] using this

theorem mem_U₁_iff (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) {x : G} :
    x ∈ yamadaU₁ d t ↔ x ∈ yamadaP d t ∧ ∀ g ∈ yamadaP d t, x * g * x⁻¹ * g⁻¹ = 1 := by
  obtain ⟨hZ1, -, -⟩ := h.yamada_5_57_1 hW d hK hQ
  have hZ0 : (Subgroup.upperCentralSeries (yamadaP d t) 0).map (yamadaP d t).subtype = ⊥ := by
    rw [Subgroup.upperCentralSeries_zero, Subgroup.map_bot]
  rw [mem_of_map_upperCentralSeries_succ (n := 0) hZ0 hZ1]
  simp only [Subgroup.mem_bot]

theorem mem_Y₂_iff (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) {x : G} :
    x ∈ yamadaY₂ d t ↔
      x ∈ yamadaP d t ∧ ∀ g ∈ yamadaP d t, x * g * x⁻¹ * g⁻¹ ∈ yamadaU₁ d t := by
  obtain ⟨hZ1, hZ2, -⟩ := h.yamada_5_57_1 hW d hK hQ
  exact mem_of_map_upperCentralSeries_succ (n := 1) hZ1 hZ2

theorem mem_F₅_iff (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) {x : G} :
    x ∈ yamadaF₅ d t ↔
      x ∈ yamadaP d t ∧ ∀ g ∈ yamadaP d t, x * g * x⁻¹ * g⁻¹ ∈ yamadaY₂ d t := by
  obtain ⟨-, hZ2, hZ3⟩ := h.yamada_5_57_1 hW d hK hQ
  exact mem_of_map_upperCentralSeries_succ (n := 2) hZ2 hZ3

theorem Y₂_le_P (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaY₂ d t ≤ yamadaP d t :=
  (h.yamadaY₂_le_yamadaM₆ hW d hK hQ).trans (h.yamadaM₆_le_yamadaP hW d hK hQ)

theorem N₂_inf_centralizer_Y₂ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d)
    {α : ↥(yamadaBarK₂ d t) ≃* SL(2, K)}
    (hex : ExactClosure (yamadaBarK₂ d t) α (yamadaT₂ d t) (yamadaBarP₂ d t) f) :
    yamadaN₂ d t ⊓ centralizer (yamadaY₂ d t : Set G) = yamadaM₆ d t := by
  have hN₂ := N₂_le_normalizer_M₆ hW h d hK hQ
  have hMY := normalizer_M₆_le_normalizer_Y₂ hW h d hK hQ
  have ht := t_mem_normalizer_M₆ hW h d hK hQ
  have hMC := Setup.Q44.M₆_le_centralizer_Y₂ hW h d hK hQ
  have hMN := yamadaM₆_le_yamadaN₂ d t
  have hD := hQ.doubling
  rcases eq_M₆_or_eq_N₂ hW h d hK hQ hex
    (Z := yamadaN₂ d t ⊓ centralizer (yamadaY₂ d t : Set G)) (le_inf hMN hMC) inf_le_left
    (fun n hn z hz => ⟨conj_mem_N₂ hW h d hK hQ (hN₂ hn) hz.1,
      conj_mem_centralizer_of_mem_normalizer (hMY (hN₂ hn)) hz.2⟩)
    (fun z hz => ⟨conj_mem_N₂ hW h d hK hQ ht hz.1,
      conj_mem_centralizer_of_mem_normalizer (hMY ht) hz.2⟩) with hZ | hZ
  · exact hZ
  · exfalso
    have hNC : ∀ x ∈ yamadaN₂ d t, x ∈ centralizer (yamadaY₂ d t : Set G) := fun x hx => by
      have : x ∈ yamadaN₂ d t ⊓ centralizer (yamadaY₂ d t : Set G) := by rw [hZ]; exact hx
      exact this.2
    have hPC : ∀ g ∈ yamadaP d t, g ∈ centralizer (yamadaY₂ d t : Set G) := fun g hg =>
      hNC g (P_le_N₂ hW h d hK hQ hex hg)
    have hYU : yamadaY₂ d t ≤ yamadaU₁ d t := fun y hy =>
      (mem_U₁_iff hW h d hK hQ).2 ⟨Y₂_le_P hW h d hK hQ hy, fun g hg => by
        rw [← commutatorElement_def]
        exact commutatorElement_eq_one_iff_mul_comm.2 (mem_centralizer_iff.1 (hPC g hg) y hy)⟩
    have h1 := Subgroup.card_le_of_le hYU
    rw [h.card_yamadaY₂ d hK hD, hD.card_eq] at h1
    have : Nat.card K ^ 2 < Nat.card K ^ 4 := Nat.pow_lt_pow_right hQ.one_lt (by norm_num)
    omega

theorem normalizer_P_le_normalizer_Y₂ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    normalizer (yamadaP d t : Set G) ≤ normalizer (yamadaY₂ d t : Set G) := by
  obtain ⟨-, hZ2, -⟩ := h.yamada_5_57_1 hW d hK hQ
  have hsub : (yamadaY₂ d t).subgroupOf (yamadaP d t) =
      Subgroup.upperCentralSeries (yamadaP d t) 2 := by
    rw [← hZ2]
    exact Subgroup.comap_map_eq_self_of_injective (yamadaP d t).subtype_injective _
  haveI : ((yamadaY₂ d t).subgroupOf (yamadaP d t)).Characteristic := by
    rw [hsub]
    infer_instance
  exact normalizer_le_normalizer_of_characteristic_subgroupOf (Y₂_le_P hW h d hK hQ) inferInstance

theorem P_inf_centralizer_Y₂ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d)
    {α : ↥(yamadaBarK₂ d t) ≃* SL(2, K)}
    (hex : ExactClosure (yamadaBarK₂ d t) α (yamadaT₂ d t) (yamadaBarP₂ d t) f) :
    yamadaP d t ⊓ centralizer (yamadaY₂ d t : Set G) = yamadaM₆ d t ∧
      normalizer (yamadaP d t : Set G) ≤ normalizer (yamadaM₆ d t : Set G) := by
  have hC := N₂_inf_centralizer_Y₂ hW h d hK hQ hex
  have hM : yamadaP d t ⊓ centralizer (yamadaY₂ d t : Set G) = yamadaM₆ d t := by
    refine le_antisymm (fun x hx => ?_) (le_inf (h.yamadaM₆_le_yamadaP hW d hK hQ)
      (Setup.Q44.M₆_le_centralizer_Y₂ hW h d hK hQ))
    rw [← hC]
    exact ⟨P_le_N₂ hW h d hK hQ hex hx.1, hx.2⟩
  refine ⟨hM, fun g hg => ?_⟩
  rw [← hM]
  exact mem_normalizer_inf_centralizer_of_mem hg (normalizer_P_le_normalizer_Y₂ hW h d hK hQ hg)

theorem t_mem_normalizer_P (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    t ∈ normalizer (yamadaP d t : Set G) := by
  obtain ⟨⟨-, htNP, -⟩, -, -⟩ := h.yamada_5_51 hW d hK hQ
  exact htNP

theorem P_inf_map_wb (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d)
    {α : ↥(yamadaBarK₂ d t) ≃* SL(2, K)}
    (hex : ExactClosure (yamadaBarK₂ d t) α (yamadaT₂ d t) (yamadaBarP₂ d t) f) :
    yamadaP d t ⊓ (yamadaP d t).map (MulAut.conj d.wb).toMonoidHom = yamadaM₆ d t := by
  obtain ⟨hCY, -⟩ := P_inf_centralizer_Y₂ hW h d hK hQ hex
  have hD := hQ.doubling
  have hwY := Setup.Q44.wb_mem_normalizer_Y₂ h d hK hD
  have hMw : (yamadaM₆ d t).map (MulAut.conj d.wb).toMonoidHom = yamadaM₆ d t :=
    Setup.Q44.map_wb_M₆ h d hK
  refine le_antisymm (fun x hx => ?_) (le_inf (h.yamadaM₆_le_yamadaP hW d hK hQ)
    (hMw.ge.trans (Subgroup.map_mono (h.yamadaM₆_le_yamadaP hW d hK hQ))))
  obtain ⟨hxP, hxPs⟩ := Subgroup.mem_inf.1 hx
  rw [mem_map_conj_iff] at hxPs
  rw [← hCY]
  refine ⟨hxP, mem_centralizer_iff.2 fun y hy => ?_⟩
  have h1 : y * x * y⁻¹ * x⁻¹ ∈ yamadaU₁ d t := ((mem_Y₂_iff hW h d hK hQ).1 hy).2 x hxP
  have hy' : d.wb⁻¹ * y * d.wb ∈ yamadaY₂ d t := Setup.Q44.inv_conj_mem hwY hy
  have h2 : d.wb⁻¹ * (y * x * y⁻¹ * x⁻¹) * d.wb ∈ yamadaU₁ d t := by
    have := ((mem_Y₂_iff hW h d hK hQ).1 hy').2 _ hxPs
    have e : (d.wb⁻¹ * y * d.wb) * (d.wb⁻¹ * x * d.wb) * (d.wb⁻¹ * y * d.wb)⁻¹ *
        (d.wb⁻¹ * x * d.wb)⁻¹ = d.wb⁻¹ * (y * x * y⁻¹ * x⁻¹) * d.wb := by group
    rwa [e] at this
  have h3 : y * x * y⁻¹ * x⁻¹ ∈ yamadaU₁ d t ⊓ (yamadaU₁ d t).map (MulAut.conj d.wb).toMonoidHom :=
    Subgroup.mem_inf.2 ⟨h1, mem_map_conj_iff.2 h2⟩
  rw [h.yamadaU₁_inf_map_wb d hK hD, Subgroup.mem_bot] at h3
  exact (commutatorElement_eq_one_iff_mul_comm.1 (by rw [commutatorElement_def]; exact h3))

theorem K₂_le_P_sup (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaK₂ d ≤ yamadaP d t ⊔ (yamadaP d t).map (MulAut.conj d.wb).toMonoidHom := by
  have hK4 : 4 ≤ Nat.card K := hQ.four_le
  have hMP : d.M ≤ yamadaP d t :=
    (h.M_le_yamadaM₆ hW d hK hQ).trans (h.yamadaM₆_le_yamadaP hW d hK hQ)
  have hSP : d.S ≤ yamadaP d t := by
    obtain ⟨-, -, -, -, hS₆P, -, -⟩ := h.yamadaP_facts hW d hK hQ
    exact (S_le_yamadaS₆ d t).trans hS₆P
  have hSb : d.rootGroup g2a ≤ d.S := by
    obtain ⟨-, -, -, -, haD, -, -, -, -⟩ := d.yamada_defs
    exact (le_sup_left.trans haD.le).trans d.inclusions.2.2.2.2.2.2.2.1
  rw [yamadaK₂_eq d hK4]
  refine sup_le (hMP.trans le_sup_left) ?_
  have hpre : Model.leviB K ≤ d.preimage
      ((yamadaP d t ⊔ (yamadaP d t).map (MulAut.conj d.wb).toMonoidHom) ⊓ L) := by
    rw [Model.leviB, g2RankOne_a_eq]
    refine (Subgroup.closure_le _).2 ?_
    have hx0 : ∀ c : K, d.emb ⟨pinnedX .G2 K g2a c, pinnedX_mem_adjointGroup g2a c⟩ ∈
        d.image (rootSubgroup .G2 K g2a) := fun c =>
      d.emb_mem_image (mem_rootSubgroup.2 ⟨c, rfl⟩)
    have hx : ∀ c : K, d.emb ⟨pinnedX .G2 K g2a c, pinnedX_mem_adjointGroup g2a c⟩ ∈
        yamadaP d t := fun c => hSP (hSb (hx0 c))
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact d.mem_preimage.2 (Subgroup.mem_inf.2 ⟨mem_sup_left (hx c), d.emb_mem _⟩)
    · refine d.mem_preimage (g := ⟨pinnedX .G2 K g2na c, pinnedX_mem_adjointGroup g2na c⟩) |>.2
        (Subgroup.mem_inf.2 ⟨?_, d.emb_mem _⟩)
      have h1 := (d.yamada_3_7_G hK4).2.2.2.2.2 (s := g2a) isRoot_g2a c
      have h2 : d.emb ⟨pinnedX .G2 K g2na c, pinnedX_mem_adjointGroup g2na c⟩ =
          d.emb ⟨pinnedX .G2 K (reflect .G2 g2ia g2a) c, pinnedX_mem_adjointGroup _ _⟩ :=
        congrArg d.emb (Subtype.ext (by rw [reflect_a_a]))
      have h3 : d.emb ⟨pinnedX .G2 K g2na c, pinnedX_mem_adjointGroup g2na c⟩ =
          d.wb * d.emb ⟨pinnedX .G2 K g2a c, pinnedX_mem_adjointGroup g2a c⟩ * d.wb⁻¹ := by
        rw [h2, ← h1, Setup.Q44.wb_inv h d hK]
      rw [h3]
      exact mem_sup_right ⟨_, hx c, rfl⟩
  calc d.leviB = d.image (Model.leviB K) := rfl
    _ ≤ d.image (d.preimage
        ((yamadaP d t ⊔ (yamadaP d t).map (MulAut.conj d.wb).toMonoidHom) ⊓ L)) :=
        d.image_mono hpre
    _ = (yamadaP d t ⊔ (yamadaP d t).map (MulAut.conj d.wb).toMonoidHom) ⊓ L :=
        d.image_preimage inf_le_right
    _ ≤ _ := inf_le_left

theorem T₂_mem_normalizer_barP₂ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaT₂ d t ∈ normalizer (yamadaBarP₂ d t : Set (BarM (yamadaM₆ d t))) := by
  have htN := t_mem_normalizer_M₆ hW h d hK hQ
  have htP := t_mem_normalizer_P hW h d hK hQ
  have hDP := h.yamadaM₆_le_yamadaP hW d hK hQ
  rw [yamadaT₂_eq d htN, mem_normalizer_iff]
  intro y
  obtain ⟨m, hm⟩ := QuotientGroup.mk'_surjective ((yamadaM₆ d t).subgroupOf
    (normalizer (yamadaM₆ d t : Set G))) y
  have hy : y = barMap (yamadaM₆ d t) m := hm.symm
  have e : barMap (yamadaM₆ d t) ⟨t, htN⟩ * y * (barMap (yamadaM₆ d t) ⟨t, htN⟩)⁻¹ =
      barMap (yamadaM₆ d t) (⟨t, htN⟩ * m * ⟨t, htN⟩⁻¹) := by
    rw [hy, map_mul, map_mul, map_inv]
  rw [e, hy]
  change barMap (yamadaM₆ d t) m ∈ barSub (yamadaM₆ d t) (yamadaP d t) ↔
    barMap (yamadaM₆ d t) (⟨t, htN⟩ * m * ⟨t, htN⟩⁻¹) ∈ barSub (yamadaM₆ d t) (yamadaP d t)
  rw [CFSG.LocalAnalysis.SymplecticFourStandard.BothTrivialClosure.mem_barSub_iff hDP,
    CFSG.LocalAnalysis.SymplecticFourStandard.BothTrivialClosure.mem_barSub_iff hDP]
  exact mem_normalizer_iff.1 htP (m : G)

theorem N₂_eq_P_sup (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d)
    {α : ↥(yamadaBarK₂ d t) ≃* SL(2, K)}
    (hex : ExactClosure (yamadaBarK₂ d t) α (yamadaT₂ d t) (yamadaBarP₂ d t) f) :
    yamadaN₂ d t = yamadaP d t ⊔ (yamadaP d t).map (MulAut.conj d.wb).toMonoidHom := by
  have hKN := K₂_le_normalizer hW h d hK hQ
  have hwN := h.wb_mem_normalizer_yamadaM₆ d hK
  have hMP := h.yamadaM₆_le_yamadaP hW d hK hQ
  have hsup := sup_eq_of_exactClosure h.two_le hK (T₂_mem_normalizer_barP₂ hW h d hK hQ) hex
  apply le_antisymm
  · intro n hn
    have hnN : n ∈ normalizer (yamadaM₆ d t : Set G) := N₂_le_normalizer_M₆ hW h d hK hQ hn
    have h1 : barMap (yamadaM₆ d t) ⟨n, hnN⟩ ∈
        normalClosure (yamadaBarK₂ d t : Set (BarM (yamadaM₆ d t))) := by
      rw [← barSub_yamadaN₂ d t hKN]
      exact ⟨⟨n, hnN⟩, mem_subgroupOf.2 hn, rfl⟩
    rw [← hsup] at h1
    have hMH : yamadaM₆ d t ≤
        yamadaP d t ⊔ (yamadaP d t).map (MulAut.conj d.wb).toMonoidHom := hMP.trans le_sup_left
    have hle : yamadaBarP₂ d t ⊔ yamadaBarK₂ d t ≤ barSub (yamadaM₆ d t)
        (yamadaP d t ⊔ (yamadaP d t).map (MulAut.conj d.wb).toMonoidHom) :=
      sup_le (Subgroup.map_mono fun x hx => mem_subgroupOf.2 (mem_sup_left (mem_subgroupOf.1 hx)))
        (Subgroup.map_mono fun x hx =>
          mem_subgroupOf.2 (K₂_le_P_sup hW h d hK hQ (mem_subgroupOf.1 hx)))
    exact (CFSG.LocalAnalysis.SymplecticFourStandard.BothTrivialClosure.mem_barSub_iff hMH
      ⟨n, hnN⟩).1 (hle h1)
  · refine sup_le (P_le_N₂ hW h d hK hQ hex) ?_
    rintro _ ⟨p, hp, rfl⟩
    exact conj_mem_N₂ hW h d hK hQ hwN (P_le_N₂ hW h d hK hQ hex hp)

end Local

end SeriesN2Aux

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Local

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]


theorem yamadaP_inf_centralizer_yamadaY₂ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d)
    {α : ↥(yamadaBarK₂ d t) ≃* SL(2, K)}
    (hex : ExactClosure (yamadaBarK₂ d t) α (yamadaT₂ d t) (yamadaBarP₂ d t) f) :
    yamadaP d t ⊓ centralizer (yamadaY₂ d t : Set G) = yamadaM₆ d t ∧
      normalizer (yamadaP d t : Set G) ≤ normalizer (yamadaM₆ d t : Set G) :=
  SeriesN2Aux.P_inf_centralizer_Y₂ hW h d hK hQ hex

theorem yamadaP_inf_map_conj_wb (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d)
    (hsyl : IsSylowOf 2 (yamadaP d t) (yamadaN₂ d t)) {α : ↥(yamadaBarK₂ d t) ≃* SL(2, K)}
    (hex : ExactClosure (yamadaBarK₂ d t) α (yamadaT₂ d t) (yamadaBarP₂ d t) f) :
    yamadaP d t ⊓ (yamadaP d t).map (MulAut.conj d.wb).toMonoidHom = yamadaM₆ d t ∧
      yamadaN₂ d t = yamadaP d t ⊔ (yamadaP d t).map (MulAut.conj d.wb).toMonoidHom :=
  ⟨SeriesN2Aux.P_inf_map_wb hW h d hK hQ hex, SeriesN2Aux.N₂_eq_P_sup hW h d hK hQ hex⟩

end Local

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
