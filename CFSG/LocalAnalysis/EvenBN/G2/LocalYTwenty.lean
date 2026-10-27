module

public import CFSG.LocalAnalysis.EvenBN.G2.LocalYNineteen

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.LocalAnalysis.EvenBN.Common (CosetData)
open scoped commutatorElement Pointwise

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Local

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem yamada_5_23_1 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    normalizer (yamadaV₂ d t : Set G) = normalizer ((d.W ⊔ zpowers t : Subgroup G) : Set G) ∧
      normalizer (yamadaV₂ d t : Set G) =
        yamadaL₃ d t ⊔ normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G) ∧
      ((normalizer (yamadaV₂ d t : Set G) : Subgroup G) : Set G) = (yamadaL₃ d t : Set G) *
        ((normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G) : Subgroup G) : Set G) ∧
      normalizer (yamadaV₂ d t : Set G) ≤ normalizer (yamadaY₂ d t : Set G) ∧
      yamadaL₃ d t ⊓ normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G) = yamadaL₂ d t := by
  have hL₃ := h.yamadaL₃_eq_translationsW₂ hW d hK hD
  have hL₃V : yamadaL₃ d t ≤ normalizer (yamadaV₂ d t : Set G) :=
    LieType.BorelTits.pCoreOf_le 2 _
  have hH₀V := (h.normalizer_tY_le d hK hD).2.2
  have hfac : ∀ g ∈ normalizer (yamadaV₂ d t : Set G), ∃ p ∈ yamadaL₃ d t,
      p⁻¹ * g ∈ normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G) := fun g hg => by
    obtain ⟨p, hp, y, hy, e⟩ :=
      h.exists_mem_translationsW₂_crossed hW d hK hD (h.crossed_mem_W hW d hK hD hg)
    have hp' : p ∈ yamadaL₃ d t := hL₃.ge hp
    exact ⟨p, hp', h.inv_mul_mem_normalizer_tY hW d hK hD (hL₃V hp') hg hy e⟩
  have hset : ((normalizer (yamadaV₂ d t : Set G) : Subgroup G) : Set G) =
      (yamadaL₃ d t : Set G) *
        ((normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G) : Subgroup G) : Set G) := by
    ext g
    refine ⟨fun hg => ?_, fun hg => ?_⟩
    · obtain ⟨p, hp, hpg⟩ := hfac g hg
      exact Set.mem_mul.2 ⟨p, hp, p⁻¹ * g, hpg, by group⟩
    · obtain ⟨p, hp, c, hc, rfl⟩ := Set.mem_mul.1 hg
      exact mul_mem (hL₃V hp) (hH₀V hc)
  refine ⟨le_antisymm (h.normalizer_yamadaV₂_le hW d hK hD).2.1 fun g hg => ?_,
    le_antisymm (fun g hg => ?_) (sup_le hL₃V hH₀V), hset,
    h.normalizer_yamadaV₂_le_normalizer_yamadaY₂ hW d hK hD,
    le_antisymm (h.yamadaL₃_inf_le d hK hD)
      (le_inf ((h.yamadaL₂_le_translationsW₂ hW d hK hD).trans hL₃.ge) (yamadaL₂_le d t))⟩
  · have hgt : g * t * g⁻¹ ∈ d.W ⊔ zpowers t :=
      (mem_normalizer_iff.1 hg t).1 (mem_sup_right (mem_zpowers t))
    have hκ : t * g * t * g⁻¹ ∈ d.W := by
      rcases (h.mem_sup_zpowers_iff (d.image_le _)).1 hgt with h1 | h1
      · exact absurd ((le_sup_left : d.W ≤ yamadaW₂ d t) h1)
          (h.conj_t_not_mem_yamadaW₂ hW d hK hD g)
      · rwa [show t * g * t * g⁻¹ = t * (g * t * g⁻¹) by group]
    obtain ⟨x, hx, hc⟩ := h.exists_mul_mem_centralizer hW d hK hD hκ
    have hxV := (Subgroup.mem_inf.1 hx).1
    have hcN : x⁻¹ * g ∈ normalizer ((d.W ⊔ zpowers t : Subgroup G) : Set G) :=
      mul_mem (inv_mem ((h.normalizer_yamadaV₂_le hW d hK hD).2.1 hxV)) hg
    have hcW := h.mem_normalizer_of_mem_normalizer_sup_t (d.image_le _) hc hcN
    have hcY := (h.centralizer_inf_normalizer_Y_le_W d hK hD).2 (Subgroup.mem_inf.2 ⟨hc, hcW⟩)
    have := mul_mem hxV (hH₀V (h.centralizer_inf_normalizer_Y_le d
      (Subgroup.mem_inf.2 ⟨hc, hcY⟩)))
    rwa [mul_inv_cancel_left] at this
  · obtain ⟨p, hp, hpg⟩ := hfac g hg
    have := mul_mem (mem_sup_left hp)
      (mem_sup_right hpg : p⁻¹ * g ∈ yamadaL₃ d t ⊔ normalizer ((d.Y ⊔ zpowers t :
        Subgroup G) : Set G))
    rwa [mul_inv_cancel_left] at this

theorem yamada_5_23_2 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    (∀ g ∈ yamadaL₃ d t, ∃ w ∈ d.W, g * t * g⁻¹ = t * w) ∧
      ∀ w ∈ d.W, ∃ g ∈ yamadaL₃ d t, g * t * g⁻¹ = t * w := by
  have hL₃ := h.yamadaL₃_eq_translationsW₂ hW d hK hD
  have hL₃V : yamadaL₃ d t ≤ normalizer (yamadaV₂ d t : Set G) :=
    LieType.BorelTits.pCoreOf_le 2 _
  refine ⟨fun g hg => ⟨_, h.crossed_mem_W hW d hK hD (hL₃V hg), h.conj_t_eq_mul_crossed g⟩,
    fun w hw => ?_⟩
  obtain ⟨p, hp, y, hy, e⟩ := h.exists_mem_translationsW₂_crossed hW d hK hD hw
  have hp' : p ∈ yamadaL₃ d t := hL₃.ge hp
  have hpY := h.normalizer_yamadaV₂_le_normalizer_Y hW d hK hD (hL₃V hp')
  have hy' : p⁻¹ * y⁻¹ * p ∈ d.Y := by
    have := (mem_normalizer_iff.1 (inv_mem hpY) y⁻¹).1 (inv_mem hy)
    rwa [inv_inv] at this
  obtain ⟨l, hl, el⟩ := (h.two_core_L₂ d hK).2.2.1 _ hy'
  refine ⟨p * l⁻¹, mul_mem hp' (hL₃.ge (h.yamadaL₂_le_translationsW₂ hW d hK hD (inv_mem hl))),
    ?_⟩
  calc p * l⁻¹ * t * (p * l⁻¹)⁻¹ = p * (l⁻¹ * t * l) * p⁻¹ := by group
    _ = p * (t * (p⁻¹ * y⁻¹ * p)) * p⁻¹ := by rw [el]
    _ = (p * t * p⁻¹) * y⁻¹ := by group
    _ = t * (t * p * t * p⁻¹) * y⁻¹ := by rw [h.conj_t_eq_mul_crossed p]
    _ = t * w := by rw [e]; group

theorem yamada_5_23_3 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    ∃ _ : ((yamadaL₂ d t).subgroupOf (yamadaL₃ d t)).Normal,
      ∃ _ : (d.Y.subgroupOf d.W).Normal,
        ∃ φ : yamadaL₃ d t ⧸ (yamadaL₂ d t).subgroupOf (yamadaL₃ d t) ≃*
          d.W ⧸ d.Y.subgroupOf d.W,
        (∀ (x : yamadaL₃ d t) (w : d.W), (x : G) * t * (x : G)⁻¹ = t * w →
          φ (QuotientGroup.mk x) = QuotientGroup.mk w) ∧
        ∀ c ∈ centralizer ({t} : Set G) ⊓ normalizer (d.Y : Set G),
          ∀ (x : yamadaL₃ d t) (w : d.W), φ (QuotientGroup.mk x) = QuotientGroup.mk w →
            ∃ (hx : c * x * c⁻¹ ∈ yamadaL₃ d t) (hw : c * w * c⁻¹ ∈ d.W),
              φ (QuotientGroup.mk ⟨_, hx⟩) = QuotientGroup.mk ⟨_, hw⟩ := by
  have hL₃ := h.yamadaL₃_eq_translationsW₂ hW d hK hD
  have hL₃V : yamadaL₃ d t ≤ normalizer (yamadaV₂ d t : Set G) :=
    LieType.BorelTits.pCoreOf_le 2 _
  have hL₃X : yamadaL₃ d t ≤ centralizerW₂Y₂ d t := fun x hx =>
    ((h.mem_translationsW₂_iff hW d hK hD).1 (hL₃.le hx)).1
  have hYWn : (d.Y.subgroupOf d.W).Normal :=
    (normal_subgroupOf_iff_le_normalizer d.inclusions.2.2.1).2 (W_le_normalizer_Y d)
  have hκW : ∀ x : yamadaL₃ d t, t * (x : G) * t * (x : G)⁻¹ ∈ d.W := fun x =>
    h.crossed_mem_W hW d hK hD (hL₃V x.2)
  let ψ : yamadaL₃ d t →* d.W ⧸ d.Y.subgroupOf d.W :=
    { toFun := fun x => QuotientGroup.mk ⟨_, hκW x⟩
      map_one' := by
        apply (QuotientGroup.eq_one_iff _).2
        rw [mem_subgroupOf]
        show t * 1 * t * (1 : G)⁻¹ ∈ d.Y
        rw [mul_one, inv_one, mul_one, h.t_mul_t]
        exact one_mem _
      map_mul' := fun x y => by
        rw [← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf]
        obtain ⟨y₁, hy₁, e⟩ := h.crossed_mul_mem_Y hW d hK hD (hL₃X x.2) (hL₃V y.2)
        show (t * ((x : G) * y) * t * ((x : G) * y)⁻¹)⁻¹ *
          ((t * x * t * (x : G)⁻¹) * (t * y * t * (y : G)⁻¹)) ∈ d.Y
        rw [e, show (t * x * t * (x : G)⁻¹ * (t * y * t * (y : G)⁻¹) * y₁)⁻¹ *
          (t * x * t * (x : G)⁻¹ * (t * y * t * (y : G)⁻¹)) = y₁⁻¹ by group]
        exact inv_mem hy₁ }
  have hψ : ∀ x : yamadaL₃ d t, ψ x = QuotientGroup.mk ⟨_, hκW x⟩ := fun _ => rfl
  have hform : ∀ (x : yamadaL₃ d t) (w : d.W), (x : G) * t * (x : G)⁻¹ = t * w →
      ψ x = QuotientGroup.mk w := by
    intro x w e
    rw [hψ]
    congr 1
    apply Subtype.ext
    show t * x * t * (x : G)⁻¹ = w
    rw [show t * (x : G) * t * (x : G)⁻¹ = t * ((x : G) * t * (x : G)⁻¹) by group, e,
      ← mul_assoc, h.t_mul_t, one_mul]
  have hker : ψ.ker = (yamadaL₂ d t).subgroupOf (yamadaL₃ d t) := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf, hψ, QuotientGroup.eq_one_iff, mem_subgroupOf]
    constructor
    · intro hx
      exact h.yamadaL₃_inf_le d hK hD (Subgroup.mem_inf.2
        ⟨x.2, (h.crossed_mem_Y_iff hW d hK hD (hL₃V x.2)).1 hx⟩)
    · intro hx
      exact (h.crossed_mem_Y_iff hW d hK hD (hL₃V x.2)).2 (yamadaL₂_le d t hx)
  have hsurj : Function.Surjective ψ := by
    intro q
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨g, hg, e⟩ := (h.yamada_5_23_2 hW d hK hD).2 w w.2
    exact ⟨⟨g, hg⟩, hform ⟨g, hg⟩ w e⟩
  have hL₂n : ((yamadaL₂ d t).subgroupOf (yamadaL₃ d t)).Normal := hker ▸ ψ.normal_ker
  set φ := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hsurj) with hφdef
  have hφ : ∀ x : yamadaL₃ d t, φ (QuotientGroup.mk x) = ψ x := fun _ => rfl
  refine ⟨hL₂n, hYWn, φ, fun x w e => (hφ x).trans (hform x w e), ?_⟩
  intro c hc x w hxw
  obtain ⟨hct, hcY⟩ := Subgroup.mem_inf.1 hc
  have hcN := h.centralizer_inf_normalizer_Y_le d hc
  have hcL₃ : c ∈ normalizer (yamadaL₃ d t : Set G) :=
    LieType.BorelTits.le_normalizer_pCoreOf 2 _ ((h.normalizer_tY_le d hK hD).2.2 hcN)
  have hcW := (h.centralizer_inf_normalizer_Y_le_W d hK hD).1 hc
  have hx : c * x * c⁻¹ ∈ yamadaL₃ d t := (mem_normalizer_iff.1 hcL₃ x).1 x.2
  have hw : c * w * c⁻¹ ∈ d.W := (mem_normalizer_iff.1 hcW w).1 w.2
  refine ⟨hx, hw, ?_⟩
  rw [hφ, hψ, QuotientGroup.eq, mem_subgroupOf] at hxw ⊢
  have hcte : c * t = t * c := mem_centralizer_singleton_iff.1 hct
  have hct' : c⁻¹ * t * c = t := by rw [mul_assoc, ← hcte, inv_mul_cancel_left]
  have hκc : t * (c * x * c⁻¹) * t * (c * x * c⁻¹)⁻¹ = c * (t * x * t * (x : G)⁻¹) * c⁻¹ := by
    calc t * (c * x * c⁻¹) * t * (c * x * c⁻¹)⁻¹ =
          (t * c) * x * (c⁻¹ * t * c) * (x : G)⁻¹ * c⁻¹ := by group
      _ = (c * t) * x * t * (x : G)⁻¹ * c⁻¹ := by rw [hct', ← hcte]
      _ = c * (t * x * t * (x : G)⁻¹) * c⁻¹ := by group
  show (t * (c * x * c⁻¹) * t * (c * x * c⁻¹)⁻¹)⁻¹ * (c * w * c⁻¹) ∈ d.Y
  rw [hκc, show (c * (t * x * t * (x : G)⁻¹) * c⁻¹)⁻¹ * (c * w * c⁻¹) =
    c * ((t * x * t * (x : G)⁻¹)⁻¹ * w) * c⁻¹ by group]
  exact (mem_normalizer_iff.1 hcY _).1 hxw

theorem isPGroup_yamadaRstar (h : Setup G L f t) (d : G2Data L K) :
    IsPGroup 2 (yamadaRstar d t) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact IsPGroup.to_sup_of_normal_left' (LieType.BorelTits.pCoreOf_isPGroup 2 _)
    d.isSylowOf_S.isPGroup (h.S_le_normalizer_yamadaCstar d)

theorem yamada_5_23_4 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) : yamadaR₃ d t = yamadaR₃star d t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL₃ := h.yamadaL₃_eq_translationsW₂ hW d hK hD
  have hL₃V : yamadaL₃ d t ≤ normalizer (yamadaV₂ d t : Set G) :=
    LieType.BorelTits.pCoreOf_le 2 _
  have hNL₃ : normalizer (yamadaV₂ d t : Set G) ≤ normalizer (yamadaL₃ d t : Set G) :=
    LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hR₃V : yamadaR₃star d t ≤ normalizer (yamadaV₂ d t : Set G) := fun g hg =>
    (Subgroup.mem_inf.1 (h.yamadaR₃star_le_normalizer hW d hK hD hg)).1
  have hSH₀ : d.S ≤ normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G) := fun s hs =>
    (h.centralizer_inf_normalizer_S_le_normalizer_yamadaR₂ d hK hD).2
      (mem_sup_left (mem_sup_right hs))
  have hH₀V := (h.normalizer_tY_le d hK hD).2.2
  obtain ⟨hR₂eq, -⟩ := h.yamada_5_21_2 hW d hK hD
  have hR₂R₃ : yamadaR₂ d t ≤ yamadaR₃star d t := by
    rw [hR₂eq]
    exact inf_le_left
  have hSR₃ : d.S ≤ yamadaR₃star d t := (le_sup_right : d.S ≤ yamadaR₂ d t).trans hR₂R₃
  have h1 : yamadaR₃star d t ≤ yamadaR₃ d t := by
    intro g hg
    have hgX := h.yamadaR₃star_le_centralizerW₂Y₂ hW d hK hD hg
    have hgV := hR₃V hg
    obtain ⟨p, hp, y, hy, e⟩ :=
      h.exists_mem_translationsW₂_crossed hW d hK hD (h.crossed_mem_W hW d hK hD hgV)
    have hpX := ((h.mem_translationsW₂_iff hW d hK hD).1 hp).1
    have hp' : p ∈ yamadaL₃ d t := hL₃.ge hp
    have hk : p⁻¹ * g ∈ kernelTW₂ d t := Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hpX) hgX,
      h.inv_mul_mem_normalizer_tY hW d hK hD (hL₃V hp') hgV hy e⟩
    have hBL₂ : d.leviB ≤ normalizer (yamadaL₂ d t : Set G) := fun b hb =>
      le_normalizer_yamadaL₂ d t (Subgroup.mem_inf.1 (h.leviB_le_kernelTW₂ hW d hK hD hb)).2
    obtain ⟨l, hl, b, hb, e'⟩ :=
      Common.exists_mul_of_le_normalizer hBL₂ _ (h.kernelTW₂_le hW d hK hD hk)
    have hlL₃ : l ∈ yamadaL₃ d t := hL₃.ge (h.yamadaL₂_le_translationsW₂ hW d hK hD hl)
    have hTp : IsPGroup 2 (yamadaL₃ d t ⊔ yamadaR₃star d t : Subgroup G) :=
      IsPGroup.to_sup_of_normal_left' (LieType.BorelTits.pCoreOf_isPGroup 2 _)
        ((h.isPGroup_yamadaRstar d).to_le inf_le_left) (hR₃V.trans hNL₃)
    have hbT : b ∈ yamadaL₃ d t ⊔ yamadaR₃star d t := by
      have hbe : b = (p * l)⁻¹ * g := by
        calc b = l⁻¹ * (l * b) := by group
          _ = l⁻¹ * (p⁻¹ * g) := by rw [e']
          _ = (p * l)⁻¹ * g := by group
      rw [hbe]
      exact mul_mem (inv_mem (mem_sup_left (mul_mem hp' hlL₃))) (mem_sup_right hg)
    have hLT : L ⊓ (yamadaL₃ d t ⊔ yamadaR₃star d t) = d.S :=
      d.isSylowOf_S.eq_of_le (le_inf (d.image_le _) (hSR₃.trans le_sup_right)) inf_le_left
        (hTp.to_le inf_le_right)
    have hbS : b ∈ d.S := by
      rw [← hLT]
      exact Subgroup.mem_inf.2 ⟨d.image_le _ hb, hbT⟩
    have hge : g = p * l * b := by
      calc g = p * (p⁻¹ * g) := by group
        _ = p * (l * b) := by rw [e']
        _ = p * l * b := by group
    rw [hge]
    exact mul_mem (mul_mem (mem_sup_left hp') (mem_sup_left hlL₃)) (mem_sup_right hbS)
  refine le_antisymm (fun z hz => ?_) h1
  have hSV : d.S ≤ normalizer (yamadaV₂ d t : Set G) := hSH₀.trans hH₀V
  have hzV : z ∈ normalizer (yamadaV₂ d t : Set G) := (sup_le hL₃V hSV) hz
  have hκz := h.crossed_mem_W hW d hK hD hzV
  obtain ⟨g, hg, u, hu, e⟩ := (h.yamada_5_21_1 d hK hD).1.2 _ (mem_sup_left hκz)
  have hgV := hR₃V hg
  have hκg : t * g * t * g⁻¹ = (t * z * t * z⁻¹) * u := by
    rw [show t * g * t * g⁻¹ = t * (g * t * g⁻¹) by group, e, ← mul_assoc, ← mul_assoc,
      h.t_mul_t, one_mul]
  have huW : u ∈ d.W := by
    have := mul_mem (inv_mem hκz) (h.crossed_mem_W hW d hK hD hgV)
    rwa [hκg, inv_mul_cancel_left] at this
  have huY : u ∈ d.Y := by
    rw [← h.W_inf_yamadaY₂ d hK hD]
    exact Subgroup.mem_inf.2 ⟨huW, yamadaU₁_le_yamadaY₂ d t hu⟩
  have hc := h.inv_mul_mem_normalizer_tY hW d hK hD hgV hzV huY hκg
  have hcR₃ : g⁻¹ * z ∈ yamadaR₃ d t := mul_mem (inv_mem (h1 hg)) hz
  obtain ⟨p', hp', s, hs, e₂⟩ :=
    Common.exists_mul_of_le_normalizer (hSV.trans hNL₃) _ hcR₃
  have hp'H : p' ∈ normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G) := by
    have := mul_mem hc (inv_mem (hSH₀ hs))
    rwa [e₂, mul_inv_cancel_right] at this
  have hp'L₂ := h.yamadaL₃_inf_le d hK hD (Subgroup.mem_inf.2 ⟨hp', hp'H⟩)
  have hcR₂ : g⁻¹ * z ∈ yamadaR₂ d t := by
    rw [e₂]
    exact mul_mem (mem_sup_left hp'L₂) (mem_sup_right hs)
  have := mul_mem hg (hR₂R₃ hcR₂)
  rwa [mul_inv_cancel_left] at this

end Local

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
