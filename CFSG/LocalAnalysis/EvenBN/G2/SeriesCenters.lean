module

public import CFSG.LocalAnalysis.EvenBN.G2.SeriesN2
import CFSG.SignalizerFunctorTheorem.McBride.Prelim.ThreeSubgroups
import CFSG.LocalAnalysis.EvenBN.GMSK.SL2Facts

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

namespace SeriesCentersAux

section Generic

variable {G : Type*} [Group G]

open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase in
theorem conj_mem_centralizerMod {W B : Subgroup G} {g x : G}
    (hgW : g ∈ normalizer (W : Set G)) (hgB : g ∈ normalizer (B : Set G))
    (hx : x ∈ centralizerMod W B) : g * x * g⁻¹ ∈ centralizerMod W B := by
  rw [mem_centralizerMod_iff] at hx ⊢
  obtain ⟨hxW, hxc⟩ := hx
  refine ⟨mul_mem (mul_mem hgW hxW) (inv_mem hgW), fun b hb hbW => ?_⟩
  have hb' : g⁻¹ * b * g ∈ B := by
    have := (mem_normalizer_iff.1 (inv_mem hgB) b).1 hb
    simpa using this
  have hb'W : g⁻¹ * b * g ∈ normalizer (W : Set G) :=
    mul_mem (mul_mem (inv_mem hgW) hbW) hgW
  have h1 := hxc _ hb' hb'W
  have h2 := (mem_normalizer_iff.1 hgW _).1 h1
  have e : g * (x * (g⁻¹ * b * g) * x⁻¹ * (g⁻¹ * b * g)⁻¹) * g⁻¹ =
      g * x * g⁻¹ * b * (g * x * g⁻¹)⁻¹ * b⁻¹ := by group
  rw [e] at h2
  exact h2

open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase in
theorem conj_mem_centerMod {X A : Subgroup G} (hXA : X ≤ A) (hAX : A ≤ normalizer (X : Set G))
    {n g : G} (hnA : n ∈ normalizer (A : Set G)) (hnX : n ∈ normalizer (X : Set G))
    (hg : g ∈ centerMod X A) : n * g * n⁻¹ ∈ centerMod X A := by
  rw [mem_centerMod_iff hXA] at hg ⊢
  obtain ⟨hgA, hgX, hgc⟩ := hg
  refine ⟨(mem_normalizer_iff.1 hnA g).1 hgA, mul_mem (mul_mem hnX hgX) (inv_mem hnX),
    fun a ha haX => ?_⟩
  have ha' : n⁻¹ * a * n ∈ A := by
    have := (mem_normalizer_iff.1 (inv_mem hnA) a).1 ha
    simpa using this
  have h1 := hgc _ ha' (hAX ha')
  have h2 := (mem_normalizer_iff.1 hnX _).1 h1
  have e : n * (g * (n⁻¹ * a * n) * g⁻¹ * (n⁻¹ * a * n)⁻¹) * n⁻¹ =
      n * g * n⁻¹ * a * (n * g * n⁻¹)⁻¹ * a⁻¹ := by group
  rw [e] at h2
  exact h2

theorem commutator_commutator_mem {Y X Z W : Subgroup G} (hX : X ≤ normalizer (Y : Set G))
    (hZ : Z ≤ normalizer (Y : Set G)) (h1 : ∀ x ∈ X, ∀ z ∈ Z, ⁅x, z⁆ ∈ W)
    (h2 : ∀ w ∈ W, ∀ x ∈ X, ⁅w, x⁆ ∈ Y) :
    ∀ a ∈ X, ∀ b ∈ X, ∀ z ∈ Z, ⁅⁅a, b⁆, z⁆ ∈ Y := by
  set H := normalizer (Y : Set G) with hH
  have hYn : (Y.subgroupOf H).Normal := inferInstance
  have hXZ : ⁅X.subgroupOf H, Z.subgroupOf H⁆ ≤ W.subgroupOf H := by
    refine commutator_le.2 fun x hx z hz => ?_
    exact mem_subgroupOf.2 (h1 x (mem_subgroupOf.1 hx) z (mem_subgroupOf.1 hz))
  have key := CFSG.SignalizerFunctorTheorem.McBride.three_subgroups_lemma_normal
    (X := X.subgroupOf H) (Y := Z.subgroupOf H) (Z := X.subgroupOf H) (N := Y.subgroupOf H)
    (commutator_le.2 fun c hc x hx => mem_subgroupOf.2
      (h2 _ (mem_subgroupOf.1 (hXZ hc)) _ (mem_subgroupOf.1 hx)))
    (commutator_le.2 fun c hc x hx => by
      rw [commutator_comm] at hc
      exact mem_subgroupOf.2 (h2 _ (mem_subgroupOf.1 (hXZ hc)) _ (mem_subgroupOf.1 hx)))
  intro a ha b hb z hz
  have ha' : (⟨a, hX ha⟩ : H) ∈ X.subgroupOf H := ha
  have hb' : (⟨b, hX hb⟩ : H) ∈ X.subgroupOf H := hb
  have hz' : (⟨z, hZ hz⟩ : H) ∈ Z.subgroupOf H := hz
  exact mem_subgroupOf.1
    (key (commutator_mem_commutator (commutator_mem_commutator ha' hb') hz'))

open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase in
theorem conj_mem_centralizerMod_map {W B : Subgroup G} {g x : G}
    (hgW : g ∈ normalizer (W : Set G)) (hx : x ∈ centralizerMod W B) :
    g * x * g⁻¹ ∈ centralizerMod W (B.map (MulAut.conj g).toMonoidHom) := by
  rw [mem_centralizerMod_iff] at hx ⊢
  obtain ⟨hxW, hxc⟩ := hx
  refine ⟨mul_mem (mul_mem hgW hxW) (inv_mem hgW), fun b hb hbW => ?_⟩
  obtain ⟨b₀, hb₀, rfl⟩ := hb
  have hb₀W : b₀ ∈ normalizer (W : Set G) := by
    have := mul_mem (mul_mem (inv_mem hgW) hbW) hgW
    simpa [MulAut.conj_apply, mul_assoc] using this
  have h1 := (mem_normalizer_iff.1 hgW _).1 (hxc b₀ hb₀ hb₀W)
  have e : g * (x * b₀ * x⁻¹ * b₀⁻¹) * g⁻¹ = g * x * g⁻¹ * (g * b₀ * g⁻¹) * (g * x * g⁻¹)⁻¹ *
      (g * b₀ * g⁻¹)⁻¹ := by group
  rw [e] at h1
  exact h1

open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase in
theorem centralizerMod_anti {W B B' : Subgroup G} (hBB' : B' ≤ B) :
    centralizerMod W B ≤ centralizerMod W B' := fun x hx => by
  rw [mem_centralizerMod_iff] at hx ⊢
  exact ⟨hx.1, fun b hb hbW => hx.2 b (hBB' hb) hbW⟩

end Generic

section Local

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

open SeriesN2Aux
open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase (mem_centerMod_iff mem_centralizerMod_iff)

theorem Y₂_le_N₂ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaY₂ d t ≤ yamadaN₂ d t :=
  (h.yamadaY₂_le_yamadaM₆ hW d hK hQ).trans (yamadaM₆_le_yamadaN₂ d t)

theorem N₂_le_normalizer_Y₂ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaN₂ d t ≤ normalizer (yamadaY₂ d t : Set G) :=
  (N₂_le_normalizer_M₆ hW h d hK hQ).trans (normalizer_M₆_le_normalizer_Y₂ hW h d hK hQ)

theorem P_le_normalizer_Y₂ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaP d t ≤ normalizer (yamadaY₂ d t : Set G) :=
  (P_le_normalizer_M₆ hW h d hK hQ).trans (normalizer_M₆_le_normalizer_Y₂ hW h d hK hQ)

theorem wb_mem_normalizer_N₂ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    d.wb ∈ normalizer (yamadaN₂ d t : Set G) :=
  mem_normalizer_fintype fun _ hx =>
    conj_mem_N₂ hW h d hK hQ (h.wb_mem_normalizer_yamadaM₆ d hK) hx

theorem t_mem_normalizer_N₂ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    t ∈ normalizer (yamadaN₂ d t : Set G) :=
  mem_normalizer_fintype fun _ hx =>
    conj_mem_N₂ hW h d hK hQ (t_mem_normalizer_M₆ hW h d hK hQ) hx

theorem N₂_le_centralizerMod_W₃ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d)
    {α : ↥(yamadaBarK₂ d t) ≃* SL(2, K)}
    (hex : ExactClosure (yamadaBarK₂ d t) α (yamadaT₂ d t) (yamadaBarP₂ d t) f) :
    yamadaN₂ d t ≤ centralizerMod (yamadaY₂ d t) (yamadaW₃ d t) := by
  have hD := hQ.doubling
  have hwY := Setup.Q44.wb_mem_normalizer_Y₂ h d hK hD
  have hwW := Setup.Q44.wb_mem_normalizer_W₃ hW h d hK hQ
  have hPY := P_le_normalizer_Y₂ hW h d hK hQ
  have hWF : yamadaW₃ d t ≤ yamadaF₅ d t := Setup.Q44.W₃_le_F₅ d t
  have hP : yamadaP d t ≤ centralizerMod (yamadaY₂ d t) (yamadaW₃ d t) := by
    intro p hp
    rw [mem_centralizerMod_iff]
    refine ⟨hPY hp, fun b hb hbN => ?_⟩
    have := ((mem_F₅_iff hW h d hK hQ).1 (hWF hb)).2 p hp
    have e : p * b * p⁻¹ * b⁻¹ = (b * p * b⁻¹ * p⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem this
  rw [N₂_eq_P_sup hW h d hK hQ hex]
  refine sup_le hP ?_
  rintro _ ⟨p, hp, rfl⟩
  exact conj_mem_centralizerMod hwY hwW (hP hp)

theorem W₃_le_centerMod_Y₂ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d)
    {α : ↥(yamadaBarK₂ d t) ≃* SL(2, K)}
    (hex : ExactClosure (yamadaBarK₂ d t) α (yamadaT₂ d t) (yamadaBarP₂ d t) f) :
    yamadaW₃ d t ≤ centerMod (yamadaY₂ d t) (yamadaN₂ d t) := by
  intro w hw
  have hWM := h.yamadaW₃_le_yamadaM₆ hW d hK hQ
  have hWN : w ∈ yamadaN₂ d t := yamadaM₆_le_yamadaN₂ d t (hWM hw)
  rw [mem_centerMod_iff (Y₂_le_N₂ hW h d hK hQ)]
  refine ⟨hWN, N₂_le_normalizer_Y₂ hW h d hK hQ hWN, fun a ha haN => ?_⟩
  have h1 := (mem_centralizerMod_iff.1 (N₂_le_centralizerMod_W₃ hW h d hK hQ hex ha)).2 w hw
    (N₂_le_normalizer_Y₂ hW h d hK hQ hWN)
  have e : w * a * w⁻¹ * a⁻¹ = (a * w * a⁻¹ * w⁻¹)⁻¹ := by group
  rw [e]
  exact inv_mem h1

theorem not_M₆_le_F₅ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    ¬ yamadaM₆ d t ≤ yamadaF₅ d t := by
  intro hle
  obtain ⟨-, -, -, hF₅c, -, -, hM₆c, -, -⟩ := h.card_yamada_five_six hW d hK hQ
  have h1 := Subgroup.card_le_of_le hle
  rw [hF₅c, hM₆c] at h1
  have : Nat.card K ^ 8 < Nat.card K ^ 10 := Nat.pow_lt_pow_right hQ.one_lt (by norm_num)
  omega

theorem centerMod_Y₂_le_F₅ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d)
    {α : ↥(yamadaBarK₂ d t) ≃* SL(2, K)}
    (hex : ExactClosure (yamadaBarK₂ d t) α (yamadaT₂ d t) (yamadaBarP₂ d t) f) {g : G}
    (hg : g ∈ centerMod (yamadaY₂ d t) (yamadaN₂ d t)) : g ∈ yamadaF₅ d t := by
  rw [mem_centerMod_iff (Y₂_le_N₂ hW h d hK hQ)] at hg
  obtain ⟨hgN, hgY, hgc⟩ := hg
  have hMN := yamadaM₆_le_yamadaN₂ d t
  have hMP := h.yamadaM₆_le_yamadaP hW d hK hQ
  have hPN := P_le_N₂ hW h d hK hQ hex
  have hNY := N₂_le_normalizer_Y₂ hW h d hK hQ
  have hNM := N₂_le_normalizer_M₆ hW h d hK hQ
  have ht := t_mem_normalizer_M₆ hW h d hK hQ
  have hMY := normalizer_M₆_le_normalizer_Y₂ hW h d hK hQ
  have hgM : g ∈ yamadaM₆ d t := by
    have hMZ : yamadaM₆ d t ≤ yamadaN₂ d t ⊓ centralizerMod (yamadaY₂ d t) (yamadaM₆ d t) := by
      refine le_inf hMN fun m hm => ?_
      rw [mem_centralizerMod_iff]
      refine ⟨hMY (Subgroup.le_normalizer hm), fun b hb hbN => ?_⟩
      exact (h.elemModulo_yamadaM₆ hW d hK hQ m hm b hb).2
    rcases eq_M₆_or_eq_N₂ hW h d hK hQ hex hMZ inf_le_left
      (fun n hn z hz => ⟨conj_mem_N₂ hW h d hK hQ (hNM hn) hz.1,
        conj_mem_centralizerMod (hNY hn) (hNM hn) hz.2⟩)
      (fun z hz => ⟨conj_mem_N₂ hW h d hK hQ ht hz.1,
        conj_mem_centralizerMod (hMY ht) ht hz.2⟩) with hZ | hZ
    · have : g ∈ yamadaN₂ d t ⊓ centralizerMod (yamadaY₂ d t) (yamadaM₆ d t) :=
        ⟨hgN, mem_centralizerMod_iff.2 ⟨hgY, fun b hb hbN => hgc b (hMN hb) hbN⟩⟩
      rw [hZ] at this
      exact this
    · exfalso
      refine not_M₆_le_F₅ hW h d hK hQ fun m hm => ?_
      refine (mem_F₅_iff hW h d hK hQ).2 ⟨hMP hm, fun p hp => ?_⟩
      have hpZ : p ∈ yamadaN₂ d t ⊓ centralizerMod (yamadaY₂ d t) (yamadaM₆ d t) := by
        rw [hZ]
        exact hPN hp
      have h1 := (mem_centralizerMod_iff.1 hpZ.2).2 m hm (hMY (Subgroup.le_normalizer hm))
      have e : m * p * m⁻¹ * p⁻¹ = (p * m * p⁻¹ * m⁻¹)⁻¹ := by group
      rw [e]
      exact inv_mem h1
  exact (mem_F₅_iff hW h d hK hQ).2 ⟨hMP hgM, fun a ha => hgc a (hPN ha) (hNY (hPN ha))⟩

theorem centerMod_Y₂_eq (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d)
    {α : ↥(yamadaBarK₂ d t) ≃* SL(2, K)}
    (hex : ExactClosure (yamadaBarK₂ d t) α (yamadaT₂ d t) (yamadaBarP₂ d t) f) :
    centerMod (yamadaY₂ d t) (yamadaN₂ d t) = yamadaW₃ d t := by
  refine le_antisymm (fun g hg => ?_) (W₃_le_centerMod_Y₂ hW h d hK hQ hex)
  have hD := hQ.doubling
  have hwY := Setup.Q44.wb_mem_normalizer_Y₂ h d hK hD
  have h1 := centerMod_Y₂_le_F₅ hW h d hK hQ hex hg
  have hs : d.wb⁻¹ * g * d.wb ∈ centerMod (yamadaY₂ d t) (yamadaN₂ d t) := by
    have := conj_mem_centerMod (Y₂_le_N₂ hW h d hK hQ) (N₂_le_normalizer_Y₂ hW h d hK hQ)
      (n := d.wb⁻¹) (inv_mem (wb_mem_normalizer_N₂ hW h d hK hQ)) (inv_mem hwY) hg
    simpa using this
  have h2 := centerMod_Y₂_le_F₅ hW h d hK hQ hex hs
  have h3 : g ∈ (yamadaF₅ d t).map (MulAut.conj d.wb).toMonoidHom := mem_map_conj_iff.2 h2
  rw [← Setup.Q44.F₅_inf_map_wb hW h d hK hQ]
  exact ⟨h1, h3⟩

theorem N₂_le_normalizer_W₃ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d)
    {α : ↥(yamadaBarK₂ d t) ≃* SL(2, K)}
    (hex : ExactClosure (yamadaBarK₂ d t) α (yamadaT₂ d t) (yamadaBarP₂ d t) f) :
    yamadaN₂ d t ≤ normalizer (yamadaW₃ d t : Set G) := by
  intro n hn
  have hb := centerMod_Y₂_eq hW h d hK hQ hex
  refine mem_normalizer_fintype fun w hw => ?_
  rw [← hb] at hw ⊢
  exact conj_mem_centerMod (Y₂_le_N₂ hW h d hK hQ) (N₂_le_normalizer_Y₂ hW h d hK hQ)
    (Subgroup.le_normalizer hn) (N₂_le_normalizer_Y₂ hW h d hK hQ hn) hw

theorem mem_M₆_of_forall_commutator_mem (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d)
    {α : ↥(yamadaBarK₂ d t) ≃* SL(2, K)}
    (hex : ExactClosure (yamadaBarK₂ d t) α (yamadaT₂ d t) (yamadaBarP₂ d t) f) {z : G}
    (hzN : z ∈ yamadaN₂ d t)
    (hz : ∀ a ∈ yamadaN₂ d t, z * a * z⁻¹ * a⁻¹ ∈ yamadaM₆ d t) : z ∈ yamadaM₆ d t := by
  have hNM := N₂_le_normalizer_M₆ hW h d hK hQ
  have hbar := barSub_yamadaN₂ d t (K₂_le_normalizer hW h d hK hQ)
  obtain ⟨hinf, hcent, -, -, -⟩ := hex
  have hxN : barMap (yamadaM₆ d t) ⟨z, hNM hzN⟩ ∈
      normalClosure (yamadaBarK₂ d t : Set (BarM (yamadaM₆ d t))) := by
    rw [← hbar]
    exact ⟨⟨z, hNM hzN⟩, mem_subgroupOf.2 hzN, rfl⟩
  have hxC : barMap (yamadaM₆ d t) ⟨z, hNM hzN⟩ ∈
      centralizer (normalClosure (yamadaBarK₂ d t : Set (BarM (yamadaM₆ d t))) :
        Set (BarM (yamadaM₆ d t))) := by
    rw [mem_centralizer_iff]
    intro y hy
    rw [← hbar] at hy
    obtain ⟨a, ha, rfl⟩ := hy
    rw [← map_mul, ← map_mul]
    refine CFSG.LocalAnalysis.SymplecticFourStandard.BothTrivialClosure.barMap_eq_iff.2 ?_
    have haN : (a : G) ∈ yamadaN₂ d t := mem_subgroupOf.1 ha
    have hc := hz _ haN
    have haz : (a : G) * z ∈ normalizer (yamadaM₆ d t : Set G) := mul_mem a.2 (hNM hzN)
    have e : ((a : G) * z)⁻¹ * (z * (a : G)) =
        ((a : G) * z)⁻¹ * (z * a * z⁻¹ * (a : G)⁻¹) * (((a : G) * z)⁻¹)⁻¹ := by group
    change ((a : G) * z)⁻¹ * (z * (a : G)) ∈ yamadaM₆ d t
    rw [e]
    exact (mem_normalizer_iff.1 (inv_mem haz) _).1 hc
  rw [hcent] at hxC
  have : barMap (yamadaM₆ d t) ⟨z, hNM hzN⟩ ∈
      normalClosure (yamadaBarK₂ d t : Set (BarM (yamadaM₆ d t))) ⊓
        CFSG.Open.standardComponentOddCore (BarM (yamadaM₆ d t)) := ⟨hxN, hxC⟩
  rw [hinf, Subgroup.mem_bot] at this
  exact CFSG.LocalAnalysis.SymplecticFourStandard.BothTrivialClosure.barMap_eq_one_iff.1 this

theorem N₂_eq_commutator_sup (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d)
    {α : ↥(yamadaBarK₂ d t) ≃* SL(2, K)}
    (hex : ExactClosure (yamadaBarK₂ d t) α (yamadaT₂ d t) (yamadaBarP₂ d t) f) :
    yamadaN₂ d t = ⁅yamadaN₂ d t, yamadaN₂ d t⁆ ⊔ yamadaM₆ d t := by
  have hMN := yamadaM₆_le_yamadaN₂ d t
  have hNM := N₂_le_normalizer_M₆ hW h d hK hQ
  have hKN := K₂_le_normalizer hW h d hK hQ
  have htN := t_mem_normalizer_N₂ hW h d hK hQ
  have ht := t_mem_normalizer_M₆ hW h d hK hQ
  rcases eq_M₆_or_eq_N₂ hW h d hK hQ hex (Z := ⁅yamadaN₂ d t, yamadaN₂ d t⁆ ⊔ yamadaM₆ d t)
    le_sup_right (sup_le (Subgroup.commutator_le_self _) hMN)
    (fun n hn z hz => (mem_normalizer_iff.1
      (mem_normalizer_sup (le_normalizer_commutator _ hn) (hNM hn)) z).1 hz)
    (fun z hz => (mem_normalizer_iff.1
      (mem_normalizer_sup (mem_normalizer_commutator_self htN) ht) z).1 hz) with hZ | hZ
  · exfalso
    have hcomm : ∀ a ∈ yamadaN₂ d t, ∀ b ∈ yamadaN₂ d t, ⁅a, b⁆ ∈ yamadaM₆ d t := fun a ha b hb =>
      hZ ▸ mem_sup_left (commutator_mem_commutator ha hb)
    obtain ⟨x, y, hxy⟩ := CFSG.LocalAnalysis.EvenBN.GMSK.sl2_exists_mul_ne (K := K)
    obtain ⟨k₁, hk₁, hk₁a⟩ := (α.symm x).2
    obtain ⟨k₂, hk₂, hk₂a⟩ := (α.symm y).2
    have hk₁N : (k₁ : G) ∈ yamadaN₂ d t := yamadaK₂_le_yamadaN₂ d t (mem_subgroupOf.1 hk₁)
    have hk₂N : (k₂ : G) ∈ yamadaN₂ d t := yamadaK₂_le_yamadaN₂ d t (mem_subgroupOf.1 hk₂)
    have hc := hcomm _ hk₁N _ hk₂N
    have hcomm' : α.symm y * α.symm x = α.symm x * α.symm y := by
      apply Subtype.ext
      show (α.symm y : BarM (yamadaM₆ d t)) * (α.symm x : BarM (yamadaM₆ d t)) =
        (α.symm x : BarM (yamadaM₆ d t)) * (α.symm y : BarM (yamadaM₆ d t))
      rw [← hk₁a, ← hk₂a, ← map_mul, ← map_mul]
      refine CFSG.LocalAnalysis.SymplecticFourStandard.BothTrivialClosure.barMap_eq_iff.2 ?_
      have e : ((k₂ : G) * k₁)⁻¹ * ((k₁ : G) * k₂) =
          ((k₂ : G) * k₁)⁻¹ * ⁅(k₁ : G), (k₂ : G)⁆ * (((k₂ : G) * k₁)⁻¹)⁻¹ := by
        simp only [commutatorElement_def]; group
      change ((k₂ : G) * k₁)⁻¹ * ((k₁ : G) * k₂) ∈ yamadaM₆ d t
      rw [e]
      exact (mem_normalizer_iff.1 (inv_mem (mul_mem k₂.2 k₁.2)) _).1 hc
    apply hxy
    have := congrArg α hcomm'
    simpa using this.symm
  · exact hZ.symm

theorem centerMod_W₃_eq (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d)
    {α : ↥(yamadaBarK₂ d t) ≃* SL(2, K)}
    (hex : ExactClosure (yamadaBarK₂ d t) α (yamadaT₂ d t) (yamadaBarP₂ d t) f) :
    centerMod (yamadaW₃ d t) (yamadaN₂ d t) = yamadaW₃ d t := by
  have hWM := h.yamadaW₃_le_yamadaM₆ hW d hK hQ
  have hMN := yamadaM₆_le_yamadaN₂ d t
  have hWN : yamadaW₃ d t ≤ yamadaN₂ d t := hWM.trans hMN
  have hYN := Y₂_le_N₂ hW h d hK hQ
  have hNY := N₂_le_normalizer_Y₂ hW h d hK hQ
  have hNW := N₂_le_normalizer_W₃ hW h d hK hQ hex
  refine le_antisymm (fun z hz0 => ?_) (fun w hw => ?_)
  · have hzc' : ∀ z' ∈ centerMod (yamadaW₃ d t) (yamadaN₂ d t), ∀ a ∈ yamadaN₂ d t,
        z' * a * z'⁻¹ * a⁻¹ ∈ yamadaW₃ d t := fun z' hz' a ha =>
      ((mem_centerMod_iff hWN).1 hz').2.2 a ha (hNW ha)
    have hZN : ∀ z' ∈ centerMod (yamadaW₃ d t) (yamadaN₂ d t), z' ∈ yamadaN₂ d t :=
      fun z' hz' => ((mem_centerMod_iff hWN).1 hz').1
    have hZM : ∀ z' ∈ centerMod (yamadaW₃ d t) (yamadaN₂ d t), z' ∈ yamadaM₆ d t := fun z' hz' =>
      mem_M₆_of_forall_commutator_mem hW h d hK hQ hex (hZN z' hz') fun a ha =>
        hWM (hzc' z' hz' a ha)
    have hWY : ∀ w ∈ yamadaW₃ d t, ∀ x ∈ yamadaN₂ d t, w * x * w⁻¹ * x⁻¹ ∈ yamadaY₂ d t :=
      fun w hw x hx => ((mem_centerMod_iff hYN).1
        (W₃_le_centerMod_Y₂ hW h d hK hQ hex hw)).2.2 x hx (hNY hx)
    set H : Subgroup G := yamadaN₂ d t ⊓
      centralizerMod (yamadaY₂ d t) (centerMod (yamadaW₃ d t) (yamadaN₂ d t)) with hH
    have hHM : yamadaM₆ d t ≤ H := by
      intro m hm
      refine ⟨hMN hm, mem_centralizerMod_iff.2 ⟨hNY (hMN hm), fun z' hz' _ => ?_⟩⟩
      exact (h.elemModulo_yamadaM₆ hW d hK hQ m hm z' (hZM z' hz')).2
    have hHc : ⁅yamadaN₂ d t, yamadaN₂ d t⁆ ≤ H := by
      refine commutator_le.2 fun a ha b hb => ?_
      have habN : ⁅a, b⁆ ∈ yamadaN₂ d t :=
        (Subgroup.commutator_le_self _) (commutator_mem_commutator ha hb)
      refine ⟨habN, mem_centralizerMod_iff.2 ⟨hNY habN, fun z' hz' hz'N => ?_⟩⟩
      exact commutator_commutator_mem (Y := yamadaY₂ d t) (X := yamadaN₂ d t)
        (Z := centerMod (yamadaW₃ d t) (yamadaN₂ d t)) (W := yamadaW₃ d t) hNY
        (fun z'' hz'' => hNY (hZN z'' hz''))
        (fun x hx z'' hz'' => by
          have e : ⁅x, z''⁆ = (z'' * x * z''⁻¹ * x⁻¹)⁻¹ := by
            simp only [commutatorElement_def]; group
          rw [e]
          exact inv_mem (hzc' z'' hz'' x hx))
        (fun w hw x hx => hWY w hw x hx) a ha b hb z' hz'
    have hHN : yamadaN₂ d t ≤ H :=
      (N₂_eq_commutator_sup hW h d hK hQ hex).le.trans (sup_le hHc hHM)
    have hzY : z ∈ centerMod (yamadaY₂ d t) (yamadaN₂ d t) := by
      rw [mem_centerMod_iff hYN]
      refine ⟨hZN z hz0, hNY (hZN z hz0), fun a ha haN => ?_⟩
      have h1 := (mem_centralizerMod_iff.1 (hHN ha).2).2 z hz0 (hNY (hZN z hz0))
      have e : z * a * z⁻¹ * a⁻¹ = (a * z * a⁻¹ * z⁻¹)⁻¹ := by group
      rw [e]
      exact inv_mem h1
    rwa [centerMod_Y₂_eq hW h d hK hQ hex] at hzY
  · rw [mem_centerMod_iff hWN]
    refine ⟨hWN hw, Subgroup.le_normalizer hw, fun a ha haN => ?_⟩
    have := mul_mem hw ((mem_normalizer_iff.1 haN w⁻¹).1 (inv_mem hw))
    simpa [mul_assoc] using this

theorem Y₂_le_W₃ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaY₂ d t ≤ yamadaW₃ d t :=
  (h.yamada_5_46_1 hW d hK hQ).1

theorem inf_centralizerMod_eq (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d)
    {α : ↥(yamadaBarK₂ d t) ≃* SL(2, K)}
    (hex : ExactClosure (yamadaBarK₂ d t) α (yamadaT₂ d t) (yamadaBarP₂ d t) f) :
    yamadaN₂ d t ⊓ centralizerMod (yamadaW₃ d t) (yamadaM₆ d t) = yamadaM₆ d t := by
  have hMN := yamadaM₆_le_yamadaN₂ d t
  have hNM := N₂_le_normalizer_M₆ hW h d hK hQ
  have hNW := N₂_le_normalizer_W₃ hW h d hK hQ hex
  have ht := t_mem_normalizer_M₆ hW h d hK hQ
  have htW := Setup.Q44.t_mem_normalizer_W₃ hW h d hK (hQ.doubling)
  have hWN : yamadaW₃ d t ≤ yamadaN₂ d t := (h.yamadaW₃_le_yamadaM₆ hW d hK hQ).trans hMN
  have hMZ : yamadaM₆ d t ≤ yamadaN₂ d t ⊓ centralizerMod (yamadaW₃ d t) (yamadaM₆ d t) := by
    refine le_inf hMN fun m hm => mem_centralizerMod_iff.2 ⟨hNW (hMN hm), fun b hb _ => ?_⟩
    exact Y₂_le_W₃ hW h d hK hQ ((h.elemModulo_yamadaM₆ hW d hK hQ m hm b hb).2)
  rcases eq_M₆_or_eq_N₂ hW h d hK hQ hex hMZ inf_le_left
    (fun n hn z hz => ⟨conj_mem_N₂ hW h d hK hQ (hNM hn) hz.1,
      conj_mem_centralizerMod (hNW hn) (hNM hn) hz.2⟩)
    (fun z hz => ⟨conj_mem_N₂ hW h d hK hQ ht hz.1,
      conj_mem_centralizerMod htW ht hz.2⟩) with hZ | hZ
  · exact hZ
  · exfalso
    have hMW : yamadaM₆ d t ≤ yamadaW₃ d t := fun m hm => by
      rw [← centerMod_W₃_eq hW h d hK hQ hex, mem_centerMod_iff hWN]
      refine ⟨hMN hm, hNW (hMN hm), fun a ha haN => ?_⟩
      have haZ : a ∈ yamadaN₂ d t ⊓ centralizerMod (yamadaW₃ d t) (yamadaM₆ d t) := by
        rw [hZ]
        exact ha
      have h1 := (mem_centralizerMod_iff.1 haZ.2).2 m hm (hNW (hMN hm))
      have e : m * a * m⁻¹ * a⁻¹ = (a * m * a⁻¹ * m⁻¹)⁻¹ := by group
      rw [e]
      exact inv_mem h1
    exact not_M₆_le_F₅ hW h d hK hQ (hMW.trans (Setup.Q44.W₃_le_F₅ d t))

theorem centerMod_W₃_P_eq (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d)
    {α : ↥(yamadaBarK₂ d t) ≃* SL(2, K)}
    (hex : ExactClosure (yamadaBarK₂ d t) α (yamadaT₂ d t) (yamadaBarP₂ d t) f) :
    centerMod (yamadaW₃ d t) (yamadaP d t) = yamadaF₅ d t := by
  have hMP := h.yamadaM₆_le_yamadaP hW d hK hQ
  have hMN := yamadaM₆_le_yamadaN₂ d t
  have hPN := P_le_N₂ hW h d hK hQ hex
  have hNW := N₂_le_normalizer_W₃ hW h d hK hQ hex
  have hWF : yamadaW₃ d t ≤ yamadaF₅ d t := Setup.Q44.W₃_le_F₅ d t
  have hFM := h.yamadaF₅_le_yamadaM₆ hW d hK hQ
  have hWP : yamadaW₃ d t ≤ yamadaP d t := hWF.trans (hFM.trans hMP)
  have hYW := Y₂_le_W₃ hW h d hK hQ
  have hwW := Setup.Q44.wb_mem_normalizer_W₃ hW h d hK hQ
  have hFc : yamadaF₅ d t ≤ centerMod (yamadaW₃ d t) (yamadaP d t) := fun f₀ hf₀ => by
    rw [mem_centerMod_iff hWP]
    refine ⟨hMP (hFM hf₀), hNW (hPN (hMP (hFM hf₀))), fun a ha _ => ?_⟩
    exact hYW (((mem_F₅_iff hW h d hK hQ).1 hf₀).2 a ha)
  refine le_antisymm (fun g hg => ?_) hFc
  have hg' := (mem_centerMod_iff hWP).1 hg
  have hgM : g ∈ yamadaM₆ d t := by
    have : g ∈ yamadaN₂ d t ⊓ centralizerMod (yamadaW₃ d t) (yamadaM₆ d t) :=
      ⟨hPN hg'.1, mem_centralizerMod_iff.2 ⟨hg'.2.1, fun b hb hbN => hg'.2.2 b (hMP hb) hbN⟩⟩
    rwa [inf_centralizerMod_eq hW h d hK hQ hex] at this
  have hset := (h.yamada_5_44_2 hW d hK hQ).2.1
  have hgset : g ∈ ((yamadaM₆ d t : Subgroup G) : Set G) := hgM
  rw [hset] at hgset
  obtain ⟨f₀, hf₀, f', hf', hgf⟩ := Set.mem_mul.1 hgset
  have hf'g : f' = f₀⁻¹ * g := by rw [← hgf]; group
  have hf'c : f' ∈ centerMod (yamadaW₃ d t) (yamadaP d t) := by
    rw [hf'g]
    exact mul_mem (inv_mem (hFc hf₀)) hg
  set B' : Subgroup G := centerMod (yamadaW₃ d t) (yamadaP d t) ⊓
    (yamadaF₅ d t).map (MulAut.conj d.wb).toMonoidHom with hB'
  have hPF : yamadaP d t ≤ centralizerMod (yamadaW₃ d t) (yamadaF₅ d t) := fun p hp => by
    rw [mem_centralizerMod_iff]
    refine ⟨hNW (hPN hp), fun b hb _ => ?_⟩
    have := hYW (((mem_F₅_iff hW h d hK hQ).1 hb).2 p hp)
    have e : p * b * p⁻¹ * b⁻¹ = (b * p * b⁻¹ * p⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem this
  have hPB : yamadaP d t ≤ centralizerMod (yamadaW₃ d t) B' := fun p hp => by
    rw [mem_centralizerMod_iff]
    refine ⟨hNW (hPN hp), fun b hb hbN => ?_⟩
    have h1 := ((mem_centerMod_iff hWP).1 hb.1).2.2 p hp (hNW (hPN hp))
    have e : p * b * p⁻¹ * b⁻¹ = (b * p * b⁻¹ * p⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem h1
  have hPsB : (yamadaP d t).map (MulAut.conj d.wb).toMonoidHom ≤
      centralizerMod (yamadaW₃ d t) B' := by
    rintro _ ⟨p, hp, rfl⟩
    have h1 := conj_mem_centralizerMod_map hwW (hPF hp)
    exact centralizerMod_anti inf_le_right h1
  have hNB : yamadaN₂ d t ≤ centralizerMod (yamadaW₃ d t) B' := by
    rw [N₂_eq_P_sup hW h d hK hQ hex]
    exact sup_le hPB hPsB
  have hf'B : f' ∈ B' := ⟨hf'c, hf'⟩
  have hf'N : f' ∈ yamadaN₂ d t := hPN ((mem_centerMod_iff hWP).1 hf'c).1
  have hf'N₂ : f' ∈ centerMod (yamadaW₃ d t) (yamadaN₂ d t) := by
    rw [mem_centerMod_iff (hWP.trans hPN)]
    refine ⟨hf'N, hNW hf'N, fun a ha haN => ?_⟩
    have h1 := (mem_centralizerMod_iff.1 (hNB ha)).2 f' hf'B (hNW hf'N)
    have e : f' * a * f'⁻¹ * a⁻¹ = (a * f' * a⁻¹ * f'⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem h1
  rw [centerMod_W₃_eq hW h d hK hQ hex] at hf'N₂
  rw [← hgf]
  exact mul_mem hf₀ (hWF hf'N₂)

theorem mem_U₁_of_mem_inf_centralizer (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d)
    {α : ↥(yamadaBarK₂ d t) ≃* SL(2, K)}
    (hex : ExactClosure (yamadaBarK₂ d t) α (yamadaT₂ d t) (yamadaBarP₂ d t) f) {z : G}
    (hz : z ∈ yamadaN₂ d t ⊓ centralizer (yamadaN₂ d t : Set G)) : z ∈ yamadaU₁ d t := by
  obtain ⟨hzN, hzC⟩ := hz
  have hzY : z ∈ centerMod (yamadaY₂ d t) (yamadaN₂ d t) := by
    rw [mem_centerMod_iff (Y₂_le_N₂ hW h d hK hQ)]
    refine ⟨hzN, N₂_le_normalizer_Y₂ hW h d hK hQ hzN, fun a ha _ => ?_⟩
    have e : z * a * z⁻¹ * a⁻¹ = 1 := by
      rw [← commutatorElement_def]
      exact commutatorElement_eq_one_iff_mul_comm.2 (mem_centralizer_iff.1 hzC a ha).symm
    rw [e]
    exact one_mem _
  rw [centerMod_Y₂_eq hW h d hK hQ hex] at hzY
  have hzP : z ∈ yamadaP d t := (Setup.Q44.W₃_le_F₅ d t).trans
    ((h.yamadaF₅_le_yamadaM₆ hW d hK hQ).trans (h.yamadaM₆_le_yamadaP hW d hK hQ)) hzY
  refine (mem_U₁_iff hW h d hK hQ).2 ⟨hzP, fun g hg => ?_⟩
  rw [← commutatorElement_def]
  exact commutatorElement_eq_one_iff_mul_comm.2
    (mem_centralizer_iff.1 hzC g (P_le_N₂ hW h d hK hQ hex hg)).symm

theorem inf_centralizer_N₂_eq_bot (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d)
    {α : ↥(yamadaBarK₂ d t) ≃* SL(2, K)}
    (hex : ExactClosure (yamadaBarK₂ d t) α (yamadaT₂ d t) (yamadaBarP₂ d t) f) :
    yamadaN₂ d t ⊓ centralizer (yamadaN₂ d t : Set G) = ⊥ := by
  refine le_antisymm (fun z hz => ?_) bot_le
  have hD := hQ.doubling
  have hwN := wb_mem_normalizer_N₂ hW h d hK hQ
  have hU := mem_U₁_of_mem_inf_centralizer hW h d hK hQ hex hz
  have hz' : d.wb⁻¹ * z * d.wb ∈ yamadaN₂ d t ⊓ centralizer (yamadaN₂ d t : Set G) := by
    refine ⟨?_, ?_⟩
    · have := (mem_normalizer_iff.1 (inv_mem hwN) z).1 hz.1
      simpa using this
    · have := conj_mem_centralizer_of_mem_normalizer (inv_mem hwN) hz.2
      simpa using this
  have hU' := mem_U₁_of_mem_inf_centralizer hW h d hK hQ hex hz'
  have : z ∈ yamadaU₁ d t ⊓ (yamadaU₁ d t).map (MulAut.conj d.wb).toMonoidHom :=
    Subgroup.mem_inf.2 ⟨hU, mem_map_conj_iff.2 hU'⟩
  rw [h.yamadaU₁_inf_map_wb d hK hD] at this
  exact this

theorem centers (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d)
    {α : ↥(yamadaBarK₂ d t) ≃* SL(2, K)}
    (hex : ExactClosure (yamadaBarK₂ d t) α (yamadaT₂ d t) (yamadaBarP₂ d t) f) :
    yamadaN₂ d t ≤ normalizer (yamadaW₃ d t : Set G) ∧
      centerMod (yamadaY₂ d t) (yamadaN₂ d t) = yamadaW₃ d t ∧
      centerMod (yamadaW₃ d t) (yamadaN₂ d t) = yamadaW₃ d t ∧
      centerMod (yamadaW₃ d t) (yamadaP d t) = yamadaF₅ d t ∧
      yamadaN₂ d t ⊓ centralizerMod (yamadaW₃ d t) (yamadaM₆ d t) = yamadaM₆ d t ∧
      yamadaN₂ d t ⊓ centralizer (yamadaN₂ d t : Set G) = ⊥ :=
  ⟨N₂_le_normalizer_W₃ hW h d hK hQ hex, centerMod_Y₂_eq hW h d hK hQ hex,
    centerMod_W₃_eq hW h d hK hQ hex, centerMod_W₃_P_eq hW h d hK hQ hex,
    inf_centralizerMod_eq hW h d hK hQ hex, inf_centralizer_N₂_eq_bot hW h d hK hQ hex⟩

end Local

end SeriesCentersAux

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Local

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]


theorem yamadaN₂_centers (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d)
    (hsyl : IsSylowOf 2 (yamadaP d t) (yamadaN₂ d t)) {α : ↥(yamadaBarK₂ d t) ≃* SL(2, K)}
    (hex : ExactClosure (yamadaBarK₂ d t) α (yamadaT₂ d t) (yamadaBarP₂ d t) f) :
    yamadaN₂ d t ≤ normalizer (yamadaW₃ d t : Set G) ∧
      centerMod (yamadaY₂ d t) (yamadaN₂ d t) = yamadaW₃ d t ∧
      centerMod (yamadaW₃ d t) (yamadaN₂ d t) = yamadaW₃ d t ∧
      centerMod (yamadaW₃ d t) (yamadaP d t) = yamadaF₅ d t ∧
      yamadaN₂ d t ⊓ centralizerMod (yamadaW₃ d t) (yamadaM₆ d t) = yamadaM₆ d t ∧
      yamadaN₂ d t ⊓ centralizer (yamadaN₂ d t : Set G) = ⊥ :=
  SeriesCentersAux.centers hW h d hK hQ hex

end Local

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
