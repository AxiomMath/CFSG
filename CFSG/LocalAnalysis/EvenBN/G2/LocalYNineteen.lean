module

public import CFSG.LocalAnalysis.EvenBN.G2.LocalYEighteen

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.LocalAnalysis.EvenBN.Common (CosetData)
open scoped commutatorElement Pointwise

section Defs

variable
  {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]

@[expose] noncomputable def centralizerW₂Y₂ (d : G2Data L K) (t : G) : Subgroup G :=
  Common.centralizerMod (normalizer (yamadaV₂ d t : Set G) ⊓ normalizer (yamadaW₂ d t : Set G) ⊓
      normalizer (yamadaY₂ d t : Set G)) (yamadaW₂ d t) (yamadaY₂ d t)
    (fun _ hg y hy =>
      (mem_normalizer_iff.1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hg).1).2 y).1 hy)
    (fun _ hg y hy => (mem_normalizer_iff.1 (Subgroup.mem_inf.1 hg).2 y).1 hy)

@[expose] noncomputable def kernelTW₂ (d : G2Data L K) (t : G) : Subgroup G :=
  centralizerW₂Y₂ d t ⊓ normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G)

@[expose] noncomputable def translationsW₂ (d : G2Data L K) (t : G) : Subgroup G :=
  Common.centralizerMod (centralizerW₂Y₂ d t ⊓ normalizer (kernelTW₂ d t : Set G) ⊓
      normalizer (yamadaL₂ d t : Set G)) (kernelTW₂ d t) (yamadaL₂ d t)
    (fun _ hg y hy =>
      (mem_normalizer_iff.1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hg).1).2 y).1 hy)
    (fun _ hg y hy => (mem_normalizer_iff.1 (Subgroup.mem_inf.1 hg).2 y).1 hy)

end Defs

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Local

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

omit [Finite G] [Finite K] in
theorem W_mul_comm (d : G2Data L K) {u v : G} (hu : u ∈ d.W) (hv : v ∈ d.W) : u * v = v * u := by
  have hWab := d.isElementaryAbelian.2.2.2
  exact congrArg Subtype.val (mul_comm' (⟨u, hu⟩ : d.W) ⟨v, hv⟩)

omit [Finite G] [Finite K] in
theorem W_mul_self (d : G2Data L K) {u : G} (hu : u ∈ d.W) : u * u = 1 := by
  have hWab := d.isElementaryAbelian.2.2.2
  rw [← sq]
  exact CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := d.W) u hu

omit [Finite K] in
theorem W_le_normalizer_Y (d : G2Data L K) : d.W ≤ normalizer (d.Y : Set G) := fun a ha =>
  mem_normalizer_of_conj_mem fun y hy => by
    rw [W_mul_comm d ha (d.inclusions.2.2.1 hy), mul_inv_cancel_right]
    exact hy

theorem yamadaL₂_inf_leviB (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) :
    yamadaL₂ d t ⊓ d.leviB = ⊥ := by
  refine eq_bot_iff.2 fun x hx => ?_
  obtain ⟨hxL₂, hxB⟩ := Subgroup.mem_inf.1 hx
  have hxL : x ∈ L := d.image_le _ hxB
  have hxMt : x ∈ d.M ⊔ zpowers t := by
    rw [← (h.two_core_L₂ d hK).2.1]
    exact Subgroup.mem_inf.2 ⟨hxL₂, h.L_le_centralizer hxL⟩
  have hxM : x ∈ d.M := by
    rcases (h.mem_sup_zpowers_iff (d.image_le _)).1 hxMt with h1 | h1
    · exact h1
    · exfalso
      have := mul_mem (d.image_le _ h1) (inv_mem hxL)
      rw [mul_inv_cancel_right] at this
      exact h.t_not_mem_L this
  have hbot : d.M ⊓ d.leviB = ⊥ := by
    rw [G2Data.M, G2Data.leviB, ← d.image_inf, Model.M_inf_leviB, d.image_bot]
  rw [← hbot]
  exact Subgroup.mem_inf.2 ⟨hxM, hxB⟩

omit [Finite G] in
theorem eq_one_of_mem_leviB_of_commute (d : G2Data L K) (hK4 : 4 ≤ Nat.card K) {b : G}
    (hb : b ∈ d.leviB) (hc : ∀ b' ∈ d.leviB, b * b' = b' * b) : b = 1 := by
  have hB := Model.leviB_le_adjointGroup K
  obtain ⟨-, hsimp, -⟩ := g2RankOne_isPerfect_isSimpleGroup (K := K) hK4
  have : IsSimpleGroup (Model.leviB K) := hsimp
  have : IsSimpleGroup d.leviB := (d.imageEquiv hB).symm.isSimpleGroup
  obtain ⟨hperf, hne⟩ := d.leviB_perfect hK4
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center d.leviB) with hbot | htop
  · have hmem : (⟨b, hb⟩ : d.leviB) ∈ Subgroup.center d.leviB :=
      Subgroup.mem_center_iff.2 fun g => Subtype.ext (hc g g.2).symm
    rw [hbot, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  · exfalso
    apply hne
    rw [← hperf, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [mem_centralizer_iff]
    intro y hy
    have hmem : (⟨x, hx⟩ : d.leviB) ∈ Subgroup.center d.leviB := by
      rw [htop]
      exact Subgroup.mem_top _
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hmem ⟨y, hy⟩)

omit [Finite G] [Finite K] in
theorem centralizerW₂Y₂_le (d : G2Data L K) (t : G) :
    centralizerW₂Y₂ d t ≤ normalizer (yamadaV₂ d t : Set G) := fun _ hg =>
  (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (Common.mem_centralizerMod.1 hg).1).1).1

theorem mem_centralizerW₂Y₂_iff (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) {g : G} :
    g ∈ centralizerW₂Y₂ d t ↔ g ∈ normalizer (yamadaV₂ d t : Set G) ∧
      ∀ w ∈ yamadaW₂ d t, g * w * g⁻¹ * w⁻¹ ∈ yamadaY₂ d t := by
  rw [centralizerW₂Y₂, Common.mem_centralizerMod]
  refine ⟨fun ⟨hg, h2⟩ => ⟨(Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hg).1).1, h2⟩,
    fun ⟨hg, h2⟩ => ⟨?_, h2⟩⟩
  exact Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hg, (h.normalizer_yamadaV₂_le hW d hK hD).1 hg⟩,
    h.normalizer_yamadaV₂_le_normalizer_yamadaY₂ hW d hK hD hg⟩

theorem normalizer_le_normalizer_centralizerW₂Y₂ (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    normalizer (yamadaV₂ d t : Set G) ≤ normalizer (centralizerW₂Y₂ d t : Set G) := fun _ hg =>
  mem_normalizer_of_conj_mem fun _ hx => Common.conj_mem_centralizerMod
    (Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hg, (h.normalizer_yamadaV₂_le hW d hK hD).1 hg⟩,
      h.normalizer_yamadaV₂_le_normalizer_yamadaY₂ hW d hK hD hg⟩) hx

theorem mem_centralizerW₂Y₂_of (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) {g : G}
    (hg : g ∈ normalizer (yamadaV₂ d t : Set G))
    (hgW : ∀ a ∈ d.W, g * a * g⁻¹ * a⁻¹ ∈ yamadaY₂ d t) : g ∈ centralizerW₂Y₂ d t := by
  refine (h.mem_centralizerW₂Y₂_iff hW d hK hD).2 ⟨hg, fun w hw => ?_⟩
  have hgY₂ := h.normalizer_yamadaV₂_le_normalizer_yamadaY₂ hW d hK hD hg
  obtain ⟨a, ha, y, hy, rfl⟩ :=
    Common.exists_mul_of_le_normalizer (h.yamadaY₂_le_normalizer_W d hK hD) w hw
  have h1 : g * y * g⁻¹ * y⁻¹ ∈ yamadaY₂ d t :=
    mul_mem ((mem_normalizer_iff.1 hgY₂ y).1 hy) (inv_mem hy)
  have h2 : a * (g * y * g⁻¹ * y⁻¹) * a⁻¹ ∈ yamadaY₂ d t := by
    rw [← mem_centralizer_iff.1 (h.W_le_centralizer_yamadaY₂ d hK hD ha) _ h1,
      mul_inv_cancel_right]
    exact h1
  rw [show g * (a * y) * g⁻¹ * (a * y)⁻¹ =
    (g * a * g⁻¹ * a⁻¹) * (a * (g * y * g⁻¹ * y⁻¹) * a⁻¹) by group]
  exact mul_mem (hgW a ha) h2

theorem crossed_mul_mem_Y (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) {x g : G}
    (hx : x ∈ centralizerW₂Y₂ d t) (hg : g ∈ normalizer (yamadaV₂ d t : Set G)) :
    ∃ y ∈ d.Y, t * (x * g) * t * (x * g)⁻¹ = (t * x * t * x⁻¹) * (t * g * t * g⁻¹) * y := by
  obtain ⟨hxV, hxW₂⟩ := (h.mem_centralizerW₂Y₂_iff hW d hK hD).1 hx
  have hxW := (h.normalizer_yamadaV₂_le hW d hK hD).2.2 hxV
  have hκ := h.crossed_mem_W hW d hK hD hg
  rw [h.crossed_mul' x g]
  generalize t * g * t * g⁻¹ = a at hκ ⊢
  generalize t * x * t * x⁻¹ = b
  have hz : x * a * x⁻¹ * a⁻¹ ∈ d.Y := by
    rw [← h.W_inf_yamadaY₂ d hK hD]
    exact Subgroup.mem_inf.2 ⟨mul_mem ((mem_normalizer_iff.1 hxW a).1 hκ) (inv_mem hκ),
      hxW₂ a ((le_sup_left : d.W ≤ yamadaW₂ d t) hκ)⟩
  refine ⟨x * a * x⁻¹ * a⁻¹, hz, ?_⟩
  have hcomm : a * (x * a * x⁻¹ * a⁻¹) = (x * a * x⁻¹ * a⁻¹) * a :=
    W_mul_comm d hκ (d.inclusions.2.2.1 hz)
  calc b * (x * a * x⁻¹) = b * ((x * a * x⁻¹ * a⁻¹) * a) := by group
    _ = b * (a * (x * a * x⁻¹ * a⁻¹)) := by rw [hcomm]
    _ = b * a * (x * a * x⁻¹ * a⁻¹) := by group

theorem yamadaL₂_le_centralizerW₂Y₂ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaL₂ d t ≤ centralizerW₂Y₂ d t := by
  have h4K : 4 ≤ Nat.card K := hK ▸ h.four_le
  obtain ⟨-, -, -, -, hWF, hFD, -, hDS, hMS, -⟩ := d.inclusions
  have hL₂V : yamadaL₂ d t ≤ normalizer (yamadaV₂ d t : Set G) :=
    (yamadaL₂_le d t).trans (h.normalizer_tY_le d hK hD).2.2
  have hWY := h.W_le_centralizer_yamadaY₂ d hK hD
  rw [h.yamadaL₂_eq_sup d hK hD] at hL₂V ⊢
  refine sup_le (sup_le (fun m hm => ?_) (fun y hy => ?_)) ((zpowers_le).2 ?_)
  · refine h.mem_centralizerW₂Y₂_of hW d hK hD (hL₂V (mem_sup_left (mem_sup_left hm)))
      fun a ha => ?_
    have := (d.mem_F_iff_commutator (by omega) (hDS (hFD (hWF ha)))).1 (hWF ha) m (hMS hm)
    rw [show m * a * m⁻¹ * a⁻¹ = ⁅a, m⁆⁻¹ by rw [commutatorElement_def]; group]
    exact h.Y_le_yamadaY₂ d hK hD (inv_mem this)
  · refine h.mem_centralizerW₂Y₂_of hW d hK hD (hL₂V (mem_sup_left (mem_sup_right hy)))
      fun a ha => ?_
    rw [mem_centralizer_iff.1 (hWY ha) y hy, mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _
  · refine h.mem_centralizerW₂Y₂_of hW d hK hD (hL₂V (mem_sup_right (mem_zpowers t)))
      fun a ha => ?_
    rw [← mem_centralizer_singleton_iff.1 (h.L_le_centralizer (d.image_le _ ha)),
      mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _

theorem yamadaR₃star_le_centralizerW₂Y₂ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaR₃star d t ≤ centralizerW₂Y₂ d t := fun g hg => by
  obtain ⟨-, -, -, -, hWF, -⟩ := d.inclusions
  refine h.mem_centralizerW₂Y₂_of hW d hK hD
    (Subgroup.mem_inf.1 (h.yamadaR₃star_le_normalizer hW d hK hD hg)).1 fun a ha => ?_
  have := (h.commutator_mem_of_mem_yamadaRstar d hK hD (Subgroup.mem_inf.1 hg).1).2 a
    (mem_sup_left (hWF ha))
  exact (sup_le (h.Y_le_yamadaY₂ d hK hD) (yamadaU₁_le_yamadaY₂ d t)) this

theorem exists_mem_centralizerW₂Y₂_crossed_eq (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d)
    {w : G} (hw : w ∈ d.W) : ∃ x ∈ centralizerW₂Y₂ d t, t * x * t * x⁻¹ = w := by
  obtain ⟨g, hg, l, hl, e⟩ := h.exists_conj_t_eq_mul_of_mem_W hW d hK hD hw
  refine ⟨g * l, mul_mem (h.yamadaR₃star_le_centralizerW₂Y₂ hW d hK hD hg)
    (h.yamadaL₂_le_centralizerW₂Y₂ hW d hK hD hl), ?_⟩
  rw [show t * (g * l) * t * (g * l)⁻¹ = t * (g * l * t * (g * l)⁻¹) by group, e, ← mul_assoc,
    h.t_mul_t, one_mul]

theorem normalizer_le_normalizer_kernelTW₂ (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    normalizer (yamadaV₂ d t : Set G) ≤ normalizer (kernelTW₂ d t : Set G) := fun g hg => by
  have hgX := h.normalizer_le_normalizer_centralizerW₂Y₂ hW d hK hD hg
  have hgY := h.normalizer_yamadaV₂_le_normalizer_Y hW d hK hD hg
  refine mem_normalizer_of_conj_mem fun k hk => ?_
  obtain ⟨hkX, hkN⟩ := Subgroup.mem_inf.1 hk
  have hkV := centralizerW₂Y₂_le d t hkX
  have hx : g * k * g⁻¹ ∈ centralizerW₂Y₂ d t := (mem_normalizer_iff.1 hgX k).1 hkX
  refine Subgroup.mem_inf.2 ⟨hx, (h.crossed_mem_Y_iff hW d hK hD (centralizerW₂Y₂_le d t hx)).1 ?_⟩
  obtain ⟨y₁, hy₁, e₁⟩ := h.crossed_mul_mem_Y hW d hK hD hx hg
  have hκk := (h.crossed_mem_Y_iff hW d hK hD hkV).2 hkN
  have hy₂ : g * (t * k * t * k⁻¹) * g⁻¹ ∈ d.Y := (mem_normalizer_iff.1 hgY _).1 hκk
  have hκg := h.crossed_mem_W hW d hK hD hg
  rw [show g * k * g⁻¹ * g = g * k by group, h.crossed_mul' g k] at e₁
  generalize t * (g * k * g⁻¹) * t * (g * k * g⁻¹)⁻¹ = b at e₁ ⊢
  generalize t * g * t * g⁻¹ = c at e₁ hκg
  generalize g * (t * k * t * k⁻¹) * g⁻¹ = y₂ at e₁ hy₂
  have hc : c * (y₂ * y₁⁻¹) = (y₂ * y₁⁻¹) * c :=
    W_mul_comm d hκg (d.inclusions.2.2.1 (mul_mem hy₂ (inv_mem hy₁)))
  have hb : b = y₂ * y₁⁻¹ := by
    calc b = b * c * y₁ * y₁⁻¹ * c⁻¹ := by group
      _ = c * y₂ * y₁⁻¹ * c⁻¹ := by rw [← e₁]
      _ = c * (y₂ * y₁⁻¹) * c⁻¹ := by group
      _ = (y₂ * y₁⁻¹) * c * c⁻¹ := by rw [hc]
      _ = y₂ * y₁⁻¹ := by group
  rw [hb]
  exact mul_mem hy₂ (inv_mem hy₁)

theorem yamadaL₂_le_kernelTW₂ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaL₂ d t ≤ kernelTW₂ d t :=
  le_inf (h.yamadaL₂_le_centralizerW₂Y₂ hW d hK hD) (yamadaL₂_le d t)

theorem normalizer_le_normalizer_yamadaL₂ (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    normalizer (yamadaV₂ d t : Set G) ≤ normalizer (yamadaL₂ d t : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : kernelTW₂ d t ≤ normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G) := inf_le_right
  have hHV := (h.normalizer_tY_le d hK hD).2.2
  have hNK := h.normalizer_le_normalizer_kernelTW₂ hW d hK hD
  have hpc : (CFSG.Open.pCore 2 (kernelTW₂ d t)).Characteristic :=
    LieType.BorelTits.pCore_characteristic 2
  have hNP : normalizer (kernelTW₂ d t : Set G) ≤
      normalizer (pCoreOf 2 (kernelTW₂ d t) : Set G) :=
    LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (CFSG.Open.pCore 2 (kernelTW₂ d t))
  have heq : pCoreOf 2 (kernelTW₂ d t) = yamadaL₂ d t := by
    apply le_antisymm
    · exact LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((LieType.BorelTits.pCoreOf_le 2 _).trans hKH) ((hHV.trans hNK).trans hNP)
        (LieType.BorelTits.pCoreOf_isPGroup 2 _)
    · exact LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (h.yamadaL₂_le_kernelTW₂ hW d hK hD)
        (hKH.trans (le_normalizer_yamadaL₂ d t)) (LieType.BorelTits.pCoreOf_isPGroup 2 _)
  rw [← heq]
  exact hNK.trans hNP

theorem leviB_le_kernelTW₂ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    d.leviB ≤ kernelTW₂ d t := fun b hb => by
  have hbN := h.centralizer_inf_normalizer_Y_le d (h.leviB_le_centralizer_inf_normalizer_Y d hb)
  refine Subgroup.mem_inf.2 ⟨h.mem_centralizerW₂Y₂_of hW d hK hD
    ((h.normalizer_tY_le d hK hD).2.2 hbN) fun a ha => ?_, hbN⟩
  have hbL : b ∈ normalizer (L : Set G) := Subgroup.le_normalizer (d.image_le _ hb)
  have hsec := (d.act_sectionCentralizer_eq Model.Y_le_W (Model.yamada_3_23_W_Y hK h.two_le)
    hbL).2 (mem_sup_left (d.image_mono le_sup_right hb)) a ha
  have := (mem_normalizer_iff.1 (W_le_normalizer_Y d ha) _).1 hsec
  rw [show a * (a⁻¹ * (b * a * b⁻¹)) * a⁻¹ = b * a * b⁻¹ * a⁻¹ by group] at this
  exact h.Y_le_yamadaY₂ d hK hD this

theorem kernelTW₂_le (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    kernelTW₂ d t ≤ yamadaL₂ d t ⊔ d.leviB := by
  intro k hk
  obtain ⟨hkX, hkN⟩ := Subgroup.mem_inf.1 hk
  have hk' : k ∈ ((normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G) : Subgroup G) :
      Set G) := hkN
  rw [(h.yamada_5_5_1 d hK).2.2.1] at hk'
  obtain ⟨l, hl, c, hc, rfl⟩ := Set.mem_mul.1 hk'
  obtain ⟨hct, -⟩ := Subgroup.mem_inf.1 hc
  have hcX : c ∈ centralizerW₂Y₂ d t := by
    have := mul_mem (inv_mem (h.yamadaL₂_le_centralizerW₂Y₂ hW d hK hD hl)) hkX
    rwa [inv_mul_cancel_left] at this
  have hcW := (h.centralizer_inf_normalizer_Y_le_W d hK hD).1 hc
  have hcL := h.centralizer_le_normalizer hct
  have hsec : ∀ y ∈ d.image (Model.W K), y⁻¹ * (c * y * c⁻¹) ∈ d.image (Model.Y K) :=
    fun a ha => by
      have h1 : c * a * c⁻¹ * a⁻¹ ∈ d.Y := by
        rw [← h.W_inf_yamadaY₂ d hK hD]
        exact Subgroup.mem_inf.2 ⟨mul_mem ((mem_normalizer_iff.1 hcW a).1 ha) (inv_mem ha),
          ((h.mem_centralizerW₂Y₂_iff hW d hK hD).1 hcX).2 a
            ((le_sup_left : d.W ≤ yamadaW₂ d t) ha)⟩
      have h2 := (mem_normalizer_iff.1 (inv_mem (W_le_normalizer_Y d ha)) _).1 h1
      rwa [show a⁻¹ * (c * a * c⁻¹ * a⁻¹) * a⁻¹⁻¹ = a⁻¹ * (c * a * c⁻¹) by group] at h2
  have hc' := (d.act_sectionCentralizer_eq Model.Y_le_W (Model.yamada_3_23_W_Y hK h.two_le)
    hcL).1 hsec
  rw [d.image_sup Model.M_le_adjointGroup (Model.leviB_le_adjointGroup K)] at hc'
  have hML : d.M ⊔ d.leviB ≤ L := sup_le (d.image_le _) (d.image_le _)
  have hZ : centralizer (L : Set G) ≤ normalizer ((d.M ⊔ d.leviB : Subgroup G) : Set G) :=
    fun z hz => mem_normalizer_of_conj_mem fun x hx => by
      rw [← mem_centralizer_iff.1 hz x (hML hx), mul_inv_cancel_right]
      exact hx
  obtain ⟨a', ha', z, hz, rfl⟩ := Common.exists_mul_of_le_normalizer hZ c hc'
  have hzt : z ∈ centralizer ({t} : Set G) := by
    have := mul_mem (inv_mem (h.L_le_centralizer (hML ha'))) hct
    rwa [inv_mul_cancel_left] at this
  have hzt' : z ∈ zpowers t := by
    rw [← h.centralizer_L_inf]
    exact Subgroup.mem_inf.2 ⟨hz, hzt⟩
  have hML₂ : d.M ≤ yamadaL₂ d t := le_sup_left.trans (h.tM_le_yamadaL₂ d hK)
  have htL₂ : t ∈ yamadaL₂ d t := h.tM_le_yamadaL₂ d hK (mem_sup_right (mem_zpowers t))
  exact mul_mem (mem_sup_left hl) (mul_mem ((sup_le_sup_right hML₂ _) ha')
    (mem_sup_left ((zpowers_le.2 htL₂) hzt')))

theorem J₄_le_normalizer_tY (h : Setup G L f t) (d : G2Data L K) :
    d.J₄ ≤ normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G) := fun j hj => by
  have hj' : j ∈ L ⊓ normalizer (d.Y : Set G) := by
    rw [(d.yamada_3_13_3_G).1]
    exact mem_sup_right (mem_sup_right hj)
  exact h.centralizer_inf_normalizer_Y_le d (Subgroup.mem_inf.2
    ⟨h.L_le_centralizer (Subgroup.mem_inf.1 hj').1, (Subgroup.mem_inf.1 hj').2⟩)

theorem J₄_commutator_mem_yamadaL₂ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) {j k : G} (hj : j ∈ d.J₄)
    (hk : k ∈ kernelTW₂ d t) : j * k * j⁻¹ * k⁻¹ ∈ yamadaL₂ d t := by
  obtain ⟨-, -, -, hJB, -⟩ := d.yamada_3_13_3_G
  have hjL₂ : j ∈ normalizer (yamadaL₂ d t : Set G) :=
    le_normalizer_yamadaL₂ d t (h.J₄_le_normalizer_tY d hj)
  have hBL₂ : d.leviB ≤ normalizer (yamadaL₂ d t : Set G) := fun b hb =>
    le_normalizer_yamadaL₂ d t (Subgroup.mem_inf.1 (h.leviB_le_kernelTW₂ hW d hK hD hb)).2
  obtain ⟨l, hl, b, hb, rfl⟩ :=
    Common.exists_mul_of_le_normalizer hBL₂ k (h.kernelTW₂_le hW d hK hD hk)
  have hjb : b * j = j * b := mem_centralizer_iff.1 (hJB hj) b hb
  have hjb' : b * j⁻¹ = j⁻¹ * b := by
    calc b * j⁻¹ = j⁻¹ * (j * b) * j⁻¹ := by group
      _ = j⁻¹ * (b * j) * j⁻¹ := by rw [hjb]
      _ = j⁻¹ * b := by group
  have := mul_mem ((mem_normalizer_iff.1 hjL₂ l).1 hl) (inv_mem hl)
  rw [show j * (l * b) * j⁻¹ * (l * b)⁻¹ = j * l * (b * j⁻¹) * b⁻¹ * l⁻¹ by group, hjb',
    show j * l * (j⁻¹ * b) * b⁻¹ * l⁻¹ = j * l * j⁻¹ * l⁻¹ by group]
  exact this

theorem mem_translationsW₂_iff (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) {g : G} :
    g ∈ translationsW₂ d t ↔ g ∈ centralizerW₂Y₂ d t ∧
      ∀ k ∈ kernelTW₂ d t, g * k * g⁻¹ * k⁻¹ ∈ yamadaL₂ d t := by
  rw [translationsW₂, Common.mem_centralizerMod]
  have hXV := centralizerW₂Y₂_le d t
  refine ⟨fun ⟨hg, h2⟩ => ⟨(Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hg).1).1, h2⟩,
    fun ⟨hg, h2⟩ => ⟨?_, h2⟩⟩
  exact Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hg,
    h.normalizer_le_normalizer_kernelTW₂ hW d hK hD (hXV hg)⟩,
    h.normalizer_le_normalizer_yamadaL₂ hW d hK hD (hXV hg)⟩

theorem normalizer_le_normalizer_translationsW₂ (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    normalizer (yamadaV₂ d t : Set G) ≤ normalizer (translationsW₂ d t : Set G) := fun g hg => by
  refine mem_normalizer_of_conj_mem fun x hx => ?_
  obtain ⟨hxX, hxK⟩ := (h.mem_translationsW₂_iff hW d hK hD).1 hx
  have hgK := h.normalizer_le_normalizer_kernelTW₂ hW d hK hD hg
  have hgL₂ := h.normalizer_le_normalizer_yamadaL₂ hW d hK hD hg
  refine (h.mem_translationsW₂_iff hW d hK hD).2 ⟨(mem_normalizer_iff.1
    (h.normalizer_le_normalizer_centralizerW₂Y₂ hW d hK hD hg) x).1 hxX, fun k hk => ?_⟩
  have hk' : g⁻¹ * k * g ∈ kernelTW₂ d t := by
    have := (mem_normalizer_iff.1 (inv_mem hgK) k).1 hk
    rwa [inv_inv] at this
  have := (mem_normalizer_iff.1 hgL₂ _).1 (hxK _ hk')
  rwa [show g * (x * (g⁻¹ * k * g) * x⁻¹ * (g⁻¹ * k * g)⁻¹) * g⁻¹ =
    g * x * g⁻¹ * k * (g * x * g⁻¹)⁻¹ * k⁻¹ by group] at this

theorem yamadaL₂_le_translationsW₂ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaL₂ d t ≤ translationsW₂ d t := fun l hl => by
  refine (h.mem_translationsW₂_iff hW d hK hD).2
    ⟨h.yamadaL₂_le_centralizerW₂Y₂ hW d hK hD hl, fun k hk => ?_⟩
  have hkL₂ : k ∈ normalizer (yamadaL₂ d t : Set G) :=
    le_normalizer_yamadaL₂ d t (Subgroup.mem_inf.1 hk).2
  have := (mem_normalizer_iff.1 hkL₂ l⁻¹).1 (inv_mem hl)
  rw [show l * k * l⁻¹ * k⁻¹ = l * (k * l⁻¹ * k⁻¹) by group]
  exact mul_mem hl this

theorem translationsW₂_inf_kernelTW₂_le (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    translationsW₂ d t ⊓ kernelTW₂ d t ≤ yamadaL₂ d t := by
  have h4K : 4 ≤ Nat.card K := hK ▸ h.four_le
  have hK4 : 4 ≤ Nat.card K := by omega
  have hBK := h.leviB_le_kernelTW₂ hW d hK hD
  have hBL₂ : d.leviB ≤ normalizer (yamadaL₂ d t : Set G) := fun b hb =>
    le_normalizer_yamadaL₂ d t (Subgroup.mem_inf.1 (hBK hb)).2
  intro x hx
  obtain ⟨hxP, hxK⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨-, hxc⟩ := (h.mem_translationsW₂_iff hW d hK hD).1 hxP
  obtain ⟨l, hl, b, hb, rfl⟩ :=
    Common.exists_mul_of_le_normalizer hBL₂ x (h.kernelTW₂_le hW d hK hD hxK)
  suffices hb1 : b = 1 by
    rw [hb1, mul_one]
    exact hl
  refine eq_one_of_mem_leviB_of_commute d hK4 hb fun b' hb' => ?_
  have h1 := hxc b' (hBK hb')
  have hc : b * b' * b⁻¹ ∈ d.leviB := mul_mem (mul_mem hb hb') (inv_mem hb)
  have h2 : l * (b * b' * b⁻¹) * l⁻¹ * (b * b' * b⁻¹)⁻¹ ∈ yamadaL₂ d t := by
    have := (mem_normalizer_iff.1 (hBL₂ hc) l⁻¹).1 (inv_mem hl)
    rw [show l * (b * b' * b⁻¹) * l⁻¹ * (b * b' * b⁻¹)⁻¹ =
      l * ((b * b' * b⁻¹) * l⁻¹ * (b * b' * b⁻¹)⁻¹) by group]
    exact mul_mem hl this
  have h3 : b * b' * b⁻¹ * b'⁻¹ ∈ yamadaL₂ d t := by
    have := mul_mem (inv_mem h2) h1
    rwa [show (l * (b * b' * b⁻¹) * l⁻¹ * (b * b' * b⁻¹)⁻¹)⁻¹ *
      (l * b * b' * (l * b)⁻¹ * b'⁻¹) = b * b' * b⁻¹ * b'⁻¹ by group] at this
  have h5 : b * b' * b⁻¹ * b'⁻¹ ∈ (⊥ : Subgroup G) := by
    rw [← h.yamadaL₂_inf_leviB d hK]
    exact Subgroup.mem_inf.2 ⟨h3, mul_mem hc (inv_mem hb')⟩
  rw [Subgroup.mem_bot] at h5
  calc b * b' = b * b' * b⁻¹ * b'⁻¹ * (b' * b) := by group
    _ = b' * b := by rw [h5, one_mul]

theorem isPGroup_translationsW₂ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    IsPGroup 2 (translationsW₂ d t) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL₂p : IsPGroup 2 (yamadaL₂ d t) := LieType.BorelTits.pCoreOf_isPGroup 2 _
  intro p
  obtain ⟨hpX, -⟩ := (h.mem_translationsW₂_iff hW d hK hD).1 p.2
  have hpV := centralizerW₂Y₂_le d t hpX
  obtain ⟨y, hy, e⟩ := h.crossed_mul_mem_Y hW d hK hD hpX hpV
  have hκ2 : t * ((p : G) * p) * t * ((p : G) * p)⁻¹ ∈ d.Y := by
    rw [e, W_mul_self d (h.crossed_mem_W hW d hK hD hpV), one_mul]
    exact hy
  have hp2K : (p : G) * p ∈ kernelTW₂ d t := Subgroup.mem_inf.2 ⟨mul_mem hpX hpX,
    (h.crossed_mem_Y_iff hW d hK hD (mul_mem hpV hpV)).1 hκ2⟩
  have hp2L₂ := h.translationsW₂_inf_kernelTW₂_le hW d hK hD
    (Subgroup.mem_inf.2 ⟨mul_mem p.2 p.2, hp2K⟩)
  obtain ⟨n, hn⟩ := hL₂p ⟨_, hp2L₂⟩
  refine ⟨n + 1, Subtype.ext ?_⟩
  have hn' := congrArg Subtype.val hn
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at hn' ⊢
  rw [pow_succ', pow_mul, sq]
  exact hn'

theorem J₄_commutator_mem_translationsW₂ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) {j x : G} (hj : j ∈ d.J₄)
    (hx : x ∈ centralizerW₂Y₂ d t) : j * x * j⁻¹ * x⁻¹ ∈ translationsW₂ d t := by
  have hjV := (h.normalizer_tY_le d hK hD).2.2 (h.J₄_le_normalizer_tY d hj)
  have hxV := centralizerW₂Y₂_le d t hx
  have hxK := h.normalizer_le_normalizer_kernelTW₂ hW d hK hD hxV
  have hxL₂ := h.normalizer_le_normalizer_yamadaL₂ hW d hK hD hxV
  have hjL₂ := h.normalizer_le_normalizer_yamadaL₂ hW d hK hD hjV
  have hjX : j * x * j⁻¹ ∈ centralizerW₂Y₂ d t :=
    (mem_normalizer_iff.1 (h.normalizer_le_normalizer_centralizerW₂Y₂ hW d hK hD hjV) x).1 hx
  refine (h.mem_translationsW₂_iff hW d hK hD).2 ⟨mul_mem hjX (inv_mem hx), fun k hk => ?_⟩
  have hk₁ : x⁻¹ * k * x ∈ kernelTW₂ d t := by
    have := (mem_normalizer_iff.1 (inv_mem hxK) k).1 hk
    rwa [inv_inv] at this
  have hℓ₁ := h.J₄_commutator_mem_yamadaL₂ hW d hK hD (inv_mem hj) hk₁
  have hℓ₂ := (mem_normalizer_iff.1 hxL₂ _).1 hℓ₁
  have hℓ₃ := (mem_normalizer_iff.1 hjL₂ _).1 hℓ₂
  have := mul_mem hℓ₃ (h.J₄_commutator_mem_yamadaL₂ hW d hK hD hj hk)
  rwa [show j * (x * (j⁻¹ * (x⁻¹ * k * x) * j⁻¹⁻¹ * (x⁻¹ * k * x)⁻¹) * x⁻¹) * j⁻¹ *
    (j * k * j⁻¹ * k⁻¹) = j * x * j⁻¹ * x⁻¹ * k * (j * x * j⁻¹ * x⁻¹)⁻¹ * k⁻¹ by group] at this

theorem exists_mem_translationsW₂_crossed (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) {w : G} (hw : w ∈ d.W) :
    ∃ p ∈ translationsW₂ d t, ∃ y ∈ d.Y, t * p * t * p⁻¹ = w * y := by
  have h4K : 4 ≤ Nat.card K := hK ▸ h.four_le
  have hYW := d.inclusions.2.2.1
  have hRW : d.rootGroup g2v ≤ d.W := by
    rw [← (d.yamada_defs).2.2.1]
    exact le_sup_left
  have hA : ∀ a ∈ d.rootGroup g2v, a ≠ 1 → ∀ r ∈ d.rootGroup g2v, r ≠ a →
      ∃ p ∈ translationsW₂ d t, ∃ y ∈ d.Y, t * p * t * p⁻¹ = r * y := by
    intro a ha ha1 r hr hra
    have hra1 : r * a ≠ 1 := fun e => hra (by
      calc r = r * a * a := by rw [mul_assoc, W_mul_self d (hRW ha), mul_one]
        _ = a := by rw [e, one_mul])
    obtain ⟨j, hj, hja⟩ := ((d.yamada_3_9_2_G (i := 3) (k := 1) (by decide)).2
      (Or.inr (by decide))).2 a ha ha1 (r * a) (mul_mem hr ha) hra1
    have hj4 : j ∈ d.J₄ := hj
    obtain ⟨x, hx, hκx⟩ := h.exists_mem_centralizerW₂Y₂_crossed_eq hW d hK hD (hRW ha)
    have hxV := centralizerW₂Y₂_le d t hx
    have hjV := (h.normalizer_tY_le d hK hD).2.2 (h.J₄_le_normalizer_tY d hj4)
    have hjX : j * x * j⁻¹ ∈ centralizerW₂Y₂ d t :=
      (mem_normalizer_iff.1 (h.normalizer_le_normalizer_centralizerW₂Y₂ hW d hK hD hjV) x).1 hx
    obtain ⟨y₁, hy₁, e₁⟩ := h.crossed_mul_mem_Y hW d hK hD hjX (inv_mem hxV)
    have hjt : j * t = t * j :=
      mem_centralizer_singleton_iff.1 (h.L_le_centralizer (d.image_le _ hj4))
    have hjt' : j⁻¹ * t * j = t := by rw [mul_assoc, ← hjt, inv_mul_cancel_left]
    have e₂ : t * (j * x * j⁻¹) * t * (j * x * j⁻¹)⁻¹ = r * a := by
      calc t * (j * x * j⁻¹) * t * (j * x * j⁻¹)⁻¹ =
            t * j * x * (j⁻¹ * t * j) * x⁻¹ * j⁻¹ := by group
        _ = j * t * x * t * x⁻¹ * j⁻¹ := by rw [hjt', ← hjt]
        _ = j * (t * x * t * x⁻¹) * j⁻¹ := by group
        _ = r * a := by rw [hκx, hja]
    have hz : x⁻¹ * a⁻¹ * x * a ∈ d.Y := by
      obtain ⟨hx'V, hx'W₂⟩ := (h.mem_centralizerW₂Y₂_iff hW d hK hD).1 (inv_mem hx)
      have hx'W := (h.normalizer_yamadaV₂_le hW d hK hD).2.2 hx'V
      have haW := hRW ha
      rw [← h.W_inf_yamadaY₂ d hK hD]
      refine Subgroup.mem_inf.2 ⟨mul_mem ?_ haW, ?_⟩
      · have := (mem_normalizer_iff.1 hx'W a⁻¹).1 (inv_mem haW)
        rwa [inv_inv] at this
      · have := hx'W₂ a⁻¹ ((le_sup_left : d.W ≤ yamadaW₂ d t) (inv_mem haW))
        rwa [inv_inv, inv_inv] at this
    have hp := h.J₄_commutator_mem_translationsW₂ hW d hK hD hj4 hx
    refine ⟨j * x * j⁻¹ * x⁻¹, hp, (x⁻¹ * a⁻¹ * x * a) * y₁, mul_mem hz hy₁, ?_⟩
    rw [e₁, e₂, h.crossed_inv' x, hκx]
    have hc : a * (x⁻¹ * a⁻¹ * x * a) = (x⁻¹ * a⁻¹ * x * a) * a :=
      W_mul_comm d (hRW ha) (hYW hz)
    calc r * a * (x⁻¹ * a⁻¹ * x) * y₁ = r * (a * (x⁻¹ * a⁻¹ * x * a)) * a⁻¹ * y₁ := by group
      _ = r * ((x⁻¹ * a⁻¹ * x * a) * a) * a⁻¹ * y₁ := by rw [hc]
      _ = r * (x⁻¹ * a⁻¹ * x * a * y₁) := by group
  obtain ⟨c, hc0, hc1⟩ : ∃ c : K, c ≠ 0 ∧ c ≠ 1 := by
    by_contra hcon
    have hcon' : ∀ c : K, c ≠ 0 → c = 1 := fun c hc0 => by
      by_contra hc1
      exact hcon ⟨c, hc0, hc1⟩
    have hsurj : Function.Surjective (fun b : Bool => if b then (1 : K) else 0) := fun c => by
      by_cases hc : c = 0
      · exact ⟨false, by simp [hc]⟩
      · exact ⟨true, by simp [hcon' c hc]⟩
    have := Nat.card_le_card_of_surjective _ hsurj
    rw [show Nat.card Bool = 2 by simp] at this
    omega
  have hrR : ∀ s : K, d.emb ⟨pinnedX .G2 K g2v s, pinnedX_mem_adjointGroup g2v s⟩ ∈
      d.rootGroup g2v := fun s =>
    d.emb_mem_image (g := ⟨_, pinnedX_mem_adjointGroup g2v s⟩) (mem_rootSubgroup.2 ⟨s, rfl⟩)
  have hrinj : ∀ s₁ s₂ : K, d.emb ⟨pinnedX .G2 K g2v s₁, pinnedX_mem_adjointGroup g2v s₁⟩ =
      d.emb ⟨pinnedX .G2 K g2v s₂, pinnedX_mem_adjointGroup g2v s₂⟩ → s₁ = s₂ := by
    intro s₁ s₂ e
    have e' : pinnedX .G2 K g2v s₁ = pinnedX .G2 K g2v s₂ :=
      congrArg Subtype.val (d.emb_injective e)
    rw [pinnedX_v_eq_g2N, pinnedX_v_eq_g2N] at e'
    exact (g2N_injective e').2.2.2.1
  have hr1 : ∀ s : K, s ≠ 0 →
      d.emb ⟨pinnedX .G2 K g2v s, pinnedX_mem_adjointGroup g2v s⟩ ≠ 1 := by
    intro s hs e
    have e' : pinnedX .G2 K g2v s = 1 :=
      congrArg Subtype.val (d.emb_injective (e.trans (map_one d.emb).symm))
    rw [pinnedX_v_eq_g2N, ← g2N_zero] at e'
    exact hs (g2N_injective e').2.2.2.1
  rw [← (d.yamada_defs).2.2.1] at hw
  obtain ⟨r₀, hr₀, y, hy, rfl⟩ := Common.exists_mul_of_le_normalizer
    (fun y hy => mem_normalizer_of_conj_mem fun u hu => by
      rw [W_mul_comm d (hYW hy) (hRW hu), mul_inv_cancel_right]
      exact hu) w hw
  have key : ∃ p ∈ translationsW₂ d t, ∃ y' ∈ d.Y, t * p * t * p⁻¹ = r₀ * y' := by
    by_cases hra : r₀ = d.emb ⟨pinnedX .G2 K g2v 1, pinnedX_mem_adjointGroup g2v 1⟩
    · refine hA _ (hrR c) (hr1 c hc0) r₀ hr₀ fun e => hc1 ?_
      exact hrinj c 1 (e.symm.trans hra)
    · exact hA _ (hrR 1) (hr1 1 one_ne_zero) r₀ hr₀ hra
  obtain ⟨p, hp, y', hy', e⟩ := key
  refine ⟨p, hp, y⁻¹ * y', mul_mem (inv_mem hy) hy', ?_⟩
  rw [e]
  group

theorem yamadaL₃_eq_translationsW₂ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaL₃ d t = translationsW₂ d t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPV : translationsW₂ d t ≤ normalizer (yamadaV₂ d t : Set G) := fun x hx =>
    centralizerW₂Y₂_le d t ((h.mem_translationsW₂_iff hW d hK hD).1 hx).1
  have hPL₃ : translationsW₂ d t ≤ yamadaL₃ d t :=
    LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hPV
      (h.normalizer_le_normalizer_translationsW₂ hW d hK hD) (h.isPGroup_translationsW₂ hW d hK hD)
  refine le_antisymm (fun z hz => ?_) hPL₃
  have hzV : z ∈ normalizer (yamadaV₂ d t : Set G) := LieType.BorelTits.pCoreOf_le 2 _ hz
  obtain ⟨p, hp, y, hy, e⟩ :=
    h.exists_mem_translationsW₂_crossed hW d hK hD (h.crossed_mem_W hW d hK hD hzV)
  have hcN := h.inv_mul_mem_normalizer_tY hW d hK hD (hPV hp) hzV hy e
  have hcL₃ : p⁻¹ * z ∈ yamadaL₃ d t := mul_mem (inv_mem (hPL₃ hp)) hz
  have := mul_mem hp (h.yamadaL₂_le_translationsW₂ hW d hK hD
    (h.yamadaL₃_inf_le d hK hD (Subgroup.mem_inf.2 ⟨hcL₃, hcN⟩)))
  rwa [mul_inv_cancel_left] at this

end Local

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
