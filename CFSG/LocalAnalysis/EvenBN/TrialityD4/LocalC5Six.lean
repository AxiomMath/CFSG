module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalC5Five

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup CFSG.Open
open scoped commutatorElement Pointwise

section Defs

variable {G : Type} [Group G] {L : Subgroup G} {q : ℕ}

@[expose] noncomputable def centralizerW₂Y₂ (d : TrialityD4Data L q) (t : G) : Subgroup G :=
  Common.centralizerMod (normalizer ((yamadaW₂ d t ⊔ zpowers t : Subgroup G) : Set G) ⊓
      normalizer (yamadaW₂ d t : Set G) ⊓ normalizer (yamadaY₂ d t : Set G))
    (yamadaW₂ d t) (yamadaY₂ d t)
    (fun _ hg y hy => (mem_normalizer_iff.1 (mem_inf.1 (mem_inf.1 hg).1).2 y).1 hy)
    (fun _ hg y hy => (mem_normalizer_iff.1 (mem_inf.1 hg).2 y).1 hy)

@[expose] noncomputable def kernelTW₂ (d : TrialityD4Data L q) (t : G) : Subgroup G :=
  centralizerW₂Y₂ d t ⊓ normalizer ((d.Y.map L.subtype ⊔ zpowers t : Subgroup G) : Set G)

@[expose] noncomputable def translationsW₂ (d : TrialityD4Data L q) (t : G) : Subgroup G :=
  Common.centralizerMod (centralizerW₂Y₂ d t ⊓ normalizer (kernelTW₂ d t : Set G) ⊓
      normalizer (yamadaL₂ d t : Set G)) (kernelTW₂ d t) (yamadaL₂ d t)
    (fun _ hg y hy => (mem_normalizer_iff.1 (mem_inf.1 (mem_inf.1 hg).1).2 y).1 hy)
    (fun _ hg y hy => (mem_normalizer_iff.1 (mem_inf.1 hg).2 y).1 hy)

theorem centralizerW₂Y₂_le (d : TrialityD4Data L q) (t : G) :
    centralizerW₂Y₂ d t ≤ normalizer ((yamadaW₂ d t ⊔ zpowers t : Subgroup G) : Set G) :=
  fun _ hg => (mem_inf.1 (mem_inf.1 (Common.mem_centralizerMod.1 hg).1).1).1

theorem yamadaL₃_inf_le [Finite G] (d : TrialityD4Data L q) (t : G) :
    yamadaL₃ d t ⊓ normalizer ((d.Y.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) ≤
      yamadaL₂ d t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right
    (fun g hg => Common.mem_normalizer_inf (LieType.BorelTits.le_normalizer_pCoreOf 2 _
      (le_normalizer_yamadaL₂ d t hg)) (le_normalizer hg))
    ((LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_left)

end Defs

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Main

variable (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hNH : NormalizerHyp d t)
  (h561 : yamadaC₁ d t = yamadaD₁ d t ⊔ zpowers t ∧ t ∉ yamadaD₁ d t ∧
    (normalizer (d.V : Set L)).map L.subtype ≤ normalizer (yamadaD₁ d t : Set G))
  (h562 : IsElemAbelian 2 (yamadaV₁ d t) ∧ Nat.card (yamadaV₁ d t) = (2 ^ f) ^ 2 ∧
    yamadaV₁ d t ⊓ centralizer ({t} : Set G) = d.V.map L.subtype ∧ yamadaV₁ d t ≤ yamadaF₁ d t)
  (h591 : yamadaL₂ d t = yamadaM₂ d t ⊔ zpowers t ∧ t ∉ yamadaM₂ d t ∧
    yamadaR₂ d t = yamadaS₂ d t ⊔ zpowers t ∧ t ∉ yamadaS₂ d t)
  (h592 : yamadaV₁ d t ⊓ (yamadaV₁ d t).map (MulAut.conj ((d.v : L) : G)).toMonoidHom = ⊥ ∧
    Nat.card (yamadaY₂ d t) = (2 ^ f) ^ 4 ∧ IsMulCommutative (yamadaY₂ d t) ∧
    yamadaM₂ d t ⊓ centralizer (yamadaM₂ d t : Set G) = yamadaY₂ d t ∧
    yamadaY₂ d t ⊓ centralizer ({t} : Set G) = d.Y.map L.subtype)
  (h593 : (Subgroup.upperCentralSeries (yamadaS₂ d t) 1).map (yamadaS₂ d t).subtype =
      yamadaV₁ d t ∧
    (Subgroup.upperCentralSeries (yamadaS₂ d t) 2).map (yamadaS₂ d t).subtype = yamadaY₂ d t)
  (h5101 : (Subgroup.upperCentralSeries (yamadaR₂ d t) 1).map (yamadaR₂ d t).subtype =
      d.V.map L.subtype ∧
    (Subgroup.upperCentralSeries (yamadaR₂ d t) 2).map (yamadaR₂ d t).subtype = yamadaY₁ d t ∧
    (Subgroup.upperCentralSeries (yamadaR₂ d t) 3).map (yamadaR₂ d t).subtype =
      yamadaW₂ d t ⊔ zpowers t ∧
    (Subgroup.upperCentralSeries (yamadaR₂ d t) 4).map (yamadaR₂ d t).subtype =
      yamadaF₂ d t ⊔ zpowers t)
  (h5102 : CFSG.Open.thompsonSubgroup (yamadaF₂ d t ⊔ zpowers t) = yamadaF₂ d t)

include h hNH h561 h562 h591 h592 h593 h5101 h5102 in
theorem mem_centralizerW₂Y₂_iff {g : G} :
    g ∈ centralizerW₂Y₂ d t ↔ g ∈ normalizer ((yamadaW₂ d t ⊔ zpowers t : Subgroup G) : Set G) ∧
      ∀ w ∈ yamadaW₂ d t, g * w * g⁻¹ * w⁻¹ ∈ yamadaY₂ d t := by
  rw [centralizerW₂Y₂, Common.mem_centralizerMod]
  refine ⟨fun ⟨hg, h2⟩ => ⟨(mem_inf.1 (mem_inf.1 hg).1).1, h2⟩, fun ⟨hg, h2⟩ => ⟨?_, h2⟩⟩
  exact mem_inf.2 ⟨mem_inf.2 ⟨hg, (h.normalizer_yamadaV₂_le d h562 h592).1 hg⟩,
    h.normalizer_yamadaV₂_le_normalizer_yamadaY₂ d hNH h561 h562 h591 h592 h593 h5101 h5102 hg⟩

include h hNH h561 h562 h591 h592 h593 h5101 h5102 in
theorem normalizer_le_normalizer_centralizerW₂Y₂ :
    normalizer ((yamadaW₂ d t ⊔ zpowers t : Subgroup G) : Set G) ≤
      normalizer (centralizerW₂Y₂ d t : Set G) := fun _ hg =>
  mem_normalizer_fintype fun _ hx => Common.conj_mem_centralizerMod
    (mem_inf.2 ⟨mem_inf.2 ⟨hg, (h.normalizer_yamadaV₂_le d h562 h592).1 hg⟩,
      h.normalizer_yamadaV₂_le_normalizer_yamadaY₂ d hNH h561 h562 h591 h592 h593 h5101 h5102
        hg⟩) hx

include h hNH h561 h562 h591 h592 h593 h5101 h5102 in
theorem mem_centralizerW₂Y₂_of {g : G}
    (hg : g ∈ normalizer ((yamadaW₂ d t ⊔ zpowers t : Subgroup G) : Set G))
    (hgW : ∀ a ∈ d.W.map L.subtype, g * a * g⁻¹ * a⁻¹ ∈ yamadaY₂ d t) :
    g ∈ centralizerW₂Y₂ d t := by
  refine (h.mem_centralizerW₂Y₂_iff d hNH h561 h562 h591 h592 h593 h5101 h5102).2
    ⟨hg, fun w hw => ?_⟩
  have hgY₂ := h.normalizer_yamadaV₂_le_normalizer_yamadaY₂ d hNH h561 h562 h591 h592 h593
    h5101 h5102 hg
  rw [show yamadaW₂ d t = d.W.map L.subtype ⊔ yamadaY₂ d t from rfl, ← SetLike.mem_coe,
    coe_mul_of_right_le_normalizer_left _ _ (yamadaY₂_le_normalizer_W d h592),
    Set.mem_mul] at hw
  obtain ⟨a, ha, y, hy, rfl⟩ := hw
  have h1 : g * y * g⁻¹ * y⁻¹ ∈ yamadaY₂ d t :=
    mul_mem ((mem_normalizer_iff.1 hgY₂ y).1 hy) (inv_mem hy)
  have h2 : a * (g * y * g⁻¹ * y⁻¹) * a⁻¹ ∈ yamadaY₂ d t := by
    rw [commute_of_mem_M_of_mem_yamadaY₂ d h592 (map_mono (d.W_le_F.trans d.F_le_M) ha) h1,
      mul_inv_cancel_right]
    exact h1
  rw [show g * (a * y) * g⁻¹ * (a * y)⁻¹ =
    (g * a * g⁻¹ * a⁻¹) * (a * (g * y * g⁻¹ * y⁻¹) * a⁻¹) by group]
  exact mul_mem (hgW a ha) h2

include h hNH h561 h562 h591 h592 h593 h5101 h5102 in
theorem crossed_mul_mem_Y {x g : G} (hx : x ∈ centralizerW₂Y₂ d t)
    (hg : g ∈ normalizer ((yamadaW₂ d t ⊔ zpowers t : Subgroup G) : Set G)) :
    ∃ y ∈ d.Y.map L.subtype, t * (x * g) * t * (x * g)⁻¹ =
      (t * x * t * x⁻¹) * (t * g * t * g⁻¹) * y := by
  obtain ⟨hxV, hxW₂⟩ := (h.mem_centralizerW₂Y₂_iff d hNH h561 h562 h591 h592 h593 h5101 h5102).1 hx
  have hxW := (h.normalizer_yamadaV₂_le d h562 h592).2.2 hxV
  have hκ := h.crossed_mem_W d h562 h592 hg
  rw [crossed_mul_D4 h.t_mul_t x g]
  generalize t * g * t * g⁻¹ = a at hκ ⊢
  generalize t * x * t * x⁻¹ = b
  have hz : x * a * x⁻¹ * a⁻¹ ∈ d.Y.map L.subtype := by
    rw [← h.W_inf_yamadaY₂ d h592]
    exact mem_inf.2 ⟨mul_mem ((mem_normalizer_iff.1 hxW a).1 hκ) (inv_mem hκ),
      hxW₂ a ((le_sup_left : d.W.map L.subtype ≤ yamadaW₂ d t) hκ)⟩
  refine ⟨x * a * x⁻¹ * a⁻¹, hz, ?_⟩
  have hcomm : a * (x * a * x⁻¹ * a⁻¹) = (x * a * x⁻¹ * a⁻¹) * a := by
    obtain ⟨a', ha', rfl⟩ := hκ
    obtain ⟨z', hz', hz'e⟩ := hz
    rw [← hz'e]
    exact congrArg Subtype.val (d.mul_comm_of_mem_W ha' (d.Y_le_W hz'))
  calc b * (x * a * x⁻¹) = b * ((x * a * x⁻¹ * a⁻¹) * a) := by group
    _ = b * (a * (x * a * x⁻¹ * a⁻¹)) := by rw [hcomm]
    _ = b * a * (x * a * x⁻¹ * a⁻¹) := by group

include h hNH h561 h562 h591 h592 h593 h5101 h5102 in
theorem yamadaL₂_le_centralizerW₂Y₂ : yamadaL₂ d t ≤ centralizerW₂Y₂ d t := fun l hl => by
  refine h.mem_centralizerW₂Y₂_of d hNH h561 h562 h591 h592 h593 h5101 h5102
    (h.normalizer_tY_le_normalizer_yamadaV₂ d h591 h592 (yamadaL₂_le d t hl)) fun a ha => ?_
  have h1 := h.commutatorElement_mem_Y_of_mem_yamadaV₂ d h591 h592
    (mem_sup_left (mem_sup_left ha)) hl
  have := inv_mem h1
  rw [show (a * l * a⁻¹ * l⁻¹)⁻¹ = l * a * l⁻¹ * a⁻¹ by group] at this
  exact Y_le_yamadaY₂ d h592 this

include h hNH h561 h562 h591 h592 h593 h5101 h5102 in
theorem yamadaR₃_le_centralizerW₂Y₂ : yamadaR₃ d t ≤ centralizerW₂Y₂ d t := fun g hg => by
  refine h.mem_centralizerW₂Y₂_of d hNH h561 h562 h591 h592 h593 h5101 h5102
    (mem_inf.1 (h.yamadaR₃_le_normalizer d hNH h561 h562 h591 h592 h593 h5101 h5102 hg)).1
    fun a ha => ?_
  have h1 := h.commutatorElement_mem_yamadaY₁ d hNH h561 h562 h591 h592 h593
    (mem_sup_left ha : a ∈ yamadaW₁ d t) (mem_inf.1 hg).1
  have := inv_mem h1
  rw [show (a * g * a⁻¹ * g⁻¹)⁻¹ = g * a * g⁻¹ * a⁻¹ by group] at this
  exact sup_le (Y_le_yamadaY₂ d h592) le_sup_left this

include h hNH h561 h562 h591 h592 h593 h5101 h5102 in
theorem exists_mem_centralizerW₂Y₂_crossed_eq {w : G} (hw : w ∈ d.W.map L.subtype) :
    ∃ x ∈ centralizerW₂Y₂ d t, t * x * t * x⁻¹ = w := by
  obtain ⟨g, hg, l, hl, e⟩ :=
    h.exists_conj_t_eq_mul_of_mem_W d hNH h561 h562 h591 h592 h593 h5101 h5102 hw
  refine ⟨g * l, mul_mem (h.yamadaR₃_le_centralizerW₂Y₂ d hNH h561 h562 h591 h592 h593 h5101 h5102
    hg) (h.yamadaL₂_le_centralizerW₂Y₂ d hNH h561 h562 h591 h592 h593 h5101 h5102 hl), ?_⟩
  rw [show t * (g * l) * t * (g * l)⁻¹ = t * (g * l * t * (g * l)⁻¹) by group, e, ← mul_assoc,
    h.t_mul_t, one_mul]

include h hNH h561 h562 h591 h592 h593 h5101 h5102 in
theorem normalizer_le_normalizer_kernelTW₂ :
    normalizer ((yamadaW₂ d t ⊔ zpowers t : Subgroup G) : Set G) ≤
      normalizer (kernelTW₂ d t : Set G) := fun g hg => by
  have hgX := h.normalizer_le_normalizer_centralizerW₂Y₂ d hNH h561 h562 h591 h592 h593 h5101 h5102
    hg
  have hgY := h.normalizer_yamadaV₂_le_normalizer_Y d hNH h561 h562 h591 h592 h593 h5101 h5102 hg
  refine mem_normalizer_fintype fun k hk => ?_
  obtain ⟨hkX, hkN⟩ := mem_inf.1 hk
  have hkV := centralizerW₂Y₂_le d t hkX
  have hx : g * k * g⁻¹ ∈ centralizerW₂Y₂ d t := (mem_normalizer_iff.1 hgX k).1 hkX
  refine mem_inf.2 ⟨hx, (h.crossed_mem_Y_iff d hNH h561 h562 h591 h592 h593 h5101 h5102
    (centralizerW₂Y₂_le d t hx)).1 ?_⟩
  obtain ⟨y₁, hy₁, e₁⟩ := h.crossed_mul_mem_Y d hNH h561 h562 h591 h592 h593 h5101 h5102 hx hg
  have hκk := (h.crossed_mem_Y_iff d hNH h561 h562 h591 h592 h593 h5101 h5102 hkV).2 hkN
  have hy₂ : g * (t * k * t * k⁻¹) * g⁻¹ ∈ d.Y.map L.subtype := (mem_normalizer_iff.1 hgY _).1 hκk
  have hκg := h.crossed_mem_W d h562 h592 hg
  rw [show g * k * g⁻¹ * g = g * k by group, crossed_mul_D4 h.t_mul_t g k] at e₁
  generalize t * (g * k * g⁻¹) * t * (g * k * g⁻¹)⁻¹ = b at e₁ ⊢
  generalize t * g * t * g⁻¹ = c at e₁ hκg
  generalize g * (t * k * t * k⁻¹) * g⁻¹ = y₂ at e₁ hy₂
  have hyy : y₂ * y₁⁻¹ ∈ d.Y.map L.subtype := mul_mem hy₂ (inv_mem hy₁)
  have hc : c * (y₂ * y₁⁻¹) = (y₂ * y₁⁻¹) * c := by
    obtain ⟨c', hc', rfl⟩ := hκg
    obtain ⟨z', hz', hz'e⟩ := hyy
    rw [← hz'e]
    exact congrArg Subtype.val (d.mul_comm_of_mem_W hc' (d.Y_le_W hz'))
  have hb : b = y₂ * y₁⁻¹ := by
    calc b = b * c * y₁ * y₁⁻¹ * c⁻¹ := by group
      _ = c * y₂ * y₁⁻¹ * c⁻¹ := by rw [← e₁]
      _ = c * (y₂ * y₁⁻¹) * c⁻¹ := by group
      _ = (y₂ * y₁⁻¹) * c * c⁻¹ := by rw [hc]
      _ = y₂ * y₁⁻¹ := by group
  rw [hb]
  exact hyy

include h hNH h561 h562 h591 h592 h593 h5101 h5102 in
theorem yamadaL₂_le_kernelTW₂ : yamadaL₂ d t ≤ kernelTW₂ d t :=
  le_inf (h.yamadaL₂_le_centralizerW₂Y₂ d hNH h561 h562 h591 h592 h593 h5101 h5102)
    (yamadaL₂_le d t)

include h hNH h561 h562 h591 h592 h593 h5101 h5102 in
theorem normalizer_yamadaV₂_le_normalizer_yamadaL₂ :
    normalizer ((yamadaW₂ d t ⊔ zpowers t : Subgroup G) : Set G) ≤
      normalizer (yamadaL₂ d t : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : kernelTW₂ d t ≤ normalizer ((d.Y.map L.subtype ⊔ zpowers t : Subgroup G) :
      Set G) := inf_le_right
  have hHV := h.normalizer_tY_le_normalizer_yamadaV₂ d h591 h592
  have hNK := h.normalizer_le_normalizer_kernelTW₂ d hNH h561 h562 h591 h592 h593 h5101 h5102
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
    · exact LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        (h.yamadaL₂_le_kernelTW₂ d hNH h561 h562 h591 h592 h593 h5101 h5102)
        (hKH.trans (le_normalizer_yamadaL₂ d t)) (LieType.BorelTits.pCoreOf_isPGroup 2 _)
  rw [← heq]
  exact hNK.trans hNP

include h hNH h561 h562 h591 h592 h593 h5101 h5102 in
theorem normalizer_yamadaL₂_eq :
    normalizer (yamadaL₂ d t : Set G) =
      normalizer ((yamadaW₂ d t ⊔ zpowers t : Subgroup G) : Set G) :=
  le_antisymm (h.normalizer_yamadaL₂_le d h591 h592)
    (h.normalizer_yamadaV₂_le_normalizer_yamadaL₂ d hNH h561 h562 h591 h592 h593 h5101 h5102)

include h hNH h561 h562 h591 h592 h593 h5101 h5102 in
theorem leviLong_le_kernelTW₂ : d.leviLong.map L.subtype ≤ kernelTW₂ d t := fun s hs => by
  have hsN : s ∈ normalizer ((d.Y.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) :=
    h.centralizer_inf_normalizer_Y_le d ⟨h.L_le_centralizer (map_subtype_le _ hs),
      map_le_normalizer_map d.leviLong_le_normalizer_Y hs⟩
  refine mem_inf.2 ⟨h.mem_centralizerW₂Y₂_of d hNH h561 h562 h591 h592 h593 h5101 h5102
    (h.normalizer_tY_le_normalizer_yamadaV₂ d h591 h592 hsN) fun a ha => ?_, hsN⟩
  obtain ⟨s', hs', rfl⟩ := hs
  obtain ⟨a', ha', rfl⟩ := ha
  exact Y_le_yamadaY₂ d h592
    (mem_map_of_mem L.subtype (d.commutatorElement_mem_Y_of_mem_leviLong hs' ha'))

include h hNH h561 h562 h591 h592 h593 h5101 h5102 in
theorem kernelTW₂_le : kernelTW₂ d t ≤ yamadaL₂ d t ⊔ d.leviLong.map L.subtype := by
  intro k hk
  obtain ⟨hkX, hkN⟩ := mem_inf.1 hk
  have hk' : k ∈ ((normalizer ((d.Y.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) :
      Subgroup G) : Set G) := hkN
  rw [(h.yamada_5_3_2 d).2.2.1] at hk'
  obtain ⟨l, hl, c, hc, rfl⟩ := Set.mem_mul.1 hk'
  obtain ⟨hcC, hcY⟩ := mem_inf.1 hc
  have hcX : c ∈ centralizerW₂Y₂ d t := by
    have := mul_mem (inv_mem (h.yamadaL₂_le_centralizerW₂Y₂ d hNH h561 h562 h591 h592 h593 h5101
      h5102 hl)) hkX
    rwa [inv_mul_cancel_left] at this
  have hcW : c ∈ normalizer ((d.W.map L.subtype : Subgroup G) : Set G) := by
    have : c ∈ centralizer ({t} : Set G) ⊓ normalizer ((d.W.map L.subtype : Subgroup G) :
        Set G) := by
      rw [← h.centralizer_inf_normalizer_Y_eq_W d]
      exact hc
    exact (mem_inf.1 this).2
  have hW : ∀ w ∈ d.W, h.act ⟨c, hcC⟩ w * w⁻¹ ∈ d.Y := by
    intro w hw
    rw [← coe_mem_map_subtype_iff_D4, Subgroup.coe_mul, h.coe_act_apply, Subgroup.coe_inv]
    have hwW : (w : G) ∈ d.W.map L.subtype := ⟨w, hw, rfl⟩
    rw [← h.W_inf_yamadaY₂ d h592]
    exact mem_inf.2 ⟨mul_mem ((mem_normalizer_iff.1 hcW _).1 hwW) (inv_mem hwW),
      ((h.mem_centralizerW₂Y₂_iff d hNH h561 h562 h591 h592 h593 h5101 h5102).1 hcX).2 _
        ((le_sup_left : d.W.map L.subtype ≤ yamadaW₂ d t) hwW)⟩
  obtain ⟨m, hm, s, hs, hα⟩ := d.eq_conj_of_trivial_W_mod_Y (h.act_mem_Y d hcC hcY) hW
  obtain ⟨τ, hτ, rfl⟩ := h.exists_mul_zpowers_of_act_eq_conj d hcC hα
  have hML₂ : d.M.map L.subtype ≤ yamadaL₂ d t := le_sup_left.trans (h.tM_le_yamadaL₂ d)
  have htL₂ : zpowers t ≤ yamadaL₂ d t :=
    (zpowers_le).2 (h.tM_le_yamadaL₂ d (mem_sup_right (mem_zpowers t)))
  have hsτ : (s : G) * τ = τ * s := h.commute_zpowers_of_mem_L s.2 hτ
  rw [show l * (((m * s : L) : G) * τ) = l * m * τ * s by
    rw [Subgroup.coe_mul, mul_assoc (m : G), hsτ]; group]
  exact mul_mem (mem_sup_left (mul_mem (mul_mem hl (hML₂ ⟨m, hm, rfl⟩)) (htL₂ hτ)))
    (mem_sup_right ⟨s, hs, rfl⟩)

include h in
theorem J₂_le_normalizer_tY :
    d.J₂.map L.subtype ≤ normalizer ((d.Y.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) :=
  fun _ hj => h.centralizer_inf_normalizer_Y_le d ⟨h.L_le_centralizer (map_subtype_le _ hj),
    map_le_normalizer_map (inf_le_left.trans d.J_le_normalizer_Y) hj⟩

include h hNH h561 h562 h591 h592 h593 h5101 h5102 in
theorem J₂_commutator_mem_yamadaL₂ {j k : G} (hj : j ∈ d.J₂.map L.subtype)
    (hk : k ∈ kernelTW₂ d t) : j * k * j⁻¹ * k⁻¹ ∈ yamadaL₂ d t := by
  have hjL₂ : j ∈ normalizer (yamadaL₂ d t : Set G) :=
    le_normalizer_yamadaL₂ d t (h.J₂_le_normalizer_tY d hj)
  have hBL₂ : d.leviLong.map L.subtype ≤ normalizer (yamadaL₂ d t : Set G) := fun b hb =>
    le_normalizer_yamadaL₂ d t (mem_inf.1 (h.leviLong_le_kernelTW₂ d hNH h561 h562 h591 h592 h593
      h5101 h5102 hb)).2
  have hk' := h.kernelTW₂_le d hNH h561 h562 h591 h592 h593 h5101 h5102 hk
  rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left _ _ hBL₂, Set.mem_mul] at hk'
  obtain ⟨l, hl, b, hb, rfl⟩ := hk'
  have hjb : b * j = j * b := by
    obtain ⟨j', hj', rfl⟩ := hj
    obtain ⟨b', hb', rfl⟩ := hb
    exact (congrArg Subtype.val
      (mem_centralizer_iff.1 (d.leviLong_le_centralizer_J₂ hb') j' hj')).symm
  have hjb' : b * j⁻¹ = j⁻¹ * b := by
    calc b * j⁻¹ = j⁻¹ * (j * b) * j⁻¹ := by group
      _ = j⁻¹ * (b * j) * j⁻¹ := by rw [hjb]
      _ = j⁻¹ * b := by group
  have := mul_mem ((mem_normalizer_iff.1 hjL₂ l).1 hl) (inv_mem hl)
  rw [show j * (l * b) * j⁻¹ * (l * b)⁻¹ = j * l * (b * j⁻¹) * b⁻¹ * l⁻¹ by group, hjb',
    show j * l * (j⁻¹ * b) * b⁻¹ * l⁻¹ = j * l * j⁻¹ * l⁻¹ by group]
  exact this

include h hNH h561 h562 h591 h592 h593 h5101 h5102 in
theorem mem_translationsW₂_iff {g : G} :
    g ∈ translationsW₂ d t ↔ g ∈ centralizerW₂Y₂ d t ∧
      ∀ k ∈ kernelTW₂ d t, g * k * g⁻¹ * k⁻¹ ∈ yamadaL₂ d t := by
  rw [translationsW₂, Common.mem_centralizerMod]
  refine ⟨fun ⟨hg, h2⟩ => ⟨(mem_inf.1 (mem_inf.1 hg).1).1, h2⟩, fun ⟨hg, h2⟩ => ⟨?_, h2⟩⟩
  have hgV := centralizerW₂Y₂_le d t hg
  exact mem_inf.2 ⟨mem_inf.2 ⟨hg,
    h.normalizer_le_normalizer_kernelTW₂ d hNH h561 h562 h591 h592 h593 h5101 h5102 hgV⟩,
    h.normalizer_yamadaV₂_le_normalizer_yamadaL₂ d hNH h561 h562 h591 h592 h593 h5101 h5102 hgV⟩

include h hNH h561 h562 h591 h592 h593 h5101 h5102 in
theorem normalizer_le_normalizer_translationsW₂ :
    normalizer ((yamadaW₂ d t ⊔ zpowers t : Subgroup G) : Set G) ≤
      normalizer (translationsW₂ d t : Set G) := fun g hg => by
  refine mem_normalizer_fintype fun x hx => ?_
  obtain ⟨hxX, hxK⟩ := (h.mem_translationsW₂_iff d hNH h561 h562 h591 h592 h593 h5101 h5102).1 hx
  have hgK := h.normalizer_le_normalizer_kernelTW₂ d hNH h561 h562 h591 h592 h593 h5101 h5102 hg
  have hgL₂ := h.normalizer_yamadaV₂_le_normalizer_yamadaL₂ d hNH h561 h562 h591 h592 h593 h5101
    h5102 hg
  refine (h.mem_translationsW₂_iff d hNH h561 h562 h591 h592 h593 h5101 h5102).2
    ⟨(mem_normalizer_iff.1 (h.normalizer_le_normalizer_centralizerW₂Y₂ d hNH h561 h562 h591 h592
      h593 h5101 h5102 hg) x).1 hxX, fun k hk => ?_⟩
  have hk' : g⁻¹ * k * g ∈ kernelTW₂ d t := by
    have := (mem_normalizer_iff.1 (inv_mem hgK) k).1 hk
    rwa [inv_inv] at this
  have := (mem_normalizer_iff.1 hgL₂ _).1 (hxK _ hk')
  rwa [show g * (x * (g⁻¹ * k * g) * x⁻¹ * (g⁻¹ * k * g)⁻¹) * g⁻¹ =
    g * x * g⁻¹ * k * (g * x * g⁻¹)⁻¹ * k⁻¹ by group] at this

include h hNH h561 h562 h591 h592 h593 h5101 h5102 in
theorem yamadaL₂_le_translationsW₂ : yamadaL₂ d t ≤ translationsW₂ d t := fun l hl => by
  refine (h.mem_translationsW₂_iff d hNH h561 h562 h591 h592 h593 h5101 h5102).2
    ⟨h.yamadaL₂_le_centralizerW₂Y₂ d hNH h561 h562 h591 h592 h593 h5101 h5102 hl, fun k hk => ?_⟩
  have hkL₂ : k ∈ normalizer (yamadaL₂ d t : Set G) :=
    le_normalizer_yamadaL₂ d t (mem_inf.1 hk).2
  have := (mem_normalizer_iff.1 hkL₂ l⁻¹).1 (inv_mem hl)
  rw [show l * k * l⁻¹ * k⁻¹ = l * (k * l⁻¹ * k⁻¹) by group]
  exact mul_mem hl this

include h in
theorem yamadaL₂_inf_leviLong : yamadaL₂ d t ⊓ d.leviLong.map L.subtype = ⊥ := by
  refine eq_bot_iff.2 fun x hx => ?_
  obtain ⟨hxL₂, hxB⟩ := mem_inf.1 hx
  obtain ⟨b, hb, rfl⟩ := hxB
  have hxMt : L.subtype b ∈ d.M.map L.subtype ⊔ zpowers t := by
    rw [← (h.yamada_5_3_2 d).2.2.2.2.1]
    exact mem_inf.2 ⟨hxL₂, h.L_le_centralizer b.2⟩
  rcases (h.mem_sup_zpowers_iff (map_subtype_le _)).1 hxMt with h1 | h1
  · obtain ⟨m, hm, hmb⟩ := h1
    have hmb' : m = b := L.subtype_injective hmb
    have hb' : b ∈ d.M ⊓ d.leviLong := mem_inf.2 ⟨hmb' ▸ hm, hb⟩
    rw [d.M_inf_leviLong, mem_bot] at hb'
    rw [mem_bot, hb', map_one]
  · exfalso
    have := mul_mem (map_subtype_le _ h1) (inv_mem b.2)
    rw [Subgroup.coe_subtype, mul_inv_cancel_right] at this
    exact h.t_not_mem_L this

include h hNH h561 h562 h591 h592 h593 h5101 h5102 in
theorem translationsW₂_inf_kernelTW₂_le :
    translationsW₂ d t ⊓ kernelTW₂ d t ≤ yamadaL₂ d t := by
  have hBK := h.leviLong_le_kernelTW₂ d hNH h561 h562 h591 h592 h593 h5101 h5102
  have hBL₂ : d.leviLong.map L.subtype ≤ normalizer (yamadaL₂ d t : Set G) := fun b hb =>
    le_normalizer_yamadaL₂ d t (mem_inf.1 (hBK hb)).2
  intro x hx
  obtain ⟨hxP, hxK⟩ := mem_inf.1 hx
  obtain ⟨-, hxc⟩ := (h.mem_translationsW₂_iff d hNH h561 h562 h591 h592 h593 h5101 h5102).1 hxP
  have hx' := h.kernelTW₂_le d hNH h561 h562 h591 h592 h593 h5101 h5102 hxK
  rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left _ _ hBL₂, Set.mem_mul] at hx'
  obtain ⟨l, hl, b, hb, rfl⟩ := hx'
  have key : ∀ b' ∈ d.leviLong.map L.subtype, b * b' = b' * b := by
    intro b' hb'
    have h1 := hxc b' (hBK hb')
    have hc : b * b' * b⁻¹ ∈ d.leviLong.map L.subtype := mul_mem (mul_mem hb hb') (inv_mem hb)
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
      rw [← h.yamadaL₂_inf_leviLong d]
      exact mem_inf.2 ⟨h3, mul_mem hc (inv_mem hb')⟩
    rw [mem_bot] at h5
    calc b * b' = b * b' * b⁻¹ * b'⁻¹ * (b' * b) := by group
      _ = b' * b := by rw [h5, one_mul]
  obtain ⟨b₀, hb₀, rfl⟩ := hb
  have hb1 : b₀ = 1 := d.eq_one_of_mem_leviLong_of_commute hb₀ fun b' hb' =>
    L.subtype_injective (by rw [map_mul, map_mul]; exact key _ ⟨b', hb', rfl⟩)
  rw [hb1, map_one, mul_one]
  exact hl

include h hNH h561 h562 h591 h592 h593 h5101 h5102 in
theorem isPGroup_translationsW₂ : IsPGroup 2 (translationsW₂ d t) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL₂p : IsPGroup 2 (yamadaL₂ d t) := LieType.BorelTits.pCoreOf_isPGroup 2 _
  intro p
  obtain ⟨hpX, -⟩ := (h.mem_translationsW₂_iff d hNH h561 h562 h591 h592 h593 h5101 h5102).1 p.2
  have hpV := centralizerW₂Y₂_le d t hpX
  obtain ⟨y, hy, e⟩ := h.crossed_mul_mem_Y d hNH h561 h562 h591 h592 h593 h5101 h5102 hpX hpV
  have hκ2 : t * ((p : G) * p) * t * ((p : G) * p)⁻¹ ∈ d.Y.map L.subtype := by
    rw [e, yamadaW₂_mul_self d h562 h592 ((le_sup_left : d.W.map L.subtype ≤ yamadaW₂ d t)
      (h.crossed_mem_W d h562 h592 hpV)), one_mul]
    exact hy
  have hp2K : (p : G) * p ∈ kernelTW₂ d t := mem_inf.2 ⟨mul_mem hpX hpX,
    (h.crossed_mem_Y_iff d hNH h561 h562 h591 h592 h593 h5101 h5102 (mul_mem hpV hpV)).1 hκ2⟩
  have hp2L₂ := h.translationsW₂_inf_kernelTW₂_le d hNH h561 h562 h591 h592 h593 h5101 h5102
    (mem_inf.2 ⟨mul_mem p.2 p.2, hp2K⟩)
  obtain ⟨n, hn⟩ := hL₂p ⟨_, hp2L₂⟩
  refine ⟨n + 1, Subtype.ext ?_⟩
  have hn' := congrArg Subtype.val hn
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at hn' ⊢
  rw [pow_succ', pow_mul, sq]
  exact hn'

include h hNH h561 h562 h591 h592 h593 h5101 h5102 in
theorem J₂_commutator_mem_translationsW₂ {j x : G} (hj : j ∈ d.J₂.map L.subtype)
    (hx : x ∈ centralizerW₂Y₂ d t) : j * x * j⁻¹ * x⁻¹ ∈ translationsW₂ d t := by
  have hjV := h.normalizer_tY_le_normalizer_yamadaV₂ d h591 h592 (h.J₂_le_normalizer_tY d hj)
  have hxV := centralizerW₂Y₂_le d t hx
  have hxK := h.normalizer_le_normalizer_kernelTW₂ d hNH h561 h562 h591 h592 h593 h5101 h5102 hxV
  have hxL₂ := h.normalizer_yamadaV₂_le_normalizer_yamadaL₂ d hNH h561 h562 h591 h592 h593 h5101
    h5102 hxV
  have hjL₂ := h.normalizer_yamadaV₂_le_normalizer_yamadaL₂ d hNH h561 h562 h591 h592 h593 h5101
    h5102 hjV
  have hjX : j * x * j⁻¹ ∈ centralizerW₂Y₂ d t :=
    (mem_normalizer_iff.1 (h.normalizer_le_normalizer_centralizerW₂Y₂ d hNH h561 h562 h591 h592
      h593 h5101 h5102 hjV) x).1 hx
  refine (h.mem_translationsW₂_iff d hNH h561 h562 h591 h592 h593 h5101 h5102).2
    ⟨mul_mem hjX (inv_mem hx), fun k hk => ?_⟩
  have hk₁ : x⁻¹ * k * x ∈ kernelTW₂ d t := by
    have := (mem_normalizer_iff.1 (inv_mem hxK) k).1 hk
    rwa [inv_inv] at this
  have hℓ₁ := h.J₂_commutator_mem_yamadaL₂ d hNH h561 h562 h591 h592 h593 h5101 h5102
    (inv_mem hj) hk₁
  have hℓ₂ := (mem_normalizer_iff.1 hxL₂ _).1 hℓ₁
  have hℓ₃ := (mem_normalizer_iff.1 hjL₂ _).1 hℓ₂
  have := mul_mem hℓ₃ (h.J₂_commutator_mem_yamadaL₂ d hNH h561 h562 h591 h592 h593 h5101 h5102
    hj hk)
  rwa [show j * (x * (j⁻¹ * (x⁻¹ * k * x) * j⁻¹⁻¹ * (x⁻¹ * k * x)⁻¹) * x⁻¹) * j⁻¹ *
    (j * k * j⁻¹ * k⁻¹) = j * x * j⁻¹ * x⁻¹ * k * (j * x * j⁻¹ * x⁻¹)⁻¹ * k⁻¹ by group] at this

include h hNH h561 h562 h591 h592 h593 h5101 h5102 in
theorem exists_mem_translationsW₂_crossed {w : G} (hw : w ∈ d.W.map L.subtype) :
    ∃ p ∈ translationsW₂ d t, ∃ y ∈ d.Y.map L.subtype, t * p * t * p⁻¹ = w * y := by
  have hA : ∀ a ∈ d.U₄, a ≠ 1 → ∀ r ∈ d.U₄, r ≠ a →
      ∃ p ∈ translationsW₂ d t, ∃ y ∈ d.Y.map L.subtype, t * p * t * p⁻¹ = (r : G) * y := by
    intro a ha ha1 r hr hra
    have hra1 : r * a ≠ 1 := fun e => hra (by
      calc r = r * a * a := by
            rw [mul_assoc, d.mul_self_eq_one_of_mem_W (d.U₄_le_W ha), mul_one]
        _ = a := by rw [e, one_mul])
    obtain ⟨j, ⟨hj, hja⟩, -⟩ := (d.yamada_three_five_five.2.2.1).2 a ha ha1 (r * a)
      (mul_mem hr ha) hra1
    have hjG : (j : G) ∈ d.J₂.map L.subtype := ⟨j, hj, rfl⟩
    have haW : (a : G) ∈ d.W.map L.subtype := ⟨a, d.U₄_le_W ha, rfl⟩
    obtain ⟨x, hx, hκx⟩ := h.exists_mem_centralizerW₂Y₂_crossed_eq d hNH h561 h562 h591 h592 h593
      h5101 h5102 haW
    have hxV := centralizerW₂Y₂_le d t hx
    have hjV := h.normalizer_tY_le_normalizer_yamadaV₂ d h591 h592 (h.J₂_le_normalizer_tY d hjG)
    have hjX : (j : G) * x * (j : G)⁻¹ ∈ centralizerW₂Y₂ d t :=
      (mem_normalizer_iff.1 (h.normalizer_le_normalizer_centralizerW₂Y₂ d hNH h561 h562 h591 h592
        h593 h5101 h5102 hjV) x).1 hx
    obtain ⟨y₁, hy₁, e₁⟩ := h.crossed_mul_mem_Y d hNH h561 h562 h591 h592 h593 h5101 h5102 hjX
      (inv_mem hxV)
    have hjt : (j : G) * t = t * j := mem_centralizer_singleton_iff.1 (h.L_le_centralizer j.2)
    have hjt' : (j : G)⁻¹ * t * j = t := by rw [mul_assoc, ← hjt, inv_mul_cancel_left]
    have e₂ : t * ((j : G) * x * (j : G)⁻¹) * t * ((j : G) * x * (j : G)⁻¹)⁻¹ =
        (r : G) * a := by
      calc t * ((j : G) * x * (j : G)⁻¹) * t * ((j : G) * x * (j : G)⁻¹)⁻¹ =
            t * j * x * ((j : G)⁻¹ * t * j) * x⁻¹ * (j : G)⁻¹ := by group
        _ = j * t * x * t * x⁻¹ * (j : G)⁻¹ := by rw [hjt', ← hjt]
        _ = j * (t * x * t * x⁻¹) * (j : G)⁻¹ := by group
        _ = (r : G) * a := by rw [hκx]; exact congrArg Subtype.val hja
    have hz : x⁻¹ * (a : G)⁻¹ * x * a ∈ d.Y.map L.subtype := by
      obtain ⟨hx'V, hx'W₂⟩ :=
        (h.mem_centralizerW₂Y₂_iff d hNH h561 h562 h591 h592 h593 h5101 h5102).1 (inv_mem hx)
      have hx'W := (h.normalizer_yamadaV₂_le d h562 h592).2.2 hx'V
      rw [← h.W_inf_yamadaY₂ d h592]
      refine mem_inf.2 ⟨mul_mem ?_ haW, ?_⟩
      · have := (mem_normalizer_iff.1 hx'W (a : G)⁻¹).1 (inv_mem haW)
        rwa [inv_inv] at this
      · have := hx'W₂ (a : G)⁻¹ ((le_sup_left : d.W.map L.subtype ≤ yamadaW₂ d t) (inv_mem haW))
        rwa [inv_inv, inv_inv] at this
    have hp := h.J₂_commutator_mem_translationsW₂ d hNH h561 h562 h591 h592 h593 h5101 h5102 hjG hx
    refine ⟨(j : G) * x * (j : G)⁻¹ * x⁻¹, hp, (x⁻¹ * (a : G)⁻¹ * x * a) * y₁, mul_mem hz hy₁, ?_⟩
    rw [e₁, e₂, crossed_inv_D4 h.t_mul_t x, hκx]
    have hc : (a : G) * (x⁻¹ * (a : G)⁻¹ * x * a) = (x⁻¹ * (a : G)⁻¹ * x * a) * a := by
      obtain ⟨z', hz', hz'e⟩ := hz
      rw [← hz'e]
      exact congrArg Subtype.val (d.mul_comm_of_mem_W (d.U₄_le_W ha) (d.Y_le_W hz'))
    calc (r : G) * a * (x⁻¹ * (a : G)⁻¹ * x) * y₁ =
          (r : G) * ((a : G) * (x⁻¹ * (a : G)⁻¹ * x * a)) * (a : G)⁻¹ * y₁ := by group
      _ = (r : G) * ((x⁻¹ * (a : G)⁻¹ * x * a) * a) * (a : G)⁻¹ * y₁ := by rw [hc]
      _ = (r : G) * (x⁻¹ * (a : G)⁻¹ * x * a * y₁) := by group
  have h2q : 2 < Nat.card d.Γ := by
    rw [d.card_Γ]
    exact lt_of_lt_of_le (by norm_num : 2 < 2 ^ 3) (Nat.pow_le_pow_left d.two_le_q 3)
  obtain ⟨c, hc0, hc1⟩ := Common.exists_ne_zero_ne_one h2q
  have hx₄1 : ∀ s : d.Γ, s ≠ 0 → d.x₄ s ≠ 1 := fun s hs e =>
    hs (d.x₄_injective (e.trans d.x₄_zero.symm))
  obtain ⟨w', hw', rfl⟩ := hw
  obtain ⟨a₀, n, hn, rfl⟩ := d.mem_W_iff.1 hw'
  have key : ∃ p ∈ translationsW₂ d t, ∃ y' ∈ d.Y.map L.subtype,
      t * p * t * p⁻¹ = (d.x₄ a₀ : G) * y' := by
    by_cases ha₀ : a₀ = 1
    · exact hA _ (d.x₄_mem_U₄ c) (hx₄1 c hc0) _ (d.x₄_mem_U₄ a₀) fun e =>
        hc1 ((d.x₄_injective e).symm.trans ha₀)
    · exact hA _ (d.x₄_mem_U₄ 1) (hx₄1 1 one_ne_zero) _ (d.x₄_mem_U₄ a₀) fun e =>
        ha₀ (d.x₄_injective e)
  obtain ⟨p, hp, y', hy', e⟩ := key
  refine ⟨p, hp, (n : G)⁻¹ * y', mul_mem (inv_mem ⟨n, hn, rfl⟩) hy', ?_⟩
  rw [e, Subgroup.coe_subtype, Subgroup.coe_mul]
  group

include h hNH h561 h562 h591 h592 h593 h5101 h5102 in
theorem yamadaL₃_eq_translationsW₂ : yamadaL₃ d t = translationsW₂ d t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNeq := h.normalizer_yamadaL₂_eq d hNH h561 h562 h591 h592 h593 h5101 h5102
  have hPV : translationsW₂ d t ≤
      normalizer ((yamadaW₂ d t ⊔ zpowers t : Subgroup G) : Set G) := fun x hx =>
    centralizerW₂Y₂_le d t
      ((h.mem_translationsW₂_iff d hNH h561 h562 h591 h592 h593 h5101 h5102).1 hx).1
  have hPL₃ : translationsW₂ d t ≤ yamadaL₃ d t :=
    LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hPV.trans hNeq.ge)
      (hNeq.le.trans (h.normalizer_le_normalizer_translationsW₂ d hNH h561 h562 h591 h592 h593
        h5101 h5102))
      (h.isPGroup_translationsW₂ d hNH h561 h562 h591 h592 h593 h5101 h5102)
  refine le_antisymm (fun z hz => ?_) hPL₃
  have hzV : z ∈ normalizer ((yamadaW₂ d t ⊔ zpowers t : Subgroup G) : Set G) :=
    hNeq.le (LieType.BorelTits.pCoreOf_le 2 _ hz)
  obtain ⟨p, hp, y, hy, e⟩ := h.exists_mem_translationsW₂_crossed d hNH h561 h562 h591 h592 h593
    h5101 h5102 (h.crossed_mem_W d h562 h592 hzV)
  have hcN := h.inv_mul_mem_normalizer_tY d hNH h561 h562 h591 h592 h593 h5101 h5102 (hPV hp)
    hzV hy e
  have hcL₃ : p⁻¹ * z ∈ yamadaL₃ d t := mul_mem (inv_mem (hPL₃ hp)) hz
  have := mul_mem hp (h.yamadaL₂_le_translationsW₂ d hNH h561 h562 h591 h592 h593 h5101 h5102
    (yamadaL₃_inf_le d t (mem_inf.2 ⟨hcL₃, hcN⟩)))
  rwa [mul_inv_cancel_left] at this

end Main

end Setup

end CFSG.LocalAnalysis.EvenBN.TrialityD4
