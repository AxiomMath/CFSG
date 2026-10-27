module

public import CFSG.LocalAnalysis.EvenBN.G2.LocalQFourUniform
public import CFSG.LocalAnalysis.EvenBN.G2.QFacts

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.LocalAnalysis.EvenBN.Common (CosetData)
open scoped commutatorElement Pointwise

section Generic

variable {G : Type*} [Group G]

private theorem mul_comm_of_mul_self_eq_one_aux {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    (hxy : x * y * (x * y) = 1) : x * y = y * x := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have h1 : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right hxy
  rw [mul_inv_rev, hxi, hyi] at h1
  exact h1.symm

private theorem twoElementaryProduct_sup_central {S A B Z : Subgroup G}
    (h : Common.TwoElementaryProduct S A B) (hZS : S ≤ centralizer (Z : Set G))
    (hZ : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x) (hA : CFSG.IsElementaryAbelian 2 ↥(A ⊔ Z))
    (hB : CFSG.IsElementaryAbelian 2 ↥(B ⊔ Z)) :
    Common.TwoElementaryProduct (S ⊔ Z) (A ⊔ Z) (B ⊔ Z) where
  le_left := sup_le_sup_right h.le_left Z
  le_right := sup_le_sup_right h.le_right Z
  exists_mul := by
    intro s hs
    have hSN : S ≤ normalizer (Z : Set G) := hZS.trans (Subgroup.centralizer_le_normalizer _)
    obtain ⟨s₀, hs₀, z, hz, rfl⟩ := Common.exists_mul_of_le_normalizer' hSN s hs
    obtain ⟨a, ha, b, hb, rfl⟩ := h.exists_mul s₀ hs₀
    exact ⟨a, mem_sup_left ha, b * z, mul_mem (mem_sup_left hb) (mem_sup_right hz), by group⟩
  isElementaryAbelian_left := hA
  isElementaryAbelian_right := hB
  exists_mul_ne := by
    obtain ⟨x, hx, y, hy, hxy⟩ := h.exists_mul_ne
    exact ⟨x, mem_sup_left hx, y, mem_sup_left hy, hxy⟩
  inf_centralizer_left := by
    intro a ha haB
    have hSN : S ≤ normalizer (Z : Set G) := hZS.trans (Subgroup.centralizer_le_normalizer _)
    have hAN : A ≤ normalizer (Z : Set G) := h.le_left.trans hSN
    obtain ⟨a₀, ha₀, z₀, hz₀, rfl⟩ := Common.exists_mul_of_le_normalizer' hAN a ha
    have ha₀B : a₀ ∉ B := fun hb => haB (mul_mem (mem_sup_left hb) (mem_sup_right hz₀))
    have hcent := h.inf_centralizer_left a₀ ha₀ ha₀B
    refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
    · obtain ⟨hxS, hxc⟩ := Subgroup.mem_inf.1 hx
      obtain ⟨s, hs, z, hz, rfl⟩ := Common.exists_mul_of_le_normalizer' hSN x hxS
      have e : s * z * (a₀ * z₀) = a₀ * z₀ * (s * z) := mem_centralizer_singleton_iff.1 hxc
      have hza : z * a₀ = a₀ * z := mem_centralizer_iff.1 (hZS (h.le_left ha₀)) z hz
      have hsz₀ : z₀ * s = s * z₀ := mem_centralizer_iff.1 (hZS hs) z₀ hz₀
      have hzz₀ : z * z₀ = z₀ * z := hZ z hz z₀ hz₀
      have e2 : s * a₀ * (z * z₀) = a₀ * s * (z * z₀) := by
        calc s * a₀ * (z * z₀) = s * (a₀ * z) * z₀ := by group
          _ = s * (z * a₀) * z₀ := by rw [hza]
          _ = s * z * (a₀ * z₀) := by group
          _ = a₀ * z₀ * (s * z) := e
          _ = a₀ * (z₀ * s) * z := by group
          _ = a₀ * (s * z₀) * z := by rw [hsz₀]
          _ = a₀ * s * (z₀ * z) := by group
          _ = a₀ * s * (z * z₀) := by rw [hzz₀]
      have hsa : s * a₀ = a₀ * s := mul_right_cancel e2
      have hsA : s ∈ A := by
        rw [← hcent]
        exact Subgroup.mem_inf.2 ⟨hs, mem_centralizer_singleton_iff.2 hsa⟩
      exact mul_mem (mem_sup_left hsA) (mem_sup_right hz)
    · exact Subgroup.mem_inf.2 ⟨sup_le_sup_right h.le_left Z hx,
        mem_centralizer_singleton_iff.2
          (congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : ↥(A ⊔ Z)) ⟨a₀ * z₀, ha⟩))⟩

end Generic

namespace Model

variable
  {K : Type} [Field K] [CharP K 2]

theorem mem_F_of_forall_commutator_mem_X {x : ModGL .G2 K} (hx : x ∈ S K)
    (h : ∀ y ∈ S K, ⁅x, y⁆ ∈ X K) : x ∈ Model.F K := by
  obtain ⟨A, B, C, D, E, F, rfl⟩ := mem_S.1 hx
  have h1 := h (g2N 1 0 0 0 0 0) (mem_S.2 ⟨1, 0, 0, 0, 0, 0, rfl⟩)
  have h2 := h (g2N 0 1 0 0 0 0) (mem_S.2 ⟨0, 1, 0, 0, 0, 0, rfl⟩)
  rw [g2N_commutator_coords, g2N_mem_X_iff] at h1 h2
  have hB : B = 0 := by simpa using h1.2.2
  have hA : A = 0 := by simpa using h2.2.2
  rw [g2N_mem_F_iff]
  exact ⟨hA, hB⟩

end Model

namespace G2Data

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] (d : G2Data L K)

variable
  [Finite K] [CharP K 2]

theorem exists_mem_W_not_mem_Y [Finite G] (hK : 4 ≤ Nat.card K) : ∃ w ∈ d.W, w ∉ d.Y := by
  by_contra hcon
  have hle : d.W ≤ d.Y := fun w hw => by_contra fun hw' => hcon ⟨w, hw, hw'⟩
  have h3 := Subgroup.card_le_of_le hle
  rw [d.cards.2.2.2.1, d.cards.2.1] at h3
  have hq : 1 < Nat.card K := by omega
  exact absurd h3 (not_le.2 (Nat.pow_lt_pow_right hq (by norm_num)))

theorem twoElementaryProduct_F : Common.TwoElementaryProduct d.F d.W d.X where
  le_left := d.inclusions.2.2.2.2.1
  le_right := d.inclusions.2.2.2.1
  exists_mul := by
    intro s hs
    obtain ⟨g, hg, rfl⟩ := d.mem_image.1 hs
    obtain ⟨a, ha, b, hb, hab⟩ :=
      (Model.twoElementaryProduct_F (K := K)).exists_mul (g : ModGL .G2 K) hg
    refine ⟨d.emb ⟨a, Model.W_le_adjointGroup ha⟩, d.emb_mem_image ha,
      d.emb ⟨b, Model.X_le_adjointGroup hb⟩, d.emb_mem_image hb, ?_⟩
    rw [← map_mul]
    congr 1
    exact Subtype.ext hab
  isElementaryAbelian_left :=
    (d.isElementaryAbelian_image_iff Model.W_le_adjointGroup).2 Model.W_isElementaryAbelian
  isElementaryAbelian_right :=
    (d.isElementaryAbelian_image_iff Model.X_le_adjointGroup).2 Model.X_isElementaryAbelian
  exists_mul_ne := by
    obtain ⟨x, hx, y, hy, hxy⟩ := (Model.twoElementaryProduct_F (K := K)).exists_mul_ne
    refine ⟨d.emb ⟨x, Model.F_le_adjointGroup hx⟩, d.emb_mem_image hx,
      d.emb ⟨y, Model.F_le_adjointGroup hy⟩, d.emb_mem_image hy, fun h' => hxy ?_⟩
    rw [← map_mul, ← map_mul] at h'
    exact congrArg Subtype.val (d.emb_injective h')
  inf_centralizer_left := by
    intro a ha haX
    have hWabel : CFSG.IsElementaryAbelian 2 d.W :=
      (d.isElementaryAbelian_image_iff Model.W_le_adjointGroup).2 Model.W_isElementaryAbelian
    obtain ⟨g, hgW, rfl⟩ := d.mem_image.1 ha
    have hgX : (g : ModGL .G2 K) ∉ Model.X K := fun h' => haX (d.emb_mem_image h')
    refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
    · obtain ⟨hxF, hxc⟩ := Subgroup.mem_inf.1 hx
      obtain ⟨x', hx'F, rfl⟩ := d.mem_image.1 hxF
      have hc : x' * g = g * x' := d.emb_injective (by
        rw [map_mul, map_mul]
        exact mem_centralizer_singleton_iff.1 hxc)
      have hmem : (x' : ModGL .G2 K) ∈ Model.F K ⊓
          centralizer ({(g : ModGL .G2 K)} : Set (ModGL .G2 K)) :=
        Subgroup.mem_inf.2 ⟨hx'F, mem_centralizer_singleton_iff.2 (congrArg Subtype.val hc)⟩
      rw [(Model.twoElementaryProduct_F (K := K)).inf_centralizer_left (g : ModGL .G2 K) hgW
        hgX] at hmem
      exact d.emb_mem_image hmem
    · refine Subgroup.mem_inf.2 ⟨d.inclusions.2.2.2.2.1 hx, mem_centralizer_singleton_iff.2 ?_⟩
      exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : d.W) ⟨d.emb g, ha⟩)

theorem mem_F_iff_commutator_X (hK : 4 ≤ Nat.card K) {s : G} (hs : s ∈ d.S) :
    s ∈ d.F ↔ ∀ g ∈ d.S, s * g * s⁻¹ * g⁻¹ ∈ d.X := by
  refine ⟨fun hsF g hg => ?_, fun h => ?_⟩
  · have := (d.mem_F_iff_commutator hK hs).1 hsF g hg
    exact d.inclusions.2.1 (by simpa only [commutatorElement_def] using this)
  · obtain ⟨a, ha, rfl⟩ := d.mem_image.1 hs
    refine d.emb_mem_image (Model.mem_F_of_forall_commutator_mem_X ha fun y hy => ?_)
    have hya : y ∈ adjointGroup .G2 K := Model.S_le_adjointGroup K hy
    have := h (d.emb ⟨y, hya⟩) (d.emb_mem_image hy)
    have e : d.emb a * d.emb ⟨y, hya⟩ * (d.emb a)⁻¹ * (d.emb ⟨y, hya⟩)⁻¹ =
        d.emb (a * ⟨y, hya⟩ * a⁻¹ * ⟨y, hya⟩⁻¹) := by
      simp only [map_mul, map_inv]
    rw [e] at this
    have := d.emb_mem_image_iff.1 this
    simpa [commutatorElement_def] using this

end G2Data

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Local

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem yamadaW₃_le_yamadaR₃ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaW₃ d t ≤ yamadaR₃ d t := by
  obtain ⟨hW₃V₃, -⟩ := h.yamadaW₃_facts hW d hK hD
  obtain ⟨-, hV₃E₃, -⟩ := h.yamadaV₃_facts hW d hK hD
  exact hW₃V₃.trans (hV₃E₃.trans (inf_le_left.trans le_sup_left))

theorem yamadaR₃_eq_sup (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaR₃ d t = yamadaW₃ d t ⊔ yamadaR₂ d t := by
  have hD := hQ.doubling
  obtain ⟨-, hR₂R₃, -, -, -⟩ := h.yamadaR₃_facts hW d hK hD
  obtain ⟨-, -, -, -, ⟨hR₃eq, -⟩, -⟩ := h.yamada_5_30_2 hW d hK hD
  have hW₃R₃ := h.yamadaW₃_le_yamadaR₃ hW d hK hD
  have htR₂ : t ∈ yamadaR₂ d t :=
    (h.yamada_5_6_1 d hK).2.1 (mem_sup_left (h.t_mem_yamadaC₁ d hK))
  refine le_antisymm ?_ (sup_le hW₃R₃ hR₂R₃)
  rw [← hR₃eq]
  refine sup_le (sup_le le_sup_left (sup_le (le_sup_right.trans le_sup_right) ?_))
    ((zpowers_le).2 (mem_sup_right htR₂))
  exact (h.yamadaY₂_le_yamadaR₂ d hK hD).trans le_sup_right

theorem yamadaR₃_eq_mul (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    (yamadaR₃ d t : Set G) = (yamadaW₃ d t : Set G) * (yamadaR₂ d t : Set G) := by
  have hD := hQ.doubling
  obtain ⟨-, -, hR₃R₂, -, -⟩ := h.yamadaR₃_facts hW d hK hD
  have hW₃N : yamadaW₃ d t ≤ normalizer (yamadaR₂ d t : Set G) :=
    (h.yamadaW₃_le_yamadaR₃ hW d hK hD).trans hR₃R₂
  rw [h.yamadaR₃_eq_sup hW d hK hQ]
  exact coe_sup_eq_mul hW₃N

theorem twoElementaryProduct_yamadaF₂ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    Common.TwoElementaryProduct (yamadaF₂ d t) (yamadaW₂ d t) (yamadaX₂ d t) := by
  have hD := hQ.doubling
  obtain ⟨-, -, -, -, -, -, hFM, -⟩ := d.inclusions
  have hFY₂ : d.F ≤ centralizer (yamadaY₂ d t : Set G) :=
    hFM.trans (h.M_le_centralizer_yamadaY₂ d hK hD)
  have hW₂ : CFSG.IsElementaryAbelian 2 ↥(yamadaW₂ d t) :=
    isElementaryAbelian_of_forall (fun x hx y hy =>
      mul_comm_of_mul_self_eq_one_aux (h.yamadaW₂_mul_self hW d hK hD hx)
        (h.yamadaW₂_mul_self hW d hK hD hy) (h.yamadaW₂_mul_self hW d hK hD (mul_mem hx hy)))
      fun x hx => h.yamadaW₂_mul_self hW d hK hD hx
  have hX₂ : CFSG.IsElementaryAbelian 2 ↥(yamadaX₂ d t) :=
    isElementaryAbelian_of_forall (fun x hx y hy =>
      mul_comm_of_mul_self_eq_one_aux (h.yamadaX₂_mul_self hW d hK hD hx)
        (h.yamadaX₂_mul_self hW d hK hD hy) (h.yamadaX₂_mul_self hW d hK hD (mul_mem hx hy)))
      fun x hx => h.yamadaX₂_mul_self hW d hK hD hx
  exact twoElementaryProduct_sup_central d.twoElementaryProduct_F hFY₂
    (fun x hx y hy => h.yamadaY₂_mul_comm d hK hD hx hy) hW₂ hX₂

theorem yamadaR₃_le_normalizer_W₃_V₃ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaR₃ d t ≤ normalizer (yamadaW₃ d t : Set G) ⊓ normalizer (yamadaV₃ d t : Set G) := by
  have hD := hQ.doubling
  obtain ⟨-, -, hW₃eq, -⟩ := h.yamada_5_33_3_uniform hW d hK hQ.doubling
  obtain ⟨-, -, hR₃L₃, hR₃V₂, -⟩ := h.yamadaL₃_facts hW d hK hD
  obtain ⟨-, -, -, hW₂W₃, -, hV₃eq, -⟩ := h.yamadaW₃_facts hW d hK hD
  have hR₃W₂ : yamadaR₃ d t ≤ normalizer (yamadaW₂ d t : Set G) :=
    hR₃V₂.trans (h.normalizer_yamadaV₂_le hW d hK hD).1
  have hW₃N : yamadaR₃ d t ≤ normalizer (yamadaW₃ d t : Set G) := fun g hg => by
    rw [← hW₃eq]
    exact Common.mem_normalizer_inf (hR₃L₃ hg)
      (mem_normalizer_centralizer_of_mem_normalizer (hR₃W₂ hg))
  have hW₃V₃ : yamadaW₃ d t ≤ yamadaV₃ d t := by
    rw [← hV₃eq]
    exact le_sup_left
  have htV₃ : t ∈ yamadaV₃ d t := by
    rw [← hV₃eq]
    exact mem_sup_right (mem_zpowers t)
  have hWV₃ : d.W ≤ yamadaV₃ d t :=
    (le_sup_left.trans hW₂W₃).trans hW₃V₃
  have hL₃V : ∀ g ∈ yamadaL₃ d t, g ∈ normalizer (yamadaV₃ d t : Set G) := by
    intro g hg
    have hgR₃ : g ∈ yamadaR₃ d t := (le_sup_left : yamadaL₃ d t ≤ yamadaR₃ d t) hg
    apply mem_normalizer_of_conj_mem
    intro x hx
    rw [← hV₃eq] at hx
    have hle : yamadaW₃ d t ⊔ zpowers t ≤ (yamadaV₃ d t).comap (MulAut.conj g).toMonoidHom := by
      refine sup_le (fun w hw => ?_) ((zpowers_le).2 ?_)
      · rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        exact hW₃V₃ ((mem_normalizer_iff.1 (hW₃N hgR₃) w).1 hw)
      · obtain ⟨w, hw, e⟩ := (h.yamada_5_23_2 hW d hK hD).1 g hg
        rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, e]
        exact mul_mem htV₃ (hWV₃ hw)
    have := hle hx
    rwa [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
  have hSV : ∀ g ∈ d.S, g ∈ normalizer (yamadaV₃ d t : Set G) := by
    intro g hg
    have hgR₃ : g ∈ yamadaR₃ d t := (le_sup_right : d.S ≤ yamadaR₃ d t) hg
    rw [← hV₃eq]
    refine mem_normalizer_sup (hW₃N hgR₃) (mem_normalizer_zpowers ?_)
    exact mem_centralizer_singleton_iff.1 (h.S_le_centralizer d hg)
  refine fun g hg => ⟨hW₃N hg, ?_⟩
  exact (sup_le (fun x hx => hL₃V x hx) (fun x hx => hSV x hx) :
    yamadaR₃ d t ≤ normalizer (yamadaV₃ d t : Set G)) hg

theorem yamadaV₃_inf_centralizer_le (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaV₃ d t ⊓ centralizer ({t} : Set G) ≤ d.W ⊔ zpowers t := by
  have hD := hQ.doubling
  obtain ⟨-, hV₃E₃, -, hV₃R₂, -⟩ := h.yamadaV₃_facts hW d hK hD
  intro x hx
  obtain ⟨hxV₃, hxc⟩ := Subgroup.mem_inf.1 hx
  have hxR₃ : x ∈ yamadaR₃ d t :=
    (le_sup_left : yamadaL₃ d t ≤ yamadaR₃ d t) ((hV₃E₃.trans inf_le_left) hxV₃)
  have hxR₅ : x ∈ yamadaR₅ d t := by
    rw [(h.yamada_5_27_2 hW d hK hD).1.1]
    exact mem_sup_left hxR₃
  have hxR : x ∈ yamadaR d t := by
    rw [← (h.yamada_5_27_1 hW d hK hD).2.2]
    exact Subgroup.mem_inf.2 ⟨hxR₅, hxc⟩
  have hxR₂ : x ∈ yamadaR₂ d t := (h.yamadaR₂_inf_centralizer d hK).1 hxR
  have hxV₂ : x ∈ yamadaV₂ d t := by
    rw [← hV₃R₂]
    exact Subgroup.mem_inf.2 ⟨hxV₃, hxR₂⟩
  obtain ⟨htW₂, -⟩ := h.t_mem_normalizer_yamadaW₂ d hK hD
  obtain ⟨w, hw, τ, hτ, rfl⟩ := Common.exists_mul_of_le_normalizer ((zpowers_le).2 htW₂) x hxV₂
  have hτt : τ * t = t * τ := by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hτ
    exact (Commute.zpow_left (Commute.refl t) k).eq
  have hwt : w * t = t * w := by
    have e : w * τ * t = t * (w * τ) := mem_centralizer_singleton_iff.1 hxc
    have e2 : w * t * τ = t * w * τ := by
      calc w * t * τ = w * (t * τ) := by group
        _ = w * (τ * t) := by rw [hτt]
        _ = w * τ * t := by group
        _ = t * (w * τ) := e
        _ = t * w * τ := by group
    exact mul_right_cancel e2
  have hwW : w ∈ d.W := by
    rw [← h.yamadaW₂_inf_centralizer d hK hD]
    exact Subgroup.mem_inf.2 ⟨hw, mem_centralizer_singleton_iff.2 hwt⟩
  exact mul_mem (mem_sup_left hwW) (mem_sup_right hτ)

theorem yamadaW₃_inf_yamadaR (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaW₃ d t ⊓ yamadaR d t = d.W := by
  have hD := hQ.doubling
  obtain ⟨hW₃V₃, -, -, hW₂W₃, htW₃, -⟩ := h.yamadaW₃_facts hW d hK hD
  obtain ⟨-, -, -, -, hWF, hFD, -, hDS, -, -⟩ := d.inclusions
  have hWW₃ : d.W ≤ yamadaW₃ d t := (le_sup_left : d.W ≤ yamadaW₂ d t).trans hW₂W₃
  have hRc : yamadaR d t ≤ centralizer ({t} : Set G) := by
    rw [h.yamadaR_eq d]
    exact sup_le (h.S_le_centralizer d) ((zpowers_le).2 h.t_mem_centralizer)
  refine le_antisymm (fun x hx => ?_) (le_inf hWW₃ ?_)
  · obtain ⟨hxW₃, hxR⟩ := Subgroup.mem_inf.1 hx
    have hx' : x ∈ d.W ⊔ zpowers t :=
      h.yamadaV₃_inf_centralizer_le hW d hK hQ (Subgroup.mem_inf.2 ⟨hW₃V₃ hxW₃, hRc hxR⟩)
    have htN : zpowers t ≤ normalizer (d.W : Set G) := (zpowers_le).2
      (Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun w hw =>
        mem_centralizer_singleton_iff.1 (h.L_le_centralizer (d.image_le _ hw))))
    obtain ⟨w, hw, τ, hτ, rfl⟩ := Common.exists_mul_of_le_normalizer htN x hx'
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hτ
    rcases h.zpow_eq_one_or_eq k with hk | hk
    · rw [hk, mul_one]
      exact hw
    · exfalso
      rw [hk] at hxW₃
      apply htW₃
      have := mul_mem (inv_mem (hWW₃ hw)) hxW₃
      rwa [inv_mul_cancel_left] at this
  · rw [h.yamadaR_eq d]
    exact ((hWF.trans hFD).trans hDS).trans le_sup_left

theorem yamada_5_35_1 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    (Subgroup.upperCentralSeries (yamadaR₃ d t) 1).map (yamadaR₃ d t).subtype = d.U ∧
      (Subgroup.upperCentralSeries (yamadaR₃ d t) 2).map (yamadaR₃ d t).subtype =
        yamadaY₁ d t ∧
      (Subgroup.upperCentralSeries (yamadaR₃ d t) 3).map (yamadaR₃ d t).subtype =
        yamadaF₂ d t := by
  have hD := hQ.doubling
  obtain ⟨hUY, hYX, hYW, hXF, hWF, hFD, hFM, hDS, hMS, hSL⟩ := d.inclusions
  obtain ⟨hR₃R, hR₂R₃, hR₃R₂, -, -⟩ := h.yamadaR₃_facts hW d hK hD
  obtain ⟨hWel, -, -, -⟩ := h.yamada_5_33_3_uniform hW d hK hQ.doubling
  obtain ⟨-, -, -, hW₂W₃, -, -, -⟩ := h.yamadaW₃_facts hW d hK hD
  have hW₃c : ∀ x ∈ yamadaW₃ d t, ∀ y ∈ yamadaW₃ d t, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : yamadaW₃ d t) ⟨y, hy⟩)
  have hY₁Y₂ := h.yamadaY₁_le_yamadaY₂ d hK hD
  have hY₂W₃ : yamadaY₂ d t ≤ yamadaW₃ d t := le_sup_right.trans hW₂W₃
  have hY₁W₃ : yamadaY₁ d t ≤ yamadaW₃ d t := hY₁Y₂.trans hY₂W₃
  have hUW₃ : d.U ≤ yamadaW₃ d t := (hUY.trans le_sup_left).trans hY₁W₃
  have hR₂N : yamadaR₂ d t ≤ normalizer (yamadaY₁ d t : Set G) :=
    h.yamadaR₂_le_normalizer_yamadaY₁ d hK hD
  have htR₂ : t ∈ yamadaR₂ d t :=
    (h.yamada_5_6_1 d hK).2.1 (mem_sup_left (h.t_mem_yamadaC₁ d hK))
  have htR₃ : t ∈ yamadaR₃ d t := hR₂R₃ htR₂
  have hR₃mul := h.yamadaR₃_eq_mul hW d hK hQ
  have hfac : ∀ g ∈ yamadaR₃ d t, ∃ w ∈ yamadaW₃ d t, ∃ r ∈ yamadaR₂ d t, g = w * r := by
    intro g hg
    rw [← SetLike.mem_coe, hR₃mul, Set.mem_mul] at hg
    obtain ⟨w, hw, r, hr, rfl⟩ := hg
    exact ⟨w, hw, r, hr, rfl⟩
  have h1 : (Subgroup.upperCentralSeries (yamadaR₃ d t) 1).map (yamadaR₃ d t).subtype = d.U := by
    rw [map_upperCentralSeries_one]
    refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
    · obtain ⟨hxR₃, hxc⟩ := Subgroup.mem_inf.1 hx
      have hxt : x ∈ centralizer ({t} : Set G) :=
        mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hxc t htR₃).symm
      have hxR₅ : x ∈ yamadaR₅ d t := by
        have := (h.yamada_5_27_2 hW d hK hD).1.1
        rw [this]
        exact mem_sup_left hxR₃
      have hxR : x ∈ yamadaR d t := by
        rw [← (h.yamada_5_27_1 hW d hK hD).2.2]
        exact Subgroup.mem_inf.2 ⟨hxR₅, hxt⟩
      have hxR₂ : x ∈ yamadaR₂ d t := (h.yamadaR₂_inf_centralizer d hK).1 hxR
      rw [← (h.yamada_5_5_4 d hK).2]
      exact Subgroup.mem_inf.2 ⟨hxR₂, mem_centralizer_iff.2 fun g hg => mem_centralizer_iff.1 hxc g (hR₂R₃ hg)⟩
    · have hxU := hx
      have hxZ' : x ∈ yamadaR₂ d t ⊓ centralizer (yamadaR₂ d t : Set G) := by
        rw [(h.yamada_5_5_4 d hK).2]
        exact hx
      obtain ⟨hxR₂, hxZ⟩ := Subgroup.mem_inf.1 hxZ'
      refine Subgroup.mem_inf.2 ⟨hR₂R₃ hxR₂, mem_centralizer_iff.2 fun g hg => ?_⟩
      obtain ⟨w, hw, r, hr, rfl⟩ := hfac g hg
      have e1 : x * w = w * x := hW₃c x (hUW₃ hxU) w hw
      have e2 : r * x = x * r := (mem_centralizer_iff.1 hxZ r hr)
      calc w * r * x = w * (r * x) := by group
        _ = w * (x * r) := by rw [e2]
        _ = (w * x) * r := by group
        _ = (x * w) * r := by rw [e1]
        _ = x * (w * r) := by group
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_mul_t
  have hY₁R₂ : yamadaY₁ d t ≤ yamadaR₂ d t := hY₁Y₂.trans (h.yamadaY₂_le_yamadaR₂ d hK hD)
  have h2 : (Subgroup.upperCentralSeries (yamadaR₃ d t) 2).map (yamadaR₃ d t).subtype =
      yamadaY₁ d t := by
    refine map_upperCentralSeries_succ h1 (hY₁R₂.trans hR₂R₃) fun x hx => ?_
    constructor
    · intro hxY g hg
      obtain ⟨w, hw, r, hr, rfl⟩ := hfac g hg
      have hxr : x * r * x⁻¹ * r⁻¹ ∈ d.U :=
        (h.mem_yamadaY₁_iff d hK hD (hY₁R₂ hxY)).1 hxY r hr
      have e1 : x * w = w * x := hW₃c x (hY₁W₃ hxY) w hw
      have e2 : w * (x * r * x⁻¹ * r⁻¹) = (x * r * x⁻¹ * r⁻¹) * w :=
        hW₃c w hw _ (hUW₃ hxr)
      have hA : x * w * x⁻¹ * w⁻¹ = 1 := by rw [e1]; group
      have hB : w * (x * r * x⁻¹ * r⁻¹) * w⁻¹ = x * r * x⁻¹ * r⁻¹ := by rw [e2]; group
      rw [show x * (w * r) * x⁻¹ * (w * r)⁻¹ =
        (x * w * x⁻¹ * w⁻¹) * (w * (x * r * x⁻¹ * r⁻¹) * w⁻¹) by group, hA, hB, one_mul]
      exact hxr
    · intro hc
      have hxR₂ : x ∈ yamadaR₂ d t := by
        refine (h.mem_yamadaR₂_iff hW d hK hD).2 ⟨hR₃R hx, ?_⟩
        have hct := hc t htR₃
        rw [ht'] at hct
        have e : t * x * t * x⁻¹ = (x * t * x⁻¹ * t)⁻¹ := by
          calc t * x * t * x⁻¹ = t⁻¹ * x * t⁻¹ * x⁻¹ := by rw [ht']
            _ = (x * t * x⁻¹ * t)⁻¹ := by group
        rw [e]
        exact (hUY.trans le_sup_left) (inv_mem hct)
      exact (h.mem_yamadaY₁_iff d hK hD hxR₂).2 fun g hg => hc g (hR₂R₃ hg)
  have hY₂R₂ := h.yamadaY₂_le_yamadaR₂ d hK hD
  have hSR₃ : d.S ≤ yamadaR₃ d t := le_sup_right
  have hFR₃ : d.F ≤ yamadaR₃ d t := (hFD.trans hDS).trans hSR₃
  have hF₂R₃ : yamadaF₂ d t ≤ yamadaR₃ d t :=
    sup_le hFR₃ (hY₂R₂.trans hR₂R₃)
  have hY₁N : yamadaR₃ d t ≤ normalizer (yamadaY₁ d t : Set G) := by
    rw [h.yamadaR₃_eq_sup hW d hK hQ]
    refine sup_le (fun w hw => ?_) hR₂N
    refine mem_normalizer_of_conj_mem fun y hy => ?_
    have hwy : w * y = y * w := hW₃c w hw y (hY₁W₃ hy)
    rw [hwy, mul_inv_cancel_right]
    exact hy
  have hB : ∀ g ∈ yamadaR₃ d t, ∀ b ∈ yamadaY₁ d t, g * b * g⁻¹ ∈ yamadaY₁ d t :=
    fun g hg b hb => (mem_normalizer_iff.1 (hY₁N hg) b).1 hb
  set Z := Common.centralizerMod (yamadaR₃ d t) (yamadaR₃ d t) (yamadaY₁ d t)
    (fun g hg y hy => mul_mem (mul_mem hg hy) (inv_mem hg)) hB with hZdef
  have hFZ : d.F ≤ Z := fun f hf => by
    refine ⟨hFR₃ hf, fun y hy => ?_⟩
    have := ((h.commutator_mem_of_mem_yamadaRstar d hK hD (hR₃R hy)).2 f (mem_sup_left hf))
    rw [show f * y * f⁻¹ * y⁻¹ = (y * f * y⁻¹ * f⁻¹)⁻¹ by group]
    exact inv_mem this
  have hY₂Z : yamadaY₂ d t ≤ Z := fun y hy => by
    refine ⟨hY₂R₂.trans hR₂R₃ hy, fun g hg => ?_⟩
    obtain ⟨w, hw, r, hr, rfl⟩ := hfac g hg
    have hyE₂ : y ∈ yamadaE₂ d t := mem_sup_left (mem_sup_right hy)
    have hc : y * r * y⁻¹ * r⁻¹ ∈ yamadaY₁ d t :=
      (h.mem_yamadaE₂_iff d hK hD (hY₂R₂ hy)).1 hyE₂ r hr
    have e1 : y * w = w * y := hW₃c y (hY₂W₃ hy) w hw
    have e2 : w * (y * r * y⁻¹ * r⁻¹) = (y * r * y⁻¹ * r⁻¹) * w :=
      hW₃c w hw _ (hY₁W₃ hc)
    have hA : y * w * y⁻¹ * w⁻¹ = 1 := by rw [e1]; group
    have hB' : w * (y * r * y⁻¹ * r⁻¹) * w⁻¹ = y * r * y⁻¹ * r⁻¹ := by rw [e2]; group
    rw [show y * (w * r) * y⁻¹ * (w * r)⁻¹ =
      (y * w * y⁻¹ * w⁻¹) * (w * (y * r * y⁻¹ * r⁻¹) * w⁻¹) by group, hA, hB', one_mul]
    exact hc
  have hF₂Z : yamadaF₂ d t ≤ Z := sup_le hFZ hY₂Z
  refine ⟨h1, h2, map_upperCentralSeries_succ h2 hF₂R₃ fun x hx => ⟨fun hxF g hg => ?_,
    fun hc => ?_⟩⟩
  · exact (hF₂Z hxF).2 g hg
  · have hxZ : x ∈ Z := ⟨hx, hc⟩
    have hxN : x ∈ normalizer (yamadaR₁ d t : Set G) := by
      refine mem_normalizer_of_conj_mem fun r hr => ?_
      have hrR₂ : r ∈ yamadaR₂ d t := (h.yamada_5_6_1 d hK).2.1 hr
      have h1' := hc r (hR₂R₃ hrR₂)
      rw [show x * r * x⁻¹ = (x * r * x⁻¹ * r⁻¹) * r by group]
      exact mul_mem (h.yamadaY₁_le_yamadaR₁ d hK hD h1') hr
    have hxR₅ : x ∈ yamadaR₅ d t := by
      have := (h.yamada_5_27_2 hW d hK hD).1.1
      rw [this]
      exact mem_sup_left hx
    have hxR₂ : x ∈ yamadaR₂ d t := by
      rw [← (h.yamada_5_28 hW d hK hD).1]
      exact Subgroup.mem_inf.2 ⟨hxR₅, hxN⟩
    have hxE₂ : x ∈ yamadaE₂ d t :=
      (h.mem_yamadaE₂_iff d hK hD hxR₂).2 fun g hg => hc g (hR₂R₃ hg)
    obtain ⟨htF₂, htF₂'⟩ := h.t_mem_normalizer_yamadaF₂ d hK hD
    obtain ⟨a, ha, τ, hτ, rfl⟩ :=
      Common.exists_mul_of_le_normalizer ((zpowers_le).2 htF₂) x hxE₂
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hτ
    rcases h.zpow_eq_one_or_eq k with hk | hk
    · rw [hk, mul_one]
      exact ha
    · exfalso
      rw [hk] at hxZ
      have htZ : t ∈ Z := by
        have := mul_mem (inv_mem (hF₂Z ha)) hxZ
        rwa [inv_mul_cancel_left] at this
      obtain ⟨w, hw, hwY⟩ := d.exists_mem_W_not_mem_Y hQ.four_le
      obtain ⟨g, hg, e⟩ := (h.yamada_5_23_2 hW d hK hD).2 w hw
      have hgR₃ : g ∈ yamadaR₃ d t := (le_sup_left : yamadaL₃ d t ≤ yamadaR₃ d t) hg
      have hcomm := htZ.2 g hgR₃
      have hval : t * g * t⁻¹ * g⁻¹ = w := by
        rw [ht']
        calc t * g * t * g⁻¹ = t * (g * t * g⁻¹) := by group
          _ = t * (t * w) := by rw [e]
          _ = (t * t) * w := by group
          _ = w := by rw [h.t_mul_t, one_mul]
      rw [hval] at hcomm
      apply hwY
      rw [← h.yamadaY₁_inf_centralizer d hK hD]
      exact ⟨hcomm, mem_centralizer_singleton_iff.2 (mem_centralizer_singleton_iff.1
        (h.L_le_centralizer (d.image_le _ hw)))⟩

theorem yamada_5_35_2 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    (Subgroup.upperCentralSeries (yamadaL₃ d t) 1).map (yamadaL₃ d t).subtype = d.Y ∧
      (Subgroup.upperCentralSeries (yamadaL₃ d t) 2).map (yamadaL₃ d t).subtype =
        yamadaW₂ d t := by
  have hD := hQ.doubling
  obtain ⟨hUY, hYX, hYW, hXF, hWF, hFD, hFM, hDS, hMS, hSL⟩ := d.inclusions
  obtain ⟨hL₂L₃, -, hR₃L₃, hR₃V₂, hL₃S⟩ := h.yamadaL₃_facts hW d hK hD
  obtain ⟨hWel, -, -, -⟩ := h.yamada_5_33_3_uniform hW d hK hQ.doubling
  obtain ⟨hW₃V₃, -, -, hW₂W₃, -, hV₃eq, -⟩ := h.yamadaW₃_facts hW d hK hD
  obtain ⟨hV₂V₃, hV₃E₃, hV₃L₂, hV₃R₂, -, hV₃L₂eq, hV₃NL₂, -, -⟩ := h.yamadaV₃_facts hW d hK hD
  have hW₃c : ∀ x ∈ yamadaW₃ d t, ∀ y ∈ yamadaW₃ d t, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : yamadaW₃ d t) ⟨y, hy⟩)
  have htL₂ : t ∈ yamadaL₂ d t := h.tM_le_yamadaL₂ d hK (mem_sup_right (mem_zpowers t))
  have htL₃ : t ∈ yamadaL₃ d t := hL₂L₃ htL₂
  have hY₂W₃ : yamadaY₂ d t ≤ yamadaW₃ d t := le_sup_right.trans hW₂W₃
  have hYY₂ := h.Y_le_yamadaY₂ d hK hD
  have hYW₃ : d.Y ≤ yamadaW₃ d t := hYY₂.trans hY₂W₃
  have hW₃L₃ : yamadaW₃ d t ≤ yamadaL₃ d t :=
    hW₃V₃.trans (hV₃E₃.trans inf_le_left)
  have hL₃eq : yamadaL₃ d t = yamadaW₃ d t ⊔ yamadaL₂ d t := by
    refine le_antisymm ?_ (sup_le hW₃L₃ hL₂L₃)
    rw [← hV₃L₂eq, ← hV₃eq]
    exact sup_le (sup_le le_sup_left ((zpowers_le).2 (mem_sup_right htL₂))) le_sup_right
  have hL₃mul : (yamadaL₃ d t : Set G) = (yamadaW₃ d t : Set G) * (yamadaL₂ d t : Set G) := by
    rw [hL₃eq]
    exact coe_sup_eq_mul (hW₃V₃.trans hV₃NL₂)
  have hfac : ∀ g ∈ yamadaL₃ d t, ∃ w ∈ yamadaW₃ d t, ∃ l ∈ yamadaL₂ d t, g = w * l := by
    intro g hg
    rw [← SetLike.mem_coe, hL₃mul, Set.mem_mul] at hg
    obtain ⟨w, hw, l, hl, rfl⟩ := hg
    exact ⟨w, hw, l, hl, rfl⟩
  obtain ⟨hL₂Y, -, -, -⟩ := h.two_core_L₂ d hK
  have hL₃Y : yamadaL₃ d t ≤ centralizer (d.Y : Set G) := by
    rw [hL₃eq]
    refine sup_le (fun w hw => mem_centralizer_iff.2 fun y hy => (hW₃c w hw y (hYW₃ hy)).symm) hL₂Y
  have hYL₂ : d.Y ≤ yamadaL₂ d t :=
    ((hYX.trans (hXF.trans hFM)).trans le_sup_left).trans (h.tM_le_yamadaL₂ d hK)
  have h1 : (Subgroup.upperCentralSeries (yamadaL₃ d t) 1).map (yamadaL₃ d t).subtype = d.Y := by
    rw [map_upperCentralSeries_one]
    refine le_antisymm (fun x hx => ?_) (fun y hy => ?_)
    · obtain ⟨hxL₃, hxc⟩ := Subgroup.mem_inf.1 hx
      have hxt : x * t = t * x := (mem_centralizer_iff.1 hxc t htL₃).symm
      have hκ : t * x * t * x⁻¹ ∈ d.Y := by
        rw [← hxt, show x * t * t * x⁻¹ = x * (t * t) * x⁻¹ by group, h.t_mul_t, mul_one,
          mul_inv_cancel]
        exact one_mem _
      have hxN : x ∈ normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G) :=
        (h.crossed_mem_Y_iff hW d hK hD (hR₃V₂ ((le_sup_left : yamadaL₃ d t ≤ yamadaR₃ d t)
hxL₃))).1 hκ
      have hxL₂ : x ∈ yamadaL₂ d t := h.yamadaL₃_inf_le d hK hD (Subgroup.mem_inf.2 ⟨hxL₃, hxN⟩)
      rw [← (h.yamada_5_5_4 d hK).1]
      exact Subgroup.mem_inf.2 ⟨hxL₂, mem_centralizer_iff.2 fun g hg => mem_centralizer_iff.1 hxc g
(hL₂L₃ hg)⟩
    · refine Subgroup.mem_inf.2 ⟨hL₂L₃ (hYL₂ hy), mem_centralizer_iff.2 fun g hg => ?_⟩
      obtain ⟨w, hw, l, hl, rfl⟩ := hfac g hg
      have e1 : y * w = w * y := hW₃c y (hYW₃ hy) w hw
      have e2 : l * y = y * l := (mem_centralizer_iff.1 (hL₂Y hl) y hy).symm
      calc w * l * y = w * (l * y) := by group
        _ = w * (y * l) := by rw [e2]
        _ = (w * y) * l := by group
        _ = (y * w) * l := by rw [e1]
        _ = y * (w * l) := by group
  refine ⟨h1, ?_⟩
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_mul_t
  have hY₂W₂ : yamadaY₂ d t ≤ yamadaW₂ d t := le_sup_right
  have hW₂L₂ : yamadaW₂ d t ≤ yamadaL₂ d t :=
    sup_le ((hWF.trans hFM).trans (le_sup_left.trans (h.tM_le_yamadaL₂ d hK)))
      (h.yamadaY₂_le_yamadaL₂ d hK hD)
  have hW₂L₃ : yamadaW₂ d t ≤ yamadaL₃ d t := hW₂W₃.trans hW₃L₃
  have hL₂NY : ∀ g ∈ yamadaL₂ d t, g ∈ normalizer (d.Y : Set G) := fun g hg =>
    Subgroup.centralizer_le_normalizer _ (hL₂Y hg)
  have hL₂comm : ∀ x ∈ yamadaL₂ d t, ∀ y ∈ yamadaL₂ d t, x * y * x⁻¹ * y⁻¹ ∈ d.Y := by
    intro x hx y hy
    have hxx := h.mul_self_mem_Y_of_mem_yamadaL₂ d hK hD hx
    have hyy := h.mul_self_mem_Y_of_mem_yamadaL₂ d hK hD hy
    have hxy := h.mul_self_mem_Y_of_mem_yamadaL₂ d hK hD (mul_mem hx hy)
    rw [show x * y * x⁻¹ * y⁻¹ =
      x * y * (x * y) * (y⁻¹ * (x * x)⁻¹ * y⁻¹⁻¹) * (y * y)⁻¹ by group]
    exact mul_mem (mul_mem hxy ((mem_normalizer_iff.1 (hL₂NY _ (inv_mem hy)) _).1
      (inv_mem hxx))) (inv_mem hyy)
  have hW₂A : ∀ x ∈ yamadaW₂ d t, ∀ g ∈ yamadaL₃ d t, x * g * x⁻¹ * g⁻¹ ∈ d.Y := by
    intro x hx g hg
    obtain ⟨w, hw, l, hl, rfl⟩ := hfac g hg
    have hxl : x * l * x⁻¹ * l⁻¹ ∈ d.Y := hL₂comm x (hW₂L₂ hx) l hl
    have e1 : x * w = w * x := hW₃c x (hW₂W₃ hx) w hw
    have e2 : w * (x * l * x⁻¹ * l⁻¹) = (x * l * x⁻¹ * l⁻¹) * w :=
      hW₃c w hw _ (hYW₃ hxl)
    have hA : x * w * x⁻¹ * w⁻¹ = 1 := by rw [e1]; group
    have hB : w * (x * l * x⁻¹ * l⁻¹) * w⁻¹ = x * l * x⁻¹ * l⁻¹ := by rw [e2]; group
    rw [show x * (w * l) * x⁻¹ * (w * l)⁻¹ =
      (x * w * x⁻¹ * w⁻¹) * (w * (x * l * x⁻¹ * l⁻¹) * w⁻¹) by group, hA, hB, one_mul]
    exact hxl
  have hBY : ∀ g ∈ yamadaL₃ d t, ∀ b ∈ d.Y, g * b * g⁻¹ ∈ d.Y := fun g hg b hb => by
    rw [← mem_centralizer_iff.1 (hL₃Y hg) b hb, mul_inv_cancel_right]
    exact hb
  have hL₃W : ∀ g ∈ yamadaL₃ d t, g ∈ normalizer (d.W : Set G) := fun g hg =>
    (h.normalizer_yamadaV₂_le hW d hK hD).2.2
      (hR₃V₂ ((le_sup_left : yamadaL₃ d t ≤ yamadaR₃ d t) hg))
  have hBW : ∀ g ∈ yamadaL₃ d t, ∀ b ∈ d.W, g * b * g⁻¹ ∈ d.W := fun g hg b hb =>
    (mem_normalizer_iff.1 (hL₃W g hg) b).1 hb
  set A := Common.centralizerMod (yamadaL₃ d t) (yamadaL₃ d t) d.Y
    (fun g hg y hy => mul_mem (mul_mem hg hy) (inv_mem hg)) hBY with hAdef
  set Zw := Common.centralizerMod (yamadaL₃ d t) (yamadaL₃ d t) d.W
    (fun g hg y hy => mul_mem (mul_mem hg hy) (inv_mem hg)) hBW with hZwdef
  have hAZw : A ≤ Zw := fun x hx => ⟨hx.1, fun g hg => hYW (hx.2 g hg)⟩
  have hW₂A' : yamadaW₂ d t ≤ A := fun x hx => ⟨hW₂L₃ hx, fun g hg => hW₂A x hx g hg⟩
  have hkt1 : ∀ g ∈ yamadaL₃ d t, t * g * t⁻¹ * g⁻¹ ∈ d.W := by
    intro g hg
    obtain ⟨w, hw, e⟩ := (h.yamada_5_23_2 hW d hK hD).1 g hg
    have : t * g * t⁻¹ * g⁻¹ = w := by
      rw [ht']
      calc t * g * t * g⁻¹ = t * (g * t * g⁻¹) := by group
        _ = t * (t * w) := by rw [e]
        _ = (t * t) * w := by group
        _ = w := by rw [h.t_mul_t, one_mul]
    rw [this]
    exact hw
  have hkt2 : ∀ w ∈ d.W, ∃ g ∈ yamadaL₃ d t, t * g * t⁻¹ * g⁻¹ = w := by
    intro w hw
    obtain ⟨g, hg, e⟩ := (h.yamada_5_23_2 hW d hK hD).2 w hw
    refine ⟨g, hg, ?_⟩
    rw [ht']
    calc t * g * t * g⁻¹ = t * (g * t * g⁻¹) := by group
      _ = t * (t * w) := by rw [e]
      _ = (t * t) * w := by group
      _ = w := by rw [h.t_mul_t, one_mul]
  have htZw : t ∈ Zw := ⟨htL₃, hkt1⟩
  obtain ⟨w₀, hw₀, hw₀Y⟩ := d.exists_mem_W_not_mem_Y hQ.four_le
  have htA : t ∉ A := by
    intro htA
    obtain ⟨g, hg, e⟩ := hkt2 w₀ hw₀
    exact hw₀Y (e ▸ htA.2 g hg)
  have hlev := h.leviB_le_centralizer_inf_normalizer_Y d
  have hlevtY : d.leviB ≤ normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G) := fun a ha =>
    h.centralizer_inf_normalizer_Y_le d (hlev ha)
  obtain ⟨hNW, -, hNV₂⟩ := h.normalizer_tY_le d hK hD
  have hNL₃ : normalizer (yamadaV₂ d t : Set G) ≤ normalizer (yamadaL₃ d t : Set G) :=
    LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hlevL₃ : d.leviB ≤ normalizer (yamadaL₃ d t : Set G) := fun a ha => hNL₃ (hNV₂ (hlevtY ha))
  have hZwN : d.leviB ≤ normalizer (Zw : Set G) := by
    intro a ha
    refine mem_normalizer_of_conj_mem fun x hx => ?_
    have haL₃ := hlevL₃ ha
    have haW : a ∈ normalizer (d.W : Set G) := hNW (hlevtY ha)
    refine ⟨(mem_normalizer_iff.1 haL₃ x).1 hx.1, fun g hg => ?_⟩
    have hg' : a⁻¹ * g * a ∈ yamadaL₃ d t := (mem_normalizer_iff''.1 haL₃ g).1 hg
    have := (mem_normalizer_iff.1 haW _).1 (hx.2 _ hg')
    rwa [show a * (x * (a⁻¹ * g * a) * x⁻¹ * (a⁻¹ * g * a)⁻¹) * a⁻¹ =
      (a * x * a⁻¹) * g * (a * x * a⁻¹)⁻¹ * g⁻¹ by group] at this
  have hBM : d.leviB ≤ normalizer (d.M : Set G) := fun a ha =>
    (h.yamada_5_8_5 d hK).2 (hlevtY ha)
  have hWE : d.W ≤ Zw ⊓ d.M :=
    le_inf (fun w hw => hAZw (hW₂A' ((le_sup_left : d.W ≤ yamadaW₂ d t) hw))) (hWF.trans hFM)
  have hEdich := (d.yamada_3_16_2_G (E := Zw ⊓ d.M)
    (fun a ha => Common.mem_normalizer_inf (hZwN ha) (hBM ha))).2 hWE inf_le_right
  have hEM : Zw ⊓ d.M ≠ d.M := by
    intro hEM
    have hMZw : d.M ≤ Zw := fun m hm => by
      rw [← hEM] at hm
      exact hm.1
    have hMM₁ : d.M ≤ yamadaM₁ d t :=
      le_inf (le_sup_left.trans (h.tM_le_yamadaL₁ d hK)) (hMS.trans le_sup_left)
    have hWM₁ : d.W ≤ yamadaM₁ d t := (hWF.trans hFM).trans hMM₁
    have hYM₁ : d.Y ≤ yamadaM₁ d t := hYW.trans hWM₁
    have hL₃M₁ : yamadaL₃ d t ≤ normalizer (yamadaM₁ d t : Set G) := by
      intro g hg
      refine mem_normalizer_of_conj_mem fun x hx => ?_
      obtain ⟨m, hm, y, hy, rfl⟩ := Common.exists_mul_of_le_normalizer
        (h.yamadaY₂_le_normalizer_M d hK hD) x (h.yamadaM₁_le_yamadaM₂ d hK hD hx)
      have hyM₁ : y ∈ yamadaM₁ d t := by
        have := mul_mem (inv_mem (hMM₁ hm)) hx
        rwa [inv_mul_cancel_left] at this
      have h1m : g * m * g⁻¹ ∈ yamadaM₁ d t := by
        rw [show g * m * g⁻¹ = (m * g * m⁻¹ * g⁻¹)⁻¹ * m by group]
        exact mul_mem (inv_mem (hWM₁ ((hMZw hm).2 g hg))) (hMM₁ hm)
      have h1y : g * y * g⁻¹ ∈ yamadaM₁ d t := by
        rw [show g * y * g⁻¹ = (y * g * y⁻¹ * g⁻¹)⁻¹ * y by group]
        exact mul_mem (inv_mem (hYM₁ (hW₂A y (hY₂W₂ hy) g hg))) hyM₁
      rw [show g * (m * y) * g⁻¹ = (g * m * g⁻¹) * (g * y * g⁻¹) by group]
      exact mul_mem h1m h1y
    have hL₃R₅ : yamadaL₃ d t ≤ yamadaR₅ d t := by
      have := (h.yamada_5_27_2 hW d hK hD).1.1
      rw [this]
      exact le_sup_left.trans' (le_sup_left : yamadaL₃ d t ≤ yamadaR₃ d t)
    have hL₃R₂ : yamadaL₃ d t ≤ yamadaR₂ d t := fun g hg => by
      rw [← (h.yamada_5_28 hW d hK hD).2.2]
      exact Subgroup.mem_inf.2 ⟨hL₃R₅ hg, hL₃M₁ hg⟩
    have hL₃L₂ : yamadaL₃ d t ≤ yamadaL₂ d t := fun g hg => by
      rw [← h.yamadaL₃_inf_yamadaR₂ hW d hK hD]
      exact Subgroup.mem_inf.2 ⟨hg, hL₃R₂ hg⟩
    have hcard := Subgroup.card_le_of_le hL₃L₂
    rw [(h.card_yamadaL₃_R₃ hW d hK hD).1, h.card_yamadaL₂ d hK] at hcard
    have hq : 1 < Nat.card K := hQ.one_lt
    have := Nat.pow_lt_pow_right hq (show 7 < 8 by norm_num)
    linarith
  have hZwE : Zw ⊓ d.M = d.W := hEdich.resolve_right hEM
  have hZwM₂ : ∀ m ∈ yamadaM₂ d t, m ∈ Zw → m ∈ yamadaW₂ d t := by
    intro m hm hmZ
    obtain ⟨m₀, hm₀, y, hy, rfl⟩ := Common.exists_mul_of_le_normalizer
      (h.yamadaY₂_le_normalizer_M d hK hD) m hm
    have hyZ : y ∈ Zw := hAZw (hW₂A' (hY₂W₂ hy))
    have hm₀Z : m₀ ∈ Zw := by
      have := mul_mem hmZ (inv_mem hyZ)
      rwa [mul_inv_cancel_right] at this
    have hm₀W : m₀ ∈ d.W := by
      rw [← hZwE]
      exact ⟨hm₀Z, hm₀⟩
    exact mul_mem (mem_sup_left hm₀W) (mem_sup_right hy)
  refine map_upperCentralSeries_succ h1 hW₂L₃ fun x hx => ⟨fun hxW g hg => hW₂A x hxW g hg,
    fun hc => ?_⟩
  have hxA : x ∈ A := ⟨hx, hc⟩
  have hxL₂ : x ∈ yamadaL₂ d t := by
    have hct := hc t htL₃
    rw [ht'] at hct
    have hκ : t * x * t * x⁻¹ ∈ d.Y := by
      have e : t * x * t * x⁻¹ = (x * t * x⁻¹ * t)⁻¹ := by
        calc t * x * t * x⁻¹ = t⁻¹ * x * t⁻¹ * x⁻¹ := by rw [ht']
          _ = (x * t * x⁻¹ * t)⁻¹ := by group
      rw [e]
      exact inv_mem hct
    have hxN : x ∈ normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G) :=
      (h.crossed_mem_Y_iff hW d hK hD
        (hR₃V₂ ((le_sup_left : yamadaL₃ d t ≤ yamadaR₃ d t) hx))).1 hκ
    exact h.yamadaL₃_inf_le d hK hD (Subgroup.mem_inf.2 ⟨hx, hxN⟩)
  have hL₂eq := h.yamadaL₂_eq_sup d hK hD
  have hM₂L₂ := h.yamadaM₂_le_yamadaL₂ d hK hD
  rw [hL₂eq] at hxL₂
  obtain ⟨m, hm, τ, hτ, rfl⟩ := Common.exists_mul_of_le_normalizer
    ((zpowers_le).2 (h.yamadaL₂_le_normalizer_yamadaM₂ d hK hD htL₂)) x hxL₂
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hτ
  rcases h.zpow_eq_one_or_eq k with hk | hk
  · rw [hk, mul_one] at hxA ⊢
    exact hZwM₂ m hm (hAZw hxA)
  · exfalso
    rw [hk] at hxA
    have hmZ : m ∈ Zw := by
      have := mul_mem (hAZw hxA) (inv_mem htZw)
      rwa [mul_inv_cancel_right] at this
    have hmA : m ∈ A := hW₂A' (hZwM₂ m hm hmZ)
    have htA' : t ∈ A := by
      have := mul_mem (inv_mem hmA) hxA
      rwa [inv_mul_cancel_left] at this
    exact htA htA'

theorem yamada_5_35_5 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaW₃ d t ≤ yamadaL₃ d t ∧ ((yamadaW₃ d t).subgroupOf (yamadaL₃ d t)).Characteristic := by
  have hD := hQ.doubling
  obtain ⟨-, -, hW₃eq, -⟩ := h.yamada_5_33_3_uniform hW d hK hQ.doubling
  obtain ⟨hW₃V₃, -⟩ := h.yamadaW₃_facts hW d hK hD
  obtain ⟨-, hV₃E₃, -⟩ := h.yamadaV₃_facts hW d hK hD
  have hW₃L₃ : yamadaW₃ d t ≤ yamadaL₃ d t := hW₃V₃.trans (hV₃E₃.trans inf_le_left)
  refine ⟨hW₃L₃, characteristic_of_autImage fun φ => ?_⟩
  have hW₂φ : autImage φ (yamadaW₂ d t) = yamadaW₂ d t := by
    rw [← (h.yamada_5_35_2 hW d hK hQ).2]
    exact autImage_map_subtype φ _
  have hle : autImage φ (yamadaW₃ d t) ≤ yamadaW₃ d t := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_autImage.1 hx
    rw [← hW₃eq] at hy ⊢
    refine ⟨(φ y).2, mem_centralizer_iff.2 fun w hw => ?_⟩
    rw [← hW₂φ] at hw
    obtain ⟨z, hz, rfl⟩ := mem_autImage.1 hw
    have e : z * y = y * z := Subtype.ext (mem_centralizer_iff.1 hy.2 _ hz)
    have := congrArg (fun u : yamadaL₃ d t => ((φ u : yamadaL₃ d t) : G)) e
    simpa only [map_mul, Subgroup.coe_mul] using this
  exact Subgroup.eq_of_le_of_card_ge hle (card_autImage φ hW₃L₃).ge

end Local

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
