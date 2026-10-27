module

public import CFSG.LargeExtraspecial.S111TOdd
public import CFSG.LargeExtraspecial.S111BTIA
public import CFSG.LocalAnalysis.ZStar

public section

namespace CFSG.LargeExtraspecial.S11

open Subgroup

variable {H : Type*} [Group H]

structure ZHyp (X N L : Subgroup H) : Prop where
  NX : N ≤ X
  LX : L ≤ X
  Nn : ∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N
  N2 : IsPGroup 2 N
  Nc : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a
  L2 : IsPGroup 2 L
  Li : ∀ l ∈ L, l * l = 1
  Lc : ∀ a ∈ L, ∀ b ∈ L, a * b = b * a
  LN : ∀ l ∈ L, (∀ n ∈ N, n * l = l * n) → l ∈ N
  wc : ∀ x ∈ X, (∀ l ∈ L, ∀ l₂ ∈ L, x * l * x⁻¹ * l₂ * (x * l * x⁻¹)⁻¹ ∈ L ⊔ N) →
    L.map (MulAut.conj x).toMonoidHom = L
  nc : ∀ R : Subgroup H, R ≤ X → IsPGroup 2 R → L ≤ R → R ≤ normalizer (L : Set H)

namespace ZHyp

variable {X N L : Subgroup H} (Z : ZHyp X N L)
include Z

theorem le_cen : N ≤ X ⊓ centralizer (N : Set H) :=
  fun n hn => Subgroup.mem_inf.mpr ⟨Z.NX hn, mem_centralizer_iff.mpr fun m hm => Z.Nc m hm n hn⟩

theorem inv_mem_L {l : H} (hl : l ∈ L) : l⁻¹ = l := inv_eq_of_mul_eq_one_right (Z.Li l hl)

theorem conj_mem_cen {x y : H} (hx : x ∈ X) (hy : y ∈ X ⊓ centralizer (N : Set H)) :
    x * y * x⁻¹ ∈ X ⊓ centralizer (N : Set H) := by
  refine Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hx (Subgroup.mem_inf.mp hy).1) (inv_mem hx),
    mem_centralizer_iff.mpr fun n hn => ?_⟩
  have hn' : x⁻¹ * n * x⁻¹⁻¹ ∈ N := Z.Nn _ (inv_mem hx) n hn
  have hc := mem_centralizer_iff.mp (Subgroup.mem_inf.mp hy).2 _ hn'
  rw [inv_inv] at hc
  calc n * (x * y * x⁻¹) = x * ((x⁻¹ * n * x) * y) * x⁻¹ := by group
    _ = x * (y * (x⁻¹ * n * x)) * x⁻¹ := by rw [hc]
    _ = x * y * x⁻¹ * n := by group

theorem L_le_normalizer_cen : L ≤ normalizer ((X ⊓ centralizer (N : Set H) : Subgroup H) :
    Set H) := fun l hl => mem_normalizer_iff.mpr fun y => ⟨fun hy => Z.conj_mem_cen
  (Z.LX hl) hy, fun hy => by
    have := Z.conj_mem_cen (inv_mem (Z.LX hl)) hy
    rwa [show l⁻¹ * (l * y * l⁻¹) * l⁻¹⁻¹ = y by group] at this⟩

theorem L_le_normalizer_N : L ≤ normalizer (N : Set H) := fun l hl =>
  mem_normalizer_iff.mpr fun n => ⟨fun hn => Z.Nn l (Z.LX hl) n hn, fun hn => by
    have := Z.Nn _ (inv_mem (Z.LX hl)) _ hn
    rwa [show l⁻¹ * (l * n * l⁻¹) * l⁻¹⁻¹ = n by group] at this⟩

theorem sup_le_X : L ⊔ (X ⊓ centralizer (N : Set H)) ≤ X := sup_le Z.LX inf_le_left

theorem comm_mem_cen {y l : H} (hy : y ∈ X ⊓ centralizer (N : Set H)) (hl : l ∈ L) :
    y * l * y⁻¹ * l⁻¹ ∈ X ⊓ centralizer (N : Set H) := by
  have := mul_mem hy (Z.conj_mem_cen (Z.LX hl) (inv_mem hy))
  rwa [show y * (l * y⁻¹ * l⁻¹) = y * l * y⁻¹ * l⁻¹ by group] at this

theorem mem_normalizer_N {x : H} (hx : x ∈ X) : x ∈ normalizer (N : Set H) :=
  mem_normalizer_iff.mpr fun n => ⟨fun hn => Z.Nn x hx n hn, fun hn => by
    have := Z.Nn _ (inv_mem hx) _ hn
    rwa [show x⁻¹ * (x * n * x⁻¹) * x⁻¹⁻¹ = n by group] at this⟩

theorem isPGroup_zpowers {v : H} (hv : v * v ∈ N) : IsPGroup 2 (zpowers v) := by
  obtain ⟨a, ha⟩ := Z.N2 ⟨v * v, hv⟩
  have hva : v ^ (2 ^ (a + 1)) = 1 := by
    have h1 := congrArg Subtype.val ha
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at h1
    rw [pow_succ', pow_mul, sq]
    exact h1
  intro g
  obtain ⟨i, hi⟩ := mem_zpowers_iff.mp g.2
  refine ⟨a + 1, Subtype.ext ?_⟩
  simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
  rw [← hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hva, one_zpow]

theorem exists_pow_eq {a y : H} (ha : a ∈ X) (hy : y ∈ X ⊓ centralizer (N : Set H)) (j : ℕ) :
    ∃ y' ∈ X ⊓ centralizer (N : Set H), (a * y) ^ j = a ^ j * y' := by
  induction j with
  | zero => exact ⟨1, one_mem _, by simp⟩
  | succ j ih =>
    obtain ⟨y', hy', e⟩ := ih
    refine ⟨a⁻¹ * y' * a⁻¹⁻¹ * y, mul_mem (Z.conj_mem_cen (inv_mem ha) hy') hy, ?_⟩
    rw [pow_succ, e, pow_succ]
    group

theorem mem_of_mem_sup {w : H} (hw : w ∈ L ⊔ N) (hwY : w ∈ X ⊓ centralizer (N : Set H)) :
    w ∈ N := by
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup Z.L_le_normalizer_N hw
  have haY : a ∈ X ⊓ centralizer (N : Set H) := by
    have := mul_mem hwY (inv_mem (Z.le_cen hb))
    rwa [mul_inv_cancel_right] at this
  exact mul_mem (Z.LN a ha fun n hn => mem_centralizer_iff.mp
    (Subgroup.mem_inf.mp haY).2 n hn) hb

theorem exists_cen_conj {b l : H} (hb : b ∈ L ⊔ (X ⊓ centralizer (N : Set H))) (hl : l ∈ L) :
    ∃ y ∈ X ⊓ centralizer (N : Set H), b * l * b⁻¹ = y * l * y⁻¹ := by
  obtain ⟨a, ha, y, hy, rfl⟩ := exists_mul_of_mem_sup Z.L_le_normalizer_cen hb
  refine ⟨a * y * a⁻¹, Z.conj_mem_cen (Z.LX ha) hy, ?_⟩
  have hc : a⁻¹ * l * a = l := by rw [mul_assoc, Z.Lc l hl a ha, inv_mul_cancel_left]
  calc a * y * l * (a * y)⁻¹ = a * y * (a⁻¹ * l * a) * y⁻¹ * a⁻¹ := by rw [hc]; group
    _ = a * y * a⁻¹ * l * (a * y * a⁻¹)⁻¹ := by group

variable [Finite H]

theorem exists_sylow : ∃ R : Subgroup H, R ≤ L ⊔ (X ⊓ centralizer (N : Set H)) ∧
    (∀ r ∈ R, ∀ l ∈ L, r * l * r⁻¹ * l⁻¹ ∈ N) ∧
    ∀ W : Subgroup H, W ≤ L ⊔ (X ⊓ centralizer (N : Set H)) → IsPGroup 2 W →
      ∃ c ∈ L ⊔ (X ⊓ centralizer (N : Set H)), ∀ w ∈ W, c⁻¹ * w * c ∈ R := by
  set B := L ⊔ (X ⊓ centralizer (N : Set H)) with hB
  have hLB : L ≤ B := le_sup_left
  have hL' : IsPGroup 2 (L.subgroupOf B) :=
    Z.L2.comap_of_injective B.subtype B.subtype_injective
  obtain ⟨R₀, hR₀⟩ := hL'.exists_le_sylow
  have hRB : (R₀ : Subgroup B).map B.subtype ≤ B := map_subtype_le _
  have hR2 : IsPGroup 2 ((R₀ : Subgroup B).map B.subtype) := R₀.isPGroup'.map _
  have hLR : L ≤ (R₀ : Subgroup B).map B.subtype := fun l hl =>
    ⟨⟨l, hLB hl⟩, hR₀ (mem_subgroupOf.mpr hl), rfl⟩
  have hRN := Z.nc _ (hRB.trans Z.sup_le_X) hR2 hLR
  refine ⟨_, hRB, fun r hr l hl => ?_, fun W hWB hW2 => ?_⟩
  · have h1 : r * l * r⁻¹ * l⁻¹ ∈ L :=
      mul_mem ((mem_normalizer_iff.mp (hRN hr) l).mp hl) (inv_mem hl)
    have h2 : r * l * r⁻¹ * l⁻¹ ∈ X ⊓ centralizer (N : Set H) := by
      obtain ⟨y, hy, hyl⟩ := Z.exists_cen_conj (hRB hr) hl
      rw [hyl]
      exact Z.comm_mem_cen hy hl
    exact Z.LN _ h1 fun n hn => mem_centralizer_iff.mp (Subgroup.mem_inf.mp h2).2 n hn
  · have hW' : IsPGroup 2 (W.subgroupOf B) :=
      hW2.comap_of_injective B.subtype B.subtype_injective
    obtain ⟨P, hP⟩ := hW'.exists_le_sylow
    obtain ⟨c, hc⟩ := MulAction.exists_smul_eq B R₀ P
    refine ⟨c, c.2, fun w hw => ?_⟩
    have hwP : (⟨w, hWB hw⟩ : B) ∈ (P : Subgroup B) := hP (mem_subgroupOf.mpr hw)
    rw [← hc, Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem] at hwP
    refine ⟨_, hwP, ?_⟩
    simp [MulAut.smul_def]

theorem comm_mem_of_comm_mem {y l : H} (hy : y ∈ X ⊓ centralizer (N : Set H)) (hl : l ∈ L)
    (hc : y * l * y⁻¹ * l * (y * l * y⁻¹)⁻¹ * l⁻¹ ∈ N) : y * l * y⁻¹ * l⁻¹ ∈ N := by
  obtain ⟨R, hRB, hRc, hconj⟩ := Z.exists_sylow
  have hli : l⁻¹ = l := Z.inv_mem_L hl
  have hll : l * l = 1 := Z.Li l hl
  have hvY : y * l * y⁻¹ * l⁻¹ ∈ X ⊓ centralizer (N : Set H) := Z.comm_mem_cen hy hl
  have hui : (y * l * y⁻¹)⁻¹ = y * l * y⁻¹ := by
    rw [mul_inv_rev, mul_inv_rev, inv_inv, hli, mul_assoc]
  have hvv : (y * l * y⁻¹ * l⁻¹) * (y * l * y⁻¹ * l⁻¹) ∈ N := by
    have e : (y * l * y⁻¹ * l⁻¹) * (y * l * y⁻¹ * l⁻¹) =
        y * l * y⁻¹ * l * (y * l * y⁻¹)⁻¹ * l⁻¹ := by
      rw [hui, hli]; group
    rw [e]; exact hc
  have hW1 : IsPGroup 2 ↥(zpowers (y * l * y⁻¹ * l⁻¹) ⊔ N) :=
    (Z.isPGroup_zpowers hvv).to_sup_of_normal_right' Z.N2
      (zpowers_le.mpr (Z.mem_normalizer_N hvY.1))
  have hlW : ∀ w ∈ zpowers (y * l * y⁻¹ * l⁻¹) ⊔ N,
      l * w * l⁻¹ ∈ zpowers (y * l * y⁻¹ * l⁻¹) ⊔ N := by
    have hle : zpowers (y * l * y⁻¹ * l⁻¹) ⊔ N ≤
        (zpowers (y * l * y⁻¹ * l⁻¹) ⊔ N).comap (MulAut.conj l).toMonoidHom := by
      refine sup_le (zpowers_le.mpr ?_) fun n hn => ?_
      · simp only [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        have e : l * (y * l * y⁻¹ * l⁻¹) * l⁻¹ = (y * l * y⁻¹ * l⁻¹)⁻¹ := by
          rw [mul_inv_rev, hui, inv_inv]
          calc l * (y * l * y⁻¹ * l⁻¹) * l⁻¹ = l * (y * l * y⁻¹) * (l⁻¹ * l⁻¹) := by group
            _ = l * (y * l * y⁻¹) := by rw [hli, hll, mul_one]
        rw [e]
        exact mem_sup_left (inv_mem (mem_zpowers _))
      · simp only [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        exact mem_sup_right (Z.Nn l (Z.LX hl) n hn)
    intro w hw
    have := hle hw
    simpa only [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using this
  have hl2 : IsPGroup 2 (zpowers l) := by
    intro g
    obtain ⟨i, hi⟩ := mem_zpowers_iff.mp g.2
    refine ⟨1, Subtype.ext ?_⟩
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
    rw [← hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_one, sq, hll,
      one_zpow]
  have hlN : zpowers l ≤ normalizer ((zpowers (y * l * y⁻¹ * l⁻¹) ⊔ N : Subgroup H) : Set H) :=
    zpowers_le.mpr (mem_normalizer_iff.mpr fun w => ⟨fun hw => hlW w hw, fun hw => by
      have := hlW _ hw
      rwa [show l * (l * w * l⁻¹) * l⁻¹ = (l * l) * w * (l * l)⁻¹ by group, hll, one_mul,
        inv_one, mul_one] at this⟩)
  have hW2 := hl2.to_sup_of_normal_right' hW1 hlN
  have hWB : zpowers l ⊔ (zpowers (y * l * y⁻¹ * l⁻¹) ⊔ N) ≤ L ⊔ (X ⊓ centralizer (N : Set H)) :=
    sup_le (zpowers_le.mpr (mem_sup_left hl))
      (sup_le (zpowers_le.mpr (mem_sup_right hvY)) (Z.le_cen.trans le_sup_right))
  obtain ⟨c, hcB, hcR⟩ := hconj _ hWB hW2
  have hcX : c ∈ X := Z.sup_le_X hcB
  have hlR : c⁻¹ * l * c ∈ R := hcR _ (mem_sup_left (mem_zpowers l))
  have hvR : c⁻¹ * (y * l * y⁻¹ * l⁻¹) * c ∈ R :=
    hcR _ (mem_sup_right (mem_sup_left (mem_zpowers _)))
  have huR : c⁻¹ * (y * l * y⁻¹) * c ∈ R := by
    have := mul_mem hvR hlR
    rwa [show c⁻¹ * (y * l * y⁻¹ * l⁻¹) * c * (c⁻¹ * l * c) = c⁻¹ * (y * l * y⁻¹) * c by
      group] at this
  have h312 : ∀ x ∈ X, x * l * x⁻¹ ∈ R → x * l * x⁻¹ ∈ L ⊔ N := fun x hx hxR =>
    mem_sup_of_conj_mem_of_comm Z.LX Z.Nn Z.L2 Z.Lc Z.wc hx hl fun l₂ hl₂ =>
      hRc _ hxR l₂ hl₂
  have hl' := h312 c⁻¹ (inv_mem hcX) (by rwa [inv_inv])
  have hu' := h312 (c⁻¹ * y) (mul_mem (inv_mem hcX) hy.1) (by
    rwa [show c⁻¹ * y * l * (c⁻¹ * y)⁻¹ = c⁻¹ * (y * l * y⁻¹) * c by group])
  rw [inv_inv] at hl'
  rw [show c⁻¹ * y * l * (c⁻¹ * y)⁻¹ = c⁻¹ * (y * l * y⁻¹) * c by group] at hu'
  have hv' : c⁻¹ * (y * l * y⁻¹ * l⁻¹) * c ∈ L ⊔ N := by
    have := mul_mem hu' (inv_mem hl')
    rwa [show c⁻¹ * (y * l * y⁻¹) * c * (c⁻¹ * l * c)⁻¹ = c⁻¹ * (y * l * y⁻¹ * l⁻¹) * c by
      group] at this
  have hvY' : c⁻¹ * (y * l * y⁻¹ * l⁻¹) * c ∈ X ⊓ centralizer (N : Set H) := by
    have := Z.conj_mem_cen (inv_mem hcX) hvY
    rwa [inv_inv] at this
  have hvN := Z.mem_of_mem_sup hv' hvY'
  have := Z.Nn c hcX _ hvN
  rwa [show c * (c⁻¹ * (y * l * y⁻¹ * l⁻¹) * c) * c⁻¹ = y * l * y⁻¹ * l⁻¹ by group] at this

end ZHyp

theorem ZHyp.comm_mem_of_oddCore_eq_bot {H : Type} [Group H] [Finite H] {X N L : Subgroup H}
    (Z : ZHyp X N L) (hO : CFSG.oddCore ↥(X ⊓ centralizer (N : Set H)) = ⊥) {y l : H}
    (hy : y ∈ X ⊓ centralizer (N : Set H)) (hl : l ∈ L) : y * l * y⁻¹ * l⁻¹ ∈ N := by
  by_cases hlN : l ∈ N
  · exact mul_mem (Z.Nn y hy.1 l hlN) (inv_mem hlN)
  set B := L ⊔ (X ⊓ centralizer (N : Set H)) with hBdef
  have hNB : N ≤ B := Z.le_cen.trans le_sup_right
  have hlB : l ∈ B := mem_sup_left hl
  have hyB : y ∈ B := mem_sup_right hy
  have hN'n : (N.subgroupOf B).Normal := ⟨fun n hn b => by
    rw [mem_subgroupOf] at hn ⊢
    exact Z.Nn _ (Z.sup_le_X b.2) _ hn⟩
  let _ : Fintype (B ⧸ N.subgroupOf B) := Fintype.ofFinite _
  have hπeq : ∀ a b : B, (QuotientGroup.mk' (N.subgroupOf B) a =
      QuotientGroup.mk' (N.subgroupOf B) b) ↔ (a : H)⁻¹ * b ∈ N := fun a b => by
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, mem_subgroupOf]
    simp
  have hπ1 : ∀ a : B, QuotientGroup.mk' (N.subgroupOf B) a = 1 ↔ (a : H) ∈ N := fun a => by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf]
  set t := QuotientGroup.mk' (N.subgroupOf B) ⟨l, hlB⟩ with ht
  have ht1 : t ≠ 1 := fun h => hlN ((hπ1 _).mp h)
  have ht2 : t * t = 1 := by
    rw [ht, ← map_mul, hπ1]
    simp only [Subgroup.coe_mul]
    rw [Z.Li l hl]
    exact one_mem _
  have hiso : ∀ g : B ⧸ N.subgroupOf B, g * t * g⁻¹ * t = t * (g * t * g⁻¹) →
      g * t * g⁻¹ = t := by
    intro g hg
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective _ g
    rw [ht, ← map_inv, ← map_mul, ← map_mul, ← map_mul, ← map_mul, hπeq] at hg
    rw [ht, ← map_inv, ← map_mul, ← map_mul, hπeq]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hg ⊢
    obtain ⟨y', hy', e⟩ := Z.exists_cen_conj b.2 hl
    rw [e] at hg ⊢
    have hlu : l * (y' * l * y'⁻¹) ∈ X :=
      mul_mem (Z.LX hl) (mul_mem (mul_mem hy'.1 (Z.LX hl)) (inv_mem hy'.1))
    have hc : y' * l * y'⁻¹ * l * (y' * l * y'⁻¹)⁻¹ * l⁻¹ ∈ N := by
      have := Z.Nn _ hlu _ (inv_mem hg)
      rwa [show l * (y' * l * y'⁻¹) * ((y' * l * y'⁻¹ * l)⁻¹ * (l * (y' * l * y'⁻¹)))⁻¹ *
        (l * (y' * l * y'⁻¹))⁻¹ = y' * l * y'⁻¹ * l * (y' * l * y'⁻¹)⁻¹ * l⁻¹ by group] at this
    have h1 := Z.comm_mem_of_comm_mem hy' hl hc
    have := Z.Nn _ (inv_mem (Z.LX hl)) _ (inv_mem h1)
    rwa [show l⁻¹ * (y' * l * y'⁻¹ * l⁻¹)⁻¹ * l⁻¹⁻¹ = (y' * l * y'⁻¹)⁻¹ * l by group] at this
  obtain ⟨K, hKn, hKodd, hK⟩ := CFSG.ZStar.glauberman_zStar _ t ht1 ht2 hiso
  set Kh := (K.comap (QuotientGroup.mk' (N.subgroupOf B))).map B.subtype with hKh
  have hmemK : ∀ b : B, QuotientGroup.mk' (N.subgroupOf B) b ∈ K → (b : H) ∈ Kh :=
    fun b hb => ⟨b, hb, rfl⟩
  have hNK : N ≤ Kh := fun n hn => hmemK ⟨n, hNB hn⟩ (by
    rw [(hπ1 _).mpr hn]; exact one_mem _)
  have hKY : Kh ≤ X ⊓ centralizer (N : Set H) := by
    rintro _ ⟨b, hb, rfl⟩
    have hpow : (b : H) ^ Nat.card K ∈ N := by
      have h1 := pow_card_eq_one' (G := K) (x := ⟨_, hb⟩)
      have h2 := congrArg Subtype.val h1
      simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at h2
      rw [← map_pow, hπ1] at h2
      simpa using h2
    obtain ⟨a, ha, y₀, hy₀, hab⟩ := exists_mul_of_mem_sup Z.L_le_normalizer_cen b.2
    obtain ⟨y', hy', e⟩ := Z.exists_pow_eq (Z.LX ha) hy₀ (Nat.card K)
    obtain ⟨j, hj⟩ := hKodd
    have haK : a ^ Nat.card K = a := by
      rw [hj, pow_succ, pow_mul, sq, Z.Li a ha, one_pow, one_mul]
    rw [← hab, e, haK] at hpow
    have haY : a ∈ X ⊓ centralizer (N : Set H) := by
      have := mul_mem (Z.le_cen hpow) (inv_mem hy')
      rwa [mul_inv_cancel_right] at this
    change (b : H) ∈ _
    rw [← hab]
    exact mul_mem haY hy₀
  have hKn' : ∀ w ∈ X ⊓ centralizer (N : Set H), ∀ r ∈ Kh, w * r * w⁻¹ ∈ Kh := by
    rintro w hw _ ⟨b, hb, rfl⟩
    refine ⟨⟨w, mem_sup_right hw⟩ * b * ⟨w, mem_sup_right hw⟩⁻¹, ?_, rfl⟩
    change QuotientGroup.mk' (N.subgroupOf B) (⟨w, mem_sup_right hw⟩ * b *
      ⟨w, mem_sup_right hw⟩⁻¹) ∈ K
    rw [map_mul, map_mul, map_inv]
    exact hKn.conj_mem _ hb _
  have hKcard : Nat.card Kh = Nat.card N * Nat.card K := by
    rw [hKh, Subgroup.card_map_of_injective B.subtype_injective]
    have h1 : (K.comap (QuotientGroup.mk' (N.subgroupOf B))).index = K.index :=
      Subgroup.index_comap_of_surjective K (QuotientGroup.mk'_surjective _)
    have h2 := (K.comap (QuotientGroup.mk' (N.subgroupOf B))).card_mul_index
    have h3 := K.card_mul_index
    have h4 := (N.subgroupOf B).card_mul_index
    have h5 : Nat.card (N.subgroupOf B) = Nat.card N :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNB).toEquiv
    have hpos : 0 < K.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    apply Nat.eq_of_mul_eq_mul_right hpos
    calc Nat.card (K.comap (QuotientGroup.mk' (N.subgroupOf B))) * K.index
        = Nat.card (K.comap (QuotientGroup.mk' (N.subgroupOf B))) *
            (K.comap (QuotientGroup.mk' (N.subgroupOf B))).index := by rw [h1]
      _ = Nat.card (N.subgroupOf B) * (N.subgroupOf B).index := by rw [h2, h4]
      _ = Nat.card N * Nat.card (B ⧸ N.subgroupOf B) := by rw [h5]; rfl
      _ = Nat.card N * (Nat.card K * K.index) := by rw [h3]
      _ = Nat.card N * Nat.card K * K.index := by ring
  have hKN := le_of_oddCore_eq_bot hNK hKY inf_le_right Z.N2 hKn' hKodd hKcard hO
  refine hKN (hmemK (⟨y, hyB⟩ * ⟨l, hlB⟩ * ⟨y, hyB⟩⁻¹ * ⟨l, hlB⟩⁻¹) ?_)
  have := hK (QuotientGroup.mk' (N.subgroupOf B) ⟨y, hyB⟩)
  rwa [ht, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul] at this

end CFSG.LargeExtraspecial.S11
