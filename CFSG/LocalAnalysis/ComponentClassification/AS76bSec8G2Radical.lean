module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8G2Pair
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenLongCentralizer
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate3951

public noncomputable section

namespace CFSG.ComponentClassification.RankTwoExceptional

open Subgroup CFSG.Blueprint.Chevalley CFSG.ComponentClassification.UnbalancedCatalog
open scoped Pointwise

section Radical

variable {K : Type} [Field K] [CharP K 2]

variable (K) in
@[expose] def g2YGroup
    (α γ : K) : Subgroup (ModGL .G2 K) where
  carrier := {g | ∃ x : K, g = g2N 0 0 0 x (α * x) (γ * x)}
  mul_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨x', rfl⟩
    refine ⟨x + x', ?_⟩
    rw [g2N_zero_mul_g2N_zero]
    exact g2N_eq_g2N rfl (by ring) (by ring) rfl (by ring) (by ring)
  one_mem' := ⟨0, by rw [mul_zero, mul_zero, g2N_zero]⟩
  inv_mem' := by
    rintro _ ⟨x, rfl⟩
    exact ⟨x, by rw [g2N_zero_inv]; exact g2N_eq_g2N rfl rfl rfl rfl rfl (by ring)⟩

variable (K) in
@[expose] def g2BCGroup
    : Subgroup (ModGL .G2 K) where
  carrier := {g | ∃ y z : K, g = g2N 0 0 0 0 y z}
  mul_mem' := by
    rintro _ _ ⟨y, z, rfl⟩ ⟨y', z', rfl⟩
    refine ⟨y + y', z + z', ?_⟩
    rw [g2N_zero_mul_g2N_zero]
    exact g2N_eq_g2N rfl (by ring) (by ring) (by ring) rfl (by ring)
  one_mem' := ⟨0, 0, g2N_zero.symm⟩
  inv_mem' := by
    rintro _ ⟨y, z, rfl⟩
    exact ⟨y, z, by rw [g2N_zero_inv]; exact g2N_eq_g2N rfl rfl rfl rfl rfl (by ring)⟩

theorem mem_g2YGroup
    {α γ : K} {g : ModGL .G2 K} :
    g ∈ g2YGroup K α γ ↔ ∃ x : K, g = g2N 0 0 0 x (α * x) (γ * x) :=
  Iff.rfl

theorem mem_g2BCGroup
    {g : ModGL .G2 K} :
    g ∈ g2BCGroup K ↔ ∃ y z : K, g = g2N 0 0 0 0 y z :=
  Iff.rfl

theorem g2YGroup_zero
    : g2YGroup K 0 0 = rootSubgroup .G2 K g2v := by
  ext g
  rw [mem_g2YGroup, mem_rootSubgroup]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, by rw [pinnedX_v_eq_g2N]; exact g2N_eq_g2N rfl rfl rfl rfl (by ring) (by ring)⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, by rw [pinnedX_v_eq_g2N]; exact g2N_eq_g2N rfl rfl rfl rfl (by ring) (by ring)⟩

theorem g2YGroup_le
    (α γ : K) : g2YGroup K α γ ≤ g2ShortRadical K := by
  rintro _ ⟨x, rfl⟩
  exact g2N_mem_g2ShortRadical _ _ _

theorem g2BCGroup_le
    : g2BCGroup K ≤ g2ShortRadical K := by
  rintro _ ⟨y, z, rfl⟩
  exact g2N_mem_g2ShortRadical _ _ _

theorem g2YGroup_inf_g2BCGroup
    (α γ : K) : g2YGroup K α γ ⊓ g2BCGroup K = ⊥ := by
  refine eq_bot_iff.2 fun g hg => ?_
  obtain ⟨⟨x, rfl⟩, ⟨y, z, h⟩⟩ := mem_inf.1 hg
  obtain ⟨-, -, -, hx, -, -⟩ := g2N_injective h
  rw [mem_bot, hx, mul_zero, mul_zero, g2N_zero]

theorem g2YGroup_inf_g2YGroup
    {α γ α' γ' : K} (h : α ≠ α' ∨ γ ≠ γ') :
    g2YGroup K α γ ⊓ g2YGroup K α' γ' = ⊥ := by
  refine eq_bot_iff.2 fun g hg => ?_
  obtain ⟨⟨x, rfl⟩, ⟨x', h'⟩⟩ := mem_inf.1 hg
  obtain ⟨-, -, -, hx, hE, hF⟩ := g2N_injective h'
  subst hx
  by_cases hx0 : x = 0
  · rw [mem_bot, hx0, mul_zero, mul_zero, g2N_zero]
  · exfalso
    rcases h with h | h
    · exact h (mul_right_cancel₀ hx0 hE)
    · exact h (mul_right_cancel₀ hx0 hF)

theorem mem_g2YGroup_of
    {x y z : K} (hx : x ≠ 0) :
    g2N 0 0 0 x y z ∈ g2YGroup K (y / x) (z / x) :=
  ⟨x, g2N_eq_g2N rfl rfl rfl rfl (div_mul_cancel₀ y hx).symm (div_mul_cancel₀ z hx).symm⟩

theorem exists_mul_of_mem_g2ShortRadical
    (α γ : K) {g : ModGL .G2 K}
    (hg : g ∈ g2ShortRadical K) :
    ∃ y ∈ g2YGroup K α γ, ∃ w ∈ g2BCGroup K, g = y * w := by
  obtain ⟨x, e, f, rfl⟩ := hg
  refine ⟨_, ⟨x, rfl⟩, _, ⟨e + α * x, f + γ * x, rfl⟩, ?_⟩
  rw [g2N_zero_mul_g2N_zero]
  exact g2N_eq_g2N rfl (by ring) (by ring) (by ring) (by char2_ring) (by char2_ring)

theorem conj_r_radical
    (s x y z : K) :
    pinnedX .G2 K g2r s * g2N 0 0 0 x y z * pinnedX .G2 K g2r s = g2N 0 0 0 x (y + x * s) z := by
  rw [conj_r]
  exact g2N_eq_g2N rfl rfl (by ring) (by ring) (by ring) (by ring)

theorem conj_u_radical
    (s x y z : K) :
    pinnedX .G2 K g2u s * g2N 0 0 0 x y z * pinnedX .G2 K g2u s = g2N 0 0 0 x y (z + x * s) := by
  rw [conj_u]
  exact g2N_eq_g2N rfl rfl rfl rfl (by ring) (by ring)

theorem conj_r_mem_g2YGroup
    (s : K) {α γ : K} {g : ModGL .G2 K}
    (hg : g ∈ g2YGroup K α γ) :
    pinnedX .G2 K g2r s * g * pinnedX .G2 K g2r s ∈ g2YGroup K (α + s) γ := by
  obtain ⟨x, rfl⟩ := hg
  rw [conj_r_radical]
  exact ⟨x, g2N_eq_g2N rfl rfl rfl rfl (by ring) rfl⟩

theorem conj_u_mem_g2YGroup
    (s : K) {α γ : K} {g : ModGL .G2 K}
    (hg : g ∈ g2YGroup K α γ) :
    pinnedX .G2 K g2u s * g * pinnedX .G2 K g2u s ∈ g2YGroup K α (γ + s) := by
  obtain ⟨x, rfl⟩ := hg
  rw [conj_u_radical]
  exact ⟨x, g2N_eq_g2N rfl rfl rfl rfl rfl (by ring)⟩

theorem conj_r_eq_of_mem_g2BCGroup
    (s : K) {g : ModGL .G2 K} (hg : g ∈ g2BCGroup K) :
    pinnedX .G2 K g2r s * g * pinnedX .G2 K g2r s = g := by
  obtain ⟨y, z, rfl⟩ := hg
  rw [conj_r_radical]
  exact g2N_eq_g2N rfl rfl rfl rfl (by ring) rfl

theorem conj_u_eq_of_mem_g2BCGroup
    (s : K) {g : ModGL .G2 K} (hg : g ∈ g2BCGroup K) :
    pinnedX .G2 K g2u s * g * pinnedX .G2 K g2u s = g := by
  obtain ⟨y, z, rfl⟩ := hg
  rw [conj_u_radical]
  exact g2N_eq_g2N rfl rfl rfl rfl rfl (by ring)

theorem conj_r_mem_g2ShortRadical
    (s : K) {g : ModGL .G2 K} (hg : g ∈ g2ShortRadical K) :
    pinnedX .G2 K g2r s * g * pinnedX .G2 K g2r s ∈ g2ShortRadical K := by
  obtain ⟨x, y, z, rfl⟩ := hg
  rw [conj_r_radical]
  exact g2N_mem_g2ShortRadical _ _ _

theorem conj_u_mem_g2ShortRadical
    (s : K) {g : ModGL .G2 K} (hg : g ∈ g2ShortRadical K) :
    pinnedX .G2 K g2u s * g * pinnedX .G2 K g2u s ∈ g2ShortRadical K := by
  obtain ⟨x, y, z, rfl⟩ := hg
  rw [conj_u_radical]
  exact g2N_mem_g2ShortRadical _ _ _

theorem card_g2YGroup
    (α γ : K) : Nat.card (g2YGroup K α γ) = Nat.card K := by
  refine (Nat.card_eq_of_bijective (fun x : K => (⟨g2N 0 0 0 x (α * x) (γ * x),
    mem_g2YGroup.2 ⟨x, rfl⟩⟩ : g2YGroup K α γ)) ⟨fun x x' h => ?_, fun g => ?_⟩).symm
  · simp only at h
    exact (g2N_injective (Subtype.mk.inj h)).2.2.2.1
  · obtain ⟨x, hx⟩ := mem_g2YGroup.1 g.2
    exact ⟨x, Subtype.ext hx.symm⟩

theorem card_g2BCGroup
    : Nat.card (g2BCGroup K) = Nat.card K * Nat.card K := by
  rw [← Nat.card_prod]
  refine (Nat.card_eq_of_bijective (fun p : K × K => (⟨g2N 0 0 0 0 p.1 p.2,
    mem_g2BCGroup.2 ⟨p.1, p.2, rfl⟩⟩ : g2BCGroup K)) ⟨fun p p' h => ?_, fun g => ?_⟩).symm
  · simp only at h
    obtain ⟨-, -, -, -, h1, h2⟩ := g2N_injective (Subtype.mk.inj h)
    exact Prod.ext h1 h2
  · obtain ⟨y, z, hg⟩ := mem_g2BCGroup.1 g.2
    exact ⟨(y, z), Subtype.ext hg.symm⟩

end Radical

section Centre

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem g2_commute_v_of_mem
    {g : ModGL .G2 K} (hg : g ∈ g2ShortCent K) (s : K) :
    g * pinnedX .G2 K g2v s = pinnedX .G2 K g2v s * g := by
  obtain ⟨-, -, -, -, hset, -, -, -, hLv, -⟩ := even_G2_highest_short_root_centralizer K
  have hg' : g ∈ ((adjointGroup .G2 K ⊓ Subgroup.centralizer {pinnedX .G2 K g2v 1} :
      Subgroup (ModGL .G2 K)) : Set (ModGL .G2 K)) := hg
  rw [hset] at hg'
  obtain ⟨q, hq, l, hl, rfl⟩ := hg'
  have h1 : Commute q (pinnedX .G2 K g2v s) :=
    commute_of_mem_g2ShortRadical hq (pinnedX_v_mem_g2ShortRadical s)
  exact (h1.mul_left (hLv l hl s)).eq

theorem g2_commute_c_of_mem
    (h184 : G2Centr184) (hK4 : 4 ≤ Nat.card K)
    {g : ModGL .G2 K} (hg : g ∈ g2LongCent K) (s : K) :
    g * pinnedX .G2 K g2c s = pinnedX .G2 K g2c s * g := by
  obtain ⟨-, hcent⟩ := h184 K hK4
  have h1 : pinnedX .G2 K g2c s ∈ g2Centralizer K (g2LongCent K : Set (ModGL .G2 K)) := by
    rw [hcent]
    exact mem_rootSubgroup.2 ⟨s, rfl⟩
  exact mem_centralizer_iff.1 (mem_inf.1 h1).2 g hg

theorem g2_conj_v_eq
    {c : ModGL .G2 K} (hc : c ∈ adjointGroup .G2 K) {μ : K}
    (hμ : μ ≠ 0) (h : c * pinnedX .G2 K g2v 1 * c⁻¹ = pinnedX .G2 K g2v μ) (s : K) :
    c * pinnedX .G2 K g2v s * c⁻¹ = pinnedX .G2 K g2v (μ * s) := by
  set d := torusElt .G2 K g2ir (Units.mk0 μ hμ) with hd
  have hdv : ∀ s, d * pinnedX .G2 K g2v s * d⁻¹ = pinnedX .G2 K g2v (μ * s) := fun s => by
    rw [hd, torus_r_v, Units.val_mk0]
  have hm : d⁻¹ * c ∈ g2ShortCent K := by
    refine mem_inf.2 ⟨mul_mem (inv_mem (torusElt_mem_adjointGroup _ _)) hc,
      mem_centralizer_singleton_iff.2 ?_⟩
    have h1 : d⁻¹ * pinnedX .G2 K g2v μ * d = pinnedX .G2 K g2v 1 := by
      have h2 := hdv 1
      rw [mul_one] at h2
      rw [← h2]
      group
    calc d⁻¹ * c * pinnedX .G2 K g2v 1 = d⁻¹ * (c * pinnedX .G2 K g2v 1 * c⁻¹) * c := by group
      _ = d⁻¹ * pinnedX .G2 K g2v μ * d * (d⁻¹ * c) := by rw [h]; group
      _ = pinnedX .G2 K g2v 1 * (d⁻¹ * c) := by rw [h1]
  have h2 := g2_commute_v_of_mem hm s
  calc c * pinnedX .G2 K g2v s * c⁻¹ = d * (d⁻¹ * c * pinnedX .G2 K g2v s) * c⁻¹ := by group
    _ = d * (pinnedX .G2 K g2v s * (d⁻¹ * c)) * c⁻¹ := by rw [h2]
    _ = d * pinnedX .G2 K g2v s * d⁻¹ := by group
    _ = pinnedX .G2 K g2v (μ * s) := hdv s

theorem g2_conj_c_eq
    (h184 : G2Centr184) (hK4 : 4 ≤ Nat.card K)
    {c : ModGL .G2 K} (hc : c ∈ adjointGroup .G2 K) {μ : K} (hμ : μ ≠ 0)
    (h : c * pinnedX .G2 K g2c 1 * c⁻¹ = pinnedX .G2 K g2c μ) (s : K) :
    c * pinnedX .G2 K g2c s * c⁻¹ = pinnedX .G2 K g2c (μ * s) := by
  set d := torusElt .G2 K g2ia (Units.mk0 μ hμ) with hd
  have hdc : ∀ s, d * pinnedX .G2 K g2c s * d⁻¹ = pinnedX .G2 K g2c (μ * s) := fun s => by
    rw [hd, torus_a_c, Units.val_mk0]
  have hm : d⁻¹ * c ∈ g2LongCent K := by
    refine mem_inf.2 ⟨mul_mem (inv_mem (torusElt_mem_adjointGroup _ _)) hc,
      mem_centralizer_singleton_iff.2 ?_⟩
    have h1 : d⁻¹ * pinnedX .G2 K g2c μ * d = pinnedX .G2 K g2c 1 := by
      have h2 := hdc 1
      rw [mul_one] at h2
      rw [← h2]
      group
    calc d⁻¹ * c * pinnedX .G2 K g2c 1 = d⁻¹ * (c * pinnedX .G2 K g2c 1 * c⁻¹) * c := by group
      _ = d⁻¹ * pinnedX .G2 K g2c μ * d * (d⁻¹ * c) := by rw [h]; group
      _ = pinnedX .G2 K g2c 1 * (d⁻¹ * c) := by rw [h1]
  have h2 := g2_commute_c_of_mem h184 hK4 hm s
  calc c * pinnedX .G2 K g2c s * c⁻¹ = d * (d⁻¹ * c * pinnedX .G2 K g2c s) * c⁻¹ := by group
    _ = d * (pinnedX .G2 K g2c s * (d⁻¹ * c)) * c⁻¹ := by rw [h2]
    _ = d * pinnedX .G2 K g2c s * d⁻¹ := by group
    _ = pinnedX .G2 K g2c (μ * s) := hdc s

end Centre

section ShortLong

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem g2_conj_v_ne_c
    (h184 : G2Centr184) (hK4 : 4 ≤ Nat.card K) {c : ModGL .G2 K}
    (hc : c ∈ adjointGroup .G2 K) :
    c * pinnedX .G2 K g2v 1 * c⁻¹ ≠ pinnedX .G2 K g2c 1 := by
  intro h
  obtain ⟨hperf, -⟩ := h184 K hK4
  have hmap : (g2ShortCent K).map (MulAut.conj c).toMonoidHom = g2LongCent K := by
    ext x
    rw [mem_map_equiv, MulAut.conj_symm_apply]
    constructor
    · intro hx
      obtain ⟨hxC, hxv⟩ := mem_inf.1 hx
      refine mem_inf.2 ⟨?_, mem_centralizer_singleton_iff.2 ?_⟩
      · have := mul_mem (mul_mem hc hxC) (inv_mem hc)
        simpa [mul_assoc] using this
      · rw [← h]
        have h1 := mem_centralizer_singleton_iff.1 hxv
        calc x * (c * pinnedX .G2 K g2v 1 * c⁻¹) =
            c * (c⁻¹ * x * c * pinnedX .G2 K g2v 1) * c⁻¹ := by group
          _ = c * (pinnedX .G2 K g2v 1 * (c⁻¹ * x * c)) * c⁻¹ := by rw [h1]
          _ = c * pinnedX .G2 K g2v 1 * c⁻¹ * x := by group
    · intro hx
      obtain ⟨hxC, hxc⟩ := mem_inf.1 hx
      refine mem_inf.2 ⟨mul_mem (mul_mem (inv_mem hc) hxC) hc, mem_centralizer_singleton_iff.2 ?_⟩
      have h1 := mem_centralizer_singleton_iff.1 hxc
      rw [← h] at h1
      calc c⁻¹ * x * c * pinnedX .G2 K g2v 1 =
          c⁻¹ * (x * (c * pinnedX .G2 K g2v 1 * c⁻¹)) * c := by group
        _ = c⁻¹ * (c * pinnedX .G2 K g2v 1 * c⁻¹ * x) * c := by rw [h1]
        _ = pinnedX .G2 K g2v 1 * (c⁻¹ * x * c) := by group
  have hperfS : ⁅g2ShortCent K, g2ShortCent K⁆ = g2ShortCent K := by
    apply Subgroup.map_injective (f := (MulAut.conj c).toMonoidHom) (MulAut.conj c).injective
    rw [map_commutator, hmap, hperf]
  have hv : pinnedX .G2 K g2v 1 ∈ rootSubgroup .G2 K g2v ⊓ ⁅g2ShortCent K, g2ShortCent K⁆ := by
    refine mem_inf.2 ⟨mem_rootSubgroup.2 ⟨1, rfl⟩, ?_⟩
    rw [hperfS]
    exact mem_inf.2 ⟨pinnedX_mem_adjointGroup g2v 1, mem_centralizer_singleton_iff.2 rfl⟩
  rw [rootSubgroup_v_inf_commutator_eq_bot, mem_bot] at hv
  have h0 : pinnedX .G2 K g2v 1 = pinnedX .G2 K g2v 0 := by rw [hv, pinnedX_zero]
  exact one_ne_zero (pinnedX_injective .G2 K g2v h0)

omit [Finite K] in
theorem g2Conj_bc
    {y z : K} (h : y ≠ 0 ∨ z ≠ 0) :
    G2Conj (g2N 0 0 0 0 y z) (pinnedX .G2 K g2c 1) := by
  by_cases hy : y = 0
  · subst hy
    exact G2Conj.of_eq (pinnedX_c_eq_g2N z).symm (G2Conj.c_one (h.resolve_left (not_not.2 rfl)))
  · refine (G2Conj.pinnedX g2a (z / y) _).trans (G2Conj.of_eq (conj_a _ _ _ _ _ _ _) ?_)
    refine G2Conj.of_eq ((g2N_eq_g2N rfl rfl (by ring) (by ring) (by ring)
      (by field_simp; char2_ring)).trans (pinnedX_b_eq_g2N y).symm) (G2Conj.b_one hy)

theorem g2_conj_v_eq_of_mem_radical
    (h184 : G2Centr184) (hK4 : 4 ≤ Nat.card K)
    {c : ModGL .G2 K} (hc : c ∈ adjointGroup .G2 K) {s₀ : K} (hs₀ : s₀ ≠ 0)
    (h : c * pinnedX .G2 K g2v s₀ * c⁻¹ ∈ g2ShortRadical K) :
    ∃ α γ μ : K, μ ≠ 0 ∧
      ∀ s, c * pinnedX .G2 K g2v s * c⁻¹ = g2N 0 0 0 (μ * s) (α * (μ * s)) (γ * (μ * s)) := by
  obtain ⟨x, y, z, hxyz⟩ := h
  have hne : c * pinnedX .G2 K g2v s₀ * c⁻¹ ≠ 1 := by
    intro h1
    have h2 : pinnedX .G2 K g2v s₀ = pinnedX .G2 K g2v 0 := by
      rw [pinnedX_zero]
      calc pinnedX .G2 K g2v s₀ = c⁻¹ * (c * pinnedX .G2 K g2v s₀ * c⁻¹) * c := by group
        _ = 1 := by rw [h1]; group
    exact hs₀ (pinnedX_injective .G2 K g2v h2)
  by_cases hx : x = 0
  · exfalso
    subst hx
    have hyz : y ≠ 0 ∨ z ≠ 0 := by
      by_contra hn
      push Not at hn
      obtain ⟨rfl, rfl⟩ := hn
      exact hne (by rw [hxyz, g2N_zero])
    have h1 : G2Conj (pinnedX .G2 K g2v 1) (pinnedX .G2 K g2c 1) := by
      obtain ⟨d, hd, hd'⟩ := G2Conj.v_one hs₀
      refine (G2Conj.trans ⟨d⁻¹, inv_mem hd, ?_⟩ ⟨c, hc, hxyz⟩).trans (g2Conj_bc hyz)
      rw [← hd']
      group
    obtain ⟨d, hd, hd'⟩ := h1
    exact g2_conj_v_ne_c h184 hK4 hd hd'
  · set u : ModGL .G2 K := g2N (y / x) 0 (z / x) 0 0 0 with hu
    have huC : u ∈ adjointGroup .G2 K := by
      rw [hu, g2N]
      exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (pinnedX_mem_adjointGroup _ _)
        (pinnedX_mem_adjointGroup _ _)) (pinnedX_mem_adjointGroup _ _))
        (pinnedX_mem_adjointGroup _ _)) (pinnedX_mem_adjointGroup _ _))
        (pinnedX_mem_adjointGroup _ _)
    have huv : ∀ t, u * pinnedX .G2 K g2v t * u⁻¹ = g2N 0 0 0 t (y / x * t) (z / x * t) :=
      fun t => by rw [hu, g2N_conj_v]
    set d := torusElt .G2 K g2ir (Units.mk0 s₀ hs₀) with hd
    have hdv : ∀ t, d * pinnedX .G2 K g2v t * d⁻¹ = pinnedX .G2 K g2v (s₀ * t) := fun t => by
      rw [hd, torus_r_v, Units.val_mk0]
    have hdC : d ∈ adjointGroup .G2 K := torusElt_mem_adjointGroup _ _
    have hm1 : u⁻¹ * c * d * pinnedX .G2 K g2v 1 * (u⁻¹ * c * d)⁻¹ = pinnedX .G2 K g2v x := by
      have h1 := hdv 1
      rw [mul_one] at h1
      have h2 := huv x
      rw [div_mul_cancel₀ y hx, div_mul_cancel₀ z hx, ← hxyz] at h2
      calc u⁻¹ * c * d * pinnedX .G2 K g2v 1 * (u⁻¹ * c * d)⁻¹ =
          u⁻¹ * (c * (d * pinnedX .G2 K g2v 1 * d⁻¹) * c⁻¹) * u := by group
        _ = u⁻¹ * (u * pinnedX .G2 K g2v x * u⁻¹) * u := by rw [h1, h2]
        _ = pinnedX .G2 K g2v x := by group
    have hm := g2_conj_v_eq (mul_mem (mul_mem (inv_mem huC) hc) hdC) hx hm1
    refine ⟨y / x, z / x, x * s₀⁻¹, mul_ne_zero hx (inv_ne_zero hs₀), fun s => ?_⟩
    have h3 : d⁻¹ * pinnedX .G2 K g2v s * d = pinnedX .G2 K g2v (s₀⁻¹ * s) := by
      have h4 := hdv (s₀⁻¹ * s)
      rw [← mul_assoc, mul_inv_cancel₀ hs₀, one_mul] at h4
      rw [← h4]
      group
    calc c * pinnedX .G2 K g2v s * c⁻¹ =
        u * ((u⁻¹ * c * d) * (d⁻¹ * pinnedX .G2 K g2v s * d) * (u⁻¹ * c * d)⁻¹) * u⁻¹ := by
          group
      _ = u * pinnedX .G2 K g2v (x * s₀⁻¹ * s) * u⁻¹ := by
          rw [h3, hm, ← mul_assoc x s₀⁻¹ s, mul_assoc u]
      _ = _ := by rw [huv]

end ShortLong

end CFSG.ComponentClassification.RankTwoExceptional
