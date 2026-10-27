module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915K4
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915K1
public import CFSG.Walter.Bender1970.S3.Involution
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915A1
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915C2

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement Pointwise

namespace L915

theorem k1_statement : K1Statement := by
  intro X _ p n hp hp2 hn hX ζ hζ2 hζ1 R hR hRζ hRn
  exact aut_pgroup_trivial_of_centralizes_involution hp hp2 hn hX hζ2 hζ1 hR hRζ hRn

section Tail

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S M : Subgroup G} {p : ℕ}
  {N A B : Subgroup G}

theorem PN_le_A1 (hC : Ctx9 G z k S M p) (hzN : z ∈ N) (hA₀ : Op p M ⊓ N ⊓ Cen z = ⊥) :
    Op p M ⊓ N ≤ A1 z M N p := by
  have : Fact p.Prime := ⟨hC.prime⟩
  have hz2 : z * z = 1 := by
    have h1 := pow_orderOf_eq_one z
    rw [hC.orderOf_z, pow_two] at h1
    exact h1
  have hodd : Odd (Nat.card ↥(Op p M ⊓ N)) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := p)).mp (hC.P_pgroup.to_le inf_le_left)
    rw [hn]
    exact (hC.prime.odd_of_ne_two hC.odd).pow
  intro x hx
  obtain ⟨c, hc, m, hm, hxcm⟩ := CFSG.Walter.exists_mem_centralizer_mul_mem_commutator hz2
    (z_mem_normalizer_PN hC hzN) hodd hx
  have hc1 : c = 1 := by
    have h1 : c ∈ Op p M ⊓ N ⊓ Cen z := ⟨hc.1, hc.2⟩
    rw [hA₀, Subgroup.mem_bot] at h1
    exact h1
  rw [hxcm, hc1, one_mul]
  exact hm

theorem A1_inf_pCore (hC : Ctx9 G z k S M p) {hzN : z ∈ N} (hA₀ : Op p M ⊓ N ⊓ Cen z = ⊥)
    {J : Subgroup ↥N} (hOJ : pCore p ↥N ≤ centralizer (J : Set ↥N))
    (hzJ : (⟨z, hzN⟩ : ↥N) ∈ J) :
    ∀ a ∈ (A1 z M N p).subgroupOf N, a ∈ pCore p ↥N → a = 1 := by
  intro a ha hO
  have haA : (a : G) ∈ A1 z M N p := Subgroup.mem_subgroupOf.mp ha
  have hP : (a : G) ∈ Op p M ⊓ N := A1_le hC hzN haA
  have hc : (a : G) ∈ Cen z := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := Subgroup.mem_centralizer_iff.mp (hOJ hO) _ hzJ
    exact (congrArg Subtype.val this).symm
  have h1 : (a : G) ∈ Op p M ⊓ N ⊓ Cen z := ⟨hP, hc⟩
  rw [hA₀, Subgroup.mem_bot] at h1
  exact Subtype.ext h1

theorem mk_injOn_A1 (hC : Ctx9 G z k S M p) {hzN : z ∈ N} (hA₀ : Op p M ⊓ N ⊓ Cen z = ⊥)
    {J : Subgroup ↥N} (hOJ : pCore p ↥N ≤ centralizer (J : Set ↥N))
    (hzJ : (⟨z, hzN⟩ : ↥N) ∈ J) :
    ∀ a ∈ (A1 z M N p).subgroupOf N, ∀ b ∈ (A1 z M N p).subgroupOf N,
      QuotientGroup.mk' (pCore p ↥N) a = QuotientGroup.mk' (pCore p ↥N) b → a = b := by
  intro a ha b hb hab
  have h1 : a⁻¹ * b ∈ pCore p ↥N := by
    have h0 : QuotientGroup.mk' (pCore p ↥N) (a⁻¹ * b) = 1 := by
      rw [map_mul, map_inv, hab]
      group
    exact (QuotientGroup.eq_one_iff _).mp h0
  have h2 : a⁻¹ * b = 1 := A1_inf_pCore hC hA₀ hOJ hzJ _ (mul_mem (inv_mem ha) hb) h1
  exact inv_mul_eq_one.mp h2

theorem A1_transitive (hC : Ctx9 G z k S M p) (h : Hyp95 z M p N A B) (hO2 : Op 2 N = ⊥)
    (hA₀ : Op p M ⊓ N ⊓ Cen z = ⊥) {J : Subgroup ↥N} (hJ : IsComponent J)
    (hOJ : pCore p ↥N ≤ centralizer (J : Set ↥N))
    (hJK : J.map (QuotientGroup.mk' (pCore p ↥N)) = ncl (xBar p N (A1 z M N p)))
    (hzJ : (⟨z, z_mem_N h⟩ : ↥N) ∈ J)
    (hcC : C43c (zSec z N (z_mem_N h) (pCore p ↥N)) p (xBar p N (A1 z M N p))) :
    ∀ x ∈ A1 z M N p, x ≠ 1 → ∀ y ∈ A1 z M N p, y ≠ 1 →
      ∃ j : ↥N, j ∈ J ∧ (j : G) ∈ Cen z ∧ (j : G) * x * (j : G)⁻¹ = y := by
  have hp := hC.prime
  have hp2 : p ≠ 2 := hC.odd
  have hzN : z ∈ N := z_mem_N h
  have hO2' : pCore 2 ↥N = ⊥ := by
    have := hO2
    rw [Op_eq_map, Subgroup.map_eq_bot_iff, Subgroup.ker_subtype] at this
    exact le_bot_iff.mp this
  have hz2 : z * z = 1 := by
    have h1 := pow_orderOf_eq_one z
    rw [hC.orderOf_z, pow_two] at h1
    exact h1
  have hA₁N : A1 z M N p ≤ N := (A1_le hC hzN).trans inf_le_right
  set Xb := xBar p N (A1 z M N p) with hXb
  set zb := zSec z N hzN (pCore p ↥N) with hzb
  set z' : ↥N := ⟨z, hzN⟩ with hz'
  have hz2' : z' * z' = 1 := Subtype.ext hz2
  have hinj : ∀ a ∈ (A1 z M N p).subgroupOf N, ∀ b ∈ (A1 z M N p).subgroupOf N,
      QuotientGroup.mk' (pCore p ↥N) a = QuotientGroup.mk' (pCore p ↥N) b → a = b := by
    intro a ha b hb hab
    have h1 : a⁻¹ * b ∈ pCore p ↥N := by
      have h0 : QuotientGroup.mk' (pCore p ↥N) (a⁻¹ * b) = 1 := by
        rw [map_mul, map_inv, hab]
        group
      exact (QuotientGroup.eq_one_iff _).mp h0
    have h2 : a⁻¹ * b = 1 :=
      A1_inf_pCore hC hA₀ hOJ hzJ _ (mul_mem (inv_mem ha) hb) h1
    exact inv_mul_eq_one.mp h2
  intro x hx hx1 y hy hy1
  have hxN := hA₁N hx
  have hyN := hA₁N hy
  have hx' : (⟨x, hxN⟩ : ↥N) ∈ (A1 z M N p).subgroupOf N := hx
  have hy' : (⟨y, hyN⟩ : ↥N) ∈ (A1 z M N p).subgroupOf N := hy
  have hπx : QuotientGroup.mk' (pCore p ↥N) ⟨x, hxN⟩ ∈ Xb := ⟨_, hx', rfl⟩
  have hπy : QuotientGroup.mk' (pCore p ↥N) ⟨y, hyN⟩ ∈ Xb := ⟨_, hy', rfl⟩
  have hπx1 : QuotientGroup.mk' (pCore p ↥N) ⟨x, hxN⟩ ≠ 1 := by
    intro h1
    have := A1_inf_pCore hC hA₀ hOJ hzJ _ hx' ((QuotientGroup.eq_one_iff _).mp h1)
    exact hx1 (congrArg Subtype.val this)
  have hπy1 : QuotientGroup.mk' (pCore p ↥N) ⟨y, hyN⟩ ≠ 1 := by
    intro h1
    have := A1_inf_pCore hC hA₀ hOJ hzJ _ hy' ((QuotientGroup.eq_one_iff _).mp h1)
    exact hy1 (congrArg Subtype.val this)
  obtain ⟨c, hc, hcxy⟩ := c43c_transitive hp hp2 hcC _ hπx hπx1 _ hπy hπy1
  have hcK : c ∈ J.map (QuotientGroup.mk' (pCore p ↥N)) := by
    rw [hJK]
    exact hc.1
  obtain ⟨j, hjJ, hjc⟩ := hcK
  have hcz : c * zb = zb * c := Subgroup.mem_centralizer_singleton_iff.mp hc.2
  have hjz : j * z' = z' * j := by
    set t : ↥N := z'⁻¹ * (j * z' * j⁻¹) with ht
    have hz'inv : z'⁻¹ = z' := inv_eq_of_mul_eq_one_right hz2'
    have htO : t ∈ pCore p ↥N := by
      have h0 : QuotientGroup.mk' (pCore p ↥N) t = 1 := by
        rw [ht, map_mul, map_inv, map_mul, map_mul, map_inv, hjc]
        have : QuotientGroup.mk' (pCore p ↥N) z' = zb := rfl
        rw [this]
        calc zb⁻¹ * (c * zb * c⁻¹) = zb⁻¹ * (zb * c * c⁻¹) := by rw [hcz]
          _ = 1 := by group
      exact (QuotientGroup.eq_one_iff _).mp h0
    have htJ : t ∈ J := by
      rw [ht]
      exact mul_mem (J.inv_mem hzJ) (mul_mem (mul_mem hjJ hzJ) (J.inv_mem hjJ))
    have htc : t ∈ centralizer (J : Set ↥N) := hOJ htO
    have htt : t * t = 1 := by
      have hu : (j * z' * j⁻¹) * (j * z' * j⁻¹) = 1 := by
        calc (j * z' * j⁻¹) * (j * z' * j⁻¹) = j * (z' * z') * j⁻¹ := by group
          _ = 1 := by rw [hz2']; group
      have hzt : z' * t = t * z' := (Subgroup.mem_centralizer_iff.mp htc z' hzJ)
      have hut : j * z' * j⁻¹ = z' * t := by
        rw [ht]
        group
      calc t * t = (z' * z') * (t * t) := by rw [hz2', one_mul]
        _ = z' * (z' * t) * t := by group
        _ = z' * (t * z') * t := by rw [hzt]
        _ = (z' * t) * (z' * t) := by group
        _ = 1 := by rw [← hut]; exact hu
    have ht1 : t = 1 := eq_one_of_central_involution hO2' hJ htJ htc htt
    have : j * z' * j⁻¹ = z' := by
      have h1 : z'⁻¹ * (j * z' * j⁻¹) = 1 := ht1
      rw [inv_mul_eq_one] at h1
      exact h1.symm
    calc j * z' = (j * z' * j⁻¹) * j := by group
      _ = z' * j := by rw [this]
  have hjzG : (j : G) ∈ Cen z := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val hjz
  have hjn : (j : G) ∈ normalizer ((A1 z M N p : Subgroup G) : Set G) := inv_A1 hC j.2 hjzG
  refine ⟨j, hjJ, hjzG, ?_⟩
  have hjxA : (j : G) * x * (j : G)⁻¹ ∈ A1 z M N p := (mem_normalizer_iff.mp hjn x).mp hx
  have hmem : j * (⟨x, hxN⟩ : ↥N) * j⁻¹ ∈ (A1 z M N p).subgroupOf N := hjxA
  have heq : QuotientGroup.mk' (pCore p ↥N) (j * (⟨x, hxN⟩ : ↥N) * j⁻¹) =
      QuotientGroup.mk' (pCore p ↥N) ⟨y, hyN⟩ := by
    rw [map_mul, map_mul, map_inv, hjc]
    exact hcxy
  have := hinj _ hmem _ hy' heq
  exact congrArg Subtype.val this

omit [Finite G] in
theorem mem_normalizer_normalizer {S : Subgroup G} {g : G} (hg : g ∈ normalizer (S : Set G)) :
    g ∈ normalizer ((normalizer (S : Set G) : Subgroup G) : Set G) := by
  have key : ∀ g ∈ normalizer (S : Set G), ∀ x ∈ normalizer (S : Set G),
      g * x * g⁻¹ ∈ normalizer (S : Set G) := by
    intro g hg x hx
    rw [mem_normalizer_iff] at hx ⊢
    intro s
    have e1 := mem_normalizer_iff.mp hg (g⁻¹ * s * g)
    have e2 := hx (g⁻¹ * s * g)
    have e3 := mem_normalizer_iff.mp hg (x * (g⁻¹ * s * g) * x⁻¹)
    have c1 : g * (g⁻¹ * s * g) * g⁻¹ = s := by group
    have c2 : g * (x * (g⁻¹ * s * g) * x⁻¹) * g⁻¹ = (g * x * g⁻¹) * s * (g * x * g⁻¹)⁻¹ := by
      group
    rw [c1] at e1
    rw [c2] at e3
    exact e1.symm.trans (e2.trans e3)
  rw [mem_normalizer_iff]
  intro x
  exact ⟨fun hx => key g hg x hx, fun hx => by
    have := key g⁻¹ ((normalizer (S : Set G)).inv_mem hg) _ hx
    simpa [mul_assoc] using this⟩


theorem P_eq_A1 (hC : Ctx9 G z k S M p) (h : Hyp95 z M p N A B) (hA₀ : Op p M ⊓ N ⊓ Cen z = ⊥)
    (htrans : ∀ x ∈ A1 z M N p, x ≠ 1 → ∀ y ∈ A1 z M N p, y ≠ 1 →
      ∃ j : ↥N, (j : G) ∈ Cen z ∧ (j : G) * x * (j : G)⁻¹ = y) :
    Op p M = A1 z M N p := by
  have hp := hC.prime
  have : Fact p.Prime := ⟨hp⟩
  have hzN : z ∈ N := z_mem_N h
  have hA₁P : A1 z M N p ≤ Op p M := (A1_le hC hzN).trans inf_le_left
  have hBN : B ≤ N := le_trans Subgroup.le_normalizer h.B_norm
  have hBA : B ≤ A1 z M N p := (le_inf h.B_le hBN).trans (PN_le_A1 hC hzN hA₀)
  set P₁ : Subgroup G := Op p M ⊓ normalizer ((A1 z M N p : Subgroup G) : Set G) with hP₁
  have hA₁P₁ : A1 z M N p ≤ P₁ := le_inf hA₁P Subgroup.le_normalizer
  have hP₁p : IsPGroup p ↥P₁ := hC.P_pgroup.to_le inf_le_left
  have hcent : A1 z M N p ≤ centralizer (P₁ : Set G) := by
    have hnil : Group.IsNilpotent ↥P₁ := hP₁p.isNilpotent
    have hnormA : (A1 z M N p).subgroupOf P₁ |>.Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hA₁P₁).mpr inf_le_right
    have hne : (A1 z M N p).subgroupOf P₁ ≠ ⊥ := by
      intro hb
      apply A1_ne_bot h
      rw [eq_bot_iff]
      intro a ha
      have : (⟨a, hA₁P₁ ha⟩ : ↥P₁) ∈ (A1 z M N p).subgroupOf P₁ := ha
      rw [hb, Subgroup.mem_bot] at this
      exact congrArg Subtype.val this
    have hZ := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
    obtain ⟨t', ht'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hZ
    have ht'A : (t' : P₁) ∈ (A1 z M N p).subgroupOf P₁ := t'.2.1
    have ht'Z : (t' : P₁) ∈ center ↥P₁ := t'.2.2
    have ht'1 : (t' : P₁) ≠ 1 := fun h1 => ht' (Subtype.ext h1)
    set t : G := ((t' : P₁) : G) with htdef
    have htA : t ∈ A1 z M N p := ht'A
    have ht1 : t ≠ 1 := fun h1 => ht'1 (Subtype.ext h1)
    have htC : t ∈ centralizer (P₁ : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have := Subgroup.mem_center_iff.mp ht'Z ⟨u, hu⟩
      simpa [Subgroup.coe_mul] using congrArg Subtype.val this
    intro x hx
    by_cases hx1 : x = 1
    · rw [hx1]; exact one_mem _
    obtain ⟨j, hjz, hjt⟩ := htrans t htA ht1 x hx hx1
    have hjM : (j : G) ∈ M := hC.cen_le hjz
    have hjA : (j : G) ∈ normalizer ((A1 z M N p : Subgroup G) : Set G) := inv_A1 hC j.2 hjz
    have hjP₁ : (j : G) ∈ normalizer ((P₁ : Subgroup G) : Set G) :=
      Thm1.mem_normalizer_inf (le_normalizer_Op' p M hjM) (mem_normalizer_normalizer hjA)
    rw [← hjt]
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hu' : (j : G)⁻¹ * u * (j : G) ∈ P₁ := by
      have := (mem_normalizer_iff.mp ((normalizer (P₁ : Set G)).inv_mem hjP₁)) u
      have h2 := this.mp hu
      simpa using h2
    have h3 := Subgroup.mem_centralizer_iff.mp htC _ hu'
    calc u * ((j : G) * t * (j : G)⁻¹) = (j : G) * (((j : G)⁻¹ * u * (j : G)) * t) * (j : G)⁻¹ := by
          group
      _ = (j : G) * (t * ((j : G)⁻¹ * u * (j : G))) * (j : G)⁻¹ := by rw [h3]
      _ = ((j : G) * t * (j : G)⁻¹) * u := by group
  have hP₁C : P₁ ≤ centralizer ((A1 z M N p : Subgroup G) : Set G) := Subgroup.le_centralizer_iff.mp hcent
  have hP₁N : P₁ ≤ N := fun x hx =>
    h.B_norm (Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le (fun b hb => hBA hb) (hP₁C hx)))
  have hle : Op p M ⊓ normalizer ((A1 z M N p : Subgroup G) : Set G) ≤ A1 z M N p := fun x hx =>
    PN_le_A1 hC hzN hA₀ ⟨hx.1, hP₁N hx⟩
  exact (eq_of_inf_normalizer_le hp hC.P_pgroup hA₁P hle).symm

theorem isElementaryAbelian_of_injective' {p : ℕ} {X Y : Type*} [Group X] [Group Y] (f : X →* Y)
    (hf : Function.Injective f) (h : CFSG.IsElementaryAbelian p Y) : CFSG.IsElementaryAbelian p X :=
  { is_comm := ⟨fun a b => hf (by rw [map_mul, map_mul]; exact h.1.1.1 (f a) (f b))⟩
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun g => hf (by
      rw [map_pow, map_one]
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.1 h.2 (f g)) }


end Tail

end L915

end CFSG.GH74.GLS.Stage2.Bender.Thm2
