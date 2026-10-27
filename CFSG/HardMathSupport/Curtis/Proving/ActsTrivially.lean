module

public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks

public section

namespace CFSG.HardMathSupport.Curtis.Proving

open CFSG.QuasithinUnique CFSG.Open
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem conj_mem_of_mem_normalizer {L : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) {x : G} (hx : x ∈ L) : g * x * g⁻¹ ∈ L :=
  (hg x).1 hx

theorem conj_inv_mem_of_mem_normalizer {L : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) {x : G} (hx : x ∈ L) : g⁻¹ * x * g ∈ L := by
  have h := (Subgroup.inv_mem _ hg) x
  rw [inv_inv] at h
  exact h.1 hx

def conjNormEquiv {L : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G)) :
    L ≃* L where
  toFun x := ⟨g * x * g⁻¹, conj_mem_of_mem_normalizer hg x.2⟩
  invFun x := ⟨g⁻¹ * x * g, conj_inv_mem_of_mem_normalizer hg x.2⟩
  left_inv x := by ext; simp [mul_assoc]
  right_inv x := by ext; simp [mul_assoc]
  map_mul' x y := by ext; simp [mul_assoc]

theorem blockQ_conj_mem_normalizer {L : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) {q : G} (hq : q ∈ blockQ L) :
    g * q * g⁻¹ ∈ blockQ L := by
  unfold blockQ pCoreOf at hq ⊢
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hq
  have hmem : conjNormEquiv hg y ∈ (CFSG.pCore 2 L).map (conjNormEquiv hg).toMonoidHom :=
    Subgroup.mem_map_of_mem _ hy
  rw [pCore_map_iso 2 (conjNormEquiv hg)] at hmem
  exact Subgroup.mem_map.mpr ⟨conjNormEquiv hg y, hmem, rfl⟩

theorem blockU_conj_mem_normalizer {L : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) {u : G} (hu : u ∈ blockU L) :
    g * u * g⁻¹ ∈ blockU L := by
  have key : ⁅blockQ L, L⁆ ≤ (⁅blockQ L, L⁆).comap (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.commutator_le]
    intro q hq x hx
    rw [Subgroup.mem_comap]
    have e : (MulAut.conj g).toMonoidHom ⁅q, x⁆ = ⁅g * q * g⁻¹, g * x * g⁻¹⁆ := by
      simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom, commutatorElement_def]
      group
    rw [e]
    exact Subgroup.commutator_mem_commutator (blockQ_conj_mem_normalizer hg hq)
      (conj_mem_of_mem_normalizer hg hx)
  have h := key hu
  rw [Subgroup.mem_comap] at h
  change g * u * g⁻¹ ∈ ⁅blockQ L, L⁆
  simpa [MulAut.conj_apply] using h

theorem blockZ_conj_mem_normalizer {L : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) {z : G} (hz : z ∈ blockZ L) :
    g * z * g⁻¹ ∈ blockZ L := by
  obtain ⟨hzU, hzC⟩ := Subgroup.mem_inf.1 hz
  refine Subgroup.mem_inf.2 ⟨blockU_conj_mem_normalizer hg hzU, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have hc := Subgroup.mem_centralizer_iff.1 hzC _ (conj_inv_mem_of_mem_normalizer hg hh)
  calc h * (g * z * g⁻¹) = g * ((g⁻¹ * h * g) * z) * g⁻¹ := by group
    _ = g * (z * (g⁻¹ * h * g)) * g⁻¹ := by rw [hc]
    _ = g * z * g⁻¹ * h := by group

@[expose] def ActsTriv (L : Subgroup G) (g : G) : Prop :=
  g ∈ Subgroup.normalizer (L : Set G) ∧ ∀ u ∈ blockU L, g * u * g⁻¹ * u⁻¹ ∈ blockZ L

def actsTrivSubgroup (L : Subgroup G) : Subgroup G where
  carrier := {g | ActsTriv L g}
  one_mem' := ⟨Subgroup.one_mem _, fun u _ => by simp⟩
  mul_mem' {g h} hg hh := by
    refine ⟨Subgroup.mul_mem _ hg.1 hh.1, fun u hu => ?_⟩
    have e : g * h * u * (g * h)⁻¹ * u⁻¹ = g * (h * u * h⁻¹ * u⁻¹) * g⁻¹ * (g * u * g⁻¹ * u⁻¹) := by
      group
    rw [e]
    exact Subgroup.mul_mem _ (blockZ_conj_mem_normalizer hg.1 (hh.2 u hu)) (hg.2 u hu)
  inv_mem' {g} hg := by
    refine ⟨Subgroup.inv_mem _ hg.1, fun u hu => ?_⟩
    have hv : g⁻¹ * u * g ∈ blockU L := by
      have h := blockU_conj_mem_normalizer (Subgroup.inv_mem _ hg.1) hu
      rwa [inv_inv] at h
    have h1 := hg.2 _ hv
    have e3 : g * (g⁻¹ * u * g) * g⁻¹ = u := by group
    rw [e3] at h1
    have h2 := (blockZ L).inv_mem h1
    have e2 : g⁻¹ * u * g⁻¹⁻¹ * u⁻¹ = ((u * (g⁻¹ * u * g)⁻¹)⁻¹) := by group
    rw [e2]
    exact h2

theorem mem_actsTrivSubgroup_iff {L : Subgroup G} {g : G} :
    g ∈ actsTrivSubgroup L ↔ ActsTriv L g := Iff.rfl

theorem actsTriv_conj {L : Subgroup G} {g n : G} (hg : g ∈ Subgroup.normalizer (L : Set G))
    (hn : ActsTriv L n) : ActsTriv L (g * n * g⁻¹) := by
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hn.1) (Subgroup.inv_mem _ hg), fun u hu => ?_⟩
  have hv : g⁻¹ * u * g ∈ blockU L := by
    have h := blockU_conj_mem_normalizer (Subgroup.inv_mem _ hg) hu
    rwa [inv_inv] at h
  have hz := blockZ_conj_mem_normalizer hg (hn.2 _ hv)
  have e : g * n * g⁻¹ * u * (g * n * g⁻¹)⁻¹ * u⁻¹ =
      g * (n * (g⁻¹ * u * g) * n⁻¹ * (g⁻¹ * u * g)⁻¹) * g⁻¹ := by
    group
  rw [e]
  exact hz

instance actsTrivSubgroup_normal_subgroupOf (L : Subgroup G) :
    ((actsTrivSubgroup L).subgroupOf (Subgroup.normalizer (L : Set G))).Normal :=
  ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact actsTriv_conj g.2 hn⟩

theorem actsTriv_of_parity {L : Subgroup G} {c t o : G} {r k : ℕ}
    (hc : ActsTriv L c) (hn : t ∈ Subgroup.normalizer (L : Set G)) (hto : t = c * o)
    (hr : Odd r) (htr : t ^ r = 1) (hok : o ^ (2 ^ k) = 1) : ActsTriv L t := by
  let T' := (actsTrivSubgroup L).subgroupOf (Subgroup.normalizer (L : Set G))
  have ho : o ∈ Subgroup.normalizer (L : Set G) := by
    have : o = c⁻¹ * t := by rw [hto]; group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hc.1) hn
  let cN : Subgroup.normalizer (L : Set G) := ⟨c, hc.1⟩
  let tN : Subgroup.normalizer (L : Set G) := ⟨t, hn⟩
  let oN : Subgroup.normalizer (L : Set G) := ⟨o, ho⟩
  have htc : tN = cN * oN := Subtype.ext hto
  have hcT : cN ∈ T' := Subgroup.mem_subgroupOf.2 hc
  have hπc : (QuotientGroup.mk' T' cN : _ ⧸ T') = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hcT
  have hπt : (QuotientGroup.mk' T' tN) ^ r = 1 := by
    rw [← map_pow]
    have : tN ^ r = 1 := by ext; simp [tN, htr]
    rw [this, map_one]
  have hπo : (QuotientGroup.mk' T' oN) ^ (2 ^ k) = 1 := by
    rw [← map_pow]
    have : oN ^ (2 ^ k) = 1 := by ext; simp [oN, hok]
    rw [this, map_one]
  have hte : QuotientGroup.mk' T' tN = QuotientGroup.mk' T' oN := by
    rw [htc, map_mul, hπc, one_mul]
  have hr1 : (QuotientGroup.mk' T' oN) ^ r = 1 := by rw [← hte]; exact hπt
  have hcop : Nat.gcd (2 ^ k) r = 1 :=
    Nat.Coprime.gcd_eq_one ((Nat.coprime_two_left.2 hr).pow_left k)
  have hgcd := pow_gcd_eq_one.2 ⟨hπo, hr1⟩
  rw [hcop, pow_one] at hgcd
  have hoT : oN ∈ T' := (QuotientGroup.eq_one_iff oN).1 hgcd
  have hoT' : o ∈ actsTrivSubgroup L := Subgroup.mem_subgroupOf.1 hoT
  have htT : t ∈ actsTrivSubgroup L := by
    rw [hto]
    exact Subgroup.mul_mem _ hc hoT'
  exact htT

theorem commutator_blockU_zpowers_le {L : Subgroup G} {t : G} (ht : ActsTriv L t) :
    ⁅blockU L, Subgroup.zpowers t⁆ ≤ blockZ L := by
  have hT : Subgroup.zpowers t ≤ actsTrivSubgroup L := Subgroup.zpowers_le.2 ht
  rw [Subgroup.commutator_le]
  intro u hu x hx
  have hxT : ActsTriv L x := hT hx
  have h := hxT.2 u hu
  have e : ⁅u, x⁆ = (x * u * x⁻¹ * u⁻¹)⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact (blockZ L).inv_mem h

end CFSG.HardMathSupport.Curtis.Proving

end
