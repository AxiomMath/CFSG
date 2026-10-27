module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8YCfgAct
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG
open scoped commutatorElement

section Zsub

variable {Γ : Type*} [Group Γ]

@[expose] def Zsub (K : Subgroup Γ) : Subgroup Γ := (center ↥K).map K.subtype

theorem mem_Zsub {K : Subgroup Γ} {x : Γ} :
    x ∈ Zsub K ↔ ∃ h : x ∈ K, (⟨x, h⟩ : ↥K) ∈ center ↥K := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨h, hc⟩
    exact ⟨⟨x, h⟩, hc, rfl⟩

theorem Zsub_le (K : Subgroup Γ) : Zsub K ≤ K := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

theorem mul_comm_of_mem_Zsub {K : Subgroup Γ} {z : Γ} (hz : z ∈ Zsub K) {k : Γ} (hk : k ∈ K) :
    k * z = z * k := by
  obtain ⟨hzK, hc⟩ := mem_Zsub.mp hz
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨k, hk⟩)

theorem conj_mem_Zsub {K : Subgroup Γ} {z : Γ} (hz : z ∈ Zsub K) {n : Γ}
    (hn : n ∈ normalizer (K : Set Γ)) : n * z * n⁻¹ ∈ Zsub K := by
  obtain ⟨hzK, -⟩ := mem_Zsub.mp hz
  have hK : n * z * n⁻¹ ∈ K := (mem_normalizer_iff.mp hn z).mp hzK
  refine mem_Zsub.mpr ⟨hK, ?_⟩
  rw [Subgroup.mem_center_iff]
  intro k
  apply Subtype.ext
  show (k : Γ) * (n * z * n⁻¹) = n * z * n⁻¹ * (k : Γ)
  have hk' : n⁻¹ * (k : Γ) * n ∈ K := by
    have := (mem_normalizer_iff.mp ((normalizer (K : Set Γ)).inv_mem hn) (k : Γ)).mp k.2
    simpa using this
  have hc := mul_comm_of_mem_Zsub hz hk'
  calc (k : Γ) * (n * z * n⁻¹) = n * ((n⁻¹ * k * n) * z) * n⁻¹ := by group
    _ = n * (z * (n⁻¹ * k * n)) * n⁻¹ := by rw [hc]
    _ = n * z * n⁻¹ * k := by group

theorem mem_Zsub_of_comm {K D : Subgroup Γ} (hKD : ⁅K, D⁆ = ⊥) {x : Γ} (hxK : x ∈ K)
    (hxD : x ∈ D) : x ∈ Zsub K := by
  refine mem_Zsub.mpr ⟨hxK, ?_⟩
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  have h1 : ⁅(y : Γ), x⁆ ∈ (⊥ : Subgroup Γ) := hKD ▸ Subgroup.commutator_mem_commutator y.2 hxD
  exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp h1)

theorem mem_centralizer_of_comm_mem_Zsub {K : Subgroup Γ} [Group.IsPerfect ↥K] {a : Γ}
    (ha : a ∈ normalizer (K : Set Γ)) (h : ∀ k ∈ K, ⁅k, a⁆ ∈ Zsub K) :
    a ∈ centralizer (K : Set Γ) := by
  rw [← YCfg.yAct_eq_one_iff K ⟨a, ha⟩]
  ext x
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
  rw [YCfg.yAct_apply_mk, MulAut.one_apply]
  symm
  apply QuotientGroup.eq.mpr
  obtain ⟨hz, hc⟩ := mem_Zsub.mp (h (k : Γ)⁻¹ (K.inv_mem k.2))
  convert hc using 2
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def, inv_inv]
  group

theorem eq_of_prod_Zsub {K X : Subgroup Γ} (hK : IsQuasisimple ↥K) (hXK : X ≤ K)
    (hX : ∀ k ∈ K, ∃ x ∈ X, ∃ z ∈ Zsub K, k = x * z) : X = K := by
  have hnorm : (X.subgroupOf K).Normal := by
    refine ⟨fun n hn k => ?_⟩
    obtain ⟨x, hxX, z, hz, hkxz⟩ := hX k k.2
    have hn' : (n : Γ) ∈ X := hn
    have hxK : x ∈ K := hXK hxX
    have hzK : z ∈ K := Zsub_le K hz
    have hnK : (n : Γ) ∈ K := n.2
    have hzn : z * n = n * z := (mul_comm_of_mem_Zsub hz hnK).symm
    show (k : Γ) * n * (k : Γ)⁻¹ ∈ X
    have : (k : Γ) * n * (k : Γ)⁻¹ = x * n * x⁻¹ := by
      rw [hkxz]
      calc x * z * n * (x * z)⁻¹ = x * (z * n) * z⁻¹ * x⁻¹ := by group
        _ = x * (n * z) * z⁻¹ * x⁻¹ := by rw [hzn]
        _ = x * n * x⁻¹ := by group
    rw [this]
    exact X.mul_mem (X.mul_mem hxX hn') (X.inv_mem hxX)
  rcases LocalCores.quasisimple_normal_subgroups hK hnorm with htop | hcen
  · refine le_antisymm hXK fun k hk => ?_
    have : (⟨k, hk⟩ : ↥K) ∈ X.subgroupOf K := by rw [htop]; trivial
    exact this
  · exfalso
    have hall : ∀ k : ↥K, k ∈ center ↥K := by
      intro k
      obtain ⟨x, hxX, z, hz, hkxz⟩ := hX k k.2
      have hxc : (⟨x, hXK hxX⟩ : ↥K) ∈ center ↥K := hcen hxX
      have hzc : (⟨z, Zsub_le K hz⟩ : ↥K) ∈ center ↥K := (mem_Zsub.mp hz).2
      have : k = ⟨x, hXK hxX⟩ * ⟨z, Zsub_le K hz⟩ := Subtype.ext hkxz
      rw [this]
      exact (center ↥K).mul_mem hxc hzc
    have h1 : IsSimpleGroup (↥K ⧸ center ↥K) := hK.2.1
    obtain ⟨q, hq⟩ := exists_ne (1 : ↥K ⧸ center ↥K)
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    exact hq ((QuotientGroup.eq_one_iff k).mpr (hall k))

end Zsub

section Maps

variable {A M Γ₀ Q : Type*} [Group A] [Group M] [Group Γ₀] [Group Q]

theorem exists_hom_map (ν : A →* M) (L : Subgroup A) (ψ : ↥L →* Q)
    (hker : ∀ l : ↥L, ν l = 1 → ψ l = 1) :
    ∃ Φ : ↥(L.map ν) →* Q, ∀ l : ↥L, Φ ⟨ν l, Subgroup.mem_map_of_mem ν l.2⟩ = ψ l := by
  have hle : (ν.subgroupMap L).ker ≤ ψ.ker := by
    intro l hl
    rw [Subgroup.ker_subgroupMap, Subgroup.mem_subgroupOf] at hl
    exact hker l hl
  refine ⟨(ν.subgroupMap L).liftOfSurjective (ν.subgroupMap_surjective L) ⟨ψ, hle⟩,
    fun l => ?_⟩
  exact (ν.subgroupMap L).liftOfRightInverse_comp_apply _ _ ⟨ψ, hle⟩ l

theorem exists_W (Lb : Subgroup M) (Φ : ↥Lb →* Q) :
    ∃ W : Subgroup M, W ≤ Lb ∧ W.subgroupOf Lb = Φ.ker :=
  ⟨Φ.ker.map Lb.subtype, by rintro _ ⟨x, -, rfl⟩; exact x.2,
    Subgroup.comap_map_eq_self_of_injective Lb.subtype_injective _⟩

theorem mem_W_iff {Lb W : Subgroup M} {Φ : ↥Lb →* Q} (hW : W.subgroupOf Lb = Φ.ker) {x : M}
    (hx : x ∈ Lb) : x ∈ W ↔ Φ ⟨x, hx⟩ = 1 := by
  have : (⟨x, hx⟩ : ↥Lb) ∈ W.subgroupOf Lb ↔ (⟨x, hx⟩ : ↥Lb) ∈ Φ.ker := by rw [hW]
  rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker] at this
  exact this

theorem quot_equiv_of_eq {X : Type*} [Group X] (Φ : X →* Q) (hΦ : Function.Surjective Φ)
    (N : Subgroup X) [N.Normal] (hN : N = Φ.ker) : Nonempty ((X ⧸ N) ≃* Q) := by
  subst hN
  exact ⟨QuotientGroup.quotientKerEquivOfSurjective Φ hΦ⟩

theorem mem_normalizer_comap (π : A →* Γ₀) {K : Subgroup Γ₀} {a : A}
    (ha : π a ∈ normalizer (K : Set Γ₀)) : a ∈ normalizer ((K.comap π : Subgroup A) : Set A) := by
  rw [mem_normalizer_iff]
  intro x
  have := mem_normalizer_iff.mp ha (π x)
  simpa only [SetLike.mem_coe, Subgroup.mem_comap, map_mul, map_inv] using this

theorem mem_normalizer_map_br (f : A →* M) {N : Subgroup A} {a : A}
    (ha : a ∈ normalizer (N : Set A)) : f a ∈ normalizer ((N.map f : Subgroup M) : Set M) := by
  have hai : a⁻¹ ∈ normalizer (N : Set A) := (normalizer (N : Set A)).inv_mem ha
  rw [mem_normalizer_iff]
  intro w
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨a * n * a⁻¹, (mem_normalizer_iff.mp ha n).mp hn, by simp⟩
  · rintro ⟨n', hn', hw⟩
    refine ⟨a⁻¹ * n' * a, ?_, ?_⟩
    · have := (mem_normalizer_iff.mp hai n').mp hn'
      simpa using this
    · have : f (a⁻¹ * n' * a) = (f a)⁻¹ * (f a * w * (f a)⁻¹) * f a := by
        rw [← hw]; simp
      rw [this]
      group

theorem mem_normalizer_of_conj_mem {N : Subgroup M} {h : M} (h1 : ∀ x ∈ N, h * x * h⁻¹ ∈ N)
    (h2 : ∀ x ∈ N, h⁻¹ * x * h ∈ N) : h ∈ normalizer (N : Set M) := by
  rw [mem_normalizer_iff]
  intro x
  exact ⟨h1 x, fun hx => by simpa [mul_assoc] using h2 _ hx⟩

end Maps

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
