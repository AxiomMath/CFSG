
module

public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneKillAction
public import Mathlib.GroupTheory.Nilpotent

@[expose] public section

namespace CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne

open Subgroup

theorem exists_mem_normalizer_not_mem_of_lt {G : Type*} [Group G] [Finite G] {H T : Subgroup G}
    (hT : IsPGroup 2 T) (hHT : H < T) : ∃ n ∈ T, n ∈ normalizer (H : Set G) ∧ n ∉ H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnil : Group.IsNilpotent T := hT.isNilpotent
  have hlt : H.subgroupOf T < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    apply (lt_iff_le_not_ge.1 hHT).2
    intro x hx
    have : (⟨x, hx⟩ : T) ∈ H.subgroupOf T := h ▸ mem_top _
    exact this
  obtain ⟨⟨n, hnT⟩, hn1, hn2⟩ := IsConcreteLE.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent _ hlt)
  have hconj : ∀ m : T, m ∈ normalizer ((H.subgroupOf T : Subgroup T) : Set T) →
      ∀ x ∈ H, (m : G) * x * (m : G)⁻¹ ∈ H := by
    intro m hm x hx
    have hxT : x ∈ T := hHT.le hx
    have := (mem_normalizer_iff.1 hm ⟨x, hxT⟩).1 hx
    exact this
  refine ⟨n, hnT, mem_normalizer_iff.2 fun x => ⟨hconj _ hn1 x, fun hx => ?_⟩, hn2⟩
  have h2 := hconj _ (inv_mem hn1) _ hx
  simpa [mul_assoc] using h2

theorem mem_normalizer_of_conj_le {G : Type*} [Group G] {J : Subgroup G} [Finite J] {g : G}
    (hg : ∀ x ∈ J, g * x * g⁻¹ ∈ J) : g ∈ normalizer (J : Set G) := by
  refine mem_normalizer_iff.2 fun x => ⟨hg x, fun hx => ?_⟩
  let f : J → J := fun y => ⟨g * y * g⁻¹, hg y y.2⟩
  have hf : Function.Injective f := fun y y' hyy' => Subtype.ext (by
    have := congrArg Subtype.val hyy'
    simpa [f] using this)
  obtain ⟨y, hy⟩ := (Finite.injective_iff_surjective.1 hf) ⟨_, hx⟩
  have : (y : G) = x := by
    have := congrArg Subtype.val hy
    simp only [f] at this
    have h2 := congrArg (fun t => g⁻¹ * t * g) this
    simpa [mul_assoc] using h2
  rw [← this]; exact y.2

namespace KillData

variable {G : Type*} [Group G] {u : Bool} {Jh E : Subgroup G} {cV cE : G → ℕ}
  {z l₁ l₂ : G} (h : KillData u Jh E cV cE z l₁ l₂)

@[expose] noncomputable def Kk : Subgroup G := (h.ρV.ker).map (normalizer (Jh : Set G)).subtype

include h

theorem mem_Kk {x : G} :
    x ∈ h.Kk ↔ x ∈ normalizer (Jh : Set G) ∧ ∀ j ∈ Jh, cV (x * j * x⁻¹) = cV j := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, fun j hj => ?_⟩
    show cV ((y : G) * j * (y : G)⁻¹) = cV j
    rw [h.cV_conj' y hj, MonoidHom.mem_ker.1 hy]
    rfl
  · rintro ⟨hx, hj⟩
    refine ⟨⟨x, hx⟩, MonoidHom.mem_ker.2 (Equiv.ext fun v => Fin.ext ?_), rfl⟩
    rw [h.ρV_apply]
    have := hj _ (h.liftV_mem v)
    rw [h.cV_liftV v.2] at this
    exact this

theorem Jh_le_Kk : Jh ≤ h.Kk := fun j hj => h.mem_Kk.2 ⟨Jh_le_X hj, fun _ hx => by
  rw [h.cV_mul _ (mul_mem hj hx) _ (inv_mem hj), h.cV_mul _ hj _ hx, h.cV_inv hj]
  simp [Nat.xor_comm]⟩

theorem card_le_of_le_Kk {P : Subgroup G} (hP : IsPGroup 2 P) (hPK : P ≤ h.Kk) :
    Nat.card P ≤ 2 ^ 15 :=
  h.ker P hP fun _ hx => h.mem_Kk.1 (hPK hx)

theorem isPGroup_Jh : IsPGroup 2 Jh := IsPGroup.of_card h.card_Jh

theorem isPGroup_zpowers_z : IsPGroup 2 (zpowers z) := by
  rintro ⟨g, hg⟩
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hg
  refine ⟨1, Subtype.ext ?_⟩
  simp only [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_two, h.z_sq, one_zpow]

theorem isPGroup_Jz : IsPGroup 2 (Jh ⊔ zpowers z : Subgroup G) :=
  h.isPGroup_Jh.to_sup_of_normal_left' h.isPGroup_zpowers_z (zpowers_le.2 h.z_norm)

theorem Jz_le_X : (Jh ⊔ zpowers z : Subgroup G) ≤ normalizer (Jh : Set G) :=
  sup_le Jh_le_X (zpowers_le.2 h.z_norm)

theorem exists_Ssyl [Finite G] : ∃ S : Sylow 2 (normalizer (Jh : Set G)),
    (Jh ⊔ zpowers z : Subgroup G).subgroupOf (normalizer (Jh : Set G)) ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (h.isPGroup_Jz.comap_of_injective _ (Subgroup.subtype_injective _)).exists_le_sylow

section S

variable [Finite G]

@[expose] noncomputable def Ssyl : Sylow 2 (normalizer (Jh : Set G)) :=
  Classical.choose h.exists_Ssyl

@[expose] noncomputable def SG : Subgroup G :=
  (h.Ssyl : Subgroup (normalizer (Jh : Set G))).map (normalizer (Jh : Set G)).subtype

theorem SG_le_X : h.SG ≤ normalizer (Jh : Set G) := map_subtype_le _

theorem Jz_le_SG : (Jh ⊔ zpowers z : Subgroup G) ≤ h.SG := by
  intro x hx
  have hxX := h.Jz_le_X hx
  exact ⟨⟨x, hxX⟩, Classical.choose_spec h.exists_Ssyl (Subgroup.mem_subgroupOf.2 hx), rfl⟩

theorem Jh_le_SG : Jh ≤ h.SG := le_sup_left.trans h.Jz_le_SG

theorem z_mem_SG : z ∈ h.SG := h.Jz_le_SG (mem_sup_right (mem_zpowers z))

theorem isPGroup_SG : IsPGroup 2 h.SG := (h.Ssyl.2).map _

theorem SG_max {Q : Subgroup G} (hQ : IsPGroup 2 Q) (hSQ : h.SG ≤ Q)
    (hQX : Q ≤ normalizer (Jh : Set G)) : Q = h.SG := by
  have hQ' : IsPGroup 2 (Q.subgroupOf (normalizer (Jh : Set G))) :=
    hQ.comap_of_injective _ (Subgroup.subtype_injective _)
  have hle : (h.Ssyl : Subgroup (normalizer (Jh : Set G))) ≤ Q.subgroupOf _ := fun x hx =>
    Subgroup.mem_subgroupOf.2 (hSQ ⟨x, hx, rfl⟩)
  have heq := h.Ssyl.3 hQ' hle
  apply le_antisymm _ hSQ
  intro x hx
  have : (⟨x, hQX hx⟩ : normalizer (Jh : Set G)) ∈ Q.subgroupOf _ := Subgroup.mem_subgroupOf.2 hx
  rw [heq] at this
  exact ⟨_, this, rfl⟩

theorem mem_Kk_iff_of_mem_SG {x : G} (hx : x ∈ h.SG) : x ∈ h.Kk ↔ x ∈ Jh := by
  refine ⟨fun hxK => ?_, fun hxJ => h.Jh_le_Kk hxJ⟩
  have hP : IsPGroup 2 (h.SG ⊓ h.Kk : Subgroup G) := h.isPGroup_SG.to_le inf_le_left
  have hJP : Jh ≤ h.SG ⊓ h.Kk := le_inf h.Jh_le_SG h.Jh_le_Kk
  have heq : Jh = h.SG ⊓ h.Kk :=
    Subgroup.eq_of_le_of_card_ge hJP (by rw [h.card_Jh]; exact h.card_le_of_le_Kk hP inf_le_right)
  rw [heq]
  exact ⟨hx, hxK⟩

end S

end KillData

end CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne
