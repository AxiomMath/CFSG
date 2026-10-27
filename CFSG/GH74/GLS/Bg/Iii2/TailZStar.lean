module

public import CFSG.GH74.GLS.Bg.Iii2.Basic

public section

namespace CFSG.GH74.GLS.Bg.Iii2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.ABGLocalTools CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement

variable {G : Type} [Group G]

structure QData (T K : Subgroup G) (z : G) : Prop where
  mem : z ∈ T ⊓ K
  sq : z * z = 1
  ne : z ≠ 1
  central : ∀ g ∈ T ⊓ K, g * z = z * g
  unique : ∀ g ∈ T ⊓ K, g * g = 1 → g = 1 ∨ g = z

theorem exists_qdata {T K : Subgroup G} (hq : ∃ n, IVK.IsQuaternionTwoGroup ↥(T ⊓ K) n) :
    ∃ z : G, QData T K z := by
  obtain ⟨z, ψ, hzP, hzz, hz1, hzc, hzu, -⟩ := quat_data hq
  exact ⟨z, hzP, hzz, hz1, hzc, hzu⟩

variable [Finite G]

theorem zStar_comm {x : G} {K T : Subgroup G} (hK : IsRigidRankOneComp x K) (hT : IsPGroup 2 T)
    {c : G} (hcT : c ∈ T) (hc : c ∈ zStar (rigidProduct x)) {p : G} (hp : p ∈ T ⊓ K) :
    p * c = c * p := by
  have hKle : K ≤ rigidProduct x := le_sSup hK
  obtain ⟨-, -, -, h⟩ := hc
  have h1 : ⁅p, c⁆ ∈ pPrimeCoreOf 2 (rigidProduct x) := h p (hKle hp.2)
  have h2 : ⁅p, c⁆ ∈ T :=
    T.mul_mem (T.mul_mem (T.mul_mem hp.1 hcT) (T.inv_mem hp.1)) (T.inv_mem hcT)
  have h3 : ⁅p, c⁆ ∈ T ⊓ pPrimeCoreOf 2 (rigidProduct x) := ⟨h2, h1⟩
  rw [inf_pPrimeCoreOf_eq_bot hT, Subgroup.mem_bot] at h3
  exact commutatorElement_eq_one_iff_mul_comm.1 h3

omit [Finite G] in
theorem rigidProduct_eq_of_single {x : G} {K : Subgroup G}
    (hsingle : ∀ K', IsRigidRankOneComp x K' → K' = K) (hK : IsRigidRankOneComp x K) :
    rigidProduct x = K := by
  have : {K' : Subgroup G | IsRigidRankOneComp x K'} = {K} := by
    ext K'
    exact ⟨fun h => hsingle K' h, fun h => by rw [Set.mem_singleton_iff] at h; rw [h]; exact hK⟩
  unfold rigidProduct
  rw [this, sSup_singleton]

theorem zStar_single (hquat : II4_4_quat) (hG : IsKProperSimple G) {x : G} {K T : Subgroup G}
    (hK : IsRigidRankOneComp x K) (hT : IsSylowOf 2 T (centralizer ({x} : Set G)))
    (hsingle : ∀ K', IsRigidRankOneComp x K' → K' = K) :
    ∃ z : G, QData T K z ∧ ∀ c ∈ T ⊓ zStar (rigidProduct x), c = 1 ∨ c = z := by
  have hq : ∃ n, IVK.IsQuaternionTwoGroup ↥(T ⊓ K) n :=
    hquat G hG x (rr_ord hK) T K hT (rr_pcomp hK) hK.2
  obtain ⟨z, ψ, hzP, hzz, hz1, hzc, hzu, -⟩ := quat_data hq
  refine ⟨z, ⟨hzP, hzz, hz1, hzc, hzu⟩, fun c hc => ?_⟩
  have hcK : c ∈ K := by
    have := (Subgroup.mem_inf.1 hc.2).1
    rwa [rigidProduct_eq_of_single hsingle hK] at this
  have hcP : c ∈ T ⊓ K := ⟨hc.1, hcK⟩
  have hcc : ∀ h ∈ T ⊓ K, c * h = h * c := fun h hh =>
    (zStar_comm hK hT.isPGroup hc.1 hc.2 hh).symm
  exact hzu c hcP (quat_data_center hq c hcP hcc)

open CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices (quaternion_center) in
theorem zStar_two (hquat : II4_4_quat) (hG : IsKProperSimple G) (hgen : Gen4 G) {x : G}
    {K₁ K₂ T : Subgroup G} (h₁ : IsRigidRankOneComp x K₁) (h₂ : IsRigidRankOneComp x K₂)
    (hne : K₁ ≠ K₂) (hT : IsSylowOf 2 T (centralizer ({x} : Set G))) :
    ∃ z₁ z₂ : G, QData T K₁ z₁ ∧ QData T K₂ z₂ ∧
      ∀ c ∈ T ⊓ zStar (rigidProduct x), c = 1 ∨ c = z₁ ∨ c = z₂ ∨ c = z₁ * z₂ := by
  have hq₁ : ∃ n, IVK.IsQuaternionTwoGroup ↥(T ⊓ K₁) n :=
    hquat G hG x (rr_ord h₁) T K₁ hT (rr_pcomp h₁) h₁.2
  have hq₂ : ∃ n, IVK.IsQuaternionTwoGroup ↥(T ⊓ K₂) n :=
    hquat G hG x (rr_ord h₂) T K₂ hT (rr_pcomp h₂) h₂.2
  obtain ⟨z₁, ψ₁, hz₁P, hz₁z, hz₁1, hz₁c, hz₁u, hi₁, hr₁, hψ₁, -⟩ := quat_data hq₁
  obtain ⟨z₂, ψ₂, hz₂P, hz₂z, hz₂1, hz₂c, hz₂u, hi₂, hr₂, hψ₂, -⟩ := quat_data hq₂
  refine ⟨z₁, z₂, ⟨hz₁P, hz₁z, hz₁1, hz₁c, hz₁u⟩, ⟨hz₂P, hz₂z, hz₂1, hz₂c, hz₂u⟩, ?_⟩
  have hc12 : ∀ a b, ψ₁ a * ψ₂ b = ψ₂ b * ψ₁ a := fun a b =>
    rr_sylow_comm h₁ h₂ hne hT _ (hr₁ a) _ (hr₂ b)
  let φ : QuaternionGroup 2 × QuaternionGroup 2 →* G :=
    ψ₁.noncommCoprod ψ₂ fun a b => hc12 a b
  have hφ : ∀ g, φ g = ψ₁ g.1 * ψ₂ g.2 := fun g => rfl
  have hker : ∀ g, φ g = 1 → g = 1 ∨ g = (QuaternionGroup.a 2, QuaternionGroup.a 2) :=
    fun g hg => q8_pair_ker hi₁ hi₂ hc12 g (by rw [← hφ]; exact hg)
  have hZ : IsPGroup 2 ↥(T ⊓ zStar (rigidProduct x)) := (hT.isPGroup).to_inf_left
  have hcomm : ∀ (a : QuaternionGroup 2 × QuaternionGroup 2) (t : G),
      t ∈ T ⊓ zStar (rigidProduct x) → φ a * t = t * φ a := by
    intro a t ht
    have c1 : ψ₁ a.1 * t = t * ψ₁ a.1 := zStar_comm h₁ hT.isPGroup ht.1 ht.2 (hr₁ a.1)
    have c2 : ψ₂ a.2 * t = t * ψ₂ a.2 := zStar_comm h₂ hT.isPGroup ht.1 ht.2 (hr₂ a.2)
    rw [hφ]
    calc ψ₁ a.1 * ψ₂ a.2 * t = ψ₁ a.1 * (ψ₂ a.2 * t) := mul_assoc _ _ _
      _ = ψ₁ a.1 * (t * ψ₂ a.2) := by rw [c2]
      _ = ψ₁ a.1 * t * ψ₂ a.2 := (mul_assoc _ _ _).symm
      _ = t * ψ₁ a.1 * ψ₂ a.2 := by rw [c1]
      _ = t * (ψ₁ a.1 * ψ₂ a.2) := mul_assoc _ _ _
  have key := CFSG.GH74.Generic.q8q8_commuting_two_subgroup_le' hgen φ hker
    (T ⊓ zStar (rigidProduct x)) hZ hcomm
  intro c hc
  obtain ⟨g, hg, hgc⟩ := key c hc
  have e1 : g.1 = 1 ∨ g.1 = QuaternionGroup.a 2 := quaternion_center g.1 (fun y => by
    have := congrArg Prod.fst (hgc (y, 1))
    simpa using this)
  have e2 : g.2 = 1 ∨ g.2 = QuaternionGroup.a 2 := quaternion_center g.2 (fun y => by
    have := congrArg Prod.snd (hgc (1, y))
    simpa using this)
  rw [← hg, hφ]
  rcases e1 with e1 | e1 <;> rcases e2 with e2 | e2
  · left; rw [e1, e2, map_one, map_one, mul_one]
  · right; right; left; rw [e1, e2, map_one, one_mul, hψ₂]
  · right; left; rw [e1, e2, map_one, mul_one, hψ₁]
  · right; right; right; rw [e1, e2, hψ₁, hψ₂]

end CFSG.GH74.GLS.Bg.Iii2
