module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisB1
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisNV

public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open CFSG Subgroup SCert CFSG.ABGLocalTools

namespace SCert.SE

theorem act_of_v_zero (d : Fin 8) (i : Fin 3) (b : SE) (h0 : b.v0 = 0) (h1 : b.v1 = 0)
    (h2 : b.v2 = 0) : act d i b = 0 := by
  simp [act, h0, h1, h2]

@[expose] def K0sub : Subgroup SE where
  carrier := {s | s.v0 = 0 ∧ s.v1 = 0 ∧ s.v2 = 0}
  mul_mem' {a b} ha hb := by
    change (mul a b).v0 = 0 ∧ (mul a b).v1 = 0 ∧ (mul a b).v2 = 0
    simp only [mul, act_of_v_zero _ _ b hb.1 hb.2.1 hb.2.2, ha.1, ha.2.1, ha.2.2, add_zero,
      and_self]
  one_mem' := ⟨rfl, rfl, rfl⟩
  inv_mem' {a} ha := by
    change (inv a).v0 = 0 ∧ (inv a).v1 = 0 ∧ (inv a).v2 = 0
    simp only [inv, act_of_v_zero _ _ a ha.1 ha.2.1 ha.2.2, neg_zero, and_self]

theorem Qsub_inf_K0sub : Qsub ⊓ K0sub = ⊥ := by
  rw [eq_bot_iff]
  intro s hs
  obtain ⟨hd, h0, h1, h2⟩ := mem_inf.mp hs
  exact (mem_bot).mpr (SE.ext hd h0 h1 h2)

theorem Qsub_sup_K0sub : Qsub ⊔ K0sub = ⊤ := by
  rw [eq_top_iff]
  intro s _
  have h : s = (⟨0, s.v0, s.v1, s.v2⟩ : SE) * ⟨s.d, 0, 0, 0⟩ := by
    rw [mul_of_d_zero _ _ rfl]
    simp
  rw [h]
  exact mul_mem_sup (show (⟨0, s.v0, s.v1, s.v2⟩ : SE).d = 0 from rfl) ⟨rfl, rfl, rfl⟩

@[expose] def QsubEquiv : Qsub ≃* Multiplicative (ZMod 4 × ZMod 4 × ZMod 4) where
  toFun s := Multiplicative.ofAdd ((s : SE).v0, (s : SE).v1, (s : SE).v2)
  invFun p := ⟨⟨0, p.toAdd.1, p.toAdd.2.1, p.toAdd.2.2⟩, rfl⟩
  left_inv s := Subtype.ext (SE.ext s.2.symm rfl rfl rfl)
  right_inv _ := rfl
  map_mul' s t := by
    change Multiplicative.ofAdd (((s : SE) * t).v0, ((s : SE) * t).v1, ((s : SE) * t).v2) = _
    rw [mul_of_d_zero _ _ s.2]
    rfl

end SCert.SE

variable {G : Type} [Group G] [Finite G]

namespace GHSylow

variable (D : GHSylow G)

omit [Finite G] in
theorem nonempty_Q_equiv : Nonempty (D.Q ≃* Multiplicative (ZMod 4 × ZMod 4 × ZMod 4)) :=
  ⟨(SE.Qsub.equivMapOfInjective D.toG D.toG_injective).symm.trans SE.QsubEquiv⟩

omit [Finite G] in
theorem exists_complement_Q_S : ∃ K : Subgroup G, K ≤ (D.S : Subgroup G) ∧ D.Q ⊓ K = ⊥ ∧
    D.Q ⊔ K = D.S := by
  refine ⟨SE.K0sub.map D.toG, ?_, ?_, ?_⟩
  · rintro _ ⟨s, -, rfl⟩
    exact D.toG_mem s
  · rw [← map_inf_eq _ _ _ D.toG_injective, SE.Qsub_inf_K0sub, Subgroup.map_bot]
  · rw [← Subgroup.map_sup, SE.Qsub_sup_K0sub, ← MonoidHom.range_eq_map, D.range_toG]


theorem exists_GL32_B (hC : GorensteinHaradaThmCInput)
    (hidx : ∀ N : Subgroup G, N.Normal → N.index ≠ 2) (hxa : ¬ ∃ g : G, g⁻¹ * D.x * g = D.a)
    (hB : D.caseB) (hOG : pPrimeCore 2 G = ⊥) :
    ∃ θ : G →* GL (Fin 3) (ZMod 2), Function.Surjective θ ∧ θ.ker = D.Q := by
  have htop := D.normalizer_V_eq_top_B hC hidx hxa hB hOG
  obtain ⟨h10, h20⟩ := D.fusN_10_20 hC hidx hxa
  obtain ⟨θ, hθ, hker⟩ :=
    D.exists_GL32_normalizer_V hC (D.oddCore_M_eq_bot hC hidx hxa hOG) h10 h20
  let ι : G →* ↥(normalizer (D.V : Set G)) :=
    { toFun := fun g => ⟨g, htop ▸ mem_top g⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  refine ⟨θ.comp ι, fun y => ?_, ?_⟩
  · obtain ⟨n, rfl⟩ := hθ y
    exact ⟨n, rfl⟩
  · ext g
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hker, mem_subgroupOf]
    rfl

theorem conclusionA_B (hC : GorensteinHaradaThmCInput)
    (hidx : ∀ N : Subgroup G, N.Normal → N.index ≠ 2) (hxa : ¬ ∃ g : G, g⁻¹ * D.x * g = D.a)
    (hB : D.caseB) (hOG : pPrimeCore 2 G = ⊥) : ConclusionA G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨θ, hθ, hker⟩ := D.exists_GL32_B hC hidx hxa hB hOG
  have hQn : D.Q.Normal := hker ▸ θ.normal_ker
  have hQc : IsMulCommutative D.Q := ⟨⟨fun a b => Subtype.ext (D.Q_comm a.2 b.2)⟩⟩
  have hQp : IsPGroup 2 D.Q := D.S.isPGroup'.to_le D.Q_le_S
  obtain ⟨K, hKQ, hKsup⟩ := (CFSG.Quasithin.gaschutz (V := D.Q) hQp D.S).mpr
    (D.exists_complement_Q_S)
  have hdec : ∀ g : G, ∃ q ∈ D.Q, ∃ k ∈ K, q * k = g := fun g =>
    mem_sup_of_normal_left.mp (hKsup ▸ mem_top g)
  refine Or.inr ⟨D.Q, K, hQn, D.nonempty_Q_equiv, ?_, hKQ, hKsup, ?_⟩
  · refine ⟨MulEquiv.ofBijective (θ.comp K.subtype) ⟨fun k₁ k₂ h => ?_, fun y => ?_⟩⟩
    · have h' : (k₁ : G)⁻¹ * k₂ ∈ θ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv]
        exact inv_mul_eq_one.mpr h
      rw [hker] at h'
      have h'' : (k₁ : G)⁻¹ * k₂ ∈ D.Q ⊓ K := mem_inf.mpr ⟨h', mul_mem (inv_mem k₁.2) k₂.2⟩
      rw [hKQ, mem_bot, inv_mul_eq_one] at h''
      exact Subtype.ext h''
    · obtain ⟨g, rfl⟩ := hθ y
      obtain ⟨q, hq, k, hk, rfl⟩ := hdec g
      refine ⟨⟨k, hk⟩, ?_⟩
      have hq1 : θ q = 1 := by rw [← MonoidHom.mem_ker, hker]; exact hq
      change θ k = θ (q * k)
      rw [map_mul, hq1, one_mul]
  · by_contra hcon
    push Not at hcon
    obtain ⟨q, hq, k, hk, hqk⟩ := hdec (D.toG ⟨2, 0, 0, 0⟩)
    apply SE.t_not_central
    apply D.toG_injective
    rw [map_mul, map_mul, ← hqk]
    have htq : D.t ∈ D.Q := D.V_le_Q D.t_mem_V
    have h1 := hcon k hk D.t htq
    have h2 : q * D.t = D.t * q := D.Q_comm hq htq
    calc q * k * D.t = q * (k * D.t * k⁻¹) * k := by group
      _ = D.t * (q * k) := by rw [h1, h2, mul_assoc]

end GHSylow

end CFSG.ComponentClassification.GHarris
