module

public import CFSG.LocalAnalysis.EvenBN.U5.CaseBParts

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient
open scoped MatrixGroups

section Generic

variable {G : Type*} [Group G]

theorem sec52_comm_mem_conj {X : Subgroup G} {g x : G} (hg : g * g = 1) :
    x ∈ X.map (MulAut.conj g).toMonoidHom ↔ g * x * g ∈ X := by
  rw [mem_map_equiv, MulAut.conj_symm_apply, inv_eq_of_mul_eq_one_right hg]

theorem sec52_comm_key {r s : G} (hr : r * r = 1) (hs : s * s = 1) (hrs : (r * s) ^ 4 = 1) :
    r * s * r * s * r = s * r * s := by
  have h4 : r * s * r * s * r * s * r * s = 1 := by
    have h := hrs
    simp only [pow_succ, pow_zero, one_mul, mul_assoc] at h ⊢
    exact h
  have h5 : (s * r * s) * (s * r * s) = 1 := by
    calc (s * r * s) * (s * r * s) = s * r * (s * s) * r * s := by group
      _ = s * (r * r) * s := by rw [hs, mul_one]; group
      _ = 1 := by rw [hr, mul_one, hs]
  refine mul_right_cancel (b := s * r * s) ?_
  rw [h5]
  calc r * s * r * s * r * (s * r * s) = r * s * r * s * r * s * r * s := by group
    _ = 1 := h4

theorem sec52_comm_aux {K V : Subgroup G} {r s t : G}
    (hr : r * r = 1) (hs : s * s = 1) (ht : t * t = 1) (hst : s * t = t * s)
    (hrt : r * t = t * r) (hrs : (r * s) ^ 4 = 1)
    (hKt : K.map (MulAut.conj t).toMonoidHom ≤ centralizer (K : Set G))
    (hVK : V ≤ K) (hVs : V.map (MulAut.conj s).toMonoidHom = V)
    (hrK : K.map (MulAut.conj r).toMonoidHom ≤ K)
    (hK : K = V ⊔ (V ⊓ V.map (MulAut.conj r).toMonoidHom).map
      (MulAut.conj (r * s)).toMonoidHom) :
    K.map (MulAut.conj (s * t)).toMonoidHom ≤ centralizer (K : Set G) := by
  have hr' : r⁻¹ = r := inv_eq_of_mul_eq_one_right hr
  have hs' : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hI1 := sec52_comm_key hr hs hrs
  set Z : Subgroup G := (V ⊓ V.map (MulAut.conj r).toMonoidHom).map
    (MulAut.conj (r * s)).toMonoidHom with hZ
  have hZK : Z ≤ K := by rw [hK]; exact le_sup_right
  have hVs' : ∀ v ∈ V, s * v * s ∈ V := fun v hv =>
    (sec52_comm_mem_conj hs).1 (by rw [hVs]; exact hv)
  have hcomm : ∀ y ∈ K, ∀ w ∈ K, w * (t * y * t) = (t * y * t) * w := fun y hy w hw =>
    mem_centralizer_iff.1 (hKt ((sec52_comm_mem_conj ht).2 (by
      rw [show t * (t * y * t) * t = y by
        calc t * (t * y * t) * t = (t * t) * y * (t * t) := by group
          _ = y := by rw [ht, one_mul, mul_one]]
      exact hy))) w hw
  have hst_inv : (s * t)⁻¹ = t * s := by rw [mul_inv_rev, ht', hs']
  have hα : ∀ x : G, (MulAut.conj (s * t)).toMonoidHom x = (s * t) * x * (t * s) := fun x => by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hst_inv]
  have hVα : V.map (MulAut.conj (s * t)).toMonoidHom ≤ K.map (MulAut.conj t).toMonoidHom := by
    rintro _ ⟨v, hv, rfl⟩
    rw [hα, sec52_comm_mem_conj ht]
    have h1 : t * (s * t) = s := by rw [hst, ← mul_assoc, ht, one_mul]
    have h2 : (t * s) * t = s := by rw [← hst, mul_assoc, ht, mul_one]
    have e : t * ((s * t) * v * (t * s)) * t = s * v * s := by
      calc t * ((s * t) * v * (t * s)) * t = (t * (s * t)) * v * ((t * s) * t) := by group
        _ = s * v * s := by rw [h1, h2]
    rw [e]
    exact hVK (hVs' v hv)
  have hG1 : V.map (MulAut.conj (s * t)).toMonoidHom ≤ centralizer (V : Set G) :=
    hVα.trans (hKt.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hVK)))
  have hG2 : V.map (MulAut.conj (s * t)).toMonoidHom ≤ centralizer (Z : Set G) :=
    hVα.trans (hKt.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hZK)))
  have hG3 : Z.map (MulAut.conj (s * t)).toMonoidHom ≤ centralizer (V : Set G) := by
    rintro _ ⟨z, hz, rfl⟩
    rw [mem_centralizer_iff]
    intro v hv
    rw [hα]
    have hc := hcomm z (hZK hz) (s * v * s) (hVK (hVs' v hv))
    calc v * ((s * t) * z * (t * s)) = (s * s) * v * ((s * t) * z * (t * s)) := by
          rw [hs, one_mul]
      _ = s * ((s * v * s) * (t * z * t)) * s := by group
      _ = s * ((t * z * t) * (s * v * s)) * s := by rw [hc]
      _ = ((s * t) * z * (t * s)) * v * (s * s) := by group
      _ = ((s * t) * z * (t * s)) * v := by rw [hs, mul_one]
  have hG4 : Z.map (MulAut.conj (s * t)).toMonoidHom ≤ centralizer (Z : Set G) := by
    have hρ : (r * s * r)⁻¹ = r * s * r := by simp only [mul_inv_rev, hr', hs', mul_assoc]
    have hrst : (r * s) * t = t * (r * s) := by
      rw [mul_assoc, hst, ← mul_assoc, hrt, mul_assoc]
    have hA : (s * t) * (r * s) = (r * s) * (t * (r * s * r)) := by
      calc (s * t) * (r * s) = (t * s) * (r * s) := by rw [hst]
        _ = t * (s * r * s) := by group
        _ = t * (r * s * r * s * r) := by rw [hI1]
        _ = (t * (r * s)) * (r * s * r) := by group
        _ = ((r * s) * t) * (r * s * r) := by rw [hrst]
        _ = (r * s) * (t * (r * s * r)) := by group
    have hconj : ∀ a : G, MulAut.conj (s * t) (MulAut.conj (r * s) a) =
        MulAut.conj (r * s) (MulAut.conj (t * (r * s * r)) a) := fun a => by
      rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← map_mul, ← map_mul, hA]
    rintro _ ⟨z₂, hz₂, rfl⟩
    rw [mem_centralizer_iff]
    intro z₁ hz₁
    obtain ⟨a₂, ha₂, rfl⟩ := hz₂
    obtain ⟨a₁, ha₁, rfl⟩ := hz₁
    simp only [MulEquiv.coe_toMonoidHom]
    rw [hconj a₂, ← map_mul, ← map_mul]
    refine congrArg (MulAut.conj (r * s)) ?_
    have hy : (r * s * r) * a₂ * (r * s * r) ∈ K := by
      have hb : r * a₂ * r ∈ V := (sec52_comm_mem_conj hr).1 ha₂.2
      have hb' : s * (r * a₂ * r) * s ∈ V := hVs' _ hb
      have hb'' : r * (s * (r * a₂ * r) * s) * r ∈ V.map (MulAut.conj r).toMonoidHom :=
        (sec52_comm_mem_conj hr).2 (by
          rw [show r * (r * (s * (r * a₂ * r) * s) * r) * r = s * (r * a₂ * r) * s by
            calc r * (r * (s * (r * a₂ * r) * s) * r) * r
                = (r * r) * (s * (r * a₂ * r) * s) * (r * r) := by group
              _ = _ := by rw [hr, one_mul, mul_one]]
          exact hb')
      have h3 := (Subgroup.map_mono hVK).trans hrK hb''
      rwa [show r * (s * (r * a₂ * r) * s) * r = (r * s * r) * a₂ * (r * s * r) by group] at h3
    have hcy := hcomm _ hy a₁ (hVK ha₁.1)
    have he : MulAut.conj (t * (r * s * r)) a₂ = t * ((r * s * r) * a₂ * (r * s * r)) * t := by
      rw [MulAut.conj_apply, mul_inv_rev, hρ, ht']
      group
    rw [he]
    exact hcy
  have hKα : K.map (MulAut.conj (s * t)).toMonoidHom =
      V.map (MulAut.conj (s * t)).toMonoidHom ⊔ Z.map (MulAut.conj (s * t)).toMonoidHom := by
    rw [hK]; exact Subgroup.map_sup _ _ _
  have hgen : ∀ X : Subgroup G, X ≤ centralizer (V : Set G) → X ≤ centralizer (Z : Set G) →
      X ≤ centralizer (K : Set G) := fun X h1 h2 => by
    rw [le_centralizer_iff, hK]
    exact sup_le (le_centralizer_iff.1 h1) (le_centralizer_iff.1 h2)
  rw [hKα]
  exact sup_le (hgen _ hG1 hG2) (hgen _ hG3 hG4)

end Generic

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

namespace CaseBData

theorem sec52_comm (hB : d.CaseBHyp) (c : d.CaseBData) (h11 : CaseBData.Sec52Sylow hB c)
    (h12 : CaseBData.Sec52Factors hB c) (h13 : c.W₂.map (MulAut.conj d.s).toMonoidHom = c.W₂)
    (h14 : c.Kc = c.W₂ ⊔ (c.W₂ ⊓ c.W₂.map (MulAut.conj d.r).toMonoidHom).map
      (MulAut.conj (d.r * d.s)).toMonoidHom) :
    CaseBData.Sec52Comm c := by
  have hLt : d.L ≤ centralizer ({d.t} : Set G) := hB.hyp.L_le_centralizer
  have hst : d.s * d.t = d.t * d.s :=
    mem_centralizer_singleton_iff.1 (hLt ((d.pull_le_L _) d.s_mem_N₂))
  have hrt : d.r * d.t = d.t * d.r :=
    mem_centralizer_singleton_iff.1 (hLt ((d.pull_le_L _) d.r_mem_N₁))
  have hrN : d.r ∈ normalizer (c.Kc : Set G) :=
    c.L₁_le_normalizer_Kc (d.N₁_le_L₁ d.r_mem_N₁)
  have hrK : c.Kc.map (MulAut.conj d.r).toMonoidHom ≤ c.Kc := by
    rintro _ ⟨x, hx, rfl⟩
    exact (mem_normalizer_iff.1 hrN x).1 hx
  exact sec52_comm_aux d.r_mul_r d.s_mul_s hB.hyp.t_mul_t hst hrt d.r_mul_s_pow_four
    (c.Kt_le_centralizer_Kc hB) inf_le_right h13 hrK h14

end CaseBData

end Data

namespace CaseBParts

theorem sec52Comm : Sec52CommStatement :=
  fun _ _ _ _ _ _ _ _ hB c h11 h12 h13 h14 => Data.CaseBData.sec52_comm hB c h11 h12 h13 h14

end CaseBParts

end CFSG.LocalAnalysis.EvenBN.U5
