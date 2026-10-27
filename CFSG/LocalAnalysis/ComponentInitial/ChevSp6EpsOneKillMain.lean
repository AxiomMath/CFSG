module

public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneKillBig
public import CFSG.Monster.B.Recog.GenericTransferExtremal
public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneKillMax
public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneKillSign
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne

open Subgroup

theorem pres_mul {u : Bool} {σ τ : Equiv.Perm (Fin 64)}
    (hσ : σ ∈ Gq u) (hτ : τ ∈ Gq u) : Pres u (σ * τ) ↔ (Pres u σ ↔ Pres u τ) := by
  cases u
  · exact pres_mul_false hσ hτ
  · obtain ⟨ω, hω, hωt⟩ := exists_omega
    exact pres_mul_true hω hωt hσ hτ

theorem pres_one {u : Bool} : Pres u 1 := by
  show presT u (tupleOf 1) = true
  rw [tupleOf_one]
  cases u
  · exact presT_facts.1
  · exact presT_facts.2.1

theorem betaOf_comm (u : Bool) (v w : ℕ) : betaOf u v w = betaOf u w v := by
  unfold betaOf
  rw [Nat.xor_comm v w, Nat.xor_assoc, Nat.xor_comm (qOf u v), ← Nat.xor_assoc]

namespace KillData

variable {G : Type*} [Group G] {u : Bool} {Jh E : Subgroup G} {cV cE : G → ℕ}
  {z l₁ l₂ : G} (h : KillData u Jh E cV cE z l₁ l₂)
include h

theorem actP_one : h.actP 1 = 1 := by
  rw [h.actP_of_mem (one_mem _),
    show (⟨1, one_mem _⟩ : normalizer (Jh : Set G)) = 1 from rfl, map_one]

theorem not_pres_z : ¬ Pres u (h.actP z) := by
  rw [h.actP_of_mem h.z_norm]
  intro hp
  have ht : tupleOf (h.ρV ⟨z, h.z_norm⟩) = z0T :=
    h.tupleOf_ρV_eq h.z_norm ⟨rfl, by decide⟩ h.z_act
  have hz : presT u z0T = true := by rw [← ht]; exact hp
  cases u
  · rw [presT_facts.2.2.1] at hz
    exact absurd hz (by decide)
  · rw [presT_facts.2.2.2] at hz
    exact absurd hz (by decide)

theorem card_le_of_le_cent_conj (g : G) {P : Subgroup G} (hP : IsPGroup 2 P)
    (hPt : P ≤ centralizer ({g * z * g⁻¹} : Set G)) : Nat.card P ≤ 2 ^ 10 := by
  have := h.cent (P.map (MulAut.conj g⁻¹).toMonoidHom) (hP.map _) (by
    rintro _ ⟨x, hx, rfl⟩
    have hxt := mem_centralizer_singleton_iff.1 (hPt hx)
    rw [mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc g⁻¹ * x * g * z = g⁻¹ * (x * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * z * g⁻¹) * x) * g := by rw [hxt]
      _ = z * (g⁻¹ * x * g) := by group)
  rwa [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective] at this

section Main

variable [Finite G]

theorem pres_actP_mul {x y : G} (hx : x ∈ h.SG) (hy : y ∈ h.SG) :
    Pres u (h.actP (x * y)) ↔ (Pres u (h.actP x) ↔ Pres u (h.actP y)) := by
  rw [h.actP_mul (h.SG_le_X hx) (h.SG_le_X hy), h.actP_of_mem (h.SG_le_X hx),
    h.actP_of_mem (h.SG_le_X hy)]
  exact pres_mul (h.ρV_mem_Gq _) (h.ρV_mem_Gq _)

@[expose] noncomputable def Msub : Subgroup G where
  carrier := {x | x ∈ h.SG ∧ Pres u (h.actP x)}
  mul_mem' := fun {x y} hx hy =>
    ⟨mul_mem hx.1 hy.1, (h.pres_actP_mul hx.1 hy.1).2 (iff_of_true hx.2 hy.2)⟩
  one_mem' := ⟨one_mem _, by rw [h.actP_one]; exact pres_one⟩
  inv_mem' := fun {x} hx => ⟨inv_mem hx.1, by
    have key := h.pres_actP_mul hx.1 (inv_mem hx.1)
    rw [mul_inv_cancel, h.actP_one] at key
    exact (key.1 pres_one).1 hx.2⟩

theorem mem_Msub {x : G} : x ∈ h.Msub ↔ x ∈ h.SG ∧ Pres u (h.actP x) := Iff.rfl

theorem relIndex_Msub : h.Msub.relIndex h.SG = 2 := by
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
  refine ⟨⟨z, h.z_mem_SG⟩, fun b => ?_⟩
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, h.mem_Msub]
  have key := h.pres_actP_mul b.2 h.z_mem_SG
  have hz := h.not_pres_z
  by_cases hb : Pres u (h.actP b)
  · exact Or.inr ⟨⟨b.2, hb⟩, fun hbz => hz ((key.1 hbz.2).1 hb)⟩
  · exact Or.inl ⟨⟨mul_mem b.2 h.z_mem_SG,
      key.2 ⟨fun h' => absurd h' hb, fun h' => absurd h' hz⟩⟩, fun hbM => hb hbM.2⟩

omit [Finite G] in
theorem card_cent_of_mem_Jh {t : G} (htJ : t ∈ Jh) (htE : t ∉ E) (ht2 : t * t = 1) :
    2 ^ 11 ≤ Nat.card (Jh ⊓ centralizer ({t} : Set G) : Subgroup G) := by
  classical
  set C := (Jh ⊓ centralizer ({t} : Set G) : Subgroup G) with hCdef
  have hEC : E ≤ C := fun e he =>
    ⟨h.E_le he, mem_centralizer_singleton_iff.2 (h.central e he t htJ)⟩
  have hcard := h.card_of_le hEC inf_le_left
  have hv0 : cV t ≠ 0 := fun h0 => htE ((h.cV_eq_zero t htJ).1 h0)
  have hq : qOf u (cV t) = 0 := by
    have := (h.sq t htJ).2
    rw [ht2, h.cE_one] at this
    exact this.symm
  have h4 := sing_ker u (cV t) (h.cV_lt t htJ) hv0 hq
  rw [card_filter_range] at h4
  have hle : Nat.card {v : Fin 64 // (betaOf u (cV t) v == 0) = true} ≤
      Nat.card {v : Fin 64 // ∃ x ∈ C, cV x = v} := by
    refine Nat.card_le_card_of_injective (fun v => ⟨v.1, h.liftV v.1,
      Subgroup.mem_inf.2 ⟨h.liftV_mem _, ?_⟩, h.cV_liftV v.1.2⟩) (fun a b hab => by
        simp only [Subtype.mk.injEq] at hab
        exact Subtype.ext hab)
    rw [mem_centralizer_singleton_iff]
    have hx := h.liftV_mem v.1
    have hβ : betaOf u (cV (h.liftV v.1)) (cV t) = 0 := by
      rw [h.cV_liftV v.1.2, betaOf_comm]
      exact beq_iff_eq.1 v.2
    have hc := h.cE_comm hx htJ
    rw [hβ] at hc
    have h1 := h.cE_inj _ (h.comm_mem_E hx htJ) hc
    calc h.liftV v.1 * t = t * h.liftV v.1 * ((h.liftV v.1)⁻¹ * t⁻¹ * h.liftV v.1 * t) := by
          group
      _ = t * h.liftV v.1 := by rw [h1, mul_one]
  rw [hcard]
  omega


theorem false_of_killData : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let T : Sylow 2 G :=
    { toSubgroup := h.SG
      isPGroup' := h.isPGroup_SG
      is_maximal' := fun {Q} hQ hle => h.SG_maximal Q hQ hle }
  have hz2 : z ^ 2 = 1 := by rw [pow_two]; exact h.z_sq
  obtain ⟨g, hgM, -⟩ := CFSG.Monster.B.Recog.exists_conj_mem_odd_relIndex_of_transfer T
    (M := h.Msub) h.relIndex_Msub hz2 h.index2
  have htS : g * z * g⁻¹ ∈ h.SG := hgM.1
  have hpres : Pres u (h.actP (g * z * g⁻¹)) := hgM.2
  have ht2 : (g * z * g⁻¹) * (g * z * g⁻¹) = 1 := by
    calc (g * z * g⁻¹) * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [h.z_sq]; group
  have hcent : ∀ {P : Subgroup G}, IsPGroup 2 P →
      P ≤ centralizer ({g * z * g⁻¹} : Set G) → Nat.card P ≤ 2 ^ 10 :=
    fun hP hPt => h.card_le_of_le_cent_conj g hP hPt
  by_cases htJ : g * z * g⁻¹ ∈ Jh
  · by_cases htE : g * z * g⁻¹ ∈ E
    · have hle : Jh ≤ centralizer ({g * z * g⁻¹} : Set G) := fun x hx =>
        mem_centralizer_singleton_iff.2 (h.central _ htE x hx).symm
      have := hcent h.isPGroup_Jh hle
      rw [h.card_Jh] at this
      norm_num at this
    · have h11 := h.card_cent_of_mem_Jh htJ htE ht2
      have := hcent (h.isPGroup_Jh.to_le inf_le_left) inf_le_right
      omega
  · obtain ⟨C, hC, hC2, hCc⟩ := h.exists_big_of_cert htS htJ ht2
      (by rw [← h.actP_of_mem (h.SG_le_X htS)]; exact hpres)
    have := hcent hC2 hC
    omega

end Main

end KillData

end CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne
