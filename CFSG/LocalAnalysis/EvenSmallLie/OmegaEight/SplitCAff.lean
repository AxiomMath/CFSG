module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Act
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SplitCSylow

public section

namespace CFSG.EvenSmallLie.OmegaEight.SplitC

open Subgroup CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.UnitarySix.YamadaPar

variable {G : Type*} [Group G]

@[expose] def InducesOrth (ε : Eps) (H₀ Q : Subgroup G) (ψ : V6 → G) : Prop :=
  ∀ σ ∈ orthGroup ε, ∃ h ∈ H₀, h ∈ normalizer (Q : Set G) ∧ ∀ v, lin ψ h v = σ v

theorem sum_check (ε : Eps) : ((List.range 64).all fun v => (List.range 64).any fun s =>
    !qfB ε s && !qfB ε (v ^^^ s)) = true := by
  cases ε <;> decide +kernel

theorem exists_add_of_singular (ε : Eps) (w : V6) :
    ∃ v v', qfV ε v = 0 ∧ qfV ε v' = 0 ∧ v + v' = w := by
  have h := sum_check ε
  simp only [List.all_eq_true, List.mem_range, List.any_eq_true, Bool.and_eq_true,
    Bool.not_eq_true'] at h
  obtain ⟨s, hs, hs1, hs2⟩ := h (vecBits w) (vecBits_lt w)
  have hxs : vecBits w ^^^ s < 64 := Nat.xor_lt_two_pow (n := 6) (vecBits_lt w) hs
  refine ⟨toVec 6 s, toVec 6 (vecBits w ^^^ s), ?_, ?_, ?_⟩
  · rw [qfV_toVec ε hs, hs1]; rfl
  · rw [qfV_toVec ε hxs, hs2]; rfl
  · rw [toVec_xor, toVec_vecBits, ← add_assoc, add_comm (toVec 6 s), add_assoc,
      CharTwo.add_self_eq_zero, add_zero]

namespace Setting

variable {ε : Eps} {t : G} {L H₀ U Q P S₀ : Subgroup G} {a : G} {ψ : V6 → G} {p : Fin 6 → G}
  (hS : Setting ε t L H₀ U Q P S₀ a ψ p)
include hS

theorem conj_t_eq {g : G} (hg : g ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G)) :
    ∃ v, g * t * g⁻¹ = t * ψ v := by
  obtain ⟨v, h | h⟩ := hS.mem_E_iff.1 ((mem_normalizer_iff.1 hg t).1 (mem_sup_right
    (mem_zpowers t)))
  · exact absurd (h ▸ hS.rad.Q_le_L (hS.rad.ψ_mem v)) (hS.shape.conj_not_mem hS.rad.odd g)
  · exact ⟨v, h⟩

theorem conj_mem_Zset {g : G} (hg : g ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G))
    {v : V6} (hv : v ∈ Zset t Q ψ) : ∃ w ∈ Zset t Q ψ, g * (t * ψ v) * g⁻¹ = t * ψ w := by
  obtain ⟨h, hh, hht⟩ := hv
  obtain ⟨w, hw⟩ := hS.conj_t_eq (mul_mem hg hh)
  refine ⟨w, ⟨g * h, mul_mem hg hh, hw⟩, ?_⟩
  rw [← hht, ← hw]
  group

theorem normalizer_E_le (hsum : ∀ w, ∃ v ∈ Zset t Q ψ, ∃ v' ∈ Zset t Q ψ, v + v' = w) :
    normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) ≤ normalizer (Q : Set G) := by
  have hprod : ∀ v v', ψ (v + v') = t * ψ v * (t * ψ v') := by
    intro v v'
    rw [hS.rad.ψ_add, mul_assoc t, ← mul_assoc (ψ v), hS.commute_ψ v, ← mul_assoc,
      ← mul_assoc, hS.shape.mul_self, one_mul]
  have key : ∀ g ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G), ∀ x ∈ Q,
      g * x * g⁻¹ ∈ Q := by
    intro g hg x hx
    obtain ⟨w, rfl⟩ := hS.rad.mem_ψ x hx
    obtain ⟨v, hv, v', hv', rfl⟩ := hsum w
    obtain ⟨u, -, hu⟩ := hS.conj_mem_Zset hg hv
    obtain ⟨u', -, hu'⟩ := hS.conj_mem_Zset hg hv'
    have : g * ψ (v + v') * g⁻¹ = ψ (u + u') := by
      rw [hprod, hprod, ← hu, ← hu']
      group
    rw [this]
    exact hS.rad.ψ_mem _
  intro g hg
  refine mem_normalizer_iff.2 fun x => ⟨key g hg x, fun hx => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hx
  simpa [mul_assoc] using this

theorem normalizer_E_le_of_singular (hZs : ∀ v, qfV ε v = 0 → v ∈ Zset t Q ψ) :
    normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) ≤ normalizer (Q : Set G) :=
  hS.normalizer_E_le fun w => by
    obtain ⟨v, v', hv, hv', h⟩ := exists_add_of_singular ε w
    exact ⟨v, hZs v hv, v', hZs v' hv', h⟩

section Aff

variable (hNQ : normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) ≤ normalizer (Q : Set G))
include hNQ

theorem t_affF {g : G} (hg : g ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G)) (v : V6) :
    t * ψ (affF t ψ g v) = g * (t * ψ v) * g⁻¹ := by
  have hmem : t * (g * (t * ψ v) * g⁻¹) ∈ Q := by
    obtain ⟨w, hw⟩ := hS.conj_t_eq hg
    have h1 : t * (g * (t * ψ v) * g⁻¹) = ψ w * (g * ψ v * g⁻¹) :=
      calc t * (g * (t * ψ v) * g⁻¹) = t * (g * t * g⁻¹) * (g * ψ v * g⁻¹) := by group
        _ = t * (t * ψ w) * (g * ψ v * g⁻¹) := by rw [hw]
        _ = (t * t) * ψ w * (g * ψ v * g⁻¹) := by group
        _ = ψ w * (g * ψ v * g⁻¹) := by rw [hS.shape.mul_self, one_mul]
    rw [h1]
    exact mul_mem (hS.rad.ψ_mem w) (hS.rad.conj_mem_Q (hNQ hg) v)
  rw [affF, hS.rad.ψ_coord hmem, ← mul_assoc, hS.shape.mul_self, one_mul]

theorem affF_eq_iff {g : G} (hg : g ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G))
    (v w : V6) : affF t ψ g v = w ↔ g * (t * ψ v) * g⁻¹ = t * ψ w := by
  rw [← hS.t_affF hNQ hg]
  constructor
  · rintro rfl; rfl
  · intro h; exact hS.rad.ψ_inj (mul_left_cancel h)

theorem affF_mul {g h : G} (hg : g ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G))
    (hh : h ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G)) (v : V6) :
    affF t ψ (g * h) v = affF t ψ g (affF t ψ h v) := by
  rw [hS.affF_eq_iff hNQ (mul_mem hg hh), hS.t_affF hNQ hg, hS.t_affF hNQ hh]
  group

theorem affF_one (v : V6) : affF t ψ 1 v = v := by
  rw [hS.affF_eq_iff hNQ (one_mem _)]
  group

theorem affF_eq_add {g : G} (hg : g ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G))
    (v : V6) : affF t ψ g v = affF t ψ g 0 + lin ψ g v := by
  rw [hS.affF_eq_iff hNQ hg]
  calc g * (t * ψ v) * g⁻¹ = (g * (t * ψ 0) * g⁻¹) * (g * ψ v * g⁻¹) := by
        rw [hS.rad.ψ_zero]; group
    _ = t * ψ (affF t ψ g 0) * ψ (lin ψ g v) := by
        rw [hS.t_affF hNQ hg, hS.rad.ψ_lin (hNQ hg)]
    _ = t * ψ (affF t ψ g 0 + lin ψ g v) := by rw [hS.rad.ψ_add, mul_assoc]

@[expose] noncomputable def affHom :
    normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) →* Equiv.Perm V6 where
  toFun g :=
    { toFun := affF t ψ g
      invFun := affF t ψ (g : G)⁻¹
      left_inv := fun v => by
        rw [← hS.affF_mul hNQ (inv_mem g.2) g.2, inv_mul_cancel, hS.affF_one hNQ]
      right_inv := fun v => by
        rw [← hS.affF_mul hNQ g.2 (inv_mem g.2), mul_inv_cancel, hS.affF_one hNQ] }
  map_one' := Equiv.ext (hS.affF_one hNQ)
  map_mul' g h := Equiv.ext (hS.affF_mul hNQ g.2 h.2)

theorem affHom_apply (g : normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G)) (v : V6) :
    hS.affHom hNQ g v = affF t ψ g v := rfl

theorem affF_mem_Zset_iff {g : G} (hg : g ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G))
    (v : V6) : affF t ψ g v ∈ Zset t Q ψ ↔ v ∈ Zset t Q ψ := by
  constructor
  · rintro ⟨h, hh, hht⟩
    refine ⟨g⁻¹ * h, mul_mem (inv_mem hg) hh, ?_⟩
    have : g * (t * ψ v) * g⁻¹ = h * t * h⁻¹ := by rw [hht, hS.t_affF hNQ hg]
    calc g⁻¹ * h * t * (g⁻¹ * h)⁻¹ = g⁻¹ * (h * t * h⁻¹) * g := by group
      _ = g⁻¹ * (g * (t * ψ v) * g⁻¹) * g := by rw [this]
      _ = t * ψ v := by group
  · rintro ⟨h, hh, hht⟩
    refine ⟨g * h, mul_mem hg hh, ?_⟩
    calc g * h * t * (g * h)⁻¹ = g * (h * t * h⁻¹) * g⁻¹ := by group
      _ = g * (t * ψ v) * g⁻¹ := by rw [hht]
      _ = t * ψ (affF t ψ g v) := (hS.t_affF hNQ hg v).symm

theorem affF_eq_lin {h : G} (hh : h ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G))
    (ht : h * t = t * h) (v : V6) : affF t ψ h v = lin ψ h v := by
  rw [hS.affF_eq_add hNQ hh, (hS.affF_eq_iff hNQ hh 0 0).2 (by
    rw [hS.rad.ψ_zero, mul_one, ht, mul_inv_cancel_right]), zero_add]

theorem affHom_mem_affGroup (hZ : ∀ v, v ∈ Zset t Q ψ ↔ qfV ε v = 0)
    (g : normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G)) : hS.affHom hNQ g ∈ affGroup ε := by
  refine ⟨fun v => ?_, fun x y z => ?_⟩
  · have h := hS.affF_mem_Zset_iff hNQ g.2 v
    rw [hZ, hZ] at h
    rw [hS.affHom_apply hNQ]
    rcases qfV_cases ε v with hv | hv <;> rcases qfV_cases ε (affF t ψ g v) with hw | hw
    · rw [hv, hw]
    · exact absurd (h.2 hv) (by rw [hw]; exact one_ne_zero)
    · exact absurd (h.1 hw) (by rw [hv]; exact one_ne_zero)
    · rw [hv, hw]
  · simp only [hS.affHom_apply hNQ]
    rw [hS.affF_eq_add hNQ g.2, hS.affF_eq_add hNQ g.2 x, hS.affF_eq_add hNQ g.2 y,
      hS.affF_eq_add hNQ g.2 z, hS.rad.lin_add (hNQ g.2), hS.rad.lin_add (hNQ g.2)]
    set c := affF t ψ (g : G) 0
    have hc : c + c = 0 := CharTwo.add_self_eq_zero c
    calc c + (lin ψ g x + lin ψ g y + lin ψ g z) =
        (c + c) + c + (lin ψ g x + lin ψ g y + lin ψ g z) := by rw [hc, zero_add]
      _ = c + lin ψ g x + (c + lin ψ g y) + (c + lin ψ g z) := by abel

theorem exists_affF_eq (hZ : ∀ v, v ∈ Zset t Q ψ ↔ qfV ε v = 0)
    (hO : InducesOrth ε H₀ Q ψ) {σ : Equiv.Perm V6} (hσ : σ ∈ affGroup ε) :
    ∃ g ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G), ∀ v, affF t ψ g v = σ v := by
  have h0 : σ 0 ∈ Zset t Q ψ := (hZ _).2 (by rw [hσ.1 0, qfV_zero])
  obtain ⟨g₁, hg₁, hg₁t⟩ := h0
  have hz : affF t ψ g₁ 0 = σ 0 :=
    (hS.affF_eq_iff hNQ hg₁ 0 _).2 (by rw [hS.rad.ψ_zero, mul_one, hg₁t])
  set A := hS.affHom hNQ ⟨g₁, hg₁⟩
  have hA : A ∈ affGroup ε := hS.affHom_mem_affGroup hNQ hZ _
  have hτ : A⁻¹ * σ ∈ orthGroup ε := by
    refine mem_orthGroup_of_mem_affGroup ((affGroup ε).mul_mem ((affGroup ε).inv_mem hA) hσ) ?_
    rw [Equiv.Perm.mul_apply, ← hz]
    exact perm_inv_apply A 0
  obtain ⟨h, hhH, hhQ, hlin⟩ := hO _ hτ
  have hht : h * t = t * h := hS.shape.commute_of_mem hhH
  have hhE : h ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) :=
    mem_normalizer_sup hhQ (mem_normalizer_zpowers hht)
  refine ⟨g₁ * h, mul_mem hg₁ hhE, fun v => ?_⟩
  rw [hS.affF_mul hNQ hg₁ hhE, hS.affF_eq_lin hNQ hhE hht, hlin]
  change A ((A⁻¹ * σ) v) = σ v
  rw [Equiv.Perm.mul_apply, perm_apply_inv]

end Aff

end Setting

end CFSG.EvenSmallLie.OmegaEight.SplitC
