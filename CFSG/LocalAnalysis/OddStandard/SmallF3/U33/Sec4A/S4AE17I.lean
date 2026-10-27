module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AE17G
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AM13A

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

private theorem map_conj_centralizes {E : Subgroup G} {a c : G}
    (h : ∀ e ∈ E, e * a = a * e) :
    ∀ e ∈ E.map (MulAut.conj c).toMonoidHom,
      e * (MulAut.conj c a) = (MulAut.conj c a) * e := by
  rintro e ⟨d, hd, rfl⟩
  have key := congrArg (MulAut.conj c) (h d hd)
  simpa only [map_mul, MulEquiv.coe_toMonoidHom] using key

private theorem mem_conj_map {E : Subgroup G} {c a : G} (ha : a ∈ E) :
    c * a * c⁻¹ ∈ E.map (MulAut.conj c).toMonoidHom :=
  (mem_map_conj (g := c) (E := E)).mpr ⟨a, ha, rfl⟩

theorem e17_no_gamma (h : L41GPh16 t L S x₁ x₂ lam rho) {γ : G} {E : Subgroup G}
    (hE : E ≤ centralizer ({lam * t} : Set G)) (hE2 : IsPGroup 2 E) (h32 : 32 ≤ Nat.card E)
    (hγE : γ ∈ E) (hcomm : ∀ e ∈ E, e * γ = γ * e) : γ ^ 4 = 1 := by
  have hlamT : lam ∈ wreathGrp x₁ x₂ lam := Subgroup.subset_closure (by simp)
  have hlam2 : lam * lam = 1 := n4_lam_sq h.toCtx0
  have hlam1 : lam ≠ 1 := by
    intro h1
    have := h.wreath.ord_lam
    rw [h1, orderOf_one] at this
    omega
  obtain ⟨g₀, hg₀⟩ := h.fusion.conj_tu lam hlamT hlam2 hlam1
  have hg₀' : g₀ * t * g₀⁻¹ = lam * t :=
    hg₀.trans (m13_t_comm_L h.toL41GPh5 (generators_mem_L h.toCtx0).2.2)
  have hEcg : E ≤ centralizer ({g₀ * t * g₀⁻¹} : Set G) := by
    rw [hg₀']; exact hE
  let E' : Subgroup G := E.map (MulAut.conj g₀⁻¹).toMonoidHom
  have hE'2 : IsPGroup 2 E' := hE2.map (MulAut.conj g₀⁻¹).toMonoidHom
  have hE'c : E' ≤ centralizer ({t} : Set G) := by
    rintro x hx
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hecomm : e * (g₀ * t * g₀⁻¹) = (g₀ * t * g₀⁻¹) * e :=
      Subgroup.mem_centralizer_singleton_iff.mp (hEcg he)
    have hconj : (MulAut.conj g₀⁻¹) (g₀ * t * g₀⁻¹) = t := by
      rw [MulAut.conj_apply]; group
    have key : (MulAut.conj g₀⁻¹) e * t = t * (MulAut.conj g₀⁻¹) e := by
      have hh := congrArg (MulAut.conj g₀⁻¹) hecomm
      simpa only [map_mul, hconj] using hh
    exact key
  obtain ⟨k, _, hk⟩ := exists_conj_le_of_isPGroup hE'c hE'2 h.toCtx0.le_invCent
    h.toCtx0.isPGroup h.toCtx0.relIndex_odd
  let E'' : Subgroup G := E'.map (MulAut.conj k).toMonoidHom
  have hE''S : E'' ≤ S := by
    rintro _ ⟨q, hq, rfl⟩
    simpa [MulAut.conj_apply] using hk q hq
  have hcard : Nat.card E'' = Nat.card E := by
    calc Nat.card E'' = Nat.card E' := Subgroup.card_map_of_injective (MulAut.conj k).injective
      _ = Nat.card E := Subgroup.card_map_of_injective (MulAut.conj g₀⁻¹).injective
  let w : G := MulAut.conj k (MulAut.conj g₀⁻¹ γ)
  have hwE'' : w ∈ E'' :=
    mem_conj_map (E := E') (c := k) (mem_conj_map (E := E) (c := g₀⁻¹) hγE)
  have hwS : w ∈ S := hE''S hwE''
  have hE'comm : ∀ e ∈ E', e * MulAut.conj g₀⁻¹ γ = MulAut.conj g₀⁻¹ γ * e := by
    have hmain := map_conj_centralizes (E := E) (a := γ) (c := g₀⁻¹) hcomm
    intro e he
    exact hmain e he
  have hE''w : ∀ e ∈ E'', e * w = w * e := by
    have hmain := map_conj_centralizes (E := E') (a := MulAut.conj g₀⁻¹ γ) (c := k) hE'comm
    intro e he
    exact hmain e he
  have hw4 : w ^ 4 = 1 :=
    e17_S_lemma h hwS hE''S hE''w (by rw [hcard]; exact h32)
  have hwconj : w = MulAut.conj (k * g₀⁻¹) γ := by
    show MulAut.conj k (MulAut.conj g₀⁻¹ γ) = MulAut.conj (k * g₀⁻¹) γ
    rw [MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply]
    group
  have hmap : MulAut.conj (k * g₀⁻¹) (γ ^ 4) = 1 := by
    have := map_pow (MulAut.conj (k * g₀⁻¹)) γ 4
    rw [this, ← hwconj]
    exact hw4
  exact (MulAut.conj (k * g₀⁻¹)).injective (by rw [hmap, map_one])

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
