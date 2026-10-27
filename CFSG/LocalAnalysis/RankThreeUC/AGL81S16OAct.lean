module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16ONorm
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16OFields

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open Subgroup Matrix

theorem card_fix_sq_le {F : Type} [Field F] [Finite F] {ι : Type} [Finite ι] {θ : F →+* F}
    (hθ : θ ≠ RingHom.id F) (α : (ι → F) ≃+ (ι → F))
    (hα : ∀ (c : F) (x : ι → F), α (c • x) = θ c • α x) :
    Nat.card {x : ι → F // α x = x} ^ 2 ≤ Nat.card (ι → F) := by
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : F, θ c₀ ≠ c₀ := by
    by_contra h
    push_neg at h
    exact hθ (RingHom.ext h)
  let P := {x : ι → F // α x = x}
  have hinj : Function.Injective (fun p : P × P => (p.1 : ι → F) + c₀ • (p.2 : ι → F)) := by
    intro p q h
    have h1 : (p.1 : ι → F) + c₀ • (p.2 : ι → F) = (q.1 : ι → F) + c₀ • (q.2 : ι → F) := h
    set u : ι → F := (p.1 : ι → F) - (q.1 : ι → F) with hu
    set v : ι → F := (q.2 : ι → F) - (p.2 : ι → F) with hv
    have huv : u = c₀ • v := by
      rw [hu, hv, smul_sub, sub_eq_sub_iff_add_eq_add, add_comm (c₀ • (q.2 : ι → F)) (q.1 : ι → F)]
      exact h1
    have hαu : α u = u := by
      rw [hu, map_sub, p.1.2, q.1.2]
    have hαv : α v = v := by
      rw [hv, map_sub, q.2.2, p.2.2]
    have h2 : u = θ c₀ • v := by
      calc u = α u := hαu.symm
        _ = α (c₀ • v) := by rw [huv]
        _ = θ c₀ • α v := hα c₀ v
        _ = θ c₀ • v := by rw [hαv]
    have h3 : (c₀ - θ c₀) • v = 0 := by
      rw [sub_smul, ← huv, ← h2, sub_self]
    have hv0 : v = 0 := (smul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr (Ne.symm hc₀))
    have hu0 : u = 0 := by rw [huv, hv0, smul_zero]
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · exact sub_eq_zero.mp hu0
    · exact (sub_eq_zero.mp hv0).symm
  have := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_prod] at this
  rw [sq]
  exact this

section Act2

variable {G : Type} [Group G] [Finite G] {n : ℕ} {M L V : Subgroup G} (d : O6NatData G n L V)

theorem O6NatData.act_inv_act (hMV : M ≤ normalizer (V : Set G)) {m : G} (hm : m ∈ M)
    (x : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → d.F) :
    d.act m⁻¹ (hMV (M.inv_mem hm)) (d.act m (hMV hm) x) = x := by
  have h : d.rho M hMV ⟨m⁻¹, M.inv_mem hm⟩ * d.rho M hMV ⟨m, hm⟩ = 1 := by
    rw [← map_mul]
    have : (⟨m⁻¹, M.inv_mem hm⟩ : ↥M) * ⟨m, hm⟩ = 1 := Subtype.ext (inv_mul_cancel m)
    rw [this, map_one]
  have h' := congrArg (fun f => f x) h
  simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply] at h'
  rw [O6NatData.rho_apply, O6NatData.rho_apply] at h'
  exact h'

theorem O6NatData.act_act_inv (hMV : M ≤ normalizer (V : Set G)) {m : G} (hm : m ∈ M)
    (x : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → d.F) :
    d.act m (hMV hm) (d.act m⁻¹ (hMV (M.inv_mem hm)) x) = x := by
  have h : d.rho M hMV ⟨m, hm⟩ * d.rho M hMV ⟨m⁻¹, M.inv_mem hm⟩ = 1 := by
    rw [← map_mul]
    have : (⟨m, hm⟩ : ↥M) * ⟨m⁻¹, M.inv_mem hm⟩ = 1 := Subtype.ext (mul_inv_cancel m)
    rw [this, map_one]
  have h' := congrArg (fun f => f x) h
  simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply] at h'
  rw [O6NatData.rho_apply, O6NatData.rho_apply] at h'
  exact h'

@[expose] noncomputable def O6NatData.actAddEquiv (hMV : M ≤ normalizer (V : Set G)) {m : G}
    (hm : m ∈ M) :
    (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → d.F) ≃+ (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → d.F) where
  toFun := d.act m (hMV hm)
  invFun := d.act m⁻¹ (hMV (M.inv_mem hm))
  left_inv := d.act_inv_act hMV hm
  right_inv := d.act_act_inv hMV hm
  map_add' := d.act_add m (hMV hm)

theorem O6NatData.act_normalizes (hLM : L ≤ M) (hML : M ≤ normalizer (L : Set G))
    (hMV : M ≤ normalizer (V : Set G)) {m : G} (hm : m ∈ M)
    {g : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) d.F}
    (hg : g ∈ StatedOmega (StatedQuadMinus 3 d.F d.b d.c)) :
    ∃ g' ∈ StatedOmega (StatedQuadMinus 3 d.F d.b d.c),
      ∀ x : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → d.F,
        d.act m (hMV hm) (((g : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) d.F) :
          Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) d.F) *ᵥ x) =
          ((g' : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) d.F) :
            Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) d.F) *ᵥ
            d.act m (hMV hm) x := by
  obtain ⟨l, hl⟩ := d.ε_surj ⟨g, hg⟩
  have hlL : (l : G) ∈ L := l.2
  have hlV : (l : G) ∈ normalizer (V : Set G) := hMV (hLM hlL)
  have hml : m * (l : G) * m⁻¹ ∈ L := (mem_normalizer_iff.mp (hML hm) (l : G)).mp hlL
  have hmlV : m * (l : G) * m⁻¹ ∈ normalizer (V : Set G) := hMV (hLM hml)
  refine ⟨((d.ε ⟨m * (l : G) * m⁻¹, hml⟩ : ↥(StatedOmega (StatedQuadMinus 3 d.F d.b d.c))) :
    GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) d.F), (d.ε _).2, fun x => ?_⟩
  have e := d.act_eps (l := (l : G)) (m := m) hlL hlV hml hmlV (hMV hm) x
  have hgl : ((d.ε ⟨(l : G), hlL⟩ : ↥(StatedOmega (StatedQuadMinus 3 d.F d.b d.c))) :
      GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) d.F) = g := congrArg Subtype.val hl
  rw [← hgl]
  exact e

theorem O6NatData.act_semilinear (hn : 1 ≤ n) (hLM : L ≤ M) (hML : M ≤ normalizer (L : Set G))
    (hMV : M ≤ normalizer (V : Set G)) {m : G} (hm : m ∈ M) :
    ∃ θ : d.F →+* d.F, ∀ (c : d.F) (x : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → d.F),
      d.act m (hMV hm) (c • x) = θ c • d.act m (hMV hm) x := by
  haveI := d.charP hn
  refine omega_semilinear d.irred (d.actAddEquiv hMV hm) (fun g hg => ?_)
  obtain ⟨g', hg', hgx⟩ := d.act_normalizes hLM hML hMV (M.inv_mem hm) hg
  exact ⟨g', hg', hgx⟩

theorem O6NatData.mem_centralizer_of_act_eq (hMV : M ≤ normalizer (V : Set G)) {m : G}
    (hm : m ∈ M) (h : ∀ x, d.act m (hMV hm) x = x) : m ∈ centralizer (V : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have h1 := h (d.eqv ⟨v, hv⟩)
  rw [d.act_eqv] at h1
  have h2 : conjOn V m (hMV hm) ⟨v, hv⟩ = ⟨v, hv⟩ := d.eqv.injective h1
  have h3 : m * v * m⁻¹ = v := congrArg Subtype.val h2
  calc v * m = (m * v * m⁻¹) * m := by rw [h3]
    _ = m * v := by group

end Act2

end CFSG.LocalAnalysis.RankThreeUC
