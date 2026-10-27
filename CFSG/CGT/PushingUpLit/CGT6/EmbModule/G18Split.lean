module

public import CFSG.CGT.PushingUpLit.CGT6X.ExtOmegaMinus

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS6 CFSG.CGT.PushingUpLit.CGT6X

theorem exists_equiv_of_natSection {V : Type} [CommGroup V] {n : ℕ} [NeZero n]
    {Y : Subgroup (MulAut V)} (hY : IsNatSectionBy (omegaMinusAct n) Y (commV Y) ⊥) :
    (∀ y ∈ Y, ∀ p ∈ commV Y, y p ∈ commV Y) ∧
      ∃ (θ : ↥Y ≃* Matrix.SpecialLinearGroup (Fin 2) (Fq (2 * n))) (φ : ↥(commV Y) ≃* NMod n),
        ∀ (g : ↥Y) (x : ↥(commV Y)) (hp : (g : MulAut V) x ∈ commV Y),
          φ ⟨(g : MulAut V) x, hp⟩ = rhoW n (θ g) (φ x) := by
  obtain ⟨hinv, θ, β, hβsurj, hβker, hβeq⟩ := hY
  let φ0 : ↥(commV Y) →* NMod n := (eHW n).toMonoidHom.comp β
  have hφinj : Function.Injective φ0 := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : β x = 1 := (MulEquiv.map_eq_one_iff (eHW n)).mp hx
    have h2 : x ∈ β.ker := h1
    rw [hβker] at h2
    exact Subtype.ext (Subgroup.mem_bot.1 (Subgroup.mem_subgroupOf.1 h2))
  have hφsurj : Function.Surjective φ0 := fun m => by
    obtain ⟨b, hb⟩ := hβsurj ((eHW n).symm m)
    exact ⟨b, by show eHW n (β b) = m; rw [hb]; exact (eHW n).apply_symm_apply m⟩
  refine ⟨hinv, θ, MulEquiv.ofBijective φ0 ⟨hφinj, hφsurj⟩, fun g x hp => ?_⟩
  have := hβeq g x hp
  show eHW n (β ⟨(g : MulAut V) x, hp⟩) = rhoW n (θ g) (eHW n (β x))
  rw [this, eHW_equivariant]

theorem exists_complement_of_natSection {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) {n : ℕ} [NeZero n] {Y : Subgroup (MulAut V)}
    (hY : IsNatSectionBy (omegaMinusAct n) Y (commV Y) ⊥) :
    ∃ C : Subgroup V, (∀ y ∈ Y, ∀ c ∈ C, y c = c) ∧ C ⊓ commV Y = ⊥ ∧ C ⊔ commV Y = ⊤ := by
  obtain ⟨hinv, θ, φ, hφ⟩ := exists_equiv_of_natSection hY
  let τV : ↥Y →* MulAut V := Y.subtype
  have hN'inv : SInv τV (commV Y) := fun g x hx => hinv g g.2 x hx
  have htriv : ∀ (g : ↥Y) (x : V), τV g x * x⁻¹ ∈ commV Y := fun g x =>
    Subgroup.subset_closure ⟨(g : MulAut V), g.2, x, rfl⟩
  let σ : ↥Y →* MulAut (NMod n) := (rhoW n).comp θ.toMonoidHom
  have hφeq : ∀ (g : ↥Y) (x : ↥(commV Y)),
      φ (resAct τV (commV Y) hN'inv g x) = σ g (φ x) := fun g x => hφ g x (hinv g g.2 x x.2)
  have h1G : ∀ c : ↥Y → NMod n, IsCocycle σ c → IsCoboundary σ c := fun c hc =>
    isCoboundary_comp (ρ := rhoW n) θ (fun c hc => h1_nat n hc) hc
  have hcoh : ∀ c : ↥Y → ↥(commV Y), IsCocycle (resAct τV (commV Y) hN'inv) c →
      IsCoboundary (resAct τV (commV Y) hN'inv) c := fun c hc =>
    isCoboundary_of_equiv φ.symm (fun g v => by
      apply φ.injective
      rw [hφeq, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]) h1G hc
  obtain ⟨C, hCinv, hCN, hCsup⟩ := exists_inv_complement_top hV τV (commV Y) hN'inv htriv hcoh
  refine ⟨C, fun y hy c hc => ?_, hCN, hCsup⟩
  have h1 : τV ⟨y, hy⟩ c * c⁻¹ ∈ C ⊓ commV Y :=
    ⟨C.mul_mem (hCinv ⟨y, hy⟩ c hc) (C.inv_mem hc), htriv ⟨y, hy⟩ c⟩
  rw [hCN] at h1
  exact mul_inv_eq_one.mp (Subgroup.mem_bot.mp h1)

end CFSG.CGT.PushingUpLit.CGT6
