module

public import CFSG.LocalAnalysis.OddStandard.SmallAltFiveDefs
public import CFSG.Quasithin.SteinbergCBAlternatingAut
public import CFSG.LocalAnalysis.SectionRank.AlternatingCover
public import CFSG.Open.StandardComponentRecognitionMilestoneDefs

public section

namespace CFSG.OddStandard

open Subgroup Equiv CFSG.Open

variable {G : Type*} [Group G]

section Theta

variable {L : Subgroup G}

theorem thetaZero_surjective (θ : L ⧸ Subgroup.center L ≃* alternatingGroup (Fin 5)) :
    Function.Surjective (thetaZero θ) :=
  θ.surjective.comp (QuotientGroup.mk'_surjective _)

theorem ker_thetaZero (θ : L ⧸ Subgroup.center L ≃* alternatingGroup (Fin 5)) :
    (thetaZero θ).ker = Subgroup.center L := by
  ext x
  rw [MonoidHom.mem_ker, thetaZero, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

theorem center_eq_bot [Finite G] (hL : standardComponentIsStandard L)
    (hodd : Odd (Nat.card (Subgroup.center L)))
    (θ : L ⧸ Subgroup.center L ≃* alternatingGroup (Fin 5)) : Subgroup.center L = ⊥ := by
  have : Group.IsPerfect L := ⟨hL.1.1⟩
  have hker := ker_thetaZero θ
  have h := (CFSG.SectionRank.alternating_small_odd_cover_bound (n := 5) le_rfl (by norm_num)
    (thetaZero θ) (thetaZero_surjective θ) hker.le (by rw [hker]; exact hodd)).1 (Or.inl rfl)
  rwa [hker] at h

theorem thetaZero_bijective [Finite G] (hL : standardComponentIsStandard L)
    (hodd : Odd (Nat.card (Subgroup.center L)))
    (θ : L ⧸ Subgroup.center L ≃* alternatingGroup (Fin 5)) :
    Function.Bijective (thetaZero θ) := by
  refine ⟨(injective_iff_map_eq_one _).mpr fun x hx => ?_, thetaZero_surjective θ⟩
  have : x ∈ (thetaZero θ).ker := hx
  rw [ker_thetaZero, center_eq_bot hL hodd θ, Subgroup.mem_bot] at this
  exact this

theorem inf_centralizer_eq_bot_of_center_eq_bot (hbot : Subgroup.center L = ⊥) :
    L ⊓ centralizer (L : Set G) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hc : (⟨x, hx.1⟩ : L) ∈ Subgroup.center L := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (mem_centralizer_iff.mp hx.2 y y.2)
  rw [hbot, Subgroup.mem_bot] at hc
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val hc)

@[expose] noncomputable def thetaEquiv {L : Subgroup G}
    (θ : L ⧸ Subgroup.center L ≃* alternatingGroup (Fin 5))
    (hbij : Function.Bijective (thetaZero θ)) : L ≃* alternatingGroup (Fin 5) :=
  MulEquiv.ofBijective (thetaZero θ) hbij

end Theta

@[expose] noncomputable def conjEquiv5 : Perm (Fin 5) ≃* MulAut (alternatingGroup (Fin 5)) :=
  MulEquiv.ofBijective (CFSG.Quasithin.SteinbergCB.conjPerm 5)
    ⟨CFSG.Quasithin.SteinbergCB.conjPerm_injective (by norm_num),
      CFSG.Quasithin.SteinbergCB.conjPerm_surjective (Or.inl rfl)⟩

theorem conjEquiv5_apply (σ : Perm (Fin 5)) (g : alternatingGroup (Fin 5)) :
    ((conjEquiv5 σ g : alternatingGroup (Fin 5)) : Perm (Fin 5)) = σ * g * σ⁻¹ :=
  CFSG.Quasithin.SteinbergCB.conjPerm_apply 5 σ g

theorem perm_eq_of_conj_eq {σ τ : Perm (Fin 5)}
    (h : ∀ g : alternatingGroup (Fin 5), σ * g * σ⁻¹ = τ * g * τ⁻¹) : σ = τ := by
  apply conjEquiv5.injective
  refine MulEquiv.ext fun g => Subtype.ext ?_
  rw [conjEquiv5_apply, conjEquiv5_apply]
  exact h g

section Rho

variable {L : Subgroup G}

@[expose] noncomputable def rhoOf (e : L ≃* alternatingGroup (Fin 5)) :
    normalizer (L : Set G) →* Perm (Fin 5) :=
  conjEquiv5.symm.toMonoidHom.comp ((MulAut.congr e).toMonoidHom.comp L.normalizerMonoidHom)

theorem rhoOf_transports (e : L ≃* alternatingGroup (Fin 5)) (m : normalizer (L : Set G)) :
    Transports (e : L →* alternatingGroup (Fin 5)) (m : G) (rhoOf e m) := by
  intro l l' hl
  have h1 : L.normalizerMonoidHom m l = l' := Subtype.ext (by simpa using hl)
  have hβ : conjEquiv5 (rhoOf e m) = MulAut.congr e (L.normalizerMonoidHom m) := by
    simp [rhoOf]
  have h3 : MulAut.congr e (L.normalizerMonoidHom m) (e l) = e l' := by
    change e (L.normalizerMonoidHom m (e.symm (e l))) = e l'
    rw [e.symm_apply_apply, h1]
  have h2 := congrArg (fun f : MulAut (alternatingGroup (Fin 5)) =>
    ((f (e l) : alternatingGroup (Fin 5)) : Perm (Fin 5))) hβ
  simp only [conjEquiv5_apply, h3] at h2
  exact h2.symm

theorem eq_of_transports (e : L ≃* alternatingGroup (Fin 5)) {m : G}
    (hm : m ∈ normalizer (L : Set G)) {σ τ : Perm (Fin 5)}
    (hσ : Transports (e : L →* alternatingGroup (Fin 5)) m σ)
    (hτ : Transports (e : L →* alternatingGroup (Fin 5)) m τ) : σ = τ := by
  apply perm_eq_of_conj_eq
  intro g
  obtain ⟨l, rfl⟩ := e.surjective g
  have hl' : m * l * m⁻¹ ∈ L := (mem_normalizer_iff.mp hm l).mp l.2
  have h1 := hσ l ⟨_, hl'⟩ rfl
  have h2 := hτ l ⟨_, hl'⟩ rfl
  exact h1.symm.trans h2

theorem rhoOf_ker (e : L ≃* alternatingGroup (Fin 5)) :
    (rhoOf e).ker = (centralizer (L : Set G)).subgroupOf (normalizer (L : Set G)) := by
  rw [← Subgroup.normalizerMonoidHom_ker]
  ext m
  simp only [MonoidHom.mem_ker, rhoOf, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff]

theorem rhoOf_apply_of_mem (e : L ≃* alternatingGroup (Fin 5)) {l : G} (hl : l ∈ L) :
    rhoOf e ⟨l, Subgroup.le_normalizer hl⟩ = ((e ⟨l, hl⟩ : alternatingGroup (Fin 5)) :
      Perm (Fin 5)) := by
  have h1 : Transports (e : L →* alternatingGroup (Fin 5)) l
      (rhoOf e ⟨l, Subgroup.le_normalizer hl⟩) := rhoOf_transports e ⟨l, Subgroup.le_normalizer hl⟩
  refine eq_of_transports e (Subgroup.le_normalizer hl) h1 ?_
  intro l₁ l₁' h
  have : (⟨l, hl⟩ : L) * l₁ * (⟨l, hl⟩ : L)⁻¹ = l₁' := Subtype.ext (by simpa using h)
  rw [← this]
  simp

end Rho

end CFSG.OddStandard
