module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyPair
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFySignB

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup

@[expose] def embD : DihedralGroup 4 →* HModel where
  toFun d := (d, 1, 1)
  map_one' := rfl
  map_mul' a b := by ext <;> simp

@[expose] def embS : Equiv.Perm (Fin 5) →* HModel where
  toFun σ := (1, 1, σ)
  map_one' := rfl
  map_mul' a b := by ext <;> simp

@[expose] def embDS : DihedralGroup 4 × Equiv.Perm (Fin 5) →* HModel where
  toFun p := (p.1, 1, p.2)
  map_one' := rfl
  map_mul' a b := by ext <;> simp

variable {G : Type} [Group G] [Finite G] {t r : G} {Θ : HModel →* G}

theorem FyConf.Phi_split (h : FyConf t r Θ) (d : DihedralGroup 4) (c : Z3)
    (σ : Equiv.Perm (Fin 5)) : h.Phi (d, c, σ) = h.Phi (d, 1, 1) * h.Phi (1, 1, σ) := by
  have hcz : h.Phi (1, c, 1) = 1 := (h.Phi_eq_one_iff _).2 ⟨rfl, rfl⟩
  have : ((d, c, σ) : HModel) = (d, 1, 1) * (1, c, 1) * (1, 1, σ) := by ext <;> simp
  rw [this, map_mul, map_mul, hcz, mul_one]

theorem FyConf.injD (h : FyConf t r Θ) : Function.Injective (h.Phi.comp embD) := by
  rw [injective_iff_map_eq_one]
  intro d hd
  exact ((h.Phi_eq_one_iff (embD d)).1 hd).1

theorem FyConf.injS (h : FyConf t r Θ) : Function.Injective (h.Phi.comp embS) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  exact ((h.Phi_eq_one_iff (embS σ)).1 hσ).2

theorem FyConf.injDS (h : FyConf t r Θ) : Function.Injective (h.Phi.comp embDS) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨d, σ⟩ hp
  have := (h.Phi_eq_one_iff (embDS (d, σ))).1 hp
  exact Prod.ext this.1 this.2

@[expose] noncomputable def FyConf.subD (h : FyConf t r Θ) : Subgroup (RedX r) :=
  (h.Phi.comp embD).range

@[expose] noncomputable def FyConf.subS (h : FyConf t r Θ) : Subgroup (RedX r) :=
  (h.Phi.comp embS).range

@[expose] noncomputable def FyConf.eD (h : FyConf t r Θ) : h.subD ≃* DihedralGroup 4 :=
  (MonoidHom.ofInjective h.injD).symm

@[expose] noncomputable def FyConf.eS (h : FyConf t r Θ) : h.subS ≃* Equiv.Perm (Fin 5) :=
  (MonoidHom.ofInjective h.injS).symm

theorem FyConf.mem_subD (h : FyConf t r Θ) (d : DihedralGroup 4) : h.Phi (d, 1, 1) ∈ h.subD :=
  ⟨d, rfl⟩

theorem FyConf.mem_subS (h : FyConf t r Θ) (σ : Equiv.Perm (Fin 5)) :
    h.Phi (1, 1, σ) ∈ h.subS := ⟨σ, rfl⟩

theorem FyConf.eD_apply (h : FyConf t r Θ) (d : DihedralGroup 4) :
    h.eD ⟨h.Phi (d, 1, 1), h.mem_subD d⟩ = d := by
  refine (MulEquiv.symm_apply_eq _).2 ?_
  exact Subtype.ext rfl

theorem FyConf.eS_apply (h : FyConf t r Θ) (σ : Equiv.Perm (Fin 5)) :
    h.eS ⟨h.Phi (1, 1, σ), h.mem_subS σ⟩ = σ := by
  refine (MulEquiv.symm_apply_eq _).2 ?_
  exact Subtype.ext rfl

theorem FyConf.localPair (h : FyConf t r Θ) :
    LocalPair h.tauX h.subD h.subS h.eD h.eS where
  tau_sq := h.tauX_sq
  tau_mem := ⟨h.mem_subD _, h.eD_apply _⟩
  comm := by
    rintro _ ⟨d, rfl⟩ _ ⟨σ, rfl⟩
    exact (h.Phi_comm_iff (embD d) (embS σ)).2 ⟨by simp [embD, embS], by simp [embD, embS]⟩
  inf := by
    rintro x ⟨d, rfl⟩ ⟨σ, hσ⟩
    have h1 : h.Phi (embD d) * h.Phi (embS σ⁻¹) = 1 := by
      have e1 : h.Phi (embS σ⁻¹) = (h.Phi (embS σ))⁻¹ := map_inv (h.Phi.comp embS) σ
      have e2 : h.Phi (embD d) = h.Phi (embS σ) := hσ.symm
      rw [e1, e2]
      exact mul_inv_cancel _
    rw [← map_mul] at h1
    have := ((h.Phi_eq_one_iff _).1 h1).1
    have hd : d = 1 := by simpa [embD, embS] using this
    show h.Phi (embD d) = 1
    simp [hd]
  cent := by
    intro x
    constructor
    · intro hx
      obtain ⟨⟨d, c, σ⟩, rfl⟩ := h.exists_lift x hx
      exact ⟨_, h.mem_subD d, _, h.mem_subS σ, h.Phi_split d c σ⟩
    · rintro ⟨_, ⟨d, rfl⟩, _, ⟨σ, rfl⟩, rfl⟩
      have h1 := h.Phi_comm_tau (embD d)
      have h2 := h.Phi_comm_tau (embS σ)
      calc h.Phi (embD d) * h.Phi (embS σ) * h.tauX
          = h.Phi (embD d) * (h.Phi (embS σ) * h.tauX) := by group
        _ = h.Phi (embD d) * (h.tauX * h.Phi (embS σ)) := by rw [h2]
        _ = (h.Phi (embD d) * h.tauX) * h.Phi (embS σ) := by group
        _ = (h.tauX * h.Phi (embD d)) * h.Phi (embS σ) := by rw [h1]
        _ = h.tauX * (h.Phi (embD d) * h.Phi (embS σ)) := by group

noncomputable def FyConf.centEquiv (h : FyConf t r Θ) :
    ↥(centralizer ({h.tauX} : Set (RedX r))) ≃* DihedralGroup 4 × Equiv.Perm (Fin 5) := by
  have hr : centralizer ({h.tauX} : Set (RedX r)) = (h.Phi.comp embDS).range := by
    rw [h.cent_eq_range]
    ext x
    constructor
    · rintro ⟨⟨d, c, σ⟩, rfl⟩
      refine ⟨(d, σ), ?_⟩
      show h.Phi (d, 1, σ) = h.Phi (d, c, σ)
      rw [h.Phi_split d 1 σ, h.Phi_split d c σ]
    · rintro ⟨p, rfl⟩
      exact ⟨embDS p, rfl⟩
  exact (MulEquiv.subgroupCongr hr).trans (MonoidHom.ofInjective h.injDS).symm

end CFSG.EvenSporadicStandard.TwoHS
