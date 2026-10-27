module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7RWr

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] {t : G} {P U : Subgroup G}

@[expose] def Wr7.prodHom (h : Wr7 t P U) : ↥U × ↥(conjSub t U) →* ↥P where
  toFun p := ⟨(p.1 : G) * (p.2 : G), h.mul_mem' p.1.2 p.2.2⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' p q := by
    apply Subtype.ext
    have hc : ((p.2 : ↥(conjSub t U)) : G) * ((q.1 : ↥U) : G) =
        ((q.1 : ↥U) : G) * ((p.2 : ↥(conjSub t U)) : G) :=
      (h.direct.2.2 q.1 q.1.2 p.2 p.2.2).symm
    show ((p.1 : G) * (q.1 : G)) * ((p.2 : G) * (q.2 : G)) =
      ((p.1 : G) * (p.2 : G)) * ((q.1 : G) * (q.2 : G))
    calc ((p.1 : G) * (q.1 : G)) * ((p.2 : G) * (q.2 : G))
        = (p.1 : G) * (((q.1 : G) * (p.2 : G)) * (q.2 : G)) := by group
      _ = (p.1 : G) * (((p.2 : G) * (q.1 : G)) * (q.2 : G)) := by rw [← hc]
      _ = ((p.1 : G) * (p.2 : G)) * ((q.1 : G) * (q.2 : G)) := by group

theorem Wr7.prodHom_bijective (h : Wr7 t P U) : Function.Bijective h.prodHom := by
  constructor
  · intro p q hpq
    have hG : ((p.1 : G) * (p.2 : G)) = ((q.1 : G) * (q.2 : G)) := by
      simpa [Wr7.prodHom] using congrArg (fun z : ↥P => (z : G)) hpq
    obtain ⟨h1, h2⟩ := h.unique p.1.2 q.1.2 p.2.2 q.2.2 hG
    exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
  · rintro ⟨x, hx⟩
    obtain ⟨u, hu, v, hv, rfl⟩ := h.decomp hx
    exact ⟨(⟨u, hu⟩, ⟨v, hv⟩), Subtype.ext rfl⟩

@[expose] noncomputable def Wr7.prodEquiv (h : Wr7 t P U) : ↥U × ↥(conjSub t U) ≃* ↥P :=
  MulEquiv.ofBijective h.prodHom h.prodHom_bijective

@[expose] noncomputable def Wr7.proj1 (h : Wr7 t P U) : ↥P →* ↥U :=
  (MonoidHom.fst _ _).comp h.prodEquiv.symm.toMonoidHom

@[expose] noncomputable def Wr7.proj2 (h : Wr7 t P U) : ↥P →* ↥(conjSub t U) :=
  (MonoidHom.snd _ _).comp h.prodEquiv.symm.toMonoidHom

theorem Wr7.proj_mul (h : Wr7 t P U) (x : ↥P) :
    ((h.proj1 x : ↥U) : G) * ((h.proj2 x : ↥(conjSub t U)) : G) = (x : G) := by
  have hx : h.prodHom (h.prodEquiv.symm x) = x := by
    rw [Wr7.prodEquiv]
    exact MulEquiv.ofBijective_apply_symm_apply h.prodHom h.prodHom_bijective
  have hx' := congrArg (fun z : ↥P => (z : G)) hx
  change ((h.prodEquiv.symm x).1 : G) * ((h.prodEquiv.symm x).2 : G) = (x : G)
  simpa [Wr7.prodHom] using hx'

theorem Wr7.proj_of_mul (h : Wr7 t P U) {u v : G} (hu : u ∈ U) (hv : v ∈ conjSub t U) :
    ((h.proj1 ⟨u * v, h.mul_mem' hu hv⟩ : ↥U) : G) = u ∧
      ((h.proj2 ⟨u * v, h.mul_mem' hu hv⟩ : ↥(conjSub t U)) : G) = v := by
  have hs : h.prodEquiv.symm ⟨u * v, h.mul_mem' hu hv⟩ = (⟨u, hu⟩, ⟨v, hv⟩) := by
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext rfl
  constructor
  · change ((h.prodEquiv.symm ⟨u * v, h.mul_mem' hu hv⟩).1 : G) = u
    rw [hs]
  · change ((h.prodEquiv.symm ⟨u * v, h.mul_mem' hu hv⟩).2 : G) = v
    rw [hs]

@[expose] noncomputable def Wr7.centMap (h : Wr7 t P U) :
    ↥U →* ↥(P ⊓ centralizer ({t} : Set G)) where
  toFun u := ⟨(u : G) * (t * (u : G) * t⁻¹), (h.mem_cent).mpr ⟨u, u.2, rfl⟩⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' p q := by
    apply Subtype.ext
    have hmem : t * (p : G) * t⁻¹ ∈ conjSub t U := (mem_conjSub_iff' t U _).mpr ⟨p, p.2, rfl⟩
    have hc : t * (p : G) * t⁻¹ * (q : G) = (q : G) * (t * (p : G) * t⁻¹) :=
      (h.direct.2.2 q q.2 _ hmem).symm
    show ((p : G) * (q : G)) * (t * ((p : G) * (q : G)) * t⁻¹) =
      ((p : G) * (t * (p : G) * t⁻¹)) * ((q : G) * (t * (q : G) * t⁻¹))
    calc ((p : G) * (q : G)) * (t * ((p : G) * (q : G)) * t⁻¹)
        = (p : G) * (q : G) * (t * (p : G) * t⁻¹) * (t * (q : G) * t⁻¹) := by group
      _ = (p : G) * ((q : G) * (t * (p : G) * t⁻¹)) * (t * (q : G) * t⁻¹) := by group
      _ = (p : G) * (t * (p : G) * t⁻¹ * (q : G)) * (t * (q : G) * t⁻¹) := by rw [hc]
      _ = ((p : G) * (t * (p : G) * t⁻¹)) * ((q : G) * (t * (q : G) * t⁻¹)) := by group

theorem Wr7.centMap_bijective (h : Wr7 t P U) : Function.Bijective h.centMap := by
  constructor
  · rw [injective_iff_map_eq_one]
    intro u hu
    have hG : (u : G) * (t * (u : G) * t⁻¹) = 1 := by
      simpa [Wr7.centMap] using congrArg (fun z : ↥(P ⊓ centralizer ({t} : Set G)) => (z : G)) hu
    have hinv : (u : G)⁻¹ = t * (u : G) * t⁻¹ := (mul_eq_one_iff_inv_eq.mp hG)
    have hmemU : (u : G)⁻¹ ∈ U := U.inv_mem u.2
    have hmemC : (u : G)⁻¹ ∈ conjSub t U :=
      (mem_conjSub_iff' t U _).mpr ⟨u, u.2, hinv⟩
    have hbot : (u : G)⁻¹ ∈ (⊥ : Subgroup G) := by
      rw [← h.direct.2.1]
      exact ⟨hmemU, hmemC⟩
    exact Subtype.ext (inv_eq_one.mp (Subgroup.mem_bot.mp hbot))
  · rintro ⟨y, hy⟩
    obtain ⟨u, hu, rfl⟩ := h.mem_cent.mp hy
    exact ⟨⟨u, hu⟩, Subtype.ext rfl⟩

@[expose] noncomputable def Wr7.centEquiv (h : Wr7 t P U) :
    ↥U ≃* ↥(P ⊓ centralizer ({t} : Set G)) :=
  MulEquiv.ofBijective h.centMap h.centMap_bijective

theorem Wr7.centEquiv_apply (h : Wr7 t P U) (u : ↥U) :
    ((h.centEquiv u : ↥(P ⊓ centralizer ({t} : Set G))) : G) = (u : G) * (t * (u : G) * t⁻¹) :=
  rfl

end CFSG.OddStandard.HigherRank.YamadaG23
