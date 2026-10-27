module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaHAutModel
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3DC2

public noncomputable section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaHAut

open CFSG.Fischer Subgroup CFSG.Blueprint


variable {G : Type} [Group G] {L : Subgroup G} {t : G}

@[expose] noncomputable def theta (hHN : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (e : L ≃* T46) : centralizer ({t} : Set G) →* Equiv.Perm (Fin 693) :=
  autT.subtype.comp (autEquiv.symm.toMonoidHom.comp
    ((MulAut.congr e).toMonoidHom.comp (Yamada.autH hHN)))

theorem theta_apply (hHN : centralizer ({t} : Set G) ≤ normalizer (L : Set G)) (e : L ≃* T46)
    (x : centralizer ({t} : Set G)) :
    theta hHN e x = (autEquiv.symm (MulAut.congr e (Yamada.autH hHN x)) : Equiv.Perm (Fin 693)) :=
  rfl

theorem theta_conj (hHN : centralizer ({t} : Set G) ≤ normalizer (L : Set G)) (e : L ≃* T46)
    (x : centralizer ({t} : Set G)) (l l' : L) (hl : (l' : G) = x * l * (x : G)⁻¹) :
    theta hHN e x * (e l : Equiv.Perm (Fin 693)) * (theta hHN e x)⁻¹ = e l' := by
  set φ := MulAut.congr e (Yamada.autH hHN x)
  have h1 := autEquiv_apply (autEquiv.symm φ) (e l)
  rw [MulEquiv.apply_symm_apply] at h1
  rw [theta_apply, ← h1]
  have h2 : Yamada.autH hHN x l = l' := Subtype.ext (by rw [Yamada.autH_apply, hl])
  change ((e (Yamada.autH hHN x (e.symm (e l))) : T46) : Equiv.Perm (Fin 693)) = e l'
  rw [MulEquiv.symm_apply_apply, h2]

theorem theta_of_mem (hHN : centralizer ({t} : Set G) ≤ normalizer (L : Set G)) (e : L ≃* T46)
    (x : centralizer ({t} : Set G)) (hx : (x : G) ∈ L) : theta hHN e x = e ⟨x, hx⟩ := by
  have hφ : MulAut.congr e (Yamada.autH hHN x) = autEquiv ⟨e ⟨x, hx⟩, T46_le_autT (e ⟨x, hx⟩).2⟩ := by
    refine MulEquiv.ext fun g => Subtype.ext ?_
    rw [autEquiv_apply]
    have h2 : ((MulAut.congr e (Yamada.autH hHN x) g : T46) : Equiv.Perm (Fin 693)) =
        e ⟨x * (e.symm g : G) * (x : G)⁻¹, (mem_normalizer_iff.1 (hHN x.2) _).1 (e.symm g).2⟩ := by
      change ((e (Yamada.autH hHN x (e.symm g)) : T46) : Equiv.Perm (Fin 693)) = _
      congr 2
    rw [h2]
    have h3 : (e ⟨x * (e.symm g : G) * (x : G)⁻¹,
        (mem_normalizer_iff.1 (hHN x.2) _).1 (e.symm g).2⟩ : T46) =
          e ⟨x, hx⟩ * g * (e ⟨x, hx⟩)⁻¹ := by
      conv_rhs => rw [← MulEquiv.apply_symm_apply e g]
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
    rw [h3]
    rfl
  rw [theta_apply, hφ, MulEquiv.symm_apply_apply]

theorem thetaSpec_theta [Finite G] {D : ToddParabolic L} (h : Yamada.Setting G L D t)
    (e : L ≃* T46) : ThetaSpec t e (theta h.H_le e) where
  normalizer x := h.H_le x.2
  conj := theta_conj h.H_le e
  apply_of_mem := theta_of_mem h.H_le e
  eq_one_iff x := by
    rw [theta_apply]
    constructor
    · intro h1
      have h2 : autEquiv.symm (MulAut.congr e (Yamada.autH h.H_le x)) = 1 := Subtype.ext h1
      rw [MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff, h.autH_eq_one_iff] at h2
      rw [← h.inf_centralizer_eq]
      exact ⟨h2, x.2⟩
    · intro h1
      have h2 : (x : G) ∈ centralizer (L : Set G) := by
        rw [← h.inf_centralizer_eq] at h1
        exact h1.1
      rw [← h.autH_eq_one_iff] at h2
      rw [h2, map_one, map_one]
      rfl
  mem_autT x := (autEquiv.symm (MulAut.congr e (Yamada.autH h.H_le x))).2


theorem exists_thetaSpec [Finite G] (hset : StandardSetting G L) (hZ : center L = ⊥)
    (hQ : LieModel (L ⧸ center L) .PSU 6 2 1) (htL : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) (e : L ≃* T46) :
    ∃ Θ : centralizer ({t} : Set G) →* Equiv.Perm (Fin 693), ThetaSpec t e Θ :=
  ⟨_, thetaSpec_theta (YamadaSec3.setting_ofMulEquivT46 hset hZ hQ htL ht e) e⟩

end CFSG.EvenSmallLie.UnitarySix.YamadaHAut
