module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84G4Dt

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Open

variable {G : Type} [Group G] [Finite G] {t : G} {E T T1 T2 V1 V2 F1 F2 : Subgroup G}

theorem sec8t84g4_J0_eq (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2) :
    (E ⊔ (F1 ⊔ F2)) ⊓ centralizer ({t} : Set G) =
      (E ⊓ centralizer ({t} : Set G)) ⊔ ((F1 ⊔ F2) ⊓ centralizer ({t} : Set G)) := by
  rw [← sec8t84g4_diag_U1 D, sec8t84g4_diagSub_sup D.wr D.mod1.V_le D.mod1.F_le,
    sec8t84g4_diag_V1 D, sec8t84g4_diag_F1 D]

theorem sec8t84g4_map_cent_inf {γ : G} (hγt : γ * t = t * γ) (X : Subgroup G) :
    (X ⊓ centralizer ({t} : Set G)).map (MulAut.conj γ).toMonoidHom =
      X.map (MulAut.conj γ).toMonoidHom ⊓ centralizer ({t} : Set G) := by
  have hC : (centralizer ({t} : Set G)).map (MulAut.conj γ).toMonoidHom =
      centralizer ({t} : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr hγt))
  rw [Subgroup.map_inf _ _ _ (MulAut.conj γ).injective, hC]

theorem sec8t84g4_mem_normalizer_sup {X Y : Subgroup G} {d : G}
    (hX : d ∈ normalizer (X : Set G)) (hY : d ∈ normalizer (Y : Set G)) :
    d ∈ normalizer ((X ⊔ Y : Subgroup G) : Set G) :=
  Subgroup.inf_normalizer_le_normalizer_sup X Y (Subgroup.mem_inf.mpr ⟨hX, hY⟩)

theorem sec8t84g4_inf_cent_mul {H : Subgroup G} {a k : G} (h : ∀ x ∈ H, x * k = k * x) :
    H ⊓ centralizer ({a * k} : Set G) = H ⊓ centralizer ({a} : Set G) := by
  ext x
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨hx, hc⟩
    refine ⟨hx, ?_⟩
    have hxk := h x hx
    have e : (x * a) * k = (a * x) * k := by
      calc (x * a) * k = x * (a * k) := by rw [mul_assoc]
        _ = (a * k) * x := hc
        _ = a * (k * x) := by rw [mul_assoc]
        _ = a * (x * k) := by rw [hxk]
        _ = (a * x) * k := by rw [mul_assoc]
    exact mul_right_cancel e
  · rintro ⟨hx, hc⟩
    refine ⟨hx, ?_⟩
    have hxk := h x hx
    calc x * (a * k) = (x * a) * k := by rw [mul_assoc]
      _ = (a * x) * k := by rw [hc]
      _ = a * (x * k) := by rw [mul_assoc]
      _ = a * (k * x) := by rw [hxk]
      _ = (a * k) * x := by rw [mul_assoc]

theorem sec8t84g4_klein_transfer (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2) {γ : G}
    (hγt : γ * t = t * γ) (hγN : γ ∈ normalizer ((V1 ⊔ F1 : Subgroup G) : Set G))
    (hK : IsElemAb2
      (((E ⊔ (F1 ⊔ F2)) ⊓ centralizer ({t} : Set G)) ⊓ centralizer ({γ} : Set G)) 2) :
    IsElemAb2 ((V1 ⊔ F1) ⊓ centralizer ({γ} : Set G)) 2 ∧
      IsElemAb2 ((V2 ⊔ F2) ⊓ centralizer ({γ} : Set G)) 2 := by
  have hU1 : V1 ⊔ F1 ≤ T1 := (sec8t84g4_U_le D).1
  have hle : (V1 ⊔ F1) ⊓ centralizer ({γ} : Set G) ≤ T1 := inf_le_left.trans hU1
  have hd : sec8t84g4_diagSub D.wr ((V1 ⊔ F1) ⊓ centralizer ({γ} : Set G)) =
      ((E ⊔ (F1 ⊔ F2)) ⊓ centralizer ({t} : Set G)) ⊓ centralizer ({γ} : Set G) := by
    rw [sec8t84g4_diagSub_cent D.wr hU1 hγt hγN, sec8t84g4_diag_U1 D]
  have h1 : IsElemAb2 ((V1 ⊔ F1) ⊓ centralizer ({γ} : Set G)) 2 := by
    refine ⟨sec8t84g4_isElemAbelian_of_diagSub D.wr hle ?_, ?_⟩
    · rw [hd]
      exact hK.1
    · rw [← sec8t84g4_card_diagSub D.wr hle, hd]
      exact hK.2
  obtain ⟨hc1, hc2⟩ :=
    sec8t84g4_swap_cent_pair (sec8t84g4_U_swap D).1 (sec8t84g4_U_swap D).2 hγt
  exact ⟨h1, sec8t84g4_elemAb2_swap D.t_sq hc1 hc2 h1⟩

end CFSG.OddStandard.SmallF3.Omega
