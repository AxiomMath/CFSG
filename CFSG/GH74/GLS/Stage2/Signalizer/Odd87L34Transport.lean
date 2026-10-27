module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Open
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87SubSecTransport

public section

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

@[expose] def L34AutOn (Y : Type) [Group Y] [Finite Y] : Prop :=
  ∀ (α : MulAut Y) (p : ℕ) (X : Subgroup (MulAut Y)), AutCfg Y α p X →
      Nat.card ↥X = 3 ∧ X ⊓ innSub Y = ⊥ ∧ α ∉ innSub Y ⊔ X ∧ IsPGL3Four ↥(innSub Y ⊔ X) ∧
      innSub Y ⊓ centralizer ({α} : Set (MulAut Y)) = innSub Y ⊓ centralizer (X : Set (MulAut Y)) ∧
      IVK.IsL2 ↥(innSub Y ⊓ centralizer ({α} : Set (MulAut Y))) (fun q => q = 4) ∧
      (innSub Y ⊔ X ⊔ zpowers α) ⊓
          centralizer ((innSub Y ⊓ centralizer ({α} : Set (MulAut Y)) : Subgroup (MulAut Y)) :
            Set (MulAut Y)) = X ⊔ zpowers α

section Transport

theorem congr_conj {Y Y' : Type} [Group Y] [Group Y'] (ψ : Y ≃* Y') (y : Y) :
    MulAut.congr ψ (MulAut.conj y) = MulAut.conj (ψ y) := by
  ext x
  simp [MulAut.conj_apply]

theorem map_innSub {Y Y' : Type} [Group Y] [Group Y'] (ψ : Y ≃* Y') :
    (innSub Y).map (MulAut.congr ψ).toMonoidHom = innSub Y' := by
  ext σ
  constructor
  · rintro ⟨τ, ⟨y, rfl⟩, rfl⟩
    exact ⟨ψ y, (congr_conj ψ y).symm⟩
  · rintro ⟨y', rfl⟩
    refine ⟨MulAut.conj (ψ.symm y'), ⟨ψ.symm y', rfl⟩, ?_⟩
    show MulAut.congr ψ (MulAut.conj (ψ.symm y')) = MulAut.conj y'
    rw [congr_conj, MulEquiv.apply_symm_apply]

theorem autCfg_map {Y Y' : Type} [Group Y] [Group Y'] (ψ : Y ≃* Y') {α : MulAut Y} {p : ℕ}
    {X : Subgroup (MulAut Y)} (h0 : AutCfg Y α p X) :
    AutCfg Y' (MulAut.congr ψ α) p (X.map (MulAut.congr ψ).toMonoidHom) where
  prime := h0.prime
  odd := h0.odd
  alpha_sq := by rw [← map_mul, h0.alpha_sq, map_one]
  alpha_ne := fun h => h0.alpha_ne ((MulAut.congr ψ).injective (by rw [h, map_one]))
  pgroup := h0.pgroup.map _
  ne_bot := fun hb => h0.ne_bot
    ((Subgroup.map_eq_bot_iff_of_injective X (MulAut.congr ψ).injective).1 hb)
  alpha_norm := by
    rw [← Transport.map_normalizer]
    exact Subgroup.mem_map_of_mem _ h0.alpha_norm
  cent_norm := by
    intro k' hk'
    have hk : MulAut.conj k' = MulAut.congr ψ (MulAut.conj (ψ.symm k')) := by
      rw [congr_conj, MulEquiv.apply_symm_apply]
    rw [hk] at hk' ⊢
    have hcomm : α * MulAut.conj (ψ.symm k') = MulAut.conj (ψ.symm k') * α := by
      apply (MulAut.congr ψ).injective
      rw [map_mul, map_mul]
      exact hk'
    rw [← Transport.map_normalizer]
    exact Subgroup.mem_map_of_mem _ (h0.cent_norm _ hcomm)
  comm := by
    rw [← Transport.map_zpowers, ← Transport.map_commutator, h0.comm]

theorem l34AutOn_of_mulEquiv {Y Y' : Type} [Group Y] [Finite Y] [Group Y'] [Finite Y']
    (ψ : Y ≃* Y') (h : L34AutOn Y') : L34AutOn Y := by
  intro α p X h0
  have key := h (MulAut.congr ψ α) p (X.map (MulAut.congr ψ).toMonoidHom) (autCfg_map ψ h0)
  have hin := map_innSub ψ
  generalize MulAut.congr ψ = Φ at key hin
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := key
  have hinj : Function.Injective Φ.toMonoidHom := Φ.injective
  have hsup : (innSub Y ⊔ X).map Φ.toMonoidHom = innSub Y' ⊔ X.map Φ.toMonoidHom := by
    rw [Transport.map_sup, hin]
  have hJ : (innSub Y ⊓ centralizer ({α} : Set (MulAut Y))).map Φ.toMonoidHom =
      innSub Y' ⊓ centralizer ({Φ α} : Set (MulAut Y')) := by
    rw [Transport.map_inf, hin, Transport.map_centralizer_singleton]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Subgroup.card_map_of_injective hinj]
    exact c1
  · apply (Subgroup.map_eq_bot_iff_of_injective _ hinj).1
    rw [Transport.map_inf, hin]
    exact c2
  · intro hmem
    apply c3
    have := Subgroup.mem_map_of_mem Φ.toMonoidHom hmem
    rw [hsup] at this
    exact this
  · exact Transport.isPGL3Four_of_mulEquiv (Transport.subEquiv Φ hsup).symm c4
  · apply Subgroup.map_injective hinj
    rw [Transport.map_inf, Transport.map_inf, hin, Transport.map_centralizer_singleton,
      Transport.map_centralizer]
    exact c5
  · exact Transport.isL2_of_mulEquiv (Transport.subEquiv Φ hJ).symm c6
  · apply Subgroup.map_injective hinj
    rw [Transport.map_inf, Transport.map_sup, Transport.map_sup, Transport.map_sup,
      Transport.map_zpowers, hin, Transport.map_centralizer, hJ]
    exact c7

end Transport

theorem l34Aut_of_model
    (h : L34AutOn ↥CFSG.ComponentClassification.PSL3Four.S) : L34Aut := by
  intro Y _ _ hY
  obtain ⟨ψ⟩ := CFSG.ComponentClassification.CatFactsSmall.nonempty_equiv_psl34_of_lieModel hY
  exact l34AutOn_of_mulEquiv ψ h

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
