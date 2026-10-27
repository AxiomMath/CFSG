module

public import CFSG.GH74.GLS.C3.Layer1.BackAction
public import CFSG.GH74.GLS.C3.Layer1.BackBasic
public import CFSG.GH74.GLS.C3.Layer1.BackStmt

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1.Back

@[expose] def B_prop43c_six : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x : G) (K M T Q : Subgroup G)
    (hh : Hyp9 x K K M T Q), Prop91Concl K M T Q → Nonempty (kBar K ≃* alternatingGroup (Fin 6)) →
    ¬ IsSylowOf 2 T ⊤ →
    (∀ (u : G) (hu : u ∈ T), u * u = 1 → ∀ e : kBar K ≃* alternatingGroup (Fin 6),
      ∃ σ : Equiv.Perm (Fin 6),
        MulAut.congr e (Back.actHom hh.a.L_normal.2
          ⟨u, hh.a.centralizer_le (hh.a.sylowT.le hu)⟩) =
          MulAut.conjNormal (H := alternatingGroup (Fin 6)) σ) →
    ∃ e : kBar K ≃* alternatingGroup (Fin 6), ∀ (t : G) (ht : t ∈ T), ∃ σ : Equiv.Perm (Fin 6),
      MulAut.congr e (Back.actHom hh.a.L_normal.2
        ⟨t, hh.a.centralizer_le (hh.a.sylowT.le ht)⟩) =
        MulAut.conjNormal (H := alternatingGroup (Fin 6)) σ

@[expose] def B_L42c_six : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x : G) (K M T Q : Subgroup G)
    (hh : Hyp9 x K K M T Q), Prop91Concl K M T Q → Nonempty (kBar K ≃* alternatingGroup (Fin 6)) →
    ¬ IsSylowOf 2 T ⊤ →
    (∀ (u : G) (hu : u ∈ T), u * u = 1 → ∀ e : kBar K ≃* alternatingGroup (Fin 6),
      ∃ σ : Equiv.Perm (Fin 6),
        MulAut.congr e (Back.actHom hh.a.L_normal.2
          ⟨u, hh.a.centralizer_le (hh.a.sylowT.le hu)⟩) =
          MulAut.conjNormal (H := alternatingGroup (Fin 6)) σ) →
    T ≤ Subgroup.closure {u : G | u ∈ T ∧ u * u = 1}

end CFSG.GH74.GLS.C3.Layer1.Bk
