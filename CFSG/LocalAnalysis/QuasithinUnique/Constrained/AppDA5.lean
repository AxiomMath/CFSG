module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppDCfg
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCD0
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Block

public section

namespace CFSG.QuasithinUnique.AppD

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Delta5 Equiv

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

@[expose] def piSOfCfg (C : AppC.Cfg T M H S L) : PiS S (blockU L) where
  β := C.P.β
  π := C.P.π.comp (Subgroup.inclusion C.hSN)
  hSU := fun _ hy => C1.mem_normalizer_blockU (C.hSN hy)
  hcomp := fun y u u' h => C.P.hcomp (Subgroup.inclusion C.hSN y) u u' h
  hker := fun y => C.P.hker (Subgroup.inclusion C.hSN y)

theorem piSOfCfg_im (C : AppC.Cfg T M H S L) {K : Subgroup G} (hK : K ≤ S) :
    (piSOfCfg C).im K = C.P.im K := by
  ext g
  rw [PiS.mem_im, C.P.mem_im]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, C.hSN y.2⟩, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hK hy⟩, hy, rfl⟩

@[expose] def GCfg.ofCfg (C : AppC.Cfg T M H S L) : GCfg T M H S L where
  hcs := C.hcs
  U := blockU L
  hUdef := (A5.blockU0_eq_blockU C.hj).symm
  P := piSOfCfg C
  hB := by rw [piSOfCfg_im C (K := baum S) inf_le_left]; exact C.hB
  hS := by rw [piSOfCfg_im C le_rfl]; exact C.hS
  hUQ := C.hUQ
  hQ := C.hQ
  hUD := C.U_inf_D
  hQeq := C.Q_eq
  hU1 := le_rfl

end CFSG.QuasithinUnique.AppD
