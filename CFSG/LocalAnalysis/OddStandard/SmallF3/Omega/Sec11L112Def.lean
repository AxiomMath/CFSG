module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L112Pm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Ctx

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

@[expose] def sec11V4 : Finset (Equiv.Perm (Fin 6)) :=
  {1, Equiv.swap 2 3 * Equiv.swap 4 5, Equiv.swap 2 4 * Equiv.swap 3 5,
    Equiv.swap 2 5 * Equiv.swap 3 4}

structure Sec11Model (t : G) (L S : Subgroup G) (z : G) (K1 K2 T : Subgroup G)
    (Alt : Subgroup (Equiv.Perm (Fin 6))) (φ : (Fin 6 → ZMod 2) → G) : Prop where
  perm : Sec11Perm (secA t S L) (secM t S L) Alt φ
  alt : Alt = alternatingGroup (Fin 6) ∨ Alt = ⊤
  t_eq : t = φ (Pi.single 0 1)
  tz_eq : t * z = φ (Pi.single 1 1)
  mem_B : ∀ v, φ v ∈ secB S L ↔ ∑ i, v i = 0
  mem_Q : ∀ v, φ v ∈ secQ K1 K2 ↔ (∑ i, v i = 0 ∧ v 0 = v 1)
  Q_act : ∀ q ∈ secQ K1 K2, ∃ s ∈ sec11V4, ∀ v, q * φ v * q⁻¹ = φ (permVec s v)
  Q_act_surj : ∀ s ∈ sec11V4, ∃ q ∈ secQ K1 K2, ∀ v, q * φ v * q⁻¹ = φ (permVec s v)
  T_set : ∀ x ∈ T, (perm.rho x 0 = 0 ∧ perm.rho x 1 = 1) ∨ (perm.rho x 0 = 1 ∧ perm.rho x 1 = 0)
  cenTA : ∀ c ∈ T, (∀ a ∈ secA t S L, c * a = a * c) → c ∈ secA t S L
  card_T : (Alt = ⊤ → Nat.card ↥T = 512) ∧ (Alt ≠ ⊤ → Nat.card ↥T = 256)

end CFSG.OddStandard.SmallF3.Omega
