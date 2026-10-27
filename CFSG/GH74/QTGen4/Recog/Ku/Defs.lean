module

public import CFSG.Quasithin.Recognition.HSType15a
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.Quasithin.Vol2.Ch6Semilinear
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.HSType
open scoped IsMulCommutative

variable {G : Type} [Group G]

abbrev kuR (T M : Subgroup G) : Subgroup G := T ⊓ oTwoUpper M

abbrev kuV2 (T M : Subgroup G) : Subgroup G :=
  pCoreOf 2 M ⊓ Subgroup.centralizer (kuR T M : Set G)

abbrev kuW (P H : Subgroup G) : Subgroup G := ⁅P, pCoreOf 2 H⁆

abbrev kuA (P H : Subgroup G) : Subgroup G :=
  pCoreOf 2 H ⊓ Subgroup.centralizer (kuW P H : Set G)

abbrev kuN (P H : Subgroup G) : Subgroup G := Subgroup.normalizer (kuA P H : Set G)

structure KuA6Model (E W V2 N : Subgroup G) (z : G) where
  Φ : SpV → G
  π : ↥N →* Equiv.Perm (Fin 6)
  mem : ∀ v, Φ v ∈ E
  inj : Function.Injective Φ
  add : ∀ v w, Φ (v + w) = Φ v * Φ w
  surj : ∀ x ∈ E, ∃ v, Φ v = x
  e0 : Φ (spE 0) = z
  polar : ∀ v, Φ v ∈ W ↔ spForm (spE 0) v = 0
  v2 : ∀ v, Φ v ∈ V2 ↔ InV2m v
  π_alt : ∀ n, π n ∈ alternatingGroup (Fin 6)
  π_surj : ∀ σ ∈ alternatingGroup (Fin 6), ∃ n, π n = σ
  ker : ∀ n : ↥N, π n = 1 ↔ (n : G) ∈ E
  act : ∀ (n : ↥N) (v : SpV), (n : G) * Φ v * (n : G)⁻¹ = Φ (actS6 (π n) v)

@[expose] def KuA6Model.pre {E W V2 N : Subgroup G} {z : G} (Ψ : KuA6Model E W V2 N z)
    (X : Subgroup (Equiv.Perm (Fin 6))) : Subgroup G :=
  (X.comap Ψ.π).map N.subtype

abbrev KuA6Model.L2 {E W V2 N : Subgroup G} {z : G} (Ψ : KuA6Model E W V2 N z) : Subgroup G :=
  Ψ.pre lamS

end CFSG.GH74.QTGen4.Ku
