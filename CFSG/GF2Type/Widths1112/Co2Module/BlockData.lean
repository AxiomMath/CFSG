module

public import CFSG.GF2Type.Widths1112.Co2Module.Gluing

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Widths1112.Co2Module

open Finset

structure BlockData {Γ : Type*} [Group Γ] (ι : AddChar F3Vec Γ) where
  n : Fin 2 → Γ
  An : Fin 2 → Matrix (Fin 4) (Fin 4) (ZMod 3)
  hn : ∀ s, ConjAct ι (n s) (An s)
  cls : F3Vec → Fin 2
  h0 : (lineReps.filter fun w => cls w = 0).card = 30
  h1 : (lineReps.filter fun w => cls w = 1).card = 10
  horbit : ∀ w ∈ lineReps, ∀ w' ∈ lineReps, cls w = cls w' → Relation.EqvGen
    (fun a b : F3Vec => ∃ s, ∃ c : ZMod 3, c ≠ 0 ∧ Matrix.vecMul b (An s) = c • a) w w'
  w₁ : F3Vec
  v₀ : F3Vec
  hw₁R : w₁ ∈ lineReps
  hw₁cls : cls w₁ = 1
  hv₀ : w₁ ⬝ᵥ v₀ ≠ 0
  w : Fin 10 → F3Vec
  hwinj : Function.Injective w
  hwR : ∀ i, w i ∈ lineReps
  hwcls : ∀ i, cls (w i) = 1
  r : Fin 10 → Γ
  Ar : Fin 10 → Matrix (Fin 4) (Fin 4) (ZMod 3)
  cr : Fin 10 → ZMod 3
  hr : ∀ i, ConjAct ι (r i) (Ar i)
  hcr : ∀ i, cr i ≠ 0
  hwA : ∀ i, Matrix.vecMul (w i) (Ar i) = cr i • w₁
  t : Γ
  At : Matrix (Fin 4) (Fin 4) (ZMod 3)
  ct : ZMod 3
  ht : ConjAct ι t At
  ht2 : t * t = 1
  hct : ct ≠ 0
  hwt : Matrix.vecMul w₁ At = ct • w₁
  p : Fin 5 → Γ
  hpstab : ∀ j, p j ∈ stabSubgroup ι w₁
  hp2 : ∀ j, ∃ k : ℕ, p j ^ 2 ^ k = 1
  m : Fin 8 → Γ
  hmn : ∀ s, m (iN s) = n s
  Am : Fin 8 → Matrix (Fin 4) (Fin 4) (ZMod 3)
  hm : ∀ k, ConjAct ι (m k) (Am k)
  σ : Fin 8 → Fin 10 → Fin 10
  u : Fin 8 → Fin 10 → Fin 2 → F3Vec
  ε : Fin 8 → Fin 10 → Fin 2 → ℕ
  pp : Fin 8 → Fin 10 → Fin 2 → Γ
  hpp : ∀ (k : Fin 8) (i : Fin 10) (j : Fin 2), pp k i j ∈ Subgroup.closure (Set.range p)
  hdec : ∀ (k : Fin 8) (i : Fin 10) (j : Fin 2),
    m k * r i * ι v₀ ^ (j : ℕ) = r (σ k i) * ι (u k i j) * t ^ ε k i j * pp k i j
  Ninf : Subgroup Γ
  hNnorm : Ninf ≤ normSubgroup ι
  hNperf : Ninf ≤ ⁅Ninf, Ninf⁆
  hy : ∀ k : Fin 3, m (iY k) ∈ Ninf
  hz : ∀ k : Fin 3, m (iZ k) ∈ Ninf
  g : Γ
  hg3 : g ^ 3 = 1
  hzdef : ∀ k : Fin 3, m (iZ k) = g * m (iY k) * g⁻¹
  hgen : Subgroup.closure ({n 0, n 1, g} : Set Γ) = ⊤
  tw : Fin 8 → List (Fin 2 × ℕ)
  kk : Fin 8 → ℕ
  hrel : ∀ j, (wordProd n (tw j) * g) ^ kk j = 1
  X0 : Fin 2 → Matrix (Fin 22) (Fin 22) (ZMod 2)
  M0 : Matrix (Fin 22) (Fin 22) (ZMod 2)
  hEnum : ∀ (θ : Fin 2 → Matrix (Fin 2) (Fin 2) (ZMod 2)) (M : Matrix (Fin 22) (Fin 22) (ZMod 2)),
    (∀ k : Fin 3, M * Xfin 1 (σ (iY k)) (cfTab w₁ v₀ (u (iY k))) =
      Xfin 1 (σ (iZ k)) (cfTab w₁ v₀ (u (iZ k))) * M) →
    M ^ 3 = 1 →
    (∀ j, (wordProd (fun s => Xfin (θ s) (σ (iN s)) (cfTab w₁ v₀ (u (iN s)))) (tw j) * M) ^
      kk j = 1) →
    ∃ S : Matrix (Fin 2) (Fin 2) (ZMod 2), IsUnit S ∧
      (∀ s, Qfin S * Xfin (θ s) (σ (iN s)) (cfTab w₁ v₀ (u (iN s))) = X0 s * Qfin S) ∧
      Qfin S * M = M0 * Qfin S

end CFSG.GF2Type.Widths1112.Co2Module
