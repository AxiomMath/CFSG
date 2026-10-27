module

public import CFSG.CGT.Stroth77.Arch76Lemma2Kappa

public section

namespace CFSG.CGT.Stroth77.Arch76

@[expose] def al0 : Co × Co := ((0, 2, 0), (0, 0, 2))

@[expose] def bet : Co × Co := ((0, 2, 2), (0, 2, 0))

@[expose] def gam1 : Co × Co := ((0, 0, 2), (0, 2, 0))

@[expose] def gam2 : Co × Co := ((0, 2, 0), (0, 2, 2))

@[expose] def gam3 : Co × Co := ((0, 2, 2), (0, 0, 2))

theorem Luv_al0 : Luv al0 = al0 := by decide
theorem Lu_al0 : Lu al0 = al0 := by decide
theorem Lρ_al0 : Lρ al0 = al0 := by decide
theorem Luv_bet : Luv bet = bet := by decide
theorem Lρ_bet : Lρ bet = bet := by decide
theorem Lu_bet_add : Lu bet + bet = al0 := by decide
theorem Luv_gam1 : Luv gam1 = gam1 := by decide
theorem Lt_gam1 : Lt gam1 = gam1 := by decide
theorem Lρ_gam1 : Lρ gam1 = gam2 := by decide
theorem Lρ_gam2 : Lρ gam2 = gam3 := by decide
theorem gam1_add_gam2 : gam1 + gam2 = gam3 := by decide
theorem al0_ne_zero : al0 ≠ 0 := by decide
theorem gam1_ne_zero : gam1 ≠ 0 := by decide

@[expose] def nρ (r : Co × Co) : Co × Co := Lρ r + Lρ (Lρ r)

set_option synthInstance.maxSize 4096 in
theorem gam1_mem_words : ∀ m : Co × Co, 2 • m.1 = 0 → 2 • m.2 = 0 → Lρ m ≠ m →
    gam1 = nρ m ∨ gam1 = Lρ (nρ m) ∨ gam1 = Lρ (Lρ (nρ m)) ∨
      gam1 = nρ (m + Luv m) ∨ gam1 = Lρ (nρ (m + Luv m)) ∨
        gam1 = Lρ (Lρ (nρ (m + Luv m))) := by
  decide +kernel

set_option synthInstance.maxSize 4096 in
theorem bet_mem_words : ∀ m : Co × Co, 2 • m.1 = 0 → 2 • m.2 = 0 → Lρ m = m → m ≠ 0 →
    m ≠ al0 → m = bet ∨ Lu m = bet := by
  decide +kernel

theorem exists_fix_of_norm : ∀ v : Co, v + fρ v + fρ (fρ v) = 0 → ∃ c : Co, c = v + fρ c := by
  decide +kernel

set_option synthInstance.maxSize 4096 in
theorem compI_finite : ∀ va vq : Co, kmap al0 va + va = -vq + fuv vq → fρ vq = vq →
    ∀ vb : Co, vb + fu vb = 0 → fu (-vb + fρ va + ft vb) = va + fuv (fρ va) →
    ((∃ c : Co, 2 • c = va) ∧ (∃ c : Co, 2 • c = fρ va)) ∨
    ∃ c : Co, vq + kmap al0 c + c = 0 ∧
      ((-c + va + fuv c = (0, 1, 1) ∧ -c + fρ va + ft c = (0, 3, 0) ∧ -c + vb + fu c = 0) ∨
       (-c + va + fuv c = (0, 3, 1) ∧ -c + fρ va + ft c = (0, 3, 2) ∧
         -c + vb + fu c = (1, 0, 0))) := by
  decide +kernel

theorem compII_finite : ∀ va : Co, fρ (fρ va) = va + fuv (fρ va) →
    (∃ c : Co, 2 • c = kmap bet (fu va) + -kmap bet va) ∧
      (∃ c : Co, 2 • c = fρ (kmap bet (fu va) + -kmap bet va)) := by
  decide +kernel

set_option synthInstance.maxSize 4096 in
theorem compIII_finite : ∀ va vd : Co, va + fuv vd = vd + ft va →
    ∀ vq : Co, kmap gam1 va + va = -vq + fuv vq → kmap gam1 vd + vd = -vq + ft vq →
    kmap gam1 vq = vq → ∀ vn : Co,
    -vn + (kmap gam2 vd + fρ va) + ft vn = fρ (fρ (va + fuv vd)) →
    (∃ c : Co, 2 • c = va) ∧ (∃ c : Co, 2 • c = vd) := by
  decide +kernel

set_option synthInstance.maxSize 4096 in
theorem sq_cases : ∀ a b : Co, 2 • a ≠ 0 → 2 • b ≠ 0 → 2 • a ≠ 2 • b →
    (2 • a = (0, 2, 0) ∧ 2 • b = (0, 0, 2)) ∨ (2 • a = (0, 0, 2) ∧ 2 • b = (0, 2, 0)) ∨
    (2 • a = (0, 0, 2) ∧ 2 • b = (0, 2, 2)) ∨ (2 • a = (0, 2, 2) ∧ 2 • b = (0, 2, 0)) ∨
    (2 • a = (0, 2, 0) ∧ 2 • b = (0, 2, 2)) ∨ (2 • a = (0, 2, 2) ∧ 2 • b = (0, 0, 2)) := by
  decide +kernel

theorem w_cases : ∀ z : Co, 2 • z = 0 → z ≠ 0 → z ≠ (0, 2, 0) → z ≠ (0, 0, 2) →
    z ≠ (0, 2, 2) → z = (1, 0, 0) ∨ z = (1, 2, 0) ∨ z = (1, 0, 2) ∨ z = (1, 2, 2) := by
  decide +kernel

theorem om_decomp : ∀ v : Co, 2 • v = 0 →
    v = v.1.val • (1, 0, 0) + (v.2.1.val / 2) • (0, 2, 0) + (v.2.2.val / 2) • (0, 0, 2) := by
  decide +kernel

theorem two_nsmul_eq : ∀ v : Co, 2 • v = v.2.1.val • (0, 2, 0) + v.2.2.val • (0, 0, 2) := by
  decide +kernel

theorem four_nsmul_eq : ∀ v : Co, 4 • v = 0 := by decide +kernel

theorem two_two_nsmul : ∀ v : Co, 2 • 2 • v = 0 := by decide +kernel

theorem fρ_add : ∀ v v' : Co, fρ (v + v') = fρ v + fρ v' := by decide +kernel

abbrev Mat : Type := Co × Co × Co

@[expose] def matAct (m : Mat) : Co → Co := lin m.1 m.2.1 m.2.2

@[expose] def matMul (m n : Mat) : Mat := (matAct n m.1, matAct n m.2.1, matAct n m.2.2)

@[expose] def d8 : List Mat :=
  [((1, 0, 0), (0, 0, 1), (0, 1, 0)), ((1, 0, 0), (0, 1, 0), (0, 0, 1)),
    ((1, 0, 2), (0, 0, 3), (0, 3, 2)), ((1, 0, 2), (0, 3, 2), (0, 0, 3)),
    ((1, 2, 0), (0, 2, 3), (0, 3, 0)), ((1, 2, 0), (0, 3, 0), (0, 2, 3)),
    ((1, 2, 2), (0, 1, 2), (0, 2, 1)), ((1, 2, 2), (0, 2, 1), (0, 1, 2))]

theorem matMul_mem_d8 : ∀ m ∈ d8, ∀ n ∈ d8, matMul m n ∈ d8 := by decide +kernel

theorem one_mem_d8 : (((1, 0, 0), (0, 1, 0), (0, 0, 1)) : Mat) ∈ d8 := by decide

theorem uv_mem_d8 : ((fuv (1, 0, 0), fuv (0, 1, 0), fuv (0, 0, 1)) : Mat) ∈ d8 := by decide

theorem t_mem_d8 : ((ft (1, 0, 0), ft (0, 1, 0), ft (0, 0, 1)) : Mat) ∈ d8 := by decide

theorem u_mem_d8 : ((fu (1, 0, 0), fu (0, 1, 0), fu (0, 0, 1)) : Mat) ∈ d8 := by decide

theorem eq_one_of_mem_d8 : ∀ m ∈ d8, m.1 = (1, 0, 0) → 2 • m.2.1 = (0, 2, 0) →
    2 • m.2.2 = (0, 0, 2) → m = ((1, 0, 0), (0, 1, 0), (0, 0, 1)) := by
  decide +kernel

end CFSG.CGT.Stroth77.Arch76
