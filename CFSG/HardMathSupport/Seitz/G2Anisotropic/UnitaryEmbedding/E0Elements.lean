module

public import CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding.E0Action

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.RF4 CFSG.Quasithin.G2U CFSG.RankThree.Chevalley

variable {L : Type} [Field L]

theorem cubeTuple_mul (ζ : Lˣ) (a b a' b' : ℤ) :
    cubeTuple ζ a b * cubeTuple ζ a' b' = cubeTuple ζ (a + a') (b + b') := by
  funext k
  fin_cases k
  · show ζ ^ a * ζ ^ a' = ζ ^ (a + a')
    rw [zpow_add]
  · show ζ ^ b * ζ ^ b' = ζ ^ (b + b')
    rw [zpow_add]

theorem toFin3_add : ∀ i i' : Fin 3, toFin3 ((i.val : ℤ) + (i'.val : ℤ)) = i + i' := by decide

theorem cubeTuple3_mul {ζ : Lˣ} (hζ : orderOf ζ = 3) (i j i' j' : Fin 3) :
    cubeTuple3 ζ i j * cubeTuple3 ζ i' j' = cubeTuple3 ζ (i + i') (j + j') := by
  rw [cubeTuple3, cubeTuple3, cubeTuple_mul, cubeTuple_eq_cubeTuple3 hζ, toFin3_add, toFin3_add]

theorem cubeTuple3_zero {ζ : Lˣ} : cubeTuple3 ζ 0 0 = 1 := by
  funext k
  fin_cases k
  · show ζ ^ (((0 : Fin 3) : ℕ) : ℤ) = 1
    simp
  · show ζ ^ (((0 : Fin 3) : ℕ) : ℤ) = 1
    simp

theorem cubeTuple3_injective {ζ : Lˣ} (hζ : orderOf ζ = 3) {i j i' j' : Fin 3}
    (h : cubeTuple3 ζ i j = cubeTuple3 ζ i' j') : i = i' ∧ j = j' := by
  have hinj : ∀ a b : Fin 3, ζ ^ (a : ℕ) = ζ ^ (b : ℕ) → a = b := fun a b hab => by
    apply Fin.ext
    refine pow_injOn_Iio_orderOf (x := ζ) ?_ ?_ hab
    · rw [hζ]; exact a.2
    · rw [hζ]; exact b.2
  have h0 := congrFun h ⟨0, by decide⟩
  have h1 := congrFun h ⟨1, by decide⟩
  simp only [cubeTuple3, cubeTuple] at h0 h1
  change ζ ^ ((i : ℕ) : ℤ) = ζ ^ ((i' : ℕ) : ℤ) at h0
  change ζ ^ ((j : ℕ) : ℤ) = ζ ^ ((j' : ℕ) : ℤ) at h1
  rw [zpow_natCast, zpow_natCast] at h0 h1
  exact ⟨hinj _ _ h0, hinj _ _ h1⟩

theorem cubeTuple3_pow_three {ζ : Lˣ} (hζ : orderOf ζ = 3) (i j : Fin 3) :
    cubeTuple3 ζ i j ^ 3 = 1 := by
  have h3 : ζ ^ 3 = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  funext k
  fin_cases k
  · simp only [cubeTuple3, cubeTuple]
    change (ζ ^ ((i : ℕ) : ℤ)) ^ 3 = 1
    rw [zpow_natCast, ← pow_mul, mul_comm, pow_mul, h3, one_pow]
  · simp only [cubeTuple3, cubeTuple]
    change (ζ ^ ((j : ℕ) : ℤ)) ^ 3 = 1
    rw [zpow_natCast, ← pow_mul, mul_comm, pow_mul, h3, one_pow]

theorem rootDiagUnit_cubeTuple3_mem_torusTorsion {ζ : Lˣ} (hζ : orderOf ζ = 3) (i j : Fin 3) :
    rootDiagUnit .G2 (cubeTuple3 ζ i j) ∈ torusTorsion L 3 :=
  (rootDiagUnit_mem_torusTorsion_iff 3 _).2 (cubeTuple3_pow_three hζ i j)

theorem exists_cubeTuple3_of_mem_torusTorsion {ζ : Lˣ} (hζ : orderOf ζ = 3) {t : ModGL .G2 L}
    (ht : t ∈ torusTorsion L 3) : ∃ i j : Fin 3, t = rootDiagUnit .G2 (cubeTuple3 ζ i j) := by
  obtain ⟨hT, -⟩ := mem_torusTorsion_iff.1 ht
  obtain ⟨c, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hT
  have hc := (rootDiagUnit_mem_torusTorsion_iff 3 c).1 ht
  have hprim : IsPrimitiveRoot ζ 3 := by
    have := IsPrimitiveRoot.orderOf ζ
    rwa [hζ] at this
  have hpow : ∀ k, ∃ m : Fin 3, ζ ^ (m : ℕ) = c k := fun k => by
    have hk : c k ^ 3 = 1 := by simpa using congrFun hc k
    have hk' : ((c k : Lˣ) : L) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, hk]; rfl
    have hprim' : IsPrimitiveRoot (ζ : L) 3 := IsPrimitiveRoot.coe_units_iff.2 hprim
    obtain ⟨m, hm, hmk⟩ := hprim'.eq_pow_of_pow_eq_one hk'
    exact ⟨⟨m, hm⟩, Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hmk)⟩
  obtain ⟨i, hi⟩ := hpow ⟨0, by decide⟩
  obtain ⟨j, hj⟩ := hpow ⟨1, by decide⟩
  refine ⟨i, j, ?_⟩
  congr 1
  funext k
  fin_cases k
  · simp only [cubeTuple3, cubeTuple]
    change c ⟨0, _⟩ = ζ ^ ((i : ℕ) : ℤ)
    rw [zpow_natCast, hi]
  · simp only [cubeTuple3, cubeTuple]
    change c ⟨1, _⟩ = ζ ^ ((j : ℕ) : ℤ)
    rw [zpow_natCast, hj]

theorem conj_pow_cubeTuple3 {ζ : Lˣ} (hζ : orderOf ζ = 3) {n : ModGL .G2 L}
    (hn : n ∈ monomialSubgroup .G2 L) (hw : weylQuotientHom .G2 L ⟨n, hn⟩ = rho0) (i j : Fin 3)
    (k : ℕ) :
    n ^ k * rootDiagUnit .G2 (cubeTuple3 ζ i j) * (n ^ k)⁻¹ =
      rootDiagUnit .G2 (cubeTuple3 ζ i (j + Fin.ofNat 3 k * i)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have : n ^ (k + 1) * rootDiagUnit .G2 (cubeTuple3 ζ i j) * (n ^ (k + 1))⁻¹ =
        n * (n ^ k * rootDiagUnit .G2 (cubeTuple3 ζ i j) * (n ^ k)⁻¹) * n⁻¹ := by
      rw [pow_succ', mul_inv_rev]; group
    rw [this, ih, conj_cubeTuple3 hζ hn hw]
    have hk : Fin.ofNat 3 (k + 1) = Fin.ofNat 3 k + 1 := by
      apply Fin.ext
      simp [Fin.val_add, Fin.ofNat]
    rw [hk, add_mul, one_mul, add_left_comm, add_comm i]

end CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding
