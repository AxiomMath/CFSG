module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcTwistedConfig
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcD4Action
public import CFSG.RankThree.PartOne.KD4L.TriNu
public import CFSG.RankThree.PartOne.KE.A1Main
public import CFSG.RankThree.PartOne.KD4L.TriDescent

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.Chevalley CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KD4L
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints)


namespace Up34Chev2

theorem Bad3.mono {G : Type} [Group G] {P P' : Subgroup G} (h : P ≤ P') (hB : Bad3 P) :
    Bad3 P' := by
  obtain ⟨X, Y, Z, hX, hY, hZ, rest⟩ := hB
  exact ⟨X, Y, Z, hX.trans h, hY.trans h, hZ.trans h, rest⟩

section Std

variable {τ : Tag} {L : Type} [Field L] [CharP L 2]

@[expose] noncomputable def stdF (n₁ : ModGL τ L) (f : ℕ) : ModGL τ L →* ModGL τ L :=
  (MulAut.conj n₁).toMonoidHom.comp (Units.map (entrywiseHom (iterateFrobenius L 2 f)))

theorem stdF_apply (n₁ : ModGL τ L) (f : ℕ) (g : ModGL τ L) :
    stdF n₁ f g = n₁ * Units.map (entrywiseHom (iterateFrobenius L 2 f)) g * n₁⁻¹ := rfl

theorem stdF_xUnit (n₁ : ModGL τ L) (f : ℕ) (j : Fin τ.rank) (c : L) :
    stdF n₁ f (xUnit τ L j c) = n₁ * xUnit τ L j (c ^ 2 ^ f) * n₁⁻¹ := by
  rw [stdF_apply, entrywise_xUnit]

theorem stdF_yUnit (n₁ : ModGL τ L) (f : ℕ) (j : Fin τ.rank) (c : L) :
    stdF n₁ f (yUnit τ L j c) = n₁ * yUnit τ L j (c ^ 2 ^ f) * n₁⁻¹ := by
  rw [stdF_apply, entrywise_yUnit]

theorem stdF_simpleRootSL2 {n₁ : ModGL τ L} {π : Equiv.Perm (Fin τ.rank)} {f : ℕ}
    {j : Fin τ.rank}
    (hgenj : ∀ c : L, n₁ * xUnit τ L j c * n₁⁻¹ = xUnit τ L (π j) c ∧
      n₁ * yUnit τ L j c * n₁⁻¹ = yUnit τ L (π j) c) (A : SL2 L) :
    stdF n₁ f (simpleRootSL2 τ L j A) =
      simpleRootSL2 τ L (π j) (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 f) A) := by
  have key : (stdF n₁ f).comp (simpleRootSL2 τ L j) = (simpleRootSL2 τ L (π j)).comp
      (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 f)) := by
    refine MonoidHom.eq_of_eqOn_dense sl2_closure_upper_lower fun g hg => ?_
    rcases hg with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · show stdF n₁ f (simpleRootSL2 τ L j (CFSG.LieType.Chevalley.uSL c)) =
        simpleRootSL2 τ L (π j) (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 f)
          (CFSG.LieType.Chevalley.uSL c))
      rw [simpleRootSL2_uSL, stdF_xUnit, sl2_map_uSL, simpleRootSL2_uSL, iterateFrobenius_def]
      exact (hgenj _).1
    · show stdF n₁ f (simpleRootSL2 τ L j (CFSG.LieType.Chevalley.vSL c)) =
        simpleRootSL2 τ L (π j) (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 f)
          (CFSG.LieType.Chevalley.vSL c))
      rw [simpleRootSL2_vSL, stdF_yUnit, sl2_map_vSL, simpleRootSL2_vSL, iterateFrobenius_def]
      exact (hgenj _).2
  exact DFunLike.congr_fun key A

theorem iform_single_cartan (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (p q : Fin τ.rank) :
    iform (Pi.single p 1 : Fin τ.rank → ℤ) (Pi.single q 1) = τ.cartan p q := by
  have hsym : τ.symmetrizer p p = 1 := by
    have h1 := iform_single_single (τ := τ) p
    have h2 := CFSG.LieType.Chevalley.EvenOddRadical.iform_self_eq_two hτ (isRoot_single τ p)
    omega
  rw [iform_single_left, hsym, one_mul,
    Finset.sum_eq_single q (fun l _ hl => by rw [Pi.single_eq_of_ne hl, mul_zero])
      (fun h => absurd (Finset.mem_univ q) h), Pi.single_eq_same, mul_one]

theorem d4Cfg_single (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {a b k c : Fin τ.rank}
    (hab : τ.cartan a b = 0) (hak : τ.cartan a k = 0) (hbk : τ.cartan b k = 0)
    (hca : τ.cartan c a = -1) (hcb : τ.cartan c b = -1) (hck : τ.cartan c k = -1) :
    D4Cfg τ (Pi.single a 1) (Pi.single b 1) (Pi.single k 1) (Pi.single c 1) :=
  ⟨isRoot_single τ a, isRoot_single τ b, isRoot_single τ k, isRoot_single τ c,
    by rw [iform_single_cartan hτ, hab], by rw [iform_single_cartan hτ, hak],
    by rw [iform_single_cartan hτ, hbk], by rw [iform_single_cartan hτ, hca],
    by rw [iform_single_cartan hτ, hcb], by rw [iform_single_cartan hτ, hck]⟩

theorem range_rootSL2_single_le {j : Fin τ.rank} (hj : j ∈ d4Set τ) :
    (rootSL2 τ L (Pi.single j 1 : Fin τ.rank → ℤ)).range ≤ subsystemGroup τ L (d4Set τ) := by
  have h : rootSL2 τ L (Pi.single j 1 : Fin τ.rank → ℤ) = simpleRootSL2 τ L j :=
    MonoidHom.ext (rootSL2_single_apply' j)
  rw [h, range_simpleRootSL2, Subgroup.closure_le]
  rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
  · exact xUnit_mem_subsystemGroup hj c
  · exact yUnit_mem_subsystemGroup hj c

theorem cfgGroup_single_le {a b k c : Fin τ.rank} (ha : a ∈ d4Set τ) (hb : b ∈ d4Set τ)
    (hk : k ∈ d4Set τ) (hc : c ∈ d4Set τ) :
    cfgGroup τ L (Pi.single a 1) (Pi.single b 1) (Pi.single k 1) (Pi.single c 1) ≤
      subsystemGroup τ L (d4Set τ) :=
  sup_le (sup_le (sup_le (range_rootSL2_single_le ha) (range_rootSL2_single_le hb))
    (range_rootSL2_single_le hk)) (range_rootSL2_single_le hc)

theorem fixSub_stdF (n₁ : ModGL τ L) (f : ℕ) :
    fixSub (stdF n₁ f) = twistedFixedPoints n₁ (Units.map (entrywiseHom (iterateFrobenius L 2 f))) :=
  rfl

end Std

section Layer

variable {τ : Tag} {L : Type} [Field L] [CharP L 2] [IsAlgClosed L]

theorem stdF_a {n₁ : ModGL τ L} {π : Equiv.Perm (Fin τ.rank)} {f : ℕ}
    (hgen : ∀ j ∈ d4Set τ, ∀ c : L, n₁ * xUnit τ L j c * n₁⁻¹ = xUnit τ L (π j) c ∧
      n₁ * yUnit τ L j c * n₁⁻¹ = yUnit τ L (π j) c) {j j' : Fin τ.rank} (hj : j ∈ d4Set τ)
    (hjj : π j = j') (A : SL2 L) :
    stdF n₁ f (rootSL2 τ L (Pi.single j 1) A) =
      rootSL2 τ L (Pi.single j' 1)
        (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 f) A) := by
  rw [rootSL2_single_apply', rootSL2_single_apply', ← hjj]
  exact stdF_simpleRootSL2 (hgen j hj) A

theorem bad3_layer_swap (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {f : ℕ} (hf : 1 ≤ f)
    {n₁ : ModGL τ L} {π : Equiv.Perm (Fin τ.rank)}
    (hgen : ∀ j ∈ d4Set τ, ∀ c : L, n₁ * xUnit τ L j c * n₁⁻¹ = xUnit τ L (π j) c ∧
      n₁ * yUnit τ L j c * n₁⁻¹ = yUnit τ L (π j) c) {a b k c : Fin τ.rank}
    (ha : a ∈ d4Set τ) (hb : b ∈ d4Set τ) (hk : k ∈ d4Set τ) (hc : c ∈ d4Set τ)
    (hab : τ.cartan a b = 0) (hak : τ.cartan a k = 0) (hbk : τ.cartan b k = 0)
    (hca : τ.cartan c a = -1) (hcb : τ.cartan c b = -1) (hck : τ.cartan c k = -1)
    (hπa : π a = b) (hπb : π b = a) (hπk : π k = k) (hπc : π c = c) :
    Bad3 (subsystemGroup τ L (d4Set τ) ⊓
      twistedFixedPoints n₁ (Units.map (entrywiseHom (iterateFrobenius L 2 f)))) := by
  have hB := bad3_swap hτ hf (d4Cfg_single hτ hab hak hbk hca hcb hck) (F₁ := stdF n₁ f)
    (stdF_a hgen ha hπa) (stdF_a hgen hb hπb) (stdF_a hgen hk hπk) (stdF_a hgen hc hπc)
  exact hB.mono (inf_le_inf (cfgGroup_single_le ha hb hk hc) (fixSub_stdF n₁ f).le)

theorem bad3_layer_cycle (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {f : ℕ} (hf : 1 ≤ f)
    {n₁ : ModGL τ L} {π : Equiv.Perm (Fin τ.rank)}
    (hgen : ∀ j ∈ d4Set τ, ∀ c : L, n₁ * xUnit τ L j c * n₁⁻¹ = xUnit τ L (π j) c ∧
      n₁ * yUnit τ L j c * n₁⁻¹ = yUnit τ L (π j) c) {a b k c : Fin τ.rank}
    (ha : a ∈ d4Set τ) (hb : b ∈ d4Set τ) (hk : k ∈ d4Set τ) (hc : c ∈ d4Set τ)
    (hab : τ.cartan a b = 0) (hak : τ.cartan a k = 0) (hbk : τ.cartan b k = 0)
    (hca : τ.cartan c a = -1) (hcb : τ.cartan c b = -1) (hck : τ.cartan c k = -1)
    (hπa : π a = b) (hπb : π b = k) (hπk : π k = a) (hπc : π c = c) :
    Bad3 (subsystemGroup τ L (d4Set τ) ⊓
      twistedFixedPoints n₁ (Units.map (entrywiseHom (iterateFrobenius L 2 f)))) := by
  have hB := bad3_cycle hτ hf (d4Cfg_single hτ hab hak hbk hca hcb hck) (F₁ := stdF n₁ f)
    (stdF_a hgen ha hπa) (stdF_a hgen hb hπb) (stdF_a hgen hk hπk) (stdF_a hgen hc hπc)
  exact hB.mono (inf_le_inf (cfgGroup_single_le ha hb hk hc) (fixSub_stdF n₁ f).le)

end Layer

section D4Std

variable {τ : Tag} [E6Sub τ] {L : Type} [Field L] [CharP L 2] [IsAlgClosed L]

theorem formPerm_three_vals {α : Type*} [DecidableEq α] {a b c : α} (hab : a ≠ b) (hbc : b ≠ c)
    (hac : a ≠ c) :
    List.formPerm [a, b, c] a = b ∧ List.formPerm [a, b, c] b = c ∧
      List.formPerm [a, b, c] c = a := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [List.formPerm_cons_cons, Equiv.swap_apply_def, hab, hbc, hac, hab.symm, hbc.symm,
      hac.symm]

theorem bad3_d4_std (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {f : ℕ} (hf : 1 ≤ f) {n₁ : ModGL τ L}
    {π : Equiv.Perm (Fin τ.rank)} (hleaf : IsD4LeafPerm π) (hπ1 : π ≠ 1)
    (hgen : ∀ j ∈ d4Set τ, ∀ c : L, n₁ * xUnit τ L j c * n₁⁻¹ = xUnit τ L (π j) c ∧
      n₁ * yUnit τ L j c * n₁⁻¹ = yUnit τ L (π j) c) :
    Bad3 (subsystemGroup τ L (d4Set τ) ⊓
      twistedFixedPoints n₁ (Units.map (entrywiseHom (iterateFrobenius L 2 f)))) := by
  have hτ' : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
    rcases hτ with h | h | h <;> simp [h]
  have m1 : e6Idx (τ := τ) 1 ∈ d4Set τ := e6Idx_mem_d4Set' 1 (by decide) (by decide)
  have m2 : e6Idx (τ := τ) 2 ∈ d4Set τ := e6Idx_mem_d4Set' 2 (by decide) (by decide)
  have m3 : e6Idx (τ := τ) 3 ∈ d4Set τ := e6Idx_mem_d4Set' 3 (by decide) (by decide)
  have m4 : e6Idx (τ := τ) 4 ∈ d4Set τ := e6Idx_mem_d4Set' 4 (by decide) (by decide)
  have n12 : e6Idx (τ := τ) 1 ≠ e6Idx 2 := e6Idx_ne (by decide)
  have n14 : e6Idx (τ := τ) 1 ≠ e6Idx 4 := e6Idx_ne (by decide)
  have n24 : e6Idx (τ := τ) 2 ≠ e6Idx 4 := e6Idx_ne (by decide)
  have n13 : e6Idx (τ := τ) 1 ≠ e6Idx 3 := e6Idx_ne (by decide)
  have n23 : e6Idx (τ := τ) 2 ≠ e6Idx 3 := e6Idx_ne (by decide)
  have n43 : e6Idx (τ := τ) 4 ≠ e6Idx 3 := e6Idx_ne (by decide)
  have c12 : τ.cartan (e6Idx 1) (e6Idx 2) = 0 := by rw [cartan_e6Idx]; decide
  have c21 : τ.cartan (e6Idx 2) (e6Idx 1) = 0 := by rw [cartan_e6Idx]; decide
  have c14 : τ.cartan (e6Idx 1) (e6Idx 4) = 0 := by rw [cartan_e6Idx]; decide
  have c41 : τ.cartan (e6Idx 4) (e6Idx 1) = 0 := by rw [cartan_e6Idx]; decide
  have c24 : τ.cartan (e6Idx 2) (e6Idx 4) = 0 := by rw [cartan_e6Idx]; decide
  have c42 : τ.cartan (e6Idx 4) (e6Idx 2) = 0 := by rw [cartan_e6Idx]; decide
  have c31 : τ.cartan (e6Idx 3) (e6Idx 1) = -1 := by rw [cartan_e6Idx]; decide
  have c32 : τ.cartan (e6Idx 3) (e6Idx 2) = -1 := by rw [cartan_e6Idx]; decide
  have c34 : τ.cartan (e6Idx 3) (e6Idx 4) = -1 := by rw [cartan_e6Idx]; decide
  rcases hleaf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hπ1
  · exact bad3_layer_swap hτ' hf hgen m1 m2 m4 m3 c12 c14 c24 c31 c32 c34
      (Equiv.swap_apply_left _ _) (Equiv.swap_apply_right _ _)
      (Equiv.swap_apply_of_ne_of_ne n14.symm n24.symm)
      (Equiv.swap_apply_of_ne_of_ne n13.symm n23.symm)
  · exact bad3_layer_swap hτ' hf hgen m1 m4 m2 m3 c14 c12 c42 c31 c34 c32
      (Equiv.swap_apply_left _ _) (Equiv.swap_apply_right _ _)
      (Equiv.swap_apply_of_ne_of_ne n12.symm n24)
      (Equiv.swap_apply_of_ne_of_ne n13.symm n43.symm)
  · exact bad3_layer_swap hτ' hf hgen m2 m4 m1 m3 c24 c21 c41 c32 c34 c31
      (Equiv.swap_apply_left _ _) (Equiv.swap_apply_right _ _)
      (Equiv.swap_apply_of_ne_of_ne n12 n14)
      (Equiv.swap_apply_of_ne_of_ne n23.symm n43.symm)
  · obtain ⟨e1, e2, e3⟩ := formPerm_three_vals n12 n24 n14
    refine bad3_layer_cycle hτ' hf hgen m1 m2 m4 m3 c12 c14 c24 c31 c32 c34 e1 e2 e3 ?_
    refine List.formPerm_apply_of_notMem ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨n13.symm, n23.symm, n43.symm⟩
  · obtain ⟨e1, e2, e3⟩ := formPerm_three_vals n14 n24.symm n12
    refine bad3_layer_cycle hτ' hf hgen m1 m4 m2 m3 c14 c12 c42 c31 c34 c32 e1 e2 e3 ?_
    refine List.formPerm_apply_of_notMem ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨n13.symm, n43.symm, n23.symm⟩

end D4Std

end Up34Chev2

end CFSG.HardMathSupport.Dickson.Sec6
