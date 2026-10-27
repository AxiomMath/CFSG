module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Campbell.Basic
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.BinaryThreeSpaceFixedCodimensions
public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitG2Cert

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Campbell

section
open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family
open scoped Pointwise

variable {A : Type} [Group A] [Finite A] {X K R P : Subgroup A}

theorem statedSL_eq_top_of_card_two {F : Type} [Field F] [Fintype F] (h : Fintype.card F = 2) :
    StatedSL 3 F = ⊤ := by
  have hu : Subsingleton Fˣ := by
    have h1 : Nat.card Fˣ = 1 := by
      rw [Nat.card_units, Nat.card_eq_fintype_card, h]
    exact (Nat.card_eq_one_iff_unique.1 h1).1
  rw [eq_top_iff]
  intro g _
  refine Subgroup.subset_closure ?_
  have h1 : Matrix.GeneralLinearGroup.det g = 1 := Subsingleton.elim _ _
  simpa [Units.ext_iff] using h1

theorem statedSL_zmod_two_eq_top : StatedSL 3 (ZMod 2) = ⊤ :=
  statedSL_eq_top_of_card_two (F := ZMod 2) (by simp)

theorem gl32_exists_det_one : ∀ v w : Fin 3 → ZMod 2, v ≠ 0 → w ≠ 0 →
    ∃ M : Matrix (Fin 3) (Fin 3) (ZMod 2), M.det = 1 ∧ M.mulVec v = w := by
  decide +kernel

theorem gl32_fixed_vec : ∀ u : Fin 3 → ZMod 2,
    (∀ M : Matrix (Fin 3) (Fin 3) (ZMod 2), M.det = 1 → M.mulVec ![1, 0, 0] = ![1, 0, 0] →
      M.mulVec u = u) → u = 0 ∨ u = ![1, 0, 0] := by
  decide +kernel

theorem gl32_exists_GL {M : Matrix (Fin 3) (Fin 3) (ZMod 2)} (h : M.det = 1) :
    ∃ g : GL32, ((g : GL32) : Matrix (Fin 3) (Fin 3) (ZMod 2)) = M :=
  ⟨Matrix.SpecialLinearGroup.toGL ⟨M, h⟩, rfl⟩

theorem exists_mulVec_eq {v w : Fin 3 → ZMod 2} (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ g : GL32, ((g : GL32) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v = w := by
  obtain ⟨M, hM, hMv⟩ := gl32_exists_det_one v w hv hw
  obtain ⟨g, hg⟩ := gl32_exists_GL hM
  exact ⟨g, by rw [hg]; exact hMv⟩

theorem natural_irreducible {T : AddSubgroup (Fin 3 → ZMod 2)}
    (hinv : ∀ (g : GL32), ∀ v ∈ T, ((g : GL32) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v ∈ T) :
    T = ⊥ ∨ T = ⊤ := by
  by_cases hT : T = ⊥
  · exact Or.inl hT
  right
  obtain ⟨v, hvT, hv0⟩ : ∃ v ∈ T, v ≠ 0 := by
    by_contra hcon
    exact hT ((AddSubgroup.eq_bot_iff_forall T).2 fun x hx => by
      by_contra hx0
      exact hcon ⟨x, hx, hx0⟩)
  rw [eq_top_iff]
  intro w _
  by_cases hw : w = 0
  · rw [hw]
    exact T.zero_mem
  · obtain ⟨g, hg⟩ := exists_mulVec_eq hv0 hw
    rw [← hg]
    exact hinv g v hvT

theorem eq_id_of_commutes (φ : (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2))
    (hadd : ∀ x y, φ (x + y) = φ x + φ y) (hinj : ∀ x, φ x = 0 → x = 0)
    (hcomm : ∀ (g : GL32) (v : Fin 3 → ZMod 2),
      φ (((g : GL32) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v) =
        ((g : GL32) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec (φ v)) :
    ∀ v, φ v = v := by
  have hφ0 : φ 0 = 0 := by
    have h := hadd 0 0
    rw [add_zero] at h
    exact left_eq_add.1 h
  have he₁0 : (![1, 0, 0] : Fin 3 → ZMod 2) ≠ 0 := by
    intro h
    have := congrFun h 0
    simp at this
  have hfix : ∀ M : Matrix (Fin 3) (Fin 3) (ZMod 2), M.det = 1 →
      M.mulVec ![1, 0, 0] = ![1, 0, 0] → M.mulVec (φ ![1, 0, 0]) = φ ![1, 0, 0] := by
    intro M hM hMe
    obtain ⟨g, hg⟩ := gl32_exists_GL hM
    have h := hcomm g ![1, 0, 0]
    rw [hg, hMe] at h
    exact h.symm
  have hφe : φ ![1, 0, 0] = ![1, 0, 0] := by
    rcases gl32_fixed_vec _ hfix with h | h
    · exact absurd (hinj _ h) he₁0
    · exact h
  intro v
  by_cases hv : v = 0
  · rw [hv, hφ0]
  · obtain ⟨g, hg⟩ := exists_mulVec_eq he₁0 hv
    rw [← hg, hcomm g, hφe]

theorem eq_one_of_fixes_all {g : GL32}
    (h : ∀ v : Fin 3 → ZMod 2, ((g : GL32) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v = v) :
    g = 1 := by
  apply Units.ext
  rw [Units.val_one, Matrix.ext_iff_mulVec]
  intro v
  rw [h v, Matrix.one_mulVec]

theorem nonempty_mulEquiv_GL32_psl :
    Nonempty (GL32 ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) := by
  let e₁ : Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) ≃*
      Matrix.ProjGenLinGroup (Fin 3) (ZMod 2) :=
    MulEquiv.ofBijective Matrix.ProjectiveSpecialLinearGroup.toPGL
      ⟨Matrix.ProjectiveSpecialLinearGroup.toPGL_injective,
        Matrix.ProjectiveSpecialLinearGroup.toPGL_surj_of_roots fun r =>
          ⟨1, Subsingleton.elim _ _⟩⟩
  have hZ : Subgroup.center (GL (Fin 3) (ZMod 2)) = ⊥ := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar, eq_bot_iff]
    rintro _ ⟨r, rfl⟩
    rw [Subsingleton.elim r 1, map_one]
    exact Subgroup.one_mem _
  let e₂ : Matrix.ProjGenLinGroup (Fin 3) (ZMod 2) ≃* GL (Fin 3) (ZMod 2) :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact ⟨(e₁.trans e₂).symm⟩
end

section
open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family
open scoped Pointwise

variable {A : Type} [Group A] [Finite A] {X K R P : Subgroup A}

theorem gl32Syl_fixed_sylowT (w : Fin 3 → ZMod 2) :
    (∀ t ∈ CFSG.ProperTwoGeneratedCore.BinaryThreeSpace.sylowT, t • w = w) ↔
      (w = 0 ∨ w = ![1, 0, 0]) := by
  have key : ∀ w : Fin 3 → ZMod 2, (∀ a b c : ZMod 2,
      (CFSG.ProperTwoGeneratedCore.BinaryThreeSpace.unitri a b c).mulVec w = w) ↔
      (w = 0 ∨ w = ![1, 0, 0]) := by
    decide +kernel
  rw [← key]
  constructor
  · intro h a b c
    exact h _ ⟨a, b, c, rfl⟩
  · rintro h t ⟨a, b, c, rfl⟩
    exact h a b c

theorem gl32Syl_exists_conj {S : Subgroup GL32} (hS : Nat.card S = 8) :
    ∃ g : GL32, ∀ t : GL32,
      t ∈ CFSG.ProperTwoGeneratedCore.BinaryThreeSpace.sylowT ↔ g * t * g⁻¹ ∈ S := by
  have hS2 : IsPGroup 2 S := IsPGroup.of_card (n := 3) (by rw [hS]; norm_num)
  obtain ⟨g, hg⟩ :=
    CFSG.ProperTwoGeneratedCore.BinaryThreeSpace.FixedCodim.exists_conj_le_sylowT hS2
  let f : S → CFSG.ProperTwoGeneratedCore.BinaryThreeSpace.sylowT :=
    fun k => ⟨g⁻¹ * (k : GL32) * g, hg k k.2⟩
  have hinj : Function.Injective f := by
    intro k k' h
    have h' : g⁻¹ * (k : GL32) * g = g⁻¹ * (k' : GL32) * g := congrArg Subtype.val h
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h'))
  have hbij : Function.Bijective f := hinj.bijective_of_nat_card_le (by
    rw [CFSG.ProperTwoGeneratedCore.BinaryThreeSpace.card_sylowT, hS]; norm_num)
  refine ⟨g, fun t => ⟨fun ht => ?_, fun ht => ?_⟩⟩
  · obtain ⟨k, hk⟩ := hbij.2 ⟨t, ht⟩
    have hk' : g⁻¹ * (k : GL32) * g = t := congrArg Subtype.val hk
    have e : g * t * g⁻¹ = k := by rw [← hk']; group
    rw [e]
    exact k.2
  · have h1 := hg _ ht
    have e : g⁻¹ * (g * t * g⁻¹) * g = t := by group
    rwa [e] at h1

theorem sylow_fixed_line {S : Subgroup GL32} (hS : Nat.card S = 8) :
    ∃ e : Fin 3 → ZMod 2, e ≠ 0 ∧ ∀ v : Fin 3 → ZMod 2,
      (∀ g ∈ S, ((g : GL32) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v = v) ↔ (v = 0 ∨ v = e) := by
  obtain ⟨g, hg⟩ := gl32Syl_exists_conj hS
  refine ⟨g • ![1, 0, 0], ?_, fun v => ?_⟩
  · intro h
    have h1 : (![1, 0, 0] : Fin 3 → ZMod 2) = 0 := by
      simpa using congrArg (fun x => g⁻¹ • x) h
    have h2 := congrFun h1 0
    simp at h2
  · show (∀ k ∈ S, k • v = v) ↔ _
    constructor
    · intro hv
      have hw : ∀ t ∈ CFSG.ProperTwoGeneratedCore.BinaryThreeSpace.sylowT,
          t • (g⁻¹ • v) = g⁻¹ • v := by
        intro t ht
        have h1 := hv (g * t * g⁻¹) ((hg t).1 ht)
        have e1 : g⁻¹ * (g * t * g⁻¹) = t * g⁻¹ := by group
        calc t • g⁻¹ • v = (t * g⁻¹) • v := (mul_smul t g⁻¹ v).symm
          _ = (g⁻¹ * (g * t * g⁻¹)) • v := by rw [e1]
          _ = g⁻¹ • ((g * t * g⁻¹) • v) := mul_smul _ _ _
          _ = g⁻¹ • v := by rw [h1]
      rcases (gl32Syl_fixed_sylowT _).1 hw with h | h
      · left
        simpa [h] using (smul_inv_smul g v).symm
      · right
        simpa [h] using (smul_inv_smul g v).symm
    · rintro (rfl | rfl) k hk
      · exact smul_zero k
      · have ht : g⁻¹ * k * g ∈ CFSG.ProperTwoGeneratedCore.BinaryThreeSpace.sylowT := by
          rw [hg]
          have e : g * (g⁻¹ * k * g) * g⁻¹ = k := by group
          rw [e]
          exact hk
        have h1 := (gl32Syl_fixed_sylowT _).2 (Or.inr rfl) _ ht
        have e : k * g = g * (g⁻¹ * k * g) := by group
        calc k • g • (![1, 0, 0] : Fin 3 → ZMod 2) = (k * g) • (![1, 0, 0] : Fin 3 → ZMod 2) :=
              (mul_smul k g _).symm
          _ = (g * (g⁻¹ * k * g)) • (![1, 0, 0] : Fin 3 → ZMod 2) := by rw [e]
          _ = g • (g⁻¹ * k * g) • (![1, 0, 0] : Fin 3 → ZMod 2) := mul_smul _ _ _
          _ = g • (![1, 0, 0] : Fin 3 → ZMod 2) := by rw [h1]

theorem index_vecStab {e : Fin 3 → ZMod 2} (he : e ≠ 0) : (vecStab e).index = 7 := by
  have hstab : vecStab e = MulAction.stabilizer GL32 e := rfl
  rw [hstab, MulAction.index_stabilizer]
  have horb : MulAction.orbit GL32 e = {w | w ≠ 0} := by
    ext w
    constructor
    · rintro ⟨g, rfl⟩ h0
      apply he
      simpa using congrArg (fun x => g⁻¹ • x) h0
    · intro hw
      obtain ⟨g, hg⟩ := exists_mulVec_eq he hw
      exact ⟨g, hg⟩
  rw [horb, ← Nat.card_coe_set_eq]
  have hc : Nat.card {w : Fin 3 → ZMod 2 // w ≠ 0} = 7 := by
    rw [Nat.card_eq_fintype_card]
    decide
  exact hc
end

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Campbell
