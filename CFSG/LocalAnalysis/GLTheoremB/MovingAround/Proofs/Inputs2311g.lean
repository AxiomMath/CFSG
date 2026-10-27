module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2311f2
public import CFSG.HardMathSupport.Seitz.ExceptionsTransport.G2SplitTorusPlane
public import CFSG.RankThree.Chevalley.SteinbergCAF4EvenQPlusOrthogonal
public import CFSG.RankThree.PartOne.K159.BorelSL

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311g

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311c
  CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311d CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311f
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section G2Three

open CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport
  CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator

set_option linter.unusedSectionVars false


theorem g2PinnedX_pow_ringChar {K : Type} [Field K] (α : Fin Tag.G2.rank → ℤ) (c : K) :
    pinnedX .G2 K α c ^ ringChar K = 1 := by
  rw [pinnedX_pow_eq, ringChar.Nat.cast_ringChar, zero_mul, pinnedX_zero]

theorem g2Qg_exists_pow_eq_one {K : Type} [Field K] [Finite K] {g : ModGL .G2 K} (hg : g ∈ Qg K) :
    ∃ n : ℕ, g ^ (ringChar K ^ n) = 1 := by
  have hle : Qg K ≤ posUnipotent .G2 K := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨γ, hγ, c, rfl⟩
    have hγ' : γ ∈ {α : Fin Tag.G2.rank → ℤ | IsRoot .G2 α ∧ 0 < height α} := by
      rcases hγ with rfl | rfl | rfl | rfl | rfl
      · exact ⟨isRoot_gA, by decide⟩
      · exact ⟨isRoot_gU, by decide⟩
      · exact ⟨isRoot_gV, by decide⟩
      · exact ⟨isRoot_gB, by decide⟩
      · exact ⟨isRoot_gC, by decide⟩
    exact (le_iSup₂_of_le (f := fun β (_ : β ∈ {α : Fin Tag.G2.rank → ℤ | IsRoot .G2 α ∧ 0 < height α}) =>
      rootSubgroup .G2 K β) γ hγ' le_rfl) (Subgroup.subset_closure ⟨c, rfl⟩)
  have : CharP K (ringChar K) := ringChar.charP K
  have hP := ((positive_root_triangularity.{0, 0} .G2).2 K (ringChar K)).2.1
  obtain ⟨n, hn⟩ := hP ⟨g, hle hg⟩
  exact ⟨n, by simpa using congrArg Subtype.val hn⟩

theorem g2UniStdPair_closure_eq_top {K : Type} [Field K] [Finite K] (h3 : 3 ∣ Nat.card K + 1)
    (hK : 3 ≤ Nat.card K) :
    Subgroup.closure {k : adjointGroup .G2 K | (Commute k (zStd K) ∨ Commute k (eStd K)) ∧
      ∃ n : ℕ, k ^ (ringChar K ^ n) = 1} = ⊤ := by
  obtain ⟨x, hx, hxz, B, hxe⟩ := conj_pair (K := K) h3
  set S := {k : adjointGroup .G2 K | (Commute k (zStd K) ∨ Commute k (eStd K)) ∧
      ∃ n : ℕ, k ^ (ringChar K ^ n) = 1} with hS
  set φ : adjointGroup .G2 K →* ModGL .G2 K :=
    (MulAut.conj x).toMonoidHom.comp (adjointGroup .G2 K).subtype with hφ
  set H : Subgroup (ModGL .G2 K) := (Subgroup.closure S).map φ with hH
  have hzStd : ((zStd K : adjointGroup .G2 K) : ModGL .G2 K) =
      rootSL2 .G2 K gV (orderThreeSL K) := rfl
  have heStd : ((eStd K : adjointGroup .G2 K) : ModGL .G2 K) =
      rootSL2 .G2 K gA (orderThreeSL K) := rfl
  have hmem : ∀ g : ModGL .G2 K, g ∈ adjointGroup .G2 K →
      (Commute g (zr K) ∨ Commute g (rootSL2 .G2 K gC B)) → (∃ n : ℕ, g ^ (ringChar K ^ n) = 1) →
      g ∈ H := by
    intro g hgA hcomm ⟨n, hn⟩
    have hyA : x⁻¹ * g * x ∈ adjointGroup .G2 K :=
      mul_mem (mul_mem (inv_mem hx) hgA) hx
    refine ⟨⟨x⁻¹ * g * x, hyA⟩, Subgroup.subset_closure ⟨?_, n, ?_⟩, ?_⟩
    · rcases hcomm with hc | hc
      · left
        apply Subtype.ext
        show x⁻¹ * g * x * (rootSL2 .G2 K gV (orderThreeSL K)) =
          rootSL2 .G2 K gV (orderThreeSL K) * (x⁻¹ * g * x)
        have e : rootSL2 .G2 K gV (orderThreeSL K) = x⁻¹ * zr K * x := by
          rw [← hxz]; group
        rw [e]
        have := hc.eq
        calc x⁻¹ * g * x * (x⁻¹ * zr K * x) = x⁻¹ * (g * zr K) * x := by group
          _ = x⁻¹ * (zr K * g) * x := by rw [this]
          _ = x⁻¹ * zr K * x * (x⁻¹ * g * x) := by group
      · right
        apply Subtype.ext
        show x⁻¹ * g * x * (rootSL2 .G2 K gA (orderThreeSL K)) =
          rootSL2 .G2 K gA (orderThreeSL K) * (x⁻¹ * g * x)
        have e : rootSL2 .G2 K gA (orderThreeSL K) = x⁻¹ * rootSL2 .G2 K gC B * x := by
          rw [← hxe]; group
        rw [e]
        have := hc.eq
        calc x⁻¹ * g * x * (x⁻¹ * rootSL2 .G2 K gC B * x) = x⁻¹ * (g * rootSL2 .G2 K gC B) * x := by
              group
          _ = x⁻¹ * (rootSL2 .G2 K gC B * g) * x := by rw [this]
          _ = x⁻¹ * rootSL2 .G2 K gC B * x * (x⁻¹ * g * x) := by group
    · apply Subtype.ext
      show (x⁻¹ * g * x) ^ (ringChar K ^ n) = 1
      rw [show x⁻¹ * g * x = (MulAut.conj x⁻¹) g by simp [MulAut.conj_apply], ← map_pow, hn, map_one]
    · simp only [hφ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        Subgroup.coe_subtype]
      group
  have hzr_range : zr K ∈ (rootSL2 .G2 K gR).range := ⟨orderThreeSL K, zr_eq_rootSL2.symm⟩
  have hB_range : rootSL2 .G2 K gC B ∈ (rootSL2 .G2 K gC).range := ⟨B, rfl⟩
  have hcomm_zr : ∀ h ∈ (rootSL2 .G2 K gC).range, Commute h (zr K) := fun h hh =>
    (commute_L_r_c _ hzr_range _ hh).symm
  have hUc : ∀ t : K, pinnedX .G2 K gC t ∈ (rootSL2 .G2 K gC).range := fun t => by
    rw [CFSG.RankThree.Chevalley.range_rootSL2_of_isRoot isRoot_gC]
    exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨t, rfl⟩)
  have hUnc : ∀ t : K, pinnedX .G2 K (-gC) t ∈ (rootSL2 .G2 K gC).range := fun t => by
    rw [CFSG.RankThree.Chevalley.range_rootSL2_of_isRoot isRoot_gC]
    exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨t, rfl⟩)
  have hle : adjointGroup .G2 K ≤ H := by
    refine adjointGroup_le_of_centralizer H ?_ ?_ ?_ ?_ ?_
      (exists_ne_zero_ne_one hK) (three_ne_zero_of_dvd h3)
    · intro t
      rw [xUnit_iR]
      have hr : pinnedX .G2 K gR t ∈ (rootSL2 .G2 K gR).range := by
        rw [CFSG.RankThree.Chevalley.range_rootSL2_of_isRoot isRoot_gR]
        exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨t, rfl⟩)
      exact hmem _ (pinnedX_mem_adjointGroup _ _) (Or.inr (commute_L_r_c _ hr _ hB_range))
        ⟨1, by rw [pow_one]; exact g2PinnedX_pow_ringChar _ _⟩
    · intro t
      rw [yUnit_iR]
      have hr : pinnedX .G2 K (-gR) t ∈ (rootSL2 .G2 K gR).range := by
        rw [CFSG.RankThree.Chevalley.range_rootSL2_of_isRoot isRoot_gR]
        exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨t, rfl⟩)
      exact hmem _ (pinnedX_mem_adjointGroup _ _) (Or.inr (commute_L_r_c _ hr _ hB_range))
        ⟨1, by rw [pow_one]; exact g2PinnedX_pow_ringChar _ _⟩
    · intro t
      exact hmem _ (pinnedX_mem_adjointGroup _ _) (Or.inl (hcomm_zr _ (hUc t)))
        ⟨1, by rw [pow_one]; exact g2PinnedX_pow_ringChar _ _⟩
    · intro t
      exact hmem _ (pinnedX_mem_adjointGroup _ _) (Or.inl (hcomm_zr _ (hUnc t)))
        ⟨1, by rw [pow_one]; exact g2PinnedX_pow_ringChar _ _⟩
    · intro g hg hfix
      refine hmem g (Qg_le_adjointGroup hg) (Or.inl ?_) (g2Qg_exists_pow_eq_one hg)
      have : zr K * g = g * zr K := by
        rw [mul_inv_eq_iff_eq_mul] at hfix; exact hfix
      exact this.symm
  rw [eq_top_iff]
  intro y _
  have hy : (x : ModGL .G2 K) * y * x⁻¹ ∈ H :=
    hle (mul_mem (mul_mem hx y.2) (inv_mem hx))
  obtain ⟨w, hw, hwy⟩ := hy
  have hwy' : w = y := by
    apply Subtype.ext
    have h1 : x * (w : ModGL .G2 K) * x⁻¹ = x * y * x⁻¹ := hwy
    have h2 := congrArg (fun t => x⁻¹ * t * x) h1
    simpa [mul_assoc] using h2
  rw [← hwy']
  exact hw

theorem g2ThreeUniNative_plus {K : Type} [Field K] [Finite K] (h3 : 3 ∣ Nat.card K + 1)
    (hK : 3 ≤ Nat.card K) (E₀ : Subgroup (adjointGroup .G2 K)) (hexp : ∀ x ∈ E₀, x ^ 3 = 1)
    (hcard : Nat.card E₀ = 3 ^ 2) :
    Subgroup.closure {k | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x ∧ ∃ n : ℕ, k ^ (ringChar K ^ n) = 1} = ⊤ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := finite_adjointGroup_G2 K
  have h3K : ¬ 3 ∣ Nat.card K := fun h => by omega
  have hE : IsElemAbelian 3 E₀ := ⟨IsPGroup.isMulCommutative_of_card_eq_prime_sq hcard, hexp⟩
  obtain ⟨P, hFP, z, hzF, hz1, hzp, hzc⟩ :=
    exists_sylow_central_in_plane (rankLE2_three_adjointGroup_G2 K h3K) hE hcard
  obtain ⟨e, heF, hez⟩ : ∃ e ∈ E₀, e ∉ Subgroup.zpowers z := by
    by_contra hne
    push Not at hne
    have h1 : Nat.card E₀ ≤ Nat.card (Subgroup.zpowers z) := Subgroup.card_le_of_le hne
    rw [Nat.card_zpowers] at h1
    have h2 : orderOf z ≤ 3 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hzp)
    omega
  have he1 : e ≠ 1 := fun h => hez (h ▸ one_mem _)
  obtain ⟨x, hxz, hxe⟩ := CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding.g2SylowPairNormalForm_of_instances
    K hK h3 P z (hFP hzF) hzc hz1 hzp e (hFP heF) he1 (hexp e heF) hez
  set S := {k : adjointGroup .G2 K | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x ∧
    ∃ n : ℕ, k ^ (ringChar K ^ n) = 1} with hS
  have hconj : ∀ k w : adjointGroup .G2 K, Commute k (x * w * x⁻¹) → Commute (x⁻¹ * k * x) w := by
    intro k w h
    have h1 : k * (x * w * x⁻¹) = (x * w * x⁻¹) * k := h.eq
    show x⁻¹ * k * x * w = w * (x⁻¹ * k * x)
    calc x⁻¹ * k * x * w = x⁻¹ * (k * (x * w * x⁻¹)) * x := by group
      _ = x⁻¹ * ((x * w * x⁻¹) * k) * x := by rw [h1]
      _ = w * (x⁻¹ * k * x) := by group
  have hpow : ∀ (k : adjointGroup .G2 K) (n : ℕ), k ^ (ringChar K ^ n) = 1 →
      (x⁻¹ * k * x) ^ (ringChar K ^ n) = 1 := by
    intro k n hn
    rw [show x⁻¹ * k * x = (MulAut.conj x⁻¹) k by simp [MulAut.conj_apply], ← map_pow, hn, map_one]
  have hle : Subgroup.closure {k : adjointGroup .G2 K | (Commute k (zStd K) ∨ Commute k (eStd K)) ∧
      ∃ n : ℕ, k ^ (ringChar K ^ n) = 1} ≤ (Subgroup.closure S).map (MulAut.conj x).toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro k ⟨hk, n, hn⟩
    refine ⟨x⁻¹ * k * x, Subgroup.subset_closure ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    rcases hk with hk | hk
    · refine ⟨z, hzF, hz1, hconj k z ?_, n, hpow k n hn⟩
      rcases hxz with h | h <;> rw [h]
      exacts [hk, hk.inv_right]
    · refine ⟨e, heF, he1, hconj k e ?_, n, hpow k n hn⟩
      rcases hxe with h | h <;> rw [h]
      exacts [hk, hk.inv_right]
  rw [g2UniStdPair_closure_eq_top h3 hK, top_le_iff] at hle
  rw [eq_top_iff]
  intro y _
  have hy : x * y * x⁻¹ ∈ (Subgroup.closure S).map (MulAut.conj x).toMonoidHom := by
    rw [hle]; exact Subgroup.mem_top _
  obtain ⟨w, hw, hwy⟩ := hy
  have hwy' : w = y := by
    have h1 : x * w * x⁻¹ = x * y * x⁻¹ := by simpa [MulAut.conj_apply] using hwy
    have h2 := congrArg (fun t => x⁻¹ * t * x) h1
    simpa [mul_assoc] using h2
  rw [← hwy']
  exact hw

theorem g2ThreeNormalizesR_minus {K : Type} [Field K] [Finite K] (h3 : 3 ∣ Nat.card K - 1)
    (E₀ : Subgroup (adjointGroup .G2 K)) (hexp : ∀ x ∈ E₀, x ^ 3 = 1) (hcard : Nat.card E₀ = 3 ^ 2) :
    ∃ R : Subgroup (adjointGroup .G2 K), R ≠ ⊥ ∧ IsPGroup (ringChar K) R ∧
      ∀ g ∈ E₀, R.map (MulAut.conj g).toMonoidHom = R := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hr, -⟩ := FiniteField.card K (ringChar K)
  haveI : Fact (ringChar K).Prime := ⟨hr⟩
  haveI : CharP K (ringChar K) := ringChar.charP K
  obtain ⟨ω, hω1, hω3⟩ : ∃ ω : K, ω ≠ 1 ∧ ω ^ 3 = 1 := by
    have h3' : 3 ∣ Nat.card Kˣ := by
      rw [Nat.card_units]
      exact h3
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 3 h3'
    refine ⟨(u : K), ?_, ?_⟩
    · intro h
      have : u = 1 := Units.ext h
      rw [this, orderOf_one] at hu
      omega
    · have := pow_orderOf_eq_one u
      rw [hu] at this
      exact congrArg Units.val this |>.trans (by simp)
  have hω : ω ^ 2 + ω + 1 = 0 := by
    have h0 : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by linear_combination hω3
    exact (mul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 hω1)
  obtain ⟨ι, hι, -⟩ := CFSG.GH74.GLS.Stage2.Bender.Thm1.exists_a2Hom_injective (K := K)
  have hEp : IsPGroup 3 E₀ := IsPGroup.of_card hcard
  obtain ⟨y, hy⟩ := CFSG.GH74.GLS.Stage2.Bender.Thm1.exists_conj_le_range_of_three_dvd_sub_one h3 ι hι E₀ hEp
  have hcomm₀ : ∀ a ∈ E₀, ∀ b ∈ E₀, a * b = b * a := by
    intro a ha b hb
    have := IsPGroup.commutative_of_card_eq_prime_sq hcard ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg Subtype.val this
  set Et := (E₀.map (MulAut.conj y).toMonoidHom).comap ι with hEt
  have hmemEt : ∀ t, t ∈ Et ↔ ι t ∈ E₀.map (MulAut.conj y).toMonoidHom := fun t => Iff.rfl
  have hE3 : ∀ t ∈ Et, t ^ 3 = 1 := by
    intro t ht
    obtain ⟨a, ha, hat⟩ := (hmemEt t).1 ht
    apply hι
    rw [map_pow, map_one, ← hat, ← map_pow, hexp a ha, map_one]
  have hEcomm : ∀ t ∈ Et, ∀ t' ∈ Et, t * t' = t' * t := by
    intro t ht t' ht'
    obtain ⟨a, ha, hat⟩ := (hmemEt t).1 ht
    obtain ⟨b, hb, hbt⟩ := (hmemEt t').1 ht'
    apply hι
    rw [map_mul, map_mul, ← hat, ← hbt, ← map_mul, ← map_mul, hcomm₀ a ha b hb]
  obtain ⟨R, hRr, hR1, hRn⟩ :=
    CFSG.GH74.GLS.Stage2.Bender.Thm1.exists_pGroup_normalized_of_commuting_cube_one (ringChar K) ω hω Et
      hE3 hEcomm
  refine ⟨(R.map ι).map (MulAut.conj y⁻¹).toMonoidHom, ?_, ?_, ?_⟩
  · intro h
    rw [Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj y⁻¹).injective,
      Subgroup.map_eq_bot_iff_of_injective _ hι] at h
    exact hR1 h
  · exact (hRr.map ι).map _
  · intro g hg
    obtain ⟨t, ht⟩ := hy ⟨g, hg, rfl⟩
    have htEt : t ∈ Et := by
      rw [hmemEt, ht]
      exact ⟨g, hg, rfl⟩
    have htN : R.map (MulAut.conj t).toMonoidHom = R :=
      Subgroup.mem_normalizer_iff_map_conj_eq.1 (hRn htEt)
    have ht' : ι t = y * g * y⁻¹ := by
      rw [ht]
      simp [MulAut.conj_apply]
    have hcomp : ((MulAut.conj g).toMonoidHom.comp (MulAut.conj y⁻¹).toMonoidHom).comp ι =
        ((MulAut.conj y⁻¹).toMonoidHom.comp ι).comp (MulAut.conj t).toMonoidHom := by
      refine MonoidHom.ext fun s => ?_
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [map_mul, map_mul, map_inv, ht']
      group
    calc ((R.map ι).map (MulAut.conj y⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom
        = R.map (((MulAut.conj g).toMonoidHom.comp (MulAut.conj y⁻¹).toMonoidHom).comp ι) := by
          rw [Subgroup.map_map, Subgroup.map_map]
      _ = R.map (((MulAut.conj y⁻¹).toMonoidHom.comp ι).comp (MulAut.conj t).toMonoidHom) := by
          rw [hcomp]
      _ = (R.map (MulAut.conj t).toMonoidHom).map ((MulAut.conj y⁻¹).toMonoidHom.comp ι) := by
          rw [Subgroup.map_map]
      _ = (R.map ι).map (MulAut.conj y⁻¹).toMonoidHom := by
          rw [htN, Subgroup.map_map]

theorem g2ThreeUniNative {K : Type} [Field K] [Finite K] (hnd : ¬ 3 ∣ Nat.card K) (hK : 3 ≤ Nat.card K)
    (E₀ : Subgroup (adjointGroup .G2 K)) (hexp : ∀ x ∈ E₀, x ^ 3 = 1) (hcard : Nat.card E₀ = 3 ^ 2)
    (hn : ¬ ∃ R : Subgroup (adjointGroup .G2 K), R ≠ ⊥ ∧ IsPGroup (ringChar K) R ∧
      ∀ g ∈ E₀, R.map (MulAut.conj g).toMonoidHom = R) :
    Subgroup.closure {k | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x ∧ ∃ n : ℕ, k ^ (ringChar K ^ n) = 1} = ⊤ := by
  rcases (by omega : 3 ∣ Nat.card K + 1 ∨ 3 ∣ Nat.card K - 1) with h | h
  · exact g2ThreeUniNative_plus h hK E₀ hexp hcard
  · exact absurd (g2ThreeNormalizesR_minus h E₀ hexp hcard) hn

end G2Three



section Transport

theorem uniClosure_eq_top_of_mulEquiv {G G' : Type*} [Group G] [Group G'] (ε : G ≃* G') (E : Subgroup G) {r : ℕ}
    (h : Subgroup.closure {k : G' | ∃ x ∈ E.map ε.toMonoidHom, x ≠ 1 ∧ Commute k x ∧
      ∃ n : ℕ, k ^ (r ^ n) = 1} = ⊤) :
    Subgroup.closure {k : G | ∃ x ∈ E, x ≠ 1 ∧ Commute k x ∧ ∃ n : ℕ, k ^ (r ^ n) = 1} = ⊤ := by
  set S := {k : G | ∃ x ∈ E, x ≠ 1 ∧ Commute k x ∧ ∃ n : ℕ, k ^ (r ^ n) = 1} with hS
  have himg : {k : G' | ∃ x ∈ E.map ε.toMonoidHom, x ≠ 1 ∧ Commute k x ∧ ∃ n : ℕ, k ^ (r ^ n) = 1} =
      ε.toMonoidHom '' S := by
    ext k
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, hx1, hkx, n, hn⟩
      refine ⟨ε.symm k, ⟨x, hx, fun h => hx1 (by rw [h]; exact map_one _), ?_, n, ?_⟩, by simp⟩
      · have := hkx.map ε.symm.toMonoidHom
        simpa using this
      · rw [← map_pow, hn, map_one]
    · rintro ⟨k₀, ⟨x, hx, hx1, hkx, n, hn⟩, rfl⟩
      exact ⟨ε x, ⟨x, hx, rfl⟩, fun h => hx1 (ε.injective (h.trans (map_one ε).symm)),
        hkx.map ε.toMonoidHom, n, by rw [← map_pow, hn, map_one]⟩
  rw [himg, ← MonoidHom.map_closure] at h
  rw [eq_top_iff]
  intro y _
  have hy : ε.toMonoidHom y ∈ (Subgroup.closure S).map ε.toMonoidHom := by
    rw [h]; exact Subgroup.mem_top _
  obtain ⟨w, hw, hwy⟩ := hy
  rwa [ε.injective hwy] at hw

end Transport

section G2Five

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.SEITZ3 CFSG.RankThree.PartOne.SEITZ11.G2Seven

set_option linter.unusedSectionVars false


theorem g2UniQPlus_closure_eq_top (X : Type) [Field X] [Finite X] (hX : Odd (Nat.card X))
    (h5 : 5 ≤ Nat.card X) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card X + 1)
    (E₁ : Subgroup (adjointGroup Tag.G2 X)) (hE₁p : ∀ x ∈ E₁, x ^ p = 1)
    (hE₁c : Nat.card E₁ = p ^ 2) :
    Subgroup.closure {k | ∃ x ∈ E₁, x ≠ 1 ∧ Commute k x ∧ ∃ n : ℕ, k ^ (ringChar X ^ n) = 1} = ⊤ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have : Fintype X := Fintype.ofFinite X
  obtain ⟨nX, hrX, hXcard⟩ := FiniteField.card X (ringChar X)
  haveI : Fact (ringChar X).Prime := ⟨hrX⟩
  have hrdvd : ringChar X ∣ Nat.card X := by
    rw [Nat.card_eq_fintype_card, hXcard]
    exact dvd_pow_self _ nX.ne_zero
  obtain ⟨K₂, hF₂, hfin₂, hAlg, σ, hdeg, hσ⟩ := exists_quadratic_ext (K := X)
  obtain ⟨g, z, hg, -, hzdef, ⟨hz, hw⟩, hΓ, -, -, ⟨S₀, hS₀⟩, ⟨E, hEmem, hEle, hEcard, -, -⟩,
      hRq, -, hcent⟩ :=
    odd_G2_qplus_toral_Sylow_and_fixed_root_centralizers X hX hp (by omega) hpq K₂ hdeg σ hσ
  have hGEN := g2_qplus_generation hX h5 K₂ hdeg σ hσ hg hzdef hz hw
  have : Finite (ModGL Tag.G2 K₂) := finite_modGL
  let Γ : Subgroup (ModGL Tag.G2 K₂) := conjEntrywiseImage X g
  have hEΓ : E ≤ Γ := fun x hx => (hEle hx).2
  have hmapE : (torsionParams K₂ p).map (rootDiagUnitHom Tag.G2 K₂) = E := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine (hEmem _).2 ⟨rootDiagUnit_mem_torusGroup_G2 a, ?_⟩
      show rootDiagUnit Tag.G2 a ^ p = 1
      have hap : a ^ p = 1 := funext fun i => mem_torsionParams.1 ha i
      rw [rootDiagUnit_pow, hap, rootDiagUnit_one]
    · intro hx
      obtain ⟨hxT, hxp⟩ := (hEmem x).1 hx
      obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hxT
      refine ⟨a, ?_, rfl⟩
      have h1 : rootDiagUnit Tag.G2 (a ^ p) = rootDiagUnit Tag.G2 (1 : Fin Tag.G2.rank → K₂ˣ) := by
        rw [← rootDiagUnit_pow, hxp, rootDiagUnit_one]
      have h2 : a ^ p = 1 := rootDiagUnit_injective h1
      exact mem_torsionParams.2 fun i => congrFun h2 i
  have hcardAp : Nat.card (torsionParams K₂ p) = p ^ 2 := by
    rw [← hEcard, ← hmapE]
    exact (Subgroup.card_map_of_injective rootDiagUnit_injective).symm
  set T : Set Γ := {k | ∃ x ∈ E.subgroupOf Γ, x ≠ 1 ∧ Commute k x ∧
    ∃ n : ℕ, k ^ (ringChar X ^ n) = 1} with hT
  have hroot : ∀ β, IsRoot Tag.G2 β →
      rootRankOneGroup Tag.G2 K₂ β ⊓ Γ ≤ (Subgroup.closure T).map Γ.subtype := by
    intro β hβ
    obtain ⟨a, haT, ha1, hachar⟩ := exists_ker hp hcardAp β
    have hxE : rootDiagUnit Tag.G2 a ∈ E := hmapE ▸ ⟨a, haT, rfl⟩
    have hxTΓ := hEle hxE
    have hxp : rootDiagUnit Tag.G2 a ^ p = 1 := ((hEmem _).1 hxE).2
    have hx1 : rootDiagUnit Tag.G2 a ≠ 1 := fun h =>
      ha1 (rootDiagUnit_injective (h.trans rootDiagUnit_one.symm))
    have hord : orderOf (rootDiagUnit Tag.G2 a) = p := orderOf_eq_prime hxp hx1
    obtain ⟨-, hne⟩ := hcent a hxTΓ hord
    have hker : rootCharKernel a ≠ ∅ := Set.nonempty_iff_ne_empty.1 ⟨β, hβ, hachar⟩
    obtain ⟨α, hα, hkerα, hcomm, -⟩ := hne hker
    have hβα : β = α ∨ β = -α := by
      have : β ∈ rootCharKernel a := ⟨hβ, hachar⟩
      rw [hkerα] at this
      simpa using this
    have hRβ : rootRankOneGroup Tag.G2 K₂ β = rootRankOneGroup Tag.G2 K₂ α := by
      rcases hβα with rfl | rfl
      · rfl
      · exact CFSG.RankThree.PartOne.KE.rootRankOneGroup_neg hα
    have hRD : rootRankOneGroup Tag.G2 K₂ β ⊓ Γ ≤
        Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.G2 a} := by
      rw [hRβ, ← hcomm]
      exact commutator_self_le _
    obtain ⟨P, hP, hqs⟩ := hRq β hβ
    have hcardR : ringChar X ∣ Nat.card (rootRankOneGroup Tag.G2 K₂ β ⊓ Γ : Subgroup _) := by
      obtain ⟨φ⟩ := CFSG.RankThree.Chevalley.EvenF4QPlus.nonempty_mulEquiv_SL2_of_rootSL2_comap_eq (K := X) (K₂ := K₂)
        (inf_le_left : rootRankOneGroup Tag.G2 K₂ β ⊓ Γ ≤ _) hP
      rw [Nat.card_congr φ.toEquiv, CFSG.RankThree.PartOne.K159.card_SL_eq_mul (by norm_num)]
      have h21 : (2 * (2 - 1) / 2 : ℕ) = 1 := rfl
      rw [h21, pow_one]
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hrdvd _) _
    have hgen := le_closure_pow_of_quasisimple (r := ringChar X) hqs hcardR
    refine hgen.trans ((Subgroup.closure_le _).2 ?_)
    rintro y ⟨hy, n, hn⟩
    have hyD := hRD hy
    refine ⟨⟨y, hyD.1⟩, Subgroup.subset_closure ⟨⟨rootDiagUnit Tag.G2 a, hxTΓ.2⟩, ?_, ?_, ?_, n, ?_⟩,
      rfl⟩
    · exact Subgroup.mem_subgroupOf.2 hxE
    · intro h
      exact hx1 (congrArg Subtype.val h)
    · exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 hyD.2)
    · exact Subtype.ext (by simpa using hn)
  have hC : Subgroup.closure T = ⊤ := by
    rw [eq_top_iff]
    intro γ _
    have h1 : (γ : ModGL Tag.G2 K₂) ∈ ⨆ α : {α : Fin Tag.G2.rank → ℤ // IsRoot Tag.G2 α},
        rootRankOneGroup Tag.G2 K₂ α.1 ⊓ Γ := by
      rw [hGEN]
      exact γ.2
    have hle : ⨆ α : {α : Fin Tag.G2.rank → ℤ // IsRoot Tag.G2 α},
        rootRankOneGroup Tag.G2 K₂ α.1 ⊓ Γ ≤ (Subgroup.closure T).map Γ.subtype :=
      iSup_le fun α => hroot α.1 α.2
    obtain ⟨c, hc, hcγ⟩ := hle h1
    have : c = γ := Subtype.ext hcγ
    exact this ▸ hc
  let ψ : ModGL Tag.G2 X →* ModGL Tag.G2 K₂ :=
    (MulAut.conj g).toMonoidHom.comp (baseChangeGL (algebraMap X K₂))
  have hψ : Function.Injective ψ :=
    (MulAut.conj g).injective.comp (baseChangeGL_injective (τ := Tag.G2) (algebraMap X K₂))
  let ε : adjointGroup Tag.G2 X ≃* Γ := Subgroup.equivMapOfInjective (adjointGroup Tag.G2 X) ψ hψ
  refine uniClosure_eq_top_of_mulEquiv ε E₁ ?_
  have hF : ∀ y ∈ E₁.map ε.toMonoidHom, y ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hE₁p x hx, map_one]
  have hFc : Nat.card (E₁.map ε.toMonoidHom) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective ε.injective]
    exact hE₁c
  have hEc : Nat.card (E.subgroupOf Γ) = p ^ 2 := by
    rw [← hEcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEΓ).toEquiv
  obtain ⟨h, hFh⟩ := plane_conj S₀ hS₀ (E := E.subgroupOf Γ) (fun x hxT hxp => by
    have h1 : (x : ModGL Tag.G2 K₂) ∈ torusGroup Tag.G2 K₂ ⊓ Γ := hxT
    have h2 : (x : ModGL Tag.G2 K₂) ^ p = 1 := by
      have := congrArg Subtype.val hxp
      simpa using this
    exact (hEmem _).2 ⟨h1.1, h2⟩) hEc hF hFc
  rw [hFh]
  show Subgroup.closure {k | ∃ x ∈ (E.subgroupOf Γ).map (MulAut.conj h).toMonoidHom, x ≠ 1 ∧
    Commute k x ∧ ∃ n : ℕ, k ^ (ringChar X ^ n) = 1} = ⊤
  rw [uniClosure_map_conj, hC, Subgroup.map_top_of_surjective _ (MulAut.conj h).surjective]

end G2Five


section TriQPlus

open CFSG.LieType.Steinberg CFSG.LieType.Steinberg.TwistedD4 CFSG.RankThree.PartOne.SEITZ3
  CFSG.RankThree.PartOne.K1214 CFSG.RankThree.PartOne.SEITZ11.G2Seven CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Universal CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

set_option linter.unusedSectionVars false


theorem sl2_closure_pow_ringChar_eq_top (F : Type) [Field F] :
    Subgroup.closure {x : Matrix.SpecialLinearGroup (Fin 2) F | x ^ ringChar F = 1} = ⊤ := by
  have h := Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field (ι := Fin 2)
    (K := F)
  rw [eq_top_iff, ← h, Subgroup.closure_le]
  rintro _ ⟨t, rfl⟩
  refine Subgroup.subset_closure ?_
  show t.toSpecialLinearGroup ^ ringChar F = 1
  rw [Matrix.TransvectionStruct.toSpecialLinearGroup_def,
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311c.transvection_pow_ringChar]

theorem uniClosure_twistedGroup_qplus {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (hσ3 : ∀ c, σ (σ (σ c)) = c) (hK2 : ringChar K ≠ 2) {q : ℕ} (hq : 2 ≤ q)
    (hK : Nat.card K = q ^ 3) (hσq : ∀ c, σ c = c ^ q) (hqodd : Odd q)
    {p e : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (hpq : p ∣ q + 1)
    (hshape : SylowShape p 2 e (twistedGroup σ.toRingHom))
    (F : Subgroup (twistedGroup σ.toRingHom)) (hFp : ∀ x ∈ F, x ^ p = 1)
    (hFc : Nat.card F = p ^ 2) :
    Subgroup.closure {k | ∃ x ∈ F, x ≠ 1 ∧ Commute k x ∧ ∃ n : ℕ, k ^ (ringChar K ^ n) = 1} = ⊤ := by
  classical
  have hp : p.Prime := Fact.out
  have hσ3' : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c := hσ3
  have hcardF : Nat.card (fixedField σ.toRingHom) = q :=
    CFSG.GH74.GLS.Stage4.Hex.card_fixedField_of_cube σ.toRingHom hq hK hσq
  have hcardX : Nat.card (fixSubfield σ) = q := hcardF
  obtain ⟨M, hM⟩ := exists_sl2_orderOf (fixedField σ.toRingHom) (p := p)
    (by rw [hcardF]; exact hpq)
  let nh : twistedGroup σ.toRingHom := nHat σ.toRingHom (ng 0) * nHat σ.toRingHom (ng 1)
  let b : twistedGroup σ.toRingHom := slLong σ.toRingHom hσ3' M
  let b₀ : twistedGroup σ.toRingHom := nh * b * nh⁻¹
  let L : Matrix.SpecialLinearGroup (Fin 2) K :=
    Matrix.SpecialLinearGroup.map (fixedField σ.toRingHom).subtype M
  let v : twistedGroup σ.toRingHom := slShort σ.toRingHom hσ3' L
  have hLfix : Matrix.SpecialLinearGroup.map σ.toRingHom L = L := by
    refine Subtype.ext ?_
    ext i j
    simp only [L, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply]
    exact (M.1 i j).2
  have hnhJ : nh ∈ FixedSub σ :=
    mul_mem (nHat_zero_mem_FixedSub σ hσ3) (nHat_one_mem_FixedSub σ hσ3)
  have hbJ : b ∈ FixedSub σ := slLong_mem_FixedSub σ hσ3 M
  have hb₀J : b₀ ∈ FixedSub σ := mul_mem (mul_mem hnhJ hbJ) (inv_mem hnhJ)
  have hvJ : v ∈ FixedSub σ := slShort_mem_FixedSub σ hσ3 L hLfix
  have hob : orderOf b = p := by
    rw [orderOf_injective (slLong σ.toRingHom hσ3') (slLong_injective hσ3') M, hM]
  have hob₀ : orderOf b₀ = p := by
    have := orderOf_injective (MulAut.conj nh).toMonoidHom (MulAut.conj nh).injective b
    rw [← hob]
    exact this
  have hoL : orderOf L = p := by
    rw [orderOf_injective (Matrix.SpecialLinearGroup.map (n := Fin 2)
      (fixedField σ.toRingHom).subtype) (sl_map_injective _) M, hM]
  have hov : orderOf v = p := by
    rw [orderOf_injective (slShort σ.toRingHom hσ3') (slShort_injective hσ3') L, hoL]
  have hb₀theta : ((b₀ : twistedGroup σ.toRingHom) : adjointGroup d4 K) ∈
      (thetaGroup : Subgroup (adjointGroup d4 K)) := by
    have e : ((b₀ : twistedGroup σ.toRingHom) : adjointGroup d4 K) =
        (nHatE K (ng 0) * nHatE K (ng 1)) * (b : adjointGroup d4 K) *
          (nHatE K (ng 0) * nHatE K (ng 1))⁻¹ := by
      have hn0 : (nHat σ.toRingHom (ng 0) : adjointGroup d4 K) = nHatE K (ng 0) := nHat_val _ _
      have hn1 : (nHat σ.toRingHom (ng 1) : adjointGroup d4 K) = nHatE K (ng 1) := nHat_val _ _
      simp only [b₀, nh, Subgroup.coe_mul, Subgroup.coe_inv, hn0, hn1, mul_assoc, mul_inv_rev]
    rw [e]
    exact conj_mem_thetaGroup (slLong_coe_mem_central σ.toRingHom hσ3' M)
  have hAb : ∀ a ∈ (slShort σ.toRingHom hσ3').range, a * b₀ = b₀ * a := by
    rintro _ ⟨B, rfl⟩
    refine Subtype.ext ?_
    exact (commute_thetaGroup_outerRankOne hb₀theta
      (slShort_coe_mem_outer σ.toRingHom hσ3' B)).eq.symm
  have hcomm : Commute b₀ v := (hAb v ⟨L, rfl⟩).symm
  have hnot : v ∉ Subgroup.zpowers b₀ := by
    intro hv'
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hv'
    have hLc : L ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) := by
      rw [Subgroup.mem_center_iff]
      intro B
      apply slShort_injective hσ3'
      rw [map_mul, map_mul]
      have h1 : Commute b₀ (slShort σ.toRingHom hσ3' B) := (hAb _ ⟨B, rfl⟩).symm
      have h2 := (h1.zpow_left i).eq
      rw [hi] at h2
      exact h2.symm
    have h2 := CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.sq_eq_one_of_mem_center hLc
    have h3 : orderOf L ∣ 2 := orderOf_dvd_of_pow_eq_one h2
    rw [hoL] at h3
    have := Nat.le_of_dvd (by norm_num) h3
    omega
  obtain ⟨E₀, hbE, hvE, hE₀p, hE₀c, hE₀le⟩ := exists_plane_of_commute hob₀ hov hcomm hnot
  have hE₀J : E₀ ≤ FixedSub σ := hE₀le _ hb₀J hvJ
  have hk3 : (3 : ℕ∞) ≤ ENat.card (fixSubfield σ) := by
    have h1 : p ≤ q + 1 := Nat.le_of_dvd (Nat.succ_pos _) hpq
    have h2 : 3 ≤ Nat.card (fixSubfield σ) := by omega
    have : Finite (fixSubfield σ) := inferInstance
    rw [ENat.card_eq_coe_natCard]
    exact_mod_cast h2
  let ε : ↥(FixedSub σ) ≃* ↥(adjointGroup Tag.G2 (fixSubfield σ)) :=
    (fixedSubEquivJ σ hK2 hq hK hσq hσ3).trans (trialityFieldImageEquivG2 σ hk3)
  have hkchar : ringChar (fixSubfield σ) = ringChar K := Algebra.ringChar_eq (fixSubfield σ) K
  set T : Set (twistedGroup σ.toRingHom) := {k | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x ∧
    ∃ n : ℕ, k ^ (ringChar K ^ n) = 1} with hT
  have hJgen : Subgroup.closure {k : FixedSub σ | ∃ x ∈ E₀.subgroupOf (FixedSub σ), x ≠ 1 ∧
      Commute k x ∧ ∃ n : ℕ, k ^ (ringChar K ^ n) = 1} = ⊤ := by
    refine uniClosure_eq_top_of_mulEquiv ε _ ?_
    have h5 : 5 ≤ Nat.card (fixSubfield σ) := by
      have h1 : p ≤ q + 1 := Nat.le_of_dvd (Nat.succ_pos _) hpq
      obtain ⟨m, hm⟩ := hqodd
      omega
    have := g2UniQPlus_closure_eq_top (fixSubfield σ) (by rw [hcardX]; exact hqodd) h5 hp hp5
      (by rw [hcardX]; exact hpq) ((E₀.subgroupOf (FixedSub σ)).map ε.toMonoidHom) (by
        rintro _ ⟨y, hy, rfl⟩
        rw [← map_pow]
        have : y ^ p = 1 := Subtype.ext (hE₀p _ hy)
        rw [this, map_one]) (by
        rw [Subgroup.card_map_of_injective ε.injective, ← hE₀c]
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE₀J).toEquiv)
    rwa [hkchar] at this
  have hJle : FixedSub σ ≤ Subgroup.closure T := by
    have h1 : (Subgroup.closure {k : FixedSub σ | ∃ x ∈ E₀.subgroupOf (FixedSub σ), x ≠ 1 ∧
        Commute k x ∧ ∃ n : ℕ, k ^ (ringChar K ^ n) = 1}).map (FixedSub σ).subtype ≤
        Subgroup.closure T := by
      rw [MonoidHom.map_closure]
      refine Subgroup.closure_mono ?_
      rintro _ ⟨k, ⟨x, hx, hx1, hk, n, hn⟩, rfl⟩
      refine ⟨(x : twistedGroup σ.toRingHom), hx, fun h => hx1 (Subtype.ext h), ?_, n, ?_⟩
      · exact Subtype.ext_iff.1 hk.eq
      · have := congrArg Subtype.val hn
        rw [Subgroup.coe_subtype]
        exact this
    rw [hJgen, Subgroup.map_top, Subgroup.range_subtype] at h1
    exact h1
  have hb₀1 : b₀ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hob₀
    exact hp.one_lt.ne hob₀
  have hAle : (slShort σ.toRingHom hσ3').range ≤ Subgroup.closure T := by
    rintro _ ⟨B, rfl⟩
    have hB : B ∈ Subgroup.closure {x : Matrix.SpecialLinearGroup (Fin 2) K | x ^ ringChar K = 1} := by
      rw [sl2_closure_pow_ringChar_eq_top]
      exact Subgroup.mem_top B
    have h1 := Subgroup.mem_map_of_mem (slShort σ.toRingHom hσ3') hB
    rw [MonoidHom.map_closure] at h1
    refine Subgroup.closure_mono ?_ h1
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨b₀, hbE, hb₀1, hAb _ ⟨x, rfl⟩, 1, by rw [pow_one, ← map_pow, hx, map_one]⟩
  have hJA : FixedSub σ ⊔ (slShort σ.toRingHom hσ3').range = ⊤ := by
    have h := CFSG.ClassicalInvolution.G2D4Models.range_slLong_sup_range_slShort hσ3'
    rw [eq_top_iff, ← h]
    refine sup_le_sup_right ?_ _
    rintro _ ⟨A, rfl⟩
    exact slLong_mem_FixedSub σ hσ3 A
  have htop₀ : Subgroup.closure T = ⊤ := by
    rw [eq_top_iff, ← hJA]
    exact sup_le hJle hAle
  haveI : Finite (CFSG.Blueprint.Chevalley.ModGL TwistTag.D4.tag K) := finite_modGL
  have hE₀p' : IsPGroup p E₀ := IsPGroup.of_card (n := 2) hE₀c
  obtain ⟨S, hS⟩ := hE₀p'.exists_le_sylow
  obtain ⟨g, hg⟩ := plane_conj S (T := (S : Subgroup (twistedGroup σ.toRingHom))) le_rfl
    (E := E₀) (eq_of_pow_eq_one_of_sylowShape hshape S hS hE₀c hE₀p) hE₀c hFp hFc
  rw [hg]
  show Subgroup.closure {k | ∃ x ∈ E₀.map (MulAut.conj g).toMonoidHom, x ≠ 1 ∧ Commute k x ∧
    ∃ n : ℕ, k ^ (ringChar K ^ n) = 1} = ⊤
  rw [uniClosure_map_conj, htop₀, Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective]

theorem uniClosure_graphFixed_D4_qplus (ℓ f : ℕ) (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hℓ2 : ℓ ≠ 2)
    (X : Type) [Field X] [Finite X] [CharP X ℓ] (hX : Nat.card X = (ℓ ^ f) ^ 3)
    (σ : X ≃+* X) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p)
    (hpq : p ∣ ℓ ^ f + 1) (E₁ : Subgroup (graphFixedRootGroup TwistTag.D4 X σ.toRingHom))
    (hE₁p : ∀ x ∈ E₁, x ^ p = 1) (hcard : Nat.card E₁ = p ^ 2) :
    Subgroup.closure {k | ∃ x ∈ E₁, x ≠ 1 ∧ Commute k x ∧ ∃ n : ℕ, k ^ (ringChar X ^ n) = 1} = ⊤ := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hq2 : 2 ≤ ℓ ^ f := by
    calc 2 ≤ ℓ := hℓ.two_le
      _ = ℓ ^ 1 := (pow_one ℓ).symm
      _ ≤ ℓ ^ f := Nat.pow_le_pow_right hℓ.pos hf
  have hX2 : ringChar X ≠ 2 := by rw [ringChar.eq X ℓ]; exact hℓ2
  have hodd : Odd (ℓ ^ f) := (hℓ.odd_of_ne_two hℓ2).pow
  have hσ3 : ∀ c, σ (σ (σ c)) = c :=
    CFSG.LieType.Steinberg.TwistedD4.sigma_three_of_card (σ := σ.toRingHom) hX hσ
  let ε := (twistedEquivRoot σ hX2 hq2 hX hσ).symm
  have hshape : SylowShape p 2 ((ℓ ^ f + 1).factorization p) (twistedGroup σ.toRingHom) :=
    SylowShape.of_mulEquiv (twistedEquivRoot σ hX2 hq2 hX hσ)
      (CFSG.RankThree.PartOne.K128.sylowShape_D4_qplus hf X hX σ hσ (Fact.out) hp5 hpq)
  refine uniClosure_eq_top_of_mulEquiv ε E₁ ?_
  exact uniClosure_twistedGroup_qplus σ hσ3 hX2 hq2 hX hσ hodd hp5 hpq hshape (E₁.map ε.toMonoidHom)
    (by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hE₁p x hx, map_one]) (by rw [Subgroup.card_map_of_injective ε.injective, hcard])


theorem subgroupOf_borel_le_normalizer_posUnipotent_D4 {K : Type} [Field K] (σ : K →+* K) :
    (graphFixedRootBorel TwistTag.D4 K σ).subgroupOf (graphFixedRootGroup TwistTag.D4 K σ) ≤
      Subgroup.normalizer (((graphFixedPosUnipotent TwistTag.D4 K σ).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ) : Subgroup (graphFixedRootGroup TwistTag.D4 K σ)) :
          Set (graphFixedRootGroup TwistTag.D4 K σ)) := by
  intro b hb
  have hbN := graphFixedRootBorel_le_normalizer_graphFixedPosUnipotent (t := TwistTag.D4) (K := K)
    (σ := σ) (Subgroup.mem_subgroupOf.1 hb)
  rw [Subgroup.mem_normalizer_iff] at hbN ⊢
  intro w
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  simpa using hbN (w : CFSG.Blueprint.Chevalley.ModGL TwistTag.D4.tag K)

theorem normalizesRSubgroup_trialityD4_of_dvd_sub_one (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ q.card - 1) {E : Subgroup (MulAut (CFSG.LieType.SeitzGeneration.Cat ⟨.trialityD4 q, hv⟩))}
    (hEp : IsPGroup p E) (hin : InnerPlane ⟨.trialityD4 q, hv⟩ p E) :
    NormalizesRSubgroup ⟨.trialityD4 q, hv⟩ E := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨K, _, _, σ, hK, hσ, -, ⟨e⟩⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_catEquiv_trialityD4 q hv
  have hK3 : Nat.card K = q.p ^ (q.exponent * 3) := by rw [hK, pow_mul]
  haveI : CharP K q.p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic q.prime_p (by
      have := q.exponent_pos; omega) hK3
  haveI : Finite (CFSG.Blueprint.Chevalley.ModGL TwistTag.D4.tag K) := finite_modGL
  have hZ : Subgroup.center ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  have hinj := conj_injective_of_mulEquiv e
    (CFSG.LieType.SeitzGeneration.conj_injective_of_center_eq_bot hZ)
  have hpq' : p ∣ q.p ^ q.exponent - 1 := by rw [← TauCeti.PrimePower.card_def]; exact hpq
  have hidx := CFSG.RankThree.PartOne.CTP.not_dvd_index_borel_D4 q.p q.exponent q.prime_p
    q.exponent_pos K hK σ hσ p hp hp5 hpq'
  obtain ⟨-, -, hU⟩ := triality_both_orientations_exact_finite_order q.p q.exponent q.prime_p
    q.exponent_pos K hK 1 (Or.inl rfl) σ.toRingHom (by simpa using hσ)
  have hcardQ : Nat.card ((graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) = (q.p ^ q.exponent) ^ 12 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (graphFixedPosUnipotent_le_graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).toEquiv, hU]
  have hQ0 : (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcardQ
    have : 1 < (q.p ^ q.exponent) ^ 12 :=
      Nat.one_lt_pow (by norm_num) (Nat.one_lt_pow q.exponent_pos.ne' q.prime_p.one_lt)
    omega
  have hQr : IsPGroup q.p ((graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :=
    IsPGroup.of_card (n := q.exponent * 12) (by rw [hcardQ, ← pow_mul])
  obtain ⟨R, hR0, hRr, hR⟩ := CFSG.LieType.SeitzGeneration.exists_normalized_of_inner e hidx
    (subgroupOf_borel_le_normalizer_posUnipotent_D4 σ.toRingHom) hQ0 hQr hinj hEp hin
  refine ⟨R, hR0, ?_, hR⟩
  simpa [TauCeti.LieTypeIndex.characteristic_trialityD4] using hRr

theorem uniSeitzPlanes_triality_inner_five :
    UniSeitzPlanes fun d p E => InnerPlane d p E ∧ 5 ≤ p ∧ d.1.characteristic ≠ 2 ∧
      ¬ NormalizesRSubgroup d E ∧ ∃ q : TauCeti.PrimePower, d.1 = .trialityD4 q ∧
        ¬ (p ∣ q.card ^ 2 + q.card + 1 ∨ p ∣ q.card ^ 2 - q.card + 1) := by
  rintro ⟨d, hv⟩ p hp hp2 hpd _ E hE hc ⟨hin, hp5, hch, hn, q, hq, h36⟩
  obtain rfl : d = .trialityD4 q := hq
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hpq : p ≠ q.p := fun h => hpd (h.trans (TauCeti.LieTypeIndex.characteristic_trialityD4 q).symm)
  have hq2 : q.p ≠ 2 := by
    intro h2
    apply hch
    rw [TauCeti.LieTypeIndex.characteristic_trialityD4, h2]
  have hq1 : 1 ≤ q.card := by rw [TauCeti.PrimePower.card_def]; exact Nat.one_le_pow _ _ q.prime_p.pos
  by_cases hm : p ∣ q.card - 1
  · exact absurd (normalizesRSubgroup_trialityD4_of_dvd_sub_one q hv hp hp5 hm hE.isPGroup hin) hn
  obtain ⟨K, _, _, σ, hK, hσ, -, ⟨e⟩⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_catEquiv_trialityD4 q hv
  have hK3 : Nat.card K = q.p ^ (q.exponent * 3) := by rw [hK, pow_mul]
  haveI : CharP K q.p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic q.prime_p (by
      have := q.exponent_pos; omega) hK3
  have hring : ringChar K = q.p := ringChar.eq K q.p
  have hZ : Subgroup.center ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  have hinj := conj_injective_of_mulEquiv e
    (CFSG.LieType.SeitzGeneration.conj_injective_of_center_eq_bot hZ)
  by_cases hp1 : p ∣ q.card + 1
  · have hpq' : p ∣ q.p ^ q.exponent + 1 := by rw [← TauCeti.PrimePower.card_def]; exact hp1
    have h := uniPlaneGen_of_native_uniClosure (p := p) (r := ringChar K) e hinj
      (fun E₀ h1 h2 _ => uniClosure_graphFixed_D4_qplus q.p q.exponent q.prime_p q.exponent_pos hq2 K hK
        σ hσ p hp5 hpq' E₀ h1 h2) hE hc hin ?_
    · rw [hring] at h
      simpa using h
    · rintro ⟨R, hR1, hRp, hRn⟩
      refine hn ⟨R, hR1, ?_, hRn⟩
      show IsPGroup (TauCeti.LieTypeIndex.trialityD4 q).characteristic R
      rw [TauCeti.LieTypeIndex.characteristic_trialityD4, ← hring]
      exact hRp
  · exfalso
    have hnd : ¬ p ∣ q.card ^ 6 - 1 := by
      intro hd
      have h6 : q.card ^ 6 - 1 = (q.card - 1) * ((q.card + 1) * ((q.card ^ 2 + q.card + 1) *
          (q.card ^ 2 - q.card + 1))) := by
        have hle : q.card ≤ q.card ^ 2 := Nat.le_self_pow (by norm_num) _
        zify [hq1, hle, Nat.one_le_pow 6 _ hq1]
        ring
      rw [h6] at hd
      rcases (Nat.Prime.dvd_mul hp).1 hd with h | hd
      · exact hm h
      rcases (Nat.Prime.dvd_mul hp).1 hd with h | hd
      · exact hp1 h
      rcases (Nat.Prime.dvd_mul hp).1 hd with h | h
      · exact h36 (Or.inl h)
      · exact h36 (Or.inr h)
    exact CFSG.LieType.SeitzGeneration.false_of_inner_plane_of_rankLE1 hp hinj
      (CFSG.HardMathSupport.Timmesfeld.CrossChar.rankLE1_cat_trialityD4 q hv hp hp2 hpq hnd) hE hc hin

end TriQPlus

section G2Cat

open CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport
  CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator

set_option linter.unusedSectionVars false


theorem uniSeitzPlanes_G2_inner_three :
    UniSeitzPlanes fun d p E => InnerPlane d p E ∧ p = 3 ∧ IsG2Index d.1 ∧ ¬ NormalizesRSubgroup d E := by
  rintro ⟨d, hv⟩ p hp hp2 hpd _ E hE hc ⟨hin, rfl, ⟨q, hq⟩, hn⟩
  obtain rfl : d = .G2 q := hq
  obtain ⟨K, _, _, hKq, hKchar, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 q hv
  have hring : ringChar K = q.p := ringChar.eq K q.p
  have hq3 : 3 ≠ q.p := fun h => hpd (h.trans (TauCeti.LieTypeIndex.characteristic_G2 q).symm)
  have hnd : ¬ 3 ∣ Nat.card K := by
    rw [hKq, TauCeti.PrimePower.card_def]
    intro hd
    exact hq3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three q.prime_p).1
      (Nat.prime_three.dvd_of_dvd_pow hd))
  have hK3 : 3 ≤ Nat.card K := by
    rw [hKq]
    exact (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have h := uniPlaneGen_of_native_uniClosure (p := 3) (r := ringChar K) e
    (conj_injective_of_mulEquiv e
      (CFSG.LieType.SeitzGeneration.conj_injective_of_center_eq_bot center_adjointGroup_eq_bot))
    (fun E₀ h1 h2 h3 => g2ThreeUniNative hnd hK3 E₀ h1 h2 h3) hE hc hin ?_
  · rw [hring] at h
    simpa using h
  · rintro ⟨R, hR1, hRp, hRn⟩
    refine hn ⟨R, hR1, ?_, hRn⟩
    show IsPGroup (TauCeti.LieTypeIndex.G2 q).characteristic R
    rw [TauCeti.LieTypeIndex.characteristic_G2, ← hring]
    exact hRp

theorem uniSeitzPlanes_G2_inner_five :
    UniSeitzPlanes fun d p E => InnerPlane d p E ∧ 5 ≤ p ∧ IsG2Index d.1 ∧ d.1.characteristic ≠ 2 ∧
      ¬ NormalizesRSubgroup d E := by
  rintro ⟨d, hv⟩ p hp hp2 hpd _ E hE hc ⟨hin, hp5, ⟨q, hq⟩, hch, hn⟩
  obtain rfl : d = .G2 q := hq
  by_cases hm : p ∣ q.card - 1
  · exact absurd (CFSG.HardMathSupport.Seitz.ExceptionsTransport.g2_innerPlane_normalizesR_of_dvd_sub_one q hv
      hp hp5 hm E hE hin) hn
  obtain ⟨K, _, _, hKq, hKchar, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 q hv
  have hring : ringChar K = q.p := ringChar.eq K q.p
  have hpq : p ≠ q.p := fun h => hpd (h.trans (TauCeti.LieTypeIndex.characteristic_G2 q).symm)
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hKq, TauCeti.PrimePower.card_def]
    intro hd
    exact hpq ((Nat.prime_dvd_prime_iff_eq hp q.prime_p).1 (hp.dvd_of_dvd_pow hd))
  have hq2 : q.p ≠ 2 := by
    intro h2
    apply hch
    rw [TauCeti.LieTypeIndex.characteristic_G2, h2]
  have hodd : Odd (Nat.card K) := by
    rw [hKq, TauCeti.PrimePower.card_def]
    exact (q.prime_p.eq_two_or_odd'.resolve_left hq2).pow
  have hm' : ¬ p ∣ Nat.card K - 1 := by rw [hKq]; exact hm
  have h := uniPlaneGen_of_native_uniClosure (p := p) (r := ringChar K) e
    (conj_injective_of_mulEquiv e
      (CFSG.LieType.SeitzGeneration.conj_injective_of_center_eq_bot center_adjointGroup_eq_bot))
    (fun E₀ h1 h2 _ => ?_) hE hc hin ?_
  · rw [hring] at h
    simpa using h
  · by_cases hp1 : p ∣ Nat.card K + 1
    · have h5 : 5 ≤ Nat.card K := by
        have hle := Nat.le_of_dvd (Nat.succ_pos _) hp1
        obtain ⟨k, hk⟩ := hodd
        omega
      exact g2UniQPlus_closure_eq_top K hodd h5 hp hp5 hp1 E₀ h1 h2
    · exfalso
      have hK1 : 1 ≤ Nat.card K := Nat.card_pos
      refine CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.false_of_isElemAbelian_sq_cyclotomic K hp hp5
        hpK (fun hd => ?_) h1 h2
      have hsq : Nat.card K ^ 2 - 1 = (Nat.card K - 1) * (Nat.card K + 1) := by
        zify [hK1, Nat.one_le_pow 2 _ hK1]
        ring
      rw [hsq] at hd
      rcases (Nat.Prime.dvd_mul hp).1 hd with hd | hd
      · exact hm' hd
      · exact hp1 hd
  · rintro ⟨R, hR1, hRp, hRn⟩
    refine hn ⟨R, hR1, ?_, hRn⟩
    show IsPGroup (TauCeti.LieTypeIndex.G2 q).characteristic R
    rw [TauCeti.LieTypeIndex.characteristic_G2, ← hring]
    exact hRp

theorem uniSeitzPlanes_G2_inner :
    UniSeitzPlanes fun d p E => InnerPlane d p E ∧ IsG2Index d.1 ∧ d.1.characteristic ≠ 2 ∧
      ¬ NormalizesRSubgroup d E := by
  intro d p hp hp2 hpd hex E hE hc ⟨hin, hg, hch, hn⟩
  rcases (by have := hp.two_le; omega : p = 3 ∨ p = 4 ∨ 5 ≤ p) with h3 | h4 | h5
  · exact uniSeitzPlanes_G2_inner_three d p hp hp2 hpd hex E hE hc ⟨hin, h3, hg, hn⟩
  · exact absurd (h4 ▸ hp) (by norm_num)
  · exact uniSeitzPlanes_G2_inner_five d p hp hp2 hpd hex E hE hc ⟨hin, h5, hg, hch, hn⟩

end G2Cat

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311g
