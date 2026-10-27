module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SingerOvergroupExclusion
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CosetNormalizerPGL3Eight
public import Mathlib.FieldTheory.Finite.GaloisField

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.CosetNormalizerSinger

open scoped LinearAlgebra.Projectivization
open Projectivization Module MulAction CFSG.ShultStronglyClosedTI.Singer

universe u

theorem eq_three_of_sum_pow_dvd {s m : ℕ} (hs : 1 ≤ s) (hm : 3 ≤ m) (h4 : 4 ≤ s * m)
    (hdvd : (∑ i ∈ Finset.range (m - 1), (2 ^ s) ^ i) ∣ s * m) : s = 3 ∧ m = 3 := by
  have hle := Nat.le_of_dvd (by omega) hdvd
  rcases Nat.lt_or_ge m 4 with hm4 | hm4
  ·
    have hm3 : m = 3 := by omega
    subst hm3
    have hT : ∑ i ∈ Finset.range (3 - 1), (2 ^ s) ^ i = 1 + 2 ^ s := by
      simp [Finset.sum_range_succ]
    rw [hT] at hdvd hle
    refine ⟨?_, rfl⟩
    rcases Nat.lt_or_ge s 4 with hs4 | hs4
    · interval_cases s
      · omega
      · norm_num at hdvd
      · rfl
    · have := three_mul_lt_two_pow hs4
      omega
  ·
    exfalso
    have h02 : ({0, m - 2} : Finset ℕ) ⊆ Finset.range (m - 1) := by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rw [Finset.mem_range]
      omega
    have hge : 1 + (2 ^ s) ^ (m - 2) ≤ ∑ i ∈ Finset.range (m - 1), (2 ^ s) ^ i := by
      have := Finset.sum_le_sum_of_subset (f := fun i => (2 ^ s) ^ i) h02
      rw [Finset.sum_pair (by omega)] at this
      simpa using this
    have hpow : (2 ^ s) ^ (m - 2) = 2 ^ (s * (m - 2)) := by rw [← pow_mul]
    have hlin := two_mul_le_two_pow (s * (m - 2))
    have hsm : s * m = s * (m - 2) + s * 2 := by rw [← Nat.mul_add]; congr 1; omega
    have h4' : s * 2 ≤ s * (m - 2) := Nat.mul_le_mul_left _ (by omega)
    omega

theorem eq_three_of_sum_pow_sub_one_dvd {s m d : ℕ} (hs : 1 ≤ s) (hm : 3 ≤ m) (h4 : 4 ≤ s * m)
    (hde : d ∣ s * m) (hdvd : (∑ i ∈ Finset.range m, (2 ^ s) ^ i) - 1 ∣ 2 ^ (s * m) * d) :
    s = 3 ∧ m = 3 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le (show 2 ≤ m by omega)
  rw [show 2 + n = (n + 1) + 1 by ring, sum_range_succ_pow, Nat.add_sub_cancel] at hdvd
  have hTodd : Odd (∑ i ∈ Finset.range (n + 1), (2 ^ s) ^ i) := by
    rw [sum_range_succ_pow]
    have h2 : Even (2 ^ s) := (Nat.even_pow' (by omega)).mpr even_two
    exact Even.add_one (h2.mul_right _)
  have hTd : (∑ i ∈ Finset.range (n + 1), (2 ^ s) ^ i) ∣ d := by
    have h1 := (Dvd.intro_left _ rfl).trans hdvd
    have hcop : Nat.Coprime (∑ i ∈ Finset.range (n + 1), (2 ^ s) ^ i) (2 ^ (s * (n + 1 + 1))) :=
      Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hTodd)
    exact hcop.dvd_of_dvd_mul_left h1
  exact eq_three_of_sum_pow_dvd hs hm h4 (by rw [show 2 + n - 1 = n + 1 by omega]; exact hTd.trans hde)

section Descent

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

theorem exists_card_eq_mul_dvd_of_semilinear [Finite F] (G : Subgroup (F ≃ₗ[k] F))
    (l : IntermediateField k F)
    (hσ : ∀ g ∈ G, ∃ σ : l ≃ₐ[k] l, ∀ (a : l) (x : F), g (a * x) = σ a * g x) :
    ∃ G₁ : Subgroup (F ≃ₗ[k] F), G₁ ≤ G ∧
      (∀ g ∈ G₁, ∀ (a : l) (x : F), g (a * x) = a * g x) ∧
      (∀ g ∈ G, (∀ (a : l) (x : F), g (a * x) = a * g x) → g ∈ G₁) ∧
      ∃ h, h ∣ finrank k l ∧ Nat.card G = Nat.card G₁ * h := by
  have : FiniteDimensional k F := Module.Finite.of_finite
  have hg1 : ∀ g : F ≃ₗ[k] F, g 1 ≠ 0 := fun g h =>
    one_ne_zero (g.injective (h.trans g.map_zero.symm))
  have huniq : ∀ (g : F ≃ₗ[k] F) (σ τ : l ≃ₐ[k] l), (∀ (a : l) (x : F), g (a * x) = σ a * g x) →
      (∀ (a : l) (x : F), g (a * x) = τ a * g x) → σ = τ := by
    intro g σ τ hσg hτg
    ext a
    exact mul_right_cancel₀ (hg1 g) ((hσg a 1).symm.trans (hτg a 1))
  choose! Φ hΦ using hσ
  let Φhom : G →* (l ≃ₐ[k] l) :=
    { toFun := fun g => Φ g
      map_one' := huniq 1 _ _ (hΦ 1 G.one_mem) (fun a x => by simp)
      map_mul' := fun g h => huniq (g * h) _ _ (hΦ _ (G.mul_mem g.2 h.2)) (fun a x => by
        simp only [LinearEquiv.mul_apply, AlgEquiv.mul_apply]
        rw [hΦ h h.2, hΦ g g.2]) }
  set G₁ : Subgroup (F ≃ₗ[k] F) := Φhom.ker.map G.subtype
  have hmem : ∀ g ∈ G, (g ∈ G₁ ↔ ∀ (a : l) (x : F), g (a * x) = a * g x) := by
    intro g hg
    constructor
    · rintro ⟨g', hg', rfl⟩ a x
      rw [SetLike.mem_coe, MonoidHom.mem_ker] at hg'
      have := hΦ g' g'.2 a x
      change (g' : F ≃ₗ[k] F) (a * x) = a * (g' : F ≃ₗ[k] F) x
      rw [this]
      change (Φhom g' a : F) * _ = _
      rw [hg']
      rfl
    · intro hlin
      refine ⟨⟨g, hg⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker]
      exact huniq g _ _ (hΦ g hg) (fun a x => by rw [hlin]; rfl)
  refine ⟨G₁, fun g hg => ?_, fun g hg => ?_, fun g hg hlin => (hmem g hg).mpr hlin,
    Φhom.ker.index, ?_, ?_⟩
  · obtain ⟨g', -, rfl⟩ := hg
    exact g'.2
  · have hgG : g ∈ G := by
      obtain ⟨g', -, rfl⟩ := hg
      exact g'.2
    exact (hmem g hgG).mp hg
  · rw [Subgroup.index_ker]
    calc Nat.card Φhom.range ∣ Nat.card (l ≃ₐ[k] l) := Subgroup.card_subgroup_dvd_card _
      _ = finrank k l := IsGalois.card_aut_eq_finrank k l
  · rw [Subgroup.card_map_of_injective G.subtype_injective, Subgroup.card_mul_index]

theorem exists_subgroup_projGenLinGroup_card_mul [Finite F] {n : ℕ} (hn : finrank k F = n)
    (G : Subgroup (F ≃ₗ[k] F)) (hS : scalars k F ≤ G) :
    ∃ H : Subgroup (Matrix.ProjGenLinGroup (Fin n) k),
      Nat.card H * (Nat.card k - 1) = Nat.card G := by
  have : FiniteDimensional k F := Module.Finite.of_finite
  have : Finite k := Finite.of_injective _ (algebraMap k F).injective
  let b : Basis (Fin n) k F := Module.finBasisOfFinrankEq k F hn
  let φ : GL (Fin n) k ≃* (F ≃ₗ[k] F) :=
    (Matrix.GeneralLinearGroup.toLin' b).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv k F)
  set G' := G.comap φ.toMonoidHom
  have hG' : Nat.card G' = Nat.card G := by
    have hmap : G'.map φ.toMonoidHom = G :=
      Subgroup.map_comap_eq_self_of_surjective φ.surjective G
    rw [← hmap, Subgroup.card_map_of_injective φ.injective]
  have hφ : ∀ u : kˣ, φ (Matrix.GeneralLinearGroup.scalar (Fin n) u) =
      scalarHom k F (Units.map (algebraMap k F : k →* F) u) := by
    intro u
    refine LinearEquiv.ext fun x => ?_
    change ((Matrix.GeneralLinearGroup.toLin' b)
      (Matrix.GeneralLinearGroup.scalar (Fin n) u)).toLinearEquiv x = _
    rw [Matrix.GeneralLinearGroup.toLin'_apply, scalarHom_apply, Units.coe_map,
      MonoidHom.coe_ofClass, ← Algebra.smul_def]
    simp [Matrix.GeneralLinearGroup.scalar, Fintype.linearCombination_apply, Basis.sum_repr]
  have hZ : Subgroup.center (GL (Fin n) k) ≤ G' := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    rintro _ ⟨u, rfl⟩
    change φ (Matrix.GeneralLinearGroup.scalar (Fin n) u) ∈ G
    rw [hφ]
    exact hS (scalarHom_mem_scalars _)
  set f := (Matrix.ProjGenLinGroup.mk : GL (Fin n) k →* _).comp G'.subtype
  have hker : f.ker = (Subgroup.center (GL (Fin n) k)).subgroupOf G' := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact Matrix.ProjGenLinGroup.mk_eq_one
  have hn0 : 0 < n := hn ▸ Module.finrank_pos
  have hscalar : Function.Injective
      (Matrix.GeneralLinearGroup.scalar (Fin n) : kˣ → GL (Fin n) k) := by
    intro a c hac
    apply Units.ext
    simpa [Matrix.GeneralLinearGroup.scalar] using
      congrArg (fun A : GL (Fin n) k => (A : Matrix (Fin n) (Fin n) k) ⟨0, hn0⟩ ⟨0, hn0⟩) hac
  have hcenter : Nat.card (Subgroup.center (GL (Fin n) k)) = Nat.card k - 1 := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar,
      ← Nat.card_congr (MonoidHom.ofInjective hscalar).toEquiv, Nat.card_units]
  refine ⟨f.range, ?_⟩
  have h1 := f.ker.card_mul_index
  rw [Subgroup.index_ker, hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZ).toEquiv,
    hcenter, hG'] at h1
  rw [← h1, mul_comm]

end Descent

theorem false_of_card_mul_eq_of_odd {F : Type u} [Field F] [Finite F] [CharP F 2] {e d : ℕ}
    (hF : Nat.card F = 2 ^ e) (hodd : Odd e) (he : 4 ≤ e) (hd : 0 < d) (hde : d ∣ e) :
    ∀ (m : ℕ) (k : Type u) [Field k] [Algebra k F] (s a : ℕ), finrank k F = m →
      Nat.card k = 2 ^ s → a ∣ s → ∀ G : Subgroup (F ≃ₗ[k] F), scalars k F ≤ G →
        Nat.card G * a = 2 ^ e * (2 ^ e - 1) * d → False := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro k _ _ s a hm hk has G hSG hcard
  have : FiniteDimensional k F := Module.Finite.of_finite
  have : Finite k := Finite.of_injective _ (algebraMap k F).injective
  have hesm : e = s * m := by
    have h := Module.natCard_eq_pow_finrank (K := k) (V := F)
    rw [hF, hk, hm, ← pow_mul] at h
    exact Nat.pow_right_injective le_rfl h
  have hs1 : 1 ≤ s := by
    have h1 : 1 < Nat.card k := Finite.one_lt_card
    rw [hk] at h1
    by_contra h0
    have : s = 0 := by omega
    subst this
    simp at h1
  have has' : a ≤ s := Nat.le_of_dvd hs1 has
  have hm1 : 1 ≤ m := by
    rw [← hm]
    exact Module.finrank_pos
  have he1 : 1 ≤ e := by omega
  have hnormal : (∀ g ∈ G, ∀ c : Fˣ, ∃ c' : Fˣ, ∀ x, g (c * x) = c' * g x) → False := by
    intro hN
    have hle := card_le_of_normalizes G hN
    rw [hF, hm] at hle
    exact lt_of_card_eq hesm he1 hd has' hcard hle
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  ·
    apply hnormal
    intro g _ c
    refine ⟨c, fun x => ?_⟩
    have htop : (⊤ : IntermediateField k F) = ⊥ :=
      IntermediateField.finrank_eq_one_iff.mp ((IntermediateField.finrank_top').trans (by omega))
    have hc : (c : F) ∈ (⊥ : IntermediateField k F) := htop ▸ IntermediateField.mem_top
    obtain ⟨r, hr⟩ := IntermediateField.mem_bot.mp hc
    rw [← hr, ← Algebra.smul_def, map_smul, Algebra.smul_def]
  have hm3 : 3 ≤ m := by
    by_contra hm3
    rw [hesm, show m = 2 by omega] at hodd
    exact Nat.not_even_iff_odd.mpr hodd (even_two.mul_left s)
  by_cases hprim : IsPreprimitive G (ℙ k F)
  ·
    have := isPreprimitive_projectiveImage G
    have := isPretransitive_projectiveImage_scalars (k := k) (F := F)
    have hcardP : Nat.card (ℙ k F) = ∑ i ∈ Finset.range m, (2 ^ s) ^ i := by
      rw [card_of_finrank k F hm, hk]
    have hP2 : 2 ≤ Nat.card (ℙ k F) := by
      rw [hcardP]
      obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hm1
      rw [add_comm, sum_range_succ_pow]
      have hb : 2 ≤ 2 ^ s :=
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs1
      have h1 : 1 ≤ ∑ i ∈ Finset.range n, (2 ^ s) ^ i := by
        obtain ⟨n', rfl⟩ := Nat.exists_eq_add_of_le (show 1 ≤ n by omega)
        rw [add_comm, sum_range_succ_pow]
        omega
      nlinarith
    rcases CFSG.burnside_schur (projectiveImage G) (projectiveImage (scalars k F)) hP2
        (projectiveImage_mono hSG) stabilizer_projectiveImage_scalars with
      h2 | ⟨p, -, -, -, -, -, hN⟩
    ·
      have hdiv := mul_pred_dvd_card h2 hP2
      have hGcard := card_eq_card_projectiveImage_mul G hSG
      have hproj := Projectivization.card k F
      rw [hF, hk] at hproj
      rw [hk] at hGcard
      set v := Nat.card (ℙ k F)
      have hb1 : 0 < 2 ^ s - 1 := by
        have := Nat.one_lt_two_pow (show s ≠ 0 by omega)
        omega
      have hv0 : 0 < v := by omega
      have hGa : Nat.card (projectiveImage G) * a = 2 ^ e * v * d := by
        have h1 : Nat.card (projectiveImage G) * a * (2 ^ s - 1) =
            2 ^ e * v * d * (2 ^ s - 1) := by
          calc Nat.card (projectiveImage G) * a * (2 ^ s - 1)
              = Nat.card G * a := by rw [hGcard]; ring
            _ = 2 ^ e * (2 ^ e - 1) * d := hcard
            _ = 2 ^ e * v * d * (2 ^ s - 1) := by rw [hproj]; ring
        exact Nat.eq_of_mul_eq_mul_right hb1 h1
      have h3 : v * (v - 1) ∣ v * (2 ^ e * d) := by
        have := hdiv.trans (Dvd.intro a hGa)
        convert this using 1
        ring
      have h4 := Nat.dvd_of_mul_dvd_mul_left hv0 h3
      rw [hcardP, hesm] at h4
      obtain ⟨rfl, rfl⟩ := eq_three_of_sum_pow_sub_one_dvd hs1 hm3 (hesm ▸ he) (hesm ▸ hde) h4
      subst hesm
      have hv : v = 73 := by
        rw [hcardP]
        simp [Finset.sum_range_succ]
      rw [hv] at hdiv hGa
      obtain ⟨j, hj⟩ := hdiv
      have hj' : Nat.card (projectiveImage G) = 5256 * j := by
        rw [hj]
      have hGa' : Nat.card (projectiveImage G) * a = 37376 * d := by
        rw [hGa]
        ring
      have hd9 : d ≤ 9 := Nat.le_of_dvd (by norm_num) hde
      have hPG : Nat.card (projectiveImage G) = 2 ^ 9 * 73 * 9 := by
        interval_cases a <;> interval_cases d <;> omega
      obtain ⟨H, hH⟩ := exists_subgroup_projGenLinGroup_card_mul hm G hSG
      rw [hGcard, hk] at hH
      refine CosetNormalizer.projective_linear_three_eight_small_order_exclusion (K := k)
        (by rw [hk]; norm_num) ⟨H, ?_⟩
      rw [← hPG]
      exact Nat.eq_of_mul_eq_mul_right (by norm_num) hH
    ·
      exact hnormal fun g hg c => normalizes_of_normal hSG hN hg c
  ·
    obtain ⟨l, hl, -, hσ, -⟩ :=
      exists_intermediateField_normalized_of_not_isPreprimitive (by omega) G hSG hprim
    obtain ⟨G₁, hG₁G, hG₁lin, hG₁mem, h, hh, hcardG⟩ :=
      exists_card_eq_mul_dvd_of_semilinear G l hσ
    have ht1 : finrank k l ≠ 1 := fun h1 => hl (IntermediateField.finrank_eq_one_iff.mp h1)
    have ht2 : 2 ≤ finrank k l := by
      have : 0 < finrank k l := Module.finrank_pos
      omega
    have htower : finrank k l * finrank l F = m := by
      rw [Module.finrank_mul_finrank, hm]
    have hlF : 0 < finrank l F := Module.finrank_pos
    have hlt : finrank l F < m := by
      rw [← htower]
      nlinarith
    have hcardl : Nat.card l = 2 ^ (s * finrank k l) := by
      rw [Module.natCard_eq_pow_finrank (K := k) (V := l), hk, ← pow_mul]
    set G' := G₁.comap (restrictScalarsHom k l)
    have hcardG' : Nat.card G' = Nat.card G₁ := by
      have hmap : G'.map (restrictScalarsHom k l) = G₁ := by
        rw [Subgroup.map_comap_eq, inf_eq_right]
        intro g hg
        obtain ⟨g', hg'⟩ := exists_restrictScalarsHom_eq (hG₁lin g hg)
        exact ⟨g', hg'⟩
      rw [← hmap, Subgroup.card_map_of_injective restrictScalarsHom_injective]
    have hSG' : scalars l F ≤ G' := by
      rintro _ ⟨c, rfl⟩
      change restrictScalarsHom k l (scalarHom l F c) ∈ G₁
      rw [restrictScalarsHom_scalarHom]
      exact hG₁mem _ (hSG (scalarHom_mem_scalars c)) fun b x => by
        rw [scalarHom_apply, scalarHom_apply, mul_left_comm]
    exact ih (finrank l F) hlt l (s * finrank k l) (a * h) rfl hcardl (Nat.mul_dvd_mul has hh) G'
      hSG' (by rw [hcardG', ← hcard, hcardG]; ring)

theorem not_exists_singer_overgroup_card_eq_of_four_le {F : Type u} [Field F] [Algebra (ZMod 2) F]
    {e d : ℕ} (he : 4 ≤ e) (hF : Nat.card F = 2 ^ e) (hd : 0 < d) (hde : d ∣ e) :
    ¬ ∃ R : Subgroup (F ≃ₗ[ZMod 2] F), scalars (ZMod 2) F ≤ R ∧
      Nat.card R = 2 ^ e * (2 ^ e - 1) * d := by
  rcases Nat.even_or_odd e with heven | hodd
  · exact not_exists_singer_overgroup_card_eq heven hF hd hde
  rintro ⟨R, hSR, hR⟩
  have : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; positivity)
  have : CharP F 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2
  have : FiniteDimensional (ZMod 2) F := Module.Finite.of_finite
  set k₀ := (⊥ : IntermediateField (ZMod 2) F)
  have hsurj : Function.Surjective (restrictScalarsHom (ZMod 2) k₀) := by
    intro g
    refine exists_restrictScalarsHom_eq fun a x => ?_
    obtain ⟨z, hz⟩ := IntermediateField.mem_bot.mp a.2
    rw [← hz, ← Algebra.smul_def, map_smul, Algebra.smul_def]
  set R₀ := R.comap (restrictScalarsHom (ZMod 2) k₀)
  have hcard₀ : Nat.card R₀ = Nat.card R := by
    have hmap : R₀.map (restrictScalarsHom (ZMod 2) k₀) = R := by
      rw [Subgroup.map_comap_eq, MonoidHom.range_eq_top.mpr hsurj, top_inf_eq]
    rw [← hmap, Subgroup.card_map_of_injective restrictScalarsHom_injective]
  have hS₀ : scalars k₀ F ≤ R₀ := by
    rintro _ ⟨c, rfl⟩
    change restrictScalarsHom (ZMod 2) k₀ (scalarHom k₀ F c) ∈ R
    rw [restrictScalarsHom_scalarHom]
    exact hSR (scalarHom_mem_scalars c)
  have hk₀ : Nat.card k₀ = 2 ^ 1 := by
    rw [Nat.card_congr (IntermediateField.botEquiv (ZMod 2) F).toEquiv, Nat.card_zmod, pow_one]
  have hfin : finrank k₀ F = e := by
    rw [IntermediateField.finrank_bot']
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F)
    rw [hF, Nat.card_zmod] at h
    exact (Nat.pow_right_injective le_rfl h).symm
  exact false_of_card_mul_eq_of_odd hF hodd he hd hde e k₀ 1 1 hfin hk₀ (dvd_refl 1) R₀ hS₀
    (by rw [mul_one, hcard₀, hR])

end CFSG.ProperTwoGeneratedCore.CosetNormalizerSinger
