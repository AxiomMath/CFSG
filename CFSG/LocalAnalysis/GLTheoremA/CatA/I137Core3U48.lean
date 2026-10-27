module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I137Core3List
public import CFSG.RankThree.PartTwo.Sec19.KS1919U48Levi
import all CFSG.RankThree.PartTwo.Sec19.KS1919U48Levi
import CFSG.Assembly.InCatalogConverse
import CFSG.Milestones.CL_LIT_Borel_Tits_local_parabolic
import CFSG.RankThree.PartTwo.Sec19.Step1910Proof
import CFSG.Adapters.TauCetiLieModels
import CFSG.Models.Blueprint
import CFSG.RankThree.CentralLiftU.UnitaryBorelLift

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I137C3

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 TauCeti
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

namespace U48

theorem card_dvd_of_pKer {A H Q₀ : Type*} [Group A] [Group H] [Finite H] [Group Q₀] [Finite Q₀]
    [IsSimpleGroup Q₀] (hnc : ∃ a b : Q₀, a * b ≠ b * a) (f₀ : A →* Q₀)
    (hf₀ : Function.Surjective f₀) (Φ : A →* H)
    (hΦ : ∀ a : A, Φ a = 1 → ∃ n : ℕ, a ^ 2 ^ n = 1) : Nat.card Q₀ ∣ Nat.card H := by
  have hker2 : IsPGroup 2 Φ.ker := fun ⟨a, ha⟩ => by
    obtain ⟨n, hn⟩ := hΦ a ha
    exact ⟨n, Subtype.ext hn⟩
  haveI hN : (Φ.ker.map f₀).Normal := Subgroup.Normal.map inferInstance f₀ hf₀
  have hbot : Φ.ker.map f₀ = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Φ.ker.map f₀) with h | h
    · exact h
    · exfalso
      have h2 : IsPGroup 2 (Φ.ker.map f₀) := hker2.map f₀
      rw [h] at h2
      haveI : IsPGroup 2 Q₀ := h2.of_equiv Subgroup.topEquiv
      haveI : Group.IsNilpotent Q₀ := IsPGroup.isNilpotent this
      obtain ⟨a, b, hab⟩ := hnc
      exact hab (IsSimpleGroup.comm_iff_isSolvable.2 inferInstance a b)
  have hle : Φ.ker ≤ f₀.ker := (Subgroup.map_eq_bot_iff _).1 hbot
  let g : Φ.range →* Q₀ := (QuotientGroup.lift Φ.ker f₀ hle).comp
    (QuotientGroup.quotientKerEquivRange Φ).symm.toMonoidHom
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨a, rfl⟩ := hf₀ y
    exact ⟨QuotientGroup.quotientKerEquivRange Φ (QuotientGroup.mk a), by simp [g]⟩
  exact (card_dvd_of_surjective g hg).trans (Subgroup.card_subgroup_dvd_card _)

theorem exists_pKer_of_mulEquiv {A A' H : Type*} [Group A] [Group A'] [Group H] (e : A ≃* A')
    (h : ∃ Φ : A' →* H, ∀ a : A', Φ a = 1 → ∃ n : ℕ, a ^ 2 ^ n = 1) :
    ∃ Φ : A →* H, ∀ a : A, Φ a = 1 → ∃ n : ℕ, a ^ 2 ^ n = 1 := by
  obtain ⟨Φ, hΦ⟩ := h
  refine ⟨Φ.comp e.toMonoidHom, fun a ha => ?_⟩
  obtain ⟨n, hn⟩ := hΦ (e a) ha
  exact ⟨n, e.injective (by rw [map_pow, hn, map_one])⟩

section Unitary

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartTwo.Sec19.KS1919U48Proof
open CFSG.RankThree.CentralLiftU (isPGroup_hypUnitriangular)
open scoped Pointwise

variable {p f : ℕ} {K : Type} [Field K]

theorem mem_hypUnitriangular_of_midBlock_corner {h : UnitaryFieldData p f K}
    {g : hypSU h 2 0} (hg : g ∈ isoStabilizer h 2 0 (hypFlag h 2 0 1))
    (h1 : midBlock (((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K)) = 1)
    (hα : ((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) (.inl 0) (.inl 0) =
      1) : g ∈ hypUnitriangular h 2 0 := by
  have hc := col_eq_zero_of_mem_isoStabilizer_one hg
  have hr := row_eq_zero_of_mem_isoStabilizer_one hg
  have hm : ∀ i j : Fin 2, ((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K)
      (midIdx i) (midIdx j) = if i = j then 1 else 0 := fun i j => by
    have := congrFun (congrFun h1 i) j
    simpa [midBlock, one_apply] using this
  have m00 := hm 0 0
  have m01 := hm 0 1
  have m10 := hm 1 0
  have m11 := hm 1 1
  simp only [midIdx] at m00 m01 m10 m11
  simp at m00 m01 m10 m11
  have c1 := hc (.inl 1) (by decide)
  have c2 := hc (.inr (.inr 0)) (by decide)
  have c3 := hc (.inr (.inr 1)) (by decide)
  have r1 := hr (.inl 0) (by decide)
  have r2 := hr (.inl 1) (by decide)
  have r3 := hr (.inr (.inr 1)) (by decide)
  have hlow : (((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K)).BlockTriangular
      fullPos := by
    intro a c hac
    fin_cases a <;> fin_cases c <;> simp [fullPos] at hac <;> assumption
  have hdet := (mem_hypSU.mp g.2).2
  rw [det_eq_prod_diag fullPos_injective hlow, prod_diag, m00, m11, mul_one, mul_one] at hdet
  rw [hα, one_mul] at hdet
  rw [mem_hypUnitriangular]
  refine ⟨hlow, fun a => ?_⟩
  fin_cases a <;> simp [m00, m11, hα, hdet]

theorem exists_pKer_flag_two (h : UnitaryFieldData 2 f K) (B : Subgroup (hypSU h 2 0))
    (hB : B ≤ isoStabilizer h 2 0 (hypFlag h 2 0 2)) :
    ∃ Φ : B →* GL (Fin 2) K × Kˣ, ∀ b : B, Φ b = 1 → ∃ n : ℕ, b ^ 2 ^ n = 1 := by
  refine ⟨((topBlockHom h).comp (Subgroup.inclusion hB)).prod 1, fun b hb => ?_⟩
  have h1 : (topBlockHom h) (Subgroup.inclusion hB b) = 1 := (Prod.ext_iff.1 hb).1
  have hU : (b : hypSU h 2 0) ∈ hypUnitriangular h 2 0 := by
    refine mem_hypUnitriangular_of_topBlock (hB b.2) ?_
    have := congrArg (fun u : GL (Fin 2) K => (u : Matrix (Fin 2) (Fin 2) K)) h1
    simpa [topBlockHom] using this
  obtain ⟨n, hn⟩ := isPGroup_hypUnitriangular (h := h) (r := 2) (ε := 0) (by norm_num) ⟨b, hU⟩
  exact ⟨n, Subtype.ext (by simpa using congrArg Subtype.val hn)⟩

theorem exists_pKer_flag_one (h : UnitaryFieldData 2 f K) (B : Subgroup (hypSU h 2 0))
    (hB : B ≤ isoStabilizer h 2 0 (hypFlag h 2 0 1)) :
    ∃ Φ : B →* GL (Fin 2) K × Kˣ, ∀ b : B, Φ b = 1 → ∃ n : ℕ, b ^ 2 ^ n = 1 := by
  refine ⟨((midBlockHom h).comp (Subgroup.inclusion hB)).prod
    ((cornerHom h).comp (Subgroup.inclusion hB)).toHomUnits, fun b hb => ?_⟩
  obtain ⟨h1, h2⟩ := Prod.ext_iff.1 hb
  have hα : ((b : hypSU h 2 0) : GL (HypIndex 2 0) K) (.inl 0) (.inl 0) = 1 := by
    have := congrArg (fun u : Kˣ => (u : K)) h2
    simpa [cornerHom] using this
  have hU : (b : hypSU h 2 0) ∈ hypUnitriangular h 2 0 := by
    refine mem_hypUnitriangular_of_midBlock_corner (hB b.2) ?_ hα
    have := congrArg (fun u : GL (Fin 2) K => (u : Matrix (Fin 2) (Fin 2) K)) h1
    simpa [midBlockHom] using this
  obtain ⟨n, hn⟩ := isPGroup_hypUnitriangular (h := h) (r := 2) (ε := 0) (by norm_num) ⟨b, hU⟩
  exact ⟨n, Subtype.ext (by simpa using congrArg Subtype.val hn)⟩

theorem exists_pKer_of_le_isoStabilizer (h : UnitaryFieldData 2 f K)
    {W : Submodule K (HypIndex 2 0 → K)} (hW0 : W ≠ ⊥)
    (hW : ∀ x ∈ W, ∀ y ∈ W, hypForm h 2 0 x y = 0) (B : Subgroup (hypSU h 2 0))
    (hB : B ≤ isoStabilizer h 2 0 W) :
    ∃ Φ : B →* GL (Fin 2) K × Kˣ, ∀ b : B, Φ b = 1 → ∃ n : ℕ, b ^ 2 ^ n = 1 := by
  obtain ⟨hd1, hd2, g, hg⟩ := exists_smul_hypFlag_eq h (by norm_num) hW0 hW
  set d := Module.finrank K W with hd
  set B' := B.map (MulAut.conj g⁻¹).toMonoidHom with hB'
  have hB'le : B' ≤ isoStabilizer h 2 0 (hypFlag h 2 0 d) := by
    have := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hB
    rwa [isoStabilizer_map_conj, ← hg, inv_smul_smul] at this
  refine exists_pKer_of_mulEquiv
    (B.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective) ?_
  obtain hd' | hd' : d = 1 ∨ d = 2 := by omega
  · rw [hd'] at hB'le
    exact exists_pKer_flag_one h B' hB'le
  · rw [hd'] at hB'le
    exact exists_pKer_flag_two h B' hB'le

theorem exists_pKer_of_le_parabolic (h : UnitaryFieldData 2 f K) (hf : Odd f)
    {P : Subgroup (hypPSU h 2 0)} (hP : P ≠ ⊤) (T : Sylow 2 (hypPSU h 2 0))
    (hTP : Subgroup.normalizer ((T : Subgroup (hypPSU h 2 0)) : Set (hypPSU h 2 0)) ≤ P)
    (A : Subgroup (hypPSU h 2 0)) (hAP : A ≤ P) :
    ∃ Φ : A →* GL (Fin 2) K × Kˣ, ∀ a : A, Φ a = 1 → ∃ n : ℕ, a ^ 2 ^ n = 1 := by
  obtain ⟨M, hM, hPM⟩ := (eq_top_or_exists_le_coatom P).resolve_left hP
  have hMmax : M ∈ maximalParabolics h 2 0 := ⟨hM, _, ⟨T, rfl⟩, hTP.trans hPM⟩
  rw [(unitary_maximal_parabolics h (by norm_num) (by norm_num)).1] at hMmax
  obtain ⟨W, ⟨hW0, hW⟩, rfl⟩ := hMmax
  have hodd : Odd (2 ^ f + 1) :=
    (Nat.even_pow.mpr ⟨even_two, by obtain ⟨k, rfl⟩ := hf; omega⟩).add_one
  have hZ : hypScalars h 2 0 = ⊥ := by
    rw [← Subgroup.card_eq_one, card_hypScalars h (by norm_num)]
    exact (Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hodd) : Nat.Coprime (2 ^ 2) _)
  have hinj : Function.Injective (hypProj h 2 0) := by
    rw [← MonoidHom.ker_eq_bot_iff, ker_hypProj, hZ]
  set A₁ := A.comap (hypProj h 2 0) with hA₁
  have hA₁W : A₁ ≤ isoStabilizer h 2 0 W := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hAP.trans hPM hx
    rwa [← hinj hxy]
  have hbij : Function.Bijective ((hypProj h 2 0).subgroupComap A) := by
    refine ⟨fun x y hxy => Subtype.ext (hinj (congrArg Subtype.val hxy)), fun a => ?_⟩
    obtain ⟨g, hg⟩ := hypProj_surjective h 2 0 a.1
    exact ⟨⟨g, show hypProj h 2 0 g ∈ A by rw [hg]; exact a.2⟩, Subtype.ext hg⟩
  exact exists_pKer_of_mulEquiv (MulEquiv.ofBijective _ hbij).symm
    (exists_pKer_of_le_isoStabilizer h hW0 hW A₁ hA₁W)

end Unitary

theorem not_two_pow_seven_dvd_card_gl {K : Type} [Field K] [Finite K] (hK : Nat.card K = 64) :
    ¬ 128 ∣ Nat.card (GL (Fin 2) K × Kˣ) := by
  haveI := Fintype.ofFinite K
  have hq : Fintype.card K = 64 := by rw [← Nat.card_eq_fintype_card, hK]
  rw [Nat.card_prod, Matrix.card_GL_field, Nat.card_units, hK, hq, Fin.prod_univ_two]
  decide +kernel

theorem exists_model_hyp {S : Type} [Group S] {q : PrimePower}
    (hv : (LieTypeIndex.twistedA 3 q).Valid) (hq : q.card = 8)
    (e : S ≃* ValidLieTypeIndex.Group ⟨.twistedA 3 q, hv⟩) :
    CFSG.Blueprint.LieModel S .PSU (3 + 1) 2 3 ∧
      ∃ h : UnitaryFieldData 2 3 (GaloisField 2 (2 * 3)), Nonempty (S ≃* hypPSU h 2 0) := by
  have h8 : q.p ^ q.exponent = 2 ^ 3 := by rw [← PrimePower.card_def, hq]; norm_num
  have h1 : q.p = 2 := (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1
    (q.prime_p.dvd_of_dvd_pow (h8 ▸ dvd_pow_self q.p q.exponent_pos.ne'))
  have h2 : q.exponent = 3 := by
    rw [h1] at h8
    exact Nat.pow_right_injective (le_refl 2) h8
  have hm : CFSG.Models.LieModel S .PSU (3 + 1) 2 3 := by
    have hc : ValidLieTypeIndex.characteristic ⟨.twistedA 3 q, hv⟩ = q.p :=
      LieTypeIndex.characteristic_twistedA 3 q
    have hf : ValidLieTypeIndex.fieldExponent ⟨.twistedA 3 q, hv⟩ = q.exponent :=
      LieTypeIndex.fieldExponent_twistedA 3 q
    have h := CFSG.Models.lieModel_twistedA 3 q hv e
    rwa [hc, hf, h1, h2] at h
  refine ⟨hm.toBlueprint (by decide), ?_⟩
  obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ := hm.statedClassicalModel (by decide)
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fintype (GaloisField 2 (2 * 3)) := Fintype.ofFinite _
  have hc : Fintype.card K = Fintype.card (GaloisField 2 (2 * 3)) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
      GaloisField.card 2 (2 * 3) (by norm_num)]
    norm_num
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : UnitaryFieldData 2 3 (GaloisField 2 (2 * 3)) :=
    ⟨Nat.prime_two, by norm_num, GaloisField.card 2 (2 * 3) (by norm_num)⟩
  obtain ⟨R, hR⟩ := exists_isHypTransport h (r := 2) (ε := 0)
  exact ⟨h, ⟨e'.trans ((CFSG.Open.StatedSUFieldChange.statedProjSUEquiv
    (FiniteField.ringEquivOfCardEq hc) 4 (2 ^ 3)).trans
    (hypPSUEquivStatedProj h hR (by norm_num)).symm)⟩⟩

end U48

open U48

section Core3


theorem core3At_U4eight :
    Core3At fun d => ∃ q : TauCeti.PrimePower, d = .twistedA 3 q ∧ q.card = 8 := by
  rintro ⟨d, hv⟩ ⟨q, hdq, hq8⟩ S _ _ ⟨e⟩
  obtain rfl : d = .twistedA 3 q := hdq
  intro T A hT2 hT hA Q₀ _ ⟨f₀, hf₀⟩ hQ
  haveI : Finite Q₀ := Finite.of_surjective f₀ hf₀
  rcases card_list93three_two_part hQ with h128 | hL3
  swap
  · exact hL3
  exfalso
  obtain ⟨d', ⟨e'⟩, -⟩ := list93three_cases hQ
  haveI : IsSimpleGroup (CFSGIndex.lie d').Group := (CFSG.Assembly.lie_finite_simple d').2
  haveI : IsSimpleGroup Q₀ := e'.isSimpleGroup
  have hnc : ∃ a b : Q₀, a * b ≠ b * a := by
    by_contra hcomm
    push Not at hcomm
    haveI : IsMulCommutative Q₀ := ⟨⟨fun a b => hcomm a b⟩⟩
    have hp : (Nat.card Q₀).Prime := Group.is_simple_iff_prime_card.mp inferInstance
    have h2 : 2 ∣ Nat.card Q₀ := (dvd_trans (by norm_num) h128)
    have h3 := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h2
    rw [← h3] at h128
    omega
  obtain ⟨hmB, h, ⟨ψ⟩⟩ := exists_model_hyp hv hq8 e
  obtain ⟨Syl, P, hP, hNT, -, -, hSN, -⟩ :=
    CFSG.Milestones.cl_lit_borel_tits_local_parabolic_all_models S .PSU (3 + 1) 2 3 hmB T hT hT2
  have hPP : CFSG.RankThree.PartTwo.Sec19.IsProperParabolic P := ⟨hP, Syl, hSN (by decide)⟩
  obtain ⟨hP', Syl', hSyl'⟩ :=
    CFSG.RankThree.PartTwo.Sec19.Step1910Proof.isProperParabolic_map ψ hPP
  have hAP : A.map ψ.toMonoidHom ≤ P.map ψ.toMonoidHom := Subgroup.map_mono (hA.trans hNT)
  obtain ⟨Φ', hΦ'⟩ := exists_pKer_of_le_parabolic h ⟨1, rfl⟩ hP' Syl' hSyl' _ hAP
  obtain ⟨Φ, hΦ⟩ := exists_pKer_of_mulEquiv
    (A.equivMapOfInjective ψ.toMonoidHom ψ.injective) ⟨Φ', hΦ'⟩
  have hK : Nat.card (GaloisField 2 (2 * 3)) = 64 := by
    rw [GaloisField.card 2 (2 * 3) (by norm_num)]
    norm_num
  exact not_two_pow_seven_dvd_card_gl hK (h128.trans (card_dvd_of_pKer hnc f₀ hf₀ Φ hΦ))

end Core3

end CFSG.LocalAnalysis.GLTheoremA.I137C3

end
