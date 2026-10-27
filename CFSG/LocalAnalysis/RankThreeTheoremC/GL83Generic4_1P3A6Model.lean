module

public import CFSG.Quasithin.Recognition.CertF9
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3SylowTransport
import CFSG.Adapters.LinearFieldTransport
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Cardinality
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.A6Model

open Matrix Subgroup CFSG.Quasithin
open scoped MatrixGroups

abbrev SL29 := Matrix.SpecialLinearGroup (Fin 2) GF9

abbrev PSL29 := Matrix.ProjectiveSpecialLinearGroup (Fin 2) GF9

@[expose] def um (a : GF9) : SL29 :=
  ⟨!![1, a; 0, 1], by rw [Matrix.det_fin_two_of]; simp⟩

private def hdw : SL29 :=
  ⟨!![GF9.ofNat' 4, 0; 0, (GF9.ofNat' 4)⁻¹], by rw [Matrix.det_fin_two_of]; decide⟩

theorem um_mul : ∀ a b : GF9, um a * um b = um (a + b) := by decide +kernel

theorem um_zero : um 0 = 1 := by decide +kernel

private theorem hdw_conj : ∀ a : GF9, hdw * um a * hdw⁻¹ = um (GF9.ofNat' 6 * a) := by
  decide +kernel

private theorem hdw_inv_conj : ∀ a : GF9, hdw⁻¹ * um a * hdw = um (GF9.ofNat' 3 * a) := by
  decide +kernel

@[expose] def IsCentral (s : SL29) : Prop :=
  ∃ r : GF9, r ^ Fintype.card (Fin 2) = 1 ∧
    Matrix.scalar (Fin 2) r = (s : Matrix (Fin 2) (Fin 2) GF9)

instance (s : SL29) : Decidable (IsCentral s) := by
  unfold IsCentral
  infer_instance

theorem isCentral_iff {s : SL29} : IsCentral s ↔ s ∈ Subgroup.center SL29 :=
  Matrix.SpecialLinearGroup.mem_center_iff.symm

theorem mk_eq_iff {A B : SL29} :
    (QuotientGroup.mk A : PSL29) = QuotientGroup.mk B ↔ IsCentral (A⁻¹ * B) :=
  QuotientGroup.eq.trans isCentral_iff.symm

theorem mk_eq_one_iff {A : SL29} : (QuotientGroup.mk A : PSL29) = 1 ↔ IsCentral A :=
  (QuotientGroup.eq_one_iff A).trans isCentral_iff.symm

private theorem um_center_inj : ∀ b c : GF9, IsCentral ((um b)⁻¹ * um c) → b = c := by
  decide +kernel

private theorem um_inj_mod_center {b c : GF9}
    (h : (QuotientGroup.mk (um b) : PSL29) = QuotientGroup.mk (um c)) : b = c :=
  um_center_inj b c (mk_eq_iff.mp h)

@[expose] def uHom : Multiplicative GF9 →* PSL29 where
  toFun a := QuotientGroup.mk (um (Multiplicative.toAdd a))
  map_one' := by
    change (QuotientGroup.mk (um 0) : PSL29) = 1
    rw [um_zero]
    rfl
  map_mul' a b := by
    change (QuotientGroup.mk (um (Multiplicative.toAdd a + Multiplicative.toAdd b)) : PSL29) =
      QuotientGroup.mk (um (Multiplicative.toAdd a)) *
        QuotientGroup.mk (um (Multiplicative.toAdd b))
    rw [← um_mul]
    rfl

theorem uHom_injective : Function.Injective uHom := fun _ _ h =>
  Multiplicative.toAdd.injective (um_inj_mod_center h)

theorem uHom_card : Nat.card uHom.range = 3 ^ 2 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective uHom_injective).toEquiv, Nat.card_eq_fintype_card]
  decide

@[expose] def ut (a : GF9) : PSL29 := uHom (Multiplicative.ofAdd a)

theorem ut_mul (a b : GF9) : ut a * ut b = ut (a + b) := by
  unfold ut
  rw [← map_mul]
  rfl

theorem ut_zero : ut 0 = 1 := by
  unfold ut
  exact map_one uHom

theorem ut_inj {a b : GF9} (h : ut a = ut b) : a = b :=
  Multiplicative.ofAdd.injective (uHom_injective h)

theorem mem_range_iff {x : PSL29} : x ∈ uHom.range ↔ ∃ a, x = ut a := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨Multiplicative.toAdd a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨Multiplicative.ofAdd a, rfl⟩

theorem ut_cube (a : GF9) : ut a * ut a * ut a = 1 := by
  rw [ut_mul, ut_mul, show a + a + a = 0 from by revert a; decide, ut_zero]

theorem conj_ut (h : SL29) (c : GF9 → GF9)
    (hc : ∀ a, h * um a * h⁻¹ = um (c a)) (a : GF9) :
    (QuotientGroup.mk h : PSL29) * ut a * (QuotientGroup.mk h)⁻¹ = ut (c a) := by
  change (QuotientGroup.mk h : PSL29) * QuotientGroup.mk (um a) * (QuotientGroup.mk h)⁻¹ =
    QuotientGroup.mk (um (c a))
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hc]

private theorem inv_conj_ut (h : SL29) (c : GF9 → GF9)
    (hc : ∀ a, h⁻¹ * um a * h = um (c a)) (a : GF9) :
    (QuotientGroup.mk h : PSL29)⁻¹ * ut a * (QuotientGroup.mk h) = ut (c a) := by
  change (QuotientGroup.mk h : PSL29)⁻¹ * QuotientGroup.mk (um a) * (QuotientGroup.mk h) =
    QuotientGroup.mk (um (c a))
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hc]

theorem mem_normalizer_of_conj {K : Type} [Group K] {T₀ : Subgroup K} {n : K}
    (h : ∀ t ∈ T₀, n * t * n⁻¹ ∈ T₀) (h' : ∀ t ∈ T₀, n⁻¹ * t * n ∈ T₀) :
    n ∈ normalizer (T₀ : Set K) := by
  rw [mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  have := h' _ hx
  simpa [mul_assoc] using this

private theorem mk_mem_normalizer (h : SL29) (c c' : GF9 → GF9)
    (hc : ∀ a, h * um a * h⁻¹ = um (c a)) (hc' : ∀ a, h⁻¹ * um a * h = um (c' a)) :
    (QuotientGroup.mk h : PSL29) ∈ normalizer (uHom.range : Set PSL29) := by
  refine mem_normalizer_of_conj (fun t ht => ?_) (fun t ht => ?_)
  · obtain ⟨a, rfl⟩ := mem_range_iff.mp ht
    rw [conj_ut h c hc]
    exact mem_range_iff.mpr ⟨_, rfl⟩
  · obtain ⟨a, rfl⟩ := mem_range_iff.mp ht
    rw [inv_conj_ut h c' hc' a]
    exact mem_range_iff.mpr ⟨_, rfl⟩

private theorem hdw_pow_central : IsCentral (hdw ^ 4) ∧ ¬ IsCentral (hdw ^ 2) := by
  constructor <;> decide +kernel

theorem exists_order_four :
    ∃ n : PSL29, n ∈ normalizer (uHom.range : Set PSL29) ∧ orderOf n = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨QuotientGroup.mk hdw,
    mk_mem_normalizer hdw (fun a => GF9.ofNat' 6 * a) (fun a => GF9.ofNat' 3 * a) hdw_conj
      hdw_inv_conj, ?_⟩
  have h4 : (QuotientGroup.mk hdw : PSL29) ^ 2 ^ (1 + 1) = 1 := by
    rw [← QuotientGroup.mk_pow, mk_eq_one_iff]
    exact hdw_pow_central.1
  have h2 : ¬ (QuotientGroup.mk hdw : PSL29) ^ 2 ^ 1 = 1 := by
    rw [pow_one, ← QuotientGroup.mk_pow, mk_eq_one_iff]
    exact hdw_pow_central.2
  rw [orderOf_eq_prime_pow h2 h4]
  norm_num

theorem psl29_card : Nat.card PSL29 = 360 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcardF : Nat.card GF9 = 3 ^ 2 := by
    rw [Nat.card_eq_fintype_card]
    decide
  let eF : GF9 ≃+* GaloisField 3 2 :=
    CFSG.ClassicalModels.finiteFieldEquivGaloisField GF9 3 2 (by norm_num) hcardF
  rw [Nat.card_congr (CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv eF (Fin 2)).toEquiv]
  have hc : Nat.card (GaloisField 3 2) = 3 ^ 2 := GaloisField.card 3 2 (by norm_num)
  have hodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card (GaloisField 3 2)) :=
    ⟨3, 2, by norm_num, by decide, by norm_num, hc⟩
  have h := CFSG.GorensteinWalter.psl2_card_formula (GaloisField 3 2) hodd
  rw [hc] at h
  norm_num at h
  exact h

theorem nonempty_equiv {K : Type} [Group K] (hK : Nonempty (K ≃* PSL(2, GaloisField 3 2))) :
    Nonempty (K ≃* PSL29) := by
  obtain ⟨eK⟩ := hK
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcardF : Nat.card GF9 = 3 ^ 2 := by
    rw [Nat.card_eq_fintype_card]
    decide
  let eF : GF9 ≃+* GaloisField 3 2 :=
    CFSG.ClassicalModels.finiteFieldEquivGaloisField GF9 3 2 (by norm_num) hcardF
  exact ⟨eK.trans (CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv eF (Fin 2)).symm⟩

theorem exists_equiv_of_sylow {K : Type} [Group K] [Finite K]
    (hK : Nonempty (K ≃* PSL(2, GaloisField 3 2))) (T : Sylow 3 K) :
    ∃ Φ : PSL29 ≃* K, (T : Subgroup K) = uHom.range.map Φ.toMonoidHom := by
  obtain ⟨eG⟩ := nonempty_equiv hK
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK360 : Nat.card K = 360 := by rw [Nat.card_congr eG.toEquiv, psl29_card]
  let T₀ : Subgroup K := uHom.range.map eG.symm.toMonoidHom
  have hmem : ∀ x : K, x ∈ T₀ ↔ eG x ∈ uHom.range := fun x => by
    rw [Subgroup.mem_map_equiv]
    rfl
  have hT₀ : Nat.card T₀ = 3 ^ 2 := by
    rw [← uHom_card]
    exact Nat.card_congr (Subgroup.equivMapOfInjective _ _ eG.symm.injective).symm.toEquiv
  have hp : IsPGroup 3 T₀ := IsPGroup.of_card hT₀
  have hidx : ¬ 3 ∣ T₀.index := by
    have h := T₀.index_mul_card
    rw [hT₀, hK360] at h
    have : T₀.index = 40 := by omega
    rw [this]
    norm_num
  obtain ⟨g, hg⟩ := exists_conj_of_sylow hp hidx T
  refine ⟨eG.symm.trans (MulAut.conj g), ?_⟩
  ext t
  rw [Subgroup.mem_map_equiv, hg t, hmem]
  rfl

end CFSG.LocalAnalysis.RankThreeTheoremC.A6Model
