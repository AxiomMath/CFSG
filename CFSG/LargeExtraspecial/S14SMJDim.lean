module

public import CFSG.LargeExtraspecial.S14SMJLoc
public import CFSG.LargeExtraspecial.S14SMGPair

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14.SMJ

open Subgroup Module CFSG.Open CFSG.SmithE CFSG.RankThree.OrthogonalInvolutions

variable {G : Type} [Group G] [Finite G]

theorem finrank_commQt_le (hM : SmithE22Module) [IsSimpleGroup G]
    (S : Setting G) (hw : S.width = 10) (hU : Nonempty (Mbar0 S ≃* timmesfeldPSU 6)) {x : G}
    (hx : IsConj S.z x) (hxM : x ∈ S.M) (hxQ : x ∉ S.QG) :
    finrank (ZMod 2) (S.commQt x) ≤ 6 := by
  obtain ⟨φ, -, -, -, h4⟩ := hM G S hw hU
  obtain ⟨k, hk, hA⟩ := h4 x hx hxM hxQ
  change SMG.Acts S φ x (applyCols (tvCols k)) at hA
  obtain ⟨-, hck, hk3⟩ := SMG.span_parts hk
  set D := spanData (tvCols k)
  have hd : ∀ v : S.commQt x, ∃ d : Fin 64, SMG.code (φ v) = applyCols D.basis d := by
    intro v
    obtain ⟨c, hc, hcv⟩ := SMG.code_mem_commQt hxM hA v.2
    have hlt : applyCols D.coef c < 2 ^ 6 := SMG.applyCols_lt (n := 6) (fun m hm => by
      have hm' : m < 20 := by rw [hck] at hm; exact hm
      have := (hk3 m hm').1
      norm_num
      exact this) c
    refine ⟨⟨applyCols D.coef c, by simpa using hlt⟩, ?_⟩
    rw [hcv]
    exact SMG.comm_eq_basis' (SMG.size_tvCols k) hck (fun m hm => (hk3 m hm).2.1) hc
  choose f hf using hd
  have hinj : Function.Injective f := by
    intro v w hvw
    apply Subtype.ext
    apply SMG.psi_inj S φ
    rw [hf v, hf w, hvw]
  have hcard := Nat.card_le_card_of_injective f hinj
  rw [Nat.card_eq_fintype_card (α := Fin 64), Fintype.card_fin, S.card_submodule] at hcard
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp (hcard.trans (by norm_num))

theorem card_cent2_ge (hM : SmithE22Module) (h25 : SmithE25)
    (h34a : SmithE34a) [IsSimpleGroup G] (S : Setting G) (hw : S.width = 10)
    (hU : Nonempty (Mbar0 S ≃* timmesfeldPSU 6)) {t u : G} (ht : IsConj S.z t)
    (hu : IsConj S.z u) (htM : t ∈ S.M) (huM : u ∈ S.M) (htQ : t ∉ S.QG) (huQ : u ∉ S.QG)
    (h3 : orderOf (t * u) = 3) : 2 ^ 9 ≤ Nat.card ↥(S.QG ⊓ cent2 t u) := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  have hθM : t * u ∈ S.M := S.M.mul_mem htM huM
  have hθ3 : (t * u) ^ 3 = 1 := by rw [← h3]; exact pow_orderOf_eq_one _
  rw [← cqx_eq_cent2 h25 h34a S hw hU ht hu htM huM htQ huQ h3,
    S.card_cqx_of_pow_three hθM hθ3]
  have hle : S.fixQt t ⊓ S.fixQt u ≤ fixSpace (S.rhoL hθM) := by
    intro v hv
    obtain ⟨hvt, hvu⟩ := Submodule.mem_inf.mp hv
    rw [S.fixQt_of_mem htM, mem_fixSpace] at hvt
    rw [S.fixQt_of_mem huM, mem_fixSpace] at hvu
    rw [mem_fixSpace]
    have hmul : S.rhoL hθM = S.rhoL htM * S.rhoL huM := by
      have h := map_mul S.ρ ⟨t, htM⟩ ⟨u, huM⟩
      have e : (⟨t * u, hθM⟩ : S.M) = ⟨t, htM⟩ * ⟨u, huM⟩ := rfl
      change ((S.ρ ⟨t * u, hθM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) = _
      rw [e, h]
      rfl
    rw [hmul, LinearEquiv.mul_apply]
    change S.rhoL htM (S.rhoL huM v) = v
    change (S.ρ ⟨u, huM⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v at hvu
    change (S.ρ ⟨t, htM⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v at hvt
    change (S.ρ ⟨t, htM⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((S.ρ ⟨u, huM⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = v
    rw [hvu, hvt]
  have hdimQ : finrank (ZMod 2) S.Qt = 20 := by rw [S.finrank_Qt_eq_two_mul_width, hw]
  have ht2 : t ^ 2 = 1 := by rw [sq]; exact SmithQ.mul_self_eq_one_of_isConj S ht
  have hu2 : u ^ 2 = 1 := by rw [sq]; exact SmithQ.mul_self_eq_one_of_isConj S hu
  have hft : 14 ≤ finrank (ZMod 2) (S.fixQt t) := by
    rw [S.fixQt_eq_orthogonal htM ht2, LinearMap.BilinForm.finrank_orthogonal S.q_nondegenerate,
      hdimQ]
    have := finrank_commQt_le hM S hw hU ht htM htQ
    omega
  have hfu : 14 ≤ finrank (ZMod 2) (S.fixQt u) := by
    rw [S.fixQt_eq_orthogonal huM hu2, LinearMap.BilinForm.finrank_orthogonal S.q_nondegenerate,
      hdimQ]
    have := finrank_commQt_le hM S hw hU hu huM huQ
    omega
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq (S.fixQt t) (S.fixQt u)
  have hsup : finrank (ZMod 2) ↥(S.fixQt t ⊔ S.fixQt u) ≤ 20 := hdimQ ▸ Submodule.finrank_le _
  have h8 : 8 ≤ finrank (ZMod 2) ↥(fixSpace (S.rhoL hθM)) :=
    le_trans (by omega) (Submodule.finrank_mono hle)
  calc 2 ^ 9 = 2 * 2 ^ 8 := by norm_num
    _ ≤ 2 * 2 ^ finrank (ZMod 2) ↥(fixSpace (S.rhoL hθM)) :=
      Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by norm_num) h8)

theorem forty_three_dvd_card_PSU {m : ℕ} (h7 : 7 ≤ m) (h12 : m ≤ 12) :
    43 ∣ Nat.card (timmesfeldPSU m) := by
  rw [Nat.card_congr ((timmesfeldPSUEquiv (n := m) (by omega)).trans
    (ClassicalGroups.UnitaryFlag.unitaryPSUEquiv unitaryFieldData_two_one
      (n := m) (by omega))).toEquiv,
    Timmesfeld.ClassicalOrders.card_statedProj_statedSU Nat.prime_two le_rfl
      (by rw [GaloisField.card 2 2 (by norm_num)]; norm_num) (by omega)]
  interval_cases m <;> decide

end CFSG.LargeExtraspecial.S14.SMJ
