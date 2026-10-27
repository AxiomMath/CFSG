module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84B0Co
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84B0Norm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84A3Facts

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace T84Co

open Matrix Certificates.Asc82NormA6

@[expose] def tS : Equiv.Perm (Fin 6) := Equiv.swap 0 1

@[expose] def tC : Equiv.Perm (Fin 6) := Equiv.swap 2 3 * Equiv.swap 3 4

theorem tC_sign : tC.sign = 1 := by decide +kernel

theorem tS_sq : rho tS * rho tS = 1 := by decide +kernel

theorem tC_cube : rho tC * rho tC * rho tC = 1 := by decide +kernel

theorem tSC_comm : rho tS * rho tC = rho tC * rho tS := by decide +kernel

theorem tS_fix : (Finset.univ.filter fun v : Fin 4 → ZMod 2 => rho tS *ᵥ v = v).card = 8 := by
  decide +kernel

theorem tC_fix : (Finset.univ.filter fun v : Fin 4 → ZMod 2 => rho tC *ᵥ v = v).card = 4 := by
  decide +kernel

theorem tSC_img : ∀ v : Fin 4 → ZMod 2, rho tC *ᵥ (rho tS *ᵥ v - v) = rho tS *ᵥ v - v := by
  decide +kernel

theorem tSC_inter : ∀ v : Fin 4 → ZMod 2, rho tC *ᵥ v = v → rho tS *ᵥ v = v →
    ∃ v' : Fin 4 → ZMod 2, v = rho tS *ᵥ v' - v' := by
  decide +kernel

theorem tS_not_even : ∀ a : Equiv.Perm (Fin 6), a.sign = 1 → rho a ≠ rho tS := by
  decide +kernel

theorem toAdd_mul_inv_vec (a b : Multiplicative (Fin 4 → ZMod 2)) :
    Multiplicative.toAdd (a * b⁻¹) = Multiplicative.toAdd a - Multiplicative.toAdd b := by
  rw [toAdd_mul, toAdd_inv]
  exact (sub_eq_add_neg _ _).symm

theorem s6_coord {G : Type} [Group G] {B : Subgroup G}
    {e : ↥B ≃* Multiplicative (Fin 4 → ZMod 2)} {x w : MulAut ↥B}
    (hx : ActsAs e x (rho tS)) (hw : ActsAs e w (rho tC)) :
    x * x = 1 ∧ Nat.card {b : ↥B // x b = b} = 8 ∧ w ^ 3 = 1 ∧ Nat.card {b : ↥B // w b = b} = 4 ∧
      x * w = w * x ∧ (∀ c : ↥B, w (x c * c⁻¹) = x c * c⁻¹) ∧
      ∀ b : ↥B, w b = b → x b = b → ∃ c : ↥B, b = x c * c⁻¹ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ActsAs.ext ((hx.mul hx).congr tS_sq) (actsAs_one e)
  · rw [card_fix_eq hx]; exact tS_fix
  · rw [pow_three']
    exact ActsAs.ext ((((hw.mul hw).mul hw)).congr tC_cube) (actsAs_one e)
  · rw [card_fix_eq hw]; exact tC_fix
  · exact ActsAs.ext (hx.mul hw) ((hw.mul hx).congr tSC_comm.symm)
  · intro c
    apply e.injective
    apply Multiplicative.toAdd.injective
    have h1 : Multiplicative.toAdd (e (x c * c⁻¹)) =
        rho tS *ᵥ Multiplicative.toAdd (e c) - Multiplicative.toAdd (e c) := by
      rw [map_mul, map_inv, toAdd_mul_inv_vec, hx c]
    rw [hw (x c * c⁻¹), h1]
    exact tSC_img _
  · intro b hwb hxb
    have hw' : rho tC *ᵥ Multiplicative.toAdd (e b) = Multiplicative.toAdd (e b) := by
      rw [← hw b, hwb]
    have hx' : rho tS *ᵥ Multiplicative.toAdd (e b) = Multiplicative.toAdd (e b) := by
      rw [← hx b, hxb]
    obtain ⟨v', hv'⟩ := tSC_inter _ hw' hx'
    refine ⟨e.symm (Multiplicative.ofAdd v'), ?_⟩
    apply e.injective
    apply Multiplicative.toAdd.injective
    rw [map_mul, map_inv, toAdd_mul_inv_vec, hx, MulEquiv.apply_symm_apply, toAdd_ofAdd]
    exact hv'

theorem H0_acts {G : Type} [Group G] {B : Subgroup G}
    (e : ↥B ≃* Multiplicative (Fin 4 → ZMod 2)) {H₁ H₀ : Subgroup (MulAut ↥B)}
    (hnorm : ∀ h ∈ H₀, ∀ a ∈ H₁, h * a * h⁻¹ ∈ H₁)
    (hmem : ∀ h : MulAut ↥B, h ∈ H₁ ↔
      ∃ a : Equiv.Perm (Fin 6), a.sign = 1 ∧ ActsAs e h (rho a))
    {h : MulAut ↥B} (hh : h ∈ H₀) : ∃ p : Equiv.Perm (Fin 6), ActsAs e h (rho p) := by
  have F := Certificates.certificate442267
  have hrho : ∀ a : Equiv.Perm (Fin 6), ∃ g : MulAut ↥B, ActsAs e g (rho a) := by
    intro a
    refine ⟨(CFSG.SectionRank.Ccomm.elemAutEquivGL e).symm (sec8t84RhoGL F a),
      (actsAs_theta e _).congr ?_⟩
    rw [MulEquiv.apply_symm_apply]
    rfl
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin 4) (Fin 4) (ZMod 2), ActsAs e h M :=
    ⟨_, actsAs_theta e h⟩
  obtain ⟨M', hM'⟩ : ∃ M : Matrix (Fin 4) (Fin 4) (ZMod 2), ActsAs e h⁻¹ M :=
    ⟨_, actsAs_theta e h⁻¹⟩
  have hinv1 : M' * M = 1 := by
    have h1 := hM'.mul hM
    rw [inv_mul_cancel] at h1
    exact h1.matrix_eq (actsAs_one e)
  have hinv2 : M * M' = 1 := by
    have h1 := hM.mul hM'
    rw [mul_inv_cancel] at h1
    exact h1.matrix_eq (actsAs_one e)
  have hcomm : ∀ a : Equiv.Perm (Fin 6), a.sign = 1 → ∃ a' : Equiv.Perm (Fin 6), a'.sign = 1 ∧
      M * rho a = rho a' * M := by
    intro a ha
    obtain ⟨g, hg⟩ := hrho a
    obtain ⟨a', ha', hga⟩ := (hmem _).mp (hnorm h hh g ((hmem g).mpr ⟨a, ha, hg⟩))
    refine ⟨a', ha', ?_⟩
    have h2 : M * rho a * M' = rho a' := ((hM.mul hg).mul hM').matrix_eq hga
    calc M * rho a = (M * rho a * M') * M := by
          rw [mul_assoc (M * rho a) M' M, hinv1, mul_one]
      _ = rho a' * M := by rw [h2]
  obtain ⟨p, hp⟩ := F.complete M ⟨M', hinv2⟩ hcomm
  exact ⟨p, hM.congr hp.symm⟩

end T84Co

theorem sec8t84FactS6_of_cert : Sec8T84FactS6 := by
  intro G _ B hB H₁ H₀ hle hH₁ hH₀
  obtain ⟨e, ψ, hact, hmem⟩ := sec8t84_a6_conj B hB H₁ hH₁
  have c1 : Nat.card ↥H₁ = 360 := by
    rw [Nat.card_congr ψ.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide
  have c0 : Nat.card ↥H₀ = 720 := by
    obtain ⟨φ⟩ := hH₀
    rw [Nat.card_congr φ.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    decide
  have hnorm := T84Co.normal_of_orders hle c1 c0
  have hmem' : ∀ h : MulAut ↥B, h ∈ H₁ ↔
      ∃ a : Equiv.Perm (Fin 6), a.sign = 1 ∧ T84Co.ActsAs e h (Certificates.Asc82NormA6.rho a) :=
    hmem
  have hact0 : ∀ h : ↥H₀, ∃ p : Equiv.Perm (Fin 6),
      T84Co.ActsAs e (h : MulAut ↥B) (Certificates.Asc82NormA6.rho p) :=
    fun h => T84Co.H0_acts e hnorm hmem' h.2
  choose ι hι using hact0
  have hinj : Function.Injective ι := by
    intro h h' hh
    apply Subtype.ext
    refine T84Co.ActsAs.ext (hι h) ?_
    rw [hh]
    exact hι h'
  have hbij : Function.Bijective ι := by
    refine hinj.bijective_of_nat_card_le ?_
    rw [c0, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    decide
  obtain ⟨x0, hx0⟩ := hbij.2 T84Co.tS
  have hx : T84Co.ActsAs e (x0 : MulAut ↥B) (Certificates.Asc82NormA6.rho T84Co.tS) := by
    rw [← hx0]
    exact hι x0
  obtain ⟨w, hwdef⟩ : ∃ w : ↥H₁, ψ w =
      ⟨T84Co.tC, Equiv.Perm.mem_alternatingGroup.mpr T84Co.tC_sign⟩ :=
    ⟨ψ.symm _, ψ.apply_symm_apply _⟩
  have hw : T84Co.ActsAs e (w : MulAut ↥B) (Certificates.Asc82NormA6.rho T84Co.tC) := by
    intro b
    have h2 := hact w b
    rw [hwdef] at h2
    exact h2
  obtain ⟨k1, k2, k3, k4, k5, k6, k7⟩ := T84Co.s6_coord hx hw
  refine ⟨x0, x0.2, ?_, k1, k2, w, w.2, k3, k4, k5, k6, k7⟩
  intro hx1
  obtain ⟨a, ha, hxa⟩ := (hmem' _).mp hx1
  exact T84Co.tS_not_even a ha (hxa.matrix_eq hx)

end CFSG.OddStandard.SmallF3.Omega
