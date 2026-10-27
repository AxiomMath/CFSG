module

public import CFSG.GH74.GLS.IVK.Lifted.IIAutQuat
public import CFSG.GH74.GLS.IVK.Lifted.IIAutA7
public import CFSG.GH74.GLS.IVK.Lifted.Lem119V
public import CFSG.GH74.GLS.IVK.Lifted.B2Split
public import CFSG.GH74.GLS.IVK.Lifted.IIAut

public section

namespace CFSG.GH74.GLS.IVK.Lifted

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.DisconnectedInvolutionGraph CFSG.DisconnectedInvolutionGraph.Helpers
  CFSG.GH74.Uniqueness.SU.SU13.TA

section Sylow

variable {Q : Type} [Group Q] [Finite Q]

omit [Finite Q] in
theorem isQuasisimple_of_sl2or2a7 (hQ : IsSL2Or2A7 Q) : CFSG.IsQuasisimple Q := by
  rcases sl_or_a7 hQ with ⟨F, _, _, _, h3, ⟨e⟩⟩ | h7
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm (isQuasisimple_sl2' (by omega))
  · exact h7.1

theorem unique_involution_of_sl2or2a7 (hQ : IsSL2Or2A7 Q) {u v : Q} (hu : orderOf u = 2)
    (hv : orderOf v = 2) : u = v := by
  rcases hQ.1 with ⟨F, _, _, ⟨hodd, -⟩, ⟨e⟩⟩ | h7
  · exact e.injective (statedSL_two_involution_unique hodd (by rwa [MulEquiv.orderOf_eq])
      (by rwa [MulEquiv.orderOf_eq]))
  · have hT : CFSG.GH74.Uniqueness.SU.K.IsTwoAlt Q 7 :=
      ⟨h7.1, (inferInstance : Finite Q), h7.2.1, h7.2.2⟩
    obtain ⟨π, hπ⟩ := TwoCover.exists_of_isTwoAlt hT
    obtain ⟨z, -, hz1, hz2, hzk⟩ := hπ.exists_z
    have hzu : ∀ x : Q, orderOf x = 2 → x = z := fun x hx => by
      rcases hzk x (mem_ker_of_orderOf_eq_two_alt_seven hπ hx) with h | h
      · rw [h, orderOf_one] at hx
        omega
      · exact h
    rw [hzu u hu, hzu v hv]

theorem sylow_isQuaternionTwoGroup (hq : CFSG.IsQuasisimple Q)
    (hno : ∀ u v : Q, orderOf u = 2 → orderOf v = 2 → u * v = v * u → u = v) (P : Sylow 2 Q) :
    ∃ n : ℕ, IVK.IsQuaternionTwoGroup ↥(P : Subgroup Q) n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hncyc := sylow_two_not_cyclic_of_quasisimple hq P
  have hrank : NoCommutingDistinctInvolutions ↥(P : Subgroup Q) := by
    intro u v huv
    have hu : orderOf ((u.1 : ↥(P : Subgroup Q)) : Q) = 2 := by
      rw [Subgroup.orderOf_coe]
      exact u.2
    have hv : orderOf ((v.1 : ↥(P : Subgroup Q)) : Q) = 2 := by
      rw [Subgroup.orderOf_coe]
      exact v.2
    have hcomm : ((u.1 : ↥(P : Subgroup Q)) : Q) * ((v.1 : ↥(P : Subgroup Q)) : Q) =
        ((v.1 : ↥(P : Subgroup Q)) : Q) * ((u.1 : ↥(P : Subgroup Q)) : Q) := by
      have := congrArg (fun x : ↥(P : Subgroup Q) => (x : Q)) huv
      simpa using this
    exact Subtype.ext (Subtype.ext (hno _ _ hu hv hcomm))
  rcases rank_one_two_cyclic_or_quaternion P.isPGroup' hrank with hc | ⟨e, he1, ⟨ε⟩⟩
  · exact absurd hc hncyc
  · refine ⟨e + 2, by omega, ?_⟩
    rw [Nat.add_sub_cancel]
    exact ⟨ε.symm⟩

theorem sylow_quat_of_sl2or2a7 (hQ : IsSL2Or2A7 Q) (P : Sylow 2 Q) :
    ∃ n : ℕ, IVK.IsQuaternionTwoGroup ↥(P : Subgroup Q) n :=
  sylow_isQuaternionTwoGroup (isQuasisimple_of_sl2or2a7 hQ)
    (fun _ _ hu hv _ => unique_involution_of_sl2or2a7 hQ hu hv) P

omit [Finite Q] in
theorem exists_sylow_of_isSylow2In {P : Subgroup Q}
    (hP : CFSG.GH74.GLS.Stage1.Thm6.IsSylow2In P ⊤) : ∃ P' : Sylow 2 Q, (P' : Subgroup Q) = P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨hP.2.1.toSylow (by simpa [Subgroup.relIndex_top_right] using hP.2.2), rfl⟩

@[expose] noncomputable def restrictAutOnSylow (φ : MulAut Q) (P : Subgroup Q) (hP : ∀ p ∈ P, φ p ∈ P) :
    MulAut ↥P :=
  MulEquiv.ofBijective ((φ.toMonoidHom.comp P.subtype).codRestrict P (fun p => hP p p.2))
    (Finite.injective_iff_bijective.1 (fun _ _ h => Subtype.ext (φ.injective (congrArg Subtype.val h))))

theorem restrictAutOnSylow_apply (φ : MulAut Q) (P : Subgroup Q) (hP : ∀ p ∈ P, φ p ∈ P) (p : ↥P) :
    ((restrictAutOnSylow φ P hP p : ↥P) : Q) = φ p := rfl

end Sylow

section SL2

variable {F : Type} [Field F] [Finite F] {Q : Type} [Group Q] [Finite Q]

theorem sl2_phi_moves_sylow (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F)
    (e : Q ≃* Matrix.SpecialLinearGroup (Fin 2) F) (φ : MulAut Q) (hφ2 : φ * φ = 1) (hφ1 : φ ≠ 1)
    (P : Sylow 2 Q) {n : ℕ} (hn : IVK.IsQuaternionTwoGroup ↥(P : Subgroup Q) n) :
    ∃ p ∈ (P : Subgroup Q), φ p ≠ p := by
  by_contra hfix
  push Not at hfix
  have hα2 : MulAut.congr e φ * MulAut.congr e φ = 1 := by rw [← map_mul, hφ2, map_one]
  have hα1 : MulAut.congr e φ ≠ 1 := fun h =>
    hφ1 ((MulAut.congr e).injective (h.trans (map_one _).symm))
  obtain ⟨hn3, ⟨ε⟩⟩ := hn
  have hm : NeZero (2 ^ (n - 2)) := ⟨by positivity⟩
  have hm2 : 2 ≤ 2 ^ (n - 2) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  by_cases hσ : (gammaOf hodd h3 (MulAut.congr e φ)).right = 1
  · obtain ⟨G, hG⟩ := eq_slConjugation_of_right_eq_one hodd h3 _ hσ
    have hcomm : ∀ a ∈ fixedSubgroup Q φ, ∀ b ∈ fixedSubgroup Q φ, a * b = b * a := by
      apply comm_fixed_of_congr e φ
      rw [hG]
      exact fixed_comm_of_slConjugation G (hG ▸ hα1)
    obtain ⟨x, y, hxy⟩ := ii4_quat_noncomm hm2
    apply hxy
    apply ε.symm.injective
    rw [map_mul, map_mul]
    apply Subtype.ext
    have hx := hfix _ (ε.symm x).2
    have hy := hfix _ (ε.symm y).2
    have := hcomm _ hx _ hy
    simpa using this
  · have hσ2 : ∃ j : ℕ, orderOf (gammaOf hodd h3 (MulAut.congr e φ)).right = 2 ^ j := by
      have hsq : (gammaOf hodd h3 (MulAut.congr e φ)).right ^ 2 = 1 := by
        rw [pow_two, ← gammaOf_mul_right, hα2, map_one]
        rfl
      exact ⟨1, by rw [pow_one]; exact orderOf_eq_prime hsq hσ⟩
    set b : Q := ((ε.symm (QuaternionGroup.a 1) : ↥(P : Subgroup Q)) : Q) with hb
    have hbfix : φ b = b := hfix b (ε.symm _).2
    have hbo : orderOf b = 2 ^ (n - 1) := by
      rw [hb, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, QuaternionGroup.orderOf_a_one]
      have hn' : n - 1 = (n - 2) + 1 := by omega
      rw [hn', pow_succ]
      ring
    have hcardP : Nat.card ↥(P : Subgroup Q) = 2 ^ n := by
      rw [Nat.card_congr ε.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
      have hn' : n = (n - 2) + 2 := by omega
      conv_rhs => rw [hn', pow_add]
      ring
    have hbig : 2 ^ ((n - 1) + 1) =
        2 ^ (Nat.card (Matrix.SpecialLinearGroup (Fin 2) F)).factorization 2 := by
      have h1 : Nat.card ↥(P : Subgroup Q) = 2 ^ (Nat.card Q).factorization 2 :=
        Sylow.card_eq_multiplicity P
      rw [Nat.card_congr e.toEquiv] at h1
      have hn1 : (n - 1) + 1 = n := by omega
      rw [hn1, ← hcardP, h1]
    exact not_fixes_big_cyclic hodd h3 e φ hσ hσ2 hbfix hbo hbig

end SL2

theorem ii4_aut_c : II4_Aut_c := by
  intro Q _ _ hQ φ hφ2 hφ1 P hP hPφ
  obtain ⟨P', hP'⟩ := exists_sylow_of_isSylow2In hP
  subst hP'
  obtain ⟨n, hn⟩ := sylow_quat_of_sl2or2a7 hQ P'
  have hmove : ∃ p ∈ (P' : Subgroup Q), φ p ≠ p := by
    rcases sl_or_a7 hQ with ⟨F, _, _, hodd, h3, ⟨e⟩⟩ | h7
    · exact sl2_phi_moves_sylow hodd h3 e φ hφ2 hφ1 P' hn
    · obtain ⟨π, z, h, -⟩ := CFSG.GH74.KGroups.TwoA7.exists_cover h7
      exact a7_phi_moves_sylow h φ hφ2 hφ1 hP
  obtain ⟨p, hp, hpne⟩ := hmove
  have hφP1 : restrictAutOnSylow φ (P' : Subgroup Q) hPφ ≠ 1 := by
    intro h1
    apply hpne
    have := congrArg (fun ρ : MulAut ↥(P' : Subgroup Q) => ((ρ ⟨p, hp⟩ : ↥(P' : Subgroup Q)) : Q)) h1
    simpa [restrictAutOnSylow_apply] using this
  have hφP2 : restrictAutOnSylow φ (P' : Subgroup Q) hPφ * restrictAutOnSylow φ (P' : Subgroup Q) hPφ = 1 := by
    ext x
    have := congrArg (fun ρ : MulAut Q => ρ (x : Q)) hφ2
    simpa [restrictAutOnSylow_apply] using this
  obtain ⟨w, hw4, hw⟩ := exists_order_four_inverted hn _ hφP2 hφP1
  refine ⟨(w : Q), w.2, by rw [Subgroup.orderOf_coe]; exact hw4, ?_⟩
  have := congrArg Subtype.val hw
  simpa [restrictAutOnSylow_apply] using this

end CFSG.GH74.GLS.IVK.Lifted
