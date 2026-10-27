module

public import CFSG.Quasithin.H13.L32NLem14411f
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem14411e

public section

namespace CFSG.Quasithin.H13.L14411

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open Mat8Cert S7Cert L1442M

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V V₂ : Subgroup G} {g : G}
  {D : HatModelU (fsuU T V)} {e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)}

theorem Ctx_F4.JH_F4 (C : Ctx_F4 G T L V V₂ g D e) (k : ℕ) :
    lOne L (fsuV1 T V) ⊔ xk D e k ⊔ T ≤ l32nH T V :=
  sup_le (sup_le L1H (xk_le_H k)) C.TH_F4


namespace Ctx_F4
open CFSG.Quasithin.H13.L14411.Ctx_F4

variable (C : Ctx_F4 G T L V V₂ g D e)
include C

theorem img_J_F4 {j k : ℕ} (hj : j = 1 ∨ j = 2) (hjk : (j = 1 ∧ k = 2) ∨ (j = 2 ∧ k = 1))
    (hjeq : img8 D e (lOne L (fsuV1 T V) ⊔ T) = M7 j) :
    img8 D e (lOne L (fsuV1 T V) ⊔ xk D e k ⊔ T) = M12 := by
  have hk3 : k < 3 := by omega
  rw [img8_sup D e (sup_le L1H (xk_le_H k) |>.trans HN) (C.TH_F4.trans HN),
    img8_sup D e (L1H.trans HN) ((xk_le_H k).trans HN), C.img_L1_F4 hj hjeq, C.img_xk_F4 hk3,
    C.imgT, M12_eq]
  rcases hjk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · rw [sup_comm (O7 2)]

theorem nonempty_quot_F4 {j k : ℕ} (hj : j = 1 ∨ j = 2) (hjk : (j = 1 ∧ k = 2) ∨ (j = 2 ∧ k = 1))
    (hjeq : img8 D e (lOne L (fsuV1 T V) ⊔ T) = M7 j) :
    Nonempty (OTwoQuot (lOne L (fsuV1 T V) ⊔ xk D e k ⊔ T) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJN : lOne L (fsuV1 T V) ⊔ xk D e k ⊔ T ≤ Subgroup.normalizer (fsuU T V : Set G) :=
    (C.JH_F4 k).trans HN
  have himg := C.img_J_F4 hj hjk hjeq
  let φ : ↥(lOne L (fsuV1 T V) ⊔ xk D e k ⊔ T) →* ↥M12 :=
    (hom8 D e hJN).codRestrict M12 fun x => by
      rw [← himg, ← range_hom8 D e hJN]
      exact ⟨x, rfl⟩
  have hφ : Function.Surjective φ := by
    rintro ⟨γ, hγ⟩
    rw [← himg, ← range_hom8 D e hJN] at hγ
    obtain ⟨x, rfl⟩ := hγ
    exact ⟨x, rfl⟩
  have hk : IsPGroup 2 (chi.comp φ).ker := by
    rintro ⟨x, hx⟩
    have hsq := sq_eq_one_of_chi (MonoidHom.mem_ker.mp hx)
    have hxx : hom8 D e hJN (x * x) = 1 := by
      rw [map_mul]
      exact hsq
    have hxQ : ((x * x : ↥(lOne L (fsuV1 T V) ⊔ xk D e k ⊔ T)) : G) ∈ pCoreOf 2 (l32nH T V) :=
      (C.matOf_eq_one_iff_F4 (C.JH_F4 k (x * x).2)).mp hxx
    obtain ⟨n, hn⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) (l32nH T V) ⟨_, hxQ⟩
    refine ⟨n + 1, Subtype.ext (Subtype.ext ?_)⟩
    have h1 : ((x : G) * x) ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
    rw [pow_succ', pow_mul, sq, h1]
  exact nonempty_quot_equiv_of_surj (chi.comp φ) (chi_surjective.comp hφ) hk s33_normal_two

end Ctx_F4

theorem y1444Claim_of_ctx_F4 (C : Ctx_F4 G T L V V₂ g D e) : Y1444Claim T L V V₂ g := by
  obtain ⟨j, hj, hjeq⟩ := C.exists_j_F4
  obtain ⟨k, hk, hjk⟩ : ∃ k, (k = 1 ∨ k = 2) ∧ ((j = 1 ∧ k = 2) ∨ (j = 2 ∧ k = 1)) := by
    rcases hj with rfl | rfl
    · exact ⟨2, Or.inr rfl, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨1, Or.inl rfl, Or.inr ⟨rfl, rfl⟩⟩
  refine ⟨xk D e k, ⟨xk_le_H k, C.T_le_normalizer_xk_F4 k, oTwoUpper_xk k, C.relIndex_xk_F4 hk,
    C.card_commutator_F4 hk, C.commutator_le_E_F4 hk⟩, fun h => ?_, C.nonempty_quot_F4 hj hjk hjeq⟩
  have h1 := C.img_xk_F4 (k := k) (by omega)
  rw [h, C.img_L1_F4 hj hjeq] at h1
  rcases hjk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact O7_ne h1
  · exact O7_ne h1.symm

theorem y1444Claim_of_case4_F4 (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) (h1222 : Stmt12_2_2_F4)
    (h12213 : Stmt12_2_13_F4) (h12811 : Lemma12_8_11_F4) (h12812 : Lemma12_8_12_two_F4)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h : Hyp14310One G T L V)
    (hext : CFSG.IsExtraspecialPGroup 2 ↥(fsuU T V)) (hV₂ : IsL32NPlane T V V₂)
    (hgP : g ∈ p128 T L V) (hgH : g ∉ l32nH T V) (h4 : Case1442Four T V V₂ g D) :
    Y1444Claim T L V V₂ g := by
  obtain ⟨e, C⟩ := exists_ctx_F4 h1332 h1334 h1222 h12213 h12811 h12812 h37 h38 h39 h hext hV₂ hgP
    hgH h4
  exact y1444Claim_of_ctx_F4 C

end CFSG.Quasithin.H13.L14411
