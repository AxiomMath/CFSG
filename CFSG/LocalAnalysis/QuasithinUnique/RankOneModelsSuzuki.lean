module

public import CFSG.LocalAnalysis.QuasithinUnique.RankOneModelsBasic
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructureTransport

public section

namespace CFSG.QuasithinUnique

open CFSG.Blueprint CFSG.LieType.Ree CFSG.ShultStronglyClosedTI.SuzukiModel

variable {a : ℕ} {K : Type} [Field K] [Finite K]

@[expose] noncomputable def suzukiRootCenterHom
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Multiplicative K →* suzukiGroup a K where
  toFun v := suzukiSElt a K 0 (Multiplicative.toAdd v)
  map_one' := suzukiSElt_zero_zero hK
  map_mul' _ _ := by
    rw [suzukiSElt_mul hK, zero_add, zero_pow (pow_ne_zero _ two_ne_zero), zero_mul, add_zero,
      toAdd_mul]

theorem suzukiRootCenterHom_apply
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (x : K) :
    suzukiRootCenterHom hK (Multiplicative.ofAdd x) = suzukiSElt a K 0 x := rfl

theorem suzukiRootCenterHom_injective
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Function.Injective (suzukiRootCenterHom hK) := fun _ _ h =>
  Multiplicative.toAdd.injective (suzukiSElt_inj.1 h).2

theorem range_suzukiRootCenterHom
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    (suzukiRootCenterHom hK).range = suzukiZ0 a K := by
  ext g
  have hz := Set.ext_iff.mp (coe_suzukiZ0 hK) g
  rw [SetLike.mem_coe] at hz
  rw [MonoidHom.mem_range, hz]
  exact ⟨fun ⟨x, hx⟩ => ⟨Multiplicative.toAdd x, hx⟩, fun ⟨v, hv⟩ => ⟨Multiplicative.ofAdd v, hv⟩⟩

theorem suzukiDElt_conj_center
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (l : Kˣ) (x : K) :
    suzukiDElt a K l * suzukiRootCenterHom hK (Multiplicative.ofAdd x) * (suzukiDElt a K l)⁻¹ =
      suzukiRootCenterHom hK
        (Multiplicative.ofAdd ((((l⁻¹ ^ (2 ^ (a + 1) + 1) : Kˣ)) : K) * x)) := by
  rw [suzukiRootCenterHom_apply, suzukiRootCenterHom_apply, suzukiDElt_conj' hK, mul_zero,
    Units.val_pow_eq_pow_val]

theorem suzuki_hasFieldScalarStructure
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    HasFieldScalarStructure (suzukiZ0 a K) (2 ^ (2 * a + 1)) := by
  obtain ⟨hchar, -, -, -, -, -, -, -, -, -, hbij, -⟩ := suzuki_frobenius_exponents a K hK
  have h := suzukiPointAction_suzukiGroup hK
  have hcent := (suzuki_unipotent_structure hK).2.2.2.2.2.1
  have h' := hasFieldScalarStructure_of_regular_root
    (⟨suzukiInfty K, suzukiInfty_mem_suzukiOmega a K⟩ : suzukiOmegaSub hK) (suzukiU a K)
    (suzukiT a K) K (suzukiRootCenterHom hK) (suzukiRootCenterHom_injective hK) ?_ ?_ ?_
    h.sup_eq_stabilizer.ge ?_ ?_ ?_
  · rw [range_suzukiRootCenterHom, hK] at h'
    exact h'
  · rw [range_suzukiRootCenterHom]
    exact suzukiZ0_le_suzukiU
  · exact h.sup_eq_stabilizer ▸ le_sup_left
  · intro ω u hu hω hfix
    have h1 := (h.regular ω ω hω hω).unique (y₁ := ⟨u, hu⟩) (y₂ := 1) hfix (one_smul _ _)
    exact congrArg Subtype.val h1
  · intro p hp x
    rw [mul_inv_eq_iff_eq_mul]
    exact (hcent _ ((range_suzukiRootCenterHom hK).le ⟨Multiplicative.ofAdd x, rfl⟩) p hp).symm
  · intro t ht
    obtain ⟨l, rfl⟩ := mem_suzukiT_iff.1 ht
    exact ⟨l⁻¹ ^ (2 ^ (a + 1) + 1), fun x => suzukiDElt_conj_center hK l x⟩
  · intro c
    obtain ⟨l, hl⟩ := hbij.2 c
    refine ⟨suzukiDElt a K l⁻¹, suzukiDElt_mem_suzukiT a K _, fun x => ?_⟩
    rw [suzukiDElt_conj_center hK, inv_inv]
    have : l ^ (2 ^ (a + 1) + 1) = c := by
      have h2 : (l ^ ((2 ^ (a + 1) + 1 : ℕ) : ℤ) : Kˣ) = c := by
        simpa using hl
      rwa [zpow_natCast] at h2
    rw [this]

end CFSG.QuasithinUnique
