module

public import CFSG.FeitThompson.Definitions.NormalInducedCharacterFamily
public import CFSG.FeitThompson.Representations.QuotientIrreducibleCharsDegreeSum
import CFSG.FeitThompson.Representations.PrimeTILocalBridgeSupportNorm
import CFSG.FeitThompson.Representations.AbelianByAbelianFrobeniusCharacters

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {L : Type*} [Group L] {N K : Subgroup L} [N.Normal]

theorem mk_mem_map_mk'_iff_of_le (hNK : N ≤ K) (z : L) :
    (QuotientGroup.mk z : L ⧸ N) ∈ Subgroup.map (QuotientGroup.mk' N) K ↔ z ∈ K := by
  have hker : (QuotientGroup.mk' N).ker ≤ K := by rw [QuotientGroup.ker_mk']; exact hNK
  have h := Subgroup.comap_map_eq_self (f := (QuotientGroup.mk' N)) (H := K) hker
  refine ⟨fun hz => ?_, fun hz => ⟨z, hz, rfl⟩⟩
  have hmem : z ∈ Subgroup.comap (QuotientGroup.mk' N) (Subgroup.map (QuotientGroup.mk' N) K) :=
    Subgroup.mem_comap.2 hz
  rwa [h] at hmem

def quotSubgroupHom (N K : Subgroup L) [N.Normal] :
    ↥K →* ↥(Subgroup.map (QuotientGroup.mk' N) K) where
  toFun x := ⟨QuotientGroup.mk (x : L), ⟨x, x.2, rfl⟩⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem coe_quotSubgroupHom_apply (x : ↥K) :
    ((quotSubgroupHom N K x : ↥(Subgroup.map (QuotientGroup.mk' N) K)) : L ⧸ N)
      = QuotientGroup.mk (x : L) := (rfl)

theorem surjective_quotSubgroupHom : Function.Surjective (quotSubgroupHom N K) := by
  rintro ⟨z, x, hx, hxz⟩
  exact ⟨⟨x, hx⟩, Subtype.ext hxz⟩

noncomputable def deflateChar (N K : Subgroup L) [N.Normal]
    (θ : ↥(Subgroup.map (QuotientGroup.mk' N) K) → ℂ) : ↥K → ℂ := θ ∘ quotSubgroupHom N K

theorem deflateChar_apply (θ : ↥(Subgroup.map (QuotientGroup.mk' N) K) → ℂ) (x : ↥K) :
    deflateChar N K θ x = θ (quotSubgroupHom N K x) := (rfl)

theorem deflateChar_mk (θ : ↥(Subgroup.map (QuotientGroup.mk' N) K) → ℂ) {x : L} (hx : x ∈ K)
    (hx' : (QuotientGroup.mk x : L ⧸ N) ∈ Subgroup.map (QuotientGroup.mk' N) K) :
    deflateChar N K θ ⟨x, hx⟩ = θ ⟨QuotientGroup.mk x, hx'⟩ := by
  rw [deflateChar_apply]
  rfl

@[simp] theorem deflateChar_one (θ : ↥(Subgroup.map (QuotientGroup.mk' N) K) → ℂ) :
    deflateChar N K θ 1 = θ 1 := by
  rw [deflateChar_apply, map_one]

theorem deflateChar_mem_Irr {θ : ↥(Subgroup.map (QuotientGroup.mk' N) K) → ℂ}
    (hθ : θ ∈ Irr ↥(Subgroup.map (QuotientGroup.mk' N) K)) : deflateChar N K θ ∈ Irr ↥K :=
  FrobeniusInduction.mem_Irr_comp_of_surjective surjective_quotSubgroupHom hθ

theorem deflateChar_injective :
    Function.Injective (deflateChar N K : (↥(Subgroup.map (QuotientGroup.mk' N) K) → ℂ) → ↥K → ℂ) :=
  fun _ _ h => funext fun y => by
    obtain ⟨x, rfl⟩ := surjective_quotSubgroupHom (N := N) (K := K) y
    exact congrFun h x

theorem indClassFun_comp_mk [Fintype L] [Fintype (L ⧸ N)] (hNK : N ≤ K)
    (θ : ↥(Subgroup.map (QuotientGroup.mk' N) K) → ℂ) :
    indClassFun (Subgroup.map (QuotientGroup.mk' N) K) θ ∘ QuotientGroup.mk
      = indClassFun K (deflateChar N K θ) := by
  classical
  funext y
  rw [Function.comp_apply, indClassFun_apply, indClassFun_apply]
  have hval : ∀ t : L, (if h : (QuotientGroup.mk t : L ⧸ N)⁻¹ * (QuotientGroup.mk y : L ⧸ N)
      * (QuotientGroup.mk t : L ⧸ N) ∈ Subgroup.map (QuotientGroup.mk' N) K then θ ⟨_, h⟩ else 0)
      = (if h : t⁻¹ * y * t ∈ K then deflateChar N K θ ⟨t⁻¹ * y * t, h⟩ else 0) := by
    intro t
    have hmk : (QuotientGroup.mk t : L ⧸ N)⁻¹ * (QuotientGroup.mk y : L ⧸ N)
        * (QuotientGroup.mk t : L ⧸ N) = (QuotientGroup.mk (t⁻¹ * y * t) : L ⧸ N) := by
      simp [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [hmk]
    by_cases hmem : t⁻¹ * y * t ∈ K
    · rw [dif_pos ((mk_mem_map_mk'_iff_of_le hNK _).2 hmem), dif_pos hmem]
      rfl
    · rw [dif_neg (fun h => hmem ((mk_mem_map_mk'_iff_of_le hNK _).1 h)), dif_neg hmem]
  have h1 := sum_comp_mk (N := N)
    (fun s : L ⧸ N => (if h : s⁻¹ * (QuotientGroup.mk y : L ⧸ N) * s
      ∈ Subgroup.map (QuotientGroup.mk' N) K then θ ⟨_, h⟩ else 0))
  rw [Finset.sum_congr rfl (fun t _ => hval t)] at h1
  have hcard : (Nat.card N) * (Nat.card (Subgroup.map (QuotientGroup.mk' N) K))
      = Nat.card K := card_mul_card_map_mk' hNK
  have hNne : (Nat.card N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hMne : (Nat.card (Subgroup.map (QuotientGroup.mk' N) K) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hKc : (Nat.card K : ℂ) = (Nat.card N : ℂ)
      * (Nat.card (Subgroup.map (QuotientGroup.mk' N) K) : ℂ) := by
    rw [← Nat.cast_mul, hcard]
  rw [hKc, h1]
  field_simp

end CFSG.FeitThompson
