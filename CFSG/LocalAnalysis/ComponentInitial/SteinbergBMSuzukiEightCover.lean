module

public import CFSG.LocalAnalysis.ComponentInitial.SuzukiCoverBoundSylow

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace SuzukiEightCover

open CFSG.Blueprint CFSG.LieType.Ree SuzukiCoverBound EvenCoverPairing
open scoped commutatorElement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Field

variable {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ (2 * 1 + 1))

include hK in
theorem two_eq_zero : (2 : K) = 0 := (suzuki_frob_data 1 hK).1

omit [Finite K] in
include hK in
theorem units_pow_seven (m : Kˣ) : m ^ 7 = 1 := by
  have h : Nat.card Kˣ = 7 := by
    rw [Nat.card_units, hK]
    norm_num
  rw [← h]
  exact pow_card_eq_one'

omit [Finite K] in
include hK in
theorem exists_pow_five_mul_eq {w w' : K} (hw : w ≠ 0) (hw' : w' ≠ 0) :
    ∃ l : Kˣ, (l : K) ^ 5 * w = w' := by
  set m : Kˣ := Units.mk0 (w' / w) (div_ne_zero hw' hw)
  refine ⟨m ^ 3, ?_⟩
  have h : (m ^ 3) ^ 5 = m := by
    rw [← pow_mul, show 3 * 5 = 7 * 2 + 1 by norm_num, pow_add, pow_mul, units_pow_seven hK,
      one_pow, one_mul, pow_one]
  rw [← Units.val_pow_eq_pow_val, h, Units.val_mk0, div_mul_cancel₀ w' hw]

include hK in
theorem exists_ne_zero_one : ∃ c : K, c ≠ 0 ∧ c + 1 ≠ 0 := by
  obtain ⟨c, hc⟩ := exists_pow_theta_ne hK le_rfl
  refine ⟨c, fun h => hc (by rw [h]; norm_num), fun h => hc ?_⟩
  have h1 : c = 1 := by linear_combination h - two_eq_zero hK
  rw [h1]
  norm_num

include hK in
theorem comm_S (u v c d : K) :
    ⁅suzukiSElt 1 K u v, suzukiSElt 1 K c d⁆ = suzukiSElt 1 K 0 (u ^ 4 * c + c ^ 4 * u) := by
  have h := commutatorElement_suzukiSElt hK u v c d
  norm_num at h
  exact h

include hK in
theorem sq_S (u v : K) : suzukiSElt 1 K u v ^ 2 = suzukiSElt 1 K 0 (u ^ 5) := by
  have h := suzukiSElt_sq hK u v
  norm_num at h
  rw [pow_two]
  exact h

include hK in
theorem conj_D (l : Kˣ) (u v : K) :
    (suzukiDElt 1 K l)⁻¹ * suzukiSElt 1 K u v * ((suzukiDElt 1 K l)⁻¹)⁻¹ =
      suzukiSElt 1 K ((l : K) * u) ((l : K) ^ 5 * v) := by
  have h := suzukiDElt_inv_conj hK l u v
  norm_num at h
  exact h

include hK in
theorem S_zero_mul (v d : K) :
    suzukiSElt 1 K 0 v * suzukiSElt 1 K 0 d = suzukiSElt 1 K 0 (v + d) :=
  suzukiSElt_zero_mul hK v d

include hK in
theorem S_eq_one_iff {u v : K} : suzukiSElt 1 K u v = 1 ↔ u = 0 ∧ v = 0 := by
  rw [← suzukiSElt_zero_zero hK, suzukiSElt_inj]

include hK in
theorem mem_commutator_iff {g : suzukiGroup 1 K} :
    g ∈ ⁅suzukiU 1 K, suzukiU 1 K⁆ ↔ ∃ w : K, suzukiSElt 1 K 0 w = g :=
  mem_commutator_suzukiU_iff hK le_rfl

include hK in
theorem card_commutator :
    Nat.card (⁅suzukiU 1 K, suzukiU 1 K⁆ : Subgroup (suzukiGroup 1 K)) = 8 := by
  have hset : ((⁅suzukiU 1 K, suzukiU 1 K⁆ : Subgroup (suzukiGroup 1 K)) :
      Set (suzukiGroup 1 K)) = Set.range fun w : K => suzukiSElt 1 K 0 w := by
    ext g
    exact mem_commutator_iff hK
  rw [← SetLike.coe_sort_coe, hset,
    Nat.card_range_of_injective fun w w' h => (suzukiSElt_inj.mp h).2, hK]
  norm_num

include hK in
theorem card_U : Nat.card (suzukiU 1 K) = 64 := by
  rw [(suzuki_unipotent_structure hK).2.1]
  norm_num

include hK in
theorem card_addMonoidHom_le : Nat.card (K →+ ZMod 2) ≤ 8 := by
  have h2 : ∀ x : K, (2 : ℕ) • x = 0 := fun x => by
    rw [nsmul_eq_mul, Nat.cast_ofNat, two_eq_zero hK, zero_mul]
  let _ : Module (ZMod 2) K := AddCommGroup.zmodModule h2
  have : Module.Finite (ZMod 2) K := Module.Finite.of_finite
  have : Finite (Module.Dual (ZMod 2) K) := Module.finite_of_finite (ZMod 2)
  calc Nat.card (K →+ ZMod 2) ≤ Nat.card (Module.Dual (ZMod 2) K) :=
        Nat.card_le_card_of_injective _ (AddMonoidHom.toZModLinearMap_injective 2)
    _ = Nat.card K := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Subspace.dual_finrank_eq,
        ← Module.natCard_eq_pow_finrank]
    _ = 8 := hK

end Field

section Cover

variable {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ (2 * 1 + 1))
  {E : Type*} [Group E] [Finite E] [Group.IsPerfect E] {η : E →* suzukiGroup 1 K}
  (hη : Function.Surjective η) (hC : η.ker ≤ Subgroup.center E) (hC2 : Nat.card η.ker = 2)

include hK hη hC hC2 in
theorem cover_facts :
    η.ker ≤ ⁅(suzukiU 1 K).comap η, (suzukiU 1 K).comap η⁆ ∧
    CFSG.Assembly.IsElemAbelian 2 η.ker ∧
    IsMulCommutative ↥⁅(suzukiU 1 K).comap η, (suzukiU 1 K).comap η⁆ ∧
    ⁅(suzukiU 1 K).comap η, (suzukiU 1 K).comap η⁆.map η = ⁅suzukiU 1 K, suzukiU 1 K⁆ ∧
    ∃ β : K → K → E,
      (∀ r s : E, r ∈ ⁅(suzukiU 1 K).comap η, (suzukiU 1 K).comap η⁆ → ∀ w u v : K,
        η r = suzukiSElt 1 K 0 w → η s = suzukiSElt 1 K u v → ⁅r, s⁆ = β w u) ∧
      (∀ w : K, w ≠ 0 → ∃ u, β w u ≠ 1) ∧ (∀ u : K, u ≠ 0 → ∃ w, β w u ≠ 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ha : 1 ≤ 1 := le_rfl
  obtain ⟨hUp, hUidx⟩ := suzukiU_isPGroup_index hK
  obtain ⟨-, -, hTcard, hTnorm, -⟩ := suzuki_borel_structure hK
  have hTodd : Odd (Nat.card (suzukiT 1 K)) := by
    rw [hTcard]
    decide
  have h2 : IsPGroup 2 η.ker := IsPGroup.of_card (n := 1) (by rw [hC2, pow_one])
  have key := even_central_two_cover_class_three_kernel_pairing η hη hC h2 (hUp.toSylow hUidx)
    (nilpotencyClass_suzukiU_le hK) (isElemAbelian_commutator_suzukiU hK ha)
    (isElemAbelian_abelianization_suzukiU hK ha) (suzukiT 1 K) hTnorm hTodd
    (suzukiU_pairing_eq_zero hK ha)
  rw [IsPGroup.toSylow_coe] at key
  obtain ⟨hker3, hCe, hAcomm, hAmap, -, β, hβval, hβ₁, hβ₂, hspan, hβT, -⟩ := key
  have hkerA : η.ker ≤ ⁅(suzukiU 1 K).comap η, (suzukiU 1 K).comap η⁆ :=
    hker3.le.trans (Subgroup.commutator_mono (commutator_le_self _) le_rfl)
  refine ⟨hkerA, hCe, hAcomm, hAmap, ?_⟩
  have hW : ∀ w : K, suzukiSElt 1 K 0 w ∈ ⁅suzukiU 1 K, suzukiU 1 K⁆ :=
    suzukiSElt_zero_mem_commutator hK ha
  set β' : K → K → η.ker := fun w v => β ⟨suzukiSElt 1 K 0 w, hW w⟩
    (Abelianization.of (sU (a := 1) v)) with hβ'
  have hβ'₁ : ∀ w w' v, β' (w + w') v = β' w v * β' w' v := fun w w' v => by
    simp only [hβ']
    rw [← hβ₁]
    congr 1
    exact Subtype.ext (suzukiSElt_zero_mul hK w w').symm
  have hβ'₂ : ∀ w v v', β' w (v + v') = β' w v * β' w v' := fun w v v' => by
    simp only [hβ']
    rw [← hβ₂, of_sU_add hK ha]
  have hβ'T : ∀ (l : Kˣ) (w v : K), β' ((l : K) ^ 5 * w) ((l : K) * v) = β' w v := by
    intro l w v
    have ht : (suzukiDElt 1 K l)⁻¹ ∈ suzukiT 1 K := inv_mem (suzukiDElt_mem_suzukiT 1 K l)
    have e1 : (suzukiDElt 1 K l)⁻¹ * suzukiSElt 1 K 0 w * ((suzukiDElt 1 K l)⁻¹)⁻¹ =
        suzukiSElt 1 K 0 ((l : K) ^ 5 * w) := by
      rw [conj_D hK, mul_zero]
    have e2 : (suzukiDElt 1 K l)⁻¹ * suzukiSElt 1 K v 0 * ((suzukiDElt 1 K l)⁻¹)⁻¹ =
        suzukiSElt 1 K ((l : K) * v) 0 := by
      rw [conj_D hK, mul_zero]
    have h := hβT _ ht (suzukiSElt 1 K 0 w) (hW w) (by rw [e1]; exact hW _)
      (suzukiSElt 1 K v 0) (suzukiSElt_mem_suzukiU 1 K v 0)
      (by rw [e2]; exact suzukiSElt_mem_suzukiU 1 K _ 0)
    have h1 : (⟨(suzukiDElt 1 K l)⁻¹ * suzukiSElt 1 K 0 w * ((suzukiDElt 1 K l)⁻¹)⁻¹, by
        rw [e1]; exact hW _⟩ : ↥⁅suzukiU 1 K, suzukiU 1 K⁆) =
          ⟨suzukiSElt 1 K 0 ((l : K) ^ 5 * w), hW _⟩ := Subtype.ext e1
    have h2 : (⟨(suzukiDElt 1 K l)⁻¹ * suzukiSElt 1 K v 0 * ((suzukiDElt 1 K l)⁻¹)⁻¹, by
        rw [e2]; exact suzukiSElt_mem_suzukiU 1 K _ 0⟩ : suzukiU 1 K) =
          sU ((l : K) * v) := Subtype.ext e2
    rw [h1, h2] at h
    exact h
  have htriv : ¬ ∀ w v, β' w v = 1 := by
    intro hall
    have hle : η.ker ≤ ⊥ := by
      rw [← hspan, Subgroup.closure_le]
      rintro _ ⟨⟨p₁, p₂⟩, rfl⟩
      obtain ⟨w, hw⟩ := (mem_commutator_iff hK).mp p₁.2
      obtain ⟨v, hv⟩ := exists_of_eq_of_sU hK ha p₂
      have hp₁ : p₁ = ⟨suzukiSElt 1 K 0 w, hW w⟩ := Subtype.ext hw.symm
      rw [SetLike.mem_coe, Subgroup.mem_bot, ← hv, hp₁]
      exact congrArg Subtype.val (hall w v)
    rw [le_bot_iff.mp hle, Subgroup.card_bot] at hC2
    exact absurd hC2 (by norm_num)
  refine ⟨fun w v => β' w v, fun r s hr w u v hrw hsuv => ?_, fun w hw => ?_, fun u hu => ?_⟩
  ·
    have hs : η s ∈ suzukiU 1 K := by
      rw [hsuv]
      exact suzukiSElt_mem_suzukiU 1 K u v
    have hr' : η r ∈ ⁅suzukiU 1 K, suzukiU 1 K⁆ := by
      rw [hrw]
      exact hW w
    have h := hβval r hr s hs hr'
    have e1 : (⟨η r, hr'⟩ : ↥⁅suzukiU 1 K, suzukiU 1 K⁆) = ⟨suzukiSElt 1 K 0 w, hW w⟩ :=
      Subtype.ext hrw
    have e2 : Abelianization.of (⟨η s, hs⟩ : suzukiU 1 K) = Abelianization.of (sU (a := 1) u) := by
      refine ((abelianization_of_eq_iff _ _).mpr ?_).symm
      change (suzukiSElt 1 K u 0)⁻¹ * η s ∈ _
      rw [hsuv, suzukiSElt_eq_mul hK u v, inv_mul_cancel_left]
      exact hW v
    rw [e1, e2] at h
    exact h.symm
  ·
    by_contra hcon
    push Not at hcon
    apply htriv
    intro w' v'
    by_cases hw' : w' = 0
    · have h := hβ'₁ 0 0 v'
      rw [add_zero] at h
      rw [hw']
      exact mul_eq_left.mp h.symm
    · obtain ⟨l, hl⟩ := exists_pow_five_mul_eq hK hw hw'
      have h := hβ'T l w ((l : K)⁻¹ * v')
      rw [hl, ← mul_assoc, mul_inv_cancel₀ l.ne_zero, one_mul] at h
      rw [h]
      exact Subtype.ext (hcon _)
  ·
    by_contra hcon
    push Not at hcon
    apply htriv
    intro w' v'
    by_cases hv' : v' = 0
    · have h := hβ'₂ w' 0 0
      rw [add_zero] at h
      rw [hv']
      exact mul_eq_left.mp h.symm
    · set l : Kˣ := Units.mk0 (v' / u) (div_ne_zero hv' hu)
      have hlu : (l : K) * u = v' := by
        rw [Units.val_mk0, div_mul_cancel₀ v' hu]
      have h := hβ'T l ((l : K)⁻¹ ^ 5 * w') u
      rw [hlu, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ l.ne_zero, one_pow, one_mul] at h
      rw [h]
      exact Subtype.ext (hcon _)

include hK in
omit [Finite E] [Group.IsPerfect E] in
theorem mem_P_iff {x : E} :
    x ∈ (suzukiU 1 K).comap η ↔ ∃ u v : K, η x = suzukiSElt 1 K u v := by
  rw [Subgroup.mem_comap, mem_suzukiU_iff hK]
  exact ⟨fun ⟨u, v, h⟩ => ⟨u, v, h.symm⟩, fun ⟨u, v, h⟩ => ⟨u, v, h.symm⟩⟩

omit [Finite K] [Finite E] [Group.IsPerfect E] in
theorem ker_le_P : η.ker ≤ (suzukiU 1 K).comap η := fun x hx => by
  rw [Subgroup.mem_comap, (MonoidHom.mem_ker).mp hx]
  exact one_mem _

include hK hη hC hC2 in
theorem mem_A_iff {r : E} :
    r ∈ ⁅(suzukiU 1 K).comap η, (suzukiU 1 K).comap η⁆ ↔
      ∃ w : K, η r = suzukiSElt 1 K 0 w := by
  obtain ⟨hkerA, -, -, hAmap, -⟩ := cover_facts hK hη hC hC2
  constructor
  · intro hr
    have h : η r ∈ ⁅suzukiU 1 K, suzukiU 1 K⁆ := by
      rw [← hAmap]
      exact Subgroup.mem_map_of_mem η hr
    obtain ⟨w, hw⟩ := (mem_commutator_iff hK).mp h
    exact ⟨w, hw.symm⟩
  · rintro ⟨w, hw⟩
    have h : η r ∈ (⁅(suzukiU 1 K).comap η, (suzukiU 1 K).comap η⁆).map η := by
      rw [hAmap, hw]
      exact (mem_commutator_iff hK).mpr ⟨w, rfl⟩
    obtain ⟨r', hr', hrr'⟩ := h
    have hk : r'⁻¹ * r ∈ η.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hrr', inv_mul_cancel]
    have h' := mul_mem hr' (hkerA hk)
    rwa [mul_inv_cancel_left] at h'

include hK hη hC hC2 in
theorem sq_eq_one_of_mem {r : E} (hr : r ∈ ⁅(suzukiU 1 K).comap η, (suzukiU 1 K).comap η⁆) :
    r ^ 2 = 1 := by
  obtain ⟨-, hCe, hAcomm, -, -⟩ := cover_facts hK hη hC hC2
  have h2 := two_eq_zero hK
  have hsqker : ∀ (r : E) (w : K), η r = suzukiSElt 1 K 0 w → r ^ 2 ∈ η.ker := fun r w hrw => by
    rw [MonoidHom.mem_ker, map_pow, hrw, sq_S hK, S_eq_one_iff hK]
    norm_num
  obtain ⟨r₁, hr₁⟩ := hη (suzukiSElt 1 K 0 1)
  have hconst : ∀ (r : E) (w : K), w ≠ 0 → η r = suzukiSElt 1 K 0 w → r ^ 2 = r₁ ^ 2 := by
    intro r w hw hrw
    obtain ⟨l, hl⟩ := exists_pow_five_mul_eq hK one_ne_zero hw
    obtain ⟨t, ht⟩ := hη (suzukiDElt 1 K l)⁻¹
    have hc : (t * r₁ * t⁻¹)⁻¹ * r ∈ η.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, map_inv, ht, hr₁, hrw, conj_D hK,
        mul_zero, hl, inv_mul_cancel]
    have hr : r = t * r₁ * t⁻¹ * ((t * r₁ * t⁻¹)⁻¹ * r) := by rw [mul_inv_cancel_left]
    have hcom : Commute (t * r₁ * t⁻¹) ((t * r₁ * t⁻¹)⁻¹ * r) :=
      Subgroup.mem_center_iff.mp (hC hc) _
    rw [hr, hcom.mul_pow, conj_pow, hCe.2 _ hc,
      mul_one, conj_eq_self_of_mem_center t (hC (hsqker r₁ 1 hr₁))]
  obtain ⟨w, hw⟩ := (mem_A_iff hK hη hC hC2).mp hr
  by_cases hw0 : w = 0
  · refine hCe.2 r ?_
    rw [MonoidHom.mem_ker, hw, hw0, suzukiSElt_zero_zero hK]
  obtain ⟨c, hc0, hc1⟩ := exists_ne_zero_one hK
  obtain ⟨r₀, hr₀⟩ := hη (suzukiSElt 1 K 0 c)
  obtain ⟨r₂, hr₂⟩ := hη (suzukiSElt 1 K 0 (c + 1))
  have hA₀ := (mem_A_iff hK hη hC hC2).mpr ⟨c, hr₀⟩
  have hA₂ := (mem_A_iff hK hη hC hC2).mpr ⟨c + 1, hr₂⟩
  have hcomm : Commute r₀ r₂ := congrArg Subtype.val (hAcomm.is_comm.comm ⟨r₀, hA₀⟩ ⟨r₂, hA₂⟩)
  have h12 : η (r₀ * r₂) = suzukiSElt 1 K 0 1 := by
    rw [map_mul, hr₀, hr₂, S_zero_mul hK]
    congr 1
    linear_combination c * h2
  have e1 := hconst (r₀ * r₂) 1 one_ne_zero h12
  rw [hcomm.mul_pow, hconst r₀ c hc0 hr₀, hconst r₂ (c + 1) hc1 hr₂] at e1
  rw [hconst r w hw0 hw, mul_eq_left.mp e1]

include hK hη hC hC2 in
theorem sq_mem_A {x : E} (hx : x ∈ (suzukiU 1 K).comap η) :
    x ^ 2 ∈ ⁅(suzukiU 1 K).comap η, (suzukiU 1 K).comap η⁆ ∧
      (x ^ 2 ∈ η.ker ↔ x ∈ ⁅(suzukiU 1 K).comap η, (suzukiU 1 K).comap η⁆) := by
  obtain ⟨u, v, huv⟩ := (mem_P_iff hK).mp hx
  have hsq : η (x ^ 2) = suzukiSElt 1 K 0 (u ^ 5) := by rw [map_pow, huv, sq_S hK]
  refine ⟨(mem_A_iff hK hη hC hC2).mpr ⟨_, hsq⟩, fun h => ?_, fun h => ?_⟩
  · rw [MonoidHom.mem_ker, hsq, S_eq_one_iff hK] at h
    have hu : u = 0 := (pow_eq_zero_iff (by norm_num)).mp h.2
    exact (mem_A_iff hK hη hC hC2).mpr ⟨v, by rw [huv, hu]⟩
  · rw [sq_eq_one_of_mem hK hη hC hC2 h]
    exact one_mem _

include hK hη hC hC2 in
theorem pow_four_eq_one {x : E} (hx : x ∈ (suzukiU 1 K).comap η) : x ^ 4 = 1 := by
  rw [show 4 = 2 * 2 from rfl, pow_mul]
  exact sq_eq_one_of_mem hK hη hC hC2 (sq_mem_A hK hη hC hC2 hx).1

include hK hη hC hC2 in
theorem mem_A_of_commute {x : E} (hx : x ∈ (suzukiU 1 K).comap η)
    (hcomm : ∀ a ∈ ⁅(suzukiU 1 K).comap η, (suzukiU 1 K).comap η⁆, a * x = x * a) :
    x ∈ ⁅(suzukiU 1 K).comap η, (suzukiU 1 K).comap η⁆ := by
  obtain ⟨-, -, -, -, β, hval, -, hright⟩ := cover_facts hK hη hC hC2
  obtain ⟨u, v, huv⟩ := (mem_P_iff hK).mp hx
  by_cases hu : u = 0
  · exact (mem_A_iff hK hη hC hC2).mpr ⟨v, by rw [huv, hu]⟩
  obtain ⟨w, hw⟩ := hright u hu
  obtain ⟨r, hr⟩ := hη (suzukiSElt 1 K 0 w)
  have hrA := (mem_A_iff hK hη hC hC2).mpr ⟨w, hr⟩
  have h := hval r x hrA w u v hr huv
  rw [commutatorElement_eq_one_iff_mul_comm.mpr (hcomm r hrA)] at h
  exact absurd h.symm hw

include hK hη hC hC2 in
theorem center_eq :
    (Subgroup.center ((suzukiU 1 K).comap η)).map ((suzukiU 1 K).comap η).subtype = η.ker := by
  obtain ⟨-, -, -, -, β, hval, hleft, -⟩ := cover_facts hK hη hC hC2
  have h2 := two_eq_zero hK
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_center_iff] at hx
    show (x : E) ∈ η.ker
    have hcx : ∀ s ∈ (suzukiU 1 K).comap η, s * (x : E) = x * s := fun s hs =>
      congrArg Subtype.val (hx ⟨s, hs⟩)
    obtain ⟨u, v, huv⟩ := (mem_P_iff hK).mp x.2
    have hu : u = 0 := by
      by_contra hu
      obtain ⟨c₀, hc₀⟩ := exists_pow_theta_ne hK le_rfl
      obtain ⟨s, hs⟩ := hη (suzukiSElt 1 K (u * c₀) 0)
      have h := congrArg η (hcx s ((mem_P_iff hK).mpr ⟨_, _, hs⟩))
      rw [map_mul, map_mul, hs, huv] at h
      have h' := comm_S hK u v (u * c₀) 0
      rw [commutatorElement_eq_one_iff_mul_comm.mpr h.symm] at h'
      have h0 := ((S_eq_one_iff hK).mp h'.symm).2
      rw [show u ^ 4 * (u * c₀) + (u * c₀) ^ 4 * u = u ^ 5 * (c₀ + c₀ ^ 4) by ring] at h0
      rcases mul_eq_zero.mp h0 with h5 | h5
      · exact hu ((pow_eq_zero_iff (by norm_num)).mp h5)
      · apply hc₀
        norm_num
        linear_combination h5 - c₀ * h2
    have hxA := (mem_A_iff hK hη hC hC2).mpr ⟨v, by rw [huv, hu]⟩
    by_cases hv : v = 0
    · rw [MonoidHom.mem_ker, huv, hu, hv, suzukiSElt_zero_zero hK]
    obtain ⟨u', hu'⟩ := hleft v hv
    obtain ⟨s, hs⟩ := hη (suzukiSElt 1 K u' 0)
    have h := hval x s hxA v u' 0 (by rw [huv, hu]) hs
    rw [commutatorElement_eq_one_iff_mul_comm.mpr (hcx s ((mem_P_iff hK).mpr ⟨_, _, hs⟩)).symm] at h
    exact absurd h.symm hu'
  · intro c hc
    refine ⟨⟨c, ker_le_P hc⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext ((Subgroup.mem_center_iff.mp (hC hc)) g)

omit [Finite E] [Group.IsPerfect E] in
theorem card_eq_card_map_mul {J : Type*} [Group J] (f : E →* J) (H : Subgroup E)
    (hH : f.ker ≤ H) : Nat.card H = Nat.card (H.map f) * Nat.card f.ker := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (f.domRestrict H).ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange (f.domRestrict H)).toEquiv,
    MonoidHom.domRestrict_range, MonoidHom.ker_domRestrict,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH).toEquiv]

include hK hη hC hC2 in
theorem card_A :
    Nat.card (⁅(suzukiU 1 K).comap η, (suzukiU 1 K).comap η⁆ : Subgroup E) = 16 := by
  obtain ⟨hkerA, -, -, hAmap, -⟩ := cover_facts hK hη hC hC2
  rw [card_eq_card_map_mul η _ hkerA, hAmap, card_commutator hK, hC2]

include hK hη hC2 in
omit [Finite E] [Group.IsPerfect E] in
theorem card_P : Nat.card ((suzukiU 1 K).comap η) = 128 := by
  rw [card_eq_card_map_mul η _ ker_le_P, Subgroup.map_comap_eq_self_of_surjective hη, card_U hK,
    hC2]

include hK hη hC hC2 in
theorem card_quotient :
    Nat.card ((suzukiU 1 K).comap η ⧸
      (⁅(suzukiU 1 K).comap η, (suzukiU 1 K).comap η⁆).subgroupOf ((suzukiU 1 K).comap η)) =
        8 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((⁅(suzukiU 1 K).comap η, (suzukiU 1 K).comap η⁆).subgroupOf ((suzukiU 1 K).comap η))
  rw [card_P hK hη hC2,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (commutator_le_self _)).toEquiv,
    card_A hK hη hC hC2] at h
  omega

end Cover

section Shear

variable {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ (2 * 1 + 1))
  {E : Type*} [Group E] [Finite E] [Group.IsPerfect E] {η : E →* suzukiGroup 1 K}
  (hη : Function.Surjective η) (hC : η.ker ≤ Subgroup.center E) (hC2 : Nat.card η.ker = 2)
  {z : E} (hz : Subgroup.zpowers z = η.ker)

include hz hC2 in
omit [Finite E] [Group.IsPerfect E] [Finite K] in
theorem z_ne_one : z ≠ 1 := by
  rintro rfl
  rw [Subgroup.zpowers_one_eq_bot] at hz
  rw [← hz, Subgroup.card_bot] at hC2
  exact absurd hC2 (by norm_num)

include hK hη hC hC2 hz in
theorem mem_ker_iff {c : E} : c ∈ η.ker ↔ c = 1 ∨ c = z := by
  obtain ⟨-, hCe, -⟩ := cover_facts hK hη hC hC2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzk : z ∈ η.ker := hz ▸ Subgroup.mem_zpowers z
  constructor
  · intro hc
    rw [← hz] at hc
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    rw [← zpow_mod_orderOf, orderOf_eq_prime (hCe.2 z hzk) (z_ne_one hC2 hz), Nat.cast_ofNat]
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left
      rw [h, zpow_zero]
    · right
      rw [h, zpow_one]
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact hzk

include hK hη hC hC2 hz in
theorem conj_range :
    Set.range (fun (p : (suzukiU 1 K).comap η)
        (a : ↥⁅(suzukiU 1 K).comap η, (suzukiU 1 K).comap η⁆) => (p : E) * a * (p : E)⁻¹) =
      {f | ∃ ℓ : Additive ↥⁅(suzukiU 1 K).comap η, (suzukiU 1 K).comap η⁆ →+ ZMod 2,
        (∀ a : ↥⁅(suzukiU 1 K).comap η, (suzukiU 1 K).comap η⁆,
          (a : E) = z → ℓ (Additive.ofMul a) = 0) ∧
        f = fun a : ↥⁅(suzukiU 1 K).comap η, (suzukiU 1 K).comap η⁆ =>
          (a : E) * z ^ (ℓ (Additive.ofMul a)).val} ∧
    Nat.card (Set.range (fun (p : (suzukiU 1 K).comap η)
        (a : ↥⁅(suzukiU 1 K).comap η, (suzukiU 1 K).comap η⁆) => (p : E) * a * (p : E)⁻¹)) =
      8 := by
  classical
  obtain ⟨hkerA, hCe, hAcomm, -, -⟩ := cover_facts hK hη hC hC2
  have hzk : z ∈ η.ker := hz ▸ Subgroup.mem_zpowers z
  have hz1 := z_ne_one hC2 hz
  set P₀ := (suzukiU 1 K).comap η with hP₀
  set A₀ := ⁅P₀, P₀⁆ with hA₀
  set Φ := fun (p : P₀) (a : A₀) => (p : E) * a * (p : E)⁻¹ with hΦ
  set S := {f : A₀ → E | ∃ ℓ : Additive A₀ →+ ZMod 2,
    (∀ a : A₀, (a : E) = z → ℓ (Additive.ofMul a) = 0) ∧
      f = fun a : A₀ => (a : E) * z ^ (ℓ (Additive.ofMul a)).val} with hS
  have hcommC : ∀ p ∈ P₀, ∀ a ∈ A₀, ⁅p, a⁆ ∈ η.ker := by
    intro p hp a ha
    obtain ⟨u, v, huv⟩ := (mem_P_iff hK).mp hp
    obtain ⟨w, hw⟩ := (mem_A_iff hK hη hC hC2).mp ha
    rw [MonoidHom.mem_ker, map_commutatorElement, huv, hw, comm_S hK, S_eq_one_iff hK]
    simp
  set lg : E → ZMod 2 := fun c => if c = 1 then 0 else 1 with hlg
  have hzz : z * z = 1 := by
    rw [← pow_two]
    exact hCe.2 z hzk
  have e1 : lg 1 = 0 := by simp [hlg]
  have e2 : lg z = 1 := by simp [hlg, hz1]
  have hlg_pow : ∀ c ∈ η.ker, c = z ^ (lg c).val := by
    intro c hc
    rcases (mem_ker_iff hK hη hC hC2 hz).mp hc with h | h <;> rw [h]
    · rw [e1, ZMod.val_zero, pow_zero]
    · rw [e2, show ZMod.val (1 : ZMod 2) = 1 from rfl, pow_one]
  have hlg_mul : ∀ c ∈ η.ker, ∀ d ∈ η.ker, lg (c * d) = lg c + lg d := by
    intro c hc d hd
    rcases (mem_ker_iff hK hη hC hC2 hz).mp hc with h | h <;>
      rcases (mem_ker_iff hK hη hC hC2 hz).mp hd with h' | h' <;> rw [h, h']
    · rw [one_mul, e1, add_zero]
    · rw [one_mul, e1, zero_add]
    · rw [mul_one, e1, add_zero]
    · rw [hzz, e1, e2]
      decide
  have hsub : Set.range Φ ⊆ S := by
    rintro _ ⟨p, rfl⟩
    have hc : ∀ a : A₀, ⁅(p : E), (a : E)⁆ ∈ η.ker := fun a => hcommC p p.2 a a.2
    refine ⟨AddMonoidHom.mk' (fun a => lg ⁅(p : E), ((Additive.toMul a : A₀) : E)⁆)
      fun a b => ?_, fun a ha => ?_, ?_⟩
    · rw [toMul_add, Subgroup.coe_mul, commutatorElement_mul_right_eq,
        conj_eq_self_of_mem_center _ (hC (hc _)), hlg_mul _ (hc _) _ (hc _)]
    · rw [AddMonoidHom.mk'_apply, toMul_ofMul, ha,
        commutatorElement_eq_one_of_mem_center_right _ (hC hzk)]
      simp [hlg]
    · funext a
      rw [AddMonoidHom.mk'_apply, toMul_ofMul, ← hlg_pow _ (hc a)]
      change (p : E) * a * (p : E)⁻¹ = _
      rw [EvenCoverPairing.conj_eq_commutatorElement_mul]
      exact (Subgroup.mem_center_iff.mp (hC (hc a)) a).symm
  have hcard : Nat.card (Set.range Φ) = 8 := by
    rw [← Nat.card_congr (Setoid.quotientKerEquivRange Φ)]
    have hs : Setoid.ker Φ = QuotientGroup.leftRel (A₀.subgroupOf P₀) := by
      refine Setoid.ext fun p q => ?_
      rw [Setoid.ker_def, QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf]
      constructor
      · intro h
        refine mem_A_of_commute hK hη hC hC2 (p⁻¹ * q).2 fun a ha => ?_
        have h' := congrFun h ⟨a, ha⟩
        simp only [hΦ] at h'
        rw [Subgroup.coe_mul, InvMemClass.coe_inv]
        calc a * ((p : E)⁻¹ * q) = (p : E)⁻¹ * (p * a * (p : E)⁻¹) * q := by group
          _ = (p : E)⁻¹ * (q * a * (q : E)⁻¹) * q := by rw [h']
          _ = (p : E)⁻¹ * q * a := by group
      · intro h
        funext a
        have hcomm : ((p⁻¹ * q : P₀) : E) * a = a * ((p⁻¹ * q : P₀) : E) :=
          congrArg Subtype.val (hAcomm.is_comm.comm ⟨_, h⟩ a)
        rw [Subgroup.coe_mul, InvMemClass.coe_inv] at hcomm
        simp only [hΦ]
        symm
        calc (q : E) * a * (q : E)⁻¹ = p * ((p : E)⁻¹ * q * a) * (q : E)⁻¹ := by group
          _ = p * (a * ((p : E)⁻¹ * q)) * (q : E)⁻¹ := by rw [hcomm]
          _ = p * a * (p : E)⁻¹ := by group
    rw [hs]
    exact card_quotient hK hη hC hC2
  have hbound : S.ncard ≤ 8 := by
    set L := {ℓ : Additive A₀ →+ ZMod 2 // ∀ a : A₀, (a : E) = z → ℓ (Additive.ofMul a) = 0}
    have hSL : S = Set.range fun ℓ : L => fun a : A₀ =>
        (a : E) * z ^ (ℓ.1 (Additive.ofMul a)).val := by
      ext f
      constructor
      · rintro ⟨ℓ, hℓ, rfl⟩
        exact ⟨⟨ℓ, hℓ⟩, rfl⟩
      · rintro ⟨⟨ℓ, hℓ⟩, rfl⟩
        exact ⟨ℓ, hℓ, rfl⟩
    have : Finite (Additive A₀ →+ ZMod 2) := FunLike.finite _
    have : Finite (K →+ ZMod 2) := FunLike.finite _
    choose r hr using fun w : K => hη (suzukiSElt 1 K 0 w)
    have hrA : ∀ w, r w ∈ A₀ := fun w => (mem_A_iff hK hη hC hC2).mpr ⟨w, hr w⟩
    have hℓC : ∀ (ℓ : L) (c : E) (hcA : c ∈ A₀), c ∈ η.ker →
        ℓ.1 (Additive.ofMul ⟨c, hcA⟩) = 0 := by
      intro ℓ c hcA hc
      rcases (mem_ker_iff hK hη hC hC2 hz).mp hc with h | h
      · have h1 : (⟨c, hcA⟩ : A₀) = 1 := Subtype.ext h
        rw [h1, ofMul_one, map_zero]
      · exact ℓ.2 _ h
    let ρ : L → (K →+ ZMod 2) := fun ℓ =>
      AddMonoidHom.mk' (fun w => ℓ.1 (Additive.ofMul ⟨r w, hrA w⟩)) fun w w' => by
        have hc : (r w * r w')⁻¹ * r (w + w') ∈ η.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, hr, hr, hr, S_zero_mul hK,
            inv_mul_cancel]
        have e : (⟨r (w + w'), hrA _⟩ : A₀) =
            ⟨r w, hrA w⟩ * ⟨r w', hrA w'⟩ * ⟨_, hkerA hc⟩ :=
          Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, mul_inv_cancel_left])
        rw [e, ofMul_mul, ofMul_mul, map_add, map_add, hℓC ℓ _ (hkerA hc) hc, add_zero]
    have hρ : Function.Injective ρ := by
      intro ℓ₁ ℓ₂ h
      apply Subtype.ext
      refine AddMonoidHom.ext fun x => ?_
      obtain ⟨w, hw⟩ := (mem_A_iff hK hη hC hC2).mp (Additive.toMul x).2
      have hc : (r w)⁻¹ * ((Additive.toMul x : A₀) : E) ∈ η.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hr, hw, inv_mul_cancel]
      have e : Additive.toMul x = ⟨r w, hrA w⟩ * ⟨_, hkerA hc⟩ :=
        Subtype.ext (by rw [Subgroup.coe_mul, mul_inv_cancel_left])
      have h1 := DFunLike.congr_fun h w
      simp only [ρ, AddMonoidHom.mk'_apply] at h1
      rw [← ofMul_toMul x, e, ofMul_mul, map_add, map_add, hℓC ℓ₁ _ (hkerA hc) hc,
        hℓC ℓ₂ _ (hkerA hc) hc, h1]
    rw [← Nat.card_coe_set_eq, hSL]
    calc Nat.card (Set.range fun ℓ : L => fun a : A₀ =>
          (a : E) * z ^ (ℓ.1 (Additive.ofMul a)).val) ≤ Nat.card L := Finite.card_range_le _
      _ ≤ Nat.card (K →+ ZMod 2) := Nat.card_le_card_of_injective ρ hρ
      _ ≤ 8 := card_addMonoidHom_le hK
  refine ⟨Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _), hcard⟩
  rw [← Nat.card_coe_set_eq (Set.range Φ), hcard]
  exact hbound

include hK hη hC hC2 hz in
theorem main_comap {P : Subgroup E} (hP : P = (suzukiU 1 K).comap η) :
    CFSG.IsElementaryAbelian 2 ↥⁅P, P⁆ ∧ Nat.card ↥⁅P, P⁆ = 16 ∧
    (Subgroup.center P).map P.subtype = η.ker ∧ (∀ x ∈ P, orderOf x ∣ 4) ∧
    Subgroup.closure {x : E | x ∈ P ∧ orderOf x = 2} = ⁅P, P⁆ ∧
    (∀ x ∈ P, x ^ 2 ∈ η.ker ↔ x ∈ ⁅P, P⁆) ∧
    Set.range (fun (p : P) (a : ↥⁅P, P⁆) => (p : E) * a * (p : E)⁻¹) =
      {f | ∃ ℓ : Additive ↥⁅P, P⁆ →+ ZMod 2,
        (∀ a : ↥⁅P, P⁆, (a : E) = z → ℓ (Additive.ofMul a) = 0) ∧
        f = fun a : ↥⁅P, P⁆ => (a : E) * z ^ (ℓ (Additive.ofMul a)).val} ∧
    Nat.card (Set.range (fun (p : P) (a : ↥⁅P, P⁆) => (p : E) * a * (p : E)⁻¹)) = 8 := by
  subst hP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hAcomm, -, -⟩ := cover_facts hK hη hC hC2
  obtain ⟨hrange, hcard⟩ := conj_range hK hη hC hC2 hz
  refine ⟨{ is_comm := hAcomm.is_comm
            exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
              Subtype.ext ?_ }, card_A hK hη hC hC2, center_eq hK hη hC hC2,
    fun x hx => orderOf_dvd_of_pow_eq_one (pow_four_eq_one hK hη hC hC2 hx), ?_,
    fun x hx => (sq_mem_A hK hη hC hC2 hx).2, hrange, hcard⟩
  · rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact sq_eq_one_of_mem hK hη hC hC2 x.2
  · apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro x ⟨hxP, hx2⟩
      refine (sq_mem_A hK hη hC hC2 hxP).2.mp ?_
      rw [← hx2, pow_orderOf_eq_one]
      exact one_mem _
    · intro a ha
      by_cases h1 : a = 1
      · rw [h1]
        exact one_mem _
      · exact Subgroup.subset_closure ⟨commutator_le_self _ ha,
          orderOf_eq_prime (sq_eq_one_of_mem hK hη hC hC2 ha) h1⟩

end Shear

end SuzukiEightCover

open CFSG.Blueprint CFSG.LieType.Ree SuzukiEightCover in
theorem even_Suzuki_eight_double_cover_Sylow_involutions {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 8) {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (η : E →* suzukiGroup 1 K) (hη : Function.Surjective η) (hC : η.ker ≤ Subgroup.center E)
    (hC2 : Nat.card η.ker = 2) (z : E) (hz : Subgroup.zpowers z = η.ker) (P : Sylow 2 E) :
    CFSG.IsElementaryAbelian 2 ↥⁅(P : Subgroup E), (P : Subgroup E)⁆ ∧
    Nat.card ↥⁅(P : Subgroup E), (P : Subgroup E)⁆ = 16 ∧
    (Subgroup.center (P : Subgroup E)).map (P : Subgroup E).subtype = η.ker ∧
    (∀ x ∈ (P : Subgroup E), orderOf x ∣ 4) ∧
    Subgroup.closure {x : E | x ∈ (P : Subgroup E) ∧ orderOf x = 2} =
      ⁅(P : Subgroup E), (P : Subgroup E)⁆ ∧
    (∀ x ∈ (P : Subgroup E), x ^ 2 ∈ η.ker ↔ x ∈ ⁅(P : Subgroup E), (P : Subgroup E)⁆) ∧
    Set.range (fun (p : (P : Subgroup E)) (a : ↥⁅(P : Subgroup E), (P : Subgroup E)⁆) =>
        (p : E) * a * (p : E)⁻¹) =
      {f | ∃ ℓ : Additive ↥⁅(P : Subgroup E), (P : Subgroup E)⁆ →+ ZMod 2,
        (∀ a : ↥⁅(P : Subgroup E), (P : Subgroup E)⁆, (a : E) = z → ℓ (Additive.ofMul a) = 0) ∧
        f = fun a : ↥⁅(P : Subgroup E), (P : Subgroup E)⁆ =>
          (a : E) * z ^ (ℓ (Additive.ofMul a)).val} ∧
    Nat.card (Set.range (fun (p : (P : Subgroup E))
        (a : ↥⁅(P : Subgroup E), (P : Subgroup E)⁆) => (p : E) * a * (p : E)⁻¹)) = 8 := by
  have hK' : Nat.card K = 2 ^ (2 * 1 + 1) := hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hUp, hUidx⟩ := suzukiU_isPGroup_index hK'
  have h2 : IsPGroup 2 η.ker := IsPGroup.of_card (n := 1) (by rw [hC2, pow_one])
  have hrange : ((hUp.toSylow hUidx : Sylow 2 (suzukiGroup 1 K)) :
      Subgroup (suzukiGroup 1 K)) ≤ η.range := by
    rw [MonoidHom.range_eq_top.mpr hη]
    exact le_top
  obtain ⟨g, hg⟩ :=
    MulAction.exists_smul_eq E ((hUp.toSylow hUidx).comapOfKerIsPGroup η h2 hrange) P
  set η' : E →* suzukiGroup 1 K := η.comp (MulAut.conj g⁻¹).toMonoidHom with hη'
  have hker' : η'.ker = η.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    change η ((MulAut.conj g⁻¹) x) = 1 ↔ η x = 1
    rw [MulAut.conj_apply, inv_inv, map_mul, map_mul, map_inv]
    simpa only [inv_inv] using conj_eq_one_iff (a := (η g)⁻¹) (b := η x)
  have hsurj : Function.Surjective η' := fun y => by
    obtain ⟨x, hx⟩ := hη y
    refine ⟨g * x * g⁻¹, ?_⟩
    change η ((MulAut.conj g⁻¹) (g * x * g⁻¹)) = y
    rw [MulAut.conj_apply, show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group, hx]
  have hP : (P : Subgroup E) = (suzukiU 1 K).comap η' := by
    ext x
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      Sylow.coe_comapOfKerIsPGroup, IsPGroup.toSylow_coe, Subgroup.mem_comap, Subgroup.mem_comap,
      MulAut.smul_def, ← map_inv]
    rfl
  have key := main_comap hK' hsurj (by rw [hker']; exact hC) (by rw [hker']; exact hC2)
    (hz.trans hker'.symm) hP
  rw [hker'] at key
  exact key

end CFSG.LocalAnalysis.ComponentInitial
