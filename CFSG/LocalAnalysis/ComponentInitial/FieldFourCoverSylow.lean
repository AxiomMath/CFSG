module

public import CFSG.LocalAnalysis.ComponentInitial.FieldFourCoverNormalizers
public import CFSG.LocalAnalysis.ComponentInitial.FieldFourCoverSylowMatrices
public import CFSG.LocalAnalysis.ComponentInitial.FieldFourCoverSylowGroup
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.Core
public import CFSG.Walter.ReeOrder.JT.Defs
public import Mathlib.GroupTheory.IsPerfect

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.FieldFourCover

open Subgroup LinearFlag CFSG.LieType.Chevalley
open scoped IsMulCommutative Pointwise commutatorElement

section Setup

variable {k : Type} [Field k] {X : Type} [Group X] {π : X →* projectiveSL 3 k}

theorem comap_projRad_sq_eq_one [Finite k] (hk : Nat.card k = 4) (hπ : Function.Surjective π)
    (hCZ : π.ker ≤ center X) (hC : CFSG.IsElementaryAbelian 2 π.ker) (j : Fin 2) :
    ∀ x ∈ (projRad k j).comap π, x ^ 2 = 1 :=
  sq_eq_one_of_comap hπ hCZ
    (fun c hc => CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := π.ker) c hc)
    (fun _ hr => sq_eq_one_of_mem_projRad hk j hr)
    (fun _ hr _ hs => commute_of_mem_projRad j hr hs)
    (fun _ hr _ hs hr1 hs1 => projRad_transitive j hr hs hr1 hs1)
    (exists_independent_projRad hk j)

theorem comap_projUnip_sq_mem [Finite k] (hk : Nat.card k = 4) {x : X}
    (hx : x ∈ (projUnip k).comap π) :
    x ^ 2 ∈ (projCenterW k).comap π := by
  rw [Subgroup.mem_comap, map_pow]
  exact sq_mem_projCenterW hk hx

theorem comap_projUnip_commutator_mem {x y : X} (hx : x ∈ (projUnip k).comap π)
    (hy : y ∈ (projUnip k).comap π) : ⁅x, y⁆ ∈ (projCenterW k).comap π := by
  rw [Subgroup.mem_comap, map_commutatorElement]
  exact proj_commutatorElement_mem _ _ hx hy

theorem mem_smul_sylow_iff {p : ℕ} {g w : X} {S : Sylow p X} :
    w ∈ ((g • S : Sylow p X) : Subgroup X) ↔ g⁻¹ * w * g ∈ (S : Subgroup X) := by
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
    ← map_inv, MulAut.conj_apply, inv_inv]

variable [Finite k] [Finite X] (hk : Nat.card k = 4) (hπ : Function.Surjective π)
  (hCZ : π.ker ≤ center X) (hC : CFSG.IsElementaryAbelian 2 π.ker)
include hk hπ hCZ hC

theorem comap_projCenterW_commute {z : X} (hz : z ∈ (projCenterW k).comap π) {t : X}
    (ht : t ∈ (projUnip k).comap π) : z * t = t * z := by
  have hprev := field_four_central_two_cover_parabolic_normalizers hk π hπ hCZ hC
  obtain ⟨-, -, -, -, -, hcenter, -⟩ := hprev
  rw [← hcenter] at hz
  obtain ⟨z', hz', rfl⟩ := hz
  exact (congrArg Subtype.val (mem_center_iff.1 hz' ⟨t, ht⟩)).symm

omit [Finite X] in
theorem sq_eq_one_iff_mem_comap_projRad {x : X} (hx : x ∈ (projUnip k).comap π) :
    x ^ 2 = 1 ↔ x ∈ (projRad k 0).comap π ∨ x ∈ (projRad k 1).comap π := by
  constructor
  · intro h2
    have h := mem_projRad_of_sq_eq_one hk hx (by rw [← map_pow, h2, map_one])
    exact h
  · rintro (h | h)
    · exact comap_projRad_sq_eq_one hk hπ hCZ hC 0 x h
    · exact comap_projRad_sq_eq_one hk hπ hCZ hC 1 x h

omit [Finite X] in
theorem le_or_le_of_isElementaryAbelian {E : Subgroup X} (hET : E ≤ (projUnip k).comap π)
    (hE : CFSG.IsElementaryAbelian 2 E) :
    E ≤ (projRad k 0).comap π ∨ E ≤ (projRad k 1).comap π := by
  have hE2 : ∀ x ∈ E, x ∈ (projRad k 0).comap π ∨ x ∈ (projRad k 1).comap π := fun x hx =>
    (sq_eq_one_iff_mem_comap_projRad hk hπ hCZ hC (hET hx)).1
      (CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := E) x hx)
  by_contra h
  rw [not_or] at h
  obtain ⟨h0, h1⟩ := h
  obtain ⟨x, hxE, hx0⟩ := Set.not_subset.1 h0
  obtain ⟨y, hyE, hy1⟩ := Set.not_subset.1 h1
  have hx1 : x ∈ (projRad k 1).comap π := (hE2 x hxE).resolve_left hx0
  have hy0 : y ∈ (projRad k 0).comap π := (hE2 y hyE).resolve_right hy1
  rcases hE2 (x * y) (mul_mem hxE hyE) with h | h
  · exact hx0 (by simpa using mul_mem h (inv_mem hy0))
  · exact hy1 (by simpa using mul_mem (inv_mem hx1) h)

theorem isMaximalElementary_iff (M : Subgroup X) :
    (M ≤ (projUnip k).comap π ∧ CFSG.IsElementaryAbelian 2 M ∧
      ∀ E : Subgroup X, M ≤ E → E ≤ (projUnip k).comap π → CFSG.IsElementaryAbelian 2 E →
        E = M) ↔ M = (projRad k 0).comap π ∨ M = (projRad k 1).comap π := by
  have hHT : ∀ j : Fin 2, (projRad k j).comap π ≤ (projUnip k).comap π := fun j =>
    Subgroup.comap_mono (projRad_le_projUnip j)
  have hHel : ∀ j : Fin 2, CFSG.IsElementaryAbelian 2 ((projRad k j).comap π) := fun j =>
    isElementaryAbelian_of_sq_eq_one (comap_projRad_sq_eq_one hk hπ hCZ hC j)
  have hcard : ∀ j : Fin 2, Nat.card ((projRad k j).comap π) = 16 * Nat.card π.ker := fun j => by
    rw [card_comap_of_surjective hπ, card_projRad, hk]
  constructor
  · rintro ⟨hMT, hM, hmax⟩
    rcases le_or_le_of_isElementaryAbelian hk hπ hCZ hC hMT hM with h | h
    · exact Or.inl (hmax _ h (hHT 0) (hHel 0)).symm
    · exact Or.inr (hmax _ h (hHT 1) (hHel 1)).symm
  · have key : ∀ j : Fin 2, (projRad k j).comap π ≤ (projUnip k).comap π ∧
        CFSG.IsElementaryAbelian 2 ((projRad k j).comap π) ∧
        ∀ E : Subgroup X, (projRad k j).comap π ≤ E → E ≤ (projUnip k).comap π →
          CFSG.IsElementaryAbelian 2 E → E = (projRad k j).comap π := by
      intro j
      refine ⟨hHT j, hHel j, fun E hjE hET hE => ?_⟩
      rcases le_or_le_of_isElementaryAbelian hk hπ hCZ hC hET hE with h | h
      · have hj0 : (projRad k j).comap π = (projRad k 0).comap π :=
          Subgroup.eq_of_le_of_card_ge (hjE.trans h) (by rw [hcard, hcard])
        rw [hj0] at hjE ⊢
        exact le_antisymm h hjE
      · have hj1 : (projRad k j).comap π = (projRad k 1).comap π :=
          Subgroup.eq_of_le_of_card_ge (hjE.trans h) (by rw [hcard, hcard])
        rw [hj1] at hjE ⊢
        exact le_antisymm h hjE
    rintro (rfl | rfl)
    · exact key 0
    · exact key 1

omit [Finite X] in
theorem inf_centralizer_eq (i : Fin 2) {x : X} (hx : x ∈ (projRad k i).comap π)
    (hxZ : x ∉ (projCenterW k).comap π) :
    (projUnip k).comap π ⊓ centralizer {x} = (projRad k i).comap π := by
  refine le_antisymm (fun y hy => ?_) (le_inf (Subgroup.comap_mono (projRad_le_projUnip i))
    fun y hy => ?_)
  · obtain ⟨hyT, hyx⟩ := Subgroup.mem_inf.1 hy
    rw [mem_centralizer_singleton_iff] at hyx
    have h := mem_projRad_of_commute i hx hxZ hyT (by rw [← map_mul, ← map_mul, hyx])
    exact h
  · rw [mem_centralizer_singleton_iff]
    exact commute_of_sq_eq_one (comap_projRad_sq_eq_one hk hπ hCZ hC i) hy hx

theorem card_involutions :
    Nat.card {x : X // x ∈ (projUnip k).comap π ∧ orderOf x = 2} = 28 * Nat.card π.ker - 1 := by
  classical
  have hHT : ∀ j : Fin 2, (projRad k j).comap π ≤ (projUnip k).comap π := fun j =>
    Subgroup.comap_mono (projRad_le_projUnip j)
  have hset : {x : X | x ∈ (projUnip k).comap π ∧ orderOf x = 2} =
      (((projRad k 0).comap π : Set X) ∪ ((projRad k 1).comap π : Set X)) \ {1} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_union, SetLike.mem_coe,
      Set.mem_singleton_iff]
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [orderOf_eq_prime_iff]
    constructor
    · rintro ⟨hxT, h2, h1⟩
      exact ⟨(sq_eq_one_iff_mem_comap_projRad hk hπ hCZ hC hxT).1 h2, h1⟩
    · rintro ⟨h, h1⟩
      have hxT : x ∈ (projUnip k).comap π := h.elim (fun h => hHT 0 h) fun h => hHT 1 h
      exact ⟨hxT, (sq_eq_one_iff_mem_comap_projRad hk hπ hCZ hC hxT).2 h, h1⟩
  have hcard : ∀ j : Fin 2, Nat.card ((projRad k j).comap π) = 16 * Nat.card π.ker := fun j => by
    rw [card_comap_of_surjective hπ, card_projRad, hk]
  have hinter : ((projRad k 0).comap π : Set X) ∩ ((projRad k 1).comap π : Set X) =
      ((projCenterW k).comap π : Set X) := by
    rw [← Subgroup.coe_inf, ← Subgroup.comap_inf, projRad_inf_eq]
  have hZ : Nat.card ((projCenterW k).comap π) = 4 * Nat.card π.ker := by
    rw [card_comap_of_surjective hπ, card_projCenterW, hk]
  have hunion := Set.ncard_union_add_ncard_inter ((projRad k 0).comap π : Set X)
    ((projRad k 1).comap π : Set X)
  rw [hinter, Nat.card_coe_set_eq ((projRad k 0).comap π : Set X) |>.symm,
    Nat.card_coe_set_eq ((projRad k 1).comap π : Set X) |>.symm,
    Nat.card_coe_set_eq ((projCenterW k).comap π : Set X) |>.symm] at hunion
  change Nat.card ({x : X | x ∈ (projUnip k).comap π ∧ orderOf x = 2} : Set X) = _
  rw [hset, Nat.card_coe_set_eq, Set.ncard_sdiff_singleton_of_mem
    (Set.mem_union_left _ (one_mem _))]
  have h' : (((projRad k 0).comap π : Set X) ∪ ((projRad k 1).comap π : Set X)).ncard =
      28 * Nat.card π.ker := by
    have e0 : Nat.card (((projRad k 0).comap π : Subgroup X) : Set X) = 16 * Nat.card π.ker :=
      hcard 0
    have e1 : Nat.card (((projRad k 1).comap π : Subgroup X) : Set X) = 16 * Nat.card π.ker :=
      hcard 1
    have e2 : Nat.card (((projCenterW k).comap π : Subgroup X) : Set X) = 4 * Nat.card π.ker := hZ
    omega
  rw [h']

omit [Finite X] in
theorem exponent_comap_projUnip : Monoid.exponent ((projUnip k).comap π) = 4 := by
  have hZsq : ∀ z ∈ (projCenterW k).comap π, z ^ 2 = 1 := fun z hz =>
    comap_projRad_sq_eq_one hk hπ hCZ hC 0 z (Subgroup.comap_mono (projCenterW_le_projRad 0) hz)
  have h4 : ∀ x : (projUnip k).comap π, x ^ 4 = 1 := fun x => Subtype.ext (by
    rw [Subgroup.coe_pow, show (4 : ℕ) = 2 * 2 from rfl, pow_mul,
      hZsq _ (comap_projUnip_sq_mem hk x.2), Subgroup.coe_one])
  obtain ⟨t, ht⟩ := hπ (proj 3 k (unipU k 1 1 0))
  have htT : t ∈ (projUnip k).comap π := by
    rw [Subgroup.mem_comap, ht]
    exact mem_projUnip.2 ⟨1, 1, 0, rfl⟩
  have ht2 : (⟨t, htT⟩ : (projUnip k).comap π) ^ 2 ≠ 1 := fun h =>
    proj_unipU_one_one_sq_ne_one hk (by
      have h' := congrArg (fun y : (projUnip k).comap π => π (y : X)) h
      simpa [ht] using h')
  have hdvd : Monoid.exponent ((projUnip k).comap π) ∣ 2 ^ 2 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one h4
  have hn2 : ¬ Monoid.exponent ((projUnip k).comap π) ∣ 2 := fun h =>
    ht2 (Monoid.exponent_dvd_iff_forall_pow_eq_one.1 h _)
  obtain ⟨m, hm, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  interval_cases m
  · exact absurd (by rw [he]; exact one_dvd 2) hn2
  · exact absurd (by rw [he, pow_one]) hn2
  · rw [he]
    norm_num

theorem exists_sylow_mem_center {x : X} (hx : orderOf x = 2) :
    ∃ S : Sylow 2 X, x ∈ (S : Subgroup X) ∧ (S : Subgroup X) ≤ centralizer {x} := by
  have hprev := field_four_central_two_cover_parabolic_normalizers hk π hπ hCZ hC
  obtain ⟨-, -, ⟨S₀, hS₀⟩, -⟩ := hprev
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzp : IsPGroup 2 (zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨S, hS⟩ := hzp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X S₀ S
  have hxS : x ∈ ((g • S₀ : Sylow 2 X) : Subgroup X) := by
    rw [hg]
    exact hS (mem_zpowers x)
  rw [mem_smul_sylow_iff, hS₀] at hxS
  set y := g⁻¹ * x * g with hy
  obtain ⟨s, hs⟩ : ∃ s : X, s * y * s⁻¹ ∈ (projCenterW k).comap π := by
    by_cases hy1 : π y = 1
    · refine ⟨1, ?_⟩
      rw [one_mul, inv_one, mul_one, Subgroup.mem_comap, hy1]
      exact one_mem _
    · have hy2 : y ^ 2 = 1 := by
        rw [hy, show g⁻¹ * x * g = MulAut.conj g⁻¹ x by rw [MulAut.conj_apply, inv_inv], ← map_pow,
          ← hx, pow_orderOf_eq_one, map_one]
      have hyR := (sq_eq_one_iff_mem_comap_projRad hk hπ hCZ hC hxS).1 hy2
      have hw : proj 3 k (unipU k 0 0 1) ≠ 1 := proj_unipU_ne_one (by simp)
      have key : ∀ i : Fin 2, y ∈ (projRad k i).comap π →
          ∃ s : X, s * y * s⁻¹ ∈ (projCenterW k).comap π := by
        intro i hyi
        obtain ⟨p, hp⟩ := projRad_transitive i hyi
          (projCenterW_le_projRad i (mem_projCenterW.2 ⟨1, rfl⟩)) hy1 hw
        obtain ⟨s, rfl⟩ := hπ p
        refine ⟨s, ?_⟩
        rw [Subgroup.mem_comap, map_mul, map_mul, map_inv, hp]
        exact mem_projCenterW.2 ⟨1, rfl⟩
      rcases hyR with h | h
      · exact key 0 h
      · exact key 1 h
  refine ⟨(g * s⁻¹) • S₀, ?_, fun w hw => ?_⟩
  · rw [mem_smul_sylow_iff, hS₀]
    have h : (g * s⁻¹)⁻¹ * x * (g * s⁻¹) = s * y * s⁻¹ := by
      rw [hy]
      group
    rw [h]
    exact (Subgroup.comap_mono ((projCenterW_le_projRad 0).trans (projRad_le_projUnip 0))) hs
  · rw [mem_smul_sylow_iff, hS₀] at hw
    rw [mem_centralizer_singleton_iff]
    have hc := comap_projCenterW_commute hk hπ hCZ hC hs hw
    set h := g * s⁻¹ with hh
    set z := s * y * s⁻¹ with hz
    set w' := h⁻¹ * w * h with hw'def
    have hx' : x = h * z * h⁻¹ := by
      rw [hh, hz, hy]
      group
    have hw' : w = h * w' * h⁻¹ := by
      rw [hw'def]
      group
    rw [hx', hw']
    calc h * w' * h⁻¹ * (h * z * h⁻¹) = h * (w' * z) * h⁻¹ := by group
      _ = h * (z * w') * h⁻¹ := by rw [hc]
      _ = h * z * h⁻¹ * (h * w' * h⁻¹) := by group

omit [Finite k] [Finite X] hk hC in
theorem norm_package {R : Subgroup (projectiveSL 3 k)} (hRU : R ≤ projUnip k)
    {J : Subgroup X} {j : X} (hj3 : j ^ 3 = 1) (hjJ : j ∈ J) (hJc : ∀ j' ∈ J, j' * j = j * j')
    (hJV : J ≤ normalizer (R.comap π : Set X))
    (hfixP : ∀ x ∈ projUnip k, π j * x * (π j)⁻¹ = x → x = 1)
    (hV2 : ∀ v ∈ R.comap π, v ^ 2 = 1) :
    (∀ x, x ∈ ⁅R.comap π, J⁆ ↔ x ∈ R.comap π ∧ normOp j x = 1) ∧
      π.ker ⊔ ⁅R.comap π, J⁆ = R.comap π ∧ π.ker ⊓ ⁅R.comap π, J⁆ = ⊥ ∧
      ∃ e : (⁅R.comap π, J⁆ : Subgroup X) ≃* R, ∀ x, (e x : projectiveSL 3 k) = π x := by
  have hJV' : ∀ j' ∈ J, ∀ v ∈ R.comap π, MulAut.conj j' v ∈ R.comap π := fun j' hj' v hv => by
    rw [MulAut.conj_apply]
    exact (mem_normalizer_iff.1 (hJV hj') v).1 hv
  have hjV := hJV' j hjJ
  have hVc : ∀ a ∈ R.comap π, ∀ b ∈ R.comap π, a * b = b * a := fun a ha b hb =>
    commute_of_sq_eq_one hV2 ha hb
  have hCV : π.ker ≤ R.comap π := π.ker_le_comap R
  have hCZ' : ∀ c ∈ π.ker, ∀ g : X, g * c = c * g := fun c hc g => mem_center_iff.1 (hCZ hc) g
  have hfix : ∀ v ∈ R.comap π, MulAut.conj j v = v → v ∈ π.ker := by
    intro v hv h
    have h' := congrArg π h
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv] at h'
    exact hfixP _ (hRU hv) h'
  have hiff := fun x => mem_commutator_iff_normOp hj3 hjV hVc hV2 hCZ' hfix hjJ hJc hJV' (x := x)
  have hsup := sup_commutator_eq hj3 hjV hVc hV2 hCV hCZ' hfix hjJ hJc hJV'
  have hinf := inf_commutator_eq_bot hj3 hjV hVc hV2 hCV hCZ' hfix hjJ hJc hJV'
  refine ⟨hiff, hsup, hinf, ?_⟩
  let f : (⁅R.comap π, J⁆ : Subgroup X) →* R :=
    (π.comp ⁅R.comap π, J⁆.subtype).codRestrict R fun x => ((hiff x).1 x.2).1
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxC : (x : X) ∈ π.ker := MonoidHom.mem_ker.2 (congrArg Subtype.val hx)
    have h : (x : X) ∈ π.ker ⊓ ⁅R.comap π, J⁆ := ⟨hxC, x.2⟩
    rw [hinf, Subgroup.mem_bot] at h
    exact Subtype.ext h
  have hfsurj : Function.Surjective f := by
    rintro ⟨r, hr⟩
    obtain ⟨v, rfl⟩ := hπ r
    have hv : v ∈ R.comap π := hr
    have hN := normOp_mem_C hj3 hjV hVc hfix hv
    have hNN : normOp j (normOp j v) = normOp j v := normOp_eq_self_of_mem hV2 hCV hCZ' hN
    have hmem : v * normOp j v ∈ ⁅R.comap π, J⁆ := by
      refine (hiff _).2 ⟨mul_mem hv (hCV hN), ?_⟩
      rw [normOp_mul hjV hVc hv (hCV hN), hNN, ← sq, hV2 _ (hCV hN)]
    refine ⟨⟨_, hmem⟩, Subtype.ext ?_⟩
    change π (v * normOp j v) = π v
    rw [map_mul, MonoidHom.mem_ker.1 hN, mul_one]
  exact ⟨MulEquiv.ofBijective f ⟨hfinj, hfsurj⟩, fun x => rfl⟩

omit [Finite k] [Finite X] hk hπ hCZ hC in
theorem inf_normalizer_le_normalizer_inf (A B : Subgroup X) :
    normalizer (A : Set X) ⊓ normalizer (B : Set X) ≤
      normalizer ((A ⊓ B : Subgroup X) : Set X) := by
  intro g hg
  obtain ⟨hA, hB⟩ := Subgroup.mem_inf.1 hg
  rw [mem_normalizer_iff] at hA hB ⊢
  intro h
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hA, hB]

theorem sylow_geometry_two (σ₁ : SL2 k →* X) (hσ₁ : ∀ B, π (σ₁ B) = leviProj k 0 B) :
    let T := (projUnip k).comap π
    let H : Fin 2 → Subgroup X := fun i => (projRad k i).comap π
    let Z := (projCenterW k).comap π
    let J := (sl2Torus k).map σ₁
    let K : Fin 2 → Subgroup X := fun i => ⁅H i, J⁆
    let Z₀ := ⁅Z, J⁆
    Nat.card J = 3 ∧
      normalizer (T : Set X) = normalizer (H 0 : Set X) ⊓ normalizer (H 1 : Set X) ∧
      T ⊔ J = normalizer (T : Set X) ∧ T ⊓ J = ⊥ ∧
      Nat.card (normalizer (T : Set X)) = 192 * Nat.card π.ker ∧
      (∀ i, J ≤ normalizer (H i : Set X)) ∧ J ≤ normalizer (Z : Set X) ∧
      normalizer (T : Set X) ≤ normalizer (Z : Set X) ∧
      (∀ i, ∃ e : K i ≃* projRad k i, ∀ x, (e x : projectiveSL 3 k) = π x) ∧
      (∃ e : Z₀ ≃* projCenterW k, ∀ x, (e x : projectiveSL 3 k) = π x) ∧
      (∀ i, CFSG.Walter.JT.IsInternalDirectProduct π.ker (K i) (H i)) ∧
      CFSG.Walter.JT.IsInternalDirectProduct π.ker Z₀ Z ∧ K 0 ⊓ K 1 = Z₀ ∧
      (∀ i, CFSG.IsElementaryAbelian 2 (K i) ∧ Nat.card (K i) = 16) ∧
      CFSG.IsElementaryAbelian 2 Z₀ ∧ Nat.card Z₀ = 4 ∧
      Z ⊓ centralizer (J : Set X) = π.ker ∧
      ∀ z ∈ Z₀, ∀ z' ∈ Z₀, z ≠ 1 → z' ≠ 1 → ∃ j ∈ J, j * z * j⁻¹ = z' := by
  intro T H Z J K Z₀
  have hσinj : Function.Injective σ₁ := fun B B' h =>
    leviProj_injective 0 (by rw [← hσ₁, ← hσ₁, h])
  have hJcard : Nat.card J = 3 := by
    rw [Subgroup.card_map_of_injective hσinj, card_sl2Torus, hk]
  have hNT : normalizer (T : Set X) = (normalizer (projUnip k : Set (projectiveSL 3 k))).comap π :=
    (Subgroup.comap_normalizer_eq_of_surjective _ hπ).symm
  have hNH : ∀ i, normalizer (H i : Set X) =
      (normalizer (projRad k i : Set (projectiveSL 3 k))).comap π := fun i =>
    (Subgroup.comap_normalizer_eq_of_surjective _ hπ).symm
  have hNTeq : normalizer (T : Set X) = normalizer (H 0 : Set X) ⊓ normalizer (H 1 : Set X) := by
    rw [hNT, hNH, hNH, normalizer_projUnip_eq_inf hk, Subgroup.comap_inf]
  have hZeq : Z = H 0 ⊓ H 1 := by
    change (projCenterW k).comap π = (projRad k 0).comap π ⊓ (projRad k 1).comap π
    rw [← Subgroup.comap_inf, projRad_inf_eq]
  let δ : sl2Torus k →* projectiveSL 3 k := (leviProj k 0).comp (sl2Torus k).subtype
  let s : sl2Torus k →* X := σ₁.comp (sl2Torus k).subtype
  have hδinj : Function.Injective δ := (leviProj_injective 0).comp Subtype.val_injective
  have hδrange : δ.range = projTorus k := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  have hsrange : s.range = J := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hs : ∀ d, π (s d) = δ d := fun d => hσ₁ d
  have hlift := lift_complement hπ hδinj (by rw [hδrange]; exact normalizer_projUnip hk)
    (by rw [hδrange]; exact projUnip_inf_projTorus) s hs
  obtain ⟨hsinj, hsN, hsup, hinf⟩ := hlift
  have hcardN := card_normalizer_of_lift s hsinj hsN hsup hinf
  rw [hsrange] at hsup hinf
  have hJT : J ≤ normalizer (T : Set X) := hsup ▸ le_sup_right
  have hJH : ∀ i, J ≤ normalizer (H i : Set X) := fun i => by
    have h := hJT.trans hNTeq.le
    fin_cases i
    · exact h.trans inf_le_left
    · exact h.trans inf_le_right
  have hJZ : J ≤ normalizer (Z : Set X) := by
    rw [hZeq]
    exact (le_inf (hJH 0) (hJH 1)).trans (inf_normalizer_le_normalizer_inf _ _)
  obtain ⟨t, ht0, ht1⟩ := exists_ne_zero_ne_one_of_card hk
  set ω : kˣ := Units.mk0 t ht0 with hω
  have hω1 : ω ≠ 1 := fun h => ht1 (by rw [← Units.val_mk0 ht0, ← hω, h, Units.val_one])
  have hω3 : ω ^ 3 = 1 := Units.ext (by
    rw [Units.val_pow_eq_pow_val, hω, Units.val_mk0, Units.val_one]
    exact pow_three_eq_one_of_card hk ht0)
  set j := σ₁ (HSL ω) with hj
  have hj3 : j ^ 3 = 1 := by
    rw [hj, ← map_pow, pow_three', HSL_mul, HSL_mul, ← pow_three', hω3, HSL_one, map_one]
  have hjJ : j ∈ J := ⟨HSL ω, ⟨ω, rfl⟩, rfl⟩
  have hJc : ∀ j' ∈ J, j' * j = j * j' := by
    rintro _ ⟨B, hB, rfl⟩
    rw [hj, ← map_mul, ← map_mul, commute_of_mem_sl2Torus hB ⟨ω, rfl⟩]
  have hfixP : ∀ x ∈ projUnip k, π j * x * (π j)⁻¹ = x → x = 1 := by
    intro x hx h
    rw [hj, hσ₁] at h
    exact eq_one_of_conj_torus_eq hk hω1 hx h
  have hHsq := comap_projRad_sq_eq_one hk hπ hCZ hC
  have hZsq : ∀ v ∈ (projCenterW k).comap π, v ^ 2 = 1 := fun v hv =>
    hHsq 0 v (Subgroup.comap_mono (projCenterW_le_projRad 0) hv)
  have pkg : ∀ i : Fin 2, _ := fun i => norm_package hπ hCZ (projRad_le_projUnip i) hj3 hjJ hJc
    (hJH i) hfixP (hHsq i)
  have pkgZ := norm_package hπ hCZ ((projCenterW_le_projRad 0).trans (projRad_le_projUnip 0)) hj3
    hjJ hJc hJZ hfixP hZsq
  have hCcent : ∀ V : Subgroup X, π.ker ≤ centralizer (V : Set X) := fun V c hc =>
    mem_centralizer_iff.2 fun g _ => mem_center_iff.1 (hCZ hc) g
  have hKsq : ∀ i : Fin 2, ∀ x ∈ K i, x ^ 2 = 1 := fun i x hx =>
    hHsq i x (((pkg i).1 x).1 hx).1
  have hZ₀sq : ∀ x ∈ Z₀, x ^ 2 = 1 := fun x hx => hZsq x ((pkgZ.1 x).1 hx).1
  have hNTZ : normalizer (T : Set X) ≤ normalizer (Z : Set X) := by
    rw [hZeq, hNTeq]
    exact inf_normalizer_le_normalizer_inf _ _
  refine ⟨hJcard, hNTeq, hsup, hinf, ?_, hJH, hJZ, hNTZ, fun i => (pkg i).2.2.2, pkgZ.2.2.2,
    fun i => ⟨(pkg i).2.1, disjoint_iff.2 (pkg i).2.2.1, hCcent _⟩,
    ⟨pkgZ.2.1, disjoint_iff.2 pkgZ.2.2.1, hCcent _⟩, ?_, fun i => ?_,
    isElementaryAbelian_of_sq_eq_one hZ₀sq, ?_, ?_, ?_⟩
  · rw [hcardN, card_comap_of_surjective hπ, card_projUnip, hk, card_sl2Torus, hk]
    ring
  · ext x
    rw [Subgroup.mem_inf, (pkg 0).1, (pkg 1).1, pkgZ.1]
    change (x ∈ H 0 ∧ _) ∧ (x ∈ H 1 ∧ _) ↔ x ∈ Z ∧ _
    rw [hZeq, Subgroup.mem_inf]
    tauto
  · obtain ⟨e, -⟩ := (pkg i).2.2.2
    refine ⟨isElementaryAbelian_of_sq_eq_one (hKsq i), ?_⟩
    rw [Nat.card_congr e.toEquiv, card_projRad, hk]
  · obtain ⟨e, -⟩ := pkgZ.2.2.2
    rw [Nat.card_congr e.toEquiv, card_projCenterW, hk]
  · refine le_antisymm (fun z hz => ?_) (le_inf (π.ker_le_comap _) (hCcent _))
    obtain ⟨hzZ, hzJ⟩ := Subgroup.mem_inf.1 hz
    have hcomm := mem_centralizer_iff.1 hzJ j hjJ
    have h := hfixP (π z) ((projCenterW_le_projRad 0).trans (projRad_le_projUnip 0) hzZ) (by
      rw [← map_inv, ← map_mul, ← map_mul, hcomm, mul_inv_cancel_right])
    exact h
  · intro z hz z' hz' hz1 hz'1
    obtain ⟨e, he⟩ := pkgZ.2.2.2
    have hne : ∀ y : Z₀, (y : X) ≠ 1 → ∃ c : k, c ≠ 0 ∧ π y = proj 3 k (unipU k 0 0 c) := by
      intro y hy
      obtain ⟨c, hc⟩ := mem_projCenterW.1 (e y).2
      refine ⟨c, fun hc0 => hy ?_, by rw [← he, ← hc]⟩
      have h1 : e y = 1 := Subtype.ext (by rw [← hc, hc0, unipU_zero, map_one]; rfl)
      rw [← map_one e] at h1
      exact congrArg Subtype.val (e.injective h1)
    obtain ⟨c, hc0, hc⟩ := hne ⟨z, hz⟩ hz1
    obtain ⟨c', hc'0, hc'⟩ := hne ⟨z', hz'⟩ hz'1
    set l : kˣ := Units.mk0 (c' / c) (div_ne_zero hc'0 hc0) with hl
    have hj'J : σ₁ (HSL l) ∈ J := ⟨HSL l, ⟨l, rfl⟩, rfl⟩
    refine ⟨σ₁ (HSL l), hj'J, ?_⟩
    have hmem : σ₁ (HSL l) * z * (σ₁ (HSL l))⁻¹ ∈ Z₀ := by
      rw [pkgZ.1] at hz ⊢
      have hconj : σ₁ (HSL l) * z * (σ₁ (HSL l))⁻¹ = MulAut.conj (σ₁ (HSL l)) z :=
        (MulAut.conj_apply _ _).symm
      refine ⟨(mem_normalizer_iff.1 (hJZ hj'J) z).1 hz.1, ?_⟩
      rw [hconj, normOp_conj (hJc _ hj'J), hz.2, map_one]
    have hπeq : e ⟨_, hmem⟩ = e ⟨z', hz'⟩ := by
      apply Subtype.ext
      rw [he, he]
      change π (σ₁ (HSL l) * z * (σ₁ (HSL l))⁻¹) = π z'
      rw [map_mul, map_mul, map_inv, hσ₁, hc, leviProj_HSL_conj_W, hc', hl, Units.val_mk0,
        div_mul_cancel₀ c' hc0]
    exact congrArg Subtype.val (e.injective hπeq)

omit [Finite X] hCZ hC in
theorem comap_projRad_zero_le {t : k} (ht0 : t ≠ 0) (ht1 : t ≠ 1) {x₁ x₂ : X}
    (h₁ : π x₁ = proj 3 k (unipU k 1 0 0)) (h₂ : π x₂ = proj 3 k (unipU k t 0 0)) :
    (projRad k 0).comap π ≤ (projCenterW k).comap π ⊔ zpowers x₁ ⊔ zpowers x₂ := by
  have hmap : ((projCenterW k).comap π ⊔ zpowers x₁ ⊔ zpowers x₂).map π =
      projCenterW k ⊔ zpowers (proj 3 k (unipU k 1 0 0)) ⊔
        zpowers (proj 3 k (unipU k t 0 0)) := by
    rw [Subgroup.map_sup, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers, h₁, h₂,
      Subgroup.map_comap_eq_self_of_surjective hπ]
  have hle := Subgroup.comap_mono (f := π) (projRad_zero_le_sup hk ht0 ht1)
  rw [← hmap, Subgroup.comap_map_eq, sup_eq_left.2
    (le_sup_left.trans le_sup_left |>.trans' (π.ker_le_comap _))] at hle
  exact hle

omit [Finite X] hCZ hC in
theorem comap_projRad_one_le {t : k} (ht0 : t ≠ 0) (ht1 : t ≠ 1) {y₁ y₂ : X}
    (h₁ : π y₁ = proj 3 k (unipU k 0 1 0)) (h₂ : π y₂ = proj 3 k (unipU k 0 t 0)) :
    (projRad k 1).comap π ≤ (projCenterW k).comap π ⊔ zpowers y₁ ⊔ zpowers y₂ := by
  have hmap : ((projCenterW k).comap π ⊔ zpowers y₁ ⊔ zpowers y₂).map π =
      projCenterW k ⊔ zpowers (proj 3 k (unipU k 0 1 0)) ⊔
        zpowers (proj 3 k (unipU k 0 t 0)) := by
    rw [Subgroup.map_sup, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers, h₁, h₂,
      Subgroup.map_comap_eq_self_of_surjective hπ]
  have hle := Subgroup.comap_mono (f := π) (projRad_one_le_sup hk ht0 ht1)
  rw [← hmap, Subgroup.comap_map_eq, sup_eq_left.2
    (le_sup_left.trans le_sup_left |>.trans' (π.ker_le_comap _))] at hle
  exact hle

theorem ker_le_commutator [Group.IsPerfect X] :
    π.ker ≤ ⁅(projUnip k).comap π, (projUnip k).comap π⁆ := by
  have hprev := field_four_central_two_cover_parabolic_normalizers hk π hπ hCZ hC
  obtain ⟨-, -, ⟨S₀, hS₀⟩, -⟩ := hprev
  have hC2 : ∀ c ∈ π.ker, c ^ 2 = 1 := fun c hc =>
    CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := π.ker) c hc
  intro c hc
  set T := (projUnip k).comap π with hT
  have hcT : c ∈ T := π.ker_le_comap _ hc
  have hidx : ¬ 2 ∣ T.index := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h := S₀.not_dvd_index
    rwa [hS₀] at h
  let φ : T →* Abelianization T := Abelianization.of
  have hkill : φ.transfer = 1 := MonoidHom.ext fun x => by
    have hx : x ∈ commutator X := by
      rw [Group.IsPerfect.commutator_eq_top]
      exact Subgroup.mem_top x
    exact Abelianization.commutator_subset_ker φ.transfer hx
  have key : ∀ (n : ℕ) (g₀ : X), g₀⁻¹ * c ^ n * g₀ ∈ T → g₀⁻¹ * c ^ n * g₀ = c ^ n := by
    intro n g₀ _
    have hcn : c ^ n ∈ π.ker := π.ker.pow_mem hc n
    rw [mul_assoc, ← mem_center_iff.1 (hCZ hcn) g₀, inv_mul_cancel_left]
  have h1 := MonoidHom.transfer_eq_pow φ c key
  have hodd : Odd T.index := Nat.not_even_iff_odd.1 fun he => hidx (even_iff_two_dvd.1 he)
  obtain ⟨m, hm⟩ := hodd
  have hcpow : c ^ T.index = c := by
    rw [hm, pow_succ, pow_mul, hC2 c hc, one_pow, one_mul]
  have h2 : φ ⟨c, hcT⟩ = 1 := by
    have e : (⟨c ^ T.index, MonoidHom.transfer_eq_pow_aux c key⟩ : T) = ⟨c, hcT⟩ :=
      Subtype.ext hcpow
    rw [← e, ← h1, hkill, MonoidHom.one_apply]
  have h3 : (⟨c, hcT⟩ : T) ∈ commutator T := by
    rw [← Abelianization.ker_of]
    exact h2
  rw [← Subgroup.map_subtype_commutator]
  exact ⟨_, h3, rfl⟩

theorem sylow_geometry_three_a [Group.IsPerfect X] :
    let T := (projUnip k).comap π
    let H : Fin 2 → Subgroup X := fun i => (projRad k i).comap π
    ⁅T, H 0⁆ = ⁅T, T⁆ ∧ ⁅T, H 1⁆ = ⁅T, T⁆ ∧ ⁅T, T⁆ = (frattini T).map T.subtype ∧
      (frattini T).map T.subtype = (center T).map T.subtype ∧
      CFSG.IsElementaryAbelian 2 (T ⧸ center T) ∧ Nat.card (T ⧸ center T) = 16 ∧
      ⁅T, T⁆ = (projCenterW k).comap π ∧ ⁅T, T⁆ = ⁅H 0, H 1⁆ := by
  intro T H
  have hprev := field_four_central_two_cover_parabolic_normalizers hk π hπ hCZ hC
  obtain ⟨-, hTmul, ⟨S₀, hS₀⟩, hTcard, -, hcenter, hZcard, -⟩ := hprev
  have hTmul' : ((projRad k 0).comap π : Set X) * ((projRad k 1).comap π : Set X) =
      (projUnip k).comap π := hTmul
  have hcenter' : (center T).map T.subtype = (projCenterW k).comap π := hcenter
  have hHsq := comap_projRad_sq_eq_one hk hπ hCZ hC
  have hHT : ∀ i, H i ≤ T := fun i => Subgroup.comap_mono (projRad_le_projUnip i)
  have hZc : ∀ z ∈ (projCenterW k).comap π, ∀ w ∈ T, z * w = w * z := fun z hz w hw =>
    comap_projCenterW_commute hk hπ hCZ hC hz hw
  have hcent : ∀ u ∈ T, ∀ v ∈ T, ∀ w ∈ T, ⁅u, v⁆ * w = w * ⁅u, v⁆ := fun u hu v hv w hw =>
    hZc _ (comap_projUnip_commutator_mem hu hv) w hw
  have hCTT := ker_le_commutator hk hπ hCZ hC
  have hTmap : T.map π = projUnip k := Subgroup.map_comap_eq_self_of_surjective hπ _
  have hTTmap : ⁅T, T⁆.map π = projCenterW k := by
    rw [Subgroup.map_commutator, hTmap, commutator_projUnip]
  have hTTZ : ⁅T, T⁆ = (projCenterW k).comap π := by
    refine le_antisymm (fun x hx => ?_) (fun z hz => ?_)
    · change π x ∈ projCenterW k
      rw [← hTTmap]
      exact ⟨x, hx, rfl⟩
    · have hzW : π z ∈ ⁅T, T⁆.map π := by
        rw [hTTmap]
        exact hz
      obtain ⟨y, hy, hyz⟩ := hzW
      have hc : y⁻¹ * z ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hyz, inv_mul_cancel]
      have h := mul_mem hy (hCTT hc)
      rwa [mul_inv_cancel_left] at h
  have hTTH : ⁅T, T⁆ ≤ ⁅H 0, H 1⁆ := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    have hx' : x ∈ ((projRad k 0).comap π : Set X) * ((projRad k 1).comap π : Set X) := by
      rw [hTmul']
      exact hx
    have hy' : y ∈ ((projRad k 0).comap π : Set X) * ((projRad k 1).comap π : Set X) := by
      rw [hTmul']
      exact hy
    obtain ⟨a, ha, b, hb, rfl⟩ := hx'
    obtain ⟨c, hc, d, hd, rfl⟩ := hy'
    rw [commutatorElement_mul_mul_eq (commute_of_sq_eq_one (hHsq 0) ha hc)
      (commute_of_sq_eq_one (hHsq 1) hb hd) (hcent _ (hHT 1 hb) _ (hHT 0 hc) _ (hHT 0 ha))
      (hcent _ (hHT 0 ha) _ (hHT 1 hd) _ (hHT 0 hc))]
    refine mul_mem ?_ (Subgroup.commutator_mem_commutator ha hd)
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator hb hc
  have hTTeq : ⁅T, T⁆ = ⁅H 0, H 1⁆ :=
    le_antisymm hTTH (Subgroup.commutator_mono (hHT 0) (hHT 1))
  have hTH0 : ⁅T, H 0⁆ = ⁅T, T⁆ := by
    refine le_antisymm (Subgroup.commutator_mono le_rfl (hHT 0)) (hTTH.trans ?_)
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_mono (hHT 1) le_rfl
  have hTH1 : ⁅T, H 1⁆ = ⁅T, T⁆ :=
    le_antisymm (Subgroup.commutator_mono le_rfl (hHT 1))
      (hTTH.trans (Subgroup.commutator_mono (hHT 0) le_rfl))
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTp : IsPGroup 2 T := by
    have h := S₀.isPGroup'
    rwa [hS₀] at h
  have : Fact (IsPGroup 2 T) := ⟨hTp⟩
  have hcommT : commutator T = center T := by
    apply Subgroup.map_injective T.subtype_injective
    rw [Subgroup.map_subtype_commutator, hcenter', hTTZ]
  have hsqT : ∀ t : T, t ^ 2 ∈ center T := fun t => by
    have h : ((t ^ 2 : T) : X) ∈ (center T).map T.subtype := by
      rw [hcenter', Subgroup.coe_pow]
      exact comap_projUnip_sq_mem hk t.2
    obtain ⟨u, hu, hut⟩ := h
    rwa [show u = t ^ 2 from Subtype.ext hut] at hu
  have hfr : frattini T = center T := by
    rw [CFSG.frattini_eq_closure_commutator_union_powers (p := 2), hcommT]
    refine le_antisymm ((Subgroup.closure_le _).2 ?_) fun x hx =>
      Subgroup.subset_closure (Or.inl hx)
    rintro x (hx | ⟨y, rfl⟩)
    · exact hx
    · exact hsqT y
  have hQcomm : IsMulCommutative (T ⧸ center T) :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := center T)).2 hcommT.le
  have hQsq : ∀ q : T ⧸ center T, q ^ 2 = 1 := fun q => by
    induction q using QuotientGroup.induction_on with
    | H t =>
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact hsqT t
  have hZTcard : Nat.card (center T) = 4 * Nat.card π.ker := by
    rw [← Subgroup.card_map_of_injective T.subtype_injective, hcenter']
    exact hZcard
  have hQcard : Nat.card (T ⧸ center T) = 16 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (center T)
    rw [hZTcard] at h
    have hT : Nat.card T = 64 * Nat.card π.ker := hTcard
    rw [hT] at h
    have hpos : 0 < 4 * Nat.card π.ker := by
      have := (Nat.card_pos (α := π.ker))
      omega
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    rw [← h]
    ring
  refine ⟨hTH0, hTH1, by rw [hfr, hcenter', hTTZ], by rw [hfr], ?_, hQcard, hTTZ, hTTeq⟩
  exact
    { toIsMulCommutative := hQcomm
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hQsq }

theorem sylow_geometry_three_b [Group.IsPerfect X] (σ₁ : SL2 k →* X)
    (hσ₁ : ∀ B, π (σ₁ B) = leviProj k 0 B) :
    let T := (projUnip k).comap π
    let H : Fin 2 → Subgroup X := fun i => (projRad k i).comap π
    let J := (sl2Torus k).map σ₁
    let K : Fin 2 → Subgroup X := fun i => ⁅H i, J⁆
    (Nat.card π.ker = 1 ∨ Nat.card π.ker = 2 ∨ Nat.card π.ker = 4) ∧ Group.rank T = 4 ∧
      K 0 ⊔ K 1 = T := by
  intro T H J K
  classical
  have hprev := field_four_central_two_cover_parabolic_normalizers hk π hπ hCZ hC
  obtain ⟨-, hTmul, -, -, -, -, hZcard, -⟩ := hprev
  have hTmul' : ((projRad k 0).comap π : Set X) * ((projRad k 1).comap π : Set X) =
      (projUnip k).comap π := hTmul
  have ha := sylow_geometry_three_a hk hπ hCZ hC
  obtain ⟨-, -, -, -, hQel, hQcard, hTTZ, hTTeq⟩ := ha
  have hHsq := comap_projRad_sq_eq_one hk hπ hCZ hC
  have hHT : ∀ i, H i ≤ T := fun i => Subgroup.comap_mono (projRad_le_projUnip i)
  set Z := (projCenterW k).comap π with hZdef
  have hZT : Z ≤ T :=
    Subgroup.comap_mono ((projCenterW_le_projRad 0).trans (projRad_le_projUnip 0))
  have hZsq : ∀ z ∈ Z, z ^ 2 = 1 := fun z hz =>
    hHsq 0 z (Subgroup.comap_mono (projCenterW_le_projRad 0) hz)
  have hZc : ∀ z ∈ Z, ∀ w ∈ T, z * w = w * z := fun z hz w hw =>
    comap_projCenterW_commute hk hπ hCZ hC hz hw
  have hcent : ∀ u ∈ T, ∀ v ∈ T, ∀ w ∈ T, ⁅u, v⁆ * w = w * ⁅u, v⁆ := fun u hu v hv w hw =>
    hZc _ (comap_projUnip_commutator_mem hu hv) w hw
  obtain ⟨t, ht0, ht1⟩ := exists_ne_zero_ne_one_of_card hk
  obtain ⟨x₁, hx₁⟩ := hπ (proj 3 k (unipU k 1 0 0))
  obtain ⟨x₂, hx₂⟩ := hπ (proj 3 k (unipU k t 0 0))
  obtain ⟨y₁, hy₁⟩ := hπ (proj 3 k (unipU k 0 1 0))
  obtain ⟨y₂, hy₂⟩ := hπ (proj 3 k (unipU k 0 t 0))
  have hmemT : ∀ {x : X} {a b c : k}, π x = proj 3 k (unipU k a b c) → x ∈ T := fun h => by
    change π _ ∈ projUnip k
    rw [h]
    exact mem_projUnip.2 ⟨_, _, _, rfl⟩
  have hx₁T := hmemT hx₁
  have hx₂T := hmemT hx₂
  have hy₁T := hmemT hy₁
  have hy₂T := hmemT hy₂
  have hH0 := comap_projRad_zero_le hk hπ ht0 ht1 hx₁ hx₂
  have hH1 := comap_projRad_one_le hk hπ ht0 ht1 hy₁ hy₂
  have hD := commutator_le_closure_four hcent hZc hZT hx₁T hx₂T hy₁T hy₂T hH0 hH1 (hHT 1)
  set D := closure ({⁅x₁, y₁⁆, ⁅x₁, y₂⁆, ⁅x₂, y₁⁆, ⁅x₂, y₂⁆} : Set X) with hDdef
  have hDcard : Nat.card D ≤ 16 := by
    let S : Finset X := {⁅x₁, y₁⁆, ⁅x₁, y₂⁆, ⁅x₂, y₁⁆, ⁅x₂, y₂⁆}
    have hSZ : ∀ g ∈ S, g ∈ Z := by
      intro g hg
      simp only [S, Finset.mem_insert, Finset.mem_singleton] at hg
      rcases hg with rfl | rfl | rfl | rfl
      · exact comap_projUnip_commutator_mem hx₁T hy₁T
      · exact comap_projUnip_commutator_mem hx₁T hy₂T
      · exact comap_projUnip_commutator_mem hx₂T hy₁T
      · exact comap_projUnip_commutator_mem hx₂T hy₂T
    have h := card_closure_le_two_pow S
      (fun a ha b hb => commute_of_sq_eq_one hZsq (hSZ a ha) (hSZ b hb))
      (fun a ha => hZsq a (hSZ a ha))
    have hS : (S : Set X) = {⁅x₁, y₁⁆, ⁅x₁, y₂⁆, ⁅x₂, y₁⁆, ⁅x₂, y₂⁆} := by
      simp only [S, Finset.coe_insert, Finset.coe_singleton]
    rw [hS] at h
    calc Nat.card D ≤ 2 ^ S.card := h
      _ ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) Finset.card_le_four
  have hZle : Nat.card Z ≤ 16 := by
    calc Nat.card Z = Nat.card (⁅T, T⁆ : Subgroup X) := by rw [hTTZ]
      _ ≤ Nat.card (⁅H 0, H 1⁆ : Subgroup X) := Subgroup.card_le_of_le hTTeq.le
      _ ≤ Nat.card D := Subgroup.card_le_of_le hD
      _ ≤ 16 := hDcard
  have hZcard' : Nat.card Z = 4 * Nat.card π.ker := hZcard
  rw [hZcard'] at hZle
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 (CFSG.IsElementaryAbelian.isPGroup 2 π.ker)
  have hn2 : n ≤ 2 := by
    by_contra h
    have h3 : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hCcard : Nat.card π.ker = 1 ∨ Nat.card π.ker = 2 ∨ Nat.card π.ker = 4 := by
    interval_cases n
    · left
      rw [hn]
      norm_num
    · right
      left
      rw [hn]
      norm_num
    · right
      right
      rw [hn]
      norm_num
  have hgen : closure ({x₁, x₂, y₁, y₂} : Set X) = T := by
    set G4 := closure ({x₁, x₂, y₁, y₂} : Set X) with hG4
    have hx₁G : x₁ ∈ G4 := subset_closure (by simp)
    have hx₂G : x₂ ∈ G4 := subset_closure (by simp)
    have hy₁G : y₁ ∈ G4 := subset_closure (by simp)
    have hy₂G : y₂ ∈ G4 := subset_closure (by simp)
    have hcomm : ∀ {a b : X}, a ∈ G4 → b ∈ G4 → ⁅a, b⁆ ∈ G4 := fun ha hb => by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
    have hDG : D ≤ G4 := by
      rw [hDdef, Subgroup.closure_le]
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl | rfl
      · exact hcomm hx₁G hy₁G
      · exact hcomm hx₁G hy₂G
      · exact hcomm hx₂G hy₁G
      · exact hcomm hx₂G hy₂G
    have hZG : Z ≤ G4 := hTTZ ▸ (hTTeq.le.trans (hD.trans hDG))
    have hH0G : H 0 ≤ G4 := hH0.trans (sup_le (sup_le hZG ((zpowers_le).2 hx₁G))
      ((zpowers_le).2 hx₂G))
    have hH1G : H 1 ≤ G4 := hH1.trans (sup_le (sup_le hZG ((zpowers_le).2 hy₁G))
      ((zpowers_le).2 hy₂G))
    refine le_antisymm ((Subgroup.closure_le _).2 ?_) fun x hx => ?_
    · intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl | rfl
      · exact hx₁T
      · exact hx₂T
      · exact hy₁T
      · exact hy₂T
    · have hx' : x ∈ ((projRad k 0).comap π : Set X) * ((projRad k 1).comap π : Set X) := by
        rw [hTmul']
        exact hx
      obtain ⟨a, ha, b, hb, rfl⟩ := hx'
      exact mul_mem (hH0G ha) (hH1G hb)
  have hrank_le : Group.rank T ≤ 4 := by
    let S : Finset T := {⟨x₁, hx₁T⟩, ⟨x₂, hx₂T⟩, ⟨y₁, hy₁T⟩, ⟨y₂, hy₂T⟩}
    have hS : closure (S : Set T) = ⊤ := by
      apply Subgroup.map_injective T.subtype_injective
      rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
      have himg : (T.subtype '' (S : Set T)) = ({x₁, x₂, y₁, y₂} : Set X) := by
        simp only [S, Finset.coe_insert, Finset.coe_singleton, Set.image_insert_eq,
          Set.image_singleton, Subgroup.coe_subtype]
      rw [himg, hgen]
    exact (Group.rank_le hS).trans Finset.card_le_four
  have hrank_ge : 4 ≤ Group.rank T := by
    have hQ : 4 ≤ Group.rank (T ⧸ center T) := by
      obtain ⟨S', hS'card, hS'⟩ := Group.rank_spec (T ⧸ center T)
      have hcommQ := hQel.toIsMulCommutative
      have hQsq : ∀ q : T ⧸ center T, q ^ 2 = 1 := fun q =>
        Monoid.exponent_dvd_iff_forall_pow_eq_one.1 hQel.exponent_dvd_p q
      have h := card_closure_le_two_pow S' (fun a _ b _ => mul_comm' a b) (fun a _ => hQsq a)
      rw [hS', Subgroup.card_top, hQcard, hS'card] at h
      by_contra hlt
      have h8 : 2 ^ Group.rank (T ⧸ center T) ≤ 2 ^ 3 :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    exact hQ.trans (Group.rank_le_of_surjective (QuotientGroup.mk' (center T))
      (QuotientGroup.mk'_surjective _))
  have htwo := sylow_geometry_two hk hπ hCZ hC σ₁ hσ₁
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hdp, -⟩ := htwo
  have hCK : ∀ i, π.ker ⊔ K i = H i := fun i => (hdp i).1
  have hKT : ∀ i, K i ≤ T := fun i => (hCK i ▸ le_sup_right).trans (hHT i)
  have hTCL : T ≤ π.ker ⊔ (K 0 ⊔ K 1) := by
    intro x hx
    have hx' : x ∈ ((projRad k 0).comap π : Set X) * ((projRad k 1).comap π : Set X) := by
      rw [hTmul']
      exact hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx'
    have ha' : a ∈ π.ker ⊔ (K 0 ⊔ K 1) := by
      have h : a ∈ π.ker ⊔ K 0 := (hCK 0).symm ▸ ha
      exact (sup_le le_sup_left (le_sup_left.trans le_sup_right) :
        π.ker ⊔ K 0 ≤ π.ker ⊔ (K 0 ⊔ K 1)) h
    have hb' : b ∈ π.ker ⊔ (K 0 ⊔ K 1) := by
      have h : b ∈ π.ker ⊔ K 1 := (hCK 1).symm ▸ hb
      exact (sup_le le_sup_left (le_sup_right.trans le_sup_right) :
        π.ker ⊔ K 1 ≤ π.ker ⊔ (K 0 ⊔ K 1)) h
    exact mul_mem ha' hb'
  have hcentral : ∀ c ∈ π.ker, ∀ g : X, g * c = c * g := fun c hc g =>
    mem_center_iff.1 (hCZ hc) g
  have hTTL : ⁅T, T⁆ ≤ K 0 ⊔ K 1 := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    have hx' := hTCL hx
    have hy' := hTCL hy
    rw [← SetLike.mem_coe, sup_comm, Subgroup.mul_normal] at hx' hy'
    obtain ⟨l, hl, c, hc, rfl⟩ := Set.mem_mul.1 hx'
    obtain ⟨l', hl', c', hc', rfl⟩ := Set.mem_mul.1 hy'
    rw [hcentral c hc l, hcentral c' hc' l',
      commutatorElement_central_mul (hcentral c hc) (hcentral c' hc'), commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hl hl') (inv_mem hl)) (inv_mem hl')
  have hCTT := ker_le_commutator hk hπ hCZ hC
  exact ⟨hCcard, le_antisymm hrank_le hrank_ge,
    le_antisymm (sup_le (hKT 0) (hKT 1)) (hTCL.trans (sup_le (hCTT.trans hTTL) le_rfl))⟩

end Setup

theorem field_four_central_cover_exact_Sylow_geometry
    {k : Type} [Field k] [Finite k] (hk : Nat.card k = 4)
    {X : Type} [Group X] [Finite X] (π : X →* projectiveSL 3 k) (hπ : Function.Surjective π)
    (hCZ : π.ker ≤ center X) (hC : CFSG.IsElementaryAbelian 2 π.ker)
    (σ₁ : SL2 k →* X) (hσ₁ : ∀ B, π (σ₁ B) = leviProj k 0 B) :
    let T := (projUnip k).comap π
    let H : Fin 2 → Subgroup X := fun i => (projRad k i).comap π
    let Z := (projCenterW k).comap π
    let J := (sl2Torus k).map σ₁
    let K : Fin 2 → Subgroup X := fun i => ⁅H i, J⁆
    let Z₀ := ⁅Z, J⁆
    (Nat.card T = 64 * Nat.card π.ker ∧ Monoid.exponent T = 4 ∧
      Z = (center T).map T.subtype ∧ Z = H 0 ⊓ H 1 ∧ Nat.card Z = 4 * Nat.card π.ker ∧
      (∀ M : Subgroup X, (M ≤ T ∧ CFSG.IsElementaryAbelian 2 M ∧
          ∀ E : Subgroup X, M ≤ E → E ≤ T → CFSG.IsElementaryAbelian 2 E → E = M) ↔
        M = H 0 ∨ M = H 1) ∧
      (∀ E : Subgroup X, E ≤ T → CFSG.IsElementaryAbelian 2 E → E ≤ H 0 ∨ E ≤ H 1) ∧
      (∀ x ∈ T, x ^ 2 = 1 ↔ x ∈ H 0 ∨ x ∈ H 1) ∧
      Nat.card {x : X // x ∈ T ∧ orderOf x = 2} = 28 * Nat.card π.ker - 1 ∧
      (∀ i, ∀ x ∈ H i, x ∉ Z → T ⊓ centralizer {x} = H i) ∧
      ∀ x : X, orderOf x = 2 →
        ∃ S : Sylow 2 X, x ∈ (S : Subgroup X) ∧ (S : Subgroup X) ≤ centralizer {x}) ∧
    (Nat.card J = 3 ∧
      normalizer (T : Set X) = normalizer (H 0 : Set X) ⊓ normalizer (H 1 : Set X) ∧
      T ⊔ J = normalizer (T : Set X) ∧ T ⊓ J = ⊥ ∧
      Nat.card (normalizer (T : Set X)) = 192 * Nat.card π.ker ∧
      (∀ i, J ≤ normalizer (H i : Set X)) ∧ J ≤ normalizer (Z : Set X) ∧
      normalizer (T : Set X) ≤ normalizer (Z : Set X) ∧
      (∀ i, ∃ e : K i ≃* projRad k i, ∀ x, (e x : projectiveSL 3 k) = π x) ∧
      (∃ e : Z₀ ≃* projCenterW k, ∀ x, (e x : projectiveSL 3 k) = π x) ∧
      (∀ i, CFSG.Walter.JT.IsInternalDirectProduct π.ker (K i) (H i)) ∧
      CFSG.Walter.JT.IsInternalDirectProduct π.ker Z₀ Z ∧ K 0 ⊓ K 1 = Z₀ ∧
      (∀ i, CFSG.IsElementaryAbelian 2 (K i) ∧ Nat.card (K i) = 16) ∧
      CFSG.IsElementaryAbelian 2 Z₀ ∧ Nat.card Z₀ = 4 ∧
      Z ⊓ centralizer (J : Set X) = π.ker ∧
      ∀ z ∈ Z₀, ∀ z' ∈ Z₀, z ≠ 1 → z' ≠ 1 → ∃ j ∈ J, j * z * j⁻¹ = z') ∧
    (Group.IsPerfect X →
      ⁅T, H 0⁆ = ⁅T, T⁆ ∧ ⁅T, H 1⁆ = ⁅T, T⁆ ∧ ⁅T, T⁆ = (frattini T).map T.subtype ∧
      (frattini T).map T.subtype = (center T).map T.subtype ∧
      CFSG.IsElementaryAbelian 2 (T ⧸ center T) ∧ Nat.card (T ⧸ center T) = 16 ∧
      (Nat.card π.ker = 1 ∨ Nat.card π.ker = 2 ∨ Nat.card π.ker = 4) ∧
      Group.rank T = 4 ∧ K 0 ⊔ K 1 = T) := by
  intro T H Z J K Z₀
  have hprev := field_four_central_two_cover_parabolic_normalizers hk π hπ hCZ hC
  obtain ⟨-, -, -, hTcard, hinf, hcenter, hZcard, -⟩ := hprev
  have hexp := exponent_comap_projUnip hk hπ hCZ hC
  have htwo := sylow_geometry_two hk hπ hCZ hC σ₁ hσ₁
  refine ⟨⟨hTcard, hexp, hcenter.symm, (hinf.trans hcenter).symm, hZcard,
    fun M => isMaximalElementary_iff hk hπ hCZ hC M,
    fun E hET hE => le_or_le_of_isElementaryAbelian hk hπ hCZ hC hET hE,
    fun x hx => sq_eq_one_iff_mem_comap_projRad hk hπ hCZ hC hx,
    card_involutions hk hπ hCZ hC,
    fun i x hx hxZ => inf_centralizer_eq hk hπ hCZ hC i hx hxZ,
    fun x hx => exists_sylow_mem_center hk hπ hCZ hC hx⟩, htwo, fun hperf => ?_⟩
  have h3a := sylow_geometry_three_a hk hπ hCZ hC
  obtain ⟨h1, h2, h3, h4, h5, h6, -, -⟩ := h3a
  have h3b := sylow_geometry_three_b hk hπ hCZ hC σ₁ hσ₁
  obtain ⟨h7, h8, h9⟩ := h3b
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

end CFSG.LocalAnalysis.ComponentInitial.FieldFourCover
