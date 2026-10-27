module

public import CFSG.CGT.Foote82.T66.CaseIBasic
import CFSG.LargeExtraspecial.S5Comp
public import CFSG.CGT.Foote82.T66.CaseIAut

public section

namespace CFSG.CGT.Foote82

namespace CaseIAux

open CFSG.Open CFSG.Quasithin.G11 CFSG.RankThree.PartTwo CFSG.QuasithinUnique
open Equiv Equiv.Perm CaseIPerm

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable {G L H₁ : Subgroup (GLV V)} {z : GLV V} {v : V} {m : ℕ}
  {ψ : ↥H₁ ≃* Equiv.Perm (Fin (m + 6 + 2))}

noncomputable abbrev CU (G : Subgroup (GLV V)) (z : GLV V)
    (ψ : ↥H₁ ≃* Equiv.Perm (Fin (m + 6 + 2))) : Subgroup (GLV V) :=
  centralizerOn G (UU z ψ)

theorem Hyp.H_isComponentOf_CU (h : Hyp G L z v H₁ m ψ) : IsComponentOf (HH G L v) (CU G z ψ) := by
  have hHC : HH G L v ≤ CU G z ψ := fun x hx =>
    ⟨h.H_le_G hx, fun w hw => h.fixes_U (h.H_le_H₁ hx) hw⟩
  have hCv : CU G z ψ ≤ G ⊓ vFix v := fun x hx => ⟨hx.1, hx.2 v h.v_mem_U⟩
  have hsub := h.H_isComponentOf.2.1.inf_of_le hCv
  rw [inf_eq_left.2 hHC] at hsub
  exact ⟨hHC, hsub, h.H_isComponentOf.2.2⟩

theorem Hyp.gg_not_mem_normalizer (h : Hyp G L z v H₁ m ψ) :
    gg ψ ∉ Subgroup.normalizer (L : Set (GLV V)) := by
  intro hg
  set c : Perm (Fin (m + 6 + 2)) := swap 2 4 * swap 4 5 with hc
  have h24 : (2 : Fin (m + 6 + 2)) ≠ 4 := Fin.ne_of_val_ne (show (2 : ℕ) ≠ 4 by decide)
  have h45 : (4 : Fin (m + 6 + 2)) ≠ 5 := Fin.ne_of_val_ne (show (4 : ℕ) ≠ 5 by decide)
  have h25 : (2 : Fin (m + 6 + 2)) ≠ 5 := Fin.ne_of_val_ne (show (2 : ℕ) ≠ 5 by decide)
  have hcA : c ∈ altOn {i : Fin (m + 6 + 2) | i ≠ 0 ∧ i ≠ 1} := by
    refine mem_altOn_iff.2 ⟨?_, fun x hx => ?_⟩
    · rw [Equiv.Perm.mem_alternatingGroup, hc, map_mul, sign_swap h24, sign_swap h45]; rfl
    · simp only [Set.mem_setOf_eq, not_and_or, not_not] at hx
      have h04 : (0 : Fin (m + 6 + 2)) ≠ 4 := Fin.ne_of_val_ne (show (0 : ℕ) ≠ 4 by decide)
      have h05 : (0 : Fin (m + 6 + 2)) ≠ 5 := Fin.ne_of_val_ne (show (0 : ℕ) ≠ 5 by decide)
      have h14 : (1 : Fin (m + 6 + 2)) ≠ 4 := Fin.ne_of_val_ne (show (1 : ℕ) ≠ 4 by decide)
      have h15 : (1 : Fin (m + 6 + 2)) ≠ 5 := Fin.ne_of_val_ne (show (1 : ℕ) ≠ 5 by decide)
      rcases hx with rfl | rfl
      · rw [hc, Perm.mul_apply, swap_apply_of_ne_of_ne h04 h05, swap_apply_of_ne_of_ne ne02 h04]
      · rw [hc, Perm.mul_apply, swap_apply_of_ne_of_ne h14 h15, swap_apply_of_ne_of_ne ne12 h14]
  have hcL : pe ψ c ∈ L := (h.mem_L_iff c).2 hcA
  have hmem : pe ψ c ∈ L.map (MulAut.conj (gg ψ)).toMonoidHom := by
    refine ⟨(gg ψ)⁻¹ * pe ψ c * gg ψ, ?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hg) (pe ψ c)).1 hcL
      rw [inv_inv] at this
      exact this
    · simp [mul_assoc]
  rw [h.conj_L_eq] at hmem
  obtain ⟨σ, hσ, hσc⟩ := hmem
  rw [pe_injective hσc] at hσ
  have h2 : c 2 = 2 := (mem_altOn_iff.1 hσ).2 2 (by simp)
  have h3 : c 2 = 4 := by
    rw [hc, Perm.mul_apply, swap_apply_of_ne_of_ne h24 h25, swap_apply_left]
  exact h24 (h2.symm.trans h3)

theorem Hyp.odd_card_CH (h : Hyp G L z v H₁ m ψ) :
    Odd (Nat.card ↥(G ⊓ Subgroup.centralizer (HH G L v : Set (GLV V)))) := by
  have htight := h.std.tight (gg ψ) h.gg_mem_G h.gg_not_mem_normalizer
  refine Odd.of_dvd_nat htight (Subgroup.card_dvd_of_le ?_)
  rintro x ⟨hxG, hxC⟩
  refine ⟨⟨hxG, Subgroup.centralizer_le h.L_le_H hxC⟩, ?_⟩
  refine ⟨(gg ψ)⁻¹ * x * gg ψ,
    ⟨G.mul_mem (G.mul_mem (G.inv_mem h.gg_mem_G) hxG) h.gg_mem_G, ?_⟩, by simp [mul_assoc]⟩
  refine Subgroup.mem_centralizer_iff.2 fun l hl => ?_
  have hl' : gg ψ * l * (gg ψ)⁻¹ ∈ HH G L v :=
    (HH G L v).mul_mem ((HH G L v).mul_mem h.gg_mem_H (h.L_le_H hl))
      ((HH G L v).inv_mem h.gg_mem_H)
  have := Subgroup.mem_centralizer_iff.1 hxC _ hl'
  calc l * ((gg ψ)⁻¹ * x * gg ψ) = (gg ψ)⁻¹ * ((gg ψ * l * (gg ψ)⁻¹) * x) * gg ψ := by group
    _ = (gg ψ)⁻¹ * (x * (gg ψ * l * (gg ψ)⁻¹)) * gg ψ := by rw [this]
    _ = ((gg ψ)⁻¹ * x * gg ψ) * l := by group

@[expose] noncomputable def jH (ψ : ↥H₁ ≃* Equiv.Perm (Fin (m + 6 + 2))) :
    alternatingGroup (Fin (m + 6 + 2)) →* GLV V :=
  (pe ψ).comp (alternatingGroup (Fin (m + 6 + 2))).subtype

theorem jH_apply (a : alternatingGroup (Fin (m + 6 + 2))) :
    jH ψ a = pe ψ (a : Perm (Fin (m + 6 + 2))) := rfl

theorem jH_injective : Function.Injective (jH ψ) := fun a b hab =>
  Subtype.ext (pe_injective hab)

theorem Hyp.range_jH (h : Hyp G L z v H₁ m ψ) : (jH ψ).range = HH G L v := by
  rw [h.H_eq, jH, MonoidHom.range_comp, Subgroup.range_subtype]

theorem Hyp.exists_thetaH (h : Hyp G L z v H₁ m ψ) :
    ∃ θ : ↥(G ⊓ Subgroup.normalizer (HH G L v : Set (GLV V))) →* Perm (Fin (m + 6 + 2)),
      (∀ (x : ↥(G ⊓ Subgroup.normalizer (HH G L v : Set (GLV V)))) a,
        (x : GLV V) * jH ψ a * (x : GLV V)⁻¹ = jH ψ (CaseIAut.conjA (θ x) a)) ∧
      (∀ x : ↥(G ⊓ Subgroup.normalizer (HH G L v : Set (GLV V))),
        θ x = 1 ↔ ∀ a, (x : GLV V) * jH ψ a = jH ψ a * x) ∧
      (∀ (x : ↥(G ⊓ Subgroup.normalizer (HH G L v : Set (GLV V)))) (hx : (x : GLV V) ∈ H₁),
        θ x = ψ ⟨x, hx⟩) := by
  obtain ⟨θ, hθ⟩ := CaseIAut.exists_theta (m := m + 6 + 2) (by omega) (jH ψ) jH_injective
    (G ⊓ Subgroup.normalizer (HH G L v : Set (GLV V))) fun x hx =>
      CaseIAut.exists_perm_conj_of_ge_seven (Or.inr (by omega)) (jH ψ) jH_injective
        (by rw [h.range_jH]; exact hx.2)
  refine ⟨θ, hθ, CaseIAut.theta_eq_one_iff (by omega) _ jH_injective hθ,
    fun x hx => CaseIAut.theta_eq (by omega) _ jH_injective hθ x fun a => ?_⟩
  rw [jH_apply, jH_apply, CaseIAut.coe_conjA, map_mul, map_mul, map_inv, pe_psi]

theorem Hyp.mem_CH_of_theta (h : Hyp G L z v H₁ m ψ)
    {θ : ↥(G ⊓ Subgroup.normalizer (HH G L v : Set (GLV V))) →* Perm (Fin (m + 6 + 2))}
    (hθ1 : ∀ x, θ x = 1 ↔ ∀ a, (x : GLV V) * jH ψ a = jH ψ a * x)
    (x : ↥(G ⊓ Subgroup.normalizer (HH G L v : Set (GLV V)))) (hx : θ x = 1) :
    (x : GLV V) ∈ G ⊓ Subgroup.centralizer (HH G L v : Set (GLV V)) := by
  refine ⟨x.2.1, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
  rw [← h.range_jH] at hy
  obtain ⟨a, rfl⟩ := hy
  exact ((hθ1 x).1 hx a).symm

theorem eq_one_of_isPGroup_of_odd {Γ : Type*} [Group Γ] {Q K : Subgroup Γ} (hQ : IsPGroup 2 Q)
    (hK : Odd (Nat.card K)) [Finite K] {q : Γ} (hqQ : q ∈ Q) (hqK : q ∈ K) : q = 1 := by
  obtain ⟨k, hk⟩ := hQ ⟨q, hqQ⟩
  have h1 : orderOf (⟨q, hqK⟩ : ↥K) ∣ Nat.card K := orderOf_dvd_natCard _
  have h2 : orderOf (⟨q, hqK⟩ : ↥K) ∣ 2 ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    apply Subtype.ext
    have := congrArg Subtype.val hk
    simpa using this
  have h3 : orderOf (⟨q, hqK⟩ : ↥K) = 1 := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
    rcases j with _ | j
    · simpa using hj
    · have h4 : 2 ∣ Nat.card K :=
        dvd_trans (by rw [hj]; exact dvd_pow_self 2 (Nat.succ_ne_zero j)) h1
      exact absurd h4 (Nat.two_dvd_ne_zero.2 (Nat.odd_iff.1 hK))
  have := orderOf_eq_one_iff.1 h3
  exact congrArg Subtype.val this

theorem Hyp.card_le_of_isPGroup (h : Hyp G L z v H₁ m ψ) {Q : Subgroup (GLV V)}
    (hQ : Q ≤ G ⊓ Subgroup.normalizer (HH G L v : Set (GLV V))) (hQ2 : IsPGroup 2 Q)
    (P : Sylow 2 (Perm (Fin (m + 6 + 2)))) : Nat.card Q ≤ Nat.card P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨θ, -, hθ1, -⟩ := h.exists_thetaH
  let X := G ⊓ Subgroup.normalizer (HH G L v : Set (GLV V))
  let Q' : Subgroup ↥X := Q.subgroupOf X
  let f : ↥Q' →* Perm (Fin (m + 6 + 2)) := θ.comp Q'.subtype
  have hf : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro q hq
    have h1 := h.mem_CH_of_theta hθ1 q (show θ (q : ↥X) = 1 from MonoidHom.mem_ker.1 hq)
    have h2 := eq_one_of_isPGroup_of_odd hQ2 h.odd_card_CH (Subgroup.mem_subgroupOf.1 q.2) h1
    exact Subgroup.mem_bot.2 (Subtype.ext (Subtype.ext h2))
  have hcard1 : Nat.card ↥Q = Nat.card ↥Q' :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ).symm.toEquiv
  have hcard2 : Nat.card ↥Q' = Nat.card f.range :=
    Nat.card_congr (MonoidHom.ofInjective hf).toEquiv
  have hQ'2 : IsPGroup 2 ↥Q' := hQ2.of_equiv (Subgroup.subgroupOfEquivOfLe hQ).symm
  have hR2 : IsPGroup 2 f.range := hQ'2.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  obtain ⟨P', hP'⟩ := hR2.exists_le_sylow
  rw [hcard1, hcard2]
  calc Nat.card f.range ≤ Nat.card P' := Subgroup.card_le_of_le hP'
    _ = Nat.card P := by rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]

theorem Hyp.card_le_two_of_centralizer (h : Hyp G L z v H₁ m ψ) {Q : Subgroup (GLV V)}
    (hQ : Q ≤ G ⊓ Subgroup.normalizer (HH G L v : Set (GLV V)))
    (hQL : Q ≤ Subgroup.centralizer (L : Set (GLV V))) (hQ2 : IsPGroup 2 Q) :
    Nat.card Q ≤ 2 := by
  classical
  obtain ⟨θ, hθ, hθ1, -⟩ := h.exists_thetaH
  let X := G ⊓ Subgroup.normalizer (HH G L v : Set (GLV V))
  let Q' : Subgroup ↥X := Q.subgroupOf X
  let f : ↥Q' →* Perm (Fin (m + 6 + 2)) := θ.comp Q'.subtype
  have hf : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro q hq
    have h1 := h.mem_CH_of_theta hθ1 q (show θ (q : ↥X) = 1 from MonoidHom.mem_ker.1 hq)
    have h2 := eq_one_of_isPGroup_of_odd hQ2 h.odd_card_CH (Subgroup.mem_subgroupOf.1 q.2) h1
    exact Subgroup.mem_bot.2 (Subtype.ext (Subtype.ext h2))
  have hval : ∀ q : ↥Q', f q = 1 ∨ f q = swap 0 1 := by
    intro q
    refine eq_one_or_eq_swap_of_commute_altOn (by omega) ne01 fun σ hσ => ?_
    have hqL : ((q : ↥X) : GLV V) ∈ Subgroup.centralizer (L : Set (GLV V)) :=
      hQL (Subgroup.mem_subgroupOf.1 q.2)
    have hσA : σ ∈ alternatingGroup (Fin (m + 6 + 2)) := (mem_altOn_iff.1 hσ).1
    have h1 := hθ (q : ↥X) ⟨σ, hσA⟩
    have hcomm : ((q : ↥X) : GLV V) * jH ψ ⟨σ, hσA⟩ = jH ψ ⟨σ, hσA⟩ * ((q : ↥X) : GLV V) :=
      (Subgroup.mem_centralizer_iff.1 hqL _ ((h.mem_L_iff σ).2 hσ)).symm
    have h2 : jH ψ ⟨σ, hσA⟩ = jH ψ (CaseIAut.conjA (θ q) ⟨σ, hσA⟩) := by
      rw [← h1, hcomm, mul_inv_cancel_right]
    have h3 := congrArg Subtype.val (jH_injective h2)
    simp only [CaseIAut.coe_conjA] at h3
    show θ q * σ = σ * θ q
    calc θ q * σ = θ q * σ * (θ q)⁻¹ * θ q := by group
      _ = σ * θ q := by rw [← h3]
  have hcard1 : Nat.card ↥Q = Nat.card ↥Q' :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ).symm.toEquiv
  rw [hcard1]
  have hinj : Function.Injective (fun q : ↥Q' => (⟨f q, by
      rcases hval q with h1 | h1 <;> simp [h1]⟩ : ({1, swap 0 1} : Finset (Perm (Fin (m + 6 + 2)))))) :=
    fun q₁ q₂ e => hf (congrArg Subtype.val e)
  have := Nat.card_le_card_of_injective _ hinj
  refine this.trans ?_
  rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  exact Finset.card_le_two

theorem isComponentOf_conj {A K : Subgroup (GLV V)} (hA : IsComponentOf A K) (x : GLV V) :
    IsComponentOf (A.map (MulAut.conj x).toMonoidHom) (K.map (MulAut.conj x).toMonoidHom) := by
  refine ⟨Subgroup.map_mono hA.1, hA.2.1.map _, ?_⟩
  exact CFSG.Open.IsQuasisimple.of_mulEquiv
    (Subgroup.equivMapOfInjective A _ (MulAut.conj x).injective).symm hA.2.2

theorem Hyp.normalizer_U_le (h : Hyp G L z v H₁ m ψ) {x : GLV V} (hxG : x ∈ G)
    (hxU : ∀ w ∈ UU z ψ, x w ∈ UU z ψ) :
    x ∈ Subgroup.normalizer (HH G L v : Set (GLV V)) := by
  have hxU' : ∀ w ∈ UU z ψ, x⁻¹ w ∈ UU z ψ := by
    let f : ↥(UU z ψ) →ₗ[ZMod 2] ↥(UU z ψ) := (x : V →ₗ[ZMod 2] V).restrict hxU
    have hfi : Function.Injective f := fun a b hab => by
      apply Subtype.ext
      have := congrArg Subtype.val hab
      exact x.injective this
    have hfs := LinearMap.injective_iff_surjective.1 hfi
    intro w hw
    obtain ⟨w', hw'⟩ := hfs ⟨w, hw⟩
    have : x (w' : V) = w := congrArg Subtype.val hw'
    rw [← this]
    simpa using w'.2
  have hCU : (CU G z ψ).map (MulAut.conj x).toMonoidHom = CU G z ψ := by
    ext c
    constructor
    · rintro ⟨c, ⟨hcG, hcU⟩, rfl⟩
      refine ⟨G.mul_mem (G.mul_mem hxG hcG) (G.inv_mem hxG), fun w hw => ?_⟩
      show x (c (x⁻¹ w)) = w
      rw [hcU _ (hxU' w hw)]
      exact x.apply_symm_apply w
    · rintro ⟨hcG, hcU⟩
      refine ⟨x⁻¹ * c * x, ⟨G.mul_mem (G.mul_mem (G.inv_mem hxG) hcG) hxG, fun w hw => ?_⟩,
        by simp [mul_assoc]⟩
      show x⁻¹ (c (x w)) = w
      rw [hcU _ (hxU w hw)]
      exact x.symm_apply_apply w
  have hcomp := isComponentOf_conj h.H_isComponentOf_CU x
  rw [hCU] at hcomp
  by_cases heq : (HH G L v).map (MulAut.conj x).toMonoidHom = HH G L v
  · rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [← heq]
      exact ⟨y, hy, rfl⟩
    · intro hy
      rw [← heq] at hy
      obtain ⟨y', hy', hyy'⟩ := hy
      have : y' = y := by
        have := hyy'
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
        exact mul_right_cancel (mul_left_cancel this)
      rw [← this]
      exact hy'
  · exfalso
    have hc := CFSG.LargeExtraspecial.S5.commute_of_isComponentOf_ne h.H_isComponentOf_CU hcomp
      (Ne.symm heq)
    have hle : (HH G L v).map (MulAut.conj x).toMonoidHom ≤
        G ⊓ Subgroup.centralizer (HH G L v : Set (GLV V)) := by
      intro y hy
      refine ⟨?_, ?_⟩
      · obtain ⟨y', hy', rfl⟩ := hy
        exact G.mul_mem (G.mul_mem hxG (h.H_le_G hy')) (G.inv_mem hxG)
      · have hc' : ⁅(HH G L v).map (MulAut.conj x).toMonoidHom, HH G L v⁆ = ⊥ := by
          rw [Subgroup.commutator_comm]; exact hc
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 hc' hy
    have hodd := Odd.of_dvd_nat h.odd_card_CH (Subgroup.card_dvd_of_le hle)
    rw [← Nat.card_congr (Subgroup.equivMapOfInjective _ _ (MulAut.conj x).injective).toEquiv]
      at hodd
    have hu : pe ψ (swap 0 1 * swap 2 3) ∈ HH G L v := (h.mem_H_iff _).2 (by
      rw [Equiv.Perm.mem_alternatingGroup, map_mul, sign_swap ne01, sign_swap ne23]; rfl)
    have hord : orderOf (⟨_, hu⟩ : ↥(HH G L v)) = 2 := by
      rw [Subgroup.orderOf_mk, orderOf_injective (pe ψ) pe_injective]
      exact orderOf_swap_mul_swap ne01 ne02 ne03 ne12 ne13 ne23
    have h2 : 2 ∣ Nat.card ↥(HH G L v) := by
      have := orderOf_dvd_natCard (⟨_, hu⟩ : ↥(HH G L v))
      rwa [hord] at this
    exact absurd h2 (by rw [Nat.two_dvd_ne_zero, ← Nat.odd_iff]; exact hodd)

end CaseIAux

end CFSG.CGT.Foote82
