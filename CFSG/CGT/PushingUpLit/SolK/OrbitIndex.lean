module

public import CFSG.CGT.PushingUpLit.SolK.Delta

public section

namespace CFSG.CGT.PushingUpLit.SolK

open CFSG CFSG.Assembly CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.BHS CFSG.Quasithin
  CFSG.Quasithin.G6 Equiv Equiv.Perm

theorem exists_alt_perm_of_card_eq {d : ℕ} {B₁ B₂ : Finset (Fin d)} (h : B₁.card = B₂.card)
    (h1 : B₁.card ≠ 1) :
    ∃ σ : Perm (Fin d), σ ∈ alternatingGroup (Fin d) ∧ ∀ x, σ x ∈ B₂ ↔ x ∈ B₁ := by
  classical
  by_cases h0 : B₁.card = 0
  · have hB₁ : B₁ = ∅ := Finset.card_eq_zero.1 h0
    have hB₂ : B₂ = ∅ := Finset.card_eq_zero.1 (by rw [← h]; exact h0)
    refine ⟨1, one_mem _, fun x => ?_⟩
    simp [hB₁, hB₂]
  · have hc : 1 < B₁.card := by omega
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 hc
    let e : {x // x ∈ B₁} ≃ {x // x ∈ B₂} := Finset.equivOfCardEq h
    set σ₀ : Perm (Fin d) := Equiv.extendSubtype e with hσ₀def
    have hσ₀ : ∀ x, σ₀ x ∈ B₂ ↔ x ∈ B₁ := fun x => by
      constructor
      · intro hx
        by_contra hxn
        exact Equiv.extendSubtype_not_mem e x hxn hx
      · intro hx
        exact Equiv.extendSubtype_mem e x hx
    by_cases hsign : Perm.sign σ₀ = 1
    · exact ⟨σ₀, Equiv.Perm.mem_alternatingGroup.2 hsign, hσ₀⟩
    · refine ⟨σ₀ * swap a b, ?_, fun x => ?_⟩
      · rw [Equiv.Perm.mem_alternatingGroup, map_mul, Equiv.Perm.sign_swap hab]
        rcases Int.units_eq_one_or (Perm.sign σ₀) with h' | h'
        · exact absurd h' hsign
        · rw [h']
          decide
      · rw [Equiv.Perm.mul_apply, hσ₀]
        rw [Equiv.swap_apply_def]
        split_ifs with h1 h2
        · subst h1
          exact ⟨fun _ => ha, fun _ => hb⟩
        · subst h2
          exact ⟨fun _ => hb, fun _ => ha⟩
        · exact Iff.rfl

theorem card_vsupp_coreAct {d : ℕ} (σ : Perm (Fin d)) (v : ↥(coreMod d)) :
    (vsupp (coreAct d σ v)).card = (vsupp v).card := by
  classical
  refine Finset.card_bij (fun i _ => σ⁻¹ i) (fun i hi => ?_) (fun i _ j _ h => σ⁻¹.injective h)
    (fun j hj => ?_)
  · rw [mem_vsupp, vcoord_coreAct] at hi
    exact mem_vsupp.2 hi
  · refine ⟨σ j, ?_, by simp⟩
    rw [mem_vsupp, vcoord_coreAct]
    simpa using mem_vsupp.1 hj

@[expose] def vecOfSupp {d : ℕ} (A : Finset (Fin d)) (hA : Even A.card) : ↥(coreMod d) :=
  mkEven (fun i => if i ∈ A then 1 else 0) (by
    classical
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]
    exact (ZMod.natCast_eq_zero_iff_even).2 hA)

theorem vsupp_vecOfSupp {d : ℕ} (A : Finset (Fin d)) (hA : Even A.card) :
    vsupp (vecOfSupp A hA) = A := by
  classical
  ext i
  rw [mem_vsupp, vecOfSupp, vcoord_mkEven]
  by_cases hi : i ∈ A <;> simp [hi]

theorem eq_of_vsupp_eq {d : ℕ} {u v : ↥(coreMod d)} (h : vsupp u = vsupp v) : u = v := by
  refine vcoord_ext fun i => ?_
  have h3 : i ∈ vsupp u ↔ i ∈ vsupp v := by rw [h]
  simp only [mem_vsupp] at h3
  generalize vcoord u i = a at h3 ⊢
  generalize vcoord v i = b at h3 ⊢
  revert a b
  decide

theorem card_vecs_of_card {d l : ℕ} (hl : Even l) :
    Nat.card {v : ↥(coreMod d) // (vsupp v).card = l} = d.choose l := by
  classical
  have hev : ∀ A : ↥((Finset.univ : Finset (Fin d)).powersetCard l), Even A.1.card := fun A => by
    rw [(Finset.mem_powersetCard.1 A.2).2]
    exact hl
  let e : {v : ↥(coreMod d) // (vsupp v).card = l} ≃
      ↥((Finset.univ : Finset (Fin d)).powersetCard l) :=
    { toFun := fun v => ⟨vsupp v.1, Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, v.2⟩⟩
      invFun := fun A => ⟨vecOfSupp A.1 (hev A), by
          rw [vsupp_vecOfSupp]
          exact (Finset.mem_powersetCard.1 A.2).2⟩
      left_inv := fun v => Subtype.ext (eq_of_vsupp_eq (by rw [vsupp_vecOfSupp]))
      right_inv := fun A => Subtype.ext (by simp only [vsupp_vecOfSupp]) }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe, Finset.card_powersetCard,
    Finset.card_univ, Fintype.card_fin]

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {n : ℕ} (S : SolCfg G M X n)

namespace SolCfg

include S

theorem exists_theta_eq_iff (v₀ v : ↥(coreMod (2 * n + 1))) :
    (∃ m : ↥M, coreAct (2 * n + 1) (S.θ m) v₀ = v) ↔ (vsupp v).card = (vsupp v₀).card := by
  classical
  constructor
  · rintro ⟨m, rfl⟩
    exact card_vsupp_coreAct _ _
  · intro hv
    have hne : (vsupp v₀).card ≠ 1 := by
      intro h1
      have := even_card_vsupp v₀
      rw [h1] at this
      exact absurd this (by decide)
    obtain ⟨σ, hσ, hσs⟩ := exists_alt_perm_of_card_eq hv.symm hne
    obtain ⟨c, hcM, hcσ⟩ := S.exists_lift_J hσ
    refine ⟨⟨c, hcM⟩, ?_⟩
    rw [hcσ]
    refine eq_of_vsupp_eq ?_
    ext i
    rw [mem_vsupp, vcoord_coreAct, ← mem_vsupp, ← hσs (σ⁻¹ i)]
    simp

theorem card_eq_choose_mul_card (hR : RSmall S) {w r : G} (hw : w ∈ S.D.W) (hr : r ∈ rOf M X) :
    Nat.card ↥M = (2 * n + 1).choose (vsupp (S.D.β ⟨w, hw⟩)).card *
      Nat.card ↥(CMOf M (w * r)) := by
  classical
  let _ : MulAction ↥M ↥(coreMod (2 * n + 1)) :=
    MulAction.compHom ↥(coreMod (2 * n + 1)) ((coreAct (2 * n + 1)).comp S.θ)
  set v₀ : ↥(coreMod (2 * n + 1)) := S.D.β ⟨w, hw⟩ with hv₀
  have hstab : MulAction.stabilizer ↥M v₀ = (CMOf M (w * r)).subgroupOf M := by
    ext m
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have hfix : coreAct (2 * n + 1) (S.θ m) v₀ = v₀ := h
      have hw' : (m : G) * w * (m : G)⁻¹ ∈ S.D.W := S.W_normalized m.2 hw
      have h1 := S.θ_spec m ⟨w, hw⟩ hw'
      rw [← hv₀, hfix] at h1
      have h2 : (m : G) * w * (m : G)⁻¹ = w :=
        congrArg Subtype.val (S.D.β.injective h1)
      have h3 := SolCfg.RSmall.central S hR m.2 hr
      refine Subgroup.mem_inf.2 ⟨m.2, mem_centralizer_zpowers_iff.2 ?_⟩
      calc (m : G) * (w * r) * (m : G)⁻¹ =
          ((m : G) * w * (m : G)⁻¹) * ((m : G) * r * (m : G)⁻¹) := by group
        _ = w * r := by rw [h2, h3]
    · intro h
      exact S.fix_of_comm hw hr m (mem_centralizer_zpowers_iff.1 (Subgroup.mem_inf.1 h).2)
  have hidx : ((CMOf M (w * r)).subgroupOf M).index =
      (2 * n + 1).choose (vsupp v₀).card := by
    have horb : MulAction.orbit ↥M v₀ = {v | (vsupp v).card = (vsupp v₀).card} := by
      ext v
      rw [MulAction.mem_orbit_iff, Set.mem_ofPred_eq, ← S.exists_theta_eq_iff]
      rfl
    rw [← hstab, MulAction.index_stabilizer, horb, ← Nat.card_coe_set_eq]
    exact card_vecs_of_card (even_card_vsupp v₀)
  have h1 := Subgroup.card_mul_index ((CMOf M (w * r)).subgroupOf M)
  have h2 : Nat.card ↥((CMOf M (w * r)).subgroupOf M) = Nat.card ↥(CMOf M (w * r)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [h2, hidx] at h1
  rw [← h1, mul_comm]

end SolCfg

end CFSG.CGT.PushingUpLit.SolK
