module

public import CFSG.CGT.PushingUpLit.SolK.Length

public section

namespace CFSG.CGT.PushingUpLit.SolK

open CFSG CFSG.Assembly CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.BHS CFSG.Quasithin
  CFSG.Quasithin.G6 Equiv Equiv.Perm
open scoped commutatorElement

abbrev TOf {G : Type} [Group G] (M : Subgroup G) (x : G) : Subgroup G :=
  pCoreOf 2 (M ⊓ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G))

section Basic

variable {G : Type} [Group G] (M : Subgroup G) (x : G)

theorem TOf_le_C : TOf M x ≤ M ⊓ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) :=
  pCoreOf_le_self _

theorem TOf_le_M : TOf M x ≤ M := (TOf_le_C M x).trans inf_le_left

theorem isPGroup_TOf : IsPGroup 2 (TOf M x) := isPGroup_pCoreOf' _

theorem normalized_TOf {c t : G}
    (hc : c ∈ M ⊓ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G))
    (ht : t ∈ TOf M x) : c * t * c⁻¹ ∈ TOf M x :=
  pCoreOf_normalized _ hc ht

end Basic

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {n : ℕ} (S : SolCfg G M X n)

noncomputable def SolCfg.thetaN (x : G) : Subgroup (Perm (Fin (2 * n + 1))) :=
  ((TOf M x).subgroupOf M).map S.θ

namespace SolCfg

include S

theorem mem_thetaN {x : G} {σ : Perm (Fin (2 * n + 1))} :
    σ ∈ S.thetaN x ↔ ∃ t : ↥M, (t : G) ∈ TOf M x ∧ S.θ t = σ := by
  unfold SolCfg.thetaN
  rw [Subgroup.mem_map]
  exact ⟨fun ⟨t, ht, h⟩ => ⟨t, ht, h⟩, fun ⟨t, ht, h⟩ => ⟨t, ht, h⟩⟩

theorem isPGroup_thetaN (x : G) : IsPGroup 2 (S.thetaN x) := by
  have h2 : IsPGroup 2 ↥((TOf M x).subgroupOf M) :=
    (isPGroup_TOf M x).of_equiv (Subgroup.subgroupOfEquivOfLe (TOf_le_M M x)).symm
  exact h2.map S.θ

theorem thetaN_le_setStab {w r : G} (hw : w ∈ S.D.W) (hr : r ∈ rOf M X) :
    S.thetaN (w * r) ≤ setStab (vsupp (S.D.β ⟨w, hw⟩)) := by
  intro σ hσ
  obtain ⟨t, ht, rfl⟩ := S.mem_thetaN.1 hσ
  have htC := TOf_le_C M (w * r) ht
  have hcomm : (t : G) * (w * r) * (t : G)⁻¹ = w * r :=
    mem_centralizer_zpowers_iff.1 (Subgroup.mem_inf.1 htC).2
  exact (coreAct_eq_iff _ _).1 (S.fix_of_comm hw hr t hcomm)

theorem thetaN_normalized {w r : G} (hw : w ∈ S.D.W) (hr : r ∈ rOf M X)
    {τ : Perm (Fin (2 * n + 1))} (hτ : τ ∈ alternatingGroup (Fin (2 * n + 1)))
    (hτI : τ ∈ setStab (vsupp (S.D.β ⟨w, hw⟩))) :
    ∀ σ ∈ S.thetaN (w * r), τ * σ * τ⁻¹ ∈ S.thetaN (w * r) := by
  intro σ hσ
  obtain ⟨c, hcτ⟩ := S.D.ρ_surj τ hτ
  have hfix : coreAct (2 * n + 1) (S.D.ρ c) (S.D.β ⟨w, hw⟩) = S.D.β ⟨w, hw⟩ := by
    rw [hcτ]
    exact (coreAct_eq_iff _ _).2 hτI
  have hcx := S.comm_of_fix_X hw hr c hfix
  have hcM : (c : G) ∈ M := S.hyp.le c.2
  have hcC : (c : G) ∈ M ⊓ Subgroup.centralizer ((Subgroup.zpowers (w * r) : Subgroup G) : Set G) :=
    Subgroup.mem_inf.2 ⟨hcM, mem_centralizer_zpowers_iff.2 hcx⟩
  obtain ⟨t, ht, rfl⟩ := S.mem_thetaN.1 hσ
  have hcmT : (c : G) * (t : G) * (c : G)⁻¹ ∈ TOf M (w * r) := normalized_TOf M (w * r) hcC ht
  refine S.mem_thetaN.2 ⟨⟨(c : G) * (t : G) * (c : G)⁻¹, TOf_le_M M _ hcmT⟩, hcmT, ?_⟩
  have hθc : S.θ ⟨(c : G), hcM⟩ = τ := by rw [S.θ_X c]; exact hcτ
  have : (⟨(c : G) * (t : G) * (c : G)⁻¹, TOf_le_M M _ hcmT⟩ : ↥M) =
      ⟨(c : G), hcM⟩ * t * ⟨(c : G), hcM⟩⁻¹ := rfl
  rw [this, map_mul, map_mul, map_inv, hθc]

theorem card_eq_card_inf_mul (hT : TightData S) {U : Subgroup G} (hUM : U ≤ M)
    (hU2 : IsPGroup 2 U) :
    Nat.card U = Nat.card ↥(U ⊓ pCoreOf 2 M) * Nat.card ↥((U.subgroupOf M).map S.θ) := by
  classical
  let U' : Subgroup ↥M := U.subgroupOf M
  let f : ↥U' →* Perm (Fin (2 * n + 1)) := S.θ.comp U'.subtype
  have h1 := Subgroup.card_ker_mul_card_range f
  have hU' : Nat.card ↥U' = Nat.card U := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv
  have hrange : Nat.card f.range = Nat.card ↥(U'.map S.θ) := by
    congr 2
    ext σ
    simp only [MonoidHom.mem_range, Subgroup.mem_map, f, MonoidHom.comp_apply,
      Subgroup.coe_subtype]
    exact ⟨fun ⟨k, hk⟩ => ⟨k, k.2, hk⟩, fun ⟨m, hm, hk⟩ => ⟨⟨m, hm⟩, hk⟩⟩
  have hker : Nat.card f.ker = Nat.card ↥(U ⊓ pCoreOf 2 M) := by
    refine Nat.card_congr (Equiv.ofBijective (fun k => ⟨((k : ↥U' ) : ↥M).1, ?_⟩) ⟨?_, ?_⟩)
    ·
      refine Subgroup.mem_inf.2 ⟨k.1.2, ?_⟩
      have hk1 : S.θ (k.1 : ↥M) = 1 := k.2
      obtain ⟨j, hj⟩ := hU2 ⟨((k.1 : ↥M) : G), k.1.2⟩
      exact hT.ker_two (k.1 : ↥M) hk1 ⟨j, by simpa using congrArg Subtype.val hj⟩
    · intro k k' h
      have := congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext (Subtype.ext this))
    · intro u
      have hu := u.2
      have huM : (u : G) ∈ M := hUM (Subgroup.mem_inf.1 hu).1
      refine ⟨⟨⟨⟨(u : G), huM⟩, (Subgroup.mem_inf.1 hu).1⟩, ?_⟩, rfl⟩
      exact (theta_eq_one_iff S.D S.xnorm S.hyp.two_le ⟨(u : G), huM⟩).2 fun w hw =>
        mul_inv_eq_iff_eq_mul.2 (S.q_comm_W (Subgroup.mem_inf.1 hu).2 hw)
  rw [hker, hrange, hU'] at h1
  exact h1.symm

end SolCfg

end CFSG.CGT.PushingUpLit.SolK
