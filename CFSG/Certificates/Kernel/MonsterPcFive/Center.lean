module

public import CFSG.Certificates.Kernel.MonsterPcFive.Card

public section

namespace CFSG.KC.MonPcFive

open Subgroup

variable {G : Type*} [Group G] {u2 u1 : G} {b : Fin 6 → G} {x : G}

theorem sig_eq_zero (hs : sigOK () = true) {i j : ℕ} (hi : i < 5) (hj : j < 5)
    (h : sig i j = sig 0 0) : i = 0 ∧ j = 0 := by
  have hp : 5 * i + j = 0 := by
    by_contra hne
    have := allBelow_spec (allBelow_spec hs (5 * i + j) (by omega)) 0 (by omega)
    have e3 : (5 * i + j) / 5 = i := by omega
    have e4 : (5 * i + j) % 5 = j := by omega
    rw [e3, e4, Nat.zero_div, Nat.zero_mod, h, Nat.beq_refl] at this
    exact absurd this (by decide)
  omega

theorem PcHyp.mem_zpowers_of_central [Finite G] (H : PcHyp u2 u1 b x) (C : TabChecks)
    (hs : sigOK () = true) (hx : x ≠ 1) {c : G} (hc : c ∈ PSub u2 u1 b)
    (hcen : ∀ y ∈ PSub u2 u1 b, c * y = y * c) : c ∈ zpowers x := by
  have D := H.rel.commData hx
  have : NeZero 5 := ⟨by norm_num⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hR : closure (Set.range b) ≤ PSub u2 u1 b :=
    closure_mono (fun _ hy => Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ hy))
  obtain ⟨n, -, rfl⟩ := mem_P_psi H C hc
  obtain ⟨he0, he1, -⟩ := dec_red n
  set v := dec n
  set U := u2 ^ v.e0 * u1 ^ v.e1
  set r := nfR b x v.r
  have hrm : r ∈ closure (Set.range b) := nfR_mem H.rel _
  have hpsi : psi u2 u1 b x v = U * r := rfl
  rw [hpsi] at hcen ⊢
  have hrow : ∀ k < 6, ∀ l, (actRow v.e0 v.e1 k).digs l = (actRow 0 0 k).digs l := by
    intro k hk l
    have c1 := H.conj_U C he0 he1 ⟨k, hk⟩
    have hbk : b ⟨k, hk⟩ ∈ closure (Set.range b) := subset_closure ⟨_, rfl⟩
    have hcb := hcen _ (hR hbk)
    have e : U⁻¹ * b ⟨k, hk⟩ * U = r⁻¹⁻¹ * b ⟨k, hk⟩ * r⁻¹ := by
      calc U⁻¹ * b ⟨k, hk⟩ * U = U⁻¹ * (b ⟨k, hk⟩ * (U * r)) * r⁻¹ := by group
        _ = U⁻¹ * (U * r * b ⟨k, hk⟩) * r⁻¹ := by rw [hcb]
        _ = r⁻¹⁻¹ * b ⟨k, hk⟩ * r⁻¹ := by group
    have e00 : b ⟨k, hk⟩ = nfR b x (actRow 0 0 k) := (nfR_unitR (b := b) (x := x) ⟨k, hk⟩).symm
    have hcd := D.coord_conj_of_mem (inv_mem hrm) hbk
    rw [← e, c1, coord_nfR H.rel hx (actRow_red _ _ _)] at hcd
    rw [e00, coord_nfR H.rel hx (actRow_red _ _ _)] at hcd
    have hl := congrFun hcd l
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (digs_lt (actRow_red _ _ _) l),
      Nat.mod_eq_of_lt (digs_lt (actRow_red _ _ _) l)] at hl
    exact hl
  have hsig : sig v.e0 v.e1 = sig 0 0 := by
    unfold sig
    rw [encA_congr (hrow 0 (by norm_num)), encA_congr (hrow 1 (by norm_num)),
      encA_congr (hrow 2 (by norm_num)), encA_congr (hrow 3 (by norm_num)),
      encA_congr (hrow 4 (by norm_num)), encA_congr (hrow 5 (by norm_num))]
  obtain ⟨h0, h1⟩ := sig_eq_zero hs he0 he1 hsig
  have hU : U = 1 := by
    change u2 ^ v.e0 * u1 ^ v.e1 = 1
    rw [h0, h1, pow_zero, pow_zero, mul_one]
  rw [hU, one_mul] at hcen ⊢
  have hker : (⟨r, hrm⟩ : closure (Set.range b)) ∈ D.psiHom.ker := by
    rw [MonoidHom.mem_ker, CFSG.Monster.B.Pinned.CommData.psiHom_apply]
    have e : CFSG.Monster.B.Pinned.psi 5 b x r = 0 := by
      funext j
      have hcj : r * b j = b j * r := hcen _ (hR (subset_closure ⟨j, rfl⟩))
      simp only [CFSG.Monster.B.Pinned.psi, Pi.zero_apply]
      rw [CFSG.Monster.B.Pinned.bcomm_eq_one_iff.2 hcj,
        CFSG.Monster.B.Pinned.lg_one D.orderOf_z]
    rw [e, ofAdd_zero]
  rw [D.ker_psiHom] at hker
  exact mem_subgroupOf.1 hker

end CFSG.KC.MonPcFive

end
