module

public import CFSG.GH74.Generic.S45.PumpA2
public import CFSG.GH74.Generic.S45.NoNormalThree

public section

namespace CFSG.GH74.Generic.S45

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.ABGLocalTools Subgroup

section C

theorem key3 : ∀ c : ℕ, c ∣ 16 → 16 ≡ c [MOD 3] → 4 ≤ c → c ≠ 16 → c = 4 := by
  intro c h2 h1 h4 h16
  have hle : c ≤ 16 := Nat.le_of_dvd (by norm_num) h2
  unfold Nat.ModEq at h1
  interval_cases c <;> omega

variable {G : Type} [Group G] [Finite G] {x : G} {K : Subgroup (CentralizerBar x)} {T : Subgroup G}

theorem card_stabilizer_eq_of_subgroup {T : Type} [Group T] (A B : Subgroup (MulAut T)) (x : T)
    (hBx : ∀ f ∈ B, f x = x) (hAB : ∀ f ∈ A, f x = x → f ∈ B) (hBA : B ≤ A) :
    Nat.card (MulAction.stabilizer (↥A) x) = Nat.card B := by
  apply Nat.card_congr
  refine ⟨fun f => ⟨(f.1 : MulAut T), ?_⟩, fun f => ⟨⟨f.1, hBA f.2⟩, ?_⟩, ?_, ?_⟩
  · exact hAB _ f.1.2 f.2
  · exact hBx _ f.2
  · intro f; rfl
  · intro f; rfl

theorem S45Conf.card_orbit_v_Ax (h : S45Conf x K T) {v : ↥T} (hv : (v : G) ∈ Pre x K) (hv1 : v ≠ 1) :
    Nat.card (MulAction.orbit ↥(T.normalizerMonoidHom.range ⊓
      MulAction.stabilizer (MulAut ↥T) (⟨x, h.x_mem⟩ : ↥T)) v) = 7 := by
  have hset : (MulAction.orbit ↥(T.normalizerMonoidHom.range ⊓
      MulAction.stabilizer (MulAut ↥T) (⟨x, h.x_mem⟩ : ↥T)) v : Set ↥T) =
      {y : ↥T | (y : G) ∈ Pre x K ∧ y ≠ 1} := by
    ext y
    constructor
    · rintro ⟨f, rfl⟩
      refine ⟨h.autG_mem_R f.2.1 hv, ?_⟩
      intro h1
      apply hv1
      have : (f : MulAut ↥T) v = (f : MulAut ↥T) 1 := by rw [map_one]; exact h1
      exact (f : MulAut ↥T).injective this
    · rintro ⟨hy, hy1⟩
      obtain ⟨f, hf, hfv⟩ := h.exists_autGx_apply_eq hv hy hv1 hy1
      exact ⟨⟨f, hf⟩, hfv⟩
  rw [hset, Nat.card_coe_set_eq]
  exact h.ncard_R_ne_one

theorem S45Conf.card_Bv (h : S45Conf x K T) {v : ↥T} (hv : (v : G) ∈ Pre x K) (hv1 : v ≠ 1) :
    Nat.card ↥((T.normalizerMonoidHom.range ⊓
      MulAction.stabilizer (MulAut ↥T) (⟨x, h.x_mem⟩ : ↥T)) ⊓ MulAction.stabilizer (MulAut ↥T) v) = 3 := by
  have h1 := orbit_card (T.normalizerMonoidHom.range ⊓
      MulAction.stabilizer (MulAut ↥T) (⟨x, h.x_mem⟩ : ↥T))
    ((T.normalizerMonoidHom.range ⊓
      MulAction.stabilizer (MulAut ↥T) (⟨x, h.x_mem⟩ : ↥T)) ⊓ MulAction.stabilizer (MulAut ↥T) v) v
    (fun f hf => MulAction.mem_stabilizer_iff.1 hf.2)
    (fun f hf hfv => ⟨hf, MulAction.mem_stabilizer_iff.2 hfv⟩) inf_le_left
  rw [h.card_orbit_v_Ax hv hv1, h.card_autGx] at h1
  omega

theorem S45Conf.fix_three (h : S45Conf x K T) {v : ↥T} (hv : (v : G) ∈ Pre x K) (hv1 : v ≠ 1)
    {c : MulAut ↥T} (hcA : c ∈ T.normalizerMonoidHom.range)
    (hcx : c (⟨x, h.x_mem⟩ : ↥T) = ⟨x, h.x_mem⟩) (hcv : c v = v) (hc1 : c ≠ 1) :
    ∀ s : ↥T, c s = s → s = 1 ∨ s = ⟨x, h.x_mem⟩ ∨ s = v ∨ s = ⟨x, h.x_mem⟩ * v := by
  classical
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  set xT : ↥T := ⟨x, h.x_mem⟩ with hxT
  have hBv := h.card_Bv hv hv1
  have hcmem : c ∈ (T.normalizerMonoidHom.range ⊓ MulAction.stabilizer (MulAut ↥T) xT) ⊓
      MulAction.stabilizer (MulAut ↥T) v :=
    ⟨⟨hcA, MulAction.mem_stabilizer_iff.2 hcx⟩, MulAction.mem_stabilizer_iff.2 hcv⟩
  have hc3 : orderOf c = 3 := by
    have h1 : orderOf (⟨c, hcmem⟩ : ↥((T.normalizerMonoidHom.range ⊓
        MulAction.stabilizer (MulAut ↥T) xT) ⊓ MulAction.stabilizer (MulAut ↥T) v)) ∣ 3 :=
      hBv ▸ orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    rcases (Nat.dvd_prime Fact.out).1 h1 with h2 | h2
    · exact absurd (orderOf_eq_one_iff.1 h2) hc1
    · exact h2
  have hT16 : Nat.card ↥T = 16 := h.card
  have hxnot : (xT : G) ∉ Pre x K := (h.fusion x h.x_mem).1 ⟨1, by simp⟩
  have hxT1 : xT ≠ 1 := by
    intro h1
    have : (xT : G) = 1 := congrArg Subtype.val h1
    exact hxnot (this ▸ one_mem (Pre x K))
  have hvne : xT ≠ v := by
    intro h1
    exact hxnot (h1 ▸ hv)
  have hxv1 : xT * v ≠ 1 := by
    intro h1
    have h2 : (xT : G) * (v : G) = 1 := congrArg Subtype.val h1
    have h3 : (xT : G) = ((v : G))⁻¹ := eq_inv_of_mul_eq_one_left h2
    exact hxnot (h3 ▸ inv_mem hv)
  have hxvx : xT * v ≠ xT := by
    intro h1
    exact hv1 (mul_eq_left.1 h1)
  have hxvv : xT * v ≠ v := by
    intro h1
    exact hxT1 (mul_eq_right.1 h1)
  set F : Subgroup ↥T := fixSub (zpowers c) with hF
  have hFx : xT ∈ F := fix_mem_zpowers hcx
  have hFv : v ∈ F := fix_mem_zpowers hcv
  have hFxv : xT * v ∈ F := F.mul_mem hFx hFv
  have hmod := card_fixSub_modEq c 3 hc3
  rw [hT16] at hmod
  have hdvd : Nat.card F ∣ 16 := hT16 ▸ Subgroup.card_subgroup_dvd_card F
  have hne16 : Nat.card F ≠ 16 := by
    intro h16
    have htop : F = ⊤ := by
      rw [← Subgroup.card_eq_iff_eq_top, hT16]
      exact h16
    exact hc1 (fix_eq_top_imp_one c htop)
  have hPcard : ({1, xT, v, xT * v} : Finset ↥T).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [hxT1.symm, hv1.symm, hxv1.symm]),
      Finset.card_insert_of_notMem (by simp [hvne, hxvx.symm]),
      Finset.card_insert_of_notMem (by simp [hxvv.symm]), Finset.card_singleton]
  have hsub : ((({1, xT, v, xT * v} : Finset ↥T)) : Set ↥T) ⊆ (F : Set ↥T) := by
    intro s hs
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · exact F.one_mem
    · exact hFx
    · exact hFv
    · exact hFxv
  have hFcard : (F : Set ↥T).ncard = Nat.card F := (Nat.card_coe_set_eq (F : Set ↥T)).symm
  have hge : 4 ≤ Nat.card F := by
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_coe_finset, hPcard, hFcard] at h1
    exact h1
  have h4 : Nat.card F = 4 := key3 _ hdvd hmod hge hne16
  have heq := Set.eq_of_subset_of_ncard_le hsub (by
    rw [Set.ncard_coe_finset, hPcard, hFcard, h4])
  intro s hs
  have hsF : s ∈ (F : Set ↥T) := fix_mem_zpowers hs
  rw [← heq] at hsF
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hsF
  exact hsF

omit [Finite G] in
theorem S45Conf.autG_mem_compl_R (h : S45Conf x K T) {f : MulAut ↥T}
    (hf : f ∈ T.normalizerMonoidHom.range) {y : ↥T} (hy : (y : G) ∉ Pre x K) :
    ((f y : ↥T) : G) ∉ Pre x K := by
  intro hfy
  apply hy
  have := h.autG_mem_R (inv_mem hf) hfy
  simpa using this

theorem S45Conf.false_of_subnormal_autGv (h : S45Conf x K T) {v : ↥T} (hv : (v : G) ∈ Pre x K) (hv1 : v ≠ 1)
    (M : Subgroup ↥(T.normalizerMonoidHom.range ⊓ MulAction.stabilizer (MulAut ↥T) v))
    (hM : M.IsSubnormal) (hM1 : M ≠ ⊥)
    (hMx : ∀ f ∈ M, (f : MulAut ↥T) (⟨x, h.x_mem⟩ : ↥T) = ⟨x, h.x_mem⟩) : False := by
  have hxnot : ((⟨x, h.x_mem⟩ : ↥T) : G) ∉ Pre x K := (h.fusion x h.x_mem).1 ⟨1, by simp⟩
  have hstab : Nat.card (MulAction.stabilizer
      ↥(T.normalizerMonoidHom.range ⊓ MulAction.stabilizer (MulAut ↥T) v) (⟨x, h.x_mem⟩ : ↥T)) = 3 := by
    rw [card_stabilizer_eq_of_subgroup
      (T.normalizerMonoidHom.range ⊓ MulAction.stabilizer (MulAut ↥T) v)
      ((T.normalizerMonoidHom.range ⊓ MulAction.stabilizer (MulAut ↥T) v) ⊓
        MulAction.stabilizer (MulAut ↥T) (⟨x, h.x_mem⟩ : ↥T)) (⟨x, h.x_mem⟩ : ↥T)
      (fun f hf => MulAction.mem_stabilizer_iff.1 hf.2)
      (fun f hf hfx => ⟨hf, MulAction.mem_stabilizer_iff.2 hfx⟩) inf_le_left]
    have : (T.normalizerMonoidHom.range ⊓ MulAction.stabilizer (MulAut ↥T) v) ⊓
        MulAction.stabilizer (MulAut ↥T) (⟨x, h.x_mem⟩ : ↥T) =
        (T.normalizerMonoidHom.range ⊓ MulAction.stabilizer (MulAut ↥T) (⟨x, h.x_mem⟩ : ↥T)) ⊓
          MulAction.stabilizer (MulAut ↥T) v := inf_right_comm _ _ _
    rw [this]
    exact h.card_Bv hv hv1
  refine no_subnormal_three_of_fix
    (H := ↥(T.normalizerMonoidHom.range ⊓ MulAction.stabilizer (MulAut ↥T) v)) (X := ↥T)
    (h.card_autGv hv hv1) (⟨x, h.x_mem⟩ : ↥T) ((⟨x, h.x_mem⟩ : ↥T) * v)
    {y : ↥T | (y : G) ∉ Pre x K} ?_ hxnot ?_ hstab M hM hM1 hMx
  · intro g s hs
    exact h.autG_mem_compl_R g.2.1 hs
  · intro c hc1 hcx s hs hcs
    have hc1' : (c : MulAut ↥T) ≠ 1 := fun h1 => hc1 (Subtype.ext h1)
    have h2 := h.fix_three hv hv1 c.2.1 hcx c.2.2 hc1' s hcs
    rcases h2 with h2 | h2 | h2 | h2
    · exact absurd (h2 ▸ one_mem (Pre x K)) hs
    · exact Or.inl h2
    · exact absurd (h2 ▸ hv) hs
    · exact Or.inr h2

end C

end CFSG.GH74.Generic.S45
