module

public import CFSG.GF2Type.Smith1980Orth.GoodT

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open Subgroup Module CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6
  CFSG.LargeExtraspecial.S14 CFSG.RankThree.OrthogonalInvolutions CFSG.Open

variable {G : Type} [Group G] [Finite G] {S : Setting G}

structure S2Rel (S : Setting G) (g : G) (t k : S.O) (M1 : Subgroup S.O) : Prop where
  le : M1 ≤ S.Mbar
  k_mem : k ∈ M1
  cent_le : ∀ x ∈ S.Mbar, x * t = t * x → x ∈ M1
  orbit : ∀ x ∈ S.Mbar, ∃ y ∈ M1, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
    (y : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹))
  inv_conj : ∀ y ∈ S.Mbar, y * y = 1 → ∃ m ∈ S.Mbar, m * y * m⁻¹ ∈ M1
  index_le : M1.relIndex S.Mbar ≤ 3
  stab_le : ∀ y ∈ S.Mbar, ∀ a ∈ Vt S g t, a ≠ 0 →
    (y : S.Qt ≃ₗ[ZMod 2] S.Qt) a ∈ Submodule.span (ZMod 2) {a, (k : S.Qt ≃ₗ[ZMod 2] S.Qt) a} →
    (y : S.Qt ≃ₗ[ZMod 2] S.Qt) ((k : S.Qt ≃ₗ[ZMod 2] S.Qt) a) ∈
      Submodule.span (ZMod 2) {a, (k : S.Qt ≃ₗ[ZMod 2] S.Qt) a} → y ∈ M1

theorem S2Rel.full {S : Setting G} {g : G} {t k : S.O} (hk : k ∈ S.Mbar) :
    S2Rel S g t k S.Mbar :=
  ⟨le_rfl, hk, fun _ hx _ => hx, fun x hx => ⟨x, hx, rfl⟩, fun y hy _ => ⟨1, one_mem _, by simpa⟩,
    by rw [Subgroup.relIndex_eq_one.mpr le_rfl]; norm_num, fun y hy _ _ _ _ _ => hy⟩

structure S2Pre (S : Setting G) (M1 : Subgroup S.O := S.Mbar) where
  g : G
  t : S.O
  k : S.O
  good : GoodPre S g t
  four_le : 4 ≤ S.width
  finrank_Vt : finrank (ZMod 2) (Vt S g t) = S.width
  k_mem : k ∈ S.Mbar
  k_ne : k ≠ 1
  k_cube : k ^ 3 = 1
  k_conj : ∀ x ∈ M1, x * k * x⁻¹ = k ∨ x * k * x⁻¹ = k⁻¹
  t_inv : t * k * t⁻¹ = k⁻¹
  fpf : ∀ v : S.Qt, (k : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v → v = 0
  mul_Cbar : ∀ {x : S.O}, x ∈ M1 → ∃ s ∈ zpowers k ⊔ zpowers t,
    ∃ c ∈ S.Mbar ⊓ centralizer ((zpowers k ⊔ zpowers t : Subgroup S.O) : Set S.O), x = s * c
  rel : S2Rel S g t k M1

structure S2Data (S : Setting G) (M1 : Subgroup S.O := S.Mbar) extends S2Pre S M1 where
  hΩ : OmegaCase good.H good.C good.ht good.ht1 good.hVQ

namespace S2Pre

variable {M1 : Subgroup S.O} (D : S2Pre S M1)

@[expose] noncomputable def Obar : Subgroup S.O := zpowers D.k

@[expose] noncomputable def Cbar : Subgroup S.O :=
  S.Mbar ⊓ centralizer ((D.Obar ⊔ zpowers D.t : Subgroup S.O) : Set S.O)

theorem Obar_eq_zpowers : D.Obar = zpowers D.k := rfl

theorem k_mem_Obar : D.k ∈ D.Obar := mem_zpowers D.k

theorem k_mem_Mbar : D.k ∈ S.Mbar := D.k_mem

theorem k_mem_M1 : D.k ∈ M1 := D.rel.k_mem

theorem Obar_le_M1 : D.Obar ≤ M1 := zpowers_le.mpr D.k_mem_M1

theorem card_Obar : Nat.card D.Obar = 3 := by
  rw [D.Obar_eq_zpowers, Nat.card_zpowers, orderOf_eq_prime D.k_cube D.k_ne]

theorem conj_mem_Obar_of_mem_M1 {x y : S.O} (hx : x ∈ M1) (hy : y ∈ D.Obar) :
    x * y * x⁻¹ ∈ D.Obar := by
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hy
  rw [← conj_zpow]
  rcases D.k_conj x hx with h | h
  · rw [h]
    exact zpow_mem D.k_mem_Obar n
  · rw [h]
    exact zpow_mem (inv_mem D.k_mem_Obar) n

theorem Cbar_le_Mbar : D.Cbar ≤ S.Mbar := inf_le_left

theorem comm_of_mem_Cbar {c : S.O} (hc : c ∈ D.Cbar) : c * D.t = D.t * c :=
  (mem_centralizer_iff.mp hc.2 D.t (mem_sup_right (mem_zpowers D.t))).symm

theorem Cbar_le_M1 : D.Cbar ≤ M1 := fun c hc => D.rel.cent_le c hc.1 (D.comm_of_mem_Cbar hc)

theorem exists_mul_Cbar_of_mem_M1 {x : S.O} (hx : x ∈ M1) :
    ∃ s ∈ D.Obar ⊔ zpowers D.t, ∃ c ∈ D.Cbar, x = s * c :=
  D.mul_Cbar hx

theorem t_mem_Mbar : D.t ∈ S.Mbar := S.Lbar_le_Mbar D.g D.good.ht

theorem t_mem_M1 : D.t ∈ M1 := D.rel.cent_le D.t D.t_mem_Mbar rfl

theorem t_mul_t : D.t * D.t = 1 := mul_self_of_mem_Lbar S D.good.H.conj_mem D.good.ht

theorem t_inv_eq : D.t⁻¹ = D.t := inv_eq_of_mul_eq_one_right D.t_mul_t

theorem k_fix_eq_zero (v : S.Qt) (hv : (D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) : v = 0 :=
  D.fpf v hv

theorem commSpace_eq : commSpace (D.t : S.Qt ≃ₗ[ZMod 2] S.Qt) = Vt S D.g D.t :=
  (commSpace_t_eq D.good.H D.good.C D.good.ht D.good.ht1 D.good.hVQ).1

@[expose] noncomputable def resC : D.Cbar →* (Vt S D.g D.t ≃ₗ[ZMod 2] Vt S D.g D.t) :=
  restrictHom (S.O.subtype.comp D.Cbar.subtype) (Vt S D.g D.t) fun c _ hu => by
    rw [← D.commSpace_eq] at hu ⊢
    exact S7.apply_mem_commSpace_of_comm (D.comm_of_mem_Cbar c.2) hu

theorem coe_resC_apply (c : D.Cbar) (v : Vt S D.g D.t) :
    ((D.resC c v : Vt S D.g D.t) : S.Qt) = ((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v :=
  rfl

theorem fixSpace_eq : fixSpace (D.t : S.Qt ≃ₗ[ZMod 2] S.Qt) = Vt S D.g D.t := by
  have htt : (D.t : S.Qt ≃ₗ[ZMod 2] S.Qt) * (D.t : S.Qt ≃ₗ[ZMod 2] S.Qt) = 1 := by
    rw [← Subgroup.coe_mul, D.t_mul_t]; rfl
  have hle : commSpace (D.t : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤ fixSpace (D.t : S.Qt ≃ₗ[ZMod 2] S.Qt) :=
    commSpace_le_fixSpace htt
  have hsum := finrank_commSpace_add_finrank_fixSpace (D.t : S.Qt ≃ₗ[ZMod 2] S.Qt)
  rw [D.commSpace_eq, D.finrank_Vt, S.finrank_Qt_eq_two_mul_width] at hsum
  rw [D.commSpace_eq] at hle
  exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [D.finrank_Vt]; omega)).symm

theorem t_apply_of_mem {v : S.Qt} (hv : v ∈ Vt S D.g D.t) : (D.t : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
  rw [← D.fixSpace_eq] at hv
  exact mem_fixSpace.mp hv

theorem t_k_apply (v : S.Qt) :
    (D.t : S.Qt ≃ₗ[ZMod 2] S.Qt) ((D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) v) =
      ((D.k⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ((D.t : S.Qt ≃ₗ[ZMod 2] S.Qt) v) := by
  have h : D.t * D.k = D.k⁻¹ * D.t := by
    rw [← D.t_inv]
    group
  rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, h, Subgroup.coe_mul, LinearEquiv.mul_apply]

theorem eq_zero_of_k_apply_mem {u : S.Qt} (hu : u ∈ Vt S D.g D.t)
    (hv : (D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) u ∈ Vt S D.g D.t) : u = 0 := by
  have h1 := D.t_apply_of_mem hv
  rw [D.t_k_apply, D.t_apply_of_mem hu] at h1
  have h2 : (D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) ((D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) u) = u := by
    have e := congrArg (D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) h1
    have e2 : (D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) (((D.k⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u) = u := by
      rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, mul_inv_cancel]
      rfl
    rw [e2] at e
    exact e.symm
  have h3 : (D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) u = u := by
    have hk3 : ((D.k ^ 3 : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u = u := by
      rw [D.k_cube]; rfl
    rw [pow_succ, Subgroup.coe_mul, LinearEquiv.mul_apply, sq, Subgroup.coe_mul,
      LinearEquiv.mul_apply, h2] at hk3
    exact hk3
  exact D.k_fix_eq_zero u h3

end S2Pre

section Full

namespace S2Pre

variable (D : S2Pre S)

theorem exists_mul_Cbar {x : S.O} (hx : x ∈ S.Mbar) :
    ∃ s ∈ D.Obar ⊔ zpowers D.t, ∃ c ∈ D.Cbar, x = s * c :=
  D.mul_Cbar hx

end S2Pre

end Full

namespace S2Data

variable {M1 : Subgroup S.O} (D : S2Data S M1)

theorem range_resC_le_orthogonalGroup {Q : QuadraticForm (ZMod 2) (Vt S D.g D.t)}
    (hsing : ∀ v : Vt S D.g D.t, v ≠ 0 →
      (Q v = 0 ↔ v ∈ orbitOf (RmodN S D.g D.t) (aV D.good.ht))) :
    D.resC.range ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
  rintro _ ⟨c, rfl⟩
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  have hD := dtEqConj_of_omegaCase D.good.H D.good.hNo D.good.C D.hΩ
  have key : ∀ x ∈ D.Cbar, ∀ v : S.Qt, v ∈ orbit S D.g D.t →
      (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ orbit S D.g D.t := fun x hx v hv =>
    S7.apply_mem_orbit_of_comm D.good.H D.good.ht hD (D.Cbar_le_Mbar hx)
      (D.comm_of_mem_Cbar hx) hv
  have z2 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  intro v
  by_cases hv0 : v = 0
  · rw [hv0, map_zero]
  have hcv0 : D.resC c v ≠ 0 := (LinearEquiv.map_ne_zero_iff _).mpr hv0
  have hiff : Q (D.resC c v) = 0 ↔ Q v = 0 := by
    rw [hsing _ hcv0, hsing _ hv0, mem_orbitOf_RmodN_iff D.good.H.conj_mem D.good.ht,
      mem_orbitOf_RmodN_iff D.good.H.conj_mem D.good.ht, D.coe_resC_apply]
    constructor
    · intro h
      have := key _ (inv_mem c.2) _ h
      rwa [inv_apply_apply_O] at this
    · exact key _ c.2 v
  rcases z2 (Q (D.resC c v)) with h1 | h1 <;> rcases z2 (Q v) with h2 | h2
  · rw [h1, h2]
  · exact absurd (hiff.mp h1) (by rw [h2]; decide)
  · exact absurd (hiff.mpr h2) (by rw [h1]; decide)
  · rw [h1, h2]

end S2Data

theorem exists_s2Data_of_obar {g : G} {t : S.O} (hG : GoodT S g t) (h4 : 4 ≤ S.width)
    (hwV : S.width = finrank (ZMod 2) (Vt S g t)) (hO3 : Nat.card (S7.Obar S) = 3)
    (hc : ∀ x ∈ S.Mbar, x * t * x⁻¹ * t⁻¹ ∈ S7.Obar S) : Nonempty (S2Data S) := by
  obtain ⟨x, hxM, hxt⟩ := S7.exists_conj_ne hG.H hG.ht hG.ht1
  have hc' := hc x hxM
  set o := x * t * x⁻¹ * t⁻¹ with ho
  have ho1 : o ≠ 1 := by
    intro h1
    apply hxt
    rw [ho] at h1
    calc x * t * x⁻¹ = x * t * x⁻¹ * t⁻¹ * t := by group
      _ = t := by rw [h1, one_mul]
  have htt : t * t = 1 := mul_self_of_mem_Lbar S hG.H.conj_mem hG.ht
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hinv : t * o * t⁻¹ = o⁻¹ := by
    have h1 : (x * t * x⁻¹) * (x * t * x⁻¹) = 1 := by
      rw [show (x * t * x⁻¹) * (x * t * x⁻¹) = x * (t * t) * x⁻¹ by group, htt, mul_one,
        mul_inv_cancel]
    have h2 : x * t * x⁻¹ = o * t := by rw [ho]; group
    rw [h2] at h1
    rw [hti]
    calc t * o * t = o⁻¹ * (o * t * (o * t)) := by group
      _ = o⁻¹ := by rw [h1, mul_one]
  have hfpf : S13.FixFree S (S7.Obar S) := by
    have hP1 : S7.Obar S ≠ ⊥ := fun h => by
      rw [h] at hO3
      simp at hO3
    exact S13.fixFree_of hP1 (fun m hm k hk => S7.conj_mem_Obar hm hk) hG.irr
  have hOeq : S7.Obar S = zpowers o := S13.eq_zpowers hO3 hc' ho1
  have hD3 : Nat.card (zpowers o) = 3 := by rw [← hOeq]; exact hO3
  have hconj : ∀ x ∈ S.Mbar, ∀ y ∈ zpowers o, x * y * x⁻¹ ∈ zpowers o := fun x hx y hy => by
    rw [← hOeq] at hy ⊢
    exact S7.conj_mem_Obar hx hy
  have hcomm : ∀ x ∈ S.Mbar, x * t * x⁻¹ * t⁻¹ ∈ zpowers o := fun x hx => by
    rw [← hOeq]
    exact hc x hx
  refine ⟨⟨⟨g, t, o, hG.toGoodPre, h4, hwV.symm, S7.Obar_le_Mbar hc', ho1,
    S13.pow_three_eq_one hO3 hc', ?_, hinv, fun v hv => S13.fix_eq_zero hO3 hfpf hc' ho1 v hv,
    fun {y} hy => S7.exists_sigma_mul_cent (zpowers_le.mpr (S7.Obar_le_Mbar hc')) hD3 hconj
      (S.Lbar_le_Mbar g hG.ht) htt hG.ht1 hcomm (S7.exists_conj_ne hG.H hG.ht hG.ht1) hy,
    S2Rel.full (S7.Obar_le_Mbar hc')⟩,
    hG.hΩ⟩⟩
  intro y hy
  rcases S13.comm_or_inv hO3 (fun k hk => S7.conj_mem_Obar hy hk) with h | h
  · left
    rw [← h o hc', mul_assoc, mul_inv_cancel, mul_one]
  · right
    exact h o hc'

theorem exists_s2Data [IsSimpleGroup G]
    (I : TimInputs) (O : OrthData S) (hw : 8 ≤ S.width)
    (hns : ¬ IsSimpleGroup (Mbar0 S)) : Nonempty (S2Data S) := by
  obtain ⟨g, t, hG⟩ := exists_goodT I O hw hns
  have hwV : S.width = finrank (ZMod 2) (Vt S g t) :=
    S7.width_eq_finrank_of_omegaCase hG.H hG.hNo hG.C hG.ht hG.ht1 hG.hN hG.hΩ
  have h8 : 8 ≤ finrank (ZMod 2) (Vt S g t) := by omega
  exact exists_s2Data_of_obar hG (by omega) hwV
    (S7.card_Obar_eq_three I.hCE hG.H hG.hNo hG.C hG.ht hG.ht1 hG.hVQ hG.hΩ hG.hN h8) fun x hx =>
      S7.comm_mem_Obar I.hCE hG.H hG.hNo hG.C hG.ht hG.ht1 hG.hVQ hG.hΩ hG.hN h8 hx

end CFSG.GF2Type.Smith1980Orth
