module

public import CFSG.LargeExtraspecial.S3cLine
public import CFSG.LargeExtraspecial.S3cEven

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent AddSubgroupClass.instZModModule

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.Literature.FSmith
  CFSG.RankThree.OrthogonalInvolutions OrthoF2

universe u

namespace TransvectionConfig

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {q : QuadraticForm (ZMod 2) V}
  {a : V} {W : Submodule (ZMod 2) V} {L : Subgroup (V ≃ₗ[ZMod 2] V)}
  (C : TransvectionConfig q a W L)
include C

theorem four_le_card_fix_of_two_le [FiniteDimensional (ZMod 2) V] {p : V}
    (h2 : 2 ≤ finrank (ZMod 2) (C.fixK p)) :
    4 ≤ Nat.card {s : V ≃ₗ[ZMod 2] V // s ∈ L ∧ s p = p} := by
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have : Finite (V ≃ₗ[ZMod 2] V) :=
    Finite.of_injective (fun e : V ≃ₗ[ZMod 2] V => (e : V → V))
      (fun _ _ h => LinearEquiv.ext (congrFun h))
  let f : C.fixK p → {s : V ≃ₗ[ZMod 2] V // s ∈ L ∧ s p = p} := fun φ =>
    ⟨C.sOf φ, C.sOf_mem φ, (C.mem_fixK).mp φ.2⟩
  have hf : Function.Injective f := fun φ φ' e =>
    Subtype.ext (C.sOf_injective (congrArg Subtype.val e))
  have hcard : 4 ≤ Nat.card (C.fixK p) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) h2
  exact hcard.trans (Nat.card_le_card_of_injective f hf)

theorem mk_eq_zero_of_mem_span {w : V} (hw : w ∈ W) (hwa : w ∈ (ZMod 2) ∙ a) :
    (Submodule.Quotient.mk ⟨w, hw⟩ : W ⧸ C.lineW) = 0 := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hwa
  have e : (⟨w, hw⟩ : W) = c • ⟨a, C.haW⟩ := Subtype.ext (by simp [← hc])
  rw [e, Submodule.Quotient.mk_smul, C.mk_a_eq_zero, smul_zero]

theorem mem_contractRad_psi_iff [FiniteDimensional (ZMod 2) V] {v : V} (hv : polar q a v = 1)
    {p : V} (hp : polar q a p = 0) (φ : C.K) :
    φ ∈ (C.isAltTrilin_theta v).contractRad (C.psi hp) ↔ C.sOf φ p - p ∈ (ZMod 2) ∙ a := by
  rw [IsAltTrilin.mem_contractRad]
  constructor
  · intro h
    exact C.mem_span_of_forall_K (C.perp _ (C.sOf_mem φ) p hp) fun χ => by
      rw [← C.theta_psi hv hp φ χ]
      exact h χ
  · intro h χ
    rw [C.theta_psi hv hp, C.mk_eq_zero_of_mem_span _ h, map_zero]

theorem finrank_le_contractRad_add_one [FiniteDimensional (ZMod 2) V] {v : V}
    (hv : polar q a v = 1) {p : V} (hp : polar q a p = 0)
    (hsame : ∀ φ φ' : C.K, C.sOf φ p - p ∉ (ZMod 2) ∙ a → C.sOf φ' p - p ∉ (ZMod 2) ∙ a →
      (C.sOf φ p - p) - (C.sOf φ' p - p) ∈ (ZMod 2) ∙ a) :
    finrank (ZMod 2) C.K ≤
      finrank (ZMod 2) ((C.isAltTrilin_theta v).contractRad (C.psi hp)) + 1 := by
  have hT := C.isAltTrilin_theta v
  by_cases htop : hT.contractRad (C.psi hp) = ⊤
  · rw [htop, finrank_top]
    exact Nat.le_succ _
  obtain ⟨φ₁, hφ₁⟩ : ∃ φ₁, φ₁ ∉ hT.contractRad (C.psi hp) := by
    by_contra hcon
    push Not at hcon
    exact htop (eq_top_iff.mpr fun φ _ => hcon φ)
  have hφ₁' : C.sOf φ₁ p - p ∉ (ZMod 2) ∙ a := fun h =>
    hφ₁ ((C.mem_contractRad_psi_iff hv hp φ₁).mpr h)
  have hle : (⊤ : Submodule (ZMod 2) C.K) ≤ hT.contractRad (C.psi hp) ⊔ (ZMod 2) ∙ φ₁ := by
    intro φ _
    by_cases hφ : φ ∈ hT.contractRad (C.psi hp)
    · exact Submodule.mem_sup_left hφ
    have hφ' : C.sOf φ p - p ∉ (ZMod 2) ∙ a := fun h =>
      hφ ((C.mem_contractRad_psi_iff hv hp φ).mpr h)
    have hW := C.perp _ (C.sOf_mem φ) p hp
    have hW₁ := C.perp _ (C.sOf_mem φ₁) p hp
    have hmk : (Submodule.Quotient.mk ⟨_, hW⟩ : W ⧸ C.lineW) =
        Submodule.Quotient.mk ⟨_, hW₁⟩ := by
      rw [← sub_eq_zero, ← Submodule.Quotient.mk_sub]
      exact C.mk_eq_zero_of_mem_span _ (hsame φ φ₁ hφ' hφ₁')
    have hsum : φ + φ₁ ∈ hT.contractRad (C.psi hp) := by
      refine (hT.mem_contractRad).mpr fun χ => ?_
      rw [hT.add_left, C.theta_psi hv hp, C.theta_psi hv hp, hmk, vec_add_self]
    have e : φ = (φ + φ₁) - φ₁ := by abel
    rw [e]
    exact Submodule.sub_mem _ (Submodule.mem_sup_left hsum)
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self φ₁))
  calc finrank (ZMod 2) C.K = finrank (ZMod 2) (⊤ : Submodule (ZMod 2) C.K) :=
        (finrank_top (ZMod 2) C.K).symm
    _ ≤ finrank (ZMod 2) ↥(hT.contractRad (C.psi hp) ⊔ (ZMod 2) ∙ φ₁) :=
        Submodule.finrank_mono hle
    _ ≤ finrank (ZMod 2) (hT.contractRad (C.psi hp)) + finrank (ZMod 2) ↥((ZMod 2) ∙ φ₁) :=
        Submodule.finrank_add_le_finrank_add_finrank _ _
    _ ≤ finrank (ZMod 2) (hT.contractRad (C.psi hp)) + 1 := by
        have := finrank_span_le_card (R := ZMod 2) ({φ₁} : Set C.K)
        simp only [Set.toFinset_singleton, Finset.card_singleton] at this
        omega

end TransvectionConfig

namespace Setting

variable {G : Type u} [Group G] [Finite G] (S : Setting G)

theorem exists_point_perp (hTI : WeaklyClosedTITransitive.{u}) (hn : 3 ≤ S.width)
    {g h ke : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (hno : ¬ S.HasTypeAInL g) (hirr : ¬ S.IsReducible) {t : S.O} (ht : t ∈ S.Dbar g)
    (ht1 : t ≠ 1) (hh : h ∈ S.M)
    (hab : g * S.z * g⁻¹ * ((h * g) * S.z * (h * g)⁻¹) =
      (h * g) * S.z * (h * g)⁻¹ * (g * S.z * g⁻¹))
    (hke : ke ∈ S.M)
    (hae : g * S.z * g⁻¹ * ((ke * g) * S.z * (ke * g)⁻¹) ≠
      (ke * g) * S.z * (ke * g)⁻¹ * (g * S.z * g⁻¹))
    {s : S.O} (hs : s ∈ S.Lbar g)
    (hw : (s : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl ((h * g) * S.z * (h * g)⁻¹)) -
      S.cl ((h * g) * S.z * (h * g)⁻¹) ∉ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹)) :
    ∃ k ∈ S.M, (k * g) * S.z * (k * g)⁻¹ ∈ S.Qa g ∧
      (k * g) * S.z * (k * g)⁻¹ * ((ke * g) * S.z * (ke * g)⁻¹) =
        (ke * g) * S.z * (ke * g)⁻¹ * ((k * g) * S.z * (k * g)⁻¹) ∧
      S.cl ((k * g) * S.z * (k * g)⁻¹) - ((s : S.Qt ≃ₗ[ZMod 2] S.Qt)
        (S.cl ((h * g) * S.z * (h * g)⁻¹)) - S.cl ((h * g) * S.z * (h * g)⁻¹)) ∈
        (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) := by
  have C := S.transvectionConfig hTI hn haQ hne hno hirr
  have hbQ := S.conj_mul_mem_QG hh haQ
  have heQ := S.conj_mul_mem_QG hke haQ
  have hp : polar S.q (S.cl (g * S.z * g⁻¹)) (S.cl ((h * g) * S.z * (h * g)⁻¹)) = 0 :=
    (S.polar_cl_eq_zero_iff haQ hbQ).mpr hab
  have hwW := C.perp _ (S.coe_mem_LbarLin hs) _ hp
  obtain ⟨y, hys⟩ := MonoidHom.mem_range.mp (S.Lbar_le_Mbar g hs)
  have hk₁ : (y : G) * h ∈ S.M := S.M.mul_mem y.2 hh
  have hb₁Q := S.conj_mul_mem_QG hk₁ haQ
  have hsp : (s : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl ((h * g) * S.z * (h * g)⁻¹)) =
      S.cl (((y : G) * h * g) * S.z * ((y : G) * h * g)⁻¹) := by
    rw [← hys, S.ρ_cl y hbQ]
    congr 1
    group
  have hpol : polar S.q (S.cl (((y : G) * h * g) * S.z * ((y : G) * h * g)⁻¹))
      (S.cl ((h * g) * S.z * (h * g)⁻¹)) = 0 := by
    have e : S.cl (((y : G) * h * g) * S.z * ((y : G) * h * g)⁻¹) +
        S.cl ((h * g) * S.z * (h * g)⁻¹) = (s : S.Qt ≃ₗ[ZMod 2] S.Qt)
          (S.cl ((h * g) * S.z * (h * g)⁻¹)) - S.cl ((h * g) * S.z * (h * g)⁻¹) := by
      rw [hsp, sub_eq_add_neg, vec_neg]
    rw [QuadraticMap.polar, e, C.totallySingular _ hwW, S.q_cl_conj_z hb₁Q, S.q_cl_conj_z hbQ,
      sub_zero, sub_zero]
  have hne1 : S.cl (((y : G) * h * g) * S.z * ((y : G) * h * g)⁻¹) ≠
      S.cl ((h * g) * S.z * (h * g)⁻¹) := by
    intro e
    apply hw
    rw [hsp, e, sub_self]
    exact Submodule.zero_mem _
  obtain ⟨kw, hkw, hkweq⟩ := S.exists_cl_eq_add hTI hn haQ hne hno hirr ht ht1 hk₁ hh
    ((S.polar_cl_eq_zero_iff hb₁Q hbQ).mp hpol) hne1
  have hweq : S.cl ((kw * g) * S.z * (kw * g)⁻¹) = (s : S.Qt ≃ₗ[ZMod 2] S.Qt)
      (S.cl ((h * g) * S.z * (h * g)⁻¹)) - S.cl ((h * g) * S.z * (h * g)⁻¹) := by
    rw [hkweq, hsp, sub_eq_add_neg, vec_neg]
  have hwQ := S.conj_mul_mem_QG hkw haQ
  have hwQa : (kw * g) * S.z * (kw * g)⁻¹ ∈ S.Qa g :=
    S.mem_Qa_of_cl_mem haQ hne hwQ (by rw [hweq]; exact hwW)
  rcases zmod2_eq_zero_or_eq_one (polar S.q (S.cl ((kw * g) * S.z * (kw * g)⁻¹))
    (S.cl ((ke * g) * S.z * (ke * g)⁻¹))) with h0 | h1
  · refine ⟨kw, hkw, hwQa, (S.polar_cl_eq_zero_iff hwQ heQ).mp h0, ?_⟩
    rw [hweq, sub_self]
    exact Submodule.zero_mem _
  ·
    have haw := S.QG_inf_Qa_comm hne ⟨haQ, S.conj_z_mem_Qa g⟩ ⟨hwQ, hwQa⟩
    have hwa : S.cl ((kw * g) * S.z * (kw * g)⁻¹) ≠ S.cl (g * S.z * g⁻¹) := by
      rw [hweq]
      intro e
      apply hw
      rw [e]
      exact Submodule.mem_span_singleton_self _
    obtain ⟨kc, hkc, hkceq⟩ := S.exists_cl_eq_add_cl hTI hn haQ hne hno hirr ht ht1 hkw haw hwa
    have hcQ := S.conj_mul_mem_QG hkc haQ
    refine ⟨kc, hkc, ?_, ?_, ?_⟩
    · refine S.mem_Qa_of_cl_mem haQ hne hcQ ?_
      rw [hkceq]
      exact Submodule.add_mem _ (S.cl_mem_clSub ⟨hwQ, hwQa⟩ hwQ)
        (S.cl_mem_clSub ⟨haQ, S.conj_z_mem_Qa g⟩ haQ)
    · refine (S.polar_cl_eq_zero_iff hcQ heQ).mp ?_
      rw [hkceq, polar_add_left, h1, (S.polar_cl_eq_one_iff haQ heQ).mpr hae]
      decide
    · rw [hkceq, ← hweq, add_sub_cancel_left]
      exact Submodule.mem_span_singleton_self _

theorem card_Dbar_ne_two (hTI : WeaklyClosedTITransitive.{u}) (hn : 5 ≤ S.width) {g : G}
    (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) (hno : ¬ S.HasTypeAInL g)
    (hirr : ¬ S.IsReducible) : Nat.card (S.Dbar g) ≠ 2 := by
  classical
  intro hD2
  obtain ⟨x, hxD, hx1⟩ := exists_mem_not_mem_finset_of_card_lt (H := S.Dbar g) {1}
    (by rw [Finset.card_singleton]; omega)
  simp only [Finset.mem_singleton] at hx1
  have hD := S.eq_one_or_eq_of_card_Dbar_eq_two hD2 hxD hx1
  obtain ⟨h, hh, hab, -, hxb⟩ :=
    S.exists_commute_not_mem_Qa hTI (by omega) haQ hne hno hirr hxD hx1
  have hbQ := S.conj_mul_mem_QG hh haQ
  have ha0 := S.cl_conj_z_ne_zero haQ hne
  have hxb' : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl ((h * g) * S.z * (h * g)⁻¹)) ≠
      S.cl ((h * g) * S.z * (h * g)⁻¹) := by
    rw [hxb x hxD hx1]
    intro e
    exact ha0 (by simpa using e)
  have hle := S.card_Lbar_fix_le_two hTI (by omega) haQ hne hno hirr hh hab hxD.1 hx1 hxD.2 hD
    hxb'
  have C := S.transvectionConfig hTI (by omega) haQ hne hno hirr
  obtain ⟨v, hv⟩ := S.exists_polar_cl_eq_one haQ hne
  have hp : polar S.q (S.cl (g * S.z * g⁻¹)) (S.cl ((h * g) * S.z * (h * g)⁻¹)) = 0 :=
    (S.polar_cl_eq_zero_iff haQ hbQ).mpr hab
  obtain ⟨ke, hke, hae⟩ := S.exists_not_commute_conj haQ hne hirr
  have hpt : ∀ φ : C.K, C.sOf φ (S.cl ((h * g) * S.z * (h * g)⁻¹)) -
      S.cl ((h * g) * S.z * (h * g)⁻¹) ∉ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) →
      ∃ k ∈ S.M, (k * g) * S.z * (k * g)⁻¹ ∈ S.Qa g ∧
        (k * g) * S.z * (k * g)⁻¹ * ((ke * g) * S.z * (ke * g)⁻¹) =
          (ke * g) * S.z * (ke * g)⁻¹ * ((k * g) * S.z * (k * g)⁻¹) ∧
        S.cl ((k * g) * S.z * (k * g)⁻¹) - (C.sOf φ (S.cl ((h * g) * S.z * (h * g)⁻¹)) -
          S.cl ((h * g) * S.z * (h * g)⁻¹)) ∈ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) := by
    intro φ hφ
    obtain ⟨s, hs, hse⟩ := S.mem_LbarLin_iff.mp (C.sOf_mem φ)
    rw [← hse] at hφ ⊢
    exact S.exists_point_perp hTI (by omega) haQ hne hno hirr hxD hx1 hh hab hke hae hs hφ
  have hsame : ∀ φ φ' : C.K,
      C.sOf φ (S.cl ((h * g) * S.z * (h * g)⁻¹)) - S.cl ((h * g) * S.z * (h * g)⁻¹) ∉
        (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) →
      C.sOf φ' (S.cl ((h * g) * S.z * (h * g)⁻¹)) - S.cl ((h * g) * S.z * (h * g)⁻¹) ∉
        (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) →
      (C.sOf φ (S.cl ((h * g) * S.z * (h * g)⁻¹)) - S.cl ((h * g) * S.z * (h * g)⁻¹)) -
        (C.sOf φ' (S.cl ((h * g) * S.z * (h * g)⁻¹)) - S.cl ((h * g) * S.z * (h * g)⁻¹)) ∈
        (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) := by
    intro φ φ' hφ hφ'
    obtain ⟨k₁, hk₁, hc₁, hc₁e, hd₁⟩ := hpt φ hφ
    obtain ⟨k₂, hk₂, hc₂, hc₂e, hd₂⟩ := hpt φ' hφ'
    by_cases h12 : S.cl ((k₁ * g) * S.z * (k₁ * g)⁻¹) = S.cl ((k₂ * g) * S.z * (k₂ * g)⁻¹)
    · have e : (C.sOf φ (S.cl ((h * g) * S.z * (h * g)⁻¹)) - S.cl ((h * g) * S.z * (h * g)⁻¹)) -
          (C.sOf φ' (S.cl ((h * g) * S.z * (h * g)⁻¹)) - S.cl ((h * g) * S.z * (h * g)⁻¹)) =
          (S.cl ((k₂ * g) * S.z * (k₂ * g)⁻¹) - (C.sOf φ' (S.cl ((h * g) * S.z * (h * g)⁻¹)) -
            S.cl ((h * g) * S.z * (h * g)⁻¹))) -
          (S.cl ((k₁ * g) * S.z * (k₁ * g)⁻¹) - (C.sOf φ (S.cl ((h * g) * S.z * (h * g)⁻¹)) -
            S.cl ((h * g) * S.z * (h * g)⁻¹))) := by
        rw [h12]
        abel
      rw [e]
      exact Submodule.sub_mem _ hd₂ hd₁
    · exact (S.false_of_two_points hTI (by omega) haQ hne hno hirr hxD hx1 hke hk₁ hk₂ hae hc₁
        hc₂ hc₁e hc₂e h12).elim
  have hR := C.finrank_le_contractRad_add_one hv hp hsame
  have h1 := C.finrank_contractRad_le hv hp
  have hW := S.finrank_clSub_of_irreducible hTI (by omega) haQ hne hno hirr
  have hK := C.finrank_K_add_one
  have h4 := C.four_le_card_fix_of_two_le (p := S.cl ((h * g) * S.z * (h * g)⁻¹)) (by omega)
  exact absurd (h4.trans hle) (by norm_num)

theorem fixLbar_eq_span (hTI : WeaklyClosedTITransitive.{u}) (hn : 4 ≤ S.width) {g : G}
    (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) (hno : ¬ S.HasTypeAInL g)
    (hirr : ¬ S.IsReducible) : S.fixLbar g = (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) := by
  rcases Nat.lt_or_ge S.width 5 with h5 | h5
  · exact S.fixLbar_eq_span_of_width_eq_four hTI (by omega) haQ hne hno hirr
  · rcases S.fixLbar_eq_span_or hTI hn haQ hne hno hirr with h | ⟨h2, -⟩
    · exact h
    · exact absurd h2 (S.card_Dbar_ne_two hTI h5 haQ hne hno hirr)

theorem false_of_width_eq_five (hTI : WeaklyClosedTITransitive.{u}) (hn : S.width = 5) {g : G}
    (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) (hno : ¬ S.HasTypeAInL g)
    (hirr : ¬ S.IsReducible) : False :=
  S.fixLbar_ne_span_of_width_eq_five hTI hn haQ hne hno hirr
    (S.fixLbar_eq_span hTI (by omega) haQ hne hno hirr)

end Setting

end CFSG.LargeExtraspecial
