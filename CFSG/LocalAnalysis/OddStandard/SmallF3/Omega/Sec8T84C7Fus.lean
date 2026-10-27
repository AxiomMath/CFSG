module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84C1Ctx
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84C6Wc
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84C6Rk
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84C6End
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84C7Inv
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84C7Lift
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SGB

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace C10

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z g : G} {B E : Subgroup G}

theorem bad_case_false (F : Sec8T84Base) (h89 : Asc82Lemma89) (hA5 : Sec8T84FactA5)
    (hInv : Sec8T84FactInv) (hE : Sec8E G t L S z g B E) {P : Subgroup (MulAut ↥E)}
    (O : OddNormal E.normalizerMonoidHom.range P)
    (hc : ∀ h ∈ E.normalizerMonoidHom.range,
      h * B89.rhoG hE t * h⁻¹ * (B89.rhoG hE t)⁻¹ ∈ P) : False := by
  classical
  have hS : HCtx E B (B89.rhoG hE t) (B89.Abar hE) E.normalizerMonoidHom.range :=
    hctx_of F h89 hE
  have hK1 : ∀ h ∈ E.normalizerMonoidHom.range, h ≠ 1 → h * h = 1 →
      Nat.card {e : ↥E // h e = e} = 16 :=
    fun h hh hh1 hh2 => HCtx.card_fix_of_invol hInv hS O hc hh hh1 hh2
  have hK2 : ∀ R : Subgroup (MulAut ↥E), R ≤ E.normalizerMonoidHom.range →
      (∀ r ∈ R, r * r = 1) → Nat.card ↥R ≤ 8 :=
    fun R hRH hR2 => HCtx.card_le_eight hInv hS O hc hRH hR2
  have hker2 : ∀ x ∈ centralizer (E : Set G), (∃ k : ℕ, x ^ (2 ^ k) = 1) → x ∈ E :=
    two_elt_cent_le F hE
  have hB16 : Nat.card ↥B = 16 := by rw [hE.ctx.B_e16.2]; norm_num
  have hfus : ∀ x ∈ E, ∀ y ∈ E, IsConj x y →
      ∃ n ∈ normalizer (E : Set G), n * x * n⁻¹ = y :=
    fusion_in_E E B t hE.elem hB16 hE.cent_t (B89.t_sq hE.ctx) (B89.t_mem_X hE)
      hker2 hK1 hK2
  have hA360 : Nat.card ↥(B89.Abar hE) = 360 := by
    obtain ⟨φ⟩ := B89.Abar_equiv_A6 F hE
    rw [Nat.card_congr φ.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite ↥(B89.Abar hE) := Nat.finite_of_card_ne_zero (by rw [hA360]; norm_num)
  obtain ⟨a', ha'ord⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥(B89.Abar hE)) 2 (by rw [hA360]; norm_num)
  have ha₀ : (a' : MulAut ↥E) ∈ B89.Abar hE := a'.2
  have ha1 : (a' : MulAut ↥E) ≠ 1 := by
    intro h
    have h' : a' = 1 := Subtype.ext h
    rw [h', orderOf_one] at ha'ord
    omega
  have ha2 : (a' : MulAut ↥E) * (a' : MulAut ↥E) = 1 := by
    have h := pow_orderOf_eq_one a'
    rw [ha'ord] at h
    have h' : a' * a' = 1 := by simpa [pow_two] using h
    have h'' := congrArg (fun z : ↥(B89.Abar hE) => (z : MulAut ↥E)) h'
    rw [Subgroup.coe_mul, Subgroup.coe_one] at h''
    exact h''
  have h4 : Nat.card {e : ↥E // (e : G) ∈ B ∧ (a' : MulAut ↥E) e = e} = 4 :=
    HCtx.card_fixB_of_inv hInv hS ha₀ ha1 ha2
  obtain ⟨m, hmL, hmB, hm2, hρm⟩ :=
    exists_involution_lift F hE ha₀ ha1 ha2 h4
  obtain ⟨s, hs, hconj, hκs⟩ := exists_conj_normalizer F hE hmL hmB hm2
  obtain ⟨y, hyfix, hynot⟩ :=
    HCtx.exists_fix_not_mem hA5 hInv hS O hc ha₀ ha1 ha2
  have hy1 : y ≠ 1 := by
    have hmemB : ((1 : ↥E) : G) ∈ B := by
      show (1 : G) ∈ B
      exact B.one_mem
    have h := hynot 1 E.normalizerMonoidHom.range.one_mem 1 hmemB
    have h1y : (1 : ↥E) ≠ y := by simpa using h
    exact fun hy => h1y hy.symm
  have hyκ : E.normalizerMonoidHom ⟨s, hs⟩ y = y := by
    rw [hκs, hρm]
    exact hyfix
  have hcomm_ys : (y : G) * s = s * (y : G) := by
    have hcoe : ((E.normalizerMonoidHom ⟨s, hs⟩) y : G) = (y : G) :=
      congrArg Subtype.val hyκ
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at hcoe
    calc (y : G) * s = (s * (y : G) * s⁻¹) * s := by rw [hcoe]
      _ = s * (y : G) := by group
  have hyInf : (y : G) ∈ E ⊓ centralizer ({s} : Set G) :=
    Subgroup.mem_inf.mpr ⟨y.2, Subgroup.mem_centralizer_singleton_iff.mpr hcomm_ys⟩
  have hyG1 : (y : G) ≠ 1 := fun hz => hy1 (Subtype.ext hz)
  have hzB : z ∈ B := (asc82Sec8B_of F.hM G t L S z g B hE.ctx.toSec8Base).1
  have hzE : z ∈ E := B89.B_le_E hE hzB
  have hconj_zy : IsConj z (y : G) :=
    F.h88b G t L S z g B E hE s hconj (y : G) hyInf hyG1
  obtain ⟨n, hn, hnz⟩ := hfus z hzE (y : G) y.2 hconj_zy
  have hh : E.normalizerMonoidHom ⟨n, hn⟩ ∈ E.normalizerMonoidHom.range :=
    MonoidHom.mem_range.mpr ⟨⟨n, hn⟩, rfl⟩
  have hb : E.normalizerMonoidHom ⟨n, hn⟩ ⟨z, hzE⟩ = y := by
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    show n * z * n⁻¹ = (y : G)
    exact hnz
  exact (hynot (E.normalizerMonoidHom ⟨n, hn⟩) hh ⟨z, hzE⟩ hzB) hb

end C10

end CFSG.OddStandard.SmallF3.Omega
