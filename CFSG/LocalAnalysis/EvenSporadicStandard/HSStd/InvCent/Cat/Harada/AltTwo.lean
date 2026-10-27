module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harada.AltOne
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harada.A9Centre
import CFSG.LocalAnalysis.ComponentClassification.CatFC.PumpBridge
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harada.TwoCfg

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent.Harada

open Subgroup CFSG Equiv Equiv.Perm
open scoped Nat

theorem dvd_cases_480 {d : ℕ} (h60 : 60 ∣ d) (h480 : d ∣ 480) :
    d = 60 ∨ d = 120 ∨ d = 240 ∨ d = 480 := by
  obtain ⟨j, rfl⟩ := h60
  have hj : 60 * j ≤ 480 := Nat.le_of_dvd (by norm_num) h480
  have hj8 : j ≤ 8 := by omega
  interval_cases j <;> first | omega | (exfalso; revert h480; decide)

theorem two_derived_equiv_alt {G : Type*} [Group G] {t v : G} {J : Subgroup G}
    (h : TwoCfg t v J) (htop : centralizer ({t} : Set G) ≠ ⊤) :
    Nonempty (↥(centralizerDerived t) ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨e⟩ := h.hJ
  rw [h.centralizerDerived_eq htop, commutator_eq_map_alt J e]
  exact ⟨(Subgroup.equivMapOfInjective _ _ (embJ_injective J e)).symm⟩

theorem alt_arm_two {G : Type} [Group G] [Finite G] {S : Subgroup G} (hSn : S.Normal)
    (hcent : centralizer (S : Set G) = ⊥) {t v : G} {J : Subgroup G} (h : TwoCfg t v J)
    {m : ℕ} (hm : Odd m) (hm7 : 7 ≤ m) (θ : ↥S ≃* alternatingGroup (Fin m))
    (hPS : centralizerDerived t ≤ S) : False := by
  classical
  haveI := hSn
  have htop : centralizer ({t} : Set G) ≠ ⊤ := centralizer_singleton_ne_top hcent h.t_ne_one
  have hC : Nat.card ↥(centralizer ({t} : Set G)) = 480 := h.card_centralizer htop
  obtain ⟨r, hr1, hr2, hd, h60, hdvd⟩ :=
    alt_arm_prelim hSn hcent h.ht hm7 θ hPS (two_derived_equiv_alt h htop)
  rw [hC] at hdvd
  rcases alt_numeric_two hm hm7 hr1 hr2 hd (dvd_cases_480 h60 hdvd) with
    ⟨rfl, -, -⟩ | ⟨rfl, hr, hd480⟩
  ·
    exfalso
    have hS7 : Nat.card ↥S = 2520 := by
      rw [Nat.card_congr θ.toEquiv]
      exact card_alt_seven
    have hMA : Nat.card (MulAut ↥S) = 5040 := by
      rw [Nat.card_congr (MulAut.congr θ).toEquiv]
      exact card_mulAut_alt_seven
    have hGle : Nat.card G ≤ 5040 := hMA ▸ card_le_card_mulAut hcent
    have h2S : 2520 ∣ Nat.card G := hS7 ▸ Subgroup.card_subgroup_dvd_card S
    have h480 : 480 ∣ Nat.card G := hC ▸ Subgroup.card_subgroup_dvd_card _
    have hGpos : 0 < Nat.card G := Nat.card_pos
    omega
  ·
    have hCS : centralizer ({t} : Set G) ≤ S := by
      have heq : S ⊓ centralizer ({t} : Set G) = centralizer ({t} : Set G) :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hC, hd480])
      exact inf_eq_right.1 heq
    have htS : t ∈ S := hCS (mem_centralizer_singleton_iff.2 rfl)
    have hvC : v ∈ centralizer ({t} : Set G) := by
      have hv' : v ∈ centralizer ({v} : Set G) := mem_centralizer_singleton_iff.2 rfl
      rwa [h.hCv] at hv'
    have hvS : v ∈ S := hCS hvC
    have ht2 : t * t = 1 := h.t_sq
    set σ : MulAut ↥S := MulAut.conjNormal t with hσdef
    have hσ2 : σ * σ = 1 := by
      refine MulEquiv.ext fun y => ?_
      exact conjNormal_involutive ht2 y
    have hσ1 : σ ≠ 1 := by
      intro h1
      apply h.t_ne_one
      apply conjNormal_injective_of_centralizer hcent
      rw [map_one]
      exact h1
    obtain ⟨π, hπ2, hπconj, a, ha1, ha2, hacyc, hacard⟩ :=
      alt_data 9 (by norm_num) (by norm_num) θ σ hσ2 hσ1
    have hcard480 : Nat.card ↥(autCentralizer σ) = 480 := by
      rw [CFSG.ComponentClassification.CatFC.autCentralizer_eq_fixedSubgroup,
        card_fixedSubgroup_conjNormal ht2]
      exact hd480
    rw [hcard480] at hacard
    have ha4 : a ≤ 4 := by omega
    have ha : a = 2 := by
      interval_cases a <;> simp only [Nat.factorial] at hacard <;> omega
    subst ha
    set y : Perm (Fin 9) := ((θ ⟨t, htS⟩ : alternatingGroup (Fin 9)) : Perm (Fin 9)) with hy
    have hπy : π = y := by
      have hall : ∀ x : ↥S, π * ((θ x : alternatingGroup (Fin 9)) : Perm (Fin 9)) * π⁻¹ =
          y * ((θ x : alternatingGroup (Fin 9)) : Perm (Fin 9)) * y⁻¹ := by
        intro x
        rw [← hπconj x]
        have hσx : σ x = ⟨t, htS⟩ * x * ⟨t, htS⟩⁻¹ := by
          apply Subtype.ext
          simp [hσdef, MulAut.conjNormal_apply]
        rw [hσx, map_mul, map_mul, map_inv]
        rfl
      have h1 : MulAut.conjNormal (H := alternatingGroup (Fin 9)) (y⁻¹ * π) = 1 := by
        refine MulEquiv.ext fun a' => ?_
        obtain ⟨x, rfl⟩ := θ.surjective a'
        apply Subtype.ext
        rw [MulAut.conjNormal_apply, MulAut.one_apply]
        calc y⁻¹ * π * ((θ x : alternatingGroup (Fin 9)) : Perm (Fin 9)) * (y⁻¹ * π)⁻¹
            = y⁻¹ * (π * ((θ x : alternatingGroup (Fin 9)) : Perm (Fin 9)) * π⁻¹) * y := by
              group
          _ = ((θ x : alternatingGroup (Fin 9)) : Perm (Fin 9)) := by
              rw [hall x]
              group
      have h2 : y⁻¹ * π = 1 :=
        CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup 9 (by norm_num)
          (h1.trans (map_one _).symm)
      calc π = y * (y⁻¹ * π) := by group
        _ = y := by rw [h2, mul_one]
    have hcyc : y.cycleType = (swap (0 : Fin 9) 1 * swap 2 3).cycleType := by
      rw [← hπy, hacyc, cycleType_swap_mul_swap_of_nodup (by decide)]
      rfl
    obtain ⟨g, hg⟩ := isConj_iff.1 (isConj_iff_cycleType_eq.2 hcyc)
    set w : Perm (Fin 9) := ((θ ⟨v, hvS⟩ : alternatingGroup (Fin 9)) : Perm (Fin 9)) with hw
    have hsw : sign w = 1 := mem_alternatingGroup.1 (θ ⟨v, hvS⟩).2
    have hsz : sign (g * w * g⁻¹) = 1 := by
      rw [map_mul, map_mul, map_inv, hsw, mul_one, mul_inv_cancel]
    have hvV : v ∈ fourGroup t v := h.mem_fourGroup.2 (Or.inr (Or.inr (Or.inl rfl)))
    have hcomm : ∀ c : Perm (Fin 9), sign c = 1 →
        c * (swap 0 1 * swap 2 3) = (swap 0 1 * swap 2 3) * c →
        c * (g * w * g⁻¹) = (g * w * g⁻¹) * c := by
      intro c hc hcc
      set c' : Perm (Fin 9) := g⁻¹ * c * g with hc'
      have hsc' : sign c' = 1 := by
        rw [hc', map_mul, map_mul, map_inv, hc]
        rw [mul_one, inv_mul_cancel]
      have hc'y : c' * y = y * c' := by
        have h1 : c * (g * y * g⁻¹) = (g * y * g⁻¹) * c := by rw [hg]; exact hcc
        calc c' * y = g⁻¹ * (c * (g * y * g⁻¹)) * g := by rw [hc']; group
          _ = g⁻¹ * ((g * y * g⁻¹) * c) * g := by rw [h1]
          _ = y * c' := by rw [hc']; group
      obtain ⟨x, hx⟩ := θ.surjective ⟨c', mem_alternatingGroup.2 hsc'⟩
      have hxc' : ((θ x : alternatingGroup (Fin 9)) : Perm (Fin 9)) = c' := by rw [hx]
      have hxt : (x : G) * t = t * (x : G) := by
        have h1 : θ (x * ⟨t, htS⟩) = θ (⟨t, htS⟩ * x) := by
          apply Subtype.ext
          rw [map_mul, map_mul]
          show ((θ x : alternatingGroup (Fin 9)) : Perm (Fin 9)) * y =
            y * ((θ x : alternatingGroup (Fin 9)) : Perm (Fin 9))
          rw [hxc']
          exact hc'y
        exact congrArg Subtype.val (θ.injective h1)
      have hxC : (x : G) ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.2 hxt
      have hxv : (x : G) * v = v * (x : G) := (h.fourGroup_central hvV hxC).symm
      have hc'w : c' * w = w * c' := by
        have h2 : x * ⟨v, hvS⟩ = ⟨v, hvS⟩ * x := Subtype.ext hxv
        have h3 := congrArg (fun u => ((θ u : alternatingGroup (Fin 9)) : Perm (Fin 9))) h2
        simp only [map_mul, Subgroup.coe_mul] at h3
        rw [hxc'] at h3
        exact h3
      calc c * (g * w * g⁻¹) = g * (c' * w) * g⁻¹ := by rw [hc']; group
        _ = g * (w * c') * g⁻¹ := by rw [hc'w]
        _ = (g * w * g⁻¹) * c := by rw [hc']; group
    rcases a9_centre_aux (g * w * g⁻¹) hsz hcomm with hz1 | hzπ
    · apply h.v_ne_one htop
      have hw1 : w = 1 := by
        calc w = g⁻¹ * (g * w * g⁻¹) * g := by group
          _ = 1 := by rw [hz1]; group
      have h1 : θ ⟨v, hvS⟩ = 1 := Subtype.ext hw1
      have h2 : (⟨v, hvS⟩ : ↥S) = 1 := θ.injective (by rw [h1, map_one])
      exact congrArg Subtype.val h2
    · apply h.v_ne_t htop
      have hwy : w = y := by
        have h1 : g * w * g⁻¹ = g * y * g⁻¹ := by rw [hg]; exact hzπ
        exact mul_left_cancel (mul_right_cancel h1)
      have h2 : θ ⟨v, hvS⟩ = θ ⟨t, htS⟩ := Subtype.ext hwy
      exact congrArg Subtype.val (θ.injective h2)

end CFSG.EvenSporadicStandard.HSStd.InvCent.Harada
