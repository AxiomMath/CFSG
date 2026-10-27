module

public import CFSG.LocalAnalysis.GLTheoremB.I2810.Defs
import CFSG.LocalAnalysis.GLTheoremB.I2810.A5BlockBase
import CFSG.LocalAnalysis.GLTheoremB.I2810.BlocksChief
import CFSG.LocalAnalysis.GLTheoremB.I2810.A5BlockInd

public section

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
open scoped commutatorElement

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.A5S

theorem eq_of_conj_eq {a b : ↥(alternatingGroup (Fin 7))}
    (h : ∀ y, a * y * a⁻¹ = b * y * b⁻¹) : a = b := by
  have hc : b⁻¹ * a ∈ Subgroup.center ↥(alternatingGroup (Fin 7)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 := h g
    calc g * (b⁻¹ * a) = b⁻¹ * (b * g * b⁻¹) * a := by group
      _ = b⁻¹ * (a * g * a⁻¹) * a := by rw [h1]
      _ = (b⁻¹ * a) * g := by group
  rw [alternatingGroup.center_eq_bot (by simp), Subgroup.mem_bot] at hc
  exact (inv_mul_eq_one.1 hc).symm

section Setting

variable {X : Type} [Group X] [Finite X] {W K S : Subgroup X} [W.Normal]
variable {e : (↥(bar W K) ⧸ Subgroup.center ↥(bar W K)) ≃* ↥(alternatingGroup (Fin 7))}

theorem act_S (h : Setup28 W K S) {V : Subgroup ↥(alternatingGroup (Fin 7))}
    (hact : ActsLikeCQ (bar W S) (bar W K) e (V.map (MulAut.conj : _ →* _)))
    {s : X} (hs : s ∈ S) :
    ∃ v ∈ V, ∀ k k' : ↥K, (k' : X) = s * k * s⁻¹ → piOf e k' = v * piOf e k * v⁻¹ := by
  have hφmem : A5Ind.indHom W K S h.hN ⟨s, hs⟩ ∈ inducedAutGroup (bar W S) (bar W K) := by
    have hmem : A5Ind.indHom W K S h.hN ⟨s, hs⟩ ∈ (A5Ind.indHom W K S h.hN).range :=
      ⟨⟨s, hs⟩, rfl⟩
    rw [A5Ind.range_indHom (W := W) (K := K) S h.hN] at hmem
    exact hmem
  obtain ⟨σ, hσ, hind⟩ := hact.1 _ hφmem
  obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.1 hσ
  refine ⟨v, hv, fun k k' hk' => ?_⟩
  have h1 := hind (toBar W K k)
  have h2 : A5Ind.indHom W K S h.hN ⟨s, hs⟩ (toBar W K k) = toBar W K k' := by
    apply Subtype.ext
    rw [A5Ind.indHom_toBar, A5Ind.toBar_coe, hk']
  rw [h2] at h1
  show e (QuotientGroup.mk (toBar W K k')) = v * e (QuotientGroup.mk (toBar W K k)) * v⁻¹
  rw [h1]
  rfl

theorem piOf_mem_of_mem_S (h : Setup28 W K S) {V : Subgroup ↥(alternatingGroup (Fin 7))}
    (hact : ActsLikeCQ (bar W S) (bar W K) e (V.map (MulAut.conj : _ →* _)))
    {x : ↥K} (hx : (x : X) ∈ S) : piOf e x ∈ V := by
  obtain ⟨v, hv, hvx⟩ := act_S h hact hx
  have key : ∀ y, piOf e x * y * (piOf e x)⁻¹ = v * y * v⁻¹ := by
    intro y
    obtain ⟨k, hk⟩ := (BlocksChief.piOf_props_aux e).1 y
    have h1 := hvx k (x * k * x⁻¹) rfl
    rw [← hk, ← h1, map_mul, map_mul, map_inv]
  rw [eq_of_conj_eq key]
  exact hv

theorem exists_lift_of_mem_inf (h : Setup28 W K S) {t : X ⧸ W} (htS : t ∈ bar W S)
    (htK : t ∈ bar W K) : ∃ x : ↥K, (x : X) ∈ S ∧ QuotientGroup.mk' W (x : X) = t := by
  obtain ⟨s, hs, hst⟩ := htS
  obtain ⟨k, hk, hkt⟩ := htK
  have hsk : s⁻¹ * k ∈ W := QuotientGroup.eq.1 (hst.trans hkt.symm)
  refine ⟨⟨k, hk⟩, ?_, hkt⟩
  have h2 : s * (s⁻¹ * k) ∈ S := S.mul_mem hs (h.hWS hsk)
  rwa [mul_inv_cancel_left] at h2

theorem cov_aux (h : Setup28 W K S) {V₄ : Subgroup ↥(alternatingGroup (Fin 7))}
    (hV₄ : IsRootFour V₄)
    (hact : ActsLikeCQ (bar W S) (bar W K) e (V₄.map (MulAut.conj : _ →* _)))
    (hS4 : Nat.card ↥(bar W S ⊓ bar W K) = 4) :
    ∀ v ∈ V₄, ∃ k : ↥K, (k : X) ∈ S ∧ piOf e k = v := by
  let τ : ↥(bar W S ⊓ bar W K) →* ↥(alternatingGroup (Fin 7)) :=
    (A5Base.piBar e).comp (Subgroup.inclusion inf_le_right)
  have hτx : ∀ (t : ↥(bar W S ⊓ bar W K)) (x : ↥K), QuotientGroup.mk' W (x : X) = (t : X ⧸ W) →
      τ t = piOf e x := by
    intro t x hxt
    show A5Base.piBar e ⟨(t : X ⧸ W), t.2.2⟩ = A5Base.piBar e (toBar W K x)
    congr 1
    exact Subtype.ext hxt.symm
  have hτV : ∀ t, τ t ∈ V₄ := by
    intro t
    obtain ⟨x, hxS, hxt⟩ := exists_lift_of_mem_inf h t.2.1 t.2.2
    rw [hτx t x hxt]
    exact piOf_mem_of_mem_S h hact hxS
  have hτinj : Function.Injective τ := by
    rw [injective_iff_map_eq_one]
    intro t ht
    obtain ⟨s, hs, hst⟩ := t.2.1
    obtain ⟨m, hm⟩ := A5Base.exists_two_pow_of_mem h hs
    have hc : (⟨(t : X ⧸ W), t.2.2⟩ : ↥(bar W K)) ∈ Subgroup.center ↥(bar W K) :=
      (A5Base.piBar_eq_one_iff e _).1 ht
    have hpow : (⟨(t : X ⧸ W), t.2.2⟩ : ↥(bar W K)) ^ (2 ^ m) = 1 := by
      apply Subtype.ext
      show (t : X ⧸ W) ^ (2 ^ m) = 1
      rw [← hst, ← map_pow, hm, map_one]
    have h1 := A5Base.central_eq_one_of_two_pow h hc hpow
    exact Subtype.ext (congrArg (fun z : ↥(bar W K) => (z : X ⧸ W)) h1)
  have hrange : τ.range = V₄ := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨t, rfl⟩
      exact hτV t
    · have h1 : Nat.card ↥τ.range = Nat.card ↥(bar W S ⊓ bar W K) :=
        (Nat.card_congr (MonoidHom.ofInjective hτinj).toEquiv).symm
      rw [h1, hS4, hV₄.1]
  intro v hv
  rw [← hrange] at hv
  obtain ⟨t, rfl⟩ := hv
  obtain ⟨x, hxS, hxt⟩ := exists_lift_of_mem_inf h t.2.1 t.2.2
  exact ⟨x, hxS, (hτx t x hxt).symm⟩

theorem dec_aux (h : Setup28 W K S) {V₄ : Subgroup ↥(alternatingGroup (Fin 7))}
    (hact : ActsLikeCQ (bar W S) (bar W K) e (V₄.map (MulAut.conj : _ →* _)))
    (hcov : ∀ v ∈ V₄, ∃ k : ↥K, (k : X) ∈ S ∧ piOf e k = v) :
    ∀ s ∈ S, ∃ k : ↥K, (k : X) ∈ S ∧ s * (k : X)⁻¹ ∈ kerAct W K S ∧ piOf e k ∈ V₄ := by
  intro s hs
  obtain ⟨v, hv, hvs⟩ := act_S h hact hs
  obtain ⟨x, hxS, hxv⟩ := hcov v hv
  refine ⟨x, hxS, ?_, hxv ▸ hv⟩
  have huS : s * (x : X)⁻¹ ∈ S := S.mul_mem hs (S.inv_mem hxS)
  refine ⟨huS, fun k hk => ?_⟩
  have hα : A5Ind.indHom W K S h.hN ⟨s * (x : X)⁻¹, huS⟩ = 1 := by
    refine A5Ind.aut_eq_one (A5Base.perfect_bar h) (Z := Subgroup.center ↥(bar W K)) le_rfl _
      fun y => ?_
    obtain ⟨k₀, rfl⟩ := BlocksChief.toBar_surjective W K y
    have hk' : (s * (x : X)⁻¹) * (k₀ : X) * (s * (x : X)⁻¹)⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.1 (h.hN huS) _).1 k₀.2
    set k' : ↥K := ⟨(s * (x : X)⁻¹) * (k₀ : X) * (s * (x : X)⁻¹)⁻¹, hk'⟩ with hk'def
    have hα1 : A5Ind.indHom W K S h.hN ⟨s * (x : X)⁻¹, huS⟩ (toBar W K k₀) = toBar W K k' := by
      apply Subtype.ext
      rw [A5Ind.indHom_toBar, A5Ind.toBar_coe]
    rw [hα1, ← A5Base.piBar_eq_one_iff e, map_mul, map_inv]
    show (piOf e k₀)⁻¹ * piOf e k' = 1
    have h1 := hvs (x⁻¹ * k₀ * x) k' (by
      show (s * (x : X)⁻¹) * (k₀ : X) * (s * (x : X)⁻¹)⁻¹ = s * ((x : X)⁻¹ * (k₀ : X) * (x : X)) * s⁻¹
      group)
    rw [h1, map_mul, map_mul, map_inv, hxv]
    group
  exact (A5Ind.indHom_eq_one_iff S h.hN ⟨s * (x : X)⁻¹, huS⟩).1 hα k hk

theorem a5_S_dec_aux (h : Setup28 W K S)
    (hroot : ActsLikeRootFourCQ (bar W S) (bar W K) 7 e)
    (hS4 : Nat.card ↥(bar W S ⊓ bar W K) = 4) (hind : Nat.card ↥(indAut W K S) = 4) :
    ∃ V₄ : Subgroup ↥(alternatingGroup (Fin 7)), IsRootFour V₄ ∧ SOverV4 W K S (piOf e) V₄ := by
  obtain ⟨V₄, hV₄, hact⟩ := hroot
  have hcov := cov_aux h hV₄ hact hS4
  refine ⟨V₄, hV₄, ?_, dec_aux h hact hcov, hcov⟩
  rw [← A5Ind.card_indAut h (le_refl S)]
  exact hind

theorem conj_S_le (h : Setup28 W K S) (hR : Red28 W K S) {V₄ : Subgroup ↥(alternatingGroup (Fin 7))}
    (hsv : SOverV4 W K S (piOf e) V₄) {k₀ : ↥K}
    (hg : piOf e k₀ ∈ Subgroup.normalizer (V₄ : Set ↥(alternatingGroup (Fin 7)))) :
    ∀ s ∈ S, (k₀ : X) * s * (k₀ : X)⁻¹ ∈ S := by
  intro s hs
  obtain ⟨x, hxS, hsx, hxV⟩ := hsv.dec s hs
  have hx : (k₀ : X) * (x : X) * (k₀ : X)⁻¹ ∈ S := by
    set y : ↥K := k₀ * x * k₀⁻¹ with hy
    have hπy : piOf e y ∈ V₄ := by
      have : piOf e y = piOf e k₀ * piOf e x * (piOf e k₀)⁻¹ := by
        rw [hy, map_mul, map_mul, map_inv]
      rw [this]
      exact (Subgroup.mem_normalizer_iff.1 hg _).1 hxV
    obtain ⟨t, htS, hty⟩ := hsv.cov _ hπy
    have hz : (toBar W K t)⁻¹ * toBar W K y ∈ Subgroup.center ↥(bar W K) := by
      rw [← A5Base.piBar_eq_one_iff e, map_mul, map_inv]
      show (piOf e t)⁻¹ * piOf e y = 1
      rw [hty]
      group
    obtain ⟨ma, hma⟩ := A5Base.exists_two_pow_of_mem h htS
    obtain ⟨mb, hmb⟩ := A5Base.exists_two_pow_of_mem h hxS
    have hyb : (y : X) ^ (2 ^ mb) = 1 := by
      have : (y : X) = (k₀ : X) * (x : X) * (k₀ : X)⁻¹ := rfl
      rw [this, conj_pow, hmb]
      group
    have ha : toBar W K t ^ (2 ^ (ma + mb)) = 1 := A5Base.pow_two_pow_add (A5Base.toBar_pow_two_pow (W := W) hma) mb
    have hb : toBar W K y ^ (2 ^ (ma + mb)) = 1 := by
      have := A5Base.pow_two_pow_add (A5Base.toBar_pow_two_pow (W := W) hyb) ma
      rwa [add_comm] at this
    have hcomm : Commute (toBar W K t)⁻¹ (toBar W K y) := by
      have h1 := Subgroup.mem_center_iff.1 hz (toBar W K t)⁻¹
      exact mul_left_cancel (h1.trans (mul_assoc _ _ _))
    have hone : (toBar W K t)⁻¹ * toBar W K y = 1 := by
      apply A5Base.central_eq_one_of_two_pow h hz (m := ma + mb)
      rw [hcomm.mul_pow, inv_pow, ha, hb]
      simp
    have hW : (t : X)⁻¹ * (y : X) ∈ W :=
      A5Ind.toBar_eq_iff.1 (inv_mul_eq_one.1 hone)
    have h2 : (t : X) * ((t : X)⁻¹ * (y : X)) ∈ S := S.mul_mem htS (h.hWS hW)
    rwa [mul_inv_cancel_left] at h2
  have hw : (k₀ : X) * (s * (x : X)⁻¹) * (k₀ : X)⁻¹ ∈ S :=
    hR.w1_S (hR.w1_nrm (k₀ : X) (Subgroup.mem_sup_left k₀.2) _ hsx)
  have h3 := S.mul_mem hw hx
  have h4 : (k₀ : X) * (s * (x : X)⁻¹) * (k₀ : X)⁻¹ * ((k₀ : X) * (x : X) * (k₀ : X)⁻¹) =
      (k₀ : X) * s * (k₀ : X)⁻¹ := by group
  rwa [h4] at h3

theorem a5_NK_aux (h : Setup28 W K S) (hR : Red28 W K S)
    {V₄ : Subgroup ↥(alternatingGroup (Fin 7))} (hsv : SOverV4 W K S (piOf e) V₄) :
    ∀ g ∈ Subgroup.normalizer (V₄ : Set ↥(alternatingGroup (Fin 7))),
      ∃ k : ↥K, (k : X) ∈ Subgroup.normalizer (S : Set X) ∧ piOf e k = g := by
  intro g hg
  obtain ⟨k₀, hk₀⟩ := (BlocksChief.piOf_props_aux e).1 g
  refine ⟨k₀, ?_, hk₀⟩
  rw [Subgroup.mem_normalizer_iff]
  intro s
  refine ⟨fun hs => conj_S_le h hR hsv (hk₀ ▸ hg) s hs, fun hs => ?_⟩
  have hg' : piOf e k₀⁻¹ ∈ Subgroup.normalizer (V₄ : Set ↥(alternatingGroup (Fin 7))) := by
    rw [map_inv, hk₀]
    exact Subgroup.inv_mem _ hg
  have h1 := conj_S_le h hR hsv hg' _ hs
  have h2 : ((k₀⁻¹ : ↥K) : X) * ((k₀ : X) * s * (k₀ : X)⁻¹) * ((k₀⁻¹ : ↥K) : X)⁻¹ = s := by
    show (k₀ : X)⁻¹ * ((k₀ : X) * s * (k₀ : X)⁻¹) * ((k₀ : X)⁻¹)⁻¹ = s
    group
  rwa [h2] at h1

end Setting

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.A5S
