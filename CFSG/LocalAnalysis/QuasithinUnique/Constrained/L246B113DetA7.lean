module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113Sec
public import CFSG.Quasithin.Background.B1MoreTenA
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeDim
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.ThreeCoverBase
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Native
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113Native

public section

namespace CFSG.QuasithinUnique.Bridge.B113Det

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique.Setup.X1
open scoped commutatorElement

theorem exists_generator_of_alt7 {L : Type} [Group L] [Finite L] (hq : CFSG.IsQuasisimple L)
    (hodd : Odd (Nat.card (Subgroup.center L))) (hc : Subgroup.center L ≠ ⊥)
    (e7 : (L ⧸ Subgroup.center L) ≃* alternatingGroup (Fin 7)) :
    ∃ z : L, z ∈ Subgroup.center L ∧ z ^ 3 = 1 ∧ z ≠ 1 ∧
      ∀ c ∈ Subgroup.center L, ∃ k : ℕ, c = z ^ k := by
  have : Group.IsPerfect L := hq.1
  have hker := CFSG.QuasithinUnique.Ch1.ker_comp_mk'_center_eq e7
  have hZ3 : Nat.card (Subgroup.center L) = 3 := by
    have hcov := (CFSG.SectionRank.alternating_small_odd_cover_bound (n := 7) (by norm_num)
      (by norm_num) (e7.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L)))
      (CFSG.QuasithinUnique.Ch1.surjective_comp_mk'_center e7) hker.le
      (by rw [hker]; exact hodd)).2 (Or.inr rfl)
    rw [hker] at hcov
    rcases hcov with h | h
    · exact absurd (Subgroup.eq_bot_of_card_eq _ h) hc
    · exact h
  have h3 : 3 ∣ Nat.card (Subgroup.center L) := by rw [hZ3]
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz
    omega
  have htop : Subgroup.zpowers z = ⊤ := zpowers_eq_top_of_prime_card hZ3 hz1
  refine ⟨(z : L), z.2, ?_, fun h => hz1 (Subtype.ext h), fun c hc => ?_⟩
  · have h := pow_orderOf_eq_one z
    rw [hz] at h
    simpa using congrArg Subtype.val h
  · have hmem : (⟨c, hc⟩ : Subgroup.center L) ∈ Subgroup.zpowers z := by rw [htop]; trivial
    obtain ⟨k, hk⟩ := Submonoid.mem_powers_iff _ _ |>.1
      ((mem_powers_iff_mem_zpowers).2 hmem)
    exact ⟨k, by simpa using (congrArg Subtype.val hk).symm⟩

section ImgT

variable {V : Type} [CommGroup V]

theorem pow_apply_mul_inv_mem_imgT (z : MulAut V) (k : ℕ) (w : V) :
    (z ^ k) w * w⁻¹ ∈ imgT z := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : (z ^ (k + 1)) w * w⁻¹ =
        (z ((z ^ k) w) * ((z ^ k) w)⁻¹) * ((z ^ k) w * w⁻¹) := by
      rw [pow_succ', MulAut.mul_apply]
      cgroup
    rw [h1]
    exact (imgT z).mul_mem (mem_imgT.2 ⟨(z ^ k) w, rfl⟩) ih

theorem apply_mem_imgT_of_conj {z b : MulAut V} (h : ∃ k : ℕ, b * z * b⁻¹ = z ^ k) {t : V}
    (ht : t ∈ imgT z) : b t ∈ imgT z := by
  obtain ⟨k, hk⟩ := h
  obtain ⟨v, rfl⟩ := mem_imgT.1 ht
  have e : b (z v * v⁻¹) = (z ^ k) (b v) * (b v)⁻¹ := by
    rw [map_mul, map_inv, ← hk]
    simp [MulAut.mul_apply]
  rw [e]
  exact pow_apply_mul_inv_mem_imgT z k (b v)

theorem mem_stabSub_imgT {z a : MulAut V} (h1 : ∃ k : ℕ, a * z * a⁻¹ = z ^ k)
    (h2 : ∃ k : ℕ, a⁻¹ * z * a = z ^ k) : a ∈ stabSub (imgT z) := by
  intro u
  constructor
  · intro hu
    have := apply_mem_imgT_of_conj (b := a⁻¹) (by simpa using h2) hu
    simpa using this
  · exact apply_mem_imgT_of_conj h1

end ImgT

section Alt7

variable {V : Type} [CommGroup V] [Finite V]

theorem center_eq_bot_of_alt7 (hD : AsB42DichotomyNat) (hV : ∀ v : V, v ^ 2 = 1)
    {G A L : Subgroup (MulAut V)} (hA : IsFFStarOffender G A) (hLG : L ≤ G)
    (hLq : CFSG.IsQuasisimple ↥L) (hLA : ⁅L, A⁆ = L)
    (hodd : Odd (Nat.card ↥(Subgroup.center ↥L)))
    (hlist : CFSG.Milestones.SQTKSimpleList (↥L ⧸ Subgroup.center ↥L))
    (e7 : (↥L ⧸ Subgroup.center ↥L) ≃* alternatingGroup (Fin 7)) :
    Subgroup.center ↥L = ⊥ := by
  by_contra hc
  have hV2 : ∀ w : V, w * w = 1 := fun w => by simpa [pow_two] using hV w
  obtain ⟨zL, hzLc, hzL3, hzL1, hZpow⟩ := exists_generator_of_alt7 hLq hodd hc e7
  set z : MulAut V := (zL : MulAut V) with hz
  have hzL : z ∈ L := zL.2
  have hz3 : z ^ 3 = 1 := by simpa using congrArg Subtype.val hzL3
  have hz1 : z ≠ 1 := fun h => hzL1 (Subtype.ext h)
  have hzc : ∀ l : ↥L, (l : MulAut V) * z = z * (l : MulAut V) := fun l =>
    congrArg Subtype.val (Subgroup.mem_center_iff.1 hzLc l)
  have hAconj : ∀ a ∈ A, ∃ k : ℕ, a * z * a⁻¹ = z ^ k := by
    intro a ha
    have hcL : a * z * a⁻¹ ∈ L := conj_mem_of_commutator_eq hLA ha hzL
    have hcent : (⟨a * z * a⁻¹, hcL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro l
      apply Subtype.ext
      have hl' : a⁻¹ * (l : MulAut V) * a ∈ L := by
        simpa using conj_mem_of_commutator_eq hLA (A.inv_mem ha) l.2
      have h1 := hzc ⟨a⁻¹ * (l : MulAut V) * a, hl'⟩
      show (l : MulAut V) * (a * z * a⁻¹) = a * z * a⁻¹ * (l : MulAut V)
      calc (l : MulAut V) * (a * z * a⁻¹)
          = a * ((a⁻¹ * (l : MulAut V) * a) * z) * a⁻¹ := by group
        _ = a * (z * (a⁻¹ * (l : MulAut V) * a)) * a⁻¹ := by rw [h1]
        _ = a * z * a⁻¹ * (l : MulAut V) := by group
    obtain ⟨k, hk⟩ := hZpow _ hcent
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  set U : Subgroup V := imgT z with hU
  have hLU : L ≤ stabSub U := by
    intro l hl
    have hcomm : ∀ m ∈ L, m * z * m⁻¹ = z := fun m hm => by
      have := hzc ⟨m, hm⟩
      rw [this]
      group
    exact mem_stabSub_imgT ⟨1, by rw [pow_one]; exact hcomm l hl⟩
      ⟨1, by rw [pow_one]; simpa using hcomm l⁻¹ (L.inv_mem hl)⟩
  have hAU : A ≤ stabSub U := fun a ha =>
    mem_stabSub_imgT (hAconj a ha) (by simpa using hAconj a⁻¹ (A.inv_mem ha))
  have hUfix : ∀ u ∈ U, z u = u → u = 1 := fun u hu hzu =>
    eq_one_of_mem_imgT_fixed hV2 (by decide : Odd 3) hz3 hu hzu
  obtain ⟨v0, hv0⟩ : ∃ v : V, z v ≠ v := by
    by_contra h
    push Not at h
    exact hz1 (MulEquiv.ext h)
  have hu0U : z v0 * v0⁻¹ ∈ U := mem_imgT.2 ⟨v0, rfl⟩
  have hu01 : z v0 * v0⁻¹ ≠ 1 := fun h => hv0 (mul_inv_eq_one.1 h)
  have hzstab : z ∈ stabSub U := hLU hzL
  have hLnc : ¬ L ≤ centSub U := fun h =>
    hu01 (hUfix _ hu0U (mem_centSub.1 (h hzL) _ hu0U))
  set zU : MulAut ↥U := resHom U ⟨z, hzstab⟩ with hzU
  have hzmem : zU ∈ autSub L U := mem_autSub.2 ⟨⟨z, hzstab⟩, hzL, rfl⟩
  have hzU3 : zU ^ 3 = 1 := by
    rw [hzU, ← map_pow]
    have : (⟨z, hzstab⟩ : ↥(stabSub U)) ^ 3 = 1 := Subtype.ext hz3
    rw [this, map_one]
  have hzUne : zU ≠ 1 := by
    intro h1
    have h2 := congrArg (fun φ : MulAut ↥U => ((φ ⟨z v0 * v0⁻¹, hu0U⟩ : ↥U) : V)) h1
    exact hu01 (hUfix _ hu0U h2)
  have hnt : ¬ A ≤ centSub U := by
    intro hAc
    have hbot : autSub A U = ⊥ := by
      refine (Subgroup.eq_bot_iff_forall _).2 fun φ hφ => ?_
      obtain ⟨g, hgA, rfl⟩ := mem_autSub.1 hφ
      exact MulEquiv.ext fun u => Subtype.ext (mem_centSub.1 (hAc hgA) u u.2)
    have hcomm := B1Red.commutator_autSub_eq hLU hAU hLA
    rw [hbot, Subgroup.commutator_bot_right] at hcomm
    have : zU ∈ (⊥ : Subgroup (MulAut ↥U)) := by rw [hcomm]; exact hzmem
    exact hzUne (Subgroup.mem_bot.1 this)
  have hV' : ∀ v : ↥U, v ^ 2 = 1 := B1.sq_eq_one_sub hV U
  have hU2 : ∀ u : ↥U, u * u = 1 := fun u => by simpa [pow_two] using hV' u
  have hLo : CFSG.Open.IsQuasisimple ↥L := B1Red.isQuasisimple_to_open hLq
  have hLq' : CFSG.IsQuasisimple ↥(autSub L U) :=
    B1Red.isQuasisimple_of_open (B1Red.isQuasisimple_autSub hLU hLo hLnc)
  have hAU' : ∀ a ∈ A, ∀ w ∈ U, a w ∈ U := fun a ha w hw => (hAU ha w).2 hw
  have hA' := B1Red.isFFStarOffender_autSub hA hAU' hnt
  have hLG' : autSub L U ≤ autSub G U := autSub_mono hLG U
  have hLA' := B1Red.commutator_autSub_eq hLU hAU hLA
  obtain ⟨W, _, _, Lb, E, hW, hLbq, hirr, ⟨e1⟩, hEN, hE0, hel, hoff, ι, hι, I', hI0, hker'⟩ :=
    exists_section_module hV' hA' hLG' hLq' hLA'
  let zA : ↥(autSub L U) := ⟨zU, hzmem⟩
  have hzAc : ∀ φ : ↥(autSub L U), φ * zA = zA * φ := by
    intro φ
    obtain ⟨g, hgL, hg⟩ := mem_autSub.1 φ.2
    apply Subtype.ext
    show (φ : MulAut ↥U) * zU = zU * (φ : MulAut ↥U)
    rw [← hg, hzU, ← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext (hzc ⟨(g : MulAut V), hgL⟩))
  have hzAcenter : ι zA ∈ Subgroup.center ↥Lb := by
    rw [Subgroup.mem_center_iff]
    intro b
    obtain ⟨φ, rfl⟩ := hι b
    rw [← map_mul, ← map_mul, hzAc φ]
  have hzA1 : ι zA ≠ 1 := by
    intro h1
    have hall := hker' zA h1
    apply hI0
    rw [eq_bot_iff]
    intro w hw
    rw [Subgroup.mem_bot]
    have hfix : zU (zU w * w⁻¹) = zU w * w⁻¹ := (hall w hw) zU hzmem
    rw [map_mul, map_inv] at hfix
    have hbw : zU (zU w) = w := by
      calc zU (zU w) = (zU (zU w) * (zU w)⁻¹) * zU w := by cgroup
        _ = (zU w * w⁻¹) * zU w := by rw [hfix]
        _ = (zU w * zU w) * w⁻¹ := by cgroup
        _ = w⁻¹ := by rw [hU2, one_mul]
        _ = w := inv_eq_of_mul_eq_one_right (hU2 w)
    have h3 : zU (zU (zU w)) = w := by
      have := congrArg (fun m : MulAut ↥U => m w) hzU3
      simpa [pow_succ, MulAut.mul_apply] using this
    rw [hbw] at h3
    exact Subtype.ext (hUfix _ w.2 (congrArg Subtype.val h3))
  have hZb : Subgroup.center ↥Lb ≠ ⊥ := by
    intro hbot
    rw [hbot] at hzAcenter
    exact hzA1 (Subgroup.mem_bot.1 hzAcenter)
  have hψker : ((resHom U).comp (Subgroup.inclusion hLU)).ker ≠ ⊤ := by
    intro htop
    have hz' : ((resHom U).comp (Subgroup.inclusion hLU)) ⟨z, hzL⟩ = 1 := by
      have : (⟨z, hzL⟩ : ↥L) ∈ ((resHom U).comp (Subgroup.inclusion hLU)).ker := by
        rw [htop]; trivial
      exact this
    exact hzUne hz'
  have e2' : Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃*
      (↥(autSub L U) ⧸ Subgroup.center ↥(autSub L U))) := by
    rw [B1Red.autSub_eq_range hLU]
    exact equiv_centerQuotient_range hLo _ hψker
  obtain ⟨e2⟩ := e2'
  let eLb : (↥Lb ⧸ Subgroup.center ↥Lb) ≃* (↥L ⧸ Subgroup.center ↥L) := (e2.trans e1).symm
  have hlistLb : CFSG.Milestones.SQTKSimpleList (↥Lb ⧸ Subgroup.center ↥Lb) :=
    CFSG.QuasithinUnique.Ch1.sqtkSimpleList_of_mulEquiv eLb hlist
  have hres := hD W hW Lb hLbq hirr hlistLb E hEN hE0 hel hoff
  exact hZb (hres.2 ⟨eLb.trans e7⟩)

end Alt7

end CFSG.QuasithinUnique.Bridge.B113Det
