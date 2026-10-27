module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.AutAFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.NormalizerTQ
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.VEnd

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup SylowEnd CFSG.GroupTheory

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G} {S A B Aa D : Subgroup G}
  {z b : G}

theorem ThCyc.t_mem_normalizer_D (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) : t ∈ normalizer (D : Set G) :=
  le_normalizer_of_conj_mem hD.norm (H.t_mem_normalizer W W2 hD)

theorem ThCyc.t_mem_normalizer_omega1 (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) :
    t ∈ normalizer (omega1 D hD.comm : Set G) :=
  H.normalizer_le_normalizer_omega1 W W2 hD (H.t_mem_normalizer W W2 hD)

theorem ThCyc.vConj_t_mul_self (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) :
    vConj hD t * vConj hD t = 1 := by
  have ht : t ∈ normalizer (omega1 D hD.comm : Set G) := H.t_mem_normalizer_omega1 W W2 hD
  have h1 : t * t = 1 := by rw [← sq]; exact H.sq_t
  rw [← vConj_mul hD ht ht, h1, vConj_one]

theorem ThCyc.val_vConj_t_add_one_apply (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (x : VSub hD) :
    ((vConj hD t + 1) x).val = thV t x.val := by
  have ht : t ∈ normalizer (omega1 D hD.comm : Set G) := H.t_mem_normalizer_omega1 W W2 hD
  change (vConj hD t x + (1 : AddMonoid.End (VSub hD)) x).val = thV t x.val
  rw [AbelianSub.val_add, val_vConj_apply hD ht]
  simp only [AddMonoid.End.coe_one, id_eq, thV]
  exact H.omega1_comm W W2 hD (H.t_conj_mem_omega1 W W2 hD (AbelianSub.val_mem x))
    (AbelianSub.val_mem x)

private theorem ThCyc.VSub_add_self (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (x : VSub hD) : x + x = 0 := by
  apply AbelianSub.ext
  rw [AbelianSub.val_add, AbelianSub.val_zero]
  exact H.omega1_mul_self W W2 hD (AbelianSub.val_mem x)

private theorem ThCyc.vConj_t_add_one_mul_self (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) :
    (vConj hD t + 1) * (vConj hD t + 1) = 0 := by
  have hτ : vConj hD t * vConj hD t = 1 := H.vConj_t_mul_self W W2 hD
  have h1 : (1 : AddMonoid.End (VSub hD)) + 1 = 0 := VSub.add_self hD 1
  calc (vConj hD t + 1) * (vConj hD t + 1)
      = vConj hD t * vConj hD t + vConj hD t * 1 + 1 * vConj hD t + 1 * 1 := by
        noncomm_ring
    _ = 1 + vConj hD t + vConj hD t + 1 := by rw [hτ]; noncomm_ring
    _ = 0 := by
        rw [show (1 : AddMonoid.End (VSub hD)) + vConj hD t + vConj hD t + 1
            = (1 + 1) + (vConj hD t + vConj hD t) from by abel, h1,
          VSub.add_self hD (vConj hD t)]
        abel

private theorem ThCyc.mul_add_one_commute (hD : DHyp A Aa t D) {f : AddMonoid.End (VSub hD)}
    (h : f * vConj hD t = vConj hD t * f) :
    f * (vConj hD t + 1) = (vConj hD t + 1) * f := by
  calc f * (vConj hD t + 1) = f * vConj hD t + f * 1 := mul_add _ _ _
    _ = f * vConj hD t + f := by rw [mul_one]
    _ = vConj hD t * f + f := by rw [h]
    _ = vConj hD t * f + 1 * f := by rw [one_mul]
    _ = (vConj hD t + 1) * f := (add_mul _ _ _).symm

private theorem ThCyc.val_mem_A_of_val_mem_A (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    {f : AddMonoid.End (VSub hD)}
    (hfN : f * (vConj hD t + 1) = (vConj hD t + 1) * f)
    {x : VSub hD} (hx : x.val ∈ A) : (f x).val ∈ A := by
  have hsq : ∀ d ∈ D, d ^ 2 ∈ A := fun d hd => H.D_sq_mem_A_of_fourth W W2 hD h4 hd
  obtain ⟨v, hv, htv⟩ := H.thV_surj W W2 hD hsq x.val hx
  let y : VSub hD := AbelianSub.mk v hv
  have hNy : (vConj hD t + 1) y = x := by
    apply AbelianSub.ext
    rw [H.val_vConj_t_add_one_apply W W2 hD, AbelianSub.val_mk, htv]
  have hcomm : f ((vConj hD t + 1) y) = (vConj hD t + 1) (f y) := by
    have h := congrArg (fun e : AddMonoid.End (VSub hD) => e y) hfN
    simpa only [AddMonoid.End.coe_mul, Function.comp_apply] using h
  have hfx : f x = (vConj hD t + 1) (f y) := by rw [← hNy]; exact hcomm
  rw [hfx, H.val_vConj_t_add_one_apply W W2 hD]
  exact H.thV_mem_A W W2 hD (AbelianSub.val_mem (f y))

private theorem ThCyc.eq_zero_or_eq_vConj_t_add_one_of_kills_A
    (H : ThCyc G L R t) (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)
    (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    {f : AddMonoid.End (VSub hD)}
    (hfN : f * (vConj hD t + 1) = (vConj hD t + 1) * f)
    (hfH : ∀ n ∈ L ⊓ normalizer (A : Set G), vConj hD n * f = f * vConj hD n)
    (hfA0 : ∀ x : VSub hD, x.val ∈ A → f x = 0) :
    f = 0 ∨ f = vConj hD t + 1 := by
  classical
  have hsq : ∀ d ∈ D, d ^ 2 ∈ A := fun d hd => H.D_sq_mem_A_of_fourth W W2 hD h4 hd
  have hAV : A ≤ omega1 D hD.comm := H.A_le_omega1 W W2 hD
  let pre : ∀ a ∈ A, VSub hD := fun a ha =>
    AbelianSub.mk (Classical.choose (H.thV_surj W W2 hD hsq a ha))
      (Classical.choose_spec (H.thV_surj W W2 hD hsq a ha)).1
  have hpre : ∀ (a : G) (ha : a ∈ A), thV t (pre a ha).val = a := fun a ha => by
    dsimp only [pre]
    rw [AbelianSub.val_mk]
    exact (Classical.choose_spec (H.thV_surj W W2 hD hsq a ha)).2
  have hwell : ∀ (a : G) (ha : a ∈ A) (v : G) (hv : v ∈ omega1 D hD.comm),
      thV t v = a → f (AbelianSub.mk v hv) = f (pre a ha) := by
    intro a ha v hv hva
    have hwV : (pre a ha).val ∈ omega1 D hD.comm := AbelianSub.val_mem _
    have hw : thV t (pre a ha).val = a := hpre a ha
    have hmem : v * (pre a ha).val ∈ omega1 D hD.comm :=
      (omega1 D hD.comm).mul_mem hv hwV
    have h1 : thV t (v * (pre a ha).val) = 1 := by
      rw [H.thV_mul W W2 hD hv hwV, hva, hw]
      simpa [pow_two] using W.A_sq a ha
    have hA : v * (pre a ha).val ∈ A := (H.thV_eq_one_iff W W2 hD hmem).1 h1
    have hkill : f (AbelianSub.mk (v * (pre a ha).val) hmem) = 0 := hfA0 _ hA
    have hsum : (AbelianSub.mk v hv : VSub hD) + (AbelianSub.mk (pre a ha).val hwV : VSub hD) =
        (AbelianSub.mk (v * (pre a ha).val) hmem : VSub hD) := by
      apply AbelianSub.ext
      simp only [AbelianSub.val_add, AbelianSub.val_mk]
    have hsum0 : f (AbelianSub.mk v hv) + f (AbelianSub.mk (pre a ha).val hwV) = 0 := by
      rw [← map_add, hsum, hkill]
    have hpremk : AbelianSub.mk (pre a ha).val hwV = pre a ha := AbelianSub.mk_val _
    rw [hpremk] at hsum0
    have hself : f (pre a ha) + f (pre a ha) = 0 := H.VSub_add_self W W2 hD _
    calc f (AbelianSub.mk v hv) = f (AbelianSub.mk v hv) + 0 := (add_zero _).symm
      _ = f (AbelianSub.mk v hv) + (f (pre a ha) + f (pre a ha)) := by rw [hself]
      _ = (f (AbelianSub.mk v hv) + f (pre a ha)) + f (pre a ha) := by abel
      _ = 0 + f (pre a ha) := by rw [hsum0]
      _ = f (pre a ha) := zero_add _
  let h : G → G := fun a => if ha : a ∈ A then (f (pre a ha)).val else 1
  have hdef : ∀ (a : G) (ha : a ∈ A), h a = (f (pre a ha)).val := by
    intro a ha
    dsimp only [h]
    rw [dif_pos ha]
  have hNpre : ∀ (a : G) (ha : a ∈ A),
      (vConj hD t + 1) (pre a ha) = AbelianSub.mk a (hAV ha) := by
    intro a ha
    apply AbelianSub.ext
    rw [H.val_vConj_t_add_one_apply W W2 hD, hpre a ha, AbelianSub.val_mk]
  have hmemA : ∀ a ∈ A, h a ∈ A := by
    intro a ha
    have hNf : (vConj hD t + 1) (f (pre a ha)) = 0 := by
      calc (vConj hD t + 1) (f (pre a ha))
          = ((vConj hD t + 1) * f) (pre a ha) := by
              rw [AddMonoid.End.coe_mul]; rfl
        _ = (f * (vConj hD t + 1)) (pre a ha) := by rw [← hfN]
        _ = f ((vConj hD t + 1) (pre a ha)) := by
              rw [AddMonoid.End.coe_mul]; rfl
        _ = f (AbelianSub.mk a (hAV ha)) := by rw [hNpre a ha]
        _ = 0 := hfA0 _ ha
    have hval : thV t (f (pre a ha)).val = 1 := by
      have := congrArg AbelianSub.val hNf
      rwa [H.val_vConj_t_add_one_apply W W2 hD, AbelianSub.val_zero] at this
    rw [hdef a ha]
    exact (H.thV_eq_one_iff W W2 hD (AbelianSub.val_mem _)).1 hval
  have hmul : ∀ a ∈ A, ∀ a' ∈ A, h (a * a') = h a * h a' := by
    intro a ha a' ha'
    have hmem : (pre a ha).val * (pre a' ha').val ∈ omega1 D hD.comm :=
      (omega1 D hD.comm).mul_mem (AbelianSub.val_mem _) (AbelianSub.val_mem _)
    have hth : thV t ((pre a ha).val * (pre a' ha').val) = a * a' := by
      rw [H.thV_mul W W2 hD (AbelianSub.val_mem _) (AbelianSub.val_mem _),
        hpre a ha, hpre a' ha']
    have hpre' : f (AbelianSub.mk ((pre a ha).val * (pre a' ha').val) hmem) =
        f (pre (a * a') (A.mul_mem ha ha')) :=
      hwell (a * a') (A.mul_mem ha ha') _ hmem hth
    have hsum : pre a ha + pre a' ha' =
        AbelianSub.mk ((pre a ha).val * (pre a' ha').val) hmem := by
      calc pre a ha + pre a' ha'
          = AbelianSub.mk (pre a ha).val (AbelianSub.val_mem _) +
              AbelianSub.mk (pre a' ha').val (AbelianSub.val_mem _) := by
                rw [AbelianSub.mk_val (pre a ha), AbelianSub.mk_val (pre a' ha')]
        _ = AbelianSub.mk ((pre a ha).val * (pre a' ha').val) hmem := by
              rw [AbelianSub.mk_mul]
    calc h (a * a') = (f (pre (a * a') (A.mul_mem ha ha'))).val :=
          hdef (a * a') (A.mul_mem ha ha')
      _ = (f (AbelianSub.mk ((pre a ha).val * (pre a' ha').val) hmem)).val := by rw [hpre']
      _ = (f (pre a ha + pre a' ha')).val := by rw [← hsum]
      _ = (f (pre a ha) + f (pre a' ha')).val := by rw [map_add]
      _ = (f (pre a ha)).val * (f (pre a' ha')).val := AbelianSub.val_add _ _
      _ = h a * h a' := by rw [hdef a ha, hdef a' ha']
  have hconj : ∀ n ∈ L ⊓ normalizer (A : Set G), ∀ a ∈ A,
      h (n * a * n⁻¹) = n * h a * n⁻¹ := by
    intro n hn a ha
    have hnA : n * a * n⁻¹ ∈ A := (mem_normalizer_iff.1 hn.2 a).1 ha
    have hn' : n ∈ normInL L A := ⟨hn.1, fun x hx => (mem_normalizer_iff.1 hn.2 x).1 hx⟩
    have hnV : n ∈ normalizer (omega1 D hD.comm : Set G) :=
      H.normalizer_le_normalizer_omega1 W W2 hD
        (H.mem_normalizer_W5_of_mem_normInL W W2 hD hn')
    have hmem : n * (pre a ha).val * n⁻¹ ∈ omega1 D hD.comm :=
      (mem_normalizer_iff.1 hnV _).1 (AbelianSub.val_mem _)
    have hth : thV t (n * (pre a ha).val * n⁻¹) = n * a * n⁻¹ := by
      rw [H.thV_conj W W2 hD hn.1, hpre a ha]
    have hstep1 : f (pre (n * a * n⁻¹) hnA) = f (vConj hD n (pre a ha)) := by
      have h1 := hwell (n * a * n⁻¹) hnA _ hmem hth
      have h2 : AbelianSub.mk (n * (pre a ha).val * n⁻¹) hmem =
          vConj hD n (pre a ha) := by
        apply AbelianSub.ext
        rw [AbelianSub.val_mk, val_vConj_apply hD hnV, AbelianSub.val_mk]
      rw [h2] at h1
      exact h1.symm
    have hstep2 : f (vConj hD n (pre a ha)) = vConj hD n (f (pre a ha)) := by
      calc f (vConj hD n (pre a ha)) = (f * vConj hD n) (pre a ha) := by
              rw [AddMonoid.End.coe_mul]; rfl
        _ = (vConj hD n * f) (pre a ha) := by rw [← hfH n hn]
        _ = vConj hD n (f (pre a ha)) := by rw [AddMonoid.End.coe_mul]; rfl
    rw [hdef (n * a * n⁻¹) hnA, hstep1, hstep2, val_vConj_apply hD hnV, ← hdef a ha]
  have hf_eq : ∀ (y : VSub hD) (ha : thV t y.val ∈ A),
      f y = f (pre (thV t y.val) ha) := by
    intro y ha
    have hNy : (vConj hD t + 1) y = AbelianSub.mk (thV t y.val) (hAV ha) := by
      apply AbelianSub.ext
      rw [H.val_vConj_t_add_one_apply W W2 hD, AbelianSub.val_mk]
    have hdiffN : (vConj hD t + 1) (y - pre (thV t y.val) ha) = 0 := by
      rw [map_sub, hNy, hNpre (thV t y.val) ha, sub_self]
    have hdiffA : (y - pre (thV t y.val) ha).val ∈ A := by
      have hval : thV t (y - pre (thV t y.val) ha).val = 1 := by
        have := congrArg AbelianSub.val hdiffN
        rwa [H.val_vConj_t_add_one_apply W W2 hD, AbelianSub.val_zero] at this
      exact (H.thV_eq_one_iff W W2 hD (AbelianSub.val_mem _)).1 hval
    have hkill : f (y - pre (thV t y.val) ha) = 0 := hfA0 _ hdiffA
    have hsum : pre (thV t y.val) ha + (y - pre (thV t y.val) ha) = y := by abel
    have hy : y = pre (thV t y.val) ha + (y - pre (thV t y.val) ha) := hsum.symm
    calc f y = f (pre (thV t y.val) ha + (y - pre (thV t y.val) ha)) := congrArg f hy
      _ = f (pre (thV t y.val) ha) + f (y - pre (thV t y.val) ha) := map_add _ _ _
      _ = f (pre (thV t y.val) ha) + 0 := by rw [hkill]
      _ = f (pre (thV t y.val) ha) := add_zero _
  have hval_eq : ∀ (y : VSub hD) (ha : thV t y.val ∈ A),
      (f y).val = h (thV t y.val) := by
    intro y ha
    have h1 : (f y).val = (f (pre (thV t y.val) ha)).val := congrArg AbelianSub.val (hf_eq y ha)
    rw [h1]
    exact (hdef _ ha).symm
  rcases W.eq_one_or_eq_self_of_conj h hmemA hmul hconj with hone | hid
  · left
    apply AddMonoidHom.ext
    intro y
    have ha : thV t y.val ∈ A := H.thV_mem_A W W2 hD (AbelianSub.val_mem y)
    apply AbelianSub.ext
    show (f y).val = (0 : VSub hD).val
    rw [hval_eq y ha, hone _ ha]
    rfl
  · right
    apply AddMonoidHom.ext
    intro y
    have ha : thV t y.val ∈ A := H.thV_mem_A W W2 hD (AbelianSub.val_mem y)
    apply AbelianSub.ext
    show (f y).val = ((vConj hD t + 1) y).val
    rw [hval_eq y ha, hid _ ha, H.val_vConj_t_add_one_apply W W2 hD]

private theorem ThCyc.kills_A_or_fixes_A_of_commute (H : ThCyc G L R t)
    (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D)
    (h4 : ∀ d ∈ D, d ^ 4 = 1) {f : AddMonoid.End (VSub hD)}
    (hfH : ∀ n ∈ L ⊓ normalizer (A : Set G), vConj hD n * f = f * vConj hD n)
    (hft : vConj hD t * f = f * vConj hD t) :
    (∀ x : VSub hD, x.val ∈ A → f x = 0) ∨
      (∀ x : VSub hD, x.val ∈ A → f x = x) := by
  classical
  have hfN : f * (vConj hD t + 1) = (vConj hD t + 1) * f :=
    ThCyc.mul_add_one_commute hD hft.symm
  have hfA : ∀ x : VSub hD, x.val ∈ A → (f x).val ∈ A :=
    fun x hx => ThCyc.val_mem_A_of_val_mem_A H W W2 hD h4 hfN hx
  have hAV : A ≤ omega1 D hD.comm := H.A_le_omega1 W W2 hD
  let g : G → G := fun a => if ha : a ∈ A then (f (AbelianSub.mk a (hAV ha))).val else 1
  have hgdef : ∀ (a : G) (ha : a ∈ A), g a = (f (AbelianSub.mk a (hAV ha))).val := by
    intro a ha
    dsimp only [g]
    rw [dif_pos ha]
  have hgA : ∀ a ∈ A, g a ∈ A := by
    intro a ha
    rw [hgdef a ha]
    exact hfA _ ha
  have hgmul : ∀ a ∈ A, ∀ a' ∈ A, g (a * a') = g a * g a' := by
    intro a ha a' ha'
    have hsum : (AbelianSub.mk a (hAV ha) : VSub hD) + (AbelianSub.mk a' (hAV ha') : VSub hD) =
        (AbelianSub.mk (a * a') (hAV (A.mul_mem ha ha')) : VSub hD) := by
      apply AbelianSub.ext
      simp only [AbelianSub.val_add, AbelianSub.val_mk]
    rw [hgdef (a * a') (A.mul_mem ha ha'), hgdef a ha, hgdef a' ha']
    calc (f (AbelianSub.mk (a * a') (hAV (A.mul_mem ha ha')))).val
        = (f (AbelianSub.mk a (hAV ha) + AbelianSub.mk a' (hAV ha'))).val := by rw [← hsum]
      _ = (f (AbelianSub.mk a (hAV ha)) + f (AbelianSub.mk a' (hAV ha'))).val := by
            rw [map_add]
      _ = (f (AbelianSub.mk a (hAV ha))).val * (f (AbelianSub.mk a' (hAV ha'))).val :=
            AbelianSub.val_add _ _
  have hgconj : ∀ n ∈ L ⊓ normalizer (A : Set G), ∀ a ∈ A,
      g (n * a * n⁻¹) = n * g a * n⁻¹ := by
    intro n hn a ha
    have hnA : n * a * n⁻¹ ∈ A := (mem_normalizer_iff.1 hn.2 a).1 ha
    have hn' : n ∈ normInL L A := ⟨hn.1, fun x hx => (mem_normalizer_iff.1 hn.2 x).1 hx⟩
    have hnV : n ∈ normalizer (omega1 D hD.comm : Set G) :=
      H.normalizer_le_normalizer_omega1 W W2 hD
        (H.mem_normalizer_W5_of_mem_normInL W W2 hD hn')
    have hmk : AbelianSub.mk (n * a * n⁻¹) (hAV hnA) =
        vConj hD n (AbelianSub.mk a (hAV ha)) := by
      apply AbelianSub.ext
      rw [AbelianSub.val_mk, val_vConj_apply hD hnV, AbelianSub.val_mk]
    have happ : f (vConj hD n (AbelianSub.mk a (hAV ha))) =
        vConj hD n (f (AbelianSub.mk a (hAV ha))) := by
      calc f (vConj hD n (AbelianSub.mk a (hAV ha)))
          = (f * vConj hD n) (AbelianSub.mk a (hAV ha)) := by
              rw [AddMonoid.End.coe_mul]; rfl
        _ = (vConj hD n * f) (AbelianSub.mk a (hAV ha)) := by rw [← hfH n hn]
        _ = vConj hD n (f (AbelianSub.mk a (hAV ha))) := by
              rw [AddMonoid.End.coe_mul]; rfl
    rw [hgdef (n * a * n⁻¹) hnA, hmk, happ, val_vConj_apply hD hnV, hgdef a ha]
  rcases W.eq_one_or_eq_self_of_conj g hgA hgmul hgconj with hone | hid
  · left
    intro x hx
    have hxmk : x = AbelianSub.mk x.val (hAV hx) := by
      apply AbelianSub.ext
      rw [AbelianSub.val_mk]
    rw [hxmk]
    apply AbelianSub.ext
    rw [show (f (AbelianSub.mk x.val (hAV hx))).val = g x.val from (hgdef x.val hx).symm,
      hone x.val hx]
    rfl
  · right
    intro x hx
    have hxmk : x = AbelianSub.mk x.val (hAV hx) := by
      apply AbelianSub.ext
      rw [AbelianSub.val_mk]
    rw [hxmk]
    apply AbelianSub.ext
    rw [show (f (AbelianSub.mk x.val (hAV hx))).val = g x.val from (hgdef x.val hx).symm,
      hid x.val hx]
    rw [AbelianSub.val_mk]

theorem ThCyc.end_cases_of_commute (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    {f : AddMonoid.End (VSub hD)}
    (hfH : ∀ n ∈ L ⊓ normalizer (A : Set G), vConj hD n * f = f * vConj hD n)
    (hft : vConj hD t * f = f * vConj hD t) :
    f = 0 ∨ f = 1 ∨ f = vConj hD t + 1 ∨ f = vConj hD t := by
  have hfN : f * (vConj hD t + 1) = (vConj hD t + 1) * f :=
    ThCyc.mul_add_one_commute hD hft.symm
  rcases H.kills_A_or_fixes_A_of_commute W W2 hD h4 hfH hft with hkill | hfix
  · rcases ThCyc.eq_zero_or_eq_vConj_t_add_one_of_kills_A H W W2 hD h4 hfN hfH hkill with
      h0 | hN
    · exact Or.inl h0
    · exact Or.inr (Or.inr (Or.inl hN))
  · have hf1N : (f + 1) * (vConj hD t + 1) = (vConj hD t + 1) * (f + 1) := by
      calc (f + 1) * (vConj hD t + 1)
          = f * (vConj hD t + 1) + 1 * (vConj hD t + 1) := add_mul _ _ _
        _ = (vConj hD t + 1) * f + (vConj hD t + 1) := by rw [hfN, one_mul]
        _ = (vConj hD t + 1) * f + (vConj hD t + 1) * 1 := by rw [mul_one]
        _ = (vConj hD t + 1) * (f + 1) := (mul_add _ _ _).symm
    have hf1H : ∀ n ∈ L ⊓ normalizer (A : Set G),
        vConj hD n * (f + 1) = (f + 1) * vConj hD n := by
      intro n hn
      calc vConj hD n * (f + 1) = vConj hD n * f + vConj hD n * 1 := mul_add _ _ _
        _ = f * vConj hD n + vConj hD n := by rw [hfH n hn, mul_one]
        _ = f * vConj hD n + 1 * vConj hD n := by rw [one_mul]
        _ = (f + 1) * vConj hD n := (add_mul _ _ _).symm
    have hf1A0 : ∀ x : VSub hD, x.val ∈ A → (f + 1) x = 0 := by
      intro x hx
      have hx' : f x = x := hfix x hx
      have h1x : (1 : AddMonoid.End (VSub hD)) x = x := rfl
      change f x + (1 : AddMonoid.End (VSub hD)) x = 0
      rw [hx', h1x]
      exact H.VSub_add_self W W2 hD x
    rcases ThCyc.eq_zero_or_eq_vConj_t_add_one_of_kills_A H W W2 hD h4 hf1N hf1H hf1A0 with
      h0 | hN
    · refine Or.inr (Or.inl ?_)
      calc f = (f + 1) + 1 := by rw [add_assoc, VSub.add_self hD 1, add_zero]
        _ = 0 + 1 := by rw [h0]
        _ = 1 := zero_add 1
    · refine Or.inr (Or.inr (Or.inr ?_))
      calc f = (f + 1) + 1 := by rw [add_assoc, VSub.add_self hD 1, add_zero]
        _ = (vConj hD t + 1) + 1 := by rw [hN]
        _ = vConj hD t := by rw [add_assoc, VSub.add_self hD 1, add_zero]

theorem ThCyc.eq_one_or_eq_vConj_t (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    {f : AddMonoid.End (VSub hD)}
    (hfH : ∀ n ∈ L ⊓ normalizer (A : Set G), vConj hD n * f = f * vConj hD n)
    (hft : vConj hD t * f = f * vConj hD t)
    (hfA : ∀ x : VSub hD, x.val ∈ A → f x = x) :
    f = 1 ∨ f = vConj hD t := by
  have hcases := H.end_cases_of_commute W W2 hD h4 hfH hft
  have hzV : z ∈ omega1 D hD.comm := H.A_le_omega1 W W2 hD W.z_mem_A
  have hz0 : AbelianSub.mk z hzV ≠ (0 : VSub hD) := by
    intro h
    have h' := congrArg AbelianSub.val h
    rw [AbelianSub.val_mk, AbelianSub.val_zero] at h'
    exact W.z_ne_one h'
  have hfz : f (AbelianSub.mk z hzV) = AbelianSub.mk z hzV := hfA _ W.z_mem_A
  rcases hcases with h0 | h1 | hN | hτ
  · exfalso
    have h' : (0 : VSub hD) = AbelianSub.mk z hzV := by
      calc (0 : VSub hD) = (0 : AddMonoid.End (VSub hD)) (AbelianSub.mk z hzV) := rfl
        _ = f (AbelianSub.mk z hzV) := by rw [h0]
        _ = AbelianSub.mk z hzV := hfz
    exact hz0 h'.symm
  · exact Or.inl h1
  · exfalso
    have hNz : (vConj hD t + 1) (AbelianSub.mk z hzV) = (0 : VSub hD) := by
      apply AbelianSub.ext
      rw [H.val_vConj_t_add_one_apply W W2 hD, AbelianSub.val_mk, AbelianSub.val_zero]
      exact (H.thV_eq_one_iff W W2 hD hzV).2 W.z_mem_A
    rw [hN] at hfz
    exact hz0 (hNz.symm.trans hfz).symm
  · exact Or.inr hτ

theorem ThCyc.vConj_commute_t (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) {m : G} (hm : m ∈ normalizer (D : Set G)) :
    vConj hD m * vConj hD t = vConj hD t * vConj hD m := by
  have htV : t ∈ normalizer (omega1 D hD.comm : Set G) := H.t_mem_normalizer_omega1 W W2 hD
  have hmV : m ∈ normalizer (omega1 D hD.comm : Set G) :=
    normalizer_D_le_normalizer_omega1 hD hm
  rcases H.mem_M0_or_inv_t_mul_mem_M0 W W2 hD h4 hb hm with hm0 | hm0
  · obtain ⟨n, hn, hact⟩ := ThCyc.exists_mem_inf_normalizer_conj_eq_of_mem_M0 hD hm0
    have hn' : n ∈ normInL L A := ⟨hn.1, fun x hx => (mem_normalizer_iff.1 hn.2 x).1 hx⟩
    have hnV : n ∈ normalizer (omega1 D hD.comm : Set G) :=
      H.normalizer_le_normalizer_omega1 W W2 hD
        (H.mem_normalizer_W5_of_mem_normInL W W2 hD hn')
    have hmn : vConj hD m = vConj hD n := by
      apply AbelianSub.end_ext
      intro x
      rw [val_vConj_apply hD hmV, val_vConj_apply hD hnV]
      exact hact x.val (AbelianSub.val_mem x)
    have hnt : n * t = t * n := (H.comm_of_mem_L hn.1).symm
    have hcomm : vConj hD n * vConj hD t = vConj hD t * vConj hD n := by
      rw [← vConj_mul hD hnV htV, ← vConj_mul hD htV hnV, hnt]
    rw [hmn]
    exact hcomm
  · obtain ⟨n, hn, hact⟩ := ThCyc.exists_mem_inf_normalizer_conj_eq_of_mem_M0 hD hm0
    have hn' : n ∈ normInL L A := ⟨hn.1, fun x hx => (mem_normalizer_iff.1 hn.2 x).1 hx⟩
    have hnV : n ∈ normalizer (omega1 D hD.comm : Set G) :=
      H.normalizer_le_normalizer_omega1 W W2 hD
        (H.mem_normalizer_W5_of_mem_normInL W W2 hD hn')
    have hqD : t⁻¹ * m ∈ normalizer (D : Set G) := hm0.1
    have hqV : t⁻¹ * m ∈ normalizer (omega1 D hD.comm : Set G) :=
      normalizer_D_le_normalizer_omega1 hD hqD
    have hmn : vConj hD m = vConj hD t * vConj hD n := by
      have hm_eq : m = t * (t⁻¹ * m) := by group
      rw [hm_eq, vConj_mul hD htV hqV]
      congr 1
      apply AbelianSub.end_ext
      intro x
      rw [val_vConj_apply hD hqV, val_vConj_apply hD hnV]
      exact hact x.val (AbelianSub.val_mem x)
    have hnt : n * t = t * n := (H.comm_of_mem_L hn.1).symm
    have hcomm : vConj hD n * vConj hD t = vConj hD t * vConj hD n := by
      rw [← vConj_mul hD hnV htV, ← vConj_mul hD htV hnV, hnt]
    rw [hmn, mul_assoc, hcomm]

private theorem ThCyc.vConj_t_add_one_ne_zero (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1) :
    vConj hD t + 1 ≠ 0 := by
  intro h
  have hsq : ∀ d ∈ D, d ^ 2 ∈ A := fun d hd => H.D_sq_mem_A_of_fourth W W2 hD h4 hd
  have hVA : omega1 D hD.comm ≤ A := by
    intro v hv
    have h1 : (vConj hD t + 1) (AbelianSub.mk v hv) = (0 : VSub hD) := by rw [h]; rfl
    have h2 : thV t v = 1 := by
      have h' := congrArg AbelianSub.val h1
      rwa [H.val_vConj_t_add_one_apply W W2 hD, AbelianSub.val_mk, AbelianSub.val_zero] at h'
    exact (H.thV_eq_one_iff W W2 hD hv).1 h2
  have hcard := Subgroup.card_le_of_le hVA
  rw [H.card_omega1 W W2 hD hsq, W.A_card] at hcard
  norm_num at hcard

private theorem ThCyc.end_one_ne_zero (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) :
    (1 : AddMonoid.End (VSub hD)) ≠ 0 := by
  have hzV : z ∈ omega1 D hD.comm := H.A_le_omega1 W W2 hD W.z_mem_A
  have hz0 : AbelianSub.mk z hzV ≠ (0 : VSub hD) := by
    intro h
    have h' := congrArg AbelianSub.val h
    rw [AbelianSub.val_mk, AbelianSub.val_zero] at h'
    exact W.z_ne_one h'
  intro h
  have h1 : AbelianSub.mk z hzV = (0 : VSub hD) := by
    calc AbelianSub.mk z hzV = (1 : AddMonoid.End (VSub hD)) (AbelianSub.mk z hzV) := rfl
      _ = (0 : AddMonoid.End (VSub hD)) (AbelianSub.mk z hzV) := by rw [h]
      _ = (0 : VSub hD) := rfl
  exact hz0 h1

theorem tau_cases_of_char_two {R : Type*} [Ring R] (h2 : ∀ x : R, x + x = 0) {τ β w : R}
    (hτ : τ * τ = 1) (hβ : β = 1 ∨ β = τ) (hw0 : w ≠ 0) (hwβ : w ≠ β)
    (hτw : τ * w * τ = w ∨ τ * w * τ = w + β)
    (hCE : ∀ f : R, (f = w ∨ f = w * w + w) → f * τ = τ * f →
      f = 0 ∨ f = 1 ∨ f = τ + 1 ∨ f = τ) :
    (τ = β ∨ τ = w ∨ τ = w + β) ∨
      (β = 1 ∧ τ * w * τ = w + 1 ∧ (w * w = w ∨ w * w = w + 1)) := by
  rcases hβ with hβ | hβ
  · subst hβ
    rcases hτw with hw | hw
    · have hwτ : w * τ = τ * w := by
        calc w * τ = (τ * τ) * w * τ := by rw [hτ, one_mul]
          _ = τ * (τ * w * τ) := by noncomm_ring
          _ = τ * w := by rw [hw]
      rcases hCE w (Or.inl rfl) hwτ with h | h | h | h
      · exact absurd h hw0
      · exact absurd h hwβ
      · exact Or.inl (Or.inr (Or.inr (by
          rw [h, add_assoc, h2 1, add_zero])))
      · exact Or.inl (Or.inr (Or.inl h.symm))
    · let u := w * w + w
      have hu : τ * u * τ = u := by
        have hww : τ * (w * w) * τ = (w + 1) * (w + 1) := by
          calc τ * (w * w) * τ = (τ * w * τ) * (τ * w * τ) := by
                rw [show (τ * w * τ) * (τ * w * τ) = τ * w * (τ * τ) * w * τ from by
                  noncomm_ring, hτ]
                noncomm_ring
            _ = (w + 1) * (w + 1) := by rw [hw]
        have hsq : (w + 1) * (w + 1) = w * w + 1 := by
          calc (w + 1) * (w + 1) = w * w + w + w + 1 := by noncomm_ring
            _ = w * w + (w + w) + 1 := by abel
            _ = w * w + 0 + 1 := by rw [h2 w]
            _ = w * w + 1 := by abel
        calc τ * u * τ = τ * (w * w) * τ + τ * w * τ := by
              dsimp only [u]; noncomm_ring
          _ = (w * w + 1) + (w + 1) := by rw [hww, hsq, hw]
          _ = w * w + w := by
              rw [show w * w + 1 + (w + 1) = w * w + w + (1 + 1) from by abel, h2 1]
              abel
      have hu_comm : u * τ = τ * u := by
        calc u * τ = (τ * u * τ) * τ := by rw [hu]
          _ = τ * u * (τ * τ) := by noncomm_ring
          _ = τ * u := by rw [hτ, mul_one]
      rcases hCE u (Or.inr rfl) hu_comm with hu0 | hu1 | huτ1 | huτ
      · dsimp only [u] at hu0
        right
        refine ⟨rfl, hw, Or.inl ?_⟩
        calc w * w = w * w + 0 := (add_zero _).symm
          _ = w * w + (w + w) := by rw [h2 w]
          _ = (w * w + w) + w := by abel
          _ = 0 + w := by rw [hu0]
          _ = w := zero_add w
      · dsimp only [u] at hu1
        right
        refine ⟨rfl, hw, Or.inr ?_⟩
        calc w * w = w * w + 0 := (add_zero _).symm
          _ = w * w + (w + w) := by rw [h2 w]
          _ = (w * w + w) + w := by abel
          _ = 1 + w := by rw [hu1]
          _ = w + 1 := by abel
      · exfalso
        dsimp only [u] at huτ1
        have hτeq : τ = w * w + w + 1 := by
          calc τ = (τ + 1) + 1 := by rw [add_assoc, h2 1, add_zero]
            _ = (w * w + w) + 1 := by rw [← huτ1]
        have hcomm : τ * w = w * τ := by
          rw [hτeq]; noncomm_ring
        have hw1 : w + 1 = w := by
          calc w + 1 = τ * w * τ := hw.symm
            _ = w * (τ * τ) := by rw [hcomm]; noncomm_ring
            _ = w := by rw [hτ, mul_one]
        have h10 : (1 : R) = 0 := by
          calc (1 : R) = 1 + (w + w) := by rw [h2 w, add_zero]
            _ = (w + 1) + w := by abel
            _ = w + w := by rw [hw1]
            _ = 0 := h2 w
        exact hw0 (by
          calc w = w * 1 := (mul_one w).symm
            _ = w * 0 := by rw [h10]
            _ = 0 := mul_zero w)
      · exfalso
        dsimp only [u] at huτ
        have hτeq : τ = w * w + w := huτ.symm
        have hcomm : τ * w = w * τ := by
          rw [hτeq]; noncomm_ring
        have hw1 : w + 1 = w := by
          calc w + 1 = τ * w * τ := hw.symm
            _ = w * (τ * τ) := by rw [hcomm]; noncomm_ring
            _ = w := by rw [hτ, mul_one]
        have h10 : (1 : R) = 0 := by
          calc (1 : R) = 1 + (w + w) := by rw [h2 w, add_zero]
            _ = (w + 1) + w := by abel
            _ = w + w := by rw [hw1]
            _ = 0 := h2 w
        exact hw0 (by
          calc w = w * 1 := (mul_one w).symm
            _ = w * 0 := by rw [h10]
            _ = 0 := mul_zero w)
  · subst hβ
    exact Or.inl (Or.inl rfl)

theorem ThCyc.false_of_vConj_t_mem (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) {Q : Subgroup G} (hQ : QHyp L A D t Q) {g : G}
    (hgQ : ∀ q ∈ Q, g * q * g⁻¹ ∈ Q)
    (hgV : g ∈ normalizer (omega1 D hD.comm : Set G))
    (hgu : g⁻¹ * t * g ∈ normalizer (D : Set G))
    (hgM : g ∉ normalizer (D : Set G))
    {𝒲 : Set (AddMonoid.End (VSub hD))}
    (h𝒲g : ∀ f ∈ 𝒲, vConj hD g⁻¹ * f * vConj hD g ∈ 𝒲)
    (h𝒲H : ∀ f ∈ 𝒲, ∀ n ∈ L ⊓ normalizer (A : Set G), vConj hD n * f = f * vConj hD n)
    (hτ : vConj hD t ∈ 𝒲) : False := by
  have htV : t ∈ normalizer (omega1 D hD.comm : Set G) := H.t_mem_normalizer_omega1 W W2 hD
  have hgVinv : g⁻¹ ∈ normalizer (omega1 D hD.comm : Set G) :=
    (normalizer (omega1 D hD.comm : Set G)).inv_mem hgV
  have huV : g⁻¹ * t * g ∈ normalizer (omega1 D hD.comm : Set G) :=
    normalizer_D_le_normalizer_omega1 hD hgu
  set F : AddMonoid.End (VSub hD) := vConj hD g⁻¹ * vConj hD t * vConj hD g with hFdef
  have hFW : F ∈ 𝒲 := by
    rw [hFdef]
    exact h𝒲g _ hτ
  have hFH : ∀ n ∈ L ⊓ normalizer (A : Set G), vConj hD n * F = F * vConj hD n :=
    fun n hn => h𝒲H F hFW n hn
  have hFeq : F = vConj hD (g⁻¹ * t * g) := by
    rw [hFdef, ← vConj_mul hD hgVinv htV,
      ← vConj_mul hD ((normalizer (omega1 D hD.comm : Set G)).mul_mem hgVinv htV) hgV]
  have hFt : F * vConj hD t = vConj hD t * F := by
    rw [hFeq]
    exact H.vConj_commute_t W W2 hD h4 hb hgu
  have hFsq : F * F = 1 := by
    rw [hFeq]
    have huu : (g⁻¹ * t * g) * (g⁻¹ * t * g) = 1 := by
      have ht2 : t * t = 1 := by rw [← sq]; exact H.sq_t
      calc (g⁻¹ * t * g) * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
        _ = 1 := by rw [ht2]; group
    rw [← vConj_mul hD huV huV, huu, vConj_one]
  have h1ne0 : (1 : AddMonoid.End (VSub hD)) ≠ 0 := H.end_one_ne_zero W W2 hD
  have hNne0 : vConj hD t + 1 ≠ 0 := H.vConj_t_add_one_ne_zero W W2 hD h4
  have hNN : (vConj hD t + 1) * (vConj hD t + 1) = 0 :=
    H.vConj_t_add_one_mul_self W W2 hD
  have hFne0 : F ≠ 0 := by
    intro h
    have h' : F * F = 0 := by rw [h, zero_mul]
    rw [hFsq] at h'
    exact h1ne0 h'
  have hFneN : F ≠ vConj hD t + 1 := by
    intro h
    have h' : F * F = 0 := by rw [h, hNN]
    rw [hFsq] at h'
    exact h1ne0 h'
  have hconjF : vConj hD g * F * vConj hD g⁻¹ = vConj hD t := by
    calc vConj hD g * F * vConj hD g⁻¹
        = vConj hD g * (vConj hD g⁻¹ * vConj hD t * vConj hD g) * vConj hD g⁻¹ := by
            rw [hFdef]
      _ = (vConj hD g * vConj hD g⁻¹) * vConj hD t * (vConj hD g * vConj hD g⁻¹) := by
            noncomm_ring
      _ = vConj hD t := by rw [vConj_mul_inv hD hgV]; noncomm_ring
  rcases H.end_cases_of_commute W W2 hD h4 hFH hFt.symm with h0 | h1 | hN | hτF
  · exact hFne0 h0
  · have hτ1 : vConj hD t = 1 := by
      have h2 := hconjF
      rw [h1, mul_one, vConj_mul_inv hD hgV] at h2
      exact h2.symm
    exact hNne0 (by rw [hτ1]; exact VSub.add_self hD 1)
  · exact hFneN hN
  · have hcommg : vConj hD g * vConj hD t = vConj hD t * vConj hD g := by
      have h2 := hconjF
      rw [hτF] at h2
      calc vConj hD g * vConj hD t
          = vConj hD g * vConj hD t * (vConj hD g⁻¹ * vConj hD g) := by
              rw [vConj_inv_mul hD hgV, mul_one]
        _ = (vConj hD g * vConj hD t * vConj hD g⁻¹) * vConj hD g := by noncomm_ring
        _ = vConj hD t * vConj hD g := by rw [h2]
    have hcommN : vConj hD g * (vConj hD t + 1) = (vConj hD t + 1) * vConj hD g :=
      ThCyc.mul_add_one_commute hD hcommg
    have hgA : ∀ a ∈ A, g * a * g⁻¹ ∈ A := by
      intro a ha
      have hsq : ∀ d ∈ D, d ^ 2 ∈ A := fun d hd => H.D_sq_mem_A_of_fourth W W2 hD h4 hd
      have hAV : A ≤ omega1 D hD.comm := H.A_le_omega1 W W2 hD
      obtain ⟨v, hv, htv⟩ := H.thV_surj W W2 hD hsq a ha
      have hmemV : g * v * g⁻¹ ∈ omega1 D hD.comm := (mem_normalizer_iff.1 hgV v).1 hv
      have hNx : (vConj hD t + 1) (AbelianSub.mk v hv) = AbelianSub.mk a (hAV ha) := by
        apply AbelianSub.ext
        rw [H.val_vConj_t_add_one_apply W W2 hD, AbelianSub.val_mk, htv, AbelianSub.val_mk]
      have h1g : vConj hD g (AbelianSub.mk a (hAV ha)) =
          AbelianSub.mk (g * a * g⁻¹) ((mem_normalizer_iff.1 hgV a).1 (hAV ha)) := by
        apply AbelianSub.ext
        rw [val_vConj_apply hD hgV, AbelianSub.val_mk, AbelianSub.val_mk]
      have h2g : vConj hD g (AbelianSub.mk v hv) =
          AbelianSub.mk (g * v * g⁻¹) hmemV := by
        apply AbelianSub.ext
        rw [val_vConj_apply hD hgV, AbelianSub.val_mk, AbelianSub.val_mk]
      have heq : AbelianSub.mk (g * a * g⁻¹) ((mem_normalizer_iff.1 hgV a).1 (hAV ha)) =
          (vConj hD t + 1) (AbelianSub.mk (g * v * g⁻¹) hmemV) := by
        calc AbelianSub.mk (g * a * g⁻¹) ((mem_normalizer_iff.1 hgV a).1 (hAV ha))
            = vConj hD g (AbelianSub.mk a (hAV ha)) := h1g.symm
          _ = vConj hD g ((vConj hD t + 1) (AbelianSub.mk v hv)) := by rw [hNx]
          _ = (vConj hD t + 1) (vConj hD g (AbelianSub.mk v hv)) := by
                have h := congrArg (fun e : AddMonoid.End (VSub hD) =>
                  e (AbelianSub.mk v hv)) hcommN
                simpa only [AddMonoid.End.coe_mul, Function.comp_apply] using h
          _ = (vConj hD t + 1) (AbelianSub.mk (g * v * g⁻¹) hmemV) := by rw [h2g]
      have hvalA : ((vConj hD t + 1) (AbelianSub.mk (g * v * g⁻¹) hmemV)).val ∈ A := by
        rw [H.val_vConj_t_add_one_apply W W2 hD, AbelianSub.val_mk]
        exact H.thV_mem_A W W2 hD hmemV
      rw [← heq] at hvalA
      rwa [AbelianSub.val_mk] at hvalA
    exact hgM (QHyp.mem_normalizer_D_of_conj_mem_A H W W2 hD h4 hQ hgQ hgA)

end CFSG.EvenSporadicStandard.ThStd
