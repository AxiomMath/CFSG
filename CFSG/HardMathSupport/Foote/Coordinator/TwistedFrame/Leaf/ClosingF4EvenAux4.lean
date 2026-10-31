module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingF4EvenAux3

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.F4Even

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4

set_option linter.unusedSectionVars false


section SigFixed

open T7

variable {L : Type} [Field L] [CharP L 2] {Fr : L →+* L}

theorem sig_root_fixed {β : Fin Tag.F4.rank → ℤ} (hβ : IsRoot Tag.F4 β) (hw : wF4 • β = β) {c : L}
    (hc : Fr c = c) : sigHom Fr (pinnedX Tag.F4 L β c) = pinnedX Tag.F4 L β c := by
  rw [sigHom_pinnedX Fr hβ, hw, hc]

theorem sig_g5 {c : L} (hc : Fr c = c) :
    sigHom Fr (pinnedX Tag.F4 L g5 c) = pinnedX Tag.F4 L g5 c :=
  sig_root_fixed isRoot_g5 w_g5 hc

theorem sig_g5n {c : L} (hc : Fr c = c) :
    sigHom Fr (pinnedX Tag.F4 L g5n c) = pinnedX Tag.F4 L g5n c :=
  sig_root_fixed isRoot_g5n w_g5n hc

theorem sig_th {c : L} (hc : Fr c = c) :
    sigHom Fr (pinnedX Tag.F4 L (highRoot Tag.F4) c) = pinnedX Tag.F4 L (highRoot Tag.F4) c :=
  sig_root_fixed isRoot_theta w_smul_theta hc

theorem sig_thn {c : L} (hc : Fr c = c) :
    sigHom Fr (pinnedX Tag.F4 L (-highRoot Tag.F4) c) = pinnedX Tag.F4 L (-highRoot Tag.F4) c :=
  sig_root_fixed (IsRoot.neg isRoot_theta) (by rw [smul_neg, w_smul_theta]) hc

theorem sig_u {s c : L} (hs : Fr (Fr s) = s) (hc : c + Fr c = s * Fr s) :
    sigHom Fr (pinnedX Tag.F4 L a3 s * pinnedX Tag.F4 L a4 (Fr s) * pinnedX Tag.F4 L g5 c) =
      pinnedX Tag.F4 L a3 s * pinnedX Tag.F4 L a4 (Fr s) * pinnedX Tag.F4 L g5 c := by
  rw [map_mul, map_mul, sigHom_pinnedX Fr isRoot_a3, sigHom_pinnedX Fr isRoot_a4,
    sigHom_pinnedX Fr isRoot_g5, w_a3, w_a4, w_g5, hs, rel_a4_a3 (Fr s) s]
  have hcm : Commute (pinnedX Tag.F4 L g5 (Fr s * s))
      (pinnedX Tag.F4 L a3 s * pinnedX Tag.F4 L a4 (Fr s)) :=
    (commute_g5_a3 _ _).mul_right (commute_g5_a4 _ _)
  have hcc : Fr s * s + Fr c = c := by
    linear_combination -hc + Fr c * CharTwo.two_eq_zero (R := L)
  calc pinnedX Tag.F4 L g5 (Fr s * s) * (pinnedX Tag.F4 L a3 s * pinnedX Tag.F4 L a4 (Fr s)) *
        pinnedX Tag.F4 L g5 (Fr c)
      = (pinnedX Tag.F4 L a3 s * pinnedX Tag.F4 L a4 (Fr s)) * pinnedX Tag.F4 L g5 (Fr s * s) *
        pinnedX Tag.F4 L g5 (Fr c) := by rw [hcm.eq]
    _ = (pinnedX Tag.F4 L a3 s * pinnedX Tag.F4 L a4 (Fr s)) *
        (pinnedX Tag.F4 L g5 (Fr s * s) * pinnedX Tag.F4 L g5 (Fr c)) := by rw [mul_assoc]
    _ = (pinnedX Tag.F4 L a3 s * pinnedX Tag.F4 L a4 (Fr s)) *
        pinnedX Tag.F4 L g5 (Fr s * s + Fr c) := by rw [pinnedX_add]
    _ = _ := by rw [hcc]

theorem sig_r {b z : L} (hb : Fr (Fr b) = b) (hz : z + Fr z = b * Fr b) :
    sigHom Fr (pinnedX Tag.F4 L rS b * pinnedX Tag.F4 L pS (Fr b) *
        pinnedX Tag.F4 L (highRoot Tag.F4) z) =
      pinnedX Tag.F4 L rS b * pinnedX Tag.F4 L pS (Fr b) * pinnedX Tag.F4 L (highRoot Tag.F4) z := by
  rw [map_mul, map_mul, sigHom_pinnedX Fr isRoot_rS, sigHom_pinnedX Fr isRoot_pS,
    sigHom_pinnedX Fr isRoot_theta, w_rS, w_pS, w_smul_theta, hb, rel_pS_rS (Fr b) b]
  have hcm : Commute (pinnedX Tag.F4 L (highRoot Tag.F4) (Fr b * b))
      (pinnedX Tag.F4 L rS b * pinnedX Tag.F4 L pS (Fr b)) :=
    (commute_theta_rS _ _).mul_right (commute_theta_pS _ _)
  have hcc : Fr b * b + Fr z = z := by
    linear_combination -hz + Fr z * CharTwo.two_eq_zero (R := L)
  calc pinnedX Tag.F4 L (highRoot Tag.F4) (Fr b * b) *
        (pinnedX Tag.F4 L rS b * pinnedX Tag.F4 L pS (Fr b)) *
        pinnedX Tag.F4 L (highRoot Tag.F4) (Fr z)
      = (pinnedX Tag.F4 L rS b * pinnedX Tag.F4 L pS (Fr b)) *
        pinnedX Tag.F4 L (highRoot Tag.F4) (Fr b * b) *
        pinnedX Tag.F4 L (highRoot Tag.F4) (Fr z) := by rw [hcm.eq]
    _ = (pinnedX Tag.F4 L rS b * pinnedX Tag.F4 L pS (Fr b)) *
        (pinnedX Tag.F4 L (highRoot Tag.F4) (Fr b * b) *
          pinnedX Tag.F4 L (highRoot Tag.F4) (Fr z)) := by rw [mul_assoc]
    _ = (pinnedX Tag.F4 L rS b * pinnedX Tag.F4 L pS (Fr b)) *
        pinnedX Tag.F4 L (highRoot Tag.F4) (Fr b * b + Fr z) := by rw [pinnedX_add]
    _ = _ := by rw [hcc]

end SigFixed

section PsetSec

open T7

variable {L : Type} [Field L] [CharP L 2] {Fr : L →+* L} {H : Subgroup (ModGL Tag.F4 L)}

theorem mem_of_isW (hth : ∀ c : L, Fr c = c → pinnedX Tag.F4 L (highRoot Tag.F4) c ∈ H)
    {v : V L} (hv : IsW Fr H v) {q' : ModGL Tag.F4 L} (hq' : q' ∈ Qθ Tag.F4 L)
    (hs : sigHom Fr q' = q') (hc : heisCoord Tag.F4 L q' = v) : q' ∈ H := by
  obtain ⟨q, hqH, hq, hqs, hqv⟩ := hv
  have hd : q' * q⁻¹ ∈ Qθ Tag.F4 L := mul_mem hq' (inv_mem hq)
  have hd0 : heisCoord Tag.F4 L (q' * q⁻¹) = 0 := by
    rw [(heisCoord_spec Tag.F4 L).mul _ hq' _ (inv_mem hq), heisCoord_inv hq, hc, hqv,
      add_neg_cancel]
  have hdU : q' * q⁻¹ ∈ Uθ Tag.F4 L := ((heisCoord_spec Tag.F4 L).eq_zero_iff _ hd).1 hd0
  obtain ⟨c, hcd⟩ := mem_rootSubgroup.1 hdU
  have hfix : sigHom Fr (q' * q⁻¹) = q' * q⁻¹ := by rw [map_mul, map_inv, hs, hqs]
  rw [← hcd, sigHom_pinnedX Fr isRoot_theta, w_smul_theta] at hfix
  have hc0 : Fr c = c := pinnedX_injective Tag.F4 L _ hfix
  have : q' * q⁻¹ ∈ H := by rw [← hcd]; exact hth c hc0
  have h2 := mul_mem this hqH
  simpa using h2

theorem pS_deg : pS 0 = 1 := by decide
theorem rS_mem_Deg1 : rS ∈ Deg1 Tag.F4 := ⟨isRoot_rS, rS_deg⟩
theorem pS_mem_Deg1 : pS ∈ Deg1 Tag.F4 := ⟨isRoot_pS, pS_deg⟩

theorem heisCoord_r (b z : L) :
    pinnedX Tag.F4 L rS b * pinnedX Tag.F4 L pS (Fr b) * pinnedX Tag.F4 L (highRoot Tag.F4) z ∈
        Qθ Tag.F4 L ∧
      heisCoord Tag.F4 L (pinnedX Tag.F4 L rS b * pinnedX Tag.F4 L pS (Fr b) *
        pinnedX Tag.F4 L (highRoot Tag.F4) z) = fv Fr rS b := by
  have h1 := pinnedX_mem_Qθ_of_mem_Deg1 (K := L) rS_mem_Deg1 b
  have h2 := pinnedX_mem_Qθ_of_mem_Deg1 (K := L) pS_mem_Deg1 (Fr b)
  have h3 : pinnedX Tag.F4 L (highRoot Tag.F4) z ∈ Qθ Tag.F4 L :=
    pinnedX_mem_rootSpan ((CoordAux.mem_radRoots_iff _).2 (Or.inr rfl)) z
  refine ⟨mul_mem (mul_mem h1 h2) h3, ?_⟩
  rw [(heisCoord_spec Tag.F4 L).mul _ (mul_mem h1 h2) _ h3,
    (heisCoord_spec Tag.F4 L).mul _ h1 _ h2, (heisCoord_spec Tag.F4 L).pinnedX_deg1 _ rS_mem_Deg1,
    (heisCoord_spec Tag.F4 L).pinnedX_deg1 _ pS_mem_Deg1,
    (heisCoord_spec Tag.F4 L).pinnedX_highRoot, add_zero, fv, w_rS]

theorem crd_fv_rS (l : L) : crd (fv Fr rS l) = ⟨l, 0, 0, 0, 0, 0, 0⟩ := by
  have hw := w_rS
  ext
  · exact fv_apply_self _ _ (by rw [hw]; decide)
  · exact fv_apply_ne _ (by decide) (by rw [hw]; decide)
  · exact fv_apply_ne _ (by decide) (by rw [hw]; decide)
  · exact fv_apply_ne _ (by decide) (by rw [hw]; decide)
  · exact fv_apply_ne _ (by decide) (by rw [hw]; decide)
  · exact fv_apply_ne _ (by decide) (by rw [hw]; decide)
  · exact fv_apply_ne _ (by decide) (by rw [hw]; decide)

theorem crd_fv_rA3 (l : L) : crd (fv Fr rA3 l) = ⟨0, 0, 0, l, 0, 0, 0⟩ := by
  have hw := w_rA3
  ext
  · exact fv_apply_ne _ (by decide) (by rw [hw]; decide)
  · exact fv_apply_ne _ (by decide) (by rw [hw]; decide)
  · exact fv_apply_ne _ (by decide) (by rw [hw]; decide)
  · exact fv_apply_self _ _ (by rw [hw]; decide)
  · exact fv_apply_ne _ (by decide) (by rw [hw]; decide)
  · exact fv_apply_ne _ (by decide) (by rw [hw]; decide)
  · exact fv_apply_ne _ (by decide) (by rw [hw]; decide)

theorem crd_fv_rB23 (l : L) : crd (fv Fr rB23 l) = ⟨0, 0, 0, 0, 0, 0, l⟩ := by
  have hw := w_rB23
  ext
  · exact fv_apply_ne _ (by decide) (by rw [hw]; decide)
  · exact fv_apply_ne _ (by decide) (by rw [hw]; decide)
  · exact fv_apply_ne _ (by decide) (by rw [hw]; decide)
  · exact fv_apply_ne _ (by decide) (by rw [hw]; decide)
  · exact fv_apply_ne _ (by decide) (by rw [hw]; decide)
  · exact fv_apply_ne _ (by decide) (by rw [hw]; decide)
  · exact fv_apply_self _ _ (by rw [hw]; decide)


structure Elts (Fr : L →+* L) (H : Subgroup (ModGL Tag.F4 L)) : Prop where
  eg5 : ∀ c : L, Fr c = c → pinnedX Tag.F4 L g5 c ∈ H
  eg5n : ∀ c : L, Fr c = c → pinnedX Tag.F4 L g5n c ∈ H
  eu : ∀ s c : L, Fr (Fr s) = s → c + Fr c = s * Fr s →
    pinnedX Tag.F4 L a3 s * pinnedX Tag.F4 L a4 (Fr s) * pinnedX Tag.F4 L g5 c ∈ H
  eth : ∀ c : L, Fr c = c → pinnedX Tag.F4 L (highRoot Tag.F4) c ∈ H
  ethn : ∀ c : L, Fr c = c → pinnedX Tag.F4 L (-highRoot Tag.F4) c ∈ H
  er : ∀ b z : L, Fr (Fr b) = b → z + Fr z = b * Fr b →
    pinnedX Tag.F4 L rS b * pinnedX Tag.F4 L pS (Fr b) * pinnedX Tag.F4 L (highRoot Tag.F4) z ∈ H
  escal : ∀ ζ : L, Fr ζ = ζ → ζ ≠ 0 → ∃ h ∈ H, sigHom Fr h = h ∧ HasAct h (fun v => ζ • v)

@[expose] def Pset (Fr : L →+* L) (H : Subgroup (ModGL Tag.F4 L)) : Set (T7 L) :=
  {x | ∃ u : V L, IsW Fr H u ∧ crd u = x}

theorem pcl_Pset (AD : ActData L) (E : Elts Fr H) : PCl Fr (Pset Fr H) where
  zero := ⟨0, isW_zero, crd_zero⟩
  add := by
    rintro x y ⟨u, hu, rfl⟩ ⟨u', hu', rfl⟩
    exact ⟨u + u', hu.add hu', crd_add u u'⟩
  smul := by
    rintro ζ hζ x ⟨u, hu, rfl⟩
    by_cases hζ0 : ζ = 0
    · refine ⟨0, isW_zero, ?_⟩
      rw [crd_zero]
      ext <;> simp [hζ0]
    · obtain ⟨h, hH, hs, hA⟩ := E.escal ζ hζ hζ0
      exact ⟨ζ • u, hu.act hH hs hA, crd_smul ζ u⟩
  g5 := by
    rintro c hc x ⟨u, hu, rfl⟩
    exact ⟨_, hu.act (E.eg5 c hc) (sig_g5 hc) (AD.hact g5 g5_root g5_deg c),
      crd_act_g5 AD (fun ν hν => hu.supp hν) c⟩
  g5n := by
    rintro c hc x ⟨u, hu, rfl⟩
    exact ⟨_, hu.act (E.eg5n c hc) (sig_g5n hc) (AD.hact g5n g5n_root g5n_deg c),
      crd_act_g5n AD (fun ν hν => hu.supp hν) c⟩
  u := by
    rintro s c hs hc x ⟨u, hu, rfl⟩
    have hA : HasAct (pinnedX Tag.F4 L a3 s * pinnedX Tag.F4 L a4 (Fr s) *
        pinnedX Tag.F4 L g5 c)
        (actFun AD.a1 AD.a2 a3 s ∘ (actFun AD.a1 AD.a2 a4 (Fr s) ∘ actFun AD.a1 AD.a2 g5 c)) := by
      rw [mul_assoc]
      exact (AD.hact a3 a3_root a3_deg s).mul ((AD.hact a4 a4_root a4_deg (Fr s)).mul
        (AD.hact g5 g5_root g5_deg c))
    have hsu : Supp u := fun ν hν => hu.supp hν
    have h5 : Supp (actFun AD.a1 AD.a2 g5 c u) := Supp.act AD hsu g5_root g5_deg c
    have h4 : Supp (actFun AD.a1 AD.a2 a4 (Fr s) (actFun AD.a1 AD.a2 g5 c u)) :=
      Supp.act AD h5 a4_root a4_deg (Fr s)
    refine ⟨_, hu.act (E.eu s c hs hc) (sig_u hs hc) hA, ?_⟩
    show crd (actFun AD.a1 AD.a2 a3 s (actFun AD.a1 AD.a2 a4 (Fr s)
      (actFun AD.a1 AD.a2 g5 c u))) = opU (Fr s) s c (crd u)
    rw [crd_act_a3 AD h4, crd_act_a4 AD h5, crd_act_g5 AD hsu]
    rfl

theorem pset_S (E : Elts Fr H) (hsurj : ∀ n : L, ∃ z, z + Fr z = n) {l : L} (hl : InE Fr l) :
    (⟨l, 0, 0, 0, 0, 0, 0⟩ : T7 L) ∈ Pset Fr H := by
  obtain ⟨z, hz⟩ := hsurj (l * Fr l)
  obtain ⟨hq, hc⟩ := heisCoord_r (Fr := Fr) l z
  refine ⟨fv Fr rS l, ⟨_, E.er l z hl hz, hq, sig_r hl hz, hc⟩, crd_fv_rS l⟩

end PsetSec


end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.F4Even
