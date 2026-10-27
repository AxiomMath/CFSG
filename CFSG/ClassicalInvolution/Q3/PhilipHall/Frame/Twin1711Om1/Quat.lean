module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Om1.Relations

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Weyl
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Data
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Check

set_option linter.unusedSectionVars false


@[expose] def TwinFail (x y s : WP) : Prop :=
  (∃ g ∈ ({x, y} : Set WP), ∀ k < 4, s * g * s⁻¹ ≠ x ^ k ∧ s * g * s⁻¹ ≠ y * x ^ k) ∧
    ∃ a ∈ ({x, y} : Set WP), ∃ b ∈ ({x, y} : Set WP), a * (s * b * s⁻¹) ≠ (s * b * s⁻¹) * a

private theorem qh_twinFail {x y s : WP}
    (h : Om1Facts.TwinFail (x : Equiv.Perm (Fin 240)) y s) : TwinFail x y s := by
  have hmem : ∀ {u : Equiv.Perm (Fin 240)},
      u ∈ ({(x : Equiv.Perm (Fin 240)), (y : Equiv.Perm (Fin 240))} : Set _) →
        ∃ u' ∈ ({x, y} : Set WP), (u' : Equiv.Perm (Fin 240)) = u := by
    rintro u (rfl | rfl)
    · exact ⟨x, Or.inl rfl, rfl⟩
    · exact ⟨y, Or.inr rfl, rfl⟩
  obtain ⟨⟨g, hg, hk⟩, a, ha, b, hb, hab⟩ := h
  obtain ⟨g', hg', rfl⟩ := hmem hg
  obtain ⟨a', ha', rfl⟩ := hmem ha
  obtain ⟨b', hb', rfl⟩ := hmem hb
  refine ⟨⟨g', hg', fun k hk' => ⟨fun e => (hk k hk').1 ?_, fun e => (hk k hk').2 ?_⟩⟩,
    a', ha', b', hb', fun e => hab ?_⟩
  · simpa using congrArg Subtype.val e
  · simpa using congrArg Subtype.val e
  · simpa using congrArg Subtype.val e

private theorem qh_sq {x u : WP} {v : Equiv.Perm (Fin 240)} (hu : (u : Equiv.Perm (Fin 240)) = v)
    (h : x * x = u) : (x : Equiv.Perm (Fin 240)) * x = v := by
  rw [← Subgroup.coe_mul, h, hu]

private theorem qh_conj {x y : WP} (h : y * x * y⁻¹ = x⁻¹) :
    (y : Equiv.Perm (Fin 240)) * x * (y : Equiv.Perm (Fin 240))⁻¹ = (x : Equiv.Perm (Fin 240))⁻¹ := by
  simpa using congrArg Subtype.val h

theorem q8_S0 {x y : WP} (hx : x ∈ closureW wS0) (hy : y ∈ closureW wS0) (hxx : x * x = t0)
    (hyy : y * y = t0) (hyx : y * x * y⁻¹ = x⁻¹) :
    (x ∈ R0 ∧ y ∈ R0) ∨ (x ∈ R0' ∧ y ∈ R0') ∨ ∃ s ∈ closureW wT, TwinFail x y s := by
  have hws := wordOK_of_sub wS0_sub
  rcases Certificates.certificate197001.2.2.2.2.2.2.1 _ ((mem_closureW_iff hws).1 hx) _
      ((mem_closureW_iff hws).1 hy) (qh_sq coe_t0 hxx) (qh_sq coe_t0 hyy) (qh_conj hyx) with
    ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨s, hs, hf⟩
  · exact Or.inl ⟨mem_R0_iff.2 h1, mem_R0_iff.2 h2⟩
  · exact Or.inr (Or.inl ⟨mem_R0'_iff.2 h1, mem_R0'_iff.2 h2⟩)
  · obtain ⟨s', hs', rfl⟩ := exists_of_mem_G (wordOK_of_sub wT_sub) hs
    exact Or.inr (Or.inr ⟨s', hs', qh_twinFail hf⟩)

theorem sq_Sa_ne {x : WP} (hx : x ∈ closureW wSa) : x * x ≠ tb := fun hxx =>
  Certificates.certificate197001.2.2.2.2.2.2.2.1.1 _
    ((mem_closureW_iff (wordOK_of_sub wSa_sub)).1 hx) (qh_sq coe_tb hxx)

theorem q8_Sa {x y : WP} (hx : x ∈ closureW wSa) (hy : y ∈ closureW wSa) (hxx : x * x = ta)
    (hyy : y * y = ta) : y * x * y⁻¹ ≠ x⁻¹ := fun hyx =>
  Certificates.certificate197001.2.2.2.2.2.2.2.1.2 _
    ((mem_closureW_iff (wordOK_of_sub wSa_sub)).1 hx) _
    ((mem_closureW_iff (wordOK_of_sub wSa_sub)).1 hy) (qh_sq coe_ta hxx) (qh_sq coe_ta hyy)
    (qh_conj hyx)

theorem q8_Sc {x y : WP} (hx : x ∈ closureW wSc) (hy : y ∈ closureW wSc) (hxx : x * x = tc)
    (hyy : y * y = tc) (hyx : y * x * y⁻¹ = x⁻¹) : ∃ s ∈ closureW wCc, TwinFail x y s := by
  have hws := wordOK_of_sub wSc_sub
  obtain ⟨s, hs, hf⟩ := Certificates.certificate197001.2.2.2.2.2.2.2.2.1 _
    ((mem_closureW_iff hws).1 hx) _ ((mem_closureW_iff hws).1 hy) (qh_sq coe_tc hxx)
    (qh_sq coe_tc hyy) (qh_conj hyx)
  obtain ⟨s', hs', rfl⟩ := exists_of_mem_G (wordOK_of_sub wCc_sub) hs
  exact ⟨s', hs', qh_twinFail hf⟩

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1
