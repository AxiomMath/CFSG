module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.CpBookkeep

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

variable {G G' : Type} [Group G] [Group G'] {a : G} {α : G → G'}

theorem bookkeep_one (F : Fam a α) (ha : orderOf a = 2) {x y : G} (hxy : ConjIn (Gx a) x y)
    {R : Set G} (hR : IsInvReps a x R)
    (hagree : ∀ r ∈ R, ∀ r' ∈ R,
      F.app r x = F.app r' x ∨ F.app r x = F.app r' (a * x * a⁻¹)) :
    (∀ t ∈ InvIn (Gxy a y), ∀ g ∈ Gxy a y, α g ∈ Gx (F.app t y)) ∧
      ∀ t ∈ InvIn (Gxy a y), ∀ t' ∈ InvIn (Gxy a y),
        (F.app t y = F.app t' y ∨ F.app t y = F.app t' (a * y * a⁻¹)) ∧
          (ConjIn (Gxy a y) t' t → F.app t y = F.app t' y) := by
  have hstar := cp_star F ha hR hagree
  have h1 : ∀ t ∈ InvIn (Gxy a y), ∀ g ∈ Gxy a y, α g ∈ Gx (F.app t y) := by
    intro t ht g hg
    obtain ⟨r, hrR, s, hs, hsx, hty⟩ := cp_transport F hxy hR ht
    rw [hty]
    exact cp_alpha_cent_conj F ha hs (mem_Gxy.1 hg).1
      (hstar r hrR _ (cp_conj_mem_Gxy hs hsx hg))
  refine ⟨h1, fun t ht t' ht' => ⟨?_, fun hc => F.conj_vals_eq ht ht' hc (h1 t' ht')⟩⟩
  obtain ⟨r, hr, s, hs, hsx, hty⟩ := cp_transport F hxy hR ht
  obtain ⟨r', hr', s', hs', hsx', hty'⟩ := cp_transport F hxy hR ht'
  obtain ⟨c1, c2⟩ := cp_cmp F ha hstar hr hr' hs hs' hsx hsx'
  rcases hagree r hr r' hr' with e | e
  · left
    rw [hty, hty']
    exact c1 e
  · right
    rw [hty, cp_app_conj_a F ht', hty']
    exact c2 (e.trans (cp_app_conj_a F (hR.subset hr')))

theorem bookkeep_two (F : Fam a α) (ha : orderOf a = 2) {x y : G} (hxy : ConjIn (Gx a) x y)
    {R : Set G} (hR : IsInvReps a x R) (hagree : ∀ r ∈ R, ∀ r' ∈ R, F.app r x = F.app r' x) :
    ∀ t ∈ InvIn (Gxy a y), ∀ t' ∈ InvIn (Gxy a y), F.app t y = F.app t' y := by
  have hstar := cp_star F ha hR fun r hr r' hr' => Or.inl (hagree r hr r' hr')
  intro t ht t' ht'
  obtain ⟨r, hr, s, hs, hsx, hty⟩ := cp_transport F hxy hR ht
  obtain ⟨r', hr', s', hs', hsx', hty'⟩ := cp_transport F hxy hR ht'
  rw [hty, hty']
  exact (cp_cmp F ha hstar hr hr' hs hs' hsx hsx').1 (hagree r hr r' hr')

end CFSG.EvenSporadicStandard.HNRecog.Section4
