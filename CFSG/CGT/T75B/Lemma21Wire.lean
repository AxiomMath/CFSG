module

public import CFSG.CGT.T75B.Front
public import CFSG.CGT.T75A.Lemma21

public section

namespace CFSG.CGT.T75B

open CFSG.BenderSuzuki (PSU3Model)

theorem lemma21Input_of_mulEquiv {D : Type} [Group D] [Finite D] {f : ℕ} (hf : 2 ≤ f)
    (e : D ≃* PSU3Model f) : Lemma21Input D where
  inner := fun S α hαα hin hαT =>
    CFSG.CGT.T75A.inner_involution_eq_conj_root_of_mulEquiv hf e α hαα hin hαT
  outer := fun S α hαα hout hαT => by
    have hne : α ≠ 1 := fun h1 => hout (h1 ▸ ⟨1, map_one _⟩)
    have hord : orderOf α = 2 := orderOf_eq_prime (by rw [pow_two]; exact hαα) hne
    exact CFSG.CGT.T75A.outer_involution_root_pair_of_mulEquiv hf e α hord hout hαT
  trans := fun S S' S'' h' h'' => by
    obtain ⟨g, -, hg, hconj⟩ := CFSG.CGT.T75A.exists_normalizer_conj_root_of_mulEquiv hf e h' h''
    exact ⟨g, hg, hconj⟩
  klein := fun S S' hne α β hα hβ hc hαS hαS' hβS hβS' =>
    CFSG.CGT.T75A.klein_four_root_pair_of_mulEquiv hf e hne hα hβ hc hαS hαS' hβS hβS'

end CFSG.CGT.T75B
