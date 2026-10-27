module

public import CFSG.Certificates.Kernel.LocalQTR9CodeSound
public import CFSG.Certificates.Kernel.LocalQTSmallSound

public section

namespace CFSG.KC.LQT.R

open CFSG.QuasithinUnique.Unc25K1

theorem s4041k (L : List R9) (hL : ∀ r, r ∈ L ↔ rdet r = 1) (x1 u0 d2 : R9) (Tl : List R9)
    {X1 U0 D2 : ℕ} {TL w2 : List ℕ}
    {cent : List (List ℕ)} (hx : codeR x1 = X1) (hu : codeR u0 = U0) (hd : codeR d2 = D2)
    (ht : Tl.map codeR = TL) (hk : c4041 X1 U0 D2 TL w2 cent = true)
    (hs : ∀ c < 20, allSLc c (sl4041 X1 U0 D2 TL w2 cent) = true) :
    let I := L.filter fun r => r != rone && rmul r r == rone
    (∀ r ∈ L, rmul r x1 ≠ rmul (rcof x1) r)
    ∧ (∀ r ∈ L, rmul r (rcof r) = rone →
          ∃ h ∈ L, rmul r (rcof h) = h)
    ∧ (∀ r ∈ L, (∀ t ∈ Tl, rmul r (rcof t) = rmul t r) → rmul r (rcof r) = u0)
    ∧ (∀ a ∈ I, ∀ b ∈ I, ∀ c ∈ I, rmul a b = rmul b a → rmul a c = rmul c a →
          rmul b c = rmul c b → a ≠ b → c ≠ a → c ≠ b → c ≠ rmul a b → False)
    ∧ (∀ a ∈ I, ∀ b ∈ I, a ≠ b → rmul a b = rmul b a →
          ∃ g ∈ L, rmul g u0 = rmul a g ∧ rmul g d2 = rmul b g)
    ∧ (∀ r ∈ L, rmul r u0 = rmul u0 r → rmul r d2 = rmul d2 r →
          r = rone ∨ r = u0 ∨ r = d2 ∨ r = rmul u0 d2)
    ∧ (rmul d2 d2 = rone ∧ rmul u0 d2 = rmul d2 u0 ∧ d2 ≠ rone ∧ u0 ≠ d2 ∧
          rcof u0 = u0 ∧ rcof d2 = d2) := by
  subst hx hu hd ht
  have hr : ∀ r ∈ L, sl4041 (codeR x1) (codeR u0) (codeR d2) (Tl.map codeR) w2 cent (codeR r) =
      true := fun r h => allSLc_sound hs r ((hL r).1 h)
  simp only [sl4041, S.allBs_cons, S.allBs_nil, P.andB_iff, and_true] at hr
  simp only [P.notB_iff, P.impB_iff, P.anyL_iff, P.beq_iff, S.memL_iff, mulK_codeR, cofK_codeR,
    oneK_eq, codeR_eq_iff, invoK_codeR, commK_codeR, anyLL_iff, List.mem_cons,
    List.not_mem_nil, or_false, allL_mapR] at hr
  simp only [c4041, S.allBs_cons, S.allBs_nil, P.andB_iff, and_true] at hk
  simp only [P.notB_iff, P.impB_iff, P.anyL_iff, P.allL_iff, P.beq_iff, allLL_iff, mulK_codeR,
    cofK_codeR, oneK_eq, codeR_eq_iff, commK_codeR, P.andB_iff] at hk
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11⟩ := hk
  have hI : ∀ a ∈ L.filter (fun r => r != rone && rmul r r == rone), a ∈ L ∧
      ∃ e ∈ cent, headL e = codeR a := by
    intro a ha
    simp only [List.mem_filter, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at ha
    exact ⟨ha.1, (hr a ha.1).2.2.2.1 ⟨ha.2.1, ha.2.2⟩⟩
  refine ⟨fun r h => (hr r h).1, ?_, fun r h => (hr r h).2.2.1, ?_, ?_,
    fun r h => (hr r h).2.2.2.2, k6, k7, k8, k9, k10, k11⟩
  · intro r h h1
    obtain ⟨w, hw, hwr⟩ := (hr r h).2.1 h1
    obtain ⟨hsl, hm⟩ := k1 w hw
    obtain ⟨y, hy, hdy⟩ := exists_of_slOK hsl
    refine ⟨y, (hL y).2 hdy, ?_⟩
    rw [← hy, hwr, cofK_codeR, mulK_codeR, codeR_eq_iff] at hm
    exact hm
  · intro a ha b hb c hc hab hac hbc hne1 hne2 hne3 hne4
    obtain ⟨-, ea, hea, hha⟩ := hI a ha
    obtain ⟨-, eb, heb, hhb⟩ := hI b hb
    obtain ⟨-, ec, hec, hhc⟩ := hI c hc
    obtain ⟨bw, hbw, hfb⟩ := k2 ea hea eb heb (by rw [hha, hhb, commK_codeR]; exact hab)
    obtain ⟨cw, hcw, hfc⟩ := k2 ea hea ec hec (by rw [hha, hhc, commK_codeR]; exact hac)
    rw [hhb] at hfb
    rw [hhc] at hfc
    have := k4 ea hea bw hbw cw hcw (by rw [hfb, hfc, commK_codeR]; exact hbc)
      (by rw [hha, hfb, codeR_eq_iff]; exact hne1) (by rw [hha, hfc, codeR_eq_iff]; exact hne2)
      (by rw [hfb, hfc, codeR_eq_iff]; exact hne3)
    rw [hha, hfb, hfc, mulK_codeR, codeR_eq_iff] at this
    exact hne4 this
  · intro a ha b hb hab hcomm
    obtain ⟨-, ea, hea, hha⟩ := hI a ha
    obtain ⟨-, eb, heb, hhb⟩ := hI b hb
    obtain ⟨bw, hbw, hfb⟩ := k2 ea hea eb heb (by rw [hha, hhb, commK_codeR]; exact hcomm)
    rw [hhb] at hfb
    obtain ⟨hsl, h1, h2⟩ := k5 ea hea bw hbw (by rw [hha, hfb, codeR_eq_iff]; exact hab)
    obtain ⟨g, hg, hdg⟩ := exists_of_slOK hsl
    rw [← hg, hha, mulK_codeR, mulK_codeR, codeR_eq_iff] at h1
    rw [← hg, hfb, mulK_codeR, mulK_codeR, codeR_eq_iff] at h2
    exact ⟨g, (hL g).2 hdg, h1, h2⟩

end CFSG.KC.LQT.R

end
