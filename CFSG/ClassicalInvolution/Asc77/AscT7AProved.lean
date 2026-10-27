module

public import CFSG.ClassicalInvolution.Asc77.AscT7AWyl
public import CFSG.ClassicalInvolution.Asc77.AscP1SevenGraphAllWire

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson

variable (p f : ℕ) [Fact p.Prime]

theorem c21_12_exclude_proved : C21_12_exclude p f := by
  intro G _ _ _ Ω K K' z u J t W h _
  have hp : p ≠ 2 := h.std.stand.odd
  have hq : 5 ≤ p ^ f := h.std.stand.five
  have hΩ : HypOmegaMod p f Ω := h.std.stand.hyp
  have hK : K ∈ Ω := h.std.stand.mem
  have hK'Ω : K' ∈ Ω := h.std.hK'.1
  have hJΩ : J ∈ Ω := h.hJ.1
  have hP : PartIHyp p f Ω := ⟨hp, hq, hΩ, h.std.stand.aEmpty⟩
  obtain ⟨S, R, R', T, hRsyl, hR'syl, hTsyl, hRS, hR'S, hTS, hRR', hRT, hR'T⟩ :=
    exists_twinSylow hp hq hΩ hK h.std.hz h.std.hK' h.std.hne h.hJ
  obtain ⟨g, hg⟩ := Thompson.exists_conj_mem_DSet hp hq hΩ h.hW S
  have hRD : conjSub g R ∈ DSet Ω W := hg R (mem_RSet_of_isSylow2In hK hRsyl) hRS
  have hR'D : conjSub g R' ∈ DSet Ω W := hg R' (mem_RSet_of_isSylow2In hK'Ω hR'syl) hR'S
  have hTD : conjSub g T ∈ DSet Ω W := hg T (mem_RSet_of_isSylow2In hJΩ hTsyl) hTS
  have hKg : conjSub g K ∈ Ω := hΩ.conjInvariant g K hK
  have hK'g : conjSub g K' ∈ Ω := hΩ.conjInvariant g K' hK'Ω
  have hJg : conjSub g J ∈ Ω := hΩ.conjInvariant g J hJΩ
  have hRsylg : IsSylow2In (conjSub g R) (conjSub g K) := hRsyl.conj g
  have hR'sylg : IsSylow2In (conjSub g R') (conjSub g K') := hR'syl.conj g
  have hTsylg : IsSylow2In (conjSub g T) (conjSub g J) := hTsyl.conj g
  have hTT := Thompson.isTT_muDelta hp hq hΩ h.hW (thompsonCube G Ω hP W h.hW)
  obtain ⟨r, hr, hrW⟩ := exists_not_mem_of_mem_D hp hq hΩ h.hW hRD
  obtain ⟨r', hr', hr'W⟩ := exists_not_mem_of_mem_D hp hq hΩ h.hW hR'D
  obtain ⟨t', ht', ht'W⟩ := exists_not_mem_of_mem_D hp hq hΩ h.hW hTD
  obtain ⟨a, ha, haeq⟩ := exists_muDelta_eq_piG hRD hr hrW
  obtain ⟨b, hb, hbeq⟩ := exists_muDelta_eq_piG hR'D hr' hr'W
  obtain ⟨c, hc, hceq⟩ := exists_muDelta_eq_piG hTD ht' ht'W
  have hKK' : conjSub g K ≠ conjSub g K' := fun e => h.std.hne.symm ((conjSub_inj g).mp e)
  have hKJ : conjSub g K ≠ conjSub g J := fun e => by
    have := h.hJ.2 K (mem_twinSet_self hK h.std.hz)
    exact this.2.1 ((conjSub_inj g).mp e).symm
  have hK'J : conjSub g K' ≠ conjSub g J := fun e => by
    have := h.hJ.2 K' h.std.hK'
    exact this.2.1 ((conjSub_inj g).mp e).symm
  have hab : a ≠ b := fun e =>
    piG_ne_of_ne_members hp hq hΩ h.hW hRD hR'D hKg hK'g hRsylg hR'sylg hKK' hr hr' hr'W
      (haeq.symm.trans ((congrArg Subtype.val e).trans hbeq))
  have hac : a ≠ c := fun e =>
    piG_ne_of_ne_members hp hq hΩ h.hW hRD hTD hKg hJg hRsylg hTsylg hKJ hr ht' ht'W
      (haeq.symm.trans ((congrArg Subtype.val e).trans hceq))
  have hbc : b ≠ c := fun e =>
    piG_ne_of_ne_members hp hq hΩ h.hW hR'D hTD hK'g hJg hR'sylg hTsylg hK'J hr' ht' ht'W
      (hbeq.symm.trans ((congrArg Subtype.val e).trans hceq))
  have hab' : a * b = b * a :=
    muGroup_comm_of_comm hRD hR'D hr hr' ((hRR'.conjSub g) r hr r' hr') haeq hbeq
  have hac' : a * c = c * a :=
    muGroup_comm_of_comm hRD hTD hr ht' ((hRT.conjSub g) r hr t' ht') haeq hceq
  have hbc' : b * c = c * b :=
    muGroup_comm_of_comm hR'D hTD hr' ht' ((hR'T.conjSub g) r' hr' t' ht') hbeq hceq
  constructor
  · rintro ⟨e⟩
    have hTT3 := T7A.isTT_map_equiv hTT e
    exact T7A.no_two_commuting_perm3 hTT3 _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      (fun e2 => hab (e.injective e2)) (by rw [← map_mul, ← map_mul, hab'])
  · rintro ⟨e⟩
    have hTT4 := T7A.isTT_map_equiv hTT e
    exact T7A.no_three_commuting_perm4 hTT4 _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩
      (fun e2 => hab (e.injective e2)) (fun e2 => hac (e.injective e2))
      (fun e2 => hbc (e.injective e2))
      (by rw [← map_mul, ← map_mul, hab']) (by rw [← map_mul, ← map_mul, hac'])
      (by rw [← map_mul, ← map_mul, hbc'])

theorem c21_12_proved : C21_12 p f := c21_12_of p f l7_17_proved (c21_12_exclude_proved p f)

theorem c21_2_final_proved (hE : ThmEWithSylow p f) (hHz : TwinFrameHyp51z p f)
    (hHt : TwinFrameHyp51t p f) (hHu : TwinFrameHyp51u p f) (hMF : DStarConnectedTwin p f)
    (h3s : ∀ n, CITBelowU p f n → T3.Thm3SectBelow p f n) (h13N : C21_13_N p f)
    (h14N : C21_14_N p f) (h14a : C21_14_alt p f) (h15 : C21_15 p f)
    (hWyl : C21_WylTrans' p f) (hY : C21_YSigma p f) : C21_2 p f :=
  c21_2_final_sect' p f hE hHz hHt hHu (c21_12_proved p f) hMF h3s h13N h14N h14a h15 hWyl hY

end CFSG.ClassicalInvolution.Asc77
