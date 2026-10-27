module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23PfTwo

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL


section Cx

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem key_of_cx {K K' : Subgroup G} {z : G}
    (hs : CFSG.ClassicalInvolution.Q8P.Asc77.Hyp23Setting Ω K K' z) {H : Subgroup G}
    (hCz : Subgroup.centralizer ({z} : Set G) ≤ H) {W₁ : Subgroup G} (hW₁ : W₁ ∈ WSet Ω)
    (hzW₁ : z ∈ W₁)
    (hCx : ∀ R₁ R₂ : Subgroup G, IsSylow2In R₁ K → IsSylow2In R₂ K' → Commutes R₁ R₂ →
      ∀ x ∈ R₁, ∀ y ∈ R₂, x ∈ W₁ → y ∈ W₁ → orderOf x = 4 → orderOf y = 4 →
        Subgroup.centralizer ({x * y} : Set G) ≤ H)
    (J' : Subgroup G) (hJ' : J' ∈ Ω) (hT : ∃ T ∈ DSet Ω W₁, IsSylow2In T J') :
    ∃ h ∈ H, conjSub h K = J' ∧ (h = 1 ∨ J' = K' ∨ h ∈ Subgroup.normalizer (W₁ : Set G)) := by
  have hst : CFSG.ClassicalInvolution.Q8P.Asc77.AscStand Ω K := hs.stand
  have : Fact (Q3CL.ClassicalClause Ω) := ⟨hst.cls⟩
  have hΩ : HypOmegaGen Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have hK' : K' ∈ Ω := hs.hK'.1
  have hKK' : K' ≠ K := hs.hne
  have hz : IsUniqueInvolution K z := hs.hz
  have hz' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hs.hK'
  have hKH : ∀ k ∈ K, k ∈ H := fun k hk =>
    hCz (Subgroup.mem_centralizer_singleton_iff.mpr (hz.commute_of_mem hk).symm)
  have hK'H : ∀ k ∈ K', k ∈ H := fun k hk =>
    hCz (Subgroup.mem_centralizer_singleton_iff.mpr (hz'.commute_of_mem hk).symm)
  obtain ⟨g₀, hg₀⟩ := hst.trans K' hK'
  have hg₀z : g₀ * z * g₀⁻¹ = z := by
    have := hz.conj g₀
    rw [hg₀] at this
    exact (hz'.eq this).symm
  have hg₀H : g₀ ∈ H :=
    hCz (Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hg₀z))
  obtain ⟨T, hTD, hTJ'⟩ := hT
  have c : Q3CL.Thompson.Ctx Ω W₁ := CFSG.ClassicalInvolution.Q8P.Asc77.T7D.ctx_of_stand hst hW₁
  obtain ⟨S, ρ, ρ', hWS, hρK, hρ'K, hρS, hρ'S, hnbr, hnbr', hab, hcomm⟩ :=
    exists_twin_reps hs hW₁ hzW₁
  obtain ⟨σ, hσK, -⟩ := CFSG.ClassicalInvolution.Q8P.Asc77.T7D.exists_rep hΩ hW₁ hJ' hTJ' hTD
  rcases rep_dichotomy hs hW₁ ρ ρ' hab hcomm with hall | ⟨e, he, σ₃, hac, hbc⟩
  · rcases hall σ with h | h
    · exact ⟨1, H.one_mem, by rw [conjSub_one, ← hσK, h, hρK], Or.inl rfl⟩
    · exact ⟨g₀, hg₀H, by rw [hg₀, ← hσK, h, hρ'K], 
        Or.inr (Or.inl (hσK.symm.trans (h.trans hρ'K)))⟩
  · obtain ⟨F, hFρ, hFρ', hFρ₃, hFz⟩ :=
      frame4_of_twin_reps hs hW₁ hρK hρ'K hnbr hnbr' hac hbc
    subst hFρ hFρ' hFρ₃
    obtain ⟨x₁, x₂, x₃, m, hm, h₁, h₂, h₃, o₁, o₂, o₃, z₁, z₂, z₃, k₁, k₂, k₃, -⟩ :=
      CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.T7E.Frame4.exists_structure c F he hab hcomm hac
    have mx₁ : x₁ ∈ F.ρ.R ⊓ W₁ := h₁ ▸ Subgroup.mem_zpowers x₁
    have mx₂ : x₂ ∈ F.ρ'.R ⊓ W₁ := h₂ ▸ Subgroup.mem_zpowers x₂
    have hbR : x₁ ^ m ∈ F.ρ.R := F.ρ.R.pow_mem mx₁.1 m
    have hb'R : x₂ ^ m ∈ F.ρ'.R := F.ρ'.R.pow_mem mx₂.1 m
    have ob : orderOf (x₁ ^ m) = 4 := by
      have := orderOf_pow_of_dvd (x := x₁) (n := m) (by omega)
        (by rw [o₁]; exact dvd_mul_left m 4)
      rwa [o₁, Nat.mul_div_cancel _ hm] at this
    have ob' : orderOf (x₂ ^ m) = 4 := by
      have := orderOf_pow_of_dvd (x := x₂) (n := m) (by omega)
        (by rw [o₂]; exact dvd_mul_left m 4)
      rwa [o₂, Nat.mul_div_cancel _ hm] at this
    have hbK : x₁ ^ m ∈ F.ρ.K ⊓ W₁ := ⟨F.ρ.hRK.1 hbR, W₁.pow_mem mx₁.2 m⟩
    have hb'K : x₂ ^ m ∈ F.ρ'.K ⊓ W₁ := ⟨F.ρ'.hRK.1 hb'R, W₁.pow_mem mx₂.2 m⟩
    obtain ⟨u₁, hu₁, hsu, -⟩ := CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.T7D.frame_fixed c F.ρ F.ρ' F.ρ₃ F.hnbr F.hnbr' F.hne₁ F.hne₂
      F.hn₁ F.hn₂ F.hn₁' F.hn₂' F.hz F.hz' F.hj hbK hb'K ob ob'
    have hRsyl : IsSylow2In F.ρ.R K := by rw [← hρK]; exact F.ρ.hRK
    have hR'syl : IsSylow2In F.ρ'.R K' := by rw [← hρ'K]; exact F.ρ'.hRK
    have hc2 : Commutes F.ρ.R F.ρ'.R :=
      CFSG.ClassicalInvolution.Q8P.Asc77.HypOmegaMod.commutes_of_twin_of_isPGroup hΩ hK hK' hKK'.symm hz hz' (hρK ▸ F.ρ.hRK.1)
        (hρ'K ▸ F.ρ'.hRK.1) (S.isPGroup'.to_le (sup_le hρS hρ'S))
    have hCx' : ∀ x ∈ F.ρ.R, ∀ y ∈ F.ρ'.R, x ∈ W₁ → y ∈ W₁ → orderOf x = 4 → orderOf y = 4 →
        Subgroup.centralizer ({x * y} : Set G) ≤ H :=
      hCx F.ρ.R F.ρ'.R hRsyl hR'syl hc2
    have hu₁H : Subgroup.centralizer ({u₁} : Set G) ≤ H := by
      rcases hu₁ with rfl | rfl
      · exact hCx' _ hbR _ hb'R (W₁.pow_mem mx₁.2 m) (W₁.pow_mem mx₂.2 m) ob ob'
      · exact hCx' _ (F.ρ.R.inv_mem hbR) _ hb'R (W₁.inv_mem (W₁.pow_mem mx₁.2 m))
            (W₁.pow_mem mx₂.2 m) (by rw [orderOf_inv]; exact ob) ob'
    have hu₁W : u₁ ∈ W₁ := by
      rcases hu₁ with rfl | rfl
      · exact W₁.mul_mem (W₁.pow_mem mx₁.2 m) (W₁.pow_mem mx₂.2 m)
      · exact W₁.mul_mem (W₁.inv_mem (W₁.pow_mem mx₁.2 m)) (W₁.pow_mem mx₂.2 m)
    have hsH : F.ρ₃.r ∈ H := hu₁H (Subgroup.mem_centralizer_singleton_iff.mpr
      (mul_inv_eq_iff_eq_mul.mp hsu))
    have hWH : W₁ ⊔ OCW W₁ ≤ H := by
      refine sup_le (fun w hw => hu₁H ?_) (fun w hw => hu₁H ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (c.comm_W w hw u₁ hu₁W)
      · have := Subgroup.mem_centralizer_iff.mp (Thompson.OCW_le_centralizer W₁ hw) u₁ hu₁W
        exact Subgroup.mem_centralizer_singleton_iff.mpr this.symm
    have hrH : F.ρ.r ∈ H := hKH _ (by rw [← hρK]; exact F.ρ.hRK.1 F.ρ.hr)
    have hr'H : F.ρ'.r ∈ H := hK'H _ (by rw [← hρ'K]; exact F.ρ'.hRK.1 F.ρ'.hr)
    have hDH := CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.T7E.rep_R_le c F he hab hcomm hac hrH hr'H hsH hWH
    have hMH : MGrp Ω W₁ ≤ H := iSup₂_le fun R hR => by
      obtain ⟨KR, hKR, hRK⟩ := exists_isSylow2In_of_mem_RSet hR.1
      obtain ⟨σ', -, hσ'R⟩ := CFSG.ClassicalInvolution.Q8P.Asc77.T7D.exists_rep hΩ hW₁ hKR hRK hR
      rw [← hσ'R]
      exact hDH σ'
    obtain ⟨y, hy⟩ := S4.exists_conj_of_mem he (T7D.imgQ_mem F.ρ) (T7D.imgQ_mem σ)
    obtain ⟨m', hm'M, hym'⟩ := T7E.exists_mem_MGrp_of_mem_muGroup y
    have hm'N : m' ∈ Subgroup.normalizer (W₁ : Set G) := Thompson.MGrp_le_normalizer Ω W₁ hm'M
    have himg : Thompson.piG W₁ m' * F.ρ.img * (Thompson.piG W₁ m')⁻¹ = σ.img := by
      rw [← hym']
      exact congrArg Subtype.val hy
    have hKm : conjSub m' F.ρ.K = σ.K :=
      c.K_eq_of_img_eq (conjRep c.hΩ hm'N F.ρ) σ (by rw [conjRep_img, himg])
    exact ⟨m', hMH hm'M, by rw [← hσK, ← hKm, hρK], Or.inr (Or.inr hm'N)⟩

theorem trans_of_cx {K K' : Subgroup G} {z : G}
    (hs : CFSG.ClassicalInvolution.Q8P.Asc77.Hyp23Setting Ω K K' z) {H : Subgroup G}
    (hCz : Subgroup.centralizer ({z} : Set G) ≤ H)
    (hCx : ∀ W₁ ∈ WSet Ω, z ∈ W₁ → ∀ R₁ R₂ : Subgroup G, IsSylow2In R₁ K → IsSylow2In R₂ K' →
      Commutes R₁ R₂ → ∀ x ∈ R₁, ∀ y ∈ R₂, x ∈ W₁ → y ∈ W₁ → orderOf x = 4 → orderOf y = 4 →
        Subgroup.centralizer ({x * y} : Set G) ≤ H) :
    ∀ J ∈ dstarComp Ω K, ∃ h ∈ H, conjSub h K = J := by
  intro J hJ
  have hst : CFSG.ClassicalInvolution.Q8P.Asc77.AscStand Ω K := hs.stand
  have : Fact (Q3CL.ClassicalClause Ω) := ⟨hst.cls⟩
  have hΩ : HypOmegaGen Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have hz : IsUniqueInvolution K z := hs.hz
  have key : ∀ W₁ : Subgroup G, W₁ ∈ WSet Ω → z ∈ W₁ → ∀ J' : Subgroup G, J' ∈ Ω →
      (∃ T ∈ DSet Ω W₁, IsSylow2In T J') → ∃ h ∈ H, conjSub h K = J' :=
    fun W₁ hW₁ hzW₁ J' hJ' hT => by
      obtain ⟨h, hh, hKh, -⟩ := key_of_cx hs hCz hW₁ hzW₁ (hCx W₁ hW₁ hzW₁) J' hJ' hT
      exact ⟨h, hh, hKh⟩
  have step : ∀ J' : Subgroup G, dstarAdj Ω K J' → ∃ h ∈ H, conjSub h K = J' := by
    rintro J' ⟨hJ'Ω, hadj⟩
    rcases hadj with h | h
    · obtain ⟨W₁, hW₁, R₁, hR₁, T, hT, hR₁K, hTJ'⟩ :=
        CFSG.ClassicalInvolution.Q8P.Asc77.Thompson.exists_W_of_mem_omegaStarNbr hΩ hK h
      have hzW₁ : z ∈ W₁ := (Q3CL.Thompson.uniqueInvolution_mem_W hΩ hW₁ hK hR₁ hR₁K hz).2
      exact key W₁ hW₁ hzW₁ J' hJ'Ω ⟨T, hT, hTJ'⟩
    · obtain ⟨W₁, hW₁, R₁, hR₁, T, hT, hR₁J', hTK⟩ :=
        CFSG.ClassicalInvolution.Q8P.Asc77.Thompson.exists_W_of_mem_omegaStarNbr hΩ hJ'Ω h
      have hzW₁ : z ∈ W₁ := (Q3CL.Thompson.uniqueInvolution_mem_W hΩ hW₁ hK hT hTK hz).2
      exact key W₁ hW₁ hzW₁ J' hJ'Ω ⟨R₁, hR₁, hR₁J'⟩
  have hJ' : Relation.ReflTransGen (dstarAdj Ω) K J := hJ
  clear hJ
  induction hJ' with
  | refl => exact ⟨1, H.one_mem, conjSub_one K⟩
  | @tail J₁ J₂ _ hadj ih =>
    obtain ⟨h₁, hh₁, hJ₁⟩ := ih
    have hadj' : dstarAdj Ω K (conjSub h₁⁻¹ J₂) := by
      obtain ⟨hJ₂, h | h⟩ := hadj
      · refine ⟨hΩ.conjInvariant h₁⁻¹ J₂ hJ₂, Or.inl ?_⟩
        have := omegaStarNbr_conj hΩ.conjInvariant h h₁⁻¹
        rwa [← hJ₁, conjSub_inv_conjSub] at this
      · refine ⟨hΩ.conjInvariant h₁⁻¹ J₂ hJ₂, Or.inr ?_⟩
        have := omegaStarNbr_conj hΩ.conjInvariant h h₁⁻¹
        rwa [← hJ₁, conjSub_inv_conjSub] at this
    obtain ⟨h₂, hh₂, hJ₂⟩ := step _ hadj'
    refine ⟨h₁ * h₂, H.mul_mem hh₁ hh₂, ?_⟩
    rw [conjSub_mul, hJ₂, conjSub_conjSub_inv]
end Cx

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
