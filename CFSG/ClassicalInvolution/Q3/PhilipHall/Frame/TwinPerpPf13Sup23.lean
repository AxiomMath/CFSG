module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf11H02
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23PfTwo
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf6Stmt
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf9A07

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {W : Subgroup G}

theorem trans_of_cent {K K' : Subgroup G} {z : G}
    (hs : CFSG.ClassicalInvolution.Q8P.Asc77.Hyp23Setting Ω K K' z)
    {H : Subgroup G} (hCz : Subgroup.centralizer ({z} : Set G) ≤ H)
    (hCv : ∀ W₁ ∈ WSet Ω, z ∈ W₁ → ∀ v ∈ W₁, v * v = 1 → v ≠ 1 → v ≠ z →
      Subgroup.centralizer ({v} : Set G) ≤ H) :
    ∀ J ∈ dstarComp Ω K, ∃ h ∈ H, conjSub h K = J := by
  intro J hJ
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

  have key : ∀ W₁ : Subgroup G, W₁ ∈ WSet Ω → z ∈ W₁ → ∀ J' : Subgroup G, J' ∈ Ω →
      (∃ T ∈ DSet Ω W₁, IsSylow2In T J') → ∃ h ∈ H, conjSub h K = J' := by
    intro W₁ hW₁ hzW₁ J' hJ' ⟨T, hTD, hTJ'⟩
    have c : Q3CL.Thompson.Ctx Ω W₁ := CFSG.ClassicalInvolution.Q8P.Asc77.T7D.ctx_of_stand hst hW₁
    obtain ⟨S, ρ, ρ', hWS, hρK, hρ'K, hρS, hρ'S, hnbr, hnbr', hab, hcomm⟩ :=
      exists_twin_reps hs hW₁ hzW₁
    obtain ⟨σ, hσK, -⟩ := CFSG.ClassicalInvolution.Q8P.Asc77.T7D.exists_rep hΩ hW₁ hJ' hTJ' hTD
    rcases rep_dichotomy hs hW₁ ρ ρ' hab hcomm with hall | ⟨e, he, σ₃, hac, hbc⟩
    · rcases hall σ with h | h
      · exact ⟨1, H.one_mem, by rw [conjSub_one, ← hσK, h, hρK]⟩
      · exact ⟨g₀, hg₀H, by rw [hg₀, ← hσK, h, hρ'K]⟩
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
      have hbKK : x₁ ^ m ∈ K := hρK ▸ hbK.1
      have hb'KK : x₂ ^ m ∈ K' := hρ'K ▸ hb'K.1
      have hbb : x₁ ^ m * x₁ ^ m = z := hFz ▸ TwinPerp.sq_eq_of_orderOf_four F.hz hbK.1 ob
      have hb'b' : x₂ ^ m * x₂ ^ m = z := hFz ▸ TwinPerp.sq_eq_of_orderOf_four F.hz' hb'K.1 ob'
      have hcomm₁₂ : x₁ ^ m * x₂ ^ m = x₂ ^ m * x₁ ^ m := c.comm_W _ hbK.2 _ hb'K.2
      have hnotK : x₂ ^ m ∉ K := fun hx =>
        CFSG.ClassicalInvolution.Q8P.Asc77.not_mem_inf_of_orderOf_four hΩ hK hK' hKK' ob' hx hb'KK
      obtain ⟨y, hyK, hyW, hyy, hyc, rfl⟩ : ∃ y, y ∈ K ∧ y ∈ W₁ ∧ y * y = z ∧
          y * x₂ ^ m = x₂ ^ m * y ∧ u₁ = y * x₂ ^ m := by
        rcases hu₁ with h | h
        · exact ⟨x₁ ^ m, hbKK, hbK.2, hbb, hcomm₁₂, h⟩
        · refine ⟨(x₁ ^ m)⁻¹, K.inv_mem hbKK, W₁.inv_mem hbK.2, ?_, ?_, h⟩
          · rw [← mul_inv_rev, hbb]; exact inv_eq_of_mul_eq_one_right hz.sq
          · exact (Commute.inv_left hcomm₁₂).eq
      have hu2 : y * x₂ ^ m * (y * x₂ ^ m) = 1 := by
        calc y * x₂ ^ m * (y * x₂ ^ m) = y * (x₂ ^ m * y) * x₂ ^ m := by group
          _ = y * (y * x₂ ^ m) * x₂ ^ m := by rw [hyc]
          _ = (y * y) * (x₂ ^ m * x₂ ^ m) := by group
          _ = 1 := by rw [hyy, hb'b', hz.sq]
      have hnot : ∀ v ∈ K, y * x₂ ^ m ≠ v := by
        intro v hv h
        have e : x₂ ^ m = y⁻¹ * v := by rw [← h]; group
        exact hnotK (by rw [e]; exact K.mul_mem (K.inv_mem hyK) hv)
      have hu₁W : y * x₂ ^ m ∈ W₁ := W₁.mul_mem hyW hb'K.2
      have hu₁H : Subgroup.centralizer ({y * x₂ ^ m} : Set G) ≤ H :=
        hCv W₁ hW₁ hzW₁ _ hu₁W hu2 (hnot 1 K.one_mem) (hnot z hz.mem)
      have hsH : F.ρ₃.r ∈ H := hu₁H (Subgroup.mem_centralizer_singleton_iff.mpr
        (mul_inv_eq_iff_eq_mul.mp hsu))
      have hWH : W₁ ⊔ OCW W₁ ≤ H := by
        refine sup_le (fun w hw => hu₁H ?_) (fun w hw => hu₁H ?_)
        · exact Subgroup.mem_centralizer_singleton_iff.mpr (c.comm_W w hw (y * x₂ ^ m) hu₁W)
        · have := Subgroup.mem_centralizer_iff.mp (Thompson.OCW_le_centralizer W₁ hw) (y * x₂ ^ m) hu₁W
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
      exact ⟨m', hMH hm'M, by rw [← hσK, ← hKm, hρK]⟩

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

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

namespace CFSG.ClassicalInvolution.Q8P.P24

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q8P.Asc77
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

section Sup23

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}

theorem centralizer_le_of_mem_W1 (C : Asc77.S24B.Ctx8F Ω K K' W S R R' z u)
    {H : Subgroup G} (hCz : Subgroup.centralizer ({z} : Set G) ≤ H)
    (hCu : Subgroup.centralizer ({u} : Set G) ≤ H) {W₁ : Subgroup G} (hW₁ : W₁ ∈ WSet Ω)
    (hzW₁ : z ∈ W₁) {v : G} (hv : v ∈ W₁) (hv2 : v * v = 1) (hv1 : v ≠ 1) (hvz : v ≠ z) :
    Subgroup.centralizer ({v} : Set G) ≤ H := by
  obtain ⟨c, hc, hcW⟩ := Asc77.S24.exists_centralizer_conj_W C hW₁ hzW₁
  have hcH : c ∈ H := hCz hc
  have hcz : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp hc
  rw [← hcW, mem_conjSub_iff] at hv
  have hw2 : (c⁻¹ * v * c) * (c⁻¹ * v * c) = 1 := by
    calc (c⁻¹ * v * c) * (c⁻¹ * v * c) = c⁻¹ * (v * v) * c := by group
      _ = 1 := by rw [hv2]; group
  have hw1 : c⁻¹ * v * c ≠ 1 := by
    intro h
    apply hv1
    calc v = c * (c⁻¹ * v * c) * c⁻¹ := by group
      _ = 1 := by rw [h]; group
  have hwz : c⁻¹ * v * c ≠ z := by
    intro h
    apply hvz
    have hz' : c⁻¹ * z * c = z := by
      calc c⁻¹ * z * c = c⁻¹ * (z * c) := by group
        _ = c⁻¹ * (c * z) := by rw [hcz]
        _ = z := by group
    calc v = c * (c⁻¹ * v * c) * c⁻¹ := by group
      _ = c * z * c⁻¹ := by rw [h]
      _ = z := by rw [hcz]; group
  have hr : C.D.F.ρ.r ∈ H := hCz C.r_mem_centralizer_z
  have hCj : Subgroup.centralizer ({C.D.F.j} : Set G) ≤ H ∧
      Subgroup.centralizer ({C.D.F.j * z} : Set G) ≤ H := by
    rcases C.u_cases with h | h
    · refine ⟨h ▸ hCu, ?_⟩
      have hCj : Subgroup.centralizer ({C.D.F.j} : Set G) ≤ H := h ▸ hCu
      exact T7A.centralizer_conj_le (Subgroup.inv_mem _ hr)
        (by rw [inv_inv]; exact (by
          have := C.r_conj_jz
          calc C.D.F.j * z = C.D.F.ρ.r⁻¹ * (C.D.F.ρ.r * (C.D.F.j * z) * C.D.F.ρ.r⁻¹) *
              C.D.F.ρ.r := by group
            _ = C.D.F.ρ.r⁻¹ * C.D.F.j * C.D.F.ρ.r := by rw [this])) hCj
    · refine ⟨?_, h ▸ hCu⟩
      have hCjz : Subgroup.centralizer ({C.D.F.j * z} : Set G) ≤ H := h ▸ hCu
      exact T7A.centralizer_conj_le hr C.r_conj_jz.symm hCjz
  have hCw : Subgroup.centralizer ({c⁻¹ * v * c} : Set G) ≤ H := by
    rcases T7B.mem_closure_pair C.hjJ.sq C.hzK.sq C.hjJ.ne_one C.hzK.ne_one C.comm_jz
      (C.mem_closure_of_mem_W hv hw2) with h | h | h | h
    · exact absurd h hw1
    · rw [h]; exact hCj.1
    · exact absurd h hwz
    · rw [h]; exact hCj.2
  exact T7A.centralizer_conj_le hcH (by group) hCw

theorem exists_sylow_q8 (hst : AscStand Ω K) {L : Subgroup G} (hL : L ∈ Ω) :
    ∃ P : Subgroup G, IsSylow2In P L ∧ Nonempty (↥P ≃* QuaternionGroup 2) := by
  obtain ⟨P, hP, hPL, -⟩ := exists_mem_RSet_ge hL (IsPGroup.of_bot : IsPGroup 2 (⊥ : Subgroup G))
    bot_le
  obtain ⟨k, hk, ⟨e⟩⟩ := Sec6Gen.isQuatSub_of_mem_RSet hst.hyp hP
  have hc := hst.card8 L hL P hPL
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card] at hc
  have hk1 : k = 1 := by
    have h2 : 2 ^ k = 2 ^ 1 := by omega
    exact Nat.pow_right_injective le_rfl h2
  subst hk1
  exact ⟨P, hPL, ⟨e⟩⟩

theorem estandQ8_of_hyp24 [CoreLike G]
    (hyp : Hyp24 Ω K K' W S R R' z u) (C : Asc77.S24B.Ctx8F Ω K K' W S R R' z u) :
    EStandQ8 Ω K S R W := by
  have hst := hyp.std.setting.stand
  exact
    { hyp := hst.hyp
      cls := hst.cls
      q8 := fun L hL => exists_sylow_q8 hst hL
      two := hyp.std.1.quot2
      ih := hyp.std.1.ih
      mem := hst.mem
      aEmpty := hst.aEmpty K hst.mem
      twin := ⟨K', hyp.std.setting.hK', hyp.std.setting.hne, R', hyp.hR'.1, hyp.hR'.2.1,
        hyp.hR'.2.2⟩
      hR := hyp.hR
      hW := ⟨hyp.hW, hyp.hWS, fun s hs => mem_normalizer_iff_conjSub_eq.mp (C.le_normalizer_W hs)⟩ }

end Sup23

end CFSG.ClassicalInvolution.Q8P.P24
