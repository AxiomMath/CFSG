module

public import CFSG.ClassicalInvolution.Asc77.AscT7EFrame2
public import CFSG.ClassicalInvolution.Asc77.AscT7EC23
public import CFSG.ClassicalInvolution.Asc77.AscT7BFuse23
public import CFSG.ClassicalInvolution.Asc77.AscT7DFrame

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace T7E

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

theorem rep_R_le (c : Thompson.Ctx p f Ω W) (F : Frame4 Ω W)
    {e : ↥(muGroup Ω W) ≃* Equiv.Perm (Fin 4)}
    (he : ∀ x, x ∈ Thompson.muDelta Ω W ↔ (e x).IsSwap)
    (hab : T7D.imgQ F.ρ ≠ T7D.imgQ F.ρ')
    (hcomm : T7D.imgQ F.ρ * T7D.imgQ F.ρ' = T7D.imgQ F.ρ' * T7D.imgQ F.ρ)
    (hac : T7D.imgQ F.ρ * T7D.imgQ F.ρ₃ ≠ T7D.imgQ F.ρ₃ * T7D.imgQ F.ρ) {H : Subgroup G}
    (hr : F.ρ.r ∈ H) (hr' : F.ρ'.r ∈ H) (hs : F.ρ₃.r ∈ H) (hWH : W ⊔ OCW W ≤ H)
    (σ : Thompson.Rep Ω W) : σ.R ≤ H := by
  have hmem : ∀ w : G, w ∈ H → w ∈ Subgroup.normalizer (W : Set G) →
      Thompson.piG W σ.r = Thompson.piG W w → σ.r ∈ H := by
    intro w hwH hwN hpi
    have h1 := (Thompson.piG_eq_iff hwN σ.r_mem_normalizer).mp hpi.symm
    have h2 : w⁻¹ * σ.r ∈ H := hWH h1
    have h3 : σ.r = w * (w⁻¹ * σ.r) := by group
    rw [h3]
    exact H.mul_mem hwH h2
  have hrN := F.ρ.r_mem_normalizer
  have hr'N := F.ρ'.r_mem_normalizer
  have hsN := F.ρ₃.r_mem_normalizer
  have hσ : σ.r ∈ H := by
    rcases swap_word_cases he (T7D.imgQ_mem F.ρ) (T7D.imgQ_mem F.ρ') (T7D.imgQ_mem F.ρ₃) hab
      hcomm hac (T7D.imgQ_mem σ) with h | h | h | h | h | h
    · exact hmem F.ρ.r hr hrN (congrArg Subtype.val h)
    · exact hmem F.ρ'.r hr' hr'N (congrArg Subtype.val h)
    · exact hmem F.ρ₃.r hs hsN (congrArg Subtype.val h)
    · refine hmem (F.ρ.r * F.ρ₃.r * F.ρ.r) (H.mul_mem (H.mul_mem hr hs) hr)
        (Subgroup.mul_mem _ (Subgroup.mul_mem _ hrN hsN) hrN) ?_
      rw [Thompson.piG_mul (Subgroup.mul_mem _ hrN hsN) hrN, Thompson.piG_mul hrN hsN]
      exact congrArg Subtype.val h
    · refine hmem (F.ρ'.r * F.ρ₃.r * F.ρ'.r) (H.mul_mem (H.mul_mem hr' hs) hr')
        (Subgroup.mul_mem _ (Subgroup.mul_mem _ hr'N hsN) hr'N) ?_
      rw [Thompson.piG_mul (Subgroup.mul_mem _ hr'N hsN) hr'N, Thompson.piG_mul hr'N hsN]
      exact congrArg Subtype.val h
    · refine hmem (F.ρ.r * F.ρ'.r * F.ρ₃.r * F.ρ'.r * F.ρ.r)
        (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem hr hr') hs) hr') hr)
        (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
          (Subgroup.mul_mem _ hrN hr'N) hsN) hr'N) hrN) ?_
      rw [Thompson.piG_mul (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hrN hr'N)
        hsN) hr'N) hrN, Thompson.piG_mul (Subgroup.mul_mem _ (Subgroup.mul_mem _ hrN hr'N) hsN)
        hr'N, Thompson.piG_mul (Subgroup.mul_mem _ hrN hr'N) hsN, Thompson.piG_mul hrN hr'N]
      exact congrArg Subtype.val h
  intro x hx
  by_cases hxW : x ∈ W
  · exact hWH (Subgroup.mem_sup_left hxW)
  · have h1 : σ.r⁻¹ * x ∈ W :=
      Thompson.D_inv_mul_mem c.hp c.hq c.hΩ c.hW σ.hR σ.hr hx σ.hrW hxW
    have h2 : x = σ.r * (σ.r⁻¹ * x) := by group
    rw [h2]
    exact H.mul_mem hσ (hWH (Subgroup.mem_sup_left h1))

end T7E

variable (p f : ℕ) [Fact p.Prime]

theorem c23_2_trans_proved : C23_2_trans p f := by
  intro G _ _ _ Ω K K' z hs W hW hzW u huK huW hu1 huz hu2 J hJ
  have hst : AscStand p f Ω K := hs.stand
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have hK' : K' ∈ Ω := hs.hK'.1
  have hKK' : K' ≠ K := hs.hne
  have hz : IsUniqueInvolution K z := hs.hz
  have hz' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hs.hK'
  set H := Subgroup.centralizer ({u} : Set G) ⊔ Subgroup.centralizer ({z} : Set G) with hH
  have hCu : Subgroup.centralizer ({u} : Set G) ≤ H := le_sup_left
  have hCz : Subgroup.centralizer ({z} : Set G) ≤ H := le_sup_right
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
    have c : Thompson.Ctx p f Ω W₁ := T7D.ctx_of_stand hst hW₁
    obtain ⟨S, ρ, ρ', hWS, hρK, hρ'K, hρS, hρ'S, hnbr, hnbr', hab, hcomm⟩ :=
      T7E.exists_twin_reps hs hW₁ hzW₁
    obtain ⟨σ, hσK, -⟩ := T7D.exists_rep hp hq hΩ hW₁ hJ' hTJ' hTD
    rcases T7E.rep_dichotomy hs hW₁ ρ ρ' hab hcomm with hall | ⟨e, he, σ₃, hac, hbc⟩
    · rcases hall σ with h | h
      · exact ⟨1, H.one_mem, by rw [conjSub_one, ← hσK, h, hρK]⟩
      · exact ⟨g₀, hg₀H, by rw [hg₀, ← hσK, h, hρ'K]⟩
    · obtain ⟨F, hFρ, hFρ', hFρ₃, hFz⟩ :=
        T7E.frame4_of_twin_reps hs hW₁ hρK hρ'K hnbr hnbr' hac hbc
      subst hFρ hFρ' hFρ₃
      obtain ⟨x₁, x₂, x₃, m, hm, h₁, h₂, h₃, o₁, o₂, o₃, z₁, z₂, z₃, k₁, k₂, k₃, -⟩ :=
        F.exists_structure c he hab hcomm hac
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
      obtain ⟨u₁, hu₁, hsu, -⟩ := T7D.frame_fixed c F.ρ F.ρ' F.ρ₃ F.hnbr F.hnbr' F.hne₁ F.hne₂
        F.hn₁ F.hn₂ F.hn₁' F.hn₂' F.hz F.hz' F.hj hbK hb'K ob ob'
      have hRsyl : IsSylow2In F.ρ.R K := by rw [← hρK]; exact F.ρ.hRK
      have hR'syl : IsSylow2In F.ρ'.R K' := by rw [← hρ'K]; exact F.ρ'.hRK
      have hc2 : Commutes F.ρ.R F.ρ'.R :=
        hΩ.commutes_of_twin_of_isPGroup hK hK' hKK'.symm hz hz' (hρK ▸ F.ρ.hRK.1)
          (hρ'K ▸ F.ρ'.hRK.1) (S.isPGroup'.to_le (sup_le hρS hρ'S))
      have hCx : ∀ x ∈ F.ρ.R, ∀ y ∈ F.ρ'.R, orderOf x = 4 → orderOf y = 4 →
          Subgroup.centralizer ({x * y} : Set G) ≤ H := by
        intro x hx y hy ox oy t ht
        obtain ⟨c₁, hc₁, hc₁u⟩ := c23_2_fuse (p := p) (f := f) G Ω K K' z hs W hW hzW u huK huW
          hu1 huz hu2 K (mem_twinSet_self hK hz) K' hs.hK' hKK' F.ρ.R F.ρ'.R hRsyl hR'syl hc2
          x hx y hy ox oy
        have ht' : t * (x * y) = (x * y) * t := Subgroup.mem_centralizer_singleton_iff.mp ht
        have hu' : u = c₁⁻¹ * (x * y) * c₁ := by rw [← hc₁u]; group
        have hmem : c₁⁻¹ * t * c₁ ∈ Subgroup.centralizer ({u} : Set G) := by
          rw [Subgroup.mem_centralizer_singleton_iff]
          calc c₁⁻¹ * t * c₁ * u = c₁⁻¹ * (t * (x * y)) * c₁ := by rw [hu']; group
            _ = c₁⁻¹ * ((x * y) * t) * c₁ := by rw [ht']
            _ = u * (c₁⁻¹ * t * c₁) := by rw [hu']; group
        have h4 : t = c₁ * (c₁⁻¹ * t * c₁) * c₁⁻¹ := by group
        rw [h4]
        exact H.mul_mem (H.mul_mem (hCz hc₁) (hCu hmem)) (H.inv_mem (hCz hc₁))
      have hu₁H : Subgroup.centralizer ({u₁} : Set G) ≤ H := by
        rcases hu₁ with rfl | rfl
        · exact hCx _ hbR _ hb'R ob ob'
        · exact hCx _ (F.ρ.R.inv_mem hbR) _ hb'R (by rw [orderOf_inv]; exact ob) ob'
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
      have hDH := T7E.rep_R_le c F he hab hcomm hac hrH hr'H hsH hWH
      have hMH : MGrp Ω W₁ ≤ H := iSup₂_le fun R hR => by
        obtain ⟨KR, hKR, hRK⟩ := exists_isSylow2In_of_mem_RSet hR.1
        obtain ⟨σ', -, hσ'R⟩ := T7D.exists_rep hp hq hΩ hW₁ hKR hRK hR
        rw [← hσ'R]
        exact hDH σ'
      obtain ⟨y, hy⟩ := S4.exists_conj_of_mem he (T7D.imgQ_mem F.ρ) (T7D.imgQ_mem σ)
      obtain ⟨m', hm'M, hym'⟩ := T7E.exists_mem_MGrp_of_mem_muGroup y
      have hm'N : m' ∈ Subgroup.normalizer (W₁ : Set G) := Thompson.MGrp_le_normalizer Ω W₁ hm'M
      have himg : Thompson.piG W₁ m' * F.ρ.img * (Thompson.piG W₁ m')⁻¹ = σ.img := by
        rw [← hym']
        exact congrArg Subtype.val hy
      have hKm : conjSub m' F.ρ.K = σ.K :=
        c.K_eq_of_img_eq (T7D.conjRep c.hΩ hm'N F.ρ) σ (by rw [T7D.conjRep_img, himg])
      exact ⟨m', hMH hm'M, by rw [← hσK, ← hKm, hρK]⟩
  have step : ∀ J' : Subgroup G, dstarAdj Ω K J' → ∃ h ∈ H, conjSub h K = J' := by
    rintro J' ⟨hJ'Ω, hadj⟩
    rcases hadj with h | h
    · obtain ⟨W₁, hW₁, R₁, hR₁, T, hT, hR₁K, hTJ'⟩ :=
        Thompson.exists_W_of_mem_omegaStarNbr hp hq hΩ hK h
      have hzW₁ : z ∈ W₁ := (Thompson.uniqueInvolution_mem_W hp hq hΩ hW₁ hK hR₁ hR₁K hz).2
      exact key W₁ hW₁ hzW₁ J' hJ'Ω ⟨T, hT, hTJ'⟩
    · obtain ⟨W₁, hW₁, R₁, hR₁, T, hT, hR₁J', hTK⟩ :=
        Thompson.exists_W_of_mem_omegaStarNbr hp hq hΩ hJ'Ω h
      have hzW₁ : z ∈ W₁ := (Thompson.uniqueInvolution_mem_W hp hq hΩ hW₁ hK hT hTK hz).2
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

end CFSG.ClassicalInvolution.Asc77
