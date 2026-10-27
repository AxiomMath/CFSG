module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23PfSetup
public import CFSG.ClassicalInvolution.Q3.Q3T7P24H03

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

section Reps

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {W : Subgroup G}

theorem exists_twin_reps {K K' : Subgroup G} {z : G}
    (hs : CFSG.ClassicalInvolution.Q8P.Asc77.Hyp23Setting Ω K K' z) (hW : W ∈ WSet Ω) (hzW : z ∈ W) :
    ∃ (S : Sylow 2 G) (ρ ρ' : Thompson.Rep Ω W), W ≤ (S : Subgroup G) ∧ ρ.K = K ∧ ρ'.K = K' ∧
      ρ.R ≤ (S : Subgroup G) ∧ ρ'.R ≤ (S : Subgroup G) ∧ ρ'.K ∈ omegaNbr Ω ρ.K ∧
      ρ.K ∈ omegaNbr Ω ρ'.K ∧ T7D.imgQ ρ ≠ T7D.imgQ ρ' ∧
      T7D.imgQ ρ * T7D.imgQ ρ' = T7D.imgQ ρ' * T7D.imgQ ρ := by
  have hst : CFSG.ClassicalInvolution.Q8P.Asc77.AscStand Ω K := hs.stand
  have hΩ : HypOmegaGen Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have hK' : K' ∈ Ω := hs.hK'.1
  have c : Q3CL.Thompson.Ctx Ω W := CFSG.ClassicalInvolution.Q8P.Asc77.T7D.ctx_of_stand hst hW
  obtain ⟨S, R, R', hWS, hRsyl, hR'syl, hRS, hR'S⟩ := CFSG.ClassicalInvolution.Q8P.Asc77.T7D.exists_sylow_frame hs hW hzW
  have hRD : R ∈ DSet Ω W :=
    Q3CL.Thompson.mem_DSet_of_le_sylow hΩ hW hWS (mem_RSet_of_isSylow2In hK hRsyl) hRS
  have hR'D : R' ∈ DSet Ω W :=
    Q3CL.Thompson.mem_DSet_of_le_sylow hΩ hW hWS (mem_RSet_of_isSylow2In hK' hR'syl) hR'S
  obtain ⟨ρ, hρK, hρR⟩ := CFSG.ClassicalInvolution.Q8P.Asc77.T7D.exists_rep hΩ hW hK hRsyl hRD
  obtain ⟨ρ', hρ'K, hρ'R⟩ := CFSG.ClassicalInvolution.Q8P.Asc77.T7D.exists_rep hΩ hW hK' hR'syl hR'D
  have hne : ρ.K ≠ ρ'.K := by
    rw [hρK, hρ'K]
    exact hs.hne.symm
  have hρnbr : ρ'.K ∈ omegaNbr Ω ρ.K := by
    have hperp : K' ∈ KPerp Ω K := by rw [hs.perp]; exact Or.inr rfl
    rw [hρK, hρ'K]
    rcases hperp with e | e
    · exact absurd e hs.hne
    · exact e
  have hcomm : ρ.img * ρ'.img = ρ'.img * ρ.img := c.comm_of_omega ρ ρ' hρnbr
  refine ⟨S, ρ, ρ', hWS, hρK, hρ'K, hρR ▸ hRS, hρ'R ▸ hR'S, hρnbr,
    c.omega_of_comm ρ' ρ hne.symm hcomm.symm, fun h => hne
      (c.K_eq_of_img_eq ρ ρ' (congrArg Subtype.val h)), Subtype.ext hcomm⟩

theorem rep_dichotomy {K K' : Subgroup G} {z : G}
    (hs : CFSG.ClassicalInvolution.Q8P.Asc77.Hyp23Setting Ω K K' z) (hW : W ∈ WSet Ω) (ρ ρ' : Thompson.Rep Ω W)
    (hab : T7D.imgQ ρ ≠ T7D.imgQ ρ')
    (hcomm : T7D.imgQ ρ * T7D.imgQ ρ' = T7D.imgQ ρ' * T7D.imgQ ρ) :
    (∀ σ : Thompson.Rep Ω W, σ.K = ρ.K ∨ σ.K = ρ'.K) ∨
      ∃ e : ↥(muGroup Ω W) ≃* Equiv.Perm (Fin 4),
        (∀ x, x ∈ Thompson.muDelta Ω W ↔ (e x).IsSwap) ∧ ∃ σ : Thompson.Rep Ω W,
          T7D.imgQ ρ * T7D.imgQ σ ≠ T7D.imgQ σ * T7D.imgQ ρ ∧
          T7D.imgQ ρ' * T7D.imgQ σ ≠ T7D.imgQ σ * T7D.imgQ ρ' := by
  have hst0 : CFSG.ClassicalInvolution.Q8P.Asc77.AscStand Ω K := hs.stand
  obtain ⟨-, hcl⟩ := Q3T7.c231_clique ⟨hst0.hyp, hst0.cls, hst0.aEmpty⟩ hst0.mem hst0.trans hs.hz hs.hK' hs.hne hs.perp hW
  have hst : CFSG.ClassicalInvolution.Q8P.Asc77.AscStand Ω K := hs.stand
  have hP : Q3CL.PartIHypG Ω := ⟨hst.hyp, hst.cls, hst.aEmpty⟩
  have c : Q3CL.Thompson.Ctx Ω W := CFSG.ClassicalInvolution.Q8P.Asc77.T7D.ctx_of_stand hst hW
  have hTT : Star3T.IsTT (Thompson.muDelta Ω W) :=
    Q3T6.Mu.isTT_muDelta hP hW
  have hS : Star3T.IsStar (Thompson.muDelta Ω W) :=
    Q3T6.Mu.isStar_muDelta (Q3CL.T8.ctxOf hP hW)
  by_cases hall : ∀ σ : Thompson.Rep Ω W, σ.K = ρ.K ∨ σ.K = ρ'.K
  · exact Or.inl hall
  right
  push Not at hall
  obtain ⟨σ, hσ1, hσ2⟩ := hall
  set Δ := Thompson.muDelta Ω W with hΔ
  set a := T7D.imgQ ρ with ha
  set b := T7D.imgQ ρ' with hb
  set x := T7D.imgQ σ with hx
  have haΔ : a ∈ Δ := T7D.imgQ_mem ρ
  have hbΔ : b ∈ Δ := T7D.imgQ_mem ρ'
  have hxΔ : x ∈ Δ := T7D.imgQ_mem σ
  have hxa : x ≠ a := fun h => hσ1 (c.K_eq_of_img_eq σ ρ (congrArg Subtype.val h))
  have hxb : x ≠ b := fun h => hσ2 (c.K_eq_of_img_eq σ ρ' (congrArg Subtype.val h))
  have hcent : ∀ d ∈ ({a, b} : Set ↥(muGroup Ω W)), Star3T.cent Δ d = {a, b} := by
    intro d hd
    have hdΔ : d ∈ Δ := by
      rcases hd with rfl | rfl
      · exact haΔ
      · exact hbΔ
    have hsub : ({a, b} : Set ↥(muGroup Ω W)) ⊆ Star3T.cent Δ d := by
      intro y hy
      rcases hd with rfl | rfl
      · rcases hy with rfl | rfl
        · exact Star3T.self_mem_cent haΔ
        · exact ⟨hbΔ, hcomm.symm⟩
      · rcases hy with rfl | rfl
        · exact ⟨haΔ, hcomm⟩
        · exact Star3T.self_mem_cent hbΔ
    exact (Set.eq_of_subset_of_ncard_le hsub
      (by rw [hcl d hdΔ, Set.ncard_pair hab]) (Set.toFinite _)).symm
  have hreach : ∀ y, Relation.ReflTransGen (Star3T.Adj Δ) a y → y = a ∨ y = b := by
    intro y hy
    induction hy with
    | refl => exact Or.inl rfl
    | @tail y₁ y₂ _ hadj ih =>
      obtain ⟨-, h2, hc⟩ := hadj
      have hy₁ : y₁ ∈ ({a, b} : Set ↥(muGroup Ω W)) := by
        rcases ih with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
      have : y₂ ∈ Star3T.cent Δ y₁ := ⟨h2, hc.symm⟩
      rw [hcent y₁ hy₁] at this
      exact this
  have hnc : ¬ Star3T.Conn Δ a x := fun h => by
    rcases hreach x h with h | h
    · exact hxa h
    · exact hxb h
  obtain ⟨e, he⟩ := Star3T.exists_mulEquiv_perm_four hTT hS haΔ hxΔ hnc (hcl a haΔ)
  have hna : a * x ≠ x * a := fun h => by
    have : x ∈ Star3T.cent Δ a := ⟨hxΔ, h.symm⟩
    rw [hcent a (Or.inl rfl)] at this
    rcases this with h | h
    · exact hxa h
    · exact hxb h
  have hnb : b * x ≠ x * b := fun h => by
    have : x ∈ Star3T.cent Δ b := ⟨hxΔ, h.symm⟩
    rw [hcent b (Or.inr rfl)] at this
    rcases this with h | h
    · exact hxa h
    · exact hxb h
  exact ⟨e, he, σ, hna, hnb⟩

theorem frame4_of_twin_reps {K K' : Subgroup G} {z : G}
    (hs : CFSG.ClassicalInvolution.Q8P.Asc77.Hyp23Setting Ω K K' z) (hW : W ∈ WSet Ω) {ρ ρ' σ : Thompson.Rep Ω W}
    (hρK : ρ.K = K) (hρ'K : ρ'.K = K') (hnbr : ρ'.K ∈ omegaNbr Ω ρ.K)
    (hnbr' : ρ.K ∈ omegaNbr Ω ρ'.K)
    (hac : T7D.imgQ ρ * T7D.imgQ σ ≠ T7D.imgQ σ * T7D.imgQ ρ)
    (hbc : T7D.imgQ ρ' * T7D.imgQ σ ≠ T7D.imgQ σ * T7D.imgQ ρ') :
    ∃ F : T7E.Frame4 Ω W, F.ρ = ρ ∧ F.ρ' = ρ' ∧ F.ρ₃ = σ ∧ F.z = z := by
  have hst : CFSG.ClassicalInvolution.Q8P.Asc77.AscStand Ω K := hs.stand
  have hΩ : HypOmegaGen Ω := hst.hyp
  have hz : IsUniqueInvolution K z := hs.hz
  have hz' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hs.hK'
  have c : Q3CL.Thompson.Ctx Ω W := CFSG.ClassicalInvolution.Q8P.Asc77.T7D.ctx_of_stand hst hW
  have hzρ : IsUniqueInvolution ρ.K z := by rw [hρK]; exact hz
  have hzρ' : IsUniqueInvolution ρ'.K z := by rw [hρ'K]; exact hz'
  have hne₁ : ρ.K ≠ σ.K := fun h => hac (by
    have h1 : T7D.imgQ ρ = T7D.imgQ σ := Subtype.ext (c.img_eq_of_K_eq ρ σ h)
    rw [← h1])
  have hne₂ : ρ'.K ≠ σ.K := fun h => hbc (by
    have h1 : T7D.imgQ ρ' = T7D.imgQ σ := Subtype.ext (c.img_eq_of_K_eq ρ' σ h)
    rw [← h1])
  obtain ⟨j, hj⟩ := Sec6Gen.exists_uniqueInvolution hΩ σ.hK
  exact ⟨⟨ρ, ρ', σ, z, j, hzρ, hzρ', hj, hnbr, hnbr', hne₁, hne₂,
    fun h => hac (Subtype.ext (c.comm_of_omega ρ σ h)),
    fun h => hbc (Subtype.ext (c.comm_of_omega ρ' σ h)),
    fun h => hac (Subtype.ext (c.comm_of_omega σ ρ h).symm),
    fun h => hbc (Subtype.ext (c.comm_of_omega σ ρ' h).symm)⟩, rfl, rfl, rfl, rfl⟩

theorem trans_of_fuse {K K' : Subgroup G} {z : G}
    (hs : CFSG.ClassicalInvolution.Q8P.Asc77.Hyp23Setting Ω K K' z) (hW : W ∈ WSet Ω)
    (hzW : z ∈ W) {u : G} (huK : u ∈ K ⊔ K') (huW : u ∈ W) (hu1 : u ≠ 1) (huz : u ≠ z)
    (hu2 : u * u = 1)
    (hfuse : ∀ L ∈ twinSet Ω K, ∀ L' ∈ twinSet Ω K, L' ≠ L → ∀ R₁ R₂ : Subgroup G,
      IsSylow2In R₁ L → IsSylow2In R₂ L' → Commutes R₁ R₂ → ∀ x ∈ R₁, ∀ y ∈ R₂,
        orderOf x = 4 → orderOf y = 4 →
          ∃ c ∈ Subgroup.centralizer ({z} : Set G), c * u * c⁻¹ = x * y) :
    ∀ J ∈ dstarComp Ω K,
      ∃ h ∈ Subgroup.centralizer ({u} : Set G) ⊔ Subgroup.centralizer ({z} : Set G),
        conjSub h K = J := by
  intro J hJ
  have hst : CFSG.ClassicalInvolution.Q8P.Asc77.AscStand Ω K := hs.stand
  have : Fact (Q3CL.ClassicalClause Ω) := ⟨hst.cls⟩
  have hΩ : HypOmegaGen Ω := hst.hyp
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
      have hRsyl : IsSylow2In F.ρ.R K := by rw [← hρK]; exact F.ρ.hRK
      have hR'syl : IsSylow2In F.ρ'.R K' := by rw [← hρ'K]; exact F.ρ'.hRK
      have hc2 : Commutes F.ρ.R F.ρ'.R :=
        CFSG.ClassicalInvolution.Q8P.Asc77.HypOmegaMod.commutes_of_twin_of_isPGroup hΩ hK hK' hKK'.symm hz hz' (hρK ▸ F.ρ.hRK.1)
          (hρ'K ▸ F.ρ'.hRK.1) (S.isPGroup'.to_le (sup_le hρS hρ'S))
      have hCx : ∀ x ∈ F.ρ.R, ∀ y ∈ F.ρ'.R, orderOf x = 4 → orderOf y = 4 →
          Subgroup.centralizer ({x * y} : Set G) ≤ H := by
        intro x hx y hy ox oy t ht
        obtain ⟨c₁, hc₁, hc₁u⟩ := hfuse K (mem_twinSet_self hK hz) K' hs.hK' hKK' F.ρ.R F.ρ'.R hRsyl hR'syl hc2
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
end Reps

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
