module

public import CFSG.ClassicalInvolution.Asc77.AscT7EFrame

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace T7E

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

theorem exists_twin_reps [IsSimpleGroup G] {K K' : Subgroup G} {z : G}
    (hs : Hyp23Setting p f Ω K K' z) (hW : W ∈ WSet Ω) (hzW : z ∈ W) :
    ∃ (S : Sylow 2 G) (ρ ρ' : Thompson.Rep Ω W), W ≤ (S : Subgroup G) ∧ ρ.K = K ∧ ρ'.K = K' ∧
      ρ.R ≤ (S : Subgroup G) ∧ ρ'.R ≤ (S : Subgroup G) ∧ ρ'.K ∈ omegaNbr Ω ρ.K ∧
      ρ.K ∈ omegaNbr Ω ρ'.K ∧ T7D.imgQ ρ ≠ T7D.imgQ ρ' ∧
      T7D.imgQ ρ * T7D.imgQ ρ' = T7D.imgQ ρ' * T7D.imgQ ρ := by
  have hst : AscStand p f Ω K := hs.stand
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have hK' : K' ∈ Ω := hs.hK'.1
  have c : Thompson.Ctx p f Ω W := T7D.ctx_of_stand hst hW
  obtain ⟨S, R, R', hWS, hRsyl, hR'syl, hRS, hR'S⟩ := T7D.exists_sylow_frame hs hW hzW
  have hRD : R ∈ DSet Ω W :=
    Thompson.mem_DSet_of_le_sylow hp hq hΩ hW hWS (mem_RSet_of_isSylow2In hK hRsyl) hRS
  have hR'D : R' ∈ DSet Ω W :=
    Thompson.mem_DSet_of_le_sylow hp hq hΩ hW hWS (mem_RSet_of_isSylow2In hK' hR'syl) hR'S
  obtain ⟨ρ, hρK, hρR⟩ := T7D.exists_rep hp hq hΩ hW hK hRsyl hRD
  obtain ⟨ρ', hρ'K, hρ'R⟩ := T7D.exists_rep hp hq hΩ hW hK' hR'syl hR'D
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

theorem rep_dichotomy [IsSimpleGroup G] {K K' : Subgroup G} {z : G}
    (hs : Hyp23Setting p f Ω K K' z) (hW : W ∈ WSet Ω) (ρ ρ' : Thompson.Rep Ω W)
    (hab : T7D.imgQ ρ ≠ T7D.imgQ ρ')
    (hcomm : T7D.imgQ ρ * T7D.imgQ ρ' = T7D.imgQ ρ' * T7D.imgQ ρ) :
    (∀ σ : Thompson.Rep Ω W, σ.K = ρ.K ∨ σ.K = ρ'.K) ∨
      ∃ e : ↥(muGroup Ω W) ≃* Equiv.Perm (Fin 4),
        (∀ x, x ∈ Thompson.muDelta Ω W ↔ (e x).IsSwap) ∧ ∃ σ : Thompson.Rep Ω W,
          T7D.imgQ ρ * T7D.imgQ σ ≠ T7D.imgQ σ * T7D.imgQ ρ ∧
          T7D.imgQ ρ' * T7D.imgQ σ ≠ T7D.imgQ σ * T7D.imgQ ρ' := by
  obtain ⟨-, hcl⟩ := c23_1_clique_proved (p := p) (f := f) G Ω K K' z hs W hW
  have hst : AscStand p f Ω K := hs.stand
  have hP : PartIHyp p f Ω := ⟨hst.odd, hst.five, hst.hyp, hst.aEmpty⟩
  have c : Thompson.Ctx p f Ω W := T7D.ctx_of_stand hst hW
  have hTT : Star3T.IsTT (Thompson.muDelta Ω W) :=
    Thompson.isTT_muDelta hst.odd hst.five hst.hyp hW (thompsonCube G Ω hP W hW)
  have hS : Star3T.IsStar (Thompson.muDelta Ω W) :=
    Thompson.isStar_muDelta hst.odd hst.five hst.hyp hW (thompsonStar G Ω hP W hW)
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

theorem frame4_of_twin_reps [IsSimpleGroup G] {K K' : Subgroup G} {z : G}
    (hs : Hyp23Setting p f Ω K K' z) (hW : W ∈ WSet Ω) {ρ ρ' σ : Thompson.Rep Ω W}
    (hρK : ρ.K = K) (hρ'K : ρ'.K = K') (hnbr : ρ'.K ∈ omegaNbr Ω ρ.K)
    (hnbr' : ρ.K ∈ omegaNbr Ω ρ'.K)
    (hac : T7D.imgQ ρ * T7D.imgQ σ ≠ T7D.imgQ σ * T7D.imgQ ρ)
    (hbc : T7D.imgQ ρ' * T7D.imgQ σ ≠ T7D.imgQ σ * T7D.imgQ ρ') :
    ∃ F : Frame4 Ω W, F.ρ = ρ ∧ F.ρ' = ρ' ∧ F.ρ₃ = σ ∧ F.z = z := by
  have hst : AscStand p f Ω K := hs.stand
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hz : IsUniqueInvolution K z := hs.hz
  have hz' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hs.hK'
  have c : Thompson.Ctx p f Ω W := T7D.ctx_of_stand hst hW
  have hzρ : IsUniqueInvolution ρ.K z := by rw [hρK]; exact hz
  have hzρ' : IsUniqueInvolution ρ'.K z := by rw [hρ'K]; exact hz'
  have hne₁ : ρ.K ≠ σ.K := fun h => hac (by
    have h1 : T7D.imgQ ρ = T7D.imgQ σ := Subtype.ext (c.img_eq_of_K_eq ρ σ h)
    rw [← h1])
  have hne₂ : ρ'.K ≠ σ.K := fun h => hbc (by
    have h1 : T7D.imgQ ρ' = T7D.imgQ σ := Subtype.ext (c.img_eq_of_K_eq ρ' σ h)
    rw [← h1])
  obtain ⟨j, hj⟩ := hΩ.exists_uniqueInvolution hp hq σ.hK
  exact ⟨⟨ρ, ρ', σ, z, j, hzρ, hzρ', hj, hnbr, hnbr', hne₁, hne₂,
    fun h => hac (Subtype.ext (c.comm_of_omega ρ σ h)),
    fun h => hbc (Subtype.ext (c.comm_of_omega ρ' σ h)),
    fun h => hac (Subtype.ext (c.comm_of_omega σ ρ h).symm),
    fun h => hbc (Subtype.ext (c.comm_of_omega σ ρ' h).symm)⟩, rfl, rfl, rfl, rfl⟩

end T7E

end CFSG.ClassicalInvolution.Asc77
