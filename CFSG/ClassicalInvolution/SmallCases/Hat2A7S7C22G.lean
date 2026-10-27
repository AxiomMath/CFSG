module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S7C22B
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S7C22F
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S7E1
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S3Main

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Hat2A7S

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Balance
open scoped commutatorElement

section Final


variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

theorem Frame3.hyp51 (hs : Pre2A7 Ω K) {K₁ K₂ K₃ R₁ R₂ R₃ : Subgroup G} {u₁ u₂ u₃ : G}
    (F : Frame3 Ω z K₁ K₂ K₃ R₁ R₂ R₃ u₁ u₂ u₃) :
    Hyp51 (Subgroup.closure ({z, u₁ * u₂, u₂ * u₃} : Set G)) := by
  refine ⟨F.isElemAbelian_B hs.hyp, F.natCard_B hs.hyp, fun c hcB hc1 => ?_⟩
  by_cases hcz : c = z
  · rw [hcz]
    exact F.hyp51At_z hs.hyp hs.classical
  · exact F.hyp51At_ne hs hcB hc1 hcz

theorem allFrame3Hyp51 (hs : Pre2A7 Ω K) : AllFrame3Hyp51 Ω z :=
  fun _ _ _ _ _ _ _ _ _ F => F.hyp51 hs

theorem exists_frame3 (hΩ : HypOmegaGen Ω) {K₁ K₂ K₃ : Subgroup G} (h₁ : K₁ ∈ Ω) (h₂ : K₂ ∈ Ω)
    (h₃ : K₃ ∈ Ω) (hz₁ : IsUniqueInvolution K₁ z) (hz₂ : IsUniqueInvolution K₂ z)
    (hz₃ : IsUniqueInvolution K₃ z) (n₁₂ : K₂ ≠ K₁) (n₁₃ : K₃ ≠ K₁) (n₂₃ : K₃ ≠ K₂) :
    ∃ (R₁ R₂ R₃ : Subgroup G) (u₁ u₂ u₃ : G), Frame3 Ω z K₁ K₂ K₃ R₁ R₂ R₃ u₁ u₂ u₃ := by
  obtain ⟨R₁, R₂, hR₁, hR₂, hc⟩ := T7X.exists_commuting_sylow_twin hΩ h₁ h₂ n₁₂ hz₁ hz₂
  obtain ⟨u₁, hu₁, ho₁⟩ :=
    Hat2A7M.P25.exists_orderOf_eq_four_of_mem_RSet hΩ (mem_RSet_of_isSylow2In h₁ hR₁)
  obtain ⟨u₂, hu₂, ho₂⟩ :=
    Hat2A7M.P25.exists_orderOf_eq_four_of_mem_RSet hΩ (mem_RSet_of_isSylow2In h₂ hR₂)
  obtain ⟨R₃, u₃, F⟩ := exists_frame3_extend hΩ h₁ h₂ h₃ hz₁ hz₂ hz₃ n₁₂ n₁₃ n₂₃ hR₁ hR₂ hc
    hu₁ ho₁ hu₂ ho₂
  exact ⟨R₁, R₂, R₃, u₁, u₂, u₃, F⟩

theorem exists_third {α : Type*} {a b c L L' : α} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ M, (M = a ∨ M = b ∨ M = c) ∧ M ≠ L ∧ M ≠ L' := by
  by_cases h1 : a ≠ L ∧ a ≠ L'
  · exact ⟨a, Or.inl rfl, h1.1, h1.2⟩
  by_cases h2 : b ≠ L ∧ b ≠ L'
  · exact ⟨b, Or.inr (Or.inl rfl), h2.1, h2.2⟩
  have h1' : a = L ∨ a = L' := by
    by_contra h
    push Not at h
    exact h1 h
  have h2' : b = L ∨ b = L' := by
    by_contra h
    push Not at h
    exact h2 h
  refine ⟨c, Or.inr (Or.inr rfl), fun hcL => ?_, fun hcL => ?_⟩
  · rcases h1' with h | h
    · exact hac (h.trans hcL.symm)
    · rcases h2' with h' | h'
      · exact hbc (h'.trans hcL.symm)
      · exact hab (h.trans h'.symm)
  · rcases h1' with h | h
    · rcases h2' with h' | h'
      · exact hab (h.trans h'.symm)
      · exact hbc (h'.trans hcL.symm)
    · exact hac (h.trans hcL.symm)

theorem htw_of_perp (hs : Pre2A7 Ω K) (hperp : KPerp Ω K = twinSet Ω K) :
    ∀ L ∈ Ω, ∀ J ∈ omegaNbr Ω L, J ∈ twinSet Ω L := by
  intro L hL J hJ
  obtain ⟨g, rfl⟩ := hs.trans L hL
  have h1 : conjSub g⁻¹ J ∈ omegaNbr Ω K := by
    have := omegaNbr_conj hs.hyp.conjInvariant hJ g⁻¹
    rwa [conjSub_inv_conjSub] at this
  have h2 : conjSub g⁻¹ J ∈ twinSet Ω K := by
    have : conjSub g⁻¹ J ∈ KPerp Ω K := Set.mem_insert_of_mem _ h1
    rwa [hperp] at this
  have h3 := twinSet_conj hs.hyp.conjInvariant h2 g
  rwa [conjSub_conjSub_inv] at h3

theorem dstarComp_involution (hs : Pre2A7 Ω K)
    (htw : ∀ L ∈ Ω, ∀ J ∈ omegaNbr Ω L, J ∈ twinSet Ω L) (hz : IsUniqueInvolution K z)
    {J : Subgroup G} (hJ : J ∈ dstarComp Ω K) : J ∈ Ω ∧ IsUniqueInvolution J z := by
  induction hJ with
  | refl => exact ⟨hs.mem, hz⟩
  | tail hab hbc ih =>
    rename_i b c
    obtain ⟨hbΩ, hbz⟩ := ih
    obtain ⟨hcΩ, hcase⟩ := hbc
    refine ⟨hcΩ, ?_⟩
    rcases hcase with h | h
    · obtain ⟨-, w, hw1, hw2⟩ :=
        htw b hbΩ c (omegaStarNbr_subset_omegaNbr_a7 hs hbΩ hcΩ h)
      have e : w = z := (hbz.eq hw1).symm
      rwa [e] at hw2
    · obtain ⟨-, w, hw1, hw2⟩ :=
        htw c hcΩ b (omegaStarNbr_subset_omegaNbr_a7 hs hcΩ hbΩ h)
      have e : w = z := (hbz.eq hw2).symm
      rwa [e] at hw1

theorem htrans_of_centralizer_le (hs : Pre2A7 Ω K)
    (htw : ∀ L ∈ Ω, ∀ J ∈ omegaNbr Ω L, J ∈ twinSet Ω L) (hz : IsUniqueInvolution K z)
    {H : Subgroup G} (hzH : Subgroup.centralizer ({z} : Set G) ≤ H) :
    ∀ J ∈ dstarComp Ω K, ∃ h ∈ H, conjSub h K = J := by
  intro J hJ
  obtain ⟨hJΩ, hJz⟩ := dstarComp_involution hs htw hz hJ
  obtain ⟨g, hg⟩ := hs.trans J hJΩ
  refine ⟨g, hzH ?_, hg⟩
  have h1 : IsUniqueInvolution (conjSub g K) (g * z * g⁻¹) := hz.conj g
  rw [hg] at h1
  have e : g * z * g⁻¹ = z := (hJz.eq h1).symm
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc g * z = g * z * g⁻¹ * g := by group
    _ = z * g := by rw [e]

theorem stdCent_of_twinProducts
    (htw : ∀ L ∈ Ω, ∀ J ∈ omegaNbr Ω L, J ∈ twinSet Ω L) (hz : IsUniqueInvolution K z)
    {H : Subgroup G} (hzH : Subgroup.centralizer ({z} : Set G) ≤ H)
    (htwin : ∀ L ∈ twinSet Ω K, ∀ L' ∈ twinSet Ω K, L' ≠ L → ∀ R₁ R₂ : Subgroup G,
      IsSylow2In R₁ L → IsSylow2In R₂ L' → Commutes R₁ R₂ → ∀ x ∈ R₁, ∀ y ∈ R₂, orderOf x = 4 →
        orderOf y = 4 → Subgroup.centralizer ({x * y} : Set G) ≤ H) :
    StdCent Ω K H z where
  z_le := hzH
  nonTwin := by
    intro L hL J hJ z' hz' hzz'
    exfalso
    obtain ⟨-, w, hw1, hw2⟩ := htw L hL.1 J hJ
    have hzL := isUniqueInvolution_of_mem_twinSet hz hL
    exact hzz' ((hzL.eq hw1).trans (hw2.eq hz')).symm
  twin := htwin

theorem commutator_oddCore_le_alphaOf_pair {c : G} (hc1 : c ≠ 1) (A : Subgroup G) (hcA : c ∈ A) :
    ⁅oddCoreOf (Subgroup.centralizer ({c} : Set G)), A⁆ ≤ alphaOf A := by
  unfold alphaOf
  exact le_sup_of_le_left (le_iSup₂_of_le c hcA (le_iSup_of_le hc1 le_rfl))

theorem exists_frame_of_data (hs : Pre2A7 Ω K) {K₁ K₂ K₃ R₁ R₂ R₃ : Subgroup G} {u₁ u₂ u₃ : G}
    (F₀ : Frame3 Ω z K₁ K₂ K₃ R₁ R₂ R₃ u₁ u₂ u₃) {L L' R R' : Subgroup G} {x y : G}
    (hL : L ∈ Ω) (hL' : L' ∈ Ω) (hzL : IsUniqueInvolution L z) (hzL' : IsUniqueInvolution L' z)
    (hne : L' ≠ L) (hR : IsSylow2In R L) (hR' : IsSylow2In R' L') (hc : Commutes R R')
    (hx : x ∈ R) (hx4 : orderOf x = 4) (hy : y ∈ R') (hy4 : orderOf y = 4) :
    ∃ (M R'' : Subgroup G) (w : G), Frame3 Ω z L L' M R R' R'' x y w := by
  obtain ⟨M, hM, hML, hML'⟩ : ∃ M, (M = K₁ ∨ M = K₂ ∨ M = K₃) ∧ M ≠ L ∧ M ≠ L' :=
    exists_third (fun h => F₀.ne₁₂ h.symm) (fun h => F₀.ne₁₃ h.symm) (fun h => F₀.ne₂₃ h.symm)
  have hMΩ : M ∈ Ω ∧ IsUniqueInvolution M z := by
    rcases hM with rfl | rfl | rfl
    · exact ⟨F₀.mem₁, F₀.hz₁⟩
    · exact ⟨F₀.mem₂, F₀.hz₂⟩
    · exact ⟨F₀.mem₃, F₀.hz₃⟩
  obtain ⟨R'', w, F⟩ := exists_frame3_extend hs.hyp hL hL' hMΩ.1 hzL hzL' hMΩ.2 hne hML hML' hR
    hR' hc hx hx4 hy hy4
  exact ⟨M, R'', w, F⟩

theorem twinProduct_centralizer_le_normalizer (hs : Pre2A7 Ω K)
    (htw : ∀ L ∈ Ω, ∀ J ∈ omegaNbr Ω L, J ∈ twinSet Ω L) (hall : AllFrame3Hyp51 Ω z)
    {K₁ K₂ K₃ R₁ R₂ R₃ : Subgroup G} {u₁ u₂ u₃ : G}
    (F₀ : Frame3 Ω z K₁ K₂ K₃ R₁ R₂ R₃ u₁ u₂ u₃) {L L' R R' : Subgroup G} {x y : G}
    (hL : L ∈ Ω) (hL' : L' ∈ Ω) (hzL : IsUniqueInvolution L z) (hzL' : IsUniqueInvolution L' z)
    (hne : L' ≠ L) (hR : IsSylow2In R L) (hR' : IsSylow2In R' L') (hc : Commutes R R')
    (hx : x ∈ R) (hx4 : orderOf x = 4) (hy : y ∈ R') (hy4 : orderOf y = 4) :
    Subgroup.centralizer ({x * y} : Set G) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({z, u₁ * u₂} : Set G)) : Set G) := by
  obtain ⟨M, R'', w, F⟩ := exists_frame_of_data hs F₀ hL hL' hzL hzL' hne hR hR' hc hx hx4 hy hy4
  have hα : alphaOf (Subgroup.closure ({z, x * y} : Set G)) =
      alphaOf (Subgroup.closure ({z, u₁ * u₂} : Set G)) := alpha_const hs hall F F₀
  have hO := F.oddCore_le_normalizer hs.hyp (hall _ _ _ _ _ _ _ _ _ F) (F.x_mem_B hs.hyp)
  rw [hα] at hO
  exact centralizer_le_of_xMem hs htw F.x_sq (F.x_ne_one hs.hyp)
    (F.xMem₃ hs.hyp ⟨x, hx, y, hy, rfl⟩) F.hz₃ _ hO
    (T8T.centralizer_le_normalizer_of_alphaOf_eq hα)

theorem twinProduct_centralizer_le_centralizer (hs : Pre2A7 Ω K)
    (htw : ∀ L ∈ Ω, ∀ J ∈ omegaNbr Ω L, J ∈ twinSet Ω L) (hall : AllFrame3Hyp51 Ω z)
    {K₁ K₂ K₃ R₁ R₂ R₃ : Subgroup G} {u₁ u₂ u₃ : G}
    (F₀ : Frame3 Ω z K₁ K₂ K₃ R₁ R₂ R₃ u₁ u₂ u₃)
    (hbot : alphaOf (Subgroup.closure ({z, u₁ * u₂} : Set G)) = ⊥) {L L' R R' : Subgroup G}
    {x y : G} (hL : L ∈ Ω) (hL' : L' ∈ Ω) (hzL : IsUniqueInvolution L z)
    (hzL' : IsUniqueInvolution L' z) (hne : L' ≠ L) (hR : IsSylow2In R L) (hR' : IsSylow2In R' L')
    (hc : Commutes R R') (hx : x ∈ R) (hx4 : orderOf x = 4) (hy : y ∈ R') (hy4 : orderOf y = 4) :
    Subgroup.centralizer ({x * y} : Set G) ≤ Subgroup.centralizer ({z} : Set G) := by
  obtain ⟨M, R'', w, F⟩ := exists_frame_of_data hs F₀ hL hL' hzL hzL' hne hR hR' hc hx hx4 hy hy4
  have hα : alphaOf (Subgroup.closure ({z, x * y} : Set G)) = ⊥ :=
    (alpha_const hs hall F F₀).trans hbot
  have hzA : z ∈ Subgroup.closure ({z, x * y} : Set G) := Subgroup.subset_closure (by simp)
  have hxyA : x * y ∈ Subgroup.closure ({z, x * y} : Set G) := Subgroup.subset_closure (by simp)
  refine centralizer_le_of_xMem hs htw F.x_sq (F.x_ne_one hs.hyp)
    (F.xMem₃ hs.hyp ⟨x, hx, y, hy, rfl⟩) F.hz₃ (Subgroup.centralizer ({z} : Set G)) ?_ ?_
  · intro n hn
    have h1 := commutator_oddCore_le_alphaOf_pair (F.x_ne_one hs.hyp)
      (Subgroup.closure ({z, x * y} : Set G)) hxyA
    rw [hα] at h1
    have h2 : ⁅n, z⁆ ∈ ⁅oddCoreOf (Subgroup.centralizer ({x * y} : Set G)),
        Subgroup.closure ({z, x * y} : Set G)⁆ := Subgroup.commutator_mem_commutator hn hzA
    have h3 := h1 h2
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h3
    exact Subgroup.mem_centralizer_singleton_iff.mpr h3
  · exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hzA)

theorem no_third_twin (hE : A7ThmE) (hs : Std2A7 Ω K) (hz : IsUniqueInvolution K z)
    {K' K'' : Subgroup G} (hK' : K' ∈ twinSet Ω K) (hne : K' ≠ K) (hK'' : K'' ∈ twinSet Ω K)
    (hne'' : K'' ≠ K) (hne3 : K'' ≠ K') (hperp : KPerp Ω K = twinSet Ω K) : False := by
  have hpre : Pre2A7 Ω K := hs.toPre2A7
  have hΩ : HypOmegaGen Ω := hs.hyp
  have htw := htw_of_perp hpre hperp
  have hall : AllFrame3Hyp51 Ω z := allFrame3Hyp51 hpre
  have hz' := isUniqueInvolution_of_mem_twinSet hz hK'
  have hz'' := isUniqueInvolution_of_mem_twinSet hz hK''
  obtain ⟨R₁, R₂, R₃, u₁, u₂, u₃, F₀⟩ :=
    exists_frame3 hΩ hpre.mem hK'.1 hK''.1 hz hz' hz'' hne hne'' hne3
  have hCz : Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({z, u₁ * u₂} : Set G)) : Set G) := by
    intro g hg
    have hgz : g * z * g⁻¹ = z := by
      have := Subgroup.mem_centralizer_singleton_iff.mp hg
      rw [this]
      group
    have h1 := alpha_const hpre hall (F₀.conj hΩ hgz) F₀
    have e : (g * u₁ * g⁻¹) * (g * u₂ * g⁻¹) = g * (u₁ * u₂) * g⁻¹ := by group
    rw [e, alphaOf_closure_conj hgz] at h1
    exact mem_normalizer_iff_conjSub_eq.mpr h1
  have hstd := stdCent_of_twinProducts htw hz hCz
    (fun L hL L' hL' hLL' S₁ S₂ hS₁ hS₂ hc x hx y hy hx4 hy4 =>
      twinProduct_centralizer_le_normalizer hpre htw hall F₀ hL.1 hL'.1
        (isUniqueInvolution_of_mem_twinSet hz hL) (isUniqueInvolution_of_mem_twinSet hz hL')
        hLL' hS₁ hS₂ hc hx hx4 hy hy4)
  have htop := a7ThmE_apply hE hs hz hK' hne hstd (htrans_of_centralizer_le hpre htw hz hCz)
  have hnorm : (alphaOf (Subgroup.closure ({z, u₁ * u₂} : Set G))).Normal :=
    Subgroup.normalizer_eq_top_iff.mp htop
  have hodd := F₀.odd_alpha hΩ (hall _ _ _ _ _ _ _ _ _ F₀)
  have hbot : alphaOf (Subgroup.closure ({z, u₁ * u₂} : Set G)) = ⊥ := by
    rcases hnorm.eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      rw [h, Subgroup.card_top] at hodd
      have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one
      have hdvd : 2 ∣ Nat.card G := hz2 ▸ orderOf_dvd_natCard z
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)
  have hstd' := stdCent_of_twinProducts htw hz le_rfl
    (fun L hL L' hL' hLL' S₁ S₂ hS₁ hS₂ hc x hx y hy hx4 hy4 =>
      twinProduct_centralizer_le_centralizer hpre htw hall F₀ hbot hL.1 hL'.1
        (isUniqueInvolution_of_mem_twinSet hz hL) (isUniqueInvolution_of_mem_twinSet hz hL')
        hLL' hS₁ hS₂ hc hx hx4 hy hy4)
  have htop' : Subgroup.centralizer ({z} : Set G) = ⊤ :=
    a7ThmE_apply hE hs hz hK' hne hstd' (htrans_of_centralizer_le hpre htw hz le_rfl)
  exact Hat2A7S8.Asc77.T8.not_central_of_ne_one hpre.nonabelian hz.ne_one
    (Subgroup.centralizer_eq_top_iff_subset.mp htop')

end Final

end CFSG.ClassicalInvolution.Hat2A7S
