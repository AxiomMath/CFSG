module

public import CFSG.LocalAnalysis.GH72.Sec5TTools
public import CFSG.LocalAnalysis.GH72.Sec5C13
public import CFSG.LocalAnalysis.GH72.Sec5DTools

public section

namespace CFSG.GH72

open Subgroup CFSG.ABGLocalTools
open scoped commutatorElement MatrixGroups Pointwise

namespace Sec5KConfig

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {ρ : Sec5Roles G A} {p : ℕ}
  (𝔨 : Sec5KConfig ρ p)

theorem isSylowOf_P_of_odd {L : Subgroup G} (hPL : 𝔨.P ≤ L) (hAL : A ≤ normalizer (L : Set G))
    (hL : Odd (Nat.card L)) : IsSylowOf p 𝔨.P L := by
  obtain ⟨R, hR, hPR, hAR⟩ := CFSG.ABGTheoremB.exists_isSylowOf_normalized_ge_of_odd 𝔨.hp
    ρ.isPGroup_A hAL hL hPL 𝔨.isPGroup_P 𝔨.A_le_normalizer_P
  rwa [𝔨.hP.2.2.2 R le_top hR.isPGroup hAR hPR] at hR

theorem A_le_normalizer_V_sup {x : G} (hx : x ∈ ρ.X) :
    A ≤ normalizer ((𝔨.V ⊔ ρ.Y ⊔ zpowers x : Subgroup G) : Set G) := by
  have h1 : A ≤ normalizer ((𝔨.V ⊔ ρ.Y : Subgroup G) : Set G) :=
    (le_inf 𝔨.A_le_normalizer_V (ρ.A_le_normalizer_of_le ρ.Y_le_A)).trans
      (CFSG.ABGTheoremB.normalizer_inf_normalizer_le_normalizer_sup _ _)
  exact (le_inf h1 (ρ.A_le_normalizer_of_le (zpowers_le.mpr (ρ.X_le_A hx)))).trans
    (CFSG.ABGTheoremB.normalizer_inf_normalizer_le_normalizer_sup _ _)

theorem P_le_normalizer_V_sup (hPP : 𝔨.P = 𝔨.Pstar) {x : G} (hPx : 𝔨.P ≤ C x) :
    𝔨.P ≤ normalizer ((𝔨.V ⊔ ρ.Y ⊔ zpowers x : Subgroup G) : Set G) := by
  have hPK : 𝔨.P ≤ 𝔨.K := hPP.le.trans inf_le_right
  have hPK₁ : 𝔨.P ≤ 𝔨.K₁ := hPP.le.trans 𝔨.Pstar_le_K₁
  intro g hg
  have hgV : g ∈ normalizer (𝔨.V : Set G) := 𝔨.K_eq_normalizer_V ▸ hPK hg
  have h1 : g ∈ normalizer ((𝔨.V ⊔ ρ.Y : Subgroup G) : Set G) := by
    apply mem_normalizer_of_map_conj_le
    rw [Subgroup.map_sup, map_conj_eq_of_mem_normalizer hgV]
    refine sup_le le_sup_left ?_
    rintro _ ⟨y, hy, rfl⟩
    have hyA : y ∈ A := ρ.Y_le_A hy
    have hcP : g * y * g⁻¹ * y⁻¹ ∈ 𝔨.P := by
      have h2 : y * g⁻¹ * y⁻¹ ∈ 𝔨.P :=
        (mem_normalizer_iff.mp (𝔨.A_le_normalizer_P hyA) g⁻¹).mp (inv_mem hg)
      have := 𝔨.P.mul_mem hg h2
      simpa [mul_assoc] using this
    have hcK : g * y * g⁻¹ * y⁻¹ ∈ 𝔨.K :=
      𝔨.K.mul_mem (𝔨.K.mul_mem (𝔨.K.mul_mem (hPK hg) (𝔨.A_le_K hyA)) (𝔨.K.inv_mem (hPK hg)))
        (𝔨.K.inv_mem (𝔨.A_le_K hyA))
    have hcO : g * y * g⁻¹ * y⁻¹ ∈ O 𝔨.K₁ := by
      have := 𝔨.commutator_K₁_Y_le (commutator_mem_commutator (hPK₁ hg) hy)
      rwa [commutatorElement_def] at this
    have hc : g * y * g⁻¹ * y⁻¹ ∈ 𝔨.V := by
      rw [← 𝔨.V_eq]
      exact ⟨⟨hcP, hcK⟩, hcO⟩
    have e : (MulAut.conj g).toMonoidHom y = g * y * g⁻¹ * y⁻¹ * y := by
      simp [mul_assoc]
    rw [e]
    exact mul_mem (mem_sup_left hc) (mem_sup_right hy)
  have h2 : g ∈ normalizer ((zpowers x : Subgroup G) : Set G) := by
    apply mem_normalizer_of_map_conj_le
    have hgx : g * x * g⁻¹ = x := by
      rw [mem_centralizer_singleton_iff.mp (hPx hg), mul_inv_cancel_right]
    rw [MonoidHom.map_zpowers]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hgx, le_refl]
  exact CFSG.ABGTheoremB.normalizer_inf_normalizer_le_normalizer_sup _ _ ⟨h1, h2⟩

theorem bar_W_le_bar_centralizer_V {WK : Subgroup G} [IsSimpleGroup (bar 𝔨.K₁ WK)]
    (hXWK : ρ.X ≤ WK) :
    bar 𝔨.K₁ WK ≤ bar 𝔨.K₁ (centralizer (𝔨.V : Set G)) := by
  have hCb : bar 𝔨.K₁ (𝔨.K₁ ⊓ centralizer (𝔨.V : Set G)) =
      bar 𝔨.K₁ (centralizer (𝔨.V : Set G)) := bar_inf_left _
  have hCn : (bar 𝔨.K₁ (𝔨.K₁ ⊓ centralizer (𝔨.V : Set G))).Normal := by
    refine bar_normal ((normal_subgroupOf_iff_le_normalizer inf_le_left).mpr ?_)
    intro g hg
    have hgK : g ∈ normalizer (𝔨.V : Set G) := 𝔨.K_eq_normalizer_V ▸ 𝔨.K₁_le_K hg
    exact inf_normalizer_le_normalizer_inf
      ⟨le_normalizer hg, normalizer_le_normalizer_centralizer _ hgK⟩
  rw [← hCb]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ((bar 𝔨.K₁ (𝔨.K₁ ⊓ centralizer (𝔨.V : Set G))).subgroupOf (bar 𝔨.K₁ WK)) with h | h
  · exfalso
    apply bar_ne_bot_of_isKleinFour 𝔨.X_le_K₁ ρ.isKleinFour_X
    rw [eq_bot_iff]
    intro y hy
    have hyJ : y ∈ bar 𝔨.K₁ WK := bar_mono hXWK hy
    have hyC : y ∈ bar 𝔨.K₁ (𝔨.K₁ ⊓ centralizer (𝔨.V : Set G)) :=
      bar_mono (le_inf 𝔨.X_le_K₁ 𝔨.X_le_centralizer_V) hy
    have h1 : (⟨y, hyJ⟩ : bar 𝔨.K₁ WK) ∈
        (bar 𝔨.K₁ (𝔨.K₁ ⊓ centralizer (𝔨.V : Set G))).subgroupOf (bar 𝔨.K₁ WK) := hyC
    rw [h, mem_bot] at h1
    exact mem_bot.mpr (congrArg Subtype.val h1)
  · exact subgroupOf_eq_top.mp h

theorem isMaxInvIn_bar_sup (hPP : 𝔨.P = 𝔨.Pstar) (hXP : 𝔨.P ≤ centralizer (ρ.X : Set G))
    (J : Subgroup (Bar 𝔨.K₁)) :
    IsMaxInvIn p (bar 𝔨.K₁ ρ.X) (J ⊔ bar 𝔨.K₁ 𝔨.P) (bar 𝔨.K₁ 𝔨.P) := by
  have hmax := 𝔨.isMaxInvIn_bar_Pstar
  rw [← hPP] at hmax
  refine ⟨le_sup_right, hmax.2.1,
    (le_centralizer_iff.mp (bar_le_centralizer hXP)).trans (centralizer_le_normalizer _), ?_⟩
  intro F _ hF hXF hPF
  refine hmax.2.2.2 F le_top hF ?_ hPF
  rw [𝔨.bar_A_eq]
  exact sup_le hXF (𝔨.bar_Y_le_center.trans (center_le_normalizer _))

theorem exists_psl {WK Q : Subgroup G} (hWK : WK ≤ 𝔨.K₁ ⊓ ρ.N₀)
    (hWKcov : Covers WK ρ.N₀ (O ρ.N))
    (hK₁WK : 𝔨.K₁ = WK ⊔ 𝔨.Pstar ⊔ ρ.Y ⊔ O 𝔨.K₁) (hWKO : O 𝔨.K₁ ⊓ WK = WK ⊓ O ρ.N)
    (hWKL : IsL2OrA7 (bar 𝔨.K₁ WK) 5 ∨
      (bar 𝔨.K₁ WK = bar 𝔨.K₁ ρ.X ∧ IsKleinFour (bar 𝔨.K₁ WK)))
    (hQUV : ¬ Q ⊓ 𝔨.U ≤ 𝔨.V) (hPP : 𝔨.P = 𝔨.Pstar) (hPU : 𝔨.P = 𝔨.U)
    (h7 : ¬ QuotIs ρ.N₀ (O ρ.N) (fun L _ => Nonempty (L ≃* alternatingGroup (Fin 7)))) :
    ∃ (r k : ℕ) (_ : Fact r.Prime), r ≠ 2 ∧ 5 ≤ r ^ k ∧
      Nonempty (bar 𝔨.K₁ WK ≃* PSL(2, GaloisField r k)) := by
  rcases hWKL with hL | ⟨hWX, -⟩
  · rcases hL with ⟨⟨e7⟩⟩ | ⟨r, k, hr, hr2, hrk, ⟨eP⟩⟩
    · exfalso
      have : ((O ρ.N).subgroupOf ρ.N₀).Normal :=
        (normal_subgroupOf_iff_le_normalizer le_sup_right).mpr ρ.N₀_le_normalizer_O_N
      obtain ⟨eW⟩ := 𝔨.nonempty_bar_W_mulEquiv (QuotientGroup.mk' _)
        (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) hWK hWKcov hWKO
      exact h7 ⟨_, _, QuotientGroup.mk' _, QuotientGroup.mk'_surjective _,
        QuotientGroup.ker_mk' _, ⟨eW.symm.trans e7⟩⟩
    · exact ⟨r, k, hr, hr2, hrk, ⟨eP⟩⟩
  · exfalso
    have hXPs : 𝔨.Pstar ≤ centralizer (ρ.X : Set G) :=
      hPP ▸ hPU.le.trans 𝔨.U_le_centralizer_X
    have hPn : (bar 𝔨.K₁ 𝔨.Pstar).Normal := by
      rw [← normalizer_eq_top_iff, eq_top_iff, ← 𝔨.bar_K₁_eq (hWK.trans inf_le_left) hK₁WK, hWX]
      refine sup_le (sup_le ?_ le_normalizer) (𝔨.bar_Y_le_center.trans (center_le_normalizer _))
      exact (le_centralizer_iff.mp (bar_le_centralizer hXPs)).trans (centralizer_le_normalizer _)
    have hPodd : Odd (Nat.card (bar 𝔨.K₁ 𝔨.Pstar)) :=
      odd_card_bar (CFSG.GH72.odd_card_of_isPGroup 𝔨.hp 𝔨.hp2 (hPP ▸ 𝔨.isPGroup_P))
    have hP1 : bar 𝔨.K₁ 𝔨.Pstar = ⊥ := by
      have h1 := le_oddCore_of_normal_of_odd hPn hPodd
      rw [𝔨.oddCore_bar_K₁] at h1
      exact eq_bot_iff.mpr h1
    exact 𝔨.bar_U_ne_bot hQUV (eq_bot_iff.mpr (hP1 ▸ bar_mono 𝔨.U_le_Pstar))

theorem exists_Tbar
    {r k : ℕ} [Fact r.Prime] (hr2 : r ≠ 2) (hrk : 5 ≤ r ^ k)
    {WK Q : Subgroup G} (hWKK₁ : WK ≤ 𝔨.K₁) (hXWK : ρ.X ≤ WK)
    (hK₁WK : 𝔨.K₁ = WK ⊔ 𝔨.Pstar ⊔ ρ.Y ⊔ O 𝔨.K₁)
    (hWKn : ((WK ⊔ O 𝔨.K₁).subgroupOf 𝔨.K₁).Normal) (e : bar 𝔨.K₁ WK ≃* PSL(2, GaloisField r k))
    (hPP : 𝔨.P = 𝔨.Pstar) (hPU : 𝔨.P = 𝔨.U) (hXP : 𝔨.P ≤ centralizer (ρ.X : Set G))
    (hQUV : ¬ Q ⊓ 𝔨.U ≤ 𝔨.V) :
    ∃ (t : ℕ) (x₁ : G) (hx₁ : x₁ ∈ ρ.X) (Tb : Subgroup (Bar 𝔨.K₁)),
      (t.Prime ∧ t ≠ 2 ∧ t ≠ p) ∧ x₁ ≠ 1 ∧ IsPGroup t Tb ∧ Tb ≤ bar 𝔨.K₁ WK ∧
      bar 𝔨.K₁ A ≤ normalizer (Tb : Set (Bar 𝔨.K₁)) ∧
      bar 𝔨.K₁ 𝔨.P ≤ normalizer (Tb : Set (Bar 𝔨.K₁)) ∧
      (QuotientGroup.mk (⟨x₁, 𝔨.X_le_K₁ hx₁⟩ : 𝔨.K₁) : Bar 𝔨.K₁) ∈
        centralizer (Tb : Set (Bar 𝔨.K₁)) ∧
      ⁅Tb, bar 𝔨.K₁ ρ.X⁆ = Tb ∧
      bar 𝔨.K₁ 𝔨.P ⊓ centralizer (Tb : Set (Bar 𝔨.K₁)) = ⊥ := by
  have hp := 𝔨.hp
  have hp2 := 𝔨.hp2
  have : Fact p.Prime := ⟨hp⟩
  have hJn : (bar 𝔨.K₁ WK).Normal := 𝔨.bar_W_normal hWKK₁ hWKn
  have hXb := 𝔨.isKleinFour_bar_X
  have hXJ : bar 𝔨.K₁ ρ.X ≤ bar 𝔨.K₁ WK := bar_mono hXWK
  have hPJ : bar 𝔨.K₁ 𝔨.P ≤ normalizer (bar 𝔨.K₁ WK : Set (Bar 𝔨.K₁)) := by
    rw [normalizer_eq_top_iff.mpr hJn]
    exact le_top
  have hPXb : bar 𝔨.K₁ 𝔨.P ≤ centralizer (bar 𝔨.K₁ ρ.X : Set (Bar 𝔨.K₁)) :=
    bar_le_centralizer hXP
  have hPb : IsPGroup p (bar 𝔨.K₁ 𝔨.P) := isPGroup_bar_of_isPGroup 𝔨.isPGroup_P
  have hPbodd : Odd (Nat.card (bar 𝔨.K₁ 𝔨.P)) := CFSG.GH72.odd_card_of_isPGroup hp hp2 hPb
  have hmax := 𝔨.isMaxInvIn_bar_sup hPP hXP (bar 𝔨.K₁ WK)
  obtain ⟨x₁, hx₁X, hx₁1⟩ := exists_ne_one_of_isKleinFour ρ.isKleinFour_X
  have hxb : (QuotientGroup.mk (⟨x₁, 𝔨.X_le_K₁ hx₁X⟩ : 𝔨.K₁) : Bar 𝔨.K₁) ∈
      bar 𝔨.K₁ ρ.X := mk_mem_bar _ hx₁X
  have hxb1 : (QuotientGroup.mk (⟨x₁, 𝔨.X_le_K₁ hx₁X⟩ : 𝔨.K₁) : Bar 𝔨.K₁) ≠ 1 := by
    intro h
    have hxO : x₁ ∈ O 𝔨.K₁ := (mk_eq_one_iff _).mp h
    have : x₁ ∈ ρ.X ⊓ O 𝔨.K₁ := ⟨hx₁X, hxO⟩
    rw [inf_eq_bot_of_isKleinFour ρ.isKleinFour_X (card_O_odd _), mem_bot] at this
    exact hx₁1 this
  have hpa :=
    not_dvd_card_inf_centralizer_of_isMaxInvIn hr2 hrk e hXb hXJ hp hp2 hPb hPJ hPXb hmax hxb hxb1
  have hPb1 : bar 𝔨.K₁ 𝔨.P ≠ ⊥ := hPU ▸ 𝔨.bar_U_ne_bot hQUV
  have hJPn : (bar 𝔨.K₁ WK ⊔ bar 𝔨.K₁ 𝔨.P).Normal := hPP ▸ 𝔨.bar_W_sup_Pstar_normal hWKK₁ hK₁WK
  have hZJ : center (bar 𝔨.K₁ WK) = ⊥ :=
    center_eq_bot_of_isL2OrA7 (Or.inr ⟨r, k, inferInstance, hr2, hrk, ⟨e⟩⟩ : IsL2OrA7 _ 5)
  have hfaith := sup_inf_centralizer_eq_bot hJn hJPn hZJ hPJ hPbodd 𝔨.oddCore_bar_K₁
  obtain ⟨t, Tb, ht, ht2, htp, hTsyl, -, hTN, hTP⟩ :=
    exists_isSylowOf_inf_centralizer_eq_bot hr2 hrk e hXb hXJ hp hp2 hPb hPb1 hPJ hPXb hfaith hxb
      hxb1 hpa
  have hTbJ : Tb ≤ bar 𝔨.K₁ WK := hTsyl.le.trans inf_le_left
  have hTbx := hTsyl.le.trans
    (inf_le_right : bar 𝔨.K₁ WK ⊓ centralizer ({(QuotientGroup.mk
      (⟨x₁, 𝔨.X_le_K₁ hx₁X⟩ : 𝔨.K₁) : Bar 𝔨.K₁)} : Set (Bar 𝔨.K₁)) ≤ _)
  have hTbp : IsPGroup t Tb := hTsyl.isPGroup
  have hXTb : bar 𝔨.K₁ ρ.X ≤ normalizer (Tb : Set (Bar 𝔨.K₁)) := by
    refine le_trans (le_inf (hXJ.trans le_normalizer) ?_) hTN
    intro y hy
    exact mem_centralizer_singleton_iff.mpr (mul_comm_of_mem_kleinFour hXb hy hxb)
  have hATb : bar 𝔨.K₁ A ≤ normalizer (Tb : Set (Bar 𝔨.K₁)) := by
    rw [𝔨.bar_A_eq]
    exact sup_le hXTb (𝔨.bar_Y_le_center.trans (center_le_normalizer _))
  have hPTb : bar 𝔨.K₁ 𝔨.P ≤ normalizer (Tb : Set (Bar 𝔨.K₁)) := by
    refine le_trans (le_inf hPJ ?_) hTN
    intro g hg
    exact mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (hPXb hg)) _ hxb).symm
  have hxTb : (QuotientGroup.mk (⟨x₁, 𝔨.X_le_K₁ hx₁X⟩ : 𝔨.K₁) : Bar 𝔨.K₁) ∈
      centralizer (Tb : Set (Bar 𝔨.K₁)) := by
    rw [mem_centralizer_iff]
    intro τ hτ
    exact mem_centralizer_singleton_iff.mp (hTbx hτ)
  have hTbC : Tb ⊓ centralizer (bar 𝔨.K₁ ρ.X : Set (Bar 𝔨.K₁)) = ⊥ := by
    have h1 := inf_eq_bot_of_odd_of_le_centralizer_kleinFour hr2 hrk e hXb hXJ
      (U := Tb ⊓ centralizer (bar 𝔨.K₁ ρ.X : Set (Bar 𝔨.K₁)))
      ((CFSG.GH72.odd_card_of_isPGroup ht ht2 hTbp).of_dvd_nat (card_dvd_of_le inf_le_left))
      inf_le_right
    rwa [inf_eq_left.mpr (inf_le_left.trans hTbJ)] at h1
  have hTbX : ⁅Tb, bar 𝔨.K₁ ρ.X⁆ = Tb := by
    refine le_antisymm ?_ ?_
    · rw [commutator_comm]
      exact le_normalizer_iff_commutator_le_right.mp hXTb
    · have h1 := le_commutator_sup_inf_centralizer_of_coprime_pGroup ht ht2 hTbp
        𝔨.isPGroup_two_bar_X hXTb
      rwa [hTbC, sup_bot_eq] at h1
  exact ⟨t, x₁, hx₁X, Tb, ⟨ht, ht2, htp⟩, hx₁1, hTbp, hTbJ, hATb, hPTb, hxTb, hTbX, hTP⟩

theorem exists_Tstar_of_Tbar {t : ℕ} (ht : t.Prime ∧ t ≠ 2 ∧ t ≠ p) {x₁ : G}
    (hx₁ : x₁ ∈ ρ.X) {WK : Subgroup G} {Tb : Subgroup (Bar 𝔨.K₁)} (hTbp : IsPGroup t Tb)
    (hTbJ : Tb ≤ bar 𝔨.K₁ WK) (hATb : bar 𝔨.K₁ A ≤ normalizer (Tb : Set (Bar 𝔨.K₁)))
    (hPTb : bar 𝔨.K₁ 𝔨.P ≤ normalizer (Tb : Set (Bar 𝔨.K₁)))
    (hxTb : (QuotientGroup.mk (⟨x₁, 𝔨.X_le_K₁ hx₁⟩ : 𝔨.K₁) : Bar 𝔨.K₁) ∈
      centralizer (Tb : Set (Bar 𝔨.K₁)))
    (hTbX : ⁅Tb, bar 𝔨.K₁ ρ.X⁆ = Tb)
    (hPTbC : bar 𝔨.K₁ 𝔨.P ⊓ centralizer (Tb : Set (Bar 𝔨.K₁)) = ⊥)
    (hcovJ : bar 𝔨.K₁ WK ≤ bar 𝔨.K₁ (centralizer (𝔨.V : Set G)))
    (hPP : 𝔨.P = 𝔨.Pstar) (hXP : 𝔨.P ≤ centralizer (ρ.X : Set G)) :
    ∃ Ts : Subgroup G, IsPGroup t Ts ∧ A ≤ normalizer (Ts : Set G) ∧
      Ts ≤ centralizer ((𝔨.V ⊔ ρ.Y ⊔ zpowers x₁ : Subgroup G) : Set G) ∧
      ⁅Ts, ρ.X⁆ = Ts ∧ 𝔨.P ⊓ centralizer (Ts : Set G) = 𝔨.V ∧
      𝔨.P ≤ normalizer (Ts : Set G) := by
  obtain ⟨htp', ht2, htp⟩ := ht
  have hp := 𝔨.hp
  have : Fact t.Prime := ⟨htp'⟩
  have : Fact p.Prime := ⟨hp⟩
  have hPK : 𝔨.P ≤ 𝔨.K := hPP.le.trans inf_le_right
  have hPK₁ : 𝔨.P ≤ 𝔨.K₁ := hPP.le.trans 𝔨.Pstar_le_K₁
  have hx₁K₁ : x₁ ∈ 𝔨.K₁ := 𝔨.X_le_K₁ hx₁
  have hPx₁ : 𝔨.P ≤ C x₁ := fun g hg =>
    mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (hXP hg)) x₁ hx₁).symm
  have hPodd : Odd (Nat.card 𝔨.P) := CFSG.GH72.odd_card_of_isPGroup hp 𝔨.hp2 𝔨.isPGroup_P
  set Tpre : Subgroup G := (Tb.comap (QuotientGroup.mk' (CFSG.oddCore 𝔨.K₁))).map 𝔨.K₁.subtype
    with hTpredef
  have hTpreK₁ : Tpre ≤ 𝔨.K₁ := map_subtype_le _
  have hTpreodd : Odd (Nat.card Tpre) :=
    odd_card_comap_map Tb (CFSG.GH72.odd_card_of_isPGroup htp' ht2 hTbp)
  have hbarTpre : bar 𝔨.K₁ Tpre = Tb := bar_comap_map Tb
  have hATpre : A ≤ normalizer (Tpre : Set G) := le_normalizer_comap_map Tb 𝔨.A_le_K₁ hATb
  have hPTpre : 𝔨.P ≤ normalizer (Tpre : Set G) := le_normalizer_comap_map Tb hPK₁ hPTb
  set B₀ : Subgroup G := centralizer (𝔨.V : Set G) ⊓ Tpre with hB₀def
  have hB₀K₁ : B₀ ≤ 𝔨.K₁ := inf_le_right.trans hTpreK₁
  have hB₀odd : Odd (Nat.card B₀) := hTpreodd.of_dvd_nat (card_dvd_of_le inf_le_right)
  have hAB₀ : A ≤ normalizer (B₀ : Set G) := fun a ha => inf_normalizer_le_normalizer_inf
    ⟨normalizer_le_normalizer_centralizer _ (𝔨.A_le_normalizer_V ha), hATpre ha⟩
  have hbarB₀ : bar 𝔨.K₁ B₀ = Tb := by
    refine le_antisymm ((bar_mono inf_le_right).trans hbarTpre.le) ?_
    intro τ hτ
    obtain ⟨⟨c, hcK₁⟩, hc, hcτ⟩ := mem_bar_iff.mp (hcovJ (hTbJ hτ))
    have hcT : c ∈ Tpre := mem_comap_map_of_mk_mem Tb hcK₁ (by rw [hcτ]; exact hτ)
    rw [← hcτ]
    exact mk_mem_bar hcK₁ ⟨hc, hcT⟩
  obtain ⟨S, hS, hAS⟩ :=
    CFSG.ABGTheoremB.exists_isSylowOf_normalized_of_odd htp' ρ.isPGroup_A hAB₀ hB₀odd
  have hSK₁ : S ≤ 𝔨.K₁ := hS.le.trans hB₀K₁
  have hbarS : bar 𝔨.K₁ S = Tb := by
    have h1 := isSylowOf_bar_of_isSylowOf hS hB₀K₁
    rw [hbarB₀] at h1
    exact (h1.eq_of_le h1.le le_rfl hTbp).symm
  set Z : Subgroup G := ρ.Y ⊔ zpowers x₁ with hZdef
  have hZA : Z ≤ A := sup_le ρ.Y_le_A (zpowers_le.mpr (ρ.X_le_A hx₁))
  have hZK₁ : Z ≤ 𝔨.K₁ := hZA.trans 𝔨.A_le_K₁
  have hbarZ : bar 𝔨.K₁ Z ≤ centralizer (Tb : Set (Bar 𝔨.K₁)) := by
    rw [hZdef, bar_sup 𝔨.Y_le_K₁ (zpowers_le.mpr hx₁K₁)]
    exact sup_le (𝔨.bar_Y_le_center.trans (center_le_centralizer _))
      ((bar_zpowers_le hx₁K₁).trans (zpowers_le.mpr hxTb))
  set T₁ : Subgroup G := S ⊓ centralizer (Z : Set G) with hT₁def
  have hbarT₁ : bar 𝔨.K₁ T₁ = Tb := by
    refine le_antisymm ((bar_mono inf_le_left).trans hbarS.le) ?_
    have h1 := le_commutator_sup_inf_centralizer_of_coprime_pGroup htp' ht2 hS.isPGroup
      (ρ.isPGroup_A.to_le hZA) (hZA.trans hAS)
    have h2 : bar 𝔨.K₁ ⁅S, Z⁆ = ⊥ := by
      rw [bar_commutator hSK₁ hZK₁, hbarS, commutator_eq_bot_iff_le_centralizer]
      exact le_centralizer_iff.mpr hbarZ
    have h3 := bar_mono (H := 𝔨.K₁) h1
    rw [bar_sup ((commutator_mono hSK₁ hZK₁).trans (commutator_le_self _))
      (inf_le_left.trans hSK₁), h2, bot_sup_eq, hbarS] at h3
    exact h3
  set D : Subgroup G := centralizer ((𝔨.V ⊔ ρ.Y ⊔ zpowers x₁ : Subgroup G) : Set G)
    with hDdef
  set B₂ : Subgroup G := D ⊓ Tpre with hB₂def
  have hB₂K₁ : B₂ ≤ 𝔨.K₁ := inf_le_right.trans hTpreK₁
  have hB₂odd : Odd (Nat.card B₂) := hTpreodd.of_dvd_nat (card_dvd_of_le inf_le_right)
  have hT₁B₂ : T₁ ≤ B₂ := by
    refine le_inf ?_ (inf_le_left.trans (hS.le.trans inf_le_right))
    rw [hDdef, le_centralizer_iff]
    have hV : 𝔨.V ≤ centralizer (T₁ : Set G) :=
      le_centralizer_iff.mp (inf_le_left.trans (hS.le.trans inf_le_left))
    have hZ : Z ≤ centralizer (T₁ : Set G) := le_centralizer_iff.mp inf_le_right
    exact sup_le (sup_le hV (le_sup_left.trans hZ)) (le_sup_right.trans hZ)
  have hbarB₂ : bar 𝔨.K₁ B₂ = Tb :=
    le_antisymm ((bar_mono inf_le_right).trans hbarTpre.le) (hbarT₁.ge.trans (bar_mono hT₁B₂))
  have hAB₂ : A ≤ normalizer (B₂ : Set G) := fun a ha => inf_normalizer_le_normalizer_inf
    ⟨normalizer_le_normalizer_centralizer _ (𝔨.A_le_normalizer_V_sup hx₁ ha), hATpre ha⟩
  have hPB₂ : 𝔨.P ≤ normalizer (B₂ : Set G) := fun g hg => inf_normalizer_le_normalizer_inf
    ⟨normalizer_le_normalizer_centralizer _ (𝔨.P_le_normalizer_V_sup hPP hPx₁ hg), hPTpre hg⟩
  have hLodd : Odd (Nat.card (B₂ ⊔ 𝔨.P : Subgroup G)) :=
    CFSG.ABGTheoremB.odd_card_sup_of_le_normalizer_of_odd hPB₂ hB₂odd hPodd
  have hAL : A ≤ normalizer ((B₂ ⊔ 𝔨.P : Subgroup G) : Set G) :=
    (le_inf hAB₂ 𝔨.A_le_normalizer_P).trans
      (CFSG.ABGTheoremB.normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hPL : IsSylowOf p 𝔨.P (B₂ ⊔ 𝔨.P) := 𝔨.isSylowOf_P_of_odd le_sup_right hAL hLodd
  have hbot : ∀ L : Subgroup G, L ≤ normalizer ((⊥ : Subgroup G) : Set G) := fun L =>
    le_top.trans (normalizer_eq_top_iff.mpr (inferInstance : (⊥ : Subgroup G).Normal)).ge
  obtain ⟨T', K', hT'L, -, hAT', hT'P, -, -, -, -⟩ := exists_isSylowOf_mul_comm hp htp' htp
    ρ.isPGroup_A hAL hLodd hPL 𝔨.A_le_normalizer_P IsPGroup.of_bot bot_le (hbot _) (hbot _)
  have hT'B₂ : T' ≤ B₂ :=
    le_of_isPGroup_of_le_sup hp htp' htp 𝔨.isPGroup_P hPB₂ hT'L.isPGroup hT'L.le
  have hT'K₁ : T' ≤ 𝔨.K₁ := hT'B₂.trans hB₂K₁
  have hbarT' : bar 𝔨.K₁ T' = Tb := by
    have h1 := isSylowOf_bar_of_isSylowOf (hT'L.of_le hT'B₂ le_sup_left) hB₂K₁
    rw [hbarB₂] at h1
    exact (h1.eq_of_le h1.le le_rfl hTbp).symm
  have hPX : 𝔨.P ≤ normalizer (ρ.X : Set G) := hXP.trans (centralizer_le_normalizer _)
  set 𝒯 : Set (Subgroup G) := {R | R ≤ B₂ ∧ IsPGroup t R ∧ A ≤ normalizer (R : Set G) ∧
    𝔨.P ≤ normalizer (R : Set G) ∧ bar 𝔨.K₁ R = Tb} with h𝒯def
  have hT₀ : ⁅T', ρ.X⁆ ∈ 𝒯 := by
    have hle : ⁅T', ρ.X⁆ ≤ T' := by
      rw [commutator_comm]
      exact le_normalizer_iff_commutator_le_right.mp (ρ.X_le_A.trans hAT')
    refine ⟨hle.trans hT'B₂, hT'L.isPGroup.to_le hle,
      le_normalizer_commutator hAT' (ρ.A_le_normalizer_of_le ρ.X_le_A),
      G5d.le_normalizer_commutator_of_mul_comm hXP hT'P, ?_⟩
    rw [bar_commutator hT'K₁ 𝔨.X_le_K₁, hbarT', hTbX]
  obtain ⟨Ts, hTs⟩ := Set.Finite.exists_minimalFor id 𝒯 (Set.toFinite _) ⟨_, hT₀⟩
  obtain ⟨⟨hTsB₂, hTsp, hATs, hPTs, hbarTs⟩, hmin⟩ := hTs
  have hTsK₁ : Ts ≤ 𝔨.K₁ := hTsB₂.trans hB₂K₁
  have hTsX : ⁅Ts, ρ.X⁆ = Ts := by
    have hle : ⁅Ts, ρ.X⁆ ≤ Ts := by
      rw [commutator_comm]
      exact le_normalizer_iff_commutator_le_right.mp (ρ.X_le_A.trans hATs)
    have hmem : ⁅Ts, ρ.X⁆ ∈ 𝒯 := ⟨hle.trans hTsB₂, hTsp.to_le hle,
      le_normalizer_commutator hATs (ρ.A_le_normalizer_of_le ρ.X_le_A),
      le_normalizer_commutator hPTs hPX, by rw [bar_commutator hTsK₁ 𝔨.X_le_K₁, hbarTs, hTbX]⟩
    exact le_antisymm hle (hmin hmem hle)
  have hTsD : Ts ≤ D := hTsB₂.trans inf_le_left
  refine ⟨Ts, hTsp, hATs, hTsD, hTsX, ?_, hPTs⟩
  apply le_antisymm
  · rintro g ⟨hgP, hgC⟩
    have hgK₁ : g ∈ 𝔨.K₁ := hPK₁ hgP
    have hmk : (QuotientGroup.mk (⟨g, hgK₁⟩ : 𝔨.K₁) : Bar 𝔨.K₁) ∈
        bar 𝔨.K₁ 𝔨.P ⊓ centralizer (Tb : Set (Bar 𝔨.K₁)) := by
      refine ⟨mk_mem_bar hgK₁ hgP, ?_⟩
      rw [← hbarTs]
      exact bar_le_centralizer (P := Ts) (Q := 𝔨.P ⊓ centralizer (Ts : Set G)) inf_le_right
        (mk_mem_bar hgK₁ ⟨hgP, hgC⟩)
    rw [hPTbC, mem_bot, mk_eq_one_iff] at hmk
    rw [← 𝔨.V_eq]
    exact ⟨⟨hgP, hPK hgP⟩, hmk⟩
  · refine le_inf (inf_le_left.trans inf_le_left) (le_centralizer_iff.mp
      (hTsD.trans (centralizer_le fun v hv => ?_)))
    exact (le_sup_left.trans le_sup_left : 𝔨.V ≤ 𝔨.V ⊔ ρ.Y ⊔ zpowers x₁) hv

end Sec5KConfig

namespace Sec5ConfigR

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {ρ : Sec5Roles G A} {p : ℕ}
  (𝔠 : Sec5ConfigR ρ p)

theorem isSylowOf_Q_O_C {x₁ : G} (hx₁ : x₁ ∈ ρ.X) (hx₁1 : x₁ ≠ 1)
    (hXP : 𝔠.P ≤ centralizer (ρ.X : Set G)) (hQ1 : 𝔠.Q ≠ ⊥)
    (h413 : ∀ H : Subgroup G, H ≠ ⊤ →
      (Covers H ρ.M₀ (O ρ.M) → ∀ x ∈ ρ.X, x ≠ 1 → x ∈ H → O H ⊓ C x ≤ O (C x)) ∧
      (Covers H ρ.N₀ (O ρ.N) → ∀ y ∈ ρ.Y, y ≠ 1 → y ∈ H → O H ⊓ C y ≤ O (C y))) :
    IsSylowOf p 𝔠.Q (O (C x₁)) := by
  have hPC : 𝔠.P ≤ C x₁ := fun g hg =>
    mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (hXP hg)) x₁ hx₁).symm
  have hx₁H₁ : x₁ ∈ 𝔠.H₀ ⊓ normalizer (𝔠.Q : Set G) := 𝔠.A_le_H₁ (ρ.X_le_A hx₁)
  have hH₁top : 𝔠.H₀ ⊓ normalizer (𝔠.Q : Set G) ≠ ⊤ := by
    intro h
    apply 𝔠.hno
    have hNQ : normalizer (𝔠.Q : Set G) = ⊤ := eq_top_iff.mpr (h.ge.trans inf_le_right)
    exact ⟨⊤, ⟨⟨𝔠.Q, hQ1, 𝔠.isPGroup_P.to_le 𝔠.Q_le_P, hNQ.symm⟩, le_top, 𝔠.P, 𝔠.hP, le_top⟩,
      fun m hm => mem_sup_left ⟨mem_top m, hm⟩, fun m hm => mem_sup_left ⟨mem_top m, hm⟩⟩
  have hQH₁ : 𝔠.Q ≤ O (𝔠.H₀ ⊓ normalizer (𝔠.Q : Set G)) :=
    G5d.le_O_of_le_normalizer (le_inf (𝔠.Q_le_P.trans 𝔠.P_le_H₀) le_normalizer) inf_le_right
      (CFSG.GH72.odd_card_of_isPGroup 𝔠.hp 𝔠.hp2 (𝔠.isPGroup_P.to_le 𝔠.Q_le_P))
  have hQO : 𝔠.Q ≤ O (C x₁) := fun q hq =>
    (h413 _ hH₁top).1 𝔠.covers_H₁ x₁ hx₁ hx₁1 hx₁H₁ ⟨hQH₁ hq, hPC (𝔠.Q_le_P hq)⟩
  have hAC : A ≤ normalizer (C x₁ : Set G) := fun a ha => le_normalizer
    (mem_centralizer_singleton_iff.mpr (ρ.comm (ρ.X_le_A hx₁) ha).symm)
  have hR := isSylowOf_inf_O_of_isMaxInvIn 𝔠.hp ρ.isPGroup_A hAC (𝔠.hP.of_le hPC le_top)
  have hOC : O (C x₁) ⊓ (𝔠.H₀ ⊓ normalizer (𝔠.Q : Set G)) ≤
      O (𝔠.H₀ ⊓ normalizer (𝔠.Q : Set G)) :=
    O_C_inf_le_O hx₁H₁ (ρ.mul_self_of_mem_A (ρ.X_le_A hx₁))
      (fun h hh => 𝔠.commutator_H₁_X_le (commutator_mem_commutator hh hx₁))
  have hQeq : 𝔠.P ⊓ O (C x₁) = 𝔠.Q := by
    refine le_antisymm ?_ (le_inf 𝔠.Q_le_P hQO)
    rintro g ⟨hgP, hgO⟩
    exact ⟨hgP, 𝔠.O_H₁_le_O_H₀ (hOC ⟨hgO, 𝔠.P_le_H₁ hgP⟩)⟩
  rwa [hQeq] at hR

theorem exists_T {t : ℕ} (ht : t.Prime ∧ t ≠ 2 ∧ t ≠ p) {x₁ : G} (hx₁ : x₁ ∈ ρ.X)
    (hx₁1 : x₁ ≠ 1) {Ts : Subgroup G} (hTsp : IsPGroup t Ts)
    (hATs : A ≤ normalizer (Ts : Set G)) (hTsC : Ts ≤ C x₁) (hTsX : ⁅Ts, ρ.X⁆ = Ts)
    (hPTs : 𝔠.P ≤ normalizer (Ts : Set G)) (hXP : 𝔠.P ≤ centralizer (ρ.X : Set G))
    (hQ1 : 𝔠.Q ≠ ⊥)
    (h411 : (∀ x ∈ ρ.X, x ≠ 1 → ∀ D : Subgroup G, D ≤ C x → Odd (Nat.card D) →
        A ≤ normalizer (D : Set G) → ⁅D, ρ.X⁆ ⊔ ⁅⁅D, ρ.Y⁆, ⁅D, ρ.Y⁆⁆ ≤ O (C x)) ∧
      (∀ y ∈ ρ.Y, y ≠ 1 → ∀ D : Subgroup G, D ≤ C y → Odd (Nat.card D) →
        A ≤ normalizer (D : Set G) → ⁅D, ρ.Y⁆ ⊔ ⁅⁅D, ρ.X⁆, ⁅D, ρ.X⁆⁆ ≤ O (C y)))
    (h413 : ∀ H : Subgroup G, H ≠ ⊤ →
      (Covers H ρ.M₀ (O ρ.M) → ∀ x ∈ ρ.X, x ≠ 1 → x ∈ H → O H ⊓ C x ≤ O (C x)) ∧
      (Covers H ρ.N₀ (O ρ.N) → ∀ y ∈ ρ.Y, y ≠ 1 → y ∈ H → O H ⊓ C y ≤ O (C y))) :
    ∃ T : Subgroup G, (Ts ≤ T ∧ IsSylowOf t T (O (C x₁)) ∧ A ≤ normalizer (T : Set G) ∧
      ((T : Set G) * (𝔠.Q : Set G) = (𝔠.Q : Set G) * (T : Set G)) ∧
      ((T : Set G) * (𝔠.P : Set G) = (𝔠.P : Set G) * (T : Set G))) ∧
      IsSylowOf p 𝔠.Q (O (C x₁)) := by
  obtain ⟨htp', ht2, htp⟩ := ht
  have hp := 𝔠.hp
  have : Fact t.Prime := ⟨htp'⟩
  have : Fact p.Prime := ⟨hp⟩
  have hPC : 𝔠.P ≤ C x₁ := fun g hg =>
    mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (hXP hg)) x₁ hx₁).symm
  have hAC : A ≤ C x₁ := fun a ha =>
    mem_centralizer_singleton_iff.mpr (ρ.comm (ρ.X_le_A hx₁) ha).symm
  have hTsO : Ts ≤ O (C x₁) := by
    have h := h411.1 x₁ hx₁ hx₁1 Ts hTsC (CFSG.GH72.odd_card_of_isPGroup htp' ht2 hTsp) hATs
    rw [hTsX] at h
    exact le_sup_left.trans h
  have hQ := 𝔠.isSylowOf_Q_O_C hx₁ hx₁1 hXP hQ1 h413
  have hPO : 𝔠.P ≤ normalizer (O (C x₁) : Set G) := hPC.trans (le_normalizer_O _)
  have hLodd : Odd (Nat.card (O (C x₁) ⊔ 𝔠.P : Subgroup G)) :=
    CFSG.ABGTheoremB.odd_card_sup_of_le_normalizer_of_odd hPO (card_O_odd _)
      (CFSG.GH72.odd_card_of_isPGroup hp 𝔠.hp2 𝔠.isPGroup_P)
  have hAL : A ≤ normalizer ((O (C x₁) ⊔ 𝔠.P : Subgroup G) : Set G) :=
    (le_inf (hAC.trans (le_normalizer_O _)) 𝔠.A_le_normalizer_P).trans
      (CFSG.ABGTheoremB.normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hPL := 𝔠.isSylowOf_P_of_odd le_sup_right hAL hLodd
  obtain ⟨T, K, hTL, hTsT, hAT, hTP, hTK, hPK, -, hKprimes⟩ := exists_isSylowOf_mul_comm hp htp'
    htp ρ.isPGroup_A hAL hLodd hPL 𝔠.A_le_normalizer_P hTsp (hTsO.trans le_sup_left) hPTs
    hATs
  have hTO : T ≤ O (C x₁) :=
    le_of_isPGroup_of_le_sup hp htp' htp 𝔠.isPGroup_P hPO hTL.isPGroup hTL.le
  have hTO' : IsSylowOf t T (O (C x₁)) := hTL.of_le hTO le_sup_left
  have hTQ : (T : Set G) * (𝔠.Q : Set G) = (𝔠.Q : Set G) * (T : Set G) := by
    have hTK' : IsSylowOf t T (K ⊓ O (C x₁)) := hTO'.of_le (le_inf hTK hTO) inf_le_right
    have hQK : IsSylowOf p 𝔠.Q (K ⊓ O (C x₁)) :=
      hQ.of_le (le_inf (𝔠.Q_le_P.trans hPK) hQ.le) inf_le_right
    obtain ⟨h1, h2⟩ := CFSG.ABGTheoremB.V4.coe_eq_mul_of_isSylowOf htp hTK' hQK
      (fun d hd hdK => hKprimes d hd (hdK.trans (card_dvd_of_le inf_le_left)))
    exact h1.symm.trans h2
  exact ⟨T, ⟨hTsT, hTO', hAT, hTQ, hTP⟩, hQ⟩

theorem exists_sec5ConfigT_of
    (h58 : 𝔠.R = 𝔠.U)
    (h48 : QuotIs ρ.N₀ (O ρ.N) (fun L _ => IsL2OrA7 L 5 ∨ IsKleinFour L) ∧
      CFSG.ABGLocalTools.IsSylowOf 2 ρ.S₁ ρ.N₀ ∧
      ρ.N = ρ.N₀ ⊔ (ρ.N ⊓ normalizer (A : Set G)) ∧
      ρ.N = ρ.N₀ ⊔ (ρ.N ⊓ normalizer (ρ.S₁ : Set G)) ∧
      (∀ y ∈ ρ.Y, y ≠ 1 → O2 (C y) = (O2 ρ.N ⊓ O2 (C y)) ⊔ O (C y)) ∧
      (∀ y ∈ ρ.Y, y ≠ 1 → ⁅O2 (C y), O2 (C y)⁆ ⊔ O (C y) =
        (ρ.N₀ ⊓ ⁅O2 (C y), O2 (C y)⁆) ⊔ O (C y)))
    (h57 : ∀ y ∈ ρ.Y, y ≠ 1 → ¬ 𝔠.V ≤ C y)
    (h59 : ∃ W : Subgroup G, 𝔠.Q = (𝔠.R ⊓ 𝔠.Q) ⊔ W ∧ IsCyclic W ∧
      A ≤ normalizer (W : Set G) ∧ W ≤ 𝔠.K₁ ⊓ centralizer (𝔠.V : Set G) ∧ ⁅ρ.X, W⁆ = W)
    (h59E : ∃ E : Subgroup G, E ≤ 𝔠.R ⊓ 𝔠.Q ∧ CFSG.Open.IsElemAbelian p E ∧ Nat.card E = p ^ 3)
    (h59cyc : IsCyclic (⁅𝔠.Pstar, ρ.X⁆ : Subgroup G))
    (h315 : (∃ H₁ : Subgroup (Bar (C ρ.z₁)), bar (C ρ.z₁) ρ.S₁ ⊓ H₁ = ⊥ ∧
        bar (C ρ.z₁) ρ.S₁ ⊔ H₁ = ⊤ ∧
        H₁ ≤ centralizer (bar (C ρ.z₁) ρ.S₁ : Set (Bar (C ρ.z₁))) ∧
        bar (C ρ.z₁) ρ.S₂ ≤ ⁅H₁, H₁⁆ ∧
        (IsL2OrA7 (⁅H₁, H₁⁆ : Subgroup (Bar (C ρ.z₁))) 5 ∨ ⁅H₁, H₁⁆ = bar (C ρ.z₁) ρ.S₂)) ∧
      (∃ K₁ : Subgroup (Bar (C ρ.z₂)), bar (C ρ.z₂) ρ.S₂ ⊓ K₁ = ⊥ ∧
        bar (C ρ.z₂) ρ.S₂ ⊔ K₁ = ⊤ ∧
        K₁ ≤ centralizer (bar (C ρ.z₂) ρ.S₂ : Set (Bar (C ρ.z₂))) ∧
        bar (C ρ.z₂) ρ.S₁ ≤ ⁅K₁, K₁⁆ ∧
        (IsL2OrA7 (⁅K₁, K₁⁆ : Subgroup (Bar (C ρ.z₂))) 5 ∨ ⁅K₁, K₁⁆ = bar (C ρ.z₂) ρ.S₁)))
    (h411 : (∀ x ∈ ρ.X, x ≠ 1 → ∀ D : Subgroup G, D ≤ C x → Odd (Nat.card D) →
        A ≤ normalizer (D : Set G) → ⁅D, ρ.X⁆ ⊔ ⁅⁅D, ρ.Y⁆, ⁅D, ρ.Y⁆⁆ ≤ O (C x)) ∧
      (∀ y ∈ ρ.Y, y ≠ 1 → ∀ D : Subgroup G, D ≤ C y → Odd (Nat.card D) →
        A ≤ normalizer (D : Set G) → ⁅D, ρ.Y⁆ ⊔ ⁅⁅D, ρ.X⁆, ⁅D, ρ.X⁆⁆ ≤ O (C y)))
    (h413 : ∀ H : Subgroup G, H ≠ ⊤ →
      (Covers H ρ.M₀ (O ρ.M) → ∀ x ∈ ρ.X, x ≠ 1 → x ∈ H → O H ⊓ C x ≤ O (C x)) ∧
      (Covers H ρ.N₀ (O ρ.N) → ∀ y ∈ ρ.Y, y ≠ 1 → y ∈ H → O H ⊓ C y ≤ O (C y))) :
    Nonempty (Sec5ConfigTR 𝔠) := by
  obtain ⟨W, hW⟩ := h59
  have hQUV : ¬ 𝔠.Q ⊓ 𝔠.U ≤ 𝔠.V := fun h =>
    𝔠.hno (𝔠.lemma_5_12_of h58 h59E h59cyc W hW (Or.inl h))
  have hW1 : W = ⊥ := by
    by_contra h
    exact 𝔠.hno (𝔠.lemma_5_12_of h58 h59E h59cyc W hW (Or.inr h))
  have h7 : ¬ QuotIs ρ.N₀ (O ρ.N)
      (fun L _ => Nonempty (L ≃* alternatingGroup (Fin 7))) := fun h =>
    𝔠.hno (𝔠.lemma_5_13_of h58 h48 h57 ⟨W, hW⟩ h59E h59cyc h315 h)
  obtain ⟨hPP, hPUW⟩ := 𝔠.lemma_5_11_of h58 W hW
  have hPU : 𝔠.P = 𝔠.U := by rw [hPUW, hW1, sup_bot_eq]
  have hXP : 𝔠.P ≤ centralizer (ρ.X : Set G) := hPU.le.trans 𝔠.U_le_centralizer_X
  have hQ1 : 𝔠.Q ≠ ⊥ := fun h => hQUV (by rw [h, bot_inf_eq]; exact bot_le)
  obtain ⟨WK, hWK, hXWK, hWKcov, hK₁WK, hWKn, hWKO, hWKL⟩ := 𝔠.exists_W
  have hWKK₁ : WK ≤ 𝔠.K₁ := hWK.trans inf_le_left
  obtain ⟨r, k, hr, hr2, hrk, ⟨e⟩⟩ :=
    𝔠.exists_psl hWK hWKcov hK₁WK hWKO hWKL hQUV hPP hPU h7
  have : IsSimpleGroup (bar 𝔠.K₁ WK) :=
    isSimpleGroup_of_isL2OrA7 le_rfl (Or.inr ⟨r, k, hr, hr2, hrk, ⟨e⟩⟩ : IsL2OrA7 _ 5)
  obtain ⟨t, x₁, hx₁, Tb, ht, hx₁1, hTbp, hTbJ, hATb, hPTb, hxTb, hTbX, hPTbC⟩ :=
    𝔠.exists_Tbar hr2 hrk hWKK₁ hXWK hK₁WK hWKn e hPP hPU hXP hQUV
  obtain ⟨Ts, hTsp, hATs, hTsD, hTsX, hTsC, hPTs⟩ :=
    𝔠.exists_Tstar_of_Tbar ht hx₁ hTbp hTbJ hATb hPTb hxTb hTbX hPTbC
      (𝔠.bar_W_le_bar_centralizer_V hXWK) hPP hXP
  have hTsx₁ : Ts ≤ C x₁ := hTsD.trans (centralizer_le (Set.singleton_subset_iff.mpr
    (mem_sup_right (mem_zpowers x₁))))
  have hPx₁ : 𝔠.P ≤ C x₁ := fun g hg =>
    mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (hXP hg)) x₁ hx₁).symm
  obtain ⟨T, hT, hQ⟩ :=
    𝔠.exists_T ht hx₁ hx₁1 hTsp hATs hTsx₁ hTsX hPTs hXP hQ1 h411 h413
  exact ⟨⟨t, ht, x₁, ⟨hx₁, hx₁1, hPx₁⟩, Ts, ⟨hTsp, hATs, hTsD, hTsX, hTsC⟩, T, hT, hXP, hQ⟩⟩

end Sec5ConfigR

end CFSG.GH72
