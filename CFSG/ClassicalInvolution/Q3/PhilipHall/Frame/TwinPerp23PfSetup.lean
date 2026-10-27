module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23Defs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf5Std
public import CFSG.ClassicalInvolution.Q3.Q3T7P24H01
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S7F0

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL


section Frame

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {W : Subgroup G}

theorem exists_swap_equiv (hP : Q3CL.PartIHypG Ω) (hW : W ∈ WSet Ω) {K K' : Subgroup G} {z : G}
    (hK : K ∈ Ω) (htrans : ∀ J ∈ Ω, ∃ g : G, conjSub g K = J) (hz : IsUniqueInvolution K z)
    (hK' : K' ∈ twinSet Ω K) (hne : K' ≠ K) (hperp : KPerp Ω K = {K, K'})
    (hS4 : MuIsoS4 Ω W) :
    ∃ e : ↥(muGroup Ω W) ≃* Equiv.Perm (Fin 4),
      ∀ x, x ∈ Thompson.muDelta Ω W ↔ (e x).IsSwap := by
  obtain ⟨⟨d₀, hd₀⟩, hcl⟩ := Q3T7.c231_clique hP hK htrans hz hK' hne hperp hW
  have hTT : Star3T.IsTT (Thompson.muDelta Ω W) := Q3T6.Mu.isTT_muDelta hP hW
  have hS : Star3T.IsStar (Thompson.muDelta Ω W) :=
    Q3T6.Mu.isStar_muDelta (Q3CL.T8.ctxOf hP hW)
  by_cases hconn : ∀ d ∈ Thompson.muDelta Ω W, ∀ a ∈ Thompson.muDelta Ω W,
      Star3T.Conn (Thompson.muDelta Ω W) d a
  · exfalso
    set Δ := Thompson.muDelta Ω W with hΔ
    obtain ⟨d', hne, hcent⟩ : ∃ d', d₀ ≠ d' ∧ Star3T.cent Δ d₀ = {d₀, d'} := by
      obtain ⟨x, y, hxy, hxy'⟩ := Set.ncard_eq_two.mp (hcl d₀ hd₀)
      have hdx : d₀ ∈ ({x, y} : Set _) := hxy' ▸ Star3T.self_mem_cent hd₀
      rcases hdx with rfl | hdy
      · exact ⟨y, hxy, hxy'⟩
      · rw [Set.mem_singleton_iff] at hdy
        subst hdy
        exact ⟨x, fun e => hxy e.symm, by rw [hxy', Set.pair_comm]⟩
    have hd'c : d' ∈ Star3T.cent Δ d₀ := by rw [hcent]; exact Or.inr rfl
    have hd'Δ : d' ∈ Δ := hd'c.1
    have hcomm : d₀ * d' = d' * d₀ := hd'c.2.symm
    have hcent' : Star3T.cent Δ d' = {d₀, d'} := by
      have hsub : ({d₀, d'} : Set _) ⊆ Star3T.cent Δ d' := by
        intro x hx
        rcases hx with rfl | rfl
        · exact ⟨hd₀, hcomm⟩
        · exact Star3T.self_mem_cent hd'Δ
      exact (Set.eq_of_subset_of_ncard_le hsub
        (by rw [hcl d' hd'Δ, Set.ncard_pair hne]) (Set.toFinite _)).symm
    have hall : ∀ a, Relation.ReflTransGen (Star3T.Adj Δ) d₀ a → a = d₀ ∨ a = d' := by
      intro a hb
      induction hb with
      | refl => exact Or.inl rfl
      | @tail b c _ hbc ih =>
        obtain ⟨-, hc, hbc⟩ := hbc
        rcases ih with rfl | rfl
        · have : c ∈ Star3T.cent Δ b := ⟨hc, hbc.symm⟩
          rw [hcent] at this
          exact this
        · have : c ∈ Star3T.cent Δ b := ⟨hc, hbc.symm⟩
          rw [hcent'] at this
          exact this
    have hΔeq : Δ = {d₀, d'} := by
      ext a
      constructor
      · exact fun ha => hall a (hconn d₀ hd₀ a ha)
      · rintro (rfl | rfl)
        · exact hd₀
        · exact hd'Δ
    have hgen : Subgroup.closure ({d₀, d'} : Set ↥(muGroup Ω W)) = ⊤ := by
      rw [← hΔeq]
      exact hTT.closure_eq_top
    obtain ⟨e₁⟩ := T7B.nonempty_mulEquiv_klein (hTT.mul_self d₀ hd₀) (hTT.mul_self d' hd'Δ)
      (hTT.ne_one d₀ hd₀) (hTT.ne_one d' hd'Δ) hne hcomm hgen
    obtain ⟨e₂⟩ := hS4
    have h1 := Nat.card_congr e₁.toEquiv
    have h2 := Nat.card_congr e₂.toEquiv
    rw [h2] at h1
    have h3 : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm]
      rfl
    have h4 : Nat.card (Multiplicative (ZMod 2 × ZMod 2)) = 4 := by
      rw [Nat.card_eq_fintype_card]
      rfl
    omega
  · push Not at hconn
    obtain ⟨d, hd, a, ha, hnc⟩ := hconn
    exact Star3T.exists_mulEquiv_perm_four hTT hS hd ha hnc (hcl d hd)

@[expose] def conjRep (hΩ : HypOmegaGen Ω) {n : G} (hn : n ∈ Subgroup.normalizer (W : Set G))
    (ρ : Thompson.Rep Ω W) : Thompson.Rep Ω W where
  K := conjSub n ρ.K
  R := conjSub n ρ.R
  r := n * ρ.r * n⁻¹
  hK := hΩ.conjInvariant n ρ.K ρ.hK
  hR := Q3CL.Thompson.conjSub_mem_D hΩ ρ.hR hn
  hRK := ρ.hRK.conj n
  hr := conj_mem_conjSub ρ.hr
  hrW := fun h => ρ.hrW ((Thompson.mem_normalizer_iff_of_mem hn _).mp h)

theorem conjRep_img (hΩ : HypOmegaGen Ω) {n : G} (hn : n ∈ Subgroup.normalizer (W : Set G))
    (ρ : Thompson.Rep Ω W) :
    (conjRep hΩ hn ρ).img = Thompson.piG W n * ρ.img * (Thompson.piG W n)⁻¹ := by
  show Thompson.piG W (n * ρ.r * n⁻¹) = Thompson.piG W n * Thompson.piG W ρ.r *
    (Thompson.piG W n)⁻¹
  rw [Thompson.piG_mul (Subgroup.mul_mem _ hn ρ.r_mem_normalizer) (Subgroup.inv_mem _ hn),
    Thompson.piG_mul hn ρ.r_mem_normalizer, Thompson.piG_inv hn]

theorem exists_frame4 {K K' : Subgroup G} {z : G}
    (hs : CFSG.ClassicalInvolution.Q8P.Asc77.Hyp23Setting Ω K K' z) (hW : W ∈ WSet Ω)
    (hzW : z ∈ W) (hS4 : MuIsoS4 Ω W) :
    ∃ (e : ↥(muGroup Ω W) ≃* Equiv.Perm (Fin 4)) (F : T7E.Frame4 Ω W),
      (∀ x, x ∈ Thompson.muDelta Ω W ↔ (e x).IsSwap) ∧ F.ρ.K = K ∧ F.ρ'.K = K' ∧ F.z = z ∧
      T7D.imgQ F.ρ ≠ T7D.imgQ F.ρ' ∧
      T7D.imgQ F.ρ * T7D.imgQ F.ρ' = T7D.imgQ F.ρ' * T7D.imgQ F.ρ ∧
      T7D.imgQ F.ρ * T7D.imgQ F.ρ₃ ≠ T7D.imgQ F.ρ₃ * T7D.imgQ F.ρ ∧
      T7D.imgQ F.ρ' * T7D.imgQ F.ρ₃ ≠ T7D.imgQ F.ρ₃ * T7D.imgQ F.ρ' := by
  have hst : CFSG.ClassicalInvolution.Q8P.Asc77.AscStand Ω K := hs.stand
  have hΩ : HypOmegaGen Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have hK' : K' ∈ Ω := hs.hK'.1
  have hz : IsUniqueInvolution K z := hs.hz
  have hz' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hs.hK'
  have hP : Q3CL.PartIHypG Ω := ⟨hst.hyp, hst.cls, hst.aEmpty⟩
  have c : Q3CL.Thompson.Ctx Ω W :=
    CFSG.ClassicalInvolution.Q8P.Asc77.T7D.ctx_of_stand hst hW
  obtain ⟨e, he⟩ := exists_swap_equiv hP hW hK hst.trans hz hs.hK' hs.hne hs.perp hS4
  obtain ⟨S, R, R', hWS, hRsyl, hR'syl, hRS, hR'S⟩ :=
    CFSG.ClassicalInvolution.Q8P.Asc77.T7D.exists_sylow_frame hs hW hzW
  have hRD : R ∈ DSet Ω W :=
    Q3CL.Thompson.mem_DSet_of_le_sylow hΩ hW hWS (mem_RSet_of_isSylow2In hK hRsyl) hRS
  have hR'D : R' ∈ DSet Ω W :=
    Q3CL.Thompson.mem_DSet_of_le_sylow hΩ hW hWS (mem_RSet_of_isSylow2In hK' hR'syl) hR'S
  obtain ⟨ρ, hρK, -⟩ :=
    CFSG.ClassicalInvolution.Q8P.Asc77.T7D.exists_rep hΩ hW hK hRsyl hRD
  obtain ⟨ρ', hρ'K, -⟩ :=
    CFSG.ClassicalInvolution.Q8P.Asc77.T7D.exists_rep hΩ hW hK' hR'syl hR'D
  have hzρ : IsUniqueInvolution ρ.K z := by rw [hρK]; exact hz
  have hzρ' : IsUniqueInvolution ρ'.K z := by rw [hρ'K]; exact hz'
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
  have hρnbr' : ρ.K ∈ omegaNbr Ω ρ'.K := c.omega_of_comm ρ' ρ hne.symm hcomm.symm
  have hab : T7D.imgQ ρ ≠ T7D.imgQ ρ' := fun h =>
    hne (c.K_eq_of_img_eq ρ ρ' (congrArg Subtype.val h))
  have hcommQ : T7D.imgQ ρ * T7D.imgQ ρ' = T7D.imgQ ρ' * T7D.imgQ ρ := Subtype.ext hcomm
  obtain ⟨c₃, hc₃Δ, hac, hbc⟩ :=
    S4.exists_third he (T7D.imgQ_mem ρ) (T7D.imgQ_mem ρ') hab hcommQ
  obtain ⟨ρ₃, hρ₃⟩ := Thompson.exists_rep_of_mem_muDelta hc₃Δ
  have hc₃ : T7D.imgQ ρ₃ = c₃ := Subtype.ext hρ₃
  have hac' : T7D.imgQ ρ * T7D.imgQ ρ₃ ≠ T7D.imgQ ρ₃ * T7D.imgQ ρ := by rw [hc₃]; exact hac
  have hbc' : T7D.imgQ ρ' * T7D.imgQ ρ₃ ≠ T7D.imgQ ρ₃ * T7D.imgQ ρ' := by rw [hc₃]; exact hbc
  have hne₁ : ρ.K ≠ ρ₃.K := fun h => hac' (by
    have h1 : T7D.imgQ ρ = T7D.imgQ ρ₃ := Subtype.ext (c.img_eq_of_K_eq ρ ρ₃ h)
    rw [← h1])
  have hne₂ : ρ'.K ≠ ρ₃.K := fun h => hbc' (by
    have h1 : T7D.imgQ ρ' = T7D.imgQ ρ₃ := Subtype.ext (c.img_eq_of_K_eq ρ' ρ₃ h)
    rw [← h1])
  obtain ⟨j, hj⟩ := Sec6Gen.exists_uniqueInvolution hΩ ρ₃.hK
  refine ⟨e, ⟨ρ, ρ', ρ₃, z, j, hzρ, hzρ', hj, hρnbr, hρnbr', hne₁, hne₂, ?_, ?_, ?_, ?_⟩, he,
    hρK, hρ'K, rfl, hab, hcommQ, hac', hbc'⟩
  · exact fun h => hac' (Subtype.ext (c.comm_of_omega ρ ρ₃ h))
  · exact fun h => hbc' (Subtype.ext (c.comm_of_omega ρ' ρ₃ h))
  · exact fun h => hac' (Subtype.ext (c.comm_of_omega ρ₃ ρ h).symm)
  · exact fun h => hbc' (Subtype.ext (c.comm_of_omega ρ₃ ρ' h).symm)

end Frame

section Data

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {W : Subgroup G}

theorem exists_data {K K' : Subgroup G} {z : G}
    (hs : CFSG.ClassicalInvolution.Q8P.Asc77.Hyp23Setting Ω K K' z) (hW : W ∈ WSet Ω)
    (hS4 : MuIsoS4 Ω W) (hE : W ⊓ Asc77.centerIn (Subgroup.normalizer (W : Set G)) ≠ ⊥)
    (hzW : z ∈ W) : ∃ (u e g : G), Hyp23bData Ω K K' W z u e g := by
  have hst : CFSG.ClassicalInvolution.Q8P.Asc77.AscStand Ω K := hs.stand
  have : Fact (Q3CL.ClassicalClause Ω) := ⟨hst.cls⟩
  have hΩ : HypOmegaGen Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have hK' : K' ∈ Ω := hs.hK'.1
  have hKK' : K' ≠ K := hs.hne
  have hz : IsUniqueInvolution K z := hs.hz
  have c : Q3CL.Thompson.Ctx Ω W := CFSG.ClassicalInvolution.Q8P.Asc77.T7D.ctx_of_stand hst hW
  obtain ⟨e, F, he, hρK, hρ'K, hFz, hab, hcomm, hac, -⟩ := exists_frame4 hs hW hzW hS4
  obtain ⟨x₁, x₂, x₃, m, hm, h₁, h₂, h₃, o₁, o₂, o₃, z₁, z₂, z₃, k₁, k₂, k₃, hfix⟩ :=
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.T7E.Frame4.exists_structure c F he hab hcomm hac
  rw [hρK] at k₁
  rw [hρ'K] at k₂
  rw [hFz] at z₁ z₂
  have m₁ : x₁ ∈ W := (h₁ ▸ Subgroup.mem_zpowers x₁ : x₁ ∈ F.ρ.R ⊓ W).2
  have m₂ : x₂ ∈ W := (h₂ ▸ Subgroup.mem_zpowers x₂ : x₂ ∈ F.ρ'.R ⊓ W).2
  have m₃ : x₃ ∈ W := (h₃ ▸ Subgroup.mem_zpowers x₃ : x₃ ∈ F.ρ₃.R ⊓ W).2
  have c12 : Commute x₁ x₂ := c.comm_W _ m₁ _ m₂
  have c13 : Commute x₁ x₃ := c.comm_W _ m₁ _ m₃
  have c23 : Commute x₂ x₃ := c.comm_W _ m₂ _ m₃
  have o₃' : x₃ ^ (4 * m) = 1 := by rw [← o₃]; exact pow_orderOf_eq_one x₃
  obtain ⟨hsq_e, hsq_u, hue⟩ := A3Mod.triple_facts c12 c13 c23 o₃' (z₁.trans z₂.symm)
  set e₄ := (x₁ * x₂⁻¹ * x₃ ^ 2) ^ m with he₄
  obtain ⟨a, haE, ha1⟩ : ∃ a ∈ W ⊓ Asc77.centerIn (Subgroup.normalizer (W : Set G)), a ≠ 1 := by
    by_contra hno
    push Not at hno
    exact hE (eq_bot_iff.mpr fun a ha => Subgroup.mem_bot.mpr (hno a ha))
  have hae : a = e₄ := (hfix a haE).resolve_left ha1
  have he₄E : e₄ ∈ W ⊓ Asc77.centerIn (Subgroup.normalizer (W : Set G)) := hae ▸ haE
  have he₄1 : e₄ ≠ 1 := hae ▸ ha1
  set u := x₁ ^ m * (x₂ ^ m)⁻¹ with hu
  have hu4 : orderOf (x₁ ^ m) = 4 := by
    have := orderOf_pow_of_dvd (x := x₁) (n := m) (by omega) (by rw [o₁]; exact dvd_mul_left m 4)
    rwa [o₁, Nat.mul_div_cancel _ hm] at this
  have hu4' : orderOf (x₂ ^ m) = 4 := by
    have := orderOf_pow_of_dvd (x := x₂) (n := m) (by omega) (by rw [o₂]; exact dvd_mul_left m 4)
    rwa [o₂, Nat.mul_div_cancel _ hm] at this
  have hmem₁ : x₁ ^ m ∈ K := K.pow_mem k₁ m
  have hmem₂ : (x₂ ^ m)⁻¹ ∈ K' := K'.inv_mem (K'.pow_mem k₂ m)
  have huK : u ∈ K ⊔ K' := Subgroup.mul_mem_sup hmem₁ hmem₂
  have huW : u ∈ W := W.mul_mem (W.pow_mem m₁ m) (W.inv_mem (W.pow_mem m₂ m))
  have hu2 : u * u = 1 := by rw [← pow_two]; exact hsq_u
  have hu1 : u ≠ 1 := by
    intro h
    have : x₁ ^ m = x₂ ^ m := mul_inv_eq_one.mp h
    exact Hat2A7S.T7X.not_mem_inf_of_orderOf_four hΩ hK hK' hKK' hu4' (this ▸ hmem₁)
      (K'.pow_mem k₂ m)
  have huz : u ≠ z := by
    intro h
    have h1 : (x₂ ^ m)⁻¹ = (x₁ ^ m)⁻¹ * z := by rw [← h, hu]; group
    have h2 : (x₂ ^ m)⁻¹ ∈ K := by
      rw [h1]
      exact K.mul_mem (K.inv_mem hmem₁) hz.mem
    exact Hat2A7S.T7X.not_mem_inf_of_orderOf_four hΩ hK hK' hKK'
      (by rw [orderOf_inv]; exact hu4') h2 hmem₂
  obtain ⟨y, hy⟩ := S4.exists_conj_of_mem he (T7D.imgQ_mem F.ρ) (T7D.imgQ_mem F.ρ₃)
  obtain ⟨g, hgM, hyg⟩ := T7E.exists_mem_MGrp_of_mem_muGroup y
  have hgN : g ∈ Subgroup.normalizer (W : Set G) := Thompson.MGrp_le_normalizer Ω W hgM
  have himg : Thompson.piG W g * F.ρ.img * (Thompson.piG W g)⁻¹ = F.ρ₃.img := by
    rw [← hyg]
    exact congrArg Subtype.val hy
  have hKg : conjSub g F.ρ.K = F.ρ₃.K :=
    c.K_eq_of_img_eq (conjRep c.hΩ hgN F.ρ) F.ρ₃ (by rw [conjRep_img, himg])
  have hzg : g * z * g⁻¹ = F.j := by
    have := F.hz.conj g
    rw [hKg] at this
    rw [hFz] at this
    exact (F.hj.eq this).symm
  have hj : u * e₄ = F.j := by rw [hue, z₃]
  refine ⟨u, e₄, g, ⟨hW, hS4, hzW, huK, huW, hu2, hu1, huz, ?_, he₄1, ?_, hgM, ?_⟩⟩
  · apply le_antisymm
    · rw [Subgroup.closure_le]
      intro x hx
      rw [Set.mem_singleton_iff.mp hx]
      exact he₄E
    · intro b hb
      rcases hfix b hb with h | h
      · rw [h]; exact Subgroup.one_mem _
      · rw [h]; exact Subgroup.subset_closure (Set.mem_singleton _)
  · rw [← pow_two]; exact hsq_e
  · rw [hzg, hj]

end Data

section Setup

theorem p23Setup (n : ℕ) : P23Setup n := by
  intro Y _ _ R S t K' W hstd
  have hC := CoreData.of_S hstd.perp.core
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hperp : KPerp (Om R) (tightCore R) = {tightCore R, K'} :=
    hstd.perp.perp.trans (twinSet_eq_pair hstd.two hstd.hK' hstd.hne)
  have hs : CFSG.ClassicalInvolution.Q8P.Asc77.Hyp23Setting (Om R) (tightCore R) K' t :=
    ⟨CFSG.ClassicalInvolution.Q8P.ascStand_of_twinCore hC, hstd.perp.disc, hz, hstd.hK',
      hstd.hne, hperp⟩
  have hE : W ⊓ Asc77.centerIn (Subgroup.normalizer (W : Set Y)) ≠ ⊥ := by
    obtain ⟨w, hw, hw1, hwc⟩ := hstd.hcen
    intro hbot
    have hwN : w ∈ Subgroup.normalizer (W : Set Y) := Subgroup.le_normalizer hw
    have : w ∈ W ⊓ Asc77.centerIn (Subgroup.normalizer (W : Set Y)) := by
      refine ⟨hw, ⟨⟨w, hwN⟩, Subgroup.mem_center_iff.mpr ?_, rfl⟩⟩
      intro g'
      exact Subtype.ext (hwc g' g'.2)
    rw [hbot] at this
    exact hw1 (Subgroup.mem_bot.mp this)
  exact exists_data hs hstd.hW hstd.hS4 hE hstd.htW

end Setup

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
