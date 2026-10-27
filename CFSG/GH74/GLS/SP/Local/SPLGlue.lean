module

public import CFSG.GH74.GLS.SP.Local.SPLBasic
public import CFSG.GH74.GLS.SP.Local.SPLFaith
public import CFSG.GH74.GLS.SP.Local.SPLRestrict
public import CFSG.GH74.GLS.SP.Local.SPLSetBasic
public import CFSG.GH74.GLS.SP.GenOrder
import CFSG.GH74.GLS.IVK.Proofs2.Lemma48a
public import CFSG.GH74.GLS.SP.Assembly

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.SP
open scoped Pointwise commutatorElement


theorem card_psp4 (Fq : Type) [Field Fq] [Finite Fq] (hodd : Odd (Nat.card Fq)) :
    2 * Nat.card (StatedProj (StatedSp 2 Fq)) =
      Nat.card Fq ^ 4 * (Nat.card Fq ^ 2 - 1) * (Nat.card Fq ^ 4 - 1) :=
  CFSG.GH74.GLS.IVK.Proofs2.Lemma48a.card_proj_statedSp_two Fq hodd


variable {G : Type} [Group G]

section Kernel

variable (D : SPLNot3 G)

theorem conjBy_t_K₁ [Finite G] (hs : SPLSetup D.toSPLNot0) : conjBy D.t D.K₁ = D.K₂ := by
  ext x
  rw [mem_conjBy_iff]
  constructor
  · intro hx
    have h := t_conj_K₁ D hs _ hx
    have e : D.t * (D.t * x * D.t⁻¹) * D.t⁻¹ = x := by
      have : D.t * (D.t * x * D.t⁻¹) * D.t⁻¹ = (D.t * D.t) * x * (D.t * D.t)⁻¹ := by group
      rw [this, t_mul_t D hs]
      simp
    rwa [e] at h
  · intro hx
    exact t_conj_K₂ D hs x hx

theorem K₂_eq [Finite G] (hs : SPLSetup D.toSPLNot0) (h3 : SPL3M2 D) : D.K₂ = D.X₂ ⊔ D.X₂' := by
  rw [← conjBy_t_K₁ D hs, h3.K₁_eq]
  unfold BNPair.conjBy
  rw [Subgroup.map_sup]
  rfl

theorem X₃_exp (h3 : SPL3M2 D) : ∀ x ∈ D.X₃, x ^ D.p = 1 := by
  intro x hx
  rw [SPLNot3.X₃, mem_conjBy_iff] at hx
  have h := h3.Y₁_eab.2 _ hx
  rw [conj_pow] at h
  have h2 : D.a * x ^ D.p * D.a⁻¹ = 1 := h
  have h3' : x ^ D.p = 1 := by
    have := congrArg (fun y => D.a⁻¹ * y * D.a) h2
    simpa [mul_assoc] using this
  exact h3'

theorem H_kernel [Finite G] (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D) :
    ∀ g ∈ D.H, (∀ i, IsRoot 4 i → ∀ x ∈ D.root i, g * x = x * g) → g = 1 := by
  intro g hgH hc
  have hcent : ∀ A : Subgroup G, (∀ x ∈ A, g * x = x * g) → A ≤ centralizer ({g} : Set G) := by
    intro A hA x hx
    rw [mem_centralizer_singleton_iff]
    exact (hA x hx).symm
  have hK₁ : D.K₁ ≤ centralizer ({g} : Set G) := by
    rw [h3.K₁_eq]
    refine sup_le (hcent _ ?_) (hcent _ ?_)
    · intro x hx
      exact hc 4 ⟨by norm_num, by norm_num⟩ x (by rw [root_p4]; exact hx)
    · intro x hx
      exact hc (-4) ⟨by norm_num, by norm_num⟩ x (by rw [root_m4]; exact hx)
  have hK₂ : D.K₂ ≤ centralizer ({g} : Set G) := by
    rw [K₂_eq D hs h3]
    refine sup_le (hcent _ ?_) (hcent _ ?_)
    · intro x hx
      exact hc 2 ⟨by norm_num, by norm_num⟩ x (by rw [root_p2]; exact hx)
    · intro x hx
      exact hc (-2) ⟨by norm_num, by norm_num⟩ x (by rw [root_m2]; exact hx)
  have hgK : g ∈ D.K₁ ⊔ D.K₂ := by
    have h1' : D.H ≤ D.K₁ ⊔ D.K₂ :=
      sup_le (le_trans (H₁_le_K₁ D h1) le_sup_left) (le_trans (H₂_le_K₂ D hs h1) le_sup_right)
    exact h1' hgH
  have hz : g ∈ zpowers D.z := by
    refine mem_zpowers_of_central hs.comps hgK (fun k hk => ?_)
    have : k ∈ centralizer ({g} : Set G) := (sup_le hK₁ hK₂) hk
    rw [mem_centralizer_singleton_iff] at this
    exact this.symm
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
  have hmod : D.z ^ m = D.z ^ (m % 2) := by
    have := zpow_mod_orderOf D.z m
    rw [hs.syl.z_inv] at this
    simpa using this.symm
  have hm2 : m % 2 = 0 ∨ m % 2 = 1 := by omega
  rcases hm2 with h0 | h0
  · rw [hmod, h0]
    simp
  · exfalso
    rw [hmod, h0, zpow_one] at hc
    have hX₃ : D.X₃ ≠ ⊥ := by
      have := root_ne_bot D hs h3 (i := 3) ⟨by norm_num, by norm_num⟩
      rwa [root_p3] at this
    obtain ⟨⟨x, hxX⟩, hx1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hX₃
    have hx1 : x ≠ 1 := fun h => hx1' (Subtype.ext h)
    have hcomm := hc 3 ⟨by norm_num, by norm_num⟩ x (by rw [root_p3]; exact hxX)
    have hinv := h3.z_X₃ x hxX
    have hsq : x * x = 1 := by
      have : x⁻¹ = x := by
        calc x⁻¹ = D.z * x * D.z⁻¹ := hinv.symm
          _ = x := by rw [hcomm]; group
      calc x * x = x * x⁻¹ := by rw [this]
        _ = 1 := by group
    have h2 : x ^ 2 = 1 := by rw [pow_two]; exact hsq
    have hp := X₃_exp D h3 x hxX
    have hdvd1 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one h2
    have hdvd2 : orderOf x ∣ D.p := orderOf_dvd_of_pow_eq_one hp
    have hcop : Nat.Coprime D.p 2 := (Nat.coprime_primes hs.prime Nat.prime_two).2 hs.p_ne_two
    have : orderOf x ∣ 1 := by
      have := Nat.dvd_gcd hdvd2 hdvd1
      rwa [hcop] at this
    exact hx1 (orderOf_eq_one_iff.1 (Nat.dvd_one.1 this))

end Kernel


section Assembly

variable (D : SPLNot3 G)

theorem F_le_cen_S₁ : D.F ≤ centralizer (D.S₁ : Set G) :=
  Subgroup.map_subtype_le _

theorem F_cen_w₁ (h1 : SPL2Set D.toSPLNot1) : ∀ f ∈ D.F, f * D.w₁ = D.w₁ * f := by
  intro f hf
  exact ((mem_centralizer_iff.1 (F_le_cen_S₁ D hf)) D.w₁ h1.w₁_mem_S₁).symm

theorem F_cen_t (h2 : SPL2Ct D.toSPLNot2) : ∀ f ∈ D.F, f * D.t = D.t * f := by
  intro f hf
  exact mem_centralizer_singleton_iff.1 (h2.F_eq hf)

theorem normalizes_sup {F A B : Subgroup G} (hA : Normalizes F A) (hB : Normalizes F B) :
    Normalizes F (A ⊔ B) := by
  intro f hf x hx
  have : A ⊔ B ≤ (A ⊔ B).comap (MulAut.conj f).toMonoidHom := by
    refine sup_le (fun a ha => ?_) (fun b hb => ?_)
    · rw [Subgroup.mem_comap]
      exact (le_sup_left : A ≤ A ⊔ B) (hA f hf a ha)
    · rw [Subgroup.mem_comap]
      exact (le_sup_right : B ≤ A ⊔ B) (hB f hf b hb)
  have h2 := this hx
  rw [Subgroup.mem_comap] at h2
  simpa [MulAut.conj_apply] using h2

theorem le_normalizer_of_normalizes {F A : Subgroup G} (hF : Normalizes F A) :
    F ≤ normalizer (A : Set G) := by
  intro f hf
  rw [mem_normalizer_iff]
  intro h
  constructor
  · exact hF f hf h
  · intro hh
    have := hF f⁻¹ (F.inv_mem hf) _ hh
    simpa [mul_assoc] using this

theorem F_le_M₂ [Finite G] (hs : SPLSetup D.toSPLNot0) (h3 : SPL3X D) : D.F ≤ D.M₂ := by
  have ht : D.t ∈ normalizer (D.F : Set G) := by
    refine normalizer_of_both (t_normalizes_F hs) ?_
    intro h hh
    have := t_normalizes_F hs h hh
    rw [t_inv D hs] at this ⊢
    exact this
  exact le_normalizer_of_normalizes (h3.F_X₁.map_conjBy ht)

theorem F_normalizes_P [Finite G] (hs : SPLSetup D.toSPLNot0) (h3 : SPL3M2 D) :
    Normalizes D.F D.P := by
  have hFM : D.F ≤ D.M₂ := F_le_M₂ D hs h3.toSPL3X
  have hFR : D.F ≤ normalizer (D.R₂ : Set G) := hFM.trans h3.R₂_normal
  have hR : Normalizes D.F D.R₂ := by
    intro f hf x hx
    exact (mem_normalizer_iff.1 (hFR hf) x).1 hx
  exact normalizes_sup h3.F_X₁ hR

theorem F_normalizes_N (h1 : SPL2Set D.toSPLNot1) (h2 : SPL2Ct D.toSPLNot2) :
    Normalizes D.F D.Nw := by
  intro f hf x hx
  have hmem : D.Nw ≤ D.Nw.comap (MulAut.conj f).toMonoidHom := by
    refine (Subgroup.closure_le _).2 ?_
    rintro y (hy | hy)
    · rw [SetLike.mem_coe, Subgroup.mem_comap]
      exact Subgroup.subset_closure (Or.inl (h1.F_norm_H f hf y hy))
    · rw [SetLike.mem_coe, Subgroup.mem_comap]
      rcases hy with rfl | rfl
      · have e : (MulAut.conj f).toMonoidHom D.t = D.t := by
          show f * D.t * f⁻¹ = D.t
          rw [F_cen_t D h2 f hf]
          group
        rw [e]
        exact Subgroup.subset_closure (Or.inr (Or.inl rfl))
      · have e : (MulAut.conj f).toMonoidHom D.w₁ = D.w₁ := by
          show f * D.w₁ * f⁻¹ = D.w₁
          rw [F_cen_w₁ D h1 f hf]
          group
        rw [e]
        exact Subgroup.subset_closure (Or.inr (Or.inr rfl))
  have h2' := hmem hx
  rw [Subgroup.mem_comap] at h2'
  simpa [MulAut.conj_apply] using h2'

end Assembly


section Main

theorem conjBy_le_of_mem {G₀ A : Subgroup G} {m : G} (hm : m ∈ G₀) (hA : A ≤ G₀) :
    conjBy m A ≤ G₀ := by
  intro x hx
  rw [mem_conjBy_iff] at hx
  have h1 := hA hx
  have : x = m⁻¹ * (m * x * m⁻¹) * m := by group
  rw [this]
  exact G₀.mul_mem (G₀.mul_mem (G₀.inv_mem hm) h1) hm


theorem spGlueData_of_stage [Finite G] (hG : IsKProperSimple G) {Fq : Type} [Field Fq] [Finite Fq]
    (hF : 4 ≤ Nat.card Fq) (D : SPLNot4 G) (hq : D.q = Nat.card Fq) (hs : SPLStage4 D)
    (h42 : D.toSPLNot3.L42) (hch : D.toSPLNot3.CH_diff) (hiso : SPLIsoStmt D.toSPLNot3 Fq hF)
    (hFB : D.toSPLNot3.F ⊓ (D.toSPLNot3.H ⊔ D.toSPLNot3.P) = ⊥) :
    SPGlueData G Fq hF := by
  classical
  have : IsSimpleGroup G := hG.1
  obtain ⟨E, hE⟩ : ∃ E : SPLNot3 G, E = D.toSPLNot3 := ⟨_, rfl⟩
  have h0 : SPLSetup E.toSPLNot0 := by rw [hE]; exact hs.setup
  have h1 : SPL2Set E.toSPLNot1 := by rw [hE]; exact hs.set
  have h2 : SPL2Ct E.toSPLNot2 := by rw [hE]; exact hs.ct
  have hord : SPL2Ord E.toSPLNot0 := by rw [hE]; exact hs.ord
  have h3 : SPL3M2 E := by rw [hE]; exact hs.m2
  have hm1 : SPL3M1 D := hs.m1
  rw [← hE] at h42 hch hiso hFB
  have hbru : ∀ y ∈ conjBy E.t E.X₄, y ≠ 1 →
      y ∈ (E.X₄ : Set G) * (E.H : Set G) * {E.t} * (E.X₄ : Set G) := by
    rw [hE]; exact hm1.bruhat₁
  have hC := toCor41 E h0 h1 h3 h42 hch hbru
  have R : RGD2 4 E.H E.t E.w₁ E.P E.root := hC.toRGD2
  obtain ⟨G₀, hG₀⟩ : ∃ G₀ : Subgroup G, G₀ = (E.H ⊔ E.P) ⊔ R.N := ⟨_, rfl⟩
  have hHG : E.H ≤ G₀ := by rw [hG₀]; exact le_trans le_sup_left le_sup_left
  have hPG : E.P ≤ G₀ := by rw [hG₀]; exact le_trans le_sup_right le_sup_left
  have hNG : R.N ≤ G₀ := by rw [hG₀]; exact le_sup_right
  have ht : E.t ∈ G₀ := hNG R.r₁_mem_N
  have hw : E.w₁ ∈ G₀ := hNG R.r₂_mem_N
  have hpos : ∀ k : ℤ, 1 ≤ k → k ≤ 4 → E.root k ≤ G₀ := fun k hk1 hk4 =>
    (R.root_le_U hk1 (by exact_mod_cast hk4)).trans hPG
  have hX₁ : E.X₁ ≤ G₀ := by
    have := hpos 4 (by norm_num) (by norm_num)
    rwa [root_p4] at this
  have hX₂ : E.X₂ ≤ G₀ := by
    have := hpos 2 (by norm_num) (by norm_num)
    rwa [root_p2] at this
  have hX₃ : E.X₃ ≤ G₀ := by
    have := hpos 3 (by norm_num) (by norm_num)
    rwa [root_p3] at this
  have hX₄ : E.X₄ ≤ G₀ := by
    have := hpos 1 (by norm_num) (by norm_num)
    rwa [root_p1] at this
  have hX₁' : E.X₁' ≤ G₀ := by
    rw [h3.X₁'_eq]
    exact conjBy_le_of_mem hw hX₁
  have hX₂' : E.X₂' ≤ G₀ := conjBy_le_of_mem ht hX₁'
  have hroot : ∀ i, IsRoot 4 i → E.root i ≤ G₀ := by
    intro i hi
    rcases root_cases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [root_p1]; exact hX₄
    · rw [root_p2]; exact hX₂
    · rw [root_p3]; exact hX₃
    · rw [root_p4]; exact hX₁
    · rw [root_m1]; exact conjBy_le_of_mem ht hX₄
    · rw [root_m2]; exact hX₂'
    · rw [root_m3]; exact conjBy_le_of_mem (G₀.mul_mem (G₀.mul_mem hw ht) hw) hX₃
    · rw [root_m4]; exact hX₁'
  have R₀ := R.restrict G₀ hHG ht hw hPG hroot
  have hgen0 : (E.H.subgroupOf G₀ ⊔ E.P.subgroupOf G₀) ⊔ R₀.N = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨K', hK'⟩ : ∃ K' : Subgroup ↥G₀, K' = (E.H.subgroupOf G₀ ⊔ E.P.subgroupOf G₀) ⊔ R₀.N :=
      ⟨_, rfl⟩
    rw [← hK']
    have hGle : (E.H ⊔ E.P) ⊔ R.N ≤ K'.map G₀.subtype := by
      refine sup_le (sup_le ?_ ?_) ?_
      · intro h hh
        refine ⟨⟨h, hHG hh⟩, ?_, rfl⟩
        rw [hK']
        exact le_trans (le_sup_left : E.H.subgroupOf G₀ ≤ E.H.subgroupOf G₀ ⊔ E.P.subgroupOf G₀)
          le_sup_left hh
      · intro h hh
        refine ⟨⟨h, hPG hh⟩, ?_, rfl⟩
        rw [hK']
        exact le_trans (le_sup_right : E.P.subgroupOf G₀ ≤ E.H.subgroupOf G₀ ⊔ E.P.subgroupOf G₀)
          le_sup_left hh
      · refine (Subgroup.closure_le _).2 ?_
        rintro y (hy | hy)
        · refine ⟨⟨y, hHG hy⟩, ?_, rfl⟩
          rw [hK']
          have hyH : (⟨y, hHG hy⟩ : ↥G₀) ∈ E.H.subgroupOf G₀ := hy
          exact le_trans (le_sup_left : E.H.subgroupOf G₀ ≤ E.H.subgroupOf G₀ ⊔ E.P.subgroupOf G₀)
            le_sup_left hyH
        · rcases hy with rfl | rfl
          · refine ⟨⟨E.t, ht⟩, ?_, rfl⟩
            rw [hK']
            exact (le_sup_right : R₀.N ≤ E.H.subgroupOf G₀ ⊔ E.P.subgroupOf G₀ ⊔ R₀.N)
              (Subgroup.subset_closure (Or.inr (Or.inl rfl)))
          · refine ⟨⟨E.w₁, hw⟩, ?_, rfl⟩
            rw [hK']
            exact (le_sup_right : R₀.N ≤ E.H.subgroupOf G₀ ⊔ E.P.subgroupOf G₀ ⊔ R₀.N)
              (Subgroup.subset_closure (Or.inr (Or.inr rfl)))
    have hle : G₀ ≤ K'.map G₀.subtype := hG₀.le.trans hGle
    obtain ⟨y, hy, hyx⟩ := hle x.2
    have : y = x := Subtype.ext hyx
    rwa [this] at hy
  have hnorm₀ := R₀.cartan_normal
  have hZ₀ : ∀ g ∈ E.H.subgroupOf G₀, (∀ i, IsRoot 4 i → ∀ x ∈ (E.root i).subgroupOf G₀,
      g * x = x * g) → g = 1 := by
    intro g hg hcomm
    apply Subtype.ext
    exact H_kernel E h0 h1 h3 g.1 hg (fun i hi x hx => by
      have := hcomm i hi ⟨x, hroot i hi hx⟩ hx
      exact congrArg Subtype.val this)
  have hfaith := R₀.faithful hgen0 hZ₀
  let Dsys : RankTwoSystem ↥G₀ 4 := (R₀.toPre hgen0).toSystem hfaith
  obtain ⟨φ, hφ⟩ := hiso
  let φ' : Dsys.U ≃* (SP.modelSystem Fq hF).U := (Subgroup.subgroupOfEquivOfLe hPG).trans φ
  have hφ' : ∀ i : ℤ, 1 ≤ i → i ≤ ((4 : ℕ) : ℤ) → ∀ x : Dsys.U, (x : ↥G₀) ∈ Dsys.root i ↔
      ((φ' x : (SP.modelSystem Fq hF).U) : StatedProj (StatedSp 2 Fq)) ∈
        (SP.modelSystem Fq hF).root i := by
    intro i hi1 hi4 x
    have hi4' : i ≤ 4 := by exact_mod_cast hi4
    exact hφ i hi1 hi4' ⟨(x : ↥G₀).1, x.2⟩
  have : IsSimpleGroup (StatedProj (StatedSp 2 Fq)) := SP.isSimpleGroup_model Fq hF
  obtain ⟨e⟩ := CFSG.GH74.BNPair.theorem30_4.{0} ↥G₀ (StatedProj (StatedSp 2 Fq)) 4 Dsys
    (SP.modelSystem Fq hF) φ' hφ'
  have hX : (SP.modelSystem Fq hF).Xplus = ⊤ := xplus_eq_top _
  have hc1 : Nat.card ↥Dsys.Xplus = Nat.card (StatedProj (StatedSp 2 Fq)) := by
    rw [Nat.card_congr e.toEquiv]
    have : Nat.card ↥(SP.modelSystem Fq hF).Xplus = Nat.card (StatedProj (StatedSp 2 Fq)) := by
      rw [hX]
      exact Subgroup.card_top
    exact this
  have hc2 : Nat.card ↥Dsys.Xplus ≤ Nat.card ↥G₀ := Subgroup.card_le_card_group _
  have hFP := F_normalizes_P E h0 h3
  have hFN := F_normalizes_N E h1 h2
  have hFG : Normalizes E.F G₀ := by
    rw [hG₀]
    exact normalizes_sup (normalizes_sup h1.F_norm_H hFP) hFN
  have hFnorm : E.F ≤ normalizer (G₀ : Set G) := le_normalizer_of_normalizes hFG
  have hinf : G₀ ⊓ E.F = ⊥ := by
    rw [eq_bot_iff]
    rintro f ⟨hfG, hfF⟩
    have hn := R₀.normalizer_B hgen0
    have hF'' : Normalizes (E.F.comap G₀.subtype) (E.H.subgroupOf G₀ ⊔ E.P.subgroupOf G₀) := by
      refine normalizes_sup ?_ ?_
      · intro g hg h hh
        exact h1.F_norm_H _ hg _ hh
      · intro g hg h hh
        exact hFP _ hg _ hh
    have hfB : (⟨f, hfG⟩ : ↥G₀) ∈ Subgroup.normalizer
        ((E.H.subgroupOf G₀ ⊔ E.P.subgroupOf G₀ : Subgroup ↥G₀) : Set ↥G₀) :=
      le_normalizer_of_normalizes hF'' (show (⟨f, hfG⟩ : ↥G₀) ∈ E.F.comap G₀.subtype from hfF)
    rw [hn] at hfB
    have hfB' : (⟨f, hfG⟩ : ↥G₀) ∈ (E.H ⊔ E.P).subgroupOf G₀ :=
      (sup_le (Subgroup.subgroupOf_mono G₀ le_sup_left) (Subgroup.subgroupOf_mono G₀ le_sup_right))
        hfB
    have hfB'' : f ∈ E.H ⊔ E.P := hfB'
    have hmem : f ∈ E.F ⊓ (E.H ⊔ E.P) := ⟨hfF, hfB''⟩
    rw [hFB] at hmem
    exact hmem
  have hodd : Odd (Nat.card Fq) := by
    obtain ⟨k, hk, hqk⟩ := h0.q_pow
    have hEq : E.q = Nat.card Fq := by rw [hE]; exact hq
    rw [← hEq, hqk]
    exact Odd.pow (h0.prime.eq_two_or_odd'.resolve_left h0.p_ne_two)
  have hq2 := card_psp4 Fq hodd
  have hG2 := hord.card_G
  have hEq : E.q = Nat.card Fq := by rw [hE]; exact hq
  rw [hEq] at hG2
  have hcard : Nat.card G ≤ Nat.card ↥G₀ * Nat.card ↥E.F := by
    have h4 : 2 * Nat.card G = (2 * Nat.card (StatedProj (StatedSp 2 Fq))) * Nat.card ↥E.F := by
      rw [hG2, hq2]
    have h5 : Nat.card G = Nat.card (StatedProj (StatedSp 2 Fq)) * Nat.card ↥E.F := by
      apply Nat.eq_of_mul_eq_mul_left (show 0 < 2 by norm_num)
      rw [h4]
      ring
    rw [h5, ← hc1]
    exact Nat.mul_le_mul_right _ hc2
  have hG₀ne : G₀ ≠ ⊥ := by
    intro h
    have := root_ne_bot E h0 h3 (i := 4) ⟨by norm_num, by norm_num⟩
    rw [root_p4] at this
    apply this
    rw [eq_bot_iff]
    exact hX₁.trans h.le
  have hG₀top : G₀ = ⊤ := gen_of_order hG₀ne hFnorm hinf hcard
  have htop : (E.H ⊔ E.P) ⊔ R.N = ⊤ := by rw [← hG₀]; exact hG₀top
  exact ⟨E.H, E.t, E.w₁, E.P, E.root, R, htop, φ, hφ⟩

end Main

end CFSG.GH74.GLS.SP.Local
