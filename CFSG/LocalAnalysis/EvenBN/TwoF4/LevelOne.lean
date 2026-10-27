module

public import CFSG.LocalAnalysis.EvenBN.TwoF4.FieldAut
public import CFSG.LocalAnalysis.EvenBN.TwoF4.ModelLevi
public import CFSG.LocalAnalysis.EvenBN.TwoF4.CosetInvolutions
public import CFSG.Adapters.FrobeniusKernel
public import CFSG.LocalAnalysis.EvenBN.TwoF4.Fusion

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.TwoF4

open Subgroup
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
open CFSG.LieType.Ree.LargeReeCover (torusPair)
open scoped commutatorElement Pointwise

theorem eq_bot_of_isPGroup_of_le_of_normal {X : Type*} [Group X] [Finite X] {N M : Subgroup X}
    [IsSimpleGroup N] (hN : ∃ x y : N, x * y ≠ y * x) (hMN : M ≤ N)
    (hMn : ∀ n ∈ N, ∀ m ∈ M, n * m * n⁻¹ ∈ M) {p : ℕ} [Fact p.Prime] (hM : IsPGroup p M) :
    M = ⊥ := by
  have hn : (M.subgroupOf N).Normal :=
    ⟨fun m hm n => by rw [mem_subgroupOf] at hm ⊢; exact hMn n n.2 m hm⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (M.subgroupOf N) with h1 | h1
  · rw [eq_bot_iff]
    intro m hm
    have : (⟨m, hMN hm⟩ : N) ∈ M.subgroupOf N := hm
    rw [h1, mem_bot] at this
    exact (mem_bot).2 (congrArg Subtype.val this)
  · exfalso
    have hNp : IsPGroup p N := fun x => by
      have hx : x ∈ M.subgroupOf N := h1 ▸ mem_top x
      obtain ⟨k, hk⟩ := hM ⟨x, hx⟩
      exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩
    have : Nontrivial N := by
      obtain ⟨x, y, hxy⟩ := hN
      exact nontrivial_of_ne (x * y) (y * x) hxy
    have hZ := hNp.center_nontrivial
    obtain ⟨x, y, hxy⟩ := hN
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center N) with h2 | h2
    · rw [h2] at hZ
      exact (not_nontrivial_iff_subsingleton.mpr inferInstance) hZ
    · exact hxy (mem_center_iff.mp (h2 ▸ mem_top y) x)

theorem exists_frobenius_kernel_of_action {G₀ Ω : Type} [Group G₀] [Finite G₀] [Finite Ω]
    [MulAction G₀ Ω] (hΩ : 2 ≤ Nat.card Ω) (ω₀ : Ω) (htrans : ∀ ω : Ω, ∃ g : G₀, g • ω₀ = ω)
    (hnt : ∃ g : G₀, g • ω₀ = ω₀ ∧ ∃ ω : Ω, g • ω ≠ ω)
    (hfrob : ∀ g : G₀, ∀ ω ω' : Ω, ω ≠ ω' → g • ω = ω → g • ω' = ω' → ∀ ω'' : Ω, g • ω'' = ω'') :
    ∃ K : Subgroup G₀, (∀ g, g ∈ K ↔ (∀ ω : Ω, g • ω = ω) ∨ ∀ ω : Ω, g • ω ≠ ω) ∧
      (∀ ω : Ω, ∃ k ∈ K, k • ω₀ = ω) ∧ (∀ k ∈ K, k • ω₀ = ω₀ → ∀ ω : Ω, k • ω = ω) := by
  classical
  set ρ := MulAction.toPermHom G₀ Ω with hρ
  set G' := ρ.range with hG'
  have hρapp : ∀ (g : G₀) (ω : Ω), (ρ g) ω = g • ω := fun _ _ => rfl
  set H := MulAction.stabilizer G' ω₀ with hH
  have hmemH : ∀ g : G', g ∈ H ↔ (g : Equiv.Perm Ω) ω₀ = ω₀ := fun g => Iff.rfl
  have hH1 : H ≠ ⊥ := by
    obtain ⟨g, hg, ω, hω⟩ := hnt
    intro hb
    have hmem : (⟨ρ g, g, rfl⟩ : G') ∈ H := (hmemH _).2 hg
    rw [hb, mem_bot] at hmem
    apply hω
    have := congrArg (fun p : G' => (p : Equiv.Perm Ω) ω) hmem
    simp only [OneMemClass.coe_one, Equiv.Perm.coe_one, id_eq] at this
    rw [hρapp] at this
    exact this
  have hHG : H ≠ ⊤ := by
    have : Nontrivial Ω := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨ω, hω⟩ := exists_ne ω₀
    obtain ⟨g, hg⟩ := htrans ω
    intro ht
    have hmem : (⟨ρ g, g, rfl⟩ : G') ∈ H := ht ▸ mem_top _
    rw [hmemH] at hmem
    change (ρ g) ω₀ = ω₀ at hmem
    rw [hρapp, hg] at hmem
    exact hω hmem
  have hconj : ∀ (a g : G'), g ∈ MulAut.conj a • H ↔ a⁻¹ * g * a ∈ H := by
    intro a g
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, ← map_inv,
      MulAut.conj_apply, inv_inv]
  have hfrob' : ∀ g : G', g ∉ H → H ⊓ (MulAut.conj g • H) = ⊥ := by
    intro g hg
    rw [eq_bot_iff]
    intro k hk
    obtain ⟨hk1, hk2⟩ := mem_inf.1 hk
    rw [hconj] at hk2
    obtain ⟨k₀, hk₀⟩ := k.2
    obtain ⟨g₀, hg₀⟩ := g.2
    have hfix1 : k₀ • ω₀ = ω₀ := by
      rw [← hρapp, hk₀]
      exact (hmemH _).1 hk1
    have hfix2 : k₀ • (g₀ • ω₀) = g₀ • ω₀ := by
      have h2 := (hmemH _).1 hk2
      simp only [coe_mul, coe_inv, Equiv.Perm.coe_mul, Function.comp_apply] at h2
      rw [← hg₀, ← hk₀] at h2
      rw [← hρapp g₀, ← hρapp k₀]
      have h3 := congrArg (ρ g₀) h2
      simpa using h3
    have hne : ω₀ ≠ g₀ • ω₀ := by
      intro he
      apply hg
      rw [hmemH, ← hg₀, hρapp]
      exact he.symm
    have htriv := hfrob k₀ ω₀ (g₀ • ω₀) hne hfix1 hfix2
    rw [mem_bot]
    apply Subtype.ext
    rw [← hk₀]
    ext ω
    rw [hρapp, htriv]
    rfl
  obtain ⟨K', hK'c, -, hK'KH, hK'H, -⟩ := CFSG.Adapters.frobenius_kernel H hH1 hHG hfrob'
  have hmemU : ∀ g : G', (g ∈ ⋃ a : G', ((MulAut.conj a • H : Subgroup G') : Set G')) ↔
      ∃ ω, (g : Equiv.Perm Ω) ω = ω := by
    intro g
    rw [Set.mem_iUnion]
    constructor
    · rintro ⟨a, ha⟩
      rw [SetLike.mem_coe, hconj, hmemH] at ha
      refine ⟨(a : Equiv.Perm Ω) ω₀, ?_⟩
      have := congrArg (a : Equiv.Perm Ω) ha
      simpa [Equiv.Perm.coe_mul] using this
    · rintro ⟨ω, hω⟩
      obtain ⟨g₀, rfl⟩ := htrans ω
      refine ⟨⟨ρ g₀, g₀, rfl⟩, ?_⟩
      rw [SetLike.mem_coe, hconj, hmemH]
      simp only [coe_mul, coe_inv, Equiv.Perm.coe_mul, Function.comp_apply]
      rw [hρapp, hω, ← hρapp]
      simp
  refine ⟨K'.comap ρ.rangeRestrict, fun g => ?_, fun ω => ?_, fun k hk hk0 => ?_⟩
  · rw [mem_comap, ← SetLike.mem_coe, hK'c]
    constructor
    · rintro (h1 | ⟨-, h2⟩)
      · left
        intro ω
        have := congrArg (fun p : G' => (p : Equiv.Perm Ω) ω) h1
        exact this
      · right
        intro ω hω
        exact h2 ((hmemU _).2 ⟨ω, hω⟩)
    · rintro (h1 | h2)
      · left
        apply Subtype.ext
        ext ω
        exact h1 ω
      · right
        refine ⟨Set.mem_univ _, fun hU => ?_⟩
        obtain ⟨ω, hω⟩ := (hmemU _).1 hU
        exact h2 ω hω
  · obtain ⟨g, rfl⟩ := htrans ω
    obtain ⟨k, hk, k', hk', hkk'⟩ := hK'KH (ρ.rangeRestrict g)
    obtain ⟨k₀, hk₀⟩ := k.2
    refine ⟨k₀, ?_, ?_⟩
    · rw [mem_comap]
      convert hk
      exact Subtype.ext hk₀
    · have h1 := congrArg (fun p : G' => (p : Equiv.Perm Ω) ω₀) hkk'
      simp only [coe_mul, Equiv.Perm.coe_mul, Function.comp_apply] at h1
      rw [(hmemH k').1 hk', ← hk₀] at h1
      exact h1.symm
  · have hkH : ρ.rangeRestrict k ∈ H := (hmemH _).2 hk0
    have hk' : ρ.rangeRestrict k ∈ K' ⊓ H := mem_inf.2 ⟨hk, hkH⟩
    rw [hK'H, mem_bot] at hk'
    intro ω
    have := congrArg (fun p : G' => (p : Equiv.Perm Ω) ω) hk'
    exact this

namespace Setup

variable {G : Type} [Group G] [Finite G]
  (h : Setup G)

theorem pull_le_centralizer {M M' : Subgroup (ModGL F4.tag h.K)}
    (hMM' : M ≤ centralizer (M' : Set (ModGL F4.tag h.K))) :
    h.pull M ≤ centralizer (h.pull M' : Set G) := by
  intro x hx
  obtain ⟨g, hg, hgΓ, rfl⟩ := (h.mem_pull_iff_elt).1 hx
  rw [mem_centralizer_iff]
  intro y hy
  obtain ⟨k, hk, hkΓ, rfl⟩ := (h.mem_pull_iff_elt).1 hy
  exact (h.commute_elt_iff hkΓ hgΓ).2 (mem_centralizer_iff.1 (hMM' hg) k hk)

theorem isSimpleGroup_N (i : Idx) : IsSimpleGroup (h.N i) ∧ ∃ x y : h.N i, x * y ≠ y * x := by
  obtain ⟨hs, x, y, hxy⟩ := isSimpleGroup_leviN h.one_le_a h.card_K i
  let e : h.N i ≃* leviN h.K h.a i := (((leviN h.K h.a i).subgroupOfEquivOfLe
    (leviN_le_reeGamma h.card_K i)).symm.trans (((leviN h.K h.a i).subgroupOf
      (F4.reeGamma h.K h.a)).equivMapOfInjective h.emb h.emb_injective)).symm
  refine ⟨e.isSimpleGroup, e.symm x, e.symm y, fun h' => hxy (e.symm.injective ?_)⟩
  rw [map_mul, map_mul, h']

theorem R_le_P : h.R ≤ h.P := h.R_le_P_and_S_le_P.1

theorem R_le_L : h.R ≤ h.L := h.pull_le_L _

theorem N_le_L (i : Idx) : h.N i ≤ h.L := h.pull_le_L _

theorem N1_le_normalizer_R : h.N .i1 ≤ normalizer (h.R : Set G) := by
  refine h.pull_le_normalizer fun g hg => ?_
  have hmem : g ∈ F4.reeGamma h.K h.a ⊓ normalizer (radR h.K h.a : Set (ModGL F4.tag h.K)) := by
    rw [(miyamoto_2_3 h.one_le_a h.card_K).1]
    exact mem_sup_left (mem_sup_right hg)
  exact (mem_inf.1 hmem).2

theorem H_le_normalizer_R : h.H ≤ normalizer (h.R : Set G) := by
  refine h.pull_le_normalizer ?_
  rw [(radR_spec h.card_K).1]
  exact torusH_le_normalizer_rootSpan_inf h.card_K fun α hα => hα.1

theorem H_le_normalizer_V (i : Idx) : h.H ≤ normalizer (h.V i : Set G) :=
  h.pull_le_normalizer (torusH_le_normalizer_rootV h.card_K i)

theorem N1_le_centralizer_H1 : h.N .i1 ≤ centralizer (h.Ht .i1 : Set G) :=
  h.pull_le_centralizer (leviN_one_le_centralizer h.card_K)

theorem exists_eq_elt_rootElt {i : Idx} (hi : i.isSz = false) {w : G} (hw : w ∈ h.V i) :
    ∃ c : h.K, w = h.elt (rootElt h.K h.a i c) := by
  obtain ⟨g, hg, -, rfl⟩ := (h.mem_pull_iff_elt).1 hw
  have hg' : g ∈ (rootV h.K h.a i : Set (ModGL F4.tag h.K)) := hg
  rw [coe_rootV h.card_K] at hg'
  obtain ⟨x, hx, rfl⟩ := hg'
  exact ⟨x i.coord, by rw [(sylowVec_eq_of_supp i hx).2 hi]⟩

theorem elt_rootElt_mem_V (i : Idx) (c : h.K) : h.elt (rootElt h.K h.a i c) ∈ h.V i :=
  (h.elt_mem_pull (rootV_le_reeGamma h.card_K i (rootElt_mem_rootV _ _))).2 (rootElt_mem_rootV _ _)

theorem R_sup_N1_le_centralizer_V12 :
    h.R ⊔ h.N .i1 ≤ centralizer (h.V .i12 : Set G) := by
  intro x hx
  rw [← h.centralizer_e_f.1] at hx
  obtain ⟨hxL, hxe⟩ := mem_inf.1 hx
  obtain ⟨g, hgΓ, rfl⟩ := h.exists_elt_eq hxL
  have hE : invE h.K h.a ∈ F4.reeGamma h.K h.a :=
    rootV_le_reeGamma h.card_K .i12 (rootElt_mem_rootV _ _)
  have hge : g ∈ F4.reeGamma h.K h.a ⊓ centralizer {invE h.K h.a} :=
    mem_inf.2 ⟨hgΓ, mem_centralizer_singleton_iff.2
      ((h.commute_elt_iff hgΓ hE).1 (mem_centralizer_singleton_iff.1 hxe))⟩
  rw [mem_centralizer_iff]
  intro w hw
  obtain ⟨c, rfl⟩ := h.exists_eq_elt_rootElt (i := .i12) rfl hw
  have hc := mem_centralizer_singleton_iff.1 (reeGamma_inf_centralizer_invE_le h.one_le_a
    h.card_K c hge)
  exact (h.commute_elt_iff (rootV_le_reeGamma h.card_K .i12 (rootElt_mem_rootV _ _)) hgΓ).2
    hc.symm

theorem P_le_centralizer_V12 : h.P ≤ centralizer (h.V .i12 : Set G) := by
  intro x hx
  rw [mem_centralizer_iff]
  intro w hw
  obtain ⟨c, rfl⟩ := h.exists_eq_elt_rootElt (i := .i12) rfl hw
  obtain ⟨g, hg, hgΓ, rfl⟩ := (h.mem_pull_iff_elt).1 hx
  refine (h.commute_elt_iff (rootV_le_reeGamma h.card_K .i12 (rootElt_mem_rootV _ _)) hgΓ).2 ?_
  have := commute_centralZ h.one_le_a h.card_K hg c
  rw [← sylowH_zero_eq_centralZ] at this
  exact this.symm

@[expose] def E : Subgroup G := zpowers h.t ⊔ h.V .i12

@[expose] def CE : Subgroup G := h.C ⊓ centralizer (h.V .i12 : Set G)

@[expose] def RT : Subgroup G := h.R ⊔ zpowers h.t

theorem V12_le_L : h.V .i12 ≤ h.L := h.pull_le_L _

theorem zpowers_t_le_centralizer_L : zpowers h.t ≤ centralizer (h.L : Set G) :=
  (zpowers_le (H := centralizer (h.L : Set G))).2 h.htL

theorem zpowers_t_le_C : zpowers h.t ≤ h.C := (zpowers_le (H := h.C)).2 h.t_mem_C

theorem exists_mul_of_mem_sup_zpowers_t {M : Subgroup G} (hM : M ≤ h.L) {x : G}
    (hx : x ∈ M ⊔ zpowers h.t) : ∃ m ∈ M, x = m ∨ x = m * h.t := by
  obtain ⟨m, hm, c, hc, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer
    (fun c hc => centralizer_le (fun x hx => hM hx) (h.zpowers_t_le_centralizer_L hc)) hx
  rcases eq_one_or_eq_of_mem_zpowers h.t_mul_t hc with rfl | rfl
  · exact ⟨m, hm, Or.inl (mul_one m)⟩
  · exact ⟨m, hm, Or.inr rfl⟩

theorem mem_E_iff {x : G} : x ∈ h.E ↔ ∃ v ∈ h.V .i12, x = v ∨ x = v * h.t := by
  constructor
  · intro hx
    rw [E, sup_comm] at hx
    exact h.exists_mul_of_mem_sup_zpowers_t h.V12_le_L hx
  · rintro ⟨v, hv, rfl | rfl⟩
    · exact mem_sup_right hv
    · exact mul_mem (mem_sup_right hv) (mem_sup_left (mem_zpowers _))

theorem E_le_C : h.E ≤ h.C := sup_le h.zpowers_t_le_C (h.V12_le_L.trans h.L_le_C)

theorem mul_t_comm {v : G} (hv : v ∈ h.L) : v * h.t = h.t * v := h.commute_t_of_mem_L hv

theorem conj_mem_tV12 {n : G} (hn : n ∈ normalizer (h.E : Set G)) {v : G} (hv : v ∈ h.V .i12) :
    ∃ v' ∈ h.V .i12, n * (h.t * v) * n⁻¹ = h.t * v' := by
  obtain ⟨-, hCL, hN⟩ := h.sec3_1
  obtain ⟨m, -, hm⟩ := hN v hv
  have htvE : h.t * v ∈ h.E := mul_mem (mem_sup_left (mem_zpowers _)) (mem_sup_right hv)
  have hy : n * (h.t * v) * n⁻¹ ∈ h.E := (mem_normalizer_iff.1 hn _).1 htvE
  have hyC : (n * m) * h.t * (n * m)⁻¹ ∈ h.C := by
    rw [show (n * m) * h.t * (n * m)⁻¹ = n * (m * h.t * m⁻¹) * n⁻¹ by group, hm]
    exact h.E_le_C hy
  have hL := hCL _ hyC
  rw [show (n * m) * h.t * (n * m)⁻¹ = n * (m * h.t * m⁻¹) * n⁻¹ by group, hm] at hL
  obtain ⟨v', hv', hv'e | hv'e⟩ := (h.mem_E_iff).1 hy
  · exfalso
    rw [hv'e] at hL
    apply h.t_not_mem_L
    have := mul_mem hL (inv_mem (h.V12_le_L hv'))
    rwa [mul_inv_cancel_right] at this
  · refine ⟨v', hv', ?_⟩
    rw [hv'e, h.mul_t_comm (h.V12_le_L hv')]

theorem conj_V12_mem {n : G} (hn : n ∈ normalizer (h.E : Set G)) {v : G} (hv : v ∈ h.V .i12) :
    n * v * n⁻¹ ∈ h.V .i12 := by
  have hy : n * v * n⁻¹ ∈ h.E := (mem_normalizer_iff.1 hn _).1 (mem_sup_right hv)
  obtain ⟨v', hv', hv'e | hv'e⟩ := (h.mem_E_iff).1 hy
  · rw [hv'e]
    exact hv'
  · exfalso
    obtain ⟨-, -, hN⟩ := h.sec3_1
    obtain ⟨m, -, hm⟩ := hN v' hv'
    apply h.conj_not_mem_L (n⁻¹ * m)
    have hv' : v = n⁻¹ * (v' * h.t) * n := by rw [← hv'e]; group
    rw [show n⁻¹ * m * h.t * (n⁻¹ * m)⁻¹ = n⁻¹ * (m * h.t * m⁻¹) * n by group, hm,
      ← h.mul_t_comm (h.V12_le_L (by assumption)), ← hv']
    exact h.V12_le_L hv

theorem normalizer_P_sup_le_N₀ :
    normalizer ((h.P ⊔ zpowers h.t : Subgroup G) : Set G) ≤ normalizer (h.E : Set G) := by
  have hT := h.sec3_1.1
  have hEZ : ∀ {n : G}, n ∈ normalizer ((h.P ⊔ zpowers h.t : Subgroup G) : Set G) →
      ∀ x ∈ h.E, n * x * n⁻¹ ∈ h.E := by
    intro n hn x hx
    have hxPT : x ∈ h.P ⊔ zpowers h.t := by
      rw [E, sup_comm] at hx
      exact sup_le_sup_right (h.pull_mono (rootV_le_sylowP h.card_K .i12)) _ hx
    have hxc : ∀ y ∈ h.P ⊔ zpowers h.t, y * x = x * y := by
      have hle : h.P ⊔ zpowers h.t ≤ centralizer ({x} : Set G) := by
        refine sup_le (fun p hp => mem_centralizer_singleton_iff.2 ?_)
          ((zpowers_le (H := centralizer ({x} : Set G))).2
            (mem_centralizer_singleton_iff.2 (h.commute_t (h.E_le_C hx)).symm))
        obtain ⟨v, hv, hve⟩ := (h.mem_E_iff).1 hx
        have hpv : p * v = v * p := (mem_centralizer_iff.1 (h.P_le_centralizer_V12 hp) v hv).symm
        have htp := h.mul_t_comm (h.P_le_L hp)
        rcases hve with rfl | rfl
        · exact hpv
        · rw [← mul_assoc, hpv, mul_assoc, htp, mul_assoc]
      exact fun y hy => mem_centralizer_singleton_iff.1 (hle hy)
    have hnx : n * x * n⁻¹ ∈ h.P ⊔ zpowers h.t := (mem_normalizer_iff.1 hn x).1 hxPT
    have hnxc : ∀ y ∈ h.P ⊔ zpowers h.t, y * (n * x * n⁻¹) = (n * x * n⁻¹) * y := by
      intro y hy
      have hy' : n⁻¹ * y * n ∈ h.P ⊔ zpowers h.t := by
        have := (mem_normalizer_iff.1 (inv_mem hn) y).1 hy
        rwa [inv_inv] at this
      have := hxc _ hy'
      calc y * (n * x * n⁻¹) = n * ((n⁻¹ * y * n) * x) * n⁻¹ := by group
        _ = n * (x * (n⁻¹ * y * n)) * n⁻¹ := by rw [this]
        _ = n * x * n⁻¹ * y := by group
    rw [← hT] at hnx hnxc
    obtain ⟨v, hv, c, hc, hvc⟩ := h.exists_mul_of_mem_center_P_sup_Tsyl hnx hnxc
    rw [hT] at hc
    rw [hvc, h.mem_E_iff]
    rcases eq_one_or_eq_of_mem_zpowers h.t_mul_t hc with rfl | rfl
    · exact ⟨v, hv, Or.inl (mul_one v)⟩
    · exact ⟨v, hv, Or.inr rfl⟩
  intro n hn
  refine mem_normalizer_iff.2 fun x => ⟨fun hx => hEZ hn x hx, fun hx => ?_⟩
  have := hEZ (inv_mem hn) _ hx
  rwa [inv_inv, show n⁻¹ * (n * x * n⁻¹) * n = x by group] at this

theorem exists_N₀_conj_t {v : G} (hv : v ∈ h.V .i12) :
    ∃ n ∈ normalizer (h.E : Set G), n * h.t * n⁻¹ = h.t * v := by
  obtain ⟨n, hn, hnt⟩ := h.sec3_1.2.2 v hv
  exact ⟨n, h.normalizer_P_sup_le_N₀ hn, hnt⟩

theorem exists_mul_of_mem_R_sup_N1 {x : G} (hx : x ∈ h.R ⊔ h.N .i1) :
    ∃ r ∈ h.R, ∃ m ∈ h.N .i1, x = r * m := by
  rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left h.R (h.N .i1)
    h.N1_le_normalizer_R, Set.mem_mul] at hx
  obtain ⟨r, hr, m, hm, rfl⟩ := hx
  exact ⟨r, hr, m, hm, rfl⟩

theorem R_sup_N1_le_L : h.R ⊔ h.N .i1 ≤ h.L := sup_le h.R_le_L (h.N_le_L _)

theorem CE_eq_centralizer : h.CE = centralizer (h.E : Set G) := by
  ext x
  constructor
  · rintro ⟨hxt, hxV⟩
    rw [mem_centralizer_iff]
    intro y hy
    obtain ⟨v, hv, hyv⟩ := (h.mem_E_iff).1 hy
    have h1 := mem_centralizer_iff.1 hxV v hv
    have h2 := mem_centralizer_singleton_iff.1 hxt
    rcases hyv with hyv | hyv <;> rw [hyv]
    · exact h1
    · rw [mul_assoc, ← h2, ← mul_assoc, h1, mul_assoc]
  · intro hx
    exact ⟨mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hx h.t
        (mem_sup_left (mem_zpowers _))).symm,
      centralizer_le (fun v hv => mem_sup_right hv) hx⟩

theorem CE_eq : h.CE = (h.R ⊔ h.N .i1) ⊔ zpowers h.t := by
  have hT := h.sec3_1.1
  apply le_antisymm
  · rintro x ⟨hxC, hxV⟩
    have hσ := h.fieldFactor_eq_one_of_commute_V12 ⟨x, hxC⟩ fun v hv =>
      (mem_centralizer_iff.1 hxV v hv).symm
    obtain ⟨l, hl, c, hc, hxlc⟩ := (h.fieldFactor_eq_one_iff ⟨x, hxC⟩).1 hσ
    change x = l * c at hxlc
    have hcT : c ∈ zpowers h.t := hT ▸ hc
    have hlV : l ∈ centralizer (h.V .i12 : Set G) := by
      rw [mem_centralizer_iff]
      intro v hv
      have h1 := mem_centralizer_iff.1 hxV v hv
      have h2 : v * c = c * v := mem_centralizer_iff.1 (mem_inf.1 hc).1 v (h.V12_le_L hv)
      rw [hxlc] at h1
      calc v * l = v * (l * c) * c⁻¹ := by group
        _ = l * c * v * c⁻¹ := by rw [h1]
        _ = l * (c * v) * c⁻¹ := by group
        _ = l * (v * c) * c⁻¹ := by rw [h2]
        _ = l * v := by group
    have hle : l ∈ h.L ⊓ centralizer ({h.e} : Set G) :=
      mem_inf.2 ⟨hl, mem_centralizer_singleton_iff.2
        (mem_centralizer_iff.1 hlV h.e h.e_f_mem_orderOf.1).symm⟩
    rw [h.centralizer_e_f.1] at hle
    rw [hxlc]
    exact mul_mem (mem_sup_left hle) (mem_sup_right hcT)
  · refine sup_le (fun x hx => mem_inf.2 ⟨h.L_le_C (h.R_sup_N1_le_L hx),
      h.R_sup_N1_le_centralizer_V12 hx⟩) fun x hx => mem_inf.2 ⟨h.zpowers_t_le_C hx,
        mem_centralizer_iff.2 fun v hv =>
          mem_centralizer_iff.1 (h.zpowers_t_le_centralizer_L hx) v (h.V12_le_L hv)⟩

theorem exists_of_mem_CE {x : G} (hx : x ∈ h.CE) :
    ∃ r ∈ h.R, ∃ m ∈ h.N .i1, x = r * m ∨ x = r * m * h.t := by
  rw [h.CE_eq] at hx
  obtain ⟨y, hy, hxy⟩ := h.exists_mul_of_mem_sup_zpowers_t h.R_sup_N1_le_L hx
  obtain ⟨r, hr, m, hm, rfl⟩ := h.exists_mul_of_mem_R_sup_N1 hy
  exact ⟨r, hr, m, hm, hxy⟩

theorem RT_le_CE : h.RT ≤ h.CE := by
  rw [h.CE_eq]
  exact sup_le_sup_right le_sup_left _

theorem N1_le_CE : h.N .i1 ≤ h.CE := by
  rw [h.CE_eq]
  exact le_sup_of_le_left le_sup_right

theorem P_le_CE : h.P ≤ h.CE := fun _ hp => ⟨h.P_le_C hp, h.P_le_centralizer_V12 hp⟩

theorem isPGroup_RT : IsPGroup 2 h.RT :=
  (h.isPGroup_P.to_le h.R_le_P).to_sup_of_normal_left' h.isPGroup_zpowers_t fun _ hc =>
    Subgroup.centralizer_le_normalizer _
      (centralizer_le (fun _ hx => h.R_le_L hx) (h.zpowers_t_le_centralizer_L hc))

theorem conj_mem_RT_of_mem_CE {c : G} (hc : c ∈ h.CE) {y : G} (hy : y ∈ h.RT) :
    c * y * c⁻¹ ∈ h.RT := by
  have hRT : ∀ {z : G}, z ∈ normalizer (h.R : Set G) → z * h.t = h.t * z → ∀ y ∈ h.RT,
      z * y * z⁻¹ ∈ h.RT := by
    intro z hzR hzt y hy
    obtain ⟨r, hr, hry⟩ := h.exists_mul_of_mem_sup_zpowers_t h.R_le_L hy
    have hzr : z * r * z⁻¹ ∈ h.R := (mem_normalizer_iff.1 hzR r).1 hr
    rcases hry with rfl | rfl
    · exact mem_sup_left hzr
    · rw [show z * (r * h.t) * z⁻¹ = (z * r * z⁻¹) * (z * h.t * z⁻¹) by group, hzt,
        mul_inv_cancel_right]
      exact mul_mem (mem_sup_left hzr) (mem_sup_right (mem_zpowers _))
  obtain ⟨r, hr, m, hm, hrm | hrm⟩ := h.exists_of_mem_CE hc
  · refine hRT ?_ (h.commute_t (mem_inf.1 hc).1) y hy
    rw [hrm]
    exact mul_mem (le_normalizer hr) (h.N1_le_normalizer_R hm)
  · refine hRT ?_ (h.commute_t (mem_inf.1 hc).1) y hy
    rw [hrm]
    refine mul_mem (mul_mem (le_normalizer hr) (h.N1_le_normalizer_R hm)) ?_
    exact Subgroup.centralizer_le_normalizer _ (centralizer_le (fun _ hx => h.R_le_L hx)
      (h.zpowers_t_le_centralizer_L (mem_zpowers _)))

theorem conj_mem_CE {n : G} (hn : n ∈ normalizer (h.E : Set G)) {c : G} (hc : c ∈ h.CE) :
    n * c * n⁻¹ ∈ h.CE := by
  rw [h.CE_eq_centralizer] at hc ⊢
  rw [mem_centralizer_iff] at hc ⊢
  intro e he
  have he' : n⁻¹ * e * n ∈ h.E := by
    have := (mem_normalizer_iff.1 (inv_mem hn) e).1 he
    rwa [inv_inv] at this
  have := hc _ he'
  calc e * (n * c * n⁻¹) = n * ((n⁻¹ * e * n) * c) * n⁻¹ := by group
    _ = n * (c * (n⁻¹ * e * n)) * n⁻¹ := by rw [this]
    _ = n * c * n⁻¹ * e := by group

theorem conj_mem_RT {n : G} (hn : n ∈ normalizer (h.E : Set G)) {y : G} (hy : y ∈ h.RT) :
    n * y * n⁻¹ ∈ h.RT := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U := h.RT.map (MulAut.conj n).toMonoidHom with hU
  have hUmem : ∀ {u : G}, u ∈ U ↔ n⁻¹ * u * n ∈ h.RT := fun {u} => by
    constructor
    · rintro ⟨y, hy, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rwa [show n⁻¹ * (n * y * n⁻¹) * n = y by group]
    · intro hu
      exact ⟨n⁻¹ * u * n, hu, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
  have hUCE : U ≤ h.CE := by
    rintro _ ⟨y, hy, rfl⟩
    exact h.conj_mem_CE hn (h.RT_le_CE hy)
  have hU2 : IsPGroup 2 U := h.isPGroup_RT.map _
  have hCEU : ∀ c ∈ h.CE, ∀ u ∈ U, c * u * c⁻¹ ∈ U := by
    intro c hc u hu
    rw [hUmem] at hu ⊢
    have hc' : n⁻¹ * c * n ∈ h.CE := by
      have := h.conj_mem_CE (inv_mem hn) hc
      rwa [inv_inv] at this
    have := h.conj_mem_RT_of_mem_CE hc' hu
    rwa [show n⁻¹ * c * n * (n⁻¹ * u * n) * (n⁻¹ * c * n)⁻¹ = n⁻¹ * (c * u * c⁻¹) * n by group]
      at this
  have hRTU : h.RT ≤ normalizer (U : Set G) := fun r hr =>
    mem_normalizer_iff.2 fun u => ⟨fun hu => hCEU r (h.RT_le_CE hr) u hu, fun hu => by
      have := hCEU r⁻¹ (inv_mem (h.RT_le_CE hr)) _ hu
      rwa [inv_inv, show r⁻¹ * (r * u * r⁻¹) * r = u by group] at this⟩
  have hUT2 : IsPGroup 2 (U ⊔ h.RT : Subgroup G) := hU2.to_sup_of_normal_left' h.isPGroup_RT hRTU
  set M := (U ⊔ h.RT) ⊓ h.N .i1 with hM
  have hN1 := h.isSimpleGroup_N .i1
  have := hN1.1
  have hMn : ∀ m ∈ h.N .i1, ∀ x ∈ M, m * x * m⁻¹ ∈ M := by
    intro m hm x hx
    refine mem_inf.2 ⟨?_, mul_mem (mul_mem hm (mem_inf.1 hx).2) (inv_mem hm)⟩
    have hmc : m ∈ h.CE := h.N1_le_CE hm
    have hmN : m ∈ normalizer ((U ⊔ h.RT : Subgroup G) : Set G) := by
      refine inf_normalizer_le_normalizer_sup U h.RT (mem_inf.2 ⟨?_, ?_⟩)
      · exact mem_normalizer_iff.2 fun u => ⟨fun hu => hCEU m hmc u hu, fun hu => by
          have := hCEU m⁻¹ (inv_mem hmc) _ hu
          rwa [inv_inv, show m⁻¹ * (m * u * m⁻¹) * m = u by group] at this⟩
      · exact mem_normalizer_iff.2 fun r => ⟨fun hr => h.conj_mem_RT_of_mem_CE hmc hr,
          fun hr => by
            have := h.conj_mem_RT_of_mem_CE (inv_mem hmc) hr
            rwa [inv_inv, show m⁻¹ * (m * r * m⁻¹) * m = r by group] at this⟩
    exact (mem_normalizer_iff.1 hmN x).1 (mem_inf.1 hx).1
  have hM1 : M = ⊥ := eq_bot_of_isPGroup_of_le_of_normal hN1.2 inf_le_right hMn
    (hUT2.to_le inf_le_left)
  have hu : n * y * n⁻¹ ∈ U := hUmem.2 (by rwa [show n⁻¹ * (n * y * n⁻¹) * n = y by group])
  obtain ⟨r, hr, m, hm, hrm | hrm⟩ := h.exists_of_mem_CE (hUCE hu)
  · have hmM : m ∈ M := by
      refine mem_inf.2 ⟨?_, hm⟩
      rw [show m = r⁻¹ * (n * y * n⁻¹) by rw [hrm]; group]
      exact mul_mem (mem_sup_right (mem_sup_left (inv_mem hr))) (mem_sup_left hu)
    rw [hM1, mem_bot] at hmM
    rw [hrm, hmM, mul_one]
    exact mem_sup_left hr
  · have hmM : m ∈ M := by
      refine mem_inf.2 ⟨?_, hm⟩
      rw [show m = r⁻¹ * (n * y * n⁻¹) * h.t⁻¹ by rw [hrm]; group]
      exact mul_mem (mul_mem (mem_sup_right (mem_sup_left (inv_mem hr))) (mem_sup_left hu))
        (mem_sup_right (mem_sup_right (inv_mem (mem_zpowers _))))
    rw [hM1, mem_bot] at hmM
    rw [hrm, hmM, mul_one]
    exact mul_mem (mem_sup_left hr) (mem_sup_right (mem_zpowers _))

@[expose] def X : Subgroup G := normalizer (h.E : Set G) ⊓ sectionCentralizer h.CE h.RT

theorem mem_normalizer_CE {n : G} (hn : n ∈ normalizer (h.E : Set G)) :
    n ∈ normalizer (h.CE : Set G) :=
  mem_normalizer_iff.2 fun c => ⟨fun hc => h.conj_mem_CE hn hc, fun hc => by
    have := h.conj_mem_CE (inv_mem hn) hc
    rwa [inv_inv, show n⁻¹ * (n * c * n⁻¹) * n = c by group] at this⟩

theorem mem_normalizer_RT {n : G} (hn : n ∈ normalizer (h.E : Set G)) :
    n ∈ normalizer (h.RT : Set G) :=
  mem_normalizer_iff.2 fun c => ⟨fun hc => h.conj_mem_RT hn hc, fun hc => by
    have := h.conj_mem_RT (inv_mem hn) hc
    rwa [inv_inv, show n⁻¹ * (n * c * n⁻¹) * n = c by group] at this⟩

theorem conj_mem_X {n : G} (hn : n ∈ normalizer (h.E : Set G)) {x : G} (hx : x ∈ h.X) :
    n * x * n⁻¹ ∈ h.X := by
  obtain ⟨hxN, hxC⟩ := mem_inf.1 hx
  rw [mem_sectionCentralizer_iff] at hxC
  obtain ⟨hxCE, hxRT, hxu⟩ := hxC
  refine mem_inf.2 ⟨mul_mem (mul_mem hn hxN) (inv_mem hn), ?_⟩
  rw [mem_sectionCentralizer_iff]
  refine ⟨mul_mem (mul_mem (h.mem_normalizer_CE hn) hxCE) (inv_mem (h.mem_normalizer_CE hn)),
    mul_mem (mul_mem (h.mem_normalizer_RT hn) hxRT) (inv_mem (h.mem_normalizer_RT hn)),
    fun u hu => ?_⟩
  have hu' : n⁻¹ * u * n ∈ h.CE := by
    have := h.conj_mem_CE (inv_mem hn) hu
    rwa [inv_inv] at this
  have := h.conj_mem_RT hn (hxu _ hu')
  rwa [show n * ((n⁻¹ * u * n)⁻¹ * x⁻¹ * (n⁻¹ * u * n) * x) * n⁻¹ =
    u⁻¹ * (n * x * n⁻¹)⁻¹ * u * (n * x * n⁻¹) by group] at this

theorem H_le_N₀ : h.H ≤ normalizer (h.E : Set G) := by
  intro g hg
  have hgL : g ∈ h.L := h.H_le_L hg
  have hgV := h.H_le_normalizer_V .i12 hg
  have hconj : ∀ g ∈ h.H, ∀ x ∈ h.E, g * x * g⁻¹ ∈ h.E := by
    intro g hg x hx
    have hgV := h.H_le_normalizer_V .i12 hg
    have hgt := h.commute_t_of_mem_L (h.H_le_L hg)
    obtain ⟨v, hv, hxv | hxv⟩ := (h.mem_E_iff).1 hx <;> rw [hxv]
    · exact mem_sup_right ((mem_normalizer_iff.1 hgV v).1 hv)
    · rw [show g * (v * h.t) * g⁻¹ = (g * v * g⁻¹) * (g * h.t * g⁻¹) by group, hgt,
        mul_inv_cancel_right]
      exact mul_mem (mem_sup_right ((mem_normalizer_iff.1 hgV v).1 hv))
        (mem_sup_left (mem_zpowers _))
  refine mem_normalizer_iff.2 fun x => ⟨fun hx => hconj g hg x hx, fun hx => ?_⟩
  have := hconj g⁻¹ (inv_mem hg) _ hx
  rwa [inv_inv, show g⁻¹ * (g * x * g⁻¹) * g = x by group] at this

theorem H1_le_X : h.Ht .i1 ≤ h.X := by
  intro g hg
  have hgH : g ∈ h.H := h.Ht_le_H .i1 hg
  have hgN := h.H_le_N₀ hgH
  refine mem_inf.2 ⟨hgN, (mem_sectionCentralizer_iff).2 ⟨h.mem_normalizer_CE hgN,
    h.mem_normalizer_RT hgN, fun u hu => ?_⟩⟩
  have hgR := h.H_le_normalizer_R hgH
  have hgt := h.commute_t_of_mem_L (h.H_le_L hgH)
  obtain ⟨r, hr, m, hm, hum | hum⟩ := h.exists_of_mem_CE hu
  all_goals
    have hgm : g * m = m * g := (mem_centralizer_iff.1 (h.N1_le_centralizer_H1 hm) g hg)
    have hr' : g⁻¹ * r * g ∈ h.R := by
      have := (mem_normalizer_iff.1 (inv_mem hgR) r).1 hr
      rwa [inv_inv] at this
    have hmR : m⁻¹ * (r⁻¹ * (g⁻¹ * r * g)) * m ∈ h.R := by
      have := (mem_normalizer_iff.1 (inv_mem (h.N1_le_normalizer_R hm)) _).1
        (mul_mem (inv_mem hr) hr')
      rwa [inv_inv] at this
    have hgm' : g⁻¹ * m * g = m := by rw [mul_assoc, ← hgm, inv_mul_cancel_left]
  · rw [hum, show (r * m)⁻¹ * g⁻¹ * (r * m) * g = m⁻¹ * (r⁻¹ * (g⁻¹ * r * g)) * (g⁻¹ * m * g)
      by group, hgm']
    exact mem_sup_left hmR
  · have hgt' : g⁻¹ * h.t * g = h.t := by rw [mul_assoc, ← hgt, inv_mul_cancel_left]
    rw [hum, show (r * m * h.t)⁻¹ * g⁻¹ * (r * m * h.t) * g =
      h.t⁻¹ * (m⁻¹ * (r⁻¹ * (g⁻¹ * r * g)) * (g⁻¹ * m * g)) * (g⁻¹ * h.t * g) by group, hgm',
      hgt']
    have hc : h.t⁻¹ * (m⁻¹ * (r⁻¹ * (g⁻¹ * r * g)) * m) * h.t ∈ h.R := by
      rw [h.t_inv, ← h.commute_t_of_mem_L (h.R_le_L hmR), mul_assoc, h.t_mul_t, mul_one]
      exact hmR
    exact mem_sup_left hc

theorem e_ne_one : h.e ≠ 1 := fun e1 => by
  have := h.e_f_mem_orderOf.2.2.1
  rw [e1, orderOf_one] at this
  exact absurd this (by norm_num)

theorem exists_X_conj_t {v : G} (hv : v ∈ h.V .i12) :
    ∃ x ∈ h.X, x * h.t * x⁻¹ = h.t * v := by
  by_cases hv1 : v = 1
  · exact ⟨1, one_mem _, by rw [hv1]; group⟩
  have hK := h.card_K
  obtain ⟨c, hc⟩ := exists_largeReeSigma_ne h.one_le_a hK
  have hc0 : c ≠ 0 := fun h0 => hc (by rw [h0, largeReeSigma_zero])
  have hc1 : c ≠ 1 := fun h1 => hc (by rw [h1, largeReeSigma_one])
  obtain ⟨t', ht'H, ht'c⟩ := exists_torusHi_rootChar_mul_eq hK (i := .i1) rfl (j := .i12)
    (by decide) (x := 1) (y := c) one_ne_zero hc0
  have hτΓ : torusPair h.a t' ∈ F4.reeGamma h.K h.a := torusH_le_reeGamma hK ⟨t', rfl⟩
  have hEΓ : invE h.K h.a ∈ F4.reeGamma h.K h.a := rootV_le_reeGamma hK .i12 (rootElt_mem_rootV _ _)
  set g₁ := h.elt (torusPair h.a t') with hg₁
  have hg₁X : g₁ ∈ h.X := h.H1_le_X ((h.elt_mem_pull hτΓ).2 ht'H)
  set e₂ := h.elt (rootElt h.K h.a .i12 c) with he₂
  have hg₁e : g₁ * h.e * g₁⁻¹ = e₂ := by
    rw [hg₁, Setup.e, ← h.elt_conj' hτΓ hEΓ]
    change h.elt (torusPair h.a t' * rootElt h.K h.a .i12 1 * (torusPair h.a t')⁻¹) = _
    rw [torusPair_conj_rootElt hK, ht'c]
  have he₂e : e₂ ≠ h.e := by
    intro he
    apply hc1
    have h1 := h.elt_injOn (rootV_le_reeGamma hK .i12 (rootElt_mem_rootV _ _)) hEΓ he
    exact rootElt_injective hK .i12 h1
  have he₂V : e₂ ∈ h.V .i12 := h.elt_rootElt_mem_V .i12 c
  have heV : h.e ∈ h.V .i12 := h.e_f_mem_orderOf.1
  obtain ⟨m, hm, hmt⟩ := h.exists_N₀_conj_t heV
  have hm' : m⁻¹ ∈ normalizer (h.E : Set G) := inv_mem hm
  have hm'te : m⁻¹ * (h.t * h.e) * m⁻¹⁻¹ = h.t := by rw [← hmt]; group
  obtain ⟨w, hw, hmw⟩ := h.conj_mem_tV12 hm' he₂V
  have hw1 : w ≠ 1 := by
    intro hw1
    rw [hw1, mul_one] at hmw
    apply he₂e
    have : h.t * e₂ = h.t * h.e := by
      calc h.t * e₂ = m * (m⁻¹ * (h.t * e₂) * m⁻¹⁻¹) * m⁻¹ := by group
        _ = m * (m⁻¹ * (h.t * h.e) * m⁻¹⁻¹) * m⁻¹ := by rw [hmw, hm'te]
        _ = h.t * h.e := by group
    exact mul_left_cancel this
  obtain ⟨x₁, hx₁, hx₁e⟩ := h.exists_conj_e_of_mem_V12 hw hw1
  obtain ⟨x₂, hx₂, hx₂e⟩ := h.exists_conj_e_of_mem_V12 hv hv1
  set j := x₂ * x₁⁻¹ with hj
  have hjH : j ∈ h.H := mul_mem hx₂ (inv_mem hx₁)
  have hjt : j * h.t * j⁻¹ = h.t := by rw [h.commute_t_of_mem_L (h.H_le_L hjH)]; group
  have hjw : j * w * j⁻¹ = v := by rw [← hx₁e, ← hx₂e, hj]; group
  set n := j * m⁻¹ with hn
  have hnN : n ∈ normalizer (h.E : Set G) := mul_mem (h.H_le_N₀ hjH) hm'
  have hnt : n⁻¹ * h.t * n = h.t * h.e := by
    rw [hn, show (j * m⁻¹)⁻¹ * h.t * (j * m⁻¹) = m * (j⁻¹ * h.t * j) * m⁻¹ by group,
      show j⁻¹ * h.t * j = h.t by rw [h.commute_t_of_mem_L (inv_mem (h.H_le_L hjH))]; group,
      hmt]
  have hnte₂ : n * (h.t * e₂) * n⁻¹ = h.t * v := by
    rw [hn, show j * m⁻¹ * (h.t * e₂) * (j * m⁻¹)⁻¹ = j * (m⁻¹ * (h.t * e₂) * m⁻¹⁻¹) * j⁻¹ by
      group, hmw, show j * (h.t * w) * j⁻¹ = (j * h.t * j⁻¹) * (j * w * j⁻¹) by group, hjt, hjw]
  refine ⟨n * g₁ * n⁻¹, h.conj_mem_X hnN hg₁X, ?_⟩
  have hg₁t : g₁ * h.t * g₁⁻¹ = h.t := by
    have hc : g₁ * h.t = h.t * g₁ :=
      h.commute_t_of_mem_L (h.H_le_L (h.Ht_le_H .i1 ((h.elt_mem_pull hτΓ).2 ht'H)))
    rw [hc, mul_inv_cancel_right]
  calc n * g₁ * n⁻¹ * h.t * (n * g₁ * n⁻¹)⁻¹ = n * (g₁ * (n⁻¹ * h.t * n) * g₁⁻¹) * n⁻¹ := by
        group
    _ = n * ((g₁ * h.t * g₁⁻¹) * (g₁ * h.e * g₁⁻¹)) * n⁻¹ := by rw [hnt]; group
    _ = h.t * v := by rw [hg₁t, hg₁e, hnte₂]

theorem RT_inf_L : h.RT ⊓ h.L = h.R := by
  refine le_antisymm (fun x hx => ?_) (le_inf le_sup_left h.R_le_L)
  obtain ⟨hx1, hx2⟩ := mem_inf.1 hx
  obtain ⟨r, hr, rfl | rfl⟩ := h.exists_mul_of_mem_sup_zpowers_t h.R_le_L hx1
  · exact hr
  · exfalso
    apply h.t_not_mem_L
    have := mul_mem (inv_mem (h.R_le_L hr)) hx2
    rwa [inv_mul_cancel_left] at this

theorem RT_inf_N1 : h.RT ⊓ h.N .i1 = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hxR : x ∈ h.R := by
    rw [← h.RT_inf_L]
    exact mem_inf.2 ⟨(mem_inf.1 hx).1, h.N_le_L _ (mem_inf.1 hx).2⟩
  have := mem_inf.2 ⟨hxR, (mem_inf.1 hx).2⟩
  rwa [h.centralizer_e_f.2.1] at this

theorem eq_one_of_mem_N1_of_commute {m : G} (hm : m ∈ h.N .i1)
    (hc : ∀ m' ∈ h.N .i1, m' * m = m * m') : m = 1 := by
  obtain ⟨hs, x, y, hxy⟩ := h.isSimpleGroup_N .i1
  have hcen : (⟨m, hm⟩ : h.N .i1) ∈ center (h.N .i1) :=
    mem_center_iff.2 fun g => Subtype.ext (hc g g.2)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (h.N .i1)) with h1 | h1
  · rw [h1, mem_bot] at hcen
    exact congrArg Subtype.val hcen
  · exact absurd (mem_center_iff.mp (h1 ▸ mem_top y) x) hxy

theorem X_inf_CE_le_RT : h.X ⊓ h.CE ≤ h.RT := by
  intro x hx
  obtain ⟨hxX, hxCE⟩ := mem_inf.1 hx
  have hxu := ((mem_sectionCentralizer_iff).1 (mem_inf.1 hxX).2).2.2
  obtain ⟨r, hr, m, hm, hxe⟩ := h.exists_of_mem_CE hxCE
  suffices hm1 : m = 1 by
    rcases hxe with rfl | rfl
    · rw [hm1, mul_one]
      exact mem_sup_left hr
    · rw [hm1, mul_one]
      exact mul_mem (mem_sup_left hr) (mem_sup_right (mem_zpowers _))
  refine h.eq_one_of_mem_N1_of_commute hm fun m' hm' => ?_
  have h1 := hxu m' (h.N1_le_CE hm')
  have hρ : r⁻¹ * (m' * r * m'⁻¹) ∈ h.R :=
    mul_mem (inv_mem hr) ((mem_normalizer_iff.1 (h.N1_le_normalizer_R hm') r).1 hr)
  have hρ' : m'⁻¹ * m⁻¹ * (r⁻¹ * (m' * r * m'⁻¹)) * m * m' ∈ h.R := by
    have h2 := (mem_normalizer_iff.1 (inv_mem (h.N1_le_normalizer_R (mul_mem hm hm'))) _).1 hρ
    rwa [show (m * m')⁻¹ * (r⁻¹ * (m' * r * m'⁻¹)) * (m * m')⁻¹⁻¹ =
      m'⁻¹ * m⁻¹ * (r⁻¹ * (m' * r * m'⁻¹)) * m * m' by group] at h2
  have hz : m'⁻¹ * m⁻¹ * m' * m ∈ h.RT := by
    have key0 : m'⁻¹ * (r * m)⁻¹ * m' * (r * m) =
        (m'⁻¹ * m⁻¹ * (r⁻¹ * (m' * r * m'⁻¹)) * m * m') * (m'⁻¹ * m⁻¹ * m' * m) := by group
    have key : m'⁻¹ * x⁻¹ * m' * x = m'⁻¹ * (r * m)⁻¹ * m' * (r * m) := by
      rcases hxe with rfl | rfl
      · rfl
      · have hw : m'⁻¹ * (r * m)⁻¹ * m' * (r * m) ∈ h.L :=
          mul_mem (mul_mem (mul_mem (inv_mem (h.N_le_L _ hm')) (inv_mem (mul_mem (h.R_le_L hr)
            (h.N_le_L _ hm)))) (h.N_le_L _ hm')) (mul_mem (h.R_le_L hr) (h.N_le_L _ hm))
        have h1 := h.commute_t_of_mem_L (h.N_le_L _ hm')
        have h2 := h.commute_t_of_mem_L hw
        have h1' : m'⁻¹ * h.t⁻¹ * m' = h.t⁻¹ := by
          rw [show m'⁻¹ * h.t⁻¹ * m' = (m'⁻¹ * h.t * m')⁻¹ by group,
            show m'⁻¹ * h.t * m' = h.t by rw [mul_assoc, ← h1, inv_mul_cancel_left]]
        calc m'⁻¹ * (r * m * h.t)⁻¹ * m' * (r * m * h.t) =
            (m'⁻¹ * h.t⁻¹ * m') * (m'⁻¹ * (r * m)⁻¹ * m' * (r * m)) * h.t := by group
          _ = h.t⁻¹ * (m'⁻¹ * (r * m)⁻¹ * m' * (r * m)) * h.t := by rw [h1']
          _ = m'⁻¹ * (r * m)⁻¹ * m' * (r * m) := by rw [mul_assoc, h2, inv_mul_cancel_left]
    rw [key, key0] at h1
    have := mul_mem (inv_mem (mem_sup_left hρ' : _ ∈ h.RT)) h1
    rwa [inv_mul_cancel_left] at this
  have hzN : m'⁻¹ * m⁻¹ * m' * m ∈ h.N .i1 :=
    mul_mem (mul_mem (mul_mem (inv_mem hm') (inv_mem hm)) hm') hm
  have := mem_inf.2 ⟨hz, hzN⟩
  rw [h.RT_inf_N1, mem_bot] at this
  calc m' * m = m' * m * (m'⁻¹ * m⁻¹ * m' * m)⁻¹ := by rw [this, inv_one, mul_one]
    _ = m * m' := by group

theorem X_le_N₀ : h.X ≤ normalizer (h.E : Set G) := inf_le_left

theorem conj_mul_inv_mem_RT {x : G} (hx : x ∈ h.X) {u : G} (hu : u ∈ h.CE) :
    x * u * x⁻¹ * u⁻¹ ∈ h.RT := by
  have h1 := ((mem_sectionCentralizer_iff).1 (mem_inf.1 (inv_mem hx)).2).2.2 u hu
  rw [inv_inv] at h1
  have := h.conj_mem_RT_of_mem_CE hu h1
  rwa [show u * (u⁻¹ * x * u * x⁻¹) * u⁻¹ = x * u * x⁻¹ * u⁻¹ by group] at this

theorem fieldFactor_eq_one_of_mem_X (x : h.C) (hx : (x : G) ∈ h.X) : h.fieldFactor x = 1 := by
  have hR : ∀ {u : G}, u ∈ h.CE → u ∈ h.L → (x : G) * u * (x : G)⁻¹ * u⁻¹ ∈ h.R := by
    intro u hu huL
    rw [← h.RT_inf_L]
    exact mem_inf.2 ⟨h.conj_mul_inv_mem_RT hx hu,
      mul_mem (h.conj_mem_L x.2 huL) (inv_mem huL)⟩
  refine h.fieldFactor_eq_one_of_V2 x (fun p hp => ?_) (fun u => ?_)
  · rw [show (x : G) * p * (x : G)⁻¹ = ((x : G) * p * (x : G)⁻¹ * p⁻¹) * p by group]
    exact mul_mem (h.R_le_P (hR (h.P_le_CE hp) (h.P_le_L hp))) hp
  · have hw : h.elt (rootElt h.K h.a .i2 u) ∈ h.N .i1 := h.V_le_N .i2 (h.elt_rootElt_mem_V .i2 u)
    exact hR (h.N1_le_CE hw) (h.N_le_L _ hw)

theorem mem_CE_of_mem_X_of_fix {x : G} (hx : x ∈ h.X) (hxC : x ∈ h.C) {v : G}
    (hv : v ∈ h.V .i12) (hv1 : v ≠ 1) (hfix : x * v * x⁻¹ = v) : x ∈ h.CE := by
  have hσ := h.fieldFactor_eq_one_of_mem_X ⟨x, hxC⟩ hx
  obtain ⟨l, hl, c, hc, hxlc⟩ := (h.fieldFactor_eq_one_iff ⟨x, hxC⟩).1 hσ
  change x = l * c at hxlc
  have hlx : ∀ w ∈ h.V .i12, l * w * l⁻¹ = x * w * x⁻¹ := by
    intro w hw
    rw [hxlc, show l * c * w * (l * c)⁻¹ = l * (c * w * c⁻¹) * l⁻¹ by group]
    congr 2
    have := mem_centralizer_iff.1 (mem_inf.1 hc).1 w (h.V12_le_L hw)
    rw [← this, mul_inv_cancel_right]
  have hlV : ∀ w ∈ h.V .i12, l * w * l⁻¹ ∈ h.V .i12 := fun w hw => by
    rw [hlx w hw]
    exact h.conj_V12_mem (h.X_le_N₀ hx) hw
  have hlc := h.commute_V12_of_conj_eq hl hlV hv hv1 (by rw [hlx v hv, hfix])
  refine mem_inf.2 ⟨hxC, mem_centralizer_iff.2 fun w hw => ?_⟩
  rw [hxlc, ← mul_assoc, ← hlc w hw, mul_assoc,
    mem_centralizer_iff.1 (mem_inf.1 hc).1 w (h.V12_le_L hw), ← mul_assoc]

@[reducible] def actX : MulAction h.X (h.V .i12) where
  smul x v := ⟨h.t⁻¹ * ((x : G) * (h.t * v) * (x : G)⁻¹), by
    obtain ⟨v', hv', he⟩ := h.conj_mem_tV12 (h.X_le_N₀ x.2) v.2
    rw [he, inv_mul_cancel_left]
    exact hv'⟩
  one_smul v := Subtype.ext (by
    change h.t⁻¹ * ((1 : G) * (h.t * v) * (1 : G)⁻¹) = v
    group)
  mul_smul x y v := Subtype.ext (by
    change h.t⁻¹ * ((x * y : G) * (h.t * v) * (x * y : G)⁻¹) =
      h.t⁻¹ * ((x : G) * (h.t * (h.t⁻¹ * ((y : G) * (h.t * v) * (y : G)⁻¹))) * (x : G)⁻¹)
    group)

@[reducible] def actConj (M : Subgroup G) (hM : M ≤ normalizer (h.E : Set G)) :
    MulAction M (h.V .i12) where
  smul m v := ⟨(m : G) * v * (m : G)⁻¹, h.conj_V12_mem (hM m.2) v.2⟩
  one_smul v := Subtype.ext (by change (1 : G) * v * (1 : G)⁻¹ = v; group)
  mul_smul x y v := Subtype.ext (by
    change (x * y : G) * v * (x * y : G)⁻¹ = (x : G) * ((y : G) * v * (y : G)⁻¹) * (x : G)⁻¹
    group)

theorem exists_H1_conj_eq {v w : G} (hv : v ∈ h.V .i12) (hw : w ∈ h.V .i12) (hv1 : v ≠ 1)
    (hw1 : w ≠ 1) : ∃ g ∈ h.Ht .i1, g * v * g⁻¹ = w := by
  have hK := h.card_K
  obtain ⟨v₀, rfl⟩ := h.exists_eq_elt_rootElt (i := .i12) rfl hv
  obtain ⟨w₀, rfl⟩ := h.exists_eq_elt_rootElt (i := .i12) rfl hw
  have hv₀ : v₀ ≠ 0 := fun h0 => hv1 (by rw [h0, rootElt_zero, h.elt_one'])
  have hw₀ : w₀ ≠ 0 := fun h0 => hw1 (by rw [h0, rootElt_zero, h.elt_one'])
  obtain ⟨t', ht'H, ht'c⟩ := exists_torusHi_rootChar_mul_eq hK (i := .i1) rfl (j := .i12)
    (by decide) hv₀ hw₀
  have hτΓ : torusPair h.a t' ∈ F4.reeGamma h.K h.a := torusH_le_reeGamma hK ⟨t', rfl⟩
  refine ⟨h.elt (torusPair h.a t'), (h.elt_mem_pull hτΓ).2 ht'H, ?_⟩
  rw [← h.elt_conj' hτΓ (rootV_le_reeGamma hK .i12 (rootElt_mem_rootV _ _)),
    torusPair_conj_rootElt hK, ht'c]

theorem RT_le_X : h.RT ≤ h.X := by
  intro r hr
  have hrCE := h.RT_le_CE hr
  have hrN : r ∈ normalizer (h.E : Set G) := by
    rw [h.CE_eq_centralizer] at hrCE
    exact Subgroup.centralizer_le_normalizer _ hrCE
  refine mem_inf.2 ⟨hrN, (mem_sectionCentralizer_iff).2 ⟨h.mem_normalizer_CE hrN,
    h.mem_normalizer_RT hrN, fun u hu => ?_⟩⟩
  have := h.conj_mem_RT_of_mem_CE (inv_mem hu) (inv_mem hr)
  rw [inv_inv] at this
  exact mul_mem this hr

theorem sec3_3 : ∃ Y : Subgroup G, IsPGroup 2 Y ∧ h.RT ≤ Y ∧ Y ≤ h.X ∧
    (∀ n ∈ normalizer (h.E : Set G), ∀ y ∈ Y, n * y * n⁻¹ ∈ Y) ∧
    Y ⊓ h.C = h.RT ∧ Y ≤ centralizer (h.V .i12 : Set G) ∧
    ∀ v ∈ h.V .i12, ∃ y ∈ Y, y * h.t * y⁻¹ = h.t * v := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ := h.actX
  have hfix : ∀ (x : h.X) (v : h.V .i12), x • v = v ↔
      (x : G) * (h.t * v) * (x : G)⁻¹ = h.t * v := by
    intro x v
    constructor
    · intro hxv
      have := congrArg Subtype.val hxv
      change h.t⁻¹ * ((x : G) * (h.t * v) * (x : G)⁻¹) = v at this
      calc (x : G) * (h.t * v) * (x : G)⁻¹ =
          h.t * (h.t⁻¹ * ((x : G) * (h.t * v) * (x : G)⁻¹)) := by group
        _ = h.t * v := by rw [this]
    · intro hxv
      apply Subtype.ext
      change h.t⁻¹ * ((x : G) * (h.t * v) * (x : G)⁻¹) = v
      rw [hxv, inv_mul_cancel_left]
  have hfix1 : ∀ x : h.X, x • (1 : h.V .i12) = 1 ↔ (x : G) ∈ h.C := by
    intro x
    rw [hfix, mem_centralizer_singleton_iff]
    simp only [OneMemClass.coe_one, mul_one]
    constructor
    · intro hx
      calc (x : G) * h.t = (x : G) * h.t * (x : G)⁻¹ * x := by group
        _ = h.t * x := by rw [hx]
    · intro hx
      rw [hx, mul_inv_cancel_right]
  have htriv : ∀ x : h.X, (∀ v : h.V .i12, x • v = v) ↔ (x : G) ∈ h.CE := by
    intro x
    constructor
    · intro hx
      have hxC := (hfix1 x).1 (hx 1)
      refine mem_inf.2 ⟨hxC, mem_centralizer_iff.2 fun w hw => ?_⟩
      have h1 := (hfix x ⟨w, hw⟩).1 (hx ⟨w, hw⟩)
      have hxt := mem_centralizer_singleton_iff.1 hxC
      change (x : G) * (h.t * w) * (x : G)⁻¹ = h.t * w at h1
      have h2 : (x : G) * w * (x : G)⁻¹ = w := by
        have e : (x : G) * (h.t * w) * (x : G)⁻¹ = ((x : G) * h.t * (x : G)⁻¹) * ((x : G) * w *
          (x : G)⁻¹) := by group
        rw [e, hxt, mul_inv_cancel_right] at h1
        exact mul_left_cancel h1
      calc w * x = (x : G) * w * (x : G)⁻¹ * x := by rw [h2]
        _ = x * w := by group
    · intro hx v
      apply (hfix x v).2
      rw [h.CE_eq_centralizer] at hx
      have h1 := mem_centralizer_iff.1 hx (h.t * v)
        (mul_mem (mem_sup_left (mem_zpowers _)) (mem_sup_right v.2))
      rw [← h1, mul_inv_cancel_right]
  have htrans : ∀ v : h.V .i12, ∃ x : h.X, x • (1 : h.V .i12) = v := by
    intro v
    obtain ⟨x, hx, hxt⟩ := h.exists_X_conj_t v.2
    refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
    change h.t⁻¹ * (x * (h.t * 1) * x⁻¹) = v
    rw [mul_one, hxt, inv_mul_cancel_left]
  have hcardV : Nat.card (h.V .i12) = 2 ^ (2 * h.a + 1) := by
    rw [h.card_V]
    simp [Idx.isSz]
  have hΩ : 2 ≤ Nat.card (h.V .i12) := by
    rw [hcardV]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * h.a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hnt : ∃ x : h.X, x • (1 : h.V .i12) = 1 ∧ ∃ v : h.V .i12, x • v ≠ v := by
    obtain ⟨c, hc⟩ := exists_largeReeSigma_ne h.one_le_a h.card_K
    have hc0 : c ≠ 0 := fun h0 => hc (by rw [h0, largeReeSigma_zero])
    have hc1 : c ≠ 1 := fun h1 => hc (by rw [h1, largeReeSigma_one])
    set e₂ := h.elt (rootElt h.K h.a .i12 c) with he₂
    have he₂V : e₂ ∈ h.V .i12 := h.elt_rootElt_mem_V .i12 c
    have he₂1 : e₂ ≠ 1 := fun h1 => hc0 (rootElt_injective h.card_K .i12 (h.elt_injOn
      (rootV_le_reeGamma h.card_K .i12 (rootElt_mem_rootV _ _)) (one_mem _)
        (by rw [← he₂, h1, h.elt_one']) |>.trans (rootElt_zero .i12).symm))
    have he₂e : e₂ ≠ h.e := fun he => hc1 (rootElt_injective h.card_K .i12 (h.elt_injOn
      (rootV_le_reeGamma h.card_K .i12 (rootElt_mem_rootV _ _))
        (rootV_le_reeGamma h.card_K .i12 (rootElt_mem_rootV _ _)) he))
    obtain ⟨g, hg, hge⟩ := h.exists_H1_conj_eq h.e_f_mem_orderOf.1 he₂V h.e_ne_one he₂1
    have hgX := h.H1_le_X hg
    have hgt := h.commute_t_of_mem_L (h.H_le_L (h.Ht_le_H .i1 hg))
    refine ⟨⟨g, hgX⟩, (hfix1 _).2 (h.L_le_C (h.H_le_L (h.Ht_le_H .i1 hg))),
      ⟨h.e, h.e_f_mem_orderOf.1⟩, fun he => ?_⟩
    rw [hfix] at he
    change g * (h.t * h.e) * g⁻¹ = h.t * h.e at he
    rw [show g * (h.t * h.e) * g⁻¹ = (g * h.t * g⁻¹) * (g * h.e * g⁻¹) by group, hge, hgt,
      mul_inv_cancel_right] at he
    exact he₂e (mul_left_cancel he)
  have hfrob : ∀ g : h.X, ∀ ω ω' : h.V .i12, ω ≠ ω' → g • ω = ω → g • ω' = ω' →
      ∀ ω'' : h.V .i12, g • ω'' = ω'' := by
    intro g ω ω' hne hω hω' ω''
    obtain ⟨x₀, hx₀⟩ := htrans ω
    set x' := x₀⁻¹ * g * x₀ with hx'
    have hx'1 : x' • (1 : h.V .i12) = 1 := by
      rw [hx', mul_smul, mul_smul, hx₀, hω, ← hx₀, inv_smul_smul]
    set w := x₀⁻¹ • ω' with hw
    have hx'w : x' • w = w := by
      rw [hx', hw, mul_smul, mul_smul, smul_inv_smul, hω']
    have hw1 : (w : G) ≠ 1 := by
      intro hw1
      apply hne
      rw [← hx₀, show (1 : h.V .i12) = w from (Subtype.ext hw1.symm), hw, smul_inv_smul]
    have hx'C := (hfix1 x').1 hx'1
    have hx'w' : (x' : G) * w * (x' : G)⁻¹ = w := by
      have h1 := (hfix x' w).1 hx'w
      rw [show (x' : G) * (h.t * w) * (x' : G)⁻¹ = ((x' : G) * h.t * (x' : G)⁻¹) *
        ((x' : G) * w * (x' : G)⁻¹) by group, mem_centralizer_singleton_iff.1 hx'C,
        mul_inv_cancel_right] at h1
      exact mul_left_cancel h1
    have hx'CE := h.mem_CE_of_mem_X_of_fix x'.2 hx'C w.2 hw1 hx'w'
    have hx'triv := (htriv x').2 hx'CE
    have hg : g = x₀ * x' * x₀⁻¹ := by rw [hx']; group
    rw [hg, mul_smul, mul_smul, hx'triv, smul_inv_smul]
  obtain ⟨K, hKc, hKt, hKs⟩ := exists_frobenius_kernel_of_action hΩ 1 htrans hnt hfrob
  set Y := K.map h.X.subtype with hY
  have hYn : ∀ n ∈ normalizer (h.E : Set G), ∀ y ∈ Y, n * y * n⁻¹ ∈ Y := by
    rintro n hn _ ⟨k, hk, rfl⟩
    have hnk : n * (k : G) * n⁻¹ ∈ h.X := h.conj_mem_X hn k.2
    refine ⟨⟨_, hnk⟩, (hKc _).2 ?_, rfl⟩
    by_cases hfp : ∀ ω : h.V .i12, (⟨_, hnk⟩ : h.X) • ω ≠ ω
    · exact Or.inr hfp
    left
    push Not at hfp
    obtain ⟨u, hu⟩ := hfp
    obtain ⟨u', hu', hnu⟩ := h.conj_mem_tV12 (inv_mem hn) u.2
    have hku : k • (⟨u', hu'⟩ : h.V .i12) = ⟨u', hu'⟩ := by
      rw [hfix]
      have h1 := (hfix _ u).1 hu
      change n * (k : G) * n⁻¹ * (h.t * u) * (n * (k : G) * n⁻¹)⁻¹ = h.t * u at h1
      change (k : G) * (h.t * u') * (k : G)⁻¹ = h.t * u'
      rw [← hnu, inv_inv]
      calc (k : G) * (n⁻¹ * (h.t * ↑u) * n) * (k : G)⁻¹ =
          n⁻¹ * (n * (k : G) * n⁻¹ * (h.t * ↑u) * (n * (k : G) * n⁻¹)⁻¹) * n := by group
        _ = n⁻¹ * (h.t * ↑u) * n := by rw [h1]
    have hktriv : ∀ ω : h.V .i12, k • ω = ω := by
      rcases (hKc k).1 hk with h1 | h1
      · exact h1
      · exact absurd hku (h1 _)
    have hkCE := (htriv k).1 hktriv
    exact (htriv _).2 (h.conj_mem_CE hn hkCE)
  have hYC : Y ⊓ h.C = h.RT := by
    apply le_antisymm
    · rintro _ ⟨⟨k, hk, rfl⟩, hkC⟩
      have hk1 : k • (1 : h.V .i12) = 1 := (hfix1 k).2 hkC
      have := (htriv k).1 (hKs k hk hk1)
      exact h.X_inf_CE_le_RT (mem_inf.2 ⟨k.2, this⟩)
    · exact le_inf (fun r hr => ⟨⟨r, h.RT_le_X hr⟩, (hKc _).2 (Or.inl ((htriv _).2
        (h.RT_le_CE hr))), rfl⟩) (fun r hr => (mem_inf.1 (h.RT_le_CE hr)).1)
  have hK2 : IsPGroup 2 K := by
    have hstab : IsPGroup 2 (MulAction.stabilizer K (1 : h.V .i12)) := by
      intro s
      have hsC : (((s : K) : h.X) : G) ∈ Y ⊓ h.C :=
        ⟨⟨(s : K), (s : K).2, rfl⟩, (hfix1 ((s : K) : h.X)).1 s.2⟩
      rw [hYC] at hsC
      obtain ⟨k, hk⟩ := h.isPGroup_RT ⟨_, hsC⟩
      refine ⟨k, Subtype.ext (Subtype.ext (Subtype.ext ?_))⟩
      have := congrArg Subtype.val hk
      simpa using this
    obtain ⟨b, hb⟩ := IsPGroup.iff_card.1 hstab
    have horbit : (MulAction.orbit K (1 : h.V .i12)) = Set.univ := by
      ext ω
      simp only [Set.mem_univ, iff_true]
      obtain ⟨k, hk, hkω⟩ := hKt ω
      exact ⟨⟨k, hk⟩, hkω⟩
    have hcard : Nat.card K = Nat.card (h.V .i12) * Nat.card
        (MulAction.stabilizer K (1 : h.V .i12)) := by
      rw [← Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup K (1 : h.V .i12)),
        Nat.card_prod, horbit, Nat.card_univ]
    rw [hcardV, hb, ← pow_add] at hcard
    exact IsPGroup.of_card hcard
  have hY2 : IsPGroup 2 Y := hK2.map _
  have hYV : Y ≤ centralizer (h.V .i12 : Set G) := by
    have hYN : Y ≤ normalizer (h.E : Set G) := (map_subtype_le K).trans h.X_le_N₀
    let _ := h.actConj Y hYN
    have h1 : (1 : h.V .i12) ∈ MulAction.fixedPoints Y (h.V .i12) := fun y =>
      Subtype.ext (by change (y : G) * 1 * (y : G)⁻¹ = 1; group)
    have h2 : 2 ∣ Nat.card (h.V .i12) := by
      rw [hcardV]
      exact dvd_pow_self 2 (by omega)
    obtain ⟨b, hb, hb1⟩ := hY2.exists_fixed_point_of_prime_dvd_card_of_fixed_point _ h2 h1
    have hbfix : ∀ y ∈ Y, y * (b : G) * y⁻¹ = b := fun y hy =>
      congrArg Subtype.val (hb ⟨y, hy⟩)
    have hb1' : (b : G) ≠ 1 := fun e => hb1 (Subtype.ext e.symm)
    intro y hy
    rw [mem_centralizer_iff]
    intro w hw
    by_cases hw1 : w = 1
    · rw [hw1, one_mul, mul_one]
    obtain ⟨g, hg, hgb⟩ := h.exists_H1_conj_eq b.2 hw hb1' hw1
    have hgN := h.H_le_N₀ (h.Ht_le_H .i1 hg)
    have hy' : g⁻¹ * y * g ∈ Y := by
      have := hYn g⁻¹ (inv_mem hgN) y hy
      rwa [inv_inv] at this
    have h3 := hbfix _ hy'
    have h4 : y * w * y⁻¹ = w := by
      rw [← hgb]
      calc y * (g * ↑b * g⁻¹) * y⁻¹ = g * ((g⁻¹ * y * g) * ↑b * (g⁻¹ * y * g)⁻¹) * g⁻¹ := by
            group
        _ = g * ↑b * g⁻¹ := by rw [h3]
    calc w * y = y * w * y⁻¹ * y := by rw [h4]
      _ = y * w := by group
  refine ⟨Y, hY2, fun r hr => ⟨⟨r, h.RT_le_X hr⟩, (hKc _).2 (Or.inl ((htriv _).2
    (h.RT_le_CE hr))), rfl⟩, map_subtype_le K, hYn, hYC, hYV, ?_⟩
  · intro v hv
    obtain ⟨k, hk, hkv⟩ := hKt ⟨v, hv⟩
    refine ⟨k, ⟨k, hk, rfl⟩, ?_⟩
    have := congrArg Subtype.val hkv
    change h.t⁻¹ * ((k : G) * (h.t * 1) * (k : G)⁻¹) = v at this
    rw [mul_one] at this
    calc (k : G) * h.t * (k : G)⁻¹ = h.t * (h.t⁻¹ * ((k : G) * h.t * (k : G)⁻¹)) := by group
      _ = h.t * v := by rw [this]

end Setup

end CFSG.LocalAnalysis.EvenBN.TwoF4
