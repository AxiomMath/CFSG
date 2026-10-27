module

public import CFSG.LocalAnalysis.EvenBN.G2.LocalU

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.EvenSmallLie.UnitarySix.YamadaD (oTwo le_oTwo oTwo_le isPGroup_oTwo le_normalizer_oTwo)
open CFSG.LocalAnalysis.EvenBN.Common (CosetData)
open scoped commutatorElement Pointwise

section Defs

variable
  {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]

@[expose] noncomputable def yamadaL₂ (d : G2Data L K) (t : G) : Subgroup G :=
  pCoreOf 2 (normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G))

@[expose] noncomputable def yamadaR₂ (d : G2Data L K) (t : G) : Subgroup G :=
  yamadaL₂ d t ⊔ d.S

theorem yamadaL₂_le (d : G2Data L K) (t : G) :
    yamadaL₂ d t ≤ normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G) :=
  LieType.BorelTits.pCoreOf_le 2 _

theorem le_normalizer_yamadaL₂ (d : G2Data L K) (t : G) :
    normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G) ≤ normalizer (yamadaL₂ d t : Set G) :=
  LieType.BorelTits.le_normalizer_pCoreOf 2 _

end Defs

namespace Model

section Torus

variable {K : Type} [Field K]

theorem J₁_inf_J₅_le_J₄ : J₁ K ⊓ J₅ K ≤ J₄ K := by
  rintro h ⟨h1, h5⟩
  obtain ⟨t₁, t₂, rfl⟩ := exists_eq_torusElt_mul h1.1
  have hc := torus_conj_of (m₁ := 1) (m₂ := 0) isRoot_g2c t₁ t₂ (by decide) (by decide) 1
  rw [(mem_centralizer_iff.1 h1.2 _ (mem_rootSubgroup.2 ⟨1, rfl⟩)).symm, mul_inv_cancel_right]
    at hc
  have hb := torus_conj_of (m₁ := -1) (m₂ := 3) isRoot_g2b t₁ t₂ (by decide) (by decide) 1
  rw [(mem_centralizer_iff.1 h5.2 _ (mem_rootSubgroup.2 ⟨1, rfl⟩)).symm, mul_inv_cancel_right]
    at hb
  have e1 := eq_one_of_pinnedX_eq hc.symm
  have e5 := eq_one_of_pinnedX_eq hb.symm
  refine mem_torusFix_of (m₁ := 2) (m₂ := -3) isRoot_g2a t₁ t₂ (by decide) (by decide) ?_
  rw [zpow_one, zpow_zero, mul_one] at e1
  rw [e1, one_zpow, one_mul] at e5 ⊢
  rw [zpow_neg, e5, inv_one]

end Torus


variable
  {K : Type} [Field K] [CharP K 2]

theorem commutator_leviB_mem_M [Finite K] {a g : ModGL .G2 K} (ha : a ∈ leviB K)
    (hg : g ∈ M K ⊔ (J₁ K ⊓ J₅ K)) : a * g * a⁻¹ * g⁻¹ ∈ M K := by
  have hJM : J₁ K ⊓ J₅ K ≤ normalizer (M K : Set (ModGL .G2 K)) := fun j hj =>
    borelGroup_le_normalizer_M (mem_sup_left hj.1.1)
  obtain ⟨m, hm, j, hj, rfl⟩ := Common.exists_mul_of_le_normalizer hJM g hg
  have hja : j * a = a * j := (mem_centralizer_iff.1 (J₄_le_centralizer_leviB
    (J₁_inf_J₅_le_J₄ hj)) a ha).symm
  have e : a * (m * j) * a⁻¹ * (m * j)⁻¹ = a * m * a⁻¹ * m⁻¹ := by
    calc a * (m * j) * a⁻¹ * (m * j)⁻¹ = a * m * (j * a⁻¹ * j⁻¹) * m⁻¹ := by group
      _ = a * m * a⁻¹ * m⁻¹ := by
        rw [show j * a⁻¹ * j⁻¹ = a⁻¹ by
          rw [show j * a⁻¹ = a⁻¹ * j from ((Commute.inv_right (hja : Commute j a)).eq),
            mul_inv_cancel_right]]
  rw [e]
  exact mul_mem ((mem_normalizer_iff.1 (leviB_le_normalizer_M ha) m).1 hm) (inv_mem hm)

end Model

namespace G2Data

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] (d : G2Data L K)

variable
  [Finite K] [CharP K 2]

theorem exists_leviB_conj_mem_U {y : G} (hy : y ∈ d.Y) (hy1 : y ≠ 1) :
    ∃ l ∈ d.leviB, l⁻¹ * y * l ∈ d.U := by
  obtain ⟨y₀, hy₀, rfl⟩ := d.mem_image.1 hy
  have hy₀1 : (y₀ : ModGL .G2 K) ≠ 1 := fun h1 =>
    hy1 (by rw [show y₀ = 1 from Subtype.ext h1, map_one])
  obtain ⟨l, hl, hly⟩ := Model.exists_leviB_conj_mem_U hy₀ hy₀1
  have hlA : l ∈ adjointGroup .G2 K := Model.leviB_le_adjointGroup K hl
  refine ⟨d.emb ⟨l, hlA⟩, d.emb_mem_image hl, ?_⟩
  rw [← map_inv, ← map_mul, ← map_mul]
  exact d.emb_mem_image (by simpa using hly)

theorem mem_Y_iff_commutator (hK : 4 ≤ Nat.card K) {s : G} (hs : s ∈ d.S) :
    s ∈ d.Y ↔ ∀ s' ∈ d.S, ⁅s, s'⁆ ∈ d.U := by
  obtain ⟨hU, hY, -⟩ := d.yamada_3_12_upperCentralSeries hK
  have h1 : s ∈ d.Y ↔ (⟨s, hs⟩ : d.S) ∈ Subgroup.upperCentralSeries d.S 2 := by
    rw [← hY, ← mem_map_iff_mem d.S.subtype_injective]
    rfl
  rw [h1, show (2 : ℕ) = 1 + 1 from rfl, Subgroup.mem_upperCentralSeries_succ_iff]
  constructor
  · intro h s' hs'
    have h2 := h ⟨s', hs'⟩
    rw [← mem_map_iff_mem d.S.subtype_injective, hU] at h2
    exact h2
  · intro h y
    rw [← mem_map_iff_mem d.S.subtype_injective, hU]
    exact h y y.2

theorem exists_mulEquiv_Y :
    ∃ ι : Multiplicative (Fin 2 → K) ≃* d.Y, ∃ ρ : SL2 K →* G, ρ.range = d.leviB ∧
      ∀ (g : SL2 K) (v : Fin 2 → K), ρ g * (ι (Multiplicative.ofAdd v) : G) * (ρ g)⁻¹ =
        ι (Multiplicative.ofAdd (Matrix.mulVec (g : Matrix (Fin 2) (Fin 2) K) v)) := by
  obtain ⟨ρ, hρ, -, ⟨φ, hφi, hφr, hφa, hφc⟩, -⟩ := d.yamada_3_16_2_natural_G
  have hφY : ∀ v, φ v ∈ d.Y := fun v => by
    have h1 : φ v ∈ (d.Y : Set G) := by
      rw [← hφr]
      exact ⟨v, rfl⟩
    exact h1
  let ψ : Multiplicative (Fin 2 → K) →* d.Y :=
    { toFun := fun v => ⟨φ (Multiplicative.toAdd v), hφY _⟩
      map_one' := Subtype.ext (by
        have h0 := hφa 0 0
        rw [add_zero] at h0
        simpa using (mul_eq_left.1 h0.symm))
      map_mul' := fun v w => Subtype.ext (hφa _ _) }
  have hψ : Function.Bijective ψ := by
    refine ⟨fun v w hvw => ?_, fun y => ?_⟩
    · have := hφi (congrArg (fun z : d.Y => (z : G)) hvw)
      exact Multiplicative.toAdd.injective this
    · obtain ⟨v, hv⟩ : (y : G) ∈ Set.range φ := by rw [hφr]; exact y.2
      exact ⟨Multiplicative.ofAdd v, Subtype.ext hv⟩
  exact ⟨MulEquiv.ofBijective ψ hψ, ρ, hρ, fun g v => hφc g v⟩

theorem normalizer_inf_centralizer_Y_le {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) :
    normalizer (L : Set G) ⊓ centralizer (d.Y : Set G) ≤
      d.image (Model.M K ⊔ (Model.J₁ K ⊓ Model.J₅ K)) ⊔ centralizer (L : Set G) := by
  rintro x ⟨hxN, hxY⟩
  have h1 : d.act ⟨x, hxN⟩ ∈ centralizer (Model.inn (Model.Y K) :
      Set (MulAut (adjointGroup .G2 K))) :=
    Model.mem_centralizer_inn_iff.2 ((d.act_mem_centralizer_inn_iff hxN).2 hxY)
  rw [Model.yamada_3_23_Y hK hn] at h1
  exact (d.act_mem_inn_iff hxN).1 h1

end G2Data

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Local

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem mem_tY_iff (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) {x : G} :
    x ∈ d.Y ⊔ zpowers t ↔
      x ∈ yamadaR d t ∧ ∀ r ∈ yamadaR d t, ⁅x, r⁆ ∈ d.U ⊔ zpowers t := by
  have hK4 : 4 ≤ Nat.card K := hK ▸ h.four_le
  have hSL : d.S ≤ L := d.image_le _
  obtain ⟨-, hYX, -, hXF, -, hFD, -, hDS, -, -⟩ := d.inclusions
  have hYS : d.Y ≤ d.S := hYX.trans (hXF.trans (hFD.trans hDS))
  have hdec : ∀ r ∈ yamadaR d t, ∃ s ∈ d.S, ∃ c ∈ zpowers t, r = s * c := by
    intro r hr
    rw [h.yamadaR_eq d] at hr
    have hset := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute d.S (zpowers t)
      fun x hx y hy => (commute_of_mem_zpowers hy (h.L_le_centralizer (hSL hx)))).2
    have hr' : r ∈ ((d.S ⊔ zpowers t : Subgroup G) : Set G) := hr
    rw [hset] at hr'
    obtain ⟨s, hs, c, hc, rfl⟩ := hr'
    exact ⟨s, hs, c, hc, rfl⟩
  have hcomm : ∀ s ∈ d.S, ∀ c ∈ zpowers t, ∀ s' ∈ d.S, ∀ c' ∈ zpowers t,
      ⁅s * c, s' * c'⁆ = ⁅s, s'⁆ := by
    intro s hs c hc s' hs' c' hc'
    exact commutatorElement_mul_mul_of_commute
      (commute_of_mem_zpowers hc (h.L_le_centralizer (hSL hs'))).symm
      (commute_of_mem_zpowers hc ((zpowers_le).2 h.t_mem_centralizer hc')).symm
      (commute_of_mem_zpowers hc' (h.L_le_centralizer (hSL hs))).symm
  have hUL : ∀ y ∈ L, y ∈ d.U ⊔ zpowers t → y ∈ d.U := by
    intro y hyL hy
    rcases (h.mem_sup_zpowers_iff (d.image_le _)).1 hy with h1 | h1
    · exact h1
    · exfalso
      refine h.t_not_mem_L ?_
      have := mul_mem (d.image_le _ h1) (inv_mem hyL)
      rwa [mul_inv_cancel_right] at this
  have hcL : ∀ s ∈ d.S, ∀ s' ∈ d.S, ⁅s, s'⁆ ∈ L := fun s hs s' hs' => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem (hSL hs) (hSL hs')) (inv_mem (hSL hs))) (inv_mem (hSL hs'))
  constructor
  · intro hx
    have hset := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute d.Y (zpowers t)
      fun x hx y hy => (commute_of_mem_zpowers hy (h.L_le_centralizer (d.image_le _ hx)))).2
    have hx' : x ∈ ((d.Y ⊔ zpowers t : Subgroup G) : Set G) := hx
    rw [hset] at hx'
    obtain ⟨y, hy, c, hc, rfl⟩ := hx'
    refine ⟨(h.yamadaR_eq d).ge (mul_mem (mem_sup_left (hYS hy)) (mem_sup_right hc)),
      fun r hr => ?_⟩
    obtain ⟨s', hs', c', hc', rfl⟩ := hdec r hr
    rw [hcomm y (hYS hy) c hc s' hs' c' hc']
    exact mem_sup_left (((d.mem_Y_iff_commutator hK4 (hYS hy)).1 hy) s' hs')
  · rintro ⟨hxR, hx⟩
    obtain ⟨s, hs, c, hc, rfl⟩ := hdec x hxR
    have hsY : s ∈ d.Y := (d.mem_Y_iff_commutator hK4 hs).2 fun s' hs' => by
      have h1 := hx s' ((h.yamadaR_eq d).ge (mem_sup_left hs'))
      rw [show s' = s' * 1 by rw [mul_one], hcomm s hs c hc s' hs' 1 (one_mem _)] at h1
      exact hUL _ (hcL s hs s' hs') h1
    exact mul_mem (mem_sup_left hsY) (mem_sup_right hc)

theorem normalizer_yamadaR_le_normalizer_tY (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) :
    normalizer (yamadaR d t : Set G) ≤ normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G) := by
  refine le_normalizer_of_conj_mem fun n hn x hx => ?_
  obtain ⟨hxR, hxc⟩ := (h.mem_tY_iff d hK).1 hx
  refine (h.mem_tY_iff d hK).2 ⟨(mem_normalizer_iff.1 hn x).1 hxR, fun r hr => ?_⟩
  have hr' : n⁻¹ * r * n ∈ yamadaR d t := by
    have := (mem_normalizer_iff.1 (inv_mem hn) r).1 hr
    rwa [inv_inv] at this
  have h1 := (mem_normalizer_iff.1 (h.normalizer_yamadaR_le d hn) _).1 (hxc _ hr')
  rwa [show n * ⁅x, n⁻¹ * r * n⁆ * n⁻¹ = ⁅n * x * n⁻¹, r⁆ by
    simp only [commutatorElement_def]
    group] at h1

theorem yamadaR₁_le_normalizer_tY (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) :
    yamadaR₁ d t ≤ normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G) :=
  (h.yamada_5_3_3 d hK).2.2.le.trans (h.normalizer_yamadaR_le_normalizer_tY d hK)

omit [Finite K] in
theorem centralizer_inf_normalizer_Y_le (_h : Setup G L f t) (d : G2Data L K) :
    centralizer ({t} : Set G) ⊓ normalizer (d.Y : Set G) ≤
      normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G) := fun _ hx =>
  mem_normalizer_sup hx.2 (mem_normalizer_zpowers (mem_centralizer_singleton_iff.1 hx.1))

theorem leviB_le_centralizer_inf_normalizer_Y (h : Setup G L f t) (d : G2Data L K) :
    d.leviB ≤ centralizer ({t} : Set G) ⊓ normalizer (d.Y : Set G) := by
  have h1 := (d.yamada_3_13_3_G).1
  intro x hx
  have hx' : x ∈ L ⊓ normalizer (d.Y : Set G) := by
    rw [h1]
    exact mem_sup_right (mem_sup_left hx)
  exact ⟨h.L_le_centralizer hx'.1, hx'.2⟩

theorem conj_tY (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) :
    {x | ∃ n ∈ normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G), n * t * n⁻¹ = x} =
      (fun y => t * y) '' (d.Y : Set G) := by
  have hYL : d.Y ≤ L := d.image_le _
  ext x
  constructor
  · rintro ⟨n, hn, rfl⟩
    have h1 : n * t * n⁻¹ ∈ d.Y ⊔ zpowers t :=
      (mem_normalizer_iff.1 hn t).1 (mem_sup_right (mem_zpowers t))
    rcases (h.mem_sup_zpowers_iff hYL).1 h1 with h2 | h2
    · exact absurd h2 (h.conj_not_mem_Y d hK n)
    · exact ⟨_, h2, by beta_reduce; rw [← mul_assoc, h.t_mul_t, one_mul]⟩
  · rintro ⟨y, hy, rfl⟩
    by_cases hy1 : y = 1
    · exact ⟨1, one_mem _, by rw [hy1]; group⟩
    obtain ⟨l, hl, hlu⟩ := d.exists_leviB_conj_mem_U hy hy1
    obtain ⟨-, -, h3, -⟩ := h.two_core_C₁ d hK
    obtain ⟨c, hc, hct⟩ := h3 _ hlu
    have hlt : l * t = t * l :=
      mem_centralizer_singleton_iff.1 (h.L_le_centralizer (d.image_le _ hl))
    refine ⟨l * c⁻¹, mul_mem (h.centralizer_inf_normalizer_Y_le d
      (h.leviB_le_centralizer_inf_normalizer_Y d hl))
      (inv_mem (h.yamadaR₁_le_normalizer_tY d hK (mem_sup_left hc))), ?_⟩
    calc l * c⁻¹ * t * (l * c⁻¹)⁻¹ = l * (c⁻¹ * t * c) * l⁻¹ := by group
      _ = l * (t * (l⁻¹ * y * l)) * l⁻¹ := by rw [hct]
      _ = (l * t) * l⁻¹ * y * l * l⁻¹ := by group
      _ = t * y := by rw [hlt]; group

theorem normalizer_tY_le_normalizer_Y (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) :
    normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G) ≤ normalizer (d.Y : Set G) := by
  refine le_normalizer_of_conj_mem fun g hg u hu => ?_
  have h1 : g * u * g⁻¹ ∈ d.Y ⊔ zpowers t := (mem_normalizer_iff.1 hg u).1 (mem_sup_left hu)
  rcases (h.mem_sup_zpowers_iff (d.image_le _)).1 h1 with h2 | h2
  · exact h2
  · exfalso
    have hmem : g * u * g⁻¹ ∈ (fun y => t * y) '' (d.Y : Set G) :=
      ⟨_, h2, by beta_reduce; rw [← mul_assoc, h.t_mul_t, one_mul]⟩
    rw [← h.conj_tY d hK] at hmem
    obtain ⟨n, -, hnt⟩ := hmem
    refine h.conj_not_mem_Y d hK (g⁻¹ * n) ?_
    rw [show g⁻¹ * n * t * (g⁻¹ * n)⁻¹ = g⁻¹ * (n * t * n⁻¹) * g by group, hnt,
      show g⁻¹ * (g * u * g⁻¹) * g = u by group]
    exact hu

theorem cosetData_tY (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) :
    CosetData (normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G)) d.Y t :=
  CosetData.of_le_normalizer h.t_mul_t ((d.image_le _).trans h.L_le_centralizer)
    d.isElementaryAbelian.2.1 (h.normalizer_tY_le_normalizer_Y d hK) le_rfl

theorem normalizer_tY_inf_centralizer (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) :
    normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G) ⊓ centralizer ({t} : Set G) =
      centralizer ({t} : Set G) ⊓ normalizer (d.Y : Set G) :=
  le_antisymm (fun _ hx => ⟨hx.2, h.normalizer_tY_le_normalizer_Y d hK hx.1⟩)
    fun _ hx => ⟨h.centralizer_inf_normalizer_Y_le d hx, hx.1⟩

theorem exists_mul_of_mem_centralizer_Y (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) {k : G}
    (hk : k ∈ centralizer ({t} : Set G) ⊓ centralizer (d.Y : Set G)) :
    ∃ l ∈ d.image (Model.M K ⊔ (Model.J₁ K ⊓ Model.J₅ K)), ∃ c ∈ zpowers t, k = l * c := by
  obtain ⟨hkC, hkY⟩ := mem_inf.1 hk
  have h1 := d.normalizer_inf_centralizer_Y_le hK h.two_le ⟨h.centralizer_le_normalizer hkC, hkY⟩
  have hset := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
    (d.image (Model.M K ⊔ (Model.J₁ K ⊓ Model.J₅ K))) (centralizer (L : Set G))
    fun x hx y hy => mem_centralizer_iff.1 hy x (d.image_le _ hx)).2
  have h1' : k ∈ ((d.image (Model.M K ⊔ (Model.J₁ K ⊓ Model.J₅ K)) ⊔ centralizer (L : Set G) :
    Subgroup G) : Set G) := h1
  rw [hset] at h1'
  obtain ⟨l, hl, c, hc, rfl⟩ := h1'
  have hlC : l ∈ centralizer ({t} : Set G) := h.L_le_centralizer (d.image_le _ hl)
  have hcC : c ∈ centralizer ({t} : Set G) := by
    have := mul_mem (inv_mem hlC) hkC
    rwa [inv_mul_cancel_left] at this
  have hct : c ∈ zpowers t := by
    rw [← h.centralizer_L_inf]
    exact ⟨hc, hcC⟩
  exact ⟨l, hl, c, hct, rfl⟩

omit [Finite K] in
theorem M_le_centralizer_Y (_h : Setup G L f t) (d : G2Data L K) :
    d.M ≤ centralizer (d.Y : Set G) := by
  rw [← Subgroup.le_centralizer_iff, ← (d.yamada_3_12_centers).2.2.1]
  exact inf_le_right

omit [Finite K] in
theorem tM_le_kernel (h : Setup G L f t) (d : G2Data L K) :
    d.M ⊔ zpowers t ≤ normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G) ⊓
      centralizer (d.Y : Set G) ⊓ centralizer ({t} : Set G) := by
  have htY : t ∈ centralizer (d.Y : Set G) := mem_centralizer_iff.2 fun u hu =>
    mem_centralizer_singleton_iff.1 (h.L_le_centralizer (d.image_le _ hu))
  refine sup_le (fun x hx => ?_) ((zpowers_le).2 ⟨⟨h.centralizer_inf_normalizer_Y_le d
    ⟨h.t_mem_centralizer, Subgroup.centralizer_le_normalizer _ htY⟩, htY⟩, h.t_mem_centralizer⟩)
  have hxY := h.M_le_centralizer_Y d hx
  have hxt := h.L_le_centralizer (d.image_le _ hx)
  exact ⟨⟨h.centralizer_inf_normalizer_Y_le d ⟨hxt, Subgroup.centralizer_le_normalizer _ hxY⟩,
    hxY⟩, hxt⟩

theorem isPGroup_tM (h : Setup G L f t) (d : G2Data L K) :
    IsPGroup 2 (d.M ⊔ zpowers t : Subgroup G) := by
  obtain ⟨-, -, -, -, -, -, -, -, hMS, -⟩ := d.inclusions
  exact (h.isSylowOf_yamadaR d).isPGroup.to_le
    (sup_le (hMS.trans le_sup_left) ((zpowers_le).2 (mem_sup_right h.t_mem_kernel)))

theorem normalizer_tY_le_normalizer_kernel (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) :
    normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G) ≤
      normalizer ((normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G) ⊓
        centralizer (d.Y : Set G) ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G) :=
  le_normalizer_of_conj_mem fun _ hg _ hk => (h.cosetData_tY d hK).conj_mem_kernel hg hk

theorem oTwo_kernel_Y (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) :
    oTwo (normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G) ⊓ centralizer (d.Y : Set G) ⊓
      centralizer ({t} : Set G)) = d.M ⊔ zpowers t := by
  have hHo : normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G) ≤
      normalizer ((oTwo (normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G) ⊓
        centralizer (d.Y : Set G) ⊓ centralizer ({t} : Set G)) : Subgroup G) : Set G) :=
    le_normalizer_of_conj_mem fun _ hg _ hy =>
      Common.conj_mem_oTwo_of_mem_normalizer (h.normalizer_tY_le_normalizer_kernel d hK hg) hy
  have hK₂ : normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G) ⊓ centralizer (d.Y : Set G) ⊓
      centralizer ({t} : Set G) ≤ centralizer ({t} : Set G) ⊓ normalizer (d.Y : Set G) :=
    fun _ hk => ⟨hk.2, Subgroup.centralizer_le_normalizer _ hk.1.2⟩
  apply le_antisymm
  · exact h.le_sup_of_pCoreOf d (h.pCoreOf_range_act d hK).2 ((oTwo_le _).trans hK₂)
      ((h.centralizer_inf_normalizer_Y_le d).trans hHo) (isPGroup_oTwo _)
  · refine le_oTwo (h.tM_le_kernel d) (fun k hk => ?_) (h.isPGroup_tM d)
    have hk' := hK₂ hk
    exact mem_normalizer_sup
      (h.centralizer_inf_normalizer_le_of_pCoreOf d (h.pCoreOf_range_act d hK).2 hk')
      (mem_normalizer_zpowers (mem_centralizer_singleton_iff.1 hk'.1))

theorem normalizer_tY_le_normalizer_tM (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) :
    normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G) ≤
      normalizer ((d.M ⊔ zpowers t : Subgroup G) : Set G) := by
  rw [← h.oTwo_kernel_Y d hK]
  exact le_normalizer_of_conj_mem fun _ hg _ hy =>
    Common.conj_mem_oTwo_of_mem_normalizer (h.normalizer_tY_le_normalizer_kernel d hK hg) hy

theorem two_core_L₂ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) :
    yamadaL₂ d t ≤ centralizer (d.Y : Set G) ∧
      yamadaL₂ d t ⊓ centralizer ({t} : Set G) = d.M ⊔ zpowers t ∧
      (∀ y ∈ d.Y, ∃ x ∈ yamadaL₂ d t, x⁻¹ * t * x = t * y) ∧
      ∀ g ∈ normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G),
        ∃ c ∈ centralizer ({t} : Set G) ⊓ normalizer (d.Y : Set G), ∃ x ∈ yamadaL₂ d t,
          g = c * x := by
  have : Fintype K := Fintype.ofFinite K
  have hK4 : 4 ≤ Nat.card K := hK ▸ h.four_le
  obtain ⟨ι, ρ, hρ, hρι⟩ := d.exists_mulEquiv_Y
  have hc := h.cosetData_tY d hK
  have hHC := h.normalizer_tY_inf_centralizer d hK
  have htr : ∀ y ∈ d.Y, ∃ g ∈ normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G),
      g⁻¹ * t * g = t * y := by
    intro y hy
    have hmem : t * y ∈ (fun y => t * y) '' (d.Y : Set G) := ⟨y, hy, rfl⟩
    rw [← h.conj_tY d hK] at hmem
    obtain ⟨n, hn, hnt⟩ := hmem
    exact ⟨n⁻¹, inv_mem hn, by rw [inv_inv]; exact hnt⟩
  have hA : d.leviB ≤ normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G) ⊓
      centralizer ({t} : Set G) := by
    rw [hHC]
    exact h.leviB_le_centralizer_inf_normalizer_Y d
  have hnat : ∀ g ∈ d.leviB, ∃ M : Matrix.SpecialLinearGroup (Fin 2) K, ∀ v : Fin 2 → K,
      g * (ι (Multiplicative.ofAdd v) : G) * g⁻¹ =
        ι (Multiplicative.ofAdd (Matrix.mulVec (M : Matrix (Fin 2) (Fin 2) K) v)) := by
    intro g hg
    rw [← hρ] at hg
    obtain ⟨M, rfl⟩ := hg
    exact ⟨M, hρι M⟩
  have hsurj : ∀ M : Matrix.SpecialLinearGroup (Fin 2) K, ∃ g ∈ d.leviB, ∀ v : Fin 2 → K,
      g * (ι (Multiplicative.ofAdd v) : G) * g⁻¹ =
        ι (Multiplicative.ofAdd (Matrix.mulVec (M : Matrix (Fin 2) (Fin 2) K) v)) := fun M =>
    ⟨ρ M, hρ ▸ ⟨M, rfl⟩, hρι M⟩
  have hBM : d.leviB ≤ normalizer (d.M : Set G) :=
    d.image_le_normalizer (Model.leviB_le_adjointGroup K) Model.M_le_adjointGroup
      Model.leviB_le_normalizer_M
  have hAn : ∀ x ∈ normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G) ⊓
      centralizer ({t} : Set G), ∀ g ∈ d.leviB, ∃ g' ∈ d.leviB, ∀ w ∈ d.Y,
        x * g * x⁻¹ * w * (x * g * x⁻¹)⁻¹ = g' * w * g'⁻¹ := by
    intro x hx g hg
    rw [hHC] at hx
    have hxLY : x ∈ normalizer ((L ⊓ normalizer (d.Y : Set G) : Subgroup G) : Set G) :=
      Common.mem_normalizer_inf (h.centralizer_le_normalizer hx.1) (le_normalizer hx.2)
    rw [(d.yamada_3_13_3_G).1, ← (d.yamada_3_13_3_G).2.2.1] at hxLY
    have hxD := normalizer_le_normalizer_commutator _ hxLY
    rw [(d.yamada_3_13_4_G hK4).2.2.1] at hxD
    have h1 : x * g * x⁻¹ ∈ d.M ⊔ d.leviB := (mem_normalizer_iff.1 hxD g).1 (mem_sup_right hg)
    obtain ⟨m, hm, g', hg', he⟩ := Common.exists_mul_of_le_normalizer hBM _ h1
    refine ⟨g', hg', fun w hw => ?_⟩
    rw [he]
    have hgw : g' * w * g'⁻¹ ∈ d.Y :=
      (mem_normalizer_iff.1 (h.leviB_le_centralizer_inf_normalizer_Y d hg').2 w).1 hw
    have hmc : g' * w * g'⁻¹ * m = m * (g' * w * g'⁻¹) :=
      mem_centralizer_iff.1 (h.M_le_centralizer_Y d hm) _ hgw
    calc m * g' * w * (m * g')⁻¹ = m * (g' * w * g'⁻¹) * m⁻¹ := by group
      _ = g' * w * g'⁻¹ := by rw [← hmc, mul_inv_cancel_right]
  have hmax : ∀ R : Subgroup G, R ≤ normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G) ⊓
      centralizer ({t} : Set G) → normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G) ⊓
        centralizer ({t} : Set G) ≤ normalizer (R : Set G) → IsPGroup 2 R →
          R ≤ d.M ⊔ zpowers t := by
    intro R hR hN hp
    rw [hHC] at hR hN
    exact h.le_sup_of_pCoreOf d (h.pCoreOf_range_act d hK).2 hR hN hp
  have hAK : ∀ a ∈ d.leviB, ∀ k ∈ normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G) ⊓
      centralizer (d.Y : Set G) ⊓ centralizer ({t} : Set G),
        a * k * a⁻¹ * k⁻¹ ∈ d.M ⊔ zpowers t := by
    intro a ha k hk
    obtain ⟨l, hl, c, hc, rfl⟩ := h.exists_mul_of_mem_centralizer_Y d hK ⟨hk.2, hk.1.2⟩
    obtain ⟨a₀, ha₀, rfl⟩ := d.mem_image.1 ha
    obtain ⟨g₀, hg₀, rfl⟩ := d.mem_image.1 hl
    have haC := h.L_le_centralizer (d.emb_mem a₀)
    have hca : c * (d.emb a₀)⁻¹ = (d.emb a₀)⁻¹ * c :=
      ((Commute.inv_left (commute_of_mem_zpowers hc haC : Commute (d.emb a₀) c)).eq).symm
    have e : d.emb a₀ * (d.emb g₀ * c) * (d.emb a₀)⁻¹ * (d.emb g₀ * c)⁻¹ =
        d.emb (a₀ * g₀ * a₀⁻¹ * g₀⁻¹) := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      calc d.emb a₀ * (d.emb g₀ * c) * (d.emb a₀)⁻¹ * (d.emb g₀ * c)⁻¹ =
          d.emb a₀ * d.emb g₀ * (c * (d.emb a₀)⁻¹) * c⁻¹ * (d.emb g₀)⁻¹ := by group
        _ = d.emb a₀ * d.emb g₀ * ((d.emb a₀)⁻¹ * c) * c⁻¹ * (d.emb g₀)⁻¹ := by rw [hca]
        _ = d.emb a₀ * d.emb g₀ * (d.emb a₀)⁻¹ * (d.emb g₀)⁻¹ := by group
    rw [e]
    refine mem_sup_left (d.emb_mem_image ?_)
    simp only [coe_mul, coe_inv]
    exact Model.commutator_leviB_mem_M ha₀ hg₀
  obtain ⟨h1, h2, h3, h4⟩ := hc.sl_two_core ι htr hA hnat hsurj hAn (h.isPGroup_tM d)
    (h.tM_le_kernel d) (h.normalizer_tY_le_normalizer_tM d hK) hmax hAK
  rw [yamadaL₂, pCoreOf_two_eq_oTwo]
  refine ⟨h1, h2, h3, fun g hg => ?_⟩
  obtain ⟨c, hc', x, hx, rfl⟩ := h4 g hg
  rw [hHC] at hc'
  exact ⟨c, hc', x, hx, rfl⟩

theorem yamada_5_5_1 (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) :
    normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G) =
        normalizer ((d.M ⊔ zpowers t : Subgroup G) : Set G) ∧
      normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G) =
        yamadaL₂ d t ⊔ (centralizer ({t} : Set G) ⊓ normalizer (d.Y : Set G)) ∧
      ((normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G) : Subgroup G) : Set G) =
        (yamadaL₂ d t : Set G) *
          ((centralizer ({t} : Set G) ⊓ normalizer (d.Y : Set G) : Subgroup G) : Set G) ∧
      yamadaL₂ d t ⊓ centralizer ({t} : Set G) = d.M ⊔ zpowers t := by
  obtain ⟨-, h2, -, h4⟩ := h.two_core_L₂ d hK
  have hZ : (d.M ⊔ zpowers t) ⊓ centralizer ((d.M ⊔ zpowers t : Subgroup G) : Set G) =
      d.Y ⊔ zpowers t := by
    rw [h.center_sup_zpowers (E := d.M) (d.image_le _), (d.yamada_3_12_centers).2.2.1]
  refine ⟨le_antisymm (h.normalizer_tY_le_normalizer_tM d hK) ?_, le_antisymm (fun g hg => ?_)
    (sup_le (yamadaL₂_le d t) (h.centralizer_inf_normalizer_Y_le d)), ?_, h2⟩
  · refine le_normalizer_of_conj_mem fun n hn x hx => ?_
    rw [← hZ] at hx ⊢
    obtain ⟨hxB, hxc⟩ := hx
    obtain ⟨h5, h6⟩ := conj_mem_center_of_mem_normalizer hn hxB fun r hr =>
      (mem_centralizer_iff.1 hxc r hr).symm
    exact ⟨h5, mem_centralizer_iff.2 fun r hr => (h6 r hr).symm⟩
  · obtain ⟨c, hc, x, hx, rfl⟩ := h4 g hg
    exact mul_mem (mem_sup_right hc) (mem_sup_left hx)
  · ext g
    constructor
    · intro hg
      obtain ⟨c, hc, x, hx, rfl⟩ := h4 g hg
      exact ⟨c * x * c⁻¹, (mem_normalizer_iff.1 (le_normalizer_yamadaL₂ d t
        (h.centralizer_inf_normalizer_Y_le d hc)) x).1 hx, c, hc, by group⟩
    · rintro ⟨x, hx, c, hc, rfl⟩
      exact mul_mem (yamadaL₂_le d t hx) (h.centralizer_inf_normalizer_Y_le d hc)

theorem yamada_5_5_2 (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) :
    {x | ∃ c ∈ yamadaL₂ d t, c * t * c⁻¹ = x} = (fun y => t * y) '' (d.Y : Set G) := by
  obtain ⟨-, -, h3, -⟩ := h.two_core_L₂ d hK
  ext x
  constructor
  · rintro ⟨c, hc, rfl⟩
    rw [← h.conj_tY d hK]
    exact ⟨c, yamadaL₂_le d t hc, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨c, hc, hct⟩ := h3 y hy
    exact ⟨c⁻¹, inv_mem hc, by rw [inv_inv]; exact hct⟩

theorem yamada_5_5_3 (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) :
    ∃ _ : ((d.M ⊔ zpowers t).subgroupOf (yamadaL₂ d t)).Normal,
      ∃ φ : yamadaL₂ d t ⧸ (d.M ⊔ zpowers t).subgroupOf (yamadaL₂ d t) ≃* d.Y,
        (∀ x : yamadaL₂ d t, (φ (QuotientGroup.mk x) : G) = t * (x : G)⁻¹ * t * x) ∧
        ∀ c ∈ centralizer ({t} : Set G) ⊓ normalizer (d.Y : Set G), ∀ x : yamadaL₂ d t,
          ∃ hx : c * x * c⁻¹ ∈ yamadaL₂ d t,
            (φ (QuotientGroup.mk ⟨c * x * c⁻¹, hx⟩) : G) = c * φ (QuotientGroup.mk x) * c⁻¹ := by
  obtain ⟨h1, h2, h3, -⟩ := h.two_core_L₂ d hK
  have hc := h.cosetData_tY d hK
  have hN := hc.normal_subgroupOf (yamadaL₂_le d t) h1 h2
  obtain ⟨φ, hφ1, hφ2⟩ := hc.exists_mulEquiv_quotient (yamadaL₂_le d t) h1 h2 h3
  refine ⟨hN, φ, fun x => ?_, fun c hc' x => ?_⟩
  · rw [hφ1]
    have hy := hc.crossed_mem_of_mem ⟨yamadaL₂_le d t x.2, h1 x.2⟩
    have hyt := hc.comm_of_mem hy
    symm
    calc t * (x : G)⁻¹ * t * x = t * ((x : G)⁻¹ * t * x * t) * t⁻¹ := by group
      _ = (x : G)⁻¹ * t * x * t := by rw [hyt, mul_inv_cancel_right]
  · have hcH : c ∈ normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G) ⊓
        centralizer ({t} : Set G) := by
      rw [h.normalizer_tY_inf_centralizer d hK]
      exact hc'
    have hx : c * x * c⁻¹ ∈ yamadaL₂ d t :=
      (mem_normalizer_iff.1 (le_normalizer_yamadaL₂ d t hcH.1) x).1 x.2
    exact ⟨hx, hφ2 c hcH x hx⟩

theorem yamada_5_5_4 (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) :
    yamadaL₂ d t ⊓ centralizer (yamadaL₂ d t : Set G) = d.Y ∧
      yamadaR₂ d t ⊓ centralizer (yamadaR₂ d t : Set G) = d.U := by
  obtain ⟨h1, h2, h3, -⟩ := h.two_core_L₂ d hK
  obtain ⟨hUY, hYX, -, hXF, -, -, hFM, -, hMS, -⟩ := d.inclusions
  have hYM : d.Y ≤ d.M := hYX.trans (hXF.trans hFM)
  have hBL₂ : d.M ⊔ zpowers t ≤ yamadaL₂ d t := by
    rw [← h2]
    exact inf_le_left
  have hYL₂ : d.Y ≤ yamadaL₂ d t := (hYM.trans le_sup_left).trans hBL₂
  have htL₂ : t ∈ yamadaL₂ d t := hBL₂ (mem_sup_right (mem_zpowers t))
  have hSU : d.S ≤ centralizer (d.U : Set G) := by
    rw [Subgroup.le_centralizer_iff, ← (d.yamada_3_12_centers).1]
    exact inf_le_right
  have hL₂U : yamadaL₂ d t ≤ centralizer (d.U : Set G) := h1.trans (centralizer_le hUY)
  have hR₂U : yamadaR₂ d t ≤ centralizer (d.U : Set G) := sup_le hL₂U hSU
  obtain ⟨-, -, -, hcU, hc1, -⟩ := d.xv_xc_spec
  obtain ⟨x₀, hx₀, hx₀t⟩ := h3 d.xc (hUY hcU)
  have hx₀' : x₀ * t ≠ t * x₀ := fun e => hc1 (by
    have e' : x₀⁻¹ * t * x₀ = t := by rw [mul_assoc, ← e, inv_mul_cancel_left]
    rw [e'] at hx₀t
    exact (mul_eq_left.1 hx₀t.symm))
  have hZ : (d.M ⊔ zpowers t) ⊓ centralizer ((d.M ⊔ zpowers t : Subgroup G) : Set G) =
      d.Y ⊔ zpowers t := by
    rw [h.center_sup_zpowers (E := d.M) (d.image_le _), (d.yamada_3_12_centers).2.2.1]
  constructor
  · refine le_antisymm (fun z hz => ?_)
      (le_inf hYL₂ (by rw [Subgroup.le_centralizer_iff]; exact h1))
    obtain ⟨hzL₂, hzc⟩ := hz
    have hzt : z ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.2
      (mem_centralizer_iff.1 hzc t htL₂).symm
    have hzB : z ∈ d.M ⊔ zpowers t := by
      rw [← h2]
      exact ⟨hzL₂, hzt⟩
    have hzZ : z ∈ d.Y ⊔ zpowers t := by
      rw [← hZ]
      exact ⟨hzB, mem_centralizer_iff.2 fun b hb => mem_centralizer_iff.1 hzc b (hBL₂ hb)⟩
    exact h.mem_of_mem_sup_zpowers (d.image_le _) h1 hx₀ hx₀' hzZ hzc
  · refine le_antisymm (fun z hz => ?_) (le_inf ((hUY.trans hYL₂).trans le_sup_left)
      (by rw [Subgroup.le_centralizer_iff]; exact hR₂U))
    obtain ⟨hzR₂, hzc⟩ := hz
    have hzt : z ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.2
      (mem_centralizer_iff.1 hzc t (mem_sup_left htL₂)).symm
    have hSN : d.S ≤ normalizer (yamadaL₂ d t : Set G) := fun s hs =>
      le_normalizer_yamadaL₂ d t (h.centralizer_inf_normalizer_Y_le d
        ⟨h.S_le_centralizer d hs, d.S_le_normalizers.2.1 hs⟩)
    obtain ⟨x, hx, s, hs, rfl⟩ := Common.exists_mul_of_le_normalizer hSN z hzR₂
    have hsC := h.S_le_centralizer d hs
    have hxC : x ∈ centralizer ({t} : Set G) := by
      have := mul_mem hzt (inv_mem hsC)
      rwa [mul_inv_cancel_right] at this
    have hxR : x ∈ yamadaR d t := by
      have hxB : x ∈ d.M ⊔ zpowers t := by
        rw [← h2]
        exact ⟨hx, hxC⟩
      rw [h.yamadaR_eq d]
      exact sup_le_sup_right hMS _ hxB
    have hRR₂ : yamadaR d t ≤ yamadaR₂ d t := by
      rw [h.yamadaR_eq d]
      exact sup_le le_sup_right ((zpowers_le).2 (mem_sup_left htL₂))
    have hzZ : x * s ∈ d.U ⊔ zpowers t := by
      rw [← h.center_yamadaR d]
      refine ⟨mul_mem hxR ((h.yamadaR_eq d).ge (mem_sup_left hs)), mem_centralizer_iff.2
        fun r hr => mem_centralizer_iff.1 hzc r (hRR₂ hr)⟩
    exact h.mem_of_mem_sup_zpowers (d.image_le _) hR₂U (mem_sup_left hx₀) hx₀' hzZ hzc

end Local

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
