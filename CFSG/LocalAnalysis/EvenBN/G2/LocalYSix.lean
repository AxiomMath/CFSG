module

public import CFSG.LocalAnalysis.EvenBN.G2.LocalYFive

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.LocalAnalysis.EvenBN.Common (CosetData)
open scoped commutatorElement Pointwise

section Defs

variable
  {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]

@[expose] noncomputable def yamadaY₂ (d : G2Data L K) (t : G) : Subgroup G :=
  yamadaU₁ d t ⊔ (yamadaU₁ d t).map (MulAut.conj d.wb).toMonoidHom

@[expose] noncomputable def yamadaM₂ (d : G2Data L K) (t : G) : Subgroup G :=
  d.M ⊔ yamadaY₂ d t

@[expose] noncomputable def yamadaS₂ (d : G2Data L K) (t : G) : Subgroup G :=
  d.S ⊔ yamadaY₂ d t

end Defs

section Generic

variable {G : Type*} [Group G]

theorem normalizer_le_normalizer_thompsonSubgroup [Finite G] (H : Subgroup G) :
    normalizer (H : Set G) ≤ normalizer (CFSG.Open.thompsonSubgroup H : Set G) := by
  intro g hg
  refine mem_normalizer_of_conj_mem fun x hx => ?_
  have hle : CFSG.Open.thompsonSubgroup H ≤
      (CFSG.Open.thompsonSubgroup H).comap (MulAut.conj g).toMonoidHom := by
    conv_lhs => rw [CFSG.Open.thompsonSubgroup_eq_iSup]
    refine iSup_le fun A => iSup_le fun hAH => iSup_le fun hAc => iSup_le fun hAm => ?_
    intro a ha
    rw [mem_comap]
    have hAg : A.map (MulAut.conj g).toMonoidHom ≤ H := by
      rintro _ ⟨y, hy, rfl⟩
      exact (mem_normalizer_iff.1 hg y).1 (hAH hy)
    have hAgc : IsMulCommutative (A.map (MulAut.conj g).toMonoidHom) := by
      have := hAc
      infer_instance
    have hAgm : ∀ B : Subgroup G, B ≤ H → IsMulCommutative B →
        Nat.card B ≤ Nat.card (A.map (MulAut.conj g).toMonoidHom) := fun B hB hBc => by
      rw [card_map_conj]
      exact hAm B hB hBc
    have hJ : A.map (MulAut.conj g).toMonoidHom ≤ CFSG.Open.thompsonSubgroup H := by
      rw [CFSG.Open.thompsonSubgroup_eq_iSup]
      exact le_iSup_of_le (A.map (MulAut.conj g).toMonoidHom) (le_iSup_of_le hAg
        (le_iSup_of_le hAgc (le_iSup_of_le hAgm le_rfl)))
    exact hJ ⟨a, ha, rfl⟩
  have := hle hx
  rwa [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this

theorem map_conj_le_normalizer_map_conj [Finite G] {P H : Subgroup G}
    (hP : P ≤ normalizer (H : Set G)) (g : G) :
    P.map (MulAut.conj g).toMonoidHom ≤
      normalizer ((H.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  rintro _ ⟨p, hp, rfl⟩
  refine mem_normalizer_of_conj_mem fun y hy => ?_
  obtain ⟨x, hx, rfl⟩ := hy
  refine ⟨p * x * p⁻¹, (mem_normalizer_iff.1 (hP hp) x).1 hx, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

end Generic

namespace Model

variable
  {K : Type} [Field K] [CharP K 2]

theorem M_le_sup_conj : M K ≤ W K ⊔ X K ⊔ (X K).map (MulAut.conj (wb K)).toMonoidHom := by
  intro g hg
  obtain ⟨A, C, D, E, F, rfl⟩ := mem_M.1 hg
  have h : g2N A 0 C D E F = g2N A 0 0 0 0 0 * g2N 0 0 C 0 0 0 * g2N 0 0 0 D E F := by
    rw [g2N_mul_coords, g2N_mul_coords]
    refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_ <;> ring
  rw [h]
  exact mul_mem (mul_mem (mem_sup_right mem_map_wb_X) (mem_sup_left (mem_sup_right
    (g2N_mem_X_iff.2 ⟨rfl, rfl, rfl⟩)))) (mem_sup_left (mem_sup_left
      (g2N_mem_W_iff.2 ⟨rfl, rfl, rfl⟩)))

end Model

namespace G2Data

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] (d : G2Data L K)

section Light

theorem J₅_le_J : d.J₅ ≤ d.J := d.image_mono inf_le_left

theorem card_J₅ [Finite K] : Nat.card d.J₅ = Nat.card K - 1 := by
  rw [G2Data.J₅, d.card_image (Model.torusFix_le_adjointGroup K g2b)]
  exact (Model.yamada_3_9_1 (K := K) 4).2

end Light

variable
  [Finite K] [CharP K 2]

omit [Finite K] in
theorem J_le_inf_normalizer_U [Finite G] : d.J ≤ L ⊓ normalizer (d.U : Set G) := by
  intro j hj
  have hj' : j ∈ L ⊓ normalizer (d.S : Set G) := by
    rw [(d.yamada_3_13_1_G).2.2]
    exact mem_sup_left hj
  refine ⟨hj'.1, ?_⟩
  have := normalizer_le_normalizer_center d.S hj'.2
  rwa [(d.yamada_3_12_centers).1] at this

omit [CharP K 2] in
theorem S_inf_centralizer_J₅ (h8 : 8 ≤ Nat.card K) :
    d.S ⊓ centralizer (d.J₅ : Set G) = d.rootGroup g2b := by
  have h1 : Model.S K ⊓ centralizer (Model.J₅ K : Set (ModGL .G2 K)) =
      rootSubgroup .G2 K g2b := Model.S_inf_centralizer_Ji (by omega) 4 (Or.inl h8)
  rw [G2Data.S, G2Data.J₅, ← d.image_inf_centralizer _ (Model.torusFix_le_adjointGroup K g2b), h1]
  rfl

omit [Finite K] in
theorem M_le_sup_conj : d.M ≤ d.W ⊔ d.X ⊔ d.X.map (MulAut.conj d.wb).toMonoidHom := by
  have hXw : (Model.X K).map (MulAut.conj (Model.wb K)).toMonoidHom ≤ adjointGroup .G2 K :=
    Model.map_wb_X_le_S.trans (Model.S_le_adjointGroup K)
  rw [← d.image_conj.2, G2Data.W, G2Data.X,
    ← d.image_sup Model.W_le_adjointGroup Model.X_le_adjointGroup,
    ← d.image_sup (sup_le Model.W_le_adjointGroup Model.X_le_adjointGroup) hXw]
  exact d.image_mono Model.M_le_sup_conj

end G2Data

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Local

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem yamadaR₂_le_normalizer_yamadaU₁ (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaR₂ d t ≤ normalizer (yamadaU₁ d t : Set G) := by
  have hC₁ : yamadaR₂ d t ≤ normalizer (yamadaC₁ d t : Set G) := by
    have := (h.yamada_5_11_4 d hK hD).2
    have h1 := LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      ((yamadaC₁ d t).subgroupOf (yamadaR₁ d t))
    have hC₁R₁ : yamadaC₁ d t ≤ yamadaR₁ d t := le_sup_left
    rw [map_subgroupOf_eq_of_le hC₁R₁] at h1
    exact (h.yamada_5_6_1 d hK).2.2.1.trans h1
  have h2 := normalizer_le_normalizer_thompsonSubgroup (yamadaC₁ d t)
  rw [h.yamada_5_11_2 d hK hD] at h2
  have h3 := normalizer_le_normalizer_center (yamadaD₁ d t)
  rw [← (hD.yamada_5_10_3).1] at h3
  exact hC₁.trans (h2.trans h3)

theorem wb_mem_normalizer_yamadaL₂ (h : Setup G L f t) (d : G2Data L K) :
    d.wb ∈ normalizer (yamadaL₂ d t : Set G) :=
  le_normalizer_yamadaL₂ d t (h.centralizer_inf_normalizer_Y_le d
    ⟨h.L_le_centralizer d.wb_mem_normalizer.1.1, d.wb_mem_normalizer.1.2⟩)

theorem yamadaU₁_le_yamadaC₁ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : yamadaU₁ d t ≤ yamadaC₁ d t :=
  (hD.spec).1.trans (h.yamadaD₁_le_yamadaC₁ d hK)

omit [Finite K] in
theorem yamadaU₁_le_yamadaL₂ (h : Setup G L f t) (d : G2Data L K) (_hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : yamadaU₁ d t ≤ yamadaL₂ d t :=
  fun _ hx => ((hD.yamada_5_10_3).2 hx).1.1

theorem map_wb_yamadaU₁_le_yamadaL₂ (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    (yamadaU₁ d t).map (MulAut.conj d.wb).toMonoidHom ≤ yamadaL₂ d t :=
  (map_mono (h.yamadaU₁_le_yamadaL₂ d hK hD)).trans
    (map_conj_eq_of_mem_normalizer (h.wb_mem_normalizer_yamadaL₂ d)).le

theorem yamadaL₂_le_normalizer_map_wb (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaL₂ d t ≤
      normalizer ((yamadaU₁ d t).map (MulAut.conj d.wb).toMonoidHom : Set G) := by
  have h1 := map_conj_le_normalizer_map_conj ((le_sup_left : yamadaL₂ d t ≤ yamadaR₂ d t).trans
    (h.yamadaR₂_le_normalizer_yamadaU₁ d hK hD)) d.wb
  rwa [map_conj_eq_of_mem_normalizer (h.wb_mem_normalizer_yamadaL₂ d)] at h1

theorem crossed_mem_of_mem_yamadaU₁ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) {x : G} (hx : x ∈ yamadaU₁ d t) :
    x⁻¹ * t * x * t ∈ d.U ∧
      (d.wb * x * d.wb⁻¹)⁻¹ * t * (d.wb * x * d.wb⁻¹) * t =
        d.wb * (x⁻¹ * t * x * t) * d.wb⁻¹ :=
  ⟨(h.cosetData_tU d hK).crossed_mem x (yamadaC₁_le d t (h.yamadaU₁_le_yamadaC₁ d hK hD hx)),
    CFSG.EvenSmallLie.UnitarySix.YamadaD.crossed_conj
      (mem_centralizer_singleton_iff.1 (h.L_le_centralizer d.wb_mem_normalizer.1.1))⟩

theorem yamadaU₁_inf_map_wb (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) :
    yamadaU₁ d t ⊓ (yamadaU₁ d t).map (MulAut.conj d.wb).toMonoidHom = ⊥ := by
  have hU := hD.inf_centralizer
  have hct : ∀ {x : G}, x ∈ yamadaU₁ d t → x⁻¹ * t * x * t = 1 → x ∈ d.U := fun {x} hx e => by
    rw [← hU]
    refine ⟨hx, mem_centralizer_singleton_iff.2 ?_⟩
    calc x * t = x * (x⁻¹ * t * x * t) * t := by rw [e, mul_one]
      _ = t * x * (t * t) := by group
      _ = t * x := by rw [h.t_mul_t, mul_one]
  refine le_bot_iff.1 fun x hx => ?_
  obtain ⟨hx₁, ⟨u, hu, rfl⟩⟩ := Subgroup.mem_inf.1 hx
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hx₁ ⊢
  obtain ⟨h1, -⟩ := h.crossed_mem_of_mem_yamadaU₁ d hK hD hx₁
  obtain ⟨h2, e2⟩ := h.crossed_mem_of_mem_yamadaU₁ d hK hD hu
  rw [e2] at h1
  have e3 := d.eq_one_of_wb_conj_mem_U h2 h1
  have huU := hct hu e3
  rw [e3, mul_one, mul_inv_cancel] at e2
  have hwU := hct hx₁ e2
  rw [d.eq_one_of_wb_conj_mem_U huU hwU, mul_one, mul_inv_cancel]
  exact one_mem _

omit [Finite K] in
theorem mem_U_of_crossed_eq_one (h : Setup G L f t) (d : G2Data L K) (_hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) {x : G} (hx : x ∈ yamadaU₁ d t)
    (e : x⁻¹ * t * x * t = 1) : x ∈ d.U := by
  rw [← hD.inf_centralizer]
  refine ⟨hx, mem_centralizer_singleton_iff.2 ?_⟩
  calc x * t = x * (x⁻¹ * t * x * t) * t := by rw [e, mul_one]
    _ = t * x * (t * t) := by group
    _ = t * x := by rw [h.t_mul_t, mul_one]

theorem map_wb_yamadaU₁_le_centralizer (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    (yamadaU₁ d t).map (MulAut.conj d.wb).toMonoidHom ≤ centralizer (yamadaU₁ d t : Set G) := by
  intro v hv
  rw [mem_centralizer_iff]
  intro u hu
  have hL₂R₂ : yamadaL₂ d t ≤ yamadaR₂ d t := le_sup_left
  have hvN := h.yamadaR₂_le_normalizer_yamadaU₁ d hK hD
    (hL₂R₂ (h.map_wb_yamadaU₁_le_yamadaL₂ d hK hD hv))
  have huN := h.yamadaL₂_le_normalizer_map_wb d hK hD (h.yamadaU₁_le_yamadaL₂ d hK hD hu)
  have h1 : u * v * u⁻¹ * v⁻¹ ∈ (yamadaU₁ d t).map (MulAut.conj d.wb).toMonoidHom :=
    mul_mem ((mem_normalizer_iff.1 huN v).1 hv) (inv_mem hv)
  have h2 : u * v * u⁻¹ * v⁻¹ ∈ yamadaU₁ d t := by
    rw [show u * v * u⁻¹ * v⁻¹ = u * (v * u⁻¹ * v⁻¹) by group]
    exact mul_mem hu ((mem_normalizer_iff.1 hvN u⁻¹).1 (inv_mem hu))
  have h3 : u * v * u⁻¹ * v⁻¹ ∈ (⊥ : Subgroup G) := by
    rw [← h.yamadaU₁_inf_map_wb d hK hD]
    exact Subgroup.mem_inf.2 ⟨h2, h1⟩
  rw [mem_bot] at h3
  calc u * v = u * v * u⁻¹ * v⁻¹ * (v * u) := by group
    _ = v * u := by rw [h3, one_mul]

theorem map_wb_yamadaU₁_le_normalizer (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    (yamadaU₁ d t).map (MulAut.conj d.wb).toMonoidHom ≤ normalizer (yamadaU₁ d t : Set G) :=
  (h.map_wb_yamadaU₁_le_centralizer d hK hD).trans (Subgroup.centralizer_le_normalizer _)

theorem yamadaY₂_mul_comm (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) {x y : G} (hx : x ∈ yamadaY₂ d t) (hy : y ∈ yamadaY₂ d t) :
    x * y = y * x := by
  have : IsMulCommutative (yamadaU₁ d t) :=
    ⟨⟨fun a b => Subtype.ext (hD.mul_comm a.2 b.2)⟩⟩
  have hc : IsMulCommutative (yamadaY₂ d t) := isMulCommutative_sup fun a ha b hb =>
    mem_centralizer_iff.1 (h.map_wb_yamadaU₁_le_centralizer d hK hD hb) a ha
  exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : yamadaY₂ d t) ⟨y, hy⟩)

omit [Finite G] [Finite K] in
theorem yamadaU₁_le_yamadaY₂ (d : G2Data L K) (t : G) : yamadaU₁ d t ≤ yamadaY₂ d t :=
  le_sup_left

theorem yamadaL₂_le_normalizer_yamadaY₂ (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaL₂ d t ≤ normalizer (yamadaY₂ d t : Set G) := fun x hx => by
  have hL₂R₂ : yamadaL₂ d t ≤ yamadaR₂ d t := le_sup_left
  exact mem_normalizer_sup (h.yamadaR₂_le_normalizer_yamadaU₁ d hK hD (hL₂R₂ hx))
    (h.yamadaL₂_le_normalizer_map_wb d hK hD hx)

theorem yamadaY₂_le_yamadaL₂ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : yamadaY₂ d t ≤ yamadaL₂ d t :=
  sup_le (h.yamadaU₁_le_yamadaL₂ d hK hD) (h.map_wb_yamadaU₁_le_yamadaL₂ d hK hD)

theorem yamadaY₂_inf_centralizer (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : yamadaY₂ d t ⊓ centralizer ({t} : Set G) = d.Y := by
  obtain ⟨hL₂Y, -, -, -⟩ := h.two_core_L₂ d hK
  obtain ⟨hU₁D₁, hUU₁, -⟩ := hD.spec
  have hcY := h.cosetData_tY d hK
  have hwb := d.wb_mem_normalizer.1
  have hV : ∀ {g : G}, g ∈ yamadaL₂ d t → g ∈ normalizer ((d.Y ⊔ zpowers t : Subgroup G) :
      Set G) ⊓ centralizer (d.Y : Set G) := fun hg => ⟨yamadaL₂_le d t hg, hL₂Y hg⟩
  apply le_antisymm
  · intro y hy
    obtain ⟨hy₁, hy₂⟩ := Subgroup.mem_inf.1 hy
    obtain ⟨u, hu, v, hv, rfl⟩ := Common.exists_mul_of_le_normalizer
      (h.map_wb_yamadaU₁_le_normalizer d hK hD) y hy₁
    have hvL₂ := h.map_wb_yamadaU₁_le_yamadaL₂ d hK hD hv
    have huL₂ := h.yamadaU₁_le_yamadaL₂ d hK hD hu
    obtain ⟨u', hu', rfl⟩ := hv
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hy₂ hvL₂ ⊢
    have h0 : (u * (d.wb * u' * d.wb⁻¹))⁻¹ * t * (u * (d.wb * u' * d.wb⁻¹)) * t = 1 := by
      have hyt := mem_centralizer_singleton_iff.1 hy₂
      calc (u * (d.wb * u' * d.wb⁻¹))⁻¹ * t * (u * (d.wb * u' * d.wb⁻¹)) * t =
          (u * (d.wb * u' * d.wb⁻¹))⁻¹ * t * ((u * (d.wb * u' * d.wb⁻¹)) * t) := by group
        _ = (u * (d.wb * u' * d.wb⁻¹))⁻¹ * t * (t * (u * (d.wb * u' * d.wb⁻¹))) := by rw [hyt]
        _ = (u * (d.wb * u' * d.wb⁻¹))⁻¹ * (t * t) * (u * (d.wb * u' * d.wb⁻¹)) := by group
        _ = 1 := by rw [h.t_mul_t, mul_one, inv_mul_cancel]
    rw [hcY.crossed_mul_of_mem (hV huL₂) (hV hvL₂)] at h0
    obtain ⟨h1, -⟩ := h.crossed_mem_of_mem_yamadaU₁ d hK hD hu
    obtain ⟨h2, e2⟩ := h.crossed_mem_of_mem_yamadaU₁ d hK hD hu'
    rw [e2] at h0
    have h3 : d.wb * (u'⁻¹ * t * u' * t) * d.wb⁻¹ = (u⁻¹ * t * u * t)⁻¹ :=
      eq_inv_of_mul_eq_one_right h0
    have h4 : u'⁻¹ * t * u' * t = 1 := d.eq_one_of_wb_conj_mem_U h2 (by rw [h3]; exact inv_mem h1)
    rw [h4, mul_one, mul_inv_cancel] at h3
    have huU := h.mem_U_of_crossed_eq_one d hK hD hu (inv_eq_one.1 h3.symm)
    have hu'U := h.mem_U_of_crossed_eq_one d hK hD hu' h4
    obtain ⟨hUY, -⟩ := d.inclusions
    refine mul_mem (hUY huU) ?_
    have := (mem_normalizer_iff.1 hwb.2 u').1 (hUY hu'U)
    exact this
  · intro y hy
    refine ⟨?_, (d.image_le _ |>.trans h.L_le_centralizer) hy⟩
    obtain ⟨u, hu, v, hv, rfl⟩ := d.exists_wb_conj_mul hy
    exact mul_mem (mem_sup_right ⟨v, hUU₁ hv, rfl⟩) (mem_sup_left (hUU₁ hu))

theorem Y_le_yamadaY₂ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : d.Y ≤ yamadaY₂ d t := by
  rw [← h.yamadaY₂_inf_centralizer d hK hD]
  exact inf_le_left

theorem M_le_centralizer_yamadaY₂ (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    d.M ≤ centralizer (yamadaY₂ d t : Set G) := by
  have hMU₁ : d.M ≤ centralizer (yamadaU₁ d t : Set G) :=
    d.inclusions.2.2.2.2.2.2.2.2.1.trans (h.S_le_centralizer_yamadaU₁ d hK hD)
  have hwb := d.wb_mem_normalizer.2.2
  rw [← Subgroup.le_centralizer_iff]
  refine sup_le ?_ ?_
  · rw [Subgroup.le_centralizer_iff]
    exact hMU₁
  · rintro _ ⟨u, hu, rfl⟩
    rw [mem_centralizer_iff]
    intro m hm
    have hm' : d.wb⁻¹ * m * d.wb ∈ d.M := by
      have := (mem_normalizer_iff.1 (inv_mem hwb) m).1 hm
      rwa [inv_inv] at this
    have e := mem_centralizer_iff.1 (hMU₁ hm') u hu
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc m * (d.wb * u * d.wb⁻¹) = d.wb * ((d.wb⁻¹ * m * d.wb) * u) * d.wb⁻¹ := by group
      _ = d.wb * (u * (d.wb⁻¹ * m * d.wb)) * d.wb⁻¹ := by rw [e]
      _ = d.wb * u * d.wb⁻¹ * m := by group

theorem yamadaY₂_le_normalizer_M (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaY₂ d t ≤ normalizer (d.M : Set G) := fun y hy =>
  Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun _ hm =>
    (mem_centralizer_iff.1 (h.M_le_centralizer_yamadaY₂ d hK hD hm) y hy).symm)

theorem yamadaM₂_center (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) :
    yamadaM₂ d t ⊓ centralizer (yamadaM₂ d t : Set G) = yamadaY₂ d t := by
  have hMY₂ := h.M_le_centralizer_yamadaY₂ d hK hD
  have hY₂c : yamadaY₂ d t ≤ centralizer (yamadaY₂ d t : Set G) := fun y hy =>
    mem_centralizer_iff.2 fun y' hy' => h.yamadaY₂_mul_comm d hK hD hy' hy
  apply le_antisymm
  · intro z hz
    obtain ⟨hz₁, hz₂⟩ := Subgroup.mem_inf.1 hz
    obtain ⟨m, hm, y, hy, rfl⟩ := Common.exists_mul_of_le_normalizer
      (h.yamadaY₂_le_normalizer_M d hK hD) z hz₁
    have hmZ : m ∈ d.M ⊓ centralizer (d.M : Set G) := by
      refine ⟨hm, mem_centralizer_iff.2 fun w hw => ?_⟩
      have h1 := mem_centralizer_iff.1 hz₂ w (mem_sup_left hw)
      have h2 := mem_centralizer_iff.1 (hMY₂ hw) y hy
      calc w * m = w * (m * y) * y⁻¹ := by group
        _ = m * y * w * y⁻¹ := by rw [h1]
        _ = m * (y * w) * y⁻¹ := by group
        _ = m * (w * y) * y⁻¹ := by rw [h2]
        _ = m * w := by group
    rw [(d.yamada_3_12_centers).2.2.1] at hmZ
    exact mul_mem (h.Y_le_yamadaY₂ d hK hD hmZ) hy
  · refine le_inf le_sup_right ?_
    rw [Subgroup.le_centralizer_iff]
    exact sup_le hMY₂ hY₂c

theorem card_yamadaY₂ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : Nat.card (yamadaY₂ d t) = Nat.card K ^ 4 := by
  have h1 := Common.card_sup_mul_card_inf_eq (h.map_wb_yamadaU₁_le_normalizer d hK hD)
  rw [h.yamadaU₁_inf_map_wb d hK hD, Subgroup.card_bot, mul_one, card_map_conj,
    (hD.yamada_5_10_1).2.2] at h1
  rw [yamadaY₂, h1]
  ring

theorem M_inf_yamadaY₂ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : d.M ⊓ yamadaY₂ d t = d.Y := by
  obtain ⟨-, hYX, -, hXF, -, -, hFM, -⟩ := d.inclusions
  apply le_antisymm
  · intro x hx
    rw [← h.yamadaY₂_inf_centralizer d hK hD]
    exact ⟨hx.2, h.L_le_centralizer (d.image_le _ hx.1)⟩
  · exact le_inf (hYX.trans (hXF.trans hFM)) (h.Y_le_yamadaY₂ d hK hD)

theorem card_yamadaM₂ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : Nat.card (yamadaM₂ d t) = Nat.card K ^ 7 := by
  have h4K : 4 ≤ Nat.card K := hK ▸ h.four_le
  have h1 := Common.card_sup_mul_card_inf_eq (h.yamadaY₂_le_normalizer_M d hK hD)
  rw [h.M_inf_yamadaY₂ d hK hD, h.card_yamadaY₂ d hK hD, d.cards.2.1, d.cards.2.2.2.2.2.2.1]
    at h1
  have hpos : 0 < Nat.card K ^ 2 := by positivity
  exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans (by ring))

theorem yamadaM₂_inf_centralizer (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaM₂ d t ⊓ centralizer ({t} : Set G) = d.M := by
  obtain ⟨-, hYX, -, hXF, -, -, hFM, -⟩ := d.inclusions
  have hMC : d.M ≤ centralizer ({t} : Set G) := (d.image_le _).trans h.L_le_centralizer
  apply le_antisymm
  · intro x hx
    obtain ⟨hx₁, hx₂⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨m, hm, y, hy, rfl⟩ := Common.exists_mul_of_le_normalizer
      (h.yamadaY₂_le_normalizer_M d hK hD) x hx₁
    have hyC : y ∈ centralizer ({t} : Set G) := by
      have := mul_mem (inv_mem (hMC hm)) hx₂
      rwa [inv_mul_cancel_left] at this
    have hyY : y ∈ d.Y := by
      rw [← h.yamadaY₂_inf_centralizer d hK hD]
      exact ⟨hy, hyC⟩
    exact mul_mem hm ((hYX.trans (hXF.trans hFM)) hyY)
  · exact le_inf le_sup_left hMC

theorem t_not_mem_yamadaM₂ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : t ∉ yamadaM₂ d t := fun ht => by
  refine h.t_not_mem_L (d.image_le (Model.M K) ?_)
  rw [← G2Data.M, ← h.yamadaM₂_inf_centralizer d hK hD]
  exact ⟨ht, h.t_mem_centralizer⟩

omit [Finite K] in
theorem card_tM (h : Setup G L f t) (d : G2Data L K) :
    Nat.card (d.M ⊔ zpowers t : Subgroup G) = 2 * Nat.card d.M := by
  have htN : zpowers t ≤ normalizer (d.M : Set G) := (zpowers_le).2
    (Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun m hm =>
      mem_centralizer_singleton_iff.1 (h.L_le_centralizer (d.image_le _ hm))))
  have h1 := Common.card_sup_mul_card_inf_eq htN
  rw [inf_comm, h.zpowers_inf_L (E := d.M) (d.image_le _), Subgroup.card_bot, mul_one,
    h.card_zpowers_t] at h1
  rw [h1, mul_comm]

theorem card_yamadaL₂ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) :
    Nat.card (yamadaL₂ d t) = 2 * Nat.card K ^ 7 := by
  obtain ⟨_, φ, -, -⟩ := h.yamada_5_5_3 d hK
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((d.M ⊔ zpowers t).subgroupOf (yamadaL₂ d t))
  rw [Nat.card_congr φ.toEquiv,
    Nat.card_congr (subgroupOfEquivOfLe (h.tM_le_yamadaL₂ d hK)).toEquiv] at h1
  rw [h1, d.cards.2.1, h.card_tM d, d.cards.2.2.2.2.2.2.1]
  ring

theorem yamadaL₂_le_normalizer_yamadaM₂ (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaL₂ d t ≤ normalizer (yamadaM₂ d t : Set G) := fun _ hx =>
  mem_normalizer_sup ((h.yamada_5_8_5 d hK).2 (yamadaL₂_le d t hx))
    (h.yamadaL₂_le_normalizer_yamadaY₂ d hK hD hx)

theorem yamadaM₂_le_yamadaL₂ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : yamadaM₂ d t ≤ yamadaL₂ d t :=
  sup_le (le_sup_left.trans (h.tM_le_yamadaL₂ d hK)) (h.yamadaY₂_le_yamadaL₂ d hK hD)

theorem yamadaL₂_eq_sup (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : yamadaL₂ d t = yamadaM₂ d t ⊔ zpowers t := by
  have htL₂ : t ∈ yamadaL₂ d t := h.tM_le_yamadaL₂ d hK (mem_sup_right (mem_zpowers t))
  have htN : zpowers t ≤ normalizer (yamadaM₂ d t : Set G) :=
    (zpowers_le).2 (h.yamadaL₂_le_normalizer_yamadaM₂ d hK hD htL₂)
  have hinf : yamadaM₂ d t ⊓ zpowers t = ⊥ := by
    refine le_bot_iff.1 fun x hx => ?_
    obtain ⟨hx₁, hx₂⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx₂
    rcases h.zpow_eq_one_or_eq k with hk | hk
    · rw [hk]
      exact one_mem _
    · rw [hk] at hx₁
      exact absurd hx₁ (h.t_not_mem_yamadaM₂ d hK hD)
  have h1 := Common.card_sup_mul_card_inf_eq htN
  rw [hinf, Subgroup.card_bot, mul_one, h.card_zpowers_t, h.card_yamadaM₂ d hK hD] at h1
  refine (Subgroup.eq_of_le_of_card_ge (sup_le (h.yamadaM₂_le_yamadaL₂ d hK hD)
    ((zpowers_le).2 htL₂)) ?_).symm
  rw [h1, h.card_yamadaL₂ d hK, mul_comm]

theorem yamada_5_13_1 (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) :
    (yamadaU₁ d t ⊓ (yamadaU₁ d t).map (MulAut.conj d.wb).toMonoidHom = ⊥ ∧
      (yamadaU₁ d t).map (MulAut.conj d.wb).toMonoidHom ≤ centralizer (yamadaU₁ d t : Set G)) ∧
    yamadaM₂ d t ⊓ centralizer (yamadaM₂ d t : Set G) = yamadaY₂ d t ∧
    yamadaY₂ d t ⊓ centralizer ({t} : Set G) = d.Y ∧
    yamadaL₂ d t = yamadaM₂ d t ⊔ zpowers t ∧ t ∉ yamadaM₂ d t :=
  ⟨⟨h.yamadaU₁_inf_map_wb d hK hD, h.map_wb_yamadaU₁_le_centralizer d hK hD⟩,
    h.yamadaM₂_center d hK hD, h.yamadaY₂_inf_centralizer d hK hD, h.yamadaL₂_eq_sup d hK hD,
    h.t_not_mem_yamadaM₂ d hK hD⟩

theorem card_le_of_le_yamadaM₂ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) {A : Subgroup G} (hAM : A ≤ yamadaM₂ d t)
    (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) : Nat.card A ≤ Nat.card K ^ 5 := by
  have hK4 : 4 ≤ Nat.card K := hK ▸ h.four_le
  obtain ⟨-, hYX, -, hXF, -, -, hFM, -⟩ := d.inclusions
  have hZ := h.yamadaM₂_center d hK hD
  have hY₂c : ∀ {x y : G}, x ∈ yamadaM₂ d t → y ∈ yamadaY₂ d t → x * y = y * x :=
    fun {x y} hx hy => by
      rw [← hZ] at hy
      exact mem_centralizer_iff.1 hy.2 x hx
  have hA'c : ∀ x ∈ A ⊔ yamadaY₂ d t, ∀ y ∈ A ⊔ yamadaY₂ d t, x * y = y * x := by
    have : IsMulCommutative A := ⟨⟨fun a b => Subtype.ext (hA a a.2 b b.2)⟩⟩
    have : IsMulCommutative (yamadaY₂ d t) :=
      ⟨⟨fun a b => Subtype.ext (h.yamadaY₂_mul_comm d hK hD a.2 b.2)⟩⟩
    have hc := isMulCommutative_sup (A := A) (B := yamadaY₂ d t) fun a ha b hb =>
      hY₂c (hAM ha) hb
    exact fun x hx y hy => congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : (A ⊔ yamadaY₂ d t :
      Subgroup G)) ⟨y, hy⟩)
  set A' := A ⊔ yamadaY₂ d t with hA'def
  set A'' := A' ⊓ d.M with hA''def
  have hA'M₂ : A' ≤ yamadaM₂ d t := sup_le hAM le_sup_right
  have hY₂A' : yamadaY₂ d t ≤ A' := le_sup_right
  have hle : A' ≤ A'' ⊔ yamadaY₂ d t := by
    intro x hx
    obtain ⟨m, hm, y, hy, rfl⟩ := Common.exists_mul_of_le_normalizer
      (h.yamadaY₂_le_normalizer_M d hK hD) x (hA'M₂ hx)
    have hmA' : m ∈ A' := by
      have := mul_mem hx (inv_mem (hY₂A' hy))
      rwa [mul_inv_cancel_right] at this
    exact mul_mem (mem_sup_left ⟨hmA', hm⟩) (mem_sup_right hy)
  have hN : yamadaY₂ d t ≤ normalizer (A'' : Set G) := fun y hy =>
    Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun x hx =>
      hA'c x hx.1 y (hY₂A' hy))
  have h1 := Common.card_sup_mul_card_inf_eq hN
  have h2 : Nat.card A'' ≤ Nat.card K ^ 3 :=
    d.yamada_3_17_4_G hK4 (Or.inr inf_le_right) fun x hx y hy => hA'c x hx.1 y hy.1
  have hYY₂ := h.Y_le_yamadaY₂ d hK hD
  have h3 : Nat.card d.Y ≤ Nat.card (A'' ⊓ yamadaY₂ d t : Subgroup G) :=
    Subgroup.card_le_of_le (le_inf (le_inf (hYY₂.trans hY₂A') (hYX.trans (hXF.trans hFM))) hYY₂)
  rw [d.cards.2.1] at h3
  have hpos : 0 < Nat.card K ^ 2 := by positivity
  have h4 : Nat.card A' * Nat.card K ^ 2 ≤ Nat.card K ^ 5 * Nat.card K ^ 2 := by
    calc Nat.card A' * Nat.card K ^ 2 ≤
        Nat.card (A'' ⊔ yamadaY₂ d t : Subgroup G) * Nat.card (A'' ⊓ yamadaY₂ d t : Subgroup G) :=
          Nat.mul_le_mul (Subgroup.card_le_of_le hle) h3
      _ = Nat.card A'' * Nat.card (yamadaY₂ d t) := h1
      _ ≤ Nat.card K ^ 3 * Nat.card K ^ 4 := by
          rw [h.card_yamadaY₂ d hK hD]
          exact Nat.mul_le_mul_right _ h2
      _ = Nat.card K ^ 5 * Nat.card K ^ 2 := by ring
  exact (Subgroup.card_le_of_le (le_sup_left : A ≤ A')).trans (Nat.le_of_mul_le_mul_right h4 hpos)

theorem card_le_of_not_le_yamadaM₂ (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) {B : Subgroup G}
    (hBL : B ≤ yamadaL₂ d t) (hB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hBM : ¬ B ≤ yamadaM₂ d t) : Nat.card B ≤ 2 * Nat.card K ^ 3 := by
  have hZ := h.yamadaM₂_center d hK hD
  have hY₂c : ∀ {x y : G}, x ∈ yamadaM₂ d t → y ∈ yamadaY₂ d t → x * y = y * x :=
    fun {x y} hx hy => by
      rw [← hZ] at hy
      exact mem_centralizer_iff.1 hy.2 x hx
  obtain ⟨b, hb, hbM⟩ := Set.not_subset.1 hBM
  have htL₂ : t ∈ yamadaL₂ d t := h.tM_le_yamadaL₂ d hK (mem_sup_right (mem_zpowers t))
  have htN : zpowers t ≤ normalizer (yamadaM₂ d t : Set G) :=
    (zpowers_le).2 (h.yamadaL₂_le_normalizer_yamadaM₂ d hK hD htL₂)
  have hbL := hBL hb
  rw [h.yamadaL₂_eq_sup d hK hD] at hbL
  obtain ⟨m, hm, τ, hτ, hbe⟩ := Common.exists_mul_of_le_normalizer htN b hbL
  have hτt : τ = t := by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hτ
    rcases h.zpow_eq_one_or_eq k with hk | hk
    · exfalso
      rw [hk, mul_one] at hbe
      exact hbM (hbe ▸ hm)
    · exact hk
  have hBY : B ⊓ yamadaY₂ d t ≤ d.Y := by
    intro x hx
    rw [← h.yamadaY₂_inf_centralizer d hK hD]
    refine ⟨hx.2, mem_centralizer_singleton_iff.2 ?_⟩
    have h1 : m * x = x * m := hY₂c hm hx.2
    have h2 : x * b = b * x := hB x hx.1 b hb
    have ht : t = m⁻¹ * b := by rw [hbe, hτt]; group
    have hxm : x * m⁻¹ = m⁻¹ * x := by
      calc x * m⁻¹ = m⁻¹ * (m * x) * m⁻¹ := by group
        _ = m⁻¹ * (x * m) * m⁻¹ := by rw [h1]
        _ = m⁻¹ * x := by group
    rw [ht]
    calc x * (m⁻¹ * b) = (x * m⁻¹) * b := by group
      _ = (m⁻¹ * x) * b := by rw [hxm]
      _ = m⁻¹ * (x * b) := by group
      _ = m⁻¹ * (b * x) := by rw [h2]
      _ = m⁻¹ * b * x := by group
  set B' := B ⊓ yamadaM₂ d t with hB'def
  have hN : yamadaY₂ d t ≤ normalizer (B' : Set G) := fun y hy =>
    Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun x hx => hY₂c hx.2 hy)
  have h1 := Common.card_sup_mul_card_inf_eq hN
  have h2 : Nat.card (B' ⊔ yamadaY₂ d t : Subgroup G) ≤ Nat.card K ^ 5 := by
    refine h.card_le_of_le_yamadaM₂ d hK hD (sup_le inf_le_right le_sup_right) ?_
    have : IsMulCommutative B' := ⟨⟨fun a b => Subtype.ext (hB a a.2.1 b b.2.1)⟩⟩
    have : IsMulCommutative (yamadaY₂ d t) :=
      ⟨⟨fun a b => Subtype.ext (h.yamadaY₂_mul_comm d hK hD a.2 b.2)⟩⟩
    have hc := isMulCommutative_sup (A := B') (B := yamadaY₂ d t) fun a ha b hb =>
      hY₂c ha.2 hb
    exact fun x hx y hy => congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : (B' ⊔ yamadaY₂ d t :
      Subgroup G)) ⟨y, hy⟩)
  have h3 : Nat.card (B' ⊓ yamadaY₂ d t : Subgroup G) ≤ Nat.card K ^ 2 := by
    rw [← d.cards.2.1]
    exact Subgroup.card_le_of_le ((inf_le_inf_right _ inf_le_left).trans hBY)
  have h4 : Nat.card B' * Nat.card (yamadaY₂ d t) ≤
      Nat.card K ^ 3 * Nat.card (yamadaY₂ d t) := by
    rw [← h1, h.card_yamadaY₂ d hK hD]
    calc Nat.card (B' ⊔ yamadaY₂ d t : Subgroup G) * Nat.card (B' ⊓ yamadaY₂ d t : Subgroup G) ≤
        Nat.card K ^ 5 * Nat.card K ^ 2 := Nat.mul_le_mul h2 h3
      _ = Nat.card K ^ 3 * Nat.card K ^ 4 := by ring
  have h5 := Nat.le_of_mul_le_mul_right h4 Nat.card_pos
  have h6 : Nat.card B ≤ 2 * Nat.card B' := by
    have hBN : B ≤ normalizer (yamadaM₂ d t : Set G) :=
      hBL.trans (h.yamadaL₂_le_normalizer_yamadaM₂ d hK hD)
    have h7 := Common.card_sup_mul_card_inf_eq hBN
    have h9 : Nat.card (yamadaM₂ d t ⊔ B : Subgroup G) ≤ 2 * Nat.card (yamadaM₂ d t) := by
      rw [h.card_yamadaM₂ d hK hD, ← h.card_yamadaL₂ d hK]
      exact Subgroup.card_le_of_le (sup_le (h.yamadaM₂_le_yamadaL₂ d hK hD) hBL)
    rw [inf_comm] at h7
    have hpos : 0 < Nat.card (yamadaM₂ d t) := Nat.card_pos
    refine Nat.le_of_mul_le_mul_left ?_ hpos
    calc Nat.card (yamadaM₂ d t) * Nat.card B =
        Nat.card (yamadaM₂ d t ⊔ B : Subgroup G) * Nat.card B' := h7.symm
      _ ≤ 2 * Nat.card (yamadaM₂ d t) * Nat.card B' := Nat.mul_le_mul_right _ h9
      _ = Nat.card (yamadaM₂ d t) * (2 * Nat.card B') := by ring
  calc Nat.card B ≤ 2 * Nat.card B' := h6
    _ ≤ 2 * Nat.card K ^ 3 := Nat.mul_le_mul_left _ h5

theorem exists_abelian_yamadaM₂ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) :
    ∃ A₁ A₂ A₃ : Subgroup G, A₁ ⊔ A₂ ⊔ A₃ = yamadaM₂ d t ∧
      (A₁ ≤ yamadaM₂ d t ∧ (∀ x ∈ A₁, ∀ y ∈ A₁, x * y = y * x) ∧
        Nat.card A₁ = Nat.card K ^ 5) ∧
      (A₂ ≤ yamadaM₂ d t ∧ (∀ x ∈ A₂, ∀ y ∈ A₂, x * y = y * x) ∧
        Nat.card A₂ = Nat.card K ^ 5) ∧
      (A₃ ≤ yamadaM₂ d t ∧ (∀ x ∈ A₃, ∀ y ∈ A₃, x * y = y * x) ∧
        Nat.card A₃ = Nat.card K ^ 5) := by
  have h4K : 4 ≤ Nat.card K := hK ▸ h.four_le
  obtain ⟨-, hYX, hYW, hXF, hWF, -, hFM, -⟩ := d.inclusions
  have hMY₂ := h.M_le_centralizer_yamadaY₂ d hK hD
  have hYY₂ := h.Y_le_yamadaY₂ d hK hD
  have key : ∀ E : Subgroup G, E ≤ d.M → d.Y ≤ E → CFSG.IsElementaryAbelian 2 E →
      Nat.card E = Nat.card K ^ 3 →
      E ⊔ yamadaY₂ d t ≤ yamadaM₂ d t ∧
        (∀ x ∈ E ⊔ yamadaY₂ d t, ∀ y ∈ E ⊔ yamadaY₂ d t, x * y = y * x) ∧
        Nat.card (E ⊔ yamadaY₂ d t : Subgroup G) = Nat.card K ^ 5 := by
    intro E hEM hYE hE hEc
    have : IsMulCommutative E := hE.toIsMulCommutative
    have : IsMulCommutative (yamadaY₂ d t) :=
      ⟨⟨fun a b => Subtype.ext (h.yamadaY₂_mul_comm d hK hD a.2 b.2)⟩⟩
    have hc := isMulCommutative_sup (A := E) (B := yamadaY₂ d t) fun a ha b hb =>
      (mem_centralizer_iff.1 (hMY₂ (hEM ha)) b hb).symm
    refine ⟨sup_le (hEM.trans le_sup_left) le_sup_right, fun x hx y hy => congrArg Subtype.val
      (mul_comm' (⟨x, hx⟩ : (E ⊔ yamadaY₂ d t : Subgroup G)) ⟨y, hy⟩), ?_⟩
    have hN : yamadaY₂ d t ≤ normalizer (E : Set G) := fun y hy =>
      Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun x hx =>
        (mem_centralizer_iff.1 (hMY₂ (hEM hx)) y hy).symm)
    have h1 := Common.card_sup_mul_card_inf_eq hN
    have hinf : E ⊓ yamadaY₂ d t = d.Y := le_antisymm
      (by rw [← h.M_inf_yamadaY₂ d hK hD]; exact inf_le_inf_right _ hEM) (le_inf hYE hYY₂)
    rw [hinf, d.cards.2.1, hEc, h.card_yamadaY₂ d hK hD] at h1
    have hpos : 0 < Nat.card K ^ 2 := by positivity
    exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans (by ring))
  have hwbM := d.wb_mem_normalizer.2.2
  have hwbY := d.wb_mem_normalizer.1.2
  have hXM : d.X ≤ d.M := hXF.trans hFM
  have hXwM : d.X.map (MulAut.conj d.wb).toMonoidHom ≤ d.M :=
    (map_mono hXM).trans (map_conj_eq_of_mem_normalizer hwbM).le
  have hYXw : d.Y ≤ d.X.map (MulAut.conj d.wb).toMonoidHom :=
    (map_conj_eq_of_mem_normalizer hwbY).symm.le.trans (map_mono hYX)
  obtain h₁ := key d.W (hWF.trans hFM) hYW d.isElementaryAbelian.2.2.2 d.cards.2.2.2.1
  obtain h₂ := key d.X hXM hYX d.isElementaryAbelian.2.2.1 d.cards.2.2.1
  obtain h₃ := key _ hXwM hYXw (isElementaryAbelian_map_conj d.isElementaryAbelian.2.2.1 _)
    (by rw [card_map_conj, d.cards.2.2.1])
  refine ⟨_, _, _, le_antisymm (sup_le (sup_le h₁.1 h₂.1) h₃.1) ?_, h₁, h₂, h₃⟩
  refine sup_le (d.M_le_sup_conj.trans (sup_le (sup_le ?_ ?_) ?_))
    (le_sup_right.trans (le_sup_left.trans le_sup_left))
  · exact le_sup_left.trans (le_sup_left.trans le_sup_left)
  · exact le_sup_left.trans (le_sup_right.trans le_sup_left)
  · exact le_sup_left.trans le_sup_right

theorem yamada_5_13_2 (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : CFSG.Open.thompsonSubgroup (yamadaL₂ d t) = yamadaM₂ d t := by
  have h4K : 4 ≤ Nat.card K := hK ▸ h.four_le
  have hM₂L₂ := h.yamadaM₂_le_yamadaL₂ d hK hD
  have hq : 2 * Nat.card K ^ 3 < Nat.card K ^ 5 := by
    have : 2 < Nat.card K ^ 2 := by nlinarith
    calc 2 * Nat.card K ^ 3 < Nat.card K ^ 2 * Nat.card K ^ 3 :=
          Nat.mul_lt_mul_of_pos_right this (by positivity)
      _ = Nat.card K ^ 5 := by ring
  have hcomm : ∀ {A : Subgroup G}, IsMulCommutative A → ∀ x ∈ A, ∀ y ∈ A, x * y = y * x :=
    fun {A} _ x hx y hy => congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : A) ⟨y, hy⟩)
  have hmax : ∀ B : Subgroup G, B ≤ yamadaL₂ d t → IsMulCommutative B →
      Nat.card B ≤ Nat.card K ^ 5 := fun B hB hBc => by
    by_cases hBM : B ≤ yamadaM₂ d t
    · exact h.card_le_of_le_yamadaM₂ d hK hD hBM (hcomm hBc)
    · exact (h.card_le_of_not_le_yamadaM₂ d hK hD hB (hcomm hBc) hBM).trans hq.le
  obtain ⟨A₁, A₂, A₃, hA, ⟨hA₁M, hA₁c, hA₁card⟩, ⟨hA₂M, hA₂c, hA₂card⟩,
    ⟨hA₃M, hA₃c, hA₃card⟩⟩ := h.exists_abelian_yamadaM₂ d hK hD
  rw [CFSG.Open.thompsonSubgroup_eq_iSup]
  have hmem : ∀ {A : Subgroup G}, A ≤ yamadaM₂ d t → (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) →
      Nat.card A = Nat.card K ^ 5 →
      A ≤ ⨆ (A' : Subgroup G) (_ : A' ≤ yamadaL₂ d t) (_ : IsMulCommutative A')
        (_ : ∀ B : Subgroup G, B ≤ yamadaL₂ d t → IsMulCommutative B →
          Nat.card B ≤ Nat.card A'), A' := by
    intro A hAM hAc hAcard
    have hAc' : IsMulCommutative A := ⟨⟨fun a b => Subtype.ext (hAc a a.2 b b.2)⟩⟩
    have hAm : ∀ B : Subgroup G, B ≤ yamadaL₂ d t → IsMulCommutative B →
        Nat.card B ≤ Nat.card A := fun B hB hBc => (hmax B hB hBc).trans hAcard.ge
    exact le_iSup_of_le A (le_iSup_of_le (hAM.trans hM₂L₂) (le_iSup_of_le hAc'
      (le_iSup_of_le hAm le_rfl)))
  refine le_antisymm (iSup_le fun A => iSup_le fun hAL => iSup_le fun hAc =>
    iSup_le fun hAm => ?_) ?_
  swap
  · rw [← hA]
    exact sup_le (sup_le (hmem hA₁M hA₁c hA₁card) (hmem hA₂M hA₂c hA₂card))
      (hmem hA₃M hA₃c hA₃card)
  by_contra hAM
  have h1 := hAm A₁ (hA₁M.trans hM₂L₂) ⟨⟨fun a b => Subtype.ext (hA₁c a a.2 b b.2)⟩⟩
  have h2 := h.card_le_of_not_le_yamadaM₂ d hK hD hAL (hcomm hAc) hAM
  rw [hA₁card] at h1
  omega

end Local

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
