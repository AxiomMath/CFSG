module

public import CFSG.LocalAnalysis.EvenBN.U5.Sec3B5
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3FModel

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.LocalAnalysis.EvenBN.Common
open CFSG.EvenSmallLie.UnitarySix.YamadaD (crossedHom mem_ker_crossedHom crossed_conj)

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

@[expose] def F (d : Data G h) : Subgroup G :=
  closure {x | ∃ n ∈ d.N₁, ∃ v ∈ d.V, x = n * v * n⁻¹}

omit [Finite G] in
theorem conj_mem_F {n v : G} (hn : n ∈ d.N₁) (hv : v ∈ d.V) : n * v * n⁻¹ ∈ d.F :=
  subset_closure ⟨n, hn, v, hv, rfl⟩

omit [Finite G] in
theorem V_le_F (d : Data G h) : d.V ≤ d.F := fun v hv => by
  have := d.conj_mem_F (one_mem _) hv
  rwa [one_mul, inv_one, mul_one] at this

omit [Finite G] in
theorem F_le {X : Subgroup G} (hX : ∀ n ∈ d.N₁, ∀ v ∈ d.V, n * v * n⁻¹ ∈ X) : d.F ≤ X :=
  (closure_le _).2 fun _ ⟨n, hn, v, hv, hx⟩ => hx ▸ hX n hn v hv

theorem N₁_le_normalizer_F (d : Data G h) : d.N₁ ≤ normalizer (d.F : Set G) := fun g hg =>
  mem_normalizer_of_conj_le fun x hx => by
    have hle : d.F ≤ d.F.comap (MulAut.conj g).toMonoidHom := F_le fun n hn v hv => by
      change g * (n * v * n⁻¹) * g⁻¹ ∈ d.F
      rw [show g * (n * v * n⁻¹) * g⁻¹ = (g * n) * v * (g * n)⁻¹ by group]
      exact conj_mem_F (mul_mem hg hn) hv
    exact hle hx

theorem Hyp.N₁_le (hd : d.Hyp) :
    d.N₁ ≤ normalizer (d.B₁ : Set G) ⊓ centralizer ({d.t} : Set G) := by
  rintro _ ⟨_, ⟨A, rfl⟩, rfl⟩
  rw [← lev_eq_leviSU A (by rw [Matrix.SpecialLinearGroup.det_coe]; exact isUnit_one)]
  exact hd.η_lev_mem _ _

theorem η_lev_mem_normalizer_A₃ (d : Data G h) (A : Matrix (Fin 2) (Fin 2) K)
    (hA : IsUnit A.det) : d.η (lev (hK := h) A hA) ∈ normalizer (d.A₃ : Set G) :=
  mem_normalizer_of_conj_le fun a ha => by
    obtain ⟨s, hs, rfl⟩ := ha
    exact ⟨_, lev_conj_mem_Ssub A hA hs, by rw [map_mul, map_mul, map_inv]⟩

theorem N₁_le_normalizer_A₃ (d : Data G h) : d.N₁ ≤ normalizer (d.A₃ : Set G) := by
  rintro _ ⟨_, ⟨A, rfl⟩, rfl⟩
  rw [← lev_eq_leviSU A (by rw [Matrix.SpecialLinearGroup.det_coe]; exact isUnit_one)]
  exact d.η_lev_mem_normalizer_A₃ _ _

theorem Hyp.V_le_centralizer_A₃ (hd : d.Hyp) : d.V ≤ centralizer (d.A₃ : Set G) := fun _ hv =>
  Subgroup.centralizer_le (SetLike.coe_subset_coe.2 d.A₃_le_P)
    (hd.CB₄I₃_le_centralizer_P (hd.V_le_CB₄I₃ hv))

theorem Hyp.F_le_B₅ (hd : d.Hyp) : d.F ≤ d.B₅ := F_le fun _ hn v hv =>
  (mem_normalizer_iff.1 (d.le_normalizer_B₅ (hd.N₁_le hn).1) v).1 (hd.V_le_B₅ hv)

theorem Hyp.F_le_centralizer_A₃ (hd : d.Hyp) : d.F ≤ centralizer (d.A₃ : Set G) :=
  F_le fun _ hn v hv => (mem_normalizer_iff.1 (Prelim.normalizer_le_normalizer_centralizer d.A₃
    (d.N₁_le_normalizer_A₃ hn)) v).1 (hd.V_le_centralizer_A₃ hv)

theorem Hyp.F_le_normalizer_B₁ (hd : d.Hyp) : d.F ≤ normalizer (d.B₁ : Set G) :=
  hd.F_le_B₅.trans d.B₅_le

theorem Hyp.F_le_centralizer_A₁ (hd : d.Hyp) : d.F ≤ centralizer (d.A₁ : Set G) :=
  hd.F_le_B₅.trans hd.two_core_B₅.1

theorem Hyp.t_mem_normalizer_F (hd : d.Hyp) : d.t ∈ normalizer (d.F : Set G) :=
  mem_normalizer_of_conj_le fun x hx => by
    have hle : d.F ≤ d.F.comap (MulAut.conj d.t).toMonoidHom := F_le fun n hn v hv => by
      change d.t * (n * v * n⁻¹) * d.t⁻¹ ∈ d.F
      have hnt : n * d.t = d.t * n := (mem_centralizer_singleton_iff.1 (hd.N₁_le hn).2)
      have htinv : d.t⁻¹ = d.t := inv_eq_of_mul_eq_one_right hd.t_mul_t
      have hcr := hd.cr_mem ((hd.V_le_CB₄I₃.trans d.CB₄I₃_le) hv)
      have e : d.t * (n * v * n⁻¹) * d.t⁻¹ = n * (v * (v⁻¹ * d.t * v * d.t)) * n⁻¹ := by
        rw [htinv]
        calc d.t * (n * v * n⁻¹) * d.t = (d.t * n) * v * (n⁻¹ * d.t) := by group
          _ = (n * d.t) * v * (d.t * n⁻¹) := by
            rw [← hnt]
            congr 1
            calc n⁻¹ * d.t = n⁻¹ * (d.t * n) * n⁻¹ := by group
              _ = n⁻¹ * (n * d.t) * n⁻¹ := by rw [hnt]
              _ = d.t * n⁻¹ := by group
          _ = n * (v * (v⁻¹ * d.t * v * d.t)) * n⁻¹ := by group
      rw [e]
      exact conj_mem_F hn (mul_mem hv (hd.Zp_le_V hcr))
    exact hle hx

theorem Hyp.closure_conj_Zp_eq (hd : d.Hyp) :
    closure {x | ∃ n ∈ d.N₁, ∃ z ∈ d.Zp, x = n * z * n⁻¹} = d.A₁ := by
  set W := closure {x | ∃ n ∈ d.N₁, ∃ z ∈ d.Zp, x = n * z * n⁻¹} with hW
  have hWA : W ≤ d.A₁ := (closure_le _).2 fun _ ⟨n, hn, z, hz, hx⟩ => hx ▸
    (mem_normalizer_iff.1 (hd.normalizer_B₁_le_normalizer_A₁ (hd.N₁_le hn).1) z).1 (d.Zp_le_A₁ hz)
  have hZW : d.Zp ≤ W := fun z hz => subset_closure ⟨1, one_mem _, z, hz, by group⟩
  have key : ∀ g : G, g ∈ normalizer (d.Zp : Set G) → g ∈ normalizer (d.N₁ : Set G) →
      g ∈ normalizer (W : Set G) := fun g hgZ hgN => mem_normalizer_of_conj_le fun x hx => by
    have hle : W ≤ W.comap (MulAut.conj g).toMonoidHom :=
      (closure_le _).2 fun _ ⟨n, hn, z, hz, hx⟩ => by
        rw [hx]
        change g * (n * z * n⁻¹) * g⁻¹ ∈ W
        rw [show g * (n * z * n⁻¹) * g⁻¹ = (g * n * g⁻¹) * (g * z * g⁻¹) * (g * n * g⁻¹)⁻¹ by
          group]
        exact subset_closure ⟨_, (mem_normalizer_iff.1 hgN n).1 hn, _,
          (mem_normalizer_iff.1 hgZ z).1 hz, rfl⟩
    exact hle hx
  have hN₁W : ∀ n ∈ d.N₁, n ∈ normalizer (W : Set G) := fun n hn =>
    mem_normalizer_of_conj_le fun x hx => by
      have hle : W ≤ W.comap (MulAut.conj n).toMonoidHom :=
        (closure_le _).2 fun _ ⟨m, hm, z, hz, hx⟩ => by
          rw [hx]
          change n * (m * z * m⁻¹) * n⁻¹ ∈ W
          rw [show n * (m * z * m⁻¹) * n⁻¹ = (n * m) * z * (n * m)⁻¹ by group]
          exact subset_closure ⟨_, mul_mem hn hm, z, hz, rfl⟩
      exact hle hx
  have hlev : ∀ (A : Matrix (Fin 2) (Fin 2) K) (hA : IsUnit A.det),
      d.η (lev (hK := h) A hA) ∈ normalizer (W : Set G) := by
    intro A hA
    obtain ⟨n, hn, e⟩ := exists_lev_eq_mul (h := h) A hA
    rw [e, map_mul]
    refine mul_mem (hN₁W _ ⟨n, hn, rfl⟩) (key _ ?_ ?_)
    · exact d.I_le_normalizer_Zp ⟨_, (lev_diag (h := h) hA.ne_zero one_ne_zero).1, rfl⟩
    · refine mem_normalizer_of_conj_le fun x hx => ?_
      obtain ⟨m, hm, rfl⟩ := hx
      exact ⟨_, lev_conj_mem_N₁sub _ _ hm, by rw [map_mul, map_mul, map_inv]⟩
  rcases hd.eq_bot_or_eq_A₁ hWA hlev with h0 | h1
  · exfalso
    obtain ⟨y, hy, hy1⟩ := hd.exists_mem_Zp_ne_one
    exact hy1 ((Subgroup.mem_bot).1 (h0 ▸ hZW hy))
  · exact h1

theorem Hyp.A₁_le_F (hd : d.Hyp) : d.A₁ ≤ d.F := by
  rw [← hd.closure_conj_Zp_eq]
  exact (closure_le _).2 fun _ ⟨n, hn, z, hz, hx⟩ => hx ▸ conj_mem_F hn (hd.Zp_le_V hz)

theorem Hyp.exists_F_cr_eq (hd : d.Hyp) {y : G} (hy : y ∈ d.A₁) :
    ∃ x ∈ d.F, x⁻¹ * d.t * x * d.t = y := by
  have hc := hd.cosetData_B₁
  set φ := crossedHom hd.t_mul_t d.A₁ d.F hd.F_le_centralizer_A₁
    (fun x hx => hc.crossed_mem x (hd.F_le_normalizer_B₁ hx)) with hφ
  set W : Subgroup G := φ.range.map d.A₁.subtype with hW
  have hWmem : ∀ x (hx : x ∈ d.F), x⁻¹ * d.t * x * d.t ∈ W := fun x hx =>
    ⟨φ ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩, rfl⟩
  have hA₁W : d.A₁ ≤ W := by
    rw [← hd.closure_conj_Zp_eq]
    refine (closure_le _).2 fun _ ⟨n, hn, z, hz, hx⟩ => ?_
    obtain ⟨v, hv, hvt⟩ := hd.exists_V_cr_eq hz
    rw [hx, ← hvt, ← crossed_conj (mem_centralizer_singleton_iff.1 (hd.N₁_le hn).2)]
    exact hWmem _ (conj_mem_F hn hv)
  obtain ⟨_, ⟨x, rfl⟩, hx⟩ := hA₁W hy
  exact ⟨x, x.2, hx⟩

theorem Hyp.B₃_le_normalizer_F (hd : d.Hyp) : d.B₃ ≤ normalizer (d.F : Set G) :=
  sup_le (zpowers_le.2 hd.t_mem_normalizer_F) fun a ha =>
    Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun _ hx =>
      (mem_centralizer_iff.1 (hd.F_le_centralizer_A₃ hx) a ha).symm)

theorem Hyp.B₅_eq_F_sup_B₃ (hd : d.Hyp) : d.B₅ = d.F ⊔ d.B₃ := by
  obtain ⟨hZ, -, hB₃, -, -⟩ := hd.two_core_B₅
  have hc := hd.cosetData_B₁
  refine le_antisymm (fun x hx => ?_) (sup_le hd.F_le_B₅ hd.B₃_le_B₅)
  have hxH : x ∈ normalizer (d.B₁ : Set G) ⊓ centralizer (d.A₁ : Set G) := ⟨d.B₅_le hx, hZ hx⟩
  obtain ⟨g, hg, hgt⟩ := hd.exists_F_cr_eq (hc.crossed_mem x hxH.1)
  have hgH : g ∈ normalizer (d.B₁ : Set G) ⊓ centralizer (d.A₁ : Set G) :=
    ⟨hd.F_le_normalizer_B₁ hg, hd.F_le_centralizer_A₁ hg⟩
  have hgx : g⁻¹ * x ∈ d.B₃ := by
    rw [← hB₃]
    refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem (hd.F_le_B₅ hg)) hx, ?_⟩
    have e := hc.crossed_mul_of_mem (inv_mem hgH) hxH
    rw [hc.crossed_inv_of_mem hgH, hgt, inv_mul_cancel] at e
    rw [mem_centralizer_singleton_iff]
    have e' : (g⁻¹ * x)⁻¹ * d.t * (g⁻¹ * x) = d.t := by
      calc (g⁻¹ * x)⁻¹ * d.t * (g⁻¹ * x) = (g⁻¹ * x)⁻¹ * d.t * (g⁻¹ * x) * d.t * d.t := by
            rw [mul_assoc _ d.t d.t, hd.t_mul_t, mul_one]
        _ = d.t := by rw [e, one_mul]
    calc g⁻¹ * x * d.t = (g⁻¹ * x) * ((g⁻¹ * x)⁻¹ * d.t * (g⁻¹ * x)) := by rw [e']
      _ = d.t * (g⁻¹ * x) := by group
  rw [show x = g * (g⁻¹ * x) by group]
  exact mul_mem (mem_sup_left hg) (mem_sup_right hgx)

theorem Hyp.exists_mul_of_mem_B₅ (hd : d.Hyp) {x : G} (hx : x ∈ d.B₅) :
    ∃ y ∈ d.F, ∃ b ∈ d.B₃, x = y * b :=
  exists_mul_of_mem_sup_of_le_normalizer hd.B₃_le_normalizer_F (hd.B₅_eq_F_sup_B₃ ▸ hx)

theorem Hyp.normalizer_B₁_inf_le_normalizer_A₃ (hd : d.Hyp) :
    normalizer (d.B₁ : Set G) ⊓ centralizer ({d.t} : Set G) ≤ normalizer (d.A₃ : Set G) := by
  intro c hc
  refine mem_normalizer_of_conj_le fun a ha => ?_
  have hcL : c ∈ normalizer (d.L : Set G) := hd.centralizer_le_normalizer hc.2
  have haL : a ∈ d.L := d.A₃_le_P.trans d.P_le_L ha
  have hxL : c * a * c⁻¹ ∈ d.L := (mem_normalizer_iff.1 hcL a).1 haL
  have haA : a ∈ centralizer (d.A₁ : Set G) := mem_centralizer_iff.2 fun y hy =>
    d.A₁_commute_A₃ y hy a ha
  have hxA : c * a * c⁻¹ ∈ centralizer (d.A₁ : Set G) :=
    (mem_normalizer_iff.1 (Prelim.normalizer_le_normalizer_centralizer d.A₁
      (hd.normalizer_B₁_le_normalizer_A₁ hc.1)) a).1 haA
  have hxt : c * a * c⁻¹ ∈ centralizer ({d.t} : Set G) := hd.L_le_centralizer hxL
  obtain ⟨k, hk⟩ := d.isPGroup_P ⟨a, d.A₃_le_P ha⟩
  have hak : a ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hxB := hd.mem_B₃_of_pow (mem_centralizer_sup (mem_centralizer_zpowers hxt) hxA) (k := k)
    (by rw [conj_pow, hak, mul_one, mul_inv_cancel])
  obtain ⟨a', ha', h1 | h1⟩ := hd.exists_of_mem_B₃ hxB
  · rw [h1]
    exact ha'
  · exfalso
    apply hd.t_not_mem_L
    have := mul_mem hxL (inv_mem (d.A₃_le_P.trans d.P_le_L ha'))
    rwa [h1, mul_inv_cancel_right] at this

theorem Hyp.B₃_le_normalizer_A₃ (hd : d.Hyp) : d.B₃ ≤ normalizer (d.A₃ : Set G) :=
  sup_le (zpowers_le.2 (Subgroup.centralizer_le_normalizer _
    (mem_centralizer_iff.2 fun _ ha =>
      (mem_centralizer_singleton_iff.1 (hd.L_le_centralizer (d.A₃_le_P.trans d.P_le_L ha))))))
    (Subgroup.le_normalizer)

theorem Hyp.normalizer_B₁_le_normalizer_A₃ (hd : d.Hyp) :
    normalizer (d.B₁ : Set G) ≤ normalizer (d.A₃ : Set G) := by
  intro g hg
  obtain ⟨c, hc, x, hx, rfl⟩ := hd.two_core_B₅.2.2.2.2 g hg
  refine mul_mem (hd.normalizer_B₁_inf_le_normalizer_A₃ hc) ?_
  obtain ⟨y, hy, b, hb, rfl⟩ := hd.exists_mul_of_mem_B₅ hx
  exact mul_mem (Subgroup.centralizer_le_normalizer _ (hd.F_le_centralizer_A₃ hy))
    (hd.B₃_le_normalizer_A₃ hb)

theorem Hyp.mem_B₁_of_mem_B₃ (hd : d.Hyp) {b : G} (hb : b ∈ d.B₃)
    (hbA : b ∈ centralizer (d.A₃ : Set G)) : b ∈ d.B₁ := by
  obtain ⟨a, ha, h1 | h1⟩ := hd.exists_of_mem_B₃ hb
  · rw [h1] at hbA ⊢
    exact mem_sup_right (d.mem_A₁_of_commute ha fun y hy => mem_centralizer_iff.1 hbA y hy)
  · have htA : d.t ∈ centralizer (d.A₃ : Set G) := mem_centralizer_iff.2 fun y hy =>
      (mem_centralizer_singleton_iff.1 (hd.L_le_centralizer (d.A₃_le_P.trans d.P_le_L hy)))
    have haA : a ∈ centralizer (d.A₃ : Set G) := by
      have := mul_mem (inv_mem htA) (h1 ▸ hbA)
      rwa [inv_mul_cancel_left] at this
    rw [h1]
    exact mul_mem (mem_sup_left (mem_zpowers _))
      (mem_sup_right (d.mem_A₁_of_commute ha fun y hy => mem_centralizer_iff.1 haA y hy))

theorem Hyp.B₅_inf_centralizer_A₃ (hd : d.Hyp) :
    d.B₅ ⊓ centralizer (d.A₃ : Set G) = d.F ⊔ zpowers d.t := by
  have htB₃ : d.t ∈ d.B₃ := mem_sup_left (mem_zpowers _)
  have htA : d.t ∈ centralizer (d.A₃ : Set G) := mem_centralizer_iff.2 fun y hy =>
    (mem_centralizer_singleton_iff.1 (hd.L_le_centralizer (d.A₃_le_P.trans d.P_le_L hy)))
  refine le_antisymm (fun x hx => ?_)
    (sup_le (le_inf hd.F_le_B₅ hd.F_le_centralizer_A₃)
      (zpowers_le.2 ⟨hd.B₃_le_B₅ htB₃, htA⟩))
  obtain ⟨y, hy, b, hb, rfl⟩ := hd.exists_mul_of_mem_B₅ hx.1
  have hbA : b ∈ centralizer (d.A₃ : Set G) := by
    have := mul_mem (inv_mem (hd.F_le_centralizer_A₃ hy)) hx.2
    rwa [inv_mul_cancel_left] at this
  obtain ⟨a, ha, h1 | h1⟩ := hd.exists_of_mem_B₁ (hd.mem_B₁_of_mem_B₃ hb hbA)
  · rw [h1]
    exact mul_mem (mem_sup_left hy) (mem_sup_left (hd.A₁_le_F ha))
  · rw [h1, show y * (d.t * a) = (y * (d.t * a * d.t⁻¹)) * d.t by group]
    refine mul_mem (mem_sup_left (mul_mem hy ?_)) (mem_sup_right (mem_zpowers _))
    exact (mem_normalizer_iff.1 hd.t_mem_normalizer_F a).1 (hd.A₁_le_F ha)

theorem Hyp.normalizer_B₁_le_normalizer_Ft (hd : d.Hyp) :
    normalizer (d.B₁ : Set G) ≤ normalizer ((d.F ⊔ zpowers d.t : Subgroup G) : Set G) := by
  intro g hg
  rw [← hd.B₅_inf_centralizer_A₃]
  exact mem_normalizer_inf (d.le_normalizer_B₅ hg) (Prelim.normalizer_le_normalizer_centralizer
    d.A₃ (hd.normalizer_B₁_le_normalizer_A₃ hg))

theorem Hyp.mul_self_ne_t_mul (hd : d.Hyp) {x a : G} (hx : x ∈ d.B₅) (ha : a ∈ d.A₁) :
    x * x ≠ d.t * a := by
  intro e
  obtain ⟨-, -, hB₃, htr, -⟩ := hd.two_core_B₅
  obtain ⟨y, hy, hyt⟩ := htr a ha
  set w := y * x * y⁻¹ with hw
  have hw2 : w * w = d.t := by
    calc w * w = y * (x * x) * y⁻¹ := by rw [hw]; group
      _ = y * (y⁻¹ * d.t * y) * y⁻¹ := by rw [e, hyt]
      _ = d.t := by group
  have hwB : w ∈ d.B₅ := mul_mem (mul_mem hy hx) (inv_mem hy)
  have hwt : w ∈ centralizer ({d.t} : Set G) := by
    rw [mem_centralizer_singleton_iff, ← hw2]
    group
  have hwB₃ : w ∈ d.B₃ := hB₃ ▸ Subgroup.mem_inf.2 ⟨hwB, hwt⟩
  have := hd.square_mem_A₁_of_mem_B₃ hwB₃
  rw [hw2] at this
  exact hd.t_not_mem_A₁ this

theorem Hyp.mul_self_mem_A₁ (hd : d.Hyp) {x : G} (hx : x ∈ d.B₅)
    (hxA : x ∈ centralizer (d.A₃ : Set G)) : x * x ∈ d.A₁ := by
  obtain ⟨hZ, -, hB₃, -, -⟩ := hd.two_core_B₅
  have hc := hd.cosetData_B₁
  have hxH : x ∈ normalizer (d.B₁ : Set G) ⊓ centralizer (d.A₁ : Set G) := ⟨d.B₅_le hx, hZ hx⟩
  have hx2 : x * x ∈ d.B₃ := by
    rw [← hB₃]
    refine Subgroup.mem_inf.2 ⟨mul_mem hx hx, ?_⟩
    have e := hc.crossed_mul_of_mem hxH hxH
    rw [hc.mul_self_of_mem (hc.crossed_mem_of_mem hxH)] at e
    rw [mem_centralizer_singleton_iff]
    have e' : (x * x)⁻¹ * d.t * (x * x) = d.t := by
      calc (x * x)⁻¹ * d.t * (x * x) = (x * x)⁻¹ * d.t * (x * x) * d.t * d.t := by
            rw [mul_assoc _ d.t d.t, hd.t_mul_t, mul_one]
        _ = d.t := by rw [e, one_mul]
    calc x * x * d.t = (x * x) * ((x * x)⁻¹ * d.t * (x * x)) := by rw [e']
      _ = d.t * (x * x) := by group
  obtain ⟨a, ha, h1 | h1⟩ := hd.exists_of_mem_B₁ (hd.mem_B₁_of_mem_B₃ hx2 (mul_mem hxA hxA))
  · rw [h1]
    exact ha
  · exact absurd h1 (hd.mul_self_ne_t_mul hx ha)

theorem Hyp.commutator_mem_A₁ (hd : d.Hyp) {x y : G} (hx : x ∈ d.B₅)
    (hxA : x ∈ centralizer (d.A₃ : Set G)) (hy : y ∈ d.B₅) (hyA : y ∈ centralizer (d.A₃ : Set G)) :
    x * y * x⁻¹ * y⁻¹ ∈ d.A₁ := by
  have hZ := hd.two_core_B₅.1
  have h1 := hd.mul_self_mem_A₁ (mul_mem hx hy) (mul_mem hxA hyA)
  have h2 := hd.mul_self_mem_A₁ hx hxA
  have h3 := hd.mul_self_mem_A₁ hy hyA
  have h4 : y⁻¹ * (x * x)⁻¹ * y ∈ d.A₁ := by
    have hc := mem_centralizer_iff.1 (hZ (inv_mem hy)) _ (inv_mem h2)
    rw [← hc, inv_mul_cancel_right]
    exact inv_mem h2
  have e : x * y * x⁻¹ * y⁻¹ = (x * y) * (x * y) * (y⁻¹ * (x * x)⁻¹ * y) * (y * y)⁻¹ := by group
  rw [e]
  exact mul_mem (mul_mem h1 h4) (inv_mem h3)

end Data

end CFSG.LocalAnalysis.EvenBN.U5
