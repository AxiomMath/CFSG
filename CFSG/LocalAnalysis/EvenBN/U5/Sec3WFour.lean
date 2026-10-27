module

public import CFSG.LocalAnalysis.EvenBN.U5.Sec3WTwo

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp
open scoped commutatorElement

section Generic

variable {G : Type*} [Group G] [Finite G]

theorem card_le_two_mul_inf_of_forall_mul_mem {X K : Subgroup G}
    (hmul : ∀ a ∈ X, ∀ b ∈ X, a ∉ K → b ∉ K → a * b ∈ K) :
    Nat.card X ≤ 2 * Nat.card (X ⊓ K : Subgroup G) := by
  classical
  by_cases hXK : X ≤ K
  · rw [inf_eq_left.mpr hXK]
    omega
  obtain ⟨a, haX, haK⟩ := IsConcreteLE.not_le_iff_exists.mp hXK
  let φ : X → Bool × (X ⊓ K : Subgroup G) := fun x =>
    if hx : (x : G) ∈ K then (true, ⟨x, mem_inf.mpr ⟨x.2, hx⟩⟩)
    else (false, ⟨a * x, mem_inf.mpr ⟨mul_mem haX x.2, hmul a haX x x.2 haK hx⟩⟩)
  have hφ : Function.Injective φ := by
    intro x y hxy
    by_cases hx : (x : G) ∈ K <;> by_cases hy : (y : G) ∈ K <;>
      simp only [φ, hx, hy, dite_true, dite_false, Prod.mk.injEq] at hxy
    · exact Subtype.ext (congrArg (fun z : (X ⊓ K : Subgroup G) => (z : G)) hxy.2)
    · exact absurd hxy.1 (by decide)
    · exact absurd hxy.1 (by decide)
    · exact Subtype.ext (mul_left_cancel (congrArg (fun z : (X ⊓ K : Subgroup G) => (z : G))
        hxy.2))
  have h1 := Nat.card_le_card_of_injective φ hφ
  rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at h1

theorem card_mul_le_of_le {X N H : Subgroup G} (hXH : X ≤ H) (hNH : N ≤ H)
    (hXN : X ≤ normalizer (N : Set G)) :
    Nat.card X * Nat.card N ≤ Nat.card (X ⊓ N : Subgroup G) * Nat.card H := by
  have h1 := Common.card_sup_mul_card_inf_eq hXN
  rw [sup_comm, inf_comm, mul_comm (Nat.card N)] at h1
  rw [← h1, mul_comm]
  exact Nat.mul_le_mul_left _ (card_le_of_le (sup_le hXH hNH))

end Generic

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem Hyp.T_le_normalizer_F (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    d.T ≤ normalizer (d.F : Set G) := fun _ hs =>
  hd.normalizer_B₁_le_normalizer_F hGMS (hd.T_le_normalizer_B₁ hs)

theorem Hyp.T_le_normalizer_P (hd : d.Hyp) : d.T ≤ normalizer (d.P : Set G) := by
  intro s hs
  have hsT : s ∈ normalizer (d.T : Set G) := le_normalizer hs
  have h1 : s ∈ normalizer (d.tP : Set G) := hd.normalizer_T_le hsT
  have h2 : s ∈ normalizer (d.L : Set G) := hd.T_le_normalizer hs
  rw [← hd.tP_inf_L]
  exact mem_normalizer_inf h1 h2

theorem Hyp.F_inf_T (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    d.F ⊓ d.T = d.A₁ := by
  refine le_antisymm (fun x hx => ?_) (le_inf hd.A₁_le_F hd.A₁_le_T)
  rw [← hd.F_inf_centralizer_t hGMS]
  exact ⟨hx.1, hd.T_le_centralizer hx.2⟩

theorem Hyp.FP_inf_T (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    (d.F ⊔ d.P) ⊓ d.T = d.P := by
  refine le_antisymm (fun x hx => ?_) (le_inf le_sup_right hd.P_le)
  obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨a, ha, p, hp, rfl⟩ := hd.exists_mul_of_mem_FP hGMS hx1
  have haT : a ∈ d.T := by
    have := mul_mem hx2 (inv_mem (hd.P_le hp))
    rwa [mul_inv_cancel_right] at this
  have haA : a ∈ d.A₁ := by
    rw [← hd.F_inf_T hGMS]
    exact Subgroup.mem_inf.2 ⟨ha, haT⟩
  exact mul_mem (d.A₁_le_P haA) hp

theorem Hyp.F_inf_A₃ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    d.F ⊓ d.A₃ = d.A₁ :=
  le_antisymm ((inf_le_inf_left _ d.A₃_le_B₃).trans (hd.F_inf_B₃ hGMS).le)
    (le_inf hd.A₁_le_F d.A₁_le_A₃)

theorem Hyp.card_FA₃ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    Nat.card (d.F ⊔ d.A₃ : Subgroup G) = (2 ^ f) ^ 12 := by
  have hN : d.A₃ ≤ normalizer (d.F : Set G) := d.A₃_le_P.trans (hd.P_le_normalizer_F hGMS)
  have h1 := Common.card_sup_mul_card_inf_eq hN
  rw [hd.F_inf_A₃ hGMS, hd.card_F hGMS, d.card_A₃, d.card_A₁] at h1
  have hq : 0 < (2 ^ f) ^ 4 := by positivity
  refine Nat.eq_of_mul_eq_mul_right hq (h1.trans ?_)
  ring

theorem Hyp.card_FP (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    Nat.card (d.F ⊔ d.P : Subgroup G) = (2 ^ f) ^ 14 := by
  have h1 := Common.card_sup_mul_card_inf_eq (hd.P_le_normalizer_F hGMS)
  rw [hd.F_inf_P hGMS, hd.card_F hGMS, d.card_P, d.card_A₁] at h1
  have hq : 0 < (2 ^ f) ^ 4 := by positivity
  refine Nat.eq_of_mul_eq_mul_right hq (h1.trans ?_)
  ring

theorem Hyp.mul_self_eq_one_of_mem_F (hGMS : GMSK.GMSUnitarySharpKRankOneStatement)
    (hd : d.Hyp) {x : G} (hx : x ∈ d.F) : x * x = 1 := by
  have h := @CFSG.elemPow_eq_one_of_isElementaryAbelian 2 G _ d.F
    (hd.isElementaryAbelian_F hGMS) x hx
  rwa [sq] at h

theorem Hyp.mem_F_of_mem_FA₃ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) {x : G}
    (hx : x ∈ d.F ⊔ d.A₃) (hx2 : x * x = 1) : x ∈ d.F := by
  have hN : d.A₃ ≤ normalizer (d.F : Set G) := d.A₃_le_P.trans (hd.P_le_normalizer_F hGMS)
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hN hx
  have hab : b * a = a * b := mem_centralizer_iff.1 (hd.F_le_centralizer_A₃ ha) b hb
  have hb2 : b * b = 1 := by
    have e : a * b * (a * b) = (a * a) * (b * b) := by
      rw [show a * b * (a * b) = a * (b * a) * b by group, hab]
      group
    rw [e, hd.mul_self_eq_one_of_mem_F hGMS ha, one_mul] at hx2
    exact hx2
  have hbA : b ∈ d.A₁ := by
    rw [← d.sec2_2_three.1]
    exact subset_closure ⟨hb, hb2⟩
  exact mul_mem ha (hd.A₁_le_F hbA)

theorem Hyp.card_F_inf_centralizer_le (hGMS : GMSK.GMSUnitarySharpKRankOneStatement)
    (hd : d.Hyp) {s : G} (hs : s ∈ centralizer ({d.t} : Set G)) :
    Nat.card (d.F ⊓ centralizer ({s} : Set G) : Subgroup G) ≤
      Nat.card (d.A₁ ⊓ centralizer ({s} : Set G) : Subgroup G) ^ 2 := by
  have hYB : d.F ⊓ centralizer ({s} : Set G) ≤
      centralizer ((d.A₁ ⊓ centralizer ({s} : Set G) : Subgroup G) : Set G) :=
    inf_le_left.trans (hd.F_le_centralizer_A₁.trans (centralizer_le inf_le_left))
  have hY : ∀ y ∈ d.F ⊓ centralizer ({s} : Set G),
      y⁻¹ * d.t * y * d.t ∈ d.A₁ ⊓ centralizer ({s} : Set G) := by
    intro y hy
    refine ⟨hd.cr_F_mem hy.1, mem_centralizer_singleton_iff.2 ?_⟩
    have e := d.cr_conj (x := y) hs
    rw [show s * y * s⁻¹ = y by rw [← mem_centralizer_singleton_iff.1 hy.2,
      mul_inv_cancel_right]] at e
    calc y⁻¹ * d.t * y * d.t * s = s * (y⁻¹ * d.t * y * d.t) * s⁻¹ * s := by rw [← e]
      _ = s * (y⁻¹ * d.t * y * d.t) := by group
  have h1 := CFSG.EvenSmallLie.UnitarySix.YamadaD.card_le_of_crossed hd.t_mul_t hYB hY
  have hker : d.F ⊓ centralizer ({s} : Set G) ⊓ centralizer ({d.t} : Set G) =
      d.A₁ ⊓ centralizer ({s} : Set G) := by
    rw [inf_right_comm, hd.F_inf_centralizer_t hGMS]
  rw [hker, ← sq] at h1
  exact h1

theorem Hyp.exists_act_pow_eq_one (hd : d.Hyp) {g : G} (hg : g ∈ d.T)
    (hgN : g ∈ normalizer (d.L : Set G)) : ∃ k : ℕ, d.act ⟨g, hgN⟩ ^ 2 ^ k = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hd.isPGroup_T) ⟨g, hg⟩
  refine ⟨k, ?_⟩
  rw [← map_pow]
  have hgk : g ^ 2 ^ k = 1 := by
    rw [← orderOf_coe] at hk
    simp only at hk
    rw [← hk, pow_orderOf_eq_one]
  have : (⟨g, hgN⟩ : normalizer (d.L : Set G)) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hgk)
  rw [this, map_one]

theorem Hyp.mem_tP_of_act_mem_Pi (hd : d.Hyp) {g : G} (hg : g ∈ d.T)
    (hgN : g ∈ normalizer (d.L : Set G)) (hgP : d.act ⟨g, hgN⟩ ∈ Pi h) : g ∈ d.tP := by
  have hmem : d.act ⟨g, hgN⟩ ∈ d.actImage d.P := by
    rw [d.actImage_P, ← hd.inf_Pi_actImage_T]
    exact ⟨d.mem_actImage.2 ⟨g, hg, hgN, rfl⟩, hgP⟩
  exact hd.mem_zpowers_sup_of_act_mem le_rfl hg hgN hmem

theorem Hyp.card_A₁_inf_centralizer_le_of_outer (hd : d.Hyp) {s : G} (hs : s ∈ d.T)
    (hst : s ∉ d.tP) :
    Nat.card (d.A₁ ⊓ centralizer ({s} : Set G) : Subgroup G) ≤ (2 ^ f) ^ 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsN : s ∈ normalizer (d.L : Set G) := hd.T_le_normalizer hs
  have hout : d.act ⟨s, hsN⟩ ∉ Pi h := fun e => hst (hd.mem_tP_of_act_mem_Pi hs hsN e)
  have hT2 : IsPGroup 2 (d.actImage d.T) :=
    (hd.isPGroup_T.comap_subtype (K := normalizer (d.L : Set G))).map _
  have h3 := card_Vh_inf_centralizer_le_of_outer hd.center_hypPSU hT2 hd.inf_Pi_actImage_T
    (d.mem_actImage.2 ⟨s, hs, hsN, rfl⟩) hout
  have hAN : ∀ a ∈ d.A₁, a ∈ normalizer (d.L : Set G) := fun a ha =>
    le_normalizer (d.A₁_le_P.trans d.P_le_L ha)
  let φ : (d.A₁ ⊓ centralizer ({s} : Set G) : Subgroup G) →
      (Vh h ⊓ centralizer {d.act ⟨s, hsN⟩} : Subgroup _) := fun a =>
    ⟨d.act ⟨a, hAN a a.2.1⟩, by
      refine ⟨?_, mem_centralizer_singleton_iff.2 ?_⟩
      · rw [← d.actImage_A₁]
        exact d.mem_actImage.2 ⟨a, a.2.1, hAN a a.2.1, rfl⟩
      · rw [← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (mem_centralizer_singleton_iff.1 a.2.2)⟩
  have hφ : Function.Injective φ := by
    intro a b hab
    have e : d.act ⟨a, hAN a a.2.1⟩ = d.act ⟨b, hAN b b.2.1⟩ := congrArg Subtype.val hab
    have hc : (a : G)⁻¹ * b ∈ centralizer (d.L : Set G) := by
      refine (d.act_eq_one_iff ⟨(a : G)⁻¹ * b, mul_mem (inv_mem (hAN a a.2.1))
        (hAN b b.2.1)⟩).1 ?_
      have e' : (⟨(a : G)⁻¹ * b, mul_mem (inv_mem (hAN a a.2.1)) (hAN b b.2.1)⟩ :
          normalizer (d.L : Set G)) = (⟨a, hAN a a.2.1⟩ : normalizer (d.L : Set G))⁻¹ *
          ⟨b, hAN b b.2.1⟩ := rfl
      rw [e', map_mul, map_inv, e, inv_mul_cancel]
    have hL : (a : G)⁻¹ * b ∈ d.L := mul_mem (inv_mem (d.A₁_le_P.trans d.P_le_L a.2.1))
      (d.A₁_le_P.trans d.P_le_L b.2.1)
    have h1 : (a : G)⁻¹ * b ∈ d.L ⊓ centralizer (d.L : Set G) := ⟨hL, hc⟩
    rw [hd.inf_centralizer_eq_bot, mem_bot] at h1
    exact Subtype.ext (inv_mul_eq_one.1 h1)
  exact (Nat.card_le_card_of_injective φ hφ).trans h3

theorem Hyp.card_le_four_mul_of_sq_mem (hd : d.Hyp) {Y : Subgroup G} (hYT : Y ≤ d.T)
    (hsq : ∀ y ∈ Y, y * y ∈ d.P) : Nat.card Y ≤ 4 * Nat.card d.P := by
  have hbar : ∀ a ∈ Y, a ∉ d.tP → ∀ hN : a ∈ normalizer (d.L : Set G), ∀ x : Gam h,
      Phi h x = d.act ⟨a, hN⟩ → ∀ c, x.1.right c = h.bar c := by
    intro a ha hat hN x hx
    have hsq' : d.act ⟨a, hN⟩ * d.act ⟨a, hN⟩ ∈ Pi h := by
      rw [← map_mul]
      have hP : d.act (⟨a, hN⟩ * ⟨a, hN⟩) ∈ d.actImage d.P :=
        d.mem_actImage.2 ⟨a * a, hsq a ha, _, rfl⟩
      rw [d.actImage_P] at hP
      exact Uh_le_Pi hP
    refine (right_eq_of_sq_mem_Pi hsq' hx).resolve_left fun e => hat ?_
    obtain ⟨k, hk⟩ := hd.exists_act_pow_eq_one (hYT ha) hN
    exact hd.mem_tP_of_act_mem_Pi (hYT ha) hN (Dlin_two_mem_Pi ((mem_Dlin_iff hx).2 e) hk)
  have hmul : ∀ a ∈ Y, ∀ b ∈ Y, a ∉ d.tP → b ∉ d.tP → a * b ∈ d.tP := by
    intro a ha b hb hat hbt
    have haN := hd.T_le_normalizer (hYT ha)
    have hbN := hd.T_le_normalizer (hYT hb)
    obtain ⟨x, hx⟩ := Phi_surjective h (d.act ⟨a, haN⟩)
    obtain ⟨y, hy⟩ := Phi_surjective h (d.act ⟨b, hbN⟩)
    have hxy : Phi h (x * y) = d.act ⟨a * b, mul_mem haN hbN⟩ := by
      rw [map_mul, hx, hy, ← map_mul]
      rfl
    have hr : (x * y).1.right = 1 := by
      rw [Subgroup.coe_mul, SemidirectProduct.mul_right]
      ext c
      change x.1.right (y.1.right c) = c
      rw [hbar b hb hbt hbN y hy c, hbar a ha hat haN x hx (h.bar c), h.bar_bar]
    obtain ⟨k, hk⟩ := hd.exists_act_pow_eq_one (mul_mem (hYT ha) (hYT hb)) (mul_mem haN hbN)
    exact hd.mem_tP_of_act_mem_Pi (mul_mem (hYT ha) (hYT hb)) (mul_mem haN hbN)
      (Dlin_two_mem_Pi ((mem_Dlin_iff hxy).2 hr) hk)
  have h1 := card_le_two_mul_inf_of_forall_mul_mem hmul
  have h2 : Nat.card (Y ⊓ d.tP : Subgroup G) ≤ 2 * Nat.card d.P := by
    rw [← hd.card_zpowers_sup d.P_le_L]
    exact card_le_of_le inf_le_right
  omega

theorem Hyp.inf_F_le_centralizer (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    {X : Subgroup G} (hXc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) {a s : G} (ha : a ∈ d.F)
    (hx : a * s ∈ X) : X ⊓ d.F ≤ d.F ⊓ centralizer ({s} : Set G) := by
  intro z hz
  obtain ⟨hzX, hzF⟩ := Subgroup.mem_inf.1 hz
  refine Subgroup.mem_inf.2 ⟨hzF, mem_centralizer_singleton_iff.2 ?_⟩
  have e1 := hXc _ hx z hzX
  have e2 := hd.F_comm hGMS a ha z hzF
  have : a * (s * z) = a * (z * s) := by
    calc a * (s * z) = a * s * z := by group
      _ = z * (a * s) := e1
      _ = (z * a) * s := by group
      _ = a * (z * s) := by rw [← e2]; group
  exact (mul_left_cancel this).symm

theorem Hyp.card_le_of_le_FT (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    {X : Subgroup G} (hXFT : X ≤ d.F ⊔ d.T) (hX : CFSG.IsElementaryAbelian 2 X) :
    Nat.card X ≤ (2 ^ f) ^ 8 ∧ ((2 ^ f) ^ 8 ≤ Nat.card X → X = d.F) := by
  have hq := hd.four_le
  have hX2 : ∀ x ∈ X, x * x = 1 := fun x hx => by
    have := @CFSG.elemPow_eq_one_of_isElementaryAbelian 2 G _ X hX x hx
    rwa [sq] at this
  have hXc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := fun x hx y hy => Prelim.mul_comm_of_mem hX hx hy
  have hTF := hd.T_le_normalizer_F hGMS
  have hPA₃ : d.P ≤ normalizer (d.A₃ : Set G) := fun p hp =>
    hd.normalizer_B₁_le_normalizer_A₃ (hd.T_le_normalizer_B₁ (hd.P_le hp))
  have hFTN : d.F ⊔ d.T ≤ normalizer ((d.F ⊔ d.P : Subgroup G) : Set G) :=
    sup_le (fun a ha => le_normalizer (mem_sup_left ha))
      (fun s hs => Common.mem_normalizer_sup (hTF hs) (hd.T_le_normalizer_P hs))
  have hFPN : d.F ⊔ d.P ≤ normalizer ((d.F ⊔ d.A₃ : Subgroup G) : Set G) :=
    sup_le (fun a ha => le_normalizer (mem_sup_left ha))
      (fun p hp => Common.mem_normalizer_sup (hd.P_le_normalizer_F hGMS hp) (hPA₃ hp))
  have hA : X ⊓ (d.F ⊔ d.A₃) ≤ d.F := fun x hx =>
    hd.mem_F_of_mem_FA₃ hGMS (Subgroup.mem_inf.1 hx).2 (hX2 x (Subgroup.mem_inf.1 hx).1)
  have hB : Nat.card (X ⊓ (d.F ⊔ d.P) : Subgroup G) ≤
      (2 ^ f) ^ 2 * Nat.card (X ⊓ d.F : Subgroup G) := by
    have h1 := card_mul_le_of_le (X := X ⊓ (d.F ⊔ d.P)) (N := d.F ⊔ d.A₃) (H := d.F ⊔ d.P)
      inf_le_right (sup_le_sup_left d.A₃_le_P _) (inf_le_right.trans hFPN)
    have h2 : Nat.card (X ⊓ (d.F ⊔ d.P) ⊓ (d.F ⊔ d.A₃) : Subgroup G) ≤
        Nat.card (X ⊓ d.F : Subgroup G) := card_le_of_le fun x hx =>
      ⟨hx.1.1, hA ⟨hx.1.1, hx.2⟩⟩
    rw [hd.card_FA₃ hGMS, hd.card_FP hGMS] at h1
    have h3 : Nat.card (X ⊓ (d.F ⊔ d.P) : Subgroup G) * (2 ^ f) ^ 12 ≤
        ((2 ^ f) ^ 2 * Nat.card (X ⊓ d.F : Subgroup G)) * (2 ^ f) ^ 12 := by
      calc _ ≤ _ := h1
        _ ≤ Nat.card (X ⊓ d.F : Subgroup G) * (2 ^ f) ^ 14 := Nat.mul_le_mul_right _ h2
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_right h3 (by positivity)
  have hC : Nat.card X ≤ 4 * Nat.card (X ⊓ (d.F ⊔ d.P) : Subgroup G) := by
    set E := X ⊔ (d.F ⊔ d.P) with hE
    have hXN : X ≤ normalizer ((d.F ⊔ d.P : Subgroup G) : Set G) := hXFT.trans hFTN
    have hEFT : E ≤ d.F ⊔ d.T := sup_le hXFT (sup_le_sup_left hd.P_le _)
    set Y := E ⊓ d.T with hY
    have hYsq : ∀ y ∈ Y, y * y ∈ d.P := by
      intro y hy
      obtain ⟨hyE, hyT⟩ := Subgroup.mem_inf.1 hy
      rw [hE, sup_comm] at hyE
      obtain ⟨n, hn, x, hx, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hXN hyE
      have e : n * x * (n * x) = n * (x * n * x⁻¹) * (x * x) := by group
      have hmem : n * x * (n * x) ∈ d.F ⊔ d.P := by
        rw [e, hX2 x hx, mul_one]
        exact mul_mem hn ((mem_normalizer_iff.1 (hXN hx) n).1 hn)
      rw [← hd.FP_inf_T hGMS]
      exact Subgroup.mem_inf.2 ⟨hmem, mul_mem hyT hyT⟩
    have hYc := hd.card_le_four_mul_of_sq_mem inf_le_right hYsq
    have hEeq : E = d.F ⊔ Y := by
      refine le_antisymm (fun e he => ?_) (sup_le (le_sup_left.trans le_sup_right)
        inf_le_left)
      obtain ⟨a, ha, s, hs, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hTF (hEFT he)
      have hsE : s ∈ E := by
        have := mul_mem (inv_mem (show a ∈ E from mem_sup_right (mem_sup_left ha))) he
        rwa [inv_mul_cancel_left] at this
      exact mul_mem (mem_sup_left ha) (mem_sup_right (Subgroup.mem_inf.2 ⟨hsE, hs⟩))
    have hFY : d.F ⊓ Y = d.A₁ := by
      rw [hY, ← inf_assoc, inf_eq_left.2 (show d.F ≤ E from le_sup_left.trans le_sup_right),
        hd.F_inf_T hGMS]
    have h1 := Common.card_sup_mul_card_inf_eq (show Y ≤ normalizer (d.F : Set G) from
      inf_le_right.trans hTF)
    rw [← hEeq, hFY, hd.card_F hGMS, d.card_A₁] at h1
    have hEc : Nat.card E ≤ 4 * Nat.card (d.F ⊔ d.P : Subgroup G) := by
      rw [hd.card_FP hGMS]
      have h2 : Nat.card E * (2 ^ f) ^ 4 ≤ (4 * (2 ^ f) ^ 14) * (2 ^ f) ^ 4 := by
        rw [h1]
        calc (2 ^ f) ^ 8 * Nat.card Y ≤ (2 ^ f) ^ 8 * (4 * Nat.card d.P) :=
              Nat.mul_le_mul_left _ hYc
          _ = _ := by rw [d.card_P]; ring
      exact Nat.le_of_mul_le_mul_right h2 (by positivity)
    have h3 := card_mul_le_of_le (X := X) (N := d.F ⊔ d.P) (H := E) le_sup_left le_sup_right hXN
    have h4 : Nat.card X * Nat.card (d.F ⊔ d.P : Subgroup G) ≤
        (4 * Nat.card (X ⊓ (d.F ⊔ d.P) : Subgroup G)) * Nat.card (d.F ⊔ d.P : Subgroup G) := by
      calc _ ≤ _ := h3
        _ ≤ Nat.card (X ⊓ (d.F ⊔ d.P) : Subgroup G) * (4 * Nat.card (d.F ⊔ d.P : Subgroup G)) :=
            Nat.mul_le_mul_left _ hEc
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_right h4 Nat.card_pos
  have hlt : 4 * ((2 ^ f) ^ 6) < (2 ^ f) ^ 8 := by
    have e : (2 ^ f) ^ 8 = (2 ^ f) ^ 2 * (2 ^ f) ^ 6 := by ring
    have h16 : 16 ≤ (2 ^ f) ^ 2 := by nlinarith
    have hpos : 0 < (2 ^ f) ^ 6 := by positivity
    rw [e]
    nlinarith
  by_cases hXA : X ≤ d.F ⊔ d.A₃
  · have hXF : X ≤ d.F := fun x hx => hA ⟨hx, hXA hx⟩
    have hle : Nat.card X ≤ (2 ^ f) ^ 8 := (card_le_of_le hXF).trans_eq (hd.card_F hGMS)
    exact ⟨hle, fun hge => Subgroup.eq_of_le_of_card_ge hXF (by rw [hd.card_F hGMS]; exact hge)⟩
  · obtain ⟨x, hxX, hxA⟩ := IsConcreteLE.not_le_iff_exists.mp hXA
    suffices hsmall : Nat.card X < (2 ^ f) ^ 8 from ⟨hsmall.le, fun hge => absurd hge (by omega)⟩
    by_cases hP' : ∃ y ∈ X, y ∈ d.F ⊔ d.P ∧ y ∉ d.F ⊔ d.A₃
    · obtain ⟨y, hyX, hyP, hyA⟩ := hP'
      obtain ⟨a, ha, p, hp, rfl⟩ := hd.exists_mul_of_mem_FP hGMS hyP
      have hpA : p ∉ d.A₃ := fun h' => hyA (mul_mem (mem_sup_left ha) (mem_sup_right h'))
      have hXF := card_le_of_le (hd.inf_F_le_centralizer hGMS hXc ha hyX)
      have hCF := hd.card_F_inf_centralizer_le hGMS (hd.L_le_centralizer (d.P_le_L hp))
      have hCA := d.sec2_2_five.1 p hp hpA
      have hXF4 : Nat.card (X ⊓ d.F : Subgroup G) ≤ (2 ^ f) ^ 4 := by
        calc _ ≤ _ := hXF
          _ ≤ _ := hCF
          _ ≤ ((2 ^ f) ^ 2) ^ 2 := Nat.pow_le_pow_left hCA 2
          _ = (2 ^ f) ^ 4 := by ring
      calc Nat.card X ≤ 4 * Nat.card (X ⊓ (d.F ⊔ d.P) : Subgroup G) := hC
        _ ≤ 4 * ((2 ^ f) ^ 2 * (2 ^ f) ^ 4) :=
            Nat.mul_le_mul_left _ (hB.trans (Nat.mul_le_mul_left _ hXF4))
        _ = 4 * (2 ^ f) ^ 6 := by ring
        _ < _ := hlt
    · push Not at hP'
      have hXFP : X ⊓ (d.F ⊔ d.P) ≤ X ⊓ d.F := fun y hy =>
        ⟨hy.1, hA ⟨hy.1, hP' y hy.1 hy.2⟩⟩
      have hxP : x ∉ d.F ⊔ d.P := fun h' => hxA (hP' x hxX h')
      obtain ⟨a, ha, s, hs, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hTF (hXFT hxX)
      have hsP : s ∉ d.P := fun h' => hxP (mul_mem (mem_sup_left ha) (mem_sup_right h'))
      have hsC : s ∈ centralizer ({d.t} : Set G) := hd.T_le_centralizer hs
      have hXF := card_le_of_le (hd.inf_F_le_centralizer hGMS hXc ha hxX)
      have hCs : Nat.card (d.F ⊓ centralizer ({s} : Set G) : Subgroup G) ≤ (2 ^ f) ^ 6 := by
        by_cases hst : s ∈ d.tP
        · obtain ⟨p, hp, hsp | hsp⟩ := hd.exists_of_mem_zpowers_sup d.P_le_L hst
          · exact absurd (hsp ▸ hp) hsP
          · by_cases hpA : p ∈ d.A₃
            ·
              have hle : d.F ⊓ centralizer ({s} : Set G) ≤ d.A₁ := by
                rw [← hd.F_inf_centralizer_t hGMS]
                intro z hz
                obtain ⟨hzF, hzs⟩ := Subgroup.mem_inf.1 hz
                refine Subgroup.mem_inf.2 ⟨hzF, mem_centralizer_singleton_iff.2 ?_⟩
                have e1 := mem_centralizer_singleton_iff.1 hzs
                have e2 : p * z = z * p := mem_centralizer_iff.1
                  (hd.F_le_centralizer_A₃ hzF) p hpA
                rw [hsp] at e1
                have : z * d.t * p = d.t * z * p := by
                  calc z * d.t * p = z * (d.t * p) := by group
                    _ = d.t * p * z := e1
                    _ = d.t * (p * z) := by group
                    _ = d.t * (z * p) := by rw [e2]
                    _ = d.t * z * p := by group
                exact mul_right_cancel this
              calc _ ≤ Nat.card d.A₁ := card_le_of_le hle
                _ = (2 ^ f) ^ 4 := d.card_A₁
                _ ≤ (2 ^ f) ^ 6 := Nat.pow_le_pow_right (by positivity) (by norm_num)
            ·
              have hle : d.A₁ ⊓ centralizer ({s} : Set G) ≤ d.A₁ ⊓ centralizer ({p} : Set G) := by
                intro z hz
                obtain ⟨hzA, hzs⟩ := Subgroup.mem_inf.1 hz
                refine Subgroup.mem_inf.2 ⟨hzA, mem_centralizer_singleton_iff.2 ?_⟩
                have e1 := mem_centralizer_singleton_iff.1 hzs
                have e2 : z * d.t = d.t * z := hd.comm_t (d.A₁_le_P.trans d.P_le_L hzA)
                rw [hsp] at e1
                have : d.t * (z * p) = d.t * (p * z) := by
                  calc d.t * (z * p) = (d.t * z) * p := by group
                    _ = (z * d.t) * p := by rw [e2]
                    _ = z * (d.t * p) := by group
                    _ = d.t * p * z := e1
                    _ = d.t * (p * z) := by group
                exact mul_left_cancel this
              have hCA := d.sec2_2_five.1 p hp hpA
              calc _ ≤ _ := hd.card_F_inf_centralizer_le hGMS hsC
                _ ≤ Nat.card (d.A₁ ⊓ centralizer ({p} : Set G) : Subgroup G) ^ 2 :=
                    Nat.pow_le_pow_left (card_le_of_le hle) 2
                _ ≤ ((2 ^ f) ^ 2) ^ 2 := Nat.pow_le_pow_left hCA 2
                _ ≤ (2 ^ f) ^ 6 := by
                    rw [← pow_mul]
                    exact Nat.pow_le_pow_right (by positivity) (by norm_num)
        · calc _ ≤ _ := hd.card_F_inf_centralizer_le hGMS hsC
            _ ≤ ((2 ^ f) ^ 3) ^ 2 :=
                Nat.pow_le_pow_left (hd.card_A₁_inf_centralizer_le_of_outer hs hst) 2
            _ = (2 ^ f) ^ 6 := by ring
      calc Nat.card X ≤ 4 * Nat.card (X ⊓ (d.F ⊔ d.P) : Subgroup G) := hC
        _ ≤ 4 * (2 ^ f) ^ 6 :=
            Nat.mul_le_mul_left _ (((card_le_of_le hXFP).trans hXF).trans hCs)
        _ < _ := hlt

end Data

end CFSG.LocalAnalysis.EvenBN.U5
