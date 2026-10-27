module

public import CFSG.LocalAnalysis.OddStandard.Seitz77WBridgeQuot
public import CFSG.LocalAnalysis.OddStandard.Seitz77Levi

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.ABGLocalTools
open scoped commutatorElement

namespace IsSetting25

variable {G : Type} [Group G] [Finite G] {A W X O : Subgroup G} {t : G}
  (S : IsSetting25 A W t X O)

include S

theorem normalizer_le_normalizer_O :
    normalizer ((W ⊔ zpowers t : Subgroup G) : Set G) ≤ normalizer (O : Set G) := fun n hn =>
  Subgroup.mem_normalizer_fintype fun o ho => S.O_norm n hn o ho

theorem mem_Mx {n : G} (hn : n ∈ normalizer ((W ⊔ zpowers t : Subgroup G) : Set G)) :
    n ∈ normalizer (X : Set G) ⊓ normalizer (O : Set G) :=
  ⟨S.normalizer_le hn, S.normalizer_le_normalizer_O hn⟩

theorem mem_normalizer_E_of_normalizer_W {a : G} (ha : a ∈ A)
    (hn : a ∈ normalizer (W : Set G)) :
    a ∈ normalizer ((W ⊔ zpowers t : Subgroup G) : Set G) := by
  have hat : a * t = t * a := mem_centralizer_iff.mp S.t_cent a ha
  have hat' : a * t * a⁻¹ = t := by rw [hat]; group
  refine Subgroup.mem_normalizer_fintype fun e he => ?_
  rcases S.mem_E_iff.mp he with hW | ⟨w, hw, rfl⟩
  · exact mem_sup_left ((mem_normalizer_iff.mp hn e).mp hW)
  · have : a * (w * t) * a⁻¹ = (a * w * a⁻¹) * t := by
      calc a * (w * t) * a⁻¹ = (a * w * a⁻¹) * (a * t * a⁻¹) := by group
        _ = (a * w * a⁻¹) * t := by rw [hat']
    rw [this]
    exact mul_mem (mem_sup_left ((mem_normalizer_iff.mp hn w).mp hw))
      (mem_sup_right (mem_zpowers t))

theorem Z_le_O : A ⊓ centralizer (A : Set G) ≤ O := by
  intro z hz
  obtain ⟨hzA, hzC⟩ := Subgroup.mem_inf.mp hz
  have hzcomm : ∀ a ∈ A, a * z = z * a := fun a ha => mem_centralizer_iff.mp hzC a ha
  have hzE : z ∈ centralizer ((W ⊔ zpowers t : Subgroup G) : Set G) := by
    rw [mem_centralizer_iff]
    intro e he
    rcases S.mem_E_iff.mp he with hew | ⟨w, hw, rfl⟩
    · exact hzcomm e (S.W_le_A hew)
    · have hwz : w * z = z * w := hzcomm w (S.W_le_A hw)
      have htz : t * z = z * t := (mem_centralizer_iff.mp S.t_cent z hzA).symm
      calc w * t * z = w * (t * z) := by rw [mul_assoc]
        _ = w * (z * t) := by rw [htz]
        _ = (w * z) * t := by rw [mul_assoc]
        _ = (z * w) * t := by rw [hwz]
        _ = z * (w * t) := by rw [mul_assoc]
  have hzOE : z ∈ O ⊔ (W ⊔ zpowers t) := by
    rw [S.O_sup]
    exact hzE
  obtain ⟨o, ho, e, he, hz_eq⟩ :=
    mem_sup_of_forall_comm (fun o ho e he => S.O_comm ho he) hzOE
  have hoe : Commute o e := S.O_comm ho he
  have hzodd : Odd (orderOf z) :=
    S.odd_inf.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ (Subgroup.mem_inf.mpr ⟨hzA, hzC⟩))
  have hoodd : Odd (orderOf o) := S.odd_orderOf_of_mem_O ho
  have hz1 : z ^ (orderOf z * orderOf o) = 1 := by
    rw [pow_mul, pow_orderOf_eq_one, one_pow]
  have ho1 : o ^ (orderOf z * orderOf o) = 1 := by
    rw [mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]
  have heN : e ^ (orderOf z * orderOf o) = 1 := by
    have h1 : (o * e) ^ (orderOf z * orderOf o) =
        o ^ (orderOf z * orderOf o) * e ^ (orderOf z * orderOf o) := hoe.mul_pow _
    rw [← hz_eq, hz1, ho1, one_mul] at h1
    exact h1.symm
  have he1 : e = 1 := by
    obtain ⟨k, hk⟩ := hzodd.mul hoodd
    have h2 : e ^ 2 = 1 := S.E_elem.2 e he
    calc e = e ^ (2 * k + 1) := by rw [pow_succ, pow_mul, h2, one_pow, one_mul]
      _ = 1 := by rw [← hk]; exact heN
  rw [hz_eq, he1, mul_one]
  exact ho

theorem mem_sup_W_O_of_cent (F : ActionFacts A W) {a : G} (ha : a ∈ A)
    (hc : ∀ w ∈ W, a * w = w * a) : a ∈ W ⊔ O := by
  have h1 : a ∈ W ⊔ centralizer (A : Set G) := F.cent a (Subgroup.le_normalizer ha) hc
  obtain ⟨w, hw, k, hk, rfl⟩ := mem_sup_centralizer S.W_le_A h1
  have hkA : k ∈ A := by
    have := A.mul_mem (A.inv_mem (S.W_le_A hw)) ha
    rwa [inv_mul_cancel_left] at this
  exact Subgroup.mul_mem_sup hw (S.Z_le_O (Subgroup.mem_inf.mpr ⟨hkA, hk⟩))

omit S [Finite G] in
theorem conjQ_apply_of_mem_X (X O : Subgroup G) [(O.subgroupOf X).Normal]
    (n : ↥(normalizer (X : Set G) ⊓ normalizer (O : Set G))) (hnX : (n : G) ∈ X)
    (y : Q25 X O) :
    conjQ X O n y = QuotientGroup.mk ⟨(n : G), hnX⟩ * y * (QuotientGroup.mk ⟨(n : G), hnX⟩)⁻¹ := by
  induction y using QuotientGroup.induction_on with
  | H x =>
    have hx : (n : G) * x * (n : G)⁻¹ ∈ X := X.mul_mem (X.mul_mem hnX x.2) (X.inv_mem hnX)
    rw [conjQ_mk X O n x hx, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul]
    rfl

variable [(O.subgroupOf X).Normal]

theorem conjQ_eq_one_of_mem_sup {n : ↥(normalizer (X : Set G) ⊓ normalizer (O : Set G))}
    (hn : (n : G) ∈ W ⊔ O) : conjQ X O n = 1 := by
  have hnX : (n : G) ∈ X := sup_le S.W_le_X S.O_le_X hn
  obtain ⟨v, hv, o, ho, hvo⟩ := S.mem_sup_W_O hn
  have hmk : (QuotientGroup.mk ⟨(n : G), hnX⟩ : Q25 X O) =
      QuotientGroup.mk ⟨v, S.W_le_X hv⟩ := by
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    show (n : G)⁻¹ * v ∈ O
    have : (n : G)⁻¹ * v = o⁻¹ := by rw [hvo]; group
    rw [this]
    exact O.inv_mem ho
  have hcen : (QuotientGroup.mk ⟨(n : G), hnX⟩ : Q25 X O) ∈ center (Q25 X O) := by
    rw [hmk]
    exact S.phiW_range_le_center ⟨⟨v, hv⟩, rfl⟩
  ext y
  rw [MulAut.one_apply, conjQ_apply_of_mem_X X O n hnX, ← Subgroup.mem_center_iff.mp hcen y,
    mul_inv_cancel_right]

@[expose] noncomputable def actQ (g : G) (hg : g ∈ A) (hn : g ∈ normalizer (W : Set G)) :
    MulAut (Q25 X O) :=
  conjQ X O ⟨g, S.mem_Mx (S.mem_normalizer_E_of_normalizer_W hg hn)⟩

theorem actQ_mk (g : G) (hg : g ∈ A) (hn : g ∈ normalizer (W : Set G)) (x : ↥X)
    (hx : g * x * g⁻¹ ∈ X) :
    S.actQ g hg hn (QuotientGroup.mk x) = QuotientGroup.mk ⟨g * x * g⁻¹, hx⟩ :=
  conjQ_mk X O _ x hx

theorem actQ_eq_one {g : G} (hg : g ∈ A) (hn : g ∈ normalizer (W : Set G)) (F : ActionFacts A W)
    (hc : ∀ w ∈ W, g * w = w * g) : S.actQ g hg hn = (1 : MulAut (Q25 X O)) :=
  S.conjQ_eq_one_of_mem_sup (S.mem_sup_W_O_of_cent F hg hc)

theorem actQ_mul {g h : G} (hg : g ∈ A) (hh : h ∈ A) (hgn : g ∈ normalizer (W : Set G))
    (hhn : h ∈ normalizer (W : Set G)) :
    S.actQ (g * h) (A.mul_mem hg hh) (Subgroup.mul_mem _ hgn hhn) =
      S.actQ g hg hgn * S.actQ h hh hhn := by
  unfold actQ
  rw [← map_mul]
  rfl

theorem actQ_congr_eq {g g' : G} (e : g = g') (hg : g ∈ A) (hg' : g' ∈ A)
    (hn : g ∈ normalizer (W : Set G)) (hn' : g' ∈ normalizer (W : Set G)) :
    S.actQ g hg hn = S.actQ g' hg' hn' := by
  subst e
  rfl

theorem actQ_congr {g g' : G} (hg : g ∈ A) (hg' : g' ∈ A) (hgn : g ∈ normalizer (W : Set G))
    (hgn' : g' ∈ normalizer (W : Set G)) (F : ActionFacts A W)
    (hc : ∀ w ∈ W, g⁻¹ * g' * w = w * (g⁻¹ * g')) :
    S.actQ g' hg' hgn' = S.actQ g hg hgn := by
  have hx : g⁻¹ * g' ∈ A := A.mul_mem (A.inv_mem hg) hg'
  have hxn : g⁻¹ * g' ∈ normalizer (W : Set G) := Subgroup.mul_mem _ (inv_mem hgn) hgn'
  have h1 := S.actQ_eq_one hx hxn F hc
  have h2 := S.actQ_mul hg hx hgn hxn
  rw [h1, mul_one] at h2
  rw [← h2]
  exact S.actQ_congr_eq (by group) _ _ _ _

theorem actQ_tbar {g : G} (hg : g ∈ A) (hn : g ∈ normalizer (W : Set G)) :
    S.actQ g hg hn S.tbar = S.tbar := by
  have hgt : g * t * g⁻¹ = t := by
    rw [mem_centralizer_iff.mp S.t_cent g hg]
    group
  have hx : g * t * g⁻¹ ∈ X := by rw [hgt]; exact S.t_mem_X
  rw [IsSetting25.tbar, S.actQ_mk g hg hn ⟨t, S.t_mem_X⟩ hx]
  congr 1
  exact Subtype.ext hgt

section Alpha

open CFSG.ComponentClassification.PSL3Four

variable (L : Levi.LeviData A W) (F : ActionFacts A W)

@[expose] noncomputable def alphaUp : Multiplicative F4 →* MulAut (Q25 X O) where
  toFun γ := S.actQ (L.u (Multiplicative.toAdd γ)) (L.u_mem _) (L.act_u _).mem_normalizer
  map_one' := by
    have h0 : Levi.ActsAs L.ι (L.u (Multiplicative.toAdd (1 : Multiplicative F4))) id :=
      (L.act_u _).congr (by rw [toAdd_one]; exact Levi.cUp_zero_fun)
    exact S.actQ_eq_one _ _ F fun w hw => h0.comm_of_id hw
  map_mul' γ γ' := by
    rw [toAdd_mul, ← S.actQ_mul]
    refine S.actQ_congr _ _ _ _ F fun w hw => ?_
    exact Levi.ActsAs.comm_of_same
      (((L.act_u _).comp (L.act_u _)).congr (Levi.cUp_add_fun _ _).symm) (L.act_u _) hw

@[expose] noncomputable def alphaLow : Multiplicative F4 →* MulAut (Q25 X O) where
  toFun γ := S.actQ (L.l (Multiplicative.toAdd γ)) (L.l_mem _) (L.act_l _).mem_normalizer
  map_one' := by
    have h0 : Levi.ActsAs L.ι (L.l (Multiplicative.toAdd (1 : Multiplicative F4))) id :=
      (L.act_l _).congr (by rw [toAdd_one]; exact Levi.cLow_zero_fun)
    exact S.actQ_eq_one _ _ F fun w hw => h0.comm_of_id hw
  map_mul' γ γ' := by
    rw [toAdd_mul, ← S.actQ_mul]
    refine S.actQ_congr _ _ _ _ F fun w hw => ?_
    exact Levi.ActsAs.comm_of_same
      (((L.act_l _).comp (L.act_l _)).congr (Levi.cLow_add_fun _ _).symm) (L.act_l _) hw

@[expose] noncomputable def alphaTor : MulAut (Q25 X O) :=
  S.actQ L.τ L.τ_mem L.act_τ.mem_normalizer

theorem alphaTor_cube (F : ActionFacts A W) : S.alphaTor L ^ 3 = 1 := by
  have hτ := L.act_τ
  have h3 : Levi.ActsAs L.ι (L.τ * (L.τ * L.τ)) id :=
    (hτ.comp (hτ.comp hτ)).congr Levi.dTor_cube_fun
  have hA : L.τ * (L.τ * L.τ) ∈ A := A.mul_mem L.τ_mem (A.mul_mem L.τ_mem L.τ_mem)
  have h1 := S.actQ_eq_one hA h3.mem_normalizer F fun w hw => h3.comm_of_id hw
  have h2 := S.actQ_mul L.τ_mem (A.mul_mem L.τ_mem L.τ_mem) hτ.mem_normalizer
    (hτ.comp hτ).mem_normalizer
  have h4 := S.actQ_mul L.τ_mem L.τ_mem hτ.mem_normalizer hτ.mem_normalizer
  rw [h4, h1] at h2
  rw [pow_three]
  exact h2.symm

theorem alphaUp_phiW (γ : F4) (w : ↥W) :
    S.alphaUp L F (Multiplicative.ofAdd γ) (S.phiW w) =
      S.phiW ⟨L.u γ * (w : G) * (L.u γ)⁻¹, (L.act_u γ).conj_mem w⟩ :=
  S.actQ_mk (L.u γ) (L.u_mem γ) (L.act_u γ).mem_normalizer ⟨(w : G), S.W_le_X w.2⟩
    (S.W_le_X ((L.act_u γ).conj_mem w))

theorem alphaLow_phiW (γ : F4) (w : ↥W) :
    S.alphaLow L F (Multiplicative.ofAdd γ) (S.phiW w) =
      S.phiW ⟨L.l γ * (w : G) * (L.l γ)⁻¹, (L.act_l γ).conj_mem w⟩ :=
  S.actQ_mk (L.l γ) (L.l_mem γ) (L.act_l γ).mem_normalizer ⟨(w : G), S.W_le_X w.2⟩
    (S.W_le_X ((L.act_l γ).conj_mem w))

theorem alphaTor_phiW (w : ↥W) :
    S.alphaTor L (S.phiW w) = S.phiW ⟨L.τ * (w : G) * L.τ⁻¹, L.act_τ.conj_mem w⟩ :=
  S.actQ_mk L.τ L.τ_mem L.act_τ.mem_normalizer ⟨(w : G), S.W_le_X w.2⟩
    (S.W_le_X (L.act_τ.conj_mem w))

theorem alphaUp_tbar (γ : F4) : S.alphaUp L F (Multiplicative.ofAdd γ) S.tbar = S.tbar :=
  S.actQ_tbar (L.u_mem γ) (L.act_u γ).mem_normalizer

theorem alphaLow_tbar (γ : F4) : S.alphaLow L F (Multiplicative.ofAdd γ) S.tbar = S.tbar :=
  S.actQ_tbar (L.l_mem γ) (L.act_l γ).mem_normalizer

theorem alphaTor_tbar : S.alphaTor L S.tbar = S.tbar :=
  S.actQ_tbar L.τ_mem L.act_τ.mem_normalizer

end Alpha

end IsSetting25

end CFSG.OddStandard.Seitz77
