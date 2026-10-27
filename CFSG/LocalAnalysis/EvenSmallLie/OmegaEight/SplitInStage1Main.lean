module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SplitInStage1N
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainModule
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.N3SplitDefs
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SplitInMain

public section

namespace CFSG.EvenSmallLie.OmegaEight.SplitIn

open Subgroup Matrix CFSG.EvenSmallLie.OmegaEight.Stage1
open CFSG.EvenSmallLie.UnitarySix.YamadaPar
open CFSG.EvenSmallLie.OmegaEight.CPrime (reflRows)
open CFSG.EvenSmallLie.OmegaEight.N3Split (snoc7 splitPr splitUr)

variable {G : Type} [Group G]

theorem sup_zpowers_t_mul_eq {t x₀ : G} (K : Subgroup G) :
    K ⊔ zpowers (t * x₀) ⊔ zpowers t = K ⊔ zpowers x₀ ⊔ zpowers t := by
  apply le_antisymm
  · refine sup_le (sup_le (le_sup_left.trans le_sup_left) (zpowers_le.2 ?_)) le_sup_right
    exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left (mem_sup_right (mem_zpowers x₀)))
  · refine sup_le (sup_le (le_sup_left.trans le_sup_left) (zpowers_le.2 ?_)) le_sup_right
    have h : t⁻¹ * (t * x₀) ∈ K ⊔ zpowers (t * x₀) ⊔ zpowers t :=
      mul_mem (inv_mem (mem_sup_right (mem_zpowers t)))
        (mem_sup_left (mem_sup_right (mem_zpowers (t * x₀))))
    rwa [inv_mul_cancel_left] at h

namespace SetupX

variable {ε : Eps} {t : G} {L H₀ U Q P : Subgroup G} {a : G} {ψ : V6 → G} {p u : Fin 6 → G}
  {x₀ : G} (hS : SetupX ε t L H₀ U Q P a ψ p u x₀) (hZ : ∀ v, v ∈ Zset t Q ψ)
include hS hZ

theorem tauD_inv {d : G} (hd : d ∈ Dsub t Q) : tauD t ψ d⁻¹ = tauD t ψ d := by
  have h := hS.tauD_mul hZ hd (inv_mem hd)
  rw [mul_inv_cancel, (hS.tauD_eq_zero_iff hZ (one_mem _)).2 (one_mem _)] at h
  have h2 : tauD t ψ d + tauD t ψ d = 0 := CharTwo.add_self_eq_zero _
  calc tauD t ψ d⁻¹ = tauD t ψ d + (tauD t ψ d + tauD t ψ d⁻¹) := by
        rw [← add_assoc, h2, zero_add]
    _ = tauD t ψ d := by rw [← h, add_zero]

theorem conj_rY_of_mem_P [Finite G] (hW2 : ∀ w ∈ hS.Wsub hZ, w * w = 1) {X : Mat6}
    (hX : ∀ i : Fin 6, hS.kapG hZ i = genMat ε i * X + X * genMat ε i) {x : G} (hx : x ∈ P)
    (v : V6) : x * hS.rY hZ X v * x⁻¹ = hS.rY hZ X (lin ψ x v) := by
  have hmem : x * hS.rY hZ X v * x⁻¹ ∈ hS.Rsub hZ hW2 X :=
    (mem_normalizer_iff.1 (hS.P_le_normalizer_Rsub hZ hW2 hX hx) _).1
      ((hS.mem_Rsub hZ).2 ⟨v, rfl⟩)
  obtain ⟨w, hw⟩ := (hS.mem_Rsub hZ).1 hmem
  have h1 := hS.tauD_conj hZ hx (hS.Wsub_le_D hZ (hS.rY_mem hZ X v))
  rw [hS.tauD_rY, ← hw, hS.tauD_rY] at h1
  rw [← hw, h1]

theorem conj_t_rY [Finite G] (X : Mat6) (u : V6) :
    t * hS.rY hZ X u * t⁻¹ = ψ u * hS.rY hZ X u := by
  set r := hS.rY hZ X u
  have hr : r ∈ Dsub t Q := hS.Wsub_le_D hZ (hS.rY_mem hZ X u)
  have h1 := hS.kap_t_right hZ hr
  rw [hS.tauD_rY] at h1
  have hq := hS.commute_ψ u
  rw [kap] at h1
  have h2 : r * t * r⁻¹ = ψ u * t := by
    calc r * t * r⁻¹ = r * t * r⁻¹ * t⁻¹ * t := by group
      _ = ψ u * t := by rw [h1]
  have h3 : r * t = ψ u * t * r := by
    calc r * t = r * t * r⁻¹ * r := by group
      _ = ψ u * t * r := by rw [h2]
  rw [hS.shape.inv_eq]
  calc t * r * t = t * (r * t) := by group
    _ = t * (ψ u * t * r) := by rw [h3]
    _ = t * ψ u * t * r := by group
    _ = ψ u * t * t * r := by rw [← hq]
    _ = ψ u * (t * t) * r := by group
    _ = ψ u * r := by rw [hS.shape.mul_self, mul_one]

theorem normalizes_R_or [Finite G] (hW2 : ∀ w ∈ hS.Wsub hZ, w * w = 1) {X : Mat6}
    (hX : ∀ i : Fin 6, hS.kapG hZ i = genMat ε i * X + X * genMat ε i) :
    (∀ r ∈ hS.Rsub hZ hW2 X, x₀ * r * x₀⁻¹ ∈ hS.Rsub hZ hW2 X) ∨
      ∀ r ∈ hS.Rsub hZ hW2 X, t * x₀ * r * (t * x₀)⁻¹ ∈ hS.Rsub hZ hW2 X := by
  set R₀ : Matrix (Fin 6) (Fin 6) (ZMod 2) := toMat 6 6 (reflRows ε (n0 ε)) with hR₀
  have hO := hS.inputs.outer
  have hx₀N := hS.x₀_mem_normalizer_Q
  have hx₀E := hS.x₀_mem_normalizer_E
  have hx₀C : x₀ * t = t * x₀ := mem_centralizer_singleton_iff.1
    (hS.K_le_centralizer (mem_sup_right (mem_zpowers x₀)))
  have hlin₀ : ∀ v, lin ψ x₀ v = R₀ *ᵥ v := fun v => (hS.rad.lin_eq_iff hx₀N v _).2 (hO.act v)
  have hR₀2 : ∀ v, R₀ *ᵥ (R₀ *ᵥ v) = v := by
    intro v
    have h1 := hS.rad.lin_mul hx₀N hx₀N v
    rw [hO.sq, hS.rad.lin_one, hlin₀, hlin₀] at h1
    exact h1.symm
  have hx₀inv : x₀⁻¹ = x₀ := inv_eq_of_mul_eq_one_right hO.sq
  have hxt : x₀⁻¹ * t * x₀ = t := by rw [mul_assoc, ← hx₀C, inv_mul_cancel_left]
  have hx₀W : x₀ ∈ normalizer (hS.Wsub hZ : Set G) :=
    hS.normalizer_E_le_normalizer_Wsub hZ hx₀E
  have hrW : ∀ v, hS.rY hZ X v ∈ hS.Wsub hZ := fun v => hS.rY_mem hZ X v
  have hrD : ∀ v, hS.rY hZ X v ∈ Dsub t Q := fun v => hS.Wsub_le_D hZ (hrW v)
  have hrtau : ∀ v, tauD t ψ (hS.rY hZ X v) = v := hS.tauD_rY hZ X
  have hradd : ∀ v w, hS.rY hZ X (v + w) = hS.rY hZ X v * hS.rY hZ X w := hS.rY_add hZ hW2 X
  have hrgen : ∀ (i : Fin 6) v, p i * hS.rY hZ X v * (p i)⁻¹ = hS.rY hZ X (genMat ε i *ᵥ v) :=
    hS.conj_rY_gen hZ hW2 hX
  have hrP : ∀ x ∈ P, ∀ v, x * hS.rY hZ X v * x⁻¹ = hS.rY hZ X (lin ψ x v) :=
    fun x hx v => hS.conj_rY_of_mem_P hZ hW2 hX hx v
  have hrt : ∀ v, t * hS.rY hZ X v * t⁻¹ = ψ v * hS.rY hZ X v := hS.conj_t_rY hZ X
  have hrmem : ∀ v, hS.rY hZ X v ∈ hS.Rsub hZ hW2 X := fun v => (hS.mem_Rsub hZ).2 ⟨v, rfl⟩
  have hrsub : ∀ r ∈ hS.Rsub hZ hW2 X, ∃ v, hS.rY hZ X v = r := fun r hr => (hS.mem_Rsub hZ).1 hr
  set rY := hS.rY hZ X with hrY
  have hconjD : ∀ v, x₀ * rY v * x₀⁻¹ ∈ Dsub t Q := fun v =>
    hS.conj_mem_D_of_normalizer hZ hx₀E (hrD v)
  have htau : ∀ v, tauD t ψ (x₀ * rY v * x₀⁻¹) = R₀ *ᵥ v := by
    intro v
    have h1 := hS.conj_t_D hZ (hconjD v)
    have h2 := hS.conj_t_D hZ (hrD v)
    rw [hrtau] at h2
    have h3 : x₀ * rY v * x₀⁻¹ * t * (x₀ * rY v * x₀⁻¹)⁻¹ = t * ψ (R₀ *ᵥ v) := by
      calc x₀ * rY v * x₀⁻¹ * t * (x₀ * rY v * x₀⁻¹)⁻¹ =
          x₀ * (rY v * (x₀⁻¹ * t * x₀) * (rY v)⁻¹) * x₀⁻¹ := by group
        _ = x₀ * (t * ψ v) * x₀⁻¹ := by rw [hxt, h2]
        _ = (x₀ * t * x₀⁻¹) * (x₀ * ψ v * x₀⁻¹) := by group
        _ = t * ψ (R₀ *ᵥ v) := by rw [hx₀C, mul_inv_cancel_right, hO.act]
    rw [h1] at h3
    exact hS.rad.ψ_inj (mul_left_cancel h3)
  have hdec : ∀ v, x₀ * rY v * x₀⁻¹ * (rY (R₀ *ᵥ v))⁻¹ ∈ Q := by
    intro v
    have hW : x₀ * rY v * x₀⁻¹ ∈ hS.Wsub hZ := (mem_normalizer_iff.1 hx₀W _).1 (hrW v)
    refine hS.mem_Q_of_mem_Wsub hZ (mul_mem hW (inv_mem (hrW _))) ?_
    rw [hS.tauD_mul hZ (hconjD v) (inv_mem (hrD _)), hS.tauD_inv hZ (hrD _), htau, hrtau]
    exact CharTwo.add_self_eq_zero _
  set g : V6 → V6 := fun v => coord ψ (x₀ * rY v * x₀⁻¹ * (rY (R₀ *ᵥ v))⁻¹) with hgdef
  have hg : ∀ v, x₀ * rY v * x₀⁻¹ = ψ (g v) * rY (R₀ *ᵥ v) := by
    intro v
    show x₀ * rY v * x₀⁻¹ = ψ (coord ψ (x₀ * rY v * x₀⁻¹ * (rY (R₀ *ᵥ v))⁻¹)) * rY (R₀ *ᵥ v)
    rw [hS.rad.ψ_coord (hdec v)]
    group
  have hψW : ∀ v, ψ v ∈ hS.Wsub hZ := fun v => hS.Q_le_Wsub hZ (hS.rad.ψ_mem v)
  have hcancel : ∀ a a' b, ψ a * rY b = ψ a' * rY b → a = a' := fun a a' b h =>
    hS.rad.ψ_inj (mul_right_cancel h)
  have hgadd : ∀ v w, g (v + w) = g v + g w := by
    intro v w
    apply hcancel _ _ (R₀ *ᵥ (v + w))
    rw [← hg, hradd, mulVec_add, hradd, hS.rad.ψ_add]
    have hc := hS.Wsub_comm hZ (hrW (R₀ *ᵥ v)) (hψW (g w))
    calc x₀ * (rY v * rY w) * x₀⁻¹ = (x₀ * rY v * x₀⁻¹) * (x₀ * rY w * x₀⁻¹) := by group
      _ = ψ (g v) * (rY (R₀ *ᵥ v) * ψ (g w)) * rY (R₀ *ᵥ w) := by rw [hg, hg]; group
      _ = ψ (g v) * (ψ (g w) * rY (R₀ *ᵥ v)) * rY (R₀ *ᵥ w) := by rw [hc]
      _ = ψ (g v) * ψ (g w) * (rY (R₀ *ᵥ v) * rY (R₀ *ᵥ w)) := by group
  have hgeq : ∀ (i : Fin 6) v, g (genMat ε i *ᵥ v) = R₀ *ᵥ (genMat ε i *ᵥ (R₀ *ᵥ g v)) := by
    intro i v
    set y := x₀ * p i * x₀⁻¹ with hy
    have hyP : y ∈ P := hS.x₀_conj_mem_P (hS.rad.p_mem i)
    have hlinY : ∀ w, lin ψ y w = R₀ *ᵥ (genMat ε i *ᵥ (R₀ *ᵥ w)) := by
      intro w
      rw [hy, hS.rad.lin_mul (mul_mem hx₀N (hS.rad.p_mem_normalizer i)) (inv_mem hx₀N),
        hS.rad.lin_mul hx₀N (hS.rad.p_mem_normalizer i), hx₀inv, hlin₀, hlin₀, hS.rad.lin_p]
    apply hcancel _ _ (R₀ *ᵥ (genMat ε i *ᵥ v))
    rw [← hg, ← hrgen]
    calc x₀ * (p i * rY v * (p i)⁻¹) * x₀⁻¹ = y * (x₀ * rY v * x₀⁻¹) * y⁻¹ := by
          rw [hy]; group
      _ = y * ψ (g v) * y⁻¹ * (y * rY (R₀ *ᵥ v) * y⁻¹) := by rw [hg]; group
      _ = ψ (lin ψ y (g v)) * rY (lin ψ y (R₀ *ᵥ v)) := by
          rw [hS.rad.ψ_lin (hS.rad.P_le_normalizer hyP), hrP y hyP]
      _ = ψ (R₀ *ᵥ (genMat ε i *ᵥ (R₀ *ᵥ g v))) * rY (R₀ *ᵥ (genMat ε i *ᵥ v)) := by
          rw [hlinY, hlinY, hR₀2]
  have hF := Chain.endF2 ε (fun v => R₀ *ᵥ g v) (fun v w => by rw [hgadd, mulVec_add])
    (fun i v => by rw [hgeq, hR₀2])
  rcases hF with h0 | h1
  · left
    intro r hr
    obtain ⟨v, rfl⟩ := hrsub r hr
    have hgv : g v = 0 := by rw [← hR₀2 (g v), h0 v, mulVec_zero]
    rw [hg, hgv, hS.rad.ψ_zero, one_mul]
    exact hrmem _
  · right
    intro r hr
    obtain ⟨v, rfl⟩ := hrsub r hr
    have hgv : g v = R₀ *ᵥ v := by rw [← hR₀2 (g v), h1 v]
    have e : x₀ * rY v * x₀⁻¹ = t * rY (R₀ *ᵥ v) * t⁻¹ := by rw [hg, hgv, hrt]
    have e2 : t * x₀ * rY v * (t * x₀)⁻¹ = rY (R₀ *ᵥ v) := by
      calc t * x₀ * rY v * (t * x₀)⁻¹ = t * (x₀ * rY v * x₀⁻¹) * t⁻¹ := by group
        _ = t * (t * rY (R₀ *ᵥ v) * t⁻¹) * t⁻¹ := by rw [e]
        _ = (t * t) * rY (R₀ *ᵥ v) * (t * t)⁻¹ := by group
        _ = rY (R₀ *ᵥ v) := by rw [hS.shape.mul_self, one_mul, inv_one, mul_one]
    rw [e2]
    exact hrmem _



theorem Wsub_sq [Finite G] (hL9 : L9 t Q) : ∀ w ∈ hS.Wsub hZ, w * w = 1 :=
  hL9 _ (hS.Q_le_Wsub hZ) (hS.t_not_mem_Wsub hZ) (hS.card_Wsub hZ)
    (fun _ hx _ hy => hS.Wsub_comm hZ hx hy)
    (fun _ hn w hw => (mem_normalizer_iff.1 (hS.normalizer_E_le_normalizer_Wsub hZ hn) w).1 hw)

theorem exists_bridgeCore [Finite G] (hL9 : L9 t Q) :
    ∃ (y : G) (R W : Subgroup G), (y = x₀ ∨ y = t * x₀) ∧
      Stage2.BridgeCore t Q R W (P ⊔ zpowers y) (U ⊔ zpowers y) ψ (splitPr ε) (snoc7 p y)
        (splitUr ε) (snoc7 u y) := by
  have hW2 := hS.Wsub_sq hZ hL9
  obtain ⟨X, hX⟩ := hS.exists_X hZ hW2
  have hO := hS.inputs.outer
  have hF := hS.inputs.link
  have hx₀C : x₀ ∈ centralizer ({t} : Set G) := hS.K_le_centralizer (mem_sup_right (mem_zpowers x₀))
  have htC : t ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.2 rfl
  have hx₀t : x₀ * t = t * x₀ := mem_centralizer_singleton_iff.1 hx₀C
  have htE : t ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) :=
    le_normalizer (mem_sup_right (mem_zpowers t))
  obtain ⟨y, hyx, hyR⟩ : ∃ y, (y = x₀ ∨ y = t * x₀) ∧
      ∀ r ∈ hS.Rsub hZ hW2 X, y * r * y⁻¹ ∈ hS.Rsub hZ hW2 X := by
    rcases hS.normalizes_R_or hZ hW2 hX with h | h
    · exact ⟨x₀, Or.inl rfl, h⟩
    · exact ⟨t * x₀, Or.inr rfl, h⟩
  have hyC : y ∈ centralizer ({t} : Set G) := by
    rcases hyx with rfl | rfl
    · exact hx₀C
    · exact mul_mem htC hx₀C
  have hysq : y * y = 1 := by
    rcases hyx with rfl | rfl
    · exact hO.sq
    · calc t * x₀ * (t * x₀) = t * (x₀ * t) * x₀ := by group
        _ = t * t * (x₀ * x₀) := by rw [hx₀t]; group
        _ = 1 := by rw [hS.shape.mul_self, hO.sq, one_mul]
  have hyact : ∀ v, y * ψ v * y⁻¹ = ψ (toMat 6 6 (reflRows ε (n0 ε)) *ᵥ v) := by
    intro v
    rcases hyx with rfl | rfl
    · exact hO.act v
    · calc t * x₀ * ψ v * (t * x₀)⁻¹ = t * (x₀ * ψ v * x₀⁻¹) * t⁻¹ := by group
        _ = ψ (toMat 6 6 (reflRows ε (n0 ε)) *ᵥ v) := by
            rw [hO.act, ← hS.commute_ψ, mul_inv_cancel_right]
  have hyE : y ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) := by
    rcases hyx with rfl | rfl
    · exact hS.x₀_mem_normalizer_E
    · exact mul_mem htE hS.x₀_mem_normalizer_E
  have hyW := hS.normalizer_E_le_normalizer_Wsub hZ hyE
  have hyRN : y ∈ normalizer (hS.Rsub hZ hW2 X : Set G) :=
    Stage0.mem_normalizer_of_mul_self hysq hyR
  have hsup : ∀ K : Subgroup G, K ⊔ zpowers y ⊔ zpowers t = K ⊔ zpowers x₀ ⊔ zpowers t := by
    intro K
    rcases hyx with rfl | rfl
    · rfl
    · exact sup_zpowers_t_mul_eq K
  have hrange : ∀ f : Fin 6 → G, Set.range f ⊆ Set.range (snoc7 f y) := by
    rintro f _ ⟨i, rfl⟩
    exact ⟨⟨i, by omega⟩, N3Split.snoc7_lt f y i⟩
  have hsix : ∀ f : Fin 6 → G, y ∈ Set.range (snoc7 f y) := fun f => ⟨6, N3Split.snoc7_six f y⟩
  refine ⟨y, hS.Rsub hZ hW2 X, hS.Wsub hZ, hyx, ?_⟩
  exact
    { coord :=
        { comm := fun _ hx _ hy => hS.Wsub_comm hZ hx hy
          sq_eq_one := hW2
          card_eq := hS.card_Wsub hZ
          Q_le_W := hS.Q_le_Wsub hZ
          R_le_W := hS.Rsub_le_Wsub hZ hW2 X
          inf_eq := hS.inf_Rsub hZ hW2 X
          sup_eq := hS.sup_Rsub hZ hW2 X
          t_mem := hS.t_mem_normalizer_Wsub hZ
          t_sq := hS.shape.mul_self
          Q_comm := fun _ hq => hS.shape.commute_of_mem (hS.rad.Q_le_L hq)
          comm_mem := fun _ hr => hS.commutator_mem_Rsub hZ hW2 hr
          comm_eq_one := fun _ hr h => hS.commutator_eq_one_Rsub hZ hW2 hr h
          ψ_add := hS.rad.ψ_add
          ψ_inj := hS.rad.ψ_inj
          ψ_mem := hS.rad.ψ_mem
          mem_ψ := hS.rad.mem_ψ }
      orderOf_t := hS.shape.orderOf_eq
      P_le_normalizer := sup_le (hS.P_le_normalizer_Wsub hZ) (zpowers_le.2 hyW)
      P_le_normalizer_R := sup_le (hS.P_le_normalizer_Rsub hZ hW2 hX) (zpowers_le.2 hyRN)
      P_le_centralizer := sup_le (hS.rad.P_le_L.trans hS.shape.le_centralizer) (zpowers_le.2 hyC)
      p_mem := fun i => by
        unfold snoc7
        split_ifs
        · exact mem_sup_left (hS.rad.p_mem _)
        · exact mem_sup_right (mem_zpowers y)
      p_act := fun i x => by
        unfold snoc7 splitPr snoc7
        split_ifs
        · exact hS.rad.p_act _ x
        · exact hyact x
      P_le := sup_le (hS.rad.P_le.trans (closure_mono (Set.union_subset_union_right _
        (hrange p)))) (zpowers_le.2 (subset_closure (Or.inr (hsix p))))
      U_le_P := sup_le_sup_right hS.rad.U_le_P _
      u_mem := fun k => by
        unfold snoc7
        split_ifs
        · exact mem_sup_left (hF.u_mem _)
        · exact mem_sup_right (mem_zpowers y)
      u_act := fun k x => by
        unfold snoc7 splitUr snoc7
        split_ifs
        · exact hF.u_act _ x
        · exact hyact x
      U_le := sup_le (hF.U_le.trans (closure_mono (Set.union_subset_union_right _
        (hrange u)))) (zpowers_le.2 (subset_closure (Or.inr (hsix u))))
      TH_pgroup := by
        rw [hsup]
        exact hS.inputs.setting.isPGroup_TH
      TH_max := by
        rw [hsup]
        exact hS.inputs.setting.data.sylow
      sylow_W := hS.sylow_Wsub hZ hW2
      centralizer_t := fun x hx hc => by
        rw [hsup]
        exact hS.mem_sup_of_comm hZ hW2 hx hc }

end SetupX

@[expose] def L9Split (ε : Eps) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L H₀ U Q P : Subgroup G) (a : G) (ψ : V6 → G)
    (p u : Fin 6 → G) (x₀ : G), HypSplit G L ε → Stage0.StepK t L → SplitShape t L H₀ x₀ →
      Inputs ε t L H₀ U Q P a ψ p u x₀ → (∀ v, v ∈ Zset t Q ψ) → L9 t Q

@[expose] def Bridge64 (ε : Eps) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L H₀ U Q P : Subgroup G) (a : G) (ψ : V6 → G)
    (p u : Fin 6 → G) (x₀ : G), HypSplit G L ε → Stage0.StepK t L → SplitShape t L H₀ x₀ →
      Inputs ε t L H₀ U Q P a ψ p u x₀ → (∀ v, v ∈ Zset t Q ψ) →
      ∃ (y : G) (R W : Subgroup G), (y = x₀ ∨ y = t * x₀) ∧
        Stage2.BridgeCore t Q R W (P ⊔ zpowers y) (U ⊔ zpowers y) ψ (splitPr ε) (snoc7 p y)
          (splitUr ε) (snoc7 u y)

theorem bridge64_of_L9Split {ε : Eps} (h : L9Split ε) : Bridge64 ε :=
  fun G _ _ t L H₀ U Q P a ψ p u x₀ hH hK hsh hI hZ =>
    (SetupX.of_inputs hK hI).exists_bridgeCore hZ (h G t L H₀ U Q P a ψ p u x₀ hH hK hsh hI hZ)

end CFSG.EvenSmallLie.OmegaEight.SplitIn
