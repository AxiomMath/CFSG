module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixMGOne

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial

section Lift

variable {G : Type*} [Group G] {t : G}

theorem eq_of_mem_of_diag_eq {A : Subgroup G}
    (hA : A.map (MulAut.conj t).toMonoidHom ≤ centralizer (A : Set G))
    (hAA : A ⊓ A.map (MulAut.conj t).toMonoidHom = ⊥) {a b : G} (ha : a ∈ A) (hb : b ∈ A)
    (h : a * (t * a * t⁻¹) = b * (t * b * t⁻¹)) : a = b := by
  have := linearSwapDiag_injective hA hAA (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) h
  exact congrArg Subtype.val this

theorem conj_mul_comm_of_mem {A : Subgroup G}
    (hA : A.map (MulAut.conj t).toMonoidHom ≤ centralizer (A : Set G)) {a x : G} (ha : a ∈ A)
    (hx : x ∈ A) : (t * a * t⁻¹) * x = x * (t * a * t⁻¹) :=
  (mem_centralizer_iff.1 (hA ⟨a, ha, rfl⟩) x hx).symm

theorem swapDiag_mul {A : Subgroup G}
    (hA : A.map (MulAut.conj t).toMonoidHom ≤ centralizer (A : Set G)) {a b : G} (ha : a ∈ A)
    (hb : b ∈ A) :
    (a * b) * (t * (a * b) * t⁻¹) = (a * (t * a * t⁻¹)) * (b * (t * b * t⁻¹)) := by
  have hc := conj_mul_comm_of_mem hA ha hb
  calc (a * b) * (t * (a * b) * t⁻¹) = a * (b * (t * a * t⁻¹)) * (t * b * t⁻¹) := by group
    _ = a * ((t * a * t⁻¹) * b) * (t * b * t⁻¹) := by rw [hc]
    _ = (a * (t * a * t⁻¹)) * (b * (t * b * t⁻¹)) := by group

theorem diag_conj_eq_conj {A : Subgroup G}
    (hA : A.map (MulAut.conj t).toMonoidHom ≤ centralizer (A : Set G)) {a x : G} (ha : a ∈ A)
    (hx : x ∈ A) :
    (a * (t * a * t⁻¹)) * x * (a * (t * a * t⁻¹))⁻¹ = a * x * a⁻¹ := by
  have hc := conj_mul_comm_of_mem hA ha hx
  calc (a * (t * a * t⁻¹)) * x * (a * (t * a * t⁻¹))⁻¹
        = a * ((t * a * t⁻¹) * x) * (t * a * t⁻¹)⁻¹ * a⁻¹ := by group
    _ = a * (x * (t * a * t⁻¹)) * (t * a * t⁻¹)⁻¹ * a⁻¹ := by rw [hc]
    _ = a * x * a⁻¹ := by group

theorem conj_t_eq_of_diag {x y : G} (hx : x * x = 1) (hxt : x * (t * x * t⁻¹) = (t * x * t⁻¹) * x)
    (hy : x * (t * x * t⁻¹) = y) : x * t * x⁻¹ = y⁻¹ * t := by
  have hinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  subst hy
  calc x * t * x⁻¹ = (x * (t * x * t⁻¹))⁻¹ * (x * (t * x * t⁻¹)) * x * t * x⁻¹ := by group
    _ = (x * (t * x * t⁻¹))⁻¹ * ((t * x * t⁻¹) * x) * x * t * x⁻¹ := by rw [hxt]
    _ = (x * (t * x * t⁻¹))⁻¹ * (t * x * t⁻¹) * (x * x) * t * x⁻¹ := by group
    _ = (x * (t * x * t⁻¹))⁻¹ * t * (x * x⁻¹) := by rw [hx, hinv]; group
    _ = (x * (t * x * t⁻¹))⁻¹ * t := by group

theorem inv_mul_mem_centralizer_of_diag_eq {x x' : G} (hx : x * x = 1) (hx' : x' * x' = 1)
    (hxt : x * (t * x * t⁻¹) = (t * x * t⁻¹) * x)
    (hxt' : x' * (t * x' * t⁻¹) = (t * x' * t⁻¹) * x')
    (h : x * (t * x * t⁻¹) = x' * (t * x' * t⁻¹)) : x'⁻¹ * x ∈ centralizer ({t} : Set G) := by
  have h1 := conj_t_eq_of_diag hx hxt rfl
  have h2 := conj_t_eq_of_diag hx' hxt' rfl
  rw [← h] at h2
  rw [mem_centralizer_singleton_iff]
  have h3 : x * t * x⁻¹ = x' * t * x'⁻¹ := by rw [h1, h2]
  calc x'⁻¹ * x * t = x'⁻¹ * (x * t * x⁻¹) * x := by group
    _ = x'⁻¹ * (x' * t * x'⁻¹) * x := by rw [h3]
    _ = t * (x'⁻¹ * x) := by group

theorem conj_t_conj_of_commute {w a : G} (hw : w * t = t * w) :
    t * (w * a * w⁻¹) * t⁻¹ = w * (t * a * t⁻¹) * w⁻¹ := by
  calc t * (w * a * w⁻¹) * t⁻¹ = (t * w) * a * (t * w)⁻¹ := by group
    _ = (w * t) * a * (w * t)⁻¹ := by rw [hw]
    _ = w * (t * a * t⁻¹) * w⁻¹ := by group

theorem diag_conj {w a : G} (hw : w * t = t * w) :
    (w * a * w⁻¹) * (t * (w * a * w⁻¹) * t⁻¹) = w * (a * (t * a * t⁻¹)) * w⁻¹ := by
  rw [conj_t_conj_of_commute hw]
  group

theorem conj_mem_map_conj_t {A : Subgroup G} {a : G} (ha : a ∈ A) :
    t * a * t⁻¹ ∈ A.map (MulAut.conj t).toMonoidHom :=
  ⟨a, ha, rfl⟩

end Lift

section Point

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {K : Type} [Field K]
  [CharP K 2]

omit [CharP K 2] in
theorem swapModuleData_split (hn : 4 ≤ n) (hK : Nat.card K = 2)
    (e : L ≃* LinearFlag.projectiveSL n K) {t : G} (ht : t * t = 1)
    (htC : t ∈ centralizer (L : Set G)) {c : Fin n} {W X : Subgroup G}
    (hdata : LinearTwoSwapModuleData e t c W X) :
    X.map (MulAut.conj t).toMonoidHom ≤ centralizer (X : Set G) ∧
      X ⊓ X.map (MulAut.conj t).toMonoidHom = ⊥ ∧
      modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin n))) ≤
        X ⊔ X.map (MulAut.conj t).toMonoidHom ∧
      W ⊓ centralizer (modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin n))) : Set G) = ⊥ := by
  obtain ⟨hW2, hWc, hWt, htW, hLW, hXp, hXW, hWX, hXY, hXYW, hD, hne⟩ := hdata
  have hDt : modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin n))) ≤
      centralizer ({t} : Set G) := fun x hx =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC x (modelToG_le e _ hx))
  have hW : ∀ v ∈ W, ∀ w ∈ W, v * w = w * v := fun v hv w hw =>
    mul_comm_of_forall_mul_self_eq_one hW2 hv hw
  have hirr : ∀ S : Subgroup G, S ≤ W ⊓ centralizer ({t} : Set G) →
      modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin n))) ≤ normalizer (S : Set G) →
      S = ⊥ ∨ S = W ⊓ centralizer ({t} : Set G) := by
    intro S hS hN
    rw [hWt] at hS ⊢
    exact modelToG_pointRadical_irreducible hK e c hS hN
  have hVc : Nat.card (W ⊓ centralizer ({t} : Set G) : Subgroup G) = 2 ^ (n - 1) :=
    card_inf_centralizer_eq_of_pointRadical hK e hWt
  have hnt : ¬ (W ⊓ centralizer ({t} : Set G) ≤
      centralizer (modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin n))) : Set G)) := by
    have h4 : 4 < Nat.card (modelToG e (pointRadical (K := K) c)) := by
      rw [← hWt, hVc]
      calc 4 < 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [hWt]
    exact not_modelToG_pointRadical_le_centralizer hK e c h4
  have hfix : W ⊓ centralizer
      (modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin n))) : Set G) = ⊥ :=
    inf_centralizer_eq_bot_of_irreducible hW hW2 ht htW hDt hLW hirr hnt
  have hWV : Nat.card W = Nat.card (W ⊓ centralizer ({t} : Set G) : Subgroup G) ^ 2 := by
    rw [hWc, hVc, ← pow_mul, mul_comm]
  have hW1 : 1 < Nat.card W := by
    rw [hWc]
    exact Nat.one_lt_two_pow (by omega)
  have hcard : Nat.card (W ⊓ centralizer (X : Set G) : Subgroup G) = 2 ^ (n - 1) := by
    rw [← hVc]
    exact card_inf_centralizer_eq_of_ne_bot_of_irreducible hW hW2 ht htW hDt hLW hirr hXW hXY hD
      hfix hWV hW1 hne
  have hDp : ⁅modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin n))),
      modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin n)))⁆ =
        modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin n))) := by
    have hcard3 : 3 ≤ (({c}ᶜ : Finset (Fin n))).card := by
      rw [Finset.card_compl, Finset.card_singleton, Fintype.card_fin]
      omega
    rw [modelToG, ← Subgroup.map_commutator, ← Subgroup.map_commutator,
      commutator_blockSL_eq_of_three_le hcard3]
  have hdec : ∀ w ∈ W,
      ∃ w₁ ∈ W ⊓ centralizer (X.map (MulAut.conj t).toMonoidHom : Set G),
        ∃ w₂ ∈ W ⊓ centralizer (X : Set G), w = w₁ * w₂ :=
    forall_eq_mul_of_card_inf_centralizer hW htW
      (by rw [hcard, hWc, ← pow_mul, Nat.mul_comm]) hD hfix
  obtain ⟨h1, h2, h3⟩ :=
    swapFactor_of_decomposition hW hXp hXW htW hWX hXY hXYW hdec hDp hD hfix
  exact ⟨h1, h2, h3, hfix⟩

theorem commutator_top_eq_top_of_perfect {G : Type*} [Group G] {X : Subgroup G}
    (hXp : ⁅X, X⁆ = X) : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = ⊤ := by
  apply Subgroup.map_injective X.subtype_injective
  rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hXp]

theorem swapModuleData_lift (hset : SeitzSetting G L) (hn : 4 ≤ n) (hK : Nat.card K = 2)
    (e : L ≃* LinearFlag.projectiveSL n K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {c : Fin n}
    {W X : Subgroup G} (hdata : LinearTwoSwapModuleData e t c W X) :
    (∀ x ∈ X, x * (t * x * t⁻¹) ∈ modelToG e (pointRadical (K := K) c) ⊔
        modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin n)))) ∧
      (∀ v ∈ modelToG e (pointRadical (K := K) c), ∃ x ∈ X ⊓ W, x * (t * x * t⁻¹) = v) ∧
      ∀ y ∈ modelToG e (pointRadical (K := K) c) ⊔
        modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin n))), ∃ x ∈ X, x * (t * x * t⁻¹) = y := by
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have htC : t ∈ centralizer (L : Set G) := mem_centralizer_of_inf_eq_zpowers hKt
  obtain ⟨hA, hAA, hΛ, hfix⟩ := swapModuleData_split (K := K) hn hK e htt htC hdata
  obtain ⟨hW2, hWc, hWt, htW, hLW, hXp, hXW, hWX, -, -, -, -⟩ := hdata
  set V := modelToG e (pointRadical (K := K) c) with hV
  set Λ := modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin n))) with hΛdef
  set δ := linearSwapDiag hA with hδ
  have hδapp : ∀ x : X, δ x = x * (t * x * t⁻¹) := fun x => rfl
  have hconjW : ∀ g ∈ normalizer (W : Set G), ∀ w ∈ W, g * w * g⁻¹ ∈ W := fun g hg w hw =>
    (mem_normalizer_iff.1 hg w).1 hw
  have hLt : ∀ y ∈ L, y * t = t * y := fun y hy => mem_centralizer_iff.1 htC y hy
  have hΛδ : ∀ l ∈ Λ, ∃ a ∈ X, a * (t * a * t⁻¹) = l := fun l hl =>
    exists_mem_mul_conj_eq_of_mem_sup htt hA hAA (hΛ hl) (hLt l (modelToG_le e _ hl)).symm
  have hδN : ∀ x : X, δ x ∈ normalizer (V : Set G) ⊓ centralizer ({t} : Set G) := by
    intro x
    have hxW : (x : G) ∈ normalizer (W : Set G) := hXW x.2
    have hxtW : t * x * t⁻¹ ∈ normalizer (W : Set G) :=
      mul_mem (mul_mem htW hxW) (inv_mem htW)
    have hδW : δ x ∈ normalizer (W : Set G) := by rw [hδapp]; exact mul_mem hxW hxtW
    have hδt : δ x ∈ centralizer ({t} : Set G) := by
      rw [mem_centralizer_singleton_iff, hδapp]
      have hc := conj_mul_comm_of_mem hA x.2 x.2
      have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
      calc (x : G) * (t * x * t⁻¹) * t = x * t * x := by group
        _ = x * t⁻¹ * x := by rw [htinv]
        _ = (t * t) * x * t⁻¹ * x := by rw [htt, one_mul]
        _ = t * ((t * x * t⁻¹) * x) := by group
        _ = t * (x * (t * x * t⁻¹)) := by rw [hc]
    refine mem_inf.2 ⟨?_, hδt⟩
    apply le_normalizer_of_mul_mul_inv_mem (A := zpowers (δ x)) (N := V) _ (mem_zpowers _)
    intro g hg v hv
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hg
    have hgW : δ x ^ k ∈ normalizer (W : Set G) := zpow_mem hδW k
    have hgt : δ x ^ k ∈ centralizer ({t} : Set G) := zpow_mem hδt k
    rw [← hWt] at hv ⊢
    obtain ⟨hvW, hvt⟩ := mem_inf.1 hv
    refine mem_inf.2 ⟨hconjW _ hgW v hvW, ?_⟩
    exact mul_mem (mul_mem hgt hvt) (inv_mem hgt)
  have hNV := normalizer_pointRadical_inf_le hset (by omega) hK e ht hKt c
  have hrange : δ.range ≤ V ⊔ Λ := by
    have hP : ⁅δ.range, δ.range⁆ = δ.range := by
      rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator,
        commutator_top_eq_top_of_perfect hXp]
    refine CFSG.SeitzReduction.perfect_le_of_le_sup (K := zpowers t) ?_ ?_ hP ?_
    · rw [zpowers_le]
      exact le_normalizer_of_mul_mul_inv_mem (A := zpowers t) (N := V ⊔ Λ)
        (fun a ha y hy => by
          obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 ha
          have hyL : y ∈ L := sup_le (modelToG_le e _) (modelToG_le e _) hy
          have hc : t ^ k * y = y * t ^ k := by
            have := (Commute.zpow_left (hLt y hyL).symm k)
            exact this.eq
          rw [hc, mul_inv_cancel_right]
          exact hy) (mem_zpowers t)
    · exact Group.isSolvable_of_comm fun a b => by
        obtain ⟨_, i, rfl⟩ := a
        obtain ⟨_, j, rfl⟩ := b
        exact Subtype.ext (zpow_mul_comm t i j)
    · rintro _ ⟨x, rfl⟩
      exact hNV (hδN x)
  have hb : ∀ v ∈ V, ∃ x ∈ X ⊓ W, x * (t * x * t⁻¹) = v := by
    set S := ((X ⊓ W).subgroupOf X).map δ with hS
    have hSV : S ≤ V := by
      rintro _ ⟨m, hm, rfl⟩
      have hmW : (m : G) ∈ W := (mem_inf.1 (mem_subgroupOf.1 hm)).2
      rw [← hWt]
      refine mem_inf.2 ⟨?_, (hδN m).2⟩
      rw [hδapp]
      exact mul_mem hmW (hconjW t htW m hmW)
    have hSN : Λ ≤ normalizer (S : Set G) := by
      apply le_normalizer_of_mul_mul_inv_mem
      rintro l hl _ ⟨m, hm, rfl⟩
      obtain ⟨a, haX, rfl⟩ := hΛδ l hl
      have hmX := mem_inf.1 (mem_subgroupOf.1 hm)
      refine ⟨⟨a, haX⟩ * m * ⟨a, haX⟩⁻¹, ?_, ?_⟩
      · rw [SetLike.mem_coe, mem_subgroupOf]
        refine mem_inf.2 ⟨mul_mem (mul_mem haX hmX.1) (inv_mem haX), ?_⟩
        exact hconjW a (hXW haX) m hmX.2
      · rw [map_mul, map_mul, map_inv]
        rfl
    rcases modelToG_pointRadical_irreducible hK e c hSV hSN with hS0 | hSV'
    · exfalso
      have hXW0 : ∀ m ∈ X, m ∈ W → m = 1 := by
        intro m hmX hmW
        have h1 : δ ⟨m, hmX⟩ ∈ S := ⟨⟨m, hmX⟩, mem_subgroupOf.2 (mem_inf.2 ⟨hmX, hmW⟩), rfl⟩
        rw [hS0, mem_bot] at h1
        have h2 := linearSwapDiag_injective hA hAA (a₁ := ⟨m, hmX⟩) (a₂ := 1)
          (by rw [map_one]; exact h1)
        exact congrArg Subtype.val h2
      have hXC : X ≤ centralizer (W : Set G) := by
        intro x hx
        rw [mem_centralizer_iff]
        intro w hw
        have hcomm : w * x * w⁻¹ * x⁻¹ = 1 := by
          apply hXW0
          · exact mul_mem ((mem_normalizer_iff.1 (hWX hw) x).1 hx) (inv_mem hx)
          · have h1 : x * w⁻¹ * x⁻¹ ∈ W := hconjW x (hXW hx) _ (inv_mem hw)
            have h2 := mul_mem hw h1
            rwa [show w * (x * w⁻¹ * x⁻¹) = w * x * w⁻¹ * x⁻¹ by group] at h2
        calc w * x = (w * x * w⁻¹ * x⁻¹) * x * w := by group
          _ = x * w := by rw [hcomm, one_mul]
      have hXtC : X.map (MulAut.conj t).toMonoidHom ≤ centralizer (W : Set G) := by
        rintro _ ⟨x, hx, rfl⟩
        rw [mem_centralizer_iff]
        intro w hw
        have hw' : t⁻¹ * w * t⁻¹⁻¹ ∈ W := hconjW _ (inv_mem htW) w hw
        rw [inv_inv] at hw'
        have h1 := mem_centralizer_iff.1 (hXC hx) _ hw'
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        calc w * (t * x * t⁻¹) = t * ((t⁻¹ * w * t) * x) * t⁻¹ := by group
          _ = t * (x * (t⁻¹ * w * t)) * t⁻¹ := by rw [h1]
          _ = t * x * t⁻¹ * w := by group
      have hWΛ : W ≤ centralizer (Λ : Set G) := by
        intro w hw
        rw [mem_centralizer_iff]
        intro l hl
        have := mem_centralizer_iff.1 ((sup_le hXC hXtC) (hΛ hl)) w hw
        exact this.symm
      have hbot : W = ⊥ := by
        rw [← hfix]
        exact (inf_eq_left.2 hWΛ).symm
      have h1 : Nat.card W = 1 := by rw [hbot]; exact Subgroup.card_bot
      rw [hWc] at h1
      have : 1 < 2 ^ (2 * (n - 1)) := Nat.one_lt_two_pow (by omega)
      omega
    · intro v hv
      have hv' : v ∈ S := by rw [hSV']; exact hv
      obtain ⟨m, hm, rfl⟩ := hv'
      exact ⟨m, mem_subgroupOf.1 hm, rfl⟩
  refine ⟨fun x hx => hrange ⟨⟨x, hx⟩, rfl⟩, hb, ?_⟩
  · intro y hy
    have hle : V ⊔ Λ ≤ δ.range := by
      refine sup_le ?_ ?_
      · intro v hv
        obtain ⟨m, hm, hmv⟩ := hb v hv
        exact ⟨⟨m, (mem_inf.1 hm).1⟩, hmv⟩
      · intro l hl
        obtain ⟨a, haX, rfl⟩ := hΛδ l hl
        exact ⟨⟨a, haX⟩, rfl⟩
    obtain ⟨⟨x, hx⟩, hxy⟩ := hle hy
    exact ⟨x, hx, hxy⟩

end Point

end CFSG.SeitzReduction.LinearPilot
