module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Child8Tools
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.IlinykhFusion
public import CFSG.LocalAnalysis.EvenSmallLie.FoursGroup
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.IlinykhCaseOne

public section

namespace CFSG.EvenSmallLie.OmegaEight.Child8

open Subgroup CFSG.Quasithin

structure CaseOneData (X : Type) [Group X] [Finite X] where
  z : X
  T : Subgroup X
  ιE : Multiplicative evenSub →* X
  ιF : Multiplicative evenSub →* X
  card_X : Nat.card X = 2 ^ 13 * 42525
  card_T : Nat.card T = 2 ^ 13
  center_T : ∀ t ∈ T, (∀ u ∈ T, t * u = u * t) → t = 1 ∨ t = z
  ιE_injective : Function.Injective ιE
  ιF_injective : Function.Injective ιF
  ιE_evenZ : ιE (Multiplicative.ofAdd evenZ) = z
  ιF_evenZ : ιF (Multiplicative.ofAdd evenZ) = z
  ιE_mem : ∀ v, ιE v ∈ T
  ιF_mem : ∀ v, ιF v ∈ T
  E_up : ∀ w : X, (∀ v, w * ιE v * w⁻¹ ∈ ιE.range) → ∃ σ ∈ alternatingGroup (Fin 8),
    ∀ v, w * ιE v * w⁻¹ = ιE (Multiplicative.ofAdd (evenPerm σ (Multiplicative.toAdd v)))
  E_down : ∀ σ ∈ alternatingGroup (Fin 8), ∃ w : X,
    ∀ v, w * ιE v * w⁻¹ = ιE (Multiplicative.ofAdd (evenPerm σ (Multiplicative.toAdd v)))
  F_gens : ∀ σ ∈ frameGens, ∃ w : X,
    ∀ v, w * ιF v * w⁻¹ = ιF (Multiplicative.ofAdd (evenPerm σ (Multiplicative.toAdd v)))
  F_types : ∀ v : evenSub, (frameCls v = 2 ∨ frameCls v = 4 ∨ frameCls v = 7) →
    ∃ w : X, w * ιF (Multiplicative.ofAdd v) * w⁻¹ ∈ ιE.range
  not_conj : ∀ w : X, ¬ ∀ v, w * ιE v * w⁻¹ ∈ ιF.range
  elem : ∀ B : Subgroup X, B ≤ T → (∀ b ∈ B, b * b = 1) → Nat.card B = 2 ^ 7 →
    B = ιE.range ∨ B = ιF.range
  inv : ∀ y : X, y * y = 1 → ∃ w : X, w * y * w⁻¹ ∈ ιF.range

theorem evenSub_add_self (v : evenSub) : v + v = 0 :=
  Subtype.ext (funext fun i => by
    change v.1 i + v.1 i = 0
    generalize v.1 i = x
    revert x
    decide)

theorem evenZ_ne_zero : evenZ ≠ 0 := fun h => by
  have h1 := congrArg (fun v : evenSub => (v : FrameVec) 0) h
  exact absurd h1 (by decide)

theorem mul_self_of_evenSub {X : Type*} [Group X] (ι : Multiplicative evenSub →* X)
    (v : Multiplicative evenSub) : ι v * ι v = 1 := by
  rw [← map_mul, show v * v = 1 from evenSub_add_self (Multiplicative.toAdd v), map_one]

theorem map_ne_one_of_ne {X : Type*} [Group X] {ι : Multiplicative evenSub →* X}
    (hι : Function.Injective ι) {v : evenSub} (hv : v ≠ 0) : ι (Multiplicative.ofAdd v) ≠ 1 :=
  fun h => hv (hι (h.trans (map_one ι).symm))

theorem eq_zero_or_frameZ_of_fixed : ∀ n < 256,
    permVec frameSinger (frameDecode n) = frameDecode n →
      permVec frameFlip (frameDecode n) = frameDecode n → n = 0 ∨ n = 255 := by
  decide +kernel

theorem eq_zero_or_eq_frameZ {v : FrameVec} (h1 : permVec frameSinger v = v)
    (h2 : permVec frameFlip v = v) : v = 0 ∨ v = frameZ := by
  obtain ⟨n, hn, rfl⟩ := frameDecode_surjective v
  rcases eq_zero_or_frameZ_of_fixed n hn h1 h2 with rfl | rfl
  · left
    decide
  · right
    exact frameDecode_255

theorem frameCls_two_add {i j : Fin 8} (hij : i ≠ j) : frameCls (frameE i + frameE j) = 2 := by
  revert i j
  decide +kernel

theorem frameCls_six_add {i j : Fin 8} (hij : i ≠ j) :
    frameCls (frameZ + frameE i + frameE j) = 7 := by
  revert i j
  decide +kernel

theorem frameCls_blockVec {B : Finset (Fin 8)} (hB : B ∈ frameBlocks) : frameCls (blockVec B) = 4 :=
  (frameCls_eq_four_iff _).2 ⟨B, hB, rfl⟩

section Generic

variable {G : Type*} [Group G]

theorem comm_of_mem_normalizer {P : Subgroup G} {z : G} (hz : z ∈ P)
    (hzc : ∀ t ∈ P, t * z = z * t) (hcent : ∀ t ∈ P, (∀ u ∈ P, t * u = u * t) → t = 1 ∨ t = z)
    (hz1 : z ≠ 1) {n : G} (hn : n ∈ normalizer (P : Set G)) : n * z = z * n := by
  have hmem : n * z * n⁻¹ ∈ P := (mem_normalizer_iff.1 hn z).1 hz
  have hc : ∀ u ∈ P, n * z * n⁻¹ * u = u * (n * z * n⁻¹) := by
    intro u hu
    have hu' : n⁻¹ * u * n ∈ P := (mem_normalizer_iff.1 hn _).2 (by simpa [mul_assoc] using hu)
    have h1 := hzc _ hu'
    calc n * z * n⁻¹ * u = n * (z * (n⁻¹ * u * n)) * n⁻¹ := by group
      _ = n * ((n⁻¹ * u * n) * z) * n⁻¹ := by rw [h1]
      _ = u * (n * z * n⁻¹) := by group
  rcases hcent _ hmem hc with h | h
  · refine absurd ?_ hz1
    calc z = n⁻¹ * (n * z * n⁻¹) * n := by group
      _ = 1 := by rw [h]; group
  · calc n * z = n * z * n⁻¹ * n := by group
      _ = z * n := by rw [h]

theorem mul_self_of_isConj {z y : G} (hz : z * z = 1) (h : IsConj z y) : y * y = 1 := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  rw [← hc]
  calc c * z * c⁻¹ * (c * z * c⁻¹) = c * (z * z) * c⁻¹ := by group
    _ = 1 := by rw [hz, mul_one, mul_inv_cancel]

theorem comm_of_mul_self {a b : G} (ha : a * a = 1) (hb : b * b = 1) (hab : a * b * (a * b) = 1) :
    a * b = b * a := by
  have h1 : a * b = (a * b)⁻¹ := eq_inv_of_mul_eq_one_left hab
  rw [h1, mul_inv_rev, inv_eq_of_mul_eq_one_right ha, inv_eq_of_mul_eq_one_right hb]

end Generic

theorem card_evenSub : Nat.card evenSub = 2 ^ 7 := by
  rw [Nat.card_congr evenSubEquiv.toEquiv, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
    Fintype.card_fin]

theorem card_range_evenSub {G : Type*} [Group G] {ι : Multiplicative evenSub →* G}
    (hι : Function.Injective ι) : Nat.card ι.range = 2 ^ 7 := by
  rw [card_range_of_injective hι]
  exact card_evenSub

theorem mul_self_of_mem_range {G : Type*} [Group G] {ι : Multiplicative evenSub →* G} {a : G}
    (ha : a ∈ ι.range) : a * a = 1 := by
  obtain ⟨v, rfl⟩ := ha
  exact mul_self_of_evenSub ι v

theorem comm_of_mem_range {G : Type*} [Group G] {ι : Multiplicative evenSub →* G} {a b : G}
    (ha : a ∈ ι.range) (hb : b ∈ ι.range) : a * b = b * a :=
  comm_of_mul_self (mul_self_of_mem_range ha) (mul_self_of_mem_range hb)
    (mul_self_of_mem_range (mul_mem ha hb))

section Coords

variable {G : Type} [Group G] {X : Type} [Group X] {ψ : X →* G} (hψ : Function.Injective ψ)
  {A : Type} [AddZeroClass A] {ι : Multiplicative A →* X} (hι : Function.Injective ι)

include hψ hι in
theorem coordConj_of_conj [Finite G] {w : X} {f : A → A}
    (hw : ∀ v, w * ι v * w⁻¹ = ι (Multiplicative.ofAdd (f (Multiplicative.toAdd v)))) :
    ∃ hn : ψ w ∈ normalizer (Set.range (ψ.comp ι)),
      ∀ v, coordConj (ψ.comp ι) ⟨ψ w, hn⟩ v = f v := by
  have hn : ψ w ∈ normalizer (Set.range (ψ.comp ι)) := by
    apply mem_normalizer_of_conj_mem
    rintro _ ⟨v, rfl⟩
    refine ⟨Multiplicative.ofAdd (f (Multiplicative.toAdd v)), ?_⟩
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, ← hw v, map_mul, map_mul, map_inv]
  refine ⟨hn, fun v => hψ.comp hι ?_⟩
  change (ψ.comp ι) (Multiplicative.ofAdd (coordConj (ψ.comp ι) ⟨ψ w, hn⟩ v)) =
    (ψ.comp ι) (Multiplicative.ofAdd (f v))
  rw [coordConj_spec, MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_inv, ← map_mul,
    ← map_mul]
  exact congrArg ψ (hw (Multiplicative.ofAdd v))

include hψ in
theorem coordConj_of_eq {n : normalizer (Set.range (ψ.comp ι))} {w : X} (hw : ψ w = n)
    (v : A) : ι (Multiplicative.ofAdd (coordConj (ψ.comp ι) n v)) =
      w * ι (Multiplicative.ofAdd v) * w⁻¹ := by
  apply hψ
  have h := coordConj_spec (ψ.comp ι) n v
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply] at h
  rw [h, map_mul, map_mul, map_inv, hw]

include hψ hι in
theorem coordConj_eq_iff (n : normalizer (Set.range (ψ.comp ι))) (v : A) :
    coordConj (ψ.comp ι) n v = v ↔
      (n : G) * ψ (ι (Multiplicative.ofAdd v)) * (n : G)⁻¹ = ψ (ι (Multiplicative.ofAdd v)) := by
  have h := coordConj_spec (ψ.comp ι) n v
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply] at h
  rw [← h]
  exact ⟨fun h' => by rw [h'], fun h' => hι (hψ h')⟩

end Coords

theorem exists_sylow_map {G X : Type} [Group G] [Finite G] [Group X] {ψ : X →* G}
    (hψ : Function.Injective ψ) {z : X} (hH : ∀ g : G, g ∈ ψ.range ↔ g * ψ z = ψ z * g)
    {T : Subgroup X} {a m : ℕ} (hT : Nat.card T = 2 ^ a) (hX : Nat.card X = 2 ^ a * m)
    (hm : ¬ 2 ∣ m) (hzT : z ∈ T) (hz1 : z ≠ 1)
    (hcent : ∀ t ∈ T, (∀ u ∈ T, t * u = u * t) → t = 1 ∨ t = z) :
    ∃ P : Sylow 2 G, (P : Subgroup G) = T.map ψ := by
  have hcard : Nat.card (T.map ψ) = 2 ^ a := by rw [card_map_of_injective hψ, hT]
  refine exists_sylow_eq_of_normalizer_le (H := ψ.range) (IsPGroup.of_card hcard)
    (fun Q hQ hPQ hQH => eq_of_card_of_le hcard
      (by rw [card_range_of_injective hψ, hX]) hm hQ hPQ hQH) ?_
  intro n hn
  rw [hH]
  refine comm_of_mem_normalizer (mem_map_of_mem ψ hzT)
    (fun t ht => by obtain ⟨t', -, rfl⟩ := ht; exact (hH _).1 ⟨t', rfl⟩)
    (fun t ht hc => ?_) (fun h => hz1 (hψ (h.trans (map_one ψ).symm))) hn
  obtain ⟨t', ht', rfl⟩ := ht
  rcases hcent t' ht' (fun u hu => hψ (by simpa using hc _ (mem_map_of_mem ψ hu))) with h | h
  · left
    rw [h, map_one]
  · right
    rw [h]

theorem exists_conj_le_sylow {W : Type*} [Group W] [Finite W] {p : ℕ} [Fact p.Prime]
    (P : Sylow p W) {Q : Subgroup W} (hQ : IsPGroup p Q) :
    ∃ w : W, ∀ q ∈ Q, w * q * w⁻¹ ∈ P := by
  obtain ⟨S', hS'⟩ := hQ.exists_le_sylow
  obtain ⟨w, hw⟩ := MulAction.exists_smul_eq W S' P
  refine ⟨w, fun q hq => ?_⟩
  rw [← hw]
  change w * q * w⁻¹ ∈ ((w • S' : Sylow p W) : Subgroup W)
  rw [Sylow.coe_subgroup_smul, mem_smul_pointwise_iff_exists]
  exact ⟨q, hS' hq, by rw [MulAut.smul_def, MulAut.conj_apply]⟩

namespace CaseOneData

variable {X : Type} [Group X] [Finite X] (D : CaseOneData X)

theorem z_mul_self : D.z * D.z = 1 := by
  rw [← D.ιE_evenZ]
  exact mul_self_of_evenSub _ _

theorem z_ne_one : D.z ≠ 1 := by
  rw [← D.ιE_evenZ]
  exact map_ne_one_of_ne D.ιE_injective evenZ_ne_zero

theorem z_mem_T : D.z ∈ D.T := D.ιE_evenZ ▸ D.ιE_mem _

variable {G : Type} [Group G] {ψ : X →* G}

theorem comm_z (hH : ∀ g : G, g ∈ ψ.range ↔ g * ψ D.z = ψ D.z * g) (x : X) :
    ψ x * ψ D.z = ψ D.z * ψ x :=
  (hH _).1 ⟨x, rfl⟩

theorem zG_ne_one (hψ : Function.Injective ψ) : ψ D.z ≠ 1 := fun h =>
  D.z_ne_one (hψ (h.trans (map_one ψ).symm))

theorem zG_mul_self : ψ D.z * ψ D.z = 1 := by rw [← map_mul, D.z_mul_self, map_one]

theorem orderOf_zG (hψ : Function.Injective ψ) : orderOf (ψ D.z) = 2 :=
  orderOf_eq_prime (by rw [pow_two, D.zG_mul_self]) (D.zG_ne_one hψ)

theorem center_TG (hψ : Function.Injective ψ) {t : G} (ht : t ∈ D.T.map ψ)
    (hc : ∀ u ∈ D.T.map ψ, t * u = u * t) : t = 1 ∨ t = ψ D.z := by
  obtain ⟨t', ht', rfl⟩ := ht
  rcases D.center_T t' ht' (fun u hu => hψ (by simpa using hc _ (mem_map_of_mem ψ hu))) with h | h
  · left
    rw [h, map_one]
  · right
    rw [h]

theorem exists_sylow [Finite G] (hψ : Function.Injective ψ)
    (hH : ∀ g : G, g ∈ ψ.range ↔ g * ψ D.z = ψ D.z * g) :
    ∃ P : Sylow 2 G, (P : Subgroup G) = D.T.map ψ :=
  exists_sylow_map hψ hH D.card_T D.card_X (by decide) D.z_mem_T D.z_ne_one D.center_T

theorem ψιE_evenZ : (ψ.comp D.ιE) (Multiplicative.ofAdd evenZ) = ψ D.z := by
  rw [MonoidHom.comp_apply, D.ιE_evenZ]

theorem ψιF_evenZ : (ψ.comp D.ιF) (Multiplicative.ofAdd evenZ) = ψ D.z := by
  rw [MonoidHom.comp_apply, D.ιF_evenZ]

theorem normalizer_E_fixes [Finite G] (hψ : Function.Injective ψ)
    (hH : ∀ g : G, g ∈ ψ.range ↔ g * ψ D.z = ψ D.z * g) :
    ∀ n ∈ normalizer (Set.range (ψ.comp D.ιE)), n * ψ D.z * n⁻¹ = ψ D.z := by
  have hι : Function.Injective (ψ.comp D.ιE) := hψ.comp D.ιE_injective
  let _ : MulAction (normalizer (Set.range (ψ.comp D.ιE))) evenSub :=
    coordAction (ψ.comp D.ιE) hι
  have key := normalizer_fixes_evenZ_of_alternating
    (N := normalizer (Set.range (ψ.comp D.ιE))) (coordConj_add hι) (fun n hn => ?_)
    (fun σ hσ => ?_)
  · intro n hn
    have h := (coordConj_eq_iff hψ D.ιE_injective ⟨n, hn⟩ evenZ).1 (key ⟨n, hn⟩)
    rwa [D.ιE_evenZ] at h
  · have hz := (coordConj_eq_iff hψ D.ιE_injective n evenZ).1 hn
    rw [D.ιE_evenZ] at hz
    obtain ⟨w, hw⟩ := (hH n).2 (by
      calc (n : G) * ψ D.z = (n : G) * ψ D.z * (n : G)⁻¹ * n := by group
        _ = ψ D.z * n := by rw [hz])
    have hconj : ∀ v, w * D.ιE v * w⁻¹ =
        D.ιE (Multiplicative.ofAdd (coordConj (ψ.comp D.ιE) n (Multiplicative.toAdd v))) :=
      fun v => (coordConj_of_eq hψ hw (Multiplicative.toAdd v)).symm
    obtain ⟨σ, hσ, hσw⟩ := D.E_up w (fun v => by rw [hconj]; exact ⟨_, rfl⟩)
    refine ⟨σ, hσ, fun v => ?_⟩
    have h1 := D.ιE_injective ((hconj (Multiplicative.ofAdd v)).symm.trans
      (hσw (Multiplicative.ofAdd v)))
    exact congrArg Subtype.val h1
  · obtain ⟨w, hw⟩ := D.E_down σ hσ
    obtain ⟨hn, hnv⟩ := coordConj_of_conj hψ D.ιE_injective hw
    exact ⟨⟨ψ w, hn⟩, fun v => congrArg Subtype.val (hnv v)⟩

theorem z_comm (hψ : Function.Injective ψ) (hH : ∀ g : G, g ∈ ψ.range ↔ g * ψ D.z = ψ D.z * g)
    (x : X) : x * D.z = D.z * x :=
  hψ (by rw [map_mul, map_mul, D.comm_z hH x])

theorem elem_TG (hψ : Function.Injective ψ) {B : Subgroup G} (hB : B ≤ D.T.map ψ)
    (hB2 : ∀ b ∈ B, b ^ 2 = 1) (hBc : Nat.card B = 2 ^ 7) :
    B = (ψ.comp D.ιE).range ∨ B = (ψ.comp D.ιF).range := by
  have hBr : B ≤ ψ.range := hB.trans (map_le_range ψ D.T)
  have hB' : B.comap ψ ≤ D.T := comap_le_of_le_map hψ hB
  have hB'2 : ∀ b ∈ B.comap ψ, b * b = 1 := fun b hb => hψ (by
    rw [map_mul, map_one, ← pow_two]
    exact hB2 _ hb)
  have hB'c : Nat.card (B.comap ψ) = 2 ^ 7 := by rw [card_comap_of_le_range hψ hBr, hBc]
  rw [← map_comap_eq_self hBr]
  rcases D.elem _ hB' hB'2 hB'c with h | h
  · left
    rw [h, MonoidHom.range_comp]
  · right
    rw [h, MonoidHom.range_comp]

theorem conj_E_ne_F [Finite G] (hψ : Function.Injective ψ)
    (hH : ∀ g : G, g ∈ ψ.range ↔ g * ψ D.z = ψ D.z * g) (g : G) :
    conjSubgroup (ψ.comp D.ιE).range g ≠ (ψ.comp D.ιF).range := by
  intro h
  have hzE : ψ D.z ∈ (ψ.comp D.ιE).range := ⟨_, D.ψιE_evenZ⟩
  have hmemF : ∀ x ∈ (ψ.comp D.ιE).range, g⁻¹ * x * g ∈ (ψ.comp D.ιF).range := fun x hx => by
    rw [← h, mem_conjSubgroup_iff]
    simpa [mul_assoc] using hx
  have hmemE : ∀ y ∈ (ψ.comp D.ιF).range, g * y * g⁻¹ ∈ (ψ.comp D.ιE).range := fun y hy => by
    rw [← h, mem_conjSubgroup_iff] at hy
    exact hy
  have hfix : ∀ n ∈ normalizer (Set.range (ψ.comp D.ιF)),
      n * (g⁻¹ * ψ D.z * g) * n⁻¹ = g⁻¹ * ψ D.z * g := by
    intro n hn
    have hn' : g * n * g⁻¹ ∈ normalizer (Set.range (ψ.comp D.ιE)) := by
      apply mem_normalizer_of_conj_mem
      intro x hx
      have h1 := hmemF x hx
      have h2 : n * (g⁻¹ * x * g) * n⁻¹ ∈ (ψ.comp D.ιF).range :=
        (mem_set_normalizer_iff.1 hn _).1 h1
      have h3 := hmemE _ h2
      have e : g * n * g⁻¹ * x * (g * n * g⁻¹)⁻¹ = g * (n * (g⁻¹ * x * g) * n⁻¹) * g⁻¹ := by
        group
      rw [e]
      exact h3
    have h1 := D.normalizer_E_fixes hψ hH _ hn'
    calc n * (g⁻¹ * ψ D.z * g) * n⁻¹ = g⁻¹ * (g * n * g⁻¹ * ψ D.z * (g * n * g⁻¹)⁻¹) * g := by
          group
      _ = g⁻¹ * ψ D.z * g := by rw [h1]
  obtain ⟨v', hv'⟩ := hmemF _ hzE
  have hperm : ∀ σ ∈ frameGens, permVec σ ((Multiplicative.toAdd v' : evenSub) : FrameVec) =
      (Multiplicative.toAdd v' : evenSub) := by
    intro σ hσ
    obtain ⟨w, hw⟩ := D.F_gens σ hσ
    obtain ⟨hn, hnv⟩ := coordConj_of_conj hψ D.ιF_injective hw
    have h1 := hfix _ hn
    rw [← hv'] at h1
    have h2 := (coordConj_eq_iff hψ D.ιF_injective ⟨ψ w, hn⟩ (Multiplicative.toAdd v')).2 h1
    rw [hnv] at h2
    exact congrArg Subtype.val h2
  rcases eq_zero_or_eq_frameZ (hperm _ (Set.mem_insert _ _))
    (hperm _ (Set.mem_insert_of_mem _ rfl)) with h0 | h0
  · have hv0 : v' = 1 := Subtype.ext h0
    rw [hv0, map_one] at hv'
    refine D.zG_ne_one hψ ?_
    calc ψ D.z = g * (g⁻¹ * ψ D.z * g) * g⁻¹ := by group
      _ = 1 := by rw [← hv']; group
  · have hv0 : v' = Multiplicative.ofAdd evenZ := Subtype.ext h0
    rw [hv0, D.ψιF_evenZ] at hv'
    obtain ⟨u, rfl⟩ := (hH g).2 (by
      calc g * ψ D.z = g * (g⁻¹ * ψ D.z * g) := by rw [← hv']
        _ = ψ D.z * g := by group)
    apply D.not_conj u⁻¹
    intro v
    obtain ⟨v'', hv''⟩ := hmemF _ ⟨v, rfl⟩
    refine ⟨v'', hψ ?_⟩
    rw [MonoidHom.comp_apply] at hv''
    rw [hv'', MonoidHom.comp_apply, map_mul, map_mul, map_inv, inv_inv]

theorem pow_two_of_mem_range {ι : Multiplicative evenSub →* G} {a : G} (ha : a ∈ ι.range) :
    a ^ 2 = 1 := by
  rw [pow_two]
  exact mul_self_of_mem_range ha

theorem wc_E [Finite G] (hψ : Function.Injective ψ)
    (hH : ∀ g : G, g ∈ ψ.range ↔ g * ψ D.z = ψ D.z * g) :
    IsWeaklyClosedIn (ψ.comp D.ιE).range (D.T.map ψ) :=
  isWeaklyClosedIn_of_elementary_eq_or_eq (fun _ ha => pow_two_of_mem_range ha)
    (fun _ hB hB2 hBc => D.elem_TG hψ hB hB2
      (hBc.trans (card_range_evenSub (hψ.comp D.ιE_injective))))
    (D.conj_E_ne_F hψ hH)

theorem wc_F [Finite G] (hψ : Function.Injective ψ)
    (hH : ∀ g : G, g ∈ ψ.range ↔ g * ψ D.z = ψ D.z * g) :
    IsWeaklyClosedIn (ψ.comp D.ιF).range (D.T.map ψ) := by
  refine isWeaklyClosedIn_of_elementary_eq_or_eq (A' := (ψ.comp D.ιE).range)
    (fun _ ha => pow_two_of_mem_range ha)
    (fun _ hB hB2 hBc => (D.elem_TG hψ hB hB2
      (hBc.trans (card_range_evenSub (hψ.comp D.ιF_injective)))).symm) (fun g hg => ?_)
  apply D.conj_E_ne_F hψ hH g⁻¹
  rw [← hg, conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]

theorem E_le_TG : (ψ.comp D.ιE).range ≤ D.T.map ψ := by
  rintro _ ⟨v, rfl⟩
  exact mem_map_of_mem ψ (D.ιE_mem v)

theorem F_le_TG : (ψ.comp D.ιF).range ≤ D.T.map ψ := by
  rintro _ ⟨v, rfl⟩
  exact mem_map_of_mem ψ (D.ιF_mem v)

theorem eq_of_isConj_E [Finite G] (hψ : Function.Injective ψ)
    (hH : ∀ g : G, g ∈ ψ.range ↔ g * ψ D.z = ψ D.z * g) {e : G}
    (he : e ∈ (ψ.comp D.ιE).range) (hze : IsConj (ψ D.z) e) : e = ψ D.z := by
  obtain ⟨P, hP⟩ := D.exists_sylow hψ hH
  refine eq_of_isConj_of_isWeaklyClosedIn P (hP ▸ D.E_le_TG) (fun _ ha _ hb =>
    comm_of_mem_range ha hb) (hP ▸ D.wc_E hψ hH) ⟨_, D.ψιE_evenZ⟩
    (D.normalizer_E_fixes hψ hH) he hze

theorem not_type (hψ : Function.Injective ψ) [Finite G]
    (hH : ∀ g : G, g ∈ ψ.range ↔ g * ψ D.z = ψ D.z * g)
    (n : normalizer (Set.range (ψ.comp D.ιF))) {v : evenSub}
    (hv : coordConj (ψ.comp D.ιF) n evenZ = v)
    (hcls : frameCls (v : FrameVec) = 2 ∨ frameCls (v : FrameVec) = 4 ∨
      frameCls (v : FrameVec) = 7) : False := by
  obtain ⟨w, e, he⟩ := D.F_types v hcls
  have hspec := coordConj_spec (ψ.comp D.ιF) n evenZ
  rw [hv, D.ψιF_evenZ, MonoidHom.comp_apply] at hspec
  have hconj : IsConj (ψ D.z) (ψ (D.ιE e)) := by
    refine isConj_iff.2 ⟨ψ w * n, ?_⟩
    rw [he, map_mul, map_mul, map_inv, hspec]
    group
  have h1 := D.eq_of_isConj_E hψ hH ⟨e, rfl⟩ hconj
  have h2 : D.ιE e = D.z := hψ h1
  rw [h2] at he
  have h3 : D.ιF (Multiplicative.ofAdd v) = D.z := by
    calc D.ιF (Multiplicative.ofAdd v) = w⁻¹ * (w * D.ιF (Multiplicative.ofAdd v) * w⁻¹) * w := by
          group
      _ = D.z := by
        rw [← he]
        calc w⁻¹ * D.z * w = w⁻¹ * (D.z * w) := by group
          _ = D.z := by rw [← D.z_comm hψ hH w]; group
  rw [← D.ιF_evenZ] at h3
  have h4 : v = evenZ := D.ιF_injective h3
  have h5 : frameCls (v : FrameVec) = 9 := by rw [h4]; exact (frameCls_eq_nine_iff _).2 rfl
  omega

theorem normalizer_F_fixes [Finite G] (hψ : Function.Injective ψ)
    (hH : ∀ g : G, g ∈ ψ.range ↔ g * ψ D.z = ψ D.z * g) :
    ∀ n ∈ normalizer (Set.range (ψ.comp D.ιF)), n * ψ D.z * n⁻¹ = ψ D.z := by
  have hι : Function.Injective (ψ.comp D.ιF) := hψ.comp D.ιF_injective
  let _ : MulAction (normalizer (Set.range (ψ.comp D.ιF))) evenSub :=
    coordAction (ψ.comp D.ιF) hι
  have key := normalizer_fixes_evenZ_of_frame (N := normalizer (Set.range (ψ.comp D.ιF)))
    (coordConj_add hι) (fun σ hσ => ?_)
    (fun n i j hij h => D.not_type hψ hH n rfl (Or.inl (by
      rw [show ((coordConj (ψ.comp D.ιF) n evenZ : evenSub) : FrameVec) = frameE i + frameE j
        from h]
      exact frameCls_two_add hij)))
    (fun n i j hij h => D.not_type hψ hH n rfl (Or.inr (Or.inr (by
      rw [show ((coordConj (ψ.comp D.ιF) n evenZ : evenSub) : FrameVec) =
        frameZ + frameE i + frameE j from h]
      exact frameCls_six_add hij))))
    (fun n B hB h => D.not_type hψ hH n rfl (Or.inr (Or.inl (by
      rw [show ((coordConj (ψ.comp D.ιF) n evenZ : evenSub) : FrameVec) = blockVec B from h]
      exact frameCls_blockVec hB))))
  · intro n hn
    have h := (coordConj_eq_iff hψ D.ιF_injective ⟨n, hn⟩ evenZ).1 (key ⟨n, hn⟩)
    rwa [D.ιF_evenZ] at h
  · obtain ⟨w, hw⟩ := D.F_gens σ hσ
    obtain ⟨hn, hnv⟩ := coordConj_of_conj hψ D.ιF_injective hw
    exact ⟨⟨ψ w, hn⟩, fun v => congrArg Subtype.val (hnv v)⟩

theorem false_of [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hψ : Function.Injective ψ) (hH : ∀ g : G, g ∈ ψ.range ↔ g * ψ D.z = ψ D.z * g) : False := by
  obtain ⟨P, hP⟩ := D.exists_sylow hψ hH
  refine false_of_isolated_involution hnonab (D.orderOf_zG hψ) fun y hy hzy => ?_
  obtain ⟨y', rfl⟩ := (hH y).2 (mem_centralizer_singleton_iff.1 hy)
  have hy2 : y' * y' = 1 := hψ (by
    rw [map_mul, map_one]
    exact mul_self_of_isConj D.zG_mul_self hzy)
  obtain ⟨w, v, hv⟩ := D.inv y' hy2
  have hx : ψ (D.ιF v) ∈ (ψ.comp D.ιF).range := ⟨v, rfl⟩
  have hzx : IsConj (ψ D.z) (ψ (D.ιF v)) :=
    hzy.trans (isConj_iff.2 ⟨ψ w, by rw [hv, map_mul, map_mul, map_inv]⟩)
  obtain ⟨n, hn, hnx⟩ := exists_normalizer_conj_of_isWeaklyClosedIn P (hP ▸ D.F_le_TG)
    (fun _ ha _ hb => comm_of_mem_range ha hb) (hP ▸ D.wc_F hψ hH) ⟨_, D.ψιF_evenZ⟩ hx hzx
  rw [D.normalizer_F_fixes hψ hH n hn, hv, map_mul, map_mul, map_inv] at hnx
  calc ψ y' = (ψ w)⁻¹ * (ψ w * ψ y' * (ψ w)⁻¹) * ψ w := by group
    _ = (ψ w)⁻¹ * ψ D.z * ψ w := by rw [← hnx]
    _ = (ψ w)⁻¹ * (ψ D.z * ψ w) := by group
    _ = ψ D.z := by rw [← D.comm_z hH w]; group

end CaseOneData

end CFSG.EvenSmallLie.OmegaEight.Child8
