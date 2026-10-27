module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4NXAct
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Basic

public section

open scoped Pointwise

namespace CFSG.CGT.Hall82

open Subgroup
open CFSG.ComponentClassification.AS81
open CFSG.ComponentClassification.AS81.Hexa

variable {G : Type} [Group G] [Finite G]
variable {V L : Subgroup G} {z : G}

structure PointsHyp (V L : Subgroup G) (z : G) : Prop where
  comm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a
  sq : ∀ v ∈ V, v * v = 1
  card : Nat.card V = 64
  norm : L ≤ Subgroup.normalizer (V : Set G)
  zL : z ∈ L
  z3 : z ^ 3 = 1
  fpf : ∀ v ∈ V, z * v * z⁻¹ = v → v = 1
  zcent : ∀ y ∈ L, y * z * y⁻¹ * z⁻¹ ∈ V
  faith5 : ∀ s ∈ L, orderOf s = 5 → ∃ v ∈ V, s * v * s⁻¹ ≠ v
  irred : ∀ W : Subgroup G, W ≤ V → L ≤ Subgroup.normalizer (W : Set G) → W = ⊥ ∨ W = V
  five : 5 ∣ Nat.card L
  not25 : ¬ 25 ∣ Nat.card L
  index : Nat.card L ∣ 1080 * Nat.card ↥(L ⊓ Subgroup.centralizer (V : Set G))

@[expose] def hallPts (V L : Subgroup G) : Set (Subgroup G) :=
  {P | ∃ s ∈ L, orderOf s = 5 ∧ P = V ⊓ Subgroup.centralizer ({s} : Set G)}

theorem mem_normalizer_of_conj_smul_eq_self {W : Subgroup G} {g : G}
    (h : MulAut.conj g • W = W) : g ∈ Subgroup.normalizer (W : Set G) := by
  rw [Subgroup.mem_normalizer_iff'']
  intro x
  calc x ∈ W ↔ x ∈ MulAut.conj g • W := by rw [h]
    _ ↔ (MulAut.conj g)⁻¹ • x ∈ W := Subgroup.mem_pointwise_smul_iff_inv_smul_mem
    _ ↔ g⁻¹ * x * g ∈ W := by simp [MulAut.conj_inv_apply]

theorem conj_smul_eq_self_of_mem_normalizer {W : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (W : Set G)) : MulAut.conj g • W = W := by
  ext x
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply]
  exact (Subgroup.mem_normalizer_iff''.mp hg x).symm

theorem conj_smul_inf_centralizer {V : Subgroup G} {g s : G}
    (hg : g ∈ Subgroup.normalizer (V : Set G)) :
    MulAut.conj g • (V ⊓ Subgroup.centralizer ({s} : Set G)) =
      V ⊓ Subgroup.centralizer ({g * s * g⁻¹} : Set G) := by
  ext x
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply]
  rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨hxV, hxs⟩
    refine ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff''.mp hg x).mpr hxV
    · calc x * (g * s * g⁻¹) = g * (g⁻¹ * x * g * s) * g⁻¹ := by group
        _ = g * (s * (g⁻¹ * x * g)) * g⁻¹ := by rw [hxs]
        _ = (g * s * g⁻¹) * x := by group
  · rintro ⟨hxV, hxs⟩
    refine ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff''.mp hg x).mp hxV
    · calc (g⁻¹ * x * g) * s = g⁻¹ * (x * (g * s * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * s * g⁻¹) * x) * g := by rw [hxs]
        _ = s * (g⁻¹ * x * g) := by group

theorem centralizer_singleton_eq_of_zpowers_eq {a b : G}
    (h : Subgroup.zpowers a = Subgroup.zpowers b) :
    Subgroup.centralizer ({a} : Set G) = Subgroup.centralizer ({b} : Set G) := by
  have hca : Subgroup.centralizer (Subgroup.zpowers a : Set G) =
      Subgroup.centralizer ({a} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hcb : Subgroup.centralizer (Subgroup.zpowers b : Set G) =
      Subgroup.centralizer ({b} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  apply le_antisymm
  · rw [← hca]
    apply Subgroup.centralizer_le
    rw [Set.singleton_subset_iff, h]
    exact Subgroup.mem_zpowers b
  · rw [← hcb]
    apply Subgroup.centralizer_le
    rw [Set.singleton_subset_iff, ← h]
    exact Subgroup.mem_zpowers a

theorem conj_smul_eq_self_of_le_centralizer {W : Subgroup G} {c : G}
    (hc : W ≤ Subgroup.centralizer ({c} : Set G)) :
    MulAut.conj c • W = W := by
  have hle : W ≤ MulAut.conj c • W := by
    intro x hx
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply]
    have hcx : x * c = c * x := Subgroup.mem_centralizer_singleton_iff.mp (hc hx)
    have hcalc : c⁻¹ * x * c = x := by
      calc c⁻¹ * x * c = c⁻¹ * (x * c) := by group
        _ = c⁻¹ * (c * x) := by rw [hcx]
        _ = x := by group
    rwa [hcalc]
  have hcard : Nat.card ↥(MulAut.conj c • W) = Nat.card W :=
    Nat.card_congr (Subgroup.equivSMul (MulAut.conj c) W).toEquiv.symm
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard])).symm


theorem exists_conj_zpowers_of_order_five {H : Subgroup G} (hnot25 : ¬ 25 ∣ Nat.card H)
    {a b : G} (ha : a ∈ H) (hb : b ∈ H)
    (hao : orderOf a = 5) (hbo : orderOf b = 5) :
    ∃ g ∈ H, Subgroup.zpowers (g * a * g⁻¹) = Subgroup.zpowers b := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let x : H := ⟨a, ha⟩
  let y : H := ⟨b, hb⟩
  let Hx : Subgroup H := Subgroup.zpowers x
  let Hy : Subgroup H := Subgroup.zpowers y
  have hxord : orderOf x = 5 := by
    change orderOf (⟨a, ha⟩ : H) = 5
    rw [Subgroup.orderOf_mk, hao]
  have hyord : orderOf y = 5 := by
    change orderOf (⟨b, hb⟩ : H) = 5
    rw [Subgroup.orderOf_mk, hbo]
  have hHxcard : Nat.card Hx = 5 := by
    rw [Nat.card_zpowers, hxord]
  have hHycard : Nat.card Hy = 5 := by
    rw [Nat.card_zpowers, hyord]
  have hHxp : IsPGroup 5 Hx := IsPGroup.of_card (n := 1) (by rw [hHxcard]; norm_num)
  have hHyp : IsPGroup 5 Hy := IsPGroup.of_card (n := 1) (by rw [hHycard]; norm_num)
  have hHxidx : ¬ 5 ∣ Hx.index := by
    intro hdvd
    have hmul := Subgroup.index_mul_card Hx
    have h25 : 25 ∣ Nat.card ↥H := by
      rw [← hmul, hHxcard]
      rw [show 25 = 5 * 5 by norm_num]
      exact mul_dvd_mul hdvd dvd_rfl
    exact hnot25 h25
  have hHyidx : ¬ 5 ∣ Hy.index := by
    intro hdvd
    have hmul := Subgroup.index_mul_card Hy
    have h25 : 25 ∣ Nat.card ↥H := by
      rw [← hmul, hHycard]
      rw [show 25 = 5 * 5 by norm_num]
      exact mul_dvd_mul hdvd dvd_rfl
    exact hnot25 h25
  let Sx : Sylow 5 H := hHxp.toSylow hHxidx
  let Sy : Sylow 5 H := hHyp.toSylow hHyidx
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H Sx Sy
  have hSxcoe : (Sx : Subgroup H) = Hx := IsPGroup.toSylow_coe hHxp hHxidx
  have hSycoe : (Sy : Subgroup H) = Hy := IsPGroup.toSylow_coe hHyp hHyidx
  have hsub : MulAut.conj g • Hx = Hy := by
    calc MulAut.conj g • Hx = ↑(g • Sx) := by
          rw [Sylow.coe_subgroup_smul, hSxcoe]
      _ = ↑Sy := by rw [hg]
      _ = Hy := hSycoe
  have hmem : g * x * g⁻¹ ∈ Hy := by
    rw [← hsub]
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply]
    have hgx : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    rw [hgx]
    exact Subgroup.mem_zpowers x
  have hzHy : Subgroup.zpowers (g * x * g⁻¹) = Hy := by
    apply Subgroup.eq_of_le_of_card_ge
    · exact Subgroup.zpowers_le.mpr hmem
    · have hord : orderOf (g * x * g⁻¹) = 5 := by
        have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
        simpa [MulAut.conj_apply, hxord] using this
      rw [hHycard, ← hord, Nat.card_zpowers]
  have hmap := congrArg (fun K : Subgroup H => K.map H.subtype) hzHy
  rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers] at hmap
  exact ⟨(g : G), g.2, by simpa using hmap⟩

theorem natCard_inf_centralizer_eq_fixedPoints {W : Subgroup G} {s : G}
    (hs : s ∈ Subgroup.normalizer (W : Set G)) :
    Nat.card ↥(W ⊓ Subgroup.centralizer ({s} : Set G)) =
      Nat.card (Function.fixedPoints (conjX W ⟨s, hs⟩)) := by
  classical
  refine Nat.card_congr ⟨fun x => ?_, fun y => ?_, ?_, ?_⟩
  · have hxV : (x : G) ∈ W := x.2.1
    have hxcomm : (x : G) * s = s * (x : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp x.2.2
    refine ⟨⟨(x : G), hxV⟩, ?_⟩
    apply Subtype.ext
    change s * (x : G) * s⁻¹ = (x : G)
    calc s * (x : G) * s⁻¹ = (x : G) * s * s⁻¹ := by rw [← hxcomm]
      _ = (x : G) := by group
  · have hy : conjX W ⟨s, hs⟩ y.1 = y.1 := y.2
    have hval : s * (y.1 : G) * s⁻¹ = (y.1 : G) := by
      have := congrArg Subtype.val hy
      simpa [coe_conjX_apply] using this
    have hcomm : (y.1 : G) * s = s * (y.1 : G) := by
      calc (y.1 : G) * s = (s * (y.1 : G) * s⁻¹) * s := by rw [hval]
        _ = s * (y.1 : G) := by group
    exact ⟨(y.1 : G), y.1.2, Subgroup.mem_centralizer_singleton_iff.mpr hcomm⟩
  · intro x; rfl
  · intro y; rfl

theorem card_inf_centralizer_modEq_of_conj_smul_eq_self {W : Subgroup G} {s : G}
    (h5 : orderOf s = 5) (hfix : MulAut.conj s • W = W) :
    Nat.card ↥(W ⊓ Subgroup.centralizer ({s} : Set G)) ≡ Nat.card W [MOD 5] := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hsN : s ∈ Subgroup.normalizer (W : Set G) := mem_normalizer_of_conj_smul_eq_self hfix
  let σ : Equiv.Perm ↥W := conjX W ⟨s, hsN⟩
  have hsub : (⟨s, hsN⟩ : ↥(Subgroup.normalizer (W : Set G))) ^ 5 = 1 := by
    apply Subtype.ext
    change s ^ 5 = 1
    rw [← h5]
    exact pow_orderOf_eq_one s
  have hσ5 : σ ^ 5 = 1 := by
    calc σ ^ 5 = conjX W (⟨s, hsN⟩ ^ 5) := by rw [map_pow]
      _ = 1 := by rw [hsub, map_one]
  haveI : Fintype ↥W := Fintype.ofFinite ↥W
  have hmod := Equiv.Perm.card_fixedPoints_modEq
    (f := (⇑σ : Function.End ↥W)) (p := 5) (n := 1) (by
      rw [pow_one]
      have h2 := Equiv.Perm.coe_pow σ 5
      rw [hσ5, Equiv.Perm.coe_one] at h2
      exact h2.symm)
  have hcard := natCard_inf_centralizer_eq_fixedPoints (W := W) (s := s) hsN
  have hmod' : Nat.card ↥W ≡ Nat.card (Function.fixedPoints σ) [MOD 5] := by
    simpa only [Nat.card_eq_fintype_card] using hmod
  rw [← hcard] at hmod'
  exact hmod'.symm

theorem le_centralizer_of_card_four {W : Subgroup G} {u : G}
    (hW : Nat.card W = 4) (hu : orderOf u = 5)
    (hfix : MulAut.conj u • W = W) :
    W ≤ Subgroup.centralizer ({u} : Set G) := by
  classical
  have hmod := card_inf_centralizer_modEq_of_conj_smul_eq_self (W := W) hu hfix
  have hdvd : Nat.card ↥(W ⊓ Subgroup.centralizer ({u} : Set G)) ∣ 4 := by
    rw [← hW]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hle : Nat.card ↥(W ⊓ Subgroup.centralizer ({u} : Set G)) ≤ 4 := by
    rw [← hW]
    exact Subgroup.card_le_of_le inf_le_left
  have h4 : Nat.card ↥(W ⊓ Subgroup.centralizer ({u} : Set G)) = 4 := by
    set n := Nat.card ↥(W ⊓ Subgroup.centralizer ({u} : Set G))
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two (m := 2)).1 (by simpa using hdvd)
    rw [hk'] at hmod ⊢
    rw [hW] at hmod
    interval_cases k <;> norm_num at hmod
    norm_num
  have heq : W ⊓ Subgroup.centralizer ({u} : Set G) = W :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h4, hW])
  intro x hx
  exact (Subgroup.mem_inf.mp (by rw [heq]; exact hx)).2

theorem le_centralizer_of_card_sixteen {W P : Subgroup G} {u : G}
    (hW : Nat.card W = 16) (hu : orderOf u = 5)
    (hfix : MulAut.conj u • W = W)
    (hPW : P ≤ W) (hP4 : Nat.card P = 4)
    (hPcent : P ≤ Subgroup.centralizer ({u} : Set G)) :
    W ≤ Subgroup.centralizer ({u} : Set G) := by
  classical
  have hmod := card_inf_centralizer_modEq_of_conj_smul_eq_self (W := W) hu hfix
  have hdvd : Nat.card ↥(W ⊓ Subgroup.centralizer ({u} : Set G)) ∣ 16 := by
    rw [← hW]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hle : Nat.card ↥(W ⊓ Subgroup.centralizer ({u} : Set G)) ≤ 16 := by
    rw [← hW]
    exact Subgroup.card_le_of_le inf_le_left
  have hge : 4 ≤ Nat.card ↥(W ⊓ Subgroup.centralizer ({u} : Set G)) := by
    have hPW' : P ≤ W ⊓ Subgroup.centralizer ({u} : Set G) := le_inf hPW hPcent
    calc 4 = Nat.card P := hP4.symm
      _ ≤ Nat.card ↥(W ⊓ Subgroup.centralizer ({u} : Set G)) := Subgroup.card_le_of_le hPW'
  have h16 : Nat.card ↥(W ⊓ Subgroup.centralizer ({u} : Set G)) = 16 := by
    set n := Nat.card ↥(W ⊓ Subgroup.centralizer ({u} : Set G))
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two (m := 4)).1 (by simpa using hdvd)
    rw [hk'] at hmod hge ⊢
    rw [hW] at hmod
    have hk2 : 2 ≤ k := by
      by_contra hklt
      interval_cases k <;> norm_num at hge
    interval_cases k
    · norm_num at hmod
    · norm_num at hmod
    · norm_num
  have heq : W ⊓ Subgroup.centralizer ({u} : Set G) = W :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h16, hW])
  intro x hx
  exact (Subgroup.mem_inf.mp (by rw [heq]; exact hx)).2



theorem conj_smul_eq_self_of_smul_le {W : Subgroup G} {g : G}
    (h : MulAut.conj g • W ≤ W) : MulAut.conj g • W = W := by
  have hcard : Nat.card ↥(MulAut.conj g • W) = Nat.card W :=
    Nat.card_congr (Subgroup.equivSMul (MulAut.conj g) W).toEquiv.symm
  exact Subgroup.eq_of_le_of_card_ge h (by rw [hcard])

theorem PointsHyp.card_ne_two_of_z_invariant (h : PointsHyp V L z) {W : Subgroup G}
    (hWV : W ≤ V) (hzW : MulAut.conj z • W = W) : Nat.card W ≠ 2 := by
  intro hW2
  have hWne : W ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hW2
    norm_num at hW2
  obtain ⟨x, hxW, hx1⟩ := (Subgroup.bot_or_exists_ne_one W).resolve_left hWne
  have hzxW : z * x * z⁻¹ ∈ W := by
    rw [← hzW]
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply]
    have hzx : z⁻¹ * (z * x * z⁻¹) * z = x := by group
    rw [hzx]
    exact hxW
  have hWncard : (W : Set G).ncard = 2 := by
    rw [← Nat.card_coe_set_eq]
    exact hW2
  have hpairncard : ({1, x} : Set G).ncard = 2 := by
    rw [Set.ncard_insert_of_notMem]
    · simp
    · simpa [Set.mem_singleton_iff, eq_comm] using hx1
  have hsub : ({1, x} : Set G) ⊆ (W : Set G) := by
    intro y hy
    rcases Set.mem_insert_iff.mp hy with rfl | hy
    · exact W.one_mem
    · rw [Set.mem_singleton_iff] at hy
      exact hy ▸ hxW
  have hWset : (W : Set G) = {1, x} := by
    symm
    exact Set.eq_of_subset_of_ncard_le hsub (by rw [hWncard, hpairncard])
  have hzx : z * x * z⁻¹ = x := by
    have hmem : z * x * z⁻¹ ∈ ({1, x} : Set G) := by
      rw [← hWset]
      exact hzxW
    rcases Set.mem_insert_iff.mp hmem with h1 | hx
    · exfalso
      apply hx1
      calc x = z⁻¹ * (z * x * z⁻¹) * z := by group
        _ = z⁻¹ * 1 * z := by rw [h1]
        _ = 1 := by group
    · exact hx
  exact hx1 (h.fpf x (hWV hxW) hzx)

theorem PointsHyp.card_fix (h : PointsHyp V L z) {s : G} (hs : s ∈ L) (h5 : orderOf s = 5) :
    Nat.card ↥(V ⊓ Subgroup.centralizer ({s} : Set G)) = 4 := by
  classical
  have hsN : s ∈ Subgroup.normalizer (V : Set G) := h.norm hs
  have hfix : MulAut.conj s • V = V := conj_smul_eq_self_of_mem_normalizer hsN
  have hmod := card_inf_centralizer_modEq_of_conj_smul_eq_self (W := V) h5 hfix
  have hdvd : Nat.card ↥(V ⊓ Subgroup.centralizer ({s} : Set G)) ∣ 64 := by
    rw [← h.card]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hle : Nat.card ↥(V ⊓ Subgroup.centralizer ({s} : Set G)) ≤ 64 := by
    rw [← h.card]
    exact Subgroup.card_le_of_le inf_le_left
  have hmod64 : Nat.card ↥(V ⊓ Subgroup.centralizer ({s} : Set G)) ≡ 4 [MOD 5] := by
    rw [h.card] at hmod
    exact hmod
  set n := Nat.card ↥(V ⊓ Subgroup.centralizer ({s} : Set G)) with hn
  have h4or64 : n = 4 ∨ n = 64 := by
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two (m := 6)).1 (by simpa using hdvd)
    rw [hk'] at hmod64 ⊢
    interval_cases k <;> norm_num at hmod64
    all_goals norm_num
  rcases h4or64 with h4 | h64
  · exact h4
  · exfalso
    have heq : V ⊓ Subgroup.centralizer ({s} : Set G) = V :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [← hn, h64, h.card])
    have hVC : V ≤ Subgroup.centralizer ({s} : Set G) := by
      intro x hx
      exact (Subgroup.mem_inf.mp (by rw [heq]; exact hx)).2
    obtain ⟨v, hvV, hvne⟩ := h.faith5 s hs h5
    have hvC : v ∈ Subgroup.centralizer ({s} : Set G) := hVC hvV
    have hcomm : v * s = s * v := Subgroup.mem_centralizer_singleton_iff.mp hvC
    apply hvne
    calc s * v * s⁻¹ = (v * s) * s⁻¹ := by rw [← hcomm]
      _ = v := by group

theorem PointsHyp.le_of_mem (h : PointsHyp V L z) {P : Subgroup G}
    (hP : P ∈ hallPts V L) : P ≤ V := by
  obtain ⟨s, hs, -, rfl⟩ := hP
  exact inf_le_left

theorem PointsHyp.card_of_mem (h : PointsHyp V L z) {P : Subgroup G}
    (hP : P ∈ hallPts V L) : Nat.card P = 4 := by
  obtain ⟨s, hs, h5, rfl⟩ := hP
  exact h.card_fix hs h5

theorem PointsHyp.z_conj_mem (h : PointsHyp V L z) {P : Subgroup G}
    (hP : P ∈ hallPts V L) {x : G} (hx : x ∈ P) : z * x * z⁻¹ ∈ P := by
  obtain ⟨s, hsL, -, rfl⟩ := hP
  have hxV : x ∈ V := (Subgroup.mem_inf.mp hx).1
  have hxcomm : x * s = s * x :=
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hx).2
  have hzN : z ∈ Subgroup.normalizer (V : Set G) := h.norm h.zL
  have hzv : z * x * z⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.mp hzN x).mp hxV
  have hcent : z * x * z⁻¹ ∈ Subgroup.centralizer ({s} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    set v : G := s * z * s⁻¹ * z⁻¹ with hvdef
    have hvV : v ∈ V := h.zcent s hsL
    have hsz : s * z * s⁻¹ = v * z := by
      rw [hvdef]
      group
    have hxv : v * (z * x * z⁻¹) = (z * x * z⁻¹) * v := h.comm v hvV _ hzv
    have hxs : s * x * s⁻¹ = x := by
      calc s * x * s⁻¹ = (x * s) * s⁻¹ := by rw [← hxcomm]
        _ = x := by group
    have key : s * (z * x * z⁻¹) * s⁻¹ = z * x * z⁻¹ := by
      calc s * (z * x * z⁻¹) * s⁻¹
          = (s * z * s⁻¹) * (s * x * s⁻¹) * (s * z * s⁻¹)⁻¹ := by group
        _ = (v * z) * x * (v * z)⁻¹ := by rw [hsz, hxs]
        _ = v * (z * x * z⁻¹) * v⁻¹ := by group
        _ = (z * x * z⁻¹) * v * v⁻¹ := by rw [hxv]
        _ = z * x * z⁻¹ := by group
    calc (z * x * z⁻¹) * s = (s * (z * x * z⁻¹) * s⁻¹) * s := by rw [key]
      _ = s * (z * x * z⁻¹) := by group
  exact Subgroup.mem_inf.mpr ⟨hzv, hcent⟩


theorem PointsHyp.inf_eq_bot_of_ne (h : PointsHyp V L z) {P Q : Subgroup G}
    (hP : P ∈ hallPts V L) (hQ : Q ∈ hallPts V L) (hne : P ≠ Q) :
    P ⊓ Q = ⊥ := by
  classical
  have hP4 : Nat.card P = 4 := h.card_of_mem hP
  have hQ4 : Nat.card Q = 4 := h.card_of_mem hQ
  have hdvd : Nat.card ↥(P ⊓ Q) ∣ 4 := by
    rw [← hP4]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hne2 : Nat.card ↥(P ⊓ Q) ≠ 2 := by
    intro h2
    have hWne : P ⊓ Q ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.card_bot] at h2
      norm_num at h2
    obtain ⟨x, hxW, hx1⟩ :=
      (Subgroup.bot_or_exists_ne_one (P ⊓ Q)).resolve_left hWne
    have hzxW : z * x * z⁻¹ ∈ P ⊓ Q :=
      Subgroup.mem_inf.mpr ⟨h.z_conj_mem hP hxW.1, h.z_conj_mem hQ hxW.2⟩
    have hWncard : (P ⊓ Q : Set G).ncard = 2 := by
      change Nat.card ↥(P ⊓ Q) = 2
      exact h2
    have hpairncard : ({1, x} : Set G).ncard = 2 := by
      rw [Set.ncard_insert_of_notMem]
      · simp
      · simpa [Set.mem_singleton_iff, eq_comm] using hx1
    have hsub : ({1, x} : Set G) ⊆ (P ⊓ Q : Set G) := by
      intro y hy
      rcases Set.mem_insert_iff.mp hy with rfl | hy
      · exact (P ⊓ Q).one_mem
      · rw [Set.mem_singleton_iff] at hy
        exact hy ▸ hxW
    have hWset : (P ⊓ Q : Set G) = {1, x} := by
      symm
      exact Set.eq_of_subset_of_ncard_le hsub (by rw [hWncard, hpairncard])
    have hzx : z * x * z⁻¹ = x := by
      have hmem : z * x * z⁻¹ ∈ ({1, x} : Set G) := by rw [← hWset]; exact hzxW
      rcases Set.mem_insert_iff.mp hmem with h1 | hx
      · exfalso
        apply hx1
        calc x = z⁻¹ * (z * x * z⁻¹) * z := by group
          _ = z⁻¹ * 1 * z := by rw [h1]
          _ = 1 := by group
      · exact hx
    exact hx1 (h.fpf x (h.le_of_mem hP hxW.1) hzx)
  have hcases : Nat.card ↥(P ⊓ Q) = 1 ∨ Nat.card ↥(P ⊓ Q) = 4 := by
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two (m := 2)).1 (by simpa using hdvd)
    have hk'' : Nat.card ↥(P ⊓ Q) = 2 ^ k := by simpa using hk'
    rw [hk''] at hne2 ⊢
    interval_cases k
    · left; norm_num
    · exact absurd rfl hne2
    · right; norm_num
  rcases hcases with h1 | h4
  · exact Subgroup.eq_bot_of_card_eq (P ⊓ Q) h1
  · exfalso
    apply hne
    have hPQ : P ⊓ Q = P :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h4, hP4])
    have hPleQ : P ≤ Q := by
      intro x hx
      have : x ∈ P ⊓ Q := by rw [hPQ]; exact hx
      exact (Subgroup.mem_inf.mp this).2
    exact Subgroup.eq_of_le_of_card_ge hPleQ (by rw [hQ4, hP4])

theorem PointsHyp.card_hallPts_le (h : PointsHyp V L z) :
    Nat.card (hallPts V L) ≤ 21 := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  let nonone : Subgroup G → Finset G := fun P =>
    ((Finset.univ : Finset P).erase ⟨1, P.one_mem⟩).image Subtype.val
  have mem_nonone : ∀ {P : Subgroup G} {x : G},
      x ∈ nonone P ↔ x ≠ 1 ∧ x ∈ P := by
    intro P x
    change x ∈ (((Finset.univ : Finset P).erase ⟨1, P.one_mem⟩).image Subtype.val) ↔
      x ≠ 1 ∧ x ∈ P
    constructor
    · intro hx
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
      rw [Finset.mem_erase] at hp
      exact ⟨fun h => hp.1 (Subtype.ext h), p.2⟩
    · rintro ⟨hx1, hxP⟩
      refine Finset.mem_image.mpr ⟨⟨x, hxP⟩, ?_, rfl⟩
      rw [Finset.mem_erase]
      exact ⟨fun h => hx1 (congrArg Subtype.val h), Finset.mem_univ _⟩
  have card_nonone : ∀ P : Subgroup G, Nat.card P = 4 → (nonone P).card = 3 := by
    intro P hP
    change (((Finset.univ : Finset P).erase ⟨1, P.one_mem⟩).image Subtype.val).card = 3
    rw [Finset.card_image_of_injective _ Subtype.val_injective,
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      ← Nat.card_eq_fintype_card, hP]
  have subset_nonone : ∀ P ∈ hallPts V L, nonone P ⊆ nonone V := by
    intro P hP x hx
    rw [mem_nonone] at hx ⊢
    exact ⟨hx.1, h.le_of_mem hP hx.2⟩
  have hdisj : Set.PairwiseDisjoint
      ((Finset.univ : Finset ↥(hallPts V L)) : Set ↥(hallPts V L))
      (fun P => nonone P.1) := by
    intro P _ Q _ hPQ
    change Disjoint (nonone P.1) (nonone Q.1)
    rw [Finset.disjoint_left]
    intro x hxP hxQ
    rw [mem_nonone] at hxP hxQ
    have hbot : (P.1 : Subgroup G) ⊓ Q.1 = ⊥ :=
      h.inf_eq_bot_of_ne P.2 Q.2 (fun heq => hPQ (Subtype.ext heq))
    have : x ∈ (⊥ : Subgroup G) := by
      rw [← hbot]
      exact Subgroup.mem_inf.mpr ⟨hxP.2, hxQ.2⟩
    exact hxP.1 (Subgroup.mem_bot.mp this)
  have hcard_union : ((Finset.univ : Finset ↥(hallPts V L)).biUnion
      (fun P => nonone P.1)).card = 3 * Nat.card (hallPts V L) := by
    rw [Finset.card_biUnion hdisj]
    have : ∀ P : ↥(hallPts V L), (nonone P.1).card = 3 :=
      fun P => card_nonone P.1 (h.card_of_mem P.2)
    simp [this, Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card, mul_comm]
  have hunion_le : ((Finset.univ : Finset ↥(hallPts V L)).biUnion
      (fun P => nonone P.1)).card ≤ (nonone V).card := by
    apply Finset.card_le_card
    intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨P, hP, hxP⟩ := hx
    exact subset_nonone P.1 P.2 hxP
  have hVcard : (nonone V).card = 63 := by
    change (((Finset.univ : Finset V).erase ⟨1, V.one_mem⟩).image Subtype.val).card = 63
    rw [Finset.card_image_of_injective _ Subtype.val_injective,
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      ← Nat.card_eq_fintype_card, h.card]
  have h3 : 3 * Nat.card (hallPts V L) ≤ 63 := by
    rw [← hcard_union, ← hVcard]
    exact hunion_le
  omega


theorem smul_mem_hallPts {V L : Subgroup G} {g : G}
    (hgV : g ∈ Subgroup.normalizer (V : Set G))
    (hgL : g ∈ Subgroup.normalizer (L : Set G))
    {P : Subgroup G} (hP : P ∈ hallPts V L) :
    MulAut.conj g • P ∈ hallPts V L := by
  obtain ⟨s, hsL, h5, rfl⟩ := hP
  have hgs : g * s * g⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hgL s).mp hsL
  have hord : orderOf (g * s * g⁻¹) = 5 := by
    have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective s
    simpa [MulAut.conj_apply, h5] using this
  refine ⟨g * s * g⁻¹, hgs, hord, ?_⟩
  rw [conj_smul_inf_centralizer hgV]

theorem PointsHyp.card_hallPts (h : PointsHyp V L z) :
    Nat.card (hallPts V L) = 6 := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨s₀L, hs₀ord⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥L) 5 (by simpa using h.five)
  let s₀ : G := (s₀L : G)
  have hs₀L : s₀ ∈ L := s₀L.2
  have h5₀ : orderOf s₀ = 5 := (Subgroup.orderOf_coe s₀L).trans hs₀ord
  let P₀ : Subgroup G := V ⊓ Subgroup.centralizer ({s₀} : Set G)
  have hP₀mem : P₀ ∈ hallPts V L := ⟨s₀, hs₀L, h5₀, rfl⟩
  have hP₀card : Nat.card P₀ = 4 := h.card_fix hs₀L h5₀
  letI : MulAction ↥L (Subgroup G) :=
    MulAction.compHom (Subgroup G) ((MulAut.conj : G →* MulAut G).comp L.subtype)
  have hsmul : ∀ (g : ↥L) (P : Subgroup G), g • P = MulAut.conj (g : G) • P :=
    fun g P => MulAction.compHom_smul_def _ g P
  have horbit : MulAction.orbit ↥L P₀ = hallPts V L := by
    ext P
    constructor
    · rintro ⟨g, rfl⟩
      change g • P₀ ∈ hallPts V L
      rw [hsmul g P₀]
      exact smul_mem_hallPts (h.norm g.2) ((Subgroup.le_normalizer (H := L)) g.2) hP₀mem
    · intro hP
      obtain ⟨s, hsL, h5, rfl⟩ := hP
      obtain ⟨gL, hgL, hz⟩ := exists_conj_zpowers_of_order_five (H := L)
        (by simpa using h.not25) hs₀L hsL h5₀ h5
      refine ⟨⟨gL, hgL⟩, ?_⟩
      change (⟨gL, hgL⟩ : ↥L) • P₀ = V ⊓ Subgroup.centralizer ({s} : Set G)
      rw [hsmul ⟨gL, hgL⟩ P₀]
      have hnorm : (gL : G) ∈ Subgroup.normalizer (V : Set G) := h.norm hgL
      rw [conj_smul_inf_centralizer hnorm, centralizer_singleton_eq_of_zpowers_eq hz]
  have hstab_card : Nat.card (hallPts V L) = (MulAction.stabilizer ↥L P₀).index := by
    rw [Nat.card_coe_set_eq, ← horbit, ← MulAction.index_stabilizer]
  let C : Subgroup G := L ⊓ Subgroup.centralizer (V : Set G)
  have hCstab : C.subgroupOf L ≤ MulAction.stabilizer ↥L P₀ := by
    intro c hc
    rw [MulAction.mem_stabilizer_iff]
    have hcC : (c : G) ∈ C := Subgroup.mem_subgroupOf.mp hc
    have hcenV : (c : G) ∈ Subgroup.centralizer (V : Set G) :=
      (Subgroup.mem_inf.mp hcC).2
    have hle : P₀ ≤ Subgroup.centralizer ({(c : G)} : Set G) := by
      intro x hx
      have hxV : x ∈ V := (Subgroup.mem_inf.mp hx).1
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hcenV x hxV)
    rw [hsmul (c : ↥L) P₀]
    exact conj_smul_eq_self_of_le_centralizer hle
  have hCindex_dvd : (MulAction.stabilizer ↥L P₀).index ∣ (C.subgroupOf L).index :=
    Subgroup.index_dvd_of_le hCstab
  have hCidx : (C.subgroupOf L).index ∣ 1080 := by
    have hcardCsub : Nat.card ↥(C.subgroupOf L) = Nat.card C :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    have hLcard : Nat.card L = (C.subgroupOf L).index * Nat.card C := by
      rw [← Subgroup.index_mul_card (H := C.subgroupOf L), hcardCsub]
    have hdvd : (C.subgroupOf L).index * Nat.card C ∣ 1080 * Nat.card C := by
      rw [← hLcard]
      exact h.index
    exact Nat.dvd_of_mul_dvd_mul_right Nat.card_pos hdvd
  have hdiv1080 : Nat.card (hallPts V L) ∣ 1080 := by
    rw [hstab_card]
    exact hCindex_dvd.trans hCidx
  have hs₀V : s₀ ∈ Subgroup.normalizer (V : Set G) := h.norm hs₀L
  have hs₀Lnorm : s₀ ∈ Subgroup.normalizer (L : Set G) :=
    (Subgroup.le_normalizer (H := L)) hs₀L
  have hs₀Vinv : s₀⁻¹ ∈ Subgroup.normalizer (V : Set G) := inv_mem hs₀V
  have hs₀Lnorminv : s₀⁻¹ ∈ Subgroup.normalizer (L : Set G) := inv_mem hs₀Lnorm
  let F : Equiv.Perm (Subgroup G) := MulAction.toPerm (MulAut.conj s₀)
  have hpres : ∀ P : Subgroup G, P ∈ hallPts V L ↔ F P ∈ hallPts V L := by
    intro P
    constructor
    · intro hP
      simpa [F] using smul_mem_hallPts hs₀V hs₀Lnorm hP
    · intro hP
      have h2 := smul_mem_hallPts hs₀Vinv hs₀Lnorminv (by simpa [F] using hP)
      have hcomp : MulAut.conj s₀⁻¹ • (MulAut.conj s₀ • P) = P := by
        rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
      simpa [hcomp] using h2
  let T : Equiv.Perm ↥(hallPts V L) := F.subtypePerm (fun P => (hpres P).symm)
  have hF5 : F ^ 5 = 1 := by
    have hA5 : (MulAut.conj s₀ : MulAut G) ^ 5 = 1 := by
      rw [← map_pow]
      have hs5 : s₀ ^ 5 = 1 := by
        rw [← h5₀]
        exact pow_orderOf_eq_one s₀
      rw [hs5, map_one]
    dsimp only [F]
    change (MulAction.toPermHom (MulAut G) (Subgroup G) (MulAut.conj s₀)) ^ 5 = 1
    have hmap := map_pow (MulAction.toPermHom (MulAut G) (Subgroup G)) (MulAut.conj s₀) 5
    rw [← hmap, hA5, map_one]
  have hT5 : T ^ 5 = 1 := by
    dsimp only [T]
    apply Equiv.ext
    intro P
    change ((F.subtypePerm (fun P => (hpres P).symm)) ^ 5) P = P
    rw [Equiv.Perm.subtypePerm_pow, Equiv.Perm.subtypePerm_apply]
    apply Subtype.ext
    change (F ^ 5) P.1 = P.1
    rw [hF5]
    rfl
  have hfixP₀ : T ⟨P₀, hP₀mem⟩ = ⟨P₀, hP₀mem⟩ := by
    apply Subtype.ext
    dsimp only [T, F, Equiv.Perm.subtypePerm_apply]
    change MulAut.conj s₀ • P₀ = P₀
    exact conj_smul_eq_self_of_le_centralizer inf_le_right
  have hfix_unique : ∀ P : ↥(hallPts V L), T P = P → P = ⟨P₀, hP₀mem⟩ := by
    intro P hP
    have hF : F P.1 = P.1 := by
      have := congrArg Subtype.val hP
      simpa [T, Equiv.Perm.subtypePerm_apply] using this
    have hsm : MulAut.conj s₀ • P.1 = P.1 := by
      simpa [F] using hF
    have hPcard : Nat.card P.1 = 4 := h.card_of_mem P.2
    have hcent : P.1 ≤ Subgroup.centralizer ({s₀} : Set G) :=
      le_centralizer_of_card_four hPcard h5₀ hsm
    have hleP₀ : P.1 ≤ P₀ := le_inf (h.le_of_mem P.2) hcent
    have heq : P.1 = P₀ :=
      Subgroup.eq_of_le_of_card_ge hleP₀ (by rw [hP₀card, hPcard])
    exact Subtype.ext heq
  have hfixcard : Fintype.card (Function.fixedPoints T) = 1 := by
    have hset : Function.fixedPoints T = {⟨P₀, hP₀mem⟩} := by
      ext P
      constructor
      · intro hP
        exact hfix_unique P hP
      · intro hP
        rw [Set.mem_singleton_iff] at hP
        subst hP
        exact hfixP₀
    have hnat : Nat.card (Function.fixedPoints T) = 1 := by
      rw [hset]
      simp
    simpa [Nat.card_eq_fintype_card] using hnat
  have hmod1 : Nat.card (hallPts V L) ≡ 1 [MOD 5] := by
    have h := Equiv.Perm.card_fixedPoints_modEq
      (f := (⇑T : Function.End ↥(hallPts V L))) (p := 5) (n := 1) (by
        rw [pow_one]
        have h2 := Equiv.Perm.coe_pow T 5
        rw [hT5, Equiv.Perm.coe_one] at h2
        exact h2.symm)
    rw [hfixcard] at h
    simpa [Nat.card_eq_fintype_card] using h
  have hne1 : Nat.card (hallPts V L) ≠ 1 := by
    intro h1
    have hset : hallPts V L = {P₀} := by
      rw [Set.eq_singleton_iff_unique_mem]
      refine ⟨hP₀mem, ?_⟩
      intro P hP
      by_contra hne
      have hsub : ({P₀, P} : Set (Subgroup G)) ⊆ hallPts V L := by
        intro Q hQ
        rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hQ
        rcases hQ with rfl | rfl <;> assumption
      have hpairncard : ({P₀, P} : Set (Subgroup G)).ncard = 2 :=
        Set.ncard_pair (Ne.symm hne)
      have hle : 2 ≤ Nat.card (hallPts V L) := by
        rw [← hpairncard, ← Nat.card_coe_set_eq]
        exact Set.ncard_le_ncard hsub
      omega
    have hLnorm : L ≤ Subgroup.normalizer (P₀ : Set G) := by
      intro g hg
      have hgP : MulAut.conj g • P₀ ∈ hallPts V L :=
        smul_mem_hallPts (h.norm hg) ((Subgroup.le_normalizer (H := L)) hg) hP₀mem
      have hgP' : MulAut.conj g • P₀ ∈ ({P₀} : Set (Subgroup G)) := by
        rw [← hset]
        exact hgP
      exact mem_normalizer_of_conj_smul_eq_self (by simpa using hgP')
    rcases h.irred P₀ inf_le_left hLnorm with hbot | htop
    · have : Nat.card P₀ = 1 := by rw [hbot, Subgroup.card_bot]
      omega
    · have : Nat.card P₀ = 64 := by rw [htop, h.card]
      omega
  have hle21 := h.card_hallPts_le
  set n := Nat.card (hallPts V L) with hn
  have hnle : n ≤ 21 := by simpa [hn] using hle21
  have hndvd : n ∣ 1080 := by simpa [hn] using hdiv1080
  have hnmod : n ≡ 1 [MOD 5] := by simpa [hn] using hmod1
  have hnne : n ≠ 1 := by simpa [hn] using hne1
  have hmem : n ∈ (Finset.range 22).filter
      (fun m => m ∣ 1080 ∧ m ≡ 1 [MOD 5] ∧ m ≠ 1) := by
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hndvd, hnmod, hnne⟩
  have hfilter : (Finset.range 22).filter
      (fun m => m ∣ 1080 ∧ m ≡ 1 [MOD 5] ∧ m ≠ 1) = {6} := by
    decide
  rw [hfilter] at hmem
  simpa using hmem

theorem PointsHyp.conj_z_smul_eq_self (h : PointsHyp V L z) {Q : Subgroup G}
    (hQ : Q ∈ hallPts V L) : MulAut.conj z • Q = Q := by
  apply conj_smul_eq_self_of_smul_le
  intro x hx
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply] at hx
  have := h.z_conj_mem hQ hx
  have hzx : z * (z⁻¹ * x * z) * z⁻¹ = x := by group
  rwa [hzx] at this

theorem PointsHyp.inf_sup_eq_bot (h : PointsHyp V L z) :
    ∀ P ∈ hallPts V L, ∀ P' ∈ hallPts V L, ∀ P'' ∈ hallPts V L,
      P ≠ P' → P ≠ P'' → P' ≠ P'' → P'' ⊓ (P ⊔ P') = ⊥ := by
  intro P hP P' hP' P'' hP'' hPP' hPP'' hP'P''
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  by_contra hne
  let ℓ : Subgroup G := P ⊔ P'
  have hPcard : Nat.card P = 4 := h.card_of_mem hP
  have hP'card : Nat.card P' = 4 := h.card_of_mem hP'
  have hP''card : Nat.card P'' = 4 := h.card_of_mem hP''
  have hPle : P ≤ V := h.le_of_mem hP
  have hP'le : P' ≤ V := h.le_of_mem hP'
  have hP''le : P'' ≤ V := h.le_of_mem hP''
  have hPP'bot : P ⊓ P' = ⊥ := h.inf_eq_bot_of_ne hP hP' hPP'
  have hℓcard : Nat.card ℓ = 16 := by
    dsimp only [ℓ]
    rw [GL83.CompFam.card_sup_of_commute_of_inf_eq_bot
      (fun x hx y hy => h.comm x (hPle hx) y (hP'le hy)) hPP'bot]
    rw [hPcard, hP'card]
  have hzℓ : MulAut.conj z • ℓ = ℓ := by
    dsimp only [ℓ]
    rw [Subgroup.smul_sup, h.conj_z_smul_eq_self hP, h.conj_z_smul_eq_self hP']
  let W : Subgroup G := P'' ⊓ ℓ
  have hzW : MulAut.conj z • W = W := by
    dsimp only [W]
    rw [Subgroup.smul_inf, h.conj_z_smul_eq_self hP'', hzℓ]
  have hWleP'' : W ≤ P'' := inf_le_left
  have hWleℓ : W ≤ ℓ := inf_le_right
  have hWdiv : Nat.card W ∣ 4 := by
    rw [← hP''card]
    exact Subgroup.card_dvd_of_le hWleP''
  have hWne : W ≠ ⊥ := by
    intro hbot
    apply hne
    rw [← hbot]
  have hW2 : Nat.card W ≠ 2 :=
    h.card_ne_two_of_z_invariant (hWleP''.trans hP''le) hzW
  have hW4 : Nat.card W = 4 := by
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two (m := 2)).1 (by simpa using hWdiv)
    have hk'' : Nat.card ↥W = 2 ^ k := by simpa using hk'
    rw [hk''] at hW2 ⊢
    interval_cases k
    · exfalso
      exact hWne (Subgroup.eq_bot_of_card_eq W (by simpa using hk''))
    · exact absurd rfl hW2
    · norm_num
  have hW_eq : W = P'' :=
    Subgroup.eq_of_le_of_card_ge hWleP'' (by rw [hP''card, hW4])
  have hP''leℓ : P'' ≤ P ⊔ P' := by
    rw [← hW_eq]
    exact hWleℓ
  obtain ⟨s, hsL, h5s, hPeq⟩ := hP
  have hPmem : P ∈ hallPts V L := ⟨s, hsL, h5s, hPeq⟩
  have hPfixed_s : MulAut.conj s • P = P := by
    rw [hPeq]
    exact conj_smul_eq_self_of_le_centralizer inf_le_right
  have hfix_only : ∀ Q ∈ hallPts V L, MulAut.conj s • Q = Q → Q = P := by
    intro Q hQ hsm
    have hQcard : Nat.card Q = 4 := h.card_of_mem hQ
    have hcent : Q ≤ Subgroup.centralizer ({s} : Set G) :=
      le_centralizer_of_card_four hQcard h5s hsm
    rw [hPeq]
    have hleP : Q ≤ V ⊓ Subgroup.centralizer ({s} : Set G) := le_inf (h.le_of_mem hQ) hcent
    exact Subgroup.eq_of_le_of_card_ge hleP (by rw [← hPeq, hPcard, hQcard])
  let H : Subgroup ↥L := Subgroup.zpowers (⟨s, hsL⟩ : ↥L)
  have hHcard : Nat.card H = 5 := by
    rw [Nat.card_zpowers]
    exact (Subgroup.orderOf_mk s hsL).trans h5s
  letI : MulAction ↥L (Subgroup G) :=
    MulAction.compHom (Subgroup G) ((MulAut.conj : G →* MulAut G).comp L.subtype)
  letI : MulAction H (Subgroup G) := MulAction.compHom (Subgroup G) H.subtype
  have hHsmul : ∀ (k : H) (Q : Subgroup G), k • Q = MulAut.conj (k : G) • Q := by
    intro k Q
    simp [MulAction.compHom_smul_def]
  have hPfixedH : ∀ k : H, k • P = P := by
    intro k
    rw [hHsmul]
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp k.2
    have hcoe : (k : G) = s ^ i := by
      rw [← hi]
      simp
    rw [hcoe]
    apply conj_smul_eq_self_of_le_centralizer
    intro x hx
    have hx' : x ∈ V ⊓ Subgroup.centralizer ({s} : Set G) := by
      rwa [hPeq] at hx
    have hxmem : x ∈ Subgroup.centralizer ({s} : Set G) := (Subgroup.mem_inf.mp hx').2
    have hxcomm : Commute x s :=
      Subgroup.mem_centralizer_singleton_iff.mp hxmem
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hxcomm.zpow_right i)
  have hOsub : MulAction.orbit H P' ⊆ hallPts V L := by
    rintro Q ⟨k, rfl⟩
    change k • P' ∈ hallPts V L
    rw [hHsmul k P']
    exact smul_mem_hallPts (h.norm k.1.2) ((Subgroup.le_normalizer (H := L)) k.1.2) hP'
  have hPnotO : P ∉ MulAction.orbit H P' := by
    rintro ⟨k, hk⟩
    change k • P' = P at hk
    have hkP : k • P = P := hPfixedH k
    have : P' = P := by
      calc P' = k⁻¹ • (k • P') := (inv_smul_smul k P').symm
        _ = k⁻¹ • P := by rw [hk]
        _ = k⁻¹ • (k • P) := by rw [hkP]
        _ = P := inv_smul_smul k P
    exact hPP' this.symm
  have hHp : IsPGroup 5 H := IsPGroup.of_card (n := 1) (by rw [hHcard]; norm_num)
  let h₀ : H := ⟨⟨s, hsL⟩, Subgroup.mem_zpowers _⟩
  have hh₀ : (h₀ : G) = s := rfl
  have hnotfix : h₀ • P' ≠ P' := by
    intro hfix
    rw [hHsmul, hh₀] at hfix
    exact hPP' (hfix_only P' hP' hfix).symm
  let O : Set (Subgroup G) := MulAction.orbit H P'
  have hO_le : O.ncard ≤ 5 := by
    have hsubO : O ⊆ (hallPts V L) \ {P} := by
      intro Q hQ
      exact ⟨hOsub hQ, fun hQP => hPnotO (hQP ▸ hQ)⟩
    have hdiff : ((hallPts V L) \ {P}).ncard = 5 := by
      have h6 : (hallPts V L).ncard = 6 := by
        simpa using (Nat.card_coe_set_eq (hallPts V L)).symm.trans h.card_hallPts
      rw [Set.ncard_sdiff_singleton_of_mem hPmem, h6]
    calc O.ncard ≤ ((hallPts V L) \ {P}).ncard := Set.ncard_le_ncard hsubO
      _ = 5 := hdiff
  have hO_one : Nat.card O ≠ 1 := by
    intro h1
    haveI : Subsingleton O := (Nat.card_eq_one_iff_unique.mp h1).1
    have hmem₁ : h₀ • P' ∈ O := MulAction.mem_orbit P' h₀
    have hmem₂ : P' ∈ O := MulAction.mem_orbit_self P'
    have hEq : (⟨h₀ • P', hmem₁⟩ : O) = ⟨P', hmem₂⟩ := Subsingleton.elim _ _
    exact hnotfix (congrArg Subtype.val hEq)
  obtain ⟨m, hmO⟩ := hHp.card_orbit (a := P')
  have hm1 : m = 1 := by
    have hmpos : 0 < m := by
      by_contra h0
      have hm0 : m = 0 := by omega
      apply hO_one
      rw [hmO, hm0]
      norm_num
    have hmle : m ≤ 1 := by
      by_contra h1
      have hm2 : 2 ≤ m := by omega
      have hpow : 5 ^ 2 ≤ 5 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
      have hle : 5 ^ m ≤ 5 := by
        rw [← hmO]
        exact hO_le
      omega
    omega
  have hOcard : Nat.card O = 5 := by
    rw [hmO, hm1]
    norm_num
  have hO_eq : O = (hallPts V L) \ {P} := by
    refine Set.eq_of_subset_of_ncard_le (s := O) (t := (hallPts V L) \ {P})
      ?_ ?_ (Set.toFinite _)
    · exact fun Q hQ => ⟨hOsub hQ, fun hQP => hPnotO (hQP ▸ hQ)⟩
    · have h6 : (hallPts V L).ncard = 6 := by
        simpa using (Nat.card_coe_set_eq (hallPts V L)).symm.trans h.card_hallPts
      have hO5 : O.ncard = 5 := by
        simpa using (Nat.card_coe_set_eq O).symm.trans hOcard
      rw [Set.ncard_sdiff_singleton_of_mem hPmem, h6, hO5]
  have hP''O : P'' ∈ O := by
    rw [hO_eq]
    exact ⟨hP'', fun h => hPP'' h.symm⟩
  obtain ⟨k, hk⟩ := MulAction.mem_orbit_iff.mp hP''O
  let u : G := (k : G)
  have huP' : MulAut.conj u • P' = P'' := by
    rw [← hk]
    exact (hHsmul k P').symm
  have huP : MulAut.conj u • P = P := hPfixedH k
  have hu_ne : u ≠ 1 := by
    intro hu1
    apply hP'P''
    calc P' = MulAut.conj u • P' := by rw [hu1]; simp
      _ = P'' := huP'
  have hu5 : u ^ 5 = 1 := by
    have hk5 : k ^ 5 = 1 := by
      have := pow_card_eq_one' (G := H) (x := k)
      rwa [hHcard] at this
    have hcoe := congrArg (fun z : H => (z : G)) hk5
    simpa [u, Subgroup.coe_pow] using hcoe
  have huord : orderOf u = 5 := orderOf_eq_prime hu5 hu_ne
  have huℓ : MulAut.conj u • ℓ = ℓ := by
    apply conj_smul_eq_self_of_smul_le
    change MulAut.conj u • (P ⊔ P') ≤ P ⊔ P'
    rw [Subgroup.smul_sup, huP, huP']
    exact sup_le le_sup_left hP''leℓ
  have hPcent_u : P ≤ Subgroup.centralizer ({u} : Set G) :=
    le_centralizer_of_card_four hPcard huord huP
  have hℓleC : ℓ ≤ Subgroup.centralizer ({u} : Set G) :=
    le_centralizer_of_card_sixteen hℓcard huord huℓ le_sup_left hPcard hPcent_u
  have huP'fix : MulAut.conj u • P' = P' :=
    conj_smul_eq_self_of_le_centralizer (le_trans le_sup_right hℓleC)
  exact hP'P'' (huP'fix.symm.trans huP')

theorem conj_mem_hallPts {V L : Subgroup G} {g : G}
    (hgV : g ∈ Subgroup.normalizer (V : Set G))
    (hgL : g ∈ Subgroup.normalizer (L : Set G))
    {P : Subgroup G} (hP : P ∈ hallPts V L) :
    ∃ P' ∈ hallPts V L, ∀ x ∈ P, g * x * g⁻¹ ∈ P' := by
  obtain ⟨s, hsL, h5, rfl⟩ := hP
  have hgs : g * s * g⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hgL s).mp hsL
  have hord : orderOf (g * s * g⁻¹) = 5 := by
    have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective s
    simpa [MulAut.conj_apply, h5] using this
  refine ⟨MulAut.conj g • (V ⊓ Subgroup.centralizer ({s} : Set G)), ?_, ?_⟩
  · refine ⟨g * s * g⁻¹, hgs, hord, ?_⟩
    rw [conj_smul_inf_centralizer hgV]
  · intro x hx
    have hsm : MulAut.conj g • x = g * x * g⁻¹ := by
      simp [MulAut.conj_apply]
    rw [← hsm]
    exact Subgroup.smul_mem_pointwise_smul x (MulAut.conj g) _ hx

theorem _root_.CFSG.ComponentClassification.AS81.HexaCoord.psi_mem_hexaM_of_maps
    {X R : Subgroup G} {pts : Set (Subgroup G)} {rep : Fin 64 → G}
    (hc : HexaCoord X R pts rep) (hc15 : hexaCheck = true) (hS : hexaStabCheck = true)
    (n : ↥(normalizer (X : Set G)))
    (hn : ∀ P ∈ pts, ∃ P' ∈ pts, ∀ x ∈ P, (n : G) * x * (n : G)⁻¹ ∈ P') :
    hc.psi n ∈ hexaM := by
  have hlen : hexaOval.length = 6 := rfl
  refine mem_hexaM_of_stab hc15 hS (hc.psi_add n) fun L hL => ?_
  obtain ⟨j, hj, hjL⟩ := List.mem_iff_getElem.1 hL
  rw [hlen] at hj
  obtain ⟨P, hP, hPL⟩ := hc.line j hj
  obtain ⟨P', hP', hPP'⟩ := hn P hP
  obtain ⟨j', hj', hP'L⟩ := hc.pt P' hP'
  refine ⟨hexaOval[j']!, ?_, fun x hx => ?_⟩
  · rw [getElem!_pos hexaOval j' (by rw [hlen]; exact hj')]
    exact List.getElem_mem _
  · have hjx : x.val ∈ hexaOval[j]! := by
      rw [getElem!_pos hexaOval j (by rw [hlen]; exact hj), hjL]
      exact hx
    have hxP : rep x ∈ P := (hPL x).2 hjx
    refine (hP'L _).1 ?_
    rw [hc.rep_psi]
    exact hPP' _ hxP


theorem PointsHyp.exists_hexaCoord (h : PointsHyp V L z)
    (hS : CFSG.ComponentClassification.AS81.Hexa.hexaStabCheck = true) :
    ∃ R ∈ hallPts V L, ∃ rep : Fin 64 → G, HexaCoord V R (hallPts V L) rep := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨s₀L, hs₀ord⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥L) 5 (by simpa using h.five)
  let s₀ : G := (s₀L : G)
  have hs₀L : s₀ ∈ L := s₀L.2
  have h5₀ : orderOf s₀ = 5 := (Subgroup.orderOf_coe s₀L).trans hs₀ord
  let R : Subgroup G := V ⊓ Subgroup.centralizer ({s₀} : Set G)
  have hR : R ∈ hallPts V L := ⟨s₀, hs₀L, h5₀, rfl⟩
  exact ⟨R, hR, CFSG.ComponentClassification.AS81.exists_hexaCoord (R := R) hS h.comm h.sq
    h.card (fun P hP => h.le_of_mem hP) (fun P hP => h.card_of_mem hP) h.inf_sup_eq_bot
    h.card_hallPts hR⟩

end CFSG.CGT.Hall82
