module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphOmegaRows

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

section Abstract

variable {G : Type*} [Group G]

theorem eq_one_of_mul_self_of_mem_of_odd_card {H : Subgroup G} (hodd : Odd (Nat.card H)) {z : G}
    (hz : z ∈ H) (hzz : z * z = 1) : z = 1 := by
  have h1 : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hzz)
  have h2 : orderOf z ∣ Nat.card H := Subgroup.orderOf_dvd_natCard H hz
  have h3 : orderOf z ∣ Nat.gcd 2 (Nat.card H) := Nat.dvd_gcd h1 h2
  rw [Nat.Coprime.gcd_eq_one (Nat.coprime_two_left.2 hodd), Nat.dvd_one] at h3
  exact orderOf_eq_one_iff.1 h3

theorem eq_of_forall_conj_eq_conj_of_odd {M : Subgroup G} (hZ : M ⊓ centralizer (M : Set G) = ⊥)
    (hodd : Odd (Nat.card (centralizer (M : Set G)))) {w m : G} (hww : w * w = 1) (hm : m ∈ M)
    (hact : ∀ x ∈ M, w * x * w⁻¹ = m * x * m⁻¹) : w = m := by
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
  have hmw : w * m = m * w := by
    have h := hact m hm
    calc w * m = w * m * w⁻¹ * w := by group
      _ = m * m * m⁻¹ * w := by rw [h]
      _ = m * w := by group
  have hm2 : m * m = 1 := by
    have h1 : m * m ∈ M ⊓ centralizer (M : Set G) := by
      refine ⟨mul_mem hm hm, mem_centralizer_iff.2 fun x hx => ?_⟩
      have hx' : w * x * w⁻¹ ∈ M := by rw [hact x hx]; exact mul_mem (mul_mem hm hx) (inv_mem hm)
      have h3 : w * (w * x * w⁻¹) * w⁻¹ = x := by
        calc w * (w * x * w⁻¹) * w⁻¹ = (w * w) * x * (w⁻¹ * w⁻¹) := by group
          _ = x := by rw [hww, hwinv, hww]; group
      have h2 := hact _ hx'
      rw [h3] at h2
      rw [hact x hx] at h2
      calc x * (m * m) = (m * (m * x * m⁻¹) * m⁻¹) * (m * m) := by rw [← h2]
        _ = m * m * x := by group
    rw [hZ] at h1
    exact h1
  have hz : m⁻¹ * w ∈ centralizer (M : Set G) := by
    refine mem_centralizer_iff.2 fun x hx => ?_
    have h := hact x hx
    calc x * (m⁻¹ * w) = m⁻¹ * (m * x * m⁻¹) * w := by group
      _ = m⁻¹ * (w * x * w⁻¹) * w := by rw [h]
      _ = m⁻¹ * w * x := by group
  have hzz : (m⁻¹ * w) * (m⁻¹ * w) = 1 := by
    have hminv : m⁻¹ = m := inv_eq_of_mul_eq_one_right hm2
    rw [hminv]
    calc m * w * (m * w) = m * (w * m) * w := by group
      _ = m * (m * w) * w := by rw [hmw]
      _ = (m * m) * (w * w) := by group
      _ = 1 := by rw [hm2, hww, one_mul]
  have h1 := eq_one_of_mul_self_of_mem_of_odd_card hodd hz hzz
  calc w = m * (m⁻¹ * w) := by group
    _ = m := by rw [h1, mul_one]

@[expose] def InvolutionO2 (X : Type*) [Group X] : Prop :=
  ∀ s : X, s * s = 1 → s ∈ closure {x : X | x ∈ centralizer ({s} : Set X) ∧ Odd (orderOf x)}

theorem InvolutionO2.of_mulEquiv {X Y : Type*} [Group X] [Group Y] (φ : X ≃* Y)
    (h : InvolutionO2 X) : InvolutionO2 Y := by
  intro s hs
  have hs' : φ.symm s * φ.symm s = 1 := by rw [← map_mul, hs, map_one]
  have h1 := h _ hs'
  have hle : closure {x : X | x ∈ centralizer ({φ.symm s} : Set X) ∧ Odd (orderOf x)} ≤
      (closure {y : Y | y ∈ centralizer ({s} : Set Y) ∧ Odd (orderOf y)}).comap
        φ.toMonoidHom := by
    rw [closure_le]
    rintro x ⟨hxc, hxo⟩
    rw [SetLike.mem_coe, mem_comap]
    apply Subgroup.subset_closure
    refine ⟨?_, ?_⟩
    · rw [mem_centralizer_singleton_iff] at hxc ⊢
      have := congrArg φ hxc
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at this
      exact this
    · rw [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq]
      exact hxo
  have h2 := hle h1
  rw [mem_comap, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] at h2
  exact h2

theorem InvolutionO2.mem_closure {M : Subgroup G} (h : InvolutionO2 M) {s : G} (hs : s ∈ M)
    (hss : s * s = 1) :
    s ∈ closure {x : G | x ∈ M ⊓ centralizer ({s} : Set G) ∧ Odd (orderOf x)} := by
  have h1 := h ⟨s, hs⟩ (Subtype.ext hss)
  have hle : closure {x : M | x ∈ centralizer ({(⟨s, hs⟩ : M)} : Set M) ∧ Odd (orderOf x)} ≤
      (closure {x : G | x ∈ M ⊓ centralizer ({s} : Set G) ∧ Odd (orderOf x)}).comap
        M.subtype := by
    rw [closure_le]
    rintro x ⟨hxc, hxo⟩
    rw [SetLike.mem_coe, mem_comap]
    apply Subgroup.subset_closure
    refine ⟨⟨x.2, ?_⟩, ?_⟩
    · show (x : G) ∈ centralizer ({s} : Set G)
      rw [mem_centralizer_singleton_iff] at hxc ⊢
      exact congrArg Subtype.val hxc
    · rw [Subgroup.coe_subtype, Subgroup.orderOf_coe]
      exact hxo
  exact hle h1

theorem conj_not_mem_closure_odd_inf {L M : Subgroup G} {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hCN : centralizer ({t} : Set G) ≤ normalizer (L : Set G)) (hZ : center L = ⊥)
    (hOut : IsCyclic (Outer L)) (g : G) :
    g⁻¹ * t * g ∉
      closure {x : G | x ∈ M ⊓ centralizer ({g⁻¹ * t * g} : Set G) ∧ Odd (orderOf x)} := by
  intro h
  apply EPilot.not_mem_closure_odd_centralizer ht hKt hCN hZ hOut
  have hle : closure {x : G | x ∈ M ⊓ centralizer ({g⁻¹ * t * g} : Set G) ∧ Odd (orderOf x)} ≤
      (closure {x : G | x ∈ centralizer ({t} : Set G) ∧ Odd (orderOf x)}).comap
        (MulAut.conj g).toMonoidHom := by
    rw [closure_le]
    rintro x ⟨hxMw, hxo⟩
    have hxw := (mem_inf.1 hxMw).2
    rw [SetLike.mem_coe, mem_comap]
    apply Subgroup.subset_closure
    refine ⟨?_, ?_⟩
    · rw [mem_centralizer_singleton_iff] at hxw ⊢
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc g * x * g⁻¹ * t = g * (x * (g⁻¹ * t * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * t * g) * x) * g⁻¹ := by rw [hxw]
        _ = t * (g * x * g⁻¹) := by group
    · rw [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq]
      exact hxo
  have h' := hle h
  rw [mem_comap] at h'
  have e : (MulAut.conj g).toMonoidHom (g⁻¹ * t * g) = t := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  rwa [e] at h'

end Abstract

section Step1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem spGlobal_inf_centralizer_eq_bot_and_odd {n f : ℕ} (hn : 3 ≤ n)
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* StatedSp n K) {t : G}
    (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {κ : Sp2mKind}
    (hκ : κ = .omegaPlus ∨ κ = .omegaMinus) (hglob : SpOmegaRowGlobal e t f κ) :
    spGlobal e ⊓ centralizer (spGlobal e : Set G) = ⊥ ∧
      Odd (Nat.card (centralizer (spGlobal e : Set G))) := by
  have hK4 : 4 ≤ Nat.card K := (LinearPilot.four_le_card_iff_two_le hKc).2 hf
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have htN := mem_normalizer_spGlobal e htC
  have hLS : L ≤ spGlobal e := le_spGlobal hK4 (by omega) e
  obtain ⟨hty, hact⟩ := hglob
  obtain ⟨hout, -⟩ := hact htN
  obtain ⟨τ, hτ, hτm⟩ : ∃ τ : StatedLieTag, (τ = .POmegaPlus ∨ τ = .POmegaMinus) ∧
      LieModel (spGlobal e) τ (n + 1) 2 f := by
    rcases hκ with rfl | rfl
    · exact ⟨_, Or.inl rfl, hty⟩
    · exact ⟨_, Or.inr rfl, hty⟩
  have hS : IsSimpleGroup (spGlobal e) := LinearPilot.isSimpleGroup_of_lieModel_POmega hτ hτm
  have hLm : LieModel L .PSp n 2 f := lieModel_of_mulEquiv_statedSp e hKc (by omega) (by
    intro h
    obtain ⟨h1, -⟩ := Prod.mk.inj h
    omega)
  have hna : ∃ a b : spGlobal e, a * b ≠ b * a := by
    by_contra hc
    push Not at hc
    let _ : CommGroup (spGlobal e) := { (inferInstance : Group (spGlobal e)) with mul_comm := hc }
    have hp : (Nat.card (spGlobal e)).Prime := IsSimpleGroup.prime_card
    have h8 : 2 ^ 8 ∣ Nat.card (spGlobal e) :=
      (two_pow_eight_dvd_card_of_lieModel_PSp hLm).trans (Subgroup.card_dvd_of_le hLS)
    rcases (Nat.dvd_prime hp).1 h8 with h1 | h1
    · norm_num at h1
    · rw [← h1] at hp
      norm_num at hp
  have hZ : center (spGlobal e) = ⊥ := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hna).2
  refine ⟨?_, ?_⟩
  · rw [eq_bot_iff]
    rintro y ⟨hy, hyc⟩
    have hyZ : (⟨y, hy⟩ : spGlobal e) ∈ center (spGlobal e) := by
      rw [mem_center_iff]
      intro z
      exact Subtype.ext (mem_centralizer_iff.1 hyc z z.2)
    rw [hZ, mem_bot] at hyZ
    exact (mem_bot).2 (congrArg Subtype.val hyZ)
  · have htZ : t ∉ centralizer (spGlobal e : Set G) := by
      intro htZ
      apply hout
      refine ⟨1, MulEquiv.ext fun y => Subtype.ext ?_⟩
      rw [map_one, MulAut.one_apply, Subgroup.normalizerMonoidHom_apply_apply_coe,
        ← mem_centralizer_iff.1 htZ y y.2, mul_inv_cancel_right]
    exact EPilot.odd_card_centralizer_of_inf_eq_zpowers hKt hLS ht htN htZ

theorem not_mem_range_conj_of_conj_mem_normalizer (hset : SeitzSetting G L) {n f : ℕ}
    (hn : 3 ≤ n) (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* StatedSp n K) {t : G}
    (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {κ : Sp2mKind}
    (hκ : κ = .omegaPlus ∨ κ = .omegaMinus) (hglob : SpOmegaRowGlobal e t f κ)
    (hO2 : InvolutionO2 (spGlobal e)) (g : G)
    (hg : g⁻¹ * t * g ∈ normalizer (spGlobal e : Set G)) :
    (spGlobal e).normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩ ∉
      (MulAut.conj : spGlobal e →* MulAut (spGlobal e)).range := by
  rintro ⟨m, hm⟩
  obtain ⟨hZ, hodd⟩ := spGlobal_inf_centralizer_eq_bot_and_odd hn hKc hf e ht hKt hκ hglob
  have hact : ∀ x ∈ spGlobal e, (g⁻¹ * t * g) * x * (g⁻¹ * t * g)⁻¹ = (m : G) * x * (m : G)⁻¹ := by
    intro x hx
    have h1 := congrArg Subtype.val (DFunLike.congr_fun hm ⟨x, hx⟩)
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h1
    rw [← h1]
    rfl
  have htt : t * t = 1 := by rw [← _root_.sq, ← ht, pow_orderOf_eq_one]
  have hww : (g⁻¹ * t * g) * (g⁻¹ * t * g) = 1 := by
    calc (g⁻¹ * t * g) * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
      _ = 1 := by rw [htt]; group
  have hwm := eq_of_forall_conj_eq_conj_of_odd hZ hodd hww m.2 hact
  have hwG : g⁻¹ * t * g ∈ spGlobal e := hwm ▸ m.2
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hCN := CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard
    hset.standardSetting.standard htC ht
  exact conj_not_mem_closure_odd_inf ht hKt hCN hset.center_eq_bot
    (isCyclic_outer_of_mulEquiv_statedSp hn e) g (hO2.mem_closure hwG hww)

end Step1

end CFSG.SeitzReduction.SymplecticPilot
