module

public import CFSG.LocalAnalysis.EvenBN.Common.SwapUnique
public import CFSG.LocalAnalysis.SteinbergSFCentralInvolutionFusion

public section

namespace CFSG.LocalAnalysis.EvenBN.Sp4

namespace BothTrivialProductEnd

open Subgroup
open scoped commutatorElement
open CFSG.LocalAnalysis.SymplecticFourStandard GomiFusion
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

namespace Base

section Generic

variable {G : Type*} [Group G]

theorem commutator_le_of_relIndex_eq_two {H K : Subgroup G} (h2 : H.relIndex K = 2) :
    ⁅K, K⁆ ≤ H := by
  have hsq : ∀ a ∈ K, a * a ∈ H := fun a ha =>
    mem_subgroupOf.1 (Subgroup.mul_self_mem_of_index_two (H := H.subgroupOf K) h2 ⟨a, ha⟩)
  rw [commutator_le]
  intro a ha b hb
  have e : ⁅a, b⁆ = (a * a) * ((a⁻¹ * b) * (a⁻¹ * b)) * (b⁻¹ * b⁻¹) := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact mul_mem (mul_mem (hsq a ha) (hsq _ (mul_mem (inv_mem ha) hb))) (hsq _ (inv_mem hb))

theorem mul_comm_of_inf_centralizer_eq_bot [Finite G] {A : Subgroup G} {x : G}
    (hx : x ∈ normalizer (A : Set G)) (hx2 : x * x = 1)
    (hC : A ⊓ centralizer ({x} : Set G) = ⊥) : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hconj : ∀ b ∈ A, x * b * x⁻¹ ∈ A := fun b hb => (mem_normalizer_iff.1 hx b).1 hb
  let φ : A → A := fun b => ⟨(b : G)⁻¹ * (x * b * x⁻¹), mul_mem (inv_mem b.2) (hconj b b.2)⟩
  have hinj : Function.Injective φ := by
    intro b b' hbb
    have e : (b : G)⁻¹ * (x * b * x⁻¹) = (b' : G)⁻¹ * (x * b' * x⁻¹) := congrArg Subtype.val hbb
    have e1 : (b' : G) * (b : G)⁻¹ * x = x * ((b' : G) * (b : G)⁻¹) := by
      calc (b' : G) * (b : G)⁻¹ * x = b' * ((b : G)⁻¹ * (x * b * x⁻¹)) * x * (b : G)⁻¹ := by
            group
        _ = b' * ((b' : G)⁻¹ * (x * b' * x⁻¹)) * x * (b : G)⁻¹ := by rw [e]
        _ = x * ((b' : G) * (b : G)⁻¹) := by group
    have hc : (b' : G) * (b : G)⁻¹ ∈ A ⊓ centralizer ({x} : Set G) :=
      mem_inf.2 ⟨mul_mem b'.2 (inv_mem b.2), mem_centralizer_singleton_iff.2 e1⟩
    rw [hC, mem_bot, mul_inv_eq_one] at hc
    exact Subtype.ext hc.symm
  have hsurj := Finite.injective_iff_surjective.1 hinj
  have hinv : ∀ a ∈ A, x * a * x⁻¹ = a⁻¹ := by
    intro a ha
    obtain ⟨b, hb⟩ := hsurj ⟨a, ha⟩
    have e : a = (b : G)⁻¹ * (x * b * x⁻¹) := (congrArg Subtype.val hb).symm
    rw [e, hxinv]
    calc x * ((b : G)⁻¹ * (x * b * x)) * x = x * (b : G)⁻¹ * x * b * (x * x) := by group
      _ = x⁻¹ * (b : G)⁻¹ * x⁻¹ * b := by rw [hx2, mul_one, hxinv]
      _ = ((b : G)⁻¹ * (x * b * x))⁻¹ := by group
  intro a ha b hb
  have h1 := hinv (a * b) (mul_mem ha hb)
  rw [show x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) by group, hinv a ha, hinv b hb,
    mul_inv_rev] at h1
  calc a * b = (b⁻¹ * a⁻¹)⁻¹ := by group
    _ = (a⁻¹ * b⁻¹)⁻¹ := by rw [h1]
    _ = b * a := by group

theorem commutatorElement_mul_mul_eq_of_commute {a b c d : G}
    (hcb : c * b = b * c) (hcd : c * d = d * c) (hda : d * a = a * d) :
    ⁅a * c, b * d⁆ = ⁅a, b⁆ := by
  have hda' : d * a⁻¹ = a⁻¹ * d := (Commute.inv_right (hda : Commute d a)).eq
  calc ⁅a * c, b * d⁆ = a * (c * b) * d * c⁻¹ * a⁻¹ * d⁻¹ * b⁻¹ := by
        rw [commutatorElement_def]; group
    _ = a * b * (c * d) * c⁻¹ * a⁻¹ * d⁻¹ * b⁻¹ := by rw [hcb]; group
    _ = a * b * (d * a⁻¹) * d⁻¹ * b⁻¹ := by rw [hcd]; group
    _ = ⁅a, b⁆ := by rw [hda', commutatorElement_def]; group

theorem comm_of_mul_self_eq_one {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    (hxy : (x * y) * (x * y) = 1) : x * y = y * x := by
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have hxy' : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right hxy
  rw [mul_inv_rev, hx', hy'] at hxy'
  exact hxy'.symm

theorem zpow_eq_one_or_eq_self {t : G} (htt : t * t = 1) (k : ℤ) : t ^ k = 1 ∨ t ^ k = t := by
  have ht2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two, htt]
  rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · left
    rw [← two_mul, zpow_mul, ht2, one_zpow]
  · right
    rw [zpow_add, zpow_mul, ht2, one_zpow, one_mul, zpow_one]

theorem exists_mul_centralizer_of_perfect {X M : Subgroup G} [Group.IsSolvable (Outer X)]
    (hM : ⁅M, M⁆ = M) (hMX : M ≤ normalizer (X : Set G)) {x : G} (hx : x ∈ M) :
    ∃ a ∈ X, ∃ c ∈ centralizer (X : Set G), x = a * c := by
  haveI : Group.IsPerfect M := (Common.isPerfect_subgroup_iff_commutator_eq M).2 hM
  obtain ⟨a, ha⟩ := CFSG.ComponentClassification.OuterAutomorphisms.perfect_action_inner
    (X.normalizerMonoidHom.comp (inclusion hMX)) ⟨x, hx⟩
  refine ⟨a, a.2, (a : G)⁻¹ * x, mem_centralizer_iff.2 fun g hg => ?_, by group⟩
  have h1 : x * g * x⁻¹ = a * g * (a : G)⁻¹ :=
    congrArg (fun f : MulAut X => ((f ⟨g, hg⟩ : X) : G)) ha
  calc g * ((a : G)⁻¹ * x) = (a : G)⁻¹ * (a * g * (a : G)⁻¹) * x := by group
    _ = (a : G)⁻¹ * (x * g * x⁻¹) * x := by rw [h1]
    _ = (a : G)⁻¹ * x * g := by group

end Generic

section Outer

variable {K : Type} [Field K] [CharP K 2] [Finite K]

theorem isSolvable_outer {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = 2 ^ n) : Group.IsSolvable (Outer (antiSp K)) := by
  obtain ⟨-, hcyc, -, -⟩ := even_symplectic_four_outer_involution_rank_and_perfect_residual hn hK
  infer_instance

theorem card_le_of_sq_eq_one {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = 2 ^ n) (R : Subgroup (MulAut (antiSp K))) (hR : ∀ r ∈ R, r * r = 1) :
    Nat.card R ≤ 2 ^ (3 * n) := by
  obtain ⟨hinj, hcyc, -, hout⟩ :=
    even_symplectic_four_outer_involution_rank_and_perfect_residual hn hK
  letI : Fintype K := Fintype.ofFinite K
  set Inn : Subgroup (MulAut (antiSp K)) := inner (antiSp K) with hInn
  set A₀ : Subgroup (antiSp K) := R.comap (MulAut.conj : antiSp K →* MulAut (antiSp K)) with hA₀
  have hA₀sq : ∀ a ∈ A₀, a * a = 1 := by
    intro a ha
    apply hinj
    rw [map_mul, map_one]
    exact hR _ ha
  have hJ : A₀.map (MulAut.conj : antiSp K →* MulAut (antiSp K)) = R ⊓ Inn := by
    rw [hA₀, Subgroup.map_comap_eq, inf_comm]
    rfl
  have hJcard : Nat.card (R ⊓ Inn : Subgroup (MulAut (antiSp K))) =
      Nat.card A₀ := by
    rw [← hJ]
    exact Subgroup.card_map_of_injective hinj
  by_cases hin : R ≤ Inn
  · rw [inf_eq_left.2 hin] at hJcard
    rw [hJcard]
    exact (elementary_abelian_card_le hK A₀ hA₀sq).1
  · obtain ⟨θ, hθR, hθin⟩ := SetLike.not_le_iff_exists.mp hin
    have hθθ : θ * θ = 1 := hR θ hθR
    have hcomm : ∀ r ∈ R, ∀ s ∈ R, r * s = s * r := fun r hr s hs =>
      comm_of_mul_self_eq_one (hR r hr) (hR s hs) (hR _ (mul_mem hr hs))
    have hfix : A₀ ≤ fixedSubgroup θ := by
      intro a ha
      rw [mem_fixedSubgroup]
      apply hinj
      have h1 : θ * MulAut.conj a * θ⁻¹ = MulAut.conj (θ a) := by
        ext x
        simp [MulAut.mul_apply, MulAut.conj_apply]
      have h2 : θ * MulAut.conj a = MulAut.conj a * θ := hcomm θ hθR _ ha
      calc MulAut.conj (θ a) = θ * MulAut.conj a * θ⁻¹ := h1.symm
        _ = MulAut.conj a := by rw [h2]; group
    have hA₀card : Nat.card A₀ ≤ 2 ^ (2 * n) := by
      refine ((hout θ hθθ hθin).2.1 A₀ hfix hA₀sq).trans (Nat.pow_le_pow_right (by norm_num) ?_)
      split_ifs <;> omega
    have hRle : R ≤ (R ⊓ Inn) ⊔ zpowers θ := by
      intro r hr
      by_cases hri : r ∈ Inn
      · exact mem_sup_left ⟨hr, hri⟩
      · have hr1 : (QuotientGroup.mk r : Outer (antiSp K)) ≠ 1 := fun h =>
          hri ((QuotientGroup.eq_one_iff r).mp h)
        have hθ1 : (QuotientGroup.mk θ : Outer (antiSp K)) ≠ 1 := fun h =>
          hθin ((QuotientGroup.eq_one_iff θ).mp h)
        have hr2 : orderOf (QuotientGroup.mk r : Outer (antiSp K)) = 2 :=
          orderOf_eq_prime (by rw [sq, ← QuotientGroup.mk_mul, hR r hr, QuotientGroup.mk_one]) hr1
        have hθ2 : orderOf (QuotientGroup.mk θ : Outer (antiSp K)) = 2 :=
          orderOf_eq_prime (by rw [sq, ← QuotientGroup.mk_mul, hθθ, QuotientGroup.mk_one]) hθ1
        have heq := eq_of_orderOf_eq_two_of_isCyclic hr2 hθ2
        have hrθ : r * θ ∈ Inn := by
          rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, heq, ← QuotientGroup.mk_mul, hθθ,
            QuotientGroup.mk_one]
        have e : r = (r * θ) * θ⁻¹ := by group
        rw [e]
        exact mul_mem (mem_sup_left ⟨mul_mem hr hθR, hrθ⟩)
          (mem_sup_right (inv_mem (mem_zpowers θ)))
    have hMθ : (R ⊓ Inn) ≤ centralizer ({θ} : Set (MulAut (antiSp K))) := fun m hm =>
      mem_centralizer_singleton_iff.2 (hcomm θ hθR m hm.1).symm
    have hθM : θ ∉ R ⊓ Inn := fun h => hθin h.2
    have h2 := Common.SwapUnique.card_sup_zpowers_of_le_centralizer hθθ hMθ hθM
    calc Nat.card R ≤ Nat.card ((R ⊓ Inn) ⊔ zpowers θ : Subgroup _) :=
          Subgroup.card_le_of_le hRle
      _ = 2 * Nat.card A₀ := by rw [h2, hJcard]
      _ ≤ 2 * 2 ^ (2 * n) := Nat.mul_le_mul_left _ hA₀card
      _ = 2 ^ (2 * n + 1) := by ring
      _ ≤ 2 ^ (3 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)

end Outer

section Diagonal

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2] {t : G}

theorem center_eq_bot (φ : L ≃* antiSp K) : center L = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [mem_bot]
  apply φ.injective
  rw [map_one]
  refine eq_one_of_forall_commute fun y => ?_
  have h := congrArg φ (mem_center_iff.1 hx (φ.symm y))
  rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h
  exact h.symm

theorem nonempty_mulEquiv_quotient_center (φ : L ≃* antiSp K) (htt : t * t = 1)
    {G₀ : Subgroup G} (h₁₂ : G₀.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₀ : Set G))
    (hδ : ∀ x ∈ G₀, x * (t * x * t⁻¹) ∈ L)
    (hsurj : ∀ y ∈ L, ∃ x ∈ G₀, x * (t * x * t⁻¹) = y) :
    Nonempty (G₀ ⧸ center G₀ ≃* antiSp K) := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hcomm₀ : ⁅G₀, G₀.map (MulAut.conj t⁻¹).toMonoidHom⁆ = ⊥ := by
    rw [htinv, commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.2 h₁₂
  have hdiag : ∀ x : G, x * (t⁻¹ * x * t) = x * (t * x * t⁻¹) := fun x => by rw [htinv]
  set δ := Common.diagonalHom G₀ t hcomm₀ with hδdef
  have hrange : δ.range = L := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨x, rfl⟩
      rw [hδdef, Common.diagonalHom_apply, hdiag]
      exact hδ x x.2
    · intro y hy
      obtain ⟨x, hx, hxy⟩ := hsurj y hy
      refine ⟨⟨x, hx⟩, ?_⟩
      rw [hδdef, Common.diagonalHom_apply, hdiag]
      exact hxy
  have hker : center G₀ = δ.ker := by
    refine le_antisymm (fun z hz => ?_) (Common.ker_diagonalHom_le_center hcomm₀)
    rw [MonoidHom.mem_ker]
    have hzL : δ z ∈ L := by
      rw [← hrange]
      exact ⟨z, rfl⟩
    have hc : (⟨δ z, hzL⟩ : L) ∈ center L := by
      rw [mem_center_iff]
      intro l
      obtain ⟨a, ha⟩ : (l : G) ∈ δ.range := by
        rw [hrange]
        exact l.2
      apply Subtype.ext
      change (l : G) * δ z = δ z * l
      rw [← ha, ← map_mul, ← map_mul, mem_center_iff.1 hz a]
    rw [center_eq_bot φ, mem_bot] at hc
    exact congrArg Subtype.val hc
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivRange δ)).trans ((MulEquiv.subgroupCongr hrange).trans φ)⟩

end Diagonal

end Base

section Setting

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G}

theorem perfect_le_of_le_centralizer
    (hS : Setup L K n φ (zpowers t) t) {H : Subgroup G}
    (hH : H ≤ centralizer ({t} : Set G)) (hp : ⁅H, H⁆ = H) : H ≤ L := by
  have hcent : H ≤ normalizer (L : Set G) := hH.trans hS.cent_le
  haveI : Group.IsPerfect H := (Common.isPerfect_subgroup_iff_commutator_eq H).2 hp
  haveI := Base.isSolvable_outer (K := K) hS.two_le hS.card_K
  have hLT : ∀ x ∈ H, x ∈ L ⊔ zpowers t := by
    intro x hx
    obtain ⟨s, hs⟩ := CFSG.ComponentClassification.OuterAutomorphisms.perfect_action_inner
      (subAct φ hcent) ⟨x, hx⟩
    have hs' : subAct φ hcent ⟨x, hx⟩ = MulAut.conj (φ (φ.symm s)) := by
      rw [MulEquiv.apply_symm_apply]
      exact hs
    have h0 := subAct_inv_mul φ hcent hs'
    have h1 : ((φ.symm s : L) : G)⁻¹ * x ∈ zpowers t :=
      hS.mem_T h0 (mul_mem (inv_mem (hS.L_le (φ.symm s).2)) (hH hx))
    have e : x = ((φ.symm s : L) : G) * (((φ.symm s : L) : G)⁻¹ * x) := by group
    rw [e]
    exact mul_mem (mem_sup_left (φ.symm s).2) (mem_sup_right h1)
  calc H = ⁅H, H⁆ := hp.symm
    _ ≤ L := by
      rw [commutator_le]
      intro a ha b hb
      exact hS.commutator_mem_L (hLT a ha) (hLT b hb)

theorem card_le_of_le_centralizer
    (hS : Setup L K n φ (zpowers t) t) {E : Subgroup G}
    (hE : E ≤ centralizer ({t} : Set G)) (hsq : ∀ x ∈ E, x * x = 1) :
    Nat.card E ≤ 2 * (2 ^ n) ^ 3 := by
  have hcent : E ≤ normalizer (L : Set G) := hE.trans hS.cent_le
  set ρ := subAct φ hcent with hρ
  have hker : Nat.card ρ.ker ≤ 2 := by
    have hle : ρ.ker.map E.subtype ≤ zpowers t := by
      rintro _ ⟨x, hx, rfl⟩
      exact hS.mem_T ((subAct_eq_one_iff φ hcent x).mp hx) (hE x.2)
    calc Nat.card ρ.ker = Nat.card (ρ.ker.map E.subtype) :=
          (Subgroup.card_map_of_injective E.subtype_injective).symm
      _ ≤ Nat.card (zpowers t) := Subgroup.card_le_of_le hle
      _ = 2 := by rw [Nat.card_zpowers, hS.order_t]
  have hR : ∀ r ∈ ρ.range, r * r = 1 := by
    rintro _ ⟨x, rfl⟩
    rw [← map_mul, show x * x = 1 from Subtype.ext (hsq x x.2), map_one]
  have hRcard := Base.card_le_of_sq_eq_one (K := K) hS.two_le hS.card_K ρ.range hR
  have hcard : Nat.card E = Nat.card ρ.range * Nat.card ρ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv]
  rw [hcard]
  calc Nat.card ρ.range * Nat.card ρ.ker ≤ 2 ^ (3 * n) * 2 := Nat.mul_le_mul hRcard hker
    _ = 2 * (2 ^ n) ^ 3 := by ring

theorem perfect_le_sup_of_le_normalizer
    (hS : Setup L K n φ (zpowers t) t) {G₀ : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple G₀) (hZ : Odd (Nat.card (center G₀)))
    (h₁₂ : G₀.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₀ : Set G))
    (hδ : ∀ x ∈ G₀, x * (t * x * t⁻¹) ∈ L)
    (hsurj : ∀ y ∈ L, ∃ x ∈ G₀, x * (t * x * t⁻¹) = y) {H : Subgroup G}
    (hH : H ≤ normalizer ((G₀ ⊔ G₀.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G))
    (hp : ⁅H, H⁆ = H) : H ≤ G₀ ⊔ G₀.map (MulAut.conj t).toMonoidHom := by
  have htt := hS.t_mul_t
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  set G₂ : Subgroup G := G₀.map (MulAut.conj t).toMonoidHom with hG₂
  obtain ⟨hperf, hbot, hn₁⟩ :=
    SeitzReduction.F4Pilot.perfect_ne_bot_dichotomy_of_isQuasisimple hq
  have hn₂ := SeitzReduction.F4Pilot.dichotomy_map_mulAut (MulAut.conj t) hn₁
  have hcomm : ∀ a ∈ G₀, ∀ b ∈ G₂, a * b = b * a := fun a ha b hb =>
    mem_centralizer_iff.1 (h₁₂ hb) a ha
  have hne : G₀ ≠ G₂ := by
    intro e
    apply hbot
    have h11 : G₀ ≤ centralizer (G₀ : Set G) := by
      calc G₀ = G₂ := e
        _ ≤ centralizer (G₀ : Set G) := h₁₂
    rw [← hperf, commutator_eq_bot_iff_le_centralizer.2 h11]
  have hperm : ∀ x ∈ normalizer ((G₀ ⊔ G₂ : Subgroup G) : Set G),
      G₀.map (MulAut.conj x).toMonoidHom = G₀ ∨ G₀.map (MulAut.conj x).toMonoidHom = G₂ :=
    fun x hx => SeitzReduction.F4Pilot.map_conj_eq_or_eq_of_perfect h₁₂ hperf hbot hn₁ hn₂ hx
  have hHN : H ≤ normalizer (G₀ : Set G) ⊓ normalizer (G₂ : Set G) := by
    have h2 := SeitzReduction.F4Pilot.relIndex_inf_normalizer_eq_two_of_swap htt rfl hne hperm
    rw [← SeitzReduction.F4Pilot.inf_normalizer_eq_of_swap htt rfl hne hperm]
    calc H = ⁅H, H⁆ := hp.symm
      _ ≤ _ := (commutator_mono hH hH).trans (Base.commutator_le_of_relIndex_eq_two h2)
  obtain ⟨ψ⟩ := Base.nonempty_mulEquiv_quotient_center φ htt h₁₂ hδ hsurj
  haveI : Group.IsPerfect G₀ := ⟨hq.1⟩
  haveI hsolvQ : Group.IsSolvable (Outer (G₀ ⧸ center G₀)) := by
    haveI := Base.isSolvable_outer (K := K) hS.two_le hS.card_K
    exact CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_equiv ψ.symm
  haveI hsolv₀ : Group.IsSolvable (Outer G₀) :=
    CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_centerQuotient G₀
  let e₂ : G₀ ≃* G₂ := Subgroup.equivMapOfInjective G₀ _ (MulAut.conj t).injective
  haveI hsolv₂ : Group.IsSolvable (Outer G₂) :=
    CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_equiv e₂
  have hLD : L ≤ G₀ ⊔ G₂ := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hsurj y hy
    exact mul_mem (mem_sup_left hx) (mem_sup_right ⟨x, hx, rfl⟩)
  set C₀ : Subgroup G := centralizer (G₀ : Set G) ⊓ centralizer (G₂ : Set G) with hC₀
  have hmemG₂ : ∀ a ∈ G₀, t * a * t⁻¹ ∈ G₂ := fun a ha => ⟨a, ha, rfl⟩
  have hmemG₀ : ∀ b ∈ G₂, t⁻¹ * b * t ∈ G₀ := by
    rintro _ ⟨a, ha, rfl⟩
    change t⁻¹ * (t * a * t⁻¹) * t ∈ G₀
    rw [show t⁻¹ * (t * a * t⁻¹) * t = a by group]
    exact ha
  have htC₀ : t ∈ normalizer (C₀ : Set G) := by
    refine mem_normalizer_fintype fun c hc => ?_
    have hc₁ := (mem_inf.1 hc).1
    have hc₂ := (mem_inf.1 hc).2
    refine mem_inf.2 ⟨mem_centralizer_iff.2 fun a ha => ?_, mem_centralizer_iff.2 fun b hb => ?_⟩
    · have hat : t⁻¹ * a * t ∈ G₂ := by
        rw [show t⁻¹ * a * t = t * a * t⁻¹ by rw [htinv]]
        exact hmemG₂ a ha
      have := mem_centralizer_iff.1 hc₂ _ hat
      calc a * (t * c * t⁻¹) = t * ((t⁻¹ * a * t) * c) * t⁻¹ := by group
        _ = t * (c * (t⁻¹ * a * t)) * t⁻¹ := by rw [this]
        _ = t * c * t⁻¹ * a := by group
    · have hbt := hmemG₀ b hb
      have := mem_centralizer_iff.1 hc₁ _ hbt
      calc b * (t * c * t⁻¹) = t * ((t⁻¹ * b * t) * c) * t⁻¹ := by group
        _ = t * (c * (t⁻¹ * b * t)) * t⁻¹ := by rw [this]
        _ = t * c * t⁻¹ * b := by group
  have htG₀ : t ∉ centralizer (G₀ : Set G) := by
    intro ht
    apply hne
    refine le_antisymm (fun a ha => ?_) ?_
    · have e : t * a * t⁻¹ = a := by
        rw [← mem_centralizer_iff.1 ht a ha, mul_inv_cancel_right]
      exact e ▸ hmemG₂ a ha
    · rintro _ ⟨a, ha, rfl⟩
      change t * a * t⁻¹ ∈ G₀
      rw [← mem_centralizer_iff.1 ht a ha, mul_inv_cancel_right]
      exact ha
  have hC₀t : C₀ ⊓ centralizer ({t} : Set G) = ⊥ := by
    refine eq_bot_iff.2 fun c hc => ?_
    obtain ⟨hcC₀, hct⟩ := mem_inf.1 hc
    have hcL : c ∈ centralizer (L : Set G) := by
      refine mem_centralizer_iff.2 fun l hl => ?_
      have hle : G₀ ⊔ G₂ ≤ centralizer ({c} : Set G) := sup_le
        (fun a ha => mem_centralizer_singleton_iff.2
          (mem_centralizer_iff.1 (mem_inf.1 hcC₀).1 a ha))
        (fun b hb => mem_centralizer_singleton_iff.2
          (mem_centralizer_iff.1 (mem_inf.1 hcC₀).2 b hb))
      exact mem_centralizer_singleton_iff.1 (hle (hLD hl))
    have hk : c ∈ zpowers t := hS.mem_T hcL hct
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hk
    rcases Base.zpow_eq_one_or_eq_self htt k with h1 | h1
    · rw [h1]
      exact one_mem _
    · rw [h1] at hcC₀
      exact absurd (mem_inf.1 hcC₀).1 htG₀
  have hab := Base.mul_comm_of_inf_centralizer_eq_bot htC₀ htt hC₀t
  have hdec : ∀ x ∈ H, ∃ g ∈ G₀ ⊔ G₂, ∃ c ∈ C₀, x = g * c := by
    intro x hx
    obtain ⟨a₁, ha₁, c₁, hc₁, e₁⟩ :=
      Base.exists_mul_centralizer_of_perfect (X := G₀) hp (hHN.trans inf_le_left) hx
    obtain ⟨a₂, ha₂, c₂, hc₂, e₂⟩ :=
      Base.exists_mul_centralizer_of_perfect (X := G₂) hp (hHN.trans inf_le_right) hx
    have h12 : a₁ * a₂ = a₂ * a₁ := hcomm a₁ ha₁ a₂ ha₂
    refine ⟨a₁ * a₂, mul_mem (mem_sup_left ha₁) (mem_sup_right ha₂), (a₁ * a₂)⁻¹ * x,
      mem_inf.2 ⟨?_, ?_⟩, by group⟩
    · have e : (a₁ * a₂)⁻¹ * x = a₂⁻¹ * c₁ := by rw [e₁]; group
      rw [e]
      exact mul_mem (inv_mem (mem_centralizer_iff.2 fun g hg => hcomm g hg a₂ ha₂)) hc₁
    · have e : (a₁ * a₂)⁻¹ * x = a₁⁻¹ * c₂ := by rw [h12, e₂]; group
      rw [e]
      exact mul_mem (inv_mem (mem_centralizer_iff.2 fun g hg => (hcomm a₁ ha₁ g hg).symm)) hc₂
  have hcen : ∀ c ∈ C₀, ∀ g ∈ G₀ ⊔ G₂, c * g = g * c := by
    intro c hc g hg
    have hle : G₀ ⊔ G₂ ≤ centralizer ({c} : Set G) := sup_le
      (fun a ha => mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 (mem_inf.1 hc).1 a ha))
      (fun b hb => mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 (mem_inf.1 hc).2 b hb))
    exact (mem_centralizer_singleton_iff.1 (hle hg)).symm
  calc H = ⁅H, H⁆ := hp.symm
    _ ≤ G₀ ⊔ G₂ := by
      rw [commutator_le]
      intro x hx y hy
      obtain ⟨g, hg, c, hc, rfl⟩ := hdec x hx
      obtain ⟨g', hg', c', hc', rfl⟩ := hdec y hy
      rw [Base.commutatorElement_mul_mul_eq_of_commute (hcen c hc g' hg') (hab c hc c' hc')
        (hcen c' hc' g hg), commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hg hg') (inv_mem hg)) (inv_mem hg')

end Setting

end BothTrivialProductEnd

end CFSG.LocalAnalysis.EvenBN.Sp4
