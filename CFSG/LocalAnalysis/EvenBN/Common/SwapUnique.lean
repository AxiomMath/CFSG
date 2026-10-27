module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotEndSwapQuasi
public import CFSG.LocalAnalysis.SteinbergBNTwoFactorDiagonalGeneration
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.EvenBN.Common.Diagonal

public section

namespace CFSG.LocalAnalysis.EvenBN.Common

open Subgroup
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_of_card exists_isSylowOf)
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

namespace SwapUnique

theorem center_eq_bot_of_isSimpleGroup {L : Subgroup G} (hL : IsSimpleGroup L)
    (hLab : ¬ ∀ x ∈ L, ∀ y ∈ L, x * y = y * x) : center L = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center L) with h | h
  · exact h
  · exfalso
    refine hLab fun x hx y hy => ?_
    have hxc : (⟨x, hx⟩ : L) ∈ center L := h ▸ mem_top _
    exact congrArg Subtype.val ((mem_center_iff.1 hxc) ⟨y, hy⟩).symm

theorem card_sup_zpowers_of_le_centralizer {t : G} (htt : t * t = 1) {M : Subgroup G}
    (hM : M ≤ centralizer ({t} : Set G)) (htM : t ∉ M) :
    Nat.card (M ⊔ zpowers t : Subgroup G) = 2 * Nat.card M := by
  have htN : t ∈ normalizer (M : Set G) := by
    refine centralizer_le_normalizer _ (mem_centralizer_iff.2 fun m hm => ?_)
    exact mem_centralizer_singleton_iff.1 (hM hm)
  have hrel := CFSG.SeitzReduction.relIndex_inf_eq_two htt htN htM (le_refl (M ⊔ zpowers t))
    (mem_sup_right (mem_zpowers t))
  rw [inf_eq_right.2 le_sup_left] at hrel
  have h := Subgroup.relIndex_mul_card M (M ⊔ zpowers t)
  rw [inf_eq_left.2 le_sup_left, hrel] at h
  exact h.symm

theorem exists_conj_le_of_isSylowOf {K P Q : Subgroup G} (hP : IsSylowOf 2 P K) (hQK : Q ≤ K)
    (hQ : IsPGroup 2 Q) : ∃ c ∈ K, ∀ q ∈ Q, c * q * c⁻¹ ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₀, hP₀⟩ := hP.exists_sylow_eq_subgroupOf
  have hQ' : IsPGroup 2 (Q.subgroupOf K) := hQ.comap_subtype
  obtain ⟨R, hR⟩ := hQ'.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq K R P₀
  refine ⟨c, c.2, fun q hq => ?_⟩
  have h1 : MulAut.conj c • (⟨q, hQK hq⟩ : K) ∈ MulAut.conj c • (R : Subgroup K) :=
    smul_mem_pointwise_smul _ (MulAut.conj c) (R : Subgroup K) (hR (mem_subgroupOf.mpr hq))
  rw [← Sylow.coe_subgroup_smul, hc, hP₀, mem_subgroupOf] at h1
  exact h1

theorem exists_mem_conj_iff_of_isSylowOf {K P P' : Subgroup G} (hP : IsSylowOf 2 P K)
    (hP' : IsSylowOf 2 P' K) : ∃ c ∈ K, ∀ x : G, x ∈ P' ↔ c * x * c⁻¹ ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hcK, hc⟩ := exists_conj_le_of_isSylowOf hP hP'.le hP'.isPGroup
  have hle : P'.map (MulAut.conj c).toMonoidHom ≤ P := by
    rintro _ ⟨q, hq, rfl⟩
    exact hc q hq
  have heq : P'.map (MulAut.conj c).toMonoidHom = P :=
    eq_of_le_of_card_ge hle (by
      rw [card_map_of_injective (MulAut.conj c).injective, hP.card_eq, hP'.card_eq])
  refine ⟨c, hcK, fun x => ⟨fun hx => hc x hx, fun hx => ?_⟩⟩
  rw [← heq] at hx
  obtain ⟨q, hq, hqx⟩ := hx
  have : q = x := by
    have h := congrArg (fun y => c⁻¹ * y * c) hqx
    simpa [mul_assoc] using h
  rwa [← this]

theorem range_diagonalHom_eq_of_card {t : G} (htt : t * t = 1) {L A : Subgroup G}
    (hCperf : ∀ H : Subgroup G, H ≤ centralizer ({t} : Set G) → ⁅H, H⁆ = H → H ≤ L)
    (hA : ⁅A, A⁆ = A) (hcomm : ⁅A, A.map (MulAut.conj t⁻¹).toMonoidHom⁆ = ⊥)
    (hcard : Nat.card A = Nat.card L * Nat.card (center A)) :
    (diagonalHom A t hcomm).range = L := by
  set δ := diagonalHom A t hcomm
  have hAp : Group.IsPerfect A := (isPerfect_subgroup_iff_commutator_eq A).2 hA
  have hle : δ.range ≤ L := by
    refine hCperf _ (range_diagonalHom_le hcomm htt) ?_
    rw [MonoidHom.range_eq_map, ← map_commutator, ← _root_.commutator_def,
      Group.IsPerfect.commutator_eq_top]
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have h2 : Nat.card A = Nat.card δ.range * Nat.card δ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup δ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange δ).toEquiv]
  have h5 : Nat.card δ.ker ≤ Nat.card (center A) :=
    Subgroup.card_le_of_le (ker_diagonalHom_le_center hcomm)
  have hpos : 0 < Nat.card (center A) := Nat.card_pos
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc Nat.card L * Nat.card (center A) = Nat.card δ.range * Nat.card δ.ker := by rw [← hcard, h2]
    _ ≤ Nat.card δ.range * Nat.card (center A) := Nat.mul_le_mul_left _ h5

theorem card_eq_mul_card_center_of_diagonal {t : G} {L G₀ : Subgroup G} (hZL : center L = ⊥)
    (hcomm : ⁅G₀, G₀.map (MulAut.conj t⁻¹).toMonoidHom⁆ = ⊥)
    (hrange : (diagonalHom G₀ t hcomm).range = L) :
    Nat.card G₀ = Nat.card L * Nat.card (center G₀) := by
  set δ := diagonalHom G₀ t hcomm
  have hker : δ.ker = center G₀ := by
    refine le_antisymm (ker_diagonalHom_le_center hcomm) (fun z hz => ?_)
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
    rw [hZL, mem_bot] at hc
    exact congrArg Subtype.val hc
  have h2 : Nat.card G₀ = Nat.card δ.range * Nat.card δ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup δ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange δ).toEquiv]
  rw [h2, hker, hrange]

theorem isSylowOf_map_diagonalHom {t : G} {L A : Subgroup G}
    (hcomm : ⁅A, A.map (MulAut.conj t⁻¹).toMonoidHom⁆ = ⊥)
    (hrange : (diagonalHom A t hcomm).range = L) (hZ : Odd (Nat.card (center A)))
    (hcard : Nat.card A = Nat.card L * Nat.card (center A)) (U₀ : Sylow 2 A) :
    IsSylowOf 2 ((U₀ : Subgroup A).map (diagonalHom A t hcomm)) L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set δ := diagonalHom A t hcomm
  have hfac : (Nat.card A).factorization 2 = (Nat.card L).factorization 2 := by
    rw [hcard, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd
        (fun h2 => (Nat.not_even_iff_odd.2 hZ) (even_iff_two_dvd.2 h2)), add_zero]
  have hinj : Function.Injective (δ.comp (U₀ : Subgroup A).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro u hu
    have hu1 : (u : A) ∈ δ.ker := hu
    have hZu : (u : A) ∈ center A := ker_diagonalHom_le_center hcomm hu1
    obtain ⟨k, hk⟩ := U₀.isPGroup' u
    have h1 : orderOf (u : A) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (by
      simpa using congrArg Subtype.val hk)
    have h2 : orderOf (u : A) ∣ Nat.card (center A) := Subgroup.orderOf_dvd_natCard _ hZu
    have hcop : Nat.Coprime (2 ^ k) (Nat.card (center A)) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hZ)
    have := orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd (hcop.coprime_dvd_left h1) h2)
    exact mem_bot.2 (Subtype.ext this)
  set V : Subgroup G := (U₀ : Subgroup A).map δ
  have hVrange : V = (δ.comp (U₀ : Subgroup A).subtype).range := by
    rw [MonoidHom.range_comp, range_subtype]
  have hVcard : Nat.card V = 2 ^ (Nat.card L).factorization 2 := by
    rw [hVrange, ← SetLike.coe_sort_coe, MonoidHom.coe_range, Nat.card_range_of_injective hinj,
      Sylow.card_eq_multiplicity, hfac]
  have hVL : V ≤ L := hrange ▸ map_le_range δ _
  exact isSylowOf_of_card hVL hVcard

theorem sup_le_of_swap_diagonal {t : G} (ht : orderOf t = 2) {L R N₀ : Subgroup G}
    (hL : IsSimpleGroup L) (hZL : center L = ⊥) (hLeven : Even (Nat.card L))
    (hLt : L ≤ centralizer ({t} : Set G))
    (hCperf : ∀ H : Subgroup G, H ≤ centralizer ({t} : Set G) → ⁅H, H⁆ = H → H ≤ L)
    (hR : IsSylowOf 2 R (L ⊔ zpowers t)) (hLN : L ≤ N₀) (htN : t ∈ N₀)
    (hRN : normalizer (R : Set G) ≤ N₀) {A : Subgroup G} (hA : ⁅A, A⁆ = A)
    (hZ : Odd (Nat.card (center A)))
    (hcomm : ⁅A, A.map (MulAut.conj t⁻¹).toMonoidHom⁆ = ⊥)
    (hcard : Nat.card A = Nat.card L * Nat.card (center A)) :
    A ⊔ A.map (MulAut.conj t⁻¹).toMonoidHom ≤ N₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hAp : Group.IsPerfect A := (isPerfect_subgroup_iff_commutator_eq A).2 hA
  set δ := diagonalHom A t hcomm
  have hrange : δ.range = L := range_diagonalHom_eq_of_card htt hCperf hA hcomm hcard
  have hker : δ.ker = center A := by
    refine Subgroup.eq_of_le_of_card_ge (ker_diagonalHom_le_center hcomm) ?_
    have h2 : Nat.card A = Nat.card δ.range * Nat.card δ.ker := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup δ.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange δ).toEquiv]
    rw [hrange] at h2
    exact (Nat.eq_of_mul_eq_mul_left Nat.card_pos (hcard.symm.trans h2)).le
  have hsimple : IsSimpleGroup (A ⧸ center A) := by
    let e : A ⧸ center A ≃* L :=
      ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
        (QuotientGroup.quotientKerEquivRange δ)).trans (MulEquiv.subgroupCongr hrange)
    exact e.isSimpleGroup
  have heven : Even (Nat.card (A ⧸ center A)) := by
    have h1 : Nat.card A = Nat.card (A ⧸ center A) * Nat.card (center A) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup (center A)
    have h2 : Nat.card (A ⧸ center A) = Nat.card L :=
      Nat.eq_of_mul_eq_mul_right Nat.card_pos (h1.symm.trans hcard)
    rw [h2]
    exact hLeven
  obtain ⟨U, hUsyl⟩ := exists_isSylowOf 2 A
  obtain ⟨U₀, hU₀⟩ := hUsyl.exists_sylow_eq_subgroupOf
  have hVsyl : IsSylowOf 2 ((U.subgroupOf A).map δ) L := by
    rw [← hU₀]
    exact isSylowOf_map_diagonalHom hcomm hrange hZ hcard U₀
  set V : Subgroup G := (U.subgroupOf A).map δ
  have hVL : V ≤ L := hVsyl.le
  have ht1 : t ≠ 1 := fun h => by
    rw [h, orderOf_one] at ht
    exact absurd ht (by norm_num)
  have htL : t ∉ L := by
    intro htL
    have htc : (⟨t, htL⟩ : L) ∈ center L := by
      rw [mem_center_iff]
      intro l
      exact Subtype.ext (mem_centralizer_singleton_iff.1 (hLt l.2))
    rw [hZL, mem_bot] at htc
    exact ht1 (congrArg Subtype.val htc)
  have hVt : V ≤ centralizer ({t} : Set G) := hVL.trans hLt
  have htV : t ∉ V := fun h => htL (hVL h)
  have hKcard : Nat.card (L ⊔ zpowers t : Subgroup G) = 2 * Nat.card L :=
    card_sup_zpowers_of_le_centralizer htt hLt htL
  have hQcard : Nat.card (V ⊔ zpowers t : Subgroup G) = 2 * Nat.card V :=
    card_sup_zpowers_of_le_centralizer htt hVt htV
  have hQsyl : IsSylowOf 2 (V ⊔ zpowers t) (L ⊔ zpowers t) := by
    refine isSylowOf_of_card (sup_le_sup_right hVL _) ?_
    rw [hQcard, hKcard, hVsyl.card_eq, Nat.factorization_mul two_ne_zero Nat.card_pos.ne',
      Finsupp.add_apply, Nat.Prime.factorization_self Nat.prime_two, pow_add, pow_one]
  obtain ⟨c, hcK, hc⟩ := exists_mem_conj_iff_of_isSylowOf hR hQsyl
  have hKN : L ⊔ zpowers t ≤ N₀ := sup_le hLN (zpowers_le.2 htN)
  have hNQ : normalizer ((V ⊔ zpowers t : Subgroup G) : Set G) ≤ N₀ := by
    intro y hy
    have hy' : c * y * c⁻¹ ∈ normalizer (R : Set G) := by
      rw [mem_normalizer_iff] at hy ⊢
      intro h
      have h1 : h ∈ R ↔ c⁻¹ * h * c ∈ V ⊔ zpowers t := by
        rw [hc, show c * (c⁻¹ * h * c) * c⁻¹ = h by group]
      have e : c * y * c⁻¹ * h * (c * y * c⁻¹)⁻¹ = c * (y * (c⁻¹ * h * c) * y⁻¹) * c⁻¹ := by
        group
      calc h ∈ R ↔ c⁻¹ * h * c ∈ V ⊔ zpowers t := h1
        _ ↔ y * (c⁻¹ * h * c) * y⁻¹ ∈ V ⊔ zpowers t := hy _
        _ ↔ c * (y * (c⁻¹ * h * c) * y⁻¹) * c⁻¹ ∈ R := hc _
        _ ↔ c * y * c⁻¹ * h * (c * y * c⁻¹)⁻¹ ∈ R := by rw [e]
    have hcN : c ∈ N₀ := hKN hcK
    have e : y = c⁻¹ * (c * y * c⁻¹) * c := by group
    rw [e]
    exact mul_mem (mul_mem (inv_mem hcN) (hRN hy')) hcN
  have key := odd_center_two_factor_diagonal_normalizer_generation ht hZ hsimple heven hcomm
    hUsyl.le hUsyl.exists_sylow_eq_subgroupOf
  simp only at key
  obtain ⟨-, -, -, -, hgen⟩ := key
  have himage : ∀ M : Subgroup G, M ≤ A → ((fun a => a * (t⁻¹ * a * t)) '' (M : Set G)) =
      ((M.subgroupOf A).map δ : Set G) := by
    intro M hM
    ext x
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact ⟨⟨m, hM hm⟩, mem_subgroupOf.2 hm, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨m, mem_subgroupOf.1 hm, rfl⟩
  have hδA : ((fun a => a * (t⁻¹ * a * t)) '' (A : Set G)) = (L : Set G) := by
    rw [himage A le_rfl, ← hrange, MonoidHom.range_eq_map]
    congr 2
    exact subgroupOf_self A
  have hδU : closure ((fun a => a * (t⁻¹ * a * t)) '' (U : Set G)) = V := by
    rw [himage U hUsyl.le, closure_eq]
  rw [hδA, hδU] at hgen
  rw [← hgen, closure_le]
  rintro x (hx | hx)
  · exact hLN hx
  · exact hNQ (mem_inf.1 hx).2

end SwapUnique

theorem mem_normalizer_of_conj_mem_normalizer_of_swap {t : G} (ht : orderOf t = 2)
    {L G₀ R : Subgroup G} (hL : IsSimpleGroup L) (hLab : ¬ ∀ x ∈ L, ∀ y ∈ L, x * y = y * x)
    (hLeven : Even (Nat.card L))
    (hLt : L ≤ centralizer ({t} : Set G))
    (hCperf : ∀ H : Subgroup G, H ≤ centralizer ({t} : Set G) → ⁅H, H⁆ = H → H ≤ L)
    (hq : CFSG.Open.IsQuasisimple G₀) (hZ : Odd (Nat.card (center G₀)))
    (h₁₂ : G₀.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₀ : Set G))
    (hδ : ∀ x ∈ G₀, x * (t * x * t⁻¹) ∈ L)
    (hsurj : ∀ y ∈ L, ∃ x ∈ G₀, x * (t * x * t⁻¹) = y)
    (hR : CFSG.ABGLocalTools.IsSylowOf 2 R (L ⊔ zpowers t))
    (hNR : normalizer (R : Set G) ≤
      normalizer ((G₀ ⊔ G₀.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G))
    (hperfN : ∀ H : Subgroup G,
      H ≤ normalizer ((G₀ ⊔ G₀.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) →
      ⁅H, H⁆ = H → H ≤ G₀ ⊔ G₀.map (MulAut.conj t).toMonoidHom)
    (hnorm : ∀ h : G, t ∈ normalizer ((G₀.map (MulAut.conj h).toMonoidHom : Subgroup G) : Set G) →
      t ∈ normalizer (((G₀.map (MulAut.conj t).toMonoidHom).map (MulAut.conj h).toMonoidHom :
        Subgroup G) : Set G) → False)
    (g : G)
    (hg : g⁻¹ * t * g ∈
      normalizer ((G₀ ⊔ G₀.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G)) :
    g ∈ normalizer ((G₀ ⊔ G₀.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) := by
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hZL : center L = ⊥ := SwapUnique.center_eq_bot_of_isSimpleGroup hL hLab
  set Gt : Subgroup G := G₀.map (MulAut.conj t).toMonoidHom with hGt
  set D : Subgroup G := G₀ ⊔ Gt with hD
  obtain ⟨hperf, hbot, hn₁⟩ :=
    SeitzReduction.F4Pilot.perfect_ne_bot_dichotomy_of_isQuasisimple hq
  have hn₂ := SeitzReduction.F4Pilot.dichotomy_map_mulAut (MulAut.conj t) hn₁
  have hperf₂ : ⁅Gt, Gt⁆ = Gt := by rw [hGt, ← map_commutator, hperf]
  have hGtbot : Gt ≠ ⊥ := fun h =>
    hbot ((map_eq_bot_iff_of_injective G₀ (MulAut.conj t).injective).1 h)
  have hDperf : ⁅D, D⁆ = D := le_antisymm (commutator_le_self _)
    (sup_le (hperf.ge.trans (commutator_mono le_sup_left le_sup_left))
      (hperf₂.ge.trans (commutator_mono le_sup_right le_sup_right)))
  have hcomm₀ : ⁅G₀, G₀.map (MulAut.conj t⁻¹).toMonoidHom⁆ = ⊥ := by
    rw [htinv, commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.2 h₁₂
  have hdiag : ∀ x : G, x * (t⁻¹ * x * t) = x * (t * x * t⁻¹) := fun x => by rw [htinv]
  have hrange₀ : (diagonalHom G₀ t hcomm₀).range = L := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨x, rfl⟩
      rw [diagonalHom_apply, hdiag]
      exact hδ x x.2
    · intro y hy
      obtain ⟨x, hx, hxy⟩ := hsurj y hy
      refine ⟨⟨x, hx⟩, ?_⟩
      rw [diagonalHom_apply, hdiag]
      exact hxy
  have hcard₀ : Nat.card G₀ = Nat.card L * Nat.card (center G₀) :=
    SwapUnique.card_eq_mul_card_center_of_diagonal hZL hcomm₀ hrange₀
  have hLD : L ≤ D := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hsurj y hy
    exact mul_mem (mem_sup_left hx) (mem_sup_right ⟨x, hx, rfl⟩)
  have htD : t ∈ normalizer (D : Set G) :=
    SeitzReduction.F4Pilot.mem_normalizer_sup_of_map_conj_eq htt rfl
  set A : Subgroup G := G₀.map (MulAut.conj g).toMonoidHom with hA
  set A' : Subgroup G := Gt.map (MulAut.conj g).toMonoidHom with hA'
  have hAperf : ⁅A, A⁆ = A := by rw [hA, ← map_commutator, hperf]
  have hA'perf : ⁅A', A'⁆ = A' := by rw [hA', ← map_commutator, hperf₂]
  have hAbot : A ≠ ⊥ := fun h =>
    hbot ((map_eq_bot_iff_of_injective G₀ (MulAut.conj g).injective).1 h)
  have hA'bot : A' ≠ ⊥ := fun h =>
    hGtbot ((map_eq_bot_iff_of_injective Gt (MulAut.conj g).injective).1 h)
  have hnA := SeitzReduction.F4Pilot.dichotomy_map_mulAut (MulAut.conj g) hn₁
  have hnA' := SeitzReduction.F4Pilot.dichotomy_map_mulAut (MulAut.conj g) hn₂
  have hAA' : A' ≤ centralizer (A : Set G) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    rw [mem_centralizer_iff]
    intro a ha
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 ha
    have hzy := mem_centralizer_iff.1 (h₁₂ hy) z hz
    change (MulAut.conj g) z * (MulAut.conj g) y = (MulAut.conj g) y * (MulAut.conj g) z
    rw [← map_mul, ← map_mul, hzy]
  have hAA'sup : A ⊔ A' = D.map (MulAut.conj g).toMonoidHom := by
    rw [hD]
    exact (Subgroup.map_sup _ _ _).symm
  have htH : t ∈ normalizer ((A ⊔ A' : Subgroup G) : Set G) := by
    rw [hAA'sup, SeitzReduction.F4Pilot.mem_normalizer_iff_map_conj_toMonoidHom,
      SeitzReduction.F4Pilot.map_conj_map_conj_toMonoidHom,
      show t * g = g * (g⁻¹ * t * g) by group,
      ← SeitzReduction.F4Pilot.map_conj_map_conj_toMonoidHom,
      SeitzReduction.F4Pilot.mem_normalizer_iff_map_conj_toMonoidHom.1 hg]
  rcases SeitzReduction.F4Pilot.map_conj_eq_or_eq_of_perfect hAA' hAperf hAbot hnA hnA' htH with
    h | h
  ·
    exfalso
    refine hnorm g (mem_normalizer_iff_map_conj_eq.2 h) ?_
    have hA'A : A ≤ centralizer (A' : Set G) := le_centralizer_iff.1 hAA'
    have htH' : t ∈ normalizer ((A' ⊔ A : Subgroup G) : Set G) := by rwa [sup_comm]
    rcases SeitzReduction.F4Pilot.map_conj_eq_or_eq_of_perfect hA'A hA'perf hA'bot hnA' hnA
      htH' with h' | h'
    · exact mem_normalizer_iff_map_conj_eq.2 h'
    · exfalso
      have hAA : A = A' :=
        h.symm.trans (SeitzReduction.F4Pilot.map_conj_symm_of_involution htt h')
      apply hAbot
      rw [← hAperf, commutator_eq_bot_iff_le_centralizer.2 (hAA ▸ hAA')]
  ·
    have hAt : A.map (MulAut.conj t⁻¹).toMonoidHom = A' := by
      rw [htinv]
      exact h
    have hcommA : ⁅A, A.map (MulAut.conj t⁻¹).toMonoidHom⁆ = ⊥ := by
      rw [hAt, commutator_comm]
      exact commutator_eq_bot_iff_le_centralizer.2 hAA'
    let e' : G₀ ≃* A := Subgroup.equivMapOfInjective G₀ _ (MulAut.conj g).injective
    have hZA : Odd (Nat.card (center A)) := by
      rw [← Nat.card_congr (Subgroup.centerCongr e').toEquiv]
      exact hZ
    have hcardA : Nat.card A = Nat.card L * Nat.card (center A) := by
      rw [← Nat.card_congr (Subgroup.centerCongr e').toEquiv, ← hcard₀]
      exact Subgroup.card_map_of_injective (MulAut.conj g).injective
    have hle := SwapUnique.sup_le_of_swap_diagonal ht hL hZL hLeven hLt hCperf hR
      (hLD.trans le_normalizer) htD hNR hAperf hZA hcommA hcardA
    rw [hAt, hAA'sup] at hle
    have hHperf : ⁅D.map (MulAut.conj g).toMonoidHom, D.map (MulAut.conj g).toMonoidHom⁆ =
        D.map (MulAut.conj g).toMonoidHom := by
      rw [← map_commutator, hDperf]
    have hHD := hperfN _ hle hHperf
    have heq : D.map (MulAut.conj g).toMonoidHom = D :=
      eq_of_le_of_card_ge hHD (by rw [card_map_of_injective (MulAut.conj g).injective])
    exact mem_normalizer_iff_map_conj_eq.2 heq

theorem false_of_swap_configuration [IsSimpleGroup G] {t : G} (ht : orderOf t = 2)
    {L G₀ R : Subgroup G} (hL : IsSimpleGroup L) (hLab : ¬ ∀ x ∈ L, ∀ y ∈ L, x * y = y * x)
    (hLeven : Even (Nat.card L))
    (hLt : L ≤ centralizer ({t} : Set G))
    (hCperf : ∀ H : Subgroup G, H ≤ centralizer ({t} : Set G) → ⁅H, H⁆ = H → H ≤ L)
    (hq : CFSG.Open.IsQuasisimple G₀) (hZ : Odd (Nat.card (center G₀)))
    (h₁₂ : G₀.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₀ : Set G))
    (hδ : ∀ x ∈ G₀, x * (t * x * t⁻¹) ∈ L)
    (hsurj : ∀ y ∈ L, ∃ x ∈ G₀, x * (t * x * t⁻¹) = y)
    (hR : CFSG.ABGLocalTools.IsSylowOf 2 R (L ⊔ zpowers t))
    (hNR : normalizer (R : Set G) ≤
      normalizer ((G₀ ⊔ G₀.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G))
    (hperfN : ∀ H : Subgroup G,
      H ≤ normalizer ((G₀ ⊔ G₀.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) →
      ⁅H, H⁆ = H → H ≤ G₀ ⊔ G₀.map (MulAut.conj t).toMonoidHom)
    (hnorm : ∀ h : G, t ∈ normalizer ((G₀.map (MulAut.conj h).toMonoidHom : Subgroup G) : Set G) →
      t ∈ normalizer (((G₀.map (MulAut.conj t).toMonoidHom).map (MulAut.conj h).toMonoidHom :
        Subgroup G) : Set G) → False) : False :=
  SeitzReduction.F4Pilot.false_of_simple_of_swap_of_isQuasisimple ht hq h₁₂ rfl
    fun g hg => mem_normalizer_of_conj_mem_normalizer_of_swap ht hL hLab hLeven hLt hCperf hq hZ
      h₁₂ hδ hsurj hR hNR hperfN hnorm g hg

end CFSG.LocalAnalysis.EvenBN.Common
