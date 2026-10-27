module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiCoordsBasic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup
open scoped commutatorElement

section General

variable {G : Type*} [Group G]

theorem zpowers_le_normalizer_of_mem_centralizer {T₁ : Subgroup G} {t : G}
    (ht : t ∈ centralizer (T₁ : Set G)) : zpowers t ≤ normalizer (T₁ : Set G) :=
  zpowers_le.mpr (centralizer_le_normalizer _ ht)

theorem exists_mul_eq_of_mem_sup_zpowers {T₁ : Subgroup G} {t : G}
    (ht : t ∈ centralizer (T₁ : Set G)) {x : G} (hx : x ∈ T₁ ⊔ zpowers t) :
    ∃ y ∈ T₁, ∃ z ∈ zpowers t, y * z = x := by
  have hx' : x ∈ ((T₁ ⊔ zpowers t : Subgroup G) : Set G) := hx
  rw [coe_mul_of_right_le_normalizer_left T₁ (zpowers t)
    (zpowers_le_normalizer_of_mem_centralizer ht)] at hx'
  obtain ⟨y, hy, z, hz, rfl⟩ := hx'
  exact ⟨y, hy, z, hz, rfl⟩

theorem mem_zpowers_involution_eq_one_or_eq {t z : G} (ht : t ^ 2 = 1)
    (hz : z ∈ zpowers t) : z = 1 ∨ z = t := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hz
  have htt : t ^ (2 : ℤ) = 1 := by rw [zpow_two, ← sq, ht]
  rcases Int.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · left
    rw [← two_mul, zpow_mul, htt, one_zpow]
  · right
    rw [zpow_add, zpow_mul, htt, one_zpow, one_mul, zpow_one]

theorem commute_of_mem_zpowers {t z y : G} (hz : z ∈ zpowers t) (hy : y * t = t * y) :
    y * z = z * y := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hz
  exact (Commute.zpow_right hy k).eq

theorem conj_mem_inf_centralizer_of_mem_normalizer {T : Subgroup G} {n : G}
    (hn : n ∈ normalizer (T : Set G)) {x : G} (hx : x ∈ T ⊓ centralizer (T : Set G)) :
    n * x * n⁻¹ ∈ T ⊓ centralizer (T : Set G) := by
  obtain ⟨hxT, hxC⟩ := mem_inf.mp hx
  refine mem_inf.mpr ⟨(mem_normalizer_iff.mp hn x).mp hxT, mem_centralizer_iff.mpr fun y hy => ?_⟩
  have hy' : n⁻¹ * y * n ∈ T := (mem_normalizer_iff''.mp hn y).mp hy
  have e := mem_centralizer_iff.mp hxC _ hy'
  calc y * (n * x * n⁻¹) = n * ((n⁻¹ * y * n) * x) * n⁻¹ := by group
    _ = n * (x * (n⁻¹ * y * n)) * n⁻¹ := by rw [e]
    _ = n * x * n⁻¹ * y := by group

theorem normalizer_le_normalizer_inf_centralizer (T : Subgroup G) :
    normalizer (T : Set G) ≤
      normalizer ((T ⊓ centralizer (T : Set G) : Subgroup G) : Set G) := by
  intro n hn
  refine mem_normalizer_iff.mpr fun x =>
    ⟨fun hx => conj_mem_inf_centralizer_of_mem_normalizer hn hx, fun hx => ?_⟩
  have h := conj_mem_inf_centralizer_of_mem_normalizer (inv_mem hn) hx
  rwa [show n⁻¹ * (n * x * n⁻¹) * n⁻¹⁻¹ = x by group] at h

theorem conj_mem_commutator_of_mem_normalizer {T : Subgroup G} {n : G}
    (hn : n ∈ normalizer (T : Set G)) {x : G} (hx : x ∈ ⁅T, T⁆) : n * x * n⁻¹ ∈ ⁅T, T⁆ := by
  have hle : ⁅T, T⁆ ≤ ⁅T, T⁆.comap (MulAut.conj n).toMonoidHom := by
    rw [commutator_le]
    intro y hy z hz
    rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      show n * ⁅y, z⁆ * n⁻¹ = ⁅n * y * n⁻¹, n * z * n⁻¹⁆ by
        simp only [commutatorElement_def]; group]
    exact commutator_mem_commutator ((mem_normalizer_iff.mp hn y).mp hy)
      ((mem_normalizer_iff.mp hn z).mp hz)
  have h := hle hx
  rwa [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h

theorem conj_mem_centralizer_conj_iff (t g x : G) :
    g⁻¹ * x * g ∈ centralizer ({g⁻¹ * t * g} : Set G) ↔ x ∈ centralizer ({t} : Set G) := by
  rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro h
    have e : g * (g⁻¹ * x * g * (g⁻¹ * t * g)) * g⁻¹ = g * (g⁻¹ * t * g * (g⁻¹ * x * g)) * g⁻¹ := by
      rw [h]
    simpa [mul_assoc] using e
  · intro h
    calc g⁻¹ * x * g * (g⁻¹ * t * g) = g⁻¹ * (x * t) * g := by group
      _ = g⁻¹ * (t * x) * g := by rw [h]
      _ = g⁻¹ * t * g * (g⁻¹ * x * g) := by group

theorem card_centralizer_inv_mul_mul (t g : G) :
    Nat.card (centralizer ({g⁻¹ * t * g} : Set G)) = Nat.card (centralizer ({t} : Set G)) := by
  have h1 : ∀ x : centralizer ({g⁻¹ * t * g} : Set G), g * (x : G) * g⁻¹ ∈
      centralizer ({t} : Set G) := fun x =>
    (conj_mem_centralizer_conj_iff t g _).mp (by simpa [mul_assoc] using x.2)
  have h2 : ∀ x : centralizer ({t} : Set G), g⁻¹ * (x : G) * g ∈
      centralizer ({g⁻¹ * t * g} : Set G) := fun x =>
    (conj_mem_centralizer_conj_iff t g _).mpr x.2
  exact Nat.card_congr
    { toFun := fun x => ⟨_, h1 x⟩
      invFun := fun x => ⟨_, h2 x⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun x => Subtype.ext (by simp [mul_assoc]) }

theorem mem_normalizer_of_forall_inv_mul_mul_mem {H : Subgroup G} [Finite H] {d : G}
    (h : ∀ x ∈ H, d⁻¹ * x * d ∈ H) : d ∈ normalizer (H : Set G) := by
  have hinj : Function.Injective (fun x : H => (⟨d⁻¹ * x * d, h x x.2⟩ : H)) := by
    intro x y hxy
    have e := congrArg Subtype.val hxy
    exact Subtype.ext (by simpa using e)
  have hsurj := Finite.injective_iff_surjective.mp hinj
  refine mem_normalizer_iff.mpr fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · obtain ⟨y, hy⟩ := hsurj ⟨x, hx⟩
    have e : d⁻¹ * (y : G) * d = x := congrArg Subtype.val hy
    rw [← e, show d * (d⁻¹ * (y : G) * d) * d⁻¹ = y by group]
    exact y.2
  · have e := h _ hx
    rwa [show d⁻¹ * (d * x * d⁻¹) * d = x by group] at e

end General

section Fusion

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem exists_mem_normalizer_inv_mul_mul_eq {t : G} {T : Subgroup G}
    (hTH : T ≤ centralizer ({t} : Set G))
    (hT : ∃ P : Sylow p (centralizer ({t} : Set G)),
      (P : Subgroup (centralizer ({t} : Set G))) = T.subgroupOf (centralizer ({t} : Set G)))
    {g : G} (hg : T ≤ centralizer ({g⁻¹ * t * g} : Set G)) :
    ∃ n ∈ normalizer (T : Set G), n⁻¹ * t * n = g⁻¹ * t * g := by
  set s := g⁻¹ * t * g with hs
  set H' := centralizer ({s} : Set G) with hH'
  obtain ⟨P, hP⟩ := hT
  have hcardT : Nat.card T = p ^ (Nat.card H').factorization p := by
    rw [hH', hs, card_centralizer_inv_mul_mul, ← Sylow.card_eq_multiplicity P, hP]
    exact (Nat.card_congr (subgroupOfEquivOfLe hTH).toEquiv).symm
  let Q : Sylow p H' := Sylow.ofCard (T.subgroupOf H') (by
    rw [← hcardT]
    exact Nat.card_congr (subgroupOfEquivOfLe hg).toEquiv)
  set T' := T.map (MulAut.conj g⁻¹).toMonoidHom with hT'
  have hmemT' : ∀ x : G, x ∈ T' ↔ g * x * g⁻¹ ∈ T := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [mul_assoc] using hy
    · intro hx
      exact ⟨g * x * g⁻¹, hx, by simp [mul_assoc]⟩
  have hT'H : T' ≤ H' := by
    intro x hx
    have h1 := hTH ((hmemT' x).mp hx)
    rw [← conj_mem_centralizer_conj_iff t g] at h1
    rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at h1
  have hcardT' : Nat.card T' = Nat.card T := card_map_of_injective (MulAut.conj g⁻¹).injective
  let Q' : Sylow p H' := Sylow.ofCard (T'.subgroupOf H') (by
    rw [← hcardT, ← hcardT']
    exact Nat.card_congr (subgroupOfEquivOfLe hT'H).toEquiv)
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq H' Q' Q
  have hmem : ∀ y : H', (y : G) ∈ T ↔ ((c⁻¹ * y * c : H') : G) ∈ T' := by
    intro y
    have e1 : y ∈ ((c • Q' : Sylow p H') : Subgroup H') ↔ c⁻¹ * y * c ∈ (Q' : Subgroup H') := by
      rw [Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem, ← map_inv,
        MulAut.smul_def, MulAut.conj_apply, inv_inv]
    rw [hc] at e1
    exact e1
  refine ⟨g * (c : G)⁻¹, mem_normalizer_iff''.mpr fun x => ?_, ?_⟩
  · constructor
    · intro hx
      have hxH : g⁻¹ * x * g ∈ H' := hT'H ((hmemT' _).mpr (by simpa [mul_assoc] using hx))
      have hyH : (c : G) * (g⁻¹ * x * g) * (c : G)⁻¹ ∈ H' :=
        mul_mem (mul_mem c.2 hxH) (inv_mem c.2)
      have h1 := (hmem ⟨_, hyH⟩).mpr (by
        show (c : G)⁻¹ * ((c : G) * (g⁻¹ * x * g) * (c : G)⁻¹) * c ∈ T'
        rw [hmemT']
        simpa [mul_assoc] using hx)
      simpa [mul_assoc] using h1
    · intro hx
      have hxH : (g * (c : G)⁻¹)⁻¹ * x * (g * (c : G)⁻¹) ∈ H' := hg hx
      have h1 := (hmem ⟨_, hxH⟩).mp hx
      have h2 := (hmemT' _).mp h1
      simpa [mul_assoc] using h2
  · have hcs : (c : G) * s = s * c := mem_centralizer_singleton_iff.mp c.2
    calc (g * (c : G)⁻¹)⁻¹ * t * (g * (c : G)⁻¹) = (c : G) * s * (c : G)⁻¹ := by
          rw [hs]; group
      _ = s := by rw [hcs, mul_inv_cancel_right]

end Fusion

section Sup

variable {G : Type*} [Group G] {T₁ : Subgroup G} {t : G}

theorem sup_zpowers_le_centralizer_singleton (ht : t ∈ centralizer (T₁ : Set G)) :
    T₁ ⊔ zpowers t ≤ centralizer ({t} : Set G) := by
  refine sup_le (fun y hy => mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp ht y hy)) ?_
  rw [zpowers_le]
  exact mem_centralizer_singleton_iff.mpr rfl

theorem mem_centralizer_sup_zpowers (ht : t ∈ centralizer (T₁ : Set G)) :
    t ∈ centralizer ((T₁ ⊔ zpowers t : Subgroup G) : Set G) :=
  mem_centralizer_iff.mpr fun _ hy =>
    mem_centralizer_singleton_iff.mp (sup_zpowers_le_centralizer_singleton ht hy)

theorem szA₁_le_centralizer_sup_zpowers (ht : t ∈ centralizer (T₁ : Set G)) :
    szA₁ T₁ ≤ centralizer ((T₁ ⊔ zpowers t : Subgroup G) : Set G) := by
  rw [le_centralizer_iff]
  refine sup_le (fun y hy => mem_centralizer_iff.mpr fun b hb =>
    (mem_centralizer_iff.mp (mem_szA₁.mp hb).2 y hy).symm) ?_
  rw [zpowers_le]
  exact mem_centralizer_iff.mpr fun b hb => mem_centralizer_iff.mp ht b (szA₁_le T₁ hb)

theorem card_sup_zpowers_of_disjoint (ht : t ∈ centralizer (T₁ : Set G)) (ht2 : orderOf t = 2)
    (hdisj : T₁ ⊓ zpowers t = ⊥) :
    Nat.card (T₁ ⊔ zpowers t : Subgroup G) = Nat.card T₁ * 2 := by
  rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer T₁ (zpowers t)
    (zpowers_le_normalizer_of_mem_centralizer ht) (disjoint_iff.mpr hdisj), Nat.card_zpowers, ht2]

end Sup

namespace SzStartField

variable {K : Type*} [Field K] [Fintype K] {a : ℕ}

theorem exists_pow_theta_succ_eq (hK : Fintype.card K = 2 ^ (2 * a + 1)) (z : K) :
    ∃ l : K, l ^ (2 ^ (a + 1) + 1) = z := by
  refine ⟨z ^ (2 ^ (a + 1) - 1), ?_⟩
  have hθ2 : 2 ≤ 2 ^ (a + 1) := Nat.le_self_pow (by omega) 2
  by_cases hz : z = 0
  · subst hz
    rw [zero_pow (by omega), zero_pow (by omega)]
  · have h1 : z ^ (2 ^ (a + 1) * 2 ^ (a + 1)) = z ^ 2 := by
      rw [pow_mul, SzRadical.pow_theta_pow_theta hK z]
    have e : (2 ^ (a + 1) - 1) * (2 ^ (a + 1) + 1) + 1 = 2 ^ (a + 1) * 2 ^ (a + 1) := by
      generalize 2 ^ (a + 1) = θ at hθ2 ⊢
      zify [show 1 ≤ θ by omega]
      ring
    have h2 : (z ^ (2 ^ (a + 1) - 1)) ^ (2 ^ (a + 1) + 1) * z = z * z := by
      rw [← pow_mul, ← pow_succ, e, h1, sq]
    exact mul_right_cancel₀ hz h2

theorem exists_pow_theta_add_ne_zero [CharP K 2] (ha : 1 ≤ a)
    (hK : Fintype.card K = 2 ^ (2 * a + 1)) : ∃ c : K, c ^ 2 ^ (a + 1) + c ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon
  have hall : ∀ w : K, w = 0 ∨ w = 1 := fun w =>
    SzRadical.eq_zero_or_eq_one_of_pow_theta_eq hK (by
      have h1 := eq_neg_of_add_eq_zero_left (hcon w)
      rwa [CharTwo.neg_eq] at h1)
  have hsub : (Finset.univ : Finset K) ⊆ {0, 1} := fun w _ => by
    rcases hall w with hw | hw <;> simp [hw]
  have h4 := (Finset.card_le_card hsub).trans Finset.card_le_two
  rw [Finset.card_univ, hK] at h4
  have h5 : 2 ^ 2 ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact absurd (h5.trans h4) (by norm_num)

theorem closure_range_eq_top [CharP K 2] (ha : 1 ≤ a) (hK : Fintype.card K = 2 ^ (2 * a + 1)) :
    AddSubgroup.closure (Set.range fun p : K × K =>
      p.1 * p.2 ^ 2 ^ (a + 1) + p.2 * p.1 ^ 2 ^ (a + 1)) = ⊤ := by
  set W := AddSubgroup.closure (Set.range fun p : K × K =>
    p.1 * p.2 ^ 2 ^ (a + 1) + p.2 * p.1 ^ 2 ^ (a + 1)) with hW
  have hscale : ∀ l : K, ∀ w ∈ W, l ^ (2 ^ (a + 1) + 1) * w ∈ W := by
    intro l
    have hle : W ≤ W.comap (AddMonoidHom.mulLeft (l ^ (2 ^ (a + 1) + 1))) := by
      rw [hW, AddSubgroup.closure_le]
      rintro _ ⟨⟨s, c⟩, rfl⟩
      show l ^ (2 ^ (a + 1) + 1) * (s * c ^ 2 ^ (a + 1) + c * s ^ 2 ^ (a + 1)) ∈ W
      have e : l ^ (2 ^ (a + 1) + 1) * (s * c ^ 2 ^ (a + 1) + c * s ^ 2 ^ (a + 1)) =
          (l * s) * (l * c) ^ 2 ^ (a + 1) + (l * c) * (l * s) ^ 2 ^ (a + 1) := by
        ring
      rw [e]
      exact AddSubgroup.subset_closure ⟨(l * s, l * c), rfl⟩
    exact fun w hw => hle hw
  have hmul : ∀ z : K, ∀ w ∈ W, z * w ∈ W := by
    intro z w hw
    obtain ⟨l, rfl⟩ := exists_pow_theta_succ_eq hK z
    exact hscale l w hw
  obtain ⟨c, hc⟩ := exists_pow_theta_add_ne_zero ha hK
  have hc' : c ^ 2 ^ (a + 1) + c ∈ W := by
    have h1 : (1 : K) * c ^ 2 ^ (a + 1) + c * 1 ^ 2 ^ (a + 1) ∈ W :=
      AddSubgroup.subset_closure ⟨(1, c), rfl⟩
    simpa using h1
  rw [eq_top_iff]
  intro z _
  have h1 := hmul (z / (c ^ 2 ^ (a + 1) + c)) _ hc'
  rwa [div_mul_cancel₀ z hc] at h1

end SzStartField

namespace SzRootCoords

variable {G : Type*} [Group G] {K : Type*} [Field K] {T₁ : Subgroup G} {a : ℕ} {d : G}
  {u v : G → K} {κ : K} {t : G}

theorem card_eq (h : SzRootCoords T₁ a d u v κ) : Nat.card T₁ = Nat.card K * Nat.card K := by
  have hbij : Function.Bijective (fun x : T₁ => (u x, v x)) := by
    constructor
    · intro x y hxy
      simp only [Prod.mk.injEq] at hxy
      exact Subtype.ext (h.inj x x.2 y y.2 hxy.1 hxy.2)
    · rintro ⟨α, β⟩
      obtain ⟨x, hx, hu, hv⟩ := h.surj α β
      exact ⟨⟨x, hx⟩, by simp [hu, hv]⟩
  rw [Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_prod]

variable [Fintype K]

theorem card_szA₁ (h : SzRootCoords T₁ a d u v κ) (ha : 1 ≤ a)
    (hK : Fintype.card K = 2 ^ (2 * a + 1)) : Nat.card (szA₁ T₁) = Nat.card K := by
  have hbij : Function.Bijective (fun x : szA₁ T₁ => v x) := by
    constructor
    · intro x y hxy
      exact Subtype.ext (h.inj x (szA₁_le T₁ x.2) y (szA₁_le T₁ y.2)
        (by rw [h.u_eq_zero_of_mem_szA₁ ha hK x.2, h.u_eq_zero_of_mem_szA₁ ha hK y.2]) hxy)
    · intro w
      obtain ⟨b, hb, hv⟩ := h.exists_v_eq ha hK w
      exact ⟨⟨b, hb⟩, hv⟩
  exact Nat.card_congr (Equiv.ofBijective _ hbij)

theorem inf_centralizer_sup_eq (ht : t ∈ centralizer (T₁ : Set G)) :
    (T₁ ⊔ zpowers t) ⊓ centralizer ((T₁ ⊔ zpowers t : Subgroup G) : Set G) =
      szA₁ T₁ ⊔ zpowers t := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxT, hxC⟩ := mem_inf.mp hx
    obtain ⟨y, hy, z, hz, rfl⟩ := exists_mul_eq_of_mem_sup_zpowers ht hxT
    have hzC : z ∈ centralizer (T₁ : Set G) := zpowers_le.mpr ht hz
    have hyA : y ∈ szA₁ T₁ := by
      refine mem_szA₁.mpr ⟨hy, mem_centralizer_iff.mpr fun w hw => ?_⟩
      have h1 := mem_centralizer_iff.mp hxC w (mem_sup_left hw)
      have h2 := mem_centralizer_iff.mp hzC w hw
      have h3 : w * y * z = y * w * z := by
        rw [mul_assoc, h1, mul_assoc, mul_assoc, h2]
      exact mul_right_cancel h3
    exact mul_mem_sup hyA hz
  · refine sup_le (le_inf ((szA₁_le T₁).trans le_sup_left) (szA₁_le_centralizer_sup_zpowers ht)) ?_
    rw [zpowers_le]
    exact mem_inf.mpr ⟨mem_sup_right (mem_zpowers t), mem_centralizer_sup_zpowers ht⟩

variable [CharP K 2]

theorem mem_of_sq_eq_one (h : SzRootCoords T₁ a d u v κ) (ha : 1 ≤ a)
    (hK : Fintype.card K = 2 ^ (2 * a + 1)) (ht : t ∈ centralizer (T₁ : Set G)) (ht2 : t ^ 2 = 1)
    {x : G} (hx : x ∈ T₁ ⊔ zpowers t) (hx2 : x ^ 2 = 1) : x ∈ szA₁ T₁ ⊔ zpowers t := by
  obtain ⟨y, hy, z, hz, rfl⟩ := exists_mul_eq_of_mem_sup_zpowers ht hx
  have hyz : Commute y z := commute_of_mem_zpowers hz (mem_centralizer_iff.mp ht y hy)
  have hz2 : z ^ 2 = 1 := by
    rcases mem_zpowers_involution_eq_one_or_eq ht2 hz with rfl | rfl
    · exact one_pow 2
    · exact ht2
  have hy2 : y ^ 2 = 1 := by
    rw [hyz.mul_pow, hz2, mul_one] at hx2
    exact hx2
  obtain ⟨-, hv⟩ := h.sq hy
  rw [hy2, h.v_one] at hv
  have hu : u y = 0 := (pow_eq_zero_iff (Nat.succ_ne_zero _)).mp hv.symm
  exact mul_mem_sup ((h.mem_szA₁_iff ha hK hy).mpr hu) hz

theorem szA₁_eq_commutator (h : SzRootCoords T₁ a d u v κ) (ha : 1 ≤ a)
    (hK : Fintype.card K = 2 ^ (2 * a + 1)) (ht : t ∈ centralizer (T₁ : Set G)) :
    szA₁ T₁ = ⁅T₁ ⊔ zpowers t, T₁ ⊔ zpowers t⁆ := by
  apply le_antisymm
  · let W : AddSubgroup K :=
      { carrier := {w | ∃ b ∈ szA₁ T₁, b ∈ ⁅T₁ ⊔ zpowers t, T₁ ⊔ zpowers t⁆ ∧ v b = w}
        add_mem' := by
          rintro _ _ ⟨b, hb, hbT, rfl⟩ ⟨b', hb', hb'T, rfl⟩
          exact ⟨b * b', mul_mem hb hb', mul_mem hbT hb'T, h.v_mul_szA₁ ha hK hb hb'⟩
        zero_mem' := ⟨1, one_mem _, one_mem _, h.v_one⟩
        neg_mem' := by
          rintro _ ⟨b, hb, hbT, rfl⟩
          exact ⟨b, hb, hbT, (CharTwo.neg_eq _).symm⟩ }
    have hW : W = ⊤ := by
      rw [eq_top_iff, ← SzStartField.closure_range_eq_top ha hK, AddSubgroup.closure_le]
      rintro _ ⟨⟨s, c⟩, rfl⟩
      obtain ⟨x, hx, hux, -⟩ := h.surj s 0
      obtain ⟨x', hx', hux', -⟩ := h.surj c 0
      refine ⟨x * x' * x⁻¹ * x'⁻¹, h.comm_mem_szA₁ ha hK hx hx', ?_, ?_⟩
      · rw [← commutatorElement_def]
        exact commutator_mem_commutator (mem_sup_left hx) (mem_sup_left hx')
      · rw [(h.comm hx hx').2, hux, hux']
    intro b hb
    have hvb : v b ∈ W := hW ▸ AddSubgroup.mem_top _
    obtain ⟨b', hb', hb'T, hv⟩ := hvb
    have hbb : b' = b := h.inj b' (szA₁_le T₁ hb') b (szA₁_le T₁ hb)
      (by rw [h.u_eq_zero_of_mem_szA₁ ha hK hb', h.u_eq_zero_of_mem_szA₁ ha hK hb]) hv
    rw [← hbb]
    exact hb'T
  · rw [commutator_le]
    intro x hx x' hx'
    rw [commutatorElement_def]
    have hcomm1 : ∀ g g' : G, g * g' = g' * g → g * g' * g⁻¹ * g'⁻¹ ∈ szA₁ T₁ :=
      fun g g' hgg => by
        rw [hgg, mul_inv_cancel_right, mul_inv_cancel]
        exact one_mem _
    refine comm_mem_of_generators (R := T₁ ⊔ zpowers t) (A := szA₁ T₁)
      (P := fun g => g ∈ T₁ ∨ g = t)
      (fun S hS => sup_le (fun y hy => hS y (Or.inl hy)) (zpowers_le.mpr (hS t (Or.inr rfl))))
      (fun g hg => hg.elim (fun hg => mem_sup_left hg)
        (fun hg => by rw [hg]; exact mem_sup_right (mem_zpowers t)))
      (fun y hy b hb => mem_centralizer_iff.mp (szA₁_le_centralizer_sup_zpowers ht hb) y hy)
      ?_ x hx x' hx'
    rintro g (hg | rfl) g' (hg' | rfl)
    · exact h.comm_mem_szA₁ ha hK hg hg'
    · exact hcomm1 _ _ (mem_centralizer_iff.mp ht g hg)
    · exact hcomm1 _ _ (mem_centralizer_iff.mp ht g' hg').symm
    · exact hcomm1 _ _ rfl

theorem sq_eq_one_of_mem_szA₁_sup (h : SzRootCoords T₁ a d u v κ) (ha : 1 ≤ a)
    (hK : Fintype.card K = 2 ^ (2 * a + 1)) (ht : t ∈ centralizer (T₁ : Set G)) (ht2 : t ^ 2 = 1)
    {x : G} (hx : x ∈ szA₁ T₁ ⊔ zpowers t) : x ^ 2 = 1 := by
  have htA : t ∈ centralizer (szA₁ T₁ : Set G) := centralizer_le (szA₁_le T₁) ht
  obtain ⟨b, hb, z, hz, rfl⟩ := exists_mul_eq_of_mem_sup_zpowers htA hx
  have hbz : Commute b z := commute_of_mem_zpowers hz (mem_centralizer_iff.mp htA b hb)
  have hz2 : z ^ 2 = 1 := by
    rcases mem_zpowers_involution_eq_one_or_eq ht2 hz with rfl | rfl
    · exact one_pow 2
    · exact ht2
  rw [hbz.mul_pow, h.sq_eq_one_of_mem_szA₁ ha hK hb, hz2, one_mul]

end SzRootCoords

theorem card_szA₁_sup {G : Type*} [Group G] {T₁ : Subgroup G} {t : G}
    (ht : t ∈ centralizer (T₁ : Set G)) (ht2 : orderOf t = 2) (hdisj : T₁ ⊓ zpowers t = ⊥) :
    Nat.card (szA₁ T₁ ⊔ zpowers t : Subgroup G) = Nat.card (szA₁ T₁) * 2 :=
  card_sup_zpowers_of_disjoint (centralizer_le (szA₁_le T₁) ht) ht2
    (eq_bot_iff.mpr (le_trans (inf_le_inf_right _ (szA₁_le T₁)) hdisj.le))

end CFSG.SeitzReduction.RankOne
