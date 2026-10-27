module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneU3StarGroups
public import CFSG.GroupTheory.PCore.PrimeCoreImages
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.Open.StandardComponentRecognitionMilestoneDefs
public import CFSG.Assembly.Defs

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.Open

theorem eq_one_or_eq_of_mem_zpowers_of_sq_eq_one {X : Type*} [Group X] {w : X} (hw : w ^ 2 = 1)
    {x : X} (hx : x ∈ zpowers w) : x = 1 ∨ x = w := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
  have h2 : w ^ (2 : ℤ) = 1 := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, hw]
  rw [zpow_eq_zpow_emod k h2]
  have h0 := Int.emod_nonneg k (by norm_num : (2 : ℤ) ≠ 0)
  have hlt := Int.emod_lt_of_pos k (by norm_num : (0 : ℤ) < 2)
  rcases (by omega : k % 2 = 0 ∨ k % 2 = 1) with h | h <;> rw [h]
  · exact Or.inl (zpow_zero w)
  · exact Or.inr (zpow_one w)

theorem zpowers_normal_of_mem_center {X : Type*} [Group X] {w : X} (hw : w ∈ center X) :
    (zpowers w).Normal :=
  ⟨fun n hn g => by
    have hnZ : n ∈ center X := zpowers_le.mpr hw hn
    have : g * n * g⁻¹ = n := by
      rw [mem_center_iff.mp hnZ g]
      group
    rw [this]
    exact hn⟩

theorem card_comap_eq_card_mul_card_ker {A B : Type*} [Group A] [Group B] [Finite A]
    (f : A →* B) (hf : Function.Surjective f) (U : Subgroup B) :
    Nat.card (U.comap f) = Nat.card U * Nat.card f.ker := by
  have : Finite B := Finite.of_surjective f hf
  have h1 := (U.comap f).card_mul_index
  have h3 : (U.comap f).index = U.index := U.index_comap_of_surjective hf
  have h4 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  have h5 : Nat.card (A ⧸ f.ker) = Nat.card B :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv
  have hpos : 0 < (U.comap f).index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  apply Nat.eq_of_mul_eq_mul_right hpos
  calc Nat.card (U.comap f) * (U.comap f).index = Nat.card A := h1
    _ = Nat.card B * Nat.card f.ker := by rw [h4, h5]
    _ = Nat.card U * U.index * Nat.card f.ker := by rw [U.card_mul_index]
    _ = Nat.card U * Nat.card f.ker * (U.comap f).index := by rw [h3]; ring

theorem pPrimeCore_eq_bot_of_standardComponentOddCore_eq_bot {X : Type*} [Group X]
    (hO : standardComponentOddCore X = ⊥) : CFSG.pPrimeCore 2 X = ⊥ := by
  rw [eq_bot_iff]
  refine sSup_le fun N hN => ?_
  rw [← hO]
  exact le_sSup ⟨hN.1, Nat.coprime_two_left.mp hN.2⟩

variable {H : Type} [Group H] [Finite H]

theorem pPrimeCore_quotient_zpowers_eq_bot {w : H} (hwZ : w ∈ center H) (hw : w ^ 2 = 1)
    [(zpowers w).Normal] (hO : standardComponentOddCore H = ⊥) :
    CFSG.pPrimeCore 2 (H ⧸ zpowers w) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.central_p_subgroup_prime_core_quotient (zpowers w) (zpowers_le.mpr hwZ)
    (isPGroup_zpowers_of_sq_eq_one_two hw),
    pPrimeCore_eq_bot_of_standardComponentOddCore_eq_bot hO, Subgroup.map_bot]

omit [Finite H] in
theorem mem_centralizer_of_mk_mem_centralizer {w t : H} (hwZ : w ∈ center H) (hw : w ^ 2 = 1)
    [(zpowers w).Normal] (h5 : ∀ g : H, g * t * g⁻¹ ≠ t * w) {g : H}
    (hg : QuotientGroup.mk' (zpowers w) g ∈
      centralizer ({QuotientGroup.mk' (zpowers w) t} : Set (H ⧸ zpowers w))) :
    g ∈ centralizer ({t} : Set H) := by
  rw [mem_centralizer_singleton_iff] at hg ⊢
  have h1 : g * t * g⁻¹ * t⁻¹ ∈ zpowers w := by
    rw [← QuotientGroup.ker_mk' (zpowers w), MonoidHom.mem_ker, map_mul, map_mul, map_mul,
      map_inv, map_inv, hg]
    group
  rcases eq_one_or_eq_of_mem_zpowers_of_sq_eq_one hw h1 with h | h
  · calc g * t = g * t * g⁻¹ * t⁻¹ * (t * g) := by group
      _ = t * g := by rw [h]; group
  · exfalso
    apply h5 g
    calc g * t * g⁻¹ = g * t * g⁻¹ * t⁻¹ * t := by group
      _ = w * t := by rw [h]
      _ = t * w := (mem_center_iff.mp hwZ t).symm

omit [Finite H] in
theorem injective_mk_comp_subtype {w : H} (hwZ : w ∈ center H) [(zpowers w).Normal]
    {D : Subgroup H} (hDs : IsSimpleGroup D) (hDnab : ∃ a b : D, a * b ≠ b * a) :
    Function.Injective ((QuotientGroup.mk' (zpowers w)).comp D.subtype) := by
  rw [injective_iff_map_eq_one]
  intro d hd
  have hdw : (d : H) ∈ zpowers w := by
    rw [← QuotientGroup.ker_mk' (zpowers w)]
    exact hd
  have hdZ : (d : H) ∈ center H := zpowers_le.mpr hwZ hdw
  have hdc : d ∈ center D :=
    mem_center_iff.mpr fun d' => Subtype.ext (mem_center_iff.mp hdZ d')
  rw [(CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hDnab).2, mem_bot] at hdc
  exact hdc

omit [Finite H] in
theorem nonempty_mulEquiv_map_mk {w : H} (hwZ : w ∈ center H) [(zpowers w).Normal]
    {D : Subgroup H} (hDs : IsSimpleGroup D) (hDnab : ∃ a b : D, a * b ≠ b * a) :
    Nonempty (D ≃* D.map (QuotientGroup.mk' (zpowers w))) := by
  have hrange : ((QuotientGroup.mk' (zpowers w)).comp D.subtype).range =
      D.map (QuotientGroup.mk' (zpowers w)) := by
    rw [MonoidHom.range_comp, range_subtype]
  exact ⟨(MonoidHom.ofInjective (injective_mk_comp_subtype hwZ hDs hDnab)).trans
    (MulEquiv.subgroupCongr hrange)⟩

theorem isComponent_of_normal_of_simple {X : Type*} [Group X] {A : Subgroup X} (hA : A.Normal)
    (hAs : IsSimpleGroup A) (hAnab : ∃ a b : A, a * b ≠ b * a) : IsComponent A :=
  ⟨(CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hAnab).1, hA.isSubnormal⟩

omit [Finite H] in
theorem isComponent_map_mk {w t : H} (hwZ : w ∈ center H) (hw : w ^ 2 = 1) [(zpowers w).Normal]
    (h5 : ∀ g : H, g * t * g⁻¹ ≠ t * w) {D : Subgroup H} (hDs : IsSimpleGroup D)
    (hDnab : ∃ a b : D, a * b ≠ b * a) (hDt : D ≤ centralizer ({t} : Set H))
    (hDn : ∀ c ∈ centralizer ({t} : Set H), ∀ d ∈ D, c * d * c⁻¹ ∈ D) :
    Nonempty (D ≃* D.map (QuotientGroup.mk' (zpowers w))) ∧
    IsSimpleGroup (D.map (QuotientGroup.mk' (zpowers w))) ∧
    (∃ a b : D.map (QuotientGroup.mk' (zpowers w)), a * b ≠ b * a) ∧
    D.map (QuotientGroup.mk' (zpowers w)) ≤
      centralizer ({QuotientGroup.mk' (zpowers w) t} : Set (H ⧸ zpowers w)) ∧
    (∀ c ∈ centralizer ({QuotientGroup.mk' (zpowers w) t} : Set (H ⧸ zpowers w)),
      ∀ d ∈ D.map (QuotientGroup.mk' (zpowers w)),
        c * d * c⁻¹ ∈ D.map (QuotientGroup.mk' (zpowers w))) ∧
    IsComponent ((D.map (QuotientGroup.mk' (zpowers w))).subgroupOf
      (centralizer ({QuotientGroup.mk' (zpowers w) t} : Set (H ⧸ zpowers w)))) := by
  set π := QuotientGroup.mk' (zpowers w) with hπ
  obtain ⟨e⟩ := nonempty_mulEquiv_map_mk hwZ hDs hDnab
  have hs : IsSimpleGroup (D.map π) := e.symm.isSimpleGroup
  have hnab : ∃ a b : D.map π, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hDnab
    exact ⟨e a, e b, fun h => hab (e.injective (by rw [map_mul, map_mul, h]))⟩
  have hle : D.map π ≤ centralizer ({π t} : Set (H ⧸ zpowers w)) := by
    rintro _ ⟨d, hd, rfl⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      mem_centralizer_singleton_iff.mp (hDt hd)]
  have hn : ∀ c ∈ centralizer ({π t} : Set (H ⧸ zpowers w)), ∀ d ∈ D.map π,
      c * d * c⁻¹ ∈ D.map π := by
    intro c hc d hd
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (zpowers w) c
    obtain ⟨y, hy, rfl⟩ := hd
    have hg := mem_centralizer_of_mk_mem_centralizer hwZ hw h5 hc
    refine ⟨g * y * g⁻¹, hDn g hg y hy, ?_⟩
    rw [map_mul, map_mul, map_inv]
  refine ⟨⟨e⟩, hs, hnab, hle, hn, ?_⟩
  have hN : ((D.map π).subgroupOf (centralizer ({π t} : Set (H ⧸ zpowers w)))).Normal :=
    (normal_subgroupOf_iff hle).mpr fun d c hd hc => hn c hc d hd
  let e₂ := subgroupOfEquivOfLe hle
  have hs₂ : IsSimpleGroup ((D.map π).subgroupOf (centralizer ({π t} : Set (H ⧸ zpowers w)))) :=
    e₂.isSimpleGroup
  have hnab₂ : ∃ a b : (D.map π).subgroupOf (centralizer ({π t} : Set (H ⧸ zpowers w))),
      a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    exact ⟨e₂.symm a, e₂.symm b, fun h => hab (e₂.symm.injective (by rw [map_mul, map_mul, h]))⟩
  exact isComponent_of_normal_of_simple hN hs₂ hnab₂

theorem card_le_two_of_le_centralizer_map_mk {w t : H} (hwZ : w ∈ center H) (hw : orderOf w = 2)
    [(zpowers w).Normal] (h5 : ∀ g : H, g * t * g⁻¹ ≠ t * w) {D : Subgroup H}
    (hDs : IsSimpleGroup D) (hDnab : ∃ a b : D, a * b ≠ b * a)
    (hDn : ∀ c ∈ centralizer ({t} : Set H), ∀ d ∈ D, c * d * c⁻¹ ∈ D)
    (h4 : ∀ Q : Subgroup H, IsPGroup 2 Q → Q ≤ centralizer ({t} : Set H) ⊓ centralizer (D : Set H) →
      Nat.card Q ≤ 4)
    (U : Subgroup (H ⧸ zpowers w)) (hU : IsPGroup 2 U)
    (hUle : U ≤ centralizer ({QuotientGroup.mk' (zpowers w) t} : Set (H ⧸ zpowers w)) ⊓
      centralizer ((D.map (QuotientGroup.mk' (zpowers w)) : Subgroup _) : Set (H ⧸ zpowers w))) :
    Nat.card U ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (zpowers w) with hπ
  have hw2 : w ^ 2 = 1 := by rw [← hw]; exact pow_orderOf_eq_one w
  have hker : π.ker = zpowers w := QuotientGroup.ker_mk' _
  have hcardker : Nat.card π.ker = 2 := by rw [hker, Nat.card_zpowers, hw]
  have hcard := card_comap_eq_card_mul_card_ker π (QuotientGroup.mk'_surjective _) U
  rw [hcardker] at hcard
  have hUp : IsPGroup 2 (U.comap π) :=
    hU.comap_of_ker_isPGroup π (by rw [hker]; exact isPGroup_zpowers_of_sq_eq_one_two hw2)
  have hinj := injective_mk_comp_subtype hwZ hDs hDnab
  have hle : U.comap π ≤ centralizer ({t} : Set H) ⊓ centralizer (D : Set H) := by
    intro g hg
    have hg1 : π g ∈ centralizer ({π t} : Set (H ⧸ zpowers w)) := (mem_inf.mp (hUle hg)).1
    have hg2 : π g ∈ centralizer ((D.map π : Subgroup _) : Set (H ⧸ zpowers w)) :=
      (mem_inf.mp (hUle hg)).2
    have hgt := mem_centralizer_of_mk_mem_centralizer hwZ hw2 h5 hg1
    refine mem_inf.mpr ⟨hgt, mem_centralizer_iff.mpr fun d hd => ?_⟩
    have hc : g * d * g⁻¹ * d⁻¹ ∈ D := mul_mem (hDn g hgt d hd) (inv_mem hd)
    have hcπ : π (g * d * g⁻¹ * d⁻¹) = 1 := by
      have := mem_centralizer_iff.mp hg2 (π d) ⟨d, hd, rfl⟩
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← this]
      group
    have h1 : (⟨g * d * g⁻¹ * d⁻¹, hc⟩ : D) = 1 :=
      hinj (by rw [MonoidHom.comp_apply, map_one]; exact hcπ)
    have h2 : g * d * g⁻¹ * d⁻¹ = 1 := congrArg Subtype.val h1
    calc d * g = (g * d * g⁻¹ * d⁻¹)⁻¹ * (g * d) := by group
      _ = g * d := by rw [h2]; group
  have := h4 _ hUp hle
  omega

theorem two_mul_card_le_of_le_centralizer_mk {w t : H} (hwZ : w ∈ center H) (hw : orderOf w = 2)
    [(zpowers w).Normal] (h5 : ∀ g : H, g * t * g⁻¹ ≠ t * w) {N : ℕ}
    (hN : ∀ Q : Subgroup H, IsPGroup 2 Q → Q ≤ centralizer ({t} : Set H) → Nat.card Q ≤ N)
    (U : Subgroup (H ⧸ zpowers w)) (hU : IsPGroup 2 U)
    (hUle : U ≤ centralizer ({QuotientGroup.mk' (zpowers w) t} : Set (H ⧸ zpowers w))) :
    2 * Nat.card U ≤ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (zpowers w) with hπ
  have hw2 : w ^ 2 = 1 := by rw [← hw]; exact pow_orderOf_eq_one w
  have hker : π.ker = zpowers w := QuotientGroup.ker_mk' _
  have hcardker : Nat.card π.ker = 2 := by rw [hker, Nat.card_zpowers, hw]
  have hcard := card_comap_eq_card_mul_card_ker π (QuotientGroup.mk'_surjective _) U
  rw [hcardker] at hcard
  have hUp : IsPGroup 2 (U.comap π) :=
    hU.comap_of_ker_isPGroup π (by rw [hker]; exact isPGroup_zpowers_of_sq_eq_one_two hw2)
  have hle : U.comap π ≤ centralizer ({t} : Set H) := fun g hg =>
    mem_centralizer_of_mk_mem_centralizer hwZ hw2 h5 (hUle hg)
  have := hN _ hUp hle
  omega

theorem card_le_two_mul_card_map_mk {w : H} (hw : w ^ 2 = 1) [(zpowers w).Normal]
    (P : Subgroup H) : Nat.card P ≤ 2 * Nat.card (P.map (QuotientGroup.mk' (zpowers w))) := by
  set π := QuotientGroup.mk' (zpowers w) with hπ
  set ψ := π.comp P.subtype with hψ
  have hrange : ψ.range = P.map π := by rw [hψ, MonoidHom.range_comp, range_subtype]
  have hkle : ψ.ker.map P.subtype ≤ zpowers w := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← QuotientGroup.ker_mk' (zpowers w)]
    exact hx
  have hkcard : Nat.card ψ.ker ≤ 2 := by
    have h1 := card_le_of_le hkle
    rw [card_map_of_injective P.subtype_injective, Nat.card_zpowers] at h1
    have h2 : orderOf w ≤ 2 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hw)
    omega
  rw [← Subgroup.card_ker_mul_card_range ψ, hrange]
  exact Nat.mul_le_mul_right _ hkcard

end CFSG.SeitzReduction.RankOne
