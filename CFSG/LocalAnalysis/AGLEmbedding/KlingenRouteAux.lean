module

public import CFSG.LocalAnalysis.AGLEmbedding.CentralizerTransport

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers

section Lift

variable {Y : Type*} [Group Y] [Finite Y] {p : ℕ}

theorem exists_mem_normalizer_mk_eq_of_mem_normalizer (hp : p.Prime) (O : Subgroup Y) [O.Normal]
    (hO : p.Coprime (Nat.card O)) {S : Subgroup Y} (hS : IsPGroup p S) {x : Y ⧸ O}
    (hx : x ∈ Subgroup.normalizer
      ((S.map (QuotientGroup.mk' O) : Subgroup (Y ⧸ O)) : Set (Y ⧸ O))) :
    ∃ g ∈ Subgroup.normalizer (S : Set Y), QuotientGroup.mk' O g = x := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective O x
  have hy : y ∈ ((O ⊔ Subgroup.normalizer (S : Set Y) : Subgroup Y) : Set Y) :=
    comap_normalizer_map_le_sup hp O hO hS hx
  rw [Subgroup.normal_mul, Set.mem_mul] at hy
  obtain ⟨n, hn, g, hg, rfl⟩ := hy
  refine ⟨g, hg, ?_⟩
  have hn1 : QuotientGroup.mk' O n = 1 := by
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
    exact hn
  rw [map_mul, hn1, one_mul]

theorem exists_normalizer_lift_with_pow_eq_one (hp : p.Prime) (O : Subgroup Y) [O.Normal]
    (hO : p.Coprime (Nat.card O)) {S : Subgroup Y} (hS : IsPGroup p S) {x : Y ⧸ O}
    (hx : x ∈ Subgroup.normalizer
      ((S.map (QuotientGroup.mk' O) : Subgroup (Y ⧸ O)) : Set (Y ⧸ O)))
    (m : ℕ) (hxm : x ^ m = 1) :
    ∃ g : Subgroup.normalizer (S : Set Y),
      QuotientGroup.mk' O (g : Y) = x ∧ (S.normalizerMonoidHom g) ^ m = 1 := by
  obtain ⟨g0, hg0, hg0x⟩ :=
    exists_mem_normalizer_mk_eq_of_mem_normalizer hp O hO hS hx
  let g : Subgroup.normalizer (S : Set Y) := ⟨g0, hg0⟩
  have hgpow :
      QuotientGroup.mk' O ((g ^ m : Subgroup.normalizer (S : Set Y)) : Y) = 1 := by
    rw [Subgroup.coe_pow, map_pow,
      show QuotientGroup.mk' O (g : Y) = x from by simpa [g] using hg0x, hxm]
  have hact : S.normalizerMonoidHom (g ^ m) = 1 := by
    apply MulEquiv.ext
    intro s
    apply Subtype.ext
    change (((S.normalizerMonoidHom (g ^ m)) s : S) : Y) = (s : Y)
    exact eq_of_mk_eq_of_isPGroup hp O hO hS
      ((S.normalizerMonoidHom (g ^ m)) s).2 s.2 (by
        rw [Subgroup.normalizerMonoidHom_apply_apply_coe,
          map_mul, map_mul, map_inv, hgpow]
        simp)
  refine ⟨g, ?_, ?_⟩
  · simpa [g] using hg0x
  · rw [← map_pow]
    exact hact

theorem exists_mem_normalizer_mk_eq_commute (hp : p.Prime) (O : Subgroup Y) [O.Normal]
    (hO : p.Coprime (Nat.card O)) {S : Subgroup Y} (hS : IsPGroup p S) {x : Y ⧸ O}
    (hx : x ∈ Subgroup.normalizer
      ((S.map (QuotientGroup.mk' O) : Subgroup (Y ⧸ O)) : Set (Y ⧸ O)))
    {y : Y} (hy : y ∈ S) (hxy : x * QuotientGroup.mk' O y = QuotientGroup.mk' O y * x) :
    ∃ g ∈ Subgroup.normalizer (S : Set Y), QuotientGroup.mk' O g = x ∧ g * y = y * g := by
  obtain ⟨g, hg, rfl⟩ := exists_mem_normalizer_mk_eq_of_mem_normalizer hp O hO hS hx
  refine ⟨g, hg, rfl, ?_⟩
  have hconj : g * y * g⁻¹ = y :=
    eq_of_mk_eq_of_isPGroup hp O hO hS ((Subgroup.mem_normalizer_iff.mp hg y).mp hy) hy (by
      rw [map_mul, map_mul, map_inv, hxy, mul_inv_cancel_right])
  exact mul_inv_eq_iff_eq_mul.mp hconj

end Lift

section LiftSubgroup

variable {G : Type*} [Group G] [Finite G] {p : ℕ} {H R : Subgroup G}

theorem exists_lift_of_le_map (hp : p.Prime) (hRH : R ≤ H) (hR : IsPGroup p R)
    (O : Subgroup H) [O.Normal] (hO : p.Coprime (Nat.card O)) {Sbar : Subgroup (H ⧸ O)}
    (hS : Sbar ≤ (R.subgroupOf H).map (QuotientGroup.mk' O)) :
    ∃ (S : Subgroup G) (hSH : S ≤ H), S ≤ R ∧
      (S.subgroupOf H).map (QuotientGroup.mk' O) = Sbar ∧
      (∀ y : H, (y : G) ∈ R → QuotientGroup.mk' O y ∈ Sbar → (y : G) ∈ S) ∧
      ∃ ψ : S ≃* Sbar, ∀ u : S,
        (ψ u : H ⧸ O) = QuotientGroup.mk' O (Subgroup.inclusion hSH u) := by
  set S₁ := Sbar.comap (QuotientGroup.mk' O) ⊓ R.subgroupOf H
  have hS₁ : (S₁.map H.subtype).subgroupOf H = S₁ :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective S₁
  have hmap : ((S₁.map H.subtype).subgroupOf H).map (QuotientGroup.mk' O) = Sbar := by
    rw [hS₁]
    exact map_comap_inf_eq _ hS
  have hSR : S₁.map H.subtype ≤ R :=
    (Subgroup.map_mono inf_le_right).trans (Subgroup.map_subgroupOf_eq_of_le hRH).le
  obtain ⟨φ, hφ⟩ := exists_mulEquiv_map_mk O hp hO (hR.to_le hSR) (Subgroup.map_subtype_le S₁)
  exact ⟨S₁.map H.subtype, Subgroup.map_subtype_le S₁, hSR, hmap,
    fun y hyR hyS => ⟨y, ⟨hyS, hyR⟩, rfl⟩, φ.trans (MulEquiv.subgroupCongr hmap), fun u => hφ u⟩

end LiftSubgroup

section Transport

variable {X Y : Type*} [Group X] [Group Y] {S : Subgroup X} {T : Subgroup Y} {p : ℕ}

theorem pow_eq_one_of_mulEquiv (ψ : S ≃* T) (hT : ∀ y ∈ T, y ^ p = 1) : ∀ x ∈ S, x ^ p = 1 := by
  intro x hx
  have h1 : ψ (⟨x, hx⟩ ^ p) = ψ 1 := by
    rw [map_pow, map_one]
    exact Subtype.ext (hT _ (ψ ⟨x, hx⟩).2)
  simpa using congrArg Subtype.val (ψ.injective h1)

theorem isElemAbelian_of_mulEquiv (ψ : S ≃* T) (hT : IsElemAbelian p T) : IsElemAbelian p S := by
  refine ⟨⟨⟨fun a b => ψ.injective ?_⟩⟩, pow_eq_one_of_mulEquiv ψ hT.2⟩
  rw [map_mul, map_mul]
  exact hT.1.is_comm.comm _ _

end Transport

end CFSG.AGLEmbedding
