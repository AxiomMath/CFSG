module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanP1ThreeLieWeakCore
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Fact1019

open CFSG.Open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.AGLEmbedding.P1Lie

section Counting

variable {K : Type*} [Group K] [Finite K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

theorem exists_card_ge_of_commRoots (hext : SteinbergExtras D n H) {p : ℕ} (hp : p.Prime)
    (t : K) (w : (Fin D.rank → ℤ) → ℕ) (S : Finset (Fin D.rank → ℤ))
    (hS : ∀ γ ∈ S, γ ∈ D.roots ∧ 0 < ht γ ∧ ∀ δ ∈ D.roots, γ ≠ 2 • δ)
    (hcomm : ∀ γ ∈ S, ∀ δ ∈ S, γ ≠ δ → CommRoots D γ δ)
    (hroot : ∀ γ ∈ S, ∃ E ≤ D.rootGroup γ ⊓ Subgroup.centralizer {t},
      IsElemAbelian p E ∧ p ^ w γ ≤ Nat.card E) :
    ∃ E : Subgroup K, E ≤ posUnipotent D ⊓ Subgroup.centralizer {t} ∧ IsElemAbelian p E ∧
      p ^ (∑ γ ∈ S, w γ) ≤ Nat.card E := by
  classical
  obtain ⟨L, hnd, hmem, hs⟩ := exists_sorted_list
    (S := {γ | γ ∈ D.roots ∧ 0 < ht γ ∧ ∀ δ ∈ D.roots, γ ≠ 2 • δ})
    ((RootSystem.ofCartan D.isFiniteType D.divisible).finite_roots.subset fun _ h => h.1) ht
  have hinj : ProdInjectiveFor D.rootGroup L :=
    hext.prodInjective_pos L hnd (fun γ => hmem γ) hs
  choose! E hEX hEab hEcard using hroot
  have hSL : ∀ γ ∈ S, γ ∈ L := fun γ hγ =>
    (hmem γ).2 ⟨(hS γ hγ).1, (hS γ hγ).2.1, (hS γ hγ).2.2⟩
  have hEX' : ∀ γ ∈ S, E γ ≤ D.rootGroup γ := fun γ hγ => (hEX γ hγ).trans inf_le_left
  have hcount := prod_card_le_card_closure hinj S hSL E hEX'
  have hlow : ∏ γ ∈ S, p ^ w γ ≤ ∏ γ ∈ S, Nat.card (E γ) :=
    Finset.prod_le_prod' fun γ hγ => hEcard γ hγ
  rw [Finset.prod_pow_eq_pow_sum] at hlow
  have hab : IsElemAbelian p (Subgroup.closure (⋃ γ ∈ S, (E γ : Set K))) := by
    refine isElemAbelian_closure_iUnion S E (fun γ hγ x hx => (hEab γ hγ).2 x hx) ?_
    intro γ hγ δ hδ x hx y hy
    by_cases hγδ : γ = δ
    · subst hγδ
      have := (hEab γ hγ).1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
      exact (congrArg Subtype.val this : x * y = y * x)
    · exact commute_of_commRoots hext (hS γ hγ).1 (hS δ hδ).1 (hcomm γ hγ δ hδ hγδ)
        (hEX' γ hγ hx) (hEX' δ hδ hy)
  refine ⟨Subgroup.closure (⋃ γ ∈ S, (E γ : Set K)), le_inf ?_ ?_, hab, hlow.trans hcount⟩
  · rw [Subgroup.closure_le]
    intro x hx
    obtain ⟨γ, hγ, hxγ⟩ : ∃ γ ∈ S, x ∈ E γ := by simpa using hx
    exact rootGroup_le_posUnipotent (hS γ hγ).1 (hS γ hγ).2.1 (hEX' γ hγ hxγ)
  · rw [Subgroup.closure_le]
    intro x hx
    obtain ⟨γ, hγ, hxγ⟩ : ∃ γ ∈ S, x ∈ E γ := by simpa using hx
    exact (hEX γ hγ hxγ).2

end Counting

theorem exists_subgroup_card_of_isElemAbelian {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {E : Subgroup G} (hE : IsElemAbelian p E) {m : ℕ} (hm : p ^ m ≤ Nat.card E) :
    ∃ E' ≤ E, IsElemAbelian p E' ∧ Nat.card E' = p ^ m := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpg : IsPGroup p E := fun g => ⟨1, by
    apply Subtype.ext
    simpa using hE.2 g g.2⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hpg
  have hmk : m ≤ k := by
    rw [hk] at hm
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 hm
  obtain ⟨K', hK', -, hKE⟩ := Sylow.exists_subgroup_card_pow_prime_le_le hp (n := m)
    (H := (⊥ : Subgroup G)) (L := E) (by simp) (by rw [hk]; exact pow_dvd_pow p hmk) bot_le
  refine ⟨K', hKE, ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => hE.2 x (hKE hx)⟩, hK'⟩
  have h := hE.1.is_comm.comm ⟨(a : G), hKE a.2⟩ ⟨(b : G), hKE b.2⟩
  exact Subtype.ext (congrArg Subtype.val h : (a : G) * b = b * a)

theorem exists_involution_of_central_cover {K X : Type*} [Group K] [Finite K] [Group X] [Finite X]
    {p : ℕ} (hp : p.Prime) (hcen : ∀ z ∈ Subgroup.center K, z ^ p = 1 → z = 1) (ψ : K →* X)
    (hker : ψ.ker ≤ Subgroup.center K) {t : K} (ht2 : t ^ 2 = 1) (ht1 : ψ t ≠ 1)
    {E : Subgroup K} (hEc : E ≤ Subgroup.centralizer {t}) (hEa : IsElemAbelian p E)
    (hEcard : Nat.card E = p ^ 4) :
    ∃ t' : X, orderOf t' = 2 ∧ ∃ E' : Subgroup X, E' ≤ Subgroup.centralizer {t'} ∧
      IsElemAbelian p E' ∧ Nat.card E' = p ^ 4 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hinjE : Function.Injective (ψ.comp E.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx1 : ψ (x : K) = 1 := hx
    have hz : (x : K) ∈ Subgroup.center K := hker (MonoidHom.mem_ker.2 hx1)
    have hxp : (x : K) ^ p = 1 := by simpa using hEa.2 x x.2
    exact Subtype.ext (hcen _ hz hxp)
  have hmap : E.map ψ = (ψ.comp E.subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  refine ⟨ψ t, orderOf_eq_prime (by rw [← map_pow, ht2, map_one]) ht1, E.map ψ, ?_,
    CFSG.SectionRank.isElemAbelian_map hEa ψ, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.1 hh]
    have := Subgroup.mem_centralizer_iff.1 (hEc hy) t (Set.mem_singleton t)
    rw [← map_mul, ← map_mul, this]
  · rw [hmap, ← Nat.card_congr (MonoidHom.ofInjective hinjE).toEquiv, hEcard]

theorem exists_isElemAbelian_of_isPGroup {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {X : Subgroup G} (hX : IsPGroup p X) (hne : X ≠ ⊥) :
    ∃ E ≤ X, IsElemAbelian p E ∧ p ^ 1 ≤ Nat.card E := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hX
  have hk1 : k ≠ 0 := by
    rintro rfl
    exact hne (Subgroup.card_eq_one.1 (by simpa using hk))
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := X) p (by
    rw [hk]
    exact dvd_pow_self p hk1)
  have hxo : orderOf (x : G) = p := by rw [Subgroup.orderOf_coe, hx]
  refine ⟨Subgroup.zpowers (x : G), ?_, ⟨inferInstance, ?_⟩, ?_⟩
  · rw [Subgroup.zpowers_le]
    exact x.2
  · intro y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hxo, pow_orderOf_eq_one,
      one_zpow]
  · rw [Nat.card_zpowers, hxo, pow_one]

section FourRoots

variable {K : Type*} [Group K] [Finite K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

theorem exists_elemAbelian_of_weighted_roots (hext : SteinbergExtras D n H) {p : ℕ}
    (hp : p.Prime) (t : K) (w : (Fin D.rank → ℤ) → ℕ) (S : Finset (Fin D.rank → ℤ))
    (hS : ∀ γ ∈ S, γ ∈ D.roots ∧ 0 < ht γ ∧ ∀ δ ∈ D.roots, γ ≠ 2 • δ)
    (hcomm : ∀ γ ∈ S, ∀ δ ∈ S, γ ≠ δ → CommRoots D γ δ)
    (htc : ∀ γ ∈ S, ∀ x ∈ D.rootGroup γ, t * x = x * t)
    (hroot : ∀ γ ∈ S, ∃ E ≤ D.rootGroup γ, IsElemAbelian p E ∧ p ^ w γ ≤ Nat.card E)
    (hw : 4 ≤ ∑ γ ∈ S, w γ) :
    ∃ E : Subgroup K, E ≤ Subgroup.centralizer {t} ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 4 := by
  have hXc : ∀ γ ∈ S, D.rootGroup γ ≤ Subgroup.centralizer {t} := by
    intro γ hγ x hx
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.1 hh]
    exact htc γ hγ x hx
  obtain ⟨E, hE, hEa, hEcard⟩ := exists_card_ge_of_commRoots hext hp t w S hS hcomm
    (fun γ hγ => by
      obtain ⟨E, hEX, hEa, hEcard⟩ := hroot γ hγ
      exact ⟨E, le_inf hEX (hEX.trans (hXc γ hγ)), hEa, hEcard⟩)
  obtain ⟨E', hE', hE'a, hE'card⟩ := exists_subgroup_card_of_isElemAbelian hp hEa
    ((Nat.pow_le_pow_right hp.pos hw).trans hEcard)
  exact ⟨E', hE'.trans (hE.trans inf_le_right), hE'a, hE'card⟩

theorem exists_elemAbelian_of_four_roots (hext : SteinbergExtras D n H) {p : ℕ} (hp : p.Prime)
    (hX : ∀ γ ∈ D.roots, IsPGroup p (D.rootGroup γ)) (t : K) (S : Finset (Fin D.rank → ℤ))
    (hcard : S.card = 4)
    (hS : ∀ γ ∈ S, γ ∈ D.roots ∧ 0 < ht γ ∧ ∀ δ ∈ D.roots, γ ≠ 2 • δ)
    (hcomm : ∀ γ ∈ S, ∀ δ ∈ S, γ ≠ δ → CommRoots D γ δ)
    (htc : ∀ γ ∈ S, ∀ x ∈ D.rootGroup γ, t * x = x * t) :
    ∃ E : Subgroup K, E ≤ Subgroup.centralizer {t} ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 4 :=
  exists_elemAbelian_of_weighted_roots hext hp t (fun _ => 1) S hS hcomm htc
    (fun γ hγ => exists_isElemAbelian_of_isPGroup hp (hX γ (hS γ hγ).1)
      (hext.ne_bot γ (hS γ hγ).1))
    (by rw [Finset.sum_const, hcard, smul_eq_mul, mul_one])

end FourRoots

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Fact1019
