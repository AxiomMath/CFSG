module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2023ARank

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2023

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

structure TD4Facts (S : Type) [Group S] [Finite S] (q : TauCeti.PrimePower) : Prop
    extends TD4Rank S where
  C : ∀ φ : MulAut S, φ ^ 3 = 1 → φ ∉ innerAutS S →
    ∃ g : S, (MulAut.conj g * φ) ^ 3 = 1 ∧
      (Nat.card {x : S // (MulAut.conj g * φ) x = x}).factorization 2 = 6 * q.exponent ∧
      ∃ E : Subgroup S, IsElemAbelian 3 E ∧ Nat.card E = 9 ∧
        ∀ e ∈ E, (MulAut.conj g * φ) e = e
  D : Odd q.exponent → ∀ E T : Subgroup (MulAut S), IsElemAbelian 3 E → IsPGroup 2 T → T ≠ ⊥ →
    E ≤ Subgroup.normalizer (T : Set (MulAut S)) → Nat.card E ≤ 9
  E : Even q.exponent → ∀ φ : MulAut S, φ ^ 3 = 1 → φ ∉ innerAutS S →
    (Nat.card {x : S // φ x = x}).factorization 2 = 6 * q.exponent →
    ∀ r : ℕ, r ≤ 2 → ∃ E : Subgroup S, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ r ∧
      (∀ e ∈ E, φ e = e) ∧
      ∃ U : Subgroup S, IsPGroup 2 U ∧ 8 < Nat.card U ∧ (∀ u ∈ U, φ u ∈ U) ∧
        (∀ e ∈ E, ∀ u ∈ U, e * u * e⁻¹ ∈ U) ∧ ∃ u ∈ U, φ u ≠ u

theorem mem_center_of_conj_eq_one {S : Type} [Group S] {c : S} (h : MulAut.conj c = 1) :
    c ∈ Subgroup.center S := by
  rw [Subgroup.mem_center_iff]
  intro g
  have hg := congrArg (fun φ : MulAut S => φ g) h
  simp only [MulAut.conj_apply, MulAut.one_apply] at hg
  exact (mul_inv_eq_iff_eq_mul.1 hg).symm

theorem exists_bs {q : TauCeti.PrimePower} {x : G} {L : Subgroup G}
    (hL : GLAPComponent 3 (cx x) L) (hXN : cx x ≤ Subgroup.normalizer (L : Set G))
    (hZ : Subgroup.center (PQuot 3 L) = ⊥) (F : TD4Facts (PQuot 3 L) q)
    {b₀ : G} (hb₀ : b₀ ∈ cx x) (hb₀3 : b₀ ^ 3 = 1) (hnon : ¬ InducesInnerMod 3 L b₀) :
    ∃ bs : G, ∃ hbs : bs ∈ cx x, (∃ g : ↥L, bs = (g : G) * b₀) ∧
      bs ^ 3 ∈ GLAPPrimeCoreOf 3 (cx x) ∧
      rho L ⟨bs, hXN hbs⟩ ^ 3 = 1 ∧ rho L ⟨bs, hXN hbs⟩ ∉ innerAutS (PQuot 3 L) ∧
      (Nat.card {y : PQuot 3 L // rho L ⟨bs, hXN hbs⟩ y = y}).factorization 2 = 6 * q.exponent ∧
      ∃ D : Subgroup (PQuot 3 L), IsElemAbelian 3 D ∧ Nat.card D = 9 ∧
        ∀ d ∈ D, rho L ⟨bs, hXN hbs⟩ d = d := by
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have hLX : L ≤ cx x := hL.1
  have hOL : GLAPPrimeCoreOf 3 L ≤ GLAPPrimeCoreOf 3 (cx x) := by
    rw [← glaPPrimeCoreOf_inf_eq_of_isSubnormal hp3 hL.2.1]
    exact inf_le_right
  have hb₀N : b₀ ∈ Subgroup.normalizer (L : Set G) := hXN hb₀
  set φ : MulAut (PQuot 3 L) := rho L ⟨b₀, hb₀N⟩ with hφ
  have hφ3 : φ ^ 3 = 1 := by
    rw [hφ, ← map_pow]
    have : (⟨b₀, hb₀N⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ 3 = 1 := Subtype.ext hb₀3
    rw [this, map_one]
  have hφout : φ ∉ innerAutS (PQuot 3 L) := fun h =>
    hnon ((inducesInnerMod_iff_barAut_mem_inner hb₀N).2 h)
  obtain ⟨g, hg3, hgfix, E, hE, hE9, hEfix⟩ := F.C φ hφ3 hφout
  obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective g
  have hbs : (g' : G) * b₀ ∈ cx x := Subgroup.mul_mem _ (hLX g'.2) hb₀
  have hbsN : (g' : G) * b₀ ∈ Subgroup.normalizer (L : Set G) := hXN hbs
  have hrho : rho L ⟨(g' : G) * b₀, hbsN⟩ = MulAut.conj (QuotientGroup.mk g' : PQuot 3 L) * φ := by
    have e : (⟨(g' : G) * b₀, hbsN⟩ : ↥(Subgroup.normalizer (L : Set G))) =
        ⟨(g' : G), Subgroup.le_normalizer g'.2⟩ * ⟨b₀, hb₀N⟩ := rfl
    rw [e, map_mul, rho_inner]
  have hψ3 : rho L ⟨(g' : G) * b₀, hbsN⟩ ^ 3 = 1 := by rw [hrho]; exact hg3
  have hcube : ((g' : G) * b₀) ^ 3 ∈ L := by
    have hb₀2 : b₀ ^ 2 ∈ Subgroup.normalizer (L : Set G) := Subgroup.pow_mem _ hb₀N 2
    have h1 : b₀ * (g' : G) * b₀⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hb₀N (g' : G)).1 g'.2
    have h2 : b₀ ^ 2 * (g' : G) * (b₀ ^ 2)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.1 hb₀2 (g' : G)).1 g'.2
    have e : ((g' : G) * b₀) ^ 3 =
        (g' : G) * (b₀ * (g' : G) * b₀⁻¹) * (b₀ ^ 2 * (g' : G) * (b₀ ^ 2)⁻¹) * b₀ ^ 3 := by
      rw [pow_three']
      group
    rw [e, hb₀3, mul_one]
    exact L.mul_mem (L.mul_mem g'.2 h1) h2
  have hbs3 : ((g' : G) * b₀) ^ 3 ∈ GLAPPrimeCoreOf 3 (cx x) := by
    set y : ↥L := ⟨((g' : G) * b₀) ^ 3, hcube⟩ with hy
    have h1 : rho L ⟨(y : G), Subgroup.le_normalizer y.2⟩ = 1 := by
      have e : (⟨(y : G), Subgroup.le_normalizer y.2⟩ : ↥(Subgroup.normalizer (L : Set G))) =
          ⟨(g' : G) * b₀, hbsN⟩ ^ 3 := rfl
      rw [e, map_pow, hψ3]
    rw [rho_inner] at h1
    have h2 := mem_center_of_conj_eq_one h1
    rw [hZ, Subgroup.mem_bot] at h2
    have h3 : (y : G) ∈ GLAPPrimeCoreOf 3 L :=
      (mem_core_iff y).2 ((QuotientGroup.eq_one_iff y).1 h2)
    exact hOL h3
  refine ⟨(g' : G) * b₀, hbs, ⟨g', rfl⟩, hbs3, ?_, ?_, ?_, ?_⟩
  · exact hψ3
  · rw [hrho]
    intro h
    apply hφout
    have hc : MulAut.conj (QuotientGroup.mk g' : PQuot 3 L) ∈ innerAutS (PQuot 3 L) := ⟨_, rfl⟩
    have := Subgroup.mul_mem _ (Subgroup.inv_mem _ hc) h
    simpa using this
  · rw [hrho]; exact hgfix
  · refine ⟨E, hE, hE9, fun d hd => ?_⟩
    rw [hrho]
    exact hEfix d hd

theorem card_ge_81 {L : Subgroup G} (hZ : Subgroup.center (PQuot 3 L) = ⊥)
    {S : Subgroup G} (hSL : S ≤ Subgroup.normalizer (L : Set G)) (hS : IsElemAbelian 3 S)
    {x : G} (hxS : x ∈ S) (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1)
    (hxL : x ∈ centModSubgroup 3 L)
    {D : Subgroup (PQuot 3 L)} (hD9 : Nat.card D = 9)
    (hDreal : ∀ d ∈ D, ∃ s ∈ S, ∃ hs : s ∈ Subgroup.normalizer (L : Set G),
      rho L ⟨s, hs⟩ = MulAut.conj d)
    {sb : G} (hsbS : sb ∈ S) (hsb : sb ∈ Subgroup.normalizer (L : Set G))
    (hψ : rho L ⟨sb, hsb⟩ ∉ innerAutS (PQuot 3 L)) : 81 ≤ Nat.card S := by
  have hinj := conj_injective_of_center_eq_bot hZ
  set R := (rhoSub L S hSL).range with hR
  have hcard := card_eq_range_mul_ker L S hSL
  have hker : 3 ≤ Nat.card (rhoSub L S hSL).ker := by
    set xs : ↥S := ⟨x, hxS⟩ with hxs
    have hxs3 : xs ^ 3 = 1 := Subtype.ext hx3
    have hxs1 : xs ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
    have hord : orderOf xs = 3 := orderOf_eq_prime hxs3 hxs1
    have hle : Subgroup.zpowers xs ≤ (rhoSub L S hSL).ker := by
      rw [Subgroup.zpowers_le]
      exact (mem_ker_rhoSub L S hSL xs).2 hxL
    have h1 := Subgroup.card_dvd_of_le hle
    rw [Nat.card_zpowers, hord] at h1
    exact Nat.le_of_dvd Nat.card_pos h1
  have hR27 : 27 ≤ Nat.card R := by
    set Dm : Subgroup (MulAut (PQuot 3 L)) := D.map (MulAut.conj : PQuot 3 L →* MulAut (PQuot 3 L))
      with hDm
    have hDm9 : Nat.card Dm = 9 := by rw [hDm, Subgroup.card_map_of_injective hinj, hD9]
    have hDmR : Dm ≤ R := by
      rintro _ ⟨d, hd, rfl⟩
      obtain ⟨s, hs, hsN, hρ⟩ := hDreal d hd
      exact ⟨⟨s, hs⟩, by rw [rhoSub_apply]; exact hρ⟩
    have hRel : IsElemAbelian 3 R := isElemAbelian_range hS (rhoSub L S hSL)
    have hRp : IsPGroup 3 R := fun g => ⟨1, Subtype.ext (by simpa using hRel.2 g.1 g.2)⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hRp
    have h9 : 9 ∣ Nat.card R := hDm9 ▸ Subgroup.card_dvd_of_le hDmR
    have hne : Nat.card R ≠ 9 := by
      intro h
      have heq : Dm = R := Subgroup.eq_of_le_of_card_ge hDmR (by rw [h, hDm9])
      have hmem : rho L ⟨sb, hsb⟩ ∈ R := ⟨⟨sb, hsbS⟩, rfl⟩
      rw [← heq] at hmem
      obtain ⟨d, -, hd⟩ := hmem
      exact hψ ⟨d, hd⟩
    rw [hk] at h9 hne ⊢
    have hk2 : 2 ≤ k := by
      by_contra hlt
      have hlt' : k < 2 := not_le.1 hlt
      interval_cases k <;> simp_all
    have hk3 : 3 ≤ k := by
      by_contra hlt
      have : k = 2 := by omega
      subst this
      exact hne (by norm_num)
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk3
  rw [hcard]
  calc 81 = 27 * 3 := by norm_num
    _ ≤ Nat.card R * Nat.card (rhoSub L S hSL).ker := Nat.mul_le_mul hR27 hker

end CFSG.LocalAnalysis.GLTheoremA.I2023

end
