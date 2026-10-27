module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2023AGen
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2023Facts

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2023

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

structure TD4Rank (S : Type) [Group S] [Finite S] : Prop where
  A : ∀ E : Subgroup S, IsElemAbelian 3 E → Nat.card E ≤ 9
  B : ∀ E : Subgroup (MulAut S), IsElemAbelian 3 E →
    Nat.card E ≤ 3 * Nat.card ↥(E ⊓ innerAutS S)

@[expose] noncomputable def rhoSub (L A : Subgroup G) (hA : A ≤ Subgroup.normalizer (L : Set G)) :
    ↥A →* MulAut (PQuot 3 L) :=
  (rho L).comp (Subgroup.inclusion hA)

theorem rhoSub_apply (L A : Subgroup G) (hA : A ≤ Subgroup.normalizer (L : Set G)) (a : ↥A) :
    rhoSub L A hA a = rho L ⟨(a : G), hA a.2⟩ := rfl

theorem mem_ker_rhoSub (L A : Subgroup G) (hA : A ≤ Subgroup.normalizer (L : Set G)) (a : ↥A) :
    a ∈ (rhoSub L A hA).ker ↔ (a : G) ∈ centModSubgroup 3 L := by
  rw [MonoidHom.mem_ker, rhoSub_apply, rho_eq_one_iff]

theorem isElemAbelian_range {A : Subgroup G} {M : Type*} [Group M] (hA : IsElemAbelian 3 A)
    (f : ↥A →* M) : IsElemAbelian 3 f.range := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨a, ha⟩ := x.2
    obtain ⟨b, hb⟩ := y.2
    apply Subtype.ext
    show (x : M) * y = y * x
    rw [← ha, ← hb, ← map_mul, ← map_mul]
    congr 1
    exact hA.1.is_comm.comm a b
  · obtain ⟨a, rfl⟩ := hx
    rw [← map_pow]
    have : a ^ 3 = 1 := Subtype.ext (hA.2 (a : G) a.2)
    rw [this, map_one]

theorem isElemAbelian_of_le {p : ℕ} {E F : Subgroup G} (hEF : E ≤ F) (hF : IsElemAbelian p F) :
    IsElemAbelian p E := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => hF.2 x (hEF hx)⟩
  apply Subtype.ext
  have h := hF.1.is_comm.comm (⟨(x : G), hEF x.2⟩ : F) ⟨(y : G), hEF y.2⟩
  exact congrArg (fun z : ↥F => (z : G)) h

theorem card_ker_le_three {L : Subgroup G} (hCyc : CycModSylow 3 L) {A : Subgroup G}
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) (hA : IsElemAbelian 3 A) :
    Nat.card (rhoSub L A hAL).ker ≤ 3 := by
  set K : Subgroup G := (rhoSub L A hAL).ker.map A.subtype with hK
  have hKA : K ≤ A := by
    rintro _ ⟨a, -, rfl⟩
    exact a.2
  have hKel : IsElemAbelian 3 K := isElemAbelian_of_le hKA hA
  have hKcm : ∀ g ∈ K, CentMod 3 L g := by
    rintro _ ⟨a, ha, rfl⟩
    exact centMod_iff.2 ((mem_ker_rhoSub L A hAL a).1 ha)
  have hP : IsPGroup 3 K := fun g => ⟨1, Subtype.ext (by simpa using hKel.2 g.1 g.2)⟩
  have hcyc : IsCyclic K := hCyc K hKcm hP
  have h3 := card_le_of_isCyclic_of_pow Nat.prime_three hcyc (fun d hd => hKel.2 d hd)
  rwa [hK, Subgroup.card_map_of_injective A.subtype_injective] at h3

theorem card_eq_range_mul_ker (L A : Subgroup G) (hA : A ≤ Subgroup.normalizer (L : Set G)) :
    Nat.card A = Nat.card (rhoSub L A hA).range * Nat.card (rhoSub L A hA).ker := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (rhoSub L A hA).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange (rhoSub L A hA)).toEquiv] at h1
  exact h1

theorem conj_injective_of_center_eq_bot {S : Type} [Group S] (hZ : Subgroup.center S = ⊥) :
    Function.Injective (MulAut.conj : S →* MulAut S) := by
  rw [injective_iff_map_eq_one]
  intro c hc
  have hmem : c ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg := congrArg (fun φ : MulAut S => φ g) hc
    simp only [MulAut.conj_apply, MulAut.one_apply] at hg
    exact (mul_inv_eq_iff_eq_mul.1 hg).symm
  rw [hZ, Subgroup.mem_bot] at hmem
  exact hmem

theorem card_inf_inner_le {S : Type} [Group S] [Finite S] (hZ : Subgroup.center S = ⊥)
    (hA : ∀ E : Subgroup S, IsElemAbelian 3 E → Nat.card E ≤ 9) {E : Subgroup (MulAut S)}
    (hE : IsElemAbelian 3 E) : Nat.card ↥(E ⊓ innerAutS S) ≤ 9 := by
  have hinj := conj_injective_of_center_eq_bot hZ
  set E₀ : Subgroup S := (E ⊓ innerAutS S).comap (MulAut.conj : S →* MulAut S) with hE₀
  have hmap : E₀.map (MulAut.conj : S →* MulAut S) = E ⊓ innerAutS S := by
    rw [hE₀, Subgroup.map_comap_eq]
    show innerAutS S ⊓ (E ⊓ innerAutS S) = E ⊓ innerAutS S
    exact inf_eq_right.2 inf_le_right
  have hcard : Nat.card E₀ = Nat.card ↥(E ⊓ innerAutS S) := by
    rw [← hmap, Subgroup.card_map_of_injective hinj]
  have hel : IsElemAbelian 3 E₀ := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · apply Subtype.ext
      apply hinj
      have hx' : MulAut.conj (x : S) ∈ E := (Subgroup.mem_inf.1 x.2).1
      have hy' : MulAut.conj (y : S) ∈ E := (Subgroup.mem_inf.1 y.2).1
      have h := hE.1.is_comm.comm (⟨_, hx'⟩ : E) ⟨_, hy'⟩
      have h2 := congrArg (fun z : ↥E => (z : MulAut S)) h
      simpa [map_mul] using h2
    · apply hinj
      have hx' : MulAut.conj x ∈ E := (Subgroup.mem_inf.1 hx).1
      rw [map_pow, map_one]
      exact hE.2 _ hx'
  rw [← hcard]
  exact hA E₀ hel

theorem rank_bounds {L : Subgroup G} (hCyc : CycModSylow 3 L)
    (hZ : Subgroup.center (PQuot 3 L) = ⊥) (F : TD4Rank (PQuot 3 L)) {A : Subgroup G}
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) (hA : IsElemAbelian 3 A) :
    Nat.card A = Nat.card (rhoSub L A hAL).range * Nat.card (rhoSub L A hAL).ker ∧
    Nat.card (rhoSub L A hAL).ker ≤ 3 ∧
    Nat.card (rhoSub L A hAL).range ≤
      3 * Nat.card ↥((rhoSub L A hAL).range ⊓ innerAutS (PQuot 3 L)) ∧
    Nat.card ↥((rhoSub L A hAL).range ⊓ innerAutS (PQuot 3 L)) ≤ 9 := by
  have hE := isElemAbelian_range hA (rhoSub L A hAL)
  exact ⟨card_eq_range_mul_ker L A hAL, card_ker_le_three hCyc hAL hA, F.B _ hE,
    card_inf_inner_le hZ F.A hE⟩

theorem card_le_81 {L : Subgroup G} (hCyc : CycModSylow 3 L)
    (hZ : Subgroup.center (PQuot 3 L) = ⊥) (F : TD4Rank (PQuot 3 L)) {A : Subgroup G}
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) (hA : IsElemAbelian 3 A) : Nat.card A ≤ 81 := by
  obtain ⟨h1, h2, h3, h4⟩ := rank_bounds hCyc hZ F hAL hA
  rw [h1]
  calc Nat.card (rhoSub L A hAL).range * Nat.card (rhoSub L A hAL).ker
      ≤ (3 * 9) * 3 := Nat.mul_le_mul (h3.trans (Nat.mul_le_mul_left 3 h4)) h2
    _ = 81 := by norm_num

end CFSG.LocalAnalysis.GLTheoremA.I2023

end
