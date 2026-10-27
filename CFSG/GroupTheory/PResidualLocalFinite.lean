module

public import CFSG.Quasithin.Background.A1cBridge
public import CFSG.Quasithin.Background.G6Basic
import CFSG.GroupTheory.PResidualNormalizer
import CFSG.Holt.General.OrbitCountBasic

public section

namespace CFSG.GroupTheory

open CFSG.Quasithin

variable {G : Type*} [Group G]

theorem pResidualOf_mono {p : ℕ} {A B : Subgroup G} (hAB : A ≤ B) :
    pResidualOf p A ≤ pResidualOf p B := by
  intro x hx
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
  refine Subgroup.mem_map.mpr ⟨⟨(a : G), hAB a.2⟩, ?_, rfl⟩
  unfold pResidual at ha ⊢
  simp only [Subgroup.mem_iInf] at ha ⊢
  intro N hN hNk
  let f : ↥A →* ↥B :=
    { toFun := fun y => ⟨(y : G), hAB y.2⟩, map_one' := Subtype.ext rfl,
      map_mul' := fun x y => Subtype.ext rfl }
  have hN' : (N.comap f).Normal := inferInstance
  have hk' : ∀ y : ↥A, ∃ k : ℕ, y ^ p ^ k ∈ N.comap f := by
    intro y
    obtain ⟨k, hk⟩ := hNk (f y)
    exact ⟨k, by rw [Subgroup.mem_comap]; simpa only [map_pow] using hk⟩
  exact ha (N.comap f) hN' hk'

theorem pResidual_map_of_surjective {X Y : Type*} [Group X] [Group Y] [Finite X] (p : ℕ)
    (f : X →* Y) (hf : Function.Surjective f) : (pResidual p X).map f = pResidual p Y := by
  haveI : Finite Y := Finite.of_surjective f hf
  haveI : (pResidual p Y).Normal := CFSG.Quasithin.G6.pResidual_normal_aux p
  haveI : ((pResidual p X).map f).Normal :=
    (CFSG.Quasithin.G6.pResidual_normal_aux p).map f hf
  refine le_antisymm ?_ ?_
  · rw [Subgroup.map_le_iff_le_comap]
    refine CFSG.Quasithin.pResidual_le (N := (pResidual p Y).comap f) fun x => ?_
    obtain ⟨k, hk⟩ := CFSG.Quasithin.G6.exists_pow_mem_pResidual p (f x)
    exact ⟨k, by rw [Subgroup.mem_comap, map_pow]; exact hk⟩
  · refine CFSG.Quasithin.pResidual_le (N := (pResidual p X).map f) fun y => ?_
    obtain ⟨x, rfl⟩ := hf y
    obtain ⟨k, hk⟩ := CFSG.Quasithin.G6.exists_pow_mem_pResidual p x
    exact ⟨k, Subgroup.mem_map.mpr ⟨x ^ p ^ k, hk, map_pow f x (p ^ k)⟩⟩

theorem pResidualOf_map_of_surjective {X Y : Type*} [Group X] [Group Y] [Finite X] (p : ℕ)
    (f : X →* Y) (hf : Function.Surjective f) (A : Subgroup X) :
    (pResidualOf p A).map f = pResidualOf p (A.map f) := by
  haveI : Finite ↥A := .of_injective A.subtype A.subtype_injective
  haveI : Finite Y := .of_surjective f hf
  let g : ↥A →* ↥(A.map f) := f.subgroupMap A
  have hg : Function.Surjective g := by
    rintro ⟨y, hy⟩
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hy
    exact ⟨⟨a, ha⟩, Subtype.ext rfl⟩
  have hres := pResidual_map_of_surjective p g hg
  have hcomp : (A.map f).subtype.comp g = f.comp A.subtype := by
    ext a
    rfl
  have h := congrArg (Subgroup.map (A.map f).subtype) hres
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map] at h
  exact h

theorem pResidualOf_normal {p : ℕ} {A : Subgroup G} (hA : A.Normal) :
    (pResidualOf p A).Normal := by
  haveI : A.Normal := hA
  haveI : (pResidual p ↥A).Characteristic := CFSG.Quasithin.pResidual_characteristic p ↥A
  exact ConjAct.normal_of_characteristic_of_normal (H := A) (K := pResidual p ↥A)

theorem le_pResidualOf_of_perfect [Finite G] {p : ℕ} [Fact p.Prime] {A N : Subgroup G}
    (hN : ⁅N, N⁆ = N) (hNA : N ≤ A) : N ≤ CFSG.Quasithin.pResidualOf p A := by
  haveI : Finite ↥A := .of_injective A.subtype A.subtype_injective
  refine CFSG.Holt.General.le_of_isPerfect_of_forall_pow_mem (p := p) hN ?_ ?_
  · exact hNA.trans ((Subgroup.le_normalizer (H := A)).trans
      (CFSG.Quasithin.normalizer_le_normalizer_pResidualOf p A))
  · intro g hg
    obtain ⟨k, hk⟩ := CFSG.Quasithin.G6.exists_pow_mem_pResidual p (⟨g, hNA hg⟩ : ↥A)
    exact ⟨k, Subgroup.mem_map.mpr ⟨(⟨g, hNA hg⟩ : ↥A) ^ p ^ k, hk, by simp⟩⟩

theorem pResidualOf_top_eq_subgroupOf {X : Subgroup G} [Finite ↥X] {p : ℕ} :
    pResidualOf p (⊤ : Subgroup ↥X) = (pResidualOf p X).subgroupOf X := by
  have htop : pResidualOf p (⊤ : Subgroup ↥X) = CFSG.Quasithin.pResidual p ↥X :=
    pResidual_map_of_surjective p _ fun x => ⟨⟨x, trivial⟩, rfl⟩
  rw [htop, pResidualOf]
  exact (Subgroup.comap_map_eq_self_of_injective X.subtype_injective
    (CFSG.Quasithin.pResidual p ↥X)).symm

theorem exists_pow_mem_opResidual_of_finite {H : Subgroup G} [Finite ↥H] {p : ℕ}
    [hp : Fact p.Prime] {x : G} (hx : x ∈ H) : ∃ k : ℕ, x ^ p ^ k ∈ opResidual p H := by
  have hxpos : 0 < orderOf x :=
    (Subgroup.orderOf_coe (⟨x, hx⟩ : ↥H)) ▸ orderOf_pos (⟨x, hx⟩ : ↥H)
  obtain ⟨k, m, hm, hdecomp⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd hxpos.ne' p hp.out.ne_one
  refine ⟨k, mem_opResidual_of_coprime (H.pow_mem hx _) ?_⟩
  rw [orderOf_pow_of_dvd (pow_ne_zero k hp.out.ne_zero) ⟨m, hdecomp⟩, hdecomp,
    Nat.mul_div_cancel_left _ (pow_pos hp.out.pos k)]
  exact ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hm).symm

theorem pResidualOf_le_opResidual_of_finite {H : Subgroup G} [Finite ↥H] {p : ℕ}
    [Fact p.Prime] : pResidualOf p H ≤ opResidual p H := by
  have hN : ((opResidual p H).subgroupOf H).Normal := opResidual_normal p H
  rw [pResidualOf, Subgroup.map_le_iff_le_comap]
  refine pResidual_le (p := p) (N := (opResidual p H).subgroupOf H) fun x => ?_
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (x : G) ^ p ^ k ∈ opResidual p H :=
    exists_pow_mem_opResidual_of_finite (p := p) (H := H) x.2
  exact ⟨k, Subgroup.mem_subgroupOf.mpr hk⟩

theorem pResidualOf_eq_opResidual_of_finite {H : Subgroup G} [Finite ↥H] {p : ℕ}
    [Fact p.Prime] : pResidualOf p H = opResidual p H :=
  le_antisymm pResidualOf_le_opResidual_of_finite (CFSG.Quasithin.opResidual_le_pResidualOf H)

theorem opResidual_sup_eq_of_finite {C T : Subgroup G} [Finite ↥C]
    (hTC : T ≤ C) (hodd : ¬ 2 ∣ T.relIndex C) : opResidual 2 C ⊔ T = C := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := opResidual 2 C with hX
  have hXC : X ≤ C := opResidual_le 2 C
  have h2pow : ∃ m : ℕ, X.relIndex C = 2 ^ m := by
    have : (X.subgroupOf C).Normal := opResidual_normal 2 C
    have hp : IsPGroup 2 (↥C ⧸ X.subgroupOf C) := by
      intro g
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
      obtain ⟨k, hk⟩ : ∃ k : ℕ, (g : G) ^ 2 ^ k ∈ opResidual 2 C :=
        exists_pow_mem_opResidual_of_finite (p := 2) (H := C) g.2
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      simpa [hX] using hk
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hp
    exact ⟨m, by rw [Subgroup.relIndex, Subgroup.index, hm]⟩
  refine le_antisymm (sup_le hXC hTC) ?_
  have h1 : (X ⊔ T).relIndex C ∣ T.relIndex C := Subgroup.relIndex_dvd_of_le_left _ le_sup_right
  have h2 : (X ⊔ T).relIndex C ∣ X.relIndex C := Subgroup.relIndex_dvd_of_le_left _ le_sup_left
  obtain ⟨m, hm⟩ := h2pow
  rw [hm] at h2
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
  have : (X ⊔ T).relIndex C = 1 := by
    rcases j with _ | j
    · simpa using hj
    · exfalso
      apply hodd
      rw [hj] at h1
      exact (dvd_pow_self 2 (Nat.succ_ne_zero j)).trans h1
  exact Subgroup.relIndex_eq_one.mp this

end CFSG.GroupTheory
