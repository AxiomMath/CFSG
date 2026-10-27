module

public import CFSG.GH74.E2.FrattiniRank
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.AS16.E2

open Subgroup

theorem exists_decomp_of_inner {G : Type*} [Group G] {T L : Subgroup G}
    (hT : IsPGroup 2 T)
    (hZ : ∀ l ∈ L, (∀ x ∈ L, l * x = x * l) → l = 1)
    (hsyl : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ L → T ⊓ L ≤ P → P = T ⊓ L)
    (hinn : ∀ t ∈ T, ∃ l ∈ L, ∀ x ∈ L, t * x * t⁻¹ = l * x * l⁻¹) :
    ∀ t ∈ T, ∃ s ∈ T ⊓ L, ∃ c ∈ T ⊓ centralizer (L : Set G), t = s * c := by
  classical
  let Ts : Subgroup G :=
    { carrier := {l | l ∈ L ∧ ∃ t ∈ T, ∀ x ∈ L, t * x * t⁻¹ = l * x * l⁻¹}
      mul_mem' := by
        rintro a b ⟨haL, t1, ht1, h1⟩ ⟨hbL, t2, ht2, h2⟩
        refine ⟨L.mul_mem haL hbL, t1 * t2, T.mul_mem ht1 ht2, fun x hx => ?_⟩
        have hb : b * x * b⁻¹ ∈ L := L.mul_mem (L.mul_mem hbL hx) (L.inv_mem hbL)
        calc t1 * t2 * x * (t1 * t2)⁻¹ = t1 * (t2 * x * t2⁻¹) * t1⁻¹ := by group
          _ = t1 * (b * x * b⁻¹) * t1⁻¹ := by rw [h2 x hx]
          _ = a * (b * x * b⁻¹) * a⁻¹ := h1 _ hb
          _ = a * b * x * (a * b)⁻¹ := by group
      one_mem' := ⟨L.one_mem, 1, T.one_mem, fun x _ => by simp⟩
      inv_mem' := by
        rintro a ⟨haL, t, ht, h⟩
        refine ⟨L.inv_mem haL, t⁻¹, T.inv_mem ht, fun x hx => ?_⟩
        have hx' : a⁻¹ * x * a ∈ L := L.mul_mem (L.mul_mem (L.inv_mem haL) hx) haL
        have h1 := h _ hx'
        have h2 : t * (a⁻¹ * x * a) * t⁻¹ = x := by rw [h1]; group
        have h3 : t⁻¹ * x * t = a⁻¹ * x * a := by
          calc t⁻¹ * x * t = t⁻¹ * (t * (a⁻¹ * x * a) * t⁻¹) * t := by rw [h2]
            _ = a⁻¹ * x * a := by group
        simpa using h3 }
  have hmem : ∀ a, a ∈ Ts ↔ a ∈ L ∧ ∃ t ∈ T, ∀ x ∈ L, t * x * t⁻¹ = a * x * a⁻¹ :=
    fun a => Iff.rfl
  have hTs2 : IsPGroup 2 Ts := by
    rintro ⟨a, ha⟩
    obtain ⟨haL, t, ht, h⟩ := (hmem a).1 ha
    obtain ⟨k, hk⟩ := hT ⟨t, ht⟩
    have hk' : t ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hpow : ∀ j : ℕ, ∀ x ∈ L, t ^ j * x * (t ^ j)⁻¹ = a ^ j * x * (a ^ j)⁻¹ := by
      intro j
      induction j with
      | zero => intro x _; simp
      | succ j ih =>
        intro x hx
        have hy : a ^ j * x * (a ^ j)⁻¹ ∈ L :=
          L.mul_mem (L.mul_mem (L.pow_mem haL j) hx) (L.inv_mem (L.pow_mem haL j))
        calc t ^ (j + 1) * x * (t ^ (j + 1))⁻¹
            = t * (t ^ j * x * (t ^ j)⁻¹) * t⁻¹ := by group
          _ = t * (a ^ j * x * (a ^ j)⁻¹) * t⁻¹ := by rw [ih x hx]
          _ = a * (a ^ j * x * (a ^ j)⁻¹) * a⁻¹ := h _ hy
          _ = a ^ (j + 1) * x * (a ^ (j + 1))⁻¹ := by group
    refine ⟨k, Subtype.ext ?_⟩
    have hcen : ∀ x ∈ L, a ^ 2 ^ k * x = x * a ^ 2 ^ k := by
      intro x hx
      have := hpow (2 ^ k) x hx
      rw [hk'] at this
      simp only [one_mul, inv_one, mul_one] at this
      calc a ^ 2 ^ k * x = (a ^ 2 ^ k * x * (a ^ 2 ^ k)⁻¹) * a ^ 2 ^ k := by group
        _ = x * a ^ 2 ^ k := by rw [← this]
    exact hZ _ (L.pow_mem haL _) hcen
  have hTsL : Ts ≤ L := fun a ha => ((hmem a).1 ha).1
  have hle : T ⊓ L ≤ Ts := fun s hs => (hmem s).2 ⟨hs.2, s, hs.1, fun x _ => rfl⟩
  have hEq : Ts = T ⊓ L := hsyl Ts hTs2 hTsL hle
  intro t ht
  obtain ⟨l, hlL, h⟩ := hinn t ht
  have hl : l ∈ T ⊓ L := hEq ▸ (hmem l).2 ⟨hlL, t, ht, h⟩
  have hc : l⁻¹ * t ∈ centralizer (L : Set G) := by
    refine Subgroup.mem_centralizer_iff.2 fun x hx => ?_
    have h1 := h x hx
    calc x * (l⁻¹ * t) = l⁻¹ * (l * x * l⁻¹) * t := by group
      _ = l⁻¹ * (t * x * t⁻¹) * t := by rw [h1]
      _ = l⁻¹ * t * x := by group
  exact ⟨l, hl, l⁻¹ * t, ⟨T.mul_mem (T.inv_mem hl.1) ht, hc⟩, by group⟩

theorem isCyclic_of_rank_le_one {X : Type*} [Group X] [Finite X] (h : Group.rank X ≤ 1) :
    IsCyclic X := by
  obtain ⟨S, hS, hcl⟩ := Group.rank_spec (G := X)
  have hcard : S.card ≤ 1 := hS ▸ h
  rcases Finset.card_le_one_iff_subset_singleton.mp hcard with ⟨g, hg⟩
  refine ⟨⟨g, fun x => ?_⟩⟩
  have hx : x ∈ Subgroup.closure (S : Set X) := by rw [hcl]; trivial
  have hsub : Subgroup.closure (S : Set X) ≤ Subgroup.zpowers g := by
    rw [Subgroup.closure_le]
    intro y hy
    have := hg hy
    rw [Finset.mem_singleton] at this
    rw [this]
    exact Subgroup.mem_zpowers g
  exact hsub hx

theorem cyclic_pow_two_eq_one {X : Type*} [Group X] [Finite X] [IsCyclic X] {z c : X}
    (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1) (hc2 : c ^ 2 = 1) : c = 1 ∨ c = z := by
  classical
  have := Fintype.ofFinite X
  have hle := IsCyclic.card_pow_eq_one_le (α := X) (n := 2) (by norm_num)
  by_contra hcon
  push Not at hcon
  obtain ⟨hc1, hcz⟩ := hcon
  have hsub : ({1, z, c} : Finset X) ⊆ Finset.univ.filter (fun a : X => a ^ 2 = 1) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases ha with rfl | rfl | rfl
    · simp
    · exact hz2
    · exact hc2
  have h3 : ({1, z, c} : Finset X).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simpa using Ne.symm hcz
    · simp [Ne.symm hz1, Ne.symm hc1]
  have := Finset.card_le_card hsub
  omega

theorem cyclic_mul_comm {X : Type*} [Group X] [IsCyclic X] (a b : X) : a * b = b * a :=
  (IsCyclic.commGroup (α := X)).mul_comm a b


theorem rank_le_one_of_gen4 {G : Type} [Group G] [Finite G] (hG : CFSG.GH74.Gen4 G)
    {U C : Subgroup G} (hU : IsPGroup 2 U) (hC : IsPGroup 2 C)
    (hcomm : ∀ u ∈ U, ∀ c ∈ C, u * c = c * u) (hUC : U ⊓ C = ⊥) (hr : 3 ≤ Group.rank U) :
    Group.rank C ≤ 1 := by
  have h := CFSG.GH74.E2.gen4_rank_add_le hG U C hU hC hcomm
  have h0 : Group.rank ↥(U ⊓ C) = 0 := by
    have hbot := (Subgroup.eq_bot_iff_forall _).1 hUC
    have : Subsingleton ↥(U ⊓ C) :=
      ⟨fun a b => Subtype.ext ((hbot a a.2).trans (hbot b b.2).symm)⟩
    exact Group.rank_eq_zero ↥(U ⊓ C)
  omega

end CFSG.GH74.AS16.E2
