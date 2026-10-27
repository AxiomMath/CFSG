module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreMultiplicity

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Subgroup
open scoped commutatorElement

theorem i227rk_hom_eq_one_of_solvable {K H : Type*} [Group K] [Group H] (hK : commutator K = ⊤)
    [Group.IsSolvable H] (f : K →* H) (k : K) : f k = 1 := by
  have hder : ∀ n, derivedSeries K n = ⊤ := by
    intro n
    induction n with
    | zero => exact derivedSeries_zero K
    | succ n ih => rw [derivedSeries_succ, ih]; exact hK
  obtain ⟨n, hn⟩ := Group.IsSolvable.solvable (G := H)
  have hle := map_derivedSeries_le_derivedSeries f n
  rw [hder n, hn] at hle
  exact Subgroup.mem_bot.mp (hle (Subgroup.mem_map_of_mem f (Subgroup.mem_top k)))

theorem i227rk_three_mul_le_card {G : Type*} [Group G] [Finite G] (hG : IsPGroup 3 G)
    {A B : Subgroup G} (hAB : A ≤ B) (hne : A ≠ B) : 3 * Nat.card A ≤ Nat.card B := by
  obtain ⟨a, ha⟩ := (hG.to_subgroup A).exists_card_eq
  obtain ⟨b, hb⟩ := (hG.to_subgroup B).exists_card_eq
  have hlt : Nat.card A < Nat.card B := by
    rcases (Subgroup.card_le_of_le hAB).lt_or_eq with h | h
    · exact h
    · exact absurd (Subgroup.eq_of_le_of_card_ge hAB h.ge) hne
  rw [ha, hb] at hlt ⊢
  have hab : a < b := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt
  calc 3 * 3 ^ a = 3 ^ (a + 1) := by ring
    _ ≤ 3 ^ b := Nat.pow_le_pow_right (by norm_num) hab

theorem i227rk_index_centralizer_le {G : Type*} [Group G] [Finite G]
    (hcomm : ∀ x y : G, ⁅x, y⁆ ∈ Subgroup.center G) (x : G) :
    (Subgroup.centralizer ({x} : Set G)).index ≤ Nat.card (Subgroup.center G) := by
  let φ : G →* Subgroup.center G :=
    { toFun := fun g => ⟨⁅x, g⁆, hcomm x g⟩
      map_one' := by ext; simp
      map_mul' := fun g h => by
        ext
        have hz := Subgroup.mem_center_iff.mp (hcomm x h)
        have hz' := hz g⁻¹
        simp only [Subgroup.coe_mul, commutatorElement_def] at hz' ⊢
        calc x * (g * h) * x⁻¹ * (g * h)⁻¹
            = x * g * x⁻¹ * (x * h * x⁻¹ * h⁻¹) * g⁻¹ := by group
          _ = x * g * x⁻¹ * (g⁻¹ * (x * h * x⁻¹ * h⁻¹)) := by rw [mul_assoc _ (x * h * x⁻¹ * h⁻¹) g⁻¹, ← hz']
          _ = x * g * x⁻¹ * g⁻¹ * (x * h * x⁻¹ * h⁻¹) := by group }
  have hker : φ.ker = Subgroup.centralizer ({x} : Set G) := by
    ext g
    simp only [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff,
      forall_eq]
    constructor
    · intro h
      have h' := congrArg Subtype.val h
      simp only [φ, MonoidHom.coe_mk, OneHom.coe_mk, commutatorElement_def,
        OneMemClass.coe_one] at h'
      calc x * g = (x * g * x⁻¹ * g⁻¹) * (g * x) := by group
        _ = g * x := by rw [h']; simp
    · intro h
      ext
      simp only [φ, MonoidHom.coe_mk, OneHom.coe_mk, commutatorElement_def,
        OneMemClass.coe_one]
      rw [h]; group
  rw [← hker, Subgroup.index_ker]
  exact Subgroup.card_le_card_group _

theorem i227rk_center_quotient_card_le {G : Type*} [Group G] [Finite G]
    (hexp : ∀ x : G, x ^ 3 = 1) (hcomm : ∀ x y : G, ⁅x, y⁆ ∈ Subgroup.center G)
    (hab : ∀ B : Subgroup G, IsMulCommutative B → Nat.card B ≤ 9) :
    Nat.card (Subgroup.center G) ≤ 9 ∧ Nat.card (G ⧸ Subgroup.center G) ≤ 9 := by
  have hG : IsPGroup 3 G := fun g => ⟨1, by simpa using hexp g⟩
  refine ⟨hab _ inferInstance, ?_⟩
  show (Subgroup.center G).index ≤ 9
  by_cases hZ : Subgroup.center G = ⊤
  · rw [hZ, Subgroup.index_top]; norm_num
  obtain ⟨x, hx⟩ : ∃ x : G, x ∉ Subgroup.center G := by
    by_contra h
    push Not at h
    exact hZ ((Subgroup.eq_top_iff' _).mpr h)
  have hxc : ∀ z ∈ Subgroup.center G, Commute x z := fun z hz =>
    (Subgroup.mem_center_iff.mp hz x)
  have hnt : Nontrivial G := ⟨⟨x, 1, fun h => hx (h ▸ Subgroup.one_mem _)⟩⟩
  have hZne : Subgroup.center G ≠ ⊥ := by
    have := hG.center_nontrivial
    exact (Subgroup.nontrivial_iff_ne_bot _).mp this
  have hZ3 : 3 ≤ Nat.card (Subgroup.center G) := by
    have := i227rk_three_mul_le_card hG (bot_le : (⊥ : Subgroup G) ≤ center G) hZne.symm
    simpa using this
  set B1 : Subgroup G := Subgroup.closure (insert x (Subgroup.center G : Set G)) with hB1
  have hB1comm : IsMulCommutative B1 := by
    apply Subgroup.isMulCommutative_closure
    intro a ha b hb _
    rcases ha with rfl | ha
    · rcases hb with rfl | hb
      · exact Commute.refl _
      · exact hxc b hb
    · rcases hb with rfl | hb
      · exact (hxc a ha).symm
      · exact (Subgroup.mem_center_iff.mp hb a)
  have hZB1 : Subgroup.center G ≤ B1 := fun z hz =>
    Subgroup.subset_closure (Set.mem_insert_of_mem _ hz)
  have hxB1 : x ∈ B1 := Subgroup.subset_closure (Set.mem_insert _ _)
  have hB1ne : Subgroup.center G ≠ B1 := fun h => hx (h ▸ hxB1)
  have h3B1 := i227rk_three_mul_le_card hG hZB1 hB1ne
  have hB1card := hab B1 hB1comm
  have hB1ge : 9 ≤ Nat.card B1 := by omega
  have hCle : Subgroup.centralizer ({x} : Set G) ≤ B1 := by
    intro y hy
    by_contra hyB1
    set B2 : Subgroup G := Subgroup.closure (insert y (insert x (Subgroup.center G : Set G)))
      with hB2
    have hyx : Commute y x := Subgroup.mem_centralizer_singleton_iff.mp hy
    have hB2comm : IsMulCommutative B2 := by
      apply Subgroup.isMulCommutative_closure
      intro a ha b hb _
      have hz : ∀ c ∈ insert x (Subgroup.center G : Set G), Commute y c := by
        intro c hc
        rcases hc with rfl | hc
        · exact hyx
        · exact (Subgroup.mem_center_iff.mp hc y)
      have hz' : ∀ c ∈ insert x (Subgroup.center G : Set G), ∀ d ∈ insert x
          (Subgroup.center G : Set G), Commute c d := by
        intro c hc d hd
        rcases hc with rfl | hc
        · rcases hd with rfl | hd
          · exact Commute.refl _
          · exact hxc d hd
        · rcases hd with rfl | hd
          · exact (hxc c hc).symm
          · exact (Subgroup.mem_center_iff.mp hd c)
      rcases ha with rfl | ha
      · rcases hb with rfl | hb
        · exact Commute.refl _
        · exact hz b hb
      · rcases hb with rfl | hb
        · exact (hz a ha).symm
        · exact hz' a ha b hb
    have hB12 : B1 ≤ B2 := Subgroup.closure_mono (Set.subset_insert _ _)
    have hyB2 : y ∈ B2 := Subgroup.subset_closure (Set.mem_insert _ _)
    have hne : B1 ≠ B2 := fun h => hyB1 (h ▸ hyB2)
    have h3 := i227rk_three_mul_le_card hG hB12 hne
    have := hab B2 hB2comm
    omega
  have hC9 : Nat.card (Subgroup.centralizer ({x} : Set G)) ≤ 9 :=
    (Subgroup.card_le_of_le hCle).trans hB1card
  have hidx := i227rk_index_centralizer_le hcomm x
  have hGC := Subgroup.card_mul_index (Subgroup.centralizer ({x} : Set G))
  have hGZ := Subgroup.card_mul_index (Subgroup.center G)
  have hpos : 0 < Nat.card (Subgroup.center G) := Nat.card_pos
  have hle : Nat.card (Subgroup.center G) * (Subgroup.center G).index ≤
      Nat.card (Subgroup.center G) * 9 := by
    rw [hGZ, ← hGC]
    calc Nat.card (Subgroup.centralizer ({x} : Set G)) *
          (Subgroup.centralizer ({x} : Set G)).index
        ≤ 9 * Nat.card (Subgroup.center G) := Nat.mul_le_mul hC9 hidx
      _ = Nat.card (Subgroup.center G) * 9 := by ring
  exact Nat.le_of_mul_le_mul_left hle hpos

theorem i227rk_small_factorization {M : Type*} [Group M] [Finite M] (hM : IsPGroup 3 M)
    (hc : Nat.card M ≤ 9) :
    (Nat.card M).factorization 3 ≤ 2 ∧
      ∀ p : ℕ, p.Prime → p ≠ 3 → (Nat.card M).factorization p ≤ 1 := by
  obtain ⟨a, ha⟩ := hM.exists_card_eq
  have ha2 : a ≤ 2 := by
    rw [ha] at hc
    by_contra h
    push Not at h
    have : 3 ^ 3 ≤ 3 ^ a := Nat.pow_le_pow_right (by norm_num) h
    omega
  rw [ha, Nat.factorization_pow, Nat.prime_three.factorization]
  refine ⟨by simpa using ha2, fun p _ hp => ?_⟩
  simp [Ne.symm hp]

theorem i227rk_mulAut_solvable {G : Type*} [Group G] [Finite G]
    (hexp : ∀ x : G, x ^ 3 = 1) (hcomm : ∀ x y : G, ⁅x, y⁆ ∈ Subgroup.center G)
    (hab : ∀ B : Subgroup G, IsMulCommutative B → Nat.card B ≤ 9) :
    Group.IsSolvable (MulAut G) := by
  obtain ⟨h1, h2⟩ := i227rk_center_quotient_card_le hexp hcomm hab
  have hG : IsPGroup 3 G := fun g => ⟨1, by simpa using hexp g⟩
  have hZ : Group.IsSolvable (MulAut (Subgroup.center G)) := by
    obtain ⟨f1, f2⟩ := i227rk_small_factorization (hG.to_subgroup (Subgroup.center G)) h1
    exact CFSG.ComponentClassification.CatalogueBHeldSmallCore.small_prime_multiplicity_solvable_automorphisms
      _ f1 f2
  have hQ : Group.IsSolvable (MulAut (G ⧸ Subgroup.center G)) := by
    have hQp : IsPGroup 3 (G ⧸ Subgroup.center G) := hG.to_quotient _
    obtain ⟨f1, f2⟩ := i227rk_small_factorization hQp h2
    have : Group.IsNilpotent (G ⧸ Subgroup.center G) := hQp.isNilpotent
    exact CFSG.ComponentClassification.CatalogueBHeldSmallCore.small_prime_multiplicity_solvable_automorphisms
      _ f1 f2
  exact CFSG.ComponentClassification.CatalogueBHeldSmallCore.automorphism_solvable_of_sections
    (Subgroup.center G)

end CFSG.HardMathSupport.Solomon.Coordinator
