module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7ToolsA
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7ToolsB
import CFSG.RankThree.PartTwo.KFacts.L34Sylow

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6C

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.UniquenessMaximal

theorem isElemAbelian_of_card_nine {X : Type} [Group X] (h : IsLThreeFour X) (P : Subgroup X)
    (hP : Nat.card P = 9) : IsElemAbelian 3 P := by
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := h
  have e' : X ≃* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F :=
    (e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F).symm).trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 F)
  set P' : Subgroup (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F) :=
    P.map e'.toMonoidHom with hP'
  have hP'9 : Nat.card P' = 9 := by
    rw [← hP]
    exact Subgroup.card_map_of_injective e'.injective
  have hel := CFSG.RankThree.PartTwo.KFacts.L34.isElementaryAbelian_of_card_eq_nine hcard hP'9
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · have hmem : ∀ y : P, e' (y : X) ∈ P' := fun y => ⟨y, y.2, rfl⟩
    have h1 := mul_comm' (⟨e' (a : X), hmem a⟩ : P') ⟨e' (b : X), hmem b⟩
    have h2 : e' ((a : X) * (b : X)) = e' ((b : X) * (a : X)) := by
      rw [map_mul, map_mul]
      exact congrArg Subtype.val h1
    exact Subtype.ext (e'.injective h2)
  · have hmem : e' x ∈ P' := ⟨x, hx, rfl⟩
    have h1 := elemPow_eq_one_of_isElementaryAbelian (p := 3) (A := P') (e' x) hmem
    apply e'.injective
    rw [map_pow, h1, map_one]

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_glaPPrimeCoreOf_of_commutator_mem {N : Subgroup G}
    (hN : IsLThreeFour (↥N ⧸ GLAPPrimeCore 3 ↥N)) {a : G} (ha : a ∈ N)
    (h : ∀ g ∈ N, g * a * g⁻¹ * a⁻¹ ∈ GLAPPrimeCoreOf 3 N) : a ∈ GLAPPrimeCoreOf 3 N := by
  obtain ⟨hs, a₀, b₀, hab⟩ := isSimpleGroup_of_isLThreeFour hN
  set z : ↥N ⧸ GLAPPrimeCore 3 ↥N := QuotientGroup.mk (⟨a, ha⟩ : ↥N) with hz
  have hcomm : ∀ y : ↥N ⧸ GLAPPrimeCore 3 ↥N, y * z = z * y := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    have hg := h (g : G) g.2
    obtain ⟨c, hc, hce⟩ := hg
    have h1 : (QuotientGroup.mk (g * ⟨a, ha⟩ * g⁻¹ * ⟨a, ha⟩⁻¹ : ↥N) :
        ↥N ⧸ GLAPPrimeCore 3 ↥N) = 1 := by
      rw [QuotientGroup.eq_one_iff]
      have : (g * ⟨a, ha⟩ * g⁻¹ * ⟨a, ha⟩⁻¹ : ↥N) = c := by
        apply Subtype.ext
        have hc2 : (c : G) = (g : G) * a * (g : G)⁻¹ * a⁻¹ := hce
        rw [hc2]
        simp
      rw [this]
      exact hc
    have h2 : (QuotientGroup.mk g : ↥N ⧸ GLAPPrimeCore 3 ↥N) * z * (QuotientGroup.mk g)⁻¹ *
        z⁻¹ = 1 := by
      rw [hz, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
        ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      exact h1
    calc (QuotientGroup.mk g : ↥N ⧸ GLAPPrimeCore 3 ↥N) * z
        = (QuotientGroup.mk g * z * (QuotientGroup.mk g)⁻¹ * z⁻¹) * z *
            QuotientGroup.mk g := by group
      _ = z * QuotientGroup.mk g := by rw [h2, one_mul]
  have hcen : Subgroup.center (↥N ⧸ GLAPPrimeCore 3 ↥N) = ⊥ := by
    rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center (↥N ⧸ GLAPPrimeCore 3 ↥N)) with h0 | h0
    · exact h0
    · exfalso
      have hmem : a₀ ∈ Subgroup.center (↥N ⧸ GLAPPrimeCore 3 ↥N) := by
        rw [h0]; trivial
      exact hab ((Subgroup.mem_center_iff.1 hmem b₀).symm)
  have hz1 : z = 1 := by
    have hmem : z ∈ Subgroup.center (↥N ⧸ GLAPPrimeCore 3 ↥N) :=
      Subgroup.mem_center_iff.2 fun y => (hcomm y).symm ▸ rfl
    rw [hcen] at hmem
    exact hmem
  rw [hz, QuotientGroup.eq_one_iff] at hz1
  exact ⟨⟨a, ha⟩, hz1, rfl⟩

theorem eq_one_of_pow_three_mem_glaPPrimeCoreOf {N : Subgroup G} {a : G}
    (ha : a ∈ GLAPPrimeCoreOf 3 N) (h3 : a ^ 3 = 1) : a = 1 := by
  by_contra hne
  have hord : orderOf a = 3 := by
    refine orderOf_eq_prime h3 hne
  have hdvd : orderOf a ∣ Nat.card (GLAPPrimeCoreOf 3 N) := by
    have := Subgroup.orderOf_dvd_natCard (GLAPPrimeCoreOf 3 N) ha
    simpa using this
  rw [hord] at hdvd
  exact not_dvd_card_glaPPrimeCoreOf Nat.prime_three N hdvd

theorem card_le_nine_of_isPGroup {N S : Subgroup G} (hSN : S ≤ N) (hS : IsPGroup 3 S)
    (hN : IsLThreeFour (↥N ⧸ GLAPPrimeCore 3 ↥N)) :
    Nat.card S ≤ 9 ∧ (Nat.card S = 9 → IsElemAbelian 3 S) := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hTcard : Nat.card (barX 3 N S) = Nat.card S := card_barX_of_isPGroup hp hSN hS
  obtain ⟨k, hk⟩ := hS.exists_card_eq
  have hTp : IsPGroup 3 (barX 3 N S) := IsPGroup.of_card (hTcard.trans hk)
  obtain ⟨P, hTP⟩ := hTp.exists_le_sylow
  have hP9 : Nat.card P = 9 := by
    rw [Sylow.card_eq_multiplicity, card_eq_of_isLThreeFour hN,
      Nat.factorization_def _ hp]
    decide +kernel
  have hle : Nat.card S ≤ 9 := by
    rw [← hTcard, ← hP9]
    exact Subgroup.card_le_of_le hTP
  refine ⟨hle, fun h9 => ?_⟩
  have hTeq : barX 3 N S = (P : Subgroup (↥N ⧸ GLAPPrimeCore 3 ↥N)) :=
    Subgroup.eq_of_le_of_card_ge hTP (by rw [hTcard, h9, hP9])
  have hel : IsElemAbelian 3 (barX 3 N S) := by
    rw [hTeq]
    exact isElemAbelian_of_card_nine hN _ hP9
  have hinj := injective_barX_comp hp hS hSN
  set f := (QuotientGroup.mk' (GLAPPrimeCore 3 ↥N)).comp (S.subgroupOf N).subtype with hf
  have hmem : ∀ y : ↥(S.subgroupOf N), f y ∈ barX 3 N S := fun y => ⟨y, y.2, rfl⟩
  have := hel.1
  have hSN' : IsElemAbelian 3 (S.subgroupOf N) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
    · have h1 := mul_comm' (⟨f a, hmem a⟩ : barX 3 N S) ⟨f b, hmem b⟩
      have h2 : f (a * b) = f (b * a) := by
        rw [map_mul, map_mul]
        exact congrArg Subtype.val h1
      exact hinj h2
    · have h1 : f ⟨y, hy⟩ ^ 3 = 1 := hel.2 (f ⟨y, hy⟩) (hmem ⟨y, hy⟩)
      have h2 : (⟨y, hy⟩ : ↥(S.subgroupOf N)) ^ 3 = 1 := by
        apply hinj
        rw [map_pow, h1, map_one]
      exact congrArg Subtype.val h2
  have := hSN'.1
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · have ha : (a : G) ∈ S := a.2
    have hb : (b : G) ∈ S := b.2
    have h1 := mul_comm' (⟨⟨a, hSN a.2⟩, (Subgroup.mem_subgroupOf).2 ha⟩ : ↥(S.subgroupOf N))
      ⟨⟨b, hSN b.2⟩, (Subgroup.mem_subgroupOf).2 hb⟩
    have := congrArg (fun t : ↥(S.subgroupOf N) => ((t : ↥N) : G)) h1
    exact Subtype.ext this
  · have h1 := hSN'.2 ⟨x, hSN hx⟩ ((Subgroup.mem_subgroupOf).2 hx)
    have := congrArg (fun t : ↥N => (t : G)) h1
    simpa using this

end CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6C
