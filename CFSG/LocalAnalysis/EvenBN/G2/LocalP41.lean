module

public import CFSG.LocalAnalysis.EvenBN.G2.LocalP40

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.LocalAnalysis.EvenBN.Common (CosetData)
open scoped commutatorElement Pointwise

section H6

open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient

variable {G : Type*} [Group G] [Finite G]

theorem exists_mem_commutator_mem_of_ne {P N N₀ : Subgroup G} (hP : IsPGroup 2 P)
    (hN₀N : N₀ ≤ N) (hNP : N ≤ P) (hPN₀ : P ≤ normalizer (N₀ : Set G))
    (hPN : P ≤ normalizer (N : Set G)) (hne : N₀ ≠ N) :
    ∃ x ∈ N, x ∉ N₀ ∧ ∀ g ∈ P, x * g * x⁻¹ * g⁻¹ ∈ N₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbar : bar N₀ N ≠ ⊥ := by
    intro h0
    refine hne (le_antisymm hN₀N fun x hx => ?_)
    have h1 : proj N₀ ⟨x, hPN₀ (hNP hx)⟩ ∈ bar N₀ N := proj_mem_bar hx
    rw [h0, Subgroup.mem_bot] at h1
    exact proj_eq_one_iff.1 h1
  obtain ⟨xb, hxbN, hxb1, hxbC⟩ := exists_ne_one_mem_centralizer_of_le (p := 2)
    (isPGroup_bar hP : IsPGroup 2 (bar N₀ P)) (bar_mono hNP)
    (bar_le_normalizer_bar hN₀N hPN) hbar
  obtain ⟨x, rfl⟩ := proj_surjective xb
  refine ⟨x, (mem_bar_iff hN₀N x).1 hxbN, fun hx => hxb1 (proj_eq_one_iff.2 hx), fun g hg => ?_⟩
  have hgN : g ∈ normalizer (N₀ : Set G) := hPN₀ hg
  have h1 := mem_centralizer_iff.1 hxbC (proj N₀ ⟨g, hgN⟩) (proj_mem_bar hg)
  have h2 := proj_eq_proj_iff.1 h1
  have h3 : (x : G)⁻¹ * g⁻¹ * x * g ∈ N₀ := by
    simpa [mul_assoc] using h2
  have h4 : ((g : G) * x) * ((x : G)⁻¹ * g⁻¹ * x * g) * ((g : G) * x)⁻¹ ∈ N₀ :=
    (mem_normalizer_iff.1 (mul_mem hgN x.2) _).1 h3
  have e : (x : G) * g * (x : G)⁻¹ * g⁻¹ =
      ((g : G) * x) * ((x : G)⁻¹ * g⁻¹ * x * g) * ((g : G) * x)⁻¹ := by group
  rw [e]
  exact h4

theorem commutator_le_of_irreducible {P N N₀ J : Subgroup G} (hP : IsPGroup 2 P)
    (hN₀N : N₀ ≤ N) (hNP : N ≤ P) (hPN₀ : P ≤ normalizer (N₀ : Set G))
    (hPN : P ≤ normalizer (N : Set G))
    (hJ : J ≤ normalizer (P : Set G) ⊓ normalizer (N : Set G) ⊓ normalizer (N₀ : Set G))
    (hirr : ∀ A : Subgroup G, N₀ ≤ A → A ≤ N → J ≤ normalizer (A : Set G) → A = N₀ ∨ A = N)
    (hne : N₀ ≠ N) : ∀ x ∈ N, ∀ g ∈ P, x * g * x⁻¹ * g⁻¹ ∈ N₀ := by
  obtain ⟨x₀, hx₀N, hx₀, hx₀c⟩ := exists_mem_commutator_mem_of_ne hP hN₀N hNP hPN₀ hPN hne
  let A : Subgroup G :=
    { carrier := {x | x ∈ N ∧ ∀ g ∈ P, x * g * x⁻¹ * g⁻¹ ∈ N₀}
      one_mem' := ⟨one_mem _, fun g _ => by simp⟩
      mul_mem' := fun {x y} hx hy => by
        refine ⟨mul_mem hx.1 hy.1, fun g hg => ?_⟩
        have h1 : x * (y * g * y⁻¹ * g⁻¹) * x⁻¹ ∈ N₀ :=
          (mem_normalizer_iff.1 (hPN₀ (hNP hx.1)) _).1 (hy.2 g hg)
        have e : x * y * g * (x * y)⁻¹ * g⁻¹ =
            x * (y * g * y⁻¹ * g⁻¹) * x⁻¹ * (x * g * x⁻¹ * g⁻¹) := by group
        rw [e]
        exact mul_mem h1 (hx.2 g hg)
      inv_mem' := fun {x} hx => by
        refine ⟨inv_mem hx.1, fun g hg => ?_⟩
        have h1 := hx.2 (x⁻¹ * g * x) (mul_mem (mul_mem (inv_mem (hNP hx.1)) hg) (hNP hx.1))
        have e : x⁻¹ * g * x⁻¹⁻¹ * g⁻¹ =
            (x * (x⁻¹ * g * x) * x⁻¹ * (x⁻¹ * g * x)⁻¹)⁻¹ := by group
        rw [e]
        exact inv_mem h1 }
  have hN₀A : N₀ ≤ A := fun x hx => by
    refine ⟨hN₀N hx, fun g hg => ?_⟩
    have := (mem_normalizer_iff.1 (hPN₀ hg) x⁻¹).1 (inv_mem hx)
    have e : x * g * x⁻¹ * g⁻¹ = x * (g * x⁻¹ * g⁻¹) := by group
    rw [e]
    exact mul_mem hx this
  have hJA : J ≤ normalizer (A : Set G) := fun j hj => by
    obtain ⟨⟨hjP, hjN⟩, hjN₀⟩ := Subgroup.mem_inf.1 (hJ hj) |>.imp_left Subgroup.mem_inf.1
    refine mem_normalizer_of_conj_mem fun x hx =>
      ⟨(mem_normalizer_iff.1 hjN x).1 hx.1, fun g hg => ?_⟩
    have hj' : j⁻¹ * g * j ∈ P := by
      have := (mem_normalizer_iff.1 (inv_mem hjP) g).1 hg
      rwa [inv_inv] at this
    have h1 := (mem_normalizer_iff.1 hjN₀ _).1 (hx.2 _ hj')
    have e : j * x * j⁻¹ * g * (j * x * j⁻¹)⁻¹ * g⁻¹ =
        j * (x * (j⁻¹ * g * j) * x⁻¹ * (j⁻¹ * g * j)⁻¹) * j⁻¹ := by group
    rw [e]
    exact h1
  have hAne : A ≠ N₀ := fun h0 => hx₀ (h0 ▸ (show x₀ ∈ A from ⟨hx₀N, hx₀c⟩))
  rcases hirr A hN₀A (fun x hx => hx.1) hJA with h0 | h1
  · exact absurd h0 hAne
  · intro x hx g hg
    have : x ∈ A := h1 ▸ hx
    exact this.2 g hg

end H6

section Generic

variable {G : Type*} [Group G]

theorem eq_or_eq_of_transitive {Q A₀ J : Subgroup G} (hA₀Q : A₀ ≤ normalizer (Q : Set G))
    (hJA₀ : J ≤ normalizer (A₀ : Set G)) (hJQ : J ≤ normalizer (Q : Set G))
    (htr : ∀ x ∈ A₀, x ≠ 1 → ∀ y ∈ A₀, y ≠ 1 → ∃ j ∈ J, j * x * j⁻¹ = y)
    {A : Subgroup G} (hQA : Q ≤ A) (hAN : A ≤ A₀ ⊔ Q) (hJA : J ≤ normalizer (A : Set G)) :
    A = Q ∨ A = A₀ ⊔ Q := by
  by_cases hAQ : A ≤ Q
  · exact Or.inl (le_antisymm hAQ hQA)
  right
  refine le_antisymm hAN (sup_le (fun y hy => ?_) hQA)
  obtain ⟨a, haA, haQ⟩ := Set.not_subset.1 hAQ
  obtain ⟨s, hs, q', hq', rfl⟩ := Common.exists_mul_of_le_normalizer' hA₀Q a (hAN haA)
  have hs1 : s ≠ 1 := by
    rintro rfl
    exact haQ (by simpa using hq')
  by_cases hy1 : y = 1
  · rw [hy1]
    exact one_mem _
  obtain ⟨j, hj, hjs⟩ := htr s hs hs1 y hy hy1
  have h1 : j * (s * q') * j⁻¹ ∈ A := (mem_normalizer_iff.1 (hJA hj) _).1 haA
  have h2 : j * q' * j⁻¹ ∈ A := hQA ((mem_normalizer_iff.1 (hJQ hj) _).1 hq')
  have := mul_mem h1 (inv_mem h2)
  rwa [show j * (s * q') * j⁻¹ * (j * q' * j⁻¹)⁻¹ = j * s * j⁻¹ by group, hjs] at this

@[expose] def centralizerModulo (Q P : Subgroup G) : Subgroup G where
  carrier := {m | m ∈ normalizer (Q : Set G) ∧ ∀ x ∈ P, m * x * m⁻¹ * x⁻¹ ∈ Q}
  one_mem' := ⟨one_mem _, fun x _ => by simp⟩
  mul_mem' := fun {m m'} hm hm' => by
    refine ⟨mul_mem hm.1 hm'.1, fun x hx => ?_⟩
    have h1 : m * (m' * x * m'⁻¹ * x⁻¹) * m⁻¹ ∈ Q := (mem_normalizer_iff.1 hm.1 _).1 (hm'.2 x hx)
    have e : m * m' * x * (m * m')⁻¹ * x⁻¹ =
        m * (m' * x * m'⁻¹ * x⁻¹) * m⁻¹ * (m * x * m⁻¹ * x⁻¹) := by group
    rw [e]
    exact mul_mem h1 (hm.2 x hx)
  inv_mem' := fun {m} hm => by
    refine ⟨inv_mem hm.1, fun x hx => ?_⟩
    have h1 : m⁻¹ * (m * x * m⁻¹ * x⁻¹)⁻¹ * m⁻¹⁻¹ ∈ Q :=
      (mem_normalizer_iff.1 (inv_mem hm.1) _).1 (inv_mem (hm.2 x hx))
    have e : m⁻¹ * x * m⁻¹⁻¹ * x⁻¹ = m⁻¹ * (m * x * m⁻¹ * x⁻¹)⁻¹ * m⁻¹⁻¹ := by group
    rw [e]
    exact h1

theorem mem_centralizerModulo_iff {Q P : Subgroup G} {m : G} :
    m ∈ centralizerModulo Q P ↔ m ∈ normalizer (Q : Set G) ∧ ∀ x ∈ P, m * x * m⁻¹ * x⁻¹ ∈ Q :=
  Iff.rfl

end Generic

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Local

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem yamadaL₂_le_yamadaL₆ (d : G2Data L K) (t : G) : yamadaL₂ d t ≤ yamadaL₆ d t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl
    (LieType.BorelTits.pCoreOf_isPGroup 2 _)

theorem isPGroup_yamadaL₆ (d : G2Data L K) (t : G) : IsPGroup 2 (yamadaL₆ d t) :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  LieType.BorelTits.pCoreOf_isPGroup 2 _

theorem S_le_normalizer_yamadaL₆ (h : Setup G L f t) (d : G2Data L K) :
    d.S ≤ normalizer (yamadaL₆ d t : Set G) :=
  (h.S_le_normalizer_yamadaL₂ d).trans (le_normalizer_yamadaL₆ d t)

theorem isPGroup_yamadaR₆ (h : Setup G L f t) (d : G2Data L K) : IsPGroup 2 (yamadaR₆ d t) :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  IsPGroup.to_sup_of_normal_left' (isPGroup_yamadaL₆ d t) d.isSylowOf_S.isPGroup
    (h.S_le_normalizer_yamadaL₆ d)

theorem yamadaR₆_le_normalizer_yamadaL₂ (h : Setup G L f t) (d : G2Data L K) :
    yamadaR₆ d t ≤ normalizer (yamadaL₂ d t : Set G) :=
  sup_le (yamadaL₆_le d t) (h.S_le_normalizer_yamadaL₂ d)

theorem J_le_normalizer_yamadaL₂ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : d.J ≤ normalizer (yamadaL₂ d t : Set G) := fun j hj => by
  have hjC := h.J_le_centralizer_inf_normalizer_S d hj
  exact le_normalizer_yamadaL₂ d t (h.centralizer_inf_normalizer_Y_le d
    (Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hjC).1,
      (h.centralizer_inf_normalizer_S_le d hK hD).2.2 hjC⟩))

theorem normalizer_yamadaL₃_le_normalizer_yamadaW₂ (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    normalizer (yamadaL₃ d t : Set G) ≤ normalizer (yamadaW₂ d t : Set G) := by
  have h1 := LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
    (Subgroup.upperCentralSeries (yamadaL₃ d t) 2)
  rwa [(h.yamada_5_35_2 hW d hK hQ).2] at h1

theorem yamadaR₆_le_normalizer_yamadaW₂ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaR₆ d t ≤ normalizer (yamadaW₂ d t : Set G) :=
  (h.yamadaR₆_le_normalizer_yamadaL₂ d).trans ((h.yamada_5_39_1 hW d hK hQ).1.2.2.trans
    (h.normalizer_yamadaL₃_le_normalizer_yamadaW₂ hW d hK hQ))

theorem yamadaR₆_le_normalizer_yamadaF₂ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaR₆ d t ≤ normalizer (yamadaF₂ d t : Set G) := by
  have h1 := normalizer_le_normalizer_closure_sq (yamadaR₅ d t)
  rw [(h.yamada_5_37_3 hW d hK hQ).2.2] at h1
  exact (h.yamada_5_40_1 hW d hK hQ).2.trans h1

theorem yamadaR₆_le_normalizer_yamadaX₂ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaR₆ d t ≤ normalizer (yamadaX₂ d t : Set G) := by
  have hD := hQ.doubling
  have hP := h.twoElementaryProduct_yamadaF₂ hW d hK hQ
  intro g hg
  have hgF := h.yamadaR₆_le_normalizer_yamadaF₂ hW d hK hQ hg
  have hgW := h.yamadaR₆_le_normalizer_yamadaW₂ hW d hK hQ hg
  have hEF : (yamadaX₂ d t).map (MulAut.conj g).toMonoidHom ≤ yamadaF₂ d t := by
    rw [← map_conj_eq_of_mem_normalizer hgF]
    exact map_mono hP.le_right
  haveI := isElementaryAbelian_map_conj hP.isElementaryAbelian_right g
  rcases hP.le_or_le hEF with hEW | hEX
  · exfalso
    have hEq : (yamadaX₂ d t).map (MulAut.conj g).toMonoidHom = yamadaW₂ d t :=
      Subgroup.eq_of_le_of_card_ge hEW (by
        rw [card_map_conj, h.card_yamadaX₂ d hK hD, h.card_yamadaW₂ d hK hD])
    refine hP.not_le_right fun x hx => ?_
    have h1 : g * x * g⁻¹ ∈ yamadaW₂ d t := hEq ▸ ⟨x, hx, rfl⟩
    exact (mem_normalizer_iff.1 hgW x).2 h1
  · exact mem_normalizer_of_conj_mem fun x hx => hEX ⟨x, hx, rfl⟩

theorem eq_or_eq_of_le_yamadaW₂ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) {A : Subgroup G} (hYA : yamadaY₂ d t ≤ A) (hAW : A ≤ yamadaW₂ d t)
    (hJ : d.Ji 3 ≤ normalizer (A : Set G)) : A = yamadaY₂ d t ∨ A = yamadaW₂ d t := by
  obtain ⟨-, -, hWdef, -⟩ := d.yamada_defs
  obtain ⟨-, -, -, -, hWF, hFD, -, hDS, -⟩ := d.inclusions
  have hW₂eq : yamadaW₂ d t = d.rootGroup g2v ⊔ yamadaY₂ d t := by
    rw [yamadaW₂, ← hWdef, sup_assoc, sup_eq_right.2 (h.Y_le_yamadaY₂ d hK hD)]
  have hJJ : d.Ji 3 ≤ d.J := d.image_mono inf_le_left
  have hAS : d.rootGroup g2v ≤ d.S :=
    (le_sup_left.trans hWdef.le).trans (hWF.trans (hFD.trans hDS))
  obtain ⟨-, htr⟩ := (d.yamada_3_9_2_G (i := 3) (k := 1) (by decide)).2 (Or.inr (by decide))
  rw [hW₂eq] at hAW ⊢
  exact eq_or_eq_of_transitive (fun x hx => h.S_le_normalizer_yamadaY₂ d hK hD (hAS hx))
    (fun j hj => J_le_normalizer_rootGroup d isRoot_g2v (hJJ hj))
    (fun j hj => h.J_le_normalizer_yamadaY₂ d hK hD (hJJ hj)) htr hYA hAW hJ

theorem eq_or_eq_of_le_yamadaX₂ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) {A : Subgroup G} (hYA : yamadaY₂ d t ≤ A) (hAX : A ≤ yamadaX₂ d t)
    (hJ : d.Ji 1 ≤ normalizer (A : Set G)) : A = yamadaY₂ d t ∨ A = yamadaX₂ d t := by
  obtain ⟨-, hXdef, -⟩ := d.yamada_defs
  obtain ⟨-, -, -, hXF, -, hFD, -, hDS, -⟩ := d.inclusions
  have hX₂eq : yamadaX₂ d t = d.rootGroup g2u ⊔ yamadaY₂ d t := by
    rw [yamadaX₂, ← hXdef, sup_assoc, sup_eq_right.2 (h.Y_le_yamadaY₂ d hK hD)]
  have hJJ : d.Ji 1 ≤ d.J := d.image_mono inf_le_left
  have hAS : d.rootGroup g2u ≤ d.S :=
    (le_sup_left.trans hXdef.le).trans (hXF.trans (hFD.trans hDS))
  obtain ⟨-, htr⟩ := (d.yamada_3_9_2_G (i := 1) (k := 5) (by decide)).2 (Or.inr (by decide))
  rw [hX₂eq] at hAX ⊢
  exact eq_or_eq_of_transitive (fun x hx => h.S_le_normalizer_yamadaY₂ d hK hD (hAS hx))
    (fun j hj => J_le_normalizer_rootGroup d isRoot_g2u (hJJ hj))
    (fun j hj => h.J_le_normalizer_yamadaY₂ d hK hD (hJJ hj)) htr hYA hAX hJ

theorem yamadaF₂_le_yamadaM₂ (d : G2Data L K) (t : G) : yamadaF₂ d t ≤ yamadaM₂ d t :=
  sup_le_sup_right d.inclusions.2.2.2.2.2.2.1 _

theorem yamadaY₂_ne_yamadaW₂ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : yamadaY₂ d t ≠ yamadaW₂ d t := fun e => by
  have := h.card_yamadaW₂ d hK hD
  rw [← e, h.card_yamadaY₂ d hK hD] at this
  have h4 : 4 ≤ Nat.card K := hK ▸ h.four_le
  have := Nat.pow_right_injective (show 2 ≤ Nat.card K by omega) this
  omega

theorem yamadaY₂_ne_yamadaX₂ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : yamadaY₂ d t ≠ yamadaX₂ d t := fun e => by
  have := h.card_yamadaX₂ d hK hD
  rw [← e, h.card_yamadaY₂ d hK hD] at this
  have h4 : 4 ≤ Nat.card K := hK ▸ h.four_le
  have := Nat.pow_right_injective (show 2 ≤ Nat.card K by omega) this
  omega

theorem commutator_yamadaW₂_yamadaL₆ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    ∀ x ∈ yamadaW₂ d t, ∀ g ∈ yamadaL₆ d t, x * g * x⁻¹ * g⁻¹ ∈ yamadaY₂ d t := by
  have hD := hQ.doubling
  have hJJ : d.Ji 3 ≤ d.J := d.image_mono inf_le_left
  have hL₂N := h.J_le_normalizer_yamadaL₂ d hK hD
  have hW₂L₆ : yamadaW₂ d t ≤ yamadaL₆ d t :=
    ((sup_le_sup_right (d.inclusions.2.2.2.2.1.trans d.inclusions.2.2.2.2.2.2.1) _ :
      yamadaW₂ d t ≤ yamadaM₂ d t).trans (h.yamadaM₂_le_yamadaL₂ d hK hD)).trans
      (yamadaL₂_le_yamadaL₆ d t)
  refine commutator_le_of_irreducible (isPGroup_yamadaL₆ d t) le_sup_right hW₂L₆
    (fun g hg => (h.normalizer_yamadaL₂_le d hK hD).2 (yamadaL₆_le d t hg))
    (fun g hg => h.yamadaR₆_le_normalizer_yamadaW₂ hW d hK hQ
      ((le_sup_left : yamadaL₆ d t ≤ yamadaR₆ d t) hg)) (J := d.Ji 3)
    (fun j hj => Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨
      le_normalizer_yamadaL₆ d t (hL₂N (hJJ hj)),
      mem_normalizer_sup (h.J_le_normalizer_W d hK hD (hJJ hj))
        (h.J_le_normalizer_yamadaY₂ d hK hD (hJJ hj))⟩,
      h.J_le_normalizer_yamadaY₂ d hK hD (hJJ hj)⟩)
    (fun A hYA hAW hJA => h.eq_or_eq_of_le_yamadaW₂ d hK hD hYA hAW hJA)
    (h.yamadaY₂_ne_yamadaW₂ d hK hD)

theorem commutator_yamadaX₂_yamadaL₆ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    ∀ x ∈ yamadaX₂ d t, ∀ g ∈ yamadaL₆ d t, x * g * x⁻¹ * g⁻¹ ∈ yamadaY₂ d t := by
  have hD := hQ.doubling
  have hJJ : d.Ji 1 ≤ d.J := d.image_mono inf_le_left
  have hL₂N := h.J_le_normalizer_yamadaL₂ d hK hD
  have hX₂L₆ : yamadaX₂ d t ≤ yamadaL₆ d t :=
    ((sup_le_sup_right (d.inclusions.2.2.2.1.trans d.inclusions.2.2.2.2.2.2.1) _ :
      yamadaX₂ d t ≤ yamadaM₂ d t).trans (h.yamadaM₂_le_yamadaL₂ d hK hD)).trans
      (yamadaL₂_le_yamadaL₆ d t)
  refine commutator_le_of_irreducible (isPGroup_yamadaL₆ d t) le_sup_right hX₂L₆
    (fun g hg => (h.normalizer_yamadaL₂_le d hK hD).2 (yamadaL₆_le d t hg))
    (fun g hg => h.yamadaR₆_le_normalizer_yamadaX₂ hW d hK hQ
      ((le_sup_left : yamadaL₆ d t ≤ yamadaR₆ d t) hg)) (J := d.Ji 1)
    (fun j hj => Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨
      le_normalizer_yamadaL₆ d t (hL₂N (hJJ hj)),
      mem_normalizer_sup (h.J_le_normalizer_X d hK hD (hJJ hj))
        (h.J_le_normalizer_yamadaY₂ d hK hD (hJJ hj))⟩,
      h.J_le_normalizer_yamadaY₂ d hK hD (hJJ hj)⟩)
    (fun A hYA hAX hJA => h.eq_or_eq_of_le_yamadaX₂ d hK hD hYA hAX hJA)
    (h.yamadaY₂_ne_yamadaX₂ d hK hD)

theorem commutator_yamadaM₂_yamadaL₆ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    ∀ m ∈ yamadaM₂ d t, ∀ g ∈ yamadaL₆ d t, m * g * m⁻¹ * g⁻¹ ∈ yamadaY₂ d t := by
  have hD := hQ.doubling
  obtain ⟨-, -, -, hXF, hWF, -, hFM, -⟩ := d.inclusions
  have hwL₆ : d.wb ∈ normalizer (yamadaL₆ d t : Set G) :=
    le_normalizer_yamadaL₆ d t (h.wb_mem_normalizer_yamadaL₂ d)
  have hwY₂ : d.wb ∈ normalizer (yamadaY₂ d t : Set G) :=
    (h.normalizer_yamadaL₂_le d hK hD).2 (h.wb_mem_normalizer_yamadaL₂ d)
  have hL₂Y₂ := h.yamadaL₂_le_normalizer_yamadaY₂ d hK hD
  have hM₂L₂ := h.yamadaM₂_le_yamadaL₂ d hK hD
  have hW₂M₂ : yamadaW₂ d t ≤ yamadaM₂ d t := sup_le_sup_right (hWF.trans hFM) _
  have hX₂M₂ : yamadaX₂ d t ≤ yamadaM₂ d t := sup_le_sup_right (hXF.trans hFM) _
  have hW₂C : yamadaW₂ d t ≤ centralizerModulo (yamadaY₂ d t) (yamadaL₆ d t) := fun x hx =>
    ⟨hL₂Y₂ (hM₂L₂ (hW₂M₂ hx)), h.commutator_yamadaW₂_yamadaL₆ hW d hK hQ x hx⟩
  have hX₂C : yamadaX₂ d t ≤ centralizerModulo (yamadaY₂ d t) (yamadaL₆ d t) := fun x hx =>
    ⟨hL₂Y₂ (hM₂L₂ (hX₂M₂ hx)), h.commutator_yamadaX₂_yamadaL₆ hW d hK hQ x hx⟩
  have hXwC : d.X.map (MulAut.conj d.wb).toMonoidHom ≤
      centralizerModulo (yamadaY₂ d t) (yamadaL₆ d t) := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' := hX₂C ((le_sup_left : d.X ≤ yamadaX₂ d t) hx)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    refine ⟨mul_mem (mul_mem hwY₂ hx'.1) (inv_mem hwY₂), fun g hg => ?_⟩
    have hg' : d.wb⁻¹ * g * d.wb ∈ yamadaL₆ d t := by
      have := (mem_normalizer_iff.1 (inv_mem hwL₆) g).1 hg
      rwa [inv_inv] at this
    have h2 := (mem_normalizer_iff.1 hwY₂ _).1 (hx'.2 _ hg')
    have e : d.wb * x * d.wb⁻¹ * g * (d.wb * x * d.wb⁻¹)⁻¹ * g⁻¹ =
        d.wb * (x * (d.wb⁻¹ * g * d.wb) * x⁻¹ * (d.wb⁻¹ * g * d.wb)⁻¹) * d.wb⁻¹ := by group
    rw [e]
    exact h2
  have hMC : d.M ≤ centralizerModulo (yamadaY₂ d t) (yamadaL₆ d t) :=
    d.M_le_sup_conj.trans (sup_le (sup_le (le_sup_left.trans hW₂C) (le_sup_left.trans hX₂C)) hXwC)
  have hY₂C : yamadaY₂ d t ≤ centralizerModulo (yamadaY₂ d t) (yamadaL₆ d t) := fun y hy =>
    ⟨Subgroup.le_normalizer hy, fun g hg => by
      have h1 := (mem_normalizer_iff.1 ((h.normalizer_yamadaL₂_le d hK hD).2
        (yamadaL₆_le d t hg)) y⁻¹).1 (inv_mem hy)
      rw [show y * g * y⁻¹ * g⁻¹ = y * (g * y⁻¹ * g⁻¹) by group]
      exact mul_mem hy h1⟩
  intro m hm g hg
  exact ((sup_le hMC hY₂C : yamadaM₂ d t ≤ centralizerModulo (yamadaY₂ d t) (yamadaL₆ d t)) hm).2
    g hg

theorem yamadaL₆_inf_le (d : G2Data L K) (t : G) :
    yamadaL₆ d t ⊓ normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G) ≤ yamadaL₂ d t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right
    (fun g hg => Common.mem_normalizer_inf (le_normalizer_yamadaL₆ d t
      (le_normalizer_yamadaL₂ d t hg)) (Subgroup.le_normalizer hg))
    ((isPGroup_yamadaL₆ d t).to_le inf_le_left)

theorem crossed_mem_yamadaM₂ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) {x : G} (hx : x ∈ normalizer (yamadaL₂ d t : Set G)) :
    t * x * t * x⁻¹ ∈ yamadaM₂ d t := by
  have htt := h.t_mul_t
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have htL₂ : t ∈ yamadaL₂ d t := h.tM_le_yamadaL₂ d hK (mem_sup_right (mem_zpowers t))
  have htM₂ : t ∈ normalizer (yamadaM₂ d t : Set G) :=
    h.yamadaL₂_le_normalizer_yamadaM₂ d hK hD htL₂
  have hxM₂ : x ∈ normalizer (yamadaM₂ d t : Set G) := (h.normalizer_yamadaL₂_le d hK hD).1 hx
  have hκ : t * x * t * x⁻¹ ∈ yamadaL₂ d t := by
    have := mul_mem htL₂ ((mem_normalizer_iff.1 hx t).1 htL₂)
    rwa [show t * (x * t * x⁻¹) = t * x * t * x⁻¹ by group] at this
  rw [h.yamadaL₂_eq_sup d hK hD] at hκ
  rcases (mem_sup_zpowers_iff_of htt htM₂).1 hκ with h1 | ⟨a, ha, e⟩
  · exact h1
  · exfalso
    have h2 : x * t * x⁻¹ = t * a * t⁻¹ := by
      calc x * t * x⁻¹ = (t * t) * x * t * x⁻¹ := by rw [htt, one_mul]
        _ = t * (t * x * t * x⁻¹) := by group
        _ = t * (a * t) := by rw [e]
        _ = t * a * t⁻¹ := by rw [htinv]; group
    exact h.t_not_mem_yamadaM₂ d hK hD
      ((mem_normalizer_iff.1 hxM₂ t).2 (by rw [h2]; exact (mem_normalizer_iff.1 htM₂ a).1 ha))

theorem crossed_mem_yamadaY₂_iff (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) {x : G}
    (hx : x ∈ yamadaL₆ d t) : t * x * t * x⁻¹ ∈ yamadaY₂ d t ↔ x ∈ yamadaL₂ d t := by
  have htt := h.t_mul_t
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have htL₂ : t ∈ yamadaL₂ d t := h.tM_le_yamadaL₂ d hK (mem_sup_right (mem_zpowers t))
  have htY₂ : t ∈ normalizer (yamadaY₂ d t : Set G) :=
    h.yamadaL₂_le_normalizer_yamadaY₂ d hK hD htL₂
  have htY₂' : t ∉ yamadaY₂ d t := fun ht =>
    h.t_not_mem_yamadaM₂ d hK hD ((le_sup_right : yamadaY₂ d t ≤ yamadaM₂ d t) ht)
  have hxY₂ : x ∈ normalizer (yamadaY₂ d t : Set G) :=
    (h.normalizer_yamadaL₂_le d hK hD).2 (yamadaL₆_le d t hx)
  constructor
  · intro hκ
    have hgt : x * t * x⁻¹ ∈ yamadaY₂ d t ⊔ zpowers t := by
      rw [h.conj_t_eq_mul_crossed x]
      exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left hκ)
    have h1 := mem_normalizer_sup_zpowers_of_conj_mem hxY₂ hgt
    rw [h.yamada_5_17_2 hW d hK hD] at h1
    exact yamadaL₆_inf_le d t (Subgroup.mem_inf.2 ⟨hx, h1⟩)
  · intro hxL₂
    have h1 : x ∈ normalizer ((yamadaY₂ d t ⊔ zpowers t : Subgroup G) : Set G) := by
      rw [h.yamada_5_17_2 hW d hK hD]
      exact yamadaL₂_le d t hxL₂
    have hgt := (mem_normalizer_iff.1 h1 t).1 (mem_sup_right (mem_zpowers t))
    rcases (mem_sup_zpowers_iff_of htt htY₂).1 hgt with h2 | ⟨a, ha, e⟩
    · exact absurd ((mem_normalizer_iff.1 hxY₂ t).2 h2) htY₂'
    · have e2 : t * x * t * x⁻¹ = t * a * t⁻¹ := by
        calc t * x * t * x⁻¹ = t * (x * t * x⁻¹) := by group
          _ = t * (a * t) := by rw [e]
          _ = t * a * t⁻¹ := by rw [htinv]; group
      rw [e2]
      exact (mem_normalizer_iff.1 htY₂ a).1 ha

theorem yamadaL₃_le_yamadaL₆ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaL₃ d t ≤ yamadaL₆ d t := by
  rw [← (h.yamada_5_39_1 hW d hK hQ).2]
  exact inf_le_left

theorem card_yamadaL₆ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    Nat.card (yamadaL₆ d t) = 2 * Nat.card K ^ 10 := by
  have hD := hQ.doubling
  have hL₃L₆ := h.yamadaL₃_le_yamadaL₆ hW d hK hQ
  obtain ⟨_, _, φ, -, -⟩ := h.yamada_5_39_2 hW d hK hQ
  have hq : 0 < Nat.card K ^ 3 := by
    have : 0 < Nat.card K := Nat.card_pos
    positivity
  have hMW : Nat.card (d.M ⧸ d.W.subgroupOf d.M) = Nat.card K ^ 2 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (d.W.subgroupOf d.M)
    rw [Nat.card_congr (subgroupOfEquivOfLe (d.inclusions.2.2.2.2.1.trans
      d.inclusions.2.2.2.2.2.2.1)).toEquiv, d.cards.2.2.2.2.2.2.1, d.cards.2.2.2.1] at h1
    refine Nat.eq_of_mul_eq_mul_right hq ?_
    rw [← h1]
    ring
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((yamadaL₃ d t).subgroupOf (yamadaL₆ d t))
  rw [Nat.card_congr φ.toEquiv, Nat.card_congr (subgroupOfEquivOfLe hL₃L₆).toEquiv, hMW,
    (h.card_yamadaL₃_R₃ hW d hK hD).1] at h1
  rw [h1]
  ring

theorem exists_crossed_hom_yamadaL₆ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    ∃ _ : (d.Y.subgroupOf d.M).Normal, ∃ ψ : yamadaL₆ d t →* d.M ⧸ d.Y.subgroupOf d.M,
      (∀ (x : yamadaL₆ d t) (m : d.M), ∀ y ∈ yamadaY₂ d t,
        (x : G) * t * (x : G)⁻¹ = t * m * y → ψ x = QuotientGroup.mk m) ∧
      ψ.ker = (yamadaL₂ d t).subgroupOf (yamadaL₆ d t) ∧ Function.Surjective ψ := by
  have hD := hQ.doubling
  obtain ⟨-, hYX, -, hXF, -, -, hFM, -⟩ := d.inclusions
  have hYM : d.Y ≤ d.M := hYX.trans (hXF.trans hFM)
  have hMY₂ := h.M_le_centralizer_yamadaY₂ d hK hD
  have huniq : ∀ {a₁ a₂ η₁ η₂ : G}, a₁ ∈ d.M → a₂ ∈ d.M → η₁ ∈ yamadaY₂ d t →
      η₂ ∈ yamadaY₂ d t → a₁ * η₁ = a₂ * η₂ → a₁⁻¹ * a₂ ∈ d.Y := by
    intro a₁ a₂ η₁ η₂ ha₁ ha₂ hη₁ hη₂ e
    rw [← h.M_inf_yamadaY₂ d hK hD]
    refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem ha₁) ha₂, ?_⟩
    rw [show a₁⁻¹ * a₂ = η₁ * η₂⁻¹ by
      calc a₁⁻¹ * a₂ = a₁⁻¹ * (a₂ * η₂) * η₂⁻¹ := by group
        _ = a₁⁻¹ * (a₁ * η₁) * η₂⁻¹ := by rw [e]
        _ = η₁ * η₂⁻¹ := by group]
    exact mul_mem hη₁ (inv_mem hη₂)
  have hκM : ∀ x : yamadaL₆ d t, t * (x : G) * t * (x : G)⁻¹ ∈ yamadaM₂ d t := fun x =>
    h.crossed_mem_yamadaM₂ d hK hD (yamadaL₆_le d t x.2)
  have hdec : ∀ x : yamadaL₆ d t, ∃ a ∈ d.M, ∃ η ∈ yamadaY₂ d t,
      t * (x : G) * t * (x : G)⁻¹ = a * η := fun x =>
    Common.exists_mul_of_le_normalizer (h.yamadaY₂_le_normalizer_M d hK hD) _ (hκM x)
  choose af haf ηf hηf hfe using hdec
  have hYMn : (d.Y.subgroupOf d.M).Normal := by
    refine (normal_subgroupOf_iff_le_normalizer hYM).2 fun a ha => ?_
    have : a ∈ L ⊓ normalizer (d.Y : Set G) := by
      rw [(d.yamada_3_13_3_G).1]
      exact mem_sup_left ha
    exact (Subgroup.mem_inf.1 this).2
  let ψ : yamadaL₆ d t →* d.M ⧸ d.Y.subgroupOf d.M :=
    { toFun := fun x => QuotientGroup.mk ⟨af x, haf x⟩
      map_one' := by
        apply (QuotientGroup.eq_one_iff _).2
        rw [mem_subgroupOf]
        have e : (1 : G) * 1 = af 1 * ηf 1 := by
          rw [← hfe 1]
          show (1 : G) * 1 = t * 1 * t * (1 : G)⁻¹
          rw [mul_one, inv_one, mul_one, mul_one, h.t_mul_t]
        have := huniq (one_mem _) (haf 1) (one_mem _) (hηf 1) e
        rwa [inv_one, one_mul] at this
      map_mul' := fun x y => by
        rw [← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf]
        show (af (x * y))⁻¹ * (af x * af y) ∈ d.Y
        have hz : (x : G) * (t * y * t * (y : G)⁻¹) * (x : G)⁻¹ *
            (t * y * t * (y : G)⁻¹)⁻¹ ∈ yamadaY₂ d t := by
          have h1 := inv_mem (h.commutator_yamadaM₂_yamadaL₆ hW d hK hQ _ (hκM y) x x.2)
          rwa [show ((t * y * t * (y : G)⁻¹) * (x : G) * (t * y * t * (y : G)⁻¹)⁻¹ *
            (x : G)⁻¹)⁻¹ = (x : G) * (t * y * t * (y : G)⁻¹) * (x : G)⁻¹ *
              (t * y * t * (y : G)⁻¹)⁻¹ by group] at h1
        have hcomm : (ηf x * ((x : G) * (t * y * t * (y : G)⁻¹) * (x : G)⁻¹ *
            (t * y * t * (y : G)⁻¹)⁻¹)) * af y =
            af y * (ηf x * ((x : G) * (t * y * t * (y : G)⁻¹) * (x : G)⁻¹ *
              (t * y * t * (y : G)⁻¹)⁻¹)) :=
          mem_centralizer_iff.1 (hMY₂ (haf y)) _ (mul_mem (hηf x) hz)
        have e : af (x * y) * ηf (x * y) = (af x * af y) * (ηf x *
            ((x : G) * (t * y * t * (y : G)⁻¹) * (x : G)⁻¹ * (t * y * t * (y : G)⁻¹)⁻¹) *
              ηf y) := by
          rw [← hfe (x * y)]
          show t * ((x : G) * y) * t * ((x : G) * y)⁻¹ = _
          rw [h.crossed_mul' (x : G) y]
          calc t * x * t * (x : G)⁻¹ * ((x : G) * (t * y * t * (y : G)⁻¹) * (x : G)⁻¹) =
                t * x * t * (x : G)⁻¹ * (((x : G) * (t * y * t * (y : G)⁻¹) * (x : G)⁻¹ *
                  (t * y * t * (y : G)⁻¹)⁻¹) * (t * y * t * (y : G)⁻¹)) := by group
            _ = af x * ηf x * (((x : G) * (t * y * t * (y : G)⁻¹) * (x : G)⁻¹ *
                  (t * y * t * (y : G)⁻¹)⁻¹) * (af y * ηf y)) := by rw [hfe x, hfe y]
            _ = af x * ((ηf x * ((x : G) * (t * y * t * (y : G)⁻¹) * (x : G)⁻¹ *
                  (t * y * t * (y : G)⁻¹)⁻¹)) * af y) * ηf y := by group
            _ = af x * (af y * (ηf x * ((x : G) * (t * y * t * (y : G)⁻¹) * (x : G)⁻¹ *
                  (t * y * t * (y : G)⁻¹)⁻¹))) * ηf y := by rw [hcomm]
            _ = _ := by group
        exact huniq (haf (x * y)) (mul_mem (haf x) (haf y)) (hηf (x * y))
          (mul_mem (mul_mem (hηf x) hz) (hηf y)) e }
  have hψ : ∀ x : yamadaL₆ d t, ψ x = QuotientGroup.mk ⟨af x, haf x⟩ := fun _ => rfl
  have hform : ∀ (x : yamadaL₆ d t) (m : d.M), ∀ y ∈ yamadaY₂ d t,
      (x : G) * t * (x : G)⁻¹ = t * m * y → ψ x = QuotientGroup.mk m := by
    intro x m y hy e
    rw [hψ, QuotientGroup.eq, mem_subgroupOf]
    refine huniq (haf x) m.2 (hηf x) hy ?_
    rw [← hfe x, show t * (x : G) * t * (x : G)⁻¹ = t * ((x : G) * t * (x : G)⁻¹) by group, e,
      ← mul_assoc, ← mul_assoc, h.t_mul_t, one_mul]
  have hker : ψ.ker = (yamadaL₂ d t).subgroupOf (yamadaL₆ d t) := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf, hψ, QuotientGroup.eq_one_iff, mem_subgroupOf,
      ← h.crossed_mem_yamadaY₂_iff hW d hK hD x.2]
    constructor
    · intro hx
      rw [hfe x]
      exact mul_mem (h.Y_le_yamadaY₂ d hK hD hx) (hηf x)
    · intro hx
      have := huniq (haf x) (one_mem _) (hηf x) hx (by rw [← hfe x, one_mul])
      simpa using this
  refine ⟨hYMn, ψ, hform, hker, ?_⟩
  have hL₂L₆ := yamadaL₂_le_yamadaL₆ d t
  have hq : 0 < Nat.card K ^ 2 := by
    have : 0 < Nat.card K := Nat.card_pos
    positivity
  have hq7 : 0 < 2 * Nat.card K ^ 7 := by
    have : 0 < Nat.card K := Nat.card_pos
    positivity
  have hcard : Nat.card (yamadaL₆ d t) = Nat.card (yamadaL₆ d t ⧸ ψ.ker) * Nat.card ψ.ker :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
  have hkerc : Nat.card ψ.ker = Nat.card (yamadaL₂ d t) := by
    rw [hker]
    exact Nat.card_congr (subgroupOfEquivOfLe hL₂L₆).toEquiv
  have hc1 : Nat.card (yamadaL₆ d t ⧸ ψ.ker) = Nat.card K ^ 3 := by
    rw [h.card_yamadaL₆ hW d hK hQ, hkerc, h.card_yamadaL₂ d hK] at hcard
    refine Nat.eq_of_mul_eq_mul_right hq7 ?_
    rw [← hcard]
    ring
  have hc2 : Nat.card (d.M ⧸ d.Y.subgroupOf d.M) = Nat.card K ^ 3 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (d.Y.subgroupOf d.M)
    rw [Nat.card_congr (subgroupOfEquivOfLe hYM).toEquiv, d.cards.2.2.2.2.2.2.1,
      d.cards.2.1] at h1
    refine Nat.eq_of_mul_eq_mul_right hq ?_
    rw [← h1]
    ring
  have hrange : ψ.range = ⊤ := by
    refine Subgroup.eq_top_of_card_eq _ ?_
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv, hc1, hc2]
  exact MonoidHom.range_eq_top.1 hrange

theorem yamada_5_41_2 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    closure {z | ∃ g ∈ yamadaL₆ d t, z = g ^ 2} = yamadaM₂ d t := by
  have hD := hQ.doubling
  have htt := h.t_mul_t
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  obtain ⟨-, hYX, hYW, hXF, hWF, -, hFM, -⟩ := d.inclusions
  have htL₂ : t ∈ yamadaL₂ d t := h.tM_le_yamadaL₂ d hK (mem_sup_right (mem_zpowers t))
  have htL₆ : t ∈ yamadaL₆ d t := yamadaL₂_le_yamadaL₆ d t htL₂
  have htY₂ : t ∈ normalizer (yamadaY₂ d t : Set G) :=
    h.yamadaL₂_le_normalizer_yamadaY₂ d hK hD htL₂
  have htM₂ : t ∈ normalizer (yamadaM₂ d t : Set G) :=
    h.yamadaL₂_le_normalizer_yamadaM₂ d hK hD htL₂
  have htW₂ : t ∈ normalizer (yamadaW₂ d t : Set G) :=
    (h.t_mem_normalizer_yamadaW₂ d hK hD).1
  have hL₂Y₂ := h.yamadaL₂_le_normalizer_yamadaY₂ d hK hD
  have hM₂L₂ := h.yamadaM₂_le_yamadaL₂ d hK hD
  have hYM₂ : d.Y ≤ yamadaM₂ d t :=
    (h.Y_le_yamadaY₂ d hK hD).trans le_sup_right
  have hsq₂ : ∀ x ∈ yamadaL₆ d t, x * x ∈ yamadaL₂ d t := by
    intro x hx
    have hκ := h.crossed_mem_yamadaM₂ d hK hD (yamadaL₆_le d t hx)
    refine (h.crossed_mem_yamadaY₂_iff hW d hK hD (mul_mem hx hx)).1 ?_
    have hc := h.commutator_yamadaM₂_yamadaL₆ hW d hK hQ _ hκ x hx
    have hκ2 := h.Y_le_yamadaY₂ d hK hD (h.mul_self_mem_Y_of_mem_yamadaL₂ d hK hD (hM₂L₂ hκ))
    have hκz := (mem_normalizer_iff.1 (hL₂Y₂ (hM₂L₂ hκ)) _).1 (inv_mem hc)
    have key : ∀ κ x : G, κ * (x * κ * x⁻¹) =
        (κ * (κ * x * κ⁻¹ * x⁻¹)⁻¹ * κ⁻¹) * (κ * κ) := fun κ x => by group
    rw [h.crossed_mul' x x, key]
    exact mul_mem hκz hκ2
  have hsqM : ∀ x ∈ yamadaL₆ d t, x * x ∈ yamadaM₂ d t := by
    intro x hx
    have h1 := hsq₂ x hx
    rw [h.yamadaL₂_eq_sup d hK hD] at h1
    rcases (mem_sup_zpowers_iff_of htt htM₂).1 h1 with h2 | ⟨m', hm', hxx⟩
    · exact h2
    · exfalso
      have hc : x * m'⁻¹ * x⁻¹ * m' ∈ yamadaY₂ d t := by
        have := inv_mem (h.commutator_yamadaM₂_yamadaL₆ hW d hK hQ m'⁻¹ (inv_mem hm') x hx)
        rwa [show (m'⁻¹ * x * m'⁻¹⁻¹ * x⁻¹)⁻¹ = x * m'⁻¹ * x⁻¹ * m' by group] at this
      have hm'e : m' = x * x * t⁻¹ := by
        calc m' = m' * t * t⁻¹ := by group
          _ = x * x * t⁻¹ := by rw [← hxx]
      have e : t * x * t * x⁻¹ = t * (x * m'⁻¹ * x⁻¹ * m') * t := by
        rw [hm'e]
        group
      have hκY₂ : t * x * t * x⁻¹ ∈ yamadaY₂ d t := by
        rw [e]
        have := (mem_normalizer_iff.1 htY₂ _).1 hc
        rwa [htinv] at this
      have hxL₂ := (h.crossed_mem_yamadaY₂_iff hW d hK hD hx).1 hκY₂
      have hxxY := h.mul_self_mem_Y_of_mem_yamadaL₂ d hK hD hxL₂
      apply h.t_not_mem_yamadaM₂ d hK hD
      have : m'⁻¹ * (x * x) ∈ yamadaM₂ d t :=
        mul_mem (inv_mem hm') (hYM₂ hxxY)
      rwa [hxx, inv_mul_cancel_left] at this
  set E := closure {z | ∃ g ∈ yamadaL₆ d t, z = g ^ 2} with hEdef
  have hEM₂ : E ≤ yamadaM₂ d t :=
    (closure_le _).2 fun z ⟨g, hg, e⟩ => by rw [e, sq]; exact hsqM g hg
  have hW₂E : yamadaW₂ d t ≤ E := by
    rw [← (h.yamada_5_35_3 hW d hK hQ).2.2.1]
    exact closure_mono fun z ⟨g, hg, e⟩ => ⟨g, h.yamadaL₃_le_yamadaL₆ hW d hK hQ hg, e⟩
  have hBE : d.leviB ≤ normalizer (E : Set G) := fun b hb =>
    normalizer_le_normalizer_closure_sq (yamadaL₆ d t) (le_normalizer_yamadaL₆ d t
      (le_normalizer_yamadaL₂ d t (h.centralizer_inf_normalizer_Y_le d
        (h.leviB_le_centralizer_inf_normalizer_Y d hb))))
  have hBM : d.leviB ≤ normalizer (d.M : Set G) := fun b hb => by
    have : b ∈ L ⊓ normalizer (d.M : Set G) := by
      rw [(d.yamada_3_13_3_G).2.2.1]
      exact mem_sup_right (mem_sup_left hb)
    exact (Subgroup.mem_inf.1 this).2
  have hirr := (d.yamada_3_16_2_G (E := E ⊓ d.M)
    (fun b hb => Common.mem_normalizer_inf (hBE hb) (hBM hb))).2
    (le_inf ((le_sup_left : d.W ≤ yamadaW₂ d t).trans hW₂E) (hWF.trans hFM)) inf_le_right
  have hEdec : E ≤ (E ⊓ d.M) ⊔ yamadaY₂ d t := fun x hx => by
    obtain ⟨m, hm, y, hy, rfl⟩ := Common.exists_mul_of_le_normalizer
      (h.yamadaY₂_le_normalizer_M d hK hD) x (hEM₂ hx)
    have hyE : y ∈ E := hW₂E ((le_sup_right : yamadaY₂ d t ≤ yamadaW₂ d t) hy)
    have hmE : m ∈ E := by
      have := mul_mem hx (inv_mem hyE)
      rwa [mul_inv_cancel_right] at this
    exact mul_mem (mem_sup_left ⟨hmE, hm⟩) (mem_sup_right hy)
  rcases hirr with h1 | h1
  · exfalso
    have hEW : E ≤ yamadaW₂ d t := by
      refine hEdec.trans (sup_le ?_ le_sup_right)
      rw [h1]
      exact le_sup_left
    have hEq : E = yamadaW₂ d t := le_antisymm hEW hW₂E
    obtain ⟨hYMn, ψ, hform, hker, hsurj⟩ := h.exists_crossed_hom_yamadaL₆ hW d hK hQ
    obtain ⟨m, hmM, hmW⟩ : ∃ m ∈ d.M, m ∉ d.W := by
      by_contra hcon
      push Not at hcon
      have h1 := Subgroup.card_le_of_le (show d.M ≤ d.W from hcon)
      rw [d.cards.2.2.2.2.2.2.1, d.cards.2.2.2.1] at h1
      have h4 : 4 ≤ Nat.card K := hK ▸ h.four_le
      have := Nat.pow_lt_pow_right hQ.one_lt (show 3 < 5 by omega)
      omega
    obtain ⟨z, hz⟩ := hsurj (QuotientGroup.mk ⟨m, hmM⟩)
    obtain ⟨a, ha, η, hη, hae⟩ := Common.exists_mul_of_le_normalizer
      (h.yamadaY₂_le_normalizer_M d hK hD) _
      (h.crossed_mem_yamadaM₂ d hK hD (yamadaL₆_le d t z.2))
    have e : (z : G) * t * (z : G)⁻¹ = t * a * η := by
      rw [h.conj_t_eq_mul_crossed (z : G), hae]
      group
    have h2 : (⟨a, ha⟩ : d.M)⁻¹ * ⟨m, hmM⟩ ∈ d.Y.subgroupOf d.M := by
      rw [← QuotientGroup.eq, ← hform z ⟨a, ha⟩ η hη e]
      exact hz
    have h2' : a⁻¹ * m ∈ d.Y := mem_subgroupOf.1 h2
    have hzt : (z : G) * t * (z : G)⁻¹ * t ∈ E := by
      have e1 : (z : G) * t * (z : G)⁻¹ * t = ((z : G) * t) ^ 2 * (t * (z : G)⁻¹ * t) ^ 2 := by
        calc (z : G) * t * (z : G)⁻¹ * t =
            (z : G) * t * z * (t * t) * (z : G)⁻¹ * (t * t) * (z : G)⁻¹ * t := by
              rw [htt]
              group
          _ = ((z : G) * t) ^ 2 * (t * (z : G)⁻¹ * t) ^ 2 := by rw [sq, sq]; group
      rw [e1]
      exact mul_mem (subset_closure ⟨(z : G) * t, mul_mem z.2 htL₆, rfl⟩)
        (subset_closure ⟨t * (z : G)⁻¹ * t, mul_mem (mul_mem htL₆ (inv_mem z.2)) htL₆, rfl⟩)
    rw [hEq, e] at hzt
    have haη : a * η ∈ yamadaW₂ d t := by
      have := (mem_normalizer_iff.1 htW₂ _).1 hzt
      rwa [show t * (t * a * η * t) * t⁻¹ = (t * t) * a * η * (t * t⁻¹) by group, htt,
        mul_inv_cancel, one_mul, mul_one] at this
    have haW₂ : a ∈ yamadaW₂ d t := by
      have := mul_mem haη (inv_mem ((le_sup_right : yamadaY₂ d t ≤ yamadaW₂ d t) hη))
      rwa [mul_inv_cancel_right] at this
    have haW : a ∈ d.W := by
      rw [← h.yamadaW₂_inf_centralizer d hK hD]
      exact Subgroup.mem_inf.2 ⟨haW₂, h.L_le_centralizer
        (d.inclusions.2.2.2.2.2.2.2.2.1.trans d.inclusions.2.2.2.2.2.2.2.2.2 ha)⟩
    refine hmW ?_
    have := mul_mem haW (hYW h2')
    rwa [mul_inv_cancel_left] at this
  · refine le_antisymm hEM₂ (sup_le (inf_eq_right.1 h1) (le_sup_right.trans hW₂E))

theorem yamada_5_41_3 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    normalizer (yamadaV₂ d t : Set G) = normalizer (yamadaV₃ d t : Set G) := by
  have hD := hQ.doubling
  obtain ⟨hW₃e, hW₃c, hW₃L, -⟩ := h.yamada_5_33_3_uniform hW d hK hQ.doubling
  obtain ⟨hW₃V₃, hV₃N, -, hW₂W₃, htW₃, hV₃eq, -⟩ := h.yamadaW₃_facts hW d hK hD
  obtain ⟨hV₂V₃, hV₃E₃, hV₃L₂, hV₃R₂, -, -, -, -, -⟩ := h.yamadaV₃_facts hW d hK hD
  have htt := h.t_mul_t
  have htV₃ : t ∈ yamadaV₃ d t := hV₂V₃ (mem_sup_right (mem_zpowers t))
  have htW₃N : t ∈ normalizer (yamadaW₃ d t : Set G) := hV₃N htV₃
  have hWW₂ : d.W ≤ yamadaW₂ d t := le_sup_left
  have h1 : normalizer (yamadaV₂ d t : Set G) ≤ normalizer (yamadaV₃ d t : Set G) := by
    intro g hg
    have hgL₃ : g ∈ normalizer (yamadaL₃ d t : Set G) :=
      LieType.BorelTits.le_normalizer_pCoreOf 2 _ hg
    have hgW₂ : g ∈ normalizer (yamadaW₂ d t : Set G) :=
      (h.normalizer_yamadaV₂_le hW d hK hD).1 hg
    have hgW₃ : g ∈ normalizer (yamadaW₃ d t : Set G) := by
      rw [← hW₃L]
      exact Common.mem_normalizer_inf hgL₃ (mem_normalizer_centralizer hgW₂)
    have hgt : g * t * g⁻¹ ∈ yamadaV₃ d t :=
      hV₂V₃ ((mem_normalizer_iff.1 hg t).1 (mem_sup_right (mem_zpowers t)))
    refine mem_normalizer_of_conj_mem fun x hx => ?_
    rw [← hV₃eq] at hx
    obtain ⟨w, hw, τ, hτ, rfl⟩ := Common.exists_mul_of_le_normalizer ((zpowers_le).2 htW₃N) x hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hτ
    rw [show g * (w * t ^ k) * g⁻¹ = g * w * g⁻¹ * (g * t * g⁻¹) ^ k by rw [conj_zpow]; group]
    exact mul_mem (hW₃V₃ ((mem_normalizer_iff.1 hgW₃ w).1 hw)) (zpow_mem hgt k)
  have hWC : d.W ≤ centralizer ({t} : Set G) := (d.image_le _).trans h.L_le_centralizer
  have hR₃R₅ : yamadaR₃ d t ≤ yamadaR₅ d t := by
    rw [(h.yamada_5_27_2 hW d hK hD).1.1]
    exact le_sup_left
  have hC : yamadaW₃ d t ⊓ centralizer ({t} : Set G) = d.W := by
    refine le_antisymm (fun x hx => ?_) (le_inf (hWW₂.trans hW₂W₃) hWC)
    obtain ⟨hxW₃, hxt⟩ := Subgroup.mem_inf.1 hx
    have hxR₃ : x ∈ yamadaR₃ d t :=
      (hV₃E₃.trans (inf_le_left.trans le_sup_left)) (hW₃V₃ hxW₃)
    have hxR : x ∈ yamadaR d t := by
      rw [← (h.yamada_5_27_1 hW d hK hD).2.2]
      exact Subgroup.mem_inf.2 ⟨hR₃R₅ hxR₃, hxt⟩
    have hxR₂ : x ∈ yamadaR₂ d t := (h.yamadaR₂_inf_centralizer d hK).1 hxR
    have hxV₂ : x ∈ yamadaV₂ d t := by
      rw [← hV₃R₂]
      exact Subgroup.mem_inf.2 ⟨hW₃V₃ hxW₃, hxR₂⟩
    have hxW₂ : x ∈ yamadaW₂ d t := by
      rcases (mem_sup_zpowers_iff_of htt (h.t_mem_normalizer_yamadaW₂ d hK hD).1).1 hxV₂ with
        h1 | ⟨a, ha, rfl⟩
      · exact h1
      · exfalso
        refine htW₃ ?_
        have := mul_mem (inv_mem (hW₂W₃ ha)) hxW₃
        rwa [inv_mul_cancel_left] at this
    rw [← h.yamadaW₂_inf_centralizer d hK hD]
    exact Subgroup.mem_inf.2 ⟨hxW₂, hxt⟩
  haveI := hW₃e
  have hab : ∀ a ∈ yamadaW₃ d t, ∀ b ∈ yamadaW₃ d t, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : yamadaW₃ d t) ⟨b, hb⟩)
  have hae : ∀ a ∈ yamadaW₃ d t, a * a = 1 := fun a ha => by
    rw [← sq]
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := yamadaW₃ d t) a ha
  have h4 : 4 ≤ Nat.card K := hK ▸ h.four_le
  have hcard : 2 * Nat.card (yamadaW₃ d t ⊓ centralizer ({t} : Set G) : Subgroup G) <
      Nat.card (yamadaW₃ d t) := by
    rw [hC, d.cards.2.2.2.1, hW₃c]
    have hq : 2 < Nat.card K ^ 3 :=
      lt_of_lt_of_le (by norm_num : 2 < 4) (h4.trans (Nat.le_self_pow (by norm_num) _))
    calc 2 * Nat.card K ^ 3 < Nat.card K ^ 3 * Nat.card K ^ 3 :=
          Nat.mul_lt_mul_of_pos_right hq (by positivity)
      _ = Nat.card K ^ 6 := by ring
  have h2 : normalizer (yamadaV₃ d t : Set G) ≤ normalizer (yamadaV₂ d t : Set G) := by
    have := normalizer_sup_zpowers_le_inf (A := yamadaW₃ d t) htt htW₃N htW₃ hab hae hcard
    rw [hV₃eq, hC] at this
    rw [(h.yamada_5_23_1 hW d hK hD).1]
    exact this
  exact le_antisymm h1 h2

theorem normalizer_yamadaL₃_le_normalizer_yamadaW₃ (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    normalizer (yamadaL₃ d t : Set G) ≤ normalizer (yamadaW₃ d t : Set G) := by
  obtain ⟨hW₃L₃, hchar⟩ := h.yamada_5_35_5 hW d hK hQ
  have h1 := LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
    ((yamadaW₃ d t).subgroupOf (yamadaL₃ d t))
  rwa [subgroupOf_map_subtype, inf_of_le_left hW₃L₃] at h1

theorem card_normalizer_yamadaL₃_lt (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    Nat.card (normalizer (yamadaL₃ d t : Set G)) <
      2 * Nat.card K ^ 2 * Nat.card (normalizer (yamadaV₂ d t : Set G)) := by
  have hD := hQ.doubling
  obtain ⟨-, hW₃c, hW₃L, -⟩ := h.yamada_5_33_3_uniform hW d hK hQ.doubling
  obtain ⟨hW₃V₃, hV₃N, -, hW₂W₃, htW₃, hV₃eq, -⟩ := h.yamadaW₃_facts hW d hK hD
  have htt := h.t_mul_t
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  obtain ⟨hL₂L₃, -⟩ := h.yamadaL₃_facts hW d hK hD
  have htL₃ : t ∈ yamadaL₃ d t :=
    hL₂L₃ (h.tM_le_yamadaL₂ d hK (mem_sup_right (mem_zpowers t)))
  have hW₃L₃ : yamadaW₃ d t ≤ yamadaL₃ d t := (h.yamada_5_35_5 hW d hK hQ).1
  have hHW₃ := h.normalizer_yamadaL₃_le_normalizer_yamadaW₃ hW d hK hQ
  have hVH : normalizer (yamadaV₂ d t : Set G) ≤ normalizer (yamadaL₃ d t : Set G) :=
    LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hV₂N := h.yamada_5_41_3 hW d hK hQ
  have hWW₂ : d.W ≤ yamadaW₃ d t := (le_sup_left : d.W ≤ yamadaW₂ d t).trans hW₂W₃
  have hmem : ∀ g : normalizer (yamadaL₃ d t : Set G),
      (g : G) * t * (g : G)⁻¹ ∈ yamadaL₃ d t := fun g => (mem_normalizer_iff.1 g.2 t).1 htL₃
  let Φ : normalizer (yamadaL₃ d t : Set G) →
      (yamadaL₃ d t ⧸ (yamadaW₃ d t).subgroupOf (yamadaL₃ d t)) := fun g =>
    QuotientGroup.mk ⟨(g : G) * t * (g : G)⁻¹, hmem g⟩
  have hΦ : ∀ g g' : normalizer (yamadaL₃ d t : Set G), Φ g = Φ g' ↔
      (g : G)⁻¹ * (g' : G) ∈ normalizer (yamadaV₂ d t : Set G) := by
    intro g g'
    show (QuotientGroup.mk ⟨(g : G) * t * (g : G)⁻¹, hmem g⟩ :
      yamadaL₃ d t ⧸ (yamadaW₃ d t).subgroupOf (yamadaL₃ d t)) =
        QuotientGroup.mk ⟨(g' : G) * t * (g' : G)⁻¹, hmem g'⟩ ↔ _
    rw [QuotientGroup.eq, mem_subgroupOf]
    have hgW₃ := hHW₃ g.2
    have hg'W₃ := hHW₃ g'.2
    have hcomp : ((g : G) * t * (g : G)⁻¹)⁻¹ * ((g' : G) * t * (g' : G)⁻¹) =
        (g : G) * (t * ((g : G)⁻¹ * g') * t * ((g : G)⁻¹ * g')⁻¹) * (g : G)⁻¹ := by
      calc ((g : G) * t * (g : G)⁻¹)⁻¹ * ((g' : G) * t * (g' : G)⁻¹) =
          (g : G) * t⁻¹ * (g : G)⁻¹ * ((g' : G) * t * (g' : G)⁻¹) := by group
        _ = (g : G) * t * (g : G)⁻¹ * ((g' : G) * t * (g' : G)⁻¹) := by rw [htinv]
        _ = _ := by group
    show ((g : G) * t * (g : G)⁻¹)⁻¹ * ((g' : G) * t * (g' : G)⁻¹) ∈ yamadaW₃ d t ↔ _
    rw [hcomp]
    constructor
    · intro hx
      have hκ : t * ((g : G)⁻¹ * g') * t * ((g : G)⁻¹ * g')⁻¹ ∈ yamadaW₃ d t := by
        have := (mem_normalizer_iff.1 (inv_mem hgW₃) _).1 hx
        rwa [show (g : G)⁻¹ * ((g : G) * (t * ((g : G)⁻¹ * g') * t * ((g : G)⁻¹ * g')⁻¹) *
          (g : G)⁻¹) * (g : G)⁻¹⁻¹ = t * ((g : G)⁻¹ * g') * t * ((g : G)⁻¹ * g')⁻¹ by group]
          at this
      have huW₃ : (g : G)⁻¹ * g' ∈ normalizer (yamadaW₃ d t : Set G) :=
        mul_mem (inv_mem hgW₃) hg'W₃
      have hgt : ((g : G)⁻¹ * g') * t * ((g : G)⁻¹ * g')⁻¹ ∈ yamadaW₃ d t ⊔ zpowers t := by
        rw [h.conj_t_eq_mul_crossed ((g : G)⁻¹ * g')]
        exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left hκ)
      have := mem_normalizer_sup_zpowers_of_conj_mem huW₃ hgt
      rwa [hV₃eq, ← hV₂N] at this
    · intro hu
      have hκ := h.crossed_mem_W hW d hK hD hu
      exact (mem_normalizer_iff.1 hgW₃ _).1 (hWW₂ hκ)
  have hΦ1 : ∀ g : normalizer (yamadaL₃ d t : Set G), Φ g ≠ QuotientGroup.mk 1 := fun g hg => by
    have h1 := mem_subgroupOf.1 (QuotientGroup.eq.1 hg)
    have h2 : ((g : G) * t * (g : G)⁻¹)⁻¹ ∈ yamadaW₃ d t := by simpa using h1
    exact htW₃ ((mem_normalizer_iff.1 (hHW₃ g.2) t).2 (inv_mem_iff.1 h2))
  let f : normalizer (yamadaL₃ d t : Set G) ⧸
      (normalizer (yamadaV₂ d t : Set G)).subgroupOf (normalizer (yamadaL₃ d t : Set G)) →
      (yamadaL₃ d t ⧸ (yamadaW₃ d t).subgroupOf (yamadaL₃ d t)) := fun q => Φ q.out
  have hf : Function.Injective f := fun q q' hqq' => by
    have h1 := (hΦ q.out q'.out).1 hqq'
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q']
    exact QuotientGroup.eq.2 (mem_subgroupOf.2 h1)
  haveI := Fintype.ofFinite (normalizer (yamadaL₃ d t : Set G) ⧸
      (normalizer (yamadaV₂ d t : Set G)).subgroupOf (normalizer (yamadaL₃ d t : Set G)))
  haveI := Fintype.ofFinite (yamadaL₃ d t ⧸ (yamadaW₃ d t).subgroupOf (yamadaL₃ d t))
  have hlt : Nat.card (normalizer (yamadaL₃ d t : Set G) ⧸
      (normalizer (yamadaV₂ d t : Set G)).subgroupOf (normalizer (yamadaL₃ d t : Set G))) <
      Nat.card (yamadaL₃ d t ⧸ (yamadaW₃ d t).subgroupOf (yamadaL₃ d t)) := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    refine Fintype.card_lt_of_injective_not_surjective f hf fun hs => ?_
    obtain ⟨q, hq⟩ := hs (QuotientGroup.mk 1)
    exact hΦ1 _ hq
  have hq6 : 0 < Nat.card K ^ 6 := by
    have : 0 < Nat.card K := Nat.card_pos
    positivity
  have hX : Nat.card (yamadaL₃ d t ⧸ (yamadaW₃ d t).subgroupOf (yamadaL₃ d t)) =
      2 * Nat.card K ^ 2 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
      ((yamadaW₃ d t).subgroupOf (yamadaL₃ d t))
    rw [Nat.card_congr (subgroupOfEquivOfLe hW₃L₃).toEquiv, hW₃c,
      (h.card_yamadaL₃_R₃ hW d hK hD).1] at h1
    refine Nat.eq_of_mul_eq_mul_right hq6 ?_
    rw [← h1]
    ring
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((normalizer (yamadaV₂ d t : Set G)).subgroupOf (normalizer (yamadaL₃ d t : Set G)))
  rw [Nat.card_congr (subgroupOfEquivOfLe hVH).toEquiv] at h2
  rw [h2]
  rw [hX] at hlt
  exact Nat.mul_lt_mul_of_pos_right hlt (Nat.card_pos (α := normalizer (yamadaV₂ d t : Set G)))

theorem yamada_5_41_4 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    normalizer (yamadaL₂ d t : Set G) = normalizer (yamadaL₃ d t : Set G) ∧
      normalizer (yamadaL₃ d t : Set G) ≤ normalizer (yamadaM₃ d t : Set G) := by
  have hD := hQ.doubling
  obtain ⟨⟨hjoin, -, hN₂N₃⟩, hinf⟩ := h.yamada_5_39_1 hW d hK hQ
  have hV₂N : normalizer (yamadaV₂ d t : Set G) ≤ normalizer (yamadaL₂ d t : Set G) := by
    rw [hjoin]
    exact le_sup_right
  have hVL₆ : normalizer (yamadaV₂ d t : Set G) ≤ normalizer (yamadaL₆ d t : Set G) :=
    hV₂N.trans (le_normalizer_yamadaL₆ d t)
  have hc₂ : Nat.card (normalizer (yamadaL₂ d t : Set G)) =
      Nat.card K ^ 2 * Nat.card (normalizer (yamadaV₂ d t : Set G)) := by
    have h1 := Common.card_sup_mul_card_inf_eq (A := yamadaL₆ d t)
      (B := normalizer (yamadaV₂ d t : Set G)) hVL₆
    rw [← hjoin, hinf, h.card_yamadaL₆ hW d hK hQ, (h.card_yamadaL₃_R₃ hW d hK hD).1] at h1
    have hq8 : 0 < 2 * Nat.card K ^ 8 := by
      have : 0 < Nat.card K := Nat.card_pos
      positivity
    refine Nat.eq_of_mul_eq_mul_right hq8 ?_
    rw [h1]
    ring
  have hN₃N₂ : normalizer (yamadaL₃ d t : Set G) ≤ normalizer (yamadaL₂ d t : Set G) := by
    by_contra hnle
    have hlt : Nat.card (normalizer (yamadaL₂ d t : Set G)) <
        Nat.card (normalizer (yamadaL₃ d t : Set G)) := by
      by_contra hge
      exact hnle (Subgroup.eq_of_le_of_card_ge hN₂N₃ (not_lt.1 hge) ▸ le_rfl)
    obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hN₂N₃
    have hpos : 0 < Nat.card (normalizer (yamadaL₂ d t : Set G)) := Nat.card_pos
    have hk2 : 2 ≤ k := by
      by_contra hk2
      interval_cases k
      · rw [mul_zero] at hk
        omega
      · rw [mul_one] at hk
        omega
    have h1 := h.card_normalizer_yamadaL₃_lt hW d hK hQ
    have h2 : 2 * (Nat.card K ^ 2 * Nat.card (normalizer (yamadaV₂ d t : Set G))) ≤
        Nat.card (normalizer (yamadaL₃ d t : Set G)) := by
      rw [hk, hc₂, mul_comm 2]
      exact Nat.mul_le_mul_left _ hk2
    rw [mul_assoc] at h1
    exact absurd (lt_of_lt_of_le h1 h2) (lt_irrefl _)
  refine ⟨le_antisymm hN₂N₃ hN₃N₂, fun g hg => ?_⟩
  exact mem_normalizer_sup (h.normalizer_yamadaL₃_le_normalizer_yamadaW₃ hW d hK hQ hg)
    ((h.normalizer_yamadaL₂_le d hK hD).1 (hN₃N₂ hg))

end Local

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
