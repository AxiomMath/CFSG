module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2421Cfg

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin
open scoped commutatorElement

namespace Lin2Hyp0

section Cyc

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}
  (E : Lin2Hyp0) (hcfg : Lin2Cfg G T M H S L n D)

include E hcfg

theorem exists_zpowers_S : ∃ s₀ ∈ S, S = thompsonJ S ⊔ Subgroup.zpowers s₀ := by
  obtain ⟨B, hB⟩ := E.exists_B hcfg
  obtain ⟨⟨hFcyc, -, hRFS, -, -⟩, -⟩ := E.h12 G T M H S L D n hcfg B hB
  obtain ⟨g, hg⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top _).1 hFcyc
  refine ⟨g, ?_, ?_⟩
  · have : g ∈ S ⊓ Subgroup.normalizer (B : Set G) := hg ▸ Subgroup.mem_zpowers g
    exact this.1
  · calc S = thompsonJ S ⊔ (S ⊓ Subgroup.normalizer (B : Set G)) := hRFS.symm
      _ = thompsonJ S ⊔ Subgroup.zpowers g := by rw [hg]

theorem card_U' : Nat.card (blockU L) = 2 ^ (2 * n) * Nat.card (centerOf L) := by
  rw [lin2_card_U hcfg.lin2, blockZ_eq_centerOf hcfg.charTwo_L (E.OL hcfg)]

theorem commutator_inf_centralizer_le (a : G) :
    ⁅thompsonJ S ⊓ Subgroup.centralizer ({a} : Set G),
        thompsonJ S ⊓ Subgroup.centralizer ({a} : Set G)⁆ ≤
      centerOf (thompsonJ S) ⊓ Subgroup.centralizer ({a} : Set G) := by
  refine le_inf ((Subgroup.commutator_mono inf_le_left inf_le_left).trans
    (E.R_comm_le_centerOf hcfg)) ?_
  rw [Subgroup.commutator_le]
  intro x hx y hy
  have hx' : Commute x a := Subgroup.mem_centralizer_singleton_iff.1 hx.2
  have hy' : Commute y a := Subgroup.mem_centralizer_singleton_iff.1 hy.2
  have : Commute ⁅x, y⁆ a := by
    rw [commutatorElement_def]
    exact (((hx'.mul_left hy').mul_left hx'.inv_left).mul_left hy'.inv_left)
  exact Subgroup.mem_centralizer_singleton_iff.2 this

theorem not_commutative_of_card_omegaOne {I : Subgroup G} (hIR : I ≤ thompsonJ S) {m : ℕ}
    (hm : 0 < m) (hI : Nat.card I = 2 ^ (3 * m)) (hΩ : Nat.card (omegaOneOf I) = 2 ^ m) :
    ¬ ∀ i ∈ I, ∀ j ∈ I, i * j = j * i := by
  intro hcomm
  classical
  let φ : I →* I :=
    { toFun := fun v => v * v
      map_one' := by simp
      map_mul' := by
        intro v w
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        have hc : (w : G) * v = v * w := hcomm w w.2 v v.2
        calc (v : G) * w * ((v : G) * w) = (v : G) * (w * v) * w := by group
          _ = (v : G) * (v * w) * w := by rw [hc]
          _ = (v : G) * v * ((w : G) * w) := by group }
  have hker : ∀ v : I, φ v = 1 → (v : G) ∈ omegaOneOf I := by
    intro v hv
    apply Subgroup.subset_closure
    refine ⟨v.2, ?_⟩
    have := congrArg Subtype.val hv
    simpa [φ, pow_two] using this
  have hrange : ∀ y : I, y ∈ φ.range → (y : G) ∈ omegaOneOf I := by
    intro y hy
    obtain ⟨v, rfl⟩ := hy
    apply Subgroup.subset_closure
    refine ⟨(φ v).2, ?_⟩
    have h4 := E.R_pow_four hcfg (hIR v.2)
    show ((v : G) * v) ^ 2 = 1
    calc ((v : G) * v) ^ 2 = (v : G) ^ 4 := by rw [← pow_two, ← pow_mul]
      _ = 1 := h4
  have hk : Nat.card φ.ker ≤ Nat.card (omegaOneOf I) := by
    refine Nat.card_le_card_of_injective (fun v => ⟨((v : I) : G), hker v v.2⟩) ?_
    intro v w hvw
    apply Subtype.ext
    apply Subtype.ext
    simpa using hvw
  have hr : Nat.card φ.range ≤ Nat.card (omegaOneOf I) := by
    refine Nat.card_le_card_of_injective (fun y => ⟨((y : I) : G), hrange y y.2⟩) ?_
    intro v w hvw
    apply Subtype.ext
    apply Subtype.ext
    simpa using hvw
  have hmul : Nat.card φ.ker * φ.ker.index = Nat.card I := Subgroup.card_mul_index φ.ker
  rw [Subgroup.index_ker] at hmul
  have h1 : Nat.card I ≤ Nat.card (omegaOneOf I) ^ 2 := by
    rw [← hmul, sq]
    exact Nat.mul_le_mul hk hr
  rw [hI, hΩ, ← pow_mul] at h1
  have h2 : 3 * m ≤ m * 2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h1
  omega

end Cyc

end Lin2Hyp0

end CFSG.QuasithinUnique.Lin2
