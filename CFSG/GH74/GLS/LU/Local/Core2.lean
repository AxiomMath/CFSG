module

public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.GH74.GLS.LU.Local

open Subgroup
open scoped Pointwise

theorem card_sup_mul_card_inf_of_commute {G : Type*} [Group G] [Finite G] {H K : Subgroup G}
    (hc : ∀ a ∈ H, ∀ b ∈ K, a * b = b * a) :
    Nat.card ↥(H ⊔ K) * Nat.card ↥(H ⊓ K) = Nat.card H * Nat.card K := by
  have hcomm : ∀ (m : H) (n : K), Commute (H.subtype m) (K.subtype n) :=
    fun m n => hc m m.2 n n.2
  set φ : (H × K) →* G := MonoidHom.noncommCoprod H.subtype K.subtype hcomm with hφdef
  have hrange : φ.range = H ⊔ K := by
    rw [hφdef, MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  have hφ : ∀ x : H × K, φ x = (x.1 : G) * (x.2 : G) := fun x => by
    rw [hφdef, MonoidHom.noncommCoprod_apply]; rfl
  have key : ∀ x : φ.ker, (x.1.1 : G) * (x.1.2 : G) = 1 := fun x => by
    rw [← hφ]; exact x.2
  have hK : ∀ x : φ.ker, (x.1.1 : G) ∈ K := by
    intro x
    have h2 : (x.1.2 : G) = (x.1.1 : G)⁻¹ := eq_inv_of_mul_eq_one_right (key x)
    have h3 : (x.1.1 : G) = (x.1.2 : G)⁻¹ := by rw [h2, inv_inv]
    rw [h3]; exact K.inv_mem x.1.2.2
  let e : φ.ker ≃ ↥(H ⊓ K) :=
    { toFun := fun x => ⟨(x.1.1 : G), x.1.1.2, hK x⟩
      invFun := fun y => ⟨(⟨(y : G), y.2.1⟩, ⟨(y : G)⁻¹, K.inv_mem y.2.2⟩), by
        rw [MonoidHom.mem_ker, hφ]; simp⟩
      left_inv := by
        intro x
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · apply Subtype.ext
          exact (eq_inv_of_mul_eq_one_right (key x)).symm
      right_inv := fun y => rfl }
  have h1 := Subgroup.card_mul_index φ.ker
  rw [Subgroup.index_ker, hrange, Nat.card_prod, Nat.card_congr e] at h1
  rw [mul_comm]
  exact h1

theorem card_map_conj {G : Type*} [Group G] (H : Subgroup G) (c : G) :
    Nat.card ↥(H.map (MulAut.conj c).toMonoidHom) = Nat.card ↥H :=
  (Nat.card_congr ((MulAut.conj c).subgroupMap H).toEquiv).symm

theorem exists_conj_mem_sylow_of_le {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) {C : Subgroup G} (hSC : (S : Subgroup G) ≤ C) {s : G} (hs : s ∈ C)
    (hsp : ∃ n : ℕ, orderOf s = p ^ n) : ∃ c ∈ C, c⁻¹ * s * c ∈ (S : Subgroup G) := by
  obtain ⟨n, hn⟩ := hsp
  let S' : Sylow p C := S.subtype hSC
  let x : C := ⟨s, hs⟩
  have hxo : orderOf x = p ^ n := by
    rw [← hn]; exact Subgroup.orderOf_mk s hs
  have hxp : IsPGroup p (zpowers x) := IsPGroup.of_card (n := n) (by rw [Nat.card_zpowers, hxo])
  obtain ⟨Q, hQ⟩ := hxp.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C Q S'
  have hxQ : x ∈ (Q : Subgroup C) := hQ (mem_zpowers x)
  have h1 : MulAut.conj c x ∈ (MulAut.conj c • (Q : Set C)) := Set.smul_mem_smul_set hxQ
  rw [← Sylow.coe_smul, hc] at h1
  have h2 : (c : G) * s * (c : G)⁻¹ ∈ (S : Subgroup G) := by
    have : (MulAut.conj c x : C) ∈ (S' : Subgroup C) := h1
    rw [Sylow.coe_subtype] at this
    exact this
  refine ⟨(c : G)⁻¹, C.inv_mem c.2, ?_⟩
  simpa using h2

theorem perfect_le_of_sup_eq_top_of_isPGroup {X : Type*} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] {N S K : Subgroup X} [N.Normal] (hNS : N ⊔ S = ⊤) (hS : IsPGroup p S)
    (hK : ⁅K, K⁆ = K) : K ≤ N := by
  let π : X →* X ⧸ N := QuotientGroup.mk' N
  have hmap : S.map π = ⊤ := by
    have h1 : (N ⊔ S).map π = ⊤ := by
      rw [hNS, Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective N)]
    rw [Subgroup.map_sup] at h1
    have hN : N.map π = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨n, hn, rfl⟩
      simpa [π] using hn
    rwa [hN, bot_sup_eq] at h1
  have hsurj : Function.Surjective (π.comp S.subtype) := by
    intro y
    have : y ∈ S.map π := by rw [hmap]; trivial
    obtain ⟨s, hs, rfl⟩ := this
    exact ⟨⟨s, hs⟩, rfl⟩
  have hQ : IsPGroup p (X ⧸ N) := hS.of_surjective _ hsurj
  have hnil : Group.IsNilpotent (X ⧸ N) := hQ.isNilpotent
  set M : Subgroup (X ⧸ N) := K.map π with hM
  have hMp : ⁅M, M⁆ = M := by
    rw [hM, ← Subgroup.map_commutator, hK]
  by_contra hKN
  have hMne : M ≠ ⊥ := by
    intro hbot
    apply hKN
    intro k hk
    have : π k ∈ M := ⟨k, hk, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact (QuotientGroup.eq_one_iff k).mp this
  have : Nontrivial ↥M := (Subgroup.nontrivial_iff_ne_bot M).mpr hMne
  have : Group.IsPerfect ↥M := Subgroup.isPerfect_iff.mpr hMp
  exact Group.IsPerfect.not_isSolvable ↥M
    (Group.isSolvable_of_isSolvable_injective M.subtype_injective)

theorem exists_conj_eq_of_card_le {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) {C : Subgroup G} (hSC : (S : Subgroup G) ≤ C) {T : Subgroup G} (hTC : T ≤ C)
    (hT : IsPGroup p T) (hcard : Nat.card (S : Subgroup G) ≤ Nat.card T) :
    ∃ c ∈ C, ∀ x : G, x ∈ T ↔ (c : G)⁻¹ * x * c ∈ (S : Subgroup G) := by
  let S₂ : Sylow p C := S.subtype hSC
  let T₂ : Subgroup C := T.subgroupOf C
  have hT₂ : IsPGroup p T₂ := hT.of_equiv (Subgroup.subgroupOfEquivOfLe hTC).symm
  obtain ⟨Q, hQ⟩ := hT₂.exists_le_sylow
  have hcS₂ : Nat.card (S₂ : Subgroup C) = Nat.card (S : Subgroup G) := by
    rw [Sylow.coe_subtype]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSC).toEquiv
  have hcT₂ : Nat.card T₂ = Nat.card T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTC).toEquiv
  have hQcard : Nat.card (Q : Subgroup C) = Nat.card (S₂ : Subgroup C) := by
    rw [Sylow.card_eq_multiplicity Q, Sylow.card_eq_multiplicity S₂]
  have hTQ : T₂ = (Q : Subgroup C) := by
    apply Subgroup.eq_of_le_of_card_ge hQ
    rw [hQcard, hcS₂, hcT₂]
    exact hcard
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C S₂ Q
  have key : ∀ y : C, y ∈ (Q : Subgroup C) ↔ c⁻¹ * y * c ∈ (S₂ : Subgroup C) := by
    intro y
    rw [← hc]
    show y ∈ ((c • S₂ : Sylow p C) : Set C) ↔ _
    rw [Sylow.coe_smul, Set.mem_smul_set_iff_inv_smul_mem]
    show (MulAut.conj c)⁻¹ y ∈ (S₂ : Set C) ↔ _
    have : (MulAut.conj c)⁻¹ y = c⁻¹ * y * c := by
      simp
    rw [this]
    rfl
  refine ⟨(c : G), c.2, fun x => ?_⟩
  constructor
  · intro hx
    have hxC : x ∈ C := hTC hx
    have h1 : (⟨x, hxC⟩ : C) ∈ (Q : Subgroup C) := by rw [← hTQ]; exact hx
    have h5 := (key ⟨x, hxC⟩).mp h1
    rw [Sylow.coe_subtype] at h5
    exact h5
  · intro hx
    have hxC : x ∈ C := by
      have h0 : (c : G) * ((c : G)⁻¹ * x * (c : G)) * (c : G)⁻¹ ∈ C :=
        C.mul_mem (C.mul_mem c.2 (hSC hx)) (C.inv_mem c.2)
      have e : (c : G) * ((c : G)⁻¹ * x * (c : G)) * (c : G)⁻¹ = x := by group
      rw [e] at h0
      exact h0
    have h5 : c⁻¹ * (⟨x, hxC⟩ : C) * c ∈ (S₂ : Subgroup C) := by
      rw [Sylow.coe_subtype]
      exact hx
    have h1 := (key ⟨x, hxC⟩).mpr h5
    rw [← hTQ] at h1
    exact h1

theorem le_normalizer_of_sylow_trick {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) {C R G₀ T : Subgroup G} (hSC : (S : Subgroup G) ≤ C)
    (hR : ∀ r ∈ R, r ∈ normalizer (G₀ : Set G))
    (hCRS : ∀ c ∈ C, ∃ r ∈ R, ∃ s ∈ (S : Subgroup G), c = r * s)
    (hTG : T ≤ G₀) (hTC : T ≤ C) (hTp : IsPGroup p T)
    (hcard : Nat.card (S : Subgroup G) ≤ Nat.card T) :
    (S : Subgroup G) ≤ G₀ ∧ ∀ c ∈ C, c ∈ normalizer (G₀ : Set G) := by
  obtain ⟨g, hgC, hg⟩ := exists_conj_eq_of_card_le S hSC hTC hTp hcard
  obtain ⟨r, hr, s, hs, hgrs⟩ := hCRS g hgC
  have hSG : (S : Subgroup G) ≤ G₀ := by
    intro x hx
    have hy : r * x * r⁻¹ ∈ T := by
      rw [hg]
      have : (g : G)⁻¹ * (r * x * r⁻¹) * g = s⁻¹ * x * s := by
        rw [hgrs]; group
      rw [this]
      exact (S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem ((S : Subgroup G).inv_mem hs) hx) hs
    have h1 : r * x * r⁻¹ ∈ G₀ := hTG hy
    have hrinv : r⁻¹ ∈ normalizer (G₀ : Set G) := inv_mem (hR r hr)
    have h2 := (mem_normalizer_iff.mp hrinv (r * x * r⁻¹)).mp h1
    have e : r⁻¹ * (r * x * r⁻¹) * r⁻¹⁻¹ = x := by group
    rw [e] at h2
    exact h2
  refine ⟨hSG, fun c hc => ?_⟩
  obtain ⟨r', hr', s', hs', rfl⟩ := hCRS c hc
  exact mul_mem (hR r' hr') (Subgroup.le_normalizer (hSG hs'))

end CFSG.GH74.GLS.LU.Local
