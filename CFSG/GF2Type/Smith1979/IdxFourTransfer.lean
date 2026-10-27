module

public import CFSG.Quasithin.Background.A1cTransferVariants
public import CFSG.LargeExtraspecial.S5Syl

public section

namespace CFSG.GF2Type.Smith1979.IdxFour

open Subgroup CFSG.LargeExtraspecial
open scoped commutatorElement

variable {G : Type} [Group G]

theorem commutator_top_eq_top [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) :
    ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnonab
    apply hab
    have hc : ⁅a, b⁆ ∈ ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ := commutator_mem_commutator (mem_top a) (mem_top b)
    rw [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
    exact hc
  · exact h

theorem mul_mem_iff_of_relIndex_eq_two {M K : Subgroup G} (hidx : K.relIndex M = 2) {a b : G}
    (ha : a ∈ M) (hb : b ∈ M) : a * b ∈ K ↔ (a ∈ K ↔ b ∈ K) := by
  have h2 : (K.subgroupOf M).index = 2 := hidx
  have := Subgroup.mul_mem_iff_of_index_two h2 (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)
  simpa [mem_subgroupOf] using this

theorem commutator_le_of_relIndex_eq_two {M K : Subgroup G} (hidx : K.relIndex M = 2) :
    ⁅M, M⁆ ≤ K := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have hab := mul_mem_iff_of_relIndex_eq_two hidx (M.mul_mem ha hb)
    (M.mul_mem (M.inv_mem ha) (M.inv_mem hb))
  have h1 := mul_mem_iff_of_relIndex_eq_two hidx ha hb
  have h2 := mul_mem_iff_of_relIndex_eq_two hidx (M.inv_mem ha) (M.inv_mem hb)
  rw [commutatorElement_def, show a * b * a⁻¹ * b⁻¹ = (a * b) * (a⁻¹ * b⁻¹) by group, hab, h1, h2,
    K.inv_mem_iff, K.inv_mem_iff]

theorem false_of_conj_not_mem [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    {M K : Subgroup G} (hodd : Nat.Coprime 2 M.index) (hKM : K ≤ M)
    (hKn : ∀ h ∈ M, ∀ k ∈ K, h * k * h⁻¹ ∈ K) (hidx : K.relIndex M = 2) {x : G} (hxM : x ∈ M)
    (hxK : x ∉ K) (hx2 : orderOf x = 2)
    (h : ∀ a : G, a⁻¹ * x * a ∈ M → a⁻¹ * x * a ∉ K) : False := by
  have hfus : ∀ a ∈ (⊤ : Subgroup G), a⁻¹ * x * a ∈ M → x⁻¹ * (a⁻¹ * x * a) ∈ K := by
    intro a _ haM
    rw [mul_mem_iff_of_relIndex_eq_two hidx (M.inv_mem hxM) haM, K.inv_mem_iff]
    exact iff_of_false hxK (h a haM)
  have hindex : Nat.Coprime 2 (M.relIndex ⊤) := by rwa [relIndex_top_right]
  have hx := CFSG.Quasithin.generalized_thompson_transfer_two_subgroup (X := ⊤) le_top hindex hKM
    hKn (commutator_le_of_relIndex_eq_two hidx) hxM hxK hx2 hfus
  rw [commutator_top_eq_top hnonab] at hx
  exact hx (mem_top x)

theorem exists_conj_mem_of_isSylowTwoIn [Finite G] {x g : G} {S L : Subgroup G}
    (hS : S5.IsSylowTwoIn S (centralizer {x})) (hL2 : IsPGroup 2 L)
    (hLC : L ≤ centralizer {g * x * g⁻¹}) :
    ∃ c ∈ centralizer ({x} : Set G), ∀ y ∈ L, c⁻¹ * (g⁻¹ * y * g) * c ∈ S := by
  set L' : Subgroup G := L.map (MulAut.conj g⁻¹).toMonoidHom with hL'
  have hL'C : L' ≤ centralizer {x} := by
    rintro _ ⟨y, hy, rfl⟩
    have hyc := mem_centralizer_singleton_iff.mp (hLC hy)
    rw [mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc g⁻¹ * y * g * x = g⁻¹ * (y * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * y) * g := by rw [hyc]
      _ = x * (g⁻¹ * y * g) := by group
  have hL'2 : IsPGroup 2 L' := hL2.map _
  obtain ⟨S', hS', hLS'⟩ := S5.exists_isSylowTwoIn_ge hL'C hL'2
  obtain ⟨c, hc, hcS⟩ := hS.exists_conj hS'
  refine ⟨c, hc, fun y hy => ?_⟩
  have hy' : g⁻¹ * y * g ∈ L' := ⟨y, hy, by simp [MulAut.conj_apply]⟩
  exact (hcS _).mp (hLS' hy')

theorem card_le_of_isSylowTwoIn [Finite G] {x g : G} {S L : Subgroup G}
    (hS : S5.IsSylowTwoIn S (centralizer {x})) (hL2 : IsPGroup 2 L)
    (hLC : L ≤ centralizer {g * x * g⁻¹}) : Nat.card L ≤ Nat.card S := by
  obtain ⟨c, -, hcS⟩ := exists_conj_mem_of_isSylowTwoIn hS hL2 hLC
  set φ : G →* G := (MulAut.conj (g * c)⁻¹).toMonoidHom with hφ
  have hφy : ∀ y, φ y = c⁻¹ * (g⁻¹ * y * g) * c := fun y => by
    simp [hφ, MulAut.conj_apply, mul_assoc]
  have hLS : L.map φ ≤ S := by
    rintro _ ⟨y, hy, rfl⟩
    rw [hφy]
    exact hcS y hy
  have hinj : Function.Injective φ := (MulAut.conj (g * c)⁻¹).injective
  calc Nat.card L = Nat.card (L.map φ) := (Subgroup.card_map_of_injective hinj).symm
    _ ≤ Nat.card S := Subgroup.card_le_of_le hLS

theorem isSylowTwoIn_centralizer_of_unique [Finite G] {x z : G} {S : Subgroup G}
    (hS : S5.IsSylowTwoIn S (centralizer {x} ⊓ centralizer {z}))
    (huniq : ∀ g : G, g * z * g⁻¹ ∈ centralizer (S : Set G) → g * z * g⁻¹ ∈ ⁅S, S⁆ →
      g * z * g⁻¹ = z)
    (hzC : z ∈ centralizer (S : Set G)) (hzS : z ∈ ⁅S, S⁆) :
    S5.IsSylowTwoIn S (centralizer {x}) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT, hST⟩ := S5.exists_isSylowTwoIn_ge (hS.le.trans inf_le_left) hS.isPGroup
  suffices hEq : S = T by rw [hEq]; exact hT
  by_contra hne
  have hlt : S.subgroupOf T < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => hne (le_antisymm hST fun y hy => ?_)
    have : (⟨y, hy⟩ : T) ∈ S.subgroupOf T := htop ▸ mem_top _
    exact this
  haveI : Finite T := inferInstance
  have hTp : IsPGroup 2 T := hT.isPGroup
  haveI : Group.IsNilpotent T := hTp.isNilpotent
  obtain ⟨n, hnN, hnS⟩ := SetLike.exists_of_lt
    (normalizerCondition_of_isNilpotent (G := T) (S.subgroupOf T) hlt)
  have hnS' : (n : G) ∉ S := hnS
  have hnorm : ∀ s : G, s ∈ S ↔ (n : G) * s * (n : G)⁻¹ ∈ S := by
    intro s
    constructor
    · intro hs
      have := (mem_normalizer_iff.mp hnN ⟨s, hST hs⟩).mp hs
      simpa [mem_subgroupOf] using this
    · intro hs
      have hsT : s ∈ T := by
        have h1 : (n : G) * s * (n : G)⁻¹ ∈ T := hST hs
        have := T.mul_mem (T.mul_mem (T.inv_mem n.2) h1) n.2
        simpa [mul_assoc] using this
      have := (mem_normalizer_iff.mp hnN ⟨s, hsT⟩).mpr (by simpa [mem_subgroupOf] using hs)
      simpa [mem_subgroupOf] using this
  set φ : G →* G := (MulAut.conj (n : G)).toMonoidHom with hφ
  have hφS : S.map φ = S := by
    ext y
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact (hnorm s).mp hs
    · intro hy
      refine ⟨(n : G)⁻¹ * y * (n : G), (hnorm _).mpr ?_, ?_⟩
      · simpa [mul_assoc] using hy
      · simp [hφ, MulAut.conj_apply, mul_assoc]
  have hzC' : (n : G) * z * (n : G)⁻¹ ∈ centralizer (S : Set G) := by
    rw [mem_centralizer_iff]
    intro s hs
    have hs' : (n : G)⁻¹ * s * (n : G) ∈ S := (hnorm _).mpr (by simpa [mul_assoc] using hs)
    have hc := mem_centralizer_iff.mp hzC _ hs'
    calc s * ((n : G) * z * (n : G)⁻¹)
        = (n : G) * (((n : G)⁻¹ * s * (n : G)) * z) * (n : G)⁻¹ := by group
      _ = (n : G) * (z * ((n : G)⁻¹ * s * (n : G))) * (n : G)⁻¹ := by rw [hc]
      _ = (n : G) * z * (n : G)⁻¹ * s := by group
  have hzS' : (n : G) * z * (n : G)⁻¹ ∈ ⁅S, S⁆ := by
    have h1 : φ z ∈ ⁅S.map φ, S.map φ⁆ := by
      rw [← Subgroup.map_commutator]
      exact mem_map_of_mem φ hzS
    rw [hφS] at h1
    simpa [hφ, MulAut.conj_apply] using h1
  have hnz : (n : G) * z * (n : G)⁻¹ = z := huniq n hzC' hzS'
  have hnCz : (n : G) ∈ centralizer ({z} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc (n : G) * z = (n : G) * z * (n : G)⁻¹ * (n : G) := by group
      _ = z * (n : G) := by rw [hnz]
  have hnCx : (n : G) ∈ centralizer ({x} : Set G) := hT.le n.2
  set U : Subgroup G := S ⊔ zpowers (n : G) with hU
  have hUT : U ≤ T := sup_le hST (zpowers_le.mpr n.2)
  have hUC : U ≤ centralizer {x} ⊓ centralizer {z} :=
    sup_le hS.le (zpowers_le.mpr ⟨hnCx, hnCz⟩)
  have hSU : S = U := (hS.eq_of_le le_sup_left hUC (hTp.to_le hUT)).symm
  exact hnS' (hSU ▸ (le_sup_right : zpowers (n : G) ≤ U) (mem_zpowers _))

end CFSG.GF2Type.Smith1979.IdxFour
