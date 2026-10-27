module

public import CFSG.GH74.GLS.LU.Local.FiveL66b

public section

namespace CFSG.GH74.GLS.LU.Local.Five

section Ncount

variable {G : Type} [Group G]

abbrev USharp (z u : G) : Type := {a : G // a ∈ UU z u ∧ a ≠ 1}

theorem conj_mem_USharp {z u n a : G} (hn : n ∈ NN z u) (ha : a ∈ UU z u ∧ a ≠ 1) :
    n * a * n⁻¹ ∈ UU z u ∧ n * a * n⁻¹ ≠ 1 := by
  refine ⟨(Subgroup.mem_normalizer_iff.mp hn a).mp ha.1, ?_⟩
  intro h
  apply ha.2
  calc a = n⁻¹ * (n * a * n⁻¹) * n := by group
    _ = 1 := by rw [h]; group

@[expose] def conjUSharp {z u : G} (n : G) (hn : n ∈ NN z u) : Equiv.Perm (USharp z u) where
  toFun a := ⟨n * a * n⁻¹, conj_mem_USharp hn a.2⟩
  invFun a := ⟨n⁻¹ * a * n, by simpa using conj_mem_USharp (inv_mem hn) a.2⟩
  left_inv a := Subtype.ext (by
    show n⁻¹ * (n * (a : G) * n⁻¹) * n = a
    group)
  right_inv a := Subtype.ext (by
    show n * (n⁻¹ * (a : G) * n) * n⁻¹ = a
    group)

@[expose] def rhoUSharp (z u : G) : ↥(NN z u) →* Equiv.Perm (USharp z u) where
  toFun n := conjUSharp n.1 n.2
  map_one' := by
    ext a
    simp [conjUSharp]
  map_mul' m n := by
    ext a
    simp [conjUSharp, mul_assoc]

theorem rhoUSharp_apply {z u : G} (n : ↥(NN z u)) (a : USharp z u) :
    ((rhoUSharp z u n a : USharp z u) : G) = (n : G) * a * (n : G)⁻¹ := rfl

theorem ker_rhoUSharp {z u : G} (hz1 : z ≠ 1) (hu1 : u ≠ 1) :
    (rhoUSharp z u).ker = (PP z u).subgroupOf (NN z u) := by
  ext n
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    rw [mem_PP]
    have hz : z ∈ UU z u := Subgroup.mem_sup_left (Subgroup.mem_zpowers z)
    have hu : u ∈ UU z u := Subgroup.mem_sup_right (Subgroup.mem_zpowers u)
    have h1 : n * z * n⁻¹ = z :=
      congrArg (fun σ : Equiv.Perm (USharp z u) => ((σ ⟨z, hz, hz1⟩ : USharp z u) : G)) h
    have h2 : n * u * n⁻¹ = u :=
      congrArg (fun σ : Equiv.Perm (USharp z u) => ((σ ⟨u, hu, hu1⟩ : USharp z u) : G)) h
    exact ⟨mul_inv_eq_iff_eq_mul.mp h1, mul_inv_eq_iff_eq_mul.mp h2⟩
  · intro hn
    refine Equiv.ext fun a => Subtype.ext ?_
    exact mul_inv_eq_iff_eq_mul.mpr (Subgroup.mem_centralizer_iff.mp hn a.1 a.2.1).symm

theorem USharp_cases [Finite G] {z u : G} (hz2 : z * z = 1) (hu2 : u * u = 1) (hzu : z * u = u * z)
    (d : USharp z u) : (d : G) = z ∨ (d : G) = u ∨ (d : G) = z * u := by
  rcases (mem_UU_iff hz2 hu2 hzu).mp d.2.1 with h | h | h | h
  · exact absurd h d.2.2
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem perm_USharp_eq_one_of_fix [Finite G] {z u : G} (hz2 : z * z = 1) (hu2 : u * u = 1)
    (hzu : z * u = u * z) (hz1 : z ≠ 1) (hu1 : u ≠ 1) {σ : Equiv.Perm (USharp z u)}
    {a b : USharp z u} (ha : (a : G) = z) (hb : (b : G) = u) (hσa : σ a = a) (hσb : σ b = b) :
    σ = 1 := by
  refine Equiv.ext fun c => ?_
  have hca : ∀ d : USharp z u, (d : G) = z → d = a := fun d hd => Subtype.ext (hd.trans ha.symm)
  have hcb : ∀ d : USharp z u, (d : G) = u → d = b := fun d hd => Subtype.ext (hd.trans hb.symm)
  rcases USharp_cases hz2 hu2 hzu c with h | h | h
  · rw [hca c h]
    exact hσa
  · rw [hcb c h]
    exact hσb
  · rcases USharp_cases hz2 hu2 hzu (σ c) with h' | h' | h'
    · exfalso
      have hc : c = a := σ.injective ((hca _ h').trans hσa.symm)
      have : z * u = z := by rw [← h, hc, ha]
      exact hu1 (mul_eq_left.mp this)
    · exfalso
      have hc : c = b := σ.injective ((hcb _ h').trans hσb.symm)
      have : z * u = u := by rw [← h, hc, hb]
      exact hz1 (mul_eq_right.mp this)
    · exact Subtype.ext (h'.trans h.symm)

theorem rhoUSharp_surjective [Finite G] {z u w x : G} (hz2 : z * z = 1) (hu2 : u * u = 1)
    (hzu : z * u = u * z) (hz1 : z ≠ 1) (hu1 : u ≠ 1) (huz : u ≠ z)
    (hwz : w * z * w⁻¹ = z) (hwu : w * u * w⁻¹ = u * z) (hxz : x * z * x⁻¹ = u)
    (hxu : x * u * x⁻¹ = z * u) : Function.Surjective (rhoUSharp z u) := by
  intro σ
  have hzU : z ∈ UU z u := Subgroup.mem_sup_left (Subgroup.mem_zpowers z)
  have huU : u ∈ UU z u := Subgroup.mem_sup_right (Subgroup.mem_zpowers u)
  let a : USharp z u := ⟨z, hzU, hz1⟩
  let b : USharp z u := ⟨u, huU, hu1⟩
  have hab : ((σ a : USharp z u) : G) ≠ (σ b : USharp z u) := fun h =>
    huz (congrArg Subtype.val (σ.injective (Subtype.ext h))).symm
  obtain ⟨m, -, hmz, hmu⟩ := exists_perm_rep hz2 hu2 hzu hwz hwu hxz hxu (σ a).2.1 (σ b).2.1
    (σ a).2.2 (σ b).2.2 hab
  have hm : m ∈ NN z u :=
    mem_NN_of_conj (by rw [hmz]; exact (σ a).2.1) (by rw [hmu]; exact (σ b).2.1)
  refine ⟨⟨m, hm⟩, ?_⟩
  have key : σ⁻¹ * rhoUSharp z u ⟨m, hm⟩ = 1 := by
    refine perm_USharp_eq_one_of_fix hz2 hu2 hzu hz1 hu1 (a := a) (b := b) rfl rfl ?_ ?_
    · have : rhoUSharp z u ⟨m, hm⟩ a = σ a := Subtype.ext hmz
      show σ⁻¹ (rhoUSharp z u ⟨m, hm⟩ a) = a
      rw [this]
      simp
    · have : rhoUSharp z u ⟨m, hm⟩ b = σ b := Subtype.ext hmu
      show σ⁻¹ (rhoUSharp z u ⟨m, hm⟩ b) = b
      rw [this]
      simp
  exact (inv_mul_eq_one.mp key).symm

theorem card_USharp [Finite G] {z u : G} (hz2 : z * z = 1) (hu2 : u * u = 1) (hzu : z * u = u * z)
    (hz1 : z ≠ 1) (hu1 : u ≠ 1) (huz : u ≠ z) : Nat.card (USharp z u) = 3 := by
  have hzu1 : z * u ≠ 1 := fun h => huz (mul_left_cancel (h.trans hz2.symm))
  have hzz : z * u ≠ z := fun h => hu1 (mul_eq_left.mp h)
  have huu : z * u ≠ u := fun h => hz1 (mul_eq_right.mp h)
  have e : USharp z u ≃ ↥({z, u, z * u} : Set G) := Equiv.subtypeEquivRight fun a => by
    rw [mem_UU_iff hz2 hu2 hzu]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h | h | h | h, h1⟩
      · exact absurd h h1
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · rintro (h | h | h)
      · exact ⟨Or.inr (Or.inl h), h ▸ hz1⟩
      · exact ⟨Or.inr (Or.inr (Or.inl h)), h ▸ hu1⟩
      · exact ⟨Or.inr (Or.inr (Or.inr h)), h ▸ hzu1⟩
  rw [Nat.card_congr e, Nat.card_coe_set_eq,
    Set.ncard_insert_of_notMem (by simp [huz.symm, hzz.symm]), Set.ncard_pair huu.symm]

end Ncount

theorem card_NN_eq_six_mul_card_PP {G : Type} [Group G] [Finite G] {z u w x : G}
    (hz2 : z * z = 1) (hu2 : u * u = 1) (hzu : z * u = u * z) (hz1 : z ≠ 1)
    (hu1 : u ≠ 1) (huz : u ≠ z)
    (hwz : w * z * w⁻¹ = z) (hwu : w * u * w⁻¹ = u * z) (hxz : x * z * x⁻¹ = u)
    (hxu : x * u * x⁻¹ = z * u) :
    Nat.card ↥(NN z u) = 6 * Nat.card ↥(PP z u) := by
  have h := Subgroup.card_ker_mul_card_of_surjective
    (rhoUSharp_surjective hz2 hu2 hzu hz1 hu1 huz hwz hwu hxz hxu)
  rw [ker_rhoUSharp hz1 hu1, Nat.card_perm, card_USharp hz2 hu2 hzu hz1 hu1 huz,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.centralizer_le_normalizer _)).toEquiv]
    at h
  rw [← h, mul_comm]
  rfl

end CFSG.GH74.GLS.LU.Local.Five
