module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A7Klein
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma32K
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma35
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdBasic

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Id2519
open Equiv Equiv.Perm

section Klein

variable {G : Type*} [Group G] [Finite G]

theorem klein_mem_cases {U : Subgroup G} (hU4 : Nat.card U = 4) (hU2 : ∀ u ∈ U, u * u = 1)
    {z a : G} (hz : z ∈ U) (ha : a ∈ U) (hz1 : z ≠ 1) (ha1 : a ≠ 1) (haz : a ≠ z) {u : G}
    (hu : u ∈ U) : u = 1 ∨ u = z ∨ u = a ∨ u = a * z := by
  have hz2 := hU2 z hz
  have h1 : (1 : G) ≠ z := fun h => hz1 h.symm
  have h2 : (1 : G) ≠ a := fun h => ha1 h.symm
  have h3 : (1 : G) ≠ a * z := by
    intro h
    apply haz
    have : a = z⁻¹ := eq_inv_of_mul_eq_one_left h.symm
    rw [this]
    exact inv_eq_of_mul_eq_one_right hz2
  have h4 : z ≠ a := fun h => haz h.symm
  have h5 : z ≠ a * z := by
    intro h
    apply ha1
    have : 1 * z = a * z := by rw [one_mul]; exact h
    exact (mul_right_cancel this).symm
  have h6 : a ≠ a * z := by
    intro h
    apply hz1
    have : a * 1 = a * z := by rw [mul_one]; exact h
    exact (mul_left_cancel this).symm
  have hsub : ({1, z, a, a * z} : Set G) ⊆ (U : Set G) := by
    intro w hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact U.one_mem
    · exact hz
    · exact ha
    · exact U.mul_mem ha hz
  have hn1 : (1 : G) ∉ ({z, a, a * z} : Set G) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨h1, h2, h3⟩
  have hn2 : z ∉ ({a, a * z} : Set G) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨h4, h5⟩
  have hcard : ({1, z, a, a * z} : Set G).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem hn1, Set.ncard_insert_of_notMem hn2, Set.ncard_pair h6]
  have hU : (U : Set G).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact hU4
  have heq : ({1, z, a, a * z} : Set G) = (U : Set G) :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hcard, hU])
  have : u ∈ ({1, z, a, a * z} : Set G) := by rw [heq]; exact hu
  simpa using this

end Klein

section Core

variable {G : Type} [Group G]

theorem a7_core {K P₀ : Subgroup G} (hP₀K : P₀ ≤ K) (hP₀ : Nat.card P₀ = 8)
    (e : K ≃* alternatingGroup (Fin 7)) {x : G} (hxK : x ∈ Subgroup.normalizer (K : Set G))
    (hxP : ∀ g ∈ P₀, x⁻¹ * g * x ∈ P₀) {a z : G} (ha : a ∈ P₀) (hz : z ∈ P₀)
    (ha2 : a * a = 1) (hz2 : z * z = 1) (haz : a * z = z * a) (hxz : x⁻¹ * z * x = z)
    (hz1 : z ≠ 1) (ha1 : a ≠ 1) (haz' : a ≠ z) (hca : x⁻¹ * a * x ≠ a)
    (hcaz : x⁻¹ * a * x ≠ a * z) : False := by
  obtain ⟨α, hα⟩ := exists_conjAut hxK
  set D : Subgroup (alternatingGroup (Fin 7)) := (P₀.subgroupOf K).map e.toMonoidHom with hD
  have hPK : Nat.card (P₀.subgroupOf K) = 8 := by
    rw [← hP₀]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP₀K).toEquiv
  have hDcard : Nat.card D = 8 := by
    rw [hD, Subgroup.card_map_of_injective e.injective, hPK]
  have hmemD : ∀ k : K, (k : G) ∈ P₀ → e k ∈ D := fun k hk =>
    Subgroup.mem_map_of_mem e.toMonoidHom (show k ∈ P₀.subgroupOf K from hk)
  let A : K := ⟨a, hP₀K ha⟩
  let Z : K := ⟨z, hP₀K hz⟩
  have hAA : A * A = 1 := Subtype.ext ha2
  have hZZ : Z * Z = 1 := Subtype.ext hz2
  have hAZ : A * Z = Z * A := Subtype.ext haz
  have hαZ : α Z = Z := Subtype.ext (by rw [hα]; exact hxz)
  have hαA : ((α A : K) : G) = x⁻¹ * a * x := hα A
  have hαAmem : ((α A : K) : G) ∈ P₀ := by rw [hαA]; exact hxP a ha
  let β : MulAut (alternatingGroup (Fin 7)) := (e.symm.trans α).trans e
  obtain ⟨π, hπ⟩ :=
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by norm_num)
      (by norm_num)).2 β
  have hπapp : ∀ g : alternatingGroup (Fin 7),
      π * (g : Perm (Fin 7)) * π⁻¹ = ((β g : alternatingGroup (Fin 7)) : Perm (Fin 7)) := by
    intro g
    have := MulAut.conjNormal_apply (H := alternatingGroup (Fin 7)) π g
    rw [hπ] at this
    exact this.symm
  have hβ : ∀ k : K, β (e k) = e (α k) := fun k => by simp [β]
  have e1 : ∀ k : K, e k = 1 → k = 1 := fun k h => e.injective (h.trans (map_one e).symm)
  have e2 : ∀ k : K, α k = 1 → k = 1 := fun k h => α.injective (h.trans (map_one α).symm)
  refine alt7_no_swap D hDcard (e A) (e (α A)) (e Z) (hmemD A ha) (hmemD (α A) hαAmem)
    (hmemD Z hz) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ π ?_ ?_
  · rw [← map_mul, hAA, map_one]
  · rw [← map_mul, ← map_mul, hAA, map_one, map_one]
  · rw [← map_mul, hZZ, map_one]
  · rw [← map_mul, ← map_mul, hAZ]
  · rw [← map_mul, ← map_mul]
    congr 1
    calc α A * Z = α A * α Z := by rw [hαZ]
      _ = α (A * Z) := (map_mul α A Z).symm
      _ = α (Z * A) := by rw [hAZ]
      _ = α Z * α A := map_mul α Z A
      _ = Z * α A := by rw [hαZ]
  · intro h
    exact hz1 (congrArg Subtype.val (e1 Z h))
  · intro h
    exact ha1 (congrArg Subtype.val (e1 A h))
  · intro h
    exact haz' (congrArg Subtype.val (e.injective h))
  · intro h
    exact ha1 (congrArg Subtype.val (e2 A (e1 _ h)))
  · intro h
    have h' : α A = Z := e.injective h
    rw [← hαZ] at h'
    exact haz' (congrArg Subtype.val (α.injective h'))
  · intro h
    have h' : α A = A := e.injective h
    exact hca (by rw [← hαA, h'])
  · intro h
    have h' : α A = A * Z := by rw [← map_mul] at h; exact e.injective h
    exact hcaz (by rw [← hαA, h']; rfl)
  · rw [hπapp, hβ]
  · rw [hπapp, hβ, hαZ]

end Core

section Excl

variable {G : Type} [Group G] [Finite G] {T M H S L K : Subgroup G} {s x z₁ z₂ : G}

theorem k32_exclA7 (ctx : K32Ctx T M H S L s x z₁ z₂ K)
    (hpre : A3A3Kpre T M H S L s x z₁ z₂ K) (h : Nonempty (↥K ≃* alternatingGroup (Fin 7))) :
    False := by
  obtain ⟨e⟩ := h
  have hcs := ctx.a3.cs
  have h3 := ctx.a3.a3
  have hA4 : IsA4Block L (blockU L) := IsA4Block.of_alt3 hcs.block.1.1 h3
  have hUK : blockU L ≤ K := hA4.le.trans hpre.L_le_K
  have hUR : blockU L ≤ baum S := blockU_le_baum hcs h3
  have hUS : blockU L ≤ sOne S x := hUR.trans le_sup_left
  have hK : Nat.card ↥K = 2520 := by rw [Nat.card_congr e.toEquiv, card_alt7]
  have hSyl : IsSylowTwoOf (sOne S x ⊓ K) K :=
    A4.isSylowTwoOf_inf_normal ctx.sylow ctx.comp.1 hpre.K_norm
  have hP8 : Nat.card ↥(sOne S x ⊓ K) = 8 := by
    obtain ⟨n, hn⟩ := hSyl.2.1.exists_card_eq
    have hcard : Nat.card ↥K = Nat.card ↥(sOne S x ⊓ K) * (sOne S x ⊓ K).relIndex K :=
      C5.card_eq_card_mul_relIndex hSyl.1
    have hodd : (sOne S x ⊓ K).relIndex K % 2 = 1 := Nat.two_dvd_ne_zero.mp hSyl.2.2
    rw [hK, hn] at hcard
    have hn3 : n ≤ 3 := by
      by_contra hn4
      have h16 : 2 ^ 4 ∣ 2 ^ n := pow_dvd_pow 2 (by omega)
      have h2520 : 2 ^ n ∣ 2520 := ⟨_, hcard⟩
      have := h16.trans h2520
      omega
    have hn3' : 3 ≤ n := by
      by_contra hn2
      interval_cases n <;> omega
    rw [hn, le_antisymm hn3 hn3']
    norm_num
  have hxK : x ∈ Subgroup.normalizer (K : Set G) :=
    hpre.K_norm (Subgroup.mem_centralizer_singleton_iff.mpr ctx.a3.x_comm₂)
  have hxS : x ∈ sOne S x := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hxP : ∀ g ∈ sOne S x ⊓ K, x⁻¹ * g * x ∈ sOne S x ⊓ K := by
    intro g hg
    refine ⟨(sOne S x).mul_mem ((sOne S x).mul_mem ((sOne S x).inv_mem hxS) hg.1) hxS, ?_⟩
    have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (K : Set G)).inv_mem hxK) g).mp
      hg.2
    simpa using this
  have hz₁U : z₁ ∈ blockU L := ctx.a3.z₁_mem.1
  have hz₁1 : z₁ ≠ 1 := ctx.a3.z₁_ne
  have hsq : ∀ u ∈ blockU L, u * u = 1 := fun u hu => by
    have := hA4.sq_U u hu
    rwa [pow_two] at this
  have hz₁2 : z₁ * z₁ = 1 := hsq z₁ hz₁U
  obtain ⟨a, haU, haz⟩ : ∃ a ∈ blockU L, a ∉ Subgroup.zpowers z₁ := by
    by_contra hcon
    have hle : blockU L ≤ Subgroup.zpowers z₁ := fun u hu => by
      by_contra h'
      exact hcon ⟨u, hu, h'⟩
    have h1 := Subgroup.card_le_of_le hle
    have hz₁sq : z₁ ^ 2 = 1 := hA4.sq_U z₁ hz₁U
    have h2 : Nat.card (Subgroup.zpowers z₁) = 2 := by
      rw [Nat.card_zpowers, orderOf_eq_prime hz₁sq hz₁1]
    rw [hA4.card_U, h2] at h1
    omega
  have ha1 : a ≠ 1 := fun h => haz (h ▸ one_mem _)
  have haz' : a ≠ z₁ := fun h => haz (h ▸ Subgroup.mem_zpowers z₁)
  have ha2 : a * a = 1 := hsq a haU
  have haz_comm : a * z₁ = z₁ * a := hA4.comm_U a haU z₁ hz₁U
  have hxz : x⁻¹ * z₁ * x = z₁ := by
    calc x⁻¹ * z₁ * x = x⁻¹ * (z₁ * x) := by group
      _ = x⁻¹ * (x * z₁) := by rw [ctx.a3.x_comm₁]
      _ = z₁ := by group
  have hcU : ¬ (x⁻¹ * a * x = a ∨ x⁻¹ * a * x = a * z₁) := by
    intro hc
    apply ctx.a3.x_good
    intro y hy
    have hy1 : x * y * x⁻¹ ∈ blockU L := mem_conjR.mp hy
    have hyeq : ∀ w, x * y * x⁻¹ = w → y = x⁻¹ * w * x := fun w hw => by rw [← hw]; group
    have haz₁U : a * z₁ ∈ blockU L := (blockU L).mul_mem haU hz₁U
    have hyU : y ∈ blockU L := by
      rcases klein_mem_cases hA4.card_U hsq hz₁U haU hz₁1 ha1 haz' hy1 with h1 | h1 | h1 | h1
      · rw [hyeq _ h1]
        simp
      · rw [hyeq _ h1, hxz]
        exact hz₁U
      · rw [hyeq _ h1]
        rcases hc with hc | hc
        · rw [hc]; exact haU
        · rw [hc]; exact haz₁U
      · rw [hyeq _ h1]
        have e1 : x⁻¹ * (a * z₁) * x = (x⁻¹ * a * x) * z₁ := by
          calc x⁻¹ * (a * z₁) * x = (x⁻¹ * a * x) * (x⁻¹ * z₁ * x) := by group
            _ = (x⁻¹ * a * x) * z₁ := by rw [hxz]
        rw [e1]
        rcases hc with hc | hc
        · rw [hc]; exact haz₁U
        · rw [hc, mul_assoc, hz₁2, mul_one]; exact haU
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact hA4.comm_U u hu y hyU
  exact a7_core (inf_le_right : sOne S x ⊓ K ≤ K) hP8 e hxK hxP
    (a := a) (z := z₁) ⟨hUS haU, hUK haU⟩ ⟨hUS hz₁U, hUK hz₁U⟩ ha2 hz₁2 haz_comm hxz hz₁1 ha1
    haz' (fun h => hcU (Or.inl h)) (fun h => hcU (Or.inr h))

theorem k32ExclA7_proof : K32ExclA7 := by
  intro G _ _ T M H S L s x z₁ z₂ K ctx hpre h
  exact k32_exclA7 ctx hpre h

end Excl

end CFSG.QuasithinUnique.DoubleA3
