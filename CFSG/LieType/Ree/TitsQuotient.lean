module

public import CFSG.LieType.Ree.TitsWeyl
public import CFSG.LieType.Ree.ReeHolds

public section

open scoped IsMulCommutative

namespace CFSG.LieType.Ree

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley ReeTag

section Torus

variable {τ : Tag} {K : Type} [Field K] [Finite K]

theorem eq_one_of_mem_H_of_card_eq_two (hK : Nat.card K = 2) {h : adjointGroup τ K}
    (hh : h ∈ (nativeData τ K).H) : h = 1 := by
  simpa [hK] using (nativeRootSubgroups τ K).pow_card_sub_one_eq_one hh

theorem nrep_eq_of_weylHom_eq (hK : Nat.card K = 2) {x : monomialGroup τ K} {w : WeylGroup τ}
    (hx : weylHom τ K x = w) : nrep τ K w = x := by
  have hy : ((x⁻¹ * ⟨nrep τ K w, nrep_mem_monomialGroup τ K w⟩ : monomialGroup τ K) :
      adjointGroup τ K) ∈ (nativeData τ K).H :=
    (RootGroupData.mem_H_iff (D := nativeData τ K)).2 ⟨(x⁻¹ * ⟨nrep τ K w,
      nrep_mem_monomialGroup τ K w⟩ : monomialGroup τ K), by
        change weylHom τ K _ = 1
        rw [map_mul, map_inv, hx, weylHom_nrep, inv_mul_cancel], rfl⟩
  have h1 : (x : adjointGroup τ K)⁻¹ * nrep τ K w = 1 := eq_one_of_mem_H_of_card_eq_two hK hy
  exact (inv_mul_eq_one.1 h1).symm

end Torus

variable {t : ReeTag} {K : Type} [Field K] [Finite K] [CharP K t.prime] {a : ℕ}

omit [CharP K t.prime] in
theorem nrep_blockElt_mul_self (hK : Nat.card K = 2) (i : Fin t.tag.rank) :
    nrep t.tag K (t.blockElt i) * nrep t.tag K (t.blockElt i) = 1 := by
  have h := nrep_eq_of_weylHom_eq hK (w := 1)
    (x := ⟨nrep t.tag K (t.blockElt i), nrep_mem_monomialGroup _ _ _⟩ *
      ⟨nrep t.tag K (t.blockElt i), nrep_mem_monomialGroup _ _ _⟩)
    (by rw [map_mul, weylHom_nrep, blockElt_mul_self])
  rw [nrep_one] at h
  exact h.symm

theorem mk_nrep_sq_eq_one (hK : Nat.card K = 2) {w : WeylGroup t.tag} (hw : w ∈ t.relWeylRee) :
    QuotientGroup.mk' (commutator (reeFixed t K a))
      (⟨nrep t.tag K w, nrep_mem_reeFixed t K a hw⟩ : reeFixed t K a) ^ 2 = 1 := by
  let gens : Fin t.tag.rank → monomialGroup t.tag K := fun i =>
    ⟨nrep t.tag K (t.blockElt i), nrep_mem_monomialGroup _ _ _⟩
  have key : ∀ x ∈ Subgroup.closure (Set.range gens),
      ∃ hx : (x : adjointGroup t.tag K) ∈ reeFixed t K a,
        QuotientGroup.mk' (commutator (reeFixed t K a)) (⟨x, hx⟩ : reeFixed t K a) ^ 2 = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      refine ⟨nrep_mem_reeFixed t K a (reeOrbitWord_mem t i), ?_⟩
      have h1 : (⟨nrep t.tag K (t.blockElt i), nrep_mem_reeFixed t K a (reeOrbitWord_mem t i)⟩ :
          reeFixed t K a) ^ 2 = 1 :=
        Subtype.ext (by rw [SubgroupClass.coe_pow, pow_two]; exact nrep_blockElt_mul_self hK i)
      rw [← map_pow]
      exact (congrArg _ h1).trans (map_one _)
    | one =>
      refine ⟨one_mem _, ?_⟩
      have e : (⟨((1 : monomialGroup t.tag K) : adjointGroup t.tag K), one_mem _⟩ :
          reeFixed t K a) = 1 := rfl
      rw [e, map_one, one_pow]
    | mul x y _ _ hx hy =>
      obtain ⟨hx, hx2⟩ := hx
      obtain ⟨hy, hy2⟩ := hy
      refine ⟨mul_mem hx hy, ?_⟩
      have e : (⟨((x * y : monomialGroup t.tag K) : adjointGroup t.tag K), mul_mem hx hy⟩ :
          reeFixed t K a) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
      rw [e, map_mul, mul_pow, hx2, hy2, one_mul]
    | inv x _ hx =>
      obtain ⟨hx, hx2⟩ := hx
      refine ⟨inv_mem hx, ?_⟩
      have e : (⟨((x⁻¹ : monomialGroup t.tag K) : adjointGroup t.tag K), inv_mem hx⟩ :
          reeFixed t K a) = (⟨x, hx⟩ : reeFixed t K a)⁻¹ := rfl
      rw [e, map_inv, inv_pow, hx2, inv_one]
  have hwc : w ∈ (Subgroup.closure (Set.range gens)).map (weylHom t.tag K) := by
    rw [MonoidHom.map_closure, ← Set.range_comp]
    have : ⇑(weylHom t.tag K) ∘ gens = t.blockElt := funext fun i => weylHom_nrep ..
    rw [this]
    exact mem_closure_blockElt _ w rfl ((mem_relWeylRee t).1 hw)
  obtain ⟨x, hx, hxw⟩ := Subgroup.mem_map.1 hwc
  obtain ⟨hxF, hx2⟩ := key x hx
  have e : (⟨nrep t.tag K w, nrep_mem_reeFixed t K a hw⟩ : reeFixed t K a) = ⟨x, hxF⟩ :=
    Subtype.ext (nrep_eq_of_weylHom_eq hK hxw)
  rw [e]
  exact hx2

theorem isPGroup_reeFixed_quotient (hp : t.prime = 2) (hK : Nat.card K = 2) :
    IsPGroup 2 (reeFixed t K a ⧸ commutator (reeFixed t K a)) := by
  have : Fact t.prime.Prime := ⟨by rw [hp]; exact Nat.prime_two⟩
  have hB : ∀ b ∈ (nativeData t.tag K).B, ∀ hb : b ∈ reeFixed t K a, ∃ k : ℕ,
      QuotientGroup.mk' (commutator (reeFixed t K a)) (⟨b, hb⟩ : reeFixed t K a) ^ 2 ^ k = 1 := by
    intro b hbB hbF
    have hbU : b ∈ (nativeData t.tag K).U := by
      obtain ⟨h, hh, u, hu, rfl⟩ := RootGroupData.exists_mul_of_mem_B hbB
      rwa [eq_one_of_mem_H_of_card_eq_two hK hh, one_mul]
    obtain ⟨k, hk⟩ := (nativeRootSubgroups t.tag K).isPGroup_U t.prime ⟨b, hbU⟩
    rw [hp] at hk
    refine ⟨k, ?_⟩
    have h1 : (⟨b, hbF⟩ : reeFixed t K a) ^ 2 ^ k = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hk)
    rw [← map_pow]
    exact (congrArg _ h1).trans (map_one _)
  have f : ∀ (y : reeFixed t K a ⧸ commutator (reeFixed t K a)) (k m : ℕ), y ^ 2 ^ k = 1 →
      k ≤ m → y ^ 2 ^ m = 1 := by
    intro y k m h hkm
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkm
    rw [pow_add, pow_mul, h, one_pow]
  intro g
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (commutator (reeFixed t K a)) g
  obtain ⟨w, hw, b₁, hb₁, hb₁F, b₂, hb₂, hb₂F, hx⟩ := reeFixed_bruhat t K a x x.2
  obtain ⟨k₁, hk₁⟩ := hB b₁ hb₁ hb₁F
  obtain ⟨k₂, hk₂⟩ := hB b₂ hb₂ hb₂F
  have hn := mk_nrep_sq_eq_one (a := a) hK hw
  have e : x = ⟨b₁, hb₁F⟩ * ⟨nrep t.tag K w, nrep_mem_reeFixed t K a hw⟩ * ⟨b₂, hb₂F⟩ :=
    Subtype.ext hx
  refine ⟨k₁ + k₂ + 1, ?_⟩
  rw [e, map_mul, map_mul, mul_pow, mul_pow, f _ k₁ _ hk₁ (by omega),
    f _ 1 _ (by rwa [pow_one]) (by omega), f _ k₂ _ hk₂ (by omega), one_mul, one_mul]

end CFSG.LieType.Ree
