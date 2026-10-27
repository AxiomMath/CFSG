module

public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

public section

namespace CFSG.GroupTheory

variable {L H : Type*} [Group L] [Finite L] [Group H] [Finite H]

theorem card_comap_eq_card_ker_mul_card (f : L →* H) (hf : Function.Surjective f)
    (Astar : Subgroup H) :
    Nat.card (Astar.comap f) = Nat.card f.ker * Nat.card Astar := by
  let N : Subgroup L := Astar.comap f
  have hker_le_N : f.ker ≤ N := fun x hx => by
    change f x ∈ Astar
    rw [MonoidHom.mem_ker] at hx
    rw [hx]
    exact Astar.one_mem
  let g : (Astar.comap f) →* Astar := (f.comp (Astar.comap f).subtype).codRestrict Astar
    fun x => Subgroup.mem_comap.mp x.2
  have hg : Function.Surjective g := by
    intro y
    have hy : (y : H) ∈ (Astar.comap f).map f := by
      rw [Subgroup.map_comap_eq_self_of_surjective hf Astar]
      exact y.2
    obtain ⟨x, hx, hx'⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hx⟩, Subtype.ext hx'⟩
  have h := Subgroup.card_ker_mul_card_of_surjective (f := g) hg
  have hker_g : g.ker = f.ker.subgroupOf (Astar.comap f) := by
    dsimp only [g]
    rw [MonoidHom.ker_codRestrict, ← MonoidHom.comap_ker f (Astar.comap f).subtype,
      Subgroup.comap_subtype]
  rw [hker_g] at h
  have hcard : Nat.card (f.ker.subgroupOf N) = Nat.card f.ker :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hker_le_N).toEquiv
  rw [show f.ker.subgroupOf (Astar.comap f) = f.ker.subgroupOf N from rfl, hcard] at h
  exact h.symm

private theorem card_map_eq_card_of_inf_ker_eq_bot {f : L →* H} {A : Subgroup L}
    (hdisj : A ⊓ f.ker = ⊥) : Nat.card (A.map f) = Nat.card A := by
  let fA : A →* ↥(A.map f) :=
    (f.comp A.subtype).codRestrict (A.map f) fun a => Subgroup.mem_map_of_mem f a.2
  have hfA : Function.Surjective fA := by
    rintro ⟨y, hy⟩
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨a, ha⟩, rfl⟩
  have hker : fA.ker = ⊥ := by
    rw [eq_bot_iff]
    rintro ⟨a, ha⟩ ha1
    have haK : (a : L) ∈ A ⊓ f.ker := by
      refine ⟨ha, ?_⟩
      have h1 : fA ⟨a, ha⟩ = 1 := MonoidHom.mem_ker.mp ha1
      change f a = 1
      simpa [fA] using congrArg Subtype.val h1
    rw [hdisj, Subgroup.mem_bot] at haK
    exact Subtype.ext haK
  have h := Subgroup.card_ker_mul_card_of_surjective (f := fA) hfA
  rw [hker, Subgroup.card_bot, one_mul] at h
  exact h

theorem exists_pSubgroup_map_eq_of_coprime_ker {p : ℕ} [Fact p.Prime]
    (f : L →* H) (hf : Function.Surjective f) (hker : ¬ p ∣ Nat.card f.ker)
    {Astar : Subgroup H} (hAstarp : IsPGroup p Astar) :
    ∃ A : Subgroup L, IsPGroup p A ∧ A ≤ Astar.comap f ∧ A.map f = Astar ∧
      A ⊓ f.ker = ⊥ := by
  classical
  let N : Subgroup L := Astar.comap f
  have hker_le_N : f.ker ≤ N := fun x hx => by
    change f x ∈ Astar
    rw [MonoidHom.mem_ker] at hx
    rw [hx]
    exact Astar.one_mem
  have hcardN : Nat.card f.ker * Nat.card Astar = Nat.card N :=
    (card_comap_eq_card_ker_mul_card f hf Astar).symm
  have hAstar_card : Nat.card Astar = p ^ (Nat.card Astar).factorization p := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hAstarp
    rw [hk, Nat.factorization_pow_self (Fact.out : p.Prime)]
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow p N))
  let A : Subgroup L := (Q : Subgroup N).map N.subtype
  have hAp : IsPGroup p A := Q.isPGroup'.map N.subtype
  have hAle : A ≤ N := Subgroup.map_subtype_le _
  have hcardA : Nat.card A = Nat.card Astar := by
    change Nat.card ((Q : Subgroup N).map N.subtype) = Nat.card Astar
    rw [Subgroup.card_map_of_injective N.subtype_injective, Sylow.card_eq_multiplicity]
    have hfac : (Nat.card N).factorization p = (Nat.card Astar).factorization p := by
      rw [← hcardN, Nat.factorization_mul (Nat.card_pos.ne') (Nat.card_pos.ne'),
        Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hker, zero_add]
    rw [hfac, ← hAstar_card]
  have hdisj : A ⊓ f.ker = ⊥ := by
    apply Subgroup.eq_bot_of_card_eq
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hAp.to_le inf_le_left)
    have hdvd : p ^ k ∣ Nat.card f.ker := hk ▸ Subgroup.card_dvd_of_le inf_le_right
    have hk0 : k = 0 := by
      by_contra hkne
      exact hker (dvd_trans (dvd_pow_self p hkne) hdvd)
    rw [hk, hk0, pow_zero]
  have hmap : A.map f = Astar := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rwa [Subgroup.map_le_iff_le_comap]
    · rw [card_map_eq_card_of_inf_ker_eq_bot hdisj, hcardA]
  exact ⟨A, hAp, hAle, hmap, hdisj⟩

theorem exists_mul_mem_comap_and_normalizer {p : ℕ} [Fact p.Prime] (f : L →* H)
    {Astar : Subgroup H} {A : Subgroup L} (hAle : A ≤ Astar.comap f)
    (hAsyl : CFSG.ABGLocalTools.IsSylowOf p A (Astar.comap f))
    {g : L} (hg : f g ∈ Subgroup.normalizer (Astar : Set H)) :
    ∃ n ∈ Astar.comap f, ∃ m ∈ Subgroup.normalizer (A : Set L), g = n * m := by
  let N : Subgroup L := Astar.comap f
  have hgn : N.map (MulAut.conj g).toMonoidHom = N := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      change f (g * x * g⁻¹) ∈ Astar
      change f x ∈ Astar at hx
      simpa [map_mul] using (Subgroup.mem_normalizer_iff.mp hg (f x)).mp hx
    · intro x hx
      refine ⟨g⁻¹ * x * g, ?_, ?_⟩
      · change f (g⁻¹ * x * g) ∈ Astar
        change f x ∈ Astar at hx
        have hg' : (f g)⁻¹ ∈ Subgroup.normalizer (Astar : Set H) :=
          (Subgroup.normalizer (Astar : Set H)).inv_mem hg
        simpa [map_mul] using (Subgroup.mem_normalizer_iff.mp hg' (f x)).mp hx
      · change g * (g⁻¹ * x * g) * g⁻¹ = x
        group
  have hA'le : A.map (MulAut.conj g).toMonoidHom ≤ N := by
    rw [← hgn]
    exact Subgroup.map_mono hAle
  have hA'syl : CFSG.ABGLocalTools.IsSylowOf p
      (A.map (MulAut.conj g).toMonoidHom) N := by
    refine CFSG.ABGLocalTools.isSylowOf_of_card hA'le ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hAsyl.card_eq]
  obtain ⟨k, hk, hkey⟩ := hAsyl.exists_mem_conj hA'syl
  have hm : k⁻¹ * g ∈ Subgroup.normalizer (A : Set L) := by
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      have hxa : g * a * g⁻¹ ∈ A.map (MulAut.conj g).toMonoidHom := ⟨a, ha, rfl⟩
      have h := (hkey (g * a * g⁻¹)).mp hxa
      simpa only [mul_inv_rev, inv_inv, mul_assoc] using h
    · intro ha
      have h := (hkey (g * a * g⁻¹)).mpr
        (by simpa only [mul_inv_rev, inv_inv, mul_assoc] using ha)
      obtain ⟨b, hb, hba⟩ := Subgroup.mem_map.mp h
      have hba' : g * b * g⁻¹ = g * a * g⁻¹ := hba
      rw [show b = a by exact mul_left_cancel (mul_right_cancel hba')] at hb
      exact hb
  exact ⟨k, hk, k⁻¹ * g, hm, by group⟩

end CFSG.GroupTheory

end
