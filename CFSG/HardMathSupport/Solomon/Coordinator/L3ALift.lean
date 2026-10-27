module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

theorem exists_elemAbelian_nine_lift {H Q : Type*} [Group H] [Group Q] [Finite H] (ρ : H →* Q)
    (hρ : Function.Surjective ρ) (hk : Nat.Coprime 3 (Nat.card ρ.ker)) (E : Subgroup Q)
    (hE : CFSG.Open.IsElemAbelian 3 E) (hc : Nat.card E = 9) :
    ∃ E' : Subgroup H, CFSG.Open.IsElemAbelian 3 E' ∧ Nat.card E' = 9 ∧
      Function.Injective (ρ.comp E'.subtype) := by
  classical
  set P : Subgroup H := E.comap ρ with hP
  have hkP : ρ.ker ≤ P := fun x hx => by
    rw [hP, Subgroup.mem_comap, MonoidHom.mem_ker.1 hx]
    exact E.one_mem
  let φ : ↥P →* ↥E := (ρ.comp P.subtype).codRestrict E (fun x => x.2)
  have hφ : Function.Surjective φ := by
    intro e
    obtain ⟨h, hh⟩ := hρ e
    exact ⟨⟨h, by rw [hP, Subgroup.mem_comap, hh]; exact e.2⟩, Subtype.ext hh⟩
  have hker : φ.ker = ρ.ker.subgroupOf P := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  have hidx : (ρ.ker.subgroupOf P).index = 9 := by
    rw [← hker, Subgroup.index, ← hc]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv
  have hN : Nat.card (ρ.ker.subgroupOf P) = Nat.card ρ.ker :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkP).toEquiv
  have hcop : Nat.Coprime (Nat.card (ρ.ker.subgroupOf P)) (ρ.ker.subgroupOf P).index := by
    rw [hidx, hN]
    have h9 : (9 : ℕ) = 3 ^ 2 := by norm_num
    rw [h9]
    exact Nat.Coprime.pow_right 2 hk.symm
  have : (ρ.ker.subgroupOf P).Normal := Subgroup.normal_subgroupOf
  obtain ⟨C, hC⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hCcard : Nat.card C = 9 := by
    have h1 := hC.card_mul_card
    have h2 := (ρ.ker.subgroupOf P).card_mul_index
    have hpos : 0 < Nat.card ↥(ρ.ker.subgroupOf P) := Nat.card_pos
    rw [hidx] at h2
    exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans h2.symm)
  have hdisj : ∀ x ∈ C, ρ (x : H) = 1 → x = 1 := fun x hx hx1 =>
    Subgroup.disjoint_def.1 hC.disjoint (by simpa [Subgroup.mem_subgroupOf] using hx1) hx
  have hinj : ∀ a ∈ C.map P.subtype, ∀ b ∈ C.map P.subtype, ρ a = ρ b → a = b := by
    rintro _ ⟨c₁, hc₁, rfl⟩ _ ⟨c₂, hc₂, rfl⟩ h
    have h1 : c₁⁻¹ * c₂ = 1 := hdisj _ (mul_mem (inv_mem hc₁) hc₂) (by
      change ρ ((c₁ : H)⁻¹ * (c₂ : H)) = 1
      rw [map_mul, map_inv, inv_mul_eq_one]
      exact h)
    rw [inv_mul_eq_one] at h1
    rw [h1]
  have hmemE : ∀ a ∈ C.map P.subtype, ρ a ∈ E := by
    rintro _ ⟨c, -, rfl⟩
    exact c.2
  refine ⟨C.map P.subtype, ⟨⟨⟨?_⟩⟩, ?_⟩, ?_, ?_⟩
  · rintro ⟨a, ha⟩ ⟨b, hb⟩
    apply Subtype.ext
    apply hinj _ (mul_mem ha hb) _ (mul_mem hb ha)
    rw [map_mul, map_mul]
    exact congrArg Subtype.val (hE.1.is_comm.comm (⟨ρ a, hmemE a ha⟩ : E) ⟨ρ b, hmemE b hb⟩)
  · intro a ha
    apply hinj _ (pow_mem ha 3) _ (one_mem _)
    rw [map_pow, map_one]
    exact hE.2 _ (hmemE a ha)
  · rw [Subgroup.card_map_of_injective P.subtype_injective]
    exact hCcard
  · intro a b h
    exact Subtype.ext (hinj a.1 a.2 b.1 b.2 h)

end CFSG.HardMathSupport.Solomon.Coordinator
