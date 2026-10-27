module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FinalTheorem
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2KleinFourCentralizerEqSelf
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Subgroup CFSG.GorensteinWalter

theorem gw_cases
    {H : Type} [Group H] [Finite H] (hD : HasDihedralSylowTwo H) :
    IsPGroup 2 (H ⧸ pPrimeCore 2 H) ∨
      Nonempty ((H ⧸ pPrimeCore 2 H) ≃* alternatingGroup (Fin 7)) ∨
      ∃ (K : Type) (_ : Field K) (_ : Finite K), IsOddPrimePower (Nat.card K) ∧
        ∃ L : Subgroup (H ⧸ pPrimeCore 2 H), L.Normal ∧ Odd L.index ∧
          (Nonempty (L ≃* PSL2 K) ∨ Nonempty (L ≃* PGL2 K)) := by
  rcases gorensteinWalter H hD with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, K, hK, L, hL, hLi, hLm⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨K, inferInstance, inferInstance, hK, L, hL, hLi, hLm⟩)

theorem hasDihedralSylowTwo_of_equiv {H : Type*} [Group H] [Finite H] (S : Sylow 2 H) {m : ℕ}
    (hm : 1 ≤ m) (e : (S : Subgroup H) ≃* DihedralGroup (2 ^ m)) : HasDihedralSylowTwo H :=
  fun T => ⟨m, hm, ⟨(Sylow.equiv S T).symm.trans e⟩⟩

theorem inf_centralizer_eq_of_linear
    {M : Type*} [Group M] {L : Subgroup M} {K : Type}
    [Field K] [Finite K] (hK : IsOddPrimePower (Nat.card K))
    (hL : Nonempty (L ≃* PSL2 K) ∨ Nonempty (L ≃* PGL2 K)) {V : Subgroup M} (hVL : V ≤ L)
    (hV : IsKleinFour V) : L ⊓ centralizer (V : Set M) = V := by
  have key : ∀ (X : Type) [Group X] (e : L ≃* X),
      (∀ W : Subgroup X, IsKleinFour W → centralizer (W : Set X) = W) →
        L ⊓ centralizer (V : Set M) = V := by
    intro X _ e hX
    set W : Subgroup X := (V.subgroupOf L).map e.toMonoidHom with hW
    have hVL' : (V.subgroupOf L).map L.subtype = V := by
      rw [subgroupOf_map_subtype, inf_eq_left.mpr hVL]
    have hWV : W ≃* V := by
      refine ((V.subgroupOf L).equivMapOfInjective e.toMonoidHom e.injective).symm.trans ?_
      exact (subgroupOfEquivOfLe hVL)
    have hWK : IsKleinFour W := by
      refine ⟨?_, ?_⟩
      · rw [Nat.card_congr hWV.toEquiv]; exact hV.card_four
      · rw [Monoid.exponent_eq_of_mulEquiv hWV]; exact hV.exponent_two
    have hC := hX W hWK
    apply le_antisymm
    · rintro x ⟨hxL, hxC⟩
      have hx : e ⟨x, hxL⟩ ∈ centralizer (W : Set X) := by
        rw [mem_centralizer_iff]
        rintro _ ⟨⟨v, hvL⟩, hv, rfl⟩
        have hv' : v ∈ V := mem_subgroupOf.mp hv
        have := (mem_centralizer_iff.mp hxC) v hv'
        change e ⟨v, hvL⟩ * e ⟨x, hxL⟩ = e ⟨x, hxL⟩ * e ⟨v, hvL⟩
        rw [← map_mul, ← map_mul]
        exact congrArg e (Subtype.ext this)
      rw [hC] at hx
      obtain ⟨⟨y, hyL⟩, hy, hye⟩ := hx
      have : (⟨y, hyL⟩ : L) = ⟨x, hxL⟩ := e.injective hye
      have hxy : y = x := congrArg Subtype.val this
      rw [← hxy]
      exact mem_subgroupOf.mp hy
    · intro v hv
      refine ⟨hVL hv, mem_centralizer_iff.mpr fun w hw => ?_⟩
      exact (IsKleinFour.isMulCommutative (G := V)).is_comm.comm ⟨w, hw⟩ ⟨v, hv⟩ |> congrArg
        Subtype.val
  rcases hL with h | h
  · obtain ⟨e⟩ := h
    exact key _ e (fun W hW => psl2_kleinFour_centralizer_eq_self K hK W hW)
  · obtain ⟨e⟩ := h
    exact key _ e (fun W hW => pgl2_kleinFour_centralizer_eq_self K hK W hW)

theorem eq_one_of_linear
    {M : Type*} [Group M] [Finite M] {L : Subgroup M} [hLn : L.Normal]
    {K : Type} [Field K] [Finite K] (hK : IsOddPrimePower (Nat.card K))
    (hL : Nonempty (L ≃* PSL2 K) ∨ Nonempty (L ≃* PGL2 K)) {V : Subgroup M} (hVL : V ≤ L)
    (hV : IsKleinFour V) {c y : M} (hy : y ∈ L) (hyc : y * c * y⁻¹ = c⁻¹)
    (hcV : c ∈ centralizer (V : Set M)) (hodd : Odd (orderOf c)) : c = 1 := by
  have h2 : c⁻¹ * c⁻¹ ∈ L := by
    have h1 : y * (c * y⁻¹ * c⁻¹) ∈ L := L.mul_mem hy (hLn.conj_mem _ (L.inv_mem hy) c)
    have : y * (c * y⁻¹ * c⁻¹) = c⁻¹ * c⁻¹ := by rw [← mul_assoc, ← mul_assoc, hyc]
    rwa [this] at h1
  obtain ⟨k, hk⟩ := hodd
  have hcL : c ∈ L := by
    have hpow : c ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one c
    have e1 : c ^ (2 * k) * c = 1 := by rw [← pow_succ, hpow]
    have e2 : c ^ (2 * k) = c⁻¹ := eq_inv_of_mul_eq_one_left e1
    have hc : (c⁻¹ * c⁻¹) ^ k = c := by rw [← sq, ← pow_mul, inv_pow, e2, inv_inv]
    rw [← hc]
    exact pow_mem h2 _
  have hcV' : c ∈ V := by
    rw [← inf_centralizer_eq_of_linear hK hL hVL hV]
    exact ⟨hcL, hcV⟩
  have hsq : c ^ 2 = 1 := by
    have h := Monoid.pow_exponent_eq_one (⟨c, hcV'⟩ : V)
    rw [hV.exponent_two] at h
    simpa using congrArg Subtype.val h
  have hd := orderOf_dvd_of_pow_eq_one hsq
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
  · exact orderOf_eq_one_iff.mp h
  · omega

@[expose] def d8ρ : Equiv.Perm (Fin 6) :=
  Equiv.swap 0 1 * Equiv.swap 4 5 * (Equiv.swap 0 2 * Equiv.swap 1 3)

@[expose] def d8s : Equiv.Perm (Fin 6) := Equiv.swap 0 1 * Equiv.swap 4 5

@[expose] def d8Fun : DihedralGroup 4 → Equiv.Perm (Fin 6)
  | .r i => d8ρ ^ i.val
  | .sr i => d8s * d8ρ ^ i.val

theorem d8Fun_mul : ∀ a b : DihedralGroup 4, d8Fun (a * b) = d8Fun a * d8Fun b := by
  decide +kernel

theorem d8Fun_injective' : ∀ a b : DihedralGroup 4, d8Fun a = d8Fun b → a = b := by
  decide +kernel

@[expose] def d8Hom : DihedralGroup 4 →* Equiv.Perm (Fin 6) where
  toFun := d8Fun
  map_one' := by decide +kernel
  map_mul' := d8Fun_mul

theorem d8Hom_injective : Function.Injective d8Hom := fun a b h => d8Fun_injective' a b h

@[expose] def d8 : Subgroup (Equiv.Perm (Fin 6)) := d8Hom.range

noncomputable def d8Equiv : d8 ≃* DihedralGroup 4 :=
  (MonoidHom.ofInjective d8Hom_injective).symm

theorem d8_le_alternatingGroup : d8 ≤ alternatingGroup (Fin 6) := by
  rintro _ ⟨a, rfl⟩
  rw [Equiv.Perm.mem_alternatingGroup]
  have h : ∀ a : DihedralGroup 4, Equiv.Perm.sign (d8Fun a) = 1 := by decide +kernel
  exact h a

theorem mem_d8_iff (x : Equiv.Perm (Fin 6)) : x ∈ d8 ↔ ∃ a : DihedralGroup 4, d8Fun a = x :=
  Iff.rfl

theorem card_d8 : Nat.card d8 = 8 := by
  rw [Nat.card_congr d8Equiv.toEquiv, Nat.card_eq_fintype_card, DihedralGroup.card]

end CFSG.ComponentClassification.RankTwoAlt
