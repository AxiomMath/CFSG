module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87TwoA7Desc
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87TwoA7Sub
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87TwoA7Trans

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open CFSG Subgroup

theorem card_ker_comp_equiv {N M K₀ : Type} [Group N] [Group M] [Group K₀] (e : N ≃* M)
    (φ : M →* K₀) : Nat.card (φ.comp (e : N →* M)).ker = Nat.card φ.ker := by
  rw [← MonoidHom.comap_ker, Subgroup.comap_equiv_eq_map_symm,
    Subgroup.card_map_of_injective e.symm.injective]

theorem pumpupTwoA7_of_noTwoA7 {H : Type} [Group H] (L I : Subgroup H) (s : H) {K₀ : Type}
    [Group K₀] (hNo : NoTwoA7Classical (↥L ⧸ Subgroup.center ↥L)) (hL : IsComponent L)
    (hs : orderOf s = 2) (hsI : s ∈ I) (hIL : I ≤ L)
    (hIc : IsPCompIn 2 (Subgroup.centralizer ({s} : Set H)) I) (hK₀ : IsDoubleCoverOfAlt K₀ 7)
    (hφ : ∃ φ : ↥I →* K₀, Function.Surjective φ ∧ Odd (Nat.card φ.ker)) : I = L := by
  obtain ⟨φ, hφs, hφo⟩ := hφ
  obtain ⟨hIC, K', -, hsub, -, -⟩ := hIc
  have hsL : s ∈ L := hIL hsI
  set s' : ↥L := ⟨s, hsL⟩ with hs'
  set φ' : ↥(I.subgroupOf L) →* K₀ :=
    φ.comp ((Subgroup.subgroupOfEquivOfLe hIL : ↥(I.subgroupOf L) ≃* ↥I) :
      ↥(I.subgroupOf L) →* ↥I) with hφ'
  have hφ's : Function.Surjective φ' := hφs.comp (Subgroup.subgroupOfEquivOfLe hIL).surjective
  have hφ'o : Odd (Nat.card φ'.ker) := by
    rw [hφ', card_ker_comp_equiv]
    exact hφo
  have hcomm : ∀ x ∈ I.subgroupOf L, x * s' = s' * x := fun x hx => by
    have hx' : (x : H) ∈ I := hx
    have := Subgroup.mem_centralizer_singleton_iff.mp (hIC hx')
    exact Subtype.ext (by simpa using this)
  have hs'2 : orderOf s' = 2 := by
    rw [hs', Subgroup.orderOf_mk]
    exact hs
  have hs'I : s' ∈ I.subgroupOf L := hsI
  have hnab : ¬ I.subgroupOf L ≤ Subgroup.center ↥L := fun hle => by
    obtain ⟨a, b, hab⟩ := hK₀.1.2.2
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    obtain ⟨x, rfl⟩ := hφs a'
    obtain ⟨y, rfl⟩ := hφs b'
    apply hab
    have hxy : x * y = y * x := by
      have hx : (⟨(x : H), hIL x.2⟩ : ↥L) ∈ Subgroup.center ↥L := hle x.2
      exact Subtype.ext
        (by simpa using (Subgroup.mem_center_iff.mp hx ⟨(y : H), hIL y.2⟩).symm)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, ← map_mul, ← map_mul, hxy]
  by_cases hsc : s' ∈ Subgroup.center ↥L
  · exact eq_of_mem_center hsL hL.1 hsc hIL hsub hnab
  · exfalso
    have hsubL := isSubnormal_subgroupOf_centralizer_of_le hsL hsub
    have hI'C : I.subgroupOf L ≤ Subgroup.centralizer ({s'} : Set ↥L) := fun x hx => by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hcomm x hx
    obtain ⟨hW, hnsolv⟩ := twoA7Witness_image (I.subgroupOf L) s' hs'2 hs'I hcomm hsc hK₀ φ'
      hφ's hφ'o
    have hsubJ := open_isSubnormal_image_centralizer (I.subgroupOf L) s' hI'C hsubL
    have hzJ : QuotientGroup.mk' (Subgroup.center ↥L) s' ∈
        (I.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)) :=
      Subgroup.mem_map_of_mem _ hs'I
    have hz1 : QuotientGroup.mk' (Subgroup.center ↥L) s' ≠ 1 := fun h =>
      hsc ((QuotientGroup.eq_one_iff _).mp h)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hz2 : orderOf (QuotientGroup.mk' (Subgroup.center ↥L) s') = 2 := by
      refine orderOf_eq_prime ?_ hz1
      rw [← map_pow]
      have h1 := pow_orderOf_eq_one s'
      rw [hs'2] at h1
      rw [h1, map_one]
    exact hNo _ hz2 _ hzJ hsubJ hW hnsolv

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
