module

public import CFSG.CharacterTheory.BrauerLinearThree.TenColumnCount
public import CFSG.CharacterTheory.Semidihedral.Principal.CyclicInversionAlternatingFive

public section

open scoped Classical

namespace CFSG.BrauerLinearThree

namespace TenColumn

open CFSG.Semidihedral.Principal

theorem card_outer_involutions_of_alternating {H : Type} [Group H] [Finite H] (W : Subgroup H)
    [W.Normal] (hodd : Odd (Nat.card W)) (hWK : W ≤ Subgroup.centralizer (W : Set H))
    (hindex : (Subgroup.centralizer (W : Set H)).index = 2)
    (hinv : ∀ h, h ∉ Subgroup.centralizer (W : Set H) → ∀ w ∈ W, h * w * h⁻¹ = w⁻¹)
    {d : ℕ} (hd : d = 4 ∨ d = 5)
    (ψ : Subgroup.centralizer (W : Set H) ⧸ W.subgroupOf (Subgroup.centralizer (W : Set H)) ≃*
      alternatingGroup (Fin d)) (P : Sylow 2 H) (eP : (P : Subgroup H) ≃* DihedralGroup 4) :
    Nat.card {u : H // u ∉ Subgroup.centralizer (W : Set H) ∧ orderOf u = 2} =
      Nat.card W * (if d = 4 then 6 else 10) := by
  rcases hd with rfl | rfl
  · obtain ⟨σH, hsurj, hker, hK⟩ := CyclicAlternatingFive.exists_perm_hom W (by norm_num)
      CyclicSymmetricFour.autEquiv CyclicSymmetricFour.autEquiv_apply
      CyclicSymmetricFour.alternating_eq_one_of_forall_commute hodd hWK hindex ψ P eP
    rw [CyclicAlternatingFive.card_outer_involutions W σH hodd hWK hinv hsurj hker hK,
      CyclicSymmetricFour.nat_card_odd_involutions]
    rfl
  · obtain ⟨σH, hsurj, hker, hK⟩ := CyclicAlternatingFive.exists_perm_hom W (by norm_num)
      CyclicAlternatingFive.autEquiv CyclicAlternatingFive.autEquiv_apply
      CyclicAlternatingFive.alternating_eq_one_of_forall_commute hodd hWK hindex ψ P eP
    rw [CyclicAlternatingFive.card_outer_involutions W σH hodd hWK hinv hsurj hker hK,
      CyclicAlternatingFive.nat_card_odd_involutions]
    rfl

theorem card_outerInvolutions_eq {G : Type} [Group G] [Fintype G] (W : Subgroup G)
    (hodd : Odd (Nat.card W)) (hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a)
    (hKH : (Subgroup.centralizer (W : Set G)).relIndex (Subgroup.normalizer (W : Set G)) = 2)
    (hinv : ∀ h ∈ Subgroup.normalizer (W : Set G), h ∉ Subgroup.centralizer (W : Set G) →
      ∀ w ∈ W, h * w * h⁻¹ = w⁻¹)
    (hR : (CFSG.pPrimeCore 2 (Subgroup.centralizer (W : Set G))).map
      (Subgroup.centralizer (W : Set G)).subtype = W)
    {d : ℕ} (hd : d = 4 ∨ d = 5)
    (hK : Nonempty ((Subgroup.centralizer (W : Set G) ⧸
      CFSG.pPrimeCore 2 (Subgroup.centralizer (W : Set G))) ≃* alternatingGroup (Fin d)))
    (hdih : ∃ P : Sylow 2 (Subgroup.normalizer (W : Set G)),
      Nonempty ((P : Subgroup (Subgroup.normalizer (W : Set G))) ≃* DihedralGroup 4)) :
    (outerInvolutions (Subgroup.centralizer (W : Set G)) (Subgroup.normalizer (W : Set G))).card =
      Nat.card W * (if d = 4 then 6 else 10) := by
  set H := Subgroup.normalizer (W : Set G) with hHdef
  set K := Subgroup.centralizer (W : Set G) with hKdef
  have hWH : W ≤ H := Subgroup.le_normalizer
  have hKH' : K ≤ H := Subgroup.centralizer_le_normalizer _
  set W' : Subgroup H := W.subgroupOf H with hW'def
  have hW'n : W'.Normal := Subgroup.normal_in_normalizer
  have hW'card : Nat.card W' = Nat.card W :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWH).toEquiv
  have hcent : Subgroup.centralizer (W' : Set H) = K.subgroupOf H := by
    ext h
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    constructor
    · intro hh w hw
      exact congrArg Subtype.val (hh ⟨w, hWH hw⟩ hw)
    · intro hh w hw
      exact Subtype.ext (hh w hw)
  have hWK' : W' ≤ Subgroup.centralizer (W' : Set H) := by
    rw [hcent]
    intro x hx
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    intro w hw
    exact hWab w hw _ hx
  have hindex' : (Subgroup.centralizer (W' : Set H)).index = 2 := by
    rw [hcent]
    exact hKH
  have hinv' : ∀ h : H, h ∉ Subgroup.centralizer (W' : Set H) → ∀ w ∈ W', h * w * h⁻¹ = w⁻¹ := by
    intro h hh w hw
    rw [hcent, Subgroup.mem_subgroupOf] at hh
    exact Subtype.ext (hinv h h.2 hh w hw)
  let φ : Subgroup.centralizer (W' : Set H) ≃* K :=
    (MulEquiv.subgroupCongr hcent).trans (Subgroup.subgroupOfEquivOfLe hKH')
  have hφval : ∀ x : Subgroup.centralizer (W' : Set H), ((φ x : K) : G) = ((x : H) : G) :=
    fun x => rfl
  have hmapN : (W'.subgroupOf (Subgroup.centralizer (W' : Set H))).map φ.toMonoidHom =
      CFSG.pPrimeCore 2 K := by
    ext k
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxW : ((x : H) : G) ∈ W := hx
      rw [← hR] at hxW
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxW
      have : y = φ.toMonoidHom x := Subtype.ext (by
        change (y : G) = ((φ x : K) : G)
        rw [hφval]
        exact hyx)
      rw [← this]
      exact hy
    · intro hk
      refine ⟨φ.symm k, ?_, by simp⟩
      change (((φ.symm k : Subgroup.centralizer (W' : Set H)) : H) : G) ∈ W
      have h1 : (((φ.symm k : Subgroup.centralizer (W' : Set H)) : H) : G) = (k : G) := by
        rw [← hφval, MulEquiv.apply_symm_apply]
      rw [h1, ← hR]
      exact ⟨k, hk, rfl⟩
  obtain ⟨ψ₀⟩ := hK
  let ψ : Subgroup.centralizer (W' : Set H) ⧸ W'.subgroupOf (Subgroup.centralizer (W' : Set H)) ≃*
      alternatingGroup (Fin d) := (QuotientGroup.congr _ _ φ hmapN).trans ψ₀
  obtain ⟨P, ⟨eP⟩⟩ := hdih
  have hcount := card_outer_involutions_of_alternating W' (hW'card ▸ hodd) hWK' hindex' hinv' hd
    ψ P eP
  rw [hW'card] at hcount
  rw [← hcount]
  have hmemC : ∀ y : H, y ∈ Subgroup.centralizer (W' : Set H) ↔ (y : G) ∈ K := fun y => by
    rw [hcent, Subgroup.mem_subgroupOf]
  rw [← Nat.card_eq_finsetCard]
  refine Nat.card_congr ?_
  refine
    { toFun := fun x => ⟨⟨x.1, (mem_outerInvolutions.mp x.2).1⟩, ?_⟩
      invFun := fun u => ⟨(u.1 : G), ?_⟩
      left_inv := fun x => rfl
      right_inv := fun u => rfl }
  · obtain ⟨-, hxK, hx2⟩ := mem_outerInvolutions.mp x.2
    refine ⟨fun h => hxK ((hmemC _).mp h), ?_⟩
    · have hx1 : (x.1 : G) ≠ 1 := fun h => hxK (h ▸ K.one_mem)
      refine orderOf_eq_prime (by rw [sq]; exact Subtype.ext hx2) ?_
      intro h
      exact hx1 (congrArg Subtype.val h)
  · obtain ⟨huK, hu2⟩ := u.2
    have huK' : ((u.1 : H) : G) ∉ K := fun h => huK ((hmemC _).mpr h)
    rw [mem_outerInvolutions]
    refine ⟨u.1.2, huK', ?_⟩
    have h := pow_orderOf_eq_one u.1
    rw [hu2, sq] at h
    exact congrArg Subtype.val h

end TenColumn

end CFSG.BrauerLinearThree
