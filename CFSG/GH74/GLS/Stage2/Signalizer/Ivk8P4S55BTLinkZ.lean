module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTLinkA
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTStmt

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local

theorem odd_card_center_of_maps {D J K : Type*} [Group D] [Finite D] [Group J] [Group K]
    [IsSimpleGroup (J ⧸ center J)] [IsSimpleGroup (K ⧸ center K)]
    (hK : ∃ a b : K ⧸ center K, a * b ≠ b * a) {ψ₁ : D →* J} {ψ₂ : D →* K}
    (h₁ : Function.Surjective ψ₁) (h₂ : Function.Surjective ψ₂)
    (hodd : Odd (Nat.card ψ₁.ker)) (hZ : Odd (Nat.card (center J))) :
    Odd (Nat.card (center K)) := by
  set f₁ : D →* J ⧸ center J := (QuotientGroup.mk' (center J)).comp ψ₁ with hf₁
  set f₂ : D →* K ⧸ center K := (QuotientGroup.mk' (center K)).comp ψ₂ with hf₂
  have hs₁ : Function.Surjective f₁ := (QuotientGroup.mk'_surjective _).comp h₁
  have hs₂ : Function.Surjective f₂ := (QuotientGroup.mk'_surjective _).comp h₂
  have hmem : ∀ d : ↥f₁.ker, ψ₁ d ∈ center J := fun d => (QuotientGroup.eq_one_iff _).mp d.2
  let g₁ : ↥f₁.ker →* ↥(center J) := (ψ₁.comp f₁.ker.subtype).codRestrict _ hmem
  have hmemk : ∀ x : ↥g₁.ker, ((x : ↥f₁.ker) : D) ∈ ψ₁.ker := by
    intro x
    have h1 : g₁ x = 1 := x.2
    exact congrArg Subtype.val h1
  let k₁ : ↥g₁.ker →* ↥ψ₁.ker := (f₁.ker.subtype.comp g₁.ker.subtype).codRestrict _ hmemk
  have hk₁ : Function.Injective k₁ := by
    intro x y hxy
    have h1 := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext h1)
  have hcardk : Odd (Nat.card ↥g₁.ker) :=
    Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_injective k₁ hk₁)
  have hcardr : Odd (Nat.card ↥g₁.range) :=
    Odd.of_dvd_nat hZ (Subgroup.card_subgroup_dvd_card g₁.range)
  have hR : Odd (Nat.card ↥f₁.ker) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup g₁.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange g₁).toEquiv]
    exact hcardr.mul hcardk
  have hsol : Group.IsSolvable ↥f₁.ker := by
    have : Group.IsSolvable ↥ψ₁.ker := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
    have : Group.IsSolvable ↥g₁.ker := Group.isSolvable_of_isSolvable_injective hk₁
    have : Group.IsSolvable ↥(center J) :=
      Group.isSolvable_of_comm fun x y => Subtype.ext (Subgroup.mem_center_iff.mp y.2 x)
    exact Group.isSolvable_of_ker_le_range g₁.ker.subtype g₁ (by rw [Subgroup.range_subtype])
  have hker := ker_eq_of_solvable hK hs₁ hs₂ hsol
  have hmem₂ : ∀ d : ↥f₂.ker, ψ₂ d ∈ center K := fun d => (QuotientGroup.eq_one_iff _).mp d.2
  let g₂ : ↥f₂.ker →* ↥(center K) := (ψ₂.comp f₂.ker.subtype).codRestrict _ hmem₂
  have hg₂ : Function.Surjective g₂ := by
    rintro ⟨z, hz⟩
    obtain ⟨d, rfl⟩ := h₂ z
    have hd : d ∈ f₂.ker := (QuotientGroup.eq_one_iff _).mpr hz
    exact ⟨⟨d, hd⟩, rfl⟩
  have h2 : Odd (Nat.card ↥f₂.ker) := by
    rw [← hker]
    exact hR
  exact Odd.of_dvd_nat h2 (Subgroup.card_dvd_of_surjective hg₂)

variable {G : Type} [Group G] [Finite G] {H P : Subgroup G} {g : G} {Γ : Type} [Group Γ]
  {K : Subgroup Γ} {a : Γ} {P' : Subgroup Γ} {J : Subgroup (HBar H)}

theorem LinkB.exists_maps (hL : LinkB H P g K a P' J) :
    ∃ (D : Type) (_ : Group D) (_ : Finite D) (ψ₁ : D →* ↥J) (ψ₂ : D →* ↥K),
      Function.Surjective ψ₁ ∧ Function.Surjective ψ₂ ∧ Odd (Nat.card ψ₁.ker) := by
  obtain ⟨Γ₀, _, _, π, ι, -, hι, -, -, -, -, -, -, -, -, Dl, -, -, hDlJ, hDlK, -⟩ := hL
  set ν : ↥H →* HBar H := QuotientGroup.mk' (pPrimeCore 2 ↥H) with hν
  set Dh : Subgroup ↥H := Dl.subgroupOf H with hDh
  have hmem₁ : ∀ d : ↥Dh, ν d ∈ J := fun d => hDlJ ▸ Subgroup.mem_map_of_mem ν d.2
  have hmem₂ : ∀ d : ↥Dh, π d ∈ K.map ι := fun d => hDlK ▸ Subgroup.mem_map_of_mem π d.2
  set ψ₁ : ↥Dh →* ↥J := (ν.comp Dh.subtype).codRestrict J hmem₁ with hψ₁
  set eK : ↥K ≃* ↥(K.map ι) := K.equivMapOfInjective ι hι with heK
  set ψ₂ : ↥Dh →* ↥K :=
    eK.symm.toMonoidHom.comp ((π.comp Dh.subtype).codRestrict _ hmem₂) with hψ₂
  have hψ₂ι : ∀ d : ↥Dh, ι (ψ₂ d) = π d := by
    intro d
    have h1 := Subgroup.coe_equivMapOfInjective_apply K ι hι (eK.symm ⟨π d, hmem₂ d⟩)
    rw [← heK, MulEquiv.apply_symm_apply] at h1
    exact h1.symm
  have hψ₁s : Function.Surjective ψ₁ := by
    rintro ⟨j, hj⟩
    have hj' : j ∈ Dh.map ν := by rw [hDlJ]; exact hj
    obtain ⟨d, hd, hdj⟩ := hj'
    exact ⟨⟨d, hd⟩, Subtype.ext hdj⟩
  have hψ₂s : Function.Surjective ψ₂ := by
    intro k
    have hk' : ι k ∈ Dh.map π := by rw [hDlK]; exact Subgroup.mem_map_of_mem ι k.2
    obtain ⟨d, hd, hdk⟩ := hk'
    exact ⟨⟨d, hd⟩, Subtype.ext (hι (by rw [hψ₂ι]; exact hdk))⟩
  have hodd : Odd (Nat.card ψ₁.ker) := by
    have hmemO : ∀ x : ↥ψ₁.ker, ((x : ↥Dh) : ↥H) ∈ pPrimeCore 2 ↥H := by
      intro x
      have h1 : ν ((x : ↥Dh) : ↥H) = 1 := congrArg Subtype.val x.2
      exact (QuotientGroup.eq_one_iff _).mp h1
    let k : ↥ψ₁.ker →* ↥(pPrimeCore 2 ↥H) :=
      (Dh.subtype.comp ψ₁.ker.subtype).codRestrict _ hmemO
    have hk : Function.Injective k := by
      intro x y hxy
      have h1 := congrArg Subtype.val hxy
      exact Subtype.ext (Subtype.ext h1)
    exact Odd.of_dvd_nat (Nat.coprime_two_left.mp pPrimeCore_coprime_card)
      (Subgroup.card_dvd_of_injective k hk)
  exact ⟨↥Dh, inferInstance, inferInstance, ψ₁, ψ₂, hψ₁s, hψ₂s, hodd⟩

theorem LinkB.odd_center (hq : IsQuasisimple ↥K) (hL : LinkB H P g K a P' J)
    (hZ : Odd (Nat.card ↥(center ↥J))) : Odd (Nat.card ↥(center ↥K)) := by
  have hJ : IsComponent J := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hJ, _⟩ := hL
    exact hJ
  obtain ⟨D, _, _, ψ₁, ψ₂, h₁, h₂, hodd⟩ := hL.exists_maps
  have : IsSimpleGroup (↥J ⧸ center ↥J) := hJ.1.2.1
  have : IsSimpleGroup (↥K ⧸ center ↥K) := hq.2.1
  exact odd_card_center_of_maps hq.2.2 h₁ h₂ hodd hZ

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
