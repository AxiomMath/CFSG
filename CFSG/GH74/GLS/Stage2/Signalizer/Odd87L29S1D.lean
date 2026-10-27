module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29S1C

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local

namespace L29S1

theorem normal_of_index_dvd_two {R : Type} [Group R] (K : Subgroup R) (h : K.index ∣ 2) :
    K.Normal := by
  rcases (Nat.dvd_prime Nat.prime_two).mp h with h1 | h2
  · exact normal_of_index_eq_one h1
  · exact normal_of_index_eq_two h2

end L29S1

theorem sylow_O2_swap_cyclic_or_dihedral {H : Type} [Group H] [Finite H]
    {L₁ L₂ : Subgroup H} {q : ℕ} (hne : L₁ ≠ L₂)
    (hcomps : {K : Subgroup H | IsComponent K} = {L₁, L₂})
    (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) (hI : Nat.card ↥(L₁ ⊓ L₂) = 2)
    (hcent : ∀ c : H, (∀ a ∈ L₁, c * a = a * c) → (∀ b ∈ L₂, c * b = b * c) → c ∈ L₁ ⊓ L₂)
    (hodd : Odd q) (hgt : 3 < q)
    (hs₁ : HasSL2Model ↥L₁ (fun r => r = q)) (hs₂ : HasSL2Model ↥L₂ (fun r => r = q))
    {u : H} (hu2 : u * u = 1)
    (h₁₂ : L₁.map (MulAut.conj u).toMonoidHom = L₂)
    (h₂₁ : L₂.map (MulAut.conj u).toMonoidHom = L₁) :
    ∀ P : Sylow 2 ↥(O2Of (centralizer ({u} : Set H))), IsCyclic ↥P ∨ IsDihedral ↥P := by
  intro P
  have _ := hs₂
  have hS : L29S1.SwapData L₁ L₂ u := ⟨hcomm, hI, hcent, hu2, h₁₂, h₂₁⟩
  have hc1 : IsComponent L₁ := by
    have : L₁ ∈ {K : Subgroup H | IsComponent K} := by
      rw [hcomps]
      exact Set.mem_insert _ _
    exact this
  have hc2 : IsComponent L₂ := by
    have : L₂ ∈ {K : Subgroup H | IsComponent K} := by
      rw [hcomps]
      exact Set.mem_insert_of_mem _ rfl
    exact this
  have hall : ∀ K : Subgroup H, IsComponent K → K = L₁ ∨ K = L₂ := fun K hK => by
    have : K ∈ ({L₁, L₂} : Set (Subgroup H)) := by
      rw [← hcomps]
      exact hK
    simpa using this
  have hidx := L29Pair.index_dvd_two_of_components hne hc1 hc2 hall (centralizer ({u} : Set H))
  have hnorm : ((L29S1.stab L₁ L₂ u).subgroupOf (centralizer ({u} : Set H))).Normal :=
    L29S1.normal_of_index_dvd_two _ hidx
  have hq2 : IsPGroup 2 (↥(centralizer ({u} : Set H)) ⧸
      (L29S1.stab L₁ L₂ u).subgroupOf (centralizer ({u} : Set H))) :=
    L29S1.isPGroup_quotient_of_index_dvd_two _ hidx
  have hO : O2Of (centralizer ({u} : Set H)) ≤ O2Of (L29S1.stab L₁ L₂ u) :=
    L29S1.O2Of_le_of_isPGroup_quotient hq2
  have hout := L29S1.out_comm_of_hasSL2Model (L := ↥L₁) hodd hgt hs₁
  obtain ⟨F, hF, hFin, hqF, ⟨ePsl⟩⟩ := L29S1.exists_equiv_psl2_diagHom_range hS hodd hs₁
  let g : ↥P →* H := (O2Of (centralizer ({u} : Set H))).subtype.comp
    (P : Subgroup ↥(O2Of (centralizer ({u} : Set H)))).subtype
  have hg : ∀ p : ↥P, g p ∈ (L29S1.diagHom hS).range := by
    intro p
    obtain ⟨k, hk⟩ := P.isPGroup' p
    have hk' : g p ^ 2 ^ k = 1 := by rw [← map_pow, hk, map_one]
    exact L29S1.mem_diagHom_range_of_two_power hS hout (hO p.1.2) hk'
  let f : ↥P →* ↥(L29S1.diagHom hS).range := g.codRestrict _ hg
  have hgi : Function.Injective g :=
    Subtype.val_injective.comp (Subtype.val_injective (p := fun x => x ∈ P))
  have hf : Function.Injective f := Function.Injective.of_comp (f := Subtype.val) hgi
  exact L29S1.isCyclic_or_isDihedral_of_psl2 (hqF ▸ hodd) ePsl P.isPGroup' f hf

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
