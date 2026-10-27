module

public import CFSG.CGT.T75P.Aut

public section

namespace CFSG.CGT.T75P

open CFSG.Open CFSG.CGT.Timmesfeld75
open scoped MatrixGroups Matrix

variable {G : Type} [Group G] {T : Subgroup G} {n : ℕ}

theorem odd_index_normalizer [Finite G] (hT : IsWC T) :
    Odd (Subgroup.normalizer (T : Set G)).index := by
  classical
  obtain ⟨P, hTP⟩ := (isPGroup_two_of_isElemAbelian hT.1).exists_le_sylow
  have hPN : (P : Subgroup G) ≤ Subgroup.normalizer (T : Set G) := by
    intro s hs
    have h1 : conjSubgroup s T ≤ (P : Subgroup G) := by
      intro x hx
      have hx' : s⁻¹ * x * s ∈ T := mem_conjSubgroup.1 hx
      have := (P : Subgroup G).mul_mem ((P : Subgroup G).mul_mem hs (hTP hx')) ((P : Subgroup G).inv_mem hs)
      simpa [mul_assoc] using this
    exact mem_normalizer_of_conjSubgroup_eq (eq_of_conj_le_pGroup hT P.isPGroup' hTP h1)
  have hdvd : (Subgroup.normalizer (T : Set G)).index ∣ (P : Subgroup G).index :=
    Subgroup.index_dvd_of_le hPN
  have hodd : Odd (P : Subgroup G).index := by
    rcases Nat.even_or_odd (P : Subgroup G).index with he | ho
    · exact absurd (even_iff_two_dvd.1 he) P.not_dvd_index
    · exact ho
  exact hodd.of_dvd_nat hdvd

theorem card_quotient_eq {H N C : Subgroup G} (hTH : T ≤ H) (hCN : C ≤ N)
    (hHnorm : ∀ g ∈ N, ∀ h ∈ H, g * h * g⁻¹ ∈ H)
    (hHC : H ⊓ C = T) (hprod : ∀ g ∈ N, ∃ h ∈ H, ∃ c ∈ C, g = h * c) :
    Nat.card (↥C ⧸ T.subgroupOf C) = Nat.card (↥N ⧸ H.subgroupOf N) := by
  classical
  let f : ↥C ⧸ T.subgroupOf C → ↥N ⧸ H.subgroupOf N :=
    Quotient.map' (fun c : ↥C => (⟨(c : G), hCN c.2⟩ : ↥N)) (fun a b hab => by
      rw [QuotientGroup.leftRel_apply] at hab ⊢
      rw [Subgroup.mem_subgroupOf] at hab ⊢
      exact hTH hab)
  have hf : ∀ c : ↥C, f (QuotientGroup.mk c) = QuotientGroup.mk ⟨(c : G), hCN c.2⟩ := fun c => rfl
  refine Nat.card_congr (Equiv.ofBijective f ⟨?_, ?_⟩)
  · intro a b hab
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    rw [hf, hf, QuotientGroup.eq] at hab
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h1 : ((a : G)⁻¹ * b) ∈ H := by simpa [Subgroup.mem_subgroupOf] using hab
    have h2 : ((a : G)⁻¹ * b) ∈ C := C.mul_mem (C.inv_mem a.2) b.2
    have := (hHC ▸ (Subgroup.mem_inf.2 ⟨h1, h2⟩) : ((a : G)⁻¹ * b) ∈ T)
    exact this
  · intro y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨h, hh, c, hc, hyhc⟩ := hprod y.1 y.2
    refine ⟨QuotientGroup.mk ⟨c, hc⟩, ?_⟩
    rw [hf, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have hcN : c ∈ N := hCN hc
    have : (c : G)⁻¹ * (y : G) = c⁻¹ * h * c := by rw [hyhc]; group
    show ((⟨c, hcN⟩ : ↥N) : G)⁻¹ * (y : G) ∈ H
    simp only
    rw [this]
    have := hHnorm c⁻¹ (N.inv_mem hcN) h hh
    simpa using this

theorem relIndex_normalizer_eq_of_natural {H : Subgroup G} (hTH : T ≤ H)
    (hHN : H ≤ Subgroup.normalizer (T : Set G))
    (hHnorm : ∀ g ∈ Subgroup.normalizer (T : Set G), ∀ h ∈ H, g * h * g⁻¹ ∈ H)
    (hnat : NaturalSL T H n 1) :
    H.relIndex (Subgroup.normalizer (T : Set G)) =
      T.relIndex (Subgroup.centralizer (T : Set G)) := by
  have hCN : Subgroup.centralizer (T : Set G) ≤ Subgroup.normalizer (T : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have hHC := inf_centralizer_eq_of_natural hTH hHN hnat
  have hprod : ∀ g ∈ Subgroup.normalizer (T : Set G), ∃ h ∈ H, ∃ c ∈ Subgroup.centralizer (T : Set G),
      g = h * c := fun g hg => exists_mul_of_natural hHN hnat hg
  exact (card_quotient_eq hTH hCN hHnorm hHC hprod).symm

theorem odd_index_of_odd_relIndex [Finite G] (hT : IsWC T) {H : Subgroup G} (hTH : T ≤ H)
    (hHN : H ≤ Subgroup.normalizer (T : Set G))
    (hHnorm : ∀ g ∈ Subgroup.normalizer (T : Set G), ∀ h ∈ H, g * h * g⁻¹ ∈ H)
    (hnat : NaturalSL T H n 1)
    (hodd : Odd (T.relIndex (Subgroup.centralizer (T : Set G)))) : Odd H.index := by
  have h1 := relIndex_normalizer_eq_of_natural hTH hHN hHnorm hnat
  have h2 := Subgroup.relIndex_mul_index hHN
  rw [← h2]
  exact (h1 ▸ hodd).mul (odd_index_normalizer hT)

end CFSG.CGT.T75P
