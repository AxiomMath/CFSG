module

public import CFSG.Dihedral.Glauberman.DicksonMaxUp
public import CFSG.Walter.PSL2Facts.Odd

public noncomputable section

namespace CFSG.ComponentClassification.AutL2Facts

open CFSG GorensteinWalter Subgroup

variable {F : Type} [Field F] [Finite F]

theorem isCoatom_centralizer_involution {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hF : Nat.card F = p ^ f) (h4 : p ^ f % 4 = 1) (h13 : 13 ≤ p ^ f) {t : PSL2 F}
    (ht : orderOf t = 2) : IsCoatom (centralizer ({t} : Set (PSL2 F))) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype F := Fintype.ofFinite F
  have hq : Fintype.card F = p ^ f := by rw [← Nat.card_eq_fintype_card, hF]
  have hf0 : 0 < f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · rw [h, pow_zero] at h13
      omega
    · exact h
  have hodd : IsOddPrimePower (Nat.card F) := ⟨p, f, hp, hp.odd_of_ne_two hp2, hf0, hF⟩
  have hF2 : ringChar F ≠ 2 :=
    CFSG.Glauberman.Dickson.MaxUp.ringChar_ne_two hF hp2
  have hTcard : Nat.card (CFSG.PSL2Table.splitTorus F) = (Fintype.card F - 1) / 2 :=
    CFSG.Glauberman.Dickson.MaxStructure.card_splitTorus_eq hF2
  have hTeven : 2 ∣ Nat.card (CFSG.PSL2Table.splitTorus F) := by
    rw [hTcard, hq]
    omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t₀, ht₀⟩ := exists_prime_orderOf_dvd_card' 2 hTeven
  have ht₀' : orderOf (t₀ : PSL2 F) = 2 := by rw [Subgroup.orderOf_coe, ht₀]
  have hinv : ∀ x : PSL2 F, orderOf x = 2 → BenderSuzuki.PFAppendixIII.IsInvolution x :=
    fun x hx => ⟨fun h => by rw [h, orderOf_one] at hx; omega,
      by have h := pow_orderOf_eq_one x; rwa [hx] at h⟩
  obtain ⟨g, hg⟩ := psl2_involutions_conjugate_of_odd_prime_power F hodd (t₀ : PSL2 F) t
    (hinv _ ht₀') (hinv _ ht)
  have hR : zpowers t ≤ (CFSG.PSL2Table.splitTorus F).map (MulAut.conj g).toMonoidHom := by
    rw [zpowers_le]
    exact ⟨t₀, t₀.2, by rw [← hg]; rfl⟩
  have hR1 : zpowers t ≠ ⊥ := by
    intro h
    have : t ∈ (⊥ : Subgroup (PSL2 F)) := h ▸ mem_zpowers t
    rw [mem_bot] at this
    rw [this, orderOf_one] at ht
    omega
  have hle : centralizer ({t} : Set (PSL2 F)) ≤
      (normalizer (CFSG.PSL2Table.splitTorus F : Set (PSL2 F))).map
        (MulAut.conj g).toMonoidHom := by
    calc centralizer ({t} : Set (PSL2 F)) = centralizer (zpowers t : Set (PSL2 F)) := by
          rw [zpowers_eq_closure, centralizer_closure]
      _ ≤ normalizer (zpowers t : Set (PSL2 F)) := centralizer_le_normalizer _
      _ ≤ _ := CFSG.Glauberman.Dickson.MaxStructure.normalizer_le_of_le_conj_splitTorus hF2
          (by omega) g hR hR1
  have hcard : Nat.card ((normalizer (CFSG.PSL2Table.splitTorus F : Set (PSL2 F))).map
      (MulAut.conj g).toMonoidHom) ≤ Nat.card (centralizer ({t} : Set (PSL2 F))) := by
    rw [card_map_of_injective (MulAut.conj g).injective,
      CFSG.PSL2Table.card_normalizer_splitTorus hF2 (by omega), hTcard,
      ((CFSG.Walter.psl2_centralizer_involution F hF (hp.odd_of_ne_two hp2) hf0 ht).1 h4).1, hq]
    omega
  rw [Subgroup.eq_of_le_of_card_ge hle hcard,
    CFSG.Glauberman.Dickson.MaxStructure.isCoatom_map_conj_iff]
  exact CFSG.Glauberman.Dickson.MaxUp.isCoatom_normalizer_splitTorus hF hp2 h13

theorem centralizer_ne_of_involution {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hF : Nat.card F = p ^ f) (h4 : p ^ f % 4 = 1) (h13 : 13 ≤ p ^ f) {t₁ t₂ : PSL2 F}
    (ht₁ : orderOf t₁ = 2) (ht₂ : orderOf t₂ = 2) (hne : t₁ ≠ t₂) :
    centralizer ({t₁} : Set (PSL2 F)) ≠ centralizer ({t₂} : Set (PSL2 F)) := by
  intro h
  have : Fact p.Prime := ⟨hp⟩
  have hf0 : 0 < f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · rw [h0, pow_zero] at h13
      omega
    · exact h0
  obtain ⟨-, ⟨ρ⟩⟩ := (CFSG.Walter.psl2_centralizer_involution F hF (hp.odd_of_ne_two hp2) hf0
    ht₁).1 h4
  have hn4 : 4 ≤ (p ^ f - 1) / 2 := by omega
  have hneven : Even ((p ^ f - 1) / 2) := ⟨(p ^ f - 1) / 4, by omega⟩
  have hZ : Nat.card (center (centralizer ({t₁} : Set (PSL2 F)))) = 2 := by
    rw [Nat.card_congr (Subgroup.centerCongr ρ).toEquiv]
    exact CFSG.Walter.card_center_dihedralGroup hn4 hneven
  have h1 : t₁ ∈ centralizer ({t₁} : Set (PSL2 F)) := mem_centralizer_singleton_iff.mpr rfl
  have h2 : t₂ ∈ centralizer ({t₁} : Set (PSL2 F)) := by
    rw [h]
    exact mem_centralizer_singleton_iff.mpr rfl
  have hz1 : (⟨t₁, h1⟩ : centralizer ({t₁} : Set (PSL2 F))) ∈ center _ := by
    rw [mem_center_iff]
    intro x
    exact Subtype.ext (mem_centralizer_singleton_iff.mp x.2)
  have hz2 : (⟨t₂, h2⟩ : centralizer ({t₁} : Set (PSL2 F))) ∈ center _ := by
    rw [mem_center_iff]
    intro x
    have hx : (x : PSL2 F) ∈ centralizer ({t₂} : Set (PSL2 F)) := h ▸ x.2
    exact Subtype.ext (mem_centralizer_singleton_iff.mp hx)
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : center (centralizer ({t₁} : Set (PSL2 F))))).mp
    hZ
  have hne1 : ∀ (s : PSL2 F) (hs : s ∈ centralizer ({t₁} : Set (PSL2 F)))
      (hsz : (⟨s, hs⟩ : centralizer ({t₁} : Set (PSL2 F))) ∈ center _), orderOf s = 2 →
      (⟨⟨s, hs⟩, hsz⟩ : center (centralizer ({t₁} : Set (PSL2 F)))) ≠ 1 := by
    intro s hs hsz hs2 h1'
    have : s = 1 := congrArg (fun z : center (centralizer ({t₁} : Set (PSL2 F))) =>
      ((z : centralizer ({t₁} : Set (PSL2 F))) : PSL2 F)) h1'
    rw [this, orderOf_one] at hs2
    omega
  have e1 := hy _ (hne1 t₁ h1 hz1 ht₁)
  have e2 := hy _ (hne1 t₂ h2 hz2 ht₂)
  apply hne
  have := e1.trans e2.symm
  exact congrArg (fun z : center (centralizer ({t₁} : Set (PSL2 F))) =>
    ((z : centralizer ({t₁} : Set (PSL2 F))) : PSL2 F)) this

end CFSG.ComponentClassification.AutL2Facts
