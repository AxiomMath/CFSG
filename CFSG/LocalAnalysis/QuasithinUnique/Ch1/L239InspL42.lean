module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239ListedInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239InspL42Core
public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalLinearFourTwo
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239

open L42Insp

theorem l239L42Overgroups : L239L42Overgroups := by
  intro G _ _ L R t hmodel hR2 hRN hRL hout htL ht1 htP X hXL hRX hCX hXne
  obtain ⟨φ⟩ := (CFSG.ComponentClassification.SymmetricLocal.lie_model_linear_four_two_iff ↥L).mp
    (Or.inl ⟨by decide, hmodel⟩)
  let Φ : ↥L →* Equiv.Perm (Fin 8) := (alternatingGroup (Fin 8)).subtype.comp φ.toMonoidHom
  have hΦinj : Function.Injective Φ := Subtype.val_injective.comp φ.injective
  have hΦA : ∀ l, Φ l ∈ A8 := fun l => (φ l).2
  have hΦsurj : ∀ a ∈ A8, ∃ l : ↥L, Φ l = a := fun a ha => ⟨φ.symm ⟨a, ha⟩, by simp [Φ]⟩
  obtain ⟨s, hsR, hsout⟩ := hout
  have hsN : s ∈ Subgroup.normalizer (L : Set G) := hsout.1
  let β : MulAut ↥L := L.normalizerMonoidHom ⟨s⁻¹, Subgroup.inv_mem _ hsN⟩
  have hβG : ∀ x : ↥L, ((β x : ↥L) : G) = s⁻¹ * x * s := by
    intro x
    simp [β]
  let α : MulAut ↥(alternatingGroup (Fin 8)) := φ.symm.trans (β.trans φ)
  obtain ⟨σ, hσα⟩ := (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 8
    (by norm_num) (by norm_num)).2 α
  have hσconj : ∀ l : ↥L, σ * Φ l * σ⁻¹ = Φ (β l) := by
    intro l
    have h1 := congrArg (fun f : MulAut ↥(alternatingGroup (Fin 8)) => ((f (φ l) : ↥(alternatingGroup (Fin 8))) :
      Equiv.Perm (Fin 8))) hσα
    simpa [α, Φ] using h1
  have hσsign : Equiv.Perm.sign σ = -1 := by
    by_contra hne
    have hσ1 : Equiv.Perm.sign σ = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
      · exact h
      · exact absurd h hne
    apply hsout.2
    obtain ⟨l, hl⟩ := hΦsurj σ⁻¹ (A8.inv_mem (Equiv.Perm.mem_alternatingGroup.mpr hσ1))
    refine ⟨(l : G), l.2, fun x hx => ?_⟩
    have h1 : Φ (β ⟨x, hx⟩) = Φ (l⁻¹ * ⟨x, hx⟩ * l) := by
      rw [← hσconj, map_mul, map_mul, map_inv, hl]
      simp
    have h2 := congrArg Subtype.val (hΦinj h1)
    rw [hβG] at h2
    exact h2
  let P_S : Subgroup (Equiv.Perm (Fin 8)) := ((R ⊓ L).subgroupOf L).map Φ
  let X_S : Subgroup (Equiv.Perm (Fin 8)) := (X.subgroupOf L).map Φ
  have hPmem : ∀ p, p ∈ P_S ↔ ∃ l : ↥L, (l : G) ∈ R ∧ Φ l = p := by
    intro p
    constructor
    · rintro ⟨l, hl, rfl⟩
      exact ⟨l, (Subgroup.mem_subgroupOf.mp hl).1, rfl⟩
    · rintro ⟨l, hl, rfl⟩
      exact ⟨l, Subgroup.mem_subgroupOf.mpr ⟨hl, l.2⟩, rfl⟩
  have hXmem : ∀ p, p ∈ X_S ↔ ∃ l : ↥L, (l : G) ∈ X ∧ Φ l = p := by
    intro p
    constructor
    · rintro ⟨l, hl, rfl⟩
      exact ⟨l, Subgroup.mem_subgroupOf.mp hl, rfl⟩
    · rintro ⟨l, hl, rfl⟩
      exact ⟨l, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
  have hPA : P_S ≤ A8 := by
    intro p hp
    obtain ⟨l, -, rfl⟩ := (hPmem p).mp hp
    exact hΦA l
  have hXA : X_S ≤ A8 := by
    intro p hp
    obtain ⟨l, -, rfl⟩ := (hXmem p).mp hp
    exact hΦA l
  have hLcard : Nat.card L = 20160 := by
    rw [Nat.card_congr φ.toEquiv]
    exact card_A8
  have hP64 : Nat.card P_S = 64 := by
    show Nat.card (((R ⊓ L).subgroupOf L).map Φ) = 64
    rw [Subgroup.card_map_of_injective hΦinj,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : R ⊓ L ≤ L)).toEquiv,
      hRL.card_eq, twoPart, hLcard]
    have hf : (20160 : ℕ).factorization 2 = 6 := by
      have h6 : 6 ≤ (20160 : ℕ).factorization 2 :=
        (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (by norm_num)).mp (by norm_num)
      have h7 : ¬ 7 ≤ (20160 : ℕ).factorization 2 := fun h =>
        absurd ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (by norm_num)).mpr h)
          (by norm_num)
      omega
    rw [hf]
    norm_num
  have ht1' : Φ ⟨t, htL⟩ ≠ 1 := fun h =>
    ht1 (congrArg Subtype.val (hΦinj (h.trans (map_one Φ).symm)))
  have htP' : ∀ p ∈ P_S, p * Φ ⟨t, htL⟩ = Φ ⟨t, htL⟩ * p := by
    intro p hp
    obtain ⟨l, hlR, rfl⟩ := (hPmem p).mp hp
    have h1 : (l : G) * t = t * (l : G) := Subgroup.mem_centralizer_iff.mp htP (l : G) ⟨hlR, l.2⟩
    rw [← map_mul, ← map_mul]
    exact congrArg Φ (Subtype.ext h1)
  have hσP : ∀ p, σ * p * σ⁻¹ ∈ P_S ↔ p ∈ P_S := by
    intro p
    constructor
    · intro hp
      obtain ⟨l', hl'R, hl'⟩ := (hPmem _).mp hp
      have hpA : p ∈ A8 := by
        have h1 : σ * p * σ⁻¹ ∈ A8 := by rw [← hl']; exact hΦA l'
        rw [Equiv.Perm.mem_alternatingGroup] at h1 ⊢
        have h2 : Equiv.Perm.sign (σ * p * σ⁻¹) = Equiv.Perm.sign p := by
          rw [map_mul, map_mul, map_inv, mul_comm (Equiv.Perm.sign σ) (Equiv.Perm.sign p),
            mul_assoc, mul_inv_cancel, mul_one]
        rw [← h2]
        exact h1
      obtain ⟨l₀, rfl⟩ := hΦsurj p hpA
      have h1 : β l₀ = l' := hΦinj (by rw [← hσconj]; exact hl'.symm)
      have h2 : (l₀ : G) = s * (l' : G) * s⁻¹ := by
        have h3 := hβG l₀
        rw [h1] at h3
        rw [h3]
        group
      refine (hPmem _).mpr ⟨l₀, ?_, rfl⟩
      rw [h2]
      exact R.mul_mem (R.mul_mem hsR hl'R) (R.inv_mem hsR)
    · intro hp
      obtain ⟨l, hlR, rfl⟩ := (hPmem p).mp hp
      refine (hPmem _).mpr ⟨β l, ?_, (hσconj l).symm⟩
      rw [hβG]
      exact R.mul_mem (R.mul_mem (R.inv_mem hsR) hlR) hsR
  have hσX : ∀ x ∈ X_S, σ * x * σ⁻¹ ∈ X_S := by
    intro x hx
    obtain ⟨l, hlX, rfl⟩ := (hXmem x).mp hx
    refine (hXmem _).mpr ⟨β l, ?_, (hσconj l).symm⟩
    rw [hβG]
    have hsNX : s ∈ Subgroup.normalizer (X : Set G) := hRX hsR
    have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hsNX) (l : G)).mp hlX
    simpa using h1
  have hCX' : ∀ c : Equiv.Perm (Fin 8), Equiv.Perm.sign c = 1 → c * Φ ⟨t, htL⟩ = Φ ⟨t, htL⟩ * c →
      c ∈ X_S := by
    intro c hc hcomm
    obtain ⟨l, rfl⟩ := hΦsurj c (Equiv.Perm.mem_alternatingGroup.mpr hc)
    have h1 : l * ⟨t, htL⟩ = ⟨t, htL⟩ * l := hΦinj (by rw [map_mul, map_mul]; exact hcomm)
    have h2 : (l : G) ∈ L ⊓ Subgroup.centralizer ({t} : Set G) :=
      ⟨l.2, Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val h1)⟩
    exact (hXmem _).mpr ⟨l, hCX h2, rfl⟩
  have hts : Equiv.Perm.sign (Φ ⟨t, htL⟩) = 1 := Equiv.Perm.mem_alternatingGroup.mp (hΦA _)
  rcases finite_main hPA hP64 hts ht1' htP' hσsign hσP hXA hCX' hσX with hcomm | hA
  · apply le_antisymm
    · intro x hx
      refine ⟨hXL hx, ?_⟩
      have h1 : Φ ⟨x, hXL hx⟩ ∈ X_S := (hXmem _).mpr ⟨⟨x, hXL hx⟩, hx, rfl⟩
      have h2 := hcomm _ h1
      rw [← map_mul, ← map_mul] at h2
      exact Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val (hΦinj h2))
    · exact hCX
  · exfalso
    apply hXne
    apply le_antisymm hXL
    intro l hl
    obtain ⟨l', hl'X, hl'⟩ := (hXmem _).mp (hA (hΦA ⟨l, hl⟩))
    have h1 : l' = ⟨l, hl⟩ := hΦinj hl'
    rw [h1] at hl'X
    exact hl'X

end CFSG.QuasithinUnique.Vol2Native.L239
