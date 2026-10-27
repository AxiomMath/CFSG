module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL3CharPar
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL3CharTr
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Orth3Mod

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.GH74.KGroups.L3Eps

section Field

variable {F : Type} [Field F] [Finite F]

theorem charP_of_dvd_card (p : ℕ) [Fact p.Prime] (hpF : p ∣ Nat.card F) : CharP F p := by
  have := Fintype.ofFinite F
  obtain ⟨n, hch, hcard⟩ := FiniteField.card F (ringChar F)
  have hpdvd : p ∣ ringChar F ^ (n : ℕ) := by
    rw [← hcard, ← Nat.card_eq_fintype_card]
    exact hpF
  have := (Nat.prime_dvd_prime_iff_eq (Fact.out) hch).mp (Nat.Prime.dvd_of_dvd_pow (Fact.out) hpdvd)
  rw [this]
  exact ringChar.charP F

end Field

section Main

variable {A : Type} [Group A] {K : Subgroup A} {H : Type} [Group H]

theorem mem_normalizer_comap_emb (e : ↥K ≃* H) {S : Subgroup A} {h : H}
    (hh : emb e h ∈ normalizer (S : Set A)) :
    h ∈ normalizer ((S.comap (emb e) : Subgroup H) : Set H) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  rw [Subgroup.mem_comap, Subgroup.mem_comap, map_mul, map_mul, map_inv]
  exact Subgroup.mem_normalizer_iff.mp hh (emb e y)

theorem emb_mem_centralizer_iff (e : ↥K ≃* H) (t h : H) :
    emb e h ∈ centralizer ({emb e t} : Set A) ↔ h ∈ centralizer ({t} : Set H) := by
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff, ← map_mul,
    ← map_mul]
  exact (emb_injective e).eq_iff

theorem isPGroup_comap_emb (e : ↥K ≃* H) {p : ℕ} {S : Subgroup A} (hS : IsPGroup p ↥S) :
    IsPGroup p ↥(S.comap (emb e)) :=
  hS.comap_of_injective (emb e) (emb_injective e)

end Main

theorem fl3_inner_char {A : Type} [Group A] [Finite A] (K : Subgroup A) {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (h3 : 3 ≤ Nat.card F) (e : ↥K ≃* projectiveSL 3 F) (p : ℕ)
    [Fact p.Prime] (hpF : p ∣ Nat.card F) (X : Subgroup A) (hX : IsPGroup p ↥X) (hX1 : X ≠ ⊥)
    (hXK : X ≤ K)
    (hJ : ∀ j : ↥K, e j * tInv = tInv * e j → (j : A) ∈ normalizer (X : Set A)) :
    ∃ P : Subgroup A, IsMaxParabolicP p K P ∧ X = Op p P ∧
      P = X ⊔ K ⊓ centralizer ({((e.symm tInv : ↥K) : A)} : Set A) ∧
      IsElementaryAbelian p ↥X ∧ Nat.card ↥X = Nat.card F ^ 2 := by
  have _ := h3
  have h2 := two_ne_zero_of_odd_card hodd
  have := charP_of_dvd_card (F := F) p hpF
  have : Finite (projectiveSL 3 F) := Finite.of_equiv ↥K e.toEquiv
  have hinj := emb_injective e
  have hCenD : ∀ g ∈ CenD F, proj 3 F g * tInv = tInv * proj 3 F g := by
    intro g hg
    rw [tInv, ← map_mul, ← map_mul, mem_CenD.mp hg]
  have hY : IsPGroup p ↥(X.comap (emb e)) := isPGroup_comap_emb e hX
  have hY1 : X.comap (emb e) ≠ ⊥ := by
    intro h
    apply hX1
    rw [← map_comap_emb e hXK, h, Subgroup.map_bot]
  have hNY : ∀ g ∈ CenD F, proj 3 F g ∈ normalizer ((X.comap (emb e) : Subgroup _) : Set _) := by
    intro g hg
    apply mem_normalizer_comap_emb e
    exact hJ (e.symm (proj 3 F g)) (by simpa using hCenD g hg)
  obtain ⟨W, ψ, hbot, htop, hψinj, hψY, hstab⟩ := classify_model h2 p (X.comap (emb e)) hY hY1 hNY
  have hXrange : X = ((emb e).comp ψ).range := by
    rw [MonoidHom.range_comp, hψY, map_comap_emb e hXK]
  have hcompinj : Function.Injective ((emb e).comp ψ) := hinj.comp hψinj
  have hcard : Nat.card ↥X = Nat.card F ^ 2 := by
    rw [hXrange]
    exact card_range_eq _ hcompinj
  have hea : IsElementaryAbelian p ↥X := by
    rw [hXrange]
    exact isElementaryAbelian_range _
  have hP : X ⊔ K ⊓ centralizer ({((e.symm tInv : ↥K) : A)} : Set A) =
      (projStabilizer W).map (emb e) := by
    rw [hstab, Subgroup.map_sup]
    congr 1
    · exact (map_comap_emb e hXK).symm
    · ext a
      constructor
      · rintro ⟨haK, has⟩
        refine ⟨e ⟨a, haK⟩, (emb_mem_centralizer_iff e tInv _).mp ?_, emb_e e ⟨a, haK⟩⟩
        rw [emb_e]
        exact has
      · rintro ⟨h, hh, rfl⟩
        exact ⟨(e.symm h).2, (emb_mem_centralizer_iff e tInv h).mpr hh⟩
  have hM : projStabilizer W ∈ maximalParabolics (projectiveSL 3 F) p := by
    rw [(maximal_parabolics (K := F) (n := 3) p (by norm_num)).1]
    exact ⟨W, ⟨hbot, htop⟩, rfl⟩
  have hmax : IsMaxParabolicP p K ((projStabilizer W).map (emb e)) :=
    isMaxParabolicP_map_emb p e hM
  set P : Subgroup A := X ⊔ K ⊓ centralizer ({((e.symm tInv : ↥K) : A)} : Set A) with hPdef
  have hCP : K ⊓ centralizer ({((e.symm tInv : ↥K) : A)} : Set A) ≤ P := le_sup_right
  have hXP : X ≤ P := le_sup_left
  have hPK : P ≤ K := sup_le hXK inf_le_left
  have hnorm : P ≤ normalizer (X : Set A) := by
    refine sup_le Subgroup.le_normalizer ?_
    rintro a ⟨haK, has⟩
    have hc : e ⟨a, haK⟩ * tInv = tInv * e ⟨a, haK⟩ := by
      have : emb e (e ⟨a, haK⟩) ∈ centralizer ({emb e tInv} : Set A) := by
        rw [emb_e]
        exact has
      exact Subgroup.mem_centralizer_singleton_iff.mp ((emb_mem_centralizer_iff e tInv _).mp this)
    exact hJ ⟨a, haK⟩ hc
  have hXOp : X ≤ Op p P := le_Op_of_normal' hXP hnorm hX
  have hOpX : Op p P ≤ X := by
    have hNP : Op p P ≤ P := Op_le' p P
    have hNK : Op p P ≤ K := hNP.trans hPK
    have hNp : IsPGroup p ↥(Op p P) := isPGroup_Op p P
    have hPN : P ≤ normalizer (Op p P : Set A) := le_normalizer_Op p P
    have hYN : IsPGroup p ↥((Op p P).comap (emb e)) := isPGroup_comap_emb e hNp
    have hYN1 : (Op p P).comap (emb e) ≠ ⊥ := by
      intro h
      apply hX1
      have : X ≤ ⊥ := by
        calc X = (X.comap (emb e)).map (emb e) := (map_comap_emb e hXK).symm
          _ ≤ ((Op p P).comap (emb e)).map (emb e) :=
            Subgroup.map_mono (Subgroup.comap_mono hXOp)
          _ = ⊥ := by rw [h, Subgroup.map_bot]
      exact le_bot_iff.mp this
    have hNYN : ∀ g ∈ CenD F,
        proj 3 F g ∈ normalizer (((Op p P).comap (emb e) : Subgroup _) : Set _) := by
      intro g hg
      apply mem_normalizer_comap_emb e
      apply hPN
      apply hCP
      refine ⟨(e.symm _).2, ?_⟩
      exact (emb_mem_centralizer_iff e tInv _).mpr
        (Subgroup.mem_centralizer_singleton_iff.mpr (hCenD g hg))
    obtain ⟨W', ψ', -, -, hψ'inj, hψ'Y, -⟩ := classify_model h2 p ((Op p P).comap (emb e)) hYN hYN1 hNYN
    have hNrange : Op p P = ((emb e).comp ψ').range := by
      rw [MonoidHom.range_comp, hψ'Y, map_comap_emb e hNK]
    have hNcard : Nat.card ↥(Op p P) = Nat.card F ^ 2 := by
      rw [hNrange]
      exact card_range_eq _ (hinj.comp hψ'inj)
    have heq : X = Op p P := Subgroup.eq_of_le_of_card_ge hXOp (by rw [hNcard, hcard])
    exact heq.ge
  exact ⟨P, by rw [hP]; exact hmax, le_antisymm hXOp hOpX, rfl, hea, hcard⟩

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
