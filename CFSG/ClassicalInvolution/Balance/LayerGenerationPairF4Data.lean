module

public import CFSG.LieType.Chevalley.RootCommutator
public import CFSG.LieType.Chevalley.SignCharacterMasks
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps
  CFSG.LieType.Steinberg.Adjoint

section Commutator

theorem repShapeCheck_F4_two : (repsOf .F4).all (repShapeCheck .F4 2) = true := by
  decide +kernel

theorem hasCommFormula_rep_F4_two {r : ℕ × ℕ × List Factor} (hr : r ∈ repsOf .F4) :
    (rootOperatorFamily .F4).HasCommFormula 2 (Tag.F4.rootCertificate.root r.1)
      (Tag.F4.rootCertificate.root r.2.1) := by
  have h := repShapeCheck_F4_two
  rw [List.all_eq_true] at h
  have h' := h r hr
  simp only [repShapeCheck, Bool.and_eq_true, Nat.blt_eq, decide_eq_true_eq, beq_iff_eq,
    List.all_eq_true, Nat.ble_eq] at h'
  obtain ⟨⟨⟨⟨hx, hy⟩, hkeys⟩, hbox⟩, hC⟩ := h'
  have hnd := keys_nodup_of_mem_repsOf hr
  refine ⟨factorConst r.2.2, fun p hp => ?_, commFormula_rep hr⟩
  have hkeys' : r.2.2.map (fun f => (f.1, f.2.1)) =
      commPairs .F4 (Tag.F4.rootCertificate.root r.1) (Tag.F4.rootCertificate.root r.2.1) :=
    hkeys.trans (commPairsAt_eq _ _)
  rw [← hkeys', List.mem_map] at hp
  obtain ⟨f, hf, rfl⟩ := hp
  rw [factorConst_of_mem hnd hf]
  obtain ⟨h1, h2⟩ := hC f hf
  rw [Int.abs_eq_natAbs]
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

theorem hasCommFormula_F4_two {α β : Fin Tag.F4.rank → ℤ} (hα : IsRoot .F4 α) (hβ : IsRoot .F4 β)
    (hne : α ≠ β) (hne' : α ≠ -β) : (rootOperatorFamily .F4).HasCommFormula 2 α β := by
  obtain ⟨r, hr, w, rfl, rfl⟩ := exists_smul_rep hα hβ hne hne'
  exact (hasCommFormula_rep_F4_two hr).smul w

theorem exists_pinnedX_commFormula_F4 {α β : Fin Tag.F4.rank → ℤ} (hα : IsRoot .F4 α)
    (hβ : IsRoot .F4 β) (hne : α ≠ β) (hne' : α ≠ -β) :
    ∃ C : ℕ × ℕ → ℤ, (∀ p ∈ commPairs .F4 α β, 1 ≤ |C p| ∧ |C p| ≤ 2) ∧
      ∀ (R : Type) [CommRing R] (c d : R),
        pinnedX .F4 R α c * pinnedX .F4 R β d * pinnedX .F4 R α (-c) * pinnedX .F4 R β (-d) =
          ((commPairs .F4 α β).map fun p =>
            pinnedX .F4 R (p.1 • α + p.2 • β) ((C p : R) * c ^ p.1 * d ^ p.2)).prod := by
  obtain ⟨C, hC, hF⟩ := hasCommFormula_F4_two hα hβ hne hne'
  refine ⟨fun p => (rootOperatorFamily .F4).pinnedFamilySign (p.1 • α + p.2 • β) *
      (rootOperatorFamily .F4).pinnedFamilySign α ^ p.1 *
      (rootOperatorFamily .F4).pinnedFamilySign β ^ p.2 * C p, fun p hp => ?_,
    pinnedX_commFormula_of_commFormula hα hβ hF⟩
  rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_pow, abs_pinnedFamilySign, abs_pinnedFamilySign,
    abs_pinnedFamilySign, one_pow, one_pow, one_mul, one_mul, one_mul]
  exact hC p hp

end Commutator

section Check

local notation "ρ" => Tag.F4.rootCertificate.root

theorem isRoot_F4_iff {v : Fin Tag.F4.rank → ℤ} :
    IsRoot .F4 v ↔ ∃ k < 48, ρ k = v := by
  rw [RootCertificate.isRoot_iff (Tag.rootCertificate_check .F4),
    show Tag.F4.rootCertificate.roots.length = 48 by decide]

@[expose] def F4ShortWitness (m : Fin 4 → Bool) (x y z : ℕ) : Prop :=
  iform (ρ y) (ρ y) = 4 ∧ maskPairing (τ := .F4) m (ρ y) % 2 = 0 ∧ ρ z + ρ y = ρ x ∧
    ρ z ≠ ρ y ∧ ρ z ≠ -ρ y ∧ commPairsAt .F4 z y = [(1, 1), (2, 1)] ∧
    ∃ w < 48, ρ w = 2 • ρ z + ρ y ∧ iform (ρ w) (ρ w) = 4

instance (m : Fin 4 → Bool) (x y z : ℕ) : Decidable (F4ShortWitness m x y z) := by
  unfold F4ShortWitness
  infer_instance

theorem f4_short_check : ∀ b₀ b₁ b₂ b₃ : Bool, ∀ x < 48, iform (ρ x) (ρ x) ≠ 4 →
    maskPairing (τ := .F4) ![b₀, b₁, b₂, b₃] (ρ x) % 2 = 0 →
    ∃ y < 48, ∃ z < 48, F4ShortWitness ![b₀, b₁, b₂, b₃] x y z := by
  decide +kernel

theorem f4_short_witness (m : Fin Tag.F4.rank → Bool) {s' : Fin Tag.F4.rank → ℤ}
    (hs' : IsRoot .F4 s') (hl : iform s' s' ≠ 4) (hm : maskPairing m s' % 2 = 0) :
    ∃ s β : Fin Tag.F4.rank → ℤ, IsRoot .F4 s ∧ IsRoot .F4 β ∧ iform β β = 4 ∧
      maskPairing m β % 2 = 0 ∧ s + β = s' ∧ s ≠ β ∧ s ≠ -β ∧
      commPairs .F4 s β = [(1, 1), (2, 1)] ∧ IsRoot .F4 (2 • s + β) ∧
      iform (2 • s + β) (2 • s + β) = 4 := by
  obtain ⟨x, hx, rfl⟩ := isRoot_F4_iff.1 hs'
  have hm' : m = ![m (0 : Fin 4), m (1 : Fin 4), m (2 : Fin 4), m (3 : Fin 4)] := by
    funext i
    fin_cases i <;> rfl
  rw [hm'] at hm ⊢
  obtain ⟨y, hy, z, hz, h1, h2, h3, h4, h5, h6, w, hw, h7, h8⟩ :=
    f4_short_check (m (0 : Fin 4)) (m (1 : Fin 4)) (m (2 : Fin 4)) (m (3 : Fin 4)) x hx hl hm
  have hroot : ∀ {k : ℕ}, k < 48 → IsRoot .F4 (ρ k) := fun {k} hk =>
    isRoot_F4_iff.2 ⟨k, hk, rfl⟩
  refine ⟨ρ z, ρ y, hroot hz, hroot hy, h1, h2, h3, h4, h5, ?_, ?_, ?_⟩
  · rw [← commPairsAt_eq]
    exact h6
  · rw [← h7]
    exact hroot hw
  · rw [← h7]
    exact h8

end Check

end CFSG.ClassicalInvolution.Balance.Bootstrap
