module

public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.Tactic.Group
public import Mathlib.Data.Finite.Perm

public section

namespace CFSG.AGLEmbedding.KFactProofs.J3Cover

open MulAction

section Over

variable {G Ω : Type*} [Group G] [MulAction G Ω]

theorem card_le_factorial_index [Finite G] [IsSimpleGroup G] (M : Subgroup G) (hM : M ≠ ⊤) :
    Nat.card G ≤ M.index.factorial := by
  let ρ := MulAction.toPermHom G (G ⧸ M)
  have hcore : M.normalCore = ⊥ := by
    have : M.normalCore.Normal := M.normalCore_normal
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M.normalCore with h | h
    · exact h
    · exact absurd (top_unique (h ▸ M.normalCore_le)) hM
  have hker : ρ.ker = ⊥ := by
    rw [← Subgroup.normalCore_eq_ker]
    exact hcore
  have hcard := Nat.card_le_card_of_injective ρ ((MonoidHom.ker_eq_bot_iff ρ).mp hker)
  rwa [Nat.card_perm, ← Subgroup.index_eq_card] at hcard

theorem eq_top_of_transitive [Finite G] [IsSimpleGroup G] {ω₀ : Ω} {P M : Subgroup G}
    (htr : ∀ ω, ∃ g : G, g • ω₀ = ω) (hSc : Nat.card (stabilizer G ω₀) = 1944)
    (hP : Nat.card P = 243) (hPS : P ≤ stabilizer G ω₀) (hPM : P ≤ M)
    (hMtr : ∀ ω, ∃ m ∈ M, m • ω₀ = ω) (hbig : 40320 < Nat.card G) : M = ⊤ := by
  have hGorb : orbit G ω₀ = Set.univ := Set.eq_univ_of_forall htr
  have hMorb : orbit M ω₀ = Set.univ := Set.eq_univ_of_forall fun ω => by
    obtain ⟨m, hm, hmω⟩ := hMtr ω
    exact ⟨⟨m, hm⟩, hmω⟩
  have hGc := Subgroup.card_mul_index (stabilizer G ω₀)
  rw [index_stabilizer, hGorb, Set.ncard_univ, hSc] at hGc
  have hMc := Subgroup.card_mul_index (stabilizer M ω₀)
  rw [index_stabilizer, hMorb, Set.ncard_univ] at hMc
  have h243 : 243 ∣ Nat.card (stabilizer M ω₀) := by
    have hle : P.subgroupOf M ≤ stabilizer M ω₀ := by
      intro p hp
      rw [mem_stabilizer_iff]
      exact mem_stabilizer_iff.1 (hPS (Subgroup.mem_subgroupOf.1 hp))
    have := Subgroup.card_dvd_of_le hle
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPM).toEquiv, hP] at this
  obtain ⟨k, hk⟩ := h243
  have hidx := Subgroup.card_mul_index M
  have hn : 0 < Nat.card Ω := by
    rcases Nat.eq_zero_or_pos (Nat.card Ω) with h | h
    · rw [h] at hGc; omega
    · exact h
  have hmain : 1944 = 243 * k * M.index := by
    apply Nat.eq_of_mul_eq_mul_left hn
    calc Nat.card Ω * 1944 = Nat.card G := by rw [← hGc, Nat.mul_comm]
      _ = Nat.card M * M.index := hidx.symm
      _ = Nat.card Ω * (243 * k) * M.index := by rw [← hMc, hk, Nat.mul_comm (243 * k)]
      _ = Nat.card Ω * (243 * k * M.index) := Nat.mul_assoc _ _ _
  have hle8 : M.index ≤ 8 := by
    have h8 : k * M.index = 8 := by
      rw [Nat.mul_assoc] at hmain
      omega
    exact Nat.le_of_dvd (by decide) (Dvd.intro_left k h8)
  by_cases hMtop : M = ⊤
  · exact hMtop
  · exfalso
    have := card_le_factorial_index M hMtop
    have h8 : M.index.factorial ≤ (8 : ℕ).factorial := Nat.factorial_le hle8
    have h40 : (8 : ℕ).factorial = 40320 := by decide
    omega

theorem sup_conj_eq_top [Finite G] [IsSimpleGroup G] {ω₀ : Ω} {P S₀ : Subgroup G} {R : Set Ω}
    (htr : ∀ ω, ∃ g : G, g • ω₀ = ω) (hSc : Nat.card (stabilizer G ω₀) = 1944)
    (hP : Nat.card P = 243) (hPS : P ≤ stabilizer G ω₀)
    (hSN : stabilizer G ω₀ ≤ Subgroup.normalizer (P : Set G)) (hS₀ : S₀ ≤ stabilizer G ω₀)
    (hcov : ∀ ω, ∃ r ∈ R, ∃ k ∈ S₀, k • r = ω)
    (hroots : ∀ r ∈ R, r ≠ ω₀ → ∃ gr : G, gr • ω₀ = r ∧
      ∀ ω, ∃ κ ∈ P ⊔ P.map (MulAut.conj gr).toMonoidHom, κ • ω₀ = ω)
    (hbig : 40320 < Nat.card G) {g : G} (hg : g ∉ stabilizer G ω₀) :
    P ⊔ P.map (MulAut.conj g).toMonoidHom = ⊤ := by
  have hSfix : ∀ s ∈ stabilizer G ω₀, s • ω₀ = ω₀ := fun s hs => mem_stabilizer_iff.1 hs
  have hgne : g • ω₀ ≠ ω₀ := fun h => hg (mem_stabilizer_iff.2 h)
  obtain ⟨r, hrR, k, hkS₀, hkr⟩ := hcov (g • ω₀)
  have hkS : k ∈ stabilizer G ω₀ := hS₀ hkS₀
  have hr : r ≠ ω₀ := by
    rintro rfl
    exact hgne (hkr.symm.trans (hSfix k hkS))
  obtain ⟨gr, hgr, hK⟩ := hroots r hrR hr
  have hs : g⁻¹ * (k * gr) ∈ stabilizer G ω₀ := by
    rw [mem_stabilizer_iff, mul_smul, mul_smul, hgr, hkr, inv_smul_smul]
  have hkgr : k * gr = g * (g⁻¹ * (k * gr)) := by group
  generalize g⁻¹ * (k * gr) = s at hs hkgr
  have hQ : P ⊔ P.map (MulAut.conj gr).toMonoidHom ≤
      (P ⊔ P.map (MulAut.conj g).toMonoidHom).comap (MulAut.conj k).toMonoidHom := by
    refine sup_le ?_ ?_
    · intro p hp
      exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.1 (hSN hkS) p).1 hp)
    · rintro _ ⟨p, hp, rfl⟩
      have hsp : s * p * s⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.1 (hSN hs) p).1 hp
      refine Subgroup.mem_sup_right ⟨s * p * s⁻¹, hsp, ?_⟩
      show g * (s * p * s⁻¹) * g⁻¹ = k * (gr * p * gr⁻¹) * k⁻¹
      calc g * (s * p * s⁻¹) * g⁻¹ = (g * s) * p * (g * s)⁻¹ := by group
        _ = (k * gr) * p * (k * gr)⁻¹ := by rw [hkgr]
        _ = k * (gr * p * gr⁻¹) * k⁻¹ := by group
  refine eq_top_of_transitive htr hSc hP hPS le_sup_left (fun ω => ?_) hbig
  obtain ⟨κ, hκ, hκω⟩ := hK (k⁻¹ • ω)
  refine ⟨k * κ * k⁻¹, hQ hκ, ?_⟩
  rw [mul_smul, mul_smul, hSfix k⁻¹ ((stabilizer G ω₀).inv_mem hkS), hκω, smul_inv_smul]

theorem le_normalizer_or_eq_top [Finite G] [IsSimpleGroup G] {ω₀ : Ω} {P S₀ : Subgroup G}
    {R : Set Ω} (htr : ∀ ω, ∃ g : G, g • ω₀ = ω) (hSc : Nat.card (stabilizer G ω₀) = 1944)
    (hP : Nat.card P = 243) (hPS : P ≤ stabilizer G ω₀)
    (hSN : stabilizer G ω₀ ≤ Subgroup.normalizer (P : Set G)) (hS₀ : S₀ ≤ stabilizer G ω₀)
    (hcov : ∀ ω, ∃ r ∈ R, ∃ k ∈ S₀, k • r = ω)
    (hroots : ∀ r ∈ R, r ≠ ω₀ → ∃ gr : G, gr • ω₀ = r ∧
      ∀ ω, ∃ κ ∈ P ⊔ P.map (MulAut.conj gr).toMonoidHom, κ • ω₀ = ω)
    (hbig : 40320 < Nat.card G) {K : Subgroup G} (hPK : P ≤ K) :
    K ≤ Subgroup.normalizer (P : Set G) ∨ K = ⊤ := by
  by_cases h : K ≤ Subgroup.normalizer (P : Set G)
  · exact Or.inl h
  · right
    obtain ⟨y, hyK, hyN⟩ := IsConcreteLE.not_le_iff_exists.1 h
    have hy : y ∉ stabilizer G ω₀ := fun hy => hyN (hSN hy)
    have := sup_conj_eq_top htr hSc hP hPS hSN hS₀ hcov hroots hbig hy
    rw [eq_top_iff, ← this]
    refine sup_le hPK ?_
    rintro _ ⟨p, hp, rfl⟩
    exact K.mul_mem (K.mul_mem hyK (hPK hp)) (K.inv_mem hyK)

end Over

end CFSG.AGLEmbedding.KFactProofs.J3Cover
