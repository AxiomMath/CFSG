module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSp48Typ
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSp48Lat
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveTauGrp

public section

namespace CFSG.AGLEmbedding.KFactProofs.Sp48

open CFSG.Quasithin CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.LieType.Steinberg.Sp (blockMat)
open CFSG.QuasithinUnique.Lin2.Five (tauEquiv tauMat)
open scoped MatrixGroups Matrix

@[expose] noncomputable def tauG : Sp8 ≃* Sp8 := tauEquiv (F := GF8)

theorem mat_tauG (g : Sp8) : mat 2 GF8 (tauG g) = tauMat (mat 2 GF8 g) := rfl

@[expose] def tauZ1c : Array ℕ := #[1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0]

theorem mat_tau_spZ1 : mat 2 GF8 (tauG spZ1) = decode tauZ1c := by
  rw [mat_tauG, spZ1, mat_longBlock, slZ_val]
  decide +kernel

theorem fpf_tau_spZ1 : SpFPF (tauG spZ1) := by
  intro v hv
  rw [mat_tau_spZ1] at hv
  have e0 := congrFun hv (Sum.inl 0)
  have e1 := congrFun hv (Sum.inl 1)
  have e2 := congrFun hv (Sum.inr 0)
  have e3 := congrFun hv (Sum.inr 1)
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, decode, tauZ1c, ix,
    gf8_ofNat_zero, gf8_ofNat_one] at e0 e1 e2 e3
  funext i
  rcases i with i | i <;> fin_cases i <;> simp_all

theorem wrp_mono {X Y : Subgroup Sl28} (h : X ≤ Y) : wrp X ≤ wrp Y := by
  rintro g ⟨x, hx, y, hy, hg⟩
  exact ⟨x, h hx, y, h hy, hg⟩

theorem sylow_conj_sp8 (hcard : Nat.card Sp8 = 3 ^ 4 * 13045760) (S : Subgroup Sp8)
    (hS : Nat.card S = 3 ^ 4) : ∃ m : Sp8, ∀ x, x ∈ spT0 ↔ m⁻¹ * x * m ∈ S := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hM : 3 ^ 4 ∣ Nat.card (⊤ : Subgroup Sp8) := by
    rw [Subgroup.card_top, hcard]
    exact Dvd.intro _ rfl
  have hM' : ¬ 3 ^ (4 + 1) ∣ Nat.card (⊤ : Subgroup Sp8) := by
    rw [Subgroup.card_top, hcard]
    intro h
    have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three
      (by norm_num : (3 ^ 4 * 13045760 : ℕ) ≠ 0)).1 h
    have hfac : (3 ^ 4 * 13045760 : ℕ).factorization 3 = 4 := by
      rw [Nat.factorization_mul (by norm_num) (by norm_num)]
      simp only [Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_three]
      have h2 : (13045760 : ℕ).factorization 3 = 0 :=
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)
      simp [h2]
    omega
  obtain ⟨m, -, hm⟩ := exists_conj_of_sylow_in (p := 3) (⊤ : Subgroup Sp8) hM hM'
    S spT0 le_top le_top hS (by rw [card_spT0]; norm_num)
  exact ⟨m, hm⟩

theorem exists_theta (hcard : Nat.card Sp8 = 3 ^ 4 * 13045760) :
    ∃ θ : Sp8 ≃* Sp8, (∀ x, x ∈ spT0 ↔ θ x ∈ spT0) ∧ θ spZ1 = spZ12 := by
  have hS : Nat.card (spT0.map tauG.toMonoidHom) = 3 ^ 4 := by
    rw [Subgroup.card_map_of_injective (f := tauG.toMonoidHom) tauG.injective, card_spT0]
    norm_num
  obtain ⟨m, hm⟩ := sylow_conj_sp8 hcard _ hS
  have hθ' : ∀ x, m * tauG x * m⁻¹ ∈ spT0 ↔ x ∈ spT0 := by
    intro x
    rw [hm, show m⁻¹ * (m * tauG x * m⁻¹) * m = tauG x by group]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = x := tauG.injective hyx
      rwa [← this]
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hz1 : m * tauG spZ1 * m⁻¹ ∈ spT0 := (hθ' _).2 spZ1_mem
  have hz3 : (m * tauG spZ1 * m⁻¹) ^ 3 = 1 := by
    rw [conj_pow, ← map_pow, spZ1_pow3, map_one]
    group
  have hz1' : m * tauG spZ1 * m⁻¹ ≠ 1 := by
    intro h
    have : tauG spZ1 = 1 := by
      calc tauG spZ1 = m⁻¹ * (m * tauG spZ1 * m⁻¹) * m := by group
        _ = 1 := by rw [h]; group
    exact spZ1_ne_one (tauG.injective (by rw [this, map_one]))
  have hfpf : SpFPF (m * tauG spZ1 * m⁻¹) := (SpFPF_conj m _).2 fpf_tau_spZ1
  obtain ⟨n, hn, hnz⟩ : ∃ n ∈ wrp slD, m * tauG spZ1 * m⁻¹ = n * spZ12 * n⁻¹ := by
    rcases spE_cases hz1 hz3 hz1' with ⟨n, hn, hnz⟩ | h
    · exfalso
      rw [hnz] at hfpf
      exact not_SpFPF_spZ1 ((SpFPF_conj n spZ1).1 hfpf)
    · exact h
  have hnN : n ∈ Subgroup.normalizer (spT0 : Set Sp8) := wrp_eq_normalizer ▸ hn
  refine ⟨tauG.trans (MulAut.conj (n⁻¹ * m)), fun x => ?_, ?_⟩
  · show x ∈ spT0 ↔ (n⁻¹ * m) * tauG x * (n⁻¹ * m)⁻¹ ∈ spT0
    have hconj : (n⁻¹ * m) * tauG x * (n⁻¹ * m)⁻¹ = n⁻¹ * (m * tauG x * m⁻¹) * n := by group
    rw [hconj, ← hθ' x]
    have hn' : n⁻¹ ∈ Subgroup.normalizer (spT0 : Set Sp8) := Subgroup.inv_mem _ hnN
    have h1 := Subgroup.mem_normalizer_iff.1 hn' (m * tauG x * m⁻¹)
    rw [inv_inv] at h1
    exact h1
  · show (n⁻¹ * m) * tauG spZ1 * (n⁻¹ * m)⁻¹ = spZ12
    have : (n⁻¹ * m) * tauG spZ1 * (n⁻¹ * m)⁻¹ = n⁻¹ * (m * tauG spZ1 * m⁻¹) * n := by group
    rw [this, hnz]
    group

theorem sp8_lattice (hcard : Nat.card Sp8 = 3 ^ 4 * 13045760) (hsimple : IsSimpleGroup Sp8) :
    ∃ θ : Sp8 ≃* Sp8, (∀ x, x ∈ spT0 ↔ θ x ∈ spT0) ∧ θ spZ1 = spZ12 ∧
      ∀ H : Subgroup Sp8, wrp slD ≤ H →
        H = wrp slD ∨ H = wrp (⊤ : Subgroup Sl28) ∨
          H = (wrp (⊤ : Subgroup Sl28)).map θ.toMonoidHom ∨ H = ⊤ := by
  obtain ⟨θ, hθT, hθz⟩ := exists_theta hcard
  refine ⟨θ, hθT, hθz, fun H hH => ?_⟩
  let D : LatData Sp8 :=
    { T0 := spT0
      N := wrp slD
      M1 := wrp (⊤ : Subgroup Sl28)
      θ := θ
      zI := spZ1
      zII := spZ12
      card_T0 := card_spT0
      comm_T0 := comm_spT0
      exp_T0 := exp_spT0
      N_eq := wrp_eq_normalizer
      card_N := card_wrp_slD
      E_cases := fun e he he3 he1 => spE_cases he he3 he1
      θ_T0 := hθT
      θ_zI := hθz
      dich := fun H hH => dich_spZ1 H hH
      N_le_M1 := wrp_mono le_top
      cent_le := fun g hg => cent_le_wrp hg
      gen := fun H hH hC => gen_wrp hH hC
      card_M1 := card_wrp_top
      card_G := by rw [hcard]; norm_num
      wit := ⟨spWit, spWit_comm, spWit_not_mem⟩
      simple := hsimple }
  exact D.lattice H hH

end CFSG.AGLEmbedding.KFactProofs.Sp48
