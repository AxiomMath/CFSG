module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911OddCyc
public import CFSG.LocalAnalysis.ComponentClassification.LiteratureLocalSmallReeOuter
public import CFSG.RankThree.Chevalley.SteinbergCFSmallReeComponentCores
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FRee

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.P911

open Subgroup CFSG CFSG.ComponentClassification CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.Burgoyne CFSG.ComponentClassification.LiteratureLocal.SmallRee
  CFSG.LieType.Ree CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Walter.Ree.Model
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped Pointwise MatrixGroups

section Ree

variable {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.G2.prime]

theorem ree_no_odd_normal (ha : 1 ≤ a) (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    ∀ s : ↥(ReeTag.G2.reeGamma K a), orderOf s = 2 →
      ∀ N : Subgroup ↥(ReeTag.G2.reeGamma K a), N ≤ centralizer ({s} : Set _) →
        (N.subgroupOf (centralizer ({s} : Set ↥(ReeTag.G2.reeGamma K a)))).Normal →
          Odd (Nat.card ↥N) → N = ⊥ := by
  classical
  intro s hs N hNs hNn hNodd
  have : Finite (ModGL ReeTag.G2.tag K) := finite_modGL
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element ReeTag.G2.tag
  have hs' : orderOf (s : ModGL ReeTag.G2.tag K) = 2 := by
    rw [Subgroup.orderOf_coe]; exact hs
  obtain ⟨g, hgΓ, hgs⟩ :=
    (small_Ree_prime_field_involution_fusion a K hK w₀ hw₀).2.2.2.2.2 (s : ModGL ReeTag.G2.tag K)
      s.2 hs'
  obtain ⟨ψ, -, -, -, -, hψ1, -, hdp, e, -⟩ :=
    small_Ree_involution_centralizer_PSL2_structure a K hK w₀ hw₀
  set t₀ := smallReeH a K (-1) with ht₀
  have ht₀2 : orderOf t₀ = 2 := by
    rw [← hgs]
    have := (MulEquiv.orderOf_eq (MulAut.conj g) (s : ModGL ReeTag.G2.tag K))
    rw [MulAut.conj_apply] at this
    rw [this, hs']
  have ht₀sq : t₀ * t₀ = 1 := by
    rw [← pow_two]; exact orderOf_dvd_iff_pow_eq_one.mp (by rw [ht₀2])
  have hZ : ∀ h ∈ Subgroup.zpowers t₀, h * h = 1 := by
    intro h hh
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    rw [← zpow_add, ← two_mul, zpow_mul, zpow_two, ht₀sq, one_zpow]
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 ≤ 3 ^ 1 + 1 := by norm_num
      _ ≤ 3 ^ (2 * a + 1) := by
        have : 3 ^ 1 ≤ 3 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        have h2 : 3 ^ 1 < 3 ^ (2 * a + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
        omega
  have hsimple : IsSimpleGroup (PSL(2, K)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hK4
  have hL : IsSimpleGroup ↥ψ.range := by
    have := hsimple
    exact e.symm.isSimpleGroup
  have hL2 : ∃ x ∈ ψ.range, orderOf x = 2 := by
    refine ⟨ψ WSL, ⟨WSL, rfl⟩, ?_⟩
    have hsq : ψ WSL * ψ WSL = 1 := by
      rw [← map_mul, WSL_mul_WSL]
      exact (hψ1 _).mpr (Or.inr rfl)
    have hne : ψ WSL ≠ 1 := by
      intro h
      rcases (hψ1 _).mp h with h | h
      · have := congrArg (fun x : SL2 K => (x : Matrix (Fin 2) (Fin 2) K) 0 0) h
        simp [WSL] at this
      · have := congrArg (fun x : SL2 K => (x : Matrix (Fin 2) (Fin 2) K) 0 0) h
        simp [WSL] at this
    exact orderOf_eq_prime (by rwa [pow_two]) hne
  set φ : ModGL ReeTag.G2.tag K →* ModGL ReeTag.G2.tag K := (MulAut.conj g).toMonoidHom
    with hφ
  have hφinj : Function.Injective φ := (MulAut.conj g).injective
  set Nm : Subgroup (ModGL ReeTag.G2.tag K) :=
    (N.map (ReeTag.G2.reeGamma K a).subtype).map φ with hNm
  have hmem : ∀ n ∈ Nm, ∃ y ∈ N, n = g * ((y : ↥(ReeTag.G2.reeGamma K a)) :
      ModGL ReeTag.G2.tag K) * g⁻¹ := by
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, by simp [hφ, MulAut.conj_apply]⟩
  have hgs' : ((s : ↥(ReeTag.G2.reeGamma K a)) : ModGL ReeTag.G2.tag K) = g⁻¹ * t₀ * g := by
    rw [← hgs]; group
  have hCdef : smallReeInvCentralizer a K =
      ReeTag.G2.reeGamma K a ⊓ Subgroup.centralizer {t₀} := rfl
  have hNmC : Nm ≤ smallReeInvCentralizer a K := by
    intro n hn
    obtain ⟨y, hy, rfl⟩ := hmem n hn
    rw [hCdef]
    refine Subgroup.mem_inf.mpr ⟨(ReeTag.G2.reeGamma K a).mul_mem
      ((ReeTag.G2.reeGamma K a).mul_mem hgΓ y.2) ((ReeTag.G2.reeGamma K a).inv_mem hgΓ), ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← hgs]
    have hys : ((y : ↥(ReeTag.G2.reeGamma K a)) : ModGL ReeTag.G2.tag K) *
        (s : ModGL ReeTag.G2.tag K) = (s : ModGL ReeTag.G2.tag K) * (y : ModGL ReeTag.G2.tag K) :=
      congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp (hNs hy))
    calc g * ↑y * g⁻¹ * (g * ↑s * g⁻¹) = g * (↑y * ↑s) * g⁻¹ := by group
      _ = g * (↑s * ↑y) * g⁻¹ := by rw [hys]
      _ = g * ↑s * g⁻¹ * (g * ↑y * g⁻¹) := by group
  have hNmn : ∀ c ∈ smallReeInvCentralizer a K, ∀ n ∈ Nm, c * n * c⁻¹ ∈ Nm := by
    intro c hc n hn
    obtain ⟨y, hy, rfl⟩ := hmem n hn
    rw [hCdef] at hc
    have hcΓ : c ∈ ReeTag.G2.reeGamma K a := (Subgroup.mem_inf.mp hc).1
    have hct : c * t₀ = t₀ * c :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hc).2
    have hdΓ : g⁻¹ * c * g ∈ ReeTag.G2.reeGamma K a :=
      (ReeTag.G2.reeGamma K a).mul_mem ((ReeTag.G2.reeGamma K a).mul_mem
        ((ReeTag.G2.reeGamma K a).inv_mem hgΓ) hcΓ) hgΓ
    have hds : (g⁻¹ * c * g) * (s : ModGL ReeTag.G2.tag K) =
        (s : ModGL ReeTag.G2.tag K) * (g⁻¹ * c * g) := by
      rw [hgs']
      calc g⁻¹ * c * g * (g⁻¹ * t₀ * g) = g⁻¹ * (c * t₀) * g := by group
        _ = g⁻¹ * (t₀ * c) * g := by rw [hct]
        _ = g⁻¹ * t₀ * g * (g⁻¹ * c * g) := by group
    let d' : ↥(centralizer ({s} : Set ↥(ReeTag.G2.reeGamma K a))) :=
      ⟨⟨g⁻¹ * c * g, hdΓ⟩, Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext hds)⟩
    have hyN : (⟨y, hNs hy⟩ : ↥(centralizer ({s} : Set ↥(ReeTag.G2.reeGamma K a)))) ∈
        N.subgroupOf (centralizer ({s} : Set ↥(ReeTag.G2.reeGamma K a))) := hy
    have h1 := hNn.conj_mem _ hyN d'
    have hdyN : (⟨g⁻¹ * c * g, hdΓ⟩ : ↥(ReeTag.G2.reeGamma K a)) * y *
        (⟨g⁻¹ * c * g, hdΓ⟩ : ↥(ReeTag.G2.reeGamma K a))⁻¹ ∈ N := h1
    refine ⟨(((⟨g⁻¹ * c * g, hdΓ⟩ : ↥(ReeTag.G2.reeGamma K a)) * y *
        (⟨g⁻¹ * c * g, hdΓ⟩ : ↥(ReeTag.G2.reeGamma K a))⁻¹ : ↥(ReeTag.G2.reeGamma K a)) :
        ModGL ReeTag.G2.tag K), ⟨_, hdyN, rfl⟩, ?_⟩
    simp only [hφ, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul,
      Subgroup.coe_inv]
    group
  have hNmcard : Nat.card Nm = Nat.card N := by
    rw [hNm, Subgroup.card_map_of_injective hφinj,
      Subgroup.card_map_of_injective (ReeTag.G2.reeGamma K a).subtype_injective]
  have hNmbot : Nm = ⊥ :=
    eq_bot_of_odd_normal_prod hdp.1 hdp.2.1 hdp.2.2 hZ hL hL2 hNmC hNmn (hNmcard ▸ hNodd)
  rw [eq_bot_iff]
  intro y hy
  have h1 : g * ((y : ↥(ReeTag.G2.reeGamma K a)) : ModGL ReeTag.G2.tag K) * g⁻¹ ∈ Nm :=
    ⟨_, ⟨y, hy, rfl⟩, by simp [hφ, MulAut.conj_apply]⟩
  rw [hNmbot, Subgroup.mem_bot] at h1
  have hy1 : ((y : ↥(ReeTag.G2.reeGamma K a)) : ModGL ReeTag.G2.tag K) = 1 := by
    have h2 := congrArg (fun x => g⁻¹ * x * g) h1
    simpa [mul_assoc] using h2
  exact Subgroup.mem_bot.mpr (Subtype.ext hy1)

theorem oddCoreCyclic_ree (ha : 1 ≤ a) (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    OddCoreCyclic ↥(ReeTag.G2.reeGamma K a) := by
  have : Finite (ModGL ReeTag.G2.tag K) := finite_modGL
  have : Finite ↥(ReeTag.G2.reeGamma K a) := inferInstance
  obtain ⟨hcyc, hcard⟩ := outer_reeGamma_cyclic ha hK
  refine oddCoreCyclic_of_outCyc (ReeTag.center_reeGamma_G2_eq_bot hK) hcyc ?_
    (ree_no_odd_normal ha hK)
  rw [hcard]
  exact odd_two_mul_add_one a

end Ree

theorem core911_ree : Core911Ree := by
  intro Y _ _ _ _ hF
  obtain ⟨f, hRee⟩ := reeTitsModel_of_FRee hF
  obtain ⟨a, K, _, _, _, ha, hK, ⟨e⟩⟩ :=
    CFSG.RankThree.Chevalley.exists_mulEquiv_reeGamma_G2_of_reeTitsModel hRee
  exact no911_of_mulEquiv e (no911_of_oddCoreCyclic (oddCoreCyclic_ree ha hK))

end CFSG.GH74.GLS.Stage2.Bender.Thm2.P911
