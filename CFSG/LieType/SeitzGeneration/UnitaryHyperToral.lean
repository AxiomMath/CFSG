module

public import CFSG.LieType.SeitzGeneration.HyperEx
public import CFSG.RankThree.PartOne.CTP.SeitzUToral

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.CTP
  CFSG.ClassicalInvolution.Phan CFSG.RankThree.PartOne.KCUnitaryModel

theorem exists_hyperplane_eq_of_hom {E : Type*} [Group E] [Finite E] {p : ℕ} (hp : p.Prime)
    (hexp : ∀ x : E, x ^ p = 1) (hcard : Nat.card E = p ^ 3) {F : Type*} [Field F]
    (χ ψ : E →* F) : ∃ H : Subgroup E, H.index = p ∧ ∀ x ∈ H, χ x = ψ x := by
  classical
  have hfp : Fact p.Prime := ⟨hp⟩
  let ρ : E →* Fˣ := χ.toHomUnits / ψ.toHomUnits
  have hρ : ∀ x, ρ x = 1 → χ x = ψ x := by
    intro x hx
    have h1 : (χ.toHomUnits x : F) = ψ.toHomUnits x := by
      have : χ.toHomUnits x / ψ.toHomUnits x = 1 := hx
      rw [div_eq_one] at this
      rw [this]
    simpa using h1
  have hrange : Nat.card ρ.range ≤ p := by
    have hle : ρ.range ≤ rootsOfUnity p F := by
      rintro _ ⟨x, rfl⟩
      rw [mem_rootsOfUnity, ← map_pow, hexp x, map_one]
    exact (Subgroup.card_le_of_le hle).trans (card_rootsOfUnity F p)
  have hidx : ρ.ker.index = Nat.card ρ.range := Subgroup.index_ker ρ
  have hdvd : ρ.ker.index ∣ p ^ 3 := hcard ▸ ρ.ker.index_dvd_card
  obtain ⟨k, hk, hkk⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  have hk1 : k ≤ 1 := by
    by_contra hk1
    have : p ^ 2 ≤ p ^ k := Nat.pow_le_pow_right hp.pos (by omega)
    have h2 : p < p ^ 2 := by nlinarith [hp.two_le]
    omega
  interval_cases k
  ·
    rw [pow_zero, Subgroup.index_eq_one] at hkk
    obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime (G := E) p (n := 2)
      (by rw [hcard]; exact pow_dvd_pow p (by norm_num))
    refine ⟨H, ?_, fun x _ => hρ x (by rw [← MonoidHom.mem_ker, hkk]; exact Subgroup.mem_top x)⟩
    have h := H.card_mul_index
    rw [hH, hcard] at h
    have : p ^ 2 * H.index = p ^ 2 * p := by rw [h]; ring
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 2) this
  · exact ⟨ρ.ker, by rw [hkk, pow_one], fun x hx => hρ x hx⟩

variable {ℓ f n p : ℕ} {K : Type} [Field K]

theorem eq_top_of_blocks_mem (h : UnitaryFieldData ℓ f K) (hq : ℓ ^ f ≠ 2)
    (P : primeFormUnitary h (idGram K (n + 1))) (S : Subgroup (unitarySU ℓ f K (n + 1)))
    (hblock : ∀ (i : Fin n) (y : unitarySU ℓ f K (n + 1)) (A : Matrix (Fin 2) (Fin 2) K),
      (((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) K) = blockMat (n + 1) i A → conjSU h P y ∈ S) :
    S = ⊤ := by
  classical
  have hfin := h.finite
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have : CharP K ℓ := h.charP
  let φ := conjSU h P
  let ε : Su K ℓ f (n + 1) ≃* unitarySU ℓ f K (n + 1) :=
    MulEquiv.subgroupCongr (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU h.card_eq_sq (n + 1))
  let ι : Fin n → (Su K ℓ f 2 →* unitarySU ℓ f K (n + 1)) := fun i =>
    ε.toMonoidHom.comp (blockEmb2 K ℓ f n i)
  have hgen : ⨆ i : Fin n, (ι i).range = ⊤ := by
    have h1 := iSup_range_blockEmb2 (K := K) (p := ℓ) (f := f) h.card_eq_sq hq n
    have h2 := congrArg (Subgroup.map ε.toMonoidHom) h1
    rw [Subgroup.map_iSup, Subgroup.map_top_of_surjective _ ε.surjective] at h2
    simpa [ι, MonoidHom.range_comp] using h2
  have hle : (⨆ i : Fin n, (ι i).range).map φ.toMonoidHom ≤ S := by
    rw [Subgroup.map_iSup]
    refine iSup_le fun i => ?_
    rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    exact hblock i _ ((a : Su K ℓ f 2) : GL (Fin 2) K) rfl
  rw [hgen, Subgroup.map_top_of_surjective _ φ.surjective] at hle
  exact top_unique hle

theorem hyperClosure_eq_top_unitarySU_toral (h : UnitaryFieldData ℓ f K) (hp : p.Prime)
    (hpq : p ∣ ℓ ^ f + 1) (hq : ℓ ^ f ≠ 2) (E : Subgroup (unitarySU ℓ f K (n + 1)))
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ p = 1)
    (hcard : Nat.card E = p ^ 3) :
    hyperClosure p ⊤ E = ⊤ := by
  classical
  have hfin := h.finite
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have : CharP K ℓ := h.charP
  have hEfin : Finite E :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 3 hp.ne_zero)
  have hle : unitarySU ℓ f K (n + 1) ≤ primeFormUnitary h (idGram K (n + 1)) :=
    unitarySU_le_primeFormUnitary h
  let G : Subgroup (primeFormUnitary h (idGram K (n + 1))) := E.map (Subgroup.inclusion hle)
  have hGcomm : ∀ u ∈ G, ∀ v ∈ G, u * v = v * u := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hcomm x hx y hy]
  have hGexp : ∀ u ∈ G, u ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hexp x hx, map_one]
  obtain ⟨P, hP⟩ := exists_unitary_conj_diag h hp hpq G hGcomm hGexp
  let Pg : GL (Fin (n + 1)) K := (P : GL (Fin (n + 1)) K)
  let Dg : E → GL (Fin (n + 1)) K := fun x =>
    Pg⁻¹ * (((x : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K)) * Pg
  have hdiag : ∀ x : E,
      ((Dg x : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K).IsDiag :=
    fun x => hP (Subgroup.inclusion hle x) ⟨x, x.2, rfl⟩
  have hDmul : ∀ x y : E, Dg (x * y) = Dg x * Dg y := by
    intro x y
    simp only [Dg, Subgroup.coe_mul]
    group
  have hD1 : Dg 1 = 1 := by simp [Dg]
  let χ : Fin (n + 1) → E →* K := fun c =>
    { toFun := fun x => ((Dg x : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) c c
      map_one' := by simp [hD1]
      map_mul' := fun x y => by
        simp only [hDmul, Units.val_mul]
        exact mul_apply_diag_of_isDiag (hdiag x) c }
  have hnz : ∀ (x : E) (c : Fin (n + 1)),
      ((Dg x : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) c c ≠ 0 := by
    intro x c
    have h1 : (((Dg x : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) *
        (((Dg x)⁻¹ : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K)) c c = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_apply_eq]
    rw [mul_apply_diag_of_isDiag (hdiag x)] at h1
    exact left_ne_zero_of_mul_eq_one h1
  have hexpE : ∀ x : E, x ^ p = 1 := fun x => Subtype.ext (by simpa using hexp x x.2)
  have hcommblock : ∀ i : Fin n, ∃ H : Subgroup E, H.index = p ∧ ∀ x ∈ H,
      ∀ A : Matrix (Fin 2) (Fin 2) K,
      blockMat (n + 1) i A * ((Dg x : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) =
        ((Dg x : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) *
          blockMat (n + 1) i A := by
    intro i
    obtain ⟨H, hH, hHeq⟩ := exists_hyperplane_eq_of_hom hp hexpE hcard (χ i.castSucc) (χ i.succ)
    refine ⟨H, hH, fun x hx A => ?_⟩
    have hD : ((Dg x : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) =
        Matrix.diagonal (fun c => ((Dg x : GL (Fin (n + 1)) K) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) K) c c) := ((hdiag x).diagonal_diag).symm
    rw [hD]
    exact blockMat_mul_diagonal_comm (by omega) _ (hnz x) i.castSucc i.succ (by simp) (by simp)
      (hHeq x hx) A
  refine eq_top_of_blocks_mem h hq P _ fun i y A hA => ?_
  obtain ⟨H, hH, hHc⟩ := hcommblock i
  refine Subgroup.subset_closure ⟨Subgroup.mem_top _, H.map E.subtype,
    Subgroup.map_subtype_le _, ?_, ?_⟩
  · have hsub : (H.map E.subtype).subgroupOf E = H :=
      Subgroup.comap_map_eq_self_of_injective E.subtype_injective H
    rw [Subgroup.relIndex, hsub]
    exact hH
  · rintro _ ⟨x, hx, rfl⟩
    apply Subtype.ext
    have hYD : ((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) * Dg x =
        Dg x * ((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) := by
      apply Units.ext
      simp only [Units.val_mul]
      rw [hA]
      exact hHc x hx A
    have hxeq : ((x : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) = Pg * Dg x * Pg⁻¹ := by
      simp [Dg, mul_assoc]
    show ((x : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) *
        (Pg * ((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) * Pg⁻¹) =
      Pg * ((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) * Pg⁻¹ *
        ((x : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K)
    rw [hxeq]
    calc Pg * Dg x * Pg⁻¹ * (Pg * ((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) * Pg⁻¹)
        = Pg * (Dg x * ((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K)) * Pg⁻¹ := by group
      _ = Pg * (((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) * Dg x) * Pg⁻¹ := by
        rw [hYD]
      _ = Pg * ((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) * Pg⁻¹ *
          (Pg * Dg x * Pg⁻¹) := by group

end CFSG.LieType.SeitzGeneration
