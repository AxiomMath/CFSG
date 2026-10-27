module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherProjective
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherSylowNormalizer

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

open Matrix Module Submodule Subgroup SymplecticFlag CFSG.Assembly.LowTwoRank

variable {r : ℕ} {K : Type} [Field K]

variable (r K) in
@[expose] def isoFlagStabilizer (F : ℕ → Submodule K (Fin r ⊕ Fin r → K)) :
    Subgroup (StatedSp r K) :=
  ⨅ i ∈ Set.Icc 1 r, stabilizer r K (F i)

variable (r K) in
@[expose] def projIsoFlagStabilizer (F : ℕ → Submodule K (Fin r ⊕ Fin r → K)) :
    Subgroup (StatedProj (StatedSp r K)) :=
  (isoFlagStabilizer r K F).map (proj r K)

theorem mem_isoFlagStabilizer {F : ℕ → Submodule K (Fin r ⊕ Fin r → K)} {g : StatedSp r K} :
    g ∈ isoFlagStabilizer r K F ↔ ∀ i, 1 ≤ i → i ≤ r → g ∈ stabilizer r K (F i) := by
  simp only [isoFlagStabilizer, Subgroup.mem_iInf, Set.mem_Icc, and_imp]

theorem isoFlagStabilizer_flag : isoFlagStabilizer r K (flag r K) = borelSubgroup r K :=
  rfl

theorem stabilizer_map_spAct (g : StatedSp r K) (W : Submodule K (Fin r ⊕ Fin r → K)) :
    stabilizer r K (W.map (spAct g)) = (stabilizer r K W).map (MulAut.conj g).toMonoidHom := by
  ext h
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, mem_stabilizer, mem_stabilizer]
  change (W.map (spAct g)).map (spAct h) = W.map (spAct g) ↔ W.map (spAct (g⁻¹ * h * g)) = W
  constructor
  · intro hh
    rw [map_spAct_mul, map_spAct_mul, hh, map_spAct_inv]
  · intro hh
    conv_lhs => rw [show h = g * (g⁻¹ * h * g) * g⁻¹ by group]
    rw [map_spAct_mul, map_spAct_mul, map_spAct_inv, hh]

theorem isoFlagStabilizer_map (g : StatedSp r K) (F : ℕ → Submodule K (Fin r ⊕ Fin r → K)) :
    isoFlagStabilizer r K (fun i => (F i).map (spAct g)) =
      (isoFlagStabilizer r K F).map (MulAut.conj g).toMonoidHom := by
  ext h
  rw [Subgroup.mem_map_equiv, mem_isoFlagStabilizer, mem_isoFlagStabilizer]
  refine forall_congr' fun i => forall_congr' fun _ => forall_congr' fun _ => ?_
  rw [stabilizer_map_spAct, Subgroup.mem_map_equiv]

theorem normalizer_unipotent :
    normalizer (unipotent r K : Set (StatedSp r K)) = borelSubgroup r K := by
  apply le_antisymm
  · intro g hg
    refine mem_borelSubgroup.mpr fun i _ hi => mem_stabilizer.mpr ?_
    have hW : IsTotallyIsotropic (pairedSympForm K r) ((flag r K i).map (spAct g)) := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [spAct, mulVecLin_apply, mulVecLin_apply, pairedSympForm_mulVec]
      exact (unitriangular_invariant_isotropic_subspaces (r := r) (K := K)).2.2.1.2.2 i hi x hx
        y hy
    have hU : ∀ u ∈ unipotent r K, ∀ v ∈ (flag r K i).map (spAct g),
        ((u : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v ∈
          (flag r K i).map (spAct g) := by
      rintro u hu _ ⟨x, hx, rfl⟩
      have hgu : g⁻¹ * u * g ∈ unipotent r K := by
        have := (mem_normalizer_iff''.mp hg u).mp hu
        simpa [mul_assoc] using this
      refine ⟨_, (unitriangular_invariant_isotropic_subspaces (r := r) (K := K)).2.2.2.1 i hi _
        hgu x hx, ?_⟩
      change spAct g (spAct (g⁻¹ * u * g) x) = spAct u (spAct g x)
      rw [← LinearMap.comp_apply, ← LinearMap.comp_apply]
      congr 1
      rw [spAct, spAct, spAct, ← mulVecLin_mul, ← mulVecLin_mul]
      congr 1
      rw [← Units.val_mul, ← Units.val_mul, ← Subgroup.coe_mul, ← Subgroup.coe_mul]
      congr 2
      group
    obtain ⟨d, hd, hdeq⟩ := ((unitriangular_invariant_isotropic_subspaces (r := r)
      (K := K)).2.1 _).mp ⟨hW, hU⟩
    have hdim : finrank K ((flag r K i).map (spAct g)) = i := by
      rw [finrank_map_spAct, finrank_flag (by omega)]
    rw [hdeq, finrank_flag (by omega)] at hdim
    rw [hdeq, hdim]
  · exact (normal_subgroupOf_iff_le_normalizer unipotent_le_borelSubgroup).mp
      unipotent_subgroupOf_borelSubgroup_normal

theorem normalizer_projUnipotent [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p] (hr : 1 ≤ r) :
    normalizer (projUnipotent r K : Set (StatedProj (StatedSp r K))) = projBorel r K := by
  classical
  have := Fintype.ofFinite K
  obtain ⟨k, hp, hk⟩ := FiniteField.card K p
  rw [← Nat.card_eq_fintype_card] at hk
  have hU : IsPGroup p (unipotent r K) :=
    IsPGroup.of_card (n := k * r ^ 2) (by rw [card_unipotent, hk, pow_mul])
  have hZ : Nat.Coprime (Nat.card (spScalars r K)) p := by
    refine Nat.Coprime.coprime_dvd_left (card_scalars_dvd hr) ?_
    rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
    intro hdvd
    have hpq : p ∣ Nat.card K := hk ▸ dvd_pow_self p k.ne_zero
    have h1 : 1 ≤ Nat.card K := Finite.card_pos
    have := Nat.dvd_sub hpq hdvd
    rw [Nat.sub_sub_self h1] at this
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  have key : ∀ h : StatedSp r K,
      proj r K h ∈ normalizer (projUnipotent r K : Set (StatedProj (StatedSp r K))) →
        ∀ u ∈ unipotent r K, h * u * h⁻¹ ∈ unipotent r K := by
    intro h hh u hu
    have h1 : proj r K (h * u * h⁻¹) ∈ projUnipotent r K := by
      rw [map_mul, map_mul, map_inv]
      exact (mem_normalizer_iff.mp hh (proj r K u)).mp (mem_map_of_mem _ hu)
    obtain ⟨u', hu', hu'eq⟩ := mem_map.mp h1
    set z := u'⁻¹ * (h * u * h⁻¹) with hz
    have hzZ : z ∈ spScalars r K := by
      rw [← ker_proj, MonoidHom.mem_ker, hz, map_mul, map_inv, hu'eq, inv_mul_cancel]
    have hzc : z ∈ center (StatedSp r K) := spScalars_le_center hzZ
    obtain ⟨a, ha⟩ := hU ⟨u, hu⟩
    obtain ⟨b, hb⟩ := hU ⟨u', hu'⟩
    have ha' : u ^ p ^ a = 1 := congrArg Subtype.val ha
    have hb' : u' ^ p ^ b = 1 := congrArg Subtype.val hb
    have hconj : h * u * h⁻¹ = u' * z := by rw [hz, mul_inv_cancel_left]
    have hzN : z ^ p ^ (a + b) = 1 := by
      have h2 : (h * u * h⁻¹) ^ p ^ (a + b) = 1 := by
        rw [conj_pow, pow_add, pow_mul, ha', one_pow, mul_one, mul_inv_cancel]
      rw [hconj, Commute.mul_pow (mem_center_iff.mp hzc u'), pow_add, mul_comm (p ^ a),
        pow_mul, hb', one_pow, one_mul, ← pow_add, add_comm] at h2
      exact h2
    have hzZcard : z ^ Nat.card (spScalars r K) = 1 :=
      congrArg Subtype.val (pow_card_eq_one' (x := (⟨z, hzZ⟩ : spScalars r K)))
    have hz1 : z = 1 := by
      have := pow_gcd_eq_one.mpr ⟨hzZcard, hzN⟩
      rwa [(hZ.pow_right (a + b)).gcd_eq_one, pow_one] at this
    rw [hconj, hz1, mul_one]
    exact hu'
  apply le_antisymm
  · intro x hx
    obtain ⟨g, rfl⟩ := proj_surjective x
    refine ⟨g, ?_, rfl⟩
    rw [SetLike.mem_coe, ← normalizer_unipotent, mem_normalizer_iff]
    intro u
    refine ⟨key g hx u, fun hu => ?_⟩
    have hx' : proj r K g⁻¹ ∈ normalizer (projUnipotent r K : Set (StatedProj (StatedSp r K))) := by
      rw [map_inv]
      exact inv_mem hx
    have := key g⁻¹ hx' _ hu
    simpa [mul_assoc] using this
  · rw [projBorel, projUnipotent, ← normalizer_unipotent]
    exact Subgroup.le_normalizer_map (proj r K)

theorem projIsoFlagStabilizer_eq_map_conj {F : ℕ → Submodule K (Fin r ⊕ Fin r → K)}
    {g : StatedSp r K} (hg : ∀ i, 1 ≤ i → i ≤ r → (flag r K i).map (spAct g) = F i) :
    projIsoFlagStabilizer r K F =
      (projBorel r K).map (MulAut.conj (proj r K g)).toMonoidHom := by
  have hF : isoFlagStabilizer r K F = isoFlagStabilizer r K fun i => (flag r K i).map (spAct g) :=
    by
    ext h
    rw [mem_isoFlagStabilizer, mem_isoFlagStabilizer]
    exact forall_congr' fun i => forall_congr' fun hi => forall_congr' fun hir => by
      rw [hg i hi hir]
  rw [projIsoFlagStabilizer, hF, isoFlagStabilizer_map, isoFlagStabilizer_flag, projBorel,
    Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem spScalars_le_isoFlagStabilizer (F : ℕ → Submodule K (Fin r ⊕ Fin r → K)) :
    spScalars r K ≤ isoFlagStabilizer r K F := fun _ hz =>
  mem_isoFlagStabilizer.mpr fun i _ _ => spScalars_le_stabilizer (F i) hz

theorem isCompleteIsotropicFlag_flag :
    IsCompleteIsotropicFlag (pairedSympForm K r) r (flag r K) :=
  (unitriangular_invariant_isotropic_subspaces (r := r) (K := K)).2.2.1

theorem exists_map_flag_eq {F : ℕ → Submodule K (Fin r ⊕ Fin r → K)}
    (hF : IsCompleteIsotropicFlag (pairedSympForm K r) r F) :
    ∃ g : StatedSp r K, ∀ i, 1 ≤ i → i ≤ r → (flag r K i).map (spAct g) = F i :=
  exists_statedSp_map_flag isCompleteIsotropicFlag_flag hF

theorem sylow_normalizers [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p] (hr : 1 ≤ r) :
    normalizer (unipotent r K : Set (StatedSp r K)) = borelSubgroup r K ∧
    normalizer (projUnipotent r K : Set (StatedProj (StatedSp r K))) = projBorel r K ∧
    LinearFlag.sylowNormalizers (StatedProj (StatedSp r K)) p =
      {B₀ | ∃ F, IsCompleteIsotropicFlag (pairedSympForm K r) r F ∧
        B₀ = projIsoFlagStabilizer r K F} ∧
    (∀ F F' : ℕ → Submodule K (Fin r ⊕ Fin r → K),
      IsCompleteIsotropicFlag (pairedSympForm K r) r F →
      IsCompleteIsotropicFlag (pairedSympForm K r) r F' →
      projIsoFlagStabilizer r K F = projIsoFlagStabilizer r K F' → ∀ i ≤ r, F i = F' i) := by
  classical
  have hNU := normalizer_projUnipotent (K := K) p hr
  have hconj : {B₀ | ∃ x : StatedProj (StatedSp r K),
        B₀ = (projBorel r K).map (MulAut.conj x).toMonoidHom} =
      {B₀ | ∃ F, IsCompleteIsotropicFlag (pairedSympForm K r) r F ∧
        B₀ = projIsoFlagStabilizer r K F} := by
    ext B₀
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨g, rfl⟩ := proj_surjective x
      refine ⟨fun i => (flag r K i).map (spAct g), ⟨fun i hi => ?_, fun i _ => map_mono
        (flag_mono (Nat.le_succ i)), fun i hi => ?_⟩,
        (projIsoFlagStabilizer_eq_map_conj fun i _ _ => rfl).symm⟩
      · rw [finrank_map_spAct, finrank_flag (by omega)]
      · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
        rw [spAct, mulVecLin_apply, mulVecLin_apply, pairedSympForm_mulVec]
        exact isCompleteIsotropicFlag_flag.2.2 i hi x hx y hy
    · rintro ⟨F, hF, rfl⟩
      obtain ⟨g, hg⟩ := exists_map_flag_eq hF
      exact ⟨proj r K g, projIsoFlagStabilizer_eq_map_conj hg⟩
  refine ⟨normalizer_unipotent, hNU, ?_, fun F F' hF hF' hFF' => ?_⟩
  ·
    rw [← hconj]
    obtain ⟨SU, hSU⟩ := exists_sylow_projUnipotent (K := K) p hr
    ext B₀
    constructor
    · rintro ⟨T, rfl⟩
      obtain ⟨x, hx⟩ := MulAction.exists_smul_eq (StatedProj (StatedSp r K)) SU T
      refine ⟨x, ?_⟩
      rw [← hx, LinearFlag.coe_sylow_smul, LinearFlag.normalizer_map_conj, hSU, hNU]
      rfl
    · rintro ⟨x, rfl⟩
      refine ⟨x • SU, ?_⟩
      rw [LinearFlag.coe_sylow_smul, LinearFlag.normalizer_map_conj, hSU, hNU]
      rfl
  ·
    have hS : isoFlagStabilizer r K F = isoFlagStabilizer r K F' := by
      have h1 := congrArg (Subgroup.comap (proj r K)) hFF'
      rwa [projIsoFlagStabilizer, projIsoFlagStabilizer,
        Subgroup.comap_map_eq_self (by rw [ker_proj]; exact spScalars_le_isoFlagStabilizer F),
        Subgroup.comap_map_eq_self (by rw [ker_proj]; exact spScalars_le_isoFlagStabilizer F')]
        at h1
    obtain ⟨g, hg⟩ := exists_map_flag_eq hF
    set W : ℕ → Submodule K (Fin r ⊕ Fin r → K) := fun i => (F' i).map (spAct g⁻¹) with hW
    have hWflag : IsCompleteIsotropicFlag (pairedSympForm K r) r W := by
      refine ⟨fun i hi => ?_, fun i hi => map_mono (hF'.2.1 i hi), fun i hi => ?_⟩
      · rw [hW, finrank_map_spAct, hF'.1 i hi]
      · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
        rw [spAct, mulVecLin_apply, mulVecLin_apply, pairedSympForm_mulVec]
        exact hF'.2.2 i hi x hx y hy
    have hWinv : ∀ i ≤ r, ∀ u ∈ unipotent r K, ∀ v ∈ W i,
        ((u : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v ∈ W i := by
      intro i hi u hu v hv
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · have : W 0 = ⊥ := by
          rw [← Submodule.finrank_eq_zero]
          exact hWflag.1 0 (Nat.zero_le _)
        rw [this, mem_bot] at hv ⊢
        rw [hv, mulVec_zero]
      have hgu : g * u * g⁻¹ ∈ isoFlagStabilizer r K F' := by
        rw [← hS, show isoFlagStabilizer r K F = (borelSubgroup r K).map
          (MulAut.conj g).toMonoidHom by
            rw [← isoFlagStabilizer_flag, ← isoFlagStabilizer_map]
            ext h
            rw [mem_isoFlagStabilizer, mem_isoFlagStabilizer]
            exact forall_congr' fun j => forall_congr' fun hj => forall_congr' fun hjr => by
              rw [hg j hj hjr]]
        exact ⟨u, unipotent_le_borelSubgroup hu, rfl⟩
      have hstab := mem_stabilizer.mp (mem_isoFlagStabilizer.mp hgu i hi0 hi)
      have hgW : (F' i).map (spAct (g⁻¹ * (g * u * g⁻¹))) = W i := by
        rw [map_spAct_mul, hstab]
      rw [← hgW, show g⁻¹ * (g * u * g⁻¹) = u * g⁻¹ by group, map_spAct_mul]
      exact ⟨v, hv, rfl⟩
    have hWF := (unitriangular_invariant_isotropic_subspaces (r := r) (K := K)).2.2.2.2 W
      hWflag hWinv
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [Submodule.finrank_eq_zero.mp (hF.1 0 (Nat.zero_le _)),
        Submodule.finrank_eq_zero.mp (hF'.1 0 (Nat.zero_le _))]
    rw [← hg i hi0 hi, ← hWF i hi, hW]
    beta_reduce
    rw [← map_spAct_mul, mul_inv_cancel, map_spAct_one]

end CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
