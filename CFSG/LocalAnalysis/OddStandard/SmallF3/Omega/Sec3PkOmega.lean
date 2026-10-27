module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2Q8Plus

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem exists_omega_involution_four_plus (hQ : Q.Nondegenerate)
    (h5 : 5 ≤ Module.finrank (ZMod 3) V) :
    ∃ z : omegaGroup hQ, (z : OGroup Q) * z = 1 ∧ invType (z : OGroup Q) = (4, 1) ∧
      0 < Module.finrank (ZMod 3) (fixSp (z : OGroup Q)) := by
  obtain ⟨t, htt, hty⟩ := (exists_involution_of_type hQ 4 1).mpr
    ⟨by omega, fun _ => rfl, fun h => absurd h (by omega)⟩
  have h1 : invDim t = 4 := by simpa only [invType, invDim] using congrArg Prod.fst hty
  have h2 : invSign t = 1 := by simpa only [invType, invSign] using congrArg Prod.snd hty
  have hmem : t ∈ omegaGroup hQ := by
    rw [involution_mem_omegaGroup_iff hQ htt, h1, h2]
    exact ⟨⟨2, rfl⟩, by decide⟩
  refine ⟨⟨t, hmem⟩, htt, hty, ?_⟩
  have h3 := finrank_fixSp_add_finrank_commSp t
  have h4 : Module.finrank (ZMod 3) (commSp t) = 4 := h1
  change 0 < Module.finrank (ZMod 3) (fixSp t)
  omega

theorem isI4PlusIn_top_omegaProj_of_fixSp (hQ : Q.Nondegenerate) {y : omegaGroup hQ}
    (hyy : (y : OGroup Q) * y = 1) (hty : invType (y : OGroup Q) = (4, 1))
    (hfix : 0 < Module.finrank (ZMod 3) (fixSp (y : OGroup Q))) :
    IsI4PlusIn (⊤ : Subgroup (omegaProj hQ)) (omegaToProj hQ y) := by
  obtain ⟨K, M, hzK, hKM, hMC, hKM', hMC', hKsl, hKπ⟩ :=
    exists_pocket_chain_of_invType hQ y hyy hty hfix
  have hy1 : (y : OGroup Q) ≠ 1 := by
    intro h
    rw [h, invType_one] at hty
    exact absurd (congrArg Prod.fst hty) (by decide)
  have hzz : orderOf y = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact Subtype.ext hyy)
      (fun h => hy1 (congrArg Subtype.val h))
  have hdis : Disjoint K (omegaToProj hQ).ker := by
    rw [Subgroup.disjoint_def]
    intro k hk hkρ
    rcases (omegaToProj_eq_one_iff hQ k).mp (MonoidHom.mem_ker.mp hkρ) with h | h
    · exact Subtype.ext h
    · exact absurd h (hKπ k hk)
  exact isI4PlusIn_map_of_chain (omegaToProj hQ) (omegaToProj_surjective hQ)
    (fun m hm g => omegaToProj_ker_central hQ (MonoidHom.mem_ker.mp hm) g) hzz hzK hKM hMC hKM'
    hMC' hKsl hdis

theorem exists_isI4PlusIn_omegaProj (hQ : Q.Nondegenerate)
    (h5 : 5 ≤ Module.finrank (ZMod 3) V) :
    ∃ q : omegaProj hQ, IsI4PlusIn (⊤ : Subgroup (omegaProj hQ)) q := by
  obtain ⟨z, hzz, hty, hfix⟩ := exists_omega_involution_four_plus hQ h5
  exact ⟨omegaToProj hQ z, isI4PlusIn_top_omegaProj_of_fixSp hQ hzz hty hfix⟩

theorem exists_isI4PlusIn_omegaGroup (hQ : Q.Nondegenerate)
    (h5 : 5 ≤ Module.finrank (ZMod 3) V) :
    ∃ q : omegaGroup hQ, IsI4PlusIn (⊤ : Subgroup (omegaGroup hQ)) q := by
  obtain ⟨z, hzz, hty, -⟩ := exists_omega_involution_four_plus hQ h5
  exact ⟨z, asc82PocketCover_holds V Q hQ z (Subtype.ext hzz) hty⟩

theorem exists_isI4PlusIn_of_isOmegaStar {X : Type} [Group X] {n : ℕ} {ε : ℤˣ}
    (hX : IsOmegaStar X n ε) (hn : 5 ≤ n) :
    ∃ q : X, IsI4PlusIn (⊤ : Subgroup X) q := by
  obtain ⟨V, i1, i2, i3, Q, hQ, hdim, -, ⟨e⟩⟩ := hX
  letI := i1
  letI := i2
  letI := i3
  obtain ⟨q, hq⟩ := exists_isI4PlusIn_omegaProj hQ (by omega)
  refine ⟨e.symm q, ?_⟩
  exact isI4PlusIn_top_map_mulEquiv e.symm hq

theorem exists_isI4PlusIn_of_isOmegaCover {X : Type} [Group X] {n : ℕ} {ε : ℤˣ}
    (hX : IsOmegaCover X n ε) (hn : 5 ≤ n) :
    ∃ q : X, IsI4PlusIn (⊤ : Subgroup X) q := by
  obtain ⟨V, i1, i2, i3, Q, hQ, hdim, -, ⟨e⟩⟩ := hX
  letI := i1
  letI := i2
  letI := i3
  obtain ⟨q, hq⟩ := exists_isI4PlusIn_omegaGroup hQ (by omega)
  refine ⟨e.symm q, ?_⟩
  exact isI4PlusIn_top_map_mulEquiv e.symm hq

end CFSG.OddStandard.SmallF3.Omega
