module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherBorelOvergroups
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSylow
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPolarRecovery

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups CFSG.LocalAnalysis.ComponentInitial
open scoped Pointwise

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

theorem flagStabilizer_singleton (h : UnitaryFieldData p f K) (d : ℕ) :
    flagStabilizer h r ε {d} = isoStabilizer h r ε (hypFlag h r ε d) := by
  ext g
  rw [mem_flagStabilizer, mem_isoStabilizer]
  exact ⟨fun hg => hg d rfl, fun hg i hi => (Set.mem_singleton_iff.mp hi) ▸ hg⟩

theorem isoStabilizer_map_conj (h : UnitaryFieldData p f K) (g : hypSU h r ε)
    (W : Submodule K (HypIndex r ε → K)) :
    (isoStabilizer h r ε W).map (MulAut.conj g).toMonoidHom = isoStabilizer h r ε (g • W) :=
  (MulAction.stabilizer_smul_eq_stabilizer_map_conj g W).symm

theorem projIsoStabilizer_map_conj (h : UnitaryFieldData p f K) (g : hypSU h r ε)
    (W : Submodule K (HypIndex r ε → K)) :
    (projIsoStabilizer h r ε W).map (MulAut.conj (hypProj h r ε g)).toMonoidHom =
      projIsoStabilizer h r ε (g • W) := by
  rw [projIsoStabilizer, projIsoStabilizer, ← isoStabilizer_map_conj, Subgroup.map_map,
    Subgroup.map_map]
  congr 1

variable (h : UnitaryFieldData p f K)

theorem hypBorel_le_isoStabilizer {d : ℕ} (hd : 1 ≤ d) (hdr : d ≤ r) :
    hypBorel h r ε ≤ isoStabilizer h r ε (hypFlag h r ε d) := by
  rw [← flagStabilizer_singleton]
  exact hypBorel_le_flagStabilizer fun i hi => (Set.mem_singleton_iff.mp hi) ▸ ⟨hd, hdr⟩

theorem isoStabilizer_hypFlag_ne_top (hε : ε ≤ 1) {d : ℕ} (hd : 1 ≤ d) (hdr : d ≤ r) :
    isoStabilizer h r ε (hypFlag h r ε d) ≠ ⊤ := by
  obtain ⟨c, hc, hc0⟩ := exists_mem_traceZero_ne_zero' h
  intro htop
  have hmem : uWeylRep ε h ⟨d - 1, by omega⟩ c hc ∈ isoStabilizer h r ε (hypFlag h r ε d) :=
    htop ▸ Subgroup.mem_top _
  exact (uWeylRep_smul_hypFlag h hε hc hc0 ⟨d - 1, by omega⟩ hdr).mp
    (mem_isoStabilizer.mp hmem) (by change d = d - 1 + 1; omega)

theorem eq_of_isoStabilizer_hypFlag_le (hr : 1 ≤ r) (hε : ε ≤ 1) {d : ℕ} (hd : 1 ≤ d)
    (hdr : d ≤ r) (A : Subgroup (hypSU h r ε))
    (hA : isoStabilizer h r ε (hypFlag h r ε d) ≤ A) :
    A = isoStabilizer h r ε (hypFlag h r ε d) ∨ A = ⊤ := by
  obtain ⟨c, hc, hc0⟩ := exists_mem_traceZero_ne_zero' h
  obtain ⟨-, hAI, -, -⟩ := unitary_Borel_overgroups h hr hε hc hc0 A
    ((hypBorel_le_isoStabilizer h hd hdr).trans hA)
  have hsub : overgroupCuts ε h c hc A ⊆ {d} := by
    rintro e ⟨k, rfl, hnot⟩
    by_contra hed
    refine hnot (hA (mem_isoStabilizer.mpr ?_))
    exact (uWeylRep_smul_hypFlag h hε hc hc0 k hdr).mpr fun e => hed (by
      rw [Set.mem_singleton_iff, e])
  rcases Set.subset_singleton_iff_eq.mp hsub with he | he
  · right
    rw [hAI, he, flagStabilizer_empty]
  · left
    rw [hAI, he, flagStabilizer_singleton]

theorem isCoatom_projIsoStabilizer_hypFlag (hr : 1 ≤ r) (hε : ε ≤ 1) {d : ℕ} (hd : 1 ≤ d)
    (hdr : d ≤ r) : IsCoatom (projIsoStabilizer h r ε (hypFlag h r ε d)) := by
  refine ⟨fun htop => isoStabilizer_hypFlag_ne_top h hε hd hdr ?_, fun M hM => ?_⟩
  · rw [← comap_projIsoStabilizer, htop, Subgroup.comap_top]
  · have hle : isoStabilizer h r ε (hypFlag h r ε d) ≤ M.comap (hypProj h r ε) := by
      rw [← comap_projIsoStabilizer]
      exact Subgroup.comap_mono hM.le
    rcases eq_of_isoStabilizer_hypFlag_le h hr hε hd hdr _ hle with he | he
    · refine absurd ?_ hM.ne'
      rw [projIsoStabilizer, ← he, Subgroup.map_comap_eq_self_of_surjective
        (hypProj_surjective h r ε)]
    · rw [← Subgroup.map_comap_eq_self_of_surjective (hypProj_surjective h r ε) M, he,
        Subgroup.map_top_of_surjective _ (hypProj_surjective h r ε)]

theorem exists_smul_hypFlag_eq (hε : ε ≤ 1) {W : Submodule K (HypIndex r ε → K)}
    (hW0 : W ≠ ⊥) (hW : ∀ x ∈ W, ∀ y ∈ W, hypForm h r ε x y = 0) :
    1 ≤ Module.finrank K W ∧ Module.finrank K W ≤ r ∧
      ∃ g : hypSU h r ε, g • hypFlag h r ε (Module.finrank K W) = W := by
  have hle := finrank_le_of_isTotIso h (hypForm_isSymm h) (hypForm_separatingLeft h) hW
  rw [Module.finrank_fintype_fun_eq_card] at hle
  simp only [Fintype.card_sum, Fintype.card_fin] at hle
  have hdr : Module.finrank K W ≤ r := by omega
  have hd1 : 1 ≤ Module.finrank K W :=
    Nat.one_le_iff_ne_zero.mpr fun h0 => hW0 (Submodule.finrank_eq_zero.mp h0)
  refine ⟨hd1, hdr, ?_⟩
  have hF := hypFlag_eq_posFlag h hε (r := r) (i := Module.finrank K W) (by omega)
  have hFiso : ∀ x ∈ hypFlag h r ε (Module.finrank K W), ∀ y ∈ hypFlag h r ε
      (Module.finrank K W), hypForm h r ε x y = 0 := by
    rw [hF]
    exact posFlag_isotropic h hdr
  have hFdim : Module.finrank K (hypFlag h r ε (Module.finrank K W)) = Module.finrank K W := by
    rw [hF, finrank_posFlag hdr]
  obtain ⟨g', hg', hgW⟩ := (isotropic_flag_extension h (hypForm_isSymm h)
    (hypForm_separatingLeft h) rfl).2.2 _ W hFiso hW hFdim
  obtain ⟨g, hg⟩ := exists_hypSU_of_mem h hg'
  exact ⟨g, by rw [hg, hgW]⟩

theorem isCoatom_projIsoStabilizer (hr : 1 ≤ r) (hε : ε ≤ 1)
    {W : Submodule K (HypIndex r ε → K)} (hW0 : W ≠ ⊥)
    (hW : ∀ x ∈ W, ∀ y ∈ W, hypForm h r ε x y = 0) :
    IsCoatom (projIsoStabilizer h r ε W) := by
  obtain ⟨hd1, hdr, g, hg⟩ := exists_smul_hypFlag_eq h hε hW0 hW
  rw [← hg, ← projIsoStabilizer_map_conj]
  exact (OrderIso.isCoatom_iff (MulEquiv.mapSubgroup (MulAut.conj (hypProj h r ε g))) _).mpr
    (isCoatom_projIsoStabilizer_hypFlag h hr hε hd1 hdr)

theorem eq_projIsoStabilizer_of_isCoatom (hr : 1 ≤ r) (hε : ε ≤ 1)
    {M : Subgroup (hypPSU h r ε)} (hM : IsCoatom M) (hBM : hypProjBorel h r ε ≤ M) :
    ∃ d, 1 ≤ d ∧ d ≤ r ∧ M = projIsoStabilizer h r ε (hypFlag h r ε d) := by
  obtain ⟨c, hc, hc0⟩ := exists_mem_traceZero_ne_zero' h
  set A := M.comap (hypProj h r ε) with hAdef
  have hBA : hypBorel h r ε ≤ A := by
    rw [hAdef, ← Subgroup.map_le_iff_le_comap]
    exact hBM
  have hMA : M = A.map (hypProj h r ε) :=
    (Subgroup.map_comap_eq_self_of_surjective (hypProj_surjective h r ε) M).symm
  obtain ⟨hsub, hAI, -, -⟩ := unitary_Borel_overgroups h hr hε hc hc0 A hBA
  obtain ⟨d, hdmem⟩ : (overgroupCuts ε h c hc A).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro he
    apply hM.1
    rw [hMA, hAI, he, flagStabilizer_empty,
      Subgroup.map_top_of_surjective _ (hypProj_surjective h r ε)]
  obtain ⟨hd, hdr⟩ := hsub hdmem
  refine ⟨d, hd, hdr, ?_⟩
  have hle : M ≤ projIsoStabilizer h r ε (hypFlag h r ε d) := by
    rw [hMA, projIsoStabilizer]
    refine Subgroup.map_mono ?_
    rw [hAI, ← flagStabilizer_singleton]
    exact fun g hg => mem_flagStabilizer.mpr fun i hi =>
      mem_flagStabilizer.mp hg i ((Set.mem_singleton_iff.mp hi) ▸ hdmem)
  rcases hM.le_iff.mp hle with he | he
  · exact absurd he (isCoatom_projIsoStabilizer_hypFlag h hr hε hd hdr).1
  · exact he.symm

theorem hypProjBorel_le_projIsoStabilizer {d : ℕ} (hd : 1 ≤ d) (hdr : d ≤ r) :
    hypProjBorel h r ε ≤ projIsoStabilizer h r ε (hypFlag h r ε d) :=
  Subgroup.map_mono (hypBorel_le_isoStabilizer h hd hdr)

theorem mem_sylowNormalizers_iff (hr : 1 ≤ r) (hε : ε ≤ 1) (B₀ : Subgroup (hypPSU h r ε)) :
    B₀ ∈ sylowNormalizers h r ε ↔ ∃ g : hypSU h r ε,
      B₀ = (hypProjBorel h r ε).map (MulAut.conj (hypProj h r ε g)).toMonoidHom := by
  obtain ⟨-, -, hsyl, -⟩ := unitary_Sylow_normalizers h hr hε
  have hchain := isIsotropicChain_hypFlag h (r := r) hε
  have hstd := flagStabP_hypFlag h hr hε
  have hgen : ∀ g : hypSU h r ε, flagStabP h r ε (fun i => g • hypFlag h r ε i) =
      (hypProjBorel h r ε).map (MulAut.conj (hypProj h r ε g)).toMonoidHom := by
    intro g
    rw [← hstd, ← flagStabP_smul]
    rfl
  rw [hsyl]
  constructor
  · rintro ⟨W, hW, rfl⟩
    obtain ⟨g, hg⟩ := hypSU_exists_smul_chain h hchain hW
    refine ⟨g, ?_⟩
    rw [← hgen]
    ext y
    rw [mem_flagStabP, mem_flagStabP]
    constructor
    · intro hy i hi
      rw [hg i hi]
      exact hy i hi
    · intro hy i hi
      rw [← hg i hi]
      exact hy i hi
  · rintro ⟨g, rfl⟩
    exact ⟨_, hchain.smul g, hgen g⟩

theorem unitary_maximal_parabolics (hr : 1 ≤ r) (hε : ε ≤ 1) :
    maximalParabolics h r ε = projIsoStabilizer h r ε ''
      {W | W ≠ ⊥ ∧ ∀ x ∈ W, ∀ y ∈ W, hypForm h r ε x y = 0} ∧
    (∀ W : Submodule K (HypIndex r ε → K), W ≠ ⊥ →
      (∀ x ∈ W, ∀ y ∈ W, hypForm h r ε x y = 0) → IsCoatom (projIsoStabilizer h r ε W)) ∧
    Set.InjOn (projIsoStabilizer h r ε)
      {W | W ≠ ⊥ ∧ ∀ x ∈ W, ∀ y ∈ W, hypForm h r ε x y = 0} := by
  refine ⟨?_, fun W hW0 hW => isCoatom_projIsoStabilizer h hr hε hW0 hW, ?_⟩
  · ext M
    constructor
    · rintro ⟨hM, B₀, hB₀, hle⟩
      obtain ⟨g, rfl⟩ := (mem_sylowNormalizers_iff h hr hε B₀).mp hB₀
      set e := MulEquiv.mapSubgroup (MulAut.conj (hypProj h r ε g)) with he
      have hM' : IsCoatom (e.symm M) := by
        rw [← OrderIso.isCoatom_iff e, OrderIso.apply_symm_apply]
        exact hM
      have hBM' : hypProjBorel h r ε ≤ e.symm M := by
        rw [← e.le_iff_le, OrderIso.apply_symm_apply]
        exact hle
      obtain ⟨d, hd, hdr, hMd⟩ := eq_projIsoStabilizer_of_isCoatom h hr hε hM' hBM'
      refine ⟨g • hypFlag h r ε d, ⟨fun h0 => ?_, smul_isotropic g ?_⟩, ?_⟩
      · have hdim := finrank_smul g (hypFlag h r ε d)
        rw [h0, finrank_bot, hypFlag_eq_posFlag h hε (by omega), finrank_posFlag hdr] at hdim
        omega
      · rw [hypFlag_eq_posFlag h hε (by omega)]
        exact posFlag_isotropic h hdr
      · rw [← projIsoStabilizer_map_conj, ← hMd]
        exact e.apply_symm_apply M
    · rintro ⟨W, ⟨hW0, hW⟩, rfl⟩
      refine ⟨isCoatom_projIsoStabilizer h hr hε hW0 hW, ?_⟩
      obtain ⟨hd1, hdr, g, hg⟩ := exists_smul_hypFlag_eq h hε hW0 hW
      refine ⟨(hypProjBorel h r ε).map (MulAut.conj (hypProj h r ε g)).toMonoidHom,
        (mem_sylowNormalizers_iff h hr hε _).mpr ⟨g, rfl⟩, ?_⟩
      rw [← hg, ← projIsoStabilizer_map_conj]
      exact Subgroup.map_mono (hypProjBorel_le_projIsoStabilizer h hd1 hdr)
  · rintro W ⟨hW0, hW⟩ W' ⟨hW0', hW'⟩ hWW'
    have hS : isoStabilizer h r ε W = isoStabilizer h r ε W' := by
      rw [← comap_projIsoStabilizer, hWW', comap_projIsoStabilizer]
    obtain ⟨hd1, hdr, g, hg⟩ := exists_smul_hypFlag_eq h hε hW0 hW
    obtain ⟨c, hc, hc0⟩ := exists_mem_traceZero_ne_zero' h
    set d := Module.finrank K W with hddef
    set X := g⁻¹ • W' with hX
    have hXW' : g • X = W' := smul_inv_smul g W'
    have hinv : ∀ k ∈ flagStabilizer h r ε {d}, k • X = X := by
      intro k hk
      rw [flagStabilizer_singleton] at hk
      have hconj : g * k * g⁻¹ ∈ isoStabilizer h r ε W' := by
        rw [← hS, ← hg, ← isoStabilizer_map_conj]
        exact ⟨k, hk, rfl⟩
      have hfix := mem_isoStabilizer.mp hconj
      calc k • X = g⁻¹ • ((g * k * g⁻¹) • W') := by
            rw [hX, smul_smul, smul_smul]
            group
        _ = X := by rw [hfix]
    have hXiso : ∀ x ∈ X, ∀ y ∈ X, hypForm h r ε x y = 0 := smul_isotropic g⁻¹ hW'
    have hX0 : X ≠ ⊥ := fun h0 => hW0' (by rw [← hXW', h0]; exact Submodule.smul_bot' g)
    have hI : ({d} : Set ℕ) ⊆ Set.Icc 1 r := fun i hi => (Set.mem_singleton_iff.mp hi) ▸
      ⟨hd1, hdr⟩
    rcases ((unitary_subflag_generation h hr hε hc hc0 hI).2.2 X).mp ⟨hXiso, hinv⟩ with
      hXb | ⟨i, hi, hXi⟩
    · rw [hypFlag_eq_posFlag h hε (Nat.zero_le _), posFlag_zero] at hXb
      exact absurd hXb hX0
    · rw [Set.mem_singleton_iff.mp hi] at hXi
      rw [← hXW', hXi, hg]

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
