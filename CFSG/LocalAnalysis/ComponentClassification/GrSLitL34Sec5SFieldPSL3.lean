module

public import CFSG.GH74.GLS.IVK.Proofs2.Lemma41dL3Mat
public import CFSG.Quasithin.Vol2.KGFactL3EvenConf
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Steps

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL projUnitriangular)
open CFSG.GH74.GLS.IVK.Proofs2.Lemma41dL3 (Heis heisEquivBar)
open scoped commutatorElement Pointwise

section PSL3

variable {F : Type} [Field F] [Finite F] [CharP F 2]

omit [Finite F] in
theorem pow_four_eq_one_of_mem_projUnitriangular {a : projectiveSL 3 F}
    (ha : a ∈ projUnitriangular 3 F) : a ^ 4 = 1 := by
  have hheis : ∀ x : Heis F, x ^ 4 = 1 := by
    intro x
    have h4 : ((4 : ℕ) : F) = 0 := by
      rw [show (4 : ℕ) = 2 * 2 by norm_num, Nat.cast_mul, CharP.cast_eq_zero, zero_mul]
    have h6 : ((Nat.choose 4 2 : ℕ) : F) = 0 := by
      rw [show Nat.choose 4 2 = 2 * 3 by decide, Nat.cast_mul, CharP.cast_eq_zero, zero_mul]
    ext
    · rw [Heis.pow_a, h4, zero_mul]; rfl
    · rw [Heis.pow_b, h4, zero_mul]; rfl
    · rw [Heis.pow_c, h4, h6, zero_mul, zero_mul, add_zero]; rfl
  obtain ⟨x, hx⟩ := heisEquivBar.surjective ⟨a, ha⟩
  have h := congrArg (fun u : projUnitriangular 3 F => (u : projectiveSL 3 F))
    (congrArg (heisEquivBar (F := F)) (hheis x))
  simp only [map_pow, map_one, hx] at h
  exact h

omit [Finite F] [CharP F 2] in
theorem commutator_commutator_eq_one_of_mem_projUnitriangular {a b c : projectiveSL 3 F}
    (ha : a ∈ projUnitriangular 3 F) (hb : b ∈ projUnitriangular 3 F)
    (hc : c ∈ projUnitriangular 3 F) : ⁅⁅a, b⁆, c⁆ = 1 := by
  have hheis : ∀ x y z : Heis F, ⁅⁅x, y⁆, z⁆ = 1 := by
    intro x y z
    have hxy : ⁅x, y⁆ ∈ Subgroup.center (Heis F) := by
      rw [Heis.mem_center, Heis.commutator_eq]
      exact ⟨rfl, rfl⟩
    rw [commutatorElement_def, ← Subgroup.mem_center_iff.mp hxy z]
    group
  obtain ⟨x, hx⟩ := heisEquivBar.surjective ⟨a, ha⟩
  obtain ⟨y, hy⟩ := heisEquivBar.surjective ⟨b, hb⟩
  obtain ⟨z, hz⟩ := heisEquivBar.surjective ⟨c, hc⟩
  have h := congrArg (fun u : projUnitriangular 3 F => (u : projectiveSL 3 F))
    (congrArg (heisEquivBar (F := F)) (hheis x y z))
  simp only [map_commutatorElement, map_one, hx, hy, hz] at h
  exact h

theorem commutator_commutator_eq_one_of_isPGroup {T : Subgroup (projectiveSL 3 F)}
    (hT : IsPGroup 2 T) : ∀ a ∈ T, ∀ b ∈ T, ∀ c ∈ T, ⁅⁅a, b⁆, c⁆ = 1 := by
  obtain ⟨g, hg⟩ := Quasithin.H13.KGL3Even.exists_conj_le hT
  intro a ha b hb c hc
  have h := commutator_commutator_eq_one_of_mem_projUnitriangular (hg ⟨a, ha, rfl⟩)
    (hg ⟨b, hb, rfl⟩) (hg ⟨c, hc, rfl⟩)
  rw [← map_commutatorElement, ← map_commutatorElement] at h
  exact (map_eq_one_iff (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).mp h

theorem pow_four_eq_one_of_isPGroup {T : Subgroup (projectiveSL 3 F)} (hT : IsPGroup 2 T) :
    ∀ a ∈ T, a ^ 4 = 1 := by
  obtain ⟨g, hg⟩ := Quasithin.H13.KGL3Even.exists_conj_le hT
  intro a ha
  have h := pow_four_eq_one_of_mem_projUnitriangular (hg ⟨a, ha, rfl⟩)
  rw [← map_pow] at h
  exact (map_eq_one_iff (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).mp h

omit [Finite F] in
theorem isElemTwo_commutator_projUnitriangular :
    IsElemTwo ⁅projUnitriangular 3 F, projUnitriangular 3 F⁆ ∧
      Nat.card ↥⁅projUnitriangular 3 F, projUnitriangular 3 F⁆ = Nat.card F := by
  set f : Heis F →* projectiveSL 3 F :=
    (projUnitriangular 3 F).subtype.comp (heisEquivBar (F := F)).toMonoidHom with hf
  have hfinj : Function.Injective f :=
    (projUnitriangular 3 F).subtype_injective.comp heisEquivBar.injective
  have hrange : (⊤ : Subgroup (Heis F)).map f = projUnitriangular 3 F := by
    rw [← MonoidHom.range_eq_map]
    ext u
    constructor
    · rintro ⟨x, rfl⟩
      exact (heisEquivBar x).2
    · intro hu
      obtain ⟨x, hx⟩ := heisEquivBar.surjective ⟨u, hu⟩
      exact ⟨x, by rw [hf]; simp [hx]⟩
  have hcomm : ⁅projUnitriangular 3 F, projUnitriangular 3 F⁆ =
      (Subgroup.center (Heis F)).map f := by
    rw [← hrange, ← Subgroup.map_commutator, Heis.commutator_eq_center]
  rw [hcomm]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, -, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx y]
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul]
    have : x * x = 1 := by
      replace hx := Heis.mem_center.mp hx
      have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
      ext
      · simp [hx.1]
      · simp [hx.2]
      · simp [hx.1]
        rw [← two_mul, h2, zero_mul]
    rw [this, map_one]
  · rw [Subgroup.card_map_of_injective hfinj, Heis.card_center]

end PSL3

section PiPSL3

variable {F : Type} [Field F] [Finite F] [CharP F 2] {k : ℕ}

theorem commutator_commutator_eq_one_of_isPGroup_pi {T : Subgroup (Fin k → projectiveSL 3 F)}
    (hT : IsPGroup 2 T) : ∀ a ∈ T, ∀ b ∈ T, ∀ c ∈ T, ⁅⁅a, b⁆, c⁆ = 1 := by
  intro a ha b hb c hc
  funext i
  have hTi : IsPGroup 2 ↥(T.map (Pi.evalMonoidHom (fun _ => projectiveSL 3 F) i)) := hT.map _
  have h := commutator_commutator_eq_one_of_isPGroup hTi (a i) ⟨a, ha, rfl⟩ (b i) ⟨b, hb, rfl⟩
    (c i) ⟨c, hc, rfl⟩
  simpa [commutatorElement_def] using h

theorem pow_four_eq_one_of_isPGroup_pi {T : Subgroup (Fin k → projectiveSL 3 F)}
    (hT : IsPGroup 2 T) : ∀ a ∈ T, a ^ 4 = 1 := by
  intro a ha
  funext i
  have hTi : IsPGroup 2 ↥(T.map (Pi.evalMonoidHom (fun _ => projectiveSL 3 F) i)) := hT.map _
  simpa using pow_four_eq_one_of_isPGroup hTi (a i) ⟨a, ha, rfl⟩

theorem exists_sylow_pi_projUnitriangular :
    ∃ V : Sylow 2 (Fin k → projectiveSL 3 F), (V : Subgroup (Fin k → projectiveSL 3 F)) =
      Subgroup.pi Set.univ fun _ => projUnitriangular 3 F := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.exists_sylow_projUnitriangular
      (K := F) 2 (n := 3) (by norm_num)
  have h2 : IsPGroup 2 ↥(Subgroup.pi Set.univ fun _ : Fin k => projUnitriangular 3 F) := by
    intro g
    refine ⟨2, Subtype.ext ?_⟩
    funext i
    have h4 := pow_four_eq_one_of_mem_projUnitriangular (g.2 i (Set.mem_univ i))
    simp only [SubgroupClass.coe_pow, Pi.pow_apply, OneMemClass.coe_one, Pi.one_apply]
    norm_num
    exact h4
  have hidx : ¬ 2 ∣ (Subgroup.pi Set.univ fun _ : Fin k => projUnitriangular 3 F).index := by
    rw [Subgroup.index_pi, Prime.dvd_finset_prod_iff Nat.prime_two.prime]
    rintro ⟨i, -, hi⟩
    exact P.not_dvd_index (hP ▸ hi)
  exact ⟨h2.toSylow hidx, rfl⟩

theorem isElemTwo_commutator_sylow_pi (V : Sylow 2 (Fin k → projectiveSL 3 F)) :
    IsElemTwo ⁅(V : Subgroup (Fin k → projectiveSL 3 F)),
        (V : Subgroup (Fin k → projectiveSL 3 F))⁆ ∧
      Nat.card ↥⁅(V : Subgroup (Fin k → projectiveSL 3 F)),
        (V : Subgroup (Fin k → projectiveSL 3 F))⁆ = Nat.card F ^ k := by
  obtain ⟨U, hU⟩ := exists_sylow_pi_projUnitriangular (F := F) (k := k)
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (Fin k → projectiveSL 3 F) U V
  have hV : (V : Subgroup (Fin k → projectiveSL 3 F)) =
      (Subgroup.pi Set.univ fun _ => projUnitriangular 3 F).map (MulAut.conj c).toMonoidHom := by
    rw [← hc, Sylow.coe_subgroup_smul, hU, Subgroup.pointwise_smul_def]
    rfl
  have hD : ⁅(V : Subgroup (Fin k → projectiveSL 3 F)),
      (V : Subgroup (Fin k → projectiveSL 3 F))⁆ =
      (Subgroup.pi Set.univ fun _ => ⁅projUnitriangular 3 F, projUnitriangular 3 F⁆).map
        (MulAut.conj c).toMonoidHom := by
    rw [hV, ← Subgroup.map_commutator, Subgroup.commutator_pi_pi_of_finite]
  obtain ⟨⟨hcomm, hsq⟩, hcard⟩ := isElemTwo_commutator_projUnitriangular (F := F)
  rw [hD]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    funext i
    exact hcomm _ (hx i (Set.mem_univ i)) _ (hy i (Set.mem_univ i))
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul]
    have : x * x = 1 := by
      funext i
      exact hsq _ (hx i (Set.mem_univ i))
    rw [this, map_one]
  ·
    let e : ↥(Subgroup.pi Set.univ fun _ : Fin k =>
        ⁅projUnitriangular 3 F, projUnitriangular 3 F⁆) ≃
        (Fin k → ↥⁅projUnitriangular 3 F, projUnitriangular 3 F⁆) :=
      { toFun := fun g i => ⟨(g : Fin k → projectiveSL 3 F) i, g.2 i (Set.mem_univ i)⟩
        invFun := fun f => ⟨fun i => f i, fun i _ => (f i).2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Subgroup.card_map_of_injective (MulAut.conj c).injective, Nat.card_congr e,
      Nat.card_fun, hcard, Nat.card_fin]

end PiPSL3

end CFSG.ComponentClassification.GrSLit.L34Sec5S

end
