module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3AutIso

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts CFSG.QuasithinUnique.Setup.X3Aut

namespace AutA6Three

@[expose] def ord3P : List (List ℕ) :=
  Core.pslLit.filter fun c => Core.cmul c (Core.cmul c c) == Core.cid && c != Core.cid

@[expose] def rCode : List ℕ := ord3P.headD Core.cid

theorem rCode_mem : rCode ∈ Core.pslLit := by decide +kernel

theorem conj_check : ord3P.all (fun a => Core.autL.any fun g =>
    Core.cmul g a == Core.cmul rCode g) = true := by
  decide +kernel

theorem aut_centralizer_check : ord3P.all (fun a =>
    ((Core.autL.filter fun c => Core.cmul a c == Core.cmul c a).dedup.length == 18)) = true := by
  decide +kernel

theorem psl_centralizer_check : ord3P.all (fun a => (Core.cpslList a).length == 9) = true := by
  decide +kernel

theorem psl_centralizer_abelian_check : ord3P.all (fun a => (Core.cpslList a).all fun b =>
    Core.cmul b (Core.cmul b b) == Core.cid &&
      (Core.cpslList a).all fun c => Core.cmul b c == Core.cmul c b) = true := by
  decide +kernel

theorem code_mem_ord3P {p : P10} (hp : p ∈ A6Models.psl29) (h3 : p * (p * p) = 1) (h1 : p ≠ 1) :
    code p ∈ ord3P := by
  unfold ord3P
  rw [List.mem_filter]
  refine ⟨(mem_psl29_iff p).1 hp, ?_⟩
  rw [← code_mul, ← code_mul, h3, code_one]
  simp only [beq_self_eq_true, Bool.true_and, bne_iff_ne, ne_eq]
  rw [← code_one]
  exact fun h => h1 (code_injective h)

theorem code_mem_ord3P_of_orderOf {x : alternatingGroup (Fin 6)} (hx : orderOf x = 3) :
    code ((psiEquiv.symm x : ↥A6Models.psl29) : P10) ∈ ord3P := by
  have h3 : x ^ 3 = 1 := hx ▸ pow_orderOf_eq_one x
  have h1 : x ≠ 1 := by
    rintro rfl
    simp at hx
  refine code_mem_ord3P (psiEquiv.symm x).2 ?_ ?_
  · have : (psiEquiv.symm x) ^ 3 = 1 := by rw [← map_pow, h3, map_one]
    rw [pow_three] at this
    exact congrArg Subtype.val this
  · intro h
    apply h1
    have : psiEquiv.symm x = 1 := Subtype.ext h
    simpa using this

noncomputable def rho : P10 := (exists_psl29_of_code rCode_mem).choose

theorem rho_code : code rho = rCode := (exists_psl29_of_code rCode_mem).choose_spec.2

theorem exists_conj_rho {w : P10} (hw : code w ∈ ord3P) :
    ∃ g : AutA6, (g : P10) * w = rho * (g : P10) := by
  obtain ⟨g0, hg0, hg⟩ := List.any_eq_true.mp (List.all_eq_true.mp conj_check _ hw)
  obtain ⟨g, rfl⟩ := exists_of_mem_autL hg0
  refine ⟨g, code_injective ?_⟩
  rw [code_mul, code_mul, rho_code]
  simpa [cd] using hg

theorem conjAut_eq_of_rho {g g' : AutA6} {w w' : ↥A6Models.psl29}
    (h : (g : P10) * (w : P10) = rho * (g : P10)) (h' : (g' : P10) * (w' : P10) = rho * (g' : P10)) :
    ((g'⁻¹ * g : AutA6) : P10) * (w : P10) * ((g'⁻¹ * g : AutA6) : P10)⁻¹ = (w' : P10) := by
  have hw : (w : P10) = (g : P10)⁻¹ * (rho * (g : P10)) := by
    rw [eq_inv_mul_iff_mul_eq]; exact h
  have hw' : (w' : P10) = (g' : P10)⁻¹ * (rho * (g' : P10)) := by
    rw [eq_inv_mul_iff_mul_eq]; exact h'
  rw [hw, hw']
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  group

end AutA6Three

open AutA6Three

theorem thetaEquiv_mk (w : ↥A6Models.psl29) :
    thetaEquiv (⟨(w : P10), psl29_le_autA6 w.2⟩ : AutA6) = MulAut.conj (psiEquiv w) :=
  thetaEquiv_psl _ w.2

theorem conj_thetaEquiv_apply (α : MulAut (alternatingGroup (Fin 6))) (x : alternatingGroup (Fin 6)) :
    α * MulAut.conj x * α⁻¹ = MulAut.conj (α x) := by
  refine MulEquiv.ext fun z => ?_
  simp [MulAut.conj_apply]

theorem exists_mulAut_apply_eq_of_orderOf_eq_three {x x' : alternatingGroup (Fin 6)}
    (hx : orderOf x = 3) (hx' : orderOf x' = 3) :
    ∃ α : MulAut (alternatingGroup (Fin 6)), α x = x' := by
  obtain ⟨g, hg⟩ := exists_conj_rho (code_mem_ord3P_of_orderOf hx)
  obtain ⟨g', hg'⟩ := exists_conj_rho (code_mem_ord3P_of_orderOf hx')
  refine ⟨thetaEquiv (g'⁻¹ * g), ?_⟩
  have h := conjAut_eq_of_rho hg hg'
  set w : ↥A6Models.psl29 := psiEquiv.symm x with hw
  set w' : ↥A6Models.psl29 := psiEquiv.symm x' with hw'
  set u : AutA6 := ⟨(w : P10), psl29_le_autA6 w.2⟩ with hu
  set u' : AutA6 := ⟨(w' : P10), psl29_le_autA6 w'.2⟩ with hu'
  have hθ : thetaEquiv u = MulAut.conj x := by
    rw [hu, thetaEquiv_mk, hw, MulEquiv.apply_symm_apply]
  have hθ' : thetaEquiv u' = MulAut.conj x' := by
    rw [hu', thetaEquiv_mk, hw', MulEquiv.apply_symm_apply]
  have hhu : (g'⁻¹ * g) * u * (g'⁻¹ * g)⁻¹ = u' := Subtype.ext h
  have h1 : thetaEquiv (g'⁻¹ * g) * MulAut.conj x * (thetaEquiv (g'⁻¹ * g))⁻¹ =
      MulAut.conj x' := by
    rw [← hθ, ← hθ', ← hhu]
    simp [map_mul, map_inv]
  rw [conj_thetaEquiv_apply] at h1
  exact CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix.inner_conjugation_injective h1

theorem card_centralizer_conj_of_orderOf_eq_three {x : alternatingGroup (Fin 6)}
    (hx : orderOf x = 3) :
    Nat.card (Subgroup.centralizer ({MulAut.conj x} :
      Set (MulAut (alternatingGroup (Fin 6))))) = 18 := by
  set w : ↥A6Models.psl29 := psiEquiv.symm x with hw
  set u : AutA6 := ⟨(w : P10), psl29_le_autA6 w.2⟩ with hu
  have hθ : thetaEquiv u = MulAut.conj x := by
    rw [hu, thetaEquiv_mk, hw, MulEquiv.apply_symm_apply]
  have hmem : cd u ∈ ord3P := code_mem_ord3P_of_orderOf hx
  have hcheck := List.all_eq_true.mp aut_centralizer_check _ hmem
  rw [beq_iff_eq] at hcheck
  set L := Core.autL.filter fun c => Core.cmul (cd u) c == Core.cmul c (cd u) with hL
  let f : ↥(Subgroup.centralizer ({MulAut.conj x} :
      Set (MulAut (alternatingGroup (Fin 6))))) → ↥L.toFinset :=
    fun g => ⟨cd (thetaEquiv.symm (g : MulAut (alternatingGroup (Fin 6)))), by
    have hg := (Subgroup.mem_centralizer_iff.mp g.2) (MulAut.conj x) (Set.mem_singleton _)
    have hc : u * thetaEquiv.symm (g : MulAut (alternatingGroup (Fin 6))) =
        thetaEquiv.symm (g : MulAut (alternatingGroup (Fin 6))) * u := by
      apply thetaEquiv.injective
      rw [map_mul, map_mul, hθ, MulEquiv.apply_symm_apply, hg]
    rw [List.mem_toFinset, hL, List.mem_filter]
    refine ⟨cd_mem_autL _, ?_⟩
    rw [← cd_mul, ← cd_mul, hc]
    simp⟩
  have hf : Function.Bijective f := by
    constructor
    · intro g g' h
      have h1 := cd_injective (congrArg Subtype.val h)
      exact Subtype.ext (thetaEquiv.symm.injective h1)
    · rintro ⟨c, hc⟩
      rw [List.mem_toFinset, hL, List.mem_filter] at hc
      obtain ⟨y, rfl⟩ := exists_of_mem_autL hc.1
      have hc2 : u * y = y * u := by
        apply cd_injective
        rw [cd_mul, cd_mul]
        simpa using hc.2
      refine ⟨⟨thetaEquiv y, ?_⟩, ?_⟩
      · rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff.mp hh, ← hθ, ← map_mul, ← map_mul, hc2]
      · apply Subtype.ext
        simp [f]
  calc Nat.card (Subgroup.centralizer ({MulAut.conj x} :
        Set (MulAut (alternatingGroup (Fin 6)))))
      = Nat.card ↥L.toFinset := Nat.card_eq_of_bijective f hf
    _ = L.toFinset.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ = L.dedup.length := List.card_toFinset L
    _ = 18 := hcheck

theorem card_centralizer_of_orderOf_eq_three {x : alternatingGroup (Fin 6)}
    (hx : orderOf x = 3) :
    Nat.card (Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 6)))) = 9 := by
  set w : ↥A6Models.psl29 := psiEquiv.symm x with hw
  have hmem := code_mem_ord3P_of_orderOf hx
  have hcheck := List.all_eq_true.mp psl_centralizer_check _ hmem
  rw [beq_iff_eq] at hcheck
  let f : ↥(Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 6)))) →
      ↥(A6Models.psl29 ⊓ Subgroup.centralizer ({(w : P10)} : Set P10)) :=
    fun g => ⟨((psiEquiv.symm (g : alternatingGroup (Fin 6)) : ↥A6Models.psl29) : P10),
      (psiEquiv.symm (g : alternatingGroup (Fin 6))).2, by
        have hg := (Subgroup.mem_centralizer_iff.mp g.2) x (Set.mem_singleton _)
        have : w * psiEquiv.symm (g : alternatingGroup (Fin 6)) =
            psiEquiv.symm (g : alternatingGroup (Fin 6)) * w := by
          rw [hw, ← map_mul, ← map_mul, hg]
        exact Subgroup.mem_centralizer_singleton_iff.2 (congrArg Subtype.val this).symm⟩
  have hf : Function.Bijective f := by
    constructor
    · intro g g' h
      have h1 := Subtype.ext_iff.mp h
      exact Subtype.ext (psiEquiv.symm.injective (Subtype.ext h1))
    · rintro ⟨p, hp1, hp2⟩
      refine ⟨⟨psiEquiv ⟨p, hp1⟩, ?_⟩, ?_⟩
      · rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff.mp hh]
        apply psiEquiv.symm.injective
        rw [map_mul, map_mul, MulEquiv.symm_apply_apply]
        apply Subtype.ext
        exact (Subgroup.mem_centralizer_singleton_iff.1 hp2).symm
      · apply Subtype.ext
        simp [f]
  rw [Nat.card_eq_of_bijective f hf, card_psl29_centralizer, hcheck]

theorem code_mem_cpslList {x : alternatingGroup (Fin 6)}
    {g : alternatingGroup (Fin 6)} (hg : g ∈ Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 6)))) :
    code ((psiEquiv.symm g : ↥A6Models.psl29) : P10) ∈
      Core.cpslList (code ((psiEquiv.symm x : ↥A6Models.psl29) : P10)) := by
  have hcomm : x * g = g * x := (Subgroup.mem_centralizer_iff.mp hg) x (Set.mem_singleton _)
  have h1 : psiEquiv.symm x * psiEquiv.symm g = psiEquiv.symm g * psiEquiv.symm x := by
    rw [← map_mul, ← map_mul, hcomm]
  have h2 := congrArg Subtype.val h1
  unfold Core.cpslList
  rw [List.mem_filter]
  refine ⟨(mem_psl29_iff _).1 (psiEquiv.symm g).2, ?_⟩
  simp only [beq_iff_eq]
  rw [← code_mul, ← code_mul]
  exact congrArg code h2.symm

theorem centralizer_commute_of_orderOf_eq_three {x : alternatingGroup (Fin 6)}
    (hx : orderOf x = 3) :
    ∀ a ∈ Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 6))),
      ∀ b ∈ Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 6))), a * b = b * a := by
  intro a ha b hb
  have h := List.all_eq_true.mp psl_centralizer_abelian_check _ (code_mem_ord3P_of_orderOf hx)
  have h1 := List.all_eq_true.mp h _ (code_mem_cpslList ha)
  rw [Bool.and_eq_true] at h1
  have h2 := List.all_eq_true.mp h1.2 _ (code_mem_cpslList hb)
  rw [beq_iff_eq, ← code_mul, ← code_mul] at h2
  have h3 := code_injective h2
  apply psiEquiv.symm.injective
  rw [map_mul, map_mul]
  exact Subtype.ext h3

theorem pow_three_of_mem_centralizer {x : alternatingGroup (Fin 6)} (hx : orderOf x = 3) :
    ∀ a ∈ Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 6))), a ^ 3 = 1 := by
  intro a ha
  have h := List.all_eq_true.mp psl_centralizer_abelian_check _ (code_mem_ord3P_of_orderOf hx)
  have h1 := List.all_eq_true.mp h _ (code_mem_cpslList ha)
  rw [Bool.and_eq_true, beq_iff_eq, ← code_mul, ← code_mul, ← code_one] at h1
  have h2 := code_injective h1.1
  apply psiEquiv.symm.injective
  rw [map_pow, map_one, pow_three]
  exact Subtype.ext h2

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus
