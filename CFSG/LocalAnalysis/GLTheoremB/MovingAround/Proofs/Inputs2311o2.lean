module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2311o
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2311o3
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2311j2
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2311k
public import CFSG.LieType.SeitzGeneration.ExcHigh.E8Levi
public import CFSG.LieType.SeitzGeneration.ExcHigh.E8Layer
public import CFSG.LieType.SeitzGeneration.ExcHigh.E8TwLayer
public import CFSG.Quasithin.Background.A3Structure36BPrime

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311o

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311c
  CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311f
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem exists_le_closure_hyperRSet_of_layer {G H : Type*} [Group G] [Group H] [Finite G]
    {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hpr : p ≠ r) {P A : Subgroup G} (π : ↥P →* H)
    (hπ : Function.Surjective π) (hcop : Nat.Coprime (Nat.card π.ker) p)
    (hcen : ∀ z : ↥P, π z = 1 → z ∈ Subgroup.center ↥P) (hQ : CFSG.Open.IsQuasisimple ↥P)
    (hAel : IsElemAbelian p A) (hAc : Nat.card A = p) (hcomm : ∀ l ∈ P, ∀ a ∈ A, l * a = a * l)
    (hdisj : Disjoint A P) {E : Subgroup H} (hEel : IsElemAbelian p E)
    (hEc : Nat.card E = p ^ 3)
    (hEgen : (⊤ : Subgroup H) ≤ Subgroup.closure (hyperRSet ⊤ E r p)) :
    ∃ V : Subgroup G, IsElemAbelian p V ∧ Nat.card V = p ^ 4 ∧
      P ≤ Subgroup.closure (hyperRSet ⊤ V r p) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Group.IsPerfect ↥P := ⟨hQ.1⟩
  obtain ⟨B, hBel, hBc, hBmap, -⟩ := ExcHigh.exists_elemAbelian_central_lift π hπ hcop hEel hEc
  have hPB : (⊤ : Subgroup ↥P) ≤ Subgroup.closure (hyperRSet ⊤ B r p) :=
    top_le_closure_hyperRSet_of_central_lift hr ((Nat.coprime_primes hp hr).2 hpr) π hπ
      (fun z hz => hcen z ((MonoidHom.mem_ker).1 hz)) (fun x hx => hBel.2 x hx)
      (by rw [hBmap]; exact hEgen)
  have hPtop : (⊤ : Subgroup ↥P).map P.subtype = P := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hP8 : P ≤ Subgroup.closure (hyperRSet P (B.map P.subtype) r p) := by
    have h1 := map_closure_hyperRSet_le P.subtype P.subtype_injective ⊤ B r p
    rw [hPtop] at h1
    calc P = (⊤ : Subgroup ↥P).map P.subtype := hPtop.symm
      _ ≤ (Subgroup.closure (hyperRSet ⊤ B r p)).map P.subtype := Subgroup.map_mono hPB
      _ ≤ _ := h1
  have hB'P : B.map P.subtype ≤ P := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hB'el : IsElemAbelian p (B.map P.subtype) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hBel P.subtype
  have hB'c : Nat.card (B.map P.subtype) = p ^ 3 := by
    rw [Subgroup.card_map_of_injective P.subtype_injective, hBc]
  have hcommAB : ∀ a ∈ A, ∀ f ∈ B.map P.subtype, a * f = f * a :=
    fun a ha f hf => (hcomm f (hB'P hf) a ha).symm
  have hdAB : Disjoint A (B.map P.subtype) := Disjoint.mono_right hB'P hdisj
  refine ⟨A ⊔ B.map P.subtype, ExcHigh.isElemAbelian_sup_of_commute hAel hB'el hcommAB, ?_,
    le_closure_hyperRSet_of_layer hp hAc hB'c hdAB hcommAB hcomm hP8⟩
  rw [ExcHigh.card_sup_eq_mul_of_commute_disjoint hcommAB hdAB, hAc, hB'c]
  ring

section Cubes


theorem exists_cube_top_le_closure_hyperRSet_E6 (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.E6 q).Valid) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ≠ q.p) (hord : orderOf ((q.card : ℕ) : ZMod p) = 3) :
    ∃ E₁ : Subgroup (Cat ⟨.E6 q, hv⟩), IsElemAbelian p E₁ ∧ Nat.card E₁ = p ^ 3 ∧
      (⊤ : Subgroup (Cat ⟨.E6 q, hv⟩)) ≤ Subgroup.closure (hyperRSet ⊤ E₁ q.p p) := by
  have h3 : UniSeitzPlanes fun d p E => Inputs2311j.TrialityPhi3Inner d p E ∧
      (fun _ => True) d.1.characteristic := by
    refine UniSeitzPlanes.mono (fun d p E hs => ?_) Inputs2311k.uniSeitzPlanes_triality_inner_phi36
    obtain ⟨⟨hin, hp5, ⟨q, hq, hdvd⟩, -⟩, -⟩ := hs
    exact ⟨hin, hp5, q, hq, Or.inl hdvd⟩
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨K, _, _, hK, hKchar, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 q hv
  obtain ⟨ψ, hinj, hcomm, hψ⟩ := CFSG.HardMathSupport.Malle.SeitzCube.exists_three_sl3_E6_signed K
  obtain ⟨hdvd, hp3⟩ :=
    CFSG.HardMathSupport.Foote.Coordinator.AnisoCube.dvd_sq_add_add_one_of_orderOf_eq_three hp hord
  have hdvdK : p ∣ Nat.card K ^ 2 + Nat.card K + 1 := by rw [hK]; exact hdvd
  obtain ⟨g, hg⟩ :=
    CFSG.HardMathSupport.Foote.Coordinator.AnisoCube.exists_sl3_orderOf (K := K) hp hp3 hdvdK
  have hordK : orderOf ((Nat.card K : ℕ) : ZMod p) = 3 := by rw [hK]; exact hord
  have hgen := Inputs2311j.top_le_closure_hyperRSet_cube_E6 (P := fun _ => True) h3 K q.p trivial
    ψ hψ hinj hcomm g hp hp5 hpq hordK hg
  set C := CFSG.HardMathSupport.Foote.Coordinator.AnisoCube.cube ψ g with hC
  have hCmap : (C.map e.symm.toMonoidHom).map e.toMonoidHom = C := by
    rw [Subgroup.map_map]
    convert Subgroup.map_id C
    ext y
    simp
  refine ⟨C.map e.symm.toMonoidHom, CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p
    (CFSG.HardMathSupport.Foote.Coordinator.AnisoCube.isElemAbelian_cube hinj hcomm hp hp3 hg) _,
    ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective e.symm.injective]
    exact CFSG.HardMathSupport.Foote.Coordinator.AnisoCube.card_cube hinj hcomm hp hp3 hg
  · refine QuasiHigh.closure_hyperRSet_of_mulEquiv e ?_
    rw [hCmap]
    exact hgen

theorem exists_cube_top_le_closure_hyperRSet_twE6_six (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ≠ q.p) (hord : orderOf ((q.card : ℕ) : ZMod p) = 6) :
    ∃ E₁ : Subgroup (Cat ⟨.twistedE6 q, hv⟩), IsElemAbelian p E₁ ∧ Nat.card E₁ = p ^ 3 ∧
      (⊤ : Subgroup (Cat ⟨.twistedE6 q, hv⟩)) ≤ Subgroup.closure (hyperRSet ⊤ E₁ q.p p) := by
  have h6 : UniSeitzPlanes fun d p E =>
      Inputs2311j.TrialityInnerAt (fun p c => p ∣ c ^ 2 - c + 1) d p E ∧
        (fun _ => True) d.1.characteristic := by
    refine UniSeitzPlanes.mono (fun d p E hs => ?_) Inputs2311k.uniSeitzPlanes_triality_inner_phi36
    obtain ⟨⟨hin, hp5, ⟨q, hq, hdvd⟩, -⟩, -⟩ := hs
    exact ⟨hin, hp5, q, hq, Or.inr hdvd⟩
  exact Inputs2311j.exists_cube_top_le_closure_hyperRSet_twE6 (P := fun _ => True) h6 q hv trivial
    hp hp5 hpq hord

end Cubes

section E8ThreeSix


theorem exists_rLayer_E8 (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E8 q).Valid)
    {p e : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) (hpq : p ≠ q.p) (he3 : e = 3 ∨ e = 6)
    (he : orderOf ((q.card : ℕ) : ZMod p) = e) :
    ∃ V P : Subgroup (Cat ⟨.E8 q, hv⟩), IsElemAbelian p V ∧ Nat.card V = p ^ 4 ∧
      CFSG.Open.IsQuasisimple ↥P ∧ ordTrialityD4 q.card ^ 2 < Nat.card ↥P ∧
      P ≤ Subgroup.closure (hyperRSet ⊤ V q.p p) := by
  obtain ⟨K8, _, _, -, -, ⟨e8⟩⟩ :=
    exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8 q hv
  have hfin8 : Finite (ModGL Tag.E8 K8) := CFSG.LieType.Chevalley.finite_modGL
  haveI : Finite (Cat ⟨.E8 q, hv⟩) := Finite.of_equiv _ e8.symm.toEquiv
  have hp3 : Nat.Coprime 3 p := (Nat.coprime_primes (by norm_num) hp).2 (by omega)
  rcases he3 with rfl | rfl
  · obtain ⟨P, A, π, hπ, hker, hcen, hQ, hAel, hAc, hcomm, hdisj⟩ :=
      ExcHigh.E8Layer.e8E6LayerInput_proved q hv p hp hp7 hpq he
    obtain ⟨E, hEel, hEc, hEgen⟩ := exists_cube_top_le_closure_hyperRSet_E6 q
      (TauCeti.LieTypeIndex.valid_E6 q) hp (by omega) hpq he
    obtain ⟨V, hVel, hVc, hPV⟩ := exists_le_closure_hyperRSet_of_layer hp q.prime_p hpq π hπ
      (Nat.Coprime.coprime_dvd_left hker hp3) hcen hQ hAel hAc hcomm hdisj hEel hEc hEgen
    exact ⟨V, P, hVel, hVc, hQ, lt_of_lt_of_le (ExcHigh.ordTrialityD4_sq_lt_cat_E6 q)
      (Nat.card_le_card_of_surjective π hπ), hPV⟩
  · obtain ⟨P, A, π, hπ, hker, hcen, hQ, hAel, hAc, hcomm, hdisj⟩ :=
      ExcHigh.E8Layer6.e8E6LayerInput6_of_twE8SCLayer ExcHigh.E8Tw.twE8SCLayer_holds q hv p hp
        hp7 hpq he
    obtain ⟨E, hEel, hEc, hEgen⟩ := exists_cube_top_le_closure_hyperRSet_twE6_six q
      (TauCeti.LieTypeIndex.valid_twistedE6 q) hp (by omega) hpq he
    obtain ⟨V, hVel, hVc, hPV⟩ := exists_le_closure_hyperRSet_of_layer hp q.prime_p hpq π hπ
      (Nat.Coprime.coprime_dvd_left hker hp3) hcen hQ hAel hAc hcomm hdisj hEel hEc hEgen
    exact ⟨V, P, hVel, hVc, hQ, lt_of_lt_of_le (ExcHigh.ordTrialityD4_sq_lt_cat_twE6 q)
      (Nat.card_le_card_of_surjective π hπ), hPV⟩

theorem exists_top_le_closure_hyperRSet_E8 (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.E8 q).Valid) {p e : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (hpq : p ≠ q.p) (he3 : e = 3 ∨ e = 6) (he : orderOf ((q.card : ℕ) : ZMod p) = e) :
    ∃ V : Subgroup (Cat ⟨.E8 q, hv⟩), IsElemAbelian p V ∧ Nat.card V = p ^ 4 ∧
      (⊤ : Subgroup (Cat ⟨.E8 q, hv⟩)) ≤ Subgroup.closure (hyperRSet ⊤ V q.p p) := by
  obtain ⟨V, P, hVel, hVc, hQ, hPc, hPV⟩ := exists_rLayer_E8 q hv hp hp7 hpq he3 he
  obtain ⟨K, _, _, hK, -, ⟨e8⟩⟩ :=
    exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8 q hv
  obtain ⟨V₁, V₂, X₁, X₂, hV₁, hV₂, hV₁c, hV₂c, hd, hcomm, hX₁V₂, hX₂V₁, hX₁, hX₂, hclose⟩ :=
    exists_rFrame_E8 q K hK hp hp7 hpq he3 he
  have hS : SylowTorus (Cat ⟨.E8 q, hv⟩) p 4 := by
    rcases he3 with rfl | rfl
    · exact ExcHigh.sylowTorus_cat_E8_three hv hp hp7 hpq he
    · exact ExcHigh.sylowTorus_cat_E8_six hv hp hp7 hpq he
  have hWc : Nat.card ↥(V₁ ⊔ V₂) = p ^ 4 := by
    rw [ExcHigh.card_sup_eq_mul_of_commute_disjoint hcomm hd, hV₁c, hV₂c]
    ring
  obtain ⟨x, hx⟩ := ExcHigh.exists_conj_of_sylowTorus_cube hp (hS.of_mulEquiv e8)
    (CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hVel e8.toMonoidHom)
    (by rw [Subgroup.card_map_of_injective e8.injective, hVc])
    (ExcHigh.isElemAbelian_sup_of_commute hV₁ hV₂ hcomm) hWc
  have hP' := map_le_closure_hyperRSet (MulAut.conj x) (map_le_closure_hyperRSet e8 hPV)
  rw [← hx] at hP'
  have hQ' : CFSG.Open.IsQuasisimple ↥((P.map e8.toMonoidHom).map (MulAut.conj x).toMonoidHom) :=
    ExcHigh.quasisimple_of_mulEquiv_levi ((P.equivMapOfInjective e8.toMonoidHom e8.injective).trans
      ((P.map e8.toMonoidHom).equivMapOfInjective (MulAut.conj x).toMonoidHom
        (MulEquiv.injective (MulAut.conj x)))) hQ
  have hPc' : ordTrialityD4 q.card ^ 2 <
      Nat.card ↥((P.map e8.toMonoidHom).map (MulAut.conj x).toMonoidHom) := by
    rwa [Subgroup.card_map_of_injective (MulEquiv.injective (MulAut.conj x)),
      Subgroup.card_map_of_injective e8.injective]
  have htop := top_le_closure_hyperRSet_of_frame_layer hp hV₁ hV₂ hV₁c hV₂c hd hcomm hX₁V₂ hX₂V₁
    hX₁ hX₂ hclose hQ' hPc' hP'
  rw [hx] at htop
  exact ⟨V, hVel, hVc, QuasiHigh.closure_hyperRSet_of_mulEquiv e8
    (QuasiHigh.closure_hyperRSet_of_mulEquiv (MulAut.conj x) htop)⟩

theorem uniSeitzPlanes_E8ThreeSix_inner :
    UniSeitzPlanes fun d p E => InnerPlane d p E ∧ 7 ≤ p ∧
      ∃ q : TauCeti.PrimePower, d.1 = .E8 q ∧
        (orderOf ((q.card : ℕ) : ZMod p) = 3 ∨ orderOf ((q.card : ℕ) : ZMod p) = 6) := by
  rintro ⟨d, hv⟩ p hp - hpd - E hE hc ⟨hin, hp7, q, hq, hord⟩
  obtain rfl : d = .E8 q := hq
  have hchar : (TauCeti.LieTypeIndex.E8 q).characteristic = q.p :=
    TauCeti.LieTypeIndex.characteristic_E8 q
  have hpq : p ≠ q.p := fun h => hpd (by rw [hchar]; exact h)
  have hS : SylowTorus (Cat ⟨.E8 q, hv⟩) p 4 := by
    rcases hord with h | h
    · exact ExcHigh.sylowTorus_cat_E8_three hv hp hp7 hpq h
    · exact ExcHigh.sylowTorus_cat_E8_six hv hp hp7 hpq h
  obtain ⟨V, hVel, hVc, hgen⟩ := exists_top_le_closure_hyperRSet_E8 q hv hp hp7 hpq hord rfl
  rw [← hchar] at hgen
  exact Inputs2311j.uniPlaneGen_of_sylowTorus_rgen hp
    (CFSG.LieType.SeitzGeneration.conj_injective_cat_E8 q hv) hS hVel hVc hgen hE hc hin

theorem uniSeitzPlanes_E8ThreeSix_inner_odd :
    Inputs2311c.UniSeitzPlanes fun d p E => OddCpfRest d p E ∧ InnerPlane d p E ∧ 7 ≤ p ∧
      ∃ q : TauCeti.PrimePower, d.1 = .E8 q ∧
        (orderOf ((q.card : ℕ) : ZMod p) = 3 ∨ orderOf ((q.card : ℕ) : ZMod p) = 6) :=
  UniSeitzPlanes.mono (fun _ _ _ hs => hs.2) uniSeitzPlanes_E8ThreeSix_inner

theorem uniSeitzPlanes_E8ThreeSix_inner_even :
    Inputs2311c.UniSeitzPlanes fun d p E => d.1.characteristic = 2 ∧ 5 ≤ p ∧
      CentralPrimeFree p d.1 ∧ InnerPlane d p E ∧ ¬ NormalizesRSubgroup d E ∧
      ∃ q : TauCeti.PrimePower, d.1 = .E8 q ∧
        (orderOf ((q.card : ℕ) : ZMod p) = 3 ∨ orderOf ((q.card : ℕ) : ZMod p) = 6) := by
  rintro d p hp hp2 hpd hex E hE hc ⟨-, hp5, -, hin, -, q, hq, hord⟩
  refine uniSeitzPlanes_E8ThreeSix_inner d p hp hp2 hpd hex E hE hc ⟨hin, ?_, q, hq, hord⟩
  rcases hord with h | h
  · exact ExcHigh.seven_le_of_orderOf_three hp hp5 h
  · exact ExcHigh.seven_le_of_orderOf_six hp h

end E8ThreeSix

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311o
