module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Gen2318Lift
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.AltFacts6
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256d
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256e

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256m

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Seitz2313Cover (EvenScope)
open CFSG.LieType.SeitzGeneration (Cat)

section Alt5

theorem alt5_orderThree_normalizes_four : ∀ g : alternatingGroup (Fin 5), g ^ 3 = 1 → g ≠ 1 →
    ∃ v : alternatingGroup (Fin 5), v ≠ 1 ∧ v ^ 2 = 1 ∧ v * (g * v * g⁻¹) = g * v * g⁻¹ * v ∧
      g * (g * v * g⁻¹) * g⁻¹ = v * (g * v * g⁻¹) := by
  decide +kernel

theorem exists_elemTwo_conj_stable_of_alt5 {X : Type*} [Group X] (e : X ≃* alternatingGroup (Fin 5))
    {g : X} (hg : g ^ 3 = 1) (hg1 : g ≠ 1) :
    ∃ V : Subgroup X, V ≠ ⊥ ∧ IsElemAbelian 2 V ∧ ∀ u ∈ V, g * u * g⁻¹ ∈ V := by
  have hg' : e g ^ 3 = 1 := by rw [← map_pow, hg, map_one]
  have hg1' : e g ≠ 1 := fun h => hg1 (e.injective (h.trans (map_one e).symm))
  obtain ⟨v₀, hv₀1, hv₀2, hc₀, hgw₀⟩ := alt5_orderThree_normalizes_four (e g) hg' hg1'
  have hv1 : e.symm v₀ ≠ 1 := fun h => hv₀1 (by rw [← e.apply_symm_apply v₀, h, map_one])
  have hv2 : e.symm v₀ ^ 2 = 1 := e.injective (by rw [map_pow, e.apply_symm_apply, hv₀2, map_one])
  have hvw : e.symm v₀ * (g * e.symm v₀ * g⁻¹) = g * e.symm v₀ * g⁻¹ * e.symm v₀ :=
    e.injective (by simpa only [map_mul, map_inv, e.apply_symm_apply] using hc₀)
  have hgw : g * (g * e.symm v₀ * g⁻¹) * g⁻¹ = e.symm v₀ * (g * e.symm v₀ * g⁻¹) :=
    e.injective (by simpa only [map_mul, map_inv, e.apply_symm_apply] using hgw₀)
  have hw2 : (g * e.symm v₀ * g⁻¹) ^ 2 = 1 := by rw [conj_pow, hv2, mul_one, mul_inv_cancel]
  refine ⟨Subgroup.closure {e.symm v₀, g * e.symm v₀ * g⁻¹}, ?_,
    CFSG.LieType.SeitzGeneration.isElemAbelian_closure_pair hvw hv2 hw2, ?_⟩
  · intro h
    apply hv1
    have hmem : e.symm v₀ ∈ Subgroup.closure ({e.symm v₀, g * e.symm v₀ * g⁻¹} : Set X) :=
      Subgroup.subset_closure (Set.mem_insert _ _)
    rw [h, Subgroup.mem_bot] at hmem
    exact hmem
  · intro u hu
    induction hu using Subgroup.closure_induction with
    | mem u hu =>
      rcases hu with rfl | rfl
      · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
      · rw [hgw]
        exact Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert _ _))
          (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
    | one => simp
    | mul a b _ _ ha hb =>
      have e1 : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
      rw [e1]
      exact Subgroup.mul_mem _ ha hb
    | inv a _ ha =>
      have e1 : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
      rw [e1]
      exact Subgroup.inv_mem _ ha

end Alt5

section TwoSub

theorem exists_twoSub_agrp_stable {K : Type} [Group K] [Finite K] {x : MulAut K} {L : Subgroup K}
    (hLx : ∀ l ∈ L, x l = l) (hL5 : IsAltType 5 (barOf 3 L)) {y : K} (hyL : y ∈ L) (hy : orderOf y = 3) :
    ∃ U : Subgroup K, U ≠ ⊥ ∧ IsPGroup 2 ↥U ∧ ∀ a ∈ Prop1310a5b.Agrp x y, ∀ u ∈ U, a u ∈ U := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := hL5
  set π : ↥L →* barOf 3 L := QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) with hπ
  set yL : ↥L := ⟨y, hyL⟩ with hyLdef
  have hy3 : y ^ 3 = 1 := hy ▸ pow_orderOf_eq_one y
  have hyL3 : yL ^ 3 = 1 := Subtype.ext (by simp [yL, hy3])
  have hyLord : orderOf yL = 3 := by rw [hyLdef, Subgroup.orderOf_mk]; exact hy
  have hcore3 : ∀ z : ↥L, z ∈ GLAPPrimeCore 3 ↥L → orderOf z ≠ 3 := fun z hz =>
    Prop115.orderOf_ne_of_coprime_card Nat.prime_three hz CFSG.pPrimeCore_coprime_card
  have hyb3 : π yL ^ 3 = 1 := by rw [← map_pow, hyL3, map_one]
  have hyb1 : π yL ≠ 1 := fun h => hcore3 yL ((QuotientGroup.eq_one_iff _).1 h) hyLord
  obtain ⟨V, hV0, hVel, hVg⟩ := exists_elemTwo_conj_stable_of_alt5 e hyb3 hyb1
  set P : Subgroup ↥L := V.comap π with hP
  have hVP : P.map π = V :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) V
  have h3P : ¬ 3 ∣ Nat.card P := by
    intro h3
    obtain ⟨p, hp⟩ := exists_prime_orderOf_dvd_card' 3 h3
    have hpV : π (p : ↥L) ∈ V := p.2
    have hp3 : (p : ↥L) ^ 3 = 1 := by
      have h1 := pow_orderOf_eq_one p
      rw [hp] at h1
      exact congrArg Subtype.val h1
    have h2 : π (p : ↥L) ^ 2 = 1 := hVel.2 _ hpV
    have h3' : π (p : ↥L) ^ 3 = 1 := by rw [← map_pow, hp3, map_one]
    have h1 : π (p : ↥L) = 1 := by
      calc π (p : ↥L) = π (p : ↥L) ^ 3 * (π (p : ↥L) ^ 2)⁻¹ := by group
        _ = 1 := by rw [h3', h2, inv_one, mul_one]
    exact hcore3 _ ((QuotientGroup.eq_one_iff _).1 h1) (by rw [Subgroup.orderOf_coe]; exact hp)
  have h2P : 2 ∣ Nat.card P := by
    obtain ⟨v, hvV, hv1⟩ := (Subgroup.bot_or_exists_ne_one V).resolve_left hV0
    have hv2 : orderOf v = 2 := orderOf_eq_prime (hVel.2 v hvV) hv1
    have h2V : 2 ∣ Nat.card V := by
      have h1 := orderOf_dvd_natCard (⟨v, hvV⟩ : V)
      rwa [Subgroup.orderOf_mk, hv2] at h1
    exact h2V.trans (hVP ▸ Subgroup.card_map_dvd P π)
  have hD3 : IsPGroup 3 ↥(Subgroup.zpowers yL) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hyLord, pow_one])
  have hyN : yL ∈ Subgroup.normalizer (P : Set ↥L) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    show π h ∈ V ↔ π (yL * h * yL⁻¹) ∈ V
    rw [map_mul, map_mul, map_inv]
    refine ⟨hVg _, fun h' => ?_⟩
    have h2 := hVg _ (hVg _ h')
    have hb : π yL * π yL * π yL = 1 := by rw [← hyb3, pow_three, mul_assoc]
    have e3 : π yL * (π yL * (π yL * π h * (π yL)⁻¹) * (π yL)⁻¹) * (π yL)⁻¹ = π h := by
      calc π yL * (π yL * (π yL * π h * (π yL)⁻¹) * (π yL)⁻¹) * (π yL)⁻¹
          = (π yL * π yL * π yL) * π h * (π yL * π yL * π yL)⁻¹ := by group
        _ = π h := by rw [hb, one_mul, inv_one, mul_one]
    rwa [e3] at h2
  have hDN : Subgroup.zpowers yL ≤ Subgroup.normalizer (P : Set ↥L) := Subgroup.zpowers_le.2 hyN
  obtain ⟨T, hT0, hT2, hDT⟩ := AltFacts6.exists_two_sub_normalized (p := 3) P (Subgroup.zpowers yL) hDN hD3
    h3P h2P
  have hyT : yL ∈ Subgroup.normalizer (T : Set ↥L) := hDT (Subgroup.mem_zpowers yL)
  have hUL : T.map L.subtype ≤ L := by
    rintro _ ⟨t, -, rfl⟩
    exact t.2
  have hxU : ∀ u : K, u ∈ T.map L.subtype ↔ x u ∈ T.map L.subtype := by
    intro u
    constructor
    · intro hu
      rw [hLx u (hUL hu)]
      exact hu
    · intro hu
      have h1 : x (x u) = x u := hLx _ (hUL hu)
      rwa [x.injective h1] at hu
  have hyU : ∀ u : K, u ∈ T.map L.subtype ↔ MulAut.conj y u ∈ T.map L.subtype := by
    intro u
    rw [MulAut.conj_apply]
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨yL * t * yL⁻¹, (Subgroup.mem_normalizer_iff.1 hyT t).1 ht, rfl⟩
    · rintro ⟨t, ht, htu⟩
      have htu' : (t : K) = y * u * y⁻¹ := htu
      have huL : u ∈ L := by
        have e1 : u = y⁻¹ * (t : K) * y := by rw [htu']; group
        rw [e1]
        exact L.mul_mem (L.mul_mem (L.inv_mem hyL) t.2) hyL
      refine ⟨⟨u, huL⟩, (Subgroup.mem_normalizer_iff.1 hyT ⟨u, huL⟩).2 ?_, rfl⟩
      have e1 : yL * ⟨u, huL⟩ * yL⁻¹ = t := Subtype.ext (by simp [yL, htu'])
      rw [e1]
      exact ht
  have hA : ∀ a ∈ Prop1310a5b.Agrp x y, ∀ u : K, u ∈ T.map L.subtype ↔ a u ∈ T.map L.subtype := by
    intro a ha
    refine Prop1310a5b.closure_pair_induction
      (P := fun a : MulAut K => ∀ u : K, u ∈ T.map L.subtype ↔ a u ∈ T.map L.subtype) hxU hyU
      (fun u => by simp) ?_ ?_ ha
    · intro b c hb hc u
      rw [MulAut.mul_apply]
      exact (hc u).trans (hb (c u))
    · intro b hb u
      have e1 : b (b⁻¹ u) = u := by simp
      constructor
      · intro hu
        rw [← e1] at hu
        exact (hb _).2 hu
      · intro hu
        rw [← e1]
        exact (hb _).1 hu
  refine ⟨T.map L.subtype, ?_, hT2.map _, fun a ha u hu => (hA a ha u).1 hu⟩
  intro hbot
  apply hT0
  rw [eq_bot_iff]
  intro t ht
  have hmem : (t : K) ∈ T.map L.subtype := ⟨t, ht, rfl⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact (Subgroup.mem_bot).2 (Subtype.ext hmem)

end TwoSub

section Vocab

@[expose] def Gen2313On (P : TauCeti.ValidLieTypeIndex → Prop) : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (d : TauCeti.ValidLieTypeIndex), P d →
    Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) →
    ∀ E : Subgroup (MulAut S), IsElemAbelian 3 E → Nat.card E = 9 →
      (∃ U : Subgroup S, U ≠ ⊥ ∧ IsPGroup 2 ↥U ∧ ∀ φ ∈ E, ∀ u ∈ U, φ u ∈ U) →
        (⨆ (F : Subgroup (MulAut S)) (_ : F ≤ E ∧ F.relIndex E = 3),
          CFSG.GH74.GLS.oPrimeResidualOf 2 (CFSG.LieType.Seitz.fixedPoints F)) = ⊤

theorem Gen2313On.mono {P Q : TauCeti.ValidLieTypeIndex → Prop} (h : Gen2313On P) (hQP : ∀ d, Q d → P d) :
    Gen2313On Q :=
  fun S _ _ d hd he E hE hE9 hU => h S d (hQP d hd) he E hE hE9 hU

theorem Gen2313On.or {P Q : TauCeti.ValidLieTypeIndex → Prop} (hP : Gen2313On P) (hQ : Gen2313On Q) :
    Gen2313On fun d => P d ∨ Q d := by
  intro S _ _ d hd he E hE hE9 hU
  rcases hd with hd | hd
  · exact hP S d hd he E hE hE9 hU
  · exact hQ S d hd he E hE hE9 hU

@[expose] def IsGF4Type (X : Type) [Group X] : Prop :=
  ∃ d' : TauCeti.ValidLieTypeIndex, d'.1.characteristic = 2 ∧
    (∃ k : ℕ, 1 ≤ k ∧ Inputs256c.defField d'.1 = 4 ^ k) ∧ Nonempty (X ≃* (TauCeti.CFSGIndex.lie d').Group)

@[expose] def IsGF4Comp {S : Type} [Group S] (β : MulAut S) (J : Subgroup S) : Prop :=
  CFSG.Open.IsSubnormal J (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β) ∧ CFSG.Open.IsQuasisimple ↥J ∧
    3 ∣ Nat.card (↥J ⧸ Subgroup.center ↥J) ∧
    (MovingAround.IsAltType 5 (↥J ⧸ Subgroup.center ↥J) ∨ IsGF4Type (↥J ⧸ Subgroup.center ↥J))

@[expose] def GF4CompsOn (P : TauCeti.ValidLieTypeIndex → Prop) : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (d : TauCeti.ValidLieTypeIndex), P d →
    Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) →
    ∀ β : MulAut S, orderOf β = 3 → ∀ s : S, β s = s → (∃ n : ℕ, s ^ (2 ^ n) = 1) →
      s ∈ ⨆ (J : Subgroup S) (_ : IsGF4Comp β J), J

theorem GF4CompsOn.mono {P Q : TauCeti.ValidLieTypeIndex → Prop} (h : GF4CompsOn P) (hQP : ∀ d, Q d → P d) :
    GF4CompsOn Q :=
  fun S _ _ d hd he β hβ s hs hs2 => h S d (hQP d hd) he β hβ s hs hs2

theorem GF4CompsOn.or {P Q : TauCeti.ValidLieTypeIndex → Prop} (hP : GF4CompsOn P) (hQ : GF4CompsOn Q) :
    GF4CompsOn fun d => P d ∨ Q d := by
  intro S _ _ d hd he β hβ s hs hs2
  rcases hd with hd | hd
  · exact hP S d hd he β hβ s hs hs2
  · exact hQ S d hd he β hβ s hs hs2

end Vocab

section Seitz

theorem gen2313On_evenScope :
    Gen2313On fun d => EvenScope d.1 := by
  intro S _ _ d hs he E hE hE9 hU
  refine CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.seitz2313Even_holds 3 Nat.prime_three (by norm_num)
    S d he hs E hE ?_ hU
  intro h
  rw [h, Subgroup.card_bot] at hE9
  norm_num at hE9

theorem closure_fixed_two_eq_top_of_gen2313
    {P : TauCeti.ValidLieTypeIndex → Prop} (hgen : Gen2313On P)
    {K : Type} [Group K] [Finite K] (hperf : commutator K = ⊤) (hO : GLAPPrimeCore 3 K = ⊥)
    {d : TauCeti.ValidLieTypeIndex} (hPd : P d) (θ : K ⧸ Subgroup.center K ≃* Cat d)
    {A : Subgroup (MulAut K)} (hAel : IsElemAbelian 3 A) (hA9 : Nat.card A = 9) {U : Subgroup K}
    (hU0 : U ≠ ⊥) (hU2 : IsPGroup 2 ↥U) (hUA : ∀ a ∈ A, ∀ u ∈ U, a u ∈ U) :
    Subgroup.closure {k : K | ∃ a ∈ A, a ≠ 1 ∧ a k = k ∧ ∃ n : ℕ, k ^ (2 ^ n) = 1} = ⊤ := by
  haveI : Finite (Cat d) := Finite.of_equiv _ θ.toEquiv
  set ψ : MulAut K →* MulAut (Cat d) := (MulAut.congr θ).toMonoidHom.comp (quotientCenterAut' K) with hψ
  have hψi : Function.Injective ψ :=
    (MulAut.congr θ).injective.comp (quotientCenterAut'_injective hperf)
  have hψa : ∀ (a : MulAut K) (y₀ : K), ψ a (θ (QuotientGroup.mk y₀)) = θ (QuotientGroup.mk (a y₀)) := by
    intro a y₀
    simp [hψ, MulAut.congr, quotientCenterAut']
  have hEel : IsElemAbelian 3 (A.map ψ) := CFSG.Open.IsElemAbelian.map hAel ψ
  have hEc : Nat.card (A.map ψ) = 9 := by rw [Subgroup.card_map_of_injective hψi, hA9]
  have hodd : Odd (Nat.card (Subgroup.center K)) :=
    Nat.coprime_two_right.1
      (Inputs2311c.coprime_card_center Nat.prime_three Nat.prime_two (by norm_num) hO)
  have hUS0 : (U.map (QuotientGroup.mk' (Subgroup.center K))).map θ.toMonoidHom ≠ ⊥ := by
    obtain ⟨u, huU, hu1⟩ := (Subgroup.bot_or_exists_ne_one U).resolve_left hU0
    intro hbot
    have hmem : θ (QuotientGroup.mk u) ∈
        (U.map (QuotientGroup.mk' (Subgroup.center K))).map θ.toMonoidHom :=
      ⟨QuotientGroup.mk u, ⟨u, huU, rfl⟩, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    have h1 : (u : K ⧸ Subgroup.center K) = ((1 : K) : K ⧸ Subgroup.center K) := by
      rw [QuotientGroup.mk_one]
      exact θ.injective (hmem.trans (map_one θ).symm)
    have hu2 : ∃ j : ℕ, u ^ (2 ^ j) = 1 := by
      obtain ⟨j, hj⟩ := hU2 ⟨u, huU⟩
      exact ⟨j, by simpa using congrArg Subtype.val hj⟩
    exact hu1 (CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Gen2318Lift.twoElem_unique hodd hu2
      ⟨0, by simp⟩ h1)
  have hUS2 : IsPGroup 2 ↥((U.map (QuotientGroup.mk' (Subgroup.center K))).map θ.toMonoidHom) :=
    (hU2.map _).map _
  have hUSE : ∀ φ ∈ A.map ψ, ∀ s ∈ (U.map (QuotientGroup.mk' (Subgroup.center K))).map θ.toMonoidHom,
      φ s ∈ (U.map (QuotientGroup.mk' (Subgroup.center K))).map θ.toMonoidHom := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    show ψ a (θ (QuotientGroup.mk u)) ∈ _
    rw [hψa]
    exact ⟨QuotientGroup.mk (a u), ⟨a u, hUA a ha u hu, rfl⟩, rfl⟩
  have hcl := CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Gen2318Lift.closure_fixed2_eq_top_of_seitz
    {F | F ≤ A.map ψ ∧ F.relIndex (A.map ψ) = 3} (fun F hF => hF)
    (hgen (Cat d) d hPd ⟨MulEquiv.refl _⟩ (A.map ψ) hEel hEc ⟨_, hUS0, hUS2, hUSE⟩)
  have huni : Inputs2311c.UniPlaneGen 2 (A.map ψ) := by
    unfold Inputs2311c.UniPlaneGen Inputs2311c.uniPlaneClosure
    rw [eq_top_iff, ← hcl]
    apply Subgroup.closure_mono
    rintro s ⟨⟨F, ⟨hFE, hFi⟩, hFs⟩, j, hj⟩
    have hF3 : Nat.card F = 3 := by
      have h1 := Subgroup.relIndex_mul_card F (A.map ψ)
      rw [inf_of_le_left hFE, hFi, hEc] at h1
      omega
    obtain ⟨φ, hφF, hφ1⟩ := (Subgroup.bot_or_exists_ne_one F).resolve_left (by
      intro h
      rw [h, Subgroup.card_bot] at hF3
      omega)
    exact ⟨φ, hFE hφF, hφ1, hFs φ hφF, j, hj⟩
  exact Inputs256c.closure_fixed_eq_top_of_uniPlaneGen Nat.prime_three Nat.prime_two (by norm_num) hperf hO θ
    A huni

end Seitz

section U34

theorem chev2On_u34 :
    Inputs256c.Chev2On fun d => ∃ q : TauCeti.PrimePower, d.1 = .twistedA 2 q ∧ q.card = 4 := by
  intro K _ _ hK hcore _ _ d hd2 hdq hθ x hx L hL hL5 y hyL hy
  exfalso
  obtain ⟨θ⟩ := hθ
  obtain ⟨hAel, hA9⟩ := Inputs256c.agrp_facts hx hL hL5 hyL hy
  obtain ⟨q, hdq, hq4⟩ := hdq
  obtain ⟨d1, hv⟩ := d
  simp only at hdq
  subst hdq
  have hq2 : q.p = 2 := by simpa using hd2
  have hqe : q.exponent = 2 := by
    have h1 : q.p ^ q.exponent = 2 ^ 2 := by rw [← TauCeti.PrimePower.card_def, hq4]; norm_num
    rw [hq2] at h1
    exact Nat.pow_right_injective (le_refl 2) h1
  have hm := CFSG.Models.lieModel_twistedA 2 q hv (MulEquiv.refl (Cat ⟨.twistedA 2 q, hv⟩))
  have hc : TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA 2 q, hv⟩ = 2 := by
    simp [TauCeti.ValidLieTypeIndex.characteristic, hq2]
  have hf : TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA 2 q, hv⟩ = 2 := by
    simp [TauCeti.ValidLieTypeIndex.fieldExponent, hqe]
  rw [hc, hf] at hm
  have hb : CFSG.Blueprint.LieModel (Cat ⟨.twistedA 2 q, hv⟩) .PSU 3 2 2 :=
    Or.inl ⟨by simp [CFSG.Blueprint.classicalTags], hm.2.resolve_right fun h => absurd h.1 (by norm_num)⟩
  obtain ⟨eP⟩ := CFSG.GH74.KGroups.equiv_psu3_of_lieModel_even (le_refl 2) hb
  have eS : (K ⧸ Subgroup.center K) ≃* CFSG.Open.PSU3 2 2 := θ.trans eP
  have hmodel : CFSG.Theory.Comparator.PSU3Model 2 = CFSG.Open.PSU3 2 2 := by
    simp only [CFSG.Open.PSU3, CFSG.Theory.Comparator.PSU3Model]
  have hBT := CFSG.GH74.Uniqueness.Bender.BenderType.unitary 2 le_rfl
    (eS.trans (MulEquiv.subgroupCongr hmodel.symm))
  have hO : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer (K ⧸ Subgroup.center K)) = 4 := by
    obtain ⟨Dd, -, -, hd, -, hq⟩ := hBT.outer_unitary
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup Dd
    rw [hq, hd] at h1
    norm_num at h1
    exact h1
  have hcardS : Nat.card (K ⧸ Subgroup.center K) = 62400 := by
    have h1 := CFSG.SignalizerFunctorTheorem.McBride.NearSolvable.card_psu3_mul_gcd (p := 2) (by norm_num)
    rw [Nat.card_congr eS.toEquiv]
    norm_num at h1
    exact h1
  have hψi : Function.Injective (quotientCenterAut' K) := quotientCenterAut'_injective hK.1.1
  have hinn : (Prop1310a5b.Agrp x y).map (quotientCenterAut' K) ≤
      CFSG.ComponentClassification.OuterAutomorphisms.inner (K ⧸ Subgroup.center K) := by
    rintro φ ⟨a, ha, rfl⟩
    have h3 : (quotientCenterAut' K a) ^ 3 = 1 := by rw [← map_pow, hAel.2 a ha, map_one]
    have hdvd3 : orderOf (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner
        (K ⧸ Subgroup.center K)) (quotientCenterAut' K a)) ∣ 3 :=
      orderOf_dvd_of_pow_eq_one (by rw [← map_pow, h3, map_one])
    have hdvd4 : orderOf (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner
        (K ⧸ Subgroup.center K)) (quotientCenterAut' K a)) ∣ 4 := by
      rw [← hO]
      exact orderOf_dvd_natCard _
    have h1 := Nat.eq_one_of_dvd_coprimes (by norm_num : Nat.Coprime 3 4) hdvd3 hdvd4
    exact (QuotientGroup.eq_one_iff _).1 (orderOf_eq_one_iff.1 h1)
  have h9 : 9 ∣ Nat.card (K ⧸ Subgroup.center K) := by
    have h1 : Nat.card ((Prop1310a5b.Agrp x y).map (quotientCenterAut' K)) = 9 := by
      rw [Subgroup.card_map_of_injective hψi, hA9]
    have h2 := Subgroup.card_dvd_of_le hinn
    have h3 : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.inner (K ⧸ Subgroup.center K)) ∣
        Nat.card (K ⧸ Subgroup.center K) := by
      unfold CFSG.ComponentClassification.OuterAutomorphisms.inner
      rw [MonoidHom.range_eq_map]
      exact (Subgroup.card_map_dvd _ _).trans (by rw [Subgroup.card_top])
    rw [← h1]
    exact h2.trans h3
  rw [hcardS] at h9
  norm_num at h9

end U34

section LiftGF4

theorem isCyclic_of_isPGroup_three_of_alt5 {X : Type*} [Group X] (e : X ≃* alternatingGroup (Fin 5))
    (R : Subgroup X) (hR : IsPGroup 3 ↥R) : IsCyclic ↥R := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite X := Finite.of_equiv _ e.symm.toEquiv
  obtain ⟨m, hm⟩ := hR.exists_card_eq
  have hdvd : 3 ^ m ∣ 60 := by
    rw [← hm, ← Inputs256b.card_alt5, ← Nat.card_congr e.toEquiv]
    exact Subgroup.card_subgroup_dvd_card R
  have hm1 : m ≤ 1 := by
    by_contra h
    have h9 : 3 ^ 2 ∣ 60 := (pow_dvd_pow 3 (by omega)).trans hdvd
    norm_num at h9
  interval_cases m
  · exact isCyclic_of_card_dvd_prime (p := 3) (by rw [hm]; norm_num)
  · exact isCyclic_of_card_dvd_prime (p := 3) (by rw [hm]; norm_num)

theorem isAltType_five_of_center_quot {Y : Type*} [Group Y] [Finite Y] (hperf : commutator Y = ⊤)
    (hO : GLAPPrimeCore 3 Y = ⊥) (e : (Y ⧸ Subgroup.center Y) ≃* alternatingGroup (Fin 5)) :
    MovingAround.IsAltType 5 Y := by
  have hZ := Inputs256d.center_eq_bot_of_isCyclic Nat.prime_three hperf hO
    (fun R hR => isCyclic_of_isPGroup_three_of_alt5 e R hR)
  exact ⟨((QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm))).trans e⟩

theorem exists_gf4Comp_lift
    (hpump : ∀ (J : Type) [Group J], IsGF4Type (J ⧸ Subgroup.center J) →
      ∀ (H : Type) [Group H] [Finite H], CFSG.LocalAnalysis.GLTheoremA.IsKHat H → GLAPPrimeCore 3 H = ⊥ →
        Prop1310a5b.IsPumpupOrSelf J H → Prop1310a5b.Good2319 H)
    {K : Type} [Group K] [Finite K] (a : MulAut K) {J : Subgroup (K ⧸ Subgroup.center K)}
    (hJ : IsGF4Comp (quotientCenterAut' K a) J) :
    ∃ JK : Subgroup K, (GLAPComponent 3 (Prop1310a5.fixedSub a) JK ∧ Inputs256b.Clause2W (barOf 3 JK)) ∧
      JK.map (QuotientGroup.mk' (Subgroup.center K)) = J := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hJsn, hJq, hJ3, hJt⟩ := hJ
  have hπβ : ∀ x : K, QuotientGroup.mk' (Subgroup.center K) (a x) =
      quotientCenterAut' K a (QuotientGroup.mk' (Subgroup.center K) x) := by
    intro x
    simp [quotientCenterAut']
  obtain ⟨JK, hsn, hq, hmap, ⟨e⟩⟩ := Inputs256e.exists_quasisimple_lift (QuotientGroup.mk' (Subgroup.center K))
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']) a (quotientCenterAut' K a) hπβ hJsn hJq
  have hJK3 : 3 ∣ Nat.card (↥JK ⧸ Subgroup.center ↥JK) := by
    rw [Nat.card_congr e.toEquiv]
    exact hJ3
  have hcomp : GLAPComponent 3 (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup a) JK :=
    CFSG.LocalAnalysis.GLTheoremA.S10.glaPComponent_of_quasisimple Nat.prime_three hsn hq hJK3
  obtain ⟨e'⟩ := Inputs256e.nonempty_pSimple_equiv Nat.prime_three hq hJK3
  have eP : CFSG.Yardstones.Md0ec50421ce4.PSimple 3 JK ≃* (↥J ⧸ Subgroup.center ↥J) := e'.symm.trans e
  refine ⟨JK, ⟨by rw [Inputs256b.fixedSub_eq]; exact hcomp, ?_⟩, hmap⟩
  rcases hJt with ⟨⟨e5⟩⟩ | ⟨d', hd'2, hk, ⟨f⟩⟩
  · exact Or.inl (isAltType_five_of_center_quot (Lemma1313.isQuasisimple_barOf_of_pComp hcomp).1
      (Lemma1311.glaPPrimeCore_quot_eq_bot 3 ↥JK) (eP.trans e5))
  · refine Or.inr ⟨Or.inr ⟨d', ⟨eP.trans f⟩, by rw [hd'2]; norm_num⟩, ?_⟩
    intro H _ _ hH hHc hP
    exact hpump (barOf 3 JK) ⟨d', hd'2, hk, ⟨eP.trans f⟩⟩ H hH hHc hP

theorem mem_iSup_gf4Comps_of_comps {P : TauCeti.ValidLieTypeIndex → Prop} (hC : GF4CompsOn P)
    (hpump : ∀ (J : Type) [Group J], IsGF4Type (J ⧸ Subgroup.center J) →
      ∀ (H : Type) [Group H] [Finite H], CFSG.LocalAnalysis.GLTheoremA.IsKHat H → GLAPPrimeCore 3 H = ⊥ →
        Prop1310a5b.IsPumpupOrSelf J H → Prop1310a5b.Good2319 H)
    {K : Type} [Group K] [Finite K] (hperf : commutator K = ⊤) (hO : GLAPPrimeCore 3 K = ⊥)
    {d : TauCeti.ValidLieTypeIndex} (hPd : P d)
    (hθ : Nonempty ((K ⧸ Subgroup.center K) ≃* (TauCeti.CFSGIndex.lie d).Group)) {a : MulAut K}
    (ha : orderOf a = 3) {k : K} (hak : a k = k) (hk : ∃ n : ℕ, k ^ (2 ^ n) = 1) :
    k ∈ ⨆ (J : Subgroup K)
      (_ : GLAPComponent 3 (Prop1310a5.fixedSub a) J ∧ Inputs256b.Clause2W (barOf 3 J)), J := by
  obtain ⟨n, hn⟩ := hk
  have hβ3 : orderOf (quotientCenterAut' K a) = 3 := by
    rw [orderOf_injective _ (quotientCenterAut'_injective hperf) a]
    exact ha
  have hπβ : ∀ x : K, QuotientGroup.mk' (Subgroup.center K) (a x) =
      quotientCenterAut' K a (QuotientGroup.mk' (Subgroup.center K) x) := by
    intro x
    simp [quotientCenterAut']
  have hs := hC (K ⧸ Subgroup.center K) d hPd hθ (quotientCenterAut' K a) hβ3
    (QuotientGroup.mk' (Subgroup.center K) k) (by rw [← hπβ, hak])
    ⟨n, by rw [← map_pow, hn, map_one]⟩
  have hle : (⨆ (J : Subgroup (K ⧸ Subgroup.center K)) (_ : IsGF4Comp (quotientCenterAut' K a) J), J) ≤
      (⨆ (J : Subgroup K)
        (_ : GLAPComponent 3 (Prop1310a5.fixedSub a) J ∧ Inputs256b.Clause2W (barOf 3 J)), J).map
        (QuotientGroup.mk' (Subgroup.center K)) := by
    refine iSup₂_le fun J hJ => ?_
    obtain ⟨JK, hJK, rfl⟩ := exists_gf4Comp_lift hpump a hJ
    exact Subgroup.map_mono (le_iSup₂_of_le (f := fun (J : Subgroup K)
      (_ : GLAPComponent 3 (Prop1310a5.fixedSub a) J ∧ Inputs256b.Clause2W (barOf 3 J)) => J) JK hJK le_rfl)
  obtain ⟨w, hw, hwk⟩ := hle hs
  have hz : w⁻¹ * k ∈ Subgroup.center K := by
    have h1 : (QuotientGroup.mk' (Subgroup.center K)) (w⁻¹ * k) = 1 := by
      rw [map_mul, map_inv, hwk, inv_mul_cancel]
    rwa [← QuotientGroup.ker_mk' (Subgroup.center K), MonoidHom.mem_ker]
  exact Inputs256e.mem_of_mul_central le_rfl
    (Inputs2311c.coprime_card_center Nat.prime_three Nat.prime_two (by norm_num) hO) hw hz hn

end LiftGF4

section Chev2GF4

theorem chev2On_of_gen2313_comps
    {P : TauCeti.ValidLieTypeIndex → Prop} (hG : Gen2313On fun d => d.1.characteristic = 2 ∧ P d)
    (hC : GF4CompsOn fun d => d.1.characteristic = 2 ∧ P d)
    (hpump : ∀ (J : Type) [Group J], IsGF4Type (J ⧸ Subgroup.center J) →
      ∀ (H : Type) [Group H] [Finite H], CFSG.LocalAnalysis.GLTheoremA.IsKHat H → GLAPPrimeCore 3 H = ⊥ →
        Prop1310a5b.IsPumpupOrSelf J H → Prop1310a5b.Good2319 H) :
    Inputs256c.Chev2On P := by
  intro K _ _ hK hcore _ _ d hd2 hd hθ x hx L hL hL5 y hyL hy
  obtain ⟨θ⟩ := hθ
  obtain ⟨hAel, hA9⟩ := Inputs256c.agrp_facts hx hL hL5 hyL hy
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx
    norm_num at hx
  have hLx : L ≤ CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup x := by
    rw [← Inputs256b.fixedSub_eq]
    exact hL.1
  obtain ⟨U, hU0, hU2, hUA⟩ := exists_twoSub_agrp_stable (fun l hl => hL.1 hl) hL5 hyL hy
  have htop := closure_fixed_two_eq_top_of_gen2313 hG hK.1.1 hcore ⟨hd2, hd⟩ θ hAel hA9 hU0 hU2 hUA
  obtain ⟨S, hS⟩ : ∃ S : MulAut K → Set (Subgroup K),
      S = fun a => {J | GLAPComponent 3 (Prop1310a5.fixedSub a) J ∧ Inputs256b.Clause2W (barOf 3 J)} :=
    ⟨_, rfl⟩
  have hmemS : ∀ (a : MulAut K) (J : Subgroup K),
      J ∈ S a ↔ GLAPComponent 3 (Prop1310a5.fixedSub a) J ∧ Inputs256b.Clause2W (barOf 3 J) := by
    intro a J
    rw [hS]
    rfl
  have hKs : Prop1310a5b.Kstar (Prop1310a5b.Agrp x y) S = ⊤ := by
    rw [eq_top_iff, ← htop, Subgroup.closure_le]
    rintro k ⟨a, haA, ha1, hak, n, hkn⟩
    have hk := mem_iSup_gf4Comps_of_comps hC hpump hK.1.1 hcore ⟨hd2, hd⟩ ⟨θ⟩
      (orderOf_eq_prime (hAel.2 a haA) ha1) hak ⟨n, hkn⟩
    have hle : (⨆ (J : Subgroup K)
        (_ : GLAPComponent 3 (Prop1310a5.fixedSub a) J ∧ Inputs256b.Clause2W (barOf 3 J)), J) ≤
        Prop1310a5b.Kstar (Prop1310a5b.Agrp x y) S :=
      iSup₂_le fun J hJ => Inputs256c.le_kstar (S := S) haA ha1 ((hmemS a J).2 hJ)
    exact hle hk
  refine ⟨S, fun a _ _ J hJ => ((hmemS a J).1 hJ).1, fun Y hY hLY => ?_,
    fun a _ _ J hJ => ((hmemS a J).1 hJ).2, ?_⟩
  · rw [hKs] at hY
    exact Inputs256b.not_alt5_of_subnormal_top hK.1 hcore hx1 hLx hL5 hY hLY
  · exact le_iSup₂_of_le (f := fun (J : Subgroup K) (_ : J ∈ S x) => J) L
      ((hmemS x L).2 ⟨hL, Or.inl hL5⟩) le_rfl

theorem chev2GF4_of_pump
    (hG : Gen2313On fun d => d.1.characteristic = 2 ∧ Inputs256c.defField d.1 = 4 ∧ ¬ EvenScope d.1 ∧
      ¬ ∃ q : TauCeti.PrimePower, d.1 = .twistedA 2 q)
    (hC : GF4CompsOn fun d => d.1.characteristic = 2 ∧ Inputs256c.defField d.1 = 4 ∧
      ¬ ∃ q : TauCeti.PrimePower, d.1 = .twistedA 2 q)
    (hpump : ∀ (J : Type) [Group J], IsGF4Type (J ⧸ Subgroup.center J) →
      ∀ (H : Type) [Group H] [Finite H], CFSG.LocalAnalysis.GLTheoremA.IsKHat H → GLAPPrimeCore 3 H = ⊥ →
        Prop1310a5b.IsPumpupOrSelf J H → Prop1310a5b.Good2319 H) :
    Inputs256c.Chev2GF4 := by
  have hG' : Gen2313On fun d => d.1.characteristic = 2 ∧
      (Inputs256c.defField d.1 = 4 ∧ ¬ ∃ q : TauCeti.PrimePower, d.1 = .twistedA 2 q) := by
    refine (Gen2313On.or gen2313On_evenScope hG).mono fun d hd => ?_
    by_cases hs : EvenScope d.1
    · exact Or.inl hs
    · exact Or.inr ⟨hd.1, hd.2.1, hs, hd.2.2⟩
  have hP := chev2On_of_gen2313_comps hG' hC hpump
  intro K _ _ hK hcore hnotPi hAlt d hd2 hd4 hθ x hx L hL hL5 y hyL hy
  by_cases hu : ∃ q : TauCeti.PrimePower, d.1 = .twistedA 2 q
  · obtain ⟨q, hq⟩ := hu
    have hq4 : q.card = 4 := by
      have h1 : Inputs256c.defField d.1 = 4 := hd4
      rw [hq] at h1
      exact h1
    exact chev2On_u34 K hK hcore hnotPi hAlt d hd2 ⟨q, hq, hq4⟩ hθ x hx L hL hL5 y hyL hy
  · exact hP K hK hcore hnotPi hAlt d hd2 ⟨hd4, hu⟩ hθ x hx L hL hL5 y hyL hy

end Chev2GF4

section Pumpup

open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple PSimple)
open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom)

theorem IsGF4Type.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (h : IsGF4Type Y) :
    IsGF4Type X := by
  obtain ⟨d', hd2, hk, ⟨f⟩⟩ := h
  exact ⟨d', hd2, hk, ⟨e.trans f⟩⟩

theorem good2319_of_pumpup_gf4 (hKD : CFSG.LocalAnalysis.GLTheoremA.KDChevDownQ 3 3)
    (h33 : ∀ (X : Type) [Group X], IsGF4Type X → ¬ IsChevSimple 3 X)
    (hSp : ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      ∀ s : TauCeti.SporadicName, IsSporType s S → ∀ α : MulAut S, α ^ 3 = 1 →
      ∀ I : Subgroup S, GLAPComponent 3 (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup α) I →
        ¬ IsGF4Type (PSimple 3 I))
    {J : Type} [Group J] (hJ : IsGF4Type (J ⧸ Subgroup.center J)) (H : Type) [Group H]
    [Finite H] (hH : CFSG.LocalAnalysis.GLTheoremA.IsKHat H) (hP : Prop1310a5b.IsPumpupOrSelf J H) :
    Prop1310a5b.Good2319 H := by
  obtain ⟨σ, hσ3, J₁, hJ₁, ⟨e⟩⟩ := hP
  have hq := hH.1
  haveI : IsSimpleGroup (H ⧸ Subgroup.center H) := hq.2
  have hnab := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian H hq
  have hJ₁' : GLAPComponent 3 (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup σ) J₁ := by
    rwa [Inputs256b.fixedSub_eq] at hJ₁
  obtain ⟨hI, ⟨eJ⟩⟩ := Inputs1415.center_transfer Nat.prime_three σ hJ₁'
  have eZ : PSimple 3 J₁ ≃* J ⧸ Subgroup.center J :=
    QuotientGroup.congr (Subgroup.center (barOf 3 J₁)) (Subgroup.center J) e (Subgroup.map_center_eq e)
  have hX : IsGF4Type (PSimple 3 (J₁.map (QuotientGroup.mk' (Subgroup.center H)))) :=
    hJ.of_mulEquiv (eJ.symm.trans eZ)
  obtain ⟨i, ⟨f⟩⟩ := hH.2
  cases i with
  | cyclic p hp =>
    exfalso
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    apply f.injective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  | alternating n hn => exact Or.inl ⟨n, ⟨f⟩⟩
  | lie idx =>
    by_cases h3 : idx.1.characteristic = 3
    · exfalso
      have hchev : IsChevSimple 3 (H ⧸ Subgroup.center H) := Or.inl ⟨TauCeti.CFSGIndex.lie idx, h3, ⟨f⟩⟩
      exact h33 _ hX (hKD (H ⧸ Subgroup.center H) inferInstance hnab hchev (centerQuotientHom H σ)
        (Inputs1415.centerQuotientHom_pow_eq_one hσ3) _ hI)
    · exact Or.inr (Or.inl ⟨idx.1.characteristic, h3, idx, ⟨f⟩, rfl⟩)
  | sporadic s =>
    exact absurd hX (hSp (H ⧸ Subgroup.center H) inferInstance hnab s ⟨f⟩ (centerQuotientHom H σ)
      (Inputs1415.centerQuotientHom_pow_eq_one hσ3) _ hI)

end Pumpup

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256m

end
