module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256c
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2311c2

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256c

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)
open CFSG.LieType.SeitzGeneration (Cat CentralPrimeFree InnerPlane IsLinearIndex NormalizesRSubgroup
  IsChevalleyExcIndex)

section Agrp

variable {K : Type} [Group K] [Finite K]

theorem exists_not_commute {L : Subgroup K} (hL5 : IsAltType 5 (barOf 3 L)) {y : K} (hyL : y ∈ L)
    (hy : orderOf y = 3) : ∃ l ∈ L, l * y ≠ y * l := by
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  have hLy : L ≤ Subgroup.centralizer ({y} : Set K) := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.2 (h l hl)
  exact not_mem_zpowers_of_mem_comp hLy hL5 hyL hy (Subgroup.mem_zpowers y)

theorem isElemAbelian_closure_pair_three {G : Type*} [Group G] {a b : G} (ha : a ^ 3 = 1) (hb : b ^ 3 = 1)
    (hab : Commute a b) : IsElemAbelian 3 (Subgroup.closure ({a, b} : Set G)) := by
  have hc : ∀ u ∈ ({a, b} : Set G), ∀ v ∈ ({a, b} : Set G), Commute u v := by
    intro u hu v hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact Commute.refl _
    · exact hab
    · exact hab.symm
    · exact Commute.refl _
  have hcomm : IsMulCommutative (Subgroup.closure ({a, b} : Set G)) :=
    Subgroup.isMulCommutative_closure fun u hu v hv _ => hc u hu v hv
  refine ⟨hcomm, fun z hz => ?_⟩
  induction hz using Subgroup.closure_induction with
  | mem u hu =>
    rcases hu with rfl | rfl
    · exact ha
    · exact hb
  | one => exact one_pow 3
  | mul u v hu hv ihu ihv =>
    have huv : Commute u v := congrArg Subtype.val (hcomm.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
    rw [huv.mul_pow, ihu, ihv, one_mul]
  | inv u hu ihu => rw [inv_pow, ihu, inv_one]

theorem agrp_facts {x : MulAut K} (hx : orderOf x = 3) {L : Subgroup K}
    (hL : GLAPComponent 3 (Prop1310a5.fixedSub x) L) (hL5 : IsAltType 5 (barOf 3 L)) {y : K} (hyL : y ∈ L)
    (hy : orderOf y = 3) :
    IsElemAbelian 3 (Prop1310a5b.Agrp x y) ∧ Nat.card (Prop1310a5b.Agrp x y) = 9 := by
  have hLx : ∀ l ∈ L, x l = l := fun l hl => hL.1 hl
  have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hy3 : y ^ 3 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
  have hc3 : (MulAut.conj y) ^ 3 = 1 := by rw [← map_pow, hy3, map_one]
  have hxc : Commute x (MulAut.conj y) := by
    show x * MulAut.conj y = MulAut.conj y * x
    ext k
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, hLx y hyL]
  obtain ⟨l, hlL, hly⟩ := exists_not_commute hL5 hyL hy
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx
    omega
  have hcz : MulAut.conj y ∉ Subgroup.zpowers x := by
    intro hm
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hm
    have hstab : x ^ k ∈ MulAction.stabilizer (MulAut K) l :=
      Subgroup.zpow_mem _ (by rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]; exact hLx l hlL) k
    rw [hk, MulAction.mem_stabilizer_iff, MulAut.smul_def, MulAut.conj_apply] at hstab
    apply hly
    calc l * y = y * l * y⁻¹ * y := by rw [hstab]
      _ = y * l := by group
  exact ⟨isElemAbelian_closure_pair_three hx3 hc3 hxc,
    CFSG.RankThree.Asc83Table.card_closure_pair_eq_nine hx3 hc3 hxc hx1 hcz⟩

end Agrp

section Lift

open Inputs2311c

theorem closure_fixed_eq_top_of_uniPlaneGen {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hqp : q ≠ p)
    {K : Type} [Group K] [Finite K] (hperf : commutator K = ⊤) (hO : GLAPPrimeCore p K = ⊥)
    {d : TauCeti.ValidLieTypeIndex} (θ : K ⧸ Subgroup.center K ≃* Cat d) (A : Subgroup (MulAut K))
    (hgen : UniPlaneGen q (A.map ((MulAut.congr θ).toMonoidHom.comp (quotientCenterAut' K)))) :
    Subgroup.closure {k : K | ∃ a ∈ A, a ≠ 1 ∧ a k = k ∧ ∃ n : ℕ, k ^ (q ^ n) = 1} = ⊤ := by
  set ψ : MulAut K →* MulAut (Cat d) := (MulAut.congr θ).toMonoidHom.comp (quotientCenterAut' K) with hψ
  set T : Set K := {k : K | ∃ a ∈ A, a ≠ 1 ∧ a k = k ∧ ∃ n : ℕ, k ^ (q ^ n) = 1} with hT
  have hcop : Nat.Coprime (Nat.card (Subgroup.center K)) q := coprime_card_center hp hq hqp hO
  have hψa : ∀ (a : MulAut K) (y₀ : K), ψ a (θ (QuotientGroup.mk y₀)) = θ (QuotientGroup.mk (a y₀)) := by
    intro a y₀
    simp [hψ, MulAut.congr, quotientCenterAut']
  have hmap : (Subgroup.closure T).map (QuotientGroup.mk' (Subgroup.center K)) = ⊤ := by
    set M := (Subgroup.closure T).map (QuotientGroup.mk' (Subgroup.center K)) with hM
    have hgenM : uniPlaneClosure q (A.map ψ) ≤ M.comap θ.symm.toMonoidHom := by
      rw [uniPlaneClosure, Subgroup.closure_le]
      rintro s ⟨e, he, he1, hes, n, hn⟩
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 he
      have ha1 : a ≠ 1 := fun h => he1 (by rw [h, map_one])
      obtain ⟨y₀, hy₀⟩ := QuotientGroup.mk_surjective (θ.symm s)
      have hs : s = θ (QuotientGroup.mk y₀) := by rw [hy₀, MulEquiv.apply_symm_apply]
      have hu : (QuotientGroup.mk y₀ : K ⧸ Subgroup.center K) ^ (q ^ n) = 1 := by
        apply θ.injective
        rw [map_pow, ← hs, hn, map_one]
      have hφ : (QuotientGroup.mk (a y₀) : K ⧸ Subgroup.center K) = QuotientGroup.mk y₀ := by
        apply θ.injective
        rw [← hψa, ← hs]
        exact hes
      obtain ⟨y, hy, hyn, hya⟩ := exists_lift_fixed hcop a y₀ hu hφ
      have hyT : y ∈ Subgroup.closure T := Subgroup.subset_closure ⟨a, ha, ha1, hya, n, hyn⟩
      show θ.symm s ∈ M
      rw [← hy₀, ← hy]
      exact Subgroup.mem_map_of_mem _ hyT
    rw [eq_top_iff]
    intro u _
    have h1 : θ u ∈ M.comap θ.symm.toMonoidHom := by
      apply hgenM
      rw [hgen]
      exact Subgroup.mem_top _
    rw [Subgroup.mem_comap] at h1
    simpa using h1
  refine eq_top_of_sup_center hperf ?_
  have h1 := Subgroup.comap_map_eq (QuotientGroup.mk' (Subgroup.center K)) (Subgroup.closure T)
  rw [hmap, Subgroup.comap_top, QuotientGroup.ker_mk'] at h1
  exact h1.symm

end Lift

section Five

open Inputs2311c

@[expose] def FiveRest (d : TauCeti.ValidLieTypeIndex) (p : ℕ) (E : Subgroup (MulAut (Cat d))) : Prop :=
  OddCpfRest d p E ∧ d.1.characteristic = 5 ∧ p = 3

theorem uniSeitzPlanes_fiveRest_of_rest (h : UniSeitzPlanes OddCpfRest) : UniSeitzPlanes FiveRest :=
  h.mono fun _ _ _ hE => hE.1

theorem uniSeitzPlanes_five_of_rest
    (h : UniSeitzPlanes FiveRest) :
    UniSeitzPlanes fun d p E => OddCpf d p E ∧ d.1.characteristic = 5 ∧ p = 3 := by
  have h₂ : UniSeitzPlanes fun d p E =>
      (OddCpf d p E ∧ d.1.characteristic = 5 ∧ p = 3) ∧ ¬ IsLinearIndex d.1 :=
    UniSeitzPlanes.of_cover (fun d p _ _ E hE => by
      by_cases hx : InnerPlane d p E ∧ IsChevalleyExcIndex d.1 ∧ NormalizesRSubgroup d E
      · exact Or.inl hx
      · exact Or.inr ⟨⟨hE.1.1, hE.2, hx⟩, hE.1.2⟩) uniSeitzPlanes_excParabolic h
  exact UniSeitzPlanes.of_cover (fun d p _ _ E hE => by
    by_cases hl : IsLinearIndex d.1
    · exact Or.inl ⟨hl, hE.1.1, hE.1.2⟩
    · exact Or.inr ⟨hE, hl⟩) uniSeitzPlanes_linear h₂

@[expose] def Input14_2Five : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.LocalAnalysis.GLTheoremA.IsKHat K → GLAPPrimeCore 3 K = ⊥ →
    IsLieChar (· = 5) K → ∀ a : MulAut K, orderOf a = 3 → ∀ k : K, a k = k → (∃ n : ℕ, k ^ (5 ^ n) = 1) →
      k ∈ ⨆ (J : Subgroup K) (_ : J ∈ Inputs256b.chev5Comps a), J

@[expose] def InputGen2311FiveNonCpf : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.LocalAnalysis.GLTheoremA.IsKHat K → GLAPPrimeCore 3 K = ⊥ →
    ∀ d : TauCeti.ValidLieTypeIndex, Nonempty (K ⧸ Subgroup.center K ≃* Cat d) → d.1.characteristic = 5 →
      ¬ CentralPrimeFree 3 d.1 →
      ∀ x : MulAut K, orderOf x = 3 → ∀ L : Subgroup K, GLAPComponent 3 (Prop1310a5.fixedSub x) L →
        IsAltType 5 (barOf 3 L) → ∀ y ∈ L, orderOf y = 3 →
          Prop1310a5b.Kstar (Prop1310a5b.Agrp x y) Inputs256b.chev5Comps = ⊤

theorem uniPlaneGen_five
    (hU : UniSeitzPlanes fun d p E => OddCpf d p E ∧ d.1.characteristic = 5 ∧ p = 3)
    {K : Type} [Group K] (hperf : commutator K = ⊤) {d : TauCeti.ValidLieTypeIndex}
    (θ : K ⧸ Subgroup.center K ≃* Cat d) (hd5 : d.1.characteristic = 5) (hcpf : CentralPrimeFree 3 d.1)
    {A : Subgroup (MulAut K)} (hAel : IsElemAbelian 3 A) (hA9 : Nat.card A = 9) :
    UniPlaneGen 5 (A.map ((MulAut.congr θ).toMonoidHom.comp (quotientCenterAut' K))) := by
  have hψi : Function.Injective ((MulAut.congr θ).toMonoidHom.comp (quotientCenterAut' K)) :=
    (MulAut.congr θ).injective.comp (quotientCenterAut'_injective hperf)
  have hEel := CFSG.Open.IsElemAbelian.map hAel ((MulAut.congr θ).toMonoidHom.comp (quotientCenterAut' K))
  have hEc : Nat.card (A.map ((MulAut.congr θ).toMonoidHom.comp (quotientCenterAut' K))) = 3 ^ 2 := by
    rw [Subgroup.card_map_of_injective hψi, hA9]
    norm_num
  have h3d : (3 : ℕ) ≠ d.1.characteristic := by rw [hd5]; norm_num
  have hex : ¬ CFSG.AGLEmbeddingD2.IsD2SeitzException 3 d.1 := fun hex => by
    have := characteristic_eq_two_of_d2Exc hex
    omega
  have hgen := hU d 3 Nat.prime_three (by norm_num) h3d hex _ hEel hEc ⟨⟨by omega, hcpf⟩, hd5, rfl⟩
  rwa [hd5] at hgen

theorem kstar_chev5_of_gen {K : Type} [Group K] [Finite K] (hK : CFSG.LocalAnalysis.GLTheoremA.IsKHat K)
    (hcore : GLAPPrimeCore 3 K = ⊥) (h5 : IsLieChar (· = 5) K) (h142 : Input14_2Five)
    {A : Subgroup (MulAut K)} (hAel : IsElemAbelian 3 A)
    (htop : Subgroup.closure {k : K | ∃ a ∈ A, a ≠ 1 ∧ a k = k ∧ ∃ n : ℕ, k ^ (5 ^ n) = 1} = ⊤) :
    Prop1310a5b.Kstar A Inputs256b.chev5Comps = ⊤ := by
  rw [eq_top_iff, ← htop, Subgroup.closure_le]
  rintro k ⟨a, haA, ha1, hak, n, hkn⟩
  have ha3 : orderOf a = 3 := orderOf_eq_prime (hAel.2 a haA) ha1
  have hk := h142 K hK hcore h5 a ha3 k hak ⟨n, hkn⟩
  have hle : (⨆ (J : Subgroup K) (_ : J ∈ Inputs256b.chev5Comps a), J) ≤
      Prop1310a5b.Kstar A Inputs256b.chev5Comps :=
    iSup₂_le fun J hJ => le_kstar haA ha1 hJ
  exact hle hk

@[expose] def UniGen2311FiveNonCpf : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.LocalAnalysis.GLTheoremA.IsKHat K → GLAPPrimeCore 3 K = ⊥ →
    ∀ d : TauCeti.ValidLieTypeIndex, ∀ θ : K ⧸ Subgroup.center K ≃* Cat d, d.1.characteristic = 5 →
      ¬ CentralPrimeFree 3 d.1 →
      ∀ x : MulAut K, orderOf x = 3 → ∀ L : Subgroup K, GLAPComponent 3 (Prop1310a5.fixedSub x) L →
        IsAltType 5 (barOf 3 L) → ∀ y ∈ L, orderOf y = 3 →
          UniPlaneGen 5 ((Prop1310a5b.Agrp x y).map ((MulAut.congr θ).toMonoidHom.comp (quotientCenterAut' K)))

theorem inputGen2311FiveNonCpf_of_uni (hU : UniGen2311FiveNonCpf) (h142 : Input14_2Five) :
    InputGen2311FiveNonCpf := by
  intro K _ _ hK hcore d hθ hd5 hcpf x hx L hL hL5 y hyL hy
  obtain ⟨θ⟩ := hθ
  obtain ⟨hAel, -⟩ := agrp_facts hx hL hL5 hyL hy
  exact kstar_chev5_of_gen hK hcore ⟨d, ⟨θ⟩, hd5⟩ h142 hAel
    (closure_fixed_eq_top_of_uniPlaneGen Nat.prime_three Nat.prime_five (by norm_num) hK.1.1 hcore θ
      (Prop1310a5b.Agrp x y) (hU K hK hcore d θ hd5 hcpf x hx L hL hL5 y hyL hy))

theorem inputGen2311Five_of_residuals
    (hU : UniSeitzPlanes FiveRest) (hR : InputGen2311FiveNonCpf) (h142 : Input14_2Five) :
    Inputs256b.InputGen2311Five := by
  intro K _ _ hK hcore h5 x hx L hL hL5 y hyL hy
  obtain ⟨d, ⟨θ⟩, hd5⟩ := h5
  by_cases hcpf : CentralPrimeFree 3 d.1
  swap
  · exact hR K hK hcore d ⟨θ⟩ hd5 hcpf x hx L hL hL5 y hyL hy
  have hperf : commutator K = ⊤ := hK.1.1
  obtain ⟨hAel, hA9⟩ := agrp_facts hx hL hL5 hyL hy
  exact kstar_chev5_of_gen hK hcore ⟨d, ⟨θ⟩, hd5⟩ h142 hAel
    (closure_fixed_eq_top_of_uniPlaneGen Nat.prime_three Nat.prime_five (by norm_num) hperf hcore θ
      (Prop1310a5b.Agrp x y) (uniPlaneGen_five (uniSeitzPlanes_five_of_rest hU) hperf θ hd5 hcpf hAel hA9))

end Five

section Chev2

@[expose] def defField : TauCeti.LieTypeIndex → ℕ
  | .A _ q | .twistedA _ q | .B _ q | .C _ q | .D _ q | .twistedD _ q
  | .E6 q | .E7 q | .E8 q | .F4 q | .G2 q | .twistedE6 q | .trialityD4 q => q.card
  | .suzuki m | .reeF4 m => 2 ^ (2 * m + 1)
  | .reeG2 m => 3 ^ (2 * m + 1)
  | .tits => 2

@[expose] def Chev2On (P : TauCeti.ValidLieTypeIndex → Prop) : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.LocalAnalysis.GLTheoremA.IsKHat K → GLAPPrimeCore 3 K = ⊥ →
    ¬ IsPiGroup 3 K → (¬ ∃ n : ℕ, IsAltType n (K ⧸ Subgroup.center K)) →
    ∀ d : TauCeti.ValidLieTypeIndex, d.1.characteristic = 2 → P d →
      Nonempty ((K ⧸ Subgroup.center K) ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ∀ x : MulAut K, orderOf x = 3 → ∀ L : Subgroup K, GLAPComponent 3 (Prop1310a5.fixedSub x) L →
        IsAltType 5 (barOf 3 L) → ∀ y ∈ L, orderOf y = 3 → Inputs256b.Concl256W K x y L

@[expose] def IsL2Sixtyfour (d : TauCeti.ValidLieTypeIndex) : Prop :=
  ∃ q : TauCeti.PrimePower, d.1 = .A 1 q ∧ q.card = 64

@[expose] def Chev2Field64 : Prop := Chev2On IsL2Sixtyfour

@[expose] def Chev2Big : Prop :=
  Chev2On fun d => defField d.1 ≠ 2 ∧ defField d.1 ≠ 4 ∧ ¬ IsL2Sixtyfour d

@[expose] def Chev2GF4 : Prop := Chev2On fun d => defField d.1 = 4

@[expose] def Chev2GF2Lin : Prop := Chev2On fun d => defField d.1 = 2 ∧ IsLinearIndex d.1

@[expose] def Chev2GF2 : Prop := Chev2On fun d => defField d.1 = 2 ∧ ¬ IsLinearIndex d.1

theorem input25_6A5Chev2_of_families (h64 : Chev2Field64) (hB : Chev2Big) (h4 : Chev2GF4)
    (h2l : Chev2GF2Lin) (h2 : Chev2GF2) : Inputs256b.Input25_6A5Chev2 := by
  intro K _ _ hK hcore hnotPi hAlt h2K x hx L hL hL5 y hyL hy
  obtain ⟨d, hθ, hd2⟩ := h2K
  by_cases hd64 : IsL2Sixtyfour d
  · exact h64 K hK hcore hnotPi hAlt d hd2 hd64 hθ x hx L hL hL5 y hyL hy
  by_cases hf2 : defField d.1 = 2
  · by_cases hl : IsLinearIndex d.1
    · exact h2l K hK hcore hnotPi hAlt d hd2 ⟨hf2, hl⟩ hθ x hx L hL hL5 y hyL hy
    · exact h2 K hK hcore hnotPi hAlt d hd2 ⟨hf2, hl⟩ hθ x hx L hL hL5 y hyL hy
  by_cases hf4 : defField d.1 = 4
  · exact h4 K hK hcore hnotPi hAlt d hd2 hf4 hθ x hx L hL hL5 y hyL hy
  · exact hB K hK hcore hnotPi hAlt d hd2 ⟨hf2, hf4, hd64⟩ hθ x hx L hL hL5 y hyL hy

end Chev2

@[expose] def Input25_6A5Rest2 : Prop :=
  Inputs256b.InputGen2311Five ∧ Inputs256b.Input25_6A5Chev2

theorem input25_6A5Rest_of_rest2
    (h : Input25_6A5Rest2) : Inputs256b.Input25_6A5Rest :=
  ⟨inputGen2324c_holds, h.1, h.2⟩

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256c

end
