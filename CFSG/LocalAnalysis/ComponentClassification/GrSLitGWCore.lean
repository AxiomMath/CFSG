module

public import CFSG.ClassicalInvolution.LBalance.Glauberman
public import CFSG.ClassicalInvolution.LBalance.Proof.Central
public import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
public import CFSG.GroupTheory.BurnsideNormalComplement

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup

section Coprime

variable {X : Type*} [Group X] [Finite X]

theorem le_commutator_sup_inf_centralizer_of_odd {D Q : Subgroup X} (hQ : IsPGroup 2 Q)
    (hQD : Q ≤ normalizer (D : Set X)) (hD : Odd (Nat.card D)) :
    D ≤ ⁅D, Q⁆ ⊔ (D ⊓ centralizer (Q : Set X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomm_le : ⁅D, Q⁆ ≤ D := by
    rw [commutator_le]
    intro x hx q hq
    have h1 : q * x⁻¹ * q⁻¹ ∈ D := (mem_normalizer_iff.mp (hQD hq) x⁻¹).mp (inv_mem hx)
    have h2 := mul_mem hx h1
    rw [commutatorElement_def]
    simpa [mul_assoc] using h2
  have hodd : ¬ 2 ∣ Nat.card (⁅D, Q⁆ : Subgroup X) := fun h =>
    (Nat.not_even_iff_odd.mpr (hD.of_dvd_nat (Subgroup.card_dvd_of_le hcomm_le)))
      (even_iff_two_dvd.mpr h)
  intro d hd
  obtain ⟨c, hc, hfix⟩ := (CFSG.Semidihedral.Principal.coprime_invariant_coset_fixed 2 hQ
    (MulAut.conj.comp Q.subtype) ⁅D, Q⁆ hodd d).1 (by
      rintro ⟨a, ha⟩ x hx
      have hxD : x ∈ D := by
        have h := mul_mem (hcomm_le hx) hd
        rwa [inv_mul_cancel_right] at h
      have hax : a * x * a⁻¹ * x⁻¹ ∈ ⁅D, Q⁆ := by
        rw [commutator_comm]
        exact commutator_mem_commutator ha hxD
      change a * x * a⁻¹ * d⁻¹ ∈ ⁅D, Q⁆
      have h := mul_mem hax hx
      rwa [show a * x * a⁻¹ * x⁻¹ * (x * d⁻¹) = a * x * a⁻¹ * d⁻¹ by group] at h)
  have hcD : c ∈ D := by
    have h := mul_mem (hcomm_le hc) hd
    rwa [inv_mul_cancel_right] at h
  have hcC : c ∈ centralizer (Q : Set X) := by
    rw [mem_centralizer_iff]
    intro q hq
    have h := hfix ⟨q, hq⟩
    change q * c * q⁻¹ = c at h
    calc q * c = q * c * q⁻¹ * q := by group
      _ = c * q := by rw [h]
  have h := mul_mem_sup (inv_mem hc) (show c ∈ D ⊓ centralizer (Q : Set X) from ⟨hcD, hcC⟩)
  rwa [show (c * d⁻¹)⁻¹ * c = d by group] at h

theorem map_centralizer_eq_of_odd_ker {E : Type*} [Group E] (f : X →* E)
    (hf : Function.Surjective f) (hodd : ¬ 2 ∣ Nat.card f.ker) {T : Subgroup X}
    (hT : IsPGroup 2 T) :
    (centralizer (T : Set X)).map f = centralizer ((T.map f : Subgroup E) : Set E) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm ?_ fun e he => ?_
  · rintro _ ⟨c, hc, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_iff] at hc
    rw [mem_centralizer_iff]
    rintro _ ⟨t, ht, rfl⟩
    rw [← map_mul, ← map_mul, hc t ht]
  obtain ⟨y, rfl⟩ := hf e
  rw [mem_centralizer_iff] at he
  obtain ⟨c, hc, hfix⟩ := (CFSG.Semidihedral.Principal.coprime_invariant_coset_fixed 2 hT
    (MulAut.conj.comp T.subtype) f.ker hodd y).2 (by
      rintro ⟨a, ha⟩ x hx
      have hxy : f x = f y := by
        have h := MonoidHom.mem_ker.1 hx
        rw [map_mul, map_inv, inv_mul_eq_one] at h
        exact h.symm
      have hcomm : f a * f y = f y * f a := he (f a) ⟨a, ha, rfl⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      change (f y)⁻¹ * f (a * x * a⁻¹) = 1
      rw [map_mul, map_mul, map_inv, hxy, hcomm]
      group)
  refine ⟨c, ?_, ?_⟩
  · rw [SetLike.mem_coe, mem_centralizer_iff]
    intro t ht
    have h := hfix ⟨t, ht⟩
    change t * c * t⁻¹ = c at h
    calc t * c = t * c * t⁻¹ * t := by group
      _ = c * t := by rw [h]
  · have h := MonoidHom.mem_ker.1 hc
    rw [map_mul, map_inv, inv_mul_eq_one] at h
    exact h.symm

end Coprime

section OddCores

variable {X : Type*} [Group X]

theorem le_map_pPrimeCore {H D : Subgroup X} (hDH : D ≤ H)
    (hnorm : ∀ h ∈ H, ∀ d ∈ D, h * d * h⁻¹ ∈ D) (hodd : Odd (Nat.card D)) :
    D ≤ (pPrimeCore 2 H).map H.subtype := by
  have hn : (D.subgroupOf H).Normal := by
    rw [normal_subgroupOf_iff hDH]
    exact fun d h hd hh => hnorm h hh d hd
  have hcard : Nat.Coprime 2 (Nat.card (D.subgroupOf H)) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hDH).toEquiv]
    exact Nat.coprime_two_left.mpr hodd
  have hle : D.subgroupOf H ≤ pPrimeCore 2 H := le_sSup ⟨hn, hcard⟩
  have h := Subgroup.map_mono (f := H.subtype) hle
  rwa [map_subgroupOf_eq_of_le hDH] at h

theorem odd_orderOf_of_mem_map_pPrimeCore [Finite X] {H : Subgroup X} {d : X}
    (hd : d ∈ (pPrimeCore 2 H).map H.subtype) : Odd (orderOf d) := by
  obtain ⟨d, hd, rfl⟩ := hd
  have hcop := pPrimeCore_coprime_card (p := 2) (G := H)
  have hdvd : orderOf d ∣ Nat.card (pPrimeCore 2 H) := by
    rw [← Subgroup.orderOf_mk d hd]
    exact orderOf_dvd_natCard _
  rw [Subgroup.coe_subtype, Subgroup.orderOf_coe]
  exact Nat.coprime_two_left.mp (hcop.coprime_dvd_right hdvd)

theorem odd_card_map_pPrimeCore [Finite X] (H : Subgroup X) :
    Odd (Nat.card ((pPrimeCore 2 H).map H.subtype)) := by
  rw [Subgroup.card_map_of_injective H.subtype_injective]
  exact Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := H))

theorem normal_map_subtype_of_characteristic {N : Subgroup X} [N.Normal] (K : Subgroup N)
    [K.Characteristic] : (K.map N.subtype).Normal := by
  constructor
  rintro _ ⟨k, hk, rfl⟩ g
  have h := (characteristic_iff_map_le.mp (inferInstance : K.Characteristic))
    (MulAut.conjNormal g)
  have hk' : MulAut.conjNormal g k ∈ K := h ⟨k, hk, rfl⟩
  exact ⟨_, hk', by simp [MulAut.conjNormal_apply]⟩

theorem map_pPrimeCore_le_of_normal [Finite X] {N : Subgroup X} [N.Normal] :
    (pPrimeCore 2 N).map N.subtype ≤ pPrimeCore 2 X := by
  have : ((pPrimeCore 2 N).map N.subtype).Normal := normal_map_subtype_of_characteristic _
  refine le_sSup ⟨inferInstance, ?_⟩
  rw [Subgroup.card_map_of_injective N.subtype_injective]
  exact pPrimeCore_coprime_card

theorem pPrimeCore_eq_bot_of_normal [Finite X] (hX : pPrimeCore 2 X = ⊥) {N : Subgroup X}
    [N.Normal] : pPrimeCore 2 N = ⊥ := by
  have h := (map_pPrimeCore_le_of_normal (N := N)).trans hX.le
  rw [le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ N.subtype_injective] at h
  exact h

theorem isPGroup_two_of_normal_comm [Finite X] (hX : pPrimeCore 2 X = ⊥) {A : Subgroup X}
    [A.Normal] (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) : IsPGroup 2 A := by
  have hcore : pPrimeCore 2 A = ⊥ := pPrimeCore_eq_bot_of_normal hX
  intro a
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos a).ne'
  refine ⟨k, ?_⟩
  set b : A := a ^ 2 ^ k with hb
  have hbm : orderOf b = m := by
    rw [hb, orderOf_pow_of_dvd (by positivity) (by rw [hkm]; exact dvd_mul_right _ _), hkm,
      Nat.mul_div_cancel_left _ (by positivity)]
  have hzn : (zpowers b).Normal := by
    constructor
    intro y hy g
    have : g * y * g⁻¹ = y := by
      have h := hA g g.2 y y.2
      have h' : g * y = y * g := Subtype.ext h
      rw [h', mul_inv_cancel_right]
    rwa [this]
  have hzc : Nat.Coprime 2 (Nat.card (zpowers b)) := by
    rw [Nat.card_zpowers, hbm]
    exact Nat.coprime_two_left.mpr hm
  have hle : zpowers b ≤ pPrimeCore 2 A := le_sSup ⟨hzn, hzc⟩
  rw [hcore, le_bot_iff, zpowers_eq_bot] at hle
  exact hle

end OddCores

section Glauberman

variable {X : Type} [Group X] [Finite X]

theorem generalizedFitting_normal : (generalizedFitting X).Normal := by
  have := CFSG.LocalCores.layer_characteristic (G := X)
  have : (fittingSubgroup X).Normal := (CFSG.LocalCores.fitting_nilpotent (G := X)).2.1
  simp only [CFSG.generalizedFitting.eq_sup]
  infer_instance

theorem mem_oddCore_centralizer_of_corefree (hX : pPrimeCore 2 X = ⊥) {Y : Subgroup X}
    (hY : Y = generalizedFitting X) (S : Sylow 2 Y) {c : X}
    (hc : c ∈ centralizer (((S : Subgroup Y).map Y.subtype : Subgroup X) : Set X))
    (hodd : Odd (orderOf c)) :
    c ∈ (pPrimeCore 2 (centralizer (((S : Subgroup Y).map Y.subtype : Subgroup X) : Set X))).map
      (centralizer (((S : Subgroup Y).map Y.subtype : Subgroup X) : Set X)).subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Y.Normal := hY ▸ generalizedFitting_normal
  set S' : Subgroup X := (S : Subgroup Y).map Y.subtype with hS'
  set C : Subgroup X := centralizer (S' : Set X) with hCdef
  set A : Subgroup X := centralizer (Y : Set X) with hAdef
  have hAF : A ≤ Y := by
    rw [hAdef, hY]
    exact centralizer_generalizedFitting_le X
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    (mem_centralizer_iff.mp ha b (hAF hb)).symm
  have hA2 : IsPGroup 2 A := isPGroup_two_of_normal_comm hX hAcomm
  have hAS : A ≤ S' := by
    have hn : (A.subgroupOf Y).Normal := Subgroup.Normal.subgroupOf inferInstance Y
    have hp : IsPGroup 2 (A.subgroupOf Y) := hA2.comap_of_injective Y.subtype Y.subtype_injective
    have hle := hp.le_sylow_of_normal S
    intro a ha
    exact ⟨⟨a, hAF ha⟩, hle ha, rfl⟩
  have hFcore : pPrimeCore 2 Y = ⊥ := pPrimeCore_eq_bot_of_normal hX
  obtain ⟨N, hNn, hNodd, hNq⟩ :=
    ClassicalInvolution.glauberman_sylowFixingAut_normal_complement hFcore S
  have hfix : ∀ x : C, (MulAut.conjNormal (x : X) : MulAut Y) ∈
      ClassicalInvolution.sylowFixingAut (S : Subgroup Y) := fun x =>
    ClassicalInvolution.LBalanceProof.conjNormal_mem_sylowFixingAut _ (x : X)
      (fun s hs => (mem_centralizer_iff.mp x.2 (s : X) ⟨s, hs, rfl⟩).symm)
  let φ : C →* ClassicalInvolution.sylowFixingAut (S : Subgroup Y) :=
    ((MulAut.conjNormal : X →* MulAut Y).comp C.subtype).codRestrict _ hfix
  have hφ : ∀ x : C, ((φ x : MulAut Y)) = MulAut.conjNormal (x : X) := fun _ => rfl
  have hφN : ∀ x : C, Odd (orderOf x) → φ x ∈ N := by
    intro x hx
    have h1 : Odd (orderOf (QuotientGroup.mk' N (φ x))) :=
      (hx.of_dvd_nat (orderOf_map_dvd φ x)).of_dvd_nat (orderOf_map_dvd _ _)
    obtain ⟨n, hn⟩ := hNq (QuotientGroup.mk' N (φ x))
    have h3 : orderOf (QuotientGroup.mk' N (φ x)) ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn
    have h4 : orderOf (QuotientGroup.mk' N (φ x)) = 1 :=
      Nat.Coprime.eq_one_of_dvd ((Nat.coprime_two_right.mpr h1).pow_right n) h3
    rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h4
    exact h4
  set M : Subgroup C := N.comap φ with hM
  have hMn : M.Normal := Subgroup.Normal.comap hNn φ
  let ψ : M →* ClassicalInvolution.sylowFixingAut (S : Subgroup Y) := φ.comp M.subtype
  set P : Subgroup M := ψ.ker with hP
  have hPA : ∀ k : M, k ∈ P → ((k : C) : X) ∈ A := by
    intro k hk
    rw [mem_centralizer_iff]
    intro y hy
    have h1 : MulAut.conjNormal ((k : C) : X) = (1 : MulAut Y) := by
      rw [← hφ]
      exact congrArg Subtype.val (MonoidHom.mem_ker.mp hk)
    have h2 := congrArg (fun α : MulAut Y => ((α ⟨y, hy⟩ : Y) : X)) h1
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h2
    calc y * ((k : C) : X) = ((k : C) : X) * y * ((k : C) : X)⁻¹ * ((k : C) : X) := by rw [h2]
      _ = ((k : C) : X) * y := by group
  have hP2 : IsPGroup 2 P := by
    intro k
    obtain ⟨n, hn⟩ := hA2 ⟨(((k : M) : C) : X), hPA k k.2⟩
    refine ⟨n, ?_⟩
    apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
    have := congrArg Subtype.val hn
    simpa using this
  have hPidx : ¬ 2 ∣ P.index := by
    rw [hP, index_ker]
    intro h2
    have hdvd : Nat.card ψ.range ∣ Nat.card N := by
      have hle : ψ.range ≤ N := by
        rintro _ ⟨m, rfl⟩
        exact m.2
      exact Subgroup.card_dvd_of_le hle
    exact (Nat.not_even_iff_odd.mpr hNodd) (even_iff_two_dvd.mpr (h2.trans hdvd))
  have hPcen : ∀ k ∈ P, ∀ m : M, m * k = k * m := by
    intro k hk m
    have hkS : (((k : M) : C) : X) ∈ S' := hAS (hPA k hk)
    have h := mem_centralizer_iff.mp ((m : C)).2 _ hkS
    apply Subtype.ext; apply Subtype.ext
    simpa using h.symm
  let PS : Sylow 2 M := hP2.toSylow hPidx
  have hPS : normalizer ((PS : Subgroup M) : Set M) ≤ centralizer ((PS : Subgroup M) : Set M) :=
    fun g _ => mem_centralizer_iff.mpr fun h hh => (hPcen h hh g).symm
  obtain ⟨K, hKn, hK2, hKidx, -, hKchar, -⟩ := CFSG.GroupTheory.burnside_normal_complement PS hPS
  have hMK : ∀ m : M, Odd (orderOf m) → m ∈ K := by
    intro m hm
    obtain ⟨n, hn⟩ := hP2.exists_card_eq
    have hcardq : Nat.card (M ⧸ K) = 2 ^ n := by
      rw [← Subgroup.index_eq_card, hKidx]
      exact hn
    have h1 : orderOf (QuotientGroup.mk' K m) ∣ 2 ^ n := by
      rw [← hcardq]
      exact orderOf_dvd_natCard _
    have h2 : Odd (orderOf (QuotientGroup.mk' K m)) := hm.of_dvd_nat (orderOf_map_dvd _ _)
    have h3 : orderOf (QuotientGroup.mk' K m) = 1 :=
      Nat.Coprime.eq_one_of_dvd ((Nat.coprime_two_right.mpr h2).pow_right n) h1
    rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
    exact h3
  set K'' : Subgroup X := (K.map M.subtype).map C.subtype with hK''
  have hK''C : K'' ≤ C := Subgroup.map_subtype_le _
  have hK''odd : Odd (Nat.card K'') := by
    rw [hK'', Subgroup.card_map_of_injective C.subtype_injective,
      Subgroup.card_map_of_injective M.subtype_injective]
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hK2)
  have hK''norm : ∀ h ∈ C, ∀ d ∈ K'', h * d * h⁻¹ ∈ K'' := by
    rintro h hh _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    have hk' : MulAut.conjNormal (⟨h, hh⟩ : C) k ∈ K :=
      (characteristic_iff_map_le.mp hKchar) (MulAut.conjNormal (⟨h, hh⟩ : C)) ⟨k, hk, rfl⟩
    exact ⟨_, ⟨_, hk', rfl⟩, by simp [MulAut.conjNormal_apply]⟩
  have hK''O : K'' ≤ (pPrimeCore 2 C).map C.subtype := le_map_pPrimeCore hK''C hK''norm hK''odd
  have hxM : (⟨c, hc⟩ : C) ∈ M := hφN ⟨c, hc⟩ (by rwa [Subgroup.orderOf_mk])
  have hxK : (⟨⟨c, hc⟩, hxM⟩ : M) ∈ K := hMK _ (by rwa [Subgroup.orderOf_mk, Subgroup.orderOf_mk])
  exact hK''O ⟨_, ⟨_, hxK, rfl⟩, rfl⟩

end Glauberman

end CFSG.ComponentClassification.GrSLit
