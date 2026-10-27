module

public import CFSG.GH74.GLS.Stage2.Final.Thm4.Final19A
public import CFSG.GroupTheory.Fitting.CoprimeAutomorphisms
public import CFSG.GH74.GLS.Stage2.Final.Thm4.Elem

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm4

open Subgroup CFSG CFSG.LocalCores CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local
  CFSG.ComponentClassification.SmallLocal
open scoped commutatorElement

section Equiv

theorem pPrimePCore_map_equiv {H H' : Type*} [Group H] [Group H'] (p : ℕ) (e : H ≃* H') :
    (pPrimePCore p H).map e.toMonoidHom = pPrimePCore p H' := by
  have hN := CFSG.pPrimeCore_map_iso p e
  let ē : H ⧸ pPrimeCore p H ≃* H' ⧸ pPrimeCore p H' := QuotientGroup.congr _ _ e hN
  have hP : (pCore p (H ⧸ pPrimeCore p H)).map ē.toMonoidHom = pCore p (H' ⧸ pPrimeCore p H') :=
    CFSG.pCore_map_iso p ē
  ext x
  rw [Subgroup.mem_map_equiv]
  unfold pPrimePCore
  rw [Subgroup.mem_comap, Subgroup.mem_comap, ← hP, Subgroup.mem_map_equiv]
  have : ē.symm ((QuotientGroup.mk' (pPrimeCore p H')) x) =
      (QuotientGroup.mk' (pPrimeCore p H)) (e.symm x) := by
    apply ē.injective
    rw [MulEquiv.apply_symm_apply]
    have h1 := QuotientGroup.congr_mk (pPrimeCore p H) (pPrimeCore p H') e hN (e.symm x)
    have h2 : ē ((e.symm x : H) : H ⧸ pPrimeCore p H) =
        ((e (e.symm x) : H') : H' ⧸ pPrimeCore p H') := h1
    show (x : H' ⧸ pPrimeCore p H') = ē ((e.symm x : H) : H ⧸ pPrimeCore p H)
    rw [h2]
    simp
  rw [this]

instance pPrimePCore_characteristic (p : ℕ) (H : Type*) [Group H] : (pPrimePCore p H).Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  intro φ
  exact pPrimePCore_map_equiv p φ

end Equiv

@[expose] def O22Res (X : Type) [Group X] : Subgroup X :=
  (pPrimePCore 2 ↥(oResidual 2 X)).map (oResidual 2 X).subtype

@[expose] def O2coreRes (X : Type) [Group X] : Subgroup X :=
  (pCore 2 ↥(oResidual 2 X)).map (oResidual 2 X).subtype

section Basic

variable {X : Type} [Group X] [Finite X]

instance fitOdd_normal : (fitOdd X).Normal := by
  unfold fitOdd
  infer_instance

omit [Finite X] in
theorem O22Res_normal : (O22Res X).Normal := by
  have : (oResidual 2 X).Normal := oResidual_normal_aux 2 X
  unfold O22Res
  infer_instance

omit [Finite X] in
theorem O2coreRes_normal : (O2coreRes X).Normal := by
  have : (oResidual 2 X).Normal := oResidual_normal_aux 2 X
  unfold O2coreRes
  infer_instance

theorem coprime_orderOf_of_mem_pPrimeCore {x : X} (hx : x ∈ pPrimeCore 2 X) :
    Nat.Coprime (orderOf x) 2 := by
  have h1 : orderOf (⟨x, hx⟩ : ↥(pPrimeCore 2 X)) ∣ Nat.card ↥(pPrimeCore 2 X) :=
    _root_.orderOf_dvd_natCard _
  have h2 : orderOf x = orderOf (⟨x, hx⟩ : ↥(pPrimeCore 2 X)) := (Subgroup.orderOf_mk x hx).symm
  rw [h2]
  exact (Nat.Coprime.coprime_dvd_left h1 (pPrimeCore_coprime_card (p := 2) (G := X)).symm)

theorem eq_one_of_mem_pPrimeCore_of_two_pow {x : X} (hx : x ∈ pPrimeCore 2 X) {a : ℕ}
    (h : x ^ (2 ^ a) = 1) : x = 1 := by
  have h1 : orderOf x ∣ 2 ^ a := orderOf_dvd_of_pow_eq_one h
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd
    ((coprime_orderOf_of_mem_pPrimeCore hx).pow_right a) h1)

theorem pPrimeCore_le_oResidual : pPrimeCore 2 X ≤ oResidual 2 X := fun _ hx =>
  Subgroup.subset_closure (coprime_orderOf_of_mem_pPrimeCore hx)

theorem map_pPrimeCore_oResidual :
    (pPrimeCore 2 ↥(oResidual 2 X)).map (oResidual 2 X).subtype = pPrimeCore 2 X := by
  have hYn : (oResidual 2 X).Normal := oResidual_normal_aux 2 X
  apply le_antisymm
  · have hnormal : ((pPrimeCore 2 ↥(oResidual 2 X)).map (oResidual 2 X).subtype).Normal := inferInstance
    refine le_sSup ⟨hnormal, ?_⟩
    rw [Subgroup.card_map_of_injective (oResidual 2 X).subtype_injective]
    exact pPrimeCore_coprime_card
  · have hN : (pPrimeCore 2 X).subgroupOf (oResidual 2 X) ≤ pPrimeCore 2 ↥(oResidual 2 X) := by
      refine le_sSup ⟨inferInstance, ?_⟩
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe pPrimeCore_le_oResidual).toEquiv]
      exact pPrimeCore_coprime_card
    calc pPrimeCore 2 X = ((pPrimeCore 2 X).subgroupOf (oResidual 2 X)).map (oResidual 2 X).subtype :=
          (Subgroup.map_subgroupOf_eq_of_le pPrimeCore_le_oResidual).symm
      _ ≤ _ := Subgroup.map_mono hN

theorem pPrimeCore_le_O22Res : pPrimeCore 2 X ≤ O22Res X := by
  rw [← map_pPrimeCore_oResidual]
  refine Subgroup.map_mono fun x hx => ?_
  change (QuotientGroup.mk' (pPrimeCore 2 ↥(oResidual 2 X)) x) ∈ pCore 2 _
  have h1 : (QuotientGroup.mk' (pPrimeCore 2 ↥(oResidual 2 X))) x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
  rw [h1]
  exact one_mem _

omit [Finite X] in
theorem O2coreRes_le_O22Res : O2coreRes X ≤ O22Res X := by
  refine Subgroup.map_mono fun x hx => ?_
  change (QuotientGroup.mk' (pPrimeCore 2 ↥(oResidual 2 X)) x) ∈ pCore 2 _
  have hn : ((pCore 2 ↥(oResidual 2 X)).map (QuotientGroup.mk' (pPrimeCore 2 ↥(oResidual 2 X)))).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  have hle : (pCore 2 ↥(oResidual 2 X)).map (QuotientGroup.mk' (pPrimeCore 2 ↥(oResidual 2 X))) ≤
      pCore 2 (↥(oResidual 2 X) ⧸ pPrimeCore 2 ↥(oResidual 2 X)) :=
    le_sSup ⟨hn, (pCore_isPGroup (G := ↥(oResidual 2 X)) (p := 2)).map _⟩
  exact hle ⟨x, hx, rfl⟩

theorem exists_pow_mem_pPrimeCore_of_mem_O22Res {w : X} (hw : w ∈ O22Res X) :
    ∃ a : ℕ, w ^ (2 ^ a) ∈ pPrimeCore 2 X := by
  obtain ⟨y, hy, rfl⟩ := hw
  have hy' : (QuotientGroup.mk' (pPrimeCore 2 ↥(oResidual 2 X)) y) ∈ pCore 2 (↥(oResidual 2 X) ⧸ pPrimeCore 2 ↥(oResidual 2 X)) := hy
  obtain ⟨a, ha⟩ := (pCore_isPGroup (G := ↥(oResidual 2 X) ⧸ pPrimeCore 2 ↥(oResidual 2 X)) (p := 2))
    ⟨_, hy'⟩
  refine ⟨a, ?_⟩
  rw [← map_pPrimeCore_oResidual]
  refine ⟨y ^ (2 ^ a), ?_, by simp⟩
  have h1 : (QuotientGroup.mk' (pPrimeCore 2 ↥(oResidual 2 X)) y) ^ (2 ^ a) = 1 := congrArg Subtype.val ha
  rw [← map_pow] at h1
  exact (QuotientGroup.eq_one_iff _).mp h1

theorem mem_of_two_element_of_sylow_inf_le (S₀ : Sylow 2 X) {W C : Subgroup X} [W.Normal] [C.Normal]
    (h : (S₀ : Subgroup X) ⊓ W ≤ C) {u : X} (hu : u ∈ W) (hu2 : ∃ a : ℕ, u ^ (2 ^ a) = 1) : u ∈ C := by
  have hp : IsPGroup 2 (Subgroup.zpowers u) := by
    obtain ⟨a, ha⟩ := hu2
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one ha)
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  obtain ⟨S₁, hS₁⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X S₁ S₀
  have hmem : g * u * g⁻¹ ∈ ((g • S₁ : Sylow 2 X) : Subgroup X) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul u (MulAut.conj g) _ (hS₁ (Subgroup.mem_zpowers u))
  rw [hg] at hmem
  have hW : g * u * g⁻¹ ∈ W := (inferInstance : W.Normal).conj_mem u hu g
  have hC : g * u * g⁻¹ ∈ C := h ⟨hmem, hW⟩
  have := (inferInstance : C.Normal).conj_mem _ hC g⁻¹
  simpa [mul_assoc] using this

theorem map_mk_eq_top_of_isPGroup' {Z : Type} [Group Z] [Finite Z] {p : ℕ} [Fact p.Prime] (P : Sylow p Z)
    (L : Subgroup Z) [L.Normal] (hL : IsPGroup p (Z ⧸ L)) :
    (P : Subgroup Z).map (QuotientGroup.mk' L) = ⊤ := by
  obtain ⟨k, hk⟩ := hL.index ((P : Subgroup Z).map (QuotientGroup.mk' L))
  have hdvd := Subgroup.index_map_dvd (P : Subgroup Z) (QuotientGroup.mk'_surjective L)
  rw [hk] at hdvd
  have hk0 : k = 0 := by
    by_contra hk0
    exact P.not_dvd_index ((dvd_pow_self p hk0).trans hdvd)
  rw [hk0, pow_zero] at hk
  exact Subgroup.index_eq_one.mp hk

theorem commute_of_two_element_of_centralizes_fitOdd {u : X} {a : ℕ} (ha : u ^ (2 ^ a) = 1)
    (h : ∀ f ∈ fitOdd X, u * f = f * u) : ∀ n ∈ pPrimeCore 2 X, u * n = n * u := by
  have hsolv : Group.IsSolvable ↥(pPrimeCore 2 X) := pPrimeCore_solvable
  have hN : (pPrimeCore 2 X).Normal := inferInstance
  let φ : MulAut ↥(pPrimeCore 2 X) := MulAut.conjNormal u
  have hφ : φ = 1 := by
    refine CFSG.mulAut_eq_one_of_fixes_fittingSubgroup ↥(pPrimeCore 2 X) hsolv φ (2 ^ a) ?_ ?_ ?_
    · have : φ ^ (2 ^ a) = MulAut.conjNormal (u ^ (2 ^ a)) := (map_pow MulAut.conjNormal u (2 ^ a)).symm
      rw [this, ha, map_one]
    · have h1 : Nat.card ↥(fittingSubgroup ↥(pPrimeCore 2 X)) ∣ Nat.card ↥(pPrimeCore 2 X) :=
        Subgroup.card_subgroup_dvd_card _
      exact (Nat.Coprime.coprime_dvd_right h1 (pPrimeCore_coprime_card (p := 2) (G := X))).pow_left a
    · intro x hx
      have hxF : (x : X) ∈ fittingSubgroup X := by
        have h1 := fitting_subnormal_intersection (N := pPrimeCore 2 X) hN.isSubnormal
        have h2 : (x : X) ∈ (fittingSubgroup ↥(pPrimeCore 2 X)).map (pPrimeCore 2 X).subtype := ⟨x, hx, rfl⟩
        rw [h1] at h2
        exact h2.2
      apply Subtype.ext
      change u * (x : X) * u⁻¹ = x
      exact conj_eq_of_comm (h x ⟨hxF, x.2⟩)
  intro n hn
  have h1 := congrArg (fun ψ : MulAut ↥(pPrimeCore 2 X) => (ψ ⟨n, hn⟩ : X)) hφ
  change u * n * u⁻¹ = n at h1
  calc u * n = (u * n * u⁻¹) * u := by group
    _ = n * u := by rw [h1]

omit [Finite X] in
theorem O22Res_le_oResidual : O22Res X ≤ oResidual 2 X := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

omit [Finite X] in
theorem two_pow_of_mem_O2coreRes {x : X} (hx : x ∈ O2coreRes X) : ∃ k : ℕ, x ^ (2 ^ k) = 1 := by
  obtain ⟨y, hy, rfl⟩ := hx
  obtain ⟨k, hk⟩ := (pCore_isPGroup (G := ↥(oResidual 2 X)) (p := 2)) ⟨y, hy⟩
  refine ⟨k, ?_⟩
  have h1 := congrArg (fun z : ↥(pCore 2 ↥(oResidual 2 X)) => ((z : ↥(oResidual 2 X)) : X)) hk
  simpa using h1

theorem internalDirectProduct_of_sylow (S₀ : Sylow 2 X)
    (h : ∀ s ∈ (S₀ : Subgroup X) ⊓ O22Res X, ∀ f ∈ fitOdd X, s * f = f * s) :
    IsInternalDirectProduct (pPrimeCore 2 X) (O2coreRes X) (O22Res X) := by
  have hYn : (oResidual 2 X).Normal := oResidual_normal_aux 2 X
  have hWn : (O22Res X).Normal := O22Res_normal
  have hTn : (O2coreRes X).Normal := O2coreRes_normal
  have h2 : ∀ u ∈ O22Res X, (∃ a : ℕ, u ^ (2 ^ a) = 1) → ∀ f ∈ fitOdd X, u * f = f * u := by
    intro u hu hu2 f hf
    have hC := mem_of_two_element_of_sylow_inf_le S₀ (W := O22Res X)
      (C := Subgroup.centralizer (fitOdd X : Set X))
      (fun s hs => Subgroup.mem_centralizer_iff.mpr fun f hf => (h s hs f hf).symm) hu hu2
    exact (Subgroup.mem_centralizer_iff.mp hC f hf).symm
  have hHH : ∀ u ∈ O22Res X, (∃ a : ℕ, u ^ (2 ^ a) = 1) → ∀ n ∈ pPrimeCore 2 X, u * n = n * u := by
    intro u hu hu2
    obtain ⟨a, ha⟩ := hu2
    exact commute_of_two_element_of_centralizes_fitOdd ha (h2 u hu ⟨a, ha⟩)
  let N' : Subgroup ↥(O22Res X) := (pPrimeCore 2 X).subgroupOf (O22Res X)
  have hquot : IsPGroup 2 (↥(O22Res X) ⧸ N') := by
    intro q
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨a, ha⟩ := exists_pow_mem_pPrimeCore_of_mem_O22Res w.2
    refine ⟨a, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact ha
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥(O22Res X)) := inferInstance
  have hPtop : (P : Subgroup ↥(O22Res X)).map (QuotientGroup.mk' N') = ⊤ :=
    map_mk_eq_top_of_isPGroup' P N' hquot
  have hdecomp : ∀ w : ↥(O22Res X), ∃ p ∈ (P : Subgroup ↥(O22Res X)), p⁻¹ * w ∈ N' := by
    intro w
    have hw : QuotientGroup.mk' N' w ∈ (P : Subgroup ↥(O22Res X)).map (QuotientGroup.mk' N') := by
      rw [hPtop]
      trivial
    obtain ⟨p, hp, hpw⟩ := hw
    exact ⟨p, hp, (QuotientGroup.eq).mp hpw⟩
  have hPcomm : ∀ p ∈ (P : Subgroup ↥(O22Res X)), ∀ n ∈ N', p * n = n * p := by
    intro p hp n hn
    obtain ⟨a, ha⟩ := P.isPGroup' ⟨p, hp⟩
    have hp2 : (p : X) ^ (2 ^ a) = 1 := by
      have h1 := congrArg (fun z : ↥(P : Subgroup ↥(O22Res X)) => ((z : ↥(O22Res X)) : X)) ha
      simpa using h1
    exact Subtype.ext (hHH (p : X) p.2 ⟨a, hp2⟩ (n : X) (Subgroup.mem_subgroupOf.mp hn))
  have hPn : (P : Subgroup ↥(O22Res X)).Normal := by
    refine ⟨fun x hx w => ?_⟩
    obtain ⟨p, hp, hn⟩ := hdecomp w
    obtain ⟨n, hn', rfl⟩ : ∃ n ∈ N', w = p * n := ⟨p⁻¹ * w, hn, by group⟩
    have hc : x * n = n * x := hPcomm x hx n hn'
    have h1 : p * n * x * (p * n)⁻¹ = p * x * p⁻¹ := by
      calc p * n * x * (p * n)⁻¹ = p * (n * x * n⁻¹) * p⁻¹ := by group
        _ = p * x * p⁻¹ := by rw [← hc]; group
    rw [h1]
    exact P.mul_mem (P.mul_mem hp hx) (P.inv_mem hp)
  have hallP : ∀ u : ↥(O22Res X), (∃ a : ℕ, u ^ (2 ^ a) = 1) → u ∈ (P : Subgroup ↥(O22Res X)) := by
    intro u hu2
    obtain ⟨a, ha⟩ := hu2
    have hpg : IsPGroup 2 (Subgroup.zpowers u) := by
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one ha)
      exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
    have hsup : IsPGroup 2 ↥(Subgroup.zpowers u ⊔ (P : Subgroup ↥(O22Res X))) :=
      hpg.to_sup_of_normal_right P.isPGroup'
    have hmax := P.is_maximal' hsup le_sup_right
    rw [← hmax]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers u)
  let Q : Subgroup X := (P : Subgroup ↥(O22Res X)).map (O22Res X).subtype
  have hQn : Q.Normal := by
    refine ⟨fun y hy g => ?_⟩
    obtain ⟨p, hp, rfl⟩ := hy
    obtain ⟨a, ha⟩ := P.isPGroup' ⟨p, hp⟩
    have hp2 : (p : X) ^ (2 ^ a) = 1 := by
      have h1 := congrArg (fun z : ↥(P : Subgroup ↥(O22Res X)) => ((z : ↥(O22Res X)) : X)) ha
      simpa using h1
    have hgW : g * (p : X) * g⁻¹ ∈ O22Res X := hWn.conj_mem p p.2 g
    have hg2 : (g * (p : X) * g⁻¹) ^ (2 ^ a) = 1 := by rw [conj_pow, hp2]; group
    have hmem := hallP ⟨_, hgW⟩ ⟨a, Subtype.ext (by simpa using hg2)⟩
    exact ⟨_, hmem, rfl⟩
  have hQY : Q ≤ oResidual 2 X := by
    rintro _ ⟨p, -, rfl⟩
    exact O22Res_le_oResidual p.2
  have hQT : Q ≤ O2coreRes X := by
    have hQ2 : IsPGroup 2 ↥Q := (P.isPGroup').map _
    have hn : (Q.subgroupOf (oResidual 2 X)).Normal := inferInstance
    have hle : Q.subgroupOf (oResidual 2 X) ≤ pCore 2 ↥(oResidual 2 X) := by
      refine le_sSup ⟨hn, ?_⟩
      exact hQ2.of_equiv (Subgroup.subgroupOfEquivOfLe hQY).symm
    calc Q = (Q.subgroupOf (oResidual 2 X)).map (oResidual 2 X).subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hQY).symm
      _ ≤ O2coreRes X := Subgroup.map_mono hle
  refine ⟨le_antisymm (sup_le pPrimeCore_le_O22Res O2coreRes_le_O22Res) ?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨p, hp, hn⟩ := hdecomp ⟨w, hw⟩
    have hwp : w = ((p : ↥(O22Res X)) : X) * ((p⁻¹ * ⟨w, hw⟩ : ↥(O22Res X)) : X) := by simp
    rw [hwp, sup_comm]
    exact Subgroup.mul_mem_sup (hQT ⟨p, hp, rfl⟩) (Subgroup.mem_subgroupOf.mp hn)
  · intro a ha b hb
    obtain ⟨k, hk⟩ := two_pow_of_mem_O2coreRes hb
    exact (hHH b (O2coreRes_le_O22Res hb) ⟨k, hk⟩ a ha).symm
  · rw [eq_bot_iff]
    rintro x ⟨hxN, hxT⟩
    obtain ⟨k, hk⟩ := two_pow_of_mem_O2coreRes hxT
    exact Subgroup.mem_bot.mpr (eq_one_of_mem_pPrimeCore_of_two_pow hxN hk)

end Basic

section FpiBridge

theorem mem_of_odd_of_mem_sup_pCore {Φ : Type*} [Group Φ] [Finite Φ] {H : Subgroup Φ} [H.Normal] {x : Φ}
    (hx : x ∈ pCore 2 Φ ⊔ H) (hodd : Nat.Coprime (orderOf x) 2) : x ∈ H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha, h, hh, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hx
  obtain ⟨k, hk⟩ := (pCore_isPGroup (G := Φ) (p := 2)) ⟨a, ha⟩
  have hk' : a ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have hh1 : QuotientGroup.mk' H h = 1 := (QuotientGroup.eq_one_iff h).mpr hh
  have h1 : QuotientGroup.mk' H (a * h) = QuotientGroup.mk' H a := by
    rw [map_mul, hh1, mul_one]
  have h2 : orderOf (QuotientGroup.mk' H (a * h)) ∣ orderOf (a * h) := orderOf_map_dvd _ _
  have h3 : orderOf (QuotientGroup.mk' H (a * h)) ∣ 2 ^ k := by
    rw [h1]
    refine orderOf_dvd_of_pow_eq_one ?_
    rw [← map_pow, hk', map_one]
  have h4 : orderOf (QuotientGroup.mk' H (a * h)) = 1 :=
    Nat.Coprime.eq_one_of_dvd ((hodd.pow_right k).coprime_dvd_left h2) h3
  have := orderOf_eq_one_iff.mp h4
  exact (QuotientGroup.eq_one_iff _).mp this

variable {G : Type} [Group G] [Finite G]

theorem fitOdd_le_Fpi (M : Subgroup G) :
    (fitOdd ↥M).map M.subtype ≤ Bg.Fpi {r | r.Prime ∧ r ≠ 2} M := by
  have hFnil : Group.IsNilpotent ↥(Bg.Fm M) :=
    Group.nilpotent_of_mulEquiv (G := ↥(fittingSubgroup ↥M))
      ((fittingSubgroup ↥M).equivMapOfInjective M.subtype M.subtype_injective)
  set D : Subgroup G := (fitOdd ↥M).map M.subtype with hD
  have hDF : D ≤ Bg.Fm M := Subgroup.map_mono inf_le_left
  set E : Subgroup ↥(Bg.Fm M) := D.subgroupOf (Bg.Fm M) with hE
  have hEn : E.Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨d, hd, hdx⟩ := hx
    obtain ⟨g', -, hg'⟩ := g.2
    refine ⟨g' * d * g'⁻¹, (inferInstance : (fitOdd ↥M).Normal).conj_mem d hd g', ?_⟩
    simp only [map_mul, map_inv, hg', hdx]
    rfl
  have hEnil : Group.IsNilpotent ↥E := inferInstance
  have hle := normal_nilpotent_le_sup_pCore hEn hEnil
  set H' : Subgroup ↥(Bg.Fm M) := ⨆ r ∈ {r : ℕ | r.Prime ∧ r ≠ 2}, pCore r ↥(Bg.Fm M) with hH'
  have hH'n : H'.Normal := Subgroup.biSup_normal _ _ (fun r _ => pCore_normal)
  have hE' : E ≤ pCore 2 ↥(Bg.Fm M) ⊔ H' := by
    refine hle.trans (iSup_le fun q => ?_)
    by_cases hq : (q.1 : ℕ) = 2
    · rw [hq]
      exact le_sup_left
    · have hqp : Nat.Prime (q.1 : ℕ) := Nat.prime_of_mem_primeFactors q.1.2
      exact le_sup_of_le_right (le_iSup₂_of_le (q.1 : ℕ) (show (q.1 : ℕ) ∈ {r : ℕ | r.Prime ∧ r ≠ 2} from ⟨hqp, hq⟩) le_rfl)
  have hEH : E ≤ H' := by
    intro x hx
    have hodd : Nat.Coprime (orderOf x) 2 := by
      obtain ⟨d, hd, hdx⟩ := Subgroup.mem_subgroupOf.mp hx
      rw [← Subgroup.orderOf_coe x, ← hdx]
      have h1 : orderOf (M.subtype d) = orderOf d := Subgroup.orderOf_coe d
      rw [h1]
      exact coprime_orderOf_of_mem_pPrimeCore hd.2
    exact mem_of_odd_of_mem_sup_pCore (hE' hx) hodd
  calc D = E.map (Bg.Fm M).subtype := (Subgroup.map_subgroupOf_eq_of_le hDF).symm
    _ ≤ H'.map (Bg.Fm M).subtype := Subgroup.map_mono hEH
    _ = Bg.Fpi {r | r.Prime ∧ r ≠ 2} M := by
        simp only [hH', Subgroup.map_iSup]
        rfl

end FpiBridge

section GLevel

variable {G : Type} [Group G]

theorem O22Of_O2Of_eq (M : Subgroup G) : O22Of (O2Of M) = (O22Res ↥M).map M.subtype := by
  let R : Subgroup ↥M := oResidual 2 ↥M
  let e : ↥R ≃* ↥(R.map M.subtype) := R.equivMapOfInjective M.subtype M.subtype_injective
  have h1 := pPrimePCore_map_equiv 2 e
  show (pPrimePCore 2 ↥(R.map M.subtype)).map (R.map M.subtype).subtype =
    ((pPrimePCore 2 ↥R).map R.subtype).map M.subtype
  rw [← h1, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem O2coreOf_O2Of_eq (M : Subgroup G) : O2coreOf (O2Of M) = (O2coreRes ↥M).map M.subtype := by
  let R : Subgroup ↥M := oResidual 2 ↥M
  let e : ↥R ≃* ↥(R.map M.subtype) := R.equivMapOfInjective M.subtype M.subtype_injective
  have h1 := CFSG.pCore_map_iso 2 e
  show (pCore 2 ↥(R.map M.subtype)).map (R.map M.subtype).subtype =
    ((pCore 2 ↥R).map R.subtype).map M.subtype
  rw [← h1, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem isInternalDirectProduct_map {X Z : Type*} [Group X] [Group Z] (f : X →* Z)
    (hf : Function.Injective f) {A B H : Subgroup X} (h : IsInternalDirectProduct A B H) :
    IsInternalDirectProduct (A.map f) (B.map f) (H.map f) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by rw [← Subgroup.map_sup, h1], ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, h2 a ha b hb]
  · rw [← Subgroup.map_inf _ _ _ hf, h3, Subgroup.map_bot]

variable [Finite G]

theorem isInternalDirectProduct_of_sylow_of_centralizes {M S : Subgroup G}
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S M)
    (h : ∀ s ∈ S ⊓ (O22Res ↥M).map M.subtype, ∀ f ∈ (fitOdd ↥M).map M.subtype, s * f = f * s) :
    IsInternalDirectProduct (pPrimeCoreOf 2 M) (O2coreOf (O2Of M)) (O22Of (O2Of M)) := by
  obtain ⟨Q, hQ⟩ := hS
  have key := internalDirectProduct_of_sylow Q (X := ↥M) (fun s hs f hf => by
    refine Subtype.ext ?_
    have hs' : (s : G) ∈ S ⊓ (O22Res ↥M).map M.subtype := by
      refine ⟨?_, ⟨s, hs.2, rfl⟩⟩
      rw [← hQ]
      exact ⟨s, hs.1, rfl⟩
    exact h (s : G) hs' (f : G) ⟨f, hf, rfl⟩)
  rw [O22Of_O2Of_eq, O2coreOf_O2Of_eq]
  exact isInternalDirectProduct_map M.subtype M.subtype_injective key

end GLevel

end CFSG.GH74.GLS.Stage2.Final.Thm4
