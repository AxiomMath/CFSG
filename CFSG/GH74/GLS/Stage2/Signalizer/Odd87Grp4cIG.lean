module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29Stmt
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Grp4cLift
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Grp4cIOdd
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Grp4cIDer
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic13

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG.ABGLocalTools CFSG.GH74.GLS.Bg.TwoGroups CFSG.GH74.GLS.Stage2.Local
open CFSG.GH74.GLS CFSG.GH74 CFSG CFSG.GH74.GLS.Stage12
open scoped commutatorElement

section Basic

theorem exists_conj_le_of_isSylowOf {G : Type} [Group G] [Finite G] {Q M W : Subgroup G}
    (hQ : IsSylowOf 2 Q M) (hWM : W ≤ M) (hW : IsPGroup 2 ↥W) :
    ∃ m ∈ M, W ≤ Q.map (MulAut.conj m).toMonoidHom := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := hQ
  have hW' : IsPGroup 2 ↥(W.subgroupOf M) := hW.comap_subtype
  obtain ⟨S', hS'⟩ := hW'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥M S S'
  refine ⟨(g : G), g.2, ?_⟩
  intro w hw
  have hwM : (⟨w, hWM hw⟩ : ↥M) ∈ W.subgroupOf M := hw
  have h1 : (⟨w, hWM hw⟩ : ↥M) ∈ (S' : Subgroup ↥M) := hS' hwM
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at h1
  obtain ⟨s, hs, hsw⟩ := h1
  refine Subgroup.mem_map.mpr ⟨(s : G), ?_, ?_⟩
  · rw [← hS]
    exact ⟨s, hs, rfl⟩
  · have := congrArg Subtype.val hsw
    simpa [MulAut.smul_def, MulAut.conj_apply] using this

theorem isSylowOf_map_conj {G : Type} [Group G] [Finite G] {P K : Subgroup G}
    (h : IsSylowOf 2 P K) (m : G) :
    IsSylowOf 2 (P.map (MulAut.conj m).toMonoidHom) (K.map (MulAut.conj m).toMonoidHom) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [isSylowOf_iff] at h ⊢
  obtain ⟨hle, hP, hdvd⟩ := h
  have hinj : Function.Injective (MulAut.conj m).toMonoidHom := (MulAut.conj m).injective
  refine ⟨Subgroup.map_mono hle, hP.map _, ?_⟩
  rw [Subgroup.relIndex_map_map, (MonoidHom.ker_eq_bot_iff _).mpr hinj, sup_bot_eq, sup_bot_eq]
  exact hdvd

theorem centralizer_map_conj {G : Type} [Group G] (Q : Subgroup G) (m : G) :
    centralizer ((Q.map (MulAut.conj m).toMonoidHom : Subgroup G) : Set G) =
      (centralizer (Q : Set G)).map (MulAut.conj m).toMonoidHom := by
  ext g
  constructor
  · intro hg
    refine Subgroup.mem_map.mpr ⟨m⁻¹ * g * m, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro q hq
      have h1 := Subgroup.mem_centralizer_iff.mp hg (m * q * m⁻¹)
        (Subgroup.mem_map.mpr ⟨q, hq, by simp [MulAut.conj_apply]⟩)
      calc q * (m⁻¹ * g * m) = m⁻¹ * ((m * q * m⁻¹) * g) * m := by group
        _ = m⁻¹ * (g * (m * q * m⁻¹)) * m := by rw [h1]
        _ = (m⁻¹ * g * m) * q := by group
    · show m * (m⁻¹ * g * m) * m⁻¹ = g
      group
  · rintro ⟨c, hc, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨q, hq, rfl⟩
    have h1 := Subgroup.mem_centralizer_iff.mp hc q hq
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc m * q * m⁻¹ * (m * c * m⁻¹) = m * (q * c) * m⁻¹ := by group
      _ = m * (c * q) * m⁻¹ := by rw [h1]
      _ = m * c * m⁻¹ * (m * q * m⁻¹) := by group

theorem isL34Two_map_conj {G : Type} [Group G] {Q : Subgroup G} (h : IsL34Two ↥Q) (m : G) :
    IsL34Two ↥(Q.map (MulAut.conj m).toMonoidHom) := by
  obtain ⟨e⟩ := h
  exact ⟨(Subgroup.equivMapOfInjective Q (MulAut.conj m).toMonoidHom
    (MulAut.conj m).injective).symm.trans e⟩

theorem card_UT3_F4 : Nat.card (UT3 F4) = 64 := by
  have e : UT3 F4 ≃ F4 × F4 × F4 :=
    { toFun := fun x => (x.a, x.b, x.c)
      invFun := fun t => ⟨t.1, t.2.1, t.2.2⟩
      left_inv := fun x => rfl
      right_inv := fun t => rfl }
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_prod, CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic.card_F4]

theorem exists_hom_of_quotIso {G : Type} [Group G] {C N : Subgroup G} {P : Type} [Group P]
    (h : QuotIso C N P) : ∃ φ : ↥C →* P, φ.ker = N.subgroupOf C := by
  obtain ⟨hn, ⟨e⟩⟩ := h
  refine ⟨(e : ↥C ⧸ N.subgroupOf C →* P).comp (QuotientGroup.mk' (N.subgroupOf C)), ?_⟩
  rw [MonoidHom.ker_mulEquiv_comp, QuotientGroup.ker_mk']

theorem l34_of_lemma29b {G : Type} [Group G] [Finite G] {U W X : Subgroup G} {p : ℕ}
    (hp : p.Prime) (hodd : p ≠ 2)
    (hU4 : IVK.IsFourSubgroup U)
    (hW2 : IsPGroup 2 ↥W) (hXp : IsPGroup p ↥X) (hXW : X ≤ normalizer (W : Set G))
    (hWX : ⁅W, X⁆ = W) (hWne : W ≠ ⊥)
    (hUW : U ≤ W) (hUZ : U ≤ centralizer (W : Set G)) (hXU : X ≤ centralizer (U : Set G))
    (hZfix : W ⊓ centralizer (W : Set G) = W ⊓ centralizer (X : Set G))
    (hZder : W ⊓ centralizer (W : Set G) = ⁅W, W⁆)
    (h29 : Lemma29b U) :
    p = 3 ∧ IsL34Two ↥W ∧ (centralizer (W : Set G)).relIndex X = 3 ∧
      W ⊓ centralizer (W : Set G) = U ∧
      IsSylowOf 2 U (centralizer (W : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, Xg, v, hQsyl, hv, ⟨x, hXg, hXg3, hxN, hx3⟩, hdec, hQXg, hQL34, hQC, hUsyl, hquot⟩ :=
    h29
  set C := centralizer (U : Set G) with hC
  have hWC : W ≤ C := by
    intro w hw
    show w ∈ centralizer (U : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact (Subgroup.mem_centralizer_iff.mp (hUZ hu) w hw).symm
  have hXC : X ≤ C := hXU
  obtain ⟨P, _, φ, hP3, hφ⟩ : ∃ (P : Type) (_ : Group P) (φ : ↥C →* P), OddThree P ∧
      φ.ker = (O22Of C).subgroupOf C := by
    rcases hquot with h | h
    · obtain ⟨φ, hφ⟩ := exists_hom_of_quotIso h
      exact ⟨_, inferInstance, φ, oddThree_mulZMod3, hφ⟩
    · obtain ⟨φ, hφ⟩ := exists_hom_of_quotIso h
      exact ⟨_, inferInstance, φ, oddThree_perm3, hφ⟩
  have hW₁2 : IsPGroup 2 ↥(W.subgroupOf C) := hW2.comap_subtype
  have hX₁p : IsPGroup p ↥(X.subgroupOf C) := hXp.comap_subtype
  have hcomm₁ : ⁅W.subgroupOf C, X.subgroupOf C⁆ = W.subgroupOf C := by
    apply Subgroup.map_injective C.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_of_le_left hWC, inf_of_le_left hXC, hWX]
  obtain ⟨hWker, hXidx⟩ := two_p_image_of_oddThree hP3 φ hp hodd hW₁2 hX₁p hcomm₁
  rw [hφ] at hWker hXidx
  have hWM : W ≤ O22Of C := fun w hw =>
    Subgroup.mem_subgroupOf.mp (hWker (show (⟨w, hWC hw⟩ : ↥C) ∈ W.subgroupOf C from hw))
  have hXidx' : (O22Of C).relIndex X ∣ 3 := by
    have h1 := Subgroup.relIndex_subgroupOf (H := O22Of C) hXC
    rw [← h1]
    exact hXidx

  have hOodd : Odd (Nat.card ↥(pPrimeCoreOf 2 C)) := by
    unfold pPrimeCoreOf
    rw [Subgroup.card_map_of_injective C.subtype_injective]
    have := Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := ↥C))
    exact this
  have hOnorm : ∀ c ∈ C, ∀ o ∈ pPrimeCoreOf 2 C, c * o * c⁻¹ ∈ pPrimeCoreOf 2 C := by
    intro c hc o ho
    obtain ⟨o₁, ho₁, rfl⟩ := Subgroup.mem_map.mp ho
    have h1 := (inferInstance : (pPrimeCore 2 ↥C).Normal).conj_mem o₁ ho₁ ⟨c, hc⟩
    exact Subgroup.mem_map.mpr ⟨_, h1, by simp⟩
  have hWO : W ⊓ pPrimeCoreOf 2 C = ⊥ := isPGroup_two_inf_eq_bot_of_odd W _ hW2 hOodd
  have hXMO : ∀ y ∈ X, y ∈ O22Of C → y ∈ pPrimeCoreOf 2 C := by
    intro y hyX hyM
    obtain ⟨y₁, hy₁, rfl⟩ := Subgroup.mem_map.mp hyM
    have hord : Odd (orderOf (y₁ : G)) := odd_orderOf_of_isPGroup hp hodd hXp hyX
    have hord1 : Odd (orderOf y₁) := by rwa [Subgroup.orderOf_coe] at hord
    have h2 : IsPGroup 2 ↥(pCore 2 (↥C ⧸ pPrimeCore 2 ↥C)) := pCore_isPGroup
    have hz : (QuotientGroup.mk' (pPrimeCore 2 ↥C) y₁) ∈ pCore 2 (↥C ⧸ pPrimeCore 2 ↥C) := hy₁
    obtain ⟨k, hk⟩ := orderOf_eq_two_pow_of_isPGroup h2 hz
    have hd : orderOf (QuotientGroup.mk' (pPrimeCore 2 ↥C) y₁) ∣ orderOf y₁ :=
      orderOf_map_dvd _ y₁
    have hd2 : orderOf (QuotientGroup.mk' (pPrimeCore 2 ↥C) y₁) ∣ 2 ^ k := hk ▸ dvd_rfl
    have hcop : Nat.Coprime (2 ^ k) (orderOf y₁) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hord1)
    have h1 : orderOf (QuotientGroup.mk' (pPrimeCore 2 ↥C) y₁) = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop hd2 hd
    have h3 := orderOf_eq_one_iff.mp h1
    have h4 : y₁ ∈ pPrimeCore 2 ↥C := (QuotientGroup.eq_one_iff y₁).mp h3
    exact Subgroup.mem_map.mpr ⟨y₁, h4, rfl⟩
  have hXMc : ∀ y ∈ X, y ∈ O22Of C → y ∈ centralizer (W : Set G) := by
    intro y hyX hyM
    have hyO := hXMO y hyX hyM
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hyW : y * w * y⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (hXW hyX) w).mp hw
    have h1 : y * w * y⁻¹ * w⁻¹ ∈ W := W.mul_mem hyW (W.inv_mem hw)
    have h2 : y * w * y⁻¹ * w⁻¹ ∈ pPrimeCoreOf 2 C := by
      have := (pPrimeCoreOf 2 C).mul_mem hyO
        (hOnorm w (hWC hw) y⁻¹ ((pPrimeCoreOf 2 C).inv_mem hyO))
      have e : y * (w * y⁻¹ * w⁻¹) = y * w * y⁻¹ * w⁻¹ := by group
      rwa [e] at this
    have h3 : y * w * y⁻¹ * w⁻¹ ∈ W ⊓ pPrimeCoreOf 2 C := Subgroup.mem_inf.mpr ⟨h1, h2⟩
    rw [hWO, Subgroup.mem_bot] at h3
    have h4 : y * w = w * y := commutatorElement_eq_one_iff_mul_comm.mp h3
    exact h4.symm
  have hrel3 : (centralizer (W : Set G)).relIndex X ∣ 3 := by
    refine Nat.dvd_trans ?_ hXidx'
    rw [← Subgroup.inf_relIndex_right (centralizer (W : Set G)) X,
      ← Subgroup.inf_relIndex_right (O22Of C) X]
    apply Subgroup.relIndex_dvd_of_le_left
    intro y hy
    exact Subgroup.mem_inf.mpr ⟨hXMc y (Subgroup.mem_inf.mp hy).2 (Subgroup.mem_inf.mp hy).1,
      (Subgroup.mem_inf.mp hy).2⟩
  have hrel_ne : (centralizer (W : Set G)).relIndex X ≠ 1 := by
    intro h1
    have hXle : X ≤ centralizer (W : Set G) := Subgroup.relIndex_eq_one.mp h1
    apply hWne
    rw [← hWX, Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hXle
  have hrel : (centralizer (W : Set G)).relIndex X = 3 :=
    ((Nat.dvd_prime Nat.prime_three).mp hrel3).resolve_left hrel_ne
  have hp3 : p = 3 := by
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨n, hn⟩ := hXp.exists_card_eq
    have h3 : 3 ∣ Nat.card ↥X := hrel ▸ Subgroup.relIndex_dvd_card (centralizer (W : Set G)) X
    rw [hn] at h3
    exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)).symm
  obtain ⟨m, hmM, hWQ⟩ := exists_conj_le_of_isSylowOf hQsyl hWM hW2
  have hmC : m ∈ C := Subgroup.map_subtype_le _ hmM
  set Q₂ : Subgroup G := Q.map (MulAut.conj m).toMonoidHom with hQ₂
  have hconj_U : ∀ u ∈ U, m * u * m⁻¹ = u := fun u hu => by
    have h1 : u * m = m * u := Subgroup.mem_centralizer_iff.mp hmC u hu
    rw [← h1]
    group
  have hUQ : U ≤ Q := hQC ▸ inf_le_left
  have hUQc : U ≤ centralizer (Q : Set G) := hUsyl.le
  have hUQ₂ : U ≤ Q₂ := fun u hu =>
    Subgroup.mem_map.mpr ⟨u, hUQ hu, by simpa [MulAut.conj_apply] using hconj_U u hu⟩
  have hUQ₂c : U ≤ centralizer (Q₂ : Set G) := by
    rw [hQ₂, centralizer_map_conj]
    intro u hu
    exact Subgroup.mem_map.mpr ⟨u, hUQc hu, by simpa [MulAut.conj_apply] using hconj_U u hu⟩
  have hQ₂L34 : IsL34Two ↥Q₂ := isL34Two_map_conj hQL34 m
  let e : ↥Q₂ ≃* UT3 F4 := hQ₂L34.some
  have hQ₂card : Nat.card ↥Q₂ = 64 := by rw [Nat.card_congr e.toEquiv, card_UT3_F4]
  have hU4card : Nat.card ↥U = 4 := hU4.2
  obtain ⟨hcomm, -⟩ := CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic.comm_central_of_equiv e hUQ₂ hU4card
    (fun y hy w hw => by
      have h1 : y * w = w * y := Subgroup.mem_centralizer_iff.mp (hUQ₂c hw) y hy
      have : y * w * y⁻¹ = w := by rw [h1]; group
      rw [this]
      exact hw)
  have hderU : ⁅W, W⁆ ≤ U := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    exact hcomm a (hWQ ha) b (hWQ hb)
  have hZU : W ⊓ centralizer (W : Set G) = U := by
    apply le_antisymm
    · rw [hZder]; exact hderU
    · exact le_inf hUW hUZ
  subst hp3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmod := card_modEq_centralizer (W := W) (X := X) hXp hXW
  rw [← hZfix, hZU, hU4card] at hmod
  obtain ⟨j, hj⟩ := hW2.exists_card_eq
  have hjdvd : 2 ^ j ∣ 2 ^ 6 := by
    have := Subgroup.card_dvd_of_le hWQ
    rw [hj, hQ₂card] at this
    simpa using this
  have hj6 : j ≤ 6 := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hjdvd
  have hUdvd : 2 ^ 2 ∣ 2 ^ j := by
    have := Subgroup.card_dvd_of_le hUW
    rw [hj, hU4card] at this
    simpa using this
  have hj2 : 2 ≤ j := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hUdvd
  rw [hj] at hmod
  have hWQeq : W = Q₂ := by
    have hj6' : j = 6 := by
      interval_cases j
      · exfalso
        have hcard : Nat.card ↥W ≤ Nat.card ↥U := by rw [hj, hU4card]; norm_num
        have hUW' : U = W := Subgroup.eq_of_le_of_card_ge hUW hcard
        apply hrel_ne
        apply Subgroup.relIndex_eq_one.mpr
        rw [← hUW']
        exact hXU
      · exfalso
        simp [Nat.ModEq] at hmod
      · exfalso
        have hder : ⁅W, W⁆ ≤ W ⊓ centralizer (W : Set G) := hZder.symm.le
        have hidx : Nat.card ↥W = 4 * Nat.card ↥(W ⊓ centralizer (W : Set G)) := by
          rw [hj, hZU, hU4card]; norm_num
        have h2 := card_derived_le_two W hder hidx
        have : ⁅W, W⁆ = U := hZder.symm.trans hZU
        rw [this, hU4card] at h2
        omega
      · exfalso
        simp [Nat.ModEq] at hmod
      · rfl
    exact (Subgroup.eq_of_le_of_card_ge hWQ (by rw [hj, hj6', hQ₂card]; norm_num))
  refine ⟨rfl, ?_, hrel, hZU, ?_⟩
  · rw [hWQeq]; exact hQ₂L34
  · have h1 := isSylowOf_map_conj hUsyl m
    have hUmap : U.map (MulAut.conj m).toMonoidHom = U := by
      ext u
      constructor
      · rintro ⟨u', hu', rfl⟩
        simpa [MulAut.conj_apply, hconj_U u' hu'] using hu'
      · intro hu
        exact Subgroup.mem_map.mpr ⟨u, hu, by simpa [MulAut.conj_apply] using hconj_U u hu⟩
    rw [hUmap, ← centralizer_map_conj] at h1
    rw [hWQeq]
    exact h1

theorem lemma29_mcl_ly {G : Type} [Group G] [Finite G] {z : G} {k : Kind}
    (hL : Lemma29FirstAt z k)
    {U WG XG : Subgroup G} {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (hU : IVK.IsFourSubgroup U)
    (hW2 : IsPGroup 2 ↥WG) (hXp : IsPGroup p ↥XG) (hcomm : ⁅WG, XG⁆ = WG) (hne : WG ≠ ⊥)
    (hWC : WG ≤ centralizer (U : Set G)) (hXC : XG ≤ centralizer (U : Set G))
    (u v : G) (hu : u ∈ WG) (hv : v ∈ WG) (hu4 : orderOf u = 4) (hv4 : orderOf v = 4)
    (huv : u * v ≠ v * u) :
    (k = Kind.mcl ∨ k = Kind.ly) ∧ Lemma29b U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer (U : Set G) with hC
  have hAlt := hL U hU
  unfold Lemma29Alt at hAlt
  rcases hAlt with hN | ⟨-, hdih, -⟩ | ⟨hk, hb⟩
  · exfalso
    obtain ⟨N, hNC, hNn, hNodd, a, hNidx⟩ := hN
    have hXN : ∀ x ∈ XG, x ∈ N := by
      intro x hx
      have hxC : x ∈ C := hXC hx
      have h2 : IsPGroup 2 (↥C ⧸ N.subgroupOf C) := IsPGroup.of_card (n := a) hNidx
      obtain ⟨j, hj⟩ := IsPGroup.iff_orderOf.mp h2 (QuotientGroup.mk (⟨x, hxC⟩ : ↥C))
      have hd : orderOf (QuotientGroup.mk (⟨x, hxC⟩ : ↥C) : ↥C ⧸ N.subgroupOf C) ∣ orderOf x := by
        have := orderOf_map_dvd (QuotientGroup.mk' (N.subgroupOf C)) (⟨x, hxC⟩ : ↥C)
        rwa [Subgroup.orderOf_mk] at this
      have hodd' : Odd (orderOf x) := odd_orderOf_of_isPGroup hp hodd hXp hx
      have hcop : Nat.Coprime (2 ^ j) (orderOf x) :=
        Nat.Coprime.pow_left j (Nat.coprime_two_left.mpr hodd')
      have h1 : orderOf (QuotientGroup.mk (⟨x, hxC⟩ : ↥C) : ↥C ⧸ N.subgroupOf C) = 1 :=
        Nat.eq_one_of_dvd_coprimes hcop (hj ▸ dvd_rfl) hd
      have h3 := orderOf_eq_one_iff.mp h1
      exact (Subgroup.mem_subgroupOf).mp ((QuotientGroup.eq_one_iff _).mp h3)
    have hWN : WG ≤ N := by
      rw [← hcomm, Subgroup.commutator_le]
      intro w hw x hx
      have h1 : w * x * w⁻¹ ∈ N := by
        have := hNn.conj_mem (⟨x, hXC hx⟩ : ↥C) (Subgroup.mem_subgroupOf.mpr (hXN x hx))
          ⟨w, hWC hw⟩
        exact Subgroup.mem_subgroupOf.mp this
      exact N.mul_mem h1 (N.inv_mem (hXN x hx))
    have hbot : WG ⊓ N = ⊥ := isPGroup_two_inf_eq_bot_of_odd WG N hW2 hNodd
    apply hne
    rw [← inf_of_le_left hWN]
    exact hbot
  · exfalso
    have hXO : ∀ x ∈ XG, x ∈ O2Of C := fun x hx =>
      mem_O2Of_of_odd (hXC hx) (Nat.coprime_two_right.mpr (odd_orderOf_of_isPGroup hp hodd hXp hx))
    have hWO : WG ≤ O2Of C := by
      rw [← hcomm, Subgroup.commutator_le]
      intro a ha b hb
      have haC : a ∈ C := hWC ha
      have hbO : b ∈ O2Of C := hXO b hb
      show a * b * a⁻¹ * b⁻¹ ∈ O2Of C
      exact (O2Of C).mul_mem (mem_O2Of_conj haC hbO) ((O2Of C).inv_mem hbO)
    have hWsub : IsPGroup 2 ↥(WG.subgroupOf (O2Of C)) := hW2.comap_subtype
    obtain ⟨P, hP⟩ := hWsub.exists_le_sylow
    obtain ⟨m, k', -, -, ⟨e⟩⟩ := hdih P
    have hP' : ∀ w (hw : w ∈ WG), (⟨w, hWO hw⟩ : ↥(O2Of C)) ∈ (P : Subgroup ↥(O2Of C)) := by
      intro w hw
      exact hP (Subgroup.mem_subgroupOf.mpr hw)
    have hord : ∀ (w : G) (hw : w ∈ WG), orderOf w = 4 →
        orderOf (⟨⟨w, hWO hw⟩, hP' w hw⟩ : ↥P) = 4 := by
      intro w hw hw4
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hw4]
    have hcommP := dihedral_order_four_commute e (hord u hu hu4) (hord v hv hv4)
    apply huv
    have := congrArg (fun t : ↥P => (((t : ↥(O2Of C)) : G))) hcommP
    simpa using this
  · exact ⟨hk, hb⟩

end Basic

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
