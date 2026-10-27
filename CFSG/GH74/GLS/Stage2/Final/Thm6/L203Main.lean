module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L203MSide
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L203Aut
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L203Sect
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L203Conj
public import CFSG.GH74.GLS.Stage2.Final.Thm6.Lemmas1
import CFSG.GH74.GLS.Stage2.Local.P27.QIdArith
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L203Core

public section

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.GH74.GLS.Stage2.Local.P27 CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Final.Thm4
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L203

@[expose] def PSp4Facts : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (E : Subgroup G) (q : ℕ), Odd q → 5 ≤ q → IVK.IsPSp4 ↥E q →
    Group.IsSolvable (Outer ↥E) ∧
    ∀ t ∈ E, orderOf t = 2 →
      (∃ H Q8 : Subgroup G, H ≤ E ⊓ centralizer ({t} : Set G) ∧ Group.IsPerfect ↥H ∧
        pPrimeCore 2 ↥H = ⊥ ∧ Q8 ≤ H ∧ Nonempty (↥Q8 ≃* QuaternionGroup 2)) ∨
      (∃ I : Subgroup G, I ≤ E ⊓ centralizer ({t} : Set G) ∧ IVK.IsL2 ↥I (fun r => r = q) ∧
        ∀ N : Subgroup G, N ≤ E ⊓ centralizer ({t} : Set G) → ⁅N, N⁆ = N → N ≤ I)

@[expose] def L203Prop27 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G) (ε : Bool) (q : ℕ)
    (L₁ L₂ : Subgroup (CentralizerBar z)), Stage2Ctx G z (Kind.l4 ε) S → Stage1L4 G z S ε q L₁ L₂ →
      q % 4 = (if ε then 3 else 1) →
      ∃ x : G, orderOf x = 2 ∧ ¬ IsConj z x ∧ FullCL4 x q ∧ HasNormal2Compl (CxK x (Jx x))

section Abstract

theorem isPerfect_of_equiv {A B : Type} [Group A] [Group B] (e : A ≃* B) (h : Group.IsPerfect A) :
    Group.IsPerfect B :=
  Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective

theorem isSolvable_of_equiv' {A B : Type} [Group A] [Group B] (e : A ≃* B) (h : Group.IsSolvable A) :
    Group.IsSolvable B :=
  Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective

theorem eq_bot_of_normal_odd {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup Y]
    (hns : ¬ Group.IsSolvable Y) (N : Subgroup Y) [N.Normal] (hodd : Odd (Nat.card N)) : N = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hb | ht
  · exact hb
  · exfalso
    apply hns
    have : Odd (Nat.card Y) := by
      rw [← Subgroup.card_top (G := Y), ← ht]
      exact hodd
    exact CFSG.FeitThompson.isSolvable_of_odd_natCard _ this

theorem noOdd_of_simple {Z : Type} [Group Z] [Finite Z] (H : Subgroup Z) [IsSimpleGroup ↥H]
    (hns : ¬ Group.IsSolvable ↥H) :
    ∀ N : Subgroup Z, N ≤ H → (N.subgroupOf H).Normal → Odd (Nat.card ↥N) → N = ⊥ := by
  intro N hNH hNn hodd
  have h1 : Odd (Nat.card ↥(N.subgroupOf H)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv]
    exact hodd
  have h2 := eq_bot_of_normal_odd hns (N.subgroupOf H) h1
  rw [eq_bot_iff]
  intro n hn
  have : (⟨n, hNH hn⟩ : ↥H) ∈ N.subgroupOf H := hn
  rw [h2, Subgroup.mem_bot] at this
  exact Subgroup.mem_bot.2 (congrArg Subtype.val this)

theorem noOdd_of_pPrimeCore_eq_bot {Z : Type} [Group Z] [Finite Z] (H : Subgroup Z)
    (h : pPrimeCore 2 ↥H = ⊥) :
    ∀ N : Subgroup Z, N ≤ H → (N.subgroupOf H).Normal → Odd (Nat.card ↥N) → N = ⊥ := by
  intro N hNH hNn hodd
  have h1 : Odd (Nat.card ↥(N.subgroupOf H)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv]
    exact hodd
  have h2 : N.subgroupOf H ≤ pPrimeCore 2 ↥H := le_sSup ⟨hNn, Nat.coprime_two_left.2 h1⟩
  rw [h] at h2
  rw [eq_bot_iff]
  intro n hn
  have : (⟨n, hNH hn⟩ : ↥H) ∈ N.subgroupOf H := hn
  have := h2 this
  rw [Subgroup.mem_bot] at this
  exact Subgroup.mem_bot.2 (congrArg Subtype.val this)

theorem not_isSolvable_of_isL2 {X : Type} [Group X] {q : ℕ} (hq : Odd q) (hq5 : 5 ≤ q)
    (h : IVK.IsL2 X (fun r => r = q)) : ¬ Group.IsSolvable X := by
  intro hsolv
  have hs : IsSimpleGroup X := Prop28.isSimpleGroup_of_isL2 (by omega) h
  have hcomm : ∀ a b : X, a * b = b * a := IsSimpleGroup.comm_iff_isSolvable.2 hsolv
  have hcard := Stage2.Local.P27.QId.card_isL2 hq h
  have : Finite X := by
    obtain ⟨F, _, hF, -, ⟨e⟩⟩ := h
    exact Finite.of_equiv _ e.toEquiv.symm
  have hprime : Nat.Prime (Nat.card X) := by
    let : CommGroup X := { ‹Group X› with mul_comm := hcomm }
    exact IsSimpleGroup.prime_card
  obtain ⟨a, ha⟩ : ∃ a, q ^ 2 = 2 * a + 1 := by
    obtain ⟨a, ha⟩ := hq.pow (n := 2)
    exact ⟨a, ha⟩
  have h1 : q ^ 2 - 1 = 2 * a := by omega
  rw [h1, show q * (2 * a) / 2 = q * a by rw [mul_left_comm, Nat.mul_div_cancel_left _ two_pos]] at hcard
  have hqa : q ∣ Nat.card X := ⟨a, hcard⟩
  rcases (Nat.dvd_prime hprime).1 hqa with h5 | h5
  · omega
  · have : q * a = q * 1 := by rw [← hcard, h5]; ring
    have ha1 : a = 1 := Nat.eq_of_mul_eq_mul_left (by omega) this
    nlinarith

end Abstract

section XLevel

variable {G : Type} [Group G]

theorem inf_O_eq_one [Finite G] {t : G} {IX : Subgroup ↥(centralizer ({t} : Set G))}
    (hIodd : ∀ N : Subgroup ↥(centralizer ({t} : Set G)), N ≤ IX → (N.subgroupOf IX).Normal →
      Odd (Nat.card ↥N) → N = ⊥) :
    ∀ i ∈ IX, i ∈ OX t → i = 1 := by
  intro i hi hiO
  have hN : ((IX ⊓ OX t).subgroupOf IX).Normal := by
    rw [Subgroup.inf_subgroupOf_left]
    exact Subgroup.Normal.subgroupOf inferInstance _
  have hodd : Odd (Nat.card ↥(IX ⊓ OX t)) :=
    Odd.of_dvd_nat (OX_odd t) (Subgroup.card_dvd_of_le inf_le_right)
  have := hIodd (IX ⊓ OX t) inf_le_left hN hodd
  have hmem : i ∈ IX ⊓ OX t := Subgroup.mem_inf.2 ⟨hi, hiO⟩
  rw [this, Subgroup.mem_bot] at hmem
  exact hmem

theorem odd_toX [Finite G] {t : G} {H : Subgroup G} (hHC : H ≤ centralizer ({t} : Set G))
    (hHodd : ∀ N : Subgroup G, N ≤ H → (N.subgroupOf H).Normal → Odd (Nat.card ↥N) → N = ⊥) :
    ∀ N : Subgroup ↥(centralizer ({t} : Set G)), N ≤ H.subgroupOf (centralizer ({t} : Set G)) →
      (N.subgroupOf (H.subgroupOf (centralizer ({t} : Set G)))).Normal → Odd (Nat.card ↥N) → N = ⊥ := by
  intro N hNH hNn hodd
  obtain ⟨N', hN'⟩ : ∃ N' : Subgroup G, N' = N.map (centralizer ({t} : Set G)).subtype := ⟨_, rfl⟩
  have hN'H : N' ≤ H := by
    rw [hN']
    rintro _ ⟨n, hn, rfl⟩
    exact hNH hn
  have hN'n : (N'.subgroupOf H).Normal := by
    refine ⟨fun a ha h => ?_⟩
    have ha' : (a : G) ∈ N' := ha
    rw [hN'] at ha'
    obtain ⟨n, hn, hna⟩ := ha'
    have hhC : (h : G) ∈ centralizer ({t} : Set G) := hHC h.2
    have h1 := hNn.conj_mem (⟨n, hNH hn⟩ : ↥(H.subgroupOf (centralizer ({t} : Set G))))
      (Subgroup.mem_subgroupOf.2 hn) ⟨⟨(h : G), hhC⟩, h.2⟩
    have h2 := Subgroup.mem_subgroupOf.1 h1
    refine Subgroup.mem_subgroupOf.2 ?_
    rw [hN']
    refine ⟨_, h2, ?_⟩
    show (h : G) * (n : G) * (h : G)⁻¹ = (h : G) * (a : G) * (h : G)⁻¹
    rw [← hna]
    rfl
  have hodd' : Odd (Nat.card ↥N') := by
    rw [hN', Subgroup.card_map_of_injective (centralizer ({t} : Set G)).subtype_injective]
    exact hodd
  have hbot := hHodd N' hN'H hN'n hodd'
  rw [eq_bot_iff]
  intro n hn
  have : (n : G) ∈ N' := by rw [hN']; exact ⟨n, hn, rfl⟩
  rw [hbot, Subgroup.mem_bot] at this
  exact Subgroup.mem_bot.2 (Subtype.ext this)

end XLevel

section Arith

theorem card_L2_sq_not_dvd {q : ℕ} (hq : Odd q) (hq5 : 5 ≤ q) :
    ¬ (q ^ 2 * ((q ^ 2) ^ 2 - 1) / 2) ∣ (q * (q ^ 2 - 1) / 2) := by
  intro h
  obtain ⟨a, ha⟩ : ∃ a, q ^ 2 = 2 * a + 1 := by
    obtain ⟨a, ha⟩ := hq.pow (n := 2)
    exact ⟨a, ha⟩
  have h1 : q ^ 2 - 1 = 2 * a := by omega
  have h2 : (q ^ 2) ^ 2 - 1 = 2 * (2 * a * a + 2 * a) := by
    rw [ha]
    have : (2 * a + 1) ^ 2 = 2 * (2 * a * a + 2 * a) + 1 := by ring
    omega
  have hA : q * (q ^ 2 - 1) / 2 = q * a := by
    rw [h1, mul_left_comm, Nat.mul_div_cancel_left _ two_pos]
  have hB : q ^ 2 * ((q ^ 2) ^ 2 - 1) / 2 = q ^ 2 * (2 * a * a + 2 * a) := by
    rw [h2, mul_left_comm, Nat.mul_div_cancel_left _ two_pos]
  rw [hA, hB] at h
  have hapos : 0 < a := by nlinarith
  have hpos : 0 < q * a := Nat.mul_pos (by omega) hapos
  have hle := Nat.le_of_dvd hpos h
  have hq2 : q < q ^ 2 := by nlinarith
  have : q * a < q ^ 2 * (2 * a * a + 2 * a) := by
    calc q * a < q ^ 2 * a := Nat.mul_lt_mul_of_pos_right hq2 hapos
      _ ≤ q ^ 2 * (2 * a * a + 2 * a) := Nat.mul_le_mul_left _ (by nlinarith)
  omega

theorem card_A7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  decide

end Arith

section TypeAB

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem not_solvable_Kb {t : G} {IX : Subgroup ↥(centralizer ({t} : Set G))}
    (hIK : IX ≤ KX t) (hIO : ∀ i ∈ IX, i ∈ OX t → i = 1) (hIns : ¬ Group.IsSolvable ↥IX) :
    ¬ Group.IsSolvable ↥((KX t).map (QuotientGroup.mk' (OX t))) := by
  intro hsolv
  let f : ↥IX →* ↥((KX t).map (QuotientGroup.mk' (OX t))) :=
    ((QuotientGroup.mk' (OX t)).comp IX.subtype).codRestrict _ (fun i => ⟨i, hIK i.2, rfl⟩)
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro i hi
    have h1 : QuotientGroup.mk' (OX t) (i : ↥(centralizer ({t} : Set G))) = 1 := congrArg Subtype.val hi
    have : (i : ↥(centralizer ({t} : Set G))) ∈ OX t := (QuotientGroup.eq_one_iff _).1 h1
    exact Subtype.ext (hIO i i.2 this)
  exact hIns (Group.isSolvable_of_isSolvable_injective hf)

theorem not_dvd_card_of_fullCL4 {t : G} {q : ℕ} (hq : Odd q) (hq5 : 5 ≤ q) (hc : FullCL4 t q)
    {I : Subgroup G} (hIL2 : IVK.IsL2 ↥I (fun r => r = q)) :
    ¬ Nat.card ↥((KX t).map (QuotientGroup.mk' (OX t))) ∣ Nat.card ↥I := by
  obtain ⟨e⟩ := KXb_equiv t
  have hK : Nat.card ↥((KX t).map (QuotientGroup.mk' (OX t))) = Nat.card (↥(Jx t) ⧸ pPrimeCore 2 ↥(Jx t)) :=
    Nat.card_congr e.toEquiv
  have hI : Nat.card ↥I = q * (q ^ 2 - 1) / 2 := Stage2.Local.P27.QId.card_isL2 hq hIL2
  rw [hK, hI]
  rcases hc with hL2 | ⟨hq5', ⟨f⟩⟩
  · rw [Stage2.Local.P27.QId.card_isL2 (hq.pow (n := 2)) hL2]
    exact card_L2_sq_not_dvd hq hq5
  · subst hq5'
    rw [Nat.card_congr f.toEquiv, card_A7]
    norm_num

theorem typeA_false {t : G} {q : ℕ}
    (hq : Odd q) (hq5 : 5 ≤ q) (hc : FullCL4 t q) (he : HasNormal2Compl (CxK t (Jx t)))
    {H Q8 : Subgroup G} (hHC : H ≤ centralizer ({t} : Set G)) (hHp : Group.IsPerfect ↥H)
    (hHp2 : pPrimeCore 2 ↥H = ⊥)
    (hQ8H : Q8 ≤ H) (hQ8 : Nonempty (↥Q8 ≃* QuaternionGroup 2)) : False := by
  have hHodd := noOdd_of_pPrimeCore_eq_bot H hHp2
  have hKn : (KX t).Normal := KX_normal t
  obtain ⟨-, hOut⟩ := KXb_simple_outer (by omega) hc
  have hCs := Ctil_solvable t he
  have hHXp : Group.IsPerfect ↥(H.subgroupOf (centralizer ({t} : Set G))) :=
    isPerfect_of_equiv (Subgroup.subgroupOfEquivOfLe hHC).symm hHp
  have hHK : H.subgroupOf (centralizer ({t} : Set G)) ≤ KX t :=
    perfect_le_of_outer_solvable hHXp hOut hCs
  have hHO := inf_O_eq_one (odd_toX hHC hHodd)
  have hQ8X : Q8.subgroupOf (centralizer ({t} : Set G)) ≤ H.subgroupOf (centralizer ({t} : Set G)) :=
    fun x hx => hQ8H hx
  obtain ⟨f⟩ := hQ8
  have hQ8C : Q8 ≤ centralizer ({t} : Set G) := hQ8H.trans hHC
  exact false_of_quaternion hq hc hHK hHO hQ8X ⟨(Subgroup.subgroupOfEquivOfLe hQ8C).trans f⟩

theorem odd_card_of_isPGroup {Z : Type} [Group Z] [Finite Z] {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (h : IsPGroup r Z) : Odd (Nat.card Z) := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨n, hn⟩ := h.exists_card_eq
  rw [hn]
  exact (hr.odd_of_ne_two hr2).pow

theorem typeB_false {t : G} {q : ℕ}
    (hq : Odd q) (hq5 : 5 ≤ q) (hc : FullCL4 t q) (he : HasNormal2Compl (CxK t (Jx t)))
    {M E I Q : Subgroup G}
    (hEn : ∀ m ∈ M, ∀ e ∈ E, m * e * m⁻¹ ∈ E) (htE : t ∈ E)
    (hZ : ∀ z ∈ E, (∀ e ∈ E, z * e = e * z) → z = 1)
    (hB : Group.IsSolvable ↥(M ⊓ centralizer (E : Set G)))
    (hOutE : Group.IsSolvable (Outer ↥E))
    (hIle : I ≤ E ⊓ centralizer ({t} : Set G)) (hIL2 : IVK.IsL2 ↥I (fun r => r = q))
    (hIP : ∀ N : Subgroup G, N ≤ E ⊓ centralizer ({t} : Set G) → ⁅N, N⁆ = N → N ≤ I)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hQp : IsPGroup r ↥Q)
    (hQE : ∀ e ∈ E, ∀ y ∈ Q, e * y = y * e)
    (hCQ : ∀ x : G, (∀ y ∈ Q, x * y = y * x) → x ∈ M) : False := by
  have hKn : (KX t).Normal := KX_normal t
  obtain ⟨hKs, hOut⟩ := KXb_simple_outer (by omega) hc
  have hCs := Ctil_solvable t he
  have hIC : I ≤ centralizer ({t} : Set G) := fun i hi => (Subgroup.mem_inf.1 (hIle hi)).2
  have hIE : I ≤ E := fun i hi => (Subgroup.mem_inf.1 (hIle hi)).1
  have hQC : Q ≤ centralizer ({t} : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hQE t htE y hy).symm
  have hIsimple : IsSimpleGroup ↥I := Prop28.isSimpleGroup_of_isL2 (by omega) hIL2
  have hInsI : ¬ Group.IsSolvable ↥I := not_isSolvable_of_isL2 hq hq5 hIL2
  let eI : ↥(I.subgroupOf (centralizer ({t} : Set G))) ≃* ↥I := Subgroup.subgroupOfEquivOfLe hIC
  have hIXs : IsSimpleGroup ↥(I.subgroupOf (centralizer ({t} : Set G))) :=
    eI.isSimpleGroup_congr.2 hIsimple
  have hIXns : ¬ Group.IsSolvable ↥(I.subgroupOf (centralizer ({t} : Set G))) :=
    fun h => hInsI (isSolvable_of_equiv' eI h)
  have hIXp : Group.IsPerfect ↥(I.subgroupOf (centralizer ({t} : Set G))) :=
    isPerfect_of_simple_nonsolvable hIXns
  have hIodd := noOdd_of_simple (I.subgroupOf (centralizer ({t} : Set G))) hIXns
  have hIO := inf_O_eq_one hIodd
  have hIK := perfect_le_of_outer_solvable hIXp hOut hCs
  have hQXp : IsPGroup r ↥(Q.subgroupOf (centralizer ({t} : Set G))) :=
    hQp.of_surjective (Subgroup.subgroupOfEquivOfLe hQC).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hQC).symm.surjective
  have hQXodd : Odd (Nat.card ↥(Q.subgroupOf (centralizer ({t} : Set G)))) :=
    odd_card_of_isPGroup hr hr2 hQXp
  have hIQ : ∀ i ∈ I.subgroupOf (centralizer ({t} : Set G)), ∀ y ∈ Q.subgroupOf (centralizer ({t} : Set G)),
      i * y = y * i := by
    intro i hi y hy
    apply Subtype.ext
    exact hQE (i : G) (hIE hi) (y : G) hy
  have hIL2X : IVK.IsL2 ↥(I.subgroupOf (centralizer ({t} : Set G))) (fun r => r = q) := by
    obtain ⟨F₀, i1, i2, hP, ⟨e₀⟩⟩ := hIL2
    exact ⟨F₀, i1, i2, hP, ⟨eI.trans e₀⟩⟩
  have hstep := stepA_of_fullCL4 hq hq5 hc hIK hIO hIQ hQXodd (Or.inl hIL2X)
  have hQO : Q.subgroupOf (centralizer ({t} : Set G)) ≤ OX t := le_OX_of_le_Ctil he hstep hQXodd
  have hCQX : ∀ x : ↥(centralizer ({t} : Set G)), (∀ y ∈ Q.subgroupOf (centralizer ({t} : Set G)), x * y = y * x) →
      x ∈ (M ⊓ centralizer ({t} : Set G)).subgroupOf (centralizer ({t} : Set G)) := by
    intro x hx
    have hxM : (x : G) ∈ M := hCQ x (fun y hy => by
      have := hx ⟨y, hQC hy⟩ hy
      exact congrArg Subtype.val this)
    exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨hxM, x.2⟩)
  have hIperfG : ⁅I, I⁆ = I := by
    have : Group.IsPerfect ↥I := isPerfect_of_simple_nonsolvable hInsI
    exact Subgroup.isPerfect_iff.1 this
  have hIMn : ∀ m ∈ (M ⊓ centralizer ({t} : Set G)).subgroupOf (centralizer ({t} : Set G)),
      ∀ i ∈ I.subgroupOf (centralizer ({t} : Set G)), m * i * m⁻¹ ∈ I.subgroupOf (centralizer ({t} : Set G)) := by
    intro m hm i hi
    have hmM : (m : G) ∈ M := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hm)).1
    have hmC : (m : G) ∈ centralizer ({t} : Set G) := m.2
    obtain ⟨I', hI'⟩ : ∃ I' : Subgroup G, I' = I.map (MulAut.conj (m : G)).toMonoidHom := ⟨_, rfl⟩
    have hI'le : I' ≤ E ⊓ centralizer ({t} : Set G) := by
      rw [hI']
      rintro _ ⟨j, hj, rfl⟩
      refine Subgroup.mem_inf.2 ⟨hEn _ hmM _ (hIE hj), ?_⟩
      exact (centralizer ({t} : Set G)).mul_mem
        ((centralizer ({t} : Set G)).mul_mem hmC (hIC hj)) ((centralizer ({t} : Set G)).inv_mem hmC)
    have hI'perf : ⁅I', I'⁆ = I' := by
      rw [hI', ← Subgroup.map_commutator, hIperfG]
    have hI'I : I' ≤ I := hIP I' hI'le hI'perf
    have hmem : (m : G) * (i : G) * (m : G)⁻¹ ∈ I' := by
      rw [hI']
      exact ⟨(i : G), Subgroup.mem_subgroupOf.1 hi, rfl⟩
    exact Subgroup.mem_subgroupOf.2 (hI'I hmem)
  have hnsK := not_solvable_Kb hIK hIO hIXns
  have hcard := not_dvd_card_of_fullCL4 hq hq5 hc hIL2
  have hsec := hsec_of_perfect hEn htE hZ hB hOutE (S := ↥((KX t).map (QuotientGroup.mk' (OX t)))) hnsK hIP hcard
  exact core_false hr hr2 (OX_odd t) hKs hOut hCs hQXp hQO hCQX hIXp hIodd hIXns hIQ hIMn hsec

end TypeAB

section Final

variable {G : Type} [Group G] [Finite G]

theorem pPrimeCoreOf_solvable (M : Subgroup G) : Group.IsSolvable ↥(pPrimeCoreOf 2 M) := by
  have hodd : Odd (Nat.card ↥(pPrimeCore 2 ↥M)) :=
    Nat.coprime_two_left.1 (pPrimeCore_coprime_card (p := 2) (G := ↥M))
  have : Odd (Nat.card ↥(pPrimeCoreOf 2 M)) := by
    show Odd (Nat.card ↥((pPrimeCore 2 ↥M).map M.subtype))
    rwa [Subgroup.card_map_of_injective M.subtype_injective]
  exact CFSG.FeitThompson.isSolvable_of_odd_natCard _ this

end Final

theorem lemma20_3_of_parts
    (h34 : Leaf_Prop34) (h27 : L203Prop27) (hPS : PSp4Facts) : Lemma20_3 := by
  intro G _ _ z k S M h
  by_contra hne
  obtain ⟨ε, q, L₁, L₂, hk, hL4, hmod, hq3, hMS⟩ := mside h34 h hne
  subst hk
  obtain ⟨x, hx2, hxz, hc, he⟩ := h27 G z S ε q L₁ L₂ h.ctx.ctx17.ctx hL4 hmod
  obtain ⟨t, ht2, htz, htE, hclass⟩ := hMS.invol
  obtain ⟨g, hg⟩ := isConj_iff.1 (hclass x hx2 hxz).symm
  have hct : FullCL4 t q := hg ▸ fullCL4_conj g hc
  have het : HasNormal2Compl (CxK t (Jx t)) := hg ▸ hasNormal2Compl_CxK_conj g he
  have hq : Odd q := hL4.pair.odd
  have hq5 : 5 ≤ q := by
    obtain ⟨m, hm⟩ := hq
    omega
  obtain ⟨hOutE, hdich⟩ := hPS G (Em M) q hq hq5 hMS.psp4
  rcases hdich t htE ht2 with ⟨H, Q8, hHle, hHp, hHodd, hQ8H, hQ8⟩ | ⟨I, hIle, hIL2, hIP⟩
  · exact typeA_false hq hq5 hct het (fun h' hh => (Subgroup.mem_inf.1 (hHle hh)).2) hHp hHodd
      hQ8H hQ8
  · obtain ⟨r, Q, hr, hr2, hQA, hQp, hQ1, hQn, hCQ⟩ := hMS.normal
    obtain ⟨hES, hEP⟩ := isSimple_isPerfect_of_isPSp4 hq3 hMS.psp4
    have hEn' := exists_noncomm_of_simple_perfect hEP
    have hZ : ∀ z ∈ Em M, (∀ e ∈ Em M, z * e = e * z) → z = 1 := by
      intro z' hz hcomm
      have hcen : (⟨z', hz⟩ : ↥(Em M)) ∈ Subgroup.center ↥(Em M) := by
        rw [Subgroup.mem_center_iff]
        intro e
        exact (Subtype.ext (hcomm (e : G) e.2).symm)
      rw [center_eq_bot_of_simple hEn', Subgroup.mem_bot] at hcen
      exact congrArg Subtype.val hcen
    have hB : Group.IsSolvable ↥(M ⊓ centralizer ((Em M : Subgroup G) : Set G)) := by
      have hle : M ⊓ centralizer ((Em M : Subgroup G) : Set G) ≤ pPrimeCoreOf 2 M := by
        intro c hc
        obtain ⟨hcM, hcC⟩ := Subgroup.mem_inf.1 hc
        exact hMS.cent c hcM (fun e he => (Subgroup.mem_centralizer_iff.1 hcC e he).symm)
      have := pPrimeCoreOf_solvable M
      exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
    have hQE : ∀ e ∈ Em M, ∀ y ∈ Q, e * y = y * e := fun e he y hy => hMS.comm e he y (hQA hy)
    exact typeB_false hq hq5 hct het hMS.norm htE hZ hB hOutE hIle hIL2 hIP hr hr2 hQp hQE hCQ

end CFSG.GH74.GLS.Stage2.Final.Thm6.L203
