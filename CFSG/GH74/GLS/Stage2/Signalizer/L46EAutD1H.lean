module

public import CFSG.GH74.GLS.Stage2.Signalizer.L46EAutD1Core
public import CFSG.GH74.GLS.Stage2.Signalizer.L46EMain
public import CFSG.GH74.GLS.Stage2.Signalizer.L46ELayer

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.L46E

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

section Lift

variable {Hg : Type*} [Group Hg]

theorem lift_coprime {p : ℕ} [Fact p.Prime] {O N : Subgroup Hg} [O.Normal]
    (hO : IsPGroup p ↥O) (hNO : ⁅N, O⁆ = ⊥) {X' : Subgroup Hg} {ī : Hg ⧸ O}
    (hī : ī ∈ N.map (QuotientGroup.mk' O)) (hcop : Nat.Coprime (orderOf ī) p)
    (hcent : ∀ x ∈ X', QuotientGroup.mk' O x * ī = ī * QuotientGroup.mk' O x) :
    ∃ i ∈ N, QuotientGroup.mk' O i = ī ∧ ∀ x ∈ X', x * i = i * x := by
  classical
  obtain ⟨i₀, hi₀N, hi₀⟩ := Subgroup.mem_map.1 hī
  set m := orderOf ī with hm
  have hi₀m : i₀ ^ m ∈ O := by
    rw [← QuotientGroup.ker_mk' O, MonoidHom.mem_ker, map_pow, hi₀, hm, pow_orderOf_eq_one]
  obtain ⟨s, hs⟩ := hO ⟨i₀ ^ m, hi₀m⟩
  have hs' : (i₀ ^ m) ^ (p ^ s) = 1 := congrArg Subtype.val hs
  have hpm : Nat.Coprime (p ^ s) (orderOf ī) := Nat.Coprime.pow_left s hcop.symm
  obtain ⟨t, ht⟩ := exists_pow_eq_self_of_coprime hpm
  set i : Hg := i₀ ^ (p ^ s * t) with hi
  have hiN : i ∈ N := Subgroup.pow_mem N hi₀N _
  have hπi : QuotientGroup.mk' O i = ī := by
    rw [hi, map_pow, hi₀, pow_mul]
    exact ht
  have him : i ^ m = 1 := by
    rw [hi, ← pow_mul]
    have : p ^ s * t * m = m * p ^ s * t := by ring
    rw [this, pow_mul, pow_mul, hs', one_pow]
  refine ⟨i, hiN, hπi, fun x hx => ?_⟩
  set c := x * i * x⁻¹ * i⁻¹ with hc
  have hcO : c ∈ O := by
    rw [← QuotientGroup.ker_mk' O, MonoidHom.mem_ker, hc]
    simp only [map_mul, map_inv, hπi]
    have := hcent x hx
    calc QuotientGroup.mk' O x * ī * (QuotientGroup.mk' O x)⁻¹ * ī⁻¹
        = (ī * QuotientGroup.mk' O x) * (QuotientGroup.mk' O x)⁻¹ * ī⁻¹ := by rw [this]
      _ = 1 := by group
  have hic : Commute c i := by
    have := Subgroup.commutator_mem_commutator hiN hcO
    rw [hNO, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this.symm
  have hxi : x * i * x⁻¹ = c * i := by rw [hc]; group
  have hcm : c ^ m = 1 := by
    have h1 : (x * i * x⁻¹) ^ m = 1 := by
      rw [conj_pow, him]; group
    rw [hxi, hic.mul_pow, him, mul_one] at h1
    exact h1
  obtain ⟨r, hr⟩ := hO ⟨c, hcO⟩
  have hr' : c ^ (p ^ r) = 1 := congrArg Subtype.val hr
  have hc1 : c = 1 := by
    have h1 : orderOf c ∣ m := orderOf_dvd_of_pow_eq_one hcm
    have h2 : orderOf c ∣ p ^ r := orderOf_dvd_of_pow_eq_one hr'
    have h3 : Nat.Coprime m (p ^ r) := Nat.Coprime.pow_right r hcop
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes h3 h1 h2)
  have : x * i * x⁻¹ = i := by rw [hxi, hc1, one_mul]
  calc x * i = (x * i * x⁻¹) * x := by group
    _ = i * x := by rw [this]

end Lift

theorem le_of_coprime_three {Y : Type*} [Group Y] {I M : Subgroup Y} (hs : IsSimpleGroup ↥I)
    {t : ↥I} (ht1 : t ≠ 1) (ht2 : t * t = 1)
    (hM : ∀ a ∈ I, Nat.Coprime (orderOf a) 3 → a ∈ M) : I ≤ M := by
  have hn : (Subgroup.normalClosure ({t} : Set ↥I)).Normal := Subgroup.normalClosure_normal
  have hne : Subgroup.normalClosure ({t} : Set ↥I) ≠ ⊥ := by
    intro h
    apply ht1
    have : t ∈ Subgroup.normalClosure ({t} : Set ↥I) := Subgroup.subset_normalClosure rfl
    rw [h, Subgroup.mem_bot] at this
    exact this
  have htop : Subgroup.normalClosure ({t} : Set ↥I) = ⊤ :=
    (hs.eq_bot_or_eq_top_of_normal _).resolve_left hne
  intro a ha
  have h1 : (⟨a, ha⟩ : ↥I) ∈ Subgroup.normalClosure ({t} : Set ↥I) := by rw [htop]; trivial
  have h2 : Subgroup.normalClosure ({t} : Set ↥I) ≤ M.comap I.subtype := by
    refine (Subgroup.closure_le _).2 ?_
    intro b hb
    obtain ⟨s, hs', hsb⟩ := Group.mem_conjugatesOfSet_iff.1 hb
    rw [Set.mem_singleton_iff] at hs'
    subst hs'
    obtain ⟨c, hc⟩ := isConj_iff.1 hsb
    have hb2 : b * b = 1 := by
      rw [← hc]
      calc c * s * c⁻¹ * (c * s * c⁻¹) = c * (s * s) * c⁻¹ := by group
        _ = 1 := by rw [ht2]; group
    have hord : orderOf (b : Y) ∣ 2 := by
      rw [Subgroup.orderOf_coe]
      exact orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hb2)
    have hcop : Nat.Coprime (orderOf (b : Y)) 3 :=
      Nat.Coprime.coprime_dvd_left hord (by decide)
    exact hM (b : Y) b.2 hcop
  exact h2 h1

theorem autFactD1_proved : AutFactD1H := by
  classical
  intro G _ _ z k H X p h hEne hd E hEle hEn hzE hodd hp'
  have hp : p.Prime := h.A.prime
  have : Fact p.Prime := ⟨hp⟩
  have hXH : X ≤ H := h.A.X_le
  have hEH : E ≤ H := hEle.trans inf_le_left
  let O : Subgroup ↥H := pCore p ↥H
  let π : ↥H →* Sec H O := QuotientGroup.mk' O
  let X' : Subgroup ↥H := X.subgroupOf H
  let E' : Subgroup ↥H := E.subgroupOf H
  have hEX' : E' ≤ centralizer (X' : Set ↥H) := by
    intro e he x hx
    have h1 := Subgroup.mem_centralizer_iff.1 (hEle he).2 (x : G) hx
    exact Subtype.ext h1
  have hcard : Nat.card ↥E' = Nat.card ↥E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEH).toEquiv
  have hlay : (layer ↥H).Normal :=
    Subgroup.normal_of_characteristic _ (h := CFSG.LocalCores.layer_characteristic)
  have hOs : Group.IsSolvable ↥O := L64.isSolvable_pCore hp H
  have hNO : ⁅layer ↥H, O⁆ = ⊥ :=
    (CFSG.LocalCores.component_solvable_centralizer hOs
      (inferInstance : O.Normal).isSubnormal).2
  have hd' := hd
  obtain ⟨hkind, hX3, hPGL, hI, hL2, hC⟩ := hd'
  have hp3 : p = 3 := by
    have h3 : 3 ∣ Nat.card ↥(xBar p H X) := by rw [hX3]
    obtain ⟨xb, hxb⟩ := exists_prime_orderOf_dvd_card' (G := ↥(xBar p H X)) 3 h3
    obtain ⟨x, hx, hxπ⟩ := Subgroup.mem_map.1 xb.2
    obtain ⟨m, hm⟩ := h.A.pgroup ⟨(x : G), (Subgroup.mem_subgroupOf.1 hx)⟩
    have hxm : x ^ (p ^ m) = 1 := Subtype.ext (by simpa using congrArg Subtype.val hm)
    have h4 : orderOf (xb : Sec H O) ∣ p ^ m := by
      rw [← hxπ]
      exact orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hxm, map_one])
    have h5 : orderOf (xb : Sec H O) = 3 := by rw [Subgroup.orderOf_coe]; exact hxb
    have : 3 ∣ p ^ m := h5 ▸ h4
    exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1
      (Nat.prime_three.dvd_of_dvd_pow this)).symm
  subst hp3
  have hKn : (ncl (xBar 3 H X)).Normal := Subgroup.normalClosure_normal
  obtain ⟨hIs, t, ht1, ht2⟩ := isL2_four hL2
  have hπn : ((layer ↥H).map π).Normal :=
    Subgroup.Normal.map hlay π (QuotientGroup.mk'_surjective O)
  have hle : ⁅layer ↥H, X'⁆ ≤ (ncl (xBar 3 H X)).comap π := by
    rw [Subgroup.commutator_le]
    intro a _ x hx
    show π ⁅a, x⁆ ∈ ncl (xBar 3 H X)
    rw [map_commutatorElement, commutatorElement_def]
    have hx' : π x ∈ xBar 3 H X := Subgroup.mem_map_of_mem _ hx
    have h1 : π a * π x * (π a)⁻¹ ∈ ncl (xBar 3 H X) :=
      (Subgroup.normalClosure_normal).conj_mem (π x) (Subgroup.subset_normalClosure hx') (π a)
    exact (ncl (xBar 3 H X)).mul_mem h1 ((ncl (xBar 3 H X)).inv_mem
      (Subgroup.subset_normalClosure hx'))
  have hQ1 : (layer ↥H).map π ⊓ ncl (xBar 3 H X) ≠ ⊥ := by
    intro hbot
    apply L64.commutator_layer_ne_bot_of_Em hXH hEne
    refine L64.commutator_layer_eq_bot_of_le hOs ?_
    intro c hc
    have h1 : π c ∈ (layer ↥H).map π ⊓ ncl (xBar 3 H X) :=
      ⟨Subgroup.mem_map_of_mem π (Subgroup.commutator_le_left _ _ hc), hle hc⟩
    rw [hbot, Subgroup.mem_bot] at h1
    exact (QuotientGroup.eq_one_iff c).1 h1
  have hIQ : ⁅ncl (xBar 3 H X), ncl (xBar 3 H X)⁆ ≤
      (layer ↥H).map π ⊓ ncl (xBar 3 H X) :=
    pgl3four_normal_ge hPGL inf_le_right
      (fun q hq k hk => ⟨hπn.conj_mem q hq.1 k, hKn.conj_mem q hq.2 k⟩) hQ1
  let EY : Subgroup (Sec H O) := E'.map π
  have hEYX : EY ≤ centralizer ((xBar 3 H X : Subgroup (Sec H O)) : Set (Sec H O)) := by
    rintro _ ⟨e, he, rfl⟩ _ ⟨x, hx, rfl⟩
    have h1 := Subgroup.mem_centralizer_iff.1 (hEX' he) x hx
    show π x * π e = π e * π x
    rw [← map_mul, ← map_mul, h1]
  have hcardY : Nat.card ↥EY ∣ Nat.card ↥E :=
    (Subgroup.card_map_dvd (H := E') π).trans (hcard ▸ dvd_rfl)
  have hoddY : Odd (Nat.card ↥EY) := Odd.of_dvd_nat hodd hcardY
  have h3Y : ¬ 3 ∣ Nat.card ↥EY := fun h3 => hp' (h3.trans hcardY)
  have hlift : ∀ b ∈ ncl (xBar 3 H X) ⊓ centralizer ({zSec z H h.A.z_mem O} : Set (Sec H O)),
      Nat.Coprime (orderOf b) 3 → ∀ e ∈ EY, b * e * b⁻¹ ∈ EY := by
    intro b hb hbcop e he
    have hb' : b ∈ ⁅ncl (xBar 3 H X), ncl (xBar 3 H X)⁆ ⊓
        centralizer ((xBar 3 H X : Subgroup (Sec H O)) : Set (Sec H O)) := by
      rw [← hI]; exact hb
    have hbL : b ∈ (layer ↥H).map π := (hIQ hb'.1).1
    have hbC : ∀ x ∈ X', π x * b = b * π x := fun x hx =>
      Subgroup.mem_centralizer_iff.1 hb'.2 (π x) (Subgroup.mem_map_of_mem π hx)
    obtain ⟨i, hiL, hπi, hix⟩ := lift_coprime (X' := X')
      (pCore_isPGroup (p := 3) (G := ↥H)) hNO hbL hbcop hbC
    obtain ⟨e₀, he₀, rfl⟩ := Subgroup.mem_map.1 he
    have hiC : (i : G) ∈ centralizer (X : Set G) := by
      refine Subgroup.mem_centralizer_iff.2 fun x hx => ?_
      have := hix ⟨x, hXH hx⟩ (Subgroup.mem_subgroupOf.2 hx)
      exact congrArg Subtype.val this
    have he₀C : (e₀ : G) ∈ centralizer (X : Set G) := (hEle he₀).2
    let i' : ↥(H ⊓ centralizer (X : Set G)) := ⟨(i : G), i.2, hiC⟩
    let e' : ↥(H ⊓ centralizer (X : Set G)) := ⟨(e₀ : G), e₀.2, he₀C⟩
    have he' : e' ∈ E.subgroupOf (H ⊓ centralizer (X : Set G)) := Subgroup.mem_subgroupOf.2 he₀
    have h1 := Subgroup.mem_subgroupOf.1 (hEn.conj_mem e' he' i')
    refine ⟨i * e₀ * i⁻¹, ?_, ?_⟩
    · exact h1
    · rw [map_mul, map_mul, map_inv, hπi]
  have hnorm : ncl (xBar 3 H X) ⊓ centralizer ({zSec z H h.A.z_mem O} : Set (Sec H O)) ≤
      normalizer (EY : Set (Sec H O)) := by
    refine le_of_coprime_three hIs ht1 ht2 (fun a ha hcop => ?_)
    rw [Subgroup.mem_normalizer_iff]
    intro e
    refine ⟨fun he => hlift a ha hcop e he, fun he => ?_⟩
    have h1 := hlift a⁻¹ (Subgroup.inv_mem _ ha) (by rwa [orderOf_inv]) _ he
    have h2 : a⁻¹ * (a * e * a⁻¹) * a⁻¹⁻¹ = e := by group
    rwa [h2] at h1
  have hnormI : ∀ i ∈ ncl (xBar 3 H X) ⊓ centralizer ({zSec z H h.A.z_mem O} : Set (Sec H O)),
      ∀ e ∈ EY, i * e * i⁻¹ ∈ EY :=
    fun i hi e he => ((Subgroup.mem_normalizer_iff.1 (hnorm hi)) e).1 he
  have hkey := autFactD1Y_proved (Sec H O) k (zSec z H h.A.z_mem O) (xBar 3 H X) hd EY hEYX
    hoddY h3Y hnormI
  have key : ∀ e ∈ E', π e ∈ centralizer ((ncl (xBar 3 H X) : Subgroup (Sec H O)) :
      Set (Sec H O)) := fun e he => hkey (Subgroup.mem_map_of_mem π he)
  have hcomm : ∀ e ∈ E', ∀ k ∈ ⁅layer ↥H, X'⁆, ⁅k, e⁆ ∈ O := by
    intro e he k hk
    have h1 := Subgroup.mem_centralizer_iff.1 (key e he) (π k) (hle hk)
    have h2 : π ⁅k, e⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_def, h1]
      group
    exact (QuotientGroup.eq_one_iff _).1 h2
  have hmain := centralizes_commutator_layer (D := O) hOs X' E' hEX' hcomm
  intro g hg
  have h2 : ⁅(layer ↥H).map H.subtype, X⁆ = (⁅layer ↥H, X'⁆).map H.subtype := by
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hXH]
  show g ∈ centralizer (((⁅(layer ↥H).map H.subtype, X⁆ : Subgroup G)) : Set G)
  rw [h2]
  rintro _ ⟨k, hk, rfl⟩
  have h3 := Subgroup.mem_centralizer_iff.1 (hmain (show (⟨g, hEH hg⟩ : ↥H) ∈ E' from hg)) k hk
  have h4 := congrArg Subtype.val h3
  exact h4

end CFSG.GH74.GLS.Stage2.Signalizer.L46E
