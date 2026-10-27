module

public import CFSG.ClassicalInvolution.Q3.TL3GlueMain
public import CFSG.ClassicalInvolution.Q3.Q3NMClass
public import CFSG.ClassicalInvolution.Q3.TL3C1

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance
open CFSG.Assembly.Dichotomy (involutionOddCore)
open scoped commutatorElement

section Gen

variable {Y : Type} [Group Y] [Finite Y]

theorem oddCoreImg_le_oddCent {t : Y} {E : Subgroup Y}
    (hE : E ≤ Subgroup.centralizer ({t} : Set Y))
    (hN : Subgroup.centralizer ({t} : Set Y) ≤ Subgroup.normalizer (E : Set Y)) :
    oddCoreImg E ≤ oddCoreImg (Subgroup.centralizer ({t} : Set Y)) :=
  TC.le_oddCoreImg_of_normalizes ((oddCoreImg_le E).trans hE)
    (fun _ hc _ ho => conj_mem_oddCoreImg (hN hc) ho) (odd_natCard_oddCoreImg E)

end Gen

section Datum

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem oddCoreImg_le_oddCent_of_datum (hd : TightDatum R S t) :
    oddCoreImg R ≤ oddCoreImg (Subgroup.centralizer ({t} : Set Y)) :=
  oddCoreImg_le_oddCent hd.cent hd.le_normalizer

end Datum

section Alpha

variable {Y : Type} [Group Y]

theorem commute_of_alphaOf_eq_bot {A : Subgroup Y} (hα : alphaOf A = ⊥) {a : Y} (ha : a ∈ A)
    (ha1 : a ≠ 1) {n : Y} (hn : n ∈ involutionOddCore a) {b : Y} (hb : b ∈ A) :
    n * b = b * n := by
  have h := commutator_le_alphaOf A ha ha1 (Subgroup.commutator_mem_commutator hn hb)
  rw [hα, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h
  exact h

end Alpha

section Gorenstein

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

omit [Finite Y] in
theorem ne_one_of_datum (hd : TightDatum R S t) : t ≠ 1 := fun h => by
  have h2 := hd.order
  rw [h, orderOf_one] at h2
  norm_num at h2

omit [Finite Y] in
theorem oddCent_le_centralizer_of_alpha (hd : TightDatum R S t) {u : Y}
    (hα : alphaOf (Subgroup.closure ({t, u} : Set Y)) = ⊥) :
    oddCoreImg (Subgroup.centralizer ({t} : Set Y)) ≤ Subgroup.centralizer ({u} : Set Y) := by
  intro n hn
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact commute_of_alphaOf_eq_bot hα (Subgroup.subset_closure (by simp)) (ne_one_of_datum hd) hn
    (Subgroup.subset_closure (by simp))

theorem le_centralizer_of_alpha (hd : TightDatum R S t) {J : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)) {u : Y}
    (hu : IsUniqueInvolution J u) (hα : alphaOf (Subgroup.closure ({t, u} : Set Y)) = ⊥) :
    R ≤ Subgroup.centralizer ({u} : Set Y) := by
  obtain ⟨-, hu2, hut, -, huK, -⟩ := hd.edge_involution hJ hu
  have hcomm : ∀ r ∈ R, ⁅u, r⁆ ∈ oddCoreImg R := (hd.act_eq_one_iff hut).mp huK
  have huT : u ∈ Bootstrap.trivialOnQuot R := ⟨hd.le_normalizer hut, hcomm⟩
  have hA : IsPGroup 2 (Subgroup.zpowers u) := isPGroup_zpowers_of_mul_self_eq_one hu2
  have hAT : Subgroup.zpowers u ≤ Bootstrap.trivialOnQuot R := Subgroup.zpowers_le.mpr huT
  have ht1 : t ≠ 1 := ne_one_of_datum hd
  have htA : t ∈ Subgroup.closure ({t, u} : Set Y) := Subgroup.subset_closure (by simp)
  have huA : u ∈ Subgroup.closure ({t, u} : Set Y) := Subgroup.subset_closure (by simp)
  intro r hr
  obtain ⟨h, hh, n, hn, rfl⟩ := Bootstrap.exists_mem_inf_centralizer_mul hA hAT hr
  have hnθ : n ∈ oddCoreImg (Subgroup.centralizer ({t} : Set Y)) :=
    oddCoreImg_le_oddCent_of_datum hd hn
  have hnu : n * u = u * n := commute_of_alphaOf_eq_bot hα htA ht1 hnθ huA
  have hhu : u * h = h * u := Subgroup.mem_centralizer_iff.mp hh.2 u (Subgroup.mem_zpowers u)
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc h * n * u = h * (n * u) := by rw [mul_assoc]
    _ = h * (u * n) := by rw [hnu]
    _ = (h * u) * n := by rw [mul_assoc]
    _ = (u * h) * n := by rw [hhu]
    _ = u * (h * n) := by rw [mul_assoc]

theorem tightCore_centralizer_of_alpha (hd : TightDatum R S t) {J : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)) {u : Y}
    (hu : IsUniqueInvolution J u) (hα : alphaOf (Subgroup.closure ({t, u} : Set Y)) = ⊥) :
    tightCore R ≤ Subgroup.centralizer ({u} : Set Y) :=
  (tightCore_le R).trans (le_centralizer_of_alpha hd hJ hu hα)

theorem edge_le_centralizer_of_alpha (hd : TightDatum R S t) {J : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)) {u : Y}
    (hu : IsUniqueInvolution J u) (hα : alphaOf (Subgroup.closure ({t, u} : Set Y)) = ⊥) :
    J ≤ Subgroup.centralizer ({t} : Set Y) := by
  obtain ⟨g, hgJ'⟩ := hJ.1
  have hgJ : conjSub g (tightCore R) = J := hgJ'
  obtain ⟨S', hd', -⟩ := hd.conj g
  have hcore : tightCore (conjSub g R) = J := by rw [← conjSub_tightCore, hgJ]
  have hfam : CoreAssembly.conjClass (tightCore (conjSub g R)) =
      CoreAssembly.conjClass (tightCore R) := by
    rw [← conjSub_tightCore, conjClass_conjSub]
  have hgu : g * t * g⁻¹ = u := by
    have h1 := hd.isUniqueInvolution_core.conj g
    rw [hgJ] at h1
    exact h1.eq hu
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) :=
    CoreAssembly.mem_conjClass_self _
  have hKJ : tightCore R ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) J :=
    Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hd.hypOmegaGen hK hJ.1 hJ
  have hKJ' : tightCore R ∈ omegaNbr (CoreAssembly.conjClass (tightCore (conjSub g R)))
      (tightCore (conjSub g R)) := by
    rw [hfam, hcore]
    exact hKJ
  have hα' : alphaOf (Subgroup.closure ({g * t * g⁻¹, t} : Set Y)) = ⊥ := by
    rw [hgu, Set.pair_comm]
    exact hα
  have h := le_centralizer_of_alpha hd' hKJ' hd.isUniqueInvolution_core hα'
  rw [← hcore]
  exact (tightCore_le _).trans h

theorem edge_le_normalizer_of_alpha (hd : TightDatum R S t) {J : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)) {u : Y}
    (hu : IsUniqueInvolution J u) (hα : alphaOf (Subgroup.closure ({t, u} : Set Y)) = ⊥) :
    J ≤ Subgroup.normalizer (tightCore R : Set Y) :=
  (edge_le_centralizer_of_alpha hd hJ hu hα).trans hd.le_normalizer_core

end Gorenstein

section Components

open CFSG.ClassicalInvolution.Asc77.Lemma52Proof

@[expose] def IsInducedAut {Q : Type} [Group Q] (L : Subgroup Q) (x : Q) (σ : MulAut ↥L) :
    Prop :=
  ∀ y : ↥L, ((σ y : ↥L) : Q) = x * y * x⁻¹

theorem autOddFreeOn_of_mulEquiv' {X X' : Type} [Group X] [Finite X] [Group X'] [Finite X']
    (e : X ≃* X') (P : MulAut X → Prop) (h : Q3NM.AutOddFreeOn X P) :
    Q3NM.AutOddFreeOn X' (fun f' => P ((MulAut.congr e).symm f')) := by
  intro 𝒳' hinn' f' hP' hf'
  set φ : MulAut X ≃* MulAut X' := MulAut.congr e with hφ
  set 𝒳 : Subgroup (MulAut X) := 𝒳'.map φ.symm.toMonoidHom with h𝒳
  have hinn : Q3NM.innSubgroup X ≤ 𝒳 := by
    rintro _ ⟨x, rfl⟩
    refine ⟨φ (MulAut.conj x), hinn' ⟨e x, ?_⟩, by simp⟩
    ext y
    simp [hφ, MulAut.congr_apply, MulAut.conj_apply]
  let ε : ↥𝒳' ≃* ↥𝒳 := φ.symm.subgroupMap 𝒳'
  have hf : orderOf (ε f') = 2 := by rw [MulEquiv.orderOf_eq]; exact hf'
  exact oddCoreIn_centralizer_eq_bot_of_mulEquiv ε f' (h 𝒳 hinn (ε f') hP' hf)

variable {Q : Type} [Group Q] [Finite Q]

omit [Finite Q] in
theorem innSubgroup_le_inducedAutOn (L : Subgroup Q) :
    Q3NM.innSubgroup ↥L ≤ inducedAutOn L := by
  rintro _ ⟨l, rfl⟩
  refine ⟨⟨(l : Q), Subgroup.le_normalizer l.2⟩, ?_⟩
  apply MulEquiv.ext
  intro y
  apply Subtype.ext
  rfl

theorem oddCent_eq_bot_of_components (hO : CFSG.pPrimeCore 2 Q = ⊥) {t : Q} (ht2 : t * t = 1)
    (ht1 : t ≠ 1)
    (hL : ∀ L : Subgroup Q, CFSG.IsComponent L → t ∈ Subgroup.normalizer (L : Set Q) →
      (∃ y ∈ L, t * y ≠ y * t) → Q3NM.AutOddFreeOn ↥L (IsInducedAut L t)) :
    involutionOddCore t = ⊥ := by
  by_contra hD0
  obtain ⟨L, hLc, x, hx, y, hyL, hxy⟩ := exists_component_moved hO ht2 ht1 le_rfl hD0
  have hxN : x ∈ Subgroup.normalizer (L : Set Q) :=
    LocalBalance.mem_normalizer_of_conjSub_eq
      (normalizes_component_of_mem_involutionOddCore hLc ht2 hx)
  by_cases htL : conjSub t L = L
  swap
  · exact hxy (LocalBalance.commute_of_moved hLc ht2 htL hx y hyL)
  have htN : t ∈ Subgroup.normalizer (L : Set Q) := LocalBalance.mem_normalizer_of_conjSub_eq htL
  by_cases hmv : ∃ y ∈ L, t * y ≠ y * t
  swap
  · push Not at hmv
    exact hxy (centralizes_of_centralizes_involution hLc hx hmv y hyL)
  have hf1 : toInducedAutOn L ⟨t, htN⟩ ≠ 1 := by
    obtain ⟨y', hy', hty'⟩ := hmv
    exact toInducedAutOn_ne_one_of_moved L htN hy' hty'
  have hff : toInducedAutOn L ⟨t, htN⟩ * toInducedAutOn L ⟨t, htN⟩ = 1 := by
    rw [← map_mul]
    have e : (⟨t, htN⟩ : Subgroup.normalizer (L : Set Q)) * ⟨t, htN⟩ = 1 := Subtype.ext ht2
    rw [e, map_one]
  have hord : orderOf (toInducedAutOn L ⟨t, htN⟩) = 2 :=
    orderOf_eq_prime (by rw [sq]; exact hff) hf1
  have hbot := hL L hLc htN hmv (inducedAutOn L) (innSubgroup_le_inducedAutOn L) _
    (fun y => rfl) hord
  have hmem := toInducedAutOn_mem_involutionOddCore L ht2 htN hxN hx
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hxy (commute_of_toInducedAutOn_eq_one L hxN hmem y hyL)

end Components

end CFSG.ClassicalInvolution.Q3.TL4
