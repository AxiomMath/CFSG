module

public import CFSG.GH74.GLS.C3.Layer1.BkP89J2Spec
public import CFSG.GH74.Generic.S45.LEvSporLeaf23

public section

open Subgroup CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore CFSG.GH74.Generic.S45.EvSpor
  CFSG.GH74.Generic.S45
open scoped commutatorElement

namespace CFSG.GH74.GLS.C3.Layer1.Bk.J2C

structure J2CentFacts (Q : Type*) [Group Q] (t : Q) (E : Subgroup Q) : Prop where
  card_cent : Nat.card ↥(centralizer ({t} : Set Q)) = 1920
  E_le : E ≤ centralizer ({t} : Set Q)
  card_E : Nat.card ↥E = 32
  t_mem : t ∈ E
  E_normal : ∀ y ∈ centralizer ({t} : Set Q), ∀ e ∈ E, y * e * y⁻¹ ∈ E
  sq_mem : ∀ x ∈ E, x * x = 1 ∨ x * x = t
  comm_mem : ∀ x ∈ E, ∀ y ∈ E, ⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = t
  center : ∀ x ∈ E, (∀ y ∈ E, x * y = y * x) → x = 1 ∨ x = t
  cent_E : ∀ g ∈ centralizer ({t} : Set Q), (∀ e ∈ E, g * e = e * g) → g = 1 ∨ g = t
  irred : ∀ N : Subgroup Q, N ≤ E → t ∈ N →
    (∀ y ∈ centralizer ({t} : Set Q), ∀ n ∈ N, y * n * y⁻¹ ∈ N) → (∃ x ∈ N, x ≠ 1 ∧ x ≠ t) →
      E ≤ N
  perfect : ⁅centralizer ({t} : Set Q), centralizer ({t} : Set Q)⁆ = centralizer ({t} : Set Q)
  two_core : ∀ N : Subgroup Q, N ≤ centralizer ({t} : Set Q) →
    (∀ y ∈ centralizer ({t} : Set Q), ∀ n ∈ N, y * n * y⁻¹ ∈ N) → IsPGroup 2 ↥N → N ≤ E
  aut : Nat.card (MulAut ↥E) ≤ 1920

section Transport

variable {Q Q' : Type*} [Group Q] [Group Q']

theorem centralizer_singleton_symm (φ : Q ≃* Q') (t' : Q') :
    centralizer ({φ.symm t'} : Set Q) = (centralizer ({t'} : Set Q')).map φ.symm.toMonoidHom := by
  ext x
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have := congrArg φ h
    simpa using this
  · intro h
    have := congrArg φ.symm h
    simpa using this


theorem mem_map_symm_iff (φ : Q ≃* Q') (K' : Subgroup Q') (x : Q) :
    x ∈ K'.map φ.symm.toMonoidHom ↔ φ x ∈ K' := by
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm]

theorem mem_map_iff' (φ : Q ≃* Q') (K : Subgroup Q) (y : Q') :
    y ∈ K.map φ.toMonoidHom ↔ φ.symm y ∈ K := Subgroup.mem_map_equiv

theorem J2CentFacts.of_mulEquiv (φ : Q ≃* Q') {t' : Q'} {E' : Subgroup Q'}
    (h : J2CentFacts Q' t' E') : J2CentFacts Q (φ.symm t') (E'.map φ.symm.toMonoidHom) := by
  have hC : centralizer ({φ.symm t'} : Set Q) =
      (centralizer ({t'} : Set Q')).map φ.symm.toMonoidHom := centralizer_singleton_symm φ t'
  have hmemE : ∀ x, x ∈ E'.map φ.symm.toMonoidHom ↔ φ x ∈ E' := mem_map_symm_iff φ E'
  have hmemC : ∀ x, x ∈ centralizer ({φ.symm t'} : Set Q) ↔ φ x ∈ centralizer ({t'} : Set Q') := by
    intro x
    rw [hC]
    exact mem_map_symm_iff φ _ x
  have hts : φ (φ.symm t') = t' := φ.apply_symm_apply t'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hC, Subgroup.card_map_of_injective φ.symm.injective]
    exact h.card_cent
  · intro x hx
    exact (hmemC x).2 (h.E_le ((hmemE x).1 hx))
  · rw [Subgroup.card_map_of_injective φ.symm.injective]
    exact h.card_E
  · exact (hmemE _).2 (by rw [hts]; exact h.t_mem)
  · intro y hy e he
    have := h.E_normal (φ y) ((hmemC y).1 hy) (φ e) ((hmemE e).1 he)
    exact (hmemE _).2 (by simpa using this)
  · intro x hx
    rcases h.sq_mem (φ x) ((hmemE x).1 hx) with h1 | h1
    · left
      apply φ.injective
      simpa using h1
    · right
      apply φ.injective
      rw [hts]
      simpa using h1
  · intro x hx y hy
    rcases h.comm_mem (φ x) ((hmemE x).1 hx) (φ y) ((hmemE y).1 hy) with h1 | h1
    · left
      apply φ.injective
      simpa [commutatorElement_def] using h1
    · right
      apply φ.injective
      rw [hts]
      simpa [commutatorElement_def] using h1
  · intro x hx hxc
    have key : ∀ y' ∈ E', φ x * y' = y' * φ x := by
      intro y' hy'
      have hy : φ.symm y' ∈ E'.map φ.symm.toMonoidHom := (hmemE _).2 (by simpa using hy')
      have := congrArg φ (hxc _ hy)
      simpa using this
    rcases h.center (φ x) ((hmemE x).1 hx) key with h1 | h1
    · left
      apply φ.injective
      simpa using h1
    · right
      apply φ.injective
      rw [hts]
      exact h1
  · intro g hg hgc
    have key : ∀ e' ∈ E', φ g * e' = e' * φ g := by
      intro e' he'
      have hy : φ.symm e' ∈ E'.map φ.symm.toMonoidHom := (hmemE _).2 (by simpa using he')
      have := congrArg φ (hgc _ hy)
      simpa using this
    rcases h.cent_E (φ g) ((hmemC g).1 hg) key with h1 | h1
    · left
      apply φ.injective
      simpa using h1
    · right
      apply φ.injective
      rw [hts]
      exact h1
  · intro N hNE htN hNn hx
    have hmemN' : ∀ y, y ∈ N.map φ.toMonoidHom ↔ φ.symm y ∈ N := mem_map_iff' φ N
    have hN'E : N.map φ.toMonoidHom ≤ E' := by
      intro y hy
      have h1 : φ.symm y ∈ E'.map φ.symm.toMonoidHom := hNE ((hmemN' y).1 hy)
      have h2 := (hmemE _).1 h1
      simpa using h2
    have ht' : t' ∈ N.map φ.toMonoidHom := (hmemN' _).2 htN
    have hn' : ∀ y ∈ centralizer ({t'} : Set Q'), ∀ n ∈ N.map φ.toMonoidHom,
        y * n * y⁻¹ ∈ N.map φ.toMonoidHom := by
      intro y hy n hn
      have hy' : φ.symm y ∈ centralizer ({φ.symm t'} : Set Q) :=
        (hmemC _).2 (by simpa using hy)
      have h1 := hNn _ hy' _ ((hmemN' n).1 hn)
      exact (hmemN' _).2 (by simpa using h1)
    obtain ⟨x, hxN, hx1, hxt⟩ := hx
    have hx' : ∃ x' ∈ N.map φ.toMonoidHom, x' ≠ 1 ∧ x' ≠ t' :=
      ⟨φ x, (hmemN' _).2 (by simpa using hxN), fun h1 => hx1 (φ.injective (by simpa using h1)),
        fun h1 => hxt (φ.injective (by rw [hts]; exact h1))⟩
    have hE'N' := h.irred _ hN'E ht' hn' hx'
    intro e he
    have h1 : φ e ∈ N.map φ.toMonoidHom := hE'N' ((hmemE e).1 he)
    simpa using (hmemN' _).1 h1
  · rw [hC, ← Subgroup.map_commutator, h.perfect]
  · intro N hNC hNn hN
    have hmemN' : ∀ y, y ∈ N.map φ.toMonoidHom ↔ φ.symm y ∈ N := mem_map_iff' φ N
    have hN'C : N.map φ.toMonoidHom ≤ centralizer ({t'} : Set Q') := by
      intro y hy
      have h1 := (hmemC _).1 (hNC ((hmemN' y).1 hy))
      simpa using h1
    have hn' : ∀ y ∈ centralizer ({t'} : Set Q'), ∀ n ∈ N.map φ.toMonoidHom,
        y * n * y⁻¹ ∈ N.map φ.toMonoidHom := by
      intro y hy n hn
      have hy' : φ.symm y ∈ centralizer ({φ.symm t'} : Set Q) :=
        (hmemC _).2 (by simpa using hy)
      have h1 := hNn _ hy' _ ((hmemN' n).1 hn)
      exact (hmemN' _).2 (by simpa using h1)
    have hN'p : IsPGroup 2 ↥(N.map φ.toMonoidHom) :=
      hN.of_equiv (Subgroup.equivMapOfInjective N φ.toMonoidHom φ.injective)
    have hle := h.two_core _ hN'C hn' hN'p
    intro x hx
    have h1 : φ x ∈ N.map φ.toMonoidHom := (hmemN' _).2 (by simpa using hx)
    exact (hmemE x).2 (hle h1)
  · have e : ↥E' ≃* ↥(E'.map φ.symm.toMonoidHom) :=
      Subgroup.equivMapOfInjective E' φ.symm.toMonoidHom φ.symm.injective
    rw [← Nat.card_congr (MulAut.congr e).toEquiv]
    exact h.aut

end Transport


section Model

theorem tA_mem_j2P :
    tA ∈ j2P := j2_row_mem_P j2Row2A_mem j2Row2A_outer

@[expose] noncomputable def tAj :
    ↥j2P := ⟨tA, tA_mem_j2P⟩


theorem coe_tAj : ((tAj : ↥j2P) : Equiv.Perm (Fin 315)) = tA := by
  unfold tAj
  rfl

@[expose] noncomputable def Ej : Subgroup ↥j2P := Esub.subgroupOf j2P

theorem mem_cent_tAj (x : ↥j2P) :
    x ∈ centralizer ({tAj} : Set ↥j2P) ↔ (x : Equiv.Perm (Fin 315)) ∈ Ysub := by
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_inf,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    exact ⟨x.2, congrArg Subtype.val h⟩
  · intro h
    exact Subtype.ext h.2

theorem j2CentFacts_model : J2CentFacts ↥j2P tAj Ej := by
  have M := j2_cent_model
  have hYP : Ysub ≤ j2P := inf_le_left
  have hEP : Esub ≤ j2P := M.E_le.trans hYP
  have hmemE : ∀ x : ↥j2P, x ∈ Ej ↔ (x : Equiv.Perm (Fin 315)) ∈ Esub := fun x => by
    rw [Ej, Subgroup.mem_subgroupOf]
  have hC : centralizer ({tAj} : Set ↥j2P) = Ysub.subgroupOf j2P := by
    ext x
    rw [mem_cent_tAj]
    exact Iff.rfl
  have hnorm : ∀ N : Subgroup ↥j2P, (∀ y ∈ centralizer ({tAj} : Set ↥j2P), ∀ n ∈ N, y * n * y⁻¹ ∈ N) →
      ∀ y ∈ Ysub, ∀ n ∈ N.map j2P.subtype, y * n * y⁻¹ ∈ N.map j2P.subtype := by
    rintro N hNn y hy _ ⟨n, hn, rfl⟩
    have hyj : y ∈ j2P := hYP hy
    exact ⟨_, hNn ⟨y, hyj⟩ ((mem_cent_tAj ⟨y, hyj⟩).2 hy) n hn, rfl⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hC, ← M.card_Y]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYP).toEquiv
  · intro x hx
    exact (mem_cent_tAj x).2 (M.E_le ((hmemE x).1 hx))
  · rw [← M.card_E]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEP).toEquiv
  · exact (hmemE _).2 M.tA_mem
  · intro y hy e he
    exact (hmemE _).2 (by simpa using M.E_normal y ((mem_cent_tAj y).1 hy) e ((hmemE e).1 he))
  · intro x hx
    rcases M.sq_mem x ((hmemE x).1 hx) with h | h
    · left; exact Subtype.ext (by simpa using h)
    · right; exact Subtype.ext (by rw [coe_tAj]; simpa using h)
  · intro x hx y hy
    rcases M.comm_mem x ((hmemE x).1 hx) y ((hmemE y).1 hy) with h | h
    · left; exact Subtype.ext (by simpa [commutatorElement_def] using h)
    · right; exact Subtype.ext (by rw [coe_tAj]; simpa [commutatorElement_def] using h)
  · intro x hx hxc
    rcases M.center x ((hmemE x).1 hx) (fun y' hy' => congrArg Subtype.val (hxc ⟨y', hEP hy'⟩ hy'))
      with h | h
    · left; exact Subtype.ext h
    · right; exact Subtype.ext h
  · intro g hg hgc
    rcases M.cent_E g ((mem_cent_tAj g).1 hg)
      (fun e he => congrArg Subtype.val (hgc ⟨e, hEP he⟩ he)) with h | h
    · left; exact Subtype.ext h
    · right; exact Subtype.ext h
  · intro N hNE htN hNn hx
    have hN'E : N.map j2P.subtype ≤ Esub := by
      rintro _ ⟨n, hn, rfl⟩
      exact hNE hn
    have ht' : tA ∈ N.map j2P.subtype := ⟨tAj, htN, rfl⟩
    obtain ⟨x, hxN, hx1, hxt⟩ := hx
    have hx' : ∃ x' ∈ N.map j2P.subtype, x' ≠ 1 ∧ x' ≠ tA :=
      ⟨(x : Equiv.Perm (Fin 315)), ⟨x, hxN, rfl⟩, fun h1 => hx1 (Subtype.ext h1),
        fun h1 => hxt (Subtype.ext h1)⟩
    have hle := M.irred _ hN'E ht' (hnorm N hNn) hx'
    intro e he
    obtain ⟨n, hn, hne⟩ := hle ((hmemE e).1 he)
    have : n = e := Subtype.ext hne
    rw [← this]
    exact hn
  · have hmap : (centralizer ({tAj} : Set ↥j2P)).map j2P.subtype = Ysub := by
      rw [hC, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hYP]
    apply Subgroup.map_injective j2P.subtype_injective
    rw [Subgroup.map_commutator, hmap]
    exact M.perfect
  · intro N hNC hNn hN
    have hN'C : N.map j2P.subtype ≤ Ysub := by
      rintro _ ⟨n, hn, rfl⟩
      exact (mem_cent_tAj n).1 (hNC hn)
    have hp : IsPGroup 2 ↥(N.map j2P.subtype) :=
      hN.of_equiv (Subgroup.equivMapOfInjective N j2P.subtype j2P.subtype_injective)
    have hle := M.two_core _ hN'C (hnorm N hNn) hp
    intro n hn
    exact hle ⟨n, hn, rfl⟩
  · exact (Nat.card_congr (MulAut.congr (Subgroup.subgroupOfEquivOfLe hEP)).toEquiv).le.trans M.aut

end Model


theorem card_cent_subtype {G : Type*} [Group G] (H : Subgroup G) (s : ↥H) :
    Nat.card ↥(centralizer ({s} : Set ↥H)) =
      Nat.card ↥(H ⊓ centralizer ({(s : G)} : Set G)) := by
  have h : centralizer ({s} : Set ↥H) = (H ⊓ centralizer ({(s : G)} : Set G)).subgroupOf H := by
    ext x
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hx
      exact ⟨x.2, congrArg Subtype.val hx⟩
    · intro hx
      exact Subtype.ext hx.2
  rw [h]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv

theorem card_cent_symm {Q Q' : Type*} [Group Q] [Group Q'] (φ : Q ≃* Q') (t' : Q') :
    Nat.card ↥(centralizer ({φ.symm t'} : Set Q)) = Nat.card ↥(centralizer ({t'} : Set Q')) := by
  rw [centralizer_singleton_symm, Subgroup.card_map_of_injective φ.symm.injective]

theorem j2_cent_facts
    {Q : Type} [Group Q] (hQ : Blueprint.NativeSporadic.IsSporadic Q .J2) {t : Q}
    (ht : orderOf t = 2) (h128 : 2 ^ 7 ∣ Nat.card ↥(centralizer ({t} : Set Q))) :
    ∃ E : Subgroup Q, J2CentFacts Q t E := by
  obtain ⟨e⟩ := hQ
  let φ₀ : Q ≃* ↥j2P := e.trans j2PermEquiv
  have hs2 : orderOf ((φ₀ t : ↥j2P) : Equiv.Perm (Fin 315)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact ht
  have hcardC : Nat.card ↥(centralizer ({φ₀ t} : Set ↥j2P)) =
      Nat.card ↥(centralizer ({t} : Set Q)) := by
    have := card_cent_symm φ₀ (φ₀ t)
    rw [MulEquiv.symm_apply_apply] at this
    exact this.symm
  rcases j2_cover (φ₀ t).1 (φ₀ t).2 hs2 with ⟨g, hg, hgt⟩ | ⟨g, hg, hgt⟩
  · let g' : ↥j2P := ⟨g, hg⟩
    have hsg : φ₀ t = g' * (tAj : ↥j2P) * g'⁻¹ := Subtype.ext hgt
    let Φ : Q ≃* ↥j2P := φ₀.trans (MulAut.conj g'⁻¹)
    have hΦ : Φ t = tAj := by
      show g'⁻¹ * φ₀ t * g'⁻¹⁻¹ = tAj
      rw [hsg]
      group
    have hΦ' : Φ.symm tAj = t := by
      rw [MulEquiv.symm_apply_eq]
      exact hΦ.symm
    have := J2CentFacts.of_mulEquiv Φ j2CentFacts_model
    rw [hΦ'] at this
    exact ⟨_, this⟩
  · exfalso
    have h240 : Nat.card ↥(j2P ⊓ centralizer ({tp 315 j2Row2B.rep} : Set (Equiv.Perm (Fin 315)))) =
        240 := ((j2_rows_spec.1 j2Row2B j2Row2B_mem).2.2.2.2).trans j2Row2B_centOrder
    have hc : Nat.card ↥(centralizer ({φ₀ t} : Set ↥j2P)) = 240 := by
      rw [card_cent_subtype j2P (φ₀ t), hgt, inf_comm, card_cent_conj hg, inf_comm]
      exact h240
    rw [← hcardC, hc] at h128
    omega

end CFSG.GH74.GLS.C3.Layer1.Bk.J2C
