module

public import CFSG.ClassicalInvolution.Q3.TL4ConnDefs

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Asc77.T8 (XMem)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

section Core

variable (x : G)

@[expose] noncomputable def coreAt (L : Subgroup G) : Subgroup G :=
  tightCore (L ⊓ Subgroup.centralizer ({x} : Set G))

omit [Finite G] in
theorem coreAt_le (L : Subgroup G) : coreAt x L ≤ L :=
  (tightCore_le _).trans inf_le_left

omit [Finite G] in
theorem coreAt_le_centralizer (L : Subgroup G) :
    coreAt x L ≤ Subgroup.centralizer ({x} : Set G) :=
  (tightCore_le _).trans inf_le_right

omit [Finite G] in
theorem le_coreAt {L P : Subgroup G} (hP : IsPGroup 2 P) (hPL : P ≤ L)
    (hPx : P ≤ Subgroup.centralizer ({x} : Set G)) : P ≤ coreAt x L :=
  fun _ hp => Subgroup.subset_closure ⟨⟨hPL hp, hPx hp⟩, hP.to_le (Subgroup.zpowers_le.mpr hp)⟩

omit [Finite G] in
theorem conjSub_coreAt {c : G} (hc : c ∈ Subgroup.centralizer ({x} : Set G)) (L : Subgroup G) :
    conjSub c (coreAt x L) = coreAt x (conjSub c L) := by
  unfold coreAt
  rw [conjSub_tightCore]
  congr 1
  show (L ⊓ Subgroup.centralizer ({x} : Set G)).map (MulAut.conj c).toMonoidHom = _
  rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj c).injective]
  show conjSub c L ⊓ conjSub c (Subgroup.centralizer ({x} : Set G)) = _
  rw [conjSub_eq_self_of_mem hc]

omit [Finite G] in
theorem mem_normalizer_coreAt {L : Subgroup G} {c : G}
    (hcL : c ∈ Subgroup.normalizer (L : Set G)) (hcx : c ∈ Subgroup.centralizer ({x} : Set G)) :
    c ∈ Subgroup.normalizer (coreAt x L : Set G) := by
  rw [mem_normalizer_iff_conjSub_eq, conjSub_coreAt x hcx, mem_normalizer_iff_conjSub_eq.mp hcL]

omit [Finite G] in
theorem closure_twoElts_coreAt (L : Subgroup G) :
    Subgroup.closure {y : G | y ∈ coreAt x L ∧ IsPGroup 2 (Subgroup.zpowers y)} = coreAt x L := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro y hy
    exact hy.1
  · refine Subgroup.closure_mono ?_
    intro y hy
    exact ⟨Subgroup.subset_closure hy, hy.2⟩

end Core

omit [Finite G] in
theorem le_oddCoreOf_of_normal_odd {M N : Subgroup G} (hNM : N ≤ M)
    (hn : M ≤ Subgroup.normalizer (N : Set G)) (hodd : Odd (Nat.card N)) : N ≤ oddCoreOf M := by
  have hnorm : (N.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNM).mpr hn
  have hodd' : Odd (Nat.card ↥(N.subgroupOf M)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNM).toEquiv]
  have hle : N.subgroupOf M ≤ classicalInvolutionOddCore ↥M := by
    unfold classicalInvolutionOddCore
    exact le_sSup ⟨hnorm, hodd'⟩
  intro y hy
  exact ⟨⟨y, hNM hy⟩, hle hy, rfl⟩

theorem inf_oddCoreOf_le {L M : Subgroup G} (hML : M ≤ L) : M ⊓ oddCoreOf L ≤ oddCoreOf M :=
  le_oddCoreOf_of_normal_odd inf_le_left
    (fun m hm => by
      have hmN : m ∈ Subgroup.normalizer (oddCoreOf L : Set G) :=
        mem_normalizer_oddCore_of_mem_normalizer (Subgroup.le_normalizer (hML hm))
      rw [Subgroup.mem_normalizer_iff] at hmN ⊢
      intro y
      constructor
      · rintro ⟨hy1, hy2⟩
        exact ⟨M.mul_mem (M.mul_mem hm hy1) (M.inv_mem hm), (hmN y).mp hy2⟩
      · rintro ⟨hy1, hy2⟩
        have h1 : m⁻¹ * (m * y * m⁻¹) * m ∈ M :=
          M.mul_mem (M.mul_mem (M.inv_mem hm) hy1) hm
        exact ⟨by simpa [mul_assoc] using h1, (hmN y).mpr hy2⟩)
    ((oddCoreOf_odd_natCard L).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right))

section Members

variable {r : ℕ} {Ω : Set (Subgroup G)} {x : G}

omit [Finite G] in
theorem XMem.exists_sylow {L : Subgroup G} (hL : XMem Ω x L) :
    ∃ P, IsSylow2In P L ∧ P ≤ Subgroup.centralizer ({x} : Set G) := by
  obtain ⟨-, -, P, hP, hPx⟩ := hL
  exact ⟨P, hP, fun p hp => Subgroup.mem_centralizer_singleton_iff.mpr (hPx p hp)⟩

omit [Finite G] in
theorem XMem.conj' (hΩ : ConjInvariant Ω) {L : Subgroup G} (hL : XMem Ω x L) {c : G}
    (hc : c ∈ Subgroup.centralizer ({x} : Set G)) : XMem Ω x (conjSub c L) := by
  obtain ⟨hLΩ, hN, P, hP, hPx⟩ := hL
  have hcx : c * x = x * c := Subgroup.mem_centralizer_singleton_iff.mp hc
  refine ⟨hΩ c L hLΩ, ?_, conjSub c P, hP.conj c, ?_⟩
  · rw [mem_normalizer_iff_conjSub_eq] at hN ⊢
    have e : x = c * x * c⁻¹ := by rw [hcx]; group
    rw [e, conjSub_mul, conjSub_mul, conjSub_inv_conjSub, hN]
  · intro p hp
    rw [mem_conjSub_iff] at hp
    have h1 := hPx _ hp
    have hcx' : c⁻¹ * x = x * c⁻¹ := by
      calc c⁻¹ * x = c⁻¹ * (x * c) * c⁻¹ := by group
        _ = c⁻¹ * (c * x) * c⁻¹ := by rw [hcx]
        _ = x * c⁻¹ := by group
    calc p * x = c * (c⁻¹ * p * c) * (c⁻¹ * x) := by group
      _ = c * (c⁻¹ * p * c) * (x * c⁻¹) := by rw [hcx']
      _ = c * ((c⁻¹ * p * c) * x) * c⁻¹ := by group
      _ = c * (x * (c⁻¹ * p * c)) * c⁻¹ := by rw [h1]
      _ = (c * x) * (c⁻¹ * p * c) * c⁻¹ := by group
      _ = (x * c) * (c⁻¹ * p * c) * c⁻¹ := by rw [hcx]
      _ = x * p := by group

theorem isSylow2In_coreAt_iff {L : Subgroup G} (hL : XMem Ω x L) {P : Subgroup G} :
    IsSylow2In P (coreAt x L) ↔
      IsSylow2In P L ∧ P ≤ Subgroup.centralizer ({x} : Set G) := by
  obtain ⟨P₀, hP₀, hP₀x⟩ := XMem.exists_sylow hL
  constructor
  · intro hP
    have hPL : P ≤ L := hP.1.trans (coreAt_le x L)
    have hle : Nat.card P₀ ≤ Nat.card P :=
      hP.natCard_le hP₀.2.1 (le_coreAt x hP₀.2.1 hP₀.1 hP₀x)
    exact ⟨hP₀.of_natCard_le hP.2.1 hPL hle, hP.1.trans (coreAt_le_centralizer x L)⟩
  · rintro ⟨hP, hPx⟩
    exact ⟨le_coreAt x hP.2.1 hP.1 hPx, hP.2.1,
      fun V hV hV2 hPV => hP.2.2 V (hV.trans (coreAt_le x L)) hV2 hPV⟩

theorem isUniqueInvolution_coreAt (h : TypeRFam r Ω) {L : Subgroup G} (hL : XMem Ω x L)
    {z : G} (hz : IsUniqueInvolution L z) : IsUniqueInvolution (coreAt x L) z := by
  obtain ⟨P₀, hP₀, hP₀x⟩ := XMem.exists_sylow hL
  have h8 := Sec6Gen.eight_le_of_mem_RSet h.hyp (mem_RSet_of_isSylow2In hL.1 hP₀)
  have hzP : z ∈ P₀ := T3.mem_of_isPGroup hz hP₀.1 hP₀.2.1 (by omega)
  exact ⟨le_coreAt x hP₀.2.1 hP₀.1 hP₀x hzP, hz.ne_one, hz.sq,
    fun y hy hy2 => hz.unique y (coreAt_le x L hy) hy2⟩

theorem twoGroup_coreAt (h : TypeRFam r Ω) {L : Subgroup G} (hL : L ∈ Ω) :
    IsPGroup 2 (↥(coreAt x L) ⧸ classicalInvolutionOddCore ↥(coreAt x L)) := by
  intro cb
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective cb
  have hcL : (c : G) ∈ L := coreAt_le x L c.2
  obtain ⟨k, hk⟩ := h.twoGroup L hL (QuotientGroup.mk (⟨c, hcL⟩ : ↥L))
  refine ⟨k, ?_⟩
  have h1 : (⟨c, hcL⟩ : ↥L) ^ 2 ^ k ∈ classicalInvolutionOddCore ↥L := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hk
  have h2 : (c : G) ^ 2 ^ k ∈ oddCoreOf L :=
    mem_oddCoreOf_iff.mpr ⟨L.pow_mem hcL _, by simpa using h1⟩
  have h3 : (c : G) ^ 2 ^ k ∈ oddCoreOf (coreAt x L) :=
    inf_oddCoreOf_le (coreAt_le x L) ⟨(coreAt x L).pow_mem c.2 _, h2⟩
  obtain ⟨hmem, h4⟩ := mem_oddCoreOf_iff.mp h3
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  have e : c ^ 2 ^ k = ⟨(c : G) ^ 2 ^ k, hmem⟩ := Subtype.ext (Subgroup.coe_pow _ c _)
  rw [e]
  exact h4

theorem padicValNat_two_inf_le {A B L M : Subgroup G} (hAL : A ≤ L) (hBM : B ≤ M) :
    padicValNat 2 (Nat.card ↥(A ⊓ B)) ≤ padicValNat 2 (Nat.card ↥(L ⊓ M)) := by
  have hd : Nat.card ↥(A ⊓ B) ∣ Nat.card ↥(L ⊓ M) :=
    Subgroup.card_dvd_of_le (inf_le_inf hAL hBM)
  have h0 : Nat.card ↥(A ⊓ B) ≠ 0 := Nat.card_pos.ne'
  have h1 : Nat.card ↥(L ⊓ M) ≠ 0 := Nat.card_pos.ne'
  have := (Nat.factorization_le_iff_dvd h0 h1).mpr hd 2
  rwa [Nat.factorization_def _ Nat.prime_two, Nat.factorization_def _ Nat.prime_two] at this

theorem mem_normalizer_of_commutator_le {L M : Subgroup G} (hLM : ⁅L, M⁆ ≤ L) {m : G}
    (hm : m ∈ M) : m ∈ Subgroup.normalizer (L : Set G) := by
  have hle : conjSub m L ≤ L := by
    intro a ha
    rw [mem_conjSub_iff] at ha
    have hc : ⁅(m⁻¹ * a * m)⁻¹, m⁆ ∈ L :=
      hLM (Subgroup.commutator_mem_commutator (L.inv_mem ha) hm)
    have e : a = (m⁻¹ * a * m) * ⁅(m⁻¹ * a * m)⁻¹, m⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact L.mul_mem ha hc
  exact mem_normalizer_iff_conjSub_eq.mpr (Subgroup.eq_of_le_of_card_ge hle
    (Subgroup.card_map_of_injective (MulAut.conj m).injective).symm.le)


omit [Finite G] in
theorem coreAt_mem_normalizer (h : TypeRFam r Ω) {L : Subgroup G} (hL : L ∈ Ω) {z : G}
    (hz : IsUniqueInvolution L z) {v : G} (hvx : v ∈ Subgroup.centralizer ({x} : Set G))
    (hvz : v * z = z * v) : v ∈ Subgroup.normalizer (coreAt x L : Set G) :=
  mem_normalizer_coreAt x (h.tight L hL z hz (Subgroup.mem_centralizer_singleton_iff.mpr hvz)) hvx

theorem coreAt_omega4 (h : TypeRFam r Ω) {L M : Subgroup G} (hL : L ∈ Ω) (hM : M ∈ Ω)
    (hne : coreAt x L ≠ coreAt x M) :
    padicValNat 2 (Nat.card ↥(coreAt x L ⊓ coreAt x M)) ≤ 1 ∧
      (padicValNat 2 (Nat.card ↥(coreAt x L ⊓ coreAt x M)) = 1 →
        ⁅coreAt x L, coreAt x M⁆ ≤ oddCoreOf (coreAt x L) ⊓ oddCoreOf (coreAt x M)) := by
  have hLM : L ≠ M := fun e => hne (by rw [e])
  obtain ⟨h1, h2⟩ := h.hyp.omega4 L hL M hM hLM
  have hv := padicValNat_two_inf_le (coreAt_le x L) (coreAt_le x M)
  refine ⟨hv.trans h1, fun hv1 => ?_⟩
  have hc := h2 (le_antisymm h1 (hv1 ▸ hv))
  have hLM' : ⁅L, M⁆ ≤ L := hc.trans (inf_le_left.trans (oddCoreOf_le_self L))
  have hML' : ⁅M, L⁆ ≤ M := by
    rw [Subgroup.commutator_comm]
    exact hc.trans (inf_le_right.trans (oddCoreOf_le_self M))
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have hab : ⁅a, b⁆ ∈ oddCoreOf L ⊓ oddCoreOf M :=
    hc (Subgroup.commutator_mem_commutator (coreAt_le x L ha) (coreAt_le x M hb))
  have hbN : b ∈ Subgroup.normalizer (coreAt x L : Set G) :=
    mem_normalizer_coreAt x (mem_normalizer_of_commutator_le hLM' (coreAt_le x M hb))
      (coreAt_le_centralizer x M hb)
  have haN : a ∈ Subgroup.normalizer (coreAt x M : Set G) :=
    mem_normalizer_coreAt x (mem_normalizer_of_commutator_le hML' (coreAt_le x L ha))
      (coreAt_le_centralizer x L ha)
  have habL : ⁅a, b⁆ ∈ coreAt x L := by
    have h3 : b * a⁻¹ * b⁻¹ ∈ coreAt x L :=
      (Subgroup.mem_normalizer_iff.mp hbN a⁻¹).mp ((coreAt x L).inv_mem ha)
    have e : ⁅a, b⁆ = a * (b * a⁻¹ * b⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (coreAt x L).mul_mem ha h3
  have habM : ⁅a, b⁆ ∈ coreAt x M := by
    have h3 : a * b * a⁻¹ ∈ coreAt x M := (Subgroup.mem_normalizer_iff.mp haN b).mp hb
    have e : ⁅a, b⁆ = (a * b * a⁻¹) * b⁻¹ := by
      simp only [commutatorElement_def]
    rw [e]
    exact (coreAt x M).mul_mem h3 ((coreAt x M).inv_mem hb)
  exact ⟨inf_oddCoreOf_le (coreAt_le x L) ⟨habL, hab.1⟩,
    inf_oddCoreOf_le (coreAt_le x M) ⟨habM, hab.2⟩⟩

end Members

end CFSG.ClassicalInvolution.Q3.TL4
