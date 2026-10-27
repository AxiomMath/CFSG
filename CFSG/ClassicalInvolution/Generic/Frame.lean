module

public import CFSG.ClassicalInvolution.Generic.SL2Involution

public section

namespace CFSG.ClassicalInvolution.Generic

open scoped MatrixGroups
open CFSG.ComponentClassification.CatalogueBHigherLinearAction

variable {F : Type*} [Field F] {G : Type*} [Group G]

@[expose] def conjSub (n : G) (K : Subgroup G) : Subgroup G :=
  K.map (MulAut.conj n).toMonoidHom

theorem mem_conjSub_iff {n : G} {K : Subgroup G} {x : G} :
    x ∈ conjSub n K ↔ n⁻¹ * x * n ∈ K := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro h
    exact ⟨_, h, by simp [mul_assoc]⟩

theorem conj_mem_conjSub {n : G} {K : Subgroup G} {x : G} (hx : x ∈ K) :
    n * x * n⁻¹ ∈ conjSub n K :=
  ⟨x, hx, by simp⟩

@[simp] theorem conjSub_one (K : Subgroup G) : conjSub 1 K = K := by
  ext x
  simp [mem_conjSub_iff]

theorem conjSub_mul (a b : G) (K : Subgroup G) : conjSub (a * b) K = conjSub a (conjSub b K) := by
  ext x
  simp only [mem_conjSub_iff, mul_inv_rev]
  rw [show b⁻¹ * a⁻¹ * x * (a * b) = b⁻¹ * (a⁻¹ * x * a) * b by group]

theorem conjSub_conjSub_inv (a : G) (K : Subgroup G) : conjSub a (conjSub a⁻¹ K) = K := by
  rw [← conjSub_mul, mul_inv_cancel, conjSub_one]

theorem conjSub_inv_conjSub (a : G) (K : Subgroup G) : conjSub a⁻¹ (conjSub a K) = K := by
  rw [← conjSub_mul, inv_mul_cancel, conjSub_one]

theorem conjSub_eq_self_of_mem {n : G} {K : Subgroup G} (hn : n ∈ K) : conjSub n K = K := by
  ext x
  rw [mem_conjSub_iff]
  constructor
  · intro h
    have := K.mul_mem (K.mul_mem hn h) (K.inv_mem hn)
    simpa [mul_assoc] using this
  · intro h
    exact K.mul_mem (K.mul_mem (K.inv_mem hn) h) hn

theorem conjSub_injective (n : G) : Function.Injective (conjSub n : Subgroup G → Subgroup G) :=
  Function.LeftInverse.injective (g := conjSub n⁻¹) (conjSub_inv_conjSub n)

theorem conjSub_mono {n : G} {K L : Subgroup G} (h : K ≤ L) : conjSub n K ≤ conjSub n L :=
  Subgroup.map_mono h

theorem conjSub_ne_of_ne {K L : Subgroup G} {w : G} (hw : w ∈ K) (hKL : K ≠ L) :
    conjSub w L ≠ K := by
  intro h
  apply hKL
  calc K = conjSub w⁻¹ (conjSub w L) := by rw [h, conjSub_eq_self_of_mem (K.inv_mem hw)]
    _ = L := conjSub_inv_conjSub _ _

@[expose] def Commutes (K L : Subgroup G) : Prop := ∀ x ∈ K, ∀ y ∈ L, x * y = y * x

theorem Commutes.symm {K L : Subgroup G} (h : Commutes K L) : Commutes L K :=
  fun x hx y hy => (h y hy x hx).symm

theorem commutes_comm {K L : Subgroup G} : Commutes K L ↔ Commutes L K :=
  ⟨Commutes.symm, Commutes.symm⟩

theorem Commutes.conjSub {K L : Subgroup G} (h : Commutes K L) (n : G) :
    Commutes (conjSub n K) (conjSub n L) := by
  intro x hx y hy
  rw [mem_conjSub_iff] at hx hy
  have := h _ hx _ hy
  calc x * y = n * ((n⁻¹ * x * n) * (n⁻¹ * y * n)) * n⁻¹ := by group
    _ = n * ((n⁻¹ * y * n) * (n⁻¹ * x * n)) * n⁻¹ := by rw [this]
    _ = y * x := by group

theorem commutes_conjSub_iff {K L : Subgroup G} (n : G) :
    Commutes (conjSub n K) (conjSub n L) ↔ Commutes K L := by
  refine ⟨fun h => ?_, fun h => h.conjSub n⟩
  have := h.conjSub n⁻¹
  rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at this

theorem conjSub_eq_of_mem_of_commutes {K L : Subgroup G} {x : G} (hx : x ∈ K) (h : Commutes K L) :
    conjSub x L = L := by
  ext y
  rw [mem_conjSub_iff]
  constructor
  · intro hy
    have h1 := h x hx _ hy
    have h2 : y * x = (x⁻¹ * y * x) * x := by
      have : x * (x⁻¹ * y * x) = y * x := by group
      rw [← this, h1]
    have h3 : y = x⁻¹ * y * x := mul_right_cancel h2
    rwa [← h3] at hy
  · intro hy
    have h1 := h x hx y hy
    have : x⁻¹ * y * x = y := by
      rw [mul_assoc, ← h1, ← mul_assoc, inv_mul_cancel, one_mul]
    rwa [this]

structure IsUniqueInvolution (K : Subgroup G) (z : G) : Prop where
  mem : z ∈ K
  ne_one : z ≠ 1
  sq : z * z = 1
  unique : ∀ y ∈ K, y * y = 1 → y = 1 ∨ y = z

namespace IsUniqueInvolution

variable {K : Subgroup G} {z : G}

theorem eq (h : IsUniqueInvolution K z) {z' : G} (h' : IsUniqueInvolution K z') : z = z' :=
  ((h.unique z' h'.mem h'.sq).resolve_left h'.ne_one).symm

theorem conj (h : IsUniqueInvolution K z) (n : G) :
    IsUniqueInvolution (conjSub n K) (n * z * n⁻¹) where
  mem := conj_mem_conjSub h.mem
  ne_one := by
    intro h1
    apply h.ne_one
    have := congrArg (fun t => n⁻¹ * t * n) h1
    simpa [mul_assoc] using this
  sq := by
    calc n * z * n⁻¹ * (n * z * n⁻¹) = n * (z * z) * n⁻¹ := by group
      _ = 1 := by rw [h.sq]; group
  unique := by
    intro y hy hy2
    rw [mem_conjSub_iff] at hy
    have h2 : (n⁻¹ * y * n) * (n⁻¹ * y * n) = 1 := by
      calc (n⁻¹ * y * n) * (n⁻¹ * y * n) = n⁻¹ * (y * y) * n := by group
        _ = 1 := by rw [hy2]; group
    have hy' : y = n * (n⁻¹ * y * n) * n⁻¹ := by group
    rcases h.unique _ hy h2 with h3 | h3
    · left
      rw [hy', h3]
      group
    · right
      rw [hy', h3]

theorem conj_eq (h : IsUniqueInvolution K z) {n : G} (hn : conjSub n K = K) :
    n * z * n⁻¹ = z := by
  have := h.conj n
  rw [hn] at this
  exact (h.eq this).symm

theorem commute_of_commutes (h : IsUniqueInvolution K z) {L : Subgroup G} (hKL : Commutes K L)
    {y : G} (hy : y ∈ L) : z * y = y * z :=
  hKL z h.mem y hy

end IsUniqueInvolution

theorem DiagData.isUniqueInvolution [Finite F] {φ : SL(2, F) →* G} {E : Subgroup G}
    (hD : DiagData φ E) (hodd : Odd (Nat.card F)) : IsUniqueInvolution φ.range (φ (-1)) where
  mem := ⟨-1, rfl⟩
  ne_one := fun h => sl2_neg_one_ne_one hodd (hD.inj (h.trans (map_one φ).symm))
  sq := by
    rw [← map_mul]
    have : (-1 : SL(2, F)) * -1 = 1 := by
      calc (-1 : SL(2, F)) * -1 = -1 * (-1)⁻¹ := by rw [neg_one_inv]
        _ = 1 := mul_inv_cancel _
    rw [this, map_one]
  unique := by
    rintro _ ⟨s, rfl⟩ hs
    rw [← map_mul] at hs
    have hs' : s * s = 1 := hD.inj (hs.trans (map_one φ).symm)
    rcases sl2_sq_eq_one (CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F hodd) hs' with
      h | h
    · exact Or.inl (by rw [h, map_one])
    · exact Or.inr (by rw [h])

theorem mem_conj_iff_of_mem_normalizer {n : G} {E : Subgroup G}
    (hn : n ∈ Subgroup.normalizer (E : Set G)) (x : G) : n⁻¹ * x * n ∈ E ↔ x ∈ E := by
  have := Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (E : Set G)).inv_mem hn) x
  simpa using this.symm

theorem conjSub_eq_of_mem_normalizer {n : G} {E : Subgroup G}
    (hn : n ∈ Subgroup.normalizer (E : Set G)) : conjSub n E = E := by
  ext x
  rw [mem_conjSub_iff]
  exact mem_conj_iff_of_mem_normalizer hn x

theorem axisSub_conjSub {n : G} {E : Subgroup G} (hn : n ∈ Subgroup.normalizer (E : Set G))
    (K : Subgroup G) : axisSub E (conjSub n K) = conjSub n (axisSub E K) := by
  ext x
  rw [mem_conjSub_iff, mem_axisSub_iff, mem_axisSub_iff, mem_conj_iff_of_mem_normalizer hn]
  refine and_congr_right fun _ => ⟨fun h k hk => ?_, fun h k hk => ?_⟩
  · have := h (n * k * n⁻¹) (conj_mem_conjSub hk)
    calc k * (n⁻¹ * x * n) = n⁻¹ * ((n * k * n⁻¹) * x) * n := by group
      _ = n⁻¹ * (x * (n * k * n⁻¹)) * n := by rw [this]
      _ = n⁻¹ * x * n * k := by group
  · rw [mem_conjSub_iff] at hk
    have := h _ hk
    calc k * x = n * ((n⁻¹ * k * n) * (n⁻¹ * x * n)) * n⁻¹ := by group
      _ = n * ((n⁻¹ * x * n) * (n⁻¹ * k * n)) * n⁻¹ := by rw [this]
      _ = x * k := by group

theorem relIndex_conjSub (n : G) (A B : Subgroup G) :
    (conjSub n A).relIndex (conjSub n B) = A.relIndex B :=
  Subgroup.relIndex_map_map_of_injective A B (MulAut.conj n).injective

theorem DiagData.conj {φ : SL(2, F) →* G} {E : Subgroup G} (hD : DiagData φ E) {n : G}
    (hn : n ∈ Subgroup.normalizer (E : Set G)) :
    DiagData ((MulAut.conj n).toMonoidHom.comp φ) E where
  inj := (MulAut.conj n).injective.comp hD.inj
  comm := hD.comm
  sq := hD.sq
  neg_mem := by
    have := (Subgroup.mem_normalizer_iff.mp hn _).mp hD.neg_mem
    simpa using this
  diag := by
    intro e he
    have he' : n⁻¹ * e * n ∈ E := (mem_conj_iff_of_mem_normalizer hn e).mpr he
    obtain ⟨g, hg⟩ := hD.diag _ he'
    refine ⟨g, fun s => ?_⟩
    have := hg s
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    calc e * (n * φ s * n⁻¹) * e⁻¹ = n * ((n⁻¹ * e * n) * φ s * (n⁻¹ * e * n)⁻¹) * n⁻¹ := by group
      _ = n * φ (slConjugation 2 F g s) * n⁻¹ := by rw [this]
  index_two := by
    have hr : ((MulAut.conj n).toMonoidHom.comp φ).range = conjSub n φ.range :=
      MonoidHom.range_comp _ _
    have h2 := relIndex_conjSub n (axisSub E φ.range) E
    rw [conjSub_eq_of_mem_normalizer hn] at h2
    rw [hr, axisSub_conjSub hn, h2]
    exact hD.index_two

@[expose] def normPart (K E : Subgroup G) : Subgroup G := K ⊓ Subgroup.normalizer (E : Set G)

@[expose] def centPart (K E : Subgroup G) : Subgroup G := K ⊓ Subgroup.centralizer (E : Set G)

theorem mem_normPart_iff {K E : Subgroup G} {x : G} :
    x ∈ normPart K E ↔ x ∈ K ∧ x ∈ Subgroup.normalizer (E : Set G) := Subgroup.mem_inf

theorem mem_centPart_iff {K E : Subgroup G} {x : G} :
    x ∈ centPart K E ↔ x ∈ K ∧ ∀ e ∈ E, e * x = x * e := by
  rw [centPart, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  exact Iff.rfl

theorem centPart_le_normPart (K E : Subgroup G) : centPart K E ≤ normPart K E :=
  inf_le_inf_left _ (Subgroup.centralizer_le_normalizer (s := (E : Set G)))

theorem normPart_le_left (K E : Subgroup G) : normPart K E ≤ K := inf_le_left

theorem centPart_le_left (K E : Subgroup G) : centPart K E ≤ K := inf_le_left

theorem centPart_range (φ : SL(2, F) →* G) (E : Subgroup G) :
    centPart φ.range E = (centSub φ E).map φ := by
  ext x
  constructor
  · rintro ⟨⟨s, rfl⟩, hx⟩
    exact ⟨s, hx, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨⟨s, rfl⟩, hs⟩

theorem normPart_range (φ : SL(2, F) →* G) (E : Subgroup G) :
    normPart φ.range E = (normSub φ E).map φ := by
  ext x
  constructor
  · rintro ⟨⟨s, rfl⟩, hx⟩
    exact ⟨s, hx, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨⟨s, rfl⟩, hs⟩

theorem DiagData.exists_preimage {φ : SL(2, F) →* G} {E : Subgroup G} {w : G}
    (hw : w ∈ normPart φ.range E) (hw' : w ∉ centPart φ.range E) :
    ∃ s : SL(2, F), φ s = w ∧ s ∈ normSub φ E ∧ s ∉ centSub φ E := by
  rw [normPart_range] at hw
  rw [centPart_range] at hw'
  obtain ⟨s, hs, rfl⟩ := hw
  exact ⟨s, rfl, hs, fun h => hw' ⟨s, h, rfl⟩⟩

variable (F) in
@[expose] def InSigma (E K : Subgroup G) : Prop :=
  ∃ φ : SL(2, F) →* G, φ.range = K ∧ DiagData φ E

namespace InSigma

variable {E K : Subgroup G}

theorem conj (hK : InSigma F E K) {n : G} (hn : n ∈ Subgroup.normalizer (E : Set G)) :
    InSigma F E (conjSub n K) := by
  obtain ⟨φ, rfl, hD⟩ := hK
  exact ⟨_, MonoidHom.range_comp _ _, hD.conj hn⟩

theorem conjSub_le (hK : InSigma F E K) {e : G} (he : e ∈ E) : conjSub e K ≤ K := by
  obtain ⟨φ, rfl, hD⟩ := hK
  obtain ⟨g, hg⟩ := hD.diag e he
  rintro _ ⟨_, ⟨s, rfl⟩, rfl⟩
  exact ⟨slConjugation 2 F g s, (hg s).symm⟩

theorem conjSub_eq (hK : InSigma F E K) {e : G} (he : e ∈ E) : conjSub e K = K := by
  refine le_antisymm (hK.conjSub_le he) ?_
  have := conjSub_mono (n := e) (hK.conjSub_le (E.inv_mem he))
  rwa [conjSub_conjSub_inv] at this

variable [Finite F]

theorem natCard_normPart (hK : InSigma F E K) (hodd : Odd (Nat.card F))
    (h5 : 5 ≤ Nat.card F) : Nat.card (normPart K E) = 2 * Nat.card (centPart K E) := by
  obtain ⟨φ, rfl, hD⟩ := hK
  rw [centPart_range, normPart_range, Subgroup.card_map_of_injective hD.inj,
    Subgroup.card_map_of_injective hD.inj]
  exact hD.natCard_normSub hodd h5

theorem relIndex_centPart_normPart (hK : InSigma F E K) (hodd : Odd (Nat.card F))
    (h5 : 5 ≤ Nat.card F) : (centPart K E).relIndex (normPart K E) = 2 := by
  obtain ⟨φ, rfl, hD⟩ := hK
  rw [centPart_range, normPart_range, Subgroup.relIndex_map_map_of_injective _ _ hD.inj]
  exact hD.relIndex_centSub_normSub hodd h5

theorem exists_mem_normPart_not_mem_centPart (hK : InSigma F E K) (hodd : Odd (Nat.card F))
    (h5 : 5 ≤ Nat.card F) : ∃ w ∈ normPart K E, w ∉ centPart K E := by
  obtain ⟨φ, rfl, hD⟩ := hK
  obtain ⟨s, hs, hs'⟩ := hD.exists_mem_normSub_not_mem_centSub hodd h5
  refine ⟨φ s, ?_, ?_⟩
  · rw [normPart_range]
    exact ⟨s, hs, rfl⟩
  · rw [centPart_range]
    rintro ⟨t, ht, hts⟩
    exact hs' (by rwa [← hD.inj hts])

theorem sq_eq_of_mem (hK : InSigma F E K) (hodd : Odd (Nat.card F)) {z : G}
    (hz : IsUniqueInvolution K z) {w : G} (hw : w ∈ normPart K E) (hw' : w ∉ centPart K E) :
    w * w = z := by
  obtain ⟨φ, rfl, hD⟩ := hK
  obtain ⟨s, rfl, hs, hs'⟩ := DiagData.exists_preimage hw hw'
  rw [← map_mul, hD.sq_eq_neg_one_of_mem hodd hs hs']
  exact hz.eq (hD.isUniqueInvolution hodd) |>.symm

theorem conj_inv_of_mem (hK : InSigma F E K) (hodd : Odd (Nat.card F)) {w c : G}
    (hw : w ∈ normPart K E) (hw' : w ∉ centPart K E) (hc : c ∈ centPart K E) :
    w * c * w⁻¹ = c⁻¹ := by
  obtain ⟨φ, rfl, hD⟩ := hK
  obtain ⟨s, rfl, hs, hs'⟩ := DiagData.exists_preimage hw hw'
  rw [centPart_range] at hc
  obtain ⟨k, hk, rfl⟩ := hc
  rw [← map_inv, ← map_mul, ← map_inv, ← map_mul, hD.mul_inv_mul_inv hodd hs hs' hk]

theorem inv_mul_mem_centPart (hK : InSigma F E K) (hodd : Odd (Nat.card F)) {w w' : G}
    (hw : w ∈ normPart K E) (hw1 : w ∉ centPart K E) (hw' : w' ∈ normPart K E)
    (hw'1 : w' ∉ centPart K E) : w⁻¹ * w' ∈ centPart K E := by
  obtain ⟨φ, rfl, hD⟩ := hK
  obtain ⟨s, rfl, hs, hs'⟩ := DiagData.exists_preimage hw hw1
  obtain ⟨t, rfl, ht, ht'⟩ := DiagData.exists_preimage hw' hw'1
  rw [centPart_range]
  exact ⟨s⁻¹ * t, hD.inv_mul_mem_centSub hodd hs hs' ht ht', by simp⟩

theorem orderOf_eq_four (hK : InSigma F E K) (hodd : Odd (Nat.card F)) {w : G}
    (hw : w ∈ normPart K E) (hw' : w ∉ centPart K E) : orderOf w = 4 := by
  obtain ⟨φ, rfl, hD⟩ := hK
  obtain ⟨s, rfl, hs, hs'⟩ := DiagData.exists_preimage hw hw'
  exact hD.orderOf_phi_eq_four hodd hs hs'

theorem conj_eq_of_mem_axis {w : G} (hw : w ∈ K) {x : G} (hx : x ∈ axisSub E K) :
    w * x * w⁻¹ = x := by
  rw [mem_axisSub_iff] at hx
  rw [hx.2 w hw]
  group

theorem conj_eq_mul_of_not_mem_axis (hK : InSigma F E K) (hodd : Odd (Nat.card F)) {z : G}
    (hz : IsUniqueInvolution K z) {w : G} (hw : w ∈ normPart K E) (hw' : w ∉ centPart K E)
    {x : G} (hx : x ∈ E) (hx' : x ∉ axisSub E K) : w * x * w⁻¹ = x * z := by
  obtain ⟨φ, rfl, hD⟩ := hK
  obtain ⟨s, rfl, hs, hs'⟩ := DiagData.exists_preimage hw hw'
  rw [hD.conj_not_mem_axis hodd hs hs' hx hx']
  rw [(hz.eq (hD.isUniqueInvolution hodd))]

omit [Finite F] in
theorem exists_split (hK : InSigma F E K) :
    ∃ a ∈ E, a ∉ axisSub E K ∧ ∀ x ∈ E, x ∈ axisSub E K ∨ x * a ∈ axisSub E K := by
  obtain ⟨φ, rfl, hD⟩ := hK
  obtain ⟨W⟩ := hD.nonempty_witness
  exact ⟨W.a, W.ha, W.na, W.split⟩

omit [Finite F] in
theorem exists_mem_not_mem_axis (hK : InSigma F E K) : ∃ a ∈ E, a ∉ axisSub E K := by
  obtain ⟨φ, rfl, hD⟩ := hK
  obtain ⟨W⟩ := hD.nonempty_witness
  exact ⟨W.a, W.ha, W.na⟩

theorem unique_involution_mem_axis (hK : InSigma F E K) (hodd : Odd (Nat.card F)) {z : G}
    (hz : IsUniqueInvolution K z) : z ∈ axisSub E K := by
  obtain ⟨φ, rfl, hD⟩ := hK
  rw [hz.eq (hD.isUniqueInvolution hodd), mem_axisSub_iff]
  refine ⟨hD.neg_mem, ?_⟩
  rintro _ ⟨s, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  exact mul_neg_one_comm s

theorem unique_involution_mem (hK : InSigma F E K) (hodd : Odd (Nat.card F)) {z : G}
    (hz : IsUniqueInvolution K z) : z ∈ E :=
  (mem_axisSub_iff.mp (hK.unique_involution_mem_axis hodd hz)).1

end InSigma

@[expose] def ConjInvariant (Ω : Set (Subgroup G)) : Prop :=
  ∀ (n : G) (K : Subgroup G), K ∈ Ω → conjSub n K ∈ Ω

variable (F) in
@[expose] def sigmaSet (Ω : Set (Subgroup G)) (E : Subgroup G) : Set (Subgroup G) :=
  {K | K ∈ Ω ∧ InSigma F E K}

@[expose] def zSet (S : Set (Subgroup G)) : Set G :=
  {z | ∃ K ∈ S, IsUniqueInvolution K z}

@[expose] def nonCommGraph (S : Set (Subgroup G)) : SimpleGraph ↥S :=
  SimpleGraph.fromRel fun K L => ¬ Commutes (K : Subgroup G) (L : Subgroup G)

theorem nonCommGraph_adj {S : Set (Subgroup G)} {K L : ↥S} :
    (nonCommGraph S).Adj K L ↔ K ≠ L ∧ ¬ Commutes (K : Subgroup G) (L : Subgroup G) := by
  simp only [nonCommGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨h1, h2 | h2⟩
    · exact ⟨h1, h2⟩
    · exact ⟨h1, fun h => h2 h.symm⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, Or.inl h2⟩

@[expose] def NonCommConnected (S : Set (Subgroup G)) : Prop :=
  (nonCommGraph S).Connected

variable (F) in
structure ToralFrame (Ω : Set (Subgroup G)) (E : Subgroup G) (S : Set (Subgroup G)) : Prop where
  odd : Odd (Nat.card F)
  five : 5 ≤ Nat.card F
  inv : ConjInvariant Ω
  elem : ∀ x ∈ E, x * x = 1
  eq_sigma : S = sigmaSet F Ω E
  gen : Subgroup.closure (zSet S) = E
  card : 8 ≤ Nat.card E

variable (F) in
@[expose] def IsSaturated (Ω : Set (Subgroup G)) (S : Set (Subgroup G)) : Prop :=
  ∀ (E' : Subgroup G) (S' : Set (Subgroup G)), ToralFrame F Ω E' S' → S'.ncard ≤ S.ncard

namespace ToralFrame

variable {Ω : Set (Subgroup G)} {E : Subgroup G} {S : Set (Subgroup G)}

theorem finite (Fr : ToralFrame F Ω E S) : Finite F := by
  by_contra h
  rw [not_finite_iff_infinite] at h
  have := Fr.odd
  rw [Nat.card_eq_zero_of_infinite] at this
  exact absurd this (by decide)

theorem subset (Fr : ToralFrame F Ω E S) : S ⊆ Ω := by
  rw [Fr.eq_sigma]
  exact fun _ h => h.1

theorem mem_iff (Fr : ToralFrame F Ω E S) {K : Subgroup G} :
    K ∈ S ↔ K ∈ Ω ∧ InSigma F E K := by
  rw [Fr.eq_sigma]
  exact Iff.rfl

theorem inSigma (Fr : ToralFrame F Ω E S) {K : Subgroup G} (hK : K ∈ S) : InSigma F E K :=
  (Fr.mem_iff.mp hK).2

theorem conj_mem (Fr : ToralFrame F Ω E S) {n : G} (hn : n ∈ Subgroup.normalizer (E : Set G))
    {K : Subgroup G} (hK : K ∈ S) : conjSub n K ∈ S :=
  Fr.mem_iff.mpr ⟨Fr.inv n K (Fr.subset hK), (Fr.inSigma hK).conj hn⟩

theorem exists_isUniqueInvolution (Fr : ToralFrame F Ω E S) {K : Subgroup G} (hK : K ∈ S) :
    ∃ z, IsUniqueInvolution K z := by
  have := Fr.finite
  obtain ⟨φ, rfl, hD⟩ := Fr.inSigma hK
  exact ⟨_, hD.isUniqueInvolution Fr.odd⟩

theorem mem_of_isUniqueInvolution (Fr : ToralFrame F Ω E S) {K : Subgroup G} (hK : K ∈ S) {z : G}
    (hz : IsUniqueInvolution K z) : z ∈ E := by
  have := Fr.finite
  exact (Fr.inSigma hK).unique_involution_mem Fr.odd hz

theorem z_mem_axisSub_of_commutes (Fr : ToralFrame F Ω E S) {K L : Subgroup G} (hK : K ∈ S)
    (hc : Commutes K L) {z : G} (hz : IsUniqueInvolution K z) : z ∈ axisSub E L :=
  mem_axisSub_iff.mpr ⟨Fr.mem_of_isUniqueInvolution hK hz,
    fun k hk => (hc z hz.mem k hk).symm⟩

theorem exists_ne (Fr : ToralFrame F Ω E S) : ∃ K ∈ S, ∃ L ∈ S, K ≠ L := by
  by_contra hne
  push Not at hne
  rcases S.eq_empty_or_nonempty with hS | ⟨K₀, hK₀⟩
  · have h1 : E = ⊥ := by
      rw [← Fr.gen, hS]
      simp [zSet]
    have := Fr.card
    rw [h1, Subgroup.card_bot] at this
    omega
  · obtain ⟨z₀, hz₀⟩ := Fr.exists_isUniqueInvolution hK₀
    have h1 : E ≤ Subgroup.zpowers z₀ := by
      rw [← Fr.gen, Subgroup.closure_le]
      rintro z ⟨K, hK, hz⟩
      have hKK : K = K₀ := hne K hK K₀ hK₀
      subst hKK
      rw [SetLike.mem_coe, hz.eq hz₀]
      exact Subgroup.mem_zpowers z₀
    have h2 : Nat.card E ≤ 2 := by
      have hfin : IsOfFinOrder z₀ :=
        isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by norm_num, by rw [pow_two]; exact hz₀.sq⟩
      have := hfin.finite_zpowers
      have h3 : Nat.card (Subgroup.zpowers z₀) ≤ 2 := by
        rw [Nat.card_zpowers]
        exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hz₀.sq))
      exact (Subgroup.card_le_of_le h1).trans h3
    have := Fr.card
    omega

end ToralFrame

end CFSG.ClassicalInvolution.Generic
