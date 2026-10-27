module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoOddLie49
import CFSG.LocalAnalysis.ComponentClassification.TightEmbeddingConjugate

public section

namespace CFSG.ComponentClassification.RankTwoOddLie

open Subgroup CFSG.Open CFSG.ComponentClassification.AS76b CFSG.ABGLocalTools
  CFSG.ComponentClassification.AschbacherTightEmbedding
open scoped commutatorElement MatrixGroups

variable {H : Type} [Group H]

def oddCenter (B : Subgroup H) : Subgroup H where
  carrier := {z | z ∈ B ∧ (∀ b ∈ B, b * z = z * b) ∧ Odd (orderOf z)}
  one_mem' := ⟨B.one_mem, fun b _ => by simp, by simp⟩
  mul_mem' := by
    rintro x y ⟨hxB, hxc, hxo⟩ ⟨hyB, hyc, hyo⟩
    refine ⟨B.mul_mem hxB hyB, fun b hb => ?_, ?_⟩
    · rw [← mul_assoc, hxc b hb, mul_assoc, hyc b hb, ← mul_assoc]
    · have hcomm : Commute x y := (hxc y hyB).symm
      exact ((hxo.mul hyo).of_dvd_nat (Nat.lcm_dvd_mul _ _)).of_dvd_nat hcomm.orderOf_mul_dvd_lcm
  inv_mem' := by
    rintro x ⟨hxB, hxc, hxo⟩
    refine ⟨B.inv_mem hxB, fun b hb => ?_, by rwa [orderOf_inv]⟩
    have h := hxc b hb
    calc b * x⁻¹ = x⁻¹ * (x * b) * x⁻¹ := by group
      _ = x⁻¹ * (b * x) * x⁻¹ := by rw [h]
      _ = x⁻¹ * b := by group

theorem mem_oddCenter_iff {B : Subgroup H} {z : H} :
    z ∈ oddCenter B ↔ z ∈ B ∧ (∀ b ∈ B, b * z = z * b) ∧ Odd (orderOf z) := Iff.rfl

theorem oddCenter_le (B : Subgroup H) : oddCenter B ≤ B := fun _ h => h.1

theorem odd_card_oddCenter [Finite H] (B : Subgroup H) : Odd (Nat.card (oddCenter B)) := by
  by_contra hev
  rw [Nat.not_odd_iff_even] at hev
  obtain ⟨⟨z, hz⟩, hz2⟩ := exists_prime_orderOf_dvd_card' (G := oddCenter B) 2
    (even_iff_two_dvd.mp hev)
  have : orderOf z = 2 := by rwa [Subgroup.orderOf_mk] at hz2
  have hodd := hz.2.2
  rw [this] at hodd
  exact absurd hodd (by decide)

theorem normalizer_le_normalizer_oddCenter (B : Subgroup H) :
    normalizer (B : Set H) ≤ normalizer (oddCenter B : Set H) := by
  have key : ∀ g ∈ normalizer (B : Set H), ∀ z ∈ oddCenter B, g * z * g⁻¹ ∈ oddCenter B := by
    rintro g hg z ⟨hzB, hzc, hzo⟩
    refine ⟨(mem_normalizer_iff.mp hg z).mp hzB, fun b hb => ?_, ?_⟩
    · have hb' : g⁻¹ * b * g ∈ B := by
        have := (mem_normalizer_iff.mp (inv_mem hg) b).mp hb
        simpa using this
      have h := hzc _ hb'
      calc b * (g * z * g⁻¹) = g * ((g⁻¹ * b * g) * z) * g⁻¹ := by group
        _ = g * (z * (g⁻¹ * b * g)) * g⁻¹ := by rw [h]
        _ = g * z * g⁻¹ * b := by group
    · rw [show g * z * g⁻¹ = MulAut.conj g z from rfl, MulEquiv.orderOf_eq]
      exact hzo
  intro g hg
  rw [mem_normalizer_iff]
  intro z
  refine ⟨key g hg z, fun hz => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hz
  simpa [mul_assoc] using this

theorem mem_centralizer_of_perfect {B : Subgroup H} (hB : commutator B = ⊤) {c : H}
    (hc : c ∈ normalizer (B : Set H))
    (hz : ∀ b ∈ B, ∀ b' ∈ B, c * b * c⁻¹ * b⁻¹ * b' = b' * (c * b * c⁻¹ * b⁻¹)) :
    c ∈ centralizer (B : Set H) := by
  have hcB : ∀ b ∈ B, c * b * c⁻¹ ∈ B := fun b hb => (mem_normalizer_iff.mp hc b).mp hb
  let u : B → B := fun b => ⟨(b : H)⁻¹ * (c * b * c⁻¹), B.mul_mem (B.inv_mem b.2) (hcB b b.2)⟩
  have hu : ∀ b : B, u b ∈ center B := by
    intro b
    rw [Subgroup.mem_center_iff]
    intro b'
    apply Subtype.ext
    have h2 := hz b b.2 b b.2
    have e : (b : H)⁻¹ * (c * b * c⁻¹) = c * b * c⁻¹ * (b : H)⁻¹ := by
      calc (b : H)⁻¹ * (c * b * c⁻¹) = (b : H)⁻¹ * ((c * b * c⁻¹ * (b : H)⁻¹) * b) := by group
        _ = (b : H)⁻¹ * (b * (c * b * c⁻¹ * (b : H)⁻¹)) := by rw [h2]
        _ = c * b * c⁻¹ * (b : H)⁻¹ := by group
    simp only [Subgroup.coe_mul, u]
    rw [e]
    exact (hz b b.2 b' b'.2).symm
  have hconj : ∀ b : B, ((b * u b : B) : H) = c * b * c⁻¹ := fun b => by
    simp only [Subgroup.coe_mul, u]
    group
  have hcomm : commutator B ≤ (centralizer ({c} : Set H)).subgroupOf B := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [mem_subgroupOf, mem_centralizer_singleton_iff]
    have h1 := congrArg Subtype.val (commutatorElement_mul_center x y (hu x) (hu y))
    have e1 : ((⁅x, y⁆ : B) : H) = ⁅(x : H), (y : H)⁆ := map_commutatorElement B.subtype x y
    have e2 : ((⁅x * u x, y * u y⁆ : B) : H) = c * ⁅(x : H), (y : H)⁆ * c⁻¹ := by
      rw [show ((⁅x * u x, y * u y⁆ : B) : H) = ⁅((x * u x : B) : H), ((y * u y : B) : H)⁆ from
        map_commutatorElement B.subtype _ _, hconj, hconj]
      exact (map_commutatorElement (MulAut.conj c) (x : H) (y : H)).symm
    rw [e2, e1] at h1
    rw [e1]
    calc ⁅(x : H), (y : H)⁆ * c = c * ⁅(x : H), (y : H)⁆ * c⁻¹ * c := by rw [h1]
      _ = c * ⁅(x : H), (y : H)⁆ := by group
  rw [hB] at hcomm
  rw [mem_centralizer_iff]
  intro b hb
  have := hcomm (Subgroup.mem_top ⟨b, hb⟩)
  rw [mem_subgroupOf, mem_centralizer_singleton_iff] at this
  exact this

abbrev imgIn {H' : Type} [Group H'] {M : Subgroup H} (ψ : ↥M →* H') (S : Subgroup H) :
    Subgroup H' :=
  (S.subgroupOf M).map ψ

section Image

variable {H' : Type} [Group H'] {M : Subgroup H} {ψ : ↥M →* H'}

theorem mem_imgIn {S : Subgroup H} {y : H'} :
    y ∈ imgIn ψ S ↔ ∃ m : M, (m : H) ∈ S ∧ ψ m = y := by
  simp only [imgIn, mem_map, mem_subgroupOf]

theorem mem_imgIn_of (ψ : ↥M →* H') {S : Subgroup H} {m : M} (hm : (m : H) ∈ S) :
    ψ m ∈ imgIn ψ S :=
  mem_map_of_mem _ (mem_subgroupOf.mpr hm)

theorem isElemAbelian_imgIn (ψ : ↥M →* H') {T : Subgroup H} (hT : IsElemAbelian 2 T) :
    IsElemAbelian 2 (imgIn ψ T) := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨a, ha⟩ := a
    obtain ⟨b, hb⟩ := b
    obtain ⟨m, hm, rfl⟩ := mem_imgIn.mp ha
    obtain ⟨n, hn, rfl⟩ := mem_imgIn.mp hb
    have h := congrArg Subtype.val (hT.1.is_comm.comm ⟨_, hm⟩ ⟨_, hn⟩)
    simp only [Subgroup.coe_mul] at h ⊢
    rw [← map_mul, ← map_mul]
    exact congrArg ψ (Subtype.ext h)
  · obtain ⟨m, hm, rfl⟩ := mem_imgIn.mp hx
    have : m ^ 2 = 1 := Subtype.ext (by simpa using hT.2 _ hm)
    rw [← map_pow, this, map_one]

theorem card_imgIn (ψ : ↥M →* H') {S : Subgroup H} (hSM : S ≤ M)
    (hinj : ∀ m : M, (m : H) ∈ S → ψ m = 1 → m = 1) : Nat.card (imgIn ψ S) = Nat.card S := by
  let f : ↥(S.subgroupOf M) →* H' := ψ.comp (S.subgroupOf M).subtype
  have hf : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    rw [MonoidHom.mem_ker] at ha
    exact (Subgroup.mem_bot).mpr (Subtype.ext (hinj a a.2 ha))
  have hr : f.range = imgIn ψ S := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hr, ← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv,
    Nat.card_congr (subgroupOfEquivOfLe hSM).toEquiv]

theorem imgIn_le_normalizer (ψ : ↥M →* H') {T B : Subgroup H}
    (hTB : T ≤ normalizer (B : Set H)) : imgIn ψ T ≤ normalizer (imgIn ψ B : Set H') := by
  refine le_trans (map_mono ?_) (le_normalizer_map ψ)
  intro t ht
  rw [mem_subgroupOf] at ht
  rw [mem_normalizer_iff]
  intro x
  rw [mem_subgroupOf, mem_subgroupOf]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  exact mem_normalizer_iff.mp (hTB ht) x

theorem isSylowOf_map_hom {G G' : Type*} [Group G] [Group G'] [Finite G] {p : ℕ} [Fact p.Prime]
    {P K : Subgroup G} (h : IsSylowOf p P K) (f : G →* G') : IsSylowOf p (P.map f) (K.map f) := by
  obtain ⟨Q, rfl⟩ := h
  refine ⟨Q.mapSurjective (f.subgroupMap_surjective K), ?_⟩
  rw [Sylow.coe_mapSurjective, Subgroup.map_map, Subgroup.map_map]
  rfl

theorem isSylowOf_imgIn [Finite H] (ψ : ↥M →* H') {T X : Subgroup H} (hTM : T ≤ M) (hXM : X ≤ M)
    (h : IsSylowOf 2 T X) : IsSylowOf 2 (imgIn ψ T) (imgIn ψ X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h' : IsSylowOf 2 (T.subgroupOf M) (X.subgroupOf M) := by
    rw [← isSylowOf_map_subtype_iff M, subgroupOf_map_subtype, subgroupOf_map_subtype,
      inf_eq_left.mpr hTM, inf_eq_left.mpr hXM]
    exact h
  exact isSylowOf_map_hom h' ψ

theorem relIndex_map_dvd {G G' : Type*} [Group G] [Group G'] [Finite G] (f : G →* G')
    {N X : Subgroup G} (hNX : N ≤ X) : (N.map f).relIndex (X.map f) ∣ N.relIndex X := by
  rw [relIndex_map_map]
  set K := f.ker
  have h1 : K.relIndex N * (N ⊔ K).relIndex (X ⊔ K) = K.relIndex X := by
    rw [← relIndex_sup_right (H := N) (K := K), ← relIndex_sup_right (H := X) (K := K)]
    exact relIndex_mul_relIndex K (N ⊔ K) (X ⊔ K) le_sup_right (sup_le_sup_right hNX K)
  have h2 : (K ⊓ N).relIndex (K ⊓ X) * K.relIndex X = K.relIndex N * N.relIndex X := by
    rw [← inf_relIndex_right (H := K) (K := X), ← inf_relIndex_right (H := K) (K := N),
      relIndex_mul_relIndex (K ⊓ N) (K ⊓ X) X (inf_le_inf_left K hNX) inf_le_right,
      relIndex_mul_relIndex (K ⊓ N) N X inf_le_right hNX]
  have hpos : K.relIndex N ≠ 0 := (K.subgroupOf N).index_ne_zero_of_finite
  refine ⟨(K ⊓ N).relIndex (K ⊓ X), ?_⟩
  apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hpos)
  rw [← h2, ← h1]
  ring

theorem isTwoNilpotent_imgIn [Finite H] (ψ : ↥M →* H') {X : Subgroup H} (hXM : X ≤ M)
    (hX : IsTwoNilpotent X) : IsTwoNilpotent (imgIn ψ X) := by
  obtain ⟨N, hNX, hNn, hNo, k, hk⟩ := hX
  have hNM := hNX.trans hXM
  have hsub : N.subgroupOf M ≤ X.subgroupOf M := fun x hx => hNX hx
  refine ⟨imgIn ψ N, map_mono hsub, ?_, ?_, ?_⟩
  · rw [normal_subgroupOf_iff (map_mono hsub)]
    intro a b ha hb
    obtain ⟨n, hn, rfl⟩ := mem_imgIn.mp ha
    obtain ⟨x, hx, rfl⟩ := mem_imgIn.mp hb
    rw [← map_inv, ← map_mul, ← map_mul]
    refine mem_imgIn_of ψ ?_
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have := hNn.conj_mem ⟨n, hNX hn⟩ (mem_subgroupOf.mpr hn) ⟨x, hx⟩
    simpa [mem_subgroupOf] using this
  · refine hNo.of_dvd_nat ((card_map_dvd _ _).trans ?_)
    rw [Nat.card_congr (subgroupOfEquivOfLe hNM).toEquiv]
  · have hdvd := relIndex_map_dvd ψ hsub
    rw [relIndex_subgroupOf hXM, hk] at hdvd
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact ⟨j, hj⟩

end Image

theorem two_element_mem_of_odd_index {G : Type*} [Group G] {N : Subgroup G} [N.Normal]
    (hN : Odd N.index) {x : G} {k : ℕ} (hx : x ^ (2 ^ k) = 1) : x ∈ N := by
  have hdvd1 : orderOf (QuotientGroup.mk' N x) ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hx, map_one])
  have hdvd2 : orderOf (QuotientGroup.mk' N x) ∣ N.index := by
    rw [Subgroup.index]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime (2 ^ k) N.index := Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hN)
  have h1 : orderOf (QuotientGroup.mk' N x) = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd1 hdvd2
  rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact h1

theorem mem_of_two_element_of_mem_sup [Finite H] {X O : Subgroup H}
    (hO : O ≤ normalizer (X : Set H)) (hodd : Odd (Nat.card O)) {w : H} (hw : w ∈ X ⊔ O) {k : ℕ}
    (hwk : w ^ (2 ^ k) = 1) : w ∈ X := by
  set Y := X ⊔ O
  have hXY : X ≤ Y := le_sup_left
  have hYN : Y ≤ normalizer (X : Set H) := sup_le le_normalizer hO
  have : (X.subgroupOf Y).Normal := (normal_subgroupOf_iff_le_normalizer hXY).mpr hYN
  have hidx : Odd (X.subgroupOf Y).index := by
    have htop : (O.subgroupOf Y).map (QuotientGroup.mk' (X.subgroupOf Y)) = ⊤ := by
      have h1 : X.subgroupOf Y ⊔ O.subgroupOf Y = ⊤ := by
        rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]
      have h2 := congrArg (Subgroup.map (QuotientGroup.mk' (X.subgroupOf Y))) h1
      rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq, ← MonoidHom.range_eq_map,
        QuotientGroup.range_mk'] at h2
      exact h2
    rw [Subgroup.index, ← card_top (G := ↥Y ⧸ X.subgroupOf Y), ← htop]
    refine hodd.of_dvd_nat ((card_map_dvd _ _).trans ?_)
    rw [Nat.card_congr (subgroupOfEquivOfLe le_sup_right).toEquiv]
  have := two_element_mem_of_odd_index (N := X.subgroupOf Y) hidx (x := ⟨w, hw⟩) (k := k)
    (Subtype.ext (by simpa using hwk))
  exact mem_subgroupOf.mp this

theorem tightlyEmbedded_subgroupOf_of {G : Type*} [Group G] [Finite G] {Q M : Subgroup G}
    (hQM : Q ≤ M) (heven : Even (Nat.card Q))
    (hN : ∀ y ∈ M, ∀ x ∈ Q, x ≠ 1 → x ^ 2 = 1 → y * x * y⁻¹ ∈ Q →
      y ∈ normalizer (Q : Set G)) :
    TightlyEmbedded (Q.subgroupOf M) := by
  refine CFSG.StandardSubgroupAPI.tightlyEmbedded_of_involution
    (by rwa [Nat.card_congr (subgroupOfEquivOfLe hQM).toEquiv]) fun g x hx hx2 => ?_
  obtain ⟨hxQ, hxg⟩ := mem_inf.mp hx
  rw [mem_rightConjugate_iff] at hxg
  rw [mem_subgroupOf] at hxQ hxg
  have hx2' : orderOf (x : G) = 2 := by rwa [Subgroup.orderOf_coe]
  have hx1 : (x : G) ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hx2'
    omega
  have hxsq : (x : G) ^ 2 = 1 := by rw [← hx2']; exact pow_orderOf_eq_one _
  have hgN := hN g g.2 x hxQ hx1 hxsq (by simpa using hxg)
  rw [mem_normalizer_iff]
  intro z
  rw [mem_subgroupOf, mem_subgroupOf]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  exact mem_normalizer_iff.mp hgN z

theorem oddLieType_of_equiv {S S' : Type} [Group S] [Group S'] (e : S ≃* S')
    (h : CFSG.Blueprint.OddLieType S) : CFSG.Blueprint.OddLieType S' := by
  obtain ⟨t, n, p, f, hp, hp2, hadm, hm⟩ := h
  exact ⟨t, n, p, f, hp, hp2, hadm, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e hm⟩

section Quotient

variable [Finite H] {B T X : Subgroup H} {H' : Type} [Group H']

omit [Finite H] in
theorem mem_centralizer_of_imgIn (hB : commutator B = ⊤) {ψ : ↥(T ⊔ B) →* H'}
    (hker : ∀ m, ψ m = 1 ↔ (m : H) ∈ oddCenter B) {m : ↥(T ⊔ B)}
    (hmN : (m : H) ∈ normalizer (B : Set H)) (hmC : ψ m ∈ centralizer (imgIn ψ B : Set H')) :
    (m : H) ∈ centralizer (B : Set H) := by
  refine mem_centralizer_of_perfect hB hmN fun b hb b' hb' => ?_
  have hbM : b ∈ T ⊔ B := mem_sup_right hb
  have h1 : ψ ⟨b, hbM⟩ * ψ m = ψ m * ψ ⟨b, hbM⟩ :=
    (mem_centralizer_iff.mp hmC) _ (mem_imgIn_of ψ (m := ⟨b, hbM⟩) hb)
  have h2 : ψ (m * ⟨b, hbM⟩ * m⁻¹ * (⟨b, hbM⟩ : ↥(T ⊔ B))⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← h1]
    group
  have h3 := ((hker _).mp h2).2.1 b' hb'
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h3
  exact h3.symm

theorem Hyp46.map_quotient [Finite H'] (h : Hyp46 B T X) (hB : commutator B = ⊤)
    (ψ : ↥(T ⊔ B) →* H') (hψ : Function.Surjective ψ)
    (hker : ∀ m, ψ m = 1 ↔ (m : H) ∈ oddCenter B) :
    Hyp46 (imgIn ψ B) (imgIn ψ T) (imgIn ψ X) := by
  have hTM : T ≤ T ⊔ B := le_sup_left
  have hBM : B ≤ T ⊔ B := le_sup_right
  have hXM : X ≤ T ⊔ B := h.le_sup
  have hsup : imgIn ψ T ⊔ imgIn ψ B = ⊤ := by
    rw [imgIn, imgIn, ← Subgroup.map_sup, ← subgroupOf_sup hTM hBM, subgroupOf_self,
      ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr hψ]
  have hTinj : ∀ m : ↥(T ⊔ B), (m : H) ∈ T → ψ m = 1 → m = 1 := by
    intro m hmT hm1
    have hodd := ((hker m).mp hm1).2.2
    have hdvd : orderOf (m : H) ∣ 2 := orderOf_dvd_of_pow_eq_one (h.elem.2 _ hmT)
    have h1 : orderOf (m : H) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
      · exact h1
      · rw [h1] at hodd
        exact absurd hodd (by decide)
    exact Subtype.ext (orderOf_eq_one_iff.mp h1)
  have hcardT : Nat.card (imgIn ψ T) = Nat.card T := card_imgIn ψ hTM hTinj
  have hON : oddCenter B ≤ normalizer (X : Set H) :=
    h.le_normalizer_of_odd ((oddCenter_le B).trans hBM)
      (h.le_normalizer.trans (normalizer_le_normalizer_oddCenter B)) (odd_card_oddCenter B)
  have hXle : imgIn ψ X ≤ imgIn ψ T ⊔ imgIn ψ B := by
    rw [hsup]
    exact le_top
  refine ⟨isElemAbelian_imgIn ψ h.elem, by rw [hcardT]; exact h.four_le,
    imgIn_le_normalizer ψ h.le_normalizer, ?_, hXle, isSylowOf_imgIn ψ hTM hXM h.sylow,
    isTwoNilpotent_imgIn ψ hXM h.twoNilpotent, ?_⟩
  ·
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hyT, hyC⟩ := mem_inf.mp hy
    obtain ⟨m, hmT, rfl⟩ := mem_imgIn.mp hyT
    have hmC := mem_centralizer_of_imgIn hB hker (h.le_normalizer hmT) hyC
    have hm : (m : H) ∈ T ⊓ centralizer (B : Set H) := mem_inf.mpr ⟨hmT, hmC⟩
    rw [h.faithful, mem_bot] at hm
    rw [show m = 1 from Subtype.ext hm, map_one]
    exact one_mem _
  ·
    have heven : Even (Nat.card (imgIn ψ X)) := by
      have h2 : 2 ∣ Nat.card (imgIn ψ T) := by
        rw [hcardT]
        exact even_iff_two_dvd.mp h.even_card
      exact even_iff_two_dvd.mpr (h2.trans (card_dvd_of_le
        (map_mono fun x hx => h.le_X hx)))
    refine tightlyEmbedded_subgroupOf_of hXle heven ?_
    intro y _ x' hx' hx1 hx2 hyx
    obtain ⟨m, rfl⟩ := hψ y
    obtain ⟨n, hnX, rfl⟩ := mem_imgIn.mp hx'
    obtain ⟨a, r, hr, hor⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (n : H)).ne'
    have hψr : ψ (n ^ r) = ψ n := by
      rw [map_pow]
      obtain ⟨s, rfl⟩ := hr
      rw [pow_succ, pow_mul, hx2, one_pow, one_mul]
    have hn2 : ((n ^ r : ↥(T ⊔ B)) : H) ^ (2 ^ a) = 1 := by
      rw [Subgroup.coe_pow, ← pow_mul, mul_comm, ← hor, pow_orderOf_eq_one]
    have hnrX : ((n ^ r : ↥(T ⊔ B)) : H) ∈ X := by
      rw [Subgroup.coe_pow]
      exact pow_mem hnX r
    have hnr1 : ((n ^ r : ↥(T ⊔ B)) : H) ≠ 1 := by
      intro h1
      apply hx1
      rw [← hψr, show n ^ r = 1 from Subtype.ext h1, map_one]
    have hconj : ((m * n ^ r * m⁻¹ : ↥(T ⊔ B)) : H) ∈ X := by
      obtain ⟨w, hwX, hw⟩ := mem_imgIn.mp hyx
      have hO : ((w⁻¹ * (m * n ^ r * m⁻¹) : ↥(T ⊔ B)) : H) ∈ oddCenter B := by
        rw [← hker, map_mul, map_inv, hw, map_mul, map_mul, map_inv, hψr]
        group
      have hmem : ((m * n ^ r * m⁻¹ : ↥(T ⊔ B)) : H) ∈ X ⊔ oddCenter B := by
        have e : ((m * n ^ r * m⁻¹ : ↥(T ⊔ B)) : H) =
            (w : H) * ((w⁻¹ * (m * n ^ r * m⁻¹) : ↥(T ⊔ B)) : H) := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          group
        rw [e]
        exact mul_mem (mem_sup_left hwX) (mem_sup_right hO)
      refine mem_of_two_element_of_mem_sup hON (odd_card_oddCenter B) hmem (k := a) ?_
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, conj_pow, hn2]
      group
    have hmN := h.mem_normalizer_of_mem m.2 hnrX (by simpa using hconj) hnr1 a hn2
    refine le_normalizer_map ψ (mem_map_of_mem ψ ?_)
    rw [mem_normalizer_iff]
    intro z
    rw [mem_subgroupOf, mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact mem_normalizer_iff.mp hmN z

end Quotient

section General

variable [Finite H] {B T X : Subgroup H} {H' : Type} [Group H'] [Finite H']

theorem Hyp46.as76b_4_9_of_hom (hI : OddLieInputs) (hHRD : ModelHighestRootData)
    (h : Hyp46 B T X) (hB : Open.IsQuasisimple B) (hL : CFSG.Blueprint.OddLieType (B ⧸ center B))
    (ψ : ↥(T ⊔ B) →* H') (hψ : Function.Surjective ψ)
    (hker : ∀ m, ψ m = 1 ↔ (m : H) ∈ oddCenter B) :
    Odd (Nat.card (center B)) ∧ ∃ (p f : ℕ) (_ : Fact p.Prime), p ≠ 2 ∧ 1 ≤ f ∧
      p ^ f ∈ ({5, 7, 9} : Finset ℕ) ∧ Nonempty (B ⧸ center B ≃* PSL(2, GaloisField p f)) ∧
      T ≤ B ⊔ centralizer (B : Set H) ∧ (p ^ f ≠ 5 → T ≤ B) := by
  have hBM : B ≤ T ⊔ B := le_sup_right
  have hTM : T ≤ T ⊔ B := le_sup_left
  have hperf : commutator B = ⊤ := hB.1
  have : Group.IsPerfect B := ⟨hB.1⟩
  have h' := h.map_quotient hperf ψ hψ hker
  let fB : ↥B →* H' := ψ.comp (inclusion hBM)
  have hfB : ∀ b : B, fB b = 1 ↔ (b : H) ∈ oddCenter B := fun b => hker _
  have hr : fB.range = imgIn ψ B := by
    rw [MonoidHom.range_comp, inclusion_range]
  have hkerB : fB.ker = (oddCenter B).subgroupOf B := by
    ext b
    rw [MonoidHom.mem_ker, hfB, mem_subgroupOf]
  have hkerC : fB.ker ≤ center B := by
    intro b hb
    rw [MonoidHom.mem_ker, hfB] at hb
    exact Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hb.2.1 g g.2)
  have hktop : fB.ker ≠ ⊤ := by
    intro htop
    have hZ : center B = ⊤ := eq_top_iff.mpr (htop ▸ hkerC)
    have : IsSimpleGroup (B ⧸ center B) := hB.2
    obtain ⟨x, hx⟩ := _root_.exists_ne (1 : B ⧸ center B)
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    exact hx ((QuotientGroup.eq_one_iff x).mpr (hZ ▸ mem_top x))
  have hq : Open.IsQuasisimple fB.range :=
    CFSG.ComponentClassification.Quasisimple.range_quasisimple_of_ker_ne_top hB fB hktop
  let f' : ↥B →* ↥fB.range := fB.rangeRestrict
  have hf's : Function.Surjective f' := fB.rangeRestrict_surjective
  have hf'k : f'.ker ≤ center B := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hkerC
  have hZmap := CFSG.ComponentClassification.Quasisimple.center_map_of_central_kernel f' hf's hf'k
  have hZcomap :=
    CFSG.ComponentClassification.Quasisimple.center_comap_of_central_kernel f' hf's hf'k
  have hZ2 : IsPGroup 2 (center fB.range) := by
    intro z'
    have hz' : (z' : ↥fB.range) ∈ (center B).map f' := by rw [hZmap]; exact z'.2
    obtain ⟨z, hzZ, hzz⟩ := hz'
    obtain ⟨a, r, hr, hor⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos z).ne'
    refine ⟨a, Subtype.ext ?_⟩
    rw [SubgroupClass.coe_pow, ← hzz, ← map_pow, OneMemClass.coe_one]
    have hO : ((z ^ (2 ^ a) : B) : H) ∈ oddCenter B := by
      refine ⟨(z ^ (2 ^ a)).2, fun b hb => ?_, ?_⟩
      · have := congrArg Subtype.val ((Subgroup.mem_center_iff.mp (pow_mem hzZ (2 ^ a))) ⟨b, hb⟩)
        simpa using this
      · rw [Subgroup.orderOf_coe]
        refine hr.of_dvd_nat (orderOf_dvd_of_pow_eq_one ?_)
        rw [← pow_mul, ← hor, pow_orderOf_eq_one]
    exact Subtype.ext ((hfB _).mpr hO)
  let g : ↥B →* ↥fB.range ⧸ center fB.range := (QuotientGroup.mk' _).comp f'
  have hgs : Function.Surjective g := (QuotientGroup.mk'_surjective _).comp hf's
  have hgk : g.ker = center B := by
    rw [← hZcomap]
    ext b
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, mem_comap]
  let e : B ⧸ center B ≃* ↥fB.range ⧸ center fB.range :=
    (QuotientGroup.quotientMulEquivOfEq hgk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective g hgs)
  have hL' : CFSG.Blueprint.OddLieType (↥fB.range ⧸ center fB.range) := oddLieType_of_equiv e hL
  rw [hr] at hq hZ2 hL'
  obtain ⟨p, f, hpF, hp2, hf, hq5, ⟨e'⟩, hTin, hTle⟩ := h'.as76b_4_9 hI hHRD hq hZ2 hL'
  have h4 : 4 ≤ Nat.card (GaloisField p f) := by
    rw [GaloisField.card p f (by omega)]
    have : p ^ f = 5 ∨ p ^ f = 7 ∨ p ^ f = 9 := by simpa using hq5
    omega
  have hZbot : center (imgIn ψ B) = ⊥ := center_eq_bot_of_psl2 h4 e'
  rw [← hr] at hZbot
  have hcB : center B = fB.ker := by
    rw [← hZcomap, hZbot, ← MonoidHom.ker_rangeRestrict]
    rfl
  refine ⟨?_, p, f, hpF, hp2, hf, hq5, ⟨e.trans ((QuotientGroup.quotientMulEquivOfEq hZbot).trans
    (QuotientGroup.quotientBot.trans ((MulEquiv.subgroupCongr hr).trans e')))⟩, ?_, ?_⟩
  · rw [hcB, hkerB, Nat.card_congr (subgroupOfEquivOfLe (oddCenter_le B)).toEquiv]
    exact odd_card_oddCenter B
  · intro t ht
    obtain ⟨b', hb', c', hc', he⟩ :=
      exists_mul_of_mem_sup_centralizer (hTin (mem_imgIn_of ψ (m := ⟨t, hTM ht⟩) ht))
    obtain ⟨mb, hmbB, rfl⟩ := mem_imgIn.mp hb'
    have hc : ψ (mb⁻¹ * ⟨t, hTM ht⟩) = c' := by
      rw [map_mul, map_inv, he]
      group
    have hcN : ((mb⁻¹ * ⟨t, hTM ht⟩ : ↥(T ⊔ B)) : H) ∈ normalizer (B : Set H) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv]
      exact mul_mem (inv_mem (Subgroup.le_normalizer hmbB)) (h.le_normalizer ht)
    have hcC := mem_centralizer_of_imgIn hperf hker hcN (hc ▸ hc')
    have e2 : t = (mb : H) * ((mb⁻¹ * ⟨t, hTM ht⟩ : ↥(T ⊔ B)) : H) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
    rw [e2]
    exact mul_mem (mem_sup_left hmbB) (mem_sup_right hcC)
  · intro h5 t ht
    obtain ⟨mb, hmbB, hmb⟩ := mem_imgIn.mp (hTle h5 (mem_imgIn_of ψ (m := ⟨t, hTM ht⟩) ht))
    have hO : ((mb⁻¹ * ⟨t, hTM ht⟩ : ↥(T ⊔ B)) : H) ∈ oddCenter B := by
      rw [← hker, map_mul, map_inv, hmb, inv_mul_cancel]
    have e2 : t = (mb : H) * ((mb⁻¹ * ⟨t, hTM ht⟩ : ↥(T ⊔ B)) : H) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
    rw [e2]
    exact mul_mem hmbB (oddCenter_le B hO)

end General

theorem Hyp46.as76b_4_9_general [Finite H] {B T X : Subgroup H} (hI : OddLieInputs)
    (hHRD : ModelHighestRootData) (h : Hyp46 B T X) (hB : Open.IsQuasisimple B)
    (hL : CFSG.Blueprint.OddLieType (B ⧸ center B)) :
    Odd (Nat.card (center B)) ∧ ∃ (p f : ℕ) (_ : Fact p.Prime), p ≠ 2 ∧ 1 ≤ f ∧
      p ^ f ∈ ({5, 7, 9} : Finset ℕ) ∧ Nonempty (B ⧸ center B ≃* PSL(2, GaloisField p f)) ∧
      T ≤ B ⊔ centralizer (B : Set H) ∧ (p ^ f ≠ 5 → T ≤ B) := by
  have hON : ((oddCenter B).subgroupOf (T ⊔ B)).Normal :=
    (normal_subgroupOf_iff_le_normalizer ((oddCenter_le B).trans le_sup_right)).mpr
      ((sup_le h.le_normalizer Subgroup.le_normalizer).trans
        (normalizer_le_normalizer_oddCenter B))
  exact h.as76b_4_9_of_hom hI hHRD hB hL (QuotientGroup.mk' ((oddCenter B).subgroupOf (T ⊔ B)))
    (QuotientGroup.mk'_surjective _)
    fun m => by rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf]

theorem hypII_of_oddLieType (hI : OddLieInputs) (hHRD : ModelHighestRootData) (A : Type)
    [Group A] (hA : Open.IsQuasisimple A) (hL : CFSG.Blueprint.OddLieType (A ⧸ center A)) :
    HypII A := by
  intro H _ _ B T ⟨e⟩ hT hK
  obtain ⟨X, hX⟩ := Hyp46.exists_of hT hK
  have hB : Open.IsQuasisimple B := isQuasisimple_of_mulEquiv e.symm hA
  have hLB : CFSG.Blueprint.OddLieType (B ⧸ center B) :=
    oddLieType_of_equiv (QuotientGroup.congr (center B) (center A) e (map_center_mulEquiv e)).symm
      hL
  obtain ⟨-, p, f, -, -, -, -, -, hTin, -⟩ := hX.as76b_4_9_general hI hHRD hB hLB
  exact hTin

end CFSG.ComponentClassification.RankTwoOddLie
