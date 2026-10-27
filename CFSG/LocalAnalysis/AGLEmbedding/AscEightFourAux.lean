module

public import CFSG.LocalAnalysis.AGLEmbedding.ZOneFacts
import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.CGT.PushingUpLit.Transport

public section

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

namespace CFSG.AGLEmbedding

theorem Asc81bHyp.twoCore_le {G : Type} [Group G] [Finite G] {M S : Subgroup G}
    (hA : Asc81bHyp M S) : pCoreOf 2 M ≤ S :=
  le_of_two_radical hA.twoRadical.1 hA.twoRadical.2.2
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 M)
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M)
    (inf_le_left.trans (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 M))

namespace AscEightFour

section Basic

variable {G : Type} [Group G]

theorem isKGroup_mono {X H : Subgroup G} (hX : CFSG.Open.IsKGroup ↥X) (hHX : H ≤ X) :
    CFSG.Open.IsKGroup ↥H :=
  hX.of_le hHX

theorem isSubnormal_inf {A B : Subgroup G} (h : IsSubnormal A B) (C : Subgroup G) :
    IsSubnormal (A ⊓ C) (B ⊓ C) :=
  h.inf C

theorem isSubnormal_trans_normal {A B C : Subgroup G} (h : IsSubnormal A B) (hBC : B ≤ C)
    (hn : (B.subgroupOf C).Normal) : IsSubnormal A C :=
  h.trans (.step hBC hn (.refl C))

theorem cgsIn_mono {H X S : Subgroup G} (h : H ≤ X) : cgsIn H S ≤ cgsIn X S :=
  iSup_mono fun _ => iSup_mono fun _ => iSup_mono fun _ => iSup_mono fun _ =>
    inf_le_inf_right _ h

end Basic

section EightFour

variable {G : Type} [Group G] (X S : Subgroup G)

abbrev piX : ↥X →* ↥X ⧸ CFSG.pCore 2 ↥X := QuotientGroup.mk' (CFSG.pCore 2 ↥X)

abbrev oddBar : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X) := CFSG.pPrimeCore 2 (↥X ⧸ CFSG.pCore 2 ↥X)

def pGrp : Subgroup G := ((oddBar X).comap (piX X)).map X.subtype

def hGrp : Subgroup G := ((oddBar X ⊔ barM X S).comap (piX X)).map X.subtype

variable {X S}

theorem pGrp_le : pGrp X ≤ X := Subgroup.map_subtype_le _

theorem hGrp_le : hGrp X S ≤ X := Subgroup.map_subtype_le _

theorem pGrp_le_hGrp : pGrp X ≤ hGrp X S :=
  Subgroup.map_mono (Subgroup.comap_mono le_sup_left)

theorem le_hGrp (hSX : S ≤ X) : S ≤ hGrp X S := by
  intro s hs
  refine ⟨⟨s, hSX hs⟩, ?_, rfl⟩
  exact le_sup_right (b := barM X S) ⟨⟨s, hSX hs⟩, hs, rfl⟩

theorem twoCore_le_hGrp : pCoreOf 2 X ≤ hGrp X S := by
  rintro _ ⟨y, hy, rfl⟩
  refine ⟨y, ?_, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_comap]
  have h1 : piX X y = 1 := by
    rw [QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff y).mpr hy
  rw [h1]
  exact one_mem _

theorem pGrp_normal : ((pGrp X).subgroupOf X).Normal := by
  unfold pGrp
  rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective X.subtype_injective]
  exact Subgroup.Normal.comap CFSG.pPrimeCore_normal _

theorem le_normalizer_pGrp : X ≤ Subgroup.normalizer (pGrp X : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer pGrp_le).mp pGrp_normal

theorem eq_one_of_mem_oddBar [Finite G] {z : ↥X ⧸ CFSG.pCore 2 ↥X} (hz : z ∈ oddBar X) {k : ℕ}
    (hk : z ^ 2 ^ k = 1) : z = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set y : oddBar X := ⟨z, hz⟩
  have hy : y ^ 2 ^ k = 1 := Subtype.ext (by simpa [y] using hk)
  have h1 : orderOf y ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hy
  have h2 : orderOf y ∣ Nat.card (oddBar X) := orderOf_dvd_natCard y
  have hcop : Nat.Coprime (2 ^ k) (Nat.card (oddBar X)) :=
    Nat.Coprime.pow_left k CFSG.pPrimeCore_coprime_card
  have h3 : orderOf y = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2
  have : y = 1 := orderOf_eq_one_iff.mp h3
  exact congrArg Subtype.val this

theorem mem_twoCore_of_pow [Finite G] {x : ↥X} (hx : piX X x ∈ oddBar X) {k : ℕ}
    (hk : x ^ 2 ^ k = 1) :
    (x : G) ∈ pCoreOf 2 X := by
  have h1 : piX X x = 1 := eq_one_of_mem_oddBar hx (by rw [← map_pow, hk, map_one])
  have h2 : x ∈ CFSG.pCore 2 ↥X := by
    rw [QuotientGroup.mk'_apply] at h1
    exact (QuotientGroup.eq_one_iff x).mp h1
  exact ⟨x, h2, rfl⟩


theorem exists_of_mem_sup {x : ↥X} (hx : piX X x ∈ oddBar X ⊔ barM X S) :
    ∃ s : ↥X, (s : G) ∈ S ∧ piX X (s⁻¹ * x) ∈ oddBar X := by
  have : (oddBar X).Normal := CFSG.pPrimeCore_normal
  rw [sup_comm, Subgroup.mem_sup_of_normal_right] at hx
  obtain ⟨t, ht, o, ho, hto⟩ := hx
  obtain ⟨s, hs, rfl⟩ := ht
  refine ⟨s, hs, ?_⟩
  rw [map_mul, map_inv, ← hto, inv_mul_cancel_left]
  exact ho

end EightFour

section EightFourMain

variable {G : Type} [Group G] [Finite G] {X S : Subgroup G}

omit [Finite G] in
theorem barM_isPGroup (hS : IsPGroup 2 S) : IsPGroup 2 (barM X S) :=
  (hS.comap_subtype (K := X)).map _

theorem isSylowTwoOf_hGrp (hyp : Asc81bHyp X S) : IsSylowTwoOf S (hGrp X S) := by
  have hSX := hyp.twoRadical.1
  refine isSylowTwoOf_of_forall_normalizer_le (le_hGrp hSX) hyp.twoRadical.isPGroup ?_
  intro U hUH hU2 hSU _ u hu
  obtain ⟨x, hx, rfl⟩ := hUH hu
  obtain ⟨s, hs, ho⟩ := exists_of_mem_sup hx
  have hvU : ((s⁻¹ * x : ↥X) : G) ∈ U := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact U.mul_mem (U.inv_mem (hSU hs)) hu
  obtain ⟨k, hk⟩ := hU2 ⟨_, hvU⟩
  have hk' : (s⁻¹ * x) ^ 2 ^ k = 1 := by
    apply Subtype.ext
    have := congrArg Subtype.val hk
    simpa using this
  have hv := hyp.twoCore_le (mem_twoCore_of_pow ho hk')
  have : (x : G) = s * ((s⁻¹ * x : ↥X) : G) := by simp
  change (x : G) ∈ S
  rw [this]
  exact S.mul_mem hs hv

omit [Finite G] in
theorem charTwo_hGrp (hyp : Asc81bHyp X S) : CharTwo (hGrp X S) := by
  have hQH : pCoreOf 2 X ≤ hGrp X S := twoCore_le_hGrp
  have hQn : ((pCoreOf 2 X).subgroupOf (hGrp X S)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQH).mpr
      (hGrp_le.trans (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 X))
  have hQle : pCoreOf 2 X ≤ pCoreOf 2 (hGrp X S) :=
    CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 _ _ hQH hQn
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 X)
  rintro g ⟨hgH, hgC⟩
  exact hQle (hyp.charTwo ⟨hGrp_le hgH,
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hQle) hgC⟩)

omit [Finite G] in
theorem cgsIn_hGrp_le (hyp : Asc81bHyp X S) :
    cgsIn (hGrp X S) S ≤ Subgroup.normalizer (S : Set G) :=
  (cgsIn_mono hGrp_le).trans (hyp.cgs.le.trans inf_le_right)

theorem oddBar_le_centralizer (hyp : Asc81bHyp X S)
    (hHN : hGrp X S ≤ Subgroup.normalizer (S : Set G)) :
    CFSG.pPrimeCore 2 (↥X ⧸ CFSG.pCore 2 ↥X) ≤ Subgroup.centralizer (barM X S : Set _) := by
  have hON : (oddBar X).Normal := CFSG.pPrimeCore_normal
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  rintro t ⟨s, hs, rfl⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥X) y
  have hxH : (x : G) ∈ hGrp X S := ⟨x, le_sup_left (b := barM X S) hy, rfl⟩
  have hsS : (s : G) ∈ S := hs
  have hw : ((x * s * x⁻¹ * s⁻¹ : ↥X) : G) ∈ S := by
    have := (Subgroup.mem_normalizer_iff.mp (hHN hxH) s).mp hsS
    push_cast
    exact S.mul_mem this (S.inv_mem hsS)
  have hw1 : piX X (x * s * x⁻¹ * s⁻¹) ∈ oddBar X := by
    have h1 : piX X x ∈ oddBar X := hy
    have h2 : piX X s * (piX X x)⁻¹ * (piX X s)⁻¹ ∈ oddBar X :=
      hON.conj_mem _ (inv_mem h1) _
    have h3 := mul_mem h1 h2
    simp only [map_mul, map_inv]
    simpa [mul_assoc] using h3
  have hw2 : piX X (x * s * x⁻¹ * s⁻¹) ∈ barM X S := ⟨_, hw, rfl⟩
  obtain ⟨k, hk⟩ := barM_isPGroup hyp.twoRadical.isPGroup ⟨_, hw2⟩
  have hk' : (piX X (x * s * x⁻¹ * s⁻¹)) ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have h3 := eq_one_of_mem_oddBar hw1 hk'
  simp only [map_mul, map_inv] at h3
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h3
  exact h3.symm


theorem le_pGrp_of_short (hyp : Asc81bHyp X S) {B : Subgroup G} (hBH : B ≤ hGrp X S)
    (hs : IsShort2 B) : B ≤ pGrp X := by
  have hBX : B ≤ X := hBH.trans hGrp_le
  have hN : ((pGrp X).subgroupOf B).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    push_cast
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pGrp (hBX g.2)) n).mp hn
  have h2 : IsPGroup 2 (↥B ⧸ (pGrp X).subgroupOf B) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H b =>
      obtain ⟨x, hx, hxb⟩ := hBH b.2
      obtain ⟨s, hs, ho⟩ := exists_of_mem_sup hx
      obtain ⟨k, hk⟩ := hyp.twoRadical.isPGroup ⟨s, hs⟩
      refine ⟨k, ?_⟩
      have hs1 : s ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
      have hρ : (QuotientGroup.mk' (oddBar X)) (piX X x) =
          (QuotientGroup.mk' (oddBar X)) (piX X s) := by
        refine ((QuotientGroup.mk'_eq_mk' _).mpr ⟨piX X (s⁻¹ * x), ho, ?_⟩).symm
        rw [map_mul, map_inv, mul_inv_cancel_left]
      have hmem : piX X (x ^ 2 ^ k) ∈ oddBar X := by
        rw [← QuotientGroup.ker_mk' (oddBar X), MonoidHom.mem_ker, map_pow, map_pow, hρ,
          ← map_pow, ← map_pow, hs1, map_one, map_one]
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      refine ⟨x ^ 2 ^ k, hmem, ?_⟩
      have hxb' : (x : G) = b := hxb
      simp [hxb']
  have htop := hs.1 _ h2
  intro b hb
  have : (⟨b, hb⟩ : ↥B) ∈ (pGrp X).subgroupOf B := htop ▸ Subgroup.mem_top _
  exact this

theorem mem_blockQ_of_pow {B : Subgroup G} (hBP : B ≤ pGrp X) {b : G} (hb : b ∈ B) {k : ℕ}
    (hk : b ^ 2 ^ k = 1) : b ∈ pCoreOf 2 B := by
  have hBX : B ≤ X := hBP.trans pGrp_le
  obtain ⟨x, hx, rfl⟩ := hBP hb
  have hk' : x ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk)
  have hQ := mem_twoCore_of_pow hx hk'
  have hle : pCoreOf 2 X ⊓ B ≤ pCoreOf 2 B := by
    refine CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 _ _ inf_le_right ?_
      ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 X).to_le inf_le_left)
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right]
    intro g hg
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨(hBX.trans (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 X)) hg,
        Subgroup.le_normalizer hg⟩
  exact hle ⟨hQ, hb⟩

omit [Finite G] in
theorem mem_pCore_of_mem_pCoreOf {B : Subgroup G} {b : ↥B} (h : (b : G) ∈ pCoreOf 2 B) :
    b ∈ CFSG.pCore 2 ↥B := (CFSG.mem_openPCoreOf_iff b).mp h

omit [Finite G] in
theorem false_of_two_element {B : Subgroup G} {T : Type*} [Group T] (α : ↥B →* T)
    (hαs : Function.Surjective α) (hαk : α.ker = CFSG.pCore 2 ↥B)
    (h2 : ∀ b : ↥B, ∀ k : ℕ, (b : G) ^ 2 ^ k = 1 → (b : G) ∈ pCoreOf 2 B)
    {t : T} (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) : False := by
  obtain ⟨b, rfl⟩ := hαs t
  have hb2 : b ^ 2 ∈ CFSG.pCore 2 ↥B := by rw [← hαk, MonoidHom.mem_ker, map_pow, ht2]
  obtain ⟨j, hj⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥B)) ⟨_, hb2⟩
  have hj' : b ^ 2 ^ (j + 1) = 1 := by
    rw [pow_succ', pow_mul]
    exact congrArg Subtype.val hj
  have hb := mem_pCore_of_mem_pCoreOf (h2 b (j + 1) (by
    rw [← Subgroup.coe_pow, hj', Subgroup.coe_one]))
  rw [← hαk, MonoidHom.mem_ker] at hb
  exact ht1 hb

end EightFourMain

end AscEightFour

end CFSG.AGLEmbedding
