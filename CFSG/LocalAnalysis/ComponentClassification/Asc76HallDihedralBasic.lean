module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76YSec4D17
public import CFSG.LocalAnalysis.ComponentClassification.Asc76XLemma38
public import CFSG.LocalAnalysis.ComponentClassification.Asc76YSec4D12

public section

namespace CFSG.ComponentClassification.Asc76X.HallDihedral

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.AschbacherTheorem3
open CFSG.ComponentClassification.Asc76 CFSG.ComponentClassification.Asc76.Sec4

variable {G : Type} [Group G] [Finite G]

structure Hyp (Ω : Set (Subgroup G)) (S K R U : Subgroup G) (t z : G) : Prop where
  lemma22 : Asc76Lemma22
  asm : Assumption41 Ω
  twoNil : ∀ K ∈ Ω, ∀ R, IsSylowOf 2 R K → IsTwoNil K R
  single : ∃ K₀ ∈ Ω, ∀ K ∈ Ω, ∃ g : G, K = AschbacherTightEmbedding.rightConjugate K₀ g
  sylow : IsSylowOf 2 S ⊤
  mem : K ∈ Ω
  sylowR : IsSylowOf 2 R K
  le : R ≤ S
  rot : IsDihedralRot U R
  weak : sec4W Ω S = U
  zinv : IsZInv Ω t
  t_mem : t ∈ S
  t_not_mem : t ∉ U
  z_mem : z ∈ U
  z_ne : z ≠ 1
  z_mul : z * z = 1

namespace Hyp

variable {Ω : Set (Subgroup G)} {S K R U : Subgroup G} {t z : G}

theorem z_unique (h : Hyp Ω S K R U t z) : ∀ y ∈ U, y * y = 1 → y = 1 ∨ y = z := by
  obtain ⟨z', hz'U, hz'1, hz'z', huniq, -⟩ := h.rot.exists_involution
  have e : z = z' := (huniq z h.z_mem h.z_mul).resolve_left h.z_ne
  rw [e]
  exact huniq

theorem z_comm (h : Hyp Ω S K R U t z) : ∀ x ∈ R, x * z = z * x := by
  obtain ⟨z', hz'U, hz'1, hz'z', huniq, hc⟩ := h.rot.exists_involution
  have e : z = z' := (huniq z h.z_mem h.z_mul).resolve_left h.z_ne
  rw [e]
  exact hc

theorem le_normalizer_U (h : Hyp Ω S K R U t z) : S ≤ normalizer (U : Set G) := by
  have := le_normalizer_sec4W h.asm.conj_mem S
  rwa [h.weak] at this

theorem z_central (h : Hyp Ω S K R U t z) : ∀ s ∈ S, s * z = z * s := by
  intro s hs
  have h1 : s * z * s⁻¹ ∈ U := (mem_normalizer_iff.mp (h.le_normalizer_U hs) z).mp h.z_mem
  have h2 : s * z * s⁻¹ * (s * z * s⁻¹) = 1 := by
    calc s * z * s⁻¹ * (s * z * s⁻¹) = s * (z * z) * s⁻¹ := by group
      _ = 1 := by rw [h.z_mul]; group
  rcases h.z_unique _ h1 h2 with e | e
  · exfalso
    apply h.z_ne
    calc z = s⁻¹ * (s * z * s⁻¹) * s := by group
      _ = 1 := by rw [e]; group
  · calc s * z = s * z * s⁻¹ * s := by group
      _ = z * s := by rw [e]

theorem tight (h : Hyp Ω S K R U t z) : TightlyEmbedded K :=
  Assumption41.tightlyEmbedded h.asm h.mem

omit [Finite G] in
theorem z_mem_K (h : Hyp Ω S K R U t z) : z ∈ K :=
  h.sylowR.le (h.rot.le h.z_mem)

theorem le_normalizer_K (h : Hyp Ω S K R U t z) : S ≤ normalizer (K : Set G) := by
  refine fun s hs => Asc76.Sec4.centralizer_le_normalizer h.tight h.z_mem_K h.z_ne h.z_mul ?_
  rw [mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  rw [hy]
  exact (h.z_central s hs).symm

theorem mem_R (h : Hyp Ω S K R U t z) {x : G} (hxS : x ∈ S) (hxK : x ∈ K) : x ∈ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : S ⊓ K = R := h.sylowR.eq_of_le (le_inf h.le h.sylowR.le) inf_le_right
    (h.sylow.isPGroup.to_le inf_le_left)
  rw [← h1]
  exact mem_inf.mpr ⟨hxS, hxK⟩

theorem le_normalizer_R (h : Hyp Ω S K R U t z) : S ≤ normalizer (R : Set G) := by
  intro s hs
  rw [mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    refine h.mem_R (mul_mem (mul_mem hs (h.le hy)) (inv_mem hs)) ?_
    exact (mem_normalizer_iff.mp (h.le_normalizer_K hs) y).mp (h.sylowR.le hy)
  · intro hy
    have hyS : y ∈ S := by
      have e : y = s⁻¹ * (s * y * s⁻¹) * s := by group
      rw [e]
      exact mul_mem (mul_mem (inv_mem hs) (h.le hy)) hs
    refine h.mem_R hyS ?_
    exact (mem_normalizer_iff.mp (h.le_normalizer_K hs) y).mpr (h.sylowR.le hy)

theorem three_le_card {H : Subgroup G} {a b c : G} (ha : a ∈ H) (hb : b ∈ H) (hc : c ∈ H)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : 3 ≤ Nat.card H := by
  have h1 : ({a, b, c} : Set G) ⊆ H := by
    intro x hx
    rcases hx with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
  have h2 := Set.ncard_le_ncard h1 (Set.toFinite _)
  rw [Set.ncard_insert_of_notMem (by simp [hab, hac]), Set.ncard_pair hbc] at h2
  have h3 : Nat.card H = (H : Set G).ncard := Nat.card_coe_set_eq _
  omega

theorem card_rot (h : Hyp Ω S K R U t z) {V : Subgroup G} (hV : IsRot Ω V) :
    Nat.card V = Nat.card U := by
  obtain ⟨J, hJ, T, hT, hVT⟩ := IsRot.exists_isDihedralRot h.asm hV
  have h1 := hVT.card_eq
  have h2 := h.rot.card_eq
  have h3 := Assumption41.card_sylow_eq h.asm h.mem hJ h.sylowR hT
  omega

theorem sec4W_of_sylow (h : Hyp Ω S K R U t z) {S' : Subgroup G} (hS' : IsSylowOf 2 S' ⊤) :
    IsRot Ω (sec4W Ω S') ∧ Nat.card (sec4W Ω S') = Nat.card U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, -, hk⟩ := L26.IsSylowOf.exists_conj_mem h.sylow hS'
  have hS'eq : S' = AschbacherTightEmbedding.rightConjugate S k⁻¹ := by
    ext x
    rw [mem_rightConjugate_iff, inv_inv, hk]
  have hW : sec4W Ω S' = AschbacherTightEmbedding.rightConjugate U k⁻¹ := by
    rw [hS'eq, ← rightConjugate_sec4W h.asm.conj_mem S k⁻¹, h.weak]
  rw [hW]
  exact ⟨isRot_of (h.asm.conj_mem K h.mem k⁻¹) (isSylowOf_rightConjugate h.sylowR k⁻¹)
    (h.rot.rightConjugate k⁻¹), rightConjugate_card U k⁻¹⟩

theorem rot_eq (h : Hyp Ω S K R U t z) {P V V' : Subgroup G} (hP : IsPGroup 2 P)
    (hV : IsRot Ω V) (hV' : IsRot Ω V') (hVP : V ≤ P) (hV'P : V' ≤ P) : V = V' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S', hS', hPS'⟩ := Asc76.Sec4.exists_isSylowOf_le hP (le_top : P ≤ ⊤)
  obtain ⟨-, hWc⟩ := h.sec4W_of_sylow hS'
  have h1 : V = sec4W Ω S' :=
    eq_of_le_of_card_ge (le_sec4W (hVP.trans hPS') hV) (by rw [hWc, h.card_rot hV])
  have h2 : V' = sec4W Ω S' :=
    eq_of_le_of_card_ge (le_sec4W (hV'P.trans hPS') hV') (by rw [hWc, h.card_rot hV'])
  rw [h1, h2]

theorem eq_of_rot_eq (h : Hyp Ω S K R U t z) {J₁ J₂ T₁ T₂ V₁ V₂ : Subgroup G} (hJ₁ : J₁ ∈ Ω)
    (hJ₂ : J₂ ∈ Ω) (hT₁ : IsSylowOf 2 T₁ J₁) (hT₂ : IsSylowOf 2 T₂ J₂)
    (hV₁ : IsDihedralRot V₁ T₁) (hV₂ : IsDihedralRot V₂ T₂) (e : V₁ = V₂) : J₁ = J₂ := by
  obtain ⟨y, hyV, hy1, hyy, -, -⟩ := hV₁.exists_involution
  exact eq_of_mem_of_mem h.asm hJ₁ hJ₂ (hT₁.le (hV₁.le hyV)) (hT₂.le (hV₂.le (e ▸ hyV))) hy1 hyy

theorem eq_of_le_isPGroup (h : Hyp Ω S K R U t z) {P J₁ J₂ T₁ T₂ : Subgroup G}
    (hP : IsPGroup 2 P) (hJ₁ : J₁ ∈ Ω) (hJ₂ : J₂ ∈ Ω) (hT₁ : IsSylowOf 2 T₁ J₁)
    (hT₂ : IsSylowOf 2 T₂ J₂) (hT₁P : T₁ ≤ P) (hT₂P : T₂ ≤ P) : J₁ = J₂ := by
  obtain ⟨V₁, hV₁⟩ := Assumption41.exists_rot h.asm hJ₁ hT₁
  obtain ⟨V₂, hV₂⟩ := Assumption41.exists_rot h.asm hJ₂ hT₂
  exact h.eq_of_rot_eq hJ₁ hJ₂ hT₁ hT₂ hV₁ hV₂ (h.rot_eq hP (isRot_of hJ₁ hT₁ hV₁)
    (isRot_of hJ₂ hT₂ hV₂) (hV₁.le.trans hT₁P) (hV₂.le.trans hT₂P))

theorem not_dStarAdj (h : Hyp Ω S K R U t z) {L M : Subgroup G} (hL : L ∈ Ω) (hM : M ∈ Ω)
    (hLM : L ≠ M) : ¬ DStarAdj Ω L M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hadj
  rcases dAdj_or_exists_omegaD_of_dStarAdj h.lemma22 h.asm hadj with hD | ⟨S', hS', hL', hM'⟩
  · obtain ⟨-, -, -, hLN⟩ := hD
    obtain ⟨T, hT⟩ := exists_isSylowOf 2 L
    obtain ⟨T', hT', hTT'⟩ :=
      Asc76.Sec4.exists_isSylowOf_normalized hT.isPGroup (hT.le.trans hLN)
    have hP : IsPGroup 2 (T ⊔ T' : Subgroup G) :=
      IsPGroup.to_sup_of_normal_right' hT.isPGroup hT'.isPGroup hTT'
    exact hLM (h.eq_of_le_isPGroup hP hL hM hT hT' le_sup_left le_sup_right)
  · obtain ⟨-, T, hT, hTW⟩ := hL'
    obtain ⟨-, T', hT', hT'W⟩ := hM'
    obtain ⟨V, hV⟩ := Assumption41.exists_rot h.asm hL hT
    obtain ⟨V', hV'⟩ := Assumption41.exists_rot h.asm hM hT'
    have hW2 : IsPGroup 2 (sec4W Ω S') := hS'.isPGroup.to_le (sec4W_le S')
    exact hLM (h.eq_of_rot_eq hL hM hT hT' hV hV' (h.rot_eq hW2 (isRot_of hL hT hV)
      (isRot_of hM hT' hV') (rot_le_sec4W h.asm hS' hL hT hV hTW)
      (rot_le_sec4W h.asm hS' hM hT' hV' hT'W)))

theorem card_le_two (h : Hyp Ω S K R U t z) {L M Q : Subgroup G} (hL : L ∈ Ω) (hM : M ∈ Ω)
    (hLM : L ≠ M) (hQ : IsPGroup 2 Q) (hQM : Q ≤ M) (hQL : Q ≤ normalizer (L : Set G)) :
    Nat.card Q ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨V, hV, hQV⟩ := Asc76.Sec4.exists_isSylowOf_le hQ (le_inf hQM hQL)
  by_cases hV1 : V = ⊥
  · rw [hV1, le_bot_iff] at hQV
    rw [hQV, card_bot]
    norm_num
  · rw [← card_eq_two_of_not_dStarAdj h.lemma22 h.asm hM hL (h.not_dStarAdj hL hM hLM) hV hV1]
    exact card_le_of_le hQV

theorem eq_of_zinv_of_mem (h : Hyp Ω S K R U t z) {x : G} (hx : IsZInv Ω x) (hxS : x ∈ S)
    (hxK : x ∈ K) : x = z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨M, hM, T, V, hT, hV, hxV, hx1, hxx⟩ := hx
  have hMK : M = K := eq_of_mem_of_mem h.asm hM h.mem (hT.le (hV.le hxV)) hxK hx1 hxx
  rw [hMK] at hT
  obtain ⟨k, hkK, hk⟩ := L26.IsSylowOf.exists_conj_mem h.sylowR hT
  have hTR : AschbacherTightEmbedding.rightConjugate T k = R := by
    ext w
    rw [mem_rightConjugate_iff, hk]
    have e : k⁻¹ * (k * w * k⁻¹) * k = w := by group
    rw [e]
  have hVU : AschbacherTightEmbedding.rightConjugate V k = U := by
    have h1 := hV.rightConjugate k
    rw [hTR] at h1
    exact (h.rot.eq_of_isCyclic h1.le h1.isCyclic h1.relIndex_eq).symm ▸ rfl
  have hxk : k⁻¹ * x * k = z := by
    have h1 : k⁻¹ * x * k ∈ U := by
      rw [← hVU, mem_rightConjugate_iff]
      have e : k * (k⁻¹ * x * k) * k⁻¹ = x := by group
      rw [e]
      exact hxV
    have h2 : k⁻¹ * x * k * (k⁻¹ * x * k) = 1 := by
      calc k⁻¹ * x * k * (k⁻¹ * x * k) = k⁻¹ * (x * x) * k := by group
        _ = 1 := by rw [hxx]; group
    refine (h.z_unique _ h1 h2).resolve_left fun e => hx1 ?_
    calc x = k * (k⁻¹ * x * k) * k⁻¹ := by group
      _ = 1 := by rw [e]; group
  obtain ⟨o, ho, r, hr, rfl⟩ := h.twoNil K h.mem R h.sylowR k hkK
  have hxo : x = o * z * o⁻¹ := by
    have hrz : r * z * r⁻¹ = z := by
      rw [h.z_comm r hr, mul_assoc, mul_inv_cancel, mul_one]
    calc x = o * r * ((o * r)⁻¹ * x * (o * r)) * (o * r)⁻¹ := by group
      _ = o * (r * z * r⁻¹) * o⁻¹ := by rw [hxk]; group
      _ = o * z * o⁻¹ := by rw [hrz]
  have hxR : x ∈ R := h.mem_R hxS hxK
  have hzR : z ∈ R := h.rot.le h.z_mem
  have hd : z⁻¹ * x ∈ R ⊓ oddCoreIn K := by
    refine mem_inf.mpr ⟨mul_mem (inv_mem hzR) hxR, ?_⟩
    have h1 : z⁻¹ * o * z ∈ oddCoreIn K := by
      have h2 := (mem_normalizer_iff.mp (le_normalizer_oddCoreIn K (inv_mem h.z_mem_K)) o).mp ho
      rwa [inv_inv] at h2
    have e : z⁻¹ * x = z⁻¹ * o * z * o⁻¹ := by rw [hxo]; group
    rw [e]
    exact mul_mem h1 (inv_mem ho)
  have hbot : R ⊓ oddCoreIn K = ⊥ := eq_bot_of_isPGroup_of_odd
    (h.sylowR.isPGroup.to_le inf_le_left)
    ((odd_card_oddCoreIn K).of_dvd_nat (card_dvd_of_le inf_le_right))
  rw [hbot, mem_bot] at hd
  calc x = z * (z⁻¹ * x) := by group
    _ = z := by rw [hd, mul_one]

structure Outer (Ω : Set (Subgroup G)) (S U : Subgroup G) (x : G) : Prop where
  zinv : IsZInv Ω x
  mem : x ∈ S
  not_mem : x ∉ U

omit [Finite G] in
theorem outer_t (h : Hyp Ω S K R U t z) : Outer Ω S U t := ⟨h.zinv, h.t_mem, h.t_not_mem⟩

namespace Outer

variable {x : G}

omit [Finite G] in
theorem mul_self (hx : Outer Ω S U x) : x * x = 1 := by
  obtain ⟨M, hM, T, V, hT, hV, hxV, hx1, hxx⟩ := hx.zinv
  exact hxx

omit [Finite G] in
theorem ne_one (hx : Outer Ω S U x) : x ≠ 1 := fun e => hx.not_mem (e ▸ U.one_mem)

theorem not_mem_K (h : Hyp Ω S K R U t z) (hx : Outer Ω S U x) : x ∉ K := fun hxK =>
  hx.not_mem (h.eq_of_zinv_of_mem hx.zinv hx.mem hxK ▸ h.z_mem)

theorem not_mem_R (h : Hyp Ω S K R U t z) (hx : Outer Ω S U x) : x ∉ R := fun hxR =>
  hx.not_mem_K h (h.sylowR.le hxR)

theorem exists_member (h : Hyp Ω S K R U t z) (hx : Outer Ω S U x) :
    ∃ M ∈ Ω, x ∈ M ∧ K ≠ M := by
  obtain ⟨M, hM, T, V, hT, hV, hxV, hx1, hxx⟩ := hx.zinv
  refine ⟨M, hM, hT.le (hV.le hxV), fun e => hx.not_mem_K h ?_⟩
  rw [e]
  exact hT.le (hV.le hxV)

theorem inv (h : Hyp Ω S K R U t z) (hx : Outer Ω S U x) : ∀ u ∈ U, x * u * x⁻¹ = u⁻¹ := by
  obtain ⟨M, hM, hxM, hKM⟩ := hx.exists_member h
  exact conj_eq_inv_of_not_dStarAdj h.lemma22 h.asm hM h.mem (h.not_dStarAdj h.mem hM hKM) hxM
    hx.ne_one hx.mul_self (h.le_normalizer_K hx.mem) h.sylowR h.rot (h.le_normalizer_R hx.mem)

theorem dihedral (h : Hyp Ω S K R U t z) (hx : Outer Ω S U x) :
    IsDihedralTwoGroup (zpowers x ⊔ R) := by
  obtain ⟨M, hM, hxM, hKM⟩ := hx.exists_member h
  exact isDihedralTwoGroup_of_not_dStarAdj h.lemma22 h.asm hM h.mem (h.not_dStarAdj h.mem hM hKM)
    hxM hx.ne_one hx.mul_self (h.le_normalizer_K hx.mem) h.sylowR h.rot (h.le_normalizer_R hx.mem)

theorem cent (h : Hyp Ω S K R U t z) (hx : Outer Ω S U x) {b : G} (hbR : b ∈ R)
    (hb : x * b = b * x) : b = 1 ∨ b = z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨M, hM, hxM, hKM⟩ := hx.exists_member h
  set V : Subgroup G := zpowers x with hVdef
  have hV2 : IsPGroup 2 V :=
    isPGroup_zpowers_of_pow_eq_one (n := 1) (by rw [pow_one, pow_two]; exact hx.mul_self)
  have hVcard : Nat.card V = 2 := by
    rw [hVdef, Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact hx.mul_self) hx.ne_one
  have hVle : V ≤ M ⊓ normalizer (K : Set G) :=
    (zpowers_le).mpr (mem_inf.mpr ⟨hxM, h.le_normalizer_K hx.mem⟩)
  obtain ⟨V₁, hV₁, hVV₁⟩ := Asc76.Sec4.exists_isSylowOf_le hV2 hVle
  have hV₁1 : V₁ ≠ ⊥ := fun e => hx.ne_one (mem_bot.mp (e ▸ hVV₁ (mem_zpowers x)))
  have hV₁card := card_eq_two_of_not_dStarAdj h.lemma22 h.asm hM h.mem
    (h.not_dStarAdj h.mem hM hKM) hV₁ hV₁1
  have hVV : V = V₁ := eq_of_le_of_card_ge hVV₁ (by rw [hV₁card, hVcard])
  have hs : Setting22 Ω K M V R := ⟨h.mem, hM, hKM, hVV ▸ hV₁, hVV ▸ hV₁1, h.sylowR,
    (zpowers_le).mpr (h.le_normalizer_R hx.mem)⟩
  have hcard := hs.card_inf_normalizer h.lemma22 h.asm
  rw [hVcard] at hcard
  have hmem : ∀ c ∈ R, x * c = c * x → c ∈ R ⊓ normalizer (V : Set G) := fun c hc hxc =>
    mem_inf.mpr ⟨hc, mem_normalizer_of_commute' fun u hu => by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hu
      exact (Commute.zpow_left hxc k).eq⟩
  by_contra hne
  push Not at hne
  have h3 := three_le_card (hmem 1 R.one_mem (by group)) (hmem z (h.rot.le h.z_mem)
    (h.z_central x hx.mem)) (hmem b hbR hb) h.z_ne.symm (Ne.symm hne.1) (Ne.symm hne.2)
  omega

theorem mul_zinv (h : Hyp Ω S K R U t z) (hx : Outer Ω S U x) {u : G} (hu : u ∈ U) :
    IsZInv Ω (x * u) := by
  obtain ⟨c, hc⟩ := exists_conj_eq_mul_of_isDihedral h.rot (hx.not_mem_R h) hx.mul_self
    (hx.dihedral h) (hx.inv h) hu
  rw [← hc]
  exact IsZInv.conj h.asm hx.zinv c

end Outer

end Hyp

end CFSG.ComponentClassification.Asc76X.HallDihedral
