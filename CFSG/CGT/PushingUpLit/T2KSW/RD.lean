module

public import CFSG.CGT.PushingUpLit.T2KSW.CenW
public import CFSG.CGT.PushingUpLit.T2KSW.Defs

public section

namespace CFSG.CGT.PushingUpLit.T2KSW

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.T2K
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L M T : Subgroup G} {n : ℕ}

namespace Aux

omit [Finite G] in
theorem mem_normalizer_inf {A B : Subgroup G} {m : G}
    (hA : m ∈ Subgroup.normalizer (A : Set G)) (hB : m ∈ Subgroup.normalizer (B : Set G)) :
    m ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  simp only [Subgroup.mem_inf, Subgroup.mem_normalizer_iff.1 hA y,
    Subgroup.mem_normalizer_iff.1 hB y]

omit [Finite G] in
theorem card_sup_mul_card_inf_of_normal (A L : Subgroup G) [L.Normal] :
    Nat.card (A ⊔ L : Subgroup G) * Nat.card (A ⊓ L : Subgroup G) = Nat.card A * Nat.card L := by
  have h1 := Subgroup.relIndex_mul_card (H := L) (K := A ⊔ L)
  have h2 := Subgroup.relIndex_mul_card (H := L) (K := A)
  rw [Subgroup.relIndex_sup_right, inf_of_le_left (le_sup_right : L ≤ A ⊔ L)] at h1
  rw [inf_comm] at h2
  rw [← h1, ← h2]
  ring

omit [Finite G] in
theorem card_sup_mul_card_inf_of_le_normalizer {A B : Subgroup G}
    (hB : B ≤ Subgroup.normalizer (A : Set G)) :
    Nat.card (A ⊔ B : Subgroup G) * Nat.card (A ⊓ B : Subgroup G) = Nat.card A * Nat.card B := by
  set N := Subgroup.normalizer (A : Set G)
  have hAN : A ≤ N := Subgroup.le_normalizer
  have : (A.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  have h := card_sup_mul_card_inf_of_normal (B.subgroupOf N) (A.subgroupOf N)
  have hc : ∀ X : Subgroup G, X ≤ N → Nat.card (X.subgroupOf N) = Nat.card X := fun X hX =>
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv
  have hsup : B.subgroupOf N ⊔ A.subgroupOf N = (A ⊔ B).subgroupOf N := by
    rw [sup_comm]
    exact (Subgroup.subgroupOf_sup hAN hB).symm
  have hinf : B.subgroupOf N ⊓ A.subgroupOf N = (A ⊓ B).subgroupOf N := by
    rw [inf_comm]
    exact Subgroup.ext fun _ => Iff.rfl
  rw [hsup, hinf, hc _ (sup_le hAN hB), hc _ (inf_le_left.trans hAN), hc A hAN, hc B hB] at h
  rw [h, mul_comm]

omit [Finite G] in
theorem mem_sup_iff_mul {A B : Subgroup G} (hA : A ≤ Subgroup.normalizer (B : Set G)) {x : G} :
    x ∈ A ⊔ B ↔ ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  have := Subgroup.coe_mul_of_left_le_normalizer_right A B hA
  rw [← SetLike.mem_coe, this]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha, b, hb, rfl⟩

omit [Finite G] in
theorem mem_normalizer_sup {A B : Subgroup G} {m : G}
    (hA : m ∈ Subgroup.normalizer (A : Set G)) (hB : m ∈ Subgroup.normalizer (B : Set G)) :
    m ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  have key : ∀ m : G, m ∈ Subgroup.normalizer (A : Set G) → m ∈ Subgroup.normalizer (B : Set G) →
      ∀ y ∈ A ⊔ B, m * y * m⁻¹ ∈ A ⊔ B := by
    intro m hA hB
    have : A ⊔ B ≤ (A ⊔ B).comap (MulAut.conj m).toMonoidHom := by
      refine sup_le (fun a ha => ?_) (fun b hb => ?_)
      · exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.1 hA a).1 ha)
      · exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.1 hB b).1 hb)
    exact fun y hy => this hy
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key m hA hB y, fun hy => ?_⟩
  have := key m⁻¹ (Subgroup.inv_mem _ hA) (Subgroup.inv_mem _ hB) _ hy
  simpa [mul_assoc] using this

omit [Finite G] in
theorem comm_mem_subgroup {H : Subgroup G} {a b : G} (ha : a ∈ H) (hb : b ∈ H) : ⁅a, b⁆ ∈ H :=
  H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)

end Aux

open Aux

omit [Finite G] in
theorem Ec_le_T : Ec L T ≤ T := inf_le_left

omit [Finite G] in
theorem Dc_le_T : Dc L T ≤ T := inf_le_left

omit [Finite G] in
theorem Rl_le_T : Rl L T ≤ T := inf_le_left

omit [Finite G] in
theorem Rl_le_L : Rl L T ≤ L := inf_le_right

omit [Finite G] in
theorem mem_normalizer_centralizer_of_le (hMN : M ≤ Subgroup.normalizer (L : Set G)) {m : G}
    (hm : m ∈ M) : m ∈ Subgroup.normalizer (Subgroup.centralizer (L : Set G) : Set G) :=
  mem_normalizer_centralizer (hMN hm)

omit [Finite G] in
theorem mem_normalizer_Dc (hMN : M ≤ Subgroup.normalizer (L : Set G)) {m : G} (hm : m ∈ M)
    (hmT : m ∈ Subgroup.normalizer (T : Set G)) : m ∈ Subgroup.normalizer (Dc L T : Set G) :=
  mem_normalizer_inf hmT (mem_normalizer_centralizer
    (NatBlock.le_normalizer_blockU_of_le hMN hm))

omit [Finite G] in
theorem mem_normalizer_Ec (hMN : M ≤ Subgroup.normalizer (L : Set G)) {m : G} (hm : m ∈ M)
    (hmT : m ∈ Subgroup.normalizer (T : Set G)) : m ∈ Subgroup.normalizer (Ec L T : Set G) :=
  mem_normalizer_inf hmT (mem_normalizer_centralizer_of_le hMN hm)

omit [Finite G] in
theorem mem_normalizer_Rl (hMN : M ≤ Subgroup.normalizer (L : Set G)) {m : G} (hm : m ∈ M)
    (hmT : m ∈ Subgroup.normalizer (T : Set G)) : m ∈ Subgroup.normalizer (Rl L T : Set G) :=
  mem_normalizer_inf hmT (hMN hm)

omit [Finite G] in
theorem le_normalizer_Dc (hMN : M ≤ Subgroup.normalizer (L : Set G)) (hTM : T ≤ M) :
    T ≤ Subgroup.normalizer (Dc L T : Set G) :=
  fun _ hx => mem_normalizer_Dc hMN (hTM hx) (Subgroup.le_normalizer hx)

omit [Finite G] in
theorem le_normalizer_Ec (hMN : M ≤ Subgroup.normalizer (L : Set G)) (hTM : T ≤ M) :
    T ≤ Subgroup.normalizer (Ec L T : Set G) :=
  fun _ hx => mem_normalizer_Ec hMN (hTM hx) (Subgroup.le_normalizer hx)

omit [Finite G] in
theorem Ec_le_Dc : Ec L T ≤ Dc L T :=
  inf_le_inf_left T (Subgroup.centralizer_le (blockU_le L))

theorem blockU_le_Dc (h : NatBlock L n) (hLM : L ≤ M) (hMN : M ≤ Subgroup.normalizer (L : Set G))
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) : blockU L ≤ Dc L T := fun v hv =>
  ⟨NatBlock.blockU_le_sylow hLM hMN hT hv,
    Subgroup.mem_centralizer_iff.2 fun w hw => h.blockU_comm w hw v hv⟩

theorem oTwoIn_le_Dc (h : NatBlock L n) (hLM : L ≤ M)
    (hMN : M ≤ Subgroup.normalizer (L : Set G)) (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) :
    oTwoIn L ≤ Dc L T :=
  fun o ho => ⟨NatBlock.oTwoIn_le_sylow hLM hMN hT ho,
    Subgroup.mem_centralizer_iff.2 fun v hv => blockU_comm_of_short h.short v hv o ho⟩

theorem Dc_eq_inf_cenW (h : NatBlock L n) (hMN : M ≤ Subgroup.normalizer (L : Set G))
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) : Dc L T = T ⊓ cenW L M := by
  ext x
  constructor
  · rintro ⟨hxT, hxC⟩
    have hxM : x ∈ M := hT.le hxT
    refine ⟨hxT, mem_cenW.2 ⟨hxM, hMN hxM, fun l hl => ?_⟩⟩
    exact h.comm_centralizer_mem_oTwoIn hMN ⟨hxM, hxC⟩ hl
  · rintro ⟨hxT, hxW⟩
    obtain ⟨-, hxN, hxc⟩ := mem_cenW.1 hxW
    refine ⟨hxT, ?_⟩
    obtain ⟨k, hk⟩ := hT.isPGroup ⟨x, hxT⟩
    have hk' : x ^ 2 ^ k = 1 := congrArg Subtype.val hk
    refine h.centralizes_of_pow hxN hxc (k := k) fun v _ => ?_
    rw [hk']
    simp

theorem isSylowOf_Dc (hMN : M ≤ Subgroup.normalizer (L : Set G))
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) :
    CFSG.ABGLocalTools.IsSylowOf 2 (Dc L T) (M ⊓ Subgroup.centralizer (blockU L : Set G)) := by
  have := hT.inf_of_le_normalizer (N := M ⊓ Subgroup.centralizer (blockU L : Set G)) inf_le_left
    (NatBlock.le_normalizer_centralizer hMN)
  have e : T ⊓ (M ⊓ Subgroup.centralizer (blockU L : Set G)) = Dc L T := by
    ext x
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hx, -, hC⟩
      exact ⟨hx, hC⟩
    · rintro ⟨hx, hC⟩
      exact ⟨hx, hT.le hx, hC⟩
  rwa [e] at this

theorem Dc_sq_mem_Ec (h : NatBlock L n) (hMN : M ≤ Subgroup.normalizer (L : Set G))
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) {d : G} (hd : d ∈ Dc L T) : d ^ 2 ∈ Ec L T :=
  ⟨T.pow_mem hd.1 2, h.sq_mem_centralizer hMN ⟨hT.le hd.1, hd.2⟩⟩

theorem Dc_comm_mem_Ec (h : NatBlock L n) (hMN : M ≤ Subgroup.normalizer (L : Set G))
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) {d d' : G} (hd : d ∈ Dc L T) (hd' : d' ∈ Dc L T) :
    ⁅d, d'⁆ ∈ Ec L T :=
  ⟨comm_mem_subgroup hd.1 hd'.1,
    h.comm_mem_centralizer hMN ⟨hT.le hd.1, hd.2⟩ ⟨hT.le hd'.1, hd'.2⟩⟩

theorem card_Dc_le (h : NatBlock L n) (hLM : L ≤ M) (hMN : M ≤ Subgroup.normalizer (L : Set G))
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) :
    Nat.card (Dc L T) ≤ 2 ^ n * Nat.card ↥(Ec L T ⊔ blockU L) := by
  set Q : Subgroup G := M ⊓ Subgroup.centralizer (blockU L : Set G) with hQ
  set C : Subgroup G := M ⊓ Subgroup.centralizer (L : Set G) with hC
  have hVD := blockU_le_Dc h hLM hMN hT
  have hEVD : Ec L T ⊔ blockU L ≤ Dc L T := sup_le Ec_le_Dc hVD
  have hDQ : Dc L T ≤ Q := fun x hx => ⟨hT.le hx.1, hx.2⟩
  have hCN : C ≤ Subgroup.normalizer (blockU L : Set G) := fun c hc =>
    NatBlock.le_normalizer_blockU_of_le hMN hc.1
  have key : (C ⊔ blockU L) ⊓ Dc L T = Ec L T ⊔ blockU L := by
    apply le_antisymm
    · rintro x ⟨hxK, hxD⟩
      obtain ⟨c, hc, v, hv, rfl⟩ := (mem_sup_iff_mul hCN).1 hxK
      have hvT : v ∈ T := NatBlock.blockU_le_sylow hLM hMN hT hv
      have hcT : c ∈ T := by
        have := T.mul_mem hxD.1 (T.inv_mem hvT)
        simpa using this
      exact mul_mem (Subgroup.mem_sup_left ⟨hcT, hc.2⟩) (Subgroup.mem_sup_right hv)
    · exact le_inf (sup_le_sup_right (fun x hx => ⟨hT.le hx.1, hx.2⟩) _) hEVD
  have h1 := h.relIndex_le hLM hMN
  have hne : (C ⊔ blockU L).relIndex Q ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h2 : (C ⊔ blockU L).relIndex (Dc L T) ≤ (C ⊔ blockU L).relIndex Q :=
    Subgroup.relIndex_le_of_le_right hDQ hne
  have h3 : (Ec L T ⊔ blockU L).relIndex (Dc L T) = (C ⊔ blockU L).relIndex (Dc L T) := by
    have := Subgroup.inf_relIndex_right (C ⊔ blockU L) (Dc L T)
    rwa [key] at this
  have h4 := Subgroup.relIndex_mul_card (H := Ec L T ⊔ blockU L) (K := Dc L T)
  rw [inf_of_le_left hEVD] at h4
  rw [← h4]
  exact Nat.mul_le_mul_right _ (h3 ▸ h2.trans h1)

theorem isSylowOf_Rl (hLM : L ≤ M) (hMN : M ≤ Subgroup.normalizer (L : Set G))
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) : CFSG.ABGLocalTools.IsSylowOf 2 (Rl L T) L :=
  hT.inf_of_le_normalizer hLM hMN

theorem Rl_inf_Dc (h : NatBlock L n) (hLM : L ≤ M) (hMN : M ≤ Subgroup.normalizer (L : Set G))
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) : Rl L T ⊓ Dc L T = oTwoIn L := by
  apply le_antisymm
  · rintro x ⟨⟨_, hxL⟩, _, hxC⟩
    rw [← h.inf_centralizer_blockU]
    exact ⟨hxL, hxC⟩
  · intro w hw
    exact ⟨⟨NatBlock.oTwoIn_le_sylow hLM hMN hT hw, oTwoIn_le L hw⟩,
      oTwoIn_le_Dc h hLM hMN hT hw⟩

theorem L_inf_cenW (h : NatBlock L n) (hLM : L ≤ M) : L ⊓ cenW L M = oTwoIn L := by
  apply le_antisymm
  · rintro l ⟨hl, hlC⟩
    obtain ⟨-, -, hlc⟩ := mem_cenW.1 hlC
    set D := h.natData
    have h1 : D.φ ⟨l, hl⟩ ∈
        Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨l', rfl⟩ := D.φ_surj g
      have hmem : (((⁅(⟨l, hl⟩ : ↥L), l'⁆ : ↥L)) : G) ∈ oTwoIn L := hlc l' l'.2
      have h2 : D.φ ⁅(⟨l, hl⟩ : ↥L), l'⁆ = 1 := (D.φ_ker _).2 hmem
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h2
      exact h2.symm
    rw [sl2_center_eq_bot, Subgroup.mem_bot] at h1
    exact (D.φ_ker ⟨l, hl⟩).1 h1
  · intro w hw
    refine ⟨oTwoIn_le L hw, mem_cenW.2 ⟨hLM (oTwoIn_le L hw),
      Subgroup.le_normalizer (oTwoIn_le L hw), fun l hl => ?_⟩⟩
    have e : ⁅w, l⁆ = w * (l * w⁻¹ * l⁻¹) := by simp [commutatorElement_def, mul_assoc]
    rw [e]
    exact mul_mem hw (conj_mem_oTwoIn (Subgroup.le_normalizer hl) (inv_mem hw))

theorem card_Rl (h : NatBlock L n) (hLM : L ≤ M) (hMN : M ≤ Subgroup.normalizer (L : Set G))
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) :
    Nat.card (Rl L T) = 2 ^ n * Nat.card (oTwoIn L) := by
  classical
  have hn : n ≠ 0 := by have := h.two_le; omega
  set D := h.natData with hD
  have hker : D.φ.ker = (oTwoIn L).subgroupOf L := by
    ext l
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact D.φ_ker l
  have hWcard : Nat.card D.φ.ker = Nat.card (oTwoIn L) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (oTwoIn_le L)).toEquiv
  have hLcard : Nat.card (oTwoIn L) * (2 ^ n * ((2 ^ n) ^ 2 - 1)) = Nat.card L := by
    have h1 := Subgroup.card_ker_mul_card_of_surjective D.φ_surj
    rw [hWcard, CFSG.CGT.PushingUpLit.T2K.card_sl2_field, GaloisField.card 2 n hn] at h1
    exact h1
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).1 (isPGroup_oTwoIn L)
  have hodd : ¬ 2 ∣ (2 ^ n) ^ 2 - 1 :=
    Nat.two_dvd_ne_zero.2 (Nat.odd_iff.1 (odd_sq_two_pow_sub_one (by omega : 1 ≤ n)))
  have h4 : 4 ≤ (2 ^ n) ^ 2 := by
    have : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    nlinarith
  have hfact : (Nat.card L).factorization 2 = k + n := by
    rw [← hLcard, hk, Nat.factorization_mul (by positivity)
      (Nat.mul_ne_zero (by positivity) (by omega)), Finsupp.add_apply,
      Nat.factorization_mul (by positivity) (by omega), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Nat.Prime.factorization_pow Nat.prime_two,
      Finsupp.single_eq_same, Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd hodd]
    omega
  rw [(isSylowOf_Rl hLM hMN hT).card_eq, hfact, hk, pow_add, mul_comm]

theorem card_sup_Rl_Dc (h : NatBlock L n) (hLM : L ≤ M) (hMN : M ≤ Subgroup.normalizer (L : Set G))
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) :
    Nat.card ↥(Rl L T ⊔ Dc L T) * Nat.card (oTwoIn L) = Nat.card (Dc L T) * Nat.card (Rl L T) := by
  have hRn : Rl L T ≤ Subgroup.normalizer (Dc L T : Set G) :=
    Rl_le_T.trans (le_normalizer_Dc hMN hT.le)
  have hRD := card_sup_mul_card_inf_of_le_normalizer hRn
  rw [inf_comm, Rl_inf_Dc h hLM hMN hT, sup_comm] at hRD
  exact hRD

theorem card_Rl_sup_Dc (h : NatBlock L n) (hLM : L ≤ M)
    (hMN : M ≤ Subgroup.normalizer (L : Set G)) (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) :
    Nat.card ↥(Rl L T ⊔ Dc L T) = 2 ^ n * Nat.card (Dc L T) := by
  have h1 := card_sup_Rl_Dc h hLM hMN hT
  rw [card_Rl h hLM hMN hT] at h1
  have hpos : 0 < Nat.card (oTwoIn L) := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [h1]
  ring

theorem inf_sup_cenW (h : NatBlock L n) (hLM : L ≤ M) (hMN : M ≤ Subgroup.normalizer (L : Set G))
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) : T ⊓ (L ⊔ cenW L M) = Rl L T ⊔ Dc L T := by
  classical
  have hCN : cenW L M ≤ Subgroup.normalizer (L : Set G) := cenW_le_normalizer
  have hDeq : Dc L T = T ⊓ cenW L M := Dc_eq_inf_cenW h hMN hT
  have hRsyl : CFSG.ABGLocalTools.IsSylowOf 2 (Rl L T) L := isSylowOf_Rl hLM hMN hT
  have hDsyl : CFSG.ABGLocalTools.IsSylowOf 2 (Dc L T) (cenW L M) := by
    have := hT.inf_of_le_normalizer (N := cenW L M) cenW_le (le_normalizer_cenW hMN)
    rwa [← hDeq] at this
  have hRDK : Rl L T ⊔ Dc L T ≤ L ⊔ cenW L M :=
    sup_le_sup Rl_le_L (hDeq ▸ inf_le_right)
  have hRDT : Rl L T ⊔ Dc L T ≤ T := sup_le Rl_le_T Dc_le_T
  have hKcard := card_sup_mul_card_inf_of_le_normalizer hCN
  rw [L_inf_cenW h hLM] at hKcard
  have hRD := card_sup_Rl_Dc h hLM hMN hT
  have hR1 := Subgroup.relIndex_mul_card (H := Rl L T) (K := L)
  rw [inf_of_le_left Rl_le_L] at hR1
  have hD1 := Subgroup.relIndex_mul_card (H := Dc L T) (K := cenW L M)
  rw [inf_of_le_left (hDeq ▸ inf_le_right : Dc L T ≤ cenW L M)] at hD1
  have hK1 := Subgroup.relIndex_mul_card (H := Rl L T ⊔ Dc L T) (K := L ⊔ cenW L M)
  rw [inf_of_le_left hRDK] at hK1
  have hx : (Rl L T ⊔ Dc L T).relIndex (L ⊔ cenW L M) =
      (Rl L T).relIndex L * (Dc L T).relIndex (cenW L M) := by
    apply Nat.eq_of_mul_eq_mul_right
      (Nat.mul_pos (Nat.card_pos (α := ↥(Rl L T ⊔ Dc L T))) (Nat.card_pos (α := ↥(oTwoIn L))))
    calc (Rl L T ⊔ Dc L T).relIndex (L ⊔ cenW L M) *
          (Nat.card ↥(Rl L T ⊔ Dc L T) * Nat.card ↥(oTwoIn L))
        = ((Rl L T ⊔ Dc L T).relIndex (L ⊔ cenW L M) * Nat.card ↥(Rl L T ⊔ Dc L T)) *
          Nat.card ↥(oTwoIn L) := by ring
      _ = Nat.card ↥(L ⊔ cenW L M) * Nat.card ↥(oTwoIn L) := by rw [hK1]
      _ = Nat.card ↥L * Nat.card ↥(cenW L M) := hKcard
      _ = ((Rl L T).relIndex L * Nat.card ↥(Rl L T)) *
          ((Dc L T).relIndex (cenW L M) * Nat.card ↥(Dc L T)) := by rw [hR1, hD1]
      _ = ((Rl L T).relIndex L * (Dc L T).relIndex (cenW L M)) *
          (Nat.card ↥(Dc L T) * Nat.card ↥(Rl L T)) := by ring
      _ = ((Rl L T).relIndex L * (Dc L T).relIndex (cenW L M)) *
          (Nat.card ↥(Rl L T ⊔ Dc L T) * Nat.card ↥(oTwoIn L)) := by rw [hRD]
  have hodd : ¬ 2 ∣ (Rl L T ⊔ Dc L T).relIndex (L ⊔ cenW L M) := by
    rw [hx]
    intro hdvd
    rcases (Nat.Prime.dvd_mul Nat.prime_two).1 hdvd with h1 | h1
    · exact ((CFSG.ABGLocalTools.isSylowOf_iff.1 hRsyl).2.2) h1
    · exact ((CFSG.ABGLocalTools.isSylowOf_iff.1 hDsyl).2.2) h1
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 2 (Rl L T ⊔ Dc L T) (L ⊔ cenW L M) :=
    CFSG.ABGLocalTools.isSylowOf_iff.2 ⟨hRDK, hT.isPGroup.to_le hRDT, hodd⟩
  exact hSyl.eq_of_le (le_inf hRDT hRDK) inf_le_right (hT.isPGroup.to_le inf_le_left)

theorem relIndex_Rl_inf_Dc (h : NatBlock L n) (hLM : L ≤ M)
    (hMN : M ≤ Subgroup.normalizer (L : Set G)) (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) :
    (Rl L T ⊓ Dc L T).relIndex (Rl L T) = 2 ^ n := by
  have hWR : oTwoIn L ≤ Rl L T := (Rl_inf_Dc h hLM hMN hT) ▸ inf_le_left
  rw [Rl_inf_Dc h hLM hMN hT]
  have h1 := Subgroup.relIndex_mul_card (H := oTwoIn L) (K := Rl L T)
  rw [inf_of_le_left hWR, card_Rl h hLM hMN hT] at h1
  have hpos : 0 < Nat.card (oTwoIn L) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos h1

theorem Qc_eq_Dc_sup (h : NatBlock L n) (hMN : M ≤ Subgroup.normalizer (L : Set G))
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) :
    M ⊓ Subgroup.centralizer (blockU L : Set G) =
      Dc L T ⊔ (M ⊓ Subgroup.centralizer (L : Set G)) := by
  classical
  set Q : Subgroup G := M ⊓ Subgroup.centralizer (blockU L : Set G) with hQ
  set C : Subgroup G := M ⊓ Subgroup.centralizer (L : Set G) with hC
  have hDQ : Dc L T ≤ Q := fun x hx => ⟨hT.le hx.1, hx.2⟩
  have hCQ : C ≤ Q := fun c hc => ⟨hc.1, Subgroup.mem_centralizer_iff.2 fun w hw =>
    Subgroup.mem_centralizer_iff.1 hc.2 w (blockU_le L hw)⟩
  refine le_antisymm ?_ (sup_le hDQ hCQ)
  have hsyl := isSylowOf_Dc hMN hT
  have hodd : ¬ 2 ∣ (Dc L T).relIndex Q := (CFSG.ABGLocalTools.isSylowOf_iff.1 hsyl).2.2
  have hCn : Q ≤ Subgroup.normalizer (C : Set G) := fun q hq =>
    mem_normalizer_inf (Subgroup.le_normalizer hq.1) (mem_normalizer_centralizer (hMN hq.1))
  have hnorm : (C.subgroupOf Q).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCQ).2 hCn
  have h2grp : IsPGroup 2 (↥Q ⧸ C.subgroupOf Q) := by
    intro x
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨k, hk⟩ := h.two_quot_of_centralizes hMN q.2.1 q.2.2
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact ⟨M.pow_mem q.2.1 _, hk⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).1 h2grp
  have h1 : C.relIndex Q = 2 ^ k := by
    rw [Subgroup.relIndex, Subgroup.index_eq_card, hk]
  have h2 : (Dc L T ⊔ C).relIndex Q ∣ 2 ^ k :=
    h1 ▸ Subgroup.relIndex_dvd_of_le_left Q (le_sup_right : C ≤ Dc L T ⊔ C)
  have h3 : (Dc L T ⊔ C).relIndex Q ∣ (Dc L T).relIndex Q :=
    Subgroup.relIndex_dvd_of_le_left Q (le_sup_left : Dc L T ≤ Dc L T ⊔ C)
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
  have hi0 : i = 0 := by
    by_contra hne
    exact hodd ((hi ▸ dvd_pow_self 2 hne : 2 ∣ (Dc L T ⊔ C).relIndex Q).trans h3)
  rw [hi0, pow_zero] at hi
  exact Subgroup.relIndex_eq_one.1 hi

end CFSG.CGT.PushingUpLit.T2KSW
