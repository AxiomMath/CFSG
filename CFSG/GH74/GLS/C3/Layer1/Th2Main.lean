module

public import CFSG.GH74.GLS.C3.Layer1.Th2Leaves
public import CFSG.GH74.GLS.C3.Layer1.Th2SigHalf
public import CFSG.GH74.GLS.C3.Layer1.Split
public import CFSG.GH74.GLS.C3.Layer1.BackBasic

public section

namespace CFSG.GH74.GLS.Th2

open Subgroup CFSG.ABGLocalTools CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G]

theorem exists_sylow_cap [Finite G] {N C : Subgroup G} (hNC : N ≤ C) {y : G} (hy : y ∈ N)
    (hy2 : IsPGroup 2 (zpowers y)) :
    ∃ T : Subgroup G, IsSylowOf 2 T C ∧ y ∈ T ∧ IsSylowOf 2 (T ⊓ N) N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : IsPGroup 2 ((zpowers y).subgroupOf N) := hy2.comap_subtype
  obtain ⟨Q0, hQ0⟩ := h1.exists_le_sylow
  have hT0 : IsSylowOf 2 (Q0.map N.subtype) N := ⟨Q0, rfl⟩
  have hyT0 : y ∈ Q0.map N.subtype := by
    refine ⟨⟨y, hy⟩, hQ0 ?_, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    exact mem_zpowers y
  have h2 : IsPGroup 2 ((Q0.map N.subtype).subgroupOf C) := hT0.isPGroup.comap_subtype
  obtain ⟨Q1, hQ1⟩ := h2.exists_le_sylow
  have hT : IsSylowOf 2 (Q1.map C.subtype) C := ⟨Q1, rfl⟩
  have hT0T : Q0.map N.subtype ≤ Q1.map C.subtype := by
    intro t ht
    have htC : t ∈ C := hNC (hT0.le ht)
    refine ⟨⟨t, htC⟩, hQ1 ?_, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    exact ht
  refine ⟨Q1.map C.subtype, hT, hT0T hyT0, ?_⟩
  have heq : Q1.map C.subtype ⊓ N = Q0.map N.subtype :=
    hT0.eq_of_le (le_inf hT0T hT0.le) inf_le_right (hT.isPGroup.to_inf_left)
  rw [heq]
  exact hT0

theorem exists_coatom_ge [Finite G] {N : Subgroup G} (h : N ≠ ⊤) :
    ∃ M : Subgroup G, IsCoatom M ∧ N ≤ M := by
  rcases eq_top_or_exists_le_coatom N with h' | ⟨M, hM, hNM⟩
  · exact absurd h' h
  · exact ⟨M, hM, hNM⟩

theorem exists_th2Std [Finite G] {x y : G} {K : Subgroup G} (h : IsV2StarStar x y K) :
    ∃ T S : Subgroup G, Th2Std x y K T S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨_, hy2, hyC, hyN, _⟩ := h.isV2Triple.1
  have hyN' : y ∈ NxK x K := ⟨hyC, hyN⟩
  have hNC : NxK x K ≤ centralizer ({x} : Set G) := inf_le_left
  have hy2' : IsPGroup 2 (zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy2, pow_one])
  obtain ⟨T, hT, hyT, hTN⟩ := exists_sylow_cap hNC hyN' hy2'
  obtain ⟨S0, hS0⟩ := hT.isPGroup.exists_le_sylow
  have hSsyl : IsSylowOf 2 (S0 : Subgroup G) ⊤ := by
    rw [isSylowOf_iff]
    refine ⟨le_top, S0.isPGroup', ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact S0.not_dvd_index
  exact ⟨T, S0, ⟨h, ⟨hT, hTN⟩, hyT, hSsyl, hS0⟩⟩

theorem exists_involution_mem [Finite G] {P : Subgroup G} (hP : IsPGroup 2 P) (hne : P ≠ ⊥) :
    ∃ u ∈ P, orderOf u = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hn1 : n ≠ 0 := by
    rintro rfl
    apply hne
    rw [pow_zero] at hn
    exact Subgroup.card_eq_one.1 hn
  have hdvd : 2 ∣ Nat.card P := by rw [hn]; exact dvd_pow_self 2 hn1
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  exact ⟨x, x.2, by rw [← hx]; exact Subgroup.orderOf_coe x⟩

theorem exists_mem_normalizer_of_lt [Finite G] {T S : Subgroup G} (hS : IsPGroup 2 S)
    (hTS : T < S) : ∃ a ∈ S, a ∈ normalizer (T : Set G) ∧ a ∉ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnil : Group.IsNilpotent ↥S := hS.isNilpotent
  have hlt : T.subgroupOf S < ⊤ := by
    refine lt_top_iff_ne_top.2 fun htop => ?_
    apply hTS.not_ge
    intro s hs
    have : (⟨s, hs⟩ : ↥S) ∈ T.subgroupOf S := by rw [htop]; trivial
    exact this
  have h := Group.normalizerCondition_of_isNilpotent (G := ↥S) (T.subgroupOf S) hlt
  obtain ⟨a, haN, haT⟩ := IsConcreteLE.exists_of_lt h
  refine ⟨a, a.2, ?_, fun h' => haT ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro g
    rw [Subgroup.mem_normalizer_iff] at haN
    constructor
    · intro hg
      have := (haN ⟨g, hTS.le hg⟩).1 (by rw [Subgroup.mem_subgroupOf]; exact hg)
      rw [Subgroup.mem_subgroupOf] at this
      exact this
    · intro hg
      have hgS : g ∈ S := by
        have : (a : G) * g * (a : G)⁻¹ ∈ S := hTS.le hg
        have h2 := S.mul_mem (S.mul_mem (S.inv_mem a.2) this) a.2
        simpa [mul_assoc] using h2
      have := (haN ⟨g, hgS⟩).2 (by rw [Subgroup.mem_subgroupOf]; exact hg)
      rw [Subgroup.mem_subgroupOf] at this
      exact this
  · rw [Subgroup.mem_subgroupOf]; exact h'

theorem exists_minSubnormal [Finite G] {K M : Subgroup G} (hKM : K ≤ M) :
    ∃ L : Subgroup G, IsMinSubnormalIn K M L := by
  let s : Set (Subgroup G) := {J | K ≤ J ∧ IsSubnormalIn J M}
  have hne : s.Nonempty := by
    refine ⟨M, hKM, le_rfl, ?_⟩
    rw [Subgroup.subgroupOf_self]
    exact Subgroup.normal_top.isSubnormal
  obtain ⟨L, hLs, hmin⟩ := Set.exists_min_image s (fun J => Nat.card J) (Set.toFinite s) hne
  exact ⟨L, hLs.1, hLs.2, fun J hKJ hJL hJs =>
    Subgroup.eq_of_le_of_card_ge hJL (hmin J ⟨hKJ, hJs⟩)⟩

theorem eq_of_isMinSubnormalIn_of_normal {K M L : Subgroup G} (hKM : K ≤ M)
    (hn : M ≤ normalizer (K : Set G)) (hL : IsMinSubnormalIn K M L) : K = L := by
  have hKsub : IsSubnormalIn K M := by
    refine ⟨hKM, ?_⟩
    have : (K.subgroupOf M).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).2 hn
    exact Subgroup.Normal.isSubnormal inferInstance
  exact hL.2.2 K le_rfl hL.1 hKsub

theorem pPrimeCoreOf_le_of_subnormal [Finite G] {L M : Subgroup G} (h : IsSubnormalIn L M) :
    pPrimeCoreOf 2 L ≤ pPrimeCoreOf 2 M := by
  have h1 := CFSG.Walter.map_pPrimeCore_le_of_isSubnormal h.2
  rw [TwoThin.pPrimeCoreOf_eq_map_subgroupOf h.1]
  exact Subgroup.map_mono h1

theorem mem_normalizer_sup {A B : Subgroup G} {c : G} (hA : c ∈ normalizer (A : Set G))
    (hB : c ∈ normalizer (B : Set G)) : c ∈ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  have key : ∀ {c : G}, c ∈ normalizer (A : Set G) → c ∈ normalizer (B : Set G) →
      ∀ k ∈ A ⊔ B, c * k * c⁻¹ ∈ A ⊔ B := by
    intro c hA hB k hk
    rw [Subgroup.sup_eq_closure] at hk
    induction hk using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.1 hA x).1 hx)
      · exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.1 hB x).1 hx)
    | one => simp
    | mul x y _ _ hx hy =>
      have : c * (x * y) * c⁻¹ = (c * x * c⁻¹) * (c * y * c⁻¹) := by group
      rw [this]; exact Subgroup.mul_mem _ hx hy
    | inv x _ hx =>
      have : c * x⁻¹ * c⁻¹ = (c * x * c⁻¹)⁻¹ := by group
      rw [this]; exact Subgroup.inv_mem _ hx
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨key hA hB h, fun hh => ?_⟩
  have := key (Subgroup.inv_mem _ hA) (Subgroup.inv_mem _ hB) _ hh
  simpa [mul_assoc] using this

theorem comm_mem_sup {O A B : Subgroup G} {c : G} (hAO : A ≤ normalizer (O : Set G))
    (hBO : B ≤ normalizer (O : Set G))
    (hA : ∀ a ∈ A, ⁅a, c⁆ ∈ O) (hB : ∀ b ∈ B, ⁅b, c⁆ ∈ O) :
    ∀ k ∈ A ⊔ B, ⁅k, c⁆ ∈ O := by
  intro k hk
  have key : k ∈ normalizer (O : Set G) ∧ ⁅k, c⁆ ∈ O := by
    rw [Subgroup.sup_eq_closure] at hk
    induction hk using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · exact ⟨hAO hx, hA x hx⟩
      · exact ⟨hBO hx, hB x hx⟩
    | one => exact ⟨Subgroup.one_mem _, by simp⟩
    | mul x y _ _ hx hy =>
      refine ⟨Subgroup.mul_mem _ hx.1 hy.1, ?_⟩
      have h1 : ⁅x * y, c⁆ = x * ⁅y, c⁆ * x⁻¹ * ⁅x, c⁆ := by
        simp only [commutatorElement_def]; group
      rw [h1]
      refine O.mul_mem ?_ hx.2
      exact (Subgroup.mem_normalizer_iff.1 hx.1 _).1 hy.2
    | inv x _ hx =>
      refine ⟨Subgroup.inv_mem _ hx.1, ?_⟩
      have h1 : ⁅x⁻¹, c⁆ = x⁻¹ * (⁅x, c⁆)⁻¹ * x := by
        simp only [commutatorElement_def]; group
      rw [h1]
      have h2 := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hx.1) _).1 (O.inv_mem hx.2)
      simpa using h2
  exact key.2

theorem inf_le_pPrimeCoreOf [Finite G] {L M : Subgroup G} (hLM : L ≤ M) :
    pPrimeCoreOf 2 M ⊓ L ≤ pPrimeCoreOf 2 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := pPrimeCoreOf 2 M ⊓ L with hW
  have hWL : W ≤ L := inf_le_right
  have hN : (W.subgroupOf L).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hgM : (g : G) ∈ M := hLM g.2
    refine ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.1
        (TwoThin.mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer hgM)) _).1 hn.1
    · exact L.mul_mem (L.mul_mem g.2 hn.2) (L.inv_mem g.2)
  have hcop : Nat.Coprime 2 (Nat.card W) := by
    have h1 : Nat.card W ∣ Nat.card (pPrimeCoreOf 2 M) := Subgroup.card_dvd_of_le inf_le_left
    have h2 : Nat.card (pPrimeCoreOf 2 M) = Nat.card (pPrimeCore 2 ↥M) :=
      Subgroup.card_map_of_injective M.subtype_injective
    rw [h2] at h1
    exact Nat.Coprime.coprime_dvd_right h1 CFSG.pPrimeCore_coprime_card
  have hcard : Nat.card (W.subgroupOf L) = Nat.card W :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWL).toEquiv
  have h1 : W.subgroupOf L ≤ pPrimeCore 2 ↥L := le_sSup ⟨hN, by rw [hcard]; exact hcop⟩
  have h2 : (W.subgroupOf L).map L.subtype = W := Subgroup.map_subgroupOf_eq_of_le hWL
  rw [← h2]
  exact Subgroup.map_mono h1

theorem sup_pPrimeCoreOf_eq [Finite G] {K L M : Subgroup G} (hsub : IsSubnormalIn L M)
    (hLeq : L = pPrimeCoreOf 2 L ⊔ K) :
    K ⊔ pPrimeCoreOf 2 M = L ⊔ pPrimeCoreOf 2 M := by
  have hOLO : pPrimeCoreOf 2 L ≤ pPrimeCoreOf 2 M := pPrimeCoreOf_le_of_subnormal hsub
  have hKL : K ≤ L := le_trans le_sup_right hLeq.ge
  apply le_antisymm
  · exact sup_le_sup_right hKL _
  · refine sup_le ?_ le_sup_right
    calc L = pPrimeCoreOf 2 L ⊔ K := hLeq
      _ ≤ K ⊔ pPrimeCoreOf 2 M := sup_le (hOLO.trans le_sup_right) le_sup_left

theorem cmbar_eq_cmk [Finite G] {K L M : Subgroup G}
    (hLM : L ≤ M) (hnorm : ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L)
    (hsub : IsSubnormalIn L M) (hLeq : L = pPrimeCoreOf 2 L ⊔ K) :
    CMbar M K = CMK M L := by
  have hOLO : pPrimeCoreOf 2 L ≤ pPrimeCoreOf 2 M := pPrimeCoreOf_le_of_subnormal hsub
  have hKO := sup_pPrimeCoreOf_eq hsub hLeq
  have hNL : ∀ g ∈ M, g ∈ normalizer (L : Set G) := fun g hg =>
    C3.Layer1.U1a.mem_normalizer_of_norm hnorm hg
  have hNO : ∀ g ∈ M, g ∈ normalizer (pPrimeCoreOf 2 M : Set G) := fun g hg =>
    TwoThin.mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer hg)
  unfold CMbar CMK
  rw [hKO]
  ext c
  simp only [Subgroup.mem_inf]
  constructor
  · rintro ⟨hcM, _, _, hcomm⟩
    refine ⟨hcM, hNL c hcM, C3.Layer1.U1a.mem_normalizer_pPrimeCoreOf hnorm hcM, fun l hl => ?_⟩
    have h1 : ⁅l, c⁆ ∈ pPrimeCoreOf 2 M := hcomm l (Subgroup.mem_sup_left hl)
    have h2 : ⁅l, c⁆ ∈ L := by
      have : ⁅l, c⁆ = l * (c * l⁻¹ * c⁻¹) := by simp only [commutatorElement_def]; group
      rw [this]
      exact L.mul_mem hl (hnorm c hcM l⁻¹ (L.inv_mem hl))
    exact inf_le_pPrimeCoreOf hLM ⟨h1, h2⟩
  · rintro ⟨hcM, hcN1, _, hcomm⟩
    refine ⟨hcM, mem_normalizer_sup hcN1 (hNO c hcM), hNO c hcM, ?_⟩
    refine comm_mem_sup (O := pPrimeCoreOf 2 M) (A := L) (B := pPrimeCoreOf 2 M) ?_ ?_ ?_ ?_
    · exact fun l hl => hNO l (hLM hl)
    · exact fun o ho => Subgroup.le_normalizer ho
    · exact fun a ha => hOLO (hcomm a ha)
    · intro b hb
      have : ⁅b, c⁆ = b * (c * b⁻¹ * c⁻¹) := by simp only [commutatorElement_def]; group
      rw [this]
      exact (pPrimeCoreOf 2 M).mul_mem hb
        ((Subgroup.mem_normalizer_iff.1 (hNO c hcM) _).1 ((pPrimeCoreOf 2 M).inv_mem hb))

theorem cmk_normal {L M : Subgroup G} (hnorm : ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L) :
    ∀ m ∈ M, ∀ c ∈ CMK M L, m * c * m⁻¹ ∈ CMK M L := by
  intro m hm c hc
  rw [C3.Layer1.U1a.mem_CMK_iff] at hc ⊢
  obtain ⟨hcM, -, -, hcomm⟩ := hc
  have hmc : m * c * m⁻¹ ∈ M := M.mul_mem (M.mul_mem hm hcM) (M.inv_mem hm)
  refine ⟨hmc, C3.Layer1.U1a.mem_normalizer_of_norm hnorm hmc,
    C3.Layer1.U1a.mem_normalizer_pPrimeCoreOf hnorm hmc, fun l hl => ?_⟩
  have h1 : ⁅l, m * c * m⁻¹⁆ = m * ⁅m⁻¹ * l * m, c⁆ * m⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [h1]
  have hl' : m⁻¹ * l * m ∈ L := by simpa using hnorm m⁻¹ (M.inv_mem hm) l hl
  exact C3.Layer1.U1a.pPrimeCoreOf_norm hnorm hm (hcomm _ hl')

theorem sylow_TM [Finite G] {M L T Q : Subgroup G} {x : G}
    (hnorm : ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L)
    (hTM : T ≤ M) (hT : IsPGroup 2 T) (hQT : Q ≤ T) (hxQ : x ∈ Q) (hx2 : orderOf x = 2)
    (hQC : IsSylowOf 2 Q (CMK M L))
    (hc5 : ∀ u ∈ Q, (∀ t ∈ T, u * t = t * u) → orderOf u = 2 →
      IsSylowOf 2 T (centralizer ({u} : Set G))) :
    IsSylowOf 2 T M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : IsPGroup 2 (T.subgroupOf M) := hT.comap_subtype
  obtain ⟨W0, hW0⟩ := h1.exists_le_sylow
  have hWsyl : IsSylowOf 2 (W0.map M.subtype) M := ⟨W0, rfl⟩
  set W : Subgroup G := W0.map M.subtype with hW
  have hTW : T ≤ W := fun t ht =>
    ⟨⟨t, hTM ht⟩, hW0 (by rw [Subgroup.mem_subgroupOf]; exact ht), rfl⟩
  have hWM : W ≤ M := hWsyl.le
  have hWp : IsPGroup 2 W := hWsyl.isPGroup
  have hWC : W ⊓ CMK M L = Q :=
    hQC.eq_of_le (le_inf (hQT.trans hTW) hQC.le) inf_le_right hWp.to_inf_left
  have hQW : ∀ w ∈ W, ∀ q ∈ Q, w * q * w⁻¹ ∈ Q := by
    intro w hw q hq
    have : w * q * w⁻¹ ∈ W ⊓ CMK M L :=
      ⟨W.mul_mem (W.mul_mem hw (hTW (hQT hq))) (W.inv_mem hw),
        cmk_normal hnorm w (hWM hw) q (hQC.le hq)⟩
    rwa [hWC] at this
  have hnil : Group.IsNilpotent ↥W := hWp.isNilpotent
  have hxW : x ∈ W := hTW (hQT hxQ)
  let H : Subgroup ↥W := Q.subgroupOf W
  have hHn : H.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hQW g g.2 n hn⟩
  have hHne : H ≠ ⊥ := by
    intro hbot
    have hmem : (⟨x, hxW⟩ : ↥W) ∈ H := by rw [Subgroup.mem_subgroupOf]; exact hxQ
    rw [hbot, Subgroup.mem_bot] at hmem
    have hx1 : x = 1 := congrArg Subtype.val hmem
    rw [hx1, orderOf_one] at hx2
    exact absurd hx2 (by norm_num)
  have hne2 := Group.IsNilpotent.inf_center_ne_bot_of_normal hHne
  set P0 : Subgroup G := (H ⊓ center ↥W).map W.subtype with hP0def
  have hP0W : P0 ≤ W := Subgroup.map_subtype_le _
  have hP0p : IsPGroup 2 P0 := hWp.to_le hP0W
  have hP0ne : P0 ≠ ⊥ := by
    intro h
    exact hne2 ((Subgroup.map_eq_bot_iff_of_injective _ W.subtype_injective).1 h)
  obtain ⟨u, huP0, hu2⟩ := exists_involution_mem hP0p hP0ne
  obtain ⟨u', ⟨huH, huZ⟩, rfl⟩ := huP0
  have huQ : (u' : G) ∈ Q := huH
  have hucomm : ∀ w ∈ W, (u' : G) * w = w * (u' : G) := by
    intro w hw
    have := Subgroup.mem_center_iff.1 huZ ⟨w, hw⟩
    exact (congrArg Subtype.val this).symm
  have hTsyl := hc5 (u' : G) huQ (fun t ht => (hucomm t (hTW ht))) (by simpa using hu2)
  have hWC' : W ≤ centralizer ({(u' : G)} : Set G) := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.2 (hucomm w hw).symm
  have hWT : W = T := hTsyl.eq_of_le hTW hWC' hWp
  rw [← hWT]
  exact hWsyl

theorem not_odd_card_of_simple [Finite G] (hs : IsSimpleGroup G) (hn : ∃ a b : G, a * b ≠ b * a) :
    ¬ Odd (Nat.card G) := by
  intro hodd
  have hsolv : Group.IsSolvable G := CFSG.Milestones.odd_order_solvable hodd
  obtain ⟨a, b, hab⟩ := hn
  exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr hsolv a b)

theorem normalizer_ne_top_of_simple (hs : IsSimpleGroup G) {H : Subgroup G} (h1 : H ≠ ⊥)
    (h2 : H ≠ ⊤) : normalizer (H : Set G) ≠ ⊤ := by
  intro htop
  have hN : H.Normal := Subgroup.normalizer_eq_top_iff.1 htop
  rcases hs.eq_bot_or_eq_top_of_normal H with h | h
  · exact h1 h
  · exact h2 h

theorem centralizer_ne_top_of_simple (hs : IsSimpleGroup G) (hn : ∃ a b : G, a * b ≠ b * a) {x : G}
    (hx : x ≠ 1) : centralizer ({x} : Set G) ≠ ⊤ := by
  intro htop
  have hz : x ∈ center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have : g ∈ centralizer ({x} : Set G) := by rw [htop]; trivial
    exact mem_centralizer_singleton_iff.1 this
  rcases hs.eq_bot_or_eq_top_of_normal (center G) with h | h
  · rw [h, Subgroup.mem_bot] at hz
    exact hx hz
  · obtain ⟨a, b, hab⟩ := hn
    have : a ∈ center G := by rw [h]; trivial
    exact hab (Subgroup.mem_center_iff.1 this b).symm

open CFSG.GH74.GLS.C3.Layer1 in
theorem hyp9_of_choice [Finite G] (hG : C3Hyp G) {x y : G} {K T S M : Subgroup G}
    (h82 : B_thm2_l82) (h83 : B_thm2_l83) (h84 : B_thm2_l84) (h85 : B_thm2_p85)
    (h812 : B_thm2_p812) (hPU3 : B_thm2_PU3) (hc5 : B_thm2_cent5) (hI_M : B_thm2_caseI_M)
    (hts : B_thm2_tstar) (hchoice : Th2Choice x y K T S M) :
    ∃ L : Subgroup G, Hyp9A x K L M T (T ⊓ CxK x K) ∧ Hyp9B1 x K T (T ⊓ CxK x K) := by
  have hstd := hchoice.std
  have hx2 : orderOf x = 2 := hstd.v2ss.isV2Triple.1.1.1
  have hKC : K ≤ centralizer ({x} : Set G) := hstd.v2ss.isV2Triple.1.1.2.1
  have hxT : x ∈ T := Back.mem_of_isSylowOf_of_central hstd.setup.sylowT
    (mem_centralizer_singleton_iff.2 rfl) (fun _ hs => mem_centralizer_singleton_iff.1 hs) hx2
  have hxC : x ∈ CxK x K := by
    refine ⟨mem_centralizer_singleton_iff.2 rfl, Back.mem_centralizerSection_of_centralizes ?_ ?_⟩
    · intro k hk
      exact (mem_centralizer_singleton_iff.1 (hKC hk)).symm
    · unfold pPrimeCoreOf
      intro y hy
      obtain ⟨y', -, rfl⟩ := hy
      exact y'.2
  have hxQ : x ∈ T ⊓ CxK x K := ⟨hxT, hxC⟩
  have hKM : K ≤ M := by
    rcases hchoice with h1 | ⟨ρ, B, h2⟩
    · exact Subgroup.le_normalizer.trans h1.le_M
    · exact h83 G hG x y K T S M ρ B h2
  obtain ⟨hQ84, -⟩ := h84 G hG x y K T S M hchoice hKM
  obtain ⟨L, hL⟩ := exists_minSubnormal hKM
  obtain ⟨hLcomp, hLeq⟩ := h85 G hG x y K T S M hchoice hKM hQ84 L hL
  obtain ⟨hgam, hrk⟩ := h812 G hG x y K T S M hchoice hKM hQ84 L hL hLcomp hLeq
  have hLnorm := hPU3 G hG x y K T S M hchoice hKM hQ84 L hL hLcomp hLeq hgam hrk
  have hLM : L ≤ M := hLcomp.1
  have hcmk : CMbar M K = CMK M L := cmbar_eq_cmk hLM hLnorm hL.2.1 hLeq
  have hQC : IsSylowOf 2 (T ⊓ CxK x K) (CMK M L) := hcmk ▸ hQ84
  have hc5' := hc5 G hG x y K T S hstd
  have hTM : T ≤ M :=
    (hstd.setup.sylowT.le.trans (U1a.centralizer_le_gammaK hxQ hx2)).trans hgam
  have hsyl : IsSylowOf 2 T M :=
    sylow_TM hLnorm hTM hstd.setup.sylowT.isPGroup inf_le_left hxQ hx2 hQC hc5'
  refine ⟨L, ?_, ?_⟩
  · exact
    { twoTerminal := hstd.v2ss.isV2Triple.2.1
      maximal := hchoice.maximal
      K_le_L := hL.1
      L_normal := ⟨hLM, hLnorm⟩
      L_comp := hLcomp
      bar_eq := sup_pPrimeCoreOf_eq hL.2.1 hLeq
      sylowT := hstd.setup.sylowT
      hQ := rfl
      sylowQ := hQC
      rankQ := hrk
      gamma := hgam
      sylowTM := hsyl
      cent5 := hc5'
      terminal_eq := fun hterm => by
        rcases hchoice with h1 | ⟨ρ, B, h2⟩
        · have hMeq := hI_M G hG x y K T S M h1
          exact eq_of_isMinSubnormalIn_of_normal hKM hMeq.le hL
        · exact absurd hterm h2.nonterminal }
  · refine ⟨⟨y, hstd.v2ss.isV2StarTriple⟩, fun hnt hQ4 hK => ?_⟩
    rcases hchoice with h1 | ⟨ρ, B, h2⟩
    · exact absurd h1.terminal hnt
    · by_contra hnS
      have hTS : T < S := lt_of_le_of_ne hstd.T_le_S fun h => hnS (h ▸ hstd.sylowS)
      obtain ⟨a, haS, haN, haT⟩ := exists_mem_normalizer_of_lt hstd.sylowS.isPGroup hTS
      obtain ⟨hrk', hnorm⟩ := hts G hG x y K T S M ρ B h2 hQ4 hK hTS
      have hb := (h82 G hG x y K T S M ρ B h2).2.1
      have hN : normalizer ((ρ.Tstar x K T S : Subgroup G) : Set G) ≤
          gammaK 2 (ρ.Tstar x K T S) ρ.level.n := by
        unfold gammaK
        exact le_iSup₂_of_le (ρ.Tstar x K T S) le_rfl (le_iSup_of_le hrk' le_rfl)
      have haM : a ∈ M := hb (hN (hnorm a haS haN))
      have hP : IsPGroup 2 ↥(T ⊔ zpowers a) :=
        hstd.sylowS.isPGroup.to_le (sup_le hstd.T_le_S (zpowers_le.2 haS))
      have heq : T ⊔ zpowers a = T :=
        hsyl.eq_of_le le_sup_left (sup_le hTM (zpowers_le.2 haM)) hP
      exact haT (heq ▸ (Subgroup.mem_sup_right (mem_zpowers a)))

end CFSG.GH74.GLS.Th2

namespace CFSG.GH74.GLS

open Subgroup CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {x y : G} {K T S : Subgroup G}

theorem b_ig_21_6_of_half (h : B_IG_21_6_half) :
    ∀ (G : Type) [Group G] [Finite G] (ℓ : Th2Level) (B : Subgroup G),
      IsE ℓ.minRank ⊤ B → ℓ.IsBal B → Odd (Nat.card ↥(ℓ.theta B)) := by
  intro G _ _ ℓ B hE hbal
  cases ℓ with
  | one => exact b_ig_21_6_int G 1 le_rfl B hE hbal
  | three => exact b_ig_21_6_int G 3 (by norm_num) B hE hbal
  | fiveHalves => exact h G B hE hbal.1 hbal.2

theorem exists_th2M2_of_positiveTheta
    {B : Subgroup G} {ρ : Th2Row}
    (hs : IsSimpleGroup G) (hn : ∃ a b : G, a * b ≠ b * a)
    (hstd : Th2Std x y K T S) (hnt : ¬ IsTerminalPair 2 x K)
    (hρ : ρ.holds x y K T S) (hB : B ∈ ρ.BT x K T S)
    (hallE : ∀ B' ∈ ρ.BT x K T S, IsE ρ.level.minRank T B')
    (hallBal : ∀ B' ∈ ρ.BT x K T S, ρ.level.IsBal B')
    (hθ : ρ.level.theta B ≠ ⊥)
    (hrank : pRank 2 ↥(B ⊓ (T ⊓ K)) = pRank 2 ↥(T ⊓ K)) :
    ∃ M : Subgroup G, Th2M2 x y K T S M ρ B := by
  have hE : IsE ρ.level.minRank T B := hallE B hB
  have hbal : ρ.level.IsBal B := hallBal B hB
  have hodd : Odd (Nat.card ↥(ρ.level.theta B)) :=
    b_ig_21_6_of_half b_ig_21_6_half G ρ.level B ⟨le_top, hE.2.1, hE.2.2⟩ hbal
  have hθtop : ρ.level.theta B ≠ ⊤ := by
    intro htop
    apply Th2.not_odd_card_of_simple hs hn
    have hcard : Nat.card ↥(ρ.level.theta B) = Nat.card G := by
      rw [htop, Subgroup.card_top]
    rwa [hcard] at hodd
  obtain ⟨M, hM, hNM⟩ :=
    Th2.exists_coatom_ge (Th2.normalizer_ne_top_of_simple hs hθ hθtop)
  exact ⟨M, hstd, hnt, hρ, hB, hallE, hallBal, hθ, hrank, hM, hNM⟩

theorem s_thm2_rank4_of_leaves (h628 : B_thm2_v2ss) (h73 : B_thm2_p73) (h72c : B_thm2_p72c)
    (hI : B_thm2_caseI) (hI_M : B_thm2_caseI_M) (h82 : B_thm2_l82)
    (h83 : B_thm2_l83) (h84 : B_thm2_l84) (h85 : B_thm2_p85) (h812 : B_thm2_p812)
    (hPU3 : B_thm2_PU3) (hc5 : B_thm2_cent5) (hts : B_thm2_tstar) : S_thm2_rank4 := by
  intro G _ _ hG hV
  obtain ⟨x, y, K, hss⟩ := h628 G hG hV
  obtain ⟨T, S, hstd⟩ := Th2.exists_th2Std hss
  have hsimple : IsSimpleGroup G := hG.kproper.1
  have hnab : ∃ a b : G, a * b ≠ b * a := hG.kproper.2.1
  by_cases hterm : IsTerminalPair 2 x K
  · have hstand := hI G hG x y K T S hstd hterm
    have hK1 : K ≠ ⊥ := by
      intro h
      have := hterm.2.2.1
      rw [h, Subgroup.card_bot] at this
      exact absurd (Nat.le_of_dvd one_pos this) (by norm_num)
    have hx1 : x ≠ 1 := by
      intro h
      have := hstd.v2ss.isV2Triple.1.1.1
      rw [h, orderOf_one] at this
      exact absurd this (by norm_num)
    have hK2 : K ≠ ⊤ := by
      intro h
      apply Th2.centralizer_ne_top_of_simple hsimple hnab hx1
      exact eq_top_iff.2 (h ▸ hstd.v2ss.isV2Triple.1.1.2.1)
    obtain ⟨M, hM, hNM⟩ := Th2.exists_coatom_ge (Th2.normalizer_ne_top_of_simple hsimple hK1 hK2)
    obtain ⟨L, hA, hB⟩ := Th2.hyp9_of_choice hG h82 h83 h84 h85 h812 hPU3 hc5 hI_M hts
      (Or.inl ⟨hstd, hterm, hstand.1, hstand.2, hM, hNM⟩)
    exact ⟨x, K, L, M, T, T ⊓ CxK x K, hA, hB⟩
  · obtain ⟨ρ, hρ, -, hbal⟩ := h73 G hG x y K T S hstd
    obtain ⟨B, hB, hθ, hrank⟩ := h72c G hG x y K T S hstd hterm ρ hρ (fun B hB => (hbal B hB).2)
    obtain ⟨M, hM⟩ := exists_th2M2_of_positiveTheta hsimple hnab hstd hterm hρ hB
      (fun B' hB' => (hbal B' hB').1) (fun B' hB' => (hbal B' hB').2) hθ hrank
    obtain ⟨L, hA, hB'⟩ := Th2.hyp9_of_choice hG h82 h83 h84 h85 h812 hPU3 hc5 hI_M hts
      (Or.inr ⟨ρ, B, hM⟩)
    exact ⟨x, K, L, M, T, T ⊓ CxK x K, hA, hB'⟩

end CFSG.GH74.GLS
