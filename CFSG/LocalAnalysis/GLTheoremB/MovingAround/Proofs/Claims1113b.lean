module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Input1919

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1113b

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf barAut innerAut)

@[expose] def NotBalancedL34A5 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsQuasisimple X → GLAPPrimeCore 3 X = ⊥ →
    (IsLThreeFour (X ⧸ Subgroup.center X) ∨ IsAltType 5 (X ⧸ Subgroup.center X)) →
    ¬ IsLocallyOTwoBalancedWrtP 3 1 X

theorem notBalancedL34A5_holds :
    NotBalancedL34A5 := by
  intro X _ _ hq hO h
  rcases h with hL | hA
  · exact Input1919.not_balanced_L34_core hq hO hL
  · exact Input1919.not_balanced_alt_core hq Nat.prime_three (by norm_num) hO
      ⟨5, le_rfl, hA, Or.inl (by norm_num)⟩

section InnerTypec

variable {G : Type} [Group G] [Finite G]

theorem inner_typec_core (hI23 : Input23_20_W) (h112 : Prop112Statement) (h111 : Prop111Statement)
    (h115 : Prop115Statement) (hNB : NotBalancedL34A5) (hnot : Input_not_LTwoTwentySeven)
    {m : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G}
    (hSec : Sec11 G m 3 B M E A) (ha : a ∈ A) (ha1 : a ≠ 1)
    (hnotD : ¬ ∃ A1 : Subgroup G, inD 3 M A1 ∧ a ∈ A1)
    (hK : GLAPComponent 3 (Cg a) K) (hKM : ¬ K ≤ M)
    (hL34 : IsLThreeFour (barOf 3 K ⧸ Subgroup.center (barOf 3 K)))
    (hA0el : IsElemAbelian 3 (E ⊓ A)) (hA0C : E ⊓ A ≤ Cg a)
    (hA0N : E ⊓ A ≤ Subgroup.normalizer (K : Set G))
    (hrank : CFSG.Open.pRank 3 (E ⊓ A) = 2) :
    ∀ x ∈ E ⊓ A, InducesInner 3 K x := by
  by_contra hcon
  have hK1 : K ≤ Cg a := hK.1
  have hsnKC : IsSubnormal K (Cg a) := hK.2.1
  obtain ⟨hW, hmom⟩ := hI23 G (Cg a) K (E ⊓ A) hK hL34 hA0C hA0el hrank hA0N hcon
  apply hKM
  refine le_trans hW (sup_le (iSup₂_le fun x hx => ?_) ?_)
  ·
    obtain ⟨hxA, hx1⟩ := hx
    have hxC : x ∈ Cg a := hA0C hxA
    have hcg2 : Subgroup.centralizer ({x, a} : Set G) = Cg a ⊓ Subgroup.centralizer ({x} : Set G) :=
      l119_cg2_eq a x
    refine sup_le ?_ ?_
    ·
      have hsub : IsSubnormal (K ⊓ Subgroup.centralizer ({x} : Set G)) (Cg a ⊓ Subgroup.centralizer ({x} : Set G)) :=
        isSubnormal_inf hsnKC _
      have hcore : GLAPPrimeCoreOf 3 (K ⊓ Subgroup.centralizer ({x} : Set G)) ≤
          GLAPPrimeCoreOf 3 (Cg a ⊓ Subgroup.centralizer ({x} : Set G)) :=
        glaPPrimeCoreOf_le_of_isSubnormal (by norm_num) hsub
      have hM2 : GLAPPrimeCoreOf 3 (Cg2 x a) ≤ M := by
        rcases h112 hSec ha ha1 hxA hx1 with h | h
        · exact h
        · exact absurd h hnotD
      rw [Cg2, hcg2] at hM2
      exact hcore.trans hM2
    ·
      unfold GLAPLayer
      refine sSup_le fun Q hQ => ?_
      have hsubQ : IsSubnormal (K ⊓ Subgroup.centralizer ({x} : Set G)) (Cg a ⊓ Subgroup.centralizer ({x} : Set G)) :=
        isSubnormal_inf hsnKC _
      have hQ' : GLAPComponent 3 (Cg a ⊓ Subgroup.centralizer ({x} : Set G)) Q :=
        l119_glaPComponent_of_isSubnormal (by norm_num) hsubQ hQ
      have hJ : GLAPComponent 3 (Cg2 x a) Q := by
        rw [Cg2, hcg2]
        exact hQ'
      have hq := hmom x hxA hx1 Q hQ
      have hquasi := l119_isQuasisimple_barOf (p := 3) (by norm_num) hQ
      have h1 : ¬ IsLocallyOTwoBalancedWrtP 3 1 (barOf 3 Q) :=
        hNB _ hquasi (glaPPrimeCore_quotient_eq_bot Nat.prime_three) hq
      have h2 : 3 = 3 → IsLTwoTwentySeven (barOf 3 Q) → ¬ IsCompLocallyOTwoBalanced 3 1 A Q := by
        intro _ hL27 _
        exact hnot (barOf 3 Q) hL27 (by
          rcases hq with hq | hq
          · exact Or.inl hq
          · exact Or.inr hq)
      rcases h115 hSec ha ha1 hxA hx1 hJ h1 h2 with hQM | ⟨A1, hA1, haA1⟩
      · exact hQM
      · exact absurd ⟨A1, hA1, haA1⟩ hnotD
  · exact (glaPPrimeCoreOf_le_of_isSubnormal (by norm_num) hsnKC).trans (h111 hSec ha ha1)

end InnerTypec

section Chev

variable {G : Type} [Group G] [Finite G]

theorem inducesInner_of_plane_core (h1111 : Lemma1111Statement) (h1112 : Lemma1112Statement)
    (h119 : Lemma119Statement) (h104v : Lemma104_vStatement) (h111 : Prop111Statement)
    (h112 : Prop112Statement) (h115 : Prop115Statement) (hNB : NotBalancedL34A5)
    (hI2320 : Input23_20_W)
    {m : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G} (h : Cex117 G m 3 B M E A a K)
    (haM : a ∈ M)
    (hrk4 : CFSG.Open.pRank 3 (⊤ : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M)) ≤ 4)
    (hnotL : QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) (⟨a, haM⟩ : ↥M) ∉
      GLAPLayer 3 (⊤ : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M)))
    (hExp : ∀ D' : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M),
      D' ≤ GLAPLayer 3 (⊤ : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M)) ⊓ Subgroup.centralizer
        ({QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) (⟨a, haM⟩ : ↥M)} : Set (↥M ⧸ GLAPPrimeCore 3 ↥M)) →
      IsElemAbelian 3 D' → Nat.card D' = 9 →
      ∃ E' : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M), D' ≤ E' ∧
        E' ≤ GLAPLayer 3 (⊤ : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M)) ∧ IsElemAbelian 3 E' ∧
        Nat.card E' = 81 ∧
        IsPGroup 3 ↥(E' ⊔ Subgroup.zpowers (QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) (⟨a, haM⟩ : ↥M))))
    {D : Subgroup ↥M}
    (hDL : D ≤ (GLAPLayer 3 (⊤ : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M))).comap
      (QuotientGroup.mk' (GLAPPrimeCore 3 ↥M)))
    (hDC : D ≤ Subgroup.centralizer ({(⟨a, haM⟩ : ↥M)} : Set ↥M))
    (hDel : IsElemAbelian 3 D) (hD9 : Nat.card D = 9) :
    ∀ x ∈ D, InducesInner 3 K (x : G) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) with hπ
  set Lq := GLAPLayer 3 (⊤ : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M)) with hLq
  set a' : ↥M := ⟨a, haM⟩ with ha'
  have hN : Nat.Coprime 3 (Nat.card (GLAPPrimeCore 3 ↥M)) := CFSG.pPrimeCore_coprime_card
  have hAel : IsElemAbelian 3 A := h.pair.1.2.1.1.1.2.1
  have ha : a ∈ A := h.ha.1
  have ha1 : a ≠ 1 := h.ha.2
  have ha3 : a ^ 3 = 1 := hAel.2 a ha
  have ha3' : a' ^ 3 = 1 := Subtype.ext (by simpa using ha3)
  have ha'1 : a' ≠ 1 := fun h1 => ha1 (congrArg Subtype.val h1)
  have hA3 : CFSG.Open.pRank 3 A = 3 := (h1111 h).2.1
  have hCa : CFSG.Open.pRank 3 (Cg a) = 3 := ((h1112 h).1).2
  have hinj3 : ∀ {T : Subgroup ↥M}, IsPGroup 3 ↥T → ∀ x ∈ T, ∀ y ∈ T, π x = π y → x = y := by
    intro T hT x hx y hy hxy
    have hmem : x⁻¹ * y ∈ GLAPPrimeCore 3 ↥M := (QuotientGroup.eq).1 hxy
    have h1 := Claims11x.eq_one_of_mem_coprime hN hT hmem (T.mul_mem (T.inv_mem hx) hy)
    rw [inv_mul_eq_one] at h1
    exact h1
  have hD3 : IsPGroup 3 ↥D := Lemma118T.isPGroup_of_isElemAbelian hDel
  have ha'D : a' ∉ D := fun h1 => hnotL (hDL h1)
  have hD'L : D.map π ≤ Lq ⊓ Subgroup.centralizer ({π a'} : Set (↥M ⧸ GLAPPrimeCore 3 ↥M)) := by
    rintro _ ⟨x, hx, rfl⟩
    have hxa : x * a' = a' * x := Subgroup.mem_centralizer_singleton_iff.1 (hDC hx)
    have hc : π x * π a' = π a' * π x := by rw [← map_mul, ← map_mul, hxa]
    exact Subgroup.mem_inf.2 ⟨hDL hx, Subgroup.mem_centralizer_singleton_iff.2 hc⟩
  have hD'el : IsElemAbelian 3 (D.map π) := CFSG.SectionRank.isElemAbelian_map hDel π
  have hD'9 : Nat.card (D.map π) = 9 := by
    rw [← hD9]
    exact ((Claims11x.isElemAbelian_of_injOn π (hinj3 hD3) hD'el).2).symm
  obtain ⟨E', hDE', hE'L, hE'el, hE'card, hE'p⟩ := hExp _ hD'L hD'el hD'9
  set S : Subgroup ↥M := D ⊔ Subgroup.zpowers a' with hS
  have hDa : D ≤ Subgroup.centralizer (Subgroup.zpowers a' : Set ↥M) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact (Commute.zpow_left (Subgroup.mem_centralizer_singleton_iff.1 (hDC hx)).symm k).eq
  have hSel : IsElemAbelian 3 S :=
    isElemAbelian_sup_of_commute hDel (CFSG.Open.isElemAbelian_zpowers ha3') hDa
  have hS3 : IsPGroup 3 ↥S := Lemma118T.isPGroup_of_isElemAbelian hSel
  have hSmap : S.map π ≤ E' ⊔ Subgroup.zpowers (π a') := by
    rw [hS, Subgroup.map_sup, MonoidHom.map_zpowers]
    exact sup_le_sup_right hDE' _
  have hTH : E' ⊔ Subgroup.zpowers (π a') ≤ (⊤ : Subgroup ↥M).map π := by
    rw [Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective _)]
    exact le_top
  obtain ⟨T, hST, -, hT3, hTm, hinjT⟩ :=
    Claims11x.exists_lift_of_coprime (GLAPPrimeCore 3 ↥M) hN hTH hE'p le_top hS3 hSmap
  set E0 : Subgroup ↥M := T ⊓ E'.comap π with hE0
  have hE0m : E0.map π = E' := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact hx.2
    · intro e he
      have : e ∈ T.map π := by rw [hTm]; exact Subgroup.mem_sup_left he
      obtain ⟨t, ht, rfl⟩ := this
      exact ⟨t, ⟨ht, he⟩, rfl⟩
  have hinjE0 : ∀ x ∈ E0, ∀ y ∈ E0, π x = π y → x = y := fun x hx y hy => hinjT x hx.1 y hy.1
  have hE0el' : IsElemAbelian 3 (E0.map π) := by rw [hE0m]; exact hE'el
  obtain ⟨hE0el, hE0card⟩ := Claims11x.isElemAbelian_of_injOn π hinjE0 hE0el'
  rw [hE0m, hE'card] at hE0card
  have hDE0 : D ≤ E0 := fun x hx => ⟨hST (Subgroup.mem_sup_left hx), hDE' ⟨x, hx, rfl⟩⟩
  set Es : Subgroup G := E0.map M.subtype with hEs
  set As : Subgroup G := S.map M.subtype with hAs
  set D0 : Subgroup G := D.map M.subtype with hD0
  have hEsel : IsElemAbelian 3 Es := CFSG.SectionRank.isElemAbelian_map hE0el _
  have hAsel : IsElemAbelian 3 As := CFSG.SectionRank.isElemAbelian_map hSel _
  have hEscard : Nat.card Es = 3 ^ 4 := by
    rw [hEs, Subgroup.card_map_of_injective M.subtype_injective, hE0card]
    norm_num
  have hDS : D ⊓ Subgroup.zpowers a' = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨hwD, hwa⟩ := Subgroup.mem_inf.1 hw
    by_contra hw1
    have hw1' : w ≠ 1 := fun h1 => hw1 (by rw [h1]; exact Subgroup.one_mem _)
    have hw3 : w ^ 3 = 1 := hDel.2 w hwD
    have hza : Nat.card (Subgroup.zpowers a') = 3 := by
      rw [Nat.card_zpowers, orderOf_eq_prime ha3' ha'1]
    have hzw : Nat.card (Subgroup.zpowers w) = 3 := by
      rw [Nat.card_zpowers, orderOf_eq_prime hw3 hw1']
    have heq : Subgroup.zpowers w = Subgroup.zpowers a' :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hwa) (by rw [hza, hzw])
    have : a' ∈ Subgroup.zpowers w := by rw [heq]; exact Subgroup.mem_zpowers a'
    exact ha'D ((Subgroup.zpowers_le.2 hwD) this)
  have hScard : Nat.card S = 27 := by
    have hc : ∀ x ∈ D, ∀ y ∈ Subgroup.zpowers a', x * y = y * x := fun x hx y hy =>
      (Subgroup.mem_centralizer_iff.1 (hDa hx) y hy).symm
    rw [hS, CFSG.HardMathSupport.Solomon.LocalBalance.card_sup_eq_mul_of_commute hc hDS, hD9,
      Nat.card_zpowers, orderOf_eq_prime ha3' ha'1]
  have hAscard : Nat.card As = 3 ^ 3 := by
    rw [hAs, Subgroup.card_map_of_injective M.subtype_injective, hScard]
    norm_num
  have hEsr : CFSG.Open.pRank 3 Es = 4 := Lemma118T.pRank_eq_of_isElemAbelian_card hEsel hEscard
  have hAsr : CFSG.Open.pRank 3 As = 3 := Lemma118T.pRank_eq_of_isElemAbelian_card hAsel hAscard
  have haAs : a ∈ As := ⟨a', Subgroup.mem_sup_right (Subgroup.mem_zpowers a'), rfl⟩
  have hEsM : Es ≤ M := Subgroup.map_subtype_le E0
  have hAsM : As ≤ M := Subgroup.map_subtype_le S
  have hD0Es : D0 ≤ Es := Subgroup.map_mono hDE0
  have hD0As : D0 ≤ As := Subgroup.map_mono le_sup_left
  have haEs : a ∉ Es := by
    rintro ⟨x, hx, hxa⟩
    have : x = a' := Subtype.ext hxa
    rw [this] at hx
    exact hnotL (hE'L hx.2)
  have hD0card : Nat.card D0 = 9 := by
    rw [hD0, Subgroup.card_map_of_injective M.subtype_injective, hD9]
  have hIcard : Nat.card ↥(Es ⊓ As) = 3 ^ 2 := by
    have hdvd : Nat.card ↥(Es ⊓ As) ∣ 3 ^ 3 := by
      rw [← hAscard]
      exact Subgroup.card_dvd_of_le inf_le_right
    obtain ⟨j, hj3, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    have hge : 9 ≤ Nat.card ↥(Es ⊓ As) := by
      rw [← hD0card]
      exact Subgroup.card_le_of_le (le_inf hD0Es hD0As)
    have hne : j ≠ 3 := by
      rintro rfl
      have heq : Es ⊓ As = As := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hj, hAscard])
      have hmem : a ∈ Es ⊓ As := by rw [heq]; exact haAs
      exact haEs (Subgroup.mem_inf.1 hmem).1
    rw [hj] at hge ⊢
    have : j = 2 := by
      rcases Nat.lt_or_ge j 2 with hlt | hge2
      · interval_cases j <;> norm_num at hge
      · omega
    rw [this]
  have hIel : IsElemAbelian 3 (Es ⊓ As) := isElemAbelian_mono hEsel inf_le_left
  have hIr : CFSG.Open.pRank 3 (Es ⊓ As) = 2 := Lemma118T.pRank_eq_of_isElemAbelian_card hIel hIcard
  have hEAp : IsPGroup 3 ↥(Es ⊔ As) := by
    have hle : Es ⊔ As ≤ T.map M.subtype :=
      sup_le (Subgroup.map_mono inf_le_left) (Subgroup.map_mono hST)
    exact (hT3.map M.subtype).to_le hle
  have hrkM : ∀ F : Subgroup G, F ≤ M → IsElemAbelian 3 F → CFSG.Open.pRank 3 F ≤ 4 :=
    fun F hFM hF => (Claims11x.pRank_le_tilde hFM hF).trans hrk4
  obtain ⟨R, hR, hEsR⟩ := Lemma1112b.exists_isSylowIn_ge hEsM (Lemma118T.isPGroup_of_isElemAbelian hEsel)
  have hD0' := (h104v h.toCex117Base.toSec11.toSec10Fails h.pair (Or.inr hA3) hR).1 Es
    ⟨hEsR, hEsel, hEscard⟩
  obtain ⟨-, -, A1, hA1, hEsA1⟩ := hD0'
  have hA1el : IsElemAbelian 3 A1 := hA1.1.1.2.1
  have hA1M : A1 ≤ M := hA1.1.1.1
  have hA1eq : A1 = Es := by
    refine (Subgroup.eq_of_le_of_card_ge hEsA1 ?_).symm
    rw [hEscard, l1110_card_eq_pow_pRank hA1el]
    exact Nat.pow_le_pow_right (by norm_num) (hrkM A1 hA1M hA1el)
  have hEsD : inD 3 M Es := hA1eq ▸ hA1
  have hAsSC : IsSCp 3 M As := by
    refine ⟨hAsM, hAsel, fun F hFM hFel hAsF => ?_⟩
    have haF : a ∈ F := hAsF haAs
    have hFC : F ≤ Cg a := fun x hx => Subgroup.mem_centralizer_singleton_iff.2
      (congrArg Subtype.val (hFel.1.is_comm.comm ⟨x, hx⟩ ⟨a, haF⟩))
    have hFr : CFSG.Open.pRank 3 F ≤ 3 :=
      (CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) hFC).trans hCa.le
    refine (Subgroup.eq_of_le_of_card_ge hAsF ?_).symm
    rw [hAscard, l1110_card_eq_pow_pRank hFel]
    exact Nat.pow_le_pow_right (by norm_num) hFr
  have hAsDp : inDp 3 M As := ⟨⟨hAsSC, by rw [hAsr]⟩, fun hU => h.notD ⟨As, ⟨⟨hAsSC, by rw [hAsr]⟩, hU⟩, haAs⟩⟩
  have hEr : CFSG.Open.pRank 3 E ≤ 4 := hrkM E h.pair.1.1.1.1.1 h.pair.1.1.1.1.2.1
  have hEAr : CFSG.Open.pRank 3 (E ⊓ A) = 2 := (h119 h).1
  have hkey : ddKey 3 E A ≤ ddKey 3 Es As := by
    refine Claims11x.ddKey_le_of (by rw [hEAr, hIr]) ?_ (by rw [hEsr]; exact hEr) (by rw [hA3, hAsr]) hEAp
    rw [hA3, hEsr, hAsr]
    exact min_le_right _ _
  have hpair : IsDDpStar 3 M Es As :=
    ⟨⟨hEsD, hAsDp, by rw [hIr]⟩, fun E'' A'' h'' => (h.pair.2 E'' A'' h'').trans hkey⟩
  have hSec' : Sec11 G m 3 B M Es As := ⟨h.toCex117Base.toSec11.toSec10Fails, hpair⟩
  have hL34 : IsLThreeFour (barOf 3 K ⧸ Subgroup.center (barOf 3 K)) := by
    have hL := (h1111 h).2.2
    exact l119_isLThreeFour_congr (l119_center_bot_quot (Lemma1112.center_eq_bot_of_isLThreeFour hL)).symm hL
  have hcfg := Inputs1114.cfg_of h1111 h119 h1112 h
  have hAsC : As ≤ Cg a := fun x hx => Subgroup.mem_centralizer_singleton_iff.2
    (congrArg Subtype.val (hAsel.1.is_comm.comm ⟨x, hx⟩ ⟨a, haAs⟩))
  have hinner := inner_typec_core hI2320 h112 h111 h115 hNB Input_not_LTwoTwentySeven_holds hSec'
    haAs ha1 h.notD h.hK h.notM hL34 hIel (inf_le_right.trans hAsC)
    ((inf_le_right.trans hAsC).trans hcfg.cg_le_normalizer) hIr
  intro x hx
  exact hinner (x : G) ⟨hD0Es ⟨x, hx, rfl⟩, hD0As ⟨x, hx, rfl⟩⟩

theorem nonsolvChevClaim_core (hQ : Lemma1113b.NonsolvQuasisimpleClaim)
    (h1111 : Lemma1111Statement) (h1112 : Lemma1112Statement) (h119 : Lemma119Statement)
    (h104v : Lemma104_vStatement) (h111 : Prop111Statement) (h112 : Prop112Statement)
    (h115 : Prop115Statement) (hNB : NotBalancedL34A5) (hI2320 : Input23_20_W) (hI29 : Claims11x.Input29_5)
    (hSolv : Claims11x.Lemma1113SolvClaim) (hC4 : Claims11x.Lemma1113C4Claim) : Lemma1113b.NonsolvChevClaim := by
  intro G _ _ m p B M E A a K h hp e he heEA he1 hL
  subst hp
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) with hπ
  set Lq := GLAPLayer 3 (⊤ : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M)) with hLq
  have hAM : A ≤ M := h.pair.1.2.1.1.1.1
  have hAel : IsElemAbelian 3 A := h.pair.1.2.1.1.1.2.1
  have ha : a ∈ A := h.ha.1
  have haM : a ∈ M := hAM ha
  set a' : ↥M := ⟨a, haM⟩ with ha'
  have ha3 : a ^ 3 = 1 := hAel.2 a ha
  have ha3' : a' ^ 3 = 1 := Subtype.ext (by simpa using ha3)
  have ha'1 : a' ≠ 1 := fun h1 => h.ha.2 (congrArg Subtype.val h1)
  have hN : Nat.Coprime 3 (Nat.card (GLAPPrimeCore 3 ↥M)) := CFSG.pPrimeCore_coprime_card
  have hO : GLAPPrimeCore 3 (↥M ⧸ GLAPPrimeCore 3 ↥M) = ⊥ :=
    CFSG.GH74.pPrimeCore_quotient_pPrimeCore_eq_bot ↥M 3
  have hLn : Lq.Normal := Lemma1113b.layer_top_normal hO
  obtain ⟨hqs, -, hfaith⟩ := hQ G m 3 B M E A a K h rfl e he heEA he1 hL
  have hMne : M ≠ ⊤ := isTwoLocal_ne_top h.standing h.pre.1.1
  have hKM : CFSG.Open.IsKGroup ↥M := isKGroup_of_isKProper h.standing.kProper hMne
  have hKL : CFSG.Open.IsKGroup ↥Lq := (hKM.quotient (GLAPPrimeCore 3 ↥M)).subgroup Lq
  have hã1 : π a' ≠ 1 := by
    intro h1
    exact ha'1 (l119_eq_one_of_pow_of_mem_core Nat.prime_three ha3' ((QuotientGroup.eq_one_iff _).1 h1))
  have hord : orderOf (π a') = 3 := orderOf_eq_prime (by rw [← map_pow, ha3', map_one]) hã1
  obtain ⟨hC4', hrk3, hsolv⟩ := Claims11x.tilde_centralizer_facts h1111 h1112 hSolv hC4 h haM
  by_contra hchev
  obtain ⟨hnotL, hrk4, hSyl, hExp⟩ := hI29 _ Lq hLn hqs hKL hfaith hchev (Claims11x.four_le_pRank_tilde h)
    (π a') hord hC4' hrk3 hsolv
  obtain ⟨Q', hQ', -⟩ := Lemma1112b.exists_isSylowIn_ge
    (bot_le : ⊥ ≤ Lq ⊓ Subgroup.centralizer ({π a'} : Set (↥M ⧸ GLAPPrimeCore 3 ↥M))) IsPGroup.of_bot
  obtain ⟨hQexp, q₁, hq₁, q₂, hq₂, hq12⟩ := hSyl Q' hQ'
  have hord' : ∃ k : ℕ, orderOf a' = 3 ^ k := by
    obtain h1 | h3 := (Nat.dvd_prime Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one ha3')
    · exact ⟨0, by rw [h1, pow_zero]⟩
    · exact ⟨1, by rw [h3, pow_one]⟩
  have hcent : Subgroup.centralizer ({π a'} : Set (↥M ⧸ GLAPPrimeCore 3 ↥M)) =
      (Subgroup.centralizer ({a'} : Set ↥M)).map π :=
    CFSG.GH74.centralizer_singleton_pPrimeCore_quotient_eq_map 3 hord'
  have hQH : Q' ≤ (Lq.comap π ⊓ Subgroup.centralizer ({a'} : Set ↥M)).map π := by
    intro y hy
    obtain ⟨hyL, hyC⟩ := Subgroup.mem_inf.1 (hQ'.1 hy)
    rw [hcent] at hyC
    obtain ⟨c, hc, rfl⟩ := hyC
    exact ⟨c, ⟨hyL, hc⟩, rfl⟩
  obtain ⟨Q, -, hQH', hQ3, hQm, hinjQ⟩ := Claims11x.exists_lift_of_coprime (GLAPPrimeCore 3 ↥M) hN hQH hQ'.2.1
    bot_le IsPGroup.of_bot (by rw [Subgroup.map_bot]; exact bot_le)
  have hQL : Q ≤ Lq.comap π := hQH'.trans inf_le_left
  have hQC : Q ≤ Subgroup.centralizer ({a'} : Set ↥M) := hQH'.trans inf_le_right
  have hQexp' : ∀ x ∈ Q, x ^ 3 = 1 := by
    intro x hx
    apply hinjQ _ (Q.pow_mem hx 3) _ Q.one_mem
    rw [map_pow, map_one]
    exact hQexp _ (by rw [← hQm]; exact ⟨x, hx, rfl⟩)
  have hnab : ∃ x ∈ Q, ∃ y ∈ Q, x * y ≠ y * x := by
    rw [← hQm] at hq₁ hq₂
    obtain ⟨x, hx, rfl⟩ := hq₁
    obtain ⟨y, hy, rfl⟩ := hq₂
    refine ⟨x, hx, y, hy, fun hxy => hq12 ?_⟩
    rw [← map_mul, ← map_mul, hxy]
  obtain ⟨x₀, hx₀, y₀, hy₀, hxy₀⟩ := hnab
  haveI : Nontrivial ↥Q := ⟨⟨⟨x₀, hx₀⟩, 1, fun h1 => hxy₀ (by
    have : x₀ = 1 := congrArg Subtype.val h1
    rw [this, one_mul, mul_one])⟩⟩
  haveI := hQ3.center_nontrivial
  obtain ⟨zc, hzc1⟩ := exists_ne (1 : ↥(Subgroup.center ↥Q))
  set z : ↥M := ((zc : ↥Q) : ↥M) with hz
  have hzQ : z ∈ Q := (zc : ↥Q).2
  have hz1 : z ≠ 1 := fun h1 => hzc1 (Subtype.ext (Subtype.ext h1))
  have hzc : ∀ y ∈ Q, y * z = z * y := fun y hy =>
    congrArg Subtype.val (Subgroup.mem_center_iff.1 zc.2 ⟨y, hy⟩)
  have hz3 : z ^ 3 = 1 := hQexp' z hzQ
  have hplane : ∀ x ∈ Q, ∃ D : Subgroup ↥M, D ≤ Q ∧ IsElemAbelian 3 D ∧ Nat.card D = 9 ∧ x ∈ D := by
    have hmk : ∀ w ∈ Q, w ∉ Subgroup.zpowers z →
        ∃ D : Subgroup ↥M, D ≤ Q ∧ IsElemAbelian 3 D ∧ Nat.card D = 9 ∧ w ∈ D ∧ z ∈ D := by
      intro w hw hwz
      obtain ⟨hel, hcard⟩ := Claims11x.plane_of_commute (hQexp' w hw) hz3 hz1 (hzc w hw) hwz
      exact ⟨_, sup_le (Subgroup.zpowers_le.2 hw) (Subgroup.zpowers_le.2 hzQ), hel, hcard,
        Subgroup.mem_sup_left (Subgroup.mem_zpowers w), Subgroup.mem_sup_right (Subgroup.mem_zpowers z)⟩
    intro x hx
    by_cases hxz : x ∈ Subgroup.zpowers z
    · have hex : ∃ w ∈ Q, w ∉ Subgroup.zpowers z := by
        by_contra hall
        push Not at hall
        apply hxy₀
        obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (hall x₀ hx₀)
        obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (hall y₀ hy₀)
        rw [← hi, ← hj]
        exact (Commute.zpow_zpow_self z i j).eq
      obtain ⟨w, hw, hwz⟩ := hex
      obtain ⟨D, hDQ, hDel, hD9, -, hzD⟩ := hmk w hw hwz
      exact ⟨D, hDQ, hDel, hD9, (Subgroup.zpowers_le.2 hzD) hxz⟩
    · obtain ⟨D, hDQ, hDel, hD9, hxD, -⟩ := hmk x hx hxz
      exact ⟨D, hDQ, hDel, hD9, hxD⟩
  have hinner : ∀ x ∈ Q, InducesInner 3 K (x : G) := by
    intro x hx
    obtain ⟨D, hDQ, hDel, hD9, hxD⟩ := hplane x hx
    exact inducesInner_of_plane_core h1111 h1112 h119 h104v h111 h112 h115 hNB hI2320 h haM hrk4 hnotL hExp
      (hDQ.trans hQL) (hDQ.trans hQC) hDel hD9 x hxD
  have hcfg := Inputs1114.cfg_of h1111 h119 h1112 h
  set Q0 : Subgroup G := Q.map M.subtype with hQ0
  have hQ0C : Q0 ≤ Cg a := by
    rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.2
      (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 (hQC hx)))
  have hQ0N : Q0 ≤ Subgroup.normalizer (K : Set G) := hQ0C.trans hcfg.cg_le_normalizer
  let ρ : ↥Q0 →* MulAut (barOf 3 K) := (barAut 3 K).comp (Subgroup.inclusion hQ0N)
  have hQ03 : IsPGroup 3 ↥Q0 := hQ3.map M.subtype
  have hρ3 : IsPGroup 3 ↥ρ.range := hQ03.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
  have hρinn : ρ.range ≤ innerAut (barOf 3 K) := by
    rintro _ ⟨⟨_, x, hx, rfl⟩, rfl⟩
    obtain ⟨k, hk, hkc⟩ := hinner x hx
    obtain ⟨⟨c, hcN⟩, hcker, hceq⟩ := Subgroup.mem_map.1 (Subgroup.mem_inf.1 hkc).1
    have hc1 : barAut 3 K ⟨c, hcN⟩ = 1 := MonoidHom.mem_ker.1 hcker
    have hkN : k ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer hk
    have hxeq : (Subgroup.inclusion hQ0N ⟨(x : G), x, hx, rfl⟩ : ↥(Subgroup.normalizer (K : Set G))) =
        ⟨k, hkN⟩ * ⟨c, hcN⟩ := by
      apply Subtype.ext
      change (x : G) = k * c
      have hc' : c = k⁻¹ * (x : G) := hceq
      rw [hc']
      group
    show barAut 3 K (Subgroup.inclusion hQ0N ⟨(x : G), x, hx, rfl⟩) ∈ innerAut (barOf 3 K)
    rw [hxeq, map_mul, hc1, mul_one, l119_barAut_eq_conj (p := 3) ⟨k, hk⟩]
    exact ⟨_, rfl⟩
  have hKbar : Nat.card (barOf 3 K) = 20160 :=
    CFSG.HardMathSupport.Solomon.UniquenessMaximal.card_eq_of_isLThreeFour (h1111 h).2.2
  have hρdvd : Nat.card ↥ρ.range ∣ 20160 := by
    rw [← hKbar, ← l1110_card_innerAut (Lemma1112.center_eq_bot_of_isLThreeFour (h1111 h).2.2)]
    exact Subgroup.card_dvd_of_le hρinn
  have hρcomm := Claims11x.comm_of_card_dvd hρ3 hρdvd
  set w : ↥M := x₀ * y₀ * x₀⁻¹ * y₀⁻¹ with hw
  have hwQ : w ∈ Q := Q.mul_mem (Q.mul_mem (Q.mul_mem hx₀ hy₀) (Q.inv_mem hx₀)) (Q.inv_mem hy₀)
  have hwQ0 : (w : G) ∈ Q0 := ⟨w, hwQ, rfl⟩
  have hw1 : w ≠ 1 := by
    intro h1
    apply hxy₀
    have : x₀ * y₀ * x₀⁻¹ * y₀⁻¹ = 1 := h1
    calc x₀ * y₀ = (x₀ * y₀ * x₀⁻¹ * y₀⁻¹) * (y₀ * x₀) := by group
      _ = y₀ * x₀ := by rw [this, one_mul]
  have hρw : ρ ⟨(w : G), hwQ0⟩ = 1 := by
    have hx0 : ((x₀ : G)) ∈ Q0 := ⟨x₀, hx₀, rfl⟩
    have hy0 : ((y₀ : G)) ∈ Q0 := ⟨y₀, hy₀, rfl⟩
    have he : (⟨(w : G), hwQ0⟩ : ↥Q0) = ⟨(x₀ : G), hx0⟩ * ⟨(y₀ : G), hy0⟩ * (⟨(x₀ : G), hx0⟩)⁻¹ *
        (⟨(y₀ : G), hy0⟩)⁻¹ := Subtype.ext (by simp [hw])
    have hc : ρ ⟨(x₀ : G), hx0⟩ * ρ ⟨(y₀ : G), hy0⟩ = ρ ⟨(y₀ : G), hy0⟩ * ρ ⟨(x₀ : G), hx0⟩ :=
      congrArg Subtype.val (hρcomm ⟨ρ ⟨(x₀ : G), hx0⟩, _, rfl⟩ ⟨ρ ⟨(y₀ : G), hy0⟩, _, rfl⟩)
    rw [he, map_mul, map_mul, map_mul, map_inv, map_inv, hc]
    group
  have hwC : (w : G) ∈ centBar 3 (Cg a) K := by
    unfold centBar
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_map.2 ⟨⟨(w : G), hQ0N hwQ0⟩, MonoidHom.mem_ker.2 hρw, rfl⟩,
      hQ0C hwQ0⟩
  have hsyl := ((h1112 h).1).1
  have hw3 : IsPGroup 3 ↥(Subgroup.zpowers (w : G)) := by
    rw [IsPGroup.iff_card, Nat.card_zpowers]
    have : (w : G) ^ 3 = 1 := by rw [← Subgroup.coe_pow, hQexp' w hwQ, Subgroup.coe_one]
    obtain h1 | h3 := (Nat.dvd_prime Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one this)
    · exact ⟨0, by rw [h1, pow_zero]⟩
    · exact ⟨1, by rw [h3, pow_one]⟩
  obtain ⟨c, hcC, hc⟩ := Claims11x.exists_conj_le_of_isSylowIn hsyl (Subgroup.zpowers_le.2 hwC) hw3
  have hca : c * a = a * c := by
    have : c ∈ Cg a := (Subgroup.mem_inf.1 hcC).2
    exact Subgroup.mem_centralizer_singleton_iff.1 this
  have hwa : (w : G) ∈ Subgroup.zpowers a := by
    have h1 := hc (w : G) (Subgroup.mem_zpowers _)
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 h1
    have hcomm : Commute c (a ^ i) := (show Commute c a from hca).zpow_right i
    have : (w : G) = a ^ i := by
      calc (w : G) = c * (c⁻¹ * (w : G) * c) * c⁻¹ := by group
        _ = c * a ^ i * c⁻¹ := by rw [hi]
        _ = a ^ i := by rw [hcomm.eq]; group
    rw [this]
    exact Subgroup.zpow_mem_zpowers a i
  have hw3' : (w : G) ^ 3 = 1 := by rw [← Subgroup.coe_pow, hQexp' w hwQ, Subgroup.coe_one]
  have hwG1 : (w : G) ≠ 1 := fun h1 => hw1 (Subtype.ext h1)
  have heqz : Subgroup.zpowers (w : G) = Subgroup.zpowers a := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hwa) ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hw3' hwG1, orderOf_eq_prime ha3 h.ha.2]
  have haQ0 : a ∈ Q0 := by
    have : a ∈ Subgroup.zpowers (w : G) := by rw [heqz]; exact Subgroup.mem_zpowers a
    exact (Subgroup.zpowers_le.2 hwQ0) this
  obtain ⟨q, hq, hqa⟩ := haQ0
  have hqa' : q = a' := Subtype.ext hqa
  rw [hqa'] at hq
  exact hnotL (hQL hq)

theorem nonsolvChevClaim_core' (hQ : Lemma1113b.NonsolvQuasisimpleClaim)
    (h1111 : Lemma1111Statement) (h1112 : Lemma1112Statement) (h119 : Lemma119Statement)
    (h104v : Lemma104_vStatement) (h111 : Prop111Statement) (h112 : Prop112Statement)
    (h115 : Prop115Statement) (hNB : NotBalancedL34A5) (hI2320 : Input23_20_W)
    (hI29 : Claims11x.Input29_5) (hN : Claims11x.InputL34SylowNormalizer)
    (hAut : Claims11x.InputAutL34Order27) : Lemma1113b.NonsolvChevClaim :=
  nonsolvChevClaim_core hQ h1111 h1112 h119 h104v h111 h112 h115 hNB hI2320 hI29
    (Claims11x.lemma1113SolvClaim_of_inputs h1111 h1112 h119 h111 hN)
    (Claims11x.lemma1113C4Claim_of_inputs h1111 h1112 h119 hAut)

end Chev

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1113b
