module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76XLemma315

public section

namespace CFSG.ComponentClassification.Asc76X

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.Asc76
open scoped Pointwise commutatorElement

variable {G : Type} [Group G]

theorem rightConjugate_omega1 (H : Subgroup G) (g : G) :
    rightConjugate (omega1 H) g = omega1 (rightConjugate H g) := by
  apply le_antisymm
  · refine rightConjugate_closure_le fun x hx => mem_omega1_of_sq ?_ ?_
    · rw [mem_rightConjugate_iff]
      simpa [mul_assoc] using hx.1
    · have e := conj_pow (a := g⁻¹) (b := x) (i := 2)
      rw [inv_inv] at e
      rw [e, hx.2, mul_one, inv_mul_cancel]
  · refine (closure_le _).mpr fun y hy => ?_
    rw [SetLike.mem_coe, mem_rightConjugate_iff]
    refine mem_omega1_of_sq ((mem_rightConjugate_iff H g y).mp hy.1) ?_
    rw [conj_pow, hy.2, mul_one, mul_inv_cancel]

variable [Finite G]

theorem exists_normalizer_conj_of_weaklyClosed {S Z : Subgroup G} (hS : IsSylowOf 2 S ⊤)
    (hZS : Z ≤ S) (hZab : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a)
    (hwc : ∀ h : G, rightConjugate Z h ≤ S → rightConjugate Z h = Z) {z h : G} (hz : z ∈ Z)
    (hzh : h⁻¹ * z * h ∈ Z) :
    ∃ n ∈ normalizer (Z : Set G), n⁻¹ * z * n = h⁻¹ * z * h := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS2 : IsPGroup 2 S := IsPGroup.of_card (isSylowOf_iff_card.mp hS).2
  have hZ2 : IsPGroup 2 Z := hS2.to_le hZS
  set y := h⁻¹ * z * h with hydef
  set C := centralizer ({y} : Set G) with hCdef
  have hmemC : ∀ x, x * y = y * x → x ∈ C := fun x hx => mem_centralizer_iff.mpr fun w hw => by
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    exact hx.symm
  have hZC : Z ≤ C := fun w hw => hmemC w (hZab w hw y hzh)
  have hZhC : rightConjugate Z h ≤ C := by
    intro x hx
    rw [mem_rightConjugate_iff] at hx
    apply hmemC
    have h1 := hZab _ hx _ hz
    calc x * y = h⁻¹ * ((h * x * h⁻¹) * z) * h := by rw [hydef]; group
      _ = h⁻¹ * (z * (h * x * h⁻¹)) * h := by rw [h1]
      _ = y * x := by rw [hydef]; group
  have hZh2 : IsPGroup 2 (rightConjugate Z h) := hZ2.map _
  obtain ⟨Q, hQ, hZQ⟩ := exists_isSylowOf_le hZC hZ2
  obtain ⟨Q', hQ', hZQ'⟩ := exists_isSylowOf_le hZhC hZh2
  obtain ⟨c, hc, hQc⟩ := exists_conj_of_isSylowOf hQ hQ'
  have hQ2 : IsPGroup 2 Q := IsPGroup.of_card (isSylowOf_iff_card.mp hQ).2
  obtain ⟨S', hS'', hQS'⟩ := exists_isSylowOf_le (le_top : Q ≤ ⊤) hQ2
  obtain ⟨d, -, hS'd⟩ := exists_conj_of_isSylowOf hS hS''
  have hcy : c * y * c⁻¹ = y := by
    have h1 := mem_centralizer_iff.mp hc y (Set.mem_singleton y)
    rw [← h1, mul_inv_cancel_right]
  have hd1 : rightConjugate Z d⁻¹ = Z := hwc _ fun x hx => by
    rw [mem_rightConjugate_iff, inv_inv] at hx
    have h1 := hQS' (hZQ hx)
    rw [hS'd, mem_rightConjugate_iff] at h1
    have e : d * (d⁻¹ * x * d) * d⁻¹ = x := by group
    rwa [e] at h1
  have hd2 : rightConjugate Z (h * c⁻¹ * d⁻¹) = Z := hwc _ fun x hx => by
    rw [mem_rightConjugate_iff] at hx
    set w := h * c⁻¹ * d⁻¹ * x * (h * c⁻¹ * d⁻¹)⁻¹ with hwdef
    have h1 : h⁻¹ * w * h ∈ rightConjugate Z h := by
      rw [mem_rightConjugate_iff]
      have e : h * (h⁻¹ * w * h) * h⁻¹ = w := by group
      rw [e]
      exact hx
    have h2 := hZQ' h1
    rw [hQc, mem_rightConjugate_iff] at h2
    have h3 := hQS' h2
    rw [hS'd, mem_rightConjugate_iff] at h3
    have e : d * (c * (h⁻¹ * w * h) * c⁻¹) * d⁻¹ = x := by rw [hwdef]; group
    rwa [e] at h3
  have hn : h * c⁻¹ ∈ normalizer (Z : Set G) := by
    rw [← rightConjugate_eq_self_iff]
    have e1 : rightConjugate Z d = Z := by
      have h1 := congrArg (rightConjugate · d) hd1
      simp only [rightConjugate_mul, inv_mul_cancel, rightConjugate_one] at h1
      exact h1.symm
    have h1 := congrArg (rightConjugate · d) hd2
    simp only [rightConjugate_mul, inv_mul_cancel_right] at h1
    rw [h1, e1]
  refine ⟨h * c⁻¹, hn, ?_⟩
  calc (h * c⁻¹)⁻¹ * z * (h * c⁻¹) = c * y * c⁻¹ := by rw [hydef]; group
    _ = y := hcy

omit [Finite G] in
theorem exists_mul_of_mem_sup {H L : Subgroup G} (hHL : ∀ h ∈ H, ∀ l ∈ L, h * l = l * h) {x : G}
    (hx : x ∈ H ⊔ L) : ∃ h ∈ H, ∃ l ∈ L, x = h * l := by
  let P : Subgroup G :=
    { carrier := {x | ∃ h ∈ H, ∃ l ∈ L, x = h * l}
      one_mem' := ⟨1, one_mem _, 1, one_mem _, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨h₁, hh₁, l₁, hl₁, rfl⟩ ⟨h₂, hh₂, l₂, hl₂, rfl⟩
        refine ⟨h₁ * h₂, mul_mem hh₁ hh₂, l₁ * l₂, mul_mem hl₁ hl₂, ?_⟩
        calc h₁ * l₁ * (h₂ * l₂) = h₁ * (l₁ * h₂) * l₂ := by group
          _ = h₁ * (h₂ * l₁) * l₂ := by rw [hHL h₂ hh₂ l₁ hl₁]
          _ = h₁ * h₂ * (l₁ * l₂) := by group
      inv_mem' := by
        rintro _ ⟨h, hh, l, hl, rfl⟩
        refine ⟨h⁻¹, inv_mem hh, l⁻¹, inv_mem hl, ?_⟩
        rw [mul_inv_rev]
        have e := hHL h⁻¹ (inv_mem hh) l⁻¹ (inv_mem hl)
        exact e.symm }
  have hle : H ⊔ L ≤ P := sup_le (fun h hh => ⟨h, hh, 1, one_mem _, by simp⟩)
    (fun l hl => ⟨1, one_mem _, l, hl, by simp⟩)
  exact hle hx

namespace MinCounter

variable {Ω : Set (Subgroup G)}

theorem inf_le_oddCoreIn (hM : MinCounter Ω) (hI : Sec3Inputs) {X : Subgroup G} (hX : X ∈ Ω) :
    X ⊓ sSup (nbr Ω X) ≤ oddCoreIn (sSup (nbr Ω X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hΩ := hM.setting
  obtain ⟨hπ, -, hsyl⟩ := hM.nbr_facts hI hX
  set A := sSup (nbr Ω X) with hAdef
  obtain ⟨Y, hY, -⟩ := hπ.nontrivial
  have hY' : adj Ω X Y := hY
  obtain ⟨TY, hTY⟩ := Sec3Setting.exists_sylow Y
  have hTY' := isSylowOf_iff_card.mp hTY
  have hTY2 : IsPGroup 2 TY := IsPGroup.of_card hTY'.2
  have hYA : Y ≤ A := le_sSup hY
  have hAX : A ≤ normalizer (X : Set G) := sSup_nbr_le_normalizer Ω X
  set N := bar A (X ⊓ A) with hNdef
  have hNn : N.Normal := by
    refine Subgroup.Normal.map ?_ _ (QuotientGroup.mk'_surjective _)
    refine ⟨fun n hn a => ?_⟩
    rw [mem_subgroupOf] at hn ⊢
    obtain ⟨hnX, hnA⟩ := mem_inf.mp hn
    refine mem_inf.mpr ⟨(mem_normalizer_iff.mp (hAX a.2) _).mp hnX, ?_⟩
    simp only [coe_mul, coe_inv]
    exact mul_mem (mul_mem a.2 hnA) (inv_mem a.2)
  have hNT : bar A TY ⊓ N = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hyT, hyN⟩ := mem_inf.mp hy
    obtain ⟨t, htT, rfl⟩ := hyT
    obtain ⟨a, haXA, hat⟩ := hyN
    have hker : a⁻¹ * t ∈ (barMk A).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hat, inv_mul_cancel]
    rw [ker_barMk] at hker
    have hO : ((a : G)⁻¹ * t) ∈ oddCoreIn A := ⟨_, hker, rfl⟩
    have htXO : (t : G) ∈ X ⊔ oddCoreIn A := by
      have e : (t : G) = (a : G) * ((a : G)⁻¹ * t) := by group
      rw [e]
      exact mul_mem (mem_sup_left (mem_inf.mp (mem_subgroupOf.mp haXA)).1) (mem_sup_right hO)
    obtain ⟨k, hk⟩ := hTY2 ⟨t, mem_subgroupOf.mp htT⟩
    have hk' : (t : G) ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have htX : (t : G) ∈ X :=
      mem_of_two_element ((oddCoreIn_le A).trans hAX) (odd_card_oddCoreIn A) htXO hk'
    have hodd := (hΩ.twoPart X hX Y hY'.1 (Ne.symm hY'.2.1)).2
    have htXY : (t : G) ∈ X ⊓ Y := mem_inf.mpr ⟨htX, hTY'.1 (mem_subgroupOf.mp htT)⟩
    have ht1 : (t : G) = 1 := by
      have h1 : orderOf (⟨t, htXY⟩ : ↥(X ⊓ Y)) ∣ 2 ^ k :=
        orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hk'))
      have h2 : orderOf (⟨t, htXY⟩ : ↥(X ⊓ Y)) ∣ Nat.card ↥(X ⊓ Y) := orderOf_dvd_natCard _
      have h3 : orderOf (⟨t, htXY⟩ : ↥(X ⊓ Y)) = 1 := by
        obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
        rcases j with _ | j
        · simpa using hj
        · exfalso
          rw [hj] at h2
          exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr
            ((dvd_pow_self 2 (Nat.succ_ne_zero j)).trans h2))
      have := congrArg Subtype.val (orderOf_eq_one_iff.mp h3)
      simpa using this
    have ht1' : t = 1 := Subtype.ext ht1
    rw [ht1', map_one]
    exact one_mem _
  have hNsyl : IsSylowOf 2 (bar A TY ⊓ N) N :=
    isSylowOf_inf le_top (by rw [normalizer_eq_top_iff.mpr hNn]) (hsyl Y hY TY hTY)
  rw [hNT, isSylowOf_iff_card, card_bot] at hNsyl
  have hNodd : Odd (Nat.card N) := by
    have h1 := hNsyl.2
    have h0 : (Nat.card N).factorization 2 = 0 := by
      by_contra h
      have := Nat.one_lt_pow h (by norm_num : 1 < 2)
      omega
    exact Nat.odd_iff.mpr (by
      rcases Nat.even_or_odd (Nat.card N) with he | ho
      · exfalso
        have hpos : Nat.card N ≠ 0 := Nat.card_pos.ne'
        exact absurd h0 (Nat.Prime.factorization_pos_of_dvd Nat.prime_two hpos
          (even_iff_two_dvd.mp he)).ne'
      · exact Nat.odd_iff.mp ho)
  have hNbot : N ≤ CFSG.oddCore (BarGroup A) := le_sSup ⟨hNn, hNodd⟩
  rw [oddCore_quotient_oddCore, le_bot_iff, hNdef, bar, Subgroup.map_eq_bot_iff, ker_barMk] at hNbot
  intro x hx
  exact ⟨⟨x, (mem_inf.mp hx).2⟩, hNbot (mem_subgroupOf.mpr hx), rfl⟩

theorem eq_one_of_mem_bar_center (hM : MinCounter Ω) (hI : Sec3Inputs) {X Y TY : Subgroup G}
    (hX : X ∈ Ω) (hY : adj Ω X Y) (hTY : IsSylowOf 2 TY Y) {z : BarGroup (sSup (nbr Ω X))}
    (hz : z ∈ bar (sSup (nbr Ω X)) TY) (hzc : ∀ w, w * z = z * w) : z = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hΩ := hM.setting
  obtain ⟨hπ, hsz, hsyl⟩ := hM.nbr_facts hI hX
  obtain ⟨Q, hQ, hQY⟩ : ∃ Q ∈ nbr Ω X, Q ≠ Y := by
    obtain ⟨J₀, hJ₀, L₀, hL₀, hne⟩ := hπ.nontrivial
    by_cases h : J₀ = Y
    · exact ⟨L₀, hL₀, fun h' => hne (h.trans h'.symm)⟩
    · exact ⟨J₀, hJ₀, h⟩
  have hY' : Y ∈ nbr Ω X := hY
  obtain ⟨TQ, hTQ⟩ := Sec3Setting.exists_sylow Q
  have hTQ' := isSylowOf_iff_card.mp hTQ
  have hTY' := isSylowOf_iff_card.mp hTY
  have hszt : IsSzOrU3 ↥(⊤ : Subgroup (BarGroup (sSup (nbr Ω X)))) :=
    isSzOrU3_of_mulEquiv Subgroup.topEquiv hsz
  have hP₁ := hsyl Y hY' TY hTY
  have hP₂ := hsyl Q hQ TQ hTQ
  have hQΩ := (hπ.adj_of_mem Q hQ).1
  have hne : bar (sSup (nbr Ω X)) TY ≠ bar (sSup (nbr Ω X)) TQ := by
    intro h
    apply hQY
    refine hΩ.eq_of_bar_le hQΩ hY.1 (le_sSup hQ) (le_sSup hY') hTQ'.1
      (IsPGroup.of_card hTQ'.2) (hΩ.sylow_ne_bot hQΩ hTQ) ?_
    rw [← h]
    exact bar_mono hTY'.1
  have hzN : z ∈ normalizer ((bar (sSup (nbr Ω X)) TQ : Subgroup (BarGroup (sSup (nbr Ω X)))) :
      Set (BarGroup (sSup (nbr Ω X)))) := by
    rw [mem_normalizer_iff]
    intro w
    rw [show z * w * z⁻¹ = w by rw [← hzc w, mul_inv_cancel_right]]
  obtain ⟨k, hk⟩ := isPGroup_bar (X := (sSup (nbr Ω X))) (IsPGroup.of_card hTY'.2) ⟨z, hz⟩
  have hk' : z ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have hzQ := mem_of_mem_normalizer_of_isSylowOf hP₂ (mem_top z) hzN hk'
  have hinf := hI.hB.inf_eq_bot_of_isSylowOf hszt hP₁ hP₂ hne
  have hmem : z ∈ bar (sSup (nbr Ω X)) TY ⊓ bar (sSup (nbr Ω X)) TQ := mem_inf.mpr ⟨hz, hzQ⟩
  rwa [hinf, mem_bot] at hmem

end MinCounter

namespace Config

variable {Ω : Set (Subgroup G)} {K J R T S : Subgroup G}

theorem Z_le_centralizer (hc : Config Ω K J R T S) (hM : MinCounter Ω) (hI : Sec3Inputs) :
    omega1 R ⊔ omega1 T ≤ centralizer (R : Set G) := by
  obtain ⟨hszJ, hRs, hRB⟩ := hc.szJ hM hI
  have hRT := hc.commute_RT hM.setting
  refine sup_le ((closure_le _).mpr fun x hx => ?_) ((closure_le _).mpr fun x hx => ?_)
  · exact mem_centralizer_iff.mpr fun y hy =>
      (commute_of_sq_eq_one hI.hB hRB hc.R2 hszJ hRs hx.1 hx.2 hy).symm
  · rw [SetLike.mem_coe, mem_centralizer_iff]
    intro y hy
    have h := commutator_mem_commutator hy hx.1
    rw [hRT, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h
    exact h

theorem normalClosure_eq_top (hc : Config Ω K J R T S) (hM : MinCounter Ω) (hI : Sec3Inputs) :
    normalClosure (R : Set G) = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hΩ := hM.setting
  have hΩK := hM.lemma312 hI.h22 hI.hB hc.mem
  have hKN : K ≤ normalClosure (R : Set G) := by
    rw [← hΩ.perfect K hc.mem]
    refine (closure_le _).mpr fun x hx => ?_
    obtain ⟨hxK, i, hxi⟩ := hx
    obtain ⟨S', hS', hxS'⟩ := exists_isSylowOf_le ((zpowers_le).mpr hxK)
      (isPGroup_zpowers_of_two_element hxi)
    obtain ⟨k, -, hk⟩ := exists_conj_of_isSylowOf hc.sylowR hS'
    have hx' : x ∈ rightConjugate R k := hk ▸ hxS' (mem_zpowers x)
    rw [mem_rightConjugate_iff] at hx'
    have h1 := normalClosure_normal.conj_mem _ (subset_normalClosure hx') k⁻¹
    simpa [mul_assoc] using h1
  rw [eq_top_iff, ← hΩ.generates]
  refine sSup_le fun L hL => ?_
  rw [hΩK] at hL
  obtain ⟨a, rfl⟩ := hL
  intro x hx
  rw [mem_rightConjugate_iff] at hx
  have h1 := normalClosure_normal.conj_mem _ (hKN hx) a⁻¹
  simpa [mul_assoc] using h1

theorem exists_omega1_conj (hc : Config Ω K J R T S) (hM : MinCounter Ω) (hI : Sec3Inputs) :
    ∃ g : G, rightConjugate (omega1 R) g = omega1 T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hΩK := hM.lemma312 hI.h22 hI.hB hc.mem
  have hJ : J ∈ Set.range (rightConjugate K) := hΩK ▸ hc.J_mem
  obtain ⟨g, hg⟩ := hJ
  have hRg : IsSylowOf 2 (rightConjugate R g) J := hg ▸ isSylowOf_rightConjugate hc.sylowR g
  obtain ⟨j, -, hj⟩ := exists_conj_of_isSylowOf hRg hc.sylowT
  refine ⟨g * j, ?_⟩
  rw [rightConjugate_omega1, ← rightConjugate_mul, ← hj]

theorem omega1_conj_le (hc : Config Ω K J R T S) (hM : MinCounter Ω) (hI : Sec3Inputs)
    {M U : Subgroup G} (hM' : M ∈ Ω) (hU : IsSylowOf 2 U M) (hUZ : omega1 U ≤ omega1 R ⊔ omega1 T)
    {h : G} (hZh : rightConjugate (omega1 R ⊔ omega1 T) h ≤ S) :
    rightConjugate (omega1 U) h ≤ omega1 R ∨ rightConjugate (omega1 U) h ≤ omega1 T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hΩ := hM.setting
  have hUh : rightConjugate (omega1 U) h ≤ S := (map_mono hUZ).trans hZh
  obtain ⟨E, hEU, hE, hE4⟩ := exists_fourGroup_le (hΩ.rank M hM' U hU).1
  have hEo : E ≤ omega1 U := fun e he => mem_omega1_of_sq (hEU he) (hE.2 e he)
  have hEh : rightConjugate E h ≤ S ⊓ rightConjugate M h :=
    le_inf ((map_mono hEo).trans hUh) (map_mono (hEU.trans hU.le))
  have hsyl := hM.lemma310 hI.h22 hI.hB hc.mem hc.sylowR hc.S2 hc.le_R hc.good
    (hΩ.conj_mem M hM' h) hEh (isElemAbelian_rightConjugate hE h)
    (by rw [rightConjugate_card, hE4])
  have hZ2 := (hc.isElemAbelian_Z hM hI).2
  have key : ∀ x ∈ rightConjugate (omega1 U) h, x ∈ S ⊓ rightConjugate M h ∧ x ^ 2 = 1 := by
    intro x hx
    refine ⟨mem_inf.mpr ⟨hUh hx, map_mono ((omega1_le U).trans hU.le) hx⟩, ?_⟩
    have h1 := hZ2 _ (hUZ ((mem_rightConjugate_iff _ h x).mp hx))
    rw [conj_pow] at h1
    have e : h⁻¹ * (h * x ^ 2 * h⁻¹) * h = x ^ 2 := by group
    rw [← e, h1]
    group
  rcases hc.sylow_eq hM hI (hΩ.conj_mem M hM' h) hsyl inf_le_left with h1 | h1
  · refine Or.inl fun x hx => ?_
    obtain ⟨hxS, hx2⟩ := key x hx
    rw [h1] at hxS
    exact mem_omega1_of_sq hxS hx2
  · refine Or.inr fun x hx => ?_
    obtain ⟨hxS, hx2⟩ := key x hx
    rw [h1] at hxS
    exact mem_omega1_of_sq hxS hx2

theorem pure_of_conj (hc : Config Ω K J R T S) (hM : MinCounter Ω) (hI : Sec3Inputs) {x h : G}
    (hx : x ∈ omega1 R ∨ x ∈ omega1 T) (hxh : h⁻¹ * x * h ∈ omega1 R ⊔ omega1 T) :
    h⁻¹ * x * h ∈ omega1 R ∨ h⁻¹ * x * h ∈ omega1 T := by
  have hZab := hc.isElemAbelian_Z hM hI
  have hZcomm : ∀ a ∈ omega1 R ⊔ omega1 T, ∀ b ∈ omega1 R ⊔ omega1 T, a * b = b * a :=
    fun a ha b hb => by
      have h1 : (⟨a, ha⟩ : ↥(omega1 R ⊔ omega1 T)) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ :=
        hZab.1.is_comm.comm _ _
      simpa using congrArg Subtype.val h1
  have hxZ : x ∈ omega1 R ⊔ omega1 T := hx.elim (fun h => mem_sup_left h) (fun h => mem_sup_right h)
  obtain ⟨n, hn, hnx⟩ := exists_normalizer_conj_of_weaklyClosed hc.sylowS hc.Z_le hZcomm
    (fun g hg => hc.weaklyClosed hM hI hg) hxZ hxh
  have hZn : rightConjugate (omega1 R ⊔ omega1 T) n ≤ S := by
    rw [(rightConjugate_eq_self_iff _ n).mpr hn]
    exact hc.Z_le
  have hmem : ∀ {U M : Subgroup G}, M ∈ Ω → IsSylowOf 2 U M → omega1 U ≤ omega1 R ⊔ omega1 T →
      x ∈ omega1 U → n⁻¹ * x * n ∈ omega1 R ∨ n⁻¹ * x * n ∈ omega1 T := by
    intro U M hM' hU hUZ hxU
    have hxn : n⁻¹ * x * n ∈ rightConjugate (omega1 U) n := by
      rw [mem_rightConjugate_iff]
      simpa [mul_assoc] using hxU
    rcases hc.omega1_conj_le hM hI hM' hU hUZ hZn with h1 | h1
    · exact Or.inl (h1 hxn)
    · exact Or.inr (h1 hxn)
  rw [← hnx]
  rcases hx with hx | hx
  · exact hmem hc.mem hc.sylowR le_sup_left hx
  · exact hmem hc.J_mem hc.sylowT le_sup_right hx

theorem eq_one_of_central (hc : Config Ω K J R T S) (hM : MinCounter Ω) (hI : Sec3Inputs)
    {x : G} (hx : x ∈ omega1 R ⊔ omega1 T) (hcen : ∀ g : G, g * x = x * g) : x = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hΩ := hM.setting
  have hRT := hc.commute_RT hΩ
  have hRTc : ∀ a ∈ R, ∀ b ∈ T, a * b = b * a := fun a ha b hb => by
    have h := commutator_mem_commutator ha hb
    rw [hRT, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h
    exact h
  have hZ2 := (hc.isElemAbelian_Z hM hI).2
  obtain ⟨r, hr, t, ht, rfl⟩ := exists_mul_of_mem_sup
    (fun a ha b hb => hRTc a ((omega1_le R) ha) b ((omega1_le T) hb)) hx
  have hrR := omega1_le R hr
  have htT := omega1_le T ht
  have hrK : r ∈ K := hc.sylowR.le hrR
  set A := sSup (nbr Ω K) with hAdef
  have hJA : J ≤ A := le_sSup hc.adjKJ
  have hAK : A ≤ normalizer (K : Set G) := sSup_nbr_le_normalizer Ω K
  have hTA : T ≤ A := hc.sylowT.le.trans hJA
  set t' : A := ⟨t, hTA htT⟩ with ht'def
  have htc : ∀ w : BarGroup A, w * barMk A t' = barMk A t' * w := by
    intro w
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.oddCore A) w
    have h1 : (a : G) * r * t * (a : G)⁻¹ = r * t := by
      have hax := hcen a
      calc (a : G) * r * t * (a : G)⁻¹ = (a : G) * (r * t) * (a : G)⁻¹ := by group
        _ = r * t * a * (a : G)⁻¹ := by rw [hax]
        _ = r * t := by group
    have e : t * ((a : G) * t * (a : G)⁻¹)⁻¹ = r⁻¹ * ((a : G) * r * (a : G)⁻¹) := by
      calc t * ((a : G) * t * (a : G)⁻¹)⁻¹ =
          r⁻¹ * ((r * t) * ((a : G) * t * (a : G)⁻¹)⁻¹) := by group
        _ = r⁻¹ * (((a : G) * r * t * (a : G)⁻¹) * ((a : G) * t * (a : G)⁻¹)⁻¹) := by rw [h1]
        _ = r⁻¹ * ((a : G) * r * (a : G)⁻¹) := by group
    have hmemK : t * ((a : G) * t * (a : G)⁻¹)⁻¹ ∈ K := by
      rw [e]
      exact mul_mem (inv_mem hrK) ((mem_normalizer_iff.mp (hAK a.2) r).mp hrK)
    set u : A := t' * (a * t' * a⁻¹)⁻¹ with hudef
    have hu : (u : G) = t * ((a : G) * t * (a : G)⁻¹)⁻¹ := by
      rw [hudef]
      simp [t']
    have hO := hM.inf_le_oddCoreIn hI hc.mem (mem_inf.mpr ⟨hu ▸ hmemK, u.2⟩)
    have hu1 : barMk A u = 1 := (barMk_eq_one_iff u).mpr hO
    rw [hudef, map_mul, map_inv, map_mul, map_mul, map_inv, mul_inv_eq_one] at hu1
    change QuotientGroup.mk' (CFSG.oddCore A) a * barMk A t' = barMk A t' * _
    calc QuotientGroup.mk' (CFSG.oddCore A) a * barMk A t' =
        (barMk A a * barMk A t' * (barMk A a)⁻¹) * barMk A a := by group
      _ = barMk A t' * barMk A a := by rw [← hu1]
  have ht1 := hM.eq_one_of_mem_bar_center hI hc.mem hc.adjKJ hc.sylowT (barMk_mem_bar htT) htc
  have ht2 : t' ^ (2 ^ 1) = 1 := Subtype.ext (by simpa [t'] using hZ2 t (mem_sup_right ht))
  have ht'1 := eq_one_of_two_element_of_ker (barMk A) (odd_card_ker_barMk A) ht2 ht1
  have htone : t = 1 := by simpa [t'] using congrArg Subtype.val ht'1
  rw [htone, mul_one] at hcen ⊢
  have hΩK := hM.lemma312 hI.h22 hI.hB hc.mem
  have hJ' : J ∈ Set.range (rightConjugate K) := hΩK ▸ hc.J_mem
  obtain ⟨g, hg⟩ := hJ'
  have hrJ : r ∈ J := by
    rw [← hg, mem_rightConjugate_iff, hcen g, mul_inv_cancel_right]
    exact hrK
  have hodd := (hΩ.twoPart K hc.mem J hc.J_mem (Ne.symm hc.adjKJ.2.1)).2
  have hrKJ : r ∈ K ⊓ J := mem_inf.mpr ⟨hrK, hrJ⟩
  have h1 : orderOf (⟨r, hrKJ⟩ : ↥(K ⊓ J)) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hZ2 r (mem_sup_left hr)))
  have h2 : orderOf (⟨r, hrKJ⟩ : ↥(K ⊓ J)) ∣ Nat.card ↥(K ⊓ J) := orderOf_dvd_natCard _
  have h3 : orderOf (⟨r, hrKJ⟩ : ↥(K ⊓ J)) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
    · exact h
    · exfalso
      rw [h] at h2
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  have := congrArg Subtype.val (orderOf_eq_one_iff.mp h3)
  simpa using this

theorem eq_bot_of_normal_le (hc : Config Ω K J R T S) (hM : MinCounter Ω) (hI : Sec3Inputs)
    {Q : Subgroup G} (hQ : Q.Normal) (hQZ : Q ≤ omega1 R ⊔ omega1 T) : Q = ⊥ := by
  have hRQ : R ≤ centralizer (Q : Set G) :=
    le_centralizer_iff.mp (hQZ.trans (hc.Z_le_centralizer hM hI))
  have htop : normalClosure (R : Set G) ≤ centralizer (Q : Set G) :=
    normalClosure_le_normal hRQ
  rw [hc.normalClosure_eq_top hM hI, top_le_iff] at htop
  rw [eq_bot_iff]
  intro x hx
  rw [mem_bot]
  refine hc.eq_one_of_central hM hI (hQZ hx) fun g => ?_
  have hg : g ∈ centralizer (Q : Set G) := htop ▸ mem_top g
  exact (mem_centralizer_iff.mp hg x hx).symm

end Config

end CFSG.ComponentClassification.Asc76X
