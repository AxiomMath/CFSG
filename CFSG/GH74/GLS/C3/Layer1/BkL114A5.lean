module

public import CFSG.GH74.GLS.C3.Layer1.BkL114A7
public import CFSG.GH74.GLS.C3.Layer1.BkA5Facts
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.L2Act
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.C3.Layer1.Back
open scoped commutatorElement

variable {G : Type} [Group G]

theorem factorization_sixty : (60 : ℕ).factorization 2 = 2 := by
  have h : (60 : ℕ) = 2 ^ 2 * 15 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  simp

theorem factorization_two_card_of_equiv_A5 [Finite G] {K : Subgroup G}
    (e : kBar K ≃* alternatingGroup (Fin 5)) : (Nat.card ↥K).factorization 2 = 2 := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥K)
  have h2 : Nat.card (kBar K) = 60 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  have hodd : Odd (Nat.card (pPrimeCore 2 ↥K)) :=
    Nat.coprime_two_left.1 CFSG.pPrimeCore_coprime_card
  have hne : Nat.card (pPrimeCore 2 ↥K) ≠ 0 := Nat.card_pos.ne'
  have h3 : Nat.card ↥K = 60 * Nat.card (pPrimeCore 2 ↥K) := by
    rw [h1]
    show Nat.card (kBar K) * _ = _
    rw [h2]
  rw [h3, Nat.factorization_mul (by norm_num) hne, Finsupp.add_apply, factorization_sixty,
    Setup91.factorization_two_of_odd hodd]

theorem alt5_no_order_four : ∀ g : alternatingGroup (Fin 5), g ^ 4 = 1 → g * g = 1 := by
  decide +kernel

theorem centerlessBar_of_A5 {K : Subgroup G} (h : Nonempty (kBar K ≃* alternatingGroup (Fin 5))) :
    CenterlessBar K := by
  obtain ⟨e⟩ := h
  intro a ha
  have hc : e a ∈ Subgroup.center (alternatingGroup (Fin 5)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨g', rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, ha g']
  have hcard4 : 4 ≤ Nat.card (Fin 5) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num
  rw [alternatingGroup.center_eq_bot hcard4, Subgroup.mem_bot] at hc
  exact e.injective (by rw [hc, map_one])

theorem inf_embeds_alt5 [Finite G] {T K : Subgroup G} (hT2 : IsPGroup 2 ↥T)
    (hP : IsSylowOf 2 (T ⊓ K) K) (e5 : kBar K ≃* alternatingGroup (Fin 5)) :
    ∃ ι : ↥(T ⊓ K) →* alternatingGroup (Fin 5), Function.Injective ι ∧ Nat.card ↥ι.range = 4 ∧
      ∀ p : ↥(T ⊓ K), ι p = e5 (QuotientGroup.mk (⟨(p : G), p.2.2⟩ : ↥K)) := by
  have hinj : Function.Injective (e5.toMonoidHom.comp ((QuotientGroup.mk' (pPrimeCore 2 ↥K)).comp
      (Subgroup.inclusion (inf_le_right : T ⊓ K ≤ K)))) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro p hp
    have hp1 : e5 ((QuotientGroup.mk' (pPrimeCore 2 ↥K)) (Subgroup.inclusion inf_le_right p)) = 1 :=
      hp
    have h1 : (QuotientGroup.mk' (pPrimeCore 2 ↥K)) (Subgroup.inclusion inf_le_right p) = 1 :=
      e5.injective (hp1.trans (map_one e5).symm)
    have h2 : Subgroup.inclusion (inf_le_right : T ⊓ K ≤ K) p ∈ pPrimeCore 2 ↥K :=
      (QuotientGroup.eq_one_iff _).1 h1
    have h3 : ((p : G)) ∈ T ⊓ pPrimeCoreOf 2 K :=
      ⟨p.2.1, Setup91.mem_pPrimeCoreOf_iff.2 ⟨p.2.2, h2⟩⟩
    rw [Setup91.inf_pPrimeCoreOf_eq_bot K hT2, Subgroup.mem_bot] at h3
    exact Subgroup.mem_bot.2 (Subtype.ext h3)
  refine ⟨e5.toMonoidHom.comp ((QuotientGroup.mk' (pPrimeCore 2 ↥K)).comp
    (Subgroup.inclusion (inf_le_right : T ⊓ K ≤ K))), hinj, ?_, fun p => rfl⟩
  have hPcard : Nat.card ↥(T ⊓ K) = 4 := by
    rw [hP.card_eq, factorization_two_card_of_equiv_A5 e5]
    norm_num
  rw [← hPcard]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem aconfigW_five_P [Finite G] {x : G} {K T Q S : Subgroup G} {a : G}
    (h : IsAConfigW 5 x K T Q S a) :
    Nat.card ↥(T ⊓ K) = 4 ∧ CFSG.IsElementaryAbelian 2 ↥(T ⊓ K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e5⟩ := h.kbar
  have hT2 : IsPGroup 2 ↥T := h.sylowT.isPGroup
  have hP := aconfigW_inf_sylow h
  obtain ⟨ι, hι, hcard, -⟩ := inf_embeds_alt5 hT2 hP e5
  have hPcard : Nat.card ↥(T ⊓ K) = 4 := by
    rw [hP.card_eq, factorization_two_card_of_equiv_A5 e5]
    norm_num
  refine ⟨hPcard, ?_⟩
  have hPcomm : IsMulCommutative ↥(T ⊓ K) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (by rw [hPcard]; norm_num)
  refine isElementaryAbelian_of_forall (fun u hu v hv => ?_) (fun u hu => ?_)
  · exact congrArg Subtype.val (hPcomm.is_comm.comm (⟨u, hu⟩ : ↥(T ⊓ K)) ⟨v, hv⟩)
  · set p : ↥(T ⊓ K) := ⟨u, hu⟩
    have h4 : p ^ 4 = 1 := by
      have := pow_card_eq_one' (G := ↥(T ⊓ K)) (x := p)
      rwa [hPcard] at this
    have h5 : ι p ^ 4 = 1 := by rw [← map_pow, h4, map_one]
    have h6 := alt5_no_order_four _ h5
    have h7 : p * p = 1 := hι (by rw [map_mul, h6, map_one])
    exact congrArg Subtype.val h7

theorem aconfigW_P_norm [Finite G] {n : ℕ} {x : G} {K T Q S : Subgroup G} {a : G}
    (h : IsAConfigW n x K T Q S a) : ∀ t ∈ T, ∀ p ∈ T ⊓ K, t * p * t⁻¹ ∈ T ⊓ K := fun t ht p hp =>
  ⟨T.mul_mem (T.mul_mem ht hp.1) (T.inv_mem ht), h.normalInC t (h.T_le_C ht) p hp.2⟩

theorem aconfigW_Q_norm [Finite G] {n : ℕ} {x : G} {K T Q S : Subgroup G} {a : G}
    (h : IsAConfigW n x K T Q S a) : ∀ t ∈ T, ∀ q ∈ Q, t * q * t⁻¹ ∈ Q := by
  intro t ht q hq
  have hCnorm : centralizer ({x} : Set G) ≤ normalizer (K : Set G) := fun c hc =>
    mem_normalizer_of_two_sided (fun w hw => h.normalInC c hc w hw) (fun w hw => by
      simpa using h.normalInC c⁻¹ ((centralizer ({x} : Set G)).inv_mem hc) w hw)
  have hNxK : t ∈ NxK x K := ⟨h.T_le_C ht, hCnorm (h.T_le_C ht)⟩
  have hQ := h.hQ
  rw [hQ] at hq ⊢
  refine ⟨T.mul_mem (T.mul_mem ht hq.1) (T.inv_mem ht), ?_⟩
  exact (Subgroup.mem_normalizer_iff.1 (NxK_le_normalizer_CxK x K hNxK) q).1 hq.2

theorem aconfigW_five_commDisj [Finite G] {x : G} {K T Q S : Subgroup G} {a : G}
    (h : IsAConfigW 5 x K T Q S a) : CommDisj (T ⊓ K) Q := by
  have hCD := commDisj_inf_CxK (x := x) h.sylowT.isPGroup (centerlessBar_of_A5 h.kbar)
  rw [← h.hQ] at hCD
  exact hCD

theorem aconfigW_five_R [Finite G] {x : G} {K T Q S : Subgroup G} {a : G}
    (h : IsAConfigW 5 x K T Q S a) :
    CFSG.IsElementaryAbelian 2 ↥((T ⊓ K) ⊔ Q) ∧ Nat.card ↥((T ⊓ K) ⊔ Q) = 16 := by
  obtain ⟨hPcard, hPel⟩ := aconfigW_five_P h
  have hCD := aconfigW_five_commDisj h
  exact ⟨isElementaryAbelian_sup_of_commute hPel h.elemQ hCD.comm, by
    rw [card_sup_of_commute_of_disjoint hCD.comm hCD.inf, hPcard, h.card_Q]⟩

theorem aconfigW_five_R_norm [Finite G] {n : ℕ} {x : G} {K T Q S : Subgroup G} {a : G}
    (h : IsAConfigW n x K T Q S a) (hCD : CommDisj (T ⊓ K) Q) :
    ∀ t ∈ T, ∀ r ∈ (T ⊓ K) ⊔ Q, t * r * t⁻¹ ∈ (T ⊓ K) ⊔ Q := by
  intro t ht r hr
  obtain ⟨p, hp, q, hq, rfl⟩ := mem_sup_of_commute hCD.comm hr
  have e : t * (p * q) * t⁻¹ = (t * p * t⁻¹) * (t * q * t⁻¹) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (aconfigW_P_norm h t ht p hp))
    (Subgroup.mem_sup_right (aconfigW_Q_norm h t ht q hq))

theorem aconfigW_five_y [Finite G] {x : G} {K T Q S : Subgroup G} {a : G}
    (h : IsAConfigW 5 x K T Q S a) :
    ∃ y ∈ T, y * y = 1 ∧ y ∉ (T ⊓ K) ⊔ Q ∧
      (∀ t ∈ T, t ∈ (T ⊓ K) ⊔ Q ∨ ∃ r ∈ (T ⊓ K) ⊔ Q, t = r * y) ∧
      ∃ q ∈ Q, y * q ≠ q * y := by
  obtain ⟨y, hyT, hy2, hTeq, q₀, hq₀, hyq₀⟩ := h.fiveCase rfl
  have hCD := aconfigW_five_commDisj h
  have hyy : y * y = 1 := by
    have := pow_orderOf_eq_one y
    rw [hy2, sq] at this
    exact this
  obtain ⟨hRel, hRcard⟩ := aconfigW_five_R h
  have hRnorm := aconfigW_five_R_norm h hCD
  refine ⟨y, hyT, hyy, ?_, ?_, q₀, hq₀, hyq₀⟩
  · intro hyR
    have hq₀R : q₀ ∈ (T ⊓ K) ⊔ Q := Subgroup.mem_sup_right hq₀
    exact hyq₀ ((forall_of_isElementaryAbelian hRel).1 y hyR q₀ hq₀R)
  · intro t ht
    rw [hTeq] at ht
    have hnorm : zpowers y ≤ normalizer (((T ⊓ K) ⊔ Q : Subgroup G) : Set G) := by
      rw [zpowers_le]
      refine mem_normalizer_of_two_sided (fun w hw => hRnorm y hyT w hw) (fun w hw => ?_)
      have := hRnorm y⁻¹ (T.inv_mem hyT) w hw
      simpa using this
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hnorm] at ht
    obtain ⟨r, hr, u, hu, rfl⟩ := ht
    rcases mem_zpowers_of_sq hyy hu with rfl | rfl
    · left
      simpa using hr
    · right
      exact ⟨r, hr, rfl⟩

theorem aconfigW_five_y_nontriv [Finite G] {x : G} {K T Q S : Subgroup G} {a : G}
    (h : IsAConfigW 5 x K T Q S a) {y : G} (hyT : y ∈ T) (hyR : y ∉ (T ⊓ K) ⊔ Q) :
    ∃ p ∈ T ⊓ K, y * p ≠ p * y := by
  by_contra hcon
  push Not at hcon
  obtain ⟨e5⟩ := h.kbar
  have hT2 : IsPGroup 2 ↥T := h.sylowT.isPGroup
  have hTC : T ≤ centralizer ({x} : Set G) := h.T_le_C
  obtain ⟨ψ, hker, hψK⟩ :=
    lemma113d_alt h.K_le_C h.normalInC (n := 5) (by norm_num) (by norm_num) e5
  obtain ⟨ι, hιinj, hιcard, hι⟩ := inf_embeds_alt5 hT2 (aconfigW_inf_sylow h) e5
  have hker' : ψ.ker =
      (CMK (centralizer ({x} : Set G)) K).subgroupOf (centralizer ({x} : Set G)) := hker
  have hyC : y ∈ centralizer ({x} : Set G) := hTC hyT
  have hψι : ∀ (p : G) (hp : p ∈ T ⊓ K), ψ ⟨p, hTC hp.1⟩ =
      ((ι ⟨p, hp⟩ : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) := by
    intro p hp
    rw [hι ⟨p, hp⟩]
    exact hψK p hp.2
  have hcommψ : ∀ (v w : G) (hv : v ∈ centralizer ({x} : Set G))
      (hw : w ∈ centralizer ({x} : Set G)), v * w = w * v →
      ψ ⟨v, hv⟩ * ψ ⟨w, hw⟩ = ψ ⟨w, hw⟩ * ψ ⟨v, hv⟩ := by
    intro v w hv hw hvw
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hvw
  obtain ⟨r, hr, hry⟩ := alt5_centralizer_mem (X := ι.range) hιcard (ψ ⟨y, hyC⟩) (by
    rintro _ ⟨p, rfl⟩
    rw [show ((ι p : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) =
      ψ ⟨(p : G), hTC p.2.1⟩ from (hψι p p.2).symm]
    exact hcommψ y p hyC _ (hcon p p.2))
  obtain ⟨p, rfl⟩ := hr
  have hyp : ψ ⟨y, hyC⟩ = ψ ⟨(p : G), hTC p.2.1⟩ := by
    rw [hψι p p.2, hry]
  have hmem : y * (p : G)⁻¹ ∈ centralizer ({x} : Set G) :=
    (centralizer ({x} : Set G)).mul_mem hyC ((centralizer ({x} : Set G)).inv_mem (hTC p.2.1))
  have h1 : ψ ⟨y * (p : G)⁻¹, hmem⟩ = 1 := by
    have e : (⟨y * (p : G)⁻¹, hmem⟩ : ↥(centralizer ({x} : Set G))) =
        ⟨y, hyC⟩ * ⟨(p : G), hTC p.2.1⟩⁻¹ := rfl
    rw [e, map_mul, map_inv, hyp, mul_inv_cancel]
  have h2 : y * (p : G)⁻¹ ∈ CxK x K := by
    have : (⟨y * (p : G)⁻¹, hmem⟩ : ↥(centralizer ({x} : Set G))) ∈ ψ.ker := h1
    rw [hker', Subgroup.mem_subgroupOf] at this
    exact this
  have h3 : y * (p : G)⁻¹ ∈ Q := by
    rw [h.hQ]
    exact ⟨T.mul_mem hyT (T.inv_mem p.2.1), h2⟩
  apply hyR
  have e : y = (y * (p : G)⁻¹) * p := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right h3) (Subgroup.mem_sup_left p.2)

theorem card_inf_centralizer_le_two [Finite G] {V : Subgroup G} (hV4 : Nat.card ↥V = 4) {y : G}
    (hy : ∃ v ∈ V, y * v ≠ v * y) : Nat.card ↥(V ⊓ centralizer ({y} : Set G)) ≤ 2 := by
  have hdvd : Nat.card ↥(V ⊓ centralizer ({y} : Set G)) ∣ Nat.card ↥V :=
    Subgroup.card_dvd_of_le inf_le_left
  rw [hV4, show (4 : ℕ) = 2 ^ 2 by norm_num] at hdvd
  obtain ⟨i, hi, hci⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hne : Nat.card ↥(V ⊓ centralizer ({y} : Set G)) ≠ 4 := by
    intro h4
    have heq := Subgroup.eq_of_le_of_card_ge (inf_le_left : V ⊓ centralizer ({y} : Set G) ≤ V)
      (by rw [h4, hV4])
    obtain ⟨v, hv, hyv⟩ := hy
    apply hyv
    have hv' : v ∈ V ⊓ centralizer ({y} : Set G) := by rw [heq]; exact hv
    exact (mem_centralizer_singleton_iff.1 hv'.2).symm
  interval_cases i
  · rw [hci]; norm_num
  · rw [hci]; norm_num
  · exact absurd (by rw [hci]; norm_num) hne

theorem aconfigW_five_card_centralizer_R [Finite G] {x : G} {K T Q S : Subgroup G} {a : G}
    (h : IsAConfigW 5 x K T Q S a) {y : G} (hyT : y ∈ T)
    (hyP : ∃ p ∈ T ⊓ K, y * p ≠ p * y) (hyQ : ∃ q ∈ Q, y * q ≠ q * y) :
    Nat.card ↥(((T ⊓ K) ⊔ Q) ⊓ centralizer ({y} : Set G)) ≤ 4 := by
  obtain ⟨hPcard, hPel⟩ := aconfigW_five_P h
  have hCD := aconfigW_five_commDisj h
  have hle : ((T ⊓ K) ⊔ Q) ⊓ centralizer ({y} : Set G) ≤
      ((T ⊓ K) ⊓ centralizer ({y} : Set G)) ⊔ (Q ⊓ centralizer ({y} : Set G)) := by
    rintro r ⟨hrR, hrC⟩
    obtain ⟨p, hp, q, hq, rfl⟩ := mem_sup_of_commute hCD.comm hrR
    have h1 : y * p * y⁻¹ * (y * q * y⁻¹) = p * q := by
      have := mem_centralizer_singleton_iff.1 hrC
      calc y * p * y⁻¹ * (y * q * y⁻¹) = y * (p * q) * y⁻¹ := by group
        _ = p * q := by rw [← this]; group
    obtain ⟨hp1, hq1⟩ := eq_of_mul_eq_of_inf_eq_bot hCD.inf (aconfigW_P_norm h y hyT p hp) hp
      (aconfigW_Q_norm h y hyT q hq) hq h1
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨hp, ?_⟩) (Subgroup.mem_sup_right ⟨hq, ?_⟩)
    · refine mem_centralizer_singleton_iff.2 ?_
      calc p * y = y * p * y⁻¹ * y := by rw [hp1]
        _ = y * p := by group
    · refine mem_centralizer_singleton_iff.2 ?_
      calc q * y = y * q * y⁻¹ * y := by rw [hq1]
        _ = y * q := by group
  have hcomm : ∀ u ∈ (T ⊓ K) ⊓ centralizer ({y} : Set G), ∀ v ∈ Q ⊓ centralizer ({y} : Set G),
      u * v = v * u := fun u hu v hv => hCD.comm u hu.1 v hv.1
  calc Nat.card ↥(((T ⊓ K) ⊔ Q) ⊓ centralizer ({y} : Set G))
      ≤ Nat.card ↥(((T ⊓ K) ⊓ centralizer ({y} : Set G)) ⊔ (Q ⊓ centralizer ({y} : Set G))) :=
        Subgroup.card_le_of_le hle
    _ ≤ Nat.card ↥((T ⊓ K) ⊓ centralizer ({y} : Set G)) *
          Nat.card ↥(Q ⊓ centralizer ({y} : Set G)) := card_sup_le_of_commute hcomm
    _ ≤ 2 * 2 := Nat.mul_le_mul (card_inf_centralizer_le_two hPcard hyP)
          (card_inf_centralizer_le_two h.card_Q hyQ)
    _ = 4 := by norm_num

theorem eq_one_or_eq_of_card_le_two [Finite G] {C : Subgroup G} (hC : Nat.card ↥C ≤ 2) {x c : G}
    (hx : x ∈ C) (hx1 : x ≠ 1) (hc : c ∈ C) : c = 1 ∨ c = x := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨hc1, hcx⟩ := hcon
  have hsub : (({1, x, c} : Finset G) : Set G) ⊆ (C : Set G) := by
    intro y hy
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · exact one_mem _
    · exact hx
    · exact hc
  have hcard3 : ({1, x, c} : Finset G).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp only [Finset.mem_singleton]
      exact fun h0 => hcx h0.symm
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h0 => hx1 h0.symm, fun h0 => hc1 h0.symm⟩
  have h3 : 3 ≤ Nat.card ↥C := by
    calc 3 = ({1, x, c} : Finset G).card := hcard3.symm
      _ = (({1, x, c} : Finset G) : Set G).ncard := (Set.ncard_coe_finset _).symm
      _ ≤ (C : Set G).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ = Nat.card ↥C := (Nat.card_coe_set_eq _).symm
  omega

theorem aconfigW_five_E_le_R [Finite G] {x : G} {K T Q S : Subgroup G} {a : G}
    (h : IsAConfigW 5 x K T Q S a) {y : G}
    (hTcases : ∀ t ∈ T, t ∈ (T ⊓ K) ⊔ Q ∨ ∃ r ∈ (T ⊓ K) ⊔ Q, t = r * y)
    (hCy : Nat.card ↥(((T ⊓ K) ⊔ Q) ⊓ centralizer ({y} : Set G)) ≤ 4)
    {E : Subgroup G} (hET : E ≤ T) (hEel : CFSG.IsElementaryAbelian 2 ↥E)
    (hE : 9 ≤ Nat.card ↥E) : E ≤ (T ⊓ K) ⊔ Q := by
  by_contra hnot
  obtain ⟨e, heE, heR⟩ := IsConcreteLE.not_le_iff_exists.1 hnot
  obtain ⟨hRel, hRcard⟩ := aconfigW_five_R h
  obtain ⟨hRc, hRs⟩ := forall_of_isElementaryAbelian hRel
  obtain ⟨hEc, hEs⟩ := forall_of_isElementaryAbelian hEel
  obtain ⟨r₀, hr₀, her₀⟩ : ∃ r₀ ∈ (T ⊓ K) ⊔ Q, e = r₀ * y := by
    rcases hTcases e (hET heE) with h1 | h1
    · exact absurd h1 heR
    · exact h1
  have hER : E ⊓ ((T ⊓ K) ⊔ Q) ≤ ((T ⊓ K) ⊔ Q) ⊓ centralizer ({y} : Set G) := by
    rintro r'' ⟨hr''E, hr''R⟩
    refine ⟨hr''R, mem_centralizer_singleton_iff.2 ?_⟩
    have h1 := hEc e heE r'' hr''E
    rw [her₀] at h1
    have h2 : r₀ * y * r'' = r₀ * (r'' * y) := by
      calc r₀ * y * r'' = r'' * (r₀ * y) := h1
        _ = r'' * r₀ * y := by group
        _ = r₀ * r'' * y := by rw [hRc r'' hr''R r₀ hr₀]
        _ = r₀ * (r'' * y) := by group
    have h3 : y * r'' = r'' * y := mul_left_cancel (by rw [← mul_assoc, h2])
    exact h3.symm
  have hEF : (E : Set G) ⊆ ((E ⊓ ((T ⊓ K) ⊔ Q) : Subgroup G) : Set G) ∪
      ((fun c => c * e) '' ((E ⊓ ((T ⊓ K) ⊔ Q) : Subgroup G) : Set G)) := by
    intro e' he'
    rcases hTcases e' (hET he') with h1 | ⟨r', hr', her'⟩
    · left
      exact ⟨he', h1⟩
    · right
      refine ⟨e' * e⁻¹, ⟨E.mul_mem he' (E.inv_mem heE), ?_⟩, by simp⟩
      have e1 : e' * e⁻¹ = r' * r₀⁻¹ := by
        rw [her', her₀]
        group
      rw [e1]
      exact Subgroup.mul_mem _ hr' (Subgroup.inv_mem _ hr₀)
  have hcardE : Nat.card ↥E ≤ 2 * Nat.card ↥(E ⊓ ((T ⊓ K) ⊔ Q)) := by
    have h1 : Nat.card ↥E = (E : Set G).ncard := Nat.card_coe_set_eq (E : Set G)
    have h2 : Nat.card ↥(E ⊓ ((T ⊓ K) ⊔ Q)) = ((E ⊓ ((T ⊓ K) ⊔ Q) : Subgroup G) : Set G).ncard :=
      Nat.card_coe_set_eq ((E ⊓ ((T ⊓ K) ⊔ Q) : Subgroup G) : Set G)
    have h3 : (E : Set G).ncard ≤ (((E ⊓ ((T ⊓ K) ⊔ Q) : Subgroup G) : Set G) ∪
        ((fun c => c * e) '' ((E ⊓ ((T ⊓ K) ⊔ Q) : Subgroup G) : Set G))).ncard :=
      Set.ncard_le_ncard hEF (Set.toFinite _)
    have h4 := Set.ncard_union_le ((E ⊓ ((T ⊓ K) ⊔ Q) : Subgroup G) : Set G)
      ((fun c => c * e) '' ((E ⊓ ((T ⊓ K) ⊔ Q) : Subgroup G) : Set G))
    have h5 : ((fun c => c * e) '' ((E ⊓ ((T ⊓ K) ⊔ Q) : Subgroup G) : Set G)).ncard ≤
        ((E ⊓ ((T ⊓ K) ⊔ Q) : Subgroup G) : Set G).ncard := Set.ncard_image_le (Set.toFinite _)
    omega
  have hle4 : Nat.card ↥(E ⊓ ((T ⊓ K) ⊔ Q)) ≤ 4 :=
    (Subgroup.card_le_of_le hER).trans hCy
  omega

theorem aconfigW_five_a_normalizes_R [Finite G] {x : G} {K T Q S : Subgroup G} {a : G}
    (h : IsAConfigW 5 x K T Q S a) {y : G}
    (hTcases : ∀ t ∈ T, t ∈ (T ⊓ K) ⊔ Q ∨ ∃ r ∈ (T ⊓ K) ⊔ Q, t = r * y)
    (hCy : Nat.card ↥(((T ⊓ K) ⊔ Q) ⊓ centralizer ({y} : Set G)) ≤ 4) :
    a ∈ normalizer ((((T ⊓ K) ⊔ Q : Subgroup G)) : Set G) := by
  obtain ⟨hRel, hRcard⟩ := aconfigW_five_R h
  have haNT' : ∀ t ∈ T, a⁻¹ * t * a ∈ T := by
    intro t ht
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem h.a_mem.2.1) t).1 ht
    simpa using this
  have hRT : (T ⊓ K) ⊔ Q ≤ T := sup_le inf_le_left h.Q_le_T
  have hle : conjugate ((T ⊓ K) ⊔ Q) a ≤ T := by
    intro u hu
    have h1 : a * u * a⁻¹ ∈ T := hRT (mem_conjugate_iff'.1 hu)
    have h2 := haNT' _ h1
    have e : a⁻¹ * (a * u * a⁻¹) * a = u := by group
    rwa [e] at h2
  have hE := aconfigW_five_E_le_R h hTcases hCy hle (isElementaryAbelian_conjugate hRel a)
    (by rw [card_conjugate', hRcard]; norm_num)
  have heq : conjugate ((T ⊓ K) ⊔ Q) a = (T ⊓ K) ⊔ Q :=
    Subgroup.eq_of_le_of_card_ge hE (le_of_eq (card_conjugate' _ _).symm)
  refine mem_normalizer_of_two_sided (fun w hw => ?_) (fun w hw => ?_)
  · have : w ∈ conjugate ((T ⊓ K) ⊔ Q) a := by rw [heq]; exact hw
    exact mem_conjugate_iff'.1 this
  · rw [← heq, mem_conjugate_iff']
    have e : a * (a⁻¹ * w * a) * a⁻¹ = w := by group
    rw [e]
    exact hw

theorem aconfigW_five_NSQ [Finite G] {x : G} {K T Q S : Subgroup G} {a : G}
    (h : IsAConfigW 5 x K T Q S a) {y : G} (hyT : y ∈ T) (hyQ : ∃ q ∈ Q, y * q ≠ q * y) :
    ∀ n ∈ S, n ∈ normalizer (Q : Set G) → n ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxQ := h.x_mem_Q
  have hx1 := h.x_ne_one
  have hxT : ∀ t ∈ T, x * t = t * x := fun t ht =>
    (mem_centralizer_singleton_iff.1 (h.T_le_C ht)).symm
  have hQn := aconfigW_Q_norm h
  set H : Subgroup G := S ⊓ normalizer (Q : Set G) with hHdef
  have hH2 : IsPGroup 2 ↥H := h.sylowS.isPGroup.to_le inf_le_left
  let ρ : ↥H →* MulAut ↥Q :=
    (Stage1.Thm6.Sec13.actHom Q).comp (Subgroup.inclusion (inf_le_right : H ≤ normalizer (Q : Set G)))
  let _inst : MulAction ↥H ↥Q := MulAction.compHom ↥Q ρ
  have hsmul : ∀ (g : ↥H) (q : ↥Q), ((g • q : ↥Q) : G) = (g : G) * (q : G) * (g : G)⁻¹ :=
    fun g q => rfl
  have hyS : y ∈ S := h.T_lt_S.le hyT
  have hyN : y ∈ normalizer (Q : Set G) :=
    mem_normalizer_of_two_sided (fun w hw => hQn y hyT w hw) (fun w hw => by
      simpa using hQn y⁻¹ (T.inv_mem hyT) w hw)
  have hmod := IsPGroup.card_modEq_card_fixedPoints hH2 (α := ↥Q)
  have hxF : (⟨x, hxQ⟩ : ↥Q) ∈ MulAction.fixedPoints ↥H ↥Q := by
    by_contra hxF
    have hC := card_inf_centralizer_le_two h.card_Q hyQ
    have hxC : x ∈ Q ⊓ centralizer ({y} : Set G) :=
      ⟨hxQ, mem_centralizer_singleton_iff.2 (hxT y hyT)⟩
    have hFeq : (MulAction.fixedPoints ↥H ↥Q) = {1} := by
      ext q
      constructor
      · intro hq
        have hqy : (⟨y, hyS, hyN⟩ : ↥H) • q = q := hq ⟨y, hyS, hyN⟩
        have hqy' : y * (q : G) * y⁻¹ = q := by
          have := congrArg Subtype.val hqy
          rwa [hsmul] at this
        have hqC : (q : G) ∈ Q ⊓ centralizer ({y} : Set G) := by
          refine ⟨q.2, mem_centralizer_singleton_iff.2 ?_⟩
          calc (q : G) * y = (y * (q : G) * y⁻¹) * y := by rw [hqy']
            _ = y * q := by group
        rcases eq_one_or_eq_of_card_le_two hC hxC hx1 hqC with h1 | h1
        · exact Set.mem_singleton_iff.2 (Subtype.ext h1)
        · exfalso
          apply hxF
          have : q = ⟨x, hxQ⟩ := Subtype.ext h1
          rw [← this]
          exact hq
      · intro hq
        rw [Set.mem_singleton_iff] at hq
        rw [hq]
        intro g
        exact Subtype.ext (by rw [hsmul]; simp)
    have hcard1 : Nat.card ↥(MulAction.fixedPoints ↥H ↥Q) = 1 := by
      rw [hFeq]
      simp
    rw [hcard1, h.card_Q] at hmod
    have := hmod
    unfold Nat.ModEq at this
    omega
  intro n hnS hnN
  have hfix := hxF ⟨n, hnS, hnN⟩
  have hfix' : n * x * n⁻¹ = x := by
    have := congrArg Subtype.val hfix
    rwa [hsmul] at this
  exact aconfigW_cent6 h x hxQ hx1 hxT n hnS (by
    calc n * x = (n * x * n⁻¹) * n := by group
      _ = x * n := by rw [hfix'])

theorem card_le_two_mul_of_cover [Finite G] {E F : Subgroup G} {e : G}
    (hcov : ∀ e' ∈ E, e' ∈ F ∨ e' * e⁻¹ ∈ F) : Nat.card ↥E ≤ 2 * Nat.card ↥F := by
  have hEF : (E : Set G) ⊆ (F : Set G) ∪ ((fun c => c * e) '' (F : Set G)) := by
    intro e' he'
    rcases hcov e' he' with h1 | h1
    · exact Or.inl h1
    · exact Or.inr ⟨e' * e⁻¹, h1, by simp⟩
  have h1 : Nat.card ↥E = (E : Set G).ncard := Nat.card_coe_set_eq (E : Set G)
  have h2 : Nat.card ↥F = (F : Set G).ncard := Nat.card_coe_set_eq (F : Set G)
  have h3 : (E : Set G).ncard ≤ ((F : Set G) ∪ ((fun c => c * e) '' (F : Set G))).ncard :=
    Set.ncard_le_ncard hEF (Set.toFinite _)
  have h4 := Set.ncard_union_le (F : Set G) ((fun c => c * e) '' (F : Set G))
  have h5 : ((fun c => c * e) '' (F : Set G)).ncard ≤ (F : Set G).ncard :=
    Set.ncard_image_le (Set.toFinite _)
  omega

theorem aconfigW_five_S1_cases [Finite G] {x : G} {K T Q S : Subgroup G} {a : G}
    (h : IsAConfigW 5 x K T Q S a)
    (horbit : ∀ g ∈ normalizer ((((T ⊓ K) ⊔ Q : Subgroup G)) : Set G),
      conjugate Q g = Q ∨ conjugate Q g = T ⊓ K)
    (hNSQ : ∀ n ∈ S, n ∈ normalizer (Q : Set G) → n ∈ T) (hQa : conjugate Q a = T ⊓ K) :
    ∀ s ∈ S, s ∈ normalizer ((((T ⊓ K) ⊔ Q : Subgroup G)) : Set G) →
      (s ∈ T ∧ conjugate Q s = Q) ∨ (s * a⁻¹ ∈ T ∧ conjugate Q s = T ⊓ K) := by
  intro s hsS hsN
  rcases horbit s hsN with hs1 | hs1
  · left
    refine ⟨hNSQ s hsS ?_, hs1⟩
    refine mem_normalizer_of_two_sided (fun w hw => ?_) (fun w hw => ?_)
    · have : w ∈ conjugate Q s := by rw [hs1]; exact hw
      exact mem_conjugate_iff'.1 this
    · have : s⁻¹ * w * s ∈ conjugate Q s := by
        rw [mem_conjugate_iff']
        have e : s * (s⁻¹ * w * s) * s⁻¹ = w := by group
        rw [e]
        exact hw
      rwa [hs1] at this
  · right
    refine ⟨?_, hs1⟩
    have hsa : conjugate Q s = conjugate Q a := by rw [hs1, hQa]
    have hn : a * s⁻¹ ∈ normalizer (Q : Set G) := by
      refine mem_normalizer_of_two_sided (fun w hw => ?_) (fun w hw => ?_)
      · have h1 : s⁻¹ * w * s ∈ conjugate Q s := by
          rw [mem_conjugate_iff']
          have e : s * (s⁻¹ * w * s) * s⁻¹ = w := by group
          rw [e]
          exact hw
        rw [hsa, mem_conjugate_iff'] at h1
        have e : a * s⁻¹ * w * (a * s⁻¹)⁻¹ = a * (s⁻¹ * w * s) * a⁻¹ := by group
        rw [e]
        exact h1
      · have h1 : a⁻¹ * w * a ∈ conjugate Q a := by
          rw [mem_conjugate_iff']
          have e : a * (a⁻¹ * w * a) * a⁻¹ = w := by group
          rw [e]
          exact hw
        rw [← hsa, mem_conjugate_iff'] at h1
        have e : (a * s⁻¹)⁻¹ * w * (a * s⁻¹) = s * (a⁻¹ * w * a) * s⁻¹ := by group
        rw [e]
        exact h1
    have hmem : a * s⁻¹ ∈ T :=
      hNSQ _ (S.mul_mem h.a_mem.1 (S.inv_mem hsS)) hn
    have := T.inv_mem hmem
    simpa using this

theorem aconfigW_five_E_le_R_S1 [Finite G] {x : G} {K T Q S : Subgroup G} {a : G}
    (h : IsAConfigW 5 x K T Q S a) {y : G}
    (hTcases : ∀ t ∈ T, t ∈ (T ⊓ K) ⊔ Q ∨ ∃ r ∈ (T ⊓ K) ⊔ Q, t = r * y)
    (hCy : Nat.card ↥(((T ⊓ K) ⊔ Q) ⊓ centralizer ({y} : Set G)) ≤ 4)
    (hyT : y ∈ T)
    (hS1c : ∀ s ∈ S, s ∈ normalizer ((((T ⊓ K) ⊔ Q : Subgroup G)) : Set G) →
      (s ∈ T ∧ conjugate Q s = Q) ∨ (s * a⁻¹ ∈ T ∧ conjugate Q s = T ⊓ K))
    {E : Subgroup G} (hE : ∀ e ∈ E, e ∈ S ∧ e ∈ normalizer ((((T ⊓ K) ⊔ Q : Subgroup G)) : Set G))
    (hEel : CFSG.IsElementaryAbelian 2 ↥E) (hE13 : 13 ≤ Nat.card ↥E) : E ≤ (T ⊓ K) ⊔ Q := by
  classical
  by_contra hnot
  obtain ⟨hRel, hRcard⟩ := aconfigW_five_R h
  obtain ⟨hRc, hRs⟩ := forall_of_isElementaryAbelian hRel
  obtain ⟨hEc, hEs⟩ := forall_of_isElementaryAbelian hEel
  have hCD := aconfigW_five_commDisj h
  by_cases hET : E ≤ T
  · exact hnot (aconfigW_five_E_le_R h hTcases hCy hET hEel (by omega))
  · obtain ⟨e₂, he₂E, he₂T⟩ := IsConcreteLE.not_le_iff_exists.1 hET
    have he₂ : e₂ * a⁻¹ ∈ T ∧ conjugate Q e₂ = T ⊓ K := by
      rcases hS1c e₂ (hE e₂ he₂E).1 (hE e₂ he₂E).2 with h1 | h1
      · exact absurd h1.1 he₂T
      · exact h1
    have hvQ : ∀ v ∈ E, v ∈ Q → v = 1 := by
      intro v hvE hvQ
      have hc := hEc e₂ he₂E v hvE
      have h1 : e₂⁻¹ * v * e₂ ∈ conjugate Q e₂ := by
        rw [mem_conjugate_iff']
        have e : e₂ * (e₂⁻¹ * v * e₂) * e₂⁻¹ = v := by group
        rw [e]
        exact hvQ
      rw [he₂.2] at h1
      have h2 : e₂⁻¹ * v * e₂ = v := by
        calc e₂⁻¹ * v * e₂ = e₂⁻¹ * (v * e₂) := by group
          _ = e₂⁻¹ * (e₂ * v) := by rw [← hc]
          _ = v := by group
      rw [h2] at h1
      have h3 : v ∈ (T ⊓ K) ⊓ Q := ⟨h1, hvQ⟩
      rw [hCD.inf, Subgroup.mem_bot] at h3
      exact h3
    have hcovE : ∀ e' ∈ E, e' ∈ E ⊓ T ∨ e' * e₂⁻¹ ∈ E ⊓ T := by
      intro e' he'
      rcases hS1c e' (hE e' he').1 (hE e' he').2 with h1 | h1
      · exact Or.inl ⟨he', h1.1⟩
      · right
        refine ⟨E.mul_mem he' (E.inv_mem he₂E), ?_⟩
        have e : e' * e₂⁻¹ = (e' * a⁻¹) * (e₂ * a⁻¹)⁻¹ := by group
        rw [e]
        exact T.mul_mem h1.1 (T.inv_mem he₂.1)
    have hF7 : 7 ≤ Nat.card ↥(E ⊓ T) := by
      have := card_le_two_mul_of_cover hcovE
      omega
    have hFE : E ⊓ T ≤ E := inf_le_left
    by_cases hFR : E ⊓ T ≤ (T ⊓ K) ⊔ Q
    ·
      have hdisj : (E ⊓ T) ⊓ Q ≠ ⊥ := by
        intro hbot
        have hcomm : ∀ u ∈ E ⊓ T, ∀ v ∈ Q, u * v = v * u := fun u hu v hv =>
          hRc u (hFR hu) v (Subgroup.mem_sup_right hv)
        have h1 := card_sup_of_commute_of_disjoint hcomm hbot
        have h2 : Nat.card ↥((E ⊓ T) ⊔ Q) ≤ 16 := by
          rw [← hRcard]
          exact Subgroup.card_le_of_le (sup_le hFR (le_sup_right))
        rw [h1, h.card_Q] at h2
        omega
      obtain ⟨⟨v, hv⟩, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hdisj
      exact hv1 (Subtype.ext (hvQ v (hFE hv.1) hv.2))
    ·
      obtain ⟨f, hfF, hfR⟩ := IsConcreteLE.not_le_iff_exists.1 hFR
      obtain ⟨r_f, hr_f, hfy⟩ : ∃ r ∈ (T ⊓ K) ⊔ Q, f = r * y := by
        rcases hTcases f hfF.2 with h1 | h1
        · exact absurd h1 hfR
        · exact h1
      have hFRC : (E ⊓ T) ⊓ ((T ⊓ K) ⊔ Q) ≤ ((T ⊓ K) ⊔ Q) ⊓ centralizer ({y} : Set G) := by
        rintro r'' ⟨hr''F, hr''R⟩
        refine ⟨hr''R, mem_centralizer_singleton_iff.2 ?_⟩
        have h1 := hEc f (hFE hfF) r'' (hFE hr''F)
        rw [hfy] at h1
        have h2 : r_f * y * r'' = r_f * (r'' * y) := by
          calc r_f * y * r'' = r'' * (r_f * y) := h1
            _ = r'' * r_f * y := by group
            _ = r_f * r'' * y := by rw [hRc r'' hr''R r_f hr_f]
            _ = r_f * (r'' * y) := by group
        have h3 : y * r'' = r'' * y := mul_left_cancel (by rw [← mul_assoc, h2])
        exact h3.symm
      have hcovF : ∀ f' ∈ E ⊓ T, f' ∈ (E ⊓ T) ⊓ ((T ⊓ K) ⊔ Q) ∨
          f' * f⁻¹ ∈ (E ⊓ T) ⊓ ((T ⊓ K) ⊔ Q) := by
        intro f' hf'
        rcases hTcases f' hf'.2 with h1 | ⟨r', hr', hf'y⟩
        · exact Or.inl ⟨hf', h1⟩
        · right
          refine ⟨(E ⊓ T).mul_mem hf' ((E ⊓ T).inv_mem hfF), ?_⟩
          have e1 : f' * f⁻¹ = r' * r_f⁻¹ := by
            rw [hf'y, hfy]
            group
          rw [e1]
          exact Subgroup.mul_mem _ hr' (Subgroup.inv_mem _ hr_f)
      have hFR8 : Nat.card ↥(E ⊓ T) ≤ 2 * Nat.card ↥((E ⊓ T) ⊓ ((T ⊓ K) ⊔ Q)) :=
        card_le_two_mul_of_cover hcovF
      have hle4 : Nat.card ↥((E ⊓ T) ⊓ ((T ⊓ K) ⊔ Q)) ≤ 4 :=
        (Subgroup.card_le_of_le hFRC).trans hCy
      have heq : (E ⊓ T) ⊓ ((T ⊓ K) ⊔ Q) = ((T ⊓ K) ⊔ Q) ⊓ centralizer ({y} : Set G) :=
        Subgroup.eq_of_le_of_card_ge hFRC (by omega)
      have hx : x ∈ ((T ⊓ K) ⊔ Q) ⊓ centralizer ({y} : Set G) :=
        ⟨Subgroup.mem_sup_right h.x_mem_Q, mem_centralizer_singleton_iff.2
          ((mem_centralizer_singleton_iff.1 (h.T_le_C hyT)).symm)⟩
      rw [← heq] at hx
      exact h.x_ne_one (hvQ x (hFE hx.1) h.x_mem_Q)

theorem aconfigW_five_fusion_two_of_orbit [Finite G] {x : G} {K T Q S : Subgroup G} {a : G}
    (h : IsAConfigW 5 x K T Q S a)
    (horbit : ∀ g ∈ normalizer ((((T ⊓ K) ⊔ Q : Subgroup G)) : Set G),
      conjugate Q g = Q ∨ conjugate Q g = T ⊓ K) :
    a * x * a⁻¹ ∈ T ⊓ K ∧ S = T ⊔ zpowers a := by
  obtain ⟨y, hyT, hyy, hyR, hTcases, q₀, hq₀, hyq₀⟩ := aconfigW_five_y h
  obtain ⟨p, hp, hyp⟩ := aconfigW_five_y_nontriv h hyT hyR
  have hCy := aconfigW_five_card_centralizer_R h hyT ⟨p, hp, hyp⟩ ⟨q₀, hq₀, hyq₀⟩
  have haR := aconfigW_five_a_normalizes_R h hTcases hCy
  have hQinf := aconfigW_Q_inf_conj h
  obtain ⟨hRel, hRcard⟩ := aconfigW_five_R h
  have hQa : conjugate Q a = T ⊓ K := by
    rcases horbit a haR with h1 | h1
    · exfalso
      rw [h1, inf_idem] at hQinf
      have := h.card_Q
      rw [hQinf, Subgroup.card_bot] at this
      omega
    · exact h1
  have hconj1 : a * x * a⁻¹ ∈ T ⊓ K := by
    have h1 : a⁻¹ * x * a ∈ conjugate Q a := by
      rw [mem_conjugate_iff']
      have e : a * (a⁻¹ * x * a) * a⁻¹ = x := by group
      rw [e]
      exact h.x_mem_Q
    rw [hQa] at h1
    rw [← h.inv_conj_x]
    exact h1
  have hNSQ := aconfigW_five_NSQ h hyT ⟨q₀, hq₀, hyq₀⟩
  have hS1c := aconfigW_five_S1_cases h horbit hNSQ hQa
  have hRT : (T ⊓ K) ⊔ Q ≤ T := sup_le inf_le_left h.Q_le_T
  have hSN : ∀ s ∈ S, s ∈ normalizer ((((T ⊓ K) ⊔ Q : Subgroup G)) : Set G) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨s0, hs0S, hs0N⟩ := hcon
    have hne : S ⊓ normalizer ((((T ⊓ K) ⊔ Q : Subgroup G)) : Set G) ≠ S := by
      intro h0
      have : s0 ∈ S ⊓ normalizer ((((T ⊓ K) ⊔ Q : Subgroup G)) : Set G) := by rw [h0]; exact hs0S
      exact hs0N this.2
    obtain ⟨n, hnS, hnN, hnnorm⟩ :=
      Sec4Core.exists_mem_normalizer_not_mem h.sylowS.isPGroup inf_le_left hne
    apply hnN
    refine ⟨hnS, ?_⟩
    have hRN : (T ⊓ K) ⊔ Q ≤ S ⊓ normalizer ((((T ⊓ K) ⊔ Q : Subgroup G)) : Set G) :=
      le_inf (hRT.trans h.T_lt_S.le) Subgroup.le_normalizer
    have hE : conjugate ((T ⊓ K) ⊔ Q) n⁻¹ ≤ (T ⊓ K) ⊔ Q := by
      refine aconfigW_five_E_le_R_S1 h hTcases hCy hyT hS1c
        (E := conjugate ((T ⊓ K) ⊔ Q) n⁻¹) (fun u hu => ?_)
        (isElementaryAbelian_conjugate hRel n⁻¹) (by rw [card_conjugate', hRcard]; norm_num)
      rw [mem_conjugate_iff'] at hu
      have h1 := (hnnorm _ (hRN hu)).1
      have e : n * (n⁻¹ * u * n⁻¹⁻¹) * n⁻¹ = u := by group
      rw [e] at h1
      exact h1
    have heq : conjugate ((T ⊓ K) ⊔ Q) n⁻¹ = (T ⊓ K) ⊔ Q :=
      Subgroup.eq_of_le_of_card_ge hE (le_of_eq (card_conjugate' _ _).symm)
    refine mem_normalizer_of_two_sided (fun w hw => ?_) (fun w hw => ?_)
    · have : n * w * n⁻¹ ∈ conjugate ((T ⊓ K) ⊔ Q) n⁻¹ := by
        rw [mem_conjugate_iff']
        have e : n⁻¹ * (n * w * n⁻¹) * n⁻¹⁻¹ = w := by group
        rw [e]
        exact hw
      rwa [heq] at this
    · rw [← heq] at hw
      have := mem_conjugate_iff'.1 hw
      simpa using this
  refine ⟨hconj1, le_antisymm (fun s hs => ?_)
    (sup_le h.T_lt_S.le (zpowers_le.2 h.a_mem.1))⟩
  rcases hS1c s hs (hSN s hs) with ⟨hsT, -⟩ | ⟨hsT, -⟩
  · exact Subgroup.mem_sup_left hsT
  · have e : s = (s * a⁻¹) * a := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hsT)
      (Subgroup.mem_sup_right (mem_zpowers a))

@[expose] def B_P46_orbit : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x : G) (K T Q S : Subgroup G) (a : G),
    IsAConfigW 5 x K T Q S a →
      ∀ g ∈ normalizer ((((T ⊓ K) ⊔ Q : Subgroup G)) : Set G),
        conjugate Q g = Q ∨ conjugate Q g = T ⊓ K

theorem b_L114_fusion5_of_orbit (horb : B_P46_orbit) : B_L114_fusion5 := by
  intro G _ _ hG x K T Q S a h
  exact aconfigW_five_fusion_two_of_orbit h (horb G hG x K T Q S a h)

end CFSG.GH74.GLS.C3.Layer1.Bk
