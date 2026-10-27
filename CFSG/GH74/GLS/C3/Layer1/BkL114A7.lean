module

public import CFSG.GH74.GLS.C3.Layer1.BkL114
public import CFSG.GH74.GLS.C3.Layer1.BkL114Cent
public import CFSG.GH74.GLS.C3.Layer1.BkS4Wr
public import CFSG.GH74.GLS.C3.Layer1.BkA7Cent
public import CFSG.GH74.GLS.Bg.Rank

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.C3.Layer1.Back
open scoped commutatorElement

variable {G : Type} [Group G]

theorem commDisj_inf_CxK [Finite G] {x : G} {K T : Subgroup G} (hT2 : IsPGroup 2 ↥T)
    (hcen : CenterlessBar K) : CommDisj (T ⊓ K) (T ⊓ CxK x K) := by
  have hbot := Setup91.inf_pPrimeCoreOf_eq_bot K hT2
  refine ⟨fun p hp q hq => ?_, ?_⟩
  · have h1 : ⁅p, q⁆ ∈ pPrimeCoreOf 2 K := hq.2.2.2.2 p hp.2
    have h2 : ⁅p, q⁆ ∈ T := by
      rw [commutatorElement_def]
      exact T.mul_mem (T.mul_mem (T.mul_mem hp.1 hq.1) (T.inv_mem hp.1)) (T.inv_mem hq.1)
    have h3 : ⁅p, q⁆ ∈ T ⊓ pPrimeCoreOf 2 K := ⟨h2, h1⟩
    rw [hbot, Subgroup.mem_bot] at h3
    exact commutatorElement_eq_one_iff_mul_comm.1 h3
  · refine eq_bot_iff.2 fun p hp => ?_
    have hpO : p ∈ pPrimeCoreOf 2 K :=
      mem_pPrimeCoreOf_of_commutators hcen hp.1.2 (fun k hk => hp.2.2.2.2.2 k hk)
    have h3 : p ∈ T ⊓ pPrimeCoreOf 2 K := ⟨hp.1.1, hpO⟩
    rw [hbot] at h3
    exact h3

theorem aconfigW_inf_sylow [Finite G] {n : ℕ} {x : G} {K T Q S : Subgroup G} {a : G}
    (h : IsAConfigW n x K T Q S a) : IsSylowOf 2 (T ⊓ K) K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCnorm : centralizer ({x} : Set G) ≤ normalizer (K : Set G) := fun c hc =>
    mem_normalizer_of_two_sided (fun w hw => h.normalInC c hc w hw) (fun w hw => by
      simpa using h.normalInC c⁻¹ ((centralizer ({x} : Set G)).inv_mem hc) w hw)
  exact h.sylowT.inf_of_le_normalizer h.K_le_C hCnorm

theorem card_T_le_sixtyfour_of_aconfigW_seven [Finite G] {x : G} {K T Q S : Subgroup G}
    {a : G} (h : IsAConfigW 7 x K T Q S a) : Nat.card ↥T ≤ 64 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : IsPGroup 2 ↥T := h.sylowT.isPGroup
  have hTC : T ≤ centralizer ({x} : Set G) := h.T_le_C
  obtain ⟨ψ, hker⟩ := h.quotientType
  have hQ4' : Nat.card ↥(T ⊓ CMK (centralizer ({x} : Set G)) K) = 4 := by
    have : T ⊓ CMK (centralizer ({x} : Set G)) K = Q := h.hQ.symm
    rw [this]
    exact h.card_Q
  exact card_le_sixtyfour_of_alt7 hT2 hTC ψ hker hQ4'

theorem sec4Core_of_aconfigW_seven [Finite G] (hr : pRank 2 G ≤ 4) {x : G} {K T Q S : Subgroup G}
    {a : G} (h : IsAConfigW 7 x K T Q S a) :
    Sec4Core a (T ⊓ K) Q T S ∧ Nat.card ↥T ≤ 64 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e7⟩ := h.kbar
  have hT2 : IsPGroup 2 ↥T := h.sylowT.isPGroup
  have hS2 : IsPGroup 2 ↥S := h.sylowS.isPGroup
  have hTC : T ≤ centralizer ({x} : Set G) := h.T_le_C
  have hKN := h.normalInC
  have hQ := h.hQ
  have hCnorm : centralizer ({x} : Set G) ≤ normalizer (K : Set G) := fun c hc =>
    mem_normalizer_of_two_sided (fun w hw => hKN c hc w hw) (fun w hw => by
      simpa using hKN c⁻¹ ((centralizer ({x} : Set G)).inv_mem hc) w hw)
  have hP : IsSylowOf 2 (T ⊓ K) K := aconfigW_inf_sylow h
  have hPD8 : IsD8 (T ⊓ K) := isD8_of_inf_alt7 hT2 hP e7
  have hCD := commDisj_inf_CxK (x := x) hT2 (centerlessBar_of_A7 ⟨e7⟩)
  rw [← hQ] at hCD
  have hPn : ∀ t ∈ T, ∀ p ∈ T ⊓ K, t * p * t⁻¹ ∈ T ⊓ K := fun t ht p hp =>
    ⟨T.mul_mem (T.mul_mem ht hp.1) (T.inv_mem ht), hKN t (hTC ht) p hp.2⟩
  have hQn : ∀ t ∈ T, ∀ q ∈ Q, t * q * t⁻¹ ∈ Q := by
    intro t ht q hq
    have hNxK : t ∈ NxK x K := ⟨hTC ht, hCnorm (hTC ht)⟩
    rw [hQ] at hq ⊢
    refine ⟨T.mul_mem (T.mul_mem ht hq.1) (T.inv_mem ht), ?_⟩
    exact (Subgroup.mem_normalizer_iff.1 (NxK_le_normalizer_CxK x K hNxK) q).1 hq.2
  have hT64 : Nat.card ↥T ≤ 64 := card_T_le_sixtyfour_of_aconfigW_seven h
  have hxQ : x ∈ Q := h.x_mem_Q
  have hcent6 := aconfigW_cent6 h
  have hrank4 : ∀ E : Subgroup G, CFSG.IsElementaryAbelian 2 ↥E → Nat.card ↥E ≤ 16 := by
    intro E hE
    have h1 := card_eq_two_pow_pRank hE
    have h2 : pRank 2 ↥E ≤ pRank 2 G := Bg.pRank_subgroup_le one_lt_two E
    have h3 := hr
    rw [h1]
    calc 2 ^ pRank 2 ↥E ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 16 := by norm_num
  refine ⟨?_, hT64⟩
  exact
    { T_pgroup := hT2
      S_pgroup := hS2
      T_le_S := h.T_lt_S.le
      a_mem := h.a_mem.1
      a_mem_norm := h.a_mem.2.1
      a_not_mem := h.a_mem.2.2.1
      a_sq_mem := by rw [← sq]; exact h.a_mem.2.2.2
      P_le := inf_le_left
      Q_le := h.Q_le_T
      P_norm := hPn
      Q_norm := hQn
      P_d8 := hPD8
      Q_shape := Or.inl h.elemQ
      Q_card := h.card_Q
      PQ_comm := hCD.comm
      PQ_disj := hCD.inf
      cent6 := hcent6
      rank4 := hrank4 }

theorem aconfigW_seven_fusion_two [Finite G] (hr : pRank 2 G ≤ 4) {x : G} {K T Q S : Subgroup G}
    {a : G} (h : IsAConfigW 7 x K T Q S a) :
    a * x * a⁻¹ ∈ T ⊓ K ∧ S = T ⊔ zpowers a := by
  obtain ⟨hcore, hT64⟩ := sec4Core_of_aconfigW_seven hr h
  have hTeq := hcore.T_eq_sup_of_card_le hT64
  have hxQ := h.x_mem_Q
  have hx1 := h.x_ne_one
  have hxx : x * x = 1 := by rw [← sq]; exact h.x_sq
  have hxT : ∀ t ∈ T, x * t = t * x := fun t ht =>
    (mem_centralizer_singleton_iff.1 (h.T_le_C ht)).symm
  obtain ⟨z, hzP, hz1, hzc, hxPa, hza⟩ := hcore.exists_swap_of_card_le hT64 hxQ hx1 hxT
  have hcentx := hcore.cent6 x hxQ hx1 hxT
  have hS1 : ∀ n ∈ S, n ∈ normalizer (T : Set G) → n ∈ T ∨ a⁻¹ * n ∈ T := fun n hn hnN =>
    hcore.mem_T_or_of_normalizer hTeq hzP hz1 hzc hxPa hx1 hxx hxT hza hcentx hn hnN
  have hScases := hcore.S_cases hTeq hS1
  refine ⟨hza ▸ hzP, le_antisymm ?_ (sup_le h.T_lt_S.le (zpowers_le.2 h.a_mem.1))⟩
  intro s hs
  rcases hScases s hs with hsT | hsT
  · exact Subgroup.mem_sup_left hsT
  · have e : s = a * (a⁻¹ * s) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (mem_zpowers a)) (Subgroup.mem_sup_left hsT)

theorem aconfigW_seven_odd [Finite G] (hr : pRank 2 G ≤ 4) {x : G} {K T Q S : Subgroup G} {a : G}
    (h : IsAConfigW 7 x K T Q S a) :
    ∀ u ∈ centralizer ((Ysub x K T a : Subgroup G) : Set G), Odd (orderOf u) → u ∈ CxK x K := by
  intro u hu hodd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hcore, hT64⟩ := sec4Core_of_aconfigW_seven hr h
  obtain ⟨e7⟩ := h.kbar
  have hT2 : IsPGroup 2 ↥T := h.sylowT.isPGroup
  have hTC : T ≤ centralizer ({x} : Set G) := h.T_le_C
  have hTeq := hcore.T_eq_sup_of_card_le hT64
  have hxQ := h.x_mem_Q
  have hx1 := h.x_ne_one
  have hxx : x * x = 1 := by rw [← sq]; exact h.x_sq
  have hxT : ∀ t ∈ T, x * t = t * x := fun t ht =>
    (mem_centralizer_singleton_iff.1 (hTC ht)).symm
  obtain ⟨z, hzP, hz1, hzc, hxPa, hza⟩ := hcore.exists_swap_of_card_le hT64 hxQ hx1 hxT
  have hPaT : conjugate (T ⊓ K) a ≤ T := hcore.conj_le hcore.P_le
  have hT64' : Nat.card ↥T = 64 :=
    (Nat.card_congr (MulEquiv.subgroupCongr hTeq).toEquiv).trans hcore.card_P_sup_conj
  obtain ⟨ψ, hker, hψK⟩ :=
    lemma113d_alt h.K_le_C h.normalInC (n := 7) (by norm_num) (by norm_num) e7
  obtain ⟨ι, hιinj, hιcard, hι⟩ := inf_embeds_alt7 hT2 (aconfigW_inf_sylow h) e7
  have hker' : ψ.ker =
      (CMK (centralizer ({x} : Set G)) K).subgroupOf (centralizer ({x} : Set G)) := hker
  have hQ4' : Nat.card ↥(T ⊓ CMK (centralizer ({x} : Set G)) K) = 4 := by
    have : T ⊓ CMK (centralizer ({x} : Set G)) K = Q := h.hQ.symm
    rw [this]
    exact h.card_Q
  have hψι : ∀ (p : G) (hp : p ∈ T ⊓ K), ψ ⟨p, hTC hp.1⟩ =
      ((ι ⟨p, hp⟩ : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) := by
    intro p hp
    rw [hι ⟨p, hp⟩]
    exact hψK p hp.2
  have hcommψ : ∀ (v w : G) (hv : v ∈ centralizer ({x} : Set G)) (hw : w ∈ centralizer ({x} : Set G)),
      v * w = w * v → ψ ⟨v, hv⟩ * ψ ⟨w, hw⟩ = ψ ⟨w, hw⟩ * ψ ⟨v, hv⟩ := by
    intro v w hv hw hvw
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hvw
  have hxz : x = a * z * a⁻¹ := by
    have := h.conj_conj_x
    rw [hza] at this
    exact this.symm
  have hxY : x ∈ (Ysub x K T a : Subgroup G) := by
    unfold Ysub
    exact Subgroup.mem_sup_left ⟨z, hzP, by rw [hxz]; rfl⟩
  have hzY : z ∈ (Ysub x K T a : Subgroup G) := by
    unfold Ysub
    rw [← hza]
    exact Subgroup.mem_sup_right (mem_zpowers _)
  have hfY : ∀ f ∈ conjugate (T ⊓ K) a, f ∈ (Ysub x K T a : Subgroup G) := by
    intro f hf
    unfold Ysub
    refine Subgroup.mem_sup_left ⟨a⁻¹ * f * a, hcore.conj_inv_mem hcore.P_norm hf, ?_⟩
    show a * (a⁻¹ * f * a) * a⁻¹ = f
    group
  have hux : x * u = u * x := mem_centralizer_iff.1 hu x hxY
  have huz : z * u = u * z := mem_centralizer_iff.1 hu z hzY
  have huf : ∀ f ∈ conjugate (T ⊓ K) a, f * u = u * f := fun f hf =>
    mem_centralizer_iff.1 hu f (hfY f hf)
  have huC : u ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.2 hux.symm
  have hzC : z ∈ centralizer ({x} : Set G) := hTC (hcore.P_le hzP)
  have hz2 : z * z = 1 := by
    rw [← hza]
    calc a * x * a⁻¹ * (a * x * a⁻¹) = a * (x * x) * a⁻¹ := by group
      _ = 1 := by rw [hxx]; group
  have hρ1 : ψ ⟨z, hzC⟩ ≠ 1 := by
    intro h1
    have hmem : (⟨z, hzC⟩ : ↥(centralizer ({x} : Set G))) ∈ ψ.ker := h1
    rw [hker', Subgroup.mem_subgroupOf] at hmem
    have hodd' := h.K_inf_CxK_odd (by norm_num) hzP.2 hmem
    have hzord : orderOf z = 2 := orderOf_eq_prime (by rw [sq]; exact hz2) hz1
    rw [hzord] at hodd'
    exact (Nat.not_even_iff_odd.2 hodd') even_two
  have hexists : ∃ f : G, ∃ hfC : f ∈ centralizer ({x} : Set G), f ∈ conjugate (T ⊓ K) a ∧
      ∀ y ∈ ι.range, (y : Equiv.Perm (Fin 7)) ≠ ψ ⟨f, hfC⟩ := by
    by_contra hcon
    push Not at hcon
    set X' : Subgroup (Equiv.Perm (Fin 7)) := ι.range.map (alternatingGroup (Fin 7)).subtype
      with hX'
    have hX'card : Nat.card ↥X' = 8 := by
      rw [hX', Subgroup.card_map_of_injective (alternatingGroup (Fin 7)).subtype_injective]
      exact hιcard
    have hφle : (ψ.comp (Subgroup.inclusion hTC)).range ≤ X' := by
      rintro _ ⟨t, rfl⟩
      have ht : (t : G) ∈ (T ⊓ K) ⊔ conjugate (T ⊓ K) a := hTeq ▸ t.2
      obtain ⟨p, hp, f, hf, hpf⟩ := mem_sup_of_commute hcore.comm_P_conj ht
      have hfC : f ∈ centralizer ({x} : Set G) := hTC (hPaT hf)
      have hpC : p ∈ centralizer ({x} : Set G) := hTC hp.1
      have e1 : (⟨(t : G), hTC t.2⟩ : ↥(centralizer ({x} : Set G))) = ⟨p, hpC⟩ * ⟨f, hfC⟩ :=
        Subtype.ext hpf
      show ψ ⟨(t : G), hTC t.2⟩ ∈ X'
      rw [e1, map_mul]
      refine X'.mul_mem ?_ ?_
      · exact ⟨ι ⟨p, hp⟩, ⟨⟨p, hp⟩, rfl⟩, (hψι p hp).symm⟩
      · obtain ⟨y, hyX, hy⟩ := hcon f hfC hf
        exact ⟨y, hyX, hy⟩
    have h16 := card_range_mul_four_of_alt7 hTC ψ hker' hQ4'
    have := Subgroup.card_le_of_le hφle
    omega
  obtain ⟨f, hfC, hfPa, hfX⟩ := hexists
  have hσ4 : (ψ ⟨u, huC⟩) ^ 4 = 1 := by
    refine alt7_odd_centralizer (X := ι.range) hιcard (ρ := ψ ⟨z, hzC⟩) (g := ψ ⟨f, hfC⟩)
      ⟨ι ⟨z, hzP⟩, ⟨⟨z, hzP⟩, rfl⟩, (hψι z hzP).symm⟩ hρ1 ?_ ?_ hfX ?_ ?_
    · rintro y ⟨p, rfl⟩
      rw [show ((ι p : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) =
        ψ ⟨(p : G), hTC p.2.1⟩ from (hψι p p.2).symm]
      exact hcommψ p z _ hzC (hzc p p.2)
    · rintro y ⟨p, rfl⟩
      rw [show ((ι p : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) =
        ψ ⟨(p : G), hTC p.2.1⟩ from (hψι p p.2).symm]
      exact (hcommψ p f _ hfC (hcore.comm_P_conj p p.2 f hfPa)).symm
    · exact (hcommψ z u hzC huC huz).symm
    · exact (hcommψ f u hfC huC (huf f hfPa)).symm
  have hπodd : Odd (orderOf (ψ ⟨u, huC⟩)) := by
    have h1 : orderOf (ψ ⟨u, huC⟩) ∣ orderOf (⟨u, huC⟩ : ↥(centralizer ({x} : Set G))) :=
      orderOf_map_dvd ψ _
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat hodd h1
  have hπ1 : ψ ⟨u, huC⟩ = 1 := by
    have hd : orderOf (ψ ⟨u, huC⟩) ∣ 2 ^ 2 := by
      have := orderOf_dvd_of_pow_eq_one hσ4
      simpa using this
    have hcop : Nat.Coprime (orderOf (ψ ⟨u, huC⟩)) (2 ^ 2) :=
      Nat.Coprime.pow_right 2 (Nat.coprime_two_right.2 hπodd)
    exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd hcop hd)
  have hmem : (⟨u, huC⟩ : ↥(centralizer ({x} : Set G))) ∈ ψ.ker := hπ1
  rw [hker', Subgroup.mem_subgroupOf] at hmem
  exact hmem

@[expose] def B_L114_fusion5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G →
    ∀ (x : G) (K T Q S : Subgroup G) (a : G), IsAConfigW 5 x K T Q S a →
      a * x * a⁻¹ ∈ T ⊓ K ∧ S = T ⊔ zpowers a

theorem b_L114_fusion57_of_five (h5 : B_L114_fusion5) : B_L114_fusion57 := by
  intro G _ _ hG n hn x K T Q S a h
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl
  · obtain ⟨h1, h2⟩ := h5 G hG x K T Q S a h
    exact ⟨h1, h2, fun h7 => absurd h7 (by norm_num)⟩
  · obtain ⟨h1, h2⟩ := aconfigW_seven_fusion_two hG.pRank_eq_four.le h
    exact ⟨h1, h2, fun _ => aconfigW_seven_odd hG.pRank_eq_four.le h⟩

theorem b_lemma114_nonEven_of_leaves5 (hA : B_L114_fusion5) (hF : B_L114_final57) :
    B_lemma114_nonEven :=
  b_lemma114_nonEven_of_leaves57 (b_L114_fusion57_of_five hA) hF

end CFSG.GH74.GLS.C3.Layer1.Bk
