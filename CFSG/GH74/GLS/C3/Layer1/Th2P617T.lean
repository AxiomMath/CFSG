module

public import CFSG.GH74.GLS.C3.Layer1.Th2P617S
public import CFSG.GH74.GLS.C3.Layer1.Th2P617L
public import CFSG.GH74.GLS.C3.Layer1.Th2P617R

public section

namespace CFSG.GH74.GLS.Th2.Obs

open Equiv Equiv.Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK
  CFSG.GH74.GLS.Th2
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {x y : G} {K T S : Subgroup G}

theorem isS_of_rank_four (hG : C3Hyp G) {X A : Subgroup G} (hAX : A ≤ X)
    (hAel : CFSG.IsElementaryAbelian 2 ↥A) (hA4 : 4 ≤ pRank 2 ↥A) : IsS X A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hAc, hAs⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hAel
  refine ⟨hAX, hAel, le_antisymm ?_ ?_⟩
  · exact Th2.le_omega1_of_isElementaryAbelian hAel (le_inf hAX (fun a ha => by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact hAc b hb a ha))
  · refine (Subgroup.closure_le A).2 ?_
    rintro u ⟨⟨huX, huC⟩, hu2⟩
    by_contra huA
    have hucomm : ∀ a ∈ A, a * u = u * a := fun a ha =>
      Subgroup.mem_centralizer_iff.1 huC a ha
    have hu1 : u ≠ 1 := fun h => huA (h ▸ A.one_mem)
    have hu2' : orderOf u = 2 := orderOf_eq_prime (by rw [sq]; exact hu2) hu1
    have hzel := Th2.isElementaryAbelian_zpowers_of_orderOf_two hu2'
    have hcd : CommDisj A (zpowers u) := by
      refine ⟨fun a ha z hz => ?_, eq_bot_iff.2 fun z hz => ?_⟩
      · obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hz
        exact (Commute.zpow_right (hucomm a ha) m).eq
      · rcases mem_zpowers_two hu2' hz.2 with h0 | h0
        · simp [h0]
        · exact absurd (h0 ▸ hz.1) huA
    have hrk := hcd.pRank_sup hAel hzel le_rfl le_rfl
    rw [Th2.pRank_zpowers_of_orderOf_two hu2'] at hrk
    have h4 := pRank_le_top' (A ⊔ zpowers u)
    have h5 := hG.pRank_eq_four
    omega

theorem exists_adapted (hL34 : B_gen4_noL34_elem) (hG : C3Hyp G) (hs : Th2Std x y K T S)
    (h7 : Nonempty (kBar K ≃* alternatingGroup (Fin 7))) {B : Subgroup G}
    (hB : IsSn 4 ((T ⊓ K) ⊔ (T ⊓ CxK x K)) B) {b : G} {J : Subgroup G} (hobs : Obstr52 B b J) :
    ∃ (y' : G) (T' S' : Subgroup G), Th2Std x y' K T' S' ∧
      Nat.card ↥(T' ⊓ CxK x K) = Nat.card ↥(T ⊓ CxK x K) ∧
      pRank 2 ↥(T' ⊓ CxK x K) = pRank 2 ↥(T ⊓ CxK x K) ∧
      IsSn 4 ((T' ⊓ K) ⊔ (T' ⊓ CxK x K)) B ∧ ∀ p ∈ T' ⊓ K, p * b = b * p := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨U, E, z, hU, hES, hE2, hBdef, -⟩ := exists_dec617 hs h7 hB
  obtain ⟨eK⟩ := h7
  have hcen := centerlessBar_of_A7 ⟨eK⟩
  have hcd := hs.commDisj hcen
  have hKN := hs.K_normal_A7 hG ⟨eK⟩
  have hG4 : pRank 2 G ≤ 4 := hG.pRank_eq_four.le
  have hE4 : IsE 4 ⊤ B := isE_of_isSn le_top hB le_rfl
  have hBel : CFSG.IsElementaryAbelian 2 ↥B := hE4.2.1
  obtain ⟨hBc, hBsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hBel
  have hBR : B ≤ (T ⊓ K) ⊔ (T ⊓ CxK x K) := hB.1.1
  have hBT : B ≤ T := hBR.trans (sup_le inf_le_left inf_le_left)
  have hEQ : E ≤ T ⊓ CxK x K := hES.1
  have hUP : U ≤ T ⊓ K := hU.1
  have hUB : U ≤ B := hBdef ▸ le_sup_left
  have hEB : E ≤ B := hBdef ▸ le_sup_right
  obtain ⟨u, hu, e, he, hbue⟩ := exists_mul_of_mem_sup_of_commute
    (fun u hu q hq => hBc u (hUB hu) q (hEB hq)) (hBdef ▸ hobs.mem : b ∈ U ⊔ E)
  have hQ2' : 2 ≤ pRank 2 ↥(CxK x K) :=
    hE2.trans (C3.Layer1.Back.pRank_mono' (hEQ.trans inf_le_right))
  set D : Subgroup G := centralizer ({x, b} : Set G) with hD
  have hxE : x ∈ E := hs.x_mem_of_isS (X := T ⊓ CxK x K) inf_le_left ⟨hs.x_mem_T, hs.x_mem_CxK⟩ hES
  have hBD : B ≤ D := by
    intro β hβ
    rw [hD, Subgroup.mem_centralizer_iff]
    intro w hw
    rcases hw with rfl | rfl
    · exact hBc _ (hEB hxE) β hβ
    · exact hBc _ hobs.mem β hβ
  have hDx : D ≤ centralizer ({x} : Set G) := Subgroup.centralizer_le (by simp)
  have hB2 : IsPGroup 2 ↥(B.subgroupOf D) := (CFSG.IsElementaryAbelian.isPGroup 2 _).comap_subtype
  obtain ⟨Qs, hQs⟩ := hB2.exists_le_sylow
  set Vs : Subgroup G := (Qs : Subgroup ↥D).map D.subtype with hVs
  have hVsSyl : IsSylowOf 2 Vs D := ⟨Qs, rfl⟩
  have hBVs : B ≤ Vs := fun β hβ =>
    ⟨⟨β, hBD hβ⟩, hQs (Subgroup.mem_subgroupOf.2 hβ), rfl⟩
  have hVsD : Vs ≤ D := hVsSyl.le
  have hVs2 : IsPGroup 2 ↥(Vs.subgroupOf (centralizer ({x} : Set G))) :=
    hVsSyl.isPGroup.comap_subtype
  obtain ⟨Qt, hQt⟩ := hVs2.exists_le_sylow
  set Tp : Subgroup G := (Qt : Subgroup ↥(centralizer ({x} : Set G))).map
    (centralizer ({x} : Set G)).subtype with hTp
  have hTpSyl : IsSylowOf 2 Tp (centralizer ({x} : Set G)) := ⟨Qt, rfl⟩
  have hVsTp : Vs ≤ Tp := fun v hv =>
    ⟨⟨v, hDx (hVsD hv)⟩, hQt (Subgroup.mem_subgroupOf.2 hv), rfl⟩
  obtain ⟨k, hk, hkconj⟩ := hs.setup.sylowT.exists_mem_conj hTpSyl
  have hTpeq : Tp = cj k T := by
    ext g
    rw [mem_cj_iff]
    exact hkconj g
  have hs' := Th2Std.conj_A7 hL34 hG hs ⟨eK⟩ hQ2' hk
  rw [← hTpeq] at hs'
  have hcK : cj k K = K := by
    have hkN : k ∈ normalizer (K : Set G) :=
      C3.Layer1.P34.mem_normalizer_of_conj_le (fun a ha => by
        have := hKN k⁻¹ ((centralizer ({x} : Set G)).inv_mem hk) a ha
        simpa using this)
    exact cj_eq_of_mem_normalizer hkN
  have hQcj : Tp ⊓ CxK x K = cj k (T ⊓ CxK x K) := by
    have e := Subgroup.map_inf_eq T (CxK x K) (MulAut.conj k).toMonoidHom (MulAut.conj k).injective
    have e' : cj k (T ⊓ CxK x K) = cj k T ⊓ cj k (CxK x K) := e
    rw [e', cj_CxK_eq hk hcK, hTpeq]
  refine ⟨k * y * k⁻¹, Tp, cj k S, hs', ?_, ?_, ?_, ?_⟩
  · rw [hQcj]
    exact Subgroup.card_map_of_injective (MulAut.conj k).injective
  · rw [hQcj]
    exact pRank_cj k _
  ·
    have hcd' := hs'.commDisj hcen
    have hTN := Th2Std.T_le_normalizer hG hs ⟨eK⟩
    have hTpN := Th2Std.T_le_normalizer hG hs' ⟨eK⟩
    have hBTp : B ≤ Tp := hBVs.trans hVsTp
    have hBR' : B ≤ (Tp ⊓ K) ⊔ (Tp ⊓ CxK x K) := by
      intro β hβ
      have hev : actOn eK hTpN ⟨β, hBTp hβ⟩ ∈ alternatingGroup (Fin 7) := by
        have h1 := actOn_even_of_mem_R hcd hs eK hTN (hBR hβ) (hBT hβ)
        exact h1
      exact mem_R_of_actOn_even hs' hcd' ⟨eK⟩ eK hTpN (hBTp hβ) hev
    exact ⟨isS_of_rank_four hG hBR' hBel hE4.2.2, hE4.2.2⟩
  ·
    have hP'8 : Nat.card ↥(Tp ⊓ K) = 8 := Th2.card_sylow_A7 hs'.sylow_P ⟨eK⟩
    have hDN : D ≤ normalizer ((D ⊓ K : Subgroup G) : Set G) := by
      intro d hd
      have hdx := hDx hd
      refine mem_normalizer_of_conj_mem' (fun n hn => ⟨?_, ?_⟩) (fun n hn => ⟨?_, ?_⟩)
      · exact D.mul_mem (D.mul_mem hd hn.1) (D.inv_mem hd)
      · exact hKN d hdx n hn.2
      · exact D.mul_mem (D.mul_mem (D.inv_mem hd) hn.1) hd
      · have := hKN d⁻¹ ((centralizer ({x} : Set G)).inv_mem hdx) n hn.2
        simpa using this
    have hVK : IsSylowOf 2 (Vs ⊓ (D ⊓ K)) (D ⊓ K) :=
      hVsSyl.inf_of_le_normalizer inf_le_left hDN
    have hDK : D ⊓ K = K ⊓ centralizer ({b} : Set G) := by
      ext g
      constructor
      · rintro ⟨hgD, hgK⟩
        exact ⟨hgK, Subgroup.mem_centralizer_iff.2 fun w hw => by
          rw [Set.mem_singleton_iff] at hw
          rw [hw]
          exact Subgroup.mem_centralizer_iff.1 hgD b (by simp)⟩
      · rintro ⟨hgK, hgb⟩
        refine ⟨Subgroup.mem_centralizer_iff.2 fun w hw => ?_, hgK⟩
        rcases hw with rfl | rfl
        · exact (mem_centralizer_singleton_iff.1 (hs.K_le_C hgK)).symm
        · exact (mem_centralizer_singleton_iff.1 hgb).symm
    have hbue' : b = u * e := hbue
    have h8 : 8 ∣ Nat.card ↥(K ⊓ centralizer ({b} : Set G)) := by
      have huK : u ∈ K := (hUP hu).2
      have hu2 : u * u = 1 := hBsq u (hUB hu)
      have he2 : e * e = 1 := hBsq e (hEB he)
      have hue : u * e = e * u := hBc u (hUB hu) e (hEB he)
      rw [hbue']
      exact eight_dvd_card_K_inf_centralizer hG hs ⟨eK⟩ huK hu2 (hEQ he).2 he2 hue
    have hvk8 : 8 ≤ Nat.card ↥(Vs ⊓ (D ⊓ K)) := by
      rw [hVK.card_eq, hDK]
      have hn0 : Nat.card ↥(K ⊓ centralizer ({b} : Set G)) ≠ 0 := Nat.card_pos.ne'
      have h23 : 2 ^ 3 ∣ Nat.card ↥(K ⊓ centralizer ({b} : Set G)) := by simpa using h8
      have h3 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hn0).1 h23
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (Nat.card ↥(K ⊓ centralizer ({b} : Set G))).factorization 2 :=
          Nat.pow_le_pow_right (by norm_num) h3
    have hVsK : Vs ⊓ (D ⊓ K) = Vs ⊓ K := by
      ext g
      constructor
      · rintro ⟨hgV, -, hgK⟩
        exact ⟨hgV, hgK⟩
      · rintro ⟨hgV, hgK⟩
        exact ⟨hgV, hVsD hgV, hgK⟩
    rw [hVsK] at hvk8
    have hle : Vs ⊓ K ≤ Tp ⊓ K := inf_le_inf_right K hVsTp
    have heq : Vs ⊓ K = Tp ⊓ K :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hP'8]; exact hvk8)
    intro p hp
    have hpV : p ∈ Vs ⊓ K := by rw [heq]; exact hp
    exact (Subgroup.mem_centralizer_iff.1 (hVsD hpV.1) b (by simp)).symm

end CFSG.GH74.GLS.Th2.Obs
