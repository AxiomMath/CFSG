module

public import CFSG.GH74.GLS.C3.Layer1.St1P89RN
public import CFSG.GH74.GLS.C3.Layer1.St1P89RRank
public import CFSG.GH74.GLS.C3.Layer1.St1P89Real
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKExcRank
public import CFSG.GH74.GLS.C3.Layer1.St1P89Aut
public import CFSG.GH74.GLS.C3.Layer1.Back112Glue
public import CFSG.LocalAnalysis.SectionRank.AmbientRank

public section

namespace CFSG.GH74.GLS.C3.Layer1.P89

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.C3.Layer1
  CFSG.GH74.GLS.C3.Layer1.Thm1 CFSG.GH74.GLS.C3.Layer1.P34Real CFSG.GH74.Uniqueness.SU.SU1

section Core

variable {G : Type} [Group G] [Finite G]

theorem exists_cfg89
    (hAL : B_prop89_autlevel) (hsimple : IsSimpleGroup G) (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hrank : pRank 2 G = 4) {u x : G} {K T : Subgroup G} (hlu : IsLocallyUnbalancing u x K)
    (hxstar : ¬ IsStar2 x) (hstarU : IsStar2 u) (hL2 : HasL2Model (kBar K) (fun q => q = 9))
    (hKN : ∀ c ∈ centralizer ({u} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K)
    (hCx1 : pRank 2 ↥(CxK u K) = 1) (hT : IsSylowOf 2 T (centralizer ({u} : Set G))) (hxT : x ∈ T) :
    ∃ (P Q : Subgroup G) (z f r s : G), P = T ⊓ K ∧ Q = T ⊓ CxK u K ∧ Cfg89T G T P Q u z x f r s ∧
      ∃ n1 n2 : G, n1 ∈ K ∧ n2 ∈ K ∧ n1 * u * n1⁻¹ = u ∧ n1 * f * n1⁻¹ = f ∧ n1 * z * n1⁻¹ = s ∧
        n1 * s * n1⁻¹ = z ∧ n2 * u * n2⁻¹ = u ∧ n2 * f * n2⁻¹ = f ∧ n2 * z * n2⁻¹ = z ∧
        n2 * s * n2⁻¹ = z * s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨hu2, hKcomp⟩, hx2, hxC, hxN, -⟩ := id hlu
  set C : Subgroup G := centralizer ({u} : Set G) with hC
  have hKC : K ≤ C := hKcomp.1
  have hCnormK : C ≤ normalizer (K : Set G) := by
    intro g hg
    refine mem_normalizer_iff.2 fun h => ⟨fun hh => hKN g hg h hh, fun hh => ?_⟩
    have := hKN g⁻¹ (C.inv_mem hg) _ hh
    rwa [show g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h by group] at this
  have hcen : Function.Injective (MulAut.conj : kBar K →* MulAut (kBar K)) := by
    have hodd : HasL2Model (kBar K) Odd := by
      obtain ⟨p, f, hp, hf, hP, hL⟩ := hL2
      exact ⟨p, f, hp, hf, by rw [show p ^ f = 9 from hP]; decide, hL⟩
    obtain ⟨F, _, _, _, ⟨e⟩⟩ := exists_l2_model_of_hasL2Model hodd
    exact IVK.conj_injective_of_L2 e
  have huC : u ∈ C := mem_centralizer_singleton_iff.2 rfl
  have hu1 : u ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hu2
    omega
  have hu_mem : u ∈ T := by
    have hu2g : IsPGroup 2 ↥(zpowers u) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu2, pow_one])
    have hsup : IsPGroup 2 ↥(T ⊔ zpowers u) := by
      refine hT.isPGroup.to_sup_of_normal_left' hu2g (P34.W_le_normalizer_of fun w hw a ha => ?_)
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hw
      have hau : Commute u a := (mem_centralizer_singleton_iff.1 (hT.le ha)).symm
      have hc : Commute (u ^ j) a := hau.zpow_left j
      have : u ^ j * a * (u ^ j)⁻¹ = a := by
        rw [hc.eq]
        group
      rw [this]
      exact ha
    have heq : T ⊔ zpowers u = T :=
      hT.eq_of_le le_sup_left (sup_le hT.le ((zpowers_le).2 huC)) hsup
    rw [← heq]
    exact Subgroup.mem_sup_right (mem_zpowers u)
  have hsylowP : IsSylowOf 2 (T ⊓ K) K := hT.inf_of_le_normalizer hKC hCnormK
  let H : Base89 u K T := ⟨hKC, hKN, hcen, hT, hsylowP, hu_mem⟩
  have hCxle : CxK u K ≤ C := inf_le_left
  have hCnormCx : C ≤ normalizer (CxK u K : Set G) := by
    intro g hg
    have hconj : ∀ g ∈ C, ∀ n ∈ CxK u K, g * n * g⁻¹ ∈ CxK u K := fun g hg n hn =>
      CMK_conj hKN hg hn
    refine mem_normalizer_iff.2 fun h => ⟨fun hh => hconj g hg h hh, fun hh => ?_⟩
    have := hconj g⁻¹ (C.inv_mem hg) _ hh
    rwa [show g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h by group] at this
  have hQT : pRank 2 ↥(Qs u K T) = 1 :=
    (pRank_eq_of_isSylowOf (hT.inf_of_le_normalizer hCxle hCnormCx)).trans hCx1
  have hQinv : ∀ q ∈ Qs u K T, q ^ 2 = 1 → q = 1 ∨ q = u := by
    intro q hq hq2
    by_contra hne
    push Not at hne
    have huq : u * q = q * u := (mem_centralizer_singleton_iff.1 (H.T_le_C (Qs_le_T hq))).symm
    have hu2' : u ^ 2 = 1 := by
      have := pow_orderOf_eq_one u
      rwa [hu2] at this
    have hEl := isElemAbelian_pair hu2' hq2 huq
    have hcard := card_klein hu2' hq2 huq hu1 hne.1 hne.2.symm
    have hle : zpowers u ⊔ zpowers q ≤ Qs u K T :=
      sup_le ((zpowers_le).2 H.u_mem_Qs) ((zpowers_le).2 hq)
    have hEA : CFSG.IsElementaryAbelian 2 ↥(zpowers u ⊔ zpowers q) :=
      (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 _).mpr hEl
    have := le_pRank_of_elem hle hEA (k := 2) (by rw [hcard]; norm_num)
    omega
  have hTrank : pRank 2 ↥T = pRank 2 G := (pRank_eq_of_isSylowOf hT).trans hstarU.2
  obtain ⟨E, hET, hEs⟩ := exists_isEStar_le hTrank
  have hEcard : Nat.card ↥E = 16 := by rw [hEs.2, hrank]; norm_num
  have hEel : Open.IsElemAbelian 2 E :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 E).mp hEs.1
  have hEcomm := (isElemAbelian_iff.mp hEel).1
  have hEsq := (isElemAbelian_iff.mp hEel).2
  have hEC : E ≤ C := hET.trans hT.le
  let φ : ↥E →* MulAut (kBar K) := (Back.actHom H.KN).comp (Subgroup.inclusion hEC)
  have hφ : ∀ e : ↥E, φ e = act H.KN (e : G) := fun e => (act_of_mem H.KN (hEC e.2)).symm
  have hEbB : φ.range ≤ H.B := by
    rintro _ ⟨e, rfl⟩
    exact (H.mem_B).2 ⟨(e : G), hET e.2, (hφ e).symm⟩
  have hEbel : Open.IsElemAbelian 2 φ.range := by
    refine isElemAbelian_iff.2 ⟨?_, ?_⟩
    · rintro _ ⟨e, rfl⟩ _ ⟨e', rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hEcomm e e.2 e' e'.2)
    · rintro _ ⟨e, rfl⟩
      rw [← map_pow]
      have : e ^ 2 = 1 := Subtype.ext (by simpa using hEsq e e.2)
      rw [this, map_one]
  have hker : Nat.card φ.ker ≤ 2 := by
    classical
    let g : φ.ker → Bool := fun k => decide (((k : ↥E) : G) = 1)
    have hk : ∀ k : φ.ker, ((k : ↥E) : G) = 1 ∨ ((k : ↥E) : G) = u := by
      intro k
      have hk1 : φ (k : ↥E) = 1 := k.2
      have hq : ((k : ↥E) : G) ∈ Qs u K T :=
        (H.mem_Qs).2 ⟨hET (k : ↥E).2, by rw [← hφ]; exact hk1⟩
      exact hQinv _ hq (hEsq _ (k : ↥E).2)
    have hinj : Function.Injective g := by
      intro k k' h
      have h' : (((k : ↥E) : G) = 1) ↔ (((k' : ↥E) : G) = 1) := by
        simpa [g] using h
      apply Subtype.ext
      apply Subtype.ext
      rcases hk k with h1 | h1 <;> rcases hk k' with h2 | h2
      · rw [h1, h2]
      · exact absurd (h'.1 h1) (by rw [h2]; exact hu1)
      · exact absurd (h'.2 h2) (by rw [h1]; exact hu1)
      · rw [h1, h2]
    have := Nat.card_le_card_of_injective g hinj
    simpa using this
  have hEb8 : 8 ≤ Nat.card ↥φ.range := by
    by_contra hlt
    push Not at hlt
    have h1 := Subgroup.card_ker_mul_card_range φ
    have h2 : Nat.card φ.ker * Nat.card φ.range ≤ 2 * 7 :=
      Nat.mul_le_mul hker (by omega)
    rw [hEcard] at h1
    omega
  have hxB : act H.KN x ∈ H.B := (H.mem_B).2 ⟨x, hxT, rfl⟩
  have hx2' : x ^ 2 = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx2] at this
  have hxb2 : act H.KN x ^ 2 = 1 := by
    rw [← act_pow_nat H.KN hxC, hx2', act_one]
  have hact_eq : act H.KN x = Back.actHom (Bk.hLn_normalizer K) ⟨x, hxN⟩ := by
    rw [act_of_mem H.KN hxC]
    ext q
    induction q using QuotientGroup.induction_on with | H l => ?_
    rw [Back.actHom_mk, Back.actHom_mk]
  obtain ⟨hnotinn, hpgl⟩ :=
    Bk.ivk10_bridge IVK.Proofs2.b_ivk_10_2L hlu (Or.inl rfl : IsFM9 9) hL2
  have hnotinn' : act H.KN x ∉ innAut (kBar K) := by
    rw [hact_eq]
    exact hnotinn
  have hpgl' : IsPGL2 ↥(innAut (kBar K) ⊔ zpowers (act H.KN x)) (fun q => q = 9) := by
    rw [hact_eq]
    exact hpgl
  obtain ⟨rb, sb, fb, k₁, k₂, hAD⟩ := hAL (kBar K) hL2 H.B H.B_isPGroup H.sylow_Pbar (act H.KN x)
    hxB hxb2 hnotinn' hpgl' φ.range hEbB hEbel hEb8
  obtain ⟨r, hr, hra⟩ := (H.mem_B_inf_inn).1 hAD.r_mem
  obtain ⟨s, hs, hsa⟩ := (H.mem_B_inf_inn).1 hAD.s_mem
  obtain ⟨⟨f, hfE⟩, hfa⟩ := MonoidHom.mem_range.1 hAD.f_mem
  have hfa' : act H.KN f = fb := by rw [← hfa, hφ]
  have hf2 : f ^ 2 = 1 := hEsq f hfE
  have c := H.cfg89_of_data hsimple hnonab hrank hu2 hx2 hxT hxstar hQinv hAD hr hs (hET hfE) hf2
    hra hsa hfa'
  obtain ⟨n1, n2, hn1, hn2, h1, h2, h3, h4, h5, h6, h7, h8⟩ := H.exists_n hAD c hra hsa hfa'
  exact ⟨T ⊓ K, Qs u K T, r ^ 2, f, r, s, rfl, rfl, c, n1, n2, hn1, hn2, h1, h2, h3, h4, h5, h6, h7, h8⟩

end Core

section Final

variable {G : Type} [Group G] [Finite G]

theorem relIndex_ne_zero' {H K : Subgroup G} : H.relIndex K ≠ 0 :=
  Subgroup.index_ne_zero_of_finite

theorem two_mul_le_of_lt_pow {a b j k : ℕ} (ha : a = 2 ^ j) (hb : b = 2 ^ k) (hab : a < b) :
    2 * a ≤ b := by
  have hjk : j < k := by
    by_contra h
    push Not at h
    have : b ≤ a := by rw [ha, hb]; exact Nat.pow_le_pow_right (by norm_num) h
    omega
  rw [ha, hb, ← pow_succ']
  exact Nat.pow_le_pow_right (by norm_num) hjk

theorem split_of_relIndex_two {S T : Subgroup G} (hTS : T ≤ S) (h2 : T.relIndex S = 2) {a : G}
    (haS : a ∈ S) (haT : a ∉ T) :
    (∀ g ∈ S, g ∈ T ∨ a⁻¹ * g ∈ T) ∧ (∀ g ∈ S, ∀ t ∈ T, g * t * g⁻¹ ∈ T) := by
  classical
  set N : Subgroup ↥S := T.subgroupOf S with hN
  have hidx : N.index = 2 := h2
  have hnorm : N.Normal := Subgroup.normal_of_index_eq_two hidx
  constructor
  · intro g hg
    by_contra hcon
    push Not at hcon
    obtain ⟨hgT, haginv⟩ := hcon
    have hcard : Nat.card (↥S ⧸ N) = 2 := by rw [← Subgroup.index_eq_card]; exact hidx
    have : Fintype (↥S ⧸ N) := Fintype.ofFinite _
    have hcard' : Fintype.card (↥S ⧸ N) = 2 := by rw [← Nat.card_eq_fintype_card]; exact hcard
    let q1 : ↥S ⧸ N := QuotientGroup.mk 1
    let qa : ↥S ⧸ N := QuotientGroup.mk ⟨a, haS⟩
    let qg : ↥S ⧸ N := QuotientGroup.mk ⟨g, hg⟩
    have h1a : q1 ≠ qa := by
      intro h
      apply haT
      have := QuotientGroup.eq.1 h
      simpa [Subgroup.mem_subgroupOf, hN] using this
    have h1g : q1 ≠ qg := by
      intro h
      apply hgT
      have := QuotientGroup.eq.1 h
      simpa [Subgroup.mem_subgroupOf, hN] using this
    have hag : qa ≠ qg := by
      intro h
      apply haginv
      have := QuotientGroup.eq.1 h
      simpa [Subgroup.mem_subgroupOf, hN] using this
    have h3 : ({q1, qa, qg} : Finset (↥S ⧸ N)).card = 3 := by
      rw [Finset.card_eq_three]
      exact ⟨q1, qa, qg, h1a, h1g, hag, rfl⟩
    have h4 := Finset.card_le_univ ({q1, qa, qg} : Finset (↥S ⧸ N))
    omega
  · intro g hg t ht
    have := hnorm.conj_mem ⟨t, hTS ht⟩ (Subgroup.mem_subgroupOf.2 ht) ⟨g, hg⟩
    simpa [Subgroup.mem_subgroupOf, hN] using this

theorem pRank_mulAut_kBar_le_three_of_L2_nine {K : Subgroup G}
    (hL2 : HasL2Model (kBar K) (fun q => q = 9)) :
    pRank 2 (MulAut (kBar K)) ≤ 3 := by
  have hodd : HasL2Model (kBar K) Odd := by
    obtain ⟨p, f, hp, hf, hq, hL⟩ := hL2
    exact ⟨p, f, hp, hf, by rw [hq]; decide, hL⟩
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := exists_l2_model_of_hasL2Model hodd
  have h := @CFSG.GH74.GLS.IVK.ivk_1_2k_a F _ _ hF (kBar K) _ _ e
  omega

theorem pRank_centralizer_le_four_of_rank_one {u : G} {K : Subgroup G}
    (hL2 : HasL2Model (kBar K) (fun q => q = 9))
    (hKN : ∀ c ∈ centralizer ({u} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K)
    (hCx1 : pRank 2 ↥(CxK u K) = 1) :
    pRank 2 ↥(centralizer ({u} : Set G)) ≤ 4 := by
  classical
  let C : Subgroup G := centralizer ({u} : Set G)
  let ψ : ↥C →* MulAut (kBar K) := Back.actHom hKN
  have hkerψ : ψ.ker = (CxK u K).subgroupOf C := by
    simpa [ψ, C, CxK, CMK] using Back.actHom_ker hKN
  have hkerMap : ψ.ker.map C.subtype = CxK u K := by
    rw [hkerψ]
    exact Subgroup.map_subgroupOf_eq_of_le (by exact inf_le_left)
  have hmain := CFSG.LocalAnalysis.UniquenessCase.PartTwo.s16k_pRank_le_add_of_hom
    (φ := ψ) (p := 2) Nat.prime_two
  rw [hkerMap] at hmain
  have hCxOpen : CFSG.Open.pRank 2 (CxK u K) = 1 := by
    rw [← CFSG.SectionRank.pRank_coe_eq_openPRank 2 (CxK u K)]
    exact hCx1
  have hrangeRoot : pRank 2 ↥ψ.range ≤ 3 :=
    (Back.pRank_le_top ψ.range).trans (pRank_mulAut_kBar_le_three_of_L2_nine hL2)
  have hrange : CFSG.Open.pRank 2 ψ.range ≤ 3 := by
    rw [← CFSG.SectionRank.pRank_coe_eq_openPRank 2 ψ.range]
    exact hrangeRoot
  have h4 : CFSG.Open.pRank 2 C ≤ 4 := by omega
  change CFSG.pRank 2 ↥C ≤ 4
  rw [CFSG.SectionRank.pRank_coe_eq_openPRank 2 C]
  exact h4

theorem b_prop89_realize_core
    (hAL : B_prop89_autlevel)
    {G : Type} [Group G] [Finite G]
    (hsimple : IsSimpleGroup G) (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hrank : pRank 2 G = 4)
    (T5 : St1Thm5 G)
    {x : G} {S U : Subgroup G} {u : G} {K W : Subgroup G}
    (hc : Config8 x S U u K W)
    (hK : HasL2Model (kBar K) (fun q => q = 9))
    (hQ : pRank 2 ↥(W ⊓ CxK u K) = 1) :
    ∃ (T P Q : Subgroup G) (z f r s a : G),
      P = T ⊓ K ∧ Q = T ⊓ CxK u K ∧ Cfg89T G T P Q u z x f r s ∧ Cfg89S G T u S a ∧
        ((∀ q ∈ Q, q = 1 ∨ q = u) → ∃ n1 n2 : G, n1 ∈ K ∧ n2 ∈ K ∧
          n1 * u * n1⁻¹ = u ∧ n1 * f * n1⁻¹ = f ∧ n1 * z * n1⁻¹ = s ∧ n1 * s * n1⁻¹ = z ∧
          n2 * u * n2⁻¹ = u ∧ n2 * f * n2⁻¹ = f ∧ n2 * z * n2⁻¹ = z ∧ n2 * s * n2⁻¹ = z * s) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hlu : IsLocallyUnbalancing u x K := hc.unbal.isLocallyUnbalancing
  have hKcomp : IsPCompIn 2 (centralizer ({u} : Set G)) K := hc.unbal.1.2
  have hU : IsNormalFourOf S U := ⟨hc.four, hc.U_le, hc.U_normal⟩
  have hstarU : IsStar2 u := isStar2_of_mem_normalFour hc.sylow_S hU hc.u_mem.1 hc.u_mem.2
  have hxstar : ¬ IsStar2 x := fun h => hc.oddCore (T5 x h)
  have hKN := K_normal_of_rank_one hKcomp hK hc.sylow_W hQ
  have hCx1 : pRank 2 ↥(CxK u K) = 1 := pRank_CxK_eq_one hc.sylow_W hQ
  set C : Subgroup G := centralizer ({u} : Set G) with hC
  have hxS : x ∈ S := hc.x_mem.1
  have hxC : x ∈ C := mem_centralizer_singleton_iff.2 (hc.x_mem.2 u hc.u_mem.1)
  have hSp : IsPGroup 2 ↥S := hc.sylow_S.isPGroup
  set T₁ : Subgroup G := S ⊓ C with hT₁
  have hxT₁ : x ∈ T₁ := ⟨hxS, hxC⟩
  have hcontra : ∀ T'' : Subgroup G, IsSylowOf 2 T'' C → IsSylowOf 2 T'' ⊤ → x ∈ T'' → False := by
    intro T'' hT'' hTtop hxT''
    obtain ⟨P, Q, z, f, r, s, -, -, c, -⟩ := exists_cfg89 hAL hsimple hnonab hrank hlu hxstar
      hstarU hK hKN hCx1 hT'' hxT''
    exact false_of_sylow c hTtop
  have hrel : T₁.relIndex S ≤ 2 := by
    have hrel0 : (S ⊓ centralizer (U : Set G)).relIndex S ≤ 2 := by
      have := (ig10_20_ii Nat.prime_two hSp hU.isNormalEp2).2.1
      rwa [inf_comm, Subgroup.inf_relIndex_right]
    have hCUle : S ⊓ centralizer (U : Set G) ≤ T₁ :=
      inf_le_inf_left S (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hc.u_mem.1))
    exact (Subgroup.relIndex_le_of_le_left hCUle relIndex_ne_zero').trans hrel0
  by_cases hSC : S ≤ C
  ·
    exfalso
    have hSylC : IsSylowOf 2 S C := by
      refine isSylowOf_iff.2 ⟨hSC, hSp, ?_⟩
      have := (isSylowOf_iff.1 hc.sylow_S).2.2
      rw [Subgroup.relIndex_top_right] at this
      exact fun hd => this (hd.trans (Subgroup.relIndex_dvd_index_of_le hSC))
    exact hcontra S hSylC hc.sylow_S hxS
  · have hrel1 : T₁.relIndex S ≠ 1 := by
      intro h1
      exact hSC ((Subgroup.relIndex_eq_one.1 h1).trans inf_le_right)
    have hrel2 : T₁.relIndex S = 2 := by
      have : T₁.relIndex S ≠ 0 := relIndex_ne_zero'
      omega
    have hScard : Nat.card ↥S = 2 * Nat.card ↥T₁ := by
      have := Subgroup.relIndex_mul_card T₁ S
      rw [inf_eq_left.2 (inf_le_left : T₁ ≤ S), hrel2] at this
      have hT : Nat.card ↥T₁ = Nat.card ↥(S ⊓ C) := rfl
      omega
    obtain ⟨T', hT', hT₁T'⟩ := CFSG.ComponentClassification.FooteLit.exists_isSylowOf_ge_of_le
      (X := C) (A := T₁) inf_le_right hSp.to_inf_left
    by_cases hEq : T' = T₁
    ·
      have hT₁C : IsSylowOf 2 T₁ C := hEq ▸ hT'
      obtain ⟨a, haS, haC⟩ := Set.not_subset.1 hSC
      have haT : a ∉ T₁ := fun h => haC h.2
      obtain ⟨hsplit, hnormT⟩ := split_of_relIndex_two inf_le_left hrel2 haS haT
      have hZcyc : IsCyclic ↥(centerIn S) := by
        by_contra hnc
        have hu := hc.U_central hnc hc.u_mem.1
        apply hSC
        intro g hg
        exact mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hu.2 g hg)
      have sc : Cfg89S G T₁ u S a :=
        { sylowS := hc.sylow_S
          T_le := inf_le_left
          a_mem := haS
          a_nmem := haT
          S_split := hsplit
          T_norm := hnormT
          T_cent := fun g hg hgu => ⟨hg, mem_centralizer_singleton_iff.2 hgu⟩
          Zcyc := hZcyc }
      obtain ⟨P, Q, z, f, r, s, hP, hQ', c, n1, n2, hn1, hn2, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
        exists_cfg89 hAL hsimple hnonab hrank hlu hxstar hstarU hK hKN hCx1 hT₁C hxT₁
      exact ⟨T₁, P, Q, z, f, r, s, a, hP, hQ', c, sc,
        fun _ => ⟨n1, n2, hn1, hn2, h1, h2, h3, h4, h5, h6, h7, h8⟩⟩
    ·
      exfalso
      have hlt : T₁ ≠ T' := Ne.symm hEq
      have hdvd : Nat.card ↥T₁ ∣ Nat.card ↥T' := Subgroup.card_dvd_of_le hT₁T'
      have hne : Nat.card ↥T₁ ≠ Nat.card ↥T' := fun h =>
        hlt (Subgroup.eq_of_le_of_card_ge hT₁T' (le_of_eq h.symm))
      have hlt' : Nat.card ↥T₁ < Nat.card ↥T' :=
        lt_of_le_of_ne (Nat.le_of_dvd Nat.card_pos hdvd) hne
      obtain ⟨j, hj⟩ := hSp.to_inf_left.exists_card_eq
      obtain ⟨k, hk⟩ := hT'.isPGroup.exists_card_eq
      have h2le : 2 * Nat.card ↥T₁ ≤ Nat.card ↥T' := two_mul_le_of_lt_pow hj hk hlt'
      have hle : Nat.card ↥T' ≤ Nat.card ↥S := card_le_of_isSylowOf hc.sylow_S le_top hk
      have hcardT' : Nat.card ↥T' = Nat.card ↥S := by omega
      have hTtop : IsSylowOf 2 T' ⊤ :=
        isSylowOf_of_card le_top (by rw [hcardT', hc.sylow_S.card_eq])
      exact hcontra T' hT' hTtop (hT₁T' hxT₁)

theorem b_prop89_realize_of_autlevel
    (hAL : B_prop89_autlevel) : B_prop89_realize := by
  intro G _ _ hG hN T7 P41 P51 T5 x S U u K W hc hK hQ
  exact b_prop89_realize_core hAL hG.kproper.1 hG.kproper.2.1 hG.pRank_eq_four
    T5 hc hK hQ

theorem b_st1_prop89_of_autlevel_general
    {G : Type} [Group G] [Finite G]
    (hsimple : IsSimpleGroup G) (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hrank3 : 3 ≤ pRank 2 G) (T5 : St1Thm5 G)
    {y : G} {S U : Subgroup G} {u : G} {K W : Subgroup G}
    (hc : Config8 y S U u K W)
    (hK : HasL2Model (kBar K) (fun q => q = 9))
    (hQ : pRank 2 ↥(W ⊓ CxK u K) = 1) : False := by
  haveI : IsSimpleGroup G := hsimple
  have hxstar : ¬ IsStar2 y := fun h => hc.oddCore (T5 y h)
  have hKN : ∀ c ∈ centralizer ({u} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K :=
    K_normal_of_rank_one hc.unbal.1.2 hK hc.sylow_W hQ
  have hCx1 : pRank 2 ↥(CxK u K) = 1 := pRank_CxK_eq_one hc.sylow_W hQ
  have hCu4 : pRank 2 ↥(centralizer ({u} : Set G)) ≤ 4 :=
    pRank_centralizer_le_four_of_rank_one hK hKN hCx1
  have hU : IsNormalFourOf S U := ⟨hc.four, hc.U_le, hc.U_normal⟩
  have hstarU : IsStar2 u := isStar2_of_mem_normalFour hc.sylow_S hU hc.u_mem.1 hc.u_mem.2
  have hGle4 : pRank 2 G ≤ 4 := by
    rw [← hstarU.2]
    exact hCu4
  have hCy3 : 3 ≤ pRank 2 ↥(centralizer ({y} : Set G)) := by
    have hnoncomm : ¬ IsMulCommutative G := by
      intro hcomm
      obtain ⟨a, b, hab⟩ := hnonab
      exact hab (hcomm.is_comm.comm a b)
    letI : Group.IsPerfect G :=
      TauCeti.IsSimpleGroup.isPerfect_of_not_isMulCommutative hnoncomm
    have hG3 : 3 ≤ CFSG.Open.twoRank G := by
      simpa only [CFSG.Open.twoRank, CFSG.SectionRank.pRank_eq_open_pRank_top] using hrank3
    have hC := CFSG.ProperTwoGeneratedCore.perfect_involution_centralizer_rank_three
      hG3 y hc.ord_x
    simpa only [CFSG.Open.twoRank, CFSG.SectionRank.pRank_eq_open_pRank_top] using hC
  have hCyle : pRank 2 ↥(centralizer ({y} : Set G)) ≤ pRank 2 G :=
    Back.pRank_le_top (centralizer ({y} : Set G))
  have hCy4 : 4 ≤ pRank 2 G := by
    have hlt : pRank 2 ↥(centralizer ({y} : Set G)) < pRank 2 G :=
      lt_of_le_of_ne hCyle (by
        intro heq
        exact hxstar ⟨hc.ord_x, heq⟩)
    omega
  have hrank4 : pRank 2 G = 4 := le_antisymm hGle4 hCy4
  obtain ⟨T, P, Q, z, f, r, s, a, -, -, c, sc, hsmall⟩ :=
    b_prop89_realize_core b_prop89_autlevel_proved hsimple hnonab hrank4 T5 hc hK hQ
  refine c.false_of_cfg89 sc ?_
  intro hQsmall
  obtain ⟨n1, n2, -, -, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hsmall hQsmall
  exact ⟨n1, n2, h1, h2, h3, h4, h5, h6, h7, h8⟩

end Final

end CFSG.GH74.GLS.C3.Layer1.P89
