module

public import CFSG.GH74.GLS.IVK.Lifted.QuatFixed
public import CFSG.GH74.GLS.IVK.Lifted.InvSylow
public import CFSG.GH74.GLS.IVK.Lifted.Std6Glue
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Glue
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.QuasisimpleNotTwoGroupQuotient

public section

namespace CFSG.GH74.GLS.IVK.Lifted

open Subgroup Matrix CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.Stage1.Thm3.Sec4
  CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6 CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm6 CFSG.DisconnectedInvolutionGraph CFSG.DisconnectedInvolutionGraph.Helpers
  CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section Basics

theorem noCommInv_of_pRank {Q : Type} [Group Q] [Finite Q] (h : pRank 2 Q = 1) :
    ∀ u v : Q, orderOf u = 2 → orderOf v = 2 → u * v = v * u → u = v := by
  intro u v hu hv huv
  have h' : pRank 2 ↥(⊤ : Subgroup Q) = 1 := by
    rw [pRank_eq_of_mulEquiv' (Subgroup.topEquiv : ↥(⊤ : Subgroup Q) ≃* Q)]
    exact h
  exact eq_of_pRank_one h' (Subgroup.mem_top u) (Subgroup.mem_top v) hu hv huv

theorem exists_fixed_order_four_elt {Q : Type} [Group Q] [Finite Q]
    (hno : ∀ u v : Q, orderOf u = 2 → orderOf v = 2 → u * v = v * u → u = v)
    (φ : MulAut Q) (hf : FixedCond Q φ) : ∃ r : Q, orderOf r = 4 ∧ φ r = r := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R⟩ : Nonempty (Sylow 2 ↥(fixedSubgroup Q φ)) := inferInstance
  have hncyc := fixedCond_noncyclic_sylow φ hf R
  have hR2 : IsPGroup 2 ↥(R : Subgroup ↥(fixedSubgroup Q φ)) := R.isPGroup'
  have hrank : NoCommutingDistinctInvolutions ↥(R : Subgroup ↥(fixedSubgroup Q φ)) := by
    intro u v huv
    have hu : orderOf ((((u.1 : ↥(R : Subgroup ↥(fixedSubgroup Q φ))) : ↥(fixedSubgroup Q φ)) : Q)) = 2 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
      exact u.2
    have hv : orderOf ((((v.1 : ↥(R : Subgroup ↥(fixedSubgroup Q φ))) : ↥(fixedSubgroup Q φ)) : Q)) = 2 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
      exact v.2
    have hcomm : (((u.1 : ↥(R : Subgroup ↥(fixedSubgroup Q φ))) : ↥(fixedSubgroup Q φ)) : Q) *
        (((v.1 : ↥(R : Subgroup ↥(fixedSubgroup Q φ))) : ↥(fixedSubgroup Q φ)) : Q) =
        (((v.1 : ↥(R : Subgroup ↥(fixedSubgroup Q φ))) : ↥(fixedSubgroup Q φ)) : Q) *
        (((u.1 : ↥(R : Subgroup ↥(fixedSubgroup Q φ))) : ↥(fixedSubgroup Q φ)) : Q) := by
      have := congrArg (fun x : ↥(R : Subgroup ↥(fixedSubgroup Q φ)) =>
        (((x : ↥(R : Subgroup ↥(fixedSubgroup Q φ))) : ↥(fixedSubgroup Q φ)) : Q)) huv
      simpa using this
    exact Subtype.ext (Subtype.ext (Subtype.ext (hno _ _ hu hv hcomm)))
  rcases rank_one_two_cyclic_or_quaternion hR2 hrank with hc | ⟨e, he1, ⟨ε⟩⟩
  · exact absurd hc hncyc
  · set r' : ↥(fixedSubgroup Q φ) :=
      ((ε (QuaternionGroup.xa 0) : ↥(R : Subgroup ↥(fixedSubgroup Q φ))) : ↥(fixedSubgroup Q φ)) with hr'
    refine ⟨(r' : Q), ?_, r'.2⟩
    rw [Subgroup.orderOf_coe, hr', Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact QuaternionGroup.orderOf_xa 0

theorem sylow_two_not_cyclic_of_quasisimple
    {Q : Type} [Group Q] [Finite Q] (hq : CFSG.IsQuasisimple Q)
    (P : Sylow 2 Q) : ¬ IsCyclic ↥(P : Subgroup Q) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hcyc
  obtain ⟨-, -, -, ⟨-, -, hidx, -⟩, -⟩ := cyclic_sylow_normal_odd_complement P hcyc
  have hgw : CFSG.GorensteinWalter.IsQuasisimple Q := by
    obtain ⟨hperf, hsimple, -⟩ := hq
    have hnt : Nontrivial Q := by
      have : Nontrivial (Q ⧸ Subgroup.center Q) := hsimple.toNontrivial
      exact (QuotientGroup.mk_surjective (s := Subgroup.center Q)).nontrivial
    exact ⟨hnt, (Group.isPerfect_def).1 hperf, hsimple⟩
  apply CFSG.GorensteinWalter.quasisimple_not_quotient_isTwoGroup hgw
  obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
  apply IsPGroup.of_card (n := k)
  show (pPrimeCore 2 Q).index = 2 ^ k
  rw [hidx]
  exact hk

theorem sylow_quaternion_of_quasisimple
    {Q : Type} [Group Q] [Finite Q] (hq : CFSG.IsQuasisimple Q)
    (hno : ∀ u v : Q, orderOf u = 2 → orderOf v = 2 → u * v = v * u → u = v)
    (P : Sylow 2 Q) (h16 : 16 ∣ Nat.card ↥(P : Subgroup Q)) :
    ∃ n : ℕ, 2 ≤ n ∧ Nonempty (QuaternionGroup (2 ^ n) ≃* ↥(P : Subgroup Q)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hncyc := sylow_two_not_cyclic_of_quasisimple hq P
  have hrank : NoCommutingDistinctInvolutions ↥(P : Subgroup Q) := by
    intro u v huv
    have hu : orderOf ((u.1 : ↥(P : Subgroup Q)) : Q) = 2 := by
      rw [Subgroup.orderOf_coe]
      exact u.2
    have hv : orderOf ((v.1 : ↥(P : Subgroup Q)) : Q) = 2 := by
      rw [Subgroup.orderOf_coe]
      exact v.2
    have hcomm : ((u.1 : ↥(P : Subgroup Q)) : Q) * ((v.1 : ↥(P : Subgroup Q)) : Q) =
        ((v.1 : ↥(P : Subgroup Q)) : Q) * ((u.1 : ↥(P : Subgroup Q)) : Q) := by
      have := congrArg (fun x : ↥(P : Subgroup Q) => (x : Q)) huv
      simpa using this
    exact Subtype.ext (Subtype.ext (hno _ _ hu hv hcomm))
  rcases rank_one_two_cyclic_or_quaternion P.isPGroup' hrank with hc | ⟨e, he1, ⟨ε⟩⟩
  · exact absurd hc hncyc
  · refine ⟨e, ?_, ⟨ε⟩⟩
    by_contra hlt
    have he : e = 1 := by omega
    subst he
    have hcard : Nat.card ↥(P : Subgroup Q) = 8 := by
      rw [← Nat.card_congr ε.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
      norm_num
    rw [hcard] at h16
    omega

theorem sylow_exists_noncomm
    {Q : Type} [Group Q] [Finite Q] (hq : CFSG.IsQuasisimple Q)
    (hno : ∀ u v : Q, orderOf u = 2 → orderOf v = 2 → u * v = v * u → u = v) (P : Sylow 2 Q) :
    ∃ a ∈ (P : Subgroup Q), ∃ b ∈ (P : Subgroup Q), a * b ≠ b * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hncyc := sylow_two_not_cyclic_of_quasisimple hq P
  have hrank : NoCommutingDistinctInvolutions ↥(P : Subgroup Q) := by
    intro u v huv
    have hu : orderOf ((u.1 : ↥(P : Subgroup Q)) : Q) = 2 := by
      rw [Subgroup.orderOf_coe]
      exact u.2
    have hv : orderOf ((v.1 : ↥(P : Subgroup Q)) : Q) = 2 := by
      rw [Subgroup.orderOf_coe]
      exact v.2
    have hcomm : ((u.1 : ↥(P : Subgroup Q)) : Q) * ((v.1 : ↥(P : Subgroup Q)) : Q) =
        ((v.1 : ↥(P : Subgroup Q)) : Q) * ((u.1 : ↥(P : Subgroup Q)) : Q) := by
      have := congrArg (fun x : ↥(P : Subgroup Q) => (x : Q)) huv
      simpa using this
    exact Subtype.ext (Subtype.ext (hno _ _ hu hv hcomm))
  rcases rank_one_two_cyclic_or_quaternion P.isPGroup' hrank with hc | ⟨e, he1, ⟨ε⟩⟩
  · exact absurd hc hncyc
  · refine ⟨(ε (QuaternionGroup.a 1) : Q), (ε (QuaternionGroup.a 1)).2,
      (ε (QuaternionGroup.xa 0) : Q), (ε (QuaternionGroup.xa 0)).2, fun h => ?_⟩
    have h1 : ε (QuaternionGroup.a 1) * ε (QuaternionGroup.xa 0) =
        ε (QuaternionGroup.xa 0) * ε (QuaternionGroup.a 1) := Subtype.ext h
    rw [← map_mul, ← map_mul] at h1
    have h2 := ε.injective h1
    rw [QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_a] at h2
    have h3 := QuatAut.xa_inj h2
    have h4 : (2 : ZMod (2 * 2 ^ e)) = 0 := by linear_combination (-1 : ZMod (2 * 2 ^ e)) * h3
    have h5 : (((2 : ℕ)) : ZMod (2 * 2 ^ e)) = 0 := by exact_mod_cast h4
    rw [ZMod.natCast_eq_zero_iff] at h5
    have h6 := Nat.le_of_dvd (by norm_num) h5
    have h7 : 1 ≤ 2 ^ e := Nat.one_le_two_pow
    have h8 : 2 ≤ 2 ^ e := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he1
    omega

end Basics

section SL2Part

variable {F : Type} [Field F] [Finite F] {Q : Type} [Group Q]

theorem sixteen_dvd_card_of_fAut (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F)
    (e : Q ≃* SpecialLinearGroup (Fin 2) F) (φ : MulAut Q) (hφ2 : φ * φ = 1) (hφ1 : φ ≠ 1)
    (hf : FixedCond Q φ) : 16 ∣ Nat.card Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hα2 : MulAut.congr e φ * MulAut.congr e φ = 1 := by rw [← map_mul, hφ2, map_one]
  have hα1 : MulAut.congr e φ ≠ 1 := fun h =>
    hφ1 ((MulAut.congr e).injective (h.trans (map_one _).symm))
  have hσ1 : (gammaOf hodd h3 (MulAut.congr e φ)).right ≠ 1 := by
    intro hσ
    obtain ⟨G, hG⟩ := eq_slConjugation_of_right_eq_one hodd h3 _ hσ
    apply not_fixedCond_of_comm φ _ hf
    apply comm_fixed_of_congr e φ
    rw [hG]
    exact fixed_comm_of_slConjugation G (hG ▸ hα1)
  have hγ2 : gammaOf hodd h3 (MulAut.congr e φ) * gammaOf hodd h3 (MulAut.congr e φ) = 1 := by
    rw [← map_mul, hα2, map_one]
  have hσσ : (gammaOf hodd h3 (MulAut.congr e φ)).right * (gammaOf hodd h3 (MulAut.congr e φ)).right = 1 := by
    have := congrArg SemidirectProduct.right hγ2
    simpa using this
  have hord : orderOf (gammaOf hodd h3 (MulAut.congr e φ)).right = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hσσ) hσ1
  obtain ⟨σ, hσdef⟩ : ∃ σ : F ≃+* F, σ = (gammaOf hodd h3 (MulAut.congr e φ)).right := ⟨_, rfl⟩
  rw [← hσdef] at hord
  have hq : Nat.card ↥(fixedField σ) ^ 2 = Nat.card F := by
    simpa [hord] using fixedField_card_pow σ
  have hq₀odd : Odd (Nat.card ↥(fixedField σ)) := odd_card_fixedField σ hodd
  have hcard : Nat.card Q = Nat.card F * (Nat.card F ^ 2 - 1) := by
    rw [Nat.card_congr e.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
  rw [hcard]
  obtain ⟨s, hs⟩ := hq₀odd
  obtain ⟨t, ht⟩ := Nat.even_mul_succ_self s
  have hF8 : Nat.card F = 8 * t + 1 := by
    rw [← hq, hs]
    nlinarith [ht]
  have hF2 : Nat.card F ^ 2 - 1 = 16 * (4 * t ^ 2 + t) := by
    rw [hF8]
    have : (8 * t + 1) ^ 2 = 16 * (4 * t ^ 2 + t) + 1 := by ring
    omega
  rw [hF2]
  exact Dvd.dvd.mul_left (dvd_mul_right 16 _) _

end SL2Part

section Dict

open CFSG.GH74.GLS.Stage1.Thm2.Recip (II4_44 IsSL2Or2A7 innOf)

variable {Q : Type} [Group Q] [Finite Q]

theorem dict_cent
    (h2A7 : II4_2A7) (hO : HatOK Q) (φ : MulAut Q) (hφ : IsFAutomorphism Q φ)
    (hφ1 : φ ≠ 1) (hφ2 : φ * φ = 1) (P : Sylow 2 Q)
    (hPφ : ∀ p ∈ (P : Subgroup Q), φ p ∈ (P : Subgroup Q)) :
    ∃ y ∈ (P : Subgroup Q), orderOf y = 4 ∧ φ y = y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases sl_or_a7 hO.sl2 with ⟨F, _, _, hodd, h3, ⟨e⟩⟩ | h7
  · have hno := noCommInv_of_pRank hO.rank
    obtain ⟨r, hr4, hrφ⟩ := exists_fixed_order_four_elt hno φ hφ.2.2.2.2
    have h16Q := sixteen_dvd_card_of_fAut hodd h3 e φ hφ2 hφ1 hφ.2.2.2.2
    have h16 : 16 ∣ Nat.card ↥(P : Subgroup Q) := by
      have hmul := Subgroup.card_mul_index (P : Subgroup Q)
      have hcop : Nat.Coprime 16 (P : Subgroup Q).index := by
        have h2 : Nat.Coprime 2 (P : Subgroup Q).index :=
          (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (Sylow.not_dvd_index P)
        have : (16 : ℕ) = 2 ^ 4 := by norm_num
        rw [this]
        exact Nat.Coprime.pow_left 4 h2
      rw [← hmul] at h16Q
      exact hcop.dvd_of_dvd_mul_right h16Q
    obtain ⟨n, hn, ⟨ε⟩⟩ := sylow_quaternion_of_quasisimple hO.quasi hno P h16
    exact exists_fixed_order_four φ hφ2 r hr4 hrφ P hPφ n hn ε
  · have hP2 : IsSylow2In (P : Subgroup Q) ⊤ :=
      ⟨le_top, P.isPGroup', by rw [Subgroup.relIndex_top_right]; exact Sylow.not_dvd_index P⟩
    exact (h2A7 Q h7).2.2.2.2.2.2 φ hφ hφ1 P hP2 hPφ

end Dict

section Core

open CFSG.GH74.GLS.Stage1.Thm2.Recip (II4_44 IsSL2Or2A7 innOf)

variable {G : Type} [Group G] [Finite G]

theorem f_cent_core
    (h2A7 : II4_2A7) {z : G} {S K : Subgroup G} (hOK : HatOK (Hat K))
    (hSp : IsPGroup 2 ↥S) (hzK : z ∈ K) (hz2 : orderOf z = 2)
    (hKC : K ≤ centralizer ({z} : Set G))
    (hSyl : ∃ P : Sylow 2 ↥K, (P : Subgroup ↥K).map K.subtype = S ⊓ K)
    {t : G} (htS : t ∈ S) (htN : t ∈ normalizer (K : Set G))
    (hF : IsFAutomorphism (Hat K) (phi K t htN)) (ht1 : t ∉ cSec K) (ht2 : t * t ∈ cSec K) :
    ∃ y ∈ S ⊓ K, y * y = z ∧ y * t = t * y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := hSyl
  let Pbar : Sylow 2 (Hat K) := P.mapSurjective (hatMk_surjective K)
  have hPbar : (Pbar : Subgroup (Hat K)) = (P : Subgroup ↥K).map (hatMk K) :=
    Sylow.coe_mapSurjective (hatMk_surjective K) P
  have hPsub : (S ⊓ K).subgroupOf K = (P : Subgroup ↥K) := by
    rw [← hP]
    exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
  have hPimg : (Pbar : Subgroup (Hat K)) = hatImg K (S ⊓ K) := by
    rw [hPbar, hatImg_eq_map, hPsub]
  have hφ1 : phi K t htN ≠ 1 := fun h1 => ht1 ((phi_eq_one_iff K htN).1 h1)
  have hφ2 : phi K t htN * phi K t htN = 1 := by
    rw [← phi_mul K htN htN]
    exact (phi_eq_one_iff K (mul_mem htN htN)).2 ht2
  have hSS : S ⊓ K ≤ K := inf_le_right
  have hSSp : IsPGroup 2 ↥(S ⊓ K) := hSp.to_inf_left
  have hinv : ∀ a ∈ S ⊓ K, t * a * t⁻¹ ∈ S ⊓ K := fun a ha =>
    ⟨S.mul_mem (S.mul_mem htS ha.1) (S.inv_mem htS), (mem_normalizer_iff.1 htN a).1 ha.2⟩
  have hPφ : ∀ p ∈ (Pbar : Subgroup (Hat K)), phi K t htN p ∈ (Pbar : Subgroup (Hat K)) := by
    intro p hp
    rw [hPimg] at hp ⊢
    exact phi_mem_hatImg htN hinv hp
  obtain ⟨yb, hybP, hyb4, hybφ⟩ := dict_cent h2A7 hOK (phi K t htN) hF hφ1 hφ2 Pbar hPφ
  rw [hPimg] at hybP
  obtain ⟨a, haS, rfl⟩ := mem_hatImg.1 hybP
  have hw : (a : G) * (a : G) ∈ S ⊓ K := mul_mem haS haS
  have hw2 : orderOf ((a : G) * (a : G)) = 2 := by
    have h1 : orderOf (hatMk K ⟨(a : G) * (a : G), hSS hw⟩) = orderOf ((a : G) * (a : G)) :=
      orderOf_hatMk hSS hSSp hw
    rw [← h1]
    have h2 : hatMk K ⟨(a : G) * (a : G), hSS hw⟩ = hatMk K a ^ 2 := by
      rw [sq, ← map_mul]
      rfl
    rw [h2, orderOf_pow' _ (by norm_num : (2 : ℕ) ≠ 0), hyb4]
    norm_num
  have hzcomm : (a : G) * (a : G) * z = z * ((a : G) * (a : G)) :=
    Subgroup.mem_centralizer_singleton_iff.1 (hKC (mul_mem a.2 a.2))
  have hKrank : pRank 2 ↥K = 1 := (pRank_hat K).symm.trans hOK.rank
  have hyyz : (a : G) * (a : G) = z :=
    eq_of_pRank_one hKrank (mul_mem a.2 a.2) hzK hw2 hz2 hzcomm
  have hcomm : (a : G) * t = t * (a : G) := by
    have h1 : hatMk K ⟨t * (a : G) * t⁻¹, (mem_normalizer_iff.mp htN a).mp a.2⟩ = hatMk K a := by
      have := phi_mk K htN a
      rw [hybφ] at this
      exact this.symm
    have h2 := eq_of_hatMk_eq hSS hSSp (hinv _ haS) haS h1
    calc (a : G) * t = (t * (a : G) * t⁻¹) * t := by rw [h2]
      _ = t * (a : G) := by group
  exact ⟨(a : G), haS, hyyz, hcomm⟩

theorem ivk_f_cent_of_II4
    (h44 : II4_44) (h2A7 : II4_2A7) (hII : II4_4_4_center) : IVK_f_cent := by
  intro G _ _ z S K₁ K₂ h K hK t htS hF ht1 ht2
  have hKc : K = K₁ ∨ K = K₂ := by simpa using hK
  obtain ⟨htN, hFa⟩ := hF
  have hOK := std4_hatOK h44 h hK
  have hM := m4_of_std hII h
  have hzK : z ∈ K := hM.z_mem_comp hKc
  have hKC := h.comp_isPCompIn hKc
  have hS : CFSG.QuasithinUnique.IsSylowTwoOf S (centralizer ({z} : Set G)) :=
    CFSG.QuasithinUnique.RankOneRecog.isSylowTwoOf_iff_exists.2 h.sylow
  obtain ⟨Kc, hKcomp, hsub, hmap, hmin⟩ := hKC.2
  have hSK : CFSG.QuasithinUnique.IsSylowTwoOf (S ⊓ K) K :=
    CFSG.QuasithinUnique.RankOneRecog.isSylowTwoOf_inf_of_subnormal hS hKC.1 hsub
  exact f_cent_core h2A7 hOK h.sylow.isPGroup hzK h.orderOf_z hKC.1
    (CFSG.QuasithinUnique.RankOneRecog.isSylowTwoOf_iff_exists.1 hSK) htS htN hFa ht1 ht2

end Core

section R1

open CFSG.GH74.GLS.Stage1.Thm2.Recip (II4_44 IsSL2Or2A7 innOf)

variable {G : Type} [Group G] [Finite G] {z : G} {S K : Subgroup G}

theorem std6r1_inv_zStarK (h : Std6r1 G z S K) {w : G} (hw : w ∈ zStar K) (hw2 : w * w = 1) :
    w = 1 ∨ w = z := by
  by_cases hw1 : w = 1
  · exact Or.inl hw1
  right
  obtain ⟨t₀, ht₀C, ht₀z, ht₀n⟩ := h.thm2
  have hcl := h.classical.2 t₀ ht₀C ht₀z ht₀n
  have hb : CFSG.ABGLocalTools.IsSylowOf 2 (zpowers z) (zStar K) := by
    have := hcl.2.1
    rwa [std6r1_rigidProduct_eq h] at this
  have hb' : M.Syl2In (zpowers z) (zStar K) := syl2In_of_isSylowOf hb
  have hz2 : z * z = 1 := mul_self_eq_one_of_orderOf_eq_two (std6r1_orderOf_z h)
  obtain ⟨W, hW, hwW⟩ := M.exists_syl2In_ge (M.isPGroup_zpowers_of_sq hw2 hw1)
    (zpowers_le.2 hw : zpowers w ≤ zStar K)
  obtain ⟨c, hc, hcW⟩ := hb'.exists_conj hW
  have hcC : c ∈ centralizer ({z} : Set G) := (std6r1_comp_isPCompIn h).1 hc.1
  have hwW' : w ∈ W := hwW (mem_zpowers w)
  rw [hcW, M.cj_zpowers_of_comm hz2 (M.centralizer_comm hcC)] at hwW'
  rcases (M.mem_zpowers_of_sq hz2).1 hwW' with h1 | h1
  · exact absurd h1 hw1
  · exact h1

theorem std6r1_z_mem_S_zStar (hII : II4_4_4_center) (h : Std6r1 G z S K) : z ∈ S ⊓ zStar K := by
  obtain ⟨hcard, -⟩ := hII G h.simple z (std6r1_orderOf_z h) S K h.sylow (std6r1_comp_isPCompIn h)
    (std6r1_comp_pRank h)
  have hex : ∃ w ∈ S ⊓ zStar K, w ≠ 1 := by
    by_contra hne
    push Not at hne
    have : S ⊓ zStar K = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      exact (Subgroup.mem_bot).2 (hne x hx)
    rw [this] at hcard
    simp at hcard
  obtain ⟨w, hw, hw1⟩ := hex
  have hw2 : w * w = 1 := by
    have := pow_card_eq_one' (G := ↥(S ⊓ zStar K)) (x := ⟨w, hw⟩)
    rw [hcard] at this
    have h2 := congrArg Subtype.val this
    simpa [pow_two] using h2
  have hwz : w = z := (std6r1_inv_zStarK h hw.2 hw2).resolve_left hw1
  exact hwz ▸ hw

theorem std6r1_z_mem_K (hII : II4_4_4_center) (h : Std6r1 G z S K) : z ∈ K :=
  (std6r1_z_mem_S_zStar hII h).2.1

theorem ivk_fAut_r1_of_II4
    (h44 : II4_44) (h2A7 : II4_2A7) (hII : II4_4_4_center) :
    IVK_fAut_r1 := by
  intro G _ _ z S K h
  have hOK := std6_hatOK h44 h.toStd6 (std6r1_comp_rigid h)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro b hb hbin
    obtain ⟨hbN, hF⟩ := hb
    have hinn : phi K b hbN ∈ innOf (Hat K) := (phi_mem_inn_iff K hbN).2 (mem_innSub_iff.1 hbin)
    obtain ⟨c, hc⟩ := hinn
    have hcz : c ∈ Subgroup.center (Hat K) := dict_inner h2A7 hOK.sl2 c (by rw [hc]; exact hF)
    have h1 : phi K b hbN = 1 := by rw [← hc]; exact conj_eq_one_of_mem_center hcz
    exact (phi_eq_one_iff K hbN).1 h1
  · intro b hb hbb
    obtain ⟨hbN, hF⟩ := hb
    have hbbN : b * b ∈ normalizer (K : Set G) := mul_mem hbN hbN
    have hphi : phi K (b * b) hbbN = phi K b hbN * phi K b hbN := phi_mul K hbN hbN
    have hin : phi K b hbN * phi K b hbN ∈ innOf (Hat K) := by
      rw [← hphi]
      exact (phi_mem_inn_iff K hbbN).2 (mem_innSub_iff.1 hbb)
    have h1 := dict_sq h2A7 hOK.sl2 _ hF hin
    rw [← hphi] at h1
    exact (phi_eq_one_iff K hbbN).1 h1
  · intro s t hsN htN hss htt htcs hst hft
    obtain ⟨htN', hF⟩ := hft
    have hφ1 : phi K t htN ≠ 1 := fun h1 => htcs ((phi_eq_one_iff K htN).1 h1)
    have hφ2 : phi K t htN * phi K t htN = 1 := by
      rw [← phi_mul K htN htN]
      exact (phi_eq_one_iff K (mul_mem htN htN)).2 htt
    have hψ2 : phi K s hsN * phi K s hsN = 1 := by
      rw [← phi_mul K hsN hsN]
      exact (phi_eq_one_iff K (mul_mem hsN hsN)).2 hss
    have htiN : t⁻¹ ∈ normalizer (K : Set G) := inv_mem htN
    have hstN : s * t⁻¹ ∈ normalizer (K : Set G) := mul_mem hsN htiN
    have hin : phi K s hsN * (phi K t htN)⁻¹ ∈ innOf (Hat K) := by
      have := (phi_mem_inn_iff K hstN).2 (mem_innSub_iff.1 hst)
      rwa [phi_mul K hsN htiN, phi_inv_aux K htN htiN] at this
    exact ⟨hsN, dict_coset h2A7 hOK _ _ hF hφ1 hφ2 hψ2 hin⟩
  · intro t htS hF ht1 ht2
    obtain ⟨htN, hFa⟩ := hF
    exact f_cent_core h2A7 hOK (std6r1_S_pgroup h) (std6r1_z_mem_K hII h) (std6r1_orderOf_z h)
      (std6r1_comp_isPCompIn h).1 (std6r1_exists_sylow_P h) htS htN hFa ht1 ht2

end R1

end CFSG.GH74.GLS.IVK.Lifted
