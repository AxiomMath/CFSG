module

public import CFSG.GH74.GLS.Stage1.Thm4.P92Ext
public import CFSG.GH74.GLS.Stage1.Thm4.Inv98
public import CFSG.GH74.Generic.OuterInvolution
public import CFSG.GH74.GLS.Bg.Iii2.L41Main

public section

namespace CFSG.GH74.GLS.Stage1.Thm4.P92

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.ABGLocalTools
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {Lh : Type} [Group Lh] {n : ℕ}

theorem exists_start (E : Env G Lh n)
    (hpair : ∃ (x : G) (L : Subgroup G), IsTwoTerminal x L ∧ Nonempty (HatT L ≃* Lh)) :
    ∃ (z : G) (J : Subgroup G), IsRigidOfType Lh z J := by
  obtain ⟨x, L, hterm, ⟨e⟩⟩ := hpair
  have hZ : center (↥L ⧸ pPrimeCore 2 ↥L) ≠ ⊥ := by
    intro h
    have h2 : Nat.card (center (HatT L)) = 2 :=
      (Nat.card_congr (Subgroup.centerCongr e).toEquiv).trans E.hL.2.1
    rw [h, Subgroup.card_bot] at h2
    exact absurd h2 (by norm_num)
  obtain ⟨z, L', hP, ⟨e'⟩⟩ := Bg.Iii2.L41.exists_goodPair E.hR hterm hZ
  exact ⟨z, L', Bg.Iii2.L41.isPRigid_of_goodPair hP, ⟨e'.trans e⟩⟩

theorem Oz_inf_le {z : G} {J : Subgroup G} (hJ : IsRigidOfType Lh z J) :
    Oz z ⊓ J ≤ pPrimeCoreOf 2 J := by
  intro x hx
  have hmem : (⟨x, hx.2⟩ : ↥J) ∈ (phiK (rig_le_cen hJ)).ker := (mem_ker_phiK (rig_le_cen hJ)).mpr hx.1
  rw [L97.phiK_ker (rig_le_cen hJ) (rig_pcomp hJ).2] at hmem
  exact Bg.Iii2.mem_pPrimeCoreOf_iff.mpr ⟨hx.2, hmem⟩

omit [Finite G] in
theorem mem_normalizer_pPrimeCoreOf' {J : Subgroup G} {t : G} (ht : t ∈ normalizer (J : Set G)) :
    t ∈ normalizer ((pPrimeCoreOf 2 J : Subgroup G) : Set G) := by
  have h1 : Thm3.Sec4.cmap t J = J := Subgroup.mem_normalizer_iff_map_conj_eq.mp ht
  have h2 := Thm3.Sec4.pPrimeCoreOf_cmap t J
  rw [h1] at h2
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h2.symm

theorem comm_eq_of_not_le (E : Env G Lh n) {z t : G} {J : Subgroup G} (hJ : IsRigidOfType Lh z J)
    (htC : t ∈ centralizer ({z} : Set G)) (hnle : ¬ ⁅J, zpowers t⁆ ≤ pPrimeCoreOf 2 J) :
    ⁅J, zpowers t⁆ = J := by
  have hKC : J ≤ Cz z := rig_le_cen hJ
  have hcomp : IsPComponent 2 (J.subgroupOf (Cz z)) := (rig_pcomp hJ).2
  have htN : t ∈ normalizer (J : Set G) := E.norm hJ htC
  have hnorm : (⟨t, htC⟩ : ↥(Cz z)) ∈
      normalizer ((J.subgroupOf (Cz z) : Subgroup ↥(Cz z)) : Set ↥(Cz z)) := by
    refine Subgroup.mem_normalizer_iff.2 fun x => ?_
    exact Subgroup.mem_normalizer_iff.1 htN (x : G)
  have hnle' : ¬ ⁅J.subgroupOf (Cz z), zpowers (⟨t, htC⟩ : ↥(Cz z))⁆ ≤ pPrimeCore 2 ↥(Cz z) := by
    intro hle
    apply hnle
    have h1 := Subgroup.map_mono (f := (Cz z).subtype) hle
    rw [Subgroup.map_commutator, MonoidHom.map_zpowers, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.2 hKC] at h1
    have hJle : ⁅J, zpowers t⁆ ≤ J :=
      (le_normalizer_iff_commutator_le_left).1 ((Subgroup.zpowers_le).2 htN)
    exact (le_inf h1 hJle).trans (Oz_inf_le hJ)
  have h2 := congrArg (Subgroup.map (Cz z).subtype)
    (commutator_zpowers_eq_of_isPComponent hcomp hnorm hnle')
  rw [Subgroup.map_commutator, MonoidHom.map_zpowers, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.2 hKC] at h2
  exact h2

theorem zStar_inf_le (E : Env G Lh n) {z : G} {J T : Subgroup G} (X : ExtData G Lh z J T)
    (hzs : z ∈ zStar J) {c : G} (hcT : c ∈ T) (hcs : c ∈ zStar J) : c = 1 ∨ c = z := by
  have hzo : orderOf z = 2 := rig_ord X.rigid
  have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hzo; omega
  obtain ⟨e⟩ := X.rigid.2
  have hcen : Nat.card (center (HatT J)) = 2 :=
    (Nat.card_congr (Subgroup.centerCongr e).toEquiv).trans E.hL.2.1
  have hT2 : IsPGroup 2 ↥T := X.sylow.isPGroup
  have h2el : ∀ g ∈ T, ∃ k : ℕ, g ^ (2 ^ k) = 1 := fun g hg => by
    obtain ⟨k, hk⟩ := hT2 ⟨g, hg⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  have hzJ : z ∈ J := X.mem
  have hcJ : c ∈ J := hcs.1
  have h2el' : ∀ (g : G) (hg : g ∈ T) (hgJ : g ∈ J), ∃ k : ℕ, (⟨g, hgJ⟩ : ↥J) ^ (2 ^ k) = 1 :=
    fun g hg hgJ => by
      obtain ⟨k, hk⟩ := h2el g hg
      exact ⟨k, Subtype.ext (by simpa using hk)⟩
  set a : HatT J := hatMk J ⟨z, hzJ⟩ with ha
  set b : HatT J := hatMk J ⟨c, hcJ⟩ with hb
  have hac : a ∈ center (HatT J) := (Alt51.mem_zStar_iff_hat_mem_center ⟨z, hzJ⟩).1 hzs
  have hbc : b ∈ center (HatT J) := (Alt51.mem_zStar_iff_hat_mem_center ⟨c, hcJ⟩).1 hcs
  have ha1 : a ≠ 1 := by
    intro h
    have := Alt51.eq_one_of_hat_eq_one ⟨z, hzJ⟩ h (h2el' z X.zT hzJ)
    exact hz1 (congrArg Subtype.val this)
  by_cases hb1 : b = 1
  · left
    have := Alt51.eq_one_of_hat_eq_one ⟨c, hcJ⟩ hb1 (h2el' c hcT hcJ)
    exact congrArg Subtype.val this
  · right
    have hab : b = a := by
      obtain ⟨y, hy1, hy⟩ := (Nat.card_eq_two_iff' (1 : ↥(center (HatT J)))).1 hcen
      have h1 : (⟨b, hbc⟩ : ↥(center (HatT J))) = y := hy _ (fun h => hb1 (congrArg Subtype.val h))
      have h2 : (⟨a, hac⟩ : ↥(center (HatT J))) = y := hy _ (fun h => ha1 (congrArg Subtype.val h))
      exact congrArg Subtype.val (h1.trans h2.symm)
    have := Alt51.eq_of_hat_eq (K := J) ⟨c, hcJ⟩ ⟨z, hzJ⟩ hab (h2el' c hcT hcJ) (h2el' z X.zT hzJ)
      (Subtype.ext (X.central c hcT))
    exact congrArg Subtype.val this

omit [Finite G] in
private theorem exists_sylow_of_isSylowOf_top [Finite G] {T : Subgroup G} (h : IsSylowOf 2 T ⊤) :
    ∃ S : Sylow 2 G, (S : Subgroup G) = T := by
  have h' := isSylowOf_iff.1 h
  refine ⟨h'.2.1.toSylow ?_, rfl⟩
  rw [← Subgroup.relIndex_top_right]; exact h'.2.2

theorem exists_good (E : Env G Lh n) {z : G} {J T : Subgroup G} (X : ExtData G Lh z J T) :
    ∃ t : G, Good92 G Lh z t J := by
  have hzo : orderOf z = 2 := rig_ord X.rigid
  have hzz : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hzo, sq] at this
  have hTz : T ≤ centralizer ({z} : Set G) := fun t ht =>
    Subgroup.mem_centralizer_singleton_iff.mpr (X.central t ht)
  have hTC : IsSylowOf 2 T (centralizer ({z} : Set G)) := X.sylow.of_le hTz le_top
  have hP : IsSylowOf 2 (T ⊓ J) J := sylow_inf X.rigid hTC
  obtain ⟨e⟩ := X.rigid.2
  have hzs : z ∈ zStar J :=
    (a4n E.rank4 E.n8 E.n11 E.hL e hP hzz (fun p hp => (X.central p hp.1).symm)).2
  obtain ⟨S, hS⟩ := exists_sylow_of_isSylowOf_top X.sylow
  obtain ⟨g, hgT, hgne⟩ := CFSG.GH74.Generic.exists_conj_in_sylow_ne E.std.kps.1 E.std.kps.2.1 hzo S
    (hS ▸ X.zT) (fun t ht => X.central t (hS ▸ ht))
  have hgT' : g⁻¹ * z * g ∈ T := hS ▸ hgT
  set t : G := g⁻¹ * z * g with ht
  have hto : orderOf t = 2 := by
    have h1 : orderOf t = orderOf z := by
      rw [ht]
      simpa using orderOf_conj_eq g⁻¹ z
    rw [h1, hzo]
  have htt : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [hto, sq] at this
  have ht1 : t ≠ 1 := fun h => by rw [h, orderOf_one] at hto; omega
  have htC : t ∈ centralizer ({z} : Set G) := hTz hgT'
  have htN : t ∈ normalizer (J : Set G) := E.norm X.rigid htC
  have hnot : t ∉ centralizerSection J (pPrimeCoreOf 2 J) := by
    intro htc
    have hcomm : ∀ p ∈ T ⊓ J, t * p = p * t := by
      intro p hp
      have h1 : ⁅p, t⁆ ∈ pPrimeCoreOf 2 J := htc.2.2 p hp.2
      have h2 : ⁅p, t⁆ ∈ T :=
        T.mul_mem (T.mul_mem (T.mul_mem hp.1 hgT') (T.inv_mem hp.1)) (T.inv_mem hgT')
      have h3 : ⁅p, t⁆ ∈ T ⊓ pPrimeCoreOf 2 J := ⟨h2, h1⟩
      rw [Bg.Iii2.inf_pPrimeCoreOf_eq_bot X.sylow.isPGroup, Subgroup.mem_bot] at h3
      exact (commutatorElement_eq_one_iff_mul_comm.1 h3).symm
    obtain ⟨htP, hts⟩ := a4n E.rank4 E.n8 E.n11 E.hL e hP htt hcomm
    rcases zStar_inf_le E X hzs htP.1 hts with h | h
    · exact ht1 h
    · exact hgne h
  have hnle : ¬ ⁅J, zpowers t⁆ ≤ pPrimeCoreOf 2 J := by
    intro hle
    apply hnot
    refine ⟨htN, mem_normalizer_pPrimeCoreOf' htN, fun k hk => ?_⟩
    exact hle (Subgroup.commutator_mem_commutator hk (Subgroup.mem_zpowers t))
  refine ⟨t, ⟨hzo, hto, htC, X.rigid, X.mem, ⟨g⁻¹, ?_⟩, comm_eq_of_not_le E X.rigid htC hnle, hnle⟩⟩
  rw [E.kz_eq X.rigid]
  have : (g⁻¹)⁻¹ * t * g⁻¹ = z := by rw [ht]; group
  rw [this]
  exact hzs

end CFSG.GH74.GLS.Stage1.Thm4.P92

namespace CFSG.GH74.GLS.Stage1.Thm4

theorem prop9_2_proved : Prop9_2 := by
  intro G _ _ Lh _ h
  obtain ⟨n, hn8, hn11, hL⟩ := h.cover
  have E : P92.Env G Lh n := ⟨h.std, hn8, hn11, hL⟩
  obtain ⟨z₀, J₀, h0⟩ := P92.exists_start E h.pair
  obtain ⟨z, J, T, X⟩ := P92.exists_ext E ⟨z₀, J₀, h0⟩
  obtain ⟨t, ht⟩ := P92.exists_good E X
  exact ⟨z, t, J, ht⟩

end CFSG.GH74.GLS.Stage1.Thm4
