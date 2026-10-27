module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6HJNormalA
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6CUniqAux2
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DExt

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem barX_eq_top_of_cover {K J : Subgroup G} (hJK : J ≤ K)
    (hcov : K ≤ J ⊔ GLAPPrimeCoreOf 3 K) : barX 3 K J = ⊤ := by
  rw [eq_top_iff]
  intro q _
  induction q using QuotientGroup.induction_on with | H k => ?_
  have hk : (k : G) ∈ J ⊔ GLAPPrimeCoreOf 3 K := hcov k.2
  have hsup : (J.subgroupOf K ⊔ GLAPPrimeCore 3 ↥K).map K.subtype = J ⊔ GLAPPrimeCoreOf 3 K := by
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hJK]
    rfl
  have hk' : k ∈ J.subgroupOf K ⊔ GLAPPrimeCore 3 ↥K := by
    rw [← Subgroup.mem_map_iff_mem K.subtype_injective, hsup]
    exact hk
  obtain ⟨j, hj, n, hn, hjn⟩ := Subgroup.mem_sup_of_normal_right.1 hk'
  refine ⟨j, hj, ?_⟩
  rw [← hjn]
  simp [(QuotientGroup.eq_one_iff n).2 hn]

theorem zclaim (iL3 : InputL3U3Facts) {C K J D F X : Subgroup G}
    (hKC : GLAPComponent 3 C K) (ht : IsLThreeEps (barOf 3 K))
    (hJK : J ≤ K) (hcov : K ≤ J ⊔ GLAPPrimeCoreOf 3 K)
    (hFJ : F ≤ J) (hF3 : IsPGroup 3 F) (hF9 : Nat.card F = 9)
    (hDX : GLAPComponent 3 X D) (hDJ : D ≤ J) (hJX : J ≤ X) :
    ∀ z ∈ D, (∀ d ∈ D, z * d * z⁻¹ * d⁻¹ ∈ GLAPPrimeCoreOf 3 X) → z ∈ GLAPPrimeCoreOf 3 X := by
  intro z hz hzc
  have hq : CFSG.Open.IsQuasisimple (barOf 3 K) :=
    (Lemma512Ns.isQuasisimple_barX_iff Nat.prime_three hKC.2.1).1 hKC.2.2.1.2.2
  have hs : IsSimpleGroup (barOf 3 K) := (iL3 (barOf 3 K) ht).1 hq.1
  have hcen : Subgroup.center (barOf 3 K) = ⊥ := center_eq_bot_of_quasisimple_simple hq hs
  have hJtop : barX 3 K J = ⊤ := barX_eq_top_of_cover hJK hcov
  have hDJ' : IsSubnormal D J := isSubnormal_of_le_of_le hDX.2.1 hDJ hJX
  have hsub : IsSubnormal (barX 3 K D) (⊤ : Subgroup (barOf 3 K)) := by
    have := isSubnormal_barX (C := K) 3 hDJ'
    rwa [hJtop] at this
  have hDK : D ≤ K := hDJ.trans hJK
  have hDOX : D ⊓ GLAPPrimeCoreOf 3 X = GLAPPrimeCoreOf 3 D :=
    glaPPrimeCoreOf_inf_eq_of_isSubnormal Nat.prime_three hDX.2.1
  have hOD_X : GLAPPrimeCoreOf 3 D ≤ GLAPPrimeCoreOf 3 X :=
    glaPPrimeCoreOf_le_of_isSubnormal Nat.prime_three hDX.2.1
  have hDnorm : (D.subgroupOf D).Normal := by
    rw [Subgroup.subgroupOf_self]
    infer_instance
  rcases subnormal_bot_or_top_of_simple hsub rfl with hbot | htop
  · have hDO : D ≤ GLAPPrimeCoreOf 3 K := by
      intro d hd
      have h1 : QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) ⟨d, hDK hd⟩ ∈ barX 3 K D :=
        ⟨⟨d, hDK hd⟩, Subgroup.mem_subgroupOf.2 hd, rfl⟩
      rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact ⟨_, h1, rfl⟩
    have h3 : ¬ 3 ∣ Nat.card D := fun h =>
      not_dvd_card_glaPPrimeCoreOf Nat.prime_three K (h.trans (Subgroup.card_dvd_of_le hDO))
    exact hOD_X (le_glaPPrimeCoreOf_of_normal Nat.prime_three le_rfl hDnorm h3 hz)
  · set N0 : Subgroup G := GLAPPrimeCoreOf 3 D with hN0
    have hN0D : N0 ≤ D := Subgroup.map_subtype_le _
    have hN0K : N0 ≤ GLAPPrimeCoreOf 3 K := by
      have hnorm : (barX 3 K N0).Normal := by
        refine ⟨fun q hq' g => ?_⟩
        obtain ⟨n, hn, rfl⟩ := hq'
        have hg : g ∈ barX 3 K D := htop ▸ Subgroup.mem_top g
        obtain ⟨c, hc, rfl⟩ := hg
        have hnN : (n : G) ∈ N0 := Subgroup.mem_subgroupOf.1 hn
        have hcD : (c : G) ∈ D := Subgroup.mem_subgroupOf.1 hc
        have hcn : (c : G) * n * (c : G)⁻¹ ∈ N0 :=
          (Subgroup.mem_normalizer_iff.1 (le_normalizer_glaPPrimeCoreOf 3 D hcD) n).1 hnN
        refine ⟨c * n * c⁻¹, Subgroup.mem_subgroupOf.2 ?_, by simp⟩
        simpa using hcn
      rcases Subgroup.Normal.eq_bot_or_eq_top (barX 3 K N0) with h | h
      · intro n hn
        have hnK : n ∈ K := hDK (hN0D hn)
        have h1 : QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) ⟨n, hnK⟩ ∈ barX 3 K N0 :=
          ⟨⟨n, hnK⟩, Subgroup.mem_subgroupOf.2 hn, rfl⟩
        rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
        exact ⟨_, h1, rfl⟩
      · exfalso
        have hF9' : Nat.card (barX 3 K F) = 9 := by
          rw [card_barX_of_isPGroup Nat.prime_three (hFJ.trans hJK) hF3, hF9]
        have h3Q : 3 ∣ Nat.card (barOf 3 K) := by
          have := Subgroup.card_subgroup_dvd_card (barX 3 K F)
          rw [hF9'] at this
          exact (dvd_trans (by norm_num : 3 ∣ 9) this)
        have hcardN : Nat.card (barX 3 K N0) ∣ Nat.card N0 := by
          have h1 : Nat.card (barX 3 K N0) ∣ Nat.card (N0.subgroupOf K) :=
            Subgroup.card_map_dvd _ _
          rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hN0D.trans hDK)).toEquiv] at h1
        rw [h, Subgroup.card_top] at hcardN
        exact not_dvd_card_glaPPrimeCoreOf Nat.prime_three D (h3Q.trans hcardN)
    have hzK : z ∈ K := hDK hz
    have hzcen : (QuotientGroup.mk (⟨z, hzK⟩ : ↥K) : barOf 3 K) ∈ Subgroup.center (barOf 3 K) := by
      rw [Subgroup.mem_center_iff]
      intro q
      have hq' : q ∈ barX 3 K D := htop ▸ Subgroup.mem_top q
      obtain ⟨c, hc, rfl⟩ := hq'
      have hcD : (c : G) ∈ D := Subgroup.mem_subgroupOf.1 hc
      have h1 : z * c * z⁻¹ * (c : G)⁻¹ ∈ GLAPPrimeCoreOf 3 X := hzc c hcD
      have h2 : z * c * z⁻¹ * (c : G)⁻¹ ∈ N0 := by
        rw [← hDOX]
        exact ⟨D.mul_mem (D.mul_mem (D.mul_mem hz hcD) (D.inv_mem hz)) (D.inv_mem hcD), h1⟩
      have h3 : z * c * z⁻¹ * (c : G)⁻¹ ∈ GLAPPrimeCoreOf 3 K := hN0K h2
      have h4 : (⟨z, hzK⟩ * c * ⟨z, hzK⟩⁻¹ * c⁻¹ : ↥K) ∈ GLAPPrimeCore 3 ↥K :=
        (Subgroup.mem_map_iff_mem K.subtype_injective).1 h3
      have h5 : (QuotientGroup.mk (⟨z, hzK⟩ * c * ⟨z, hzK⟩⁻¹ * c⁻¹ : ↥K) : barOf 3 K) = 1 :=
        (QuotientGroup.eq_one_iff _).2 h4
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h5
      exact (commutatorElement_eq_one_iff_mul_comm.1
        (show ⁅(QuotientGroup.mk ⟨z, hzK⟩ : barOf 3 K), (QuotientGroup.mk c : barOf 3 K)⁆ = 1
          from h5)).symm
    rw [hcen, Subgroup.mem_bot] at hzcen
    have hzO : z ∈ GLAPPrimeCoreOf 3 K :=
      ⟨_, (QuotientGroup.eq_one_iff _).1 hzcen, rfl⟩
    have hHD : D ⊓ GLAPPrimeCoreOf 3 K ≤ D := inf_le_left
    have hHnorm : ((D ⊓ GLAPPrimeCoreOf 3 K).subgroupOf D).Normal := by
      rw [Subgroup.normal_subgroupOf_iff hHD]
      intro h d hh hd
      refine ⟨D.mul_mem (D.mul_mem hd hh.1) (D.inv_mem hd), ?_⟩
      exact (Subgroup.mem_normalizer_iff.1 (le_normalizer_glaPPrimeCoreOf 3 K (hDK hd)) h).1 hh.2
    have hHcop : ¬ 3 ∣ Nat.card (D ⊓ GLAPPrimeCoreOf 3 K : Subgroup G) := fun h =>
      not_dvd_card_glaPPrimeCoreOf Nat.prime_three K (h.trans (Subgroup.card_dvd_of_le inf_le_right))
    exact hOD_X (le_glaPPrimeCoreOf_of_normal Nat.prime_three hHD hHnorm hHcop ⟨hz, hzO⟩)

theorem jLayer_le_conj (iL3 : InputL3U3Facts) (iK : InputKType) (h514 : Lemma514)
    {m : ℕ} {B : Subgroup G} {b : G} {L A : Subgroup G} (e : Env m B b L A) {n : G}
    (hn : n ∈ Subgroup.normalizer (A : Set G)) :
    jLayerOf L A ≤ GLBConj n (jLayerOf L A) := by
  have hx := e.X
  set X : Subgroup G := Subgroup.centralizer (A : Set G) with hXdef
  set S : Subgroup G := L ⊓ X with hSdef
  have hbX : X ≤ Subgroup.centralizer ({b} : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact Subgroup.mem_centralizer_iff.1 hy b hx.b_A
  have hSsn : IsSubnormal S X := by
    have := isSubnormal_inf hx.L_comp.2.1 X
    rwa [inf_eq_right.2 hbX] at this
  have hcomp : ∀ D, GLAPComponent 3 S D → GLAPComponent 3 X D := fun D hD =>
    glaPComponent_of_subnormal Nat.prime_three hSsn hD
  have hnX : GLBConj n X = X := gLBConj_centralizer_of_mem_normalizer hn
  have hnA : GLBConj n A = A := mem_normalizer_iff_gLBConj_eq.1 hn
  have hJX : jLayerOf L A ≤ X := (jOf_le' L A).trans inf_le_right
  have hb3 : b ^ 3 = 1 := hx.Bel.2 b hx.b_mem
  have hzb : Nat.card (Subgroup.zpowers b) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hb3 hx.b_ne]
  obtain ⟨a, haA, hab⟩ : ∃ a ∈ A, a ∉ Subgroup.zpowers b := by
    by_contra hcon
    push Not at hcon
    have hle : A ≤ Subgroup.zpowers b := fun a ha => hcon a ha
    have := Subgroup.card_le_of_le hle
    rw [hx.Ac, hzb] at this
    omega
  have ha1 : a ≠ 1 := fun h => hab (h ▸ Subgroup.one_mem _)
  have hKcomp := Ka_comp iL3 hx haA ha1
  have hKty := Ka_type iK e haA ha1
  have hcov : kOf L A a ≤ jLayerOf L A ⊔ GLAPPrimeCoreOf 3 (kOf L A a) :=
    (h514 G m e.S e.C B e.B1 b L A e.w a haA ha1).2 hab
  have hJK : jLayerOf L A ≤ kOf L A a := jOf_le_kOf' L A a
  have hFJ : B ⊓ L ≤ jLayerOf L A := hx.FJ
  have hF3 : IsPGroup 3 ↥(B ⊓ L) := (isPGroup_of_isElemAbelian hx.Bel).to_inf_left
  refine sSup_le (fun D hD => ?_)
  have hDX : GLAPComponent 3 X D := hcomp D hD
  have hDJ : D ≤ jLayerOf L A := le_sSup hD
  by_contra hDn
  obtain ⟨N, hNX, hN1, hN2, hN3⟩ := exists_centralizing_normalizing hDX
  have hconj_le : GLBConj n (jLayerOf L A) ≤ N := by
    have hle : jLayerOf L A ≤ GLBConj n⁻¹ N := by
      refine sSup_le fun D₁ hD₁ y hy => ?_
      have hD₁X : GLAPComponent 3 X D₁ := hcomp D₁ hD₁
      have hD₁n : GLAPComponent 3 X (GLBConj n D₁) := by
        have := glaPComponent_gLBConj hD₁X n
        rwa [hnX] at this
      have hne : GLBConj n D₁ ≠ D := by
        intro h
        apply hDn
        rw [← h]
        exact gLBConj_mono n (le_sSup hD₁)
      have hmem : n⁻¹ * y * n ∈ GLBConj n D₁ := by
        rw [mem_gLBConj]
        simpa [mul_assoc] using hy
      have := hN1 _ hD₁n hne hmem
      rw [mem_gLBConj]
      simpa using this
    have := gLBConj_mono n hle
    rwa [gLBConj_gLBConj_inv] at this
  set P : Subgroup G := GLBConj n (B ⊓ L) with hPdef
  have hPN : P ≤ N := (gLBConj_mono n hFJ).trans hconj_le
  have hPexp : ∀ p ∈ P, p ^ 3 = 1 := by
    intro p hp
    rw [hPdef, mem_gLBConj] at hp
    have h3 := hx.Bel.2 _ hp.1
    rw [conj_pow] at h3
    calc p ^ 3 = n⁻¹ * (n * p ^ 3 * n⁻¹) * n := by group
      _ = 1 := by rw [h3]; group
  have hP3 : IsPGroup 3 ↥P := fun g => ⟨1, Subtype.ext (by simpa using hPexp g g.2)⟩
  have hPD : P ≤ Subgroup.normalizer (D : Set G) := fun p hp => hN3 p (hPN hp)
  have h3D : 3 ∣ Nat.card D := three_dvd_card_of_glaPComponent hDX
  have hfact : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨T, hTD, hT3, hTord, hPT⟩ :=
    Sec6C.exists_sylow_normalized_of_isPGroup (p := 3) D P hP3 hPD
  have h3T : 3 ∣ Nat.card T := by
    have := hTord 1 (by simpa using h3D)
    simpa using this
  have hT1 : T ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at h3T
    omega
  obtain ⟨w, hwT, hw1, hwP⟩ :=
    Sec6C.exists_ne_one_mem_centralizer_of_isPGroup (p := 3) T P hT3 hT1 hP3 hPT
  have hwD : w ∈ D := hTD hwT
  obtain ⟨k, hk⟩ := hT3 ⟨w, hwT⟩
  have hwk : w ^ (3 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have hord : orderOf w ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hwk
  have hwo1 : orderOf w ≠ 1 := fun h => hw1 (orderOf_eq_one_iff.1 h)
  have h3o : 3 ∣ orderOf w := by
    obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hord
    have hj0 : j ≠ 0 := by
      rintro rfl
      exact hwo1 (by simpa using hj')
    rw [hj']
    exact dvd_pow_self 3 hj0
  set s : G := w ^ (orderOf w / 3) with hsdef
  have hs3 : orderOf s = 3 :=
    orderOf_pow_orderOf_div (ne_of_gt (orderOf_pos w)) h3o
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hs3
    omega
  have hs3' : s ^ 3 = 1 := by
    rw [← hs3]
    exact pow_orderOf_eq_one s
  have hsD : s ∈ D := D.pow_mem hwD _
  have hsP : ∀ p ∈ P, p * s = s * p := fun p hp =>
    (Commute.pow_right (show Commute p w from hwP p hp) _).eq
  have hsA : ∀ a ∈ A, a * s = s * a := fun a ha =>
    Subgroup.mem_centralizer_iff.1 (hDX.1 hsD) a ha
  have hBn : GLBConj n B = A ⊔ P := by
    have e1 : GLBConj n (A ⊔ (B ⊓ L)) = GLBConj n A ⊔ GLBConj n (B ⊓ L) :=
      Subgroup.map_sup _ _ _
    rw [hx.BAF, hnA] at e1
    exact e1
  have hsB : s ∈ GLBConj n B := by
    refine mem_conj_of_isSCp hx.SC (fun y hy => ?_) hs3'
    rw [hBn] at hy
    have hle : A ⊔ P ≤ Subgroup.centralizer ({s} : Set G) := by
      refine sup_le (fun a ha => ?_) (fun p hp => ?_)
      · rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        rw [hh]
        exact (hsA a ha).symm
      · rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        rw [hh]
        exact (hsP p hp).symm
    exact (Subgroup.mem_centralizer_iff.1 (hle hy) s (Set.mem_singleton s)).symm
  have hcentP : A ≤ Subgroup.centralizer (P : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    have hp' : n * p * n⁻¹ ∈ B ⊓ L := mem_gLBConj.1 hp
    have ha' : n * a * n⁻¹ ∈ A := by
      have : a ∈ GLBConj n A := by rw [hnA]; exact ha
      exact mem_gLBConj.1 this
    have hcomm := ea_comm hx.Bel (hx.AB ha') hp'.1
    calc p * a = n⁻¹ * ((n * p * n⁻¹) * (n * a * n⁻¹)) * n := by group
      _ = n⁻¹ * ((n * a * n⁻¹) * (n * p * n⁻¹)) * n := by rw [← hcomm]
      _ = a * p := by group
  rw [hBn] at hsB
  obtain ⟨a', ha', p', hp', hsap⟩ := exists_mul_of_mem_sup hcentP hsB
  have hz : ∀ d ∈ D, s * d * s⁻¹ * d⁻¹ ∈ GLAPPrimeCoreOf 3 X := by
    intro d hd
    have hp'N : p' ∈ N := hPN hp'
    have hu : p' * d * p'⁻¹ ∈ D :=
      (Subgroup.mem_normalizer_iff.1 (hN3 p' hp'N) d).1 hd
    have h1 : a' * (p' * d * p'⁻¹) * a'⁻¹ = p' * d * p'⁻¹ := by
      have := Subgroup.mem_centralizer_iff.1 (hDX.1 hu) a' ha'
      rw [this]
      group
    have h2 := hN2 p' hp'N d hd
    rw [hsap]
    have heq : a' * p' * d * (a' * p')⁻¹ * d⁻¹ = p' * d * p'⁻¹ * d⁻¹ := by
      calc a' * p' * d * (a' * p')⁻¹ * d⁻¹
          = (a' * (p' * d * p'⁻¹) * a'⁻¹) * d⁻¹ := by group
        _ = p' * d * p'⁻¹ * d⁻¹ := by rw [h1]
    rw [heq]
    exact h2
  have hsO := zclaim iL3 hKcomp hKty hJK hcov hFJ hF3 hx.Fc hDX hDJ hJX s hsD hz
  exact hs1 (Sec6C.eq_one_of_pow_three_mem_glaPPrimeCoreOf hsO hs3')

theorem jNormalA_of_inputs (iL3 : InputL3U3Facts) (iK : InputKType) (h514 : Lemma514) :
    InputJNormalA := by
  intro G _ _ m hS hC B hB b L A hw n hn
  have e : Env m B b L A := ⟨hS, hC, hB, hw, exists_extCtx hS hC hB hw⟩
  have h1 := jLayer_le_conj iL3 iK h514 e hn
  have h2 := jLayer_le_conj iL3 iK h514 e (inv_mem hn)
  have h3 : GLBConj n (jLayerOf L A) ≤ jLayerOf L A := by
    have := gLBConj_mono n h2
    rwa [gLBConj_gLBConj_inv] at this
  exact mem_normalizer_iff_gLBConj_eq.2 (le_antisymm h3 h1)

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
