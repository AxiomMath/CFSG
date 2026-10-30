module

public import CFSG.LocalAnalysis.GLTheoremA.S4S.Inputs
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3Bridge
public import CFSG.ClassicalInvolution.SubnormalCommutator
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_5STr
public import CFSG.HardMathSupport.Solomon.Coordinator.Generation228
public import CFSG.LocalAnalysis.GLTheoremA.P51.SCp
public import CFSG.LocalAnalysis.AGLEmbedding.TheoremZAux
public import CFSG.LocalAnalysis.GLTheoremA.Lemma44
public import CFSG.LocalAnalysis.GLTheoremA.Sec5A
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def Lemma413At (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  ∀ (B : Subgroup G) (b : G) (K : Subgroup G), GLAIsBmax p B → b ∈ B → b ≠ 1 →
    GLAPComponent p (Subgroup.centralizer ({b} : Set G)) K → IsGStar p B K →
    Odd (Nat.card (⁅closureIn K B, GLAPPrimeCoreOf p (Subgroup.centralizer ({b} : Set G))⁆ :
      Subgroup G))

@[expose] def Lemma414At (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  dLevel G p ≤ 2 → ∀ (B : Subgroup G) (x : G) (T : Subgroup G), GLAIsBmax p B → x ∈ B → x ≠ 1 →
    T ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G)) → IsPGroup 2 T →
    B ≤ Subgroup.normalizer (T : Set G) → (⁅T, B⁆ : Subgroup G) = ⊥

theorem delta_zero_contra {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hΔ : GLADeltaZero G p)
    {B D S : Subgroup G} (hB : GLAIsBmax p B) (hDB : D ≤ B) (hD : IsElemAbelian p D)
    (hDc : Nat.card D = p ^ 2) (hS : IsPGroup 2 S) (hSΔ : S ≤ GLADelta p D)
    (hBS : B ≤ Subgroup.normalizer (S : Set G)) (hne : (⁅S, B⁆ : Subgroup G) ≠ ⊥) : False := by
  obtain ⟨h5, h3⟩ := hΔ B hB D hDB hD hDc
  have hSB : (⁅S, B⁆ : Subgroup G) ≤ S := by
    rw [Subgroup.commutator_le]
    intro s hs b hb
    rw [commutatorElement_def]
    have h1 : b * s⁻¹ * b⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.1 (hBS hb) s⁻¹).1 (S.inv_mem hs)
    simpa [mul_assoc] using S.mul_mem hs h1
  have h2 : 2 ∣ Nat.card (⁅S, B⁆ : Subgroup G) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hP : IsPGroup 2 (⁅S, B⁆ : Subgroup G) := hS.to_le hSB
    haveI : Nontrivial (⁅S, B⁆ : Subgroup G) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
    obtain ⟨n, hn, hcard⟩ := hP.nontrivial_iff_card.1 inferInstance
    rw [hcard]
    exact dvd_pow_self 2 hn.ne'
  by_cases hp3 : p = 3
  · subst hp3
    have hle : (⁅S, B⁆ : Subgroup G) ≤ ⁅GLADelta 3 D, B⁆ := Subgroup.commutator_mono hSΔ le_rfl
    have hdvd : Nat.card (⁅S, B⁆ : Subgroup G) ∣ Nat.card (⁅GLADelta 3 D, B⁆ : Subgroup G) :=
      Subgroup.card_dvd_of_le hle
    exact (Nat.not_even_iff_odd.2 (h3 rfl)) (even_iff_two_dvd.2 (h2.trans hdvd))
  · have hp5 : 5 ≤ p := by
      have h2' := hp.two_le
      have hp4 : p ≠ 4 := by
        rintro rfl
        exact absurd hp (by decide)
      omega
    have hdvd : Nat.card (⁅S, B⁆ : Subgroup G) ∣ Nat.card (GLADelta p D) :=
      Subgroup.card_dvd_of_le (hSB.trans hSΔ)
    exact (Nat.not_even_iff_odd.2 (h5 hp5)) (even_iff_two_dvd.2 (h2.trans hdvd))

theorem exists_invariant_sylow_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {B X : Subgroup G}
    (hB : IsPGroup p B) (hBX : B ≤ Subgroup.normalizer (X : Set G))
    (hX : Nat.Coprime p (Nat.card X)) :
    ∃ R : Subgroup G, R ≤ X ∧ IsPGroup 2 R ∧ ¬ 2 ∣ R.relIndex X ∧
      B ≤ Subgroup.normalizer (R : Set G) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnd : ¬ p ∣ Nat.card X := (Nat.Prime.coprime_iff_not_dvd hp).1 hX
  obtain ⟨Q, hQX, hQ2, hQn, hBQ⟩ :=
    exists_sylow_normalized_of_not_dvd (q := 2) X B hB hBX hnd
  refine ⟨Q, hQX, hQ2, ?_, hBQ⟩
  intro h2
  obtain ⟨k, hk⟩ := hQ2.exists_card_eq
  have hmul : Q.relIndex X * Nat.card Q = Nat.card X := by
    have := Subgroup.relIndex_mul_card (H := Q) (K := X)
    rwa [inf_eq_left.2 hQX] at this
  have hdvd : 2 ^ (k + 1) ∣ Nat.card X := by
    rw [← hmul, hk, pow_succ, mul_comm]
    exact Nat.mul_dvd_mul h2 (dvd_refl _)
  have := hQn (k + 1) hdvd
  rw [hk] at this
  have h3 := Nat.le_of_dvd (by positivity) this
  have h4 : 2 ^ k < 2 ^ (k + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

theorem isMaxRankIn_of_even {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {B Y N : Subgroup G}
    (hB : GLAIsBmax p B) (hN2 : Even (Nat.card N)) (hNp : Nat.Coprime p (Nat.card N))
    (hYN : Y ≤ Subgroup.normalizer (N : Set G)) : IsMaxRankIn p B Y := by
  intro E hEY hE
  obtain ⟨R, hRN, hR2, hRidx, hER⟩ :=
    exists_invariant_sylow_two hp hp2 (isPGroup_of_isElemAbelian hE) (hEY.trans hYN) hNp
  have hR : R ≠ ⊥ := by
    rintro rfl
    apply hRidx
    have hmul := Subgroup.relIndex_mul_card (H := (⊥ : Subgroup G)) (K := N)
    rw [bot_inf_eq, Subgroup.card_bot, mul_one] at hmul
    rw [hmul]
    exact even_iff_two_dvd.1 hN2
  have := card_le_pow_glaTwoLocalRank hp hE hR hR2 hER
  rw [hB.2.1]
  exact this

theorem gLADelta_zpowers {p : ℕ} (hp : p.Prime) {x : G} (hx : x ^ p = 1) (hx1 : x ≠ 1) :
    GLADelta p (Subgroup.zpowers x) = GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G)) := by
  have hcard : Nat.card (Subgroup.zpowers x) = p := card_zpowers_eq_of_pow hp hx hx1
  apply le_antisymm
  · exact iInf₂_le_of_le x (Subgroup.mem_zpowers x) (iInf_le_of_le hx1 le_rfl)
  · refine le_iInf fun d => le_iInf fun hd => le_iInf fun hd1 => ?_
    have hdle : Subgroup.zpowers d ≤ Subgroup.zpowers x := Subgroup.zpowers_le.2 hd
    have hdcard : Nat.card (Subgroup.zpowers d) = p := by
      have hdp : d ^ p = 1 := by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hd
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]
      exact card_zpowers_eq_of_pow hp hdp hd1
    have heq : Subgroup.zpowers d = Subgroup.zpowers x :=
      Subgroup.eq_of_le_of_card_ge hdle (by rw [hcard, hdcard])
    have hC : Subgroup.centralizer ({d} : Set G) = Subgroup.centralizer ({x} : Set G) := by
      rw [← Subgroup.centralizer_closure ({d} : Set G), ← Subgroup.centralizer_closure ({x} : Set G),
        ← Subgroup.zpowers_eq_closure, ← Subgroup.zpowers_eq_closure, heq]
    rw [hC]

theorem fullCoverLevel_le_four (p : ℕ) (Q : Type) [Group Q] : fullCoverLevel p Q ≤ 4 := by
  classical
  unfold fullCoverLevel
  split_ifs <;> omega

theorem fullCoverLevel_eq_dLevel {p : ℕ} {B L : Subgroup G} {x : G} (h : IsS0 p B x L)
    (hnG : ¬ IsGStar p B L) : fullCoverLevel p (PQuot p L) = dLevel G p := by
  have h2 := h.2
  unfold tripleLevel at h2
  rw [if_neg hnG] at h2
  have h4 := fullCoverLevel_le_four p (PQuot p L)
  omega

theorem k1Cover_or_k2Cover_of_fullCoverLevel_le_two {p : ℕ} {Q : Type} [Group Q]
    (h : fullCoverLevel p Q ≤ 2) : K1Cover p Q ∨ K2Cover p Q := by
  classical
  unfold fullCoverLevel at h
  by_cases h1 : K1Cover p Q
  · exact Or.inl h1
  · rw [if_neg h1] at h
    by_cases h2 : K2Cover p Q
    · exact Or.inr h2
    · rw [if_neg h2] at h
      by_cases h3 : K3Cover p Q
      · rw [if_pos h3] at h
        omega
      · rw [if_neg h3] at h
        omega

theorem k3Cover_of_fullCoverLevel_eq_three {p : ℕ} {Q : Type} [Group Q]
    (h : fullCoverLevel p Q = 3) : K3Cover p Q := by
  classical
  unfold fullCoverLevel at h
  by_cases h1 : K1Cover p Q
  · rw [if_pos h1] at h
    omega
  · rw [if_neg h1] at h
    by_cases h2 : K2Cover p Q
    · rw [if_pos h2] at h
      omega
    · rw [if_neg h2] at h
      by_cases h3 : K3Cover p Q
      · exact h3
      · rw [if_neg h3] at h
        omega

theorem eq_three_of_k3Cover {p : ℕ} {Q : Type} [Group Q] (h : K3Cover p Q) : p = 3 := by
  obtain ⟨-, h | h | h⟩ := h
  · obtain ⟨-, i, hi, -⟩ := h
    cases i <;> first | exact hi.1 | exact hi.elim
  · exact h.1
  · obtain ⟨i, hi, -⟩ := h
    cases i <;> first | exact hi.1 | exact hi.elim

theorem commutator_self_le {M : Type*} [Group M] (S : Subgroup M) : (⁅S, S⁆ : Subgroup M) ≤ S := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact S.mul_mem (S.mul_mem (S.mul_mem ha hb) (S.inv_mem ha)) (S.inv_mem hb)

theorem ne_bot_of_even {X R : Subgroup G} (hR : ¬ 2 ∣ R.relIndex X) (hX : Even (Nat.card X)) :
    R ≠ ⊥ := by
  rintro rfl
  apply hR
  have hmul := Subgroup.relIndex_mul_card (H := (⊥ : Subgroup G)) (K := X)
  rw [bot_inf_eq, Subgroup.card_bot, mul_one] at hmul
  rw [hmul]
  exact even_iff_two_dvd.1 hX

theorem le_normalizer_commutator {A H K : Subgroup G} (hH : A ≤ Subgroup.normalizer (H : Set G))
    (hK : A ≤ Subgroup.normalizer (K : Set G)) :
    A ≤ Subgroup.normalizer ((⁅H, K⁆ : Subgroup G) : Set G) := by
  intro g hg
  rw [mem_normalizer_iff_gLBConj_eq]
  have h1 := mem_normalizer_iff_gLBConj_eq.1 (hH hg)
  have h2 := mem_normalizer_iff_gLBConj_eq.1 (hK hg)
  unfold GLBConj at h1 h2 ⊢
  rw [Subgroup.map_commutator, h1, h2]

theorem le_normalizer_inf {A H K : Subgroup G} (hH : A ≤ Subgroup.normalizer (H : Set G))
    (hK : A ≤ Subgroup.normalizer (K : Set G)) : A ≤ Subgroup.normalizer ((H ⊓ K : Subgroup G) : Set G) := by
  intro g hg
  rw [mem_normalizer_iff_gLBConj_eq]
  have h1 := mem_normalizer_iff_gLBConj_eq.1 (hH hg)
  have h2 := mem_normalizer_iff_gLBConj_eq.1 (hK hg)
  rw [gLBConj_inf, h1, h2]

theorem le_normalizer_sup {A H K : Subgroup G} (hH : A ≤ Subgroup.normalizer (H : Set G))
    (hK : A ≤ Subgroup.normalizer (K : Set G)) :
    A ≤ Subgroup.normalizer ((H ⊔ K : Subgroup G) : Set G) := by
  intro g hg
  rw [mem_normalizer_iff_gLBConj_eq]
  have h1 := mem_normalizer_iff_gLBConj_eq.1 (hH hg)
  have h2 := mem_normalizer_iff_gLBConj_eq.1 (hK hg)
  unfold GLBConj at h1 h2 ⊢
  rw [Subgroup.map_sup, h1, h2]

theorem commutator_le_left_of_normalizes {A J : Subgroup G}
    (hJ : J ≤ Subgroup.normalizer (A : Set G)) : (⁅A, J⁆ : Subgroup G) ≤ A := by
  rw [Subgroup.commutator_le]
  intro a ha j hj
  rw [commutatorElement_def]
  have h1 : j * a⁻¹ * j⁻¹ ∈ A := by
    have := (Subgroup.mem_normalizer_iff.1 (hJ hj) a⁻¹).1 (A.inv_mem ha)
    exact this
  simpa [mul_assoc] using A.mul_mem ha h1

theorem i326UsedAt_holds (p : ℕ) :
    p.Prime → p ≠ 2 → ∀ B D : Subgroup G, GLAIsBmax p B → D ≤ B → D ≠ ⊥ →
      Even (Nat.card (GLAPPrimeCoreOf p (Subgroup.centralizer (D : Set G)))) → IsSC p B := by
  intro hp hp2 B D hB hDB hD heven
  refine ⟨hB.1, ?_⟩
  intro g hg hord
  by_contra hgB
  have hBel : IsElemAbelian p B := hB.1
  have hgp : g ^ p = 1 := hord ▸ pow_orderOf_eq_one g
  have hz : ∀ e ∈ B, e * g = g * e := fun e he => Subgroup.mem_centralizer_iff.1 hg e he
  have hEel : IsElemAbelian p (B ⊔ Subgroup.zpowers g) :=
    IsElemAbelian.sup_of_commute hBel (CFSG.Open.isElemAbelian_zpowers hgp) (by
      intro a ha b hb
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      exact ((show Commute a g from hz a ha).zpow_right k).eq)
  have hgE : g ∈ B ⊔ Subgroup.zpowers g := Subgroup.mem_sup_right (Subgroup.mem_zpowers g)
  have hBE : B ≤ B ⊔ Subgroup.zpowers g := le_sup_left
  have hEC : B ⊔ Subgroup.zpowers g ≤ Subgroup.centralizer (D : Set G) := by
    refine sup_le ?_ ?_
    · intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      exact isElemAbelian_commute hBel (hDB hd) hb
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_iff.2 (fun d hd => hz d (hDB hd))
  have hcop : Nat.Coprime p (Nat.card (GLAPPrimeCoreOf p (Subgroup.centralizer (D : Set G)))) :=
    (hp.coprime_iff_not_dvd).2 (not_dvd_card_glaPPrimeCoreOf hp _)
  have hmax := isMaxRankIn_of_even hp hp2 hB heven hcop
    (hEC.trans (le_normalizer_glaPPrimeCoreOf p (Subgroup.centralizer (D : Set G))))
  have hle := hmax (B ⊔ Subgroup.zpowers g) le_rfl hEel
  have hEB : B = B ⊔ Subgroup.zpowers g := Subgroup.eq_of_le_of_card_ge hBE hle
  exact hgB (by rw [hEB]; exact hgE)

theorem i321UsedAt_holds (p : ℕ) : I321UsedAt G p := by
  intro hp A J hcop hJA hres
  haveI : Fact p.Prime := ⟨hp⟩
  set C : Subgroup G := ⁅⁅A, J⁆, J⁆ with hCdef
  have hJN1 : J ≤ Subgroup.normalizer ((⁅A, J⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator hJA Subgroup.le_normalizer
  have hJC : J ≤ Subgroup.normalizer (C : Set G) :=
    le_normalizer_commutator hJN1 Subgroup.le_normalizer
  have hconj : ∀ g ∈ J, ∀ x ∈ C, g * x * g⁻¹ ∈ C := fun g hg x hx =>
    (Subgroup.mem_normalizer_iff.1 (hJC hg) x).1 hx
  let Q : Subgroup G :=
    { carrier := {g | g ∈ J ∧ ∀ a ∈ A, ⁅a, g⁆ ∈ C}
      mul_mem' := by
        rintro g h ⟨hg, hgA⟩ ⟨hh, hhA⟩
        refine ⟨J.mul_mem hg hh, fun a ha => ?_⟩
        have e : ⁅a, g * h⁆ = ⁅a, g⁆ * (g * ⁅a, h⁆ * g⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact C.mul_mem (hgA a ha) (hconj g hg _ (hhA a ha))
      one_mem' := ⟨J.one_mem, fun a _ => by rw [commutatorElement_one_right]; exact C.one_mem⟩
      inv_mem' := by
        rintro g ⟨hg, hgA⟩
        refine ⟨J.inv_mem hg, fun a ha => ?_⟩
        have e : ⁅a, g⁻¹⁆ = g⁻¹ * ⁅a, g⁆⁻¹ * g⁻¹⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact hconj g⁻¹ (J.inv_mem hg) _ (C.inv_mem (hgA a ha)) }
  have hQmem : ∀ g ∈ Q, g ∈ J ∧ ∀ a ∈ A, ⁅a, g⁆ ∈ C := fun g hg => hg
  let P : Sylow p ↥J := default
  set R : Subgroup G := P.toSubgroup.map J.subtype with hRdef
  have hRJ : R ≤ J := Subgroup.map_subtype_le _
  have hRA : R ≤ Subgroup.normalizer (A : Set G) := hRJ.trans hJA
  have hRcop : Nat.Coprime (Nat.card R) (Nat.card A) := by
    have hcard : Nat.card R = Nat.card P.toSubgroup := by
      rw [hRdef]
      exact Subgroup.card_map_of_injective Subtype.val_injective
    obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
    rw [hcard, hk]
    exact Nat.Coprime.pow_left k hcop
  have hPidx : Nat.Coprime p P.toSubgroup.index :=
    (Nat.Prime.coprime_iff_not_dvd hp).2 (Sylow.not_dvd_index P)
  have hARC : (⁅A, R⁆ : Subgroup G) ≤ C :=
    (CFSG.ClassicalInvolution.commutator_le_commutator_commutator_of_coprime A R hRA hRcop).trans
      (Subgroup.commutator_mono (Subgroup.commutator_mono le_rfl hRJ) hRJ)
  have hRQ : R ≤ Q := fun g hg => ⟨hRJ hg, fun a ha =>
    hARC (Subgroup.commutator_mem_commutator ha hg)⟩
  have hPQ : P.toSubgroup ≤ Q.subgroupOf J := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    exact hRQ (Subgroup.mem_map_of_mem J.subtype hx)
  have hQn : (Q.subgroupOf J).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    obtain ⟨hnJ, hnA⟩ := hQmem _ hn
    refine ⟨J.mul_mem (J.mul_mem g.2 hnJ) (J.inv_mem g.2), fun a ha => ?_⟩
    have hga : (g : G)⁻¹ * a * (g : G) ∈ A := by
      have := (Subgroup.mem_normalizer_iff.1 (hJA (J.inv_mem g.2)) a).1 ha
      rwa [inv_inv] at this
    have e : ⁅a, (g : G) * (n : G) * (g : G)⁻¹⁆ =
        (g : G) * ⁅(g : G)⁻¹ * a * (g : G), (n : G)⁆ * (g : G)⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact hconj _ g.2 _ (hnA _ hga)
  have hQcop : Nat.Coprime p (Q.subgroupOf J).index :=
    Nat.Coprime.coprime_dvd_right (Subgroup.index_dvd_of_le hPQ) hPidx
  have hQJ : Q = J := hres Q (fun g hg => (hQmem g hg).1) hQn hQcop
  have hJQ : J ≤ Q := le_of_eq hQJ.symm
  refine le_antisymm (commutator_le_left_of_normalizes hJN1) ?_
  rw [Subgroup.commutator_le]
  intro a ha g hg
  exact (hQmem g (hJQ hg)).2 a ha

theorem i145_of_oPrimeFree (h : Input14_5Print) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (X : Type)
    [Group X] [Finite X] (hK : CFSG.Open.IsKGroup X) (hO : GLAPPrimeCore p X = ⊥) (D : Subgroup X)
    (hD : IsPGroup p D) :
    ⁅GLAPLayer p (Subgroup.centralizer (D : Set X)),
      GLAPPrimeCoreOf p (Subgroup.centralizer (D : Set X))⁆ = ⊥ := by
  by_cases hD1 : D = ⊥
  · subst hD1
    have hC : Subgroup.centralizer (((⊥ : Subgroup X)) : Set X) = ⊤ := by simp
    have hcore : GLAPPrimeCoreOf p (⊤ : Subgroup X) = ⊥ := by
      have h1 := glaPPrimeCore_map_iso p (Subgroup.topEquiv (G := X))
      rw [hO] at h1
      have hsub : (⊤ : Subgroup X).subtype = (Subgroup.topEquiv (G := X)).toMonoidHom :=
        MonoidHom.ext fun _ => rfl
      unfold GLAPPrimeCoreOf
      rw [hsub, h1]
    rw [hC, hcore]
    exact Subgroup.commutator_bot_right _
  · have hsub : IsSubnormal (Subgroup.centralizer (D : Set X)) (Subgroup.normalizer (D : Set X)) :=
      IsSubnormal.step (Subgroup.centralizer_le_normalizer _) inferInstance (IsSubnormal.refl _)
    have hL : GLAPLayer p (Subgroup.centralizer (D : Set X)) ≤
        GLAPLayer p (Subgroup.normalizer (D : Set X)) := by
      unfold GLAPLayer
      exact sSup_le fun J hJ => le_sSup (glaPComponent_of_isSubnormal' hp hsub hJ)
    have hO' : GLAPPrimeCoreOf p (Subgroup.centralizer (D : Set X)) ≤
        GLAPPrimeCoreOf p (Subgroup.normalizer (D : Set X)) :=
      CFSG.LocalAnalysis.GLTheoremB.glaPPrimeCoreOf_le_of_isSubnormal hp hsub
    exact le_bot_iff.1 ((Subgroup.commutator_mono hL hO').trans
      (h X hK p hp hp2 hO D hD1 hD).le)

theorem i145UsedAt_of_oPrimeFree (p : ℕ)
    (hh : p.Prime → p ≠ 2 → ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X →
      GLAPPrimeCore p X = ⊥ → ∀ D : Subgroup X, IsPGroup p D →
        ⁅GLAPLayer p (Subgroup.centralizer (D : Set X)),
          GLAPPrimeCoreOf p (Subgroup.centralizer (D : Set X))⁆ = ⊥) :
    I145UsedAt G p := by
  intro hp hp2 X D hK hDX hD
  haveI : Fact p.Prime := ⟨hp⟩
  have hD' : IsPGroup p (D.subgroupOf X) := hD.comap_subtype
  set D' : Subgroup ↥X := D.subgroupOf X with hD'def
  set C' : Subgroup ↥X := Subgroup.centralizer (D' : Set ↥X) with hC'def
  have hkerX : Nat.Coprime p (Nat.card ↥(C' ⊓ X.subtype.ker)) := by
    rw [Subgroup.ker_subtype, inf_bot_eq, Subgroup.card_bot]; exact Nat.coprime_one_right p
  have hF1 : X ⊓ Subgroup.centralizer (D : Set G) = C'.map X.subtype := by
    ext x
    constructor
    · rintro ⟨hxX, hxC⟩
      have hxC' : x ∈ Subgroup.centralizer (D : Set G) := hxC
      refine ⟨⟨x, hxX⟩, Subgroup.mem_centralizer_iff.2 ?_, rfl⟩
      intro h hh'
      have hh2 : h ∈ D' := hh'
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.1 hxC' (h : G) (Subgroup.mem_subgroupOf.1 hh2)
    · rintro ⟨c, hc, rfl⟩
      refine ⟨c.2, Subgroup.mem_centralizer_iff.2 ?_⟩
      intro d hd
      have hc' : c ∈ Subgroup.centralizer (D' : Set ↥X) := hc
      have h1 := Subgroup.mem_centralizer_iff.1 hc' ⟨d, hDX hd⟩ (Subgroup.mem_subgroupOf.2 hd)
      exact congrArg Subtype.val h1
  have hF2 : GLAPLayer p (X ⊓ Subgroup.centralizer (D : Set G)) =
      (GLAPLayer p C').map X.subtype := by
    rw [hF1]; exact i145s_layer_map hp X.subtype hkerX
  have hF3 : GLAPPrimeCoreOf p (X ⊓ Subgroup.centralizer (D : Set G)) =
      (GLAPPrimeCoreOf p C').map X.subtype := by
    rw [hF1]; exact (i145s_primeCoreOf_map hp X.subtype C' hkerX).symm
  have hOcop : Nat.Coprime p (Nat.card ↥(GLAPPrimeCore p ↥X)) := CFSG.pPrimeCore_coprime_card
  have hOnd : ¬ p ∣ Nat.card ↥(GLAPPrimeCore p ↥X) := (Nat.Prime.coprime_iff_not_dvd hp).1 hOcop
  set ψ : ↥X →* ↥X ⧸ GLAPPrimeCore p ↥X := QuotientGroup.mk' (GLAPPrimeCore p ↥X) with hψdef
  have hker : ψ.ker = GLAPPrimeCore p ↥X := QuotientGroup.ker_mk' _
  have hcopC : Nat.Coprime p (Nat.card ↥(C' ⊓ ψ.ker)) := by
    rw [hker]; exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right) hOcop
  have hCψ : C'.map ψ = Subgroup.centralizer ((D'.map ψ : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X)) :
      Set (↥X ⧸ GLAPPrimeCore p ↥X)) := by
    ext y
    constructor
    · rintro ⟨c, hc, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨d, hd, rfl⟩
      show ψ d * ψ c = ψ c * ψ d
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.1 hc d hd]
    · intro hy
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore p ↥X) y
      have hy' : ∀ a ∈ D', x⁻¹ * (a * x * a⁻¹) ∈ GLAPPrimeCore p ↥X := by
        intro a ha
        have h1 : ψ a * ψ x = ψ x * ψ a :=
          Subgroup.mem_centralizer_iff.1 hy (ψ a) (Subgroup.mem_map_of_mem ψ ha)
        have h2 : ψ (x⁻¹ * (a * x * a⁻¹)) = 1 := by
          simp only [map_mul, map_inv]
          rw [h1]
          group
        rw [← hker]
        exact MonoidHom.mem_ker.2 h2
      have hD'N : D' ≤ Subgroup.normalizer (GLAPPrimeCore p ↥X : Set ↥X) :=
        le_top.trans (Subgroup.normalizer_eq_top_iff.2 inferInstance).ge
      obtain ⟨n, hn, hxn⟩ := Generation228.exists_fixed_mem_coset hp hD' hD'N hOnd hy'
      have hψn : ψ n = 1 := MonoidHom.mem_ker.1 (by rw [hker]; exact hn)
      exact Subgroup.mem_map.2 ⟨x * n, hxn, by rw [map_mul, hψn, mul_one]⟩
  have hXbar : CFSG.Open.IsKGroup (↥X ⧸ GLAPPrimeCore p ↥X) := hK.quotient _
  have hO0 : GLAPPrimeCore p (↥X ⧸ GLAPPrimeCore p ↥X) = ⊥ := glaPPrimeCore_quotient_eq_bot hp
  have hDbar : IsPGroup p (D'.map ψ) := hD'.map ψ
  have hbot := hh hp hp2 (↥X ⧸ GLAPPrimeCore p ↥X) hXbar hO0 (D'.map ψ) hDbar
  rw [← hCψ] at hbot
  have hbad := i145s_bad_map hp ψ C' hcopC
  have hmapbot : (⁅GLAPLayer p C', GLAPPrimeCoreOf p C'⁆).map ψ = ⊥ := by
    rw [← hbad]; exact hbot
  have hkey : ⁅GLAPLayer p C', GLAPPrimeCoreOf p C'⁆ ≤ GLAPPrimeCore p ↥X := by
    intro x hx
    have h1 : ψ x ∈ (⁅GLAPLayer p C', GLAPPrimeCoreOf p C'⁆).map ψ :=
      Subgroup.mem_map_of_mem ψ hx
    rw [hmapbot, Subgroup.mem_bot] at h1
    rw [← hker]
    exact MonoidHom.mem_ker.2 h1
  rw [hF2, hF3, ← Subgroup.map_commutator]
  exact Subgroup.map_mono hkey

theorem i145UsedAt_of (h : Input14_5Print) (p : ℕ) : I145UsedAt G p :=
  i145UsedAt_of_oPrimeFree p fun hp hp2 X _ _ hK hO D hD => i145_of_oPrimeFree h hp hp2 X hK hO D hD

theorem layer_isOPrimeResidual {p : ℕ} (hp : p.Prime) (X : Subgroup G) :
    ∀ N : Subgroup G, N ≤ GLAPLayer p X → (N.subgroupOf (GLAPLayer p X)).Normal →
      Nat.Coprime p (N.subgroupOf (GLAPLayer p X)).index → N = GLAPLayer p X := by
  intro N hN hNn hidx
  refine le_antisymm hN ?_
  refine sSup_le fun T hT => ?_
  exact i183_le_of_coprime_index (A := GLAPLayer p X) hp (show GLAPComponent p X T from hT)
    (le_sSup hT) hidx

theorem dvd_card_pQuot_of_component {p : ℕ} (hp : p.Prime) {X H : Subgroup G}
    (hH : GLAPComponent p X H) : p ∣ Nat.card (PQuot p H) := by
  by_contra hdvd
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Nontrivial (PQuot p H) := isQuasisimple_nontrivial
    (isQuasisimple_pQuot_of_glaPComponent hp hH)
  have hKc : Nat.Coprime p (Nat.card (GLAPPrimeCore p ↥H)) := CFSG.pPrimeCore_coprime_card
  have hcard : Nat.card ↥H = Nat.card (PQuot p H) * Nat.card (GLAPPrimeCore p ↥H) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hcop : Nat.Coprime p (Nat.card (⊤ : Subgroup ↥H)) := by
    rw [Nat.card_congr Subgroup.topEquiv.toEquiv, hcard]
    exact Nat.Coprime.mul_right ((Nat.Prime.coprime_iff_not_dvd hp).2 hdvd) hKc
  have htop : (⊤ : Subgroup ↥H) ≤ GLAPPrimeCore p ↥H := le_sSup ⟨inferInstance, hcop⟩
  obtain ⟨x, hx⟩ := exists_ne (1 : PQuot p H)
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
  exact hx ((QuotientGroup.eq_one_iff h).2 (htop (Subgroup.mem_top h)))

private theorem le_normalizer_closureIn_S4S (I H : Subgroup G) :
    H ≤ Subgroup.normalizer (closureIn I H : Set G) := by
  intro h hh
  rw [mem_normalizer_iff_gLBConj_eq, closureIn_eq_iSup_gLBConj I H]
  have hsup : GLBConj h (⨆ g ∈ H, GLBConj g I) = ⨆ g ∈ H, GLBConj h (GLBConj g I) := by
    unfold GLBConj
    simp only [Subgroup.map_iSup]
  rw [hsup]
  apply le_antisymm
  · refine iSup₂_le fun g hg => ?_
    rw [gLBConj_gLBConj]
    exact le_biSup (fun g => GLBConj g I) (H.mul_mem hg hh)
  · refine iSup₂_le fun g hg => ?_
    have e : GLBConj g I = GLBConj h (GLBConj (g * h⁻¹) I) := by
      rw [gLBConj_gLBConj, inv_mul_cancel_right]
    rw [e]
    exact le_biSup (fun g' => GLBConj h (GLBConj g' I)) (H.mul_mem hg (H.inv_mem hh))

theorem le_closureIn_of_isSC {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {B J : Subgroup G}
    (hB : IsElemAbelian p B) (hSC : IsSC p B) (hBJ : B ≤ Subgroup.normalizer (J : Set G))
    (hJ : GLAPLayer p J = J) : J ≤ closureIn B J := by
  haveI : Fact p.Prime := ⟨hp⟩
  set M : Subgroup G := closureIn B J with hMdef
  have hBM : B ≤ M := le_closureIn_self B J
  have hJN : J ≤ Subgroup.normalizer (M : Set G) := le_normalizer_closureIn_S4S B J
  have hOJ : GLAPPrimeCoreOf p J ≤ J := by
    unfold GLAPPrimeCoreOf; exact Subgroup.map_subtype_le _
  have hJO : J ≤ Subgroup.normalizer (GLAPPrimeCoreOf p J : Set G) :=
    le_normalizer_glaPPrimeCoreOf p J
  have hOcop : p.Coprime (Nat.card (GLAPPrimeCoreOf p J)) := i183_coprime_card_glaPPrimeCoreOf hp J
  have hON : GLAPPrimeCoreOf p J ≤ Subgroup.normalizer (M : Set G) := hOJ.trans hJN
  have hconj : ∀ t ∈ J, ∀ b ∈ B, t * b * t⁻¹ ∈ M := by
    intro t ht b hb
    have hle : B.map (MulAut.conj t).toMonoidHom ≤ M :=
      le_iSup₂ (f := fun (a : G) (_ : a ∈ J) => B.map (MulAut.conj a).toMonoidHom) t ht
    exact hle (Subgroup.mem_map_of_mem _ hb)
  have hcomm : ∀ t ∈ J, ∀ b ∈ B, ⁅t, b⁆ ∈ M := by
    intro t ht b hb
    rw [commutatorElement_def]
    exact M.mul_mem (hconj t ht b hb) (M.inv_mem (hBM hb))
  have hmaxAll : ∀ E : Subgroup G, IsElemAbelian p E → B ≤ E → E = B := by
    intro E hE hBE
    apply le_antisymm _ hBE
    intro e he
    by_cases he1 : e = 1
    · rw [he1]; exact B.one_mem
    · apply hSC.2 e _ (orderOf_eq_prime (hE.2 e he) he1)
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact (isElemAbelian_commute hE he (hBE hb)).symm
  have hcompM : ∀ T : Subgroup G, GLAPComponent p J T → T ≤ M ⊔ GLAPPrimeCoreOf p J := by
    intro T hT
    by_cases hBT : B ≤ Subgroup.normalizer (T : Set G)
    · have h1 := P51.le_commutator_of_maximal hp hp2 hT hB hBT
        (fun E hE hBE _ => hmaxAll E hE hBE)
      have h2 : (⁅T, B⁆ : Subgroup G) ≤ M := by
        rw [Subgroup.commutator_le]
        intro t ht b hb
        exact hcomm t (hT.1 ht) b hb
      exact (h1.trans h2).trans le_sup_left
    · obtain ⟨b, hb, hbT⟩ : ∃ b ∈ B, b ∉ Subgroup.normalizer (T : Set G) := by
        by_contra hcon
        push Not at hcon
        exact hBT (fun b hb => hcon b hb)
      have hbJ : b⁻¹ ∈ Subgroup.normalizer (J : Set G) := hBJ (B.inv_mem hb)
      have hT' : GLAPComponent p J (GLBConj b⁻¹ T) := by
        have h := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_gLBConj hT b⁻¹
        rwa [mem_normalizer_iff_gLBConj_eq.1 hbJ] at h
      have hne : T ≠ GLBConj b⁻¹ T := by
        intro h
        apply hbT
        have hn : b⁻¹ ∈ Subgroup.normalizer (T : Set G) := mem_normalizer_iff_gLBConj_eq.2 h.symm
        simpa using Subgroup.inv_mem _ hn
      have hcomm' : (⁅T, GLBConj b⁻¹ T⁆ : Subgroup G) ≤ GLAPPrimeCoreOf p J :=
        commutator_le_gLAPPrimeCore_of_ne hp hT hT' hne
      have hperf := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hT
      have hcommT : (⁅T, T⁆ : Subgroup G) ≤ M ⊔ GLAPPrimeCoreOf p J := by
        rw [Subgroup.commutator_le]
        intro s hs t ht
        have hu : b * t⁻¹ * b⁻¹ ∈ GLBConj b⁻¹ T := by
          rw [mem_gLBConj]
          have e : b⁻¹ * (b * t⁻¹ * b⁻¹) * b⁻¹⁻¹ = t⁻¹ := by group
          rw [e]; exact T.inv_mem ht
        have hsJ : s ∈ J := hT.1 hs
        have htJ : t ∈ J := hT.1 ht
        have hc : t * (b * t⁻¹ * b⁻¹) ∈ M := by
          have e : t * (b * t⁻¹ * b⁻¹) = ⁅t, b⁆ := by rw [commutatorElement_def]; group
          rw [e]; exact hcomm t htJ b hb
        have hsu : ⁅s, b * t⁻¹ * b⁻¹⁆ ∈ GLAPPrimeCoreOf p J :=
          hcomm' (Subgroup.commutator_mem_commutator hs hu)
        have hsuJ : t * ⁅s, b * t⁻¹ * b⁻¹⁆ * t⁻¹ ∈ GLAPPrimeCoreOf p J :=
          (Subgroup.mem_normalizer_iff.1 (hJO htJ) _).1 hsu
        have hsc : ⁅s, t * (b * t⁻¹ * b⁻¹)⁆ ∈ M := by
          have h1 : s * (t * (b * t⁻¹ * b⁻¹)) * s⁻¹ ∈ M :=
            (Subgroup.mem_normalizer_iff.1 (hJN hsJ) _).1 hc
          rw [commutatorElement_def]
          exact M.mul_mem h1 (M.inv_mem hc)
        have key : ⁅s, t⁆ = ⁅s, t * (b * t⁻¹ * b⁻¹)⁆ * (t * ⁅s, b * t⁻¹ * b⁻¹⁆ * t⁻¹)⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [key]
        exact Subgroup.mul_mem_sup hsc ((GLAPPrimeCoreOf p J).inv_mem hsuJ)
      calc T = ⁅T, T⁆ := hperf.symm
        _ ≤ M ⊔ GLAPPrimeCoreOf p J := hcommT
  calc J = GLAPLayer p J := hJ.symm
    _ ≤ M := sSup_le fun T hT =>
        i183_le_of_le_sup hp (show GLAPComponent p J T from hT) hOcop hON
          (hcompM T (show GLAPComponent p J T from hT))

theorem layer_commutator_eq_bot {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hΔ : GLADeltaZero G p)
    {B D J C : Subgroup G} (hB : GLAIsBmax p B) (hSC : IsSC p B) (hDB : D ≤ B)
    (hDel : IsElemAbelian p D) (hDc : Nat.card D = p ^ 2)
    (hBJ : B ≤ Subgroup.normalizer (J : Set G)) (hJL : GLAPLayer p J = J) (hC2 : IsPGroup 2 C)
    (hBC : B ≤ Subgroup.normalizer (C : Set G)) (hJC : J ≤ Subgroup.normalizer (C : Set G))
    (hCΔ : (⁅C, J⁆ : Subgroup G) ≤ GLADelta p D) : (⁅C, J⁆ : Subgroup G) = ⊥ := by
  by_contra hS
  set S : Subgroup G := ⁅C, J⁆ with hSdef
  have hSC' : S ≤ C := commutator_le_left_of_normalizes hJC
  have hS2 : IsPGroup 2 S := hC2.to_le hSC'
  have hBS : B ≤ Subgroup.normalizer (S : Set G) := le_normalizer_commutator hBC hBJ
  have hJS : J ≤ Subgroup.normalizer (S : Set G) :=
    le_normalizer_commutator hJC Subgroup.le_normalizer
  have hcopC : Nat.Coprime p (Nat.card C) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := hC2.exists_card_eq
    rw [hn]
    exact Nat.Coprime.pow_right n ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have hres : ∀ N : Subgroup G, N ≤ J → (N.subgroupOf J).Normal →
      Nat.Coprime p (N.subgroupOf J).index → N = J := by
    have h := layer_isOPrimeResidual hp J
    rw [hJL] at h
    exact h
  have hSJ : (⁅S, J⁆ : Subgroup G) = S := i321UsedAt_holds p hp C J hcopC hJC hres
  have hJB : J ≤ closureIn B J := le_closureIn_of_isSC hp hp2 hB.1 hSC hBJ hJL
  have hSB : (⁅S, B⁆ : Subgroup G) ≠ ⊥ := by
    intro hSB0
    have hBC' : B ≤ Subgroup.centralizer (S : Set G) := by
      intro g hg
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      have hmem : ⁅s, g⁆ ∈ (⁅S, B⁆ : Subgroup G) := Subgroup.commutator_mem_commutator hs hg
      rw [hSB0, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
      exact hmem
    have hJC' : J ≤ Subgroup.centralizer (S : Set G) := by
      refine hJB.trans ?_
      unfold closureIn
      refine iSup₂_le fun a ha => ?_
      rintro _ ⟨g, hg, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      have hs' : a⁻¹ * s * a ∈ S := by
        have := (Subgroup.mem_normalizer_iff.1 (hJS (J.inv_mem ha)) s).1 hs
        simpa using this
      have h1 := Subgroup.mem_centralizer_iff.1 (hBC' hg) _ hs'
      have hc : (MulAut.conj a).toMonoidHom g = a * g * a⁻¹ := rfl
      rw [hc]
      calc s * (a * g * a⁻¹) = a * ((a⁻¹ * s * a) * g) * a⁻¹ := by group
        _ = a * (g * (a⁻¹ * s * a)) * a⁻¹ := by rw [h1]
        _ = (a * g * a⁻¹) * s := by group
    have hJS0 : (⁅S, J⁆ : Subgroup G) = ⊥ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 hJC'
    exact hS (by rw [← hSJ]; exact hJS0)
  exact delta_zero_contra hp hp2 hΔ hB hDB hDel hDc hS2 hCΔ hBS hSB

private theorem glaPLayer_idem_S4S {p : ℕ} (hp : p.Prime) (X : Subgroup G) :
    GLAPLayer p (GLAPLayer p X) = GLAPLayer p X := by
  have hLX : GLAPLayer p X ≤ X := sSup_le fun T hT => (show GLAPComponent p X T from hT).1
  refine le_antisymm (sSup_le fun T hT => (show GLAPComponent p (GLAPLayer p X) T from hT).1) ?_
  refine sSup_le fun T hT => ?_
  have hc : GLAPComponent p (GLAPLayer p X) T :=
    glaPComponent_of_le hp (show GLAPComponent p X T from hT) (le_sSup hT) hLX
  exact le_sSup (show T ∈ {L | GLAPComponent p (GLAPLayer p X) L} from hc)

private theorem glaPLayer_le_self_S4S {p : ℕ} (X : Subgroup G) : GLAPLayer p X ≤ X :=
  sSup_le fun T hT => (show GLAPComponent p X T from hT).1

private theorem glaPLayer_sup_S4S {p : ℕ} (hp : p.Prime) {Y H N : Subgroup G}
    (hHY : H ≤ Y) (hNY : N ≤ Y) (hYN : Y ≤ Subgroup.normalizer (N : Set G))
    (hN : p.Coprime (Nat.card N)) (hY : Y ≤ H ⊔ N) :
    GLAPLayer p Y ≤ GLAPLayer p H ⊔ N ∧ GLAPLayer p H ≤ GLAPLayer p Y ⊔ N := by
  have hHNY : H ⊔ N = Y := le_antisymm (sup_le hHY hNY) hY
  set H' : Subgroup ↥Y := H.subgroupOf Y with hH'
  set N' : Subgroup ↥Y := N.subgroupOf Y with hN'
  haveI : N'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNY).2 hYN
  have hNcop : p.Coprime (Nat.card N') := by
    rw [hN', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNY).toEquiv]
    exact hN
  have hsup : H' ⊔ N' = ⊤ := by
    rw [hH', hN', ← Subgroup.subgroupOf_sup hHY hNY, hHNY, Subgroup.subgroupOf_self]
  set ψ : ↥Y →* ↥Y ⧸ N' := QuotientGroup.mk' N' with hψ
  have hker : ψ.ker = N' := QuotientGroup.ker_mk' N'
  have hT : (⊤ : Subgroup ↥Y).map ψ = ⊤ := by
    rw [← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top_of_surjective ψ (QuotientGroup.mk'_surjective N')]
  have hHt : H'.map ψ = ⊤ := by
    rw [eq_top_iff]
    intro q _
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N' q
    have hy : y ∈ H' ⊔ N' := by rw [hsup]; exact Subgroup.mem_top y
    obtain ⟨h, hh, n, hn, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hy
    have hψn : ψ n = 1 := (QuotientGroup.eq_one_iff n).2 hn
    exact Subgroup.mem_map.2 ⟨h, hh, by rw [map_mul, hψn, mul_one]⟩
  have hkerTop : Nat.Coprime p (Nat.card ↥((⊤ : Subgroup ↥Y) ⊓ ψ.ker)) := by
    rw [top_inf_eq, hker]; exact hNcop
  have hkerH : Nat.Coprime p (Nat.card ↥(H' ⊓ ψ.ker)) := by
    rw [hker]; exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right) hNcop
  have hkey1 : (GLAPLayer p (⊤ : Subgroup ↥Y)).map ψ = (GLAPLayer p H').map ψ := by
    have hL1 := i145s_layer_map hp ψ hkerTop
    have hL2 := i145s_layer_map hp ψ hkerH
    rw [← hL1, ← hL2, hT, hHt]
  have hkeyA : GLAPLayer p (⊤ : Subgroup ↥Y) ≤ GLAPLayer p H' ⊔ N' := by
    intro y hy
    have hy' : ψ y ∈ (GLAPLayer p H').map ψ := by
      rw [← hkey1]; exact Subgroup.mem_map_of_mem ψ hy
    obtain ⟨h, hh, hhy⟩ := Subgroup.mem_map.1 hy'
    have hn : h⁻¹ * y ∈ N' := QuotientGroup.eq.1 hhy
    simpa using Subgroup.mul_mem_sup hh hn
  have hkeyB : GLAPLayer p H' ≤ GLAPLayer p (⊤ : Subgroup ↥Y) ⊔ N' := by
    intro h hh
    have hh' : ψ h ∈ (GLAPLayer p (⊤ : Subgroup ↥Y)).map ψ := by
      rw [hkey1]; exact Subgroup.mem_map_of_mem ψ hh
    obtain ⟨y, hy, hyh⟩ := Subgroup.mem_map.1 hh'
    have hn : y⁻¹ * h ∈ N' := QuotientGroup.eq.1 hyh
    simpa using Subgroup.mul_mem_sup hy hn
  have hkerY : Nat.Coprime p (Nat.card ↥((⊤ : Subgroup ↥Y) ⊓ Y.subtype.ker)) := by
    rw [top_inf_eq, Subgroup.ker_subtype, Subgroup.card_bot]; exact Nat.coprime_one_right p
  have hkerYH : Nat.Coprime p (Nat.card ↥(H' ⊓ Y.subtype.ker)) := by
    rw [Subgroup.ker_subtype, inf_bot_eq, Subgroup.card_bot]; exact Nat.coprime_one_right p
  have hYtop : (⊤ : Subgroup ↥Y).map Y.subtype = Y := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hHtop : H'.map Y.subtype = H := by
    rw [hH', Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hHY]
  have hNtop : N'.map Y.subtype = N := by
    rw [hN', Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hNY]
  have hY1 : GLAPLayer p Y = (GLAPLayer p (⊤ : Subgroup ↥Y)).map Y.subtype := by
    have h := i145s_layer_map hp Y.subtype hkerY
    rw [hYtop] at h
    exact h
  have hH1 : GLAPLayer p H = (GLAPLayer p H').map Y.subtype := by
    have h := i145s_layer_map hp Y.subtype hkerYH
    rw [hHtop] at h
    exact h
  constructor
  · rw [hY1, hH1]
    calc (GLAPLayer p (⊤ : Subgroup ↥Y)).map Y.subtype
        ≤ (GLAPLayer p H' ⊔ N').map Y.subtype := Subgroup.map_mono hkeyA
      _ = (GLAPLayer p H').map Y.subtype ⊔ N := by rw [Subgroup.map_sup, hNtop]
  · rw [hH1, hY1]
    calc (GLAPLayer p H').map Y.subtype
        ≤ (GLAPLayer p (⊤ : Subgroup ↥Y) ⊔ N').map Y.subtype := Subgroup.map_mono hkeyB
      _ = (GLAPLayer p (⊤ : Subgroup ↥Y)).map Y.subtype ⊔ N := by rw [Subgroup.map_sup, hNtop]

theorem exists_Jstar {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K B R X : Subgroup G}
    (hKL : GLAPLayer p K = K) (hBK : B ≤ Subgroup.normalizer (K : Set G)) (hB : IsElemAbelian p B)
    (hXK : X ≤ K) (hKX : K ≤ Subgroup.normalizer (X : Set G)) (hXO : X ≤ GLAPPrimeCoreOf p K)
    (hR : IsPGroup 2 R) (hRX : R ≤ X) (hRidx : ¬ 2 ∣ R.relIndex X)
    (hBR : B ≤ Subgroup.normalizer (R : Set G)) :
    ∃ Js : Subgroup G, Js ≤ K ∧ Js ≤ Subgroup.normalizer (R : Set G) ∧
      B ≤ Subgroup.normalizer (Js : Set G) ∧ GLAPLayer p Js = Js ∧ K ≤ Js ⊔ GLAPPrimeCoreOf p K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H : Subgroup G := K ⊓ Subgroup.normalizer (R : Set G) with hHdef
  have hBH : B ≤ Subgroup.normalizer (H : Set G) :=
    le_normalizer_inf hBK (hBR.trans Subgroup.le_normalizer)
  have hHK : H ≤ K := inf_le_left
  have hXcop : p.Coprime (Nat.card X) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hXO)
      (i183_coprime_card_glaPPrimeCoreOf hp K)
  have hKHX : K ≤ H ⊔ X := by
    intro k hk
    obtain ⟨l, hl, hlk⟩ := CFSG.AGLEmbedding.exists_mem_inv_mul_mem_normalizer_of_not_dvd_index
      (p := 2) (L := X) (P := R) (m := k) hRX hR hRidx (hKX hk)
    have hlH : l⁻¹ * k ∈ H := ⟨K.mul_mem (K.inv_mem (hXK hl)) hk, hlk⟩
    have h2 : l * (l⁻¹ * k) ∈ X ⊔ H := Subgroup.mul_mem_sup hl hlH
    rw [mul_inv_cancel_left, sup_comm] at h2
    exact h2
  have hLH := glaPLayer_sup_S4S hp hHK hXK hKX hXcop hKHX
  have hKle : K ≤ GLAPLayer p H ⊔ GLAPPrimeCoreOf p K :=
    calc K = GLAPLayer p K := hKL.symm
      _ ≤ GLAPLayer p H ⊔ X := hLH.1
      _ ≤ GLAPLayer p H ⊔ GLAPPrimeCoreOf p K := sup_le_sup_left hXO _
  exact ⟨GLAPLayer p H, (glaPLayer_le_self_S4S H).trans hHK,
    (glaPLayer_le_self_S4S H).trans inf_le_right,
    fun b hb => mem_normalizer_glaPLayer (hBH hb), glaPLayer_idem_S4S hp H, hKle⟩

private theorem mem_sup_S4S {W N : Subgroup G} (hWN : W ≤ Subgroup.normalizer (N : Set G))
    {x : G} (hx : x ∈ W ⊔ N) : ∃ w ∈ W, ∃ n ∈ N, w * n = x := by
  let P : Subgroup G :=
    { carrier := {x | ∃ w ∈ W, ∃ n ∈ N, w * n = x}
      mul_mem' := by
        rintro _ _ ⟨w1, hw1, n1, hn1, rfl⟩ ⟨w2, hw2, n2, hn2, rfl⟩
        have h1 : w2⁻¹ * n1 * w2 ∈ N := by
          have h := (Subgroup.mem_normalizer_iff.1 (hWN (W.inv_mem hw2)) n1).1 hn1
          simpa using h
        exact ⟨w1 * w2, W.mul_mem hw1 hw2, w2⁻¹ * n1 * w2 * n2, N.mul_mem h1 hn2, by group⟩
      one_mem' := ⟨1, W.one_mem, 1, N.one_mem, mul_one 1⟩
      inv_mem' := by
        rintro _ ⟨w, hw, n, hn, rfl⟩
        have h1 : w * n⁻¹ * w⁻¹ ∈ N :=
          (Subgroup.mem_normalizer_iff.1 (hWN hw) n⁻¹).1 (N.inv_mem hn)
        exact ⟨w⁻¹, W.inv_mem hw, w * n⁻¹ * w⁻¹, h1, by group⟩ }
  have hle : W ⊔ N ≤ P := sup_le
    (fun w hw => ⟨w, hw, 1, N.one_mem, mul_one w⟩)
    (fun n hn => ⟨1, W.one_mem, n, hn, one_mul n⟩)
  obtain ⟨w, hw, n, hn, h⟩ := hle hx
  exact ⟨w, hw, n, hn, h⟩

theorem exists_J_of_Jstar {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K B R E X Js : Subgroup G}
    (hKL : GLAPLayer p K = K) (hBK : B ≤ Subgroup.normalizer (K : Set G)) (hB : IsElemAbelian p B)
    (hEB : E ≤ B) (hXK : X ≤ K) (hKX : K ≤ Subgroup.normalizer (X : Set G))
    (hXO : X ≤ GLAPPrimeCoreOf p K) (hR : IsPGroup 2 R) (hRX : R ≤ X) (hRidx : ¬ 2 ∣ R.relIndex X)
    (hBR : B ≤ Subgroup.normalizer (R : Set G)) (hJsK : Js ≤ K)
    (hJsR : Js ≤ Subgroup.normalizer (R : Set G)) (hBJs : B ≤ Subgroup.normalizer (Js : Set G))
    (hJsL : GLAPLayer p Js = Js) (hcov : K ≤ Js ⊔ GLAPPrimeCoreOf p K)
    (hZ : GLAPLayer p (K ⊓ Subgroup.centralizer (E : Set G)) ≠ ⊥) :
    ∃ J : Subgroup G, J ≤ K ∧ J ≤ Subgroup.normalizer (R : Set G) ∧
      J ≤ Subgroup.centralizer (E : Set G) ∧ B ≤ Subgroup.normalizer (J : Set G) ∧ J ≠ ⊥ ∧
      GLAPLayer p J = J ∧ J ≤ GLAPLayer p (K ⊓ Subgroup.centralizer (E : Set G)) ∧
      GLAPLayer p (K ⊓ Subgroup.centralizer (E : Set G)) ≤ J ⊔ GLAPPrimeCoreOf p K := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hOK : GLAPPrimeCoreOf p K ≤ K := by
    unfold GLAPPrimeCoreOf; exact Subgroup.map_subtype_le _
  have hOcop : p.Coprime (Nat.card (GLAPPrimeCoreOf p K)) := i183_coprime_card_glaPPrimeCoreOf hp K
  have hKO : K ≤ Subgroup.normalizer (GLAPPrimeCoreOf p K : Set G) :=
    le_normalizer_glaPPrimeCoreOf p K
  have hBO : B ≤ Subgroup.normalizer (GLAPPrimeCoreOf p K : Set G) :=
    hBK.trans (normalizer_le_normalizer_glaPPrimeCoreOf p K)
  have hEp : IsPGroup p E := (isPGroup_of_isElemAbelian hB).to_le hEB
  have hBC : B ≤ Subgroup.centralizer (E : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact isElemAbelian_commute hB (hEB he) hb
  set O : Subgroup G := GLAPPrimeCoreOf p K with hOdef
  set Y0 : Subgroup G := Js ⊓ Subgroup.centralizer (E : Set G) with hY0
  set Yc : Subgroup G := K ⊓ Subgroup.centralizer (E : Set G) with hYc
  set N' : Subgroup G := O ⊓ Subgroup.centralizer (E : Set G) with hN'
  have hBY0 : B ≤ Subgroup.normalizer (Y0 : Set G) :=
    le_normalizer_inf hBJs (hBC.trans Subgroup.le_normalizer)
  have hYcN' : Yc ≤ Subgroup.normalizer (N' : Set G) :=
    le_normalizer_inf (inf_le_left.trans hKO) (inf_le_right.trans Subgroup.le_normalizer)
  have hN'Yc : N' ≤ Yc := inf_le_inf hOK le_rfl
  have hcopN' : p.Coprime (Nat.card N') :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left) hOcop
  have hY : Yc ≤ Y0 ⊔ N' := by
    rintro c ⟨hcK, hcE⟩
    obtain ⟨j, hj, o, ho, hjo⟩ := mem_sup_S4S (hJsK.trans hKO) (hcov hcK)
    subst hjo
    have hBJsO : B ≤ Subgroup.normalizer ((Js ⊓ O : Subgroup G) : Set G) :=
      le_normalizer_inf hBJs hBO
    have hy : ∀ a ∈ E, j⁻¹ * (a * j * a⁻¹) ∈ (Js ⊓ O : Subgroup G) := by
      intro a ha
      have hac : a * (j * o) = j * o * a := Subgroup.mem_centralizer_iff.1 hcE a ha
      have h1 : a * j = j * o * a * o⁻¹ := by
        calc a * j = a * (j * o) * o⁻¹ := by group
          _ = j * o * a * o⁻¹ := by rw [hac]
      have e : j⁻¹ * (a * j * a⁻¹) = o * (a * o⁻¹ * a⁻¹) := by
        rw [h1]; group
      have hajs : a * j * a⁻¹ ∈ Js := (Subgroup.mem_normalizer_iff.1 (hBJs (hEB ha)) j).1 hj
      have hao : a * o⁻¹ * a⁻¹ ∈ GLAPPrimeCoreOf p K :=
        (Subgroup.mem_normalizer_iff.1 (hBO (hEB ha)) o⁻¹).1 (Subgroup.inv_mem _ ho)
      refine Subgroup.mem_inf.2 ⟨Js.mul_mem (Js.inv_mem hj) hajs, ?_⟩
      rw [e]
      exact (GLAPPrimeCoreOf p K).mul_mem ho hao
    have hN0 : ¬ p ∣ Nat.card ↥(Js ⊓ O : Subgroup G) :=
      (Nat.Prime.coprime_iff_not_dvd hp).1
        (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right) hOcop)
    have hEN0 : E ≤ Subgroup.normalizer ((Js ⊓ O : Subgroup G) : Set G) :=
      le_normalizer_inf (hEB.trans hBJs) (hEB.trans hBO)
    obtain ⟨n, hn, hjn⟩ := Generation228.exists_fixed_mem_coset hp hEp hEN0 hN0 hy
    have hnJs : n ∈ Js := (Subgroup.mem_inf.1 hn).1
    have hnO : n ∈ O := (Subgroup.mem_inf.1 hn).2
    have hx : j * n ∈ Y0 := Subgroup.mem_inf.2 ⟨Js.mul_mem hj hnJs, hjn⟩
    have hy' : n⁻¹ * o ∈ N' := by
      refine Subgroup.mem_inf.2 ⟨O.mul_mem (O.inv_mem hnO) ho, ?_⟩
      have := Subgroup.mul_mem _ (Subgroup.inv_mem _ hjn) hcE
      convert this using 1
      group
    have e2 : j * o = (j * n) * (n⁻¹ * o) := by group
    rw [e2]
    exact Subgroup.mul_mem_sup hx hy'
  have hH := glaPLayer_sup_S4S hp (inf_le_inf hJsK le_rfl) hN'Yc hYcN' hcopN' hY
  have hJZ : GLAPLayer p Y0 ≤ GLAPLayer p Yc := by
    refine sSup_le fun T hT => ?_
    have hTY : T ≤ GLAPLayer p Y0 := le_sSup hT
    exact i183_le_of_le_sup hp (show GLAPComponent p Y0 T from hT) hcopN'
      (fun n hn => mem_normalizer_glaPLayer (Subgroup.le_normalizer (hN'Yc hn)))
      (hTY.trans hH.2)
  have hJne : GLAPLayer p Y0 ≠ ⊥ := by
    intro hJbot
    have hZO : GLAPLayer p Yc ≤ GLAPPrimeCoreOf p K := by
      refine hH.1.trans ?_
      rw [hJbot, bot_sup_eq]
      exact inf_le_left
    have hcomp : ∃ T, GLAPComponent p Yc T := by
      by_contra hno
      apply hZ
      refine le_antisymm (sSup_le fun T hT => ?_) bot_le
      exact absurd ⟨T, show GLAPComponent p Yc T from hT⟩ hno
    obtain ⟨T, hT⟩ := hcomp
    have hTO : T ≤ GLAPPrimeCoreOf p K := (le_sSup (show T ∈ {L | GLAPComponent p Yc L} from hT)).trans hZO
    have hdvd : p ∣ Nat.card ↥T := by
      have h1 := dvd_card_pQuot_of_component hp hT
      have hcard : Nat.card ↥T = Nat.card (PQuot p T) * Nat.card (GLAPPrimeCore p ↥T) :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup _
      rw [hcard]
      exact Dvd.dvd.mul_right h1 _
    exact (Nat.Prime.coprime_iff_not_dvd hp).1 (i183_coprime_card_glaPPrimeCoreOf hp K)
      (hdvd.trans (Subgroup.card_dvd_of_le hTO))
  refine ⟨GLAPLayer p Y0, (glaPLayer_le_self_S4S (p := p) Y0).trans (inf_le_left.trans hJsK),
    (glaPLayer_le_self_S4S (p := p) Y0).trans (inf_le_left.trans hJsR),
    (glaPLayer_le_self_S4S (p := p) Y0).trans inf_le_right,
    fun b hb => mem_normalizer_glaPLayer (hBY0 hb), hJne,
    glaPLayer_idem_S4S hp Y0, hJZ, ?_⟩
  exact hH.1.trans (sup_le_sup_left (inf_le_left : N' ≤ O) _)

theorem exists_J_data {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K B R E X : Subgroup G}
    (hKL : GLAPLayer p K = K) (hBK : B ≤ Subgroup.normalizer (K : Set G)) (hB : IsElemAbelian p B)
    (hEB : E ≤ B) (hXK : X ≤ K) (hKX : K ≤ Subgroup.normalizer (X : Set G))
    (hXO : X ≤ GLAPPrimeCoreOf p K) (hR : IsPGroup 2 R) (hRX : R ≤ X) (hRidx : ¬ 2 ∣ R.relIndex X)
    (hBR : B ≤ Subgroup.normalizer (R : Set G))
    (hZ : GLAPLayer p (K ⊓ Subgroup.centralizer (E : Set G)) ≠ ⊥) :
    ∃ J : Subgroup G, J ≤ K ∧ J ≤ Subgroup.normalizer (R : Set G) ∧
      J ≤ Subgroup.centralizer (E : Set G) ∧ B ≤ Subgroup.normalizer (J : Set G) ∧ J ≠ ⊥ ∧
      GLAPLayer p J = J ∧ J ≤ GLAPLayer p (K ⊓ Subgroup.centralizer (E : Set G)) ∧
      GLAPLayer p (K ⊓ Subgroup.centralizer (E : Set G)) ≤ J ⊔ GLAPPrimeCoreOf p K := by
  obtain ⟨Js, hJsK, hJsR, hBJs, hJsL, hcov⟩ :=
    exists_Jstar hp hp2 hKL hBK hB hXK hKX hXO hR hRX hRidx hBR
  exact exists_J_of_Jstar hp hp2 hKL hBK hB hEB hXK hKX hXO hR hRX hRidx hBR hJsK hJsR hBJs hJsL
    hcov hZ

theorem quaternion_commutator_centralized {B S : Subgroup G} (e : S ≃* QuaternionGroup 2)
    (hBS : B ≤ Subgroup.normalizer (S : Set G)) :
    (⁅B, (⁅S, S⁆ : Subgroup G)⁆ : Subgroup G) = ⊥ := by
  set z : S := e.symm (QuaternionGroup.a 2) with hz
  have hcomm : ∀ x y : QuaternionGroup 2, ⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = QuaternionGroup.a 2 := by decide
  have hex : ∃ x y : QuaternionGroup 2, ⁅x, y⁆ = QuaternionGroup.a 2 := by decide
  have hz1 : z ≠ 1 := by
    intro h
    have := congrArg e h
    rw [hz, MulEquiv.apply_symm_apply, map_one] at this
    exact absurd this (by decide)
  have hz2 : z ^ 2 = 1 := by
    apply e.injective
    rw [map_pow, hz, MulEquiv.apply_symm_apply, map_one]
    decide
  have hcommS : ∀ s t : S, ⁅s, t⁆ = 1 ∨ ⁅s, t⁆ = z := by
    intro s t
    have h := hcomm (e s) (e t)
    have hmap : e ⁅s, t⁆ = ⁅e s, e t⁆ := by simp [commutatorElement_def]
    rw [← hmap] at h
    rcases h with h | h
    · left
      exact e.injective (by simpa using h)
    · right
      exact e.injective (by simpa [hz] using h)
  have hSS : (⁅S, S⁆ : Subgroup G) ≤ Subgroup.zpowers (z : G) := by
    rw [Subgroup.commutator_le]
    intro s hs t ht
    have h := hcommS ⟨s, hs⟩ ⟨t, ht⟩
    have hc : ⁅s, t⁆ = ((⁅(⟨s, hs⟩ : S), (⟨t, ht⟩ : S)⁆ : S) : G) := rfl
    rw [hc]
    rcases h with h | h
    · rw [h]
      exact Subgroup.one_mem _
    · rw [h]
      exact Subgroup.mem_zpowers _
  obtain ⟨x, y, hxy⟩ := hex
  have hzS : (z : G) ∈ (⁅S, S⁆ : Subgroup G) := by
    have h1 := Subgroup.commutator_mem_commutator (e.symm x).2 (e.symm y).2
    have h2 : ⁅((e.symm x : S) : G), ((e.symm y : S) : G)⁆ = (z : G) := by
      have : (⁅e.symm x, e.symm y⁆ : S) = z := by
        apply e.injective
        have hmap : e ⁅e.symm x, e.symm y⁆ = ⁅x, y⁆ := by simp [commutatorElement_def]
        rw [hmap, hxy, hz, MulEquiv.apply_symm_apply]
      exact congrArg Subtype.val this
    rw [h2] at h1
    exact h1
  have hBSS : B ≤ Subgroup.normalizer ((⁅S, S⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator hBS hBS
  have hbz : ∀ b ∈ B, b * (z : G) * b⁻¹ = (z : G) := by
    intro b hb
    have h1 : b * (z : G) * b⁻¹ ∈ (⁅S, S⁆ : Subgroup G) :=
      (Subgroup.mem_normalizer_iff.1 (hBSS hb) (z : G)).1 hzS
    have h2 := hSS h1
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h2
    have hord : orderOf (z : G) = 2 := by
      have hz1' : (z : G) ≠ 1 := fun h => hz1 (Subtype.ext h)
      have h2' : (z : G) ^ 2 = 1 := by
        have := congrArg Subtype.val hz2
        simpa using this
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact orderOf_eq_prime h2' hz1'
    rw [← zpow_mod_orderOf, hord] at hk
    push_cast at hk
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · rw [h, zpow_zero] at hk
      have h3 : (z : G) = 1 := by
        calc (z : G) = b⁻¹ * (b * (z : G) * b⁻¹) * b := by group
          _ = b⁻¹ * 1 * b := by rw [← hk]
          _ = 1 := by group
      exact absurd h3 (fun h' => hz1 (Subtype.ext h'))
    · rw [h, zpow_one] at hk
      exact hk.symm
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro b hb
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  have hgz := hSS hg
  have hbC : b ∈ Subgroup.centralizer ((Subgroup.zpowers (z : G) : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure, Subgroup.mem_centralizer_singleton_iff]
    have := hbz b hb
    calc b * (z : G) = b * (z : G) * b⁻¹ * b := by group
      _ = (z : G) * b := by rw [this]
  exact (Subgroup.mem_centralizer_iff.1 hbC) g hgz

theorem isEssential_of_two_group {p : ℕ} {B S : Subgroup G} {x : G} (hx : x ∈ B) (hx1 : x ≠ 1)
    (hS : IsPGroup 2 S) (hSx : S ≤ Subgroup.centralizer ({x} : Set G))
    (hBS : B ≤ Subgroup.normalizer (S : Set G))
    (hS' : (⁅B, (⁅S, S⁆ : Subgroup G)⁆ : Subgroup G) ≠ ⊥) : IsEssential p B x := by
  refine ⟨hx, hx1, S, hSx, hS, hBS, ?_, fun _ =>
    ⟨fun e => hS' (quaternion_commutator_centralized e hBS)⟩⟩
  intro h
  apply hS'
  have hSS : (⁅S, S⁆ : Subgroup G) ≤ S := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact S.mul_mem (S.mul_mem (S.mul_mem ha hb) (S.inv_mem ha)) (S.inv_mem hb)
  rw [eq_bot_iff]
  calc (⁅B, (⁅S, S⁆ : Subgroup G)⁆ : Subgroup G) ≤ ⁅B, S⁆ := Subgroup.commutator_mono le_rfl hSS
    _ = ⁅S, B⁆ := Subgroup.commutator_comm B S
    _ = ⊥ := h
    _ ≤ ⊥ := le_rfl

end CFSG.LocalAnalysis.GLTheoremA
