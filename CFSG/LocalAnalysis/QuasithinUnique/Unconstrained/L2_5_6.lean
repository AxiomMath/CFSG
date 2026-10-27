module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_4
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_6M11
public import CFSG.CharacterTheory.Semidihedral.GL2Recognition.M11Order

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

section Lists

variable {G : Type} [Group G]

@[expose] def IsListed25 (L : Subgroup G) : Prop :=
  fusionIsBenderGroup ↥L ∨ IsRankTwoEvenType L ∨
    (StatedClassicalModel ↥L .PSL 3 3 1 ∨
      Nonempty (↥L ≃* CFSG.Blueprint.NativeSporadic.Carrier .M11)) ∨
    ∃ p : ℕ, IsFermatOrMersenne p ∧ 7 < p ∧ StatedClassicalModel ↥L .PSL 2 p 1

theorem ComponentList.isListed25 {M S L : Subgroup G} {z : G} (h : ComponentList M S z L) :
    IsListed25 L := by
  obtain ⟨-, -, -, -, h | h | ⟨h, -⟩ | ⟨h, -⟩⟩ := h
  · exact Or.inl h.1
  · exact Or.inr (Or.inl h.1)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

end Lists

@[expose] def Lemma256Embedding : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G) (hs : UnconstrainedSetting G T M)
    (N : Notation25 hs), Lv255 N → ∀ E : Subgroup G, E ≠ ⊥ → E ≤ N.SC →
      N.S ≤ Subgroup.normalizer (E : Set G) →
      ∃ KE : Subgroup G, N.K ≤ KE ∧ IsComponentIn KE (Subgroup.normalizer (E : Set G))

@[expose] def A312Sublist : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), UniqueSetting G T M →
    ∀ X S K L : Subgroup G, pCoreOf 2 X ≠ ⊥ → IsSylowTwoOf S X →
      IsComponentIn K (K ⊔ S) → IsSylowTwoOf S (K ⊔ S) → pCoreOf 2 (K ⊔ S) ≠ ⊥ →
      K ≤ L → IsComponentIn L X → IsListed25 K → ¬ fusionIsBenderGroup ↥K → IsListed25 L →
      K = L ∨ (Nonempty (↥K ≃* alternatingGroup (Fin 6)) ∧
        Nonempty (↥L ≃* CFSG.Blueprint.NativeSporadic.Carrier .M11))

@[expose] def M11OutTrivial : Prop :=
  ∀ (G : Type) [Group G] (L : Subgroup G),
    Nonempty (↥L ≃* CFSG.Blueprint.NativeSporadic.Carrier .M11) →
    ∀ g ∈ Subgroup.normalizer (L : Set G), ∃ y ∈ L, ∀ x ∈ L, g * x * g⁻¹ = y * x * y⁻¹

@[expose] def M11A6Normalizer : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L B Q : Subgroup G),
    Nonempty (↥L ≃* CFSG.Blueprint.NativeSporadic.Carrier .M11) →
    Nonempty (↥B ≃* alternatingGroup (Fin 6)) → B ≤ L → IsSylowTwoOf Q L →
    Q ≤ Subgroup.normalizer (B : Set G) →
      L ⊓ Subgroup.normalizer (B : Set G) = B ⊔ Q ∧
        L ⊓ Subgroup.centralizer (B : Set G) = ⊥ ∧
        Nonempty (↥(L ⊓ Subgroup.normalizer (B : Set G)) ≃* ↥A6Models.m10)

namespace Unc25G2

section Rank

variable {G : Type*} [Group G] [Finite G]

theorem exists_elemAbelian_card_pow_succ_of_commuting {p : ℕ} (hp : p.Prime)
    {L₁ L₂ E₁ : Subgroup G} (h₁₂ : ⁅L₁, L₂⁆ = ⊥) (hE₁L : E₁ ≤ L₁)
    (hE₁ : CFSG.Assembly.IsElemAbelian p E₁) {n : ℕ} (hE₁card : Nat.card E₁ = p ^ n)
    (hZ₂ : ∀ x ∈ L₂, (∀ y ∈ L₂, y * x = x * y) → x ^ p = 1 → x = 1)
    (hd₂ : p ∣ Nat.card L₂) :
    ∃ E : Subgroup G, E ≤ L₁ ⊔ L₂ ∧ CFSG.Assembly.IsElemAbelian p E ∧
      Nat.card E = p ^ (n + 1) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x₂, hx₂⟩ := exists_prime_orderOf_dvd_card' p hd₂
  set a₂ : G := (x₂ : G) with ha₂
  have ho₂ : orderOf a₂ = p := (Subgroup.orderOf_coe x₂).trans hx₂
  have hap : a₂ ^ p = 1 := by
    rw [← ho₂]
    exact pow_orderOf_eq_one a₂
  have hP₂ : Subgroup.zpowers a₂ ≤ L₂ := Subgroup.zpowers_le.mpr x₂.2
  have hc : ∀ x ∈ E₁, ∀ y ∈ Subgroup.zpowers a₂, x * y = y * x := fun x hx y hy =>
    BenderBranch.commute_of_commutator_eq_bot h₁₂ (hE₁L hx) (hP₂ hy)
  have hpowB : ∀ v ∈ Subgroup.zpowers a₂, v ^ p = 1 := by
    intro v hv
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hap, one_zpow]
  have hcomB : ∀ v v' : G, v ∈ Subgroup.zpowers a₂ → v' ∈ Subgroup.zpowers a₂ →
      v * v' = v' * v := by
    intro v v' hv hv'
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv'
    exact (Commute.zpow_zpow_self a₂ m k).eq
  have hcomA : ∀ u u' : G, u ∈ E₁ → u' ∈ E₁ → u * u' = u' * u := by
    intro u u' hu hu'
    have := hE₁.1
    exact congrArg Subtype.val (mul_comm' (⟨u, hu⟩ : E₁) ⟨u', hu'⟩)
  have hinf : E₁ ⊓ Subgroup.zpowers a₂ = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hy1, hy2⟩
    have hyL₂ : y ∈ L₂ := hP₂ hy2
    have hyc : ∀ w ∈ L₂, w * y = y * w := fun w hw =>
      (BenderBranch.commute_of_commutator_eq_bot h₁₂ (hE₁L hy1) hw).symm
    exact Subgroup.mem_bot.mpr (hZ₂ y hyL₂ hyc (hpowB y hy2))
  have hmem : ∀ x : G, x ∈ E₁ ⊔ Subgroup.zpowers a₂ ↔
      ∃ u ∈ E₁, ∃ v ∈ Subgroup.zpowers a₂, u * v = x := fun x =>
    BenderBranch.mem_sup_iff_of_commute hc
  refine ⟨E₁ ⊔ Subgroup.zpowers a₂, sup_le_sup hE₁L hP₂, ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩, ?_⟩
  · apply Subtype.ext
    obtain ⟨u, hu, v, hv, hx⟩ := (hmem x.1).mp x.2
    obtain ⟨u', hu', v', hv', hy⟩ := (hmem y.1).mp y.2
    have c1 : Commute u u' := hcomA u u' hu hu'
    have c2 : Commute v v' := hcomB v v' hv hv'
    have c3 : Commute u v' := hc u hu v' hv'
    have c4 : Commute v u' := (hc u' hu' v hv).symm
    show (x : G) * y = y * x
    rw [← hx, ← hy]
    exact ((c1.mul_right c3).mul_left (c4.mul_right c2)).eq
  · intro x hx
    obtain ⟨u, hu, v, hv, rfl⟩ := (hmem x).mp hx
    have hcuv : Commute u v := hc u hu v hv
    rw [hcuv.mul_pow, hE₁.2 u hu, hpowB v hv, one_mul]
  · rw [BenderBranch.card_sup_of_commute_of_inf_eq_bot hc hinf, hE₁card, Nat.card_zpowers, ho₂,
      pow_succ]

end Rank

section Conj

variable {G : Type*} [Group G]

theorem iSup_conjugate_eq_conjJoin (X L : Subgroup G) :
    (⨆ g : X, CFSG.conjugate L (g : G)) = conjJoin X L := by
  apply le_antisymm
  · refine iSup_le fun g => ?_
    exact le_iSup (fun s : X => L.map (MulAut.conj (s : G)).toMonoidHom)
      ⟨(g : G)⁻¹, X.inv_mem g.2⟩
  · refine iSup_le fun s => ?_
    have := le_iSup (fun g : X => CFSG.conjugate L (g : G)) ⟨(s : G)⁻¹, X.inv_mem s.2⟩
    simpa [CFSG.conjugate] using this

end Conj

end Unc25G2

namespace Notation25

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}
  (N : Notation25 hs)

theorem K0_le_centralizer_of_le_SC {E : Subgroup G} (hE : E ≤ N.SC) :
    N.K0 ≤ Subgroup.centralizer (E : Set G) := fun k hk =>
  Subgroup.mem_centralizer_iff.mpr fun _ he =>
    (Subgroup.mem_centralizer_iff.mp (N.SC_le_centralizer (hE he)) k hk).symm

theorem isGamma_of_le {X E : Subgroup G} (hE1 : E ≠ ⊥) (hE2 : IsPGroup 2 E) (hEX : E ≤ X)
    (hXE : X ≤ Subgroup.normalizer (E : Set G)) (hHX : N.H ≤ X) : IsGamma M X := by
  have hnorm : (E.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hEX).mpr hXE
  have hle : E ≤ pCoreOf 2 X :=
    CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 E X hEX hnorm hE2
  have hcore : pCoreOf 2 X ≠ ⊥ := fun hbot => hE1 (le_bot_iff.mp (hbot ▸ hle))
  obtain ⟨-, U, HU, hpair, hUH⟩ := N.gammaU.isGamma
  exact ⟨hcore, U, HU, hpair, hUH.trans hHX⟩

theorem tuple_of_overgroup {H' : Subgroup G} (hΓ : IsGamma M H') (hHH' : N.H ≤ H') :
    Tuple25 T M H' N.S N.z ∧ IsGammaU M H' := by
  obtain ⟨h0, hSH', hSM', hU, -⟩ := IsGamma0.overgroup_of_le hs.setting N.tuple.gamma0
    N.tuple.sylow_inf hΓ hHH'
  exact ⟨{ gamma0 := h0
           sylow_inf := hSM'
           sylow := hSH'
           center_le := N.tuple.center_le
           lt := N.tuple.lt
           z_mem := N.tuple.z_mem
           z_ne_one := N.tuple.z_ne_one
           z_sq := N.tuple.z_sq }, hU N.gammaU⟩

end Notation25

section M11Case

variable {G : Type} [Group G] [Finite G]

theorem conjugate_eq_of_iso_M11
    (he : CFSG.Assembly.evenRank G ≤ 2) {X KE : Subgroup G}
    (hX : pCoreOf 2 X ≠ ⊥) (hKE : IsComponentIn KE X) (hcen : Unc25G2.CentreTwo KE)
    (e : ↥KE ≃* CFSG.Blueprint.NativeSporadic.Carrier .M11) {g : G} (hg : g ∈ X) :
    CFSG.conjugate KE g = KE := by
  by_contra hne
  have hKEg : IsComponentIn (CFSG.conjugate KE g) X := Unc25G2.isComponentIn_conjugate hKE hg
  have hcomm : ⁅KE, CFSG.conjugate KE g⁆ = ⊥ :=
    (BenderBranch.eq_or_commute_of_isComponentIn hKE hKEg).resolve_left fun h => hne h.symm
  obtain ⟨E₉, hE₉KE, hE₉, hE₉card⟩ := Unc25G2.exists_elemAbelian_nine_of_iso e
  have hcardKE : Nat.card KE = 7920 :=
    (Nat.card_congr e.toEquiv).trans CFSG.Semidihedral.GL2Recognition.card_nativeM11
  have h3 : 3 ∣ Nat.card (CFSG.conjugate KE g) := by
    rw [BenderBranch.card_conjugate, hcardKE]
    norm_num
  have hZ : ∀ x ∈ CFSG.conjugate KE g, (∀ y ∈ CFSG.conjugate KE g, y * x = x * y) →
      x ^ 3 = 1 → x = 1 := by
    intro x hx hxc hxp
    obtain ⟨k, hk⟩ := (hcen.conjugate g) x hx hxc
    exact Unc25G2.eq_one_of_pow_eq_one_of_two_pow Nat.prime_three (by norm_num) hxp hk
  obtain ⟨E, hEle, hE, hEcard⟩ := Unc25G2.exists_elemAbelian_card_pow_succ_of_commuting
    Nat.prime_three hcomm hE₉KE hE₉ (n := 2) (by rw [hE₉card]; norm_num) hZ h3
  exact Unc25G2.false_of_isElemAbelian_card_cube he hX (hEle.trans (sup_le hKE.1 hKEg.1))
    Nat.prime_three (by norm_num) hE (by rw [hEcard])

theorem nonempty_autOn_equiv_m10 (hout : M11OutTrivial) (hnorm : M11A6Normalizer)
    {K KE S : Subgroup G} (eK : ↥K ≃* alternatingGroup (Fin 6))
    (eE : ↥KE ≃* CFSG.Blueprint.NativeSporadic.Carrier .M11) (hKKE : K ≤ KE)
    (hSK : S ≤ Subgroup.normalizer (K : Set G)) (hSKE : S ≤ Subgroup.normalizer (KE : Set G))
    (hQ : IsSylowTwoOf (S ⊓ KE) KE) :
    Nonempty (↥(autOn (K ⊔ S) K) ≃* ↥A6Models.m10) := by
  obtain ⟨hNL, hC, ⟨eN⟩⟩ := hnorm G KE K (S ⊓ KE) ⟨eE⟩ ⟨eK⟩ hKKE hQ (inf_le_left.trans hSK)
  have hNLnorm : KE ⊓ Subgroup.normalizer (K : Set G) ≤ Subgroup.normalizer (K : Set G) :=
    inf_le_right
  let ψ : ↥((KE ⊓ Subgroup.normalizer (K : Set G)).subgroupOf
      (Subgroup.normalizer (K : Set G))) →* MulAut ↥K :=
    (conjAct K).comp ((KE ⊓ Subgroup.normalizer (K : Set G)).subgroupOf
      (Subgroup.normalizer (K : Set G))).subtype
  have hψapp : ∀ (n : ↥((KE ⊓ Subgroup.normalizer (K : Set G)).subgroupOf
      (Subgroup.normalizer (K : Set G)))) (x : ↥K),
      ((ψ n x : ↥K) : G) = (n : G) * x * (n : G)⁻¹ := fun n x => rfl
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro n hn
    have hnNL : ((n : Subgroup.normalizer (K : Set G)) : G) ∈
        KE ⊓ Subgroup.normalizer (K : Set G) := n.2
    have hcent : ((n : Subgroup.normalizer (K : Set G)) : G) ∈
        Subgroup.centralizer (K : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have h1 := congrArg (fun φ : MulAut ↥K => ((φ ⟨x, hx⟩ : ↥K) : G)) hn
      simp only [hψapp, MulAut.one_apply] at h1
      calc x * (n : G) = (n : G) * x * (n : G)⁻¹ * (n : G) := by rw [h1]
        _ = (n : G) * x := by group
    have hmem : ((n : Subgroup.normalizer (K : Set G)) : G) ∈
        KE ⊓ Subgroup.centralizer (K : Set G) := ⟨hnNL.1, hcent⟩
    rw [hC, Subgroup.mem_bot] at hmem
    exact Subtype.ext (Subtype.ext hmem)
  have hrange : autOn (K ⊔ S) K = ψ.range := by
    have hψr : ψ.range = ((KE ⊓ Subgroup.normalizer (K : Set G)).subgroupOf
        (Subgroup.normalizer (K : Set G))).map (conjAct K) := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [hψr]
    unfold autOn
    apply le_antisymm
    · rintro φ ⟨⟨h, hhN⟩, hh, rfl⟩
      have hhS : h ∈ S ⊔ K := by
        rw [sup_comm]
        exact hh
      have hmul := Subgroup.coe_mul_of_left_le_normalizer_right S K hSK
      rw [← SetLike.mem_coe, hmul, Set.mem_mul] at hhS
      obtain ⟨s, hs, k, hk, rfl⟩ := hhS
      obtain ⟨y, hyKE, hy⟩ := hout G KE ⟨eE⟩ s (hSKE hs)
      have hyN : y ∈ Subgroup.normalizer (K : Set G) := by
        rw [Subgroup.mem_normalizer_iff]
        intro x
        constructor
        · intro hx
          rw [← hy x (hKKE hx)]
          exact (Subgroup.mem_normalizer_iff.mp (hSK hs) x).mp hx
        · intro hx
          have hxKE : x ∈ KE := by
            have h1 : y * x * y⁻¹ ∈ KE := hKKE hx
            have := KE.mul_mem (KE.mul_mem (KE.inv_mem hyKE) h1) hyKE
            simpa [mul_assoc] using this
          rw [← hy x hxKE] at hx
          exact (Subgroup.mem_normalizer_iff.mp (hSK hs) x).mpr hx
      have hykN : y * k ∈ Subgroup.normalizer (K : Set G) :=
        (Subgroup.normalizer (K : Set G)).mul_mem hyN (Subgroup.le_normalizer hk)
      have hykNL : y * k ∈ KE ⊓ Subgroup.normalizer (K : Set G) :=
        ⟨KE.mul_mem hyKE (hKKE hk), hykN⟩
      refine ⟨⟨y * k, hykN⟩, hykNL, ?_⟩
      refine MulEquiv.ext fun x => Subtype.ext ?_
      have hxk : (k : G) * x * k⁻¹ ∈ KE := hKKE (K.mul_mem (K.mul_mem hk x.2) (K.inv_mem hk))
      have h1 := hy _ hxk
      show (y * k) * (x : G) * (y * k)⁻¹ = s * k * (x : G) * (s * k)⁻¹
      calc y * k * (x : G) * (y * k)⁻¹ = y * (k * x * k⁻¹) * y⁻¹ := by group
        _ = s * (k * x * k⁻¹) * s⁻¹ := h1.symm
        _ = s * k * (x : G) * (s * k)⁻¹ := by group
    · apply Subgroup.map_mono
      intro n hn
      have hnNL : (n : G) ∈ KE ⊓ Subgroup.normalizer (K : Set G) := hn
      rw [hNL] at hnNL
      exact (sup_le_sup_left (inf_le_left : S ⊓ KE ≤ S) K) hnNL
  exact ⟨(MulEquiv.subgroupCongr hrange).trans ((MonoidHom.ofInjective hψinj).symm.trans
    ((Subgroup.subgroupOfEquivOfLe hNLnorm).trans eN))⟩

end M11Case

theorem lemma256_of_inputs
    (h252 : Lemma252) (hemb : Lemma256Embedding) (ha312 : A312Sublist)
    (hout : M11OutTrivial) (hnorm : M11A6Normalizer) : Lemma256 := by
  intro G _ _ T M hs N hlv E hE1 hEc hES
  have hin : Ch1.InducesInner N.z N.K := hlv.list252.2.1
  have hE2 : IsPGroup 2 E := N.tuple.sylow.isPGroup.to_le (hEc.trans N.SC_le_S)
  have hHX : N.H ≤ Subgroup.normalizer (E : Set G) :=
    N.H_le_normalizer_of (N.K0_le_centralizer_of_le_SC hEc) hES
  have hΓ : IsGamma M (Subgroup.normalizer (E : Set G)) :=
    N.isGamma_of_le hE1 hE2 Subgroup.le_normalizer le_rfl hHX
  obtain ⟨htupX, hUX⟩ := N.tuple_of_overgroup hΓ hHX
  refine ⟨hUX, htupX.sylow, ?_⟩
  obtain ⟨KE, hKKE, hKEX⟩ := hemb G T M hs N hlv E hE1 hEc hES
  have hKEle : KE ≤ Subgroup.normalizer (E : Set G) := hKEX.1
  have hH'X : KE ⊔ N.S ≤ Subgroup.normalizer (E : Set G) := sup_le hKEle hES
  have hHH' : N.H ≤ KE ⊔ N.S := by
    rw [N.join]
    exact sup_le_sup_right hKKE _
  have hES' : E ≤ KE ⊔ N.S := (hEc.trans N.SC_le_S).trans le_sup_right
  have hΓ' : IsGamma M (KE ⊔ N.S) := N.isGamma_of_le hE1 hE2 hES' hH'X hHH'
  obtain ⟨htup', hU'⟩ := N.tuple_of_overgroup hΓ' hHH'
  have hKE' : IsComponentIn KE (KE ⊔ N.S) :=
    BenderBranch.isComponentIn_of_le hKEX le_sup_left hH'X
  have hlistKE : ComponentList M N.S N.z KE :=
    h252 G T M (KE ⊔ N.S) N.S N.z hs htup' KE hKE'
  have hX : pCoreOf 2 (Subgroup.normalizer (E : Set G)) ≠ ⊥ := hΓ.1
  have hKcompJ : IsComponentIn N.K (N.K ⊔ N.S) := by
    rw [← N.join]
    exact N.isComp
  have hKsylJ : IsSylowTwoOf N.S (N.K ⊔ N.S) := by
    rw [← N.join]
    exact N.tuple.sylow
  have hKcoreJ : pCoreOf 2 (N.K ⊔ N.S) ≠ ⊥ := by
    rw [← N.join]
    exact N.tuple.gamma0.isGamma.1
  rcases ha312 G T M hs.setting _ N.S N.K KE hX htupX.sylow hKcompJ hKsylJ hKcoreJ hKKE hKEX
    hlv.list252.isListed25 N.nonBender hlistKE.isListed25 with hEq | ⟨⟨eK⟩, ⟨eE⟩⟩
  · left
    rw [hEq]
    exact hKEX
  · right
    have hcenKE : Unc25G2.CentreTwo KE := htup'.centreTwo hs hKE' hlistKE.2.1
    have hnormKE : ∀ g ∈ Subgroup.normalizer (E : Set G), CFSG.conjugate KE g = KE :=
      fun g hg => conjugate_eq_of_iso_M11 hs.setting.qtke.2.2 hX hKEX hcenKE eE hg
    have hSKE : N.S ≤ Subgroup.normalizer (KE : Set G) := fun s hs' =>
      BenderBranch.conjugate_eq_iff_mem_normalizer.mp (hnormKE s (hES hs'))
    have hK0 : N.K0 = N.K := by
      rcases N.shape hin with h | ⟨s₀, hs₀S, hne, -, hcommK⟩
      · exact h
      · exfalso
        have hs₀X : s₀ ∈ Subgroup.normalizer (E : Set G) := hES hs₀S
        have hKs₀ : CFSG.conjugate N.K s₀ ≤ KE := by
          have := BenderBranch.conjugate_mono hKKE s₀
          rwa [hnormKE s₀ hs₀X] at this
        have hle : N.K ⊔ CFSG.conjugate N.K s₀ ≤ KE := sup_le hKKE hKs₀
        have hc : ∀ a ∈ N.K, ∀ b ∈ CFSG.conjugate N.K s₀, a * b = b * a := fun a ha b hb =>
          BenderBranch.commute_of_commutator_eq_bot hcommK ha hb
        have hinf : N.K ⊓ CFSG.conjugate N.K s₀ = ⊥ := by
          rw [eq_bot_iff]
          rintro y ⟨hy1, hy2⟩
          exact Subgroup.mem_bot.mpr
            (Unc25G2.eq_one_of_central_of_iso_alt6 eK hy1 (fun w hw => hc w hw y hy2))
        have hcard := BenderBranch.card_sup_of_commute_of_inf_eq_bot hc hinf
        have hcardK : Nat.card N.K = 360 :=
          (Nat.card_congr eK.toEquiv).trans Unc25G2.card_alternatingGroup_six
        have hcardKE : Nat.card KE = 7920 :=
          (Nat.card_congr eE.toEquiv).trans CFSG.Semidihedral.GL2Recognition.card_nativeM11
        have hle' := Subgroup.card_le_of_le hle
        rw [hcard, BenderBranch.card_conjugate, hcardK, hcardKE] at hle'
        omega
    have hSK : N.S ≤ Subgroup.normalizer (N.K : Set G) := by
      have := N.S_le_normalizer_K0
      rwa [hK0] at this
    refine ⟨hK0, ⟨eK⟩, ?_, ?_⟩
    · have hQ : IsSylowTwoOf (N.S ⊓ KE) KE :=
        RankOneRecog.isSylowTwoOf_inf_of_subnormal htupX.sylow hKEle hKEX.2.2
      rw [N.join]
      exact nonempty_autOn_equiv_m10 hout hnorm eK eE hKKE hSK hSKE hQ
    · have hKbKE : (⨆ g : ↥(Subgroup.normalizer (E : Set G)), CFSG.conjugate N.K (g : G)) ≤ KE :=
        iSup_le fun g => (BenderBranch.conjugate_mono hKKE (g : G)).trans (hnormKE g g.2).le
      have hKbN : KE ≤ Subgroup.normalizer
          ((⨆ g : ↥(Subgroup.normalizer (E : Set G)), CFSG.conjugate N.K (g : G) : Subgroup G) :
            Set G) := by
        rw [Unc25G2.iSup_conjugate_eq_conjJoin]
        exact hKEle.trans (le_normalizer_conjJoin _ _)
      have hKbnormal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKbKE).mpr hKbN
      have hKQ : CFSG.IsQuasisimple ↥KE := BenderBranch.isQuasisimple_of_isComponentIn hKEX
      have hKKb : N.K ≤ (⨆ g : ↥(Subgroup.normalizer (E : Set G)),
          CFSG.conjugate N.K (g : G)) :=
        (BenderBranch.conjugate_one N.K).symm.le.trans
          (le_iSup (fun g : ↥(Subgroup.normalizer (E : Set G)) => CFSG.conjugate N.K (g : G))
            ⟨1, Subgroup.one_mem _⟩)
      have hKb : (⨆ g : ↥(Subgroup.normalizer (E : Set G)), CFSG.conjugate N.K (g : G)) = KE := by
        rcases CFSG.LocalCores.quasisimple_normal_subgroups hKQ hKbnormal with htop | hcen
        · exact le_antisymm hKbKE (Subgroup.subgroupOf_eq_top.mp htop)
        · exfalso
          apply Unc25G2.isComponentIn_ne_bot N.isComp
          rw [eq_bot_iff]
          intro x hx
          have hxc : (⟨x, hKKE hx⟩ : KE) ∈ Subgroup.center ↥KE :=
            hcen (show (⟨x, hKKE hx⟩ : KE) ∈ _ from hKKb hx)
          rw [Subgroup.mem_bot]
          refine Unc25G2.eq_one_of_central_of_iso_alt6 eK hx fun w hw => ?_
          have := Subgroup.mem_center_iff.mp hxc ⟨w, hKKE hw⟩
          exact congrArg Subtype.val this
      exact ⟨KE, hKb.symm, hKEX, ⟨eE⟩⟩

end CFSG.QuasithinUnique
