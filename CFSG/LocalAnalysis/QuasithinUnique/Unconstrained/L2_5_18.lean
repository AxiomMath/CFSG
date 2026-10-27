module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.Assembly
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_6
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_18Aux
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.Elementary
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_12Aux

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

@[expose] def M11NotBender : Prop :=
  ¬ fusionIsBenderGroup (CFSG.Blueprint.NativeSporadic.Carrier .M11)

theorem fusionIsBenderGroup_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : fusionIsBenderGroup B) : fusionIsBenderGroup A := by
  rcases h with ⟨f, hf, ⟨e'⟩⟩ | ⟨f, hf, ⟨e'⟩⟩ | ⟨a, ha, ⟨e'⟩⟩
  · exact Or.inl ⟨f, hf, ⟨e.trans e'⟩⟩
  · exact Or.inr (Or.inl ⟨f, hf, ⟨e.trans e'⟩⟩)
  · exact Or.inr (Or.inr ⟨a, ha, ⟨e.trans e'⟩⟩)

section Config

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}
  (N : Notation25 hs)

theorem Notation25.t_mul_self {t zK : G} (hf : Facts2511 N t zK) : t * t = 1 := by
  have := hf.t_sq
  rwa [sq] at this

theorem Notation25.zpowers_t_facts {t zK : G} (hf : Facts2511 N t zK) :
    Subgroup.zpowers t ≠ ⊥ ∧ Subgroup.zpowers t ≤ N.SC ∧
      N.S ≤ Subgroup.normalizer (Subgroup.zpowers t : Set G) := by
  have ht2 := N.t_mul_self hf
  refine ⟨?_, Subgroup.zpowers_le.mpr hf.t_mem, ?_⟩
  · intro hbot
    apply hf.t_ne_one
    have : t ∈ Subgroup.zpowers t := Subgroup.mem_zpowers t
    rw [hbot] at this
    exact Subgroup.mem_bot.mp this
  · have htcent : t ∈ centerOf N.S := by
      rw [hf.centerS_z]
      exact Subgroup.subset_closure (Set.mem_insert _ _)
    rw [normalizer_zpowers_eq_centralizer ht2]
    intro s hs'
    exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp htcent.2 s hs')

theorem Notation25.pCoreOf_centralizer_t_ne_bot {t zK : G} (hf : Facts2511 N t zK) :
    pCoreOf 2 (Subgroup.centralizer ({t} : Set G)) ≠ ⊥ := by
  have ht2 := N.t_mul_self hf
  obtain ⟨hE1, hEC, -⟩ := N.zpowers_t_facts hf
  have hE2 : IsPGroup 2 (Subgroup.zpowers t) :=
    N.tuple.sylow.isPGroup.to_le (hEC.trans N.SC_le_S)
  have hXE : Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers t : Set G) :=
    (normalizer_zpowers_eq_centralizer ht2).ge
  have hEX : Subgroup.zpowers t ≤ Subgroup.centralizer ({t} : Set G) := by
    rw [← normalizer_zpowers_eq_centralizer ht2]
    exact Subgroup.le_normalizer
  exact (N.isGamma_of_le hE1 hE2 hEX hXE hf.H_le).1

theorem Notation25.exists_overgroup_config {E KE : Subgroup G} (hE1 : E ≠ ⊥) (hEC : E ≤ N.SC)
    (hES : N.S ≤ Subgroup.normalizer (E : Set G)) (hKKE : N.K ≤ KE)
    (hKEX : IsComponentIn KE (Subgroup.normalizer (E : Set G))) (hnb : ¬ fusionIsBenderGroup ↥KE) :
    ∃ N' : Notation25 hs, N'.K = KE := by
  have hE2 : IsPGroup 2 E := N.tuple.sylow.isPGroup.to_le (hEC.trans N.SC_le_S)
  have hHX : N.H ≤ Subgroup.normalizer (E : Set G) :=
    N.H_le_normalizer_of (N.K0_le_centralizer_of_le_SC hEC) hES
  have hKEle : KE ≤ Subgroup.normalizer (E : Set G) := hKEX.1
  have hH'X : KE ⊔ N.S ≤ Subgroup.normalizer (E : Set G) := sup_le hKEle hES
  have hHH' : N.H ≤ KE ⊔ N.S := by
    rw [N.join]
    exact sup_le_sup_right hKKE _
  have hES' : E ≤ KE ⊔ N.S := (hEC.trans N.SC_le_S).trans le_sup_right
  have hΓ' : IsGamma M (KE ⊔ N.S) := N.isGamma_of_le hE1 hE2 hES' hH'X hHH'
  obtain ⟨htup', hU'⟩ := N.tuple_of_overgroup hΓ' hHH'
  have hKE' : IsComponentIn KE (KE ⊔ N.S) :=
    BenderBranch.isComponentIn_of_le hKEX le_sup_left hH'X
  exact ⟨{ H := KE ⊔ N.S
           S := N.S
           K := KE
           z := N.z
           x := N.x
           tuple := htup'
           gammaU := hU'
           isComp := hKE'
           nonBender := hnb
           join := rfl
           x_mem := N.x_mem
           x_not_mem := N.x_not_mem
           x_sq := N.x_sq }, rfl⟩

theorem Notation25.isComponentIn_centralizer_t (hst : EarlyStages) (h2515 : Lemma2515)
    (hnb : M11NotBender) {t zK : G} (h : Lv2516 N t zK) :
    IsComponentIn N.K (Subgroup.centralizer ({t} : Set G)) := by
  have hf := h.facts2511
  have ht2 := N.t_mul_self hf
  obtain ⟨hE1, hEC, hSX⟩ := N.zpowers_t_facts hf
  obtain ⟨-, -, hcomp | ⟨-, -, -, KE, hKE, hKEX, ⟨eE⟩⟩⟩ :=
    h.concl256 (Subgroup.zpowers t) hE1 hEC hSX
  · rwa [normalizer_zpowers_eq_centralizer ht2] at hcomp
  · exfalso
    have hKKE : N.K ≤ KE := by
      rw [hKE]
      exact (BenderBranch.conjugate_one N.K).symm.le.trans
        (le_iSup (fun g : ↥(Subgroup.normalizer (Subgroup.zpowers t : Set G)) =>
          CFSG.conjugate N.K (g : G)) ⟨1, Subgroup.one_mem _⟩)
    have hnbKE : ¬ fusionIsBenderGroup ↥KE := fun hb =>
      hnb (fusionIsBenderGroup_of_mulEquiv eE.symm hb)
    obtain ⟨N', hN'K⟩ := N.exists_overgroup_config hE1 hEC hSX hKKE hKEX hnbKE
    obtain ⟨t', zK', hlv⟩ := hst.exists_lv2513 N'
    have h15 := h2515 G T M hs N' t' zK' hlv
    apply h15.1
    rw [hN'K]
    exact ⟨eE⟩

theorem Notation25.two_dvd_card_K (h258 : Facts258 N) : 2 ∣ Nat.card N.K := by
  have h8 := eight_le_card_of_shape h258.SK_shape
  have hSK2 : IsPGroup 2 ↥N.SK := N.tuple.sylow.isPGroup.to_le N.SK_le_S
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨j, hj⟩ := hSK2.exists_card_eq
  have hdvd : Nat.card N.SK ∣ Nat.card N.K := Subgroup.card_dvd_of_le N.SK_le_K
  rw [hj] at h8 hdvd
  have hj1 : j ≠ 0 := by
    rintro rfl
    simp at h8
  exact (dvd_pow_self 2 hj1).trans hdvd

theorem Notation25.odd_eq_mul_centralizer {t zK : G} (h : Lv2516 N t zK)
    (hK : IsComponentIn N.K (Subgroup.centralizer ({t} : Set G))) {g : G}
    (hgX : g ∈ Subgroup.centralizer ({t} : Set G)) (hodd : Odd (orderOf g)) :
    ∃ k ∈ N.K, ∃ c ∈ Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer (N.K : Set G),
      g = k * c := by
  have hf := h.facts2511
  have hcen : Unc25G2.CentreTwo N.K := N.centreTwo_K h.list252.2.1
  have hgN : g ∈ Subgroup.normalizer (N.K : Set G) :=
    odd_mem_normalizer_component hs.setting.qtke.2.2 (N.pCoreOf_centralizer_t_ne_bot hf) hK hcen
      hgX hodd
  let φ : MulAut ↥N.K := conjAct N.K ⟨g, hgN⟩
  obtain ⟨k, hk⟩ := h.facts258.out_two φ
  have hφ : φ ∈ (MulAut.conj : ↥N.K →* MulAut ↥N.K).range := by
    have hord : orderOf φ ∣ orderOf g := by
      have h1 := orderOf_map_dvd (conjAct N.K) (⟨g, hgN⟩ : ↥(Subgroup.normalizer (N.K : Set G)))
      rwa [Subgroup.orderOf_mk] at h1
    have hcop : Nat.Coprime (2 ^ k) (orderOf φ) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr (hodd.of_dvd_nat hord))
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
    rw [← hm]
    exact (MulAut.conj : ↥N.K →* MulAut ↥N.K).range.pow_mem hk m
  obtain ⟨k₁, hk₁⟩ := hφ
  have hconj : ∀ y : ↥N.K, (k₁ : G) * y * (k₁ : G)⁻¹ = g * y * g⁻¹ := by
    intro y
    have h1 : ((MulAut.conj k₁ y : ↥N.K) : G) = (k₁ : G) * y * (k₁ : G)⁻¹ := rfl
    have h2 : ((φ y : ↥N.K) : G) = g * y * g⁻¹ := rfl
    rw [← h1, ← h2, hk₁]
  have hk₁X : (k₁ : G) ∈ Subgroup.centralizer ({t} : Set G) := hf.H_le (N.K_le_H k₁.2)
  refine ⟨(k₁ : G), k₁.2, (k₁ : G)⁻¹ * g,
    ⟨(Subgroup.centralizer ({t} : Set G)).mul_mem
      ((Subgroup.centralizer ({t} : Set G)).inv_mem hk₁X) hgX, ?_⟩, by group⟩
  refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
  have := hconj ⟨y, hy⟩
  calc y * ((k₁ : G)⁻¹ * g) = (k₁ : G)⁻¹ * ((k₁ : G) * y * (k₁ : G)⁻¹) * g := by group
    _ = (k₁ : G)⁻¹ * (g * y * g⁻¹) * g := by rw [this]
    _ = ((k₁ : G)⁻¹ * g) * y := by group

theorem Notation25.odd_mem_K0_mul {t zK : G} (h : Lv2516 N t zK)
    (hK : IsComponentIn N.K (Subgroup.centralizer ({t} : Set G))) {g : G}
    (hgX : g ∈ Subgroup.centralizer ({t} : Set G)) (hodd : Odd (orderOf g)) :
    ∃ a ∈ N.K0, ∃ c ∈ Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer (N.K0 : Set G),
      g = a * c := by
  have hf := h.facts2511
  obtain ⟨k₁, hk₁, c₁, hc₁, hg₁⟩ := N.odd_eq_mul_centralizer h hK hgX hodd
  rcases h.facts254.shape with hK0 | ⟨s₀, hs₀S, hne, hK0, hcomm⟩
  · refine ⟨k₁, hK0 ▸ hk₁, c₁, ⟨hc₁.1, ?_⟩, hg₁⟩
    rw [hK0]
    exact hc₁.2
  · have hs₀X : s₀ ∈ Subgroup.centralizer ({t} : Set G) := hf.H_le (N.S_le_H hs₀S)
    have hg' : s₀ * g * s₀⁻¹ ∈ Subgroup.centralizer ({t} : Set G) :=
      (Subgroup.centralizer ({t} : Set G)).mul_mem
        ((Subgroup.centralizer ({t} : Set G)).mul_mem hs₀X hgX)
        ((Subgroup.centralizer ({t} : Set G)).inv_mem hs₀X)
    have hodd' : Odd (orderOf (s₀ * g * s₀⁻¹)) := by
      have : orderOf (s₀ * g * s₀⁻¹) = orderOf g := (MulAut.conj s₀).orderOf_eq g
      rw [this]
      exact hodd
    obtain ⟨k₂, hk₂, c₂, hc₂, hg₂⟩ := N.odd_eq_mul_centralizer h hK hg' hodd'
    have hc : ∀ a ∈ N.K, ∀ b ∈ CFSG.conjugate N.K s₀, a * b = b * a := fun a ha b hb =>
      BenderBranch.commute_of_commutator_eq_bot hcomm ha hb
    set k₂' : G := s₀⁻¹ * k₂ * s₀ with hk₂'
    set c₂' : G := s₀⁻¹ * c₂ * s₀ with hc₂'
    have hgeq : g = k₂' * c₂' := by
      calc g = s₀⁻¹ * (s₀ * g * s₀⁻¹) * s₀ := by group
        _ = s₀⁻¹ * (k₂ * c₂) * s₀ := by rw [hg₂]
        _ = k₂' * c₂' := by simp only [hk₂', hc₂']; group
    have hk₂'mem : k₂' ∈ CFSG.conjugate N.K s₀ := by
      rw [BenderBranch.mem_conjugate_iff]
      have : s₀ * k₂' * s₀⁻¹ = k₂ := by simp only [hk₂']; group
      rw [this]
      exact hk₂
    have hc₂'cent : ∀ w ∈ CFSG.conjugate N.K s₀, w * c₂' = c₂' * w := by
      intro w hw
      have hw' : s₀ * w * s₀⁻¹ ∈ N.K := BenderBranch.mem_conjugate_iff.mp hw
      have := Subgroup.mem_centralizer_iff.mp hc₂.2 _ hw'
      calc w * c₂' = s₀⁻¹ * ((s₀ * w * s₀⁻¹) * c₂) * s₀ := by simp only [hc₂']; group
        _ = s₀⁻¹ * (c₂ * (s₀ * w * s₀⁻¹)) * s₀ := by rw [this]
        _ = c₂' * w := by simp only [hc₂']; group
    have hk₁k₂ : k₁ * k₂' = k₂' * k₁ := hc k₁ hk₁ k₂' hk₂'mem
    have hk₂'K0 : k₂' ∈ N.K0 := by
      rw [hK0]
      exact Subgroup.mem_sup_right hk₂'mem
    have haK0 : k₁ * k₂' ∈ N.K0 := N.K0.mul_mem (N.K_le_K0 hk₁) hk₂'K0
    refine ⟨k₁ * k₂', haK0, (k₁ * k₂')⁻¹ * g,
      ⟨(Subgroup.centralizer ({t} : Set G)).mul_mem
        ((Subgroup.centralizer ({t} : Set G)).inv_mem (hf.H_le (N.K0_le_H haK0))) hgX, ?_⟩,
      by group⟩
    have hKc : N.K ≤ Subgroup.centralizer ({(k₁ * k₂')⁻¹ * g} : Set G) := by
      intro w hw
      rw [Subgroup.mem_centralizer_singleton_iff]
      have e : (k₁ * k₂')⁻¹ * g = k₂'⁻¹ * c₁ := by
        rw [hg₁]
        group
      rw [e]
      have hcw : Commute w k₂' := hc w hw k₂' hk₂'mem
      have hcc : Commute w c₁ := Subgroup.mem_centralizer_iff.mp hc₁.2 w hw
      exact (hcw.inv_right.mul_right hcc).eq
    have hKsc : CFSG.conjugate N.K s₀ ≤ Subgroup.centralizer ({(k₁ * k₂')⁻¹ * g} : Set G) := by
      intro w hw
      rw [Subgroup.mem_centralizer_singleton_iff]
      have e : (k₁ * k₂')⁻¹ * g = k₁⁻¹ * c₂' := by
        calc (k₁ * k₂')⁻¹ * g = (k₂' * k₁)⁻¹ * g := by rw [hk₁k₂]
          _ = k₁⁻¹ * k₂'⁻¹ * (k₂' * c₂') := by rw [mul_inv_rev, hgeq]
          _ = k₁⁻¹ * c₂' := by group
      rw [e]
      have hcw : Commute w k₁ := (hc k₁ hk₁ w hw).symm
      have hcc : Commute w c₂' := hc₂'cent w hw
      exact (hcw.inv_right.mul_right hcc).eq
    have hle : N.K0 ≤ Subgroup.centralizer ({(k₁ * k₂')⁻¹ * g} : Set G) := by
      rw [hK0]
      exact sup_le hKc hKsc
    refine Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hw)

theorem Notation25.centralizer_t_le {t zK : G} (h : Lv2516 N t zK)
    (hK : IsComponentIn N.K (Subgroup.centralizer ({t} : Set G))) :
    Subgroup.centralizer ({t} : Set G) ≤ N.K0 ⊔ N.S ⊔
      (Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer (N.K0 : Set G)) := by
  refine (le_closure_odd_sup_of_isSylowTwoOf h.facts2511.sylow).trans (sup_le ?_ ?_)
  · rw [Subgroup.closure_le]
    rintro g ⟨hgX, hodd⟩
    obtain ⟨a, ha, c, hc, rfl⟩ := N.odd_mem_K0_mul h hK hgX hodd
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_sup_left ha))
      (Subgroup.mem_sup_right hc)
  · exact le_sup_right.trans le_sup_left

theorem Notation25.centralizer_t_eq {t zK : G} (h : Lv2516 N t zK)
    (hK : IsComponentIn N.K (Subgroup.centralizer ({t} : Set G))) :
    Subgroup.centralizer ({t} : Set G) = N.K0 ⊔ N.S ⊔
      (Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer (N.K0 : Set G)) :=
  le_antisymm (N.centralizer_t_le h hK)
    (sup_le (sup_le (N.K0_le_H.trans h.facts2511.H_le) (N.S_le_H.trans h.facts2511.H_le))
      inf_le_left)

theorem Notation25.inf_centralizer_K0_le_M {t zK : G} (h : Lv2516 N t zK) :
    Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer (N.K0 : Set G) ≤ M := by
  have hf := h.facts2511
  intro c hc
  have hzS : N.z ∈ centerOf N.S :=
    ⟨N.tuple.center_le N.tuple.z_mem, Subgroup.centralizer_le
      (SetLike.coe_subset_coe.mpr N.S_le_T) N.tuple.z_mem.2⟩
  have hzcl : N.z ∈ Subgroup.closure ({t, zK} : Set G) := by
    rw [← hf.centerS_zK]
    exact hzS
  have hct : c * t = t * c := Subgroup.mem_centralizer_singleton_iff.mp hc.1
  have hczK : zK * c = c * zK := Subgroup.mem_centralizer_iff.mp hc.2 zK hf.zK_mem
  have hle : Subgroup.closure ({t, zK} : Set G) ≤ Subgroup.centralizer ({c} : Set G) := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | hx
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hct.symm
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact Subgroup.mem_centralizer_singleton_iff.mpr hczK
  have hzc : N.z * c = c * N.z := Subgroup.mem_centralizer_singleton_iff.mp (hle hzcl)
  exact hs.setting.centralizer_le_of_mem_center_isSylowTwoOf hs.setting.isSylowTwoOf_M
    N.tuple.z_mem N.tuple.z_ne_one (Subgroup.mem_centralizer_singleton_iff.mpr hzc.symm)

theorem Notation25.centralizer_t_le_normalizer_K0 {t zK : G} (h : Lv2516 N t zK)
    (hK : IsComponentIn N.K (Subgroup.centralizer ({t} : Set G))) :
    Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (N.K0 : Set G) := by
  rw [N.centralizer_t_eq h hK]
  refine sup_le (sup_le Subgroup.le_normalizer (N.S_le_H.trans N.H_le_normalizer_K0)) ?_
  intro c hc
  exact Subgroup.centralizer_le_normalizer _ hc.2

theorem Notation25.charTwo_inf_centralizer_K0 {t zK : G} (h : Lv2516 N t zK)
    (hK : IsComponentIn N.K (Subgroup.centralizer ({t} : Set G))) :
    CharTwo (Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer (N.K0 : Set G)) := by
  have hf := h.facts2511
  have hSXM : IsSylowTwoOf N.S (Subgroup.centralizer ({t} : Set G) ⊓ M) :=
    isSylowTwoOf_of_sylow_le hf.sylow
      (le_inf hf.sylow.le fun s hs' => hs.setting.le (N.S_le_T hs')) inf_le_left
  have hfm : CharTwo (Subgroup.centralizer ({t} : Set G) ⊓ M) :=
    IsGamma0.charTwo_inf hs.setting (Or.inl hf.gammaU) hSXM
  have hCM : Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer (N.K0 : Set G) ≤
      Subgroup.centralizer ({t} : Set G) ⊓ M := le_inf inf_le_left (N.inf_centralizer_K0_le_M h)
  have hXN := N.centralizer_t_le_normalizer_K0 h hK
  have hnorm : ((Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer (N.K0 : Set G)).subgroupOf
      (Subgroup.centralizer ({t} : Set G) ⊓ M)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hCM]
    intro c x hc hx
    refine ⟨(Subgroup.centralizer ({t} : Set G)).mul_mem
      ((Subgroup.centralizer ({t} : Set G)).mul_mem hx.1 hc.1)
      ((Subgroup.centralizer ({t} : Set G)).inv_mem hx.1), ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
    have hxinv : x⁻¹ ∈ Subgroup.normalizer (N.K0 : Set G) :=
      (Subgroup.normalizer (N.K0 : Set G)).inv_mem (hXN hx.1)
    have hw' : x⁻¹ * w * x ∈ N.K0 := by
      have := (Subgroup.mem_normalizer_iff.mp hxinv w).mp hw
      simpa using this
    have hcc := Subgroup.mem_centralizer_iff.mp hc.2 _ hw'
    calc w * (x * c * x⁻¹) = x * ((x⁻¹ * w * x) * c) * x⁻¹ := by group
      _ = x * (c * (x⁻¹ * w * x)) * x⁻¹ := by rw [hcc]
      _ = x * c * x⁻¹ * w := by group
  exact CharTwo.of_isSubnormal hfm hCM hnorm.isSubnormal

theorem Notation25.oddCoreIn_centralizer_t_eq_bot {t zK : G} (h : Lv2516 N t zK)
    (hK : IsComponentIn N.K (Subgroup.centralizer ({t} : Set G))) :
    oddCoreIn (Subgroup.centralizer ({t} : Set G)) = ⊥ := by
  have hf := h.facts2511
  have hCh := N.charTwo_inf_centralizer_K0 h hK
  have hcen : Unc25G2.CentreTwo N.K := N.centreTwo_K h.list252.2.1
  have hKodd : N.K ⊓ oddCoreIn (Subgroup.centralizer ({t} : Set G)) = ⊥ :=
    inf_oddCoreIn_eq_bot_of_simple (N.K_le_H.trans hf.H_le) h.facts258.simple
      (N.two_dvd_card_K h.facts258)
  have hcenK : ∀ y ∈ oddCoreIn (Subgroup.centralizer ({t} : Set G)), ∀ w ∈ N.K,
      w * y = y * w := by
    intro y hy w hw
    have hyX : y ∈ Subgroup.centralizer ({t} : Set G) := oddCoreIn_le _ hy
    have hodd : Odd (orderOf y) :=
      (odd_card_oddCoreIn _).of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hy)
    have hyN : y ∈ Subgroup.normalizer (N.K : Set G) :=
      odd_mem_normalizer_component hs.setting.qtke.2.2 (N.pCoreOf_centralizer_t_ne_bot hf) hK hcen
        hyX hodd
    have hwX : w ∈ Subgroup.centralizer ({t} : Set G) := hf.H_le (N.K_le_H hw)
    have hc1 : y * w⁻¹ * y⁻¹ ∈ N.K :=
      (Subgroup.mem_normalizer_iff.mp hyN w⁻¹).mp (N.K.inv_mem hw)
    have hc2 : w * (y * w⁻¹ * y⁻¹) ∈ N.K := N.K.mul_mem hw hc1
    have hc3 : w * (y * w⁻¹ * y⁻¹) ∈ oddCoreIn (Subgroup.centralizer ({t} : Set G)) := by
      have h1 : w * y * w⁻¹ ∈ oddCoreIn (Subgroup.centralizer ({t} : Set G)) :=
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_oddCoreIn _ hwX) y).mp hy
      have h2 := (oddCoreIn (Subgroup.centralizer ({t} : Set G))).mul_mem h1
        ((oddCoreIn (Subgroup.centralizer ({t} : Set G))).inv_mem hy)
      have e : w * (y * w⁻¹ * y⁻¹) = w * y * w⁻¹ * y⁻¹ := by group
      rw [e]
      exact h2
    have h4 : w * (y * w⁻¹ * y⁻¹) = 1 := by
      have : w * (y * w⁻¹ * y⁻¹) ∈ N.K ⊓ oddCoreIn (Subgroup.centralizer ({t} : Set G)) :=
        ⟨hc2, hc3⟩
      rw [hKodd] at this
      exact Subgroup.mem_bot.mp this
    calc w * y = (w * (y * w⁻¹ * y⁻¹)) * (y * w) := by group
      _ = y * w := by rw [h4, one_mul]
  have hcenK0 : ∀ y ∈ oddCoreIn (Subgroup.centralizer ({t} : Set G)),
      y ∈ Subgroup.centralizer (N.K0 : Set G) := by
    intro y hy
    rcases h.facts254.shape with hK0 | ⟨s₀, hs₀S, hne, hK0, hcomm⟩
    · refine Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
      rw [hK0] at hw
      exact hcenK y hy w hw
    · have hs₀X : s₀ ∈ Subgroup.centralizer ({t} : Set G) := hf.H_le (N.S_le_H hs₀S)
      have hy' : s₀ * y * s₀⁻¹ ∈ oddCoreIn (Subgroup.centralizer ({t} : Set G)) :=
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_oddCoreIn _ hs₀X) y).mp hy
      have hKs : CFSG.conjugate N.K s₀ ≤ Subgroup.centralizer ({y} : Set G) := by
        intro w hw
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hw' : s₀ * w * s₀⁻¹ ∈ N.K := BenderBranch.mem_conjugate_iff.mp hw
        have := hcenK _ hy' _ hw'
        calc w * y = s₀⁻¹ * ((s₀ * w * s₀⁻¹) * (s₀ * y * s₀⁻¹)) * s₀ := by group
          _ = s₀⁻¹ * ((s₀ * y * s₀⁻¹) * (s₀ * w * s₀⁻¹)) * s₀ := by rw [this]
          _ = y * w := by group
      have hKy : N.K ≤ Subgroup.centralizer ({y} : Set G) := by
        intro w hw
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact hcenK y hy w hw
      have hle : N.K0 ≤ Subgroup.centralizer ({y} : Set G) := by
        rw [hK0]
        exact sup_le hKy hKs
      refine Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle hw)
  rw [eq_bot_iff]
  intro y hy
  have hyC : y ∈ Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer (N.K0 : Set G) :=
    ⟨oddCoreIn_le _ hy, hcenK0 y hy⟩
  have hmem : y ∈ oddCoreIn (Subgroup.centralizer ({t} : Set G)) ⊓
      (Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer (N.K0 : Set G)) := ⟨hy, hyC⟩
  rw [oddCoreIn_inf_eq_bot hCh inf_le_left] at hmem
  exact hmem

end Config

theorem lemma2518 (hst : EarlyStages) (h2515 : Lemma2515) (hnb : M11NotBender) : Lemma2518 := by
  intro G _ _ T M hs N t zK h
  have hK := N.isComponentIn_centralizer_t hst h2515 hnb h
  refine ⟨hK, N.centralizer_t_eq h hK, sup_le (N.inf_centralizer_K0_le_M h) ?_,
    N.charTwo_inf_centralizer_K0 h hK, N.oddCoreIn_centralizer_t_eq_bot h hK⟩
  intro s hs'
  exact hs.setting.le (N.S_le_T hs')

end CFSG.QuasithinUnique
