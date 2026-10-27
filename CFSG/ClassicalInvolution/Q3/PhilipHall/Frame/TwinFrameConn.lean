module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrame
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPair
public import CFSG.ClassicalInvolution.SmallCases.A7Q4
public import CFSG.ClassicalInvolution.SmallCases.A7Q1C

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Balance.Bootstrap

namespace TwinFrame

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

@[expose] def Conn (Ω : Set (Subgroup G)) : Subgroup G → Subgroup G → Prop :=
  Relation.ReflTransGen (fun X Y => X ∈ frameSet Ω ∧ Y ∈ frameSet Ω ∧ ShareFour X Y)

theorem Conn.symm {B B' : Subgroup G} (h : Conn Ω B B') : Conn Ω B' B := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head ⟨hbc.2.1, hbc.1, hbc.2.2.symm⟩ ih

theorem Conn.trans {B B' B'' : Subgroup G} (h : Conn Ω B B') (h' : Conn Ω B' B'') :
    Conn Ω B B'' :=
  Relation.ReflTransGen.trans h h'

theorem conn_of_shareFour {B B' : Subgroup G} (hB : B ∈ frameSet Ω) (hB' : B' ∈ frameSet Ω)
    (h : ShareFour B B') : Conn Ω B B' :=
  Relation.ReflTransGen.single ⟨hB, hB', h⟩

theorem oddCore_le_rankTwoSpan {B : Subgroup G} {z : G} (hB : IsElemAbelian 2 B)
    (hB8 : Nat.card B = 8) (hBC : B ≤ Subgroup.centralizer ({z} : Set G)) :
    oddCoreOf (Subgroup.centralizer ({z} : Set G)) ≤ rankTwoSpan B := by
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 2 2
    Nat.prime_two B (oddCoreOf (Subgroup.centralizer ({z} : Set G))) hB
    (by rw [hB8]; norm_num)
    (fun b hb => CFSG.ClassicalInvolution.Balance.normalizer_oddCoreIn _ (hBC hb))
    (Nat.coprime_two_left.mpr
      (CFSG.ClassicalInvolution.Balance.odd_card_oddCoreIn (Subgroup.centralizer ({z} : Set G))))
  conv_lhs => rw [← hgen]
  refine iSup₂_le fun E hE => inf_le_right.trans ?_
  exact le_iSup₂ (f := fun (F : Subgroup G) (_ : F ∈ signalizerFunctorEk 2 2 B) =>
    Subgroup.centralizer (F : Set G)) E hE

section Twins


theorem twin_le_rankTwoSpan (hΩ : HypOmegaGen Ω) {K K' J : Subgroup G} {z u t : G}
    (h : TwinFrameData Ω K K' z u J t) {L : Subgroup G} (hL : L ∈ twinSet Ω K) :
    L ≤ rankTwoSpan (Subgroup.closure ({z, u, t} : Set G)) := by
  obtain ⟨hB, hB8⟩ := shape_of_frameData hΩ h
  have hzt : z * t = t * z := A7Q.Gen.comm_zt hΩ h
  have hBC : Subgroup.closure ({z, u, t} : Set G) ≤ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl | rfl
    · exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
    · exact Subgroup.mem_centralizer_singleton_iff.mpr h.comm_zu.symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hzt.symm
  have hO := oddCore_le_rankTwoSpan hB hB8 hBC
  have hzL := isUniqueInvolution_of_mem_twinSet h.hz hL
  have hsub := isSubnormal_of_hypOmegaGen hΩ hL.1 hzL
  intro ℓ hℓ
  have hℓC : ℓ ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hzL.commute_of_mem hℓ).symm
  have htC : t ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hzt.symm
  have hc' : t * ℓ * t⁻¹ * ℓ⁻¹ ∈ oddCoreOf (Subgroup.centralizer ({z} : Set G)) := by
    have := A7Q.Gen.commutator_twin_mem_oddCoreOf hΩ h hL hsub ℓ hℓ
    rwa [commutatorElement_def] at this
  obtain ⟨o, hoO, hfix⟩ := T7A.exists_fixed_mul_of_odd
    (CFSG.ClassicalInvolution.Balance.odd_card_oddCoreIn (Subgroup.centralizer ({z} : Set G)))
    h.ht.sq (CFSG.ClassicalInvolution.Balance.normalizer_oddCoreIn _ htC)
    (CFSG.ClassicalInvolution.Balance.normalizer_oddCoreIn _ hℓC) hc'
  have hcz : ℓ * o ∈ Subgroup.centralizer ({z} : Set G) := Subgroup.mul_mem _ hℓC
    (CFSG.ClassicalInvolution.Balance.oddCoreIn_le _ hoO)
  have hct : (ℓ * o) * t = t * (ℓ * o) := (mul_inv_eq_iff_eq_mul.mp hfix).symm
  have hcE : ℓ * o ∈ Subgroup.centralizer
      ((Subgroup.closure ({z, t} : Set G) : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have hle : Subgroup.closure ({z, t} : Set G) ≤ Subgroup.centralizer ({ℓ * o} : Set G) := by
      rw [Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | rfl
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_singleton_iff.mp hcz).symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hct.symm
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle he)
  have h1 : Subgroup.centralizer ((Subgroup.closure ({z, t} : Set G) : Subgroup G) : Set G) ≤
      rankTwoSpan (Subgroup.closure ({z, u, t} : Set G)) :=
    le_iSup₂ (f := fun (F : Subgroup G) (_ : F ∈ signalizerFunctorEk 2 2
      (Subgroup.closure ({z, u, t} : Set G))) => Subgroup.centralizer (F : Set G))
      (Subgroup.closure ({z, t} : Set G)) (closure_zt_mem hΩ h)
  have h2 : (ℓ * o) * o⁻¹ ∈ rankTwoSpan (Subgroup.closure ({z, u, t} : Set G)) :=
    Subgroup.mul_mem _ (h1 hcE) (Subgroup.inv_mem _ (hO hoO))
  rwa [mul_inv_cancel_right] at h2

theorem conn_map_of_twin (hΩ : HypOmegaGen Ω) {K K' J : Subgroup G} {z u t : G}
    (h : TwinFrameData Ω K K' z u J t) {L L' : Subgroup G} (hL : L ∈ twinSet Ω K)
    (hL' : L' ∈ twinSet Ω K) {g : G} (hg : g ∈ L ⊔ L') :
    Conn Ω (Subgroup.closure ({z, u, t} : Set G))
      (Subgroup.closure ({z, g * u * g⁻¹, g * t * g⁻¹} : Set G)) := by
  have hgs : g ∈ rankTwoSpan (Subgroup.closure ({z, u, t} : Set G)) :=
    sup_le (twin_le_rankTwoSpan hΩ h hL) (twin_le_rankTwoSpan hΩ h hL') hg
  have hzg : z * g = g * z := T7A.z_comm_of_mem_sup (isUniqueInvolution_of_mem_twinSet h.hz hL)
    (isUniqueInvolution_of_mem_twinSet h.hz hL') hg
  have hgz : g * z * g⁻¹ = z := by
    calc g * z * g⁻¹ = (z * g) * g⁻¹ := by rw [hzg]
      _ = z := by group
  have := Balance.Theorem5.reflTransGen_shareFour_map_of_mem_rankTwoSpan
    (fun A hA g => frameSet_conj hΩ.conjInvariant hA g) (closure_mem_frameSet h) hgs
  rw [map_conj_closure_three, hgz] at this
  exact this

theorem exists_frame_swap (hΩ : HypOmegaGen Ω) {K K' J : Subgroup G} {z u t : G}
    (h : TwinFrameData Ω K K' z u J t) {J' : Subgroup G} (hJ' : J' ∈ twinSet Ω J)
    (hne : J' ≠ J) : ∃ v : G, TwinFrameData Ω J J' t v K z := by
  have hJΩ : J ∈ Ω := h.hJ.1
  have hJ'Ω : J' ∈ Ω := hJ'.1
  have htJ' : IsUniqueInvolution J' t := isUniqueInvolution_of_mem_twinSet h.ht hJ'
  have hKnbr : K ∈ omegaNbr Ω J := Q3.Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ h.mem hJΩ
    (h.hJ.2 K (mem_twinSet_self h.mem h.hz))
  have hKnot : K ∉ twinSet Ω J := by
    rintro ⟨-, z', hz'J, hz'K⟩
    exact h.t_ne_z ((h.ht.eq hz'J).trans (h.hz.eq hz'K).symm)
  have hKo : K ∈ omegaOfSet Ω (twinSet Ω J) :=
    A7Q.Gen.mem_omegaOfSet_of_mem_kPerp hΩ hJΩ (Set.mem_insert_of_mem _ hKnbr) hKnot
  obtain ⟨-, R, R', T, hR, hR', hT, -, -, -, hRR', hRT, hR'T⟩ :=
    A7Q.Gen.exists_twinSylow hΩ hJΩ h.ht hJ' hne hKo
  obtain ⟨x, hxR, hx4⟩ :=
    (Sec6Gen.isQuatSub_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hJΩ hR)).exists_orderOf_four
  obtain ⟨y, hyR', hy4⟩ :=
    (Sec6Gen.isQuatSub_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hJ'Ω hR')).exists_orderOf_four
  have hxJ : x ∈ J := hR.1 hxR
  have hyJ' : y ∈ J' := hR'.1 hyR'
  have hsqx : x * x = t := T7A.sq_eq_of_orderOf_four h.ht hxJ hx4
  have hsqy : y * y = t := T7A.sq_eq_of_orderOf_four htJ' hyJ' hy4
  have hcxy : x * y = y * x := hRR' x hxR y hyR'
  have hxJ' : x ∉ J' := A7Q.Gen.not_mem_of_orderOf_four hΩ hJΩ hJ'Ω hne hx4 hxJ
  have hu2 : (x * y) * (x * y) = 1 := by
    calc (x * y) * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [← hcxy]
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [hsqx, hsqy, h.ht.sq]
  have hu1 : x * y ≠ 1 := by
    intro e
    apply hxJ'
    rw [eq_inv_of_mul_eq_one_left e]
    exact J'.inv_mem hyJ'
  have hut : x * y ≠ t := by
    intro e
    apply hxJ'
    have : x = t * y⁻¹ := by rw [← e]; group
    rw [this]
    exact J'.mul_mem htJ'.mem (J'.inv_mem hyJ')
  have hT8 : 8 ≤ Nat.card T := Sec6Gen.eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In h.mem hT)
  have hzT : z ∈ T := mem_of_isUniqueInvolution_of_isPGroup h.hz hT.1 hT.2.1 (by omega)
  have hxz : x * z = z * x := hRT x hxR z hzT
  have hyz : y * z = z * y := hR'T y hyR' z hzT
  refine ⟨x * y, hJΩ, h.ht, hJ', hne, Subgroup.mul_mem _ (Subgroup.mem_sup_left hxJ)
    (Subgroup.mem_sup_right hyJ'), hu2, hu1, hut, hKo, h.hz, ?_⟩
  calc z * (x * y) = (z * x) * y := by group
    _ = (x * z) * y := by rw [hxz]
    _ = x * (z * y) := by group
    _ = x * (y * z) := by rw [hyz]
    _ = (x * y) * z := by group

theorem conn_swap (hΩ : HypOmegaGen Ω) {K K' J J' : Subgroup G} {z u t v : G}
    (h : TwinFrameData Ω K K' z u J t) (h' : TwinFrameData Ω J J' t v K z) :
    Conn Ω (Subgroup.closure ({z, u, t} : Set G)) (Subgroup.closure ({t, v, z} : Set G)) := by
  refine conn_of_shareFour (closure_mem_frameSet h) (closure_mem_frameSet h')
    ⟨Subgroup.closure ({z, t} : Set G), closure_zt_mem hΩ h, ?_⟩
  have := closure_zt_mem hΩ h'
  rwa [Set.pair_comm t z] at this

theorem conn_of_same_z (hΩ : HypOmegaGen Ω) {K₁ K₁' J₁ K₂ K₂' J₂ : Subgroup G}
    {z u₁ t₁ u₂ t₂ : G} (h₁ : TwinFrameData Ω K₁ K₁' z u₁ J₁ t₁)
    (h₂ : TwinFrameData Ω K₂ K₂' z u₂ J₂ t₂) :
    Conn Ω (Subgroup.closure ({z, u₁, t₁} : Set G)) (Subgroup.closure ({z, u₂, t₂} : Set G)) := by
  have hzK₁' := isUniqueInvolution_of_mem_twinSet h₁.hz h₁.hK'
  have hK₂tw : K₂ ∈ twinSet Ω K₁ := ⟨h₂.mem, z, h₁.hz, h₂.hz⟩
  have hK₁tw : K₁ ∈ twinSet Ω K₂ := ⟨h₁.mem, z, h₂.hz, h₁.hz⟩
  have hK₁'tw : K₁' ∈ twinSet Ω K₂ := ⟨h₁.hK'.1, z, h₂.hz, hzK₁'⟩
  have htw : twinSet Ω K₂ = twinSet Ω K₁ := twinSet_eq_of_mem_twinSet h₁.hz hK₂tw
  have hJ₂ : J₂ ∈ omegaOfSet Ω (twinSet Ω K₁) := htw ▸ h₂.hJ
  obtain ⟨g, hg, h₁'⟩ := A7Q.Gen.exists_twinFrameData_at hΩ h₁.mem h₁.hz h₁.hK' h₁.hne h₁.hu
    h₁.hu2 h₁.hu1 h₁.huz hJ₂ h₂.ht
  have hzg : z * g = g * z := T7A.z_comm_of_mem_sup h₁.hz hzK₁' hg
  have hgz : g * z * g⁻¹ = z := by
    calc g * z * g⁻¹ = (z * g) * g⁻¹ := by rw [hzg]
      _ = z := by group
  have h₂g := frameData_conj hΩ.conjInvariant h₂ g
  rw [hgz] at h₂g
  have c1 : Conn Ω (Subgroup.closure ({z, u₁, t₁} : Set G))
      (Subgroup.closure ({z, u₁, g * t₂ * g⁻¹} : Set G)) :=
    conn_of_shareFour (closure_mem_frameSet h₁) (closure_mem_frameSet h₁')
      ⟨Subgroup.closure ({z, u₁} : Set G), closure_zu_mem h₁, closure_zu_mem h₁'⟩
  have c2 : Conn Ω (Subgroup.closure ({z, u₁, g * t₂ * g⁻¹} : Set G))
      (Subgroup.closure ({z, g * u₂ * g⁻¹, g * t₂ * g⁻¹} : Set G)) :=
    conn_of_shareFour (closure_mem_frameSet h₁') (closure_mem_frameSet h₂g)
      ⟨Subgroup.closure ({z, g * t₂ * g⁻¹} : Set G), closure_zt_mem hΩ h₁', closure_zt_mem hΩ h₂g⟩
  have c3 := conn_map_of_twin hΩ h₂ hK₁tw hK₁'tw hg
  exact c1.trans (c2.trans c3.symm)

theorem exists_frame_at_J (hΩ : HypOmegaGen Ω) {K K' J : Subgroup G} {z u t : G}
    (h : TwinFrameData Ω K K' z u J t) {N : Subgroup G} {tN : G}
    (hN : N ∈ omegaOfSet Ω (twinSet Ω K)) (htN : IsUniqueInvolution N tN) :
    ∃ u' : G, TwinFrameData Ω K K' z u' N tN ∧
      Conn Ω (Subgroup.closure ({z, u, t} : Set G)) (Subgroup.closure ({z, u', tN} : Set G)) := by
  have hzK' := isUniqueInvolution_of_mem_twinSet h.hz h.hK'
  obtain ⟨g, hg, h₁⟩ := A7Q.Gen.exists_twinFrameData_at hΩ h.mem h.hz h.hK' h.hne h.hu h.hu2
    h.hu1 h.huz hN htN
  have hgi : g⁻¹ ∈ K ⊔ K' := Subgroup.inv_mem _ hg
  obtain ⟨hgK, hgK'⟩ := A7Q.Gen.conjSub_eq_of_mem_sup hΩ h.mem h.hK'.1 h.hne h.hz hzK' hgi
  have hzg : z * g⁻¹ = g⁻¹ * z := T7A.z_comm_of_mem_sup h.hz hzK' hgi
  have hgz : g⁻¹ * z * g⁻¹⁻¹ = z := by
    calc g⁻¹ * z * g⁻¹⁻¹ = (z * g⁻¹) * g⁻¹⁻¹ := by rw [hzg]
      _ = z := by group
  have hgt : g⁻¹ * (g * tN * g⁻¹) * g⁻¹⁻¹ = tN := by group
  have h₃ := frameData_conj hΩ.conjInvariant h₁ g⁻¹
  rw [hgK, hgK', hgz, conjSub_inv_conjSub, hgt] at h₃
  refine ⟨g⁻¹ * u * g⁻¹⁻¹, h₃, ?_⟩
  have c1 : Conn Ω (Subgroup.closure ({z, u, t} : Set G))
      (Subgroup.closure ({z, u, g * tN * g⁻¹} : Set G)) :=
    conn_of_shareFour (closure_mem_frameSet h) (closure_mem_frameSet h₁)
      ⟨Subgroup.closure ({z, u} : Set G), closure_zu_mem h, closure_zu_mem h₁⟩
  have c2 := conn_map_of_twin hΩ h₁ (mem_twinSet_self h.mem h.hz) h.hK' hgi
  rw [hgt] at c2
  exact c1.trans c2

theorem exists_twin_of_trans (hΩ : HypOmegaGen Ω)
    (htr : ∀ M ∈ Ω, ∀ N ∈ Ω, ∃ g : G, conjSub g M = N) {K K' : Subgroup G} (hK : K ∈ Ω)
    (hK' : K' ∈ twinSet Ω K) (hne : K' ≠ K) {N : Subgroup G} (hN : N ∈ Ω) :
    ∃ N' ∈ twinSet Ω N, N' ≠ N := by
  obtain ⟨g, hg⟩ := htr K hK N hN
  refine ⟨conjSub g K', ?_, fun e => hne (conjSub_injective g (e.trans hg.symm))⟩
  have := twinSet_conj hΩ.conjInvariant hK' g
  rwa [hg] at this

omit [Finite G] in
theorem trans_conjClass (K₀ : Subgroup G) :
    ∀ M ∈ CoreAssembly.conjClass K₀, ∀ N ∈ CoreAssembly.conjClass K₀,
      ∃ g : G, conjSub g M = N := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  refine ⟨b * a⁻¹, ?_⟩
  rw [conjSub_mul, conjSub_inv_conjSub]

theorem frameSet_connected (hΩ : HypOmegaGen Ω)
    (htr : ∀ M ∈ Ω, ∀ N ∈ Ω, ∃ g : G, conjSub g M = N) (hconn : DConnected Ω) :
    ∀ B ∈ frameSet Ω, ∀ B' ∈ frameSet Ω, Conn Ω B B' := by
  intro B₀ hB₀ B' hB'
  obtain ⟨K₀, K₀', J₀, z₀, u₀, t₀, h₀, rfl⟩ := hB₀
  let P : Subgroup G → Prop := fun M => ∃ (M' J : Subgroup G) (z u t : G),
    TwinFrameData Ω M M' z u J t ∧
      Conn Ω (Subgroup.closure ({z₀, u₀, t₀} : Set G)) (Subgroup.closure ({z, u, t} : Set G))
  have hP₀ : P K₀ := ⟨K₀', J₀, z₀, u₀, t₀, h₀, Relation.ReflTransGen.refl⟩
  have step : ∀ M N : Subgroup G, P M → N ∈ omegaNbr Ω M → P N := by
    rintro M N ⟨M', J, z, u, t, h, hc⟩ hNn
    have hNΩ : N ∈ Ω := hNn.1
    by_cases hNt : N ∈ twinSet Ω M
    ·
      have hzN := isUniqueInvolution_of_mem_twinSet h.hz hNt
      have hMN : M ∈ twinSet Ω N := ⟨h.mem, z, hzN, h.hz⟩
      have hMne : M ≠ N := fun e => hNn.2.1 e.symm
      have hJt : J ∉ twinSet Ω N := by
        intro hJt
        rw [twinSet_eq_of_mem_twinSet h.hz hNt] at hJt
        exact (h.hJ.2 J hJt).2.1 rfl
      have hJperp : J ∈ KPerp Ω N := by
        rw [← A7Q.Gen.kPerp_eq_of_twin hΩ h.mem hNt]
        exact Set.mem_insert_of_mem _ (h.hJ.2 M (mem_twinSet_self h.mem h.hz))
      have hperp : KPerp Ω N ≠ twinSet Ω N := fun e => hJt (e ▸ hJperp)
      obtain ⟨u'', J'', t'', h''⟩ := A7Q.Gen.exists_twinFrameData hΩ hNΩ hzN hMN hMne hperp
      exact ⟨M, J'', z, u'', t'', h'', hc.trans (conn_of_same_z hΩ h h'')⟩
    ·
      have hNo : N ∈ omegaOfSet Ω (twinSet Ω M) :=
        A7Q.Gen.mem_omegaOfSet_of_mem_kPerp hΩ h.mem (Set.mem_insert_of_mem _ hNn) hNt
      obtain ⟨tN, htN⟩ := Sec6Gen.exists_uniqueInvolution hΩ hNΩ
      obtain ⟨u', h', hcc⟩ := exists_frame_at_J hΩ h hNo htN
      obtain ⟨N', hN'tw, hN'ne⟩ := exists_twin_of_trans hΩ htr h.mem h.hK' h.hne hNΩ
      obtain ⟨v, hv⟩ := exists_frame_swap hΩ h' hN'tw hN'ne
      exact ⟨N', M, tN, v, z, hv, hc.trans (hcc.trans (conn_swap hΩ h' hv))⟩
  have all' : ∀ M : Subgroup G,
      Relation.ReflTransGen (fun X Y : Subgroup G => Y ∈ Ω ∧ dAdj Ω X Y) K₀ M → M ∈ Ω ∧ P M := by
    intro M hpath
    induction hpath with
    | refl => exact ⟨h₀.mem, hP₀⟩
    | @tail b c _ hstep ih =>
      obtain ⟨hcΩ, hadj⟩ := hstep
      refine ⟨hcΩ, ?_⟩
      rcases hadj with hbc | hcb
      · exact step b c ih.2 hbc
      · exact step b c ih.2 (Q3.Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hcΩ ih.1 hcb)
  have all : ∀ M ∈ Ω, P M := fun M hM => (all' M (hconn K₀ h₀.mem M hM)).2
  obtain ⟨K₁, K₁', J₁, z₁, u₁, t₁, h₁, rfl⟩ := hB'
  obtain ⟨M', J, z, u, t, h, hc⟩ := all K₁ h₁.mem
  have hzz : z = z₁ := h.hz.eq h₁.hz
  subst hzz
  exact hc.trans (conn_of_same_z hΩ h h₁)

end Twins

end TwinFrame

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
