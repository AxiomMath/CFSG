module

public import CFSG.Adapters.QiuzhenLegacy.FeitThompson.Gorenstein.Normality
public import CFSG.GroupTheory.ABGLocalTools.ZJFactorization
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection6.Defs

public section

namespace CFSG.ABGTheoremB.RelativeZJ

open CFSG CFSG.ABGLocalTools Subgroup
open scoped Pointwise commutatorElement

section

variable {G : Type*} [Group G]


private theorem rzj_thompsonSubgroup_top_map_subtype (P : Subgroup G) :
    (thompsonSubgroup (G := P) (⊤ : Subgroup P)).map P.subtype = thompsonSubgroup (G := G) P :=
  CFSG.thompsonSubgroup_top_map_subtype P

private theorem rzj_centerIn_top_map_subtype (P : Subgroup G) (H : Subgroup P) :
    (centerIn (G := P) H).map P.subtype = centerIn (G := G) (H.map P.subtype) :=
  CFSG.centerIn_top_map_subtype P H

private theorem rzj_thompsonCenter_top_map_subtype (P : Subgroup G) :
    (thompsonCenter (G := P) (⊤ : Subgroup P)).map P.subtype = thompsonCenter (G := G) P :=
  CFSG.thompsonCenter_top_map_subtype P

private theorem rzj_centerIn_map_mulEquiv {H : Type*} [Group H] [Finite H] (e : G ≃* H)
    (J : Subgroup G) :
    (centerIn (G := G) J).map e.toMonoidHom = centerIn (G := H) (J.map e.toMonoidHom) :=
  CFSG.centerIn_map_mulEquiv e J

private theorem rzj_thompsonSubgroup_top_map_mulEquiv {H : Type*} [Group H] [Finite H]
    (e : G ≃* H) :
    (thompsonSubgroup (G := G) (⊤ : Subgroup G)).map e.toMonoidHom =
      thompsonSubgroup (G := H) (⊤ : Subgroup H) :=
  CFSG.thompsonSubgroup_top_map_mulEquiv e

private theorem rzj_thompsonCenter_top_map_mulEquiv {H : Type*} [Group H] [Finite H] (e : G ≃* H) :
    (thompsonCenter (G := G) (⊤ : Subgroup G)).map e.toMonoidHom =
      thompsonCenter (G := H) (⊤ : Subgroup H) :=
  CFSG.thompsonCenter_top_map_mulEquiv e

section ConstraintAndStability

variable (p : ℕ) [Fact p.Prime]

variable [Finite G]

private theorem rzj_quotient_pPrimeCore_subgroupMap_injective
    (H : Subgroup G) (hHp : IsPGroup p H) :
    Function.Injective ((QuotientGroup.mk' (pPrimeCore p G)).comp H.subtype) :=
  CFSG.quotient_pPrimeCore_subgroupMap_injective (p := p) H hHp

private theorem rzj_pConstrained_quotient_pPrimeCore
    (hconstrained : PConstrainedGroup (G := G) p) :
    PConstrainedGroup (G := G ⧸ pPrimeCore p G) p := by
  classical
  let M : Subgroup G := pPrimeCore p G
  let q : G →* G ⧸ M := QuotientGroup.mk' M
  let T : Sylow p (Op_p'p p G) := Classical.choice (Sylow.nonempty (p := p) (G := Op_p'p p G))
  let TG : Subgroup G := T.1.map (Op_p'p p G).subtype
  let Tbar : Subgroup (G ⧸ M) := TG.map q
  have hqsurj : Function.Surjective q := QuotientGroup.mk'_surjective M
  have hMnormal : M.Normal := by
    dsimp [M]
    infer_instance
  have hMcop : Nat.Coprime p (Nat.card M) := by
    simpa [M] using (pPrimeCore_coprime_card (G := G) (p := p))
  have hTG_p : IsPGroup p TG := by
    simpa [TG] using
      (IsPGroup.map (p := p) (H := (T : Subgroup (Op_p'p p G))) T.isPGroup'
        (Op_p'p p G).subtype)
  have hTG_le_op : TG ≤ Op_p'p p G := by
    simpa [TG] using
      (Subgroup.map_subtype_le (H := Op_p'p p G) (K := (T : Subgroup (Op_p'p p G))))
  have hmap_op : (Op_p'p p G).map q = pCore p (G ⧸ M) := by
    dsimp [Op_p'p, q, M]
    simpa using
      (Subgroup.map_comap_eq_self_of_surjective
        (f := QuotientGroup.mk' (pPrimeCore p G))
        (h := QuotientGroup.mk'_surjective (pPrimeCore p G))
        (H := pCore p (G ⧸ pPrimeCore p G)))
  have hTbar_le_pcore : Tbar ≤ pCore p (G ⧸ M) := by
    exact (Subgroup.map_mono hTG_le_op).trans hmap_op.le
  let f : Op_p'p p G →* pCore p (G ⧸ M) :=
    ((q.comp (Op_p'p p G).subtype)).codRestrict (pCore p (G ⧸ M)) (by
      intro x
      have hxmap : (q (x : G) : G ⧸ M) ∈ (Op_p'p p G).map q :=
        Subgroup.mem_map.mpr ⟨(x : G), x.property, rfl⟩
      exact hmap_op ▸ hxmap)
  have hf_surj : Function.Surjective f := by
    intro y
    rcases hqsurj y.1 with ⟨x, hx⟩
    refine ⟨⟨x, ?_⟩, ?_⟩
    · have hxmem : (q x : G ⧸ M) ∈ pCore p (G ⧸ M) := by
        simp [hx]
      simpa [Op_p'p, q, M] using hxmem
    · apply Subtype.ext
      simpa [f] using hx
  have hmapf_eq :
      (Subgroup.map f (T : Subgroup (Op_p'p p G))).map (pCore p (G ⧸ M)).subtype = Tbar := by
    ext z
    constructor
    · intro hz
      rcases Subgroup.mem_map.mp hz with ⟨x, hx, hxz⟩
      rcases Subgroup.mem_map.mp hx with ⟨t, ht, htx⟩
      refine Subgroup.mem_map.mpr ?_
      refine ⟨(t : Op_p'p p G), ?_, ?_⟩
      · exact Subgroup.mem_map.mpr ⟨t, ht, rfl⟩
      · rw [← hxz]
        exact congrArg Subtype.val htx
    · intro hz
      rcases Subgroup.mem_map.mp hz with ⟨x, hx, hxz⟩
      rcases Subgroup.mem_map.mp hx with ⟨t, ht, htx⟩
      refine Subgroup.mem_map.mpr ?_
      refine ⟨f t, ?_, ?_⟩
      · exact Subgroup.mem_map.mpr ⟨t, ht, rfl⟩
      · rw [← hxz]
        simpa [f] using congrArg q htx
  have hT_not_dvd : ¬ p ∣ (T : Subgroup (Op_p'p p G)).index := T.not_dvd_index
  have hidx_dvd :
      (Subgroup.map f (T : Subgroup (Op_p'p p G))).index ∣
        (T : Subgroup (Op_p'p p G)).index :=
    Subgroup.index_map_dvd (H := (T : Subgroup (Op_p'p p G))) (f := f) hf_surj
  have hmapf_not_dvd : ¬ p ∣ (Subgroup.map f (T : Subgroup (Op_p'p p G))).index := by
    intro hp_dvd
    exact hT_not_dvd (hp_dvd.trans hidx_dvd)
  have hpcore_p : IsPGroup p (pCore p (G ⧸ M)) := pCore_isPGroup (p := p) (G := (G ⧸ M))
  have hpow_idx :
      ∃ n, (Subgroup.map f (T : Subgroup (Op_p'p p G))).index = p ^ n := by
    exact IsPGroup.index (hG := hpcore_p) (H := Subgroup.map f (T : Subgroup (Op_p'p p G)))
  rcases hpow_idx with ⟨n, hn⟩
  have hnzero : n = 0 := by
    cases n with
    | zero => rfl
    | succ n =>
        exfalso
        apply hmapf_not_dvd
        refine ⟨p ^ n, ?_⟩
        rw [hn]
        simp [Nat.pow_succ, Nat.mul_comm]
  have hidx_one : (Subgroup.map f (T : Subgroup (Op_p'p p G))).index = 1 := by
    rw [hn, hnzero]
    simp
  have hmapf_top : Subgroup.map f (T : Subgroup (Op_p'p p G)) = ⊤ :=
    (Subgroup.index_eq_one).1 hidx_one
  have hTbar_eq_pcore : Tbar = pCore p (G ⧸ M) := by
    have htop_map :
        (⊤ : Subgroup (pCore p (G ⧸ M))).map (pCore p (G ⧸ M)).subtype = pCore p (G ⧸ M) := by
      let K : Subgroup (G ⧸ M) := pCore p (G ⧸ M)
      have hsubtop : K.subgroupOf K = ⊤ := (Subgroup.subgroupOf_eq_top).2 le_rfl
      calc
        (⊤ : Subgroup K).map K.subtype = (K.subgroupOf K).map K.subtype := by rw [hsubtop]
        _ = K ⊓ K := Subgroup.subgroupOf_map_subtype (H := K) (K := K)
        _ = K := inf_eq_right.mpr le_rfl
    have hEq :
        Tbar = (⊤ : Subgroup (pCore p (G ⧸ M))).map (pCore p (G ⧸ M)).subtype := by
      calc
        Tbar = (Subgroup.map f (T : Subgroup (Op_p'p p G))).map (pCore p (G ⧸ M)).subtype := by
          exact hmapf_eq.symm
        _ = (⊤ : Subgroup (pCore p (G ⧸ M))).map (pCore p (G ⧸ M)).subtype := by
          rw [hmapf_top]
    exact hEq.trans htop_map
  have hM_le_comap_opmap : M ≤ Subgroup.comap q ((Op_p'p p G).map q) := by
    intro x hx
    change q x ∈ (Op_p'p p G).map q
    have hx1 : q x = 1 := by
      simpa [q, M] using hx
    rw [hx1]
    simp
  have hTG_sup : M ⊔ TG = Op_p'p p G := by
    calc
      M ⊔ TG = Subgroup.comap q (TG.map q) := by
        simp [q]
      _ = Subgroup.comap q Tbar := rfl
      _ = Subgroup.comap q (pCore p (G ⧸ M)) := by rw [hTbar_eq_pcore]
      _ = Subgroup.comap q ((Op_p'p p G).map q) := by rw [hmap_op]
      _ = Op_p'p p G := by
        rw [QuotientGroup.comap_map_mk' M (Op_p'p p G)]
        exact sup_eq_right.mpr <| by
          dsimp [M, Op_p'p]
          exact QuotientGroup.le_comap_mk' (pPrimeCore p G) (pCore p (G ⧸ pPrimeCore p G))
  have hcent_TG : Subgroup.centralizer (TG : Set G) ≤ Op_p'p p G :=
    hconstrained (Q := TG) hTG_p hTG_sup
  have hcent_Tbar :
      Subgroup.centralizer (Tbar : Set (G ⧸ M)) ≤ pCore p (G ⧸ M) := by
    let : Fact (IsPGroup p (↥TG)) := ⟨hTG_p⟩
    have hcent_map :
        Subgroup.centralizer ((TG.map q : Subgroup (G ⧸ M)) : Set (G ⧸ M)) =
          (Subgroup.centralizer (TG : Set G)).map q := by
      have h := centralizer_map_quotient_eq_map_centralizer (G := G) (p := p)
        (T := TG) (M := M) hMnormal hMcop
      change
        Subgroup.centralizer ((fun a : G => q a) '' (TG : Set G)) =
          (Subgroup.centralizer (TG : Set G)).map q at h
      simpa using h
    have hcent_map' :
        Subgroup.centralizer (Tbar : Set (G ⧸ M)) =
          (Subgroup.centralizer (TG : Set G)).map q := by
      simpa [Tbar] using hcent_map
    rw [hcent_map']
    exact (Subgroup.map_mono hcent_TG).trans hmap_op.le
  have hquot_core_bot : pPrimeCore p (G ⧸ M) = ⊥ := by
    simpa [M] using (pPrimeCore_quotient_pPrimeCore_eq_bot (G := G) (p := p))
  have hOp_eq_pCore_quot : Op_p'p p (G ⧸ M) = pCore p (G ⧸ M) := by
    simpa [hquot_core_bot] using
      (Op_p'p_eq_pCore_of_pPrimeCore_eq_bot (G := G ⧸ M) (p := p) hquot_core_bot)
  intro Q hQ hQeq
  have hQ_eq_pcore : Q = pCore p (G ⧸ M) := by
    rw [hquot_core_bot, hOp_eq_pCore_quot, bot_sup_eq] at hQeq
    exact hQeq
  rw [hQ_eq_pcore]
  have hcent_pcore : Subgroup.centralizer (pCore p (G ⧸ M) : Set (G ⧸ M)) ≤ pCore p (G ⧸ M) := by
    simpa [hTbar_eq_pcore] using hcent_Tbar
  exact hcent_pcore.trans <| by
    rw [← hOp_eq_pCore_quot]

end ConstraintAndStability

end

section Main

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

omit [Finite G] [Fact p.Prime] in
private theorem rzj_normalizerPCoreModCentralizer_le_pCore {B : Subgroup G} [B.Normal]
    (hC : IsPGroup p (centralizer (B : Set G))) :
    normalizerPCoreModCentralizer p B ≤ pCore p G := by
  set N : Subgroup G := normalizer (B : Set G) with hN
  set C : Subgroup N := (centralizer (B : Set G)).subgroupOf N with hC'
  have hNtop : N = ⊤ := Subgroup.normalizer_eq_top (H := B)
  have hmem : ∀ x : G, x ∈ normalizerPCoreModCentralizer p B ↔
      ∃ hx : x ∈ N, QuotientGroup.mk' C ⟨x, hx⟩ ∈ pCore p (N ⧸ C) := by
    intro x
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact ⟨n.2, hn⟩
    · rintro ⟨hx, h⟩
      exact ⟨⟨x, hx⟩, h, rfl⟩
  apply le_sSup
  refine ⟨⟨fun x hx g => ?_⟩, ?_⟩
  · obtain ⟨hxN, hxp⟩ := (hmem x).1 hx
    have hgN : g ∈ N := by
      rw [hNtop]
      exact Subgroup.mem_top g
    refine (hmem _).2 ⟨N.mul_mem (N.mul_mem hgN hxN) (N.inv_mem hgN), ?_⟩
    have heq : (⟨g * x * g⁻¹, N.mul_mem (N.mul_mem hgN hxN) (N.inv_mem hgN)⟩ : N) =
        ⟨g, hgN⟩ * ⟨x, hxN⟩ * (⟨g, hgN⟩ : N)⁻¹ := rfl
    rw [heq, map_mul, map_mul, map_inv]
    exact (pCore_normal (p := p) (G := N ⧸ C)).conj_mem _ hxp _
  · rintro ⟨x, hx⟩
    obtain ⟨hxN, hxp⟩ := (hmem x).1 hx
    obtain ⟨k, hk⟩ := (pCore_isPGroup (p := p) (G := N ⧸ C)) ⟨_, hxp⟩
    have h1 : QuotientGroup.mk' C ((⟨x, hxN⟩ : N) ^ p ^ k) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val hk
    have h2 : x ^ p ^ k ∈ centralizer (B : Set G) := by
      have h2' := (QuotientGroup.eq_one_iff ((⟨x, hxN⟩ : N) ^ p ^ k)).mp h1
      rw [hC', Subgroup.mem_subgroupOf] at h2'
      simpa using h2'
    obtain ⟨m, hm⟩ := hC ⟨_, h2⟩
    refine ⟨k + m, Subtype.ext ?_⟩
    have hm' : (x ^ p ^ k) ^ p ^ m = 1 := congrArg Subtype.val hm
    simpa [pow_add, pow_mul] using hm'

theorem relative_zj_normal (hp : p ≠ 2) (U : Subgroup G) (hU : IsPGroup p U)
    (hCB : centralizer (pCore p G : Set G) ≤ pCore p G) (hBU : pCore p G ≤ U)
    (hstable : ∀ B' A : Subgroup G, B'.Normal → IsPGroup p B' → B' ≠ ⊥ → A ≤ U →
      ⁅⁅B', A⁆, A⁆ = ⊥ → A ≤ normalizerPCoreModCentralizer p B')
    (Ostar : Subgroup G) (hOn : Ostar.Normal)
    (hOZ : Ostar ≤ normalizer (thompsonCenter U : Set G))
    (hFr : ∀ (L : Subgroup G) [L.Normal], Ostar ≤ L →
      (IsSylowOf p (U ⊓ L) L ∧ pCore p (G ⧸ L) ≤ U.map (QuotientGroup.mk' L)) ∨
        L ⊔ normalizer (thompsonCenter U : Set G) = ⊤) :
    (thompsonCenter U).Normal := by
  set B : Subgroup G := pCore p G with hBdef
  set Z : Subgroup G := thompsonCenter U with hZdef
  by_cases hB1 : B = ⊥
  · have hall : ∀ g : G, g = 1 := by
      intro g
      have hg : g ∈ centralizer (B : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [hB1, SetLike.mem_coe, Subgroup.mem_bot] at hh
        simp [hh]
      have := hCB hg
      rwa [hB1, Subgroup.mem_bot] at this
    refine ⟨fun z _ g => ?_⟩
    rw [hall g, hall z]
    simp
  have hZU : Z ≤ U := rzj_thompsonCenter_le U
  have hUZ : U ≤ normalizer (Z : Set G) :=
    Subgroup.le_normalizer.trans (rzj_normalizer_le_normalizer_thompsonCenter U)
  have hZcomm : IsMulCommutative Z := rzj_thompsonCenter_isMulCommutative U
  have hBZ : ⁅B, Z⁆ ≤ Z := by
    rw [Subgroup.commutator_le]
    intro b hb z hz
    have hbz : b * z * b⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp (hUZ (hBU hb)) z).mp hz
    rw [commutatorElement_def]
    exact Z.mul_mem hbz (Z.inv_mem hz)
  have hcomm2 : ⁅⁅B, Z⁆, Z⁆ = ⊥ :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).2
      (hBZ.trans ((Subgroup.le_centralizer_iff_isMulCommutative (K := Z)).2 hZcomm))
  have hZQ : Z ≤ normalizerPCoreModCentralizer p B :=
    hstable B Z (pCore_normal (p := p) (G := G)) (pCore_isPGroup (p := p) (G := G)) hB1 hZU
      hcomm2
  have hCp : IsPGroup p (centralizer (B : Set G)) :=
    (pCore_isPGroup (p := p) (G := G)).to_le hCB
  have hZB : Z ≤ B := hZQ.trans (rzj_normalizerPCoreModCentralizer_le_pCore hCp)
  have h := inf_thompsonCenter_normal hp U hU hBU hstable Ostar hOn hOZ hFr B
    (pCore_isPGroup (p := p) (G := G)) hB1
  rwa [inf_eq_right.mpr hZB] at h

private theorem rzj_le_normalizer_of_sup_normal {P : Subgroup G} (S : Sylow p G)
    (hPS : P ≤ S) (hn : (pPrimeCore p G ⊔ P).Normal) :
    (S : Subgroup G) ≤ normalizer (P : Set G) := by
  have hPp : IsPGroup p P := S.isPGroup'.to_le hPS
  have hsyl : IsSylowOf p P (pPrimeCore p G ⊔ P) :=
    isSylowOf_sup_of_coprime pPrimeCore_coprime_card hPp
  have heq : (S : Subgroup G) ⊓ (pPrimeCore p G ⊔ P) = P :=
    hsyl.eq_of_le (le_inf hPS le_sup_right) inf_le_right (S.isPGroup'.to_le inf_le_left)
  intro s hs
  rw [← heq]
  exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hs,
    by rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top s⟩

private theorem rzj_relativeStable_quotient (U : Subgroup G) (hU : IsPGroup p U)
    (hst : ∀ P A : Subgroup G, P ≠ ⊥ → P ≤ U → (pPrimeCore p G ⊔ P).Normal → A ≤ U →
      ⁅⁅P, A⁆, A⁆ = ⊥ → A ≤ normalizerPCoreModCentralizer p P)
    (Q A : Subgroup (G ⧸ pPrimeCore p G)) [hQ_normal : Q.Normal] (hQne : Q ≠ ⊥)
    (hQU : Q ≤ U.map (QuotientGroup.mk' (pPrimeCore p G)))
    (hAU : A ≤ U.map (QuotientGroup.mk' (pPrimeCore p G))) (hcomm2 : ⁅⁅Q, A⁆, A⁆ = ⊥) :
    A ≤ normalizerPCoreModCentralizer p Q := by
  classical
  let M : Subgroup G := pPrimeCore p G
  let q : G →* G ⧸ M := QuotientGroup.mk' M
  have hM_normal : M.Normal := by
    dsimp [M]
    infer_instance
  let : M.Normal := hM_normal
  let N : Subgroup (G ⧸ M) := Subgroup.normalizer (Q : Set (G ⧸ M))
  let C : Subgroup (G ⧸ M) := Subgroup.centralizer (Q : Set (G ⧸ M))
  let : (C.subgroupOf N).Normal := by
    have hCN : C ≤ N := by
      simpa [C, N] using (centralizer_le_normalizer (G := G ⧸ M) Q)
    exact
      (Subgroup.normal_subgroupOf_iff_le_normalizer
        (H := C) (K := N) hCN).2
        (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer (X := G ⧸ M) Q)
  let Q1 : Subgroup G := U ⊓ Subgroup.comap q Q
  let A0 : Subgroup G := U ⊓ Subgroup.comap q A
  have hQ1p : IsPGroup p Q1 := hU.to_le inf_le_left
  have hQ1_map_q : Q1.map q = Q := by
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact hy.2
    · intro x hx
      obtain ⟨u, huU, rfl⟩ := Subgroup.mem_map.mp (hQU hx)
      exact Subgroup.mem_map_of_mem q ⟨huU, hx⟩
  have hA0_map_q : A0.map q = A := by
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact hy.2
    · intro x hx
      obtain ⟨u, huU, rfl⟩ := Subgroup.mem_map.mp (hAU hx)
      exact Subgroup.mem_map_of_mem q ⟨huU, hx⟩
  have hA0_le_normalizer_Q1 : A0 ≤ Subgroup.normalizer (Q1 : Set G) := by
    intro a ha
    have haU : a ∈ Subgroup.normalizer (U : Set G) := Subgroup.le_normalizer ha.1
    have haQ : a ∈ Subgroup.normalizer ((Subgroup.comap q Q : Subgroup G) : Set G) := by
      have : (Subgroup.comap q Q).Normal := hQ_normal.comap q
      rw [Subgroup.normalizer_eq_top (H := Subgroup.comap q Q)]
      exact Subgroup.mem_top a
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨haU, haQ⟩

  have hcomm_Q1A0_le_Q1 : ⁅Q1, A0⁆ ≤ Q1 := by
    refine Subgroup.commutator_le.mpr ?_
    intro g₁ hg₁ g₂ hg₂
    have hg₂_norm : g₂ ∈ Subgroup.normalizer (Q1 : Set G) := hA0_le_normalizer_Q1 hg₂
    have hg₂_conj : g₂ * g₁⁻¹ * g₂⁻¹ ∈ Q1 := by
      exact ((Subgroup.mem_normalizer_iff.mp hg₂_norm) g₁⁻¹).1 (Q1.inv_mem hg₁)
    rw [commutatorElement_def]
    simpa [mul_assoc] using Q1.mul_mem hg₁ hg₂_conj
  have hcomm2_lift : ⁅⁅Q1, A0⁆, A0⁆ = ⊥ := by
    let H : Subgroup G := ⁅⁅Q1, A0⁆, A0⁆
    have hH_le_Q1 : H ≤ Q1 := by
      refine Subgroup.commutator_le.mpr ?_
      intro g₁ hg₁ g₂ hg₂
      have hg₁Q1 : g₁ ∈ Q1 := hcomm_Q1A0_le_Q1 hg₁
      have hg₂_norm : g₂ ∈ Subgroup.normalizer (Q1 : Set G) := hA0_le_normalizer_Q1 hg₂
      have hg₂_conj : g₂ * g₁⁻¹ * g₂⁻¹ ∈ Q1 := by
        exact ((Subgroup.mem_normalizer_iff.mp hg₂_norm) g₁⁻¹).1 (Q1.inv_mem hg₁Q1)
      rw [commutatorElement_def]
      simpa [mul_assoc] using Q1.mul_mem hg₁Q1 hg₂_conj
    have hH_inj :
        Function.Injective ((q.comp H.subtype)) := by
      exact rzj_quotient_pPrimeCore_subgroupMap_injective (G := G) (p := p) (H := H)
        (hQ1p.to_le hH_le_Q1)
    have hH_map_bot : H.map q = ⊥ := by
      calc
        H.map q = (⁅⁅Q1, A0⁆, A0⁆).map q := rfl
        _ = ⁅⁅Q1.map q, A0.map q⁆, A0.map q⁆ := by
          rw [Subgroup.map_commutator, Subgroup.map_commutator]
        _ = ⁅⁅Q, A⁆, A⁆ := by rw [hQ1_map_q, hA0_map_q]
        _ = ⊥ := hcomm2
    refine le_antisymm ?_ bot_le
    intro x hx
    have hx1 : q x = 1 := by
      have hxmap : q x ∈ H.map q := Subgroup.mem_map_of_mem q hx
      rw [hH_map_bot] at hxmap
      simpa using hxmap
    have hx_sub_eq : (⟨x, hx⟩ : H) = 1 := by
      apply hH_inj
      simp [hx1]
    simpa using congrArg Subtype.val hx_sub_eq
  let N1 : Subgroup G := Subgroup.normalizer (Q1 : Set G)
  let C1 : Subgroup G := Subgroup.centralizer (Q1 : Set G)
  let : (C1.subgroupOf N1).Normal := by
    have hC1N1 : C1 ≤ N1 := by
      simpa [C1, N1] using (centralizer_le_normalizer (G := G) Q1)
    exact
      (Subgroup.normal_subgroupOf_iff_le_normalizer
        (H := C1) (K := N1) hC1N1).2
        (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer (X := G) Q1)
  have hQ1ne : Q1 ≠ ⊥ := by
    intro h
    apply hQne
    rw [← hQ1_map_q, h, Subgroup.map_bot]
  have hMQ1_normal : (M ⊔ Q1).Normal := by
    have heq : M ⊔ Q1 = Subgroup.comap q Q := by
      calc M ⊔ Q1 = Subgroup.comap q (Q1.map q) := (QuotientGroup.comap_map_mk' M Q1).symm
        _ = Subgroup.comap q Q := by rw [hQ1_map_q]
    rw [heq]
    exact hQ_normal.comap q
  have hA0 := hst Q1 A0 hQ1ne inf_le_left hMQ1_normal inf_le_left hcomm2_lift
  have hstable_up :
      ((A0.subgroupOf N1).map (QuotientGroup.mk' (C1.subgroupOf N1))) ≤
        pCore p (N1 ⧸ C1.subgroupOf N1) := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨n, hn', hna⟩ := hA0 ha
    have hna' : n = a := Subtype.ext hna
    rw [← hna']
    exact hn'

  have hMcop : Nat.Coprime p (Nat.card M) := by
    simpa [M] using (pPrimeCore_coprime_card (G := G) (p := p))
  have hNmap : N1.map q = N := by
    let : Fact (IsPGroup p (↑Q1)) := ⟨hQ1p⟩
    have himage :
        ((fun a : G => q a) '' (Q1 : Set G)) = ((Q1.map q : Subgroup (G ⧸ M)) : Set (G ⧸ M)) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact Subgroup.mem_map_of_mem q hy
      · intro hx
        rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
        exact ⟨y, hy, rfl⟩
    have htmp :=
      normalizer_map_quotient_eq_map_normalizer
        (G := G) (p := p) Q1 M hM_normal hMcop
    change
      Subgroup.normalizer ((fun a : G => q a) '' (Q1 : Set G)) = N1.map q at htmp
    have htmp' :
        Subgroup.normalizer ((Q1.map q : Subgroup (G ⧸ M)) : Set (G ⧸ M)) = N1.map q := by
      rw [← himage]
      exact htmp
    simpa [N, hQ1_map_q] using htmp'.symm
  have hCmap : C1.map q = C := by
    let : Fact (IsPGroup p (↑Q1)) := ⟨hQ1p⟩
    have himage :
        ((fun a : G => q a) '' (Q1 : Set G)) = ((Q1.map q : Subgroup (G ⧸ M)) : Set (G ⧸ M)) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact Subgroup.mem_map_of_mem q hy
      · intro hx
        rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
        exact ⟨y, hy, rfl⟩
    have htmp :=
      centralizer_map_quotient_eq_map_centralizer
        (G := G) (p := p) (T := Q1) (M := M) hM_normal hMcop
    change
      Subgroup.centralizer ((fun a : G => q a) '' (Q1 : Set G)) = C1.map q at htmp
    have htmp' :
        Subgroup.centralizer ((Q1.map q : Subgroup (G ⧸ M)) : Set (G ⧸ M)) = C1.map q := by
      rw [← himage]
      exact htmp
    simpa [C, hQ1_map_q] using htmp'.symm
  let qN1 : N1 →* N :=
    (q.comp N1.subtype).codRestrict N (by
      intro x
      have hxmap : q x ∈ N1.map q := Subgroup.mem_map_of_mem q x.2
      rwa [hNmap] at hxmap)
  have hqN1_surj : Function.Surjective qN1 := by
    intro y
    have hy : (y : G ⧸ M) ∈ N1.map q := by
      simp [hNmap]
    rcases Subgroup.mem_map.mp hy with ⟨x, hx, hxy⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    change q x = (y : G ⧸ M)
    exact hxy
  have hC1_le_comap_qN1 : C1.subgroupOf N1 ≤ (C.subgroupOf N).comap qN1 := by
    intro x hx
    change q ((x : N1) : G) ∈ C
    have hxmap : q ((x : N1) : G) ∈ C1.map q := by
      exact Subgroup.mem_map.mpr ⟨((x : N1) : G), hx, rfl⟩
    rwa [hCmap] at hxmap
  let φ : N1 ⧸ C1.subgroupOf N1 →* N ⧸ C.subgroupOf N :=
    QuotientGroup.map (N := C1.subgroupOf N1) (M := C.subgroupOf N) qN1 hC1_le_comap_qN1
  let SA : Subgroup (N1 ⧸ C1.subgroupOf N1) :=
    (A0.subgroupOf N1).map (QuotientGroup.mk' (C1.subgroupOf N1))
  let TA : Subgroup (N ⧸ C.subgroupOf N) :=
    (A.subgroupOf N).map (QuotientGroup.mk' (C.subgroupOf N))
  have hφ_surj : Function.Surjective φ := by
    intro y
    refine Quotient.inductionOn' y ?_
    intro z
    rcases hqN1_surj z with ⟨x, rfl⟩
    refine ⟨QuotientGroup.mk' (C1.subgroupOf N1) x, ?_⟩
    simp [φ]
  have hSA_map_le : SA.map φ ≤ TA := by
    intro z hz
    rcases Subgroup.mem_map.mp hz with ⟨x, hx, rfl⟩
    rcases Subgroup.mem_map.mp hx with ⟨a, ha, rfl⟩
    have haA : q ((a : N1) : G) ∈ A := by
      rw [← hA0_map_q]
      exact Subgroup.mem_map_of_mem q ha
    let aq : A.subgroupOf N := ⟨qN1 a, haA⟩
    refine Subgroup.mem_map.mpr ?_
    refine ⟨qN1 a, aq.2, ?_⟩
    change φ (QuotientGroup.mk' (C1.subgroupOf N1) a) =
      QuotientGroup.mk' (C.subgroupOf N) (qN1 a)
    simp [φ]
  have hTA_le : TA ≤ SA.map φ := by
    intro z hz
    rcases Subgroup.mem_map.mp hz with ⟨a, ha, rfl⟩
    have haA0map : (a : G ⧸ M) ∈ A0.map q := by
      change (a : G ⧸ M) ∈ A at ha
      rwa [← hA0_map_q] at ha
    rcases Subgroup.mem_map.mp haA0map with ⟨x, hxA0, hxa⟩
    let xN1 : N1 := ⟨x, hA0_le_normalizer_Q1 hxA0⟩
    have hxSA : QuotientGroup.mk' (C1.subgroupOf N1) xN1 ∈ SA := by
      exact Subgroup.mem_map_of_mem (QuotientGroup.mk' (C1.subgroupOf N1)) hxA0
    refine Subgroup.mem_map.mpr ⟨QuotientGroup.mk' (C1.subgroupOf N1) xN1, hxSA, ?_⟩
    have hxq : qN1 xN1 = (a : N) := by
      apply Subtype.ext
      change q x = (a : G ⧸ M)
      exact hxa
    rw [show φ (QuotientGroup.mk' (C1.subgroupOf N1) xN1) =
        QuotientGroup.mk' (C.subgroupOf N) (qN1 xN1) by
          simp [φ]]
    rw [hxq]
  have hSA_map : SA.map φ = TA := le_antisymm hSA_map_le hTA_le
  have hTA : TA ≤ pCore p (N ⧸ C.subgroupOf N) :=
    calc
      TA = SA.map φ := hSA_map.symm
      _ ≤ (pCore p (N1 ⧸ C1.subgroupOf N1)).map φ := by
            exact Subgroup.map_mono hstable_up
      _ ≤ pCore p (N ⧸ C.subgroupOf N) := by
            exact
              rzj_pCore_map_le_pCore_of_surjective (G := N1 ⧸ C1.subgroupOf N1)
                (p := p) φ hφ_surj
  intro a ha
  have haN : a ∈ N := by
    change a ∈ Subgroup.normalizer (Q : Set (G ⧸ M))
    rw [Subgroup.normalizer_eq_top (H := Q)]
    exact Subgroup.mem_top a
  exact ⟨⟨a, haN⟩, hTA (Subgroup.mem_map_of_mem _ (show (⟨a, haN⟩ : N) ∈ A.subgroupOf N from ha)),
    rfl⟩


theorem centralizer_pCore_quotient_le (hcon : IsPConstrained p G) :
    centralizer (pCore p (G ⧸ pPrimeCore p G) : Set (G ⧸ pPrimeCore p G)) ≤
      pCore p (G ⧸ pPrimeCore p G) := by
  have hcon' : PConstrainedGroup (G := G ⧸ pPrimeCore p G) p :=
    rzj_pConstrained_quotient_pPrimeCore (G := G) (p := p)
      (isPConstrained_iff_pConstrainedGroup.mp hcon)
  have hbot : pPrimeCore p (G ⧸ pPrimeCore p G) = ⊥ :=
    pPrimeCore_quotient_pPrimeCore_eq_bot (G := G) (p := p)
  have hOp : Op_p'p p (G ⧸ pPrimeCore p G) = pCore p (G ⧸ pPrimeCore p G) :=
    Op_p'p_eq_pCore_of_pPrimeCore_eq_bot (G := G ⧸ pPrimeCore p G) (p := p) hbot
  have h := hcon' (pCore p (G ⧸ pPrimeCore p G)) (pCore_isPGroup (p := p) (G := _))
    (by rw [hbot, bot_sup_eq, hOp])
  rwa [hOp] at h

theorem pCore_quotient_le_map {U : Subgroup G} (hU : IsPGroup p U)
    (hsyl : IsSylowOf p (U ⊓ Op_p'p p G) (Op_p'p p G)) :
    pCore p (G ⧸ pPrimeCore p G) ≤ U.map (QuotientGroup.mk' (pPrimeCore p G)) := by
  have hsup : pPrimeCore p G ⊔ (U ⊓ Op_p'p p G) = Op_p'p p G :=
    (sup_eq_Op_p'p_iff_isSylowOf (hU.to_le inf_le_left)).mpr hsyl
  have hmap : (Op_p'p p G).map (QuotientGroup.mk' (pPrimeCore p G)) =
      pCore p (G ⧸ pPrimeCore p G) :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
  rw [← hmap, ← hsup, Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
  exact Subgroup.map_mono inf_le_left

theorem relativeStable_of_isPStable {U : Subgroup G} (hU : IsPGroup p U) (hst : IsPStable p G) :
    ∀ P A : Subgroup G, P ≠ ⊥ → P ≤ U → (pPrimeCore p G ⊔ P).Normal → A ≤ U →
      ⁅⁅P, A⁆, A⁆ = ⊥ → A ≤ normalizerPCoreModCentralizer p P := by
  intro P A hP1 hPU hn hAU hcomm
  obtain ⟨S, hS⟩ := hU.exists_le_sylow
  exact hst.2 P A hP1 (hU.to_le hPU) hn (hU.to_le hAU)
    (hAU.trans (hS.trans (rzj_le_normalizer_of_sup_normal S (hPU.trans hS) hn))) hcomm

theorem relative_zj_factorization_of_normal (U : Subgroup G) (hU : IsPGroup p U)
    (hN : (thompsonCenter (U.map (QuotientGroup.mk' (pPrimeCore p G)))).Normal) :
    pPrimeCore p G ⊔ normalizer (thompsonCenter U : Set G) = ⊤ := by
  classical
  let M : Subgroup G := pPrimeCore p G
  let q : G →* G ⧸ M := QuotientGroup.mk' M
  let Z : Subgroup G := thompsonCenter U
  let Zbar : Subgroup (G ⧸ M) := thompsonCenter (U.map q)
  have hZ_map : Z.map q = Zbar := by
    have hqinj : Function.Injective (q.comp U.subtype) :=
      rzj_quotient_pPrimeCore_subgroupMap_injective (G := G) (p := p) U hU
    let f : U →* (U.map q) :=
      (q.comp U.subtype).codRestrict (U.map q) (by
        intro x
        exact Subgroup.mem_map_of_mem q x.2)
    let e : U ≃* (U.map q) := by
      refine MulEquiv.ofBijective f ⟨?_, ?_⟩
      · intro a b hab
        exact hqinj <| by exact congrArg Subtype.val hab
      intro x
      rcases Subgroup.mem_map.mp x.2 with ⟨y, hy, hxy⟩
      refine ⟨⟨y, hy⟩, ?_⟩
      apply Subtype.ext
      exact hxy
    have hcomp : ((Subgroup.subtype (U.map q)).comp e.toMonoidHom) = q.comp U.subtype := rfl
    calc
      Z.map q = ((thompsonCenter (G := U) (⊤ : Subgroup U)).map U.subtype).map q := by
        rw [rzj_thompsonCenter_top_map_subtype]
      _ = (thompsonCenter (G := U) (⊤ : Subgroup U)).map (q.comp U.subtype) := by
        rw [Subgroup.map_map]
      _ = ((thompsonCenter (G := U) (⊤ : Subgroup U)).map e.toMonoidHom).map
            (Subgroup.subtype (U.map q)) := by
        rw [Subgroup.map_map, hcomp]
      _ = (thompsonCenter (G := U.map q) (⊤ : Subgroup (U.map q))).map
            (Subgroup.subtype (U.map q)) := by
        rw [rzj_thompsonCenter_top_map_mulEquiv]
      _ = Zbar := rzj_thompsonCenter_top_map_subtype (G := G ⧸ M) (U.map q)
  have hsup_map : (Z ⊔ M).map q = Zbar := by
    calc
      (Z ⊔ M).map q = Z.map q ⊔ M.map q := Subgroup.map_sup _ _ _
      _ = Zbar ⊔ ⊥ := by rw [hZ_map, QuotientGroup.map_mk'_self]
      _ = Zbar := by simp
  have hcomap_eq : Subgroup.comap q Zbar = Z ⊔ M := by
    calc
      Subgroup.comap q Zbar = Subgroup.comap q ((Z ⊔ M).map q) := by rw [hsup_map]
      _ = M ⊔ (Z ⊔ M) := by simp [q]
      _ = Z ⊔ M := by simp [sup_comm]
  have hZM : (M ⊔ Z).Normal := by
    have : (Subgroup.comap q Zbar).Normal := hN.comap q
    rw [hcomap_eq, sup_comm] at this
    exact this
  have hZp : IsPGroup p Z := hU.to_le (rzj_thompsonCenter_le U)
  have hsyl : IsSylowOf p Z (M ⊔ Z) := isSylowOf_sup_of_coprime pPrimeCore_coprime_card hZp
  obtain ⟨T, hT⟩ := hsyl
  have hfr := Sylow.normalizer_sup_eq_top (N := M ⊔ Z) T
  rw [hT] at hfr
  apply top_le_iff.mp
  rw [← hfr]
  exact sup_le le_sup_right (sup_le le_sup_left (le_sup_of_le_right Subgroup.le_normalizer))

theorem relative_zj_factorization (hp : p ≠ 2) (U : Subgroup G) (hU : IsPGroup p U)
    (hcon : IsPConstrained p G) (hsyl : IsSylowOf p (U ⊓ Op_p'p p G) (Op_p'p p G))
    (hst : ∀ P A : Subgroup G, P ≠ ⊥ → P ≤ U → (pPrimeCore p G ⊔ P).Normal → A ≤ U →
      ⁅⁅P, A⁆, A⁆ = ⊥ → A ≤ normalizerPCoreModCentralizer p P)
    (Ostar : Subgroup (G ⧸ pPrimeCore p G)) (hOn : Ostar.Normal)
    (hOZ : Ostar ≤ normalizer (thompsonCenter (U.map (QuotientGroup.mk' (pPrimeCore p G))) :
      Set (G ⧸ pPrimeCore p G)))
    (hFr : ∀ (L : Subgroup (G ⧸ pPrimeCore p G)) [L.Normal], Ostar ≤ L →
      (IsSylowOf p (U.map (QuotientGroup.mk' (pPrimeCore p G)) ⊓ L) L ∧
          pCore p ((G ⧸ pPrimeCore p G) ⧸ L) ≤
            (U.map (QuotientGroup.mk' (pPrimeCore p G))).map (QuotientGroup.mk' L)) ∨
        L ⊔ normalizer (thompsonCenter (U.map (QuotientGroup.mk' (pPrimeCore p G))) :
          Set (G ⧸ pPrimeCore p G)) = ⊤) :
    pPrimeCore p G ⊔ normalizer (thompsonCenter U : Set G) = ⊤ := by
  have hBU := pCore_quotient_le_map hU hsyl
  refine relative_zj_factorization_of_normal U hU ?_
  refine relative_zj_normal hp _ (hU.map _) (centralizer_pCore_quotient_le hcon) hBU ?_
    Ostar hOn hOZ hFr
  intro B' A hB' hB'p hB'ne hAU hcomm
  have hB'le : B' ≤ pCore p (G ⧸ pPrimeCore p G) := le_sSup ⟨hB', hB'p⟩
  exact rzj_relativeStable_quotient U hU hst B' A hB'ne (hB'le.trans hBU) hAU hcomm

end Main

end CFSG.ABGTheoremB.RelativeZJ
