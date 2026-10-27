module

public import CFSG.Quasithin.H13.A7Nat1238QTab
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Background.A3Structure314Cases
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A7Nat1238Ke
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A7Nat1238Q

public section

namespace CFSG.Quasithin.H13.A7

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Subgroup

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G}
  {ψ : V ≃* Multiplicative (evenWeight 7)}

theorem insp1238QTab_core_F4
    (hF : A314Facts_F4) (h312 : Vol2Native.A312ForSQTKCat) (h1222 : Stmt12_2_2_F4)
    (h1225 : Stmt12_2_5_F4) (hyp : Hyp1223 G T L V) (h : A7NatPre T L V ψ) {e : V}
    (he : vec ψ e = vecFS) (hS : Setting1238 hyp ψ e) {K K₀ : Subgroup G}
    (hK : K ∈ cComp (hyp.Gv e)) (hKeK : Kv hyp e < K) (hKK₀ : K ≤ K₀)
    (hK₀max : quasithinIsMaximalLocal T K₀) (hK₀f : quasithinIsFaithfulLocal T K₀)
    (hq : CFSG.IsQuasisimple (↥K₀ ⧸ CFSG.pCore 2 ↥K₀)) :
    K = K₀ ∧ Nonempty ((↥K₀ ⧸ CFSG.pCore 2 ↥K₀) ⧸ center (↥K₀ ⧸ CFSG.pCore 2 ↥K₀) ≃*
      alternatingGroup (Fin 7)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hyp.simple
  set Ke := Kv hyp e with hKedef

  have he2 := orderOf_eq_two_of_vecFS he
  have he1 : (e : G) ≠ 1 := fun h1 => by simp [h1] at he2
  have hZC : quasithinOmegaOneCenter T ≤ centralizer (T : Set G) :=
    (Subgroup.closure_le _).2 fun x hx => (mem_inf.1 hx.1).2
  have hTe : T ≤ hyp.Gv e := fun t ht =>
    mem_centralizer_singleton_iff.2 ((mem_centralizer_iff.1 (hZC hS.mem) t ht))
  have hTKe : T ≤ normalizer (Ke : Set G) := T_le_normalizer_Kv_F4 hyp h1225 e.2 he1 hS.mem
  have hKeF : Ke ∈ lFamily T := Kv_mem_lFamily hyp h he hTKe
  have hKep : ⁅Ke, Ke⁆ = Ke := Kv_perfect hyp e
  have hKe1 : Ke ≠ ⊥ := ne_bot_of_mem_cComp hKeF
  have hKp : ⁅K, K⁆ = K := perfect_of_mem_cComp hK
  have hK1 : K ≠ ⊥ := ne_bot_of_mem_cComp hK

  have hLocal : QuasithinUnique.LocalSQTK G :=
    (QuasithinUnique.qtkeCore_of_cat hyp.nonabelian hyp.qtke).1
  have hH2 : pCoreOf 2 (hyp.Gv e) ≠ ⊥ :=
    pCoreOf_ne_bot_of_le_centralizer he2 (mem_centralizer_singleton_iff.2 rfl) le_rfl
  have hTK : T ≤ normalizer (K : Set G) := by
    intro t ht
    have hKt := map_conj_mem_cComp hK (hTe ht)
    have hKzt : Ke ≤ K.map (MulAut.conj t).toMonoidHom := by
      intro k hk
      have hk' : t⁻¹ * k * t ∈ Ke := by
        have := (mem_normalizer_iff.1 (hTKe (T.inv_mem ht)) k).1 hk
        simpa using this
      exact ⟨t⁻¹ * k * t, hKeK.le hk', by simp [MulAut.conj_apply, mul_assoc]⟩
    have heq := QuasithinUnique.Vol2Native.lemma_1_2_4_unique hLocal
      QuasithinUnique.Vol2Native.a37ForSQTKCat_proved hH2 hKeF hKt hK hKzt hKeK.le
    exact A38.map_conj_eq_iff.1 heq

  set H := K₀ ⊔ T with hH
  set P := CFSG.pCore 2 ↥H with hP
  have hK₀loc := hK₀max.1
  have hK₀c : K₀ ∈ cComp H := hK₀loc.2.1
  have hK₀H : K₀ ≤ H := le_sup_left
  have hKH : K ≤ H := hKK₀.trans hK₀H
  have hKeH : Ke ≤ H := hKeK.le.trans hKH
  have hSH : QuasithinUnique.IsSylowTwoOf T H := isSylowTwoOf_of_le hyp.sylow le_sup_right
  have hPT : pCoreOf 2 H ≤ T := EscapingLocal.pCoreOf_le_of_isSylowTwoOf hSH
  have hQ : Vol2Native.SQTKHypCat (↥H ⧸ P) :=
    Vol2Native.sqtkHypCat_quotient_of_pCoreOf_ne_bot hLocal hK₀loc.2.2.2
  have hTbar : QuasithinUnique.IsSylowTwoOf ((T.subgroupOf H).map (QuotientGroup.mk' P)) ⊤ :=
    isSylowTwoOf_top_map_of_surjective (isSylowTwoOf_top_subgroupOf hSH) _
      (QuotientGroup.mk'_surjective P)
  set Tb := (T.subgroupOf H).map (QuotientGroup.mk' P) with hTb
  set Lb := modO2Image H K₀ with hLb
  set Bb := modO2Image H Ke with hBb
  set Kb := modO2Image H K with hKb
  have hLc : Lb ∈ cComp (⊤ : Subgroup (↥H ⧸ P)) := modO2Image_mem_cComp hK₀c
  obtain ⟨eL⟩ := modO2_mulEquiv hK₀c
  have hLq : CFSG.IsQuasisimple ↥Lb := CFSG.LocalCores.isQuasisimple_of_mulEquiv eL hq
  have hLZ : Odd (Nat.card (center ↥Lb)) := by
    obtain ⟨-, -, hodd⟩ := SteinbergBM.five_core_quotient_center_odd hq
    rw [← Nat.card_congr (Subgroup.centerCongr eL).toEquiv]
    exact hodd
  have hBK : Bb ≤ Kb := Subgroup.map_mono fun x hx => hKeK.le hx
  have hKL : Kb ≤ Lb := Subgroup.map_mono fun x hx => hKK₀ hx

  have hBL : Bb < Lb := by
    refine lt_of_le_of_ne (hBK.trans hKL) fun heq => ?_
    have h1 := le_sup_pCoreOf_of_modO2Image_le hK₀H heq.ge
    have h2 : K₀ ≤ normalizer (Ke : Set G) := h1.trans (sup_le le_normalizer (hPT.trans hTKe))
    exact not_subnormal_of_mem_cComp hK₀c (hKeK.trans_le hKK₀) hKe1 hKep
      (IsSubnormal.step (hKeK.le.trans hKK₀)
        ((Subgroup.normal_subgroupOf_iff_le_normalizer (hKeK.le.trans hKK₀)).2 h2)
        (subnormal_of_mem_cComp hK₀c))
  have hBKs : Bb < Kb := by
    refine lt_of_le_of_ne hBK fun heq => ?_
    have h1 := le_sup_pCoreOf_of_modO2Image_le hKH heq.ge
    have h2 : K ≤ normalizer (Ke : Set G) := h1.trans (sup_le le_normalizer (hPT.trans hTKe))
    exact not_subnormal_of_mem_cComp hK hKeK hKe1 hKep
      (IsSubnormal.step hKeK.le ((Subgroup.normal_subgroupOf_iff_le_normalizer hKeK.le).2 h2)
        (subnormal_of_mem_cComp hK))

  rcases Vol2Native.lemma_1_2_4_list_of_a3 (h312 _ hQ) hSH hKeH hKeF hK₀c (hKeK.le.trans hKK₀)
    with heq | hcase | hnq
  · exact absurd heq hBL.ne
  swap
  · exact absurd hLq (A312.not_quasisimple_of_nonquasi hnq)

  set π : ↥Ke →* ↥Bb := ((QuotientGroup.mk' P).comp (Subgroup.inclusion hKeH)).codRestrict Bb
    (fun k => ⟨Subgroup.inclusion hKeH k, Subgroup.mem_subgroupOf.2 k.2, rfl⟩) with hπ
  have hπs : Function.Surjective π := by
    rintro ⟨_, y, hy, rfl⟩
    exact ⟨⟨y, Subgroup.mem_subgroupOf.1 hy⟩, rfl⟩
  have hπk : IsPGroup 2 ↥π.ker := by
    intro x
    have hx : Subgroup.inclusion hKeH (x : ↥Ke) ∈ P := by
      have h0 : QuotientGroup.mk' P (Subgroup.inclusion hKeH (x : ↥Ke)) = 1 :=
        congrArg Subtype.val x.2
      exact (QuotientGroup.eq_one_iff _).1 h0
    obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥H)) ⟨_, hx⟩
    refine ⟨m, Subtype.ext (Subtype.ext ?_)⟩
    have h1 : (Subgroup.inclusion hKeH (x : ↥Ke)) ^ 2 ^ m = 1 := congrArg Subtype.val hm
    have h2 : ((Subgroup.inclusion hKeH (x : ↥Ke)) : G) ^ 2 ^ m = 1 := by
      simpa using congrArg Subtype.val h1
    simpa using h2
  have hA : IsAlt 5 (↥Bb ⧸ CFSG.solvableRadical ↥Bb) :=
    isAlt_quot_solvableRadical_of_surj (Kv_modO2_alt5 hyp h he) hπs hπk

  have hBfam : Bb ∈ lFamily Tb := modO2Image_mem_lFamily hSH hKeH hKeF
  have hTΛ : QuasithinUnique.IsSylowTwoOf (Tb ⊓ Lb) Lb :=
    A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp hLc) hTbar
  have hB1 : Bb ∈ lFamily (Tb ⊓ Lb) :=
    cComp_mem_of_le hBfam le_sup_left (sup_le_sup_left inf_le_left _)
  have h314 := A314.of_case_F4 hF ⟨hBfam, hBL, hTΛ, hB1, hA⟩ hcase

  obtain ⟨V₁, hab, hmod⟩ : ∃ V₁ : Subgroup G, ∃ _ : IsMulCommutative ↥V₁, Modules12_2_2 K₀ V₁ := by
    rcases h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow with hAlt | h3
    · exact absurd hAlt hyp.notAlt
    obtain ⟨-, ⟨V₁, hV₁⟩, hall⟩ := h3 K₀ hK₀max hK₀f hq
    obtain ⟨-, -, -, hmod⟩ := hall V₁ hV₁
    exact ⟨V₁, hmod⟩
  have hlist : List1222 ↥Lb := List1222.of_mulEquiv eL (list1222_of_modules hq hmod)
  obtain ⟨hB5, hL7, f, hfr, hfk, S, hScard, hSN⟩ :=
    a314_case_two_of_list h314 hBL hLq hLZ hlist
  refine ⟨?_, ?_⟩
  ·
    have hTKb : Tb ≤ normalizer (Kb : Set (↥H ⧸ P)) := map_le_normalizer_modO2Image hTK
    have hTBb : Tb ≤ normalizer (Bb : Set (↥H ⧸ P)) := map_le_normalizer_modO2Image hTKe
    have hKbp : ⁅Kb, Kb⁆ = Kb := by
      rw [hKb, modO2Image, ← Subgroup.map_commutator, commutator_subgroupOf_self hKH hKp]
    obtain ⟨eB⟩ := hB5
    have htop := eq_top_of_alt7_overgroup (Λ := ↥Lb) hLq.1.commutator_eq_top hLZ hfr hfk hScard
      (B := Bb.subgroupOf Lb) (K := Kb.subgroupOf Lb) (P := (Tb ⊓ Lb).subgroupOf Lb)
      ⟨(Subgroup.subgroupOfEquivOfLe hBL.le).trans eB⟩
      (lt_of_le_of_ne (fun x hx => Subgroup.mem_subgroupOf.2 (hBK (Subgroup.mem_subgroupOf.1 hx)))
        fun h => hBKs.ne (by
        rw [Subgroup.subgroupOf_inj, inf_eq_left.2 hBL.le, inf_eq_left.2 hKL] at h
        exact h))
      (commutator_subgroupOf_self hKL hKbp)
      (fun b hb x hx => (hSN b).1 (le_normalizer (Subgroup.mem_subgroupOf.1 hb)) x hx)
      (isSylowTwoOf_top_subgroupOf hTΛ)
      (fun t ht x hx => (hSN t).1 (hTBb (Subgroup.mem_subgroupOf.1 ht).1) x hx)
      (fun t ht => by
        rw [mem_normalizer_iff]
        intro x
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.coe_mul,
          Subgroup.coe_mul, Subgroup.coe_inv]
        exact mem_normalizer_iff.1 (hTKb (Subgroup.mem_subgroupOf.1 ht).1) x)
    have hLK : Lb ≤ Kb := fun x hx => by
      have : (⟨x, hx⟩ : ↥Lb) ∈ Kb.subgroupOf Lb := htop ▸ mem_top _
      exact Subgroup.mem_subgroupOf.1 this
    have h1 := le_sup_pCoreOf_of_modO2Image_le hK₀H hLK
    have h2 : K₀ ≤ normalizer (K : Set G) := h1.trans (sup_le le_normalizer (hPT.trans hTK))
    by_contra hne
    exact not_subnormal_of_mem_cComp hK₀c (lt_of_le_of_ne hKK₀ hne) hK1 hKp
      (IsSubnormal.step hKK₀ ((Subgroup.normal_subgroupOf_iff_le_normalizer hKK₀).2 h2)
        (subnormal_of_mem_cComp hK₀c))
  ·
    have e1 : (↥K₀ ⧸ CFSG.pCore 2 ↥K₀) ⧸ center (↥K₀ ⧸ CFSG.pCore 2 ↥K₀) ≃*
        ↥Lb ⧸ center ↥Lb :=
      QuotientGroup.congr _ _ eL (Subgroup.map_center_eq eL)
    rcases hL7 with hA7 | ⟨-, -, ⟨eA⟩⟩
    · obtain ⟨eA⟩ := hA7
      have hZ : center ↥Lb = ⊥ := by
        have h1 := Subgroup.map_center_eq eA
        rw [alternatingGroup.center_eq_bot (by simp)] at h1
        exact (Subgroup.map_eq_bot_iff_of_injective _ eA.injective).1 h1
      exact ⟨e1.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans
        (QuotientGroup.quotientBot.trans eA))⟩
    · exact ⟨e1.trans eA⟩

theorem insp1238QTab_of_F4
    (hF : A314Facts_F4) (h312 : Vol2Native.A312ForSQTKCat) (h1222 : Stmt12_2_2_F4)
    (h1225 : Stmt12_2_5_F4) : Insp1238QTab_F4 := by
  intro G _ _ T L V hyp ψ e hS h he K K₀ hK hKeK hKK₀ hK₀max hK₀f hq _ _
  exact insp1238QTab_core_F4 hF h312 h1222 h1225 hyp h he hS hK hKeK hKK₀ hK₀max hK₀f hq

end CFSG.Quasithin.H13.A7
