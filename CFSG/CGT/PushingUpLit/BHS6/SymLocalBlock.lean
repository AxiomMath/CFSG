module

public import CFSG.CGT.PushingUpLit.BHS6.SymLocalMod
public import CFSG.CGT.PushingUpLit.BHS6.AltThreeBlockGen
public import CFSG.CGT.PushingUpLit.BHS7.TwoThree
public import CFSG.CGT.PushingUpLit.BHS6.ThreeEightS3

public section

namespace CFSG.CGT.PushingUpLit.BHS6

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.G6 CFSG.QuasithinUnique
  CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement Pointwise

variable {Γ : Type} [Group Γ] {n : ℕ}

theorem hom_eq_one_of_oResidualTwo_eq_top {E : Subgroup Γ} (h : oResidualTwo ↥E = ⊤) {Q : Type*}
    [Group Q] (hQ : IsPGroup 2 Q) (f : ↥E →* Q) : ∀ x, f x = 1 := by
  have hN : oResidualTwo ↥E ≤ f.ker := by
    refine sInf_le ⟨inferInstance, ?_⟩
    exact hQ.of_injective (QuotientGroup.kerLift f) (QuotientGroup.kerLift_injective f)
  rw [h] at hN
  intro x
  exact MonoidHom.mem_ker.1 (hN (Subgroup.mem_top x))

theorem perm_three_sq_eq_one {a : Equiv.Perm (Fin 3)} {k : ℕ} (h : a ^ (2 ^ k) = 1) :
    a ^ 2 = 1 := by
  have h1 : orderOf a ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h
  have hG : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    simp [Nat.factorial]
  have h2 : orderOf a ∣ 6 := by
    have := orderOf_dvd_natCard a
    rwa [hG] at this
  obtain ⟨m, hm, hm'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  have hm1 : m ≤ 1 := by
    by_contra hcon
    have h4 : 2 ^ 2 ∣ 2 ^ m := pow_dvd_pow 2 (by omega)
    rw [← hm'] at h4
    have := h4.trans h2
    omega
  have h5 : orderOf a ∣ 2 := by
    rw [hm']
    simpa using pow_dvd_pow 2 hm1
  exact orderOf_dvd_iff_pow_eq_one.1 h5

theorem map_mem_of_oResidualTwo {G E : Subgroup Γ} {φ : ↥G →* Equiv.Perm (Fin n)}
    {Y N0 B : Subgroup (Equiv.Perm (Fin n))} (hN0Y : N0 ≤ Y)
    (hYn : Y ≤ Subgroup.normalizer (N0 : Set (Equiv.Perm (Fin n)))) (hB : IsPGroup 2 ↥B)
    (hdec : ∀ y ∈ Y, ∃ b ∈ B, ∃ δ ∈ N0, y = b * δ) (hE : oResidualTwo ↥E = ⊤)
    (hEG : E ≤ G) (hEY : ∀ (e : Γ) (he : e ∈ E), φ ⟨e, hEG he⟩ ∈ Y) :
    ∀ (e : Γ) (he : e ∈ E), φ ⟨e, hEG he⟩ ∈ N0 := by
  classical
  have : (N0.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hN0Y).mpr hYn
  let f : ↥E →* ↥Y ⧸ N0.subgroupOf Y :=
    (QuotientGroup.mk' (N0.subgroupOf Y)).comp
      (MonoidHom.codRestrict (φ.comp (Subgroup.inclusion hEG)) Y fun e => hEY e e.2)
  have hQ : IsPGroup 2 (↥Y ⧸ N0.subgroupOf Y) := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨b, hb, δ, hδ, hy⟩ := hdec y y.2
    have hbY : b ∈ Y := by
      have : b = (y : Equiv.Perm (Fin n)) * δ⁻¹ := by rw [hy]; group
      rw [this]
      exact Y.mul_mem y.2 (Y.inv_mem (hN0Y hδ))
    obtain ⟨k, hk⟩ := hB ⟨b, hb⟩
    refine ⟨k, ?_⟩
    have hmk : (QuotientGroup.mk y : ↥Y ⧸ N0.subgroupOf Y) = QuotientGroup.mk ⟨b, hbY⟩ := by
      rw [QuotientGroup.eq]
      show (y : Equiv.Perm (Fin n))⁻¹ * b ∈ N0
      have e : (y : Equiv.Perm (Fin n))⁻¹ * b = δ⁻¹ := by rw [hy]; group
      rw [e]
      exact N0.inv_mem hδ
    rw [hmk, ← QuotientGroup.mk_pow]
    have hb1 : (⟨b, hbY⟩ : ↥Y) ^ (2 ^ k) = 1 := by
      apply Subtype.ext
      have := congrArg Subtype.val hk
      simpa using this
    rw [hb1]
    rfl
  have hf : ∀ x, f x = 1 := hom_eq_one_of_oResidualTwo_eq_top hE hQ f
  intro e he
  have h1 := hf ⟨e, he⟩
  have h2 : (QuotientGroup.mk ⟨φ ⟨e, hEG he⟩, hEY e he⟩ : ↥Y ⧸ N0.subgroupOf Y) = 1 := h1
  rwa [QuotientGroup.eq_one_iff] at h2

theorem mem_of_fixes_pts {p : Fin 3 → Fin n} {Y B : Subgroup (Equiv.Perm (Fin n))}
    (hp : LocalPts p Y) (hB : B ≤ Subgroup.normalizer
      (Subgroup.zpowers (triCyc p) : Set (Equiv.Perm (Fin n))))
    (hY : Y = B ⊔ Subgroup.zpowers (triCyc p)) (hB2 : IsPGroup 2 ↥B) {σ : Equiv.Perm (Fin n)}
    (hσ : σ ∈ Y) (hfix : ∀ i, σ (p i) = p i) : σ ∈ B := by
  classical
  have hmul : ((B ⊔ Subgroup.zpowers (triCyc p) : Subgroup (Equiv.Perm (Fin n))) :
      Set (Equiv.Perm (Fin n))) = (B : Set (Equiv.Perm (Fin n))) *
      (Subgroup.zpowers (triCyc p) : Set (Equiv.Perm (Fin n))) :=
    Subgroup.coe_mul_of_left_le_normalizer_right B _ hB
  have hσ' : σ ∈ ((B ⊔ Subgroup.zpowers (triCyc p) : Subgroup (Equiv.Perm (Fin n))) :
      Set (Equiv.Perm (Fin n))) := hY ▸ hσ
  rw [hmul] at hσ'
  obtain ⟨b, hb, δ, hδ, rfl⟩ := hσ'
  have hbY : b ∈ Y := hY ▸ Subgroup.mem_sup_left hb
  have hδY : δ ∈ Y := hY ▸ Subgroup.mem_sup_right hδ
  have hbS : b ∈ setStab (triSet p) := hp.le_stab hbY
  have hδS : δ ∈ setStab (triSet p) := hp.le_stab hδY
  have hσS : b * δ ∈ setStab (triSet p) := (setStab (triSet p)).mul_mem hbS hδS
  set a := resHom hp.inj ⟨b, hbS⟩ with ha_def
  set e := resHom hp.inj ⟨δ, hδS⟩ with he_def
  have hae : a * e = 1 := by
    have h1 : resHom hp.inj ⟨b * δ, hσS⟩ = 1 := by
      refine Equiv.ext fun i => hp.inj ?_
      rw [p_resHom hp.inj]
      exact hfix i
    have e1 : (⟨b * δ, hσS⟩ : ↥(setStab (triSet p))) = ⟨b, hbS⟩ * ⟨δ, hδS⟩ := rfl
    rw [e1, map_mul] at h1
    exact h1
  have ha2 : a ^ 2 = 1 := by
    obtain ⟨k, hk⟩ := hB2 ⟨b, hb⟩
    have hk' : b ^ (2 ^ k) = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hk'' : (⟨b, hbS⟩ : ↥(setStab (triSet p))) ^ (2 ^ k) = 1 := Subtype.ext (by simpa using hk')
    exact perm_three_sq_eq_one (k := k) (by rw [ha_def, ← map_pow, hk'', map_one])
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hδ
  have hδ3 : (triCyc p ^ j) ^ 3 = 1 := by
    have h1 : (triCyc p ^ j) ^ 3 = (triCyc p ^ 3) ^ j := by
      rw [← zpow_natCast, ← zpow_natCast (triCyc p), ← zpow_mul, ← zpow_mul, mul_comm]
    rw [h1, triCyc_pow_three hp.inj, one_zpow]
  have he3 : e ^ 3 = 1 := by
    have : (⟨triCyc p ^ j, hδS⟩ : ↥(setStab (triSet p))) ^ 3 = 1 := Subtype.ext (by simpa using hδ3)
    rw [he_def, ← map_pow, this, map_one]
  have hae' : a = e⁻¹ := eq_inv_of_mul_eq_one_left hae
  have ha3 : a ^ 3 = 1 := by rw [hae', inv_pow, he3, inv_one]
  have ha1 : a = 1 := by
    calc a = a ^ 3 * (a ^ 2)⁻¹ := by group
      _ = 1 := by rw [ha3, ha2, inv_one, mul_one]
  have he1 : e = 1 := by
    rw [ha1, one_mul] at hae
    exact hae
  have hfixδ : (triCyc p ^ j) (p 0) = p 0 := by
    have := p_resHom hp.inj ⟨triCyc p ^ j, hδS⟩ 0
    rw [← he_def, he1, Equiv.Perm.one_apply] at this
    exact this.symm
  obtain ⟨m, hm⟩ := three_dvd_of_triCyc_zpow_apply_eq hp.inj hfixδ
  have hδ1 : triCyc p ^ j = 1 := by
    rw [hm, zpow_mul]
    have : triCyc p ^ (3 : ℤ) = 1 := by
      rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by rfl, zpow_natCast, triCyc_pow_three hp.inj]
    rw [this, one_zpow]
  show b * triCyc p ^ j ∈ B
  rw [hδ1, mul_one]
  exact hb

theorem pCoreOf_ne_bot_of_isNaturalAltModule_one {E : Subgroup Γ} (h : IsNaturalAltModule ↥E 1) :
    pCoreOf 2 E ≠ ⊥ := by
  intro hbot
  obtain ⟨φ', ψ', hsum, hs, hk, he⟩ := h
  obtain ⟨u, hu⟩ := hs (fun i : Fin (2 * 1 + 1) => if i.val < 2 then (1 : ZMod 2) else 0)
    (by decide)
  have hu1 : ((u : ↥E) : Γ) ∈ (shortU ↥E).map E.subtype := ⟨u, u.2, rfl⟩
  rw [map_shortU_eq_commutator E, hbot, Subgroup.commutator_bot_left] at hu1
  have h2 : (u : ↥E) = 1 := Subtype.ext (Subgroup.mem_bot.1 hu1)
  have hu0 : u = 1 := Subtype.ext h2
  rw [hu0, map_one] at hu
  have h3 : (0 : Fin (2 * 1 + 1) → ZMod 2) =
      fun i : Fin (2 * 1 + 1) => if i.val < 2 then (1 : ZMod 2) else 0 :=
    congrArg Multiplicative.toAdd hu
  have h4 := congrFun h3 ⟨0, by omega⟩
  simp at h4

structure SymBlockData (G T V : Subgroup Γ) (φ : ↥G →* Equiv.Perm (Fin n))
    (d : Equiv.Perm (Fin n)) (E : Subgroup Γ) : Prop where
  le : E ≤ G
  residual : oResidualTwo ↥E = ⊤
  commutator : ⁅E, baum T⁆ = E
  perfect : ⁅pCoreOf 2 E, E⁆ = pCoreOf 2 E
  elemAbelian : (∀ x ∈ pCoreOf 2 E, ∀ y ∈ pCoreOf 2 E, x * y = y * x) ∧
    ∀ x ∈ pCoreOf 2 E, x ^ 2 = 1
  pCore_le : pCoreOf 2 E ≤ V
  pCore_ne : pCoreOf 2 E ≠ ⊥
  comm_le : ⁅E, omegaOneCenterOf (baum T)⁆ ≤ V
  mem_img : ∃ (e : Γ) (he : e ∈ E), φ ⟨e, le he⟩ = d

structure SymSetting (G T V : Subgroup Γ) (n : ℕ) (φ : ↥G →* Equiv.Perm (Fin n))
    (ψ : ↥V →* ↥(coreMod n)) (T' : Set (Equiv.Perm (Fin n))) : Prop where
  data : SymNatData G V n φ ψ
  odd : Odd n
  charTwo : CharTwo G
  sylow : IsSylowTwoOf T G
  ne : cStarIn G T ≠ G
  vQ : V ≤ omegaOneCenterOf (pCoreOf 2 G)
  vT : omegaOneCenterOf T ≤ V
  nonempty : T'.Nonempty
  swaps : ∀ t ∈ T', t.IsSwap
  comm : ∀ t ∈ T', ∀ t' ∈ T', t * t' = t' * t
  baum : imgG G φ (baum T) = Subgroup.closure T'

structure SymTriple (T' : Set (Equiv.Perm (Fin n))) (t : Equiv.Perm (Fin n)) (x c : Fin n) :
    Prop where
  mem : t ∈ T'
  moves : t x ≠ x
  fixed : ∀ s ∈ T', s c = c

variable {G T V : Subgroup Γ} {φ : ↥G →* Equiv.Perm (Fin n)} {ψ : ↥V →* ↥(coreMod n)}
  {T' : Set (Equiv.Perm (Fin n))}

theorem localPts_of_triple (hs : ∀ t ∈ T', t.IsSwap) (hc : ∀ t ∈ T', ∀ t' ∈ T', t * t' = t' * t)
    {t : Equiv.Perm (Fin n)} {x c : Fin n} (h : SymTriple T' t x c) :
    LocalPts (triPts x c (t x)) (Subgroup.closure T' ⊔ Subgroup.zpowers (cyc x (t x) c)) := by
  classical
  have e1 : t = Equiv.swap x (t x) := eq_swap_of_isSwap_apply_ne (hs t h.mem) h.moves
  have hy : t (t x) = x := by
    have := congrArg (fun σ : Equiv.Perm (Fin n) => σ (t x)) e1
    simpa using this
  have hxy : x ≠ t x := h.moves.symm
  have hxc : x ≠ c := fun h' => h.moves (h' ▸ h.fixed t h.mem)
  have hcy : c ≠ t x := fun h' => h.moves (by
    have h1 := h.fixed t h.mem
    rw [h', hy] at h1
    exact h1.symm)
  refine ⟨injective_triPts hxc hxy hcy, sup_zpowers_le_setStab hs hc h.mem h.moves h.fixed,
    ?_, ?_, ?_⟩
  · rw [← triCyc_triPts]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  · exact sup_le (closure_le_normalizer_zpowers_cyc hs hc h.mem h.moves h.fixed)
      Subgroup.le_normalizer
  · show Equiv.swap x (t x) ∈ _
    rw [← e1]
    exact Subgroup.mem_sup_left (Subgroup.subset_closure h.mem)

theorem omegaOneCenterOf_le_of_baum_le {T T₀ : Subgroup Γ} (hB : baum T ≤ T₀) (hT₀T : T₀ ≤ T) :
    omegaOneCenterOf T ≤ omegaOneCenterOf T₀ := by
  refine Subgroup.closure_mono ?_
  rintro x ⟨hxZ, hx2⟩
  have hxZ' : x ∈ T ⊓ Subgroup.centralizer (T : Set Γ) := hxZ
  have hxc : ∀ y ∈ T, y * x = x * y := fun y hy => Subgroup.mem_centralizer_iff.1 hxZ'.2 y hy
  have hxB : x ∈ baum T := BHS7.inf_centralizer_baum_le T ⟨hxZ'.1,
    Subgroup.mem_centralizer_iff.2 fun y hy => hxc y ((inf_le_left : baum T ≤ T) hy)⟩
  have hxT₀ : x ∈ T₀ := hB hxB
  exact ⟨⟨hxT₀, Subgroup.mem_centralizer_iff.2 fun y hy => hxc y (hT₀T hy)⟩, hx2⟩

theorem map_eq_one_of_mem_pCoreOf (D : SymNatData G V n φ ψ)
    (hVQ : V ≤ omegaOneCenterOf (pCoreOf 2 G)) {g : Γ} (hg : g ∈ pCoreOf 2 G)
    (hgG : g ∈ G) : φ ⟨g, hgG⟩ = 1 := by
  have hVc : V ≤ Subgroup.centralizer (pCoreOf 2 G : Set Γ) :=
    hVQ.trans ((Subgroup.closure_le _).mpr fun x hx => hx.1.2)
  have h1 : (⟨g, hgG⟩ : ↥G) ∈ φ.ker := by
    rw [D.φ_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    refine ⟨hgG, Subgroup.mem_centralizer_iff.2 fun v hv => ?_⟩
    exact (Subgroup.mem_centralizer_iff.1 (hVc hv) g hg).symm
  exact h1

section Local

variable [Finite Γ]

omit [Finite Γ] in
theorem uMod_le_omegaOneCenter (D : SymNatData G V n φ ψ) {p : Fin 3 → Fin n}
    {Y : Subgroup (Equiv.Perm (Fin n))} (hp : LocalPts p Y)
    (hVQ : V ≤ omegaOneCenterOf (pCoreOf 2 G)) :
    uMod G V φ p ≤ omegaOneCenterOf (pCoreOf 2 (preimG G φ Y)) := by
  classical
  set L : Subgroup Γ := preimG G φ Y with hL
  have hLG : L ≤ G := preimG_le G φ Y
  have hOL : pCoreOf 2 G ≤ pCoreOf 2 L := by
    refine le_pCoreOf_of_normalizes (p := 2) (fun g hg => ?_) ?_
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 G)
    · have hgG : g ∈ G := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 G hg
      exact mem_preimG_of_map_eq_one hgG (map_eq_one_of_mem_pCoreOf D hVQ hg hgG)
    · exact hLG.trans (le_normalizer_pCoreOf_self' G)
  have hOLL : pCoreOf 2 L ≤ L := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 L
  have hQnormal : ((pCoreOf 2 L).subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOLL).mpr
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
  have hQp : IsPGroup 2 ↥((pCoreOf 2 L).subgroupOf L) :=
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 L).of_equiv
      (Subgroup.subgroupOfEquivOfLe hOLL).symm
  have hNn : ((pCoreOf 2 L).subgroupOf L).map (locHom (G := G) (φ := φ) hp) = ⊥ :=
    eq_bot_of_normal_isPGroup_perm_three
      (hQnormal.map _ (locHom_surjective D hp)) (hQp.map _)
  intro u hu
  have huV : u ∈ V := uMod_le_V D hu
  refine Subgroup.subset_closure ⟨⟨hOL ((hVQ.trans (C1GN.omegaOneCenterOf_le_self _)) huV), ?_⟩, ?_⟩
  · show u ∈ Subgroup.centralizer (pCoreOf 2 L : Set Γ)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyL : y ∈ L := hOLL hy
    have h1 : locHom (G := G) (φ := φ) hp ⟨y, hyL⟩ = 1 := by
      have : locHom (G := G) (φ := φ) hp ⟨y, hyL⟩ ∈
          ((pCoreOf 2 L).subgroupOf L).map (locHom (G := G) (φ := φ) hp) :=
        ⟨⟨y, hyL⟩, hy, rfl⟩
      rw [hNn] at this
      exact Subgroup.mem_bot.1 this
    have h2 : (⟨y, hyL⟩ : ↥L) ∈ (locHom (G := G) (φ := φ) hp).ker := h1
    rw [ker_locHom D hp, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at h2
    exact (Subgroup.mem_centralizer_iff.1 h2.2 u hu).symm
  · exact D.elemAbelian.2 u huV

theorem sym_local_block (S : SymSetting G T V n φ ψ T') {t : Equiv.Perm (Fin n)} {x c : Fin n}
    (h : SymTriple T' t x c) : ∃ E : Subgroup Γ, SymBlockData G T V φ (cyc x (t x) c) E := by
  classical
  set d : Equiv.Perm (Fin n) := cyc x (t x) c with hd
  set p : Fin 3 → Fin n := triPts x c (t x) with hp_def
  set B : Subgroup (Equiv.Perm (Fin n)) := Subgroup.closure T' with hB_def
  set Y : Subgroup (Equiv.Perm (Fin n)) := B ⊔ Subgroup.zpowers d with hY_def
  have hp : LocalPts p Y := localPts_of_triple S.swaps S.comm h
  have hSB : imgG G φ (baum T) = B := S.baum
  have hdp : triCyc p = d := triCyc_triPts x c (t x)
  have hd3 : d ^ 3 = 1 := by rw [← hdp]; exact triCyc_pow_three hp.inj
  have hBn : B ≤ Subgroup.normalizer (Subgroup.zpowers d : Set (Equiv.Perm (Fin n))) :=
    closure_le_normalizer_zpowers_cyc S.swaps S.comm h.mem h.moves h.fixed
  have hBp : IsPGroup 2 ↥B := by
    have h1 : IsPGroup 2 ↥(imgG G φ (baum T)) :=
      isPGroup_imgG (inf_le_left.trans S.sylow.1) (S.sylow.2.1.to_le inf_le_left)
    rw [hSB] at h1
    exact h1
  set L : Subgroup Γ := preimG G φ Y with hL_def
  set TL : Subgroup Γ := T ⊓ L with hTL_def
  set C : Subgroup Γ := cStarIn G T with hC_def
  have hLG : L ≤ G := preimG_le G φ Y
  have hbG : baum T ≤ G := inf_le_left.trans S.sylow.1
  have hKC : ∀ (g : Γ) (hg : g ∈ G), φ ⟨g, hg⟩ = 1 → g ∈ C := by
    intro g hg h1
    have h2 : (⟨g, hg⟩ : ↥G) ∈ φ.ker := h1
    rw [S.data.φ_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at h2
    exact centralizer_le_cStarIn G T ⟨hg, Subgroup.centralizer_le S.vT h2.2⟩
  have hBimg : B ≤ imgG G φ T := by
    rw [← hSB]
    exact imgG_mono G φ (inf_le_left : baum T ≤ T)
  have hmax : ∀ P : Subgroup (Equiv.Perm (Fin n)), P ≤ Y → IsPGroup 2 ↥P →
      imgG G φ T ⊓ Y ≤ P → P ≤ imgG G φ T ⊓ Y := by
    intro P hPY hP hXP
    have hBX : B ≤ imgG G φ T ⊓ Y := le_inf hBimg (le_sup_left)
    have hBP : B ≤ P := hBX.trans hXP
    have hPB : P ≤ B := le_of_isPGroup_of_le_sup_zpowers hd3 hBn hP hBP hPY
    exact hPB.trans hBX
  have hTL : IsSylowTwoOf TL L := isSylowTwoOf_preimG_inf S.sylow φ Y hmax
  have hbTL : baum T ≤ TL := by
    refine le_inf inf_le_left fun b hb => ?_
    exact mem_preimG.2 ⟨hbG hb, le_sup_left (a := B) (b := Subgroup.zpowers d) (by
      rw [← hSB]; exact mem_imgG.2 ⟨b, hbG hb, hb, rfl⟩)⟩
  have hbaumTL : baum TL = baum T :=
    baum_eq_of_isPGroup_of_baum_le S.sylow (S.sylow.2.1.to_le inf_le_left)
      (inf_le_left.trans S.sylow.1) hbTL
  have hGL : CharTwo L := BHS7.two_three_c S.charTwo S.sylow hLG hTL hbTL
  have hb0 : baum T ≠ ⊥ := by
    intro h0
    have h1 : t ∈ imgG G φ (baum T) := by
      rw [hSB]
      exact Subgroup.subset_closure h.mem
    obtain ⟨g, hg, hgB, hgt⟩ := mem_imgG.1 h1
    rw [h0, Subgroup.mem_bot] at hgB
    subst hgB
    have h1' : (⟨(1 : Γ), hg⟩ : ↥G) = 1 := rfl
    rw [h1', map_one] at hgt
    obtain ⟨a, b, hab, rfl⟩ := S.swaps _ h.mem
    have := congrArg (fun f : Equiv.Perm (Fin n) => f a) hgt
    simp only [Equiv.swap_apply_left, Equiv.Perm.one_apply] at this
    exact hab this
  have hNC : G ⊓ Subgroup.normalizer (baum T : Set Γ) ≤ C := inf_normalizer_baum_le_cStarIn hb0
  have hMne : C ⊓ L ≠ L := by
    intro hM
    exact not_preimG_le_cStarIn S.sylow S.ne φ S.data.φ_surj S.odd hKC S.nonempty S.swaps S.comm
      S.baum h.mem h.moves h.fixed (inf_eq_right.1 hM)
  have hN : L ⊓ Subgroup.normalizer (TL : Set Γ) ≤ C ⊓ L := by
    intro l hl
    refine ⟨hNC ⟨hLG hl.1, ?_⟩, hl.1⟩
    have h1 := normalizer_le_normalizer_baum TL hl.2
    rwa [hbaumTL] at h1
  have hchN : ∀ C' : Subgroup Γ, C' ≤ baum TL → C' ≠ ⊥ → (C'.subgroupOf (baum TL)).Characteristic →
      L ⊓ Subgroup.normalizer (C' : Set Γ) ≤ C ⊓ L := by
    intro C' hC'B hC'0 hC'c l hl
    rw [hbaumTL] at hC'B hC'c
    have h1 : G ⊓ Subgroup.normalizer (C' : Set Γ) ≤ cgsIn G (baum T) :=
      le_iSup_of_le C' (le_iSup_of_le hC'B (le_iSup_of_le hC'0 (le_iSup_of_le hC'c le_rfl)))
    exact ⟨le_sup_right (a := G ⊓ Subgroup.centralizer (omegaOneCenterOf T : Set Γ))
      (h1 ⟨hLG hl.1, hl.2⟩), hl.1⟩
  set U : Subgroup Γ := uMod G V φ p with hU_def
  have hCUB : ∀ l ∈ L, l ∈ Subgroup.centralizer (U : Set Γ) →
      ∃ hlG : l ∈ G, φ ⟨l, hlG⟩ ∈ B := by
    intro l hlL hlc
    have hlG : l ∈ G := hLG hlL
    refine ⟨hlG, ?_⟩
    have h2 : (⟨l, hlL⟩ : ↥L) ∈ (locHom (G := G) (φ := φ) hp).ker := by
      rw [ker_locHom S.data hp, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨hlL, hlc⟩
    have hfix : ∀ i, (φ ⟨l, hlG⟩ : Equiv.Perm (Fin n)) (p i) = p i := fun i => by
      have := p_locHom hp ⟨l, hlL⟩ i
      rw [show locHom (G := G) (φ := φ) hp ⟨l, hlL⟩ = 1 from h2, Equiv.Perm.one_apply] at this
      exact this.symm
    exact mem_of_fixes_pts hp hBn hY_def hBp (mem_preimG.1 hlL).2 hfix
  have hCU : L ⊓ Subgroup.centralizer (U : Set Γ) ≤ C ⊓ L := by
    intro l hl
    obtain ⟨hlG, hlB⟩ := hCUB l hl.1 hl.2
    rw [← hSB] at hlB
    obtain ⟨b, hbG, hbB, hbl⟩ := mem_imgG.1 hlB
    have hbC : b ∈ C := hNC ⟨hbG, Subgroup.le_normalizer hbB⟩
    have hker : b⁻¹ * l ∈ C := by
      refine hKC _ (G.mul_mem (G.inv_mem hbG) hlG) ?_
      have e : (⟨b⁻¹ * l, G.mul_mem (G.inv_mem hbG) hlG⟩ : ↥G) = ⟨b, hbG⟩⁻¹ * ⟨l, hlG⟩ := rfl
      rw [e, map_mul, map_inv, hbl]
      simp
    have := C.mul_mem hbC hker
    refine ⟨by simpa using this, hl.1⟩
  have hZ : L ⊓ Subgroup.centralizer (omegaOneCenterOf TL : Set Γ) ≤ C ⊓ L := by
    intro l hl
    have hZT : omegaOneCenterOf T ≤ omegaOneCenterOf TL :=
      omegaOneCenterOf_le_of_baum_le hbTL inf_le_left
    exact ⟨centralizer_le_cStarIn G T ⟨hLG hl.1, Subgroup.centralizer_le hZT hl.2⟩, hl.1⟩
  have hVn : L ≤ Subgroup.normalizer (U : Set Γ) := fun l hl => mem_normalizer_uMod S.data hp hl
  have hVQ : U ≤ omegaOneCenterOf (pCoreOf 2 L) := uMod_le_omegaOneCenter S.data hp S.vQ
  have hnat : IsNatSL L U 1 := isNatSL_one_of_isNatSym_three (isNatSym_local S.data hp)
  obtain ⟨E, hEblock, hEnat, hEpC, hGfin, hEcomm⟩ :=
    alt_three_block_gen hGL hTL inf_le_right hMne hN hchN hCU hZ hVn hVQ hnat
  have hEL : E ≤ L := hEblock.le
  have hEG : E ≤ G := hEL.trans hLG
  have hUV : U ≤ V := uMod_le_V S.data
  have hdec : ∀ y ∈ Y, ∃ b ∈ B, ∃ δ ∈ Subgroup.zpowers d, y = b * δ := by
    intro y hy
    have hmul : ((B ⊔ Subgroup.zpowers d : Subgroup (Equiv.Perm (Fin n))) :
        Set (Equiv.Perm (Fin n))) = (B : Set (Equiv.Perm (Fin n))) *
        (Subgroup.zpowers d : Set (Equiv.Perm (Fin n))) :=
      Subgroup.coe_mul_of_left_le_normalizer_right B _ hBn
    have hy' : y ∈ ((B ⊔ Subgroup.zpowers d : Subgroup (Equiv.Perm (Fin n))) :
        Set (Equiv.Perm (Fin n))) := hy
    rw [hmul] at hy'
    obtain ⟨b, hb, δ, hδ, rfl⟩ := hy'
    exact ⟨b, hb, δ, hδ, rfl⟩
  have hEY : ∀ (e : Γ) (he : e ∈ E), φ ⟨e, hEG he⟩ ∈ Y := fun e he =>
    (mem_preimG.1 (hEL he)).2
  have hφE : ∀ (e : Γ) (he : e ∈ E), φ ⟨e, hEG he⟩ ∈ Subgroup.zpowers d :=
    map_mem_of_oResidualTwo (le_sup_right : Subgroup.zpowers d ≤ Y)
      (hdp ▸ hp.normalizes) hBp hdec hEblock.residual hEG hEY
  have hne1 : ∃ (e : Γ) (he : e ∈ E), φ ⟨e, hEG he⟩ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hLB : L ≤ preimG G φ B := by
      have hsub : baum TL ⊔ E ⊔ (L ⊓ Subgroup.centralizer (U : Set Γ)) ≤ preimG G φ B := by
        refine sup_le (sup_le ?_ ?_) ?_
        · rw [hbaumTL]
          intro b hb
          exact mem_preimG.2 ⟨hbG hb, by rw [← hSB]; exact mem_imgG.2 ⟨b, hbG hb, hb, rfl⟩⟩
        · intro e he
          exact mem_preimG.2 ⟨hEG he, by rw [hcon e he]; exact B.one_mem⟩
        · intro l hl
          obtain ⟨hlG, hlB⟩ := hCUB l hl.1 hl.2
          exact mem_preimG.2 ⟨hlG, hlB⟩
      exact hGfin.trans hsub
    obtain ⟨l₀, hl₀⟩ := S.data.φ_surj d
    have hl₀φ : φ ⟨(l₀ : Γ), l₀.2⟩ = d := hl₀
    have hl₀L : (l₀ : Γ) ∈ L :=
      mem_preimG.2 ⟨l₀.2, by rw [hl₀φ]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers d)⟩
    have hdB : d ∈ B := by
      have := (mem_preimG.1 (hLB hl₀L)).2
      rwa [hl₀φ] at this
    obtain ⟨k, hk⟩ := hBp ⟨d, hdB⟩
    have hk' : d ^ (2 ^ k) = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left _ (by norm_num)
    have hone : orderOf d = 1 := Nat.eq_one_of_dvd_coprimes hcop
      (orderOf_dvd_of_pow_eq_one hk') (orderOf_dvd_of_pow_eq_one hd3)
    have hd1 : d = 1 := orderOf_eq_one_iff.1 hone
    exact triCyc_ne_one hp.inj (hdp.trans hd1)
  have hmem : ∃ (e : Γ) (he : e ∈ E), φ ⟨e, hEG he⟩ = d := by
    obtain ⟨e, he, hne⟩ := hne1
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (hφE e he)
    have hjmod : d ^ j = d ^ (j % 3) := by
      rw [← zpow_mod_orderOf, ← hdp, (triCyc_isThreeCycle hp.inj).orderOf]
      rfl
    have hr : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
    rcases hr with h0 | h1 | h2
    · exfalso
      apply hne
      rw [← hj, hjmod, h0, zpow_zero]
    · refine ⟨e, he, ?_⟩
      rw [← hj, hjmod, h1, zpow_one]
    · refine ⟨e ^ 2, Subgroup.pow_mem E he 2, ?_⟩
      have e1 : (⟨e ^ 2, hEG (Subgroup.pow_mem E he 2)⟩ : ↥G) = ⟨e, hEG he⟩ ^ 2 := rfl
      rw [e1, map_pow, ← hj, hjmod, h2]
      calc (d ^ (2 : ℤ)) ^ 2 = d ^ 3 * d := by group
        _ = d := by rw [hd3, one_mul]
  refine ⟨E, ⟨hEG, hEblock.residual, ?_, hEblock.perfect, hEblock.elemAbelian,
    hEpC.trans hUV, pCoreOf_ne_bot_of_isNaturalAltModule_one hEnat, ?_, hmem⟩⟩
  · rw [← hbaumTL]
    exact hEblock.commutator
  · rw [← hbaumTL]
    exact hEcomm.trans hUV

end Local

end CFSG.CGT.PushingUpLit.BHS6
