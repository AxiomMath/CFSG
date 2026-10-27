module

public import CFSG.GH74.GLS.Stage1.Main.BrTwoClassU
public import CFSG.GH74.GLS.Stage1.Main.BrTwoClassT
public import CFSG.GH74.GLS.Stage1.Main.BrTwoClassN

public section

namespace CFSG.GH74.GLS.Stage1.Main

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage1.Thm3.Sec4
  CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6 CFSG.GH74.GLS.Stage1.Thm3.Sec7
  CFSG.GH74.GLS.Stage1.Thm3.Sec8 CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.GH74.GLS.Stage1.Thm6.Prod
  CFSG.GH74.GLS.Stage2.Final CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement Pointwise

section Concrete

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G} {q : ℕ}

omit [Finite G] in
theorem bar_mem_normalizer {K : Subgroup G} (hK : K ≤ Cz z) {w : G} (hw : w ∈ Cz z)
    (hN : w ∈ normalizer (K : Set G)) :
    piC z ⟨w, hw⟩ ∈ normalizer ((imgBar z K : Subgroup (CentralizerBar z)) : Set (CentralizerBar z)) := by
  have hcj : conjugate K w = K := by
    ext x
    rw [mem_conjugate_iff]
    exact (Subgroup.mem_normalizer_iff.1 hN x).symm
  have himg : conjugate (imgBar z K) (piC z ⟨w, hw⟩) = imgBar z K := by
    have := imgBar_conjugate hK hw
    rw [hcj] at this
    exact this.symm
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have := Subgroup.ext_iff.1 himg x
  rw [mem_conjugate_iff] at this
  exact this.symm

theorem mem_normalizer_of_bar (hII : II4_4_4_center) (hs : Std4 G z S K₁ K₂)
    (hA12 : imgBar z K₁ ≠ imgBar z K₂) {s : G} (hsC : s ∈ Cz z)
    (hn : piC z ⟨s, hsC⟩ ∈
      normalizer ((imgBar z K₁ : Subgroup (CentralizerBar z)) : Set (CentralizerBar z))) :
    s ∈ normalizer (K₁ : Set G) := by
  have hM := m4_of_std hII hs
  have hr₁ := hs.comp_rigid (K := K₁) (Or.inl rfl)
  have hc₁ := isRigidRankOneComp_cmap hr₁ ((Cz z).inv_mem hsC)
  have hmem₁ : cmap s⁻¹ K₁ ∈ ({K₁, K₂} : Set (Subgroup G)) := by
    rw [← hs.comps]
    exact hc₁
  have hcj : conjugate K₁ s = cmap s⁻¹ K₁ := rfl
  have himg : imgBar z (conjugate K₁ s) = imgBar z K₁ := by
    rw [imgBar_conjugate hM.K₁_le hsC]
    ext x
    rw [mem_conjugate_iff]
    exact (Subgroup.mem_normalizer_iff.1 hn x).symm
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem₁
  rcases hmem₁ with h | h
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    have hx := Subgroup.ext_iff.1 (hcj.trans h) x
    rw [mem_conjugate_iff] at hx
    exact hx.symm
  · exfalso
    rw [hcj, h] at himg
    exact hA12 himg.symm

theorem S_le_normalizer_Pz (hII : II4_4_4_center) (hs : Std4 G z S K₁ K₂) :
    S ≤ normalizer ((Pz S z : Subgroup G) : Set G) := by
  have hM := m4_of_std hII hs
  have hSC : S ≤ Cen z := hs.sylow.le
  have key : ∀ {s : G}, s ∈ S → ∀ {p : G}, p ∈ Pz S z → s * p * s⁻¹ ∈ Pz S z := by
    intro s hs' p hp
    refine ⟨S.mul_mem (S.mul_mem hs' hp.1) (S.inv_mem hs'), ?_⟩
    have hpK : p ∈ K₁ ⊔ K₂ := by
      have := hp.2
      rwa [hs.rigidProduct_eq] at this
    rw [hs.rigidProduct_eq]
    exact hM.C_norm_K (hSC hs') hpK
  intro s hs'
  rw [Subgroup.mem_normalizer_iff]
  intro p
  constructor
  · exact fun hp => key hs' hp
  · intro hp
    have := key (S.inv_mem hs') hp
    have e : s⁻¹ * (s * p * s⁻¹) * (s⁻¹)⁻¹ = p := by group
    rw [e] at this
    exact this

theorem bar_S1_le (hII : II4_4_4_center) (hs : Std4 G z S K₁ K₂) (hA12 : imgBar z K₁ ≠ imgBar z K₂)
    {w : G} (hwS : w ∈ S) (hw2 : w * w = 1) (hwN₂ : w ∈ normalizer (K₂ : Set G))
    (hS1 : CFSG.GH74.GLS.Stage1.Thm3.Sec5.S1 S K₁ = Pz S z ⊔ zpowers w) {s : G} (hsS : s ∈ S)
    (hsn : piC z ⟨s, hs.sylow.le hsS⟩ ∈
      normalizer ((imgBar z K₁ : Subgroup (CentralizerBar z)) : Set (CentralizerBar z))) :
    piC z ⟨s, hs.sylow.le hsS⟩ ∈ (imgBar z K₁ ⊔ barOf z (zpowers w)) ⊔
      centralizer ((imgBar z K₁ : Subgroup (CentralizerBar z)) : Set (CentralizerBar z)) := by
  have hM := m4_of_std hII hs
  have hsC : s ∈ Cz z := hs.sylow.le hsS
  have hwC : w ∈ Cz z := hs.sylow.le hwS
  have hsN₁ := mem_normalizer_of_bar hII hs hA12 hsC hsn
  have hs1 : s ∈ CFSG.GH74.GLS.Stage1.Thm3.Sec5.S1 S K₁ := ⟨hsS, hsN₁⟩
  rw [hS1] at hs1
  have hzw : zpowers w ≤ normalizer ((Pz S z : Subgroup G) : Set G) :=
    (Subgroup.zpowers_le.2 hwS).trans (S_le_normalizer_Pz hII hs)
  have hmul := Subgroup.coe_mul_of_right_le_normalizer_left (Pz S z) (zpowers w) hzw
  have hs' : s ∈ ((Pz S z : Subgroup G) : Set G) * ((zpowers w : Subgroup G) : Set G) := by
    rw [← hmul]
    exact hs1
  obtain ⟨p, hp, a, ha, hpa⟩ := Set.mem_mul.1 hs'
  have hpC : p ∈ Cz z := hs.sylow.le hp.1
  have haC : a ∈ Cz z := (Subgroup.zpowers_le.2 hwC) ha
  have hpK : p ∈ K₁ ⊔ K₂ := by
    have := hp.2
    rwa [hs.rigidProduct_eq] at this
  have hpbar : piC z ⟨p, hpC⟩ ∈ imgBar z K₁ ⊔ imgBar z K₂ := by
    rw [← map_K12 hII hs]
    exact ⟨⟨p, hpC⟩, hpK, rfl⟩
  have hcommA := imgBar_comm4 hII hs
  obtain ⟨a₁, ha₁, a₂, ha₂, hpa'⟩ :=
    CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic.mem_sup_of_commute' hcommA hpbar
  have hsplit : piC z ⟨s, hsC⟩ = piC z ⟨p, hpC⟩ * piC z ⟨a, haC⟩ := by
    rw [← map_mul]
    congr 1
    exact Subtype.ext hpa.symm
  have hC₂ : a₂ ∈ centralizer ((imgBar z K₁ : Subgroup (CentralizerBar z)) : Set (CentralizerBar z)) :=
    Subgroup.mem_centralizer_iff.2 fun l hl => hcommA l hl a₂ ha₂
  have hLB : imgBar z K₁ ≤ imgBar z K₁ ⊔ barOf z (zpowers w) := le_sup_left
  rcases eq_one_or_eq_of_mem_zpowers_sq hw2 ha with h | h
  · have ha1 : piC z ⟨a, haC⟩ = 1 := by
      have : (⟨a, haC⟩ : ↥(Cz z)) = 1 := Subtype.ext h
      rw [this, map_one]
    rw [hsplit, ha1, mul_one, hpa']
    exact Subgroup.mul_mem_sup (hLB ha₁) hC₂
  · have haw : piC z ⟨a, haC⟩ = piC z ⟨w, hwC⟩ := by
      have : (⟨a, haC⟩ : ↥(Cz z)) = ⟨w, hwC⟩ := Subtype.ext h
      rw [this]
    have hwbar₂ := bar_mem_normalizer hM.K₂_le hwC hwN₂
    have hbarw : piC z ⟨w, hwC⟩ ∈ barOf z (zpowers w) :=
      ⟨⟨w, hwC⟩, Subgroup.mem_subgroupOf.2 (Subgroup.mem_zpowers w), rfl⟩
    have hb₂ : (piC z ⟨w, hwC⟩)⁻¹ * a₂ * (piC z ⟨w, hwC⟩)⁻¹⁻¹ ∈ imgBar z K₂ :=
      (Subgroup.mem_normalizer_iff.1 ((normalizer _).inv_mem hwbar₂) a₂).1 ha₂
    have hb₂' : (piC z ⟨w, hwC⟩)⁻¹ * a₂ * piC z ⟨w, hwC⟩ ∈
        centralizer ((imgBar z K₁ : Subgroup (CentralizerBar z)) : Set (CentralizerBar z)) := by
      rw [inv_inv] at hb₂
      exact Subgroup.mem_centralizer_iff.2 fun l hl => hcommA l hl _ hb₂
    have e : piC z ⟨s, hsC⟩ =
        (a₁ * piC z ⟨w, hwC⟩) * ((piC z ⟨w, hwC⟩)⁻¹ * a₂ * piC z ⟨w, hwC⟩) := by
      rw [hsplit, haw, hpa']
      group
    rw [e]
    exact Subgroup.mul_mem_sup
      ((imgBar z K₁ ⊔ barOf z (zpowers w)).mul_mem (hLB ha₁) (Subgroup.mem_sup_right hbarw)) hb₂'
  

omit [Finite G] in
theorem barOf_zpowers {w : G} (hw : w ∈ Cz z) :
    barOf z (zpowers w) = zpowers (piC z ⟨w, hw⟩) := by
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (Subgroup.mem_subgroupOf.1 hv)
    have : v = (⟨w, hw⟩ : ↥(Cz z)) ^ k := Subtype.ext (by simpa using hk.symm)
    rw [this, map_zpow]
    exact zpow_mem_zpowers _ k
  · intro hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    refine ⟨(⟨w, hw⟩ : ↥(Cz z)) ^ k, Subgroup.mem_subgroupOf.2 ?_, ?_⟩
    · simp
    · rw [map_zpow]
      rfl

theorem inducedPGL2_of_pglQuot (hII : II4_4_4_center) (hs : Std4 G z S K₁ K₂) {K : Subgroup G}
    (hK : K = K₁ ∨ K = K₂) {q : ℕ} (hodd : Odd q) (h3 : 3 < q)
    (hL : HasSL2Model ↥(imgBar z K) (fun r => r = q)) {w : G} (hwC : w ∈ Cz z) (hw2 : w * w = 1)
    (hwN : w ∈ normalizer (K : Set G)) {Fq : Type} [Field Fq] [Finite Fq] (hq : Nat.card Fq = q)
    (h : PGLQuot z w K Fq) {T : Subgroup (CentralizerBar z)}
    (hTN : T ≤ normalizer ((imgBar z K : Subgroup (CentralizerBar z)) : Set (CentralizerBar z)))
    (hwT : piC z ⟨w, hwC⟩ ∈ T)
    (hTle : T ≤ (imgBar z K ⊔ barOf z (zpowers w)) ⊔
      centralizer ((imgBar z K : Subgroup (CentralizerBar z)) : Set (CentralizerBar z))) :
    InducedPGL2 (imgBar z K) T q := by
  have hM := m4_of_std hII hs
  have hKC : K ≤ Cz z := by
    rcases hK with rfl | rfl
    · exact hM.K₁_le
    · exact hM.K₂_le
  obtain ⟨hZn, F, iF, fF, hFq, ⟨φ⟩⟩ := pglOver_of_pglQuot hII hs hK hL hwC hw2 hwN hq h
  set L : Subgroup (CentralizerBar z) := imgBar z K with hLdef
  set Z : Subgroup (CentralizerBar z) := (center ↥L).map L.subtype with hZdef
  have hbar_w : piC z ⟨w, hwC⟩ ∈ normalizer (L : Set (CentralizerBar z)) :=
    bar_mem_normalizer hKC hwC hwN
  have hbw : barOf z (zpowers w) = zpowers (piC z ⟨w, hwC⟩) := barOf_zpowers hwC
  have hBN : L ⊔ barOf z (zpowers w) ≤ normalizer (L : Set (CentralizerBar z)) := by
    refine sup_le Subgroup.le_normalizer ?_
    rw [hbw]
    exact Subgroup.zpowers_le.2 hbar_w
  have hLB : L ≤ L ⊔ barOf z (zpowers w) := le_sup_left
  have hwb2 : piC z ⟨w, hwC⟩ * piC z ⟨w, hwC⟩ = 1 := by
    rw [← map_mul]
    have : (⟨w, hwC⟩ : ↥(Cz z)) * ⟨w, hwC⟩ = 1 := Subtype.ext hw2
    rw [this, map_one]
  have hq5 : 5 ≤ q := by
    have := hodd
    obtain ⟨m, hm⟩ := hodd
    omega
  have hperf : Group.IsPerfect ↥L := (quasi_of_hasSL2 hq5 hL).1
  have hidx : L.relIndex (L ⊔ barOf z (zpowers w)) ≤ 2 := by
    rw [hbw]
    exact relIndex_le_two_of_involution hwb2 hbar_w
  have hFodd : Odd (Nat.card F) := by rw [hFq]; exact hodd
  have hFop := CFSG.ABGLocalTools.isOddPrimePower_card_of_odd hFodd
  have hF3 : 3 < Nat.card F := by rw [hFq]; exact h3
  have hBC : (L ⊔ barOf z (zpowers w)) ⊓ centralizer (L : Set (CentralizerBar z)) = Z := by
    apply le_antisymm
    · exact inf_centralizer_le_Z hLB hperf hidx hFop hF3 φ
    · refine le_inf ?_ ?_
      · rintro _ ⟨c, -, rfl⟩
        exact hLB c.2
      · rintro _ ⟨c, hc, rfl⟩
        rw [Subgroup.mem_centralizer_iff]
        intro l hl
        exact congrArg Subtype.val ((Subgroup.mem_center_iff.1 hc) ⟨l, hl⟩)
  have hBT : L ⊔ barOf z (zpowers w) ≤ L ⊔ T := by
    refine sup_le le_sup_left ?_
    rw [hbw]
    exact (Subgroup.zpowers_le.2 hwT).trans le_sup_right
  have hA : L ⊔ T ≤ (L ⊔ barOf z (zpowers w)) ⊔ centralizer (L : Set (CentralizerBar z)) :=
    sup_le (hLB.trans le_sup_left) hTle
  obtain ⟨hCn, ⟨e⟩⟩ := inducedQuot_equiv hBN hTN hBT hA hBC (hZn := hZn)
  exact ⟨hCn, F, iF, fF, hFq, ⟨e.trans φ⟩⟩

theorem mem_normalizer_swap (hs : Std4 G z S K₁ K₂) {s : G} (hsC : s ∈ Cz z)
    (h : s ∈ normalizer (K₁ : Set G)) : s ∈ normalizer (K₂ : Set G) := by
  have hr₂ := hs.comp_rigid (K := K₂) (Or.inr rfl)
  have hc₂ := isRigidRankOneComp_cmap hr₂ ((Cz z).inv_mem hsC)
  have hmem : cmap s⁻¹ K₂ ∈ ({K₁, K₂} : Set (Subgroup G)) := by
    rw [← hs.comps]
    exact hc₂
  have hcj₂ : conjugate K₂ s = cmap s⁻¹ K₂ := rfl
  have hcj₁ : conjugate K₁ s = K₁ := by
    ext x
    rw [mem_conjugate_iff]
    exact (Subgroup.mem_normalizer_iff.1 h x).symm
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h2 | h2
  · exfalso
    have : conjugate K₂ s = conjugate K₁ s := by rw [hcj₂, h2, hcj₁]
    apply hs.ne
    exact (Subgroup.map_injective (MulAut.conj s⁻¹).injective this).symm
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    have hx := Subgroup.ext_iff.1 (hcj₂.trans h2) x
    rw [mem_conjugate_iff] at hx
    exact hx.symm

omit [Finite G] in
theorem mem_localS1_iff {s : G} (hsC : s ∈ Cen z) :
    s ∈ CFSG.GH74.GLS.Stage2.Local.S1 S z ↔ s ∈ S ∧ ∀ K : Subgroup (CentralizerBar z),
      IsComponent K → K ≤ LBar z →
        toBar z ⟨s, hsC⟩ ∈ normalizer (K : Set (CentralizerBar z)) := by
  unfold CFSG.GH74.GLS.Stage2.Local.S1
  simp only [Subgroup.mem_inf, Subgroup.mem_map, Subgroup.mem_iInf, Subgroup.mem_comap,
    Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hs, ⟨c, hc, hcs⟩⟩
    refine ⟨hs, fun K hK hKL => ?_⟩
    have hcs' : c = ⟨s, hsC⟩ := Subtype.ext hcs
    rw [← hcs']
    exact hc K ⟨hK, hKL⟩
  · rintro ⟨hs, h⟩
    exact ⟨hs, ⟨⟨s, hsC⟩, fun K hK => h K hK.1 hK.2, rfl⟩⟩

theorem S1_swap_eq (hs : Std4 G z S K₁ K₂) :
    CFSG.GH74.GLS.Stage1.Thm3.Sec5.S1 S K₂ = CFSG.GH74.GLS.Stage1.Thm3.Sec5.S1 S K₁ := by
  ext s
  constructor
  · rintro ⟨hsS, hsN⟩
    exact ⟨hsS, mem_normalizer_swap hs.swap (hs.sylow.le hsS) hsN⟩
  · rintro ⟨hsS, hsN⟩
    exact ⟨hsS, mem_normalizer_swap hs (hs.sylow.le hsS) hsN⟩

theorem w7_ne_one (hII : II4_4_4_center) (h41 : Prop4_1) {w : G} (hT : Term7Out G z S q w) (hw : w ≠ 1)
    (hs : Std4 G z S K₁ K₂) (hLB : LBar z = imgBar z K₁ ⊔ imgBar z K₂) {t : G} (htS : t ∈ S)
    (ht2 : t * t = 1) (hSP : S = Pz S z ⊔ zpowers t) : False := by
  obtain ⟨Gs, iGs, fGs, z', t', w', S', E₁, E₂, σ, hz'o, hcenS', hz'S', hz'c, hD, hww, hσL, hσf,
    hσz⟩ := term7_data' hII h41 hT
  have hw'1 : w' ≠ 1 := fun h => hw (hww.1 h)
  have ht'1 : t' ≠ 1 := by
    intro h
    have := hD.t_ord
    rw [h, orderOf_one] at this
    omega
  have hz'1 : z' ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz'o
    omega
  have hYle : ∀ y ∈ zpowers t' ⊔ zpowers w', y ≠ 1 → y ∉ IVK.Ez z' := by
    intro y hy hy1 hyE
    have : y ∈ IVK.Ez z' ⊓ (zpowers t' ⊔ zpowers w') := ⟨hyE, hy⟩
    rw [hD.inter] at this
    exact hy1 (Subgroup.mem_bot.1 this)
  have htw1 : t' * w' ≠ 1 := by
    intro h
    have := (hD.w_fus hw'1).1
    rw [h] at this
    exact hz'1 (isConj_one_right.1 this.symm)
  have hmem_t : t' ∈ zpowers t' ⊔ zpowers w' := Subgroup.mem_sup_left (mem_zpowers t')
  have hmem_w : w' ∈ zpowers t' ⊔ zpowers w' := Subgroup.mem_sup_right (mem_zpowers w')
  have hmem_tw : t' * w' ∈ zpowers t' ⊔ zpowers w' := Subgroup.mul_mem_sup (mem_zpowers t') (mem_zpowers w')
  set a : ↥S := σ.symm ⟨t', hD.t_mem⟩ with ha
  set b : ↥S := σ.symm ⟨w', hD.w_mem⟩ with hb
  have hσa : ((σ a : ↥S') : Gs) = t' := by rw [ha, MulEquiv.apply_symm_apply]
  have hσb : ((σ b : ↥S') : Gs) = w' := by rw [hb, MulEquiv.apply_symm_apply]
  have hσab : ((σ (a * b) : ↥S') : Gs) = t' * w' := by rw [map_mul]; rw [hσa.symm, hσb.symm]; rfl
  have haL : (a : G) ∉ LC z := fun h => hYle t' hmem_t ht'1 (by rw [← hσa]; exact (hσL a).1 h)
  have hbL : (b : G) ∉ LC z := fun h => hYle w' hmem_w hw'1 (by rw [← hσb]; exact (hσL b).1 h)
  have habL : ((a * b : ↥S) : G) ∉ LC z := fun h =>
    hYle (t' * w') hmem_tw htw1 (by rw [← hσab]; exact (hσL (a * b)).1 h)
  have hPL : Pz S z ≤ LC z := Pz_le_LC hII hs hLB
  have hPn : S ≤ normalizer ((Pz S z : Subgroup G) : Set G) := S_le_normalizer_Pz hII hs
  have hzt : zpowers t ≤ normalizer ((Pz S z : Subgroup G) : Set G) :=
    (Subgroup.zpowers_le.2 htS).trans hPn
  have hmul := Subgroup.coe_mul_of_right_le_normalizer_left (Pz S z) (zpowers t) hzt
  have key : ∀ x : ↥S, (x : G) ∉ LC z → ∃ p ∈ Pz S z, (x : G) = p * t := by
    intro x hx
    have hx' : (x : G) ∈ ((Pz S z : Subgroup G) : Set G) * ((zpowers t : Subgroup G) : Set G) := by
      rw [← hmul, ← hSP]
      exact x.2
    obtain ⟨p, hp, y, hy, hpy⟩ := Set.mem_mul.1 hx'
    rcases eq_one_or_eq_of_mem_zpowers_sq ht2 hy with rfl | rfl
    · exact absurd (by rw [← hpy, mul_one]; exact hPL hp) hx
    · exact ⟨p, hp, hpy.symm⟩
  obtain ⟨p₁, hp₁, hpa⟩ := key a haL
  obtain ⟨p₂, hp₂, hpb⟩ := key b hbL
  apply habL
  have hab : ((a * b : ↥S) : G) = p₁ * (t * p₂ * t⁻¹) := by
    show (a : G) * (b : G) = _
    rw [hpa, hpb]
    calc p₁ * t * (p₂ * t) = p₁ * (t * p₂ * t⁻¹) * (t * t) := by group
      _ = p₁ * (t * p₂ * t⁻¹) := by rw [ht2, mul_one]
  rw [hab]
  exact hPL ((Pz S z).mul_mem hp₁ ((Subgroup.mem_normalizer_iff.1 (hPn htS) p₂).1 hp₂))

theorem induced_of_cfg (hII : II4_4_4_center) (hs : Std4 G z S K₁ K₂)
    {L₁ L₂ : Subgroup (CentralizerBar z)} (hpair : Stage1Pair G z S q L₁ L₂)
    (hsets : ({L₁, L₂} : Set (Subgroup (CentralizerBar z))) = {imgBar z K₁, imgBar z K₂})
    {w : G} (hwS : w ∈ S) (hwo : orderOf w = 2)
    (hS1 : CFSG.GH74.GLS.Stage1.Thm3.Sec5.S1 S K₁ = Pz S z ⊔ zpowers w)
    (hf : ∀ K ∈ ({K₁, K₂} : Set (Subgroup G)), ∃ (Fq : Type) (_ : Field Fq) (_ : Finite Fq),
      Nat.card Fq = q ∧ PGLQuot z w K Fq) :
    InducedPGL2 L₁ (SBar (CFSG.GH74.GLS.Stage2.Local.S1 S z) z) q ∧
      InducedPGL2 L₂ (SBar (CFSG.GH74.GLS.Stage2.Local.S1 S z) z) q := by
  classical
  have hM := m4_of_std hII hs
  have hcomps : {K : Subgroup (CentralizerBar z) | IsComponent K} = {imgBar z K₁, imgBar z K₂} :=
    hpair.comps.trans hsets
  have hLB : LBar z = imgBar z K₁ ⊔ imgBar z K₂ := by
    rcases Set.pair_eq_pair_iff.1 hsets with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← hpair.prod.1, h1, h2]
    · rw [← hpair.prod.1, h1, h2, sup_comm]
  have hA12 : imgBar z K₁ ≠ imgBar z K₂ := by
    rcases Set.pair_eq_pair_iff.1 hsets with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← h1, ← h2]
      exact hpair.ne
    · rw [← h1, ← h2]
      exact hpair.ne.symm
  have hSC : S ≤ Cz z := hs.sylow.le
  have hwC : w ∈ Cz z := hSC hwS
  have hw2 : w * w = 1 := by
    have := pow_orderOf_eq_one w
    rwa [hwo, pow_two] at this
  have hwN₁ : w ∈ normalizer (K₁ : Set G) := by
    have : w ∈ CFSG.GH74.GLS.Stage1.Thm3.Sec5.S1 S K₁ := by
      rw [hS1]
      exact Subgroup.mem_sup_right (mem_zpowers w)
    exact this.2
  have hS1₂ : CFSG.GH74.GLS.Stage1.Thm3.Sec5.S1 S K₂ = Pz S z ⊔ zpowers w :=
    (S1_swap_eq hs).trans hS1
  have hwN₂ : w ∈ normalizer (K₂ : Set G) := by
    have : w ∈ CFSG.GH74.GLS.Stage1.Thm3.Sec5.S1 S K₂ := by
      rw [hS1₂]
      exact Subgroup.mem_sup_right (mem_zpowers w)
    exact this.2
  have hwN : ∀ K, (K = K₁ ∨ K = K₂) → w ∈ normalizer (K : Set G) := by
    intro K hK
    rcases hK with h | h
    · rw [h]
      exact hwN₁
    · rw [h]
      exact hwN₂
  have hcomp : ∀ K, (K = K₁ ∨ K = K₂) → IsComponent (imgBar z K) ∧ imgBar z K ≤ LBar z := by
    intro K hK
    have hmem : imgBar z K ∈ ({imgBar z K₁, imgBar z K₂} : Set (Subgroup (CentralizerBar z))) := by
      rcases hK with h | h
      · rw [h]
        exact Or.inl rfl
      · rw [h]
        exact Or.inr rfl
    have hmemc : imgBar z K ∈ {K' : Subgroup (CentralizerBar z) | IsComponent K'} := by
      rw [hcomps]
      exact hmem
    refine ⟨hmemc, ?_⟩
    rw [hLB]
    rcases hK with h | h
    · rw [h]
      exact le_sup_left
    · rw [h]
      exact le_sup_right
  have hwS1 : w ∈ CFSG.GH74.GLS.Stage2.Local.S1 S z := by
    rw [mem_localS1_iff hwC]
    refine ⟨hwS, fun K' hK' hKL => ?_⟩
    have hmem : K' ∈ ({imgBar z K₁, imgBar z K₂} : Set (Subgroup (CentralizerBar z))) := by
      rw [← hcomps]
      exact hK'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h | h
    · rw [h]
      exact bar_mem_normalizer hM.K₁_le hwC hwN₁
    · rw [h]
      exact bar_mem_normalizer hM.K₂_le hwC hwN₂
  set T : Subgroup (CentralizerBar z) := SBar (CFSG.GH74.GLS.Stage2.Local.S1 S z) z with hTdef
  have hTN : ∀ K, (K = K₁ ∨ K = K₂) →
      T ≤ normalizer ((imgBar z K : Subgroup (CentralizerBar z)) : Set (CentralizerBar z)) := by
    intro K hK x hx
    obtain ⟨c, hc, rfl⟩ := hx
    have hcS1 : (c : G) ∈ CFSG.GH74.GLS.Stage2.Local.S1 S z := Subgroup.mem_subgroupOf.1 hc
    exact ((mem_localS1_iff c.2).1 hcS1).2 _ (hcomp K hK).1 (hcomp K hK).2
  have hwT : piC z ⟨w, hwC⟩ ∈ T := ⟨⟨w, hwC⟩, Subgroup.mem_subgroupOf.2 hwS1, rfl⟩
  have hTle : ∀ K, (K = K₁ ∨ K = K₂) → T ≤ (imgBar z K ⊔ barOf z (zpowers w)) ⊔
      centralizer ((imgBar z K : Subgroup (CentralizerBar z)) : Set (CentralizerBar z)) := by
    intro K hK x hx
    obtain ⟨c, hc, rfl⟩ := hx
    have hcS1 : (c : G) ∈ CFSG.GH74.GLS.Stage2.Local.S1 S z := Subgroup.mem_subgroupOf.1 hc
    obtain ⟨hcS, hcn⟩ := (mem_localS1_iff c.2).1 hcS1
    rcases hK with h | h
    · rw [h]
      exact bar_S1_le hII hs hA12 hwS hw2 hwN₂ hS1 hcS
        (hcn _ (hcomp K₁ (Or.inl rfl)).1 (hcomp K₁ (Or.inl rfl)).2)
    · rw [h]
      exact bar_S1_le hII hs.swap hA12.symm hwS hw2 hwN₁ hS1₂ hcS
        (hcn _ (hcomp K₂ (Or.inr rfl)).1 (hcomp K₂ (Or.inr rfl)).2)
  have hmain : ∀ K, (K = K₁ ∨ K = K₂) → HasSL2Model ↥(imgBar z K) (fun r => r = q) →
      InducedPGL2 (imgBar z K) T q := by
    intro K hK hL
    have hKmem : K ∈ ({K₁, K₂} : Set (Subgroup G)) := by
      rcases hK with h | h
      · rw [h]
        exact Or.inl rfl
      · rw [h]
        exact Or.inr rfl
    obtain ⟨Fq, iF, fF, hq, hpgl⟩ := hf K hKmem
    exact inducedPGL2_of_pglQuot hII hs hK hpair.odd hpair.gt3 hL hwC hw2 (hwN K hK) hq hpgl
      (hTN K hK) hwT (hTle K hK)
  rcases Set.pair_eq_pair_iff.1 hsets with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
    exact ⟨hmain K₁ (Or.inl rfl) (by rw [← h1]; exact hpair.sl₁),
      hmain K₂ (Or.inr rfl) (by rw [← h2]; exact hpair.sl₂)⟩
  · rw [h1, h2]
    exact ⟨hmain K₂ (Or.inr rfl) (by rw [← h1]; exact hpair.sl₁),
      hmain K₁ (Or.inl rfl) (by rw [← h2]; exact hpair.sl₂)⟩

theorem l4nfInduced_proved (hII : II4_4_4_center) (h41 : Prop4_1) (h61 : Prop6_1) (h66 : Prop6_6)
    (hpnf : P_normal_four) (hL44 : Lemma4_4) (hL45 : Lemma4_5) (h72 : Prop7_2) : L4NFInduced := by
  intro G _ _ z S q w ε hcen hT hw hε L₁ L₂ hpair
  have hnf := nonfused_of_term7 hII h41 hT
  have hT' := hT
  obtain ⟨K₁, K₂, hstd, hodd, h5, hK₁, hK₂, hT7⟩ := hT'
  obtain ⟨t, u, hcfg⟩ := cfg7_of_std hII h41 h61 h66 hpnf hL44 hL45 hstd hnf hodd h5 hK₁ hK₂
  obtain ⟨w₇, hw₇, hde₇⟩ := h72 G z S K₁ K₂ t u q hcfg
  have hsets : ({L₁, L₂} : Set (Subgroup (CentralizerBar z))) = {imgBar z K₁, imgBar z K₂} :=
    hpair.comps.symm.trans (comps_of_std4 hII h41 hstd)
  have hLB := LBar_eq_imgBar hII h41 hstd
  obtain ⟨hwS, hwo, -, ⟨-, hSPY⟩, hS1, -, hf⟩ := hw₇
  have ht2 : t * t = 1 := mul_self_of_isConj hstd.orderOf_z hde₇.1.1
  have hw71 : w₇ ≠ 1 := by
    intro h1
    have hY : Ysub t w₇ = zpowers t := by
      rw [h1]
      simp [Ysub]
    have hSP : S = Pz S z ⊔ zpowers t := by
      have := hSPY
      rwa [hY] at this
    exact w7_ne_one hII h41 hT hw hstd hLB hcfg.ch.t_mem ht2 hSP
  exact induced_of_cfg hII hstd hpair hsets hwS (hwo.resolve_left hw71) hS1 (hf hw71)

end Concrete

end CFSG.GH74.GLS.Stage1.Main
