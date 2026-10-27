module

public import CFSG.LocalAnalysis.GLTheoremA.S8.Lemma88
public import CFSG.LocalAnalysis.GLTheoremA.S6.InputsAlt72

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal (Input18_3_4)
open CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement

namespace S8

namespace L89

variable {G : Type} [Group G] [Finite G]

abbrev cfgJa (p : ℕ) (I : Subgroup G) (a : G) : Subgroup G := closureIn I (GLAPLayer p (cx a))

@[expose] def isSp8of2 : TauCeti.CFSGIndex → Prop :=
  onLie fun
    | .B 4 q => q.card = 2
    | _ => False

@[expose] def isU5of2 : TauCeti.CFSGIndex → Prop :=
  onLie fun
    | .twistedA 4 q => q.card = 2
    | _ => False

@[expose] def isU6of2 : TauCeti.CFSGIndex → Prop :=
  onLie fun
    | .twistedA 5 q => q.card = 2
    | _ => False

@[expose] def i1431List (i : TauCeti.CFSGIndex) : Prop :=
  sporIs .Co2 i ∨ isSp8of2 i ∨ isD4of 2 i ∨ isU5of2 i ∨ isU6of2 i ∨ isU4of 8 i

@[expose] def i1431List2 (i : TauCeti.CFSGIndex) : Prop :=
  sporIs .Co2 i ∨ isSp8of2 i ∨ isU6of2 i

@[expose] def I112NormAt (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  p.Prime → p ≠ 2 → ∀ X B L : Subgroup G, CFSG.Open.IsKGroup ↥X → GLAIsBmax p B → B ≤ X →
    GLAPComponent p X L → (∃ E : Subgroup G, E ≤ L ∧ IsElemAbelian p E ∧ p ^ 3 ≤ Nat.card E) →
    B ≤ Subgroup.normalizer (L : Set G)

@[expose] def I112RankAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ J : Subgroup G, catalogIs (PQuot 3 J) weakExcIndex → ∀ E : Subgroup G, E ≤ J → IsElemAbelian 3 E →
    Nat.card E ≤ 3 ^ 2

@[expose] def I1420Concl (row : Row) (p : ℕ) (J : Subgroup G) : Prop :=
  match row with
  | .suz => catalogIs (PSimple p J) (sporIs .Suz) ∨ IsTypeWithCenter p J (sporIs .Fi22) 3
  | .suzh => catalogIs (PSimple p J) (sporIs .Suz) ∨ catalogIs (PSimple p J) (sporIs .Co1)
  | _ => catalogIs (PSimple p J) (sporIs row.name)

@[expose] def I1420CfgAt (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  ∀ (x : G) (L : Subgroup G) (row : Row) (c : SporCfg G p x L row), orderOf x = p →
    GLAPComponent p (cx x) L → RowL row p L →
    (row = .ly ∨ row = .co1 ∨ row = .suz ∨ row = .suzh ∨ row = .m3 ∨ row = .m5) →
    ∀ a ∈ c.D, a ≠ 1 → CFSG.Open.IsKGroup ↥(cx a) → ∀ J : Subgroup G, GLAPComponent p (cx a) J →
      GLAPComponent p (J ⊓ Subgroup.centralizer (c.D : Set G)) (cfgI p L c.D) →
      ¬ J ≤ cfgI p L c.D ⊔ GLAPPrimeCoreOf p J → I1420Concl row p J

@[expose] def I1016At89 (G : Type) [Group G] [Finite G] : Prop :=
  (∀ X J : Subgroup G, CFSG.Open.IsKGroup ↥X → GLAPComponent 3 X J →
      IsTypeWithCenter 3 J (sporIs .Fi22) 3 →
      ∃ E V : Subgroup G, E ≤ J ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 5 ∧ V ≤ J ∧ IsPGroup 2 V ∧
        V ≠ ⊥ ∧ E ≤ Subgroup.normalizer (V : Set G)) ∧
  (∀ X J : Subgroup G, CFSG.Open.IsKGroup ↥X → GLAPComponent 3 X J →
      catalogIs (PSimple 3 J) (sporIs .Co1) →
      ∃ E V : Subgroup G, E ≤ J ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 ∧ E ⊓ centerOf J = ⊥ ∧
        V ≤ J ∧ IsPGroup 2 V ∧ V ≠ ⊥ ∧ E ≤ Subgroup.normalizer (V : Set G))

structure Case2Ctx (a y : G) (J I : Subgroup G) : Prop where
  ha : orderOf a = 3
  hK : CFSG.Open.IsKGroup ↥(cx a)
  hya : y ∈ cx a
  hy : orderOf y = 3
  hyn : y ∉ Subgroup.zpowers a
  hJ : GLAPComponent 3 (cx a) J
  hyJ : y ∈ Subgroup.normalizer (J : Set G)
  hI : GLAPComponent 3 (J ⊓ cx y) I
  hIt : IsTypeWithCenter 3 I isPSp43 1
  hJI : ¬ J ≤ I ⊔ GLAPPrimeCoreOf 3 J
  hrank : GLATwoLocalRank 3 G ≤ 4

structure Case2Local (y : G) (J K T : Subgroup G) : Prop where
  hKy : K ≤ cx y
  hKJ : K ≤ J
  hKt : IsTypeWithCenter 3 K isA6 1
  hKl : ∃ H : Subgroup G, K = GLAPLayer 3 H
  hT2 : IsPGroup 2 T
  hT1 : T ≠ ⊥
  hTJ : T ≤ Subgroup.normalizer (J : Set G)
  hfaith : T ⊓ centModSubgroup 3 J = ⊥
  hinner : ∀ t ∈ T, InducesInnerMod 3 J t
  hKT : K ≤ Subgroup.normalizer (T : Set G)
  hyT : y ∈ Subgroup.normalizer (T : Set G)

@[expose] def I1431At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (a y : G) (J I K T : Subgroup G), Case2Ctx a y J I →
    catalogIs (PSimple 3 J) i1431List ∧ (Case2Local y J K T → catalogIs (PSimple 3 J) i1431List2)

@[expose] def I71InnerAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X J T D : Subgroup G), CFSG.Open.IsKGroup ↥X → GLAPComponent 3 X J →
    catalogIs (PSimple 3 J) i1431List → IsPGroup 2 T → T ≤ Subgroup.normalizer (J : Set G) →
    IsPGroup 3 D → D ≤ Subgroup.normalizer (J : Set G) → D ≤ Subgroup.normalizer (T : Set G) →
    T ≤ ⁅T, D⁆ → ∀ t ∈ T, InducesInnerMod 3 J t

@[expose] def I2016At (G : Type) [Group G] [Finite G] : Prop :=
  (∀ (a y : G) (J I K T : Subgroup G), Case2Ctx a y J I → Case2Local y J K T →
      ¬ catalogIs (PSimple 3 J) isSp8of2) ∧
  (∀ (a y : G) (J I K T : Subgroup G), Case2Ctx a y J I → Case2Local y J K T →
      catalogIs (PSimple 3 J) isU6of2 →
      ∃ W : Subgroup G, W ≤ J ∧ IsPGroup 2 W ∧ ¬ W ≤ GLAPPrimeCoreOf 3 J ∧
        I ⊔ Subgroup.zpowers y ≤ Subgroup.normalizer ((W ⊔ GLAPPrimeCoreOf 3 J : Subgroup G) : Set G))

@[expose] def I1432At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X K B I U : Subgroup G) (b y : G), CFSG.Open.IsKGroup ↥X → GLAPComponent 3 X K →
    GLAIsBmax 3 B → B ≤ X → U ≤ X → U ≠ ⊥ → IsPGroup 2 U → B ≤ Subgroup.normalizer (U : Set G) →
    b ∈ B → b ≠ 1 → CentMod 3 K b → y ∈ B → GLAPComponent 3 (K ⊓ cx y) I →
    ¬ K ≤ I ⊔ GLAPPrimeCoreOf 3 K →
    (IsTypeWithCenter 3 I (isD4of 3) 1 → catalogIs (PSimple 3 K) (sporIs .Fi24Prime)) ∧
    (IsTypeWithCenter 3 I (isG2of 3) 1 → GLATwoLocalRank 3 G ≤ 4 →
      catalogIs (PSimple 3 K) (sporIs .Th))

section Elementary

variable {p : ℕ}

theorem isElemAbelian_gLBConj {E : Subgroup G} (hE : IsElemAbelian p E) (g : G) :
    IsElemAbelian p (GLBConj g E) ∧ Nat.card (GLBConj g E) = Nat.card E := by
  refine ⟨⟨⟨⟨fun u v => ?_⟩⟩, fun y hy => ?_⟩, ?_⟩
  · obtain ⟨u, hu⟩ := u
    obtain ⟨v, hv⟩ := v
    apply Subtype.ext
    rw [mem_gLBConj] at hu hv
    have h := isElemAbelian_commute hE hu hv
    show u * v = v * u
    have h2 : g * (u * v) * g⁻¹ = g * (v * u) * g⁻¹ := by
      calc g * (u * v) * g⁻¹ = (g * u * g⁻¹) * (g * v * g⁻¹) := by group
        _ = (g * v * g⁻¹) * (g * u * g⁻¹) := h
        _ = g * (v * u) * g⁻¹ := by group
    simpa using h2
  · rw [mem_gLBConj] at hy
    have h := hE.2 _ hy
    rw [conj_pow, conj_eq_one_iff] at h
    exact h
  · unfold GLBConj
    exact Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective

theorem mem_normalizer_of_conj_le {g : G} {H : Subgroup G} (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) :
    g ∈ Subgroup.normalizer (H : Set G) := by
  have hle : H.map (MulAut.conj g).toMonoidHom ≤ H := by
    rintro _ ⟨y, hy, rfl⟩
    exact h y hy
  have hcard : Nat.card H ≤ Nat.card (H.map (MulAut.conj g).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have heq := Subgroup.eq_of_le_of_card_ge hle hcard
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨h y, fun hy => ?_⟩
  rw [← heq] at hy
  obtain ⟨z, hz, hzy⟩ := hy
  have hzy' : g * z * g⁻¹ = g * y * g⁻¹ := hzy
  have : z = y := by simpa using hzy'
  rw [← this]
  exact hz

theorem normalizer_le_normalizer_centMod (J : Subgroup G) :
    Subgroup.normalizer (J : Set G) ≤ Subgroup.normalizer (centModSubgroup p J : Set G) :=
  fun _ hg => mem_normalizer_of_conj_le fun _ ha => S3.conj_mem_centModSubgroup hg ha

theorem commutator_le_of_le_normalizer {H A : Subgroup G} (hA : A ≤ Subgroup.normalizer (H : Set G)) :
    ⁅H, A⁆ ≤ H := by
  rw [Subgroup.commutator_le]
  intro h hh a ha
  rw [commutatorElement_def]
  have h1 : a * h⁻¹ * a⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.1 (hA ha) _).1 (H.inv_mem hh)
  have h2 : h * a * h⁻¹ * a⁻¹ = h * (a * h⁻¹ * a⁻¹) := by group
  rw [h2]
  exact H.mul_mem hh h1

theorem closureIn_eq_iSup_gLBConj (I H : Subgroup G) :
    closureIn I H = ⨆ g ∈ H, GLBConj g I := by
  unfold closureIn
  apply le_antisymm
  · refine iSup₂_le fun a ha => ?_
    have : I.map (MulAut.conj a).toMonoidHom = GLBConj a⁻¹ I := by
      unfold GLBConj
      rw [inv_inv]
    rw [this]
    exact le_iSup₂_of_le a⁻¹ (H.inv_mem ha) le_rfl
  · refine iSup₂_le fun g hg => ?_
    unfold GLBConj
    exact le_iSup₂_of_le g⁻¹ (H.inv_mem hg) le_rfl

theorem rank_contra (hp : p.Prime) {B E H : Subgroup G} (hB : GLAIsBmax p B) (hE : IsElemAbelian p E)
    (hbig : Nat.card B < Nat.card E) (hEH : E ≤ Subgroup.normalizer (H : Set G))
    (hcop : Nat.Coprime p (Nat.card H)) (h2 : 2 ∣ Nat.card H) : False := by
  obtain ⟨S, -, hS2, hSne, hES, -⟩ := S3.exists_invariant_sylow hp Nat.prime_two
    (isPGroup_of_isElemAbelian hE) hEH hcop h2
  have h1 := card_le_pow_glaTwoLocalRank hp hE hSne hS2 hES
  rw [← hB.2.1] at h1
  omega

theorem no_centMod_two (hp : p.Prime) (hp2 : p ≠ 2) {B E I D J W : Subgroup G} {a : G}
    (hB : GLAIsBmax p B) (hE : IsElemAbelian p E) (hbig : Nat.card B < Nat.card E) (hEID : E ≤ I ⊔ D)
    (hIJ : I ≤ J) (hJ : GLAPComponent p (cx a) J) (hDa : D ≤ cx a) (hWa : W ≤ cx a)
    (hW2 : IsPGroup 2 W) (hDW : D ≤ Subgroup.normalizer (W : Set G))
    (hWJ : W ≤ centModSubgroup p J) : W = ⊥ := by
  by_contra hW1
  have hWO : W ≤ Subgroup.normalizer (GLAPPrimeCoreOf p (cx a) : Set G) :=
    hWa.trans (le_normalizer_glaPPrimeCoreOf p (cx a))
  have hOp : ¬ p ∣ Nat.card (GLAPPrimeCoreOf p (cx a)) :=
    (Nat.Prime.coprime_iff_not_dvd hp).1 (i183_coprime_card_glaPPrimeCoreOf hp (cx a))
  have hWp : ¬ p ∣ Nat.card W :=
    (Nat.Prime.coprime_iff_not_dvd hp).1 (coprime_card_of_two hp hp2 hW2)
  have hcop : Nat.Coprime p (Nat.card (GLAPPrimeCoreOf p (cx a) ⊔ W : Subgroup G)) :=
    (Nat.Prime.coprime_iff_not_dvd hp).2 (not_dvd_card_sup_of_le_normalizer hp hWO hOp hWp)
  have h2 : 2 ∣ Nat.card (GLAPPrimeCoreOf p (cx a) ⊔ W : Subgroup G) :=
    (two_dvd_card_of_two hW2 hW1).trans (Subgroup.card_dvd_of_le le_sup_right)
  have hDH : D ≤ Subgroup.normalizer ((GLAPPrimeCoreOf p (cx a) ⊔ W : Subgroup G) : Set G) :=
    le_normalizer_sup' (hDa.trans (le_normalizer_glaPPrimeCoreOf p (cx a))) hDW
  have hIH : I ≤ Subgroup.normalizer ((GLAPPrimeCoreOf p (cx a) ⊔ W : Subgroup G) : Set G) := by
    intro i hi
    have hiO : i ∈ Subgroup.normalizer (GLAPPrimeCoreOf p (cx a) : Set G) :=
      le_normalizer_glaPPrimeCoreOf p (cx a) (hJ.1 (hIJ hi))
    have key : (GLAPPrimeCoreOf p (cx a) ⊔ W).map (MulAut.conj i).toMonoidHom ≤
        GLAPPrimeCoreOf p (cx a) ⊔ W := by
      rw [Subgroup.map_sup]
      apply sup_le
      · rintro _ ⟨o, ho, rfl⟩
        exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.1 hiO o).1 ho)
      · rintro _ ⟨w, hw, rfl⟩
        have hcm : ⁅i, w⁆ ∈ GLAPPrimeCoreOf p (cx a) :=
          glaPPrimeCoreOf_le_of_isSubnormal hp hJ.2.1 ((hWJ hw).2 i (hIJ hi))
        have he : (MulAut.conj i).toMonoidHom w = ⁅i, w⁆ * w := by
          show i * w * i⁻¹ = ⁅i, w⁆ * w
          rw [commutatorElement_def]
          group
        rw [he]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hcm) (Subgroup.mem_sup_right hw)
    exact mem_normalizer_of_conj_le fun y hy => key ⟨y, hy, rfl⟩
  exact rank_contra hp hB hE hbig (hEID.trans (sup_le hIH hDH)) hcop h2

theorem twoLocalRank_le_pRank (hp : p.Prime) {B X : Subgroup G} (hB : GLAIsBmax p B) (hBX : B ≤ X) :
    GLATwoLocalRank p ↥X ≤ CFSG.Open.pRank p B := by
  refine le_trans ?_ (CFSG.SectionRank.le_pRank hp.one_lt le_rfl hB.1 hB.2.1)
  unfold GLATwoLocalRank CFSG.Open.twoLocalPrimeRank
  refine csSup_le' ?_
  rintro k ⟨H, ⟨P, hP1, hP2, rfl⟩, rfl⟩
  have hPG1 : P.map X.subtype ≠ ⊥ := fun h => hP1 ((Subgroup.map_eq_bot_iff_of_injective P X.subtype_injective).1 h)
  have hPG2 : IsPGroup 2 (P.map X.subtype) := hP2.map X.subtype
  have hle : (Subgroup.normalizer (P : Set ↥X)).map X.subtype ≤
      Subgroup.normalizer ((P.map X.subtype : Subgroup G) : Set G) := by
    rintro _ ⟨h, hh, rfl⟩
    apply mem_normalizer_of_conj_le
    rintro _ ⟨q, hq, rfl⟩
    refine ⟨h * q * h⁻¹, (Subgroup.mem_normalizer_iff.1 hh q).1 hq, ?_⟩
    simp
  exact (CFSG.SectionRank.pRank_le_map hp.one_lt X.subtype X.subtype_injective _).trans
    ((CFSG.SectionRank.pRank_mono hp.one_lt hle).trans (pRank_normalizer_le hp.one_lt hPG1 hPG2))

end Elementary

section Cfg

variable {p : ℕ} {x : G} {L : Subgroup G} {row : Row}

theorem cfg_twoLocalRank (hp : p.Prime) (c : SporCfg G p x L row) : GLATwoLocalRank p G = row.rank :=
  Nat.pow_right_injective hp.two_le (c.hBs.2.1.symm.trans c.hBsCard)

theorem cfg_centralizer_D_le_cx (c : SporCfg G p x L row) :
    Subgroup.centralizer (c.D : Set G) ≤ cx x := centralizer_le_cx_of_mem c.hD.2.2.2

theorem cfgI_comp_cen (hp : p.Prime) (hL : GLAPComponent p (cx x) L) (c : SporCfg G p x L row)
    (hI : GLAPComponent p (L ⊓ Subgroup.centralizer (c.D : Set G)) (cfgI p L c.D)) :
    GLAPComponent p (Subgroup.centralizer (c.D : Set G)) (cfgI p L c.D) := by
  have hsn := isSubnormal_inf hL.2.1 (Subgroup.centralizer (c.D : Set G))
  rw [inf_eq_right.2 (cfg_centralizer_D_le_cx c)] at hsn
  exact glaPComponent_of_isSubnormal' hp hsn hI

theorem cfgI_big (hp : p.Prime) (c : SporCfg G p x L row)
    (hE : ∃ E : Subgroup G, E ≤ cfgI p L c.D ∧ IsElemAbelian p E ∧
      p ^ (row.rank - 1) * Nat.card (E ⊓ centerOf (cfgI p L c.D) : Subgroup G) ≤ Nat.card E) :
    ∃ E : Subgroup G, E ≤ cfgI p L c.D ∧ IsElemAbelian p E ∧ p ^ 3 ≤ Nat.card E := by
  obtain ⟨E, hEI, hE, hbig⟩ := hE
  refine ⟨E, hEI, hE, ?_⟩
  have h1 : 1 ≤ Nat.card (E ⊓ centerOf (cfgI p L c.D) : Subgroup G) := Nat.card_pos
  have h2 : p ^ 3 ≤ p ^ (row.rank - 1) :=
    Nat.pow_le_pow_right hp.pos (by have := four_le_rank row; omega)
  calc p ^ 3 ≤ p ^ (row.rank - 1) := h2
    _ = p ^ (row.rank - 1) * 1 := (mul_one _).symm
    _ ≤ p ^ (row.rank - 1) * Nat.card (E ⊓ centerOf (cfgI p L c.D) : Subgroup G) :=
        Nat.mul_le_mul_left _ h1
    _ ≤ Nat.card E := hbig

theorem I_le_cfgJa (p : ℕ) (I : Subgroup G) (a : G) : I ≤ cfgJa p I a := by
  have h : I = I.map (MulAut.conj (1 : G)).toMonoidHom := by
    rw [map_one]
    exact (Subgroup.map_id I).symm
  conv_lhs => rw [h]
  exact le_iSup₂_of_le (1 : G) (Subgroup.one_mem _) le_rfl

end Cfg

section Ja

variable {p : ℕ} {x : G} {L : Subgroup G} {row : Row}

theorem orbit_contra (hc : S8Ctx G p) (h112s : I112StarAt G p) (h112r : I112RankAt G)
    (hcfg : CfgIAt G p) (hx : orderOf x = p) (hL : GLAPComponent p (cx x) L) (hrow : RowL row p L)
    (c : SporCfg G p x L row) {a : G} (ha : a ∈ c.D) (ha1 : a ≠ 1) {J₁ : Subgroup G}
    (hJ₁ : GLAPComponent p (cx a) J₁) (hIJ : cfgI p L c.D ≤ closureIn J₁ c.Bs) {e : G} (he : e ∈ c.D)
    (heN : e ∉ Subgroup.normalizer (J₁ : Set G)) : False := by
  have hp := hc.ctx.prime
  obtain ⟨hIc, hIE⟩ := hcfg x L row c hx hL hrow
  obtain ⟨E, hEI, hE, hE3⟩ := cfgI_big hp c hIE
  have hBsa := cfg_Bs_le_cx_of_mem c (c.hD.1 ha)
  have hnot : ¬ c.Bs ≤ Subgroup.normalizer (J₁ : Set G) := fun h => heN (h (c.hD.1 he))
  obtain ⟨hp3, hcomp⟩ := h112s hp hc.ctx.odd (cx a) c.Bs J₁ (isKGroup_cx hc.ctx ha1) hBsa c.hBs.1
    (twoLocalRank_le_pRank hp c.hBs hBsa) hJ₁ hnot
  have hea : e ∉ Subgroup.zpowers a := fun h => heN (zpowers_le_normalizer_of_le_cx hJ₁.1 h)
  have hcen := centralizer_eq_inf hp c.hD.2.1 c.hD.2.2.1 ha ha1 he hea
  have hclo : closureIn J₁ c.Bs ≤ cx a := by
    unfold closureIn
    refine iSup₂_le fun b hb => ?_
    rintro _ ⟨l, hl, rfl⟩
    show b * l * b⁻¹ ∈ cx a
    exact (cx a).mul_mem ((cx a).mul_mem (hBsa hb) (hJ₁.1 hl)) ((cx a).inv_mem (hBsa hb))
  have hIcomp : GLAPComponent p (closureIn J₁ c.Bs ⊓ cx e) (cfgI p L c.D) := by
    refine glaPComponent_of_le hp (cfgI_comp_cen hp hL c hIc)
      (le_inf hIJ ((cfg_I_le_centralizer c).trans (centralizer_le_cx_of_mem he))) ?_
    rw [hcen]
    exact inf_le_inf_right _ hclo
  have hw := hcomp e (c.hD.1 he) heN (cfgI p L c.D) hIcomp
  subst hp3
  have h9 := h112r (cfgI 3 L c.D) hw E hEI hE
  have : 3 ^ 3 ≤ 3 ^ 2 := hE3.trans h9
  norm_num at this

theorem ja_single (hc : S8Ctx G p) (h183 : Input18_3_4) (h112s : I112StarAt G p) (h112r : I112RankAt G)
    (hcfg : CfgIAt G p) (hx : orderOf x = p) (hL : GLAPComponent p (cx x) L) (hrow : RowL row p L)
    (c : SporCfg G p x L row) {a : G} (ha : a ∈ c.D) (ha1 : a ≠ 1) :
    GLAPComponent p (cx a) (cfgJa p (cfgI p L c.D) a) := by
  have hp := hc.ctx.prime
  obtain ⟨hIc, -⟩ := hcfg x L row c hx hL hrow
  have hIcen := cfgI_comp_cen hp hL c hIc
  have hDa : c.D ≤ cx a := (cfg_D_le_centralizer_D c).trans (centralizer_le_cx_of_mem ha)
  have hX : cx a ⊓ Subgroup.centralizer (c.D : Set G) = Subgroup.centralizer (c.D : Set G) :=
    inf_eq_right.2 (centralizer_le_cx_of_mem ha)
  obtain ⟨𝒞, h𝒞c, h𝒞sup, -, h𝒞tr⟩ := h183 G (cx a) (isKGroup_cx hc.ctx ha1) p hp c.D hDa c.hD.2.1
    (cfgI p L c.D) (by rw [hX]; exact hIcen)
  have hJa : cfgJa p (cfgI p L c.D) a = ⨆ L' ∈ 𝒞, L' := by
    rw [h𝒞sup]
    exact closureIn_eq_iSup_gLBConj _ _
  have hIJ := I_le_cfgJa p (cfgI p L c.D) a
  obtain ⟨L₁, hL₁⟩ : 𝒞.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have h0 : cfgJa p (cfgI p L c.D) a = ⊥ := by
      rw [hJa, hne]
      simp
    exact glaPComponent_ne_bot' hIc (le_bot_iff.1 (h0 ▸ hIJ))
  have hIL : cfgI p L c.D ≤ closureIn L₁ c.Bs := by
    refine hIJ.trans ?_
    rw [hJa]
    refine iSup₂_le fun L' hL' => ?_
    obtain ⟨e', he', rfl⟩ := h𝒞tr L₁ hL₁ L' hL'
    unfold GLBConj closureIn
    exact le_iSup₂_of_le e'⁻¹ (c.Bs.inv_mem (c.hD.1 he')) le_rfl
  have hall : ∀ L' ∈ 𝒞, L' = L₁ := by
    intro L' hL'
    obtain ⟨e, he, rfl⟩ := h𝒞tr L₁ hL₁ L' hL'
    by_contra hne
    exact orbit_contra hc h112s h112r hcfg hx hL hrow c ha ha1 (h𝒞c L₁ hL₁) hIL he
      (fun h => hne (mem_normalizer_iff_gLBConj_eq.1 h))
  have heq : cfgJa p (cfgI p L c.D) a = L₁ := by
    rw [hJa]
    exact le_antisymm (iSup₂_le fun L' hL' => (hall L' hL').le) (le_iSup₂_of_le L₁ hL₁ le_rfl)
  rw [heq]
  exact h𝒞c L₁ hL₁

theorem ja_setup (hc : S8Ctx G p) (h183 : Input18_3_4) (h112s : I112StarAt G p) (h112r : I112RankAt G)
    (h112n : I112NormAt G p) (hcfg : CfgIAt G p) (hx : orderOf x = p) (hL : GLAPComponent p (cx x) L)
    (hrow : RowL row p L) (c : SporCfg G p x L row) {a : G} (ha : a ∈ c.D) (ha1 : a ≠ 1) :
    GLAPComponent p (cx a) (cfgJa p (cfgI p L c.D) a) ∧
      c.Bs ≤ Subgroup.normalizer (cfgJa p (cfgI p L c.D) a : Set G) ∧
      GLAPComponent p (cfgJa p (cfgI p L c.D) a ⊓ Subgroup.centralizer (c.D : Set G)) (cfgI p L c.D) := by
  have hp := hc.ctx.prime
  have hJ := ja_single hc h183 h112s h112r hcfg hx hL hrow c ha ha1
  obtain ⟨hIc, hIE⟩ := hcfg x L row c hx hL hrow
  obtain ⟨E, hEI, hE, hE3⟩ := cfgI_big hp c hIE
  have hIJ := I_le_cfgJa p (cfgI p L c.D) a
  refine ⟨hJ, ?_, ?_⟩
  · exact h112n hp hc.ctx.odd (cx a) c.Bs _ (isKGroup_cx hc.ctx ha1) c.hBs
      (cfg_Bs_le_cx_of_mem c (c.hD.1 ha)) hJ ⟨E, hEI.trans hIJ, hE, hE3⟩
  · exact glaPComponent_of_le hp (cfgI_comp_cen hp hL c hIc) (le_inf hIJ (cfg_I_le_centralizer c))
      inf_le_right

end Ja

section Para1

variable {p : ℕ} {x : G} {L : Subgroup G} {row : Row}

theorem tstar_facts (hp : p.Prime) (hp2 : p ≠ 2) (c : SporCfg G p x L row) {Q : Subgroup G}
    (hQ2 : IsPGroup 2 Q) (hQn : cfgK p x L c.D c.R ⊔ c.Bs ≤ Subgroup.normalizer (Q : Set G))
    (hQD : ¬ Q ≤ Subgroup.centralizer (c.D : Set G)) :
    ⁅Q, c.D⁆ ≤ Q ∧ ⁅Q, c.D⁆ ≠ ⊥ ∧ ⁅Q, c.D⁆ ≤ ⁅⁅Q, c.D⁆, c.D⁆ ∧
      cfgK p x L c.D c.R ⊔ c.Bs ≤ Subgroup.normalizer ((⁅Q, c.D⁆ : Subgroup G) : Set G) := by
  have hDQ : c.D ≤ Subgroup.normalizer (Q : Set G) := ((cfg_D_le_Bs c).trans le_sup_right).trans hQn
  refine ⟨commutator_le_of_le_normalizer hDQ, fun h => hQD ?_, ?_, ?_⟩
  · rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h
    exact h
  · have hcop : Nat.Coprime (Nat.card c.D) (Nat.card Q) := by
      rw [c.hD.2.2.1]
      exact Nat.Coprime.pow_left 2 (coprime_card_of_two hp hp2 hQ2)
    have hsolv : Group.IsSolvable ↥Q := by
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      haveI := hQ2.isNilpotent
      infer_instance
    rw [GL83.commutator_double_eq_self c.D Q hDQ hcop hsolv]
  · exact le_normalizer_commutator' hQn
      ((cfg_KB_le_centralizer_D c).trans (Subgroup.centralizer_le_normalizer _))

theorem tstar_le_normalizer (hc : S8Ctx G p) (h112n : I112NormAt G p) (hcfg : CfgIAt G p)
    (hx : orderOf x = p) (hL : GLAPComponent p (cx x) L) (hrow : RowL row p L) (c : SporCfg G p x L row)
    {a : G} (ha : a ∈ c.D) (ha1 : a ≠ 1) {J T : Subgroup G} (hJ : GLAPComponent p (cx a) J)
    (hIJ : cfgI p L c.D ≤ J) (hTa : T ≤ cx a) (hTD : T ≤ ⁅T, c.D⁆) :
    T ≤ Subgroup.normalizer (J : Set G) := by
  have hp := hc.ctx.prime
  obtain ⟨-, hIE⟩ := hcfg x L row c hx hL hrow
  obtain ⟨E, hEI, hE, hE3⟩ := cfgI_big hp c hIE
  refine S3.normalizes_of_comm (A := c.D) (fun t ht => ?_) hTD
  have hcx : GLBConj t (cx a) = cx a :=
    mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer (hTa ht))
  have hJt : GLAPComponent p (cx a) (GLBConj t J) := by
    have h := glaPComponent_gLBConj hJ t
    rwa [hcx] at h
  obtain ⟨hEt, hEtc⟩ := isElemAbelian_gLBConj hE t
  have hEtJ : GLBConj t E ≤ GLBConj t J := by
    unfold GLBConj
    exact Subgroup.map_mono (hEI.trans hIJ)
  exact (cfg_D_le_Bs c).trans (h112n hp hc.ctx.odd (cx a) c.Bs (GLBConj t J) (isKGroup_cx hc.ctx ha1) c.hBs
    (cfg_Bs_le_cx_of_mem c (c.hD.1 ha)) hJt ⟨GLBConj t E, hEtJ, hEt, hEtc ▸ hE3⟩)

theorem para1 (hc : S8Ctx G p) (hcfg : CfgIAt G p) (hx : orderOf x = p) (hL : GLAPComponent p (cx x) L)
    (hrow : RowL row p L) (c : SporCfg G p x L row) {a : G} (ha : a ∈ c.D) {J T : Subgroup G}
    (hJ : GLAPComponent p (cx a) J) (hBsJ : c.Bs ≤ Subgroup.normalizer (J : Set G))
    (hIJ : cfgI p L c.D ≤ J) (hTa : T ≤ cx a) (hT2 : IsPGroup 2 T) (hT1 : T ≠ ⊥)
    (hTJ : T ≤ Subgroup.normalizer (J : Set G)) (hTD : T ≤ ⁅T, c.D⁆)
    (hDT : c.D ≤ Subgroup.normalizer (T : Set G)) :
    ¬ J ≤ cfgI p L c.D ⊔ GLAPPrimeCoreOf p J := by
  intro hcov
  have hp := hc.ctx.prime
  have hDJ : c.D ≤ Subgroup.normalizer (J : Set G) := (cfg_D_le_Bs c).trans hBsJ
  have hsup : cfgI p L c.D ⊔ GLAPPrimeCoreOf p J = J :=
    le_antisymm (sup_le hIJ (Subgroup.map_subtype_le _)) hcov
  have hDc : c.D ≤ centModSubgroup p J :=
    S3.le_centModSubgroup_of_cover hIJ hDJ (cfg_I_le_centralizer c) hsup
  have hTc : T ≤ centModSubgroup p J := S3.le_centModSubgroup_of_comm hDc hTJ hTD
  obtain ⟨E, hEID, hE, hbig⟩ := rank_ID' hc hcfg hx hL hrow c
  exact hT1 (no_centMod_two hp hc.ctx.odd c.hBs hE hbig hEID hIJ hJ
    ((cfg_D_le_centralizer_D c).trans (centralizer_le_cx_of_mem ha)) hTa hT2 hDT hTc)

end Para1

section Rows

variable {p : ℕ} {x : G} {L : Subgroup G} {row : Row}

theorem case_1420 (hc : S8Ctx G p) (h1420 : I1420CfgAt G p) (h1016 : I1016At89 G) (hx : orderOf x = p)
    (hL : GLAPComponent p (cx x) L) (hrow : RowL row p L) (c : SporCfg G p x L row)
    (hrows : row = .ly ∨ row = .co1 ∨ row = .suz ∨ row = .suzh ∨ row = .m3 ∨ row = .m5)
    {a : G} (ha : a ∈ c.D) (ha1 : a ≠ 1) {J : Subgroup G} (hJ : GLAPComponent p (cx a) J)
    (hIJ : GLAPComponent p (J ⊓ Subgroup.centralizer (c.D : Set G)) (cfgI p L c.D))
    (hJI : ¬ J ≤ cfgI p L c.D ⊔ GLAPPrimeCoreOf p J) :
    catalogIs (PSimple p J) (sporIs row.name) := by
  have hp := hc.ctx.prime
  have hK := isKGroup_cx hc.ctx ha1
  have h := h1420 x L row c hx hL hrow hrows a ha ha1 hK J hJ hIJ hJI
  have hBs4 : Nat.card c.Bs = p ^ row.rank := c.hBsCard
  rcases hrows with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h
  · exact h
  · rcases h with h | h
    · exact h
    · exfalso
      obtain rfl : p = 3 := hrow.1
      obtain ⟨E, V, -, hE, hEc, -, hV2, hV1, hEV⟩ := h1016.1 (cx a) J hK hJ h
      refine rank_contra hp c.hBs hE ?_ hEV (coprime_card_of_two hp hc.ctx.odd hV2)
        (two_dvd_card_of_two hV2 hV1)
      rw [hBs4, hEc]
      norm_num [Row.rank]
  · rcases h with h | h
    · exact h
    · exfalso
      obtain rfl : p = 3 := hrow.1
      have : Fact (Nat.Prime 3) := ⟨hp⟩
      obtain ⟨E, V, hEJ, hE, hEc, hEZ, hVJ, hV2, hV1, hEV⟩ := h1016.2 (cx a) J hK hJ h
      have hAD : Subgroup.zpowers a ≤ c.D := (Subgroup.zpowers_le).2 ha
      have hA : IsElemAbelian 3 (Subgroup.zpowers a) := isElemAbelian_mono c.hD.2.1 hAD
      have hEA : E ≤ Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G) := by
        rw [S3.centralizer_zpowers]
        exact hEJ.trans hJ.1
      have hoa : orderOf a = 3 := orderOf_eq_prime (c.hD.2.1.2 a ha) ha1
      have hinf : E ⊓ Subgroup.zpowers a = ⊥ := by
        have hdvd : Nat.card (E ⊓ Subgroup.zpowers a : Subgroup G) ∣ 3 := by
          rw [← hoa, ← Nat.card_zpowers]
          exact Subgroup.card_dvd_of_le inf_le_right
        rcases (Nat.dvd_prime hp).1 hdvd with h1 | h1
        · exact Subgroup.eq_bot_of_card_eq _ h1
        · exfalso
          have heq := Subgroup.eq_of_le_of_card_ge
            (inf_le_right : E ⊓ Subgroup.zpowers a ≤ Subgroup.zpowers a)
            (by rw [h1, Nat.card_zpowers, hoa])
          have haE : a ∈ E := by
            have : a ∈ E ⊓ Subgroup.zpowers a := by rw [heq]; exact Subgroup.mem_zpowers a
            exact this.1
          have haZ : a ∈ E ⊓ centerOf J := by
            refine ⟨haE, mem_centerOf_iff.2 ⟨hEJ haE, fun j hj => ?_⟩⟩
            exact Subgroup.mem_centralizer_singleton_iff.1 (hJ.1 hj)
          rw [hEZ] at haZ
          exact ha1 (Subgroup.mem_bot.1 haZ)
      have hAE : Subgroup.zpowers a ≤ Subgroup.normalizer (E : Set G) :=
        zpowers_le_normalizer_of_le_cx (hEJ.trans hJ.1)
      have hcard := card_sup_mul_card_inf_of_le_normalizer hAE
      rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, hoa, hEc] at hcard
      have hEAV : E ⊔ Subgroup.zpowers a ≤ Subgroup.normalizer (V : Set G) :=
        sup_le hEV (zpowers_le_normalizer_of_le_cx (hVJ.trans hJ.1))
      refine rank_contra hp c.hBs (isElemAbelian_sup hE hA hEA) ?_ hEAV
        (coprime_card_of_two hp hc.ctx.odd hV2) (two_dvd_card_of_two hV2 hV1)
      rw [hBs4, hcard]
      norm_num [Row.rank]
  · exact h
  · exact h

theorem case_co2 (hc : S8Ctx G 3) (hcfg : CfgIAt G 3) (h1431 : I1431At G) (h71 : I71InnerAt G)
    (h2016 : I2016At G) (hx : orderOf x = 3) (hL : GLAPComponent 3 (cx x) L) (hrow : RowL .co2 3 L)
    (c : SporCfg G 3 x L .co2) {a : G} (ha : a ∈ c.D) (ha1 : a ≠ 1) {J T : Subgroup G}
    (hJ : GLAPComponent 3 (cx a) J) (hBsJ : c.Bs ≤ Subgroup.normalizer (J : Set G))
    (hIJ : GLAPComponent 3 (J ⊓ Subgroup.centralizer (c.D : Set G)) (cfgI 3 L c.D))
    (hJI : ¬ J ≤ cfgI 3 L c.D ⊔ GLAPPrimeCoreOf 3 J)
    (hTa : T ≤ cx a) (hT2 : IsPGroup 2 T) (hT1 : T ≠ ⊥) (hTJ : T ≤ Subgroup.normalizer (J : Set G))
    (hTD : T ≤ ⁅T, c.D⁆)
    (hTn : cfgK 3 x L c.D c.R ⊔ c.Bs ≤ Subgroup.normalizer (T : Set G)) :
    catalogIs (PSimple 3 J) (sporIs .Co2) := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  obtain ⟨hD1, hD2, hD3, -⟩ := c.hD
  obtain ⟨-, -, hRI, hRK, -⟩ := c.hData
  obtain ⟨y, hyD, hya⟩ := exists_not_mem_zpowers hp hD2 hD3 ha
  have hcen := centralizer_eq_inf hp hD2 hD3 ha ha1 hyD hya
  have hy1 : y ≠ 1 := fun h => hya (h ▸ Subgroup.one_mem _)
  have hK := isKGroup_cx hc.ctx ha1
  have hyca : y ∈ cx a := Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute hD2 hyD ha)
  have hJy : J ⊓ cx y = J ⊓ Subgroup.centralizer (c.D : Set G) := by
    rw [hcen, ← inf_assoc, inf_eq_left.2 hJ.1]
  have hctx : Case2Ctx a y J (cfgI 3 L c.D) :=
    ⟨orderOf_eq_prime (hD2.2 a ha) ha1, hK, hyca, orderOf_eq_prime (hD2.2 y hyD) hy1, hya, hJ,
      hBsJ (hD1 hyD), hJy ▸ hIJ, hRI, hJI, (cfg_twoLocalRank hp c).le⟩
  obtain ⟨h1, h2⟩ := h1431 a y J (cfgI 3 L c.D) (cfgK 3 x L c.D c.R) T hctx
  obtain ⟨E, hEID, hE, hbig⟩ := rank_ID' hc hcfg hx hL hrow c
  have hDa : c.D ≤ cx a := (cfg_D_le_centralizer_D c).trans (centralizer_le_cx_of_mem ha)
  have hDJ : c.D ≤ Subgroup.normalizer (J : Set G) := (cfg_D_le_Bs c).trans hBsJ
  have hDT : c.D ≤ Subgroup.normalizer (T : Set G) := ((cfg_D_le_Bs c).trans le_sup_right).trans hTn
  have hIJle : cfgI 3 L c.D ≤ J := hIJ.1.trans inf_le_left
  have hfaith : T ⊓ centModSubgroup 3 J = ⊥ :=
    no_centMod_two hp (by norm_num) c.hBs hE hbig hEID hIJle hJ hDa (inf_le_left.trans hTa)
      (hT2.to_le inf_le_left) (le_normalizer_inf' hDT (hDJ.trans (normalizer_le_normalizer_centMod J)))
      inf_le_right
  have hinner := h71 (cx a) J T c.D hK hJ h1 hT2 hTJ (isPGroup_of_isElemAbelian hD2) hDJ hDT hTD
  have hloc : Case2Local y J (cfgK 3 x L c.D c.R) T :=
    ⟨(cfg_K_le_centralizer c).trans (centralizer_le_cx_of_mem hyD),
      ((cfg_K_le c).trans inf_le_left).trans hIJle, hRK, ⟨_, rfl⟩, hT2, hT1, hTJ, hfaith, hinner,
      le_sup_left.trans hTn, hTn (Subgroup.mem_sup_right (hD1 hyD))⟩
  obtain ⟨i, hi, hiS⟩ := h2 hloc
  rcases hi with hi | hi | hi
  · exact ⟨i, hi, hiS⟩
  · exact absurd ⟨i, hi, hiS⟩ (h2016.1 a y J _ _ T hctx hloc)
  · exfalso
    obtain ⟨W, hWJ, hW2, hWO, hWn⟩ := h2016.2 a y J _ _ T hctx hloc ⟨i, hi, hiS⟩
    have hDle := le_sup_zpowers hp hD2 hD3 ha ha1 hyD hya
    have hWOJ : W ⊔ GLAPPrimeCoreOf 3 J ≤ cx a := (sup_le hWJ (Subgroup.map_subtype_le _)).trans hJ.1
    have hEN : E ≤ Subgroup.normalizer ((W ⊔ GLAPPrimeCoreOf 3 J : Subgroup G) : Set G) :=
      hEID.trans (sup_le (le_sup_left.trans hWn)
        (hDle.trans (sup_le (zpowers_le_normalizer_of_le_cx hWOJ) (le_sup_right.trans hWn))))
    have hW1 : W ≠ ⊥ := fun h => hWO (h ▸ bot_le)
    have hWO' : W ≤ Subgroup.normalizer (GLAPPrimeCoreOf 3 J : Set G) :=
      hWJ.trans (le_normalizer_glaPPrimeCoreOf 3 J)
    have hOp : ¬ 3 ∣ Nat.card (GLAPPrimeCoreOf 3 J) :=
      (Nat.Prime.coprime_iff_not_dvd hp).1 (i183_coprime_card_glaPPrimeCoreOf hp J)
    have hWp : ¬ 3 ∣ Nat.card W := (Nat.Prime.coprime_iff_not_dvd hp).1 (coprime_card_of_two hp (by norm_num) hW2)
    have hcop : Nat.Coprime 3 (Nat.card (W ⊔ GLAPPrimeCoreOf 3 J : Subgroup G)) := by
      rw [sup_comm]
      exact (Nat.Prime.coprime_iff_not_dvd hp).2 (not_dvd_card_sup_of_le_normalizer hp hWO' hOp hWp)
    exact rank_contra hp c.hBs hE hbig hEN hcop
      ((two_dvd_card_of_two hW2 hW1).trans (Subgroup.card_dvd_of_le le_sup_left))

theorem case_1432 (hc : S8Ctx G 3) (h1432 : I1432At G) (hrow : RowL row 3 L)
    (c : SporCfg G 3 x L row) (hrows : row = .fi24 ∨ row = .fi24h ∨ row = .th)
    {a : G} (ha : a ∈ c.D) (ha1 : a ≠ 1) {J T : Subgroup G} (hJ : GLAPComponent 3 (cx a) J)
    (hIJ : GLAPComponent 3 (J ⊓ Subgroup.centralizer (c.D : Set G)) (cfgI 3 L c.D))
    (hJI : ¬ J ≤ cfgI 3 L c.D ⊔ GLAPPrimeCoreOf 3 J)
    (hTa : T ≤ cx a) (hT2 : IsPGroup 2 T) (hT1 : T ≠ ⊥)
    (hTn : c.Bs ≤ Subgroup.normalizer (T : Set G)) :
    catalogIs (PSimple 3 J) (sporIs row.name) := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  obtain ⟨hD1, hD2, hD3, -⟩ := c.hD
  obtain ⟨-, -, hRI, -, -⟩ := c.hData
  obtain ⟨y, hyD, hya⟩ := exists_not_mem_zpowers hp hD2 hD3 ha
  have hcen := centralizer_eq_inf hp hD2 hD3 ha ha1 hyD hya
  have hJy : J ⊓ cx y = J ⊓ Subgroup.centralizer (c.D : Set G) := by
    rw [hcen, ← inf_assoc, inf_eq_left.2 hJ.1]
  have h := h1432 (cx a) J c.Bs (cfgI 3 L c.D) T a y (isKGroup_cx hc.ctx ha1) hJ c.hBs
    (cfg_Bs_le_cx_of_mem c (hD1 ha)) hTa hT1 hT2 hTn (hD1 ha) ha1 (centMod_of_le_cx hJ.1) (hD1 hyD)
    (hJy ▸ hIJ) hJI
  rcases hrows with rfl | rfl | rfl
  · exact h.1 hRI
  · exact h.1 hRI
  · exact h.2 hRI (cfg_twoLocalRank hp c).le

end Rows

structure Inputs89 (G : Type) [Group G] [Finite G] (p : ℕ) : Prop extends Inputs88 G p where
  i183 : Input18_3_4
  i112s : I112StarAt G p
  i112r : I112RankAt G
  i112n : I112NormAt G p
  i1420 : I1420CfgAt G p
  i1016 : I1016At89 G
  i1431 : I1431At G
  i71 : I71InnerAt G
  i2016 : I2016At G
  i1432 : I1432At G

theorem lemma89 {p : ℕ} {x : G} {L : Subgroup G} {row : Row} (hc : S8Ctx G p) (hin : Inputs89 G p)
    (hx : orderOf x = p) (hL : GLAPComponent p (cx x) L) (hrow : RowL row p L) (c : SporCfg G p x L row)
    {a : G} (ha : a ∈ c.D) (ha1 : a ≠ 1) {Q : Subgroup G} (hQa : Q ≤ cx a) (hQ2 : IsPGroup 2 Q)
    (hQn : cfgK p x L c.D c.R ⊔ c.Bs ≤ Subgroup.normalizer (Q : Set G))
    (hQD : ¬ Q ≤ Subgroup.centralizer (c.D : Set G)) :
    Nonempty (PSimple p (cfgJa p (cfgI p L c.D) a) ≃* PSimple p L) := by
  have hp := hc.ctx.prime
  obtain ⟨hJ, hBsJ, hIJ⟩ := ja_setup hc hin.i183 hin.i112s hin.i112r hin.i112n hin.cfgI hx hL hrow c ha ha1
  obtain ⟨hTQ, hT1, hTD, hTn⟩ := tstar_facts hp hc.ctx.odd c hQ2 hQn hQD
  have hTa : ⁅Q, c.D⁆ ≤ cx a := hTQ.trans hQa
  have hT2 : IsPGroup 2 (⁅Q, c.D⁆ : Subgroup G) := hQ2.to_le hTQ
  have hIJle : cfgI p L c.D ≤ cfgJa p (cfgI p L c.D) a := I_le_cfgJa p _ a
  have hTJ := tstar_le_normalizer hc hin.i112n hin.cfgI hx hL hrow c ha ha1 hJ hIJle hTa hTD
  have hDT : c.D ≤ Subgroup.normalizer ((⁅Q, c.D⁆ : Subgroup G) : Set G) :=
    ((cfg_D_le_Bs c).trans le_sup_right).trans hTn
  have hJI := para1 hc hin.cfgI hx hL hrow c ha hJ hBsJ hIJle hTa hT2 hT1 hTJ hTD hDT
  have hcat : catalogIs (PSimple p (cfgJa p (cfgI p L c.D) a)) (sporIs row.name) := by
    have hrow' := hrow
    obtain ⟨hpr, -⟩ := hrow'
    rcases row with _ | _ | _ | _ | _ | _ | _ | _ | _ | _
    · exact case_1420 hc hin.i1420 hin.i1016 hx hL hrow c (Or.inl rfl) ha ha1 hJ hIJ hJI
    · obtain rfl : p = 3 := hpr
      exact case_co2 hc hin.cfgI hin.i1431 hin.i71 hin.i2016 hx hL hrow c ha ha1 hJ hBsJ hIJ hJI hTa hT2
        hT1 hTJ hTD hTn
    · exact case_1420 hc hin.i1420 hin.i1016 hx hL hrow c (Or.inr (Or.inl rfl)) ha ha1 hJ hIJ hJI
    · obtain rfl : p = 3 := hpr
      exact case_1432 hc hin.i1432 hrow c (Or.inl rfl) ha ha1 hJ hIJ hJI hTa hT2 hT1
        (le_sup_right.trans hTn)
    · obtain rfl : p = 3 := hpr
      exact case_1432 hc hin.i1432 hrow c (Or.inr (Or.inl rfl)) ha ha1 hJ hIJ hJI hTa hT2 hT1
        (le_sup_right.trans hTn)
    · exact case_1420 hc hin.i1420 hin.i1016 hx hL hrow c (Or.inr (Or.inr (Or.inl rfl))) ha ha1 hJ hIJ hJI
    · exact case_1420 hc hin.i1420 hin.i1016 hx hL hrow c (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) ha ha1
        hJ hIJ hJI
    · obtain rfl : p = 3 := hpr
      exact case_1432 hc hin.i1432 hrow c (Or.inr (Or.inr rfl)) ha ha1 hJ hIJ hJI hTa hT2 hT1
        (le_sup_right.trans hTn)
    · exact case_1420 hc hin.i1420 hin.i1016 hx hL hrow c
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) ha ha1 hJ hIJ hJI
    · exact case_1420 hc hin.i1420 hin.i1016 hx hL hrow c
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) ha ha1 hJ hIJ hJI
  exact nonempty_mulEquiv_of_catalogIs_spor hcat hrow.2.1

end L89

end S8

end CFSG.LocalAnalysis.GLTheoremA
