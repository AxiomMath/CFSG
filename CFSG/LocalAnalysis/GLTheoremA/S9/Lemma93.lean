module

public import CFSG.LocalAnalysis.GLTheoremA.S9.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4S.Prop415Base
public import CFSG.LocalAnalysis.GLTheoremA.Prop51
public import CFSG.LocalAnalysis.GLTheoremA.S9.L93Comp
public import CFSG.LocalAnalysis.GLTheoremA.S9.L93PGroup

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S9

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

structure Lemma93Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  i183 : Input18_3_4
  i264 : I264At G p
  i91 : I91At G
  i147 : I147At G
  k3 : K3NotChev2At
  i264b : I264bAt G p
  i712 : I712At G p
  list93 : I9List93At G p
  i137 : I137At G p
  sl34 : I71SL34At G

abbrev bstar (B U : Subgroup G) : Subgroup G := (B ⊓ Subgroup.centralizer (U : Set G)) ⊔ U

theorem d4_contradiction_cover {p : ℕ} (hc : S9Ctx G p) (h183 : Input18_3_4) (h264 : I264At G p)
    (h91 : I91At G) (h147 : I147At G) {B : Subgroup G} {x : G} {L N : Subgroup G}
    (hS0 : IsS0 p B x L) (hBL : B ≤ Subgroup.normalizer (L : Set G)) (hd : dLevel G p = 4)
    (hnoG : ¬ IsGStar p B L) (hmax : IsMaxRankIn p B (L ⊔ B)) (hN : IsTwoLocal N)
    (hcov : Covers p N (Subgroup.centralizer ({x} : Set G))) : False := by
  have hB : GLAIsBmax p B := hS0.1.1
  have hL : GLAPComponent p (Subgroup.centralizer ({x} : Set G)) L := hS0.1.2.2
  have hpp : p.Prime := hc.ctx.prime
  have hp2 : p ≠ 2 := hc.ctx.odd
  have hBel : IsElemAbelian p B := hB.1
  obtain ⟨hxB, hx1, -⟩ := hS0.1.2.1
  have hlev : fullCoverLevel p (PQuot p L) = 4 := by
    have h1 := fullCoverLevel_min_eq_dLevel hS0 hnoG
    have h2 := fullCoverLevel_le_four p (PQuot p L)
    omega
  have h4 : p ^ 4 ≤ Nat.card B := by
    rw [hB.2.1]
    exact Nat.pow_le_pow_right hpp.pos hc.ctx.rank_ge
  have hCx0 : Subgroup.centralizer ({x} : Set G) ≠ ⊤ :=
    centralizer_ne_top_of_ne_one hc.ctx.simple hc.ctx.nonabelian hx1
  have hLK : CFSG.Open.IsKGroup ↥L :=
    hc.ctx.kProper.isKGroup L (fun h => hCx0 (top_le_iff.1 (h ▸ hL.1)))
  rcases h264 hpp hp2 B x L hBel hxB hx1 hL hLK hBL h4 hmax hlev with
    hGB | ⟨hp3, hB81, hCM, hcat, b, hbB, hbout⟩
  · exact hnoG (isGStar_of_isGB hGB hBL)
  · subst hp3
    have hbN : b ∈ Subgroup.normalizer (L : Set G) := hBL hbB
    have hb3 : b ^ 3 = 1 := hBel.2 b hbB
    obtain ⟨y, hyLb, hy3, hyout, hL0, hcat0⟩ :=
      h91 (Subgroup.centralizer ({x} : Set G)) L b hL hcat hbN hb3 hbout
    set L₀ : Subgroup G := GLAPLayer 3 (L ⊓ Subgroup.centralizer ({y} : Set G)) with hL₀def
    obtain ⟨⟨D₀, hD₀L, hD₀el, hD₀c⟩, hlay, hZ0⟩ :=
      h147 (L ⊓ Subgroup.centralizer ({y} : Set G)) L₀ hL0 hcat0
    have hBCx : B ≤ Subgroup.centralizer ({x} : Set G) := isElemAbelian_le_centralizer hBel hxB
    have hLbC : L ⊔ Subgroup.zpowers b ≤ Subgroup.centralizer ({x} : Set G) :=
      sup_le hL.1 (Subgroup.zpowers_le.2 (hBCx hbB))
    have hLbN : L ⊔ Subgroup.zpowers b ≤ Subgroup.normalizer (L : Set G) :=
      sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.2 hbN)
    have hyC : y ∈ Subgroup.centralizer ({x} : Set G) := hLbC hyLb
    have hyN : y ∈ Subgroup.normalizer (L : Set G) := hLbN hyLb
    have hx3 : x ^ 3 = 1 := hBel.2 x hxB
    have hx0 : CentMod 3 L x := (hCM x hxB).2 (Subgroup.mem_zpowers x)
    have hL₀le : L₀ ≤ L ⊓ Subgroup.centralizer ({y} : Set G) := sSup_le fun K hK => hK.1
    obtain ⟨z, hzD, hz1⟩ : ∃ z ∈ D₀, z ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have : D₀ = ⊥ := (Subgroup.eq_bot_iff_forall D₀).2 hcon
      rw [this, Subgroup.card_bot] at hD₀c
      omega
    obtain ⟨B₀, D, E, hB₀el, hB₀c, hxB₀, hD, hDE, hEB₀, hDnc, hDel, hDc, hEel, hEc, hEdef, hB₀L⟩ :=
      exists_B0_elem hx3 hx1 hL.1 hyC hy3 hyN hyout hx0 hL₀le hZ0 hD₀L hD₀el hD₀c hzD hz1
    have hB₀C : B₀ ≤ Subgroup.centralizer ({x} : Set G) := isElemAbelian_le_centralizer hB₀el hxB₀
    have hB₀card : Nat.card B₀ = Nat.card B := hB₀c.trans hB81.symm
    have hB₀ : GLAIsBmax 3 B₀ := isBmax_of_covers hpp hB hB₀C hB₀el hB₀card hN hcov
    obtain ⟨N₀, hN₀, hB₀N₀⟩ := GLAIsBmax.exists_maxTwoLocal hB₀
    obtain ⟨D', hD'D, hD'c, hD'ess, -⟩ := hc.stage3.2.2.1 B₀ D N₀ hB₀ (hDE.trans hEB₀) hDnc hN₀ hB₀N₀
    obtain ⟨a, haD', ha1⟩ : ∃ a ∈ D', a ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have : D' = ⊥ := (Subgroup.eq_bot_iff_forall D').2 hcon
      rw [this, Subgroup.card_bot] at hD'c
      omega
    have hL₀comp : GLAPComponent 3 (Subgroup.centralizer (D : Set G)) L₀ := by
      rw [hD]
      exact component_cent_of_two hpp hL hL0
    have hlayE : GLAPLayer 3 (L₀ ⊓ Subgroup.centralizer (E : Set G)) ≠ ⊥ := by
      have h1 := hlay z (hD₀L hzD) (hD₀el.2 z hzD) hz1
      have heq : L₀ ⊓ Subgroup.centralizer (E : Set G) = L₀ ⊓ Subgroup.centralizer ({z} : Set G) := by
        ext g
        simp only [Subgroup.mem_inf]
        constructor
        · rintro ⟨hg, hgE⟩
          refine ⟨hg, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
          have hzE : z ∈ E := by
            rw [hEdef]
            exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
          exact (Subgroup.mem_centralizer_iff.1 hgE z hzE).symm
        · rintro ⟨hg, hgz⟩
          refine ⟨hg, Subgroup.mem_centralizer_iff.2 fun e he => ?_⟩
          have hgx : g ∈ Subgroup.centralizer ({x} : Set G) := hL.1 (hL₀le hg).1
          have hgy : g ∈ Subgroup.centralizer ({y} : Set G) := (hL₀le hg).2
          have hEg : E ≤ Subgroup.centralizer ({g} : Set G) := by
            rw [hEdef, hD]
            refine sup_le (sup_le ?_ ?_) ?_
            · exact Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2
                (Subgroup.mem_centralizer_singleton_iff.1 hgx).symm)
            · exact Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2
                (Subgroup.mem_centralizer_singleton_iff.1 hgy).symm)
            · exact Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2
                (Subgroup.mem_centralizer_singleton_iff.1 hgz).symm)
          exact Subgroup.mem_centralizer_singleton_iff.1 (hEg he)
      rwa [heq]
    obtain ⟨L₁, hL₁S, hL₁G⟩ := exists_isGStar_pump h183 hpp hc.ctx.simple hc.ctx.nonabelian
      hc.ctx.kProper hB₀ hDE hEB₀ hDel hEel hEc (hD'D haD') ha1 (hD'ess a haD' ha1) hL₀comp hlayE
    have h5 := tripleLevel_le_dLevel hL₁S
    unfold tripleLevel at h5
    rw [if_pos hL₁G, hd] at h5
    omega

private theorem lemma93_conj_mem_commutator {T₀ B : Subgroup G} (hBN : B ≤ Subgroup.normalizer (T₀ : Set G))
    (hBc : ∀ b ∈ B, ∀ c ∈ B, b * c = c * b) {b : G} (hb : b ∈ B) {t : G}
    (ht : t ∈ (⁅T₀, B⁆ : Subgroup G)) : b * t * b⁻¹ ∈ (⁅T₀, B⁆ : Subgroup G) := by
  have hle : (⁅T₀, B⁆ : Subgroup G) ≤ (⁅T₀, B⁆ : Subgroup G).comap (MulAut.conj b).toMonoidHom := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    rw [Subgroup.mem_comap]
    show b * ⁅g₁, g₂⁆ * b⁻¹ ∈ _
    have h2 : b * g₂ = g₂ * b := hBc b hb g₂ hg₂
    have e1 : b * g₂ * b⁻¹ = g₂ := by rw [h2]; group
    have e2 : b * g₂⁻¹ * b⁻¹ = g₂⁻¹ := by
      rw [show b * g₂⁻¹ * b⁻¹ = (b * g₂ * b⁻¹)⁻¹ by group, e1]
    have key : b * ⁅g₁, g₂⁆ * b⁻¹ = ⁅b * g₁ * b⁻¹, g₂⁆ := by
      calc b * ⁅g₁, g₂⁆ * b⁻¹
          = (b * g₁ * b⁻¹) * (b * g₂ * b⁻¹) * (b * g₁⁻¹ * b⁻¹) * (b * g₂⁻¹ * b⁻¹) := by
            simp only [commutatorElement_def]; group
        _ = ⁅b * g₁ * b⁻¹, g₂⁆ := by
            rw [e1, e2, commutatorElement_def]; group
    rw [key]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_normalizer_iff.1 (hBN hb) g₁ |>.1 hg₁) hg₂
  have h := hle ht
  rw [Subgroup.mem_comap] at h
  exact h

theorem exists_T_not_le_core {p : ℕ} (hc : S9Ctx G p) (hd : dLevel G p ≤ 2) {B : Subgroup G} {x : G}
    (hB : GLAIsBmax p B) (hess : IsEssential p B x) :
    ∃ T : Subgroup G, T ≤ Subgroup.centralizer ({x} : Set G) ∧ IsPGroup 2 T ∧
      B ≤ Subgroup.normalizer (T : Set G) ∧ (⁅T, B⁆ : Subgroup G) = T ∧
      ¬ T ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G)) := by
  classical
  obtain ⟨hxB, hx1, T₀, hT₀C, hT₀2, hBT₀, hTB₀, -⟩ := hess
  have hp := hc.ctx.prime
  have hp2 := hc.ctx.odd
  have hBc : ∀ b ∈ B, ∀ c ∈ B, b * c = c * b := fun b hb c hc' => isElemAbelian_commute hB.1 hb hc'
  have hTle : (⁅T₀, B⁆ : Subgroup G) ≤ T₀ := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    have hg₂' : g₂ * g₁⁻¹ * g₂⁻¹ ∈ T₀ :=
      (Subgroup.mem_normalizer_iff.1 (hBT₀ hg₂) g₁⁻¹).1 (T₀.inv_mem hg₁)
    have e : ⁅g₁, g₂⁆ = g₁ * (g₂ * g₁⁻¹ * g₂⁻¹) := by
      rw [commutatorElement_def]; group
    rw [e]
    exact T₀.mul_mem hg₁ hg₂'
  set T : Subgroup G := ⁅T₀, B⁆ with hTdef
  have hBN : B ≤ Subgroup.normalizer (T : Set G) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact lemma93_conj_mem_commutator hBT₀ hBc hb hh
    · intro hh
      have h' := lemma93_conj_mem_commutator hBT₀ hBc (B.inv_mem hb) hh
      have e : b⁻¹ * (b * h * b⁻¹) * b⁻¹⁻¹ = h := by group
      rw [e] at h'
      exact h'
  have hTC : T ≤ Subgroup.centralizer ({x} : Set G) := hTle.trans hT₀C
  have hT2 : IsPGroup 2 T := hT₀2.to_le hTle
  have hcop : Nat.Coprime (Nat.card B) (Nat.card T₀) := by
    obtain ⟨j, hj⟩ := hT₀2.exists_card_eq
    rw [hB.2.1, hj]
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have hsolv : Group.IsSolvable T₀ := by
    haveI := IsPGroup.isNilpotent hT₀2
    infer_instance
  have hTB : (⁅T, B⁆ : Subgroup G) = T := GL83.commutator_double_eq_self B T₀ hBT₀ hcop hsolv
  refine ⟨T, hTC, hT2, hBN, hTB, fun hO => ?_⟩
  have hbot := hc.stage4.2.2 hd B x T hB hxB hx1 hO hT2 hBN
  exact hTB₀ (hTB.symm.trans hbot)

theorem cx_le_normalizer_L {p : ℕ} (hc : S9Ctx G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    (h : H92 p B x L)
    (hspade : ∀ A : Subgroup G, A ≤ Subgroup.centralizer ({x} : Set G) ⊓ centModSubgroup p L →
      IsElemAbelian p A → Nat.card A ≤ p) :
    Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  exact l93_cx_le_normalizer_L hc h hspade

theorem pow_mem_core_of_centMod {p : ℕ} (hc : S9Ctx G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    (h : H92 p B x L) (hN : Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (L : Set G))
    (hspade : ∀ A : Subgroup G, A ≤ Subgroup.centralizer ({x} : Set G) ⊓ centModSubgroup p L →
      IsElemAbelian p A → Nat.card A ≤ p) :
    ∀ g ∈ Subgroup.centralizer ({x} : Set G) ⊓ centModSubgroup p L,
      ∃ n : ℕ, g ^ (p ^ n) ∈ GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G)) := by
  exact l93_pow_mem_core_of_centMod hc h hN hspade

private theorem lemma93_mem_sup_of_le_normalizer {H K : Subgroup G}
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) {w : G} (hw : w ∈ H ⊔ K) :
    ∃ h ∈ H, ∃ k ∈ K, h * k = w := by
  let P : Subgroup G :=
    { carrier := {w | ∃ h ∈ H, ∃ k ∈ K, h * k = w}
      mul_mem' := by
        rintro _ _ ⟨h1, hh1, k1, hk1, rfl⟩ ⟨h2, hh2, k2, hk2, rfl⟩
        have hk' : h2⁻¹ * k1 * h2⁻¹⁻¹ ∈ K :=
          (Subgroup.mem_normalizer_iff.1 (hHK (H.inv_mem hh2)) k1).1 hk1
        exact ⟨h1 * h2, H.mul_mem hh1 hh2, (h2⁻¹ * k1 * h2⁻¹⁻¹) * k2, K.mul_mem hk' hk2, by group⟩
      one_mem' := ⟨1, H.one_mem, 1, K.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨h, hh, k, hk, rfl⟩
        have hk' : h * k⁻¹ * h⁻¹ ∈ K :=
          (Subgroup.mem_normalizer_iff.1 (hHK hh) k⁻¹).1 (K.inv_mem hk)
        exact ⟨h⁻¹, H.inv_mem hh, h * k⁻¹ * h⁻¹, hk', by group⟩ }
  have hsub : H ⊔ K ≤ P := sup_le (fun h hh => ⟨h, hh, 1, K.one_mem, mul_one h⟩)
    (fun k hk => ⟨1, H.one_mem, k, hk, one_mul k⟩)
  exact hsub hw

private theorem lemma93_mem_zpowers {Q : Type} [Group Q] {a b : Q} (hab : Commute a b) {m n : ℕ}
    (hmn : Nat.Coprime m n) (ha : a ^ n = 1) (hab' : (a * b) ^ m = 1) :
    a ∈ Subgroup.zpowers b := by
  rw [hab.mul_pow] at hab'
  have hinv : a ^ m = (b ^ m)⁻¹ := eq_inv_of_mul_eq_one_left hab'
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hmn
  have hbez : (n : ℤ) * v + (m : ℤ) * u = 1 := by
    rw [mul_comm (n : ℤ) v, mul_comm (m : ℤ) u, add_comm]
    exact huv
  have h2 : a ^ ((n : ℤ) * v + (m : ℤ) * u) = a := by rw [hbez, zpow_one]
  have e1 : a ^ ((n : ℤ) * v) = 1 := by rw [zpow_mul, zpow_natCast, ha, one_zpow]
  rw [zpow_add, e1, one_mul, zpow_mul, zpow_natCast, hinv] at h2
  rw [← h2]
  exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers b) m)) u

private theorem lemma93_mem_sup_core {C L O : Subgroup G} (hOC : C ≤ Subgroup.normalizer (O : Set G))
    (hLC : L ≤ C) {r l : G} (hrC : r ∈ C) (hlL : l ∈ L) (hcomm : ⁅l, r⁆ ∈ O)
    {m n : ℕ} (hmn : Nat.Coprime m n) (hrn : r ^ n ∈ O) (hrl : (r * l) ^ m = 1) :
    r ∈ L ⊔ O := by
  let M : Subgroup C := O.subgroupOf C
  haveI hMn : M.Normal := ⟨fun a ha g => by
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    have := (Subgroup.mem_normalizer_iff.1 (hOC g.2) (a : G)).1 ha
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using this⟩
  have hlC : l ∈ C := hLC hlL
  set ra : C := ⟨r, hrC⟩ with hra
  set la : C := ⟨l, hlC⟩ with hla
  have hab : Commute (QuotientGroup.mk ra : C ⧸ M) (QuotientGroup.mk la : C ⧸ M) := by
    rw [Commute, SemiconjBy, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    rw [Subgroup.mem_subgroupOf]
    have h1 : r⁻¹ * ⁅l, r⁆ * r⁻¹⁻¹ ∈ O :=
      (Subgroup.mem_normalizer_iff.1 (hOC (C.inv_mem hrC)) _).1 hcomm
    rw [inv_inv] at h1
    have h2 : l⁻¹ * (r⁻¹ * ⁅l, r⁆ * r) * l⁻¹⁻¹ ∈ O :=
      (Subgroup.mem_normalizer_iff.1 (hOC (C.inv_mem hlC)) _).1 h1
    rw [inv_inv] at h2
    have e : (((ra * la)⁻¹ * (la * ra) : C) : G) = l⁻¹ * (r⁻¹ * ⁅l, r⁆ * r) * l := by
      simp only [hra, hla, Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
      group
    rw [e]
    exact h2
  have hpow_a : (QuotientGroup.mk ra : C ⧸ M) ^ n = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa only [hra, Subgroup.coe_pow] using hrn
  have hpow_ab : ((QuotientGroup.mk ra : C ⧸ M) * QuotientGroup.mk la) ^ m = 1 := by
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf]
    have e : (((ra * la) ^ m : C) : G) = (r * l) ^ m := by
      simp only [hra, hla, Subgroup.coe_pow, Subgroup.coe_mul]
    rw [e, hrl]
    exact O.one_mem
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (lemma93_mem_zpowers hab hmn hpow_a hpow_ab)
  rw [← QuotientGroup.mk_zpow] at hj
  have hmem := Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 hj)
  have ho : (l ^ j)⁻¹ * r ∈ O := by
    have e : (((la ^ j)⁻¹ * ra : C) : G) = (l ^ j)⁻¹ * r := by
      simp only [hra, hla, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow]
    rw [← e]
    exact hmem
  have hlj : l ^ j ∈ L := L.zpow_mem hlL j
  have hr_eq : r = l ^ j * ((l ^ j)⁻¹ * r) := by group
  rw [hr_eq]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hlj) (Subgroup.mem_sup_right ho)


theorem le_sup_core_of_inner {p : ℕ} (hc : S9Ctx G p) (hI712 : I712At G p) {B : Subgroup G}
    {x : G} {L T : Subgroup G} (h : H92 p B x L)
    (hN : Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (L : Set G))
    (hR : ∀ g ∈ Subgroup.centralizer ({x} : Set G) ⊓ centModSubgroup p L,
      ∃ n : ℕ, g ^ (p ^ n) ∈ GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G)))
    (hT : T ≤ Subgroup.centralizer ({x} : Set G)) (hT2 : IsPGroup 2 T)
    (hBT : B ≤ Subgroup.normalizer (T : Set G)) (hTB : (⁅T, B⁆ : Subgroup G) = T) :
    T ≤ L ⊔ GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G)) := by
  classical
  have hp := hc.ctx.prime
  have hp2 := hc.ctx.odd
  have hBC : B ≤ Subgroup.centralizer ({x} : Set G) := isElemAbelian_le_centralizer h.bmax.1 h.mem
  have hLC : L ≤ Subgroup.centralizer ({x} : Set G) := h.comp.1
  have hTN : T ≤ Subgroup.normalizer (L : Set G) := fun t ht => hN (hT ht)
  have hOC : Subgroup.centralizer ({x} : Set G) ≤
      Subgroup.normalizer (GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G)) : Set G) :=
    le_normalizer_glaPPrimeCoreOf p _
  have hLO : GLAPPrimeCoreOf p L ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G)) := by
    rw [← glaPPrimeCoreOf_inf_eq_of_isSubnormal hp h.comp.2.1]
    exact inf_le_right
  have hRN : (Subgroup.centralizer ({x} : Set G) ⊓ centModSubgroup p L) ≤
      Subgroup.normalizer (L : Set G) := fun r hr => hr.2.1
  have hdec : ∀ b ∈ B, ∀ t ∈ T,
      ⁅b, t⁆ ∈ (Subgroup.centralizer ({x} : Set G) ⊓ centModSubgroup p L) ⊔ L := by
    intro b hb t ht
    obtain ⟨l, hl, hall⟩ := hI712 hp hp2 (Subgroup.centralizer ({x} : Set G)) L B T
      (isKGroup_cx hc h.ne_one) h.comp h.chev2 (isPGroup_of_isElemAbelian h.bmax.1) hT2 h.norm
      hTN hBT b hb t ht
    have hbN : b ∈ Subgroup.normalizer (L : Set G) := h.norm hb
    have htN : t ∈ Subgroup.normalizer (L : Set G) := hTN ht
    have hgN : ⁅b, t⁆ ∈ Subgroup.normalizer (L : Set G) := by
      rw [commutatorElement_def]
      exact (Subgroup.normalizer (L : Set G)).mul_mem
        ((Subgroup.normalizer (L : Set G)).mul_mem
          ((Subgroup.normalizer (L : Set G)).mul_mem hbN htN)
          ((Subgroup.normalizer (L : Set G)).inv_mem hbN))
        ((Subgroup.normalizer (L : Set G)).inv_mem htN)
    have hgC : ⁅b, t⁆ ∈ Subgroup.centralizer ({x} : Set G) := by
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hBC hb) (hT ht))
        (Subgroup.inv_mem _ (hBC hb))) (Subgroup.inv_mem _ (hT ht))
    have hcN : l * ⁅b, t⁆⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
      (Subgroup.normalizer (L : Set G)).mul_mem (Subgroup.le_normalizer hl)
        ((Subgroup.normalizer (L : Set G)).inv_mem hgN)
    have hcO : ∀ y ∈ L, ⁅y, l * ⁅b, t⁆⁻¹⁆ ∈ GLAPPrimeCoreOf p L := by
      intro y hy
      have hw := hall y hy
      have hw' : l * ((l⁻¹ * y * l)⁻¹ * (⁅b, t⁆⁻¹ * y * ⁅b, t⁆)) * l⁻¹ ∈ GLAPPrimeCoreOf p L :=
        (Subgroup.mem_normalizer_iff.1 (le_normalizer_glaPPrimeCoreOf p L hl) _).1 hw
      have e : ⁅y, l * ⁅b, t⁆⁻¹⁆ = y * (l * ((l⁻¹ * y * l)⁻¹ * (⁅b, t⁆⁻¹ * y * ⁅b, t⁆)) * l⁻¹)⁻¹ * y⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.1 (le_normalizer_glaPPrimeCoreOf p L hy) _).1
        (Subgroup.inv_mem _ hw')
    have hcR : l * ⁅b, t⁆⁻¹ ∈ Subgroup.centralizer ({x} : Set G) ⊓ centModSubgroup p L :=
      ⟨Subgroup.mul_mem _ (hLC hl) (Subgroup.inv_mem _ hgC), ⟨hcN, hcO⟩⟩
    have key : ⁅b, t⁆ = (l * ⁅b, t⁆⁻¹)⁻¹ * l := by group
    rw [key]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ((Subgroup.centralizer ({x} : Set G) ⊓
      centModSubgroup p L).inv_mem hcR)) (Subgroup.mem_sup_right hl)
  have hTsup : (⁅T, B⁆ : Subgroup G) ≤ (Subgroup.centralizer ({x} : Set G) ⊓ centModSubgroup p L) ⊔ L := by
    rw [Subgroup.commutator_le]
    intro t ht b hb
    have e : ⁅t, b⁆ = ⁅b, t⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact ((Subgroup.centralizer ({x} : Set G) ⊓ centModSubgroup p L) ⊔ L).inv_mem (hdec b hb t ht)
  have hTR : T ≤ (Subgroup.centralizer ({x} : Set G) ⊓ centModSubgroup p L) ⊔ L := by
    rw [← hTB]
    exact hTsup
  intro t ht
  obtain ⟨r, hr, l', hl', hrl⟩ := lemma93_mem_sup_of_le_normalizer hRN (hTR ht)
  obtain ⟨k, hk⟩ := hT2 ⟨t, ht⟩
  have hk' : t ^ (2 ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  rw [← hrl] at hk'
  obtain ⟨n, hn⟩ := hR r ⟨hr.1, hr.2⟩
  have hcomm : ⁅l', r⁆ ∈ GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G)) :=
    hLO (hr.2.2 l' hl')
  have hmn : Nat.Coprime (2 ^ k) (p ^ n) :=
    Nat.Coprime.pow k n ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
  have hrO := lemma93_mem_sup_core hOC hLC hr.1 hl' hcomm hmn hn hk'
  rw [← hrl]
  exact Subgroup.mul_mem _ hrO (Subgroup.mem_sup_left hl')

theorem exists_two_group_of_le_sup {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {B : Subgroup G} {x : G}
    {L T : Subgroup G} (h : H92 p B x L) (hT : T ≤ Subgroup.centralizer ({x} : Set G))
    (hT2 : IsPGroup 2 T) (hBT : B ≤ Subgroup.normalizer (T : Set G))
    (hTle : T ≤ L ⊔ GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G)))
    (hTO : ¬ T ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G))) :
    ∃ T₀ : Subgroup G, T₀ ≤ L ∧ IsPGroup 2 T₀ ∧ B ≤ Subgroup.normalizer (T₀ : Set G) ∧
      ¬ T₀ ≤ GLAPPrimeCoreOf p L := by
  exact l93_exists_two_group_of_le_sup hp hp2 h hT hT2 hBT hTle hTO

theorem exists_two_group_in_L_of {p : ℕ} (hc : S9Ctx G p) (hI712 : I712At G p) {B : Subgroup G}
    {x : G} {L T : Subgroup G} (h : H92 p B x L)
    (hN : Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (L : Set G))
    (hR : ∀ g ∈ Subgroup.centralizer ({x} : Set G) ⊓ centModSubgroup p L,
      ∃ n : ℕ, g ^ (p ^ n) ∈ GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G)))
    (hT : T ≤ Subgroup.centralizer ({x} : Set G)) (hT2 : IsPGroup 2 T)
    (hBT : B ≤ Subgroup.normalizer (T : Set G)) (hTB : (⁅T, B⁆ : Subgroup G) = T)
    (hTO : ¬ T ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G))) :
    ∃ T₀ : Subgroup G, T₀ ≤ L ∧ IsPGroup 2 T₀ ∧ B ≤ Subgroup.normalizer (T₀ : Set G) ∧
      ¬ T₀ ≤ GLAPPrimeCoreOf p L :=
  exists_two_group_of_le_sup hc.ctx.prime hc.ctx.odd h hT hT2 hBT
    (le_sup_core_of_inner hc hI712 h hN hR hT hT2 hBT hTB) hTO

theorem exists_two_group_in_L {p : ℕ} (hc : S9Ctx G p) (hI712 : I712At G p) {B : Subgroup G} {x : G}
    {L T : Subgroup G} (h : H92 p B x L) (hT : T ≤ Subgroup.centralizer ({x} : Set G))
    (hT2 : IsPGroup 2 T) (hBT : B ≤ Subgroup.normalizer (T : Set G)) (hTB : (⁅T, B⁆ : Subgroup G) = T)
    (hTO : ¬ T ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G)))
    (hspade : ∀ A : Subgroup G, A ≤ Subgroup.centralizer ({x} : Set G) ⊓ centModSubgroup p L →
      IsElemAbelian p A → Nat.card A ≤ p) :
    ∃ T₀ : Subgroup G, T₀ ≤ L ∧ IsPGroup 2 T₀ ∧ B ≤ Subgroup.normalizer (T₀ : Set G) ∧
      ¬ T₀ ≤ GLAPPrimeCoreOf p L := by
  have hN := cx_le_normalizer_L hc h hspade
  have hR := pow_mem_core_of_centMod hc h hN hspade
  exact exists_two_group_in_L_of hc hI712 h hN hR hT hT2 hBT hTB hTO

theorem exists_cent_rank_two {p : ℕ} (hc : S9Ctx G p) (hin : Lemma93Inputs G p)
    (hd : dLevel G p ≤ 2) {B : Subgroup G} {x : G} {L : Subgroup G} (h : H92 p B x L)
    (hess : IsEssential p B x) (hmax : IsMaxRankIn p B (Subgroup.centralizer ({x} : Set G)))
    (hnoGB : ¬ IsGB p B L) :
    ∃ A : Subgroup G, A ≤ Subgroup.centralizer ({x} : Set G) ⊓ centModSubgroup p L ∧
      IsElemAbelian p A ∧ p ^ 2 ≤ Nat.card A := by
  by_contra hcon
  push Not at hcon
  have hp := hc.ctx.prime
  have hp2 := hc.ctx.odd
  obtain ⟨T, hTC, hT2, hBT, hTB, hTO⟩ := exists_T_not_le_core hc hd h.bmax hess
  have hspade : ∀ A : Subgroup G, A ≤ Subgroup.centralizer ({x} : Set G) ⊓ centModSubgroup p L →
      IsElemAbelian p A → Nat.card A ≤ p := by
    intro A hA hAel
    by_contra hlt
    push Not at hlt
    obtain ⟨k, hk⟩ := exists_card_eq_pow_of_isElemAbelian hp hAel
    have hk2 : 2 ≤ k := by
      by_contra hk2
      push Not at hk2
      have hk' : k ≤ 1 := by omega
      have h1 : p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos hk'
      rw [pow_one] at h1
      omega
    have hpp : p ^ 2 ≤ Nat.card A := by
      rw [hk]
      exact Nat.pow_le_pow_right hp.pos hk2
    exact absurd (hcon A hA hAel) (not_lt.2 hpp)
  obtain ⟨T₀, hT₀L, hT₀2, hBT₀, hT₀O⟩ :=
    exists_two_group_in_L hc hin.i712 h hTC hT2 hBT hTB hTO hspade
  have hLK : CFSG.Open.IsKGroup ↥L := by
    refine isKGroup_of_isKProper hc.ctx.kProper ?_
    intro htop
    exact (centralizer_ne_top_of_ne_one hc.ctx.simple hc.ctx.nonabelian h.ne_one)
      (top_le_iff.1 (htop ▸ h.comp.1))
  have h4 : p ^ 4 ≤ Nat.card B := h.pow_four_le hc
  exact hnoGB (hin.i264b hp hp2 B x L h.bmax.1 h.mem h.ne_one h.comp hLK h.norm h4
    (fun E hEY hE => hmax E (hEY.trans (sup_le h.comp.1 h.le_cx)) hE) h.chev2
    ⟨T₀, hT₀L, hT₀2, hBT₀, hT₀O⟩)

theorem nonInner_or_center {p : ℕ} (hc : S9Ctx G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    (h : H92 p B x L) (hmax : IsMaxRankIn p B (Subgroup.centralizer ({x} : Set G)))
    (hA : ∃ A : Subgroup G, A ≤ Subgroup.centralizer ({x} : Set G) ⊓ centModSubgroup p L ∧
      IsElemAbelian p A ∧ p ^ 2 ≤ Nat.card A) :
    (∃ b ∈ B, ¬ InducesInnerMod p L b) ∨ p ∣ Nat.card (Subgroup.center (PQuot p L)) := by
  exact l93_nonInner_or_center hc h hmax hA

private theorem lemma93_card_le_of_isCyclic {p : ℕ} (hp : p.Prime) {P E : Subgroup G} (hPc : IsCyclic P)
    (hEP : E ≤ P) (hE : IsElemAbelian p E) : Nat.card E ≤ p := by
  haveI := hPc
  have hdvd : Monoid.exponent (E.subgroupOf P) ∣ p := by
    apply Monoid.exponent_dvd_of_forall_pow_eq_one
    intro h
    apply Subtype.ext
    apply Subtype.ext
    simpa using hE.2 ((h : P) : G) (Subgroup.mem_subgroupOf.1 h.2)
  rw [IsCyclic.exponent_eq_card, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEP).toEquiv] at hdvd
  exact Nat.le_of_dvd hp.pos hdvd

theorem exists_invariant_noncyclic_sylow {p : ℕ} (hp : p.Prime) {B X A : Subgroup G} {x : G}
    (hB : IsElemAbelian p B) (hxB : x ∈ B) (hBX : B ≤ Subgroup.normalizer (X : Set G)) (hxX : x ∈ X)
    (hxc : X ≤ Subgroup.centralizer ({x} : Set G)) (hA : A ≤ X) (hAel : IsElemAbelian p A)
    (hAc : p ^ 2 ≤ Nat.card A) :
    ∃ P : Subgroup G, P ≤ X ∧ IsPGroup p P ∧ B ≤ Subgroup.normalizer (P : Set G) ∧ x ∈ P ∧
      ¬ IsCyclic P := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set Y : Subgroup G := B ⊔ X with hYdef
  have hBY : B ≤ Y := le_sup_left
  have hXY : X ≤ Y := le_sup_right
  have hYN : Y ≤ Subgroup.normalizer (X : Set G) := sup_le hBX Subgroup.le_normalizer
  have hYC : Y ≤ Subgroup.centralizer ({x} : Set G) :=
    sup_le (isElemAbelian_le_centralizer hB hxB) hxc
  have hYX : ∀ y ∈ Y, ∀ g ∈ X, y * g * y⁻¹ ∈ X := fun y hy g hg =>
    (Subgroup.mem_normalizer_iff.1 (hYN hy) g).1 hg
  have hsub : ∀ H : Subgroup G, H ≤ Y → IsElemAbelian p H → IsPGroup p (H.subgroupOf Y) := by
    intro H hHY hH
    exact (isPGroup_of_isElemAbelian hH).of_injective (Subgroup.subgroupOfEquivOfLe hHY).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hHY).injective
  obtain ⟨S, hBS⟩ := (hsub B hBY hB).exists_le_sylow
  set P : Subgroup G := (S : Subgroup Y).map Y.subtype ⊓ X with hPdef
  have hPp : IsPGroup p P := ((S.isPGroup').map Y.subtype).to_inf_left
  have hPX : P ≤ X := inf_le_right
  have hxY : x ∈ Y := hXY hxX
  have hxS : (⟨x, hxY⟩ : Y) ∈ (S : Subgroup Y) := by
    have hN : Subgroup.zpowers x ≤ Y := (Subgroup.zpowers_le).2 hxY
    haveI hNn : ((Subgroup.zpowers x).subgroupOf Y).Normal := by
      constructor
      intro n hn g
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      have hc : Commute ((g : Y) : G) x :=
        Subgroup.mem_centralizer_singleton_iff.1 (hYC g.2)
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hn
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hk, (hc.zpow_right k).eq]
      rw [mul_assoc, mul_inv_cancel, mul_one]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) k
    have hzp : IsPGroup p (Subgroup.zpowers x) := isPGroup_zpowers_of_mem hB hxB
    have hpN : IsPGroup p ((Subgroup.zpowers x).subgroupOf Y) :=
      hzp.of_injective (Subgroup.subgroupOfEquivOfLe hN).toMonoidHom
        (Subgroup.subgroupOfEquivOfLe hN).injective
    exact IsPGroup.le_sylow_of_normal hpN S (Subgroup.mem_subgroupOf.2 (Subgroup.mem_zpowers x))
  have hxP : x ∈ P := ⟨Subgroup.mem_map.2 ⟨⟨x, hxY⟩, hxS, rfl⟩, hxX⟩
  have hBP : B ≤ Subgroup.normalizer (P : Set G) := by
    have hconj : ∀ b ∈ B, ∀ h ∈ P, b * h * b⁻¹ ∈ P := by
      intro b hb h hh
      have hbS : b ∈ (S : Subgroup Y).map Y.subtype :=
        Subgroup.mem_map.2 ⟨⟨b, hBY hb⟩, hBS (Subgroup.mem_subgroupOf.2 hb), rfl⟩
      exact ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hbS hh.1) (Subgroup.inv_mem _ hbS),
        hYX b (hBY hb) h hh.2⟩
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact hconj b hb h hh
    · intro hh
      have h' := hconj b⁻¹ (B.inv_mem hb) _ hh
      have e : b⁻¹ * (b * h * b⁻¹) * b⁻¹⁻¹ = h := by group
      rwa [e] at h'
  refine ⟨P, hPX, hPp, hBP, hxP, ?_⟩
  intro hPc
  obtain ⟨T, hAT⟩ := (hsub A (hA.trans hXY) hAel).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y T S
  have hgX : ∀ a ∈ A, (g : G) * a * (g : G)⁻¹ ∈ X := fun a ha => hYX g g.2 a (hA ha)
  have hgS : ∀ a ∈ A, (g : G) * a * (g : G)⁻¹ ∈ (S : Subgroup Y).map Y.subtype := by
    intro a ha
    have haT : (⟨a, hXY (hA ha)⟩ : Y) ∈ T := hAT (Subgroup.mem_subgroupOf.2 ha)
    have hm := Subgroup.smul_mem_pointwise_smul _ (MulAut.conj g) (T : Subgroup Y) haT
    rw [← Sylow.coe_subgroup_smul, hg] at hm
    exact Subgroup.mem_map.2 ⟨MulAut.conj g ⟨a, hXY (hA ha)⟩, hm, rfl⟩
  set E : Subgroup G := A.map (MulAut.conj (g : G)).toMonoidHom with hEdef
  have hEP : E ≤ P := by
    intro y hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hy
    exact ⟨hgS a ha, hgX a ha⟩
  have hEel : IsElemAbelian p E := by
    have hcomm : ∀ u ∈ E, ∀ v ∈ E, u * v = v * u := by
      intro u hu v hv
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hu
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hv
      have hab : a * b = b * a := isElemAbelian_commute hAel ha hb
      show (MulAut.conj (g : G)) a * (MulAut.conj (g : G)) b =
        (MulAut.conj (g : G)) b * (MulAut.conj (g : G)) a
      simp only [MulAut.conj_apply]
      calc (g : G) * a * (g : G)⁻¹ * ((g : G) * b * (g : G)⁻¹)
          = (g : G) * (a * b) * (g : G)⁻¹ := by group
        _ = (g : G) * (b * a) * (g : G)⁻¹ := by rw [hab]
        _ = (g : G) * b * (g : G)⁻¹ * ((g : G) * a * (g : G)⁻¹) := by group
    refine ⟨⟨⟨fun u v => Subtype.ext (hcomm u.1 u.2 v.1 v.2)⟩⟩, ?_⟩
    intro u hu
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hu
    rw [← MonoidHom.map_pow, hAel.2 a ha, map_one]
  have hcardE : Nat.card E = Nat.card A :=
    Subgroup.card_map_of_injective (f := (MulAut.conj (g : G)).toMonoidHom) (MulAut.conj (g : G)).injective
  have hle := lemma93_card_le_of_isCyclic hp hPc hEP hEel
  rw [hcardE] at hle
  have h2 := hp.two_le
  nlinarith

theorem exists_invariant_elemAbelian_of_noncyclic {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {B P : Subgroup G} {x : G} (hB : IsElemAbelian p B) (hP : IsPGroup p P)
    (hBP : B ≤ Subgroup.normalizer (P : Set G)) (hxP : x ∈ P) (hx1 : x ≠ 1) (hxp : x ^ p = 1)
    (hxc : P ≤ Subgroup.centralizer ({x} : Set G))
    (hxB : B ≤ Subgroup.centralizer ({x} : Set G)) (hnc : ¬ IsCyclic P) :
    ∃ U : Subgroup G, U ≤ P ∧ IsElemAbelian p U ∧ Nat.card U = p ^ 2 ∧ x ∈ U ∧
      B ≤ Subgroup.normalizer (U : Set G) := by
  exact l93_exists_invariant_elemAbelian_of_noncyclic hp hp2 hB hP hBP hxP hx1 hxp hxc hxB hnc

theorem exists_invariant_U {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {B : Subgroup G} {x : G}
    {L A : Subgroup G} (hB : IsElemAbelian p B) (hxB : x ∈ B)
    (hBL : B ≤ Subgroup.normalizer (L : Set G)) (hLx : L ≤ Subgroup.centralizer ({x} : Set G))
    (hx1 : x ≠ 1)
    (hA : A ≤ Subgroup.centralizer ({x} : Set G) ⊓ centModSubgroup p L) (hAel : IsElemAbelian p A)
    (hAc : p ^ 2 ≤ Nat.card A) :
    ∃ U : Subgroup G, U ≤ Subgroup.centralizer ({x} : Set G) ⊓ centModSubgroup p L ∧
      IsElemAbelian p U ∧ Nat.card U = p ^ 2 ∧ x ∈ U ∧ B ≤ Subgroup.normalizer (U : Set G) := by
  have hxc : x ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.1 (hLx hl)
  have hxN : x ∈ Subgroup.normalizer (L : Set G) := Subgroup.centralizer_le_normalizer _ hxc
  have hxX : x ∈ Subgroup.centralizer ({x} : Set G) ⊓ centModSubgroup p L := by
    refine ⟨Subgroup.mem_centralizer_singleton_iff.2 rfl, hxN, fun l hl => ?_⟩
    have hcomm : l * x = x * l := (Subgroup.mem_centralizer_iff.1 hxc l hl)
    have : ⁅l, x⁆ = 1 := by
      rw [commutatorElement_def, hcomm]
      group
    rw [this]
    exact (GLAPPrimeCoreOf p L).one_mem
  have hBX : B ≤ Subgroup.normalizer
      ((Subgroup.centralizer ({x} : Set G) ⊓ centModSubgroup p L : Subgroup G) : Set G) := by
    intro b hb
    have hbN : b ∈ Subgroup.normalizer (L : Set G) := hBL hb
    have hbcm : b ∈ Subgroup.normalizer (centModSubgroup p L : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro a
      constructor
      · exact fun ha => S3.conj_mem_centModSubgroup hbN ha
      · intro ha
        have := S3.conj_mem_centModSubgroup (Subgroup.inv_mem _ hbN) ha
        simpa [mul_assoc] using this
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer (isElemAbelian_le_centralizer hB hxB hb), hbcm⟩
  obtain ⟨P, hPX, hPp, hBP, hxP, hnc⟩ :=
    exists_invariant_noncyclic_sylow hp hB hxB hBX hxX inf_le_left hA hAel hAc
  obtain ⟨U, hUP, hUel, hUc, hxU, hBU⟩ := exists_invariant_elemAbelian_of_noncyclic hp hp2 hB hPp hBP
    hxP hx1 (hB.2 x hxB) (fun g hg => (hPX hg).1)
    (fun b hb => Subgroup.mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff.1 hh]; exact isElemAbelian_commute hB hxB hb) hnc
  exact ⟨U, hUP.trans hPX, hUel, hUc, hxU, hBU⟩

private abbrev lemma93Act {B U : Subgroup G} (hBU : B ≤ Subgroup.normalizer (U : Set G)) :
    MulAction B U where
  smul b u := ⟨(b : G) * u * (b : G)⁻¹, (Subgroup.mem_normalizer_iff.1 (hBU b.2) u).1 u.2⟩
  one_smul u := Subtype.ext (by
    show ((1 : B) : G) * (u : G) * ((1 : B) : G)⁻¹ = (u : G)
    simp)
  mul_smul b b' u := Subtype.ext (by
    show ((b * b' : B) : G) * (u : G) * ((b * b' : B) : G)⁻¹ =
      (b : G) * ((b' : G) * (u : G) * (b' : G)⁻¹) * (b : G)⁻¹
    simp [mul_assoc])

private theorem lemma93_index_le {p : ℕ} (hp : p.Prime) {B U : Subgroup G}
    (hB : IsElemAbelian p B) (hU : IsElemAbelian p U) (hUc : Nat.card U = p ^ 2)
    (hBU : B ≤ Subgroup.normalizer (U : Set G)) :
    Nat.card B ≤ p * Nat.card ↥(B ⊓ Subgroup.centralizer (U : Set G)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  letI : MulAction B U := lemma93Act hBU
  have hBp : IsPGroup p B := isPGroup_of_isElemAbelian hB
  have hmemF : ∀ u : U, u ∈ MulAction.fixedPoints B U ↔
      ∀ b : B, (b : G) * (u : G) * (b : G)⁻¹ = u := by
    intro u
    rw [MulAction.mem_fixedPoints]
    constructor
    · intro h b
      exact congrArg Subtype.val (h b)
    · intro h b
      exact Subtype.ext (h b)
  have hcong := hBp.card_modEq_card_fixedPoints U
  have h1F : (1 : U) ∈ MulAction.fixedPoints B U := (hmemF 1).2 (fun b => by simp)
  have hpU : p ∣ Nat.card U := by rw [hUc]; exact dvd_pow_self p two_ne_zero
  have hpF : p ∣ Nat.card (MulAction.fixedPoints B U) := by
    have h0 : Nat.card U % p = 0 := Nat.mod_eq_zero_of_dvd hpU
    unfold Nat.ModEq at hcong
    exact Nat.dvd_of_mod_eq_zero (by omega)
  haveI : Nonempty (MulAction.fixedPoints B U) := ⟨⟨1, h1F⟩⟩
  have hpFle : p ≤ Nat.card (MulAction.fixedPoints B U) :=
    Nat.le_of_dvd (Nat.card_pos) hpF
  by_cases hall : ∀ u : U, u ∈ MulAction.fixedPoints B U
  ·
    have hBC : B ⊓ Subgroup.centralizer (U : Set G) = B := by
      apply inf_eq_left.2
      intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have := (hmemF ⟨u, hu⟩).1 (hall _) ⟨b, hb⟩
      exact (mul_inv_eq_iff_eq_mul.1 this).symm
    rw [hBC]
    exact Nat.le_mul_of_pos_left _ hp.pos
  · push Not at hall
    obtain ⟨v, hv⟩ := hall
    have hfixb : ∀ w ∈ MulAction.fixedPoints B U, ∀ k : ℤ, ∀ b : B,
        (b : G) * ((w : U) : G) ^ k * (b : G)⁻¹ = ((w : U) : G) ^ k := by
      intro w hw k b
      rw [← conj_zpow, ((hmemF w).1 hw) b]
    obtain ⟨f, hf, hf1⟩ : ∃ f ∈ MulAction.fixedPoints B U, f ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have hsub : MulAction.fixedPoints B U ⊆ {1} := fun g hg => hcon g hg
      have h1 : (MulAction.fixedPoints B U).ncard ≤ ({1} : Set U).ncard :=
        Set.ncard_le_ncard hsub (Set.finite_singleton _)
      rw [Set.ncard_singleton, ← Nat.card_coe_set_eq] at h1
      have := hp.two_le
      omega
    have hdisj : Disjoint (MulAction.orbit B v : Set U) (MulAction.fixedPoints B U) := by
      rw [Set.disjoint_left]
      intro w hw hwF
      obtain ⟨b, rfl⟩ := MulAction.mem_orbit_iff.1 hw
      apply hv
      have h1 : b⁻¹ • (b • v) = b • v := MulAction.mem_fixedPoints.1 hwF b⁻¹
      have h2 : b⁻¹ • (b • v) = v := by rw [← mul_smul, inv_mul_cancel, one_smul]
      rw [← h2, h1]
      exact hwF
    have hcardsum : Nat.card (MulAction.orbit B v) + Nat.card (MulAction.fixedPoints B U) ≤
        Nat.card U := by
      rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, ← Set.ncard_univ,
        ← Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)]
      exact Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)
    obtain ⟨n, hn⟩ := hBp.card_orbit v
    have hpow : n ≤ 1 := by
      by_contra hcon
      push Not at hcon
      have h2 : p ^ 2 ≤ p ^ n := Nat.pow_le_pow_right hp.pos hcon
      rw [hn, hUc] at hcardsum
      have := hp.two_le
      linarith
    have hcard : Nat.card (MulAction.orbit B v) ≤ p := by
      rw [hn]
      calc p ^ n ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos hpow
        _ = p := pow_one p
    have hidx : (MulAction.stabilizer B v).index ≤ p := by
      rw [MulAction.index_stabilizer]
      exact hcard
    have hvf : (v : G) ∉ Subgroup.zpowers (f : G) := by
      intro hmem
      apply hv
      rw [hmemF]
      intro b
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
      rw [← hk, ← conj_zpow, (hmemF f).1 hf b]
    have hfpow : (f : G) ^ p = 1 := hU.2 _ f.2
    have hfne : (f : G) ≠ 1 := fun h => hf1 (Subtype.ext h)
    have hord : Nat.card (Subgroup.zpowers (f : G)) = p := by
      rw [Nat.card_zpowers, orderOf_eq_prime hfpow hfne]
    have hstab : ∀ c ∈ MulAction.stabilizer B v, (c : G) ∈ Subgroup.centralizer (U : Set G) := by
      intro c hc
      rw [MulAction.mem_stabilizer_iff] at hc
      have hcv : (c : G) * (v : G) * (c : G)⁻¹ = v := congrArg Subtype.val hc
      have hcf : (c : G) * (f : G) * (c : G)⁻¹ = f := (hmemF f).1 hf c
      have hcomf : (c : G) * (f : G) = (f : G) * (c : G) := mul_inv_eq_iff_eq_mul.1 hcf
      have hcomv : (c : G) * (v : G) = (v : G) * (c : G) := mul_inv_eq_iff_eq_mul.1 hcv
      set W : Subgroup G := U ⊓ Subgroup.centralizer ({(c : G)} : Set G) with hWdef
      have hfW : (f : G) ∈ W :=
        ⟨f.2, Subgroup.mem_centralizer_singleton_iff.2 hcomf.symm⟩
      have hvW : (v : G) ∈ W :=
        ⟨v.2, Subgroup.mem_centralizer_singleton_iff.2 hcomv.symm⟩
      have hzW : Subgroup.zpowers (f : G) ≤ W := Subgroup.zpowers_le.2 hfW
      have hWU : W ≤ U := inf_le_left
      have hdvd : Nat.card W ∣ p ^ 2 := by
        rw [← hUc]
        exact Subgroup.card_dvd_of_le hWU
      obtain ⟨i, hi, hWi⟩ := (Nat.dvd_prime_pow hp).1 hdvd
      have hle : p ≤ Nat.card W := by
        rw [← hord]
        exact Subgroup.card_le_of_le hzW
      interval_cases i
      · have := hp.two_le
        rw [pow_zero] at hWi
        omega
      ·
        exfalso
        have heq : Subgroup.zpowers (f : G) = W :=
          Subgroup.eq_of_le_of_card_ge hzW (by rw [hord, hWi, pow_one])
        exact hvf (heq ▸ hvW)
      ·
        have heq : W = U := Subgroup.eq_of_le_of_card_ge hWU (le_of_eq (by rw [hUc, hWi]))
        rw [Subgroup.mem_centralizer_iff]
        intro u hu
        have huW : u ∈ W := by
          rw [heq]
          exact hu
        exact Subgroup.mem_centralizer_singleton_iff.1 huW.2
    have hKle : MulAction.stabilizer B v ≤ (B ⊓ Subgroup.centralizer (U : Set G)).subgroupOf B := by
      intro c hc
      rw [Subgroup.mem_subgroupOf]
      exact ⟨c.2, hstab c hc⟩
    have hKidx : ((B ⊓ Subgroup.centralizer (U : Set G)).subgroupOf B).index ≤ p := by
      have hd := Subgroup.index_dvd_of_le hKle
      have hpos : (MulAction.stabilizer B v).index ≠ 0 := Subgroup.index_ne_zero_of_finite
      exact le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hpos) hd) hidx
    have hKc : Nat.card ↥((B ⊓ Subgroup.centralizer (U : Set G)).subgroupOf B) =
        Nat.card ↥(B ⊓ Subgroup.centralizer (U : Set G)) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    have hmul := ((B ⊓ Subgroup.centralizer (U : Set G)).subgroupOf B).index_mul_card
    rw [hKc] at hmul
    rw [← hmul]
    exact Nat.mul_le_mul_right _ hKidx

theorem bstar_facts {p : ℕ} (hp : p.Prime) {B : Subgroup G} {x : G} {L U : Subgroup G}
    (hB : IsElemAbelian p B) (hxB : x ∈ B) (hBL : B ≤ Subgroup.normalizer (L : Set G))
    (hmax : IsMaxRankIn p B (Subgroup.centralizer ({x} : Set G)))
    (hcent : CentModEqZpowers p B L x)
    (hU : U ≤ Subgroup.centralizer ({x} : Set G) ⊓ centModSubgroup p L) (hUel : IsElemAbelian p U)
    (hUc : Nat.card U = p ^ 2) (hxU : x ∈ U) (hBU : B ≤ Subgroup.normalizer (U : Set G))
    (h4 : p ^ 4 ≤ Nat.card B) :
    IsElemAbelian p (bstar B U) ∧ bstar B U ≤ Subgroup.centralizer ({x} : Set G) ∧
      bstar B U ≤ Subgroup.normalizer (L : Set G) ∧ bstar B U ≤ Subgroup.centralizer (U : Set G) ∧
      Nat.card (bstar B U) = Nat.card B ∧
      Nat.card B ≤ p * Nat.card ↥(B ⊓ bstar B U) ∧ ¬ bstar B U ≤ centModSubgroup p L := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hBC : B ≤ Subgroup.centralizer ({x} : Set G) := isElemAbelian_le_centralizer hB hxB
  set K : Subgroup G := B ⊓ Subgroup.centralizer (U : Set G) with hKdef
  have hKB : K ≤ B := inf_le_left
  have hKC : ∀ k ∈ K, ∀ u ∈ U, k * u = u * k := fun k hk u hu =>
    ((Subgroup.mem_centralizer_iff.1 hk.2) u hu).symm
  have hKN : K ≤ Subgroup.normalizer (U : Set G) :=
    inf_le_right.trans (Subgroup.centralizer_le_normalizer _)
  have hsup : ∀ w ∈ bstar B U, ∃ k ∈ K, ∃ u ∈ U, k * u = w := fun w hw =>
    lemma93_mem_sup_of_le_normalizer hKN hw
  have hcomm : ∀ w ∈ bstar B U, ∀ w' ∈ bstar B U, w * w' = w' * w := by
    intro w hw w' hw'
    obtain ⟨k, hk, u, hu, rfl⟩ := hsup w hw
    obtain ⟨k', hk', u', hu', rfl⟩ := hsup w' hw'
    have hkk' : k * k' = k' * k := isElemAbelian_commute hB hk.1 hk'.1
    have huu' : u * u' = u' * u := isElemAbelian_commute hUel hu hu'
    have hku' : k * u' = u' * k := hKC k hk u' hu'
    have hk'u : k' * u = u * k' := hKC k' hk' u hu
    calc k * u * (k' * u') = k * (u * k') * u' := by group
      _ = k * (k' * u) * u' := by rw [← hk'u]
      _ = (k * k') * (u * u') := by group
      _ = (k' * k) * (u' * u) := by rw [hkk', huu']
      _ = k' * (k * u') * u := by group
      _ = k' * (u' * k) * u := by rw [hku']
      _ = (k' * u') * (k * u) := by group
  have hbEl : IsElemAbelian p (bstar B U) := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hcomm a.1 a.2 b.1 b.2)⟩⟩, ?_⟩
    intro w hw
    obtain ⟨k, hk, u, hu, rfl⟩ := hsup w hw
    have hku : Commute k u := hKC k hk u hu
    rw [hku.mul_pow, hB.2 k hk.1, hUel.2 u hu, one_mul]
  have hbC : bstar B U ≤ Subgroup.centralizer ({x} : Set G) :=
    sup_le (hKB.trans hBC) (hU.trans inf_le_left)
  have hbL : bstar B U ≤ Subgroup.normalizer (L : Set G) :=
    sup_le (hKB.trans hBL) (fun u hu => (hU hu).2.1)
  have hbU : bstar B U ≤ Subgroup.centralizer (U : Set G) :=
    sup_le inf_le_right (fun u hu => Subgroup.mem_centralizer_iff.2 (fun v hv =>
      (isElemAbelian_commute hUel hv hu)))
  have hzp : Nat.card (Subgroup.zpowers x) ≤ p := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one (hB.2 x hxB))
  have hUK : U ⊓ K ≤ Subgroup.zpowers x := by
    intro w hw
    exact (hcent w hw.2.1).1 (centMod_iff.2 ((hU hw.1).2))
  have hUint : Nat.card ↥(U ⊓ K) ≤ p :=
    (Subgroup.card_le_of_le hUK).trans hzp
  have hcf := card_sup_mul_card_inf_of_le_normalizer hKN
  rw [sup_comm, hUc] at hcf
  have hlow : p * Nat.card K ≤ Nat.card (bstar B U) := by
    have h1 : p * (p * Nat.card K) ≤ p * Nat.card (bstar B U) := by
      calc p * (p * Nat.card K) = p ^ 2 * Nat.card K := by ring
        _ = Nat.card (bstar B U) * Nat.card ↥(U ⊓ K) := hcf.symm
        _ ≤ Nat.card (bstar B U) * p := Nat.mul_le_mul_left _ hUint
        _ = p * Nat.card (bstar B U) := mul_comm _ _
    exact Nat.le_of_mul_le_mul_left h1 hp.pos
  have hidx := lemma93_index_le hp hB hUel hUc hBU
  have heqcard : Nat.card (bstar B U) = Nat.card B :=
    le_antisymm (hmax (bstar B U) hbC hbEl) (hidx.trans (le_trans (Nat.mul_le_mul_left p le_rfl) hlow))
  refine ⟨hbEl, hbC, hbL, hbU, heqcard, ?_, ?_⟩
  ·
    have hKle : K ≤ B ⊓ bstar B U := le_inf inf_le_left le_sup_left
    exact hidx.trans (Nat.mul_le_mul_left p (Subgroup.card_le_of_le hKle))
  · intro hcm
    have hBint : Nat.card ↥(B ⊓ bstar B U) ≤ p := by
      have hle : B ⊓ bstar B U ≤ Subgroup.zpowers x := by
        intro b hb
        exact (hcent b hb.1).1 (centMod_iff.2 (hcm hb.2))
      exact (Subgroup.card_le_of_le hle).trans hzp
    have hKle : K ≤ B ⊓ bstar B U := le_inf inf_le_left le_sup_left
    have hKp : Nat.card K ≤ p := (Subgroup.card_le_of_le hKle).trans hBint
    have hB2 : Nat.card B ≤ p * p := hidx.trans (Nat.mul_le_mul_left p hKp)
    have := hp.two_le
    have h4' : p ^ 4 ≤ p * p := h4.trans hB2
    have hpp : 4 ≤ p * p := by nlinarith
    have h6 : (p * p) * 4 ≤ (p * p) * (p * p) := Nat.mul_le_mul_left _ hpp
    have h7 : (p * p) * (p * p) = p ^ 4 := by ring
    linarith

structure Stage93 (p : ℕ) (B : Subgroup G) (x : G) (L U N : Subgroup G) : Prop where
  U_le : U ≤ Subgroup.centralizer ({x} : Set G) ⊓ centModSubgroup p L
  U_el : IsElemAbelian p U
  U_card : Nat.card U = p ^ 2
  x_mem : x ∈ U
  B_U : B ≤ Subgroup.normalizer (U : Set G)
  Bs_el : IsElemAbelian p (bstar B U)
  Bs_bmax : GLAIsBmax p (bstar B U)
  Bs_le_N : bstar B U ≤ N
  N_two : IsTwoLocal N
  N_cov : Covers p N (Subgroup.centralizer ({x} : Set G))
  Bs_norm : bstar B U ≤ Subgroup.normalizer (L : Set G)
  Bs_cent_U : bstar B U ≤ Subgroup.centralizer (U : Set G)
  Bs_le_C : bstar B U ≤ Subgroup.centralizer ({x} : Set G)
  idx : Nat.card B ≤ p * Nat.card ↥(B ⊓ bstar B U)
  not_cent : ¬ bstar B U ≤ centModSubgroup p L

theorem exists_stage93 {p : ℕ} (hc : S9Ctx G p) {B : Subgroup G} {x : G} {L N : Subgroup G}
    (h : H92 p B x L) (hN : IsTwoLocal N) (hcov : Covers p N (Subgroup.centralizer ({x} : Set G)))
    (hmax : IsMaxRankIn p B (Subgroup.centralizer ({x} : Set G)))
    (hA : ∃ A : Subgroup G, A ≤ Subgroup.centralizer ({x} : Set G) ⊓ centModSubgroup p L ∧
      IsElemAbelian p A ∧ p ^ 2 ≤ Nat.card A) :
    ∃ U N' : Subgroup G, Stage93 p B x L U N' := by
  have hp := hc.ctx.prime
  have hp2 := hc.ctx.odd
  obtain ⟨A, hAle, hAel, hAc⟩ := hA
  obtain ⟨U, hU, hUel, hUc, hxU, hBU⟩ :=
    exists_invariant_U hp hp2 h.bmax.1 h.mem h.norm h.comp.1 h.ne_one hAle hAel hAc
  obtain ⟨hBsel, hBsC, hBsL, hBsU, hBsc, hidx, hnot⟩ :=
    bstar_facts hp h.bmax.1 h.mem h.norm hmax h.cent hU hUel hUc hxU hBU (h.pow_four_le hc)
  obtain ⟨N', hN', hcov', hBsN'⟩ :=
    exists_covers_conj hp (isPGroup_of_isElemAbelian hBsel) hBsC hN hcov
  refine ⟨U, N', ⟨hU, hUel, hUc, hxU, hBU, hBsel, ?_, hBsN', hN', hcov', hBsL, hBsU, hBsC, hidx,
    hnot⟩⟩
  exact isBmax_of_covers hp h.bmax hBsC hBsel hBsc hN' hcov'

private theorem l93c_fixed_of_coset {p : ℕ} [Fact p.Prime] {P : Subgroup G} (hP : IsPGroup p P)
    (T : Set G) (hT : ∀ g ∈ P, ∀ t ∈ T, g * t * g⁻¹ ∈ T) (hcard : ¬ p ∣ Nat.card ↥T) :
    ∃ t ∈ T, ∀ g ∈ P, g * t * g⁻¹ = t := by
  letI : MulAction ↥P ↥T :=
    { smul := fun g t => ⟨(g : G) * t * (g : G)⁻¹, hT g g.2 t t.2⟩
      one_smul := fun t => Subtype.ext (by
        change ((1 : ↥P) : G) * (t : G) * ((1 : ↥P) : G)⁻¹ = (t : G)
        simp)
      mul_smul := fun g h t => Subtype.ext (by
        change ((g * h : ↥P) : G) * (t : G) * ((g * h : ↥P) : G)⁻¹ =
          (g : G) * ((h : G) * (t : G) * (h : G)⁻¹) * (g : G)⁻¹
        simp [mul_assoc]) }
  have hG : IsPGroup p ↥P := hP
  obtain ⟨t, ht⟩ := IsPGroup.nonempty_fixed_point_of_prime_not_dvd_card hG (↥T) hcard
  refine ⟨t, t.2, fun g hg => ?_⟩
  have h := (MulAction.mem_fixedPoints.1 ht) ⟨g, hg⟩
  have h' := congrArg Subtype.val h
  exact h'

private theorem l93c_le_glaPPrimeCoreOf {p : ℕ} {X M : Subgroup G} (hMX : M ≤ X)
    (hMn : (M.subgroupOf X).Normal) (hcop : Nat.Coprime p (Nat.card ↥M)) :
    M ≤ GLAPPrimeCoreOf p X := by
  have hcard : Nat.Coprime p (Nat.card ↥(M.subgroupOf X)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMX).toEquiv]
    exact hcop
  have hsub : M.subgroupOf X ≤ GLAPPrimeCore p ↥X := by
    unfold GLAPPrimeCore CFSG.pPrimeCore
    exact le_sSup ⟨hMn, hcard⟩
  intro m hm
  exact ⟨⟨m, hMX hm⟩, hsub (Subgroup.mem_subgroupOf.2 hm), rfl⟩

private theorem l93c_conj_mem_centralizer {U : Subgroup G} {g c : G}
    (hg : g ∈ Subgroup.centralizer (U : Set G)) (hc : c ∈ Subgroup.centralizer (U : Set G)) :
    g * c * g⁻¹ ∈ Subgroup.centralizer (U : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hc hg ⊢
  intro u hu
  have h1 : u * g = g * u := hg u hu
  have h2 : u * c = c * u := hc u hu
  have h3 : u * g⁻¹ = g⁻¹ * u := by
    calc u * g⁻¹ = g⁻¹ * (g * u) * g⁻¹ := by group
      _ = g⁻¹ * (u * g) * g⁻¹ := by rw [h1]
      _ = g⁻¹ * u := by group
  calc u * (g * c * g⁻¹) = (u * g) * c * g⁻¹ := by group
    _ = (g * u) * c * g⁻¹ := by rw [h1]
    _ = g * (u * c) * g⁻¹ := by group
    _ = g * (c * u) * g⁻¹ := by rw [h2]
    _ = g * c * (u * g⁻¹) := by group
    _ = g * c * (g⁻¹ * u) := by rw [h3]
    _ = (g * c * g⁻¹) * u := by group

private theorem l93c_mem_normalizer_centralizer {U : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.centralizer (U : Set G)) :
    g ∈ Subgroup.normalizer (Subgroup.centralizer (U : Set G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro c
  constructor
  · exact fun hc => l93c_conj_mem_centralizer hg hc
  · intro hc
    have hinv : g⁻¹ ∈ Subgroup.centralizer (U : Set G) := Subgroup.inv_mem _ hg
    have := l93c_conj_mem_centralizer hinv hc
    simpa [mul_assoc] using this

private theorem l93c_isSubnormal_sup {A B : Subgroup G} (h : IsSubnormal A B) :
    ∀ N : Subgroup G, N ≤ B → (N.subgroupOf B).Normal → IsSubnormal (A ⊔ N) B := by
  induction h with
  | refl H =>
    intro N hNH _
    rw [sup_eq_left.2 hNH]
    exact IsSubnormal.refl _
  | @step H M K hHM hHMn hMK ih =>
    intro N hNK hNn
    have hMK' : M ≤ K := isSubnormal_le' hMK
    have hNM : (N.subgroupOf K).Normal := hNn
    have hMN : M ≤ Subgroup.normalizer (N : Set G) := by
      have := (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).1 hNn
      exact hMK'.trans this
    have hMH : M ≤ Subgroup.normalizer (H : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hHM).1 hHMn
    have hHN : (H ⊔ N : Subgroup G) ≤ M ⊔ N := sup_le_sup hHM le_rfl
    have hnorm : (M ⊔ N : Subgroup G) ≤ Subgroup.normalizer ((H ⊔ N : Subgroup G) : Set G) := by
      apply sup_le
      · exact fun m hm => Subgroup.inf_normalizer_le_normalizer_sup H N ⟨hMH hm, hMN hm⟩
      · exact fun n hn => Subgroup.le_normalizer (Subgroup.mem_sup_right hn)
    have hstep : IsSubnormal (H ⊔ N) (M ⊔ N) :=
      IsSubnormal.step hHN ((Subgroup.normal_subgroupOf_iff_le_normalizer hHN).2 hnorm)
        (IsSubnormal.refl _)
    exact isSubnormal_trans' hstep (ih N hNK hNn)

private theorem l93c_mem_normalizer_inf {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro y
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hA y, hB y]

private theorem l93c_cover_cu {p : ℕ} (hp : p.Prime) {x : G} {N U : Subgroup G}
    (hU : IsPGroup p U) (hUC : U ≤ Subgroup.centralizer ({x} : Set G))
    (hCUC : Subgroup.centralizer (U : Set G) ≤ Subgroup.centralizer ({x} : Set G))
    (hUN : U ≤ N) (hcov : Covers p N (Subgroup.centralizer ({x} : Set G))) :
    (N ⊓ Subgroup.centralizer (U : Set G)) ⊔
      GLAPPrimeCoreOf p (Subgroup.centralizer (U : Set G)) = Subgroup.centralizer (U : Set G) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set C := Subgroup.centralizer ({x} : Set G) with hCdef
  set CU := Subgroup.centralizer (U : Set G) with hCUdef
  set O := GLAPPrimeCoreOf p C with hOdef
  have hcov' : (N ⊓ C) ⊔ O = C := hcov
  have hOn : ∀ g ∈ C, g ∈ Subgroup.normalizer (O : Set G) := fun g hg =>
    le_normalizer_glaPPrimeCoreOf p C hg
  have hcopO : Nat.Coprime p (Nat.card ↥O) :=
    CFSG.HardMathSupport.Solomon.Coordinator.i183_coprime_card_glaPPrimeCoreOf hp C
  apply le_antisymm
  · exact sup_le inf_le_right (Subgroup.map_subtype_le _)
  intro c hc
  have hcC : c ∈ C := hCUC hc
  have hc2 : c ∈ (N ⊓ C) ⊔ O := by
    rw [hcov']
    exact hcC
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right (N ⊓ C) O
    (fun g hg => hOn g (Subgroup.mem_inf.1 hg).2)] at hc2
  obtain ⟨n₀, hn₀, o₀, ho₀, hno⟩ := Set.mem_mul.mp hc2
  set T : Set G := {t | t ∈ N ⊓ C ∧ t⁻¹ * c ∈ O} with hTdef
  have hn₀T : n₀ ∈ T := ⟨hn₀, by rw [← hno, inv_mul_cancel_left]; exact ho₀⟩
  have hT : ∀ g ∈ U, ∀ t ∈ T, g * t * g⁻¹ ∈ T := by
    intro g hg t ht
    have hgC : g ∈ C := hUC hg
    have hgNC : g ∈ N ⊓ C := ⟨hUN hg, hgC⟩
    refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hgNC ht.1) (Subgroup.inv_mem _ hgNC), ?_⟩
    have hcomm : g * c = c * g := (Subgroup.mem_centralizer_iff.1 hc) g hg
    have hgc : g⁻¹ * c = c * g⁻¹ := by
      calc g⁻¹ * c = g⁻¹ * (c * g) * g⁻¹ := by group
        _ = g⁻¹ * (g * c) * g⁻¹ := by rw [hcomm]
        _ = c * g⁻¹ := by group
    have hkey : (g * t * g⁻¹)⁻¹ * c = g * (t⁻¹ * c) * g⁻¹ := by
      calc (g * t * g⁻¹)⁻¹ * c = g * t⁻¹ * (g⁻¹ * c) := by group
        _ = g * t⁻¹ * (c * g⁻¹) := by rw [hgc]
        _ = g * (t⁻¹ * c) * g⁻¹ := by group
    rw [hkey]
    exact (Subgroup.mem_normalizer_iff.1 (hOn g hgC) (t⁻¹ * c)).1 ht.2
  have hcard : ¬ p ∣ Nat.card ↥T := by
    have hmemT : ∀ q ∈ (N ⊓ C) ⊓ O, n₀ * q ∈ T := by
      intro q hq
      obtain ⟨hq1, hq2⟩ := Subgroup.mem_inf.1 hq
      refine ⟨(N ⊓ C).mul_mem hn₀ hq1, ?_⟩
      have e : (n₀ * q)⁻¹ * c = q⁻¹ * o₀ := by
        rw [← hno]
        group
      rw [e]
      exact O.mul_mem (O.inv_mem hq2) ho₀
    have hbij : Function.Bijective
        (fun q : ↥((N ⊓ C) ⊓ O) => (⟨n₀ * (q : G), hmemT q q.2⟩ : ↥T)) := by
      constructor
      · intro a b hab
        have h1 : n₀ * (a : G) = n₀ * (b : G) := congrArg Subtype.val hab
        exact Subtype.ext (mul_left_cancel h1)
      · rintro ⟨t, ht⟩
        have hq : n₀⁻¹ * t ∈ (N ⊓ C) ⊓ O := by
          refine Subgroup.mem_inf.2 ⟨(N ⊓ C).mul_mem ((N ⊓ C).inv_mem hn₀) ht.1, ?_⟩
          have e : n₀⁻¹ * t = o₀ * (t⁻¹ * c)⁻¹ := by
            rw [← hno]
            group
          rw [e]
          exact O.mul_mem ho₀ (O.inv_mem ht.2)
        exact ⟨⟨n₀⁻¹ * t, hq⟩, Subtype.ext (by simp)⟩
    have heq : Nat.card ↥T = Nat.card ↥((N ⊓ C) ⊓ O) :=
      (Nat.card_congr (Equiv.ofBijective _ hbij)).symm
    rw [heq]
    have hdvd : Nat.card ↥((N ⊓ C) ⊓ O) ∣ Nat.card ↥O :=
      Subgroup.card_dvd_of_le (inf_le_right : (N ⊓ C) ⊓ O ≤ O)
    exact (Nat.Prime.coprime_iff_not_dvd hp).1 (Nat.Coprime.coprime_dvd_right hdvd hcopO)
  obtain ⟨t, htT, htfix⟩ := l93c_fixed_of_coset hU T hT hcard
  have htCU : t ∈ CU := by
    rw [hCUdef, Subgroup.mem_centralizer_iff]
    intro h hh
    have h1 := htfix h hh
    calc h * t = (h * t * h⁻¹) * h := by group
      _ = t * h := by rw [h1]
  have hoCU : t⁻¹ * c ∈ CU := CU.mul_mem (CU.inv_mem htCU) hc
  have hcopOC : Nat.Coprime p (Nat.card ↥(O ⊓ CU)) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le (inf_le_left : O ⊓ CU ≤ O)) hcopO
  have hnormOC : ((O ⊓ CU).subgroupOf CU).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer (inf_le_right : O ⊓ CU ≤ CU)]
    intro g hg
    have hgC : g ∈ C := hCUC hg
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hO := Subgroup.mem_normalizer_iff.1 (hOn g hgC) y
    have hCU' := Subgroup.mem_normalizer_iff.1 (l93c_mem_normalizer_centralizer hg) y
    constructor
    · intro hy
      exact Subgroup.mem_inf.2 ⟨hO.1 (Subgroup.mem_inf.1 hy).1, hCU'.1 (Subgroup.mem_inf.1 hy).2⟩
    · intro hy
      exact Subgroup.mem_inf.2 ⟨hO.2 (Subgroup.mem_inf.1 hy).1, hCU'.2 (Subgroup.mem_inf.1 hy).2⟩
  have hO' : t⁻¹ * c ∈ GLAPPrimeCoreOf p CU :=
    l93c_le_glaPPrimeCoreOf inf_le_right hnormOC hcopOC (Subgroup.mem_inf.2 ⟨htT.2, hoCU⟩)
  have hmem := Subgroup.mul_mem_sup (Subgroup.mem_inf.2 ⟨htT.1.1, htCU⟩ : t ∈ N ⊓ CU) hO'
  have hdecomp : t * (t⁻¹ * c) = c := by group
  rwa [hdecomp] at hmem

theorem exists_cover_component {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {x : G} {L U N Bs : Subgroup G}
    (hL : GLAPComponent p (Subgroup.centralizer ({x} : Set G)) L)
    (hU : U ≤ Subgroup.centralizer ({x} : Set G) ⊓ centModSubgroup p L) (hUel : IsElemAbelian p U)
    (hxU : x ∈ U) (hUN : U ≤ N) (hcov : Covers p N (Subgroup.centralizer ({x} : Set G)))
    (hBsL : Bs ≤ Subgroup.normalizer (L : Set G)) (hBsU : Bs ≤ Subgroup.centralizer (U : Set G))
    (hBsN : Bs ≤ N) :
    ∃ I : Subgroup G, GLAPComponent p (N ⊓ Subgroup.centralizer (U : Set G)) I ∧ I ≤ L ∧
      I ⊔ GLAPPrimeCoreOf p L = L ∧ Bs ≤ Subgroup.normalizer (I : Set G) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hUp : IsPGroup p U := isPGroup_of_isElemAbelian hUel
  set C := Subgroup.centralizer ({x} : Set G) with hCdef
  set CU := Subgroup.centralizer (U : Set G) with hCUdef
  set O' := GLAPPrimeCoreOf p CU with hO'def
  have hUC : U ≤ C := fun u hu => (hU hu).1
  have hCUC : CU ≤ C := by
    intro g hg
    rw [hCdef, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.1 hh]
    exact (Subgroup.mem_centralizer_iff.1 hg) x hxU
  have hcopO' : Nat.Coprime p (Nat.card ↥O') :=
    CFSG.HardMathSupport.Solomon.Coordinator.i183_coprime_card_glaPPrimeCoreOf hp CU
  have hCUN : CU ≤ Subgroup.normalizer (O' : Set G) := fun g hg =>
    normalizer_le_normalizer_glaPPrimeCoreOf p CU (Subgroup.le_normalizer hg)
  have hDcov : (N ⊓ CU) ⊔ O' = CU := l93c_cover_cu hp hUp hUC hCUC hUN hcov
  have hcmU : ∀ d ∈ U, CentMod p L d := fun d hd => centMod_iff.2 (hU hd).2
  have hY₀cov : (L ⊓ CU) ⊔ GLAPPrimeCoreOf p L = L := by
    refine CFSG.LocalAnalysis.GLTheoremA.S3.eq_inf_centralizer_sup_of_pgroup hp hUp
      (Subgroup.map_subtype_le _)
      (fun d hd => normalizer_le_normalizer_glaPPrimeCoreOf p L ((hcmU d hd).1)) ?_ ?_
    · exact CFSG.HardMathSupport.Solomon.Coordinator.i183_coprime_card_glaPPrimeCoreOf hp L
    · intro y hy d hd
      exact (hcmU d hd).2 (Subgroup.commutator_mem_commutator hy (Subgroup.mem_zpowers d))
  obtain ⟨hO₀, ⟨e₀⟩⟩ := cover_facts hp (inf_le_left : L ⊓ CU ≤ L) hY₀cov
  have hY₀q : CFSG.Open.IsQuasisimple (PQuot p (L ⊓ CU)) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e₀.symm
      (isQuasisimple_pQuot_of_glaPComponent hp hL)
  obtain ⟨hI₁c, hI₁uniq, hI₁bar⟩ := glaPLayer_of_isQuasisimple hY₀q
  set Y₀ := L ⊓ CU with hY₀def
  set I₁ := GLAPLayer p Y₀ with hI₁def
  have hI₁Y₀ : I₁ ≤ Y₀ := hI₁c.1
  have hI₁cov : I₁ ⊔ GLAPPrimeCoreOf p Y₀ = Y₀ :=
    sup_glaPPrimeCoreOf_eq_of_barX_eq_top hI₁Y₀ hI₁bar
  have hO₀le : GLAPPrimeCoreOf p Y₀ ≤ GLAPPrimeCoreOf p L :=
    (le_of_eq hO₀).trans inf_le_right
  have hI₁L : I₁ ⊔ GLAPPrimeCoreOf p L = L := by
    have hY₀le : Y₀ ≤ I₁ ⊔ GLAPPrimeCoreOf p L :=
      calc Y₀ = I₁ ⊔ GLAPPrimeCoreOf p Y₀ := hI₁cov.symm
        _ ≤ I₁ ⊔ GLAPPrimeCoreOf p L := sup_le_sup_left hO₀le _
    apply le_antisymm (sup_le (hI₁Y₀.trans inf_le_left) (Subgroup.map_subtype_le _))
    calc L = Y₀ ⊔ GLAPPrimeCoreOf p L := hY₀cov.symm
      _ ≤ I₁ ⊔ GLAPPrimeCoreOf p L := sup_le hY₀le le_sup_right
  have hI₁L_le : I₁ ≤ L := hI₁Y₀.trans inf_le_left
  have hSubY₀ : IsSubnormal Y₀ CU := by
    have h := hL.2.1.inf CU
    rwa [inf_eq_right.2 hCUC] at h
  have hI₁CU : GLAPComponent p CU I₁ := glaPComponent_of_isSubnormal' hp hSubY₀ hI₁c
  have hO'CU : O' ≤ CU := Subgroup.map_subtype_le _
  have hO'CUn : (O'.subgroupOf CU).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hO'CU).2 hCUN
  have hO'N : O' ≤ Subgroup.normalizer (I₁ : Set G) := by
    have hPN : preimBarX p CU I₁ ≤ Subgroup.normalizer (I₁ : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (le_preimBarX p hI₁CU.1)).1
        (glaPComponent_normal_preimBarX hI₁CU)
    intro o ho
    apply hPN
    obtain ⟨q, hq, hqo⟩ := Subgroup.mem_map.1 ho
    refine Subgroup.mem_map.2 ⟨q, Subgroup.mem_comap.2 ?_, hqo⟩
    have h1 : (QuotientGroup.mk' (GLAPPrimeCore p ↥CU)) q = 1 := by
      rw [QuotientGroup.mk'_apply]
      exact (QuotientGroup.eq_one_iff q).2 hq
    rw [h1]
    exact Subgroup.one_mem _
  set H := I₁ ⊔ O' with hHdef
  have hHCU : H ≤ CU := sup_le hI₁CU.1 hO'CU
  have hHN : H ≤ Subgroup.normalizer (O' : Set G) := fun h hh => hCUN (hHCU hh)
  have hO'H : O' ≤ GLAPPrimeCoreOf p H :=
    l93c_le_glaPPrimeCoreOf le_sup_right
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).2 hHN) hcopO'
  have hHcov : I₁ ⊔ GLAPPrimeCoreOf p H = H :=
    le_antisymm (sup_le le_sup_left (Subgroup.map_subtype_le _))
      (sup_le le_sup_left (hO'H.trans le_sup_right))
  obtain ⟨hO_I₁H, ⟨eIH⟩⟩ := cover_facts hp (le_sup_left : I₁ ≤ H) hHcov
  have hHq : CFSG.Open.IsQuasisimple (PQuot p H) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv eIH
      (isQuasisimple_pQuot_of_glaPComponent hp hI₁c)
  set D := N ⊓ CU with hDdef
  have hY₃cov : (D ⊓ H) ⊔ GLAPPrimeCoreOf p H = H := by
    have hDN : D ≤ Subgroup.normalizer (O' : Set G) := fun d hd => hCUN (Subgroup.mem_inf.1 hd).2
    apply le_antisymm (sup_le inf_le_right (Subgroup.map_subtype_le _))
    intro h hh
    have hh' : h ∈ D ⊔ O' := by
      rw [hDcov]
      exact hHCU hh
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right D O' hDN] at hh'
    obtain ⟨d, hd, o, ho, hdo⟩ := Set.mem_mul.mp hh'
    have hdH : d ∈ H := by
      have : d = h * o⁻¹ := by rw [← hdo]; group
      rw [this]
      exact H.mul_mem hh (H.inv_mem (Subgroup.mem_sup_right ho))
    have hdY : d ∈ D ⊓ H := Subgroup.mem_inf.2 ⟨hd, hdH⟩
    rw [← hdo]
    exact Subgroup.mul_mem_sup hdY (hO'H ho)
  obtain ⟨hO₃, ⟨e₃⟩⟩ := cover_facts hp (inf_le_right : D ⊓ H ≤ H) hY₃cov
  have hY₃q : CFSG.Open.IsQuasisimple (PQuot p (D ⊓ H)) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e₃.symm hHq
  obtain ⟨K, hK, hKbar⟩ := exists_glaPComponent_of_isQuasisimple hY₃q
  set Y₃ := D ⊓ H with hY₃def
  have hKY₃ : K ≤ Y₃ := hK.1
  have hKcov : K ⊔ GLAPPrimeCoreOf p Y₃ = Y₃ :=
    sup_glaPPrimeCoreOf_eq_of_barX_eq_top hKY₃ hKbar
  obtain ⟨-, hK_uniq, -⟩ := glaPLayer_of_isQuasisimple hY₃q
  have hKlayer : GLAPLayer p Y₃ = K := (hK_uniq K hK).symm
  have hO₃le : GLAPPrimeCoreOf p Y₃ ≤ GLAPPrimeCoreOf p H := (le_of_eq hO₃).trans inf_le_right
  have hKH : K ⊔ GLAPPrimeCoreOf p H = H := by
    apply le_antisymm (sup_le (hKY₃.trans inf_le_right) (Subgroup.map_subtype_le _))
    calc H = Y₃ ⊔ GLAPPrimeCoreOf p H := hY₃cov.symm
      _ ≤ K ⊔ GLAPPrimeCoreOf p H := sup_le (calc Y₃ = K ⊔ GLAPPrimeCoreOf p Y₃ := hKcov.symm
          _ ≤ K ⊔ GLAPPrimeCoreOf p H := sup_le_sup_left hO₃le _) le_sup_right
  have hHsub : IsSubnormal H CU :=
    l93c_isSubnormal_sup hI₁CU.2.1 O' hO'CU hO'CUn
  have hsub3 : IsSubnormal (D ⊓ H) D := by
    have h := hHsub.inf D
    rw [inf_eq_right.2 (inf_le_right : D ≤ CU), inf_comm] at h
    exact h
  have hKD : GLAPComponent p D K := glaPComponent_of_isSubnormal' hp hsub3 hK
  have hHN₁ : H ≤ Subgroup.normalizer (I₁ : Set G) := sup_le Subgroup.le_normalizer hO'N
  have hKH' : K ≤ H := hKY₃.trans inf_le_right
  have hIH : Nat.Coprime p ((I₁.subgroupOf H).index) := by
    have h1 := card_sup_mul_card_inf_of_le_normalizer (A := I₁) (B := O') hO'N
    rw [← hHdef] at h1
    have h2 := Subgroup.index_mul_card (H := I₁.subgroupOf H)
    have h3 : Nat.card ↥(I₁.subgroupOf H) = Nat.card ↥I₁ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv
    rw [h3] at h2
    have hpos : 0 < Nat.card ↥I₁ := Nat.card_pos
    have h4 : (I₁.subgroupOf H).index * Nat.card ↥(I₁ ⊓ O') = Nat.card ↥O' := by
      apply Nat.eq_of_mul_eq_mul_left hpos
      calc Nat.card ↥I₁ * ((I₁.subgroupOf H).index * Nat.card ↥(I₁ ⊓ O'))
          = ((I₁.subgroupOf H).index * Nat.card ↥I₁) * Nat.card ↥(I₁ ⊓ O') := by ring
        _ = Nat.card ↥H * Nat.card ↥(I₁ ⊓ O') := by rw [h2]
        _ = Nat.card ↥I₁ * Nat.card ↥O' := h1
    have hdvd : (I₁.subgroupOf H).index ∣ Nat.card ↥O' :=
      ⟨Nat.card ↥(I₁ ⊓ O'), h4.symm⟩
    exact Nat.Coprime.coprime_dvd_right hdvd hcopO'
  have hI₁Hn : (I₁.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (le_sup_left : I₁ ≤ H)).2 hHN₁
  let f : ↥K →* (↥H ⧸ I₁.subgroupOf H) :=
    (QuotientGroup.mk' (I₁.subgroupOf H)).comp (Subgroup.inclusion hKH')
  have hker : f.ker = (I₁ ⊓ K).subgroupOf K := by
    ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    change (QuotientGroup.mk' (I₁.subgroupOf H) (Subgroup.inclusion hKH' k) :
      ↥H ⧸ I₁.subgroupOf H) = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => ⟨h, k.2⟩, fun h => h.1⟩
  have hcopN : Nat.Coprime p ((I₁ ⊓ K).subgroupOf (GLAPLayer p Y₃)).index := by
    rw [hKlayer, ← hker, Subgroup.index_ker]
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_subgroup_dvd_card f.range) hIH
  have hN1 : I₁ ⊓ K ≤ GLAPLayer p Y₃ := by
    rw [hKlayer]
    exact inf_le_right
  have hN1n : ((I₁ ⊓ K).subgroupOf (GLAPLayer p Y₃)).Normal := by
    rw [hKlayer, Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right]
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hI := Subgroup.mem_normalizer_iff.1 (hHN₁ (hKH' hk)) y
    have hK' := Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer hk) y
    constructor
    · intro hy
      exact Subgroup.mem_inf.2 ⟨hI.1 (Subgroup.mem_inf.1 hy).1, hK'.1 (Subgroup.mem_inf.1 hy).2⟩
    · intro hy
      exact Subgroup.mem_inf.2 ⟨hI.2 (Subgroup.mem_inf.1 hy).1, hK'.2 (Subgroup.mem_inf.1 hy).2⟩
  have hKI₁ : K ≤ I₁ := by
    have hF := layer_isOPrimeResidual hp Y₃ (I₁ ⊓ K) hN1 hN1n hcopN
    rw [hKlayer] at hF
    calc K = I₁ ⊓ K := hF.symm
      _ ≤ I₁ := inf_le_left
  have hKL_le : K ≤ L := hKI₁.trans hI₁L_le
  obtain ⟨hO_I₁L, -⟩ := cover_facts hp hI₁L_le hI₁L
  have hKHN : K ≤ Subgroup.normalizer (GLAPPrimeCoreOf p H : Set G) :=
    hKH'.trans (le_normalizer_glaPPrimeCoreOf p H)
  have hKHcov : K ⊔ GLAPPrimeCoreOf p H = H := hKH
  have hI₁le : I₁ ≤ K ⊔ GLAPPrimeCoreOf p L := by
    intro i hi
    have hiH : i ∈ K ⊔ GLAPPrimeCoreOf p H := by
      rw [hKHcov]
      exact (le_sup_left : I₁ ≤ H) hi
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right K _ hKHN] at hiH
    obtain ⟨k, hk, q, hq, hkq⟩ := Set.mem_mul.mp hiH
    have hqI : q ∈ I₁ := by
      have e : q = k⁻¹ * i := by
        rw [← hkq]
        group
      rw [e]
      exact I₁.mul_mem (I₁.inv_mem (hKI₁ hk)) hi
    have hqO : q ∈ GLAPPrimeCoreOf p I₁ := by
      rw [hO_I₁H]
      exact Subgroup.mem_inf.2 ⟨hqI, hq⟩
    have hqL : q ∈ GLAPPrimeCoreOf p L := by
      have h := hqO
      rw [hO_I₁L] at h
      exact (Subgroup.mem_inf.1 h).2
    rw [← hkq]
    exact Subgroup.mul_mem_sup hk hqL
  have hKO : K ⊔ GLAPPrimeCoreOf p L = L := by
    apply le_antisymm (sup_le hKL_le (Subgroup.map_subtype_le _))
    calc L = I₁ ⊔ GLAPPrimeCoreOf p L := hI₁L.symm
      _ ≤ K ⊔ GLAPPrimeCoreOf p L := sup_le hI₁le le_sup_right
  have hBsK : Bs ≤ Subgroup.normalizer (K : Set G) := by
    intro b hb
    have hbN : b ∈ Subgroup.normalizer (N : Set G) := Subgroup.le_normalizer (hBsN hb)
    have hbC : b ∈ Subgroup.normalizer (CU : Set G) := l93c_mem_normalizer_centralizer (hBsU hb)
    have hbD : b ∈ Subgroup.normalizer (D : Set G) := l93c_mem_normalizer_inf hbN hbC
    have hbY₀ : b ∈ Subgroup.normalizer (Y₀ : Set G) := l93c_mem_normalizer_inf (hBsL hb) hbC
    have hbI₁ : b ∈ Subgroup.normalizer (I₁ : Set G) := by
      have h1 := glaPComponent_gLBConj hI₁c b
      rw [mem_normalizer_iff_gLBConj_eq.1 hbY₀] at h1
      exact mem_normalizer_iff_gLBConj_eq.2 (hI₁uniq _ h1)
    have hbO' : b ∈ Subgroup.normalizer (O' : Set G) := hCUN (hBsU hb)
    have hbH : b ∈ Subgroup.normalizer (H : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_sup I₁ O' ⟨hbI₁, hbO'⟩
    have hbY₃ : b ∈ Subgroup.normalizer (Y₃ : Set G) := l93c_mem_normalizer_inf hbD hbH
    have h1 : GLAPComponent p Y₃ (GLBConj b K) := by
      have h2 := glaPComponent_gLBConj hK b
      rwa [mem_normalizer_iff_gLBConj_eq.1 hbY₃] at h2
    exact mem_normalizer_iff_gLBConj_eq.2 (glaPComponent_eq_of_isQuasisimple hY₃q h1 hK)
  exact ⟨K, hKD, hKL_le, hKO, hBsK⟩

private theorem lemma93_normalizes_commutator {H K : Subgroup G} {h : G}
    (hH : h ∈ Subgroup.normalizer (H : Set G)) (hK : h ∈ Subgroup.normalizer (K : Set G))
    {g : G} (hg : g ∈ (⁅H, K⁆ : Subgroup G)) : h * g * h⁻¹ ∈ (⁅H, K⁆ : Subgroup G) := by
  have hle : (⁅H, K⁆ : Subgroup G) ≤ (⁅H, K⁆ : Subgroup G).comap (MulAut.conj h).toMonoidHom := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_comap]
    show h * ⁅a, b⁆ * h⁻¹ ∈ _
    have e : h * ⁅a, b⁆ * h⁻¹ = ⁅h * a * h⁻¹, h * b * h⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.commutator_mem_commutator ((Subgroup.mem_normalizer_iff.1 hH a).1 ha)
      ((Subgroup.mem_normalizer_iff.1 hK b).1 hb)
  have h' := hle hg
  rw [Subgroup.mem_comap] at h'
  exact h'

private theorem lemma93_mem_normalizer_commutator {H K : Subgroup G} {h : G}
    (hH : h ∈ Subgroup.normalizer (H : Set G)) (hK : h ∈ Subgroup.normalizer (K : Set G)) :
    h ∈ Subgroup.normalizer ((⁅H, K⁆ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    exact lemma93_normalizes_commutator hH hK hg
  · intro hg
    have h' := lemma93_normalizes_commutator ((Subgroup.normalizer (H : Set G)).inv_mem hH)
      ((Subgroup.normalizer (K : Set G)).inv_mem hK) hg
    have e : h⁻¹ * (h * g * h⁻¹) * h⁻¹⁻¹ = g := by group
    rwa [e] at h'

theorem exists_S_data {p : ℕ} (hc : S9Ctx G p) {x : G} {U N I Bs : Subgroup G}
    (hN : IsTwoLocal N) (hUel : IsElemAbelian p U) (hUc : Nat.card U = p ^ 2) (hUN : U ≤ N)
    (hxU : x ∈ U) (hI : GLAPComponent p (N ⊓ Subgroup.centralizer (U : Set G)) I)
    (hBsU : Bs ≤ Subgroup.centralizer (U : Set G)) (hBsN : Bs ≤ N)
    (hBsI : Bs ≤ Subgroup.normalizer (I : Set G)) (hUBs : U ≤ Bs) :
    ∃ u ∈ U, u ≠ 1 ∧ ∃ S : Subgroup G, S ≠ ⊥ ∧ IsPGroup 2 S ∧ S ≤ Subgroup.centralizer ({u} : Set G) ∧
      I ≤ Subgroup.normalizer (S : Set G) ∧ Bs ≤ Subgroup.normalizer (S : Set G) ∧
      (⁅S, I⁆ : Subgroup G) = S := by
  have hp := hc.ctx.prime
  have hp2 := hc.ctx.odd
  have hIC : I ≤ Subgroup.centralizer (U : Set G) := hI.1.trans inf_le_right
  have hIN : I ≤ N := hI.1.trans inf_le_left
  have hI2 : ¬ IsPGroup 2 I := by
    intro h2
    have hd := dvd_card_pQuot_of_component hp hI
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hq : IsPGroup 2 (PQuot p I) :=
      h2.of_surjective (QuotientGroup.mk' (GLAPPrimeCore p ↥I)) (QuotientGroup.mk'_surjective _)
    obtain ⟨k, hk⟩ := hq.exists_card_eq
    rw [hk] at hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))
  have hUne : U ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hUc
    have := hp.two_le
    nlinarith
  obtain ⟨A, hAU, hAidx, hA⟩ :=
    GL83.I_33_3_proved G hc.ctx.charTwo p hp hp2 N U I hN hUne hUel hUN hI.1 hI2
  have hAne : A ≠ ⊥ := by
    intro h
    rw [h, Subgroup.bot_subgroupOf, Subgroup.index_bot] at hAidx
    rw [hUc] at hAidx
    have := hp.two_le
    nlinarith
  obtain ⟨u, huA, hu1⟩ : ∃ u ∈ A, u ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hAne ((Subgroup.eq_bot_iff_forall A).2 hcon)
  have huU : u ∈ U := hAU huA
  set K : Subgroup G := pCoreOf 2 N ⊓ Subgroup.centralizer ({u} : Set G) with hKdef
  have hCu : Subgroup.centralizer (U : Set G) ≤ Subgroup.centralizer ({u} : Set G) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff] at hg
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.1 hh]
    exact hg u huU
  have hfwd : ∀ n ∈ N, n ∈ Subgroup.centralizer (U : Set G) → ∀ g ∈ K,
      n * g * n⁻¹ ∈ K := by
    intro n hnN hnC g hg
    have hnC' : n ∈ Subgroup.centralizer ({u} : Set G) := hCu hnC
    exact ⟨(Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 N hnN) g).1 hg.1,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hnC' hg.2) (Subgroup.inv_mem _ hnC')⟩
  have hNK : ∀ n ∈ N, n ∈ Subgroup.centralizer (U : Set G) →
      n ∈ Subgroup.normalizer (K : Set G) := by
    intro n hnN hnC
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · exact hfwd n hnN hnC g
    · intro hg
      have h1 := hfwd n⁻¹ (N.inv_mem hnN) ((Subgroup.centralizer (U : Set G)).inv_mem hnC) _ hg
      have e : n⁻¹ * (n * g * n⁻¹) * n⁻¹⁻¹ = g := by group
      rwa [e] at h1
  have hIC : I ≤ Subgroup.centralizer (U : Set G) := hI.1.trans inf_le_right
  have hIN : I ≤ N := hI.1.trans inf_le_left
  have hIK : I ≤ Subgroup.normalizer (K : Set G) := fun i hi => hNK i (hIN hi) (hIC hi)
  have hBsK : Bs ≤ Subgroup.normalizer (K : Set G) := fun b hb => hNK b (hBsN hb) (hBsU hb)
  have hS_le : (⁅I, K⁆ : Subgroup G) ≤ pCoreOf 2 N := by
    rw [Subgroup.commutator_le]
    intro i hi k hk
    rw [commutatorElement_def]
    have h1 : i * k * i⁻¹ ∈ pCoreOf 2 N :=
      (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 N (hIN hi)) k).1 hk.1
    exact (pCoreOf 2 N).mul_mem h1 ((pCoreOf 2 N).inv_mem hk.1)
  have hS2 : IsPGroup 2 (⁅I, K⁆ : Subgroup G) := (isPGroup_pCoreOf 2 N).to_le hS_le
  have hSC : (⁅I, K⁆ : Subgroup G) ≤ Subgroup.centralizer ({u} : Set G) := by
    rw [Subgroup.commutator_le]
    intro i hi k hk
    have hi' : i ∈ Subgroup.centralizer ({u} : Set G) := hCu (hIC hi)
    have hk' : k ∈ Subgroup.centralizer ({u} : Set G) := hk.2
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hi' hk')
      (Subgroup.inv_mem _ hi')) (Subgroup.inv_mem _ hk')
  have hIS : I ≤ Subgroup.normalizer ((⁅I, K⁆ : Subgroup G) : Set G) := fun i hi =>
    lemma93_mem_normalizer_commutator (Subgroup.le_normalizer hi) (hIK hi)
  have hBsS : Bs ≤ Subgroup.normalizer ((⁅I, K⁆ : Subgroup G) : Set G) := fun b hb =>
    lemma93_mem_normalizer_commutator (hBsI hb) (hBsK hb)
  have hCA : Subgroup.centralizer (A : Set G) ≤ Subgroup.centralizer ({u} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.2 huA)
  have hSne : (⁅I, K⁆ : Subgroup G) ≠ ⊥ := by
    intro h
    apply hA
    apply le_bot_iff.1
    rw [← h]
    exact Subgroup.commutator_mono_right (inf_le_inf_left _ hCA)
  have hcop : Nat.Coprime p (Nat.card K) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨j, hj⟩ := ((isPGroup_pCoreOf 2 N).to_le inf_le_left : IsPGroup 2 K).exists_card_eq
    rw [hj]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have hOp : ∀ M : Subgroup G, M ≤ I → (M.subgroupOf I).Normal →
      Nat.Coprime p (M.subgroupOf I).index → M = I := by
    intro M hM hMn hMi
    haveI := hMn
    exact le_antisymm hM (CFSG.HardMathSupport.Solomon.Coordinator.i183_le_of_coprime_index hp hI
      le_rfl hMi)
  have key := i321UsedAt_holds p hp K I hcop hIK hOp
  refine ⟨u, huU, hu1, ⁅I, K⁆, hSne, hS2, hSC, hIS, hBsS, ?_⟩
  rw [Subgroup.commutator_comm I K]
  exact key

private theorem lemma93_normalizes_of_comm_eq {S I : Subgroup G} (hSI : (⁅S, I⁆ : Subgroup G) = S) :
    I ≤ Subgroup.normalizer (S : Set G) := by
  have key : ∀ i ∈ I, ∀ s ∈ S, i * s * i⁻¹ ∈ S := by
    intro i hi s hs
    have h1 : ⁅s⁻¹, i⁆ ∈ S := hSI ▸ Subgroup.commutator_mem_commutator (S.inv_mem hs) hi
    have e : i * s * i⁻¹ = s * ⁅s⁻¹, i⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact S.mul_mem hs h1
  intro i hi
  rw [Subgroup.mem_normalizer_iff]
  intro s
  constructor
  · exact key i hi s
  · intro hs
    have h1 := key i⁻¹ (I.inv_mem hi) _ hs
    have e : i⁻¹ * (i * s * i⁻¹) * i⁻¹⁻¹ = s := by group
    rwa [e] at h1

private theorem lemma93_mem_core_iff {p : ℕ} {I : Subgroup G} {y : G} (hy : y ∈ I) :
    (⟨y, hy⟩ : ↥I) ∈ GLAPPrimeCore p ↥I ↔ y ∈ GLAPPrimeCoreOf p I := by
  constructor
  · intro h
    exact ⟨⟨y, hy⟩, h, rfl⟩
  · rintro ⟨z, hz, hzy⟩
    have : z = ⟨y, hy⟩ := Subtype.ext hzy
    rw [← this]
    exact hz

private theorem lemma93_central_of_comm {p : ℕ} {I : Subgroup G} {x : G} (hx : x ∈ I)
    (hcomm : ∀ g ∈ I, ⁅x, g⁆ ∈ GLAPPrimeCoreOf p I) :
    (QuotientGroup.mk' (GLAPPrimeCore p ↥I) (⟨x, hx⟩ : ↥I) : PQuot p I) ∈
      Subgroup.center (PQuot p I) := by
  rw [Subgroup.mem_center_iff]
  intro z
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore p ↥I) z
  have hcommu : ⁅x, (g : G)⁆ ∈ I := by
    rw [commutatorElement_def]
    exact I.mul_mem (I.mul_mem (I.mul_mem hx g.2) (I.inv_mem hx)) (I.inv_mem g.2)
  have h1 : ⁅(QuotientGroup.mk' (GLAPPrimeCore p ↥I) (⟨x, hx⟩ : ↥I) : PQuot p I),
      (QuotientGroup.mk' (GLAPPrimeCore p ↥I) g : PQuot p I)⁆ = 1 := by
    rw [← map_commutatorElement]
    have hmem : (⟨⁅x, (g : G)⁆, hcommu⟩ : ↥I) ∈ GLAPPrimeCore p ↥I :=
      (lemma93_mem_core_iff hcommu).2 (hcomm g g.2)
    have e : ⁅(⟨x, hx⟩ : ↥I), g⁆ = ⟨⁅x, (g : G)⁆, hcommu⟩ :=
      Subtype.ext (by simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv])
    rw [e]
    exact (QuotientGroup.eq_one_iff _).2 hmem
  exact (commutatorElement_eq_one_iff_mul_comm.1 h1).symm

private theorem lemma93_comm_of_central {p : ℕ} {I : Subgroup G} {x g : G} (hx : x ∈ I) (hg : g ∈ I)
    (hz : (QuotientGroup.mk' (GLAPPrimeCore p ↥I) (⟨x, hx⟩ : ↥I) : PQuot p I) ∈
      Subgroup.center (PQuot p I)) :
    ⁅x, g⁆ ∈ GLAPPrimeCoreOf p I := by
  have hcommu : ⁅x, g⁆ ∈ I := by
    rw [commutatorElement_def]
    exact I.mul_mem (I.mul_mem (I.mul_mem hx hg) (I.inv_mem hx)) (I.inv_mem hg)
  have hcomm : (QuotientGroup.mk' (GLAPPrimeCore p ↥I) (⟨x, hx⟩ : ↥I) : PQuot p I) *
      QuotientGroup.mk' (GLAPPrimeCore p ↥I) (⟨g, hg⟩ : ↥I) =
      QuotientGroup.mk' (GLAPPrimeCore p ↥I) (⟨g, hg⟩ : ↥I) *
      QuotientGroup.mk' (GLAPPrimeCore p ↥I) (⟨x, hx⟩ : ↥I) :=
    (Subgroup.mem_center_iff.1 hz _).symm
  have hkey : (QuotientGroup.mk' (GLAPPrimeCore p ↥I) ⁅(⟨x, hx⟩ : ↥I), (⟨g, hg⟩ : ↥I)⁆ :
      PQuot p I) = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm
  rw [← lemma93_mem_core_iff hcommu]
  have e : (⟨⁅x, g⁆, hcommu⟩ : ↥I) = ⁅(⟨x, hx⟩ : ↥I), (⟨g, hg⟩ : ↥I)⁆ :=
    Subtype.ext (by simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv])
  rw [e]
  exact (QuotientGroup.eq_one_iff _).1 hkey

private theorem lemma93_comm_core {p : ℕ} (hp : p.Prime) {Y I : Subgroup G}
    (hI : GLAPComponent p Y I) {b : G} (hbI : b ∈ Subgroup.normalizer (I : Set G))
    (hcen : ∀ j ∈ I, ∀ g ∈ I, ⁅⁅b, j⁆, g⁆ ∈ GLAPPrimeCoreOf p I) :
    ∀ j ∈ I, ⁅b, j⁆ ∈ GLAPPrimeCoreOf p I := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hcomm_mem : ∀ j ∈ I, ⁅b, j⁆ ∈ I := by
    intro j hj
    rw [commutatorElement_def]
    exact I.mul_mem ((Subgroup.mem_normalizer_iff.1 hbI j).1 hj) (I.inv_mem hj)
  let π : ↥I →* PQuot p I := QuotientGroup.mk' (GLAPPrimeCore p ↥I)
  let F : ↥I → PQuot p I := fun j => π ⟨⁅b, (j : G)⁆, hcomm_mem j j.2⟩
  have hFcen : ∀ j : ↥I, F j ∈ Subgroup.center (PQuot p I) := fun j =>
    lemma93_central_of_comm (hcomm_mem j j.2) (fun g hg => hcen j j.2 g hg)
  have hFmul : ∀ j k : ↥I, F (j * k) = F j * F k := by
    intro j k
    have e : (⟨⁅b, ((j * k : ↥I) : G)⁆, hcomm_mem _ (I.mul_mem j.2 k.2)⟩ : ↥I) =
        ⟨⁅b, (j : G)⁆, hcomm_mem j j.2⟩ * (j * ⟨⁅b, (k : G)⁆, hcomm_mem k k.2⟩ * j⁻¹) :=
      Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]; group)
    have hc : π j * π ⟨⁅b, (k : G)⁆, hcomm_mem k k.2⟩ =
        π ⟨⁅b, (k : G)⁆, hcomm_mem k k.2⟩ * π j :=
      Subgroup.mem_center_iff.1 (hFcen k) (π j)
    show π ⟨⁅b, ((j * k : ↥I) : G)⁆, _⟩ =
      π ⟨⁅b, (j : G)⁆, _⟩ * π ⟨⁅b, (k : G)⁆, _⟩
    have key2 : π j * π ⟨⁅b, (k : G)⁆, hcomm_mem k k.2⟩ * (π j)⁻¹ =
        π ⟨⁅b, (k : G)⁆, hcomm_mem k k.2⟩ := by
      rw [hc, mul_inv_cancel_right]
    rw [e, map_mul, map_mul, map_mul, map_inv, key2]
  let f : ↥I →* PQuot p I := MonoidHom.mk' F hFmul
  have hfcomm : ∀ x y : ↥I, f ⁅x, y⁆ = 1 := by
    intro x y
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.1 (hFcen x) (f y)).symm
  have hperf : (⁅(⊤ : Subgroup ↥I), (⊤ : Subgroup ↥I)⁆ : Subgroup ↥I) = ⊤ := by
    have hG : (⁅I, I⁆ : Subgroup G) = I := glaPComponent_perfect hI
    have hmt : Subgroup.map I.subtype (⊤ : Subgroup ↥I) = I := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    apply Subgroup.map_injective (f := I.subtype) (fun a b h => Subtype.ext h)
    rw [Subgroup.map_commutator, hmt]
    exact hG
  have hle : (⁅(⊤ : Subgroup ↥I), (⊤ : Subgroup ↥I)⁆ : Subgroup ↥I) ≤ f.ker :=
    Subgroup.commutator_le.2 (fun x _ y _ => MonoidHom.mem_ker.2 (hfcomm x y))
  have hker : (⊤ : Subgroup ↥I) ≤ f.ker := hperf ▸ hle
  intro j hj
  have hfj : f ⟨j, hj⟩ = 1 := MonoidHom.mem_ker.1 (hker (Subgroup.mem_top _))
  have h1 : π ⟨⁅b, j⁆, hcomm_mem j hj⟩ = 1 := hfj
  exact (lemma93_mem_core_iff (hcomm_mem j hj)).1 ((QuotientGroup.eq_one_iff _).1 h1)

private theorem lemma93_le_of_cover {p : ℕ} (hp : p.Prime) {Y I Q : Subgroup G}
    (hI : GLAPComponent p Y I) (hQI : Q ≤ I) (hQn : (Q.subgroupOf I).Normal)
    (hcov : ∀ i ∈ I, ∃ q ∈ Q, q⁻¹ * i ∈ GLAPPrimeCoreOf p I) : I ≤ Q := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := hQn
  let φ : GLAPPrimeCore p ↥I →* (↥I ⧸ Q.subgroupOf I) :=
    (QuotientGroup.mk' (Q.subgroupOf I)).comp (GLAPPrimeCore p ↥I).subtype
  have hφ : Function.Surjective φ := by
    intro z
    obtain ⟨i, rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf I) z
    obtain ⟨q, hq, hqi⟩ := hcov i.1 i.2
    have hqI : q ∈ I := hQI hq
    have hq' : (⟨q, hqI⟩ : ↥I) ∈ Q.subgroupOf I := Subgroup.mem_subgroupOf.2 hq
    have hyI : q⁻¹ * i.1 ∈ I := I.mul_mem (I.inv_mem hqI) i.2
    have hy : (⟨q⁻¹ * i.1, hyI⟩ : ↥I) ∈ GLAPPrimeCore p ↥I := (lemma93_mem_core_iff hyI).2 hqi
    refine ⟨⟨⟨q⁻¹ * i.1, hyI⟩, hy⟩, ?_⟩
    show QuotientGroup.mk' (Q.subgroupOf I) (⟨q⁻¹ * i.1, hyI⟩ : ↥I) =
      QuotientGroup.mk' (Q.subgroupOf I) i
    have hq1 : QuotientGroup.mk' (Q.subgroupOf I) (⟨q, hqI⟩ : ↥I) = 1 :=
      (QuotientGroup.eq_one_iff _).2 hq'
    have e : (⟨q⁻¹ * i.1, hyI⟩ : ↥I) = (⟨q, hqI⟩ : ↥I)⁻¹ * i := Subtype.ext (by simp)
    rw [e, map_mul, map_inv, hq1, inv_one, one_mul]
  have hdvd : Nat.card (↥I ⧸ Q.subgroupOf I) ∣ Nat.card (GLAPPrimeCore p ↥I) :=
    Subgroup.card_dvd_of_surjective hφ
  have hO : Nat.card (GLAPPrimeCore p ↥I) = Nat.card (GLAPPrimeCoreOf p I) := by
    rw [GLAPPrimeCoreOf, Subgroup.card_map_of_injective (f := I.subtype) (fun a b h => Subtype.ext h)]
  have hcop : p.Coprime (Q.subgroupOf I).index := by
    have h1 : p.Coprime (Nat.card (GLAPPrimeCore p ↥I)) := by
      rw [hO]
      exact CFSG.HardMathSupport.Solomon.Coordinator.i183_coprime_card_glaPPrimeCoreOf hp I
    rw [Subgroup.index]
    exact Nat.Coprime.coprime_dvd_right hdvd h1
  exact CFSG.HardMathSupport.Solomon.Coordinator.i183_le_of_coprime_index hp hI le_rfl hcop

private theorem lemma93_comm_L {p : ℕ} (hp : p.Prime) {L I : Subgroup G} {b : G}
    (hIL : I ≤ L) (hcov : I ⊔ GLAPPrimeCoreOf p L = L) (hbL : b ∈ Subgroup.normalizer (L : Set G))
    (hbI : ∀ j ∈ I, ⁅b, j⁆ ∈ GLAPPrimeCoreOf p I) : b ∈ centModSubgroup p L := by
  have hOI : GLAPPrimeCoreOf p I = I ⊓ GLAPPrimeCoreOf p L := (cover_facts hp hIL hcov).1
  have hbO : b ∈ Subgroup.normalizer (GLAPPrimeCoreOf p L : Set G) :=
    normalizer_le_normalizer_glaPPrimeCoreOf p L hbL
  refine ⟨hbL, fun l hl => ?_⟩
  have hlmem : l ∈ I ⊔ GLAPPrimeCoreOf p L := by
    rw [hcov]
    exact hl
  obtain ⟨i, hi, o, ho, rfl⟩ := lemma93_mem_sup_of_le_normalizer
    (hIL.trans (le_normalizer_glaPPrimeCoreOf p L)) hlmem
  have hio : i ∈ L := hIL hi
  have hobr : ⁅o, b⁆ ∈ GLAPPrimeCoreOf p L := by
    have e : ⁅o, b⁆ = o * (b * o⁻¹ * b⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (GLAPPrimeCoreOf p L).mul_mem ho
      ((Subgroup.mem_normalizer_iff.1 hbO o⁻¹).1 ((GLAPPrimeCoreOf p L).inv_mem ho))
  have hib : ⁅i, b⁆ ∈ GLAPPrimeCoreOf p L := by
    have h1 : ⁅b, i⁆ ∈ GLAPPrimeCoreOf p I := hbI i hi
    rw [hOI] at h1
    have h2 : ⁅b, i⁆ ∈ GLAPPrimeCoreOf p L := h1.2
    have e : ⁅i, b⁆ = ⁅b, i⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (GLAPPrimeCoreOf p L).inv_mem h2
  have e : ⁅i * o, b⁆ = i * ⁅o, b⁆ * i⁻¹ * ⁅i, b⁆ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact (GLAPPrimeCoreOf p L).mul_mem
    ((Subgroup.mem_normalizer_iff.1 (le_normalizer_glaPPrimeCoreOf p L hio) _).1 hobr) hib

theorem commutator_ne_bot_of_cover {p : ℕ} (hp : p.Prime) {X Y L I Bs S : Subgroup G}
    (hL : GLAPComponent p X L) (hI : GLAPComponent p Y I) (hIL : I ≤ L)
    (hcov : I ⊔ GLAPPrimeCoreOf p L = L) (hBsL : Bs ≤ Subgroup.normalizer (L : Set G))
    (hBsI : Bs ≤ Subgroup.normalizer (I : Set G)) (hnot : ¬ Bs ≤ centModSubgroup p L) (hS : S ≠ ⊥)
    (hSI : (⁅S, I⁆ : Subgroup G) = S) (hBsS : Bs ≤ Subgroup.normalizer (S : Set G)) :
    (⁅S, Bs⁆ : Subgroup G) ≠ ⊥ := by
  intro h0
  classical
  have hIN : I ≤ Subgroup.normalizer (S : Set G) := lemma93_normalizes_of_comm_eq hSI
  have hSC : S ≤ Subgroup.centralizer (Bs : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 h0
  have hIS_le : (⁅I, S⁆ : Subgroup G) ≤ S := by
    rw [Subgroup.commutator_le]
    intro i hi s hs
    rw [commutatorElement_def]
    have h1 : i * s * i⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.1 (hIN hi) s).1 hs
    exact S.mul_mem h1 (S.inv_mem hs)
  have h1 : (⁅⁅I, S⁆, Bs⁆ : Subgroup G) = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.2 (hIS_le.trans hSC)
  have h2 : (⁅⁅S, Bs⁆, I⁆ : Subgroup G) = ⊥ := by
    rw [h0]
    exact Subgroup.commutator_bot_left I
  have hrot := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  have hWC : (⁅Bs, I⁆ : Subgroup G) ≤ Subgroup.centralizer (S : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 hrot
  have hWI : (⁅Bs, I⁆ : Subgroup G) ≤ I := by
    rw [Subgroup.commutator_le]
    intro b hb i hi
    rw [commutatorElement_def]
    have h1' : b * i * b⁻¹ ∈ I := (Subgroup.mem_normalizer_iff.1 (hBsI hb) i).1 hi
    exact I.mul_mem h1' (I.inv_mem hi)
  set Q : Subgroup G := I ⊓ Subgroup.centralizer (S : Set G) with hQdef
  have hQI : Q ≤ I := inf_le_left
  have hWQ : (⁅Bs, I⁆ : Subgroup G) ≤ Q := le_inf hWI hWC
  have hQn : (Q.subgroupOf I).Normal := by
    constructor
    intro q hq i
    rw [Subgroup.mem_subgroupOf] at hq ⊢
    obtain ⟨hqI, hqC⟩ := Subgroup.mem_inf.1 hq
    refine Subgroup.mem_inf.2 ⟨I.mul_mem (I.mul_mem i.2 hqI) (I.inv_mem i.2), ?_⟩
    rw [Subgroup.mem_centralizer_iff] at hqC ⊢
    intro s hs
    have hs' : (i : G)⁻¹ * s * (i : G) ∈ S := by
      have := (Subgroup.mem_normalizer_iff.1 (hIN (I.inv_mem i.2)) s).1 hs
      simpa only [inv_inv] using this
    have hc := hqC _ hs'
    calc s * ((i : G) * q * (i : G)⁻¹) = (i : G) * (((i : G)⁻¹ * s * (i : G)) * q) * (i : G)⁻¹ := by
          group
      _ = (i : G) * (q * ((i : G)⁻¹ * s * (i : G))) * (i : G)⁻¹ := by rw [hc]
      _ = ((i : G) * q * (i : G)⁻¹) * s := by group
  by_cases hQtop : (Q.subgroupOf I).map (QuotientGroup.mk' (GLAPPrimeCore p ↥I)) = ⊤
  ·
    have hcov' : ∀ i ∈ I, ∃ q ∈ Q, q⁻¹ * i ∈ GLAPPrimeCoreOf p I := by
      intro i hi
      have hmem : (QuotientGroup.mk' (GLAPPrimeCore p ↥I) (⟨i, hi⟩ : ↥I) : PQuot p I) ∈
          (Q.subgroupOf I).map (QuotientGroup.mk' (GLAPPrimeCore p ↥I)) := by
        rw [hQtop]
        exact Subgroup.mem_top _
      obtain ⟨q', hq', hqe⟩ := Subgroup.mem_map.1 hmem
      have hc : q'⁻¹ * (⟨i, hi⟩ : ↥I) ∈ GLAPPrimeCore p ↥I := QuotientGroup.eq.1 hqe
      have hyI : (q' : G)⁻¹ * i ∈ I := I.mul_mem (I.inv_mem q'.2) hi
      have e : (⟨(q' : G)⁻¹ * i, hyI⟩ : ↥I) = q'⁻¹ * ⟨i, hi⟩ := Subtype.ext (by simp)
      refine ⟨(q' : G), Subgroup.mem_subgroupOf.1 hq', ?_⟩
      rw [← lemma93_mem_core_iff hyI, e]
      exact hc
    have hIQ : I ≤ Q := lemma93_le_of_cover hp hI hQI hQn hcov'
    have hSC' : S ≤ Subgroup.centralizer (I : Set G) := by
      intro s hs
      rw [Subgroup.mem_centralizer_iff]
      intro i hi
      exact ((Subgroup.mem_centralizer_iff.1 (hIQ hi).2) s hs).symm
    have hSI0 : (⁅S, I⁆ : Subgroup G) = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 hSC'
    exact hS (hSI.symm.trans hSI0)
  ·
    have hQbn : ((Q.subgroupOf I).map (QuotientGroup.mk' (GLAPPrimeCore p ↥I))).Normal :=
      Subgroup.Normal.map hQn _ (QuotientGroup.mk'_surjective _)
    have hQbc : (Q.subgroupOf I).map (QuotientGroup.mk' (GLAPPrimeCore p ↥I)) ≤
        Subgroup.center (PQuot p I) :=
      le_center_of_normal_of_isQuasisimple (isQuasisimple_pQuot_of_glaPComponent hp hI) hQbn hQtop
    have hbI : ∀ b ∈ Bs, ∀ j ∈ I, ⁅b, j⁆ ∈ GLAPPrimeCoreOf p I := by
      intro b hb
      refine lemma93_comm_core hp hI (hBsI hb) ?_
      intro j hj g hg
      have hbjI : ⁅b, j⁆ ∈ I := hWI (Subgroup.commutator_mem_commutator hb hj)
      have hbjQ : ⁅b, j⁆ ∈ Q := hWQ (Subgroup.commutator_mem_commutator hb hj)
      have hmem : (QuotientGroup.mk' (GLAPPrimeCore p ↥I) (⟨⁅b, j⁆, hbjI⟩ : ↥I) : PQuot p I) ∈
          (Q.subgroupOf I).map (QuotientGroup.mk' (GLAPPrimeCore p ↥I)) :=
        Subgroup.mem_map.2 ⟨⟨⁅b, j⁆, hbjI⟩, Subgroup.mem_subgroupOf.2 hbjQ, rfl⟩
      exact lemma93_comm_of_central hbjI hg (hQbc hmem)
    exact hnot (fun b hb => lemma93_comm_L hp hIL hcov (hBsL hb) (hbI b hb))

private def lemma93Cls (x : QuaternionGroup 2) : Fin 3 :=
  if x = QuaternionGroup.a 1 ∨ x = QuaternionGroup.a 3 then 0
  else if x = QuaternionGroup.xa 0 ∨ x = QuaternionGroup.xa 2 then 1 else 2

private theorem lemma93_cls_inv : ∀ x : QuaternionGroup 2, lemma93Cls x⁻¹ = lemma93Cls x := by
  decide

private theorem lemma93_cls_eq : ∀ x y : QuaternionGroup 2, x * x ≠ 1 → y * y ≠ 1 →
    lemma93Cls x = lemma93Cls y → y = x ∨ y = x⁻¹ := by
  decide

private theorem lemma93_sq_ne : ∀ x : QuaternionGroup 2, x * x ≠ 1 → x * x = QuaternionGroup.a 2 := by
  decide

private theorem lemma93_sq_eq_one : ∀ x : QuaternionGroup 2,
    x * x = 1 ↔ x = 1 ∨ x = QuaternionGroup.a 2 := by
  decide

private def lemma93Rep : Fin 3 → QuaternionGroup 2 :=
  ![QuaternionGroup.a 1, QuaternionGroup.xa 0, QuaternionGroup.xa 1]

private theorem lemma93_rep_cls : ∀ k : Fin 3, lemma93Cls (lemma93Rep k) = k := by
  decide

private theorem lemma93_rep_nc : ∀ k : Fin 3, lemma93Rep k * lemma93Rep k ≠ 1 := by
  decide

private theorem lemma93_sign_comm : ∀ x y : Equiv.Perm (Fin 3),
    Equiv.Perm.sign x = 1 → Equiv.Perm.sign y = 1 → x * y = y * x := by
  decide

private theorem lemma93_perm_perfect (H : Subgroup (Equiv.Perm (Fin 3)))
    (hH : (⁅H, H⁆ : Subgroup (Equiv.Perm (Fin 3))) = H) : H = ⊥ := by
  have hsign : ∀ h ∈ H, Equiv.Perm.sign h = 1 := by
    intro h hh
    have h1 : Subgroup.map (Equiv.Perm.sign : Equiv.Perm (Fin 3) →* ℤˣ) H = ⊥ := by
      have hc : (⁅Subgroup.map (Equiv.Perm.sign : Equiv.Perm (Fin 3) →* ℤˣ) H,
          Subgroup.map (Equiv.Perm.sign : Equiv.Perm (Fin 3) →* ℤˣ) H⁆ : Subgroup ℤˣ) = ⊥ :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.2 (fun a _ =>
          Subgroup.mem_centralizer_iff.2 (fun b _ => mul_comm b a))
      calc Subgroup.map (Equiv.Perm.sign : Equiv.Perm (Fin 3) →* ℤˣ) H
          = Subgroup.map (Equiv.Perm.sign : Equiv.Perm (Fin 3) →* ℤˣ) ⁅H, H⁆ := by rw [hH]
        _ = ⁅Subgroup.map (Equiv.Perm.sign : Equiv.Perm (Fin 3) →* ℤˣ) H,
            Subgroup.map (Equiv.Perm.sign : Equiv.Perm (Fin 3) →* ℤˣ) H⁆ := by
          rw [Subgroup.map_commutator]
        _ = ⊥ := hc
    have h2 : Equiv.Perm.sign h ∈ Subgroup.map (Equiv.Perm.sign : Equiv.Perm (Fin 3) →* ℤˣ) H :=
      Subgroup.mem_map_of_mem _ hh
    rw [h1, Subgroup.mem_bot] at h2
    exact h2
  have hbot : (⁅H, H⁆ : Subgroup (Equiv.Perm (Fin 3))) = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.2 (fun x hx => Subgroup.mem_centralizer_iff.2
      (fun y hy => (lemma93_sign_comm y x (hsign y hy) (hsign x hx))))
  rw [hbot] at hH
  exact hH.symm

private theorem lemma93_top_perfect {p : ℕ} {Y I : Subgroup G} (hI : GLAPComponent p Y I) :
    (⁅(⊤ : Subgroup ↥I), (⊤ : Subgroup ↥I)⁆ : Subgroup ↥I) = ⊤ := by
  have hG : (⁅I, I⁆ : Subgroup G) = I := glaPComponent_perfect hI
  have hmt : Subgroup.map I.subtype (⊤ : Subgroup ↥I) = I := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  apply Subgroup.map_injective (f := I.subtype) (fun a b h => Subtype.ext h)
  rw [Subgroup.map_commutator, hmt]
  exact hG

private def lemma93Conj {S : Subgroup G} (i : ↥(Subgroup.normalizer (S : Set G))) : S →* S where
  toFun s := ⟨(i : G) * s * (i : G)⁻¹, (Subgroup.mem_normalizer_iff.1 i.2 s).1 s.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' s t := Subtype.ext (by
    show (i : G) * ((s : G) * (t : G)) * (i : G)⁻¹ =
      ((i : G) * (s : G) * (i : G)⁻¹) * ((i : G) * (t : G) * (i : G)⁻¹)
    group)

private theorem lemma93Conj_val {S : Subgroup G} (i : ↥(Subgroup.normalizer (S : Set G))) (s : S) :
    ((lemma93Conj i s : S) : G) = (i : G) * (s : G) * (i : G)⁻¹ := rfl

private theorem lemma93Conj_mul {S : Subgroup G} (i j : ↥(Subgroup.normalizer (S : Set G))) (s : S) :
    lemma93Conj (i * j) s = lemma93Conj i (lemma93Conj j s) :=
  Subtype.ext (by
    rw [lemma93Conj_val, lemma93Conj_val, lemma93Conj_val, Subgroup.coe_mul]
    group)

private theorem lemma93Conj_one {S : Subgroup G} (s : S) :
    lemma93Conj (1 : ↥(Subgroup.normalizer (S : Set G))) s = s :=
  Subtype.ext (by rw [lemma93Conj_val]; simp)

private theorem lemma93Conj_eq_one {S : Subgroup G} (i : ↥(Subgroup.normalizer (S : Set G))) {s : S}
    (h : lemma93Conj i s = 1) : s = 1 := by
  have h' : (i : G) * (s : G) * (i : G)⁻¹ = 1 := by
    have := congrArg Subtype.val h
    rwa [lemma93Conj_val] at this
  have : (s : G) = 1 := by
    have h2 : (s : G) = (i : G)⁻¹ * ((i : G) * (s : G) * (i : G)⁻¹) * (i : G) := by group
    rw [h', mul_one] at h2
    rw [h2]
    group
  exact Subtype.ext this

private theorem lemma93_quaternion_absurd {p : ℕ} {Y I S : Subgroup G} (hI : GLAPComponent p Y I)
    (hSI : (⁅S, I⁆ : Subgroup G) = S) (hIS : I ≤ Subgroup.normalizer (S : Set G))
    (e : ↥S ≃* QuaternionGroup 2) : False := by
  classical
  set z : S := e.symm (QuaternionGroup.a 2) with hzdef
  have hsq : ∀ x : S, x * x = 1 ↔ x = 1 ∨ x = z := by
    intro x
    rw [← e.injective.eq_iff, map_mul, map_one, lemma93_sq_eq_one]
    constructor
    · rintro (h | h)
      · exact Or.inl (e.injective (by rw [h, map_one]))
      · exact Or.inr (e.injective (by rw [h, hzdef, MulEquiv.apply_symm_apply]))
    · rintro (h | h)
      · left; rw [h, map_one]
      · right; rw [h, hzdef, MulEquiv.apply_symm_apply]
  have hz1 : z ≠ 1 := by
    intro h
    have : e z = 1 := by rw [h, map_one]
    rw [hzdef, MulEquiv.apply_symm_apply] at this
    exact absurd this (by decide)
  have hzz : z * z = 1 := (hsq z).2 (Or.inr rfl)
  set cl : S → Fin 3 := fun x => lemma93Cls (e x) with hcldef
  have hnc_iff : ∀ x : S, x * x ≠ 1 ↔ e x * e x ≠ 1 := fun x => by
    rw [← map_mul]
    exact e.injective.ne_iff.symm.trans ⟨fun h => by simpa using h, fun h => by simpa using h⟩
  have hcl_inv : ∀ x : S, cl x⁻¹ = cl x := fun x => by
    simp only [hcldef, map_inv]
    exact lemma93_cls_inv _
  have hcl_eq : ∀ x y : S, x * x ≠ 1 → y * y ≠ 1 → cl x = cl y → y = x ∨ y = x⁻¹ := by
    intro x y hx hy hxy
    rcases lemma93_cls_eq (e x) (e y) ((hnc_iff x).1 hx) ((hnc_iff y).1 hy) hxy with h | h
    · exact Or.inl (e.injective h)
    · exact Or.inr (e.injective (by rw [h, map_inv]))
  set r : Fin 3 → S := fun k => e.symm (lemma93Rep k) with hrdef
  have hr_cl : ∀ k, cl (r k) = k := fun k => by
    simp only [hcldef, hrdef, MulEquiv.apply_symm_apply]
    exact lemma93_rep_cls k
  have hr_nc : ∀ k, r k * r k ≠ 1 := fun k => by
    rw [hnc_iff]
    simp only [hrdef, MulEquiv.apply_symm_apply]
    exact lemma93_rep_nc k
  set N : Subgroup G := Subgroup.normalizer (S : Set G) with hNdef
  set sig : ↥N → Fin 3 → Fin 3 := fun i k => cl (lemma93Conj i (r k)) with hsigdef
  have hcj_nc : ∀ (i : ↥N) (s : S), s * s ≠ 1 → lemma93Conj i s * lemma93Conj i s ≠ 1 := by
    intro i s hs h
    have h2 : lemma93Conj i (s * s) = 1 := by
      rw [map_mul]
      exact h
    exact hs (lemma93Conj_eq_one i h2)
  have hinv : ∀ (i : ↥N) (s : S), s * s ≠ 1 → cl (lemma93Conj i s) = sig i (cl s) := by
    intro i s hs
    have hcs : cl (r (cl s)) = cl s := hr_cl _
    rcases hcl_eq (r (cl s)) s (hr_nc _) hs hcs with h | h
    · exact congrArg (fun t => cl (lemma93Conj i t)) h
    · have h2 := congrArg (fun t => cl (lemma93Conj i t)) h
      simp only [map_inv, hcl_inv] at h2
      exact h2
  have hsig_mul : ∀ (i j : ↥N) (k : Fin 3), sig (i * j) k = sig i (sig j k) := by
    intro i j k
    show cl (lemma93Conj (i * j) (r k)) = sig i (cl (lemma93Conj j (r k)))
    rw [lemma93Conj_mul]
    exact hinv i _ (hcj_nc j (r k) (hr_nc k))
  have hsig_one : ∀ k, sig 1 k = k := fun k => by
    show cl (lemma93Conj 1 (r k)) = k
    rw [lemma93Conj_one, hr_cl]
  let permOf : ↥N → Equiv.Perm (Fin 3) := fun i =>
    { toFun := sig i
      invFun := sig i⁻¹
      left_inv := fun k => by
        have := hsig_mul i⁻¹ i k
        rw [inv_mul_cancel, hsig_one] at this
        exact this.symm
      right_inv := fun k => by
        have := hsig_mul i i⁻¹ k
        rw [mul_inv_cancel, hsig_one] at this
        exact this.symm }
  let ψ0 : ↥N →* Equiv.Perm (Fin 3) :=
    MonoidHom.mk' permOf (fun i j => Equiv.ext fun k => hsig_mul i j k)
  let ψ : ↥I →* Equiv.Perm (Fin 3) := ψ0.comp (Subgroup.inclusion hIS)
  have hperf : ⁅ψ.range, ψ.range⁆ = ψ.range := by
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, lemma93_top_perfect hI]
  have hψ : ψ.range = ⊥ := lemma93_perm_perfect _ hperf
  have hfix : ∀ (i : ↥I) (k : Fin 3), sig ⟨(i : G), hIS i.2⟩ k = k := by
    intro i k
    have h1 : ψ i ∈ ψ.range := MonoidHom.mem_range.2 ⟨i, rfl⟩
    rw [hψ, Subgroup.mem_bot] at h1
    have h3 : ψ i = permOf ⟨(i : G), hIS i.2⟩ := rfl
    have h2 : permOf ⟨(i : G), hIS i.2⟩ k = k := by
      rw [← h3, h1, Equiv.Perm.one_apply]
    exact h2
  have hcomm_key : ∀ (i : ↥I) (s : S), s * s ≠ 1 →
      lemma93Conj ⟨(i : G), hIS i.2⟩ s = s ∨ lemma93Conj ⟨(i : G), hIS i.2⟩ s = s⁻¹ := by
    intro i s hs
    have h1 : cl (lemma93Conj ⟨(i : G), hIS i.2⟩ s) = cl s := by
      rw [hinv _ s hs, hfix]
    exact hcl_eq s _ hs (hcj_nc _ s hs) h1.symm
  have hcomm_z : ∀ (i : ↥I) (s : S), lemma93Conj ⟨(i : G), hIS i.2⟩ s * s⁻¹ ∈ Subgroup.zpowers z := by
    intro i s
    by_cases hs : s * s = 1
    · rcases (hsq s).1 hs with h | h
      · rw [h, map_one, one_mul, inv_one]
        exact Subgroup.one_mem _
      · have hcz : lemma93Conj ⟨(i : G), hIS i.2⟩ s = s := by
          rw [h]
          have h2 : lemma93Conj ⟨(i : G), hIS i.2⟩ z * lemma93Conj ⟨(i : G), hIS i.2⟩ z = 1 := by
            rw [← map_mul, hzz, map_one]
          rcases (hsq _).1 h2 with h3 | h3
          · exact absurd (lemma93Conj_eq_one _ h3) hz1
          · exact h3
        rw [hcz, mul_inv_cancel]
        exact Subgroup.one_mem _
    · rcases hcomm_key i s hs with h | h
      · rw [h, mul_inv_cancel]
        exact Subgroup.one_mem _
      · rw [h]
        have hsz : s * s = z := by
          rw [← e.injective.eq_iff, map_mul, hzdef, MulEquiv.apply_symm_apply]
          exact (lemma93_sq_ne _ ((hnc_iff s).1 hs))
        have hinvsq : s⁻¹ * s⁻¹ = z := by
          calc s⁻¹ * s⁻¹ = (s * s)⁻¹ := by group
            _ = z := by rw [hsz, inv_eq_of_mul_eq_one_right hzz]
        rw [hinvsq]
        exact Subgroup.mem_zpowers z
  have hmemG : ∀ x ∈ Subgroup.zpowers z, (x : G) ∈ Subgroup.zpowers (z : G) := by
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    exact Subgroup.mem_zpowers_iff.2 ⟨k, by rw [Subgroup.coe_zpow]⟩
  have hle : (⁅S, I⁆ : Subgroup G) ≤ Subgroup.zpowers (z : G) := by
    rw [Subgroup.commutator_le]
    intro s hs i hi
    have hx := hmemG _ (hcomm_z ⟨i, hi⟩ ⟨s, hs⟩)
    have e1 : ((lemma93Conj ⟨i, hIS hi⟩ ⟨s, hs⟩ * ⟨s, hs⟩⁻¹ : S) : G) = ⁅i, s⁆ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, lemma93Conj_val, commutatorElement_def]
    rw [e1] at hx
    have e2 : ⁅s, i⁆ = (⁅i, s⁆)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e2]
    exact (Subgroup.zpowers (z : G)).inv_mem hx
  have hS_le : S ≤ Subgroup.zpowers (z : G) := by
    calc S = (⁅S, I⁆ : Subgroup G) := hSI.symm
      _ ≤ Subgroup.zpowers (z : G) := hle
  have hcardS : Nat.card S = 8 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hz2 : (z : G) ^ 2 = 1 := by
    rw [pow_two]
    exact congrArg Subtype.val hzz
  have hcardZ : Nat.card (Subgroup.zpowers (z : G)) ≤ 2 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hz2)
  have hle8 := Subgroup.card_le_of_le hS_le
  omega


theorem isEmpty_quaternion {p : ℕ} {Y I S : Subgroup G} (hI : GLAPComponent p Y I) (hS : S ≠ ⊥)
    (hSI : (⁅S, I⁆ : Subgroup G) = S) (hIS : I ≤ Subgroup.normalizer (S : Set G)) :
    IsEmpty (↥S ≃* QuaternionGroup 2) :=
  ⟨fun e => lemma93_quaternion_absurd hI hSI hIS e⟩

private theorem l93c_quot_eq_bot {p : ℕ} (hp : p.Prime) {X I : Subgroup G} (hI : GLAPComponent p X I)
    {K : Subgroup (PQuot p I)} (hKn : K.Normal) (hKc : Nat.Coprime p (Nat.card ↥K)) : K = ⊥ := by
  classical
  set π : ↥I →* PQuot p I := QuotientGroup.mk' (GLAPPrimeCore p ↥I) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  set K' : Subgroup ↥I := K.comap π with hK'
  haveI : K'.Normal := hKn.comap π
  have hKidx : K'.index = K.index := Subgroup.index_comap_of_surjective K hπs
  have hfin : K.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hcardK' : Nat.card ↥K' = Nat.card ↥K * Nat.card ↥(GLAPPrimeCore p ↥I) := by
    have h1 := Subgroup.card_mul_index K'
    have h2 := Subgroup.card_mul_index K
    have h3 := Subgroup.card_mul_index (GLAPPrimeCore p ↥I)
    have h4 : (GLAPPrimeCore p ↥I).index = Nat.card (PQuot p I) := rfl
    rw [h4] at h3
    apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hfin)
    calc Nat.card ↥K' * K.index = Nat.card ↥K' * K'.index := by rw [hKidx]
      _ = Nat.card ↥I := h1
      _ = Nat.card ↥(GLAPPrimeCore p ↥I) * Nat.card (PQuot p I) := h3.symm
      _ = Nat.card ↥(GLAPPrimeCore p ↥I) * (Nat.card ↥K * K.index) := by rw [← h2]
      _ = (Nat.card ↥K * Nat.card ↥(GLAPPrimeCore p ↥I)) * K.index := by ring
  have hcoreC : Nat.Coprime p (Nat.card ↥(GLAPPrimeCore p ↥I)) := by
    have h := CFSG.HardMathSupport.Solomon.Coordinator.i183_coprime_card_glaPPrimeCoreOf hp I
    rw [GLAPPrimeCoreOf, Subgroup.card_map_of_injective (f := I.subtype)
      (fun a b h => Subtype.ext h)] at h
    exact h
  have hK'c : Nat.Coprime p (Nat.card ↥K') := by
    rw [hcardK']
    exact Nat.Coprime.mul_right hKc hcoreC
  have hK'le : K' ≤ GLAPPrimeCore p ↥I := by
    unfold GLAPPrimeCore CFSG.pPrimeCore
    exact le_sSup ⟨inferInstance, hK'c⟩
  rw [eq_bot_iff]
  intro q hq
  obtain ⟨y, rfl⟩ := hπs q
  have hyc : y ∈ GLAPPrimeCore p ↥I := hK'le hq
  rw [Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply]
  exact (QuotientGroup.eq_one_iff y).2 hyc

private theorem l93c_residual {p : ℕ} (hp : p.Prime) {X I : Subgroup G} (hI : GLAPComponent p X I)
    {M : Subgroup G} (hMI : M ≤ I) (hMn : (M.subgroupOf I).Normal)
    (hcop : Nat.Coprime p (M.subgroupOf I).index) : M = I := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hq : CFSG.Open.IsQuasisimple (PQuot p I) := isQuasisimple_pQuot_of_glaPComponent hp hI
  haveI : Nontrivial (PQuot p I) := isQuasisimple_nontrivial hq
  set π : ↥I →* PQuot p I := QuotientGroup.mk' (GLAPPrimeCore p ↥I) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  haveI := hMn
  set Mbar : Subgroup (PQuot p I) := (M.subgroupOf I).map π with hMbar
  have hMbarn : Mbar.Normal := Subgroup.Normal.map hMn _ hπs
  have hidx : Nat.Coprime p Mbar.index :=
    Nat.Coprime.coprime_dvd_right (Subgroup.index_map_dvd (M.subgroupOf I) hπs) hcop
  by_cases htop : Mbar = ⊤
  ·
    by_contra hne
    have hlt : M < I := lt_of_le_of_ne hMI hne
    have hMX : IsSubnormal M X :=
      isSubnormal_trans' (IsSubnormal.step (H := M) (M := I) (K := I) hMI hMn (IsSubnormal.refl I)) hI.2.1
    have hOX : GLAPPrimeCoreOf p I ≤ GLAPPrimeCoreOf p X :=
      CFSG.LocalAnalysis.GLTheoremB.glaPPrimeCoreOf_le_of_isSubnormal hp hI.2.1
    have hIX : I ≤ X := hI.1
    apply hI.2.2.2 M hlt hMX
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨x, Subgroup.mem_subgroupOf.2 (hMI (Subgroup.mem_subgroupOf.1 hx)), rfl⟩
    · rintro _ ⟨x, hx, rfl⟩
      have hxI : (x : G) ∈ I := Subgroup.mem_subgroupOf.1 hx
      have hmem : (QuotientGroup.mk' (GLAPPrimeCore p ↥I) (⟨x, hxI⟩ : ↥I) : PQuot p I) ∈ Mbar := by
        rw [htop]
        exact Subgroup.mem_top _
      obtain ⟨m, hm, hmeq⟩ := Subgroup.mem_map.1 hmem
      have hmcore : (m : ↥I)⁻¹ * (⟨x, hxI⟩ : ↥I) ∈ GLAPPrimeCore p ↥I := QuotientGroup.eq.1 hmeq
      have hval : ((m : G))⁻¹ * (x : G) ∈ GLAPPrimeCoreOf p I := by
        have e : (m : ↥I)⁻¹ * (⟨x, hxI⟩ : ↥I) = ⟨(m : G)⁻¹ * x, I.mul_mem (I.inv_mem m.2) hxI⟩ :=
          Subtype.ext (by simp)
        rw [e] at hmcore
        exact (lemma93_mem_core_iff _).1 hmcore
      have hvalX : ((m : G))⁻¹ * (x : G) ∈ GLAPPrimeCoreOf p X := hOX hval
      refine Subgroup.mem_map.2 ⟨(⟨(m : G), hIX m.2⟩ : ↥X), Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.1 hm), ?_⟩
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply]
      apply QuotientGroup.eq.2
      have e : (⟨(m : G), hIX m.2⟩ : ↥X)⁻¹ * x = ⟨(m : G)⁻¹ * x, X.mul_mem (X.inv_mem (hIX m.2)) x.2⟩ :=
        Subtype.ext (by simp)
      rw [e]
      exact (lemma93_mem_core_iff _).2 hvalX
  · have hcen : Mbar ≤ Subgroup.center (PQuot p I) := le_center_of_normal_of_isQuasisimple hq hMbarn htop
    obtain ⟨P⟩ : Nonempty (Sylow p (PQuot p I)) := inferInstance
    have hP2 : IsPGroup p (P : Subgroup (PQuot p I)) := P.2
    have hPM : (P : Subgroup (PQuot p I)) ≤ Mbar := by
      intro y hy
      obtain ⟨k, hk⟩ := hP2 ⟨y, hy⟩
      have hyk : y ^ p ^ k = 1 := by
        have := congrArg Subtype.val hk
        simpa using this
      have hf : (QuotientGroup.mk' Mbar y : PQuot p I ⧸ Mbar) ^ p ^ k = 1 := by
        rw [← map_pow, hyk, map_one]
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one hf)
      have hdvd : orderOf (QuotientGroup.mk' Mbar y : PQuot p I ⧸ Mbar) ∣ Mbar.index :=
        orderOf_dvd_natCard _
      rw [hj] at hdvd
      have h1 : p ^ j = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_left j hidx) hdvd
      have h2 : orderOf (QuotientGroup.mk' Mbar y : PQuot p I ⧸ Mbar) = 1 := by
        rw [hj, h1]
      have h3 := orderOf_eq_one_iff.1 h2
      exact (QuotientGroup.eq_one_iff y).1 h3
    have hPc : (P : Subgroup (PQuot p I)) ≤ Subgroup.center (PQuot p I) := hPM.trans hcen
    haveI : (P : Subgroup (PQuot p I)).Normal := ⟨fun n hn g => by
      have hcg := Subgroup.mem_center_iff.1 (hPc hn) g
      have e : g * n * g⁻¹ = n := by rw [hcg, mul_inv_cancel_right]
      rw [e]
      exact hn⟩
    obtain ⟨K, hK⟩ := Subgroup.exists_right_complement'_of_coprime (N := (P : Subgroup (PQuot p I)))
      P.card_coprime_index
    haveI : K.Normal := ⟨fun k hk g => by
      obtain ⟨⟨⟨h, hh⟩, ⟨k₀, hk₀⟩⟩, rfl⟩ := hK.2 g
      have hz : h * (k₀ * k * k₀⁻¹) * h⁻¹ = k₀ * k * k₀⁻¹ := by
        rw [show h * (k₀ * k * k₀⁻¹) = (k₀ * k * k₀⁻¹) * h from
          (Subgroup.mem_center_iff.1 (hPc hh) _).symm, mul_inv_cancel_right]
      have e : h * k₀ * k * (h * k₀)⁻¹ = h * (k₀ * k * k₀⁻¹) * h⁻¹ := by group
      rw [e, hz]
      exact K.mul_mem (K.mul_mem hk₀ hk) (K.inv_mem hk₀)⟩
    have hcardK : Nat.card ↥K = (P : Subgroup (PQuot p I)).index := by
      have h1 := hK.card_mul_card
      have h2 := Subgroup.card_mul_index (P : Subgroup (PQuot p I))
      have hpos : 0 < Nat.card ↥(P : Subgroup (PQuot p I)) := Nat.card_pos
      exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans h2.symm)
    have hKcop : Nat.Coprime p (Nat.card ↥K) := by
      rw [hcardK]
      exact (Nat.Prime.coprime_iff_not_dvd hp).2 P.not_dvd_index
    have hKbot : K = ⊥ := l93c_quot_eq_bot hp hI inferInstance hKcop
    have hindex1 : (P : Subgroup (PQuot p I)).index = 1 := by
      rw [← hcardK, hKbot, Subgroup.card_bot]
    have hPtop : (P : Subgroup (PQuot p I)) = ⊤ := Subgroup.index_eq_one.1 hindex1
    have hpgrp : IsPGroup p (PQuot p I) := by
      intro g
      have hg : g ∈ (P : Subgroup (PQuot p I)) := by
        rw [hPtop]
        exact Subgroup.mem_top _
      obtain ⟨k, hk⟩ := hP2 ⟨g, hg⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    haveI : Group.IsNilpotent (PQuot p I) := hpgrp.isNilpotent
    exact ((Group.IsSolvable.commutator_lt_top_of_nontrivial (PQuot p I)).ne hq.1).elim

private theorem l93c_exists_J_core {p : ℕ} (hc : S9Ctx G p) (h183 : Input18_3_4) {x u : G}
    {L U N I Bs : Subgroup G}
    (hL : GLAPComponent p (Subgroup.centralizer ({x} : Set G)) L) (hxU : x ∈ U) (huU : u ∈ U)
    (hU : U ≤ Subgroup.centralizer ({x} : Set G) ⊓ centModSubgroup p L) (hUel : IsElemAbelian p U)
    (hI : GLAPComponent p (N ⊓ Subgroup.centralizer (U : Set G)) I) (hIL : I ≤ L)
    (hIcov : I ⊔ GLAPPrimeCoreOf p L = L) (hd4 : dLevel G p ≤ 4)
    (hBs : GLAIsBmax p Bs) (hUBs : U ≤ Bs) (hu1 : u ≠ 1) (hess : IsEssential p Bs u)
    (hBsL : Bs ≤ Subgroup.normalizer (L : Set G)) :
    ∃ J : Subgroup G, IsSTriple p Bs u J ∧ Bs ≤ Subgroup.normalizer (J : Set G) ∧ I ≤ J ∧
      GLAPLayer p (L ⊓ Subgroup.centralizer ({u} : Set G)) ≤ J ∧
      GLAPComponent p (J ⊓ Subgroup.centralizer ({x} : Set G))
        (GLAPLayer p (L ⊓ Subgroup.centralizer ({u} : Set G))) ∧
      I ≤ GLAPLayer p (L ⊓ Subgroup.centralizer ({u} : Set G)) := by
  classical
  have hp := hc.ctx.prime
  haveI : Fact p.Prime := ⟨hp⟩
  set Cx := Subgroup.centralizer ({x} : Set G) with hCxdef
  set Cu := Subgroup.centralizer ({u} : Set G) with hCudef
  set CU := Subgroup.centralizer (U : Set G) with hCUdef
  have hxu : x * u = u * x := isElemAbelian_commute hUel hxU huU
  have hxCu : x ∈ Cu := by
    rw [hCudef, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.1 hh]
    exact hxu.symm
  have hCUCu : CU ≤ Cu := by
    intro g hg
    rw [hCudef, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.1 hh]
    exact (Subgroup.mem_centralizer_iff.1 hg) u huU
  have hCM : CentMod p L u := centMod_iff.2 (hU huU).2
  have hpu : IsPGroup p (Subgroup.zpowers u) := isPGroup_zpowers_of_mem hUel huU
  have hY₀cov : (L ⊓ Cu) ⊔ GLAPPrimeCoreOf p L = L := inf_centralizer_sup_eq_of_centMod hp hpu hCM
  obtain ⟨hO₀, ⟨e₀⟩⟩ := cover_facts hp (inf_le_left : L ⊓ Cu ≤ L) hY₀cov
  have hY₀q : CFSG.Open.IsQuasisimple (PQuot p (L ⊓ Cu)) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e₀.symm
      (isQuasisimple_pQuot_of_glaPComponent hp hL)
  obtain ⟨hIuc, hIuuniq, hIubar⟩ := glaPLayer_of_isQuasisimple hY₀q
  set Y₀ := L ⊓ Cu with hY₀def
  set Iu := GLAPLayer p Y₀ with hIudef
  have hIuY₀ : Iu ≤ Y₀ := hIuc.1
  have hIucov : Iu ⊔ GLAPPrimeCoreOf p Y₀ = Y₀ := sup_glaPPrimeCoreOf_eq_of_barX_eq_top hIuY₀ hIubar
  have hIuN : Y₀ ≤ Subgroup.normalizer (Iu : Set G) := le_normalizer_of_unique_glaPComponent hIuc hIuuniq
  have hIuL : Iu ≤ L := hIuY₀.trans inf_le_left
  have hIuCx : Iu ≤ Cx := hIuL.trans hL.1
  have hIY₀ : I ≤ Y₀ := le_inf hIL (hI.1.trans (inf_le_right.trans hCUCu))
  have hIcovY₀ : I ⊔ GLAPPrimeCoreOf p Y₀ = Y₀ := by
    apply le_antisymm (sup_le hIY₀ (Subgroup.map_subtype_le _))
    intro y hy
    have hy' : y ∈ I ⊔ GLAPPrimeCoreOf p L := by
      rw [hIcov]
      exact (Subgroup.mem_inf.1 hy).1
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right I _
      (fun g hg => le_normalizer_glaPPrimeCoreOf p L (hIL hg))] at hy'
    obtain ⟨i, hi, o, ho, hio⟩ := Set.mem_mul.mp hy'
    have hoY : o ∈ GLAPPrimeCoreOf p Y₀ := by
      rw [hO₀]
      refine Subgroup.mem_inf.2 ⟨?_, ho⟩
      have e : o = i⁻¹ * y := by rw [← hio]; group
      rw [e]
      exact Y₀.mul_mem (Y₀.inv_mem (hIY₀ hi)) hy
    rw [← hio]
    exact Subgroup.mul_mem_sup hi hoY
  have hIIu : I ≤ Iu := by
    have hn : ((Iu ⊓ I).subgroupOf I).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer (inf_le_right : Iu ⊓ I ≤ I)]
      intro i hi
      exact l93c_mem_normalizer_inf (hIuN (hIY₀ hi)) (Subgroup.le_normalizer hi)
    have hO₀N : GLAPPrimeCoreOf p Y₀ ≤ Subgroup.normalizer (Iu : Set G) :=
      (Subgroup.map_subtype_le _).trans hIuN
    have hcopO : Nat.Coprime p (Nat.card ↥(GLAPPrimeCoreOf p Y₀)) :=
      CFSG.HardMathSupport.Solomon.Coordinator.i183_coprime_card_glaPPrimeCoreOf hp Y₀
    have hidx : Nat.Coprime p ((Iu ⊓ I).subgroupOf I).index := by
      have h1 := card_sup_mul_card_inf_of_le_normalizer (A := Iu) (B := I) (hIY₀.trans hIuN)
      have h2 : Nat.card ↥Y₀ * Nat.card ↥(Iu ⊓ GLAPPrimeCoreOf p Y₀) =
          Nat.card ↥Iu * Nat.card ↥(GLAPPrimeCoreOf p Y₀) := by
        have h := card_sup_mul_card_inf_of_le_normalizer (A := Iu) (B := GLAPPrimeCoreOf p Y₀) hO₀N
        rwa [hIucov] at h
      have hsub : Iu ⊔ I ≤ Y₀ := sup_le hIuY₀ hIY₀
      have h3 : ((Iu ⊓ I).subgroupOf I).index * Nat.card ↥(Iu ⊓ I) = Nat.card ↥I := by
        have h := Subgroup.index_mul_card (H := (Iu ⊓ I).subgroupOf I)
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : Iu ⊓ I ≤ I)).toEquiv] at h
        exact h
      have hcI : 0 < Nat.card ↥(Iu ⊓ I) := Nat.card_pos
      have haI : 0 < Nat.card ↥Iu := Nat.card_pos
      have hs : Nat.card ↥(Iu ⊔ I) = Nat.card ↥Iu * ((Iu ⊓ I).subgroupOf I).index := by
        apply Nat.eq_of_mul_eq_mul_right hcI
        rw [h1, ← h3]
        ring
      obtain ⟨t, ht⟩ := Subgroup.card_dvd_of_le hsub
      have hdvd : ((Iu ⊓ I).subgroupOf I).index ∣ Nat.card ↥(GLAPPrimeCoreOf p Y₀) := by
        refine ⟨t * Nat.card ↥(Iu ⊓ GLAPPrimeCoreOf p Y₀), ?_⟩
        apply Nat.eq_of_mul_eq_mul_left haI
        calc Nat.card ↥Iu * Nat.card ↥(GLAPPrimeCoreOf p Y₀)
            = Nat.card ↥Y₀ * Nat.card ↥(Iu ⊓ GLAPPrimeCoreOf p Y₀) := h2.symm
          _ = Nat.card ↥(Iu ⊔ I) * t * Nat.card ↥(Iu ⊓ GLAPPrimeCoreOf p Y₀) := by rw [ht]
          _ = Nat.card ↥Iu * ((Iu ⊓ I).subgroupOf I).index * t *
              Nat.card ↥(Iu ⊓ GLAPPrimeCoreOf p Y₀) := by rw [hs]
          _ = Nat.card ↥Iu * (((Iu ⊓ I).subgroupOf I).index *
              (t * Nat.card ↥(Iu ⊓ GLAPPrimeCoreOf p Y₀))) := by ring
      exact Nat.Coprime.coprime_dvd_right hdvd hcopO
    have hres := l93c_residual hp hI (M := Iu ⊓ I) inf_le_right hn hidx
    calc I = Iu ⊓ I := hres.symm
      _ ≤ Iu := inf_le_left
  have hSub : IsSubnormal Y₀ (Cu ⊓ Cx) := by
    have h := hL.2.1.inf Cu
    rw [inf_comm Cx Cu] at h
    exact h
  have hIuX : GLAPComponent p (Cu ⊓ Cx) Iu := glaPComponent_of_isSubnormal' hp hSub hIuc
  have hEu : IsElemAbelian p (Subgroup.zpowers x) := isElemAbelian_zpowers_of_mem hUel hxU
  have hEC : Subgroup.zpowers x ≤ Cu := Subgroup.zpowers_le.2 hxCu
  have hCE : Subgroup.centralizer (Subgroup.zpowers x : Set G) = Cx := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hIuE : GLAPComponent p (Cu ⊓ Subgroup.centralizer (Subgroup.zpowers x : Set G)) Iu := by
    rw [hCE]
    exact hIuX
  have hKu : CFSG.Open.IsKGroup ↥Cu := isKGroup_cx hc hu1
  obtain ⟨𝒞, h𝒞c, h𝒞sup, -, h𝒞tr⟩ :=
    h183 G Cu hKu p hp (Subgroup.zpowers x) hEC hEu Iu hIuE
  have hEBs : Subgroup.zpowers x ≤ Bs := Subgroup.zpowers_le.2 (hUBs hxU)
  have hBsnorm : ∀ L' ∈ 𝒞, Bs ≤ Subgroup.normalizer (L' : Set G) := fun L' hL' =>
    hc.stage4o.2.2.2.2.2.2.2 hd4 Bs u L' ⟨hBs, hess, h𝒞c L' hL'⟩
  have hsub1 : ∀ L' ∈ 𝒞, ∀ L'' ∈ 𝒞, L' = L'' := by
    intro L' hL' L'' hL''
    obtain ⟨e, he, hee⟩ := h𝒞tr L' hL' L'' hL''
    have hfix : GLBConj e L' = L' := mem_normalizer_iff_gLBConj_eq.1 (hBsnorm L' hL' (hEBs he))
    rw [← hee, hfix]
  have hIu_sup : Iu ≤ ⨆ L' ∈ 𝒞, L' := by
    rw [h𝒞sup]
    exact le_iSup₂_of_le (1 : G) (GLAPLayer p Cu).one_mem (gLBConj_one Iu).symm.le
  have hne : 𝒞.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hempty
    rw [hempty] at hIu_sup
    simp at hIu_sup
    exact glaPComponent_ne_bot' hIuc hIu_sup
  obtain ⟨J, hJ𝒞⟩ := hne
  have hIuJ : Iu ≤ J := hIu_sup.trans (iSup₂_le fun L' hL' => le_of_eq (hsub1 L' hL' J hJ𝒞))
  refine ⟨J, ⟨hBs, hess, h𝒞c J hJ𝒞⟩, hBsnorm J hJ𝒞, hIIu.trans hIuJ, hIuJ, ?_, hIIu⟩
  exact glaPComponent_of_le hp hIuX (le_inf hIuJ hIuCx) (inf_le_inf_right Cx (h𝒞c J hJ𝒞).1)

theorem exists_J {p : ℕ} (hc : S9Ctx G p) (h183 : Input18_3_4) {x u : G} {L U N I Bs : Subgroup G}
    (hL : GLAPComponent p (Subgroup.centralizer ({x} : Set G)) L) (hxU : x ∈ U) (huU : u ∈ U)
    (hU : U ≤ Subgroup.centralizer ({x} : Set G) ⊓ centModSubgroup p L) (hUel : IsElemAbelian p U)
    (hI : GLAPComponent p (N ⊓ Subgroup.centralizer (U : Set G)) I) (hIL : I ≤ L)
    (hIcov : I ⊔ GLAPPrimeCoreOf p L = L) (hd4 : dLevel G p ≤ 4)
    (hBs : GLAIsBmax p Bs) (hUBs : U ≤ Bs) (hu1 : u ≠ 1) (hess : IsEssential p Bs u)
    (hBsL : Bs ≤ Subgroup.normalizer (L : Set G)) :
    ∃ J : Subgroup G, IsSTriple p Bs u J ∧ Bs ≤ Subgroup.normalizer (J : Set G) ∧ I ≤ J ∧
      GLAPLayer p (L ⊓ Subgroup.centralizer ({u} : Set G)) ≤ J ∧
      GLAPComponent p (J ⊓ Subgroup.centralizer ({x} : Set G))
        (GLAPLayer p (L ⊓ Subgroup.centralizer ({u} : Set G))) ∧
      I ≤ GLAPLayer p (L ⊓ Subgroup.centralizer ({u} : Set G)) := by
  exact l93c_exists_J_core hc h183 hL hxU huU hU hUel hI hIL hIcov hd4 hBs hUBs hu1 hess hBsL

private theorem l93c_not_two_covers {p : ℕ} (hp : p.Prime) {X J S : Subgroup G}
    (hJ : GLAPComponent p X J) (hSJ : S ≤ J) (hS2 : IsPGroup 2 S)
    (hcov : S ⊔ GLAPPrimeCoreOf p J = J) : False := by
  classical
  have hq : CFSG.Open.IsQuasisimple (PQuot p J) := isQuasisimple_pQuot_of_glaPComponent hp hJ
  haveI : Nontrivial (PQuot p J) := isQuasisimple_nontrivial hq
  have hSN : S ≤ Subgroup.normalizer (GLAPPrimeCoreOf p J : Set G) :=
    hSJ.trans (le_normalizer_glaPPrimeCoreOf p J)
  have hP : IsPGroup 2 (PQuot p J) := by
    intro q
    obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore p ↥J) q
    have hj : (j : G) ∈ S ⊔ GLAPPrimeCoreOf p J := by
      rw [hcov]
      exact j.2
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right S _ hSN] at hj
    obtain ⟨s, hs, o, ho, hso⟩ := Set.mem_mul.mp hj
    have hsJ : s ∈ J := hSJ hs
    have hy : s⁻¹ * (j : G) ∈ GLAPPrimeCoreOf p J := by
      rw [← hso, inv_mul_cancel_left]
      exact ho
    have hkey : (⟨s, hsJ⟩ : ↥J)⁻¹ * j ∈ GLAPPrimeCore p ↥J := by
      have e : (⟨s, hsJ⟩ : ↥J)⁻¹ * j = ⟨s⁻¹ * (j : G), J.mul_mem (J.inv_mem hsJ) j.2⟩ :=
        Subtype.ext (by simp)
      rw [e]
      exact (lemma93_mem_core_iff _).2 hy
    obtain ⟨k, hk⟩ := hS2 ⟨s, hs⟩
    refine ⟨k, ?_⟩
    have hk' : (⟨s, hsJ⟩ : ↥J) ^ 2 ^ k = 1 := Subtype.ext (by
      have := congrArg Subtype.val hk
      simpa using this)
    have hq' : (QuotientGroup.mk' (GLAPPrimeCore p ↥J) ⟨s, hsJ⟩ : PQuot p J) =
        QuotientGroup.mk' (GLAPPrimeCore p ↥J) j := QuotientGroup.eq.2 hkey
    rw [← hq', ← map_pow, hk', map_one]
  haveI : Group.IsNilpotent (PQuot p J) := hP.isNilpotent
  exact (Group.IsSolvable.commutator_lt_top_of_nontrivial (PQuot p J)).ne hq.1

theorem S_data_J {p : ℕ} (hc : S9Ctx G p) (hd : dLevel G p ≤ 2) {x u : G} {L I Bs S J : Subgroup G}
    (hL : GLAPComponent p (Subgroup.centralizer ({x} : Set G)) L) (hIL : I ≤ L)
    (hBs : GLAIsBmax p Bs) (hu : u ∈ Bs) (hu1 : u ≠ 1) (hx : x ∈ Bs)
    (hS : S ≠ ⊥) (hS2 : IsPGroup 2 S) (hSu : S ≤ Subgroup.centralizer ({u} : Set G))
    (hBsS : Bs ≤ Subgroup.normalizer (S : Set G)) (hSBs : (⁅S, Bs⁆ : Subgroup G) ≠ ⊥)
    (hSI : (⁅S, I⁆ : Subgroup G) = S) (hIS : I ≤ Subgroup.normalizer (S : Set G))
    (hJ : IsSTriple p Bs u J) (hIu : GLAPLayer p (L ⊓ Subgroup.centralizer ({u} : Set G)) ≤ J)
    (hIuc : GLAPComponent p (J ⊓ Subgroup.centralizer ({x} : Set G))
      (GLAPLayer p (L ⊓ Subgroup.centralizer ({u} : Set G))))
    (hIuI : GLAPLayer p (L ⊓ Subgroup.centralizer ({u} : Set G)) ≤ I ⊔ GLAPPrimeCoreOf p J)
    (hIJ : I ≤ J) :
    S ≤ J ∧ ¬ S ≤ GLAPPrimeCoreOf p J ∧ ¬ CentMod p J x := by
  have hp := hc.ctx.prime
  have hJc : GLAPComponent p (Subgroup.centralizer ({u} : Set G)) J := hJ.2.2
  have hSJ : S ≤ J := le_of_isSubnormal_commutator_eq hJc.2.1 hIJ hSu hSI
  have hnotO : ¬ S ≤ GLAPPrimeCoreOf p J := by
    intro hSO
    have hOC : GLAPPrimeCoreOf p J ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ({u} : Set G)) :=
      glaPPrimeCoreOf_le_of_isSubnormal hp hJc.2.1
    exact hSBs (hc.stage4.2.2 hd Bs u S hBs hu hu1 (hSO.trans hOC) hS2 hBsS)
  refine ⟨hSJ, hnotO, fun hCM => ?_⟩
  have hxp : IsPGroup p (Subgroup.zpowers x) := isPGroup_zpowers_of_mem hBs.1 hx
  obtain ⟨-, hall, -, -, hcovJ, -⟩ := glaPLayer_inf_centralizer hp hJc hxp hCM
  rw [← hall _ hIuc] at hcovJ
  have hIcov : I ⊔ GLAPPrimeCoreOf p J = J := by
    apply le_antisymm (sup_le hIJ (Subgroup.map_subtype_le _))
    calc J = GLAPLayer p (L ⊓ Subgroup.centralizer ({u} : Set G)) ⊔ GLAPPrimeCoreOf p J := hcovJ.symm
      _ ≤ I ⊔ GLAPPrimeCoreOf p J := sup_le hIuI le_sup_right
  have hON : J ≤ Subgroup.normalizer ((S ⊔ GLAPPrimeCoreOf p J : Subgroup G) : Set G) := by
    have hIN : I ≤ Subgroup.normalizer ((S ⊔ GLAPPrimeCoreOf p J : Subgroup G) : Set G) := fun g hg =>
      Subgroup.inf_normalizer_le_normalizer_sup S (GLAPPrimeCoreOf p J)
        ⟨hIS hg, le_normalizer_glaPPrimeCoreOf p J (hIJ hg)⟩
    have hOJ : GLAPPrimeCoreOf p J ≤
        Subgroup.normalizer ((S ⊔ GLAPPrimeCoreOf p J : Subgroup G) : Set G) :=
      le_sup_right.trans Subgroup.le_normalizer
    calc J = I ⊔ GLAPPrimeCoreOf p J := hIcov.symm
      _ ≤ _ := sup_le hIN hOJ
  have hSOJ : (S ⊔ GLAPPrimeCoreOf p J : Subgroup G) ≤ J :=
    sup_le hSJ (Subgroup.map_subtype_le _)
  have hTn : ((S ⊔ GLAPPrimeCoreOf p J).subgroupOf J).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSOJ).2 hON
  set M : Subgroup (PQuot p J) :=
    ((S ⊔ GLAPPrimeCoreOf p J).subgroupOf J).map (QuotientGroup.mk' (GLAPPrimeCore p ↥J)) with hMdef
  have hMn : M.Normal := hTn.map _ (QuotientGroup.mk'_surjective _)
  have hMne : M ≠ ⊤ := by
    intro hM
    refine l93c_not_two_covers hp hJc hSJ hS2 (le_antisymm hSOJ fun j hj => ?_)
    have hmem : (QuotientGroup.mk' (GLAPPrimeCore p ↥J) (⟨j, hj⟩ : ↥J) : PQuot p J) ∈ M := by
      rw [hM]
      exact Subgroup.mem_top _
    obtain ⟨t, ht, hteq⟩ := Subgroup.mem_map.1 hmem
    have hk := QuotientGroup.eq.1 hteq
    have hkO : ((t : ↥J)⁻¹ * ⟨j, hj⟩ : ↥J).1 ∈ GLAPPrimeCoreOf p J :=
      (lemma93_mem_core_iff _).1 hk
    have hdecomp : j = (t : ↥J).1 * ((t : ↥J)⁻¹ * ⟨j, hj⟩ : ↥J).1 := by
      simp
    rw [hdecomp]
    exact (S ⊔ GLAPPrimeCoreOf p J).mul_mem (Subgroup.mem_subgroupOf.1 ht)
      (Subgroup.mem_sup_right hkO)
  have hcentre : M ≤ Subgroup.center (PQuot p J) :=
    le_center_of_normal_of_isQuasisimple (isQuasisimple_pQuot_of_glaPComponent hp hJc) hMn hMne
  have hcomm : ∀ s ∈ S, ∀ i ∈ I, ⁅s, i⁆ ∈ GLAPPrimeCoreOf p J := by
    intro s hs i hi
    have hsJ : s ∈ J := hSJ hs
    have hiJ : i ∈ J := hIJ hi
    have hcJ : ⁅s, i⁆ ∈ J := by
      rw [commutatorElement_def]
      exact J.mul_mem (J.mul_mem (J.mul_mem hsJ hiJ) (J.inv_mem hsJ)) (J.inv_mem hiJ)
    have hmem : (QuotientGroup.mk' (GLAPPrimeCore p ↥J) (⟨s, hsJ⟩ : ↥J) : PQuot p J) ∈ M :=
      Subgroup.mem_map.2 ⟨⟨s, hsJ⟩, Subgroup.mem_subgroupOf.2 (Subgroup.mem_sup_left hs), rfl⟩
    have hz := (Subgroup.mem_center_iff.1 (hcentre hmem))
      (QuotientGroup.mk' (GLAPPrimeCore p ↥J) (⟨i, hiJ⟩ : ↥J))
    have h1 : (QuotientGroup.mk' (GLAPPrimeCore p ↥J)
        (⁅(⟨s, hsJ⟩ : ↥J), (⟨i, hiJ⟩ : ↥J)⁆) : PQuot p J) = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hz.symm
    have e : (⁅(⟨s, hsJ⟩ : ↥J), (⟨i, hiJ⟩ : ↥J)⁆ : ↥J) = ⟨⁅s, i⁆, hcJ⟩ :=
      Subtype.ext (by simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv])
    rw [e] at h1
    exact (lemma93_mem_core_iff hcJ).1 ((QuotientGroup.eq_one_iff _).1 h1)
  have hSIO : (⁅S, I⁆ : Subgroup G) ≤ GLAPPrimeCoreOf p J :=
    Subgroup.commutator_le.2 fun s hs i hi => hcomm s hs i hi
  rw [hSI] at hSIO
  exact hnotO hSIO

theorem S_data_J_cov {p : ℕ} (hc : S9Ctx G p) (hd : dLevel G p ≤ 2) {x u : G} {L I Bs S J : Subgroup G}
    (hL : GLAPComponent p (Subgroup.centralizer ({x} : Set G)) L) (hIL : I ≤ L)
    (hBs : GLAIsBmax p Bs) (hu : u ∈ Bs) (hu1 : u ≠ 1) (hx : x ∈ Bs)
    (hS : S ≠ ⊥) (hS2 : IsPGroup 2 S) (hSu : S ≤ Subgroup.centralizer ({u} : Set G))
    (hBsS : Bs ≤ Subgroup.normalizer (S : Set G)) (hSBs : (⁅S, Bs⁆ : Subgroup G) ≠ ⊥)
    (hSI : (⁅S, I⁆ : Subgroup G) = S) (hIS : I ≤ Subgroup.normalizer (S : Set G))
    (hJ : IsSTriple p Bs u J) (hIu : GLAPLayer p (L ⊓ Subgroup.centralizer ({u} : Set G)) ≤ J)
    (hIuc : GLAPComponent p (J ⊓ Subgroup.centralizer ({x} : Set G))
      (GLAPLayer p (L ⊓ Subgroup.centralizer ({u} : Set G))))
    (hIcovL : I ⊔ GLAPPrimeCoreOf p L = L)
    (hIIu : I ≤ GLAPLayer p (L ⊓ Subgroup.centralizer ({u} : Set G))) (hCMu : CentMod p L u)
    (hIJ : I ≤ J) :
    S ≤ J ∧ ¬ S ≤ GLAPPrimeCoreOf p J ∧ ¬ CentMod p J x := by
  have hp := hc.ctx.prime
  have hJc : GLAPComponent p (Subgroup.centralizer ({u} : Set G)) J := hJ.2.2
  have hSJ : S ≤ J := le_of_isSubnormal_commutator_eq hJc.2.1 hIJ hSu hSI
  have hnotO : ¬ S ≤ GLAPPrimeCoreOf p J := by
    intro hSO
    have hOC : GLAPPrimeCoreOf p J ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ({u} : Set G)) :=
      glaPPrimeCoreOf_le_of_isSubnormal hp hJc.2.1
    exact hSBs (hc.stage4.2.2 hd Bs u S hBs hu hu1 (hSO.trans hOC) hS2 hBsS)
  refine ⟨hSJ, hnotO, fun hCM => ?_⟩
  have hxp : IsPGroup p (Subgroup.zpowers x) := isPGroup_zpowers_of_mem hBs.1 hx
  obtain ⟨-, hall, -, -, hcovJ, -⟩ := glaPLayer_inf_centralizer hp hJc hxp hCM
  rw [← hall _ hIuc] at hcovJ
  have hIuI : GLAPLayer p (L ⊓ Subgroup.centralizer ({u} : Set G)) ≤ I ⊔ GLAPPrimeCoreOf p J := by
    have hupu : IsPGroup p (Subgroup.zpowers u) := isPGroup_zpowers_of_mem hBs.1 hu
    have hIuL := (glaPLayer_inf_centralizer hp hL hupu hCMu).2.2.2.2.1
    have hIuLle : GLAPLayer p (L ⊓ Subgroup.centralizer ({u} : Set G)) ≤ L :=
      ((glaPLayer_inf_centralizer hp hL hupu hCMu).1).1.trans inf_le_left
    have hO_L : GLAPPrimeCoreOf p (GLAPLayer p (L ⊓ Subgroup.centralizer ({u} : Set G))) =
        GLAPLayer p (L ⊓ Subgroup.centralizer ({u} : Set G)) ⊓ GLAPPrimeCoreOf p L :=
      (cover_facts hp hIuLle hIuL).1
    have hO_J : GLAPPrimeCoreOf p (GLAPLayer p (L ⊓ Subgroup.centralizer ({u} : Set G))) =
        GLAPLayer p (L ⊓ Subgroup.centralizer ({u} : Set G)) ⊓ GLAPPrimeCoreOf p J :=
      (cover_facts hp hIu hcovJ).1
    intro y hy
    have hyL : y ∈ L := hIuLle hy
    have hy' : y ∈ I ⊔ GLAPPrimeCoreOf p L := by
      rw [hIcovL]
      exact hyL
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right I _
      (fun g hg => le_normalizer_glaPPrimeCoreOf p L (hIL hg))] at hy'
    obtain ⟨i, hi, o, ho, hio⟩ := Set.mem_mul.mp hy'
    have hoIu : o ∈ GLAPLayer p (L ⊓ Subgroup.centralizer ({u} : Set G)) := by
      have e : o = i⁻¹ * y := by
        rw [← hio]
        group
      rw [e]
      exact (GLAPLayer p (L ⊓ Subgroup.centralizer ({u} : Set G))).mul_mem
        ((GLAPLayer p (L ⊓ Subgroup.centralizer ({u} : Set G))).inv_mem (hIIu hi)) hy
    have hoJ : o ∈ GLAPPrimeCoreOf p J := by
      have hoO : o ∈ GLAPPrimeCoreOf p (GLAPLayer p (L ⊓ Subgroup.centralizer ({u} : Set G))) := by
        rw [hO_L]
        exact Subgroup.mem_inf.2 ⟨hoIu, ho⟩
      rw [hO_J] at hoO
      exact (Subgroup.mem_inf.1 hoO).2
    rw [← hio]
    exact Subgroup.mul_mem_sup hi hoJ
  have hIcov : I ⊔ GLAPPrimeCoreOf p J = J := by
    apply le_antisymm (sup_le hIJ (Subgroup.map_subtype_le _))
    calc J = GLAPLayer p (L ⊓ Subgroup.centralizer ({u} : Set G)) ⊔ GLAPPrimeCoreOf p J := hcovJ.symm
      _ ≤ I ⊔ GLAPPrimeCoreOf p J := sup_le hIuI le_sup_right
  have hON : J ≤ Subgroup.normalizer ((S ⊔ GLAPPrimeCoreOf p J : Subgroup G) : Set G) := by
    have hIN : I ≤ Subgroup.normalizer ((S ⊔ GLAPPrimeCoreOf p J : Subgroup G) : Set G) := fun g hg =>
      Subgroup.inf_normalizer_le_normalizer_sup S (GLAPPrimeCoreOf p J)
        ⟨hIS hg, le_normalizer_glaPPrimeCoreOf p J (hIJ hg)⟩
    have hOJ : GLAPPrimeCoreOf p J ≤
        Subgroup.normalizer ((S ⊔ GLAPPrimeCoreOf p J : Subgroup G) : Set G) :=
      le_sup_right.trans Subgroup.le_normalizer
    calc J = I ⊔ GLAPPrimeCoreOf p J := hIcov.symm
      _ ≤ _ := sup_le hIN hOJ
  have hSOJ : (S ⊔ GLAPPrimeCoreOf p J : Subgroup G) ≤ J :=
    sup_le hSJ (Subgroup.map_subtype_le _)
  have hTn : ((S ⊔ GLAPPrimeCoreOf p J).subgroupOf J).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSOJ).2 hON
  set M : Subgroup (PQuot p J) :=
    ((S ⊔ GLAPPrimeCoreOf p J).subgroupOf J).map (QuotientGroup.mk' (GLAPPrimeCore p ↥J)) with hMdef
  have hMn : M.Normal := hTn.map _ (QuotientGroup.mk'_surjective _)
  have hMne : M ≠ ⊤ := by
    intro hM
    refine l93c_not_two_covers hp hJc hSJ hS2 (le_antisymm hSOJ fun j hj => ?_)
    have hmem : (QuotientGroup.mk' (GLAPPrimeCore p ↥J) (⟨j, hj⟩ : ↥J) : PQuot p J) ∈ M := by
      rw [hM]
      exact Subgroup.mem_top _
    obtain ⟨t, ht, hteq⟩ := Subgroup.mem_map.1 hmem
    have hk := QuotientGroup.eq.1 hteq
    have hkO : ((t : ↥J)⁻¹ * ⟨j, hj⟩ : ↥J).1 ∈ GLAPPrimeCoreOf p J :=
      (lemma93_mem_core_iff _).1 hk
    have hdecomp : j = (t : ↥J).1 * ((t : ↥J)⁻¹ * ⟨j, hj⟩ : ↥J).1 := by
      simp
    rw [hdecomp]
    exact (S ⊔ GLAPPrimeCoreOf p J).mul_mem (Subgroup.mem_subgroupOf.1 ht)
      (Subgroup.mem_sup_right hkO)
  have hcentre : M ≤ Subgroup.center (PQuot p J) :=
    le_center_of_normal_of_isQuasisimple (isQuasisimple_pQuot_of_glaPComponent hp hJc) hMn hMne
  have hcomm : ∀ s ∈ S, ∀ i ∈ I, ⁅s, i⁆ ∈ GLAPPrimeCoreOf p J := by
    intro s hs i hi
    have hsJ : s ∈ J := hSJ hs
    have hiJ : i ∈ J := hIJ hi
    have hcJ : ⁅s, i⁆ ∈ J := by
      rw [commutatorElement_def]
      exact J.mul_mem (J.mul_mem (J.mul_mem hsJ hiJ) (J.inv_mem hsJ)) (J.inv_mem hiJ)
    have hmem : (QuotientGroup.mk' (GLAPPrimeCore p ↥J) (⟨s, hsJ⟩ : ↥J) : PQuot p J) ∈ M :=
      Subgroup.mem_map.2 ⟨⟨s, hsJ⟩, Subgroup.mem_subgroupOf.2 (Subgroup.mem_sup_left hs), rfl⟩
    have hz := (Subgroup.mem_center_iff.1 (hcentre hmem))
      (QuotientGroup.mk' (GLAPPrimeCore p ↥J) (⟨i, hiJ⟩ : ↥J))
    have h1 : (QuotientGroup.mk' (GLAPPrimeCore p ↥J)
        (⁅(⟨s, hsJ⟩ : ↥J), (⟨i, hiJ⟩ : ↥J)⁆) : PQuot p J) = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hz.symm
    have e : (⁅(⟨s, hsJ⟩ : ↥J), (⟨i, hiJ⟩ : ↥J)⁆ : ↥J) = ⟨⁅s, i⁆, hcJ⟩ :=
      Subtype.ext (by simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv])
    rw [e] at h1
    exact (lemma93_mem_core_iff hcJ).1 ((QuotientGroup.eq_one_iff _).1 h1)
  have hSIO : (⁅S, I⁆ : Subgroup G) ≤ GLAPPrimeCoreOf p J :=
    Subgroup.commutator_le.2 fun s hs i hi => hcomm s hs i hi
  rw [hSI] at hSIO
  exact hnotO hSIO

private theorem l93c_cover_of_le {p : ℕ} (hp : p.Prime) {I Iu L : Subgroup G} (hIIu : I ≤ Iu)
    (hIuL : Iu ≤ L) (hcov : I ⊔ GLAPPrimeCoreOf p L = L)
    (hOL : L ≤ Subgroup.normalizer (GLAPPrimeCoreOf p L : Set G)) :
    I ⊔ GLAPPrimeCoreOf p Iu = Iu := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hIL : I ≤ L := hIIu.trans hIuL
  have hM : Iu ≤ I ⊔ (Iu ⊓ GLAPPrimeCoreOf p L) := by
    intro y hy
    have hy' : y ∈ I ⊔ GLAPPrimeCoreOf p L := by
      rw [hcov]
      exact hIuL hy
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right I _
      (fun g hg => hOL (hIL hg))] at hy'
    obtain ⟨i, hi, o, ho, hio⟩ := Set.mem_mul.mp hy'
    have hoIu : o ∈ Iu := by
      have e : o = i⁻¹ * y := by
        rw [← hio]
        group
      rw [e]
      exact Iu.mul_mem (Iu.inv_mem (hIIu hi)) hy
    rw [← hio]
    exact Subgroup.mul_mem_sup hi (Subgroup.mem_inf.2 ⟨hoIu, ho⟩)
  have hMn : ((Iu ⊓ GLAPPrimeCoreOf p L).subgroupOf Iu).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer (inf_le_left : Iu ⊓ GLAPPrimeCoreOf p L ≤ Iu)]
    intro g hg
    exact l93c_mem_normalizer_inf (Subgroup.le_normalizer hg) (hOL (hIuL hg))
  have hMcop : Nat.Coprime p (Nat.card ↥(Iu ⊓ GLAPPrimeCoreOf p L)) :=
    Nat.Coprime.coprime_dvd_right
      (Subgroup.card_dvd_of_le (inf_le_right : Iu ⊓ GLAPPrimeCoreOf p L ≤ GLAPPrimeCoreOf p L))
      (CFSG.HardMathSupport.Solomon.Coordinator.i183_coprime_card_glaPPrimeCoreOf hp L)
  have hMle : Iu ⊓ GLAPPrimeCoreOf p L ≤ GLAPPrimeCoreOf p Iu :=
    l93c_le_glaPPrimeCoreOf inf_le_left hMn hMcop
  apply le_antisymm
  · exact sup_le hIIu (Subgroup.map_subtype_le _)
  · exact hM.trans (sup_le_sup_left hMle I)

theorem lemma93_d2 {p : ℕ} (hc : S9Ctx G p) (hin : Lemma93Inputs G p) (hd : dLevel G p ≤ 2)
    {B : Subgroup G} {x : G} {L N : Subgroup G} (h : H92 p B x L) (hess : IsEssential p B x)
    (hmax : IsMaxRankIn p B (Subgroup.centralizer ({x} : Set G))) (hnoGB : ¬ IsGB p B L)
    (hlev : fullCoverLevel p (PQuot p L) ≤ 2) (hN : IsTwoLocal N)
    (hcov : Covers p N (Subgroup.centralizer ({x} : Set G))) : False := by
  have hp := hc.ctx.prime
  have hp2 := hc.ctx.odd
  have hA := exists_cent_rank_two hc hin hd h hess hmax hnoGB
  have hγ := nonInner_or_center hc h hmax hA
  have hX : CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({x} : Set G)) := isKGroup_cx hc h.ne_one
  have hlist : catalogIs (PSimple p L) (isList93 p) :=
    hin.list93 hp hp2 _ L B hX h.comp h.chev2 hlev h.bmax.1 h.norm (h.pow_three_mul_le hc) hγ
  obtain ⟨U, N', hst⟩ := exists_stage93 hc h hN hcov hmax hA
  have hUBs : U ≤ bstar B U := le_sup_right
  obtain ⟨I, hI, hIL, hIcov, hBsI⟩ := exists_cover_component hp hp2 h.comp hst.U_le hst.U_el
    hst.x_mem (hUBs.trans hst.Bs_le_N) hst.N_cov hst.Bs_norm hst.Bs_cent_U hst.Bs_le_N
  obtain ⟨u, huU, hu1, S, hS, hS2, hSu, hIS, hBsS, hSI⟩ := exists_S_data hc hst.N_two hst.U_el
    hst.U_card (hUBs.trans hst.Bs_le_N) hst.x_mem hI hst.Bs_cent_U hst.Bs_le_N hBsI hUBs
  have hSBs : (⁅S, bstar B U⁆ : Subgroup G) ≠ ⊥ :=
    commutator_ne_bot_of_cover hp h.comp hI hIL hIcov hst.Bs_norm hBsI hst.not_cent hS hSI hBsS
  have hQ : IsEmpty (↥S ≃* QuaternionGroup 2) := isEmpty_quaternion hI hS hSI hIS
  have huBs : u ∈ bstar B U := hUBs huU
  have hxBs : x ∈ bstar B U := hUBs hst.x_mem
  have hess_u : IsEssential p (bstar B U) u := ⟨huBs, hu1, S, hSu, hS2, hBsS, hSBs, fun _ => hQ⟩
  obtain ⟨J, hJst, hBsJ, hIJ, hIuJ, hIuc, hIIu⟩ := exists_J hc hin.i183 h.comp hst.x_mem huU
    hst.U_le hst.U_el hI hIL hIcov (hd.trans (by norm_num)) hst.Bs_bmax hUBs hu1 hess_u hst.Bs_norm
  have hu_cm : CentMod p L u := centMod_iff.2 (hst.U_le huU).2
  obtain ⟨hSJ, hSnot, hxnot⟩ := S_data_J_cov hc hd h.comp hIL hst.Bs_bmax huBs hu1 hxBs hS hS2 hSu hBsS
    hSBs hSI hIS hJst hIuJ hIuc hIcov hIIu hu_cm hIJ
  have hJlev : fullCoverLevel p (PQuot p J) ≤ 2 := by
    have h1 := tripleLevel_le_dLevel hJst
    unfold tripleLevel at h1
    split_ifs at h1 with hG
    · omega
    · omega
  obtain ⟨-, -, -, -, -, ⟨eIL⟩⟩ :=
    glaPLayer_inf_centralizer hp h.comp (isPGroup_zpowers_of_mem hst.U_el huU) hu_cm
  have hIuL : Nonempty (PSimple p (GLAPLayer p (L ⊓ Subgroup.centralizer ({u} : Set G))) ≃*
      PSimple p L) := nonempty_pSimple_congr eIL
  obtain ⟨fIL⟩ := hIuL
  have hlistIu : catalogIs (PSimple p (GLAPLayer p (L ⊓ Subgroup.centralizer ({u} : Set G))))
      (isList93 p) := (catalogIs_congr fIL).2 hlist
  have hOJ : J ≤ Subgroup.normalizer (GLAPPrimeCoreOf p J : Set G) := le_normalizer_glaPPrimeCoreOf p J
  have hIN : I ≤ Subgroup.normalizer ((S ⊔ GLAPPrimeCoreOf p J : Subgroup G) : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_sup S (GLAPPrimeCoreOf p J) ⟨hIS hg, hOJ (hIJ hg)⟩
  have hIuLle : GLAPLayer p (L ⊓ Subgroup.centralizer ({u} : Set G)) ≤ L :=
    ((glaPLayer_inf_centralizer hp h.comp (isPGroup_zpowers_of_mem hst.U_el huU) hu_cm).1).1.trans
      inf_le_left
  have hcovIu := l93c_cover_of_le hp hIIu hIuLle hIcov (le_normalizer_glaPPrimeCoreOf p L)
  have hxN : x ∈ Subgroup.normalizer ((S ⊔ GLAPPrimeCoreOf p J : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_sup S (GLAPPrimeCoreOf p J)
      ⟨hBsS hxBs, normalizer_le_normalizer_glaPPrimeCoreOf p J (hBsJ hxBs)⟩
  have hJc : GLAPComponent p (Subgroup.centralizer ({u} : Set G)) J := hJst.2.2
  have hY : CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({u} : Set G)) := isKGroup_cx hc hu1
  obtain ⟨hp3, hcat3⟩ := hin.i137 hp hp2 _ J _ S x hY hJc hJlev hSJ hS2 hSnot (hBsJ hxBs)
    (hst.U_el.2 x hst.x_mem) hxnot hIuc ⟨I, hIIu, hcovIu, hIN⟩ hxN hlistIu
  subst hp3
  have hcatL : catalogIs (PSimple 3 L) isL3four := (catalogIs_congr fIL).1 hcat3
  have h1 := hin.sl34 _ L B h.comp hcatL h.bmax.1 h.norm
  have h2 := h.card_inf_centMod hp
  have h3 := h.pow_four_le hc
  norm_num at h3
  omega

theorem lemma93 {p : ℕ} (hc : S9Ctx G p) (hin : Lemma93Inputs G p) {B : Subgroup G} {x : G}
    {L N : Subgroup G} (h : H92 p B x L) (hN : IsTwoLocal N)
    (hcov : Covers p N (Subgroup.centralizer ({x} : Set G))) : IsGB p B L := by
  by_contra hnoGB
  have hp := hc.ctx.prime
  have hp2 := hc.ctx.odd
  have hmax : IsMaxRankIn p B (Subgroup.centralizer ({x} : Set G)) :=
    isMaxRankIn_of_covers hp hp2 h.bmax hN hcov
  have hSC : IsSC p B := isSC_of_isMaxRankIn hp h.bmax.1 h.mem hmax
  have hS0 : IsS0 p B x L := by
    rcases h.alt with h0 | hGB | ⟨hnsc, _⟩
    · exact h0
    · exact absurd hGB hnoGB
    · exact absurd hSC hnsc
  have hess : IsEssential p B x := hS0.1.2.1
  have hnoG : ¬ IsGStar p B L := fun hG => hnoGB (isGB_of_isGStar hG h.norm)
  have hmin := fullCoverLevel_min_eq_dLevel hS0 hnoG
  have hf4 := fullCoverLevel_le_four p (PQuot p L)
  have hmaxL : IsMaxRankIn p B (L ⊔ B) :=
    fun E hEY hE => hmax E (hEY.trans (sup_le h.comp.1 h.le_cx)) hE
  by_cases hd4 : dLevel G p = 4
  · exact d4_contradiction_cover hc hin.i183 hin.i264 hin.i91 hin.i147 hS0 h.norm hd4 hnoG hmaxL
      hN hcov
  · by_cases hd3 : fullCoverLevel p (PQuot p L) = 3
    · exact hin.k3 p (PQuot p L) (k3Cover_of_fullCoverLevel_eq_three hd3) h.chev2
    · have hlev : fullCoverLevel p (PQuot p L) ≤ 2 := by omega
      have hd : dLevel G p ≤ 2 := by omega
      exact lemma93_d2 hc hin hd h hess hmax hnoGB hlev hN hcov


theorem odd_core_of_not_isGB {p : ℕ} (hc : S9Ctx G p) (hin : Lemma93Inputs G p) {B : Subgroup G}
    {x : G} {L : Subgroup G} (h : H92 p B x L) (hnoGB : ¬ IsGB p B L) :
    Odd (Nat.card (GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G)))) := by
  by_contra hev
  obtain ⟨N, hN, hcov⟩ := exists_covers_of_even hc.ctx.prime hc.ctx.odd (Nat.not_odd_iff_even.1 hev)
  exact hnoGB (lemma93 hc hin h hN hcov)

end CFSG.LocalAnalysis.GLTheoremA.S9
