module

public import CFSG.Quasithin.Vol2.Ch12Sec8OnePara
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec8OneFlag
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec8OneLemma8
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec9Lemma7Act

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.SL2Model
open scoped IsMulCommutative MatrixGroups

namespace L128P

variable {G : Type} [Group G]

variable [CFSG.GH74.QTGen4.Finite4 G]

theorem mem_p128_of_conj_F4 (h1222 : Stmt12_2_2_F4) {T L V : Subgroup G} {n : ℕ}
    (h : Hyp1281One G T L V n) {V₂ : Subgroup G} (hV₂ : IsTSub T V V₂ 2) {l : G} (hlL : l ∈ L)
    (hlN : l ∈ Subgroup.normalizer (V : Set G))
    (hl : ∀ x ∈ V, l * x * l⁻¹ * x⁻¹ ∈ V₂) : l ∈ p128 T L V := by
  refine Subgroup.mem_inf.2 ⟨Subgroup.mem_sup_left hlL,
    Subgroup.mem_iInf.2 fun Y => Subgroup.mem_iInf.2 fun hY => ?_⟩
  obtain ⟨i, hi, hYi⟩ := hY
  have hV₂Y : V₂ ≤ Y := by
    rcases tinv_comparable_of_hyp1281One_F4 h1222 h hV₂.1 hYi.1 hV₂.2.2 hYi.2.2 with hle | hle
    · exact hle
    · have heq : Y = V₂ := Subgroup.eq_of_le_of_card_ge hle (by
        rw [hV₂.2.1, hYi.2.1]
        exact Nat.pow_le_pow_right (by norm_num) hi)
      rw [heq]
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have hyV := hYi.1 hy
    have e : l * y * l⁻¹ = (l * y * l⁻¹ * y⁻¹) * y := by group
    rw [e]
    exact Y.mul_mem (hV₂Y (hl y hyV)) hy
  · intro hy
    have hyV : y ∈ V := (Subgroup.mem_normalizer_iff.1 hlN y).2 (hYi.1 hy)
    have e : y = (l * y * l⁻¹ * y⁻¹)⁻¹ * (l * y * l⁻¹) := by group
    rw [e]
    exact Y.mul_mem (Y.inv_mem (hV₂Y (hl y hyV))) hy

theorem exists_tflag_F4 (h1222 : Stmt12_2_2_F4) {T L V : Subgroup G} {n : ℕ}
    (h : Hyp1281One G T L V n) : ∃ Vs : ℕ → Subgroup G, ∀ i, IsTSub T V (Vs i) (min i n) := by
  obtain ⟨hcard, hsq, hab⟩ := h.card_sq
  obtain ⟨-, hTV⟩ := h.hyp.le_and_normalizes_F4 h1222
  have hex := exists_tsub h.hyp.sylow.1 hsq hab hTV hcard
  exact ⟨fun i => Classical.choose (hex (min i n) (min_le_right i n)),
    fun i => Classical.choose_spec (hex (min i n) (min_le_right i n))⟩

theorem pow_mem_T_of_mem_centralizer_F4 (h1222 : Stmt12_2_2_F4) {T L V : Subgroup G} {n : ℕ}
    (h : Hyp1281One G T L V n) {V₁ V₂ : Subgroup G} (hV₁ : IsTSub T V V₁ 1)
    (hle : V₁ ≤ V₂) {x : G} (hxP : x ∈ p128 T L V)
    (hxC : x ∈ Subgroup.centralizer (V₂ : Set G)) : x ^ (2 ^ n) ∈ T := by
  obtain ⟨hcard, hsq, hab⟩ := h.card_sq
  obtain ⟨Vs, hVs⟩ := exists_tflag_F4 h1222 h
  have hVsV : ∀ i, Vs i ≤ V := fun i => (hVs i).1
  have hcardVs : ∀ i, Nat.card (Vs i) = 2 ^ min i n := fun i => (hVs i).2.1

  have hxV₁ : x ∈ Subgroup.normalizer (V₁ : Set G) :=
    Subgroup.centralizer_le_normalizer _
      (Subgroup.centralizer_le (show (V₁ : Set G) ⊆ V₂ from hle) hxC)
  have hxN : ∀ i, x ∈ Subgroup.normalizer (Vs i : Set G) := by
    intro i
    rcases Nat.lt_or_ge (min i n) 2 with hlt | hge
    · rcases (show min i n = 0 ∨ min i n = 1 by omega) with h0 | h1
      · have hbot : Vs i = ⊥ := Subgroup.eq_bot_of_card_eq _ (by rw [hcardVs, h0, pow_zero])
        rw [hbot]
        exact Subgroup.mem_normalizer_iff.2 fun y => by simp
      · have heq : Vs i = V₁ := unique1282_F4 h1222 G T L V n h 1 _ _ (h1 ▸ hVs i) hV₁
        rw [heq]
        exact hxV₁
    · exact p128_le_normalizer hge (hVs i) hxP

  have hstep : ∀ i, ∀ v ∈ Vs (i + 1), x * v * x⁻¹ * v⁻¹ ∈ Vs i := by
    intro i v hv
    have hle' : Vs i ≤ Vs (i + 1) := by
      rcases tinv_comparable_of_hyp1281One_F4 h1222 h (hVsV i) (hVsV (i + 1)) (hVs i).2.2
        (hVs (i + 1)).2.2 with h1 | h1
      · exact h1
      · have hc := Subgroup.card_le_of_le h1
        rw [hcardVs, hcardVs] at hc
        have hmono : min i n ≤ min (i + 1) n := min_le_min_right n (Nat.le_succ i)
        have heq : Vs (i + 1) = Vs i := Subgroup.eq_of_le_of_card_ge h1 (by
          rw [hcardVs, hcardVs]
          exact Nat.pow_le_pow_right (by norm_num) hmono)
        rw [heq]
    have hrel := Subgroup.relIndex_mul_card (Vs i) (Vs (i + 1))
    rw [inf_eq_left.2 hle', hcardVs, hcardVs] at hrel
    have hidx : (Vs i).relIndex (Vs (i + 1)) = 1 ∨ (Vs i).relIndex (Vs (i + 1)) = 2 := by
      rcases (show min (i + 1) n = min i n ∨ min (i + 1) n = min i n + 1 by omega) with h1 | h1
      · left
        rw [h1] at hrel
        have hpos : 0 < 2 ^ min i n := pow_pos (by norm_num) _
        exact Nat.eq_of_mul_eq_mul_right hpos (hrel.trans (one_mul _).symm)
      · right
        have hpos : 0 < 2 ^ min i n := pow_pos (by norm_num) _
        have h2 : (Vs i).relIndex (Vs (i + 1)) * 2 ^ min i n = 2 * 2 ^ min i n := by
          rw [hrel, h1, pow_succ, mul_comm]
        exact Nat.eq_of_mul_eq_mul_right hpos h2
    exact commutator_mem_of_relIndex_le_two hidx (hxN i) (hxN (i + 1)) hv

  have hVsn : Vs (2 ^ n) = V := by
    have hmin : min (2 ^ n) n = n := min_eq_right (Nat.lt_two_pow_self).le
    refine Subgroup.eq_of_le_of_card_ge (hVsV _) ?_
    rw [hcardVs, hmin, hcard]
  have hcen : ∀ v ∈ V, x ^ (2 ^ n) * v * (x ^ (2 ^ n))⁻¹ * v⁻¹ ∈ V₁ := by
    intro v hv
    have h1 := pow_two_pow_conj_mem hsq Vs hVsV hstep n 0 v (by rw [zero_add, hVsn]; exact hv)
    have hbot : Vs 0 = ⊥ := Subgroup.eq_bot_of_card_eq _ (by rw [hcardVs]; simp)
    rw [hbot, Subgroup.mem_bot] at h1
    rw [h1]
    exact V₁.one_mem
  have hxLT : x ^ (2 ^ n) ∈ L ⊔ T :=
    (L ⊔ T).pow_mem ((show p128 T L V ≤ L ⊔ T from inf_le_left) hxP) _
  have hxNV₁ : x ^ (2 ^ n) ∈ Subgroup.normalizer (V₁ : Set G) :=
    Subgroup.pow_mem _ hxV₁ _
  exact L1297.centralizerMod_sup_le_T_F4 h1222 h hV₁ ⟨hxLT, hxNV₁, hcen⟩

theorem isPGroup_centralizer_p128_F4 (h1222 : Stmt12_2_2_F4) {T L V : Subgroup G} {n : ℕ}
    (h : Hyp1281One G T L V n) {V₁ V₂ : Subgroup G} (hV₁ : IsTSub T V V₁ 1)
    (hle : V₁ ≤ V₂) :
    IsPGroup 2 ↥(p128 T L V ⊓ Subgroup.centralizer (V₂ : Set G)) := by
  intro x
  have hx := pow_mem_T_of_mem_centralizer_F4 h1222 h hV₁ hle x.2.1 x.2.2
  obtain ⟨k, hk⟩ := h.hyp.sylow.1 ⟨_, hx⟩
  refine ⟨n + k, Subtype.ext ?_⟩
  have h1 : ((x : G) ^ 2 ^ n) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  simpa [pow_add, pow_mul] using h1

theorem exists_rotation_mem_F4 (h1222 : Stmt12_2_2_F4) {T L V : Subgroup G} {n : ℕ}
    (h : Hyp1281One G T L V n) {V₁ V₂ : Subgroup G} (hV₁ : IsTSub T V V₁ 1)
    (hV₂ : IsTSub T V V₂ 2) (hle : V₁ ≤ V₂) {a b : G} (ha : a ∈ V₁) (ha1 : a ≠ 1)
    (hb : b ∈ V₂) (hbV₁ : b ∉ V₁) :
    ∃ k ∈ oTwoUpper (p128 T L V), k * a * k⁻¹ = b ∧ k * b * k⁻¹ = a * b ∧
      ∀ x ∈ V, k * x * k⁻¹ * x⁻¹ ∈ V₂ := by
  classical
  obtain ⟨hcard, hsq, hab⟩ := h.card_sq
  obtain ⟨hcV, -⟩ := h.natural
  have haV : a ∈ V := hV₁.1 ha
  have hbV : b ∈ V := hV₂.1 hb
  let _ := zmodModuleOf hsq
  set a' : Additive ↥V := Additive.ofMul ⟨a, haV⟩ with ha'
  set b' : Additive ↥V := Additive.ofMul ⟨b, hbV⟩ with hb'
  set S : Submodule (ZMod 2) (Additive ↥V) := (ZMod 2) ∙ a' ⊔ (ZMod 2) ∙ b' with hS
  obtain ⟨C, hSC⟩ := Submodule.exists_isCompl S
  have haS : a' ∈ S := Submodule.mem_sup_left (Submodule.mem_span_singleton_self _)
  have hbS : b' ∈ S := Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have ha0 : a' ≠ 0 := fun h0 => ha1 (by
    have := congrArg (fun x : Additive ↥V => ((Additive.toMul x : ↥V) : G)) h0
    simpa [ha'] using this)
  have hab' : a' ≠ b' := fun h0 => hbV₁ (by
    have := congrArg (fun x : Additive ↥V => ((Additive.toMul x : ↥V) : G)) h0
    simp only [ha', hb', toMul_ofMul] at this
    rw [← this]
    exact ha)
  have hb0 : b' ≠ 0 := fun h0 => hbV₁ (by
    have := congrArg (fun x : Additive ↥V => ((Additive.toMul x : ↥V) : G)) h0
    simp only [hb', toMul_ofMul, toMul_zero, OneMemClass.coe_one] at this
    rw [this]
    exact V₁.one_mem)

  have hnot : ∀ {x y : Additive ↥V}, x ∈ S → y ∈ S → x ≠ 0 → x ≠ y → x ∉ C ⊔ (ZMod 2) ∙ y := by
    intro x y hx hy hx0 hxy hmem
    obtain ⟨c, hc, q, hq, hcq⟩ := Submodule.mem_sup.1 hmem
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hq
    have hcS : c ∈ S := by
      have e : c = x - t • y := by rw [← hcq]; abel
      rw [e]
      exact S.sub_mem hx (S.smul_mem t hy)
    have hc0 : c = 0 := by
      have := hSC.inf_eq_bot
      have hmem' : c ∈ S ⊓ C := ⟨hcS, hc⟩
      rw [this] at hmem'
      exact hmem'
    rw [hc0, zero_add] at hcq
    rcases zmod_two_cases t with rfl | rfl
    · exact hx0 (by rw [← hcq, zero_smul])
    · exact hxy (by rw [← hcq, one_smul])
  obtain ⟨ρ, hρ3, hρa, hρb, hρC⟩ := exists_rotation (hnot haS hbS ha0 hab')
    (hnot hbS haS hb0 (Ne.symm hab'))

  have hρS : ∀ s ∈ S, ρ s ∈ S := by
    intro s hs
    obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.1 hs
    obtain ⟨t₁, rfl⟩ := Submodule.mem_span_singleton.1 hp
    obtain ⟨t₂, rfl⟩ := Submodule.mem_span_singleton.1 hq
    rw [map_add, map_smul, map_smul, hρa, hρb]
    exact S.add_mem (S.smul_mem _ hbS) (S.smul_mem _ (S.sub_mem (S.neg_mem haS) hbS))
  have hSV₂ : ∀ s ∈ S, ((Additive.toMul s : ↥V) : G) ∈ V₂ := by
    intro s hs
    have hle2 : S ≤ subOf (V := V) V₂ := sup_le
      ((Submodule.span_singleton_le_iff_mem _ _).2 (mem_subOf.2 (hle ha)))
      ((Submodule.span_singleton_le_iff_mem _ _).2 (mem_subOf.2 hb))
    exact mem_subOf.1 (hle2 hs)

  have hρmod : ∀ x : Additive ↥V, ρ x - x ∈ S := by
    intro x
    have hx : x ∈ S ⊔ C := by rw [hSC.sup_eq_top]; trivial
    obtain ⟨s, hs, c, hc, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add, hρC c hc]
    have e : ρ s + c - (s + c) = ρ s - s := by abel
    rw [e]
    exact S.sub_mem (hρS s hs) hs
  have hneg : ∀ y : Additive ↥V, -y = y := fun y => by
    have h1 : y + y = 0 := by
      rw [← one_smul (ZMod 2) y, ← add_smul, show (1 + 1 : ZMod 2) = 0 from rfl, zero_smul]
    exact neg_eq_of_add_eq_zero_left h1

  have hα3 : mulAutOfLin ρ ^ 3 = 1 := by
    refine MulEquiv.ext fun x => ?_
    rw [pow_three, MulAut.mul_apply, MulAut.mul_apply, mulAutOfLin_apply, mulAutOfLin_apply,
      mulAutOfLin_apply, ofMul_toMul, ofMul_toMul, hρ3, toMul_ofMul, MulAut.one_apply]
  have hαL : mulAutOfLin ρ ∈ autOn L V := by
    rw [autOn_eq_top_of_hyp1281One h]
    exact Subgroup.mem_top _
  obtain ⟨⟨l, hlN⟩, hlL, hlα⟩ := hαL
  have hlL' : l ∈ L := Subgroup.mem_subgroupOf.1 hlL
  have hconj : ∀ x (hx : x ∈ V), l * x * l⁻¹ = ((mulAutOfLin ρ ⟨x, hx⟩ : ↥V) : G) := by
    intro x hx
    rw [← hlα]
    rfl
  have hmod : ∀ x (hx : x ∈ V), ((mulAutOfLin ρ ⟨x, hx⟩ : ↥V) : G) * x⁻¹ ∈ V₂ := by
    intro x hx
    have h1 := hSV₂ _ (hρmod (Additive.ofMul ⟨x, hx⟩))
    rw [toMul_sub, toMul_ofMul, Subgroup.coe_div, div_eq_mul_inv] at h1
    rw [mulAutOfLin_apply]
    exact h1
  have hlP : l ∈ p128 T L V := mem_p128_of_conj_F4 h1222 h hV₂ hlL' hlN fun x hx => by
    rw [hconj x hx]
    exact hmod x hx
  obtain ⟨k, hk, hkx⟩ := exists_mem_oTwoUpper_of_order_three hlP (mulAutOfLin ρ) hα3 hconj
  refine ⟨k, hk, ?_, ?_, fun x hx => ?_⟩
  · rw [hkx a haV, mulAutOfLin_apply, ← ha', hρa, hb', toMul_ofMul]
  · rw [hkx b hbV, mulAutOfLin_apply, ← hb', hρb, sub_eq_add_neg, hneg, hneg, toMul_add, ha', hb',
      toMul_ofMul, toMul_ofMul, Subgroup.coe_mul]
  · rw [hkx x hx]
    exact hmod x hx

theorem pCoreOf_le_centralizer_F4 (h1222 : Stmt12_2_2_F4) {T L V : Subgroup G} {n : ℕ}
    (h : Hyp1281One G T L V n) {V₁ V₂ : Subgroup G} (hV₁ : IsTSub T V V₁ 1)
    (hV₂ : IsTSub T V V₂ 2) (hle : V₁ ≤ V₂) :
    pCoreOf 2 (oTwoUpper (p128 T L V) ⊔ T) ≤ Subgroup.centralizer (V₂ : Set G) := by
  have hV₁2 : Nat.card V₁ = 2 := by simpa using hV₁.2.1
  have hV₂4 : Nat.card V₂ = 4 := by simpa using hV₂.2.1
  obtain ⟨a, ha, ha1, b, hb, hbV₁⟩ := exists_gens hV₁2 hV₂4
  obtain ⟨k, hk, hka, hkb, -⟩ := exists_rotation_mem_F4 h1222 h hV₁ hV₂ hle ha ha1 hb hbV₁
  set K := oTwoUpper (p128 T L V) with hK
  have hTsyl : QuasithinUnique.IsSylowTwoOf T (K ⊔ T) :=
    isSylowTwoOf_of_quasithinIsSylowTwo h.hyp.sylow le_sup_right
  have hOT : pCoreOf 2 (K ⊔ T) ≤ T := pCoreOf_two_le_of_isSylowTwoOf hTsyl
  have hkN : k ∈ Subgroup.normalizer (pCoreOf 2 (K ⊔ T) : Set G) :=
    LieType.BorelTits.le_normalizer_pCoreOf 2 (K ⊔ T) (Subgroup.mem_sup_left hk)
  have hfix : ∀ o ∈ pCoreOf 2 (K ⊔ T), o * a * o⁻¹ = a := fun o ho =>
    L1297.conj_eq_of_mem_normalizer hV₁2 ha (hV₁.2.2 (hOT ho))
  intro o ho
  have h1 : o * b * o⁻¹ = b := by
    have ho' : k⁻¹ * o * k ∈ pCoreOf 2 (K ⊔ T) := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hkN) o).mp ho
      simpa [mul_assoc] using this
    have := hfix _ ho'
    rw [← hka]
    calc o * (k * a * k⁻¹) * o⁻¹ = k * ((k⁻¹ * o * k) * a * (k⁻¹ * o * k)⁻¹) * k⁻¹ := by group
      _ = k * a * k⁻¹ := by rw [this]
  have h2 : o * (a * b) * o⁻¹ = a * b := by
    calc o * (a * b) * o⁻¹ = (o * a * o⁻¹) * (o * b * o⁻¹) := by group
      _ = a * b := by rw [hfix o ho, h1]
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  rcases eq_of_mem_four hle hV₁2 hV₂4 ha ha1 hbV₁ hb hv with e | e | e | e <;> rw [e]
  · group
  · calc a * o = (o * a * o⁻¹) * o := by rw [hfix o ho]
      _ = o * a := by group
  · calc b * o = (o * b * o⁻¹) * o := by rw [h1]
      _ = o * b := by group
  · calc a * b * o = (o * (a * b) * o⁻¹) * o := by rw [h2]
      _ = o * (a * b) := by group

theorem mem_centralizer_iff_mem_pCoreOf_F4 (h1222 : Stmt12_2_2_F4) {T L V : Subgroup G} {n : ℕ}
    (h : Hyp1281One G T L V n) {V₁ V₂ : Subgroup G} (hV₁ : IsTSub T V V₁ 1)
    (hV₂ : IsTSub T V V₂ 2) (hle : V₁ ≤ V₂) {x : G} (hx : x ∈ oTwoUpper (p128 T L V)) :
    x ∈ Subgroup.centralizer (V₂ : Set G) ↔ x ∈ pCoreOf 2 (oTwoUpper (p128 T L V) ⊔ T) := by
  set K := oTwoUpper (p128 T L V) with hK
  refine ⟨fun hxC => ?_, fun hxO => pCoreOf_le_centralizer_F4 h1222 h hV₁ hV₂ hle hxO⟩
  have hKTP : K ⊔ T ≤ p128 T L V := sup_le (oTwoUpper_le _) le_p128
  have hKTN : K ⊔ T ≤ Subgroup.normalizer (V₂ : Set G) := hKTP.trans (p128_le_normalizer le_rfl hV₂)
  have hD : (K ⊔ T) ⊓ Subgroup.centralizer (V₂ : Set G) ≤ pCoreOf 2 (K ⊔ T) :=
    LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
      ((le_inf Subgroup.le_normalizer
        (hKTN.trans (normalizer_le_normalizer_centralizer'' V₂))).trans
        Subgroup.inf_normalizer_le_normalizer_inf)
      ((isPGroup_centralizer_p128_F4 h1222 h hV₁ hle).to_le (inf_le_inf_right _ hKTP))
  exact hD ⟨Subgroup.mem_sup_left hx, hxC⟩

theorem eq_conjClosure_F4 (h1222 : Stmt12_2_2_F4) {T L V : Subgroup G} {n : ℕ}
    (h : Hyp1281One G T L V n) {V₁ V₂ : Subgroup G} (hV₁ : IsTSub T V V₁ 1)
    (hV₂ : IsTSub T V V₂ 2) (hle : V₁ ≤ V₂) : V₂ = conjClosure V₁ (oTwoUpper (p128 T L V)) := by
  have hV₁2 : Nat.card V₁ = 2 := by simpa using hV₁.2.1
  have hV₂4 : Nat.card V₂ = 4 := by simpa using hV₂.2.1
  obtain ⟨a, ha, ha1, b, hb, hbV₁⟩ := exists_gens hV₁2 hV₂4
  obtain ⟨k, hk, hka, -, -⟩ := exists_rotation_mem_F4 h1222 h hV₁ hV₂ hle ha ha1 hb hbV₁
  have hKN : oTwoUpper (p128 T L V) ≤ Subgroup.normalizer (V₂ : Set G) :=
    (oTwoUpper_le _).trans (p128_le_normalizer le_rfl hV₂)
  refine le_antisymm (fun v hv => ?_) (conjClosure_le fun g hg x hx =>
    (Subgroup.mem_normalizer_iff.mp (hKN hg) x).mp (hle hx))
  have haC : a ∈ conjClosure V₁ (oTwoUpper (p128 T L V)) := le_conjClosure _ _ ha
  have hbC : b ∈ conjClosure V₁ (oTwoUpper (p128 T L V)) := by
    rw [← hka]
    exact mem_conjClosure hk ha
  rcases eq_of_mem_four hle hV₁2 hV₂4 ha ha1 hbV₁ hb hv with e | e | e | e <;> rw [e]
  · exact Subgroup.one_mem _
  · exact haC
  · exact hbC
  · exact Subgroup.mul_mem _ haC hbC

theorem almostSpecialHyp_F4 (h1222 : Stmt12_2_2_F4) (h12213 : Stmt12_2_13_F4) {T L V : Subgroup G}
    {n : ℕ} {V₁ V₂ : Subgroup G} (hs : Setting1282One G T L V n V₁ V₂) :
    AlmostSpecialHyp V₂ V₁ (oTwoUpper (p128 T L V)) T (Subgroup.normalizer (V₁ : Set G)) := by
  have hA := hs.almostSpecial_F4 h1222 h12213
  have hV₁ := hs.v1
  have hV₂ := hs.v2
  have hle := hs.le
  obtain ⟨-, hsq, hab⟩ := hs.hyp.card_sq
  have hV₁2 : Nat.card V₁ = 2 := by simpa using hV₁.2.1
  have hV₂4 : Nat.card V₂ = 4 := by simpa using hV₂.2.1
  have hKN : oTwoUpper (p128 T L V) ≤ Subgroup.normalizer (V₂ : Set G) :=
    (oTwoUpper_le _).trans (p128_le_normalizer le_rfl hV₂)
  have hL₁ : lOne (oTwoUpper (p128 T L V)) V₁ ≤
      oTwoUpper (p128 T L V) ⊓ Subgroup.normalizer (V₁ : Set G) := oTwoUpper_le _
  refine
    { elemAbelian := ⟨⟨⟨fun x y => Subtype.ext (hab _ (hV₂.1 x.2) _ (hV₂.1 y.2))⟩⟩,
        fun x hx => hsq x (hV₂.1 hx)⟩
      ne_bot := hA.ne_bot
      le_V := hle
      oTwo_eq := (oTwoUpper_oTwoUpper _).symm
      V_le_T := hV₂.1.trans hA.V_le_T
      T_le_normV₁ := hV₁.2.2
      T_le_normV := hV₂.2.2
      T_le_normL := le_p128.trans (le_normalizer_oTwoUpper _)
      sylow_LT := isSylowTwoOf_of_quasithinIsSylowTwo hs.hyp.hyp.sylow le_sup_right
      H_le := le_rfl
      lOne_sup_le := sup_le (hL₁.trans inf_le_right) hV₁.2.2
      sylow_H := isSylowTwoOf_of_quasithinIsSylowTwo hs.hyp.hyp.sylow hV₁.2.2
      charTwo := hA.charTwo
      irred := ⟨lt_of_le_of_ne hle fun he => by rw [he, hV₂4] at hV₁2; norm_num at hV₁2,
        sup_le (hL₁.trans (inf_le_left.trans hKN)) hV₂.2.2,
        sup_le (hL₁.trans inf_le_right) hV₁.2.2, fun W hW₁ hW₂ _ => ?_⟩ }
  have h1 : Nat.card W ∣ 2 ^ 2 := by
    rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← hV₂4]
    exact Subgroup.card_dvd_of_le hW₂
  have h2 : 2 ∣ Nat.card W := by
    rw [← hV₁2]
    exact Subgroup.card_dvd_of_le hW₁
  obtain ⟨j, hj, hjW⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  interval_cases j
  · rw [hjW] at h2
    norm_num at h2
  · left
    exact (Subgroup.eq_of_le_of_card_ge hW₁ (by rw [hjW, hV₁2, pow_one])).symm
  · right
    exact Subgroup.eq_of_le_of_card_ge hW₂ (by rw [hjW, hV₂4]; norm_num)

theorem isNaturalSL2Module_F4 (h1222 : Stmt12_2_2_F4) (h12213 : Stmt12_2_13_F4) {T L V : Subgroup G}
    {n : ℕ} {V₁ V₂ : Subgroup G} (hs : Setting1282One G T L V n V₁ V₂) :
    IsNaturalSL2Module 1 (oTwoUpper (p128 T L V))
      (pCoreOf 2 (oTwoUpper (p128 T L V) ⊔ T)) V₂ V₁ := by
  have hA := almostSpecialHyp_F4 h1222 h12213 hs
  have hV₁2 : Nat.card V₁ = 2 := by simpa using hs.v1.2.1
  have hV₂4 : Nat.card V₂ = 4 := by simpa using hs.v2.2.1
  obtain ⟨a, ha, ha1, b, hb, hbV₁⟩ := exists_gens hV₁2 hV₂4
  obtain ⟨k, hk, hka, -, -⟩ :=
    exists_rotation_mem_F4 h1222 hs.hyp hs.v1 hs.v2 hs.le ha ha1 hb hbV₁
  refine isNaturalSL2Module_one_of ((oTwoUpper_le _).trans (p128_le_normalizer le_rfl hs.v2))
    hA.elemAbelian hV₂4 hA.oTwo_eq
    (fun x hx => mem_centralizer_iff_mem_pCoreOf_F4 h1222 hs.hyp hs.v1 hs.v2 hs.le hx)
    (fun hKC => hbV₁ ?_) hs.le hV₁2
  have hkC := Subgroup.mem_centralizer_iff.mp (hKC hk) a (hs.le ha)
  rw [← hka, ← hkC]
  simpa using ha

theorem not_conjClosure_le_F4 (h1222 : Stmt12_2_2_F4) (h12213 : Stmt12_2_13_F4) {T L V : Subgroup G}
    {n : ℕ} {V₁ V₂ : Subgroup G} (hs : Setting1282One G T L V n V₁ V₂) :
    ¬ conjClosure V₂ (Subgroup.normalizer (V₁ : Set G)) ≤
      pCoreOf 2 (oTwoUpper (p128 T L V) ⊔ T) := by
  intro hU
  rw [← lemma12_8_8_six_F4 h1222 hs] at hU
  have hUC := hU.trans (pCoreOf_le_centralizer_F4 h1222 hs.hyp hs.v1 hs.v2 hs.le)
  have hV₂Z : V₂ ≤ V ⊓ zU128 V V₁ := fun v hv => ⟨hs.v2.1 hv, le_conjClosure V _ (hs.v2.1 hv),
    Subgroup.mem_centralizer_iff.2 fun u hu => (Subgroup.mem_centralizer_iff.1 (hUC hu) v hv).symm⟩
  rw [lemma12_8_8_three_F4 h1222 h12213 hs] at hV₂Z
  have h1 := Subgroup.card_le_of_le hV₂Z
  rw [hs.v2.2.1, hs.v1.2.1] at h1
  norm_num at h1

theorem almostSpecialL2Hyp_F4 (h1222 : Stmt12_2_2_F4) (h12213 : Stmt12_2_13_F4) {T L V : Subgroup G}
    {n : ℕ} {V₁ V₂ : Subgroup G} (hs : Setting1282One G T L V n V₁ V₂) :
    AlmostSpecialL2Hyp 1 V₂ V₁ (oTwoUpper (p128 T L V)) T
      (Subgroup.normalizer (V₁ : Set G)) where
  base := almostSpecialHyp_F4 h1222 h12213 hs
  n_pos := Nat.one_pos
  V_eq := eq_conjClosure_F4 h1222 hs.hyp hs.v1 hs.v2 hs.le
  natural := isNaturalSL2Module_F4 h1222 h12213 hs
  U_ne := not_conjClosure_le_F4 h1222 h12213 hs

end L128P

end CFSG.Quasithin.H13
