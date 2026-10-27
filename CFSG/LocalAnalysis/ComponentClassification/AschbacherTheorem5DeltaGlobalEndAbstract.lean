module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5SixGlobalInputs
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeaklyClosed
public import CFSG.FeitThompson.OddOrderTheorem

public section

open CFSG.Open
open CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding
open scoped commutatorElement

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace DeltaGlobal

variable {Y : Type} [Group Y]

structure EndSetting (Ahat E S V : Subgroup Y) {m : ℕ} (X : Fin m → Subgroup Y) : Prop where
  normal : Ahat.Normal
  sup_eq : Ahat ⊔ E = ⊤
  inf_eq : E ⊓ Ahat = ⊥
  elem : IsElemAbelian 2 E
  simple : ∀ l, IsSimpleGroup (X l)
  nonabelian : ∀ l, ∃ x ∈ X l, ∃ y ∈ X l, x * y ≠ y * x
  le : ∀ l, X l ≤ Ahat
  comm : ∀ l l', l ≠ l' → ∀ x ∈ X l, ∀ y ∈ X l', x * y = y * x
  gen : ⨆ l, X l = Ahat
  perm : ∀ e ∈ E, ∀ l, ∃ l', rightConjugate (X l) e = X l'
  sylow : IsSylowOf 2 S Ahat
  sylow_normalizer : E ≤ Subgroup.normalizer (S : Set Y)
  V_le : V ≤ S
  V_elem : IsElemAbelian 2 V
  V_closed : ∀ v ∈ V, ∀ x ∈ Ahat, x⁻¹ * v * x ∈ S → x⁻¹ * v * x ∈ V
  V_comm : ∀ e ∈ E, ∀ v ∈ V, e * v = v * e
  comm_le : ∀ e ∈ E, ∀ s ∈ S, e⁻¹ * s⁻¹ * e * s ∈ V
  wcl : ∀ x ∈ Ahat, rightConjugate E x ≤ S ⊔ E → rightConjugate E x ≤ E ⊔ V
  card_lt : Nat.card V < Nat.card E

theorem isQuasisimple_of_simple {L : Type*} [Group L] [IsSimpleGroup L]
    (hna : ∃ a b : L, a * b ≠ b * a) : IsQuasisimple L := by
  obtain ⟨a, b, hab⟩ := hna
  refine ⟨?_, ?_⟩
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator L) with hbot | htop
    · exfalso
      have hmem : ⁅a, b⁆ ∈ commutator L :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
      exact hab hmem
    · exact htop
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center L) with hbot | htop
    · exact ((QuotientGroup.quotientMulEquivOfEq hbot).trans
        QuotientGroup.quotientBot).isSimpleGroup
    · exfalso
      have hmem : a ∈ Subgroup.center L := htop ▸ Subgroup.mem_top a
      exact hab (Subgroup.mem_center_iff.mp hmem b).symm

theorem goldschmidtSimpleType_of_equiv {L L' : Type} [Group L] [Group L'] (e : L ≃* L')
    (h : goldschmidtSimpleType L') : goldschmidtSimpleType L := by
  unfold goldschmidtSimpleType at h ⊢
  rcases h with ⟨f, hf, ⟨e'⟩⟩ | ⟨n, hn, ⟨e'⟩⟩ | ⟨f, hf, ⟨e'⟩⟩ |
      ⟨p, f, hp, hodd, hf, h5, h8, ⟨e'⟩⟩ | ⟨k, hk, hcard⟩ | ⟨⟨e'⟩⟩
  · exact Or.inl ⟨f, hf, ⟨e.trans e'⟩⟩
  · exact Or.inr (Or.inl ⟨n, hn, ⟨e.trans e'⟩⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨f, hf, ⟨e.trans e'⟩⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, f, hp, hodd, hf, h5, h8, ⟨e.trans e'⟩⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨k, hk, (Nat.card_congr e.toEquiv).trans hcard⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e.trans e'⟩))))

namespace EndSetting

variable {Ahat E S V : Subgroup Y} {m : ℕ} {X : Fin m → Subgroup Y}

theorem eq_one_of_central (h : EndSetting Ahat E S V X) (l : Fin m) {z : Y} (hz : z ∈ X l)
    (hzc : ∀ x ∈ X l, z * x = x * z) : z = 1 := by
  have := h.simple l
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (X l)) with hbot | htop
  · have hmem : (⟨z, hz⟩ : X l) ∈ Subgroup.center (X l) := by
      rw [Subgroup.mem_center_iff]
      intro x
      exact Subtype.ext (hzc x x.2).symm
    rw [hbot, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  · exfalso
    obtain ⟨x, hx, y, hy, hxy⟩ := h.nonabelian l
    have hmem : (⟨x, hx⟩ : X l) ∈ Subgroup.center (X l) := htop ▸ Subgroup.mem_top _
    rw [Subgroup.mem_center_iff] at hmem
    exact hxy (congrArg Subtype.val (hmem ⟨y, hy⟩)).symm

theorem le_normalizer (h : EndSetting Ahat E S V X) (l : Fin m) :
    Ahat ≤ Subgroup.normalizer (X l : Set Y) := by
  rw [← h.gen]
  refine iSup_le fun l' => ?_
  by_cases hl : l' = l
  · subst hl
    exact Subgroup.le_normalizer
  · refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (h.comm l' l hl x hx y hy).symm

theorem inf_eq_bot (h : EndSetting Ahat E S V X) {l l' : Fin m} (hl : l ≠ l') :
    X l ⊓ X l' = ⊥ := by
  rw [eq_bot_iff]
  rintro z ⟨hz, hz'⟩
  rw [Subgroup.mem_bot]
  exact h.eq_one_of_central l hz fun x hx => (h.comm l' l (Ne.symm hl) z hz' x hx)

theorem even_card (h : EndSetting Ahat E S V X) [Finite Y] (l : Fin m) :
    Even (Nat.card (X l)) := by
  have := h.simple l
  by_contra hodd
  have hsolv := CFSG.FeitThompson.isSolvable_of_odd_natCard (G := X l) (Nat.not_even_iff_odd.mp hodd)
  obtain ⟨x, hx, y, hy, hxy⟩ := h.nonabelian l
  exact hxy (congrArg Subtype.val
    (IsSimpleGroup.comm_iff_isSolvable.mpr hsolv ⟨x, hx⟩ ⟨y, hy⟩))

theorem isSylowOf_inf (h : EndSetting Ahat E S V X) [Finite Y] (l : Fin m) :
    IsSylowOf 2 (S ⊓ X l) (X l) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact h.sylow.inf_of_le_normalizer (h.le l) (h.le_normalizer l)

theorem inf_ne_bot (h : EndSetting Ahat E S V X) [Finite Y] (l : Fin m) : S ⊓ X l ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hbot
  obtain ⟨-, -, hdvd⟩ := isSylowOf_iff.mp (h.isSylowOf_inf l)
  apply hdvd
  rw [hbot, Subgroup.relIndex_bot_left]
  exact even_iff_two_dvd.mp (h.even_card l)

theorem le_or_inf_eq_bot (h : EndSetting Ahat E S V X) (l : Fin m) {M : Subgroup Y}
    (hM : M.Normal) : X l ≤ M ∨ X l ⊓ M = ⊥ := by
  have := h.simple l
  have : (M.subgroupOf (X l)).Normal := Subgroup.normal_subgroupOf
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (M.subgroupOf (X l)) with hbot | htop
  · right
    rw [eq_bot_iff]
    rintro z ⟨hz, hzM⟩
    have hmem : (⟨z, hz⟩ : X l) ∈ M.subgroupOf (X l) := hzM
    rw [hbot, Subgroup.mem_bot] at hmem
    exact (Subgroup.mem_bot).mpr (congrArg Subtype.val hmem)
  · left
    exact Subgroup.subgroupOf_eq_top.mp htop

theorem le_normalizer_of_centralizes (h : EndSetting Ahat E S V X) (l : Fin m)
    {R : Subgroup Y} (hR : R ≤ X l) (hR1 : R ≠ ⊥) (hER : ∀ e ∈ E, ∀ x ∈ R, e * x = x * e) :
    E ≤ Subgroup.normalizer (X l : Set Y) := by
  intro e he
  obtain ⟨l', hl'⟩ := h.perm e he l
  by_cases hll : l' = l
  · rw [← rightConjugate_eq_self_iff, hl', hll]
  · exfalso
    apply hR1
    rw [eq_bot_iff, ← (h.inf_eq_bot (Ne.symm hll) : X l ⊓ X l' = ⊥)]
    intro x hx
    have hx' : x ∈ X l' := by
      rw [← hl', mem_rightConjugate_iff]
      have hc := hER e he x hx
      have : e * x * e⁻¹ = x := by rw [hc]; group
      rw [this]
      exact hR hx
    exact ⟨hR hx, hx'⟩

theorem le_normalizer_of_inf_eq_bot (h : EndSetting Ahat E S V X) [Finite Y] (l : Fin m)
    {M : Subgroup Y} (hM : M.Normal) (hVM : V ≤ M) (hXM : X l ⊓ M = ⊥) :
    E ≤ Subgroup.normalizer (X l : Set Y) := by
  intro e he
  obtain ⟨l', hl'⟩ := h.perm e he l
  by_cases hll : l' = l
  · rw [← rightConjugate_eq_self_iff, hl', hll]
  · exfalso
    apply h.inf_ne_bot l
    rw [eq_bot_iff]
    rintro s ⟨hsS, hsX⟩
    rw [Subgroup.mem_bot]
    refine h.eq_one_of_central l hsX fun y hy => ?_
    set a := e⁻¹ * s⁻¹ * e with ha
    have haX : a ∈ X l' := by
      rw [← hl', mem_rightConjugate_iff, ha]
      have : e * (e⁻¹ * s⁻¹ * e) * e⁻¹ = s⁻¹ := by group
      rw [this]
      exact (X l).inv_mem hsX
    have hcM : a * s ∈ M := hVM (h.comm_le e he s hsS)
    have hsy : s * y * s⁻¹ ∈ X l :=
      (X l).mul_mem ((X l).mul_mem hsX hy) ((X l).inv_mem hsX)
    have hcomm : a * (s * y * s⁻¹) = (s * y * s⁻¹) * a :=
      h.comm l' l hll a haX _ hsy
    have hkey : (a * s) * y * (a * s)⁻¹ * y⁻¹ = s * y * s⁻¹ * y⁻¹ := by
      calc (a * s) * y * (a * s)⁻¹ * y⁻¹ = (a * (s * y * s⁻¹)) * a⁻¹ * y⁻¹ := by group
        _ = ((s * y * s⁻¹) * a) * a⁻¹ * y⁻¹ := by rw [hcomm]
        _ = s * y * s⁻¹ * y⁻¹ := by group
    have hmemM : (a * s) * y * (a * s)⁻¹ * y⁻¹ ∈ M := by
      have h1 : y * (a * s)⁻¹ * y⁻¹ ∈ M := hM.conj_mem _ (M.inv_mem hcM) y
      have : (a * s) * y * (a * s)⁻¹ * y⁻¹ = (a * s) * (y * (a * s)⁻¹ * y⁻¹) := by group
      rw [this]
      exact M.mul_mem hcM h1
    rw [hkey] at hmemM
    have hmemX : s * y * s⁻¹ * y⁻¹ ∈ X l := (X l).mul_mem hsy ((X l).inv_mem hy)
    have h1 : s * y * s⁻¹ * y⁻¹ ∈ X l ⊓ M := ⟨hmemX, hmemM⟩
    rw [hXM, Subgroup.mem_bot] at h1
    calc s * y = (s * y * s⁻¹ * y⁻¹) * (y * s) := by group
      _ = y * s := by rw [h1, one_mul]


omit [Group Y] in
theorem exists_involution {Y : Type} [Group Y] [Finite Y] {P : Subgroup Y} (hP : IsPGroup 2 P)
    (hP1 : P ≠ ⊥) : ∃ x ∈ P, orderOf x = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    exact hP1 (Subgroup.eq_bot_of_card_eq P hn)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 (hn ▸ dvd_pow_self 2 hn0)
  exact ⟨x, x.2, by rw [Subgroup.orderOf_coe, hx]⟩

theorem isPGroup_E (h : EndSetting Ahat E S V X) : IsPGroup 2 E := fun x =>
  ⟨1, Subtype.ext (by simpa using h.elem.2 x x.2)⟩

omit [Group Y] in
theorem le_normalizer_inf {Y : Type} [Group Y] {R P Q : Subgroup Y}
    (hP : R ≤ Subgroup.normalizer (P : Set Y)) (hQ : R ≤ Subgroup.normalizer (Q : Set Y)) :
    R ≤ Subgroup.normalizer ((P ⊓ Q : Subgroup Y) : Set Y) := by
  intro e he
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_normalizer_iff.mp (hP he) x,
    Subgroup.mem_normalizer_iff.mp (hQ he) x]

theorem oddCore_eq_bot (h : EndSetting Ahat E S V X) [Finite Y] (l : Fin m) :
    CFSG.oddCore (X l) = ⊥ := by
  have := h.simple l
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.oddCore (X l)) with hbot | htop
  · exact hbot
  · exfalso
    have hodd := AschbacherTheorem3.odd_card_oddCore (X l)
    rw [htop, Subgroup.card_top] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) (h.even_card l)

theorem centralizes_of_inf_eq_bot (h : EndSetting Ahat E S V X) [Finite Y] (l : Fin m)
    {M : Subgroup Y} (hM : M.Normal) (hVM : V ≤ M) (hXM : X l ⊓ M = ⊥) :
    ∀ e ∈ E, ∀ x ∈ X l, e * x = x * e := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := S ⊓ X l with hPdef
  have hEN : E ≤ Subgroup.normalizer (X l : Set Y) :=
    h.le_normalizer_of_inf_eq_bot l hM hVM hXM
  have hEP : E ≤ Subgroup.normalizer (P : Set Y) := le_normalizer_inf h.sylow_normalizer hEN
  have hEX : E ⊓ X l = ⊥ := le_bot_iff.mp (h.inf_eq ▸ inf_le_inf_left E (h.le l))
  have hF : AschbacherTheorem3.Frame (X l) E := ⟨hEN, hEX, h.isPGroup_E⟩
  have hsyl := AschbacherTheorem3.isSylowOf_sup_of_frame hF (h.isSylowOf_inf l) hEP
  have hSA : S ≤ Ahat := h.sylow.le
  have hEV : E ≤ Subgroup.normalizer (V : Set Y) := by
    intro e he
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (h.V_comm e he v hv).symm
  have hclosed : ∀ x ∈ X l, rightConjugate E x ≤ E ⊔ P → rightConjugate E x = E := by
    intro x hx hle
    have hle' : rightConjugate E x ≤ S ⊔ E :=
      hle.trans (sup_le le_sup_right (inf_le_left.trans le_sup_left))
    have hwc := h.wcl x (h.le l hx) hle'
    apply Subgroup.eq_of_le_of_card_ge _ (by rw [rightConjugate_card])
    intro y hy
    have hy1 : y ∈ ((E ⊔ V : Subgroup Y) : Set Y) := hwc hy
    have hy2 : y ∈ ((E ⊔ P : Subgroup Y) : Set Y) := hle hy
    rw [Subgroup.coe_mul_of_left_le_normalizer_right E V hEV] at hy1
    rw [Subgroup.coe_mul_of_left_le_normalizer_right E P hEP] at hy2
    obtain ⟨e₁, he₁, v, hv, rfl⟩ := Set.mem_mul.mp hy1
    obtain ⟨e₂, he₂, p, hp, hep⟩ := Set.mem_mul.mp hy2
    have hpX : p ∈ X l := hp.2
    have hmemE : e₂⁻¹ * e₁ ∈ E := E.mul_mem (E.inv_mem he₂) he₁
    have heq : e₂⁻¹ * e₁ = p * v⁻¹ := by
      calc e₂⁻¹ * e₁ = e₂⁻¹ * (e₁ * v) * v⁻¹ := by group
        _ = e₂⁻¹ * (e₂ * p) * v⁻¹ := by rw [hep]
        _ = p * v⁻¹ := by group
    have hmemA : p * v⁻¹ ∈ Ahat := Ahat.mul_mem (h.le l hpX) (Ahat.inv_mem (hSA (h.V_le hv)))
    have h1 : e₂⁻¹ * e₁ ∈ E ⊓ Ahat := ⟨hmemE, heq ▸ hmemA⟩
    rw [h.inf_eq, Subgroup.mem_bot] at h1
    have hpv : p = v := by
      have : p * v⁻¹ = 1 := heq ▸ h1
      calc p = p * v⁻¹ * v := by group
        _ = v := by rw [this, one_mul]
    have hv1 : v ∈ X l ⊓ M := ⟨hpv ▸ hpX, hVM hv⟩
    rw [hXM, Subgroup.mem_bot] at hv1
    rw [hv1, mul_one]
    exact he₁
  have hH42 : AschbacherTheorem3.Hyp42 (X l) E (E ⊔ P) := ⟨hF, hsyl, le_sup_left, hclosed⟩
  have hcomm := AschbacherTheorem3.lemma_4_2_oddCore hH42
  rw [h.oddCore_eq_bot l, Subgroup.map_bot, le_bot_iff] at hcomm
  intro e he x hx
  have hmem := Subgroup.commutator_mem_commutator hx he
  rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
  exact hmem.symm


theorem exists_centralizing_of_type (hin : SectionSixGlobalInputs)
    (h : EndSetting Ahat E S V X) [Finite Y] (l : Fin m)
    (htype : goldschmidtSimpleType (X l ⧸ Subgroup.center (X l)))
    (hΩ : AschbacherTheorem3.omegaOne (S ⊓ X l) ≤ V) :
    ∃ e ∈ E, e ≠ 1 ∧ ∀ x ∈ X l, e * x = x * e := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := S ⊓ X l with hPdef
  have hP2 : IsPGroup 2 P := (h.isSylowOf_inf l).isPGroup
  obtain ⟨t, htP, ht2⟩ := exists_involution hP2 (h.inf_ne_bot l)
  have htΩ : t ∈ AschbacherTheorem3.omegaOne P :=
    Subgroup.subset_closure ⟨htP, by rw [← ht2, pow_orderOf_eq_one]⟩
  have hΩ1 : AschbacherTheorem3.omegaOne P ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.mem_bot] at htΩ
    rw [htΩ, orderOf_one] at ht2
    exact absurd ht2 (by norm_num)
  have hEΩ : ∀ e ∈ E, ∀ x ∈ AschbacherTheorem3.omegaOne P, e * x = x * e :=
    fun e he x hx => h.V_comm e he x (hΩ hx)
  have hEN : E ≤ Subgroup.normalizer (X l : Set Y) :=
    h.le_normalizer_of_centralizes l ((AschbacherTheorem3.omegaOne_le P).trans inf_le_right)
      hΩ1 hEΩ
  have hEP : E ≤ Subgroup.normalizer (P : Set Y) := le_normalizer_inf h.sylow_normalizer hEN
  have hcomm : ∀ e ∈ E, ∀ p ∈ P, e⁻¹ * p⁻¹ * e * p ∈ AschbacherTheorem3.omegaOne P := by
    intro e he p hp
    have hV := h.comm_le e he p hp.1
    have hc : e⁻¹ * p⁻¹ * e ∈ P := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hEP he)) p⁻¹).mp
        (P.inv_mem hp)
      simpa using h1
    refine Subgroup.subset_closure ⟨P.mul_mem hc hp, ?_⟩
    exact h.V_elem.2 _ hV
  have hbound := hin.goldschmidt_type_automorphisms Y (X l) P E (h.simple l) htype
    (h.isSylowOf_inf l) h.elem hEN hEP hEΩ hcomm
  have hcardΩ : Nat.card (AschbacherTheorem3.omegaOne P) ≤ Nat.card V :=
    Subgroup.card_le_of_le hΩ
  have hC1 : 1 < Nat.card (E ⊓ Subgroup.centralizer (X l : Set Y) : Subgroup Y) := by
    by_contra hle
    push Not at hle
    have h1 : Nat.card E ≤ Nat.card V := by
      calc Nat.card E ≤ _ := hbound
        _ ≤ Nat.card V * 1 := Nat.mul_le_mul hcardΩ hle
        _ = Nat.card V := mul_one _
    exact absurd h.card_lt (not_lt.mpr h1)
  have hne : (E ⊓ Subgroup.centralizer (X l : Set Y) : Subgroup Y) ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hC1
    exact lt_irrefl _ hC1
  obtain ⟨⟨e, heE, heC⟩, he1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  refine ⟨e, heE, fun he => he1 (Subtype.ext he), fun x hx => ?_⟩
  exact (Subgroup.mem_centralizer_iff.mp heC x hx).symm


theorem isSylowOf_top (h : EndSetting Ahat E S V X) [Finite Y] :
    IsSylowOf 2 (E ⊔ S) ⊤ := by
  have hEA : E ≤ Subgroup.normalizer (Ahat : Set Y) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr h.normal]
    exact le_top
  have hF : AschbacherTheorem3.Frame Ahat E := ⟨hEA, h.inf_eq, h.isPGroup_E⟩
  have hsyl := AschbacherTheorem3.isSylowOf_sup_of_frame hF h.sylow h.sylow_normalizer
  rwa [h.sup_eq] at hsyl

theorem stronglyClosed (h : EndSetting Ahat E S V X) :
    ∀ a ∈ V, ∀ g : Y, g⁻¹ * a * g ∈ E ⊔ S → g⁻¹ * a * g ∈ V := by
  have hEA : E ≤ Subgroup.normalizer (Ahat : Set Y) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr h.normal]
    exact le_top
  intro a ha g hg
  have hgmem : g ∈ ((E ⊔ Ahat : Subgroup Y) : Set Y) := by
    rw [sup_comm, h.sup_eq]
    exact Subgroup.mem_top g
  rw [Subgroup.coe_mul_of_left_le_normalizer_right E Ahat hEA] at hgmem
  obtain ⟨e, he, x, hx, rfl⟩ := Set.mem_mul.mp hgmem
  have hea : e⁻¹ * a * e = a := by
    have := h.V_comm e he a ha
    calc e⁻¹ * a * e = e⁻¹ * (a * e) := by group
      _ = e⁻¹ * (e * a) := by rw [this]
      _ = a := by group
  have heq : (e * x)⁻¹ * a * (e * x) = x⁻¹ * a * x := by
    calc (e * x)⁻¹ * a * (e * x) = x⁻¹ * (e⁻¹ * a * e) * x := by group
      _ = x⁻¹ * a * x := by rw [hea]
  rw [heq] at hg ⊢
  apply h.V_closed a ha x hx
  have hmemA : x⁻¹ * a * x ∈ Ahat :=
    Ahat.mul_mem (Ahat.mul_mem (Ahat.inv_mem hx) (h.sylow.le (h.V_le ha))) hx
  have hg' : x⁻¹ * a * x ∈ ((E ⊔ S : Subgroup Y) : Set Y) := hg
  rw [Subgroup.coe_mul_of_left_le_normalizer_right E S h.sylow_normalizer] at hg'
  obtain ⟨e', he', s, hs, hes⟩ := Set.mem_mul.mp hg'
  have he'A : e' ∈ Ahat := by
    have : e' = (x⁻¹ * a * x) * s⁻¹ := by rw [← hes]; group
    rw [this]
    exact Ahat.mul_mem hmemA (Ahat.inv_mem (h.sylow.le hs))
  have h1 : e' ∈ E ⊓ Ahat := ⟨he', he'A⟩
  rw [h.inf_eq, Subgroup.mem_bot] at h1
  rw [← hes, h1, one_mul]
  exact hs

theorem goldschmidt_component (hgold : CFSG.Goldschmidt.TopStatement)
    (h : EndSetting Ahat E S V X) [Finite Y] (l : Fin m)
    (hXM : X l ≤ Subgroup.normalClosure (V : Set Y)) :
    goldschmidtSimpleType (X l ⧸ Subgroup.center (X l)) ∧
      AschbacherTheorem3.omegaOne (S ⊓ X l) ≤ V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hES2, hidx⟩ := isSylowOf_iff.mp h.isSylowOf_top
  rw [Subgroup.relIndex_top_right] at hidx
  set SY : Sylow 2 Y := hES2.toSylow hidx with hSYdef
  have hSYc : (SY : Subgroup Y) = E ⊔ S := IsPGroup.toSylow_coe hES2 hidx
  have hVSY : V ≤ (SY : Subgroup Y) := hSYc ▸ (h.V_le.trans le_sup_right)
  have hcl : ∀ a ∈ V, ∀ g : Y, g⁻¹ * a * g ∈ (SY : Subgroup Y) → g⁻¹ * a * g ∈ V := by
    intro a ha g hg
    rw [hSYc] at hg
    exact h.stronglyClosed a ha g hg
  have hG := CFSG.Goldschmidt.milestone_of_topStatement hgold Y SY V hVSY h.V_elem.1 hcl
  dsimp only at hG
  obtain ⟨-, hVeq, hcomp⟩ := hG
  set M := Subgroup.normalClosure (V : Set Y) with hMdef
  set O := goldschmidtOddCore M with hOdef
  have hOodd : Odd (Nat.card O) := by
    have hO : O = CFSG.oddCore M := rfl
    rw [hO]
    exact AschbacherTheorem3.odd_card_oddCore M
  have hMA : M ≤ Ahat := by
    have := h.normal
    exact Subgroup.normalClosure_le_normal fun v hv => h.sylow.le (h.V_le hv)
  have hMN : M ≤ Subgroup.normalizer (X l : Set Y) := hMA.trans (h.le_normalizer l)
  have hXO : ∀ x ∈ X l, x ∈ O.map M.subtype → x = 1 := by
    have := h.simple l
    set N : Subgroup (X l) := (O.map M.subtype).subgroupOf (X l) with hNdef
    have hNn : N.Normal := by
      constructor
      intro n hn g
      rw [hNdef, Subgroup.mem_subgroupOf] at hn ⊢
      obtain ⟨o, ho, hon⟩ := Subgroup.mem_map.mp hn
      have hgM : (g : Y) ∈ M := hXM g.2
      refine Subgroup.mem_map.mpr ⟨⟨g, hgM⟩ * o * ⟨g, hgM⟩⁻¹,
        (inferInstance : O.Normal).conj_mem o ho _, ?_⟩
      simpa using hon
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hbot | htop
    · intro x hx hxO
      have hxN : (⟨x, hx⟩ : X l) ∈ N := hxO
      rw [hbot, Subgroup.mem_bot] at hxN
      exact congrArg Subtype.val hxN
    · exfalso
      have hle : X l ≤ O.map M.subtype := fun x hx => by
        have : (⟨x, hx⟩ : X l) ∈ N := htop ▸ Subgroup.mem_top _
        exact this
      have hdvd := Subgroup.card_dvd_of_le hle
      rw [Subgroup.card_map_of_injective M.subtype_injective] at hdvd
      exact (Nat.not_even_iff_odd.mpr (hOodd.of_dvd_nat hdvd)) (h.even_card l)
  set π := QuotientGroup.mk' O with hπdef
  set K : Subgroup (M ⧸ O) := ((X l).subgroupOf M).map π with hKdef
  have hmemK : ∀ x : X l, π ⟨x, hXM x.2⟩ ∈ K := fun x =>
    Subgroup.mem_map.mpr ⟨⟨x, hXM x.2⟩, Subgroup.mem_subgroupOf.mpr x.2, rfl⟩
  set f : X l →* K :=
    (π.comp (Subgroup.inclusion hXM)).codRestrict K (fun x => hmemK x) with hfdef
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : π ⟨x, hXM x.2⟩ = 1 := congrArg Subtype.val hx
    rw [hπdef, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact Subtype.ext (hXO x x.2 (Subgroup.mem_map.mpr ⟨_, h1, rfl⟩))
  have hfsurj : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
    refine ⟨⟨z, Subgroup.mem_subgroupOf.mp hz⟩, Subtype.ext ?_⟩
    rfl
  set e : X l ≃* K := MulEquiv.ofBijective f ⟨hfinj, hfsurj⟩ with hedef
  have hXn : ((X l).subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXM).mpr hMN
  have hKn : K.Normal := hXn.map π (QuotientGroup.mk'_surjective O)
  have hKs : IsSimpleGroup K := by
    have := h.simple l
    exact e.symm.isSimpleGroup
  have hKq : IsQuasisimple K := by
    obtain ⟨x, hx, y, hy, hxy⟩ := h.nonabelian l
    refine isQuasisimple_of_simple ⟨e ⟨x, hx⟩, e ⟨y, hy⟩, fun heq => hxy ?_⟩
    rw [← map_mul, ← map_mul] at heq
    exact congrArg Subtype.val (e.injective heq)
  have hKc : IsComponentOf K ⊤ := by
    refine ⟨le_top, ?_, hKq⟩
    exact IsSubnormal.step le_top Subgroup.normal_subgroupOf (IsSubnormal.refl ⊤)
  refine ⟨?_, ?_⟩
  ·
    have htype := hcomp K hKc
    refine goldschmidtSimpleType_of_equiv ?_ htype
    exact QuotientGroup.congr (Subgroup.center (X l)) (Subgroup.center K) e
      (Subgroup.map_center_eq e)
  ·
    rw [AschbacherTheorem3.omegaOne, Subgroup.closure_le]
    rintro x ⟨⟨hxS, hxX⟩, hx2⟩
    set x' : M := ⟨x, hXM hxX⟩ with hx'def
    have hlayer : π x' ∈ goldschmidtLayer (M ⧸ O) :=
      (le_sSup hKc : K ≤ goldschmidtLayer (M ⧸ O)) (hmemK ⟨x, hxX⟩)
    have hT : π x' ∈ ((SY : Subgroup Y).subgroupOf M).map π ⊓ goldschmidtLayer (M ⧸ O) := by
      refine ⟨Subgroup.mem_map.mpr ⟨x', ?_, rfl⟩, hlayer⟩
      rw [Subgroup.mem_subgroupOf, hSYc]
      exact Subgroup.mem_sup_right hxS
    have hx'2 : (π x') ^ 2 = 1 := by
      rw [← map_pow]
      have : x' ^ 2 = 1 := Subtype.ext (by simpa using hx2)
      rw [this, map_one]
    have hmemV : π x' ∈ (V.subgroupOf M).map π := by
      rw [hVeq]
      exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨hT, hx'2⟩)
    obtain ⟨v', hv', hvx⟩ := Subgroup.mem_map.mp hmemV
    have hO' : v'⁻¹ * x' ∈ O := by
      rw [hπdef, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hvx
      exact hvx
    have hvS : (v' : Y) ∈ S := h.V_le (Subgroup.mem_subgroupOf.mp hv')
    have hwS : (v' : Y)⁻¹ * x ∈ S := S.mul_mem (S.inv_mem hvS) hxS
    obtain ⟨k, hk⟩ := h.sylow.isPGroup ⟨_, hwS⟩
    have hk' : ((v' : Y)⁻¹ * x) ^ (2 ^ k) = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hord : orderOf (⟨v'⁻¹ * x', hO'⟩ : O) = 1 := by
      have hdvd1 : orderOf (⟨v'⁻¹ * x', hO'⟩ : O) ∣ Nat.card O := orderOf_dvd_natCard _
      have hdvd2 : orderOf (⟨v'⁻¹ * x', hO'⟩ : O) ∣ 2 ^ k := by
        apply orderOf_dvd_of_pow_eq_one
        apply Subtype.ext
        apply Subtype.ext
        simpa using hk'
      have hcop : Nat.Coprime (Nat.card O) (2 ^ k) :=
        Nat.Coprime.pow_right k hOodd.coprime_two_right
      exact Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hdvd1 hcop) hdvd2
    have hw1 : (v' : Y)⁻¹ * x = 1 := by
      have h1 := orderOf_eq_one_iff.mp hord
      have h2 := congrArg (fun z : O => ((z : M) : Y)) h1
      simpa using h2
    have hxv : x = v' := by
      calc x = (v' : Y) * ((v' : Y)⁻¹ * x) := by group
        _ = v' := by rw [hw1, mul_one]
    rw [hxv]
    exact Subgroup.mem_subgroupOf.mp hv'


theorem exists_centralizing (hin : SectionSixGlobalInputs) (h : EndSetting Ahat E S V X)
    [Finite Y] (l : Fin m) : ∃ e ∈ E, e ≠ 1 ∧ ∀ x ∈ X l, e * x = x * e := by
  set M := Subgroup.normalClosure (V : Set Y) with hMdef
  have hMn : M.Normal := Subgroup.normalClosure_normal
  have hVM : V ≤ M := Subgroup.le_normalClosure
  rcases h.le_or_inf_eq_bot l hMn with hXM | hXM
  · obtain ⟨htype, hΩ⟩ := h.goldschmidt_component hin.goldschmidt l hXM
    exact h.exists_centralizing_of_type hin l htype hΩ
  · have hE1 : E ≠ ⊥ := by
      intro hb
      have := h.card_lt
      rw [hb, Subgroup.card_bot] at this
      exact Nat.not_lt_zero _ (Nat.lt_one_iff.mp this ▸ Nat.card_pos (α := V))
    obtain ⟨⟨e, he⟩, he1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hE1
    exact ⟨e, he, fun h1 => he1 (Subtype.ext h1), h.centralizes_of_inf_eq_bot l hMn hVM hXM e he⟩

end EndSetting

end DeltaGlobal

end CFSG.ComponentClassification.AschbacherTheorem5
