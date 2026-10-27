module

public import CFSG.CGT.Timmesfeld75.Sec3TenCaseB8
public import CFSG.CGT.Timmesfeld75.Sec3TenExcPart

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open DihedralGroup
open scoped commutatorElement

variable {G : Type} [Group G] {T T₁ S : Subgroup G} {a : G}

section MkEq

variable [hN : ((cfgM T T₁).subgroupOf (T ⊔ T₁)).Normal]

set_option quotPrecheck false in
local notation "XQ" => ↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁)

omit hN in
theorem mk_eq_iff {x y : G} (hx : x ∈ T ⊔ T₁) (hy : y ∈ T ⊔ T₁) :
    (QuotientGroup.mk ⟨x, hx⟩ : XQ) = QuotientGroup.mk ⟨y, hy⟩ ↔ x⁻¹ * y ∈ cfgM T T₁ := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  rfl

end MkEq

namespace SecB6

variable (h : SecB6 T T₁ S a)

include h

theorem comm_conj_normIn [Finite G] {x f : G} (hx : x ∈ cfgM T T₁)
    (hf : f ∈ conjSubgroup a (normIn T₁ T)) : x * f = f * x := by
  obtain ⟨l, hl, y, hy, rfl⟩ := h.sec.cfg.mem_cfgM_iff.1 hx
  have hfy : y * f = f * y := h.hcomm y hy f hf
  have hlf : l * f = f * l := by
    obtain ⟨f₀, hf₀, rfl⟩ := mem_conjSubgroup_iff_exists.1 hf
    have hl' : a⁻¹ * l * a ∈ normIn T T₁ := by
      have := conj_mem_of_mem_normalizer ((Subgroup.normalizer _).inv_mem h.haNL) hl
      simpa using this
    have h1 : (a⁻¹ * l * a) * f₀ = f₀ * (a⁻¹ * l * a) := h.sec.cfg.comm_L_L₁ hl' hf₀
    calc l * (a * f₀ * a⁻¹) = a * ((a⁻¹ * l * a) * f₀) * a⁻¹ := by group
      _ = a * (f₀ * (a⁻¹ * l * a)) * a⁻¹ := by rw [h1]
      _ = (a * f₀ * a⁻¹) * l := by group
  calc l * y * f = l * (y * f) := by group
    _ = l * (f * y) := by rw [hfy]
    _ = (l * f) * y := by group
    _ = (f * l) * y := by rw [hlf]
    _ = f * (l * y) := by group

section Quotient

variable [hN : ((cfgM T T₁).subgroupOf (T ⊔ T₁)).Normal]

set_option quotPrecheck false in
local notation "XQ" => ↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁)

theorem conj_le_cfgM [Finite G] {n : ℕ} (hn : Odd n) (hn3 : 3 < n) (e : XQ ≃* DihedralGroup n)
    (hL4 : Nat.card (normIn T T₁) = 4) : conjSubgroup a (normIn T₁ T) ≤ cfgM T T₁ := by
  have hS := h.sec
  have hTab := hS.cfg.wc.1
  have hMab := hS.cfg.isElemAbelian_cfgM
  have haT : conjSubgroup a T = T := mem_normalizer_iff_conjSubgroup_eq.1 h.haN
  obtain ⟨-, hpart⟩ := hS.eq_five_and_exists_conj_of_card_four hn hn3 e hL4
  obtain ⟨x₀, -, hx₀⟩ := hS.conj
  obtain ⟨T', hT'⟩ : ∃ T' : Subgroup G, T' = conjSubgroup a T₁ := ⟨_, rfl⟩
  obtain ⟨L', hL'⟩ : ∃ L' : Subgroup G, L' = conjSubgroup a (normIn T₁ T) := ⟨_, rfl⟩
  have hT'wc : IsWC T' := by rw [hT']; exact hS.cfg.wc₁.conj a
  have hT'k : T' = conjSubgroup (a * x₀) T := by
    rw [hT', hx₀, conjSubgroup_conjSubgroup]
  have hL'eq : normIn T' T = L' := by
    have := normIn_conj a T₁ T
    rw [haT] at this
    rw [hT', hL', this]
  have hL'T' : L' ≤ T' := by
    rw [hL', hT']
    exact conjSubgroup_mono (normIn_le T₁ T)
  have hL'ab : IsElemAbelian 2 L' := isElemAbelian_of_le (hT'k ▸ isElemAbelian_conjSubgroup hTab _)
    hL'T'
  have hcardT' : Nat.card T' = Nat.card L' * 2 := by
    rw [hT', hL', card_conjSubgroup, card_conjSubgroup]
    exact h.card_T₁
  have hcardL' : Nat.card L' = 4 := by
    rw [hL', card_conjSubgroup, hS.card_normIn_swap]
    exact hL4
  have hMc : ∀ m ∈ cfgM T T₁, ∀ f ∈ L', m * f = f * m := fun m hm f hf =>
    h.comm_conj_normIn hm (hL' ▸ hf)
  have hL'ne : L' ≠ ⊥ := by
    rw [hL']
    exact fun h0 => hS.cfg.ne₁ (conjSubgroup_eq_bot_iff.1 h0)
  obtain ⟨⟨f, hfL'⟩, hf1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hL'ne
  have hf1' : f ≠ 1 := fun h1 => hf1 (Subtype.ext h1)
  have hMN : ∀ m ∈ cfgM T T₁, m ∈ Subgroup.normalizer (T' : Set G) := fun m hm =>
    hT'wc.centralizer_le_normalizer (hL'T' hfL') hf1'
      (Subgroup.mem_centralizer_singleton_iff.2 (hMc m hm f hfL'))
  obtain ⟨t₀, ht₀T', ht₀L'⟩ : ∃ t₀ ∈ T', t₀ ∉ L' := by
    by_contra hcon
    push Not at hcon
    have h1 : Nat.card T' ≤ Nat.card L' := Subgroup.card_le_of_le hcon
    have h2 : 0 < Nat.card L' := Nat.card_pos
    omega
  have hδmem : ∀ m ∈ cfgM T T₁, m * t₀ * m⁻¹ * t₀⁻¹ ∈ L' := by
    intro m hm
    have hv : m * t₀ * m⁻¹ ∈ T' := (Subgroup.mem_normalizer_iff.1 (hMN m hm) t₀).1 ht₀T'
    have hvL' : m * t₀ * m⁻¹ ∉ L' := by
      intro hv'
      apply ht₀L'
      have hc := hMc m hm _ hv'
      have e1 : t₀ = m⁻¹ * (m * t₀ * m⁻¹) * m := by group
      rw [e1]
      have e2 : m⁻¹ * (m * t₀ * m⁻¹) * m = m * t₀ * m⁻¹ := by
        calc m⁻¹ * (m * t₀ * m⁻¹) * m = m⁻¹ * ((m * t₀ * m⁻¹) * m) := by group
          _ = m⁻¹ * (m * (m * t₀ * m⁻¹)) := by rw [← hc]
          _ = m * t₀ * m⁻¹ := by group
      rw [e2]
      exact hv'
    exact mul_mem_of_not_mem_of_card hL'T' hcardT' hv (T'.inv_mem ht₀T') hvL'
      (fun h' => ht₀L' (L'.inv_mem_iff.1 h'))
  let δ : ↥(cfgM T T₁) →* ↥L' :=
    { toFun := fun m => ⟨(m : G) * t₀ * (m : G)⁻¹ * t₀⁻¹, hδmem m m.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro m m'
        apply Subtype.ext
        have hd' := hδmem m' m'.2
        have hcomm : (m : G) * ((m' : G) * t₀ * (m' : G)⁻¹ * t₀⁻¹) =
            ((m' : G) * t₀ * (m' : G)⁻¹ * t₀⁻¹) * (m : G) := hMc m m.2 _ hd'
        have hdd : ((m : G) * t₀ * (m : G)⁻¹ * t₀⁻¹) * ((m' : G) * t₀ * (m' : G)⁻¹ * t₀⁻¹) =
            ((m' : G) * t₀ * (m' : G)⁻¹ * t₀⁻¹) * ((m : G) * t₀ * (m : G)⁻¹ * t₀⁻¹) :=
          elemAbelian_mul_comm hL'ab (hδmem m m.2) hd'
        show ((m : G) * (m' : G)) * t₀ * ((m : G) * (m' : G))⁻¹ * t₀⁻¹ =
          ((m : G) * t₀ * (m : G)⁻¹ * t₀⁻¹) * ((m' : G) * t₀ * (m' : G)⁻¹ * t₀⁻¹)
        rw [hdd]
        calc ((m : G) * (m' : G)) * t₀ * ((m : G) * (m' : G))⁻¹ * t₀⁻¹
            = ((m : G) * ((m' : G) * t₀ * (m' : G)⁻¹ * t₀⁻¹) * (m : G)⁻¹) *
              ((m : G) * t₀ * (m : G)⁻¹ * t₀⁻¹) := by group
          _ = ((m' : G) * t₀ * (m' : G)⁻¹ * t₀⁻¹) * ((m : G) * t₀ * (m : G)⁻¹ * t₀⁻¹) := by
            rw [show (m : G) * ((m' : G) * t₀ * (m' : G)⁻¹ * t₀⁻¹) * (m : G)⁻¹ =
              (m' : G) * t₀ * (m' : G)⁻¹ * t₀⁻¹ by rw [hcomm]; group] }
  have hKcard : 4 ≤ Nat.card δ.ker := by
    have h1 := Subgroup.card_ker_mul_card_range δ
    have h2 : Nat.card ↥(cfgM T T₁) = 16 := by
      rw [hS.card_cfgM_eq_sq, hL4]
      norm_num
    have h3 : Nat.card δ.range ≤ 4 := by
      have := Nat.card_le_card_of_injective (fun x : δ.range => (x : ↥L')) Subtype.val_injective
      rwa [hcardL'] at this
    by_contra hlt
    push Not at hlt
    nlinarith
  have hK₀L' : δ.ker.map (cfgM T T₁).subtype ≤ L' := by
    rintro _ ⟨m, hm, rfl⟩
    have hmt : (m : G) * t₀ = t₀ * (m : G) := by
      have h1 : ((δ m : ↥L') : G) = 1 := by rw [MonoidHom.mem_ker.1 hm]; rfl
      have h2 : (m : G) * t₀ * (m : G)⁻¹ * t₀⁻¹ = 1 := h1
      calc (m : G) * t₀ = ((m : G) * t₀ * (m : G)⁻¹ * t₀⁻¹) * (t₀ * m) := by group
        _ = t₀ * m := by rw [h2, one_mul]
    have hmT' : ∀ v ∈ T', (m : G) * v = v * (m : G) := by
      intro v hv
      by_cases hvL' : v ∈ L'
      · exact hMc m m.2 v hvL'
      · have hvt : v * t₀ ∈ L' := mul_mem_of_not_mem_of_card hL'T' hcardT' hv ht₀T' hvL' ht₀L'
        have h1 : (m : G) * (v * t₀) = (v * t₀) * (m : G) := hMc m m.2 _ hvt
        calc (m : G) * v = ((m : G) * (v * t₀)) * t₀⁻¹ := by group
          _ = ((v * t₀) * (m : G)) * t₀⁻¹ := by rw [h1]
          _ = v * (t₀ * (m : G)) * t₀⁻¹ := by group
          _ = v * ((m : G) * t₀) * t₀⁻¹ := by rw [hmt]
          _ = v * (m : G) := by group
    by_cases hm1 : (m : G) = 1
    · show (m : G) ∈ L'
      rw [hm1]
      exact L'.one_mem
    have hmD : (m : G) ∈ classD T := by
      obtain ⟨x, -, hx⟩ := hpart m m.2 hm1
      have hxT : x⁻¹ * (m : G) * x ∈ T := mem_conjSubgroup.1 hx
      refine ⟨x⁻¹, x⁻¹ * (m : G) * x, hxT, fun h1 => hm1 ?_, by group⟩
      have e1 : (m : G) = x * (x⁻¹ * (m : G) * x) * x⁻¹ := by group
      rw [e1, h1]
      group
    have hmT'mem : (m : G) ∈ T' := by
      rw [hT'k]
      exact mem_conj_of_mem_classD_of_centralizes hS.cfg.wc hmD fun t ht =>
        hmT' t (by rw [hT'k]; exact ht)
    obtain ⟨⟨l₀, hl₀⟩, hl₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hS.cfg.ne
    have hl₀1' : l₀ ≠ 1 := fun h1 => hl₀1 (Subtype.ext h1)
    have hmN : (m : G) ∈ Subgroup.normalizer (T : Set G) :=
      hS.cfg.wc.centralizer_le_normalizer (normIn_le T T₁ hl₀) hl₀1'
        (Subgroup.mem_centralizer_singleton_iff.2
          (elemAbelian_mul_comm hMab m.2 (Cfg.normIn_le_cfgM_left T T₁ hl₀)))
    show (m : G) ∈ L'
    rw [← hL'eq]
    exact ⟨hmT'mem, hmN⟩
  have hK₀eq : δ.ker.map (cfgM T T₁).subtype = L' := by
    refine Subgroup.eq_of_le_of_card_ge hK₀L' ?_
    rw [Subgroup.card_map_of_injective (cfgM T T₁).subtype_injective]
    omega
  rw [← hL', ← hK₀eq]
  exact Subgroup.map_subtype_le _

theorem conj_le_sup [Finite G] {n : ℕ} (hn : Odd n) (hn3 : 3 < n) (e : XQ ≃* DihedralGroup n)
    (hL4 : Nat.card (normIn T T₁) = 4) : conjSubgroup a T₁ ≤ T ⊔ T₁ := by
  have hS := h.sec
  obtain ⟨-, hpart⟩ := hS.eq_five_and_exists_conj_of_card_four hn hn3 e hL4
  obtain ⟨x₀, hx₀X, hx₀⟩ := hS.conj
  have hL'M := h.conj_le_cfgM hn hn3 e hL4
  have hL'ne : conjSubgroup a (normIn T₁ T) ≠ ⊥ := fun h0 =>
    hS.cfg.ne₁ (conjSubgroup_eq_bot_iff.1 h0)
  obtain ⟨⟨f, hfL'⟩, hf1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hL'ne
  have hf1' : f ≠ 1 := fun h1 => hf1 (Subtype.ext h1)
  obtain ⟨x, hxX, hfx⟩ := hpart f (hL'M hfL') hf1'
  have hfT' : f ∈ conjSubgroup a T₁ := conjSubgroup_mono (normIn_le T₁ T) hfL'
  have hwc : IsWC (conjSubgroup x T) := hS.cfg.wc.conj x
  have hT'x : conjSubgroup a T₁ = conjSubgroup x T := by
    have hk : conjSubgroup a T₁ = conjSubgroup ((a * x₀) * x⁻¹) (conjSubgroup x T) := by
      rw [conjSubgroup_conjSubgroup, show a * x₀ * x⁻¹ * x = a * x₀ by group, hx₀,
        conjSubgroup_conjSubgroup]
    rw [hk]
    refine hwc.conj_eq_of_inf_ne_bot ?_
    intro h0
    have hm : f ∈ conjSubgroup x T ⊓ conjSubgroup ((a * x₀) * x⁻¹) (conjSubgroup x T) :=
      ⟨hfx, hk ▸ hfT'⟩
    rw [h0, Subgroup.mem_bot] at hm
    exact hf1' hm
  rw [hT'x]
  exact conjSubgroup_le_of_le_of_mem le_sup_left hxX

theorem mem_normalizer_sup_cfgM [Finite G] {n : ℕ} (hn : Odd n) (hn3 : 3 < n)
    (e : XQ ≃* DihedralGroup n) (hL4 : Nat.card (normIn T T₁) = 4) :
    a ∈ Subgroup.normalizer ((T ⊔ T₁ : Subgroup G) : Set G) ∧
      a ∈ Subgroup.normalizer ((cfgM T T₁ : Subgroup G) : Set G) := by
  have haT : conjSubgroup a T = T := mem_normalizer_iff_conjSubgroup_eq.1 h.haN
  have haL : conjSubgroup a (normIn T T₁) = normIn T T₁ :=
    mem_normalizer_iff_conjSubgroup_eq.1 h.haNL
  have hT'X := h.conj_le_sup hn hn3 e hL4
  have hL'M := h.conj_le_cfgM hn hn3 e hL4
  constructor
  · rw [mem_normalizer_iff_conjSubgroup_eq]
    refine conjSubgroup_eq_of_le ?_
    rw [conjSubgroup_sup_eq_sup, haT]
    exact sup_le le_sup_left hT'X
  · rw [mem_normalizer_iff_conjSubgroup_eq]
    refine conjSubgroup_eq_of_le ?_
    rw [cfgM, conjSubgroup_sup_eq_sup, haL]
    exact sup_le (Cfg.normIn_le_cfgM_left T T₁) hL'M

end Quotient

end SecB6

theorem sec3TenExceptional : Sec3TenExceptional := by
  intro G _ _ _ hnab T T₁ S n hS hn hn3 hD hL4 a u hB hu hvals hnc
  obtain ⟨hN, ⟨e⟩⟩ := hD
  have hD : Sec3Dih T T₁ n := ⟨hN, ⟨e⟩⟩
  obtain ⟨hn5, -⟩ := hS.eq_five_and_exists_conj_of_card_four hn hn3 e hL4
  subst hn5
  have hTab := hS.cfg.wc.1
  have haT : conjSubgroup a T = T := mem_normalizer_iff_conjSubgroup_eq.1 hB.haN
  obtain ⟨haXn, haMn⟩ := hB.mem_normalizer_sup_cfgM hn hn3 e hL4
  have hL'M := hB.conj_le_cfgM hn hn3 e hL4
  have hT'X := hB.conj_le_sup hn hn3 e hL4
  have haX : ∀ x ∈ T ⊔ T₁, a * x * a⁻¹ ∈ T ⊔ T₁ := fun x hx => conj_mem_of_mem_normalizer haXn hx
  have haM : ∀ m ∈ cfgM T T₁, a * m * a⁻¹ ∈ cfgM T T₁ := fun m hm =>
    conj_mem_of_mem_normalizer haMn hm
  obtain ⟨x₀, hx₀X, hx₀⟩ := hS.conj
  obtain ⟨t₀, ht₀T, ht₀M⟩ : ∃ t₀ ∈ T, t₀ ∉ cfgM T T₁ := by
    by_contra hcon
    push Not at hcon
    exact hS.not_le_cfgM hcon
  obtain ⟨t₁, ht₁T, ht₁M⟩ : ∃ t₁ ∈ T₁, t₁ ∉ cfgM T T₁ := by
    by_contra hcon
    push Not at hcon
    exact hS.not_conj_le_cfgM hx₀X (hx₀ ▸ hcon)
  have ht₀X : t₀ ∈ T ⊔ T₁ := (le_sup_left : T ≤ T ⊔ T₁) ht₀T
  have ht₁X : t₁ ∈ T ⊔ T₁ := (le_sup_right : T₁ ≤ T ⊔ T₁) ht₁T
  have hT₁ab := hS.cfg.wc₁.1
  have ht₀2 : t₀ * t₀ = 1 := elemAbelian_mul_self hTab ht₀T
  have ht₁2 : t₁ * t₁ = 1 := elemAbelian_mul_self hT₁ab ht₁T
  have ht₀i : t₀⁻¹ = t₀ := inv_eq_of_mul_eq_one_right ht₀2
  have ht₁i : t₁⁻¹ = t₁ := inv_eq_of_mul_eq_one_right ht₁2
  have haa := hB.haa
  let f : ↥(T ⊔ T₁) →* ↥(T ⊔ T₁) :=
    { toFun := fun x => ⟨a * x * a⁻¹, haX x x.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro x y
        apply Subtype.ext
        show a * ((x : G) * (y : G)) * a⁻¹ = (a * (x : G) * a⁻¹) * (a * (y : G) * a⁻¹)
        group }
  let ρG : (↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁)) →*
      (↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁)) :=
    QuotientGroup.map _ _ f (fun x hx => Subgroup.mem_comap.2
      (Subgroup.mem_subgroupOf.2 (haM x (Subgroup.mem_subgroupOf.1 hx))))
  have hρG : ∀ (x : G) (hx : x ∈ T ⊔ T₁), ρG (QuotientGroup.mk ⟨x, hx⟩) =
      QuotientGroup.mk ⟨a * x * a⁻¹, haX x hx⟩ := fun x hx =>
    QuotientGroup.map_mk _ _ f _ ⟨x, hx⟩
  have hρGρG : ∀ y : (↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁)), ρG (ρG y) = y := by
    intro y
    induction y using QuotientGroup.induction_on with
    | H x =>
      obtain ⟨x, hx⟩ := x
      rw [hρG x hx, hρG (a * x * a⁻¹) (haX x hx)]
      refine congrArg QuotientGroup.mk (Subtype.ext ?_)
      show a * (a * x * a⁻¹) * a⁻¹ = x
      calc a * (a * x * a⁻¹) * a⁻¹ = (a * a) * x * (a * a)⁻¹ := by group
        _ = x := by rw [haa]; group
  have hmkM : ∀ (x : G) (hx : x ∈ T ⊔ T₁),
      (QuotientGroup.mk ⟨x, hx⟩ : ↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁)) = 1 ↔
        x ∈ cfgM T T₁ := fun x hx =>
    ⟨fun h1 => Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h1),
      fun h1 => (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 h1)⟩
  have hmkmul : ∀ (x y : G) (hx : x ∈ T ⊔ T₁) (hy : y ∈ T ⊔ T₁),
      (QuotientGroup.mk ⟨x, hx⟩ : ↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁)) *
        QuotientGroup.mk ⟨y, hy⟩ = QuotientGroup.mk ⟨x * y, (T ⊔ T₁).mul_mem hx hy⟩ :=
    fun x y hx hy => (QuotientGroup.mk_mul _ _ _).symm
  have haX₁ : a * t₁ * a⁻¹ ∈ T ⊔ T₁ := haX t₁ ht₁X
  have hq₀ : (QuotientGroup.mk ⟨t₀, ht₀X⟩ : ↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁)) *
      QuotientGroup.mk ⟨t₀, ht₀X⟩ = 1 := by
    rw [hmkmul, hmkM]
    rw [ht₀2]
    exact one_mem _
  have hq₁ : (QuotientGroup.mk ⟨t₁, ht₁X⟩ : ↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁)) *
      QuotientGroup.mk ⟨t₁, ht₁X⟩ = 1 := by
    rw [hmkmul, hmkM]
    rw [ht₁2]
    exact one_mem _
  have hq₂ : (QuotientGroup.mk ⟨a * t₁ * a⁻¹, haX₁⟩ :
      ↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁)) *
      QuotientGroup.mk ⟨a * t₁ * a⁻¹, haX₁⟩ = 1 := by
    rw [hmkmul, hmkM]
    have : a * t₁ * a⁻¹ * (a * t₁ * a⁻¹) = 1 := by
      calc a * t₁ * a⁻¹ * (a * t₁ * a⁻¹) = a * (t₁ * t₁) * a⁻¹ := by group
        _ = 1 := by rw [ht₁2]; group
    rw [this]
    exact one_mem _
  have hq₀1 : (QuotientGroup.mk ⟨t₀, ht₀X⟩ :
      ↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁)) ≠ 1 := fun h1 => ht₀M ((hmkM _ _).1 h1)
  have hq₁1 : (QuotientGroup.mk ⟨t₁, ht₁X⟩ :
      ↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁)) ≠ 1 := fun h1 => ht₁M ((hmkM _ _).1 h1)
  have hq₂1 : (QuotientGroup.mk ⟨a * t₁ * a⁻¹, haX₁⟩ :
      ↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁)) ≠ 1 := by
    intro h1
    apply ht₁M
    have h3 := conj_mem_of_mem_normalizer ((Subgroup.normalizer _).inv_mem haMn)
      ((hmkM _ _).1 h1)
    have e1 : a⁻¹ * (a * t₁ * a⁻¹) * a⁻¹⁻¹ = t₁ := by group
    rwa [e1] at h3
  let ρ : DihedralGroup 5 →* DihedralGroup 5 := e.toMonoidHom.comp (ρG.comp e.symm.toMonoidHom)
  have hρρ : ∀ g, ρ (ρ g) = g := by
    intro g
    show e (ρG (e.symm (e (ρG (e.symm g))))) = g
    rw [MulEquiv.symm_apply_apply, hρGρG, MulEquiv.apply_symm_apply]
  obtain ⟨i₀, hi₀⟩ := dih_exists_sr_of_sq hn (by rw [← map_mul, hq₀, map_one])
    (fun h1 => hq₀1 (e.injective (h1.trans (map_one e).symm)))
  obtain ⟨i₁, hi₁⟩ := dih_exists_sr_of_sq hn (by rw [← map_mul, hq₁, map_one])
    (fun h1 => hq₁1 (e.injective (h1.trans (map_one e).symm)))
  obtain ⟨i₂, hi₂⟩ := dih_exists_sr_of_sq hn (by rw [← map_mul, hq₂, map_one])
    (fun h1 => hq₂1 (e.injective (h1.trans (map_one e).symm)))
  have hLa : ∀ t ∈ T, ⁅t, a⁆ ∈ normIn T T₁ := fun t ht => by
    rcases hvals t ht with h0 | h0
    · rw [h0]
      exact (normIn T T₁).one_mem
    · rw [h0]
      exact hu
  have hcom0 : (a * t₀ * a⁻¹)⁻¹ * t₀ ∈ cfgM T T₁ := by
    have e1 : (a * t₀ * a⁻¹)⁻¹ * t₀ = (⁅t₀, a⁆)⁻¹ := by
      calc (a * t₀ * a⁻¹)⁻¹ * t₀ = a * t₀⁻¹ * a⁻¹ * t₀ := by group
        _ = a * t₀ * a⁻¹ * t₀⁻¹ := by rw [ht₀i]
        _ = (⁅t₀, a⁆)⁻¹ := by
          simp only [commutatorElement_def]
          group
    rw [e1]
    exact (cfgM T T₁).inv_mem (Cfg.normIn_le_cfgM_left T T₁ (hLa t₀ ht₀T))
  have hρ0 : ρ (sr i₀) = sr i₀ := by
    rw [← hi₀]
    show e (ρG (e.symm (e (QuotientGroup.mk ⟨t₀, ht₀X⟩)))) = e (QuotientGroup.mk ⟨t₀, ht₀X⟩)
    rw [MulEquiv.symm_apply_apply, hρG t₀ ht₀X]
    exact congrArg e ((mk_eq_iff _ _).2 hcom0)
  have hρ1 : ρ (sr i₁) = sr i₂ := by
    rw [← hi₁]
    show e (ρG (e.symm (e (QuotientGroup.mk ⟨t₁, ht₁X⟩)))) = sr i₂
    rw [MulEquiv.symm_apply_apply, hρG t₁ ht₁X]
    exact hi₂
  have hcardT₁ := hB.card_T₁
  have hVp : IsPGroup 2 ↥(T₁ ⊔ cfgM T T₁) :=
    (isPGroup_two_of_isElemAbelian hS.cfg.wc₁.1).to_sup_of_normal_right'
      (isPGroup_two_of_isElemAbelian hS.cfg.isElemAbelian_cfgM)
      (le_sup_right.trans hS.cfg.le_normalizer_cfgM)
  have ht₁L₁ : t₁ ∉ normIn T₁ T := fun hh => ht₁M (Cfg.normIn_le_cfgM_right T T₁ hh)
  rcases dih5_conj_dichotomy ρ hρρ hρ0 hρ1 with hcase | hcase
  ·
    exfalso
    have hm21 : (QuotientGroup.mk ⟨a * t₁ * a⁻¹, haX₁⟩ :
        ↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁)) = QuotientGroup.mk ⟨t₁, ht₁X⟩ := by
      apply e.injective
      rw [hi₂, hi₁, hcase]
    have hB1 : (a * t₁ * a⁻¹)⁻¹ * t₁ ∈ cfgM T T₁ := (mk_eq_iff haX₁ ht₁X).1 hm21
    have hconj : conjSubgroup a T₁ ≤ T₁ ⊔ cfgM T T₁ := by
      intro y hy
      obtain ⟨v, hvT₁, rfl⟩ := mem_conjSubgroup_iff_exists.1 hy
      by_cases hvL₁ : v ∈ normIn T₁ T
      · exact Subgroup.mem_sup_right (hL'M (conj_mem_conjSubgroup a hvL₁))
      · have hvt : v * t₁ ∈ normIn T₁ T :=
          mul_mem_of_not_mem_of_card (normIn_le T₁ T) hcardT₁ hvT₁ ht₁T hvL₁ ht₁L₁
        have h1 : a * (v * t₁) * a⁻¹ ∈ cfgM T T₁ := hL'M (conj_mem_conjSubgroup a hvt)
        have h2 : (a * t₁ * a⁻¹)⁻¹ ∈ T₁ ⊔ cfgM T T₁ := by
          have e1 : (a * t₁ * a⁻¹)⁻¹ = ((a * t₁ * a⁻¹)⁻¹ * t₁) * t₁⁻¹ := by group
          rw [e1]
          exact (T₁ ⊔ cfgM T T₁).mul_mem (Subgroup.mem_sup_right hB1)
            (Subgroup.mem_sup_left (T₁.inv_mem ht₁T))
        have e2 : a * v * a⁻¹ = (a * (v * t₁) * a⁻¹) * (a * t₁ * a⁻¹)⁻¹ := by group
        rw [e2]
        exact (T₁ ⊔ cfgM T T₁).mul_mem (Subgroup.mem_sup_right h1) h2
    exact hB.hne (eq_of_conj_le_pGroup hS.cfg.wc₁ hVp le_sup_left hconj)
  ·
    have ht₀t₁t₀X : t₀ * t₁ * t₀ ∈ T ⊔ T₁ :=
      (T ⊔ T₁).mul_mem ((T ⊔ T₁).mul_mem ht₀X ht₁X) ht₀X
    have hm2 : (QuotientGroup.mk ⟨a * t₁ * a⁻¹, haX₁⟩ :
        ↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁)) =
        QuotientGroup.mk ⟨t₀ * t₁ * t₀, ht₀t₁t₀X⟩ := by
      apply e.injective
      rw [hi₂, hcase]
      have e1 : (QuotientGroup.mk ⟨t₀ * t₁ * t₀, ht₀t₁t₀X⟩ :
          ↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁)) =
          QuotientGroup.mk ⟨t₀, ht₀X⟩ * QuotientGroup.mk ⟨t₁, ht₁X⟩ *
            QuotientGroup.mk ⟨t₀, ht₀X⟩ := by
        rw [hmkmul, hmkmul]
      rw [e1, map_mul, map_mul, hi₀, hi₁, sr_mul_sr, r_mul_sr]
      congr 1
      ring
    have hB2 : (a * t₁ * a⁻¹)⁻¹ * (t₀ * t₁ * t₀) ∈ cfgM T T₁ :=
      (mk_eq_iff haX₁ ht₀t₁t₀X).1 hm2
    have hTM : ∀ z ∈ T, ∀ m ∈ cfgM T T₁, z * m * z⁻¹ ∈ cfgM T T₁ := fun z hz m hm =>
      hS.cfg.conj_mem_cfgM_of_mem_left hz hm
    have ht₀iT : t₀⁻¹ ∈ T := T.inv_mem ht₀T
    have hκT₁ : conjSubgroup (t₀⁻¹ * a) T₁ = T₁ := by
      refine eq_of_conj_le_pGroup hS.cfg.wc₁ hVp le_sup_left ?_
      intro y hy
      obtain ⟨v, hvT₁, rfl⟩ := mem_conjSubgroup_iff_exists.1 hy
      have hκv : (t₀⁻¹ * a) * v * (t₀⁻¹ * a)⁻¹ = t₀⁻¹ * (a * v * a⁻¹) * t₀⁻¹⁻¹ := by group
      have hconjM : ∀ m ∈ cfgM T T₁, t₀⁻¹ * m * t₀⁻¹⁻¹ ∈ cfgM T T₁ := fun m hm =>
        hTM _ ht₀iT m hm
      by_cases hvL₁ : v ∈ normIn T₁ T
      · rw [hκv]
        exact Subgroup.mem_sup_right (hconjM _ (hL'M (conj_mem_conjSubgroup a hvL₁)))
      · have hvt : v * t₁ ∈ normIn T₁ T :=
          mul_mem_of_not_mem_of_card (normIn_le T₁ T) hcardT₁ hvT₁ ht₁T hvL₁ ht₁L₁
        have h1 : t₀⁻¹ * (a * (v * t₁) * a⁻¹) * t₀⁻¹⁻¹ ∈ cfgM T T₁ :=
          hconjM _ (hL'M (conj_mem_conjSubgroup a hvt))
        have h2 : (t₀⁻¹ * (a * t₁ * a⁻¹) * t₀⁻¹⁻¹)⁻¹ ∈ T₁ ⊔ cfgM T T₁ := by
          refine (T₁ ⊔ cfgM T T₁).inv_mem ?_
          have hm' := hTM t₀ ht₀T _ ((cfgM T T₁).inv_mem hB2)
          rw [ht₀i] at hm'
          have e1 : t₀⁻¹ * (a * t₁ * a⁻¹) * t₀⁻¹⁻¹ =
              t₁ * (t₀ * ((a * t₁ * a⁻¹)⁻¹ * (t₀ * t₁ * t₀))⁻¹ * t₀) := by group
          rw [e1]
          exact (T₁ ⊔ cfgM T T₁).mul_mem (Subgroup.mem_sup_left ht₁T) (Subgroup.mem_sup_right hm')
        have e2 : t₀⁻¹ * (a * v * a⁻¹) * t₀⁻¹⁻¹ =
            (t₀⁻¹ * (a * (v * t₁) * a⁻¹) * t₀⁻¹⁻¹) *
              (t₀⁻¹ * (a * t₁ * a⁻¹) * t₀⁻¹⁻¹)⁻¹ := by group
        rw [hκv, e2]
        exact (T₁ ⊔ cfgM T T₁).mul_mem (Subgroup.mem_sup_right h1) h2
    have hκN : t₀⁻¹ * a ∈ Subgroup.normalizer (T : Set G) :=
      (Subgroup.normalizer _).mul_mem ((Subgroup.normalizer _).inv_mem
        (Subgroup.le_normalizer ht₀T)) hB.haN
    have hcomm_κ : ∀ t' ∈ T, ⁅t', t₀⁻¹ * a⁆ = ⁅t', a⁆ := by
      intro t' ht'
      have htt' : t' * t₀⁻¹ = t₀⁻¹ * t' := by
        rw [ht₀i]
        exact elemAbelian_mul_comm hTab ht' ht₀T
      have hct : ⁅t', a⁆ * t₀ = t₀ * ⁅t', a⁆ :=
        elemAbelian_mul_comm hTab (normIn_le T T₁ (hLa t' ht')) ht₀T
      calc ⁅t', t₀⁻¹ * a⁆ = (t' * t₀⁻¹) * a * t'⁻¹ * a⁻¹ * t₀ := by
            simp only [commutatorElement_def]
            group
        _ = (t₀⁻¹ * t') * a * t'⁻¹ * a⁻¹ * t₀ := by rw [htt']
        _ = t₀⁻¹ * (⁅t', a⁆ * t₀) := by
            simp only [commutatorElement_def]
            group
        _ = t₀⁻¹ * (t₀ * ⁅t', a⁆) := by rw [hct]
        _ = ⁅t', a⁆ := by group
    have hvalsκ : ∀ t' ∈ T, ⁅t', t₀⁻¹ * a⁆ = 1 ∨ ⁅t', t₀⁻¹ * a⁆ = u := fun t' ht' => by
      rw [hcomm_κ t' ht']
      exact hvals t' ht'
    have hLκ : ∀ t' ∈ T, ⁅t', t₀⁻¹ * a⁆ ∈ normIn T T₁ := fun t' ht' => by
      rw [hcomm_κ t' ht']
      exact hLa t' ht'
    have hncκ : ∃ l ∈ normIn T T₁, (t₀⁻¹ * a) * l ≠ l * (t₀⁻¹ * a) := by
      obtain ⟨l, hl, hne⟩ := hnc
      refine ⟨l, hl, fun heq => hne ?_⟩
      have htl : t₀ * l = l * t₀ := elemAbelian_mul_comm hTab ht₀T (normIn_le T T₁ hl)
      calc a * l = t₀ * ((t₀⁻¹ * a) * l) := by group
        _ = t₀ * (l * (t₀⁻¹ * a)) := by rw [heq]
        _ = (t₀ * l) * (t₀⁻¹ * a) := by group
        _ = (l * t₀) * (t₀⁻¹ * a) := by rw [htl]
        _ = l * a := by group
    exact Sec3.false_of_conj_eq hS hn hn3 hD hκN hκT₁ hLκ hvalsκ hncκ

end CFSG.CGT.Timmesfeld75
