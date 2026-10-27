module

public import CFSG.CGT.Timmesfeld75.Sec3TenCaseB4
public import CFSG.CGT.Timmesfeld75.Sec3TenCaseB3

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] {T T₁ S : Subgroup G} {a : G}

theorem card_le_sq_centralizer [Finite G] {V : Subgroup G} (hV : IsElemAbelian 2 V) {a : G}
    (haa : a * a = 1) (haV : ∀ v ∈ V, a * v * a⁻¹ ∈ V) :
    Nat.card V ≤ Nat.card ↥(V ⊓ Subgroup.centralizer ({a} : Set G)) ^ 2 := by
  let Φ : ↥V →* ↥V := MonoidHom.mk' (fun v => ⟨v * (a * v * a⁻¹), V.mul_mem v.2 (haV v v.2)⟩) (by
    intro v w
    apply Subtype.ext
    show (v * w : G) * (a * (v * w) * a⁻¹) = (v * (a * v * a⁻¹)) * (w * (a * w * a⁻¹))
    have h1 : (a * v * a⁻¹ : G) * w = w * (a * v * a⁻¹) :=
      elemAbelian_mul_comm hV (haV v v.2) w.2
    calc (v * w : G) * (a * (v * w) * a⁻¹) = v * w * ((a * v * a⁻¹) * (a * w * a⁻¹)) := by group
      _ = v * (w * (a * v * a⁻¹)) * (a * w * a⁻¹) := by group
      _ = v * ((a * v * a⁻¹) * w) * (a * w * a⁻¹) := by rw [h1]
      _ = (v * (a * v * a⁻¹)) * (w * (a * w * a⁻¹)) := by group)
  have hker : ∀ v : ↥V, v ∈ Φ.ker → (v : G) ∈ V ⊓ Subgroup.centralizer ({a} : Set G) := by
    intro v hv
    refine ⟨v.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have h1 : (v : G) * (a * v * a⁻¹) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hv)
    have hvv : (v : G) * v = 1 := elemAbelian_mul_self hV v.2
    have h2 : a * (v : G) * a⁻¹ = (v : G)⁻¹ := eq_inv_of_mul_eq_one_right h1
    have h3 : (v : G)⁻¹ = v := inv_eq_of_mul_eq_one_right hvv
    rw [h3] at h2
    calc (v : G) * a = (a * v * a⁻¹) * a := by rw [h2]
      _ = a * v := by group
  have hran : ∀ y : ↥V, y ∈ Φ.range → (y : G) ∈ V ⊓ Subgroup.centralizer ({a} : Set G) := by
    rintro y ⟨v, rfl⟩
    refine ⟨(Φ v).2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    change (v : G) * (a * v * a⁻¹) * a = a * ((v : G) * (a * v * a⁻¹))
    have h1 : (a * v * a⁻¹ : G) * v = v * (a * v * a⁻¹) :=
      elemAbelian_mul_comm hV (haV v v.2) v.2
    have h2 : a * (a * v * a⁻¹) * a⁻¹ = (v : G) := by
      calc a * (a * v * a⁻¹) * a⁻¹ = (a * a) * v * (a * a)⁻¹ := by group
        _ = v := by rw [haa]; group
    calc (v : G) * (a * v * a⁻¹) * a = (a * v * a⁻¹) * v * a := by rw [h1]
      _ = (a * v * a⁻¹) * (a * (a * v * a⁻¹) * a⁻¹) * a := by rw [h2]
      _ = a * ((v : G) * (a * v * a⁻¹)) := by group
  have hk : Nat.card Φ.ker ≤ Nat.card ↥(V ⊓ Subgroup.centralizer ({a} : Set G)) :=
    Nat.card_le_card_of_injective (fun x => ⟨(x : ↥V).1, hker x x.2⟩)
      (fun x y hxy => Subtype.ext (Subtype.ext (by
        have := congrArg (fun z : ↥(V ⊓ Subgroup.centralizer ({a} : Set G)) => (z : G)) hxy
        exact this)))
  have hr : Nat.card Φ.range ≤ Nat.card ↥(V ⊓ Subgroup.centralizer ({a} : Set G)) :=
    Nat.card_le_card_of_injective (fun x => ⟨(x : ↥V).1, hran x x.2⟩)
      (fun x y hxy => Subtype.ext (Subtype.ext (by
        have := congrArg (fun z : ↥(V ⊓ Subgroup.centralizer ({a} : Set G)) => (z : G)) hxy
        exact this)))
  rw [← Subgroup.card_ker_mul_card_range Φ, sq]
  exact Nat.mul_le_mul hk hr

namespace SecB6

variable (h : SecB6 T T₁ S a)

include h

theorem mem_cfgM_iff [Finite G] (h214 : Lemma214) (hInv : InvolutionClassInput) {m : G} :
    m ∈ cfgM T₁ (conjSubgroup a T₁) ↔
      ∃ e ∈ normIn T₁ T, ∃ f ∈ conjSubgroup a (normIn T₁ T), m = e * f := by
  rw [h.cfgM_eq_sup h214 hInv]
  have hnorm : normIn T₁ T ≤ Subgroup.normalizer (conjSubgroup a (normIn T₁ T) : Set G) := by
    apply le_normalizer_of_conjSubgroup_le
    intro g hg
    apply conjSubgroup_le_of_forall_mem
    intro x hx
    rw [mul_inv_eq_iff_eq_mul.2 (h.hcomm g hg x hx)]
    exact hx
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right (normIn T₁ T)
    (conjSubgroup a (normIn T₁ T)) hnorm
  constructor
  · intro hm
    have hm' : m ∈ ((normIn T₁ T : Set G) * (conjSubgroup a (normIn T₁ T) : Set G)) := by
      rw [← hmul]
      exact hm
    obtain ⟨e, he, f, hf, rfl⟩ := hm'
    exact ⟨e, he, f, hf, rfl⟩
  · rintro ⟨e, he, f, hf, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left he) (Subgroup.mem_sup_right hf)

theorem fixed_eq [Finite G] (h214 : Lemma214) (hInv : InvolutionClassInput) {w : G}
    (hw : w ∈ cfgM T₁ (conjSubgroup a T₁)) (hwa : a * w * a⁻¹ = w) :
    ∃ e ∈ normIn T₁ T, w = e * (a * e * a⁻¹) := by
  obtain ⟨e, he, f, hf, rfl⟩ := (h.mem_cfgM_iff h214 hInv).1 hw
  obtain ⟨e', he', rfl⟩ := mem_conjSubgroup_iff_exists.1 hf
  have h1 : a * (e * (a * e' * a⁻¹)) * a⁻¹ = (a * e * a⁻¹) * e' := by
    have haa' : a⁻¹ * a⁻¹ = 1 := by rw [← mul_inv_rev, h.haa, inv_one]
    calc a * (e * (a * e' * a⁻¹)) * a⁻¹
        = (a * e * a⁻¹) * ((a * a) * e' * (a⁻¹ * a⁻¹)) := by group
      _ = (a * e * a⁻¹) * e' := by rw [h.haa, haa', one_mul, mul_one]
  rw [h1] at hwa
  have hα : a * e * a⁻¹ ∈ conjSubgroup a (normIn T₁ T) := conj_mem_conjSubgroup a he
  have hcomm : e' * (a * e * a⁻¹) = (a * e * a⁻¹) * e' := h.hcomm e' he' _ hα
  have hx : e⁻¹ * e' = (a * e' * a⁻¹) * (a * e * a⁻¹)⁻¹ := by
    calc e⁻¹ * e' = e⁻¹ * (e' * (a * e * a⁻¹)) * (a * e * a⁻¹)⁻¹ := by group
      _ = e⁻¹ * ((a * e * a⁻¹) * e') * (a * e * a⁻¹)⁻¹ := by rw [hcomm]
      _ = e⁻¹ * (e * (a * e' * a⁻¹)) * (a * e * a⁻¹)⁻¹ := by rw [hwa]
      _ = (a * e' * a⁻¹) * (a * e * a⁻¹)⁻¹ := by group
  have hxT₁ : e⁻¹ * e' ∈ T₁ :=
    T₁.mul_mem (T₁.inv_mem (normIn_le _ _ he)) (normIn_le _ _ he')
  have hxP : e⁻¹ * e' ∈ conjSubgroup a T₁ := by
    rw [hx]
    exact (conjSubgroup a T₁).mul_mem
      (conjSubgroup_mono (normIn_le T₁ T) (conj_mem_conjSubgroup a he'))
      ((conjSubgroup a T₁).inv_mem (conjSubgroup_mono (normIn_le T₁ T) hα))
  have hbot := h.sec.cfg.wc₁.inf_conj_eq_bot h.hne
  have hmem : e⁻¹ * e' ∈ T₁ ⊓ conjSubgroup a T₁ := ⟨hxT₁, hxP⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  have hee : e' = e := by
    calc e' = e * (e⁻¹ * e') := by group
      _ = e := by rw [hmem, mul_one]
  subst hee
  exact ⟨e', he', rfl⟩

theorem conj_normIn_comm_L {f l : G} (hf : f ∈ conjSubgroup a (normIn T₁ T))
    (hl : l ∈ normIn T T₁) : f * l = l * f := by
  obtain ⟨e, he, rfl⟩ := mem_conjSubgroup_iff_exists.1 hf
  have h1 : e * (a⁻¹ * l * a) = (a⁻¹ * l * a) * e := by
    have hl' : a⁻¹ * l * a⁻¹⁻¹ ∈ normIn T T₁ :=
      conj_mem_of_mem_normalizer ((Subgroup.normalizer _).inv_mem h.haNL) hl
    have := h.sec.cfg.comm_L_L₁ (l := a⁻¹ * l * a) (x := e) (by simpa using hl') he
    exact this.symm
  calc a * e * a⁻¹ * l = a * (e * (a⁻¹ * l * a)) * a⁻¹ := by group
    _ = a * ((a⁻¹ * l * a) * e) * a⁻¹ := by rw [h1]
    _ = l * (a * e * a⁻¹) := by group

theorem comm_conj {u : G} (hu : u ∈ normIn T T₁) (hvals : ∀ t ∈ T, ⁅t, a⁆ = 1 ∨ ⁅t, a⁆ = u)
    {t e : G} (ht : t ∈ T) (he : e ∈ normIn T₁ T) :
    ⁅t, a * e * a⁻¹⁆ = a * ⁅t, e⁆ * a⁻¹ := by
  have hL := isElemAbelian_of_le h.sec.cfg.wc.1 (normIn_le T T₁)
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right h.haa
  have hκ : a⁻¹ * t * a * t⁻¹ ∈ normIn T T₁ := by
    have e1 : a⁻¹ * t * a * t⁻¹ = (⁅t, a⁆)⁻¹ := by
      calc a⁻¹ * t * a * t⁻¹ = a * t * a⁻¹ * t⁻¹ := by rw [hai]
        _ = (⁅t, a⁆)⁻¹ := by
          simp only [commutatorElement_def]
          group
    rw [e1]
    rcases hvals t ht with h0 | h0
    · rw [h0, inv_one]
      exact (normIn T T₁).one_mem
    · rw [h0]
      exact (normIn T T₁).inv_mem hu
  set κ : G := a⁻¹ * t * a * t⁻¹ with hκdef
  have hκt : a⁻¹ * t * a = κ * t := by rw [hκdef]; group
  have hec : e * κ = κ * e := (h.sec.cfg.comm_L_L₁ hκ he).symm
  have hlam : ⁅t, e⁆ ∈ normIn T T₁ := h.sec.cfg.comm_mem_normIn ht he
  have hkl : κ * ⁅t, e⁆ = ⁅t, e⁆ * κ := elemAbelian_mul_comm hL hκ hlam
  calc ⁅t, a * e * a⁻¹⁆ = a * ((a⁻¹ * t * a) * e * (a⁻¹ * t * a)⁻¹ * e⁻¹) * a⁻¹ := by
        simp only [commutatorElement_def]
        group
    _ = a * (κ * t * e * t⁻¹ * κ⁻¹ * e⁻¹) * a⁻¹ := by rw [hκt]; group
    _ = a * (κ * ⁅t, e⁆ * (e * κ⁻¹ * e⁻¹)) * a⁻¹ := by
        simp only [commutatorElement_def]
        group
    _ = a * ⁅t, e⁆ * a⁻¹ := by
        have h3 : e * κ⁻¹ * e⁻¹ = κ⁻¹ := by
          have := Commute.inv_right (show Commute e κ from hec)
          rw [mul_inv_eq_iff_eq_mul]
          exact this.eq
        rw [h3]
        have h4 : κ * ⁅t, e⁆ * κ⁻¹ = ⁅t, e⁆ := mul_inv_eq_iff_eq_mul.2 hkl
        rw [h4]

theorem cfgM_comm_L [Finite G] (h214 : Lemma214) (hInv : InvolutionClassInput) {w l : G}
    (hw : w ∈ cfgM T₁ (conjSubgroup a T₁)) (hl : l ∈ normIn T T₁) : w * l = l * w := by
  obtain ⟨e, he, f, hf, rfl⟩ := (h.mem_cfgM_iff h214 hInv).1 hw
  have h1 : e * l = l * e := (h.sec.cfg.comm_L_L₁ hl he).symm
  have h2 := h.conj_normIn_comm_L hf hl
  calc e * f * l = e * (l * f) := by rw [mul_assoc, h2]
    _ = (e * l) * f := by group
    _ = (l * e) * f := by rw [h1]
    _ = l * (e * f) := by group

theorem comm_fixed_values {u : G} (hu : u ∈ normIn T T₁)
    (hvals : ∀ t ∈ T, ⁅t, a⁆ = 1 ∨ ⁅t, a⁆ = u) {t e : G} (ht : t ∈ T) (he : e ∈ normIn T₁ T) :
    ⁅t, e * (a * e * a⁻¹)⁆ = 1 ∨ ⁅t, e * (a * e * a⁻¹)⁆ = u := by
  have hL := isElemAbelian_of_le h.sec.cfg.wc.1 (normIn_le T T₁)
  have hlam : ⁅t, e⁆ ∈ normIn T T₁ := h.sec.cfg.comm_mem_normIn ht he
  have hf : a * ⁅t, e⁆ * a⁻¹ ∈ normIn T T₁ := conj_mem_of_mem_normalizer h.haNL hlam
  have hec : e * (a * ⁅t, e⁆ * a⁻¹) = (a * ⁅t, e⁆ * a⁻¹) * e :=
    (h.sec.cfg.comm_L_L₁ hf he).symm
  have hk : ⁅t, e * (a * e * a⁻¹)⁆ = ⁅t, e⁆ * (a * ⁅t, e⁆ * a⁻¹) := by
    have e1 : ⁅t, e * (a * e * a⁻¹)⁆ = ⁅t, e⁆ * (e * ⁅t, a * e * a⁻¹⁆ * e⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e1, h.comm_conj hu hvals ht he]
    have : e * (a * ⁅t, e⁆ * a⁻¹) * e⁻¹ = a * ⁅t, e⁆ * a⁻¹ := mul_inv_eq_iff_eq_mul.2 hec
    rw [this]
  have hlam2 : ⁅t, e⁆ * ⁅t, e⁆ = 1 := elemAbelian_mul_self hL hlam
  have hcl : ⁅t, e⁆ * (a * ⁅t, e⁆ * a⁻¹) = (a * ⁅t, e⁆ * a⁻¹) * ⁅t, e⁆ :=
    elemAbelian_mul_comm hL hlam hf
  have hlamT : ⁅t, e⁆ ∈ T := normIn_le T T₁ hlam
  have hval : ⁅t, e⁆ * (a * ⁅t, e⁆ * a⁻¹) = (⁅⁅t, e⁆, a⁆)⁻¹ := by
    have hinv : ⁅t, e⁆⁻¹ = ⁅t, e⁆ := inv_eq_of_mul_eq_one_right hlam2
    calc ⁅t, e⁆ * (a * ⁅t, e⁆ * a⁻¹) = (a * ⁅t, e⁆ * a⁻¹) * ⁅t, e⁆ := hcl
      _ = (a * ⁅t, e⁆ * a⁻¹ * ⁅t, e⁆⁻¹) := by rw [hinv]
      _ = (⁅⁅t, e⁆, a⁆)⁻¹ := by
        simp only [commutatorElement_def]
        group
  rw [hk, hval]
  rcases hvals _ hlamT with h0 | h0
  · left
    rw [h0, inv_one]
  · right
    rw [h0]
    exact inv_eq_of_mul_eq_one_right (elemAbelian_mul_self hL hu)

theorem values_of_fixed [Finite G] (h214 : Lemma214) (hInv : InvolutionClassInput) {u : G}
    (hu : u ∈ normIn T T₁) (hvals : ∀ t ∈ T, ⁅t, a⁆ = 1 ∨ ⁅t, a⁆ = u) {w t : G}
    (hw : w ∈ cfgM T₁ (conjSubgroup a T₁)) (hwa : a * w * a⁻¹ = w) (ht : t ∈ T) :
    ⁅t, w⁆ = 1 ∨ ⁅t, w⁆ = u := by
  obtain ⟨e, he, rfl⟩ := h.fixed_eq h214 hInv hw hwa
  exact h.comm_fixed_values hu hvals ht he

theorem exists_ne_one_centralizes [Finite G] (h214 : Lemma214) (hInv : InvolutionClassInput)
    {u : G} (hu : u ∈ normIn T T₁) (hvals : ∀ t ∈ T, ⁅t, a⁆ = 1 ∨ ⁅t, a⁆ = u)
    {V : Subgroup G} (hVN : V ≤ cfgM T₁ (conjSubgroup a T₁)) (hVa : ∀ w ∈ V, a * w * a⁻¹ = w)
    (hV3 : 3 ≤ Nat.card V) : ∃ w ∈ V, w ≠ 1 ∧ ∀ t ∈ T, t * w = w * t := by
  have hLT : normIn T T₁ ≤ T := normIn_le T T₁
  have hTnle : ¬ T ≤ normIn T T₁ := by
    intro hle
    have heq : normIn T T₁ = T := le_antisymm hLT hle
    have hpos : 0 < Nat.card T := Nat.card_pos
    have := h.hcard
    rw [heq] at this
    omega
  obtain ⟨t₀, ht₀T, ht₀L⟩ := IsConcreteLE.not_le_iff_exists.1 hTnle
  classical
  let f : V → Bool := fun w => decide (⁅t₀, (w : G)⁆ = 1)
  let _ : Fintype V := Fintype.ofFinite V
  have hcard : Fintype.card Bool < Fintype.card V := by
    rw [Fintype.card_bool, ← Nat.card_eq_fintype_card]
    omega
  obtain ⟨x, y, hxy, hfxy⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  have hvx := h.values_of_fixed h214 hInv hu hvals (hVN x.2) (hVa x x.2) ht₀T
  have hvy := h.values_of_fixed h214 hInv hu hvals (hVN y.2) (hVa y y.2) ht₀T
  have hcomm_eq : ⁅t₀, (x : G)⁆ = ⁅t₀, (y : G)⁆ := by
    simp only [f] at hfxy
    by_cases hx1 : ⁅t₀, (x : G)⁆ = 1
    · have hy1 : ⁅t₀, (y : G)⁆ = 1 := by
        by_contra hy1
        simp [hx1, hy1] at hfxy
      rw [hx1, hy1]
    · have hy1 : ⁅t₀, (y : G)⁆ ≠ 1 := by
        intro hy1
        simp [hx1, hy1] at hfxy
      rw [hvx.resolve_left hx1, hvy.resolve_left hy1]
  set w : G := (x : G) * (y : G)⁻¹ with hwdef
  have hwV : w ∈ V := V.mul_mem x.2 (V.inv_mem y.2)
  have hw1 : w ≠ 1 := by
    intro h1
    apply hxy
    apply Subtype.ext
    rw [hwdef, mul_inv_eq_one] at h1
    exact h1
  have hwN : w ∈ cfgM T₁ (conjSubgroup a T₁) := hVN hwV
  have hxN : (x : G) ∈ cfgM T₁ (conjSubgroup a T₁) := hVN x.2
  have hlam : ⁅t₀, (x : G)⁆ ∈ normIn T T₁ := by
    rcases hvx with h0 | h0
    · rw [h0]
      exact (normIn T T₁).one_mem
    · rw [h0]
      exact hu
  have hcw : w * ⁅t₀, (x : G)⁆ = ⁅t₀, (x : G)⁆ * w := h.cfgM_comm_L h214 hInv hwN hlam
  have ht₀w : t₀ * w = w * t₀ := by
    have e1 : t₀ * (x : G) * t₀⁻¹ = ⁅t₀, (x : G)⁆ * x := by
      simp only [commutatorElement_def]
      group
    have e2 : t₀ * (y : G) * t₀⁻¹ = ⁅t₀, (x : G)⁆ * y := by
      rw [hcomm_eq]
      simp only [commutatorElement_def]
      group
    have e3 : t₀ * w * t₀⁻¹ = w := by
      calc t₀ * w * t₀⁻¹ = (t₀ * (x : G) * t₀⁻¹) * (t₀ * (y : G) * t₀⁻¹)⁻¹ := by
            rw [hwdef]
            group
        _ = (⁅t₀, (x : G)⁆ * x) * (⁅t₀, (x : G)⁆ * y)⁻¹ := by rw [e1, e2]
        _ = ⁅t₀, (x : G)⁆ * ((x : G) * (y : G)⁻¹) * ⁅t₀, (x : G)⁆⁻¹ := by group
        _ = w := by
          rw [← hwdef, ← hcw]
          group
    exact mul_inv_eq_iff_eq_mul.1 e3
  refine ⟨w, hwV, hw1, fun t ht => ?_⟩
  by_cases htL : t ∈ normIn T T₁
  · exact (h.cfgM_comm_L h214 hInv hwN htL).symm
  · have h1 : t * t₀ ∈ normIn T T₁ :=
      mul_mem_of_not_mem_of_card hLT h.hcard ht ht₀T htL ht₀L
    have h2 := h.cfgM_comm_L h214 hInv hwN h1
    have ht₀i : t₀⁻¹ = t₀ := elemAbelian_inv h.sec.cfg.wc.1 ht₀T
    have htt : t = (t * t₀) * t₀ := by
      have : t₀ * t₀ = 1 := elemAbelian_mul_self h.sec.cfg.wc.1 ht₀T
      rw [mul_assoc, this, mul_one]
    calc t * w = ((t * t₀) * t₀) * w := by rw [← htt]
      _ = (t * t₀) * (t₀ * w) := by group
      _ = (t * t₀) * (w * t₀) := by rw [ht₀w]
      _ = ((t * t₀) * w) * t₀ := by group
      _ = (w * (t * t₀)) * t₀ := by rw [h2]
      _ = w * ((t * t₀) * t₀) := by group
      _ = w * t := by rw [← htt]

end SecB6

end CFSG.CGT.Timmesfeld75
