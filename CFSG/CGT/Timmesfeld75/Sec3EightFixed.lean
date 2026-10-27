module

public import CFSG.CGT.Timmesfeld75.Sec3EightPair
public import CFSG.CGT.Timmesfeld75.L2FixedSylow

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] {T T₁ S : Subgroup G} {a b : G}

theorem eq_one_of_odd_orderOf_of_mem {S : Subgroup G} (hS : IsPGroup 2 S) {x : G} (hx : x ∈ S)
    (hodd : Odd (orderOf x)) : x = 1 := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf (p := 2)).1 hS ⟨x, hx⟩
  have hk' : orderOf x = 2 ^ k := by rw [← Subgroup.orderOf_mk x hx]; exact hk
  rw [hk'] at hodd
  have hk0 : k = 0 := by
    by_contra hk0
    exact (Nat.not_even_iff_odd.2 hodd) (Nat.even_pow.2 ⟨even_two, hk0⟩)
  exact orderOf_eq_one_iff.1 (by rw [hk', hk0, pow_zero])

theorem commutator_centralizes_aux {y f l m m' : G} (F1 : y * l * y⁻¹ = m * l)
    (F2 : y⁻¹ * l * y = m' * l) (F3 : y * m' * y⁻¹ = m') (F4 : f * m' * f⁻¹ = m')
    (F5 : f * l = l * f) (F6 : m' * m = 1) :
    (y * f * y⁻¹ * f⁻¹) * l * (y * f * y⁻¹ * f⁻¹)⁻¹ = l := by
  have F5' : f * l * f⁻¹ = l := by rw [F5]; group
  have F5'' : f⁻¹ * l * f = l := by rw [mul_assoc, ← F5, ← mul_assoc, inv_mul_cancel, one_mul]
  calc (y * f * y⁻¹ * f⁻¹) * l * (y * f * y⁻¹ * f⁻¹)⁻¹
      = y * (f * (y⁻¹ * (f⁻¹ * l * f) * y) * f⁻¹) * y⁻¹ := by group
    _ = y * (f * (y⁻¹ * l * y) * f⁻¹) * y⁻¹ := by rw [F5'']
    _ = y * (f * (m' * l) * f⁻¹) * y⁻¹ := by rw [F2]
    _ = y * ((f * m' * f⁻¹) * (f * l * f⁻¹)) * y⁻¹ := by group
    _ = y * (m' * l) * y⁻¹ := by rw [F4, F5']
    _ = (y * m' * y⁻¹) * (y * l * y⁻¹) := by group
    _ = m' * (m * l) := by rw [F3, F1]
    _ = (m' * m) * l := by group
    _ = l := by rw [F6, one_mul]

theorem mem_conjSubgroup_iff_exists {K : Subgroup G} {a f : G} :
    f ∈ conjSubgroup a K ↔ ∃ e ∈ K, f = a * e * a⁻¹ :=
  ⟨fun hf => ⟨a⁻¹ * f * a, mem_conjSubgroup.1 hf, by group⟩, fun ⟨e, he, hfe⟩ => by
    rw [hfe]
    exact conj_mem_conjSubgroup a he⟩

namespace Sec38Hyp

variable (h : Sec38Hyp T T₁ S a b)

include h

theorem conj_conj : conjSubgroup a (conjSubgroup a T₁) = T₁ := by
  rw [conjSubgroup_conjSubgroup, h.aa, conjSubgroup_one]

theorem sec₂ [Finite G] (h214 : Lemma214) (hInv : InvolutionClassInput) :
    Sec3 T₁ (conjSubgroup a T₁) :=
  Sec3.of_inputs h214 hInv h.sec.cfg.wc₁ h.conj_a_ne h.normIn_conj_ne_bot

theorem mem_normalizer_cfgM :
    a ∈ Subgroup.normalizer (cfgM T₁ (conjSubgroup a T₁) : Set G) := by
  apply mem_normalizer_of_conjSubgroup_eq
  rw [← cfgM_conj, h.conj_conj, cfgM_symm]

theorem mem_normalizer_sup :
    a ∈ Subgroup.normalizer ((T₁ ⊔ conjSubgroup a T₁ : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_conjSubgroup_eq, conjSubgroup_sup_eq_sup, h.conj_conj, sup_comm]

theorem normIn_le_cfgM [Finite G] (h214 : Lemma214) (hInv : InvolutionClassInput) :
    normIn T₁ T ≤ cfgM T₁ (conjSubgroup a T₁) := by
  intro e he
  by_contra heN
  have hS2 := h.sec₂ h214 hInv
  obtain ⟨y, hyX, hy⟩ := hS2.conj
  have heT₁ : e ∈ T₁ := (mem_normIn.1 he).1
  have haN := h.mem_normalizer_cfgM
  have hf : a * e * a⁻¹ ∈ conjSubgroup y T₁ := by
    rw [← hy, mem_conjSubgroup]
    have : a⁻¹ * (a * e * a⁻¹) * a = e := by group
    rw [this]
    exact heT₁
  have hfN : a * e * a⁻¹ ∉ cfgM T₁ (conjSubgroup a T₁) := by
    intro hfN
    apply heN
    have := conj_mem_of_mem_normalizer ((Subgroup.normalizer _).inv_mem haN) hfN
    have e2 : a⁻¹ * (a * e * a⁻¹) * a⁻¹⁻¹ = e := by group
    rwa [e2] at this
  have hne : conjSubgroup 1 T₁ ≠ conjSubgroup y T₁ := by
    rw [conjSubgroup_one, ← hy]
    exact h.conj_a_ne.symm
  have hodd := hS2.odd_orderOf_mul (Subgroup.one_mem _) hyX hne (a := e) (b := a * e * a⁻¹)
    (by rw [conjSubgroup_one]; exact heT₁) heN hf hfN
  have hSmem : e * (a * e * a⁻¹) ∈ S :=
    S.mul_mem (h.hL₁S he) (S.mul_mem (S.mul_mem h.haS (h.hL₁S he)) (S.inv_mem h.haS))
  have h1 := eq_one_of_odd_orderOf_of_mem h.two hSmem hodd
  have hfe : a * e * a⁻¹ = e⁻¹ := eq_inv_of_mul_eq_one_right h1
  have hfT₁ : a * e * a⁻¹ ∈ T₁ := by
    rw [hfe]
    exact T₁.inv_mem heT₁
  have hfP : a * e * a⁻¹ ∈ conjSubgroup a T₁ := conj_mem_conjSubgroup a heT₁
  have hbot := h.sec.cfg.wc₁.inf_conj_eq_bot h.conj_a_ne
  have hmem : a * e * a⁻¹ ∈ T₁ ⊓ conjSubgroup a T₁ := ⟨hfT₁, hfP⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  have he1 : e = 1 := by
    calc e = a⁻¹ * (a * e * a⁻¹) * a := by group
      _ = 1 := by rw [hmem]; group
  exact heN (he1 ▸ (cfgM T₁ (conjSubgroup a T₁)).one_mem)

theorem conj_conj_eq (K : Subgroup G) : conjSubgroup a (conjSubgroup a K) = K := by
  rw [conjSubgroup_conjSubgroup, h.aa, conjSubgroup_one]

theorem conj_normIn_le_cfgM [Finite G] (h214 : Lemma214) (hInv : InvolutionClassInput) :
    conjSubgroup a (normIn T₁ T) ≤ cfgM T₁ (conjSubgroup a T₁) := by
  have := conjSubgroup_mono (g := a) (h.normIn_le_cfgM h214 hInv)
  rwa [mem_normalizer_iff_conjSubgroup_eq.1 h.mem_normalizer_cfgM] at this

theorem commute_normIn_conj [Finite G] (h214 : Lemma214) (hInv : InvolutionClassInput) :
    ∀ x ∈ normIn T₁ T, ∀ y ∈ conjSubgroup a (normIn T₁ T), x * y = y * x :=
  fun _ hx _ hy => elemAbelian_mul_comm (h.sec₂ h214 hInv).cfg.isElemAbelian_cfgM
    (h.normIn_le_cfgM h214 hInv hx) (h.conj_normIn_le_cfgM h214 hInv hy)

theorem conj_normIn_comm_L {f l : G} (hf : f ∈ conjSubgroup a (normIn T₁ T))
    (hl : l ∈ normIn T T₁) : f * l = l * f := by
  obtain ⟨e, he, rfl⟩ := mem_conjSubgroup_iff_exists.1 hf
  have h1 : e * l = l * e := (h.sec.cfg.comm_L_L₁ hl he).symm
  have h2 : a * l = l * a := h.ha.transv.2.2.1 l hl
  have h3 : a⁻¹ * l * a = l := by rw [mul_assoc, ← h2, ← mul_assoc, inv_mul_cancel, one_mul]
  calc a * e * a⁻¹ * l = a * e * (a⁻¹ * l * a) * a⁻¹ := by group
    _ = a * (e * l) * a⁻¹ := by rw [h3]; group
    _ = a * (l * e) * a⁻¹ := by rw [h1]
    _ = (a * l) * e * a⁻¹ := by group
    _ = (l * a) * e * a⁻¹ := by rw [h2]
    _ = l * (a * e * a⁻¹) := by group

theorem mem_M_iff [Finite G] (h214 : Lemma214) (hInv : InvolutionClassInput) {m : G} :
    m ∈ normIn T₁ T ⊔ conjSubgroup a (normIn T₁ T) ↔
      ∃ e ∈ normIn T₁ T, ∃ f ∈ conjSubgroup a (normIn T₁ T), m = e * f := by
  have hnorm : normIn T₁ T ≤ Subgroup.normalizer (conjSubgroup a (normIn T₁ T) : Set G) := by
    apply le_normalizer_of_conjSubgroup_le
    intro g hg
    apply conjSubgroup_le_of_forall_mem
    intro x hx
    rw [mul_inv_eq_iff_eq_mul.2 (h.commute_normIn_conj h214 hInv g hg x hx)]
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

theorem mem_normalizer_M :
    a ∈ Subgroup.normalizer
      ((normIn T₁ T ⊔ conjSubgroup a (normIn T₁ T) : Subgroup G) : Set G) := by
  apply mem_normalizer_of_conjSubgroup_eq
  rw [conjSubgroup_sup_eq_sup, h.conj_conj_eq, sup_comm]

theorem commutator_mem_normIn [Finite G] (h214 : Lemma214) (hInv : InvolutionClassInput) {y f : G}
    (hy : y ∈ T₁) (hf : f ∈ conjSubgroup a (normIn T₁ T)) : ⁅y, f⁆ ∈ normIn T₁ T := by
  have hc := h.sec.cfg
  have hfN : f ∈ Subgroup.normalizer (T₁ : Set G) :=
    cfgM_le_normalizer T₁ (conjSubgroup a T₁) (h.conj_normIn_le_cfgM h214 hInv hf)
  have hT₁ : ⁅y, f⁆ ∈ T₁ := by
    have h1 := conj_mem_of_mem_normalizer hfN (T₁.inv_mem hy)
    have e : ⁅y, f⁆ = y * (f * y⁻¹ * f⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact T₁.mul_mem hy h1
  have hcent : ⁅y, f⁆ ∈ Subgroup.centralizer (normIn T T₁ : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hlam : ⁅y, l⁆ ∈ normIn T₁ T := hc.symm.comm_mem_normIn hy hl
    have hlam' : ⁅y⁻¹, l⁆ ∈ normIn T₁ T := hc.symm.comm_mem_normIn (T₁.inv_mem hy) hl
    have F1 : y * l * y⁻¹ = ⁅y, l⁆ * l := by
      simp only [commutatorElement_def]
      group
    have F2 : y⁻¹ * l * y = ⁅y⁻¹, l⁆ * l := by
      simp only [commutatorElement_def]
      group
    have F3 : y * ⁅y⁻¹, l⁆ * y⁻¹ = ⁅y⁻¹, l⁆ :=
      mul_inv_eq_iff_eq_mul.2 (elemAbelian_mul_comm hc.wc₁.1 hy (normIn_le _ _ hlam'))
    have F4 : f * ⁅y⁻¹, l⁆ * f⁻¹ = ⁅y⁻¹, l⁆ :=
      mul_inv_eq_iff_eq_mul.2 (h.commute_normIn_conj h214 hInv _ hlam' f hf).symm
    have F5 : f * l = l * f := h.conj_normIn_comm_L hf hl
    have F6 : ⁅y⁻¹, l⁆ * ⁅y, l⁆ = 1 := by
      have h1 : l = (⁅y⁻¹, l⁆ * ⁅y, l⁆) * l := by
        calc l = y * (y⁻¹ * l * y) * y⁻¹ := by group
          _ = y * (⁅y⁻¹, l⁆ * l) * y⁻¹ := by rw [F2]
          _ = (y * ⁅y⁻¹, l⁆ * y⁻¹) * (y * l * y⁻¹) := by group
          _ = ⁅y⁻¹, l⁆ * (⁅y, l⁆ * l) := by rw [F3, F1]
          _ = (⁅y⁻¹, l⁆ * ⁅y, l⁆) * l := by group
      exact mul_right_cancel (b := l) (by rw [one_mul]; exact h1.symm)
    exact (mul_inv_eq_iff_eq_mul.1 (commutator_centralizes_aux F1 F2 F3 F4 F5 F6)).symm
  rw [← hc.symm.inf_centralizer_normIn]
  exact ⟨hT₁, hcent⟩

theorem T₁_le_normalizer_M [Finite G] (h214 : Lemma214) (hInv : InvolutionClassInput) :
    T₁ ≤ Subgroup.normalizer
      ((normIn T₁ T ⊔ conjSubgroup a (normIn T₁ T) : Subgroup G) : Set G) := by
  apply le_normalizer_of_conjSubgroup_le
  intro y hy
  apply conjSubgroup_le_of_forall_mem
  intro m hm
  obtain ⟨e, he, f, hf, rfl⟩ := (h.mem_M_iff h214 hInv).1 hm
  have hyc := h.commutator_mem_normIn h214 hInv hy hf
  have hye : y * e * y⁻¹ = e :=
    mul_inv_eq_iff_eq_mul.2 (elemAbelian_mul_comm h.sec.cfg.wc₁.1 hy (normIn_le _ _ he))
  have hyf : y * f * y⁻¹ = ⁅y, f⁆ * f := by
    simp only [commutatorElement_def]
    group
  have key : y * (e * f) * y⁻¹ = (e * ⁅y, f⁆) * f := by
    calc y * (e * f) * y⁻¹ = (y * e * y⁻¹) * (y * f * y⁻¹) := by group
      _ = e * (⁅y, f⁆ * f) := by rw [hye, hyf]
      _ = (e * ⁅y, f⁆) * f := by group
  rw [key]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ((normIn T₁ T).mul_mem he hyc))
    (Subgroup.mem_sup_right hf)

theorem le_normalizer_M [Finite G] (h214 : Lemma214) (hInv : InvolutionClassInput) :
    T₁ ⊔ conjSubgroup a T₁ ≤ Subgroup.normalizer
      ((normIn T₁ T ⊔ conjSubgroup a (normIn T₁ T) : Subgroup G) : Set G) := by
  refine sup_le (h.T₁_le_normalizer_M h214 hInv) ?_
  apply le_normalizer_of_conjSubgroup_le
  intro y' hy'
  obtain ⟨y, hy, rfl⟩ := mem_conjSubgroup_iff_exists.1 hy'
  apply conjSubgroup_le_of_forall_mem
  intro m hm
  have haM := h.mem_normalizer_M
  have h1 := conj_mem_of_mem_normalizer ((Subgroup.normalizer _).inv_mem haM) hm
  have h2 := conj_mem_of_mem_normalizer (h.T₁_le_normalizer_M h214 hInv hy) h1
  have h3 := conj_mem_of_mem_normalizer haM h2
  have e : a * y * a⁻¹ * m * (a * y * a⁻¹)⁻¹ = a * (y * (a⁻¹ * m * a⁻¹⁻¹) * y⁻¹) * a⁻¹ := by
    group
  rw [e]
  exact h3

theorem commute_T_of_fixed [Finite G] (h214 : Lemma214) (hInv : InvolutionClassInput) {w : G}
    (hw : w ∈ normIn T₁ T ⊔ conjSubgroup a (normIn T₁ T)) (hwa : a * w * a⁻¹ = w) {t : G}
    (ht : t ∈ T) : w * t = t * w := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right h.aa
  obtain ⟨e, he, f, hf, rfl⟩ := (h.mem_M_iff h214 hInv).1 hw
  obtain ⟨e', he', rfl⟩ := mem_conjSubgroup_iff_exists.1 hf
  have h1 : a * (e * (a * e' * a⁻¹)) * a⁻¹ = (a * e * a⁻¹) * e' := by
    have haa' : a⁻¹ * a⁻¹ = 1 := by rw [← mul_inv_rev, h.aa, inv_one]
    calc a * (e * (a * e' * a⁻¹)) * a⁻¹
        = (a * e * a⁻¹) * ((a * a) * e' * (a⁻¹ * a⁻¹)) := by group
      _ = (a * e * a⁻¹) * e' := by rw [h.aa, haa', one_mul, mul_one]
  rw [h1] at hwa
  have hα : a * e * a⁻¹ ∈ conjSubgroup a (normIn T₁ T) := conj_mem_conjSubgroup a he
  have hcomm : e' * (a * e * a⁻¹) = (a * e * a⁻¹) * e' :=
    h.commute_normIn_conj h214 hInv e' he' _ hα
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
  have hbot := h.sec.cfg.wc₁.inf_conj_eq_bot h.conj_a_ne
  have hmem : e⁻¹ * e' ∈ T₁ ⊓ conjSubgroup a T₁ := ⟨hxT₁, hxP⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  have hee : e' = e := by
    calc e' = e * (e⁻¹ * e') := by group
      _ = e := by rw [hmem, mul_one]
  subst hee
  have hL := isElemAbelian_of_le h.sec.cfg.wc.1 (normIn_le T T₁)
  have := IsTransv.mul_mul_comm hL (h.sec.cfg.isTransv_of_mem_normIn he) h.ha.transv ht
  have e2 : e' * (a * e' * a⁻¹) = e' * a * (e' * a) := by rw [hai]; group
  rw [e2]
  exact this

theorem conj_eq_of_fixed [Finite G] (h214 : Lemma214) (hInv : InvolutionClassInput) {g : G}
    (hg : g ∈ T₁ ⊔ conjSubgroup a T₁)
    (hfix : ∀ u ∈ conjSubgroup g T₁, ∃ u' ∈ conjSubgroup g T₁,
      ∃ n ∈ cfgM T₁ (conjSubgroup a T₁), a * u * a⁻¹ = u' * n) :
    conjSubgroup g T₁ = T := by
  have hS2 := h.sec₂ h214 hInv
  have hwcU : IsWC (conjSubgroup g T₁) := h.sec.cfg.wc₁.conj g
  have hUX : conjSubgroup g T₁ ≤ T₁ ⊔ conjSubgroup a T₁ :=
    conjSubgroup_le_of_le_of_mem le_sup_left hg
  have hUp : IsPGroup 2 (conjSubgroup g T₁) :=
    isPGroup_two_of_isElemAbelian (isElemAbelian_conjSubgroup h.sec.cfg.wc₁.1 g)
  have hNp : IsPGroup 2 (cfgM T₁ (conjSubgroup a T₁)) :=
    isPGroup_two_of_isElemAbelian hS2.cfg.isElemAbelian_cfgM
  have hV : IsPGroup 2 ↥(conjSubgroup g T₁ ⊔ cfgM T₁ (conjSubgroup a T₁)) :=
    hUp.to_sup_of_normal_right' hNp (hUX.trans hS2.cfg.le_normalizer_cfgM)
  have haU : conjSubgroup a (conjSubgroup g T₁) = conjSubgroup g T₁ := by
    refine eq_of_conj_le_pGroup hwcU hV le_sup_left ?_
    refine conjSubgroup_le_of_forall_mem fun u hu => ?_
    obtain ⟨u', hu', n, hn, e⟩ := hfix u hu
    rw [e]
    exact (conjSubgroup g T₁ ⊔ cfgM T₁ (conjSubgroup a T₁)).mul_mem
      (Subgroup.mem_sup_left hu') (Subgroup.mem_sup_right hn)
  have hMg : conjSubgroup g (normIn T₁ T ⊔ conjSubgroup a (normIn T₁ T)) =
      normIn T₁ T ⊔ conjSubgroup a (normIn T₁ T) :=
    mem_normalizer_iff_conjSubgroup_eq.1 (h.le_normalizer_M h214 hInv hg)
  have hMa : conjSubgroup a (normIn T₁ T ⊔ conjSubgroup a (normIn T₁ T)) =
      normIn T₁ T ⊔ conjSubgroup a (normIn T₁ T) :=
    mem_normalizer_iff_conjSubgroup_eq.1 h.mem_normalizer_M
  have hWne : conjSubgroup g T₁ ⊓ (normIn T₁ T ⊔ conjSubgroup a (normIn T₁ T)) ≠ ⊥ := by
    intro h0
    have hle : conjSubgroup g (normIn T₁ T) ≤
        conjSubgroup g T₁ ⊓ (normIn T₁ T ⊔ conjSubgroup a (normIn T₁ T)) :=
      le_inf (conjSubgroup_mono (normIn_le T₁ T)) (by
        rw [← hMg]
        exact conjSubgroup_mono le_sup_left)
    rw [h0, le_bot_iff, conjSubgroup_eq_bot_iff] at hle
    exact h.sec.cfg.ne₁ hle
  have hWa : ∀ w ∈ conjSubgroup g T₁ ⊓ (normIn T₁ T ⊔ conjSubgroup a (normIn T₁ T)),
      a * w * a⁻¹ ∈ conjSubgroup g T₁ ⊓ (normIn T₁ T ⊔ conjSubgroup a (normIn T₁ T)) := by
    intro w hw
    refine ⟨?_, ?_⟩
    · rw [← haU]
      exact conj_mem_conjSubgroup a hw.1
    · rw [← hMa]
      exact conj_mem_conjSubgroup a hw.2
  have hWp : IsPGroup 2 ↥(conjSubgroup g T₁ ⊓
      (normIn T₁ T ⊔ conjSubgroup a (normIn T₁ T))) :=
    isPGroup_two_of_isElemAbelian (isElemAbelian_of_le
      (isElemAbelian_conjSubgroup h.sec.cfg.wc₁.1 g) inf_le_left)
  obtain ⟨w, hwW, hw1, hwa⟩ := exists_fixed_ne_one_of_involution hWne hWp h.aa hWa
  have hwT : ∀ t ∈ T, t * w = w * t := fun t ht =>
    (h.commute_T_of_fixed h214 hInv hwW.2 hwa ht).symm
  have hTN : T ≤ Subgroup.normalizer (conjSubgroup g T₁ : Set G) := fun t ht =>
    hwcU.centralizer_le_normalizer hwW.1 hw1 (Subgroup.mem_centralizer_singleton_iff.2 (hwT t ht))
  obtain ⟨x₀, -, hx₀⟩ := h.sec.conj
  have hconj : ∃ k : G, T = conjSubgroup k (conjSubgroup g T₁) :=
    ⟨(g * x₀)⁻¹, by
      rw [hx₀, conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup,
        show (g * x₀)⁻¹ * g * x₀ = 1 by group, conjSubgroup_one]⟩
  exact (eq_of_le_normalizer_of_isWC hwcU hconj hTN).symm

end Sec38Hyp

end CFSG.CGT.Timmesfeld75
