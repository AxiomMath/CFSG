module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalV
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalYPrelim

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup CFSG.Open
open CFSG.EvenSmallLie.UnitarySix.YamadaD (oTwo le_oTwo oTwo_le isPGroup_oTwo le_normalizer_oTwo)
open CFSG.LocalAnalysis.EvenBN.Common (CosetData)
open scoped commutatorElement Pointwise Matrix

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Transitive

variable {q : ℕ}

theorem Y_map_le_centralizer (h : Setup G L f t) (d : TrialityD4Data L q) :
    d.Y.map L.subtype ≤ centralizer ({t} : Set G) :=
  (map_subtype_le _).trans h.L_le_centralizer

theorem commutatorElement_t_mul_left (_h : Setup G L f t) {a b : G}
    (ha : a ∈ centralizer ({t} : Set G)) (hb : b ∈ centralizer ({t} : Set G)) :
    ⁅t * a, b⁆ = ⁅a, b⁆ := by
  have hab : ⁅a, b⁆ ∈ centralizer ({t} : Set G) := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have htb : t * b = b * t := (mem_centralizer_singleton_iff.1 hb).symm
  have htab : t * ⁅a, b⁆ = ⁅a, b⁆ * t := (mem_centralizer_singleton_iff.1 hab).symm
  calc ⁅t * a, b⁆ = t * (a * b * a⁻¹) * (t⁻¹ * b⁻¹) := by rw [commutatorElement_def]; group
    _ = t * (a * b * a⁻¹) * (b⁻¹ * t⁻¹) := by
      rw [show t⁻¹ * b⁻¹ = (b * t)⁻¹ by group, ← htb, mul_inv_rev]
    _ = t * ⁅a, b⁆ * t⁻¹ := by rw [commutatorElement_def]; group
    _ = ⁅a, b⁆ := by rw [htab, mul_inv_cancel_right]

theorem commutatorElement_t_mul_right (h : Setup G L f t) {a b : G}
    (ha : a ∈ centralizer ({t} : Set G)) (hb : b ∈ centralizer ({t} : Set G)) :
    ⁅a, t * b⁆ = ⁅a, b⁆ := by
  rw [← commutatorElement_inv, h.commutatorElement_t_mul_left hb ha, commutatorElement_inv]

theorem mem_tY_iff (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) {x : G} :
    x ∈ d.Y.map L.subtype ⊔ zpowers t ↔
      x ∈ yamadaR d t ∧ ∀ r ∈ yamadaR d t, ⁅x, r⁆ ∈ d.V.map L.subtype ⊔ zpowers t := by
  have hR := yamadaR_eq_of_eq d (h.centralizer_L_inf_of_data d)
  have hSL : d.S.map L.subtype ≤ L := map_subtype_le _
  have hYL : d.Y.map L.subtype ≤ L := map_subtype_le _
  have hRC := h.yamadaR_le_centralizer d
  have hred : ∀ {E : Subgroup L} {x : G}, x ∈ E.map L.subtype ⊔ zpowers t →
      ∃ x₀ ∈ E.map L.subtype, x = x₀ ∨ x = t * x₀ := by
    intro E x hx
    rcases (h.mem_sup_zpowers_iff (map_subtype_le _)).1 hx with h1 | h1
    · exact ⟨x, h1, Or.inl rfl⟩
    · exact ⟨t * x, h1, Or.inr (by rw [← mul_assoc, h.t_mul_t, one_mul])⟩
  have hcomm : ∀ {x₀ r₀ x r : G}, x₀ ∈ centralizer ({t} : Set G) →
      r₀ ∈ centralizer ({t} : Set G) → (x = x₀ ∨ x = t * x₀) → (r = r₀ ∨ r = t * r₀) →
        ⁅x, r⁆ = ⁅x₀, r₀⁆ := by
    intro x₀ r₀ x r hx₀ hr₀ hx hr
    have htr₀ : t * r₀ ∈ centralizer ({t} : Set G) := mul_mem h.t_mem_centralizer hr₀
    rcases hx with rfl | rfl <;> rcases hr with rfl | rfl
    · rfl
    · exact h.commutatorElement_t_mul_right hx₀ hr₀
    · exact h.commutatorElement_t_mul_left hx₀ hr₀
    · rw [h.commutatorElement_t_mul_left hx₀ htr₀, h.commutatorElement_t_mul_right hx₀ hr₀]
  have hYS : d.Y.map L.subtype ≤ d.S.map L.subtype := map_mono d.Y_le_S
  constructor
  · intro hx
    refine ⟨hR ▸ sup_le_sup_right hYS _ hx, fun r hr => ?_⟩
    obtain ⟨x₀, ⟨y, hy, rfl⟩, hxx⟩ := hred hx
    obtain ⟨r₀, ⟨s, hs, rfl⟩, hrr⟩ := hred (hR ▸ hr)
    rw [hcomm (h.L_le_centralizer y.2) (h.L_le_centralizer s.2) hxx hrr]
    have h1 : ⁅y, s⁆ ∈ d.V := commutatorElement_mem_comm.1
      (d.commutator_S_Y (commutator_mem_commutator hs hy))
    exact mem_sup_left ⟨_, h1, rfl⟩
  · rintro ⟨hx, hxr⟩
    obtain ⟨x₀, ⟨y, hy, rfl⟩, hxx⟩ := hred (hR ▸ hx)
    have hyY : y ∈ d.Y := by
      refine d.mem_Y_iff_forall.2 ⟨hy, fun s hs => ?_⟩
      have h1 := hxr s (hR ▸ mem_sup_left ⟨s, hs, rfl⟩)
      rw [hcomm (h.L_le_centralizer y.2) (h.L_le_centralizer s.2) hxx (Or.inl rfl)] at h1
      have h2 : ⁅(y : G), (s : G)⁆ ∈ L := by
        rw [commutatorElement_def]
        exact mul_mem (mul_mem (mul_mem y.2 s.2) (inv_mem y.2)) (inv_mem s.2)
      rcases (h.mem_sup_zpowers_iff (map_subtype_le _)).1 h1 with h3 | h3
      · rw [show ⁅(y : G), (s : G)⁆ = ((⁅y, s⁆ : L) : G) from
          (map_commutatorElement L.subtype y s).symm] at h3
        exact coe_mem_map_subtype_iff_D4.1 h3
      · exfalso
        refine h.t_not_mem_L ?_
        have := mul_mem (map_subtype_le _ h3) (inv_mem h2)
        rwa [mul_inv_cancel_right] at this
    rcases hxx with rfl | rfl
    · exact mem_sup_left ⟨y, hyY, rfl⟩
    · exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left ⟨y, hyY, rfl⟩)

theorem normalizer_yamadaR_le_tY (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    normalizer (yamadaR d t : Set G) ≤
      normalizer ((d.Y.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) := by
  intro n hn
  refine mem_normalizer_fintype fun x hx => ?_
  obtain ⟨hxR, hxc⟩ := (h.mem_tY_iff d).1 hx
  refine (h.mem_tY_iff d).2 ⟨(mem_normalizer_iff.1 hn x).1 hxR, fun r hr => ?_⟩
  have hr' : n⁻¹ * r * n ∈ yamadaR d t := by
    have := (mem_normalizer_iff.1 (inv_mem hn) r).1 hr
    rwa [inv_inv] at this
  have h1 := hxc _ hr'
  have h2 := (mem_normalizer_iff.1 (h.normalizer_yamadaR_le_tV d hn) _).1 h1
  rwa [show n * ⁅x, n⁻¹ * r * n⁆ * n⁻¹ = ⁅n * x * n⁻¹, r⁆ by
    simp only [commutatorElement_def]; group] at h2

omit [Finite G] in
theorem exists_leviLong_conj_eq (d : TrialityD4Data L q) {y : L} (hy : y ∈ d.Y) (hy1 : y ≠ 1) :
    ∃ l ∈ d.leviLong, l * d.x₆ 1 * l⁻¹ = y := by
  have hy' : y ∈ Set.range d.yv := by rw [d.range_yv]; exact hy
  obtain ⟨w, rfl⟩ := hy'
  have hw : w ≠ 0 := by
    rintro rfl
    apply hy1
    simp [TrialityD4Data.yv, d.x₅_zero, d.x₆_zero]
  have he : (![0, 1] : Fin 2 → d.Γ₀) ≠ 0 := fun e => one_ne_zero (congrFun e 1)
  obtain ⟨A, hA⟩ := CFSG.LocalAnalysis.EvenBN.LinearThree.Plane.exists_sl_smul he hw
  obtain ⟨l, hl⟩ := d.leviLongRep_bijective.2 A
  refine ⟨l, l.2, ?_⟩
  have h1 := d.leviLongRep_spec l ![0, 1]
  have hx : d.yv ![0, 1] = d.x₆ 1 := by simp [TrialityD4Data.yv, d.x₅_zero]
  rw [hx, hl] at h1
  rw [h1]
  exact congrArg d.yv hA

theorem conj_tY (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    {x | ∃ n ∈ normalizer ((d.Y.map L.subtype ⊔ zpowers t : Subgroup G) : Set G),
        n * t * n⁻¹ = x} =
      (fun y => t * y) '' ((d.Y.map L.subtype : Subgroup G) : Set G) := by
  have hYL : d.Y.map L.subtype ≤ L := map_subtype_le _
  ext x
  constructor
  · rintro ⟨n, hn, rfl⟩
    rcases (h.mem_sup_zpowers_iff hYL).1 ((mem_normalizer_iff.1 hn t).1
      (mem_sup_right (mem_zpowers t))) with h1 | h1
    · exact absurd (hYL h1) (h.conj_not_mem_L d n)
    · exact ⟨_, h1, by beta_reduce; rw [← mul_assoc, h.t_mul_t, one_mul]⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    by_cases hy1 : y = 1
    · exact ⟨1, one_mem _, by rw [hy1]; simp⟩
    obtain ⟨l, hl, hly⟩ := exists_leviLong_conj_eq d hy hy1
    have hmem : t * (d.x₆ 1 : G) ∈ (fun v => t * v) '' ((d.V.map L.subtype : Subgroup G) :
        Set G) := ⟨_, ⟨_, d.x₆_mem_V 1, rfl⟩, rfl⟩
    rw [← (h.conj_t_eq_tV d).1] at hmem
    obtain ⟨n, hn, hnt⟩ := hmem
    have hlH : (l : G) ∈ normalizer ((d.Y.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) := by
      have hlY : (l : G) ∈ normalizer ((d.Y.map L.subtype : Subgroup G) : Set G) := by
        refine mem_normalizer_fintype fun z hz => ?_
        obtain ⟨y', hy', rfl⟩ := hz
        exact ⟨l * y' * l⁻¹, (mem_normalizer_iff.1 (d.leviLong_le_normalizer_Y hl) y').1 hy',
          rfl⟩
      exact mem_normalizer_sup hlY (mem_normalizer_zpowers_of_comm_D4
        (mem_centralizer_singleton_iff.1 (h.L_le_centralizer l.2)))
    refine ⟨l * n, mul_mem hlH (h.normalizer_yamadaR_le_tY d hn), ?_⟩
    have htl : (l : G) * t = t * l := mem_centralizer_iff.1 h.htL _ l.2
    rw [show (l : G) * n * t * ((l : G) * n)⁻¹ = l * (n * t * n⁻¹) * (l : G)⁻¹ by group, hnt,
      ← mul_assoc, htl, mul_assoc, mul_assoc]
    congr 1
    rw [← hly]
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]
    group

theorem normalizer_tY_le_normalizer_Y (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    normalizer ((d.Y.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) ≤
      normalizer ((d.Y.map L.subtype : Subgroup G) : Set G) := by
  refine fun g hg => mem_normalizer_fintype fun y hy => ?_
  have hYL : d.Y.map L.subtype ≤ L := map_subtype_le _
  have h1 : g * y * g⁻¹ ∈ d.Y.map L.subtype ⊔ zpowers t :=
    (mem_normalizer_iff.1 hg y).1 (mem_sup_left hy)
  rcases (h.mem_sup_zpowers_iff hYL).1 h1 with h2 | h2
  · exact h2
  · exfalso
    have hmem : g * y * g⁻¹ ∈ (fun y => t * y) '' ((d.Y.map L.subtype : Subgroup G) : Set G) :=
      ⟨_, h2, by beta_reduce; rw [← mul_assoc, h.t_mul_t, one_mul]⟩
    rw [← h.conj_tY d] at hmem
    obtain ⟨n, -, hnt⟩ := hmem
    refine h.conj_not_mem_L d (g⁻¹ * n) ?_
    rw [show g⁻¹ * n * t * (g⁻¹ * n)⁻¹ = g⁻¹ * (n * t * n⁻¹) * g by group, hnt,
      show g⁻¹ * (g * y * g⁻¹) * g = y by group]
    exact hYL hy

omit [Finite G] in
theorem isElementaryAbelian_Y_map (d : TrialityD4Data L q) :
    IsElementaryAbelian 2 (d.Y.map L.subtype) := by
  refine isElementaryAbelian_two_of_forall (fun x hx y hy => ?_) (fun x hx => ?_)
  · obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact congrArg Subtype.val (d.mul_comm_of_mem_W (d.Y_le_W ha) (d.Y_le_W hb))
  · obtain ⟨a, ha, rfl⟩ := hx
    exact congrArg Subtype.val (d.mul_self_eq_one_of_mem_W (d.Y_le_W ha))

theorem cosetData_tY (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    CosetData (normalizer ((d.Y.map L.subtype ⊔ zpowers t : Subgroup G) : Set G))
      (d.Y.map L.subtype) t :=
  CosetData.of_le_normalizer h.t_mul_t (h.Y_map_le_centralizer d) (isElementaryAbelian_Y_map d)
    (h.normalizer_tY_le_normalizer_Y d) le_rfl

theorem centralizer_inf_normalizer_Y_le (_h : Setup G L f t) (d : TrialityD4Data L q) :
    centralizer ({t} : Set G) ⊓ normalizer ((d.Y.map L.subtype : Subgroup G) : Set G) ≤
      normalizer ((d.Y.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) := fun _ hx =>
  mem_normalizer_sup hx.2 (mem_normalizer_zpowers_of_comm_D4 (mem_centralizer_singleton_iff.1 hx.1))

theorem normalizer_tY_inf_centralizer (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    normalizer ((d.Y.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) ⊓
        centralizer ({t} : Set G) =
      centralizer ({t} : Set G) ⊓ normalizer ((d.Y.map L.subtype : Subgroup G) : Set G) :=
  le_antisymm (fun _ hx => ⟨hx.2, h.normalizer_tY_le_normalizer_Y d hx.1⟩)
    fun _ hx => ⟨h.centralizer_inf_normalizer_Y_le d hx, hx.1⟩

end Transitive

section Kernel

variable {q : ℕ}

theorem kernel_Y_le (_h : Setup G L f t) (d : TrialityD4Data L q) :
    normalizer ((d.Y.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) ⊓
        centralizer ((d.Y.map L.subtype : Subgroup G) : Set G) ⊓ centralizer ({t} : Set G) ≤
      centralizer ({t} : Set G) ⊓ normalizer ((d.Y.map L.subtype : Subgroup G) : Set G) :=
  fun _ hk => ⟨hk.2, Subgroup.centralizer_le_normalizer _ hk.1.2⟩

theorem normalizer_tY_le_normalizer_kernel_Y (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    normalizer ((d.Y.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) ≤
      normalizer ((normalizer ((d.Y.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) ⊓
        centralizer ((d.Y.map L.subtype : Subgroup G) : Set G) ⊓
          centralizer ({t} : Set G) : Subgroup G) : Set G) :=
  fun _ hg => mem_normalizer_fintype fun _ hk => (h.cosetData_tY d).conj_mem_kernel hg hk

theorem act_mem_Y (h : Setup G L f t) (d : TrialityD4Data L q) {x : G}
    (hxC : x ∈ centralizer ({t} : Set G))
    (hxY : x ∈ normalizer ((d.Y.map L.subtype : Subgroup G) : Set G)) :
    ∀ y ∈ d.Y, h.act ⟨x, hxC⟩ y ∈ d.Y := fun y hy => by
  rw [← h.conj_mem_map_iff hxC]
  exact (mem_normalizer_iff.1 hxY _).1 ⟨y, hy, rfl⟩

theorem centralizer_inf_normalizer_Y_le_normalizer_M (h : Setup G L f t) (d : TrialityD4Data L q) :
    centralizer ({t} : Set G) ⊓ normalizer ((d.Y.map L.subtype : Subgroup G) : Set G) ≤
      normalizer ((d.M.map L.subtype : Subgroup G) : Set G) := by
  rintro x ⟨hxC, hxY⟩
  obtain ⟨g, k, hgk⟩ := d.aut_eq (h.act ⟨x, hxC⟩)
  have hgM : g ∈ normalizer (d.M : Set L) := by
    rw [← d.normalizer_Y_eq_normalizer_W_and_M.2]
    exact d.mem_normalizer_Y_of_conj_mul_φ_pow fun y hy => hgk ▸ h.act_mem_Y d hxC hxY y hy
  refine mem_normalizer_fintype fun z hz => ?_
  obtain ⟨n, hn, rfl⟩ := hz
  rw [SetLike.mem_coe, Subgroup.coe_subtype, h.conj_mem_map_iff hxC, hgk, MulAut.mul_apply,
    MulAut.conj_apply]
  exact (mem_normalizer_iff.1 hgM _).1 (d.φ_pow_mem_M k hn)

theorem le_tM_of_isPGroup (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) {P : Subgroup G}
    (hPC : P ≤ centralizer ({t} : Set G) ⊓ normalizer ((d.Y.map L.subtype : Subgroup G) : Set G))
    (hN : centralizer ({t} : Set G) ⊓ normalizer ((d.Y.map L.subtype : Subgroup G) : Set G) ≤
      normalizer (P : Set G))
    (hP : IsPGroup 2 P) : P ≤ d.M.map L.subtype ⊔ zpowers t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNL : ∀ l : L, l ∈ normalizer (d.Y : Set L) →
      (l : G) ∈ centralizer ({t} : Set G) ⊓
        normalizer ((d.Y.map L.subtype : Subgroup G) : Set G) := by
    intro l hl
    refine ⟨h.L_le_centralizer l.2, mem_normalizer_fintype fun z hz => ?_⟩
    obtain ⟨y, hy, rfl⟩ := hz
    exact ⟨l * y * l⁻¹, (mem_normalizer_iff.1 hl y).1 hy, rfl⟩
  set Q : Subgroup L := P.comap L.subtype with hQ
  have hQ2 : IsPGroup 2 Q := hP.comap_of_injective L.subtype L.subtype_injective
  have hQnorm : ∀ l : L, l ∈ normalizer (d.Y : Set L) → l ∈ normalizer (Q : Set L) := by
    intro l hl
    have hlP := hN (hNL l hl)
    rw [mem_normalizer_iff]
    intro y
    change (y : G) ∈ P ↔ ((l * y * l⁻¹ : L) : G) ∈ P
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact mem_normalizer_iff.1 hlP y
  have hQM : Q ≤ d.M := d.le_M_of_isPGroup hQ2
    (fun s hs => hQnorm s (d.S_le_normalizer_Y hs))
    (hQnorm d.v (d.leviLong_le_normalizer_Y d.v_mem_leviLong))
  have hJY : d.J₂ ≤ normalizer (d.Y : Set L) := inf_le_left.trans d.J_le_normalizer_Y
  intro x hx
  obtain ⟨hxC, hxY⟩ := hPC hx
  have hcomm : ∀ y : L, y ∈ normalizer (d.Y : Set L) → h.act ⟨x, hxC⟩ y * y⁻¹ ∈ d.M := by
    intro y hy
    apply hQM
    change ((h.act ⟨x, hxC⟩ y * y⁻¹ : L) : G) ∈ P
    rw [Subgroup.coe_mul, h.coe_act_apply, Subgroup.coe_inv,
      show x * (y : G) * x⁻¹ * (y : G)⁻¹ = x * ((y : G) * x⁻¹ * (y : G)⁻¹) by group]
    exact mul_mem hx ((mem_normalizer_iff.1 (hN (hNL y hy)) _).1 (inv_mem hx))
  obtain ⟨m, hm, j, hj, hmj⟩ := d.eq_conj_of_trivial_mod_M (h.act_mem_Y d hxC hxY)
    (fun y hy => hcomm y (d.leviLong_le_normalizer_Y hy)) (fun y hy => hcomm y (hJY hy))
  obtain ⟨c, hc, rfl⟩ := h.exists_mul_zpowers_of_act_eq_conj d hxC hmj
  obtain ⟨a, ha⟩ := hP ⟨_, hx⟩
  have hc2 : c * c = 1 := by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hc
    rcases h.zpow_eq_one_or_eq k with hk | hk <;> rw [hk]
    · exact mul_one 1
    · exact h.t_mul_t
  have hcomm' : Commute ((m * j : L) : G) c := by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hc
    exact Commute.zpow_right (mem_centralizer_iff.1 h.htL _ (m * j).2) k
  have hmj1 : (m * j) ^ 2 ^ (a + 1) = 1 := by
    have h1 := congrArg Subtype.val ha
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at h1
    have h2 : ((m * j : L) : G) ^ 2 ^ (a + 1) * c ^ 2 ^ (a + 1) = 1 := by
      rw [← hcomm'.mul_pow, pow_succ, pow_mul, h1, one_pow]
    have hc' : c ^ 2 ^ (a + 1) = 1 := by rw [pow_succ', pow_mul, sq, hc2, one_pow]
    rw [hc', mul_one] at h2
    exact Subtype.ext (by rw [SubmonoidClass.coe_pow, h2, OneMemClass.coe_one])
  rw [d.eq_one_of_mul_pow_eq_one_M hm hj hmj1, mul_one]
  exact mul_mem (mem_sup_left ⟨m, hm, rfl⟩) (mem_sup_right hc)

theorem tM_le_kernel_Y (h : Setup G L f t) (d : TrialityD4Data L q) :
    d.M.map L.subtype ⊔ zpowers t ≤
      normalizer ((d.Y.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) ⊓
        centralizer ((d.Y.map L.subtype : Subgroup G) : Set G) ⊓ centralizer ({t} : Set G) := by
  have hMY : d.M.map L.subtype ≤ centralizer ((d.Y.map L.subtype : Subgroup G) : Set G) := by
    rintro _ ⟨m, hm, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨y, hy, rfl⟩
    exact congrArg Subtype.val (mem_centralizer_iff.1 (d.M_le_centralizer_Y hm) y hy)
  have htY : t ∈ centralizer ((d.Y.map L.subtype : Subgroup G) : Set G) :=
    mem_centralizer_iff.2 fun y hy =>
      mem_centralizer_singleton_iff.1 (h.L_le_centralizer (map_subtype_le _ hy))
  have hle : d.M.map L.subtype ⊔ zpowers t ≤
      centralizer ((d.Y.map L.subtype : Subgroup G) : Set G) :=
    sup_le hMY ((zpowers_le).2 htY)
  have hleC : d.M.map L.subtype ⊔ zpowers t ≤ centralizer ({t} : Set G) :=
    sup_le ((map_subtype_le _).trans h.L_le_centralizer) ((zpowers_le).2 h.t_mem_centralizer)
  intro x hx
  exact ⟨⟨h.centralizer_inf_normalizer_Y_le d ⟨hleC hx,
    Subgroup.centralizer_le_normalizer _ (hle hx)⟩, hle hx⟩, hleC hx⟩

theorem isPGroup_tM (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    IsPGroup 2 (d.M.map L.subtype ⊔ zpowers t : Subgroup G) := by
  refine (h.isSylowOf_yamadaR d).isPGroup.to_le ?_
  rw [yamadaR, h.centralizer_L_inf_of_data d]
  exact sup_le_sup_right (map_mono d.M_le_S) _

theorem oTwo_kernel_Y (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    oTwo (normalizer ((d.Y.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) ⊓
      centralizer ((d.Y.map L.subtype : Subgroup G) : Set G) ⊓ centralizer ({t} : Set G)) =
        d.M.map L.subtype ⊔ zpowers t := by
  have hHo : normalizer ((d.Y.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) ≤
      normalizer ((oTwo (normalizer ((d.Y.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) ⊓
        centralizer ((d.Y.map L.subtype : Subgroup G) : Set G) ⊓
          centralizer ({t} : Set G)) : Subgroup G) : Set G) :=
    fun _ hg => mem_normalizer_fintype fun _ hy =>
      Common.conj_mem_oTwo_of_mem_normalizer (h.normalizer_tY_le_normalizer_kernel_Y d hg) hy
  apply le_antisymm
  · exact h.le_tM_of_isPGroup d ((oTwo_le _).trans (h.kernel_Y_le d))
      ((h.centralizer_inf_normalizer_Y_le d).trans hHo) (isPGroup_oTwo _)
  · refine le_oTwo (h.tM_le_kernel_Y d) (fun k hk => ?_) (h.isPGroup_tM d)
    have hk' := h.kernel_Y_le d hk
    exact mem_normalizer_sup (h.centralizer_inf_normalizer_Y_le_normalizer_M d hk')
      (mem_normalizer_zpowers_of_comm_D4 (mem_centralizer_singleton_iff.1 hk'.1))

theorem normalizer_tY_le_normalizer_tM (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    normalizer ((d.Y.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) ≤
      normalizer ((d.M.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) := by
  rw [← h.oTwo_kernel_Y d]
  exact fun _ hg => mem_normalizer_fintype fun _ hy =>
    Common.conj_mem_oTwo_of_mem_normalizer (h.normalizer_tY_le_normalizer_kernel_Y d hg) hy

end Kernel

section SL

variable {q : ℕ}

omit [Finite G] in
theorem exists_mulEquiv_Y (d : TrialityD4Data L q) :
    ∃ ι : Multiplicative (Fin 2 → d.Γ₀) ≃* (d.Y.map L.subtype : Subgroup G),
      ∀ w : Fin 2 → d.Γ₀, (ι (Multiplicative.ofAdd w) : G) = (d.yv w : G) := by
  let φ : Multiplicative (Fin 2 → d.Γ₀) →* (d.Y.map L.subtype : Subgroup G) :=
    { toFun := fun w => ⟨(d.yv (Multiplicative.toAdd w) : G), ⟨_, d.yv_mem_Y _, rfl⟩⟩
      map_one' := Subtype.ext (by
        change ((d.yv 0 : L) : G) = 1
        rw [show d.yv 0 = 1 by simp [TrialityD4Data.yv, d.x₅_zero, d.x₆_zero]]
        rfl)
      map_mul' := fun a b => Subtype.ext (by
        change ((d.yv (Multiplicative.toAdd a + Multiplicative.toAdd b) : L) : G) = _
        rw [d.yv_add]
        rfl) }
  have hinj : Function.Injective φ := fun a b hab => by
    have h1 := congrArg Subtype.val hab
    change ((d.yv (Multiplicative.toAdd a) : L) : G) = d.yv (Multiplicative.toAdd b) at h1
    exact Multiplicative.toAdd.injective (d.yv_injective (Subtype.ext h1))
  have hsurj : Function.Surjective φ := by
    rintro ⟨_, ⟨y, hy, rfl⟩⟩
    have hy' : y ∈ Set.range d.yv := by rw [d.range_yv]; exact hy
    obtain ⟨w, rfl⟩ := hy'
    exact ⟨Multiplicative.ofAdd w, rfl⟩
  exact ⟨MulEquiv.ofBijective φ ⟨hinj, hsurj⟩, fun w => rfl⟩

theorem exists_leviLong_of_conj (h : Setup G L f t) (d : TrialityD4Data L q) {x : G}
    (hx : x ∈ centralizer ({t} : Set G) ⊓ normalizer ((d.Y.map L.subtype : Subgroup G) : Set G))
    {g : G} (hg : g ∈ d.leviLong.map L.subtype) :
    ∃ g' ∈ d.leviLong.map L.subtype, ∀ w ∈ d.Y.map L.subtype,
      x * g * x⁻¹ * w * (x * g * x⁻¹)⁻¹ = g' * w * g'⁻¹ := by
  obtain ⟨hxC, hxY⟩ := hx
  obtain ⟨l, k, hlk⟩ := d.aut_eq (h.act ⟨x, hxC⟩)
  have hlY : l ∈ normalizer (d.Y : Set L) :=
    d.mem_normalizer_Y_of_conj_mul_φ_pow fun y hy => hlk ▸ h.act_mem_Y d hxC hxY y hy
  obtain ⟨m, hm, s, hs, j, hj, rfl⟩ := d.exists_mul_of_mem_normalizer_Y hlY
  obtain ⟨g₀, hg₀, rfl⟩ := hg
  have hφ := d.φ_pow_mem_leviLong k hg₀
  refine ⟨((s * (d.φ ^ k) g₀ * s⁻¹ : L) : G),
    ⟨_, mul_mem (mul_mem hs hφ) (inv_mem hs), rfl⟩, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  have hjc : j * (d.φ ^ k) g₀ * j⁻¹ = (d.φ ^ k) g₀ := by
    rw [← mem_centralizer_iff.1 (d.yamada_three_eight_five.2.2.2.2.1 hj) _ hφ,
      mul_inv_cancel_right]
  have hxg : x * (L.subtype g₀) * x⁻¹ = ((m * (s * (d.φ ^ k) g₀ * s⁻¹) * m⁻¹ : L) : G) := by
    rw [Subgroup.coe_subtype, ← h.coe_act_apply ⟨x, hxC⟩ g₀, hlk, MulAut.mul_apply,
      MulAut.conj_apply,
      show m * s * j * (d.φ ^ k) g₀ * (m * s * j)⁻¹ =
        m * (s * (j * (d.φ ^ k) g₀ * j⁻¹) * s⁻¹) * m⁻¹ by group, hjc]
  set z := s * (d.φ ^ k) g₀ * s⁻¹
  have hzy : z * y * z⁻¹ ∈ d.Y := by
    have hzN : z ∈ normalizer (d.Y : Set L) :=
      d.leviLong_le_normalizer_Y (mul_mem (mul_mem hs hφ) (inv_mem hs))
    exact (mem_normalizer_iff.1 hzN y).1 hy
  have hmc : ∀ y' ∈ d.Y, m * y' * m⁻¹ = y' := fun y' hy' => by
    rw [← mem_centralizer_iff.1 (d.M_le_centralizer_Y hm) y' hy', mul_inv_cancel_right]
  have h1 : m⁻¹ * y * m = y := by
    rw [mul_assoc, mem_centralizer_iff.1 (d.M_le_centralizer_Y hm) y hy, inv_mul_cancel_left]
  have key : (m * z * m⁻¹) * y * (m * z * m⁻¹)⁻¹ = z * y * z⁻¹ := by
    calc (m * z * m⁻¹) * y * (m * z * m⁻¹)⁻¹ = m * (z * (m⁻¹ * y * m) * z⁻¹) * m⁻¹ := by group
      _ = m * (z * y * z⁻¹) * m⁻¹ := by rw [h1]
      _ = z * y * z⁻¹ := hmc _ hzy
  rw [hxg]
  have := congrArg Subtype.val key
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
  exact this

end SL

section Core

theorem commutator_leviLong_kernel_mem (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    {a : G} (ha : a ∈ d.leviLong.map L.subtype) {k : G}
    (hk : k ∈ normalizer ((d.Y.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) ⊓
      centralizer ((d.Y.map L.subtype : Subgroup G) : Set G) ⊓ centralizer ({t} : Set G)) :
    a * k * a⁻¹ * k⁻¹ ∈ d.M.map L.subtype ⊔ zpowers t := by
  obtain ⟨⟨-, hkY⟩, hkC⟩ := hk
  obtain ⟨a₀, ha₀, rfl⟩ := ha
  have haC : (a₀ : G) ∈ centralizer ({t} : Set G) := h.L_le_centralizer a₀.2
  obtain ⟨g, m', hgm⟩ := d.aut_eq (h.act ⟨k, hkC⟩)
  have hcent : ∀ y ∈ d.Y, (MulAut.conj g * d.φ ^ m') y = y := by
    intro y hy
    rw [← hgm]
    refine Subtype.ext ?_
    rw [h.coe_act_apply]
    change k * (y : G) * k⁻¹ = y
    have hyk : (y : G) * k = k * y := mem_centralizer_iff.1 hkY _ ⟨y, hy, rfl⟩
    rw [← hyk, mul_inv_cancel_right]
  obtain ⟨m, hm, j, hj, rfl, -, hfix⟩ := d.exists_of_centralizes_Y hcent
  have hφa : (d.φ ^ m') a₀⁻¹ = a₀⁻¹ := d.φ_pow_apply_of_mem_leviLong hfix (inv_mem ha₀)
  have hja : j * a₀⁻¹ * j⁻¹ = a₀⁻¹ := by
    rw [← mem_centralizer_iff.1 (d.yamada_three_eight_five.2.2.2.2.1 hj) _ (inv_mem ha₀),
      mul_inv_cancel_right]
  have hcomm : a₀ * (m * j) * a₀⁻¹ * (m * j)⁻¹ ∈ d.M := by
    have e1 : a₀ * (m * j) * a₀⁻¹ * (m * j)⁻¹ = a₀ * m * (j * a₀⁻¹ * j⁻¹) * m⁻¹ := by group
    rw [e1, hja, show a₀ * m * a₀⁻¹ * m⁻¹ = (a₀ * m * a₀⁻¹) * m⁻¹ by group]
    exact mul_mem ((mem_normalizer_iff.1 (d.leviLong_le_normalizer_M ha₀) m).1 hm) (inv_mem hm)
  have hact : h.act (⟨a₀, haC⟩ * ⟨k, hkC⟩ * ⟨a₀, haC⟩⁻¹ * ⟨k, hkC⟩⁻¹) =
      MulAut.conj (a₀ * (m * j) * a₀⁻¹ * (m * j)⁻¹) := by
    have e2 : ∀ β : MulAut L, MulAut.conj a₀ * β * (MulAut.conj a₀)⁻¹ * β⁻¹ =
        MulAut.conj (a₀ * β a₀⁻¹) := by
      intro β
      rw [map_mul, ← mulAut_mul_conj_mul_inv β, map_inv]
      group
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hgm,
      show (⟨(a₀ : G), haC⟩ : centralizer ({t} : Set G)) = ⟨a₀, h.L_le_centralizer a₀.2⟩ from rfl,
      h.act_of_mem_L a₀.2, Subtype.coe_eta, e2, MulAut.mul_apply, hφa, MulAut.conj_apply]
    congr 1
    group
  obtain ⟨c, hc, he⟩ := h.exists_mul_zpowers_of_act_eq_conj d
    (mul_mem (mul_mem (mul_mem haC hkC) (inv_mem haC)) (inv_mem hkC)) hact
  rw [Subgroup.coe_subtype, he]
  exact mul_mem (mem_sup_left ⟨_, hcomm, rfl⟩) (mem_sup_right hc)

theorem two_core_L₂ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    yamadaL₂ d t ≤ centralizer ((d.Y.map L.subtype : Subgroup G) : Set G) ∧
      yamadaL₂ d t ⊓ centralizer ({t} : Set G) = d.M.map L.subtype ⊔ zpowers t ∧
      (∀ y ∈ d.Y.map L.subtype, ∃ x ∈ yamadaL₂ d t, x⁻¹ * t * x = t * y) ∧
      ∀ g ∈ normalizer ((d.Y.map L.subtype ⊔ zpowers t : Subgroup G) : Set G),
        ∃ c ∈ centralizer ({t} : Set G) ⊓ normalizer ((d.Y.map L.subtype : Subgroup G) : Set G),
          ∃ x ∈ yamadaL₂ d t, g = c * x := by
  have := Fintype.ofFinite d.Γ₀
  obtain ⟨ι, hι⟩ := exists_mulEquiv_Y (G := G) d
  have hc := h.cosetData_tY d
  have htr : ∀ y ∈ d.Y.map L.subtype, ∃ g ∈ normalizer
      ((d.Y.map L.subtype ⊔ zpowers t : Subgroup G) : Set G), g⁻¹ * t * g = t * y := by
    intro y hy
    have hmem : t * y ∈ (fun y => t * y) '' ((d.Y.map L.subtype : Subgroup G) : Set G) :=
      ⟨y, hy, rfl⟩
    rw [← h.conj_tY d] at hmem
    obtain ⟨n, hn, hnt⟩ := hmem
    exact ⟨n⁻¹, inv_mem hn, by rw [inv_inv]; exact hnt⟩
  have hA : d.leviLong.map L.subtype ≤
      normalizer ((d.Y.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) ⊓
        centralizer ({t} : Set G) := by
    rintro _ ⟨a, ha, rfl⟩
    have haC : (a : G) ∈ centralizer ({t} : Set G) := h.L_le_centralizer a.2
    have haY : (a : G) ∈ normalizer ((d.Y.map L.subtype : Subgroup G) : Set G) := by
      refine mem_normalizer_fintype fun z hz => ?_
      obtain ⟨y, hy, rfl⟩ := hz
      exact ⟨a * y * a⁻¹, (mem_normalizer_iff.1 (d.leviLong_le_normalizer_Y ha) y).1 hy, rfl⟩
    exact ⟨h.centralizer_inf_normalizer_Y_le d ⟨haC, haY⟩, haC⟩
  have hnat : ∀ g ∈ d.leviLong.map L.subtype, ∃ A : Matrix.SpecialLinearGroup (Fin 2) d.Γ₀,
      ∀ w : Fin 2 → d.Γ₀, g * (ι (Multiplicative.ofAdd w) : G) * g⁻¹ =
        ι (Multiplicative.ofAdd ((A : Matrix (Fin 2) (Fin 2) d.Γ₀) *ᵥ w)) := by
    rintro _ ⟨a, ha, rfl⟩
    refine ⟨d.leviLongRep ⟨a, ha⟩, fun w => ?_⟩
    rw [hι, hι]
    have h1 := d.leviLongRep_spec ⟨a, ha⟩ w
    have h2 := congrArg Subtype.val h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2
    exact h2
  have hsurj : ∀ A : Matrix.SpecialLinearGroup (Fin 2) d.Γ₀, ∃ g ∈ d.leviLong.map L.subtype,
      ∀ w : Fin 2 → d.Γ₀, g * (ι (Multiplicative.ofAdd w) : G) * g⁻¹ =
        ι (Multiplicative.ofAdd ((A : Matrix (Fin 2) (Fin 2) d.Γ₀) *ᵥ w)) := by
    intro A
    obtain ⟨⟨a, ha⟩, hA'⟩ := d.leviLongRep_bijective.2 A
    refine ⟨a, ⟨a, ha, rfl⟩, fun w => ?_⟩
    rw [hι, hι, ← hA']
    have h1 := d.leviLongRep_spec ⟨a, ha⟩ w
    have h2 := congrArg Subtype.val h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2
    exact h2
  have hAn : ∀ x ∈ normalizer ((d.Y.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) ⊓
      centralizer ({t} : Set G), ∀ g ∈ d.leviLong.map L.subtype,
        ∃ g' ∈ d.leviLong.map L.subtype, ∀ w ∈ d.Y.map L.subtype,
          x * g * x⁻¹ * w * (x * g * x⁻¹)⁻¹ = g' * w * g'⁻¹ := by
    intro x hx g hg
    rw [h.normalizer_tY_inf_centralizer d] at hx
    exact h.exists_leviLong_of_conj d hx hg
  have hmax : ∀ R : Subgroup G,
      R ≤ normalizer ((d.Y.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) ⊓
        centralizer ({t} : Set G) →
      normalizer ((d.Y.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) ⊓
        centralizer ({t} : Set G) ≤ normalizer (R : Set G) → IsPGroup 2 R →
          R ≤ d.M.map L.subtype ⊔ zpowers t := by
    intro R hR hN hp
    rw [h.normalizer_tY_inf_centralizer d] at hR hN
    exact h.le_tM_of_isPGroup d hR hN hp
  obtain ⟨h1, h2, h3, h4⟩ := hc.sl_two_core ι htr hA hnat hsurj hAn (h.isPGroup_tM d)
    (h.tM_le_kernel_Y d) (h.normalizer_tY_le_normalizer_tM d) hmax
    (fun a ha k hk => h.commutator_leviLong_kernel_mem d ha hk)
  rw [yamadaL₂, pCoreOf_two_eq_oTwo_D4]
  refine ⟨h1, h2, h3, fun g hg => ?_⟩
  obtain ⟨c, hc, x, hx, rfl⟩ := h4 g hg
  rw [h.normalizer_tY_inf_centralizer d] at hc
  exact ⟨c, hc, x, hx, rfl⟩

theorem center_map_sup_zpowers (h : Setup G L f t) (E : Subgroup L) :
    (E.map L.subtype ⊔ zpowers t) ⊓ centralizer ((E.map L.subtype ⊔ zpowers t : Subgroup G) :
      Set G) = (E ⊓ centralizer (E : Set L)).map L.subtype ⊔ zpowers t := by
  have hEL : E.map L.subtype ≤ L := map_subtype_le _
  have hZ : ∀ z : L, (z : G) ∈ centralizer ((E.map L.subtype : Subgroup G) : Set G) ↔
      z ∈ centralizer (E : Set L) := by
    intro z
    rw [mem_centralizer_iff, mem_centralizer_iff]
    constructor
    · intro hz e he
      exact Subtype.ext (hz _ ⟨e, he, rfl⟩)
    · rintro hz _ ⟨e, he, rfl⟩
      exact congrArg Subtype.val (hz e he)
  apply le_antisymm
  · rintro z ⟨hzB, hzc⟩
    have hzE : ∀ x ∈ E.map L.subtype, x * z = z * x := fun x hx =>
      mem_centralizer_iff.1 hzc x (mem_sup_left hx)
    rcases (h.mem_sup_zpowers_iff hEL).1 hzB with hz | hz
    · obtain ⟨z₀, hz₀, rfl⟩ := hz
      exact mem_sup_left ⟨z₀, ⟨hz₀, (hZ z₀).1 (mem_centralizer_iff.2 hzE)⟩, rfl⟩
    · obtain ⟨z₀, hz₀, hz₀e⟩ := hz
      have h1 : (z₀ : G) ∈ centralizer ((E.map L.subtype : Subgroup G) : Set G) := by
        rw [Subgroup.coe_subtype] at hz₀e
        rw [hz₀e, mem_centralizer_iff]
        intro x hx
        have hxt : x * t = t * x :=
          mem_centralizer_singleton_iff.1 (h.L_le_centralizer (hEL hx))
        calc x * (t * z) = t * (x * z) := by rw [← mul_assoc, hxt, mul_assoc]
          _ = t * (z * x) := by rw [hzE x hx]
          _ = t * z * x := by group
      rw [show z = t * (t * z) by rw [← mul_assoc, h.t_mul_t, one_mul]]
      refine mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left ⟨z₀, ⟨hz₀, (hZ z₀).1 h1⟩, ?_⟩)
      rw [Subgroup.coe_subtype] at hz₀e ⊢
      exact hz₀e
  · have htZ : t ∈ centralizer ((E.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) := by
      rw [mem_centralizer_iff]
      intro b hb
      have hbC : b ∈ centralizer ({t} : Set G) :=
        sup_le ((map_subtype_le _).trans h.L_le_centralizer)
          ((zpowers_le).2 h.t_mem_centralizer) hb
      exact (mem_centralizer_singleton_iff.1 hbC)
    refine le_inf (sup_le_sup_right (map_mono inf_le_left) _) (sup_le ?_ ((zpowers_le).2 htZ))
    rintro _ ⟨z, ⟨hzE, hzc⟩, rfl⟩
    rw [Subgroup.coe_subtype, mem_centralizer_iff]
    intro b hb
    rcases (h.mem_sup_zpowers_iff hEL).1 hb with hb' | hb'
    · exact mem_centralizer_iff.1 ((hZ z).2 hzc) b hb'
    · have h1 := mem_centralizer_iff.1 ((hZ z).2 hzc) _ hb'
      have hzt : (z : G) * t = t * z := mem_centralizer_iff.1 h.htL _ z.2
      calc b * z = t * (t * b) * z := by rw [← mul_assoc, h.t_mul_t, one_mul]
        _ = t * (z * (t * b)) := by rw [mul_assoc, h1]
        _ = z * b := by rw [← mul_assoc, ← hzt, mul_assoc, ← mul_assoc t, h.t_mul_t, one_mul]

theorem yamada_5_3_2 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    normalizer ((d.Y.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) =
        normalizer ((d.M.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) ∧
      normalizer ((d.Y.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) =
        yamadaL₂ d t ⊔ (centralizer ({t} : Set G) ⊓
          normalizer ((d.Y.map L.subtype : Subgroup G) : Set G)) ∧
      ((normalizer ((d.Y.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) : Subgroup G) :
          Set G) = (yamadaL₂ d t : Set G) * ((centralizer ({t} : Set G) ⊓
            normalizer ((d.Y.map L.subtype : Subgroup G) : Set G) : Subgroup G) : Set G) ∧
      normalizer ((d.Y.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) ≤
        normalizer ((d.Y.map L.subtype : Subgroup G) : Set G) ∧
      yamadaL₂ d t ⊓ centralizer ({t} : Set G) = d.M.map L.subtype ⊔ zpowers t ∧
      {x | ∃ c ∈ yamadaL₂ d t, c * t * c⁻¹ = x} =
        (fun y => t * y) '' ((d.Y.map L.subtype : Subgroup G) : Set G) ∧
      yamadaL₂ d t ≤ centralizer ((d.Y.map L.subtype : Subgroup G) : Set G) := by
  obtain ⟨h1, h2, h3, h4⟩ := h.two_core_L₂ d
  have hZ : (d.M.map L.subtype ⊔ zpowers t) ⊓ centralizer
      ((d.M.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) = d.Y.map L.subtype ⊔ zpowers t := by
    rw [h.center_map_sup_zpowers d.M, d.M_inf_centralizer_M]
  refine ⟨le_antisymm (h.normalizer_tY_le_normalizer_tM d) ?_,
    le_antisymm (fun g hg => ?_) (sup_le (yamadaL₂_le d t)
      (h.centralizer_inf_normalizer_Y_le d)), ?_, h.normalizer_tY_le_normalizer_Y d, h2, ?_, h1⟩
  · refine fun n hn => mem_normalizer_fintype fun x hx => ?_
    rw [← hZ] at hx ⊢
    obtain ⟨hxB, hxc⟩ := hx
    obtain ⟨h5, h6⟩ := conj_mem_center_of_mem_normalizer_D4 hn hxB fun r hr =>
      (mem_centralizer_iff.1 hxc r hr).symm
    exact ⟨h5, mem_centralizer_iff.2 fun r hr => (h6 r hr).symm⟩
  · obtain ⟨c, hc, x, hx, rfl⟩ := h4 g hg
    exact mul_mem (mem_sup_right hc) (mem_sup_left hx)
  · ext g
    constructor
    · intro hg
      obtain ⟨c, hc, x, hx, rfl⟩ := h4 g hg
      refine ⟨c * x * c⁻¹, (mem_normalizer_iff.1 (le_normalizer_yamadaL₂ d t
        (h.centralizer_inf_normalizer_Y_le d hc)) x).1 hx, c, hc, by group⟩
    · rintro ⟨x, hx, c, hc, rfl⟩
      exact mul_mem (yamadaL₂_le d t hx) (h.centralizer_inf_normalizer_Y_le d hc)
  · ext x
    constructor
    · rintro ⟨c, hc, rfl⟩
      rw [← h.conj_tY d]
      exact ⟨c, yamadaL₂_le d t hc, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨c, hc, hct⟩ := h3 y hy
      exact ⟨c⁻¹, inv_mem hc, by rw [inv_inv]; exact hct⟩

theorem yamada_5_3_2_module (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    ∃ _ : ((d.M.map L.subtype ⊔ zpowers t).subgroupOf (yamadaL₂ d t)).Normal,
      ∃ φ : yamadaL₂ d t ⧸ (d.M.map L.subtype ⊔ zpowers t).subgroupOf (yamadaL₂ d t) ≃*
          (d.Y.map L.subtype : Subgroup G),
        (∀ x : yamadaL₂ d t, (φ (QuotientGroup.mk x) : G) = t * (x : G)⁻¹ * t * x) ∧
        ∀ c ∈ centralizer ({t} : Set G) ⊓ normalizer ((d.Y.map L.subtype : Subgroup G) : Set G),
          ∀ x : yamadaL₂ d t, ∃ hx : c * x * c⁻¹ ∈ yamadaL₂ d t,
            (φ (QuotientGroup.mk ⟨c * x * c⁻¹, hx⟩) : G) = c * φ (QuotientGroup.mk x) * c⁻¹ := by
  obtain ⟨h1, h2, h3, -⟩ := h.two_core_L₂ d
  have hc := h.cosetData_tY d
  have hN := hc.normal_subgroupOf (yamadaL₂_le d t) h1 h2
  obtain ⟨φ, hφ1, hφ2⟩ := hc.exists_mulEquiv_quotient (yamadaL₂_le d t) h1 h2 h3
  refine ⟨hN, φ, fun x => ?_, fun c hc' x => ?_⟩
  · rw [hφ1]
    have hy := hc.crossed_mem_of_mem ⟨yamadaL₂_le d t x.2, h1 x.2⟩
    have hyt := hc.comm_of_mem hy
    symm
    calc t * (x : G)⁻¹ * t * x = t * ((x : G)⁻¹ * t * x * t) * t⁻¹ := by group
      _ = (x : G)⁻¹ * t * x * t := by rw [hyt, mul_inv_cancel_right]
  · have hcH : c ∈ normalizer ((d.Y.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) ⊓
        centralizer ({t} : Set G) := by
      rw [h.normalizer_tY_inf_centralizer d]
      exact hc'
    have hx : c * x * c⁻¹ ∈ yamadaL₂ d t :=
      (mem_normalizer_iff.1 (le_normalizer_yamadaL₂ d t hcH.1) x).1 x.2
    exact ⟨hx, hφ2 c hcH x hx⟩

end Core

end Setup

end CFSG.LocalAnalysis.EvenBN.TrialityD4
