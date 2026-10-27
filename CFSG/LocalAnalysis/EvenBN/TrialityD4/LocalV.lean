module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.NotCentral
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalVPrelim
public import CFSG.LocalAnalysis.EvenBN.Common.CosetFactorization

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup CFSG.Open
open CFSG.EvenSmallLie.UnitarySix.YamadaD (oTwo le_oTwo oTwo_le isPGroup_oTwo le_normalizer_oTwo)
open CFSG.LocalAnalysis.EvenBN.Common (CosetData)
open scoped commutatorElement Pointwise

section Defs

variable {G : Type*} [Group G] {L : Subgroup G} {q : ℕ}

@[expose] noncomputable def yamadaC₁ (d : TrialityD4Data L q) (t : G) : Subgroup G :=
  pCoreOf 2 (normalizer ((d.V.map L.subtype ⊔ zpowers t : Subgroup G) : Set G))

@[expose] noncomputable def yamadaR₁ (d : TrialityD4Data L q) (t : G) : Subgroup G :=
  yamadaC₁ d t ⊔ d.S.map L.subtype

@[expose] noncomputable def yamadaL₂ (d : TrialityD4Data L q) (t : G) : Subgroup G :=
  pCoreOf 2 (normalizer ((d.Y.map L.subtype ⊔ zpowers t : Subgroup G) : Set G))

@[expose] noncomputable def yamadaR₂ (d : TrialityD4Data L q) (t : G) : Subgroup G :=
  yamadaL₂ d t ⊔ d.S.map L.subtype

theorem yamadaC₁_le (d : TrialityD4Data L q) (t : G) :
    yamadaC₁ d t ≤ normalizer ((d.V.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) :=
  LieType.BorelTits.pCoreOf_le 2 _

theorem le_normalizer_yamadaC₁ (d : TrialityD4Data L q) (t : G) :
    normalizer ((d.V.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) ≤
      normalizer (yamadaC₁ d t : Set G) :=
  LieType.BorelTits.le_normalizer_pCoreOf 2 _

theorem yamadaL₂_le (d : TrialityD4Data L q) (t : G) :
    yamadaL₂ d t ≤ normalizer ((d.Y.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) :=
  LieType.BorelTits.pCoreOf_le 2 _

theorem le_normalizer_yamadaL₂ (d : TrialityD4Data L q) (t : G) :
    normalizer ((d.Y.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) ≤
      normalizer (yamadaL₂ d t : Set G) :=
  LieType.BorelTits.le_normalizer_pCoreOf 2 _

theorem pCoreOf_two_eq_oTwo_D4 [Finite G] (H : Subgroup G) : pCoreOf 2 H = oTwo H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact le_antisymm (le_oTwo (LieType.BorelTits.pCoreOf_le 2 H)
      (LieType.BorelTits.le_normalizer_pCoreOf 2 H) (LieType.BorelTits.pCoreOf_isPGroup 2 H))
    (LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (oTwo_le H) (le_normalizer_oTwo H)
      (isPGroup_oTwo H))

end Defs

section Generic

variable {G : Type*} [Group G]

theorem mem_normalizer_zpowers_of_comm_D4 {g t : G} (hg : g * t = t * g) :
    g ∈ normalizer (zpowers t : Set G) := by
  have key : ∀ k : G, k * t = t * k → ∀ x ∈ zpowers t, k * x * k⁻¹ = x := by
    intro k hk x hx
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hx
    rw [(Commute.zpow_right (hk : Commute k t) n).eq, mul_inv_cancel_right]
  have hg' : g⁻¹ * t = t * g⁻¹ := by
    calc g⁻¹ * t = g⁻¹ * (t * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * t) * g⁻¹ := by rw [hg]
      _ = t * g⁻¹ := by group
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [key g hg x hx]
    exact hx
  · intro hx
    have := key g⁻¹ hg' _ hx
    rw [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at this
    rw [this]
    exact hx

theorem coe_mem_map_subtype_iff_D4 {L : Subgroup G} {E : Subgroup L} {l : L} :
    (l : G) ∈ E.map L.subtype ↔ l ∈ E :=
  mem_map_iff_mem L.subtype_injective

end Generic

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Action

variable {q : ℕ}

theorem conj_mem_map_iff (h : Setup G L f t) {x : G} (hx : x ∈ centralizer ({t} : Set G))
    {E : Subgroup L} (l : L) :
    x * (l : G) * x⁻¹ ∈ E.map L.subtype ↔ h.act ⟨x, hx⟩ l ∈ E := by
  rw [← h.coe_act_apply ⟨x, hx⟩ l]
  exact coe_mem_map_subtype_iff_D4

theorem exists_mul_zpowers_of_act_eq_conj (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    {x : G} (hx : x ∈ centralizer ({t} : Set G)) {l : L} (hl : h.act ⟨x, hx⟩ = MulAut.conj l) :
    ∃ c ∈ zpowers t, x = l * c := by
  have hlC : (l : G) ∈ centralizer ({t} : Set G) := h.L_le_centralizer l.2
  have h1 : h.act (⟨l, hlC⟩⁻¹ * ⟨x, hx⟩) = 1 := by
    rw [map_mul, map_inv, hl, show (⟨(l : G), hlC⟩ : centralizer ({t} : Set G)) =
      ⟨l, h.L_le_centralizer l.2⟩ from rfl, h.act_of_mem_L l.2, inv_mul_cancel]
  have h2 := (h.act_eq_one_iff _).1 h1
  rw [coe_mul, coe_inv] at h2
  have h3 : (l : G)⁻¹ * x ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) :=
    Subgroup.mem_inf.2 ⟨h2, mul_mem (inv_mem hlC) hx⟩
  rw [h.centralizer_L_inf_of_data d] at h3
  exact ⟨_, h3, by group⟩

theorem centralizer_inf_normalizer_V_le_normalizer_D (h : Setup G L f t) (d : TrialityD4Data L q) :
    centralizer ({t} : Set G) ⊓ normalizer ((d.V.map L.subtype : Subgroup G) : Set G) ≤
      normalizer ((d.D.map L.subtype : Subgroup G) : Set G) := by
  rintro x ⟨hxC, hxV⟩
  obtain ⟨g, k, hgk⟩ := d.aut_eq (h.act ⟨x, hxC⟩)
  have hV : ∀ y ∈ d.V, (MulAut.conj g * d.φ ^ k) y ∈ d.V := by
    intro y hy
    rw [← hgk, ← h.conj_mem_map_iff hxC]
    exact (mem_normalizer_iff.1 hxV _).1 ⟨y, hy, rfl⟩
  have hgD : g ∈ normalizer (d.D : Set L) := by
    rw [← d.normalizer_V_eq_normalizer_D]
    exact d.mem_normalizer_V_of_conj_mul_φ_pow hV
  refine mem_normalizer_fintype fun z hz => ?_
  obtain ⟨n, hn, rfl⟩ := hz
  rw [SetLike.mem_coe, Subgroup.coe_subtype, h.conj_mem_map_iff hxC, hgk, MulAut.mul_apply,
    MulAut.conj_apply]
  exact (mem_normalizer_iff.1 hgD _).1 (d.φ_pow_mem_D k hn)

theorem le_tD_of_isPGroup (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) {P : Subgroup G}
    (hPC : P ≤ centralizer ({t} : Set G) ⊓ normalizer ((d.V.map L.subtype : Subgroup G) : Set G))
    (hN : centralizer ({t} : Set G) ⊓ normalizer ((d.V.map L.subtype : Subgroup G) : Set G) ≤
      normalizer (P : Set G))
    (hP : IsPGroup 2 P) : P ≤ d.D.map L.subtype ⊔ zpowers t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNL : ∀ l : L, l ∈ normalizer (d.V : Set L) →
      (l : G) ∈ centralizer ({t} : Set G) ⊓
        normalizer ((d.V.map L.subtype : Subgroup G) : Set G) := by
    intro l hl
    refine ⟨h.L_le_centralizer l.2, mem_normalizer_fintype fun z hz => ?_⟩
    obtain ⟨y, hy, rfl⟩ := hz
    exact ⟨l * y * l⁻¹, (mem_normalizer_iff.1 hl y).1 hy, rfl⟩
  set Q : Subgroup L := P.comap L.subtype with hQ
  have hQ2 : IsPGroup 2 Q := hP.comap_of_injective L.subtype L.subtype_injective
  have hQnorm : ∀ l : L, l ∈ normalizer (d.V : Set L) → l ∈ normalizer (Q : Set L) := by
    intro l hl
    have hlP := hN (hNL l hl)
    rw [mem_normalizer_iff]
    intro y
    change (y : G) ∈ P ↔ ((l * y * l⁻¹ : L) : G) ∈ P
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact mem_normalizer_iff.1 hlP y
  have hQD : Q ≤ d.D := d.le_D_of_isPGroup hQ2
    (fun s hs => hQnorm s (d.S_le_normalizer_V hs))
    (hQnorm d.u (d.leviShort_le_normalizer_V d.u_mem_leviShort))
  intro x hx
  obtain ⟨hxC, hxV⟩ := hPC hx
  have hV : ∀ y ∈ d.V, h.act ⟨x, hxC⟩ y ∈ d.V := by
    intro y hy
    rw [← h.conj_mem_map_iff hxC]
    exact (mem_normalizer_iff.1 hxV _).1 ⟨y, hy, rfl⟩
  have hα : ∀ y ∈ d.leviShort, h.act ⟨x, hxC⟩ y * y⁻¹ ∈ d.D := by
    intro y hy
    apply hQD
    change ((h.act ⟨x, hxC⟩ y * y⁻¹ : L) : G) ∈ P
    rw [Subgroup.coe_mul, h.coe_act_apply, Subgroup.coe_inv,
      show x * (y : G) * x⁻¹ * (y : G)⁻¹ = x * ((y : G) * x⁻¹ * (y : G)⁻¹) by group]
    exact mul_mem hx ((mem_normalizer_iff.1 (hN (hNL y (d.leviShort_le_normalizer_V hy))) _).1
      (inv_mem hx))
  obtain ⟨n, hn, j, hj, hnj⟩ := d.eq_conj_of_trivial_mod_D hV hα
  obtain ⟨c, hc, rfl⟩ := h.exists_mul_zpowers_of_act_eq_conj d hxC hnj
  obtain ⟨a, ha⟩ := hP ⟨_, hx⟩
  have hc2 : c * c = 1 := by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hc
    rcases h.zpow_eq_one_or_eq k with hk | hk <;> rw [hk]
    · exact mul_one 1
    · exact h.t_mul_t
  have hcomm : Commute ((n * j : L) : G) c := by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hc
    exact Commute.zpow_right (mem_centralizer_iff.1 h.htL _ (n * j).2) k
  have hnj1 : (n * j) ^ 2 ^ (a + 1) = 1 := by
    have h1 := congrArg Subtype.val ha
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at h1
    have h2 : ((n * j : L) : G) ^ 2 ^ (a + 1) * c ^ 2 ^ (a + 1) = 1 := by
      rw [← hcomm.mul_pow, pow_succ, pow_mul, h1, one_pow]
    have hc' : c ^ 2 ^ (a + 1) = 1 := by rw [pow_succ', pow_mul, sq, hc2, one_pow]
    rw [hc', mul_one] at h2
    exact Subtype.ext (by rw [SubmonoidClass.coe_pow, h2, OneMemClass.coe_one])
  rw [d.eq_one_of_mul_pow_eq_one hn hj hnj1, mul_one]
  exact mul_mem (mem_sup_left ⟨n, hn, rfl⟩) (mem_sup_right hc)

end Action

section Normalizer

variable {q : ℕ}

theorem centralizer_inf_normalizer_V_le (_h : Setup G L f t) (d : TrialityD4Data L q) :
    centralizer ({t} : Set G) ⊓ normalizer ((d.V.map L.subtype : Subgroup G) : Set G) ≤
      normalizer ((d.V.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) := fun _ hx =>
  mem_normalizer_sup hx.2 (mem_normalizer_zpowers_of_comm_D4 (mem_centralizer_singleton_iff.1 hx.1))

theorem normalizer_tV_le_normalizer_V (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    normalizer ((d.V.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) ≤
      normalizer ((d.V.map L.subtype : Subgroup G) : Set G) := by
  refine fun g hg => mem_normalizer_fintype fun v hv => ?_
  have hVL : d.V.map L.subtype ≤ L := map_subtype_le _
  have h1 : g * v * g⁻¹ ∈ d.V.map L.subtype ⊔ zpowers t :=
    (mem_normalizer_iff.1 hg v).1 (mem_sup_left hv)
  rcases (h.mem_sup_zpowers_iff hVL).1 h1 with h2 | h2
  · exact h2
  · exfalso
    have hmem : g * v * g⁻¹ ∈ (fun v => t * v) '' ((d.V.map L.subtype : Subgroup G) : Set G) :=
      ⟨_, h2, by beta_reduce; rw [← mul_assoc, h.t_mul_t, one_mul]⟩
    rw [← (h.conj_t_eq_tV d).2] at hmem
    obtain ⟨n, -, hnt⟩ := hmem
    refine h.conj_not_mem_L d (g⁻¹ * n) ?_
    rw [show g⁻¹ * n * t * (g⁻¹ * n)⁻¹ = g⁻¹ * (n * t * n⁻¹) * g by group, hnt,
      show g⁻¹ * (g * v * g⁻¹) * g = v by group]
    exact hVL hv

omit [Finite G] in
theorem isElementaryAbelian_V_map (d : TrialityD4Data L q) :
    IsElementaryAbelian 2 (d.V.map L.subtype) := by
  refine isElementaryAbelian_two_of_forall (fun x hx y hy => ?_) (fun x hx => ?_)
  · obtain ⟨_, ⟨a, rfl⟩, rfl⟩ := hx
    obtain ⟨_, ⟨b, rfl⟩, rfl⟩ := hy
    change ((d.x₆ a * d.x₆ b : L) : G) = ((d.x₆ b * d.x₆ a : L) : G)
    rw [(commute_of_add d.x₆_add a b).eq]
  · obtain ⟨_, ⟨a, rfl⟩, rfl⟩ := hx
    change ((d.x₆ a * d.x₆ a : L) : G) = 1
    rw [d.x₆_mul_self]
    rfl

theorem cosetData_tV (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    CosetData (normalizer ((d.V.map L.subtype ⊔ zpowers t : Subgroup G) : Set G))
      (d.V.map L.subtype) t :=
  CosetData.of_le_normalizer h.t_mul_t ((map_subtype_le _).trans h.L_le_centralizer)
    (isElementaryAbelian_V_map d) (h.normalizer_tV_le_normalizer_V d) le_rfl

theorem normalizer_tV_inf_centralizer (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    normalizer ((d.V.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) ⊓
        centralizer ({t} : Set G) =
      centralizer ({t} : Set G) ⊓ normalizer ((d.V.map L.subtype : Subgroup G) : Set G) :=
  le_antisymm (fun _ hx => ⟨hx.2, h.normalizer_tV_le_normalizer_V d hx.1⟩)
    fun _ hx => ⟨h.centralizer_inf_normalizer_V_le d hx, hx.1⟩

theorem kernel_V_le (_h : Setup G L f t) (d : TrialityD4Data L q) :
    normalizer ((d.V.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) ⊓
        centralizer ((d.V.map L.subtype : Subgroup G) : Set G) ⊓ centralizer ({t} : Set G) ≤
      centralizer ({t} : Set G) ⊓ normalizer ((d.V.map L.subtype : Subgroup G) : Set G) :=
  fun _ hk => ⟨hk.2, Subgroup.centralizer_le_normalizer _ hk.1.2⟩

theorem normalizer_tV_le_normalizer_kernel_V (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    normalizer ((d.V.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) ≤
      normalizer ((normalizer ((d.V.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) ⊓
        centralizer ((d.V.map L.subtype : Subgroup G) : Set G) ⊓
          centralizer ({t} : Set G) : Subgroup G) : Set G) :=
  fun _ hg => mem_normalizer_fintype fun _ hk => (h.cosetData_tV d).conj_mem_kernel hg hk

omit [Finite G] in
theorem coe_mem_centralizer_V_iff (d : TrialityD4Data L q) (l : L) :
    (l : G) ∈ centralizer ((d.V.map L.subtype : Subgroup G) : Set G) ↔ l ∈ d.D ⊔ d.leviShort := by
  rw [← d.centralizer_V_eq, mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · intro hl v hv
    exact Subtype.ext (hl _ ⟨v, hv, rfl⟩)
  · rintro hl _ ⟨v, hv, rfl⟩
    exact congrArg Subtype.val (hl v hv)

theorem N₀_le_kernel_V (h : Setup G L f t) (d : TrialityD4Data L q) :
    (d.D ⊔ d.leviShort).map L.subtype ≤
      normalizer ((d.V.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) ⊓
        centralizer ((d.V.map L.subtype : Subgroup G) : Set G) ⊓ centralizer ({t} : Set G) := by
  rintro _ ⟨y, hy, rfl⟩
  have hyC := h.L_le_centralizer y.2
  have hyV := (coe_mem_centralizer_V_iff d y).2 hy
  exact ⟨⟨h.centralizer_inf_normalizer_V_le d ⟨hyC, Subgroup.centralizer_le_normalizer _ hyV⟩,
    hyV⟩, hyC⟩

theorem mem_N₀_sup_of_mem (h : Setup G L f t) (d : TrialityD4Data L q) {x : G}
    (hx : x ∈ L ⊔ zpowers t) (hxV : x ∈ centralizer ((d.V.map L.subtype : Subgroup G) : Set G)) :
    x ∈ (d.D ⊔ d.leviShort).map L.subtype ⊔ zpowers t := by
  have htV : t ∈ centralizer ((d.V.map L.subtype : Subgroup G) : Set G) :=
    mem_centralizer_iff.2 fun v hv =>
      mem_centralizer_singleton_iff.1 (h.L_le_centralizer (map_subtype_le _ hv))
  rcases (h.mem_sup_zpowers_iff le_rfl).1 hx with hxL | hxL
  · exact mem_sup_left ⟨⟨x, hxL⟩, (coe_mem_centralizer_V_iff d ⟨x, hxL⟩).1 hxV, rfl⟩
  · have h1 : t * x ∈ (d.D ⊔ d.leviShort).map L.subtype :=
      ⟨⟨t * x, hxL⟩, (coe_mem_centralizer_V_iff d ⟨t * x, hxL⟩).1 (mul_mem htV hxV), rfl⟩
    rw [show x = t * (t * x) by rw [← mul_assoc, h.t_mul_t, one_mul]]
    exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left h1)

theorem commutator_commutator_kernel_V (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    ⁅⁅normalizer ((d.V.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) ⊓
        centralizer ((d.V.map L.subtype : Subgroup G) : Set G) ⊓ centralizer ({t} : Set G),
      normalizer ((d.V.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) ⊓
        centralizer ((d.V.map L.subtype : Subgroup G) : Set G) ⊓ centralizer ({t} : Set G)⁆,
      ⁅normalizer ((d.V.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) ⊓
        centralizer ((d.V.map L.subtype : Subgroup G) : Set G) ⊓ centralizer ({t} : Set G),
      normalizer ((d.V.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) ⊓
        centralizer ((d.V.map L.subtype : Subgroup G) : Set G) ⊓ centralizer ({t} : Set G)⁆⁆ =
      (d.D ⊔ d.leviShort).map L.subtype := by
  set K₀ := normalizer ((d.V.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) ⊓
    centralizer ((d.V.map L.subtype : Subgroup G) : Set G) ⊓ centralizer ({t} : Set G) with hK₀
  set N₀ := (d.D ⊔ d.leviShort).map L.subtype with hN₀
  have hT := h.centralizer_L_inf_of_data d
  have hcV : ∀ {A : Subgroup G}, A ≤ centralizer ((d.V.map L.subtype : Subgroup G) : Set G) →
      ⁅A, A⁆ ≤ centralizer ((d.V.map L.subtype : Subgroup G) : Set G) := fun hA =>
    (commutator_mono hA hA).trans (TrialityD4Data.commutator_self_le_D4 _)
  have h1 : ⁅K₀, K₀⁆ ≤ N₀ ⊔ zpowers t := by
    intro x hx
    have hxC : x ∈ L ⊔ zpowers t := by
      have := h.commutator_le_sup_kernel d
        (commutator_mono (inf_le_right : K₀ ≤ centralizer ({t} : Set G))
          (inf_le_right : K₀ ≤ centralizer ({t} : Set G)) hx)
      rwa [hT] at this
    exact h.mem_N₀_sup_of_mem d hxC
      (hcV (inf_le_left.trans inf_le_right : K₀ ≤ centralizer
        ((d.V.map L.subtype : Subgroup G) : Set G)) hx)
  have htV : t ∈ centralizer ((d.V.map L.subtype : Subgroup G) : Set G) :=
    mem_centralizer_iff.2 fun v hv =>
      mem_centralizer_singleton_iff.1 (h.L_le_centralizer (map_subtype_le _ hv))
  have hN₀V : N₀ ⊔ zpowers t ≤ centralizer ((d.V.map L.subtype : Subgroup G) : Set G) := by
    refine sup_le ?_ ((zpowers_le).2 htV)
    rintro _ ⟨y, hy, rfl⟩
    exact (coe_mem_centralizer_V_iff d y).2 hy
  have h2 : ⁅N₀ ⊔ zpowers t, N₀ ⊔ zpowers t⁆ ≤ N₀ := by
    have hle : N₀ ⊔ zpowers t ≤ L ⊔ (centralizer (L : Set G) ⊓ centralizer ({t} : Set G)) := by
      rw [hT]
      exact sup_le_sup_right (map_subtype_le _) _
    intro x hx
    have hxL : x ∈ L := h.commutator_le_of_le_sup_kernel hle hx
    exact ⟨⟨x, hxL⟩, (coe_mem_centralizer_V_iff d ⟨x, hxL⟩).1 (hcV hN₀V hx), rfl⟩
  have hN₀K : N₀ ≤ K₀ := h.N₀_le_kernel_V d
  have hN₀ : ⁅N₀, N₀⁆ = N₀ := by rw [hN₀, ← map_commutator, d.commutator_D_sup_leviShort]
  refine le_antisymm ((commutator_mono h1 h1).trans h2) ?_
  calc N₀ = ⁅⁅N₀, N₀⁆, ⁅N₀, N₀⁆⁆ := by rw [hN₀, hN₀]
    _ ≤ _ := commutator_mono (commutator_mono hN₀K hN₀K) (commutator_mono hN₀K hN₀K)

theorem normalizer_tV_le_normalizer_N₀ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    normalizer ((d.V.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) ≤
      normalizer (((d.D ⊔ d.leviShort).map L.subtype : Subgroup G) : Set G) := by
  intro g hg
  rw [← h.commutator_commutator_kernel_V d]
  have hK := h.normalizer_tV_le_normalizer_kernel_V d hg
  exact mem_normalizer_fintype fun x hx => conj_mem_commutator
    (mem_normalizer_fintype fun y hy => conj_mem_commutator hK hy) hx

omit [Finite G] in
theorem le_D_of_le_N₀ (d : TrialityD4Data L q) {P : Subgroup G}
    (hPN : P ≤ (d.D ⊔ d.leviShort).map L.subtype) (hP : IsPGroup 2 P)
    (hn : (d.D ⊔ d.leviShort).map L.subtype ≤ normalizer (P : Set G)) :
    P ≤ d.D.map L.subtype := by
  set Q : Subgroup L := P.comap L.subtype with hQ
  have hQ2 : IsPGroup 2 Q := hP.comap_of_injective L.subtype L.subtype_injective
  have hQnorm : ∀ l : L, l ∈ d.D ⊔ d.leviShort → l ∈ normalizer (Q : Set L) := by
    intro l hl
    have hlP := hn ⟨l, hl, rfl⟩
    rw [mem_normalizer_iff]
    intro y
    change (y : G) ∈ P ↔ ((l * y * l⁻¹ : L) : G) ∈ P
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact mem_normalizer_iff.1 hlP y
  have hSN : d.S ≤ d.D ⊔ d.leviShort := by
    rw [d.S_eq_sup]
    exact sup_le (d.U₁_le_leviShort.trans le_sup_right) le_sup_left
  have hQD : Q ≤ d.D := d.le_D_of_isPGroup hQ2 (fun s hs => hQnorm s (hSN hs))
    (hQnorm d.u (mem_sup_right d.u_mem_leviShort))
  intro x hx
  obtain ⟨y, -, rfl⟩ := hPN hx
  exact ⟨y, hQD hx, rfl⟩

theorem normalizer_tV_le_normalizer_D (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    normalizer ((d.V.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) ≤
      normalizer ((d.D.map L.subtype : Subgroup G) : Set G) := by
  intro g hg
  have hgN := h.normalizer_tV_le_normalizer_N₀ d hg
  have hDN : d.D.map L.subtype ≤ (d.D ⊔ d.leviShort).map L.subtype := map_mono le_sup_left
  have hND : (d.D ⊔ d.leviShort).map L.subtype ≤
      normalizer ((d.D.map L.subtype : Subgroup G) : Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    have hyD : y ∈ normalizer (d.D : Set L) :=
      sup_le le_normalizer d.leviShort_le_normalizer_D hy
    refine mem_normalizer_fintype fun z hz => ?_
    obtain ⟨n, hn, rfl⟩ := hz
    exact ⟨y * n * y⁻¹, (mem_normalizer_iff.1 hyD n).1 hn, rfl⟩
  set P := (d.D.map L.subtype).map (MulAut.conj g).toMonoidHom with hP
  have hPN : P ≤ (d.D ⊔ d.leviShort).map L.subtype := by
    rintro _ ⟨z, hz, rfl⟩
    exact (mem_normalizer_iff.1 hgN z).1 (hDN hz)
  have hP2 : IsPGroup 2 P := by
    have h2 : IsPGroup 2 d.D := by
      obtain ⟨P₀, hP₀⟩ := d.exists_sylow_eq_S
      exact (hP₀ ▸ P₀.isPGroup').to_le d.D_le_S
    exact (h2.map _).map _
  have hn : (d.D ⊔ d.leviShort).map L.subtype ≤ normalizer (P : Set G) := by
    intro s hs
    have hs' : g⁻¹ * s * g ∈ (d.D ⊔ d.leviShort).map L.subtype := by
      have := (mem_normalizer_iff.1 (inv_mem hgN) s).1 hs
      rwa [inv_inv] at this
    refine mem_normalizer_fintype fun z hz => ?_
    obtain ⟨w, hw, rfl⟩ := hz
    refine ⟨(g⁻¹ * s * g) * w * (g⁻¹ * s * g)⁻¹,
      (mem_normalizer_iff.1 (hND hs') w).1 hw, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hPD := le_D_of_le_N₀ d hPN hP2 hn
  exact mem_normalizer_fintype fun z hz => hPD ⟨z, hz, rfl⟩

theorem normalizer_tV_le_normalizer_tD (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    normalizer ((d.V.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) ≤
      normalizer ((d.D.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) := by
  intro g hg
  have hVD : d.V.map L.subtype ≤ d.D.map L.subtype :=
    map_mono (d.V_le_Y.trans (d.Y_le_W.trans (d.W_le_F.trans d.F_le_D)))
  have hgt : g * t * g⁻¹ ∈ d.D.map L.subtype ⊔ zpowers t :=
    sup_le_sup_right hVD _ ((mem_normalizer_iff.1 hg t).1 (mem_sup_right (mem_zpowers t)))
  refine mem_normalizer_fintype (conj_mem_sup (fun n hn => mem_sup_left
    ((mem_normalizer_iff.1 (h.normalizer_tV_le_normalizer_D d hg) n).1 hn)) fun n hn => ?_)
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hn
  rw [show g * t ^ k * g⁻¹ = (g * t * g⁻¹) ^ k by
    rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply]]
  exact zpow_mem hgt k

theorem tD_le_kernel_V (h : Setup G L f t) (d : TrialityD4Data L q) :
    d.D.map L.subtype ⊔ zpowers t ≤
      normalizer ((d.V.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) ⊓
        centralizer ((d.V.map L.subtype : Subgroup G) : Set G) ⊓ centralizer ({t} : Set G) := by
  refine sup_le ((map_mono le_sup_left).trans (h.N₀_le_kernel_V d)) ((zpowers_le).2 ?_)
  have htV : t ∈ centralizer ((d.V.map L.subtype : Subgroup G) : Set G) :=
    mem_centralizer_iff.2 fun v hv =>
      mem_centralizer_singleton_iff.1 (h.L_le_centralizer (map_subtype_le _ hv))
  exact ⟨⟨h.centralizer_inf_normalizer_V_le d ⟨h.t_mem_centralizer,
    Subgroup.centralizer_le_normalizer _ htV⟩, htV⟩, h.t_mem_centralizer⟩

theorem isPGroup_tD (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    IsPGroup 2 (d.D.map L.subtype ⊔ zpowers t : Subgroup G) := by
  refine (h.isSylowOf_yamadaR d).isPGroup.to_le ?_
  rw [yamadaR, h.centralizer_L_inf_of_data d]
  exact sup_le_sup_right (map_mono d.D_le_S) _

end Normalizer

section Frobenius

theorem exists_scalar_of_kernel_V (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) {e : G}
    (he : e ∈ normalizer ((d.V.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) ⊓
      centralizer ({t} : Set G))
    (hek : ∀ k ∈ normalizer ((d.V.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) ⊓
      centralizer ((d.V.map L.subtype : Subgroup G) : Set G) ⊓ centralizer ({t} : Set G),
        e * k * e⁻¹ * k⁻¹ ∈ d.D.map L.subtype ⊔ zpowers t) :
    ∃ a : d.Γ₀, a ≠ 0 ∧ ∀ x : d.Γ₀, e * (d.x₆ x : G) * e⁻¹ = (d.x₆ (a * x) : G) := by
  have heC := he.2
  have heV : e ∈ normalizer ((d.V.map L.subtype : Subgroup G) : Set G) :=
    h.normalizer_tV_le_normalizer_V d he.1
  have hV : ∀ y ∈ d.V, h.act ⟨e, heC⟩ y ∈ d.V := fun y hy => by
    rw [← h.conj_mem_map_iff heC]
    exact (mem_normalizer_iff.1 heV _).1 ⟨y, hy, rfl⟩
  have hα : ∀ y ∈ d.leviShort, h.act ⟨e, heC⟩ y * y⁻¹ ∈ d.D := by
    intro y hy
    have h1 := hek _ (h.N₀_le_kernel_V d ⟨y, mem_sup_right hy, rfl⟩)
    rw [show e * (L.subtype y) * e⁻¹ * (L.subtype y)⁻¹ =
      ((h.act ⟨e, heC⟩ y * y⁻¹ : L) : G) by
        rw [Subgroup.coe_mul, h.coe_act_apply, Subgroup.coe_inv]; rfl] at h1
    rcases (h.mem_sup_zpowers_iff (map_subtype_le _)).1 h1 with h3 | h3
    · exact coe_mem_map_subtype_iff_D4.1 h3
    · exfalso
      refine h.t_not_mem_L ?_
      have := mul_mem (map_subtype_le _ h3) (inv_mem (h.act ⟨e, heC⟩ y * y⁻¹).2)
      rwa [mul_inv_cancel_right] at this
  obtain ⟨n, hn, j, hj, hnj⟩ := d.eq_conj_of_trivial_mod_D hV hα
  obtain ⟨⟨l, m⟩, rfl, hm⟩ := d.mem_J₁.1 hj
  dsimp only at hm
  subst hm
  refine ⟨(l : d.Γ₀) * (l : d.Γ₀), mul_ne_zero l.ne_zero l.ne_zero, fun x => ?_⟩
  have h1 := h.coe_act_apply ⟨e, heC⟩ (d.x₆ x)
  rw [hnj, MulAut.conj_apply] at h1
  change _ = e * ((d.x₆ x : L) : G) * e⁻¹ at h1
  rw [← h1, show n * d.torus (l, 1) * d.x₆ x * (n * d.torus (l, 1))⁻¹ =
      n * (d.torus (l, 1) * d.x₆ x * (d.torus (l, 1))⁻¹) * n⁻¹ by group,
    d.torus_conj_x₆_of_snd_eq_one,
    ← mem_centralizer_iff.1 (d.S_le_centralizer_V (d.D_le_S hn)) _ (d.x₆_mem_V _),
    mul_inv_cancel_right]

theorem exists_kernel_of_scalar_V (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) {a : d.Γ₀}
    (ha : a ≠ 0) :
    ∃ e ∈ normalizer ((d.V.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) ⊓
      centralizer ({t} : Set G),
      (∀ k ∈ normalizer ((d.V.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) ⊓
        centralizer ((d.V.map L.subtype : Subgroup G) : Set G) ⊓ centralizer ({t} : Set G),
          e * k * e⁻¹ * k⁻¹ ∈ d.D.map L.subtype ⊔ zpowers t) ∧
        ∀ x : d.Γ₀, e * (d.x₆ x : G) * e⁻¹ = (d.x₆ (a * x) : G) := by
  obtain ⟨l, hl⟩ := d.sq_surjective_units₀ (Units.mk0 a ha)
  set j : L := d.torus (l, 1) with hjdef
  have hjJ₁ : j ∈ d.J₁ := (d.torus_mem_J₁_iff _).2 rfl
  have hjC : (j : G) ∈ centralizer ({t} : Set G) := h.L_le_centralizer j.2
  have hjV : (j : G) ∈ normalizer ((d.V.map L.subtype : Subgroup G) : Set G) := by
    refine mem_normalizer_fintype fun z hz => ?_
    obtain ⟨y, hy, rfl⟩ := hz
    exact ⟨j * y * j⁻¹, (mem_normalizer_iff.1 (d.J_le_normalizer_V hjJ₁.1) y).1 hy, rfl⟩
  refine ⟨j, ⟨h.centralizer_inf_normalizer_V_le d ⟨hjC, hjV⟩, hjC⟩, fun k hk => ?_,
    fun x => ?_⟩
  · obtain ⟨⟨-, hkV⟩, hkC⟩ := hk
    obtain ⟨g, m, hgm⟩ := d.aut_eq (h.act ⟨k, hkC⟩)
    have hcent : ∀ y ∈ d.V, (MulAut.conj g * d.φ ^ m) y = y := by
      intro y hy
      rw [← hgm]
      refine Subtype.ext ?_
      rw [h.coe_act_apply]
      change k * (y : G) * k⁻¹ = y
      have hyk : (y : G) * k = k * y := mem_centralizer_iff.1 hkV _ ⟨y, hy, rfl⟩
      rw [← hyk, mul_inv_cancel_right]
    obtain ⟨hg, hfix⟩ := d.exists_of_centralizes_V hcent
    have hφj : (d.φ ^ m) j⁻¹ = j⁻¹ := by
      rw [map_inv, d.φ_pow_apply_of_mem_J₁ hfix hjJ₁]
    obtain ⟨n, hn, s, hs, rfl⟩ := d.exists_mul_of_mem_D_sup_leviShort hg
    have hjs : j * s * j⁻¹ = s := by
      rw [← mem_centralizer_iff.1 (d.yamada_three_eight_four.2.2.2.1 hjJ₁) s hs,
        mul_inv_cancel_right]
    have hjn : j * n * j⁻¹ ∈ d.D := (mem_normalizer_iff.1 (d.J₁_le_normalizer_D hjJ₁) n).1 hn
    have hcomm : j * (n * s) * j⁻¹ * (n * s)⁻¹ ∈ d.D := by
      have e1 : j * (n * s) * j⁻¹ * (n * s)⁻¹ = (j * n * j⁻¹) * (j * s * j⁻¹) * s⁻¹ * n⁻¹ := by
        group
      rw [e1, hjs, mul_inv_cancel_right]
      exact mul_mem hjn (inv_mem hn)
    have hact : h.act (⟨j, hjC⟩ * ⟨k, hkC⟩ * ⟨j, hjC⟩⁻¹ * ⟨k, hkC⟩⁻¹) =
        MulAut.conj (j * (n * s) * j⁻¹ * (n * s)⁻¹) := by
      have e2 : ∀ β : MulAut L, MulAut.conj j * β * (MulAut.conj j)⁻¹ * β⁻¹ =
          MulAut.conj (j * β j⁻¹) := by
        intro β
        rw [map_mul, ← mulAut_mul_conj_mul_inv β, map_inv]
        group
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hgm,
        show (⟨(j : G), hjC⟩ : centralizer ({t} : Set G)) = ⟨j, h.L_le_centralizer j.2⟩ from rfl,
        h.act_of_mem_L j.2, Subtype.coe_eta, e2, MulAut.mul_apply, hφj, MulAut.conj_apply]
      congr 1
      group
    obtain ⟨c, hc, he⟩ := h.exists_mul_zpowers_of_act_eq_conj d
      (mul_mem (mul_mem (mul_mem hjC hkC) (inv_mem hjC)) (inv_mem hkC)) hact
    rw [he]
    exact mul_mem (mem_sup_left ⟨_, hcomm, rfl⟩) (mem_sup_right hc)
  · have hla : (l : d.Γ₀) * (l : d.Γ₀) = a := by
      rw [← sq, ← Units.val_pow_eq_pow_val, hl, Units.val_mk0]
    change ((j * d.x₆ x * j⁻¹ : L) : G) = _
    rw [hjdef, d.torus_conj_x₆_of_snd_eq_one, hla]

omit [Finite G] in
theorem exists_mulEquiv_V {q : ℕ} (d : TrialityD4Data L q) :
    ∃ ι : Multiplicative d.Γ₀ ≃* (d.V.map L.subtype : Subgroup G),
      ∀ a : d.Γ₀, (ι (Multiplicative.ofAdd a) : G) = (d.x₆ a : G) := by
  let φ : Multiplicative d.Γ₀ →* (d.V.map L.subtype : Subgroup G) :=
    { toFun := fun a => ⟨(d.x₆ (Multiplicative.toAdd a) : G), ⟨_, d.x₆_mem_V _, rfl⟩⟩
      map_one' := Subtype.ext (by simp [d.x₆_zero])
      map_mul' := fun a b => Subtype.ext (by simp [d.x₆_add]) }
  have hinj : Function.Injective φ := fun a b hab => by
    have h1 := congrArg Subtype.val hab
    change ((d.x₆ (Multiplicative.toAdd a) : L) : G) = d.x₆ (Multiplicative.toAdd b) at h1
    exact Multiplicative.toAdd.injective (d.x₆_injective (Subtype.ext h1))
  have hsurj : Function.Surjective φ := by
    rintro ⟨_, ⟨_, ⟨a, rfl⟩, rfl⟩⟩
    exact ⟨Multiplicative.ofAdd a, rfl⟩
  exact ⟨MulEquiv.ofBijective φ ⟨hinj, hsurj⟩, fun a => rfl⟩

theorem two_core_C₁ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hq : 4 ≤ 2 ^ f) :
    yamadaC₁ d t ≤ centralizer ((d.V.map L.subtype : Subgroup G) : Set G) ∧
      yamadaC₁ d t ⊓ centralizer ({t} : Set G) = d.D.map L.subtype ⊔ zpowers t ∧
      (∀ y ∈ d.V.map L.subtype, ∃ x ∈ yamadaC₁ d t, x⁻¹ * t * x = t * y) ∧
      ∀ g ∈ normalizer ((d.V.map L.subtype ⊔ zpowers t : Subgroup G) : Set G),
        ∃ c ∈ centralizer ({t} : Set G) ⊓ normalizer ((d.V.map L.subtype : Subgroup G) : Set G),
          ∃ x ∈ yamadaC₁ d t, g = c * x := by
  obtain ⟨ι, hι⟩ := exists_mulEquiv_V (G := G) d
  have hc := h.cosetData_tV d
  have hK2 : 2 < Nat.card d.Γ₀ := by
    rw [d.card_Γ₀]
    omega
  have hmax : ∀ R : Subgroup G,
      R ≤ normalizer ((d.V.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) ⊓
        centralizer ({t} : Set G) →
      normalizer ((d.V.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) ⊓
        centralizer ({t} : Set G) ≤ normalizer (R : Set G) → IsPGroup 2 R →
          R ≤ d.D.map L.subtype ⊔ zpowers t := by
    intro R hR hN hp
    rw [h.normalizer_tV_inf_centralizer d] at hR hN
    exact h.le_tD_of_isPGroup d hR hN hp
  have htr : ∀ y ∈ d.V.map L.subtype, ∃ g ∈ normalizer
      ((d.V.map L.subtype ⊔ zpowers t : Subgroup G) : Set G), g⁻¹ * t * g = t * y := by
    intro y hy
    have hmem : t * y ∈ (fun v => t * v) '' ((d.V.map L.subtype : Subgroup G) : Set G) :=
      ⟨y, hy, rfl⟩
    rw [← (h.conj_t_eq_tV d).2] at hmem
    obtain ⟨n, hn, hnt⟩ := hmem
    exact ⟨n⁻¹, inv_mem hn, by rw [inv_inv]; exact hnt⟩
  obtain ⟨h1, h2, h3, h4⟩ := hc.frobenius_two_core hK2 ι htr (h.isPGroup_tD d)
    (h.tD_le_kernel_V d) (h.normalizer_tV_le_normalizer_tD d) hmax
    (fun e he hek => by
      obtain ⟨a, ha, hax⟩ := h.exists_scalar_of_kernel_V d he hek
      exact ⟨a, ha, fun x => by rw [hι, hι]; exact hax x⟩)
    (fun a ha => by
      obtain ⟨e, he, hek, hax⟩ := h.exists_kernel_of_scalar_V d ha
      exact ⟨e, he, hek, fun x => by rw [hι, hι]; exact hax x⟩)
  rw [yamadaC₁, pCoreOf_two_eq_oTwo_D4]
  refine ⟨h1, h2, h3, fun g hg => ?_⟩
  obtain ⟨c, hc, x, hx, rfl⟩ := h4 g hg
  rw [h.normalizer_tV_inf_centralizer d] at hc
  exact ⟨c, hc, x, hx, rfl⟩

end Frobenius

section Main

@[expose] def CoreC₁ (d : TrialityD4Data L (2 ^ f)) (t : G) : Prop :=
  yamadaC₁ d t ≤ centralizer ((d.V.map L.subtype : Subgroup G) : Set G) ∧
    yamadaC₁ d t ⊓ centralizer ({t} : Set G) = d.D.map L.subtype ⊔ zpowers t ∧
    (∀ y ∈ d.V.map L.subtype, ∃ x ∈ yamadaC₁ d t, x⁻¹ * t * x = t * y) ∧
    ∀ g ∈ normalizer ((d.V.map L.subtype ⊔ zpowers t : Subgroup G) : Set G),
      ∃ c ∈ centralizer ({t} : Set G) ⊓ normalizer ((d.V.map L.subtype : Subgroup G) : Set G),
        ∃ x ∈ yamadaC₁ d t, g = c * x

theorem yamada_5_3_1_of_core (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hcore : CoreC₁ d t) :
    normalizer ((d.V.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) =
        yamadaC₁ d t ⊔ (centralizer ({t} : Set G) ⊓
          normalizer ((d.V.map L.subtype : Subgroup G) : Set G)) ∧
      ((normalizer ((d.V.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) : Subgroup G) :
          Set G) = (yamadaC₁ d t : Set G) * ((centralizer ({t} : Set G) ⊓
            normalizer ((d.V.map L.subtype : Subgroup G) : Set G) : Subgroup G) : Set G) ∧
      normalizer ((d.V.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) ≤
        normalizer ((d.D.map L.subtype : Subgroup G) : Set G) ∧
      yamadaC₁ d t ⊓ centralizer ({t} : Set G) = d.D.map L.subtype ⊔ zpowers t ∧
      {x | ∃ c ∈ yamadaC₁ d t, c * t * c⁻¹ = x} =
        (fun v => t * v) '' ((d.V.map L.subtype : Subgroup G) : Set G) ∧
      yamadaC₁ d t ≤ centralizer ((d.V.map L.subtype : Subgroup G) : Set G) := by
  obtain ⟨h1, h2, h3, h4⟩ := hcore
  refine ⟨le_antisymm (fun g hg => ?_) (sup_le (yamadaC₁_le d t)
    (h.centralizer_inf_normalizer_V_le d)), ?_, h.normalizer_tV_le_normalizer_D d, h2, ?_, h1⟩
  · obtain ⟨c, hc, x, hx, rfl⟩ := h4 g hg
    exact mul_mem (mem_sup_right hc) (mem_sup_left hx)
  · ext g
    constructor
    · intro hg
      obtain ⟨c, hc, x, hx, rfl⟩ := h4 g hg
      refine ⟨c * x * c⁻¹, (mem_normalizer_iff.1 (le_normalizer_yamadaC₁ d t
        (h.centralizer_inf_normalizer_V_le d hc)) x).1 hx, c, hc, by group⟩
    · rintro ⟨x, hx, c, hc, rfl⟩
      exact mul_mem (yamadaC₁_le d t hx) (h.centralizer_inf_normalizer_V_le d hc)
  · ext x
    constructor
    · rintro ⟨c, hc, rfl⟩
      rw [← (h.conj_t_eq_tV d).2]
      exact ⟨c, yamadaC₁_le d t hc, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨c, hc, hct⟩ := h3 v hv
      exact ⟨c⁻¹, inv_mem hc, by rw [inv_inv]; exact hct⟩

theorem yamada_5_3_1_module_of_core (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hcore : CoreC₁ d t) :
    ∃ _ : ((d.D.map L.subtype ⊔ zpowers t).subgroupOf (yamadaC₁ d t)).Normal,
      ∃ φ : yamadaC₁ d t ⧸ (d.D.map L.subtype ⊔ zpowers t).subgroupOf (yamadaC₁ d t) ≃*
          (d.V.map L.subtype : Subgroup G),
        (∀ x : yamadaC₁ d t, (φ (QuotientGroup.mk x) : G) = t * (x : G)⁻¹ * t * x) ∧
        ∀ c ∈ centralizer ({t} : Set G) ⊓ normalizer ((d.V.map L.subtype : Subgroup G) : Set G),
          ∀ x : yamadaC₁ d t, ∃ hx : c * x * c⁻¹ ∈ yamadaC₁ d t,
            (φ (QuotientGroup.mk ⟨c * x * c⁻¹, hx⟩) : G) = c * φ (QuotientGroup.mk x) * c⁻¹ := by
  obtain ⟨h1, h2, h3, -⟩ := hcore
  have hc := h.cosetData_tV d
  have hN := hc.normal_subgroupOf (yamadaC₁_le d t) h1 h2
  obtain ⟨φ, hφ1, hφ2⟩ := hc.exists_mulEquiv_quotient (yamadaC₁_le d t) h1 h2 h3
  refine ⟨hN, φ, fun x => ?_, fun c hc' x => ?_⟩
  · rw [hφ1]
    have hy := hc.crossed_mem_of_mem ⟨yamadaC₁_le d t x.2, h1 x.2⟩
    have hyt := hc.comm_of_mem hy
    symm
    calc t * (x : G)⁻¹ * t * x = t * ((x : G)⁻¹ * t * x * t) * t⁻¹ := by group
      _ = (x : G)⁻¹ * t * x * t := by rw [hyt, mul_inv_cancel_right]
  · have hcH : c ∈ normalizer ((d.V.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) ⊓
        centralizer ({t} : Set G) := by
      rw [h.normalizer_tV_inf_centralizer d]
      exact hc'
    have hx : c * x * c⁻¹ ∈ yamadaC₁ d t :=
      (mem_normalizer_iff.1 (le_normalizer_yamadaC₁ d t hcH.1) x).1 x.2
    exact ⟨hx, hφ2 c hcH x hx⟩

theorem commutator_mem_D_of_core (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hcore : CoreC₁ d t) {x y : G} (hx : x ∈ yamadaC₁ d t)
    (hy : y ∈ (d.D ⊔ d.leviShort).map L.subtype) : x * y * x⁻¹ * y⁻¹ ∈ d.D.map L.subtype := by
  have hyH : y ∈ normalizer ((d.V.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) :=
    (h.N₀_le_kernel_V d hy).1.1
  have h1 : x * y * x⁻¹ * y⁻¹ ∈ yamadaC₁ d t := by
    rw [show x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) by group]
    exact mul_mem hx ((mem_normalizer_iff.1 (le_normalizer_yamadaC₁ d t hyH) _).1 (inv_mem hx))
  have h2 : x * y * x⁻¹ * y⁻¹ ∈ (d.D ⊔ d.leviShort).map L.subtype :=
    mul_mem ((mem_normalizer_iff.1 (h.normalizer_tV_le_normalizer_N₀ d (yamadaC₁_le d t hx))
      y).1 hy) (inv_mem hy)
  have h2L : x * y * x⁻¹ * y⁻¹ ∈ L := map_subtype_le _ h2
  have h3 : x * y * x⁻¹ * y⁻¹ ∈ d.D.map L.subtype ⊔ zpowers t := by
    rw [← hcore.2.1]
    exact ⟨h1, h.L_le_centralizer h2L⟩
  rcases (h.mem_sup_zpowers_iff (map_subtype_le _)).1 h3 with h4 | h4
  · exact h4
  · exfalso
    refine h.t_not_mem_L ?_
    have := mul_mem (map_subtype_le _ h4) (inv_mem h2L)
    rwa [mul_inv_cancel_right] at this

omit [Finite G] in
theorem S_le_N₀ {q : ℕ} (d : TrialityD4Data L q) : d.S ≤ d.D ⊔ d.leviShort := by
  rw [d.S_eq_sup]
  exact sup_le (d.U₁_le_leviShort.trans le_sup_right) le_sup_left

theorem yamadaC₁_le_normalizer_S_of_core (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hcore : CoreC₁ d t) :
    yamadaC₁ d t ≤ normalizer ((d.S.map L.subtype : Subgroup G) : Set G) := by
  intro x hx
  refine mem_normalizer_fintype fun s hs => ?_
  have h1 := h.commutator_mem_D_of_core d hcore hx (map_mono (S_le_N₀ d) hs)
  rw [show x * s * x⁻¹ = x * s * x⁻¹ * s⁻¹ * s by group]
  exact mul_mem (map_mono d.D_le_S h1) hs

theorem yamadaC₁_le_normalizer_yamadaR_of_core (h : Setup G L f t)
    (d : TrialityD4Data L (2 ^ f)) (hcore : CoreC₁ d t) :
    yamadaC₁ d t ≤ normalizer (yamadaR d t : Set G) := by
  intro x hx
  have hR := yamadaR_eq_of_eq d (h.centralizer_L_inf_of_data d)
  rw [hR]
  have hVS : d.V.map L.subtype ≤ d.S.map L.subtype := map_mono d.V_le_S
  have hxt : x * t * x⁻¹ ∈ d.S.map L.subtype ⊔ zpowers t :=
    sup_le_sup_right hVS _ ((mem_normalizer_iff.1 (yamadaC₁_le d t hx) t).1
      (mem_sup_right (mem_zpowers t)))
  refine mem_normalizer_fintype (conj_mem_sup (fun n hn => mem_sup_left
    ((mem_normalizer_iff.1 (h.yamadaC₁_le_normalizer_S_of_core d hcore hx) n).1 hn))
    fun n hn => ?_)
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hn
  rw [show x * t ^ k * x⁻¹ = (x * t * x⁻¹) ^ k by
    rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply]]
  exact zpow_mem hxt k

theorem normalizer_yamadaR_le_tV (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    normalizer (yamadaR d t : Set G) ≤
      normalizer ((d.V.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) := by
  have hZ := h.center_yamadaR_of_eq d (h.centralizer_L_inf_of_data d)
  refine fun n hn => mem_normalizer_fintype fun x hx => ?_
  obtain ⟨hxR, hxc⟩ := Subgroup.mem_inf.1 (hZ.ge hx)
  obtain ⟨hnR, hnc⟩ := conj_mem_center_of_mem_normalizer_D4 hn hxR fun r hr =>
    (mem_centralizer_iff.1 hxc r hr).symm
  rw [← hZ]
  exact Subgroup.mem_inf.2 ⟨hnR, mem_centralizer_iff.2 fun r hr => (hnc r hr).symm⟩

theorem yamada_5_3_3_of_core (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hcore : CoreC₁ d t) :
    normalizer (yamadaR d t : Set G) = yamadaC₁ d t ⊔
        (centralizer ({t} : Set G) ⊓ normalizer ((d.S.map L.subtype : Subgroup G) : Set G)) ∧
      ((normalizer (yamadaR d t : Set G) : Subgroup G) : Set G) =
        (yamadaC₁ d t : Set G) * ((centralizer ({t} : Set G) ⊓
          normalizer ((d.S.map L.subtype : Subgroup G) : Set G) : Subgroup G) : Set G) ∧
      normalizer (yamadaR d t : Set G) ≤ normalizer ((d.S.map L.subtype : Subgroup G) : Set G) := by
  have hR := yamadaR_eq_of_eq d (h.centralizer_L_inf_of_data d)
  have hSL : d.S.map L.subtype ≤ L := map_subtype_le _
  have hC₁R := h.yamadaC₁_le_normalizer_yamadaR_of_core d hcore
  have hNS : centralizer ({t} : Set G) ⊓ normalizer ((d.S.map L.subtype : Subgroup G) : Set G) ≤
      normalizer (yamadaR d t : Set G) := by
    intro x hx
    rw [hR]
    exact mem_normalizer_sup hx.2
      (mem_normalizer_zpowers_of_comm_D4 (mem_centralizer_singleton_iff.1 hx.1))
  have heq : normalizer (yamadaR d t : Set G) = yamadaC₁ d t ⊔
      (centralizer ({t} : Set G) ⊓ normalizer ((d.S.map L.subtype : Subgroup G) : Set G)) := by
    refine le_antisymm (fun n hn => ?_) (sup_le hC₁R hNS)
    obtain ⟨c, hc, x, hx, rfl⟩ := hcore.2.2.2 n (h.normalizer_yamadaR_le_tV d hn)
    have hcR : c ∈ normalizer (yamadaR d t : Set G) := by
      have := mul_mem hn (inv_mem (hC₁R hx))
      rwa [mul_inv_cancel_right] at this
    have hcS : c ∈ normalizer ((d.S.map L.subtype : Subgroup G) : Set G) :=
      mem_normalizer_fintype fun s hs => by
        have h1 : c * s * c⁻¹ ∈ yamadaR d t := (mem_normalizer_iff.1 hcR s).1
          (hR.ge (mem_sup_left hs))
        have h2 : c * s * c⁻¹ ∈ L :=
          (mem_normalizer_iff.1 (h.centralizer_le_normalizer hc.1) s).1 (hSL hs)
        rw [hR] at h1
        rcases (h.mem_sup_zpowers_iff hSL).1 h1 with h3 | h3
        · exact h3
        · exfalso
          refine h.t_not_mem_L ?_
          have := mul_mem (hSL h3) (inv_mem h2)
          rwa [mul_inv_cancel_right] at this
    exact mul_mem (mem_sup_right ⟨hc.1, hcS⟩) (mem_sup_left hx)
  refine ⟨heq, ?_, ?_⟩
  · ext n
    constructor
    · intro hn
      have hNC : centralizer ({t} : Set G) ⊓
          normalizer ((d.S.map L.subtype : Subgroup G) : Set G) ≤
            normalizer (yamadaC₁ d t : Set G) :=
        hNS.trans ((h.normalizer_yamadaR_le_tV d).trans (le_normalizer_yamadaC₁ d t))
      rw [SetLike.mem_coe, heq, ← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left _ _ hNC]
        at hn
      exact hn
    · rintro ⟨x, hx, c, hc, rfl⟩
      exact mul_mem (hC₁R hx) (hNS hc)
  · rw [heq]
    exact sup_le (h.yamadaC₁_le_normalizer_S_of_core d hcore) inf_le_right

end Main

end Setup

end CFSG.LocalAnalysis.EvenBN.TrialityD4
