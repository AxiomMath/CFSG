module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AM13B

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup
open scoped Pointwise commutatorElement

namespace S4A

section Orbit

variable {G : Type} [Group G]

private theorem card_range_eq_index {H X : Type*} [Group H] (f : H → X) (K : Subgroup H)
    (hK : ∀ a b, f a = f b ↔ a⁻¹ * b ∈ K) : Nat.card (Set.range f) = K.index := by
  rw [Subgroup.index]
  refine Nat.card_congr (Equiv.ofBijective (fun q : H ⧸ K => (⟨Quotient.liftOn' q f
    (fun a b hab => (hK a b).mpr (QuotientGroup.leftRel_apply.mp hab)), by
      induction q using QuotientGroup.induction_on with | H a => exact ⟨a, rfl⟩⟩ :
      Set.range f)) ⟨fun q q' hqq => ?_, fun y => ?_⟩).symm
  · induction q using QuotientGroup.induction_on with | H a => ?_
    induction q' using QuotientGroup.induction_on with | H b => ?_
    have e : f a = f b := congrArg Subtype.val hqq
    exact QuotientGroup.eq.mpr ((hK a b).mp e)
  · obtain ⟨_, a, rfl⟩ := y
    exact ⟨QuotientGroup.mk a, rfl⟩

private theorem card_conj_orbit {H P : Type*} [Group H] [Group P] (σ : H →* P) (F : P) :
    Nat.card (Set.range fun c : H => σ c * F * (σ c)⁻¹) =
      ((centralizer ({F} : Set P)).comap σ).index := by
  refine card_range_eq_index _ _ fun a b => ?_
  rw [mem_comap, mem_centralizer_singleton_iff, map_mul, map_inv]
  constructor
  · intro h
    calc (σ a)⁻¹ * σ b * F = (σ a)⁻¹ * (σ b * F * (σ b)⁻¹) * σ b := by group
      _ = (σ a)⁻¹ * (σ a * F * (σ a)⁻¹) * σ b := by rw [h]
      _ = F * ((σ a)⁻¹ * σ b) := by group
  · intro h
    calc σ a * F * (σ a)⁻¹ = σ a * (F * ((σ a)⁻¹ * σ b)) * (σ b)⁻¹ := by group
      _ = σ a * ((σ a)⁻¹ * σ b * F) * (σ b)⁻¹ := by rw [h]
      _ = σ b * F * (σ b)⁻¹ := by group

theorem m13_card_conjIn_mul (K : Subgroup G) (x : G) :
    Nat.card K = (conjIn K x).ncard * Nat.card ↥(K ⊓ centralizer ({x} : Set G)) := by
  have hrange : conjIn K x = Set.range (fun c : K => (c : G) * x * (c : G)⁻¹) := by
    ext u
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, hk⟩, rfl⟩
    · rintro ⟨k, rfl⟩
      exact ⟨k, k.2, rfl⟩
  have h1 : Nat.card ↥(Set.range fun c : K => (c : G) * x * (c : G)⁻¹) =
      ((centralizer ({x} : Set G)).comap K.subtype).index := card_conj_orbit K.subtype x
  have h2 := Subgroup.card_mul_index ((centralizer ({x} : Set G)).comap K.subtype)
  have h3 : Nat.card ↥((centralizer ({x} : Set G)).comap K.subtype) =
      Nat.card ↥(K ⊓ centralizer ({x} : Set G)) := by
    have e := Subgroup.inf_subgroupOf_left (centralizer ({x} : Set G)) K
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_left : K ⊓ centralizer ({x} : Set G) ≤ K)).toEquiv, e]
    rfl
  rw [hrange, ← _root_.Nat.card_coe_set_eq (Set.range fun c : K => (c : G) * x * (c : G)⁻¹),
    h1, ← h2, ← h3]
  exact mul_comm _ _

end Orbit

section M13C

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem m13_F_eq (h : L41GPh8 t L S x₁ x₂ lam rho) : l41F t x₁ x₂ rho = l41O2 t x₁ x₂ :=
  h.rfacts.O2_eq.symm

theorem m13_N_le_M (h : L41GPh8 t L S x₁ x₂ lam rho) : l41N t x₁ x₂ ≤ l41M t x₁ x₂ rho := by
  intro g hg
  refine mem_normalizer_of_conj_mem fun f hf => ?_
  rw [m13_F_eq h] at hf ⊢
  exact pCoreOf_two_conj_mem hg hf

theorem m13_W_le_invCent (h : L41GPh5 t L S x₁ x₂ lam rho) : ctxW t x₁ x₂ ≤ invCent t := by
  refine sup_le (pCoreOf_two_le (invCent t)) ?_
  exact (pt_base_le_L h.toCtx0).trans (L_le_invCent h.hyp)

theorem m13_W_le_F (h : L41GPh8 t L S x₁ x₂ lam rho) :
    ctxW t x₁ x₂ ≤ l41F t x₁ x₂ rho := by
  have hP : twoCore t = zpowers t := h.p2
  refine sup_le ?_ ((n4_base_le_R h.toL41GPh3).trans le_sup_left)
  rw [hP]
  exact Subgroup.zpowers_le.mpr (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))

theorem m13_F_inf_cent_t (h : L41GPh10 t L S x₁ x₂ lam rho) :
    l41F t x₁ x₂ rho ⊓ invCent t = ctxW t x₁ x₂ := by
  apply le_antisymm
  · intro f hf
    obtain ⟨hfF, hft⟩ := Subgroup.mem_inf.mp hf
    rcases m13_mem_F h.toL41GPh8 hfF with h1 | ⟨k, hk, rfl⟩
    · have h2 : f ∈ l41R t x₁ x₂ rho ⊓ invCent t := Subgroup.mem_inf.mpr ⟨h1, hft⟩
      rw [h.rfacts.cent_t] at h2
      exact Subgroup.mem_sup_right h2
    · have h2 : t * (k * t) = t * (t * k) := by
        rw [← mul_assoc]
        exact mem_invCent_iff.mp hft
      have hkt : k ∈ invCent t := mem_invCent_iff.mpr (mul_left_cancel h2)
      have hk2 : k ∈ l41R t x₁ x₂ rho ⊓ invCent t := Subgroup.mem_inf.mpr ⟨hk, hkt⟩
      rw [h.rfacts.cent_t] at hk2
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h.hyp.mem_twoCore)
        (Subgroup.mem_sup_right hk2)
  · exact le_inf (m13_W_le_F h.toL41GPh8) (m13_W_le_invCent h.toL41GPh5)

theorem m13_cent_M_t (h : L41GPh10 t L S x₁ x₂ lam rho) :
    invCent t ⊓ l41M t x₁ x₂ rho = ctxW t x₁ x₂ ⊔ closure {rho, lam} := by
  apply le_antisymm
  · intro g hg
    obtain ⟨hgt, hgM⟩ := Subgroup.mem_inf.mp hg
    have hgt' : g * t = t * g := mem_invCent_iff.mp hgt
    have hgt2 : g * t * g⁻¹ = t := n4_conj_eq_of_comm hgt'.symm
    have hgW : g ∈ normalizer ((ctxW t x₁ x₂ : Subgroup G) : Set G) := by
      refine mem_normalizer_of_conj_mem fun w hw => ?_
      rw [← m13_F_inf_cent_t h] at hw ⊢
      obtain ⟨hwF, hwt⟩ := Subgroup.mem_inf.mp hw
      refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hgM w).mp hwF, ?_⟩
      have hwt' : w * t = t * w := mem_invCent_iff.mp hwt
      rw [mem_invCent_iff]
      calc g * w * g⁻¹ * t = g * w * g⁻¹ * (g * t * g⁻¹) := by rw [hgt2]
        _ = g * (w * t) * g⁻¹ := by group
        _ = g * (t * w) * g⁻¹ := by rw [hwt']
        _ = (g * t * g⁻¹) * (g * w * g⁻¹) := by group
        _ = t * (g * w * g⁻¹) := by rw [hgt2]
    have hmem : g ∈ invCent t ⊓ normalizer ((ctxW t x₁ x₂ : Subgroup G) : Set G) :=
      Subgroup.mem_inf.mpr ⟨hgt, hgW⟩
    rw [h.basic.norm_W] at hmem
    exact hmem
  · refine sup_le (le_inf (m13_W_le_invCent h.toL41GPh5)
      ((m13_W_le_F h.toL41GPh8).trans Subgroup.le_normalizer)) ?_
    exact le_inf ((n4_K_le_L h.toCtx0).trans (L_le_invCent h.hyp))
      ((n4_K_le_N h.toL41GPh1).trans (m13_N_le_M h.toL41GPh8))

theorem m13_card_N (h : L41GPh8 t L S x₁ x₂ lam rho) : Nat.card (l41N t x₁ x₂) = 768 := by
  obtain ⟨ψ, hs, hker⟩ := h.normalizerFacts.quot_N
  have h1 := card_eq_mul_of_section (n4_W_le_N h.toL41GPh1) ψ hs hker
  have hP : twoCore t = zpowers t := h.p2
  have hcP : Nat.card (twoCore t) = 2 := by
    rw [hP, Nat.card_zpowers, h.hyp.ord_t]
  have hW := pt_card_W h.toCtx0
  rw [hcP] at hW
  have hperm : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
    rw [Nat.card_perm, Nat.card_fin]
    rfl
  rw [hperm, hW] at h1
  omega

theorem m13_conj_mem_X (h : L41GPh10 t L S x₁ x₂ lam rho) {m : G} (hm : m ∈ l41M t x₁ x₂ rho) :
    m * t * m⁻¹ ∈ {u | u ∈ t • (l41R t x₁ x₂ rho : Set G) ∧ u * u = 1} := by
  have htF : t ∈ l41F t x₁ x₂ rho := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have h1 : m * t * m⁻¹ ∈ l41F t x₁ x₂ rho := (Subgroup.mem_normalizer_iff.mp hm t).mp htF
  refine ⟨?_, ?_⟩
  · rcases m13_mem_F h.toL41GPh8 h1 with h2 | ⟨k, hk, hk'⟩
    · exfalso
      have h3 := (m13_normal_R h).2 m⁻¹ (Subgroup.inv_mem _ hm) _ h2
      have e : m⁻¹ * (m * t * m⁻¹) * m⁻¹⁻¹ = t := by group
      rw [e] at h3
      exact h.rfacts.t_not_mem h3
    · exact n4_mem_smul_iff.mpr ⟨k, hk, hk'⟩
  · have ht2 := t_mul_self h.hyp
    calc m * t * m⁻¹ * (m * t * m⁻¹) = m * (t * t) * m⁻¹ := by group
      _ = 1 := by rw [ht2]; group

theorem m13_ncard_conjIn_M_le (h : L41GPh10 t L S x₁ x₂ lam rho) :
    (conjIn (l41M t x₁ x₂ rho) t).ncard ≤ 16 := by
  have hsub : conjIn (l41M t x₁ x₂ rho) t ⊆
      {u | u ∈ t • (l41R t x₁ x₂ rho : Set G) ∧ u * u = 1} := by
    rintro u ⟨m, hm, rfl⟩
    exact m13_conj_mem_X h hm
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  rwa [m13_card_X h] at this

theorem m13_ncard_conjIn_M_mod (h : L41GPh10 t L S x₁ x₂ lam rho) :
    (conjIn (l41M t x₁ x₂ rho) t).ncard % 3 = 1 := by
  set Ω := conjIn (l41M t x₁ x₂ rho) t with hΩdef
  have hρN : rho ∈ l41N t x₁ x₂ := n4_rho_mem_N h.toL41GPh1
  have hρM : rho ∈ l41M t x₁ x₂ rho := m13_N_le_M h.toL41GPh8 hρN
  have hΩ : ∀ n ∈ l41M t x₁ x₂ rho, ∀ x ∈ Ω, n * x * n⁻¹ ∈ Ω := by
    rintro n hn _ ⟨m, hm, rfl⟩
    exact ⟨n * m, Subgroup.mul_mem _ hn hm, by group⟩
  have hΩ' : ∀ n ∈ zpowers rho, ∀ x ∈ Ω, n * x * n⁻¹ ∈ Ω := fun n hn x hx =>
    hΩ n (Subgroup.zpowers_le.mpr hρM hn) x hx
  letI : MulAction ↥(zpowers rho) ↥Ω := MulAction.compHom ↥Ω (conjAct (zpowers rho) Ω hΩ')
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 ↥(zpowers rho) := by
    have hc : Nat.card ↥(zpowers rho) = 3 ^ 1 := by
      rw [Nat.card_zpowers, h.ord_rho]
      norm_num
    exact IsPGroup.of_card hc
  have hmod := hp.card_modEq_card_fixedPoints ↥Ω
  have htΩ : t ∈ Ω := ⟨1, Subgroup.one_mem _, by group⟩
  have hfix_t : ∀ g : ↥(zpowers rho), g • (⟨t, htΩ⟩ : ↥Ω) = ⟨t, htΩ⟩ := by
    intro g
    apply Subtype.ext
    show (g : G) * t * (g : G)⁻¹ = t
    have hgK : (g : G) ∈ closure {rho, lam} :=
      Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)) g.2
    exact n4_K_fix_t h.toCtx0 hgK
  have hfix_unique : ∀ x : ↥Ω, (∀ g : ↥(zpowers rho), g • x = x) → x = ⟨t, htΩ⟩ := by
    intro x hx
    obtain ⟨u, hu⟩ := x
    have hux : u ∈ t • (l41R t x₁ x₂ rho : Set G) ∧ u * u = 1 := by
      obtain ⟨m, hm, rfl⟩ := hu
      exact m13_conj_mem_X h hm
    obtain ⟨k, hk, rfl⟩ := n4_mem_smul_iff.mp hux.1
    have hrho : rho * (t * k) * rho⁻¹ = t * k :=
      congrArg Subtype.val (hx ⟨rho, Subgroup.mem_zpowers rho⟩)
    have htrho : rho * t * rho⁻¹ = t :=
      n4_K_fix_t h.toCtx0 (Subgroup.subset_closure (by simp))
    have hk1 : rho * k * rho⁻¹ = k := by
      have e : rho * (t * k) * rho⁻¹ = (rho * t * rho⁻¹) * (rho * k * rho⁻¹) := by group
      rw [e, htrho] at hrho
      exact mul_left_cancel hrho
    have hk0 : k ∈ l41R t x₁ x₂ rho ⊓ centralizer ({rho} : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨hk, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc k * rho = (rho * k * rho⁻¹) * rho := by rw [hk1]
        _ = rho * k := by group
    rw [h.rfacts.cent_rho, Subgroup.mem_bot] at hk0
    subst hk0
    exact Subtype.ext (mul_one t)
  have hfix : Nat.card (MulAction.fixedPoints ↥(zpowers rho) ↥Ω) = 1 := by
    haveI : Nonempty (MulAction.fixedPoints ↥(zpowers rho) ↥Ω) :=
      ⟨⟨⟨t, htΩ⟩, MulAction.mem_fixedPoints.mpr hfix_t⟩⟩
    haveI : Subsingleton (MulAction.fixedPoints ↥(zpowers rho) ↥Ω) :=
      ⟨fun a b => Subtype.ext ((hfix_unique a.1 (MulAction.mem_fixedPoints.mp a.2)).trans
        (hfix_unique b.1 (MulAction.mem_fixedPoints.mp b.2)).symm)⟩
    exact Nat.card_unique
  rw [hfix, Nat.card_coe_set_eq] at hmod
  exact hmod

theorem m13_card_M_cases (h : L41GPh10 t L S x₁ x₂ lam rho) :
    Nat.card (l41M t x₁ x₂ rho) = 768 ∨ Nat.card (l41M t x₁ x₂ rho) = 3072 := by
  have hNM : l41N t x₁ x₂ ≤ l41M t x₁ x₂ rho := m13_N_le_M h.toL41GPh8
  have hC : l41M t x₁ x₂ rho ⊓ centralizer ({t} : Set G) =
      l41N t x₁ x₂ ⊓ centralizer ({t} : Set G) := by
    apply le_antisymm
    · have h1 : invCent t ⊓ l41M t x₁ x₂ rho ≤ l41N t x₁ x₂ := by
        rw [m13_cent_M_t h]
        exact sup_le (n4_W_le_N h.toL41GPh1) (n4_K_le_N h.toL41GPh1)
      intro g hg
      obtain ⟨hgM, hgc⟩ := Subgroup.mem_inf.mp hg
      exact Subgroup.mem_inf.mpr ⟨h1 (Subgroup.mem_inf.mpr ⟨hgc, hgM⟩), hgc⟩
    · exact inf_le_inf_right _ hNM
  have h1 := m13_card_conjIn_mul (l41M t x₁ x₂ rho) t
  have h2 := m13_card_conjIn_mul (l41N t x₁ x₂) t
  rw [h.normalizerFacts.orbit_t] at h2
  have h4 : (t • (fourGrp x₁ x₂ : Set G)).ncard = 4 := by
    rw [Set.ncard_smul_set, ← Nat.card_coe_set_eq]
    exact n4_card_four h.toCtx0
  rw [h4, m13_card_N h.toL41GPh8, ← hC] at h2
  have hdvd : Nat.card (l41N t x₁ x₂) ∣ Nat.card (l41M t x₁ x₂ rho) :=
    Subgroup.card_dvd_of_le hNM
  rw [m13_card_N h.toL41GPh8] at hdvd
  have hle := m13_ncard_conjIn_M_le h
  have hmod := m13_ncard_conjIn_M_mod h
  have hc : Nat.card ↥(l41M t x₁ x₂ rho ⊓ centralizer ({t} : Set G)) = 192 := by omega
  rw [hc] at h1
  have he : (conjIn (l41M t x₁ x₂ rho) t).ncard = 4 ∨
      (conjIn (l41M t x₁ x₂ rho) t).ncard = 16 := by omega
  rcases he with he | he
  · left
    rw [h1, he]
  · right
    rw [h1, he]

theorem m13_sylow3 (h : L41GPh10 t L S x₁ x₂ lam rho) :
    ¬ 3 ∣ (zpowers rho).relIndex (l41M t x₁ x₂ rho) := by
  have hρM : rho ∈ l41M t x₁ x₂ rho :=
    m13_N_le_M h.toL41GPh8 (n4_rho_mem_N h.toL41GPh1)
  have hle : zpowers rho ≤ l41M t x₁ x₂ rho := Subgroup.zpowers_le.mpr hρM
  have h1 := Subgroup.relIndex_mul_card (H := zpowers rho) (K := l41M t x₁ x₂ rho)
  rw [inf_eq_left.mpr hle, Nat.card_zpowers, h.ord_rho] at h1
  rcases m13_card_M_cases h with h2 | h2
  · rw [h2] at h1
    omega
  · rw [h2] at h1
    omega

theorem m13_card_M (h : L41GPh10 t L S x₁ x₂ lam rho) :
    ∃ k : ℕ, Nat.card (l41M t x₁ x₂ rho) = 2 ^ k * 3 := by
  rcases m13_card_M_cases h with h1 | h1
  · exact ⟨8, by rw [h1]; norm_num⟩
  · exact ⟨10, by rw [h1]; norm_num⟩

theorem l41_mbasic_of (h : L41GPh12 t L S x₁ x₂ lam rho) : L41MBasic t x₁ x₂ lam rho where
  orbit_tk := fun k hk => m13_orbit_tk h.toL41GPh10 hk
  cent_tk := fun k hk => m13_cent_tk h.toL41GPh10 hk
  card_invol_tR := m13_card_X h.toL41GPh10
  normal_R := m13_normal_R h.toL41GPh10
  normal_Y := m13_normal_Y h.toL41GPh10
  cent_F := m13_cent_F h.toL41GPh10
  oddCore_M := m13_oddCore h.toL41GPh10
  J0_F := m13_J0 h.toL41GPh10
  cent_M_t := m13_cent_M_t h.toL41GPh10
  sylow3 := m13_sylow3 h.toL41GPh10
  card_M := m13_card_M h.toL41GPh10

end M13C

end S4A

theorem l41_mbasic_holds : L41MBasicStmt :=
  fun h => S4A.l41_mbasic_of h.toG

end CFSG.OddStandard.SmallF3.HarrisU33
