module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1StageLevel
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1StageFpf
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1Lambda

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup

namespace U3C1

variable {G : Type*} [Group G] {T₁ : Subgroup G}

theorem exists_inv_mul_conj_of_fixedPointFree [Finite G] {k : G}
    (hcomm : ∀ y ∈ T₁, ∀ y' ∈ T₁, y * y' * y⁻¹ * y'⁻¹ ∈ szA₁ T₁)
    (hkT : k ∈ normalizer (T₁ : Set G)) (hkA : ∀ a ∈ szA₁ T₁, k * a * k⁻¹ = a)
    (hfpf : ∀ y ∈ T₁, y⁻¹ * (k * y * k⁻¹) ∈ szA₁ T₁ → y ∈ szA₁ T₁) {z : G} (hz : z ∈ T₁) :
    ∃ y ∈ T₁, (y⁻¹ * (k * y * k⁻¹))⁻¹ * z ∈ szA₁ T₁ := by
  classical
  have hkT' : ∀ y ∈ T₁, k * y * k⁻¹ ∈ T₁ := fun y hy => (mem_normalizer_iff.mp hkT y).mp hy
  have hcen : ∀ a ∈ szA₁ T₁, ∀ y ∈ T₁, a * y = y * a := fun a ha y hy =>
    (mem_centralizer_iff.mp (mem_szA₁.mp ha).2 y hy).symm
  set A' := (szA₁ T₁).subgroupOf T₁ with hA'
  set ψ : T₁ → T₁ := fun y => ⟨(y : G)⁻¹ * (k * y * k⁻¹), mul_mem (inv_mem y.2) (hkT' _ y.2)⟩
    with hψ
  have hψc : ∀ (y : T₁) (a : T₁), (a : G) ∈ szA₁ T₁ → ψ (y * a) = ψ y := by
    intro y a ha
    apply Subtype.ext
    simp only [hψ, Subgroup.coe_mul]
    have hka := hkA _ ha
    calc ((y : G) * a)⁻¹ * (k * (y * a) * k⁻¹) = (a : G)⁻¹ * ((y : G)⁻¹ * (k * y * k⁻¹)) *
          (k * a * k⁻¹) := by group
      _ = (a : G)⁻¹ * ((y : G)⁻¹ * (k * y * k⁻¹)) * a := by rw [hka]
      _ = (y : G)⁻¹ * (k * y * k⁻¹) := by
          rw [mul_assoc, ← hcen _ ha _ (mul_mem (inv_mem y.2) (hkT' _ y.2)), inv_mul_cancel_left]
  let ψ' : T₁ ⧸ A' → T₁ ⧸ A' := Quotient.lift (fun y => (ψ y : T₁ ⧸ A')) fun a b hab => by
    have h1 : a⁻¹ * b ∈ A' := QuotientGroup.leftRel_apply.mp hab
    have hb : b = a * (a⁻¹ * b) := by group
    change (ψ a : T₁ ⧸ A') = (ψ b : T₁ ⧸ A')
    rw [hb, hψc a _ (mem_subgroupOf.mp h1)]
  have hinj : Function.Injective ψ' := by
    intro a b hab
    induction a using QuotientGroup.induction_on with | H a => ?_
    induction b using QuotientGroup.induction_on with | H b => ?_
    change (ψ a : T₁ ⧸ A') = (ψ b : T₁ ⧸ A') at hab
    rw [QuotientGroup.eq, mem_subgroupOf] at hab ⊢
    simp only [hψ, Subgroup.coe_inv, Subgroup.coe_mul] at hab ⊢
    set x := (a : G)⁻¹ * b with hx
    have hxT : x ∈ T₁ := mul_mem (inv_mem a.2) b.2
    set p := (a : G)⁻¹ * (k * a * k⁻¹) with hp
    have hpT : p ∈ T₁ := mul_mem (inv_mem a.2) (hkT' _ a.2)
    have e : ((a : G)⁻¹ * (k * a * k⁻¹))⁻¹ * ((b : G)⁻¹ * (k * b * k⁻¹)) =
        (p⁻¹ * x⁻¹ * p⁻¹⁻¹ * x⁻¹⁻¹) * (x⁻¹ * (k * x * k⁻¹)) := by
      rw [hp, hx]; group
    rw [e] at hab
    exact hfpf x hxT (by
      have := mul_mem (inv_mem (hcomm _ (inv_mem hpT) _ (inv_mem hxT))) hab
      rwa [inv_mul_cancel_left] at this)
  have hsurj : Function.Surjective ψ' := Finite.injective_iff_surjective.mp hinj
  obtain ⟨c, hc⟩ := hsurj (⟨z, hz⟩ : T₁)
  induction c using QuotientGroup.induction_on with | H y => ?_
  change (ψ y : T₁ ⧸ A') = ((⟨z, hz⟩ : T₁) : T₁ ⧸ A') at hc
  rw [QuotientGroup.eq, mem_subgroupOf] at hc
  exact ⟨y, y.2, by simpa [hψ] using hc⟩

end U3C1

namespace U3C1Stage

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}
  {d : G} {V U U₁ : Subgroup G} {k : ℕ}

section Branch

variable (h : U3C1Stage G L f t T d V U U₁ k)
include h

theorem comm_mem_V : ∀ x ∈ U, ∀ y ∈ U, x * y * x⁻¹ * y⁻¹ ∈ V := by
  refine SzC1.comm_mem_of_generators_normal (P := fun g => g ∈ U₁ ∨ g = t)
    (fun S hS => by
      rw [← h.sup_eq]
      exact sup_le (fun x hx => hS x (Or.inl hx)) (zpowers_le.mpr (hS t (Or.inr rfl))))
    (fun g hg => hg.elim (fun hg => h.U₁_le hg) (fun hg => hg ▸ h.t_mem_U))
    (fun y hy b hb => h.conj_V_of_mem_U hy hb) ?_
  rintro g (hg | hg) g' (hg' | hg')
  · exact h.le (h.comm_mem_szA₁ g hg g' hg')
  · rw [hg']
    exact h.comm_t_mem (h.U₁_le hg)
  · rw [hg, show t * g' * t⁻¹ * g'⁻¹ = (g' * t * g'⁻¹ * t⁻¹)⁻¹ by group]
    exact inv_mem (h.comm_t_mem (h.U₁_le hg'))
  · rw [hg, hg', show t * t * t⁻¹ * t⁻¹ = (1 : G) by group]
    exact one_mem _

theorem conj_V_of_mem_normalizer {g : G} (hg : g ∈ normalizer (U : Set G)) {r : G} (hr : r ∈ V) :
    g * r * g⁻¹ ∈ V := by
  obtain ⟨K, _, _, _, v, μ, hK, hc, hμ⟩ := h.coords
  obtain ⟨y, hy, rfl⟩ := h.exists_comm_t_eq hK hc hμ hr
  have hgU : ∀ x ∈ U, g * x * g⁻¹ ∈ U := fun x hx => (mem_normalizer_iff.mp hg x).mp hx
  rw [show g * (y * t * y⁻¹ * t⁻¹) * g⁻¹ =
    (g * y * g⁻¹) * (g * t * g⁻¹) * (g * y * g⁻¹)⁻¹ * (g * t * g⁻¹)⁻¹ by group]
  exact h.comm_mem_V _ (hgU y (h.U₁_le hy)) _ (hgU t h.t_mem_U)

theorem normalizer_U_le_normalizer_V : normalizer (U : Set G) ≤ normalizer (V : Set G) :=
  fun _ hg => mem_normalizer_of_forall_inv_mul_mul_mem fun _ hr => by
    simpa using h.conj_V_of_mem_normalizer (inv_mem hg) hr

theorem conj_t_inv_of_normalizer {g : G} (hg : g ∈ normalizer (U : Set G)) {r : G} (hr : r ∈ V) :
    g * t * g⁻¹ * r * (g * t * g⁻¹)⁻¹ = r⁻¹ := by
  have hr' : g⁻¹ * r * g ∈ V := by simpa using h.conj_V_of_mem_normalizer (inv_mem hg) hr
  calc g * t * g⁻¹ * r * (g * t * g⁻¹)⁻¹ = g * (t * (g⁻¹ * r * g) * t⁻¹) * g⁻¹ := by group
    _ = r⁻¹ := by rw [h.inv _ hr']; group

theorem T_le_U : T ≤ U := by
  rw [h.T_eq]
  exact sup_le (h.T₁_le_U₁.trans h.U₁_le) (zpowers_le.mpr h.t_mem_U)

theorem mem_U_of_comm_t_mem {P : Subgroup G} (hP2 : IsPGroup 2 P) (hUP : U ≤ P) {g : G}
    (hgP : g ∈ P) (hσ : g * t * g⁻¹ * t⁻¹ ∈ V) : g ∈ U := by
  obtain ⟨K, _, _, _, v, μ, hK, hc, hμ⟩ := h.coords
  obtain ⟨w, hw, hwσ⟩ := h.exists_comm_t_eq hK hc hμ hσ
  have hcent : w⁻¹ * g ∈ centralizer ({t} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have e : w * t * w⁻¹ = g * t * g⁻¹ := by
      calc w * t * w⁻¹ = (w * t * w⁻¹ * t⁻¹) * t := by group
        _ = (g * t * g⁻¹ * t⁻¹) * t := by rw [hwσ]
        _ = g * t * g⁻¹ := by group
    calc w⁻¹ * g * t = w⁻¹ * (g * t * g⁻¹) * g := by group
      _ = w⁻¹ * (w * t * w⁻¹) * g := by rw [e]
      _ = t * (w⁻¹ * g) := by group
  have hTU := h.T_le_U
  obtain ⟨P₀, hP₀⟩ := h.start.sylow
  have hmax := P₀.is_maximal' (Q := P.subgroupOf (centralizer ({t} : Set G)))
    hP2.comap_subtype (by
      rw [hP₀]
      intro z hz
      exact mem_subgroupOf.mpr (hUP (hTU (mem_subgroupOf.mp hz))))
  have hwg : (⟨w⁻¹ * g, hcent⟩ : centralizer ({t} : Set G)) ∈ (P₀ : Subgroup _) := by
    rw [← hmax]
    exact mem_subgroupOf.mpr (mul_mem (inv_mem (hUP (h.U₁_le hw))) hgP)
  rw [hP₀, mem_subgroupOf] at hwg
  simpa using mul_mem (h.U₁_le hw) (hTU hwg)

theorem exists_conj_escape (hU : ¬ ∃ S : Sylow 2 G, (S : Subgroup G) = U) :
    ∃ g ∈ normalizer (U : Set G), g ∉ U ∧ g * t * g⁻¹ * t ∈ U₁ ∧
      g * t * g⁻¹ ∉ szR (szT₁ L T) V t := by
  obtain ⟨g, hgN, hgU, P, hP2, hUP, hgP⟩ :=
    exists_normalizer_not_mem_of_not_isSylow h.isPGroup_U hU
  have hxU : g * t * g⁻¹ ∈ U := (mem_normalizer_iff.mp hgN t).mp h.t_mem_U
  have hxU₁ := h.conj_not_mem_U₁ g
  refine ⟨g, hgN, hgU, (h.mem_or_mul_t_mem hxU).resolve_left hxU₁, fun hxR => ?_⟩
  rcases CFSG.SeitzReduction.mem_or_mul_mem_of_mem_sup_zpowers h.t_mul_self
    h.t_mem_normalizer_sup hxR with h1 | h1
  · exact hxU₁ (h.sup_le_U₁ h1)
  obtain ⟨y, hy, r, hr, hyr⟩ := h.exists_mul_of_mem_sup h1
  have hx2 : (g * t * g⁻¹) ^ 2 = 1 := by
    rw [sq, show g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ by group, h.t_mul_self,
      mul_one, mul_inv_cancel]
  have hxe : g * t * g⁻¹ = y * r * t := by
    rw [← hyr, mul_assoc (g * t * g⁻¹) t t, h.t_mul_self, mul_one]
  rw [hxe, h.sq_mul_mul_t hy hr] at hx2
  have hyA := h.mem_szA₁_of_sq_eq_one hy hx2
  refine hgU (h.mem_U_of_comm_t_mem hP2 hUP hgP ?_)
  rw [show g * t * g⁻¹ * t⁻¹ = y * r by rw [hxe]; group]
  exact mul_mem (h.le hyA) hr

theorem false_of_mu_one (hμV : ¬ U₁ ≤ centralizer (V : Set G)) : False := by
  by_cases hU : ∃ S : Sylow 2 G, (S : Subgroup G) = U
  · exact h.false_of_isSylow hU
  obtain ⟨g, hgN, -, hxt, hxR⟩ := h.exists_conj_escape hU
  have hxtV : g * t * g⁻¹ * t ∈ centralizer (V : Set G) := by
    refine mem_centralizer_iff.mpr fun r hr => ?_
    have e : (g * t * g⁻¹ * t) * r * (g * t * g⁻¹ * t)⁻¹ = r := by
      calc (g * t * g⁻¹ * t) * r * (g * t * g⁻¹ * t)⁻¹ =
            (g * t * g⁻¹) * (t * r * t⁻¹) * (g * t * g⁻¹)⁻¹ := by group
        _ = ((g * t * g⁻¹) * r * (g * t * g⁻¹)⁻¹)⁻¹ := by rw [h.inv r hr]; group
        _ = r := by rw [h.conj_t_inv_of_normalizer hgN hr, inv_inv]
    calc r * (g * t * g⁻¹ * t) =
          ((g * t * g⁻¹ * t) * r * (g * t * g⁻¹ * t)⁻¹) * (g * t * g⁻¹ * t) := by rw [e]
      _ = (g * t * g⁻¹ * t) * r := by group
  have hmem := h.mem_sup_of_mem_centralizer_V hμV hxt hxtV
  refine hxR ?_
  rw [show g * t * g⁻¹ = (g * t * g⁻¹ * t) * t by
    rw [mul_assoc (g * t * g⁻¹) t t, h.t_mul_self, mul_one]]
  exact mul_mem (sup_le_szR _ _ _ hmem) (mem_szR_right _ _ _)

theorem le_centralizer_V : U₁ ≤ centralizer (V : Set G) := by
  by_contra hμV
  exact h.false_of_mu_one hμV

theorem exists_sq_ne_one : ∃ r ∈ V, r ^ 2 ≠ 1 := by
  by_contra hne
  push Not at hne
  have hle : V ≤ szA₁ (szT₁ L T) := fun r hr => h.omega r hr (hne r hr)
  have h1 := Subgroup.card_le_of_le hle
  rw [h.card, h.card_szA₁] at h1
  have h2 : 2 ^ f < (2 ^ f) ^ (k + 1) := by
    calc 2 ^ f = (2 ^ f) ^ 1 := (pow_one _).symm
      _ < (2 ^ f) ^ (k + 1) := Nat.pow_lt_pow_right h.one_lt_q (by have := h.one_le; omega)
  omega

theorem conj_mem_U₁_of_normalizer (hμ : U₁ ≤ centralizer (V : Set G)) {g : G}
    (hg : g ∈ normalizer (U : Set G)) {w : G} (hw : w ∈ U₁) : g * w * g⁻¹ ∈ U₁ := by
  have hzU : g * w * g⁻¹ ∈ U := (mem_normalizer_iff.mp hg w).mp (h.U₁_le hw)
  refine (h.mem_or_mul_t_mem hzU).resolve_right fun hzt => ?_
  obtain ⟨r, hr, hr2⟩ := h.exists_sq_ne_one
  have hzV : (g * w * g⁻¹) * r = r * (g * w * g⁻¹) := by
    have hr' : g⁻¹ * r * g ∈ V := by simpa using h.conj_V_of_mem_normalizer (inv_mem hg) hr
    have e := mem_centralizer_iff.mp (hμ hw) _ hr'
    calc g * w * g⁻¹ * r = g * (w * (g⁻¹ * r * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * r * g) * w) * g⁻¹ := by rw [e]
      _ = r * (g * w * g⁻¹) := by group
  have hztV := (mem_centralizer_iff.mp (hμ hzt) r hr).symm
  have htr : t * r = r * t := by
    have e1 : (g * w * g⁻¹) * (t * r) = (g * w * g⁻¹) * (r * t) := by
      calc (g * w * g⁻¹) * (t * r) = (g * w * g⁻¹ * t) * r := by group
        _ = r * (g * w * g⁻¹ * t) := hztV
        _ = (r * (g * w * g⁻¹)) * t := by group
        _ = (g * w * g⁻¹ * r) * t := by rw [hzV]
        _ = (g * w * g⁻¹) * (r * t) := by group
    exact mul_left_cancel e1
  apply hr2
  have e1 : t * r * t⁻¹ = r := by rw [htr, mul_inv_cancel_right]
  rw [h.inv r hr] at e1
  rw [sq]
  nth_rewrite 1 [← e1]
  exact inv_mul_cancel r

end Branch

section Lambda

variable {K : Type} [Field K] [Fintype K] [CharP K 2] {v : G → K}
  {μ : K} (h : U3C1Stage G L f t T d V U U₁ k) (hK : Fintype.card K = 2 ^ f)
  (hc : U3A₁Coords (szA₁ (szT₁ L T)) d v μ)
include h hK hc

theorem S_conj_d_pow (n : ℕ) {x : G} (hx : x ∈ U₁) :
    (d ^ n)⁻¹ * x * d ^ n ∈ U₁ ∧
      v ((((d ^ n)⁻¹ * x * d ^ n) * t * ((d ^ n)⁻¹ * x * d ^ n)⁻¹ * t⁻¹) ^ 2 ^ k) =
        μ ^ n * v ((x * t * x⁻¹ * t⁻¹) ^ 2 ^ k) := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    have e : (d ^ (n + 1))⁻¹ * x * d ^ (n + 1) = d⁻¹ * ((d ^ n)⁻¹ * x * d ^ n) * d := by
      rw [pow_succ]
      group
    rw [e]
    exact ⟨h.conj_d_mem_U₁ ih.1, by rw [h.S_conj_d hK hc ih.1, ih.2, pow_succ]; ring⟩

theorem S_inv {x : G} (hx : x ∈ U₁) :
    v ((x⁻¹ * t * x⁻¹⁻¹ * t⁻¹) ^ 2 ^ k) = v ((x * t * x⁻¹ * t⁻¹) ^ 2 ^ k) := by
  have h1 := h.S_mul hK hc (inv_mem hx) hx
  rw [inv_mul_cancel, show (1 : G) * t * (1 : G)⁻¹ * t⁻¹ = 1 by group, one_pow, hc.v_one] at h1
  have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
  linear_combination -h1 - v ((x * t * x⁻¹ * t⁻¹) ^ 2 ^ k) * h2K

theorem inv_mul_conj_mem_sup {m : ℕ} (hm : ∀ b ∈ szA₁ (szT₁ L T), d ^ m * b * (d ^ m)⁻¹ = b)
    {x : G} (hx : x ∈ U₁) : x⁻¹ * (d ^ m * x * (d ^ m)⁻¹) ∈ szT₁ L T ⊔ V := by
  have hμm := hc.pow_eq_one_of_centralizes hm
  have hx' : d ^ m * x * (d ^ m)⁻¹ ∈ U₁ :=
    (mem_normalizer_iff.mp (pow_mem h.d_mem_U₁ m) x).mp hx
  have h1 := (h.S_conj_d_pow hK hc m hx').2
  rw [show (d ^ m)⁻¹ * (d ^ m * x * (d ^ m)⁻¹) * d ^ m = x by group, hμm, one_mul] at h1
  refine h.mem_sup_of_S_eq_zero hK hc (mul_mem (inv_mem hx) hx') ?_
  rw [h.S_mul hK hc (inv_mem hx) hx', h.S_inv hK hc hx, h1, CharTwo.add_self_eq_zero]

end Lambda

theorem le_sup_inf_centralizer (h : U3C1Stage G L f t T d V U U₁ k)
    (hfpf : U3C1TorusFpf L T d) :
    U₁ ≤ szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G)) := by
  obtain ⟨K, _, _, _, v, μ, hK, hc, -⟩ := h.coords
  obtain ⟨m, hmA, hmfix⟩ := hfpf
  set e := d ^ m with he
  have heT : e ∈ normalizer (szT₁ L T : Set G) := pow_mem h.d_norm.1.2 m
  have heV : e ∈ normalizer (V : Set G) := pow_mem h.d_norm.1.1 m
  have hcomm : ∀ y ∈ szT₁ L T, ∀ y' ∈ szT₁ L T, y * y' * y⁻¹ * y'⁻¹ ∈ szA₁ (szT₁ L T) :=
    fun y hy y' hy' => h.comm_T₁_mem hy hy'
  have hcen : ∀ a ∈ szA₁ (szT₁ L T), ∀ y ∈ szT₁ L T, a * y = y * a := fun a ha y hy =>
    (mem_centralizer_iff.mp (mem_szA₁.mp ha).2 y hy).symm
  intro x hx
  have hxU := h.U₁_le hx
  obtain ⟨z, hz, r, hr, hzr⟩ :=
    h.exists_mul_of_mem_sup (h.inv_mul_conj_mem_sup hK hc hmA hx)
  obtain ⟨y, hy, hyA⟩ := U3C1.exists_inv_mul_conj_of_fixedPointFree hcomm heT hmA hmfix
    (inv_mem hz)
  set ψ := y⁻¹ * (e * y * e⁻¹) with hψ
  have hψT : ψ ∈ szT₁ L T :=
    mul_mem (inv_mem hy) ((mem_normalizer_iff.mp heT y).mp hy)
  set c := ψ⁻¹ * z⁻¹ with hcdef
  have hz' : z = c⁻¹ * ψ⁻¹ := by rw [hcdef]; group
  set a := ψ⁻¹ * (x⁻¹ * ψ * x⁻¹⁻¹) with hadef
  have haA : a ∈ szA₁ (szT₁ L T) := h.conj_T₁ x⁻¹ (inv_mem hxU) ψ hψT
  have hxψ : x⁻¹ * ψ * x = ψ * a := by rw [hadef]; group
  set w := y * x with hw
  have hwU₁ : w ∈ U₁ := mul_mem (h.T₁_le_U₁ hy) hx
  have hwU := h.U₁_le hwU₁
  have hs : w⁻¹ * (e * w * e⁻¹) ∈ V := by
    have e1 : w⁻¹ * (e * w * e⁻¹) = (x⁻¹ * ψ * x) * (x⁻¹ * (e * x * e⁻¹)) := by
      rw [hw, hψ]; group
    rw [e1, hxψ, hzr, hz']
    have hcA : c ∈ szA₁ (szT₁ L T) := hyA
    have e2 : ψ * a * (c⁻¹ * ψ⁻¹ * r) = (a * c⁻¹) * r := by
      have h3 : ψ * (a * c⁻¹) = (a * c⁻¹) * ψ :=
        (hcen _ (mul_mem haA (inv_mem hcA)) ψ hψT).symm
      calc ψ * a * (c⁻¹ * ψ⁻¹ * r) = (ψ * (a * c⁻¹)) * ψ⁻¹ * r := by group
        _ = ((a * c⁻¹) * ψ) * ψ⁻¹ * r := by rw [h3]
        _ = (a * c⁻¹) * r := by group
    rw [e2]
    exact mul_mem (h.le (mul_mem haA (inv_mem hcA))) hr
  set s := w⁻¹ * (e * w * e⁻¹) with hsdef
  have hews : e * w * e⁻¹ = w * s := by rw [hsdef]; group
  have hinv : ∀ y' ∈ szT₁ L T, (e * y' * e⁻¹)⁻¹ * (w * (e * y' * e⁻¹) * w⁻¹) =
      y'⁻¹ * (w * y' * w⁻¹) := by
    intro y' hy'
    have hey' : e * y' * e⁻¹ ∈ szT₁ L T := (mem_normalizer_iff.mp heT y').mp hy'
    have hδ := h.conj_T₁ w hwU y' hy'
    have hsc : s * (e * y' * e⁻¹) = (e * y' * e⁻¹) * s := (h.V_comm hs hey').symm
    have e1 : e * (y'⁻¹ * (w * y' * w⁻¹)) * e⁻¹ =
        (e * y' * e⁻¹)⁻¹ * ((e * w * e⁻¹) * (e * y' * e⁻¹) * (e * w * e⁻¹)⁻¹) := by group
    rw [hews] at e1
    have e2 : (e * y' * e⁻¹)⁻¹ * (w * s * (e * y' * e⁻¹) * (w * s)⁻¹) =
        (e * y' * e⁻¹)⁻¹ * (w * (e * y' * e⁻¹) * w⁻¹) := by
      rw [show w * s * (e * y' * e⁻¹) * (w * s)⁻¹ = w * (s * (e * y' * e⁻¹)) * s⁻¹ * w⁻¹ by
        group, hsc]
      group
    rw [← e2, ← e1, hmA _ hδ]
  have hwC := U3C1.commute_of_fixedPointFree hcomm heT hmA hmfix (h.conj_szA₁ w hwU)
    (h.conj_T₁ w hwU) hinv
  have hwC' : w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G) :=
    mem_inf.mpr ⟨hwU₁, mem_centralizer_iff.mpr fun y' hy' => by
      calc y' * w = (w * y' * w⁻¹) * w := by rw [hwC y' hy']
        _ = w * y' := by group⟩
  have hx' : x = y⁻¹ * w := by rw [hw]; group
  rw [hx']
  exact mul_mem (mem_sup_left (inv_mem hy)) (mem_sup_right hwC')

theorem reduction (h : U3C1Stage G L f t T d V U U₁ k)
    (hfpf : U3C1TorusFpf L T d) :
    (¬ ∃ S : Sylow 2 G, (S : Subgroup G) = U) ∧ U₁ ≤ centralizer (V : Set G) ∧
      U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G)) :=
  ⟨fun hU => h.false_of_isSylow hU, h.le_centralizer_V,
    le_antisymm (h.le_sup_inf_centralizer hfpf) (sup_le h.T₁_le_U₁ inf_le_left)⟩

end U3C1Stage

end CFSG.SeitzReduction.RankOne
