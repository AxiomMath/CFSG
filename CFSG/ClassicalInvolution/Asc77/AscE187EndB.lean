module

public import CFSG.ClassicalInvolution.Asc77.AscE187EndA
public import CFSG.ClassicalInvolution.Asc77.AscE187Sq

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem twin_conj (hΩ : HypOmegaMod p f Ω) {M : Subgroup G} {t δ : G} (hM : M ∈ Ω)
    (hMt : IsUniqueInvolution M t) (hδ : δ * t = t * δ) :
    conjSub δ M ∈ Ω ∧ IsUniqueInvolution (conjSub δ M) t := by
  refine ⟨hΩ.conjInvariant δ M hM, ?_⟩
  have := hMt.conj δ
  rwa [show δ * t * δ⁻¹ = t by rw [hδ]; group] at this

theorem inv_eq_self_of_sq {δ : G} (h : δ * δ = 1) : δ⁻¹ = δ := inv_eq_of_mul_eq_one_right h

theorem mul_mem_centralizer_of_swap {δ a b : G} (hδ : δ * δ = 1) (hab : δ * a * δ⁻¹ = b)
    (hc : a * b = b * a) : a * b ∈ Subgroup.centralizer ({δ} : Set G) := by
  have hba : δ * b * δ⁻¹ = a := by
    rw [← hab]
    have : δ * (δ * a * δ⁻¹) * δ⁻¹ = (δ * δ) * a * (δ * δ)⁻¹ := by group
    rw [this, hδ]
    group
  have e : δ * (a * b) * δ⁻¹ = a * b := by
    calc δ * (a * b) * δ⁻¹ = (δ * a * δ⁻¹) * (δ * b * δ⁻¹) := by group
      _ = b * a := by rw [hab, hba]
      _ = a * b := hc.symm
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (mul_inv_eq_iff_eq_mul.mp e).symm

section EndNone

variable [Finite G]

theorem E187C.endgame_none_of (hcI : ConjInvariant Ω)
    (hlesq : ∀ {M L : Subgroup G}, M ∈ Ω → (∀ x ∈ M, x * x ∈ L) → M ≤ L)
    (hfour4 : ∀ {M : Subgroup G}, M ∈ Ω → ∃ u ∈ M, orderOf u = 4)
    (hcmtw : ∀ {K J : Subgroup G} {z : G}, K ∈ Ω → J ∈ Ω → K ≠ J → IsUniqueInvolution K z →
      IsUniqueInvolution J z → Commutes K J)
    {H : Subgroup G} {t : G}
    (hbad : ∀ M ∈ Ω, IsUniqueInvolution M t → ∀ u ∈ M, orderOf u = 4 → u ∉ H)
    {K₁ : Subgroup G} (hK₁ : K₁ ∈ Ω) (ht : IsUniqueInvolution K₁ t) {d₁ d₂ : G}
    (g₁ : GoodInv H t d₁) (g₂ : GoodInv H t d₂) (g₃ : GoodInv H t (d₁ * d₂))
    (hc : d₁ * d₂ = d₂ * d₁) (m₁ : conjSub d₁ K₁ ≠ K₁) (m₂ : conjSub d₂ K₁ ≠ K₁)
    (m₃ : conjSub (d₁ * d₂) K₁ ≠ K₁) : False := by
  have htc : ∀ {δ : G}, δ * t = t * δ → conjSub δ K₁ ∈ Ω ∧ IsUniqueInvolution (conjSub δ K₁) t :=
    fun {δ} hδ => ⟨hcI δ K₁ hK₁, by
      have := ht.conj δ
      rwa [show δ * t * δ⁻¹ = t by rw [hδ]; group] at this⟩
  obtain ⟨hK₂Ω, hK₂t⟩ := htc g₁.comm_t
  obtain ⟨hK₃Ω, hK₃t⟩ := htc g₂.comm_t
  have h23 : conjSub d₁ K₁ ≠ conjSub d₂ K₁ := by
    intro h
    apply m₃
    rw [conjSub_mul, ← h, ← conjSub_mul, g₁.sq, conjSub_one]
  have c12 : Commutes K₁ (conjSub d₁ K₁) :=
    hcmtw hK₁ hK₂Ω (Ne.symm m₁) ht hK₂t
  have c13 : Commutes K₁ (conjSub d₂ K₁) :=
    hcmtw hK₁ hK₃Ω (Ne.symm m₂) ht hK₃t
  have c23 : Commutes (conjSub d₁ K₁) (conjSub d₂ K₁) :=
    hcmtw hK₂Ω hK₃Ω h23 hK₂t hK₃t
  have hdd : d₁ * d₂ * d₁ = d₂ := by
    calc d₁ * d₂ * d₁ = d₁ * (d₂ * d₁) := mul_assoc _ _ _
      _ = d₁ * (d₁ * d₂) := by rw [hc]
      _ = d₂ := by rw [← mul_assoc, g₁.sq, one_mul]
  have key : ∀ x ∈ K₁, d₂ * (x * x) * d₂⁻¹ ∈ H := by
    intro x hx
    have hx₂ : d₁ * x * d₁⁻¹ ∈ conjSub d₁ K₁ := conj_mem_conjSub hx
    have hx₃ : d₂ * x * d₂⁻¹ ∈ conjSub d₂ K₁ := conj_mem_conjSub hx
    have hxx₂ : x * (d₁ * x * d₁⁻¹) = (d₁ * x * d₁⁻¹) * x := c12 x hx _ hx₂
    have hxx₃ : x * (d₂ * x * d₂⁻¹) = (d₂ * x * d₂⁻¹) * x := c13 x hx _ hx₃
    have hx₂₃ : (d₁ * x * d₁⁻¹) * (d₂ * x * d₂⁻¹) = (d₂ * x * d₂⁻¹) * (d₁ * x * d₁⁻¹) :=
      c23 _ hx₂ _ hx₃
    have n₁ : x * (d₁ * x * d₁⁻¹) ∈ H :=
      g₁.cent (mul_mem_centralizer_of_swap g₁.sq rfl hxx₂)
    have n₂ : x * (d₂ * x * d₂⁻¹) ∈ H :=
      g₂.cent (mul_mem_centralizer_of_swap g₂.sq rfl hxx₃)
    have hswap : (d₁ * d₂) * (d₁ * x * d₁⁻¹) * (d₁ * d₂)⁻¹ = d₂ * x * d₂⁻¹ := by
      have : (d₁ * d₂) * (d₁ * x * d₁⁻¹) * (d₁ * d₂)⁻¹ = (d₁ * d₂ * d₁) * x * (d₁ * d₂ * d₁)⁻¹ := by
        group
      rw [this, hdd]
    have n₃ : (d₁ * x * d₁⁻¹) * (d₂ * x * d₂⁻¹) ∈ H :=
      g₃.cent (mul_mem_centralizer_of_swap g₃.sq hswap hx₂₃)
    set x₂ := d₁ * x * d₁⁻¹ with hx₂def
    set x₃ := d₂ * x * d₂⁻¹ with hx₃def
    have e1 : x * x₂ * (x * x₃)⁻¹ = x₂ * x₃⁻¹ := by
      have hxi : x * x₃⁻¹ = x₃⁻¹ * x := (Commute.inv_right (show Commute x x₃ from hxx₃)).eq
      calc x * x₂ * (x * x₃)⁻¹ = x * x₂ * x₃⁻¹ * x⁻¹ := by group
        _ = x₂ * x * x₃⁻¹ * x⁻¹ := by rw [hxx₂]
        _ = x₂ * (x * x₃⁻¹) * x⁻¹ := by group
        _ = x₂ * (x₃⁻¹ * x) * x⁻¹ := by rw [hxi]
        _ = x₂ * x₃⁻¹ := by group
    have e2 : x₃ * x₃ = (x₂ * x₃) * (x₂ * x₃⁻¹)⁻¹ := by
      have hc3 : x₂ * (x₃ * x₃) = (x₃ * x₃) * x₂ := (Commute.mul_right
        (show Commute x₂ x₃ from hx₂₃) (show Commute x₂ x₃ from hx₂₃)).eq
      calc x₃ * x₃ = x₂ * (x₃ * x₃) * x₂⁻¹ := by rw [hc3]; group
        _ = (x₂ * x₃) * (x₂ * x₃⁻¹)⁻¹ := by group
    have : x₃ * x₃ ∈ H := by
      rw [e2, ← e1]
      exact H.mul_mem n₃ (H.inv_mem (H.mul_mem n₁ (H.inv_mem n₂)))
    have e3 : d₂ * (x * x) * d₂⁻¹ = x₃ * x₃ := by rw [hx₃def]; group
    rw [e3]
    exact this
  have hle : K₁ ≤ conjSub d₂⁻¹ H := by
    refine hlesq hK₁ fun x hx => ?_
    rw [mem_conjSub_iff, inv_inv]
    exact key x hx
  have hK₃H : conjSub d₂ K₁ ≤ H := by
    have := conjSub_mono (n := d₂) hle
    rwa [conjSub_conjSub_inv] at this
  obtain ⟨u, hu, hu4⟩ := hfour4 hK₃Ω
  exact hbad _ hK₃Ω hK₃t u hu hu4 (hK₃H hu)



theorem endgame_none (hp : p ≠ 2) (_hq : 5 ≤ p ^ f) (hΩ : HypOmega p f Ω) {H : Subgroup G} {t : G}
    (hbad : ∀ M ∈ Ω, IsUniqueInvolution M t → ∀ u ∈ M, orderOf u = 4 → u ∉ H)
    {K₁ : Subgroup G} (hK₁ : K₁ ∈ Ω) (ht : IsUniqueInvolution K₁ t) {d₁ d₂ : G}
    (g₁ : GoodInv H t d₁) (g₂ : GoodInv H t d₂) (g₃ : GoodInv H t (d₁ * d₂))
    (hc : d₁ * d₂ = d₂ * d₁) (m₁ : conjSub d₁ K₁ ≠ K₁) (m₂ : conjSub d₂ K₁ ≠ K₁)
    (m₃ : conjSub (d₁ * d₂) K₁ ≠ K₁) : False := by
  exact E187C.endgame_none_of hΩ.toMod.conjInvariant
    (fun hM h => le_of_sq_mem (hΩ.toMod.isPerfect hM) h)
    (fun hM => hΩ.toMod.exists_orderOf_four_of_mem hp hM)
    (fun hK hJ hKJ hzK hzJ => hΩ.commutes_of_twin hK hJ hKJ hzK hzJ)
    hbad hK₁ ht g₁ g₂ g₃ hc m₁ m₂ m₃

end EndNone

section EndOne

variable [Finite G]

def commE (δ x : G) : G := x * (δ * x * δ⁻¹)⁻¹

omit [Finite G] in
theorem conj_mul_commE (δ y x : G) : y * commE δ x * y⁻¹ = commE δ (y * x) * (commE δ y)⁻¹ := by
  unfold commE
  group

def commSub (K : Subgroup G) (δ : G) : Subgroup G :=
  Subgroup.closure (Set.range fun x : ↥K => commE δ (x : G))

omit [Finite G] in
theorem commSub_le (K : Subgroup G) {δ : G} (hδ : conjSub δ K = K) : commSub K δ ≤ K := by
  refine (Subgroup.closure_le K).mpr ?_
  rintro _ ⟨x, rfl⟩
  have h1 : δ * (x : G) * δ⁻¹ ∈ K := by
    have := conj_mem_conjSub (n := δ) x.2
    rwa [hδ] at this
  exact K.mul_mem x.2 (K.inv_mem h1)

omit [Finite G] in
theorem commSub_normal (K : Subgroup G) (δ : G) :
    ∀ y ∈ K, ∀ w ∈ commSub K δ, y * w * y⁻¹ ∈ commSub K δ := by
  intro y hy w hw
  induction hw using Subgroup.closure_induction with
  | mem w hw =>
    obtain ⟨x, rfl⟩ := hw
    rw [conj_mul_commE]
    refine Subgroup.mul_mem _ (Subgroup.subset_closure ⟨⟨y * x, K.mul_mem hy x.2⟩, rfl⟩)
      (Subgroup.inv_mem _ (Subgroup.subset_closure ⟨⟨y, hy⟩, rfl⟩))
  | one => simp
  | mul a b _ _ ha hb =>
    have : y * (a * b) * y⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ ha hb
  | inv a _ ha =>
    have : y * a⁻¹ * y⁻¹ = (y * a * y⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ ha

theorem E187C.endgame_one_of {t : G} (hcI : ConjInvariant Ω)
    (hlesq : ∀ {M L : Subgroup G}, M ∈ Ω → (∀ x ∈ M, x * x ∈ L) → M ≤ L)
    (hfour4 : ∀ {M : Subgroup G}, M ∈ Ω → ∃ u ∈ M, orderOf u = 4)
    (hcmtw : ∀ {K J : Subgroup G} {z : G}, K ∈ Ω → J ∈ Ω → K ≠ J → IsUniqueInvolution K z →
      IsUniqueInvolution J z → Commutes K J)
    (hcen : ∀ {K₀ : Subgroup G} {w : G}, K₀ ∈ Ω → IsUniqueInvolution K₀ t → w ∈ K₀ →
      (∀ y ∈ K₀, w * y = y * w) → w * w = 1)
    (hdich : ∀ {K₀ : Subgroup G}, K₀ ∈ Ω → ∀ E : Subgroup ↥K₀, E.Normal →
      E ≤ Subgroup.center ↥K₀ ∨ ∃ u₀ : ↥K₀, u₀ ∈ E ∧ orderOf u₀ = 4)
    {H : Subgroup G}
    (hbad : ∀ M ∈ Ω, IsUniqueInvolution M t → ∀ u ∈ M, orderOf u = 4 → u ∉ H)
    {K₁ : Subgroup G} (hK₁ : K₁ ∈ Ω) (ht : IsUniqueInvolution K₁ t) {δ₀ δ₁ : G}
    (g₀ : GoodInv H t δ₀) (g₁ : GoodInv H t δ₁) (g₂ : GoodInv H t (δ₀ * δ₁))
    (hc : δ₀ * δ₁ = δ₁ * δ₀) (n₀ : conjSub δ₀ K₁ = K₁) (m₁ : conjSub δ₁ K₁ ≠ K₁) : False := by
  have htc : ∀ {δ : G}, δ * t = t * δ → conjSub δ K₁ ∈ Ω ∧ IsUniqueInvolution (conjSub δ K₁) t :=
    fun {δ} hδ => ⟨hcI δ K₁ hK₁, by
      have := ht.conj δ
      rwa [show δ * t * δ⁻¹ = t by rw [hδ]; group] at this⟩
  obtain ⟨hK₂Ω, hK₂t⟩ := htc g₁.comm_t
  have c12 : Commutes K₁ (conjSub δ₁ K₁) :=
    hcmtw hK₁ hK₂Ω (Ne.symm m₁) ht hK₂t
  have hφ : ∀ x ∈ K₁, δ₀ * x * δ₀⁻¹ ∈ K₁ := by
    intro x hx
    have := conj_mem_conjSub (n := δ₀) hx
    rwa [n₀] at this
  have key : ∀ x ∈ K₁, δ₁ * commE δ₀ x * δ₁⁻¹ ∈ H := by
    intro x hx
    have hx₂ : δ₁ * x * δ₁⁻¹ ∈ conjSub δ₁ K₁ := conj_mem_conjSub hx
    have hy₂ : δ₁ * (δ₀ * x * δ₀⁻¹) * δ₁⁻¹ ∈ conjSub δ₁ K₁ := conj_mem_conjSub (hφ x hx)
    have hxx₂ : x * (δ₁ * x * δ₁⁻¹) = (δ₁ * x * δ₁⁻¹) * x := c12 x hx _ hx₂
    have hxy₂ : x * (δ₁ * (δ₀ * x * δ₀⁻¹) * δ₁⁻¹) = (δ₁ * (δ₀ * x * δ₀⁻¹) * δ₁⁻¹) * x :=
      c12 x hx _ hy₂
    have n₁ : x * (δ₁ * x * δ₁⁻¹) ∈ H :=
      g₁.cent (mul_mem_centralizer_of_swap g₁.sq rfl hxx₂)
    have hswap : (δ₀ * δ₁) * x * (δ₀ * δ₁)⁻¹ = δ₁ * (δ₀ * x * δ₀⁻¹) * δ₁⁻¹ := by
      rw [hc]
      group
    have n₂ : x * (δ₁ * (δ₀ * x * δ₀⁻¹) * δ₁⁻¹) ∈ H :=
      g₂.cent (mul_mem_centralizer_of_swap g₂.sq hswap hxy₂)
    set a := δ₁ * x * δ₁⁻¹ with ha
    set b := δ₁ * (δ₀ * x * δ₀⁻¹) * δ₁⁻¹ with hb
    have e1 : x * a * (x * b)⁻¹ = a * b⁻¹ := by
      have hxi : x * b⁻¹ = b⁻¹ * x := (Commute.inv_right (show Commute x b from hxy₂)).eq
      calc x * a * (x * b)⁻¹ = x * a * b⁻¹ * x⁻¹ := by group
        _ = a * x * b⁻¹ * x⁻¹ := by rw [hxx₂]
        _ = a * (x * b⁻¹) * x⁻¹ := by group
        _ = a * (b⁻¹ * x) * x⁻¹ := by rw [hxi]
        _ = a * b⁻¹ := by group
    have e2 : δ₁ * commE δ₀ x * δ₁⁻¹ = a * b⁻¹ := by
      rw [ha, hb]
      unfold commE
      group
    rw [e2, ← e1]
    exact H.mul_mem n₁ (H.inv_mem n₂)
  have hEK : commSub K₁ δ₀ ≤ K₁ := commSub_le K₁ n₀
  have hEL : commSub K₁ δ₀ ≤ conjSub δ₁⁻¹ H := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨x, rfl⟩
    rw [SetLike.mem_coe, mem_conjSub_iff, inv_inv]
    exact key x x.2
  have hN : (commSub K₁ δ₀).subgroupOf K₁ |>.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := commSub_normal K₁ δ₀ (g : G) g.2 n hn
    simpa using this
  have hcase : (commSub K₁ δ₀).subgroupOf K₁ ≤ Subgroup.center ↥K₁ → False := by
    intro hcase
    have hcent : ∀ w ∈ commSub K₁ δ₀, ∀ y ∈ K₁, w * y = y * w := by
      intro w hw y hy
      have hwK : w ∈ K₁ := hEK hw
      have hmem : (⟨w, hwK⟩ : ↥K₁) ∈ (commSub K₁ δ₀).subgroupOf K₁ :=
        Subgroup.mem_subgroupOf.mpr hw
      have := Subgroup.mem_center_iff.mp (hcase hmem) ⟨y, hy⟩
      exact congrArg Subtype.val this.symm
    have hsq : ∀ x ∈ K₁, (x * x) * δ₀ = δ₀ * (x * x) := by
      intro x hx
      have hwE : commE δ₀ x ∈ commSub K₁ δ₀ := Subgroup.subset_closure ⟨⟨x, hx⟩, rfl⟩
      have hwK : commE δ₀ x ∈ K₁ := hEK hwE
      have hwc : ∀ y ∈ K₁, commE δ₀ x * y = y * commE δ₀ x := hcent _ hwE
      have hw2 : commE δ₀ x * commE δ₀ x = 1 := by
        exact hcen hK₁ ht hwK hwc
      have hφ' : δ₀ * x * δ₀⁻¹ = (commE δ₀ x)⁻¹ * x := by
        unfold commE
        group
      have hwx : (commE δ₀ x)⁻¹ * x = x * (commE δ₀ x)⁻¹ :=
        (Commute.inv_left (show Commute (commE δ₀ x) x from hwc x hx)).eq
      have hww : (commE δ₀ x)⁻¹ * (commE δ₀ x)⁻¹ = 1 := by
        rw [← mul_inv_rev, hw2, inv_one]
      have hxx : δ₀ * (x * x) * δ₀⁻¹ = x * x := by
        calc δ₀ * (x * x) * δ₀⁻¹ = (δ₀ * x * δ₀⁻¹) * (δ₀ * x * δ₀⁻¹) := by group
          _ = ((commE δ₀ x)⁻¹ * x) * ((commE δ₀ x)⁻¹ * x) := by rw [hφ']
          _ = (commE δ₀ x)⁻¹ * (x * (commE δ₀ x)⁻¹) * x := by group
          _ = (commE δ₀ x)⁻¹ * ((commE δ₀ x)⁻¹ * x) * x := by rw [hwx]
          _ = ((commE δ₀ x)⁻¹ * (commE δ₀ x)⁻¹) * (x * x) := by group
          _ = x * x := by rw [hww, one_mul]
      exact (mul_inv_eq_iff_eq_mul.mp hxx).symm
    have hK₁C : K₁ ≤ Subgroup.centralizer ({δ₀} : Set G) :=
      hlesq hK₁ fun x hx => by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact hsq x hx
    obtain ⟨u, hu, hu4⟩ := hfour4 hK₁
    exact hbad _ hK₁ ht u hu hu4 (g₀.cent (hK₁C hu))
  rcases hdich hK₁ _ hN with h | ⟨u₀, hu₀E, hu₀4⟩
  · exact (hcase h).elim
  ·
    have hu₀E' : (u₀ : G) ∈ commSub K₁ δ₀ := Subgroup.mem_subgroupOf.mp hu₀E
    have hmemH : δ₁ * (u₀ : G) * δ₁⁻¹ ∈ H := by
      have := hEL hu₀E'
      rw [mem_conjSub_iff, inv_inv] at this
      exact this
    have hord : orderOf (δ₁ * (u₀ : G) * δ₁⁻¹) = 4 := by
      have h1 : orderOf (δ₁ * (u₀ : G) * δ₁⁻¹) = orderOf (u₀ : G) := by
        simpa using (MulAut.conj δ₁).orderOf_eq (u₀ : G)
      rw [h1, Subgroup.orderOf_coe]
      exact hu₀4
    exact hbad _ hK₂Ω hK₂t (δ₁ * (u₀ : G) * δ₁⁻¹) (conj_mem_conjSub u₀.2) hord hmemH



theorem endgame_one (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmega p f Ω) {H : Subgroup G} {t : G}
    (hbad : ∀ M ∈ Ω, IsUniqueInvolution M t → ∀ u ∈ M, orderOf u = 4 → u ∉ H)
    {K₁ : Subgroup G} (hK₁ : K₁ ∈ Ω) (ht : IsUniqueInvolution K₁ t) {δ₀ δ₁ : G}
    (g₀ : GoodInv H t δ₀) (g₁ : GoodInv H t δ₁) (g₂ : GoodInv H t (δ₀ * δ₁))
    (hc : δ₀ * δ₁ = δ₁ * δ₀) (n₀ : conjSub δ₀ K₁ = K₁) (m₁ : conjSub δ₁ K₁ ≠ K₁) : False := by
  exact E187C.endgame_one_of hΩ.toMod.conjInvariant
    (fun hM h => le_of_sq_mem (hΩ.toMod.isPerfect hM) h)
    (fun hM => hΩ.toMod.exists_orderOf_four_of_mem hp hM)
    (fun hK hJ hKJ hzK hzJ => hΩ.commutes_of_twin hK hJ hKJ hzK hzJ)
    (fun hK ht hw hwc => by
      rcases (hΩ.center_eq hp hq hK ht).2 _ hw hwc with h | h
      · rw [h, one_mul]
      · rw [h]
        exact ht.sq)
    (fun hM E hN => by
      obtain ⟨e⟩ := hΩ.nonempty_equiv_sl2 hM
      rcases normal_cases_of_equiv_sl2 (four_le_natCard_galoisField hq) e _ hN with h | h | h
      · exact Or.inl (by rw [h]; exact bot_le)
      · exact Or.inl h.le
      · obtain ⟨u, hu, hu4⟩ := hΩ.toMod.exists_orderOf_four_of_mem hp hM
        exact Or.inr ⟨⟨u, hu⟩, h ▸ Subgroup.mem_top _, by rw [Subgroup.orderOf_mk]; exact hu4⟩)
    hbad hK₁ ht g₀ g₁ g₂ hc n₀ m₁

end EndOne

section EndFour

variable [Finite G]

theorem E187C.endgame_four_exact_of {H : Subgroup G} {t : G}
    (hall : ∀ {K₁ : Subgroup G} {d₁ d₂ : G}, K₁ ∈ Ω → IsUniqueInvolution K₁ t →
      (∀ u ∈ K₁, orderOf u = 4 → u ∉ H) → GoodInv H t d₁ → GoodInv H t d₂ →
      GoodInv H t (d₁ * d₂) → d₁ * d₂ = d₂ * d₁ → conjSub d₁ K₁ = K₁ → conjSub d₂ K₁ = K₁ → False)
    (hone : ∀ {K₁ : Subgroup G} {δ₀ δ₁ : G}, K₁ ∈ Ω → IsUniqueInvolution K₁ t →
      GoodInv H t δ₀ → GoodInv H t δ₁ → GoodInv H t (δ₀ * δ₁) → δ₀ * δ₁ = δ₁ * δ₀ →
      conjSub δ₀ K₁ = K₁ → conjSub δ₁ K₁ ≠ K₁ → False)
    (hnone : ∀ {K₁ : Subgroup G} {d₁ d₂ : G}, K₁ ∈ Ω → IsUniqueInvolution K₁ t →
      GoodInv H t d₁ → GoodInv H t d₂ → GoodInv H t (d₁ * d₂) → d₁ * d₂ = d₂ * d₁ →
      conjSub d₁ K₁ ≠ K₁ → conjSub d₂ K₁ ≠ K₁ → conjSub (d₁ * d₂) K₁ ≠ K₁ → False)
    (hbad : ∀ M ∈ Ω, IsUniqueInvolution M t → ∀ u ∈ M, orderOf u = 4 → u ∉ H)
    {K₁ : Subgroup G} (hK₁ : K₁ ∈ Ω) (ht : IsUniqueInvolution K₁ t) {d₁ d₂ : G}
    (g₁ : GoodInv H t d₁) (g₂ : GoodInv H t d₂) (g₃ : GoodInv H t (d₁ * d₂))
    (hc : d₁ * d₂ = d₂ * d₁) : False := by
  have hdd : d₁ * d₂ * d₁ = d₂ := by
    calc d₁ * d₂ * d₁ = d₁ * (d₂ * d₁) := mul_assoc _ _ _
      _ = d₁ * (d₁ * d₂) := by rw [hc]
      _ = d₂ := by rw [← mul_assoc, g₁.sq, one_mul]
  have hdd' : d₁ * (d₁ * d₂) = d₂ := by rw [← mul_assoc, g₁.sq, one_mul]
  have hbadK : ∀ u ∈ K₁, orderOf u = 4 → u ∉ H := fun u hu hu4 => hbad K₁ hK₁ ht u hu hu4
  by_cases n₁ : conjSub d₁ K₁ = K₁
  · by_cases n₂ : conjSub d₂ K₁ = K₁
    · exact hall hK₁ ht hbadK g₁ g₂ g₃ hc n₁ n₂
    · have n₃ : conjSub (d₁ * d₂) K₁ ≠ K₁ := by
        intro h3
        apply n₂
        have : conjSub d₁ (conjSub d₂ K₁) = K₁ := by rw [← conjSub_mul]; exact h3
        calc conjSub d₂ K₁ = conjSub d₁⁻¹ (conjSub d₁ (conjSub d₂ K₁)) :=
              (conjSub_inv_conjSub d₁ _).symm
          _ = conjSub d₁⁻¹ K₁ := by rw [this]
          _ = K₁ := by
            have := congrArg (conjSub d₁⁻¹) n₁
            rw [conjSub_inv_conjSub] at this
            exact this.symm
      exact hone hK₁ ht g₁ g₂ g₃ hc n₁ n₂
  · by_cases n₂ : conjSub d₂ K₁ = K₁
    · have n₃ : conjSub (d₁ * d₂) K₁ ≠ K₁ := by
        intro h3
        apply n₁
        have h2' : conjSub d₂⁻¹ K₁ = K₁ := by
          have := congrArg (conjSub d₂⁻¹) n₂
          rw [conjSub_inv_conjSub] at this
          exact this.symm
        calc conjSub d₁ K₁ = conjSub (d₁ * d₂ * d₂⁻¹) K₁ := by group
          _ = conjSub (d₁ * d₂) (conjSub d₂⁻¹ K₁) := conjSub_mul _ _ _
          _ = K₁ := by rw [h2', h3]
      have g₃' : GoodInv H t (d₂ * d₁) := by rw [← hc]; exact g₃
      exact hone hK₁ ht g₂ g₁ g₃' hc.symm n₂ n₁
    · by_cases n₃ : conjSub (d₁ * d₂) K₁ = K₁
      · have g₂' : GoodInv H t (d₁ * d₂ * d₁) := by rw [hdd]; exact g₂
        refine hone hK₁ ht g₃ g₁ g₂' ?_ n₃ n₁
        rw [hdd, hdd']
      · exact hnone hK₁ ht g₁ g₂ g₃ hc n₁ n₂ n₃



theorem endgame_four_exact (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmega p f Ω) {H : Subgroup G}
    {t : G} (hbad : ∀ M ∈ Ω, IsUniqueInvolution M t → ∀ u ∈ M, orderOf u = 4 → u ∉ H)
    {K₁ : Subgroup G} (hK₁ : K₁ ∈ Ω) (ht : IsUniqueInvolution K₁ t) {d₁ d₂ : G}
    (g₁ : GoodInv H t d₁) (g₂ : GoodInv H t d₂) (g₃ : GoodInv H t (d₁ * d₂))
    (hc : d₁ * d₂ = d₂ * d₁) : False := by
  exact E187C.endgame_four_exact_of
    (fun hK ht hb g₁ g₂ g₃ hc n₁ n₂ => endgame_all hp hΩ.toMod hK ht hb g₁ g₂ g₃ hc n₁ n₂)
    (fun hK ht g₀ g₁ g₂ hc n₀ m₁ => endgame_one hp hq hΩ hbad hK ht g₀ g₁ g₂ hc n₀ m₁)
    (fun hK ht g₁ g₂ g₃ hc m₁ m₂ m₃ => endgame_none hp hq hΩ hbad hK ht g₁ g₂ g₃ hc m₁ m₂ m₃) hbad hK₁ ht g₁ g₂ g₃ hc

end EndFour

end CFSG.ClassicalInvolution.Asc77
