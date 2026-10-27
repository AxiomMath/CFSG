module

public import CFSG.ClassicalInvolution.Generic.Frame
public import CFSG.LieType.Universal.Spin.Twisted.Graded
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ClassicalInvolution.RouteD.Exotic

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open scoped commutatorElement

section Layer

variable {K : Type*} [Group K]

@[expose] def LayerAt (Fund : Set (Subgroup K)) (R₀ : Subgroup K) : Prop :=
  ∃ L : Subgroup K, CFSG.Open.IsQuasisimple ↥L ∧ L ≤ Subgroup.centralizer (R₀ : Set K) ∧
    (∀ P : Subgroup K, P ≤ Subgroup.centralizer (R₀ : Set K) → P ≤ ⁅P, P⁆ → P ≤ L) ∧
    L ∉ Fund

theorem open_isQuasisimple_congr {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    CFSG.Open.IsQuasisimple G ↔ CFSG.Open.IsQuasisimple H :=
  ⟨fun h => CFSG.ComponentClassification.Components.quasisimple_of_equiv e.symm h,
    fun h => CFSG.ComponentClassification.Components.quasisimple_of_equiv e h⟩

theorem open_isQuasisimple_conjSub (g : K) {L : Subgroup K} :
    CFSG.Open.IsQuasisimple ↥(conjSub g L) ↔ CFSG.Open.IsQuasisimple ↥L :=
  (open_isQuasisimple_congr
    (Subgroup.equivMapOfInjective L (MulAut.conj g).toMonoidHom (MulAut.conj g).injective)).symm

theorem conjSub_le_centralizer_iff (g : K) {P R : Subgroup K} :
    conjSub g P ≤ Subgroup.centralizer (conjSub g R : Set K) ↔
      P ≤ Subgroup.centralizer (R : Set K) := by
  constructor
  · intro h x hx
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have h1 := Subgroup.mem_centralizer_iff.mp (h (conj_mem_conjSub hx)) _ (conj_mem_conjSub hr)
    have h2 : g * (r * x) * g⁻¹ = g * (x * r) * g⁻¹ := by
      calc g * (r * x) * g⁻¹ = (g * r * g⁻¹) * (g * x * g⁻¹) := by group
        _ = (g * x * g⁻¹) * (g * r * g⁻¹) := h1
        _ = g * (x * r) * g⁻¹ := by group
    simpa using h2
  · intro h _ hx
    obtain ⟨x, hx, rfl⟩ := hx
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨r, hr, rfl⟩
    have h1 := Subgroup.mem_centralizer_iff.mp (h hx) r hr
    change g * r * g⁻¹ * (g * x * g⁻¹) = g * x * g⁻¹ * (g * r * g⁻¹)
    calc g * r * g⁻¹ * (g * x * g⁻¹) = g * (r * x) * g⁻¹ := by group
      _ = g * (x * r) * g⁻¹ := by rw [h1]
      _ = g * x * g⁻¹ * (g * r * g⁻¹) := by group

theorem LayerAt.conj {Fund : Set (Subgroup K)} (hFund : ∀ S ∈ Fund, ∀ g : K, conjSub g S ∈ Fund)
    {R : Subgroup K} (h : LayerAt Fund R) (g : K) : LayerAt Fund (conjSub g R) := by
  obtain ⟨L, hLq, hLC, hLP, hLF⟩ := h
  refine ⟨conjSub g L, (open_isQuasisimple_conjSub g).2 hLq, ?_, ?_, ?_⟩
  · exact (conjSub_le_centralizer_iff g).2 hLC
  · intro P hPC hPperf
    have h1 : conjSub g⁻¹ P ≤ Subgroup.centralizer (R : Set K) := by
      have := (conjSub_le_centralizer_iff g⁻¹ (P := P) (R := conjSub g R)).2 hPC
      rwa [conjSub_inv_conjSub] at this
    have h2 : conjSub g⁻¹ P ≤ ⁅conjSub g⁻¹ P, conjSub g⁻¹ P⁆ := by
      unfold conjSub
      rw [← Subgroup.map_commutator]
      exact Subgroup.map_mono hPperf
    calc P = conjSub g (conjSub g⁻¹ P) := (conjSub_conjSub_inv g P).symm
      _ ≤ conjSub g L := conjSub_mono (hLP _ h1 h2)
  · intro hmem
    apply hLF
    have := hFund _ hmem g⁻¹
    rwa [conjSub_inv_conjSub] at this

end Layer

section Commuting

variable {K : Type*} [Group K]

theorem mem_sup_iff_of_le_centralizer {A B : Subgroup K}
    (h : A ≤ Subgroup.centralizer (B : Set K)) {x : K} :
    x ∈ A ⊔ B ↔ ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  constructor
  · intro hx
    let T : Subgroup K :=
      { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, x = a * b}
        mul_mem' := by
          rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
          have hc : b * a' = a' * b := Subgroup.mem_centralizer_iff.mp (h ha') b hb
          refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
          calc a * b * (a' * b') = a * (b * a') * b' := by group
            _ = a * (a' * b) * b' := by rw [hc]
            _ = a * a' * (b * b') := by group
        one_mem' := ⟨1, A.one_mem, 1, B.one_mem, (mul_one 1).symm⟩
        inv_mem' := by
          rintro _ ⟨a, ha, b, hb, rfl⟩
          have hc : b * a = a * b := Subgroup.mem_centralizer_iff.mp (h ha) b hb
          refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
          calc (a * b)⁻¹ = b⁻¹ * a⁻¹ := mul_inv_rev a b
            _ = a⁻¹ * b⁻¹ := (Commute.inv_inv hc.symm).eq.symm }
    have hle : A ⊔ B ≤ T := sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, (mul_one a).symm⟩)
      (fun b hb => ⟨1, A.one_mem, b, hb, (one_mul b).symm⟩)
    exact hle hx
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact Subgroup.mul_mem_sup ha hb

theorem commutator_mul_mul_eq_of_commute {a₁ a₂ b₁ b₂ : K} (h1 : Commute a₁ b₁)
    (h2 : Commute a₁ b₂) (h3 : Commute a₁ a₂) (h4 : Commute a₂ b₁) (h5 : Commute a₂ b₂) :
    ⁅a₁ * b₁, a₂ * b₂⁆ = ⁅b₁, b₂⁆ := by
  have e1 : a₁ * b₁ = b₁ * a₁ := h1.eq
  have e2 : a₂ * b₂ = b₂ * a₂ := h5.eq
  have c1 : ⁅a₁, b₂ * a₂⁆ = 1 := (h2.mul_right h3).commutator_eq
  have c2 : ⁅b₁, a₂⁆ = 1 := h4.symm.commutator_eq
  rw [e1, e2, commutatorElement_mul_left_eq_conj_mul, c1, commutatorElement_mul_right_eq_mul_conj,
    c2]
  simp

theorem le_of_perfect_of_le_sup_of_commutes {A B P : Subgroup K}
    (h : A ≤ Subgroup.centralizer (B : Set K)) (hP : P ≤ A ⊔ B) (hperf : P ≤ ⁅P, P⁆)
    (hPA : P ≤ Subgroup.centralizer (A : Set K)) : P ≤ B := by
  refine hperf.trans (Subgroup.commutator_le.mpr fun x hx y hy => ?_)
  obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := (mem_sup_iff_of_le_centralizer h).mp (hP hx)
  obtain ⟨a₂, ha₂, b₂, hb₂, rfl⟩ := (mem_sup_iff_of_le_centralizer h).mp (hP hy)
  have hAB : ∀ {a b : K}, a ∈ A → b ∈ B → Commute a b := fun {a b} ha hb =>
    (Subgroup.mem_centralizer_iff.mp (h ha) b hb).symm
  have hcen : ∀ {a b : K}, a ∈ A → b ∈ B → a * b ∈ P → ∀ {a' : K}, a' ∈ A → Commute a a' := by
    intro a b ha hb hab a' ha'
    have h1 := Subgroup.mem_centralizer_iff.mp (hPA hab) a' ha'
    have h2 : a' * a * b = a * a' * b := by
      calc a' * a * b = a' * (a * b) := by group
        _ = a * b * a' := h1
        _ = a * (b * a') := by group
        _ = a * (a' * b) := by rw [(hAB ha' hb).eq.symm]
        _ = a * a' * b := by group
    exact (mul_right_cancel h2).symm
  have hc12 : Commute a₁ a₂ := hcen ha₁ hb₁ hx ha₂
  rw [commutator_mul_mul_eq_of_commute (hAB ha₁ hb₁) (hAB ha₁ hb₂) hc12 (hAB ha₂ hb₁)
    (hAB ha₂ hb₂), commutatorElement_def]
  exact B.mul_mem (B.mul_mem (B.mul_mem hb₁ hb₂) (B.inv_mem hb₁)) (B.inv_mem hb₂)

end Commuting

section Solvable

variable {X : Type*} [Group X]

theorem le_of_perfect_of_derivedSeries_two (N : Subgroup X) [N.Normal]
    (hN : derivedSeries (X ⧸ N) 2 = ⊥) {P : Subgroup X} (hP : P ≤ ⁅P, P⁆) : P ≤ N := by
  have key : ∀ n : ℕ, P.map (QuotientGroup.mk' N) ≤ derivedSeries (X ⧸ N) n := by
    intro n
    induction n with
    | zero => exact le_top
    | succ n ih =>
      rw [derivedSeries_succ]
      calc P.map (QuotientGroup.mk' N) ≤ ⁅P.map (QuotientGroup.mk' N),
            P.map (QuotientGroup.mk' N)⁆ := by
            rw [← Subgroup.map_commutator]
            exact Subgroup.map_mono hP
        _ ≤ _ := Subgroup.commutator_mono ih ih
  intro x hx
  have h1 := key 2 ⟨x, hx, rfl⟩
  rw [hN] at h1
  exact (QuotientGroup.eq_one_iff x).mp (Subgroup.mem_bot.mp h1)

theorem le_of_perfect_of_derivedSeries_two' {M : Type*} [Group M] {X S P : Subgroup M}
    [(S.subgroupOf X).Normal] (hN : derivedSeries (↥X ⧸ S.subgroupOf X) 2 = ⊥) (hPX : P ≤ X)
    (hP : P ≤ ⁅P, P⁆) : P ≤ S := by
  have h1 : P.subgroupOf X ≤ ⁅P.subgroupOf X, P.subgroupOf X⁆ := by
    intro x hx
    have h2 : (⁅P.subgroupOf X, P.subgroupOf X⁆).map X.subtype = ⁅P, P⁆ := by
      rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPX]
    have h3 : (x : M) ∈ (⁅P.subgroupOf X, P.subgroupOf X⁆).map X.subtype := by
      rw [h2]
      exact hP hx
    obtain ⟨y, hy, hyx⟩ := h3
    exact (Subtype.ext hyx : y = x) ▸ hy
  have h2 := le_of_perfect_of_derivedSeries_two (S.subgroupOf X) hN h1
  intro x hx
  exact h2 (show (⟨x, hPX hx⟩ : ↥X) ∈ P.subgroupOf X from hx)

end Solvable

section CentralKernel

variable {K : Type*} [Group K]

theorem commutes_of_commutator_mem_center {R : Subgroup K} (hR : R ≤ ⁅R, R⁆) {x : K}
    (hx : ∀ r ∈ R, ⁅x, r⁆ ∈ Subgroup.center K) : ∀ r ∈ R, x * r = r * x := by
  have conjEq : ∀ r ∈ R, x * r * x⁻¹ = r * ⁅x, r⁆ := fun r hr => by
    rw [Subgroup.mem_center_iff.mp (hx r hr) r, commutatorElement_def]
    group
  have hle : R ≤ R ⊓ Subgroup.centralizer ({x} : Set K) := by
    refine hR.trans (Subgroup.commutator_le.mpr fun r₁ hr₁ r₂ hr₂ =>
      ⟨?_, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩)
    · rw [commutatorElement_def]
      exact R.mul_mem (R.mul_mem (R.mul_mem hr₁ hr₂) (R.inv_mem hr₁)) (R.inv_mem hr₂)
    · symm
      calc x * ⁅r₁, r₂⁆ = (x * ⁅r₁, r₂⁆ * x⁻¹) * x := by group
        _ = ⁅x * r₁ * x⁻¹, x * r₂ * x⁻¹⁆ * x := by rw [conjugate_commutatorElement]
        _ = ⁅r₁ * ⁅x, r₁⁆, r₂ * ⁅x, r₂⁆⁆ * x := by rw [conjEq r₁ hr₁, conjEq r₂ hr₂]
        _ = ⁅r₁, r₂⁆ * x := by
          rw [CFSG.ComponentClassification.CentralExtensions.commutator_mul_center_left _ _ _
              (hx r₁ hr₁),
            CFSG.ComponentClassification.CentralExtensions.commutator_mul_center_right _ _ _
              (hx r₂ hr₂)]
  intro r hr
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hr).2).symm

end CentralKernel

section Derived

variable {K C : Type*} [Group K] [Group C]

theorem map_commutator_comap_eq (θ : K →* C) (hθ : Function.Surjective θ) {L : Subgroup C}
    (hL : ⁅L, L⁆ = L) : (⁅L.comap θ, L.comap θ⁆).map θ = L := by
  rw [Subgroup.map_commutator, Subgroup.map_comap_eq_self_of_surjective hθ, hL]

theorem commutator_comap_perfect (θ : K →* C) (hθ : Function.Surjective θ)
    (hker : θ.ker ≤ Subgroup.center K) {L : Subgroup C} (hL : ⁅L, L⁆ = L) :
    ⁅⁅L.comap θ, L.comap θ⁆, ⁅L.comap θ, L.comap θ⁆⁆ = ⁅L.comap θ, L.comap θ⁆ := by
  set M := L.comap θ with hM
  set N := ⁅M, M⁆ with hN
  have hmapN : N.map θ = L := map_commutator_comap_eq θ hθ hL
  have hMN : M ≤ N ⊔ θ.ker := by
    intro m hm
    have h1 : θ m ∈ N.map θ := by rw [hmapN]; exact hm
    obtain ⟨n, hn, hnm⟩ := h1
    have : n⁻¹ * m ∈ θ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hnm, inv_mul_cancel]
    have hm' : m = n * (n⁻¹ * m) := by group
    rw [hm']
    exact Subgroup.mul_mem_sup hn this
  refine le_antisymm (Subgroup.commutator_le_self N) ?_
  calc N = ⁅M, M⁆ := rfl
    _ ≤ ⁅N ⊔ θ.ker, N ⊔ θ.ker⁆ := Subgroup.commutator_mono hMN hMN
    _ = ⁅N, N⁆ := CFSG.ComponentClassification.CentralExtensions.commutator_sup_central N θ.ker hker

theorem isQuasisimple_commutator_comap (θ : K →* C) (hθ : Function.Surjective θ)
    (hker : θ.ker ≤ Subgroup.center K) {L : Subgroup C} (hL : CFSG.Open.IsQuasisimple ↥L) :
    CFSG.Open.IsQuasisimple ↥⁅L.comap θ, L.comap θ⁆ := by
  have hLperf : ⁅L, L⁆ = L := by
    have : Group.IsPerfect ↥L := ⟨hL.1⟩
    exact Subgroup.isPerfect_iff.mp this
  set M := L.comap θ with hM
  set N := ⁅M, M⁆ with hN
  have hmapN : N.map θ = L := map_commutator_comap_eq θ hθ hLperf
  have hNM : N ≤ M := Subgroup.commutator_le_of_le le_rfl le_rfl
  have hNperf : Group.IsPerfect ↥N :=
    Subgroup.isPerfect_iff.mpr (commutator_comap_perfect θ hθ hker hLperf)
  let π : ↥N →* ↥L := (θ.comp N.subtype).codRestrict L (fun x => hNM x.2)
  have hπsurj : Function.Surjective π := by
    intro y
    have h1 : (y : C) ∈ N.map θ := by rw [hmapN]; exact y.2
    obtain ⟨n, hn, hny⟩ := h1
    exact ⟨⟨n, hn⟩, Subtype.ext hny⟩
  have hπker : π.ker ≤ Subgroup.center ↥N := by
    intro x hx
    have h1 : θ (x : K) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    have h2 : (x : K) ∈ Subgroup.center K := hker (MonoidHom.mem_ker.mpr h1)
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.mp h2 y)
  exact CFSG.ComponentClassification.CentralExtensions.quasisimple_of_surjective hL π hπsurj hπker

end Derived

section Family

variable {K : Type*} [Group K]

theorem not_mem_of_le_of_ne [Finite K] {Fund : Set (Subgroup K)}
    (hsingle : ∀ R ∈ Fund, ∀ R' ∈ Fund, ∃ g : K, R' = conjSub g R)
    {R L : Subgroup K} (hR : R ∈ Fund) (hRL : R ≤ L) (hne : R ≠ L) : L ∉ Fund := by
  intro hL
  obtain ⟨g, hg⟩ := hsingle R hR L hL
  apply hne
  refine Subgroup.eq_of_le_of_card_ge hRL ?_
  rw [hg]
  exact (Nat.card_congr (Subgroup.equivMapOfInjective R (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).toEquiv).symm.le

end Family

section Std

variable {G : Type*} [Group G]

@[expose] def StdLayer (R₀ R₂ : Subgroup G) : Prop :=
  ∃ L : Subgroup G, CFSG.Open.IsQuasisimple ↥L ∧ L ≤ Subgroup.centralizer (R₀ : Set G) ∧
    (∀ P : Subgroup G, P ≤ Subgroup.centralizer (R₀ : Set G) → P ≤ ⁅P, P⁆ → P ≤ L) ∧
    R₂ ≤ L ∧ R₂ ≠ L

theorem layerAt_of_stdLayer [Finite G] {Fund : Set (Subgroup G)}
    (hsingle : ∀ R ∈ Fund, ∀ R' ∈ Fund, ∃ g : G, R' = conjSub g R) {R₀ R₂ : Subgroup G}
    (hR₂ : R₂ ∈ Fund) (h : StdLayer R₀ R₂) : LayerAt Fund R₀ := by
  obtain ⟨L, hLq, hLC, hLP, hR₂L, hne⟩ := h
  exact ⟨L, hLq, hLC, hLP, not_mem_of_le_of_ne hsingle hR₂ hR₂L hne⟩

variable {C : Type*} [Group C]

theorem StdLayer.of_central_cover (θ : G →* C) (hθ : Function.Surjective θ)
    (hker : θ.ker ≤ Subgroup.center G) {R₀ R₂ : Subgroup G} (hR₀ : R₀ ≤ ⁅R₀, R₀⁆)
    (hR₂ : R₂ ≤ ⁅R₂, R₂⁆) {R₀' R₂' : Subgroup C} (h₀ : R₀.map θ = R₀') (h₂ : R₂.map θ = R₂')
    (h : StdLayer R₀' R₂') : StdLayer R₀ R₂ := by
  obtain ⟨L, hLq, hLC, hLP, hR₂L, hne⟩ := h
  have hLperf : ⁅L, L⁆ = L := by
    have : Group.IsPerfect ↥L := ⟨hLq.1⟩
    exact Subgroup.isPerfect_iff.mp this
  set M := L.comap θ with hM
  set N := ⁅M, M⁆ with hN
  have hmapN : N.map θ = L := map_commutator_comap_eq θ hθ hLperf
  have hNM : N ≤ M := Subgroup.commutator_le_of_le le_rfl le_rfl
  have hMC : M ≤ Subgroup.centralizer (R₀ : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hcomm : ∀ r ∈ R₀, ⁅x, r⁆ ∈ Subgroup.center G := by
      intro r hr
      apply hker
      rw [MonoidHom.mem_ker, map_commutatorElement]
      have h1 : θ r ∈ R₀' := h₀ ▸ Subgroup.mem_map_of_mem θ hr
      have h2 := Subgroup.mem_centralizer_iff.mp (hLC hx) (θ r) h1
      rw [commutatorElement_def]
      calc θ x * θ r * (θ x)⁻¹ * (θ r)⁻¹ = (θ r * θ x) * (θ x)⁻¹ * (θ r)⁻¹ := by rw [h2]
        _ = 1 := by group
    exact (commutes_of_commutator_mem_center hR₀ hcomm r hr).symm
  refine ⟨N, isQuasisimple_commutator_comap θ hθ hker hLq, hNM.trans hMC, ?_, ?_, ?_⟩
  · intro P hPC hPperf
    have h1 : P.map θ ≤ Subgroup.centralizer (R₀' : Set C) := by
      rintro _ ⟨x, hx, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ hr
      rw [← h₀] at hr
      obtain ⟨r, hr, rfl⟩ := hr
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp (hPC hx) r hr]
    have h2 : P.map θ ≤ ⁅P.map θ, P.map θ⁆ := by
      rw [← Subgroup.map_commutator]
      exact Subgroup.map_mono hPperf
    have h3 : P ≤ M := fun x hx => hLP _ h1 h2 (Subgroup.mem_map_of_mem θ hx)
    exact hPperf.trans (Subgroup.commutator_mono h3 h3)
  · have h3 : R₂ ≤ M := fun x hx => hR₂L (h₂ ▸ Subgroup.mem_map_of_mem θ hx)
    exact hR₂.trans (Subgroup.commutator_mono h3 h3)
  · intro heq
    apply hne
    rw [← h₂, heq, hmapN]

end Std

end CFSG.ClassicalInvolution.RouteD.Exotic
