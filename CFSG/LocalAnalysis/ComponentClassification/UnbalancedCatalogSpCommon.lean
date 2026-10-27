module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogEvenCore
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenSymplecticNormalForm

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticFlag SymplecticHigher
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

namespace SpChain

section OddCore

variable {M : Type*} [Group M]

theorem eq_one_of_odd_orderOf {x : M} (hodd : Odd (orderOf x)) {k : ℕ} (hk : x ^ 2 ^ k = 1) :
    x = 1 :=
  orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
    (Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hodd)) dvd_rfl
    (orderOf_dvd_of_pow_eq_one hk))

theorem odd_orderOf_of_mem {X : Subgroup M} (hX : Odd (Nat.card X)) {x : M} (hx : x ∈ X) :
    Odd (orderOf x) :=
  Odd.of_dvd_nat hX (Subgroup.orderOf_dvd_natCard X hx)

theorem eq_bot_of_oddCore_eq_bot {N X : Subgroup M} (hN : CFSG.oddCore N = ⊥) (hXN : X ≤ N)
    (hXn : ∀ n ∈ N, ∀ x ∈ X, n * x * n⁻¹ ∈ X) (hodd : Odd (Nat.card X)) : X = ⊥ := by
  set X' := X.subgroupOf N with hX'
  have hX'n : X'.Normal :=
    ⟨fun x hx n => Subgroup.mem_subgroupOf.mpr (hXn n n.2 x (Subgroup.mem_subgroupOf.mp hx))⟩
  have hcard : Nat.card X' = Nat.card X :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXN).toEquiv
  have hle : X' ≤ CFSG.oddCore N := EvenCatalog.le_oddCore_of_normal hX'n (hcard ▸ hodd)
  rw [hN, le_bot_iff] at hle
  rw [eq_bot_iff]
  intro x hx
  have h1 : (⟨x, hXN hx⟩ : N) ∈ X' := Subgroup.mem_subgroupOf.mpr hx
  rw [hle, Subgroup.mem_bot] at h1
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val h1

theorem eq_bot_of_isPGroup_two {N X : Subgroup M} (hN : IsPGroup 2 N) (hXN : X ≤ N)
    (hodd : Odd (Nat.card X)) : X = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨k, hk⟩ := hN ⟨x, hXN hx⟩
  rw [Subgroup.mem_bot]
  refine eq_one_of_odd_orderOf (odd_orderOf_of_mem hodd hx) (k := k) ?_
  have h1 := congrArg Subtype.val hk
  simpa using h1

theorem oddCore_eq_bot_of_centralizer {C N : Subgroup M} [Finite C] (hNC : N ≤ C)
    (hnorm : ∀ c ∈ C, ∀ n ∈ N, c * n * c⁻¹ ∈ N)
    (hcore : ∀ X : Subgroup M, X ≤ N → (∀ n ∈ N, ∀ x ∈ X, n * x * n⁻¹ ∈ X) →
      Odd (Nat.card X) → X = ⊥)
    (hcent : ∀ c ∈ C, (∀ n ∈ N, c * n = n * c) → ∃ k : ℕ, c ^ 2 ^ k = 1) :
    CFSG.oddCore C = ⊥ := by
  set Q := CFSG.oddCore C with hQ
  have hQodd : Odd (Nat.card Q) := EvenCatalog.odd_card_oddCore
  set Q₁ := Q.map C.subtype with hQ₁
  have hQ₁odd : Odd (Nat.card Q₁) := by
    rw [hQ₁, Subgroup.card_map_of_injective C.subtype_injective]
    exact hQodd
  have hQ₁C : Q₁ ≤ C := Subgroup.map_subtype_le Q
  have hQ₁norm : ∀ c ∈ C, ∀ x ∈ Q₁, c * x * c⁻¹ ∈ Q₁ := by
    rintro c hc _ ⟨q, hq, rfl⟩
    exact ⟨⟨c, hc⟩ * q * ⟨c, hc⟩⁻¹, (inferInstance : Q.Normal).conj_mem q hq _, rfl⟩
  have hX : Q₁ ⊓ N = ⊥ := by
    refine hcore _ inf_le_right (fun n hn x hx => ?_) ?_
    · exact Subgroup.mem_inf.mpr ⟨hQ₁norm n (hNC hn) x (Subgroup.mem_inf.mp hx).1,
        hnorm n (hNC hn) x (Subgroup.mem_inf.mp hx).2⟩
    · exact Odd.of_dvd_nat hQ₁odd (Subgroup.card_dvd_of_le inf_le_left)
  have hcomm : ∀ x ∈ Q₁, ∀ n ∈ N, x * n = n * x := by
    intro x hx n hn
    have h1 : x * n * x⁻¹ * n⁻¹ ∈ Q₁ ⊓ N := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · have h2 := mul_mem hx (hQ₁norm n (hNC hn) x⁻¹ (inv_mem hx))
        rwa [show x * (n * x⁻¹ * n⁻¹) = x * n * x⁻¹ * n⁻¹ by group] at h2
      · exact mul_mem (hnorm x (hQ₁C hx) n hn) (inv_mem hn)
    rw [hX, Subgroup.mem_bot] at h1
    calc x * n = x * n * x⁻¹ * n⁻¹ * (n * x) := by group
      _ = n * x := by rw [h1, one_mul]
  rw [eq_bot_iff]
  intro q hq
  rw [Subgroup.mem_bot]
  have hq₁ : (q : M) ∈ Q₁ := ⟨q, hq, rfl⟩
  obtain ⟨k, hk⟩ := hcent q q.2 (hcomm q hq₁)
  exact Subtype.ext (eq_one_of_odd_orderOf (odd_orderOf_of_mem hQ₁odd hq₁) hk)

theorem oddCore_eq_bot_of_le {A B : Subgroup M} (hAB : A ≤ B) [Finite B]
    (hA : CFSG.oddCore A = ⊥) (hmem : ∀ x ∈ CFSG.oddCore B, (x : M) ∈ A) :
    CFSG.oddCore B = ⊥ := by
  set Q := CFSG.oddCore B with hQ
  set Q₁ := Q.map B.subtype with hQ₁
  have hQ₁A : Q₁ ≤ A := by
    rintro _ ⟨x, hx, rfl⟩
    exact hmem x hx
  have hQ₁bot : Q₁ = ⊥ := by
    refine eq_bot_of_oddCore_eq_bot hA hQ₁A (fun n hn x hx => ?_) ?_
    · obtain ⟨q, hq, rfl⟩ := hx
      exact ⟨⟨n, hAB hn⟩ * q * ⟨n, hAB hn⟩⁻¹, (inferInstance : Q.Normal).conj_mem q hq _, rfl⟩
    · rw [hQ₁, Subgroup.card_map_of_injective B.subtype_injective]
      exact EvenCatalog.odd_card_oddCore
  rw [eq_bot_iff]
  intro x hx
  have h1 : (x : M) ∈ Q₁ := ⟨x, hx, rfl⟩
  rw [hQ₁bot, Subgroup.mem_bot] at h1
  exact Subgroup.mem_bot.mpr (Subtype.ext h1)

theorem mem_of_odd_orderOf_of_index_le_two [Finite M] {E : Subgroup M} [E.Normal]
    (hE : E.index ≤ 2) {x : M} (hx : Odd (orderOf x)) : x ∈ E := by
  have h1 : orderOf (QuotientGroup.mk' E x) ∣ E.index := by
    rw [Subgroup.index_eq_card]
    exact orderOf_dvd_natCard _
  have h2 : orderOf (QuotientGroup.mk' E x) ∣ orderOf x := orderOf_map_dvd _ x
  have hpos : 0 < E.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hle : orderOf (QuotientGroup.mk' E x) ≤ 2 := (Nat.le_of_dvd hpos h1).trans hE
  have hpos' : 0 < orderOf (QuotientGroup.mk' E x) := orderOf_pos _
  obtain ⟨m, hm⟩ := Odd.of_dvd_nat hx h2
  have h3 : orderOf (QuotientGroup.mk' E x) = 1 := by omega
  rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
  exact h3

theorem oddCore_eq_bot_of_index_le_two [Finite M] {E : Subgroup M} [E.Normal]
    (hE : E.index ≤ 2) {H : Subgroup M} {t : M}
    (h₀ : CFSG.oddCore ↥(H ⊓ E ⊓ Subgroup.centralizer {t}) = ⊥) :
    CFSG.oddCore ↥(H ⊓ Subgroup.centralizer {t}) = ⊥ := by
  refine oddCore_eq_bot_of_le (inf_le_inf_right _ inf_le_left) h₀ fun x hx => ?_
  have hodd : Odd (orderOf (x : M)) := by
    rw [Subgroup.orderOf_coe]
    exact Odd.of_dvd_nat EvenCatalog.odd_card_oddCore (Subgroup.orderOf_dvd_natCard _ hx)
  obtain ⟨hxH, hxC⟩ := Subgroup.mem_inf.mp x.2
  exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hxH,
    mem_of_odd_orderOf_of_index_le_two hE hodd⟩, hxC⟩

theorem map_centralizer_of_injective {X : Type*} [Group X] {ρ : X →* M}
    (hρ : Function.Injective ρ) (z : X) :
    (Subgroup.centralizer ({z} : Set X)).map ρ =
      ρ.range ⊓ Subgroup.centralizer ({ρ z} : Set M) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' := Subgroup.mem_centralizer_singleton_iff.mp hx
    refine Subgroup.mem_inf.mpr ⟨⟨x, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    rw [← map_mul, ← map_mul, hx']
  · intro hy
    obtain ⟨⟨x, rfl⟩, hc⟩ := Subgroup.mem_inf.mp hy
    have hc' := Subgroup.mem_centralizer_singleton_iff.mp hc
    refine ⟨x, Subgroup.mem_centralizer_singleton_iff.mpr ?_, rfl⟩
    apply hρ
    rw [map_mul, map_mul, hc']

@[expose] def centralizerEquivOfInjective {X : Type*} [Group X] {ρ : X →* M}
    (hρ : Function.Injective ρ) (z : X) :
    ↥(Subgroup.centralizer ({z} : Set X)) ≃*
      ↥(ρ.range ⊓ Subgroup.centralizer ({ρ z} : Set M)) :=
  ((Subgroup.centralizer ({z} : Set X)).equivMapOfInjective ρ hρ).trans
    (MulEquiv.subgroupCongr (map_centralizer_of_injective hρ z))

theorem oddCore_centralizer_eq_bot_iff {X : Type*} [Group X] {ρ : X →* M}
    (hρ : Function.Injective ρ) (z : X) :
    CFSG.oddCore ↥(Subgroup.centralizer ({z} : Set X)) = ⊥ ↔
      CFSG.oddCore ↥(ρ.range ⊓ Subgroup.centralizer ({ρ z} : Set M)) = ⊥ :=
  ⟨EvenCatalog.oddCore_eq_bot_of_mulEquiv (centralizerEquivOfInjective hρ z),
    EvenCatalog.oddCore_eq_bot_of_mulEquiv (centralizerEquivOfInjective hρ z).symm⟩

end OddCore

section Symplectic

variable {r : ℕ} {K : Type} [Field K]

abbrev spMat (g : StatedSp r K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
  ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)

theorem spMat_mul_mulVec (g h : StatedSp r K) (v : Fin r ⊕ Fin r → K) :
    spMat (g * h) *ᵥ v = spMat g *ᵥ (spMat h *ᵥ v) := by
  rw [mulVec_mulVec]
  rfl

theorem spMat_mulVec_inv_mulVec (g : StatedSp r K) (v : Fin r ⊕ Fin r → K) :
    spMat g *ᵥ (spMat g⁻¹ *ᵥ v) = v := by
  rw [← spMat_mul_mulVec, mul_inv_cancel]
  exact one_mulVec v

theorem spMat_inv_mulVec_mulVec (g : StatedSp r K) (v : Fin r ⊕ Fin r → K) :
    spMat g⁻¹ *ᵥ (spMat g *ᵥ v) = v := by
  rw [← spMat_mul_mulVec, inv_mul_cancel]
  exact one_mulVec v

theorem statedSp_ext {g h : StatedSp r K} (H : ∀ v, spMat g *ᵥ v = spMat h *ᵥ v) : g = h := by
  refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
  have h1 := congrFun (H (Pi.single j 1)) i
  simpa [Matrix.mulVec_single] using h1

variable (r K) in
@[expose] def spInner : StatedSp r K →* MulAut (StatedProj (StatedSp r K)) :=
  (conjAut r K).comp (Subgroup.inclusion statedSp_le_gsp)

theorem spInner_apply (g : StatedSp r K) :
    spInner r K g = conjAut r K ⟨g, statedSp_le_gsp g.2⟩ :=
  rfl

theorem spInner_eq_conj (g : StatedSp r K) : spInner r K g = MulAut.conj (proj r K g) :=
  conjAut_statedSp g

theorem range_spInner : (spInner r K).range = inner (StatedProj (StatedSp r K)) := by
  ext α
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨proj r K g, (spInner_eq_conj g).symm⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨g, rfl⟩ := proj_surjective x
    exact ⟨g, spInner_eq_conj g⟩

theorem spInner_mem_inner (g : StatedSp r K) :
    spInner r K g ∈ inner (StatedProj (StatedSp r K)) :=
  ⟨proj r K g, (spInner_eq_conj g).symm⟩

theorem spInner_mem_spSemilinearAutGroup (g : StatedSp r K) :
    spInner r K g ∈ spSemilinearAutGroup r K :=
  spLinearAutGroup_le_spSemilinearAutGroup (conjAut_mem_spLinearAutGroup _)

theorem inner_le_spSemilinearAutGroup :
    inner (StatedProj (StatedSp r K)) ≤ spSemilinearAutGroup r K := by
  rw [← range_spInner]
  rintro _ ⟨g, rfl⟩
  exact spInner_mem_spSemilinearAutGroup g

theorem spInner_mul_fieldAut_inj [NeZero r] [CharP K 2] {g h : StatedSp r K} {φ ψ : K ≃+* K}
    (H : spInner r K g * fieldAut r K φ = spInner r K h * fieldAut r K ψ) : g = h ∧ φ = ψ := by
  have h1 := UnitaryHigher.spNormalFormHom_injective (r := r) (K := K)
    (show UnitaryHigher.spNormalFormHom r K ⟨g, φ⟩ = UnitaryHigher.spNormalFormHom r K ⟨h, ψ⟩
      from H)
  exact ⟨congrArg SemidirectProduct.left h1, congrArg SemidirectProduct.right h1⟩

theorem spInner_injective [NeZero r] [CharP K 2] : Function.Injective (spInner r K) := by
  intro g h hgh
  refine (spInner_mul_fieldAut_inj (φ := 1) (ψ := 1) ?_).1
  rw [hgh]

theorem fieldAut_mul_spInner_mul_inv (φ : K ≃+* K) (g : StatedSp r K) :
    fieldAut r K φ * spInner r K g * (fieldAut r K φ)⁻¹ = spInner r K (fieldSp r K φ g) := by
  rw [spInner_apply, fieldAut_mul_conjAut_mul_inv, spInner_apply]
  rfl

theorem spInner_mul_fieldAut_mul (g h : StatedSp r K) (φ ψ : K ≃+* K) :
    spInner r K g * fieldAut r K φ * (spInner r K h * fieldAut r K ψ) =
      spInner r K (g * fieldSp r K φ h) * fieldAut r K (φ * ψ) := by
  calc spInner r K g * fieldAut r K φ * (spInner r K h * fieldAut r K ψ)
      _ = spInner r K g * (fieldAut r K φ * spInner r K h * (fieldAut r K φ)⁻¹) *
          (fieldAut r K φ * fieldAut r K ψ) := by group
      _ = _ := by rw [fieldAut_mul_spInner_mul_inv, ← map_mul, ← map_mul]

theorem exists_eq_spInner_mul_fieldAut [Finite K] [CharP K 2]
    {α : MulAut (StatedProj (StatedSp r K))} (hα : α ∈ spSemilinearAutGroup r K) :
    ∃ (g : StatedSp r K) (φ : K ≃+* K), α = spInner r K g * fieldAut r K φ := by
  obtain ⟨A, φ, rfl⟩ := mem_spSemilinearAutGroup_iff.mp hα
  obtain ⟨s, hs⟩ := UnitaryHigher.exists_conjAut_eq_statedSp A
  exact ⟨s, φ, by rw [hs, spInner_apply]⟩

theorem conj_spInner (g s : StatedSp r K) (φ : K ≃+* K) :
    spInner r K g * fieldAut r K φ * spInner r K s * (spInner r K g * fieldAut r K φ)⁻¹ =
      spInner r K (g * fieldSp r K φ s * g⁻¹) := by
  calc spInner r K g * fieldAut r K φ * spInner r K s * (spInner r K g * fieldAut r K φ)⁻¹
      _ = spInner r K g * (fieldAut r K φ * spInner r K s * (fieldAut r K φ)⁻¹) *
          (spInner r K g)⁻¹ := by group
      _ = _ := by rw [fieldAut_mul_spInner_mul_inv, ← map_inv, ← map_mul, ← map_mul]

end Symplectic

end SpChain

end CFSG.ComponentClassification.UnbalancedCatalog
