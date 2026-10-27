module

public import CFSG.CGT.PushingUpLit.CGT6.SixTwoBasic
public import CFSG.CGT.PushingUpLit.ThreeFromEightOneCore
public import CFSG.CGT.PushingUpLit.BHS6.Subnormal
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.ThreeSubgroups

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open CFSG.CGT.PushingUpLit.SixThree
open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

theorem exists_pow_mem_sup {Y D : Subgroup G} (hD : IsPGroup 2 D)
    (hDY : D ≤ Subgroup.normalizer (Y : Set G)) {k : G} (hk : k ∈ Y ⊔ D) :
    ∃ n : ℕ, k ^ 2 ^ n ∈ Y := by
  have hmem : k ∈ (Y : Set G) * (D : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left Y D hDY]
    exact hk
  obtain ⟨y, hy, d, hd, rfl⟩ := hmem
  exact SubTwo.exists_pow_mem_of_decomp (B := Y ⊔ D) (sup_le Subgroup.le_normalizer hDY) hD
    (fun b hb => by
      have hb' : b ∈ (Y : Set G) * (D : Set G) := by
        rw [← Subgroup.coe_mul_of_right_le_normalizer_left Y D hDY]
        exact hb
      obtain ⟨y', hy', d', hd', rfl⟩ := hb'
      exact ⟨y', hy', d', hd', Subgroup.mem_sup_right hd', rfl⟩) (y * d) hk

theorem le_of_noTwoQuotient {Y' Y D : Subgroup G} (hNo : SubTwo.NoTwoQuotient Y')
    (hD : IsPGroup 2 D) (hDY : D ≤ Subgroup.normalizer (Y : Set G)) (h : Y' ≤ Y ⊔ D) :
    Y' ≤ Y := by
  have hY'N : Y' ≤ Subgroup.normalizer (Y : Set G) :=
    h.trans (sup_le Subgroup.le_normalizer hDY)
  have key : Y' ⊓ Y = Y' := by
    refine hNo (Y' ⊓ Y) inf_le_left ?_ ?_
    · exact le_trans (le_inf Subgroup.le_normalizer hY'N)
        Subgroup.inf_normalizer_le_normalizer_inf
    · intro y hy
      obtain ⟨n, hn⟩ := exists_pow_mem_sup hD hDY (h hy)
      exact ⟨n, Subgroup.mem_inf.mpr ⟨Y'.pow_mem hy _, hn⟩⟩
  intro x hx
  have : x ∈ Y' ⊓ Y := by rw [key]; exact hx
  exact this.2

theorem noTwoQuotient_map {Y : Subgroup G} (e : G ≃* G) (hY : SubTwo.NoTwoQuotient Y) :
    SubTwo.NoTwoQuotient (Y.map e.toMonoidHom) := by
  intro N hNY hnorm hpow
  set N0 : Subgroup G := N.comap e.toMonoidHom with hN0
  have hN0Y : N0 ≤ Y := fun z hz => by
    have : e z ∈ Y.map e.toMonoidHom := hNY hz
    rw [Subgroup.mem_map_equiv] at this
    simpa using this
  have hnorm0 : Y ≤ Subgroup.normalizer (N0 : Set G) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro n
    have hy' : e y ∈ Subgroup.normalizer (N : Set G) := hnorm (Subgroup.mem_map_of_mem _ hy)
    have := Subgroup.mem_normalizer_iff.mp hy' (e n)
    simpa [hN0, Subgroup.mem_comap] using this
  have hpow0 : ∀ y ∈ Y, ∃ k : ℕ, y ^ 2 ^ k ∈ N0 := by
    intro y hy
    obtain ⟨k, hk⟩ := hpow (e y) (Subgroup.mem_map_of_mem _ hy)
    exact ⟨k, by simpa [hN0, Subgroup.mem_comap, map_pow] using hk⟩
  have h0 : N0 = Y := hY N0 hN0Y hnorm0 hpow0
  have : N = N0.map e.toMonoidHom := (Subgroup.map_comap_eq_self_of_surjective e.surjective N).symm
  rw [this, h0]

theorem mem_normalizer_of_conj_le_sup [Finite G] {Y D : Subgroup G}
    (hNo : SubTwo.NoTwoQuotient Y) (hD : IsPGroup 2 D)
    (hDY : D ≤ Subgroup.normalizer (Y : Set G)) {a : G} (ha : ∀ y ∈ Y, a * y * a⁻¹ ∈ Y ⊔ D) :
    a ∈ Subgroup.normalizer (Y : Set G) := by
  have hNo' := noTwoQuotient_map (MulAut.conj a) hNo
  have hle : Y.map (MulAut.conj a).toMonoidHom ≤ Y := by
    refine le_of_noTwoQuotient hNo' hD hDY ?_
    rintro _ ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply] using ha y hy
  have hmap : Y.map (MulAut.conj a).toMonoidHom = Y := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj a).injective]
  refine Subgroup.mem_normalizer_iff.mpr fun y => ⟨fun hy => ?_, fun hy => ?_⟩
  · have := hle (Subgroup.mem_map_of_mem _ hy)
    simpa [MulAut.conj_apply] using this
  · have hy' : a * y * a⁻¹ ∈ Y.map (MulAut.conj a).toMonoidHom := by rw [hmap]; exact hy
    obtain ⟨z, hz, hzy⟩ := hy'
    have h2 : a * z * a⁻¹ = a * y * a⁻¹ := by simpa [MulAut.conj_apply] using hzy
    have hzy' : z = y := mul_left_cancel (mul_right_cancel h2)
    rw [← hzy']
    exact hz

theorem isSubnormal_subgroupOf_of_isSubnormal {X : Subgroup G} (hX : X.IsSubnormal)
    (H : Subgroup G) : (X.subgroupOf H).IsSubnormal :=
  CFSG.GroupTheory.isSubnormal_subgroupOf_of_le le_top
    (BHS6.isSubnormal_subgroupOf_of_open (BHS6.open_isSubnormal_top_of_isSubnormal hX))

structure PerfCtx (V Y X : Subgroup G) [Finite G] : Prop where
  hYX : Y ≤ X
  hXs : X.IsSubnormal
  hNoY : SubTwo.NoTwoQuotient Y
  hNoX : SubTwo.NoTwoQuotient X
  hperf : ⁅X, X⁆ = X
  hCX : Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (X : Set G)
  hN0 : IsPGroup 2 ↥(X ⊓ Subgroup.centralizer (V : Set G))
  hOX : ⁅oTwoIn X, X⁆ ≤ Subgroup.centralizer (V : Set G)
  hCY : Subgroup.centralizer (V : Set G) ≤ centralizerModCore Y

namespace PerfCtx

variable [Finite G] {V Y X : Subgroup G}

theorem centralizer_le_normalizer (h : PerfCtx V Y X) :
    Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (Y : Set G) :=
  fun _ hg => (h.hCY hg).1

theorem inf_le_oTwoIn [V.Normal] (h : PerfCtx V Y X) :
    X ⊓ Subgroup.centralizer (V : Set G) ≤ oTwoIn X := by
  refine le_oTwoIn_of_isPGroup inf_le_left h.hN0 ?_
  refine le_trans (le_inf Subgroup.le_normalizer ?_) Subgroup.inf_normalizer_le_normalizer_inf
  rw [Subgroup.normalizer_eq_top (Subgroup.centralizer (V : Set G))]
  exact le_top

theorem oTwoIn_le_pCore (h : PerfCtx V Y X) : oTwoIn X ≤ pCore 2 G :=
  ThreeFromEight.oTwoIn_le_pCore_of_isSubnormal h.hXs

theorem pCore_le_normalizer (h : PerfCtx V Y X) : pCore 2 G ≤ Subgroup.normalizer (X : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQn : (pCore 2 G).Normal := pCore_normal
  refine SubTwo.le_normalizer_of_isSubnormal_sup h.hNoX pCore_isPGroup ?_
    (isSubnormal_subgroupOf_of_isSubnormal h.hXs (X ⊔ pCore 2 G))
  rw [Subgroup.normalizer_eq_top (pCore 2 G)]
  exact le_top

theorem commutator_pCore_le_oTwoIn (h : PerfCtx V Y X) : ⁅pCore 2 G, X⁆ ≤ oTwoIn X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQn : (pCore 2 G).Normal := pCore_normal
  refine commutator_le_oTwoIn_of_normalizes pCore_isPGroup (pCore_le_normalizer h) ?_
  rw [Subgroup.normalizer_eq_top (pCore 2 G)]
  exact le_top

theorem commutator_centralizerModCore_le [V.Normal] (h : PerfCtx V Y X) :
    ⁅centralizerModCore X, X⁆ ≤ Subgroup.centralizer (V : Set G) := by
  set A₁ : Subgroup G := centralizerModCore X with hA₁
  have h1 : ⁅A₁, X⁆ ≤ oTwoIn X :=
    Subgroup.commutator_le.mpr fun g hg x hx => hg.2 x hx
  have h2 : ⁅⁅A₁, X⁆, X⁆ ≤ Subgroup.centralizer (V : Set G) :=
    (Subgroup.commutator_mono h1 le_rfl).trans h.hOX
  have h3 : ⁅⁅X, A₁⁆, X⁆ ≤ Subgroup.centralizer (V : Set G) := by
    rw [Subgroup.commutator_comm X A₁]
    exact h2
  have h4 : ⁅⁅X, X⁆, A₁⁆ ≤ Subgroup.centralizer (V : Set G) :=
    CFSG.SignalizerFunctorTheorem.McBride.three_subgroups_lemma_normal h3 h2
  rw [h.hperf, Subgroup.commutator_comm] at h4
  exact h4

theorem mem_normalizer_of_commutator_mem [V.Normal] (h : PerfCtx V Y X) {a : G}
    (haX : a ∈ Subgroup.normalizer (X : Set G))
    (hc : ∀ x ∈ X, ⁅a, x⁆ ∈ Subgroup.centralizer (V : Set G)) :
    a ∈ Subgroup.normalizer (Y : Set G) := by
  refine mem_normalizer_of_conj_le_sup (D := X ⊓ Subgroup.centralizer (V : Set G)) h.hNoY
    (h.hN0) (fun g hg => h.centralizer_le_normalizer hg.2) fun y hy => ?_
  have hyX : y ∈ X := h.hYX hy
  have hcomm : ⁅a, y⁆ ∈ X ⊓ Subgroup.centralizer (V : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨?_, hc y hyX⟩
    have : a * y * a⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp haX y).mp hyX
    rw [commutatorElement_def]
    exact X.mul_mem this (X.inv_mem hyX)
  have e : a * y * a⁻¹ = ⁅a, y⁆ * y := by
    simp [commutatorElement_def]
  rw [e]
  exact (Y ⊔ X ⊓ Subgroup.centralizer (V : Set G)).mul_mem
    (Subgroup.mem_sup_right hcomm) (Subgroup.mem_sup_left hy)

theorem pCore_le_normalizer_Y [V.Normal] (h : PerfCtx V Y X) :
    pCore 2 G ≤ Subgroup.normalizer (Y : Set G) := by
  intro a ha
  refine mem_normalizer_of_commutator_mem h (pCore_le_normalizer h ha) fun x hx => ?_
  have h1 : ⁅pCore 2 G, X⁆ ≤ Subgroup.centralizer (V : Set G) := by
    have hQ : ⁅⁅X, pCore 2 G⁆, X⁆ ≤ Subgroup.centralizer (V : Set G) := by
      rw [Subgroup.commutator_comm X (pCore 2 G)]
      exact (Subgroup.commutator_mono (commutator_pCore_le_oTwoIn h) le_rfl).trans h.hOX
    have hQ' : ⁅⁅pCore 2 G, X⁆, X⁆ ≤ Subgroup.centralizer (V : Set G) :=
      (Subgroup.commutator_mono (commutator_pCore_le_oTwoIn h) le_rfl).trans h.hOX
    have h4 : ⁅⁅X, X⁆, pCore 2 G⁆ ≤ Subgroup.centralizer (V : Set G) :=
      CFSG.SignalizerFunctorTheorem.McBride.three_subgroups_lemma_normal hQ hQ'
    rw [h.hperf, Subgroup.commutator_comm] at h4
    exact h4
  exact h1 (Subgroup.commutator_mem_commutator ha hx)

theorem pCore_le_centralizerModCore [V.Normal] (h : PerfCtx V Y X) :
    pCore 2 G ≤ centralizerModCore Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQn : (pCore 2 G).Normal := pCore_normal
  have hQY := pCore_le_normalizer_Y h
  have hYQ : Y ≤ Subgroup.normalizer (pCore 2 G : Set G) := by
    rw [Subgroup.normalizer_eq_top (pCore 2 G)]
    exact le_top
  have hM : ⁅pCore 2 G, Y⁆ ≤ oTwoIn Y := commutator_le_oTwoIn_of_normalizes pCore_isPGroup hQY hYQ
  intro g hg
  exact ⟨hQY hg, fun x hx => hM (Subgroup.commutator_mem_commutator hg hx)⟩

theorem centralizerModCore_le [V.Normal] (h : PerfCtx V Y X) :
    centralizerModCore X ≤ centralizerModCore Y := by
  intro a ha
  have hc : ∀ x ∈ X, ⁅a, x⁆ ∈ Subgroup.centralizer (V : Set G) := fun x hx =>
    commutator_centralizerModCore_le h (Subgroup.commutator_mem_commutator ha hx)
  have haY : a ∈ Subgroup.normalizer (Y : Set G) := mem_normalizer_of_commutator_mem h ha.1 hc
  refine ⟨haY, fun y hy => ?_⟩
  have h1 : ⁅a, y⁆ ∈ Y := by
    have : a * y * a⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp haY y).mp hy
    rw [commutatorElement_def]
    exact Y.mul_mem this (Y.inv_mem hy)
  have h2 : ⁅a, y⁆ ∈ oTwoIn X := ha.2 y (h.hYX hy)
  have hD : Y ⊓ oTwoIn X ≤ oTwoIn Y := by
    refine le_oTwoIn_of_isPGroup inf_le_left ?_ ?_
    · exact (isPGroup_oTwoIn X).to_le inf_le_right
    · refine le_trans (le_inf Subgroup.le_normalizer ?_) Subgroup.inf_normalizer_le_normalizer_inf
      intro g hg
      exact normalizer_le_normalizer_oTwoIn X (Subgroup.le_normalizer (h.hYX hg))
  exact hD ⟨h1, h2⟩

theorem normalizer_sup_le [V.Normal] (h : PerfCtx V Y X) :
    Subgroup.normalizer ((X ⊔ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) ≤
      Subgroup.normalizer (X : Set G) := by
  set C : Subgroup G := Subgroup.centralizer (V : Set G) with hC
  have hCnorm : C.Normal := inferInstance
  intro g hg
  set X' : Subgroup G := X.map (MulAut.conj g).toMonoidHom with hX'
  have hmemX' : ∀ z, z ∈ X' ↔ g⁻¹ * z * g ∈ X := fun z => by
    rw [hX', Subgroup.mem_map_equiv]
    simp
  have hgn : ∀ z, z ∈ X ⊔ C ↔ g * z * g⁻¹ ∈ X ⊔ C := fun z => Subgroup.mem_normalizer_iff.mp hg z
  have hgn' : ∀ z, z ∈ X ⊔ C ↔ g⁻¹ * z * g ∈ X ⊔ C := fun z => by
    have := hgn (g⁻¹ * z * g)
    simpa [mul_assoc] using this.symm
  have hXN : X ⊔ C ≤ Subgroup.normalizer (X : Set G) := sup_le Subgroup.le_normalizer h.hCX
  have hX'le : X' ≤ X ⊔ C := by
    rintro _ ⟨x, hx, rfl⟩
    have := (hgn x).mp (Subgroup.mem_sup_left hx)
    simpa [MulAut.conj_apply] using this
  have hCX' : C ≤ Subgroup.normalizer (X' : Set G) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro z
    have hcn : g⁻¹ * c * g ∈ C := by
      simpa [mul_assoc] using hCnorm.conj_mem c hc g⁻¹
    have hcX := Subgroup.mem_normalizer_iff.mp (h.hCX hcn) (g⁻¹ * z * g)
    rw [hmemX', hmemX']
    have e : g⁻¹ * (c * z * c⁻¹) * g = (g⁻¹ * c * g) * (g⁻¹ * z * g) * (g⁻¹ * c * g)⁻¹ := by group
    rw [e]
    exact hcX
  have hX'N : X' ≤ Subgroup.normalizer (X : Set G) := hX'le.trans hXN
  have hXX'C : X ≤ X' ⊔ C := by
    intro x hx
    have h1 : g⁻¹ * x * g ∈ X ⊔ C := (hgn' x).mp (Subgroup.mem_sup_left hx)
    have h2 : g⁻¹ * x * g ∈ (X : Set G) * (C : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left X C h.hCX]
      exact h1
    obtain ⟨x₁, hx₁, c, hc, hxc⟩ := h2
    have hx' : x = (g * x₁ * g⁻¹) * (g * c * g⁻¹) := by
      have e1 : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      rw [e1, ← hxc]
      group
    rw [hx']
    refine (X' ⊔ C).mul_mem (Subgroup.mem_sup_left ?_) (Subgroup.mem_sup_right ?_)
    · exact (hmemX' _).mpr (by simpa [mul_assoc] using hx₁)
    · exact hCnorm.conj_mem c hc g
  have hXX'N : X ≤ Subgroup.normalizer (X' : Set G) :=
    hXX'C.trans (sup_le Subgroup.le_normalizer hCX')
  have hNoX' : SubTwo.NoTwoQuotient X' := noTwoQuotient_map (MulAut.conj g) h.hNoX
  have hD : X ⊓ C ≤ Subgroup.normalizer (X' : Set G) := fun d hd => hCX' hd.2
  have hXD : X ≤ X' ⊔ X ⊓ C := by
    conv_lhs => rw [← h.hperf]
    refine Subgroup.commutator_le.mpr fun x₁ hx₁ x₂ hx₂ => ?_
    have h2 : x₂ ∈ (X' : Set G) * (C : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left X' C hCX']
      exact hXX'C hx₂
    obtain ⟨x', hx', c, hc, rfl⟩ := h2
    rw [commutatorElement_mul_right_eq_mul_conj]
    have hx₁N : x₁ ∈ Subgroup.normalizer (X' : Set G) := hXX'N hx₁
    have h3 : ⁅x₁, x'⁆ ∈ X' := by
      have := (Subgroup.mem_normalizer_iff.mp hx₁N x').mp hx'
      rw [commutatorElement_def]
      exact X'.mul_mem this (X'.inv_mem hx')
    have hx'N : x' ∈ Subgroup.normalizer (X : Set G) := hX'N hx'
    have h4 : ⁅x₁, c⁆ ∈ X ⊓ C := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · have h5 : c * x₁⁻¹ * c⁻¹ ∈ X :=
          (Subgroup.mem_normalizer_iff.mp (h.hCX hc) x₁⁻¹).mp (X.inv_mem hx₁)
        have e : ⁅x₁, c⁆ = x₁ * (c * x₁⁻¹ * c⁻¹) := by simp [commutatorElement_def, mul_assoc]
        rw [e]
        exact X.mul_mem hx₁ h5
      · rw [commutatorElement_def]
        exact C.mul_mem (hCnorm.conj_mem c hc x₁) (C.inv_mem hc)
    have h6 : x' * ⁅x₁, c⁆ * x'⁻¹ ∈ X ⊓ C := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp hx'N _).mp h4.1
      · exact hCnorm.conj_mem _ h4.2 x'
    have e : ⁅x₁, x'⁆ * x' * ⁅x₁, c⁆ * x'⁻¹ = ⁅x₁, x'⁆ * (x' * ⁅x₁, c⁆ * x'⁻¹) := by
      simp [mul_assoc]
    rw [e]
    exact (X' ⊔ X ⊓ C).mul_mem (Subgroup.mem_sup_left h3) (Subgroup.mem_sup_right h6)
  have hXX' : X ≤ X' := le_of_noTwoQuotient h.hNoX h.hN0 hD hXD
  have hXeq : X = X' := by
    refine Subgroup.eq_of_le_of_card_ge hXX' ?_
    rw [hX', Subgroup.card_map_of_injective (MulAut.conj g).injective]
  refine Subgroup.mem_normalizer_iff.mpr fun y => ⟨fun hy => ?_, fun hy => ?_⟩
  · have : g * y * g⁻¹ ∈ X' := ⟨y, hy, by simp [MulAut.conj_apply]⟩
    rw [hXeq]
    exact this
  · rw [hXeq, hmemX'] at hy
    simpa [mul_assoc] using hy

end PerfCtx

structure XCtx (V Y X : Subgroup G) [Finite G] : Prop where
  hYX : Y ≤ X
  hXs : X.IsSubnormal
  hNoY : SubTwo.NoTwoQuotient Y
  hNoX : SubTwo.NoTwoQuotient X
  hCX : Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (X : Set G)
  hN0 : IsPGroup 2 ↥(X ⊓ Subgroup.centralizer (V : Set G))
  hCY : Subgroup.centralizer (V : Set G) ≤ centralizerModCore Y
  hQY : pCore 2 G ≤ centralizerModCore Y
  hXY : centralizerModCore X ≤ centralizerModCore Y

namespace XCtx

variable [Finite G] {V Y X : Subgroup G}

theorem inf_le_oTwoIn [V.Normal] (h : XCtx V Y X) :
    X ⊓ Subgroup.centralizer (V : Set G) ≤ oTwoIn X := by
  refine le_oTwoIn_of_isPGroup inf_le_left h.hN0 ?_
  refine le_trans (le_inf Subgroup.le_normalizer ?_) Subgroup.inf_normalizer_le_normalizer_inf
  rw [Subgroup.normalizer_eq_top (Subgroup.centralizer (V : Set G))]
  exact le_top

theorem oTwoIn_le_pCore (h : XCtx V Y X) : oTwoIn X ≤ pCore 2 G :=
  ThreeFromEight.oTwoIn_le_pCore_of_isSubnormal h.hXs

theorem _root_.CFSG.CGT.PushingUpLit.CGT6.PerfCtx.toXCtx [V.Normal] (h : PerfCtx V Y X) :
    XCtx V Y X :=
  { hYX := h.hYX, hXs := h.hXs, hNoY := h.hNoY, hNoX := h.hNoX, hCX := h.hCX, hN0 := h.hN0,
    hCY := h.hCY, hQY := h.pCore_le_centralizerModCore, hXY := h.centralizerModCore_le }

theorem of_eq [V.Normal] (hNo : SubTwo.NoTwoQuotient Y) (hs : Y.IsSubnormal)
    (hCY : Subgroup.centralizer (V : Set G) ≤ centralizerModCore Y)
    (hN0 : IsPGroup 2 ↥(Y ⊓ Subgroup.centralizer (V : Set G))) : XCtx V Y Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQn : (pCore 2 G).Normal := pCore_normal
  have hQY : pCore 2 G ≤ Subgroup.normalizer (Y : Set G) := by
    refine SubTwo.le_normalizer_of_isSubnormal_sup hNo pCore_isPGroup ?_
      (isSubnormal_subgroupOf_of_isSubnormal hs (Y ⊔ pCore 2 G))
    rw [Subgroup.normalizer_eq_top (pCore 2 G)]
    exact le_top
  have hYQ : Y ≤ Subgroup.normalizer (pCore 2 G : Set G) := by
    rw [Subgroup.normalizer_eq_top (pCore 2 G)]
    exact le_top
  have hM : ⁅pCore 2 G, Y⁆ ≤ oTwoIn Y :=
    commutator_le_oTwoIn_of_normalizes pCore_isPGroup hQY hYQ
  exact { hYX := le_rfl, hXs := hs, hNoY := hNo, hNoX := hNo,
          hCX := fun _ hg => (hCY hg).1, hN0 := hN0, hCY := hCY,
          hQY := fun g hg => ⟨hQY hg, fun x hx => hM (Subgroup.commutator_mem_commutator hg hx)⟩,
          hXY := le_rfl }

end XCtx

end CFSG.CGT.PushingUpLit.CGT6
