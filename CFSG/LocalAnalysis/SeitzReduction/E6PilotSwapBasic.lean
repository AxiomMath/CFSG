module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotSwapBLiftLift
import CFSG.LocalAnalysis.ComponentClassification.M12CoverKernelBasic

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup
open CFSG.Quasithin (perfectCore derivedSeriesOf)
open scoped commutatorElement

section Commute

variable {G : Type*} [Group G]

theorem swapExists_mul_of_mem_sup {A B : Subgroup G} (hAB : B ≤ centralizer (A : Set G))
    {x : G} (hx : x ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, x = a * b :=
  CFSG.ComponentClassification.M12Cover.CyclicKernel.exists_mul_of_mem_sup_of_commute
    (fun a ha _ hb => mem_centralizer_iff.1 (hAB hb) a ha) hx

theorem swapCommutatorElement_mul_left {x y z : G} (hz : Commute z y) :
    ⁅x * z, y⁆ = ⁅x, y⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  calc x * z * y * (x * z)⁻¹ * y⁻¹ = x * (z * y) * z⁻¹ * x⁻¹ * y⁻¹ := by group
    _ = x * (y * z) * z⁻¹ * x⁻¹ * y⁻¹ := by rw [hz.eq]
    _ = x * y * x⁻¹ * y⁻¹ := by group

theorem swapCommutatorElement_mul_right {x y z : G} (hz : Commute z x) :
    ⁅x, y * z⁆ = ⁅x, y⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  calc x * (y * z) * x⁻¹ * (y * z)⁻¹ = x * y * (z * x⁻¹) * z⁻¹ * y⁻¹ := by group
    _ = x * y * (x⁻¹ * z) * z⁻¹ * y⁻¹ := by rw [hz.inv_right.eq]
    _ = x * y * x⁻¹ * y⁻¹ := by group

theorem swapCommutatorElement_mul_mul {a a' b b' : G} (h1 : Commute a b') (h2 : Commute a' b)
    (h3 : Commute a b) (h4 : Commute a' b') :
    ⁅a * b, a' * b'⁆ = ⁅a, a'⁆ * ⁅b, b'⁆ := by
  rw [commutatorElement_def, commutatorElement_def, commutatorElement_def]
  have e1 : b * a' = a' * b := h2.eq.symm
  have e2 : (b * b' * b⁻¹) * a⁻¹ = a⁻¹ * (b * b' * b⁻¹) :=
    ((h3.mul_right h1).mul_right h3.inv_right).inv_left.eq.symm
  have e3 : (b * b' * b⁻¹ * b'⁻¹) * a'⁻¹ = a'⁻¹ * (b * b' * b⁻¹ * b'⁻¹) :=
    (((h2.mul_right h4).mul_right h2.inv_right).mul_right h4.inv_right).inv_left.eq.symm
  calc a * b * (a' * b') * (a * b)⁻¹ * (a' * b')⁻¹
      = a * (b * a') * b' * b⁻¹ * a⁻¹ * b'⁻¹ * a'⁻¹ := by group
    _ = a * (a' * b) * b' * b⁻¹ * a⁻¹ * b'⁻¹ * a'⁻¹ := by rw [e1]
    _ = a * a' * ((b * b' * b⁻¹) * a⁻¹) * b'⁻¹ * a'⁻¹ := by group
    _ = a * a' * (a⁻¹ * (b * b' * b⁻¹)) * b'⁻¹ * a'⁻¹ := by rw [e2]
    _ = a * a' * a⁻¹ * ((b * b' * b⁻¹ * b'⁻¹) * a'⁻¹) := by group
    _ = a * a' * a⁻¹ * (a'⁻¹ * (b * b' * b⁻¹ * b'⁻¹)) := by rw [e3]
    _ = a * a' * a⁻¹ * a'⁻¹ * (b * b' * b⁻¹ * b'⁻¹) := by group

theorem swapCommutator_sup_le {A B : Subgroup G} (hAB : B ≤ centralizer (A : Set G)) :
    ⁅A ⊔ B, A ⊔ B⁆ ≤ ⁅A, A⁆ ⊔ ⁅B, B⁆ := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨a, ha, b, hb, rfl⟩ := swapExists_mul_of_mem_sup hAB hx
  obtain ⟨a', ha', b', hb', rfl⟩ := swapExists_mul_of_mem_sup hAB hy
  have hc : ∀ c ∈ A, ∀ d ∈ B, Commute c d := fun c hc d hd => mem_centralizer_iff.1 (hAB hd) c hc
  rw [swapCommutatorElement_mul_mul (hc a ha b' hb') (hc a' ha' b hb) (hc a ha b hb)
    (hc a' ha' b' hb')]
  exact mul_mem (mem_sup_left (commutator_mem_commutator ha ha'))
    (mem_sup_right (commutator_mem_commutator hb hb'))

theorem swapCommutator_eq_bot_of_le_centralizer {Z : Subgroup G}
    (hZ : Z ≤ centralizer (Z : Set G)) : ⁅Z, Z⁆ = ⊥ :=
  commutator_eq_bot_iff_le_centralizer.2 hZ

theorem swapPerfect_le_of_le_sup_central {A Z P : Subgroup G} (hZA : Z ≤ centralizer (A : Set G))
    (hZ : Z ≤ centralizer (Z : Set G)) (hA : ⁅A, A⁆ ≤ A) (hP : ⁅P, P⁆ = P) (hPA : P ≤ A ⊔ Z) :
    P ≤ A := by
  calc P = ⁅P, P⁆ := hP.symm
    _ ≤ ⁅A ⊔ Z, A ⊔ Z⁆ := commutator_mono hPA hPA
    _ ≤ ⁅A, A⁆ ⊔ ⁅Z, Z⁆ := swapCommutator_sup_le hZA
    _ ≤ A := by rw [swapCommutator_eq_bot_of_le_centralizer hZ, sup_bot_eq]; exact hA

theorem swapPerfect_le_sup_perfectCore [Finite G] {A B P : Subgroup G}
    (hAB : B ≤ centralizer (A : Set G)) (hP : ⁅P, P⁆ = P) (hPAB : P ≤ A ⊔ B) :
    P ≤ perfectCore A ⊔ perfectCore B := by
  have hstep : ∀ n, P ≤ derivedSeriesOf A n ⊔ derivedSeriesOf B n := by
    intro n
    induction n with
    | zero => exact hPAB
    | succ n ih =>
      rw [CFSG.Quasithin.derivedSeriesOf_succ, CFSG.Quasithin.derivedSeriesOf_succ]
      have hc : derivedSeriesOf B n ≤ centralizer (derivedSeriesOf A n : Set G) :=
        (CFSG.Quasithin.derivedSeriesOf_le B n).trans
          (hAB.trans (centralizer_le (SetLike.coe_subset_coe.2
            (CFSG.Quasithin.derivedSeriesOf_le A n))))
      calc P = ⁅P, P⁆ := hP.symm
        _ ≤ ⁅derivedSeriesOf A n ⊔ derivedSeriesOf B n,
            derivedSeriesOf A n ⊔ derivedSeriesOf B n⁆ := commutator_mono ih ih
        _ ≤ _ := swapCommutator_sup_le hc
  obtain ⟨n, hn⟩ := CFSG.Quasithin.exists_perfectCore_eq A
  obtain ⟨m, hm⟩ := CFSG.Quasithin.exists_perfectCore_eq B
  rw [hn (max n m) (le_max_left _ _), hm (max n m) (le_max_right _ _)]
  exact hstep _

end Commute

section Centralizer

variable {G : Type*} [Group G]

theorem swapMem_centralizer_of_perfect {P Z : Subgroup G} (hP : ⁅P, P⁆ = P)
    (hZP : Z ≤ centralizer (P : Set G)) (hZ : Z ≤ centralizer (Z : Set G)) {c : G}
    (hc : ∀ x ∈ P, x⁻¹ * (c * x * c⁻¹) ∈ Z) : c ∈ centralizer (P : Set G) := by
  have h : P ≤ centralizer ({c} : Set G) := by
    rw [← hP, Subgroup.commutator_le]
    intro x hx y hy
    rw [mem_centralizer_singleton_iff]
    have hzx := hc x hx
    have hzy := hc y hy
    set z := x⁻¹ * (c * x * c⁻¹) with hzdef
    set z' := y⁻¹ * (c * y * c⁻¹) with hz'def
    have hcx : c * x * c⁻¹ = x * z := by rw [hzdef, mul_inv_cancel_left]
    have hcy : c * y * c⁻¹ = y * z' := by rw [hz'def, mul_inv_cancel_left]
    have hzy' : Commute z y := (mem_centralizer_iff.1 (hZP hzx) y hy).symm
    have hzz' : Commute z z' := (mem_centralizer_iff.1 (hZ hzx) z' hzy).symm
    have hz'x : Commute z' x := (mem_centralizer_iff.1 (hZP hzy) x hx).symm
    have key : c * ⁅x, y⁆ * c⁻¹ = ⁅x, y⁆ := by
      have e : c * ⁅x, y⁆ * c⁻¹ = ⁅c * x * c⁻¹, c * y * c⁻¹⁆ := by
        simp only [commutatorElement_def]
        group
      rw [e, hcx, hcy, swapCommutatorElement_mul_left (hzy'.mul_right hzz'),
        swapCommutatorElement_mul_right hz'x]
    calc ⁅x, y⁆ * c = c * ⁅x, y⁆ * c⁻¹ * c := by rw [key]
      _ = c * ⁅x, y⁆ := by group
  rw [mem_centralizer_iff]
  intro p hp
  exact mem_centralizer_singleton_iff.1 (h hp)

theorem swapNormal_le_centralizer_or_le {F N : Subgroup G} {S : Type*} [Group S]
    [IsSimpleGroup S] (φ : F →* S) (hφ : Function.Surjective φ)
    (hker : ∀ x : F, φ x = 1 → (x : G) ∈ centralizer (F : Set G)) (hFp : ⁅F, F⁆ = F)
    (hNF : N ≤ F) (hFN : F ≤ normalizer (N : Set G)) :
    N ≤ centralizer (F : Set G) ∨ F ≤ N := by
  have hn : (N.subgroupOf F).Normal := ⟨fun n hn g => by
    rw [mem_subgroupOf] at hn ⊢
    simpa using (mem_normalizer_iff.1 (hFN g.2) n).1 hn⟩
  have hnS : ((N.subgroupOf F).map φ).Normal := hn.map φ hφ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N.subgroupOf F).map φ) with h | h
  · left
    intro x hx
    have hx' : (⟨x, hNF hx⟩ : F) ∈ N.subgroupOf F := mem_subgroupOf.2 hx
    have h1 : φ ⟨x, hNF hx⟩ = 1 := by
      have := mem_map_of_mem φ hx'
      rw [h, mem_bot] at this
      exact this
    exact hker _ h1
  · right
    refine F4Pilot.perfect_le_of_forall_exists_commute hFp hNF fun a ha => ?_
    have hφa : φ ⟨a, ha⟩ ∈ (N.subgroupOf F).map φ := h ▸ mem_top _
    obtain ⟨n, hn', hna⟩ := hφa
    refine ⟨n, mem_subgroupOf.1 hn', (n : G)⁻¹ * a, by group, fun b hb => ?_⟩
    have hk : φ (n⁻¹ * ⟨a, ha⟩) = 1 := by rw [map_mul, map_inv, hna, inv_mul_cancel]
    have := mem_centralizer_iff.1 (hker _ hk) b hb
    exact this.symm

end Centralizer

section Twist

variable {G : Type*} [Group G]

theorem swapLe_of_inf_le_centralizer {F F₂ F' : Subgroup G} (h₂ : F₂ ≤ centralizer (F : Set G))
    (hF₂ : ⁅F₂, F₂⁆ = F₂) (hF' : ⁅F', F'⁆ = F') (hF'M : F' ≤ F ⊔ F₂)
    (hN : F₂ ≤ normalizer (F' : Set G)) (hinf : F' ⊓ F₂ ≤ centralizer (F₂ : Set G)) :
    F' ≤ F := by
  have hF₂c : F ≤ centralizer (F₂ : Set G) := le_centralizer_iff.1 h₂
  have hF'N : F' ≤ normalizer (F₂ : Set G) :=
    hF'M.trans (sup_le (hF₂c.trans (centralizer_le_normalizer _)) le_normalizer)
  have hc1 : ⁅F₂, F'⁆ ≤ F' := le_normalizer_iff_commutator_le_right.1 hN
  have hc2 : ⁅F₂, F'⁆ ≤ F₂ := le_normalizer_iff_commutator_le_left.1 hF'N
  have hZc : F' ⊓ F₂ ≤ centralizer ((F' ⊓ F₂ : Subgroup G) : Set G) := fun z hz =>
    mem_centralizer_iff.2 fun w hw => mem_centralizer_iff.1 (hinf hz) w hw.2
  have hcen : F' ≤ centralizer (F₂ : Set G) := fun c hc =>
    swapMem_centralizer_of_perfect hF₂ hinf hZc fun x hx => by
      have e : x⁻¹ * (c * x * c⁻¹) = ⁅x⁻¹, c⁆ := by rw [commutatorElement_def, inv_inv]; group
      rw [e]
      exact ⟨hc1 (commutator_mem_commutator (inv_mem hx) hc),
        hc2 (commutator_mem_commutator (inv_mem hx) hc)⟩
  have hF'le : F' ≤ F ⊔ (F₂ ⊓ centralizer (F₂ : Set G)) := by
    intro c hc
    obtain ⟨a, ha, b, hb, rfl⟩ := swapExists_mul_of_mem_sup h₂ (hF'M hc)
    have hb' : b ∈ centralizer (F₂ : Set G) := by
      have := mul_mem (inv_mem (hF₂c ha)) (hcen hc)
      rwa [inv_mul_cancel_left] at this
    exact mul_mem (mem_sup_left ha) (mem_sup_right ⟨hb, hb'⟩)
  refine swapPerfect_le_of_le_sup_central (inf_le_left.trans h₂) (fun z hz => ?_)
    (CFSG.Quasithin.A3.commutator_self_le F) hF' hF'le
  exact mem_centralizer_iff.2 fun w hw => (mem_centralizer_iff.1 hz.2 w hw.1)

theorem swapEq_or_eq_conj {t : G} {F F' : Subgroup G}
    (hF : F.map (MulAut.conj t).toMonoidHom ≤ centralizer (F : Set G))
    (hF'c : F'.map (MulAut.conj t).toMonoidHom ≤ centralizer (F' : Set G))
    (hsup : F' ⊔ F'.map (MulAut.conj t).toMonoidHom = F ⊔ F.map (MulAut.conj t).toMonoidHom)
    (hFp : ⁅F, F⁆ = F) (hFtp : ⁅F.map (MulAut.conj t).toMonoidHom,
      F.map (MulAut.conj t).toMonoidHom⁆ = F.map (MulAut.conj t).toMonoidHom)
    (hF'p : ⁅F', F'⁆ = F') (hF'ne : F' ≠ ⊥)
    (hqs : ∀ N : Subgroup G, N ≤ F → F ≤ normalizer (N : Set G) →
      N ≤ centralizer (F : Set G) ∨ F ≤ N)
    (hqst : ∀ N : Subgroup G, N ≤ F.map (MulAut.conj t).toMonoidHom →
      F.map (MulAut.conj t).toMonoidHom ≤ normalizer (N : Set G) →
      N ≤ centralizer (F.map (MulAut.conj t).toMonoidHom : Set G) ∨
        F.map (MulAut.conj t).toMonoidHom ≤ N) :
    F' = F ∨ F' = F.map (MulAut.conj t).toMonoidHom := by
  set Ft := F.map (MulAut.conj t).toMonoidHom with hFtdef
  set F't := F'.map (MulAut.conj t).toMonoidHom with hF'tdef
  have hFt' : F ≤ centralizer (Ft : Set G) := le_centralizer_iff.1 hF
  have hF'M : F' ≤ F ⊔ Ft := hsup ▸ le_sup_left
  have hMN : F ⊔ Ft ≤ normalizer (F' : Set G) := by
    rw [← hsup]
    exact sup_le le_normalizer (hF'c.trans (centralizer_le_normalizer _))
  have hFN : F ≤ normalizer (F' : Set G) := le_sup_left.trans hMN
  have hFtN : Ft ≤ normalizer (F' : Set G) := le_sup_right.trans hMN
  have hn1 : F ≤ normalizer ((F' ⊓ F : Subgroup G) : Set G) := fun g hg =>
    mem_normalizer_iff.2 fun x => by
      rw [mem_inf, mem_inf]
      exact and_congr (mem_normalizer_iff.1 (hFN hg) x) (mem_normalizer_iff.1 (le_normalizer hg) x)
  have hn2 : Ft ≤ normalizer ((F' ⊓ Ft : Subgroup G) : Set G) := fun g hg =>
    mem_normalizer_iff.2 fun x => by
      rw [mem_inf, mem_inf]
      exact and_congr (mem_normalizer_iff.1 (hFtN hg) x) (mem_normalizer_iff.1 (le_normalizer hg) x)
  have hbot : ∀ P : Subgroup G, ⁅P, P⁆ = P → P ≤ centralizer (P : Set G) → P = ⊥ := fun P hP hc => by
    rw [← hP]
    exact commutator_eq_bot_iff_le_centralizer.2 hc
  rcases hqs _ inf_le_right hn1 with h1 | h1 <;> rcases hqst _ inf_le_right hn2 with h2 | h2
  ·
    exfalso
    have hle1 : F' ≤ F := swapLe_of_inf_le_centralizer hF hFtp hF'p hF'M hFtN h2
    have hle2 : F' ≤ Ft := swapLe_of_inf_le_centralizer hFt' hFp hF'p
      (by rw [sup_comm]; exact hF'M) hFN h1
    exact hF'ne (hbot F' hF'p fun c hc => centralizer_le (SetLike.coe_subset_coe.2 hle1)
      (hF (hle2 hc)))
  ·
    right
    exact le_antisymm (swapLe_of_inf_le_centralizer hFt' hFp hF'p
      (by rw [sup_comm]; exact hF'M) hFN h1) (h2.trans inf_le_left)
  ·
    left
    exact le_antisymm (swapLe_of_inf_le_centralizer hF hFtp hF'p hF'M hFtN h2) (h1.trans inf_le_left)
  ·
    exfalso
    have hF'eq : F' = F ⊔ Ft := le_antisymm hF'M (sup_le (h1.trans inf_le_left) (h2.trans inf_le_left))
    have hF'tle : F't ≤ F' := by rw [hF'eq, ← hsup]; exact le_sup_right
    have hF'tp : ⁅F't, F't⁆ = F't := by rw [hF'tdef, ← map_commutator, hF'p]
    have h3 : F't = ⊥ := hbot F't hF'tp fun c hc =>
      centralizer_le (SetLike.coe_subset_coe.2 hF'tle) (hF'c hc)
    apply hF'ne
    rw [hF'tdef] at h3
    exact (map_eq_bot_iff_of_injective _ (MulAut.conj t).injective).1 h3

end Twist

end CFSG.SeitzReduction.E6Pilot
