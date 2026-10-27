module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.Wreath
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.AutA6Three

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup Wreath
open scoped commutatorElement

section Cover

variable {G : Type*} [Group G]

@[expose] def s11Pi (L₁ : Subgroup G) (e : ↥L₁ ⧸ center ↥L₁ ≃* alternatingGroup (Fin 6)) :
    ↥L₁ →* alternatingGroup (Fin 6) :=
  e.toMonoidHom.comp (QuotientGroup.mk' (center ↥L₁))

variable {L₁ : Subgroup G} {e : ↥L₁ ⧸ center ↥L₁ ≃* alternatingGroup (Fin 6)}

theorem s11Pi_eq_one_iff (z : ↥L₁) : s11Pi L₁ e z = 1 ↔ z ∈ center ↥L₁ := by
  show e (QuotientGroup.mk z) = 1 ↔ _
  rw [map_eq_one_iff _ e.injective, QuotientGroup.eq_one_iff]

theorem s11Pi_surjective : Function.Surjective (s11Pi L₁ e) :=
  e.surjective.comp (QuotientGroup.mk'_surjective _)

theorem s11_ker {u : G} (hu : u * u = 1) (hZ : ∀ z ∈ center ↥L₁, (z : G) ∈ zpowers u)
    {z : ↥L₁} (hz : s11Pi L₁ e z = 1) : (∀ w : ↥L₁, z * w = w * z) ∧ z * z = 1 := by
  have hc : z ∈ center ↥L₁ := (s11Pi_eq_one_iff z).1 hz
  refine ⟨fun w => (mem_center_iff.1 hc w).symm, ?_⟩
  obtain ⟨n, hn⟩ := mem_zpowers_iff.1 (hZ z hc)
  apply Subtype.ext
  rw [Subgroup.coe_mul, ← hn, ← zpow_add, ← two_mul, zpow_mul]
  have : u ^ (2 : ℤ) = 1 := by rw [zpow_two, hu]
  rw [this, one_zpow]
  rfl

theorem s11_comm_of_cube {u : G} (hu : u * u = 1) (hZ : ∀ z ∈ center ↥L₁, (z : G) ∈ zpowers u)
    {a b : ↥L₁} (ha : a ^ 3 = 1) (hab : s11Pi L₁ e a * s11Pi L₁ e b = s11Pi L₁ e b * s11Pi L₁ e a) :
    a * b = b * a := by
  set z : ↥L₁ := a * b * a⁻¹ * b⁻¹ with hz
  have hz1 : s11Pi L₁ e z = 1 := by
    rw [hz]
    simp only [map_mul, map_inv]
    rw [hab]
    group
  obtain ⟨hzc, hz2⟩ := s11_ker hu hZ hz1
  have h1 : a * b * a⁻¹ = z * b := by rw [hz]; group
  have h2 : a * (z * b) * a⁻¹ = z * (a * b * a⁻¹) := by
    calc a * (z * b) * a⁻¹ = (a * z) * b * a⁻¹ := by group
      _ = (z * a) * b * a⁻¹ := by rw [← hzc a]
      _ = z * (a * b * a⁻¹) := by group
  have h3 : a * a * b * (a * a)⁻¹ = b := by
    calc a * a * b * (a * a)⁻¹ = a * (a * b * a⁻¹) * a⁻¹ := by group
      _ = a * (z * b) * a⁻¹ := by rw [h1]
      _ = z * (z * b) := by rw [h2, h1]
      _ = (z * z) * b := by group
      _ = b := by rw [hz2]; group
  have ha' : a⁻¹ = a * a := by
    have : a * (a * a) = 1 := by
      have h := ha
      rw [pow_succ, pow_two] at h
      rw [← mul_assoc]; exact h
    exact inv_eq_of_mul_eq_one_right this
  have h4 : a⁻¹ * b * a = b := by
    have : a * a * b * (a * a)⁻¹ = b := h3
    have e2 : (a * a)⁻¹ = a := by
      rw [← ha']; group
    rw [e2] at this
    calc a⁻¹ * b * a = a * a * b * a := by rw [ha']
      _ = b := this
  calc a * b = a * (a⁻¹ * b * a) := by rw [h4]
    _ = b * a := by group

theorem s11_exists_X {u : G} (hu : u * u = 1) (hZ : ∀ z ∈ center ↥L₁, (z : G) ∈ zpowers u)
    {x : G} (hx : x ∈ L₁) (hx3 : orderOf x = 3) :
    ∃ X : Subgroup G, X ≤ L₁ ⊓ centralizer ({x} : Set G) ∧ Nat.card X = 9 ∧
      (∀ g ∈ L₁ ⊓ centralizer ({x} : Set G), orderOf g = 3 → g ∈ X) ∧ (∀ a ∈ X, a ^ 3 = 1) ∧
      (∀ a ∈ X, ∀ b ∈ X, a * b = b * a) ∧
      (∀ b ∈ centralizer ({s11Pi L₁ e ⟨x, hx⟩} : Set (alternatingGroup (Fin 6))),
        ∃ c : ↥L₁, (c : G) ∈ X ∧ s11Pi L₁ e c = b) ∧
      (∀ c : ↥L₁, (c : G) ∈ X →
        s11Pi L₁ e c ∈ centralizer ({s11Pi L₁ e ⟨x, hx⟩} : Set (alternatingGroup (Fin 6)))) ∧
      orderOf (s11Pi L₁ e ⟨x, hx⟩) = 3 := by
  set π := s11Pi L₁ e with hπ
  set x' : ↥L₁ := ⟨x, hx⟩ with hx'
  have hx'3 : x' ^ 3 = 1 := by
    apply Subtype.ext
    have := pow_orderOf_eq_one x
    rw [hx3] at this
    exact this
  have hπx3 : orderOf (π x') = 3 := by
    have h1 : (π x') ^ 3 = 1 := by rw [← map_pow, hx'3, map_one]
    have h2 : π x' ≠ 1 := by
      intro h
      obtain ⟨-, hsq⟩ := s11_ker hu hZ h
      have : x' = 1 := by
        calc x' = x' ^ 3 := by rw [pow_succ, pow_two, hsq, one_mul]
          _ = 1 := hx'3
      have h3 : x = 1 := congrArg Subtype.val this
      rw [h3, orderOf_one] at hx3
      omega
    exact orderOf_eq_prime h1 h2
  have hcentπ : ∀ a : ↥L₁, a * x' = x' * a → π a ∈ centralizer ({π x'} : Set (alternatingGroup (Fin 6))) := by
    intro a h
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, h]
  have hcomm : ∀ a b : ↥L₁, a * x' = x' * a → b * x' = x' * b → a ^ 3 = 1 → a * b = b * a := by
    intro a b ha hb ha3
    refine s11_comm_of_cube (e := e) hu hZ ha3 ?_
    exact centralizer_commute_of_orderOf_eq_three hπx3 _ (hcentπ a ha) _ (hcentπ b hb)
  let Xl : Subgroup ↥L₁ :=
    { carrier := {a | a * x' = x' * a ∧ a ^ 3 = 1}
      mul_mem' := by
        rintro a b ⟨ha, ha3⟩ ⟨hb, hb3⟩
        refine ⟨?_, ?_⟩
        · calc a * b * x' = a * (b * x') := mul_assoc _ _ _
            _ = a * (x' * b) := by rw [hb]
            _ = (a * x') * b := (mul_assoc _ _ _).symm
            _ = x' * a * b := by rw [ha]
            _ = x' * (a * b) := mul_assoc _ _ _
        · rw [(show Commute a b from hcomm a b ha hb ha3).mul_pow, ha3, hb3, one_mul]
      one_mem' := ⟨by simp, one_pow 3⟩
      inv_mem' := by
        rintro a ⟨ha, ha3⟩
        refine ⟨?_, by rw [inv_pow, ha3, inv_one]⟩
        exact ((show Commute a x' from ha).inv_left).eq }
  have hXl : ∀ a : ↥L₁, a ∈ Xl ↔ a * x' = x' * a ∧ a ^ 3 = 1 := fun a => Iff.rfl
  have hXab : ∀ a ∈ Xl, ∀ b ∈ Xl, a * b = b * a := fun a ha b hb => hcomm a b ha.1 hb.1 ha.2
  let f : Xl →* alternatingGroup (Fin 6) := π.comp Xl.subtype
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 : π (a : ↥L₁) = 1 := ha
    obtain ⟨-, hsq⟩ := s11_ker hu hZ h1
    apply Subtype.ext
    calc (a : ↥L₁) = (a : ↥L₁) ^ 3 := by rw [pow_succ, pow_two, hsq, one_mul]
      _ = 1 := a.2.2
  have hrange : f.range = centralizer ({π x'} : Set (alternatingGroup (Fin 6))) := by
    ext b
    constructor
    · rintro ⟨a, rfl⟩
      exact hcentπ a a.2.1
    · intro hb
      obtain ⟨b₀, hb₀⟩ := s11Pi_surjective (L₁ := L₁) (e := e) b
      have hb3 : b ^ 3 = 1 := pow_three_of_mem_centralizer hπx3 b hb
      have hz0 : π (b₀ ^ 3) = 1 := by rw [map_pow, hb₀, hb3]
      obtain ⟨-, hz2⟩ := s11_ker hu hZ hz0
      have hc3 : (b₀ ^ 4) ^ 3 = 1 := by
        have h2 : (b₀ ^ 3) ^ 2 = 1 := by rw [pow_two]; exact hz2
        calc (b₀ ^ 4) ^ 3 = ((b₀ ^ 3) ^ 2) ^ 2 := by
              rw [← pow_mul, ← pow_mul, ← pow_mul]
          _ = 1 := by rw [h2, one_pow]
      have hπc : π (b₀ ^ 4) = b := by
        rw [map_pow, hb₀, pow_succ, hb3, one_mul]
      have hcx : b₀ ^ 4 * x' = x' * b₀ ^ 4 := by
        set c := b₀ ^ 4 with hc
        set z : ↥L₁ := c * x' * c⁻¹ * x'⁻¹ with hz
        have hbc : b * π x' = π x' * b := mem_centralizer_singleton_iff.1 hb
        have hz1 : π z = 1 := by
          rw [hz]
          simp only [map_mul, map_inv, hπc]
          rw [hbc]
          group
        obtain ⟨hzc, hz2'⟩ := s11_ker hu hZ hz1
        have h1 : c * x' * c⁻¹ = z * x' := by rw [hz]; group
        have h2 : (c * x' * c⁻¹) ^ 3 = 1 := by
          rw [conj_pow, hx'3]
          simp
        have h3 : (z * x') ^ 3 = z := by
          rw [(show Commute z x' from hzc x').mul_pow, hx'3, mul_one, pow_succ, pow_two, hz2', one_mul]
        have hz0' : z = 1 := by rw [← h3, ← h1, h2]
        have : c * x' * c⁻¹ = x' := by rw [h1, hz0', one_mul]
        rw [mul_inv_eq_iff_eq_mul] at this
        exact this
      exact ⟨⟨b₀ ^ 4, hcx, hc3⟩, hπc⟩
  have hcardXl : Nat.card Xl = 9 := by
    have h1 : Nat.card Xl = Nat.card f.range :=
      Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv
    rw [h1, hrange]
    exact card_centralizer_of_orderOf_eq_three hπx3
  refine ⟨Xl.map L₁.subtype, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hπx3⟩
  · rintro _ ⟨a, ha, rfl⟩
    refine ⟨a.2, mem_centralizer_singleton_iff.2 ?_⟩
    exact congrArg Subtype.val ha.1
  · rw [Subgroup.card_map_of_injective L₁.subtype_injective, hcardXl]
  · intro g hg hg3
    refine ⟨⟨g, hg.1⟩, ⟨?_, ?_⟩, rfl⟩
    · exact Subtype.ext (mem_centralizer_singleton_iff.1 hg.2)
    · apply Subtype.ext
      have := pow_orderOf_eq_one g
      rw [hg3] at this
      exact this
  · rintro _ ⟨a, ha, rfl⟩
    exact congrArg Subtype.val ha.2
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact congrArg Subtype.val (hXab a ha b hb)
  · intro b hb
    obtain ⟨⟨c, hc⟩, hcb⟩ := hrange ▸ hb
    exact ⟨c, ⟨c, hc, rfl⟩, hcb⟩
  · rintro c ⟨a, ha, hac⟩
    have : a = c := Subtype.ext hac
    subst this
    exact hcentπ a ha.1

end Cover

section AutQuot

variable {K : Type*} [Group K]

theorem s11_commutator_mul_central {d d' z z' : K} (hz : z ∈ center K)
    (hz' : z' ∈ center K) : ⁅d * z, d' * z'⁆ = ⁅d, d'⁆ := by
  have h1 : Commute z (d' * z') := (mem_center_iff.1 hz _).symm
  have h2 : Commute d z' := (mem_center_iff.1 hz' _)
  rw [commutatorElement_mul_left_eq_conj_mul, h1.commutator_eq,
    commutatorElement_mul_right_eq_mul_conj, h2.commutator_eq]
  simp

theorem s11_eq_of_forall_mem_center (hK : commutator K = ⊤) (φ ψ : K →* K)
    (h : ∀ g, (φ g)⁻¹ * ψ g ∈ center K) : φ = ψ := by
  have hle : commutator K ≤ MonoidHom.eqLocus φ ψ := by
    rw [commutator_eq_closure, Subgroup.closure_le]
    rintro _ ⟨g, g', rfl⟩
    have hg := h g
    have hg' := h g'
    have e1 : ψ g = φ g * ((φ g)⁻¹ * ψ g) := by group
    have e2 : ψ g' = φ g' * ((φ g')⁻¹ * ψ g') := by group
    show φ ⁅g, g'⁆ = ψ ⁅g, g'⁆
    rw [map_commutatorElement, map_commutatorElement, e1, e2, s11_commutator_mul_central hg hg']
  rw [hK] at hle
  ext g
  exact hle (mem_top g)

@[expose] noncomputable def s11AutQuot (K : Type*) [Group K] :
    MulAut K →* MulAut (K ⧸ center K) where
  toFun φ := QuotientGroup.congr _ _ φ (Subgroup.map_center_eq φ)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with | H x => simp
  map_mul' φ ψ := by
    ext x
    induction x using QuotientGroup.induction_on with | H x => simp

theorem s11AutQuot_mk (φ : MulAut K) (x : K) :
    s11AutQuot K φ (QuotientGroup.mk x) = QuotientGroup.mk (φ x) :=
  QuotientGroup.congr_mk _ _ _ (Subgroup.map_center_eq φ) x

theorem s11AutQuot_injective (hK : commutator K = ⊤) : Function.Injective (s11AutQuot K) := by
  rw [injective_iff_map_eq_one]
  intro φ hφ
  have h : ∀ g, (g : K)⁻¹ * φ g ∈ center K := by
    intro g
    have := DFunLike.congr_fun hφ (QuotientGroup.mk g)
    rw [s11AutQuot_mk, MulAut.one_apply] at this
    exact QuotientGroup.eq.1 this.symm
  have := s11_eq_of_forall_mem_center hK (MonoidHom.id K) φ.toMonoidHom h
  ext g
  exact (DFunLike.congr_fun this g).symm

theorem s11AutQuot_conj (l : K) :
    s11AutQuot K (MulAut.conj l) = MulAut.conj (QuotientGroup.mk l : K ⧸ center K) := by
  ext x
  induction x using QuotientGroup.induction_on with | H x =>
  rw [s11AutQuot_mk]
  simp [MulAut.conj_apply]

end AutQuot

section WrMap

variable {A B : Type*} [Group A] [Group B]

theorem s11_map_eq_base (f : A →* B) {w : Wr2 A} {b₁ b₂ : B} (h : mapHom f w = base b₁ b₂) :
    ∃ a₁ a₂, w = base a₁ a₂ ∧ f a₁ = b₁ ∧ f a₂ = b₂ := by
  rcases eq_base_or_eq_base_mul_tau w with ⟨a, b, rfl⟩ | ⟨a, b, rfl⟩
  · rw [mapHom_base, base_injective] at h
    exact ⟨a, b, rfl, h.1, h.2⟩
  · rw [map_mul, mapHom_base, mapHom_tau] at h
    exact absurd h.symm (base_ne_base_mul_tau _ _ _ _)

theorem s11_mapHom_injective {f : A →* B} (hf : Function.Injective f) :
    Function.Injective (mapHom f) := by
  rw [injective_iff_map_eq_one]
  intro w hw
  obtain ⟨a₁, a₂, rfl, h1, h2⟩ := s11_map_eq_base f (b₁ := 1) (b₂ := 1) (by rw [hw, base_one])
  have : a₁ = 1 := hf (by rw [h1, map_one])
  have : a₂ = 1 := hf (by rw [h2, map_one])
  subst_vars
  exact base_one

end WrMap

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
