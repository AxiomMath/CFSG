module

public import CFSG.GH74.Generic.BProg.B3.S3T2A7Defs

public section

namespace CFSG.GH74.Generic.BProg.B3.S3T2A7Loc

open CFSG CFSG.Assembly.Dichotomy Subgroup

variable {T : Type} [Group T]

theorem center_eq_bot_of_simple (hs : IsSimpleGroup T) (hna : ∃ a b : T, a * b ≠ b * a) :
    center T = ⊥ := by
  obtain ⟨a, b, hab⟩ := hna
  have := hs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center T) with h | h
  · exact h
  · exact absurd (mem_center_iff.mp (h ▸ mem_top b) a) hab

theorem exists_noncomm_of_not_prime [Finite T] (hs : IsSimpleGroup T)
    (hp : ¬ (Nat.card T).Prime) : ∃ a b : T, a * b ≠ b * a := by
  by_contra h
  have hc : ∀ a b : T, a * b = b * a := fun a b => by
    by_contra hab
    exact h ⟨a, b, hab⟩
  have := hs
  let _ : CommGroup T := { (inferInstance : Group T) with mul_comm := hc }
  exact hp (IsSimpleGroup.prime_card (α := T))

theorem center_eq_bot_of_equiv {G₀ : Type} [Group G₀] (e : T ≃* G₀) (h : center G₀ = ⊥) :
    center T = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [mem_bot]
  have hez : e z ∈ center G₀ := by
    rw [mem_center_iff]
    intro g
    obtain ⟨g', rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, mem_center_iff.mp hz g']
  rw [h, mem_bot] at hez
  exact e.injective (by rw [hez, map_one])

theorem center_eq_bot_of_centralizer {A : Type} [Group A] {P : Subgroup A}
    (h : centralizer (P : Set A) = ⊥) : center ↥P = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [mem_bot]
  have hz' : (z : A) ∈ centralizer (P : Set A) := by
    rw [mem_centralizer_iff]
    intro g hg
    exact congrArg Subtype.val (mem_center_iff.mp hz ⟨g, hg⟩)
  rw [h, mem_bot] at hz'
  exact Subtype.ext hz'

theorem conj_range_normal : (MulAut.conj : T →* MulAut T).range.Normal :=
  ⟨fun _ ⟨s, hs⟩ g => ⟨g s, by
    rw [← hs]
    ext x
    simp [MulAut.mul_apply, MulAut.conj_apply, MulAut.inv_apply]⟩⟩

theorem conj_injective (hZ : center T = ⊥) :
    Function.Injective (MulAut.conj : T →* MulAut T) := by
  rw [injective_iff_map_eq_one]
  intro t ht
  rw [← mem_bot, ← hZ, mem_center_iff]
  intro g
  have h2 := congrArg (fun f : MulAut T => f g) ht
  simp only [MulAut.conj_apply, MulAut.one_apply] at h2
  rw [mul_inv_eq_iff_eq_mul] at h2
  exact h2.symm

theorem exists_inner_normal (hZ : center T = ⊥) {H : Subgroup (MulAut T)}
    (hH : (MulAut.conj : T →* MulAut T).range ≤ H) :
    ∃ S : Subgroup ↥H, S.Normal ∧ Nonempty (↥S ≃* T) ∧ centralizer (S : Set ↥H) = ⊥ := by
  refine ⟨(MulAut.conj : T →* MulAut T).range.subgroupOf H, conj_range_normal.subgroupOf H,
    ⟨(subgroupOfEquivOfLe hH).trans (MonoidHom.ofInjective (conj_injective hZ)).symm⟩, ?_⟩
  rw [eq_bot_iff_forall]
  intro h hh
  rw [mem_centralizer_iff] at hh
  apply Subtype.ext
  ext g
  have hs : (⟨MulAut.conj g, hH ⟨g, rfl⟩⟩ : ↥H) ∈
      (MulAut.conj : T →* MulAut T).range.subgroupOf H := ⟨g, rfl⟩
  have hcomm := hh _ hs
  have h1 : ∀ x : T, g * (h : MulAut T) x * g⁻¹ =
      (h : MulAut T) g * (h : MulAut T) x * ((h : MulAut T) g)⁻¹ := by
    intro x
    have := congrArg (fun f : ↥H => (f : MulAut T) x) hcomm
    simp only [coe_mul, MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv] at this
    exact this
  have hz : ((h : MulAut T) g)⁻¹ * g ∈ center T := by
    rw [mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := (h : MulAut T).surjective y
    calc (h : MulAut T) x * (((h : MulAut T) g)⁻¹ * g)
        = ((h : MulAut T) g)⁻¹ *
            (((h : MulAut T) g * (h : MulAut T) x * ((h : MulAut T) g)⁻¹) * g) := by group
      _ = ((h : MulAut T) g)⁻¹ * ((g * (h : MulAut T) x * g⁻¹) * g) := by rw [h1 x]
      _ = (((h : MulAut T) g)⁻¹ * g) * (h : MulAut T) x := by group
  rw [hZ, mem_bot, inv_mul_eq_one] at hz
  simpa using hz

theorem involutionOddCore_eq_bot {X : Type} [Group X] {t : X}
    (h : CFSG.oddCore ↥(centralizer ({t} : Set X)) = ⊥) : involutionOddCore t = ⊥ := by
  unfold involutionOddCore
  have h' : CFSG.Assembly.oddCore ↥(centralizer ({t} : Set X)) = ⊥ := h
  rw [h', Subgroup.map_bot]

theorem locBal1Two_of_normal [Finite T] (hZ : center T = ⊥)
    (hT : ∀ (X : Type) [Group X] [Finite X] (S : Subgroup X) [S.Normal], Nonempty (↥S ≃* T) →
      centralizer (S : Set X) = ⊥ → ∀ t : X, orderOf t = 2 →
        CFSG.oddCore ↥(centralizer ({t} : Set X)) = ⊥) :
    S3T2A7.LocBal1Two T := by
  intro H hH t ht
  have : Finite (MulAut T) :=
    Finite.of_injective (fun f : MulAut T => (f : T → T)) DFunLike.coe_injective
  obtain ⟨S, hSn, hST, hC⟩ := exists_inner_normal hZ hH
  exact involutionOddCore_eq_bot (hT ↥H S hST hC t ht)

theorem locBal1Two_of_normal_equiv [Finite T] {G₀ : Type} [Group G₀] (ψ : T ≃* G₀)
    (hZ : center G₀ = ⊥)
    (hG : ∀ (X : Type) [Group X] [Finite X] (S : Subgroup X) [S.Normal], Nonempty (↥S ≃* G₀) →
      centralizer (S : Set X) = ⊥ → ∀ t : X, orderOf t = 2 →
        CFSG.oddCore ↥(centralizer ({t} : Set X)) = ⊥) :
    S3T2A7.LocBal1Two T :=
  locBal1Two_of_normal (center_eq_bot_of_equiv ψ hZ) fun X _ _ S _ ⟨e⟩ hC t ht =>
    hG X S ⟨e.trans ψ⟩ hC t ht

theorem forall_inner_of_equiv {G₀ : Type} [Group G₀] (e : T ≃* G₀)
    (h : ∀ φ : MulAut G₀, ∃ g : G₀, φ = MulAut.conj g) :
    ∀ φ : MulAut T, ∃ g : T, φ = MulAut.conj g := by
  intro φ
  obtain ⟨g, hg⟩ := h (MulAut.congr e φ)
  refine ⟨e.symm g, MulEquiv.ext fun x => e.injective ?_⟩
  have := congrArg (fun ψ : MulAut G₀ => ψ (e x)) hg
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    MulAut.conj_apply] at this
  rw [this, MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem locBal1Two_of_inner (hZ : center T = ⊥)
    (hInn : ∀ φ : MulAut T, ∃ g : T, φ = MulAut.conj g)
    (hO : ∀ t : T, orderOf t = 2 → CFSG.oddCore ↥(centralizer ({t} : Set T)) = ⊥) :
    S3T2A7.LocBal1Two T := by
  intro H hH b hb
  let φ : T →* ↥H := (MulAut.conj : T →* MulAut T).codRestrict H fun g => hH ⟨g, rfl⟩
  have hinj : Function.Injective φ := fun s t hst =>
    conj_injective hZ (congrArg Subtype.val hst)
  have hsurj : Function.Surjective φ := by
    intro h
    obtain ⟨g, hg⟩ := hInn h.1
    exact ⟨g, Subtype.ext hg.symm⟩
  let e : T ≃* ↥H := MulEquiv.ofBijective φ ⟨hinj, hsurj⟩
  obtain ⟨t, rfl⟩ := e.surjective b
  have ht : orderOf t = 2 := by rwa [MulEquiv.orderOf_eq] at hb
  have h := involutionOddCore_map e t
  rw [involutionOddCore_eq_bot (hO t ht), Subgroup.map_bot] at h
  exact h.symm

end CFSG.GH74.Generic.BProg.B3.S3T2A7Loc
