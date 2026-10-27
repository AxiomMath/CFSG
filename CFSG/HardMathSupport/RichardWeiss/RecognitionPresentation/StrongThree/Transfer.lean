module

public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Descent2
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Quotient

public section

namespace CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree

open CFSG.Open Subgroup

variable {N : Type*} [Group N] [Finite N] {N₀ : Subgroup N}

omit [Finite N] in
theorem inj_core_of_pgroup (hC3 : ¬ 3 ∣ Nat.card N₀.normalCore) {E : Subgroup N}
    (hE : IsPGroup 3 E) {x : N} (hx : x ∈ E) (h : coreMk N₀ x = 1) : x = 1 := by
  have hmem : x ∈ N₀.normalCore := (QuotientGroup.eq_one_iff x).mp h
  obtain ⟨a, ha⟩ := hE ⟨x, hx⟩
  have h1 : x ^ 3 ^ a = 1 := by simpa using congrArg Subtype.val ha
  have hd1 : orderOf x ∣ 3 ^ a := orderOf_dvd_of_pow_eq_one h1
  have hd2 : orderOf x ∣ Nat.card N₀.normalCore := Subgroup.orderOf_dvd_natCard _ hmem
  have hcop : Nat.Coprime (3 ^ a) (Nat.card N₀.normalCore) :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hC3)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hd1 hd2)

omit [Finite N] in
theorem injOn_core_of_pgroup (hC3 : ¬ 3 ∣ Nat.card N₀.normalCore) {E : Subgroup N}
    (hE : IsPGroup 3 E) {x y : N} (hx : x ∈ E) (hy : y ∈ E) (h : coreMk N₀ x = coreMk N₀ y) :
    x = y := by
  have : coreMk N₀ (x⁻¹ * y) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
  have := inj_core_of_pgroup hC3 hE (E.mul_mem (E.inv_mem hx) hy) this
  rwa [inv_mul_eq_one] at this

theorem isElemAbelian_map {G H : Type*} [Group G] [Group H] (f : G →* H) {E : Subgroup G}
    (hE : IsElemAbelian 3 E) : IsElemAbelian 3 (E.map f) := CFSG.Open.IsElemAbelian.map hE _

omit [Finite N] in
theorem card_map_core (hC3 : ¬ 3 ∣ Nat.card N₀.normalCore) {E : Subgroup N}
    (hE : IsPGroup 3 E) : Nat.card (E.map (coreMk N₀)) = Nat.card E := by
  have hinj : Function.Injective ((coreMk N₀).subgroupMap E) := by
    refine (injective_iff_map_eq_one _).mpr fun x hx => ?_
    have hx1 : coreMk N₀ (x : N) = 1 := congrArg Subtype.val hx
    exact Subtype.ext (inj_core_of_pgroup hC3 hE x.2 hx1)
  exact (Nat.card_eq_of_bijective _ ⟨hinj, MonoidHom.subgroupMap_surjective _ _⟩).symm

omit [Finite N] in
theorem isElemAbelian_of_map (hC3 : ¬ 3 ∣ Nat.card N₀.normalCore) {E : Subgroup N}
    (hE : IsPGroup 3 E) (h : IsElemAbelian 3 (E.map (coreMk N₀))) : IsElemAbelian 3 E := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · have hc := h.1.is_comm.comm ⟨coreMk N₀ a, a, a.2, rfl⟩ ⟨coreMk N₀ b, b, b.2, rfl⟩
    have h1 : coreMk N₀ ((a : N) * b) = coreMk N₀ ((b : N) * a) := by
      rw [map_mul, map_mul]; exact congrArg Subtype.val hc
    exact injOn_core_of_pgroup hC3 hE (E.mul_mem a.2 b.2) (E.mul_mem b.2 a.2) h1
  · have h1 : coreMk N₀ (x ^ 3) = coreMk N₀ 1 := by
      rw [map_pow, map_one]; exact h.2 _ ⟨x, hx, rfl⟩
    exact injOn_core_of_pgroup hC3 hE (E.pow_mem hx 3) E.one_mem h1

omit [Finite N] in
theorem comm_map {E : Subgroup N} (h : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) :
    ∀ a ∈ E.map (coreMk N₀), ∀ b ∈ E.map (coreMk N₀), a * b = b * a := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  rw [← map_mul, ← map_mul, h a ha b hb]

theorem exists_lift_normalizer (hstr : GLBStronglyEmbedded 3 N₀) {R : Subgroup N}
    (hRN₀ : R ≤ N₀) (hR3 : IsPGroup 3 R) (hR3d : 3 ∣ Nat.card R)
    {g : N ⧸ N₀.normalCore} (hg : g ∈ Subgroup.normalizer ((R.map (coreMk N₀) : Subgroup _) : Set _)) :
    ∃ n ∈ N₀ ⊓ Subgroup.normalizer (R : Set N), coreMk N₀ n = g := by
  have hC3 := not_dvd_card_normalCore hstr
  have hstr' := stronglyEmbedded_coreImage hstr
  have hRM : R.map (coreMk N₀) ≤ coreImage N₀ := Subgroup.map_mono hRN₀
  have h3 : 3 ∣ Nat.card (R.map (coreMk N₀)) := by rw [card_map_core hC3 hR3]; exact hR3d
  have hgM : g ∈ coreImage N₀ := normalizer_le_of_stronglyEmbedded hstr' hRM h3 hg
  obtain ⟨n₀, rfl⟩ := coreMk_surjective g
  have hn₀ : n₀ ∈ N₀ := (mem_coreImage_iff N₀).mp hgM
  have hker : (R.map (coreMk N₀)).comap (coreMk N₀) = R ⊔ N₀.normalCore := by
    rw [Subgroup.comap_map_eq]; congr 1; exact QuotientGroup.ker_mk' _
  have hmem : ∀ y : N, y ∈ R ⊔ N₀.normalCore ↔ coreMk N₀ y ∈ R.map (coreMk N₀) := by
    intro y; rw [← hker]; rfl
  have hn : n₀ ∈ Subgroup.normalizer ((N₀.normalCore ⊔ R : Subgroup N) : Set N) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [sup_comm, hmem, hmem, map_mul, map_mul, map_inv]
    exact Subgroup.mem_normalizer_iff.mp hg _
  obtain ⟨c, hc, hcn⟩ := exists_mul_mem_normalizer_of_sup hR3 hC3 hn
  refine ⟨c * n₀, ⟨N₀.mul_mem (N₀.normalCore_le hc) hn₀, hcn⟩, ?_⟩
  have : coreMk N₀ c = 1 := (QuotientGroup.eq_one_iff c).mpr hc
  rw [map_mul, this, one_mul]

end CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
