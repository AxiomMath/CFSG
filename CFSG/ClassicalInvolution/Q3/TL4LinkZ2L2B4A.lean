module

public import CFSG.ClassicalInvolution.Q3.TL3Induct
public import CFSG.ClassicalInvolution.Asc77.AscP1Transfer
public import CFSG.ClassicalInvolution.Asc77.AscE184Quot
public import CFSG.RankThree.PartTwo.Sec8.TransferExtremal

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.LinkZ2B

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.RankThree.PartTwo.Sec8

variable {Y : Type} [Group Y] [Finite Y]

theorem hom_eq_one_of_sylow_tight {R R₀ : Subgroup Y} (hgen : TightSelfGen R)
    (hR₀ : IsSylow2In R₀ (tightCore R)) {A : Type*} [CommGroup A] (f : Y →* A)
    (hf : ∀ x ∈ R₀, f x = 1) : f = 1 := by
  have hK : tightCore R ≤ f.ker := by
    rw [tightCore, Subgroup.closure_le]
    rintro x ⟨hxR, hx2⟩
    have hxK : x ∈ tightCore R := Subgroup.subset_closure ⟨hxR, hx2⟩
    obtain ⟨V, hV, hxV⟩ := IsSylow2In.exists_ge hx2 (Subgroup.zpowers_le.mpr hxK)
    obtain ⟨c, -, hc⟩ := exists_conjSub_eq_of_isSylow2In hR₀ hV
    have hxV' : x ∈ conjSub c R₀ := hc ▸ hxV (Subgroup.mem_zpowers x)
    rw [mem_conjSub_iff] at hxV'
    have h1 := hf _ hxV'
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    simpa [map_mul, map_inv, mul_comm] using h1
  have hconj : ∀ g : Y, conjSub g (tightCore R) ≤ f.ker := by
    intro g x hx
    rw [mem_conjSub_iff] at hx
    have h1 := MonoidHom.mem_ker.mp (hK hx)
    rw [MonoidHom.mem_ker]
    simpa [map_mul, map_inv, mul_comm] using h1
  have hle : (⨆ g : Y, conjSub g (tightCore R)) ≤ f.ker := iSup_le hconj
  rw [hgen] at hle
  ext g
  simpa using hle (Subgroup.mem_top g)

theorem false_of_transfer_of_hom {R₀ : Subgroup Y}
    (hhom : ∀ (A : Type) [CommGroup A] (f : Y →* A), (∀ x ∈ R₀, f x = 1) → f = 1)
    (P : Sylow 2 Y) {N : Subgroup Y}
    (habel : ∀ y ∈ (P : Subgroup Y), ∀ z ∈ (P : Subgroup Y), y * z * y⁻¹ * z⁻¹ ∈ N)
    {x : Y} (hx : x ∈ (P : Subgroup Y)) (hxN : x ∉ N) (hxp : x ^ 2 = 1)
    (hfus : ∀ g : Y,
      (∀ y ∈ (P : Subgroup Y) ⊓ Subgroup.centralizer {x}, g⁻¹ * y * g ∈ (P : Subgroup Y)) →
        x⁻¹ * (g⁻¹ * x * g) ∈ N)
    (hweak : ∀ y ∈ R₀, y ≠ 1 → ∀ g : Y, g⁻¹ * y * g ∈ (P : Subgroup Y) → g⁻¹ * y * g ∈ N) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U : Subgroup (P : Subgroup Y) := N.subgroupOf P with hU
  have hUn : U.Normal := ⟨fun u hu y => by
    rw [hU, Subgroup.mem_subgroupOf] at hu ⊢
    have h := N.mul_mem (habel y y.2 u u.2) hu
    rwa [inv_mul_cancel_right] at h⟩
  have hcomm : ∀ a b : (P : Subgroup Y) ⧸ U, a * b = b * a := by
    intro a b
    induction a using QuotientGroup.induction_on with
    | H y =>
    induction b using QuotientGroup.induction_on with
    | H z =>
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    refine Subgroup.mem_subgroupOf.mpr ?_
    have := habel (z : Y)⁻¹ (Subgroup.inv_mem _ z.2) (y : Y)⁻¹ (Subgroup.inv_mem _ y.2)
    simpa [mul_assoc] using this
  let : CommGroup ((P : Subgroup Y) ⧸ U) :=
    { QuotientGroup.Quotient.group U with mul_comm := hcomm }
  let ϕ : (P : Subgroup Y) →* (P : Subgroup Y) ⧸ U := QuotientGroup.mk' U
  have hT : ϕ.transfer x = ϕ ⟨x, hx⟩ ^ (P : Subgroup Y).index := by
    refine transfer_eq_pow_index_of_extremal P ϕ hx hxp fun t hD ht => ?_
    change (QuotientGroup.mk' U _ : _) = QuotientGroup.mk' U _
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, eq_comm, QuotientGroup.eq]
    exact Subgroup.mem_subgroupOf.mpr (by simpa using hfus t hD)
  have hne : ϕ ⟨x, hx⟩ ≠ 1 := fun h =>
    hxN (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h))
  have hpow : ϕ ⟨x, hx⟩ ^ 2 = 1 := by
    rw [← map_pow]
    have : (⟨x, hx⟩ : (P : Subgroup Y)) ^ 2 = 1 := Subtype.ext (by simp [hxp])
    rw [this, map_one]
  have hVR : ∀ y ∈ R₀, ϕ.transfer y = 1 := by
    intro y hy
    refine transfer_apply_eq_one ϕ y fun g n hg => ?_
    by_cases hyn : y ^ n = 1
    · have : (⟨g⁻¹ * y ^ n * g, hg⟩ : ↥(P : Subgroup Y)) = 1 := Subtype.ext (by simp [hyn])
      rw [this, map_one]
    · exact (QuotientGroup.eq_one_iff _).mpr
        (Subgroup.mem_subgroupOf.mpr (hweak (y ^ n) (R₀.pow_mem hy n) hyn g hg))
  have h1 : ϕ.transfer x = 1 := by rw [hhom _ ϕ.transfer hVR]; rfl
  rw [hT] at h1
  have hdvd := orderOf_dvd_of_pow_eq_one h1
  rw [orderOf_eq_prime hpow hne] at hdvd
  exact P.not_dvd_index hdvd

theorem false_of_transfer_tight {R R₀ : Subgroup Y} (hgen : TightSelfGen R)
    (hR₀ : IsSylow2In R₀ (tightCore R)) (P : Sylow 2 Y) {N : Subgroup Y}
    (habel : ∀ y ∈ (P : Subgroup Y), ∀ z ∈ (P : Subgroup Y), y * z * y⁻¹ * z⁻¹ ∈ N)
    {x : Y} (hx : x ∈ (P : Subgroup Y)) (hxN : x ∉ N) (hxp : x ^ 2 = 1)
    (hfus : ∀ g : Y,
      (∀ y ∈ (P : Subgroup Y) ⊓ Subgroup.centralizer {x}, g⁻¹ * y * g ∈ (P : Subgroup Y)) →
        x⁻¹ * (g⁻¹ * x * g) ∈ N)
    (hweak : ∀ y ∈ R₀, y ≠ 1 → ∀ g : Y, g⁻¹ * y * g ∈ (P : Subgroup Y) → g⁻¹ * y * g ∈ N) :
    False :=
  false_of_transfer_of_hom (fun _ _ f hf => hom_eq_one_of_sylow_tight hgen hR₀ f hf) P habel hx
    hxN hxp hfus hweak

end CFSG.ClassicalInvolution.Q3.TL4.LinkZ2B
