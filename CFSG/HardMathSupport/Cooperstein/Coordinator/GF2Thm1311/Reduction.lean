module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311.Dihedral
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFInputs
public import CFSG.RankThree.PartOne.S11d.OutAbstract
import CFSG.Quasithin.Background.A1aFStar

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311

open CFSG.Quasithin CFSG.Open CFSG.RankThree.PartOne.OutStructure
open CFSG.HardMathSupport.Cooperstein.Coordinator

@[expose] def BigInv {Y : Type} [Group Y] (α : MulAut Y) : Prop :=
  ∃ x : Y, ∃ p : ℕ, p.Prime ∧ (11 ≤ p ∨ p = 7) ∧ orderOf (α x * x⁻¹) = p

@[expose] def KleinBigInv (Y : Type) [Group Y] : Prop :=
  ∀ B : Subgroup (MulAut Y), (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) → (∀ a ∈ B, a * a = 1) →
    Nat.card B = 4 → B ⊓ Inn Y = ⊥ → ∃ α ∈ B, BigInv α

theorem BigInv.of_congr {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {b : MulAut Y}
    (h : BigInv (MulAut.congr e.symm b)) : BigInv b := by
  obtain ⟨x, p, hp, h11, hord⟩ := h
  refine ⟨e x, p, hp, h11, ?_⟩
  rw [← hord]
  have : e.symm (b (e x) * (e x)⁻¹) = (MulAut.congr e.symm b) x * x⁻¹ := by
    rw [map_mul, map_inv, MulAut.congr_apply]
    simp
  rw [← this]
  exact (orderOf_injective e.symm.toMonoidHom e.symm.injective _).symm

theorem BigInv.of_inv {Y : Type} [Group Y] [Finite Y] (c φ : MulAut Y) (y : Y) {p : ℕ} (hp : p.Prime)
    (hbig : 11 ≤ p ∨ p = 7) (hy : orderOf y = p) (hφ : φ y = y⁻¹) : BigInv (c * φ * c⁻¹) := by
  refine ⟨c y, p, hp, hbig, ?_⟩
  have h1 : (c * φ * c⁻¹) (c y) = (c y)⁻¹ := by
    simp only [MulAut.mul_apply]
    rw [MulAut.inv_apply, MulEquiv.symm_apply_apply, hφ, map_inv]
  rw [h1, ← mul_inv_rev, ← pow_two]
  have hx : orderOf (c y) = p := by
    rw [← hy]
    exact MulEquiv.orderOf_eq c y
  have hg : Nat.gcd p 2 = 1 :=
    (Nat.Prime.coprime_iff_not_dvd hp).mpr (fun h => by
      have := Nat.le_of_dvd (by norm_num) h
      rcases hbig with h' | h' <;> omega)
  rw [orderOf_inv, orderOf_pow, hx, hg, Nat.div_one]

theorem KleinBigInv.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : KleinBigInv X) : KleinBigInv Y := by
  intro B hcomm hsq hcard hinn
  set φ : MulAut Y ≃* MulAut X := MulAut.congr e.symm with hφ
  have hinj : Function.Injective φ.toMonoidHom := φ.injective
  obtain ⟨α, ⟨b, hb, rfl⟩, hbig⟩ := h (B.map φ.toMonoidHom)
    (by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨c, hc, rfl⟩
      rw [← map_mul, ← map_mul, hcomm a ha c hc])
    (by
      rintro _ ⟨a, ha, rfl⟩
      rw [← map_mul, hsq a ha, map_one])
    (by rw [Subgroup.card_map_of_injective hinj]; exact hcard)
    (by
      refine eq_bot_iff.mpr ?_
      rintro _ ⟨⟨b, hb, rfl⟩, ⟨u, hu⟩⟩
      have hbI : b ∈ Inn Y := by
        refine ⟨e u, ?_⟩
        apply φ.injective
        have hu' : MulAut.conj u = φ b := hu
        rw [← hu']
        ext x
        simp [hφ, MulAut.congr_apply, MulAut.conj_apply]
      have : b = 1 := by
        have hb1 : b ∈ B ⊓ Inn Y := ⟨hb, hbI⟩
        rw [hinn] at hb1
        simpa using hb1
      rw [this]
      simp)
  exact ⟨b, hb, BigInv.of_congr e hbig⟩

section Action

variable {G : Type} [Group G] (L : Subgroup G)

@[expose] noncomputable def actL : Subgroup.normalizer (L : Set G) →* MulAut (L ⧸ Subgroup.center L) :=
  (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom L).comp L.normalizerMonoidHom

theorem actL_mk (g : G) (hg : g ∈ Subgroup.normalizer (L : Set G)) (x : L) :
    actL L ⟨g, hg⟩ (QuotientGroup.mk x : L ⧸ Subgroup.center L) =
      QuotientGroup.mk (⟨g * x * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg x).mp x.2⟩ : L) := by
  refine (CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk _ x).trans ?_
  rfl

theorem exists_mem_of_actL_inner [Group.IsPerfect L] {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G))
    (h : actL L ⟨g, hg⟩ ∈ Inn (L ⧸ Subgroup.center L)) :
    ∃ j ∈ L, j⁻¹ * g ∈ Subgroup.centralizer (L : Set G) := by
  have hα : L.normalizerMonoidHom ⟨g, hg⟩ ∈ Inn L := by
    have h1 : (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom L)
        (L.normalizerMonoidHom ⟨g, hg⟩) ∈ Inn (L ⧸ Subgroup.center L) := h
    have h2 : CFSG.ComponentClassification.OuterAutomorphisms.centerQuotientOuterHom L
        (QuotientGroup.mk (L.normalizerMonoidHom ⟨g, hg⟩)) = 1 := by
      rw [CFSG.ComponentClassification.OuterAutomorphisms.centerQuotientOuterHom,
        QuotientGroup.map_mk]
      exact (QuotientGroup.eq_one_iff _).mpr h1
    have h3 := CFSG.ComponentClassification.OuterAutomorphisms.centerQuotient_outer_injective L
      (h2.trans (map_one _).symm)
    exact (QuotientGroup.eq_one_iff _).mp h3
  obtain ⟨j, hj⟩ := hα
  refine ⟨j, j.2, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have h4 := congrArg (fun f : MulAut L => ((f ⟨y, hy⟩ : L) : G)) hj
  rw [MulAut.conj_apply, Subgroup.normalizerMonoidHom_apply_apply_coe] at h4
  have h5 : (j : G) * y * (j : G)⁻¹ = g * y * g⁻¹ := by
    simpa using h4
  calc y * ((j : G)⁻¹ * g) = (j : G)⁻¹ * ((j : G) * y * (j : G)⁻¹) * g := by group
    _ = (j : G)⁻¹ * (g * y * g⁻¹) * g := by rw [h5]
    _ = (j : G)⁻¹ * g * y := by group

end Action

section Main

variable {V : Type} [CommGroup V] [Finite V]

theorem inf_ne_bot_of_kleinBigInv (hV : ∀ v : V, v ^ 2 = 1) {H L : Subgroup (MulAut V)}
    (hff : FFHyp H L) (hK : KleinBigInv (↥L ⧸ Subgroup.center ↥L))
    {A : Subgroup (MulAut V)} (hAH : A ≤ H) (hA : IsElemAbelian2 A) (hcard : Nat.card A = 4)
    (hineq : Nat.card V ≤ 4 * Nat.card {v : V | ∀ a ∈ A, a v = v}) : A ⊓ L ≠ ⊥ := by
  obtain ⟨hLeq, hqs, -, -⟩ := hff
  intro hAL
  have hLH : L ≤ H := by rw [hLeq]; exact quasithinGenFitting_le H
  have hHN : H ≤ Subgroup.normalizer (L : Set (MulAut V)) := by
    rw [hLeq]; exact le_normalizer_quasithinGenFitting H
  have hcent : H ⊓ Subgroup.centralizer (L : Set (MulAut V)) ≤ L := by
    rw [hLeq]; exact centralizer_quasithinGenFitting_le H
  have : Group.IsPerfect L := hqs.1
  let ρ : A →* MulAut (L ⧸ Subgroup.center L) :=
    (actL L).comp ((Subgroup.inclusion (hAH.trans hHN)))
  have hker : ∀ a : A, ρ a ∈ Inn (L ⧸ Subgroup.center L) → a = 1 := by
    intro a ha
    obtain ⟨j, hj, hjc⟩ := exists_mem_of_actL_inner L (hAH.trans hHN a.2) ha
    have hmem : (j⁻¹ * (a : MulAut V)) ∈ H ⊓ Subgroup.centralizer (L : Set (MulAut V)) :=
      ⟨H.mul_mem (H.inv_mem (hLH hj)) (hAH a.2), hjc⟩
    have haL : (a : MulAut V) ∈ L := by
      have := L.mul_mem hj (hcent hmem)
      simpa using this
    have : (a : MulAut V) ∈ A ⊓ L := ⟨a.2, haL⟩
    rw [hAL] at this
    exact Subtype.ext (by simpa using this)
  have hinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    exact hker a (by rw [ha]; exact Subgroup.one_mem _)
  obtain ⟨α, ⟨a, rfl⟩, hbig⟩ := hK ρ.range
    (by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hA.1 a a.2 b b.2))
    (by
      rintro _ ⟨a, rfl⟩
      rw [← map_mul]
      have : a * a = 1 := Subtype.ext (by simpa [pow_two] using hA.2 a a.2)
      rw [this, map_one])
    (by rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]; exact hcard)
    (by
      refine eq_bot_iff.mpr ?_
      rintro _ ⟨⟨a, rfl⟩, hin⟩
      have := hker a hin
      rw [this, map_one]
      exact Subgroup.one_mem _)
  obtain ⟨x, p, hp, h11, hord⟩ := hbig
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  have ha2 : (a : MulAut V) * a = 1 := by simpa [pow_two] using hA.2 a a.2
  have hai : (a : MulAut V)⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have haN : (a : MulAut V) ∈ Subgroup.normalizer (L : Set (MulAut V)) := hAH.trans hHN a.2
  have hw : (a : MulAut V) * g * (a : MulAut V)⁻¹ * (g : MulAut V)⁻¹ ∈ L :=
    L.mul_mem ((Subgroup.mem_normalizer_iff.mp haN g).mp g.2) (L.inv_mem g.2)
  have himg : (QuotientGroup.mk (⟨_, hw⟩ : L) : L ⧸ Subgroup.center L) =
      ρ a (QuotientGroup.mk g) * (QuotientGroup.mk g)⁻¹ := by
    show _ = actL L ⟨(a : MulAut V), _⟩ (QuotientGroup.mk g) * _
    rw [actL_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    rfl
  have hdvd : p ∣ orderOf ((a : MulAut V) * ((g : MulAut V) * a * (g : MulAut V)⁻¹)) := by
    rw [← hord, ← himg]
    refine (orderOf_map_dvd (QuotientGroup.mk' (Subgroup.center L)) (⟨_, hw⟩ : L)).trans ?_
    rw [← Subgroup.orderOf_coe]
    simp only [hai, mul_assoc]
    exact dvd_rfl
  exact false_of_prime_dvd_orderOf_conj_pair hV hineq a.2 ha2 g hp h11 hdvd

end Main

end CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311
