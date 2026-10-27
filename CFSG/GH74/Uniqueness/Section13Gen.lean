module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GH74.Uniqueness.Statements
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

section BarHom

variable {X : Type*} [Group X] (F : Subgroup X)

theorem A6.map_center_mulAut (σ : MulAut ↥F) : map (σ : ↥F →* ↥F) (center ↥F) = center ↥F :=
  Subgroup.characteristic_iff_map_eq.mp inferInstance σ

@[expose] noncomputable def A6.barHom :
    ↥(normalizer (F : Set X)) →* MulAut (↥F ⧸ center ↥F) where
  toFun g := QuotientGroup.congr (center ↥F) (center ↥F) (F.normalizerMonoidHom g)
    (A6.map_center_mulAut F _)
  map_one' := by
    refine MulEquiv.ext fun x => ?_
    induction x using QuotientGroup.induction_on with
    | H x => rw [QuotientGroup.congr_mk, map_one]; rfl
  map_mul' g h := by
    refine MulEquiv.ext fun x => ?_
    induction x using QuotientGroup.induction_on with
    | H x => rw [MulAut.mul_apply, QuotientGroup.congr_mk, QuotientGroup.congr_mk,
        QuotientGroup.congr_mk, map_mul, MulAut.mul_apply]

theorem A6.barHom_mk (g : ↥(normalizer (F : Set X))) (x : ↥F) :
    A6.barHom F g (QuotientGroup.mk' (center ↥F) x) =
      QuotientGroup.mk' (center ↥F) (F.normalizerMonoidHom g x) :=
  QuotientGroup.congr_mk _ _ _ (A6.map_center_mulAut F _) _

theorem A6.barHom_mk' (g : ↥(normalizer (F : Set X))) {x y : X} (hx : x ∈ F) (hy : y ∈ F)
    (hxy : (g : X) * x * (g : X)⁻¹ = y) :
    A6.barHom F g (QuotientGroup.mk' (center ↥F) ⟨x, hx⟩) =
      QuotientGroup.mk' (center ↥F) ⟨y, hy⟩ := by
  rw [A6.barHom_mk]
  congr 1
  apply Subtype.ext
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
  exact hxy

theorem A6.barHom_of_mem (g : ↥(normalizer (F : Set X))) (hg : (g : X) ∈ F) :
    A6.barHom F g = MulAut.conj (QuotientGroup.mk' (center ↥F) ⟨g, hg⟩) := by
  refine MulEquiv.ext fun x => ?_
  induction x using QuotientGroup.induction_on with
  | H x =>
    rw [MulAut.conj_apply]
    change A6.barHom F g (QuotientGroup.mk' (center ↥F) x) = QuotientGroup.mk' _ ⟨g, hg⟩ *
      QuotientGroup.mk' _ x * (QuotientGroup.mk' _ ⟨g, hg⟩)⁻¹
    rw [A6.barHom_mk, ← map_inv, ← map_mul, ← map_mul]
    exact congrArg (QuotientGroup.mk' (center ↥F))
      (Subtype.ext (Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _))

end BarHom

section Odd

theorem A6.eq_of_inv_mul_mem_two {G : Type*} [Group G] {N : Subgroup G} (hN : Odd (Nat.card N))
    (hNc : N ≤ center G) {x y : G} {k l : ℕ} (hx : x ^ 2 ^ k = 1) (hy : y ^ 2 ^ l = 1)
    (hxy : x⁻¹ * y ∈ N) : x = y := by
  set m := x⁻¹ * y with hm
  have hcomm : Commute x m := mem_center_iff.mp (hNc hxy) x
  have hy' : y = x * m := by rw [hm, mul_inv_cancel_left]
  have h1 : m ^ 2 ^ (k + l) = 1 := by
    have h2 : y ^ 2 ^ (k + l) = 1 := by rw [pow_add, pow_mul', hy, one_pow]
    rw [hy', hcomm.mul_pow, pow_add, pow_mul, hx, one_pow, one_mul] at h2
    rwa [pow_add]
  have hd1 : orderOf m ∣ 2 ^ (k + l) := orderOf_dvd_of_pow_eq_one h1
  have hd2 : orderOf m ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hxy
  have hcop : Nat.Coprime (2 ^ (k + l)) (Nat.card N) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hN)
  have : orderOf m = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hd1 hcop) hd2
  rw [orderOf_eq_one_iff] at this
  rw [hy', this, mul_one]

theorem A6.exists_sylow_map_eq {G : Type*} [Group G] [Finite G] (N : Subgroup G) [N.Normal]
    (P : Sylow 2 (G ⧸ N)) :
    ∃ Q : Sylow 2 G, (Q : Subgroup G).map (QuotientGroup.mk' N) = P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := Sylow.mapSurjective_surjective (QuotientGroup.mk'_surjective N) 2 P
  refine ⟨Q, ?_⟩
  rw [← hQ, Sylow.coe_mapSurjective]

theorem A6.mem_of_two_of_mk_mem {G : Type*} [Group G] {N : Subgroup G} [N.Normal]
    (hN : Odd (Nat.card N)) (hNc : N ≤ center G) {P : Subgroup G} (hP : IsPGroup 2 P) {x : G}
    {k : ℕ} (hx : x ^ 2 ^ k = 1) (hxP : QuotientGroup.mk' N x ∈ P.map (QuotientGroup.mk' N)) :
    x ∈ P := by
  obtain ⟨s, hs, hsx⟩ := hxP
  obtain ⟨l, hl⟩ := hP ⟨s, hs⟩
  have hl' : s ^ 2 ^ l = 1 := by
    have := congrArg Subtype.val hl
    simpa using this
  have hsx' : s⁻¹ * x ∈ N := QuotientGroup.eq.mp hsx
  rw [← A6.eq_of_inv_mul_mem_two hN hNc hl' hx hsx']
  exact hs

theorem A6.mem_of_mem_normalizer_sylow {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) {x : G} (hx : x ∈ normalizer ((P : Subgroup G) : Set G)) {k : ℕ}
    (hxk : x ^ p ^ k = 1) : x ∈ (P : Subgroup G) := by
  have hz : IsPGroup p (zpowers x) := by
    have hd : orderOf x ∣ p ^ k := orderOf_dvd_of_pow_eq_one hxk
    obtain ⟨j, -, hj'⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hd
    refine IsPGroup.of_card (n := j) ?_
    rw [Nat.card_zpowers, hj']
  have hle : zpowers x ≤ normalizer ((P : Subgroup G) : Set G) :=
    (zpowers_le).mpr hx
  have hsup : IsPGroup p ↥(zpowers x ⊔ (P : Subgroup G)) :=
    IsPGroup.to_sup_of_normal_right' hz P.isPGroup' hle
  have heq : zpowers x ⊔ (P : Subgroup G) = P := P.3 hsup le_sup_right
  rw [← heq]
  exact mem_sup_left (mem_zpowers x)

end Odd

section Fix

variable {X : Type*} [Group X] (F : Subgroup X)

theorem A6.conj_eq_of_barHom_fix (hodd : Odd (Nat.card (center ↥F)))
    (g : ↥(normalizer (F : Set X))) {z : X} (hz : z ∈ F) (hzz : z * z = 1)
    (hfix : A6.barHom F g (QuotientGroup.mk' (center ↥F) ⟨z, hz⟩) =
      QuotientGroup.mk' (center ↥F) ⟨z, hz⟩) : (g : X) * z * (g : X)⁻¹ = z := by
  set y : ↥F := F.normalizerMonoidHom g ⟨z, hz⟩ with hy
  have hyv : (y : X) = (g : X) * z * (g : X)⁻¹ := Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _
  rw [A6.barHom_mk] at hfix
  have h1 : y⁻¹ * ⟨z, hz⟩ ∈ center ↥F := QuotientGroup.eq.mp hfix
  have hyy : y ^ 2 ^ 1 = 1 := by
    apply Subtype.ext
    rw [pow_one, sq, Subgroup.coe_mul, hyv, OneMemClass.coe_one]
    calc (g : X) * z * (g : X)⁻¹ * ((g : X) * z * (g : X)⁻¹) = (g : X) * (z * z) * (g : X)⁻¹ := by
          group
      _ = 1 := by rw [hzz]; group
  have hzz' : (⟨z, hz⟩ : ↥F) ^ 2 ^ 1 = 1 := by
    apply Subtype.ext
    rw [pow_one, sq, Subgroup.coe_mul, OneMemClass.coe_one]
    exact hzz
  have h2 := A6.eq_of_inv_mul_mem_two hodd le_rfl hyy hzz' h1
  rw [← hyv, h2]

theorem A6.mem_centralizer_of_barHom_eq_one {Z : Set X} (hZ : ∀ z ∈ Z, z * z = 1)
    (hF : zHull Z F = F) (hodd : Odd (Nat.card (center ↥F))) (g : ↥(normalizer (F : Set X)))
    (hg : ∀ z ∈ Z, ∀ hzF : z ∈ F, A6.barHom F g (QuotientGroup.mk' (center ↥F) ⟨z, hzF⟩) =
      QuotientGroup.mk' (center ↥F) ⟨z, hzF⟩) : (g : X) ∈ centralizer (F : Set X) := by
  have hle : F ≤ centralizer ({(g : X)} : Set X) := by
    suffices h : zHull Z F ≤ centralizer ({(g : X)} : Set X) by rwa [hF] at h
    refine (closure_le _).mpr fun z hz => ?_
    have hzF : z ∈ F := hz.2
    have h1 := A6.conj_eq_of_barHom_fix F hodd g hzF (hZ z hz.1) (hg z hz.1 hzF)
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    calc z * (g : X) = ((g : X) * z * (g : X)⁻¹) * g := by rw [h1]
      _ = g * z := by group
  rw [mem_centralizer_iff]
  intro x hx
  exact (mem_centralizer_singleton_iff.mp (hle hx))

end Fix

end CFSG.GH74.Uniqueness
