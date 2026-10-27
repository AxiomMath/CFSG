module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsRank
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsInv
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ModelGenA
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.CGT.T75P.SylowSplit

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Cls

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA CFSG.Yardstones.Md0ec50421ce4

theorem exists_maximal_elemAbelian {G : Type*} [Group G] [Finite G] {p : ℕ} {K A₁ : Subgroup G}
    (hA₁ : IsElemAbelian p A₁) (hA₁K : A₁ ≤ K) :
    ∃ A : Subgroup G, A₁ ≤ A ∧ IsElemAbelian p A ∧ A ≤ K ∧
      ∀ A' : Subgroup G, A ≤ A' → IsElemAbelian p A' → A' ≤ K → A' ≤ A := by
  classical
  haveI : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  obtain ⟨A, hA, hmax⟩ := Set.exists_max_image {A : Subgroup G | A₁ ≤ A ∧ IsElemAbelian p A ∧ A ≤ K}
    (fun A => Nat.card A) (Set.toFinite _) ⟨A₁, le_rfl, hA₁, hA₁K⟩
  refine ⟨A, hA.1, hA.2.1, hA.2.2, fun A' hAA' hA' hA'K => ?_⟩
  exact (Subgroup.eq_of_le_of_card_ge hAA' (hmax A' ⟨hA.1.trans hAA', hA', hA'K⟩)).symm.le

section Card

variable {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}

theorem card_eq_of_inner_split (hB : IsElemAbelian p B)
    (hBC : Nat.card ↥(B ⊓ Subgroup.centralizer (S : Set Ω)) = p) {b : Ω} (hbB : b ∈ B)
    (hBb : B = B ⊓ (S ⊔ Subgroup.centralizer (S : Set Ω)) ⊔ Subgroup.zpowers b)
    (hbout : Subgroup.zpowers b ⊓ (S ⊔ Subgroup.centralizer (S : Set Ω)) = ⊥) {a : ℕ}
    (ha : a * Nat.card ↥(B ⊓ (S ⊔ Subgroup.centralizer (S : Set Ω)) ⊓
      Subgroup.centralizer (S : Set Ω)) = Nat.card ↥(B ⊓ (S ⊔ Subgroup.centralizer (S : Set Ω)))) :
    Nat.card B = p * a * Nat.card (Subgroup.zpowers b) := by
  set N := S ⊔ Subgroup.centralizer (S : Set Ω) with hN
  have hinf : B ⊓ N ⊓ Subgroup.centralizer (S : Set Ω) = B ⊓ Subgroup.centralizer (S : Set Ω) := by
    rw [inf_assoc, inf_eq_right.mpr (le_sup_right : Subgroup.centralizer (S : Set Ω) ≤ N)]
  rw [hinf, hBC] at ha
  have hcomm : ∀ x ∈ B ⊓ N, ∀ y ∈ Subgroup.zpowers b, x * y = y * x := by
    intro x hx y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact (Commute.zpow_right (hB.comm hx.1 hbB) n).eq
  have hdisj : B ⊓ N ⊓ Subgroup.zpowers b = ⊥ := by
    rw [eq_bot_iff, ← hbout]
    exact fun x hx => ⟨hx.2, hx.1.2⟩
  have hcard := CFSG.CGT.T75P.card_sup_of_commute hcomm hdisj
  rw [← hBb] at hcard
  rw [hcard, ← ha]
  ring

end Card

section Transfer

variable {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}

theorem eq_of_le_of_involution (hp : p.Prime) (hSn : S.Normal) (hcore : GLAPPrimeCore p ↥S = ⊥)
    (hZ : Subgroup.center ↥S = ⊥) (hB : IsElemAbelian p B)
    (hrank : p ^ GLATwoLocalRank p Ω ≤ Nat.card B) (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p)
    {H : Type} [Group H] [Finite H] (φ : H →* Ω) (hφS : φ.range = S)
    (hkerp : Nat.Coprime (Nat.card φ.ker) p) {A E : Subgroup H} (hAE : A ≤ E)
    (hE : IsElemAbelian p E) {b : Ω} (hbB : b ∈ B) (hbE : ∀ e ∈ E, b * φ e = φ e * b)
    (hbout : Subgroup.zpowers b ⊓ (S ⊔ Subgroup.centralizer (S : Set Ω)) = ⊥)
    (hBcard : Nat.card B = p * Nat.card A * Nat.card (Subgroup.zpowers b))
    {z : H} (hz2 : z ^ 2 = 1) (hz1 : φ z ≠ 1) (hzE : ∀ e ∈ E, e * z = z * e)
    (hbz : b * φ z = φ z * b) : E = A := by
  have hinj : ∀ x ∈ E, φ x = 1 → x = 1 := by
    intro x hx hφx
    have h1 : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one (hE.2 x hx)
    have h2 : orderOf x ∣ Nat.card φ.ker := by
      have := orderOf_dvd_natCard (⟨x, MonoidHom.mem_ker.mpr hφx⟩ : φ.ker)
      rwa [Subgroup.orderOf_mk] at this
    have h3 : orderOf x ∣ 1 := by
      have := Nat.dvd_gcd h2 h1
      rwa [hkerp.gcd_eq_one] at this
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
  have hres : Function.Injective (φ.domRestrict E) :=
    (injective_iff_map_eq_one _).mpr fun x hx => Subtype.ext (hinj x x.2 hx)
  have hcardE : Nat.card ↥(E.map φ) = Nat.card E := by
    rw [← MonoidHom.domRestrict_range]
    exact (Nat.card_congr (MonoidHom.ofInjective hres).toEquiv).symm
  have hEC : E.map φ ⊓ centModSubgroup p S = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨⟨e, -, rfl⟩, hy⟩
    have hyS : φ e ∈ S := hφS ▸ ⟨e, rfl⟩
    have hc : (⟨φ e, hyS⟩ : ↥S) ∈ Subgroup.center ↥S := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (ModelGen.comm_of_mem_centMod hSn hcore hy g.2).symm
    rw [hZ, Subgroup.mem_bot] at hc
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hc)
  have hle := ModelGen.card_mul_le_of_involution hp hSn hcore hB hrank hBC φ hφS hE hEC hbB hbE
    hbout hz2 hz1 hzE hbz
  rw [hBcard, hcardE] at hle
  have hpos : 0 < p * Nat.card (Subgroup.zpowers b) :=
    Nat.mul_pos hp.pos Nat.card_pos
  have hEA : Nat.card E ≤ Nat.card A := by
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    calc Nat.card E * (p * Nat.card (Subgroup.zpowers b))
        = p * Nat.card E * Nat.card (Subgroup.zpowers b) := by ring
      _ ≤ p * Nat.card A * Nat.card (Subgroup.zpowers b) := hle
      _ = Nat.card A * (p * Nat.card (Subgroup.zpowers b)) := by ring
  exact (Subgroup.eq_of_le_of_card_ge hAE hEA).symm

end Transfer

section Scalar

open CFSG.LocalAnalysis.GLTheoremA.H81Orth.Wt

variable {K : Type*} [Field K] {A : Type*} [CommGroup A] {p : ℕ}
variable {V : Type*} [AddCommGroup V] [Module K V]
variable (ρ : Representation K A V) [Finite A]
variable (hp : p.Prime) (hA : ∀ a : A, a ^ p = 1) (hpK : (p : K) ≠ 0)

include hp hA hpK in
theorem invol_ne_smul (h2 : (2 : K) ≠ 0) {I : Finset (Hyperplane A p)} {H H' : Hyperplane A p}
    (hH : H ∈ I) (hH' : H' ∉ I) (hW : weightSpace ρ H.1 ≠ ⊥) (hW' : weightSpace ρ H'.1 ≠ ⊥)
    (c : K) : ¬ ∀ v, invol ρ hp hA hpK I v = c • v := by
  intro hc
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  obtain ⟨v', hv', hv'0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW'
  have e1 : (c + 1) • v = 0 := by
    have h := hc v
    rw [invol_apply_of_mem ρ hp hA hpK hH hv] at h
    rw [add_smul, one_smul, ← h, neg_add_cancel]
  have e2 : (c - 1) • v' = 0 := by
    have hi : ∀ H₀ ∈ I, (some H' : Option (Hyperplane A p)) ≠ some H₀ := by
      intro H₀ hH₀ h
      exact hH' (by rw [Option.some.inj h]; exact hH₀)
    have hv'f : v' ∈ weightFamily (p := p) ρ (some H') := by rw [weightFamily_some]; exact hv'
    have h := hc v'
    rw [invol_apply_of_not_mem ρ hp hA hpK hi hv'f] at h
    rw [sub_smul, one_smul, ← h, sub_self]
  have hc1 : c + 1 = 0 := (smul_eq_zero.mp e1).resolve_right hv0
  have hc2 : c - 1 = 0 := (smul_eq_zero.mp e2).resolve_right hv'0
  exact h2 (by linear_combination hc1 - hc2)

end Scalar

end CFSG.LocalAnalysis.GLTheoremA.S267.Cls
