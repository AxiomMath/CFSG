module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG.Open (IsElemAbelian)

@[expose] def HasIndepPair (p : ℕ) (G : Type*) [Group G] : Prop :=
  ∃ y₁ y₂ : G, Commute y₁ y₂ ∧ y₁ ^ p = 1 ∧ y₂ ^ p = 1 ∧
    ∀ i j : ℤ, y₁ ^ i * y₂ ^ j = 1 → (p : ℤ) ∣ i ∧ (p : ℤ) ∣ j

theorem HasIndepPair.of_injective {p : ℕ} {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) (h : HasIndepPair p G) : HasIndepPair p H := by
  obtain ⟨y₁, y₂, hc, h1, h2, hi⟩ := h
  refine ⟨f y₁, f y₂, hc.map f, ?_, ?_, fun i j hij => ?_⟩
  · rw [← map_pow, h1, map_one]
  · rw [← map_pow, h2, map_one]
  · rw [← map_zpow, ← map_zpow, ← map_mul] at hij
    exact hi i j (hf (hij.trans (map_one f).symm))

theorem HasIndepPair.of_mulEquiv {p : ℕ} {G H : Type*} [Group G] [Group H] (ψ : G ≃* H)
    (h : HasIndepPair p G) : HasIndepPair p H :=
  h.of_injective ψ.toMonoidHom ψ.injective

theorem hasIndepPair_of_elemAbelian_sq {p : ℕ} (hp : p.Prime) {G : Type*} [Group G]
    {E : Subgroup G} (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 2) : HasIndepPair p G := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := hE.1
  haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hEc]; exact (pow_pos hp.pos 2).ne')
  have hdvd : p ∣ Nat.card E := by rw [hEc]; exact dvd_pow_self p two_ne_zero
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hcardu : Nat.card (Subgroup.zpowers u) = p := by rw [Nat.card_zpowers, hu]
  obtain ⟨v, hv⟩ : ∃ v : E, v ∉ Subgroup.zpowers u := by
    by_contra h
    push Not at h
    have htop : Subgroup.zpowers u = ⊤ := eq_top_iff.2 fun x _ => h x
    rw [htop, Subgroup.card_top, hEc] at hcardu
    have h1 : p ^ 2 = p ^ 1 := by rw [hcardu, pow_one]
    have := Nat.pow_right_injective hp.two_le h1
    omega
  have hv1 : v ≠ 1 := fun h => hv (h ▸ Subgroup.one_mem _)
  have hvp : v ^ p = 1 := Subtype.ext (hE.2 v v.2)
  have hup : u ^ p = 1 := Subtype.ext (hE.2 u u.2)
  have hvo : orderOf v = p := orderOf_eq_prime hvp hv1
  refine ⟨(u : G), (v : G), congrArg Subtype.val (mul_comm' u v), hE.2 u u.2, hE.2 v v.2,
    fun i j hij => ?_⟩
  have hij' : u ^ i * v ^ j = 1 := Subtype.ext (by simpa using hij)
  have hvj : v ^ j = (u ^ i)⁻¹ := eq_inv_of_mul_eq_one_right hij'
  have hpj : (p : ℤ) ∣ j := by
    by_contra hj
    have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
    obtain ⟨a, b, hab⟩ := (Irreducible.coprime_iff_not_dvd hpz.irreducible).2 hj
    have h1 : v = (v ^ j) ^ b := by
      have h2 : v ^ (a * (p : ℤ) + b * j) = v := by rw [hab, zpow_one]
      rw [zpow_add, mul_comm a, mul_comm b, zpow_mul, zpow_mul, zpow_natCast, hvp,
        _root_.one_zpow, one_mul] at h2
      exact h2.symm
    apply hv
    rw [h1, hvj]
    exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.zpow_mem _
      (Subgroup.mem_zpowers u) i)) b
  refine ⟨?_, hpj⟩
  obtain ⟨j₁, rfl⟩ := hpj
  have hvj1 : v ^ ((p : ℤ) * j₁) = 1 := by
    rw [zpow_mul, zpow_natCast, hvp, _root_.one_zpow]
  rw [hvj1, mul_one] at hij'
  have : (orderOf u : ℤ) ∣ i := orderOf_dvd_iff_zpow_eq_one.2 hij'
  rwa [hu] at this

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
