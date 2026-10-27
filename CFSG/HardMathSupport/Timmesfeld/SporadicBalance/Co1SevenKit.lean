module

public import CFSG.Assembly.Defs
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreBasics

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open scoped Pointwise

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Proving

variable {p : ℕ} {S : Type*} [Group S]

theorem gLAPPrimeCoreOf_eq_bot_of_closure [Finite S] (hp : p.Prime) {C : Subgroup S}
    (h : ∀ w ∈ C, (orderOf w).Prime → orderOf w ≠ p →
      ∃ c ∈ C, ∃ r ∈ C, w * c = c * r ∧ ∃ a ∈ C, ∃ b ∈ C,
        p ∣ orderOf (r * (a * r * a⁻¹) * (b * r * b⁻¹))) :
    GLAPPrimeCoreOf p C = ⊥ := by
  by_contra hL
  set R := GLAPPrimeCoreOf p C with hRdef
  have hRC : R ≤ C := GLAPPrimeCoreOf_le C
  have hcop : Nat.Coprime p (Nat.card R) := coprime_card_GLAPPrimeCoreOf hp C
  have hRne : Nat.card R ≠ 1 := fun h1 => hL (Subgroup.card_eq_one.1 h1)
  obtain ⟨q, hq, hqR⟩ := Nat.exists_prime_and_dvd hRne
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := R) q hqR
  set w : S := (x : S) with hw
  have hwo : orderOf w = q := by rw [hw, Subgroup.orderOf_coe, hx]
  have hwR : w ∈ R := x.2
  have hqp : q ≠ p := by
    rintro rfl
    exact (hp.coprime_iff_not_dvd.1 hcop) hqR
  obtain ⟨c, hc, r, hrC, hwc, a, ha, b, hb, hdvd⟩ :=
    h w (hRC hwR) (hwo ▸ hq) (hwo ▸ hqp)
  have hrR : r ∈ R := by
    have h1 : c⁻¹ * w * c⁻¹⁻¹ ∈ R := GLAPPrimeCoreOf_conj_mem c⁻¹ (C.inv_mem hc) w hwR
    have h2 : c⁻¹ * w * c⁻¹⁻¹ = r := by
      rw [inv_inv, mul_assoc, hwc, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [← h2]
    exact h1
  have h1 : a * r * a⁻¹ ∈ R := GLAPPrimeCoreOf_conj_mem a ha r hrR
  have h2 : b * r * b⁻¹ ∈ R := GLAPPrimeCoreOf_conj_mem b hb r hrR
  have hy : r * (a * r * a⁻¹) * (b * r * b⁻¹) ∈ R := R.mul_mem (R.mul_mem hrR h1) h2
  have h3 : orderOf (⟨_, hy⟩ : R) ∣ Nat.card R := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk] at h3
  exact (hp.coprime_iff_not_dvd.1 hcop) (hdvd.trans h3)

theorem centralizer_pow_eq_of_not_dvd {s : S} (hp : p.Prime) (hs : orderOf s = p) {m : ℕ}
    (hm : ¬ p ∣ m) :
    Subgroup.centralizer ({s ^ m} : Set S) = Subgroup.centralizer ({s} : Set S) := by
  obtain ⟨m', hm'⟩ := exists_pow_eq_self_of_coprime (n := m) (x := s)
    (by rw [hs]; exact ((Nat.Prime.coprime_iff_not_dvd hp).2 hm).symm)
  have hsm : s = (s ^ m) ^ m' := hm'.symm
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    simp only [Set.mem_singleton_iff, forall_eq] at hx ⊢
    have := Commute.pow_left (show Commute (s ^ m) x from hx) m'
    rw [← hsm] at this
    exact this.eq
  · intro x hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    simp only [Set.mem_singleton_iff, forall_eq] at hx ⊢
    exact (Commute.pow_left (show Commute s x from hx) m).eq

theorem conj_pow_of_conj {c x t : S} (h : c * x = t * c) (m : ℕ) : c * x ^ m * c⁻¹ = t ^ m := by
  have h1 : c * x * c⁻¹ = t := by rw [h]; group
  rw [← h1]
  exact (conj_pow).symm

theorem exists_conj_sylow [Finite S] [Fact p.Prime] {P0 P : Subgroup S}
    (h0 : Nat.card P0 = p ^ (Nat.card S).factorization p)
    (h1 : Nat.card P = p ^ (Nat.card S).factorization p) :
    ∃ g : S, ∀ x ∈ P0, g * x * g⁻¹ ∈ P := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq S (Sylow.ofCard P0 h0) (Sylow.ofCard P h1)
  refine ⟨g, fun x hx => ?_⟩
  have hmem : MulAut.conj g x ∈
      ((g • Sylow.ofCard P0 h0 : Sylow p S) : Subgroup S) :=
    Subgroup.smul_mem_pointwise_smul _ _ _ hx
  rw [hg, Sylow.coe_ofCard] at hmem
  simpa [MulAut.conj_apply] using hmem

theorem comm_of_conj_comm {g c x : S} (h : g * x * g⁻¹ * c = c * (g * x * g⁻¹)) :
    g⁻¹ * c * g * x = x * (g⁻¹ * c * g) := by
  calc g⁻¹ * c * g * x = g⁻¹ * (c * (g * x * g⁻¹)) * g := by group
    _ = g⁻¹ * (g * x * g⁻¹ * c) * g := by rw [h]
    _ = x * (g⁻¹ * c * g) := by group

theorem pow_eq_one_of_conj {g c : S} {n : ℕ} (h : (g⁻¹ * c * g) ^ n = 1) : c ^ n = 1 := by
  have e : c = g * (g⁻¹ * c * g) * g⁻¹ := by group
  rw [e, conj_pow, h]
  group

theorem isPGroup_centralizer_of_mulEquiv {K K' : Type*} [Group K] [Group K'] (e : K ≃* K')
    (n : ℕ)
    (h : ∀ P : Subgroup K', Nat.card P = n → IsPGroup p ↥(Subgroup.centralizer (P : Set K'))) :
    ∀ P : Subgroup K, Nat.card P = n → IsPGroup p ↥(Subgroup.centralizer (P : Set K)) := by
  intro P hP
  have hcard : Nat.card (P.map e.toMonoidHom) = n := by
    rw [Subgroup.card_map_of_injective e.injective, hP]
  have h' := h _ hcard
  intro c
  obtain ⟨k, hk⟩ := h' ⟨e (c : K), by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    have := Subgroup.mem_centralizer_iff.1 c.2 y hy
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass]
    rw [← map_mul, ← map_mul, this]⟩
  refine ⟨k, Subtype.ext ?_⟩
  have h2 := congrArg Subtype.val hk
  simp only [Subgroup.coe_pow, Subgroup.coe_one] at h2 ⊢
  apply e.injective
  rw [map_pow, map_one]
  exact h2

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
