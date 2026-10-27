module

public import CFSG.ClassicalInvolution.AschTight.Sec6Gen64C
public import CFSG.ClassicalInvolution.Asc77.WP1Proofs6
public import CFSG.ClassicalInvolution.AschTight.Sec6Gen64B

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K J R T : Subgroup G}
  {z j u v : G}

structure OddCompl (H U N₀ : Subgroup G) : Prop where
  le : N₀ ≤ H
  odd : Odd (Nat.card N₀)
  dec : ∀ h ∈ H, ∃ n ∈ N₀, ∃ u ∈ U, h = n * u
  mem_of_odd : ∀ x ∈ H, Odd (orderOf x) → x ∈ N₀

theorem exists_oddCompl {H U : Subgroup G} (hU : IsSylow2In U H) (hUc : IsCyclic ↥U) :
    ∃ N₀ : Subgroup G, OddCompl H U N₀ := by
  obtain ⟨N₀, h1, h2, h3, h4⟩ := exists_odd_complement hU hUc
  exact ⟨N₀, ⟨h1, h2, h3, h4⟩⟩

namespace OddCompl

variable {H U N₀ : Subgroup G} (hN : OddCompl H U N₀)
include hN

omit [Finite G] in
theorem odd_orderOf {n : G} (hn : n ∈ N₀) : Odd (orderOf n) :=
  hN.odd.of_dvd_nat (Subgroup.orderOf_dvd_natCard N₀ hn)

omit [Finite G] in
theorem conj_mem {g : G} (hg : ∀ h ∈ H, g * h * g⁻¹ ∈ H) {n : G} (hn : n ∈ N₀) :
    g * n * g⁻¹ ∈ N₀ := by
  refine hN.mem_of_odd _ (hg n (hN.le hn)) ?_
  have e : orderOf (g * n * g⁻¹) = orderOf n := by
    simpa [MulAut.conj_apply] using (MulAut.conj g).orderOf_eq n
  rw [e]
  exact hN.odd_orderOf hn

omit [Finite G] in
theorem le_normalizer {g : G} (hg : g ∈ Subgroup.normalizer (H : Set G)) :
    g ∈ Subgroup.normalizer (N₀ : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro n
  refine ⟨fun hn => hN.conj_mem (fun h hh => (Subgroup.mem_normalizer_iff.mp hg h).mp hh) hn,
    fun hn => ?_⟩
  have hg' : g⁻¹ ∈ Subgroup.normalizer (H : Set G) := (Subgroup.normalizer _).inv_mem hg
  have := hN.conj_mem (fun h hh => (Subgroup.mem_normalizer_iff.mp hg' h).mp hh) hn
  have e : g⁻¹ * (g * n * g⁻¹) * g⁻¹⁻¹ = n := by group
  rwa [e] at this

omit [Finite G] in
theorem H_le_normalizer : H ≤ Subgroup.normalizer (N₀ : Set G) := fun _ hh =>
  hN.le_normalizer (Subgroup.le_normalizer hh)

end OddCompl

namespace Cfg64

variable (c : Cfg64 Ω K J z j u v R T)
include c

omit [Finite G] in
theorem UV_comm : ∀ x ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers v,
    ∀ y ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers v, x * y = y * x := by
  have hc : Subgroup.zpowers u ⊔ Subgroup.zpowers v ≤
      Subgroup.centralizer ((Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) : Set G) := by
    refine sup_le (fun a ha => ?_) (fun b hb => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨a', ha', b', hb', rfl⟩ := exists_mul_of_mem_sup_of_commutes c.hUV hy
      have h1 : a' * a = a * a' := AscL62.cyclic_comm inferInstance ha' ha
      have h2 : b' * a = a * b' := (c.hUV a ha b' hb').symm
      calc a' * b' * a = a' * (b' * a) := by group
        _ = a' * (a * b') := by rw [h2]
        _ = (a' * a) * b' := by group
        _ = (a * a') * b' := by rw [h1]
        _ = a * (a' * b') := by group
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨a', ha', b', hb', rfl⟩ := exists_mul_of_mem_sup_of_commutes c.hUV hy
      have h1 : b' * b = b * b' := AscL62.cyclic_comm inferInstance hb' hb
      have h2 : a' * b = b * a' := c.hUV a' ha' b hb
      calc a' * b' * b = a' * (b' * b) := by group
        _ = a' * (b * b') := by rw [h1]
        _ = (a' * b) * b' := by group
        _ = (b * a') * b' := by rw [h2]
        _ = b * (a' * b') := by group
  intro x hx y hy
  exact Subgroup.mem_centralizer_iff.mp (hc hy) x hx

theorem U_inf_V : Subgroup.zpowers u ⊓ Subgroup.zpowers v = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  exact c.pair.eq_one_of_mem_of_mem (c.hUK hx.1) (c.hVJ hx.2)
    (AscL62.orderOf_eq_two_pow_of_isPGroup c.U_isPGroup hx.1)

theorem sq_eq_one_of_mem_UV {x : G} (hx : x ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers v)
    (hxx : x * x = 1) : x = 1 ∨ x = z ∨ x = j ∨ x = z * j := by
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_commutes c.hUV hx
  have hab : a * b = b * a := c.hUV a ha b hb
  have h1 : a * a = (b * b)⁻¹ := by
    have : (a * a) * (b * b) = 1 := by
      calc (a * a) * (b * b) = a * (a * b) * b := by group
        _ = a * (b * a) * b := by rw [hab]
        _ = (a * b) * (a * b) := by group
        _ = 1 := hxx
    exact eq_inv_of_mul_eq_one_left this
  have h2 : a * a ∈ Subgroup.zpowers u ⊓ Subgroup.zpowers v :=
    ⟨Subgroup.mul_mem _ ha ha, h1 ▸ Subgroup.inv_mem _ (Subgroup.mul_mem _ hb hb)⟩
  rw [c.U_inf_V, Subgroup.mem_bot] at h2
  have h3 : b * b = 1 := by
    rw [h2] at h1
    have := congrArg (fun w => w⁻¹) h1
    simpa using this.symm
  rcases c.hz.unique a (c.hUK ha) h2 with ha1 | ha1 <;>
    rcases c.hj.unique b (c.hVJ hb) h3 with hb1 | hb1
  · left; rw [ha1, hb1, mul_one]
  · right; right; left; rw [ha1, hb1, one_mul]
  · right; left; rw [ha1, hb1, mul_one]
  · right; right; right; rw [ha1, hb1]

theorem j_mem_UV : j ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers v :=
  Subgroup.mem_sup_right c.j_mem_V

theorem z_mem_UV : z ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers v :=
  Subgroup.mem_sup_left c.z_mem_U

omit [Finite G] in
theorem z_comm {k : G} (hk : k ∈ K) : k * z = z * k := (c.hz.commute_of_mem hk).symm

theorem conj_j_of_not_mem {r : G} (hr : r ∈ R) (hru : r ∉ Subgroup.zpowers u) :
    r * j * r⁻¹ = z * j := by
  have hrN := c.hRN hr
  have hmem : r * j * r⁻¹ ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers v :=
    (Subgroup.mem_normalizer_iff.mp hrN j).mp c.j_mem_UV
  have hsq : (r * j * r⁻¹) * (r * j * r⁻¹) = 1 := by
    calc (r * j * r⁻¹) * (r * j * r⁻¹) = r * (j * j) * r⁻¹ := by group
      _ = 1 := by rw [c.hj.sq]; group
  have hzj := c.z_ne_j
  have hrz : r * z * r⁻¹ = z := by
    rw [c.z_comm (c.hR.1 hr)]
    group
  rcases c.sq_eq_one_of_mem_UV hmem hsq with h | h | h | h
  · exfalso
    apply c.hj.ne_one
    have := congrArg (fun w => r⁻¹ * w * r) h
    simpa [mul_assoc] using this
  · exfalso
    apply hzj
    have h1 : r * j * r⁻¹ = r * z * r⁻¹ := by rw [h, hrz]
    have := congrArg (fun w => r⁻¹ * w * r) h1
    simpa [mul_assoc] using this.symm
  · exfalso
    apply hru
    rw [← c.R_inf_centralizer]
    refine ⟨hr, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    calc r * j = (r * j * r⁻¹) * r := by group
      _ = j * r := by rw [h]
  · exact h

end Cfg64

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen
