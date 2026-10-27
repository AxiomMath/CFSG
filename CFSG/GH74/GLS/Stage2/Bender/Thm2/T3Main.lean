module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.T3Key
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.T3Lift
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.T3Comp
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915T5

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.GH74.GLS.Stage2.Bender.Thm1

namespace T3

theorem false_of_tail3_hyps {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S M : Subgroup G}
    {p : ℕ} (hC : Ctx9 G z k S M p)
    (hk : k = Kind.g2 ∨ k = Kind.psp4 ∨ ∃ ε : Bool, k = Kind.l4 ε)
    {J : Subgroup G} (hzJ : z ∈ J)
    (hnoc : ∀ c ∈ J, (∀ g ∈ J, c * g = g * c) → c * c = 1 → c = 1) {n : ℕ} (hn : 2 ≤ n)
    (hLie : LieModel (↥J ⧸ center ↥J) .PSL 3 p n) (hel : IsElementaryAbelian p ↥(Op p M))
    (hcard : Nat.card ↥(Op p M) = p ^ (2 * n)) (hPz : Op p M ⊓ Cen z = ⊥) : False := by
  have hp := hC.prime
  have hp2 : p ≠ 2 := hC.odd
  have hz := hC.orderOf_z
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  obtain ⟨ℓ, hℓ, hℓdvd, hprim⟩ :=
    CFSG.SL2MinimalFaithful.exists_primitive_prime_dvd_pow_sub_one hp3 (by omega : 3 ≤ 2 * n)
  have hℓq : ℓ ∣ (p ^ n) ^ 2 - 1 := by
    have : (p ^ n) ^ 2 = p ^ (2 * n) := by rw [← pow_mul, mul_comm]
    rw [this]
    exact hℓdvd
  have hℓp : ℓ ≠ p := by
    intro h
    subst h
    have h1 : ℓ ∣ ℓ ^ (2 * n) := dvd_pow_self ℓ (by omega)
    have h2 : 1 ≤ ℓ ^ (2 * n) := Nat.one_le_pow _ _ hℓ.pos
    have h3 := Nat.dvd_sub h1 hℓdvd
    rw [Nat.sub_sub_self h2] at h3
    exact hℓ.one_lt.ne' (Nat.dvd_one.mp h3)
  have hℓ2 : ℓ ≠ 2 := by
    intro h
    subst h
    apply hprim 1 (by norm_num) (by omega)
    have hodd : Odd p := hp.odd_of_ne_two hp2
    obtain ⟨m, hm⟩ := hodd
    rw [pow_one, hm]
    exact ⟨m, by omega⟩
  have hnorm : ∀ e ∈ Cen z, ∀ x ∈ Op p M, e * x * e⁻¹ ∈ Op p M := fun e he x hx =>
    (mem_normalizer_iff.mp (le_normalizer_Op' p M (hC.cen_le he)) x).mp hx
  have hfaith : ∀ e ∈ Cen z, (∀ x ∈ Op p M, e * x * e⁻¹ = x) → e = 1 := by
    intro e he hcent
    have h1 : e ∈ Op p M := L915.Ctx9.cent_Op_le hC (hC.cen_le he) hcent
    have h3 : e ∈ Op p M ⊓ Cen z := ⟨h1, he⟩
    rw [hPz, Subgroup.mem_bot] at h3
    exact h3
  have hρ := conjAction_injective (Op p M) (Cen z) hnorm hfaith
  have hPexp : ∀ v : ↥(Op p M), v ^ p = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p p ↥(Op p M))
  let : CommGroup ↥(Op p M) :=
    { (inferInstance : Group ↥(Op p M)) with
      mul_comm := fun a b => (inferInstance : Std.Commutative (α := ↥(Op p M)) (· * ·)).comm a b }
  have hcyc : ∀ y : ↥(Cen z), orderOf y = ℓ →
      IsCyclic ↥(Subgroup.centralizer ({y} : Set ↥(Cen z))) := fun y hy =>
    isCyclic_centralizer_of_primitive hp hℓ hℓp hprim hcard hPexp (conjAction (Op p M) (Cen z) hnorm)
      hρ hy
  obtain ⟨r₁, r₂, L₁, L₂, ho1, ho2, hgt, hprod, hs1, hs2⟩ := exists_two_comps hC.ctx.data hk
  obtain ⟨x, hx, hxLC⟩ := exists_elt_order_in_LC (perfInner_of_data hC.ctx.data hk) hzJ hz hnoc hp hp2 hn hLie hℓ hℓq
  have hq1 : IsQuasisimple ↥L₁ :=
    CFSG.GH74.Generic.S1.isQuasisimple_of_sl2 (by omega) hs1
  have hnonsolv₁ : ¬ Group.IsSolvable ↥L₁ := by
    have hperf : Group.IsPerfect ↥L₁ := hq1.1
    have : Nontrivial ↥L₁ := CFSG.LocalCores.isQuasisimple_nontrivial hq1
    intro hs
    exact Group.IsPerfect.not_isSolvable ↥L₁ hs
  have hnonab₂ : ∃ a ∈ L₂, ∃ b ∈ L₂, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := noncomm_of_hasSL2Model' hs2
    exact ⟨a, a.2, b, b.2, fun h => hab (Subtype.ext h)⟩
  have hxL : (x : CentralizerBar z) ∈ L₁ ⊔ L₂ := by
    rw [hprod.1]
    exact ⟨x, (Subgroup.mem_subgroupOf).mpr hxLC, rfl⟩
  exact false_of_commuting_components (pPrimeCore 2 ↥(Cen z)) hℓ hℓ2 hcyc L₁ L₂ hprod.2.1 hprod.2.2
    hnonsolv₁ hnonab₂ x hx hxL

end T3

theorem prop9_5Tail3_proved : Prop9_5Tail3 := by
  intro G _ _ z k S M p hC hk J n hJ hzJ hnoc hn hLie hPJ hel hcard hPz htr
  exact (T3.false_of_tail3_hyps hC hk hzJ hnoc hn hLie hel hcard hPz).elim

theorem lemma9_15_of_tail3_proved (h43E : Prop4_3E) (h34 : Leaf_Prop34) (h911 : Prop9_11Core) :
    Lemma9_15 :=
  lemma9_15_of_tail3 h43E h34 prop9_5Tail3_proved h911

end CFSG.GH74.GLS.Stage2.Bender.Thm2
