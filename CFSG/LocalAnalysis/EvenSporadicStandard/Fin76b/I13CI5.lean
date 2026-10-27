module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.I13CI4
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.I13CI3
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.I13Cl1
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.I13Pi

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

set_option maxRecDepth 100000 in
theorem a5_pow8 : ∀ s : Equiv.Perm (Fin 5), Equiv.Perm.sign s = 1 → s ^ 8 = 1 → s * s = 1 := by
  decide

theorem a5_two_element {s : Equiv.Perm (Fin 5)} (hs : s ∈ alternatingGroup (Fin 5)) {k : ℕ}
    (hk : s ^ (2 ^ k) = 1) : s * s = 1 := by
  rw [Equiv.Perm.mem_alternatingGroup] at hs
  have h1 : orderOf s ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf s ∣ 120 := by
    have := orderOf_dvd_card (x := s)
    simpa [Fintype.card_perm, Nat.factorial] using this
  obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  have hj3 : j ≤ 3 := by
    by_contra h
    have h16 : 2 ^ 4 ∣ 2 ^ j := pow_dvd_pow 2 (by omega)
    have := h16.trans (hj' ▸ h2)
    norm_num at this
  have h8 : s ^ 8 = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hj']
    exact (pow_dvd_pow 2 hj3).trans (by norm_num)
  exact a5_pow8 s hs h8

namespace I13Ctx

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T₀ E : Subgroup G}
  {Q : Sylow 2 G} {x β : G} {B S : Subgroup G} {α : G}
  (c : I13Ctx L z t T₀ E Q x β B S α) {π : MulAut ↥E →* Equiv.Perm (Fin 5)}

include c

theorem card_Cprime_le {R : Subgroup G} (hRN : R ≤ c.N1) (hKR : R ⊓ c.KR ≤ c.Zs) {x : G}
    (hx : x ∈ c.N1) :
    Nat.card ↥(c.Cprime hRN x) ≤ 4 * Nat.card ↥(c.Rhat R ⊓ centralizer
      ({c.rho ⟨x, hx⟩} : Set (MulAut ↥E × MulAut ↥E))) := by
  have hC'N : c.Cprime hRN x ≤ c.N1 := (c.Cprime_le hRN x).trans hRN
  let ρ' : ↥(c.Cprime hRN x) →* MulAut ↥E × MulAut ↥E :=
    c.rho.comp (Subgroup.inclusion hC'N)
  have hmul : Nat.card ρ'.ker * Nat.card ρ'.range = Nat.card ↥(c.Cprime hRN x) :=
    Subgroup.card_ker_mul_card_range ρ'
  have hker : Nat.card ρ'.ker ≤ 4 := by
    have hinj : Function.Injective (fun r : ρ'.ker => (⟨((r : ↥(c.Cprime hRN x)) : G),
        hKR ⟨(r : ↥(c.Cprime hRN x)).2.1, c.mem_KR.2 ⟨hC'N (r : ↥(c.Cprime hRN x)).2, r.2⟩⟩⟩ :
        ↥c.Zs)) := by
      intro a b hab
      have h5 := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext h5)
    have := Nat.card_le_card_of_injective _ hinj
    rwa [c.card_Zs'] at this
  have hrange : Nat.card ρ'.range ≤ Nat.card ↥(c.Rhat R ⊓ centralizer
      ({c.rho ⟨x, hx⟩} : Set (MulAut ↥E × MulAut ↥E))) := by
    refine Subgroup.card_le_of_le ?_
    rintro _ ⟨r, rfl⟩
    refine ⟨c.mem_Rhat.2 ⟨⟨(r : G), hC'N r.2⟩, r.2.1, rfl⟩, mem_centralizer_singleton_iff.2 ?_⟩
    have hrx : (r : G) * x * (r : G)⁻¹ * x⁻¹ ∈ c.N1 :=
      mul_mem (mul_mem (mul_mem (hC'N r.2) hx) (inv_mem (hC'N r.2))) (inv_mem hx)
    have h1 : c.rho ⟨(r : G) * x * (r : G)⁻¹ * x⁻¹, hrx⟩ = 1 :=
      c.rho_Zs r.2.2
    have e : (⟨(r : G) * x * (r : G)⁻¹ * x⁻¹, hrx⟩ : ↥c.N1) =
        ⟨(r : G), hC'N r.2⟩ * ⟨x, hx⟩ * ⟨(r : G), hC'N r.2⟩⁻¹ * ⟨x, hx⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    exact cmt_eq_one_iff.1 h1
  calc Nat.card ↥(c.Cprime hRN x) = Nat.card ρ'.ker * Nat.card ρ'.range := hmul.symm
    _ ≤ 4 * Nat.card ↥(c.Rhat R ⊓ centralizer
      ({c.rho ⟨x, hx⟩} : Set (MulAut ↥E × MulAut ↥E))) := Nat.mul_le_mul hker hrange

theorem card_cent_Qhat_le (a a' : MulAut ↥E) :
    Nat.card ↥(c.Rhat c.Qs ⊓ centralizer ({(a, a')} : Set (MulAut ↥E × MulAut ↥E))) ≤
      Nat.card ↥(innAutE E ⊓ centralizer ({a} : Set (MulAut ↥E))) *
        Nat.card ↥(innAutE E ⊓ centralizer ({a'} : Set (MulAut ↥E))) := by
  have hmem : ∀ p : ↥(c.Rhat c.Qs ⊓ centralizer ({(a, a')} : Set (MulAut ↥E × MulAut ↥E))),
      (p : MulAut ↥E × MulAut ↥E).1 ∈ innAutE E ⊓ centralizer ({a} : Set (MulAut ↥E)) ∧
      (p : MulAut ↥E × MulAut ↥E).2 ∈ innAutE E ⊓ centralizer ({a'} : Set (MulAut ↥E)) := by
    rintro ⟨p, hp, hpc⟩
    obtain ⟨r, hrQ, rfl⟩ := c.mem_Rhat.1 hp
    obtain ⟨e₁, e₂, h⟩ := c.rho_Qs_mem hrQ
    have hcomm := mem_centralizer_singleton_iff.1 hpc
    refine ⟨⟨?_, mem_centralizer_singleton_iff.2 (congrArg Prod.fst hcomm)⟩,
      ⟨?_, mem_centralizer_singleton_iff.2 (congrArg Prod.snd hcomm)⟩⟩
    · show (c.rho r).1 ∈ innAutE E
      rw [h]
      exact ⟨e₁, rfl⟩
    · show (c.rho r).2 ∈ innAutE E
      rw [h]
      exact ⟨e₂, rfl⟩
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective
    (fun p => ((⟨(p : MulAut ↥E × MulAut ↥E).1, (hmem p).1⟩ :
        ↥(innAutE E ⊓ centralizer ({a} : Set (MulAut ↥E)))),
      (⟨(p : MulAut ↥E × MulAut ↥E).2, (hmem p).2⟩ :
        ↥(innAutE E ⊓ centralizer ({a'} : Set (MulAut ↥E)))))) ?_
  intro p p' hpp'
  have h1 := congrArg (fun u => (u.1 : MulAut ↥E)) hpp'
  have h2 := congrArg (fun u => (u.2 : MulAut ↥E)) hpp'
  exact Subtype.ext (Prod.ext h1 h2)

variable {c}

include c in
theorem card_cent_inn_le' (hπ : EPi E π)
    (hfix : ∀ φ : MulAut ↥E, BInv E π φ → Nat.card {e : ↥E // φ e = e} = 4)
    {φ' : MulAut ↥E} (hA : π φ' ∈ alternatingGroup (Fin 5)) (h1 : π φ' ≠ 1)
    (h2 : π φ' * π φ' = 1) :
    Nat.card ↥(innAutE E ⊓ centralizer ({φ'} : Set (MulAut ↥E))) ≤ 4 := by
  obtain ⟨b, hb⟩ := c.exists_pi_kappa hπ hA
  set φ := c.kappa b with hφ
  have hbb : b * b = 1 := by
    apply c.pi_kappa_injective hπ
    show π (c.kappa (b * b)) = π (c.kappa 1)
    rw [map_mul, map_mul, map_one, map_one, hb, h2]
  have hφ2 : φ * φ = 1 := by
    rw [hφ, ← map_mul, hbb, map_one]
  have hBInv : BInv E π φ := by
    refine ⟨hφ2, by rw [hφ]; exact c.pi_kappa_mem b, fun hin => h1 ?_⟩
    rw [← hb]
    exact (hπ.ker _).2 hin
  have hi : φ' * φ⁻¹ ∈ innAutE E := by
    refine (hπ.ker _).1 ?_
    rw [map_mul, map_inv, hb]
    group
  have hle : innAutE E ⊓ centralizer ({φ'} : Set (MulAut ↥E)) ≤
      innAutE E ⊓ centralizer ({φ} : Set (MulAut ↥E)) := by
    rintro j ⟨hj, hjc⟩
    refine ⟨hj, mem_centralizer_singleton_iff.2 ?_⟩
    have hjφ' : j * φ' = φ' * j := mem_centralizer_singleton_iff.1 hjc
    have hcomm := c.innAutE_comm hj hi
    have : j * (φ' * φ⁻¹) * φ = (φ' * φ⁻¹) * j * φ := by rw [hcomm]
    calc j * φ = (φ' * φ⁻¹)⁻¹ * ((φ' * φ⁻¹) * (j * φ)) := by group
      _ = (φ' * φ⁻¹)⁻¹ * (((φ' * φ⁻¹) * j) * φ) := by group
      _ = (φ' * φ⁻¹)⁻¹ * ((j * (φ' * φ⁻¹)) * φ) := by rw [hcomm]
      _ = (φ' * φ⁻¹)⁻¹ * ((j * φ') * φ⁻¹ * φ) := by group
      _ = (φ' * φ⁻¹)⁻¹ * ((φ' * j) * φ⁻¹ * φ) := by rw [hjφ']
      _ = φ * j := by group
  exact (Subgroup.card_le_of_le hle).trans (c.card_cent_inn_le (hfix φ hBInv))

end I13Ctx

end CFSG.EvenSporadicStandard.Fin76b
