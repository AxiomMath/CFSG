module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB83S2Data
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB8Triple

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

namespace Eight

theorem conjugate_centralizer_singleton {G : Type*} [Group G] (u g : G) :
    conjugate (centralizer ({u} : Set G)) g = centralizer ({g⁻¹ * u * g} : Set G) := by
  ext x
  rw [mem_conjugate_iff, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro hx
    calc x * (g⁻¹ * u * g) = g⁻¹ * ((g * x * g⁻¹) * u) * g := by group
      _ = g⁻¹ * (u * (g * x * g⁻¹)) * g := by rw [hx]
      _ = g⁻¹ * u * g * x := by group
  · intro hx
    calc g * x * g⁻¹ * u = g * (x * (g⁻¹ * u * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * u * g) * x) * g⁻¹ := by rw [hx]
      _ = u * (g * x * g⁻¹) := by group

variable {A B : Type*} [Group A] [Group B]

theorem fixSubgroup_trans (κ : A ≃* B) (α : MulAut A) :
    fixSubgroup (κ.symm.trans (α.trans κ)) = (fixSubgroup α).map κ.toMonoidHom := by
  ext y
  rw [mem_fixSubgroup, MulEquiv.trans_apply, MulEquiv.trans_apply]
  constructor
  · intro hy
    refine ⟨κ.symm y, ?_, by simp⟩
    show α (κ.symm y) = κ.symm y
    apply κ.injective
    rw [hy, MulEquiv.apply_symm_apply]
  · rintro ⟨x, hx, rfl⟩
    have hx' : α x = x := hx
    simp [hx']

end Eight

namespace Cat8

theorem IsAdmQ.trans {K₀ K₁ : Type} [Group K₀] [Group K₁] {q : ℕ} {α : MulAut K₀}
    (hα : IsAdmQ K₀ q α) (κ : K₀ ≃* K₁) : IsAdmQ K₁ q (κ.symm.trans (α.trans κ)) where
  sq := by
    have h2 : ∀ z, α (α z) = z := fun z => by simpa using DFunLike.congr_fun hα.sq z
    ext x
    simp only [MulAut.mul_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
      MulAut.one_apply]
    rw [h2, MulEquiv.apply_symm_apply]
  out h1 := hα.out ((Eight.trans_mem_range_conj_iff κ α).mp h1)
  dvd := by
    rw [Eight.fixSubgroup_trans, card_map_of_injective κ.injective]
    exact hα.dvd

end Cat8

namespace Hyp52

variable {X : Type} [Group X] [Finite X] {h : Hyp52 X}

namespace L83Hyp

variable {H : L83Hyp h}

namespace S2Data

variable (d : S2Data H)
include d

abbrev xg : X := h.x * d.g

abbrev w : X := d.xg⁻¹ * d.b * d.xg

abbrev e : X := d.xg⁻¹ * h.a * d.xg

abbrev L : Subgroup X := conjugate h.K d.xg

theorem g_conj_b : d.g⁻¹ * d.b * d.g = d.b := by
  rw [mul_assoc, ← d.b_comm_of_mem_M3 d.g_M, inv_mul_cancel_left]

theorem e_eq : d.e = h.a * d.tau := by
  have hxa : h.x⁻¹ * h.a * h.x = h.a := by
    rw [mul_assoc, ← mem_centralizer_singleton_iff.mp (h.S_le h.x_mem).1, inv_mul_cancel_left]
  calc d.e = d.g⁻¹ * (h.x⁻¹ * h.a * h.x) * d.g := by
        show (h.x * d.g)⁻¹ * h.a * (h.x * d.g) = _
        group
    _ = d.g⁻¹ * h.a * d.g := by rw [hxa]
    _ = h.a * d.tau := d.a_g

theorem w_eq : d.w = h.a * d.tau * d.b := by
  calc d.w = d.g⁻¹ * (h.x⁻¹ * d.b * h.x) * d.g := by
        show (h.x * d.g)⁻¹ * d.b * (h.x * d.g) = _
        group
    _ = (d.g⁻¹ * h.a * d.g) * (d.g⁻¹ * d.b * d.g) := by
        rw [d.xbx]
        group
    _ = h.a * d.tau * d.b := by rw [d.a_g, d.g_conj_b]

theorem w_mul_self : d.w * d.w = 1 := by
  show d.xg⁻¹ * d.b * d.xg * (d.xg⁻¹ * d.b * d.xg) = 1
  rw [show d.xg⁻¹ * d.b * d.xg * (d.xg⁻¹ * d.b * d.xg) = d.xg⁻¹ * (d.b * d.b) * d.xg by group,
    d.b_mul_self, mul_one, inv_mul_cancel]

theorem w_ne_one : d.w ≠ 1 := by
  intro h1
  apply d.b_ne_one
  have h2 : d.b = d.xg * d.w * d.xg⁻¹ := by
    show d.b = d.xg * (d.xg⁻¹ * d.b * d.xg) * d.xg⁻¹
    group
  rw [h2, h1, mul_one, mul_inv_cancel]

theorem orderOf_w : orderOf d.w = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [pow_two]; exact d.w_mul_self) d.w_ne_one

theorem w_comm_a : d.w * h.a = h.a * d.w := by
  rw [d.w_eq]
  calc h.a * d.tau * d.b * h.a = h.a * d.tau * (d.b * h.a) := by group
    _ = h.a * d.tau * (h.a * d.b) := by rw [d.ba]
    _ = h.a * (d.tau * h.a) * d.b := by group
    _ = h.a * (h.a * d.tau) * d.b := by rw [d.tau_comm_a]
    _ = h.a * (h.a * d.tau * d.b) := by group

theorem e_comm_w : d.e * d.w = d.w * d.e := by
  show d.xg⁻¹ * h.a * d.xg * (d.xg⁻¹ * d.b * d.xg) = d.xg⁻¹ * d.b * d.xg * (d.xg⁻¹ * h.a * d.xg)
  calc d.xg⁻¹ * h.a * d.xg * (d.xg⁻¹ * d.b * d.xg) = d.xg⁻¹ * (d.b * h.a) * d.xg := by
        rw [d.ba]
        group
    _ = d.xg⁻¹ * d.b * d.xg * (d.xg⁻¹ * h.a * d.xg) := by group

theorem e_comm_a : d.e * h.a = h.a * d.e := by
  rw [d.e_eq, mul_assoc, d.tau_comm_a]

theorem e_mul_self : d.e * d.e = 1 := by
  show d.xg⁻¹ * h.a * d.xg * (d.xg⁻¹ * h.a * d.xg) = 1
  rw [show d.xg⁻¹ * h.a * d.xg * (d.xg⁻¹ * h.a * d.xg) = d.xg⁻¹ * (h.a * h.a) * d.xg by group,
    Six.a_mul_a_self h, mul_one, inv_mul_cancel]

theorem a_mem_centralizer_w : h.a ∈ centralizer ({d.w} : Set X) :=
  mem_centralizer_singleton_iff.mpr d.w_comm_a.symm

theorem e_mem_centralizer_w : d.e ∈ centralizer ({d.w} : Set X) :=
  mem_centralizer_singleton_iff.mpr d.e_comm_w

theorem w_mem_centralizer_a : d.w ∈ centralizer ({h.a} : Set X) :=
  mem_centralizer_singleton_iff.mpr d.w_comm_a

theorem centralizer_w_eq :
    conjugate (centralizer ({d.b} : Set X)) d.xg = centralizer ({d.w} : Set X) :=
  Eight.conjugate_centralizer_singleton d.b d.xg

theorem K_le_centralizer_b : h.K ≤ centralizer ({d.b} : Set X) := fun _ hk =>
  mem_centralizer_singleton_iff.mpr (d.b_comm_of_mem_M3 (mem_sup_left hk))

theorem L_le_centralizer_w : d.L ≤ centralizer ({d.w} : Set X) := by
  rw [← d.centralizer_w_eq]
  exact map_mono d.K_le_centralizer_b

theorem L_eq_layerIn : d.L = layerIn (centralizer ({d.w} : Set X)) := by
  rw [← d.centralizer_w_eq, ← d.normalizer_B, S2Data.L, ← H.V_eq_K, Hyp52.V,
    Six.conjugate_layerIn]

theorem centralizer_w_le_normalizer_L :
    centralizer ({d.w} : Set X) ≤ normalizer (d.L : Set X) := by
  rw [d.L_eq_layerIn]
  exact OddQuot.le_normalizer_layerIn _

theorem a_mem_normalizer_L : h.a ∈ normalizer (d.L : Set X) :=
  d.centralizer_w_le_normalizer_L d.a_mem_centralizer_w

theorem e_mem_normalizer_L : d.e ∈ normalizer (d.L : Set X) :=
  d.centralizer_w_le_normalizer_L d.e_mem_centralizer_w

theorem isPComponent_L : IsPComponent 2 (d.L.subgroupOf (centralizer ({d.w} : Set X))) := by
  have h1 := (Six.isPComponent_conjugate h.isPComponent_K.1 h.isPComponent_K.2 d.xg).2
  rwa [d.normalizer_B, d.centralizer_w_eq] at h1

@[expose] noncomputable def eKL : h.K ≃* d.L :=
  h.K.equivMapOfInjective (MulAut.conj d.xg⁻¹).toMonoidHom (MulAut.conj d.xg⁻¹).injective

theorem eKL_apply (k : h.K) : ((d.eKL k : d.L) : X) = d.xg⁻¹ * k * d.xg := by
  show (MulAut.conj d.xg⁻¹) k = _
  rw [MulAut.conj_apply, inv_inv]

@[expose] noncomputable def eKLbar : (h.K ⧸ pPrimeCore 2 h.K) ≃* (d.L ⧸ pPrimeCore 2 d.L) :=
  QuotientGroup.congr (pPrimeCore 2 h.K) (pPrimeCore 2 d.L) d.eKL (pPrimeCore_map_iso 2 d.eKL)

theorem isSec8Socle_L {p f : ℕ} (hK : IsSec8Socle (h.K ⧸ pPrimeCore 2 h.K) p f) :
    IsSec8Socle (d.L ⧸ pPrimeCore 2 d.L) p f :=
  Eight.isSec8Socle_of_mulEquiv d.eKLbar hK

theorem center_Lbar (hCF1 : CFSec8Simple) : center (d.L ⧸ pPrimeCore 2 d.L) = ⊥ := by
  obtain ⟨-, p, f, hp, hp2, hf, hK, -⟩ := Sec8Case.exists_params h H.sec8Case
  obtain ⟨hsimp, u, v, huv⟩ := hCF1 _ p f hp hp2 hf (d.isSec8Socle_L hK)
  have := hsimp
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (d.L ⧸ pPrimeCore 2 d.L)) with h1 | h1
  · exact h1
  · exfalso
    apply huv
    have hu : u ∈ center (d.L ⧸ pPrimeCore 2 d.L) := h1 ▸ mem_top u
    exact (Subgroup.mem_center_iff.mp hu v).symm

noncomputable abbrev epsL : MulAut (d.L ⧸ pPrimeCore 2 d.L) :=
  Eight.oddBarAction d.L ⟨d.e, d.e_mem_normalizer_L⟩

theorem epsL_eq : d.epsL = d.eKLbar.symm.trans (H.rhoA.trans d.eKLbar) := by
  have key : ∀ k : h.K, d.epsL (d.eKLbar (k : h.K ⧸ pPrimeCore 2 h.K)) =
      d.eKLbar (H.rhoA (k : h.K ⧸ pPrimeCore 2 h.K)) := by
    intro k
    have hk : h.a * (k : X) * h.a⁻¹ ∈ h.K :=
      (mem_normalizer_iff.mp H.a_mem_normalizer_K k).mp k.2
    have h1 : d.eKLbar (H.rhoA (k : h.K ⧸ pPrimeCore 2 h.K)) =
        ((d.eKL ⟨h.a * k * h.a⁻¹, hk⟩ : d.L) : d.L ⧸ pPrimeCore 2 d.L) := rfl
    have h2 : d.epsL (d.eKLbar (k : h.K ⧸ pPrimeCore 2 h.K)) =
        ((⟨d.e * (d.eKL k : X) * d.e⁻¹, (mem_normalizer_iff.mp d.e_mem_normalizer_L _).mp
          (d.eKL k).2⟩ : d.L) : d.L ⧸ pPrimeCore 2 d.L) := rfl
    rw [h1, h2]
    congr 1
    apply Subtype.ext
    show d.e * ((d.eKL k : d.L) : X) * d.e⁻¹ = ((d.eKL ⟨h.a * k * h.a⁻¹, hk⟩ : d.L) : X)
    rw [eKL_apply, eKL_apply]
    show d.xg⁻¹ * h.a * d.xg * (d.xg⁻¹ * k * d.xg) * (d.xg⁻¹ * h.a * d.xg)⁻¹ =
      d.xg⁻¹ * (h.a * k * h.a⁻¹) * d.xg
    group
  ext y
  obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective (d.eKLbar.symm y)
  have hy : y = d.eKLbar (k : h.K ⧸ pPrimeCore 2 h.K) := by
    rw [hk, MulEquiv.apply_symm_apply]
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, hy, MulEquiv.symm_apply_apply, key]

theorem epsL_admQ (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) (hJo : CFSec8JOrder)
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hJ : IsSec8JType (h.J ⧸ pPrimeCore 2 h.J) p f) :
    Cat8.IsAdmQ (d.L ⧸ pPrimeCore 2 d.L) (p ^ f) d.epsL := by
  rw [d.epsL_eq]
  exact (H.rhoA_admQ hCF1 hCF2 hJo hp hp2 hf hJ).trans d.eKLbar

noncomputable abbrev sigL : MulAut d.L := d.L.normalizerMonoidHom ⟨h.a, d.a_mem_normalizer_L⟩

noncomputable abbrev alphaL : MulAut (d.L ⧸ pPrimeCore 2 d.L) :=
  Eight.oddBarAction d.L ⟨h.a, d.a_mem_normalizer_L⟩

theorem alphaL_eq : d.alphaL = Eight.oddBarAut d.L d.sigL := rfl

theorem sigL_mul_self : d.sigL * d.sigL = 1 := by
  show d.L.normalizerMonoidHom ⟨h.a, d.a_mem_normalizer_L⟩ *
    d.L.normalizerMonoidHom ⟨h.a, d.a_mem_normalizer_L⟩ = 1
  rw [← map_mul, show (⟨h.a, d.a_mem_normalizer_L⟩ : normalizer (d.L : Set X)) *
    ⟨h.a, d.a_mem_normalizer_L⟩ = 1 from Subtype.ext (Six.a_mul_a_self h), map_one]

theorem alphaL_mul_self : d.alphaL * d.alphaL = 1 := by
  rw [d.alphaL_eq, ← map_mul, d.sigL_mul_self, map_one]

end S2Data

end L83Hyp

end Hyp52

end CFSG.ComponentClassification.GSThmB
