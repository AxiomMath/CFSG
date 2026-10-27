module

public import CFSG.CGT.Foote82.T66.CaseII513Inv
import CFSG.LocalAnalysis.ComponentClassification.PresentationLocalSymplecticSix
import CFSG.CGT.Foote82.Lemma61
public import CFSG.CGT.Foote82.T66.CaseIINorm

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11 CFSG.RankThree.PartTwo CFSG.PGLModel
open Equiv Equiv.Perm

namespace CaseII

@[expose] def rA : Perm (Fin 6) := swap 2 3 * swap 3 4 * swap 4 5 * swap 0 1
@[expose] def sA : Perm (Fin 6) := swap 2 4 * swap 0 1
@[expose] def tB : Perm (Fin 6) := swap 0 1 * swap 2 3 * swap 4 5
@[expose] def rB : Perm (Fin 6) := swap 0 2 * swap 2 1 * swap 1 3 * swap 4 5
@[expose] def sB : Perm (Fin 6) := swap 0 2 * swap 1 3

structure DihIn (t r s : Perm (Fin 6)) : Prop where
  r_mem : r ∈ alternatingGroup (Fin 6)
  s_mem : s ∈ alternatingGroup (Fin 6)
  orderOf_r : orderOf r = 4
  s_mul_s : s * s = 1
  srs : s * r * s⁻¹ = r⁻¹
  s_not_mem : s ∉ Subgroup.zpowers r
  r_comm : r * t = t * r
  s_comm : s * t = t * s

theorem orderOf_eq_four {σ : Perm (Fin 6)} (h2 : σ ^ 2 ≠ 1) (h4 : σ ^ 4 = 1) : orderOf σ = 4 := by
  have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := σ) (by simpa using h2) (by simpa using h4)
  simpa using h

theorem not_mem_zpowers_of_four {r s : Perm (Fin 6)} (h4 : r ^ (4 : ℕ) = 1)
    (h : s ≠ r ^ (0 : ℕ) ∧ s ≠ r ^ (1 : ℕ) ∧ s ≠ r ^ (2 : ℕ) ∧ s ≠ r ^ (3 : ℕ)) :
    s ∉ Subgroup.zpowers r := by
  intro hs
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hs
  have e : r ^ n = r ^ (n % 4) := by
    have := zpow_eq_zpow_emod' n h4
    simpa using this
  rw [e] at hn
  have h0 : 0 ≤ n % 4 := Int.emod_nonneg n (by norm_num)
  have h1 : n % 4 < 4 := Int.emod_lt_of_pos n (by norm_num)
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n % 4 = k := ⟨(n % 4).toNat, (Int.toNat_of_nonneg h0).symm⟩
  rw [hk, zpow_natCast] at hn
  have hk4 : k < 4 := by omega
  interval_cases k
  · exact h.1 hn.symm
  · exact h.2.1 hn.symm
  · exact h.2.2.1 hn.symm
  · exact h.2.2.2 hn.symm

theorem dihIn_A : DihIn (swap 0 1) rA sA where
  r_mem := by
    rw [mem_alternatingGroup, rA, Perm.sign_mul, Perm.sign_mul, Perm.sign_mul,
      Perm.sign_swap (by decide), Perm.sign_swap (by decide), Perm.sign_swap (by decide),
      Perm.sign_swap (by decide)]
    decide
  s_mem := by
    rw [mem_alternatingGroup, sA, Perm.sign_mul, Perm.sign_swap (by decide),
      Perm.sign_swap (by decide)]
    decide
  orderOf_r := orderOf_eq_four (by decide) (by decide)
  s_mul_s := by decide
  srs := by decide
  s_not_mem := not_mem_zpowers_of_four (by decide) (by decide)
  r_comm := by decide
  s_comm := by decide

theorem dihIn_B : DihIn tB rB sB where
  r_mem := by
    rw [mem_alternatingGroup, rB, Perm.sign_mul, Perm.sign_mul, Perm.sign_mul,
      Perm.sign_swap (by decide), Perm.sign_swap (by decide), Perm.sign_swap (by decide),
      Perm.sign_swap (by decide)]
    decide
  s_mem := by
    rw [mem_alternatingGroup, sB, Perm.sign_mul, Perm.sign_swap (by decide),
      Perm.sign_swap (by decide)]
    decide
  orderOf_r := orderOf_eq_four (by decide) (by decide)
  s_mul_s := by decide
  srs := by decide
  s_not_mem := not_mem_zpowers_of_four (by decide) (by decide)
  r_comm := by decide
  s_comm := by decide

theorem DihIn.conj {t r s : Perm (Fin 6)} (h : DihIn t r s) (π : Perm (Fin 6)) :
    DihIn (π * t * π⁻¹) (π * r * π⁻¹) (π * s * π⁻¹) where
  r_mem := (inferInstance : (alternatingGroup (Fin 6)).Normal).conj_mem _ h.r_mem π
  s_mem := (inferInstance : (alternatingGroup (Fin 6)).Normal).conj_mem _ h.s_mem π
  orderOf_r := by rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, h.orderOf_r]
  s_mul_s := by
    calc π * s * π⁻¹ * (π * s * π⁻¹) = π * (s * s) * π⁻¹ := by group
      _ = 1 := by rw [h.s_mul_s, mul_one, mul_inv_cancel]
  srs := by
    calc π * s * π⁻¹ * (π * r * π⁻¹) * (π * s * π⁻¹)⁻¹ = π * (s * r * s⁻¹) * π⁻¹ := by group
      _ = (π * r * π⁻¹)⁻¹ := by rw [h.srs]; group
  s_not_mem := by
    intro hm
    apply h.s_not_mem
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hm
    refine Subgroup.mem_zpowers_iff.2 ⟨n, ?_⟩
    have h1 : MulAut.conj π (r ^ n) = MulAut.conj π s := by
      rw [map_zpow, MulAut.conj_apply, MulAut.conj_apply, hn]
    exact (MulAut.conj π).injective h1
  r_comm := by
    calc π * r * π⁻¹ * (π * t * π⁻¹) = π * (r * t) * π⁻¹ := by group
      _ = π * (t * r) * π⁻¹ := by rw [h.r_comm]
      _ = π * t * π⁻¹ * (π * r * π⁻¹) := by group
  s_comm := by
    calc π * s * π⁻¹ * (π * t * π⁻¹) = π * (s * t) * π⁻¹ := by group
      _ = π * (t * s) * π⁻¹ := by rw [h.s_comm]
      _ = π * t * π⁻¹ * (π * s * π⁻¹) := by group

theorem swap01_cycleType : (swap (0 : Fin 6) 1).cycleType = {2} := by
  rw [(isCycle_swap (by decide : (0 : Fin 6) ≠ 1)).cycleType, card_support_swap (by decide)]

theorem tB_cycleType : tB.cycleType = {2, 2, 2} := by
  have h1 : (swap (0 : Fin 6) 1).IsCycle := isCycle_swap (by decide)
  have h2 : (swap (2 : Fin 6) 3).IsCycle := isCycle_swap (by decide)
  have h3 : (swap (4 : Fin 6) 5).IsCycle := isCycle_swap (by decide)
  have hd1 : Equiv.Perm.Disjoint (swap (0 : Fin 6) 1) (swap 2 3) := by
    rw [disjoint_iff_disjoint_support]
    decide
  have hd2 : Equiv.Perm.Disjoint (swap (0 : Fin 6) 1 * swap 2 3) (swap 4 5) := by
    rw [disjoint_iff_disjoint_support]
    decide
  rw [tB, hd2.cycleType_mul, hd1.cycleType_mul, h1.cycleType, h2.cycleType, h3.cycleType,
    card_support_swap (by decide), card_support_swap (by decide), card_support_swap (by decide)]
  rfl

theorem exists_dih_perm {τ : Perm (Fin 6)} (hτ : τ ∉ alternatingGroup (Fin 6))
    (hτ2 : τ * τ = 1) : ∃ r s : Perm (Fin 6), DihIn τ r s := by
  have hτ1 : τ ≠ 1 := fun h => hτ (h ▸ (alternatingGroup (Fin 6)).one_mem)
  have ho : orderOf τ = 2 := orderOf_eq_two_of_mul_self hτ2 hτ1
  rcases cycleType_of_orderOf_two_odd ho hτ with h | h
  · obtain ⟨π, hπ⟩ := isConj_iff.1 (isConj_iff_cycleType_eq.2 (swap01_cycleType.trans h.symm))
    refine ⟨π * rA * π⁻¹, π * sA * π⁻¹, ?_⟩
    rw [← hπ]
    exact dihIn_A.conj π
  · obtain ⟨π, hπ⟩ := isConj_iff.1 (isConj_iff_cycleType_eq.2 (tB_cycleType.trans h.symm))
    refine ⟨π * rB * π⁻¹, π * sB * π⁻¹, ?_⟩
    rw [← hπ]
    exact dihIn_B.conj π

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {G L : Subgroup (GLV V)} {z : GLV V} {v : V} {H₁ : Subgroup (GLV V)}
  {ψ : ↥H₁ ≃* ↥(orthogonalMinus 2 (ZMod 2) 1 1)}

theorem eq_of_finrank_eq_one {W : Submodule (ZMod 2) V} (h : Module.finrank (ZMod 2) ↥W = 1)
    {a b : V} (ha : a ∈ W) (hb : b ∈ W) (ha0 : a ≠ 0) (hb0 : b ≠ 0) : a = b := by
  obtain ⟨e, -, hall⟩ := finrank_eq_one_iff'.1 h
  have key : ∀ x ∈ W, x ≠ 0 → x = (e : V) := by
    intro x hx hx0
    obtain ⟨cx, hcx⟩ := hall ⟨x, hx⟩
    have hcx' : cx • (e : V) = x := congrArg Subtype.val hcx
    rcases zmod2_cases cx with h0 | h1
    · rw [h0, zero_smul] at hcx'
      exact absurd hcx'.symm hx0
    · rw [h1, one_smul] at hcx'
      exact hcx'.symm
  rw [key a ha ha0, key b hb hb0]

namespace GD

variable {c : Ctx G L z v H₁ ψ} {g : GLV V} (d : GD c g)
include d

theorem u_mem_G : g * z * g⁻¹ ∈ G := c.H₁_le_G d.u_mem_H₁

theorem u_mem_Cz : g * z * g⁻¹ ∈ G ⊓ Subgroup.centralizer ({z} : Set (GLV V)) :=
  ⟨d.u_mem_G, Subgroup.mem_centralizer_singleton_iff.2 d.comm⟩

theorem u_mem_N : g * z * g⁻¹ ∈ Subgroup.normalizer (L : Set (GLV V)) :=
  c.centralizer_le_normalizer d.u_mem_Cz

theorem orderOf_u : orderOf (g * z * g⁻¹) = 2 := c.orderOf_conj_z g

theorem cdim6_u : cdim6 (ψ ⟨g * z * g⁻¹, d.u_mem_H₁⟩) = 1 := by
  rw [cdim6_eq_rank, d.psi_u, ← cdim6_eq_rank]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [cdim6_conj]
  exact c.data.ψ_z

theorem finrank_V₀u (hs : CaseIISplit) :
    Module.finrank (ZMod 2) ↥((commSpace (HH G L v) ⊤).map (subOne (g * z * g⁻¹))) = 1 := by
  rw [c.finrank_map_V₀ hs d.u_mem_H₁]
  exact d.cdim6_u

theorem u_not_mem_centralizer (hG1 : CaseIIG1) :
    g * z * g⁻¹ ∉ Subgroup.centralizer (L : Set (GLV V)) := by
  intro h
  rcases c.eq_one_or_eq_z hG1 d.u_mem_H₁
      (fun l hl => (Subgroup.mem_centralizer_iff.1 h l hl).symm) with h1 | h1
  · have h2 := d.orderOf_u
    rw [h1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  · exact d.ne h1

theorem not_inner (hs : CaseIISplit) (hG1 : CaseIIG1)
    {α : ↥L →* ↥(alternatingGroup (Fin 6))} {β : ↥(commSpace L ⊤) →+ altHeart 6}
    (ad : AD L α β) (hL : Nonempty (↥L ≃* alternatingGroup (Fin 6))) (ℓ₀ : ↥L)
    (hconj : ∀ l : ↥L, conjL L ⟨g * z * g⁻¹, d.u_mem_N⟩ l = ℓ₀ * l * ℓ₀⁻¹) : False := by
  set u := g * z * g⁻¹ with hu
  have hu2 : u * u = 1 := d.u_mul_u
  have hk : ∀ l ∈ L, ((ℓ₀ : GLV V)⁻¹ * u) * l = l * ((ℓ₀ : GLV V)⁻¹ * u) := by
    intro l hl
    have h1 := congrArg Subtype.val (hconj ⟨l, hl⟩)
    rw [conjL_coe] at h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
    calc (↑ℓ₀)⁻¹ * u * l = (↑ℓ₀)⁻¹ * (u * l * u⁻¹) * u := by group
      _ = (↑ℓ₀)⁻¹ * (↑ℓ₀ * l * (↑ℓ₀)⁻¹) * u := by rw [h1]
      _ = l * ((↑ℓ₀)⁻¹ * u) := by group
  have hkH₁ : (ℓ₀ : GLV V)⁻¹ * u ∈ H₁ := H₁.mul_mem (H₁.inv_mem (c.L_le_H₁ ℓ₀.2)) d.u_mem_H₁
  have h61 := c.std.extremal.setup.toSetup6.lemma61 (Subgroup.mem_zpowers z)
  have hcases := c.eq_one_or_eq_z hG1 hkH₁ hk
  have hagree : ∀ w ∈ commSpace L ⊤, u w = (ℓ₀ : GLV V) w := by
    intro w hw
    rcases hcases with h | h
    · have : u = ℓ₀ := by
        have := congrArg (fun t => (ℓ₀ : GLV V) * t) h
        simpa using this
      rw [this]
    · have hu' : u = (ℓ₀ : GLV V) * z := by
        have := congrArg (fun t => (ℓ₀ : GLV V) * t) h
        simpa using this
      have hzw : z w = w := (h61.2 hw) z (Subgroup.mem_zpowers z)
      rw [hu']
      show (ℓ₀ : GLV V) (z w) = (ℓ₀ : GLV V) w
      rw [hzw]
  have hℓ₀2 : (ℓ₀ : GLV V) * ℓ₀ = 1 := by
    rcases hcases with h | h
    · have : u = ℓ₀ := by
        have := congrArg (fun t => (ℓ₀ : GLV V) * t) h
        simpa using this
      rw [← this, hu2]
    · have hu' : (ℓ₀ : GLV V) = u * z := by
        have := congrArg (fun t => (ℓ₀ : GLV V) * t) h
        have h2 : u = (ℓ₀ : GLV V) * z := by simpa using this
        rw [h2, mul_assoc, c.z_mul_z, mul_one]
      rw [hu']
      calc u * z * (u * z) = u * (z * u) * z := by group
        _ = u * (u * z) * z := by rw [d.comm]
        _ = (u * u) * (z * z) := by group
        _ = 1 := by rw [hu2, c.z_mul_z, mul_one]
  have hℓ₀1 : (ℓ₀ : GLV V) ≠ 1 := by
    intro h1
    rw [h1, inv_one, one_mul] at hcases
    rcases hcases with h | h
    · have h2 : orderOf u = 2 := d.orderOf_u
      rw [h, orderOf_one] at h2
      exact absurd h2 (by norm_num)
    · exact d.ne h
  have hℓ₀o : orderOf ℓ₀ = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact orderOf_eq_two_of_mul_self hℓ₀2 hℓ₀1
  have hαo : orderOf (α ℓ₀ : Perm (Fin 6)) = 2 := by
    rw [Subgroup.orderOf_coe, ← ad.αe_apply hL, MulEquiv.orderOf_eq, hℓ₀o]
  obtain ⟨w₁, w₂, h1, h2, h12⟩ :=
    ad.exists_two_comm ℓ₀ (cycleType_of_orderOf_two hαo (α ℓ₀).2)
  have hmem : ∀ w : ↥(commSpace L ⊤), (ℓ₀ : GLV V) w - w ∈
      (commSpace (HH G L v) ⊤).map (subOne u) := by
    intro w
    rw [← hagree w w.2]
    exact ⟨w, c.VL_le_V₀ w.2, (subOne_apply u w).symm⟩
  exact h12 (eq_of_finrank_eq_one (d.finrank_V₀u hs) (hmem w₁) (hmem w₂) h1 h2)

theorem exists_odd_perm (hs : CaseIISplit) (hG1 : CaseIIG1)
    {α : ↥L →* ↥(alternatingGroup (Fin 6))} {β : ↥(commSpace L ⊤) →+ altHeart 6}
    (ad : AD L α β) (hL : Nonempty (↥L ≃* alternatingGroup (Fin 6))) :
    ∃ τ : Perm (Fin 6), τ ∉ alternatingGroup (Fin 6) ∧ τ * τ = 1 ∧
      ∀ l : ↥L, (α (conjL L ⟨g * z * g⁻¹, d.u_mem_N⟩ l) : Perm (Fin 6)) = τ * α l * τ⁻¹ := by
  set u := g * z * g⁻¹ with hu
  set un : ↥(Subgroup.normalizer (L : Set (GLV V))) := ⟨u, d.u_mem_N⟩ with hun
  obtain ⟨τ, hτ⟩ := ad.exists_perm hL un
  have hu2 : u * u = 1 := d.u_mul_u
  refine ⟨τ, ?_, ?_, hτ⟩
  ·
    intro hτA
    obtain ⟨ℓ₀, hℓ₀⟩ := ad.α_surj ⟨τ, hτA⟩
    have hconj : ∀ l : ↥L, conjL L un l = ℓ₀ * l * ℓ₀⁻¹ := by
      intro l
      apply ad.α_injective hL
      apply Subtype.ext
      rw [hτ l, map_mul, map_mul, map_inv, hℓ₀]
      rfl
    exact d.not_inner hs hG1 ad hL ℓ₀ hconj
  ·
    have hcen := CFSG.ComponentClassification.PresentationLocal.centralizer_alternatingGroup_eq_bot
      (α := Fin 6) (by simp)
    have hmem : τ * τ ∈ Subgroup.centralizer (alternatingGroup (Fin 6) : Set (Perm (Fin 6))) := by
      rw [Subgroup.mem_centralizer_iff]
      intro σ hσ
      obtain ⟨l, hl⟩ := ad.α_surj ⟨σ, hσ⟩
      have hll : conjL L un (conjL L un l) = l := by
        apply Subtype.ext
        rw [conjL_coe, conjL_coe]
        show u * (u * (l : GLV V) * u⁻¹) * u⁻¹ = l
        have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
        rw [hui]
        calc u * (u * ↑l * u) * u = (u * u) * ↑l * (u * u) := by group
          _ = ↑l := by rw [hu2, one_mul, mul_one]
      have h1 := hτ (conjL L un l)
      rw [hll, hτ l] at h1
      have hσ' : (α l : Perm (Fin 6)) = σ := congrArg Subtype.val hl
      rw [hσ'] at h1
      calc σ * (τ * τ) = (τ * (τ * σ * τ⁻¹) * τ⁻¹) * (τ * τ) := by rw [← h1]
        _ = τ * τ * σ := by group
    rw [hcen, Subgroup.mem_bot] at hmem
    exact hmem

theorem exists_rs (hs : CaseIISplit) (hG1 : CaseIIG1)
    {α : ↥L →* ↥(alternatingGroup (Fin 6))} {β : ↥(commSpace L ⊤) →+ altHeart 6}
    (ad : AD L α β) (hL : Nonempty (↥L ≃* alternatingGroup (Fin 6))) :
    ∃ r s : GLV V, r ∈ L ∧ s ∈ L ∧ orderOf r = 4 ∧ s * s = 1 ∧ s * r * s⁻¹ = r⁻¹ ∧
      s ∉ Subgroup.zpowers r ∧ r * (g * z * g⁻¹) = (g * z * g⁻¹) * r ∧
      s * (g * z * g⁻¹) = (g * z * g⁻¹) * s := by
  obtain ⟨τ, hτ, hτ2, hτc⟩ := d.exists_odd_perm hs hG1 ad hL
  obtain ⟨r', s', hd⟩ := exists_dih_perm hτ hτ2
  set e := ad.αe hL with he
  set ℓr : ↥L := e.symm ⟨r', hd.r_mem⟩ with hℓr
  set ℓs : ↥L := e.symm ⟨s', hd.s_mem⟩ with hℓs
  have hαr : (α ℓr : Perm (Fin 6)) = r' := by
    rw [← ad.αe_apply hL, ← he, hℓr, MulEquiv.apply_symm_apply]
  have hαs : (α ℓs : Perm (Fin 6)) = s' := by
    rw [← ad.αe_apply hL, ← he, hℓs, MulEquiv.apply_symm_apply]
  have hcomm : ∀ ℓ : ↥L, (α ℓ : Perm (Fin 6)) * τ = τ * α ℓ →
      (ℓ : GLV V) * (g * z * g⁻¹) = (g * z * g⁻¹) * ℓ := by
    intro ℓ hℓ
    have h1 : conjL L ⟨g * z * g⁻¹, d.u_mem_N⟩ ℓ = ℓ := by
      apply ad.α_injective hL
      apply Subtype.ext
      rw [hτc ℓ, ← hℓ, mul_inv_cancel_right]
    have h2 := congrArg Subtype.val h1
    rw [conjL_coe] at h2
    calc (ℓ : GLV V) * (g * z * g⁻¹) = (g * z * g⁻¹) * ℓ * (g * z * g⁻¹)⁻¹ * (g * z * g⁻¹) := by
          rw [h2]
      _ = (g * z * g⁻¹) * ℓ := by group
  refine ⟨ℓr, ℓs, ℓr.2, ℓs.2, ?_, ?_, ?_, ?_, hcomm ℓr (by rw [hαr]; exact hd.r_comm),
    hcomm ℓs (by rw [hαs]; exact hd.s_comm)⟩
  · rw [Subgroup.orderOf_coe, hℓr, MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hd.orderOf_r]
  · have : ℓs * ℓs = 1 := by
      rw [hℓs, ← map_mul, show (⟨s', hd.s_mem⟩ : ↥(alternatingGroup (Fin 6))) * ⟨s', hd.s_mem⟩ = 1
        from Subtype.ext hd.s_mul_s, map_one]
    exact congrArg Subtype.val this
  · have : ℓs * ℓr * ℓs⁻¹ = ℓr⁻¹ := by
      rw [hℓs, hℓr, ← map_inv, ← map_mul, ← map_mul, ← map_inv]
      congr 1
      exact Subtype.ext hd.srs
    exact congrArg Subtype.val this
  · intro hm
    apply hd.s_not_mem
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hm
    refine Subgroup.mem_zpowers_iff.2 ⟨n, ?_⟩
    have h1 : ℓr ^ n = ℓs := Subtype.ext (by rw [Subgroup.coe_zpow, hn])
    have h2 := congrArg (fun t => (e t : Perm (Fin 6))) h1
    simp only [map_zpow, hℓr, hℓs, MulEquiv.apply_symm_apply, Subgroup.coe_zpow] at h2
    exact h2

end GD

end CaseII

end CFSG.CGT.Foote82
