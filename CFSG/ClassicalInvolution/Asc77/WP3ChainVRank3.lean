module

import CFSG.ClassicalInvolution.Asc77.AscE187Img
import CFSG.ClassicalInvolution.Asc77.WP3FrameModelPSU
import CFSG.ClassicalInvolution.ModelFacts.Orth15ChainLModel
import CFSG.ClassicalInvolution.ModelFacts.Orth15ChainUModel
public import CFSG.ClassicalInvolution.Asc77.WP3FrameChain
public import CFSG.ClassicalInvolution.Asc77.WP3FrameLieE

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Disconnected
open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section Shape

variable (p f : ℕ) [Fact p.Prime] {G : Type} [Group G] [Finite G]

@[expose] def ChainShapeRank (n : ℕ) (Ω : Set (Subgroup G)) (z : G) : Prop :=
  ∃ D : LocalLieSystemAt p f (exactFamily Ω z) z,
    D.card = 2 ∧ ∃ i₀ i₁ : Fin D.card, i₀ ≠ i₁ ∧ D.tag i₀ = .PSL ∧ D.rank i₀ = 2 ∧
      (D.tag i₁ = .PSL ∨ D.tag i₁ = .PSU) ∧ D.rank i₁ = n

variable {p f}

theorem chainShape_cases {Ω : Set (Subgroup G)} {z : G} (h : ChainShape p f Ω z) :
    ChainShapeRank p f 3 Ω z ∨ ChainShapeRank p f 4 Ω z := by
  obtain ⟨D, hcard, i₀, i₁, hne, ht₀, hr₀, ht₁, hr₁⟩ := h
  rcases hr₁ with h3 | h4
  · exact Or.inl ⟨D, hcard, i₀, i₁, hne, ht₀, hr₀, ht₁, h3⟩
  · exact Or.inr ⟨D, hcard, i₀, i₁, hne, ht₀, hr₀, ht₁, h4⟩

end Shape

section Model3

theorem rank3_model_involution {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    ∀ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n e : ℕ), (t = .PSL ∨ t = .PSU) → n = 3 →
      5 ≤ p ^ e →
      StatedLieAdmissible t n p e → ∀ {H : Type} [Group H]
      (ψ : (modelUniv t n p e Fact.out).K →* H),
      ψ.ker ≤ Subgroup.center (modelUniv t n p e Fact.out).K →
      ∀ {R : Subgroup (modelUniv t n p e Fact.out).K},
      R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D →
      ∀ {x : (modelUniv t n p e Fact.out).K}, x ∈ R → (∀ r ∈ R, x * r = r * x) → x ≠ 1 →
      ∀ {v : H}, v ∈ Subgroup.normalizer (ψ.range : Set H) → v * v = 1 →
      (∀ r ∈ R, v * ψ r = ψ r * v) →
      (∀ y ∈ ψ.range, v * y = y * v) ∨ (∀ y ∈ ψ.range, (v * ψ x) * y = y * (v * ψ x)) := by
  intro t n e ht hn hq hadm H _ ψ hker R hR x hxR hxc hx1 v hv hv2 hvR
  subst hn
  rcases ht with rfl | rfl
  · exact CFSG.ClassicalInvolution.ModelFacts.Orth15.psl3_model_involution_fund hp2 hadm ψ hker hR
      hxR hxc hx1 hv hv2 hvR
  · exact CFSG.ClassicalInvolution.ModelFacts.Orth15.psu3_model_involution_fund hp2 hq hadm ψ hker
      hR hxR hxc hx1 hv hv2 hvR

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}

theorem ChainCtx.rank3_involution (C : ChainCtx p f Ω z) (hr : C.D.rank C.i₁ = 3)
    {R : Subgroup (compModel C.D C.i₁).K}
    (hR : R ∈ fundamentalSubgroups (C.D.tag C.i₁) (compModel C.D C.i₁).D)
    {x : (compModel C.D C.i₁).K} (hxR : x ∈ R) (hxc : ∀ r ∈ R, x * r = r * x) (hx1 : x ≠ 1)
    {v : OddQuot z} (hv : v ∈ Subgroup.normalizer ((C.psi C.i₁).range : Set (OddQuot z)))
    (hv2 : v * v = 1) (hvR : ∀ r ∈ R, v * C.psi C.i₁ r = C.psi C.i₁ r * v) :
    (∀ y ∈ (C.psi C.i₁).range, v * y = y * v) ∨
      (∀ y ∈ (C.psi C.i₁).range, (v * C.psi C.i₁ x) * y = y * (v * C.psi C.i₁ x)) :=
  rank3_model_involution C.hp (C.D.tag C.i₁) (C.D.rank C.i₁) (C.D.exp C.i₁) C.tag₁ hr
    (by rw [C.exp_eq C.i₁ C.tag₁]; exact C.hq) (C.D.admissible C.i₁) (C.psi C.i₁)
    (C.psi_ker C.i₁) hR hxR hxc hx1 hv hv2 hvR

end Model3

section Central

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}

theorem ChainCtx.exists_central_lift (C : ChainCtx p f Ω z) {N : Subgroup G} {w : G}
    (hN : N ∈ tqMembers Ω z) (hw : IsClassicalMember p f N w) (j : Fin C.D.card)
    (hj : C.D.tag j = .PSL ∨ C.D.tag j = .PSU) {R : Subgroup (compModel C.D j).K}
    (hR : R ∈ fundamentalSubgroups (C.D.tag j) (compModel C.D j).D)
    (hmod : modOdd z (exactCore z N) = R.map (C.psi j)) :
    ∃ r ∈ R, (∀ s ∈ R, r * s = s * r) ∧ r ≠ 1 ∧
      oddQuotMk z ⟨w, C.involution_mem_centralizer hN hw⟩ = C.psi j r := by
  have hwE := C.involution_mem_exactCore hN hw
  have hwC := C.involution_mem_centralizer hN hw
  have hmem : oddQuotMk z ⟨w, hwC⟩ ∈ R.map (C.psi j) := hmod ▸ oddQuotMk_mem_modOdd hwE hwC
  obtain ⟨r, hrR, hr⟩ := hmem
  have hcw := isCentralInvolution_of_isClassicalMember hw
  have hcent : ∀ s ∈ R, C.psi j r * C.psi j s = C.psi j s * C.psi j r := by
    intro s hs
    have hsm : C.psi j s ∈ modOdd z (exactCore z N) := hmod ▸ ⟨s, hs, rfl⟩
    obtain ⟨k, hk, hks⟩ := hsm
    rw [hr, ← hks, ← map_mul, ← map_mul]
    exact congrArg (oddQuotMk z) (Subtype.ext (hcw.central _ (exactCore_le_left z N hk)))
  have hperf : Group.IsPerfect ↥R := Subgroup.isPerfect_iff.mpr (C.fund_perfect j hj hR)
  have hrc : ∀ s ∈ R, r * s = s * r := by
    have key : (⟨r, hrR⟩ : ↥R) ∈ Subgroup.center ↥R :=
      FrameVertex.mem_center_of_commutators_central fun t => by
        rw [Subgroup.mem_center_iff]
        intro u
        have h1 : C.psi j (r * (t : (compModel C.D j).K) * r⁻¹ *
            (t : (compModel C.D j).K)⁻¹) = 1 := by
          have := hcent t t.2
          rw [map_mul, map_mul, map_mul, map_inv, map_inv, this]
          group
        have h2 : r * (t : (compModel C.D j).K) * r⁻¹ * (t : (compModel C.D j).K)⁻¹ ∈
            Subgroup.center (compModel C.D j).K :=
          C.psi_ker j (MonoidHom.mem_ker.mpr h1)
        apply Subtype.ext
        have := Subgroup.mem_center_iff.mp h2 u
        simpa [commutatorElement_def] using this
    intro s hs
    have := Subgroup.mem_center_iff.mp key ⟨s, hs⟩
    exact congrArg Subtype.val this.symm
  refine ⟨r, hrR, hrc, fun hr1 => ?_, hr.symm⟩
  rw [hr1, map_one] at hr
  have h1 : (⟨w, hwC⟩ : ↥(Subgroup.centralizer ({z} : Set G))) = 1 :=
    eq_one_of_oddQuotMk_eq_one (Subtype.ext hcw.sq) hr.symm
  exact hcw.ne_one (congrArg Subtype.val h1)

end Central

section Vertex

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}

theorem not_movedByAll_rank3 (C : ChainCtx p f Ω z) (hr : C.D.rank C.i₁ = 3)
    (hBelow : CITBelowU p f (Nat.card G)) (hnc : ¬ ({z} : Set G) ⊆ Subgroup.center G)
    {B : Subgroup G} (hB : IsElemAbelian 2 B) (hzB : z ∈ B) {a b : G}
    (haB : a ∈ B) (hbB : b ∈ B) (ha1 : a ≠ 1) (haz : a ≠ z) (hb1 : b ≠ 1) (hbz : b ≠ z)
    (hba1 : b * a ≠ 1) (hbaz : b * a ≠ z) {M : Subgroup G} (hM : M ∈ tqMembers Ω z)
    (hMa : IsClassicalMember p f M a) (haK : a ∈ trivialOnQuot C.K)
    (hbM : b ∈ trivialOnQuot M) (j : Fin C.D.card) : ¬ MovedByAll B z (C.psi j).range := by
  have hz1 : z ≠ 1 := C.hKz.ne_one
  have hBC : B ≤ Subgroup.centralizer ({z} : Set G) := Lemma52Proof.le_centralizer_of_mem hB hzB
  have haC := hBC haB
  have hbC := hBC hbB
  have hbaB : b * a ∈ B := Subgroup.mul_mem _ hbB haB
  have hbaC := hBC hbaB
  have hKcl : IsClassicalMember p f C.K z := isClassicalMember_of_twin C.hΩ C.hK C.hKz
  have hbsq : b * b = 1 := by rw [← pow_two]; exact hB.2 b hbB
  intro hmov
  rcases C.eq_i₀_or_i₁ j with rfl | rfl
  · obtain ⟨y, hy, hne⟩ := hmov _ (oddQuotMk_mem_modOdd haB haC)
      (Lemma52Proof.oddQuotMk_not_mem_zpowers hB hzB hz1 haB ha1 haz haC)
    exact hne (C.centralizes_K haK haC y hy)
  · have hQ : CFSG.IsComponent (C.psi C.i₁).range := C.isComponent_range C.i₁
    have hBN := FrameVertex.modOdd_le_normalizer C.hp C.hq C.hΩ.conjInvariant C.hΩ.classical
      hBelow C.hc2 hnc hB hzB hz1 haB ha1 haz hM hMa hQ hmov
    obtain ⟨k, R, hR, hmod⟩ := C.exists_fund_of_mem hM
    rcases C.eq_i₀_or_i₁ k with rfl | rfl
    ·
      have hR' := C.fund_eq_top₀ hR
      have hmod' : modOdd z (exactCore z M) = modOdd z (exactCore z C.K) := by
        rw [← hmod, hR', Subgroup.map_top, C.modOdd_K_eq_range]
      have hU1 := C.isUniqueInvolution_modOdd hM hMa
      have hU2 := C.isUniqueInvolution_modOdd ⟨C.hK, C.hKtq⟩ hKcl
      rw [hmod'] at hU1
      have heq := hU1.eq hU2
      apply Lemma52Proof.oddQuotMk_not_mem_zpowers hB hzB hz1 haB ha1 haz haC
      rw [heq]
      exact oddQuotMk_mem_modOdd (Subgroup.mem_zpowers z) ChainLift.hzC
    · obtain ⟨r, hrR, hrc, hr1, hrbar⟩ := C.exists_central_lift hM hMa C.i₁ C.tag₁ hR hmod.symm
      have hquasi : CFSG.Open.IsQuasisimple ↥(modOdd z (exactCore z M)) := by
        rw [← hmod]
        exact isQuasisimple_map_of_ker_le_center _ (C.psi_ker C.i₁)
          (fundQuasisimple_core C.hp (C.D.isFundTag C.i₁) (C.D.admissible C.i₁)
            (C.four_le C.i₁ C.tag₁) R hR)
      have hcen := oddQuotMk_centralizes_modOdd_exactCore hMa C.hc2 hM.2 hbM hbC hquasi
      have hvR : ∀ s ∈ R, oddQuotMk z ⟨b, hbC⟩ * C.psi C.i₁ s =
          C.psi C.i₁ s * oddQuotMk z ⟨b, hbC⟩ := by
        intro s hs
        apply hcen
        rw [← hmod]
        exact ⟨s, hs, rfl⟩
      have hbv2 : oddQuotMk z ⟨b, hbC⟩ * oddQuotMk z ⟨b, hbC⟩ = 1 := by
        rw [← map_mul]
        have : (⟨b, hbC⟩ : ↥(Subgroup.centralizer ({z} : Set G))) * ⟨b, hbC⟩ = 1 :=
          Subtype.ext hbsq
        rw [this, map_one]
      have hbmem := oddQuotMk_mem_modOdd hbB hbC
      rcases C.rank3_involution hr hR hrR hrc hr1 (hBN hbmem) hbv2 hvR with h | h
      · obtain ⟨y, hy, hne⟩ := hmov _ hbmem
          (Lemma52Proof.oddQuotMk_not_mem_zpowers hB hzB hz1 hbB hb1 hbz hbC)
        exact hne (h y hy)
      · rw [← hrbar] at h
        have e : oddQuotMk z ⟨b, hbC⟩ * oddQuotMk z ⟨a, haC⟩ = oddQuotMk z ⟨b * a, hbaC⟩ :=
          (map_mul (oddQuotMk z) _ _).symm
        rw [e] at h
        obtain ⟨y, hy, hne⟩ := hmov _ (oddQuotMk_mem_modOdd hbaB hbaC)
          (Lemma52Proof.oddQuotMk_not_mem_zpowers hB hzB hz1 hbaB hba1 hbaz hbaC)
        exact hne (h y hy)

end Vertex

section VertexT

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K J K' : Subgroup G} {z t z' : G}

theorem chainFrame_rank3_conj (hs : ChainFrameSetting p f Ω K J K' z t z')
    (hr3 : ChainShapeRank p f 3 Ω z) :
    ∃ (C : ChainCtx p f Ω z) (g : G), g * t * g⁻¹ = z ∧
      IsElemAbelian 2 (conjSub g (Subgroup.closure ({z, t, z'} : Set G))) ∧
      Nat.card (conjSub g (Subgroup.closure ({z, t, z'} : Set G))) = 8 ∧
      z ∈ conjSub g (Subgroup.closure ({z, t, z'} : Set G)) ∧
      (∃ a ∈ conjSub g (Subgroup.closure ({z, t, z'} : Set G)), a ≠ 1 ∧ a ≠ z ∧
        ∃ M ∈ tqMembers Ω z, IsClassicalMember p f M a) ∧
      ∀ j : Fin C.D.card,
        ¬ MovedByAll (conjSub g (Subgroup.closure ({z, t, z'} : Set G))) z (C.psi j).range := by
  have hp := hs.odd
  have hq := hs.five
  have hΩ := hs.hyp
  have hd := hs.frame
  obtain ⟨D, hcard, i₀, i₁, hne, ht₀, hr₀, ht₁, hr₁⟩ := hr3
  have hpairD : ChainPair (fundamentalSubgroups (D.tag i₁) (compModel D i₁).D) :=
    chainPair_model hp (D.tag i₁) (D.rank i₁) (D.exp i₁) ht₁ (by omega) (D.admissible i₁)
  let C : ChainCtx p f Ω z :=
    { K := K, hK := hd.mem, hKz := hd.hz, hΩ := hΩ, hp := hp, hq := hq, D := D,
      card_eq := hcard, i₀ := i₀, i₁ := i₁, ne := hne, tag₁ := ht₁, tag₀ := ht₀, rank₀ := hr₀,
      pair := hpairD }
  obtain ⟨g₀, hg₀⟩ := hs.trans J hd.memJ
  have hKcl : IsClassicalMember p f K z := isClassicalMember_of_twin hΩ hd.mem hd.hz
  have hgz : g₀ * z * g₀⁻¹ = t := by
    have h1 : IsUniqueInvolution (conjSub g₀ K) (g₀ * z * g₀⁻¹) :=
      ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq (hKcl.conj g₀)
    rw [hg₀] at h1
    exact h1.eq hd.ht
  have hzt : g₀⁻¹ * t * g₀⁻¹⁻¹ = z := by rw [← hgz]; group
  have hzB : z ∈ Subgroup.closure ({z, t, z'} : Set G) := Subgroup.subset_closure (by simp)
  have htB : t ∈ Subgroup.closure ({z, t, z'} : Set G) := Subgroup.subset_closure (by simp)
  have hz'B : z' ∈ Subgroup.closure ({z, t, z'} : Set G) := Subgroup.subset_closure (by simp)
  have hB := hd.isElemAbelian hp hΩ
  have hnc : ¬ ({z} : Set G) ⊆ Subgroup.center G :=
    Balance.not_subset_center_of_ne_one hs.nonabelian hd.hz.ne_one
  have hinj : ∀ x y : G, g₀⁻¹ * x * g₀⁻¹⁻¹ = g₀⁻¹ * y * g₀⁻¹⁻¹ → x = y := fun x y h =>
    mul_left_cancel (mul_right_cancel h)
  have htz := hd.t_ne_z hp hq hΩ
  have hz'z := hd.z'_ne_z hp hq hΩ
  have hz't := hd.z'_ne_t hΩ
  have hz'zt := hd.z'_ne_zt hp hq hΩ
  have hztc := hd.comm_zt hp hΩ
  have hzsq := hd.hz.sq
  have hmemM : conjSub g₀⁻¹ K ∈ tqMembers Ω z := by
    refine ⟨hΩ.conjInvariant g₀⁻¹ K hd.mem, ?_⟩
    have h := trivialOnQuot_conjSub (hd.tq_t hp hq hΩ) g₀⁻¹
    rwa [hzt] at h
  have haK : g₀⁻¹ * z * g₀⁻¹⁻¹ ∈ trivialOnQuot C.K := by
    have h := trivialOnQuot_conjSub (hd.tq_z_J hp hq hΩ) g₀⁻¹
    rwa [← hg₀, conjSub_inv_conjSub] at h
  have hbM : g₀⁻¹ * z' * g₀⁻¹⁻¹ ∈ trivialOnQuot (conjSub g₀⁻¹ K) :=
    trivialOnQuot_conjSub (hd.tq_z' hp hq hΩ) g₀⁻¹
  have hzB' : z ∈ conjSub g₀⁻¹ (Subgroup.closure ({z, t, z'} : Set G)) := by
    have := conj_mem_conjSub (n := g₀⁻¹) htB
    rwa [hzt] at this
  have hB8 : Nat.card (conjSub g₀⁻¹ (Subgroup.closure ({z, t, z'} : Set G))) = 8 := by
    rw [show Nat.card (conjSub g₀⁻¹ (Subgroup.closure ({z, t, z'} : Set G))) =
      Nat.card (Subgroup.closure ({z, t, z'} : Set G)) from
      Subgroup.card_map_of_injective (MulAut.conj g₀⁻¹).injective]
    exact hd.natCard_eight hp hq hΩ
  have hba : (g₀⁻¹ * z' * g₀⁻¹⁻¹) * (g₀⁻¹ * z * g₀⁻¹⁻¹) = g₀⁻¹ * (z' * z) * g₀⁻¹⁻¹ := by
    group
  have ha1 : g₀⁻¹ * z * g₀⁻¹⁻¹ ≠ 1 := fun h => hd.hz.ne_one (hinj z 1 (by rw [h]; group))
  have haz : g₀⁻¹ * z * g₀⁻¹⁻¹ ≠ z := fun h => htz (hinj t z (by rw [hzt]; exact h.symm))
  have hb1 : g₀⁻¹ * z' * g₀⁻¹⁻¹ ≠ 1 := fun h => hd.hz'.ne_one (hinj z' 1 (by rw [h]; group))
  have hbz : g₀⁻¹ * z' * g₀⁻¹⁻¹ ≠ z := fun h => hz't (hinj z' t (by rw [hzt]; exact h))
  have hba1 : (g₀⁻¹ * z' * g₀⁻¹⁻¹) * (g₀⁻¹ * z * g₀⁻¹⁻¹) ≠ 1 := by
    intro h
    have h1 : z' * z = 1 := hinj (z' * z) 1 (by rw [← hba, h]; group)
    apply hz'z
    calc z' = z' * (z * z) := by rw [hzsq, mul_one]
      _ = (z' * z) * z := by group
      _ = z := by rw [h1, one_mul]
  have hbaz : (g₀⁻¹ * z' * g₀⁻¹⁻¹) * (g₀⁻¹ * z * g₀⁻¹⁻¹) ≠ z := by
    intro h
    have h1 : z' * z = t := hinj (z' * z) t (by rw [← hba, h, hzt])
    apply hz'zt
    calc z' = z' * (z * z) := by rw [hzsq, mul_one]
      _ = (z' * z) * z := by group
      _ = t * z := by rw [h1]
      _ = z * t := hztc.symm
  refine ⟨C, g₀⁻¹, hzt, isElemAbelian_conjSub hB g₀⁻¹, hB8, hzB',
    ⟨g₀⁻¹ * z * g₀⁻¹⁻¹, conj_mem_conjSub hzB, ha1, haz, conjSub g₀⁻¹ K, hmemM,
      hKcl.conj g₀⁻¹⟩, fun j => ?_⟩
  exact not_movedByAll_rank3 C hr₁ hs.below hnc (isElemAbelian_conjSub hB g₀⁻¹) hzB'
    (conj_mem_conjSub hzB) (conj_mem_conjSub hz'B) ha1 haz hb1 hbz hba1 hbaz hmemM
    (hKcl.conj g₀⁻¹) haK hbM j

theorem chainFrameHyp51t_rank3 (hs : ChainFrameSetting p f Ω K J K' z t z')
    (hr3 : ChainShapeRank p f 3 Ω z) : Hyp51At (Subgroup.closure ({z, t, z'} : Set G)) t := by
  obtain ⟨C, g, hgt, hB, hB8, hzB, ⟨a, haB, ha1, haz, M, hM, hMa⟩, hnot⟩ :=
    chainFrame_rank3_conj hs hr3
  have hnc : ¬ ({z} : Set G) ⊆ Subgroup.center G :=
    Balance.not_subset_center_of_ne_one hs.nonabelian hs.frame.hz.ne_one
  have hz : Hyp51At (conjSub g (Subgroup.closure ({z, t, z'} : Set G))) z :=
    FrameVertex.hyp51At_of_system C.hp C.hq C.hΩ.conjInvariant C.hΩ.classical hs.below C.hc2 hnc
      hB hB8 hzB C.hKz.ne_one haB ha1 haz hM hMa
      ⟨C.D, fun j hmov => absurd hmov (hnot j)⟩
  have := (hyp51At_conj g t (Subgroup.closure ({z, t, z'} : Set G))).mp
  rw [hgt] at this
  exact this hz

end VertexT

end CFSG.ClassicalInvolution.Asc77
