module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinT
import CFSG.ClassicalInvolution.Asc77.AscP1SevenOmega
import CFSG.ClassicalInvolution.Asc77.WP3FrameChain
import CFSG.ClassicalInvolution.Asc77.AscE187Img
public import CFSG.ClassicalInvolution.Asc77.AscT7AHyp51Cases

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Disconnected
open CFSG.Open (IsElemAbelian classicalInvolutionOddCore)
open scoped commutatorElement

namespace FrameVertex

section Variant

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem hyp51At_of_witness_alpha' (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : ConjInvariant Ω)
    (hcls : ∀ K ∈ Ω, ∃ z, IsClassicalMember p f K z) (hBelow : CITBelowU p f (Nat.card G))
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) (hnc : ¬ ({c} : Set G) ⊆ Subgroup.center G)
    {B : Subgroup G} (hB : IsElemAbelian 2 B) (hcB : c ∈ B) (hc1 : c ≠ 1) {b : G} (hbB : b ∈ B)
    (hb1 : b ≠ 1) (hbc : b ≠ c) {M : Subgroup G} (hM : M ∈ tqMembers Ω c)
    (hMb : IsClassicalMember p f M b)
    (hα : ∀ (D : LocalLieSystemAt p f (exactFamily Ω c) c) (j : Fin D.card),
      modOdd c (exactCore c M) ≤
          (secComponentHom (normalizesLayer_exactFamily hΩ) D j).range →
        MovedByAll B c (secComponentHom (normalizesLayer_exactFamily hΩ) D j).range →
          CFSG.IsComponent (secComponentHom (normalizesLayer_exactFamily hΩ) D j).range →
            alphaOf (inducedImage (secComponentHom (normalizesLayer_exactFamily hΩ) D j).range
              (modOdd c B)) = ⊥) :
    Hyp51At B c := by
  refine ⟨uniq_of_witness hp2 hq hΩ hcls hBelow hc2 hnc hB hcB hc1 hbB hb1 hbc hM hMb, ?_⟩
  intro L hL hmov
  have hne : (tqMembers Ω c).Nonempty := ⟨M, hM⟩
  obtain ⟨Dsys⟩ := lieSystemAt_exactFamily hΩ hcls hc2 hBelow hnc hne
  obtain ⟨D', hD'Q, -⟩ := lieDecomposition_exactFamily_comp hp2
    CFSG.ClassicalInvolution.ModelFacts.modelClauseZero fundamentalWholeA1 hq hΩ hcls hc2 hne Dsys
  obtain ⟨j₀, hMj₀, hj₀⟩ := movedComponent_eq' hΩ hc2 hB hcB hc1 hbB hb1 hbc hM hMb D'
  obtain ⟨j, hj⟩ := hD'Q j₀
  have hLeq : L = (secComponentHom (normalizesLayer_exactFamily hΩ) Dsys j).range :=
    (hj₀ L hL hmov).trans hj.symm
  subst hLeq
  exact hα Dsys j (hMj₀.trans hj.symm.le) hmov hL

end Variant

end FrameVertex


section UCoset

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' J : Subgroup G} {z u t c : G}

@[expose] def UCoset (z u t c : G) : Prop := c = u ∨ c = u * z ∨ c = u * t ∨ c = u * t * z

omit [Finite G] in
theorem UCoset.mem_closure (hc : UCoset z u t c) : c ∈ Subgroup.closure ({z, u, t} : Set G) := by
  have hz : z ∈ Subgroup.closure ({z, u, t} : Set G) := Subgroup.subset_closure (by simp)
  have hu : u ∈ Subgroup.closure ({z, u, t} : Set G) := Subgroup.subset_closure (by simp)
  have ht : t ∈ Subgroup.closure ({z, u, t} : Set G) := Subgroup.subset_closure (by simp)
  rcases hc with hc | hc | hc | hc <;> rw [hc]
  · exact hu
  · exact Subgroup.mul_mem _ hu hz
  · exact Subgroup.mul_mem _ hu ht
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hu ht) hz

theorem TwinFrameSettingCore.u_not_mem_closure (hs : TwinFrameSettingCore p f Ω K K' J z u t) :
    u ∉ Subgroup.closure ({z, t} : Set G) := by
  intro hu
  have hd := hs.frame
  have hzt : z * t = t * z := hd.comm_zt hs.odd hs.hyp
  have hz2 : z * z = 1 := hd.hz.sq
  have ht2 : t * t = 1 := hd.ht.sq
  have hnt := hd.t_not_mem_closure hs.odd hs.five hs.hyp
  have hzcl : z ∈ Subgroup.closure ({z, u} : Set G) := Subgroup.subset_closure (by simp)
  have hucl : u ∈ Subgroup.closure ({z, u} : Set G) := Subgroup.subset_closure (by simp)
  rcases ChainFrame.mem_closure_four hz2 ht2 hzt hu with h | h | h | h
  · exact hd.hu1 h
  · exact hd.huz h
  · exact hnt (h ▸ hucl)
  · apply hnt
    have : t = z * u := by
      rw [h, ← mul_assoc, hz2, one_mul]
    rw [this]
    exact Subgroup.mul_mem _ hzcl hucl

theorem TwinFrameSetting.u_not_mem_closure (hs : TwinFrameSetting p f Ω K K' J z u t) :
    u ∉ Subgroup.closure ({z, t} : Set G) :=
  hs.toCore.u_not_mem_closure

end UCoset


section UCosetFacts

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' J : Subgroup G} {z u t c : G}

theorem TwinFrameSettingCore.UCoset_exists_w (hs : TwinFrameSettingCore p f Ω K K' J z u t)
    (hc : UCoset z u t c) :
    ∃ w : G, (w = 1 ∨ w = z ∨ w = t ∨ w = t * z) ∧ c = u * w ∧ u = c * w := by
  have hd := hs.frame
  have hzt : z * t = t * z := hd.comm_zt hs.odd hs.hyp
  have hz2 : z * z = 1 := hd.hz.sq
  have ht2 : t * t = 1 := hd.ht.sq
  rcases hc with hc | hc | hc | hc
  · exact ⟨1, Or.inl rfl, by rw [hc, mul_one], by rw [hc, mul_one]⟩
  · refine ⟨z, Or.inr (Or.inl rfl), hc, ?_⟩
    rw [hc, mul_assoc, hz2, mul_one]
  · refine ⟨t, Or.inr (Or.inr (Or.inl rfl)), hc, ?_⟩
    rw [hc, mul_assoc, ht2, mul_one]
  · refine ⟨t * z, Or.inr (Or.inr (Or.inr rfl)), by rw [hc, mul_assoc], ?_⟩
    have h1 : (t * z) * (t * z) = 1 := mul_involution_of_commute ht2 hz2 hzt.symm
    rw [hc]
    calc u = u * ((t * z) * (t * z)) := by rw [h1, mul_one]
      _ = u * t * z * (t * z) := by group

theorem TwinFrameSetting.UCoset_exists_w (hs : TwinFrameSetting p f Ω K K' J z u t)
    (hc : UCoset z u t c) :
    ∃ w : G, (w = 1 ∨ w = z ∨ w = t ∨ w = t * z) ∧ c = u * w ∧ u = c * w :=
  hs.toCore.UCoset_exists_w hc

theorem TwinFrameSettingCore.uc_not_mem_closure (hs : TwinFrameSettingCore p f Ω K K' J z u t)
    (hc : UCoset z u t c) : c ∉ Subgroup.closure ({z, t} : Set G) := by
  intro hcl
  apply hs.u_not_mem_closure
  obtain ⟨w, hw, -, huw⟩ := hs.UCoset_exists_w hc
  have hz : z ∈ Subgroup.closure ({z, t} : Set G) := Subgroup.subset_closure (by simp)
  have ht : t ∈ Subgroup.closure ({z, t} : Set G) := Subgroup.subset_closure (by simp)
  have hwcl : w ∈ Subgroup.closure ({z, t} : Set G) := by
    rcases hw with hw | hw | hw | hw <;> rw [hw]
    · exact Subgroup.one_mem _
    · exact hz
    · exact ht
    · exact Subgroup.mul_mem _ ht hz
  rw [huw]
  exact Subgroup.mul_mem _ hcl hwcl

theorem TwinFrameSetting.uc_not_mem_closure (hs : TwinFrameSetting p f Ω K K' J z u t)
    (hc : UCoset z u t c) : c ∉ Subgroup.closure ({z, t} : Set G) := by
  intro hcl
  apply hs.u_not_mem_closure
  obtain ⟨w, hw, -, huw⟩ := hs.UCoset_exists_w hc
  have hz : z ∈ Subgroup.closure ({z, t} : Set G) := Subgroup.subset_closure (by simp)
  have ht : t ∈ Subgroup.closure ({z, t} : Set G) := Subgroup.subset_closure (by simp)
  have hwcl : w ∈ Subgroup.closure ({z, t} : Set G) := by
    rcases hw with hw | hw | hw | hw <;> rw [hw]
    · exact Subgroup.one_mem _
    · exact hz
    · exact ht
    · exact Subgroup.mul_mem _ ht hz
  rw [huw]
  exact Subgroup.mul_mem _ hcl hwcl

theorem TwinFrameSettingCore.uc_ne_one (hs : TwinFrameSettingCore p f Ω K K' J z u t)
    (hc : UCoset z u t c) : c ≠ 1 := fun h =>
  hs.uc_not_mem_closure hc (h ▸ Subgroup.one_mem _)

theorem TwinFrameSetting.uc_ne_one (hs : TwinFrameSetting p f Ω K K' J z u t)
    (hc : UCoset z u t c) : c ≠ 1 := fun h =>
  hs.uc_not_mem_closure hc (h ▸ Subgroup.one_mem _)

theorem TwinFrameSettingCore.t_ne_uc (hs : TwinFrameSettingCore p f Ω K K' J z u t)
    (hc : UCoset z u t c) : t ≠ c := fun h =>
  hs.uc_not_mem_closure hc (h ▸ Subgroup.subset_closure (by simp))

theorem TwinFrameSetting.t_ne_uc (hs : TwinFrameSetting p f Ω K K' J z u t)
    (hc : UCoset z u t c) : t ≠ c := fun h =>
  hs.uc_not_mem_closure hc (h ▸ Subgroup.subset_closure (by simp))

theorem TwinFrameSettingCore.z_ne_uc (hs : TwinFrameSettingCore p f Ω K K' J z u t)
    (hc : UCoset z u t c) : z ≠ c := fun h =>
  hs.uc_not_mem_closure hc (h ▸ Subgroup.subset_closure (by simp))

theorem TwinFrameSetting.z_ne_uc (hs : TwinFrameSetting p f Ω K K' J z u t)
    (hc : UCoset z u t c) : z ≠ c := fun h =>
  hs.uc_not_mem_closure hc (h ▸ Subgroup.subset_closure (by simp))

theorem TwinFrameSettingCore.zt_ne_uc (hs : TwinFrameSettingCore p f Ω K K' J z u t)
    (hc : UCoset z u t c) : z * t ≠ c := fun h =>
  hs.uc_not_mem_closure hc (h ▸ Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
    (Subgroup.subset_closure (by simp)))

theorem TwinFrameSetting.zt_ne_uc (hs : TwinFrameSetting p f Ω K K' J z u t)
    (hc : UCoset z u t c) : z * t ≠ c := fun h =>
  hs.uc_not_mem_closure hc (h ▸ Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
    (Subgroup.subset_closure (by simp)))

theorem TwinFrameSettingCore.zt_ne_one (hs : TwinFrameSettingCore p f Ω K K' J z u t) :
    z * t ≠ 1 := by
  intro h
  apply hs.frame.t_ne_z
  exact (eq_inv_of_mul_eq_one_right h).trans (inv_eq_of_mul_eq_one_right hs.frame.hz.sq)

theorem TwinFrameSetting.zt_ne_one (hs : TwinFrameSetting p f Ω K K' J z u t) : z * t ≠ 1 :=
  hs.toCore.zt_ne_one

end UCosetFacts


section Members

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' J : Subgroup G} {z u t c : G}

theorem TwinFrameSettingCore.exists_twin_J (hs : TwinFrameSettingCore p f Ω K K' J z u t) :
    ∃ J' : Subgroup G, J' ∈ twinSet Ω J ∧ J' ≠ J := by
  have hd := hs.frame
  have hK'Ω : K' ∈ Ω := hd.hK'.1
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hd.hz hd.hK'
  obtain ⟨g, hg⟩ := hs.trans J hd.hJ.1
  have h1 := hzK'.conj g
  have h2 : IsUniqueInvolution J (g * z * g⁻¹) := by
    have := hd.hz.conj g
    rwa [hg] at this
  have hgz : g * z * g⁻¹ = t := h2.eq hd.ht ▸ rfl
  refine ⟨conjSub g K', ⟨hs.hyp.conjInvariant g K' hK'Ω, t, hd.ht, ?_⟩, ?_⟩
  · rwa [hgz] at h1
  · intro h
    apply hd.hne
    rw [← hg] at h
    have := congrArg (conjSub g⁻¹) h
    rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at this

theorem TwinFrameSetting.exists_twin_J (hs : TwinFrameSetting p f Ω K K' J z u t) :
    ∃ J' : Subgroup G, J' ∈ twinSet Ω J ∧ J' ≠ J :=
  hs.toCore.exists_twin_J

theorem le_trivialOnQuot_of_commutator_le {M V : Subgroup G} (h : ⁅V, M⁆ ≤ oddCoreOf M) :
    V ≤ trivialOnQuot M := by
  have key : ∀ v ∈ V, ∀ m ∈ M, v * m * v⁻¹ ∈ M := by
    intro v hv m hm
    have h1 : ⁅v, m⁆ ∈ oddCoreOf M := h (Subgroup.commutator_mem_commutator hv hm)
    have e : v * m * v⁻¹ = ⁅v, m⁆ * m := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact M.mul_mem (oddCoreIn_le M h1) hm
  intro v hv
  refine ⟨?_, fun x hx => h (Subgroup.commutator_mem_commutator hv hx)⟩
  rw [Subgroup.mem_normalizer_iff]
  intro m
  refine ⟨fun hm => key v hv m hm, fun hm => ?_⟩
  have := key v⁻¹ (V.inv_mem hv) _ hm
  have e : v⁻¹ * (v * m * v⁻¹) * v⁻¹⁻¹ = m := by group
  rwa [e] at this

theorem sylow_le_trivialOnQuot (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {N M V : Subgroup G} {w : G} (hN : N ∈ Ω) (hM : M ∈ Ω) (hw : IsUniqueInvolution N w)
    (hMt : IsUniqueInvolution M t) (hwt : w ≠ t) (hV : IsSylow2In V N)
    (hVt : ∀ r ∈ V, r * t = t * r) : V ≤ trivialOnQuot M := by
  have hMN : M ≠ N := by
    rintro rfl
    exact hwt (hw.eq hMt)
  exact le_trivialOnQuot_of_commutator_le (Thompson.comm_le_oddCore_of_isSylow2In (l6_2 p f) hp hq
    hΩ hM hN hMN hMt hw hV fun r hr => Subgroup.mem_centralizer_singleton_iff.mpr (hVt r hr))

theorem TwinFrameSettingCore.tq_uc (hs : TwinFrameSettingCore p f Ω K K' J z u t)
    (hc : UCoset z u t c) {M : Subgroup G} (hM : M ∈ Ω) (hMt : IsUniqueInvolution M t) :
    c ∈ trivialOnQuot M := by
  have hd := hs.frame
  obtain ⟨R, R', hR, hR', -, hRt, hR't, x, hx, y, hy, hx2, hy2, hxy⟩ := hs.exists_sylow_frame
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hd.hz hd.hK'
  have hRM := sylow_le_trivialOnQuot hs.odd hs.five hs.hyp hd.mem hM hd.hz hMt hd.t_ne_z.symm hR hRt
  have hR'M := sylow_le_trivialOnQuot hs.odd hs.five hs.hyp hd.hK'.1 hM hzK' hMt hd.t_ne_z.symm
    hR' hR't
  have htM : t ∈ trivialOnQuot M := trivialOnQuot_of_isUniqueInvolution hs.odd hs.five hs.hyp hM hMt
  have hxM : x ∈ trivialOnQuot M := hRM hx
  have hyM : y ∈ trivialOnQuot M := hR'M hy
  have hzM : z ∈ trivialOnQuot M := by
    rw [← hx2]
    exact Subgroup.mul_mem _ hxM hxM
  have huM : u ∈ trivialOnQuot M := by
    rw [← hxy]
    exact Subgroup.mul_mem _ hxM hyM
  rcases hc with hc | hc | hc | hc <;> rw [hc]
  · exact huM
  · exact Subgroup.mul_mem _ huM hzM
  · exact Subgroup.mul_mem _ huM htM
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ huM htM) hzM

theorem TwinFrameSetting.tq_uc (hs : TwinFrameSetting p f Ω K K' J z u t) (hc : UCoset z u t c)
    {M : Subgroup G} (hM : M ∈ Ω) (hMt : IsUniqueInvolution M t) : c ∈ trivialOnQuot M := by
  have hd := hs.frame
  obtain ⟨R, R', hR, hR', -, hRt, hR't, x, hx, y, hy, hx2, hy2, hxy⟩ := hs.exists_sylow_frame
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hd.hz hd.hK'
  have hRM := sylow_le_trivialOnQuot hs.odd hs.five hs.hyp hd.mem hM hd.hz hMt hd.t_ne_z.symm hR hRt
  have hR'M := sylow_le_trivialOnQuot hs.odd hs.five hs.hyp hd.hK'.1 hM hzK' hMt hd.t_ne_z.symm
    hR' hR't
  have htM : t ∈ trivialOnQuot M := trivialOnQuot_of_isUniqueInvolution hs.odd hs.five hs.hyp hM hMt
  have hxM : x ∈ trivialOnQuot M := hRM hx
  have hyM : y ∈ trivialOnQuot M := hR'M hy
  have hzM : z ∈ trivialOnQuot M := by
    rw [← hx2]
    exact Subgroup.mul_mem _ hxM hxM
  have huM : u ∈ trivialOnQuot M := by
    rw [← hxy]
    exact Subgroup.mul_mem _ hxM hyM
  rcases hc with hc | hc | hc | hc <;> rw [hc]
  · exact huM
  · exact Subgroup.mul_mem _ huM hzM
  · exact Subgroup.mul_mem _ huM htM
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ huM htM) hzM

end Members


section Normalizer

theorem mem_normalizer_of_commute_noncentral {X : Type} [Group X] [Finite X] {L : Subgroup X}
    (hL : CFSG.IsComponent L) {a : X} (haL : a ∈ L) (hnc : ¬ ∀ y ∈ L, a * y = y * a) {g : X}
    (hg : g * a = a * g) : g ∈ Subgroup.normalizer (L : Set X) := by
  have hL' : CFSG.IsComponent (conjSub g L) :=
    (isComponent_map_equiv_iff (MulAut.conj g) L).mpr hL
  rcases CFSG.LocalCores.distinct_components_commute hL hL' with h | h
  · exact mem_normalizer_iff_conjSub_eq.mpr h.symm
  · exfalso
    apply hnc
    intro y hy
    have haL' : a ∈ conjSub g L := by
      have := conj_mem_conjSub (n := g) haL
      have e : g * a * g⁻¹ = a := by rw [hg]; group
      rwa [e] at this
    have h1 : ⁅y, a⁆ ∈ ⁅L, conjSub g L⁆ := Subgroup.commutator_mem_commutator hy haL'
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm

end Normalizer


section Vertex

variable {p f : ℕ} [Fact p.Prime]

theorem TwinShape.not_A1 {t : StatedLieTag} {n : ℕ} (h : TwinShape t n) :
    ¬ (t = .PSL ∧ n = 2) := by
  rintro ⟨rfl, rfl⟩
  rcases h with h | h | h | h | h | h <;> simp at h

theorem TwinFrameSettingCore.hyp51At_u_of {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    {Ω : Set (Subgroup G)} {K K' J : Subgroup G} {z u t c : G}
    (hs : TwinFrameSettingCore p f Ω K K' J z u t) (hc : UCoset z u t c)
    (hv : ∀ J' : Subgroup G, J' ∈ tqMembers Ω c → IsClassicalMember p f J' t → J' ≠ J →
      ∀ (D : LocalLieSystemAt p f (exactFamily Ω c) c) (j : Fin D.card),
      modOdd c (exactCore c J) ≤
        (secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j).range →
      modOdd c (exactCore c J') ≤
        (secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j).range →
      MovedByAll (Subgroup.closure ({z, u, t} : Set G)) c
        (secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j).range →
      ∃ (htC : t ∈ Subgroup.centralizer ({c} : Set G)) (R R' : Subgroup (compModel D j).K)
        (x x' : (compModel D j).K),
        TwinPairOn (D.tag j) (compModel D j)
          (secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j) R R' x x' ∧
        R.map (secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j) =
          modOdd c (exactCore c J) ∧
        R'.map (secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j) =
          modOdd c (exactCore c J') ∧
        secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j x =
          oddQuotMk c ⟨t, htC⟩ ∧
        ¬ (D.tag j = .PSL ∧ D.rank j = 2) ∧ D.exp j = f ∧
        TwinOuterAlpha p (D.exp j) (D.tag j) (D.rank j)) :
    Hyp51At (Subgroup.closure ({z, u, t} : Set G)) c := by
  have hp : p ≠ 2 := hs.odd
  have hq : 5 ≤ p ^ f := hs.five
  have hΩ := hs.hyp
  have hd := hs.frame
  have hK : K ∈ Ω := hd.mem
  have hz := hd.hz
  have hcK : IsClassicalMember p f K z := isClassicalMember_of_twin hΩ hK hz
  have hBab := twinFrame_isElemAbelian hp hΩ hd
  have hzB : z ∈ Subgroup.closure ({z, u, t} : Set G) := Subgroup.subset_closure (by simp)
  have huB : u ∈ Subgroup.closure ({z, u, t} : Set G) := Subgroup.subset_closure (by simp)
  have htB : t ∈ Subgroup.closure ({z, u, t} : Set G) := Subgroup.subset_closure (by simp)
  have hcB : c ∈ Subgroup.closure ({z, u, t} : Set G) := hc.mem_closure
  have hc1 : c ≠ 1 := hs.uc_ne_one hc
  have htc : t ≠ c := hs.t_ne_uc hc
  have hzc : z ≠ c := hs.z_ne_uc hc
  have hztc : z * t ≠ c := hs.zt_ne_uc hc
  have hcc : c * c = 1 := Lemma52Proof.mul_self_eq_one_of_mem hBab hcB
  have hc2 : IsPGroup 2 (Subgroup.zpowers c) := isPGroup_zpowers_of_sq_eq_one hcc
  have hnonab : ∃ x y : G, x * y ≠ y * x := exists_noncomm_of_isClassicalMember hcK
  have hnc : ¬ ({c} : Set G) ⊆ Subgroup.center G :=
    Balance.not_subset_center_of_ne_one hnonab hc1
  obtain ⟨J', hJ'tw, hJ'ne⟩ := hs.exists_twin_J
  have hJΩ : J ∈ Ω := hd.hJ.1
  have hJ'Ω : J' ∈ Ω := hJ'tw.1
  have hJt : IsUniqueInvolution J t := hd.ht
  have hJ't : IsUniqueInvolution J' t := by
    obtain ⟨t', hJt', hJ't'⟩ := hJ'tw.2
    have : t' = t := hJt'.eq hJt
    rwa [this] at hJ't'
  have hcJ : IsClassicalMember p f J t := isClassicalMember_of_twin hΩ hJΩ hJt
  have hcJ' : IsClassicalMember p f J' t := isClassicalMember_of_twin hΩ hJ'Ω hJ't
  have hMJ : J ∈ tqMembers Ω c := ⟨hJΩ, hs.tq_uc hc hJΩ hJt⟩
  have hMJ' : J' ∈ tqMembers Ω c := ⟨hJ'Ω, hs.tq_uc hc hJ'Ω hJ't⟩
  refine FrameVertex.hyp51At_of_witness_alpha' hp hq hΩ.conjInvariant hΩ.classical hs.below hc2
    hnc hBab hcB hc1 htB hJt.ne_one htc hMJ hcJ ?_
  intro D j hMj hmov hLcomp
  have ht1 : t ≠ 1 := hJt.ne_one
  have hz1 : z ≠ 1 := hz.ne_one
  have hM'j := vertexTwin_mem hΩ hc2 hBab hcB hc1 htB ht1 htc hMJ hMJ' hcJ' D j hmov
  obtain ⟨htC, R, R', x₁, x₁', hpair, hRM, hR'M, hψx₁, hnA1, hexp, hTO⟩ :=
    hv J' hMJ' hcJ' hJ'ne D j hMj hM'j hmov
  have hq' : 5 ≤ p ^ D.exp j := by rw [hexp]; exact hq
  set ψ := secComponentHom (normalizesLayer_exactFamily hΩ.conjInvariant) D j with hψdef
  have hker := secComponentHom_ker_le_center (normalizesLayer_exactFamily hΩ.conjInvariant) D j
  have hzC : z ∈ Subgroup.centralizer ({c} : Set G) :=
    Lemma52Proof.le_centralizer_of_mem hBab hcB hzB
  obtain ⟨RK, RK', hRK, hRK', hcommK, hRKt, hRK't, x, hx, y, hy, hx2, hy2, hxy⟩ :=
    hs.exists_sylow_frame
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hd.hK'
  have hKz : K ≤ Subgroup.centralizer ({z} : Set G) := isSubnormal_le hcK.subnormal
  have hxz : x * z = z * x := Subgroup.mem_centralizer_singleton_iff.mp (hKz (hRK.1 hx))
  have hxt : x * t = t * x := hRKt x hx
  have hxy_c : x * y = y * x := hcommK x hx y hy
  have hxu : x * u = u * x := by
    rw [← hxy]
    calc x * (x * y) = x * (y * x) := by rw [hxy_c]
      _ = (x * y) * x := by group
  have hxB : Subgroup.closure ({z, u, t} : Set G) ≤ Subgroup.centralizer ({x} : Set G) := by
    refine (Subgroup.closure_le _).mpr ?_
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    rcases hg with hg | hg | hg <;> rw [hg]
    · exact hxz.symm
    · exact hxu.symm
    · exact hxt.symm
  have hxc : x * c = c * x := (Subgroup.mem_centralizer_singleton_iff.mp (hxB hcB)).symm
  have hxC : x ∈ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hxc
  have hxJ : x ∈ trivialOnQuot J :=
    sylow_le_trivialOnQuot hp hq hΩ hK hJΩ hz hJt hd.t_ne_z.symm hRK hRKt hx
  have hxJ' : x ∈ trivialOnQuot J' :=
    sylow_le_trivialOnQuot hp hq hΩ hK hJ'Ω hz hJ't hd.t_ne_z.symm hRK hRKt hx
  have hqs : ∀ R₀ : Subgroup (compModel D j).K,
      R₀ ∈ fundamentalSubgroups (D.tag j) (compModel D j).D →
        CFSG.Open.IsQuasisimple ↥(R₀.map ψ) := fun R₀ hR₀ =>
    isQuasisimple_map_of_ker_le_center ψ hker
      (fundQuasisimple_core hp (D.isFundTag j) (D.admissible j) (by omega) R₀ hR₀)
  have hqJ : CFSG.Open.IsQuasisimple ↥(modOdd c (exactCore c J)) := by
    rw [← hRM]
    exact hqs R hpair.mem
  have hqJ' : CFSG.Open.IsQuasisimple ↥(modOdd c (exactCore c J')) := by
    rw [← hR'M]
    exact hqs R' hpair.mem'
  have hcommJ := oddQuotMk_centralizes_modOdd_exactCore hcJ hc2 hMJ.2 hxJ hxC hqJ
  have hcommJ' := oddQuotMk_centralizes_modOdd_exactCore hcJ' hc2 hMJ'.2 hxJ' hxC hqJ'
  have hx₁nc : ¬ ∀ y ∈ ψ.range, ψ x₁ * y = y * ψ x₁ := by
    intro hall
    have hcen : ∀ k : (compModel D j).K,
        x₁ * k * x₁⁻¹ * k⁻¹ ∈ Subgroup.center (compModel D j).K := by
      intro k
      apply hker
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv]
      have h1 := hall (ψ k) ⟨k, rfl⟩
      calc ψ x₁ * ψ k * (ψ x₁)⁻¹ * (ψ k)⁻¹ = (ψ x₁ * ψ k) * (ψ x₁)⁻¹ * (ψ k)⁻¹ := rfl
        _ = (ψ k * ψ x₁) * (ψ x₁)⁻¹ * (ψ k)⁻¹ := by rw [h1]
        _ = 1 := by group
    exact hpair.hx1 (CFSG.ClassicalInvolution.ModelFacts.fundNoncentral_generic p (D.tag j)
      (D.rank j) (D.exp j) (D.isFundTag j) (D.admissible j) hnA1 R hpair.mem x₁ hpair.hx hcen)
  have hxn : oddQuotMk c ⟨x, hxC⟩ ∈ Subgroup.normalizer (ψ.range : Set (OddQuot c)) :=
    mem_normalizer_of_commute_noncentral hLcomp ⟨x₁, rfl⟩ hx₁nc
      (g := oddQuotMk c ⟨x, hxC⟩) (by
        rw [hψx₁, ← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext hxt)
  have hψnorm : ∀ w : (compModel D j).K,
      ψ w ∈ Subgroup.normalizer (ψ.range : Set (OddQuot c)) :=
    FrameVertex.mem_normalizer_range ψ
  set v : ↥(inducedAutOn ψ.range) := toInducedAutOn ψ.range ⟨oddQuotMk c ⟨x, hxC⟩, hxn⟩ with hv
  have hvR : ∀ r ∈ R, v * FrameVertex.innerHom ψ r = FrameVertex.innerHom ψ r * v := by
    intro r hr
    rw [FrameVertex.innerHom_apply, hv, ← map_mul, ← map_mul]
    have hr' : ψ r ∈ modOdd c (exactCore c J) := hRM ▸ Subgroup.mem_map_of_mem ψ hr
    congr 1
    exact Subtype.ext (hcommJ (ψ r) hr')
  have hvR' : ∀ r ∈ R', v * FrameVertex.innerHom ψ r = FrameVertex.innerHom ψ r * v := by
    intro r hr
    rw [FrameVertex.innerHom_apply, hv, ← map_mul, ← map_mul]
    have hr' : ψ r ∈ modOdd c (exactCore c J') := hR'M ▸ Subgroup.mem_map_of_mem ψ hr
    congr 1
    exact Subtype.ext (hcommJ' (ψ r) hr')
  have hxx : oddQuotMk c ⟨x, hxC⟩ * oddQuotMk c ⟨x, hxC⟩ = oddQuotMk c ⟨z, hzC⟩ := by
    rw [← map_mul]
    congr 1
    exact Subtype.ext hx2
  have hzn : oddQuotMk c ⟨z, hzC⟩ ∈ Subgroup.normalizer (ψ.range : Set (OddQuot c)) := by
    rw [← hxx]
    exact Subgroup.mul_mem _ hxn hxn
  have htn : oddQuotMk c ⟨t, htC⟩ ∈ Subgroup.normalizer (ψ.range : Set (OddQuot c)) := by
    rw [← hψx₁]
    exact hψnorm x₁
  have hvv : v * v = toInducedAutOn ψ.range ⟨oddQuotMk c ⟨z, hzC⟩, hzn⟩ := by
    rw [hv, ← map_mul]
    congr 1
    exact Subtype.ext hxx
  have hzz : oddQuotMk c ⟨z, hzC⟩ * oddQuotMk c ⟨z, hzC⟩ = 1 := by
    rw [← map_mul]
    have : (⟨z, hzC⟩ * ⟨z, hzC⟩ : ↥(Subgroup.centralizer ({c} : Set G))) = 1 :=
      Subtype.ext hz.sq
    rw [this, map_one]
  have htt : oddQuotMk c ⟨t, htC⟩ * oddQuotMk c ⟨t, htC⟩ = 1 := by
    rw [← map_mul]
    have : (⟨t, htC⟩ * ⟨t, htC⟩ : ↥(Subgroup.centralizer ({c} : Set G))) = 1 :=
      Subtype.ext hJt.sq
    rw [this, map_one]
  have hvv2 : v * v * (v * v) = 1 := by
    rw [hvv, ← map_mul]
    have : (⟨oddQuotMk c ⟨z, hzC⟩, hzn⟩ * ⟨oddQuotMk c ⟨z, hzC⟩, hzn⟩ :
        ↥(Subgroup.normalizer (ψ.range : Set (OddQuot c)))) = 1 := Subtype.ext hzz
    rw [this, map_one]
  have hmovz := hmov (oddQuotMk c ⟨z, hzC⟩) (oddQuotMk_mem_modOdd hzB hzC)
    (Lemma52Proof.oddQuotMk_not_mem_zpowers hBab hcB hc1 hzB hz1 hzc hzC)
  have hvv1 : v * v ≠ 1 := by
    rw [hvv]
    obtain ⟨y', hy', hxy'⟩ := hmovz
    exact Lemma52Proof.toInducedAutOn_ne_one_of_moved ψ.range hzn hy' hxy'
  have hztC : z * t ∈ Subgroup.centralizer ({c} : Set G) := Subgroup.mul_mem _ hzC htC
  have hztB : z * t ∈ Subgroup.closure ({z, u, t} : Set G) := Subgroup.mul_mem _ hzB htB
  have hmovzt := hmov (oddQuotMk c ⟨z * t, hztC⟩) (oddQuotMk_mem_modOdd hztB hztC)
    (Lemma52Proof.oddQuotMk_not_mem_zpowers hBab hcB hc1 hztB hs.zt_ne_one hztc hztC)
  have hv4 : v * v ≠ FrameVertex.innerHom ψ x₁ := by
    intro h
    have h1 : toInducedAutOn ψ.range ⟨oddQuotMk c ⟨z, hzC⟩, hzn⟩ =
        toInducedAutOn ψ.range ⟨oddQuotMk c ⟨t, htC⟩, htn⟩ := by
      rw [← hvv, h, FrameVertex.innerHom_apply]
      congr 1
      exact Subtype.ext hψx₁
    have hztn : oddQuotMk c ⟨z * t, hztC⟩ ∈ Subgroup.normalizer (ψ.range : Set (OddQuot c)) := by
      have : oddQuotMk c ⟨z * t, hztC⟩ = oddQuotMk c ⟨z, hzC⟩ * oddQuotMk c ⟨t, htC⟩ :=
        map_mul (oddQuotMk c) (⟨z, hzC⟩ : ↥(Subgroup.centralizer ({c} : Set G))) ⟨t, htC⟩
      rw [this]
      exact Subgroup.mul_mem _ hzn htn
    have h2 : toInducedAutOn ψ.range ⟨oddQuotMk c ⟨z * t, hztC⟩, hztn⟩ = 1 := by
      have h3 : (⟨oddQuotMk c ⟨z * t, hztC⟩, hztn⟩ :
          ↥(Subgroup.normalizer (ψ.range : Set (OddQuot c)))) =
            ⟨oddQuotMk c ⟨z, hzC⟩, hzn⟩ * ⟨oddQuotMk c ⟨t, htC⟩, htn⟩ :=
        Subtype.ext (map_mul (oddQuotMk c)
          (⟨z, hzC⟩ : ↥(Subgroup.centralizer ({c} : Set G))) ⟨t, htC⟩)
      rw [h3, map_mul, h1, ← map_mul]
      have h4 : (⟨oddQuotMk c ⟨t, htC⟩, htn⟩ * ⟨oddQuotMk c ⟨t, htC⟩, htn⟩ :
          ↥(Subgroup.normalizer (ψ.range : Set (OddQuot c)))) = 1 := Subtype.ext htt
      rw [h4, map_one]
    have hcomm := Lemma52Proof.commute_of_toInducedAutOn_eq_one ψ.range hztn h2
    obtain ⟨y', hy', hxy'⟩ := hmovzt
    exact hxy' (hcomm y' hy')
  have key := hTO (OddQuot c) ψ R R' x₁ x₁' hpair v hvR hvR' hvv2 hvv1 hv4
  set T : Subgroup ↥(inducedAutOn ψ.range) :=
    Subgroup.closure ({FrameVertex.innerHom ψ x₁, v * v} : Set ↥(inducedAutOn ψ.range)) with hT
  have hztcl : ∀ w : G, (w = 1 ∨ w = z ∨ w = t ∨ w = t * z) →
      w ∈ Subgroup.closure ({z, t, c} : Set G) := by
    have hz' : z ∈ Subgroup.closure ({z, t, c} : Set G) := Subgroup.subset_closure (by simp)
    have ht' : t ∈ Subgroup.closure ({z, t, c} : Set G) := Subgroup.subset_closure (by simp)
    intro w hw
    rcases hw with hw | hw | hw | hw <;> rw [hw]
    · exact Subgroup.one_mem _
    · exact hz'
    · exact ht'
    · exact Subgroup.mul_mem _ ht' hz'
  have hBeq : Subgroup.closure ({z, u, t} : Set G) = Subgroup.closure ({z, t, c} : Set G) := by
    apply le_antisymm
    · refine (Subgroup.closure_le _).mpr ?_
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with hg | hg | hg <;> rw [hg]
      · exact Subgroup.subset_closure (by simp)
      · obtain ⟨w, hw, -, huw⟩ := hs.UCoset_exists_w hc
        rw [huw]
        exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (hztcl w hw)
      · exact Subgroup.subset_closure (by simp)
    · refine (Subgroup.closure_le _).mpr ?_
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with hg | hg | hg <;> rw [hg]
      · exact hzB
      · exact htB
      · exact hcB
  have hcC : c ∈ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hS : ({z, t, c} : Set G) ⊆ Subgroup.centralizer ({c} : Set G) := by
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with hg | hg | hg <;> rw [hg]
    · exact hzC
    · exact htC
    · exact hcC
  have hgen : ∀ s : G, s ∈ ({z, t, c} : Set G) → ∀ hs' : s ∈ Subgroup.centralizer ({c} : Set G),
      ∃ hn : oddQuotMk c ⟨s, hs'⟩ ∈ Subgroup.normalizer (ψ.range : Set (OddQuot c)),
        toInducedAutOn ψ.range ⟨oddQuotMk c ⟨s, hs'⟩, hn⟩ ∈ T := by
    intro s hs' hsC
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs'
    rcases hs' with hs' | hs' | hs'
    · subst s
      refine ⟨hzn, ?_⟩
      rw [← hvv]
      exact Subgroup.subset_closure (by simp)
    · subst s
      refine ⟨htn, ?_⟩
      have h1 : toInducedAutOn ψ.range ⟨oddQuotMk c ⟨t, hsC⟩, htn⟩ =
          FrameVertex.innerHom ψ x₁ := by
        rw [FrameVertex.innerHom_apply]
        congr 1
        exact Subtype.ext hψx₁.symm
      rw [h1]
      exact Subgroup.subset_closure (by simp)
    · subst s
      obtain ⟨hcn, hc1'⟩ := oddQuotSelf_induced c ψ.range
      refine ⟨hcn, ?_⟩
      have h1 : toInducedAutOn ψ.range ⟨oddQuotMk c ⟨c, hsC⟩, hcn⟩ = 1 := hc1'
      rw [h1]
      exact T.one_mem
  have hle1 : inducedImage ψ.range (modOdd c (Subgroup.closure ({z, u, t} : Set G))) ≤ T := by
    rw [hBeq]
    exact inducedImage_modOdd_closure_le hS ψ.range T (fun s hs'' => hgen s hs'' (hS hs''))
  have hψx₁B : ψ x₁ ∈ modOdd c (Subgroup.closure ({z, u, t} : Set G)) := by
    rw [hψx₁]
    exact oddQuotMk_mem_modOdd htB htC
  have hle2 : T ≤ inducedImage ψ.range (modOdd c (Subgroup.closure ({z, u, t} : Set G))) := by
    refine (Subgroup.closure_le _).mpr ?_
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with hg | hg
    · rw [hg, FrameVertex.innerHom_apply]
      exact ⟨⟨ψ x₁, hψnorm x₁⟩, Subgroup.mem_subgroupOf.mpr hψx₁B, rfl⟩
    · rw [hg, hvv]
      exact ⟨⟨oddQuotMk c ⟨z, hzC⟩, hzn⟩,
        Subgroup.mem_subgroupOf.mpr (oddQuotMk_mem_modOdd hzB hzC), rfl⟩
  exact (congrArg alphaOf (le_antisymm hle1 hle2)).trans key

theorem twinFrameHyp51u_of (hres : TwinSmallOuter p) (hex : G2D4VertexExcl p f) :
    TwinFrameHyp51u p f := by
  intro G _ _ _ Ω K K' J z u t hs
  have main : ∀ c : G, UCoset z u t c → Hyp51At (Subgroup.closure ({z, u, t} : Set G)) c := by
    intro c hc
    have hp : p ≠ 2 := hs.odd
    have hq : 5 ≤ p ^ f := hs.five
    have hΩ := hs.hyp
    have hd := hs.frame
    have hBab := twinFrame_isElemAbelian hp hΩ hd
    have htB : t ∈ Subgroup.closure ({z, u, t} : Set G) := Subgroup.subset_closure (by simp)
    have hcB : c ∈ Subgroup.closure ({z, u, t} : Set G) := hc.mem_closure
    have hc1 : c ≠ 1 := hs.uc_ne_one hc
    have htc : t ≠ c := hs.t_ne_uc hc
    have hcc : c * c = 1 := Lemma52Proof.mul_self_eq_one_of_mem hBab hcB
    have hc2 : IsPGroup 2 (Subgroup.zpowers c) := isPGroup_zpowers_of_sq_eq_one hcc
    have hJΩ : J ∈ Ω := hd.hJ.1
    have hJt : IsUniqueInvolution J t := hd.ht
    have hcJ : IsClassicalMember p f J t := isClassicalMember_of_twin hΩ hJΩ hJt
    have hMJ : J ∈ tqMembers Ω c := ⟨hJΩ, hs.tq_uc hc hJΩ hJt⟩
    refine hs.toCore.hyp51At_u_of hc fun J' hMJ' hcJ' hJ'ne D j hMj hM'j hmov => ?_
    have ht1 : t ≠ 1 := hJt.ne_one
    have hG2 : D.tag j ≠ .G2 := fun h =>
      hex G Ω hΩ hs.aEmpty c hc2 D j (Or.inl h) J J' t hMJ hMJ' hcJ hcJ' hJ'ne hMj hM'j
    have hD4 : D.tag j ≠ .trialityD4 := fun h =>
      hex G Ω hΩ hs.aEmpty c hc2 D j (Or.inr h) J J' t hMJ hMJ' hcJ hcJ' hJ'ne hMj hM'j
    obtain ⟨htC, R, R', x₁, x₁', hpair, hshape, hRM, hR'M, hψx₁⟩ := vertexTwin hp hq hΩ hc2
      hBab hcB hc1 htB ht1 htc hMJ hMJ' hcJ hcJ' hJ'ne D j hMj hmov hG2 hD4
    have hexp : D.exp j = f := (D.exp_eq j).resolve_right fun h => hD4 h.1
    have hq' : 5 ≤ p ^ D.exp j := by rw [hexp]; exact hq
    exact ⟨htC, R, R', x₁, x₁', hpair, hRM, hR'M, hψx₁, hshape.not_A1, hexp,
      twinOuterAlpha_of_shape hres hp hq' (D.admissible j) hshape⟩
  exact ⟨main u (Or.inl rfl), main (u * z) (Or.inr (Or.inl rfl)),
    main (u * t) (Or.inr (Or.inr (Or.inl rfl))), main (u * t * z) (Or.inr (Or.inr (Or.inr rfl)))⟩

end Vertex


theorem twinFrameHyp51_of {p f : ℕ} [Fact p.Prime] (hin : TwinSmallInner p)
    (hout : TwinSmallOuter p) (hex : G2D4VertexExcl p f) : TwinFrameHyp51 p f :=
  twinFrameHyp51_of_cases (twinFrameHyp51z p f) (twinFrameHyp51t_of hin hex)
    (twinFrameHyp51u_of hout hex)


theorem c21_3_of_residuals {p f : ℕ} [Fact p.Prime] (hin : TwinSmallInner p)
    (hout : TwinSmallOuter p) (hex : G2D4VertexExcl p f) : C21_3 p f :=
  c21_3_of p f (twinFrameHyp51_of hin hout hex)

end CFSG.ClassicalInvolution.Asc77
