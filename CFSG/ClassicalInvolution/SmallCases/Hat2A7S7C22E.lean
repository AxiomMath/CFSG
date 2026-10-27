module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S7C22D
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S8Alpha

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Hat2A7S

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Balance

section Conj


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}
  {K₁ K₂ K₃ R₁ R₂ R₃ : Subgroup G} {u₁ u₂ u₃ : G}

theorem Frame3.conj (hΩ : HypOmegaGen Ω) (F : Frame3 Ω z K₁ K₂ K₃ R₁ R₂ R₃ u₁ u₂ u₃) {g : G}
    (hgz : g * z * g⁻¹ = z) :
    Frame3 Ω z (conjSub g K₁) (conjSub g K₂) (conjSub g K₃) (conjSub g R₁) (conjSub g R₂)
      (conjSub g R₃) (g * u₁ * g⁻¹) (g * u₂ * g⁻¹) (g * u₃ * g⁻¹) where
  mem₁ := hΩ.conjInvariant g K₁ F.mem₁
  mem₂ := hΩ.conjInvariant g K₂ F.mem₂
  mem₃ := hΩ.conjInvariant g K₃ F.mem₃
  hz₁ := by
    have := F.hz₁.conj g
    rwa [hgz] at this
  hz₂ := by
    have := F.hz₂.conj g
    rwa [hgz] at this
  hz₃ := by
    have := F.hz₃.conj g
    rwa [hgz] at this
  ne₁₂ := fun h => F.ne₁₂ (conjSub_injective g h)
  ne₁₃ := fun h => F.ne₁₃ (conjSub_injective g h)
  ne₂₃ := fun h => F.ne₂₃ (conjSub_injective g h)
  syl₁ := F.syl₁.conj g
  syl₂ := F.syl₂.conj g
  syl₃ := F.syl₃.conj g
  comm₁₂ := F.comm₁₂.conjSub g
  comm₁₃ := F.comm₁₃.conjSub g
  comm₂₃ := F.comm₂₃.conjSub g
  mem_u₁ := conj_mem_conjSub F.mem_u₁
  mem_u₂ := conj_mem_conjSub F.mem_u₂
  mem_u₃ := conj_mem_conjSub F.mem_u₃
  ord₁ := by rw [orderOf_conj_mul_inv_eq]; exact F.ord₁
  ord₂ := by rw [orderOf_conj_mul_inv_eq]; exact F.ord₂
  ord₃ := by rw [orderOf_conj_mul_inv_eq]; exact F.ord₃

theorem Frame3.withElems (F : Frame3 Ω z K₁ K₂ K₃ R₁ R₂ R₃ u₁ u₂ u₃) {v₁ v₂ v₃ : G}
    (h₁ : v₁ ∈ R₁) (h₂ : v₂ ∈ R₂) (h₃ : v₃ ∈ R₃) (o₁ : orderOf v₁ = 4) (o₂ : orderOf v₂ = 4)
    (o₃ : orderOf v₃ = 4) : Frame3 Ω z K₁ K₂ K₃ R₁ R₂ R₃ v₁ v₂ v₃ :=
  { F with mem_u₁ := h₁, mem_u₂ := h₂, mem_u₃ := h₃, ord₁ := o₁, ord₂ := o₂, ord₃ := o₃ }

theorem alphaOf_closure_conj {g : G} (hgz : g * z * g⁻¹ = z) (x : G) :
    alphaOf (Subgroup.closure ({z, g * x * g⁻¹} : Set G)) =
      conjSub g (alphaOf (Subgroup.closure ({z, x} : Set G))) := by
  have h : conjSub g (Subgroup.closure ({z, x} : Set G)) =
      Subgroup.closure ({z, g * x * g⁻¹} : Set G) := by
    unfold conjSub
    rw [MonoidHom.map_closure, Set.image_pair]
    have e1 : (MulAut.conj g).toMonoidHom z = z := by simp [MulAut.conj_apply, hgz]
    have e2 : (MulAut.conj g).toMonoidHom x = g * x * g⁻¹ := by simp [MulAut.conj_apply]
    rw [e1, e2]
  rw [← alphaOf_conjSub, h]

theorem exists_frame3_extend (hΩ : HypOmegaGen Ω) {L L' M R R' : Subgroup G} {x y : G}
    (hL : L ∈ Ω) (hL' : L' ∈ Ω) (hM : M ∈ Ω) (hzL : IsUniqueInvolution L z)
    (hzL' : IsUniqueInvolution L' z) (hzM : IsUniqueInvolution M z) (h12 : L' ≠ L) (h13 : M ≠ L)
    (h23 : M ≠ L') (hR : IsSylow2In R L) (hR' : IsSylow2In R' L') (hc : Commutes R R')
    (hx : x ∈ R) (hx4 : orderOf x = 4) (hy : y ∈ R') (hy4 : orderOf y = 4) :
    ∃ (R'' : Subgroup G) (w : G), Frame3 Ω z L L' M R R' R'' x y w := by
  have hP2 : IsPGroup 2 ↥(R ⊔ R') :=
    hR.2.1.to_sup_of_normal_right' hR'.2.1 (T7A.le_normalizer_of_commutes hc.symm)
  have hNL : L ≤ Subgroup.normalizer (M : Set G) :=
    Sec6Gen.le_normalizer_of_twin hΩ hL hM h13.symm hzL hzM
  have hNL' : L' ≤ Subgroup.normalizer (M : Set G) :=
    Sec6Gen.le_normalizer_of_twin hΩ hL' hM h23.symm hzL' hzM
  obtain ⟨R'', hR'', hfix⟩ :=
    exists_sylow_normalized hP2 (sup_le (hR.1.trans hNL) (hR'.1.trans hNL'))
  have hnorm : R ⊔ R' ≤ Subgroup.normalizer (R'' : Set G) := fun t ht =>
    mem_normalizer_iff_conjSub_eq.mpr (hfix t ht)
  have hV : IsPGroup 2 ↥((R ⊔ R') ⊔ R'') := hP2.to_sup_of_normal_right' hR''.2.1 hnorm
  have hc1 : Commutes R R'' :=
    Sec6Gen.commutes_of_twin_of_isPGroup hΩ hL hM h13.symm hzL hzM hR.1 hR''.1
      (hV.to_le (sup_le_sup_right le_sup_left _))
  have hc2 : Commutes R' R'' :=
    Sec6Gen.commutes_of_twin_of_isPGroup hΩ hL' hM h23.symm hzL' hzM hR'.1 hR''.1
      (hV.to_le (sup_le_sup_right le_sup_right _))
  obtain ⟨w, hw, hw4⟩ :=
    Hat2A7M.P25.exists_orderOf_eq_four_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hM hR'')
  exact ⟨R'', w,
    { mem₁ := hL, mem₂ := hL', mem₃ := hM, hz₁ := hzL, hz₂ := hzL', hz₃ := hzM, ne₁₂ := h12,
      ne₁₃ := h13, ne₂₃ := h23, syl₁ := hR, syl₂ := hR', syl₃ := hR'', comm₁₂ := hc,
      comm₁₃ := hc1, comm₂₃ := hc2, mem_u₁ := hx, mem_u₂ := hy, mem_u₃ := hw, ord₁ := hx4,
      ord₂ := hy4, ord₃ := hw4 }⟩

end Conj

section Dichotomy


variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)}
  {K₀ : Subgroup G} {z : G}

theorem layer_dichotomy_odd {x : G} {K J : Subgroup G}
    (hL : Hat2A7S8.Asc77.T8.LayerHyp Ω x) (hK : T8.XMem Ω x K) (hJ : T8.XMem Ω x J) :
    (∃ n ∈ oddCoreOf (T8.layerJoin Ω x), J = conjSub n K) ∨
      (∃ n ∈ oddCoreOf (T8.layerJoin Ω x), J ∈ omegaNbr Ω (conjSub n K)) := by
  by_cases heq : T8.layerImg Ω x K = T8.layerImg Ω x J
  · obtain ⟨n, hn, hnK⟩ := Hat2A7S8.Asc77.T8.exists_oddCore_conj_of_layerImg_eq hL hK hJ heq
    exact Or.inl ⟨n, hn, hnK.symm⟩
  · have hF := Hat2A7S8.Asc77.T8.LayerFam.layerSet hL.gen hK
    rcases hF.images_eq_or_commute hL ⟨K, hK, rfl⟩ ⟨J, hJ, rfl⟩ with h | hcomm
    · exact absurd h heq
    · exact Or.inr
        (Hat2A7S8.Asc77.T8.exists_oddCore_conj_omegaNbr_of_commute hL hK hJ heq hcomm)

theorem normalizer_le_centralizer_member {K : Subgroup G} (hz : IsUniqueInvolution K z) :
    Subgroup.normalizer (K : Set G) ≤ Subgroup.centralizer ({z} : Set G) := by
  intro n hn
  have h1 : n * z * n⁻¹ = z := hz.conj_eq (mem_normalizer_iff_conjSub_eq.mp hn)
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc n * z = n * z * n⁻¹ * n := by group
    _ = z * n := by rw [h1]

theorem centralizer_le_of_xMem (hs : Pre2A7 Ω K₀)
    (htw : ∀ L ∈ Ω, ∀ J ∈ omegaNbr Ω L, J ∈ twinSet Ω L) {c : G} (hc2 : c * c = 1) (hc1 : c ≠ 1)
    {K : Subgroup G} (hK : T8.XMem Ω c K) (hz : IsUniqueInvolution K z) (T : Subgroup G)
    (hT1 : oddCoreOf (Subgroup.centralizer ({c} : Set G)) ≤ T)
    (hT2 : Subgroup.centralizer ((Subgroup.closure ({z, c} : Set G) : Subgroup G) : Set G) ≤ T) :
    Subgroup.centralizer ({c} : Set G) ≤ T := by
  intro g hg
  have hΩ : HypOmegaGen Ω := hs.hyp
  have hL : Hat2A7S8.Asc77.T8.LayerHyp Ω c := Hat2A7S8.layerHyp_of_pre hs hc2 hc1
  have hgc : g ∈ T8.cenZ c := by
    rw [T8.cenZ_eq_centralizer]
    exact hg
  have hKg : T8.XMem Ω c (conjSub g K) := Hat2A7S8.Asc77.T8.XMem.conj hΩ hK hgc
  suffices h : ∃ n ∈ oddCoreOf (T8.layerJoin Ω c),
      n⁻¹ * g ∈ Subgroup.centralizer ((Subgroup.closure ({z, c} : Set G) : Subgroup G) : Set G) by
    obtain ⟨n, hn, hng⟩ := h
    have hnT : n ∈ T :=
      hT1 (Hat2A7S8.oddCoreOf_layerJoin_le_oddCoreOf_centralizer hΩ c hn)
    have e : g = n * (n⁻¹ * g) := by group
    rw [e]
    exact T.mul_mem hnT (hT2 hng)
  have hnc : ∀ n ∈ oddCoreOf (T8.layerJoin Ω c), n * c = c * n := fun n hn =>
    T8.mem_cenZ_iff.mp (T8.layerJoin_le_cenZ c (oddCoreOf_le_self _ hn))
  have hcomm_c : ∀ n ∈ oddCoreOf (T8.layerJoin Ω c), c * (n⁻¹ * g) = (n⁻¹ * g) * c := by
    intro n hn
    have h1 : c * n⁻¹ = n⁻¹ * c := by
      have := hnc n hn
      calc c * n⁻¹ = n⁻¹ * (n * c) * n⁻¹ := by group
        _ = n⁻¹ * (c * n) * n⁻¹ := by rw [this]
        _ = n⁻¹ * c := by group
    have h2 : g * c = c * g := T8.mem_cenZ_iff.mp hgc
    calc c * (n⁻¹ * g) = (c * n⁻¹) * g := by group
      _ = (n⁻¹ * c) * g := by rw [h1]
      _ = n⁻¹ * (c * g) := by group
      _ = n⁻¹ * (g * c) := by rw [h2]
      _ = (n⁻¹ * g) * c := by group
  rcases layer_dichotomy_odd hL hK hKg with ⟨n, hn, hnK⟩ | ⟨n, hn, hnb⟩
  · refine ⟨n, hn, mem_centralizer_closure_pair ?_ (hcomm_c n hn)⟩
    have hN : n⁻¹ * g ∈ Subgroup.normalizer (K : Set G) := by
      refine mem_normalizer_iff_conjSub_eq.mpr ?_
      rw [conjSub_mul, hnK, conjSub_inv_conjSub]
    have hzc := normalizer_le_centralizer_member hz hN
    exact (Subgroup.mem_centralizer_singleton_iff.mp hzc).symm
  · refine ⟨n, hn, mem_centralizer_closure_pair ?_ (hcomm_c n hn)⟩
    have htwin := htw (conjSub n K) (hΩ.conjInvariant n K hK.1) _ hnb
    obtain ⟨-, w, hw1, hw2⟩ := htwin
    have e1 : n * z * n⁻¹ = w := (hz.conj n).eq hw1
    have e2 : g * z * g⁻¹ = w := (hz.conj g).eq hw2
    have e : n * z * n⁻¹ = g * z * g⁻¹ := e1.trans e2.symm
    calc z * (n⁻¹ * g) = n⁻¹ * (n * z * n⁻¹) * g := by group
      _ = n⁻¹ * (g * z * g⁻¹) * g := by rw [e]
      _ = (n⁻¹ * g) * z := by group

end Dichotomy

end CFSG.ClassicalInvolution.Hat2A7S
