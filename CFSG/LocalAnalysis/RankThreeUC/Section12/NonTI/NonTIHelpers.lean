module




public import CFSG.LieType.BorelTits.Basic
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.CGT.Timmesfeld75.Defs
public import CFSG.Open.RankThreeDefs

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace Section12

namespace NonTI

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem normalizer_le_of_max {M : Subgroup G} (hM : rankThreeIsMaxTwoLocal M) :
    Subgroup.normalizer (M : Set G) ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP, hP2, hMP⟩ := hM.1
  have hPO : P ≤ pCoreOf 2 M :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hMP ▸ Subgroup.le_normalizer)
      (le_of_eq hMP) hP2
  have hO : pCoreOf 2 M ≠ ⊥ := fun hb => hP (le_bot_iff.mp (hb ▸ hPO))
  have hloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 M : Set G)) :=
    ⟨pCoreOf 2 M, hO, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M, rfl⟩
  have heq := hM.2 _ hloc (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)
  exact (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 M).trans heq.le

theorem isTwoLocal_map_conj {K : Subgroup G} (hK : IsTwoLocal K) (g : G) :
    IsTwoLocal (K.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨P, hP, hP2, rfl⟩ := hK
  refine ⟨P.map (MulAut.conj g).toMonoidHom, ?_, hP2.map _, ?_⟩
  · intro hb
    exact hP ((Subgroup.map_eq_bot_iff_of_injective P (MulAut.conj g).injective).mp hb)
  · exact Subgroup.map_normalizer_eq_of_bijective P (MulAut.conj g).bijective

theorem max_map_conj {K : Subgroup G} (hK : rankThreeIsMaxTwoLocal K) (g : G) :
    rankThreeIsMaxTwoLocal (K.map (MulAut.conj g).toMonoidHom) := by
  refine ⟨isTwoLocal_map_conj hK.1 g, fun H hH hKH => ?_⟩
  have hH' := isTwoLocal_map_conj hH g⁻¹
  have e : ∀ L : Subgroup G, (L.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = L := by
    intro L
    rw [Subgroup.map_map]
    ext x; simp [MulAut.conj_apply, mul_assoc]
  have e' : ∀ L : Subgroup G, (L.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = L := by
    intro L
    rw [Subgroup.map_map]
    ext x; simp [MulAut.conj_apply, mul_assoc]
  have hKH' : K ≤ H.map (MulAut.conj g⁻¹).toMonoidHom := by
    have := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hKH
    rwa [e] at this
  have h1 := hK.2 _ hH' hKH'
  rw [← e' H, h1]

theorem exists_max_above {H0 : Subgroup G} (h0 : IsTwoLocal H0) :
    ∃ N, rankThreeIsMaxTwoLocal N ∧ H0 ≤ N := by
  obtain ⟨W, ⟨hW, hH0⟩, hWmax⟩ := exists_maximal_of_wellFoundedGT
    (fun W : Subgroup G => IsTwoLocal W ∧ H0 ≤ W) ⟨H0, h0, le_rfl⟩
  exact ⟨W, ⟨hW, fun H hH hWH => le_antisymm (hWmax ⟨hH, hH0.trans hWH⟩ hWH) hWH⟩, hH0⟩

theorem cent_le_max {u : G} (hu1 : u ≠ 1) (hu2 : u ^ 2 = 1) :
    ∃ N, rankThreeIsMaxTwoLocal N ∧ Subgroup.centralizer ({u} : Set G) ≤ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf u = 2 := orderOf_eq_prime hu2 hu1
  have hP : IsPGroup 2 (Subgroup.zpowers u) := by
    rw [IsPGroup.iff_card]
    exact ⟨1, by rw [Nat.card_zpowers, hord]; rfl⟩
  have hne : Subgroup.zpowers u ≠ ⊥ := by
    intro h; apply hu1; have := Subgroup.mem_zpowers u; rw [h] at this; simpa using this
  have hloc : IsTwoLocal (Subgroup.normalizer (Subgroup.zpowers u : Set G)) := ⟨_, hne, hP, rfl⟩
  obtain ⟨N, hN, hle⟩ := exists_max_above hloc
  refine ⟨N, hN, le_trans ?_ hle⟩
  intro x hx
  have hxu : x * u * x⁻¹ = u := by
    have := Subgroup.mem_centralizer_iff.mp hx u rfl
    rw [mul_inv_eq_iff_eq_mul]; exact this.symm
  have key : ∀ z ∈ Subgroup.centralizer ({u} : Set G), ∀ y, y ∈ Subgroup.zpowers u →
      z * y * z⁻¹ ∈ Subgroup.zpowers u := by
    intro z hz y hy
    have hzu : z * u * z⁻¹ = u := by
      have := Subgroup.mem_centralizer_iff.mp hz u rfl
      rw [mul_inv_eq_iff_eq_mul]; exact this.symm
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
    rw [← conj_zpow, hzu]
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key x hx y, fun h => ?_⟩
  have := key x⁻¹ (Subgroup.inv_mem _ hx) _ h
  simpa [mul_assoc] using this

theorem isTI_of_unique {M V : Subgroup G} (hM : rankThreeIsMaxTwoLocal M) (hVM : V ≤ M)
    (hVn : M ≤ Subgroup.normalizer (V : Set G)) (hab : CFSG.Assembly.IsElemAbelian 2 V)
    (huniq : ∀ N, rankThreeIsMaxTwoLocal N → M ⊓ Subgroup.centralizer (V : Set G) ≤ N → N = M) :
    CFSG.CGT.Timmesfeld75.IsTI V := by
  have hcent : ∀ u ∈ V, u ≠ 1 → Subgroup.centralizer ({u} : Set G) ≤ M := by
    intro u hu hu1
    obtain ⟨N, hN, hle⟩ := cent_le_max hu1 (by simpa using hab.2 u hu)
    have hsub : M ⊓ Subgroup.centralizer (V : Set G) ≤ Subgroup.centralizer ({u} : Set G) := by
      intro x hx
      refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
      rw [Set.mem_singleton_iff] at hy; subst hy
      exact (Subgroup.mem_centralizer_iff.mp hx.2 y hu)
    have : N = M := huniq N hN (le_trans hsub hle)
    exact this ▸ hle
  intro g
  by_cases hb : V ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup g V = ⊥
  · exact Or.inl hb
  right
  obtain ⟨⟨w, hw⟩, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hb
  have hw1 : w ≠ 1 := fun h => hw1 (Subtype.ext h)
  have hw' : w ∈ V := hw.1
  have hwg : g⁻¹ * w * g ∈ V := CFSG.CGT.Timmesfeld75.mem_conjSubgroup.mp hw.2
  have hv1 : g⁻¹ * w * g ≠ 1 := by
    intro h; apply hw1
    have h2 : g * (g⁻¹ * w * g) * g⁻¹ = w := by group
    rw [h] at h2; simpa using h2.symm
  have hCv := hcent _ hwg hv1
  have hM' := max_map_conj hM g
  have : M.map (MulAut.conj g).toMonoidHom = M := by
    refine huniq _ hM' (fun x hx => ?_)
    have hxw : x ∈ Subgroup.centralizer ({w} : Set G) := by
      refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
      rw [Set.mem_singleton_iff] at hy; subst hy
      exact Subgroup.mem_centralizer_iff.mp hx.2 _ hw'
    have : g⁻¹ * x * g ∈ M := by
      apply hCv
      refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
      rw [Set.mem_singleton_iff] at hy; subst hy
      have := Subgroup.mem_centralizer_iff.mp hxw w rfl
      calc g⁻¹ * w * g * (g⁻¹ * x * g) = g⁻¹ * (w * x) * g := by group
        _ = g⁻¹ * (x * w) * g := by rw [this]
        _ = g⁻¹ * x * g * (g⁻¹ * w * g) := by group
    exact ⟨g⁻¹ * x * g, this, by simp [MulAut.conj_apply, mul_assoc]⟩
  have hgn : g ∈ Subgroup.normalizer (M : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [← this]; exact ⟨h, hh, rfl⟩
    · intro hh
      rw [← this] at hh
      obtain ⟨y, hy, hyh⟩ := hh
      have : y = h := by simpa [MulAut.conj_apply] using hyh
      exact this ▸ hy
  have hgM : g ∈ M := normalizer_le_of_max hM hgn
  have : CFSG.CGT.Timmesfeld75.conjSubgroup g V = V := by
    ext x
    rw [CFSG.CGT.Timmesfeld75.mem_conjSubgroup]
    have := (Subgroup.mem_normalizer_iff.mp (hVn (Subgroup.inv_mem _ hgM))) x
    simpa using this.symm
  rw [this]; simp

end NonTI

end Section12

end CFSG.LocalAnalysis.RankThreeUC
