module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_3Rest
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_3Quasi
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

section Radical

variable {G : Type} [Group G]

theorem conjJoin_le_self {H K : Subgroup G} (hK : K ≤ H) : conjJoin H K ≤ H := by
  refine iSup_le fun g => ?_
  rintro _ ⟨y, hy, rfl⟩
  have hg : (g : G) ∈ H := g.2
  exact H.mul_mem (H.mul_mem hg (hK hy)) (H.inv_mem hg)

theorem map_conj_le_conjJoin (H K : Subgroup G) (g : ↥H) :
    K.map (MulAut.conj (g : G)).toMonoidHom ≤ conjJoin H K :=
  le_iSup (fun g : ↥H => K.map (MulAut.conj (g : G)).toMonoidHom) g

@[expose] def radicalOf (M H K : Subgroup G) : Subgroup G :=
  pCoreOf 2 (M ⊓ conjJoin H K)

theorem radicalOf_le_conjJoin (M H K : Subgroup G) : radicalOf M H K ≤ conjJoin H K :=
  (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 _).trans inf_le_right

theorem radicalOf_le {M H K : Subgroup G} (hK : K ≤ H) : radicalOf M H K ≤ H :=
  (radicalOf_le_conjJoin M H K).trans (conjJoin_le_self hK)

theorem isPGroup_radicalOf (M H K : Subgroup G) : IsPGroup 2 (radicalOf M H K) :=
  CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 _

theorem le_normalizer_radicalOf {M H K S : Subgroup G} (hSH : S ≤ H) (hSM : S ≤ M) :
    S ≤ Subgroup.normalizer (radicalOf M H K : Set G) :=
  (CFSG.RankThreeCoreUniqueness.Helpers.common_normalizer_le_normalizer_inf S M (conjJoin H K)
    (hSM.trans Subgroup.le_normalizer) (hSH.trans (le_normalizer_conjJoin H K))).trans
    (CFSG.RankThreeCoreUniqueness.Helpers.normalizer_localGroup_le_normalizer_pCoreOf 2 _)

@[expose] def benderRadical (S H K : Subgroup G) : Subgroup G :=
  ⨆ g : ↥H, S ⊓ K.map (MulAut.conj (g : G)).toMonoidHom

theorem benderRadical_le_S (S H K : Subgroup G) : benderRadical S H K ≤ S :=
  iSup_le fun _ => inf_le_left

theorem benderRadical_le_conjJoin (S H K : Subgroup G) : benderRadical S H K ≤ conjJoin H K :=
  iSup_le fun g => inf_le_right.trans (map_conj_le_conjJoin H K g)

theorem benderRadical_le {S H K : Subgroup G} (hK : K ≤ H) : benderRadical S H K ≤ H :=
  (benderRadical_le_conjJoin S H K).trans (conjJoin_le_self hK)

theorem inf_le_benderRadical (S H K : Subgroup G) : S ⊓ K ≤ benderRadical S H K := by
  have h1 : S ⊓ K.map (MulAut.conj ((⟨1, H.one_mem⟩ : ↥H) : G)).toMonoidHom ≤
      benderRadical S H K :=
    le_iSup (fun g : ↥H => S ⊓ K.map (MulAut.conj (g : G)).toMonoidHom) ⟨1, H.one_mem⟩
  rwa [show K.map (MulAut.conj ((⟨1, H.one_mem⟩ : ↥H) : G)).toMonoidHom = K from
    Unc25G2.map_conj_one K] at h1

theorem isPGroup_benderRadical {S : Subgroup G} (hS : IsPGroup 2 S) (H K : Subgroup G) :
    IsPGroup 2 (benderRadical S H K) :=
  hS.to_le (benderRadical_le_S S H K)

theorem benderRadical_map_le {S H K P : Subgroup G}
    (hP : ∀ g : ↥H, S ⊓ K.map (MulAut.conj (g : G)).toMonoidHom =
      P ⊓ K.map (MulAut.conj (g : G)).toMonoidHom) {h : G} (hhH : h ∈ H)
    (hhP : h ∈ Subgroup.normalizer (P : Set G)) :
    (benderRadical S H K).map (MulAut.conj h).toMonoidHom ≤ benderRadical S H K := by
  unfold benderRadical
  rw [Subgroup.map_iSup]
  refine iSup_le fun g => ?_
  refine le_trans ?_ (le_iSup _ (⟨h, hhH⟩ * g))
  rw [hP g, hP (⟨h, hhH⟩ * g)]
  rintro _ ⟨y, ⟨hyP, hyL⟩, rfl⟩
  refine ⟨(Subgroup.mem_normalizer_iff.mp hhP y).mp hyP, ?_⟩
  obtain ⟨k₀, hk₀, rfl⟩ := hyL
  refine ⟨k₀, hk₀, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul, mul_inv_rev]
  group

theorem le_normalizer_benderRadical_of {S H K P W : Subgroup G}
    (hP : ∀ g : ↥H, S ⊓ K.map (MulAut.conj (g : G)).toMonoidHom =
      P ⊓ K.map (MulAut.conj (g : G)).toMonoidHom) (hWH : W ≤ H)
    (hWP : W ≤ Subgroup.normalizer (P : Set G)) :
    W ≤ Subgroup.normalizer (benderRadical S H K : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro h hh r hr
  exact benderRadical_map_le hP (hWH hh) (hWP hh) (Subgroup.mem_map_of_mem _ hr)

theorem le_conjJoin_self (H K : Subgroup G) : K ≤ conjJoin H K := by
  have h1 : K.map (MulAut.conj ((⟨1, H.one_mem⟩ : ↥H) : G)).toMonoidHom ≤ conjJoin H K :=
    map_conj_le_conjJoin H K ⟨1, H.one_mem⟩
  rwa [show K.map (MulAut.conj ((⟨1, H.one_mem⟩ : ↥H) : G)).toMonoidHom = K from
    Unc25G2.map_conj_one K] at h1

theorem le_pCoreOf_of_normal_pGroup {P X : Subgroup G} (hPX : P ≤ X)
    (hn : X ≤ Subgroup.normalizer (P : Set G)) (hP : IsPGroup 2 P) : P ≤ pCoreOf 2 X :=
  CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 P X hPX
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hPX).mpr hn) hP

variable [Finite G]

theorem pCoreOf_le_normalizer_of_le_conjJoin {H K R : Subgroup G} (hK : IsComponentIn K H)
    (hR : R ≤ conjJoin H K) : pCoreOf 2 H ≤ Subgroup.normalizer (R : Set G) := by
  have hD : conjJoin H K ≤ Subgroup.centralizer (pCoreOf 2 H : Set G) := by
    refine iSup_le fun g => ?_
    have hKg : IsComponentIn (K.map (MulAut.conj (g : G)).toMonoidHom) H :=
      Unc25G2.isComponentIn_map_conj hK g.2
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (Unc25G2.commutator_pCoreOf_eq_bot hKg)
  intro x hx
  refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun r hr => ?_)
  exact (Subgroup.mem_centralizer_iff.mp (hD (hR hr)) x hx).symm

theorem conjJoin_le_normalizer_of_component {H K : Subgroup G} (hK : IsComponentIn K H) :
    conjJoin H K ≤ Subgroup.normalizer (K : Set G) := by
  refine iSup_le fun g => ?_
  have hKg : IsComponentIn (K.map (MulAut.conj (g : G)).toMonoidHom) H :=
    Unc25G2.isComponentIn_map_conj hK g.2
  rcases BenderBranch.eq_or_commute_of_isComponentIn hKg hK with h | h
  · rw [h]
    exact Subgroup.le_normalizer
  · refine le_trans (fun y hy => ?_)
      (Subgroup.centralizer_le_normalizer (s := (K : Set G)))
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact (BenderBranch.commute_of_commutator_eq_bot h hy hk).symm

theorem pCoreOf_inf_le_radicalOf {M H K : Subgroup G} (hK : IsComponentIn K H) :
    pCoreOf 2 (M ⊓ K) ≤ radicalOf M H K := by
  have hMK : M ⊓ conjJoin H K ≤ Subgroup.normalizer ((M ⊓ K : Subgroup G) : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.common_normalizer_le_normalizer_inf _ M K
      (inf_le_left.trans Subgroup.le_normalizer)
      (inf_le_right.trans (conjJoin_le_normalizer_of_component hK))
  exact le_pCoreOf_of_normal_pGroup
    ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 _).trans
      (inf_le_inf_left M (le_conjJoin_self H K)))
    (hMK.trans (CFSG.RankThreeCoreUniqueness.Helpers.normalizer_localGroup_le_normalizer_pCoreOf 2 _))
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 _)

omit [Finite G] in
theorem radicalOf_le_pCoreOf_of_normal {M H K : Subgroup G} (hK : IsComponentIn K H)
    (hN : conjJoin H K ≤ Subgroup.normalizer (radicalOf M H K : Set G)) :
    radicalOf M H K ≤ pCoreOf 2 H := by
  have hRD : radicalOf M H K ≤ conjJoin H K := radicalOf_le_conjJoin M H K
  have h1 : radicalOf M H K ≤ pCoreOf 2 (conjJoin H K) :=
    le_pCoreOf_of_normal_pGroup hRD hN (isPGroup_radicalOf M H K)
  have hDH : conjJoin H K ≤ H := conjJoin_le_self hK.1
  have hOD : pCoreOf 2 (conjJoin H K) ≤ H :=
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 _).trans hDH
  have h2 : pCoreOf 2 (conjJoin H K) ≤ pCoreOf 2 H :=
    le_pCoreOf_of_normal_pGroup hOD
      ((le_normalizer_conjJoin H K).trans
        (CFSG.RankThreeCoreUniqueness.Helpers.normalizer_localGroup_le_normalizer_pCoreOf 2 _))
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 _)
  exact h1.trans h2

end Radical

@[expose] def Lemma253BenderOrbit : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S : Subgroup G) (z : G),
    UnconstrainedSetting G T M → Tuple25 T M H S z →
      ∀ K : Subgroup G, IsComponentIn K H → fusionIsBenderGroup ↥K →
        ∀ L : Subgroup G,
          IsComponentIn L (H ⊓ Subgroup.normalizer (benderRadical S H K : Set G)) →
            IsComponentIn L H

@[expose] def Lemma253ListOrbit : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S : Subgroup G) (z : G),
    UnconstrainedSetting G T M → Tuple25 T M H S z →
      ∀ K : Subgroup G, IsComponentIn K H → ¬ fusionIsBenderGroup ↥K →
        ∀ L : Subgroup G,
          IsComponentIn L (H ⊓ Subgroup.normalizer (radicalOf M H K : Set G)) →
            IsComponentIn L H

@[expose] def Lemma253Core : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S : Subgroup G) (z : G) (U HU : Subgroup G),
    UnconstrainedSetting G T M → Tuple25 T M H S z → IsNormalizerIntersection H →
    IsMaxUPair M H U HU → U ≤ S →
    (IsGammaU M H → ∀ V : Subgroup G, IsWitness M V → Nat.card V ≤ Nat.card U) →
    (∃ K : Subgroup G, IsComponentIn K H) →
    (∀ K : Subgroup G, IsComponentIn K H → ¬ fusionIsBenderGroup ↥K) →
    (∀ K : Subgroup G, IsComponentIn K H →
      ¬ HU ≤ Subgroup.normalizer (radicalOf M H K : Set G)) →
    ∃ K U₁ HU₁ : Subgroup G, IsComponentIn K H ∧ IsWitnessPair M U₁ HU₁ ∧ HU₁ ≤ K ⊔ S ∧
      (IsGammaU M H → ∀ V : Subgroup G, IsWitness M V → Nat.card V ≤ Nat.card U₁)

section Bender

variable {G : Type} [Group G] [Finite G] {T M H S : Subgroup G} {z : G}

theorem le_normalizer_benderRadical_of_bender (hBend : Lemma253Bender)
    (hs : UnconstrainedSetting G T M) (ht : Tuple25 T M H S z) {k : ℕ} (B : Fin k → Subgroup G)
    (hB : ∀ i, B i ≤ H ∧ IsPGroup 2 (B i)) (hH : H = ⨅ i, Subgroup.normalizer (B i : Set G))
    {U HU : Subgroup G} (hmaxP : IsMaxUPair M H U HU) (hUS : U ≤ S) {K : Subgroup G}
    (hK : IsComponentIn K H) (hKB : fusionIsBenderGroup ↥K) :
    HU ≤ Subgroup.normalizer (benderRadical S H K : Set G) := by
  obtain ⟨hbang, -, -, -, hQU, -⟩ := upair_saturation hs.setting ht B hB hH hmaxP hUS
  have hQS : pCoreOf 2 HU ≤ S := hQU.trans hUS
  have hSQ : ∀ g : ↥H, S ⊓ K.map (MulAut.conj (g : G)).toMonoidHom =
      pCoreOf 2 HU ⊓ K.map (MulAut.conj (g : G)).toMonoidHom := by
    intro g
    have hLg : IsComponentIn (K.map (MulAut.conj (g : G)).toMonoidHom) H :=
      Unc25G2.isComponentIn_map_conj hK g.2
    have hBg : fusionIsBenderGroup ↥(K.map (MulAut.conj (g : G)).toMonoidHom) :=
      RankOneRecog.fusionIsBenderGroup_of_mulEquiv
        (K.equivMapOfInjective (MulAut.conj (g : G)).toMonoidHom
          (MulAut.conj (g : G)).injective) hKB
    have hSyl := hBend G T M H S z hs ht k B hB hH U HU hmaxP.1 _ hLg hBg hbang
    exact hSyl.eq_of_le (inf_le_inf_right _ hQS) inf_le_right
      (ht.sylow.isPGroup.to_le inf_le_left)
  exact le_normalizer_benderRadical_of hSQ hmaxP.1.2
    (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 HU)

theorem le_normalizer_benderRadical_self (ht : Tuple25 T M H S z) {K : Subgroup G} :
    S ≤ Subgroup.normalizer (benderRadical S H K : Set G) :=
  le_normalizer_benderRadical_of (fun _ => rfl) ht.le_H Subgroup.le_normalizer

theorem not_le_normalizer_benderRadical (ht : Tuple25 T M H S z) {K : Subgroup G}
    (hK : IsComponentIn K H) : ¬ H ≤ Subgroup.normalizer (benderRadical S H K : Set G) :=
  Unc25G2.not_le_normalizer_of_sylow_inf_le ht.sylow hK (benderRadical_le hK.1)
    (isPGroup_benderRadical ht.sylow.2.1 H K) (inf_le_benderRadical S H K)

theorem not_le_normalizer_radicalOf (ht : Tuple25 T M H S z) {K : Subgroup G}
    (hK : IsComponentIn K H) (hcl : ComponentList M S z K) :
    ¬ conjJoin H K ≤ Subgroup.normalizer (radicalOf M H K : Set G) := by
  intro hN
  have hRO : radicalOf M H K ≤ pCoreOf 2 H := radicalOf_le_pCoreOf_of_normal hK hN
  have hKc : K ≤ Subgroup.centralizer (pCoreOf 2 H : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp (Unc25G2.commutator_pCoreOf_eq_bot hK)
  have hQc : ∀ x ∈ pCoreOf 2 (M ⊓ K), ∀ y ∈ K, y * x = x * y := fun x hx y hy =>
    (Subgroup.mem_centralizer_iff.mp (hKc hy) x (hRO (pCoreOf_inf_le_radicalOf hK hx))).symm
  have hKq : CFSG.IsQuasisimple ↥K := BenderBranch.isQuasisimple_of_isComponentIn hK
  have hfromP : ∀ P : Subgroup G, IsSylowTwoOf P K → P ≤ pCoreOf 2 (M ⊓ K) → False :=
    fun P hP hPQ => Unc25G2.false_of_isSylowTwoOf_le_centralizer hKq hP fun x hx =>
      Subgroup.mem_centralizer_iff.mpr fun y hy => hQc x (hPQ hx) y hy
  obtain ⟨-, -, hcomm, -, hcase⟩ := hcl
  rcases hcase with ⟨-, P, hP, hB⟩ | ⟨-, -, P, hP, hB⟩ | ⟨-, zL, hzL, hMK⟩ | ⟨-, hMK⟩
  · exact hfromP P hP (le_pCoreOf_of_normal_pGroup
      (by rw [hB]; exact le_inf hP.1 Subgroup.le_normalizer) (by rw [hB]; exact inf_le_right)
      hP.2.1)
  · exact hfromP P hP (le_pCoreOf_of_normal_pGroup
      (by rw [hB]; exact le_inf hP.1 Subgroup.le_normalizer) (by rw [hB]; exact inf_le_right)
      hP.2.1)
  ·
    obtain ⟨hzLK, hproj⟩ := hzL
    have hzz : z * z = 1 := by rw [← pow_two]; exact ht.z_sq
    have hsq : ∀ x ∈ K, (zL * zL) * x = x * (zL * zL) := by
      intro x hx
      have hx' : zL⁻¹ * x * zL ∈ K := K.mul_mem (K.mul_mem (K.inv_mem hzLK) hx) hzLK
      have h1 := hproj x hx
      have h2 := hproj _ hx'
      have h3 : z⁻¹ * (z⁻¹ * x * z) * z = x := by
        have hinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
        rw [hinv]
        calc z * (z * x * z) * z = (z * z) * x * (z * z) := by group
          _ = x := by rw [hzz]; group
      have h4 : x = zL⁻¹ * (zL⁻¹ * x * zL) * zL :=
        calc x = z⁻¹ * (z⁻¹ * x * z) * z := h3.symm
          _ = z⁻¹ * (zL⁻¹ * x * zL) * z := by rw [h1]
          _ = zL⁻¹ * (zL⁻¹ * x * zL) * zL := h2
      calc (zL * zL) * x = (zL * zL) * (zL⁻¹ * (zL⁻¹ * x * zL) * zL) := by rw [← h4]
        _ = x * (zL * zL) := by group
    have hord : orderOf zL ≠ 0 := (orderOf_pos zL).ne'
    obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd hord
    have ha2 : (zL ^ m) ^ (2 ^ k) = 1 := by
      rw [← pow_mul, mul_comm, ← hkm]
      exact pow_orderOf_eq_one zL
    have hp : IsPGroup 2 (Subgroup.zpowers (zL ^ m)) := by
      intro g
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp g.2
      refine ⟨k, Subtype.ext ?_⟩
      show (g : G) ^ 2 ^ k = 1
      rw [← hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha2, one_zpow]
    have hle : Subgroup.zpowers (zL ^ m) ≤ M ⊓ K := by
      rw [hMK, Subgroup.zpowers_le]
      exact ⟨K.pow_mem hzLK m, Subgroup.mem_centralizer_singleton_iff.mpr
        (Commute.pow_left (Commute.refl zL) m).eq⟩
    have hn : M ⊓ K ≤ Subgroup.normalizer ((Subgroup.zpowers (zL ^ m) : Subgroup G) : Set G) := by
      intro y hy
      rw [hMK] at hy
      have hyz : Commute y zL := Subgroup.mem_centralizer_singleton_iff.mp hy.2
      refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun h hh => ?_)
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      exact ((Commute.zpow_left (hyz.pow_right m).symm i).eq)
    have hQa : Subgroup.zpowers (zL ^ m) ≤ pCoreOf 2 (M ⊓ K) :=
      le_pCoreOf_of_normal_pGroup hle hn hp
    have hA : ∀ y ∈ K, y * zL ^ m = zL ^ m * y := fun y hy =>
      hQc _ (hQa (Subgroup.mem_zpowers _)) y hy
    obtain ⟨j, hj⟩ := hm
    have hzLc : ∀ y ∈ K, y * zL = zL * y := by
      intro y hy
      have hB : Commute y (zL * zL) := (hsq y hy).symm
      have hpow : zL ^ m = (zL * zL) ^ j * zL := by rw [hj, pow_succ, pow_mul, pow_two]
      have hzL_eq : zL = ((zL * zL) ^ j)⁻¹ * zL ^ m := by
        rw [hpow, inv_mul_cancel_left]
      rw [hzL_eq]
      exact (((hB.pow_right j).inv_right).mul_right (hA y hy)).eq
    have hz_cent : ∀ x ∈ K, z * x = x * z := by
      intro x hx
      have h1 := hproj x hx
      have h2 : zL⁻¹ * x * zL = x := by
        calc zL⁻¹ * x * zL = zL⁻¹ * (x * zL) := by rw [mul_assoc]
          _ = zL⁻¹ * (zL * x) := by rw [hzLc x hx]
          _ = x := by rw [← mul_assoc, inv_mul_cancel, one_mul]
      have h3 : z⁻¹ * x * z = x := h1.trans h2
      calc z * x = z * (z⁻¹ * x * z) := by rw [h3]
        _ = x * z := by group
    have hKbot : K = ⊥ := by
      calc K = ⁅K, Subgroup.zpowers z⁆ := hcomm.symm
        _ = ⊥ := by
          refine Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun x hx => ?_
          refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
          obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
          exact (Commute.zpow_left (hz_cent x hx) i).eq
    exact Unc25G2.isComponentIn_ne_bot hK hKbot
  ·
    have hsyl : IsSylowTwoOf (S ⊓ K) K :=
      RankOneRecog.isSylowTwoOf_inf_of_subnormal ht.sylow hK.1 hK.2.2
    exact hfromP (S ⊓ K) hsyl (le_pCoreOf_of_normal_pGroup (by rw [hMK])
      (by rw [hMK]; exact Subgroup.le_normalizer) hsyl.2.1)

end Bender

theorem lemma253_of_inputs (h252 : Lemma252) (hBend : Lemma253Bender)
    (hBO : Lemma253BenderOrbit) (hLO : Lemma253ListOrbit) (hCore : Lemma253Core) :
    Lemma253Component := by
  intro G _ _ T M H₀ S z hs ht₀ k₀ B₀ hB₀ hH₀
  have key : ∀ n : ℕ, ∀ H : Subgroup G, Nat.card H = n → Tuple25 T M H S z →
      IsNormalizerIntersection H →
      ∃ K : Subgroup G, IsComponentIn K H ∧ ¬ fusionIsBenderGroup ↥K ∧
        IsComponentIn K (K ⊔ S) ∧ (IsGammaU M H → IsGammaU M (K ⊔ S)) ∧
        (IsGamma2 M H → IsGamma2 M (K ⊔ S)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro H hn ht hHn
      obtain ⟨k, B, hB, hH⟩ := hHn
      have hHn' : IsNormalizerIntersection H := ⟨k, B, hB, hH⟩
      obtain ⟨U, HU, hmaxP, hUS, hmaxU⟩ := exists_maxUPair_of_gamma0 ht.gamma0 ht.sylow_inf
      have hexists : ∃ K : Subgroup G, IsComponentIn K H :=
        exists_component_of_maximal hs.setting ht
          (fun X hSX hX => ht.le_M_of_charTwo hs hSX hX) B hB hH hmaxP.1 hUS hmaxP.2
      have hred : ∀ R : Subgroup G, R ≤ H → IsPGroup 2 R →
          S ≤ Subgroup.normalizer (R : Set G) → HU ≤ Subgroup.normalizer (R : Set G) →
          pCoreOf 2 H ≤ Subgroup.normalizer (R : Set G) → ¬ H ≤ Subgroup.normalizer (R : Set G) →
          (∀ L : Subgroup G, IsComponentIn L (H ⊓ Subgroup.normalizer (R : Set G)) →
            IsComponentIn L H) →
          ∃ K' : Subgroup G, IsComponentIn K' H ∧ ¬ fusionIsBenderGroup ↥K' ∧
            IsComponentIn K' (K' ⊔ S) ∧ (IsGammaU M H → IsGammaU M (K' ⊔ S)) ∧
            (IsGamma2 M H → IsGamma2 M (K' ⊔ S)) := by
        intro R hRH hR2 hSR hHUR hOR hne hbridge
        obtain ⟨hX, hXn, c1, c2, hlt⟩ := reduction_step hs.setting ht hHn' hmaxP hmaxU hRH hR2
          hSR hHUR hOR hne
        obtain ⟨K', hK'X, hK'B, hK'c, h1, h2⟩ := ih _ (hn ▸ hlt) _ rfl hX hXn
        exact ⟨K', hbridge K' hK'X, hK'B, hK'c, fun hU => h1 (c1 hU), fun h2' => h2 (c2 h2')⟩
      by_cases hBe : ∃ L : Subgroup G, IsComponentIn L H ∧ fusionIsBenderGroup ↥L
      · obtain ⟨L, hL, hLB⟩ := hBe
        exact hred _ (benderRadical_le hL.1) (isPGroup_benderRadical ht.sylow.isPGroup H L)
          (le_normalizer_benderRadical_self ht)
          (le_normalizer_benderRadical_of_bender hBend hs ht B hB hH hmaxP hUS hL hLB)
          (pCoreOf_le_normalizer_of_le_conjJoin hL (benderRadical_le_conjJoin S H L))
          (not_le_normalizer_benderRadical ht hL) (hBO G T M H S z hs ht L hL hLB)
      · push Not at hBe
        by_cases hI : ∃ K : Subgroup G, IsComponentIn K H ∧
            HU ≤ Subgroup.normalizer (radicalOf M H K : Set G)
        · obtain ⟨K, hK, hKR⟩ := hI
          have hcl : ComponentList M S z K := h252 G T M H S z hs ht K hK
          exact hred _ (radicalOf_le hK.1) (isPGroup_radicalOf M H K)
            (le_normalizer_radicalOf ht.le_H ht.le_M) hKR
            (pCoreOf_le_normalizer_of_le_conjJoin hK (radicalOf_le_conjJoin M H K))
            (fun hHR => not_le_normalizer_radicalOf ht hK hcl
              ((conjJoin_le_self hK.1).trans hHR))
            (hLO G T M H S z hs ht K hK (hBe K hK))
        · push Not at hI
          obtain ⟨K, U₁, HU₁, hK, hpair, hHU, hmax₁⟩ := hCore G T M H S z U HU hs ht hHn' hmaxP
            hUS hmaxU hexists hBe hI
          exact ⟨K, lemma253_conclusion_of_witness hs.setting ht hK (hBe K hK) hpair hHU hmax₁⟩
  exact key _ H₀ rfl ht₀ ⟨k₀, B₀, hB₀, hH₀⟩

end CFSG.QuasithinUnique
