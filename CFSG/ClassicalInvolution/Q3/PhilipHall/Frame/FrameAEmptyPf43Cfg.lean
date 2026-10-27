module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf49G3At
public import CFSG.ClassicalInvolution.Asc77.AscT7V1
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf51Ambient

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameSimple)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.ClassicalInvolution.Asc77.T3Core
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ComponentClassification.AS76b
  CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.Q3T6D
open scoped commutatorElement

section Defs

variable {T : Type} [Group T]

@[expose] def oddTwoCoreIn (H : Subgroup T) : Subgroup T :=
  ((CFSG.pCore 2 (SecQuot H)).comap
    (QuotientGroup.mk' (classicalInvolutionOddCore ↥H))).map H.subtype

@[expose] def sigmaOf (K : Subgroup T) : Set (Subgroup T) :=
  dstarComp (CoreAssembly.conjClass K) K

@[expose] def sigmaGen (K : Subgroup T) : Subgroup T := omegaGen (sigmaOf K)

@[expose] def sigmaNorm (K : Subgroup T) : Subgroup T :=
  Subgroup.normalizer (sigmaGen K : Set T)

@[expose] def firstFactor (K : Subgroup T) : Subgroup T :=
  omegaGen (aStar (CoreAssembly.conjClass K) K) ⊔ oddCoreOf (sigmaGen K)

end Defs

section Cfg

structure FrameStd {T : Type} [Group T] (K : Subgroup T) (z : T) (J : Subgroup T) (zJ : T) :
    Prop where
  nonabelian : ∃ a b : T, a * b ≠ b * a
  datum : FrameTightDatum K z
  viol : AViol (CoreAssembly.conjClass K) K J z zJ
  ne : aStar (CoreAssembly.conjClass K) K ≠ CoreAssembly.conjClass K
  below : Thm3A.Thm3RBelowG (Nat.card T)

structure FrameCfg {T : Type} [Group T] [Finite T] (K : Subgroup T) (z : T) (J : Subgroup T)
    (zJ : T) (S : Subgroup T) : Prop extends FrameStd K z J zJ where
  sigma_ne : sigmaOf K ≠ CoreAssembly.conjClass K
  hs_stab : sigmaGen K ≤ conjStab (aStar (CoreAssembly.conjClass K) K)
  hS : IsSylow2In S (sigmaNorm K)
  hzS : z ∈ S

structure FrameQCfg {T : Type} [Group T] [Finite T] (K : Subgroup T) (z : T) (J : Subgroup T)
    (zJ : T) (Q E S : Subgroup T) : Prop extends FrameCfg K z J zJ S where
  hQ : Q = oddTwoCoreIn (firstFactor K)
  hE : E = Q ⊓ S

structure EFacts {T : Type} [Group T] (K : Subgroup T) (z : T) (E : Subgroup T) : Prop where
  z_mem : z ∈ E
  conj : ∀ e ∈ E, e * e = 1 → e ≠ 1 → ∃ l ∈ firstFactor K, l⁻¹ * z * l = e

end Cfg

section Sigma

variable {T : Type} [Group T] {K : Subgroup T}

theorem sigmaStarNorm_le_sigmaNorm (K : Subgroup T) :
    sigmaStarNorm (CoreAssembly.conjClass K) K ≤ sigmaNorm K := by
  intro g hg
  have : g ∈ conjStab (dstarComp (CoreAssembly.conjClass K) K) := by
    intro M
    exact (mem_sigmaStarNorm_iff.mp hg M).symm
  exact conjStab_le_normalizer_omegaGen _ this

theorem sigmaGen_le_sigmaStarNorm (hΩ : ConjInvariant (CoreAssembly.conjClass K)) :
    sigmaGen K ≤ sigmaStarNorm (CoreAssembly.conjClass K) K := by
  refine iSup₂_le fun M hM x hx => ?_
  have hx' := mem_conjStab_dstarComp hΩ (CoreAssembly.mem_conjClass_self K) hM
    (conjSub_eq_self_of_mem hx)
  exact fun N => (mem_conjStab_iff.mp hx' N).symm

theorem sigmaGen_ne_top (hΩ : ConjInvariant (CoreAssembly.conjClass K))
    (hσ : sigmaOf K ≠ CoreAssembly.conjClass K) : sigmaGen K ≠ ⊤ := by
  intro h
  apply hσ
  have hle := sigmaGen_le_sigmaStarNorm hΩ
  have htop : sigmaStarNorm (CoreAssembly.conjClass K) K = ⊤ := top_le_iff.mp (h ▸ hle)
  refine Set.Subset.antisymm (fun J hJ => (mem_dstarComp_symm
    (CoreAssembly.mem_conjClass_self K) hJ).1) ?_
  rintro _ ⟨g, rfl⟩
  have hg : g ∈ sigmaStarNorm (CoreAssembly.conjClass K) K := htop ▸ Subgroup.mem_top g
  exact (mem_sigmaStarNorm_iff.mp hg K).mp Relation.ReflTransGen.refl

theorem omegaNbr_subset_omegaStarNbr_gen [Finite T] {Ω : Set (Subgroup T)} (hΩ : HypOmegaGen Ω)
    (K : Subgroup T) : omegaNbr Ω K ⊆ omegaStarNbr Ω K := by
  rintro J ⟨hJ, hJK, R, hR, hRJ, hRN⟩
  obtain ⟨U, hUR, hUc, hcard⟩ := (Sec6Gen.isQuatSub_of_mem_RSet hΩ hR).exists_cyclic_index_two
  have hrel : U.relIndex R = 2 := by
    have h1 := Subgroup.relIndex_mul_card U R
    rw [inf_eq_left.mpr hUR, hcard] at h1
    have hU0 : 0 < Nat.card U := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hU0 h1
  exact ⟨hJ, hJK, U, ⟨R, hR, hUR, hUc, hrel⟩, hUR.trans hRJ, hUR.trans hRN⟩

theorem aStar_subset_dstarComp_gen [Finite T] {Ω : Set (Subgroup T)} (hΩ : HypOmegaGen Ω)
    {K : Subgroup T} (hK : K ∈ Ω) {J : Subgroup T} (hJ : J ∈ aStar Ω K) :
    J ∈ Ω ∧ J ∈ dstarComp Ω K := by
  induction hJ with
  | refl => exact ⟨hK, Relation.ReflTransGen.refl⟩
  | @tail b c _ hbc ih =>
    obtain ⟨hbΩ, hbd⟩ := ih
    obtain ⟨hcΩ, hA | hA | ⟨htw, hne⟩⟩ := hbc
    · obtain ⟨zb, zc, hv⟩ := hA
      exact ⟨hcΩ, hbd.tail ⟨hcΩ, Or.inl hv.star⟩⟩
    · obtain ⟨zc, zb, hv⟩ := hA
      exact ⟨hcΩ, hbd.tail ⟨hcΩ, Or.inr hv.star⟩⟩
    · obtain ⟨-, z, hzb, hzc⟩ := htw
      exact ⟨hcΩ, hbd.tail ⟨hcΩ, Or.inl (omegaNbr_subset_omegaStarNbr_gen hΩ b
        (Q3CL.T3.twin_mem_omegaNbr hΩ hbΩ hcΩ hne hzb hzc))⟩⟩

theorem firstFactor_le_sigmaGen [Finite T] (hΩ : HypOmegaGen (CoreAssembly.conjClass K)) :
    firstFactor K ≤ sigmaGen K := by
  refine sup_le (iSup₂_le fun M hM => ?_) (oddCoreOf_le_self _)
  exact le_omegaGen (aStar_subset_dstarComp_gen hΩ (CoreAssembly.mem_conjClass_self K) hM).2

theorem mem_normalizer_firstFactor {x : T}
    (hx : x ∈ conjStab (aStar (CoreAssembly.conjClass K) K)) (hxM : x ∈ sigmaNorm K) :
    x ∈ Subgroup.normalizer (firstFactor K : Set T) := by
  rw [mem_normalizer_iff_conjSub_eq]
  have h1 : conjSub x (omegaGen (aStar (CoreAssembly.conjClass K) K)) =
      omegaGen (aStar (CoreAssembly.conjClass K) K) :=
    mem_normalizer_iff_conjSub_eq.mp (conjStab_le_normalizer_omegaGen _ hx)
  have h2 : conjSub x (oddCoreOf (sigmaGen K)) = oddCoreOf (sigmaGen K) :=
    Asc77.T7V.conjSub_oddCoreOf_eq_of_mem_normalizer hxM
  unfold firstFactor
  rw [conjSub_sup, h1, h2]

theorem sigmaGen_le_normalizer_firstFactor
    (hst : sigmaGen K ≤ conjStab (aStar (CoreAssembly.conjClass K) K)) :
    sigmaGen K ≤ Subgroup.normalizer (firstFactor K : Set T) :=
  fun x hx => mem_normalizer_firstFactor (hst hx) (Subgroup.le_normalizer hx)

theorem conjStab_aStar_le_sigmaNorm [Finite T] (hΩ : HypOmegaGen (CoreAssembly.conjClass K)) :
    conjStab (aStar (CoreAssembly.conjClass K) K) ≤ sigmaNorm K := by
  intro g hg
  have hK := CoreAssembly.mem_conjClass_self K
  have h1 : conjSub g K ∈ aStar (CoreAssembly.conjClass K) K :=
    (mem_conjStab_iff.mp hg K).mpr Relation.ReflTransGen.refl
  have h2 := (aStar_subset_dstarComp_gen hΩ hK h1).2
  exact sigmaStarNorm_le_sigmaNorm K (T7A.mem_sigmaStarNorm_of_conj hΩ.conjInvariant hK h2)

theorem centralizer_le_sigmaNorm [Finite T] {z : T}
    (hΩ : HypOmegaGen (CoreAssembly.conjClass K)) (hz : IsUniqueInvolution K z) :
    Subgroup.centralizer ({z} : Set T) ≤ sigmaNorm K := by
  intro c hc
  have hK : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  have hcz : c * z * c⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hc
    rw [this]
    group
  have hzc : IsUniqueInvolution (conjSub c K) z := by
    have := hz.conj c
    rwa [hcz] at this
  have hmem : conjSub c K ∈ dstarComp (CoreAssembly.conjClass K) K := by
    by_cases he : conjSub c K = K
    · rw [he]
      exact Relation.ReflTransGen.refl
    · have hcΩ : conjSub c K ∈ CoreAssembly.conjClass K := hΩ.conjInvariant c K hK
      have hnbr := Q3CL.T3.twin_mem_omegaNbr hΩ hK hcΩ he hz hzc
      exact Relation.ReflTransGen.single ⟨hcΩ, Or.inl (omegaNbr_subset_omegaStarNbr_gen hΩ K hnbr)⟩
  exact sigmaStarNorm_le_sigmaNorm K
    (T7A.mem_sigmaStarNorm_of_conj hΩ.conjInvariant hK hmem)

theorem normalizer_le_normalizer_oddTwoCoreIn (H : Subgroup T) :
    Subgroup.normalizer (H : Set T) ≤ Subgroup.normalizer (oddTwoCoreIn H : Set T) := by
  have key : ∀ g ∈ Subgroup.normalizer (H : Set T), ∀ x ∈ oddTwoCoreIn H,
      g * x * g⁻¹ ∈ oddTwoCoreIn H := by
    intro g hg x hx
    have hg' : ∀ h : T, h ∈ H ↔ g * h * g⁻¹ ∈ H := Subgroup.mem_normalizer_iff.mp hg
    have hgi : ∀ h : T, h ∈ H ↔ g⁻¹ * h * g⁻¹⁻¹ ∈ H :=
      Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (H : Set T)).inv_mem hg)
    let φ : ↥H ≃* ↥H :=
      { toFun := fun h => ⟨g * (h : T) * g⁻¹, (hg' h).mp h.2⟩
        invFun := fun h => ⟨g⁻¹ * (h : T) * g, by
          have := (hgi h).mp h.2
          simpa using this⟩
        left_inv := fun h => Subtype.ext (by
          show g⁻¹ * (g * (h : T) * g⁻¹) * g = h
          group)
        right_inv := fun h => Subtype.ext (by
          show g * (g⁻¹ * (h : T) * g) * g⁻¹ = h
          group)
        map_mul' := fun h k => Subtype.ext (by
          show g * ((h : T) * (k : T)) * g⁻¹ = g * (h : T) * g⁻¹ * (g * (k : T) * g⁻¹)
          group) }
    have hO : (classicalInvolutionOddCore ↥H).map φ.toMonoidHom = classicalInvolutionOddCore ↥H :=
      CFSG.ComponentClassification.OddCore.equiv_invariant φ
    let ψ : SecQuot H ≃* SecQuot H :=
      QuotientGroup.congr (classicalInvolutionOddCore ↥H) (classicalInvolutionOddCore ↥H) φ hO
    unfold oddTwoCoreIn at hx ⊢
    obtain ⟨y, hy, rfl⟩ := hx
    have hy' : QuotientGroup.mk' (classicalInvolutionOddCore ↥H) (φ y) ∈
        CFSG.pCore 2 (SecQuot H) := by
      have h1 : ψ.toMonoidHom (QuotientGroup.mk' (classicalInvolutionOddCore ↥H) y) ∈
          (CFSG.pCore 2 (SecQuot H)).map ψ.toMonoidHom :=
        Subgroup.mem_map_of_mem _ (Subgroup.mem_comap.mp hy)
      rw [CFSG.pCore_map_iso] at h1
      have h2 : ψ.toMonoidHom (QuotientGroup.mk' (classicalInvolutionOddCore ↥H) y) =
          QuotientGroup.mk' (classicalInvolutionOddCore ↥H) (φ y) :=
        QuotientGroup.congr_mk' _ _ φ hO y
      rw [h2] at h1
      exact h1
    exact Subgroup.mem_map.mpr ⟨φ y, Subgroup.mem_comap.mpr hy', rfl⟩
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key g hg x, fun h => ?_⟩
  have h1 := key g⁻¹ ((Subgroup.normalizer (H : Set T)).inv_mem hg) _ h
  have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
  rwa [e] at h1

theorem tightlyEmbedded_of_conj [Finite T] {Ω : Set (Subgroup T)} {Λ : Subgroup T} {z : T}
    (hΩ : ConjInvariant Ω) (hK : K ∈ Ω) (hz : IsUniqueInvolution K z) (hzΛ : z ∈ Λ)
    (hΛN : ∀ g ∈ conjStab (aStar Ω K), g ∈ Subgroup.normalizer (Λ : Set T))
    (hconj : ∀ x ∈ Λ, x * x = 1 → x ≠ 1 → ∃ h ∈ conjStab (aStar Ω K), h * z * h⁻¹ = x) :
    TightlyEmbedded Λ := by
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one
  refine ⟨even_iff_two_dvd.mpr (hz2 ▸ Subgroup.orderOf_dvd_natCard Λ hzΛ), fun g hg => ?_⟩
  by_contra hnot
  have heven : Even (Nat.card ↥(Λ ⊓ rightConjugate Λ g)) := Nat.not_odd_iff_even.mp hnot
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp heven)
  have hx' : orderOf (x : T) = 2 := (Subgroup.orderOf_coe x).trans hx
  have hx2 : (x : T) * (x : T) = 1 := by rw [← pow_two]; exact hx' ▸ pow_orderOf_eq_one _
  have hx1 : (x : T) ≠ 1 := fun h => by rw [h, orderOf_one] at hx'; omega
  have hxH : (x : T) ∈ Λ := (Subgroup.mem_inf.mp x.2).1
  have hxg : g * (x : T) * g⁻¹ ∈ Λ :=
    (mem_rightConjugate_iff Λ g x).mp (Subgroup.mem_inf.mp x.2).2
  have hy2 : (g * (x : T) * g⁻¹) * (g * (x : T) * g⁻¹) = 1 := by
    calc (g * (x : T) * g⁻¹) * (g * (x : T) * g⁻¹) = g * ((x : T) * (x : T)) * g⁻¹ := by group
      _ = 1 := by rw [hx2]; group
  have hy1 : g * (x : T) * g⁻¹ ≠ 1 := fun h => hx1 (by
    have := congrArg (fun w => g⁻¹ * w * g) h
    simpa [mul_assoc] using this)
  obtain ⟨h, hh, hhx⟩ := hconj x hxH hx2 hx1
  obtain ⟨h', hh', hh'y⟩ := hconj _ hxg hy2 hy1
  have hc : h'⁻¹ * g * h * z * (h'⁻¹ * g * h)⁻¹ = z := by
    calc h'⁻¹ * g * h * z * (h'⁻¹ * g * h)⁻¹
        = h'⁻¹ * (g * (h * z * h⁻¹) * g⁻¹) * h' := by group
      _ = h'⁻¹ * (g * (x : T) * g⁻¹) * h' := by rw [hhx]
      _ = h'⁻¹ * (h' * z * h'⁻¹) * h' := by rw [hh'y]
      _ = z := by group
  have hcz : h'⁻¹ * g * h ∈ Subgroup.centralizer ({z} : Set T) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact mul_inv_eq_iff_eq_mul.mp hc
  have hmem : g ∈ conjStab (aStar Ω K) := by
    have e : g = h' * (h'⁻¹ * g * h) * h⁻¹ := by group
    rw [e]
    exact (conjStab (aStar Ω K)).mul_mem
      ((conjStab (aStar Ω K)).mul_mem hh' (centralizer_le_conjStab_aStar hΩ hK hz hcz))
      ((conjStab (aStar Ω K)).inv_mem hh)
  exact hg (hΛN g hmem)

theorem dstarComp_of_centralizes [Finite T] {Ω : Set (Subgroup T)} (hΩ : HypOmegaGen Ω)
    {K₁ K₂ : Subgroup T} (hK₁ : K₁ ∈ Ω) (hK₂ : K₂ ∈ Ω) {u : T} (hu : IsUniqueInvolution K₂ u)
    {X : Subgroup T} (hX : X ∈ USet Ω) (hXK : X ≤ K₁)
    (hc : X ≤ Subgroup.centralizer ({u} : Set T)) : K₁ ∈ dstarComp Ω K₂ := by
  by_cases h : K₁ = K₂
  · rw [h]
    exact Relation.ReflTransGen.refl
  · obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hX
    have hX2 := Sec6Gen.isPGroup_of_mem_USet hΩ hX
    have hN : X ≤ Subgroup.normalizer (K₂ : Set T) :=
      Sec6Gen.le_normalizer_of_le_centralizer hΩ hK₂ hK₁ (Ne.symm h) hu hXK hX2 (by omega) hc
    exact Relation.ReflTransGen.single ⟨hK₁, Or.inl ⟨hK₁, h, X, hX, hXK, hN⟩⟩

private theorem exists_conj_commute_aux {G : Type} [Group G] [Finite G] {N : Subgroup G} [N.Normal]
    (hN : Odd (Nat.card N)) {a b : G} (ha : IsPGroup 2 (Subgroup.zpowers a))
    (hb : IsPGroup 2 (Subgroup.zpowers b)) (hab : a * b * a⁻¹ * b⁻¹ ∈ N) :
    ∃ n ∈ N, a * (n * b * n⁻¹) = (n * b * n⁻¹) * a := by
  have hpow : ∀ v ∈ Subgroup.zpowers a, v * b * v⁻¹ * b⁻¹ ∈ N := by
    intro v hv
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    have h0 : QuotientGroup.mk' N (a * b * a⁻¹ * b⁻¹) = 1 := (QuotientGroup.eq_one_iff _).mpr hab
    have hcomm : Commute (QuotientGroup.mk' N a) (QuotientGroup.mk' N b) := by
      simp only [map_mul, map_inv] at h0
      exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h0)
    have hcomm' := hcomm.zpow_left i
    have h1 : QuotientGroup.mk' N (a ^ i * b * (a ^ i)⁻¹ * b⁻¹) = 1 := by
      simp only [map_mul, map_inv, map_zpow]
      rw [hcomm'.eq]
      simp
    exact (QuotientGroup.eq_one_iff _).mp h1
  have hodd1 : ∀ y ∈ N, IsPGroup 2 (Subgroup.zpowers y) → y = 1 := fun y hy hy2 =>
    eq_one_of_isPGroup_of_mem_odd hN hy hy2
  have hBM : Subgroup.zpowers b ≤ N ⊔ Subgroup.zpowers b := le_sup_right
  have hNM : N ≤ N ⊔ Subgroup.zpowers b := le_sup_left
  have hBsyl : IsSylow2In (Subgroup.zpowers b) (N ⊔ Subgroup.zpowers b) := by
    refine ⟨hBM, hb, fun V' hV'M hV'2 hBV' => ?_⟩
    refine le_antisymm ?_ hBV'
    intro y hy
    obtain ⟨m, hm, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp (hV'M hy)
    have hcV : c ∈ V' := hBV' hc
    have hmV : m ∈ V' := by
      have := V'.mul_mem hy (V'.inv_mem hcV)
      simpa using this
    have hm1 : m = 1 := hodd1 m hm (hV'2.to_le (Subgroup.zpowers_le.mpr hmV))
    rw [hm1, one_mul]
    exact hc
  have hperm : ∀ v ∈ Subgroup.zpowers a, ∃ n ∈ N,
      conjSub v (Subgroup.zpowers b) = conjSub n (Subgroup.zpowers b) := by
    intro v hv
    have hvb : v * b * v⁻¹ * b⁻¹ ∈ N := hpow v hv
    have hvB : v * b * v⁻¹ ∈ N ⊔ Subgroup.zpowers b := by
      have e : v * b * v⁻¹ = (v * b * v⁻¹ * b⁻¹) * b := by group
      rw [e]
      exact (N ⊔ Subgroup.zpowers b).mul_mem (hNM hvb) (hBM (Subgroup.mem_zpowers b))
    have hconjB : conjSub v (Subgroup.zpowers b) = Subgroup.zpowers (v * b * v⁻¹) := by
      show Subgroup.map (MulAut.conj v).toMonoidHom (Subgroup.zpowers b) = _
      rw [MonoidHom.map_zpowers] <;> rfl
    have hle : conjSub v (Subgroup.zpowers b) ≤ N ⊔ Subgroup.zpowers b := by
      rw [hconjB]
      exact Subgroup.zpowers_le.mpr hvB
    have hcard : Nat.card (Subgroup.zpowers b) ≤ Nat.card (conjSub v (Subgroup.zpowers b)) :=
      (Nat.card_congr (Subgroup.equivMapOfInjective (Subgroup.zpowers b)
        (MulAut.conj v).toMonoidHom (MulAut.conj v).injective).toEquiv).le
    have hBv : IsSylow2In (conjSub v (Subgroup.zpowers b)) (N ⊔ Subgroup.zpowers b) :=
      hBsyl.of_natCard_le (isPGroup_conjSub v hb) hle hcard
    obtain ⟨x, hxM, hx⟩ := exists_conjSub_eq_of_isSylow2In hBsyl hBv
    obtain ⟨m, hm, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hxM
    refine ⟨m, hm, ?_⟩
    rw [← hx, conjSub_mul, conjSub_eq_self_of_mem hc]
  obtain ⟨n, hn, hnor⟩ := exists_conj_normalizer_of_perm hN (Subgroup.zpowers b) ha hperm
  refine ⟨n, hn, ?_⟩
  have hb'B : n * b * n⁻¹ ∈ conjSub n (Subgroup.zpowers b) :=
    conj_mem_conjSub (Subgroup.mem_zpowers b)
  have haN' : a ∈ Subgroup.normalizer ((conjSub n (Subgroup.zpowers b) : Subgroup G) : Set G) :=
    hnor (Subgroup.mem_zpowers a)
  have h1 : a * (n * b * n⁻¹) * a⁻¹ ∈ conjSub n (Subgroup.zpowers b) :=
    (Subgroup.mem_normalizer_iff.mp haN' (n * b * n⁻¹)).mp hb'B
  have h2 : a * (n * b * n⁻¹) * a⁻¹ * (n * b * n⁻¹)⁻¹ ∈ conjSub n (Subgroup.zpowers b) :=
    (conjSub n (Subgroup.zpowers b)).mul_mem h1 ((conjSub n (Subgroup.zpowers b)).inv_mem hb'B)
  have h3 : a * (n * b * n⁻¹) * a⁻¹ * (n * b * n⁻¹)⁻¹ ∈ N := by
    have hn₁ : a * n * a⁻¹ ∈ N := ‹N.Normal›.conj_mem n hn a
    have hbn₁ : b * (a * n * a⁻¹)⁻¹ * b⁻¹ ∈ N := ‹N.Normal›.conj_mem _ (N.inv_mem hn₁) b
    have hbn : b * n * b⁻¹ ∈ N := ‹N.Normal›.conj_mem n hn b
    have e : a * (n * b * n⁻¹) * a⁻¹ * (n * b * n⁻¹)⁻¹ =
        (a * n * a⁻¹) * (a * b * a⁻¹ * b⁻¹) * (b * (a * n * a⁻¹)⁻¹ * b⁻¹) * (b * n * b⁻¹) *
          n⁻¹ := by group
    rw [e]
    exact N.mul_mem (N.mul_mem (N.mul_mem (N.mul_mem hn₁ hab) hbn₁) hbn) (N.inv_mem hn)
  have h4 : a * (n * b * n⁻¹) * a⁻¹ * (n * b * n⁻¹)⁻¹ = 1 :=
    eq_one_of_isPGroup_of_mem_odd hN h3
      ((isPGroup_conjSub n hb).to_le (Subgroup.zpowers_le.mpr h2))
  exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h4)

theorem exists_conj_commute_of_commutator_mem_odd [Finite T] {N : Subgroup T}
    (hN : Odd (Nat.card N)) {a b : T} (ha : IsPGroup 2 (Subgroup.zpowers a))
    (hb : IsPGroup 2 (Subgroup.zpowers b)) (haN : a ∈ Subgroup.normalizer (N : Set T))
    (hbN : b ∈ Subgroup.normalizer (N : Set T)) (hab : a * b * a⁻¹ * b⁻¹ ∈ N) :
    ∃ n ∈ N, a * (n * b * n⁻¹) = (n * b * n⁻¹) * a := by
  have hle : N ≤ Subgroup.normalizer (N : Set T) := Subgroup.le_normalizer
  haveI : (N.subgroupOf (Subgroup.normalizer (N : Set T))).Normal := Subgroup.normal_in_normalizer
  have hN₁ : Odd (Nat.card ↥(N.subgroupOf (Subgroup.normalizer (N : Set T)))) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
    exact hN
  have hpg : ∀ (c : T) (hc : c ∈ Subgroup.normalizer (N : Set T)),
      IsPGroup 2 (Subgroup.zpowers c) →
      IsPGroup 2 (Subgroup.zpowers (⟨c, hc⟩ : ↥(Subgroup.normalizer (N : Set T)))) := by
    intro c hc hc2
    obtain ⟨m, hm⟩ := hc2.exists_card_eq
    refine IsPGroup.of_card (n := m) ?_
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, ← Nat.card_zpowers]
    exact hm
  obtain ⟨n₁, hn₁, h⟩ :=
    exists_conj_commute_aux (N := N.subgroupOf (Subgroup.normalizer (N : Set T)))
      (a := ⟨a, haN⟩) (b := ⟨b, hbN⟩) hN₁ (hpg a haN ha) (hpg b hbN hb)
      (Subgroup.mem_subgroupOf.mpr hab)
  exact ⟨(n₁ : T), Subgroup.mem_subgroupOf.mp hn₁, congrArg Subtype.val h⟩

end Sigma

namespace FrameCfg

variable {T : Type} [Group T] [Finite T] {K : Subgroup T} {z : T} {J : Subgroup T} {zJ : T}
  {S : Subgroup T}

theorem ht_le (cfg : FrameCfg K z J zJ S) : firstFactor K ≤ sigmaGen K :=
  firstFactor_le_sigmaGen cfg.datum.hyp

theorem hs_le_normalizer_ht (cfg : FrameCfg K z J zJ S) :
    sigmaGen K ≤ Subgroup.normalizer (firstFactor K : Set T) :=
  sigmaGen_le_normalizer_firstFactor cfg.hs_stab

theorem ht_le_sigmaNorm (cfg : FrameCfg K z J zJ S) : firstFactor K ≤ sigmaNorm K :=
  cfg.ht_le.trans Subgroup.le_normalizer

theorem cz_le (cfg : FrameCfg K z J zJ S) :
    Subgroup.centralizer ({z} : Set T) ≤ sigmaNorm K :=
  centralizer_le_sigmaNorm cfg.datum.hyp cfg.datum.unique

theorem sigmaNorm_ne_top (cfg : FrameCfg K z J zJ S) : sigmaNorm K ≠ ⊤ := fun h =>
  sigmaGen_ne_top cfg.datum.hyp.conjInvariant cfg.sigma_ne
    (cfg.datum.eq_top_of_normal (Subgroup.normalizer_eq_top_iff.mp h)
      (le_omegaGen (Relation.ReflTransGen.refl : K ∈ sigmaOf K)))

theorem cz_le_normalizer_ht (cfg : FrameCfg K z J zJ S) :
    Subgroup.centralizer ({z} : Set T) ≤ Subgroup.normalizer (firstFactor K : Set T) :=
  fun _ hc => mem_normalizer_firstFactor (centralizer_le_conjStab_aStar
    cfg.datum.hyp.conjInvariant (CoreAssembly.mem_conjClass_self K) cfg.datum.unique hc) (cfg.cz_le hc)

theorem unique_of_S (cfg : FrameCfg K z J zJ S) {a : T} (ha2 : orderOf a = 2)
    (h : ∀ g : T, g ∉ sigmaNorm K → g⁻¹ * a * g ∈ S → False) {x : T}
    (hx : x⁻¹ * a * x ∈ sigmaNorm K) : x ∈ sigmaNorm K := by
  by_contra hxM
  have hy2 : orderOf (x⁻¹ * a * x) = 2 := by
    have : x⁻¹ * a * x = MulAut.conj x⁻¹ a := by rw [MulAut.conj_apply, inv_inv]
    rw [this, MulEquiv.orderOf_eq, ha2]
  obtain ⟨m, hm, hmS⟩ :=
    CFSG.StronglyEmbedded.UniqueCoset.exists_conj_mem_of_isSylow2In cfg.hS hx hy2
  have hg : x * m ∉ sigmaNorm K := fun h =>
    hxM (by simpa using (sigmaNorm K).mul_mem h ((sigmaNorm K).inv_mem hm))
  refine h (x * m) hg ?_
  have : (x * m)⁻¹ * a * (x * m) = m⁻¹ * (x⁻¹ * a * x) * m := by group
  rw [this]
  exact hmS

theorem cent_of_mod_odd (cfg : FrameCfg K z J zJ S) {u x k : T} {R₀ : Subgroup T}
    (hu2 : u * u = 1) (huN : u ∈ Subgroup.normalizer (firstFactor K : Set T))
    (hx : x ∈ firstFactor K) (hR₀ : IsSylow2In R₀ K) (hk : k ∈ R₀) (hk4 : orderOf k = 4)
    (hc : u * (x * k * x⁻¹) * u⁻¹ * (x * k * x⁻¹)⁻¹ ∈ oddCoreOf (firstFactor K)) :
    ∃ M' ∈ sigmaOf K, ∃ X' ∈ USet (CoreAssembly.conjClass K), X' ≤ M' ∧
      X' ≤ Subgroup.centralizer ({u} : Set T) := by
  have hΩ := cfg.datum.hyp
  have hKΩ : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  have hKHt : K ≤ firstFactor K :=
    (le_omegaGen (Relation.ReflTransGen.refl :
      K ∈ aStar (CoreAssembly.conjClass K) K)).trans le_sup_left
  have hkHt : k ∈ firstFactor K := hKHt (hR₀.1 hk)
  have hbHt : x * k * x⁻¹ ∈ firstFactor K :=
    (firstFactor K).mul_mem ((firstFactor K).mul_mem hx hkHt) ((firstFactor K).inv_mem hx)
  have hN : Odd (Nat.card (oddCoreOf (firstFactor K))) := oddCoreOf_odd_natCard _
  have hu_p : IsPGroup 2 (Subgroup.zpowers u) := by
    have hdvd : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hu2)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
  have hconj_ord : ∀ c : T, orderOf (c * k * c⁻¹) = 4 := by
    intro c
    have e : c * k * c⁻¹ = MulAut.conj c k := by rw [MulAut.conj_apply]
    rw [e, MulEquiv.orderOf_eq, hk4]
  have hb_p : IsPGroup 2 (Subgroup.zpowers (x * k * x⁻¹)) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hconj_ord x] <;> norm_num)
  have huN' : u ∈ Subgroup.normalizer (oddCoreOf (firstFactor K) : Set T) :=
    mem_normalizer_iff_conjSub_eq.mpr (Asc77.T7V.conjSub_oddCoreOf_eq_of_mem_normalizer huN)
  have hbN' : x * k * x⁻¹ ∈ Subgroup.normalizer (oddCoreOf (firstFactor K) : Set T) :=
    mem_normalizer_iff_conjSub_eq.mpr
      (Asc77.T7V.conjSub_oddCoreOf_eq_of_mem_normalizer (Subgroup.le_normalizer hbHt))
  obtain ⟨n, hn, hcomm⟩ :=
    exists_conj_commute_of_commutator_mem_odd hN hu_p hb_p huN' hbN' hc
  have hcHt : n * x ∈ firstFactor K :=
    (firstFactor K).mul_mem (oddCoreOf_le_self _ hn) hx
  have hst : n * x ∈ conjStab (aStar (CoreAssembly.conjClass K) K) :=
    cfg.hs_stab (cfg.ht_le hcHt)
  have hM : conjSub (n * x) K ∈ aStar (CoreAssembly.conjClass K) K :=
    (mem_conjStab_iff.mp hst K).mpr Relation.ReflTransGen.refl
  have hMS : conjSub (n * x) K ∈ sigmaOf K :=
    (aStar_subset_dstarComp_gen hΩ hKΩ hM).2
  have hMΩ : conjSub (n * x) K ∈ CoreAssembly.conjClass K :=
    hΩ.conjInvariant (n * x) K hKΩ
  have e : n * (x * k * x⁻¹) * n⁻¹ = (n * x) * k * (n * x)⁻¹ := by group
  have h8 : Nat.card R₀ = 8 := by
    obtain ⟨e8⟩ := cfg.datum.quat R₀ hR₀
    rw [Nat.card_congr e8.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hcardR : Nat.card (conjSub (n * x) R₀) = 8 := by
    have h1 : Nat.card ↥(conjSub (n * x) R₀) = Nat.card R₀ :=
      (Nat.card_congr (Subgroup.equivMapOfInjective R₀ (MulAut.conj (n * x)).toMonoidHom
        (MulAut.conj (n * x)).injective).toEquiv).symm
    rw [h1, h8]
  have hXcard : Nat.card (Subgroup.zpowers ((n * x) * k * (n * x)⁻¹)) = 4 := by
    rw [Nat.card_zpowers, hconj_ord]
  have hkR : (n * x) * k * (n * x)⁻¹ ∈ conjSub (n * x) R₀ := conj_mem_conjSub hk
  refine ⟨conjSub (n * x) K, hMS, Subgroup.zpowers ((n * x) * k * (n * x)⁻¹), ?_, ?_, ?_⟩
  · refine mem_USet_of_natCard hMΩ (hR₀.conj (n * x)) (Subgroup.zpowers_le.mpr hkR)
      inferInstance ?_
    omega
  · exact (Subgroup.zpowers_le.mpr hkR).trans (conjSub_mono hR₀.1)
  · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff, ← e]
    exact hcomm.symm

end FrameCfg

namespace FrameQCfg

variable {T : Type} [Group T] [Finite T] {K : Subgroup T} {z : T} {J : Subgroup T} {zJ : T}
  {Q E S : Subgroup T}

theorem E_le_Q (cfg : FrameQCfg K z J zJ Q E S) : E ≤ Q := by
  rw [cfg.hE]
  exact inf_le_left

theorem E_le_S (cfg : FrameQCfg K z J zJ Q E S) : E ≤ S := by
  rw [cfg.hE]
  exact inf_le_right

theorem Q_le_ht (cfg : FrameQCfg K z J zJ Q E S) : Q ≤ firstFactor K := by
  rw [cfg.hQ]
  exact Subgroup.map_subtype_le _

theorem E_sylow (cfg : FrameQCfg K z J zJ Q E S) : IsSylow2In E Q := by
  have hQH : Q ≤ sigmaGen K := (cfg.Q_le_ht).trans cfg.ht_le
  have hHs : IsSylow2In (S ⊓ sigmaGen K) (sigmaGen K) :=
    isSylow2In_inf_of_le_normalizer cfg.hS Subgroup.le_normalizer le_rfl
  have hn : sigmaGen K ≤ Subgroup.normalizer (Q : Set T) := by
    rw [cfg.hQ]
    exact fun x hx => normalizer_le_normalizer_oddTwoCoreIn _ (cfg.hs_le_normalizer_ht hx)
  have h := isSylow2In_inf_of_le_normalizer hHs hQH hn
  have hEq : (S ⊓ sigmaGen K) ⊓ Q = E := by
    rw [cfg.hE]
    ext x
    simp only [Subgroup.mem_inf]
    exact ⟨fun ⟨⟨hS, _⟩, hQ⟩ => ⟨hQ, hS⟩, fun ⟨hQ, hS⟩ => ⟨⟨hS, hQH hQ⟩, hQ⟩⟩
  rw [hEq] at h
  exact h

theorem Q_conj (cfg : FrameQCfg K z J zJ Q E S) (hE : EFacts K z E) {x : T} (hx : x ∈ Q)
    (hx2 : x * x = 1) (hx1 : x ≠ 1) : ∃ l ∈ firstFactor K, l⁻¹ * z * l = x := by
  have hxo : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two]; exact hx2) hx1
  obtain ⟨q, hq, hqE⟩ :=
    CFSG.StronglyEmbedded.UniqueCoset.exists_conj_mem_of_isSylow2In cfg.E_sylow hx hxo
  have h1 : q⁻¹ * x * q ≠ 1 := by
    intro h
    apply hx1
    have := congrArg (fun w => q * w * q⁻¹) h
    simpa [mul_assoc] using this
  have hqx2 : (q⁻¹ * x * q) * (q⁻¹ * x * q) = 1 := by
    calc (q⁻¹ * x * q) * (q⁻¹ * x * q) = q⁻¹ * (x * x) * q := by group
      _ = 1 := by rw [hx2]; group
  obtain ⟨l, hl, hlx⟩ := hE.conj _ hqE hqx2 h1
  refine ⟨l * q⁻¹, (firstFactor K).mul_mem hl ((firstFactor K).inv_mem (cfg.Q_le_ht hq)), ?_⟩
  calc (l * q⁻¹)⁻¹ * z * (l * q⁻¹) = q * (l⁻¹ * z * l) * q⁻¹ := by group
    _ = q * (q⁻¹ * x * q) * q⁻¹ := by rw [hlx]
    _ = x := by group

theorem tight (cfg : FrameQCfg K z J zJ Q E S) (hE : EFacts K z E) : TightlyEmbedded Q := by
  have hΩ := cfg.datum.hyp
  refine tightlyEmbedded_of_conj hΩ.conjInvariant (CoreAssembly.mem_conjClass_self K)
    cfg.datum.unique (cfg.E_le_Q hE.z_mem) (fun g hg => ?_) fun x hx hx2 hx1 => ?_
  · rw [cfg.hQ]
    exact normalizer_le_normalizer_oddTwoCoreIn _
      (mem_normalizer_firstFactor hg (conjStab_aStar_le_sigmaNorm hΩ hg))
  · obtain ⟨l, hl, hlx⟩ := cfg.Q_conj hE hx hx2 hx1
    exact ⟨l⁻¹, (conjStab (aStar (CoreAssembly.conjClass K) K)).inv_mem
      (cfg.hs_stab (cfg.ht_le hl)), by simpa using hlx⟩

theorem clash (cfg : FrameQCfg K z J zJ Q E S) (hE : EFacts K z E) {g u : T} (hu2 : u * u = 1)
    (hu1 : u ≠ 1) (hguE : g * u * g⁻¹ ∈ E) {M' : Subgroup T} (hM' : M' ∈ sigmaOf K)
    {X' : Subgroup T} (hX' : X' ∈ USet (CoreAssembly.conjClass K)) (hX'M' : X' ≤ M')
    (hX'c : X' ≤ Subgroup.centralizer ({u} : Set T)) : g ∈ sigmaNorm K := by
  have hΩ := cfg.datum.hyp
  have hKΩ : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  have hg1 : g * u * g⁻¹ ≠ 1 := by
    intro h
    apply hu1
    have := congrArg (fun w => g⁻¹ * w * g) h
    simpa [mul_assoc] using this
  have hg2 : (g * u * g⁻¹) * (g * u * g⁻¹) = 1 := by
    calc (g * u * g⁻¹) * (g * u * g⁻¹) = g * (u * u) * g⁻¹ := by group
      _ = 1 := by rw [hu2]; group
  obtain ⟨l, hl, hlu⟩ := hE.conj _ hguE hg2 hg1
  have hu_eq : u = (l * g)⁻¹ * z * (l * g) := by
    have h5 : g * u * g⁻¹ = l⁻¹ * z * l := hlu.symm
    calc u = g⁻¹ * (g * u * g⁻¹) * g := by group
      _ = g⁻¹ * (l⁻¹ * z * l) * g := by rw [h5]
      _ = (l * g)⁻¹ * z * (l * g) := by group
  have hKu : IsUniqueInvolution (conjSub (l * g)⁻¹ K) u := by
    have := cfg.datum.unique.conj (l * g)⁻¹
    rwa [show (l * g)⁻¹ * z * ((l * g)⁻¹)⁻¹ = u by rw [hu_eq]; group] at this
  have hKuΩ : conjSub (l * g)⁻¹ K ∈ CoreAssembly.conjClass K := hΩ.conjInvariant _ K hKΩ
  have hM'd : M' ∈ dstarComp (CoreAssembly.conjClass K) K := hM'
  have hM'Ω : M' ∈ CoreAssembly.conjClass K := (mem_dstarComp_symm hKΩ hM'd).1
  have h1 : M' ∈ dstarComp (CoreAssembly.conjClass K) (conjSub (l * g)⁻¹ K) :=
    dstarComp_of_centralizes hΩ hM'Ω hKuΩ hKu hX' hX'M' hX'c
  have h2 : conjSub (l * g)⁻¹ K ∈ dstarComp (CoreAssembly.conjClass K) M' :=
    (mem_dstarComp_symm hKuΩ h1).2
  have h3 : conjSub (l * g)⁻¹ K ∈ dstarComp (CoreAssembly.conjClass K) K := hM'd.trans h2
  have h5 : (l * g)⁻¹ ∈ sigmaStarNorm (CoreAssembly.conjClass K) K :=
    T7A.mem_sigmaStarNorm_of_conj hΩ.conjInvariant hKΩ h3
  have h6 : l * g ∈ sigmaStarNorm (CoreAssembly.conjClass K) K := by
    simpa using (sigmaStarNorm (CoreAssembly.conjClass K) K).inv_mem h5
  have hl' : l ∈ sigmaStarNorm (CoreAssembly.conjClass K) K :=
    sigmaGen_le_sigmaStarNorm hΩ.conjInvariant (cfg.ht_le hl)
  have hg : g ∈ sigmaStarNorm (CoreAssembly.conjClass K) K := by
    simpa using (sigmaStarNorm (CoreAssembly.conjClass K) K).mul_mem
      ((sigmaStarNorm (CoreAssembly.conjClass K) K).inv_mem hl') h6
  exact sigmaStarNorm_le_sigmaNorm K hg

end FrameQCfg

theorem frameQCfg_of {T : Type} [Group T] [Finite T] {K : Subgroup T} {z : T} {J : Subgroup T}
    {zJ : T} {S : Subgroup T} (cfg : FrameCfg K z J zJ S) :
    FrameQCfg K z J zJ (oddTwoCoreIn (firstFactor K)) (oddTwoCoreIn (firstFactor K) ⊓ S) S :=
  { toFrameCfg := cfg, hQ := rfl, hE := rfl }

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
