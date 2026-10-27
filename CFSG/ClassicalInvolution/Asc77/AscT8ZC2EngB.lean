module

public import CFSG.ClassicalInvolution.Asc77.AscT8ZC2Eng
public import CFSG.ClassicalInvolution.Asc77.AscT8YAEng

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Asc77.MuTab T8YY
open scoped commutatorElement

namespace T8ZZ

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J W : Subgroup G} {z t : G}

theorem exists_xMem_of_omegaNbrE (hcl : ConjInvariant Ω)
    (hsyl : ∀ {M R : Subgroup G}, M ∈ Ω → R ∈ RSet Ω → R ≤ M → IsSylow2In R M)
    (huniq : ∀ {M : Subgroup G}, M ∈ Ω → ∃ u : G, IsUniqueInvolution M u)
    (h8 : ∀ {R : Subgroup G}, R ∈ RSet Ω → 8 ≤ Nat.card R)
    (hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M) {K L : Subgroup G} {z : G}
    (hz : IsUniqueInvolution K z) (hL : L ∈ omegaNbr Ω K) :
    ∃ P : Subgroup G, IsSylow2In P L ∧ (∀ r ∈ P, r * z = z * r) ∧
      z ∈ Subgroup.normalizer (L : Set G) := by
  obtain ⟨hLΩ, -, R₁, hR₁, hR₁L, hR₁N⟩ := hL
  have hsyl : IsSylow2In R₁ L := hsyl hLΩ hR₁ hR₁L
  have hRz : ∀ r ∈ R₁, r * z = z * r := fun r hr => by
    have h := hz.conj_eq (n := r) (mem_normalizer_iff_conjSub_eq.mp (hR₁N hr))
    calc r * z = (r * z * r⁻¹) * r := by group
      _ = z * r := by rw [h]
  obtain ⟨u, hu⟩ := huniq hLΩ
  have h8 := h8 hR₁
  have huR : u ∈ R₁ := T3.mem_of_isPGroup hu hR₁L hsyl.2.1 (by omega)
  refine ⟨R₁, hsyl, hRz, ?_⟩
  have hzu : z ∈ Subgroup.centralizer ({u} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hRz u huR).symm
  exact T8.centralizer_le_normalizer_of_noTwins hcl hLΩ (hnt L hLΩ) hu hzu

theorem exists_common_sylowE {K J L : Subgroup G} (hz : IsUniqueInvolution K z)
    (ht : IsUniqueInvolution J t) (hLK : L ∈ omegaNbr Ω K) (hLJ : L ∈ omegaNbr Ω J)
    (hxm : ∀ {K₀ : Subgroup G} {z₀ : G}, IsUniqueInvolution K₀ z₀ → L ∈ omegaNbr Ω K₀ →
      ∃ P : Subgroup G, IsSylow2In P L ∧ (∀ r ∈ P, r * z₀ = z₀ * r) ∧
        z₀ ∈ Subgroup.normalizer (L : Set G))
    (hcomm : ∀ {R₀ : Subgroup G} {y : G} {m : ℕ}, IsSylow2In R₀ L →
      y ∈ Subgroup.normalizer (L : Set G) → y ^ 2 ^ m = 1 → (∀ r ∈ R₀, y * r = r * y) →
        ∀ k ∈ L, ⁅y, k⁆ ∈ oddCoreOf L)
    (hzt : z * t = t * z) (hne : z ≠ t) :
    ∃ P : Subgroup G, IsSylow2In P L ∧ (∀ r ∈ P, r * z = z * r) ∧ (∀ r ∈ P, r * t = t * r) ∧
      z ∈ Subgroup.normalizer (L : Set G) ∧ t ∈ Subgroup.normalizer (L : Set G) := by
  have hLΩ : L ∈ Ω := hLK.1
  obtain ⟨P₁, hP₁, hP₁z, hzN⟩ := hxm hz hLK
  obtain ⟨P₂, hP₂, hP₂t, htN⟩ := hxm ht hLJ
  have hcz : ∀ k ∈ L, ⁅z, k⁆ ∈ oddCoreOf L :=
    hcomm (m := 1) hP₁ hzN (by rw [pow_one, pow_two]; exact hz.sq) (fun r hr => (hP₁z r hr).symm)
  have hct : ∀ k ∈ L, ⁅t, k⁆ ∈ oddCoreOf L :=
    hcomm (m := 1) hP₂ htN (by rw [pow_one, pow_two]; exact ht.sq) (fun r hr => (hP₂t r hr).symm)
  have hA : IsElemAbelian2 (Subgroup.closure ({z, t} : Set G)) 2 :=
    T7A.isElemAbelian2_closure_pair hz.sq ht.sq hz.ne_one ht.ne_one hne hzt
  have hA2 : IsPGroup 2 (Subgroup.closure ({z, t} : Set G)) := IsPGroup.of_card hA.1
  have hAN : Subgroup.closure ({z, t} : Set G) ≤ Subgroup.normalizer (L : Set G) := by
    rw [Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact hzN
    · exact htN
  obtain ⟨P, hPsyl, hPfix⟩ := T3.exists_sylow_normalized hA2 hAN
  have hzA : z ∈ Subgroup.closure ({z, t} : Set G) := Subgroup.subset_closure (by simp)
  have htA : t ∈ Subgroup.closure ({z, t} : Set G) := Subgroup.subset_closure (by simp)
  exact ⟨P, hPsyl,
    fun r hr => commute_of_normalizes_sylowE hPsyl.2.1 hPsyl.1 (hPfix z hzA) hcz hr,
    fun r hr => commute_of_normalizes_sylowE hPsyl.2.1 hPsyl.1 (hPfix t htA) hct hr, hzN, htN⟩

theorem oddCore_commutes_zzE (F : FrameData Ω W K J z t)
    (V : Subgroup G) (hαV' : alphaOf V = alphaOf (Subgroup.closure ({t, z} : Set G)))
    (hzmem : ∀ j : Fin 4, F.zz 0 * F.zz j ∈ V)
    {Y : Subgroup G} (hoY : oddCoreOf Y ≤ oddCoreOf (Subgroup.centralizer ({z * t} : Set G)))
    (hα : alphaOf (Subgroup.closure ({t, z} : Set G)) = ⊥)
    (j : Fin 4) {n : G} (hn : n ∈ oddCoreOf Y) : n * F.zz j = F.zz j * n := by
  have hαV : alphaOf V = ⊥ := hαV'.trans hα
  have hnC : n ∈ oddCoreOf (Subgroup.centralizer ({z * t} : Set G)) := hoY hn
  have hztV : z * t ∈ V := by
    have h01 : F.zz 0 * F.zz 1 ∈ V := hzmem 1
    rwa [F.hz0, F.hz1] at h01
  have hzt1 : z * t ≠ 1 := by
    have := F.mul_ne_oneE 0 1 (by decide)
    rwa [F.hz0, F.hz1] at this
  have hV : ∀ y ∈ V, n * y = y * n := fun y hy =>
    T8.oddCoreOf_centralizer_commutes hαV hztV hzt1 hy n hnC
  have hzA : z ∈ Subgroup.closure ({t, z} : Set G) := Subgroup.subset_closure (by simp)
  have htA : t ∈ Subgroup.closure ({t, z} : Set G) := Subgroup.subset_closure (by simp)
  have hnz : n * z = z * n :=
    T8.oddCoreOf_centralizer_commutes hα (Subgroup.mul_mem _ hzA htA) hzt1 hzA n hnC
  have h1 : Commute n (F.zz 0) := by
    rw [F.hz0]
    exact hnz
  have h2 : Commute n (F.zz 0 * F.zz j) := hV _ (hzmem j)
  have h3 : Commute n (F.zz 0 * (F.zz 0 * F.zz j)) := h1.mul_right h2
  have e : F.zz 0 * (F.zz 0 * F.zz j) = F.zz j := by
    rw [← mul_assoc, (F.hz 0).sq, one_mul]
  rw [e] at h3
  exact h3.eq

end T8ZZ

end CFSG.ClassicalInvolution.Asc77
