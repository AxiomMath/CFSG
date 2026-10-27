module

public import CFSG.LocalAnalysis.RankThreeUC.GN15AltModNat
import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.Covered
import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56.NaturalOn

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.GN
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.RankThree.PartTwo
  CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542
  CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56
open Equiv Equiv.Perm
open scoped commutatorElement

variable {X : Type} [Group X] {T : Subgroup X}

section Sylow

variable [Finite X]

theorem altMod_sylow (hX : GNSetting X T) {L : Subgroup (X ⧸ gnC T)}
    (hL : IsComponentOf L ⊤) {n : ℕ} (hn : 2 ≤ n)
    (g : ↥L →* alternatingGroup (Fin n)) (hg : Function.Surjective g)
    (hginj : Function.Injective g) {N : Subgroup X} (hKN : gnPre T L ≤ N)
    (ρ : ↥N →* Equiv.Perm (Fin n))
    (hρpre : ∀ (k : X) (hk : toStar T k ∈ L) (hkN : k ∈ N),
      ρ ⟨k, hkN⟩ = (g ⟨toStar T k, hk⟩ : Equiv.Perm (Fin n)))
    (hs : ∃ s : Equiv.Perm (Fin n),
      s ∈ ((T ⊓ N).subgroupOf N).map ρ ∧ s ∉ alternatingGroup (Fin n)) :
    IsPGroup 2 (((T ⊓ N).subgroupOf N).map ρ) ∧ ¬ 2 ∣ (((T ⊓ N).subgroupOf N).map ρ).index := by
  classical
  have hT2 : IsPGroup 2 T := hX.sylow.2.1
  refine ⟨?_, ?_⟩
  · have hS2 : IsPGroup 2 ↥((T ⊓ N).subgroupOf N) := by
      rintro ⟨x, hx⟩
      obtain ⟨k, hk⟩ := hT2 ⟨(x : X), (Subgroup.mem_subgroupOf.mp hx).1⟩
      refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
      have := congrArg (fun y : ↥T => (y : X)) hk
      simpa using this
    exact hS2.map ρ
  · have hSyl : IsSylowTwoOf (gnImg T T ⊓ L) L :=
      L246C127.isSylowTwoOf_inf_of_isSubnormal' hL.2.1 (isSylowTwoOf_gnImg_top hX)
    let f₀ : ↥L →* Equiv.Perm (Fin n) := (alternatingGroup (Fin n)).subtype.comp g
    have hf₀ : Function.Injective f₀ := (alternatingGroup (Fin n)).subtype_injective.comp hginj
    have hrange : Subgroup.map f₀ ⊤ = alternatingGroup (Fin n) := by
      ext σ
      constructor
      · rintro ⟨l, -, rfl⟩
        exact (g l).2
      · intro hσ
        obtain ⟨l, hl⟩ := hg ⟨σ, hσ⟩
        exact ⟨l, Subgroup.mem_top _, by simp [f₀, hl]⟩
    refine altMod_not_two_dvd_index hn (P₀ := Subgroup.map f₀
      ((gnImg T T ⊓ L).subgroupOf L)) ?_ ?_ ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨t, ht, hty⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hy).1
      have hyL : toStar T t ∈ L := by rw [hty]; exact y.2
      have htN : t ∈ N := hKN hyL
      refine ⟨⟨t, htN⟩, Subgroup.mem_subgroupOf.2 ⟨ht, htN⟩, ?_⟩
      have h1 := hρpre t hyL htN
      show ρ ⟨t, htN⟩ = f₀ y
      rw [h1]
      have : (⟨toStar T t, hyL⟩ : ↥L) = y := Subtype.ext hty
      rw [this]
      rfl
    · rintro _ ⟨y, -, rfl⟩
      exact (g y).2
    · rw [← hrange, Subgroup.relIndex_map_map_of_injective _ _ hf₀, Subgroup.relIndex_top_right]
      exact hSyl.2.2
    · obtain ⟨s, hsQ, hsA⟩ := hs
      exact fun h => hsA (h hsQ)


end Sylow

section Data

structure GNAltModData (T : Subgroup X) (L : Subgroup (X ⧸ gnC T)) {n : ℕ}
    (g : ↥L →* alternatingGroup (Fin n)) where
  ρ : ↥(Subgroup.normalizer (gnPre T L : Set X)) →* Equiv.Perm (Fin n)
  ρ_pre : ∀ (k : ↥(gnPre T L)) (hk : toStar T k ∈ L),
    ρ ⟨k, Subgroup.le_normalizer k.2⟩ = (g ⟨toStar T k, hk⟩ : Equiv.Perm (Fin n))
  ρ_C : ∀ x : ↥(Subgroup.normalizer (gnPre T L : Set X)), (x : X) ∈ gnC T → ρ x = 1
  baum_le : baum T ≤ Subgroup.normalizer (gnPre T L : Set X)
  J_swaps : ∃ T' : Set (Equiv.Perm (Fin n)), T'.Nonempty ∧ (∀ t ∈ T', t.IsSwap) ∧
    (∀ t ∈ T', ∀ t' ∈ T', t * t' = t' * t) ∧
    ((thompsonJ T).subgroupOf (Subgroup.normalizer (gnPre T L : Set X))).map ρ =
      Subgroup.closure T'
  baum_le_J : ((baum T).subgroupOf (Subgroup.normalizer (gnPre T L : Set X))).map ρ ≤
    ((thompsonJ T).subgroupOf (Subgroup.normalizer (gnPre T L : Set X))).map ρ
  sylow : IsPGroup 2 (((T ⊓ Subgroup.normalizer (gnPre T L : Set X)).subgroupOf
      (Subgroup.normalizer (gnPre T L : Set X))).map ρ) ∧
    ¬ 2 ∣ (((T ⊓ Subgroup.normalizer (gnPre T L : Set X)).subgroupOf
      (Subgroup.normalizer (gnPre T L : Set X))).map ρ).index
  g_bij : Function.Bijective g

variable {L : Subgroup (X ⧸ gnC T)} {n : ℕ} {g : ↥L →* alternatingGroup (Fin n)}

namespace GNAltModData

variable (S : GNAltModData T L g)

@[expose] def J : Subgroup (Perm (Fin n)) :=
  ((thompsonJ T).subgroupOf (Subgroup.normalizer (gnPre T L : Set X))).map S.ρ

@[expose] def Q : Subgroup (Perm (Fin n)) :=
  ((T ⊓ Subgroup.normalizer (gnPre T L : Set X)).subgroupOf
    (Subgroup.normalizer (gnPre T L : Set X))).map S.ρ

@[expose] def R (a b : Fin n) : Subgroup X :=
  T ⊓ ((swapPairStab a b).comap S.ρ).map (Subgroup.normalizer (gnPre T L : Set X)).subtype

theorem mem_R_iff {a b : Fin n} {x : X} :
    x ∈ S.R a b ↔ x ∈ T ∧ ∃ hx : x ∈ Subgroup.normalizer (gnPre T L : Set X),
      S.ρ ⟨x, hx⟩ ∈ swapPairStab a b := by
  constructor
  · rintro ⟨hxT, y, hy, rfl⟩
    exact ⟨hxT, y.2, hy⟩
  · rintro ⟨hxT, hxN, h⟩
    exact ⟨hxT, ⟨x, hxN⟩, h, rfl⟩

theorem J_le_Q : S.J ≤ S.Q := by
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨x, Subgroup.mem_subgroupOf.2 ⟨?_, x.2⟩, rfl⟩
  have hJT : thompsonJ T ≤ T := iSup_le fun _ => iSup_le fun hA => hA.1
  exact hJT (Subgroup.mem_subgroupOf.1 hx)

theorem J_comm : ∀ x ∈ S.J, ∀ y ∈ S.J, x * y = y * x := by
  obtain ⟨T', -, -, hT'c, hT'J⟩ := S.J_swaps
  intro x hx y hy
  rw [J, hT'J] at hx hy
  exact congrArg Subtype.val
    ((Subgroup.closureCommGroupOfComm (fun t ht t' ht' _ => hT'c t ht t' ht')).mul_comm
      ⟨x, hx⟩ ⟨y, hy⟩)

theorem baum_map_mem_J {x : X} (hx : x ∈ baum T) : S.ρ ⟨x, S.baum_le hx⟩ ∈ S.J :=
  S.baum_le_J ⟨⟨x, S.baum_le hx⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩

theorem g_conj (x : ↥(Subgroup.normalizer (gnPre T L : Set X))) (l : ↥L)
    (hxl : toStar T x * (l : X ⧸ gnC T) * (toStar T x)⁻¹ ∈ L) :
    (g ⟨toStar T x * (l : X ⧸ gnC T) * (toStar T x)⁻¹, hxl⟩ : Perm (Fin n)) =
      S.ρ x * (g l : Perm (Fin n)) * (S.ρ x)⁻¹ := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective (l : X ⧸ gnC T)
  have hkK : k ∈ gnPre T L := by
    show toStar T k ∈ L
    rw [show toStar T k = (l : X ⧸ gnC T) from hk]
    exact l.2
  have hkN : k ∈ Subgroup.normalizer (gnPre T L : Set X) := Subgroup.le_normalizer hkK
  have hxkK : (x : X) * k * (x : X)⁻¹ ∈ gnPre T L :=
    (Subgroup.mem_normalizer_iff.1 x.2 k).1 hkK
  have h1 := S.ρ_pre ⟨(x : X) * k * (x : X)⁻¹, hxkK⟩ hxkK
  have h2 := S.ρ_pre ⟨k, hkK⟩ hkK
  have h3 : (⟨(x : X) * k * (x : X)⁻¹, Subgroup.le_normalizer hxkK⟩ :
      ↥(Subgroup.normalizer (gnPre T L : Set X))) = x * ⟨k, hkN⟩ * x⁻¹ := rfl
  have h4 : S.ρ ⟨(x : X) * k * (x : X)⁻¹, Subgroup.le_normalizer hxkK⟩ =
      S.ρ x * S.ρ ⟨k, hkN⟩ * (S.ρ x)⁻¹ := by
    rw [h3, map_mul, map_mul, map_inv]
  have h5 : (⟨toStar T ((x : X) * k * (x : X)⁻¹), hxkK⟩ : ↥L) =
      ⟨toStar T x * (l : X ⧸ gnC T) * (toStar T x)⁻¹, hxl⟩ := by
    apply Subtype.ext
    show toStar T ((x : X) * k * (x : X)⁻¹) = _
    rw [map_mul, map_mul, map_inv, show toStar T k = (l : X ⧸ gnC T) from hk]
  have h6 : (⟨toStar T k, hkK⟩ : ↥L) = l := Subtype.ext hk
  have h7 : S.ρ ⟨k, hkN⟩ = (g l : Perm (Fin n)) := by
    have := h2
    rw [h6] at this
    exact this
  calc (g ⟨toStar T x * (l : X ⧸ gnC T) * (toStar T x)⁻¹, hxl⟩ : Perm (Fin n))
      = (g ⟨toStar T ((x : X) * k * (x : X)⁻¹), hxkK⟩ : Perm (Fin n)) := by rw [h5]
    _ = S.ρ ⟨(x : X) * k * (x : X)⁻¹, Subgroup.le_normalizer hxkK⟩ := h1.symm
    _ = S.ρ x * S.ρ ⟨k, hkN⟩ * (S.ρ x)⁻¹ := h4
    _ = S.ρ x * (g l : Perm (Fin n)) * (S.ρ x)⁻¹ := by rw [h7]

end GNAltModData

section Existence

variable [Finite X]

theorem nonempty_gnAltModData (hX : GNSetting X T) {L : Subgroup (X ⧸ gnC T)}
    (hL : IsComponentOf L ⊤) (hJ : ⁅L, gnImg T (thompsonJ T)⁆ = L)
    (hM2 : gnImg T (baum T) ≤ Subgroup.normalizer (L : Set (X ⧸ gnC T)))
    {n : ℕ} (hn9 : 9 ≤ n) (hodd : Odd n) (e : ↥L ≃* alternatingGroup (Fin n))
    (g : ↥L →* alternatingGroup (Fin n)) (hg : Function.Surjective g)
    (W : Subgroup X) (hWV : W ≤ gnV T)
    (hWK : ∀ k ∈ gnPre T L, ∀ w ∈ W, k * w * k⁻¹ ∈ W)
    (π : ↥⁅W, gnPre T L⁆ →* Multiplicative (altHeart n))
    (hπk : ∀ u : ↥⁅W, gnPre T L⁆, π u = 1 → ∀ k ∈ gnPre T L, (k : X) * u * (k : X)⁻¹ = u)
    (hπi : ∀ (l : X) (hl : toStar T l ∈ L) (u u' : ↥⁅W, gnPre T L⁆),
      (u' : X) = l * u * l⁻¹ → ∀ x : evenWeight n,
        Multiplicative.toAdd (π u) = (QuotientAddGroup.mk x : altHeart n) →
        Multiplicative.toAdd (π u') = (QuotientAddGroup.mk (evenWeightPerm
          (g ⟨toStar T l, hl⟩ : Equiv.Perm (Fin n)) x) : altHeart n))
    (hVW : ⁅gnV T, gnPre T L⁆ = ⁅W, gnPre T L⁆) :
    Nonempty (GNAltModData T L g) := by
  classical
  obtain ⟨ρ, hρpre, hρC, hJs, hρB⟩ := exists_altModRep_of_natural hX hL hJ hM2 hn9 hodd e g hg
    (W := W) (K := gnPre T L) (M := ⁅W, gnPre T L⁆) rfl rfl hWV hWK π hπk hπi hVW
  have hginj : Function.Injective g := (Finite.injective_iff_surjective_of_equiv e.toEquiv).2 hg
  have hBN : baum T ≤ Subgroup.normalizer (gnPre T L : Set X) := fun x hx =>
    mem_normalizer_gnPre_iff.2 (hM2 (Subgroup.mem_map_of_mem _ hx))
  have hJT : thompsonJ T ≤ T := iSup_le fun _ => iSup_le fun hA => hA.1
  have hsylow : IsPGroup 2 (((T ⊓ Subgroup.normalizer (gnPre T L : Set X)).subgroupOf
      (Subgroup.normalizer (gnPre T L : Set X))).map ρ) ∧
    ¬ 2 ∣ (((T ⊓ Subgroup.normalizer (gnPre T L : Set X)).subgroupOf
      (Subgroup.normalizer (gnPre T L : Set X))).map ρ).index := by
    obtain ⟨T', hT'ne, hT's, -, hT'J⟩ := hJs
    obtain ⟨s, hsT'⟩ := hT'ne
    obtain ⟨a, b, hab, hsab⟩ := hT's s hsT'
    refine altMod_sylow hX hL (by omega) g hg hginj
      (N := Subgroup.normalizer (gnPre T L : Set X)) Subgroup.le_normalizer ρ
      (fun k hk hkN => hρpre ⟨k, hk⟩ hk) ⟨s, ?_, ?_⟩
    · have hsJ : s ∈ ((thompsonJ T).subgroupOf
          (Subgroup.normalizer (gnPre T L : Set X))).map ρ := by
        rw [hT'J]; exact Subgroup.subset_closure hsT'
      obtain ⟨x, hx, rfl⟩ := hsJ
      exact ⟨x, Subgroup.mem_subgroupOf.2 ⟨hJT (Subgroup.mem_subgroupOf.1 hx), x.2⟩, rfl⟩
    · rw [hsab, Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_swap hab]
      decide
  exact ⟨⟨ρ, hρpre, hρC, hBN, hJs, hρB, hsylow, ⟨hginj, hg⟩⟩⟩

end Existence

end Data

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15
