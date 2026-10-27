module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.HU42SE27LDefs
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieU6Aut
import CFSG.LocalAnalysis.GLTheoremA.CatB.HU42SE27CRed
import CFSG.LocalAnalysis.GLTheoremA.CatB.HU42SE27CD4
import CFSG.LocalAnalysis.GLTheoremA.CatB.HU42SE27CU5
import CFSG.LocalAnalysis.GLTheoremA.CatB.HU42SE27CU6
import CFSG.LocalAnalysis.GLTheoremA.CatB.HU42SE27CU6Nine
import CFSG.LocalAnalysis.GLTheoremA.CatB.HU42SE27CU6Cube
import CFSG.LocalAnalysis.GLTheoremA.CatB.U4Tab5
import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTCompU6

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat

open CFSG.Open

open scoped commutatorElement

@[expose] def LocShapeOn (G : Type) [Group G] : Prop :=
  ∀ (E U₀ K : Subgroup G) (s : G), IsElemAbelian 3 E → Nat.card E = 3 ^ 3 → IsPGroup 2 ↥U₀ →
    E ≤ Subgroup.normalizer (U₀ : Set G) → (⁅U₀, E⁆ : Subgroup G) ≠ ⊥ → s ∈ E → s ≠ 1 →
    K ≤ Subgroup.centralizer ({s} : Set G) → Group.IsPerfect ↥K → HasU4Quot K →
      ∃ T : Subgroup G, T ≤ K ∧ IsPGroup 2 ↥T ∧ (E ⊓ K) ≤ Subgroup.normalizer (T : Set G) ∧
        (⁅T, E ⊓ K⁆ : Subgroup G) ≠ ⊥ ∧ 8 < Nat.card T

theorem LocShapeOn.of_mulEquiv {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    (h : LocShapeOn G) : LocShapeOn G' := by
  intro E' U₀' K' s' hE' hE27' hU₀' hnorm' hcomm' hsE' hs1' hK' hKperf' hU4'
  let E : Subgroup G := E'.comap (e : G →* G')
  let U₀ : Subgroup G := U₀'.comap (e : G →* G')
  let K : Subgroup G := K'.comap (e : G →* G')
  let s : G := e.symm s'
  have hse : e s = s' := by simp [s]
  have hcard_comap : ∀ H : Subgroup G', Nat.card (H.comap (e : G →* G')) = Nat.card H := by
    intro H
    exact Nat.card_congr (e.toEquiv.subtypeEquiv (p := fun x => x ∈ H.comap (e : G →* G'))
      (q := fun y => y ∈ H) fun _ => Iff.rfl)
  have hEmap : E.map (e : G →* G') = E' :=
    Subgroup.map_comap_eq_self_of_surjective e.surjective E'
  have hU₀map : U₀.map (e : G →* G') = U₀' :=
    Subgroup.map_comap_eq_self_of_surjective e.surjective U₀'
  have hKmap : K.map (e : G →* G') = K' :=
    Subgroup.map_comap_eq_self_of_surjective e.surjective K'
  have hE : IsElemAbelian 3 E := CFSG.Open.IsElemAbelian.comap hE' e.injective
  have hE27 : Nat.card E = 3 ^ 3 := by rw [hcard_comap E']; exact hE27'
  have hU₀ : IsPGroup 2 ↥U₀ := hU₀'.comap_of_injective (e : G →* G') e.injective
  have hnorm : E ≤ Subgroup.normalizer (U₀ : Set G) := by
    have h1 : E ≤ (Subgroup.normalizer (U₀' : Set G')).comap (e : G →* G') := fun x hx => hnorm' hx
    rwa [Subgroup.comap_normalizer_eq_of_surjective U₀' e.surjective] at h1
  have hcomm : (⁅U₀, E⁆ : Subgroup G) ≠ ⊥ := by
    intro hbot
    apply hcomm'
    have h1 : (⁅U₀, E⁆ : Subgroup G).map (e : G →* G') = ⊥ := by rw [hbot, Subgroup.map_bot]
    rwa [Subgroup.map_commutator, hU₀map, hEmap] at h1
  have hsE : s ∈ E := by
    show e s ∈ E'
    rw [hse]
    exact hsE'
  have hs1 : s ≠ 1 := by
    intro h1
    apply hs1'
    rw [← hse, h1, map_one]
  have hK : K ≤ Subgroup.centralizer ({s} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply e.injective
    rw [map_mul, map_mul, hse]
    exact Subgroup.mem_centralizer_singleton_iff.1 (hK' hx)
  have hKperf : Group.IsPerfect ↥K := by
    rw [Subgroup.isPerfect_iff] at hKperf' ⊢
    apply Subgroup.map_injective (f := (e : G →* G')) e.injective
    rw [Subgroup.map_commutator, hKmap]
    exact hKperf'
  have hU4 : HasU4Quot K := by
    obtain ⟨Y, Ygrp, hY, f, hf⟩ := hU4'
    letI : Group Y := Ygrp
    let ψ : ↥K ≃* ↥K' := (e.subgroupMap K).trans (MulEquiv.subgroupCongr hKmap)
    exact ⟨Y, Ygrp, hY, f.comp (ψ : ↥K →* ↥K'), hf.comp ψ.surjective⟩
  obtain ⟨T, hTK, hT2, hEN, hTE, hT8⟩ :=
    h E U₀ K s hE hE27 hU₀ hnorm hcomm hsE hs1 hK hKperf hU4
  refine ⟨T.map (e : G →* G'), ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hKmap]
    exact Subgroup.map_mono hTK
  · exact hT2.map (e : G →* G')
  · have h1 : ((E ⊓ K).map (e : G →* G')) ≤ (Subgroup.normalizer (T : Set G)).map
        (e : G →* G') := Subgroup.map_mono hEN
    rw [Subgroup.map_inf_eq _ _ _ e.injective, hEmap, hKmap] at h1
    rw [Subgroup.map_normalizer_eq_of_bijective (H := T) (f := (e : G →* G'))
      ⟨e.injective, e.surjective⟩] at h1
    exact h1
  · intro hbot
    apply hTE
    have h1 : (⁅T, E ⊓ K⁆ : Subgroup G).map (e : G →* G') = ⊥ := by
      rw [Subgroup.map_commutator, Subgroup.map_inf_eq _ _ _ e.injective, hEmap, hKmap]
      exact hbot
    exact Subgroup.map_injective (f := (e : G →* G')) e.injective
      (by rw [h1, Subgroup.map_bot])
  · rw [Subgroup.card_map_of_injective e.injective]
    exact hT8

theorem locShapeOn_of_hosts {G : Type} [Group G] [Finite G] (hS : CentSplitOn G)
    (hI : InvCentOn G) (hY : U42InvFact) : LocShapeOn G := by
  intro E U₀ K s hE hE27 hU₀ hnorm hcommNE hsE hs1 hK hKperf hU4
  have hsord : orderOf s = 3 := orderOf_eq_three_of_mem hE hsE hs1
  obtain ⟨hKC, hgen, hsK, hZK, hKcard⟩ := u4Split_of_centSplitOn hS hsord hK hKperf hU4
  have hnoU4 : ¬ NoU4Sect s := by
    intro hno
    obtain ⟨Y, Ygrp, hYcat, f, hf⟩ := hU4
    letI : Group Y := Ygrp
    have hYcard : Nat.card Y = 25920 := card_of_catalogIs_u4two hYcat
    have hdvd : Nat.card Y ∣ Nat.card ↥K := Subgroup.card_dvd_of_surjective hf
    exact hno K hK hKperf (dvd_trans (by rw [hYcard]; norm_num) hdvd)
  have hU₀ne : U₀ ≠ ⊥ := by
    intro hbot
    apply hcommNE
    rw [hbot, Subgroup.commutator_bot_left]
  obtain ⟨z, hz2, hz1, hzE⟩ := hI E U₀ s hE hE27 hU₀ hU₀ne hnorm hsE hs1 hnoU4
  have hzC : z ∈ Subgroup.centralizer ({s} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact (hzE s hsE).symm
  obtain ⟨n, k, hkK, hzeq⟩ := hgen z hzC
  have hsk : ∀ y ∈ K, Commute s y := fun y hy =>
    (Subgroup.mem_centralizer_singleton_iff.1 (hKC hy)).symm
  have hKs : K ⊓ Subgroup.zpowers s = ⊥ := by
    have hdvd : Nat.card ↥(K ⊓ Subgroup.zpowers s) ∣ 3 := by
      have h := Subgroup.card_dvd_of_le
        (inf_le_right : K ⊓ Subgroup.zpowers s ≤ Subgroup.zpowers s)
      rwa [Nat.card_zpowers, hsord] at h
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      apply hsK
      have hle : K ⊓ Subgroup.zpowers s ≤ Subgroup.zpowers s := inf_le_right
      have heq : K ⊓ Subgroup.zpowers s = Subgroup.zpowers s :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [h3, Nat.card_zpowers, hsord])
      have hmem : s ∈ K ⊓ Subgroup.zpowers s := by
        rw [heq]
        exact Subgroup.mem_zpowers s
      exact (Subgroup.mem_inf.1 hmem).1
  have hcomm_nk : Commute (s ^ n) k := (hsk k hkK).pow_left n
  have hz2' : s ^ (n * 2) * k ^ 2 = 1 := by
    have h2 : (s ^ n * k) ^ 2 = 1 := by
      rw [← hzeq]
      exact hz2
    calc s ^ (n * 2) * k ^ 2 = (s ^ n) ^ 2 * k ^ 2 := by rw [pow_mul]
      _ = (s ^ n * k) ^ 2 := (hcomm_nk.mul_pow 2).symm
      _ = 1 := h2
  have hsk2 : s ^ (n * 2) = (k ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left hz2'
  have hone : s ^ (n * 2) = 1 := by
    have hmemK : s ^ (n * 2) ∈ K := by
      rw [hsk2]
      exact K.inv_mem (K.pow_mem hkK 2)
    have hmem : s ^ (n * 2) ∈ K ⊓ Subgroup.zpowers s :=
      ⟨hmemK, Subgroup.pow_mem _ (Subgroup.mem_zpowers s) _⟩
    rw [hKs] at hmem
    simpa using hmem
  have h3dvd : 3 ∣ n * 2 := by
    rw [← hsord]
    exact orderOf_dvd_iff_pow_eq_one.2 hone
  have h3n : 3 ∣ n := by
    rcases Nat.prime_three.dvd_mul.1 h3dvd with h | h
    · exact h
    · exact absurd h (by norm_num)
  have hsn : s ^ n = 1 := by
    have h3 : orderOf s ∣ n := by rwa [hsord]
    exact orderOf_dvd_iff_pow_eq_one.1 h3
  have hzK : z ∈ K := by
    rw [hzeq, hsn, one_mul]
    exact hkK
  have hEC : E ≤ Subgroup.centralizer ({s} : Set G) := by
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact (hE.comm he hsE).symm
  let F : Subgroup G := E ⊓ K
  have hEsup : E = Subgroup.zpowers s ⊔ F := by
    apply le_antisymm
    · intro e he
      obtain ⟨m, k', hk'K, rfl⟩ := hgen e (hEC he)
      have hk'E : k' ∈ E := by
        have hsmE : s ^ m ∈ E := E.pow_mem hsE m
        have hk'eq : k' = (s ^ m)⁻¹ * (s ^ m * k') := by group
        rw [hk'eq]
        exact E.mul_mem (E.inv_mem hsmE) he
      have hk'F : k' ∈ F := ⟨hk'E, hk'K⟩
      exact (Subgroup.zpowers s ⊔ F).mul_mem
        (Subgroup.mem_sup_left (Subgroup.pow_mem _ (Subgroup.mem_zpowers s) m))
        (Subgroup.mem_sup_right hk'F)
    · exact sup_le (Subgroup.zpowers_le.mpr hsE) inf_le_left
  have hinf : Subgroup.zpowers s ⊓ F = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxs, hxF⟩ := Subgroup.mem_inf.1 hx
    have hxK' : x ∈ K ⊓ Subgroup.zpowers s := ⟨hxF.2, hxs⟩
    rw [hKs] at hxK'
    exact hxK'
  have hcomm_zp : ∀ x ∈ Subgroup.zpowers s, ∀ y ∈ F, x * y = y * x := by
    intro x hx y hy
    have h1 : s ∈ Subgroup.centralizer (F : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y' hy'
      exact (hsk y' hy'.2).symm
    have h2 : x ∈ Subgroup.centralizer (F : Set G) := Subgroup.zpowers_le.mpr h1 hx
    exact (Subgroup.mem_centralizer_iff.1 h2 y hy).symm
  have hFcard : Nat.card F = 9 := by
    have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
      (Subgroup.zpowers s) F hcomm_zp).1
    rw [← hEsup, hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, hsord] at hcard
    have h27 : Nat.card E = 27 := by rw [hE27]; norm_num
    omega
  obtain ⟨Y, Ygrp, hYcat, f, hf⟩ := hU4
  letI : Group Y := Ygrp
  have hYcard : Nat.card Y = 25920 := card_of_catalogIs_u4two hYcat
  have hbij : Function.Bijective f := by
    rw [Nat.bijective_iff_surjective_and_card f]
    exact ⟨hf, by rw [hKcard, hYcard]⟩
  have hfinj : Function.Injective f := hbij.1
  let Fk : Subgroup ↥K := F.subgroupOf K
  have hF'card : Nat.card (Fk.map (f : ↥K →* Y)) = 9 := by
    rw [Subgroup.card_map_of_injective hfinj]
    have hFk : Nat.card Fk = Nat.card F :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (H := E ⊓ K) (K := K) (inf_le_right : E ⊓ K ≤ K)).toEquiv
    rw [hFk, hFcard]
  have hz'2 : f ⟨z, hzK⟩ ^ 2 = 1 := by
    rw [← map_pow, show (⟨z, hzK⟩ : ↥K) ^ 2 = 1 from Subtype.ext hz2, map_one]
  have hz'1 : f ⟨z, hzK⟩ ≠ 1 := by
    intro h
    apply hz1
    have h1 : (⟨z, hzK⟩ : ↥K) = 1 := hfinj (h.trans (map_one f).symm)
    simpa using congrArg Subtype.val h1
  have hz'comm : ∀ f' ∈ Fk.map (f : ↥K →* Y), f ⟨z, hzK⟩ * f' = f' * f ⟨z, hzK⟩ := by
    intro f' hf'
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hf'
    have hxF : (x : G) ∈ F := Subgroup.mem_subgroupOf.1 hx
    have hcomm : (⟨z, hzK⟩ : ↥K) * x = x * ⟨z, hzK⟩ := Subtype.ext (hzE x hxF.1)
    rw [← map_mul, ← map_mul, hcomm]
  obtain ⟨T', hT'2, hT'8, hF'N, hT'F'⟩ :=
    hY Y hYcat (Fk.map (f : ↥K →* Y)) (f ⟨z, hzK⟩) hF'card hz'2 hz'1 hz'comm
  let Tk : Subgroup ↥K := T'.comap (f : ↥K →* Y)
  let T : Subgroup G := Tk.map K.subtype
  have hTk_map : Tk.map (f : ↥K →* Y) = T' :=
    Subgroup.map_comap_eq_self_of_surjective hf T'
  have hT2 : IsPGroup 2 ↥T := by
    have h1 : IsPGroup 2 ↥Tk := hT'2.comap_of_injective (f : ↥K →* Y) hfinj
    exact h1.map K.subtype
  have hTK : T ≤ K := Subgroup.map_subtype_le Tk
  have hcardT : Nat.card T = Nat.card T' := by
    change Nat.card (Tk.map K.subtype) = Nat.card T'
    rw [Subgroup.card_subtype, ← hTk_map, Subgroup.card_map_of_injective hfinj]
  have hFN : F ≤ Subgroup.normalizer (T : Set G) := by
    have hFkN : Fk ≤ Subgroup.normalizer (Tk : Set ↥K) := by
      rw [← Subgroup.comap_normalizer_eq_of_surjective T' hf]
      intro x hx
      exact hF'N (Subgroup.mem_map_of_mem (f : ↥K →* Y) hx)
    have h1 : Fk.map K.subtype ≤ (Subgroup.normalizer (Tk : Set ↥K)).map K.subtype :=
      Subgroup.map_mono hFkN
    have h2 : (Subgroup.normalizer (Tk : Set ↥K)).map K.subtype ≤
        Subgroup.normalizer (Tk.map K.subtype : Set G) := Subgroup.le_normalizer_map K.subtype
    have h3 : Fk.map K.subtype = F :=
      Subgroup.map_subgroupOf_eq_of_le (H := E ⊓ K) (K := K) (inf_le_right : E ⊓ K ≤ K)
    rw [h3] at h1
    exact h1.trans h2
  have hTF : (⁅T, F⁆ : Subgroup G) ≠ ⊥ := by
    intro hbot
    apply hT'F'
    have h1 : (⁅Tk, Fk⁆ : Subgroup ↥K).map K.subtype = ⊥ := by
      rw [Subgroup.map_commutator,
        Subgroup.map_subgroupOf_eq_of_le (H := E ⊓ K) (K := K)
          (inf_le_right : E ⊓ K ≤ K)]
      exact hbot
    have h2 : (⁅Tk, Fk⁆ : Subgroup ↥K) = ⊥ :=
      Subgroup.map_injective K.subtype_injective (by rw [h1, Subgroup.map_bot])
    have h3 : (⁅Tk, Fk⁆ : Subgroup ↥K).map (f : ↥K →* Y) = ⊥ := by
      rw [h2, Subgroup.map_bot]
    rw [Subgroup.map_commutator, hTk_map] at h3
    exact h3
  exact ⟨T, hTK, hT2, hFN, hTF, by rw [hcardT]; exact hT'8⟩

theorem u42E27LocAt_of_hosts (hD : InvCentOn ↥CFSG.AGLEmbedding.Om8)
    (h5 : InvCentOn CFSG.LocalAnalysis.GLTheoremA.CatB.U52Layer.M5)
    (h6 : InvCentOn CFSG.LocalAnalysis.GLTheoremA.LevelLieU6.S6) (hY : U42InvFact) :
    U42E27LocAt := by
  intro S _ _ hS E U₀ K s hE hE27 hU₀ hnorm hcomm hsE hs1 hK hKperf hU4
  obtain ⟨i, hi, ⟨e⟩⟩ := hS
  have hshape : LocShapeOn S := by
    rcases hi with h | h | h
    · obtain ⟨e'⟩ := bridge_d4two ⟨i, h, ⟨e⟩⟩
      exact LocShapeOn.of_mulEquiv e'.symm (locShapeOn_of_hosts centSplitOn_Om8 hD hY)
    · obtain ⟨e'⟩ := U52Layer.bridge_u5two_stated ⟨i, h, ⟨e⟩⟩
      exact LocShapeOn.of_mulEquiv e'.symm (locShapeOn_of_hosts centSplitOn_M5 h5 hY)
    · obtain ⟨e'⟩ := HSubT.nonempty_S6_of_isU6two ⟨i, h, ⟨e⟩⟩
      exact LocShapeOn.of_mulEquiv e'.symm
        (locShapeOn_of_hosts (centSplitOn_S6_of u6NineFact_holds u6CubeFact_holds) h6 hY)
  exact hshape E U₀ K s hE hE27 hU₀ hnorm hcomm hsE hs1 hK hKperf hU4

end CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat

end
