module

public import CFSG.LocalAnalysis.AGLEmbedding.ReeF4Defs
public import CFSG.Quasithin.Background.SmithB45TorOrbit

public section

namespace CFSG.HardMathSupport.Malle.LocalAction

section Generic
variable {Y : Type*} [Group Y]

theorem normalizer_le_normalizer_of_centralizer_eq {Z T : Subgroup Y}
    (hC : Subgroup.centralizer (Z : Set Y) = T) :
    Subgroup.normalizer (Z : Set Y) ≤ Subgroup.normalizer (T : Set Y) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  have key : ∀ g ∈ Subgroup.normalizer (Z : Set Y), ∀ t ∈ T, g * t * g⁻¹ ∈ T := by
    intro g hg t ht
    rw [← hC] at ht ⊢
    rw [Subgroup.mem_centralizer_iff] at ht ⊢
    intro z hz
    have hz' : g⁻¹ * z * g ∈ Z := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) z).mp hz
      simpa using this
    have := ht _ hz'
    calc z * (g * t * g⁻¹) = g * ((g⁻¹ * z * g) * t) * g⁻¹ := by group
      _ = g * (t * (g⁻¹ * z * g)) * g⁻¹ := by rw [this]
      _ = g * t * g⁻¹ * z := by group
  intro t
  constructor
  · exact key g hg t
  · intro h
    have := key g⁻¹ (inv_mem hg) _ h
    simpa [mul_assoc] using this

theorem inf_eq_bot_of_coprime {p : ℕ} [Fact p.Prime] [Finite Y] {W T : Subgroup Y}
    (hT : IsPGroup p T) (hW : Nat.Coprime p (Nat.card W)) : W ⊓ T = ⊥ := by
  have h1 : IsPGroup p (W ⊓ T : Subgroup Y) := hT.to_inf_right (H := W)
  obtain ⟨k, hk⟩ := h1.exists_card_eq
  have hdvd : Nat.card (W ⊓ T : Subgroup Y) ∣ Nat.card W :=
    Subgroup.card_dvd_of_le inf_le_left
  rw [hk] at hdvd
  have : k = 0 := by
    by_contra hk0
    have : p ∣ Nat.card W := (dvd_pow_self p hk0).trans hdvd
    exact (Fact.out : p.Prime).one_lt.ne' (Nat.eq_one_of_dvd_coprimes hW (dvd_refl p) this)
  rw [this, pow_zero] at hk
  exact Subgroup.eq_bot_of_card_eq _ hk

theorem le_centralizer_of_disjoint {W T : Subgroup Y} (hWT : W ≤ Subgroup.normalizer (T : Set Y))
    (hTW : T ≤ Subgroup.normalizer (W : Set Y)) (hd : W ⊓ T = ⊥) :
    W ≤ Subgroup.centralizer (T : Set Y) := by
  intro w hw
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  have h1 : w * t * w⁻¹ * t⁻¹ ∈ T := by
    have := (Subgroup.mem_normalizer_iff.mp (hWT hw) t).mp ht
    exact mul_mem this (inv_mem ht)
  have h2 : w * t * w⁻¹ * t⁻¹ ∈ W := by
    have : t * w⁻¹ * t⁻¹ ∈ W := by
      have := (Subgroup.mem_normalizer_iff.mp (hTW ht) w⁻¹).mp (inv_mem hw)
      simpa using this
    simpa [mul_assoc] using mul_mem hw this
  have : w * t * w⁻¹ * t⁻¹ ∈ (W ⊓ T : Subgroup Y) := ⟨h2, h1⟩
  rw [hd, Subgroup.mem_bot] at this
  exact (mul_inv_eq_one.mp (by simpa [mul_assoc] using this)).symm

end Generic

section Dichotomy
variable {Y : Type*} [Group Y] [Finite Y]

theorem normal_dichotomy_of_lines {T N W : Subgroup Y}
    (hTp : IsPGroup 5 T) (hZexp : ∀ z ∈ T ⊓ Subgroup.centralizer (T : Set Y), z ^ 5 = 1)
    (hCT : Subgroup.centralizer ((T ⊓ Subgroup.centralizer (T : Set Y) : Subgroup Y) : Set Y) = T)
    (hNT : N ≤ Subgroup.normalizer (T : Set Y)) (hTN : T ≤ N)
    (hNZ : N ≤ Subgroup.normalizer ((T ⊓ Subgroup.centralizer (T : Set Y) : Subgroup Y) : Set Y))
    (hW : W ≤ N) (hWN : N ≤ Subgroup.normalizer (W : Set Y))
    (htr : ∀ F F' : Subgroup Y, F ≤ T ⊓ Subgroup.centralizer (T : Set Y) →
      F' ≤ T ⊓ Subgroup.centralizer (T : Set Y) → Nat.card F = 5 → Nat.card F' = 5 →
      ∃ g ∈ N, F.map (MulAut.conj g).toMonoidHom = F') :
    W = ⊥ ∨ T ⊓ Subgroup.centralizer (T : Set Y) ≤ W := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set Z := T ⊓ Subgroup.centralizer (T : Set Y) with hZ
  have hZT : Z ≤ T := inf_le_left
  by_cases hWT : W ⊓ T = ⊥
  · left
    have h1 : W ≤ Subgroup.centralizer (T : Set Y) :=
      le_centralizer_of_disjoint (hW.trans hNT) (hTN.trans hWN) hWT
    have h2 : Subgroup.centralizer (T : Set Y) ≤ Subgroup.centralizer (Z : Set Y) :=
      Subgroup.centralizer_le hZT
    have h3 : W ≤ T := by
      have := h1.trans h2
      rwa [hCT] at this
    rw [eq_bot_iff, ← hWT]
    exact le_inf le_rfl h3
  · right
    have : Group.IsNilpotent T := hTp.isNilpotent
    let H : Subgroup T := (W ⊓ T).subgroupOf T
    have hnorm : H.Normal := by
      refine ⟨fun n hn t => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      have htN : (t : Y) ∈ Subgroup.normalizer (W : Set Y) := hWN (hTN t.2)
      refine ⟨?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp htN (n : Y)).mp hn.1
      · exact T.mul_mem (T.mul_mem t.2 hn.2) (T.inv_mem t.2)
    have hHne : H ≠ ⊥ := by
      intro hH
      apply hWT
      rw [eq_bot_iff]
      intro x hx
      have hxT : x ∈ T := hx.2
      have : (⟨x, hxT⟩ : T) ∈ H := by
        rw [Subgroup.mem_subgroupOf]
        exact hx
      rw [hH, Subgroup.mem_bot] at this
      have : x = 1 := congrArg Subtype.val this
      rw [this]
      exact one_mem _
    obtain ⟨x, hxH, hxne⟩ : ∃ x : T, x ∈ H ⊓ Subgroup.center T ∧ x ≠ 1 := by
      have hne := Group.IsNilpotent.inf_center_ne_bot_of_normal (H := H) hHne
      by_contra hcon
      apply hne
      rw [eq_bot_iff]
      intro y hy
      by_contra hy1
      exact hcon ⟨y, hy, by simpa using hy1⟩
    have hxW : (x : Y) ∈ W := (Subgroup.mem_subgroupOf.mp hxH.1).1
    have hxZ : (x : Y) ∈ Z := by
      refine ⟨x.2, ?_⟩
      show (x : Y) ∈ Subgroup.centralizer (T : Set Y)
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      have := Subgroup.mem_center_iff.mp hxH.2 ⟨t, ht⟩
      exact congrArg Subtype.val this
    have hx1 : (x : Y) ≠ 1 := fun h => hxne (Subtype.ext h)
    have hx5 : orderOf (x : Y) = 5 :=
      orderOf_eq_prime (hZexp _ hxZ) hx1
    set F : Subgroup Y := W ⊓ Z with hF
    have hFZ : F ≤ Z := inf_le_right
    have hL0 : Subgroup.zpowers (x : Y) ≤ F :=
      (Subgroup.zpowers_le).mpr ⟨hxW, hxZ⟩
    have hFinv : ∀ g ∈ N, ∀ f ∈ F, g * f * g⁻¹ ∈ F := by
      intro g hg f hf
      exact ⟨(Subgroup.mem_normalizer_iff.mp (hWN hg) f).mp hf.1,
        (Subgroup.mem_normalizer_iff.mp (hNZ hg) f).mp hf.2⟩
    intro z hz
    by_cases hz1 : z = 1
    · rw [hz1]; exact one_mem _
    have hz5 : orderOf z = 5 := orderOf_eq_prime (hZexp z hz) hz1
    obtain ⟨g, hg, hgL⟩ := htr (Subgroup.zpowers (x : Y)) (Subgroup.zpowers z)
      (hL0.trans hFZ) ((Subgroup.zpowers_le).mpr hz) (by rw [Nat.card_zpowers, hx5])
      (by rw [Nat.card_zpowers, hz5])
    have hzmem : z ∈ Subgroup.zpowers z := Subgroup.mem_zpowers z
    rw [← hgL] at hzmem
    obtain ⟨k, hk, hkz⟩ := Subgroup.mem_map.mp hzmem
    have hk' := hFinv g hg k (hL0 hk)
    have : z = g * k * g⁻¹ := by
      rw [← hkz]; simp [MulAut.conj_apply]
    rw [this]
    exact hk'.1
end Dichotomy

section Counting

theorem map_conj_eq_of_mem_normalizer {Y : Type*} [Group Y] {F : Subgroup Y} {y : Y}
    (hy : y ∈ Subgroup.normalizer (F : Set Y)) : F.map (MulAut.conj y).toMonoidHom = F := by
  ext x
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hy k).mp hk
  · intro hx
    refine ⟨y⁻¹ * x * y, ?_, by group⟩
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hy) x).mp hx
    simpa using this

theorem card_conj_set_le_relIndex {Y : Type*} [Group Y] [Finite Y] {Y₀ Y₁ F : Subgroup Y}
    (hF : Y₁ ≤ Subgroup.normalizer (F : Set Y)) (S : Finset (Subgroup Y))
    (hS : ∀ K' ∈ S, ∃ g ∈ Y₀, K' = F.map (MulAut.conj g).toMonoidHom) :
    S.card ≤ Y₁.relIndex Y₀ := by
  classical
  let r : Setoid Y₀ := QuotientGroup.leftRel (Y₁.subgroupOf Y₀)
  let f : Y₀ ⧸ Y₁.subgroupOf Y₀ → Subgroup Y :=
    Quotient.lift (fun g : Y₀ => F.map (MulAut.conj (g : Y)).toMonoidHom) (by
      intro g g' hgg
      have hgg' : g⁻¹ * g' ∈ Y₁.subgroupOf Y₀ := QuotientGroup.leftRel_apply.mp hgg
      have hy : ((g : Y)⁻¹ * (g' : Y)) ∈ Y₁ := by simpa [Subgroup.mem_subgroupOf] using hgg'
      have hn := hF hy
      have h1 : F.map (MulAut.conj ((g : Y)⁻¹ * (g' : Y))).toMonoidHom = F :=
        map_conj_eq_of_mem_normalizer hn
      have h2 : (g' : Y) = (g : Y) * ((g : Y)⁻¹ * (g' : Y)) := by group
      show F.map (MulAut.conj (g : Y)).toMonoidHom = F.map (MulAut.conj (g' : Y)).toMonoidHom
      have h3 : F.map (MulAut.conj ((g : Y) * ((g : Y)⁻¹ * (g' : Y)))).toMonoidHom =
          (F.map (MulAut.conj ((g : Y)⁻¹ * (g' : Y))).toMonoidHom).map
            (MulAut.conj (g : Y)).toMonoidHom := by
        rw [Subgroup.map_map]
        congr 1
        ext x
        simp [mul_assoc]
      rw [← h2] at h3
      rw [h3, h1])
  have hsub : (S : Set (Subgroup Y)) ⊆ Set.range f := by
    intro K' hK'
    obtain ⟨g, hg, rfl⟩ := hS K' hK'
    exact ⟨QuotientGroup.mk (⟨g, hg⟩ : Y₀), rfl⟩
  have hfin : (Set.range f).Finite := Set.finite_range f
  calc S.card = (S : Set (Subgroup Y)).ncard := (Set.ncard_coe_finset S).symm
    _ ≤ (Set.range f).ncard := Set.ncard_le_ncard hsub hfin
    _ ≤ Nat.card (Y₀ ⧸ Y₁.subgroupOf Y₀) := by
        have h1 : (Set.range f).ncard ≤ (Set.univ : Set (Y₀ ⧸ Y₁.subgroupOf Y₀)).ncard := by
          rw [← Set.image_univ]
          exact Set.ncard_image_le Set.finite_univ
        rwa [Set.ncard_univ] at h1
    _ = Y₁.relIndex Y₀ := by
        rw [Subgroup.relIndex, Subgroup.index_eq_card]

variable {Y : Type*} [Group Y] [Finite Y]

theorem eq_bot_or_eq_of_card_dvd {p : ℕ} [Fact p.Prime] {F Z : Subgroup Y} (hFZ : F ≤ Z)
    (hZ : Nat.card Z = p ^ 2) : F = ⊥ ∨ F = Z ∨ Nat.card F = p := by
  have hdvd : Nat.card F ∣ p ^ 2 := hZ ▸ Subgroup.card_dvd_of_le hFZ
  obtain ⟨k, hk, hkF⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hdvd
  interval_cases k
  · left; exact Subgroup.eq_bot_of_card_eq _ (by simpa using hkF)
  · right; right; simpa using hkF
  · right; left
    exact Subgroup.eq_of_le_of_card_ge hFZ (by rw [hZ, hkF])

theorem irred_of_six {N Y₁ Z F : Subgroup Y}
    (hidx : Y₁.relIndex N ≤ 3) (hZ : Nat.card Z = 5 ^ 2) (hFZ : F ≤ Z)
    (hFN : Y₁ ≤ Subgroup.normalizer (F : Set Y))
    (h6 : ∀ L : Subgroup Y, L ≤ Z → Nat.card L = 5 → ∃ S : Finset (Subgroup Y), 6 ≤ S.card ∧
      ∀ K' ∈ S, ∃ g ∈ N, K' = L.map (MulAut.conj g).toMonoidHom) :
    F = ⊥ ∨ F = Z := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  rcases eq_bot_or_eq_of_card_dvd hFZ hZ with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exfalso
    obtain ⟨S, hS6, hS⟩ := h6 F hFZ h
    have := card_conj_set_le_relIndex hFN S hS
    omega

end Counting

section Main

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding

theorem six_conj_of_isQ8Data {Y : Type} [Group Y] {Z : Subgroup Y} {i j h : Y}
    (hZe : IsElemAbelian 5 Z) (hZc : Nat.card Z = 5 ^ 2)
    (hQ : CFSG.Quasithin.B45Tor.IsQ8Data Z i j h) (L : Subgroup Y) (hL : L ≤ Z)
    (hLc : Nat.card L = 5) :
    ∃ S : Finset (Subgroup Y), 6 ≤ S.card ∧ ∀ K' ∈ S, ∃ g ∈ Subgroup.normalizer (Z : Set Y),
      K' = L.map (MulAut.conj g).toMonoidHom := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨S, hS6, hS⟩ := CFSG.Quasithin.B45Tor.six_le_orbit_of_eq_five (p := 5) rfl hZe.2 hZc hQ hL hLc
  refine ⟨S, hS6, fun K' hK' => ?_⟩
  obtain ⟨g, hg, rfl⟩ := hS K' hK'
  refine ⟨g, ?_, rfl⟩
  have hle : Subgroup.closure ({i, j, h} : Set Y) ≤ Subgroup.normalizer (Z : Set Y) := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    exacts [hQ.mem_i, hQ.mem_j, hQ.mem_h]
  exact hle hg

theorem lines_transitive_of_isQ8Data {Y : Type} [Group Y] {Z : Subgroup Y} {i j h : Y}
    (hZe : IsElemAbelian 5 Z) (hZc : Nat.card Z = 5 ^ 2)
    (hQ : CFSG.Quasithin.B45Tor.IsQ8Data Z i j h) (F F' : Subgroup Y) (hF : F ≤ Z)
    (hF' : F' ≤ Z) (hFc : Nat.card F = 5) (hF'c : Nat.card F' = 5) :
    ∃ g ∈ Subgroup.normalizer (Z : Set Y), F.map (MulAut.conj g).toMonoidHom = F' := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hΩ : {M : Subgroup Y | M ≤ Z ∧ Nat.card M = 5}.ncard = 5 + 1 :=
    CFSG.Quasithin.B45Tor.ncard_lines_of_plane hZc hZe.2
  obtain ⟨S, hS6, hS⟩ := six_conj_of_isQ8Data hZe hZc hQ F hF hFc
  have hΩfin : {M : Subgroup Y | M ≤ Z ∧ Nat.card M = 5}.Finite :=
    Set.finite_of_ncard_pos (by rw [hΩ]; omega)
  have hsub : (S : Set (Subgroup Y)) ⊆ {M : Subgroup Y | M ≤ Z ∧ Nat.card M = 5} := by
    intro K' hK'
    obtain ⟨g, hg, rfl⟩ := hS K' hK'
    refine ⟨?_, ?_⟩
    · intro x hx
      obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hx
      have := (Subgroup.mem_normalizer_iff.mp hg k).mp (hF hk)
      simpa [MulAut.conj_apply] using this
    · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hFc]
  have hcard : (S : Set (Subgroup Y)).ncard = S.card := Set.ncard_coe_finset S
  have heq : (S : Set (Subgroup Y)) = {M : Subgroup Y | M ≤ Z ∧ Nat.card M = 5} :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hcard, hΩ]; omega) hΩfin
  have hF'S : F' ∈ S := by
    have : F' ∈ (S : Set (Subgroup Y)) := by rw [heq]; exact ⟨hF', hF'c⟩
    exact this
  obtain ⟨g, hg, hgF⟩ := hS F' hF'S
  exact ⟨g, hg, hgF.symm⟩

theorem reeF4InSitu_normalizer_of_solvable {Y : Type} [Group Y] [Finite Y] (T : Sylow 5 Y)
    (hZe : IsElemAbelian 5 (centerOf (T : Subgroup Y)))
    (hZc : Nat.card (centerOf (T : Subgroup Y)) = 5 ^ 2)
    (hC : Subgroup.centralizer ((centerOf (T : Subgroup Y) : Subgroup Y) : Set Y) =
      (T : Subgroup Y))
    {i j h : Y} (hQ : CFSG.Quasithin.B45Tor.IsQ8Data (centerOf (T : Subgroup Y)) i j h)
    (hsolv : Group.IsSolvable ↥(Subgroup.normalizer
      ((centerOf (T : Subgroup Y) : Subgroup Y) : Set Y))) :
    ReeF4InSitu (T : Subgroup Y)
      (Subgroup.normalizer ((centerOf (T : Subgroup Y) : Subgroup Y) : Set Y)) := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set Z := centerOf (T : Subgroup Y) with hZdef
  set N := Subgroup.normalizer (Z : Set Y) with hN
  have hZT : Z ≤ (T : Subgroup Y) := inf_le_left
  have hZ' : Z = (T : Subgroup Y) ⊓ Subgroup.centralizer ((T : Subgroup Y) : Set Y) := rfl
  have hNT : N ≤ Subgroup.normalizer ((T : Subgroup Y) : Set Y) :=
    normalizer_le_normalizer_of_centralizer_eq hC
  have hTN : (T : Subgroup Y) ≤ N := hC.symm.le.trans (Subgroup.centralizer_le_normalizer _)
  have htr : ∀ F F' : Subgroup Y, F ≤ Z → F' ≤ Z → Nat.card F = 5 → Nat.card F' = 5 →
      ∃ g ∈ N, F.map (MulAut.conj g).toMonoidHom = F' :=
    fun F F' hF hF' hFc hF'c => lines_transitive_of_isQ8Data hZe hZc hQ F F' hF hF' hFc hF'c
  refine ⟨hNT, ?_, ?_, ?_, hsolv, hZe, hZc, htr, ?_⟩
  ·
    intro W hW hWN hcop
    have hWT : W ⊓ (T : Subgroup Y) = ⊥ := inf_eq_bot_of_coprime T.isPGroup' hcop
    have h1 : W ≤ Subgroup.centralizer ((T : Subgroup Y) : Set Y) :=
      le_centralizer_of_disjoint (hW.trans hNT) (hTN.trans hWN) hWT
    have h3 : W ≤ (T : Subgroup Y) :=
      (h1.trans (Subgroup.centralizer_le hZT)).trans hC.le
    rw [eq_bot_iff, ← hWT]
    exact le_inf le_rfl h3
  ·
    intro W hW hWN
    exact normal_dichotomy_of_lines T.isPGroup' hZe.2 hC hNT hTN le_rfl hW hWN htr
  ·
    exact inf_le_right.trans hC.le
  ·
    intro Y₁ hY₁ hidx F hF hFN
    exact irred_of_six hidx hZc hF hFN fun L hL hLc =>
      six_conj_of_isQ8Data hZe hZc hQ L hL hLc

end Main

end CFSG.HardMathSupport.Malle.LocalAction
