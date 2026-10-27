module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7SFa
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FactsS
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrVocB

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G]

private lemma zpow_eq_one_or_self {v : G} (hv : v * v = 1) (m : ℤ) :
    v ^ m = 1 ∨ v ^ m = v := by
  have hv2 : v ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hv
  obtain ⟨j, hj | hj⟩ := Int.even_or_odd' m
  · left; rw [hj, zpow_mul, hv2, one_zpow]
  · right; rw [hj, zpow_add, zpow_mul, hv2, one_zpow, one_mul, zpow_one]

private lemma eq_one_or_eq_of_mem_zpowers {v g : G} (hv : v * v = 1) (hg : g ∈ zpowers v) :
    g = 1 ∨ g = v := by
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
  exact zpow_eq_one_or_self hv i

private lemma exists_mul_of_mem_sup {H K : Subgroup G}
    (hc : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) {g : G} (hg : g ∈ H ⊔ K) :
    ∃ h ∈ H, ∃ k ∈ K, g = h * k := by
  let S : Subgroup G :=
    { carrier := {g | ∃ h ∈ H, ∃ k ∈ K, g = h * k}
      one_mem' := ⟨1, one_mem _, 1, one_mem _, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨h₁, hh₁, k₁, hk₁, rfl⟩ ⟨h₂, hh₂, k₂, hk₂, rfl⟩
        refine ⟨h₁ * h₂, mul_mem hh₁ hh₂, k₁ * k₂, mul_mem hk₁ hk₂, ?_⟩
        calc h₁ * k₁ * (h₂ * k₂) = h₁ * (k₁ * h₂) * k₂ := by group
          _ = h₁ * (h₂ * k₁) * k₂ := by rw [← hc h₂ hh₂ k₁ hk₁]
          _ = h₁ * h₂ * (k₁ * k₂) := by group
      inv_mem' := by
        rintro _ ⟨h, hh, k, hk, rfl⟩
        refine ⟨h⁻¹, inv_mem hh, k⁻¹, inv_mem hk, ?_⟩
        calc (h * k)⁻¹ = (k * h)⁻¹ := by rw [hc h hh k hk]
          _ = h⁻¹ * k⁻¹ := by group }
  have hle : H ⊔ K ≤ S := sup_le (fun h hh => ⟨h, hh, 1, one_mem _, by simp⟩)
    (fun k hk => ⟨1, one_mem _, k, hk, by simp⟩)
  exact hle hg

private lemma exists_invols_classes12 (fr : Frame G) (h12 : fr.Fact12) (i : Fin 7) :
    ∃ y, y ∈ fr.S ∧ orderOf y = 2 ∧ fr.classes12 i = conjClass fr.S y := by
  obtain ⟨c1, _⟩ := h12
  have hmem : fr.classes12 i ∈ Set.range fr.classes12 := Set.mem_range_self i
  rw [← c1] at hmem
  simpa only [invols, Set.mem_setOf_eq, and_assoc] using hmem

private lemma mem_classes12_aux (fr : Frame G) (h12 : fr.Fact12) {i : Fin 7} {x : G}
    (hx : x ∈ fr.classes12 i) : x ∈ fr.S ∧ x ^ 2 = 1 ∧ x ≠ 1 := by
  obtain ⟨y, hyS, hyord, hyi⟩ := exists_invols_classes12 fr h12 i
  rw [hyi] at hx
  obtain ⟨s, hs, rfl⟩ := hx
  have hy2 : y ^ 2 = 1 := by rw [← hyord]; exact pow_orderOf_eq_one y
  refine ⟨?_, ?_, ?_⟩
  · exact fr.S.mul_mem (fr.S.mul_mem hs hyS) (fr.S.inv_mem hs)
  · rw [conj_pow, hy2, mul_one, mul_inv_cancel]
  · intro h
    have hy1 : y = 1 := by
      have h' := congrArg (fun z => s⁻¹ * z * s) h
      simpa [mul_assoc] using h'
    rw [hy1, orderOf_one] at hyord
    omega

private lemma classes12_injective (fr : Frame G) (h12 : fr.Fact12) :
    Function.Injective fr.classes12 :=
  h12.2.1

private lemma conjClass_eq_of_mem {S : Subgroup G} {y w : G} (h : w ∈ conjClass S y) :
    conjClass S w = conjClass S y := by
  obtain ⟨a, ha, rfl⟩ := h
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t * a, S.mul_mem ht ha, by group⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t * a⁻¹, S.mul_mem ht (S.inv_mem ha), by group⟩

private lemma classes12_eq_of_mem (fr : Frame G) (h12 : fr.Fact12) {i j : Fin 7} {x : G}
    (hi : x ∈ fr.classes12 i) (hj : x ∈ fr.classes12 j) : i = j := by
  obtain ⟨y, _, _, hyi⟩ := exists_invols_classes12 fr h12 i
  obtain ⟨y', _, _, hyj⟩ := exists_invols_classes12 fr h12 j
  rw [hyi] at hi
  rw [hyj] at hj
  obtain ⟨s, hs, rfl⟩ := hi
  obtain ⟨s', hs', hxs'⟩ := hj
  have hy' : y' ∈ conjClass fr.S y := by
    refine ⟨s'⁻¹ * s, fr.S.mul_mem (fr.S.inv_mem hs') hs, ?_⟩
    calc y' = s'⁻¹ * (s' * y' * s'⁻¹) * s' := by group
      _ = s'⁻¹ * (s * y * s⁻¹) * s' := by rw [← hxs']
      _ = (s'⁻¹ * s) * y * (s'⁻¹ * s)⁻¹ := by group
  exact classes12_injective fr h12 (by rw [hyi, hyj, conjClass_eq_of_mem hy'])

private lemma isElemAbelian_top_iff {X : Subgroup G} :
    IsElemAbelian 2 (⊤ : Subgroup X) ↔ IsElemAbelian 2 X := by
  constructor
  · intro h
    refine ⟨IsMulCommutative.of_comm ?_, ?_⟩
    · intro a b
      exact congrArg Subtype.val
        (h.1.is_comm.comm (⟨a, trivial⟩ : ↥(⊤ : Subgroup X)) ⟨b, trivial⟩)
    · intro x hx
      have hx2 := h.2 ⟨x, hx⟩ trivial
      simpa using congrArg (fun z : X => (z : G)) hx2
  · intro h
    haveI := h.1
    refine ⟨IsMulCommutative.of_comm ?_, ?_⟩
    · intro a b
      exact Subtype.ext (mul_comm' a.1 b.1)
    · intro x _
      exact Subtype.ext (h.2 (x : G) x.2)

private lemma isE_toSub {X : Subgroup G} (h : IsE 3 ↥X) :
    IsElemAbelian 2 X ∧ Nat.card X = 8 :=
  ⟨isElemAbelian_top_iff.mp h.1, by rw [h.2]; norm_num⟩

private lemma z_mem_S (fr : Frame G) : fr.z ∈ fr.S := by
  show fr.b₁ ^ 2 ∈ fr.S
  exact fr.S.pow_mem (Subgroup.subset_closure (by simp)) 2

private lemma F_le_S (fr : Frame G) : fr.F ≤ fr.S := by
  refine (Subgroup.closure_le fr.S).mpr ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact fr.S.mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  · exact fr.S.mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  · exact z_mem_S fr

private lemma E_le_S (fr : Frame G) : fr.E ≤ fr.S := by
  refine (Subgroup.closure_le fr.S).mpr ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact fr.S.mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  · exact fr.S.mul_mem (fr.S.mul_mem (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))) (Subgroup.subset_closure (by simp))
  · exact z_mem_S fr

private lemma conjSub_le_of_mem {c : G} {Y T : Subgroup G} (hc : c ∈ T) (hY : Y ≤ T) :
    conjSub c Y ≤ T := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  show c * y * c⁻¹ ∈ T
  exact T.mul_mem (T.mul_mem hc (hY hy)) (T.inv_mem hc)

private lemma card_conjSub (c : G) (E : Subgroup G) :
    Nat.card ↥(conjSub c E) = Nat.card ↥E :=
  Subgroup.card_map_of_injective (f := (MulAut.conj c).toMonoidHom) (MulAut.conj c).injective

private def rep12 (fr : Frame G) : Fin 7 → G :=
  ![fr.z, fr.b₁ * fr.b₂, fr.a₁ * fr.a₂, fr.a₁ * fr.b₂, fr.b₁ * fr.a₂,
    fr.a₁ * fr.b₁ * fr.a₂, fr.h₀]

private lemma rep12_mem_classes12 (fr : Frame G) (i : Fin 7) :
    rep12 fr i ∈ fr.classes12 i := by
  fin_cases i <;> simp [rep12, Frame.classes12, Matrix.cons_val]

private lemma rep12_cover (fr : Frame G) (h12 : fr.Fact12)
    (hE : IsE 3 ↥fr.E) (hF : IsE 3 ↥fr.F)
    (hW : closure {fr.a₁ * fr.b₂, fr.b₁ * fr.a₂, fr.z} ≤ fr.S ∧
      IsElemAbelian 2 (closure {fr.a₁ * fr.b₂, fr.b₁ * fr.a₂, fr.z}) ∧
      Nat.card ↥(closure {fr.a₁ * fr.b₂, fr.b₁ * fr.a₂, fr.z}) = 8) (i : Fin 7) :
    ∃ E : Subgroup G, E ≤ fr.S ∧ IsElemAbelian 2 E ∧ Nat.card E = 8 ∧ rep12 fr i ∈ E := by
  fin_cases i
  · exact ⟨fr.F, F_le_S fr, (isE_toSub hF).1, (isE_toSub hF).2,
      Subgroup.subset_closure (by simp [rep12, Matrix.cons_val])⟩
  · exact ⟨fr.F, F_le_S fr, (isE_toSub hF).1, (isE_toSub hF).2,
      Subgroup.subset_closure (by simp [rep12, Matrix.cons_val])⟩
  · exact ⟨fr.F, F_le_S fr, (isE_toSub hF).1, (isE_toSub hF).2,
      Subgroup.subset_closure (by simp [rep12, Matrix.cons_val])⟩
  · exact ⟨_, hW.1, hW.2.1, hW.2.2,
      Subgroup.subset_closure (by simp [rep12, Matrix.cons_val])⟩
  · exact ⟨_, hW.1, hW.2.1, hW.2.2,
      Subgroup.subset_closure (by simp [rep12, Matrix.cons_val])⟩
  · exact ⟨fr.E, E_le_S fr, (isE_toSub hE).1, (isE_toSub hE).2,
      Subgroup.subset_closure (by simp [rep12, Matrix.cons_val])⟩
  · obtain ⟨_, _, _, _, _, _, _, _, c9, c10⟩ := h12
    refine ⟨centEl fr.S fr.h₀, inf_le_left, (isE_toSub c10).1, (isE_toSub c10).2, ?_⟩
    rw [c9]
    exact Subgroup.subset_closure (by simp [rep12, Matrix.cons_val])

theorem frame_W_isE3 (fr : Frame G) (h12 : fr.Fact12) (h14 : fr.Fact14) :
    closure {fr.a₁ * fr.b₂, fr.b₁ * fr.a₂, fr.z} ≤ fr.S ∧
    IsElemAbelian 2 (closure {fr.a₁ * fr.b₂, fr.b₁ * fr.a₂, fr.z}) ∧
    Nat.card ↥(closure {fr.a₁ * fr.b₂, fr.b₁ * fr.a₂, fr.z}) = 8 := by
  have _h14 := h14
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩ := h12
  have h12' : fr.Fact12 := ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩
  have ha3 : fr.a₁ * fr.b₂ ∈ fr.classes12 3 := by simp [Frame.classes12, Matrix.cons_val]
  have hb4 : fr.b₁ * fr.a₂ ∈ fr.classes12 4 := by simp [Frame.classes12, Matrix.cons_val]
  have hz0 : fr.z ∈ fr.classes12 0 := by simp [Frame.classes12, Matrix.cons_val]
  have hbz4 : fr.b₁ * fr.a₂ * fr.z ∈ fr.classes12 4 := by
    simp [Frame.classes12, Matrix.cons_val]
  have hs1 : (fr.a₁ * fr.b₂) ^ 2 = 1 := (mem_classes12_aux fr h12' ha3).2.1
  have hs2 : (fr.b₁ * fr.a₂) ^ 2 = 1 := (mem_classes12_aux fr h12' hb4).2.1
  have hs3 : fr.z ^ 2 = 1 := (mem_classes12_aux fr h12' hz0).2.1
  have hn2 : fr.b₁ * fr.a₂ ≠ 1 := (mem_classes12_aux fr h12' hb4).2.2
  have hn3 : fr.z ≠ 1 := (mem_classes12_aux fr h12' hz0).2.2
  have hn23 : fr.b₁ * fr.a₂ ≠ fr.z := by
    intro h
    exact absurd (classes12_eq_of_mem fr h12' hb4 (h.symm ▸ hz0)) (by decide)
  have hzS : fr.S ≤ Subgroup.centralizer ({fr.z} : Set G) := by
    rw [← c3]; exact inf_le_right
  have hab2S : fr.a₁ * fr.b₂ ∈ fr.S :=
    fr.S.mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  have hba2S : fr.b₁ * fr.a₂ ∈ fr.S :=
    fr.S.mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  have hz13 : (fr.a₁ * fr.b₂) * fr.z = fr.z * (fr.a₁ * fr.b₂) :=
    Subgroup.mem_centralizer_singleton_iff.mp (hzS hab2S)
  have hz23 : (fr.b₁ * fr.a₂) * fr.z = fr.z * (fr.b₁ * fr.a₂) :=
    Subgroup.mem_centralizer_singleton_iff.mp (hzS hba2S)
  have hc12 : (fr.a₁ * fr.b₂) * (fr.b₁ * fr.a₂) = (fr.b₁ * fr.a₂) * (fr.a₁ * fr.b₂) :=
    c6.1.2.2 _ (Subgroup.subset_closure (by simp)) _ (Subgroup.subset_closure (by simp))
  have hn1 : fr.a₁ * fr.b₂ ∉ closure ({fr.b₁ * fr.a₂, fr.z} : Set G) := by
    intro h
    have hzpow : closure ({fr.b₁ * fr.a₂, fr.z} : Set G) =
        zpowers (fr.b₁ * fr.a₂) ⊔ zpowers fr.z := by
      rw [← Set.singleton_union, Subgroup.closure_union, zpowers_eq_closure, zpowers_eq_closure]
    rw [hzpow] at h
    have hcomm : ∀ a ∈ zpowers (fr.b₁ * fr.a₂), ∀ b ∈ zpowers fr.z, a * b = b * a := by
      intro a ha b hb
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      exact (Commute.zpow_zpow (show Commute (fr.b₁ * fr.a₂) fr.z from hz23) i j).eq
    obtain ⟨g₁, hg₁, g₂, hg₂, hg₁₂⟩ := exists_mul_of_mem_sup hcomm h
    rcases eq_one_or_eq_of_mem_zpowers (by simpa [pow_two] using hs2) hg₁ with rfl | rfl <;>
      rcases eq_one_or_eq_of_mem_zpowers (by simpa [pow_two] using hs3) hg₂ with rfl | rfl
    · rw [one_mul] at hg₁₂
      exact (mem_classes12_aux fr h12' ha3).2.2 hg₁₂
    · rw [one_mul] at hg₁₂
      exact absurd (classes12_eq_of_mem fr h12' hz0 (hg₁₂ ▸ ha3)) (by decide)
    · rw [mul_one] at hg₁₂
      exact absurd (classes12_eq_of_mem fr h12' hb4 (hg₁₂ ▸ ha3)) (by decide)
    · exact absurd (classes12_eq_of_mem fr h12' hbz4 (hg₁₂ ▸ ha3)) (by decide)
  have hmain := isE3_closure_of_commuting hs1 hs2 hs3 hc12 hz13 hz23 hn1 hn2 hn3 hn23
  refine ⟨?_, hmain.1, hmain.2⟩
  refine (Subgroup.closure_le fr.S).mpr ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact hab2S
  · exact hba2S
  · exact z_mem_S fr

theorem frame_cover (fr : Frame G) (h12 : fr.Fact12) (h14 : fr.Fact14)
    (hE : IsE 3 ↥fr.E) (hF : IsE 3 ↥fr.F) :
    ∀ y ∈ fr.S, y ^ 2 = 1 →
      ∃ E : Subgroup G, E ≤ fr.S ∧ IsElemAbelian 2 E ∧ Nat.card E = 8 ∧ y ∈ E := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro y hyS hy2
  by_cases hy1 : y = 1
  · refine ⟨fr.F, F_le_S fr, (isE_toSub hF).1, (isE_toSub hF).2, ?_⟩
    rw [hy1]; exact fr.F.one_mem
  · have hyord : orderOf y = 2 := orderOf_eq_prime hy2 hy1
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩ := h12
    have h12' : fr.Fact12 := ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩
    have hmem : conjClass fr.S y ∈ Set.range fr.classes12 := by
      rw [← c1]
      exact ⟨y, ⟨hyS, hyord⟩, rfl⟩
    obtain ⟨i, hi⟩ := hmem
    have hrep : rep12 fr i ∈ conjClass fr.S y := by
      rw [← hi]; exact rep12_mem_classes12 fr i
    obtain ⟨s', hs', hseq⟩ := hrep
    obtain ⟨E₀, hE₀S, hE₀E, hE₀card, hrep_in⟩ :=
      rep12_cover fr h12' hE hF (frame_W_isE3 fr h12' h14) i
    refine ⟨conjSub s'⁻¹ E₀, ?_, ?_, ?_, ?_⟩
    · exact conjSub_le_of_mem (fr.S.inv_mem hs') hE₀S
    · exact (isElemAbelian_map (f := (MulAut.conj s'⁻¹).toMonoidHom)
        (MulAut.conj s'⁻¹).injective 2 E₀).mpr hE₀E
    · rw [card_conjSub]; exact hE₀card
    · have hyeq : y = s'⁻¹ * rep12 fr i * s' := by rw [hseq]; group
      rw [hyeq]
      exact Subgroup.mem_map.mpr ⟨rep12 fr i, hrep_in, by
        show (MulAut.conj s'⁻¹) (rep12 fr i) = s'⁻¹ * rep12 fr i * s'
        rw [MulAut.conj_apply]; group⟩

end CFSG.OddStandard.HigherRank.YamadaG23
