module

public import CFSG.Fischer.Classification.PartIII.U4.Points

public section

namespace CFSG.Fischer.Classification.LocalU4

open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Fischer.Classification
  CFSG.Fischer.Classification.Unitary CFSG.Fischer.Classification.Beta
  CFSG.Fischer.Classification.LocalU CFSG.ClassicalGroups.Unitary
open CFSG.Blueprint.Fischer (K)

@[expose] def InI6 (i : Fin 45) : Prop :=
  i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 15 ∨ i = 25 ∨ i = 35

instance : DecidablePred InI6 := fun i =>
  inferInstanceAs (Decidable (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 15 ∨ i = 25 ∨ i = 35))

@[expose] def InB (i : Fin 45) : Prop := 3 ≤ i.val ∧ i.val ≤ 14

instance : DecidablePred InB := fun i => inferInstanceAs (Decidable (3 ≤ i.val ∧ i.val ≤ 14))

@[expose] def InI18 (i : Fin 45) : Prop := i.val ≤ 15 ∨ i = 25 ∨ i = 35

instance : DecidablePred InI18 := fun i =>
  inferInstanceAs (Decidable (i.val ≤ 15 ∨ i = 25 ∨ i = 35))

@[expose] noncomputable def M6 : Set (PG 4) := pt '' {i | InI6 i}

@[expose] noncomputable def M18 : Set (PG 4) := pt '' {i | InI18 i}

theorem st_zero_twentyfive : st 0 25 := by decide +kernel

theorem st_fifteen_zero : st 15 0 ∧ st 15 1 ∧ st 15 2 := by decide +kernel

theorem tauI_fifteen_twentyfive : tauI 15 25 = 35 := by decide +kernel

theorem chk_twin_zero : ∀ j : Fin 45, tw 0 25 j → j = 25 ∨ (tw 0 j (zI j) ∧ j ≠ zI j) := by
  decide +kernel

theorem chk_fibres : ∀ s : Fin 45, (s = 0 ∨ s = 1 ∨ s = 2) → ∀ l, st s l →
    l = 15 ∨ l = 25 ∨ l = 35 ∨ tw s l 15 ∨ tw s l 25 ∨ tw s l 35 := by
  decide +kernel

theorem chk_classes : ∀ l : Fin 45, InI6 l ∨ InB l ∨ (st 15 l ∧ ¬(l = 0 ∨ l = 1 ∨ l = 2)) ∨
    ∃ s : Fin 45, (s = 0 ∨ s = 1 ∨ s = 2) ∧ st s l ∧ ¬(l = 15 ∨ l = 25 ∨ l = 35) := by
  decide +kernel

theorem chk_star_B : ∀ b : Fin 45, InB b → ∀ j, InI6 j → ¬ st b j := by
  decide +kernel

theorem chk_B_noncomm : ∀ b : Fin 45, InB b → ∀ l, InB l → ∀ j, InB j → st b l → st b j →
    cm l j → l = j := by
  decide +kernel

theorem chk_tau_B : ∀ b : Fin 45, InB b → InB (tauI 15 b) := by
  decide +kernel

theorem chk_B_reach : ∀ b : Fin 45, InB b → ∀ b', InB b' →
    (b' = b ∨ st b b' ∨ ∃ c, InB c ∧ st b c ∧ st c b') ∨
      (b' = tauI 15 b ∨ st (tauI 15 b) b' ∨ ∃ c, InB c ∧ st (tauI 15 b) c ∧ st c b') := by
  decide +kernel

theorem chk_I18 : ∀ l : Fin 45, InI18 l ↔ InI6 l ∨ InB l := by
  decide +kernel

theorem chk_zI_fix : zI 15 = 15 ∧ zI 0 = 0 ∧ zI 1 = 1 ∧ zI 2 = 2 := by
  decide +kernel

theorem card_I6 : (Finset.univ.filter InI6).card = 6 := by decide +kernel

theorem eq_I6_or_eq_I18 (I : Set (Fin 45)) (hτ : ∀ i ∈ I, ∀ j ∈ I, tauI i j ∈ I)
    (hTF : ∀ k ∈ I, ∀ i ∈ I, ∀ j ∈ I, tw k i j → i = j)
    (hMT : ∀ k ∈ I, ∀ i, st k i → ∃ j ∈ I, tw k i j) (hp : (15 : Fin 45) ∈ I)
    (hS : ∀ l, st 15 l → (l ∈ I ↔ (l = 0 ∨ l = 1 ∨ l = 2))) (hz : ∀ i ∈ I, zI i ∈ I) :
    I = {i | InI6 i} ∨ I = {i | InI18 i} := by
  obtain ⟨h15₀, h15₁, h15₂⟩ := st_fifteen_zero
  have h0 : (0 : Fin 45) ∈ I := (hS 0 h15₀).2 (Or.inl rfl)
  have h1 : (1 : Fin 45) ∈ I := (hS 1 h15₁).2 (Or.inr (Or.inl rfl))
  have h2 : (2 : Fin 45) ∈ I := (hS 2 h15₂).2 (Or.inr (Or.inr rfl))
  have h25 : (25 : Fin 45) ∈ I := by
    obtain ⟨j, hj, htw⟩ := hMT 0 h0 25 st_zero_twentyfive
    rcases chk_twin_zero j htw with rfl | ⟨htw', hne⟩
    · exact hj
    · exact absurd (hTF 0 h0 j hj (zI j) (hz j hj) htw') hne
  have h35 : (35 : Fin 45) ∈ I := tauI_fifteen_twentyfive ▸ hτ 15 hp 25 h25
  have hC : ∀ s, (s = 0 ∨ s = 1 ∨ s = 2) → ∀ l ∈ I, st s l → l = 15 ∨ l = 25 ∨ l = 35 := by
    intro s hs l hl hsl
    have hsI : s ∈ I := by rcases hs with rfl | rfl | rfl <;> assumption
    rcases chk_fibres s hs l hsl with h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact Or.inl (hTF s hsI l hl 15 hp h)
    · exact Or.inr (Or.inl (hTF s hsI l hl 25 h25 h))
    · exact Or.inr (Or.inr (hTF s hsI l hl 35 h35 h))
  have hD : ∀ l ∈ I, InI6 l ∨ InB l := by
    intro l hl
    rcases chk_classes l with h | h | ⟨h1, h2⟩ | ⟨s, hs, hsl, hne⟩
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd ((hS l h1).1 hl) h2
    · exact absurd (hC s hs l hl hsl) hne
  have hE : ∀ b ∈ I, InB b → ∀ l, InB l → st b l → l ∈ I := by
    intro b hb hbB l hlB hbl
    obtain ⟨j, hj, htw⟩ := hMT b hb l hbl
    rcases hD j hj with hj6 | hjB
    · exact absurd htw.2.1 (chk_star_B b hbB j hj6)
    · rw [chk_B_noncomm b hbB l hlB j hjB hbl htw.2.1 htw.2.2.1]
      exact hj
  have hF : ∀ b ∈ I, InB b → ∀ b', InB b' → b' ∈ I := by
    intro b hb hbB b' hb'B
    have hreach : ∀ x ∈ I, InB x → (b' = x ∨ st x b' ∨ ∃ c, InB c ∧ st x c ∧ st c b') →
        b' ∈ I := by
      rintro x hx hxB (rfl | h | ⟨c, hcB, hxc, hcb⟩)
      · exact hx
      · exact hE x hx hxB b' hb'B h
      · exact hE c (hE x hx hxB c hcB hxc) hcB b' hb'B hcb
    rcases chk_B_reach b hbB b' hb'B with h | h
    · exact hreach b hb hbB h
    · exact hreach _ (hτ 15 hp b hb) (chk_tau_B b hbB) h
  have hM6 : ∀ l, InI6 l → l ∈ I := by
    rintro l (rfl | rfl | rfl | rfl | rfl | rfl) <;> assumption
  by_cases hB : ∃ b ∈ I, InB b
  · obtain ⟨b, hb, hbB⟩ := hB
    refine Or.inr (Set.ext fun l => ⟨fun hl => (chk_I18 l).2 (hD l hl), fun hl => ?_⟩)
    rcases (chk_I18 l).1 hl with h | h
    · exact hM6 l h
    · exact hF b hb hbB l h
  · push Not at hB
    refine Or.inl (Set.ext fun l => ⟨fun hl => ?_, hM6 l⟩)
    rcases hD l hl with h | h
    · exact h
    · exact absurd h (hB l hl)

theorem eq_M6_or_eq_M18 {N : Set (PG 4)} (hND : N ⊆ DG 4)
    (hτ : ∀ a ∈ N, ∀ b ∈ N, a * b * a ∈ N)
    (hTF : ∀ g ∈ N, TwinFree (LocalClass (DG 4) g) (N ∩ LocalClass (DG 4) g))
    (hMT : ∀ g ∈ N, MeetsTwins (LocalClass (DG 4) g) (N ∩ LocalClass (DG 4) g))
    (hp : pt 15 ∈ N)
    (hS : N ∩ LocalClass (DG 4) (pt 15) = pt '' {l | l = 0 ∨ l = 1 ∨ l = 2})
    (hz : ∀ a ∈ N, zq * a * zq⁻¹ ∈ N) : N = M6 ∨ N = M18 := by
  have hN : N = pt '' (pt ⁻¹' N) := by
    rw [Set.image_preimage_eq_of_subset (DG_four_eq ▸ hND)]
  have key := eq_I6_or_eq_I18 (pt ⁻¹' N)
    (fun i hi j hj => by
      show pt (tauI i j) ∈ N
      rw [← pt_mul_mul]
      exact hτ _ hi _ hj)
    (fun k hk i hi j hj htw => pt_injective (hTF (pt k) hk (pt i)
      ⟨hi, (pt_mem_localClass_iff k i).2 htw.1⟩ (pt j) ⟨hj, (pt_mem_localClass_iff k j).2 htw.2.1⟩
      ((isTwin_pt_iff k i j).2 htw)))
    (fun k hk i hki => by
      obtain ⟨b, ⟨hbN, hbS⟩, htw⟩ := hMT (pt k) hk (pt i) ((pt_mem_localClass_iff k i).2 hki)
      obtain ⟨j, rfl⟩ := exists_pt_eq hbS.1
      exact ⟨j, hbN, (isTwin_pt_iff k i j).1 htw⟩)
    hp
    (fun l hl => by
      have hmem : pt l ∈ N ↔ pt l ∈ N ∩ LocalClass (DG 4) (pt 15) :=
        ⟨fun h => ⟨h, (pt_mem_localClass_iff 15 l).2 hl⟩, fun h => h.1⟩
      rw [Set.mem_preimage, hmem, hS, pt_injective.mem_set_image]
      rfl)
    (fun i hi => by
      show pt (zI i) ∈ N
      rw [← conj_zq_pt]
      exact hz _ hi)
  rcases key with h | h
  · exact Or.inl (by rw [hN, h, M6])
  · exact Or.inr (by rw [hN, h, M18])

theorem ncard_M6 : M6.ncard = 6 := by
  rw [M6, ← card_I6, ← ncard_image_pt]
  congr 2
  ext i
  simp

@[expose] def FlagInv {Y : Type} [Group Y] (p : Y) (S N : Set Y) : Prop :=
  ∀ h : Y, h * p * h⁻¹ = p → (fun s => h * s * h⁻¹) '' S = S →
    (fun s => h * s * h⁻¹) '' N = N

theorem image_conj_map {X Y : Type} [Group X] [Group Y] (φ : X ≃* Y) (h : X) (T : Set X) :
    φ '' ((fun s => h * s * h⁻¹) '' T) = (fun s => φ h * s * (φ h)⁻¹) '' (φ '' T) := by
  rw [Set.image_image, Set.image_image]
  exact Set.image_congr fun s _ => by rw [map_mul, map_mul, map_inv]

theorem FlagInv.map {X Y : Type} [Group X] [Group Y] (φ : X ≃* Y) {p : X} {S N : Set X}
    (hN : FlagInv p S N) : FlagInv (φ p) (φ '' S) (φ '' N) := by
  intro h hp hS
  have hp' : φ.symm h * p * (φ.symm h)⁻¹ = p :=
    φ.injective (by rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hp])
  have hS' : (fun s => φ.symm h * s * (φ.symm h)⁻¹) '' S = S := by
    have h1 := image_conj_map φ (φ.symm h) S
    rw [MulEquiv.apply_symm_apply, hS] at h1
    exact (Set.image_injective.2 φ.injective) h1
  rw [← MulEquiv.apply_symm_apply φ h, ← image_conj_map, hN _ hp' hS']

theorem conj_image_inter_localClass {Y : Type} [Group Y] {F : Set Y} (hP : Pair Y F) (c : Y)
    (N : Set Y) (g : Y) :
    (fun s => c * s * c⁻¹) '' (N ∩ LocalClass F g) =
      (fun s => c * s * c⁻¹) '' N ∩ LocalClass F (c * g * c⁻¹) := by
  rw [Set.image_inter (conj_injective c), Pair.image_conj_localClass hP]

theorem twinFree_conj {Y : Type} [Group Y] {F : Set Y} (hP : Pair Y F) (c : Y) {p : Y}
    {S : Set Y} (h : TwinFree (LocalClass F p) S) :
    TwinFree (LocalClass F (c * p * c⁻¹)) ((fun s => c * s * c⁻¹) '' S) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ htw
  have e : ∀ x : Y, c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ = x := fun x => by group
  have h1 := isTwin_conj hP c⁻¹ htw
  dsimp only at h1
  rw [e, e, e] at h1
  rw [h a ha b hb h1]

theorem meetsTwins_conj {Y : Type} [Group Y] {F : Set Y} (hP : Pair Y F) (c : Y) {p : Y}
    {S : Set Y} (h : MeetsTwins (LocalClass F p) S) :
    MeetsTwins (LocalClass F (c * p * c⁻¹)) ((fun s => c * s * c⁻¹) '' S) := by
  intro y hy
  rw [← Pair.image_conj_localClass hP] at hy
  obtain ⟨a, ha, rfl⟩ := hy
  obtain ⟨b, hb, htw⟩ := h a ha
  exact ⟨c * b * c⁻¹, ⟨b, hb, rfl⟩, isTwin_conj hP c htw⟩

theorem exists_conj_flag {g q : PG 4} (hg : g ∈ DG 4) (hq : q ∈ DG 4) (hqg : q * g ≠ g * q) :
    ∃ c : PG 4, c * g * c⁻¹ = pt 15 ∧
      (fun s => c * s * c⁻¹) '' muSet (DG 4) g q = pt '' {l | l = 0 ∨ l = 1 ∨ l = 2} := by
  have hPG : Pair (PG 4) (DG 4) := pair_DG le_rfl
  obtain ⟨c₁, hc₁⟩ := isConj_iff.1 (Pair.isConj hPG hg (tq_mem_DG (v₀_ne_zero (n := 2))
    herm_v₀_v₀))
  have hq' : c₁ * q * c₁⁻¹ ∈ DG 4 := Pair.conj_mem hPG hq c₁
  have hqv : c₁ * q * c₁⁻¹ * tq (v₀ 2) ≠ tq (v₀ 2) * (c₁ * q * c₁⁻¹) := by
    rw [← hc₁, ne_eq, conj_commute_iff]
    exact hqg
  obtain ⟨y, hy⟩ := exists_muY_eq_muSet (n := 2) (by norm_num) hq' hqv
  obtain ⟨g₂, hgv, hgu⟩ := exists_smul_eq_hyp (n := 2) (by norm_num) v₀_ne_zero herm_v₀_v₀
    (herm_uy_uy y) (herm_v₀_uy y)
  set c₂ : PG 4 := QuotientGroup.mk g₂ with hc₂def
  have hc₂v : c₂ * tq (v₀ 2) * c₂⁻¹ = tq (v₀ 2) := by
    rw [hc₂def, conj_tq g₂ herm_v₀_v₀, hgv]
  refine ⟨c₂ * c₁, ?_, ?_⟩
  · have e : c₂ * c₁ * g * (c₂ * c₁)⁻¹ = c₂ * (c₁ * g * c₁⁻¹) * c₂⁻¹ := by group
    rw [e, hc₁, hc₂v, tq_v₀_eq]
  · have e1 : (fun s => c₂ * c₁ * s * (c₂ * c₁)⁻¹) '' muSet (DG 4) g q =
        (fun s => c₂ * s * c₂⁻¹) '' ((fun s => c₁ * s * c₁⁻¹) '' muSet (DG 4) g q) := by
      rw [Set.image_image]
      exact Set.image_congr fun s _ => by group
    rw [e1, Pair.image_conj_muSet hPG, hc₁, hy, muY, Pair.image_conj_muSet hPG, hc₂v,
      hc₂def, conj_tq g₂ (herm_uy_uy y), hgu,
      muSet_eq_muY (by norm_num) herm_u₀_u₀ herm_v₀_u₀, π_u₀, ← muY_zero_eq]

theorem zq_fix_flag : zq * pt 15 * zq⁻¹ = pt 15 ∧
    (fun s => zq * s * zq⁻¹) '' (pt '' {l | l = 0 ∨ l = 1 ∨ l = 2}) =
      pt '' {l | l = 0 ∨ l = 1 ∨ l = 2} := by
  obtain ⟨e15, e0, e1, e2⟩ := chk_zI_fix
  refine ⟨by rw [conj_zq_pt, e15], ?_⟩
  rw [Set.image_image]
  refine Set.image_congr fun l hl => ?_
  rw [conj_zq_pt]
  rcases hl with rfl | rfl | rfl
  · rw [e0]
  · rw [e1]
  · rw [e2]

theorem exists_conj_eq_M6_or_M18 {N : Set (PG 4)} (hND : N ⊆ DG 4)
    (hτ : ∀ a ∈ N, ∀ b ∈ N, a * b * a ∈ N)
    (hTF : ∀ g ∈ N, TwinFree (LocalClass (DG 4) g) (N ∩ LocalClass (DG 4) g))
    (hMT : ∀ g ∈ N, MeetsTwins (LocalClass (DG 4) g) (N ∩ LocalClass (DG 4) g))
    {g₀ q₀ : PG 4} (hg₀ : g₀ ∈ N) (hq₀ : q₀ ∈ DG 4) (hq₀g₀ : q₀ * g₀ ≠ g₀ * q₀)
    (hS₀ : N ∩ LocalClass (DG 4) g₀ = muSet (DG 4) g₀ q₀)
    (hinv : FlagInv g₀ (N ∩ LocalClass (DG 4) g₀) N) :
    ∃ c : PG 4, (fun s => c * s * c⁻¹) '' N = M6 ∨ (fun s => c * s * c⁻¹) '' N = M18 := by
  have hPG : Pair (PG 4) (DG 4) := pair_DG le_rfl
  obtain ⟨c, hcg, hcS⟩ := exists_conj_flag (hND hg₀) hq₀ hq₀g₀
  refine ⟨c, eq_M6_or_eq_M18 ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact Pair.conj_mem hPG (hND ha) c
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact ⟨a * b * a, hτ a ha b hb, by group⟩
  · rintro _ ⟨g, hg, rfl⟩
    rw [← conj_image_inter_localClass hPG]
    exact twinFree_conj hPG c (hTF g hg)
  · rintro _ ⟨g, hg, rfl⟩
    rw [← conj_image_inter_localClass hPG]
    exact meetsTwins_conj hPG c (hMT g hg)
  · exact ⟨g₀, hg₀, hcg⟩
  · rw [← hcg, ← conj_image_inter_localClass hPG, hS₀, hcS]
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := ha
    set h := c⁻¹ * zq * c with hh
    have hS' : (fun s => c * s * c⁻¹) '' (N ∩ LocalClass (DG 4) g₀) =
        pt '' {l | l = 0 ∨ l = 1 ∨ l = 2} := by
      rw [hS₀, hcS]
    have hhg : h * g₀ * h⁻¹ = g₀ := by
      have e : h * g₀ * h⁻¹ = c⁻¹ * (zq * (c * g₀ * c⁻¹) * zq⁻¹) * c := by
        rw [hh]
        group
      rw [e, hcg, zq_fix_flag.1, ← hcg]
      group
    have hhS : (fun s => h * s * h⁻¹) '' (N ∩ LocalClass (DG 4) g₀) =
        N ∩ LocalClass (DG 4) g₀ := by
      have e : (fun s => h * s * h⁻¹) '' (N ∩ LocalClass (DG 4) g₀) =
          (fun s => c⁻¹ * s * c⁻¹⁻¹) '' ((fun s => zq * s * zq⁻¹) ''
            ((fun s => c * s * c⁻¹) '' (N ∩ LocalClass (DG 4) g₀))) := by
        rw [Set.image_image, Set.image_image]
        exact Set.image_congr fun s _ => by rw [hh]; group
      rw [e, hS', zq_fix_flag.2, ← hS', Set.image_image]
      conv_rhs => rw [← Set.image_id (N ∩ LocalClass (DG 4) g₀)]
      exact Set.image_congr fun s _ => by rw [id]; group
    have hmem : h * b * h⁻¹ ∈ N := by
      rw [← hinv h hhg hhS]
      exact ⟨b, hb, rfl⟩
    exact ⟨h * b * h⁻¹, hmem, by rw [hh]; group⟩

end CFSG.Fischer.Classification.LocalU4
