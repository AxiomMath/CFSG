module

public import CFSG.Certificates.Kernel.SporSch.ChainKEnum
public import Certificates.Data.Kernel.SporSch.SliceK

public section

namespace CFSG.KS.SporSch.MOC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.Prim CFSG.KS.M11
open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Th
open CFSG.Sporadic.Th.Native CFSG.Monster.B.Mathieu

theorem countP_conj {G : Type*} [Group G] {H : Subgroup G} {E : List G} (hE : E.Nodup)
    (hm : ∀ g, g ∈ E ↔ g ∈ H) {u : G} (hu : u ∈ H) (p : G → Bool) :
    E.countP p = E.countP (fun g => p (u * g * u⁻¹)) := by
  have hperm : (E.map fun g => u * g * u⁻¹).Perm E := by
    refine (List.perm_ext_iff_of_nodup (hE.map fun x y hxy => ?_) hE).2 fun a => ?_
    · simpa using hxy
    · simp only [List.mem_map, hm]
      constructor
      · rintro ⟨g, hg, rfl⟩
        exact H.mul_mem (H.mul_mem hu hg) (H.inv_mem hu)
      · intro ha
        exact ⟨u⁻¹ * a * u, H.mul_mem (H.mul_mem (H.inv_mem hu) ha) hu, by group⟩
  rw [← hperm.countP_eq, List.countP_map]
  rfl

theorem sum_range_ite {k₀ : Nat} (f : Nat → Nat) :
    ∀ c, k₀ < c → ((List.range c).map fun j => if j = k₀ then f j else 0).sum = f k₀
  | 0, h => absurd h (Nat.not_lt_zero _)
  | c + 1, h => by
    rw [List.range_succ, List.map_append, List.sum_append]
    by_cases hc : k₀ < c
    · rw [sum_range_ite f c hc]
      simp [Nat.ne_of_gt hc]
    · have e : c = k₀ := by omega
      subst e
      have hz : ((List.range c).map fun j => if j = c then f j else 0).sum = 0 := by
        apply List.sum_eq_zero
        intro x hx
        obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
        simp [Nat.ne_of_lt (List.mem_range.1 ha)]
      simp [hz]

theorem anyLtK_spec {f : Nat → Bool} : ∀ {m : Nat}, anyLtK f m = true → ∃ j < m, f j = true
  | 0, h => absurd h Bool.false_ne_true
  | m + 1, h => by
    change Bool.rec (motive := fun _ => Bool) (anyLtK f m) true (f m) = true at h
    cases hf : f m
    · rw [hf] at h
      obtain ⟨j, hj, hfj⟩ := anyLtK_spec h
      exact ⟨j, by omega, hfj⟩
    · exact ⟨m, by omega, hf⟩

variable {n w : Nat} {gens : List (Equiv.Perm (Fin n))} {words : List (List Int)} {k : Nat}
  {bv : Vector (Fin n) k} {PS PSI LR TR TRI : Nat → Nat} {kS BP NS CH : Nat}

@[expose] noncomputable def tailP (n w : Nat) (LR TR : Nat → Nat) (k : Nat) :
    List (Equiv.Perm (Fin n)) :=
  products ((List.range (k - 1)).map fun t => trL n w LR TR (1 + t))

section Chain

variable (hQ : ChainK n w gens words bv PS PSI LR TR TRI kS BP NS CH) (hn : 1 ≤ n)
  (hbs : bv.toList.Nodup)
include hQ hn hbs

theorem trP_mem_level {i k' : Nat} (hi : i < k) (hk' : k' < rcnt (LR i)) :
    trP n w LR TR i k' ∈ (certificate hn gens words bv hbs).levelSubgroup i :=
  mem_levelSubgroup_of_mem_levelTransversals (certificate hn gens words bv hbs) ⟨i, hi⟩
    (by
      rw [levelTransversals_eq hQ hn hbs hi]
      exact List.mem_map.2 ⟨k', List.mem_range.2 hk', rfl⟩)

theorem level_le_original (i : Nat) :
    (certificate hn gens words bv hbs).levelSubgroup i ≤
      (certificate hn gens words bv hbs).originalSubgroup := by
  rw [← (certificate hn gens words bv hbs).levelSubgroup_zero_eq_original
    (chainK_check hn hbs hQ).1]
  exact (certificate hn gens words bv hbs).levelSubgroup_antitone 0 i (Nat.zero_le _)

theorem level_one_fix (hk : 0 < k) {g : Equiv.Perm (Fin n)}
    (hg : g ∈ (certificate hn gens words bv hbs).levelSubgroup 1) :
    g (bv.get ⟨0, hk⟩) = bv.get ⟨0, hk⟩ :=
  (certificate hn gens words bv hbs).levelSubgroup_fixes_base_index 1 g hg ⟨0, hk⟩ Nat.one_pos

theorem tailP_mem (hk : 0 < k) :
    ∀ p ∈ tailP n w LR TR k, p ∈ (certificate hn gens words bv hbs).levelSubgroup 1 := by
  apply mem_of_mem_products ((certificate hn gens words bv hbs).levelSubgroup 1).toSubmonoid
  intro T hT t ht
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hT
  obtain ⟨k', hk', rfl⟩ := List.mem_map.1 ht
  have hi' := List.mem_range.1 hi
  exact (certificate hn gens words bv hbs).levelSubgroup_antitone 1 (1 + i) (by omega)
    (trP_mem_level hQ hn hbs (by omega) (List.mem_range.1 hk'))

theorem trP_zero_inj (hk : 0 < k) {k₁ k₂ : Nat} (h₁ : k₁ < rcnt (LR 0)) (h₂ : k₂ < rcnt (LR 0))
    (h : trP n w LR TR 0 k₁ (bv.get ⟨0, hk⟩) = trP n w LR TR 0 k₂ (bv.get ⟨0, hk⟩)) :
    k₁ = k₂ := by
  set Q := certificate hn gens words bv hbs
  have hT := levelTransversals_eq hQ hn hbs hk
  have hkeys : ((List.range (rcnt (LR 0))).map fun j => trP n w LR TR 0 j (bv.get ⟨0, hk⟩)) =
      (Q.orbitSearch ⟨0, hk⟩).keys := by
    have e : ((List.range (rcnt (LR 0))).map fun j => trP n w LR TR 0 j (bv.get ⟨0, hk⟩)) =
        (levelTransversals Q ⟨0, hk⟩).map fun t => t (bv.get ⟨0, hk⟩) := by
      rw [hT, List.map_map]
      rfl
    rw [e, levelTransversals, List.map_map]
    conv_rhs => rw [← List.map_id (Q.orbitSearch ⟨0, hk⟩).keys]
    apply List.map_congr_left
    intro x hx
    have hx' : x ∈ Q.orbitPoints ⟨0, hk⟩ :=
      (SchreierOrbitState.mem_points_iff_mem_keys (Q.orbitSearch ⟨0, hk⟩) x).2 hx
    exact (Q.transversal_getD_spec ⟨0, hk⟩ x hx').2.2
  have hnd : ((List.range (rcnt (LR 0))).map fun j =>
      trP n w LR TR 0 j (bv.get ⟨0, hk⟩)).Nodup := by
    rw [hkeys]
    exact Q.orbitSearch_keys_nodup ⟨0, hk⟩
  exact List.inj_on_of_nodup_map hnd (List.mem_range.2 h₁) (List.mem_range.2 h₂) h

theorem slice_eq (hk : 0 < k) (q : Equiv.Perm (Fin n) → Bool) {k₀ : Nat}
    (hk₀ : k₀ < rcnt (LR 0)) :
    ((tailP n w LR TR k).map (trP n w LR TR 0 k₀ * ·)).countP q =
      (enumeration (certificate hn gens words bv hbs)).countP (fun g =>
        decide (g (bv.get ⟨0, hk⟩) = trP n w LR TR 0 k₀ (bv.get ⟨0, hk⟩)) && q g) := by
  have e1 := countP_coset1 hQ hn hbs hk (fun g =>
    decide (g (bv.get ⟨0, hk⟩) = trP n w LR TR 0 k₀ (bv.get ⟨0, hk⟩)) && q g) 1
  have hmap : (enumeration (certificate hn gens words bv hbs)).map (fun x => 1 * x) =
      enumeration (certificate hn gens words bv hbs) := by simp
  rw [hmap] at e1
  rw [e1]
  symm
  have hterm : ∀ k₁ ∈ List.range (rcnt (LR 0)),
      ((tailP n w LR TR k).map ((1 * trP n w LR TR 0 k₁) * ·)).countP (fun g =>
        decide (g (bv.get ⟨0, hk⟩) = trP n w LR TR 0 k₀ (bv.get ⟨0, hk⟩)) && q g) =
      if k₁ = k₀ then ((tailP n w LR TR k).map (trP n w LR TR 0 k₁ * ·)).countP q else 0 := by
    intro k₁ hk₁
    have hk₁' := List.mem_range.1 hk₁
    rw [List.countP_map, List.countP_map]
    have hfix : ∀ p ∈ tailP n w LR TR k, (1 * trP n w LR TR 0 k₁ * p) (bv.get ⟨0, hk⟩) =
        trP n w LR TR 0 k₁ (bv.get ⟨0, hk⟩) := by
      intro p hp
      rw [one_mul, Equiv.Perm.mul_apply, level_one_fix hQ hn hbs hk (tailP_mem hQ hn hbs hk p hp)]
    split_ifs with he
    · subst he
      apply List.countP_congr
      intro p hp
      rw [Function.comp_apply, Function.comp_apply, hfix p hp, one_mul]
      simp
    · rw [List.countP_eq_zero]
      intro p hp
      simp only [Function.comp_apply, hfix p hp, Bool.and_eq_true, decide_eq_true_eq, not_and]
      intro h
      exact absurd (trP_zero_inj hQ hn hbs hk hk₁' hk₀ h) he
  have e2 : products ((List.range (k - 1)).map fun t => trL n w LR TR (1 + t)) =
      tailP n w LR TR k := rfl
  rw [e2, List.map_congr_left hterm]
  exact sum_range_ite (fun k₁ => ((tailP n w LR TR k).map (trP n w LR TR 0 k₁ * ·)).countP q) _ hk₀

theorem cntOrdK_one_eq {G₀ e : Nat}
    (hg₀ : imageList (1 : Equiv.Perm (Fin n)) = (unpack n w G₀).toList) (he : 0 < e) (hk : 0 < k) {k₀ : Nat} (hk₀ : k₀ < rcnt (LR 0)) :
    cntOrdK n w (mask w) (n * w) (pidn n w) LR TR k G₀ e k₀ =
      ((tailP n w LR TR k).map (trP n w LR TR 0 k₀ * ·)).countP
        (fun x => decide (orderOf x = e)) := by
  have hn32 := chainK_h32 hQ
  have hw := PF.w_pos hQ.2.1
  have hsz := chainK_szOK hQ
  obtain ⟨h1, -⟩ := tr_facts hQ hk hk₀
  have e1 : cntOrdK n w (mask w) (n * w) (pidn n w) LR TR k G₀ e k₀ =
      enumFrom n w (mask w) (n * w) LR TR (fun g => ordIs n w (mask w) (pidn n w) g (e - 1))
        (k - 1) 1 (pcomp n w (mask w) G₀ (TR (roff n (n * w) (LR 0) + k₀))) 0 := by
    unfold cntOrdK
    rw [Orb.strictN_eq]
    rfl
  rw [e1, enumFrom_spec hQ (q := fun x => decide (orderOf x = e))
    (fun P x hP sP => ordIs_eq hsz hP sP he) (k - 1) 1 (by omega) _ _ 0
    (prep_pcomp hn32 (prep_of_imageList hg₀) h1) (PF.pcomp_shr _ _ hn32 hw), Nat.zero_add,
    one_mul]
  rfl

theorem countP_point_conj (hk : 0 < k) {u : Equiv.Perm (Fin n)}
    (hu : u ∈ (certificate hn gens words bv hbs).originalSubgroup)
    (hub : u (bv.get ⟨0, hk⟩) = bv.get ⟨0, hk⟩) (p : Fin n) (e : Nat) :
    (enumeration (certificate hn gens words bv hbs)).countP (fun g =>
        decide (g (bv.get ⟨0, hk⟩) = u p) && decide (orderOf g = e)) =
      (enumeration (certificate hn gens words bv hbs)).countP (fun g =>
        decide (g (bv.get ⟨0, hk⟩) = p) && decide (orderOf g = e)) := by
  set Q := certificate hn gens words bv hbs
  have hV : ValidSchreier Q := (chainK_check hn hbs hQ).1
  rw [countP_conj (enumeration_nodup Q hV) (mem_enumeration_iff Q hV) hu]
  apply List.countP_congr
  intro g _
  have hub' : u⁻¹ (bv.get ⟨0, hk⟩) = bv.get ⟨0, hk⟩ := by
    rw [Equiv.Perm.inv_eq_iff_eq, hub]
  have ho : orderOf (u * g * u⁻¹) = orderOf g := by
    have := orderOf_injective (MulAut.conj u).toMonoidHom (MulAut.conj u).injective g
    simpa [MulAut.conj_apply] using this
  simp only [Equiv.Perm.mul_apply, hub', ho, EmbeddingLike.apply_eq_iff_eq, Bool.and_eq_true,
    decide_eq_true_eq]

theorem chainK_cosetCount_slices {G₀ e : Nat}
    (hg₀ : imageList (1 : Equiv.Perm (Fin n)) = (unpack n w G₀).toList) (he : 0 < e)
    (hk : 2 ≤ k) {s₀ s₁ : Nat}
    (h₀ : cntOrdK n w (mask w) (n * w) (pidn n w) LR TR k G₀ e 0 = s₀)
    (h₁ : cntOrdK n w (mask w) (n * w) (pidn n w) LR TR k G₀ e 1 = s₁)
    (hc : 1 < rcnt (LR 0))
    (htr : ∀ k₀, 1 ≤ k₀ → k₀ < rcnt (LR 0) → ∃ j < rcnt (LR 1),
      pg w (mask w) (TR (roff n (n * w) (LR 1) + j)) (bv.get ⟨1, hk⟩) =
        pg w (mask w) (TR (roff n (n * w) (LR 0) + k₀)) (bv.get ⟨0, by omega⟩)) :
    (cosetOrderTables (certificate hn gens words bv hbs) 1 e).length =
      s₀ + (rcnt (LR 0) - 1) * s₁ := by
  have hk0 : 0 < k := by omega
  set Q := certificate hn gens words bv hbs
  set b₀ := bv.get ⟨0, hk0⟩
  set b₁ := bv.get ⟨1, hk⟩
  let F : Fin n → Nat := fun p =>
    (enumeration Q).countP (fun g => decide (g b₀ = p) && decide (orderOf g = e))
  have hslice : ∀ k₀ < rcnt (LR 0),
      cntOrdK n w (mask w) (n * w) (pidn n w) LR TR k G₀ e k₀ = F (trP n w LR TR 0 k₀ b₀) :=
    fun k₀ hk₀ => (cntOrdK_one_eq hQ hn hbs hg₀ he hk0 hk₀).trans
      (slice_eq hQ hn hbs hk0 _ hk₀)
  have hpt : ∀ k₀, 1 ≤ k₀ → k₀ < rcnt (LR 0) → F (trP n w LR TR 0 k₀ b₀) = F b₁ := by
    intro k₀ h1 h2
    obtain ⟨j, hj, hpg⟩ := htr k₀ h1 h2
    have hu1 := trP_mem_level hQ hn hbs (by omega : 1 < k) hj
    have hpoint : trP n w LR TR 1 j b₁ = trP n w LR TR 0 k₀ b₀ := by
      apply Fin.ext
      rw [← (tr_facts hQ (by omega : 1 < k) hj).1 b₁, ← (tr_facts hQ hk0 h2).1 b₀]
      exact hpg
    rw [← hpoint]
    exact countP_point_conj hQ hn hbs hk0 (level_le_original hQ hn hbs 1 hu1)
      (level_one_fix hQ hn hbs hk0 hu1) b₁ e
  have hs : ∀ k₀ < rcnt (LR 0),
      cntOrdK n w (mask w) (n * w) (pidn n w) LR TR k G₀ e k₀ =
        (s₀ :: List.replicate (rcnt (LR 0) - 1) s₁).getD k₀ 0 := by
    intro k₀ hk₀
    rcases Nat.eq_zero_or_pos k₀ with rfl | hpos
    · exact h₀
    · obtain ⟨m, rfl⟩ : ∃ m, k₀ = m + 1 := ⟨k₀ - 1, by omega⟩
      have hm : m < (List.replicate (rcnt (LR 0) - 1) s₁).length := by
        rw [List.length_replicate]
        omega
      rw [List.getD_cons_succ, List.getD_eq_getElem _ _ hm, List.getElem_replicate,
        hslice _ hk₀, hpt _ hpos hk₀, ← hpt 1 le_rfl hc, ← hslice 1 hc, h₁]
  rw [chainK_cosetCount' hQ hn hbs hg₀ he hk0 (by simp; omega) hs, List.sum_cons,
    List.sum_replicate, smul_eq_mul]

theorem chainK_cosetCount_trOrb {G₀ e : Nat}
    (hg₀ : imageList (1 : Equiv.Perm (Fin n)) = (unpack n w G₀).toList) (he : 0 < e)
    (hk : 2 ≤ k) {s₀ s₁ : Nat}
    (h₀ : cntOrdK n w (mask w) (n * w) (pidn n w) LR TR k G₀ e 0 = s₀)
    (h₁ : cntOrdK n w (mask w) (n * w) (pidn n w) LR TR k G₀ e 1 = s₁)
    (hc : 1 < rcnt (LR 0))
    (htr : trOrbK n w LR TR (bv.get ⟨0, by omega⟩) (bv.get ⟨1, hk⟩) = true) :
    (cosetOrderTables (certificate hn gens words bv hbs) 1 e).length =
      s₀ + (rcnt (LR 0) - 1) * s₁ := by
  refine chainK_cosetCount_slices hQ hn hbs hg₀ he hk h₀ h₁ hc fun k₀ h1 h2 => ?_
  obtain ⟨i, rfl⟩ : ∃ i, k₀ = i + 1 := ⟨k₀ - 1, by omega⟩
  have hi : i < Nat.sub (rcnt (LR 0)) 1 := by
    change i < rcnt (LR 0) - 1
    omega
  obtain ⟨j, hj, hb⟩ := anyLtK_spec (allN_spec htr i hi)
  exact ⟨j, hj, Nat.eq_of_beq_eq_true hb⟩

end Chain

end CFSG.KS.SporSch.MOC
