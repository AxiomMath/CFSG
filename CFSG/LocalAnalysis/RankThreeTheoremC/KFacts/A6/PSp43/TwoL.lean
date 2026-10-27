module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.PSp43.TwoData
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.PSp43.TwoCentral

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.A6.PSp43

open CFSG.Open CFSG.GH74.Exceptional CFSG.ComponentClassification.CatFactsSmall.PSp43 Subgroup

theorem exists_fixed_of_invariant {p : ℕ} [Fact p.Prime] {V : Subgroup (Equiv.Perm (Fin 45))}
    (hV : IsPGroup p V) (s : Fin 45 → Prop) (hs : ∀ v ∈ V, ∀ j, s j → s (v j))
    (hcard : ¬ p ∣ Nat.card {j // s j}) : ∃ j, s j ∧ ∀ v ∈ V, v j = j := by
  letI : MulAction V {j // s j} :=
    { smul := fun v j => ⟨(v : Equiv.Perm (Fin 45)) j.1, hs v v.2 j.1 j.2⟩
      one_smul := fun j => rfl
      mul_smul := fun v w j => rfl }
  obtain ⟨⟨j, hj⟩, hfix⟩ := hV.nonempty_fixed_point_of_prime_not_dvd_card _ hcard
  refine ⟨j, hj, fun v hv => ?_⟩
  have := hfix ⟨v, hv⟩
  exact congrArg Subtype.val this

theorem normalizer_sup_of_le {G : Type*} [Group G] [Finite G] {A B : Subgroup G} {u : G}
    (hA : u ∈ normalizer (A : Set G)) (hB : u ∈ normalizer (B : Set G)) :
    u ∈ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  refine mem_normalizer_of_conj_mem' _ u fun x hx => ?_
  have hle : A ⊔ B ≤ (A ⊔ B).comap (MulAut.conj u).toMonoidHom := by
    refine sup_le (fun a ha => ?_) (fun b hb => ?_)
    · exact mem_sup_left ((mem_normalizer_iff.1 hA a).1 ha)
    · exact mem_sup_right ((mem_normalizer_iff.1 hB b).1 hb)
  exact hle hx

theorem le_E_of_normalized {Y U : Subgroup (Equiv.Perm (Fin 45))} (hYH : Y ≤ H0)
    (hY : IsPGroup 2 Y) (hUH : U ≤ H0) (hU : Nat.card U = 9)
    (hN : U ≤ normalizer (Y : Set (Equiv.Perm (Fin 45)))) : Y ≤ E := by
  set M := Y ⊔ E
  have hMH : M ≤ H0 := sup_le hYH E_le_H0
  have hMp : IsPGroup 2 M :=
    hY.to_sup_of_normal_right' isPGroup_E (hYH.trans H0_le_normalizer_E)
  have hM576 : Nat.card M ∣ 576 := card_H0 ▸ Subgroup.card_dvd_of_le hMH
  obtain ⟨n, hn⟩ := hMp.exists_card_eq
  have hEM : Nat.card E ∣ Nat.card M := Subgroup.card_dvd_of_le le_sup_right
  rw [card_E, hn] at hEM
  rw [hn] at hM576
  have hn6 : n ≤ 6 := by
    by_contra h
    have : 2 ^ 7 ∣ 2 ^ n := pow_dvd_pow 2 (by omega)
    have := this.trans hM576
    norm_num at this
  have hn5 : 5 ≤ n := by
    by_contra h
    have : 2 ^ n ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have := Nat.le_of_dvd (by positivity) hEM
    omega
  rcases (show n = 5 ∨ n = 6 by omega) with rfl | rfl
  · have : M = E := (Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [hn, card_E]; norm_num)).symm
    exact le_sup_left.trans this.le
  · exfalso
    have hUM : U ≤ normalizer (M : Set (Equiv.Perm (Fin 45))) := fun u hu =>
      normalizer_sup_of_le (hN hu) (H0_le_normalizer_E (hUH hu))
    have hMU : M ⊔ U = H0 := by
      apply Subgroup.eq_of_le_of_card_ge (sup_le hMH hUH)
      have h1 : Nat.card M ∣ Nat.card (M ⊔ U : Subgroup _) := Subgroup.card_dvd_of_le le_sup_left
      have h2 : Nat.card U ∣ Nat.card (M ⊔ U : Subgroup _) := Subgroup.card_dvd_of_le le_sup_right
      rw [hn] at h1
      rw [hU] at h2
      have h3 : 576 ∣ Nat.card (M ⊔ U : Subgroup _) :=
        Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h1 h2
      rw [card_H0]
      exact Nat.le_of_dvd Nat.card_pos h3
    have hMn : H0 ≤ normalizer (M : Set (Equiv.Perm (Fin 45))) := by
      rw [← hMU]
      exact sup_le le_normalizer hUM
    have hMcard : Nat.card M = 2 ^ (Nat.card H0).factorization 2 := by
      rw [hn, card_H0, factorization_two_576]
    have heq : ∀ S : Subgroup (Equiv.Perm (Fin 45)), S ≤ H0 →
        Nat.card S = 2 ^ (Nat.card H0).factorization 2 → S = M := by
      intro S hSH hS
      obtain ⟨g, hg, rfl⟩ := exists_conj_eq_of_card hMH hSH hMcard hS
      ext x
      constructor
      · rintro ⟨m, hm, rfl⟩
        exact (mem_normalizer_iff.1 (hMn hg) m).1 hm
      · intro hx
        refine ⟨g⁻¹ * x * g, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
        have := (mem_normalizer_iff.1 (hMn (inv_mem hg)) x).1 hx
        simpa using this
    have hk : wperm [4, 3, 1, 0] ∈ H0 := K_le_H0 (wperm_mem_gen (by simp [Kgens]))
    have h1 := heq S0 S0_le_H0 card_S0_eq
    have hc : Nat.card (S0.map (MulAut.conj (wperm [4, 3, 1, 0])).toMonoidHom) =
        2 ^ (Nat.card H0).factorization 2 := by
      rw [← card_S0_eq]
      exact Subgroup.card_map_of_injective (MulAut.conj _).injective
    have hle : S0.map (MulAut.conj (wperm [4, 3, 1, 0])).toMonoidHom ≤ H0 := by
      rintro _ ⟨s, hs, rfl⟩
      exact mul_mem (mul_mem hk (S0_le_H0 hs)) (inv_mem hk)
    have h2 := heq _ hle hc
    have hS0E : S0 ≤ E := by
      intro s hs
      have hs' : s ∈ S0.map (MulAut.conj (wperm [4, 3, 1, 0])).toMonoidHom := by
        rw [h2, ← h1]; exact hs
      have hx2 := mem_conj_S0 hs'
      obtain ⟨t, ht, hr⟩ := exists_mem_tab S0_enumOK hs
      have hm := List.all_eq_true.1 S0_meet t ht
      obtain ⟨t', ht', hr'⟩ := exists_mem_tab S0_enumOK hx2
      have hr2 : Rep ((wperm [4, 3, 1, 0])⁻¹ * s * wperm [4, 3, 1, 0])
          (tmul (tmul (wtab [4, 3, 1, 0].reverse) t) (wtab [4, 3, 1, 0])) := by
        rw [wperm_inv]
        exact rep_mul (rep_mul (rep_wperm _) hr) (rep_wperm _)
      rw [← rep_eq_tab hr' hr2] at hm
      have hc1 : S0elems.contains t' = true := List.contains_iff_mem.2 ht'
      simp only [hc1, Bool.not_true, Bool.false_or, List.contains_iff_mem] at hm
      exact mem_gen_of_mem_tab E_enumOK hm hr
    have := Subgroup.card_le_of_le hS0E
    rw [card_S0, card_E] at this
    omega

theorem card_le_64 {M : Subgroup (Equiv.Perm (Fin 45))} (hMH : M ≤ H0) (hM : IsPGroup 2 M) :
    Nat.card M ≤ 64 := by
  obtain ⟨n, hn⟩ := hM.exists_card_eq
  have h576 : Nat.card M ∣ 576 := card_H0 ▸ Subgroup.card_dvd_of_le hMH
  rw [hn] at h576 ⊢
  have hn6 : n ≤ 6 := by
    by_contra h
    have : 2 ^ 7 ∣ 2 ^ n := pow_dvd_pow 2 (by omega)
    have := this.trans h576
    norm_num at this
  calc 2 ^ n ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hn6
    _ = 64 := by norm_num

@[expose] def fixOK (gens : List (List (Fin 45))) (fixl : List ℕ) : Bool :=
  (List.range 45).all fun j => (fixl.contains j) == (gens.all fun w => (wtab w).getD j 0 == j)

@[expose] def stabOK (elems : List Tab) (fixl : List ℕ) : Bool :=
  (List.range 45).all fun j => fixl.contains j ||
    Eelems.all fun e => e == tid || elems.any fun u =>
      e.getD ((wtab (transW.getD j []).reverse).getD (u.getD j 0) 0) 0 !=
        (wtab (transW.getD j []).reverse).getD (u.getD j 0) 0

theorem U1_fix : fixOK U1gens U1fix = true := by decide +kernel
theorem U2_fix : fixOK U2gens U2fix = true := by decide +kernel
theorem U1_stab : stabOK U1elems U1fix = true := by decide +kernel
theorem U2_stab : stabOK U2elems U2fix = true := by decide +kernel
theorem U1fix_card : Nat.card {j : Fin 45 // j.1 ∈ U1fix} = 3 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide
theorem U2fix_card : Nat.card {j : Fin 45 // j.1 ∈ U2fix} = 3 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide

theorem cW_apply (j : Fin 45) : wperm (transW.getD j []).reverse j = 0 := by
  have h1 : wperm (transW.getD j []) 0 = j := Fin.ext
    (((rep_wperm _).2 0 (by norm_num)).trans (transW_spec j.1 j.2))
  have h2 : (wperm (transW.getD j []))⁻¹ (wperm (transW.getD j []) 0) = 0 := by
    rw [← Equiv.Perm.mul_apply, inv_mul_cancel, Equiv.Perm.one_apply]
  rw [h1] at h2
  rw [← wperm_inv]
  exact h2

theorem fix_iff {ws : List (List (Fin 45))} {fixl : List ℕ} (h : fixOK ws fixl = true)
    (j : Fin 45) : j.1 ∈ fixl ↔ ∀ w ∈ ws, wperm w j = j := by
  have h1 := List.all_eq_true.1 h j.1 (List.mem_range.2 j.2)
  rw [beq_iff_eq] at h1
  rw [← List.contains_iff_mem, h1, List.all_eq_true]
  refine forall_congr' fun w => imp_congr_right fun _ => ?_
  rw [beq_iff_eq, ← (rep_wperm w).2 j.1 j.2]
  exact ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩

theorem fix_of_mem_gen {ws : List (List (Fin 45))} {fixl : List ℕ} (h : fixOK ws fixl = true)
    {j : Fin 45} (hj : j.1 ∈ fixl) {u : Equiv.Perm (Fin 45)} (hu : u ∈ gen (ws.map wperm)) :
    u j = j := by
  induction hu using Subgroup.closure_induction with
  | mem x hx =>
    simp only [Set.mem_setOf_eq, List.mem_map] at hx
    obtain ⟨w, hw, rfl⟩ := hx
    exact (fix_iff h j).1 hj w hw
  | one => rfl
  | mul x y _ _ hx hy => rw [Equiv.Perm.mul_apply, hy, hx]
  | inv x _ hx => rw [Equiv.Perm.inv_eq_iff_eq, hx]

theorem le_conj_E_of_normalized {ws : List (List (Fin 45))} {elems : List Tab}
    {par : List (ℕ × ℕ)} {act : List (List ℕ)} {fixl : List ℕ}
    (henum : enumOK (ws.map wtab) elems par act = true) (hlen : elems.length = 9)
    (hfix : fixOK ws fixl = true) (hstab : stabOK elems fixl = true)
    (hfixc : Nat.card {j : Fin 45 // j.1 ∈ fixl} = 3)
    {Y : Subgroup (Equiv.Perm (Fin 45))} (hYP : Y ≤ P) (hY : IsPGroup 2 Y)
    (hN : gen (ws.map wperm) ≤ normalizer (Y : Set (Equiv.Perm (Fin 45)))) :
    ∃ i : Fin 45, i.1 ∈ fixl ∧
      Y ≤ E.map (MulAut.conj (wperm (transW.getD i []))).toMonoidHom := by
  set U := gen (ws.map wperm)
  have hUcard : Nat.card U = 9 := (card_gen_words henum).trans hlen
  have hUP : U ≤ P := gen_words_le_P ws
  have hinvU : ∀ u ∈ U, ∀ j : Fin 45, (∀ y ∈ Y, y j = j) → ∀ y ∈ Y, y (u j) = u j := by
    intro u hu j hj y hy
    have h1 : u⁻¹ * y * u ∈ Y := by
      have := (mem_normalizer_iff.1 (hN (inv_mem hu)) y).1 hy
      simpa using this
    have h2 := hj _ h1
    simp only [Equiv.Perm.mul_apply] at h2
    rw [Equiv.Perm.inv_eq_iff_eq] at h2
    exact h2
  have hcase : ∀ i : Fin 45, i.1 ∈ fixl → (∀ y ∈ Y, y i = i) →
      Y ≤ E.map (MulAut.conj (wperm (transW.getD i []))).toMonoidHom := by
    intro i hi hYi
    set c := wperm (transW.getD i []).reverse
    have hcP : c ∈ P := wperm_mem _
    have hci : c i = 0 := cW_apply i
    have hcinv : c⁻¹ 0 = i := by
      rw [← hci, ← Equiv.Perm.mul_apply, inv_mul_cancel, Equiv.Perm.one_apply]
    set Y' := Y.map (MulAut.conj c).toMonoidHom
    set U' := U.map (MulAut.conj c).toMonoidHom
    have hconjH0 : ∀ g ∈ P, g i = i → c * g * c⁻¹ ∈ H0 := by
      intro g hg hgi
      have hP' : c * g * c⁻¹ ∈ P := mul_mem (mul_mem hcP hg) (inv_mem hcP)
      refine ⟨hP', (mem_centralizer_tauPerm_iff hP' 0).2 ?_⟩
      simp only [Equiv.Perm.mul_apply, hcinv, hgi, hci]
    have hY'H : Y' ≤ H0 := by
      rintro _ ⟨y, hy, rfl⟩
      exact hconjH0 y (hYP hy) (hYi y hy)
    have hU'H : U' ≤ H0 := by
      rintro _ ⟨u, hu, rfl⟩
      exact hconjH0 u (hUP hu) (fix_of_mem_gen hfix hi hu)
    have hU'c : Nat.card U' = 9 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj c).injective, hUcard]
    have hY'p : IsPGroup 2 Y' := hY.map _
    have hU'N : U' ≤ normalizer (Y' : Set (Equiv.Perm (Fin 45))) := by
      rintro _ ⟨u, hu, rfl⟩
      refine mem_normalizer_of_conj_mem' _ _ fun x hx => ?_
      obtain ⟨y, hy, rfl⟩ := hx
      have h1 := (mem_normalizer_iff.1 (hN hu) y).1 hy
      refine ⟨u * y * u⁻¹, h1, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    have hY'E := le_E_of_normalized hY'H hY'p hU'H hU'c hU'N
    intro y hy
    have h1 := hY'E ⟨y, hy, rfl⟩
    refine ⟨c * y * c⁻¹, h1, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, c, ← wperm_inv]
    group
  by_cases hex : ∃ i : Fin 45, i.1 ∈ fixl ∧ ∀ y ∈ Y, y i = i
  · obtain ⟨i, hi, hYi⟩ := hex
    exact ⟨i, hi, hcase i hi hYi⟩
  · exfalso
    push Not at hex
    obtain ⟨j, -, hj⟩ := exists_fixed_of_invariant hY (fun _ => True) (fun _ _ _ _ => trivial)
      (by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.filter_true_of_mem
          (fun _ _ => trivial), Finset.card_univ, Fintype.card_fin]
        norm_num)
    have hjfix : j.1 ∉ fixl := fun h => by
      obtain ⟨y, hy, hyj⟩ := hex j h
      exact hyj (hj y hy)
    set c := wperm (transW.getD j []).reverse
    have hcP : c ∈ P := wperm_mem _
    have hcj : c j = 0 := cW_apply j
    have hcinv : c⁻¹ 0 = j := by
      rw [← hcj, ← Equiv.Perm.mul_apply, inv_mul_cancel, Equiv.Perm.one_apply]
    set Y' := Y.map (MulAut.conj c).toMonoidHom
    have hY'H : Y' ≤ H0 := by
      rintro _ ⟨y, hy, rfl⟩
      have hP' : c * y * c⁻¹ ∈ P := mul_mem (mul_mem hcP (hYP hy)) (inv_mem hcP)
      refine ⟨hP', (mem_centralizer_tauPerm_iff hP' 0).2 ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Equiv.Perm.mul_apply, hcinv,
        hj y hy, hcj]
    have hmeet : ∀ e ∈ Y', e ∈ E → e = 1 := by
      rintro _ ⟨y, hy, rfl⟩ he
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at he ⊢
      obtain ⟨t, ht, hr⟩ := exists_mem_tab E_enumOK he
      have h1 := List.all_eq_true.1 hstab j.1 (List.mem_range.2 j.2)
      have hjc : fixl.contains j.1 = false := by
        rw [Bool.eq_false_iff, ne_eq, List.contains_iff_mem]
        exact hjfix
      rw [hjc, Bool.false_or] at h1
      have h2 := List.all_eq_true.1 h1 t ht
      rw [Bool.or_eq_true, beq_iff_eq] at h2
      rcases h2 with h2 | h2
      · exact rep_unique (h2 ▸ hr) rep_one
      · exfalso
        obtain ⟨u, hu, hne⟩ := List.any_eq_true.1 h2
        obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hu
        obtain ⟨g, hgU, hgr⟩ := exists_mem_rep_of_enumOK (length_words ws) (rep_words ws)
          henum k hk
        rw [List.getD_eq_getElem _ _ hk] at hgr
        have hcr := rep_wperm (transW.getD j []).reverse
        have e1 : elems[k].getD j.1 0 = (g j : ℕ) := (hgr.2 j.1 j.2).symm
        have hgj := (g j).2
        rw [e1] at hne
        have e2 : (wtab (transW.getD j []).reverse).getD (g j : ℕ) 0 = (c (g j) : ℕ) :=
          (hcr.2 _ hgj).symm
        rw [e2] at hne
        have e3 : t.getD (c (g j) : ℕ) 0 = ((c * y * c⁻¹) (c (g j)) : ℕ) :=
          (hr.2 _ (c (g j)).2).symm
        rw [e3] at hne
        have hfix' : (c * y * c⁻¹) (c (g j)) = c (g j) := by
          have h4 : c⁻¹ (c (g j)) = g j := by
            rw [← Equiv.Perm.mul_apply, inv_mul_cancel, Equiv.Perm.one_apply]
          simp only [Equiv.Perm.mul_apply, h4, hinvU g hgU j hj y hy]
        rw [hfix', bne_self_eq_false] at hne
        exact Bool.noConfusion hne
    have hY'p : IsPGroup 2 Y' := hY.map _
    have hsupH : Y' ⊔ E ≤ H0 := sup_le hY'H E_le_H0
    have hsupp : IsPGroup 2 (Y' ⊔ E : Subgroup _) :=
      hY'p.to_sup_of_normal_right' isPGroup_E (hY'H.trans H0_le_normalizer_E)
    have h64 := card_le_64 hsupH hsupp
    let F : Y' × E → ↥(Y' ⊔ E) := fun q => ⟨q.1 * q.2, mul_mem (mem_sup_left q.1.2)
      (mem_sup_right q.2.2)⟩
    have hF : Function.Injective F := by
      rintro ⟨a, e⟩ ⟨a', e'⟩ hq
      have h1 : (a : Equiv.Perm (Fin 45)) * e = a' * e' := congrArg Subtype.val hq
      have h2 : (a' : Equiv.Perm (Fin 45))⁻¹ * a = e' * (e : Equiv.Perm (Fin 45))⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h1, mul_inv_cancel_right]
      have h3 : (a' : Equiv.Perm (Fin 45))⁻¹ * a = 1 :=
        hmeet _ (mul_mem (inv_mem a'.2) a.2) (h2 ▸ mul_mem e'.2 (inv_mem e.2))
      have ha : a = a' := Subtype.ext (inv_mul_eq_one.1 h3).symm
      subst ha
      have he : e = e' := Subtype.ext (mul_left_cancel h1)
      rw [he]
    have hcardF := Nat.card_le_card_of_injective F hF
    rw [Nat.card_prod, card_E] at hcardF
    have hY'2 : Nat.card Y' ≤ 2 := by omega
    have hY2 : Nat.card Y ≤ 2 := by
      rwa [Subgroup.card_map_of_injective (MulAut.conj c).injective] at hY'2
    have hcomm : ∀ y ∈ Y, ∀ u ∈ U, u * y = y * u := by
      intro y hy u hu
      by_cases hy1 : y = 1
      · rw [hy1, one_mul, mul_one]
      have h1 : u * y * u⁻¹ ∈ Y := (mem_normalizer_iff.1 (hN hu) y).1 hy
      have h2 : u * y * u⁻¹ ≠ 1 := by
        intro h
        apply hy1
        have : y = u⁻¹ * (u * y * u⁻¹) * u := by group
        rw [this, h]; group
      by_contra hne
      have h3 : u * y * u⁻¹ ≠ y := by
        intro h
        apply hne
        calc u * y = u * y * u⁻¹ * u := by group
          _ = y * u := by rw [h]
      have hsub : ({1, y, u * y * u⁻¹} : Set (Equiv.Perm (Fin 45))) ⊆ Y := by
        intro x hx
        rcases hx with rfl | rfl | rfl
        · exact one_mem _
        · exact hy
        · exact h1
      have h4 := Set.ncard_le_ncard hsub (Set.toFinite _)
      have e : Nat.card Y = (Y : Set (Equiv.Perm (Fin 45))).ncard := Nat.card_coe_set_eq _
      rw [Set.ncard_eq_three.2 ⟨1, y, u * y * u⁻¹, Ne.symm hy1, Ne.symm h2, h3.symm, rfl⟩] at h4
      omega
    obtain ⟨i, hi, hYi⟩ := exists_fixed_of_invariant hY (fun j : Fin 45 => j.1 ∈ fixl)
      (by
        intro y hy j hj
        rw [fix_iff hfix] at hj ⊢
        intro w hw
        have h1 := hcomm y hy (wperm w) (wperm_mem_gen hw)
        have h2 := congrArg (fun σ : Equiv.Perm (Fin 45) => σ j) h1
        simp only [Equiv.Perm.mul_apply, hj w hw] at h2
        exact h2)
      (by rw [hfixc]; norm_num)
    obtain ⟨y, hy, hyi⟩ := hex i hi
    exact hyi (hYi y hy)

theorem conj_E_eq (i : Fin 45) :
    E.map (MulAut.conj (wperm (transW.getD i []))).toMonoidHom =
      pCoreOf 2 (P ⊓ centralizer ({tauPerm i} : Set (Equiv.Perm (Fin 45)))) := by
  have hw : wperm (transW.getD i []) 0 = i := Fin.ext
    (((rep_wperm _).2 0 (by norm_num)).trans (transW_spec i.1 i.2))
  have h := conj_tauPerm (wperm_mem (transW.getD i [])) 0
  rw [hw] at h
  rw [← h, P_inf_centralizer_conj (wperm_mem _),
    pCoreOf_map_of_injective' (MulAut.conj _).injective, pCoreOf_H0]

end CFSG.LocalAnalysis.RankThreeTheoremC.A6.PSp43
