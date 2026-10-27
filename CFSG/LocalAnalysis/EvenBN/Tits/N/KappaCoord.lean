module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.KappaDDefs
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P09K

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.KappaD

open Subgroup CFSG.Sporadic.Schreier.Tits

section Basis

variable {G : Type} [Group G] {d : Data G}

@[expose] noncomputable def pb (d : Data G) : Fin 6 → G :=
  ![d.z, d.pv 11, d.pv 10, d.pv 9, d.pv 7, d.t]

@[expose] noncomputable def mono (d : Data G) (a : Fin 6 → ZMod 2) : G :=
  (List.ofFn fun j => pb d j ^ (a j).val).prod

theorem mono_eq (a : Fin 6 → ZMod 2) :
    mono d a = d.z ^ (a 0).val * d.pv 11 ^ (a 1).val * d.pv 10 ^ (a 2).val *
      d.pv 9 ^ (a 3).val * d.pv 7 ^ (a 4).val * d.t ^ (a 5).val := by
  simp [mono, pb, List.ofFn_succ, mul_assoc]

theorem mono_zero : mono d 0 = 1 := by simp [mono]

theorem mono_single (j : Fin 6) : mono d (Pi.single j 1) = pb d j := by
  fin_cases j <;> simp [mono_eq, pb, Pi.single_apply]

theorem mono_mem {S : Subgroup G} {a : Fin 6 → ZMod 2} (h : ∀ j, a j ≠ 0 → pb d j ∈ S) :
    mono d a ∈ S := by
  refine S.list_prod_mem fun x hx => ?_
  obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
  by_cases ha : a j = 0
  · simp [ha]
  · exact pow_mem (h j ha) _

end Basis

section Coord

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {d : Data G}


theorem pv_mem_F {i : ℕ} (hi : i ∈ ({7, 9, 10, 11, 12} : Set ℕ)) : d.pv i ∈ d.F :=
  Data.mem_liftSub.2 ⟨_, Model.parrottV_mem_parrottF hi,
    Model.parrottF_le_titsD (Model.parrottV_mem_parrottF hi), rfl⟩

theorem pb_mem_B (hd : d.Hyp) (j : Fin 6) : pb d j ∈ d.B := by
  fin_cases j
  · exact Data.s56_F_le_B d hd.s56_z_mem_F
  · exact Data.s56_F_le_B d (pv_mem_F (i := 11) (by simp))
  · exact Data.s56_F_le_B d (pv_mem_F (i := 10) (by simp))
  · exact Data.s56_F_le_B d (pv_mem_F (i := 9) (by simp))
  · exact Data.s56_F_le_B d (pv_mem_F (i := 7) (by simp))
  · exact Data.s56_t_mem_B d

theorem B_comm (hd : d.Hyp) {a b : G} (ha : a ∈ d.B) (hb : b ∈ d.B) : a * b = b * a :=
  haveI := hd.B_facts.2.2.1.1
  setLike_mul_comm ha hb

theorem B_sq (hd : d.Hyp) {a : G} (ha : a ∈ d.B) : a * a = 1 := by
  rw [← pow_two]
  exact hd.B_facts.2.2.1.2 a ha

theorem mono_mem_B (hd : d.Hyp) (a : Fin 6 → ZMod 2) : mono d a ∈ d.B :=
  mono_mem fun j _ => pb_mem_B hd j

theorem mono_add (hd : d.Hyp) (a a' : Fin 6 → ZMod 2) :
    mono d (a + a') = mono d a * mono d a' :=
  ofFn_prod_pow_add (pb d) (fun i j => B_comm hd (pb_mem_B hd i) (pb_mem_B hd j))
    (fun i => B_sq hd (pb_mem_B hd i)) a a'

theorem mono_surj (hd : d.Hyp) {g : G} (hg : g ∈ d.B) : ∃ a, mono d a = g := by
  let S : Subgroup G :=
    { carrier := Set.range (mono d)
      mul_mem' := by
        rintro _ _ ⟨a, rfl⟩ ⟨a', rfl⟩
        exact ⟨a + a', mono_add hd a a'⟩
      one_mem' := ⟨0, mono_zero⟩
      inv_mem' := by
        rintro _ ⟨a, rfl⟩
        have h : mono d a * mono d a = 1 := by
          rw [← mono_add hd, show a + a = 0 by ext j; exact CharTwo.add_self_eq_zero (a j),
            mono_zero]
        exact ⟨a, (inv_eq_of_mul_eq_one_right h).symm⟩ }
  have hF : d.F ≤ S := by
    intro f hf
    obtain ⟨x, hx, hxD, rfl⟩ := Data.mem_liftSub.1 hf
    have hx' : x ∈ closure (Model.parrottV '' {7, 9, 10, 11, 12}) := hx
    refine (closure_induction (p := fun x _ => x ∈ titsD ∧ d.lift x ∈ S) ?_ ?_ ?_ ?_ hx').2
    · rintro _ ⟨i, hi, rfl⟩
      refine ⟨Model.parrottF_le_titsD (Model.parrottV_mem_parrottF hi), ?_⟩
      rcases hi with rfl | rfl | rfl | rfl | rfl
      · exact ⟨Pi.single 4 1, mono_single 4⟩
      · exact ⟨Pi.single 3 1, mono_single 3⟩
      · exact ⟨Pi.single 2 1, mono_single 2⟩
      · exact ⟨Pi.single 1 1, mono_single 1⟩
      · exact ⟨Pi.single 0 1, (mono_single 0).trans (Data.s56_pv12 d).symm⟩
    · exact ⟨one_mem _, by rw [d.lift_one]; exact S.one_mem⟩
    · rintro x y _ _ ⟨hxD, hxS⟩ ⟨hyD, hyS⟩
      exact ⟨mul_mem hxD hyD, by rw [d.lift_mul hxD hyD]; exact S.mul_mem hxS hyS⟩
    · rintro x _ ⟨hxD, hxS⟩
      exact ⟨inv_mem hxD, by rw [d.lift_inv hxD]; exact S.inv_mem hxS⟩
  exact (sup_le hF (zpowers_le.2 ⟨Pi.single 5 1, mono_single 5⟩) : d.B ≤ S) hg

theorem B_coord_unique (hd : d.Hyp) {a a' : Fin 6 → ZMod 2} (h : mono d a = mono d a') :
    a = a' := by
  have hsurj : Function.Surjective fun a : Fin 6 → ZMod 2 =>
      (⟨mono d a, mono_mem_B hd a⟩ : d.B) := by
    rintro ⟨g, hg⟩
    obtain ⟨a, rfl⟩ := mono_surj hd hg
    exact ⟨a, rfl⟩
  have hcard : Nat.card (Fin 6 → ZMod 2) ≤ Nat.card d.B := by
    rw [hd.B_facts.2.2.2.1]
    simp [Nat.card_fun]
  exact (hsurj.bijective_of_nat_card_le hcard).1 (Subtype.ext h)

theorem exists_coord (hd : d.Hyp) {S : Subgroup G} {k : ℕ} (hk : k ≤ 6) (hS : Nat.card S = 2 ^ k)
    (hmem : ∀ j : Fin 6, j.val < k → pb d j ∈ S) {s : G} (hs : s ∈ S) :
    ∃ a : Fin 6 → ZMod 2, (∀ j : Fin 6, k ≤ j.val → a j = 0) ∧ s = mono d a := by
  let ext : (Fin k → ZMod 2) → (Fin 6 → ZMod 2) := fun c j =>
    if h : j.val < k then c ⟨j, h⟩ else 0
  have hext : ∀ c (j : Fin 6), k ≤ j.val → ext c j = 0 := fun c j hj => by
    simp [ext, not_lt.2 hj]
  have hmemS : ∀ c, mono d (ext c) ∈ S := fun c =>
    mono_mem fun j hj => hmem j (by by_contra h; exact hj (hext c j (not_lt.1 h)))
  let f : (Fin k → ZMod 2) → S := fun c => ⟨mono d (ext c), hmemS c⟩
  have hinj : Function.Injective f := by
    intro c c' h
    have h' := congrFun (B_coord_unique hd (congrArg Subtype.val h))
    funext i
    simpa [ext] using h' ⟨i, by omega⟩
  obtain ⟨c, hc⟩ := (hinj.bijective_of_nat_card_le (by simp [hS])).2 ⟨s, hs⟩
  exact ⟨ext c, fun j hj => hext c j hj, (congrArg Subtype.val hc).symm⟩

theorem mem_U10_of_coord (e₁ e₂ e₃ : ZMod 2) :
    d.z ^ e₁.val * d.pv 11 ^ e₂.val * d.pv 10 ^ e₃.val ∈ d.s56U10 :=
  mul_mem (mul_mem (pow_mem (Data.s56_U11_le_U10 d (Data.s56_z_mem_U11 d)) _)
    (pow_mem (Data.s56_U11_le_U10 d (Data.s56_pv11_mem_U11 d)) _))
    (pow_mem (Data.s56_pv10_mem_U10 d) _)

theorem coord_EF (hd : d.Hyp) {e : G} (he : e ∈ d.E ⊓ d.F) :
    ∃ e₁ e₂ e₃ e₄ : ZMod 2,
      e = d.z ^ e₁.val * d.pv 11 ^ e₂.val * d.pv 10 ^ e₃.val * d.pv 9 ^ e₄.val ∧
        (e₄ = 0 → e ∈ d.s56U10) := by
  have hmem : ∀ j : Fin 6, j.val < 4 → pb d j ∈ d.E ⊓ d.F := by
    intro j hj
    fin_cases j
    · exact mem_inf.2 ⟨hd.s56_z_mem_E, hd.s56_z_mem_F⟩
    · exact mem_inf.2 ⟨Data.s56_pv11_mem_E d, pv_mem_F (i := 11) (by simp)⟩
    · exact mem_inf.2 ⟨hd.s56_pv10_mem_E, pv_mem_F (i := 10) (by simp)⟩
    · exact mem_inf.2 ⟨node09K_pv9_mem_E d, node09K_pv9_mem_F d⟩
    · exact absurd hj (by decide)
    · exact absurd hj (by decide)
  obtain ⟨a, ha, rfl⟩ := exists_coord hd (k := 4) (by norm_num)
    (by rw [hd.s56_card_E_inf_F]; norm_num) hmem he
  have h4 := ha 4 (by norm_num)
  have h5 := ha 5 (by norm_num)
  refine ⟨a 0, a 1, a 2, a 3, ?_, fun h0 => ?_⟩
  · rw [mono_eq, h4, h5]
    simp
  · rw [mono_eq, h4, h5, h0]
    simpa using mem_U10_of_coord (d := d) (a 0) (a 1) (a 2)

theorem coord_U10 (hd : d.Hyp) {δ : G} (hδ : δ ∈ d.s56U10) :
    ∃ d₁ d₂ d₃ : ZMod 2, δ = d.z ^ d₁.val * d.pv 11 ^ d₂.val * d.pv 10 ^ d₃.val ∧
      (d₃ = 0 → δ ∈ d.s56U11) := by
  have hmem : ∀ j : Fin 6, j.val < 3 → pb d j ∈ d.s56U10 := by
    intro j hj
    fin_cases j
    · exact Data.s56_U11_le_U10 d (Data.s56_z_mem_U11 d)
    · exact Data.s56_U11_le_U10 d (Data.s56_pv11_mem_U11 d)
    · exact Data.s56_pv10_mem_U10 d
    · exact absurd hj (by decide)
    · exact absurd hj (by decide)
    · exact absurd hj (by decide)
  obtain ⟨a, ha, rfl⟩ := exists_coord hd (k := 3) (by norm_num)
    (by rw [Data.s56_card_U10]; norm_num) hmem hδ
  have h3 := ha 3 (by norm_num)
  have h4 := ha 4 (by norm_num)
  have h5 := ha 5 (by norm_num)
  refine ⟨a 0, a 1, a 2, ?_, fun h0 => ?_⟩
  · rw [mono_eq, h3, h4, h5]
    simp
  · rw [mono_eq, h3, h4, h5, h0]
    simpa using mul_mem (pow_mem (Data.s56_z_mem_U11 d) (a 0).val)
      (pow_mem (Data.s56_pv11_mem_U11 d) (a 1).val)

theorem conj_mono (hd : d.Hyp) {n : G} {M : Mat6}
    (h : ∀ i, n * pb d i * n⁻¹ = mono d (M i)) (v : Fin 6 → ZMod 2) :
    n * mono d v * n⁻¹ = mono d (Matrix.vecMul v M) := by
  have key : ∀ w : ZMod 2, w = 0 ∨ w = 1 := by decide
  have hadd : ∀ w w' : Fin 6 → ZMod 2, n * mono d w * n⁻¹ = mono d (Matrix.vecMul w M) →
      n * mono d w' * n⁻¹ = mono d (Matrix.vecMul w' M) →
      n * mono d (w + w') * n⁻¹ = mono d (Matrix.vecMul (w + w') M) := by
    intro w w' hw hw'
    rw [mono_add hd, Matrix.add_vecMul, mono_add hd, ← hw, ← hw']
    group
  have := Finset.sum_induction (s := Finset.univ) (fun i => (Pi.single i (v i) : Fin 6 → ZMod 2))
    (fun w => n * mono d w * n⁻¹ = mono d (Matrix.vecMul w M)) hadd (by simp [mono_zero])
    fun i _ => by
      rcases key (v i) with h0 | h1
      · simp [h0, mono_zero]
      · rw [h1, Matrix.single_one_vecMul, mono_single]
        exact h i
  rwa [Finset.univ_sum_single] at this

end Coord

end CFSG.LocalAnalysis.EvenBN.Tits.N.KappaD
