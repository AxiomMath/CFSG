module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69K.PermCentInv
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69K.PermHalves
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69K.AltGenHalves
public import Mathlib.GroupTheory.SpecificGroups.Alternating.MaximalSubgroups

public section

open scoped Pointwise

namespace CFSG.Quasithin.B69K

open Equiv Equiv.Perm

theorem ncard_pair_le_two {m : ℕ} (a b : Fin m) : ({a, b} : Set (Fin m)).ncard ≤ 2 := by
  have h := Set.ncard_insert_le a ({b} : Set (Fin m))
  rw [Set.ncard_singleton] at h
  exact h

theorem ncard_triple_le_three {m : ℕ} (x y z : Fin m) : ({x, y, z} : Set (Fin m)).ncard ≤ 3 := by
  have h1 := Set.ncard_insert_le x ({y, z} : Set (Fin m))
  have h2 := ncard_pair_le_two y z
  omega

theorem exists_ne_two {m : ℕ} (hm : 3 ≤ m) (a b : Fin m) : ∃ c : Fin m, c ≠ a ∧ c ≠ b := by
  have hu : (Set.univ : Set (Fin m)).ncard = m := by
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hlt : ({a, b} : Set (Fin m)).ncard < (Set.univ : Set (Fin m)).ncard := by
    have := ncard_pair_le_two a b
    omega
  obtain ⟨c, -, hc⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hlt
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hc
  exact ⟨c, hc.1, hc.2⟩

theorem sig_mem_alt {m : ℕ} {ι : Perm (Fin m)} {a b : Fin m} (hab : a ≠ b) (hιab : ι a ≠ ι b) :
    swap a b * swap (ι a) (ι b) ∈ alternatingGroup (Fin m) := by
  rw [Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap hab, Perm.sign_swap hιab]
  all_goals first | rfl | decide | norm_num | simp

theorem sig_nodup {m : ℕ} {ι : Perm (Fin m)} (hιι : ∀ x, ι (ι x) = x) (hfix : ∀ x, ι x ≠ x)
    {a b : Fin m} (hab : a ≠ b) (hbι : b ≠ ι a) : [a, b, ι a, ι b].Nodup := by
  have h1 : a ≠ ι a := fun h => hfix a h.symm
  have h2 : a ≠ ι b := fun h => hbι (by rw [h, hιι])
  have h3 : b ≠ ι b := fun h => hfix b h.symm
  have h4 : ι a ≠ ι b := fun h => hab (by simpa [hιι] using congrArg ι h)
  simp [List.nodup_cons, hab, h1, h2, h3, hbι, h4, Ne.symm hab, Ne.symm h1, Ne.symm h2,
    Ne.symm h3, Ne.symm hbι, Ne.symm h4]

theorem sig_comm {m : ℕ} {ι : Perm (Fin m)} (hιι : ∀ x, ι (ι x) = x) {a b : Fin m}
    (hnd : [a, b, ι a, ι b].Nodup) :
    (swap a b * swap (ι a) (ι b)) * ι = ι * (swap a b * swap (ι a) (ι b)) := by
  have hc : swap a b * swap (ι a) (ι b) = swap (ι a) (ι b) * swap a b :=
    (Equiv.Perm.disjoint_swap_swap hnd).commute
  have h1 : ι * swap a b = swap (ι a) (ι b) * ι := Equiv.mul_swap_eq_swap_mul ι a b
  have h2 : ι * swap (ι a) (ι b) = swap a b * ι := by
    have h := Equiv.mul_swap_eq_swap_mul ι (ι a) (ι b)
    rw [hιι, hιι] at h
    exact h
  have hmain : ι * (swap a b * swap (ι a) (ι b)) = (swap a b * swap (ι a) (ι b)) * ι := by
    calc ι * (swap a b * swap (ι a) (ι b))
        = (ι * swap a b) * swap (ι a) (ι b) := by rw [mul_assoc]
      _ = (swap (ι a) (ι b) * ι) * swap (ι a) (ι b) := by rw [h1]
      _ = swap (ι a) (ι b) * (ι * swap (ι a) (ι b)) := by rw [mul_assoc]
      _ = swap (ι a) (ι b) * (swap a b * ι) := by rw [h2]
      _ = (swap (ι a) (ι b) * swap a b) * ι := by rw [mul_assoc]
      _ = (swap a b * swap (ι a) (ι b)) * ι := by rw [hc]
  exact hmain.symm

theorem sig_apply_left {m : ℕ} {ι : Perm (Fin m)} (hιι : ∀ x, ι (ι x) = x) (hfix : ∀ x, ι x ≠ x)
    {a b : Fin m} (hbι : b ≠ ι a) : (swap a b * swap (ι a) (ι b)) a = b := by
  have h1 : a ≠ ι a := fun h => hfix a h.symm
  have h2 : a ≠ ι b := fun h => hbι (by rw [h, hιι])
  rw [Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h1 h2, Equiv.swap_apply_left]

theorem sig_apply_fix {m : ℕ} {ι : Perm (Fin m)} {a b u : Fin m} (hua : u ≠ a) (hub : u ≠ b)
    (huia : u ≠ ι a) (huib : u ≠ ι b) : (swap a b * swap (ι a) (ι b)) u = u := by
  rw [Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne huia huib,
    Equiv.swap_apply_of_ne_of_ne hua hub]

theorem cycle3_mem_alt {m : ℕ} {a b c : Fin m} (hac : a ≠ c) (hab : a ≠ b) :
    swap a c * swap a b ∈ alternatingGroup (Fin m) := by
  rw [Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap hac, Perm.sign_swap hab]
  all_goals first | rfl | decide | norm_num | simp

theorem cycle3_apply_right {m : ℕ} {a b c : Fin m} : (swap a c * swap a b) b = c := by
  rw [Perm.mul_apply, Equiv.swap_apply_right, Equiv.swap_apply_left]

theorem cycle3_apply_fix {m : ℕ} {a b c u : Fin m} (hua : u ≠ a) (hub : u ≠ b) (huc : u ≠ c) :
    (swap a c * swap a b) u = u := by
  rw [Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hua hub,
    Equiv.swap_apply_of_ne_of_ne hua huc]

theorem mem_stab_set_iff {m : ℕ} (O : Set (Fin m)) (g : alternatingGroup (Fin m)) :
    g ∈ MulAction.stabilizer (alternatingGroup (Fin m)) O ↔ (g : Perm (Fin m)) '' O = O :=
  MulAction.mem_stabilizer_iff.trans Iff.rfl

theorem image_mul_eq {n : ℕ} (f g : Perm (Fin n)) (s : Set (Fin n)) :
    (f * g) '' s = f '' (g '' s) :=
  (Set.image_image f g s).symm

theorem image_conj_eq {n : ℕ} (τ g : Perm (Fin n)) (O : Set (Fin n)) :
    (τ * g * τ⁻¹) '' O = τ '' (g '' ((⇑(τ⁻¹)) '' O)) := by
  rw [image_mul_eq, image_mul_eq]

theorem halves_image_mem {n : ℕ} {π : Perm (Fin n)} {B Y : Set (Fin n)}
    (hπ : π '' B = B ∨ π '' B = Bᶜ) (hY : Y = B ∨ Y = Bᶜ) :
    π '' Y = B ∨ π '' Y = Bᶜ := by
  rcases hY with h | h
  · rw [h]
    exact hπ
  · rw [h, Set.image_compl_eq π.bijective]
    rcases hπ with h' | h'
    · rw [h']
      exact Or.inr rfl
    · rw [h', compl_compl]
      exact Or.inl rfl

theorem halves_inv_mem {n : ℕ} {π : Perm (Fin n)} {B : Set (Fin n)}
    (hπ : π '' B = B ∨ π '' B = Bᶜ) : (⇑(π⁻¹)) '' B = B ∨ (⇑(π⁻¹)) '' B = Bᶜ := by
  have key : ∀ X : Set (Fin n), π '' B = X → (⇑(π⁻¹)) '' X = B := by
    intro X hX
    rw [← hX, Set.image_image]
    simp [Equiv.Perm.inv_def, Set.image_id']
  rcases hπ with h | h
  · exact Or.inl (key B h)
  · refine Or.inr (compl_inj_iff.1 ?_)
    have h2 := key Bᶜ h
    rw [Set.image_compl_eq (π⁻¹).bijective] at h2
    rw [compl_compl]
    exact h2

theorem image_eq_of_fix {n : ℕ} {π : Perm (Fin n)} {B : Set (Fin n)} (h : ∀ x ∈ B, π x = x) :
    π '' B = B := by
  have h1 : π '' B = id '' B := Set.image_congr h
  rw [h1, Set.image_id]

theorem image_eq_of_fix_compl {n : ℕ} {π : Perm (Fin n)} {B : Set (Fin n)}
    (h : ∀ x ∈ Bᶜ, π x = x) : π '' B = B := by
  have h1 : π '' Bᶜ = Bᶜ := image_eq_of_fix h
  rw [Set.image_compl_eq π.bijective] at h1
  exact compl_inj_iff.1 h1

theorem exists_halves_subgroup {m : ℕ} (B : Set (Fin m)) :
    ∃ Q : Subgroup (alternatingGroup (Fin m)), ∀ g : alternatingGroup (Fin m),
      g ∈ Q ↔ ((g : Perm (Fin m)) '' B = B ∨ (g : Perm (Fin m)) '' B = Bᶜ) := by
  obtain ⟨P, hP⟩ : ∃ P : alternatingGroup (Fin m) → Prop, ∀ g, P g ↔
      ((g : Perm (Fin m)) '' B = B ∨ (g : Perm (Fin m)) '' B = Bᶜ) :=
    ⟨fun g => (g : Perm (Fin m)) '' B = B ∨ (g : Perm (Fin m)) '' B = Bᶜ, fun g => Iff.rfl⟩
  have hmul : ∀ a b : alternatingGroup (Fin m), P a → P b → P (a * b) := by
    intro a b ha hb
    rw [hP] at ha hb ⊢
    show ((a : Perm (Fin m)) * (b : Perm (Fin m))) '' B = B ∨
      ((a : Perm (Fin m)) * (b : Perm (Fin m))) '' B = Bᶜ
    rw [image_mul_eq]
    exact halves_image_mem ha hb
  have hone : P 1 := by
    rw [hP]
    left
    simp
  have hinv : ∀ a : alternatingGroup (Fin m), P a → P a⁻¹ := by
    intro a ha
    rw [hP] at ha ⊢
    show (⇑((a : Perm (Fin m))⁻¹)) '' B = B ∨ (⇑((a : Perm (Fin m))⁻¹)) '' B = Bᶜ
    exact halves_inv_mem ha
  exact ⟨⟨⟨⟨{g | P g}, fun {a b} ha hb => hmul a b ha hb⟩, hone⟩, fun {x} hx => hinv x hx⟩, hP⟩

theorem exists_cross_pair {m : ℕ} (hm : 3 ≤ m) {ι : Perm (Fin m)} (hιι : ∀ x, ι (ι x) = x)
    (O : Set (Fin m)) (h0 : O.Nonempty) (h1 : Oᶜ.Nonempty) :
    ∃ a ∈ O, ∃ b ∈ Oᶜ, b ≠ ι a := by
  by_contra hcon
  push Not at hcon
  obtain ⟨a₀, ha₀⟩ := h0
  obtain ⟨b₀, hb₀⟩ := h1
  have hb₀' : b₀ = ι a₀ := hcon a₀ ha₀ b₀ hb₀
  obtain ⟨y, hya₀, hyb₀⟩ := exists_ne_two hm a₀ b₀
  have hyO : y ∈ O := by
    by_contra hy
    exact hyb₀ (by rw [hcon a₀ ha₀ y hy, hb₀'])
  have hyb : b₀ = ι y := hcon y hyO b₀ hb₀
  have h3 : ι y = ι a₀ := hyb.symm.trans hb₀'
  have h4 : y = a₀ := by
    have h5 := congrArg ι h3
    rw [hιι, hιι] at h5
    exact h5
  exact hya₀ h4

theorem alt_pair_even {m : ℕ} (hm : 10 ≤ m) (hev : Even m) (T' : Subgroup (Perm (Fin m)))
    (hT' : IsPGroup 2 T') :
    ∃ Q₀ Q₁ : Subgroup (alternatingGroup (Fin m)), Q₀ ≠ ⊤ ∧ Q₁ ≠ ⊤ ∧ Q₀ ⊔ Q₁ = ⊤ ∧
      (∀ Q ∈ ({Q₀, Q₁} : Set (Subgroup (alternatingGroup (Fin m)))),
        (∀ τ ∈ T', ∀ g ∈ Q, ∀ h : τ * (g : Perm (Fin m)) * τ⁻¹ ∈ alternatingGroup (Fin m),
          (⟨τ * (g : Perm (Fin m)) * τ⁻¹, h⟩ : alternatingGroup (Fin m)) ∈ Q) ∧
        (∀ u : alternatingGroup (Fin m), (u : Perm (Fin m)) ∈ T' → u ∈ Q)) := by
  obtain ⟨ι, hιι, hιfix, hιT⟩ := exists_fpf_involution_comm hev (by omega) T' hT'
  have hιι' : ∀ x, ι (ι x) = x := fun x => by
    have h := congrArg (fun π : Perm (Fin m) => π x) hιι
    simpa using h
  obtain ⟨Q₁, hQ₁⟩ : ∃ Q : Subgroup (alternatingGroup (Fin m)), ∀ g : alternatingGroup (Fin m),
      g ∈ Q ↔ (g : Perm (Fin m)) * ι = ι * (g : Perm (Fin m)) :=
    ⟨(Subgroup.centralizer {ι}).subgroupOf _, fun g => by
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]⟩
  have hQ₁inv : ∀ τ ∈ T', ∀ g ∈ Q₁, ∀ h : τ * (g : Perm (Fin m)) * τ⁻¹ ∈ alternatingGroup (Fin m),
      (⟨τ * (g : Perm (Fin m)) * τ⁻¹, h⟩ : alternatingGroup (Fin m)) ∈ Q₁ := by
    intro τ hτ g hg h
    rw [hQ₁] at hg ⊢
    have hτi : τ⁻¹ * ι = ι * τ⁻¹ := hιT τ⁻¹ (inv_mem hτ)
    have hτι : τ * ι = ι * τ := hιT τ hτ
    show τ * (g : Perm (Fin m)) * τ⁻¹ * ι = ι * (τ * (g : Perm (Fin m)) * τ⁻¹)
    calc τ * (g : Perm (Fin m)) * τ⁻¹ * ι = τ * (g : Perm (Fin m)) * (τ⁻¹ * ι) := by
          simp only [mul_assoc]
      _ = τ * (g : Perm (Fin m)) * (ι * τ⁻¹) := by rw [hτi]
      _ = τ * ((g : Perm (Fin m)) * ι) * τ⁻¹ := by simp only [mul_assoc]
      _ = τ * (ι * (g : Perm (Fin m))) * τ⁻¹ := by rw [hg]
      _ = (τ * ι) * (g : Perm (Fin m)) * τ⁻¹ := by simp only [mul_assoc]
      _ = (ι * τ) * (g : Perm (Fin m)) * τ⁻¹ := by rw [hτι]
      _ = ι * (τ * (g : Perm (Fin m)) * τ⁻¹) := by simp only [mul_assoc]
  have hQ₁sup : ∀ u : alternatingGroup (Fin m), (u : Perm (Fin m)) ∈ T' → u ∈ Q₁ :=
    fun u hu => (hQ₁ u).2 (hιT _ hu)
  have hQ₁ne : Q₁ ≠ ⊤ := by
    obtain ⟨a⟩ : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
    obtain ⟨c, hca, hci⟩ := exists_ne_two (by omega) a (ι a)
    have hai : a ≠ ι a := fun h => hιfix a h.symm
    have hσ : swap a c * swap a (ι a) ∈ alternatingGroup (Fin m) :=
      cycle3_mem_alt hca.symm hai
    intro htop
    have hmem : (⟨swap a c * swap a (ι a), hσ⟩ : alternatingGroup (Fin m)) ∈ Q₁ := by
      rw [htop]
      exact Subgroup.mem_top _
    rw [hQ₁] at hmem
    have h1 : (swap a c * swap a (ι a) * ι) a = c := by
      rw [Perm.mul_apply, Perm.mul_apply, Equiv.swap_apply_right, Equiv.swap_apply_left]
    have h2 : (ι * (swap a c * swap a (ι a))) a = a := by
      rw [Perm.mul_apply, Perm.mul_apply, Equiv.swap_apply_left,
        Equiv.swap_apply_of_ne_of_ne (hιfix a) (Ne.symm hci), hιι']
    exact hca (h1.symm.trans ((congrArg (fun π : Perm (Fin m) => π a) hmem).trans h2))
  obtain ⟨Q₀, hQ₀ne, hQ₀sup, hQ₀inv, hQ₀T⟩ : ∃ Q₀ : Subgroup (alternatingGroup (Fin m)),
      Q₀ ≠ ⊤ ∧ Q₀ ⊔ Q₁ = ⊤ ∧
      (∀ τ ∈ T', ∀ g ∈ Q₀, ∀ h : τ * (g : Perm (Fin m)) * τ⁻¹ ∈ alternatingGroup (Fin m),
        (⟨τ * (g : Perm (Fin m)) * τ⁻¹, h⟩ : alternatingGroup (Fin m)) ∈ Q₀) ∧
      (∀ u : alternatingGroup (Fin m), (u : Perm (Fin m)) ∈ T' → u ∈ Q₀) := by
    by_cases hI : ∃ O : Set (Fin m), O.Nonempty ∧ Oᶜ.Nonempty ∧ 2 * O.ncard ≠ m ∧
        ∀ τ ∈ T', (τ : Perm (Fin m)) '' O = O
    ·
      obtain ⟨O, hO0, hO1, hOm, hO⟩ := hI
      have hco : IsCoatom (MulAction.stabilizer (alternatingGroup (Fin m)) O) :=
        alternatingGroup.isCoatom_stabilizer hO0 hO1 (by
          rw [Nat.card_eq_fintype_card, Fintype.card_fin]
          omega)
      refine ⟨MulAction.stabilizer (alternatingGroup (Fin m)) O, hco.ne_top, ?_, ?_, ?_⟩
      · have hle : MulAction.stabilizer (alternatingGroup (Fin m)) O ≤
            MulAction.stabilizer (alternatingGroup (Fin m)) O ⊔ Q₁ := le_sup_left
        rcases hco.le_iff.1 hle with h | h
        · exact h
        · exfalso
          have hQ1 : Q₁ ≤ MulAction.stabilizer (alternatingGroup (Fin m)) O :=
            le_of_le_of_eq le_sup_right h
          obtain ⟨a, ha, b, hb, hba⟩ := exists_cross_pair (by omega) hιι' O hO0 hO1
          have hab : a ≠ b := by
            rintro rfl
            exact hb ha
          have hιab : ι a ≠ ι b := fun h' => hab (by simpa [hιι'] using congrArg ι h')
          have hσA : swap a b * swap (ι a) (ι b) ∈ alternatingGroup (Fin m) :=
            sig_mem_alt hab hιab
          have hσQ : (⟨swap a b * swap (ι a) (ι b), hσA⟩ : alternatingGroup (Fin m)) ∈ Q₁ :=
            (hQ₁ _).2 (sig_comm hιι' (sig_nodup hιι' hιfix hab hba))
          have hσ0 := hQ1 hσQ
          rw [mem_stab_set_iff] at hσ0
          have hbO : b ∈ ((⟨swap a b * swap (ι a) (ι b), hσA⟩ : alternatingGroup (Fin m)) :
              Perm (Fin m)) '' O :=
            ⟨a, ha, sig_apply_left hιι' hιfix hba⟩
          rw [hσ0] at hbO
          exact hb hbO
      · intro τ hτ g hg h
        rw [mem_stab_set_iff] at hg ⊢
        show (τ * (g : Perm (Fin m)) * τ⁻¹) '' O = O
        rw [image_conj_eq, hO τ⁻¹ (inv_mem hτ), hg, hO τ hτ]
      · intro u hu
        rw [mem_stab_set_iff]
        exact hO _ hu
    ·
      have hB : ∃ B : Set (Fin m), 2 * B.ncard = m ∧
          ∀ τ ∈ T', (τ : Perm (Fin m)) '' B = B ∨ (τ : Perm (Fin m)) '' B = Bᶜ := by
        obtain ⟨p0⟩ : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
        by_cases hall : ∀ y : Fin m, ∃ τ ∈ T', τ p0 = y
        · refine exists_invariant_halves (by omega) T' hT' ?_
          intro x y
          obtain ⟨τx, hτx, hx⟩ := hall x
          obtain ⟨τy, hτy, hy⟩ := hall y
          refine ⟨τy * τx⁻¹, mul_mem hτy (inv_mem hτx), ?_⟩
          have hinv : τx⁻¹ (τx p0) = p0 := by simp [Equiv.Perm.inv_def]
          rw [← hx, Perm.mul_apply, hinv, hy]
        · push Not at hall
          obtain ⟨y, hy⟩ := hall
          obtain ⟨O₀, hO₀⟩ : ∃ O₀ : Set (Fin m), ∀ z, z ∈ O₀ ↔ ∃ τ ∈ T', τ p0 = z :=
            ⟨{z | ∃ τ ∈ T', τ p0 = z}, fun z => Iff.rfl⟩
          have hinv : ∀ σ ∈ T', (σ : Perm (Fin m)) '' O₀ = O₀ := by
            intro σ hσ
            ext z
            constructor
            · rintro ⟨w, hw, rfl⟩
              obtain ⟨τ, hτ, rfl⟩ := (hO₀ w).1 hw
              exact (hO₀ _).2 ⟨σ * τ, mul_mem hσ hτ, rfl⟩
            · intro hz
              obtain ⟨τ, hτ, rfl⟩ := (hO₀ z).1 hz
              refine ⟨(σ⁻¹ * τ) p0, (hO₀ _).2 ⟨σ⁻¹ * τ, mul_mem (inv_mem hσ) hτ, rfl⟩, ?_⟩
              simp [Perm.mul_apply]
          have hne : 2 * O₀.ncard = m := by
            by_contra hne
            refine hI ⟨O₀, ⟨p0, (hO₀ p0).2 ⟨1, Subgroup.one_mem T', rfl⟩⟩,
              ⟨y, fun hy' => ?_⟩, hne, hinv⟩
            obtain ⟨τ, hτ, hτy⟩ := (hO₀ y).1 hy'
            exact hy τ hτ hτy
          exact ⟨O₀, hne, fun τ hτ => Or.inl (hinv τ hτ)⟩
      obtain ⟨B, hB, hBinv⟩ := hB
      obtain ⟨Qh, hQh⟩ := exists_halves_subgroup B
      have hsum := Set.ncard_add_ncard_compl B
      rw [Nat.card_eq_fintype_card, Fintype.card_fin] at hsum
      have hB4 : 4 ≤ B.ncard := by omega
      have hBc4 : 4 ≤ Bᶜ.ncard := by omega
      refine ⟨Qh, ?_, ?_, ?_, ?_⟩
      ·
        intro htop
        obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩ :=
          (Set.two_lt_ncard_iff (Set.toFinite B)).1 (by omega : 2 < B.ncard)
        obtain ⟨c, hc⟩ := Set.nonempty_of_ncard_ne_zero (by omega : Bᶜ.ncard ≠ 0)
        have hxc : x ≠ c := by
          rintro rfl
          exact hc hx
        have hzc : z ≠ c := by
          rintro rfl
          exact hc hz
        have hgA : swap x c * swap x y ∈ alternatingGroup (Fin m) := cycle3_mem_alt hxc hxy
        have hmem : (⟨swap x c * swap x y, hgA⟩ : alternatingGroup (Fin m)) ∈ Qh := by
          rw [htop]
          exact Subgroup.mem_top _
        rw [hQh] at hmem
        rcases hmem with h | h
        · have hcg : c ∈ ((⟨swap x c * swap x y, hgA⟩ : alternatingGroup (Fin m)) :
              Perm (Fin m)) '' B :=
            ⟨y, hy, cycle3_apply_right⟩
          rw [h] at hcg
          exact hc hcg
        · have hzg : z ∈ ((⟨swap x c * swap x y, hgA⟩ : alternatingGroup (Fin m)) :
              Perm (Fin m)) '' B :=
            ⟨z, hz, cycle3_apply_fix (Ne.symm hxz) (Ne.symm hyz) hzc⟩
          rw [h] at hzg
          exact hzg hz
      ·
        obtain ⟨a, ha⟩ := Set.nonempty_of_ncard_ne_zero (by omega : B.ncard ≠ 0)
        obtain ⟨b, hb, hbF⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard
          (s := ({ι a} : Set (Fin m))) (t := Bᶜ) (by rw [Set.ncard_singleton]; omega)
        have hba : b ≠ ι a := by simpa using hbF
        have hab : a ≠ b := by
          rintro rfl
          exact hb ha
        have hιab : ι a ≠ ι b := fun h' => hab (by simpa [hιι'] using congrArg ι h')
        obtain ⟨u, hu, huF⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard
          (s := ({a, ι a, ι b} : Set (Fin m))) (t := B)
          (by have := ncard_triple_le_three a (ι a) (ι b); omega)
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at huF
        obtain ⟨hua, huia, huib⟩ := huF
        have hub : u ≠ b := by
          rintro rfl
          exact hb hu
        have hσA : swap a b * swap (ι a) (ι b) ∈ alternatingGroup (Fin m) :=
          sig_mem_alt hab hιab
        have hσQ : (⟨swap a b * swap (ι a) (ι b), hσA⟩ : alternatingGroup (Fin m)) ∈ Q₁ :=
          (hQ₁ _).2 (sig_comm hιι' (sig_nodup hιι' hιfix hab hba))
        have hsupp : ∀ g : alternatingGroup (Fin m), (∀ x ∈ Bᶜ, (g : Perm (Fin m)) x = x) →
            g ∈ Qh ⊔ Q₁ := fun g hg =>
          Subgroup.mem_sup_left ((hQh g).2 (Or.inl (image_eq_of_fix_compl hg)))
        have hsuppc : ∀ g : alternatingGroup (Fin m), (∀ x ∈ B, (g : Perm (Fin m)) x = x) →
            g ∈ Qh ⊔ Q₁ := fun g hg =>
          Subgroup.mem_sup_left ((hQh g).2 (Or.inl (image_eq_of_fix hg)))
        have hmix : ∃ g ∈ Qh ⊔ Q₁, (g : Perm (Fin m)) '' B ≠ B ∧
            (g : Perm (Fin m)) '' B ≠ Bᶜ := by
          refine ⟨⟨swap a b * swap (ι a) (ι b), hσA⟩, Subgroup.mem_sup_right hσQ, ?_, ?_⟩
          · intro h'
            have hbim : b ∈ ((⟨swap a b * swap (ι a) (ι b), hσA⟩ : alternatingGroup (Fin m)) :
                Perm (Fin m)) '' B :=
              ⟨a, ha, sig_apply_left hιι' hιfix hba⟩
            rw [h'] at hbim
            exact hb hbim
          · intro h'
            have huim : u ∈ ((⟨swap a b * swap (ι a) (ι b), hσA⟩ : alternatingGroup (Fin m)) :
                Perm (Fin m)) '' B :=
              ⟨u, hu, sig_apply_fix hua hub huia huib⟩
            rw [h'] at huim
            exact huim hu
        exact alt_eq_top_of_halves hB4 hBc4 (Qh ⊔ Q₁) hsupp hsuppc hmix
      ·
        intro τ hτ g hg h
        rw [hQh] at hg ⊢
        show (τ * (g : Perm (Fin m)) * τ⁻¹) '' B = B ∨
          (τ * (g : Perm (Fin m)) * τ⁻¹) '' B = Bᶜ
        rw [image_conj_eq]
        exact halves_image_mem (hBinv τ hτ) (halves_image_mem hg (hBinv τ⁻¹ (inv_mem hτ)))
      · intro u hu
        rw [hQh]
        exact hBinv _ hu
  refine ⟨Q₀, Q₁, hQ₀ne, hQ₁ne, hQ₀sup, ?_⟩
  rintro Q (rfl | rfl)
  · exact ⟨hQ₀inv, hQ₀T⟩
  · exact ⟨hQ₁inv, hQ₁sup⟩

end CFSG.Quasithin.B69K
