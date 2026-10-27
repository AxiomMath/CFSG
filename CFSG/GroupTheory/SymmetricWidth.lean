module

public import CFSG.GroupTheory.SymmetricFiveWidth

public section

namespace CFSG.GroupTheory

open CFSG.OddTranspositions

@[expose] def transpositionsFin (m : ℕ) : Set (Equiv.Perm (Fin m)) := {σ | σ.IsSwap}

theorem transpositionsFin_subset_of_le {m : ℕ} (hm : m ≤ 5) :
    ∃ e : Equiv.Perm (Fin m) → Equiv.Perm (Fin 5), Function.Injective e ∧
      (∀ σ, σ.IsSwap → e σ ∈ transpositions) ∧
      (∀ σ τ, Commute σ τ → Commute (e σ) (e τ)) := by
  classical
  let ι : Fin m ↪ Fin 5 := Fin.castLEEmb hm
  let e : Equiv.Perm (Fin m) → Equiv.Perm (Fin 5) := Equiv.Perm.viaEmbeddingHom ι
  refine ⟨e, Equiv.Perm.viaEmbeddingHom_injective ι, ?_, ?_⟩
  · intro σ hσ
    obtain ⟨x, y, hxy, rfl⟩ := hσ
    change (Equiv.Perm.viaEmbedding (Equiv.swap x y) ι).IsSwap
    refine ⟨ι x, ι y, fun h => hxy (ι.injective h), ?_⟩
    ext z
    by_cases hz : z ∈ Set.range ι
    · obtain ⟨w, rfl⟩ := hz
      rw [Equiv.Perm.viaEmbedding_apply]
      rcases eq_or_ne w x with rfl | hwx
      · rw [Equiv.swap_apply_left, Equiv.swap_apply_left]
      · rcases eq_or_ne w y with rfl | hwy
        · rw [Equiv.swap_apply_right, Equiv.swap_apply_right]
        · rw [Equiv.swap_apply_of_ne_of_ne hwx hwy,
            Equiv.swap_apply_of_ne_of_ne (fun h => hwx (ι.injective h))
              (fun h => hwy (ι.injective h))]
    · have hz1 : Equiv.Perm.viaEmbedding (Equiv.swap x y) ι z = z :=
        Equiv.Perm.viaEmbedding_apply_of_notMem (Equiv.swap x y) ι z hz
      have hz2 : Equiv.swap (ι x) (ι y) z = z :=
        Equiv.swap_apply_of_ne_of_ne (fun h => hz ⟨x, h.symm⟩) (fun h => hz ⟨y, h.symm⟩)
      rw [hz1, hz2]
  · intro σ τ h
    exact h.map (Equiv.Perm.viaEmbeddingHom ι)

theorem widthLe_transpositionsFin_of_le {m : ℕ} (hm : m ≤ 5) :
    WidthLe (transpositionsFin m) 2 := by
  classical
  obtain ⟨e, hinj, hswap, hcomm⟩ := transpositionsFin_subset_of_le hm
  intro S hS hpair
  have hsub : (↑(S.image e) : Set (Equiv.Perm (Fin 5))) ⊆ transpositions := by
    intro σ hσ
    obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.mp hσ
    exact hswap τ (hS hτ)
  have hpair' : ∀ x ∈ S.image e, ∀ y ∈ S.image e, x ≠ y → Commute x y := by
    intro x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    exact hcomm a b (hpair a ha b hb fun hab => hxy (by rw [hab]))
  have hcard : (S.image e).card = S.card := Finset.card_image_of_injective S hinj
  have hle := swaps_widthLe_two (S.image e) hsub hpair'
  omega

theorem widthLe_transpositionsFin_of_six_le {m : ℕ} (hm : 6 ≤ m) :
    ¬ WidthLe (transpositionsFin m) 2 := by
  classical
  let a : Fin m := ⟨0, by omega⟩
  let b : Fin m := ⟨1, by omega⟩
  let c : Fin m := ⟨2, by omega⟩
  let d : Fin m := ⟨3, by omega⟩
  let e : Fin m := ⟨4, by omega⟩
  let f : Fin m := ⟨5, by omega⟩
  have hab : a ≠ b := fun h => by
    have h' : (0 : ℕ) = 1 := congrArg Fin.val h
    omega
  have hac : a ≠ c := fun h => by
    have h' : (0 : ℕ) = 2 := congrArg Fin.val h
    omega
  have had : a ≠ d := fun h => by
    have h' : (0 : ℕ) = 3 := congrArg Fin.val h
    omega
  have hae : a ≠ e := fun h => by
    have h' : (0 : ℕ) = 4 := congrArg Fin.val h
    omega
  have haf : a ≠ f := fun h => by
    have h' : (0 : ℕ) = 5 := congrArg Fin.val h
    omega
  have hbc : b ≠ c := fun h => by
    have h' : (1 : ℕ) = 2 := congrArg Fin.val h
    omega
  have hbd : b ≠ d := fun h => by
    have h' : (1 : ℕ) = 3 := congrArg Fin.val h
    omega
  have hbe : b ≠ e := fun h => by
    have h' : (1 : ℕ) = 4 := congrArg Fin.val h
    omega
  have hbf : b ≠ f := fun h => by
    have h' : (1 : ℕ) = 5 := congrArg Fin.val h
    omega
  have hcd : c ≠ d := fun h => by
    have h' : (2 : ℕ) = 3 := congrArg Fin.val h
    omega
  have hce : c ≠ e := fun h => by
    have h' : (2 : ℕ) = 4 := congrArg Fin.val h
    omega
  have hcf : c ≠ f := fun h => by
    have h' : (2 : ℕ) = 5 := congrArg Fin.val h
    omega
  have hde : d ≠ e := fun h => by
    have h' : (3 : ℕ) = 4 := congrArg Fin.val h
    omega
  have hdf : d ≠ f := fun h => by
    have h' : (3 : ℕ) = 5 := congrArg Fin.val h
    omega
  have hef : e ≠ f := fun h => by
    have h' : (4 : ℕ) = 5 := congrArg Fin.val h
    omega
  have hnodup : ∀ {x y z t : Fin m}, x ≠ y → x ≠ z → x ≠ t → y ≠ z → y ≠ t → z ≠ t →
      [x, y, z, t].Nodup := by
    intro x y z t hxy hxz hxt hyz hyt hzt
    simp [List.nodup_cons, hxy, hxz, hxt, hyz, hyt, hzt]
  have hne : ∀ {x y z t : Fin m}, x ≠ y → x ≠ z → x ≠ t → y ≠ z → y ≠ t →
      Equiv.swap x y ≠ Equiv.swap z t := by
    intro x y z t hxy hxz hxt hyz hyt h
    have h1 : y = x := by
      have h2 := congrArg (fun σ : Equiv.Perm (Fin m) => σ x) h
      simpa [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hxz hxt] using h2
    exact hxy h1.symm
  have hS12 : Equiv.swap a b ≠ Equiv.swap c d := hne hab hac had hbc hbd
  have hS13 : Equiv.swap a b ≠ Equiv.swap e f := hne hab hae haf hbe hbf
  have hS23 : Equiv.swap c d ≠ Equiv.swap e f := hne hcd hce hcf hde hdf
  let S : Finset (Equiv.Perm (Fin m)) :=
    {Equiv.swap a b, Equiv.swap c d, Equiv.swap e f}
  have hsub : (↑S : Set (Equiv.Perm (Fin m))) ⊆ transpositionsFin m := by
    intro σ hσ
    simp only [S, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hσ
    rcases hσ with rfl | rfl | rfl
    · exact ⟨a, b, hab, rfl⟩
    · exact ⟨c, d, hcd, rfl⟩
    · exact ⟨e, f, hef, rfl⟩
  have hpair : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Commute x y := by
    intro x hx y hy hxy
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    · exact absurd rfl hxy
    · exact (Equiv.Perm.disjoint_swap_swap (hnodup hab hac had hbc hbd hcd)).commute
    · exact (Equiv.Perm.disjoint_swap_swap (hnodup hab hae haf hbe hbf hef)).commute
    · exact ((Equiv.Perm.disjoint_swap_swap (hnodup hab hac had hbc hbd hcd)).commute).symm
    · exact absurd rfl hxy
    · exact (Equiv.Perm.disjoint_swap_swap (hnodup hcd hce hcf hde hdf hef)).commute
    · exact ((Equiv.Perm.disjoint_swap_swap (hnodup hab hae haf hbe hbf hef)).commute).symm
    · exact ((Equiv.Perm.disjoint_swap_swap (hnodup hcd hce hcf hde hdf hef)).commute).symm
    · exact absurd rfl hxy
  have hcard : S.card = 3 := by
    have hnot1 : Equiv.swap a b ∉ ({Equiv.swap c d, Equiv.swap e f} : Finset _) := by
      simp [hS12, hS13]
    have hnot2 : Equiv.swap c d ∉ ({Equiv.swap e f} : Finset _) := by
      simp [hS23]
    rw [show S = ({Equiv.swap a b, Equiv.swap c d, Equiv.swap e f} : Finset _) from rfl,
      Finset.card_insert_of_notMem hnot1, Finset.card_insert_of_notMem hnot2,
      Finset.card_singleton]
  intro hwidth
  have := hwidth S hsub hpair
  omega

theorem widthLe_transpositionsFin_iff {m : ℕ} (hm : 2 ≤ m) :
    WidthLe (transpositionsFin m) 2 ↔ m ≤ 5 := by
  by_cases h : m ≤ 5
  · exact ⟨fun _ => h, fun _ => widthLe_transpositionsFin_of_le h⟩
  · have h6 : 6 ≤ m := by omega
    exact ⟨fun hw => absurd hw (widthLe_transpositionsFin_of_six_le h6), fun h5 => absurd h5 h⟩

end CFSG.GroupTheory
