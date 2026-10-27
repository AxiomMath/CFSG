module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.PropA.AutModel
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.PropA.CosetHom

public section

namespace CFSG.EvenSporadicStandard.M12Std.PropA

open Equiv Subgroup CFSG.Sporadic.Schreier

theorem exists_emb_of_hom {C : Type*} [Group C] [Finite C]
    (N : Subgroup C) [N.Normal] {t g : C} (ht : ∀ c : C, c * t = t * c) (ht2 : orderOf t = 2)
    (htN : t ∉ N) (π : C →* Perm (Fin 24)) (hker : π.ker = zpowers t)
    (hN : N.map π = D24) (hπg : π g = m12Sigma) (hcard : Nat.card C = 380160) :
    ∃ (b : Bool) (ι : C →* Perm (Fin 28)), Function.Injective ι ∧ N.map ι = D28 ∧ ι t = pT ∧
      K28 b ≤ ι.range := by
  classical
  have ht2' : t * t = 1 := by
    rw [← pow_two, ← ht2]
    exact pow_orderOf_eq_one t
  have hπt : π t = 1 := by
    rw [← MonoidHom.mem_ker, hker]
    exact Subgroup.mem_zpowers t
  have hzp : ∀ c : C, c ∈ zpowers t → c = 1 ∨ c = t := by
    intro c hc
    rw [mem_zpowers_iff_mem_range_orderOf, Finset.mem_image] at hc
    obtain ⟨i, hi, hci⟩ := hc
    rw [Finset.mem_range, ht2] at hi
    interval_cases i
    · left; simpa using hci.symm
    · right; simpa using hci.symm
  have hgN : g ∉ N := by
    intro hg
    have hmem : π g ∈ N.map π := Subgroup.mem_map_of_mem π hg
    rw [hN, hπg] at hmem
    exact sigma_not_mem_D24 hmem
  have hgtN : g * t ∉ N := by
    intro hgt
    have hmem : π (g * t) ∈ N.map π := Subgroup.mem_map_of_mem π hgt
    rw [hN, map_mul, hπg, hπt, mul_one] at hmem
    exact sigma_not_mem_D24 hmem
  have hkerN : (π.comp N.subtype).ker = ⊥ := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_bot]
    constructor
    · intro hx
      have hxt : (x : C) ∈ zpowers t := by
        rw [← hker]
        exact MonoidHom.mem_ker.mpr hx
      rcases hzp (x : C) hxt with h | h
      · exact Subtype.ext h
      · exact absurd (h ▸ x.2) htN
    · intro hx
      rw [hx]
      simp
  have hinj_restrict : Function.Injective (π.comp N.subtype) :=
    (MonoidHom.ker_eq_bot_iff _).mp hkerN
  have hcardN : Nat.card N = 95040 := by
    have h1 := Subgroup.card_map_of_injective (K := (⊤ : Subgroup N)) hinj_restrict
    have hmap : Subgroup.map (π.comp N.subtype) (⊤ : Subgroup N) = N.map π := by
      ext x; constructor
      · rintro ⟨y, -, rfl⟩
        exact ⟨y, y.2, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨⟨y, hy⟩, trivial, rfl⟩
    rw [hmap, Subgroup.card_top, hN, card_D24] at h1
    exact h1.symm
  have hcard4 : Nat.card (C ⧸ N) = 4 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [hcard, hcardN] at h
    omega
  have hgg_mem : g * g ∈ zpowers t := by
    rw [← hker, MonoidHom.mem_ker]
    simp [hπg, sigma_mul_self]
  have hgg : g * g = 1 ∨ g * g = t := hzp _ hgg_mem
  obtain ⟨τ, hτN, hτt, hτg1, hτg2⟩ :=
    exists_coset_hom N ht ht2' hgg htN hgN hgtN hcard4
  let j : Perm (Fin 24) →* Perm (Fin 28) := block28.comp (MonoidHom.inl _ _)
  let ι : C →* Perm (Fin 28) := block28.comp (π.prod τ)
  have hι_eq_j : ∀ n ∈ N, ι n = j (π n) := by
    intro n hn
    simp [ι, j, MonoidHom.prod_apply, MonoidHom.inl_apply, hτN n hn]
  have hinj : Function.Injective ι := by
    intro a b hab
    have hφ : (π.prod τ) a = (π.prod τ) b := block28_injective hab
    have hπab : π a = π b := by simpa using congrArg Prod.fst hφ
    have hτab : τ a = τ b := by simpa using congrArg Prod.snd hφ
    have hmem : a * b⁻¹ ∈ zpowers t := by
      rw [← hker, MonoidHom.mem_ker]
      simp [hπab]
    rcases hzp _ hmem with h1 | h2
    · exact eq_of_mul_inv_eq_one h1
    · have hτ1 : τ (a * b⁻¹) = 1 := by simp [hτab]
      rw [h2, hτt] at hτ1
      exact absurd hτ1 (by decide)
  have hD24 : D24 = Subgroup.closure ({m12A1, m12B1} : Set (Perm (Fin 24))) := by
    change m12D.originalSubgroup = Subgroup.closure ({m12A1, m12B1} : Set (Perm (Fin 24)))
    rw [m12D_eq_closure]
    congr 1
    ext x
    simp
  have hDj : D24.map j = D28 := by
    rw [hD24, MonoidHom.map_closure, Set.image_pair]
    change Subgroup.closure {j m12A1, j m12B1} = Subgroup.closure {pA, pB}
    rw [show j m12A1 = pA from rfl, show j m12B1 = pB from rfl]
  have hmapN : N.map ι = D28 := by
    apply le_antisymm
    · rintro x ⟨n, hn, rfl⟩
      have hπn : π n ∈ D24 := by
        rw [← hN]
        exact Subgroup.mem_map_of_mem π hn
      rw [hι_eq_j n hn, ← hDj]
      exact Subgroup.mem_map_of_mem j hπn
    · rw [← hDj]
      rintro x ⟨y, hy, rfl⟩
      rw [← hN] at hy
      obtain ⟨n, hn, rfl⟩ := hy
      rw [← hι_eq_j n hn]
      exact Subgroup.mem_map_of_mem ι hn
  have hιt : ι t = pT := by
    simp [ι, pT, MonoidHom.prod_apply, hπt, hτt]
  set b : Bool := if g * g = t then true else false with hb
  have hpg : pG b = ι g := by
    by_cases hggt : g * g = t
    · have hbval : b = true := by simp [hb, hggt]
      have hτg : τ g = hTwo := hτg2 hggt
      simp [pG, ι, MonoidHom.prod_apply, hπg, hτg, hbval]
    · have hgg1 : g * g = 1 := hgg.resolve_right hggt
      have hbval : b = false := by simp [hb, hggt]
      have hτg : τ g = hOne := hτg1 hgg1
      simp [pG, ι, MonoidHom.prod_apply, hπg, hτg, hbval]
  have hsub : N.map ι ≤ ι.range := Subgroup.map_le_range (f := ι) N
  have hK : K28 b ≤ ι.range := by
    change Subgroup.closure ({pA, pB, pG b, pT} : Set (Perm (Fin 28))) ≤ ι.range
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact hsub (by rw [hmapN]; exact Subgroup.subset_closure (by simp))
    · exact hsub (by rw [hmapN]; exact Subgroup.subset_closure (by simp))
    · exact MonoidHom.mem_range.mpr ⟨g, hpg.symm⟩
    · exact MonoidHom.mem_range.mpr ⟨t, hιt⟩
  exact ⟨b, ι, hinj, hmapN, hιt, hK⟩

end CFSG.EvenSporadicStandard.M12Std.PropA
