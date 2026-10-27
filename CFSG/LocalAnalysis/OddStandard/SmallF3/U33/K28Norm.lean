module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.K28Cent
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Wreath
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.WreathB

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

variable {Γ : Type*} [Group Γ]

theorem card_le_card_mul_card_inf_centralizer_pair (N : Subgroup Γ) [Finite N] (a b : Γ)
    (X : Finset (Γ × Γ)) (hX : ∀ n ∈ N, (n * a * n⁻¹, n * b * n⁻¹) ∈ X) :
    Nat.card N ≤ X.card * Nat.card ↥(N ⊓ Subgroup.centralizer ({a, b} : Set Γ)) := by
  classical
  let C : Subgroup Γ := N ⊓ Subgroup.centralizer ({a, b} : Set Γ)
  let C' : Subgroup ↥N := C.subgroupOf N
  have hCN : C ≤ N := inf_le_left
  have hcardC : Nat.card ↥C' = Nat.card ↥C :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCN).toEquiv
  let φ : ↥N → Γ × Γ := fun n => ((n : Γ) * a * (n : Γ)⁻¹, (n : Γ) * b * (n : Γ)⁻¹)
  have hφmem : ∀ n : ↥N, φ n ∈ X := fun n => hX n n.2
  let f : ↥N ⧸ C' → ↥X := Quotient.lift (fun n : ↥N => (⟨φ n, hφmem n⟩ : ↥X))
    (fun n m h => by
      have hmem : (QuotientGroup.leftRel C') n m := h
      rw [QuotientGroup.leftRel_apply] at hmem
      have hC : ((n⁻¹ * m : ↥N) : Γ) ∈ C := Subgroup.mem_subgroupOf.mp hmem
      have hcent : ((n⁻¹ * m : ↥N) : Γ) ∈ Subgroup.centralizer ({a, b} : Set Γ) :=
        (Subgroup.mem_inf.mp hC).2
      have hca : a * ((n⁻¹ * m : ↥N) : Γ) = ((n⁻¹ * m : ↥N) : Γ) * a :=
        (Subgroup.mem_centralizer_iff.mp hcent) a (by simp)
      have hcb : b * ((n⁻¹ * m : ↥N) : Γ) = ((n⁻¹ * m : ↥N) : Γ) * b :=
        (Subgroup.mem_centralizer_iff.mp hcent) b (by simp)
      have hcoe : ((n⁻¹ * m : ↥N) : Γ) = (n : Γ)⁻¹ * (m : Γ) := by simp
      rw [hcoe] at hca hcb
      apply Subtype.ext
      apply Prod.ext
      · show (n : Γ) * a * (n : Γ)⁻¹ = (m : Γ) * a * (m : Γ)⁻¹
        have key : (m : Γ) * a * (m : Γ)⁻¹ = (n : Γ) * a * (n : Γ)⁻¹ := by
          calc (m : Γ) * a * (m : Γ)⁻¹
              = (n : Γ) * ((n : Γ)⁻¹ * (m : Γ)) * a * (m : Γ)⁻¹ := by group
            _ = (n : Γ) * (((n : Γ)⁻¹ * (m : Γ)) * a) * (m : Γ)⁻¹ := by group
            _ = (n : Γ) * (a * ((n : Γ)⁻¹ * (m : Γ))) * (m : Γ)⁻¹ := by rw [← hca]
            _ = (n : Γ) * a * (n : Γ)⁻¹ := by group
        exact key.symm
      · show (n : Γ) * b * (n : Γ)⁻¹ = (m : Γ) * b * (m : Γ)⁻¹
        have key : (m : Γ) * b * (m : Γ)⁻¹ = (n : Γ) * b * (n : Γ)⁻¹ := by
          calc (m : Γ) * b * (m : Γ)⁻¹
              = (n : Γ) * ((n : Γ)⁻¹ * (m : Γ)) * b * (m : Γ)⁻¹ := by group
            _ = (n : Γ) * (((n : Γ)⁻¹ * (m : Γ)) * b) * (m : Γ)⁻¹ := by group
            _ = (n : Γ) * (b * ((n : Γ)⁻¹ * (m : Γ))) * (m : Γ)⁻¹ := by rw [← hcb]
            _ = (n : Γ) * b * (n : Γ)⁻¹ := by group
        exact key.symm)
  have hf : Function.Injective f := by
    intro q r h
    induction q using Quotient.inductionOn with
    | h n =>
      induction r using Quotient.inductionOn with
      | h m =>
        rw [QuotientGroup.eq]
        have hnm : (⟨φ n, hφmem n⟩ : ↥X) = ⟨φ m, hφmem m⟩ := h
        have hp : φ n = φ m := Subtype.ext_iff.mp hnm
        have ha' : (n : Γ) * a * (n : Γ)⁻¹ = (m : Γ) * a * (m : Γ)⁻¹ :=
          congrArg Prod.fst hp
        have hb' : (n : Γ) * b * (n : Γ)⁻¹ = (m : Γ) * b * (m : Γ)⁻¹ :=
          congrArg Prod.snd hp
        refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨(n⁻¹ * m).2, ?_⟩)
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        have hcoe : ((n⁻¹ * m : ↥N) : Γ) = (n : Γ)⁻¹ * (m : Γ) := by simp
        rcases hy with hya | hyb
        · rw [hya, hcoe]
          have hma : (m : Γ) * a = (n : Γ) * a * (n : Γ)⁻¹ * (m : Γ) := by
            calc (m : Γ) * a = (m : Γ) * a * (m : Γ)⁻¹ * (m : Γ) := by group
              _ = (n : Γ) * a * (n : Γ)⁻¹ * (m : Γ) := by rw [← ha']
          calc a * ((n : Γ)⁻¹ * (m : Γ))
              = (n : Γ)⁻¹ * ((n : Γ) * a * (n : Γ)⁻¹ * (m : Γ)) := by group
            _ = (n : Γ)⁻¹ * ((m : Γ) * a) := by rw [hma]
            _ = ((n : Γ)⁻¹ * (m : Γ)) * a := by group
        · rw [hyb, hcoe]
          have hmb : (m : Γ) * b = (n : Γ) * b * (n : Γ)⁻¹ * (m : Γ) := by
            calc (m : Γ) * b = (m : Γ) * b * (m : Γ)⁻¹ * (m : Γ) := by group
              _ = (n : Γ) * b * (n : Γ)⁻¹ * (m : Γ) := by rw [← hb']
          calc b * ((n : Γ)⁻¹ * (m : Γ))
              = (n : Γ)⁻¹ * ((n : Γ) * b * (n : Γ)⁻¹ * (m : Γ)) := by group
            _ = (n : Γ)⁻¹ * ((m : Γ) * b) := by rw [hmb]
            _ = ((n : Γ)⁻¹ * (m : Γ)) * b := by group
  have hlen : Nat.card (↥N ⧸ C') ≤ X.card := by
    have h := Nat.card_le_card_of_injective f hf
    have hXcard : Nat.card ↥X = X.card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    rwa [hXcard] at h
  change Nat.card ↥N ≤ X.card * Nat.card ↥C
  calc Nat.card ↥N = Nat.card (↥N ⧸ C') * Nat.card ↥C' :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup C'
    _ ≤ X.card * Nat.card ↥C' := Nat.mul_le_mul_right _ hlen
    _ = X.card * Nat.card ↥C := by rw [hcardC]

namespace K28

open CFSG.GH74.KGroups CFSG.GH74.KGroups.U33 CFSG.Sporadic.Schreier CFSG.Certificates

private instance finiteSubgroup (H : Subgroup Pm) : Finite H :=
  Finite.of_injective (Subtype.val : H → Pm) Subtype.val_injective

private theorem baseGrp_comm {a b : Pm} (ha : a ∈ baseGrp fx₁ fx₂)
    (hb : b ∈ baseGrp fx₁ fx₂) : a * b = b * a := by
  haveI := wreathRel_frame.baseGrp_eq.1
  simpa using congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : baseGrp fx₁ fx₂) ⟨b, hb⟩)

private theorem baseGrp_le_P : baseGrp fx₁ fx₂ ≤ QP.originalSubgroup := by
  rw [baseGrp, Subgroup.closure_le]
  intro x hx
  rcases hx with rfl | hx
  · exact fx₁_mem
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    exact fx₂_mem

private theorem fy_mem_base : fy ∈ baseGrp fx₁ fx₂ := by
  rw [fy_def]
  exact Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) 2

private theorem fz_mem_base : fz ∈ baseGrp fx₁ fx₂ := by
  change (fx₁ * fx₂) ^ 2 ∈ baseGrp fx₁ fx₂
  exact Subgroup.pow_mem _
    (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))) 2

private theorem fy_mul_self : fy * fy = 1 := by
  rw [fy_def, ← pow_add, show (2 : ℕ) + 2 = 4 by norm_num, fx₁_pow.1]

private theorem fz_mul_self : fz * fz = 1 := by
  have h4 : (fx₁ * fx₂) ^ 4 = 1 := by
    rw [Commute.mul_pow fx₁_fx₂_comm 4, fx₁_pow.1, fx₂_pow.1, one_mul]
  change (fx₁ * fx₂) ^ 2 * (fx₁ * fx₂) ^ 2 = 1
  rw [← pow_add, show (2 : ℕ) + 2 = 4 by norm_num, h4]

private theorem ftau_mul_self : ftau * ftau = 1 := by rw [← pow_two, ftau_pow.1]

private theorem fy_ne_one : fy ≠ 1 := fx₁_pow.2

private theorem fz_ne_one : fz ≠ 1 := by
  intro h
  apply fx₁_sq_ne
  have hx2 : fx₂ ^ 2 * fx₂ ^ 2 = 1 := by
    rw [← pow_add, show (2 : ℕ) + 2 = 4 by norm_num, fx₂_pow.1]
  have hprod : fx₁ ^ 2 * fx₂ ^ 2 = 1 := by
    rw [← fz_eq.1]; exact h
  calc fx₁ ^ 2 = fx₁ ^ 2 * (fx₂ ^ 2 * fx₂ ^ 2) := by rw [hx2, mul_one]
    _ = (fx₁ ^ 2 * fx₂ ^ 2) * fx₂ ^ 2 := by group
    _ = fx₂ ^ 2 := by rw [hprod, one_mul]

private theorem fy_ne_fz : fy ≠ fz := by
  intro h
  have h2 : fx₂ ^ 2 = 1 := by
    have hx2 : fx₂ ^ 2 = fy * fz := wreathRel_frame.x₂_sq
    rw [hx2, ← h, fy_mul_self]
  exact fx₂_pow.2 h2

private theorem fy_mul_fz_ne_one : fy * fz ≠ 1 := by
  intro h
  apply fy_ne_fz
  calc fy = fy * (fy * fz) := by rw [h, mul_one]
    _ = fy * fy * fz := by group
    _ = fz := by rw [fy_mul_self, one_mul]

private theorem fy_ne_fy_mul_fz : fy ≠ fy * fz := by
  intro h
  apply fz_ne_one
  have hfyinv : fy⁻¹ = fy := inv_eq_of_mul_eq_one_right fy_mul_self
  calc fz = (fy⁻¹ * fy) * fz := by rw [hfyinv, fy_mul_self, one_mul]
    _ = fy⁻¹ * (fy * fz) := by group
    _ = fy⁻¹ * fy := by rw [← h]
    _ = 1 := by rw [hfyinv, fy_mul_self]

private theorem fz_ne_fy_mul_fz : fz ≠ fy * fz := by
  intro h
  apply fy_ne_one
  have hfzinv : fz⁻¹ = fz := inv_eq_of_mul_eq_one_right fz_mul_self
  calc fy = (fy * fz) * fz⁻¹ := by rw [hfzinv, mul_assoc, fz_mul_self, mul_one]
    _ = fz * fz⁻¹ := by rw [← h]
    _ = 1 := by rw [hfzinv, fz_mul_self]

private theorem explicitList_nodup : ([1, fy, fz, fy * fz] : List Pm).Nodup := by
  rw [List.nodup_cons]
  refine ⟨?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨fy_ne_one.symm, fz_ne_one.symm, fy_mul_fz_ne_one.symm⟩
  · rw [List.nodup_cons]
    refine ⟨?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨fy_ne_fz, fy_ne_fy_mul_fz⟩
    · rw [List.nodup_cons]
      refine ⟨?_, ?_⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false]
        exact fz_ne_fy_mul_fz
      · rw [List.nodup_cons]
        exact ⟨by simp, List.nodup_nil⟩

private theorem inv_mul_inv_comm : fx₁⁻¹ * fx₂⁻¹ = (fx₁ * fx₂)⁻¹ := by
  calc fx₁⁻¹ * fx₂⁻¹ = (fx₂ * fx₁)⁻¹ := (mul_inv_rev fx₂ fx₁).symm
    _ = (fx₁ * fx₂)⁻¹ := by rw [← fx₁_fx₂_comm]

private theorem mem_normalizer_of_conj_gens {g : Pm}
    (h1 : g * fx₁ * g⁻¹ ∈ baseGrp fx₁ fx₂) (h2 : g * fx₂ * g⁻¹ ∈ baseGrp fx₁ fx₂) :
    g ∈ Subgroup.normalizer (baseGrp fx₁ fx₂) := by
  have hmap : (baseGrp fx₁ fx₂).map (MulAut.conj g).toMonoidHom =
      Subgroup.closure ({g * fx₁ * g⁻¹, g * fx₂ * g⁻¹} : Set Pm) := by
    rw [baseGrp, MonoidHom.map_closure, Set.image_pair]
    rfl
  have hle : (baseGrp fx₁ fx₂).map (MulAut.conj g).toMonoidHom ≤ baseGrp fx₁ fx₂ := by
    rw [hmap, Subgroup.closure_le]
    rintro x (hx : x ∈ ({g * fx₁ * g⁻¹, g * fx₂ * g⁻¹} : Set Pm))
    rcases hx with rfl | rfl
    · exact h1
    · exact h2
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact Subgroup.eq_of_le_of_card_ge hle
    (le_of_eq (Subgroup.card_map_of_injective (K := baseGrp fx₁ fx₂)
      (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective).symm)

private theorem conj_inv_of_conj {lam x y : Pm} (hl : lam * lam = 1)
    (h : lam * x * lam⁻¹ = y) : lam * y * lam⁻¹ = x := by
  have hlinv : lam⁻¹ = lam := inv_eq_of_mul_eq_one_right hl
  calc lam * y * lam⁻¹ = lam * (lam * x * lam⁻¹) * lam⁻¹ := by rw [← h]
    _ = (lam * lam) * x * (lam⁻¹ * lam⁻¹) := by group
    _ = x := by rw [hl, hlinv, hl, one_mul, mul_one]

private theorem fx₁_normW0 : fx₁ ∈ Subgroup.normalizer (baseGrp fx₁ fx₂) := by
  exact Subgroup.centralizer_le_normalizer _ (by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact baseGrp_comm hy (Subgroup.subset_closure (by simp)))

private theorem fx₂_normW0 : fx₂ ∈ Subgroup.normalizer (baseGrp fx₁ fx₂) := by
  exact Subgroup.centralizer_le_normalizer _ (by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact baseGrp_comm hy (Subgroup.subset_closure (by simp)))

private theorem frho_normW0 : frho ∈ Subgroup.normalizer (baseGrp fx₁ fx₂) := by
  refine mem_normalizer_of_conj_gens ?_ ?_
  · rw [frho_x₁]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.subset_closure (by simp)))
      (Subgroup.subset_closure (by simp))
  · rw [frho_x₂]
    exact Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))

private theorem flam_normW0 : flam ∈ Subgroup.normalizer (baseGrp fx₁ fx₂) := by
  refine mem_normalizer_of_conj_gens ?_ ?_
  · rw [flam_conj]
    exact Subgroup.subset_closure (by simp)
  · rw [conj_inv_of_conj (by rw [← pow_two, flam_pow.1]) flam_conj]
    exact Subgroup.subset_closure (by simp)

private theorem ftau_normW0 : ftau ∈ Subgroup.normalizer (baseGrp fx₁ fx₂) := by
  refine mem_normalizer_of_conj_gens ?_ ?_
  · rw [ftau_x₁]
    exact Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))
  · rw [ftau_x₂]
    exact Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))

private theorem baseGrp_sq_one_cases {x : Pm} (hx : x ∈ baseGrp fx₁ fx₂)
    (h2 : x * x = 1) : x = 1 ∨ x = fy ∨ x = fz ∨ x = fy * fz := by
  have hxfour : x ∈ fourGrp fx₁ fx₂ := by
    rw [(wreathRel_frame.fourGrp_eq_omega).1]
    exact Subgroup.subset_closure ⟨hx, h2⟩
  have hlist_mem : ∀ g ∈ ([1, fy, fz, fy * fz] : List Pm), g ∈ fourGrp fx₁ fx₂ := by
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure (Or.inl rfl)
    · exact Subgroup.subset_closure (Or.inr rfl)
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inl rfl))
        (Subgroup.subset_closure (Or.inr rfl))
  have hcard : Nat.card (fourGrp fx₁ fx₂) ≤ ([1, fy, fz, fy * fz] : List Pm).length := by
    rw [wreathRel_frame.fourGrp_eq_omega.2.2]
    rfl
  have hiff := mem_iff_of_card_le (fourGrp fx₁ fx₂) [1, fy, fz, fy * fz]
    hlist_mem explicitList_nodup hcard
  have := hiff x |>.mp hxfour
  simpa using this

@[expose] def yConjWs : List Pm := [1, fg3⁻¹, fg3, flam, fg3⁻¹ * flam, fg3 * flam]

private def pairIdx : Fin 6 → Pm × Pm
  | 0 => (fy, fz)
  | 1 => (fz, fy)
  | 2 => (fy, fy * fz)
  | 3 => (fy * fz, fy)
  | 4 => (fz, fy * fz)
  | 5 => (fy * fz, fz)

private def pairX : Finset (Pm × Pm) := Finset.univ.image pairIdx

private theorem pairX_card_le : pairX.card ≤ 6 := by
  rw [pairX]
  calc (Finset.univ.image pairIdx).card ≤ (Finset.univ : Finset (Fin 6)).card :=
        Finset.card_image_le
    _ = 6 := by simp

private theorem pairX_mem {p q : Pm} (hp : p = fy ∨ p = fz ∨ p = fy * fz)
    (hq : q = fy ∨ q = fz ∨ q = fy * fz) (hpq : p ≠ q) : (p, q) ∈ pairX := by
  have h0 : (fy, fz) ∈ pairX := Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  have h1 : (fz, fy) ∈ pairX := Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩
  have h2 : (fy, fy * fz) ∈ pairX := Finset.mem_image.mpr ⟨2, Finset.mem_univ _, rfl⟩
  have h3 : (fy * fz, fy) ∈ pairX := Finset.mem_image.mpr ⟨3, Finset.mem_univ _, rfl⟩
  have h4 : (fz, fy * fz) ∈ pairX := Finset.mem_image.mpr ⟨4, Finset.mem_univ _, rfl⟩
  have h5 : (fy * fz, fz) ∈ pairX := Finset.mem_image.mpr ⟨5, Finset.mem_univ _, rfl⟩
  rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl
  · exact absurd rfl hpq
  · exact h0
  · exact h2
  · exact h1
  · exact absurd rfl hpq
  · exact h4
  · exact h3
  · exact h5
  · exact absurd rfl hpq

private theorem yConjWs_length : yConjWs.length = 6 := by decide

theorem yConjWs_nodup : (yConjWs.map fun w => w * fy * w⁻¹).Nodup := by
  apply nodup_of_nodup_permTab
  rw [List.map_map]
  simp only [Function.comp_apply, yConjWs, List.map_cons, List.map_nil,
    permTab_mul, permTab_inv, permTab_one]
  decide +kernel

theorem yConjWs_mem : ∀ w ∈ yConjWs,
    w ∈ QP.originalSubgroup ⊓ Subgroup.centralizer ({fz} : Set Pm) := by
  intro w hw
  have hfg3c : fg3 ∈ Subgroup.centralizer ({fz} : Set Pm) :=
    Subgroup.mem_centralizer_singleton_iff.mpr fg3_pow.2.2
  have hflamc : flam ∈ Subgroup.centralizer ({fz} : Set Pm) :=
    Subgroup.mem_centralizer_singleton_iff.mpr frame_comm_fz.2.2
  simp only [yConjWs, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩
  · exact ⟨Subgroup.inv_mem _ fg3_mem, Subgroup.inv_mem _ hfg3c⟩
  · exact ⟨fg3_mem, hfg3c⟩
  · exact ⟨flam_mem, hflamc⟩
  · exact ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ fg3_mem) flam_mem,
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hfg3c) hflamc⟩
  · exact ⟨Subgroup.mul_mem _ fg3_mem flam_mem, Subgroup.mul_mem _ hfg3c hflamc⟩

private theorem D_eq_cent_E :
    (QP.originalSubgroup ⊓ Subgroup.centralizer ({fz} : Set Pm)) ⊓
        Subgroup.centralizer ({fy} : Set Pm) =
      QP.originalSubgroup ⊓ Subgroup.centralizer ({fy, fz} : Set Pm) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨⟨hxP, hz⟩, hy⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨hxP, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rcases hh with rfl | hh
    · exact (Subgroup.mem_centralizer_iff.mp hy) fy (by simp)
    · rw [Set.mem_singleton_iff] at hh
      subst hh
      exact (Subgroup.mem_centralizer_iff.mp hz) fz (by simp)
  · intro x hx
    obtain ⟨hxP, h⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hxP, ?_⟩, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact (Subgroup.mem_centralizer_iff.mp h) fz (by simp)
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact (Subgroup.mem_centralizer_iff.mp h) fy (by simp)

private theorem baseGrp_le_cent_E :
    baseGrp fx₁ fx₂ ≤ QP.originalSubgroup ⊓ Subgroup.centralizer ({fy, fz} : Set Pm) := by
  refine le_inf baseGrp_le_P ?_
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with rfl | rfl
  · exact (baseGrp_comm hx fy_mem_base).symm
  · exact (baseGrp_comm hx fz_mem_base).symm

theorem card_cent_E :
    Nat.card ↥(QP.originalSubgroup ⊓ Subgroup.centralizer ({fy, fz} : Set Pm)) = 16 := by
  classical
  let D : Subgroup Pm := QP.originalSubgroup ⊓ Subgroup.centralizer ({fz} : Set Pm)
  have hDcard : Nat.card D = 96 := card_cent_fz
  have hle : Nat.card ↥(D ⊓ Subgroup.centralizer ({fy} : Set Pm)) ≤ 16 := by
    have h := card_inf_centralizer_mul_le D fy yConjWs
      (fun w hw => yConjWs_mem w hw) yConjWs_nodup
    rw [yConjWs_length, hDcard] at h
    omega
  rw [← D_eq_cent_E]
  refine le_antisymm hle ?_
  have h := Subgroup.card_le_of_le baseGrp_le_cent_E
  rw [wreathRel_frame.baseGrp_eq.2.2, ← D_eq_cent_E] at h
  exact h

theorem cent_E_eq :
    QP.originalSubgroup ⊓ Subgroup.centralizer ({fy, fz} : Set Pm) = baseGrp fx₁ fx₂ := by
  refine (Subgroup.eq_of_le_of_card_ge baseGrp_le_cent_E ?_).symm
  rw [card_cent_E, wreathRel_frame.baseGrp_eq.2.2]

theorem cent_W0_eq :
    QP.originalSubgroup ⊓ Subgroup.centralizer (baseGrp fx₁ fx₂ : Set Pm) = baseGrp fx₁ fx₂ := by
  apply le_antisymm
  · have hsub : ({fy, fz} : Set Pm) ⊆ (baseGrp fx₁ fx₂ : Set Pm) := by
      intro x hx
      rcases hx with rfl | hx
      · exact fy_mem_base
      · rw [Set.mem_singleton_iff] at hx
        subst hx
        exact fz_mem_base
    calc QP.originalSubgroup ⊓ Subgroup.centralizer (baseGrp fx₁ fx₂ : Set Pm)
        ≤ QP.originalSubgroup ⊓ Subgroup.centralizer ({fy, fz} : Set Pm) :=
          le_inf inf_le_left (le_trans inf_le_right (Subgroup.centralizer_le hsub))
      _ = baseGrp fx₁ fx₂ := cent_E_eq
  · refine le_inf baseGrp_le_P ?_
    exact Subgroup.le_centralizer_iff_isMulCommutative.mpr wreathRel_frame.baseGrp_eq.1

private theorem subset4subset5 :
    ({fx₁, fx₂, frho, flam} : Set Pm) ⊆ ({fx₁, fx₂, frho, flam, ftau} : Set Pm) := by
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
  rcases hx with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))

private theorem closure_x1x2rholam_le_normalizer :
    Subgroup.closure ({fx₁, fx₂, frho, flam} : Set Pm) ≤
      QP.originalSubgroup ⊓ Subgroup.normalizer (baseGrp fx₁ fx₂) := by
  refine le_inf ?_ ?_
  · rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact fx₁_mem
    · exact fx₂_mem
    · exact frho_mem
    · exact flam_mem
  · rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact fx₁_normW0
    · exact fx₂_normW0
    · exact frho_normW0
    · exact flam_normW0

private theorem card_inf_normalizer_W0_le :
    Nat.card ↥(QP.originalSubgroup ⊓ Subgroup.normalizer (baseGrp fx₁ fx₂)) ≤ 96 := by
  classical
  let N : Subgroup Pm := QP.originalSubgroup ⊓ Subgroup.normalizer (baseGrp fx₁ fx₂)
  change Nat.card ↥N ≤ 96
  have hX : ∀ n ∈ N, (n * fy * n⁻¹, n * fz * n⁻¹) ∈ pairX := by
    intro n hn
    obtain ⟨-, hnorm⟩ := Subgroup.mem_inf.mp hn
    have hfyW : n * fy * n⁻¹ ∈ baseGrp fx₁ fx₂ :=
      (Subgroup.mem_normalizer_iff.mp hnorm fy).mp fy_mem_base
    have hfzW : n * fz * n⁻¹ ∈ baseGrp fx₁ fx₂ :=
      (Subgroup.mem_normalizer_iff.mp hnorm fz).mp fz_mem_base
    have hfy2 : (n * fy * n⁻¹) * (n * fy * n⁻¹) = 1 := by
      calc (n * fy * n⁻¹) * (n * fy * n⁻¹) = n * (fy * fy) * n⁻¹ := by group
        _ = 1 := by rw [fy_mul_self]; group
    have hfz2 : (n * fz * n⁻¹) * (n * fz * n⁻¹) = 1 := by
      calc (n * fz * n⁻¹) * (n * fz * n⁻¹) = n * (fz * fz) * n⁻¹ := by group
        _ = 1 := by rw [fz_mul_self]; group
    have hfy_ne1 : n * fy * n⁻¹ ≠ 1 := by
      intro h
      apply fy_ne_one
      calc fy = n⁻¹ * (n * fy * n⁻¹) * n := by group
        _ = n⁻¹ * 1 * n := by rw [h]
        _ = 1 := by group
    have hfz_ne1 : n * fz * n⁻¹ ≠ 1 := by
      intro h
      apply fz_ne_one
      calc fz = n⁻¹ * (n * fz * n⁻¹) * n := by group
        _ = n⁻¹ * 1 * n := by rw [h]
        _ = 1 := by group
    have hne : n * fy * n⁻¹ ≠ n * fz * n⁻¹ := by
      intro heq
      apply fy_ne_fz
      calc fy = n⁻¹ * (n * fy * n⁻¹) * n := by group
        _ = n⁻¹ * (n * fz * n⁻¹) * n := by rw [heq]
        _ = fz := by group
    have hfy3 : n * fy * n⁻¹ = fy ∨ n * fy * n⁻¹ = fz ∨ n * fy * n⁻¹ = fy * fz := by
      rcases baseGrp_sq_one_cases hfyW hfy2 with h | h | h | h
      · exact absurd h hfy_ne1
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    have hfz3 : n * fz * n⁻¹ = fy ∨ n * fz * n⁻¹ = fz ∨ n * fz * n⁻¹ = fy * fz := by
      rcases baseGrp_sq_one_cases hfzW hfz2 with h | h | h | h
      · exact absurd h hfz_ne1
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    exact pairX_mem hfy3 hfz3 hne
  have hbound := card_le_card_mul_card_inf_centralizer_pair N fy fz pairX hX
  have hC : Nat.card ↥(N ⊓ Subgroup.centralizer ({fy, fz} : Set Pm)) ≤ 16 := by
    have hle : N ⊓ Subgroup.centralizer ({fy, fz} : Set Pm) ≤
        QP.originalSubgroup ⊓ Subgroup.centralizer ({fy, fz} : Set Pm) :=
      le_inf (le_trans inf_le_left inf_le_left) inf_le_right
    calc Nat.card ↥(N ⊓ Subgroup.centralizer ({fy, fz} : Set Pm))
        ≤ Nat.card ↥(QP.originalSubgroup ⊓ Subgroup.centralizer ({fy, fz} : Set Pm)) :=
          Subgroup.card_le_of_le hle
      _ = 16 := card_cent_E
  calc Nat.card ↥N ≤ pairX.card * Nat.card ↥(N ⊓ Subgroup.centralizer ({fy, fz} : Set Pm)) :=
        hbound
    _ ≤ 6 * 16 := Nat.mul_le_mul pairX_card_le hC
    _ = 96 := by norm_num

private theorem card_closure_x1x2rholam :
    Nat.card ↥(Subgroup.closure ({fx₁, fx₂, frho, flam} : Set Pm)) = 96 := by
  let Cl : Subgroup Pm := Subgroup.closure ({fx₁, fx₂, frho, flam} : Set Pm)
  change Nat.card ↥Cl = 96
  have hClN : Cl ≤ QP.originalSubgroup ⊓ Subgroup.normalizer (baseGrp fx₁ fx₂) :=
    closure_x1x2rholam_le_normalizer
  have h32 : 32 ∣ Nat.card ↥Cl := by
    have hT : wreathGrp fx₁ fx₂ flam ≤ Cl := by
      rw [wreathGrp]
      exact Subgroup.closure_mono (by
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
        rcases hx with rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inr rfl)))
    have h := Subgroup.card_dvd_of_le hT
    rwa [card_T] at h
  have h3 : 3 ∣ Nat.card ↥Cl := by
    have hle : Subgroup.zpowers frho ≤ Cl := by
      rw [Subgroup.zpowers_le]
      exact Subgroup.subset_closure (by simp)
    have h := Subgroup.card_dvd_of_le hle
    rwa [Nat.card_zpowers, frho_ord] at h
  have h96 : 96 ∣ Nat.card ↥Cl := by
    have h := Nat.lcm_dvd h32 h3
    rw [Nat.Coprime.lcm_eq_mul (by decide : Nat.Coprime 32 3)] at h
    norm_num at h
    exact h
  haveI : Nonempty ↥Cl := ⟨1, Subgroup.one_mem _⟩
  have hge : 96 ≤ Nat.card ↥Cl := Nat.le_of_dvd Nat.card_pos h96
  have hle : Nat.card ↥Cl ≤ Nat.card ↥(QP.originalSubgroup ⊓
      Subgroup.normalizer (baseGrp fx₁ fx₂)) := Subgroup.card_le_of_le hClN
  exact le_antisymm (le_trans hle card_inf_normalizer_W0_le) hge

theorem norm_W0_eq :
    QP.originalSubgroup ⊓ Subgroup.normalizer (baseGrp fx₁ fx₂ : Set Pm) =
      Subgroup.closure {fx₁, fx₂, frho, flam} := by
  refine (Subgroup.eq_of_le_of_card_ge closure_x1x2rholam_le_normalizer ?_).symm
  rw [card_closure_x1x2rholam]
  exact card_inf_normalizer_W0_le

theorem centA_W0_eq :
    QA.originalSubgroup ⊓ Subgroup.centralizer (baseGrp fx₁ fx₂ : Set Pm) = baseGrp fx₁ fx₂ := by
  apply le_antisymm
  · intro a ha
    obtain ⟨haA, haC⟩ := Subgroup.mem_inf.mp ha
    rcases mem_A_cases a haA with haP | hap
    · have haN : a ∈ QP.originalSubgroup ⊓
          Subgroup.centralizer (baseGrp fx₁ fx₂ : Set Pm) := ⟨haP, haC⟩
      rwa [cent_W0_eq] at haN
    · exfalso
      set p : Pm := a * ftau with hp
      have hpP : p ∈ QP.originalSubgroup := hap
      have hax1 : a * fx₁⁻¹ = fx₁⁻¹ * a :=
        ((Subgroup.mem_centralizer_iff.mp haC) fx₁⁻¹
          (Subgroup.inv_mem _ (Subgroup.subset_closure (by simp)))).symm
      have hax2 : a * fx₂⁻¹ = fx₂⁻¹ * a :=
        ((Subgroup.mem_centralizer_iff.mp haC) fx₂⁻¹
          (Subgroup.inv_mem _ (Subgroup.subset_closure (by simp)))).symm
      have hconj1 : p * fx₁ * p⁻¹ = fx₁⁻¹ := by
        rw [hp]
        calc (a * ftau) * fx₁ * (a * ftau)⁻¹
            = a * (ftau * fx₁ * ftau⁻¹) * a⁻¹ := by group
          _ = a * fx₁⁻¹ * a⁻¹ := by rw [ftau_x₁]
          _ = fx₁⁻¹ := by rw [hax1]; group
      have hconj2 : p * fx₂ * p⁻¹ = fx₂⁻¹ := by
        rw [hp]
        calc (a * ftau) * fx₂ * (a * ftau)⁻¹
            = a * (ftau * fx₂ * ftau⁻¹) * a⁻¹ := by group
          _ = a * fx₂⁻¹ * a⁻¹ := by rw [ftau_x₂]
          _ = fx₂⁻¹ := by rw [hax2]; group
      have hfy2 : fx₁ ^ 2 * fx₁ ^ 2 = 1 := by
        rw [← pow_add, show (2 : ℕ) + 2 = 4 by norm_num, fx₁_pow.1]
      have hfyinv : (fx₁ ^ 2)⁻¹ = fx₁ ^ 2 := inv_eq_of_mul_eq_one_right hfy2
      have hpfy : p * fy * p⁻¹ = fy := by
        have hsq : p * fx₁ ^ 2 * p⁻¹ = (p * fx₁ * p⁻¹) ^ 2 := by
          rw [pow_two, pow_two]; group
        rw [fy_def, hsq, hconj1, inv_pow, hfyinv]
      have hfz2 : (fx₁ * fx₂) ^ 2 * (fx₁ * fx₂) ^ 2 = 1 := by
        have h4 : (fx₁ * fx₂) ^ 4 = 1 := by
          rw [Commute.mul_pow fx₁_fx₂_comm 4, fx₁_pow.1, fx₂_pow.1, one_mul]
        rw [← pow_add, show (2 : ℕ) + 2 = 4 by norm_num, h4]
      have hfzinv : ((fx₁ * fx₂) ^ 2)⁻¹ = (fx₁ * fx₂) ^ 2 :=
        inv_eq_of_mul_eq_one_right hfz2
      have hconj12 : p * (fx₁ * fx₂) * p⁻¹ = (fx₁ * fx₂)⁻¹ := by
        calc p * (fx₁ * fx₂) * p⁻¹ = (p * fx₁ * p⁻¹) * (p * fx₂ * p⁻¹) := by group
          _ = fx₁⁻¹ * fx₂⁻¹ := by rw [hconj1, hconj2]
          _ = (fx₁ * fx₂)⁻¹ := inv_mul_inv_comm
      have hpfz : p * fz * p⁻¹ = fz := by
        have hsq : p * (fx₁ * fx₂) ^ 2 * p⁻¹ = (p * (fx₁ * fx₂) * p⁻¹) ^ 2 := by
          rw [pow_two, pow_two]; group
        rw [show fz = (fx₁ * fx₂) ^ 2 from rfl, hsq, hconj12, inv_pow, hfzinv]
      have hpcent : p ∈ Subgroup.centralizer ({fy, fz} : Set Pm) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl
        · have hcomm : p * fy = fy * p := by
            calc p * fy = p * fy * p⁻¹ * p := by group
              _ = fy * p := by rw [hpfy]
          exact hcomm.symm
        · have hcomm : p * fz = fz * p := by
            calc p * fz = p * fz * p⁻¹ * p := by group
              _ = fz * p := by rw [hpfz]
          exact hcomm.symm
      have hpW : p ∈ baseGrp fx₁ fx₂ := by
        rw [← cent_E_eq]
        exact ⟨hpP, hpcent⟩
      have hpcomm : p * fx₁ = fx₁ * p :=
        baseGrp_comm hpW (Subgroup.subset_closure (by simp))
      have hfeq : fx₁ = fx₁⁻¹ := by
        have h1 : p * fx₁ * p⁻¹ = fx₁ := by rw [hpcomm, mul_assoc, mul_inv_cancel, mul_one]
        exact h1.symm.trans hconj1
      have hsq : fx₁ ^ 2 = 1 := by
        rw [pow_two]
        exact eq_inv_iff_mul_eq_one.mp hfeq
      exact fx₁_pow.2 hsq
  · refine le_inf (le_trans baseGrp_le_P P_le_A) ?_
    exact Subgroup.le_centralizer_iff_isMulCommutative.mpr wreathRel_frame.baseGrp_eq.1

theorem normA_W0_eq :
    QA.originalSubgroup ⊓ Subgroup.normalizer (baseGrp fx₁ fx₂ : Set Pm) =
      Subgroup.closure {fx₁, fx₂, frho, flam, ftau} := by
  apply le_antisymm
  · intro a ha
    obtain ⟨haA, hanorm⟩ := Subgroup.mem_inf.mp ha
    rcases mem_A_cases a haA with haP | hap
    · have haN : a ∈ QP.originalSubgroup ⊓
          Subgroup.normalizer (baseGrp fx₁ fx₂ : Set Pm) := ⟨haP, hanorm⟩
      rw [norm_W0_eq] at haN
      exact Subgroup.closure_mono subset4subset5 haN
    · have hpnorm : a * ftau ∈ Subgroup.normalizer (baseGrp fx₁ fx₂ : Set Pm) :=
        Subgroup.mul_mem _ hanorm ftau_normW0
      have hpCl : a * ftau ∈ Subgroup.closure ({fx₁, fx₂, frho, flam} : Set Pm) := by
        rw [← norm_W0_eq]
        exact ⟨hap, hpnorm⟩
      have hftauCl : ftau ∈ Subgroup.closure ({fx₁, fx₂, frho, flam, ftau} : Set Pm) :=
        Subgroup.subset_closure (by simp)
      have haeq : a = (a * ftau) * ftau := by rw [mul_assoc, ftau_mul_self, mul_one]
      rw [haeq]
      exact Subgroup.mul_mem _ (Subgroup.closure_mono subset4subset5 hpCl) hftauCl
  · refine le_inf ?_ ?_
    · rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact P_le_A fx₁_mem
      · exact P_le_A fx₂_mem
      · exact P_le_A frho_mem
      · exact P_le_A flam_mem
      · exact ftau_mem_A
    · rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact fx₁_normW0
      · exact fx₂_normW0
      · exact frho_normW0
      · exact flam_normW0
      · exact ftau_normW0

end K28

end CFSG.OddStandard.SmallF3.HarrisU33
