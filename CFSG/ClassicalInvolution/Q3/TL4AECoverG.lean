module

public import CFSG.ClassicalInvolution.Q3.TL4AECoverD
public import CFSG.ClassicalInvolution.Q3.TL4AECoverE
public import CFSG.ClassicalInvolution.Q3.TL4AECoverF

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.AECov

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE
open CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.LocalAnalysis.ComponentInitial (altThreeCycle coe_altThreeCycle_mul)

variable {m : ℕ}

@[expose] def alpha0 (hm : 2 ≤ m) : Finset (Fin (m + 2)) :=
  Finset.univ.map (Fin.castLEEmb (by omega : 4 ≤ m + 2))

theorem card_alpha0 (hm : 2 ≤ m) : (alpha0 hm).card = 4 := by
  simp [alpha0]

theorem emb_alpha0 (hm : 2 ≤ m) (i : Fin 4) :
    emb (alpha0 hm) (card_alpha0 hm) i = Fin.castLE (by omega) i := by
  have h := Finset.orderEmbOfFin_unique (card_alpha0 hm) (f := Fin.castLE (by omega))
    (fun x => Finset.mem_map_of_mem _ (Finset.mem_univ x)) (Fin.strictMono_castLE _)
  exact (congrFun h i).symm

theorem embedPerm_alpha0_d₂ (hm : 2 ≤ m) :
    embedPerm (emb (alpha0 hm) (card_alpha0 hm)) d₂ =
      Equiv.swap (0 : Fin (m + 2)) ⟨2, by omega⟩ * Equiv.swap (1 : Fin (m + 2)) ⟨3, by omega⟩ := by
  have h4 : 4 ≤ m + 2 := by omega
  refine Equiv.ext fun x => ?_
  by_cases hx : x.val < 4
  · obtain ⟨i, hi⟩ : ∃ i : Fin 4, Fin.castLE h4 i = x := ⟨⟨x.val, hx⟩, Fin.ext rfl⟩
    rw [← hi, ← emb_alpha0 hm i, embedPerm_apply, emb_alpha0, emb_alpha0]
    fin_cases i <;> simp [d₂, Equiv.swap_apply_def, Equiv.Perm.mul_apply, Fin.ext_iff]
  · have hxr : x ∉ Set.range (emb (alpha0 hm) (card_alpha0 hm)) := by
      rintro ⟨i, hi⟩
      rw [emb_alpha0] at hi
      apply hx
      rw [← hi]
      exact Nat.lt_of_lt_of_le i.2 le_rfl
    have hx0 : x ≠ 0 := fun h => hx (by rw [h]; simp)
    have hx1 : x ≠ 1 := fun h => hx (by rw [h]; simp)
    have hx2 : x ≠ ⟨2, by omega⟩ := fun h => hx (by rw [h]; simp)
    have hx3 : x ≠ ⟨3, by omega⟩ := fun h => hx (by rw [h]; simp)
    rw [embedPerm_of_not_mem _ _ hxr, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hx1 hx3,
      Equiv.swap_apply_of_ne_of_ne hx0 hx2]

theorem kList_pow_four : ∀ a ∈ kList, a * a * (a * a) = 1 := by decide +kernel

variable {G : Type} [Group G] [Finite G] {P : Set (Subgroup G)}

theorem ker_permHom_le_zSpan (I : AEIdent P (m + 2)) (hm : 3 ≤ m)
    (h8 : ∀ L ∈ P, Nat.card ↥L = 8)
    (hconj : ∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P)
    (hinj : ∀ L ∈ P, ∀ L' ∈ P,
      (L.subgroupOf (pSpan P)).map I.φ = (L'.subgroupOf (pSpan P)).map I.φ → L = L')
    (hker : IsPGroup 2 ↥I.φ.ker) (hWn : (zSpan P).Normal)
    (hW : ∀ a ∈ zSpan P, ∀ b ∈ zSpan P, a * b = b * a ∧ a * a = 1) :
    (permHom I).ker ≤ zSpan P := by
  have hk : 5 ≤ m + 2 := by omega
  have := isPerfect_pSpan I hk h8 hconj hinj
  set ψ := permHom I with hψ
  have hWU : zSpan P ≤ ψ.ker := zSpan_le_ker_permHom I hk h8
  set η : ↥(pSpan P) ⧸ zSpan P →* alternatingGroup (Fin (m + 2)) :=
    QuotientGroup.lift (zSpan P) ψ hWU with hη
  have hηs : Function.Surjective η :=
    QuotientGroup.lift_surjective_of_surjective _ ψ (permHom_surjective I) hWU
  have hker' : η.ker = ψ.ker.map (QuotientGroup.mk' (zSpan P)) := QuotientGroup.ker_lift _ ψ hWU
  have hcen : η.ker ≤ Subgroup.center (↥(pSpan P) ⧸ zSpan P) := by
    intro q hq
    rw [hker'] at hq
    obtain ⟨u, hu, rfl⟩ := hq
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (zSpan P) g
    have h1 := comm_mem_zSpan_of_mem_ker I hk h8 hWn hu x
    rw [← QuotientGroup.eq_one_iff (N := zSpan P)] at h1
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h1
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply]
    calc ((x : ↥(pSpan P) ⧸ zSpan P)) * (u : ↥(pSpan P) ⧸ zSpan P)
        = (x : ↥(pSpan P) ⧸ zSpan P) * u * (x : ↥(pSpan P) ⧸ zSpan P)⁻¹ *
          (u : ↥(pSpan P) ⧸ zSpan P)⁻¹ * u * x := by group
      _ = u * x := by rw [h1, one_mul]
  have hp : IsPGroup 2 ↥η.ker := by
    rw [hker']
    exact (isPGroup_ker_permHom I hk h8 hker hW).map _
  have hm2 : 2 ≤ m := by omega
  obtain ⟨L₀, hL₀, hlab₀⟩ := I.label_surj (alpha0 hm2) (card_alpha0 hm2) true
  obtain ⟨a₂, ha₂, ha₂p⟩ := exists_mem_kQ_perm d₂ (by simp)
  set ι := emb (alpha0 hm2) (card_alpha0 hm2) with hι
  have hkbar : mkQ (m + 2) (embed ι a₂) ∈ (L₀.subgroupOf (pSpan P)).map I.φ := by
    rw [hlab₀]
    exact ⟨embed ι a₂, ⟨a₂, ha₂, rfl⟩, rfl⟩
  obtain ⟨l₀, hl₀, hl₀e⟩ := I.exists_of_mem_map hL₀ hkbar
  set y₀ : ↥(pSpan P) := ⟨l₀, le_pSpan hL₀ hl₀⟩ with hy₀
  have hψy : ((ψ y₀ : alternatingGroup (Fin (m + 2))) : Equiv.Perm (Fin (m + 2))) =
      Equiv.swap (0 : Fin (m + 2)) ⟨2, by omega⟩ * Equiv.swap (1 : Fin (m + 2)) ⟨3, by omega⟩ := by
    rw [hψ, coe_permHom, hl₀e, permQ_mkQ, embed_perm, ha₂p, embedPerm_alpha0_d₂]
  have hsq : y₀ * y₀ ∈ zSpan P := by
    obtain ⟨u, hu, hue⟩ := exists_isUniqueInvolution I hk hL₀ (h8 L₀ hL₀) hlab₀
    have hmem : I.φ (y₀ * y₀) ∈ memBar (alpha0 hm2) (card_alpha0 hm2) true := by
      rw [← hlab₀]
      exact I.mem_map hL₀ (L₀.mul_mem hl₀ hl₀)
    have hsq2 : I.φ (y₀ * y₀) * I.φ (y₀ * y₀) = 1 := by
      have e : I.φ (y₀ * y₀) * I.φ (y₀ * y₀) = mkQ (m + 2) (embed ι (a₂ * a₂ * (a₂ * a₂))) := by
        simp only [map_mul, hl₀e]
      rw [e, kList_pow_four a₂ ha₂, map_one, map_one]
    rcases eq_of_mem_memBar_mul_self hk hmem hsq2 with h1 | h1
    · have : y₀ * y₀ = 1 := by
        apply Subtype.ext
        exact I.injOn hk hL₀ (h8 L₀ hL₀) hlab₀ (L₀.mul_mem hl₀ hl₀) L₀.one_mem
          (h1.trans (map_one I.φ).symm)
      rw [this]
      exact (zSpan P).one_mem
    · have : y₀ * y₀ = ⟨u, le_pSpan hL₀ hu.mem⟩ := by
        apply Subtype.ext
        exact I.injOn hk hL₀ (h8 L₀ hL₀) hlab₀ (L₀.mul_mem hl₀ hl₀) hu.mem (h1.trans hue.symm)
      rw [this]
      exact Subgroup.subset_closure ⟨L₀, hL₀, hu⟩
  have h01 : (⟨0, by omega⟩ : Fin m) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have hd : η (QuotientGroup.mk' (zSpan P) y₀) =
      altThreeCycle (⟨0, by omega⟩ : Fin m) * altThreeCycle (⟨1, by omega⟩ : Fin m) := by
    apply Subtype.ext
    rw [hη, QuotientGroup.mk'_apply, QuotientGroup.lift_mk, hψy, coe_altThreeCycle_mul h01]
    rfl
  have hd2 : QuotientGroup.mk' (zSpan P) y₀ * QuotientGroup.mk' (zSpan P) y₀ = 1 := by
    rw [← map_mul, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hsq
  have hbot := ker_eq_bot_of_lift_mul_self hm η hηs hcen hp hd hd2
  intro u hu
  have h1 : QuotientGroup.mk' (zSpan P) u ∈ η.ker := by
    rw [hker']
    exact ⟨u, hu, rfl⟩
  rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact h1

end CFSG.ClassicalInvolution.Q3.TL4.AECov
