module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7RRk
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G]

private lemma mem_sup_zpowers {S : Subgroup G} {t : G} (ht : t ^ 2 = 1)
    (hcomm : ∀ x ∈ S, x * t = t * x) {x : G} (hx : x ∈ S ⊔ Subgroup.zpowers t) :
    x ∈ S ∨ x * t⁻¹ ∈ S := by
  have ht2 : t * t = 1 := by simpa [pow_two] using ht
  have comm_inv : ∀ z ∈ S, t⁻¹ * z = z * t⁻¹ := by
    intro z hz
    have h : t⁻¹ * z * t = z := by
      rw [mul_assoc, hcomm z hz, ← mul_assoc, inv_mul_cancel, one_mul]
    have h2 : z * t⁻¹ = t⁻¹ * z := by
      calc z * t⁻¹ = (t⁻¹ * z * t) * t⁻¹ := by rw [h]
        _ = t⁻¹ * z := by group
    exact h2.symm
  let K : Subgroup G :=
    { carrier := {x : G | x ∈ S ∨ x * t⁻¹ ∈ S}
      one_mem' := Or.inl S.one_mem
      mul_mem' := by
        intro x y hx hy
        rcases hx with hxS | hxt
        · rcases hy with hyS | hyt
          · exact Or.inl (S.mul_mem hxS hyS)
          · exact Or.inr (by rw [mul_assoc]; exact S.mul_mem hxS hyt)
        · rcases hy with hyS | hyt
          · exact Or.inr (by
              rw [mul_assoc, ← comm_inv y hyS, ← mul_assoc]
              exact S.mul_mem hxt hyS)
          · refine Or.inl ?_
            have hxb : x = (x * t⁻¹) * t := by group
            have hyb : y = (y * t⁻¹) * t := by group
            have hc : t * (y * t⁻¹) = (y * t⁻¹) * t := (hcomm (y * t⁻¹) hyt).symm
            have heq : (x * t⁻¹) * t * ((y * t⁻¹) * t) = (x * t⁻¹) * (y * t⁻¹) := by
              calc (x * t⁻¹) * t * ((y * t⁻¹) * t)
                  = (x * t⁻¹) * (t * (y * t⁻¹)) * t := by group
                _ = (x * t⁻¹) * ((y * t⁻¹) * t) * t := by rw [hc]
                _ = (x * t⁻¹) * (y * t⁻¹) * (t * t) := by group
                _ = (x * t⁻¹) * (y * t⁻¹) := by rw [ht2, mul_one]
            rw [hxb, hyb, heq]
            exact S.mul_mem hxt hyt
      inv_mem' := by
        intro x hx
        rcases hx with hxS | hxt
        · exact Or.inl (S.inv_mem hxS)
        · refine Or.inr ?_
          have hxa : x = (x * t⁻¹) * t := by group
          have hc : t⁻¹ * (x * t⁻¹)⁻¹ = (x * t⁻¹)⁻¹ * t⁻¹ :=
            comm_inv _ (S.inv_mem hxt)
          have heq : ((x * t⁻¹) * t)⁻¹ * t⁻¹ = (x * t⁻¹)⁻¹ := by
            calc ((x * t⁻¹) * t)⁻¹ * t⁻¹
                = t⁻¹ * (x * t⁻¹)⁻¹ * t⁻¹ := by group
              _ = (x * t⁻¹)⁻¹ * t⁻¹ * t⁻¹ := by rw [hc]
              _ = (x * t⁻¹)⁻¹ * (t⁻¹ * t⁻¹) := by group
              _ = (x * t⁻¹)⁻¹ := by
                    rw [show t⁻¹ * t⁻¹ = 1 by rw [← mul_inv_rev, ht2, inv_one], mul_one]
          rw [hxa, heq]
          exact S.inv_mem hxt }
  have hKS : S ≤ K := fun x hx => Or.inl hx
  have hKt : Subgroup.zpowers t ≤ K := by
    rw [Subgroup.zpowers_le]
    exact Or.inr (by rw [mul_inv_cancel]; exact S.one_mem)
  exact sup_le hKS hKt hx

private lemma relIndex_sup_zpowers_le_two {S : Subgroup G} {t : G} (ht : t ^ 2 = 1)
    (hcomm : ∀ x ∈ S, x * t = t * x) :
    S.relIndex (S ⊔ Subgroup.zpowers t) ≤ 2 := by
  have ht2 : t * t = 1 := by simpa [pow_two] using ht
  by_cases htS : t ∈ S
  · have hle : S ⊔ Subgroup.zpowers t ≤ S := sup_le le_rfl (Subgroup.zpowers_le.mpr htS)
    rw [Subgroup.relIndex_eq_one.mpr hle]
    norm_num
  · have h2 : S.relIndex (S ⊔ Subgroup.zpowers t) = 2 := by
      refine (Subgroup.relIndex_eq_two_iff' (H := S)
        (K := S ⊔ Subgroup.zpowers t)).mpr
        ⟨t, Subgroup.mem_sup_right (Subgroup.mem_zpowers t), ?_⟩
      intro b hb
      rcases mem_sup_zpowers ht hcomm hb with hbS | hbt
      · refine Or.inr ⟨hbS, ?_⟩
        intro htb
        exact htS (by
          have h : t = (t * b) * b⁻¹ := by group
          rw [h]
          exact S.mul_mem htb (S.inv_mem hbS))
      · have hb_notS : b ∉ S := by
          intro hbS'
          have htinv : t⁻¹ ∈ S := by
            simpa [mul_assoc] using S.mul_mem (S.inv_mem hbS') hbt
          exact htS (by simpa using S.inv_mem htinv)
        refine Or.inl ⟨?_, hb_notS⟩
        have hb_eq : b = (b * t⁻¹) * t := by group
        have hc : t * (b * t⁻¹) = (b * t⁻¹) * t := (hcomm (b * t⁻¹) hbt).symm
        have heq : t * b = b * t⁻¹ := by
          calc t * b = t * ((b * t⁻¹) * t) := by rw [← hb_eq]
            _ = (t * (b * t⁻¹)) * t := by group
            _ = ((b * t⁻¹) * t) * t := by rw [hc]
            _ = (b * t⁻¹) * (t * t) := by group
            _ = b * t⁻¹ := by rw [ht2, mul_one]
        rw [heq]
        exact hbt
    exact h2.le

private lemma card_le_sixteen_of_le_sup {S F : Subgroup G} {t : G} (hS : RankFacts S)
    (ht : t ^ 2 = 1) (hcomm : ∀ x ∈ S, x * t = t * x)
    (hF : F ≤ S ⊔ Subgroup.zpowers t) (hFab : IsElemAbelian 2 F) : Nat.card F ≤ 16 := by
  have hrel : S.relIndex F ≤ 2 := by
    haveI : S.IsFiniteRelIndex (S ⊔ Subgroup.zpowers t) :=
      Subgroup.isFiniteRelIndex_of_finiteIndex
    exact (Subgroup.relIndex_le_of_le_right hF Subgroup.relIndex_ne_zero).trans
      (relIndex_sup_zpowers_le_two ht hcomm)
  have hmul := Subgroup.relIndex_mul_card (H := S) (K := F)
  have hcardSF : Nat.card ↥(S ⊓ F) ≤ 8 :=
    hS.bound (S ⊓ F) inf_le_left (hFab.mono inf_le_right)
  calc Nat.card F = S.relIndex F * Nat.card ↥(S ⊓ F) := hmul.symm
    _ ≤ 2 * Nat.card ↥(S ⊓ F) := Nat.mul_le_mul_right _ hrel
    _ ≤ 2 * 8 := Nat.mul_le_mul_left _ hcardSF
    _ = 16 := by norm_num

theorem cent_elem_bound {S T : Subgroup G} {t : G} (hS : RankFacts S) (ht : t ^ 2 = 1)
    (hTS : T = S ⊔ zpowers t) (hcomm : ∀ x ∈ S, x * t = t * x)
    (hT : IsSylowIn 2 (centralizer ({t} : Set G)) T) :
    ∀ E : Subgroup G, E ≤ centralizer ({t} : Set G) → IsElemAbelian 2 E → Nat.card E ≤ 16 := by
  intro E hEH hEab
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H : Subgroup G := centralizer ({t} : Set G) with hHdef
  have hT' : IsSylowIn 2 H T := by rw [hHdef]; exact hT
  have hH_E : E ≤ H := by rw [hHdef]; exact hEH
  have hTsub_pg : IsPGroup 2 (T.subgroupOf H) := hT'.2.1.comap_subtype
  have hTsub_ne : ¬ 2 ∣ (T.subgroupOf H).index := by
    simpa only [Subgroup.relIndex] using hT'.2.2
  let P : Sylow 2 ↥H := hTsub_pg.toSylow hTsub_ne
  have hPcoe : (P : Subgroup ↥H) = T.subgroupOf H := rfl
  haveI : Finite (Sylow 2 ↥H) := Sylow.finite_of_finiteIndex P
  have hEsub_pg : IsPGroup 2 (E.subgroupOf H) := (hEab.subgroupOf H).isPGroup
  obtain ⟨Q, hQ⟩ := hEsub_pg.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (M := ↥H) P Q
  set F : Subgroup G := conjSub ((c : G)⁻¹) E with hFdef
  have hFT : F ≤ T := by
    intro x hx
    rw [hFdef, conjSub, Subgroup.mem_map] at hx
    obtain ⟨e, he, rfl⟩ := hx
    have heH : e ∈ H := hH_E he
    have heQ : (⟨e, heH⟩ : ↥H) ∈ (Q : Subgroup ↥H) :=
      hQ (Subgroup.mem_subgroupOf.mpr he)
    have hmem : (⟨e, heH⟩ : ↥H) ∈ ((c • P : Sylow 2 ↥H) : Subgroup ↥H) := by
      rw [hc]; exact heQ
    rw [Sylow.coe_subgroup_smul] at hmem
    have h2 := Subgroup.mem_pointwise_smul_iff_inv_smul_mem.mp hmem
    rw [hPcoe] at h2
    have h3 : (((MulAut.conj c)⁻¹ • (⟨e, heH⟩ : ↥H) : ↥H) : G) =
        (c : G)⁻¹ * e * (c : G) := by
      rw [MulAut.smul_def, MulAut.conj_inv_apply]
      simp
    have h4 : (c : G)⁻¹ * e * (c : G) ∈ T := h3 ▸ Subgroup.mem_subgroupOf.mp h2
    simpa [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h4
  have hFab : IsElemAbelian 2 F := by
    rw [hFdef]
    exact hEab.map (MulAut.conj ((c : G)⁻¹)).toMonoidHom
  have hFcard : Nat.card F = Nat.card E := by
    rw [hFdef, conjSub]
    exact Subgroup.card_map_of_injective (MulAut.conj ((c : G)⁻¹)).injective
  calc Nat.card E = Nat.card F := hFcard.symm
    _ ≤ 16 := card_le_sixteen_of_le_sup hS ht hcomm (hTS ▸ hFT) hFab

end CFSG.OddStandard.HigherRank.YamadaG23
