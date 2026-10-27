module

public import CFSG.LocalAnalysis.GL83PartI.I_27_9.Elem
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup

public section

namespace GL83.PiGen

open GL83.CompFam CFSG.Open

variable {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]

theorem card_le_pow_twoLocalRank {E U : Subgroup X} (hE : IsElemAbelian p E) (hU2 : IsPGroup 2 U)
    (hU : U ≠ ⊥) (hEU : E ≤ Subgroup.normalizer (U : Set X)) :
    Nat.card E ≤ p ^ GLATwoLocalRank p X := by
  have hp := (Fact.out : p.Prime)
  obtain ⟨k, hk⟩ := exists_card_eq_pow hE
  have h1 : k ≤ pRank p (Subgroup.normalizer (U : Set X)) :=
    CFSG.SectionRank.le_pRank hp.one_lt hEU hE hk
  have h2 : pRank p (Subgroup.normalizer (U : Set X)) ≤ GLATwoLocalRank p X :=
    le_csSup ⟨pRank p (⊤ : Subgroup X), by
      rintro j ⟨H, -, rfl⟩
      exact CFSG.SectionRank.pRank_mono hp.one_lt le_top⟩ ⟨_, ⟨U, hU, hU2, rfl⟩, rfl⟩
  rw [hk]
  exact Nat.pow_le_pow_right hp.pos (h1.trans h2)

theorem card_conj_family_le {B K : Subgroup X} (hB : IsElemAbelian p B) (hK : IsComponentOf K ⊤)
    (hZ : K ⊓ Subgroup.centralizer (K : Set X) = ⊥) {V E₀ : Subgroup X} (hVK : V ≤ K)
    (hEK : E₀ ≤ K) (hV0 : V ≠ ⊥) (hV2 : IsElemAbelian 2 V) (hEel : IsElemAbelian p E₀)
    (hEV : E₀ ≤ Subgroup.normalizer (V : Set X)) :
    Nat.card (cen B K) * Nat.card E₀ ^ (stab B K).relIndex B ≤ p ^ GLATwoLocalRank p X := by
  classical
  have hF := isFam_conjSet hB hK
  set A := stab B K with hA
  have hAB : A ≤ B := inf_le_left
  let ι := B ⧸ A.subgroupOf B
  have : Fintype ι := Fintype.ofFinite ι
  let b : ι → X := fun i => ((Quotient.out i : B) : X)
  have hbB : ∀ i, b i ∈ B := fun i => (Quotient.out i : B).2
  let Ks : ι → Subgroup X := fun i => cj (b i) K
  let Vs : ι → Subgroup X := fun i => cj (b i) V
  let Es : ι → Subgroup X := fun i => cj (b i) E₀
  have hKmem : ∀ i, Ks i ∈ conjSet B K := fun i => ⟨b i, hbB i, rfl⟩
  have hKK : ∀ i j, i ≠ j → ∀ x ∈ Ks i, ∀ y ∈ Ks j, x * y = y * x := by
    intro i j hij x hx y hy
    have hne : Ks i ≠ Ks j := by
      intro h
      apply hij
      have h1 : cj ((b i)⁻¹ * b j) K = K := by
        rw [cj_mul]
        have : cj (b j) K = cj (b i) K := h.symm
        rw [this, cj_inv_cj]
      have h2 : (b i)⁻¹ * b j ∈ A :=
        mem_stab.2 ⟨B.mul_mem (B.inv_mem (hbB i)) (hbB j), h1⟩
      have h3 : ((Quotient.out i : B)⁻¹ * Quotient.out j : B) ∈ A.subgroupOf B :=
        Subgroup.mem_subgroupOf.2 h2
      have h4 : (QuotientGroup.mk (Quotient.out i : B) : ι) = QuotientGroup.mk (Quotient.out j) :=
        QuotientGroup.eq.2 h3
      rwa [QuotientGroup.out_eq', QuotientGroup.out_eq'] at h4
    exact hF.comm _ (hKmem i) _ (hKmem j) hne x hx y hy
  have hcen : ∀ i, Ks i ⊓ Subgroup.centralizer (Ks i : Set X) = ⊥ := by
    intro i
    refine eq_bot_iff.2 fun x hx => ?_
    obtain ⟨hxK, hxC⟩ := hx
    have hy : (b i)⁻¹ * x * b i ∈ K := mem_cj.1 hxK
    have hyc : (b i)⁻¹ * x * b i ∈ Subgroup.centralizer (K : Set X) := by
      refine Subgroup.mem_centralizer_iff.2 fun z hz => ?_
      have h1 := Subgroup.mem_centralizer_iff.1 hxC (b i * z * (b i)⁻¹) (mul_mem_cj hz)
      have : (b i)⁻¹ * x * b i * z = z * ((b i)⁻¹ * x * b i) := by
        calc (b i)⁻¹ * x * b i * z = (b i)⁻¹ * (x * (b i * z * (b i)⁻¹)) * b i := by group
          _ = (b i)⁻¹ * ((b i * z * (b i)⁻¹) * x) * b i := by rw [← h1]
          _ = z * ((b i)⁻¹ * x * b i) := by group
      exact this.symm
    have : (b i)⁻¹ * x * b i ∈ K ⊓ Subgroup.centralizer (K : Set X) := ⟨hy, hyc⟩
    rw [hZ, Subgroup.mem_bot] at this
    have hx1 : x = 1 := by
      have := congrArg (fun z => b i * z * (b i)⁻¹) this
      simpa [mul_assoc] using this
    exact hx1 ▸ Subgroup.one_mem _
  have hSK : ∀ i, Es i ≤ Ks i := fun i => cj_mono _ hEK
  have hVKs : ∀ i, Vs i ≤ Ks i := fun i => cj_mono _ hVK
  have hC : ∀ i, ∀ c ∈ cen B K, ∀ x ∈ Ks i, c * x = x * c := fun i c hc x hx =>
    hF.cen_comm (mem_conjSet_self B K) hc (hKmem i) x hx
  have hcard := card_sup_iSup Ks Es (cen B K) hSK hcen hKK hC Finset.univ
  have hEcard : ∀ i, Nat.card (Es i) = Nat.card E₀ := fun i =>
    Subgroup.card_map_of_injective (MulAut.conj (b i)).injective
  have hprod : ∏ i ∈ (Finset.univ : Finset ι), Nat.card (Es i) = Nat.card E₀ ^ Nat.card ι := by
    rw [Finset.prod_congr rfl (fun i _ => hEcard i), Finset.prod_const, Finset.card_univ,
      ← Nat.card_eq_fintype_card (α := ι)]
  have hidx : Nat.card ι = A.relIndex B := rfl
  rw [hprod, hidx] at hcard
  have hiSup : ∀ S : ι → Subgroup X, (⨆ i ∈ (Finset.univ : Finset ι), S i) = ⨆ i, S i := by
    intro S
    simp
  have hEel' : ∀ i, IsElemAbelian p (Es i) := fun i =>
    CFSG.SectionRank.isElemAbelian_map hEel (MulAut.conj (b i)).toMonoidHom
  have hVel' : ∀ i, IsElemAbelian 2 (Vs i) := fun i =>
    CFSG.SectionRank.isElemAbelian_map hV2 (MulAut.conj (b i)).toMonoidHom
  have hEjoin : IsElemAbelian p (⨆ i, Es i) :=
    isElemAbelian_iSup Es hEel' fun i j hij x hx y hy => hKK i j hij x (hSK i hx) y (hSK j hy)
  have hVjoin : IsElemAbelian 2 (⨆ i, Vs i) :=
    isElemAbelian_iSup Vs hVel' fun i j hij x hx y hy => hKK i j hij x (hVKs i hx) y (hVKs j hy)
  have hCel : IsElemAbelian p (cen B K) := elem_mono hB inf_le_left
  have hEtot : IsElemAbelian p (cen B K ⊔ ⨆ i ∈ (Finset.univ : Finset ι), Es i) := by
    rw [hiSup]
    refine isElemAbelian_sup hCel hEjoin fun c hc y hy => ?_
    have : (⨆ i, Es i) ≤ Subgroup.centralizer ((cen B K : Subgroup X) : Set X) :=
      iSup_le fun i y hy => Subgroup.mem_centralizer_iff.2 fun c hc => hC i c hc y (hSK i hy)
    exact Subgroup.mem_centralizer_iff.1 (this hy) c hc
  have hUne : (⨆ i ∈ (Finset.univ : Finset ι), Vs i : Subgroup X) ≠ ⊥ := by
    intro h
    have hle : Vs (QuotientGroup.mk 1) ≤ (⨆ i ∈ (Finset.univ : Finset ι), Vs i : Subgroup X) :=
      le_iSup₂_of_le (QuotientGroup.mk 1) (Finset.mem_univ _) le_rfl
    rw [h, le_bot_iff] at hle
    exact hV0 ((Subgroup.map_eq_bot_iff_of_injective V
      (MulAut.conj (b (QuotientGroup.mk 1))).injective).1 hle)
  have hU2 : IsPGroup 2 (⨆ i ∈ (Finset.univ : Finset ι), Vs i : Subgroup X) := by
    rw [hiSup]
    exact isPGroup_of_elem hVjoin
  have hnorm := sup_iSup_le_normalizer Ks (cen B K) Vs Es hVKs hSK
    (fun i => (Subgroup.map_mono hEV).trans
      (Subgroup.le_normalizer_map (H := V) (MulAut.conj (b i)).toMonoidHom)) hKK hC Finset.univ
  have hbound := card_le_pow_twoLocalRank hEtot hU2 hUne hnorm
  rw [hcard] at hbound
  exact hbound

end GL83.PiGen
