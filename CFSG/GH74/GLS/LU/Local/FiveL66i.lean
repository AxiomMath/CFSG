module

public import CFSG.GH74.GLS.LU.Local.FiveL66e

public section

open Subgroup CFSG CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS CFSG.GH74.GLS.LU CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

namespace CFSG.GH74.GLS.LU.Local.Five

section GTorus

variable {G : Type} [Group G] [Finite G] {Gs : Type} [Group Gs] {z t u : G} {K₁ K₂ : Subgroup G}
  {ht : t ∈ Cz z} {hu : u ∈ Cz z} {z' t' u' : Gs} {S' : Sylow 2 Gs} {K₁' K₂' : Subgroup Gs}
  {ψ : ↥(Cz z) ≃* ↥(Cz z')}

@[expose] def GTorus (z u : G) (K₁ K₂ A : Subgroup G) : Prop :=
  (∀ h ∈ A, h * z = z * h ∧ h * u = u * h) ∧ Nonempty (↥A ≃* Z4Z4) ∧
    ∀ h ∈ A, cjL h K₁ = K₁ ∧ cjL h K₂ = K₂

omit [Finite G] in
theorem le_Cz_of_cent {A : Subgroup G} (h : ∀ x ∈ A, x * z = z * x ∧ x * u = u * x) : A ≤ Cz z :=
  fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr (h x hx).1

omit [Finite G] in
theorem ModelPic.pe_comm_z (pic : ModelPic z t u K₁ K₂ ht hu z' S' K₁' K₂' t' u' ψ) {x : G}
    (hx : x ∈ Cz z) (h : x * z = z * x) : pe ψ x hx * z' = z' * pe ψ x hx := by
  have h1 : pe ψ z (mem_Cz_self z) = z' := pic.psi_z
  have h2 := (pe_comm_iff ψ hx (mem_Cz_self z)).mp h
  rwa [h1] at h2

omit [Finite G] in
theorem ModelPic.pe_comm_u (pic : ModelPic z t u K₁ K₂ ht hu z' S' K₁' K₂' t' u' ψ) {x : G}
    (hx : x ∈ Cz z) (h : x * u = u * x) : pe ψ x hx * u' = u' * pe ψ x hx := by
  have h1 : pe ψ u hu = u' := pic.psi_u
  have h2 := (pe_comm_iff ψ hx hu).mp h
  rwa [h1] at h2

omit [Finite G] in
theorem ModelPic.comm_z_of_pe (pic : ModelPic z t u K₁ K₂ ht hu z' S' K₁' K₂' t' u' ψ) {x : G}
    (hx : x ∈ Cz z) (h : pe ψ x hx * z' = z' * pe ψ x hx) : x * z = z * x := by
  have h1 : pe ψ z (mem_Cz_self z) = z' := pic.psi_z
  refine (pe_comm_iff ψ hx (mem_Cz_self z)).mpr ?_
  rwa [h1]

omit [Finite G] in
theorem ModelPic.comm_u_of_pe (pic : ModelPic z t u K₁ K₂ ht hu z' S' K₁' K₂' t' u' ψ) {x : G}
    (hx : x ∈ Cz z) (h : pe ψ x hx * u' = u' * pe ψ x hx) : x * u = u * x := by
  have h1 : pe ψ u hu = u' := pic.psi_u
  refine (pe_comm_iff ψ hx hu).mpr ?_
  rwa [h1]

omit [Finite G] in
theorem ModelPic.pe_cjL_eq (_pic : ModelPic z t u K₁ K₂ ht hu z' S' K₁' K₂' t' u' ψ) {g : G}
    (hg : g ∈ Cz z) {K : Subgroup G} {K' : Subgroup Gs} (hK' : K' ≤ Cz z') (hK : pull ψ K' = K)
    (h : cjL g K = K) : cjL (pe ψ g hg) K' = K' := by
  apply pull_inj ψ (cjL_le_of_mem (ψ ⟨g, hg⟩).2 hK') hK'
  rw [← pull_cjL ψ hg K', hK]
  exact h

omit [Finite G] in
theorem ModelPic.cjL_eq_of_pe (_pic : ModelPic z t u K₁ K₂ ht hu z' S' K₁' K₂' t' u' ψ) {g : G}
    (hg : g ∈ Cz z) {K : Subgroup G} {K' : Subgroup Gs} (hK : pull ψ K' = K)
    (h : cjL (pe ψ g hg) K' = K') : cjL g K = K := by
  rw [← hK, pull_cjL ψ hg K', h]

omit [Finite G] in
theorem ModelPic.isTorus_push (pic : ModelPic z t u K₁ K₂ ht hu z' S' K₁' K₂' t' u' ψ)
    {A : Subgroup G} (hA : GTorus z u K₁ K₂ A) : IsTorus z' u' K₁' K₂' (push ψ A) := by
  have hAle : A ≤ Cz z := le_Cz_of_cent hA.1
  refine ⟨?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨x, hxC, hxA, rfl⟩ := exists_pe_of_mem_push ψ hy
    obtain ⟨c1, c2⟩ := hA.1 x hxA
    exact mem_PP.mpr ⟨pic.pe_comm_z hxC c1, pic.pe_comm_u hxC c2⟩
  · exact ⟨((pullEquiv ψ (push_le ψ A)).symm.trans
      (MulEquiv.subgroupCongr (pull_push ψ hAle))).trans hA.2.1.some⟩
  · intro y hy
    obtain ⟨x, hxC, hxA, rfl⟩ := exists_pe_of_mem_push ψ hy
    obtain ⟨n1, n2⟩ := hA.2.2 x hxA
    exact ⟨pic.pe_cjL_eq hxC pic.K₁'_le pic.K₁_eq n1, pic.pe_cjL_eq hxC pic.K₂'_le pic.K₂_eq n2⟩

omit [Finite G] in
theorem ModelPic.torus_unique_G (pic : ModelPic z t u K₁ K₂ ht hu z' S' K₁' K₂' t' u' ψ)
    {A B : Subgroup G} (hA : GTorus z u K₁ K₂ A) (hB : GTorus z u K₁ K₂ B) : A = B := by
  have h := pic.facts.torus_unique _ _ (pic.isTorus_push hA) (pic.isTorus_push hB)
  have h2 := congrArg (pull ψ) h
  rwa [pull_push ψ (le_Cz_of_cent hA.1), pull_push ψ (le_Cz_of_cent hB.1)] at h2

theorem ModelPic.normalizes_of_sylow (pic : ModelPic z t u K₁ K₂ ht hu z' S' K₁' K₂' t' u' ψ)
    (hC : Nat.card ↥(Cz z) = 28800) {A : Subgroup G}
    (hAc : ∀ h ∈ A, h * z = z * h ∧ h * u = u * h) (hAiso : Nonempty (↥A ≃* Z4Z4))
    {R : Subgroup G} (hR : IsSylowIn 5 R (Cz z)) (hAR : ∀ h ∈ A, cjL h R = R) :
    ∀ h ∈ A, cjL h K₁ = K₁ ∧ cjL h K₂ = K₂ := by
  have hAle : A ≤ Cz z := le_Cz_of_cent hAc
  have hRle : R ≤ Cz z := hR.1
  have hcR : Nat.card ↥R = 25 := card_of_isSylowIn_five hR hC
  have hcR' : Nat.card ↥(push ψ R) = 25 :=
    (card_pull ψ (push_le ψ R)).symm.trans (by rw [pull_push ψ hRle]; exact hcR)
  have hCz'card : Nat.card ↥(Cz z') = 28800 := by
    rw [← hC]; exact (Nat.card_congr ψ.toEquiv).symm
  have hR'syl : IsSylowIn 5 (push ψ R) (Cz z') := isSylowIn_five_of_card (push_le ψ R) hcR' hCz'card
  have hinv : ∀ y ∈ push ψ A, cjL y (push ψ R) = push ψ R := push_hinv ψ hRle hAR
  have hiso' : Nonempty (↥(push ψ A) ≃* Z4Z4) :=
    ⟨((pullEquiv ψ (push_le ψ A)).symm.trans
      (MulEquiv.subgroupCongr (pull_push ψ hAle))).trans hAiso.some⟩
  have hcomm' : ∀ h ∈ push ψ A, h * z' = z' * h ∧ h * u' = u' * h := by
    intro y hy
    obtain ⟨x, hxC, hxA, rfl⟩ := exists_pe_of_mem_push ψ hy
    obtain ⟨c1, c2⟩ := hAc x hxA
    exact ⟨pic.pe_comm_z hxC c1, pic.pe_comm_u hxC c2⟩
  have key := pic.facts.sylow_torus (push ψ A) hcomm' hiso' ⟨push ψ R, hR'syl, hinv⟩
  intro x hxA
  have hxC : x ∈ Cz z := hAle hxA
  obtain ⟨k1, k2⟩ := key (pe ψ x hxC) (pe_mem_push ψ hxA hxC)
  exact ⟨pic.cjL_eq_of_pe hxC pic.K₁_eq k1, pic.cjL_eq_of_pe hxC pic.K₂_eq k2⟩

end GTorus

section NormH

variable {G : Type} [Group G] [Finite G] {p f : ℕ} {z : G} {S : Sylow 2 G} {K₁ K₂ H : Subgroup G}
  {t u w₁ : G} {Gs : Type} [Group Gs] {z' t' u' : Gs} {S' : Sylow 2 Gs} {K₁' K₂' : Subgroup Gs}
  {ht : t ∈ Cz z} {hu : u ∈ Cz z} {ψ : ↥(Cz z) ≃* ↥(Cz z')}

omit [Finite G] in
theorem conj_mem_UU_of_mem_NN {n : G} (hn : n ∈ NN z u) {a : G} (ha : a ∈ UU z u) :
    n⁻¹ * a * n ∈ UU z u := by
  have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) a).mp ha
  simpa using h

omit [Finite G] in
theorem cjL_torus_basic (b66 : Five66W z t u K₁ K₂ H w₁) {n : G} (hn : n ∈ NN z u) :
    (∀ a ∈ cjL n H, a * z = z * a ∧ a * u = u * a) ∧ Nonempty (↥(cjL n H) ≃* Z4Z4) := by
  have hzU : z ∈ UU z u := Subgroup.mem_sup_left (Subgroup.mem_zpowers z)
  have huU : u ∈ UU z u := Subgroup.mem_sup_right (Subgroup.mem_zpowers u)
  have hHP : ∀ h ∈ H, ∀ a ∈ UU z u, h * a = a * h := fun h hh a ha =>
    (Subgroup.mem_centralizer_iff.mp (mem_PP.mpr (b66.H_cent h hh)) a ha).symm
  refine ⟨?_, ?_⟩
  · intro a ha
    have ha' : n⁻¹ * a * n ∈ H := mem_cjL.mp ha
    set h := n⁻¹ * a * n with hh
    have hea : a = n * h * n⁻¹ := by rw [hh]; group
    have hz1 := conj_mem_UU_of_mem_NN hn hzU
    have hu1 := conj_mem_UU_of_mem_NN hn huU
    have c1 := hHP h ha' _ hz1
    have c2 := hHP h ha' _ hu1
    constructor
    · rw [hea]
      calc n * h * n⁻¹ * z = n * (h * (n⁻¹ * z * n)) * n⁻¹ := by group
        _ = n * ((n⁻¹ * z * n) * h) * n⁻¹ := by rw [c1]
        _ = z * (n * h * n⁻¹) := by group
    · rw [hea]
      calc n * h * n⁻¹ * u = n * (h * (n⁻¹ * u * n)) * n⁻¹ := by group
        _ = n * ((n⁻¹ * u * n) * h) * n⁻¹ := by rw [c2]
        _ = u * (n * h * n⁻¹) := by group
  · exact ⟨(Subgroup.equivMapOfInjective H (MulAut.conj n).toMonoidHom
      (MulAut.conj n).injective).symm.trans b66.H_iso.some⟩

omit [Finite G] in
theorem GTorus.of_five66W (b66 : Five66W z t u K₁ K₂ H w₁) : GTorus z u K₁ K₂ H :=
  ⟨b66.H_cent, b66.H_iso, b66.H_normK⟩

omit [Finite G] in
theorem ModelPic.normH_of_normK (pic : ModelPic z t u K₁ K₂ ht hu z' S' K₁' K₂' t' u' ψ)
    (b66 : Five66W z t u K₁ K₂ H w₁) {n : G} (hn : n ∈ NN z u) (h1 : cjL n K₁ = K₁)
    (h2 : cjL n K₂ = K₂) : cjL n H = H := by
  obtain ⟨hc, hi⟩ := cjL_torus_basic b66 hn
  have hn1 : cjL n⁻¹ K₁ = K₁ := by
    have := congrArg (cjL n⁻¹) h1
    rw [cjL_cjL, inv_mul_cancel, cjL_one] at this
    exact this.symm
  have hn2 : cjL n⁻¹ K₂ = K₂ := by
    have := congrArg (cjL n⁻¹) h2
    rw [cjL_cjL, inv_mul_cancel, cjL_one] at this
    exact this.symm
  have hA : GTorus z u K₁ K₂ (cjL n H) := by
    refine ⟨hc, hi, ?_⟩
    intro a ha
    have ha' : n⁻¹ * a * n ∈ H := mem_cjL.mp ha
    obtain ⟨k1, k2⟩ := b66.H_normK _ ha'
    have e : a = n * (n⁻¹ * a * n) * n⁻¹ := by group
    have key : ∀ K : Subgroup G, cjL n⁻¹ K = K → cjL (n⁻¹ * a * n) K = K → cjL a K = K := by
      intro K hK hK'
      calc cjL a K = cjL (n * (n⁻¹ * a * n) * n⁻¹) K := by rw [← e]
        _ = cjL n (cjL (n⁻¹ * a * n) (cjL n⁻¹ K)) := by rw [cjL_cjL, cjL_cjL]
        _ = cjL n (cjL (n⁻¹ * a * n) K) := by rw [hK]
        _ = cjL n K := by rw [hK']
        _ = K := by
          have := congrArg (cjL n) hK.symm
          rw [cjL_cjL, mul_inv_cancel, cjL_one] at this
          exact this
    exact ⟨key K₁ hn1 k1, key K₂ hn2 k2⟩
  exact pic.torus_unique_G hA (GTorus.of_five66W b66)

theorem ModelPic.normH_aux (pic : ModelPic z t u K₁ K₂ ht hu z' S' K₁' K₂' t' u' ψ)
    (hC : Nat.card ↥(Cz z) = 28800) (b66 : Five66W z t u K₁ K₂ H w₁) {n : G} (hn : n ∈ NN z u)
    {R₀ : Subgroup G} (hR₀le : R₀ ≤ centralizer ({n⁻¹ * z * n} : Set G))
    (hR₀c : Nat.card ↥R₀ = 25) (hR₀H : ∀ h ∈ H, cjL h R₀ = R₀) : cjL n H = H := by
  obtain ⟨hc, hi⟩ := cjL_torus_basic b66 hn
  have hRle : cjL n R₀ ≤ Cz z := by
    intro y hy
    have hy' : n⁻¹ * y * n ∈ R₀ := mem_cjL.mp hy
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hR₀le hy')
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    calc y * z = n * ((n⁻¹ * y * n) * (n⁻¹ * z * n)) * n⁻¹ := by group
      _ = n * ((n⁻¹ * z * n) * (n⁻¹ * y * n)) * n⁻¹ := by rw [h1]
      _ = z * y := by group
  have hRc : Nat.card ↥(cjL n R₀) = 25 := by rw [card_cjL]; exact hR₀c
  have hCz' : Nat.card ↥(Cz z) = 28800 := hC
  have hsyl : IsSylowIn 5 (cjL n R₀) (Cz z) := isSylowIn_five_of_card hRle hRc hCz'
  have hinv : ∀ a ∈ cjL n H, cjL a (cjL n R₀) = cjL n R₀ := by
    intro a ha
    have ha' : n⁻¹ * a * n ∈ H := mem_cjL.mp ha
    have e : a * n = n * (n⁻¹ * a * n) := by group
    rw [cjL_cjL, e, ← cjL_cjL, hR₀H _ ha']
  have hnorm := pic.normalizes_of_sylow hC hc hi hsyl hinv
  exact pic.torus_unique_G ⟨hc, hi, hnorm⟩ (GTorus.of_five66W b66)

end NormH

end CFSG.GH74.GLS.LU.Local.Five
