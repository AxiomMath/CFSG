module

public import CFSG.GH74.GLS.LU.Local.FiveL66i

public section

open Subgroup CFSG CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS CFSG.GH74.GLS.LU CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

namespace CFSG.GH74.GLS.LU.Local.Five

section PPFacts

variable {G : Type} [Group G] [Finite G] {p f : ℕ} {z : G} {S : Sylow 2 G} {K₁ K₂ H : Subgroup G}
  {t u w₁ : G} {Gs : Type} [Group Gs] {z' t' u' : Gs} {S' : Sylow 2 Gs} {K₁' K₂' : Subgroup Gs}
  {ht : t ∈ Cz z} {hu : u ∈ Cz z} {ψ : ↥(Cz z) ≃* ↥(Cz z')}

omit [Finite G] in
theorem PP_le_Cz : PP z u ≤ Cz z := le_Cz_of_cent (fun _ hx => mem_PP.mp hx)

omit [Finite G] in
theorem ModelPic.card_PP (pic : ModelPic z t u K₁ K₂ ht hu z' S' K₁' K₂' t' u' ψ) :
    Nat.card ↥(PP z u) = 64 := by
  have hle : PP z u ≤ Cz z := PP_le_Cz
  have h : push ψ (PP z u) = PP z' u' := by
    apply le_antisymm
    · intro y hy
      obtain ⟨x, hxC, hxP, rfl⟩ := exists_pe_of_mem_push ψ hy
      obtain ⟨c1, c2⟩ := mem_PP.mp hxP
      exact mem_PP.mpr ⟨pic.pe_comm_z hxC c1, pic.pe_comm_u hxC c2⟩
    · intro y hy
      obtain ⟨c1, c2⟩ := mem_PP.mp hy
      have hyC : y ∈ Cz z' := Subgroup.mem_centralizer_singleton_iff.mpr c1
      obtain ⟨x, hxC, hψ⟩ := exists_psi_eq ψ hyC
      have h1 : pe ψ x hxC = y := hψ
      have hx : x ∈ PP z u := by
        refine mem_PP.mpr ⟨pic.comm_z_of_pe hxC ?_, pic.comm_u_of_pe hxC ?_⟩
        · rw [h1]; exact c1
        · rw [h1]; exact c2
      rw [← h1]
      exact pe_mem_push ψ hx hxC
  have hc := card_pull ψ (push_le ψ (PP z u))
  rw [pull_push ψ hle, h] at hc
  rw [hc]
  exact pic.facts.P_card

omit [Finite G] in
theorem ModelPic.PP_facts (pic : ModelPic z t u K₁ K₂ ht hu z' S' K₁' K₂' t' u' ψ)
    (b66 : Five66W z t u K₁ K₂ H w₁) :
    (∀ p ∈ PP z u, cjL p H = H) ∧ (∀ p ∈ PP z u, p * p ∈ H) := by
  have hK₁le : K₁ ≤ Cz z := by rw [← pic.K₁_eq]; exact pull_le ψ K₁'
  have hw₁C : w₁ ∈ Cz z := hK₁le b66.w₁_mem
  obtain ⟨hT, -, -, -⟩ := pic.torus_of_five66W b66 hw₁C
  obtain ⟨-, -, hnorm, hsq⟩ := pic.facts.torus_facts _ hT
  have hHle : H ≤ Cz z := le_Cz_of_cent b66.H_cent
  have hpull : pull ψ (push ψ H) = H := pull_push ψ hHle
  have hP' : ∀ q (hq : q ∈ PP z u), pe ψ q (PP_le_Cz hq) ∈ PP z' u' := by
    intro q hq
    obtain ⟨c1, c2⟩ := mem_PP.mp hq
    exact mem_PP.mpr ⟨pic.pe_comm_z _ c1, pic.pe_comm_u _ c2⟩
  refine ⟨fun q hq => ?_, fun q hq => ?_⟩
  · exact pic.cjL_eq_of_pe (PP_le_Cz hq) hpull (hnorm _ (hP' q hq))
  · have hqC := PP_le_Cz hq
    have h1 := hsq _ (hP' q hq)
    have h2 : pe ψ (q * q) ((Cz z).mul_mem hqC hqC) ∈ push ψ H := by
      rw [pe_mul ψ hqC hqC]; exact h1
    have h3 : q * q ∈ pull ψ (push ψ H) := (mem_pull ψ _ ((Cz z).mul_mem hqC hqC)).mpr h2
    rwa [hpull] at h3

end PPFacts

section CommP

variable {G : Type} [Group G]

theorem comm_mem_of_sq_mem {P H : Subgroup G} (hnorm : ∀ p ∈ P, cjL p H = H)
    (hsq : ∀ p ∈ P, p * p ∈ H) : ∀ a ∈ P, ∀ b ∈ P, a * b * a⁻¹ * b⁻¹ ∈ H := by
  intro a ha b hb
  have hconj : ∀ q ∈ P, ∀ h ∈ H, q⁻¹ * h * q ∈ H := by
    intro q hq h hh
    have h1 : q⁻¹ * h * q⁻¹⁻¹ ∈ cjL q⁻¹ H := mem_cjL_self hh
    rw [hnorm q⁻¹ (P.inv_mem hq)] at h1
    simpa using h1
  have e : a * b * a⁻¹ * b⁻¹ = ((a * b) * (a * b)) * (b⁻¹ * (a * a)⁻¹ * b) * (b * b)⁻¹ := by group
  rw [e]
  exact H.mul_mem (H.mul_mem (hsq _ (P.mul_mem ha hb)) (hconj b hb _ (H.inv_mem (hsq a ha))))
    (H.inv_mem (hsq b hb))

end CommP

section Omega1

variable {G : Type} [Group G] [Finite G] {z u : G}

theorem z4_involutions_card : (Finset.univ.filter (fun x : Z4Z4 => x * x = 1)).card = 4 := by decide

omit [Finite G] in
theorem sq_eq_one_mem_UU (hz2 : z * z = 1) (hu2 : u * u = 1) (hzu : z * u = u * z) (hz1 : z ≠ 1)
    (hu1 : u ≠ 1) (huz : u ≠ z) {H : Subgroup G} (hzH : z ∈ H) (huH : u ∈ H)
    (hiso : Nonempty (↥H ≃* Z4Z4)) : ∀ y ∈ H, y * y = 1 → y ∈ UU z u := by
  classical
  obtain ⟨f⟩ := hiso
  have hzuH : z * u ∈ H := H.mul_mem hzH huH
  let F : Finset Z4Z4 := Finset.univ.filter (fun x : Z4Z4 => x * x = 1)
  have hF : F.card = 4 := z4_involutions_card
  have hsqf : ∀ (a : G) (ha : a ∈ H), a * a = 1 → f ⟨a, ha⟩ * f ⟨a, ha⟩ = 1 := by
    intro a ha h
    have : (⟨a, ha⟩ : ↥H) * ⟨a, ha⟩ = 1 := Subtype.ext h
    rw [← map_mul, this, map_one]
  have hzu2 : (z * u) * (z * u) = 1 := by
    calc (z * u) * (z * u) = z * (u * z) * u := by group
      _ = z * (z * u) * u := by rw [hzu]
      _ = (z * z) * (u * u) := by group
      _ = 1 := by rw [hz2, hu2, one_mul]
  have hzu1 : z * u ≠ 1 := fun h => huz (mul_left_cancel (h.trans hz2.symm))
  have hzzu : z ≠ z * u := fun h => hu1 (by
    have := congrArg (z⁻¹ * ·) h
    simpa using this.symm)
  have huzu : u ≠ z * u := fun h => hz1 (by
    have := congrArg (· * u⁻¹) h
    simpa using this.symm)
  have hinj : ∀ (a b : G) (ha : a ∈ H) (hb : b ∈ H), f ⟨a, ha⟩ = f ⟨b, hb⟩ → a = b := fun a b ha hb h =>
    congrArg Subtype.val (f.injective h)
  have hf1 : f ⟨1, H.one_mem⟩ = 1 := by
    have : (⟨1, H.one_mem⟩ : ↥H) = 1 := rfl
    rw [this, map_one]
  let S : Finset Z4Z4 := {1, f ⟨z, hzH⟩, f ⟨u, huH⟩, f ⟨z * u, hzuH⟩}
  have h1z : (1 : Z4Z4) ≠ f ⟨z, hzH⟩ := fun h => hz1 (by
    have := hinj 1 z H.one_mem hzH (hf1.trans h)
    exact this.symm)
  have h1u : (1 : Z4Z4) ≠ f ⟨u, huH⟩ := fun h => hu1 (by
    have := hinj 1 u H.one_mem huH (hf1.trans h)
    exact this.symm)
  have h1zu : (1 : Z4Z4) ≠ f ⟨z * u, hzuH⟩ := fun h => hzu1 (by
    have := hinj 1 (z * u) H.one_mem hzuH (hf1.trans h)
    exact this.symm)
  have hzu' : f ⟨z, hzH⟩ ≠ f ⟨u, huH⟩ := fun h => huz (hinj z u hzH huH h).symm
  have hzzu' : f ⟨z, hzH⟩ ≠ f ⟨z * u, hzuH⟩ := fun h => hzzu (hinj z (z * u) hzH hzuH h)
  have huzu' : f ⟨u, huH⟩ ≠ f ⟨z * u, hzuH⟩ := fun h => huzu (hinj u (z * u) huH hzuH h)
  have hS : S.card = 4 := by
    have a1 : f ⟨u, huH⟩ ∉ ({f ⟨z * u, hzuH⟩} : Finset Z4Z4) := by
      simpa using huzu'
    have a2 : f ⟨z, hzH⟩ ∉ ({f ⟨u, huH⟩, f ⟨z * u, hzuH⟩} : Finset Z4Z4) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hzu', hzzu'⟩
    have a3 : (1 : Z4Z4) ∉ ({f ⟨z, hzH⟩, f ⟨u, huH⟩, f ⟨z * u, hzuH⟩} : Finset Z4Z4) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨h1z, h1u, h1zu⟩
    show ({1, f ⟨z, hzH⟩, f ⟨u, huH⟩, f ⟨z * u, hzuH⟩} : Finset Z4Z4).card = 4
    rw [Finset.card_insert_of_notMem a3, Finset.card_insert_of_notMem a2,
      Finset.card_insert_of_notMem a1, Finset.card_singleton]
  have hSF : S ⊆ F := by
    intro a ha
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at ha
    simp only [F, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases ha with rfl | rfl | rfl | rfl
    · simp
    · exact hsqf z hzH hz2
    · exact hsqf u huH hu2
    · exact hsqf (z * u) hzuH hzu2
  have hSeq : S = F := Finset.eq_of_subset_of_card_le hSF (by rw [hF, hS])
  intro y hy hy2
  have hyF : f ⟨y, hy⟩ ∈ F := by
    simp only [F, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hsqf y hy hy2
  rw [← hSeq] at hyF
  simp only [S, Finset.mem_insert, Finset.mem_singleton] at hyF
  rcases hyF with h | h | h | h
  · have : y = 1 := hinj y 1 hy H.one_mem (h.trans hf1.symm)
    rw [this]; exact (UU z u).one_mem
  · have : y = z := hinj y z hy hzH h
    rw [this]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers z)
  · have : y = u := hinj y u hy huH h
    rw [this]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers u)
  · have : y = z * u := hinj y (z * u) hy hzuH h
    rw [this]
    exact (UU z u).mul_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers z))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers u))

end Omega1

end CFSG.GH74.GLS.LU.Local.Five
