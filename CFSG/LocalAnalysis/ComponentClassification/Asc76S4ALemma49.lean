module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76S4AFacts

public section

namespace CFSG.ComponentClassification.Asc76.Sec4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {S : Subgroup G}

omit [Finite G] in
theorem IsZOf.rightConjugate {T : Subgroup G} {z : G} (hz : IsZOf T z) (g : G) :
    IsZOf (AschbacherTightEmbedding.rightConjugate T g) (g⁻¹ * z * g) := by
  obtain ⟨V, hV, hzV, hz1, hzz⟩ := hz
  refine ⟨_, hV.rightConjugate g, ?_, ?_, ?_⟩
  · rw [mem_rightConjugate_iff]
    simpa [mul_assoc] using hzV
  · intro h
    apply hz1
    calc z = g * (g⁻¹ * z * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group
  · calc g⁻¹ * z * g * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g := by group
      _ = 1 := by rw [hzz]; group

omit [Finite G] in
theorem IsBarOf.rightConjugate {W T : Subgroup G} {d : NBar W} (hd : IsBarOf W T d)
    (g : normalizer (W : Set G)) :
    IsBarOf W (AschbacherTightEmbedding.rightConjugate T g) ((g : NBar W)⁻¹ * d * g) := by
  obtain ⟨V, hV, t, htT, htV, rfl⟩ := hd
  refine ⟨_, hV.rightConjugate g, g⁻¹ * t * g, ?_, ?_, ?_⟩
  · rw [mem_rightConjugate_iff]
    simpa [mul_assoc] using htT
  · rw [mem_rightConjugate_iff]
    simpa [mul_assoc] using htV
  · rfl

theorem DBar.mul_self (hΩ : Assumption41 Ω) (hS : IsSylowOf 2 S ⊤)
    {d : NBar (sec4W Ω S)} (hd : d ∈ DBar Ω (sec4W Ω S)) : d * d = 1 := by
  rw [← pow_two, ← DBar.orderOf_eq_two hΩ hS hd, pow_orderOf_eq_one]

theorem lemma49 :
    ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), Sec4Hyp Ω →
      ∀ S : Subgroup G, IsSylowOf 2 S ⊤ → ∀ a b d : NBar (sec4W Ω S),
        a ∈ DBar Ω (sec4W Ω S) → b ∈ DBar Ω (sec4W Ω S) → d ∈ DBar Ω (sec4W Ω S) →
        b * d ≠ d * b → a * d = d * a ∨ a * b = b * a ∨ a * (d * b * d) = d * b * d * a := by
  intro G _ _ Ω H S hS a b d ha hb hd hbd
  by_contra hcon
  push Not at hcon
  obtain ⟨had, hab, habd⟩ := hcon
  obtain ⟨T, hT, haT⟩ := DBar.exists_isBarOf ha
  obtain ⟨R, hR, hbR⟩ := DBar.exists_isBarOf hb
  obtain ⟨P, hP, hdP⟩ := DBar.exists_isBarOf hd
  obtain ⟨V, hV⟩ := DSet.exists_rot H.hΩ hT
  obtain ⟨t, ht⟩ := IsZOf.exists_of_rot hV
  obtain ⟨U, hU⟩ := DSet.exists_rot H.hΩ hR
  obtain ⟨z, hz⟩ := IsZOf.exists_of_rot hU
  obtain ⟨Q, hQ⟩ := DSet.exists_rot H.hΩ hP
  obtain ⟨y, hy⟩ := IsZOf.exists_of_rot hQ
  have hdP' := hdP
  obtain ⟨Q', hQ', x, hxP, hxQ', rfl⟩ := hdP'
  have hQQ : Q' = Q := hQ.eq_of_isCyclic hQ'.le hQ'.isCyclic hQ'.relIndex_eq
  subst hQQ
  obtain ⟨s, hsT, hsV⟩ := hV.exists_not_mem
  have hdd : (x : NBar (sec4W Ω S)) * x = 1 := DBar.mul_self H.hΩ hS hd
  have hdinv : (x : NBar (sec4W Ω S))⁻¹ = x := inv_eq_of_mul_eq_one_right hdd
  have hRx : AschbacherTightEmbedding.rightConjugate R x ∈ DSet Ω (sec4W Ω S) :=
    DSet.rightConjugate_mem H.hΩ hR x.2
  have hbx := hbR.rightConjugate x
  rw [hdinv] at hbx
  have hzx := hz.rightConjugate (x : G)
  have e1 : (x : G)⁻¹ * z * x = z * y :=
    conj_z_of_not_commute H hS hP hR hQ hy hz hdP hbR (fun h => hbd h.symm) hxP hxQ'
  have e2 : s⁻¹ * z * s = z * t :=
    conj_z_of_not_commute H hS hT hR hV ht hz haT hbR hab hsT hsV
  have e3 : s⁻¹ * y * s = y * t :=
    conj_z_of_not_commute H hS hT hP hV ht hy haT hdP had hsT hsV
  have e4 : s⁻¹ * ((x : G)⁻¹ * z * x) * s = (x : G)⁻¹ * z * x * t :=
    conj_z_of_not_commute H hS hT hRx hV ht hzx haT hbx habd hsT hsV
  rw [e1] at e4
  have hW := fun {u v : G} (hu : u ∈ sec4W Ω S) (hv : v ∈ sec4W Ω S) => sec4W_comm H.hΩ hS hu hv
  have htW : t ∈ sec4W Ω S := DSet.rot_le H.hΩ hS hT hV (ht.mem_rot hV).1
  have hyW : y ∈ sec4W Ω S := DSet.rot_le H.hΩ hS hP hQ (hy.mem_rot hQ).1
  have h1 : s⁻¹ * (z * y) * s = z * y := by
    calc s⁻¹ * (z * y) * s = (s⁻¹ * z * s) * (s⁻¹ * y * s) := by group
      _ = z * (t * y) * t := by rw [e2, e3]; group
      _ = z * y * (t * t) := by rw [hW htW hyW]; group
      _ = z * y := by rw [ht.mul_self, mul_one]
  rw [h1] at e4
  apply ht.ne_one
  calc t = (z * y)⁻¹ * (z * y * t) := by group
    _ = 1 := by rw [← e4, inv_mul_cancel]

end CFSG.ComponentClassification.Asc76.Sec4
