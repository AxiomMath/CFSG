module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Klein

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup

variable {G : Type} [Group G]

structure JBasic (t z : G) : Prop where
  J_le_C : Jg t z ≤ Cz z
  conj_K : ∀ j ∈ Jg t z, ∀ k ∈ Kg t z, j * k * j⁻¹ ∈ Kg t z
  conj_OK : ∀ j ∈ Jg t z, ∀ o ∈ OKg t z, j * o * j⁻¹ ∈ OKg t z
  relIndex_KJ : (Kg t z).relIndex (Jg t z) = 2
  swap_of_not_mem : ∀ j ∈ Jg t z, j ∉ Kg t z → j * t * j⁻¹ = t * z
  swap : ∃ y ∈ Jg t z, y * t * y⁻¹ = t * z

theorem conj_mem_Vtz {t z j v : G} (hj : j ∈ Jg t z) (hv : v ∈ Vtz t z) :
    j * v * j⁻¹ ∈ Vtz t z :=
  (mem_normalizer_iff.1 hj v).1 hv

theorem inv_conj_mem_Vtz {t z j v : G} (hj : j ∈ Jg t z) (hv : v ∈ Vtz t z) :
    j⁻¹ * v * j ∈ Vtz t z := by
  simpa using (mem_normalizer_iff.1 (inv_mem hj) v).1 hv

theorem conj_z_eq {t z j : G} (hK : KleinPair t z) (hj : j ∈ Jg t z) (h1 : ¬ IsConj t z)
    (h2 : IsConj t (t * z)) : j * z * j⁻¹ = z := by
  have hmem : j * z * j⁻¹ ∈ Vtz t z := conj_mem_Vtz hj z_mem_Vtz
  rcases (mem_Vtz_iff hK).1 hmem with h | h | h | h
  · exfalso
    have hz1 : z = 1 := by
      calc z = j⁻¹ * (j * z * j⁻¹) * j := by group
        _ = 1 := by rw [h]; group
    exact hK.z_ne hz1
  · exfalso
    exact h1 (isConj_iff.2 ⟨j, h⟩).symm
  · exact h
  · exfalso
    exact h1 (h2.trans (isConj_iff.2 ⟨j, h⟩).symm)

theorem conj_t_eq_or {t z j : G} (hK : KleinPair t z) (hj : j ∈ Jg t z)
    (h1 : ¬ IsConj t z) : j * t * j⁻¹ = t ∨ j * t * j⁻¹ = t * z := by
  have hmem : j * t * j⁻¹ ∈ Vtz t z := conj_mem_Vtz hj t_mem_Vtz
  rcases (mem_Vtz_iff hK).1 hmem with h | h | h | h
  · exfalso
    have ht1 : t = 1 := by
      calc t = j⁻¹ * (j * t * j⁻¹) * j := by group
        _ = 1 := by rw [h]; group
    exact hK.t_ne ht1
  · exact Or.inl h
  · exfalso
    exact h1 (isConj_iff.2 ⟨j, h⟩)
  · exact Or.inr h

theorem mem_Kg_iff {t z j : G} (hK : KleinPair t z) (h1 : ¬ IsConj t z)
    (h2 : IsConj t (t * z)) (hj : j ∈ Jg t z) : j ∈ Kg t z ↔ j * t * j⁻¹ = t := by
  constructor
  · intro hk
    rw [mem_Kg] at hk
    calc j * t * j⁻¹ = (j * t) * j⁻¹ := by group
      _ = (t * j) * j⁻¹ := by rw [hk.1]
      _ = t := by group
  · intro h
    rw [mem_Kg]
    refine ⟨?_, ?_⟩
    · calc j * t = (j * t * j⁻¹) * j := by group
        _ = t * j := by rw [h]
    · calc j * z = (j * z * j⁻¹) * j := by group
        _ = z * j := by rw [conj_z_eq hK hj h1 h2]

theorem conj_K {t z : G} (hK : KleinPair t z) (h1 : ¬ IsConj t z) (h2 : IsConj t (t * z))
    {j k : G} (hj : j ∈ Jg t z) (hk : k ∈ Kg t z) : j * k * j⁻¹ ∈ Kg t z := by
  have hjt : j⁻¹ * t * j ∈ Vtz t z := inv_conj_mem_Vtz hj t_mem_Vtz
  have hjz : j⁻¹ * z * j ∈ Vtz t z := inv_conj_mem_Vtz hj z_mem_Vtz
  have hkt : k * (j⁻¹ * t * j) * k⁻¹ = j⁻¹ * t * j := Kg_comm_Vtz hk hjt
  have hkz : k * (j⁻¹ * z * j) * k⁻¹ = j⁻¹ * z * j := Kg_comm_Vtz hk hjz
  have hconjt : (j * k * j⁻¹) * t * (j * k * j⁻¹)⁻¹ = t := by
    calc (j * k * j⁻¹) * t * (j * k * j⁻¹)⁻¹
        = j * (k * (j⁻¹ * t * j) * k⁻¹) * j⁻¹ := by group
      _ = j * (j⁻¹ * t * j) * j⁻¹ := by rw [hkt]
      _ = t := by group
  have hconjz : (j * k * j⁻¹) * z * (j * k * j⁻¹)⁻¹ = z := by
    calc (j * k * j⁻¹) * z * (j * k * j⁻¹)⁻¹
        = j * (k * (j⁻¹ * z * j) * k⁻¹) * j⁻¹ := by group
      _ = j * (j⁻¹ * z * j) * j⁻¹ := by rw [hkz]
      _ = z := by group
  rw [mem_Kg]
  constructor
  · calc (j * k * j⁻¹) * t
        = ((j * k * j⁻¹) * t * (j * k * j⁻¹)⁻¹) * (j * k * j⁻¹) := by group
      _ = t * (j * k * j⁻¹) := by rw [hconjt]
  · calc (j * k * j⁻¹) * z
        = ((j * k * j⁻¹) * z * (j * k * j⁻¹)⁻¹) * (j * k * j⁻¹) := by group
      _ = z * (j * k * j⁻¹) := by rw [hconjz]

theorem conj_OK {t z : G} (hK : KleinPair t z) (h1 : ¬ IsConj t z) (h2 : IsConj t (t * z))
    {j o : G} (hj : j ∈ Jg t z) (ho : o ∈ OKg t z) : j * o * j⁻¹ ∈ OKg t z := by
  change o ∈ TwoFi22.O2In (Kg t z) at ho
  change j * o * j⁻¹ ∈ TwoFi22.O2In (Kg t z)
  have hn : ∀ k ∈ Kg t z, j * k * j⁻¹ ∈ Kg t z := fun k hk => conj_K hK h1 h2 hj hk
  have hn' : ∀ k ∈ Kg t z, j⁻¹ * k * j ∈ Kg t z := fun k hk => by
    have h := conj_K hK h1 h2 (inv_mem hj) hk
    simpa using h
  let φ : ↥(Kg t z) →* ↥(Kg t z) :=
    { toFun := fun k => ⟨j * (k : G) * j⁻¹, hn k k.2⟩
      map_one' := by ext; simp
      map_mul' := by
        intro a b
        ext
        show j * ((a * b : ↥(Kg t z)) : G) * j⁻¹ =
          j * (a : G) * j⁻¹ * (j * (b : G) * j⁻¹)
        rw [Subgroup.coe_mul]
        group }
  have hφinj : Function.Injective φ := by
    intro a b hab
    have hval : (φ a : G) = (φ b : G) := congrArg Subtype.val hab
    apply Subtype.ext
    have := congrArg (fun x : G => j⁻¹ * x * j) hval
    simpa [φ] using this
  have hφsurj : Function.Surjective φ := by
    intro b
    refine ⟨⟨j⁻¹ * (b : G) * j, hn' b b.2⟩, ?_⟩
    ext
    simp only [φ, MonoidHom.coe_mk, OneHom.coe_mk]
    group
  let Φ : ↥(Kg t z) ≃* ↥(Kg t z) := MulEquiv.ofBijective φ ⟨hφinj, hφsurj⟩
  have hmap : (TwoFi22.O2In (Kg t z)).map (MulAut.conj j).toMonoidHom =
      TwoFi22.O2In (Kg t z) := by
    have hp : (CFSG.pCore 2 ↥(Kg t z)).map Φ.toMonoidHom = CFSG.pCore 2 ↥(Kg t z) :=
      CFSG.pCore_map_iso 2 Φ
    change ((CFSG.pCore 2 ↥(Kg t z)).map (Kg t z).subtype).map
        (MulAut.conj j).toMonoidHom = (CFSG.pCore 2 ↥(Kg t z)).map (Kg t z).subtype
    rw [Subgroup.map_map]
    have hcomp : (MulAut.conj j).toMonoidHom.comp (Kg t z).subtype =
        (Kg t z).subtype.comp Φ.toMonoidHom := by
      ext x
      change (MulAut.conj j) (x : G) = ((φ x : ↥(Kg t z)) : G)
      rw [MulAut.conj_apply]
      rfl
    rw [hcomp, ← Subgroup.map_map, hp]
  rw [← hmap]
  exact ⟨o, ho, by simp [MulAut.conj_apply]⟩

theorem swap_of_not_mem {t z : G} (hK : KleinPair t z) (h1 : ¬ IsConj t z)
    (h2 : IsConj t (t * z)) {j : G} (hj : j ∈ Jg t z) (hjnk : j ∉ Kg t z) :
    j * t * j⁻¹ = t * z := by
  rcases conj_t_eq_or hK hj h1 with h | h
  · exact absurd ((mem_Kg_iff hK h1 h2 hj).2 h) hjnk
  · exact h

theorem relIndex_KJ {t z : G} (hK : KleinPair t z) (h1 : ¬ IsConj t z) (h2 : IsConj t (t * z))
    (hs : ∃ y ∈ Jg t z, y * t * y⁻¹ = t * z) : (Kg t z).relIndex (Jg t z) = 2 := by
  obtain ⟨y, hyJ, hyt⟩ := hs
  rw [Subgroup.relIndex_eq_two_iff]
  refine ⟨y, hyJ, fun b hbJ => ?_⟩
  have hbyJ : b * y ∈ Jg t z := mul_mem hbJ hyJ
  have hconj : (b * y) * t * (b * y)⁻¹ = (b * t * b⁻¹) * z := by
    calc (b * y) * t * (b * y)⁻¹ = b * (y * t * y⁻¹) * b⁻¹ := by group
      _ = b * (t * z) * b⁻¹ := by rw [hyt]
      _ = (b * t * b⁻¹) * (b * z * b⁻¹) := by group
      _ = (b * t * b⁻¹) * z := by rw [conj_z_eq hK hbJ h1 h2]
  have hbt_or : b * t * b⁻¹ = t ∨ b * t * b⁻¹ = t * z := conj_t_eq_or hK hbJ h1
  by_cases hbK : b ∈ Kg t z
  · have hbt : b * t * b⁻¹ = t := (mem_Kg_iff hK h1 h2 hbJ).1 hbK
    have hbyK : b * y ∉ Kg t z := by
      intro hyK
      have hbyt : (b * y) * t * (b * y)⁻¹ = t := (mem_Kg_iff hK h1 h2 hbyJ).1 hyK
      rw [hconj, hbt] at hbyt
      have hz1 : z = 1 := by
        have h' : t * z = t * 1 := by rw [hbyt, mul_one]
        exact mul_left_cancel h'
      exact hK.z_ne hz1
    exact Or.inr ⟨hbK, hbyK⟩
  · have hbt : b * t * b⁻¹ = t * z := by
      rcases hbt_or with h | h
      · exact absurd ((mem_Kg_iff hK h1 h2 hbJ).2 h) hbK
      · exact h
    have hbyt : (b * y) * t * (b * y)⁻¹ = t := by
      rw [hconj, hbt, mul_assoc, ← pow_two, hK.z_sq, mul_one]
    exact Or.inl ⟨(mem_Kg_iff hK h1 h2 hbyJ).2 hbyt, hbK⟩

theorem J_le_C {t z : G} (hK : KleinPair t z) (h1 : ¬ IsConj t z) (h2 : IsConj t (t * z)) :
    Jg t z ≤ Cz z := by
  intro j hj
  rw [mem_Cz]
  have h := conj_z_eq hK hj h1 h2
  calc j * z = (j * z * j⁻¹) * j := by group
    _ = z * j := by rw [h]

theorem jBasic {t z : G} (hK : KleinPair t z) (h1 : ¬ IsConj t z) (h2 : IsConj t (t * z))
    (hs : ∃ y ∈ Jg t z, y * t * y⁻¹ = t * z) : JBasic t z where
  J_le_C := J_le_C hK h1 h2
  conj_K := fun j hj k hk => conj_K hK h1 h2 hj hk
  conj_OK := fun j hj o ho => conj_OK hK h1 h2 hj ho
  relIndex_KJ := relIndex_KJ hK h1 h2 hs
  swap_of_not_mem := fun j hj hjnk => swap_of_not_mem hK h1 h2 hj hjnk
  swap := hs

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
