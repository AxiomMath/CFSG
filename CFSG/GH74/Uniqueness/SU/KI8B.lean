module

public import CFSG.GH74.Uniqueness.SU.KInputs2
public import CFSG.GH74.Uniqueness.SU.SU4Quot
public import CFSG.CharacterTheory.Semidihedral.GL2Recognition.OddCoreFreeGL2Recognition
public import Certificates.Certificate12000

public section

namespace CFSG.GH74.Uniqueness.SU.K

open Subgroup CFSG.Blueprint CFSG.GH74.Uniqueness.SU.SU4

theorem gl23_eq_neg_one_of_central (g : GL (Fin 2) (ZMod 3))
    (hc : ∀ h : GL (Fin 2) (ZMod 3), h * g = g * h) (h1 : g ≠ 1) : g = -1 :=
  Certificates.certificate12000 g hc h1

theorem ki8b_core
    {H : Type} [Group H] [Finite H]
    (hO : pPrimeCore 2 H = ⊥) (hone : OneInvClass H)
    {z : H} (hz : orderOf z = 2) (e : Nonempty (CBar H z ≃* GL (Fin 2) (ZMod 3))) :
    (NativeSporadic.IsSporadic H .M11 ∨ LieModel H .PSL 3 3 1) ∧
      pPrimeCore 2 ↥(centralizer ({z} : Set H)) = ⊥ := by
  obtain ⟨e⟩ := e
  set C : Subgroup H := centralizer ({z} : Set H) with hC
  have hzC : z ∈ C := mem_centralizer_singleton_iff.mpr rfl
  let π : ↥C →* GL (Fin 2) (ZMod 3) := e.toMonoidHom.comp (proj C)
  have hπsurj : Function.Surjective π := e.surjective.comp (proj_surjective C)
  have hker : π.ker = pPrimeCore 2 ↥C := by
    ext x
    rw [MonoidHom.mem_ker, ← ker_proj C, MonoidHom.mem_ker]
    exact e.map_eq_one_iff
  have hodd : Odd (Nat.card π.ker) := by
    rw [hker]
    exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥C))
  have hodd' : ∀ K : Subgroup H, K.Normal → Odd (Nat.card K) → K = ⊥ := fun K hK hKo =>
    (pPrimeCore_eq_bot_iff).mp hO K hK (Nat.coprime_two_left.mpr hKo)
  let zc : ↥C := ⟨z, hzC⟩
  have hzc2 : zc * zc = 1 := by
    apply Subtype.ext
    change z * z = 1
    rw [← sq]
    have := pow_orderOf_eq_one z
    rwa [hz] at this
  have hzc_not : zc ∉ pPrimeCore 2 ↥C := by
    intro h
    have h1 : orderOf zc ∣ Nat.card (pPrimeCore 2 ↥C) := Subgroup.orderOf_dvd_natCard _ h
    have h2 : orderOf zc = 2 := by
      rw [← Subgroup.orderOf_coe]
      exact hz
    rw [h2] at h1
    have h3 : Odd (Nat.card (pPrimeCore 2 ↥C)) :=
      Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥C))
    exact (Nat.not_even_iff_odd.mpr h3) (even_iff_two_dvd.mpr h1)
  have hπz : π ⟨z, mem_centralizer_singleton_iff.mpr rfl⟩ = -1 := by
    apply gl23_eq_neg_one_of_central
    · intro h
      obtain ⟨c, rfl⟩ := hπsurj h
      change π c * π zc = π zc * π c
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact mem_centralizer_singleton_iff.mp c.2
    · intro h1
      apply hzc_not
      rw [← hker]
      exact h1
  obtain ⟨hk0, -, -, hxor⟩ :=
    CFSG.Semidihedral.GL2Recognition.odd_core_free_GL2_centralizer_quotient_recognition hodd'
      hone z hz π hπsurj hodd hπz
  refine ⟨?_, by rw [← hker]; exact hk0⟩
  rcases hxor with ⟨⟨-, hmodel⟩, -⟩ | ⟨⟨-, -, ⟨e'⟩⟩, -⟩
  · exact Or.inr (Or.inl ⟨by simp [classicalTags], hmodel⟩)
  · exact Or.inl ⟨e'.trans (MulEquiv.subgroupCongr
      CFSG.Semidihedral.GL2Recognition.lowTwoRankStatedM11_eq_nativeM11)⟩

@[expose] def KI8b : Prop :=
  ∀ (H : Type) [Group H] [Finite H], pPrimeCore 2 H = ⊥ → OneInvClass H →
    ∀ (T : Sylow 2 H) (z : H), z ∈ (T : Subgroup H) → orderOf z = 2 →
      (∀ t ∈ (T : Subgroup H), t * z = z * t) →
      Nonempty (CBar H z ≃* GL (Fin 2) (ZMod 3)) →
        (NativeSporadic.IsSporadic H .M11 ∨ LieModel H .PSL 3 3 1) ∧
          pPrimeCore 2 ↥(centralizer ({z} : Set H)) = ⊥

theorem ki8b : KI8b := by
  intro H _ _ hO hone _ z _ hz _ e
  exact ki8b_core hO hone hz e

end CFSG.GH74.Uniqueness.SU.K
