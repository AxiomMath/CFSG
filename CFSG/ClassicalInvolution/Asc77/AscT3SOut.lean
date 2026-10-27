module

public import CFSG.ClassicalInvolution.Asc77.AscT3SInv
public import CFSG.ClassicalInvolution.Asc77.AscT3RAct

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII.T3S

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3CII.T3R
open scoped MatrixGroups commutatorElement

section Out

variable {G : Type} [Group G] {p f : ℕ} [Fact p.Prime]

@[expose] def OutCommMod (K : Subgroup G) : Prop :=
  ∀ x ∈ Subgroup.normalizer (K : Set G), ∀ y ∈ Subgroup.normalizer (K : Set G),
    ∃ k ∈ K, ∀ g ∈ K, (k * g * k⁻¹)⁻¹ * (⁅x, y⁆ * g * ⁅x, y⁆⁻¹) ∈ oddCoreOf K

theorem outCommMod_of_chart (hp : p ≠ 2) (hq : 5 ≤ p ^ f) {K : Subgroup G}
    (e : ↥K ⧸ classicalInvolutionOddCore ↥K ≃* SL(2, GaloisField p f)) : OutCommMod K := by
  intro x hx y hy
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
  have hodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card (GaloisField p f)) := by
    refine ⟨p, f, Fact.out, ?_, Nat.one_le_iff_ne_zero.mpr hf, hcard⟩
    rcases (Fact.out : p.Prime).eq_two_or_odd' with h | h
    · exact absurd h hp
    · exact h
  have h4 : 4 ≤ Nat.card (GaloisField p f) := by
    rw [hcard]
    exact (by norm_num : 4 ≤ 5).trans hq
  have hxi : x⁻¹ ∈ Subgroup.normalizer (K : Set G) := Subgroup.inv_mem _ hx
  have hyi : y⁻¹ ∈ Subgroup.normalizer (K : Set G) := Subgroup.inv_mem _ hy
  have hxy : x * y ∈ Subgroup.normalizer (K : Set G) := Subgroup.mul_mem _ hx hy
  have hxyx : x * y * x⁻¹ ∈ Subgroup.normalizer (K : Set G) := Subgroup.mul_mem _ hxy hxi
  have hc : ⁅x, y⁆ ∈ Subgroup.normalizer (K : Set G) := by
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ hxyx hyi
  obtain ⟨s, hs⟩ := isInnerAut_commutator_of_equiv_sl2 hodd h4
    (MulEquiv.refl SL(2, GaloisField p f)) (phiG K e x) (phiG K e y)
  obtain ⟨k, rfl⟩ := eta_surjective K e s
  have hphi : phiG K e ⁅x, y⁆ = phiG K e x * phiG K e y * (phiG K e x)⁻¹ * (phiG K e y)⁻¹ := by
    rw [commutatorElement_def, phiG_mul hxyx hyi, phiG_mul hxy hxi, phiG_mul hx hy,
      phiG_inv hx, phiG_inv hy]
  refine ⟨k, k.2, fun g hg => ?_⟩
  have h1 := phiG_apply_eta (L := K) (e := e) hc ⟨g, hg⟩
  rw [hphi, ← hs] at h1
  have h2 : (MulAut.conj (eta K e k) : MulAut SL(2, GaloisField p f)) (eta K e ⟨g, hg⟩) =
      eta K e (k * ⟨g, hg⟩ * k⁻¹) := by
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv]
  rw [h2] at h1
  have hB : ⁅x, y⁆ * g * ⁅x, y⁆⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hc g).mp hg
  have hAB : (k * ⟨g, hg⟩ * k⁻¹)⁻¹ * (⟨⁅x, y⁆ * g * ⁅x, y⁆⁻¹, hB⟩ : ↥K) ∈
      classicalInvolutionOddCore ↥K := by
    rw [← eta_eq_one_iff K e, map_mul, map_inv, h1]
    exact inv_mul_cancel _
  exact mem_oddCoreOf_iff.mpr ⟨((k * ⟨g, hg⟩ * k⁻¹)⁻¹ * (⟨⁅x, y⁆ * g * ⁅x, y⁆⁻¹, hB⟩ : ↥K)).2,
    hAB⟩

omit [Fact p.Prime] in
theorem side_trivial {A B : Subgroup G} (hBN : B ≤ Subgroup.normalizer (A : Set G))
    (hc : ∀ g ∈ A, ∀ b ∈ B, ⁅g, b⁆ ∈ oddCoreOf A) {w a₀ b₀ : G} (ha₀ : a₀ ∈ A) (hb₀ : b₀ ∈ B)
    (hkg : ∀ g ∈ A, (a₀ * g * a₀⁻¹)⁻¹ * (w * g * w⁻¹) ∈ oddCoreOf A) :
    ∀ g ∈ A, ⁅(a₀ * b₀)⁻¹ * w, g⁆ ∈ oddCoreOf A := by
  intro g hg
  have hbg : ⁅b₀⁻¹, g⁆ ∈ oddCoreOf A := by
    rw [← commutatorElement_inv]
    exact (oddCoreOf A).inv_mem (hc g hg b₀⁻¹ (B.inv_mem hb₀))
  have ho := hkg g hg
  have hab : (a₀ * b₀)⁻¹ ∈ Subgroup.normalizer (A : Set G) :=
    Subgroup.inv_mem _ (Subgroup.mul_mem _ (Subgroup.le_normalizer ha₀) (hBN hb₀))
  have hn : (a₀ * b₀)⁻¹ * ((a₀ * g * a₀⁻¹)⁻¹ * (w * g * w⁻¹)) * (a₀ * b₀) ∈ oddCoreOf A := by
    have := (Subgroup.mem_normalizer_iff.mp (mem_normalizer_oddCore_of_mem_normalizer hab) _).mp ho
    simpa using this
  have hg' : g * ((a₀ * b₀)⁻¹ * ((a₀ * g * a₀⁻¹)⁻¹ * (w * g * w⁻¹)) * (a₀ * b₀)) * g⁻¹ ∈
      oddCoreOf A :=
    (Subgroup.mem_normalizer_iff.mp (mem_normalizer_oddCore_of_mem_normalizer
      (Subgroup.le_normalizer hg)) _).mp hn
  have e : ⁅(a₀ * b₀)⁻¹ * w, g⁆ = ⁅b₀⁻¹, g⁆ * (g * ((a₀ * b₀)⁻¹ * ((a₀ * g * a₀⁻¹)⁻¹ *
      (w * g * w⁻¹)) * (a₀ * b₀)) * g⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact (oddCoreOf A).mul_mem hbg hg'

omit [Fact p.Prime] in
theorem commutator_decomp_mod [Finite G] {K K' : Subgroup G}
    (hKN' : K ≤ Subgroup.normalizer (K' : Set G)) (hK'N : K' ≤ Subgroup.normalizer (K : Set G))
    (hc : ∀ k ∈ K, ∀ k' ∈ K', ⁅k, k'⁆ ∈ oddCoreOf K ∧ ⁅k, k'⁆ ∈ oddCoreOf K')
    (hK : OutCommMod K) (hK' : OutCommMod K') {x y : G}
    (hxK : x ∈ Subgroup.normalizer (K : Set G)) (hxK' : x ∈ Subgroup.normalizer (K' : Set G))
    (hyK : y ∈ Subgroup.normalizer (K : Set G)) (hyK' : y ∈ Subgroup.normalizer (K' : Set G)) :
    ∃ k ∈ K, ∃ k' ∈ K', (k * k')⁻¹ * ⁅x, y⁆ ∈ centralizerModOdd (⊤ : Subgroup G) (K ⊔ K') := by
  obtain ⟨k, hk, hkg⟩ := hK x hxK y hyK
  obtain ⟨k', hk', hk'g⟩ := hK' x hxK' y hyK'
  refine ⟨k, hk, k', hk', ?_⟩
  have hcom : ∀ (u v : G), u ∈ Subgroup.normalizer (K : Set G) →
      v ∈ Subgroup.normalizer (K : Set G) → ⁅u, v⁆ ∈ Subgroup.normalizer (K : Set G) :=
    fun u v hu hv => by
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hu hv)
      (Subgroup.inv_mem _ hu)) (Subgroup.inv_mem _ hv)
  have hcom' : ∀ (u v : G), u ∈ Subgroup.normalizer (K' : Set G) →
      v ∈ Subgroup.normalizer (K' : Set G) → ⁅u, v⁆ ∈ Subgroup.normalizer (K' : Set G) :=
    fun u v hu hv => by
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hu hv)
      (Subgroup.inv_mem _ hu)) (Subgroup.inv_mem _ hv)
  have hwK := hcom x y hxK hyK
  have hwK' := hcom' x y hxK' hyK'
  set w : G := ⁅x, y⁆ with hw
  have hKO : oddCoreOf K ≤ oddCoreOf (K ⊔ K') := oddCoreOf_le_oddCoreOf_sup hK'N
  have hK'O : oddCoreOf K' ≤ oddCoreOf (K ⊔ K') := by
    have := oddCoreOf_le_oddCoreOf_sup hKN'
    rwa [sup_comm] at this
  have hside1 : ∀ g ∈ K, ⁅(k * k')⁻¹ * w, g⁆ ∈ oddCoreOf K :=
    side_trivial hK'N (fun g hg b hb => (hc g hg b hb).1) hk hk' hkg
  have hside2 : ∀ g ∈ K', ⁅(k' * k)⁻¹ * w, g⁆ ∈ oddCoreOf K' :=
    side_trivial hKN' (fun g hg b hb => by
      rw [← commutatorElement_inv]
      exact (oddCoreOf K').inv_mem (hc b hb g hg).2) hk' hk hk'g
  have hν : (k * k')⁻¹ * (k' * k) = ⁅k'⁻¹, k⁻¹⁆ := by
    simp only [commutatorElement_def]
    group
  have hν' : ⁅k'⁻¹, k⁻¹⁆ ∈ oddCoreOf K' := by
    rw [← commutatorElement_inv]
    exact (oddCoreOf K').inv_mem (hc k⁻¹ (K.inv_mem hk) k'⁻¹ (K'.inv_mem hk')).2
  have hside2' : ∀ g ∈ K', ⁅(k * k')⁻¹ * w, g⁆ ∈ oddCoreOf K' := by
    intro g hg
    have e : (k * k')⁻¹ * w = ⁅k'⁻¹, k⁻¹⁆ * ((k' * k)⁻¹ * w) := by
      rw [← hν]
      group
    have hid : ⁅⁅k'⁻¹, k⁻¹⁆ * ((k' * k)⁻¹ * w), g⁆ = ⁅k'⁻¹, k⁻¹⁆ * ⁅(k' * k)⁻¹ * w, g⁆ *
        ⁅k'⁻¹, k⁻¹⁆⁻¹ * ⁅⁅k'⁻¹, k⁻¹⁆, g⁆ := by
      simp only [commutatorElement_def]
      group
    have hg1 : ⁅⁅k'⁻¹, k⁻¹⁆, g⁆ ∈ oddCoreOf K' := by
      have h1 : g * ⁅k'⁻¹, k⁻¹⁆⁻¹ * g⁻¹ ∈ oddCoreOf K' :=
        (Subgroup.mem_normalizer_iff.mp (mem_normalizer_oddCore_of_mem_normalizer
          (Subgroup.le_normalizer hg)) _).mp ((oddCoreOf K').inv_mem hν')
      have e2 : ⁅⁅k'⁻¹, k⁻¹⁆, g⁆ = ⁅k'⁻¹, k⁻¹⁆ * (g * ⁅k'⁻¹, k⁻¹⁆⁻¹ * g⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e2]
      exact (oddCoreOf K').mul_mem hν' h1
    rw [e, hid]
    exact (oddCoreOf K').mul_mem ((oddCoreOf K').mul_mem ((oddCoreOf K').mul_mem hν'
      (hside2 g hg)) ((oddCoreOf K').inv_mem hν')) hg1
  have hM₀ : ∀ u ∈ K ⊔ K', u ∈ Subgroup.normalizer ((K ⊔ K' : Subgroup G) : Set G) :=
    fun u _ => Subgroup.le_normalizer ‹_›
  have hkk : (k * k')⁻¹ ∈ Subgroup.normalizer ((K ⊔ K' : Subgroup G) : Set G) :=
    Subgroup.inv_mem _ (Subgroup.le_normalizer
      (Subgroup.mul_mem _ (Subgroup.mem_sup_left hk) (Subgroup.mem_sup_right hk')))
  have hwM : w ∈ Subgroup.normalizer ((K ⊔ K' : Subgroup G) : Set G) := by
    rw [mem_normalizer_iff_conjSub_eq, late_conjSub_sup]
    rw [mem_normalizer_iff_conjSub_eq.mp hwK, mem_normalizer_iff_conjSub_eq.mp hwK']
  have heM : (k * k')⁻¹ * w ∈ Subgroup.normalizer ((K ⊔ K' : Subgroup G) : Set G) :=
    Subgroup.mul_mem _ hkk hwM
  refine ⟨Subgroup.mem_top _, heM, mem_normalizer_oddCore_of_mem_normalizer heM, fun m hm => ?_⟩
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left K K' hK'N] at hm
  obtain ⟨g, hg, g', hg', rfl⟩ := hm
  have hexp : ⁅(k * k')⁻¹ * w, g * g'⁆ =
      ⁅(k * k')⁻¹ * w, g⁆ * (g * ⁅(k * k')⁻¹ * w, g'⁆ * g⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [hexp]
  have h1 : ⁅(k * k')⁻¹ * w, g⁆ ∈ oddCoreOf (K ⊔ K') := hKO (hside1 g hg)
  have h2 : ⁅(k * k')⁻¹ * w, g'⁆ ∈ oddCoreOf (K ⊔ K') := hK'O (hside2' g' hg')
  have h3 : g * ⁅(k * k')⁻¹ * w, g'⁆ * g⁻¹ ∈ oddCoreOf (K ⊔ K') :=
    (Subgroup.mem_normalizer_iff.mp (mem_normalizer_oddCore_of_mem_normalizer
      (Subgroup.le_normalizer (Subgroup.mem_sup_left hg))) _).mp h2
  exact (oddCoreOf (K ⊔ K')).mul_mem h1 h3

end Out

end CFSG.ClassicalInvolution.Asc77.T3CII.T3S
