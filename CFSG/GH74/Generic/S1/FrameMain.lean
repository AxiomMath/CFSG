module

public import CFSG.GH74.Generic.S1.FrameNormUni
public import CFSG.GH74.Generic.S1.FrameLift
public import CFSG.GH74.Generic.S1.Defs
public import CFSG.GH74.Generic.S1.FrameGroup

public section

namespace CFSG.GH74.Generic.S1

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank Subgroup CFSG.GH74.Generic

section Aux

variable {G : Type} [Group G]

theorem ringChar_ne_two_of_ne {F : Type} [Field F] (h2 : (2 : F) ≠ 0) : ringChar F ≠ 2 := by
  intro h
  apply h2
  have := (ringChar.spec F 2).2 (by rw [h])
  simpa using this

theorem exists_lift_bar {x : G} (c : CentralizerBar x) :
    ∃ (g : G) (hg : g ∈ centralizer ({x} : Set G)), barOf hg = c := by
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective c
  exact ⟨y.1, y.2, hy⟩

theorem barOf_conj {x g v : G} (hg : g ∈ centralizer ({x} : Set G))
    (hv : v ∈ centralizer ({x} : Set G)) :
    barOf (mul_mem (mul_mem hg hv) (inv_mem hg) : g * v * g⁻¹ ∈ centralizer ({x} : Set G)) =
      barOf hg * barOf hv * (barOf hg)⁻¹ := rfl

theorem barOf_mul_self {x v : G} (hv : v ∈ centralizer ({x} : Set G)) (hv2 : v * v = 1) :
    barOf hv * barOf hv = 1 := by
  have : proj x ((⟨v, hv⟩ : ↥(centralizer ({x} : Set G))) * ⟨v, hv⟩) = 1 := by
    rw [show (⟨v, hv⟩ : ↥(centralizer ({x} : Set G))) * ⟨v, hv⟩ = 1 from Subtype.ext hv2, map_one]
  rwa [map_mul] at this

end Aux

variable {G : Type} [Group G] [Finite G]

theorem frame_of_model {x : G} (hx : orderOf x = 2) {K : Subgroup (CentralizerBar x)} [K.Normal]
    (hxK : xbar x ∈ K) {v : G} (hv : v ∈ centralizer ({x} : Set G)) (hconj : IsConj x v)
    (hv2 : v * v = 1) (hvK : barOf hv ∉ K) {α : MulAut ↥K}
    (hα : ∀ k : ↥K, ((α k : ↥K) : CentralizerBar x) = barOf hv * k * (barOf hv)⁻¹)
    {F : Type} [Field F] (h2 : (2 : F) ≠ 0) {S : Subgroup (GL (Fin 4) F)} (e₁ : ↥K ≃* ↥S)
    (hact1 : ∀ n : ↥K, ((e₁ (α n) : ↥S) : GL (Fin 4) F) =
      reflDiag F 3 * ((e₁ n : ↥S) : GL (Fin 4) F) * (reflDiag F 3)⁻¹)
    (hxe1 : ((e₁ ⟨xbar x, hxK⟩ : ↥S) : GL (Fin 4) F) = -1) (m : Fin 4 → ↥S)
    (hm : ∀ i, ((m i : ↥S) : GL (Fin 4) F) * reflDiag F 3 * ((m i : ↥S) : GL (Fin 4) F)⁻¹ =
      reflDiag F i) :
    ∃ (u : Fin 4 → G) (hu : ∀ i, u i ∈ centralizer ({x} : Set G)),
      (∀ i, IsConj x (u i) ∧ u i * u i = 1 ∧ barOf (hu i) ∉ K) ∧
        (∀ i j, u i * u j = u j * u i) ∧ u 0 * u 1 * u 2 * u 3 = x ∧
          (∀ i j, i ≠ j → u i ≠ u j) ∧ ∀ i, ActsAsReflOn e₁ (barOf (hu i)) (reflDiag F i) := by
  classical
  have hvb2 := barOf_mul_self hv hv2
  obtain ⟨w, hw2, hwK, hwc, hwprod, hwne, hwk, hwact⟩ :=
    frame_in_bar h2 e₁ hvb2 hvK hα hact1 m hm hxK hxe1
  obtain ⟨u, hu, hu2, huc, hprod⟩ := exists_frame_lift hx w hw2 hwc hwprod
  have hbar : ∀ i, barOf (hu i) = w i := fun i => (hu2 i).2
  have hconjs : ∀ i, IsConj x (u i) := by
    intro i
    obtain ⟨k, hk⟩ := hwk i
    obtain ⟨g, hg, hgk⟩ := exists_lift_bar (x := x) (k : CentralizerBar x)
    have hvi : g * v * g⁻¹ ∈ centralizer ({x} : Set G) := mul_mem (mul_mem hg hv) (inv_mem hg)
    have hbvi : barOf hvi = w i := by
      rw [barOf_conj hg hv, hgk, hk]
      rfl
    have hvi2 : (g * v * g⁻¹) * (g * v * g⁻¹) = 1 := by
      calc (g * v * g⁻¹) * (g * v * g⁻¹) = g * (v * v) * g⁻¹ := by group
        _ = 1 := by rw [hv2]; group
    have h1 : IsConj (u i) (g * v * g⁻¹) :=
      isConj_of_barOf_eq (hu i) hvi (hu2 i).1 hvi2 ((hbar i).trans hbvi.symm)
    have h2' : IsConj v (g * v * g⁻¹) := isConj_iff.2 ⟨g, rfl⟩
    exact (hconj.trans h2').trans h1.symm
  refine ⟨u, hu, fun i => ⟨hconjs i, (hu2 i).1, ?_⟩, huc, hprod, ?_, ?_⟩
  · rw [hbar i]
    exact hwK i
  · intro i j hij heq
    apply hwne i j hij
    rw [← hbar i, ← hbar j]
    exact congrArg QuotientGroup.mk (Subtype.ext heq)
  · intro i
    rw [hbar i]
    exact hwact i

theorem s1_frame_lin {x : G} (hx : orderOf x = 2) {K : Subgroup (CentralizerBar x)} [K.Normal]
    (hxK : xbar x ∈ K) {v : G} (hv : v ∈ centralizer ({x} : Set G)) (hconj : IsConj x v)
    (hv2 : v * v = 1) (hvK : barOf hv ∉ K) {α : MulAut ↥K}
    (hα : ∀ k : ↥K, ((α k : ↥K) : CentralizerBar x) = barOf hv * k * (barOf hv)⁻¹)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F % 4 = 3) (e : ↥K ≃* ↥(StatedSL 4 F))
    (hR : IsReflection (StatedSL 4 F) (MulAut.congr e α)) :
    ∃ (u : Fin 4 → G) (hu : ∀ i, u i ∈ centralizer ({x} : Set G)), S1Frame x K u hu := by
  classical
  obtain ⟨ρ, hρ2, hρdet, hρact⟩ := hR
  have hodd : Odd (Nat.card F) := Nat.odd_iff.2 (by omega)
  have h2 : (2 : F) ≠ 0 := CFSG.GH74.L5U5.two_ne_zero_of_odd_card hodd
  have hchar : ringChar F ≠ 2 := ringChar_ne_two_of_ne h2
  obtain ⟨ρ', P, hρ', hP, -⟩ := exists_refl_conj hchar hρ2 hρdet
  have hact0 : ∀ n : ↥K, ((e (α n) : ↥(StatedSL 4 F)) : GL (Fin 4) F) =
      ρ * ((e n : ↥(StatedSL 4 F)) : GL (Fin 4) F) * ρ⁻¹ := fun n => by
    have h1 : (MulAut.congr e α) (e n) = e (α n) := by simp [MulAut.congr_apply]
    have := hρact (e n)
    rw [h1] at this
    exact this
  obtain ⟨e₁, hact1, he1⟩ := exists_normalized_iso e α hρ' hact0 hP
    (fun k hk => conj_mem_statedSL P hk)
    (fun k hk => by simpa using conj_mem_statedSL P⁻¹ hk)
  have hz : (⟨xbar x, hxK⟩ : ↥K) ∈ Subgroup.center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (xbar_comm x (g : CentralizerBar x))
  have hz1 : (⟨xbar x, hxK⟩ : ↥K) ≠ 1 := fun h => xbar_ne_one hx (congrArg Subtype.val h)
  have hxe0 : ((e ⟨xbar x, hxK⟩ : ↥(StatedSL 4 F)) : GL (Fin 4) F) = -1 := by
    have hc := (mem_center_iff_of_mulEquiv e _).2 hz
    rcases (mem_center_statedSL_four_iff hF _).1 hc with h | h
    · exfalso
      apply hz1
      apply e.injective
      rw [map_one]
      exact Subtype.ext h
    · rw [h, xGL_eq_neg_one]
  have hxe1 : ((e₁ ⟨xbar x, hxK⟩ : ↥(StatedSL 4 F)) : GL (Fin 4) F) = -1 := by
    rw [he1, hxe0]
    simp
  obtain ⟨u, hu, h1, h2', h3, h4, h5⟩ := frame_of_model hx hxK hv hconj hv2 hvK hα h2 e₁ hact1 hxe1
    (fun i => ⟨monoGL F i, monoGL_mem_statedSL F i⟩) (fun i => monoGL_conj F i)
  exact ⟨u, hu, h1, h2', h3, h4, Or.inl ⟨F, inferInstance, inferInstance, e₁, hF, h5⟩⟩

theorem s1_frame_uni {x : G} (hx : orderOf x = 2) {K : Subgroup (CentralizerBar x)} [K.Normal]
    (hxK : xbar x ∈ K) {v : G} (hv : v ∈ centralizer ({x} : Set G)) (hconj : IsConj x v)
    (hv2 : v * v = 1) (hvK : barOf hv ∉ K) {α : MulAut ↥K}
    (hα : ∀ k : ↥K, ((α k : ↥K) : CentralizerBar x) = barOf hv * k * (barOf hv)⁻¹)
    {q : ℕ} {F : Type} [Field F] [Finite F] (hF : Nat.card F = q ^ 2) (hq : q % 4 = 1)
    (e : ↥K ≃* ↥(StatedSU 4 q F)) (hR : IsReflection (StatedSU 4 q F) (MulAut.congr e α)) :
    ∃ (u : Fin 4 → G) (hu : ∀ i, u i ∈ centralizer ({x} : Set G)), S1Frame x K u hu := by
  classical
  obtain ⟨ρ, hρ2, hρdet, hρact⟩ := hR
  have hqodd : Odd q := Nat.odd_iff.2 (by omega)
  have hodd : Odd (Nat.card F) := by
    rw [hF]
    exact hqodd.pow
  have h2 : (2 : F) ≠ 0 := CFSG.GH74.L5U5.two_ne_zero_of_odd_card hodd
  have hnorm : ∀ k ∈ StatedSU 4 q F, ρ * k * ρ⁻¹ ∈ StatedSU 4 q F := fun k hk => by
    have := hρact ⟨k, hk⟩
    rw [← this]
    exact (MulAut.congr e α ⟨k, hk⟩).2
  obtain ⟨ρ', P, hρ', hP, hP1, hP2⟩ := FrameUni.exists_refl_conj_uni hF hq hρ2 hρdet hnorm
  have hact0 : ∀ n : ↥K, ((e (α n) : ↥(StatedSU 4 q F)) : GL (Fin 4) F) =
      ρ * ((e n : ↥(StatedSU 4 q F)) : GL (Fin 4) F) * ρ⁻¹ := fun n => by
    have h1 : (MulAut.congr e α) (e n) = e (α n) := by simp [MulAut.congr_apply]
    have := hρact (e n)
    rw [h1] at this
    exact this
  obtain ⟨e₁, hact1, he1⟩ := exists_normalized_iso e α hρ' hact0 hP hP1 hP2
  have hz : (⟨xbar x, hxK⟩ : ↥K) ∈ Subgroup.center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (xbar_comm x (g : CentralizerBar x))
  have hz1 : (⟨xbar x, hxK⟩ : ↥K) ≠ 1 := fun h => xbar_ne_one hx (congrArg Subtype.val h)
  have hxe0 : ((e ⟨xbar x, hxK⟩ : ↥(StatedSU 4 q F)) : GL (Fin 4) F) = -1 := by
    have hc := (mem_center_iff_of_mulEquiv e _).2 hz
    obtain ⟨p, f, hp, hchar, rfl⟩ := exists_prime_pow_of_card_eq_sq hF
    rcases (mem_center_statedSU_four_iff hF hq _).1 hc with h | h
    · exfalso
      apply hz1
      apply e.injective
      rw [map_one]
      exact Subtype.ext h
    · rw [h, xGL_eq_neg_one]
  have hxe1 : ((e₁ ⟨xbar x, hxK⟩ : ↥(StatedSU 4 q F)) : GL (Fin 4) F) = -1 := by
    rw [he1, hxe0]
    simp
  obtain ⟨u, hu, h1, h2', h3, h4, h5⟩ := frame_of_model hx hxK hv hconj hv2 hvK hα h2 e₁ hact1 hxe1
    (fun i => ⟨monoGL F i, monoGL_mem_statedSU F hqodd i⟩) (fun i => monoGL_conj F i)
  exact ⟨u, hu, h1, h2', h3, h4, Or.inr ⟨q, F, inferInstance, inferInstance, e₁, hF, hq, h5⟩⟩

theorem s1_frame {x : G} (hx : orderOf x = 2) {K : Subgroup (CentralizerBar x)} [K.Normal]
    (hxK : xbar x ∈ K) {v : G} (hv : v ∈ centralizer ({x} : Set G)) (hconj : IsConj x v)
    (hv2 : v * v = 1) (hvK : barOf hv ∉ K) {α : MulAut ↥K}
    (hα : ∀ k : ↥K, ((α k : ↥K) : CentralizerBar x) = barOf hv * k * (barOf hv)⁻¹)
    (hR : IsReflectionAut α) :
    ∃ (u : Fin 4 → G) (hu : ∀ i, u i ∈ centralizer ({x} : Set G)), S1Frame x K u hu := by
  rcases hR with ⟨F, _, _, e, hF, hR⟩ | ⟨q, F, _, _, e, hF, hq, hR⟩
  · exact s1_frame_lin hx hxK hv hconj hv2 hvK hα hF e hR
  · exact s1_frame_uni hx hxK hv hconj hv2 hvK hα hF hq e hR

end CFSG.GH74.Generic.S1
