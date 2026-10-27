module

public import CFSG.GH74.E2.BoxT5Def
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.E2.ComponentsUnique
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.E2.Box

open CFSG.Open Subgroup

theorem comm_of_commutator_eq_one {G : Type*} [Group G] {y a : G} (h : y⁻¹ * a⁻¹ * y * a = 1) :
    y * a = a * y := by
  have h1 : a⁻¹ * y * a = y := by
    have : y⁻¹ * (a⁻¹ * y * a) = 1 := by rw [← h]; group
    exact (inv_mul_eq_one.1 this).symm
  calc y * a = a * (a⁻¹ * y * a) := by group
    _ = a * y := by rw [h1]

theorem quasisimple_map_mk {G : Type*} [Group G] (D H : Subgroup G) (hHD : H ≤ D)
    {N : Subgroup ↥D} [N.Normal] (hN : Function.Injective (QuotientGroup.mk' N))
    (hq : CFSG.IsQuasisimple ↥H) :
    CFSG.IsQuasisimple ↥((H.subgroupOf D).map (QuotientGroup.mk' N)) := by
  let e : ↥H ≃* ↥((H.subgroupOf D).map (QuotientGroup.mk' N)) :=
    (Subgroup.subgroupOfEquivOfLe hHD).symm.trans
      ((H.subgroupOf D).equivMapOfInjective (QuotientGroup.mk' N) hN)
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq

variable {G : Type} [Group G] [Finite G]

theorem thm5_two_factors (hT5 : AschbacherTheorem5Statement)
    {A B : Subgroup G} (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hqA : CFSG.IsQuasisimple ↥A) (hqB : CFSG.IsQuasisimple ↥B) (hAB : A ≠ B)
    (hodd : ∀ N : Subgroup ↥(A ⊔ B), N.Normal → Odd (Nat.card N) → N = ⊥)
    (hperm : ∀ h ∈ normalizer ((A ⊔ B : Subgroup G) : Set G),
      (A.map (MulAut.conj h).toMonoidHom = A ∨ A.map (MulAut.conj h).toMonoidHom = B) ∧
      (B.map (MulAut.conj h).toMonoidHom = A ∨ B.map (MulAut.conj h).toMonoidHom = B))
    (hi : ∀ (P Q : Subgroup G), (P = A ∨ P = B) → (Q = A ∨ Q = B) → ∀ t g : G,
      (∃ k : ℕ, t ^ (2 ^ k) = 1) → t ∉ Subgroup.center G → (∀ a ∈ P, t * a = a * t) →
      (∀ a ∈ Q, (g⁻¹ * t * g) * a = a * (g⁻¹ * t * g)) →
      g ∈ normalizer ((A ⊔ B : Subgroup G) : Set G))
    (hii : ∀ (P : Subgroup G), (P = A ∨ P = B) → ∀ g : G,
      P ≤ (normalizer ((A ⊔ B : Subgroup G) : Set G)).map (MulAut.conj g⁻¹).toMonoidHom →
      g ∈ normalizer ((A ⊔ B : Subgroup G) : Set G))
    (hH : normalizer ((A ⊔ B : Subgroup G) : Set G) ≠ ⊤) :
    CFSG.Open.pRank 2 A = 1 := by
  set D : Subgroup G := A ⊔ B with hD
  have hAD : A ≤ D := le_sup_left
  have hBD : B ≤ D := le_sup_right
  have hO : aschbacherThm5OddCore ↥D = ⊥ := by
    refine le_bot_iff.1 (sSup_le fun N hN => ?_)
    exact (hodd N hN.1 hN.2).le
  have hcoreG : aschbacherThm5Core D = ⊥ := by
    unfold aschbacherThm5Core
    rw [hO, Subgroup.map_bot]
  let mk : ↥D →* ↥D ⧸ aschbacherThm5OddCore ↥D := QuotientGroup.mk' _
  have hmk : Function.Injective mk := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hO]
  let P : Fin 2 → Subgroup G := ![A, B]
  let Abar : Fin 2 → Subgroup (↥D ⧸ aschbacherThm5OddCore ↥D) :=
    fun i => ((P i).subgroupOf D).map mk
  have hP0 : P 0 = A := rfl
  have hP1 : P 1 = B := rfl
  have hPi : ∀ i, P i = A ∨ P i = B := by
    intro i; fin_cases i
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hPD : ∀ i, P i ≤ D := fun i => by
    rcases hPi i with h | h
    · rw [h]; exact hAD
    · rw [h]; exact hBD
  have hpre : ∀ i, aschbacherThm5Preimage D (Abar i) = P i := by
    intro i
    unfold aschbacherThm5Preimage
    have h1 : (Abar i).comap (QuotientGroup.mk' (aschbacherThm5OddCore ↥D)) =
        (P i).subgroupOf D := Subgroup.comap_map_eq_self_of_injective hmk _
    rw [h1, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 (hPD i)]
  have hqP : ∀ i, CFSG.IsQuasisimple ↥(P i) := fun i => by
    rcases hPi i with h | h
    · rw [h]; exact hqA
    · rw [h]; exact hqB
  have hdistinct : Function.Injective Abar := by
    intro i j hij
    by_contra hne
    have hPij : P i = P j := by rw [← hpre i, ← hpre j, hij]
    fin_cases i <;> fin_cases j
    · exact hne rfl
    · exact hAB hPij
    · exact hAB hPij.symm
    · exact hne rfl
  have hsemi : ∀ i, aschbacherThm5IsSemisimple (Abar i) := by
    intro i
    refine ⟨1, fun _ => Abar i, Nat.one_pos, fun _ => ⟨le_rfl, ?_⟩, ?_, ?_⟩
    · have := quasisimple_map_mk D (P i) (hPD i) hmk (hqP i)
      exact ⟨Group.isPerfect_def.1 this.1, this.2.1⟩
    · intro l m hlm
      exact absurd (Subsingleton.elim l m) hlm
    · exact iSup_const
  have hcommP : ∀ i j, i ≠ j → ∀ a ∈ P i, ∀ b ∈ P j, a * b = b * a := by
    intro i j hij a ha b hb
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact hcomm a ha b hb
    · exact (hcomm b hb a ha).symm
    · exact absurd rfl hij
  have hcommq : ∀ i j, i ≠ j → ∀ x ∈ Abar i, ∀ y ∈ Abar j, x * y = y * x := by
    intro i j hij x hx y hy
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact hcommP i j hij x' (Subgroup.mem_subgroupOf.1 hx') y' (Subgroup.mem_subgroupOf.1 hy')
  have hgen : ⨆ i, Abar i = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherThm5OddCore ↥D) x
    have hd : (d : G) ∈ A ⊔ B := d.2
    obtain ⟨a, ha, b, hb, hab⟩ := mem_sup_of_commute hcomm hd
    have hdab : d = ⟨a, hAD ha⟩ * ⟨b, hBD hb⟩ := Subtype.ext hab
    rw [hdab, map_mul]
    refine Subgroup.mul_mem _ (Subgroup.mem_iSup_of_mem 0 ⟨⟨a, hAD ha⟩, ?_, rfl⟩)
      (Subgroup.mem_iSup_of_mem 1 ⟨⟨b, hBD hb⟩, ?_, rfl⟩)
    · exact Subgroup.mem_subgroupOf.2 ha
    · exact Subgroup.mem_subgroupOf.2 hb
  have hperm' : ∀ h ∈ normalizer (D : Set G), ∀ i, ∃ j,
      (aschbacherThm5Preimage D (Abar i)).map (MulAut.conj h).toMonoidHom =
        aschbacherThm5Preimage D (Abar j) := by
    intro h hh i
    obtain ⟨h1, h2⟩ := hperm h hh
    rw [hpre i]
    fin_cases i
    · rcases h1 with h1 | h1
      · exact ⟨0, by rw [hpre 0]; exact h1⟩
      · exact ⟨1, by rw [hpre 1]; exact h1⟩
    · rcases h2 with h2 | h2
      · exact ⟨0, by rw [hpre 0]; exact h2⟩
      · exact ⟨1, by rw [hpre 1]; exact h2⟩
  have hi' : ∀ (i j : Fin 2) (t g : G), (∃ k : ℕ, t ^ (2 ^ k) = 1) → t ∉ Subgroup.center G →
      aschbacherThm5Centralizes (aschbacherThm5Core D) (aschbacherThm5Preimage D (Abar i)) t →
      aschbacherThm5Centralizes (aschbacherThm5Core D) (aschbacherThm5Preimage D (Abar j))
        (g⁻¹ * t * g) →
      g ∈ normalizer (D : Set G) := by
    intro i j t g h2 htc hc1 hc2
    refine hi (P i) (P j) (hPi i) (hPi j) t g h2 htc ?_ ?_
    · intro a ha
      have := hc1 a (by rw [hpre i]; exact ha)
      rw [hcoreG, Subgroup.mem_bot] at this
      exact comm_of_commutator_eq_one this
    · intro a ha
      have := hc2 a (by rw [hpre j]; exact ha)
      rw [hcoreG, Subgroup.mem_bot] at this
      exact comm_of_commutator_eq_one this
  have hii' : ∀ (i : Fin 2) (g : G) (X : Subgroup G),
      X ≤ (normalizer (D : Set G)).map (MulAut.conj g⁻¹).toMonoidHom →
      (∀ a ∈ aschbacherThm5Preimage D (Abar i), ∃ x ∈ X, ∃ o ∈ aschbacherThm5Core D,
        a = x * o) →
      g ∈ normalizer (D : Set G) := by
    intro i g X hX hsub
    refine hii (P i) (hPi i) g fun a ha => ?_
    obtain ⟨x, hx, o, ho, hao⟩ := hsub a (by rw [hpre i]; exact ha)
    rw [hcoreG, Subgroup.mem_bot] at ho
    rw [ho, mul_one] at hao
    rw [hao]
    exact hX hx
  have hres := hT5 G D 2 (by norm_num) Abar hdistinct hsemi hcommq hgen hperm' hi' hii' hH
  rcases hres with h1 | ⟨-, h2⟩
  · exact absurd h1 (by norm_num)
  · have := (h2 0 1 (by decide)).2.1
    rw [hpre 0] at this
    exact this

end CFSG.GH74.E2.Box
