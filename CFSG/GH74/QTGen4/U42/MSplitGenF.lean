module

public import CFSG.GH74.QTGen4.U42.MSplitGenC
public import CFSG.GH74.QTGen4.U42.MSplitGenE

public section

namespace CFSG.GH74.QTGen4.U42

variable {G : Type} [Group G]

theorem exists_complement_of_conj {M L V A : Subgroup G}
    (hVL : V ≤ L) (hLM : L ≤ M)
    (hVn : ∀ g ∈ M, ∀ v ∈ V, g * v * g⁻¹ ∈ V)
    (hA : A ≤ L) (hAV : A ⊓ V = ⊥)
    (hconj : ∀ g ∈ M, ∃ w ∈ V, ∀ x : G, x ∈ A ↔ w⁻¹ * (g * x * g⁻¹) * w ∈ A)
    (hfix : ∀ v ∈ V, (∀ a ∈ A, v * a = a * v) → v = 1) :
    ∃ C : Subgroup G, C ≤ M ∧ C ⊓ V = ⊥ ∧ V ⊔ C = M := by
  have hVM : V ≤ M := hVL.trans hLM
  have hAM : A ≤ M := hA.trans hLM
  refine ⟨Subgroup.normalizer (A : Set G) ⊓ M, inf_le_right, ?_, ?_⟩
  ·
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxN, hxM⟩ := Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hx).1
    have hxV : x ∈ V := (Subgroup.mem_inf.mp hx).2
    rw [Subgroup.mem_bot]
    apply hfix x hxV
    intro a ha
    have h1 : x * a * x⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hxN a).mp ha
    have h2 : x * a * x⁻¹ * a⁻¹ ∈ A := A.mul_mem h1 (A.inv_mem ha)
    have h3 : x * a * x⁻¹ * a⁻¹ ∈ V := by
      have e : x * a * x⁻¹ * a⁻¹ = x * (a * x⁻¹ * a⁻¹) := by group
      rw [e]
      exact V.mul_mem hxV (hVn a (hAM ha) x⁻¹ (V.inv_mem hxV))
    have h4 : x * a * x⁻¹ * a⁻¹ = 1 := by
      have hbot : x * a * x⁻¹ * a⁻¹ ∈ A ⊓ V := Subgroup.mem_inf.mpr ⟨h2, h3⟩
      rw [hAV, Subgroup.mem_bot] at hbot
      exact hbot
    have h5 : x * a * x⁻¹ = a := mul_inv_eq_one.mp h4
    calc x * a = (x * a * x⁻¹) * x := by group
      _ = a * x := by rw [h5]
  ·
    apply le_antisymm
    · exact sup_le hVM inf_le_right
    · intro g hg
      obtain ⟨w, hw, hwg⟩ := hconj g hg
      have hwM : w ∈ M := hVM hw
      have hnM : w⁻¹ * g ∈ M := M.mul_mem (M.inv_mem hwM) hg
      have hnN : w⁻¹ * g ∈ Subgroup.normalizer (A : Set G) := by
        rw [Subgroup.mem_normalizer_iff]
        intro x
        have e : w⁻¹ * g * x * (w⁻¹ * g)⁻¹ = w⁻¹ * (g * x * g⁻¹) * w := by group
        rw [e]
        exact hwg x
      have hn : w⁻¹ * g ∈ Subgroup.normalizer (A : Set G) ⊓ M :=
        Subgroup.mem_inf.mpr ⟨hnN, hnM⟩
      have hsplit : g = w * (w⁻¹ * g) := by group
      rw [hsplit]
      exact (V ⊔ (Subgroup.normalizer (A : Set G) ⊓ M)).mul_mem
        (Subgroup.mem_sup_left hw) (Subgroup.mem_sup_right hn)

theorem mem_mul_of_sup {V A : Subgroup G} (hA : ∀ a ∈ A, ∀ v ∈ V, a * v * a⁻¹ ∈ V) {g : G}
    (hg : g ∈ V ⊔ A) : ∃ v ∈ V, ∃ a ∈ A, g = v * a := by
  let P : Subgroup G :=
    { carrier := {g | ∃ v ∈ V, ∃ a ∈ A, g = v * a}
      one_mem' := ⟨1, V.one_mem, 1, A.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨v₁, hv₁, a₁, ha₁, rfl⟩ ⟨v₂, hv₂, a₂, ha₂, rfl⟩
        refine ⟨v₁ * (a₁ * v₂ * a₁⁻¹), V.mul_mem hv₁ (hA a₁ ha₁ v₂ hv₂), a₁ * a₂,
          A.mul_mem ha₁ ha₂, ?_⟩
        group
      inv_mem' := by
        rintro _ ⟨v, hv, a, ha, rfl⟩
        refine ⟨a⁻¹ * v⁻¹ * a, ?_, a⁻¹, A.inv_mem ha, ?_⟩
        · have h := hA a⁻¹ (A.inv_mem ha) v⁻¹ (V.inv_mem hv)
          rwa [inv_inv] at h
        · group }
  have hle : V ⊔ A ≤ P :=
    sup_le (fun v hv => ⟨v, hv, 1, A.one_mem, by simp⟩) (fun a ha => ⟨1, V.one_mem, a, ha, by simp⟩)
  obtain ⟨v, hv, a, ha, hga⟩ := hle hg
  exact ⟨v, hv, a, ha, hga⟩

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.A5Model CFSG.Blueprint
open CFSG.Quasithin.H13 CFSG.Quasithin.H13.A5

namespace Setting

variable [Finite G] {T L V : Subgroup G} (S : A5.Setting G T L V)
include S

theorem exists_complement_of_le (hVL : V ≤ L) (hO : pCoreOf 2 (L ⊔ T) = V) :
    ∃ A : Subgroup G, A ≤ L ⊔ T ∧ A ⊓ V = ⊥ ∧ V ⊔ A = L ⊔ T := by
  have hLTL : L ⊔ T ≤ Subgroup.normalizer (L : Set G) :=
    sup_le Subgroup.le_normalizer S.T_le_NL
  have hLTV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) :=
    sup_le S.frame.L_le S.frame.T_le
  have hVn : ∀ g ∈ L ⊔ T, ∀ v ∈ V, g * v * g⁻¹ ∈ V := fun g hg v hv =>
    (Subgroup.mem_normalizer_iff.mp (hLTV hg) v).mp hv
  have hLn : ∀ g ∈ L ⊔ T, ∀ l ∈ L, g * l * g⁻¹ ∈ L := fun g hg l hl =>
    (Subgroup.mem_normalizer_iff.mp (hLTL hg) l).mp hl
  obtain ⟨A, hAL, hAV, hAVL⟩ := Setting.L_splits S hVL hO
  have hAM : A ≤ L ⊔ T := hAL.trans le_sup_left
  have hVnA : ∀ a ∈ A, ∀ v ∈ V, a * v * a⁻¹ ∈ V := fun a ha => hVn a (hAM ha)
  have hconj : ∀ g ∈ L ⊔ T, ∃ w ∈ V, ∀ x : G, x ∈ A ↔ w⁻¹ * (g * x * g⁻¹) * w ∈ A := by
    intro g hg
    have hg' : g⁻¹ ∈ L ⊔ T := (L ⊔ T).inv_mem hg
    let B : Subgroup G := A.map (MulAut.conj g).toMonoidHom
    have hmemB : ∀ y : G, y ∈ B ↔ g⁻¹ * y * g ∈ A := by
      intro y
      constructor
      · rintro ⟨a, ha, rfl⟩
        have e : g⁻¹ * ((MulAut.conj g).toMonoidHom a) * g = a := by
          change g⁻¹ * (g * a * g⁻¹) * g = a
          group
        rw [e]
        exact ha
      · intro hy
        refine ⟨g⁻¹ * y * g, hy, ?_⟩
        change g * (g⁻¹ * y * g) * g⁻¹ = y
        group
    have hBL : B ≤ L := by
      rintro y ⟨a, ha, rfl⟩
      exact hLn g hg a (hAL ha)
    have hBV : B ⊓ V = ⊥ := by
      rw [eq_bot_iff]
      rintro y hy
      obtain ⟨hyB, hyV⟩ := Subgroup.mem_inf.mp hy
      rw [Subgroup.mem_bot]
      have ha : g⁻¹ * y * g ∈ A := (hmemB y).mp hyB
      have hav : g⁻¹ * y * g ∈ V := by
        have h := hVn g⁻¹ hg' y hyV
        rwa [inv_inv] at h
      have h1 : g⁻¹ * y * g = 1 := by
        have h2 : g⁻¹ * y * g ∈ A ⊓ V := Subgroup.mem_inf.mpr ⟨ha, hav⟩
        rw [hAV, Subgroup.mem_bot] at h2
        exact h2
      calc y = g * (g⁻¹ * y * g) * g⁻¹ := by group
        _ = 1 := by rw [h1, mul_one, mul_inv_cancel]
    have hBL' : V ⊔ B = L := by
      apply le_antisymm
      · exact sup_le hVL hBL
      · intro l hl
        have hl' : g⁻¹ * l * g ∈ L := by
          have h := hLn g⁻¹ hg' l hl
          rwa [inv_inv] at h
        have hmem : g⁻¹ * l * g ∈ V ⊔ A := by
          rw [hAVL]
          exact hl'
        obtain ⟨v, hv, a, ha, hva⟩ := mem_mul_of_sup hVnA hmem
        have hl_eq : l = (g * v * g⁻¹) * (g * a * g⁻¹) := by
          calc l = g * (g⁻¹ * l * g) * g⁻¹ := by group
            _ = g * (v * a) * g⁻¹ := by rw [hva]
            _ = (g * v * g⁻¹) * (g * a * g⁻¹) := by group
        have hgaB : g * a * g⁻¹ ∈ B := by
          refine (hmemB _).mpr ?_
          have e : g⁻¹ * (g * a * g⁻¹) * g = a := by group
          rw [e]
          exact ha
        rw [hl_eq]
        exact (V ⊔ B).mul_mem (Subgroup.mem_sup_left (hVn g hg v hv))
          (Subgroup.mem_sup_right hgaB)
    obtain ⟨w, hw, hwB⟩ := complement_conj S hO hAL hAV hAVL hBL hBV hBL'
    refine ⟨w, hw, fun x => ?_⟩
    rw [← hwB (g * x * g⁻¹), hmemB]
    have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    rw [e]
  have hfixA : ∀ v ∈ V, (∀ a ∈ A, v * a = a * v) → v = 1 := by
    intro v hv hcomm
    have hact : ∀ a ∈ A, pact (rgL S a) (S.frame.ψ ⟨v, hv⟩) = S.frame.ψ ⟨v, hv⟩ := by
      intro a ha
      have hconjv : a * v * a⁻¹ = v := by
        calc a * v * a⁻¹ = v * a * a⁻¹ := by rw [hcomm a ha]
          _ = v := by group
      have key : S.frame.ψ ⟨v, hv⟩ =
          pact (S.frame.ρ ⟨a, S.frame.L_le (hAL ha)⟩) (S.frame.ψ ⟨v, hv⟩) := by
        rw [← S.psi_conj]
        congr 1
        exact Subtype.ext hconjv.symm
      rw [rgL_of_mem S (hAL ha)]
      exact key.symm
    have hallL : ∀ g ∈ L, pact (rgL S g) (S.frame.ψ ⟨v, hv⟩) = S.frame.ψ ⟨v, hv⟩ := by
      intro g hg
      have hgs : g ∈ V ⊔ A := by
        rw [hAVL]
        exact hg
      obtain ⟨w, hw, a, ha, rfl⟩ := mem_mul_of_sup hVnA hgs
      rw [rgL_mul S (hVL hw) (hAL ha), rgL_V S hVL hw, one_mul, hact a ha]
    have hpa : pact pa (S.frame.ψ ⟨v, hv⟩) = S.frame.ψ ⟨v, hv⟩ := by
      obtain ⟨g, hgL, hgρ⟩ := (S.frame.image_L pa).2 pa_sign_one
      have h1 : rgL S (g : G) = pa := by
        rw [rgL_of_mem S hgL]
        exact hgρ
      have h2 := hallL (g : G) hgL
      rw [h1] at h2
      exact h2
    have ht3 : pact t3 (S.frame.ψ ⟨v, hv⟩) = S.frame.ψ ⟨v, hv⟩ := by
      obtain ⟨g, hgL, hgρ⟩ := (S.frame.image_L t3).2 t3_sign_one
      have h1 : rgL S (g : G) = t3 := by
        rw [rgL_of_mem S hgL]
        exact hgρ
      have h2 := hallL (g : G) hgL
      rw [h1] at h2
      exact h2
    have hx1 : S.frame.ψ ⟨v, hv⟩ = 1 := fix_t3 _ hpa ht3
    have h3 : (⟨v, hv⟩ : ↥V) = 1 := S.frame.ψ.injective (by rw [hx1, map_one])
    exact congrArg Subtype.val h3
  obtain ⟨C, hCM, hCV, hVC⟩ :=
    exists_complement_of_conj hVL le_sup_left hVn hAL hAV hconj hfixA
  exact ⟨C, hCM, hCV, hVC⟩

end Setting

end CFSG.GH74.QTGen4.U42

end
