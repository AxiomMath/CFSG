module

public import CFSG.ClassicalInvolution.Sp62Rec.Odd
public import CFSG.ClassicalInvolution.Sp62Rec.CEBasic
public import CFSG.ClassicalInvolution.Sp62Rec.CECent
public import CFSG.ClassicalInvolution.Sp62Rec.CEOdd
public import CFSG.ClassicalInvolution.Sp62Rec.CETheta

public section

namespace CFSG.ClassicalInvolution.Sp62Rec

open CFSG.ClassicalInvolution.Solomon73 CFSG.ClassicalInvolution.Solomon73.Yamaki
  CFSG.ClassicalInvolution.Balance CFSG.Open


theorem alpha_ne_one : alpha ≠ 1 := by
  intro h
  have h5 : yamakiMat 5 ≠ 1 := by decide
  apply h5
  have := congrArg (fun g : StatedSp 3 (ZMod 2) =>
    ((g : GL (Fin 3 ⊕ Fin 3) (ZMod 2)) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2))) h
  simpa [alpha] using this

variable {G : Type} [Group G] [Finite G] {z e : G} {E B : Subgroup G} {T : Sylow 2 G}
  {A X : Subgroup G}

theorem E8ZPkg.ce (P : E8ZPkg z e E B T A X)
    (hS0 : Nat.card S0 = 512) (hH : Nat.card Hhat = 23040)
    (hZ : ∀ x ∈ S0, (∀ y ∈ S0, x * y = y * x) → x = 1 ∨ x = alpha ∨ x = pi12 ∨ x = pi3)
    (hα : Hhat ≤ Subgroup.centralizer ({alpha} : Set (StatedSp 3 (ZMod 2))))
    (hfour : ∀ x : StatedSp 3 (ZMod 2), x = pi12 ∨ x = pi3 →
      ∃ D : Subgroup (StatedSp 3 (ZMod 2)), D ≤ Hhat ∧ Nat.card D = 4 ∧ (∀ d ∈ D, d * d = 1) ∧
        ∀ d ∈ D, d ≠ 1 → ∃ c ∈ Hhat, c * x * c⁻¹ = d)
    (V : Subgroup ↥E0) [V.Normal] (hV : ∀ v ∈ V, v * v = 1)
    (hA6 : Nonempty (↥E0 ⧸ V ≃* alternatingGroup (Fin 6)))
    (hcomm : ∀ f : MulAut V, (∀ (x : ↥E0) (v : V),
      f (MulAut.conjNormal x v) = MulAut.conjNormal x (f v)) → f = 1)
    (hCE0 : ∀ x ∈ Hhat, (∀ y ∈ E0, x * y = y * x) → x = 1 ∨ x = alpha)
    (A0 : Subgroup (StatedSp 3 (ZMod 2)))
    (hA0 : ∀ A' : Subgroup (StatedSp 3 (ZMod 2)), A' ≤ S0 → IsE64 A' → A' = A0) :
    oddCoreIn (Subgroup.centralizer ({e} : Set G)) = ⊥ ∧ oddCoreIn E = ⊥ ∧
      Subgroup.centralizer (E : Set G) = Subgroup.zpowers e ∧
      Subgroup.centralizer ({e} : Set G) = B ∧
      ∃ θ : ↥(Subgroup.centralizer ({e} : Set G)) ≃* ↥Hhat,
        θ ⟨e, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩ = ⟨alpha, alpha_mem_Hhat⟩ ∧
        ((T : Subgroup G).subgroupOf (Subgroup.centralizer ({e} : Set G))).map θ.toMonoidHom =
          S0.subgroupOf Hhat ∧
        (A.subgroupOf (Subgroup.centralizer ({e} : Set G))).map θ.toMonoidHom =
          A0.subgroupOf Hhat ∧
        (E.subgroupOf (Subgroup.centralizer ({e} : Set G))).map θ.toMonoidHom =
          E0.subgroupOf Hhat := by
  have hodd := P.oddCoreIn_centralizer_eq_bot hS0 hH hZ hα hfour
  obtain ⟨φ, hφE, hφe⟩ := P.exists_mulEquiv hodd
  have he1 : e ≠ 1 := by
    rintro rfl
    apply alpha_ne_one
    have h1 : φ ⟨1, P.E_le_B P.e_mem⟩ = 1 := by
      rw [show (⟨1, P.E_le_B P.e_mem⟩ : ↥B) = 1 from rfl, map_one]
    rw [hφe] at h1
    exact congrArg Subtype.val h1
  have hCE := P.centralizer_eq_zpowers hodd φ hφE P.e_mul_self he1 hCE0
  have hCeB := P.centralizer_eq_B φ hφE hCE P.e_mul_self V hV hA6 hcomm
  exact ⟨hodd, P.oddCoreIn_eq_bot hodd, hCE, hCeB,
    P.exists_theta hCeB φ hφE hφe A0 hA0 hS0 hH hα⟩

end CFSG.ClassicalInvolution.Sp62Rec
