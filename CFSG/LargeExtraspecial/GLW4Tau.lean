module

public import CFSG.LargeExtraspecial.GLW4TauB
public import CFSG.LargeExtraspecial.GLW4Trans
public import CFSG.LargeExtraspecial.GLW4Lift
public import CFSG.LargeExtraspecial.GLW4TauA

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.GLW4

open Subgroup Module Matrix QuadraticMap CFSG.LargeExtraspecial.GLR CFSG.GH74.GLS.Bg.Thompson
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {C : Config S}

theorem exists_lifts (e : Basis (Fin 4) (ZMod 2) C.At) {τ : G} (hτM : τ ∈ S.M) (hτX : τ ∉ C.X)
    (hττ : τ * τ = 1) (hJ : gram C e (S.ρ ⟨τ, hτM⟩) = J) :
    ∃ (l₁ l₂ : G) (y₁ y₂ : C.Xbar) (hl₁ : l₁ ∈ S.M) (hl₂ : l₂ ∈ S.M),
      l₁ * τ = τ * l₁ ∧ l₂ * τ = τ * l₂ ∧ S.ρ ⟨l₁, hl₁⟩ = y₁ ∧ S.ρ ⟨l₂, hl₂⟩ = y₂ ∧
        matX C e y₁ = c₁ ∧ matX C e y₂ = c₂ := by
  set s := S.ρ ⟨τ, hτM⟩
  have hs : s ∈ S.Mbar := Config.ρ_mem_Mbar _
  have hsX : s ∉ C.Xbar := Config.ρ_not_mem_Xbar hτM hτX
  obtain ⟨xP, hxP⟩ := exists_matX_eq e P_mul_P P_mul_P
  obtain ⟨xb₁, hxb₁⟩ := exists_matX_eq e b₁_mul_b₁inv b₁inv_mul_b₁
  obtain ⟨xa₂, hxa₂⟩ := exists_matX_eq e a₂_mul_a₂inv a₂inv_mul_a₂
  obtain ⟨xb₂, hxb₂⟩ := exists_matX_eq e b₂_mul_b₂inv b₂inv_mul_b₂
  have cP := commute_of_sp e hs hsX hJ hxP P_mul_P sp_P
  have cb₁ := commute_of_sp e hs hsX hJ hxb₁ b₁inv_mul_b₁ sp_b₁inv
  have ca₂ := commute_of_sp e hs hsX hJ hxa₂ a₂inv_mul_a₂ sp_a₂inv
  have cb₂ := commute_of_sp e hs hsX hJ hxb₂ b₂inv_mul_b₂ sp_b₂inv
  obtain ⟨l₁, hl₁, hl₁τ, hρ₁⟩ := exists_lift_commutator e hτM hτX hττ hJ (C.Xbar_le xP.2)
    (C.Xbar_le xb₁.2) cP cb₁
  obtain ⟨l₂, hl₂, hl₂τ, hρ₂⟩ := exists_lift_commutator e hτM hτX hττ hJ (C.Xbar_le xa₂.2)
    (C.Xbar_le xb₂.2) ca₂ cb₂
  refine ⟨l₁, l₂, ⁅xP, xb₁⁆, ⁅xa₂, xb₂⁆, hl₁, hl₂, hl₁τ, hl₂τ, ?_, ?_, ?_, ?_⟩
  · rw [hρ₁]; simp [commutatorElement_def]
  · rw [hρ₂]; simp [commutatorElement_def]
  · rw [matX_commutator e hxP P_mul_P hxb₁ b₁inv_mul_b₁, ← c₁_eq]
  · rw [matX_commutator e hxa₂ a₂inv_mul_a₂ hxb₂ b₂inv_mul_b₂, ← c₂_eq]

theorem cl_conj_lift (e : Basis (Fin 4) (ZMod 2) C.At) {l h : G} {y : C.Xbar} (hl : l ∈ S.M)
    (hρ : S.ρ ⟨l, hl⟩ = y) (hh : h ∈ C.A) {j : Fin 4} (hc : S.cl h = e j) :
    S.cl (l * h * l⁻¹) = ((∑ i, matX C e y i j • e i : C.At) : S.Qt) := by
  rw [Config.cl_conj hl (C.A_le_QG hh), hρ, hc, ← C.resAt_apply y (e j), resAt_basis]

theorem formOf_add_basis (e : Basis (Fin 4) (ZMod 2) C.At) {s : S.O} (hJ : gram C e s = J)
    (i k j : Fin 4) : C.formOf s (e i + e k) (e j) = J i j + J k j := by
  rw [map_add, LinearMap.add_apply]
  have h1 := congrFun (congrFun hJ i) j
  have h2 := congrFun (congrFun hJ k) j
  simp only [gram] at h1 h2
  rw [h1, h2]

theorem commutator_phiOf_eq (e : Basis (Fin 4) (ZMod 2) C.At) {τ : G} (hτM : τ ∈ S.M)
    (hτX : τ ∉ C.X) (hJ : gram C e (S.ρ ⟨τ, hτM⟩) = J) {l h h₀ : G} {y : C.Xbar}
    (hl : l ∈ S.M) (hlτ : l * τ = τ * l) (hρ : S.ρ ⟨l, hl⟩ = y) (hh₀ : h₀ ∈ C.A)
    (hc₀ : S.cl h₀ = e 0) (hh : h ∈ C.A) {j : Fin 4} (hc : S.cl h = e j)
    (hsum : (∑ i, matX C e y i j • e i : C.At) = e 0 + e j) :
    ⁅phiOf τ h, l⁆ = phiOf τ h * phiOf τ (h₀ * h) := by
  have hlX : l ∈ C.X := C.mem_X_iff.mpr ⟨hl, by rw [hρ]; exact y.2⟩
  have hA : l * h * l⁻¹ ∈ C.A := C.conj_mem_A hlX hh
  have hQ : h₀ * h ∈ S.QG := S.QG.mul_mem (C.A_le_QG hh₀) (C.A_le_QG hh)
  have hcl : S.cl (l * h * l⁻¹) = S.cl (h₀ * h) := by
    rw [cl_conj_lift e hl hρ hh hc, hsum, S.cl_mul (C.A_le_QG hh₀) (C.A_le_QG hh), hc₀, hc]
    rfl
  have hφ : phiOf τ (l * h * l⁻¹) = phiOf τ (h₀ * h) := by
    rcases (S.cl_eq_cl_iff (C.A_le_QG hA) hQ).mp hcl with h1 | h1
    · rw [h1]
    · rw [h1, phiOf_mul_z hτM (S.QG_le_M (C.A_le_QG hA))]
  have hsq := phiOf_mul_self_of_formOf hτM hτX hA (formOf_self_eq_zero e hJ _)
  rw [commutator_phiOf hlτ hsq, hφ]

theorem sum_c₁ (e : Basis (Fin 4) (ZMod 2) C.At) : (∑ i, c₁ i 2 • e i) = e 0 + e 2 := by
  simp [Fin.sum_univ_four, c₁]

theorem sum_c₂ (e : Basis (Fin 4) (ZMod 2) C.At) : (∑ i, c₂ i 1 • e i) = e 0 + e 1 := by
  simp [Fin.sum_univ_four, c₂]

theorem commutators_eq_z (e : Basis (Fin 4) (ZMod 2) C.At) {τ : G} (hτM : τ ∈ S.M)
    (hτX : τ ∉ C.X) (hJ : gram C e (S.ρ ⟨τ, hτM⟩) = J) {l₁ l₂ : G} {y₁ y₂ : C.Xbar}
    (hl₁ : l₁ ∈ S.M) (hl₂ : l₂ ∈ S.M) (hl₁τ : l₁ * τ = τ * l₁) (hl₂τ : l₂ * τ = τ * l₂)
    (hρ₁ : S.ρ ⟨l₁, hl₁⟩ = y₁) (hρ₂ : S.ρ ⟨l₂, hl₂⟩ = y₂) (hm₁ : matX C e y₁ = c₁)
    (hm₂ : matX C e y₂ = c₂) {h₀ h₁ h₂ : G} (hh₀ : h₀ ∈ C.A) (hh₁ : h₁ ∈ C.A) (hh₂ : h₂ ∈ C.A)
    (hc₀ : S.cl h₀ = e 0) (hc₁ : S.cl h₁ = e 1) (hc₂ : S.cl h₂ = e 2) :
    ⁅phiOf τ h₂, l₁⁆ * ⁅phiOf τ h₁, l₂⁆ = S.z := by
  rw [commutator_phiOf_eq e hτM hτX hJ hl₁ hl₁τ hρ₁ hh₀ hc₀ hh₂ hc₂ (by rw [hm₁]; exact sum_c₁ e),
    commutator_phiOf_eq e hτM hτX hJ hl₂ hl₂τ hρ₂ hh₀ hc₀ hh₁ hc₁ (by rw [hm₂]; exact sum_c₂ e)]
  have hA₂ : h₀ * h₂ ∈ C.A := C.A.mul_mem hh₀ hh₂
  have hA₁ : h₀ * h₁ ∈ C.A := C.A.mul_mem hh₀ hh₁
  have he₂ : (⟨S.cl (h₀ * h₂), hA₂.2⟩ : C.At) = e 0 + e 2 :=
    Subtype.ext (by
      show S.cl (h₀ * h₂) = ((e 0 + e 2 : C.At) : S.Qt)
      rw [S.cl_mul (C.A_le_QG hh₀) (C.A_le_QG hh₂), hc₀, hc₂]; rfl)
  have he₁ : (⟨S.cl (h₀ * h₁), hA₁.2⟩ : C.At) = e 0 + e 1 :=
    Subtype.ext (by
      show S.cl (h₀ * h₁) = ((e 0 + e 1 : C.At) : S.Qt)
      rw [S.cl_mul (C.A_le_QG hh₀) (C.A_le_QG hh₁), hc₀, hc₁]; rfl)
  have p₂ := (phiOf_mul_eq hτM hτX hh₂ hA₂).2 (by
    rw [he₂, show (⟨S.cl h₂, hh₂.2⟩ : C.At) = e 2 from Subtype.ext hc₂, formOf_add_basis e hJ]
    decide)
  have p₁ := (phiOf_mul_eq hτM hτX hh₁ hA₁).1 (by
    rw [he₁, show (⟨S.cl h₁, hh₁.2⟩ : C.At) = e 1 from Subtype.ext hc₁, formOf_add_basis e hJ]
    decide)
  have e₂ : h₂ * (h₀ * h₂) = h₀ := by
    rw [← mul_assoc, C.A_comm hh₂ hh₀, mul_assoc, C.A_mul_self hh₂, mul_one]
  have e₁ : h₁ * (h₀ * h₁) = h₀ := by
    rw [← mul_assoc, C.A_comm hh₁ hh₀, mul_assoc, C.A_mul_self hh₁, mul_one]
  rw [p₂, p₁, e₂, e₁]
  have hφM : phiOf τ h₀ ∈ S.M := S.QG_le_M (phiOf_mem_QG hτM hτX hh₀)
  have hsq := phiOf_mul_self_of_formOf hτM hτX hh₀ (formOf_self_eq_zero e hJ _)
  calc phiOf τ h₀ * S.z * phiOf τ h₀ = phiOf τ h₀ * (S.z * phiOf τ h₀) := mul_assoc _ _ _
    _ = phiOf τ h₀ * phiOf τ h₀ * S.z := by rw [← S.z_comm hφM, mul_assoc]
    _ = S.z := by rw [hsq, one_mul]

theorem mul_self_eq_one_of_matX (e : Basis (Fin 4) (ZMod 2) C.At) {y : C.Xbar} {g : Mat}
    (hy : matX C e y = g) (hg : g * g = 1) : (y : S.O) * y = 1 := by
  have : y * y = 1 := matX_injective e (by rw [matX_mul, hy, hg, matX_one])
  exact congrArg Subtype.val this

theorem false_of_involution_J [IsSimpleGroup G] (h4 : S.width = 4)
    (e : Basis (Fin 4) (ZMod 2) C.At) {τ : G} (hτM : τ ∈ S.M) (hτX : τ ∉ C.X) (hττ : τ * τ = 1)
    (hJ : gram C e (S.ρ ⟨τ, hτM⟩) = J) : False := by
  obtain ⟨l₁, l₂, y₁, y₂, hl₁, hl₂, hl₁τ, hl₂τ, hρ₁, hρ₂, hm₁, hm₂⟩ :=
    exists_lifts e hτM hτX hττ hJ
  set V : Subgroup S.O := closure {(y₁ : S.O), (y₂ : S.O)}
  have hy₁ := mul_self_eq_one_of_matX e hm₁ c₁_mul_c₁
  have hy₂ := mul_self_eq_one_of_matX e hm₂ c₂_mul_c₂
  have hy₁₂ : (y₁ : S.O) * y₂ = y₂ * y₁ := by
    have : y₁ * y₂ = y₂ * y₁ := matX_injective e (by rw [matX_mul, matX_mul, hm₁, hm₂, c₁_mul_c₂])
    exact congrArg Subtype.val this
  have hV : ∀ v ∈ V, v * v = 1 := fun v hv => mul_self_eq_one_of_mem_closure
    (by
      intro a ha b hb _
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      exacts [Commute.refl _, hy₁₂, hy₁₂.symm, Commute.refl _])
    (by rintro x (rfl | rfl); exacts [hy₁, hy₂]) hv
  set W : Subgroup G := (V.comap S.ρ).map S.M.subtype ⊓ centralizer {τ}
  have hWK : W ≤ centralizer {τ} ⊓ S.M := fun w hw => by
    obtain ⟨⟨m, hm, rfl⟩, hwτ⟩ := hw
    exact ⟨hwτ, m.2⟩
  have hW2 : IsPGroup 2 W := by
    rintro ⟨w, ⟨⟨m, hm, rfl⟩, -⟩⟩
    refine ⟨3, Subtype.ext ?_⟩
    have hmm : S.ρ (m * m) = 1 := by rw [map_mul]; exact hV _ hm
    have hQ : ((m * m : S.M) : G) ∈ S.QG := (S.ρ_eq_one_iff _).mp hmm
    have h4' := S.pow_four_eq_one hQ
    simp only [SubgroupClass.coe_pow, Subgroup.coe_mul, OneMemClass.coe_one,
      Subgroup.coe_subtype] at h4' ⊢
    rw [show ((m : G)) ^ 2 ^ 3 = ((m : G) * m) ^ 4 by rw [← pow_two, ← pow_mul]; norm_num]
    exact h4'
  have hl₁W : l₁ ∈ W := ⟨⟨⟨l₁, hl₁⟩, by
    show S.ρ ⟨l₁, hl₁⟩ ∈ V
    rw [hρ₁]; exact subset_closure (Set.mem_insert _ _), rfl⟩,
    mem_centralizer_singleton_iff.mpr hl₁τ⟩
  have hl₂W : l₂ ∈ W := ⟨⟨⟨l₂, hl₂⟩, by
    show S.ρ ⟨l₂, hl₂⟩ ∈ V
    rw [hρ₂]; exact subset_closure (Set.mem_insert_of_mem _ rfl), rfl⟩,
    mem_centralizer_singleton_iff.mpr hl₂τ⟩
  obtain ⟨T, hWT, hT⟩ := exists_isSylowIn_le hWK hW2
  have hlift : ∀ i : Fin 4, ∃ h ∈ C.A, S.cl h = e i := fun i => by
    obtain ⟨h, hQ, hc⟩ := S.exists_cl (e i : S.Qt)
    exact ⟨h, ⟨hQ, by rw [hc]; exact (e i).2⟩, hc⟩
  obtain ⟨h₀, hh₀, hc₀⟩ := hlift 0
  obtain ⟨h₁, hh₁, hc₁⟩ := hlift 1
  obtain ⟨h₂, hh₂, hc₂⟩ := hlift 2
  have hφT : ∀ {h : G}, h ∈ C.A → phiOf τ h ∈ T := fun {h} hh => by
    refine Levi.centralizer_QG_le hT (Subgroup.mem_inf.mpr ⟨phiOf_mem_QG hτM hτX hh,
      mem_centralizer_singleton_iff.mpr ?_⟩)
    have h1 : τ * phiOf τ h * τ⁻¹ = phiOf τ h :=
      (Config.conj_mul_conj_eq_iff hτM hτX (Or.inl hττ) hh).mpr (formOf_self_eq_zero e hJ _)
    calc phiOf τ h * τ = τ * phiOf τ h * τ⁻¹ * τ := by rw [h1]
      _ = τ * phiOf τ h := by group
  have hzT : S.z ∈ ⁅T, T⁆ := by
    rw [← commutators_eq_z e hτM hτX hJ hl₁ hl₂ hl₁τ hl₂τ hρ₁ hρ₂ hm₁ hm₂ hh₀ hh₁ hh₂ hc₀ hc₁
      hc₂]
    exact mul_mem (commutator_mem_commutator (hφT hh₂) (hWT hl₁W))
      (commutator_mem_commutator (hφT hh₁) (hWT hl₂W))
  have hβ := isGoodForm_of_gram e hJ
  have hS₁G := Levi.sylowIn_centralizer hτM hτX hττ hβ hT hzT
  have hcard := Levi.card_le_of_sylowIn hτM hτX hττ hβ hT
  rw [h4] at hcard
  exact false_of_sylowIn_le C h4 hτM hτX hττ hT hS₁G (by simpa using hcard)

end CFSG.LargeExtraspecial.GLW4
