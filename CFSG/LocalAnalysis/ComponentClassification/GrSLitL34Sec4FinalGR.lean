module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4FinalGSyl
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4FinalGThree

public section

namespace CFSG.ComponentClassification.GrSLit.FinalG

open CFSG Subgroup CFSG.ComponentClassification

theorem inv_mul_mem_of_relIndex_two {G : Type} [Group G] {H K : Subgroup G} (h2 : H.relIndex K = 2)
    {x y : G} (hx : x ∈ K) (hy : y ∈ K) (hxH : x ∉ H) (hyH : y ∉ H) : x⁻¹ * y ∈ H := by
  have h := Subgroup.mul_mem_iff_of_index_two (H := H.subgroupOf K) h2
    (a := ⟨x⁻¹, inv_mem hx⟩) (b := ⟨y, hy⟩)
  rw [mem_subgroupOf, mem_subgroupOf, mem_subgroupOf] at h
  refine h.mpr ⟨fun h1 => absurd (by simpa using inv_mem h1) hxH, fun h1 => absurd h1 hyH⟩

namespace Data

variable {G : Type} [Group G] [Finite G] (D : Data G)

abbrev X : Subgroup G := D.L ⊓ centralizer ({D.a} : Set G)

theorem X_le_Ca : D.X ≤ centralizer ({D.a} : Set G) := inf_le_right

theorem X_le_NB : D.X ≤ normalizer (D.B : Set G) := inf_le_left.trans D.L_le_N_B

theorem X_le_NJ : D.X ≤ normalizer (D.J : Set G) := D.X_le_Ca.trans D.centralizer_le

theorem S_le_X : D.S ≤ D.X := fun s hs =>
  mem_inf.mpr ⟨D.S_le_L hs, mem_centralizer_singleton_iff.mpr (D.a_cent s hs)⟩

abbrev X₀ : Subgroup G := lineKernel D.X D.B D.a D.X_le_Ca D.X_le_NB

theorem mem_X₀ {y : G} : y ∈ D.X₀ ↔ y ∈ D.X ∧ ∀ b ∈ D.B, b⁻¹ * (y⁻¹ * b * y) ∈ zpowers D.a :=
  Iff.rfl

theorem conj_zpow_a {x : G} (hx : x ∈ centralizer ({D.a} : Set G)) (k : ℤ) :
    x * D.a ^ k * x⁻¹ = D.a ^ k := by
  have hxa : x * D.a * x⁻¹ = D.a := by
    rw [mem_centralizer_singleton_iff.mp hx, mul_inv_cancel_right]
  rw [← conj_zpow, hxa]

theorem X_le_N_X₀ : D.X ≤ normalizer (D.X₀ : Set G) := by
  intro x hx
  refine GrS4.mem_normalizer_of_map_le_self ?_
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨hyX, hyB⟩ := D.mem_X₀.mp hy
  refine D.mem_X₀.mpr ⟨?_, fun b hb => ?_⟩
  · exact mul_mem (mul_mem hx hyX) (inv_mem hx)
  · change b⁻¹ * ((x * y * x⁻¹)⁻¹ * b * (x * y * x⁻¹)) ∈ zpowers D.a
    have hb' : x⁻¹ * b * x ∈ D.B := by
      have := (mem_normalizer_iff.mp (D.X_le_NB (inv_mem hx)) b).mp hb
      rwa [inv_inv] at this
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hyB _ hb')
    rw [show b⁻¹ * ((x * y * x⁻¹)⁻¹ * b * (x * y * x⁻¹)) =
      x * ((x⁻¹ * b * x)⁻¹ * (y⁻¹ * (x⁻¹ * b * x) * y)) * x⁻¹ by group, ← hk,
      D.conj_zpow_a (D.X_le_Ca hx)]
    exact zpow_mem (mem_zpowers _) k

theorem sylow_X : IsSylowTwoIn D.S D.X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := D.sylow
  refine GrS4.isSylowTwoIn_of_not_dvd D.S_le_X D.isPGroup_S fun h => ?_
  have h2 := h.trans (relIndex_dvd_index_of_le D.S_le_X)
  rw [← hP] at h2
  exact P.not_dvd_index h2

theorem sylow_P₀ : IsSylowTwoIn (D.S ⊓ D.X₀) D.X₀ :=
  ⟨inf_le_right, UnbalancedGS.RankProjectiveAction.exists_sylow_inf_of_le_normalizer
    D.S_le_X D.sylow_X.2 (fun _ h => (D.mem_X₀.mp h).1) D.X_le_N_X₀⟩

theorem R_le_X₀ : D.R ≤ D.X₀ := by
  intro r hr
  refine D.mem_X₀.mpr ⟨D.S_le_X hr.1, fun b hb => ?_⟩
  rcases D.R_act hr hb with h | h
  · rw [h, inv_mul_cancel]
    exact one_mem _
  · rw [h, inv_mul_cancel_left]
    exact mem_zpowers _

theorem P₀_inf_J : D.S ⊓ D.X₀ ⊓ D.J = D.R := by
  refine le_antisymm (fun y hy => mem_inf.mpr ⟨(mem_inf.mp (mem_inf.mp hy).1).1,
    (mem_inf.mp hy).2⟩) (fun y hy => mem_inf.mpr ⟨mem_inf.mpr ⟨hy.1, D.R_le_X₀ hy⟩, hy.2⟩)

theorem exists_cycle {b₂ b₃ : G} (hb₂B : b₂ ∈ D.B) (hb₃B : b₃ ∈ D.B) (hb₂1 : b₂ ≠ 1)
    (hb₂a : b₂ ≠ D.a) (hb₃1 : b₃ ≠ 1) (hb₃a : b₃ ≠ D.a) (hb₃b : b₃ ≠ b₂)
    (hb₃ab : b₃ ≠ D.a * b₂) :
    ∃ m ∈ D.L, m ∈ normalizer (D.R : Set G) ∧
      (m⁻¹ * b₂ * m = b₃ ∨ m⁻¹ * b₂ * m = b₃ * D.a) ∧
      (m⁻¹ * b₃ * m = b₃ * b₂ ∨ m⁻¹ * b₃ * m = b₃ * b₂ * D.a) := by
  have hne : ∀ {u v : G} (hu : u ∈ D.B) (hv : v ∈ D.B), u ≠ v →
      (⟨u, hu⟩ : ↥D.B) ≠ ⟨v, hv⟩ := fun _ _ h h' => h (congrArg Subtype.val h')
  obtain ⟨σ, hσa, hσ₂, hσ₃⟩ := exists_mulAut_cycle (E := ↥D.B)
    (fun u v => Subtype.ext (D.B_comm u.2 v.2)) (fun u => Subtype.ext (D.B_sq u.2))
    (a := ⟨D.a, D.a_mem_B⟩) (b₂ := ⟨b₂, hb₂B⟩) (b₃ := ⟨b₃, hb₃B⟩) (hne hb₂B (one_mem _) hb₂1)
    (hne hb₂B D.a_mem_B hb₂a) (hne hb₃B (one_mem _) hb₃1) (hne hb₃B D.a_mem_B hb₃a)
    (hne hb₃B hb₂B hb₃b) (hne hb₃B (mul_mem D.a_mem_B hb₂B) hb₃ab)
  obtain ⟨n, hnN, hn⟩ := D.aut σ
  obtain ⟨c₀, hc₀C, hnc⟩ := GrS4.exists_mul_mem_normalizer D.sylow_T hnN
  have hxb : ∀ b : ↥D.B, (n * c₀)⁻¹ * (b : G) * (n * c₀) = (σ b : G) := by
    intro b
    have h1 := hn b
    have h2 := mem_centralizer_iff.mp hc₀C _ (σ b).2
    calc (n * c₀)⁻¹ * (b : G) * (n * c₀) = c₀⁻¹ * (n⁻¹ * b * n) * c₀ := by group
      _ = (σ b : G) := by rw [h1, mul_assoc, h2, ← mul_assoc, inv_mul_cancel, one_mul]
  have hxa : (n * c₀)⁻¹ * D.a * (n * c₀) = D.a := by
    have := hxb ⟨D.a, D.a_mem_B⟩
    rw [hσa] at this
    exact this
  have hxX : n * c₀ ∈ D.X := by
    refine mem_inf.mpr ⟨hnc, mem_centralizer_singleton_iff.mpr ?_⟩
    calc n * c₀ * D.a = n * c₀ * ((n * c₀)⁻¹ * D.a * (n * c₀)) := by rw [hxa]
      _ = D.a * (n * c₀) := by group
  set x := n * c₀ with hx
  have hP₀2 : IsPGroup 2 ↥(D.S ⊓ D.X₀) := D.isPGroup_S.to_le inf_le_left
  have hVX₀ : (D.S ⊓ D.X₀).map (MulAut.conj x⁻¹).toMonoidHom ≤ D.X₀ := by
    rintro _ ⟨p, hp, rfl⟩
    exact (mem_normalizer_iff.mp (D.X_le_N_X₀ (inv_mem hxX)) p).mp (mem_inf.mp hp).2
  obtain ⟨y, hyX₀, hy⟩ := GrS4.exists_conj_mem_of_isSylowTwoIn D.sylow_P₀ hVX₀ (hP₀2.map _)
  have hmN : (x * y)⁻¹ ∈ normalizer ((D.S ⊓ D.X₀ : Subgroup G) : Set G) := by
    refine GrS4.mem_normalizer_of_map_le_self ?_
    rintro _ ⟨p, hp, rfl⟩
    have h1 := hy _ (mem_map_of_mem (MulAut.conj x⁻¹).toMonoidHom hp)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at h1 ⊢
    rwa [show (x * y)⁻¹ * p * (x * y) = y⁻¹ * (x⁻¹ * p * x) * y by group]
  have hmX : x * y ∈ D.X := mul_mem hxX (D.mem_X₀.mp hyX₀).1
  have hmR : x * y ∈ normalizer (D.R : Set G) := by
    rw [← D.P₀_inf_J]
    exact GrS4.inf_mem_normalizer (by simpa using inv_mem hmN) (D.X_le_NJ hmX)
  have hyB := (D.mem_X₀.mp hyX₀).2
  have hmb : ∀ b : ↥D.B, (x * y)⁻¹ * (b : G) * (x * y) = (σ b : G) ∨
      (x * y)⁻¹ * (b : G) * (x * y) = (σ b : G) * D.a := by
    intro b
    rcases GrS4.eq_one_or_eq_of_mem_zpowers D.a_sq (hyB _ (σ b).2) with h | h
    · left
      calc (x * y)⁻¹ * (b : G) * (x * y) = y⁻¹ * (x⁻¹ * b * x) * y := by group
        _ = (σ b : G) * ((σ b : G)⁻¹ * (y⁻¹ * (σ b : G) * y)) := by rw [hxb]; group
        _ = (σ b : G) := by rw [h, mul_one]
    · right
      calc (x * y)⁻¹ * (b : G) * (x * y) = y⁻¹ * (x⁻¹ * b * x) * y := by group
        _ = (σ b : G) * ((σ b : G)⁻¹ * (y⁻¹ * (σ b : G) * y)) := by rw [hxb]; group
        _ = (σ b : G) * D.a := by rw [h]
  refine ⟨x * y, (mem_inf.mp hmX).1, hmR, ?_, ?_⟩
  · have := hmb ⟨b₂, hb₂B⟩
    rwa [hσ₂] at this
  · have := hmb ⟨b₃, hb₃B⟩
    rwa [hσ₃] at this

theorem R_le_L₁ : D.R ≤ D.L₁ := by
  obtain ⟨b₂, hb₂B, hb₂1, hb₂a, -, -⟩ := GrS4.exists_mem_not_mem_four D.eight.2 1 D.a 1 1
  obtain ⟨b₃, hb₃B, hb₃1, hb₃a, hb₃b, hb₃ab⟩ :=
    GrS4.exists_mem_not_mem_four D.eight.2 1 D.a b₂ (D.a * b₂)
  obtain ⟨m, hmL, hmR, hm₂, hm₃⟩ := D.exists_cycle hb₂B hb₃B hb₂1 hb₂a hb₃1 hb₃a hb₃b hb₃ab
  by_contra hRL
  obtain ⟨r₁, hr₁R, hr₁L⟩ : ∃ r₁ ∈ D.R, r₁ ∉ D.L₁ := by
    by_contra! h
    exact hRL fun x hx => h x hx
  have hR₀ : (D.R ⊓ D.L₁).relIndex D.R = 2 := by
    refine relIndex_eq_two_iff.mpr ⟨r₁, hr₁R, fun b hb => ?_⟩
    by_cases hbL : b ∈ D.L₁
    · refine Or.inr ⟨mem_inf.mpr ⟨hb, hbL⟩, fun h => hr₁L ?_⟩
      have := mul_mem (inv_mem hbL) (mem_inf.mp h).2
      rwa [inv_mul_cancel_left] at this
    · refine Or.inl ⟨mem_inf.mpr ⟨mul_mem hb hr₁R, ?_⟩, fun h => hbL (mem_inf.mp h).2⟩
      have hbc : b * D.c ∈ D.L₁ := (D.mem_L₁_or hb.1).resolve_left hbL
      have hrc : r₁ * D.c ∈ D.L₁ := (D.mem_L₁_or hr₁R.1).resolve_left hr₁L
      have hcr : D.c * r₁ ∈ D.L₁ := by
        have := D.conj_mem_L₁ (D.S_le_L D.c_mem) hrc
        rwa [show D.c * (r₁ * D.c) * D.c⁻¹ = D.c * r₁ by group] at this
      have := mul_mem hbc hcr
      rwa [show b * D.c * (D.c * r₁) = b * (D.c * D.c) * r₁ by group, D.c_sq, mul_one] at this
  have hcardR₀ : Nat.card ↥(D.R ⊓ D.L₁) = 128 := by
    have h := relIndex_mul_card (D.R ⊓ D.L₁) D.R
    rw [hR₀, inf_eq_left.mpr inf_le_left, D.card_R] at h
    omega
  have hT₁R₀ : D.T₁ ≤ D.R ⊓ D.L₁ := le_inf D.T₁_le_R D.T₁_le_L₁
  have hidx : D.T₁.relIndex (D.R ⊓ D.L₁) = 2 := by
    have h := relIndex_mul_card D.T₁ (D.R ⊓ D.L₁)
    rw [inf_eq_left.mpr hT₁R₀, D.card_T₁, hcardR₀] at h
    omega
  obtain ⟨r₀, hr₀, hr₀T⟩ : ∃ r₀ ∈ D.R ⊓ D.L₁, r₀ ∉ D.T₁ := by
    by_contra! h
    have := card_le_of_le (show D.R ⊓ D.L₁ ≤ D.T₁ from h)
    rw [hcardR₀, D.card_T₁] at this
    omega
  have hw : m * r₀ * m⁻¹ ∈ D.R ⊓ D.L₁ :=
    mem_inf.mpr ⟨(mem_normalizer_iff.mp hmR r₀).mp (mem_inf.mp hr₀).1,
      D.conj_mem_L₁ hmL (mem_inf.mp hr₀).2⟩
  have hwT : m * r₀ * m⁻¹ ∉ D.T₁ := fun h => hr₀T ((D.conj_mem_T₁_iff hmL).mp h)
  have ht := inv_mul_mem_of_relIndex_two hidx hr₀ hw hr₀T hwT
  set t := r₀⁻¹ * (m * r₀ * m⁻¹) with htdef
  have hrt : m * r₀ * m⁻¹ = r₀ * t := by rw [htdef]; group
  have hinv : ∀ b ∈ D.B, b ∈ centralizer ({r₀} : Set G) →
      m⁻¹ * b * m ∈ centralizer ({r₀} : Set G) := by
    intro b hb hbr
    rw [mem_centralizer_singleton_iff] at hbr ⊢
    have htb : b * t = t * b := mem_centralizer_iff.mp (D.T₁_le_T.trans D.T_le_C ht) b hb
    calc m⁻¹ * b * m * r₀ = m⁻¹ * b * (m * r₀ * m⁻¹) * m := by group
      _ = m⁻¹ * ((b * r₀) * t) * m := by rw [hrt]; group
      _ = m⁻¹ * (r₀ * (b * t)) * m := by rw [hbr]; group
      _ = m⁻¹ * (r₀ * t) * b * m := by rw [htb]; group
      _ = r₀ * (m⁻¹ * b * m) := by rw [← hrt]; group
  have hr₀C := mem_centralizer_of_cycle D.eight D.a_mem_B hb₂B hb₃B D.a_ne hb₂1 hb₂a hb₃1 hb₃a
    hb₃b hb₃ab (D.a_cent r₀ (mem_inf.mp hr₀).1.1).symm (fun b hb => D.R_act (mem_inf.mp hr₀).1 hb)
    hm₂ hm₃ hinv
  exact hr₀T (mem_inf.mpr ⟨(mem_inf.mp hr₀).1, hr₀C⟩)

end Data

end CFSG.ComponentClassification.GrSLit.FinalG
