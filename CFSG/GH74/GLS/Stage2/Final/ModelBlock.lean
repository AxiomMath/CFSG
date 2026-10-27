module

public import CFSG.GH74.L5U5.ModelsInvolution

public section

namespace CFSG.GH74.GLS.Stage2.Final.ModelBlock

open CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5 Matrix Subgroup

variable {F : Type} [Field F]

abbrev Zs (M : ModelData F) : Subgroup ↥M.K4 := (StatedScalars (Fin 4) F).subgroupOf M.K4

abbrev PG (M : ModelData F) : Type := StatedProj M.K4

abbrev mkP (M : ModelData F) : ↥M.K4 →* PG M := QuotientGroup.mk' (Zs M)

abbrev yP (M : ModelData F) : PG M := mkP M M.yK

theorem mem_Zs {M : ModelData F} {g : ↥M.K4} :
    g ∈ Zs M ↔ ∃ c : Fˣ, Matrix.GeneralLinearGroup.scalar (Fin 4) c = (g : GL (Fin 4) F) := by
  rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range]

theorem mkP_eq_iff {M : ModelData F} {a b : ↥M.K4} :
    mkP M a = mkP M b ↔ ∃ c : Fˣ, (a : GL (Fin 4) F)⁻¹ * (b : GL (Fin 4) F) =
      Matrix.GeneralLinearGroup.scalar (Fin 4) c := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, mem_Zs]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  constructor <;> rintro ⟨c, h⟩ <;> exact ⟨c, h.symm⟩

theorem units_sq_eq_one {c : Fˣ} (h : c * c = 1) : c = 1 ∨ c = -1 := by
  have h' : (c : F) * c = 1 := by
    have := congrArg (fun u : Fˣ => (u : F)) h
    simpa using this
  rcases mul_self_eq_one_iff.1 h' with h2 | h2
  · exact Or.inl (Units.ext h2)
  · exact Or.inr (Units.ext (by simpa using h2))

theorem scalar_injective' {c d : Fˣ}
    (h : (Matrix.GeneralLinearGroup.scalar (Fin 4) c : GL (Fin 4) F) =
      Matrix.GeneralLinearGroup.scalar (Fin 4) d) : c = d := by
  have := congrArg (fun u : GL (Fin 4) F => (u : Matrix (Fin 4) (Fin 4) F) 0 0) h
  simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using Units.ext this

theorem scalar_comm (c : Fˣ) (A : GL (Fin 4) F) :
    A * Matrix.GeneralLinearGroup.scalar (Fin 4) c = Matrix.GeneralLinearGroup.scalar (Fin 4) c * A := by
  have : (Matrix.GeneralLinearGroup.scalar (Fin 4) c : GL (Fin 4) F) ∈
      Subgroup.center (GL (Fin 4) F) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c, rfl⟩
  exact Subgroup.mem_center_iff.1 this A

theorem Zs_le_center (M : ModelData F) : Zs M ≤ Subgroup.center ↥M.K4 := by
  intro s hs
  obtain ⟨c, hc⟩ := mem_Zs.1 hs
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hc]
  exact scalar_comm c _

theorem Zs_normal (M : ModelData F) : (Zs M).Normal := inferInstance

def Nsub (M : ModelData F) : Subgroup ↥M.K4 := (Subgroup.centralizer {yP M}).comap (mkP M)

theorem mem_Nsub {M : ModelData F} {g : ↥M.K4} :
    g ∈ Nsub M ↔ mkP M M.yK * mkP M g = mkP M g * mkP M M.yK := by
  rw [Nsub, Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
  simp

theorem xK_mem_Zs (M : ModelData F) : M.xK ∈ Zs M :=
  mem_Zs.2 ⟨-1, by
    rw [show (M.xK : GL (Fin 4) F) = xGL F from rfl, xGL_eq_neg_one, scalar_neg_one_eq]⟩

theorem Zs_sq_one {M : ModelData F} {s : ↥M.K4} (hs : s ∈ Zs M) (h : s * s = 1) :
    s = 1 ∨ s = M.xK := by
  obtain ⟨c, hc⟩ := mem_Zs.1 hs
  have h1 : (Matrix.GeneralLinearGroup.scalar (Fin 4) (c * c) : GL (Fin 4) F) = 1 := by
    rw [map_mul, hc]
    have := congrArg (fun u : ↥M.K4 => (u : GL (Fin 4) F)) h
    simpa using this
  have h2 : c * c = 1 := by
    apply scalar_injective' (F := F)
    rw [h1, map_one]
  rcases units_sq_eq_one h2 with rfl | rfl
  · left
    apply Subtype.ext
    rw [← hc, map_one]; rfl
  · right
    apply Subtype.ext
    rw [← hc]
    show _ = xGL F
    rw [xGL_eq_neg_one, scalar_neg_one_eq]

theorem mem_Nsub_iff (M : ModelData F) {g : ↥M.K4} :
    g ∈ Nsub M ↔ g * M.yK = M.yK * g ∨ g * M.yK * g⁻¹ = M.xyK := by
  constructor
  · intro hg
    rw [mem_Nsub] at hg
    have h1 : mkP M (M.yK * g) = mkP M (g * M.yK) := by rw [map_mul, map_mul]; exact hg
    have hs : (M.yK * g)⁻¹ * (g * M.yK) ∈ Zs M := by
      rw [← QuotientGroup.eq]
      exact h1
    set s := (M.yK * g)⁻¹ * (g * M.yK) with hsdef
    have hsc : ∀ t : ↥M.K4, t * s = s * t := fun t =>
      (Subgroup.mem_center_iff.1 (Zs_le_center M hs) t)
    have hyy : M.yK * M.yK = 1 := M.yK_mul_self
    have hyinv : M.yK⁻¹ = M.yK := inv_eq_of_mul_eq_one_right hyy
    have ha : g⁻¹ * M.yK * g * M.yK = s := by
      rw [hsdef, _root_.mul_inv_rev, hyinv]
      simp only [mul_assoc]
    have ha2 : (g⁻¹ * M.yK * g) * (g⁻¹ * M.yK * g) = 1 := by
      calc (g⁻¹ * M.yK * g) * (g⁻¹ * M.yK * g) = g⁻¹ * (M.yK * M.yK) * g := by group
        _ = 1 := by rw [hyy]; group
    have hs2 : s * s = 1 := by
      have hsa : s * M.yK = g⁻¹ * M.yK * g := by
        rw [← ha]
        calc g⁻¹ * M.yK * g * M.yK * M.yK = g⁻¹ * M.yK * g * (M.yK * M.yK) := by group
          _ = _ := by rw [hyy, mul_one]
      calc s * s = s * s * (M.yK * M.yK) := by rw [hyy, mul_one]
        _ = (s * M.yK) * (s * M.yK) := by
          calc s * s * (M.yK * M.yK) = s * (s * M.yK) * M.yK := by group
            _ = s * (M.yK * s) * M.yK := by rw [hsc M.yK]
            _ = (s * M.yK) * (s * M.yK) := by group
        _ = 1 := by rw [hsa]; exact ha2
    rcases Zs_sq_one hs hs2 with h | h
    · left
      rw [h] at ha
      have : g⁻¹ * M.yK * g = M.yK := by
        have h3 := congrArg (fun t => t * M.yK) ha
        simp only [one_mul, mul_assoc, hyy, mul_one] at h3
        simpa [mul_assoc] using h3
      calc g * M.yK = g * (g⁻¹ * M.yK * g) := by rw [this]
        _ = M.yK * g := by group
    · right
      rw [h] at ha
      have h3 : g⁻¹ * M.yK * g = M.xyK := by
        have h4 := congrArg (fun t => t * M.yK) ha
        simp only [mul_assoc, hyy, mul_one] at h4
        rw [← M.xK_mul_yK]
        simpa [mul_assoc] using h4
      have hxc := fun t : ↥M.K4 => (Subgroup.mem_center_iff.1 M.xK_mem_center t)
      have hxx := M.xK_mul_self
      have e1 : M.yK = M.xK * (g * M.yK * g⁻¹) := by
        calc M.yK = g * (g⁻¹ * M.yK * g) * g⁻¹ := by group
          _ = g * M.xyK * g⁻¹ := by rw [h3]
          _ = g * (M.xK * M.yK) * g⁻¹ := by rw [M.xK_mul_yK]
          _ = (g * M.xK) * M.yK * g⁻¹ := by group
          _ = (M.xK * g) * M.yK * g⁻¹ := by rw [hxc g]
          _ = M.xK * (g * M.yK * g⁻¹) := by group
      calc g * M.yK * g⁻¹ = (M.xK * M.xK) * (g * M.yK * g⁻¹) := by rw [hxx, one_mul]
        _ = M.xK * (M.xK * (g * M.yK * g⁻¹)) := by group
        _ = M.xK * M.yK := by rw [← e1]
        _ = M.xyK := M.xK_mul_yK
  · rintro (h | h)
    · rw [mem_Nsub, ← map_mul, ← map_mul, h]
    · rw [mem_Nsub, ← map_mul, ← map_mul]
      have e : g * M.yK = M.xK * (M.yK * g) := by
        calc g * M.yK = (g * M.yK * g⁻¹) * g := by group
          _ = M.xyK * g := by rw [h]
          _ = M.xK * (M.yK * g) := by rw [← M.xK_mul_yK, mul_assoc]
      have hx1 : mkP M M.xK = 1 := (QuotientGroup.eq_one_iff _).2 (xK_mem_Zs M)
      rw [e, map_mul (mkP M) M.xK (M.yK * g), hx1, one_mul]

abbrev sc2 (c : Fˣ) : GL (Fin 2) F := Matrix.GeneralLinearGroup.scalar (Fin 2) c

theorem scalar4_eq (c : Fˣ) :
    (Matrix.GeneralLinearGroup.scalar (Fin 4) c : GL (Fin 4) F) = diagGL (sc2 c) (sc2 c) := by
  apply Units.ext
  rw [coe_diagGL, blk4_eq_reindex]
  simp only [Matrix.GeneralLinearGroup.coe_scalar]
  have h : (Matrix.scalar (Fin 2) (c : F) : Matrix (Fin 2) (Fin 2) F) = (c : F) • 1 := by
    rw [Matrix.smul_one_eq_diagonal, Matrix.scalar_apply]
  have hb : Matrix.fromBlocks ((c : F) • (1 : Matrix (Fin 2) (Fin 2) F)) 0 0
      ((c : F) • (1 : Matrix (Fin 2) (Fin 2) F)) =
      (c : F) • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := by
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_smul]
    simp
  rw [h, hb, map_smul, map_one, Matrix.smul_one_eq_diagonal, Matrix.scalar_apply]

theorem sc2_comm (c : Fˣ) (a : GL (Fin 2) F) : sc2 c * a = a * sc2 c := by
  have : sc2 c ∈ Subgroup.center (GL (Fin 2) F) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c, rfl⟩
  exact (Subgroup.mem_center_iff.1 this a).symm

theorem sc2_mul (c d : Fˣ) : sc2 c * sc2 d = sc2 ((c * d : Fˣ)) := (map_mul _ c d).symm

theorem sc2_one : (sc2 (1 : Fˣ) : GL (Fin 2) F) = 1 := map_one _

theorem sc2_inj {c d : Fˣ} (h : (sc2 c : GL (Fin 2) F) = sc2 d) : c = d := by
  have := congrArg (fun u : GL (Fin 2) F => (u : Matrix (Fin 2) (Fin 2) F) 0 0) h
  simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using Units.ext this

theorem wK_mul_self (M : ModelData F) : M.wK * M.wK = 1 := Subtype.ext swapGL_mul_self

abbrev Dsub (M : ModelData F) : Subgroup ↥M.K4 := Subgroup.centralizer {M.yK}

theorem mem_Dsub {M : ModelData F} {g : ↥M.K4} : g ∈ Dsub M ↔ g * M.yK = M.yK * g :=
  Subgroup.mem_centralizer_singleton_iff

theorem mem_Nsub_iff_D (M : ModelData F) {g : ↥M.K4} :
    g ∈ Nsub M ↔ g ∈ Dsub M ∨ M.wK * g ∈ Dsub M := by
  rw [mem_Nsub_iff, mem_Dsub, mem_Dsub]
  have hww := wK_mul_self M
  have hwinv : M.wK⁻¹ = M.wK := inv_eq_of_mul_eq_one_right hww
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · right
      have h1 : M.wK * g * M.yK * (M.wK * g)⁻¹ = M.yK := by
        calc M.wK * g * M.yK * (M.wK * g)⁻¹ = M.wK * (g * M.yK * g⁻¹) * M.wK⁻¹ := by group
          _ = M.wK * M.xyK * M.wK⁻¹ := by rw [h]
          _ = M.yK := M.wK_mul_xyK_mul_inv
      calc M.wK * g * M.yK = (M.wK * g * M.yK * (M.wK * g)⁻¹) * (M.wK * g) := by group
        _ = M.yK * (M.wK * g) := by rw [h1]
  · rintro (h | h)
    · exact Or.inl h
    · right
      have h1 : (M.wK * g) * M.yK * (M.wK * g)⁻¹ = M.yK := by
        calc (M.wK * g) * M.yK * (M.wK * g)⁻¹ = (M.yK * (M.wK * g)) * (M.wK * g)⁻¹ := by rw [h]
          _ = M.yK := by group
      calc g * M.yK * g⁻¹ = M.wK⁻¹ * ((M.wK * g) * M.yK * (M.wK * g)⁻¹) * M.wK⁻¹⁻¹ := by group
        _ = M.wK * M.yK * M.wK⁻¹ := by rw [h1]; simp only [hwinv]
        _ = M.xyK := M.wK_mul_yK_mul_inv

theorem centralizer_yP (M : ModelData F) :
    Subgroup.centralizer {yP M} = (Nsub M).map (mkP M) := by
  rw [Nsub, Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]

theorem mkP_comm_iff {M : ModelData F} {a b : ↥M.K4} :
    mkP M a * mkP M b = mkP M b * mkP M a ↔ ∃ κ : Fˣ,
      (b : GL (Fin 4) F)⁻¹ * (a : GL (Fin 4) F)⁻¹ * ((b : GL (Fin 4) F) * (a : GL (Fin 4) F)) =
        Matrix.GeneralLinearGroup.scalar (Fin 4) κ := by
  rw [← map_mul, ← map_mul, mkP_eq_iff]
  simp only [Subgroup.coe_mul, _root_.mul_inv_rev]

theorem commute_of_inv_mul_eq_one {G : Type*} [Group G] {x y : G} (h : x⁻¹ * y⁻¹ * (x * y) = 1) :
    x * y = y * x := by
  have h2 : x⁻¹ * (y⁻¹ * x * y) = 1 := by simpa [mul_assoc] using h
  have h3 : x = y⁻¹ * x * y := inv_mul_eq_one.1 h2
  calc x * y = y * (y⁻¹ * x * y) := by group
    _ = y * x := by rw [← h3]

theorem diagGL_conj (a b x y : GL (Fin 2) F) :
    diagGL a b * diagGL x y * (diagGL a b)⁻¹ = diagGL (a * x * a⁻¹) (b * y * b⁻¹) := by
  rw [diagGL_inv, diagGL_mul, diagGL_mul]

@[expose] def phiGL {P : Type*} [Group P] (ρ : P →* GL (Fin 2) F) : P × P →* GL (Fin 4) F :=
  (diagGLHom F).comp (ρ.prodMap ρ)

theorem phiGL_apply {P : Type*} [Group P] (ρ : P →* GL (Fin 2) F) (c d : P) :
    phiGL ρ (c, d) = diagGL (ρ c) (ρ d) := rfl

theorem phiGL_mem {M : ModelData F} {P : Type*} [Group P] {ρ : P →* GL (Fin 2) F}
    (hρ : ∀ c, ρ c ∈ M.H2) (c d : P) : phiGL ρ (c, d) ∈ M.K4 := by
  rw [phiGL_apply, M.diagGL_mem_K4_iff]
  obtain ⟨h1, h2⟩ := (M.mem_H2 _).1 (hρ c)
  obtain ⟨h3, h4⟩ := (M.mem_H2 _).1 (hρ d)
  exact ⟨h1, h3, by rw [h2, h4, one_mul]⟩

@[expose] def Phi (M : ModelData F) {P : Type*} [Group P] (ρ : P →* GL (Fin 2) F)
    (hρ : ∀ c, ρ c ∈ M.H2) : P × P →* ↥M.K4 :=
  (phiGL ρ).codRestrict M.K4 (fun x => phiGL_mem hρ x.1 x.2)

theorem Phi_coe (M : ModelData F) {P : Type*} [Group P] (ρ : P →* GL (Fin 2) F)
    (hρ : ∀ c, ρ c ∈ M.H2) (c d : P) :
    ((Phi M ρ hρ (c, d) : ↥M.K4) : GL (Fin 4) F) = diagGL (ρ c) (ρ d) := rfl

theorem swapGL_mul_diagGL_mul_swapGL (a b : GL (Fin 2) F) :
    swapGL F * diagGL a b * swapGL F = diagGL b a := by
  have := swapGL_mul_diagGL_mul_inv a b
  rwa [swapGL_inv] at this

theorem coe_wK (M : ModelData F) : (M.wK : GL (Fin 4) F) = swapGL F := rfl

theorem coe_yK (M : ModelData F) : (M.yK : GL (Fin 4) F) = yGL F := rfl

theorem block_comm_eq {M : ModelData F} {P : Type*} [Group P] (ρ : P →* GL (Fin 2) F)
    (hρ : ∀ c, ρ c ∈ M.H2) {g : ↥M.K4} {a b : GL (Fin 2) F}
    (hab : (g : GL (Fin 4) F) = diagGL a b) (c d : P)
    (hcomm : mkP M g * mkP M (Phi M ρ hρ (c, d)) = mkP M (Phi M ρ hρ (c, d)) * mkP M g) :
    ∃ κ : Fˣ, (ρ c)⁻¹ * a⁻¹ * (ρ c * a) = sc2 κ ∧ (ρ d)⁻¹ * b⁻¹ * (ρ d * b) = sc2 κ := by
  obtain ⟨κ, hκ⟩ := mkP_comm_iff.1 hcomm
  refine ⟨κ, ?_⟩
  rw [Phi_coe, hab, diagGL_inv, diagGL_inv, diagGL_mul, diagGL_mul, diagGL_mul, scalar4_eq] at hκ
  exact diagGL_inj hκ

theorem commute_of_comm_one {x y : GL (Fin 2) F} (h : x⁻¹ * y⁻¹ * (x * y) = sc2 (1 : Fˣ)) :
    y * x = x * y := by
  rw [sc2_one] at h
  exact (commute_of_inv_mul_eq_one h).symm

theorem blockScalar_of_comm (M : ModelData F) (h2 : (2 : F) ≠ 0) {P : Type*} [Group P]
    (ρ : P →* GL (Fin 2) F) (hρ : ∀ c, ρ c ∈ M.H2)
    (hirr : ∀ a : GL (Fin 2) F, (∀ c, a * ρ c = ρ c * a) → ∃ l : Fˣ, a = sc2 l)
    (hnc : ∃ c, ∀ l : Fˣ, ρ c ≠ sc2 l)
    {g : ↥M.K4} (hg : g ∈ Nsub M)
    (hcomm : ∀ c d : P, mkP M g * mkP M (Phi M ρ hρ (c, d)) =
      mkP M (Phi M ρ hρ (c, d)) * mkP M g) :
    ∃ l m : Fˣ, (g : GL (Fin 4) F) = diagGL (sc2 l) (sc2 m) := by
  rcases (mem_Nsub_iff_D M).1 hg with hD | hD
  · have hc : (g : GL (Fin 4) F) * yGL F = yGL F * (g : GL (Fin 4) F) :=
      congrArg Subtype.val (mem_Dsub.1 hD)
    obtain ⟨a, b, hab, -, -, -⟩ := M.exists_diagGL_of_comm h2 g.2 hc
    have key : ∀ c d : P, ∃ κ : Fˣ, (ρ c)⁻¹ * a⁻¹ * (ρ c * a) = sc2 κ ∧
        (ρ d)⁻¹ * b⁻¹ * (ρ d * b) = sc2 κ := fun c d =>
      block_comm_eq ρ hρ hab c d (hcomm c d)
    have ha : ∀ c, a * ρ c = ρ c * a := by
      intro c
      obtain ⟨κ, h1, h2'⟩ := key c 1
      rw [map_one] at h2'
      have : sc2 κ = (1 : GL (Fin 2) F) := by rw [← h2']; group
      rw [this, ← sc2_one (F := F)] at h1
      exact commute_of_comm_one h1
    have hb : ∀ d, b * ρ d = ρ d * b := by
      intro d
      obtain ⟨κ, h1, h2'⟩ := key 1 d
      rw [map_one] at h1
      have : sc2 κ = (1 : GL (Fin 2) F) := by rw [← h1]; group
      rw [this, ← sc2_one (F := F)] at h2'
      exact commute_of_comm_one h2'
    obtain ⟨l, hl⟩ := hirr a ha
    obtain ⟨m, hm⟩ := hirr b hb
    exact ⟨l, m, by rw [hab, hl, hm]⟩
  · exfalso
    have hc : ((M.wK * g : ↥M.K4) : GL (Fin 4) F) * yGL F = yGL F * ((M.wK * g : ↥M.K4) : GL (Fin 4) F) :=
      congrArg Subtype.val (mem_Dsub.1 hD)
    obtain ⟨a, b, hab, -, -, -⟩ := M.exists_diagGL_of_comm h2 (M.wK * g).2 hc
    have hg' : (g : GL (Fin 4) F) = swapGL F * diagGL a b := by
      have h1 : ((M.wK * g : ↥M.K4) : GL (Fin 4) F) = swapGL F * (g : GL (Fin 4) F) := rfl
      rw [h1] at hab
      calc (g : GL (Fin 4) F) = swapGL F * (swapGL F * (g : GL (Fin 4) F)) := by
            rw [← mul_assoc, swapGL_mul_self, one_mul]
        _ = swapGL F * diagGL a b := by rw [hab]
    obtain ⟨c, hc'⟩ := hnc
    obtain ⟨κ, hκ⟩ := mkP_comm_iff.1 (hcomm c 1)
    rw [Phi_coe, hg', map_one] at hκ
    have hginv : ((swapGL F * diagGL a b)⁻¹ : GL (Fin 4) F) = (diagGL a b)⁻¹ * swapGL F := by
      rw [_root_.mul_inv_rev, swapGL_inv]
    have e1 : (diagGL (ρ c) (1 : GL (Fin 2) F))⁻¹ * (swapGL F * diagGL a b)⁻¹ *
        (diagGL (ρ c) 1 * (swapGL F * diagGL a b)) =
        diagGL ((ρ c)⁻¹ * a⁻¹ * 1 * a) (1 * b⁻¹ * ρ c * b) := by
      rw [hginv]
      calc (diagGL (ρ c) (1 : GL (Fin 2) F))⁻¹ * ((diagGL a b)⁻¹ * swapGL F) *
          (diagGL (ρ c) 1 * (swapGL F * diagGL a b))
          = (diagGL (ρ c) (1 : GL (Fin 2) F))⁻¹ * (diagGL a b)⁻¹ *
              (swapGL F * diagGL (ρ c) 1 * swapGL F) * diagGL a b := by group
        _ = diagGL ((ρ c)⁻¹ * a⁻¹ * 1 * a) (1 * b⁻¹ * ρ c * b) := by
          rw [swapGL_mul_diagGL_mul_swapGL, diagGL_inv, diagGL_inv, diagGL_mul, diagGL_mul,
            diagGL_mul]
          simp
    rw [e1, scalar4_eq] at hκ
    have h3 := (diagGL_inj hκ).1
    apply hc' κ⁻¹
    have h4 : (ρ c)⁻¹ = sc2 κ := by simpa using h3
    calc ρ c = ((ρ c)⁻¹)⁻¹ := (inv_inv _).symm
      _ = (sc2 κ)⁻¹ := by rw [h4]
      _ = sc2 κ⁻¹ := (map_inv _ κ).symm

theorem Dsub_le_Nsub (M : ModelData F) : Dsub M ≤ Nsub M := fun _ hg =>
  (mem_Nsub_iff M).2 (Or.inl (mem_Dsub.1 hg))

theorem wK_mem_Nsub (M : ModelData F) : M.wK ∈ Nsub M := by
  rw [mem_Nsub_iff]
  right
  exact M.wK_mul_yK_mul_inv

theorem wK_not_mem_Dsub (M : ModelData F) (h2 : (2 : F) ≠ 0) : M.wK ∉ Dsub M := by
  intro h
  rw [mem_Dsub] at h
  have h1 : M.xyK = M.yK := by
    rw [← M.wK_mul_yK_mul_inv, h]
    group
  have h3 : M.xK = 1 := by
    have : M.xK * M.yK = 1 * M.yK := by rw [M.xK_mul_yK, h1, one_mul]
    exact mul_right_cancel this
  exact xGL_ne_one h2 (congrArg Subtype.val h3)

theorem relIndex_D_N (M : ModelData F) (h2 : (2 : F) ≠ 0) :
    (Dsub M).relIndex (Nsub M) = 2 := by
  rw [Subgroup.relIndex_eq_two_iff]
  refine ⟨M.wK, wK_mem_Nsub M, fun b hb => ?_⟩
  rcases (mem_Nsub_iff_D M).1 hb with hbD | hbD
  ·
    right
    refine ⟨hbD, fun hbw => ?_⟩
    apply wK_not_mem_Dsub M h2
    have := (Dsub M).mul_mem ((Dsub M).inv_mem hbD) hbw
    simpa using this
  ·
    have hbnD : b ∉ Dsub M := by
      intro hbD'
      apply wK_not_mem_Dsub M h2
      have := (Dsub M).mul_mem hbD ((Dsub M).inv_mem hbD')
      simpa using this
    have hbw : b * M.wK ∈ Dsub M := by
      have hmem : b * M.wK ∈ Nsub M := (Nsub M).mul_mem hb (wK_mem_Nsub M)
      rcases (mem_Nsub_iff_D M).1 hmem with h | h
      · exact h
      · exfalso
        apply wK_not_mem_Dsub M h2
        have := (Dsub M).mul_mem ((Dsub M).inv_mem hbD) h
        have e : (M.wK * b)⁻¹ * (M.wK * (b * M.wK)) = M.wK := by group
        rwa [e] at this
    left
    exact ⟨hbw, hbnD⟩

theorem card_Nsub (M : ModelData F) (h2 : (2 : F) ≠ 0) :
    Nat.card ↥(Nsub M) = 2 * Nat.card ↥(Dsub M) := by
  have h := Subgroup.relIndex_mul_card (Dsub M) (Nsub M)
  rw [relIndex_D_N M h2, inf_eq_left.2 (Dsub_le_Nsub M)] at h
  exact h.symm

theorem ker_mkP_le_D (M : ModelData F) : (mkP M).ker ≤ Dsub M := by
  intro g hg
  rw [QuotientGroup.ker_mk'] at hg
  obtain ⟨c, hc⟩ := mem_Zs.1 hg
  rw [mem_Dsub]
  apply Subtype.ext
  change (g : GL (Fin 4) F) * yGL F = yGL F * (g : GL (Fin 4) F)
  rw [← hc]
  exact scalar_comm c _ |>.symm

theorem index_C (M : ModelData F) :
    (Subgroup.centralizer {yP M}).index = (Nsub M).index := by
  rw [centralizer_yP]
  exact Subgroup.index_map_eq (Nsub M) (QuotientGroup.mk'_surjective _)
    ((ker_mkP_le_D M).trans (Dsub_le_Nsub M))

theorem index_C0 (M : ModelData F) (h2 : (2 : F) ≠ 0) :
    ((Dsub M).map (mkP M)).index = 2 * (Nsub M).index := by
  rw [Subgroup.index_map_eq (Dsub M) (QuotientGroup.mk'_surjective _) (ker_mkP_le_D M),
    ← Subgroup.relIndex_mul_index (Dsub_le_Nsub M), relIndex_D_N M h2]

theorem sylow_of_odd_index {G : Type*} [Group G] [Finite G] (C : Subgroup G) (hodd : Odd C.index)
    (P : Sylow 2 ↥C) : ∃ S : Sylow 2 G, (S : Subgroup G) = (P : Subgroup ↥C).map C.subtype := by
  have h1 : Nat.card ((P : Subgroup ↥C).map C.subtype) = 2 ^ (Nat.card G).factorization 2 := by
    rw [Subgroup.card_map_of_injective C.subtype_injective, Sylow.card_eq_multiplicity]
    congr 1
    have hG : C.index * Nat.card C = Nat.card G := Subgroup.index_mul_card C
    rw [← hG, Nat.factorization_mul (Subgroup.index_ne_zero_of_finite) Nat.card_pos.ne']
    have : C.index.factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (Nat.not_even_iff_odd.2 hodd |> fun h => by
        rw [even_iff_two_dvd] at h; exact h)
    simp [this]
  exact ⟨Sylow.ofCard _ h1, Sylow.coe_ofCard _ _⟩

theorem sylow_not_le {G : Type*} [Group G] [Finite G] {C₀ C : Subgroup G} (hodd : Odd C.index)
    (hcard : Nat.card C = 2 * Nat.card C₀) (S : Sylow 2 G) : ¬ (S : Subgroup G) ≤ C₀ := by
  intro hle
  have h1 := Subgroup.card_dvd_of_le hle
  rw [Sylow.card_eq_multiplicity] at h1
  have hG : C.index * Nat.card C = Nat.card G := Subgroup.index_mul_card C
  have hodd2 : C.index.factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (Nat.not_even_iff_odd.2 hodd |> fun h => by
      rw [even_iff_two_dvd] at h; exact h)
  have hC0 : Nat.card C₀ ≠ 0 := Nat.card_pos.ne'
  have hv : (Nat.card G).factorization 2 = (Nat.card C₀).factorization 2 + 1 := by
    rw [← hG, Nat.factorization_mul (Subgroup.index_ne_zero_of_finite) Nat.card_pos.ne', hcard,
      Nat.factorization_mul (by norm_num) hC0]
    simp [hodd2, Nat.Prime.factorization_self Nat.prime_two]
    ring
  rw [hv] at h1
  exact Nat.pow_succ_factorization_not_dvd hC0 Nat.prime_two h1

theorem Phi_mem_Dsub (M : ModelData F) {P : Type*} [Group P] (ρ : P →* GL (Fin 2) F)
    (hρ : ∀ c, ρ c ∈ M.H2) (c d : P) : Phi M ρ hρ (c, d) ∈ Dsub M := by
  rw [mem_Dsub]
  apply Subtype.ext
  change diagGL (ρ c) (ρ d) * yGL F = yGL F * diagGL (ρ c) (ρ d)
  rw [yGL, diagGL_mul, diagGL_mul]
  simp only [mul_neg, neg_mul, mul_one, one_mul]

theorem sc2_inv (c : Fˣ) : (sc2 c : GL (Fin 2) F)⁻¹ = sc2 c⁻¹ :=
  map_inv (Matrix.GeneralLinearGroup.scalar (Fin 2)) c

theorem sc2_conj_mul (a : GL (Fin 2) F) (c d : Fˣ) :
    a⁻¹ * (sc2 c)⁻¹ * a * sc2 d = sc2 (c⁻¹ * d) := by
  have hc : (sc2 c : GL (Fin 2) F)⁻¹ * a = a * (sc2 c)⁻¹ := by
    rw [sc2_inv]; exact sc2_comm _ _
  calc a⁻¹ * (sc2 c)⁻¹ * a * sc2 d = a⁻¹ * ((sc2 c)⁻¹ * a) * sc2 d := by group
    _ = a⁻¹ * (a * (sc2 c)⁻¹) * sc2 d := by rw [hc]
    _ = (sc2 c)⁻¹ * sc2 d := by group
    _ = sc2 (c⁻¹ * d) := by rw [sc2_inv, sc2_mul]

theorem sc2_neg_one : (sc2 (-1 : Fˣ) : GL (Fin 2) F) = -1 := scalar_neg_one_eq 2

theorem center_le (M : ModelData F) (h2 : (2 : F) ≠ 0) {P : Type*} [Group P]
    (ρ : P →* GL (Fin 2) F) (hρ : ∀ c, ρ c ∈ M.H2)
    (hirr : ∀ a : GL (Fin 2) F, (∀ c, a * ρ c = ρ c * a) → ∃ l : Fˣ, a = sc2 l)
    (hnc : ∃ c, ∀ l : Fˣ, ρ c ≠ sc2 l) {S : Subgroup (PG M)}
    (hSC : S ≤ Subgroup.centralizer {yP M})
    (hQS : ∀ c d : P, mkP M (Phi M ρ hρ (c, d)) ∈ S)
    (hout : ∃ h ∈ Nsub M, h ∉ Dsub M ∧ mkP M h ∈ S)
    {z : PG M} (hz : z ∈ S) (hzc : ∀ s ∈ S, s * z = z * s) : z = 1 ∨ z = yP M := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (Zs M) z
  have hgN : g ∈ Nsub M := by
    have := Subgroup.mem_centralizer_iff.1 (hSC hz) (yP M) rfl
    rw [mem_Nsub]
    exact this
  obtain ⟨l, m, hlm⟩ := blockScalar_of_comm M h2 ρ hρ hirr hnc hgN
    (fun c d => (hzc _ (hQS c d)).symm)
  obtain ⟨h, hhN, hhD, hhS⟩ := hout
  have hwh : M.wK * h ∈ Dsub M := ((mem_Nsub_iff_D M).1 hhN).resolve_left hhD
  have hc : ((M.wK * h : ↥M.K4) : GL (Fin 4) F) * yGL F =
      yGL F * ((M.wK * h : ↥M.K4) : GL (Fin 4) F) := congrArg Subtype.val (mem_Dsub.1 hwh)
  obtain ⟨a, b, hab, -, -, -⟩ := M.exists_diagGL_of_comm h2 (M.wK * h).2 hc
  have hh' : (h : GL (Fin 4) F) = swapGL F * diagGL a b := by
    have h1 : ((M.wK * h : ↥M.K4) : GL (Fin 4) F) = swapGL F * (h : GL (Fin 4) F) := rfl
    rw [h1] at hab
    calc (h : GL (Fin 4) F) = swapGL F * (swapGL F * (h : GL (Fin 4) F)) := by
          rw [← mul_assoc, swapGL_mul_self, one_mul]
      _ = swapGL F * diagGL a b := by rw [hab]
  obtain ⟨κ, hκ⟩ := mkP_comm_iff.1 (hzc _ hhS).symm
  have hhinv : ((swapGL F * diagGL a b)⁻¹ : GL (Fin 4) F) = (diagGL a b)⁻¹ * swapGL F := by
    rw [_root_.mul_inv_rev, swapGL_inv]
  have e1 : ((swapGL F * diagGL a b)⁻¹ : GL (Fin 4) F) * (diagGL (sc2 l) (sc2 m))⁻¹ *
      ((swapGL F * diagGL a b) * diagGL (sc2 l) (sc2 m)) =
      diagGL (a⁻¹ * (sc2 m)⁻¹ * a * sc2 l) (b⁻¹ * (sc2 l)⁻¹ * b * sc2 m) := by
    rw [hhinv]
    calc (diagGL a b)⁻¹ * swapGL F * (diagGL (sc2 l) (sc2 m))⁻¹ *
          (swapGL F * diagGL a b * diagGL (sc2 l) (sc2 m))
        = (diagGL a b)⁻¹ * (swapGL F * (diagGL (sc2 l) (sc2 m))⁻¹ * swapGL F) * diagGL a b *
          diagGL (sc2 l) (sc2 m) := by group
      _ = diagGL (a⁻¹ * (sc2 m)⁻¹ * a * sc2 l) (b⁻¹ * (sc2 l)⁻¹ * b * sc2 m) := by
        rw [diagGL_inv (sc2 l) (sc2 m), swapGL_mul_diagGL_mul_swapGL, diagGL_inv a b,
          diagGL_mul, diagGL_mul, diagGL_mul]
  rw [hh', hlm, e1, scalar4_eq] at hκ
  obtain ⟨hκ1, hκ2⟩ := diagGL_inj hκ
  have hk1 : m⁻¹ * l = κ := sc2_inj (by rw [← sc2_conj_mul a m l]; exact hκ1)
  have hk2 : l⁻¹ * m = κ := sc2_inj (by rw [← sc2_conj_mul b l m]; exact hκ2)
  have hkk : κ * κ = 1 := by
    calc κ * κ = (m⁻¹ * l) * (l⁻¹ * m) := by rw [hk1, hk2]
      _ = 1 := by group
  rcases units_sq_eq_one hkk with rfl | rfl
  · left
    have hlm' : l = m := by
      calc l = m * (m⁻¹ * l) := by group
        _ = m := by rw [hk1, mul_one]
    have hgZ : g ∈ Zs M := mem_Zs.2 ⟨m, by rw [hlm, hlm', scalar4_eq]⟩
    exact (QuotientGroup.eq_one_iff _).2 hgZ
  · right
    have hlm' : l = m * (-1) := by
      calc l = m * (m⁻¹ * l) := by group
        _ = m * (-1) := by rw [hk1]
    have hg1 : (g : GL (Fin 4) F) = yGL F * Matrix.GeneralLinearGroup.scalar (Fin 4) m := by
      rw [hlm, hlm', scalar4_eq, yGL, diagGL_mul, one_mul, ← sc2_neg_one (F := F), sc2_mul,
        mul_comm m (-1)]
    have hs0 : M.yK⁻¹ * g ∈ Zs M := by
      refine mem_Zs.2 ⟨m, ?_⟩
      change _ = (M.yK : GL (Fin 4) F)⁻¹ * (g : GL (Fin 4) F)
      rw [hg1, coe_yK, ← mul_assoc, inv_mul_cancel, one_mul]
    have hg2 : g = M.yK * (M.yK⁻¹ * g) := by group
    have hs1 : mkP M (M.yK⁻¹ * g) = 1 := (QuotientGroup.eq_one_iff _).2 hs0
    show mkP M g = yP M
    calc mkP M g = mkP M (M.yK * (M.yK⁻¹ * g)) := by rw [← hg2]
      _ = yP M := by rw [map_mul, hs1, mul_one]

theorem yP_sq (M : ModelData F) : yP M * yP M = 1 := by
  rw [← map_mul, M.yK_mul_self, map_one]

theorem yP_ne_one (M : ModelData F) (h2 : (2 : F) ≠ 0) : yP M ≠ 1 := by
  intro h
  have hy : M.yK ∈ Zs M := (QuotientGroup.eq_one_iff _).1 h
  obtain ⟨c, hc⟩ := mem_Zs.1 hy
  rw [scalar4_eq] at hc
  have h1 : (diagGL (sc2 c) (sc2 c) : GL (Fin 4) F) = diagGL (-1 : GL (Fin 2) F) 1 := hc
  obtain ⟨h3, h4⟩ := diagGL_inj h1
  exact ModelData.neg_one_ne_one_gl2 h2 (h3.symm.trans h4)

theorem orderOf_yP (M : ModelData F) (h2 : (2 : F) ≠ 0) : orderOf (yP M) = 2 :=
  orderOf_eq_prime (by rw [sq]; exact yP_sq M) (yP_ne_one M h2)

theorem exists_sylow_center [Finite F] (M : ModelData F) (h2 : (2 : F) ≠ 0)
    (hodd : Odd (Nsub M).index) {P : Type*} [Group P] (ρ : P →* GL (Fin 2) F)
    (hρ : ∀ c, ρ c ∈ M.H2)
    (hirr : ∀ a : GL (Fin 2) F, (∀ c, a * ρ c = ρ c * a) → ∃ l : Fˣ, a = sc2 l)
    (hnc : ∃ c, ∀ l : Fˣ, ρ c ≠ sc2 l) (hP2 : IsPGroup 2 (P × P)) :
    ∃ S : Sylow 2 (PG M),
      (Subgroup.center ↥(S : Subgroup (PG M))).map (S : Subgroup (PG M)).subtype =
        Subgroup.zpowers (yP M) := by
  classical
  set C : Subgroup (PG M) := Subgroup.centralizer {yP M} with hCdef
  have hCindex : C.index = (Nsub M).index := index_C M
  set Qbar : Subgroup (PG M) := ((mkP M).comp (Phi M ρ hρ)).range with hQdef
  have hQC : Qbar ≤ C := by
    rintro _ ⟨x, rfl⟩
    rw [hCdef, centralizer_yP]
    exact ⟨Phi M ρ hρ x, Dsub_le_Nsub M (Phi_mem_Dsub M ρ hρ x.1 x.2), rfl⟩
  have hQp : IsPGroup 2 ↥Qbar :=
    hP2.of_surjective ((mkP M).comp (Phi M ρ hρ)).rangeRestrict
      (MonoidHom.rangeRestrict_surjective _)
  have hQ' : IsPGroup 2 ↥(Qbar.subgroupOf C) :=
    hQp.of_injective (Subgroup.subgroupOfEquivOfLe hQC).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hQC).injective
  obtain ⟨Pc, hPc⟩ := hQ'.exists_le_sylow
  obtain ⟨S, hS⟩ := sylow_of_odd_index C (by rw [hCindex]; exact hodd) Pc
  have hSC : (S : Subgroup (PG M)) ≤ C := by
    rw [hS]; exact Subgroup.map_subtype_le _
  have hQS : ∀ c d : P, mkP M (Phi M ρ hρ (c, d)) ∈ (S : Subgroup (PG M)) := by
    intro c d
    have hx : mkP M (Phi M ρ hρ (c, d)) ∈ Qbar := ⟨(c, d), rfl⟩
    rw [hS]
    refine ⟨⟨_, hQC hx⟩, hPc ?_, rfl⟩
    exact Subgroup.mem_subgroupOf.2 hx
  have hout : ∃ h ∈ Nsub M, h ∉ Dsub M ∧ mkP M h ∈ (S : Subgroup (PG M)) := by
    by_contra hno
    push Not at hno
    set C₀ : Subgroup (PG M) := (Dsub M).map (mkP M) with hC₀
    have hSle : (S : Subgroup (PG M)) ≤ C₀ := by
      intro x hx
      have hxC := hSC hx
      rw [hCdef, centralizer_yP] at hxC
      obtain ⟨h, hh, rfl⟩ := hxC
      by_cases hhD : h ∈ Dsub M
      · exact ⟨h, hhD, rfl⟩
      · exact absurd hx (hno h hh hhD)
    have hcard : Nat.card C = 2 * Nat.card C₀ := by
      have h1 : C.index * Nat.card C = Nat.card (PG M) := Subgroup.index_mul_card C
      have h2' : C₀.index * Nat.card C₀ = Nat.card (PG M) := Subgroup.index_mul_card C₀
      have h3 : C₀.index = 2 * C.index := by
        rw [hC₀, index_C0 M h2, hCindex, mul_comm]
      rw [h3] at h2'
      have hpos : 0 < C.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
      apply Nat.eq_of_mul_eq_mul_left hpos
      rw [h1, ← h2']
      ring
    exact sylow_not_le (by rw [hCindex]; exact hodd) hcard S hSle
  have hz : ∀ z : PG M, z ∈ (S : Subgroup (PG M)) → (∀ s ∈ (S : Subgroup (PG M)), s * z = z * s) →
      z = 1 ∨ z = yP M := fun z hzS hzc =>
    center_le M h2 ρ hρ hirr hnc hSC hQS hout hzS hzc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial ↥(S : Subgroup (PG M)) := by
    obtain ⟨c, hc⟩ := hnc
    refine ⟨⟨⟨mkP M (Phi M ρ hρ (c, 1)), hQS c 1⟩, 1, ?_⟩⟩
    intro h
    have h1 : mkP M (Phi M ρ hρ (c, 1)) = 1 := congrArg Subtype.val h
    have h2' : Phi M ρ hρ (c, 1) ∈ Zs M := (QuotientGroup.eq_one_iff _).1 h1
    obtain ⟨κ, hκ⟩ := mem_Zs.1 h2'
    rw [scalar4_eq, Phi_coe, map_one] at hκ
    obtain ⟨h5, -⟩ := diagGL_inj hκ
    exact hc κ h5.symm
  have : Nontrivial ↥(Subgroup.center ↥(S : Subgroup (PG M))) :=
    (S.isPGroup').center_nontrivial
  refine ⟨S, ?_⟩
  obtain ⟨⟨z, hzcen⟩, hz1⟩ := exists_ne (1 : ↥(Subgroup.center ↥(S : Subgroup (PG M))))
  have hzcen' := Subgroup.mem_center_iff.1 hzcen
  have hz' : (z : PG M) = 1 ∨ (z : PG M) = yP M :=
    hz z z.2 (fun s hs => by
      have := hzcen' ⟨s, hs⟩
      exact congrArg Subtype.val this)
  have hzy : (z : PG M) = yP M := by
    rcases hz' with h | h
    · exfalso
      apply hz1
      apply Subtype.ext
      apply Subtype.ext
      exact h
    · exact h
  ext x
  constructor
  · rintro ⟨⟨s, hsS⟩, hs, hx⟩
    change s = x at hx
    subst hx
    have hsc := Subgroup.mem_center_iff.1 hs
    rcases hz s hsS (fun t ht => by
      have := hsc ⟨t, ht⟩
      exact congrArg Subtype.val this) with h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact Subgroup.mem_zpowers _
  · intro hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    refine ⟨z ^ n, Subgroup.zpow_mem _ hzcen n, ?_⟩
    rw [map_zpow, Subgroup.coe_subtype, hzy]

end CFSG.GH74.GLS.Stage2.Final.ModelBlock
