module

public import CFSG.GH74.QTGen4.Recog.G23.P7.Leaf.VertexLettersB
public import CFSG.GH74.QTGen4.Recog.G23.P7.TriData
public import CFSG.GH74.QTGen4.Recog.G23.P7.Defs

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Recog.G23.P7.VL

variable {G : Type} [Group G]

theorem _root_.CFSG.GH74.QTGen4.Recog.G23.P7.VertexHyp.toVHc {σ a b z : G} {M W : Subgroup G}
    {w₁ w₂ : G} (h : VertexHyp σ a b z M W w₁ w₂) : VHc σ a b z M w₁ w₂ where
  a3 := h.a3
  b3 := h.b3
  rel := h.rel
  z_def := h.z_def
  Ma m hm := (h.M_norm m hm).1
  Mb m hm := (h.M_norm m hm).2
  σ_mem := h.sigma_mem
  σ3 := by
    have := pow_orderOf_eq_one σ
    rwa [h.sigma_ord] at this
  σ_ne := by
    intro h1
    have := h.sigma_ord
    rw [h1, orderOf_one] at this
    omega
  σ_M m hm := (h.sigma_cent m (Subgroup.mem_sup_left hm)).symm
  σ_a := (h.sigma_cent a (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp)))).symm
  σ_b := (h.sigma_cent b (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp)))).symm
  card_M := h.card_M
  exp3 := h.exp3
  comm_le := h.comm_le
  w₁_mem := h.w₁_mem.2.1
  w₁_cent m hm := Subgroup.mem_centralizer_iff.1 h.w₁_mem.2.2 m hm
  w₁_ne := h.w₁_ne
  w₂_mem := (h.W_le h.w₂_mem).1
  w₂_nc := by
    by_contra hcon
    refine h.w₂_not ⟨(h.W_le h.w₂_mem).1, Subgroup.mem_centralizer_iff.2 (fun m hm => ?_)⟩
    by_contra hne
    exact hcon ⟨m, hm, hne⟩
  a_w₁ := Subgroup.mem_centralizer_iff.1 (h.W_le h.w₁_mem.1).2 a (Set.mem_singleton a)
  a_w₂ := Subgroup.mem_centralizer_iff.1 (h.W_le h.w₂_mem).2 a (Set.mem_singleton a)
  z_w₁ := h.W_inv w₁ h.w₁_mem.1
  z_w₂ := h.W_inv w₂ h.w₂_mem

namespace VHc

variable {σ a b z : G} {M : Subgroup G} {w₁ w₂ : G}

theorem flipσ (h : VHc σ a b z M w₁ w₂) : VHc σ⁻¹ a b z M w₁ w₂ :=
  { h with
    σ_mem := inv_mem h.σ_mem
    σ3 := by rw [inv_pow, h.σ3, inv_one]
    σ_ne := inv_ne_one.2 h.σ_ne
    σ_M := fun m hm => (show Commute σ m from h.σ_M m hm).inv_left.eq
    σ_a := (show Commute σ a from h.σ_a).inv_left.eq
    σ_b := (show Commute σ b from h.σ_b).inv_left.eq
    comm_le := fun x hx y hy => by rw [Subgroup.zpowers_inv]; exact h.comm_le x hx y hy }

theorem flipw₁ (h : VHc σ a b z M w₁ w₂) : VHc σ a b z M w₁⁻¹ w₂ :=
  { h with
    w₁_mem := inv_mem h.w₁_mem
    w₁_cent := fun m hm => (show Commute m w₁ from h.w₁_cent m hm).inv_right.eq
    w₁_ne := inv_ne_one.2 h.w₁_ne
    a_w₁ := (show Commute a w₁ from h.a_w₁).inv_right.eq
    z_w₁ := by
      calc z * w₁⁻¹ * z⁻¹ = (z * w₁ * z⁻¹)⁻¹ := by group
        _ = (w₁⁻¹)⁻¹ := by rw [h.z_w₁] }

theorem flipw₂ (h : VHc σ a b z M w₁ w₂) : VHc σ a b z M w₁ w₂⁻¹ :=
  { h with
    w₂_mem := inv_mem h.w₂_mem
    w₂_nc := by
      obtain ⟨m, hm, hne⟩ := h.w₂_nc
      refine ⟨m, hm, fun hc => hne ?_⟩
      exact Commute.inv_right_iff.1 (show Commute m w₂⁻¹ from hc)
    a_w₂ := (show Commute a w₂ from h.a_w₂).inv_right.eq
    z_w₂ := by
      calc z * w₂⁻¹ * z⁻¹ = (z * w₂ * z⁻¹)⁻¹ := by group
        _ = (w₂⁻¹)⁻¹ := by rw [h.z_w₂] }

theorem flipab (h : VHc σ a b z M w₁ w₂) : VHc σ a⁻¹ b⁻¹ z M w₁ w₂ :=
  { h with
    a3 := by rw [inv_pow, h.a3, inv_one]
    b3 := by rw [inv_pow, h.b3, inv_one]
    rel := by simp only [inv_inv]; exact rel_I4 h.rel
    z_def := by
      rw [sq, rel_inv_sq h.a3 h.b3 h.rel]
      exact h.z_def'
    Ma := fun m hm => by simpa using h.Ma' hm
    Mb := fun m hm => by simpa using h.Mb' hm
    σ_a := (show Commute σ a from h.σ_a).inv_right.eq
    σ_b := (show Commute σ b from h.σ_b).inv_right.eq
    a_w₁ := (show Commute a w₁ from h.a_w₁).inv_left.eq
    a_w₂ := (show Commute a w₂ from h.a_w₂).inv_left.eq }

theorem bab_inv_conj (h : VHc σ a b z M w₁ w₂) {w : G} (haw : a * w = w * a)
    (hzw : z * w * z⁻¹ = w⁻¹) : (b * a * b)⁻¹ * w⁻¹ * (b * a * b) = w := by
  have hbab : b * a * b = a⁻¹ * z := by rw [h.z_def']; group
  have haw' : a * w⁻¹ = w⁻¹ * a := (show Commute a w from haw).inv_right.eq
  have hz : z⁻¹ * w⁻¹ * z = w := by
    have : z⁻¹ * w⁻¹ * z = (z⁻¹ * (z * w * z⁻¹) * z) := by rw [hzw]
    rw [this]; group
  rw [hbab]
  calc (a⁻¹ * z)⁻¹ * w⁻¹ * (a⁻¹ * z) = z⁻¹ * (a * w⁻¹ * a⁻¹) * z := by group
    _ = z⁻¹ * (w⁻¹ * a * a⁻¹) * z := by rw [haw']
    _ = z⁻¹ * w⁻¹ * z := by group
    _ = w := hz

end VHc

@[expose] def relCommon : List (List (Fin 5 × Bool)) := vertexBaseU.take 14

@[expose] def relTail : List (List (Fin 5 × Bool)) := (vertexBaseU.drop 14).take 3

@[expose] def hardU : List (Fin 5 × Bool) := vertexBaseU.getD 17 []

@[expose] def hardS : List (Fin 5 × Bool) := vertexBaseS.getD 14 []

theorem baseU_eq : vertexBaseU = relCommon ++ relTail ++ [hardU] := by decide +kernel

theorem baseS_eq : vertexBaseS = relCommon ++ [hardS] ++ relTail := by decide +kernel

theorem cube_rel {x : G} (hx : x ^ 3 = 1) : x * (x * x) = 1 := by
  rw [← hx]; simp [pow_succ, mul_assoc]

theorem comm_pos {x y : G} (h : x * y = y * x) : x * (y * (x⁻¹ * y⁻¹)) = 1 := by
  calc x * (y * (x⁻¹ * y⁻¹)) = (x * y) * (x⁻¹ * y⁻¹) := by group
    _ = (y * x) * (x⁻¹ * y⁻¹) := by rw [h]
    _ = 1 := by group

theorem comm_neg {x y : G} (h : x * y = y * x) : x * (y⁻¹ * (x⁻¹ * y)) = 1 := by
  have h' : x * y⁻¹ = y⁻¹ * x := (show Commute x y from h).inv_right.eq
  calc x * (y⁻¹ * (x⁻¹ * y)) = (x * y⁻¹) * (x⁻¹ * y) := by group
    _ = (y⁻¹ * x) * (x⁻¹ * y) := by rw [h']
    _ = 1 := by group

theorem gword {g : G} (hg : g ^ 3 = 1) (P₀ P₁ P₂ : G) :
    P₀ * (g⁻¹ * (P₁ * (g⁻¹ * (P₂ * g⁻¹)))) = P₀ * cj g P₁ * cj g (cj g P₂) := by
  have e : g⁻¹ = g * g := inv_eq_mul_self hg
  calc P₀ * (g⁻¹ * (P₁ * (g⁻¹ * (P₂ * g⁻¹)))) = P₀ * (g⁻¹ * (P₁ * (g⁻¹ * (P₂ * (g * g))))) := by
        rw [← e]
    _ = _ := by simp only [cj]; group

namespace VHc

variable {σ a b z : G} {M : Subgroup G} {w₁ w₂ : G}

theorem easy_sat (h : VHc σ a b z M w₁ w₂) :
    SatWords (relCommon ++ relTail) (![σ, a, b, w₁, w₂] : Fin 5 → G) := by
  have hw₁c : w₁ * cj b w₁ = cj b w₁ * w₁ := (h.w₁_cent _ (h.cj_b_mem h.w₁_mem)).symm
  have hw₂c : w₂ * cj b w₁ = cj b w₁ * w₂ := h.cent_cj_b h.w₁_cent _ h.w₂_mem
  simp [SatWords, relCommon, relTail, vertexBaseU, FreeGroup.lift_mk]
  refine ⟨cube_rel (h.exp3 _ h.w₂_mem), cube_rel (h.exp3 _ h.w₁_mem), cube_rel h.σ3,
    cube_rel h.a3, cube_rel h.b3, comm_pos (h.w₁_cent _ h.w₂_mem).symm, comm_neg h.a_w₂.symm,
    comm_pos (h.σ_M _ h.w₂_mem), comm_neg h.a_w₁.symm, comm_pos (h.σ_M _ h.w₁_mem),
    comm_neg h.σ_b, comm_neg h.σ_a, ?_, ?_, ?_, ?_, ?_⟩
  · rw [gword h.b3]
    simp only [cj_inv]
    rw [h.D2, inv_inv]
    calc w₁⁻¹ * (cj b w₁)⁻¹ * (w₁ * cj b w₁) = w₁⁻¹ * (cj b w₁)⁻¹ * (cj b w₁ * w₁) := by rw [hw₁c]
      _ = 1 := by group
  · simpa [mul_assoc] using h.rel
  · calc w₂ * (b⁻¹ * (w₁ * (b * (w₂⁻¹ * (b⁻¹ * (w₁⁻¹ * b))))))
        = w₂ * (cj b w₁ * (w₂⁻¹ * (cj b w₁)⁻¹)) := by simp only [cj]; group
      _ = 1 := comm_pos hw₂c
  · calc w₂⁻¹ * (b⁻¹ * (a⁻¹ * (b⁻¹ * (w₂⁻¹ * (b * (a * b))))))
        = w₂⁻¹ * ((b * a * b)⁻¹ * w₂⁻¹ * (b * a * b)) := by group
      _ = 1 := by rw [h.bab_inv_conj h.a_w₂ h.z_w₂]; group
  · calc w₁⁻¹ * (b⁻¹ * (a⁻¹ * (b⁻¹ * (w₁⁻¹ * (b * (a * b))))))
        = w₁⁻¹ * ((b * a * b)⁻¹ * w₁⁻¹ * (b * a * b)) := by group
      _ = 1 := by rw [h.bab_inv_conj h.a_w₁ h.z_w₁]; group

end VHc

theorem satWords_append {X : Type*} [Group X] {m : ℕ} {l₁ l₂ : List (List (Fin m × Bool))}
    {ρ : Fin m → X} : SatWords (l₁ ++ l₂) ρ ↔ SatWords l₁ ρ ∧ SatWords l₂ ρ := by
  unfold SatWords
  constructor
  · intro h
    exact ⟨fun r hr => h r (List.mem_append_left _ hr), fun r hr => h r (List.mem_append_right _ hr)⟩
  · rintro ⟨h1, h2⟩ r hr
    rcases List.mem_append.1 hr with hr | hr
    · exact h1 r hr
    · exact h2 r hr

theorem satWords_singleton {X : Type*} [Group X] {m : ℕ} {r : List (Fin m × Bool)}
    {ρ : Fin m → X} : SatWords [r] ρ ↔ FreeGroup.lift ρ (FreeGroup.mk r) = 1 := by
  simp only [SatWords, List.mem_singleton, forall_eq]

theorem satWords_map_flipWord {X : Type*} [Group X] {m : ℕ} {ws : List (List (Fin m × Bool))}
    {φ : Fin m → Bool} {ρ : Fin m → X} :
    SatWords (ws.map (flipWord φ)) ρ ↔ SatWords ws (flipLetters φ ρ) := by
  simp only [SatWords, List.forall_mem_map, lift_mk_flipWord]

theorem sat_U_iff {ρ : Fin 5 → G} : SatWords vertexBaseU ρ ↔
    SatWords (relCommon ++ relTail) ρ ∧ FreeGroup.lift ρ (FreeGroup.mk hardU) = 1 := by
  rw [baseU_eq, satWords_append, satWords_singleton]

theorem sat_S_iff {ρ : Fin 5 → G} : SatWords vertexBaseS ρ ↔
    SatWords (relCommon ++ relTail) ρ ∧ FreeGroup.lift ρ (FreeGroup.mk hardS) = 1 := by
  rw [baseS_eq, satWords_append, satWords_append, satWords_singleton, satWords_append]
  tauto

theorem hardU_eq : hardU = [(3, true), (0, false), (4, false), (2, false), (4, false), (2, false),
    (4, false), (3, false), (2, false)] := by decide +kernel

theorem hardS_eq : hardS = [(4, false), (0, true), (2, false), (4, false), (2, false), (4, false),
    (2, false)] := by decide +kernel

variable {c : ZMod 3}

theorem lift_hardU {b : G} (hb : b ^ 3 = 1) (Φ : VG c →* G) (T : VG c → VG c)
    (hT : ∀ x, cj b (Φ x) = Φ (T x)) (a : G) (y₀ y₁ y₂ : VG c) :
    FreeGroup.lift (![Φ y₀, a, b, Φ y₁, Φ y₂] : Fin 5 → G) (FreeGroup.mk hardU) =
      Φ (VG.hardUval T y₀ y₁ y₂) := by
  have e : FreeGroup.lift (![Φ y₀, a, b, Φ y₁, Φ y₂] : Fin 5 → G) (FreeGroup.mk hardU) =
      (Φ y₁ * (Φ y₀)⁻¹ * (Φ y₂)⁻¹) * (b⁻¹ * ((Φ y₂)⁻¹ * (b⁻¹ * (((Φ y₂)⁻¹ * (Φ y₁)⁻¹) * b⁻¹)))) := by
    simp [hardU_eq, FreeGroup.lift_mk, mul_assoc]
  rw [e, gword hb]
  simp only [← map_inv, ← map_mul, hT, VG.hardUval]

theorem lift_hardS {b : G} (hb : b ^ 3 = 1) (Φ : VG c →* G) (T : VG c → VG c)
    (hT : ∀ x, cj b (Φ x) = Φ (T x)) (a : G) (y₀ y₁ y₂ : VG c) :
    FreeGroup.lift (![Φ y₀, a, b, Φ y₁, Φ y₂] : Fin 5 → G) (FreeGroup.mk hardS) =
      Φ (VG.hardSval T y₀ y₂) := by
  have e : FreeGroup.lift (![Φ y₀, a, b, Φ y₁, Φ y₂] : Fin 5 → G) (FreeGroup.mk hardS) =
      ((Φ y₂)⁻¹ * Φ y₀) * (b⁻¹ * ((Φ y₂)⁻¹ * (b⁻¹ * ((Φ y₂)⁻¹ * b⁻¹)))) := by
    simp [hardS_eq, FreeGroup.lift_mk, mul_assoc]
  rw [e, gword hb]
  simp only [← map_inv, ← map_mul, hT, VG.hardSval]

theorem satU_flip {φ : Fin 5 → Bool} {ρ : Fin 5 → G} :
    SatWords (vertexBaseU.map (flipWord φ)) ρ ↔ SatWords (relCommon ++ relTail) (flipLetters φ ρ) ∧
      FreeGroup.lift (flipLetters φ ρ) (FreeGroup.mk hardU) = 1 := by
  rw [satWords_map_flipWord, sat_U_iff]

theorem satS_flip {φ : Fin 5 → Bool} {ρ : Fin 5 → G} :
    SatWords (vertexBaseS.map (flipWord φ)) ρ ↔ SatWords (relCommon ++ relTail) (flipLetters φ ρ) ∧
      FreeGroup.lift (flipLetters φ ρ) (FreeGroup.mk hardS) = 1 := by
  rw [satWords_map_flipWord, sat_S_iff]

theorem flip_σ_tuple (σ a b w₁ w₂ : G) :
    flipLetters (flipPat true false false false) (![σ, a, b, w₁, w₂] : Fin 5 → G) =
      ![σ⁻¹, a, b, w₁, w₂] := by
  funext i; fin_cases i <;> simp [flipLetters, flipPat]

theorem flip_ab_tuple (σ a b w₁ w₂ : G) :
    flipLetters (flipPat false true false false) (![σ, a, b, w₁, w₂] : Fin 5 → G) =
      ![σ, a⁻¹, b⁻¹, w₁, w₂] := by
  funext i; fin_cases i <;> simp [flipLetters, flipPat]

theorem flip_w₁_tuple (σ a b w₁ w₂ : G) :
    flipLetters (flipPat false false true false) (![σ, a, b, w₁, w₂] : Fin 5 → G) =
      ![σ, a, b, w₁⁻¹, w₂] := by
  funext i; fin_cases i <;> simp [flipLetters, flipPat]

theorem flip_w₂_tuple (σ a b w₁ w₂ : G) :
    flipLetters (flipPat false false false true) (![σ, a, b, w₁, w₂] : Fin 5 → G) =
      ![σ, a, b, w₁, w₂⁻¹] := by
  funext i; fin_cases i <;> simp [flipLetters, flipPat]

theorem cj_inv_eq {b : G} (hb : b ^ 3 = 1) (x : G) : cj b⁻¹ x = cj b (cj b x) := by
  rw [cj_cj, ← inv_eq_mul_self hb]

namespace VHc

variable {σ a b z : G} {M : Subgroup G} {w₁ w₂ : G}

theorem generation (h : VHc σ a b z M w₁ w₂) :
    Subgroup.closure ({σ, a, b, w₁, w₂} : Set G) = M ⊔ Subgroup.closure ({a, b} : Set G) := by
  obtain ⟨c, hd, η, hc0, hinj, hsurj, -⟩ := h.vertex_coords
  have hσ : σ ∈ Subgroup.closure ({σ, a, b, w₁, w₂} : Set G) := Subgroup.subset_closure (by simp)
  have ha : a ∈ Subgroup.closure ({σ, a, b, w₁, w₂} : Set G) := Subgroup.subset_closure (by simp)
  have hb : b ∈ Subgroup.closure ({σ, a, b, w₁, w₂} : Set G) := Subgroup.subset_closure (by simp)
  have hw₁ : w₁ ∈ Subgroup.closure ({σ, a, b, w₁, w₂} : Set G) := Subgroup.subset_closure (by simp)
  have hw₂ : w₂ ∈ Subgroup.closure ({σ, a, b, w₁, w₂} : Set G) := Subgroup.subset_closure (by simp)
  have hw₁' : cj b w₁ ∈ Subgroup.closure ({σ, a, b, w₁, w₂} : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (inv_mem hb) hw₁) hb
  have hw₂' : cj b w₂ ∈ Subgroup.closure ({σ, a, b, w₁, w₂} : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (inv_mem hb) hw₂) hb
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact Subgroup.mem_sup_left h.σ_mem
    · exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
    · exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
    · exact Subgroup.mem_sup_left h.w₁_mem
    · exact Subgroup.mem_sup_left h.w₂_mem
  · apply sup_le
    · intro m hm
      obtain ⟨x, rfl⟩ := hsurj m hm
      show phi σ w₁ w₂ (cj b w₁) (cj b w₂) x ∈ _
      unfold phi zpw
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.pow_mem _ hσ _)
        (Subgroup.mul_mem _ (Subgroup.pow_mem _ hw₁ _) (Subgroup.pow_mem _ hw₁' _)))
        (Subgroup.mul_mem _ (Subgroup.pow_mem _ hw₂ _) (Subgroup.pow_mem _ hw₂' _))
    · rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ha
      · exact hb

theorem main (h : VHc σ a b z M w₁ w₂) :
    ∃ k : Fin 6, SatWords (vertexRels1 k) (![σ, a, b, w₁, w₂] : Fin 5 → G) ∧
      SatWords (vertexRels2 k) (![σ, a, b, w₁, w₂] : Fin 5 → G) := by
  obtain ⟨c, hd, η, hc0, hinj, hsurj, hτ, hα, hEτ, hEr⟩ := h.vertex_coords
  have hb3' : b⁻¹ ^ 3 = 1 := by rw [inv_pow, h.b3, inv_one]
  have hτ' : ∀ x, cj b⁻¹ (hd.hom x) = hd.hom (VG.tauV η (VG.tauV η x)) := fun x => by
    rw [cj_inv_eq h.b3, hτ, hτ]
  rcases VG.classify c hc0 η hEτ hEr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨0, ?_, ?_⟩ <;>
    · show SatWords vertexBaseU _
      rw [sat_U_iff]
      refine ⟨h.easy_sat, ?_⟩
      have key := lift_hardU h.b3 hd.hom _ hτ a VG.gσ VG.g₁ VG.g₂
      simp only [hd.hom_gσ, hd.hom_g₁, hd.hom_g₂] at key
      rw [key]
      refine (congrArg hd.hom ?_).trans (map_one hd.hom)
      exact VG.check_k0
  · refine ⟨1, ?_, ?_⟩
    · show SatWords (vertexBaseU.map (flipWord (flipPat false false false true))) _
      rw [satU_flip, flip_w₂_tuple]
      refine ⟨h.flipw₂.easy_sat, ?_⟩
      have key := lift_hardU h.b3 hd.hom _ hτ a VG.gσ VG.g₁ VG.g₂⁻¹
      simp only [map_inv, hd.hom_gσ, hd.hom_g₁, hd.hom_g₂] at key
      rw [key]
      refine (congrArg hd.hom ?_).trans (map_one hd.hom)
      exact VG.check_k1a
    · show SatWords (vertexBaseU.map (flipWord (flipPat false false true false))) _
      rw [satU_flip, flip_w₁_tuple]
      refine ⟨h.flipw₁.easy_sat, ?_⟩
      have key := lift_hardU h.b3 hd.hom _ hτ a VG.gσ VG.g₁⁻¹ VG.g₂
      simp only [map_inv, hd.hom_gσ, hd.hom_g₁, hd.hom_g₂] at key
      rw [key]
      refine (congrArg hd.hom ?_).trans (map_one hd.hom)
      exact VG.check_k1b
  · refine ⟨2, ?_, ?_⟩ <;>
    · show SatWords (vertexBaseU.map (flipWord (flipPat false true false false))) _
      rw [satU_flip, flip_ab_tuple]
      refine ⟨h.flipab.easy_sat, ?_⟩
      have key := lift_hardU hb3' hd.hom _ hτ' a⁻¹ VG.gσ VG.g₁ VG.g₂
      simp only [hd.hom_gσ, hd.hom_g₁, hd.hom_g₂] at key
      rw [key]
      refine (congrArg hd.hom ?_).trans (map_one hd.hom)
      exact VG.check_k2
  · refine ⟨3, ?_, ?_⟩ <;>
    · show SatWords (vertexBaseU.map (flipWord (flipPat true false false false))) _
      rw [satU_flip, flip_σ_tuple]
      refine ⟨h.flipσ.easy_sat, ?_⟩
      have key := lift_hardU h.b3 hd.hom _ hτ a VG.gσ⁻¹ VG.g₁ VG.g₂
      simp only [map_inv, hd.hom_gσ, hd.hom_g₁, hd.hom_g₂] at key
      rw [key]
      refine (congrArg hd.hom ?_).trans (map_one hd.hom)
      exact VG.check_k3
  · refine ⟨4, ?_, ?_⟩ <;>
    · show SatWords vertexBaseS _
      rw [sat_S_iff]
      refine ⟨h.easy_sat, ?_⟩
      have key := lift_hardS h.b3 hd.hom _ hτ a VG.gσ VG.g₁ VG.g₂
      simp only [hd.hom_gσ, hd.hom_g₁, hd.hom_g₂] at key
      rw [key]
      refine (congrArg hd.hom ?_).trans (map_one hd.hom)
      exact VG.check_k4
  · refine ⟨5, ?_, ?_⟩ <;>
    · show SatWords (vertexBaseS.map (flipWord (flipPat true false false false))) _
      rw [satS_flip, flip_σ_tuple]
      refine ⟨h.flipσ.easy_sat, ?_⟩
      have key := lift_hardS h.b3 hd.hom _ hτ a VG.gσ⁻¹ VG.g₁ VG.g₂
      simp only [map_inv, hd.hom_gσ, hd.hom_g₁, hd.hom_g₂] at key
      rw [key]
      refine (congrArg hd.hom ?_).trans (map_one hd.hom)
      exact VG.check_k5

end VHc

end CFSG.GH74.QTGen4.Recog.G23.P7.VL
