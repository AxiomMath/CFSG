module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog82P29Lc
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog82P29Sb

public section

namespace CFSG.ComponentClassification.GSThmB.P29

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.ComponentClassification.CatFactsL4U4
  DiagL CSL Subgroup DihedralGroup

section Dih

variable {G : Type*} [Group G] {n : ℕ} [NeZero n] {a b : G} (ha : a ^ n = 1) (hb : b * b = 1)
  (hba : b * a * b⁻¹ = a⁻¹)

theorem commute_dihHom {c : G} (h1 : Commute c a) (h2 : Commute c b) (x : DihedralGroup n) :
    Commute c (dihHom a b ha hb hba x) := by
  cases x with
  | r i =>
    rw [dihHom_r]
    exact h1.pow_right _
  | sr i =>
    rw [dihHom_sr]
    exact h2.mul_right (h1.pow_right _)

theorem dihHom_conj_comm {t : G} (h1 : Commute (t⁻¹ * a * t) a) (h2 : Commute (t⁻¹ * a * t) b)
    (h3 : Commute (t⁻¹ * b * t) a) (h4 : Commute (t⁻¹ * b * t) b) (x y : DihedralGroup n) :
    dihHom a b ha hb hba x * (t⁻¹ * dihHom a b ha hb hba y * t) =
      (t⁻¹ * dihHom a b ha hb hba y * t) * dihHom a b ha hb hba x := by
  have key : ∀ z : G, t⁻¹ * z * t = MulAut.conj t⁻¹ z := fun z => by
    rw [MulAut.conj_apply, inv_inv]
  have hA := commute_dihHom ha hb hba h1 h2 x
  have hB := commute_dihHom ha hb hba h3 h4 x
  suffices h : Commute (t⁻¹ * dihHom a b ha hb hba y * t) (dihHom a b ha hb hba x) from h.eq.symm
  cases y with
  | r j =>
    rw [dihHom_r, key, map_pow, ← key]
    exact hA.pow_left _
  | sr j =>
    rw [dihHom_sr, key, map_mul, map_pow, ← key, ← key]
    exact hB.mul_left (hA.pow_left _)

end Dih

namespace L4M

variable {F : Type} [Field F] [Fintype F]

theorem normJ_JK (h2 : (2 : F) ≠ 0) (hneg : ¬ IsSquare (-1 : F))
    (hJp : ⁅JK F neg_one_ne_zero', JK F neg_one_ne_zero'⁆ = JK F neg_one_ne_zero')
    (hJc : Nat.card F ^ 2 * ((Nat.card F ^ 2) ^ 2 - 1) ≤ 2 * Nat.card (JK F neg_one_ne_zero'))
    {c : projectiveSL 4 F} (hc : c ∈ centralizer ({proj 4 F kSL} : Set (projectiveSL 4 F)))
    (w : projectiveSL 4 F) :
    w ∈ JK F neg_one_ne_zero' ↔ c * w * c⁻¹ ∈ JK F neg_one_ne_zero' := by
  have hJ' : (JK F neg_one_ne_zero').map (MulAut.conj c).toMonoidHom = JK F neg_one_ne_zero' := by
    refine eq_JK h2 neg_one_ne_zero' hneg ?_ ?_ ?_
    · rintro _ ⟨v, hv, rfl⟩
      have hck : Commute (proj 4 F kSL) c := (mem_centralizer_singleton_iff.mp hc).symm
      have hvk : Commute (proj 4 F kSL) v :=
        (mem_centralizer_singleton_iff.mp (JK_le_cent hv)).symm
      rw [conjAut_kG_eq]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [((hck.mul_right hvk).mul_right hck.inv_right).eq, mul_inv_cancel_right]
    · rw [← Subgroup.map_commutator, hJp]
    · rw [Subgroup.card_map_of_injective (MulAut.conj c).injective]
      exact hJc
  constructor
  · intro hw
    rw [← hJ']
    exact ⟨w, hw, by simp [MulAut.conj_apply]⟩
  · intro hw
    rw [← hJ'] at hw
    obtain ⟨v, hv, hvw⟩ := hw
    have : v = w := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hvw
      have := congrArg (fun z => c⁻¹ * z * c) hvw
      simpa [mul_assoc] using this
    rwa [← this]

theorem nonempty_model (h2 : (2 : F) ≠ 0) (hneg : ¬ IsSquare (-1 : F)) {x y : F}
    (hxy : x ^ 2 + y ^ 2 = -1) {m : ℕ} (hm : 2 ≤ m)
    (hZ : zM x y ^ 2 ^ (m - 1) = kap ∨ zM x y ^ 2 ^ (m - 1) = -kap)
    (hJp : ⁅JK F neg_one_ne_zero', JK F neg_one_ne_zero'⁆ = JK F neg_one_ne_zero')
    (hJc : Nat.card F ^ 2 * ((Nat.card F ^ 2) ^ 2 - 1) ≤ 2 * Nat.card (JK F neg_one_ne_zero'))
    (hJZ : JK F neg_one_ne_zero' ⊓
      centralizer (JK F neg_one_ne_zero' : Set (projectiveSL 4 F)) = ⊥)
    (hL1 : 2 ^ (2 * m + 3) ∣ Nat.card (projectiveSL 4 F))
    (hL2 : ¬ 2 ^ (2 * m + 4) ∣ Nat.card (projectiveSL 4 F))
    (hJ2 : ¬ 2 ^ (m + 2) ∣ Nat.card (JK F neg_one_ne_zero')) :
    Nonempty (Model (⊤ : Subgroup (projectiveSL 4 F)) (proj 4 F kSL) (JK F neg_one_ne_zero')
      m) := by
  have hm1 : 1 ≤ m := by omega
  have ha := proj_sA_pow hxy hm1 hZ
  have hb := proj_sW_mul (F := F)
  have hba := proj_sW_conj hxy
  have h1m : 1 < 2 ^ m := lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hm1)
  have hval1 : (1 : ZMod (2 ^ m)).val = 1 := by
    rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt h1m]
  have hz : dihHom (proj 4 F (sA hxy)) (proj 4 F sW) ha hb hba (r (cc m)) = proj 4 F sK := by
    rw [dihHom_r, val_cc hm, proj_sA_half hxy hZ]
  have hr1 : dihHom (proj 4 F (sA hxy)) (proj 4 F sW) ha hb hba (r 1) = proj 4 F (sA hxy) := by
    rw [dihHom_r, hval1, pow_one]
  have hs0 : dihHom (proj 4 F (sA hxy)) (proj 4 F sW) ha hb hba (sr 0) = proj 4 F sW := by
    rw [dihHom_sr, ZMod.val_zero, pow_zero, mul_one]
  have hconj : ∀ X : SpecialLinearGroup (Fin 4) F,
      (proj 4 F (sT hxy))⁻¹ * proj 4 F X * proj 4 F (sT hxy) =
        proj 4 F ((sT hxy)⁻¹ * X * sT hxy) := fun X => by
    rw [map_mul, map_mul, map_inv]
  have haJ : proj 4 F (sA hxy) ∈ JK F neg_one_ne_zero' := ⟨_, sA_mem_SK hxy h2, rfl⟩
  have hbJ : proj 4 F (sW : SpecialLinearGroup (Fin 4) F) ∈ JK F neg_one_ne_zero' :=
    ⟨_, sW_mem_SK h2, rfl⟩
  refine ⟨{
    ρ := dihHom (proj 4 F (sA hxy)) (proj 4 F sW) ha hb hba
    t₀ := proj 4 F (sT hxy)
    two_le := hm
    inj := dihHom_injective ha hb hba (orderOf_proj_sA hxy hm1 hZ) (proj_sW_mul_pow_ne_one hxy)
    le_J := ?_
    J_le_L := le_top
    t₀_mem := mem_top _
    J_le := JK_le_cent
    normJ := fun c hc w => normJ_JK h2 hneg hJp hJc hc.1 w
    inf_cent := hJZ
    comm := ?_
    gamma := ?_
    sr_not := ?_
    iota := ?_
    sq := ?_
    not_conj := ?_
    dvd_L := by rw [Subgroup.card_top]; exact hL1
    not_dvd_L := by rw [Subgroup.card_top]; exact hL2
    not_dvd_J := hJ2 }⟩
  · intro w
    cases w with
    | r i =>
      rw [dihHom_r]
      exact pow_mem haJ _
    | sr i =>
      rw [dihHom_sr]
      exact mul_mem hbJ (pow_mem haJ _)
  · refine dihHom_conj_comm ha hb hba ?_ ?_ ?_ ?_ <;> rw [hconj]
    · exact commute_proj_of_eq (by rw [coe_conj_sA hxy]; exact apM_aM)
    · refine commute_proj_of_neg ?_
      rw [coe_conj_sA hxy]
      change apM x y * wK = -(wK * apM x y)
      rw [wK_apM, neg_neg]
    · refine commute_proj_of_neg ?_
      rw [coe_conj_sW hxy]
      change wpM x y * aM x y = -(aM x y * wpM x y)
      rw [aM_wpM, neg_neg]
    · refine commute_proj_of_neg ?_
      rw [coe_conj_sW hxy]
      change wpM x y * wK = -(wK * wpM x y)
      rw [wK_wpM, neg_neg]
  · rw [hz, hr1]
    exact gamma_mem hxy
  · rw [hs0]
    exact conj_sW_not_mem hxy h2
  · rw [hz]
    exact iota_eq hxy
  · rw [hz]
    exact sT_sq hxy
  · intro g _
    rw [hz]
    exact not_conj hneg g

end L4M

end CFSG.ComponentClassification.GSThmB.P29
