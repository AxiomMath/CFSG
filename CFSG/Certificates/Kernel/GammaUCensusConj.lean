
module

public import CFSG.Certificates.Kernel.GammaUCensusSound
public import CFSG.GF2Type.Smith1979.GammaU.StepAInputs
public import CFSG.GF2Type.Smith1979.GammaU.Violation

public section

namespace CFSG.KC.GUC

open CFSG.KC.IF4C CFSG.KC.IF4R CFSG.GF2Type.Smith1979.GammaU

section Group

variable {G : Type*} [Group G] [Finite G]

@[expose] def candR (L Le : Subgroup G) (θ : G) : Subgroup G :=
  Subgroup.closure (↑L ∪ ↑Le ∪ {θ})

theorem map_conj_eq_of_le {K M : Subgroup G} {g : G}
    (h : K.map (MulAut.conj g).toMonoidHom ≤ M) (hc : Nat.card K = Nat.card M) :
    K.map (MulAut.conj g).toMonoidHom = M :=
  Subgroup.eq_of_le_of_card_ge h (by
    rw [Subgroup.card_map_of_injective (fun a b e => (MulAut.conj g).injective e), hc])

theorem card_map_conj (K : Subgroup G) (g : G) :
    Nat.card (K.map (MulAut.conj g).toMonoidHom) = Nat.card K :=
  Subgroup.card_map_of_injective (fun a b e => (MulAut.conj g).injective e)

theorem map_conj_one (K : Subgroup G) : K.map (MulAut.conj (1 : G)).toMonoidHom = K := by
  ext x
  simp

theorem map_conj_map_conj (K : Subgroup G) (a b : G) :
    (K.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom =
      K.map (MulAut.conj (a * b)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem map_conj_candR {L Lp LX : Subgroup G} {θ g : G}
    (hL : L.map (MulAut.conj g).toMonoidHom ≤ L)
    (hθ : g * θ * g⁻¹ ∈ Subgroup.closure ((↑L : Set G) ∪ {θ}))
    (hp : Lp.map (MulAut.conj g).toMonoidHom ≤ LX) (hc : Nat.card Lp = Nat.card LX) :
    (candR L Lp θ).map (MulAut.conj g).toMonoidHom = candR L LX θ := by
  have hL' : L.map (MulAut.conj g).toMonoidHom = L := map_conj_eq_of_le hL rfl
  have hp' : Lp.map (MulAut.conj g).toMonoidHom = LX := map_conj_eq_of_le hp hc
  have hM : (Subgroup.closure ((↑L : Set G) ∪ {θ})).map (MulAut.conj g).toMonoidHom ≤
      Subgroup.closure ((↑L : Set G) ∪ {θ}) := by
    rw [Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
    rintro x (hx | hx)
    · exact Subgroup.subset_closure (Or.inl (hL ⟨x, hx, rfl⟩))
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      change (MulAut.conj g) x ∈ Subgroup.closure ((↑L : Set G) ∪ {x})
      rw [MulAut.conj_apply]
      exact hθ
  have hM' := map_conj_eq_of_le hM rfl
  have hMR : ∀ K : Subgroup G, Subgroup.closure ((↑L : Set G) ∪ {θ}) ≤ candR L K θ := fun K =>
    Subgroup.closure_mono (Set.union_subset_union_left _ Set.subset_union_left)
  have hLR : ∀ K : Subgroup G, L ≤ candR L K θ := fun K x hx =>
    Subgroup.subset_closure (Or.inl (Or.inl hx))
  have hKR : ∀ K : Subgroup G, K ≤ candR L K θ := fun K x hx =>
    Subgroup.subset_closure (Or.inl (Or.inr hx))
  apply le_antisymm
  · rw [candR, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨x, (hx | hx) | hx, rfl⟩
    · exact Subgroup.subset_closure (Or.inl (Or.inl (hL ⟨x, hx, rfl⟩)))
    · exact Subgroup.subset_closure (Or.inl (Or.inr (hp ⟨x, hx, rfl⟩)))
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hMR LX (hM ⟨x, Subgroup.subset_closure (Or.inr rfl), rfl⟩)
  · rw [candR, Subgroup.closure_le]
    rintro x ((hx | hx) | hx)
    · have hx' : x ∈ L.map (MulAut.conj g).toMonoidHom := by rw [hL']; exact hx
      exact Subgroup.map_mono (hLR Lp) hx'
    · have hx' : x ∈ Lp.map (MulAut.conj g).toMonoidHom := by rw [hp']; exact hx
      exact Subgroup.map_mono (hKR Lp) hx'
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      have hx' : x ∈ (Subgroup.closure ((↑L : Set G) ∪ {x})).map (MulAut.conj g).toMonoidHom := by
        rw [hM']
        exact Subgroup.subset_closure (Or.inr rfl)
      exact Subgroup.map_mono (hMR Lp) hx'

end Group

local notation "GL" => V12 ≃ₗ[ZMod 2] V12

@[expose] noncomputable def confR (CG FC i : Nat) (T : Nat → GL) (θ : GL) (X : Nat) : Subgroup GL :=
  candR (pGrp (five CG i)) ((pGrp (five CG (fld FC X))).map (MulAut.conj (T X)).toMonoidHom) θ

theorem mem_five {CG c m : Nat} : m ∈ five CG c ↔ ∃ l < 5, look CG (5 * c + l) = m := by
  unfold five
  simp only [List.mem_cons, List.not_mem_nil, or_false, Nat.mul_eq, Nat.add_eq]
  constructor
  · rintro (rfl | rfl | rfl | rfl | rfl)
    exacts [⟨0, by norm_num, rfl⟩, ⟨1, by norm_num, rfl⟩, ⟨2, by norm_num, rfl⟩,
      ⟨3, by norm_num, rfl⟩, ⟨4, by norm_num, rfl⟩]
  · rintro ⟨l, hl, rfl⟩
    interval_cases l <;> simp

theorem confR_conj_root {CS CSI FT FTi FC CG LB DP NC N TH i : Nat} {CN ED : List (List Nat)}
    (hE : ∀ X < N, entOK CS CSI FT FTi FC CG LB DP NC N X (ED.getD X []) = true)
    (hcn : cnOK CS CSI TH (five CG i) CN 0 = true) (hNC : CN.length = NC)
    (hCS : ∀ k < NC, mulP (look CS k) (look CSI k) = idP)
    (hFT : ∀ X < N, mulP (look FT X) (look FTi X) = idP)
    (hCGi : ∀ g ∈ five CG i, ∃ U, IsP U g)
    (hCG : ∀ X < N, ∀ g ∈ five CG (fld FC X), ∃ U, IsP U g)
    (hcard : ∀ X < N, Nat.card (pGrp (five CG (fld FC X))) = 32)
    {T : Nat → GL} (hT : ∀ X < N, IsP (T X) (look FT X)) {θ : GL} (hθ : IsP θ TH) :
    ∀ X < N, ∃ h : GL,
      confR CG FC i T θ X = (confR CG FC i T θ (fld LB X)).map (MulAut.conj h).toMonoidHom := by
  refine forest_ind hE _ (fun X _ hr => ⟨1, by rw [hr, map_conj_one]⟩) ?_
  rintro X k p ms hX hk hp hl he ⟨h, hRp⟩
  obtain ⟨A, hA⟩ := IsP.exists_of_mul (hCS k hk)
  have hAi : IsP A⁻¹ (look CSI k) := IsP.inv hA (hCS k hk)
  have hle := map_conj_le_of_edgeOK he (hCG X hX) hA (hT p hp) (hT X hX) (hCS k hk) (hFT p hp)
    (hFT X hX)
  obtain ⟨t, ms', -, hcj, hth⟩ := cnOK_spec hcn k (by rw [hNC]; exact hk)
  rw [Nat.zero_add] at hcj hth
  have hL := map_conj_le_of_cjOK hcj hCGi hA hAi
  have hθA : A * θ * A⁻¹ ∈ Subgroup.closure ((↑(pGrp (five CG i)) : Set GL) ∪ {θ}) := by
    rcases hth with ⟨-, e⟩ | ⟨-, e⟩
    · have e' : A * θ = θ * A := IsP.inj (by rw [e]; exact IsP.mul hθ hA) (IsP.mul hA hθ) |>.symm
      rw [e', mul_assoc, mul_inv_cancel, mul_one]
      exact Subgroup.subset_closure (Or.inr rfl)
    · obtain ⟨W, hW, hWp⟩ := exists_subP (five CG i) hCGi t
      have e' : A * θ * (A⁻¹ * θ) = W := IsP.inj (by
        rw [← e]
        exact IsP.mul (IsP.mul hA hθ) (IsP.mul hAi hθ)) hWp
      have e'' : A * θ * A⁻¹ = W * θ⁻¹ := by
        rw [← e']
        group
      rw [e'']
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inl hW))
        (Subgroup.inv_mem _ (Subgroup.subset_closure (Or.inr rfl)))
  have hc : Nat.card ((pGrp (five CG (fld FC p))).map (MulAut.conj (T p)).toMonoidHom) =
      Nat.card ((pGrp (five CG (fld FC X))).map (MulAut.conj (T X)).toMonoidHom) := by
    rw [card_map_conj, card_map_conj, hcard p hp, hcard X hX]
  have hRX : confR CG FC i T θ X = (confR CG FC i T θ p).map (MulAut.conj A).toMonoidHom :=
    (map_conj_candR hL hθA hle hc).symm
  refine ⟨A * h, ?_⟩
  rw [hRX, hRp, hl, map_conj_map_conj]

theorem classify {R : Nat → Subgroup GL} {LB N AR : Nat} {OR : List Nat}
    (hroot : ∀ X < N, ∃ h : GL, R X = (R (fld LB X)).map (MulAut.conj h).toMonoidHom)
    (hlab : labOK LB N OR AR = true) (hrej : ∀ r ∈ OR, Nat.card (R r) ≠ 1152)
    (hacc : Nat.card (R AR) = 1152) :
    ∀ X < N, (Nat.card (R X) = 1152 ↔ fld LB X = AR) ∧
      (fld LB X = AR → ∃ h : GL, R X = (R AR).map (MulAut.conj h).toMonoidHom) := by
  intro X hX
  obtain ⟨h, hR⟩ := hroot X hX
  have hc : Nat.card (R X) = Nat.card (R (fld LB X)) := by rw [hR, card_map_conj]
  refine ⟨⟨fun h1 => ?_, fun ha => by rw [hc, ha, hacc]⟩, fun ha => ⟨h, by rw [hR, ha]⟩⟩
  rcases labOK_spec hlab X hX with hm | ha
  · exact absurd (hc.symm.trans h1) (hrej _ hm)
  · exact ha

theorem lGrp_eq_confR {CG FT FTi FC TH i X G : Nat} (h : candOK CG FT FTi FC TH i X G = true)
    (hCG : ∀ l < 5, ∃ U, IsP U (look CG (5 * fld FC X + l))) {T : Nat → GL} {θ : GL}
    (hT : IsP (T X) (look FT X)) (hTi : IsP (T X)⁻¹ (look FTi X)) (hθ : IsP θ TH) :
    lGrp G 11 = confR CG FC i T θ X := by
  obtain ⟨h1, h2, h3⟩ := candOK_spec h
  have hconj : pGrp (five CG (fld FC X)) ≤ (lGrp G 11).comap (MulAut.conj (T X)).toMonoidHom := by
    refine (Subgroup.closure_le _).2 fun U ⟨m, hm, hU⟩ => ?_
    obtain ⟨l, hl, rfl⟩ := mem_five.1 hm
    refine Subgroup.subset_closure ⟨5 + l, by omega, ?_⟩
    rw [h2 l hl]
    change IsP (T X * U * (T X)⁻¹) _
    rw [mul_assoc]
    exact IsP.mul hT (IsP.mul hU hTi)
  apply le_antisymm
  · refine (Subgroup.closure_le _).2 fun U ⟨g, hg, hU⟩ => ?_
    by_cases g5 : g < 5
    · rw [h1 g g5] at hU
      exact Subgroup.subset_closure (Or.inl (Or.inl
        (Subgroup.subset_closure ⟨_, mem_five.2 ⟨g, g5, rfl⟩, hU⟩)))
    by_cases g10 : g < 10
    · obtain ⟨l, rfl⟩ : ∃ l, g = 5 + l := ⟨g - 5, by omega⟩
      rw [h2 l (by omega)] at hU
      obtain ⟨V, hV⟩ := hCG l (by omega)
      have e : U = T X * V * (T X)⁻¹ := by
        rw [mul_assoc]
        exact IsP.inj hU (IsP.mul hT (IsP.mul hV hTi))
      refine Subgroup.subset_closure (Or.inl (Or.inr ⟨V, Subgroup.subset_closure
        ⟨_, mem_five.2 ⟨l, by omega, rfl⟩, hV⟩, ?_⟩))
      rw [e]
      rfl
    · obtain rfl : g = 10 := by omega
      rw [h3] at hU
      exact Subgroup.subset_closure (Or.inr (IsP.inj hU hθ))
  · rw [confR, candR, Subgroup.closure_le]
    rintro x ((hx | ⟨y, hy, rfl⟩) | hx)
    · refine (Subgroup.closure_le (lGrp G 11)).2 (fun U hU' => ?_) hx
      obtain ⟨m, hm, hU⟩ := hU'
      obtain ⟨l, hl, rfl⟩ := mem_five.1 hm
      exact Subgroup.subset_closure ⟨l, by omega, by rw [h1 l hl]; exact hU⟩
    · exact hconj hy
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact Subgroup.subset_closure ⟨10, by norm_num, by rw [h3]; exact hθ⟩

end CFSG.KC.GUC

end
