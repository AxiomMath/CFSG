module

public import CFSG.ClassicalInvolution.Phan.PhanDn.Diameter
public import CFSG.ClassicalInvolution.Phan.PhanDn.Solid
public import CFSG.ClassicalInvolution.Phan.Geometry.ShortCycleMoves
import all CFSG.ClassicalInvolution.Phan.PhanDn.Perp
import all CFSG.ClassicalInvolution.Phan.PhanDn.FlipSpace
public import CFSG.ClassicalInvolution.Phan.Geometry.ShortCycles

public section

namespace CFSG.ClassicalInvolution.PhanDn

open QuadraticMap CFSG.LieType.Universal.Spin CFSG.LieType.BorelTits
open CFSG.ClassicalGroups.Unitary
open CFSG.ClassicalInvolution.Phan

variable {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}

private theorem qplus_of_hyperbolic_pair {α γ : Fin n ⊕ Fin n → K}
    (hαq : quadPlus n K α = 0) (hαγ : polar (quadPlus n K) α γ ≠ 0) :
    QPlus (K ∙ α ⊔ K ∙ γ) := by
  have hbot : QNondeg (⊥ : Submodule K (Fin n ⊕ Fin n → K)) := by
    rw [QNondeg, bot_inf_eq]
  have hbotPlus : QPlus (⊥ : Submodule K (Fin n ⊕ Fin n → K)) := by
    refine ⟨⊥, le_rfl, ?_, by simp⟩
    intro w hw
    rw [Submodule.mem_bot] at hw
    rw [hw, map_zero]
  have hαperp : α ∈ qPerp n K (⊥ : Submodule K (Fin n ⊕ Fin n → K)) := by
    rw [qPerp_bot]
    exact Submodule.mem_top
  have h := QPlus.sup_pair (A := (⊥ : Submodule K (Fin n ⊕ Fin n → K)))
    hbot hbotPlus hαperp hαq hαγ
  simpa only [bot_sup_eq] using h

private theorem qplus_sup_pair {A : Submodule K (Fin n ⊕ Fin n → K)}
    (hA : QNondeg A) (hP : QPlus A) {v w : Fin n ⊕ Fin n → K}
    (hv : v ∈ qPerp n K A) (hvs : quadPlus n K v = 0)
    (hvw : polar (quadPlus n K) v w ≠ 0) :
    QPlus (A ⊔ K ∙ v ⊔ K ∙ w) :=
  QPlus.sup_pair hA hP hv hvs hvw

private theorem polar_zero_of_le {p q : Submodule K (Fin n ⊕ Fin n → K)}
    {u v : Fin n ⊕ Fin n → K} (hp : p = K ∙ u) (hq : q = K ∙ v)
    (h : p ≤ qPerp n K q) : polar (quadPlus n K) u v = 0 := by
  have hup : u ∈ p := by rw [hp]; exact Submodule.mem_span_singleton_self u
  have hperp : u ∈ qPerp n K q := h hup
  have hv : v ∈ q := by rw [hq]; exact Submodule.mem_span_singleton_self v
  have h0 : polar (quadPlus n K) v u = 0 := (mem_qPerp.mp hperp) v hv
  rw [polar_comm (quadPlus n K) u v]
  exact h0

private theorem le_qPerp_symm {p q : Submodule K (Fin n ⊕ Fin n → K)}
    (h : p ≤ qPerp n K q) : q ≤ qPerp n K p := by
  intro x hx
  rw [mem_qPerp]
  intro y hy
  have h0 : polar (quadPlus n K) x y = 0 := (mem_qPerp.mp (h hy)) x hx
  simpa [polar_comm (quadPlus n K)] using h0

private theorem span_singleton_le_qPerp_sup {u v x : Fin n ⊕ Fin n → K}
    (hux : polar (quadPlus n K) u x = 0) (hvx : polar (quadPlus n K) v x = 0) :
    K ∙ x ≤ qPerp n K (K ∙ u ⊔ K ∙ v) := by
  rw [Submodule.span_singleton_le_iff_mem, qPerp_sup, Submodule.mem_inf, mem_qPerp, mem_qPerp]
  exact ⟨fun y hy => by
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
      rw [polar_smul_left, hux, smul_zero], fun y hy => by
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
      rw [polar_smul_left, hvx, smul_zero]⟩

private theorem flipColl_symm {p q : Submodule K (Fin n ⊕ Fin n → K)}
    (h : FlipColl σ p q) : FlipColl σ q p :=
  ⟨h.1.symm, by rw [sup_comm]; exact h.2⟩

private theorem cycleHomotopic_quad_of_perp₂_eq {a b d : FlipPt σ n}
    (hab : (flipGraph σ n).Adj a b) (hba : (flipGraph σ n).Adj b a)
    (had : (flipGraph σ n).Adj a d) (hda : (flipGraph σ n).Adj d a) :
    CycleHomotopic (solidWalks σ n) (quadWalk hab hba had hda) .nil := by
  classical
  have h1 : CycleHomotopic (solidWalks σ n)
      (.cons hab (.cons hba .nil) : (flipGraph σ n).Walk a a) .nil := by
    simpa [Subsingleton.elim hba hab.symm] using
      cycleHomotopic_cons_cons_nil (solidWalks σ n) hab
  have h2 : CycleHomotopic (solidWalks σ n)
      (.cons had (.cons hda .nil) : (flipGraph σ n).Walk a a) .nil := by
    simpa [Subsingleton.elim hda had.symm] using
      cycleHomotopic_cons_cons_nil (solidWalks σ n) had
  simpa [quadWalk] using h1.append h2

private theorem cycleHomotopic_quad_of_perp₂_bd {a b c : FlipPt σ n}
    (hab : (flipGraph σ n).Adj a b) (hbc : (flipGraph σ n).Adj b c)
    (hcb : (flipGraph σ n).Adj c b) (hba : (flipGraph σ n).Adj b a) :
    CycleHomotopic (solidWalks σ n) (quadWalk hab hbc hcb hba) .nil := by
  classical
  have h1 : CycleHomotopic (solidWalks σ n) (quadWalk hab hbc hcb hba)
      (.cons hab (.cons hba .nil) : (flipGraph σ n).Walk a a) := by
    have h := cycleHomotopic_backtrack (solidWalks σ n)
      (.cons hab .nil : (flipGraph σ n).Walk a b) (.cons hba .nil : (flipGraph σ n).Walk b a)
      hbc
    simpa [quadWalk, Subsingleton.elim hcb hbc.symm] using h.symm
  have h2 : CycleHomotopic (solidWalks σ n)
      (.cons hab (.cons hba .nil) : (flipGraph σ n).Walk a a) .nil := by
    simpa [Subsingleton.elim hba hab.symm] using
      cycleHomotopic_cons_cons_nil (solidWalks σ n) hab
  exact h1.trans h2

private theorem cycleHomotopic_quad_of_perp₂_chord_ac (h3 : NullLen (solidWalks σ n) 3)
    {a b c d : FlipPt σ n} (hab : (flipGraph σ n).Adj a b) (hbc : (flipGraph σ n).Adj b c)
    (hcd : (flipGraph σ n).Adj c d) (hda : (flipGraph σ n).Adj d a)
    (hchord : (flipGraph σ n).Adj a c) :
    CycleHomotopic (solidWalks σ n) (quadWalk hab hbc hcd hda) .nil := by
  classical
  have habc : CycleHomotopic (solidWalks σ n)
      (triWalk hab hbc hchord.symm) .nil := h3 _ rfl
  have hacd : CycleHomotopic (solidWalks σ n)
      (triWalk hchord hcd hda) .nil := h3 _ rfl
  have hdetour : CycleHomotopic (solidWalks σ n) (quadWalk hab hbc hcd hda)
      ((triWalk hab hbc hchord.symm).append (triWalk hchord hcd hda)) := by
    have h := cycleHomotopic_backtrack (solidWalks σ n)
      (.cons hab (.cons hbc .nil) : (flipGraph σ n).Walk a c)
      (.cons hcd (.cons hda .nil) : (flipGraph σ n).Walk c a) hchord.symm
    simpa [triWalk, quadWalk] using h
  exact hdetour.trans (habc.append hacd)

private theorem cycleHomotopic_quad_of_perp₂_chord_bd (h3 : NullLen (solidWalks σ n) 3)
    {a b c d : FlipPt σ n} (hab : (flipGraph σ n).Adj a b) (hbc : (flipGraph σ n).Adj b c)
    (hcd : (flipGraph σ n).Adj c d) (hda : (flipGraph σ n).Adj d a)
    (hchord : (flipGraph σ n).Adj b d) :
    CycleHomotopic (solidWalks σ n) (quadWalk hab hbc hcd hda) .nil := by
  classical
  have hbcd : CycleHomotopic (solidWalks σ n)
      (triWalk hbc hcd hchord.symm) .nil := h3 _ rfl
  have hbda : CycleHomotopic (solidWalks σ n)
      (triWalk hchord hda hab) .nil := h3 _ rfl
  have hrot : CycleHomotopic (solidWalks σ n) (quadWalk hbc hcd hda hab) .nil := by
    have hdetour : CycleHomotopic (solidWalks σ n) (quadWalk hbc hcd hda hab)
        ((triWalk hbc hcd hchord.symm).append (triWalk hchord hda hab)) := by
      have h := cycleHomotopic_backtrack (solidWalks σ n)
        (.cons hbc (.cons hcd .nil) : (flipGraph σ n).Walk b d)
        (.cons hda (.cons hab .nil) : (flipGraph σ n).Walk d b) hchord.symm
      simpa [triWalk, quadWalk] using h
    exact hdetour.trans (hbcd.append hbda)
  exact cycleHomotopic_quad_rotate (solidWalks σ n) hda hab hbc hcd
    (cycleHomotopic_quad_rotate (solidWalks σ n) hcd hda hab hbc
      (cycleHomotopic_quad_rotate (solidWalks σ n) hbc hcd hda hab hrot))

private theorem cycleHomotopic_quad_of_perp₂_nochord (hσ : IsUnitaryInvolution σ) [Finite K]
    {q : ℕ} (hK : Nat.card K = q ^ 2) (hq : 4 ≤ q) (h3 : NullLen (solidWalks σ n) 3)
    {a b c d : FlipPt σ n} (hab : (flipGraph σ n).Adj a b) (hbc : (flipGraph σ n).Adj b c)
    (hcd : (flipGraph σ n).Adj c d) (hda : (flipGraph σ n).Adj d a)
    (hac : a.1 ≤ qPerp n K c.1) (hbd : b.1 ≤ qPerp n K d.1)
    (hchord_ac : ¬ (flipGraph σ n).Adj a c) (hchord_bd : ¬ (flipGraph σ n).Adj b d) :
    CycleHomotopic (solidWalks σ n) (quadWalk hab hbc hcd hda) .nil := by
  classical
  set L : Submodule K (Fin n ⊕ Fin n → K) := a.1 ⊔ b.1 with hLdef
  have hL : IsFlipLine σ L := hab.isFlipLine a.2 b.2
  have hcL : c.1 ≤ qPerp n K L := by
    rw [hLdef, qPerp_sup]
    exact le_inf (le_qPerp_symm hac) (le_qPerp_symm hbc.le_qPerp)
  have hdL : d.1 ≤ qPerp n K L := by
    rw [hLdef, qPerp_sup]
    exact le_inf hda.le_qPerp (le_qPerp_symm hbd)
  have haL : a.1 ≤ qPerp n K L := by
    rw [hLdef, qPerp_sup]
    exact le_inf (QSing.le_qPerp a.2.1.total) hab.le_qPerp
  have hbL : b.1 ≤ qPerp n K L := by
    rw [hLdef, qPerp_sup]
    exact le_inf (le_qPerp_symm hab.le_qPerp) (QSing.le_qPerp b.2.1.total)
  obtain ⟨x, hxL, hxc, hxd⟩ := exists_flipColl₂ hσ hK hq hL c.2 d.2 hcL hdL
  have hx_pt : IsFlipflopPt σ x := hxL.1
  have hx_le : x ≤ L := hxL.2
  have hxa_ne : x ≠ a.1 := by
    intro hxa
    have hca : FlipColl σ a.1 c.1 := by
      rw [← hxa]
      exact flipColl_symm hxc
    exact hchord_ac hca
  have hxb_ne : x ≠ b.1 := by
    intro hxb
    have hdb : FlipColl σ b.1 d.1 := by
      rw [← hxb]
      exact flipColl_symm hxd
    exact hchord_bd hdb
  have hxa : FlipColl σ a.1 x :=
    flipColl_of_le_line hL ⟨a.2, le_sup_left⟩ hxL (Ne.symm hxa_ne)
  have hxb : FlipColl σ b.1 x :=
    flipColl_of_le_line hL ⟨b.2, le_sup_right⟩ hxL (Ne.symm hxb_ne)
  let e : FlipPt σ n := ⟨x, hx_pt⟩
  have he_a : (flipGraph σ n).Adj a e := hxa
  have he_b : (flipGraph σ n).Adj b e := hxb
  have he_c : (flipGraph σ n).Adj c e := hxc
  have he_d : (flipGraph σ n).Adj d e := hxd
  have h_ab_e : CycleHomotopic (solidWalks σ n) (triWalk hab he_b he_a.symm) .nil := by
    apply cycleHomotopic_of_mem
    apply mem_solidWalks_of_le hσ hL.1
    intro y hy
    simp only [triWalk, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact le_sup_left
    · exact le_sup_right
    · exact hx_le
    · exact le_sup_left
  have h_bc_e : CycleHomotopic (solidWalks σ n) (triWalk hbc he_c he_b.symm) .nil :=
    h3 _ rfl
  have h_cd_e : CycleHomotopic (solidWalks σ n) (triWalk hcd he_d he_c.symm) .nil :=
    h3 _ rfl
  have h_da_e : CycleHomotopic (solidWalks σ n) (triWalk hda he_a he_d.symm) .nil :=
    h3 _ rfl
  refine cycleHomotopic_cone_nil (solidWalks σ n) (e := e)
    (fun x y => (x = a ∧ y = b) ∨ (x = b ∧ y = c) ∨ (x = c ∧ y = d) ∨
      (x = d ∧ y = a)) ?_ _ he_a ?_
  · rintro x y (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨hab, he_a, he_b, h_ab_e⟩
    · exact ⟨hbc, he_b, he_c, h_bc_e⟩
    · exact ⟨hcd, he_c, he_d, h_cd_e⟩
    · exact ⟨hda, he_d, he_a, h_da_e⟩
  · intro d' hd'
    simp only [quadWalk, SimpleGraph.Walk.darts_cons, SimpleGraph.Walk.darts_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hd'
    rcases hd' with rfl | rfl | rfl | rfl
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))

theorem cycleHomotopic_quad_of_perp₂ (hσ : IsUnitaryInvolution σ) [Finite K] {q : ℕ}
    (hK : Nat.card K = q ^ 2) (hq : 4 ≤ q) (h3 : NullLen (solidWalks σ n) 3)
    {a b c d : FlipPt σ n} (hab : (flipGraph σ n).Adj a b) (hbc : (flipGraph σ n).Adj b c)
    (hcd : (flipGraph σ n).Adj c d) (hda : (flipGraph σ n).Adj d a)
    (hac : a.1 ≤ qPerp n K c.1) (hbd : b.1 ≤ qPerp n K d.1) :
    CycleHomotopic (solidWalks σ n) (quadWalk hab hbc hcd hda) .nil := by
  classical
  by_cases hac_eq : a = c
  · subst hac_eq
    exact cycleHomotopic_quad_of_perp₂_eq hab hbc hcd hda
  · by_cases hbd_eq : b = d
    · subst hbd_eq
      exact cycleHomotopic_quad_of_perp₂_bd hab hbc hcd hda
    · by_cases hchord_ac : (flipGraph σ n).Adj a c
      · exact cycleHomotopic_quad_of_perp₂_chord_ac h3 hab hbc hcd hda hchord_ac
      · by_cases hchord_bd : (flipGraph σ n).Adj b d
        · exact cycleHomotopic_quad_of_perp₂_chord_bd h3 hab hbc hcd hda hchord_bd
        · exact cycleHomotopic_quad_of_perp₂_nochord hσ hK hq h3 hab hbc hcd hda hac hbd
            hchord_ac hchord_bd

private theorem ncard_isotropic_projPerp_le (hσ : IsUnitaryInvolution σ) [Finite K] {q : ℕ}
    (hK : Nat.card K = q ^ 2) {m : ℕ} {a₀ u v : Fin m → K} (ha₀ : herm σ a₀ a₀ ≠ 0)
    (hind : ∀ x y : K, x • u + y • v ∈ K ∙ a₀ → x = 0 ∧ y = 0)
    (hu : herm σ (projPerp σ a₀ u) (projPerp σ a₀ u) ≠ 0) :
    {t : K | herm σ (projPerp σ a₀ (u + t • v))
      (projPerp σ a₀ (u + t • v)) = 0}.ncard ≤ q + 1 := by
  classical
  set ρ := projPerp σ a₀ with hρ
  set T := (K ∙ u ⊔ K ∙ v).map ρ with hT
  have hu0 : u ≠ 0 := by
    intro h
    have hmem : (1 : K) • u + (0 : K) • v ∈ K ∙ a₀ := by
      rw [h]
      simp
    exact one_ne_zero (hind (1 : K) (0 : K) hmem).1
  have hv0 : v ≠ 0 := by
    intro h
    have hmem : (0 : K) • u + (1 : K) • v ∈ K ∙ a₀ := by
      rw [h]
      simp
    exact one_ne_zero (hind (0 : K) (1 : K) hmem).2
  have hsup2 : Module.finrank K ↥(K ∙ u ⊔ K ∙ v) ≤ 2 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (K ∙ u) (K ∙ v)
    rw [finrank_span_singleton hu0, finrank_span_singleton hv0] at h
    omega
  have hT2 : Module.finrank K ↥T ≤ 2 := (Submodule.finrank_map_le ρ _).trans hsup2
  have hTne : ∃ w ∈ T, herm σ w w ≠ 0 :=
    ⟨ρ u, Submodule.mem_map_of_mem (Submodule.mem_sup_left
      (Submodule.mem_span_singleton_self u)), hu⟩
  have hspan : ∀ z : Fin m → K, Submodule.map ρ (K ∙ z) = K ∙ ρ z := fun z => by
    rw [Submodule.map_span, Set.image_singleton]
  have hmaps : ∀ t ∈ {t : K | herm σ (projPerp σ a₀ (u + t • v))
      (projPerp σ a₀ (u + t • v)) = 0},
      K ∙ ρ (u + t • v) ∈ isoPts σ T := by
    intro t ht
    have hnot : u + t • v ∉ K ∙ a₀ := by
      intro hmem
      exact one_ne_zero (hind 1 t (by simpa using hmem)).1
    have hz : ρ (u + t • v) ≠ 0 := fun h => hnot ((projPerp_eq_zero_iff ha₀).mp h)
    have hmemT : u + t • v ∈ K ∙ u ⊔ K ∙ v :=
      Submodule.add_mem _
        (Submodule.mem_sup_left (Submodule.mem_span_singleton_self u))
        (Submodule.mem_sup_right
          (Submodule.smul_mem _ t (Submodule.mem_span_singleton_self v)))
    rw [hT]
    exact span_singleton_mem_isoPts hz ht (Submodule.mem_map_of_mem hmemT)
  have hinj : Set.InjOn (fun t : K => K ∙ ρ (u + t • v))
      {t : K | herm σ (projPerp σ a₀ (u + t • v))
        (projPerp σ a₀ (u + t • v)) = 0} := by
    intro t₁ _ t₂ _ hEq
    have hEq' : K ∙ ρ (u + t₁ • v) = K ∙ ρ (u + t₂ • v) := hEq
    have hρ : ρ (u + t₂ • v) ∈ K ∙ ρ (u + t₁ • v) := by
      rw [hEq']
      exact Submodule.mem_span_singleton_self _
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hρ
    have hzero : ρ ((1 - c) • u + (t₂ - c * t₁) • v) = 0 := by
      have hvec : (1 - c) • u + (t₂ - c * t₁) • v =
          (u + t₂ • v) - c • (u + t₁ • v) := by
        module
      rw [hvec, map_sub, map_smul, hc, sub_self]
    obtain ⟨h1, h2⟩ := hind (1 - c) (t₂ - c * t₁) ((projPerp_eq_zero_iff ha₀).mp hzero)
    have hc1 : c = 1 := by linear_combination -h1
    have htt : t₂ = t₁ := by
      rw [hc1] at h2
      exact sub_eq_zero.mp (by simpa using h2)
    rw [htt]
  calc {t : K | herm σ (projPerp σ a₀ (u + t • v))
        (projPerp σ a₀ (u + t • v)) = 0}.ncard
      ≤ (isoPts σ T).ncard :=
        Set.ncard_le_ncard_of_injOn (fun t : K => K ∙ ρ (u + t • v)) hmaps hinj
          (Set.toFinite _)
    _ ≤ q + 1 := ncard_isoPts_le hσ hK hT2 hTne

private theorem exists_good_scalar [Finite K] {q : ℕ} (hK : Nat.card K = q ^ 2) (hq : 4 ≤ q)
    {B₁ B₂ : Set K} (h₁ : B₁.ncard ≤ q + 1) (h₂ : B₂.ncard ≤ q + 1) {c : K}
    (hc : c ≠ 0) : ∃ t : K, t ≠ 0 ∧ t ∉ B₁ ∧ c * t⁻¹ ∉ B₂ := by
  classical
  let U₂ : Set K := {t : K | t ≠ 0 ∧ c * t⁻¹ ∈ B₂}
  have hU₂ : U₂.ncard ≤ B₂.ncard := by
    refine Set.ncard_le_ncard_of_injOn (fun t : K => c * t⁻¹) (fun t ht => ht.2) ?_
      (Set.toFinite _)
    intro a _ b _ hab
    exact inv_injective (mul_left_cancel₀ hc hab)
  by_contra hcon
  have hmiss : ∀ t : K, t ≠ 0 → t ∈ B₁ ∨ c * t⁻¹ ∈ B₂ := by
    intro t ht
    by_contra h
    push Not at h
    exact hcon ⟨t, ht, h.1, h.2⟩
  have hsub : (Set.univ : Set K) ⊆ B₁ ∪ U₂ ∪ {0} := by
    intro t _
    by_cases ht : t = 0
    · simp [ht]
    · rcases hmiss t ht with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr ⟨ht, h⟩)
  have hle : Nat.card K ≤ (q + 1) + (q + 1) + 1 := by
    calc Nat.card K = (Set.univ : Set K).ncard := (Set.ncard_univ K).symm
      _ ≤ (B₁ ∪ U₂ ∪ {0}).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ (B₁ ∪ U₂).ncard + 1 := by
          have h := Set.ncard_union_le (B₁ ∪ U₂) ({0} : Set K)
          rw [Set.ncard_singleton] at h
          simpa using h
      _ ≤ (B₁.ncard + U₂.ncard) + 1 := by
          have h := Set.ncard_union_le B₁ U₂
          linarith
      _ ≤ (q + 1) + (q + 1) + 1 := by linarith
  rw [hK] at hle
  nlinarith

private theorem isFlipflopSub_span_pair_iff (hσ : IsUnitaryInvolution σ)
    {α z : Fin n ⊕ Fin n → K} (hαq : quadPlus n K α = 0) (hzq : quadPlus n K z = 0)
    (hαz : polar (quadPlus n K) α z = 0) (hαh : flipHerm σ α α ≠ 0) (hz : z ∉ K ∙ α) :
    IsFlipflopSub σ (K ∙ α ⊔ K ∙ z) ↔
      herm σ (projPerp σ (toA n K α) (toA n K z))
        (projPerp σ (toA n K α) (toA n K z)) ≠ 0 := by
  have hαsing : QSing (K ∙ α) := by
    intro w hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [QuadraticMap.map_smul, hαq, smul_zero]
  have hzsing : QSing (K ∙ z) := by
    intro w hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [QuadraticMap.map_smul, hzq, smul_zero]
  have hperp : K ∙ α ≤ qPerp n K (K ∙ z) := by
    rw [Submodule.span_singleton_le_iff_mem, mem_qPerp]
    intro w hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [polar_smul_left, polar_comm (quadPlus n K), hαz, smul_zero]
  have hsing : QSing (K ∙ α ⊔ K ∙ z) :=
    (qSing_iff_isTotallySingular (K ∙ α ⊔ K ∙ z)).mpr
      ((qSing_iff_isTotallySingular (K ∙ α)).mp hαsing |>.sup
        ((qSing_iff_isTotallySingular (K ∙ z)).mp hzsing) hperp)
  have hA : herm σ (toA n K α) (toA n K α) ≠ 0 := by
    rw [herm_toA]
    exact hαh
  have hzA : toA n K z ∉ K ∙ toA n K α := by
    intro hmem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    refine hz ?_
    rw [Submodule.mem_span_singleton]
    exact ⟨c, (toA n K).injective (by rw [map_smul, hc])⟩
  rw [isFlipflopSub_iff_nondeg hσ.invol hsing, Submodule.map_sup, Submodule.map_span,
    Submodule.map_span, Set.image_singleton, Set.image_singleton]
  exact nondeg_span_pair_iff hσ hA hzA

private theorem cycleHomotopic_quad_of_aux (hσ : IsUnitaryInvolution σ) [Finite K] {q : ℕ}
    (hK : Nat.card K = q ^ 2) (hq : 4 ≤ q) (h3 : NullLen (solidWalks σ n) 3)
    {a b c d p p' : FlipPt σ n} (hab : (flipGraph σ n).Adj a b) (hbc : (flipGraph σ n).Adj b c)
    (hcd : (flipGraph σ n).Adj c d) (hda : (flipGraph σ n).Adj d a)
    (hap : (flipGraph σ n).Adj a p) (hpc : (flipGraph σ n).Adj p c)
    (hap' : (flipGraph σ n).Adj a p') (hp'c : (flipGraph σ n).Adj p' c)
    (hac : a.1 ≤ qPerp n K c.1) (hbp : b.1 ≤ qPerp n K p.1) (hpp' : p.1 ≤ qPerp n K p'.1)
    (hp'd : p'.1 ≤ qPerp n K d.1) :
    CycleHomotopic (solidWalks σ n) (quadWalk hab hbc hcd hda) .nil := by
  refine cycleHomotopic_quad_trans (solidWalks σ n) hab hbc hpc.symm hap.symm hcd hda ?_ ?_
  · exact cycleHomotopic_quad_of_perp₂ hσ hK hq h3 hab hbc hpc.symm hap.symm hac hbp
  · refine cycleHomotopic_quad_trans (solidWalks σ n) hap hpc hp'c.symm hap'.symm hcd hda ?_ ?_
    · exact cycleHomotopic_quad_of_perp₂ hσ hK hq h3 hap hpc hp'c.symm hap'.symm hac hpp'
    · exact cycleHomotopic_quad_of_perp₂ hσ hK hq h3 hap' hp'c hcd hda hac hp'd

private theorem exists_perp_w_of_hyperbolic_pair {α β γ δ : Fin n ⊕ Fin n → K}
    (hβq : quadPlus n K β = 0) (hβα : polar (quadPlus n K) β α = 0)
    (hβγ : polar (quadPlus n K) β γ = 0) (hδα : polar (quadPlus n K) δ α = 0)
    (hδγ : polar (quadPlus n K) δ γ = 0) (hβδ : polar (quadPlus n K) β δ ≠ 0)
    (hα_notin : α ∉ K ∙ γ) :
    ∃ A₀ : Submodule K (Fin n ⊕ Fin n → K), ∃ w₁ : Fin n ⊕ Fin n → K,
      A₀ = K ∙ β ⊔ K ∙ δ ∧ QPlus A₀ ∧ QNondeg A₀ ∧ Module.finrank K A₀ = 2 ∧
      α ∈ qPerp n K A₀ ∧ γ ∈ qPerp n K A₀ ∧ w₁ ∈ qPerp n K A₀ ∧
      polar (quadPlus n K) α w₁ = 1 ∧ polar (quadPlus n K) β w₁ = 0 ∧
      polar (quadPlus n K) δ w₁ = 0 ∧ polar (quadPlus n K) γ w₁ = 0 := by
  classical
  have hbot : QNondeg (⊥ : Submodule K (Fin n ⊕ Fin n → K)) := by
    rw [QNondeg, bot_inf_eq]
  have hβperp : β ∈ qPerp n K (⊥ : Submodule K (Fin n ⊕ Fin n → K)) := by
    rw [qPerp_bot]
    exact Submodule.mem_top
  obtain ⟨A₀, hA₀⟩ : ∃ A₀ : Submodule K (Fin n ⊕ Fin n → K), A₀ = K ∙ β ⊔ K ∙ δ :=
    ⟨K ∙ β ⊔ K ∙ δ, rfl⟩
  have hA₀plus : QPlus A₀ := by
    rw [hA₀]
    exact qplus_of_hyperbolic_pair hβq hβδ
  have hA₀nd : QNondeg A₀ := by
    rw [hA₀]
    have h := QNondeg.sup_pair (A := ⊥) (v := β) (w := δ) hbot hβperp hβq hβδ
    simpa only [bot_sup_eq] using h.1
  have hA₀dim : Module.finrank K A₀ = 2 := by
    rw [hA₀]
    have h := (QNondeg.sup_pair (A := ⊥) (v := β) (w := δ) hbot hβperp hβq hβδ).2
    rw [finrank_bot, zero_add, bot_sup_eq] at h
    simpa using h
  have hγperpA₀ : γ ∈ qPerp n K A₀ := by
    rw [hA₀, qPerp_sup, Submodule.mem_inf]
    exact ⟨by
      rw [mem_qPerp]; intro y hy
      obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hy
      simp [polar_smul_left, hβγ], by
      rw [mem_qPerp]; intro y hy
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hy
      simp [polar_smul_left, hδγ]⟩
  have hαperpA₀ : α ∈ qPerp n K A₀ := by
    rw [hA₀, qPerp_sup, Submodule.mem_inf]
    exact ⟨by
      rw [mem_qPerp]; intro y hy
      obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hy
      simp [polar_smul_left, hβα], by
      rw [mem_qPerp]; intro y hy
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hy
      simp [polar_smul_left, hδα]⟩
  have hM₁nd : QNondeg (qPerp n K A₀) := QNondeg.qPerp hA₀nd
  have hW₁ : K ∙ γ ≤ qPerp n K A₀ := by
    rw [Submodule.span_singleton_le_iff_mem]
    exact hγperpA₀
  obtain ⟨w₁, hw₁_mem, hw₁_pol⟩ := exists_polar_eq_one hM₁nd hW₁ hαperpA₀ hα_notin
  have hw₁_perpA₀ : w₁ ∈ qPerp n K A₀ := (Submodule.mem_inf.mp hw₁_mem).1
  have hw₁_perpγ : polar (quadPlus n K) γ w₁ = 0 :=
    (mem_qPerp.mp (Submodule.mem_inf.mp hw₁_mem).2) γ
      (Submodule.mem_span_singleton_self γ)
  have hβw₁ : polar (quadPlus n K) β w₁ = 0 :=
    (mem_qPerp.mp hw₁_perpA₀) β (by
      rw [hA₀]
      exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self β))
  have hδw₁ : polar (quadPlus n K) δ w₁ = 0 :=
    (mem_qPerp.mp hw₁_perpA₀) δ (by
      rw [hA₀]
      exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self δ))
  exact ⟨A₀, w₁, hA₀, hA₀plus, hA₀nd, hA₀dim, hαperpA₀, hγperpA₀, hw₁_perpA₀,
    hw₁_pol, hβw₁, hδw₁, hw₁_perpγ⟩

private theorem exists_perp_plane_of_hyperbolic_pair {α γ w₁ : Fin n ⊕ Fin n → K}
    {A₀ : Submodule K (Fin n ⊕ Fin n → K)} (hαq : quadPlus n K α = 0)
    (hA₀plus : QPlus A₀) (hA₀nd : QNondeg A₀) (hA₀dim : Module.finrank K A₀ = 2)
    (hαperpA₀ : α ∈ qPerp n K A₀) (hγperpA₀ : γ ∈ qPerp n K A₀)
    (hαw₁ : polar (quadPlus n K) α w₁ ≠ 0) (hγw₁ : polar (quadPlus n K) γ w₁ = 0)
    (hαγ : polar (quadPlus n K) α γ = 0) :
    ∃ A₁ : Submodule K (Fin n ⊕ Fin n → K), A₁ = A₀ ⊔ K ∙ α ⊔ K ∙ w₁ ∧
      QPlus A₁ ∧ QNondeg A₁ ∧ Module.finrank K A₁ = 4 ∧ γ ∈ qPerp n K A₁ := by
  classical
  obtain ⟨A₁, hA₁⟩ : ∃ A₁ : Submodule K (Fin n ⊕ Fin n → K), A₁ = A₀ ⊔ K ∙ α ⊔ K ∙ w₁ :=
    ⟨_, rfl⟩
  have hA₁plus : QPlus A₁ := by
    rw [hA₁]
    exact qplus_sup_pair hA₀nd hA₀plus hαperpA₀ hαq hαw₁
  have hA₁nd : QNondeg A₁ := by
    rw [hA₁]
    have h := QNondeg.sup_pair (A := A₀) (v := α) (w := w₁) hA₀nd hαperpA₀ hαq hαw₁
    simpa using h.1
  have hA₁dim : Module.finrank K A₁ = 4 := by
    rw [hA₁]
    have h := (QNondeg.sup_pair (A := A₀) (v := α) (w := w₁) hA₀nd hαperpA₀ hαq hαw₁).2
    rw [hA₀dim] at h
    omega
  have hγperpA₁ : γ ∈ qPerp n K A₁ := by
    rw [hA₁, qPerp_sup, Submodule.mem_inf]
    exact ⟨by
      rw [qPerp_sup, Submodule.mem_inf]
      exact ⟨hγperpA₀, by
        rw [mem_qPerp]; intro y hy
        obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hy
        simp [polar_smul_left, hαγ]⟩, by
      rw [mem_qPerp]; intro y hy
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hy
      simp [polar_comm, hγw₁]⟩
  exact ⟨A₁, hA₁, hA₁plus, hA₁nd, hA₁dim, hγperpA₁⟩

private theorem exists_hyperbolic_pair_in_orthogonal {α β γ δ w₁ : Fin n ⊕ Fin n → K}
    {A₀ A₁ : Submodule K (Fin n ⊕ Fin n → K)} (hA₀ : A₀ = K ∙ β ⊔ K ∙ δ)
    (hA₁ : A₁ = A₀ ⊔ K ∙ α ⊔ K ∙ w₁) (hA₁plus : QPlus A₁) (hA₁nd : QNondeg A₁)
    (hA₁dim : Module.finrank K A₁ = 4) (hγperpA₁ : γ ∈ qPerp n K A₁)
    (hγq : quadPlus n K γ = 0) (hγ0 : γ ≠ 0) (hn : 4 ≤ n) :
    ∃ s s' : Fin n ⊕ Fin n → K, quadPlus n K s = 0 ∧ quadPlus n K s' = 0 ∧
      polar (quadPlus n K) s s' = 1 ∧ s ≠ 0 ∧
      (∀ x ∈ ({α, β, γ, δ, w₁} : Set (Fin n ⊕ Fin n → K)),
        polar (quadPlus n K) x s = 0 ∧ polar (quadPlus n K) x s' = 0) := by
  classical
  have hM₂nd : QNondeg (qPerp n K A₁) := QNondeg.qPerp hA₁nd
  obtain ⟨w₂, hw₂_mem, hw₂_pol⟩ := exists_polar_eq_one hM₂nd bot_le hγperpA₁ (by
    intro h; exact hγ0 (by simpa using h))
  have hγw₂ : polar (quadPlus n K) γ w₂ ≠ 0 := by
    rw [hw₂_pol]; exact one_ne_zero
  obtain ⟨N, hN⟩ : ∃ N : Submodule K (Fin n ⊕ Fin n → K), N = A₁ ⊔ K ∙ γ ⊔ K ∙ w₂ :=
    ⟨_, rfl⟩
  have hNplus : QPlus N := by
    rw [hN]
    exact qplus_sup_pair hA₁nd hA₁plus hγperpA₁ hγq hγw₂
  have hNnd : QNondeg N := by
    rw [hN]
    have h := QNondeg.sup_pair (A := A₁) (v := γ) (w := w₂) hA₁nd hγperpA₁ hγq hγw₂
    simpa using h.1
  have hNdim : Module.finrank K N = 6 := by
    rw [hN]
    have h := (QNondeg.sup_pair (A := A₁) (v := γ) (w := w₂) hA₁nd hγperpA₁ hγq hγw₂).2
    rw [hA₁dim] at h
    omega
  have hCdim : Module.finrank K (qPerp n K N) = 2 * n - 6 := by
    have h := finrank_qPerp (n := n) (K := K) N
    rw [hNdim] at h
    exact Nat.eq_sub_of_add_eq h
  have hCnd : QNondeg (qPerp n K N) := QNondeg.qPerp hNnd
  have hCplus : QPlus (qPerp n K N) := QPlus.qPerp hNnd hNplus
  obtain ⟨T, hT_le, hT_sing, hT_dim⟩ := hCplus
  have hT_ne_bot : T ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hT_dim
    omega
  obtain ⟨s, hs_mem, hs_ne_zero⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hT_ne_bot
  have hs_C : s ∈ qPerp n K N := hT_le hs_mem
  have hs_sing : quadPlus n K s = 0 := hT_sing s hs_mem
  obtain ⟨s', hs'_mem, hs'_sing, hss'⟩ := exists_singular_polar_eq_one hCnd bot_le
    (show s ∈ qPerp n K N ⊓ qPerp n K (⊥ : Submodule K (Fin n ⊕ Fin n → K)) by
      rw [qPerp_bot]; exact ⟨hs_C, Submodule.mem_top⟩)
    (by simpa using hs_ne_zero) hs_sing
  have hs'_C : s' ∈ qPerp n K N := (Submodule.mem_inf.mp hs'_mem).1
  refine ⟨s, s', hs_sing, hs'_sing, hss', hs_ne_zero, ?_⟩
  intro x hx
  have hxN : x ∈ N := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h | h | h | h | h
    · rw [h, hN, hA₁]
      exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left
        (Submodule.mem_sup_right (Submodule.mem_span_singleton_self α))))
    · rw [h, hN, hA₁, hA₀]
      exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left
        (Submodule.mem_sup_left (Submodule.mem_sup_left
          (Submodule.mem_span_singleton_self β)))))
    · rw [h, hN]
      exact Submodule.mem_sup_left (Submodule.mem_sup_right
        (Submodule.mem_span_singleton_self γ))
    · rw [h, hN, hA₁, hA₀]
      exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left
        (Submodule.mem_sup_left (Submodule.mem_sup_right
          (Submodule.mem_span_singleton_self δ)))))
    · rw [h, hN, hA₁]
      exact Submodule.mem_sup_left (Submodule.mem_sup_left
        (Submodule.mem_sup_right (Submodule.mem_span_singleton_self w₁)))
  exact ⟨(mem_qPerp.mp hs_C) x hxN, (mem_qPerp.mp hs'_C) x hxN⟩

private theorem exists_perp_hyperbolic_pair {α β γ δ : Fin n ⊕ Fin n → K}
    (hαq : quadPlus n K α = 0) (hβq : quadPlus n K β = 0) (hγq : quadPlus n K γ = 0)
    (hβα : polar (quadPlus n K) β α = 0)
    (hβγ : polar (quadPlus n K) β γ = 0) (hδα : polar (quadPlus n K) δ α = 0)
    (hδγ : polar (quadPlus n K) δ γ = 0) (hαγ : polar (quadPlus n K) α γ = 0)
    (hβδ : polar (quadPlus n K) β δ ≠ 0) (hγ0 : γ ≠ 0) (hα_notin : α ∉ K ∙ γ)
    (hn : 4 ≤ n) :
    ∃ s s' w : Fin n ⊕ Fin n → K, quadPlus n K s = 0 ∧ quadPlus n K s' = 0 ∧
      polar (quadPlus n K) s s' = 1 ∧ s ≠ 0 ∧
      (∀ x ∈ ({α, β, γ, δ, w} : Set (Fin n ⊕ Fin n → K)),
        polar (quadPlus n K) x s = 0 ∧ polar (quadPlus n K) x s' = 0) ∧
      polar (quadPlus n K) α w = 1 ∧ polar (quadPlus n K) β w = 0 ∧
      polar (quadPlus n K) δ w = 0 := by
  classical
  obtain ⟨A₀, w₁, hA₀, hA₀plus, hA₀nd, hA₀dim, hαperpA₀, hγperpA₀, hw₁_perpA₀,
    hαw₁, hβw₁, hδw₁, hγw₁⟩ :=
    exists_perp_w_of_hyperbolic_pair hβq hβα hβγ hδα hδγ hβδ hα_notin
  obtain ⟨A₁, hA₁, hA₁plus, hA₁nd, hA₁dim, hγperpA₁⟩ :=
    exists_perp_plane_of_hyperbolic_pair hαq hA₀plus hA₀nd hA₀dim hαperpA₀ hγperpA₀
      (by rw [hαw₁]; exact one_ne_zero) hγw₁ hαγ
  obtain ⟨s, s', hs_q, hs'_q, hss', hs0, hperp⟩ :=
    exists_hyperbolic_pair_in_orthogonal hA₀ hA₁ hA₁plus hA₁nd hA₁dim hγperpA₁ hγq hγ0 hn
  exact ⟨s, s', w₁, hs_q, hs'_q, hss', hs0, hperp, hαw₁, hβw₁, hδw₁⟩

private theorem cycleHomotopic_quad_of_perp_eq {a b d : FlipPt σ n}
    (hab : (flipGraph σ n).Adj a b) (hba : (flipGraph σ n).Adj b a)
    (had : (flipGraph σ n).Adj a d) (hda : (flipGraph σ n).Adj d a) :
    CycleHomotopic (solidWalks σ n) (quadWalk hab hba had hda) .nil := by
  classical
  have h1 : CycleHomotopic (solidWalks σ n)
      (.cons hab (.cons hba .nil) : (flipGraph σ n).Walk a a) .nil := by
    simpa [Subsingleton.elim hba hab.symm] using
      cycleHomotopic_cons_cons_nil (solidWalks σ n) hab
  have h2 : CycleHomotopic (solidWalks σ n)
      (.cons had (.cons hda .nil) : (flipGraph σ n).Walk a a) .nil := by
    simpa [Subsingleton.elim hda had.symm] using
      cycleHomotopic_cons_cons_nil (solidWalks σ n) had
  simpa [quadWalk] using h1.append h2

private theorem exists_quad_span_data {a b c d : FlipPt σ n}
    (hab : (flipGraph σ n).Adj a b) (hbc : (flipGraph σ n).Adj b c)
    (hcd : (flipGraph σ n).Adj c d) (hda : (flipGraph σ n).Adj d a)
    (hac : a.1 ≤ qPerp n K c.1) (hbd : ¬ b.1 ≤ qPerp n K d.1) (hac_eq : a ≠ c) :
    ∃ α β γ δ : Fin n ⊕ Fin n → K, a.1 = K ∙ α ∧ b.1 = K ∙ β ∧ c.1 = K ∙ γ ∧
      d.1 = K ∙ δ ∧ quadPlus n K α = 0 ∧ quadPlus n K β = 0 ∧ quadPlus n K γ = 0 ∧
      quadPlus n K δ = 0 ∧ flipHerm σ α α ≠ 0 ∧ flipHerm σ β β ≠ 0 ∧
      flipHerm σ γ γ ≠ 0 ∧ flipHerm σ δ δ ≠ 0 ∧ polar (quadPlus n K) β α = 0 ∧
      polar (quadPlus n K) β γ = 0 ∧ polar (quadPlus n K) δ α = 0 ∧
      polar (quadPlus n K) δ γ = 0 ∧ polar (quadPlus n K) α γ = 0 ∧
      polar (quadPlus n K) β δ ≠ 0 ∧ α ≠ 0 ∧ β ≠ 0 ∧ γ ≠ 0 ∧ δ ≠ 0 ∧
      α ∉ K ∙ γ := by
  classical
  obtain ⟨α, hαspan, hαq, hαh⟩ := IsFlipflopPt.exists_eq_span a.2
  obtain ⟨β, hβspan, hβq, hβh⟩ := IsFlipflopPt.exists_eq_span b.2
  obtain ⟨γ, hγspan, hγq, hγh⟩ := IsFlipflopPt.exists_eq_span c.2
  obtain ⟨δ, hδspan, hδq, hδh⟩ := IsFlipflopPt.exists_eq_span d.2
  have hα0 : α ≠ 0 := fun h => hαh (by rw [h, flipHerm_zero_left])
  have hβ0 : β ≠ 0 := fun h => hβh (by rw [h, flipHerm_zero_left])
  have hγ0 : γ ≠ 0 := fun h => hγh (by rw [h, flipHerm_zero_left])
  have hδ0 : δ ≠ 0 := fun h => hδh (by rw [h, flipHerm_zero_left])
  have hβα : polar (quadPlus n K) β α = 0 := polar_zero_of_le hβspan hαspan hab.symm.le_qPerp
  have hβγ : polar (quadPlus n K) β γ = 0 := polar_zero_of_le hβspan hγspan hbc.le_qPerp
  have hδα : polar (quadPlus n K) δ α = 0 :=
    polar_zero_of_le (u := δ) (v := α) hδspan hαspan hda.le_qPerp
  have hδγ : polar (quadPlus n K) δ γ = 0 :=
    polar_zero_of_le (u := δ) (v := γ) hδspan hγspan hcd.symm.le_qPerp
  have hαγ : polar (quadPlus n K) α γ = 0 := by
    have h := hac (by rw [hαspan]; exact Submodule.mem_span_singleton_self α)
    rw [mem_qPerp] at h
    have h0 : polar (quadPlus n K) γ α = 0 :=
      h γ (by rw [hγspan]; exact Submodule.mem_span_singleton_self γ)
    rwa [polar_comm] at h0
  have hβδ : polar (quadPlus n K) β δ ≠ 0 := by
    intro h
    apply hbd
    rw [hβspan, hδspan]
    intro x hx
    rw [mem_qPerp]
    intro w hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hx
    simp [polar_smul_right, polar_comm, h]
  have hα_notin : α ∉ K ∙ γ := by
    intro hmem
    obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp hmem
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hk
      exact hα0 hk.symm
    have hspan_eq : a.1 = c.1 := by
      rw [hαspan, hγspan, ← hk]
      exact Submodule.span_singleton_smul_eq (IsUnit.mk0 k hk0) γ
    exact hac_eq (Subtype.ext hspan_eq)
  exact ⟨α, β, γ, δ, hαspan, hβspan, hγspan, hδspan, hαq, hβq, hγq, hδq, hαh,
    hβh, hγh, hδh, hβα, hβγ, hδα, hδγ, hαγ, hβδ, hα0, hβ0, hγ0, hδ0, hα_notin⟩

private theorem polar_orthogonal_facts {α β γ δ s s' w : Fin n ⊕ Fin n → K}
    (hperp : ∀ x ∈ ({α, β, γ, δ, w} : Set (Fin n ⊕ Fin n → K)),
      polar (quadPlus n K) x s = 0 ∧ polar (quadPlus n K) x s' = 0) :
    polar (quadPlus n K) α s = 0 ∧ polar (quadPlus n K) α s' = 0 ∧
      polar (quadPlus n K) β s = 0 ∧ polar (quadPlus n K) β s' = 0 ∧
      polar (quadPlus n K) γ s = 0 ∧ polar (quadPlus n K) γ s' = 0 ∧
      polar (quadPlus n K) δ s = 0 ∧ polar (quadPlus n K) δ s' = 0 ∧
      polar (quadPlus n K) w s = 0 ∧ polar (quadPlus n K) w s' = 0 :=
  ⟨(hperp α (by simp)).1, (hperp α (by simp)).2, (hperp β (by simp)).1,
    (hperp β (by simp)).2, (hperp γ (by simp)).1, (hperp γ (by simp)).2,
    (hperp δ (by simp)).1, (hperp δ (by simp)).2, (hperp w (by simp)).1,
    (hperp w (by simp)).2⟩

private theorem polar_symmetry_facts {α β γ δ s s' w : Fin n ⊕ Fin n → K}
    (hws : polar (quadPlus n K) w s = 0) (hδs : polar (quadPlus n K) δ s = 0)
    (hβs' : polar (quadPlus n K) β s' = 0) (hαw : polar (quadPlus n K) α w = 1)
    (hβw : polar (quadPlus n K) β w = 0) (hδw : polar (quadPlus n K) δ w = 0)
    (hβα : polar (quadPlus n K) β α = 0) (hβγ : polar (quadPlus n K) β γ = 0)
    (hδα : polar (quadPlus n K) δ α = 0) (hδγ : polar (quadPlus n K) δ γ = 0)
    (hβδ : polar (quadPlus n K) β δ ≠ 0) (hss' : polar (quadPlus n K) s s' = 1) :
    polar (quadPlus n K) s w = 0 ∧ polar (quadPlus n K) s δ = 0 ∧
      polar (quadPlus n K) s' β = 0 ∧ polar (quadPlus n K) w α = 1 ∧
      polar (quadPlus n K) w β = 0 ∧ polar (quadPlus n K) w δ = 0 ∧
      polar (quadPlus n K) α β = 0 ∧ polar (quadPlus n K) α δ = 0 ∧
      polar (quadPlus n K) γ β = 0 ∧ polar (quadPlus n K) γ δ = 0 ∧
      polar (quadPlus n K) δ β ≠ 0 ∧ s' ≠ 0 := by
  have hsw : polar (quadPlus n K) s w = 0 := by
    rw [polar_comm (quadPlus n K)]
    exact hws
  have hsδ : polar (quadPlus n K) s δ = 0 := by
    rw [polar_comm (quadPlus n K)]
    exact hδs
  have hs'β : polar (quadPlus n K) s' β = 0 := by
    rw [polar_comm (quadPlus n K)]
    exact hβs'
  have hwα : polar (quadPlus n K) w α = 1 := by
    rw [polar_comm (quadPlus n K)]
    exact hαw
  have hwβ : polar (quadPlus n K) w β = 0 := by
    rw [polar_comm (quadPlus n K)]
    exact hβw
  have hwδ : polar (quadPlus n K) w δ = 0 := by
    rw [polar_comm (quadPlus n K)]
    exact hδw
  have hαβ : polar (quadPlus n K) α β = 0 := by
    rw [polar_comm (quadPlus n K)]
    exact hβα
  have hαδ : polar (quadPlus n K) α δ = 0 := by
    rw [polar_comm (quadPlus n K)]
    exact hδα
  have hγβ : polar (quadPlus n K) γ β = 0 := by
    rw [polar_comm (quadPlus n K)]
    exact hβγ
  have hγδ : polar (quadPlus n K) γ δ = 0 := by
    rw [polar_comm (quadPlus n K)]
    exact hδγ
  have hδβ : polar (quadPlus n K) δ β ≠ 0 := by
    rw [polar_comm (quadPlus n K)]
    exact hβδ
  have hs'0 : s' ≠ 0 := by
    intro h
    have h1 : polar (quadPlus n K) s s' = 0 := by rw [h, polar_zero_right]
    rw [hss'] at h1
    exact one_ne_zero h1
  exact ⟨hsw, hsδ, hs'β, hwα, hwβ, hwδ, hαβ, hαδ, hγβ, hγδ, hδβ, hs'0⟩

private theorem toA_independent_pair {α β δ s s' w : Fin n ⊕ Fin n → K}
    (hwα : polar (quadPlus n K) w α = 1) (hwβ : polar (quadPlus n K) w β = 0)
    (hwδ : polar (quadPlus n K) w δ = 0) (hws : polar (quadPlus n K) w s = 0)
    (hws' : polar (quadPlus n K) w s' = 0) (hsδ : polar (quadPlus n K) s δ = 0)
    (hs'β : polar (quadPlus n K) s' β = 0)
    (hβδ : polar (quadPlus n K) β δ ≠ 0) (hδβ : polar (quadPlus n K) δ β ≠ 0)
    (hs0 : s ≠ 0) (hs'0 : s' ≠ 0) :
    (∀ x y : K, x • toA n K β + y • toA n K s ∈ K ∙ toA n K α → x = 0 ∧ y = 0) ∧
      (∀ x y : K, x • toA n K δ + y • toA n K s' ∈ K ∙ toA n K α →
        x = 0 ∧ y = 0) := by
  refine ⟨?_, ?_⟩
  · intro x y hmem
    have hmem' : x • β + y • s ∈ K ∙ α := by
      have hmap : toA n K (x • β + y • s) ∈ K ∙ toA n K α := by
        simpa only [map_add, map_smul] using hmem
      obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp hmap
      rw [Submodule.mem_span_singleton]
      exact ⟨k, (toA n K).injective (by rw [map_smul, hk])⟩
    obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp hmem'
    have hk0 : k = 0 := by
      have h := congrArg (fun z => polar (quadPlus n K) w z) hk
      simp only [polar_smul_right, polar_add_right, hwα, hwβ, hws,
        smul_eq_mul, mul_one, mul_zero, add_zero] at h
      exact h
    have hzero : x • β + y • s = 0 := by
      rw [hk0, zero_smul] at hk
      exact hk.symm
    have hx : x = 0 := by
      have h := congrArg (fun z => polar (quadPlus n K) z δ) hzero
      rw [polar_zero_left, polar_add_left, polar_smul_left, polar_smul_left,
        hsδ, smul_zero, add_zero, smul_eq_mul] at h
      exact (mul_eq_zero.mp h).resolve_right hβδ
    refine ⟨hx, ?_⟩
    rw [hx, zero_smul, zero_add] at hzero
    exact (smul_eq_zero.mp hzero).resolve_right hs0
  · intro x y hmem
    have hmem' : x • δ + y • s' ∈ K ∙ α := by
      have hmap : toA n K (x • δ + y • s') ∈ K ∙ toA n K α := by
        simpa only [map_add, map_smul] using hmem
      obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp hmap
      rw [Submodule.mem_span_singleton]
      exact ⟨k, (toA n K).injective (by rw [map_smul, hk])⟩
    obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp hmem'
    have hk0 : k = 0 := by
      have h := congrArg (fun z => polar (quadPlus n K) w z) hk
      simp only [polar_smul_right, polar_add_right, hwα, hwδ, hws',
        smul_eq_mul, mul_one, mul_zero, add_zero] at h
      exact h
    have hzero : x • δ + y • s' = 0 := by
      rw [hk0, zero_smul] at hk
      exact hk.symm
    have hx : x = 0 := by
      have h := congrArg (fun z => polar (quadPlus n K) z β) hzero
      rw [polar_zero_left, polar_add_left, polar_smul_left, polar_smul_left,
        hs'β, smul_zero, add_zero, smul_eq_mul] at h
      exact (mul_eq_zero.mp h).resolve_right hδβ
    refine ⟨hx, ?_⟩
    rw [hx, zero_smul, zero_add] at hzero
    exact (smul_eq_zero.mp hzero).resolve_right hs'0

private theorem notin_span_of_ne {a b : FlipPt σ n} {α β : Fin n ⊕ Fin n → K}
    (hαspan : a.1 = K ∙ α) (hβspan : b.1 = K ∙ β) (hα0 : α ≠ 0) (hβ0 : β ≠ 0)
    (hne : a.1 ≠ b.1) : β ∉ K ∙ α := by
  intro hmem
  have hle : K ∙ β ≤ K ∙ α := (Submodule.span_singleton_le_iff_mem _ _).mpr hmem
  have heq : K ∙ β = K ∙ α :=
    Submodule.eq_of_le_of_finrank_eq hle
      (by rw [finrank_span_singleton hβ0, finrank_span_singleton hα0])
  exact hne (by rw [hαspan, hβspan]; exact heq.symm)

private theorem exists_good_parameter (hσ : IsUnitaryInvolution σ) [Finite K] {q : ℕ}
    (hK : Nat.card K = q ^ 2) (hq : 4 ≤ q) {α β δ s s' : Fin n ⊕ Fin n → K}
    (hαh : flipHerm σ α α ≠ 0) (hβδ : polar (quadPlus n K) β δ ≠ 0)
    (hind₁ : ∀ x y : K, x • toA n K β + y • toA n K s ∈ K ∙ toA n K α → x = 0 ∧ y = 0)
    (hind₂ : ∀ x y : K, x • toA n K δ + y • toA n K s' ∈ K ∙ toA n K α → x = 0 ∧ y = 0)
    (hu₁ : herm σ (projPerp σ (toA n K α) (toA n K β))
      (projPerp σ (toA n K α) (toA n K β)) ≠ 0)
    (hu₂ : herm σ (projPerp σ (toA n K α) (toA n K δ))
      (projPerp σ (toA n K α) (toA n K δ)) ≠ 0) :
    ∃ t : K, t ≠ 0 ∧
      herm σ (projPerp σ (toA n K α) (toA n K β + t • toA n K s))
        (projPerp σ (toA n K α) (toA n K β + t • toA n K s)) ≠ 0 ∧
      herm σ (projPerp σ (toA n K α) (toA n K δ +
        ((-polar (quadPlus n K) β δ) * t⁻¹) • toA n K s'))
        (projPerp σ (toA n K α) (toA n K δ +
          ((-polar (quadPlus n K) β δ) * t⁻¹) • toA n K s')) ≠ 0 := by
  classical
  set B₁ : Set K := {t : K | herm σ (projPerp σ (toA n K α)
    (toA n K β + t • toA n K s)) (projPerp σ (toA n K α)
    (toA n K β + t • toA n K s)) = 0} with hB₁def
  set B₂ : Set K := {t : K | herm σ (projPerp σ (toA n K α)
    (toA n K δ + t • toA n K s')) (projPerp σ (toA n K α)
    (toA n K δ + t • toA n K s')) = 0} with hB₂def
  have hB₁ : B₁.ncard ≤ q + 1 := by
    rw [hB₁def]
    exact ncard_isotropic_projPerp_le hσ hK (a₀ := toA n K α) (u := toA n K β)
      (v := toA n K s) (by rw [herm_toA]; exact hαh) hind₁ hu₁
  have hB₂ : B₂.ncard ≤ q + 1 := by
    rw [hB₂def]
    exact ncard_isotropic_projPerp_le hσ hK (a₀ := toA n K α) (u := toA n K δ)
      (v := toA n K s') (by rw [herm_toA]; exact hαh) hind₂ hu₂
  set c₀ : K := -polar (quadPlus n K) β δ with hc₀def
  have hc₀ : c₀ ≠ 0 := by
    rw [hc₀def]
    intro h
    exact hβδ (neg_eq_zero.mp h)
  obtain ⟨t, ht0, htB₁, htcB₂⟩ := exists_good_scalar hK hq hB₁ hB₂ hc₀
  refine ⟨t, ht0, ?_, ?_⟩
  · rw [hB₁def] at htB₁
    simpa only [Set.mem_setOf_eq, map_add, map_smul] using htB₁
  · rw [hB₂def] at htcB₂
    simpa only [Set.mem_setOf_eq, hc₀def, map_add, map_smul] using htcB₂

private theorem exists_orthogonal_vectors {α β γ δ s s' : Fin n ⊕ Fin n → K} (t : K)
    (hβq : quadPlus n K β = 0) (hδq : quadPlus n K δ = 0)
    (hs_q : quadPlus n K s = 0) (hs'_q : quadPlus n K s' = 0)
    (hαβ : polar (quadPlus n K) α β = 0) (hαδ : polar (quadPlus n K) α δ = 0)
    (hγβ : polar (quadPlus n K) γ β = 0) (hγδ : polar (quadPlus n K) γ δ = 0)
    (hαs : polar (quadPlus n K) α s = 0) (hγs : polar (quadPlus n K) γ s = 0)
    (hβs : polar (quadPlus n K) β s = 0) (hαs' : polar (quadPlus n K) α s' = 0)
    (hγs' : polar (quadPlus n K) γ s' = 0) (hδs' : polar (quadPlus n K) δ s' = 0)
    (hβs' : polar (quadPlus n K) β s' = 0) (hsδ : polar (quadPlus n K) s δ = 0)
    (hss' : polar (quadPlus n K) s s' = 1)
    (hind₁ : ∀ x y : K, x • toA n K β + y • toA n K s ∈ K ∙ toA n K α → x = 0 ∧ y = 0)
    (hind₂ : ∀ x y : K, x • toA n K δ + y • toA n K s' ∈ K ∙ toA n K α → x = 0 ∧ y = 0)
    (ht0 : t ≠ 0)
    (htB₁ : herm σ (projPerp σ (toA n K α) (toA n K β + t • toA n K s))
      (projPerp σ (toA n K α) (toA n K β + t • toA n K s)) ≠ 0)
    (htB₂ : herm σ (projPerp σ (toA n K α) (toA n K δ +
      ((-polar (quadPlus n K) β δ) * t⁻¹) • toA n K s'))
      (projPerp σ (toA n K α) (toA n K δ +
        ((-polar (quadPlus n K) β δ) * t⁻¹) • toA n K s')) ≠ 0) :
    ∃ z₁ z₂ : Fin n ⊕ Fin n → K, z₁ = β + t • s ∧
      z₂ = δ + ((-polar (quadPlus n K) β δ) * t⁻¹) • s' ∧
      quadPlus n K z₁ = 0 ∧ quadPlus n K z₂ = 0 ∧
      herm σ (projPerp σ (toA n K α) (toA n K z₁))
        (projPerp σ (toA n K α) (toA n K z₁)) ≠ 0 ∧
      herm σ (projPerp σ (toA n K α) (toA n K z₂))
        (projPerp σ (toA n K α) (toA n K z₂)) ≠ 0 ∧
      polar (quadPlus n K) α z₁ = 0 ∧ polar (quadPlus n K) γ z₁ = 0 ∧
      polar (quadPlus n K) β z₁ = 0 ∧ polar (quadPlus n K) α z₂ = 0 ∧
      polar (quadPlus n K) γ z₂ = 0 ∧ polar (quadPlus n K) δ z₂ = 0 ∧
      polar (quadPlus n K) z₁ z₂ = 0 ∧ z₁ ∉ K ∙ α ∧ z₂ ∉ K ∙ α := by
  classical
  set z₁ : Fin n ⊕ Fin n → K := β + t • s with hz₁def
  set z₂ : Fin n ⊕ Fin n → K := δ + ((-polar (quadPlus n K) β δ) * t⁻¹) • s' with hz₂def
  have hu₁' : herm σ (projPerp σ (toA n K α) (toA n K z₁))
      (projPerp σ (toA n K α) (toA n K z₁)) ≠ 0 := by
    simpa only [hz₁def, map_add, map_smul] using htB₁
  have hu₂' : herm σ (projPerp σ (toA n K α) (toA n K z₂))
      (projPerp σ (toA n K α) (toA n K z₂)) ≠ 0 := by
    simpa only [hz₂def, map_add, map_smul] using htB₂
  have hz₁q : quadPlus n K z₁ = 0 := by
    rw [hz₁def, QuadraticMap.map_add (quadPlus n K),
      QuadraticMap.map_smul (quadPlus n K), polar_smul_right,
      hβq, hs_q, hβs, smul_zero, smul_zero, add_zero, add_zero]
  have hz₂q : quadPlus n K z₂ = 0 := by
    rw [hz₂def, QuadraticMap.map_add (quadPlus n K),
      QuadraticMap.map_smul (quadPlus n K), polar_smul_right,
      hδq, hs'_q, hδs', smul_zero, smul_zero, add_zero, add_zero]
  have hαz₁ : polar (quadPlus n K) α z₁ = 0 := by
    rw [hz₁def, polar_add_right, polar_smul_right, hαβ, hαs, smul_zero, add_zero]
  have hγz₁ : polar (quadPlus n K) γ z₁ = 0 := by
    rw [hz₁def, polar_add_right, polar_smul_right, hγβ, hγs, smul_zero, add_zero]
  have hβz₁ : polar (quadPlus n K) β z₁ = 0 := by
    rw [hz₁def, polar_add_right, polar_smul_right, polar_self_of_singular hβq, hβs,
      smul_zero, add_zero]
  have hαz₂ : polar (quadPlus n K) α z₂ = 0 := by
    rw [hz₂def, polar_add_right, polar_smul_right, hαδ, hαs', smul_zero, add_zero]
  have hγz₂ : polar (quadPlus n K) γ z₂ = 0 := by
    rw [hz₂def, polar_add_right, polar_smul_right, hγδ, hγs', smul_zero, add_zero]
  have hδz₂ : polar (quadPlus n K) δ z₂ = 0 := by
    rw [hz₂def, polar_add_right, polar_smul_right, polar_self_of_singular hδq, hδs',
      smul_zero, add_zero]
  have hz₁z₂ : polar (quadPlus n K) z₁ z₂ = 0 := by
    rw [hz₁def, hz₂def, polar_add_left, polar_add_right, polar_add_right,
      polar_smul_left, polar_smul_left, polar_smul_right,
      polar_smul_right, hβs', hsδ, hss']
    simp only [smul_eq_mul, mul_one, mul_zero, add_zero]
    field_simp
    ring
  have hz₁_notin : z₁ ∉ K ∙ α := by
    intro hmem
    have hmap : toA n K z₁ ∈ K ∙ toA n K α := by
      obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp hmem
      rw [Submodule.mem_span_singleton]
      exact ⟨k, by rw [← hk, map_smul]⟩
    have hmem' : (1 : K) • toA n K β + t • toA n K s ∈ K ∙ toA n K α := by
      simpa only [hz₁def, map_add, map_smul, one_smul] using hmap
    exact one_ne_zero (hind₁ 1 t hmem').1
  have hz₂_notin : z₂ ∉ K ∙ α := by
    intro hmem
    have hmap : toA n K z₂ ∈ K ∙ toA n K α := by
      obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp hmem
      rw [Submodule.mem_span_singleton]
      exact ⟨k, by rw [← hk, map_smul]⟩
    have hmem' : (1 : K) • toA n K δ +
        ((-polar (quadPlus n K) β δ) * t⁻¹) • toA n K s' ∈ K ∙ toA n K α := by
      simpa only [hz₂def, map_add, map_smul, one_smul] using hmap
    exact one_ne_zero (hind₂ 1 _ hmem').1
  exact ⟨z₁, z₂, rfl, rfl, hz₁q, hz₂q, hu₁', hu₂', hαz₁, hγz₁, hβz₁,
    hαz₂, hγz₂, hδz₂, hz₁z₂, hz₁_notin, hz₂_notin⟩

private theorem exists_two_perp_flip_lines (hσ : IsUnitaryInvolution σ)
    {α β γ δ z₁ z₂ : Fin n ⊕ Fin n → K} {a b c d : FlipPt σ n}
    (hαspan : a.1 = K ∙ α) (hβspan : b.1 = K ∙ β) (hγspan : c.1 = K ∙ γ)
    (hδspan : d.1 = K ∙ δ)
    (hαq : quadPlus n K α = 0) (hαh : flipHerm σ α α ≠ 0) (hα0 : α ≠ 0)
    (hz₁q : quadPlus n K z₁ = 0) (hz₂q : quadPlus n K z₂ = 0)
    (hαz₁ : polar (quadPlus n K) α z₁ = 0) (hαz₂ : polar (quadPlus n K) α z₂ = 0)
    (hu₁' : herm σ (projPerp σ (toA n K α) (toA n K z₁))
      (projPerp σ (toA n K α) (toA n K z₁)) ≠ 0)
    (hu₂' : herm σ (projPerp σ (toA n K α) (toA n K z₂))
      (projPerp σ (toA n K α) (toA n K z₂)) ≠ 0)
    (hz₁_notin : z₁ ∉ K ∙ α) (hz₂_notin : z₂ ∉ K ∙ α)
    (hγz₁ : polar (quadPlus n K) γ z₁ = 0) (hβz₁ : polar (quadPlus n K) β z₁ = 0)
    (hγz₂ : polar (quadPlus n K) γ z₂ = 0) (hδz₂ : polar (quadPlus n K) δ z₂ = 0)
    (hz₁z₂ : polar (quadPlus n K) z₁ z₂ = 0)
    (hαγ : polar (quadPlus n K) α γ = 0) (hαβ : polar (quadPlus n K) α β = 0)
    (hαδ : polar (quadPlus n K) α δ = 0) :
    ∃ L₁ L₂ : Submodule K (Fin n ⊕ Fin n → K), IsFlipLine σ L₁ ∧ IsFlipLine σ L₂ ∧
      c.1 ≤ qPerp n K L₁ ∧ c.1 ≤ qPerp n K L₂ ∧ b.1 ≤ qPerp n K L₁ ∧
      d.1 ≤ qPerp n K L₂ ∧ L₁ ≤ qPerp n K L₂ ∧ a.1 ≤ L₁ ∧ a.1 ≤ L₂ := by
  classical
  set L₁ : Submodule K (Fin n ⊕ Fin n → K) := K ∙ α ⊔ K ∙ z₁ with hL₁def
  set L₂ : Submodule K (Fin n ⊕ Fin n → K) := K ∙ α ⊔ K ∙ z₂ with hL₂def
  have hdim₁ : Module.finrank K ↥L₁ = 2 := by
    rw [hL₁def, Submodule.finrank_sup_span_singleton hz₁_notin,
      finrank_span_singleton hα0]
  have hdim₂ : Module.finrank K ↥L₂ = 2 := by
    rw [hL₂def, Submodule.finrank_sup_span_singleton hz₂_notin,
      finrank_span_singleton hα0]
  have hL₁ : IsFlipLine σ L₁ := by
    refine ⟨?_, hdim₁⟩
    rw [hL₁def]
    exact (isFlipflopSub_span_pair_iff hσ hαq hz₁q hαz₁ hαh hz₁_notin).mpr hu₁'
  have hL₂ : IsFlipLine σ L₂ := by
    refine ⟨?_, hdim₂⟩
    rw [hL₂def]
    exact (isFlipflopSub_span_pair_iff hσ hαq hz₂q hαz₂ hαh hz₂_notin).mpr hu₂'
  have hz₁γ : polar (quadPlus n K) z₁ γ = 0 := by
    rw [polar_comm (quadPlus n K)]; exact hγz₁
  have hz₁β : polar (quadPlus n K) z₁ β = 0 := by
    rw [polar_comm (quadPlus n K)]; exact hβz₁
  have hz₂γ : polar (quadPlus n K) z₂ γ = 0 := by
    rw [polar_comm (quadPlus n K)]; exact hγz₂
  have hz₂δ : polar (quadPlus n K) z₂ δ = 0 := by
    rw [polar_comm (quadPlus n K)]; exact hδz₂
  have hz₂α : polar (quadPlus n K) z₂ α = 0 := by
    rw [polar_comm (quadPlus n K)]; exact hαz₂
  have hz₂z₁ : polar (quadPlus n K) z₂ z₁ = 0 := by
    rw [polar_comm (quadPlus n K)]; exact hz₁z₂
  have hcL₁ : c.1 ≤ qPerp n K L₁ := by
    rw [hγspan, hL₁def]
    exact span_singleton_le_qPerp_sup hαγ hz₁γ
  have hcL₂ : c.1 ≤ qPerp n K L₂ := by
    rw [hγspan, hL₂def]
    exact span_singleton_le_qPerp_sup hαγ hz₂γ
  have hbL₁ : b.1 ≤ qPerp n K L₁ := by
    rw [hβspan, hL₁def]
    exact span_singleton_le_qPerp_sup hαβ hz₁β
  have hdL₂ : d.1 ≤ qPerp n K L₂ := by
    rw [hδspan, hL₂def]
    exact span_singleton_le_qPerp_sup hαδ hz₂δ
  have hL₁L₂ : L₁ ≤ qPerp n K L₂ := by
    rw [hL₁def, hL₂def]
    refine sup_le ?_ ?_
    · exact span_singleton_le_qPerp_sup (polar_self_of_singular hαq) hz₂α
    · exact span_singleton_le_qPerp_sup hαz₁ hz₂z₁
  have haL₁ : a.1 ≤ L₁ := by rw [hαspan, hL₁def]; exact le_sup_left
  have haL₂ : a.1 ≤ L₂ := by rw [hαspan, hL₂def]; exact le_sup_left
  exact ⟨L₁, L₂, hL₁, hL₂, hcL₁, hcL₂, hbL₁, hdL₂, hL₁L₂, haL₁, haL₂⟩

private theorem exists_flip_point_on_perp_line (hσ : IsUnitaryInvolution σ) [Finite K] {q : ℕ}
    (hK : Nat.card K = q ^ 2) (hq : 4 ≤ q)
    {L : Submodule K (Fin n ⊕ Fin n → K)} (hL : IsFlipLine σ L) {a : FlipPt σ n}
    (haL : a.1 ≤ L) {c : FlipPt σ n} (hcL : c.1 ≤ qPerp n K L) :
    ∃ p : FlipPt σ n, (flipGraph σ n).Adj a p ∧ (flipGraph σ n).Adj p c ∧ p.1 ≤ L := by
  obtain ⟨p₀, hp₀_pts, hp₀_ne_a, -, hp₀coll⟩ :=
    exists_flipColl_ne hσ hK hq hL c.2 hcL a.1 a.1
  let p : FlipPt σ n := ⟨p₀, hp₀_pts.1⟩
  refine ⟨p, ?_, ?_, hp₀_pts.2⟩
  · exact flipColl_of_le_line hL ⟨a.2, haL⟩ hp₀_pts (Ne.symm hp₀_ne_a)
  · exact flipColl_symm hp₀coll

theorem cycleHomotopic_quad_of_perp (hσ : IsUnitaryInvolution σ) [Finite K] {q : ℕ}
    (hK : Nat.card K = q ^ 2) (hq : 4 ≤ q) (hn : 4 ≤ n) (h3 : NullLen (solidWalks σ n) 3)
    {a b c d : FlipPt σ n} (hab : (flipGraph σ n).Adj a b) (hbc : (flipGraph σ n).Adj b c)
    (hcd : (flipGraph σ n).Adj c d) (hda : (flipGraph σ n).Adj d a)
    (hac : a.1 ≤ qPerp n K c.1) :
    CycleHomotopic (solidWalks σ n) (quadWalk hab hbc hcd hda) .nil := by
  classical
  by_cases hbd : b.1 ≤ qPerp n K d.1
  · exact cycleHomotopic_quad_of_perp₂ hσ hK hq h3 hab hbc hcd hda hac hbd
  · by_cases hac_eq : a = c
    · subst hac_eq
      exact cycleHomotopic_quad_of_perp_eq hab hbc hcd hda
    · obtain ⟨α, β, γ, δ, hαspan, hβspan, hγspan, hδspan, hαq, hβq, hγq, hδq,
        hαh, hβh, hγh, hδh, hβα, hβγ, hδα, hδγ, hαγ, hβδ, hα0, hβ0, hγ0, hδ0,
        hα_notin⟩ := exists_quad_span_data hab hbc hcd hda hac hbd hac_eq
      obtain ⟨s, s', w, hs_q, hs'_q, hss', hs0, hperp, hαw, hβw, hδw⟩ :=
        exists_perp_hyperbolic_pair hαq hβq hγq hβα hβγ hδα hδγ hαγ hβδ hγ0
          hα_notin hn
      obtain ⟨hαs, hαs', hβs, hβs', hγs, hγs', hδs, hδs', hws, hws'⟩ :=
        polar_orthogonal_facts hperp
      obtain ⟨hsw, hsδ, hs'β, hwα, hwβ, hwδ, hαβ, hαδ, hγβ, hγδ, hδβ, hs'0⟩ :=
        polar_symmetry_facts hws hδs hβs' hαw hβw hδw hβα hβγ hδα hδγ hβδ hss'
      obtain ⟨hind₁, hind₂⟩ :=
        toA_independent_pair hwα hwβ hwδ hws hws' hsδ hs'β hβδ hδβ hs0 hs'0
      have hβ_notin : β ∉ K ∙ α :=
        notin_span_of_ne hαspan hβspan hα0 hβ0 hab.1
      have hδ_notin : δ ∉ K ∙ α :=
        notin_span_of_ne hαspan hδspan hα0 hδ0 hda.1.symm
      have hu₁ : herm σ (projPerp σ (toA n K α) (toA n K β))
          (projPerp σ (toA n K α) (toA n K β)) ≠ 0 :=
        (isFlipflopSub_span_pair_iff hσ hαq hβq hαβ hαh hβ_notin).mp
          (by simpa [hαspan, hβspan] using hab.2)
      have hu₂ : herm σ (projPerp σ (toA n K α) (toA n K δ))
          (projPerp σ (toA n K α) (toA n K δ)) ≠ 0 :=
        (isFlipflopSub_span_pair_iff hσ hαq hδq hαδ hαh hδ_notin).mp
          (by simpa [hαspan, hδspan, sup_comm] using hda.2)
      obtain ⟨t, ht0, htB₁, htB₂⟩ :=
        exists_good_parameter hσ hK hq hαh hβδ hind₁ hind₂ hu₁ hu₂
      obtain ⟨z₁, z₂, hz₁def, hz₂def, hz₁q, hz₂q, hu₁', hu₂', hαz₁, hγz₁, hβz₁,
        hαz₂, hγz₂, hδz₂, hz₁z₂, hz₁_notin, hz₂_notin⟩ :=
        exists_orthogonal_vectors t hβq hδq hs_q hs'_q hαβ hαδ hγβ hγδ hαs hγs
          hβs hαs' hγs' hδs' hβs' hsδ hss' hind₁ hind₂ ht0 htB₁ htB₂
      obtain ⟨L₁, L₂, hL₁, hL₂, hcL₁, hcL₂, hbL₁, hdL₂, hL₁L₂, haL₁, haL₂⟩ :=
        exists_two_perp_flip_lines hσ hαspan hβspan hγspan hδspan hαq hαh hα0 hz₁q hz₂q
          hαz₁ hαz₂ hu₁' hu₂' hz₁_notin hz₂_notin hγz₁ hβz₁ hγz₂ hδz₂ hz₁z₂
          hαγ hαβ hαδ
      obtain ⟨p, hap, hpc, hp_le_L₁⟩ :=
        exists_flip_point_on_perp_line hσ hK hq hL₁ haL₁ hcL₁
      obtain ⟨p', hap', hp'c, hq_le_L₂⟩ :=
        exists_flip_point_on_perp_line hσ hK hq hL₂ haL₂ hcL₂
      have hbp : b.1 ≤ qPerp n K p.1 := le_trans hbL₁ (qPerp_antitone hp_le_L₁)
      have hpp' : p.1 ≤ qPerp n K p'.1 :=
        le_trans (le_trans hp_le_L₁ hL₁L₂) (qPerp_antitone hq_le_L₂)
      have hp'd : p'.1 ≤ qPerp n K d.1 := le_trans hq_le_L₂ (le_qPerp_symm hdL₂)
      exact cycleHomotopic_quad_of_aux hσ hK hq h3 hab hbc hcd hda hap hpc hap' hp'c hac
        hbp hpp' hp'd

private theorem exists_quad_span_data_nonperp {a b c d : FlipPt σ n}
    (hab : (flipGraph σ n).Adj a b) (hbc : (flipGraph σ n).Adj b c)
    (hcd : (flipGraph σ n).Adj c d) (hda : (flipGraph σ n).Adj d a)
    (hac : ¬ a.1 ≤ qPerp n K c.1) (hbd : ¬ b.1 ≤ qPerp n K d.1) :
    ∃ α β γ δ : Fin n ⊕ Fin n → K, a.1 = K ∙ α ∧ b.1 = K ∙ β ∧ c.1 = K ∙ γ ∧
      d.1 = K ∙ δ ∧ quadPlus n K α = 0 ∧ quadPlus n K β = 0 ∧ quadPlus n K γ = 0 ∧
      quadPlus n K δ = 0 ∧ flipHerm σ α α ≠ 0 ∧ polar (quadPlus n K) α β = 0 ∧
      polar (quadPlus n K) α δ = 0 ∧ polar (quadPlus n K) β γ = 0 ∧
      polar (quadPlus n K) γ δ = 0 ∧ polar (quadPlus n K) α γ ≠ 0 ∧
      polar (quadPlus n K) β δ ≠ 0 := by
  classical
  obtain ⟨α, hαspan, hαq, hαh⟩ := IsFlipflopPt.exists_eq_span a.2
  obtain ⟨β, hβspan, hβq, hβh⟩ := IsFlipflopPt.exists_eq_span b.2
  obtain ⟨γ, hγspan, hγq, hγh⟩ := IsFlipflopPt.exists_eq_span c.2
  obtain ⟨δ, hδspan, hδq, hδh⟩ := IsFlipflopPt.exists_eq_span d.2
  have hαβ : polar (quadPlus n K) α β = 0 := polar_zero_of_le hαspan hβspan hab.le_qPerp
  have hαδ : polar (quadPlus n K) α δ = 0 := polar_zero_of_le hαspan hδspan hda.symm.le_qPerp
  have hβγ : polar (quadPlus n K) β γ = 0 := polar_zero_of_le hβspan hγspan hbc.le_qPerp
  have hγδ : polar (quadPlus n K) γ δ = 0 := polar_zero_of_le hγspan hδspan hcd.le_qPerp
  have hαγ : polar (quadPlus n K) α γ ≠ 0 := by
    intro h
    apply hac
    rw [hαspan, hγspan]
    intro y hy
    rw [mem_qPerp]
    intro w hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hw
    simp [polar_smul_right, polar_comm (quadPlus n K), h]
  have hβδ : polar (quadPlus n K) β δ ≠ 0 := by
    intro h
    apply hbd
    rw [hβspan, hδspan]
    intro y hy
    rw [mem_qPerp]
    intro w hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hw
    simp [polar_smul_right, polar_comm (quadPlus n K), h]
  exact ⟨α, β, γ, δ, hαspan, hβspan, hγspan, hδspan, hαq, hβq, hγq, hδq, hαh,
    hαβ, hαδ, hβγ, hγδ, hαγ, hβδ⟩

private theorem exists_solid_of_quad (hσ : IsUnitaryInvolution σ) (hn : 4 ≤ n)
    {α β γ δ : Fin n ⊕ Fin n → K} (hαq : quadPlus n K α = 0) (hβq : quadPlus n K β = 0)
    (hαh : flipHerm σ α α ≠ 0) (hαβ : polar (quadPlus n K) α β = 0)
    (hαδ : polar (quadPlus n K) α δ = 0) (hβγ : polar (quadPlus n K) β γ = 0)
    (hγδ : polar (quadPlus n K) γ δ = 0) (hαγ : polar (quadPlus n K) α γ ≠ 0)
    (hβδ : polar (quadPlus n K) β δ ≠ 0) :
    ∃ A₀ N : Submodule K (Fin n ⊕ Fin n → K), ∃ e : Submodule K (Fin n ⊕ Fin n → K),
      A₀ = K ∙ α ⊔ K ∙ γ ∧ N = A₀ ⊔ K ∙ β ⊔ K ∙ δ ∧ QPlus N ∧ QNondeg N ∧
      e ≤ qPerp n K N ∧ IsFlipflopPt σ e := by
  classical
  have hbot : QNondeg (⊥ : Submodule K (Fin n ⊕ Fin n → K)) := by
    rw [QNondeg, bot_inf_eq]
  have hbotPlus : QPlus (⊥ : Submodule K (Fin n ⊕ Fin n → K)) := by
    refine ⟨⊥, le_rfl, ?_, by simp⟩
    intro w hw
    rw [Submodule.mem_bot] at hw
    rw [hw, map_zero]
  have hαperp : α ∈ qPerp n K (⊥ : Submodule K (Fin n ⊕ Fin n → K)) := by
    rw [qPerp_bot]
    exact Submodule.mem_top
  obtain ⟨A₀, hA₀⟩ : ∃ A₀ : Submodule K (Fin n ⊕ Fin n → K), A₀ = K ∙ α ⊔ K ∙ γ :=
    ⟨K ∙ α ⊔ K ∙ γ, rfl⟩
  have hA₀plus : QPlus A₀ := by
    rw [hA₀]
    exact qplus_of_hyperbolic_pair hαq hαγ
  have hA₀nd : QNondeg A₀ := by
    rw [hA₀]
    have h := QNondeg.sup_pair (A := ⊥) (v := α) (w := γ) hbot hαperp hαq hαγ
    simpa only [bot_sup_eq] using h.1
  have hβperp : β ∈ qPerp n K A₀ := by
    rw [hA₀, qPerp_sup, Submodule.mem_inf]
    constructor
    · rw [mem_qPerp]; intro y hy
      obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hy
      simp [polar_comm (quadPlus n K), hαβ]
    · rw [mem_qPerp]; intro y hy
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hy
      simp [polar_comm (quadPlus n K), hβγ]
  have hδperp : δ ∈ qPerp n K A₀ := by
    rw [hA₀, qPerp_sup, Submodule.mem_inf]
    constructor
    · rw [mem_qPerp]; intro y hy
      obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hy
      simp [polar_comm (quadPlus n K), hαδ]
    · rw [mem_qPerp]; intro y hy
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hy
      simp [polar_comm (quadPlus n K), hγδ]
  obtain ⟨N, hN⟩ : ∃ N : Submodule K (Fin n ⊕ Fin n → K), N = A₀ ⊔ K ∙ β ⊔ K ∙ δ :=
    ⟨A₀ ⊔ K ∙ β ⊔ K ∙ δ, rfl⟩
  have hNplus : QPlus N := by
    rw [hN]
    exact qplus_sup_pair (A := A₀) hA₀nd hA₀plus hβperp hβq hβδ
  have hNnd : QNondeg N := by
    rw [hN]
    have h := QNondeg.sup_pair (A := A₀) (v := β) (w := δ) hA₀nd hβperp hβq hβδ
    simpa using h.1
  have hNdim : Module.finrank K N = 4 := by
    rw [hN]
    have h := (QNondeg.sup_pair (A := A₀) (v := β) (w := δ)
      hA₀nd hβperp hβq hβδ).2
    have hA₀dim : Module.finrank K A₀ = 2 := by
      rw [hA₀]
      have h := (QNondeg.sup_pair (A := ⊥) (v := α) (w := γ) hbot hαperp hαq hαγ).2
      rw [finrank_bot, zero_add, bot_sup_eq] at h
      simpa using h
    rw [hA₀dim] at h
    omega
  have hCdim : Module.finrank K (qPerp n K N) = 2 * n - 4 := by
    have h := finrank_qPerp (n := n) (K := K) N
    rw [hNdim] at h
    omega
  have hCn : n ≤ Module.finrank K (qPerp n K N) := by omega
  have hC4 : 4 ≤ Module.finrank K (qPerp n K N) := by omega
  have hαC : α ∈ qPerp n K (qPerp n K N) := by
    rw [qPerp_qPerp, hN, hA₀]
    exact Submodule.mem_sup_left (Submodule.mem_sup_left
      (Submodule.mem_sup_left (Submodule.mem_span_singleton_self α)))
  have hne : ∃ u ∈ qPerp n K N, ∃ v ∈ qPerp n K N, flipHerm σ u v ≠ 0 :=
    exists_flipHerm_ne_zero_of_le hσ.invol hCn hαC hαh
  obtain ⟨e, heC, he_pt⟩ := exists_isFlipflopPt_le_of_qPlus hσ
    (QNondeg.qPerp hNnd) (QPlus.qPerp hNnd hNplus) hC4 hne
  exact ⟨A₀, N, e, hA₀, hN, hNplus, hNnd, heC, he_pt⟩

private theorem vertices_le_solid {a b c d : FlipPt σ n} {α β γ δ : Fin n ⊕ Fin n → K}
    {A₀ N : Submodule K (Fin n ⊕ Fin n → K)} (hαspan : a.1 = K ∙ α)
    (hβspan : b.1 = K ∙ β) (hγspan : c.1 = K ∙ γ) (hδspan : d.1 = K ∙ δ)
    (hA₀ : A₀ = K ∙ α ⊔ K ∙ γ) (hN : N = A₀ ⊔ K ∙ β ⊔ K ∙ δ) :
    a.1 ≤ N ∧ b.1 ≤ N ∧ c.1 ≤ N ∧ d.1 ≤ N := by
  have haN : a.1 ≤ N := by
    rw [hαspan, hN, hA₀]
    exact le_trans le_sup_left (le_trans le_sup_left le_sup_left)
  have hbN : b.1 ≤ N := by
    rw [hβspan, hN, hA₀]
    exact le_trans le_sup_right le_sup_left
  have hcN : c.1 ≤ N := by
    rw [hγspan, hN, hA₀]
    exact le_trans le_sup_right (le_trans le_sup_left le_sup_left)
  have hdN : d.1 ≤ N := by
    rw [hδspan, hN, hA₀]
    exact le_sup_right
  exact ⟨haN, hbN, hcN, hdN⟩

private theorem exists_wheel_points (hσ : IsUnitaryInvolution σ) [Finite K] {q : ℕ}
    (hK : Nat.card K = q ^ 2) (hq : 4 ≤ q) {a b c d e : FlipPt σ n}
    (hab : (flipGraph σ n).Adj a b) (hbc : (flipGraph σ n).Adj b c)
    (hcd : (flipGraph σ n).Adj c d) (hda : (flipGraph σ n).Adj d a)
    {N : Submodule K (Fin n ⊕ Fin n → K)} (haN : a.1 ≤ N) (hbN : b.1 ≤ N)
    (hcN : c.1 ≤ N) (hdN : d.1 ≤ N) (heC : e.1 ≤ qPerp n K N) :
    ∃ m₁ m₂ m₃ m₄ : FlipPt σ n,
      (flipGraph σ n).Adj m₁ a ∧ (flipGraph σ n).Adj m₁ b ∧
      (flipGraph σ n).Adj m₂ b ∧ (flipGraph σ n).Adj m₂ c ∧
      (flipGraph σ n).Adj m₃ c ∧ (flipGraph σ n).Adj m₃ d ∧
      (flipGraph σ n).Adj m₄ d ∧ (flipGraph σ n).Adj m₄ a ∧
      (flipGraph σ n).Adj m₁ e ∧ (flipGraph σ n).Adj m₂ e ∧
      (flipGraph σ n).Adj m₃ e ∧ (flipGraph σ n).Adj m₄ e := by
  classical
  have hL₁ : IsFlipLine σ (a.1 ⊔ b.1) := hab.isFlipLine a.2 b.2
  have hL₂ : IsFlipLine σ (b.1 ⊔ c.1) := hbc.isFlipLine b.2 c.2
  have hL₃ : IsFlipLine σ (c.1 ⊔ d.1) := hcd.isFlipLine c.2 d.2
  have hL₄ : IsFlipLine σ (d.1 ⊔ a.1) := hda.isFlipLine d.2 a.2
  have he₁ : e.1 ≤ qPerp n K (a.1 ⊔ b.1) :=
    le_trans heC (qPerp_antitone (sup_le haN hbN))
  have he₂ : e.1 ≤ qPerp n K (b.1 ⊔ c.1) :=
    le_trans heC (qPerp_antitone (sup_le hbN hcN))
  have he₃ : e.1 ≤ qPerp n K (c.1 ⊔ d.1) :=
    le_trans heC (qPerp_antitone (sup_le hcN hdN))
  have he₄ : e.1 ≤ qPerp n K (d.1 ⊔ a.1) :=
    le_trans heC (qPerp_antitone (sup_le hdN haN))
  obtain ⟨m₁, hm₁_pts, hm₁a_ne, hm₁b_ne, hm₁e⟩ :=
    exists_flipColl_ne hσ hK hq hL₁ e.2 he₁ a.1 b.1
  obtain ⟨m₂, hm₂_pts, hm₂b_ne, hm₂c_ne, hm₂e⟩ :=
    exists_flipColl_ne hσ hK hq hL₂ e.2 he₂ b.1 c.1
  obtain ⟨m₃, hm₃_pts, hm₃c_ne, hm₃d_ne, hm₃e⟩ :=
    exists_flipColl_ne hσ hK hq hL₃ e.2 he₃ c.1 d.1
  obtain ⟨m₄, hm₄_pts, hm₄d_ne, hm₄a_ne, hm₄e⟩ :=
    exists_flipColl_ne hσ hK hq hL₄ e.2 he₄ d.1 a.1
  let m₁_pt : FlipPt σ n := ⟨m₁, hm₁_pts.1⟩
  let m₂_pt : FlipPt σ n := ⟨m₂, hm₂_pts.1⟩
  let m₃_pt : FlipPt σ n := ⟨m₃, hm₃_pts.1⟩
  let m₄_pt : FlipPt σ n := ⟨m₄, hm₄_pts.1⟩
  have hm₁a : (flipGraph σ n).Adj m₁_pt a :=
    flipColl_of_le_line hL₁ hm₁_pts ⟨a.2, le_sup_left⟩ hm₁a_ne
  have hm₁b : (flipGraph σ n).Adj m₁_pt b :=
    flipColl_of_le_line hL₁ hm₁_pts ⟨b.2, le_sup_right⟩ hm₁b_ne
  have hm₂b : (flipGraph σ n).Adj m₂_pt b :=
    flipColl_of_le_line hL₂ hm₂_pts ⟨b.2, le_sup_left⟩ hm₂b_ne
  have hm₂c : (flipGraph σ n).Adj m₂_pt c :=
    flipColl_of_le_line hL₂ hm₂_pts ⟨c.2, le_sup_right⟩ hm₂c_ne
  have hm₃c : (flipGraph σ n).Adj m₃_pt c :=
    flipColl_of_le_line hL₃ hm₃_pts ⟨c.2, le_sup_left⟩ hm₃c_ne
  have hm₃d : (flipGraph σ n).Adj m₃_pt d :=
    flipColl_of_le_line hL₃ hm₃_pts ⟨d.2, le_sup_right⟩ hm₃d_ne
  have hm₄d : (flipGraph σ n).Adj m₄_pt d :=
    flipColl_of_le_line hL₄ hm₄_pts ⟨d.2, le_sup_left⟩ hm₄d_ne
  have hm₄a : (flipGraph σ n).Adj m₄_pt a :=
    flipColl_of_le_line hL₄ hm₄_pts ⟨a.2, le_sup_right⟩ hm₄a_ne
  have hm₁e' : (flipGraph σ n).Adj m₁_pt e := flipColl_symm hm₁e
  have hm₂e' : (flipGraph σ n).Adj m₂_pt e := flipColl_symm hm₂e
  have hm₃e' : (flipGraph σ n).Adj m₃_pt e := flipColl_symm hm₃e
  have hm₄e' : (flipGraph σ n).Adj m₄_pt e := flipColl_symm hm₄e
  exact ⟨m₁_pt, m₂_pt, m₃_pt, m₄_pt, hm₁a, hm₁b, hm₂b, hm₂c, hm₃c, hm₃d,
    hm₄d, hm₄a, hm₁e', hm₂e', hm₃e', hm₄e'⟩

private theorem cycleHomotopic_quad_wheel_of_points (hσ : IsUnitaryInvolution σ) [Finite K]
    {q : ℕ} (hK : Nat.card K = q ^ 2) (hq : 4 ≤ q) (hn : 4 ≤ n)
    (h3 : NullLen (solidWalks σ n) 3) {a b c d e m₁ m₂ m₃ m₄ : FlipPt σ n}
    (hab : (flipGraph σ n).Adj a b) (hbc : (flipGraph σ n).Adj b c)
    (hcd : (flipGraph σ n).Adj c d) (hda : (flipGraph σ n).Adj d a)
    (hm₁a : (flipGraph σ n).Adj m₁ a) (hm₁b : (flipGraph σ n).Adj m₁ b)
    (hm₂b : (flipGraph σ n).Adj m₂ b) (hm₂c : (flipGraph σ n).Adj m₂ c)
    (hm₃c : (flipGraph σ n).Adj m₃ c) (hm₃d : (flipGraph σ n).Adj m₃ d)
    (hm₄d : (flipGraph σ n).Adj m₄ d) (hm₄a : (flipGraph σ n).Adj m₄ a)
    (hm₁e : (flipGraph σ n).Adj m₁ e) (hm₂e : (flipGraph σ n).Adj m₂ e)
    (hm₃e : (flipGraph σ n).Adj m₃ e) (hm₄e : (flipGraph σ n).Adj m₄ e)
    {N : Submodule K (Fin n ⊕ Fin n → K)} (haN : a.1 ≤ N) (hbN : b.1 ≤ N)
    (hcN : c.1 ≤ N) (hdN : d.1 ≤ N) (heC : e.1 ≤ qPerp n K N) :
    CycleHomotopic (solidWalks σ n) (quadWalk hab hbc hcd hda) .nil := by
  have hae : a.1 ≤ qPerp n K e.1 := le_qPerp_symm (le_trans heC (qPerp_antitone haN))
  have hbe : b.1 ≤ qPerp n K e.1 := le_qPerp_symm (le_trans heC (qPerp_antitone hbN))
  have hce : c.1 ≤ qPerp n K e.1 := le_qPerp_symm (le_trans heC (qPerp_antitone hcN))
  have hde : d.1 ≤ qPerp n K e.1 := le_qPerp_symm (le_trans heC (qPerp_antitone hdN))
  have hSa : CycleHomotopic (solidWalks σ n)
      (quadWalk hm₁a.symm hm₁e hm₄e.symm hm₄a) .nil :=
    cycleHomotopic_quad_of_perp hσ hK hq hn h3 hm₁a.symm hm₁e hm₄e.symm hm₄a hae
  have hSb_rot : CycleHomotopic (solidWalks σ n)
      (quadWalk hm₂b.symm hm₂e hm₁e.symm hm₁b) .nil :=
    cycleHomotopic_quad_of_perp hσ hK hq hn h3 hm₂b.symm hm₂e hm₁e.symm hm₁b hbe
  have hSb : CycleHomotopic (solidWalks σ n)
      (quadWalk hm₁b hm₂b.symm hm₂e hm₁e.symm) .nil :=
    cycleHomotopic_quad_rotate_rev (solidWalks σ n) hm₁b hm₂b.symm hm₂e hm₁e.symm hSb_rot
  have hSc_rot : CycleHomotopic (solidWalks σ n)
      (quadWalk hm₃c.symm hm₃e hm₂e.symm hm₂c) .nil :=
    cycleHomotopic_quad_of_perp hσ hK hq hn h3 hm₃c.symm hm₃e hm₂e.symm hm₂c hce
  have hSc : CycleHomotopic (solidWalks σ n)
      (quadWalk hm₂c hm₃c.symm hm₃e hm₂e.symm) .nil :=
    cycleHomotopic_quad_rotate_rev (solidWalks σ n) hm₂c hm₃c.symm hm₃e hm₂e.symm hSc_rot
  have hSd_rot : CycleHomotopic (solidWalks σ n)
      (quadWalk hm₄d.symm hm₄e hm₃e.symm hm₃d) .nil :=
    cycleHomotopic_quad_of_perp hσ hK hq hn h3 hm₄d.symm hm₄e hm₃e.symm hm₃d hde
  have hSd : CycleHomotopic (solidWalks σ n)
      (quadWalk hm₃d hm₄d.symm hm₄e hm₃e.symm) .nil :=
    cycleHomotopic_quad_rotate_rev (solidWalks σ n) hm₃d hm₄d.symm hm₄e hm₃e.symm hSd_rot
  exact cycleHomotopic_quad_wheel (solidWalks σ n) h3 hab hbc hcd hda
    hm₁a hm₁b hm₁e hm₂b hm₂c hm₂e hm₃c hm₃d hm₃e hm₄d hm₄a hm₄e
    hSa hSb hSc hSd

theorem cycleHomotopic_quad (hσ : IsUnitaryInvolution σ) [Finite K] {q : ℕ}
    (hK : Nat.card K = q ^ 2) (hq : 4 ≤ q) (hn : 4 ≤ n) (h3 : NullLen (solidWalks σ n) 3)
    {a b c d : FlipPt σ n} (hab : (flipGraph σ n).Adj a b) (hbc : (flipGraph σ n).Adj b c)
    (hcd : (flipGraph σ n).Adj c d) (hda : (flipGraph σ n).Adj d a) :
    CycleHomotopic (solidWalks σ n) (quadWalk hab hbc hcd hda) .nil := by
  classical
  by_cases hac : a.1 ≤ qPerp n K c.1
  · exact cycleHomotopic_quad_of_perp hσ hK hq hn h3 hab hbc hcd hda hac
  · by_cases hbd : b.1 ≤ qPerp n K d.1
    · exact cycleHomotopic_quad_rotate_rev (solidWalks σ n) hab hbc hcd hda
        (cycleHomotopic_quad_of_perp hσ hK hq hn h3 hbc hcd hda hab hbd)
    · obtain ⟨α, β, γ, δ, hαspan, hβspan, hγspan, hδspan, hαq, hβq, hγq, hδq,
        hαh, hαβ, hαδ, hβγ, hγδ, hαγ, hβδ⟩ :=
        exists_quad_span_data_nonperp hab hbc hcd hda hac hbd
      obtain ⟨A₀, N, e, hA₀, hN, hNplus, hNnd, heC, he_pt⟩ :=
        exists_solid_of_quad hσ hn hαq hβq hαh hαβ hαδ hβγ hγδ hαγ hβδ
      let e_pt : FlipPt σ n := ⟨e, he_pt⟩
      have heC' : e_pt.1 ≤ qPerp n K N := heC
      obtain ⟨haN, hbN, hcN, hdN⟩ :=
        vertices_le_solid hαspan hβspan hγspan hδspan hA₀ hN
      obtain ⟨m₁, m₂, m₃, m₄, hm₁a, hm₁b, hm₂b, hm₂c, hm₃c, hm₃d, hm₄d, hm₄a,
        hm₁e, hm₂e, hm₃e, hm₄e⟩ :=
        exists_wheel_points hσ hK hq hab hbc hcd hda haN hbN hcN hdN heC'
      exact cycleHomotopic_quad_wheel_of_points hσ hK hq hn h3 hab hbc hcd hda
        hm₁a hm₁b hm₂b hm₂c hm₃c hm₃d hm₄d hm₄a hm₁e hm₂e hm₃e hm₄e
        haN hbN hcN hdN heC'
theorem nullLen_four_of_nullLen_three (hσ : IsUnitaryInvolution σ) [Finite K] {q : ℕ}
    (hK : Nat.card K = q ^ 2) (hq : 4 ≤ q) (hn : 4 ≤ n) (h3 : NullLen (solidWalks σ n) 3) :
    NullLen (solidWalks σ n) 4 := by
  intro u p hp
  match u, p, hp with
  | _, .nil, hp => simp at hp
  | _, .cons _ .nil, hp => simp at hp
  | _, .cons _ (.cons _ .nil), hp => simp at hp
  | _, .cons _ (.cons _ (.cons _ .nil)), hp => simp at hp
  | a, .cons (v := b) hab (.cons (v := c) hbc (.cons (v := d) hcd (.cons hda .nil))), _ =>
    by_cases hac : a.1 ≤ qPerp n K c.1
    · exact cycleHomotopic_quad_of_perp hσ hK hq hn h3 hab hbc hcd hda hac
    · by_cases hbd : b.1 ≤ qPerp n K d.1
      · exact cycleHomotopic_quad_rotate_rev (solidWalks σ n) hab hbc hcd hda
          (cycleHomotopic_quad_of_perp hσ hK hq hn h3 hbc hcd hda hab hbd)
      · exact cycleHomotopic_quad hσ hK hq hn h3 hab hbc hcd hda
