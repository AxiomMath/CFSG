module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6LayerData
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Layer

open CFSG.Open Subgroup CFSG.ABGLocalTools CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Aux
  CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Mod CFSG.ComponentClassification

theorem vec_pair_sum (a b c : ZMod 3) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hnc : ¬ (a = b ∧ b = c)) :
    (c + b = 0 ∧ a + c = 0) ∨ (c + b = 0 ∧ b + a = 0) ∨ (a + c = 0 ∧ b + a = 0) := by
  revert ha hb hc hnc
  revert a b c
  decide

theorem vec_diff_pos (a b c : ZMod 3) (hnc : ¬ (a = b ∧ b = c)) :
    ¬ ((((b, c, a) + -(c, a, b) : Vec)).2.1 = 0 ∧ (((b, c, a) + -(c, a, b) : Vec)).2.2 = 0) ∧
    ¬ ((((b, c, a) + -(c, a, b) : Vec)).1 = 0 ∧ (((b, c, a) + -(c, a, b) : Vec)).2.2 = 0) ∧
    ¬ ((((b, c, a) + -(c, a, b) : Vec)).1 = 0 ∧ (((b, c, a) + -(c, a, b) : Vec)).2.1 = 0) := by
  revert hnc
  revert a b c
  decide

theorem vec_diff_neg (a b c : ZMod 3) (hnc : ¬ (a = b ∧ b = c)) :
    ¬ (((-(b, c, a) + (c, a, b) : Vec)).2.1 = 0 ∧ ((-(b, c, a) + (c, a, b) : Vec)).2.2 = 0) ∧
    ¬ (((-(b, c, a) + (c, a, b) : Vec)).1 = 0 ∧ ((-(b, c, a) + (c, a, b) : Vec)).2.2 = 0) ∧
    ¬ (((-(b, c, a) + (c, a, b) : Vec)).1 = 0 ∧ ((-(b, c, a) + (c, a, b) : Vec)).2.1 = 0) := by
  revert hnc
  revert a b c
  decide

namespace Tri

variable {X : Type} [Group X] [Finite X] {q₁ q₂ q₃ : X} (hq : VITriple q₁ q₂ q₃)

include hq

theorem coord_zero {L₁ L₂ L₃ : Subgroup X} (h1 : q₁ ∈ L₁) (h2 : q₂ ∈ L₂) (h3 : q₃ ∈ L₃)
    (i1 : (L₂ ⊔ L₃) ⊓ L₁ = ⊥) (i2 : (L₁ ⊔ L₃) ⊓ L₂ = ⊥) (i3 : (L₁ ⊔ L₂) ⊓ L₃ = ⊥) (v : Vec) :
    (qel q₁ q₂ q₃ v ∈ L₁ → v.2.1 = 0 ∧ v.2.2 = 0) ∧
    (qel q₁ q₂ q₃ v ∈ L₂ → v.1 = 0 ∧ v.2.2 = 0) ∧
    (qel q₁ q₂ q₃ v ∈ L₃ → v.1 = 0 ∧ v.2.1 = 0) := by
  obtain ⟨a, b, c⟩ := v
  have hA : gp q₁ a ∈ L₁ := pow_mem h1 _
  have hB : gp q₂ b ∈ L₂ := pow_mem h2 _
  have hC : gp q₃ c ∈ L₃ := pow_mem h3 _
  have hAB : gp q₁ a * gp q₂ b = gp q₂ b * gp q₁ a :=
    (Commute.pow_pow (show Commute q₁ q₂ from hq.comm_x₂) _ _).eq
  have hz : ∀ v : Vec, qel q₁ q₂ q₃ v = 1 → v = 0 := fun v hv => qel_eq_one hq hv
  refine ⟨fun hv => ?_, fun hv => ?_, fun hv => ?_⟩
  · have hBC : gp q₂ b * gp q₃ c ∈ (L₂ ⊔ L₃) ⊓ L₁ := by
      refine mem_inf.mpr ⟨mul_mem (mem_sup_left hB) (mem_sup_right hC), ?_⟩
      have e : gp q₂ b * gp q₃ c = (gp q₁ a)⁻¹ * qel q₁ q₂ q₃ (a, b, c) := by
        simp only [qel]; group
      rw [e]
      exact L₁.mul_mem (L₁.inv_mem hA) hv
    rw [i1, mem_bot] at hBC
    have h0 := hz (0, b, c) (by simp only [qel, gp_zero, one_mul]; exact hBC)
    simp only [Prod.mk_eq_zero] at h0
    exact ⟨h0.2.1, h0.2.2⟩
  · have hAC : gp q₁ a * gp q₃ c ∈ (L₁ ⊔ L₃) ⊓ L₂ := by
      refine mem_inf.mpr ⟨mul_mem (mem_sup_left hA) (mem_sup_right hC), ?_⟩
      have e : gp q₁ a * gp q₃ c = (gp q₂ b)⁻¹ * qel q₁ q₂ q₃ (a, b, c) := by
        simp only [qel]; rw [hAB]; group
      rw [e]
      exact L₂.mul_mem (L₂.inv_mem hB) hv
    rw [i2, mem_bot] at hAC
    have h0 := hz (a, 0, c) (by simp only [qel, gp_zero, mul_one]; exact hAC)
    simp only [Prod.mk_eq_zero] at h0
    exact ⟨h0.1, h0.2.2⟩
  · have hAB' : gp q₁ a * gp q₂ b ∈ (L₁ ⊔ L₂) ⊓ L₃ := by
      refine mem_inf.mpr ⟨mul_mem (mem_sup_left hA) (mem_sup_right hB), ?_⟩
      have e : gp q₁ a * gp q₂ b = qel q₁ q₂ q₃ (a, b, c) * (gp q₃ c)⁻¹ := by
        simp only [qel]; group
      rw [e]
      exact L₃.mul_mem hv (L₃.inv_mem hC)
    rw [i3, mem_bot] at hAB'
    have h0 := hz (a, b, 0) (by simp only [qel, gp_zero, mul_one]; exact hAB')
    simp only [Prod.mk_eq_zero] at h0
    exact ⟨h0.1, h0.2.1⟩

end Tri

section Helpers

variable {X : Type} [Group X]

theorem le_centralizer_singleton {L : Subgroup X} {y : X} (hy : y ∈ centralizer (L : Set X)) :
    L ≤ centralizer ({y} : Set X) := by
  intro l hl
  rw [mem_centralizer_singleton_iff]
  exact mem_centralizer_iff.mp hy l hl

theorem map_conj_map_conj (A : Subgroup X) (g k : X) :
    (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj k).toMonoidHom =
      A.map (MulAut.conj (k * g)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext y
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

end Helpers

namespace XData

variable {X : Type} [Group X] [Finite X] {P : Subgroup X} {x e₂ e₃ t ρ : X} {s : ℤ}
  (hd : XData X P x e₂ e₃ t ρ s)

include hd

theorem not_le_centralizer {L : Subgroup X} (hL : IsComponentOf L ⊤) {q : X} (hqL : q ∈ L)
    (hq3 : q ^ 3 = 1) (hq1 : q ≠ 1) : ¬ L ≤ centralizer ({x} : Set X) := by
  intro hle
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsimple := RadicalFreeLayer.component_simple hd.free L hL
  have h3 : 3 ∣ Nat.card L := by
    have := Subgroup.orderOf_dvd_natCard L hqL
    rwa [orderOf_eq_prime hq3 hq1] at this
  exact not_isPSolvable_of_simple hsimple (component_not_comm hL) h3
    (CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure.isPSolvable_of_le hd.solv hle)

theorem t_mem_normalizer_of_component {L : Subgroup X} (hL : IsComponentOf L ⊤)
    (hQL : Qf x e₂ e₃ ⊓ L ≠ ⊥) : t ∈ normalizer (L : Set X) := by
  by_contra htL
  have hf := hd.frame
  have hfree := hd.free
  set L₂ : Subgroup X := L.map (MulAut.conj t).toMonoidHom with hL₂def
  set L₃ : Subgroup X := L₂.map (MulAut.conj t).toMonoidHom with hL₃def
  have hL₂ : IsComponentOf L₂ ⊤ := isComponent_map_conj hL t
  have hL₃ : IsComponentOf L₃ ⊤ := isComponent_map_conj hL₂ t
  have h12 : L ≠ L₂ := fun h => htL (mem_normalizer_iff_map_conj.mpr h.symm)
  have h23 : L₂ ≠ L₃ := fun h => h12 (Subgroup.map_injective (MulAut.conj t).injective h)
  have h13 : L ≠ L₃ := by
    intro h
    apply h12
    have hc : t * t * t ∈ normalizer (L : Set X) := hd.Q_le_normalizer hL hd.t_cube_mem
    have e1 : L.map (MulAut.conj (t * t * t)).toMonoidHom = L := mem_normalizer_iff_map_conj.mp hc
    have e2 : L₃ = L.map (MulAut.conj (t * t)).toMonoidHom := map_conj_map_conj L t t
    calc L = L.map (MulAut.conj (t * t * t)).toMonoidHom := e1.symm
      _ = (L.map (MulAut.conj (t * t)).toMonoidHom).map (MulAut.conj t).toMonoidHom := by
          rw [map_conj_map_conj, mul_assoc]
      _ = L₃.map (MulAut.conj t).toMonoidHom := by rw [e2]
      _ = L.map (MulAut.conj t).toMonoidHom := by rw [← h]
  have c12 := le_centralizer_of_ne hL hL₂ h12
  have c13 := le_centralizer_of_ne hL hL₃ h13
  have c21 := le_centralizer_of_ne hL₂ hL h12.symm
  have c23 := le_centralizer_of_ne hL₂ hL₃ h23
  have c31 := le_centralizer_of_ne hL₃ hL h13.symm
  have c32 := le_centralizer_of_ne hL₃ hL₂ h23.symm
  have i1 : (L₂ ⊔ L₃) ⊓ L = ⊥ := inf_eq_bot_of_le_centralizer hfree hL (sup_le c21 c31)
  have i2 : (L ⊔ L₃) ⊓ L₂ = ⊥ := inf_eq_bot_of_le_centralizer hfree hL₂ (sup_le c12 c32)
  have i3 : (L ⊔ L₂) ⊓ L₃ = ⊥ := inf_eq_bot_of_le_centralizer hfree hL₃ (sup_le c13 c23)
  have i23 : L₂ ⊓ L₃ = ⊥ := inf_eq_bot_of_le_centralizer hfree hL₃ c23
  obtain ⟨q₁, hq₁, hq₁1⟩ := ((Qf x e₂ e₃ ⊓ L).bot_or_exists_ne_one).resolve_left hQL
  have hq₁Q : q₁ ∈ Qf x e₂ e₃ := (mem_inf.mp hq₁).1
  have hq₁L : q₁ ∈ L := (mem_inf.mp hq₁).2
  set q₂ : X := t * q₁ * t⁻¹ with hq₂def
  set q₃ : X := t * q₂ * t⁻¹ with hq₃def
  have htN := hf.t_mem_normalizer
  have hq₂Q : q₂ ∈ Qf x e₂ e₃ := hf.conj_mem_of_mem_normalizer htN hq₁Q
  have hq₃Q : q₃ ∈ Qf x e₂ e₃ := hf.conj_mem_of_mem_normalizer htN hq₂Q
  have hq₂L : q₂ ∈ L₂ := ⟨q₁, hq₁L, rfl⟩
  have hq₃L : q₃ ∈ L₃ := ⟨q₂, hq₂L, rfl⟩
  have hq₃t : t * q₃ * t⁻¹ = q₁ := by
    have hc := hf.Q_comm _ hd.t_cube_mem q₁ hq₁Q
    calc t * q₃ * t⁻¹ = (t * t * t) * q₁ * (t * t * t)⁻¹ := by rw [hq₃def, hq₂def]; group
      _ = q₁ * (t * t * t) * (t * t * t)⁻¹ := by rw [hc]
      _ = q₁ := by group
  have hne1 : ∀ y : X, y ≠ 1 → t * y * t⁻¹ ≠ 1 := by
    intro y hy h1
    apply hy
    have : y = t⁻¹ * (t * y * t⁻¹) * t := by group
    rw [this, h1]; group
  have hq₂1 : q₂ ≠ 1 := hne1 q₁ hq₁1
  have hq₃1 : q₃ ≠ 1 := hne1 q₂ hq₂1
  have tri : VITriple q₁ q₂ q₃ :=
    { x_pow := hf.Q_exp q₁ hq₁Q, e₂_pow := hf.Q_exp q₂ hq₂Q, e₃_pow := hf.Q_exp q₃ hq₃Q
      x_ne := hq₁1, e₂_ne := hq₂1, e₃_ne := hq₃1
      comm_x₂ := hf.Q_comm _ hq₁Q _ hq₂Q, comm_x₃ := hf.Q_comm _ hq₁Q _ hq₃Q
      comm_23 := hf.Q_comm _ hq₂Q _ hq₃Q
      ind_23 := le_bot_iff.mp (by
        rw [← i23]; exact inf_le_inf (zpowers_le.mpr hq₂L) (zpowers_le.mpr hq₃L))
      ind_x := le_bot_iff.mp (by
        rw [← i1]
        exact inf_le_inf (sup_le_sup (zpowers_le.mpr hq₂L) (zpowers_le.mpr hq₃L))
          (zpowers_le.mpr hq₁L)) }
  have hQq : Qf q₁ q₂ q₃ = Qf x e₂ e₃ :=
    Subgroup.eq_of_le_of_card_ge (Tri.Q_le_of_mem tri hq₁Q hq₂Q hq₃Q)
      (by rw [tri.Q_card, hf.Q_card])
  have hcoord := Tri.coord_zero tri hq₁L hq₂L hq₃L i1 i2 i3
  obtain ⟨⟨a, b, c⟩, hxv⟩ := Tri.exists_qel tri (hQq ▸ hf.x_mem)
  have hxne : ∀ {M₁ : Subgroup X} {q : X}, IsComponentOf M₁ ⊤ → q ∈ M₁ → q ^ 3 = 1 → q ≠ 1 →
      x ∉ centralizer (M₁ : Set X) := fun hM hq h3 h1 hx =>
    hd.not_le_centralizer hM hq h3 h1 (le_centralizer_singleton hx)
  have ha : a ≠ 0 := by
    rintro rfl
    refine hxne hL hq₁L tri.x_pow hq₁1 ?_
    rw [← hxv]
    have hmem : qel q₁ q₂ q₃ (0, b, c) ∈ L₂ ⊔ L₃ := by
      simp only [qel, gp_zero, one_mul]
      exact mul_mem (mem_sup_left (pow_mem hq₂L _)) (mem_sup_right (pow_mem hq₃L _))
    exact sup_le c21 c31 hmem
  have hb : b ≠ 0 := by
    rintro rfl
    refine hxne hL₂ hq₂L tri.e₂_pow hq₂1 ?_
    rw [← hxv]
    have hmem : qel q₁ q₂ q₃ (a, 0, c) ∈ L ⊔ L₃ := by
      simp only [qel, gp_zero, mul_one]
      exact mul_mem (mem_sup_left (pow_mem hq₁L _)) (mem_sup_right (pow_mem hq₃L _))
    exact sup_le c12 c32 hmem
  have hc : c ≠ 0 := by
    rintro rfl
    refine hxne hL₃ hq₃L tri.e₃_pow hq₃1 ?_
    rw [← hxv]
    have hmem : qel q₁ q₂ q₃ (a, b, 0) ∈ L ⊔ L₂ := by
      simp only [qel, gp_zero, mul_one]
      exact mul_mem (mem_sup_left (pow_mem hq₁L _)) (mem_sup_right (pow_mem hq₂L _))
    exact sup_le c13 c23 hmem
  have hrot := Tri.conj_rot tri (t := t) rfl rfl hq₃t
  have he₂v : qel q₁ q₂ q₃ (c, a, b) = e₂ := by rw [← hrot, hxv, hf.t_x]
  have he₃v : qel q₁ q₂ q₃ (b, c, a) = e₃ := by rw [← hrot, he₂v, hf.t_e₂]
  have hnc : ¬ (a = b ∧ b = c) := by
    rintro ⟨rfl, rfl⟩
    exact hf.lines_ne.1 (by rw [← hxv, ← he₂v])
  have he23 : e₂ * e₃ = qel q₁ q₂ q₃ ((c, a, b) + (b, c, a)) := by
    rw [Tri.qel_add tri, he₂v, he₃v]
  have he23' : e₂ * e₃ = qel q₁ q₂ q₃ (c + b, a + c, b + a) := he23
  have hmem23 : e₂ * e₃ ∈ L ∨ e₂ * e₃ ∈ L₂ ∨ e₂ * e₃ ∈ L₃ := by
    rcases vec_pair_sum a b c ha hb hc hnc with ⟨k1, k2⟩ | ⟨k1, k3⟩ | ⟨k2, k3⟩
    · right; right
      rw [he23', k1, k2]
      simp only [qel, gp_zero, one_mul]
      exact pow_mem hq₃L _
    · right; left
      rw [he23', k1, k3]
      simp only [qel, gp_zero, mul_one, one_mul]
      exact pow_mem hq₂L _
    · left
      rw [he23', k2, k3]
      simp only [qel, gp_zero, mul_one]
      exact pow_mem hq₁L _
  have hw : ρ * (e₂ * e₃) * ρ⁻¹ = e₃ ^ s * e₂ ^ (-s) := by
    rw [show ρ * (e₂ * e₃) * ρ⁻¹ = (ρ * e₂ * ρ⁻¹) * (ρ * e₃ * ρ⁻¹) by group, hf.ρ_e₂, hf.ρ_e₃]
  have hwQ : ρ * (e₂ * e₃) * ρ⁻¹ ∈ Qf x e₂ e₃ :=
    hf.conj_mem_of_mem_normalizer hf.ρ_mem_normalizer (mul_mem hf.e₂_mem hf.e₃_mem)
  have he231 : e₂ * e₃ ≠ 1 := by
    intro h1
    have h2 : e₂ = e₃⁻¹ := eq_inv_of_mul_eq_one_left h1
    have : e₂ ∈ zpowers e₂ ⊓ zpowers e₃ :=
      mem_inf.mpr ⟨mem_zpowers e₂, h2 ▸ inv_mem (mem_zpowers e₃)⟩
    rw [hf.ind_23, mem_bot] at this
    exact hf.e₂_ne this
  have hw1 : ρ * (e₂ * e₃) * ρ⁻¹ ≠ 1 := by
    intro h1
    apply he231
    have : e₂ * e₃ = ρ⁻¹ * (ρ * (e₂ * e₃) * ρ⁻¹) * ρ := by group
    rw [this, h1]; group
  have hQsup : Qf x e₂ e₃ ≤ L ⊔ L₂ ⊔ L₃ := by
    rw [← hQq]
    exact Tri.Q_le_of_mem tri (mem_sup_left (mem_sup_left hq₁L)) (mem_sup_left (mem_sup_right hq₂L))
      (mem_sup_right hq₃L)
  have hwL : ρ * (e₂ * e₃) * ρ⁻¹ ∈ L ∨ ρ * (e₂ * e₃) * ρ⁻¹ ∈ L₂ ∨
      ρ * (e₂ * e₃) * ρ⁻¹ ∈ L₃ := by
    have key : ∀ M₁ : Subgroup X, IsComponentOf M₁ ⊤ → e₂ * e₃ ∈ M₁ →
        ρ * (e₂ * e₃) * ρ⁻¹ ∈ L ∨ ρ * (e₂ * e₃) * ρ⁻¹ ∈ L₂ ∨ ρ * (e₂ * e₃) * ρ⁻¹ ∈ L₃ := by
      intro M₁ hM₁ hM₁m
      set M' : Subgroup X := M₁.map (MulAut.conj ρ).toMonoidHom with hM'def
      have hM' : IsComponentOf M' ⊤ := isComponent_map_conj hM₁ ρ
      have hwM' : ρ * (e₂ * e₃) * ρ⁻¹ ∈ M' := ⟨e₂ * e₃, hM₁m, rfl⟩
      by_cases e1 : M' = L
      · exact Or.inl (e1 ▸ hwM')
      by_cases e2 : M' = L₂
      · exact Or.inr (Or.inl (e2 ▸ hwM'))
      by_cases e3 : M' = L₃
      · exact Or.inr (Or.inr (e3 ▸ hwM'))
      exfalso
      have hsupC : L ⊔ L₂ ⊔ L₃ ≤ centralizer (M' : Set X) :=
        sup_le (sup_le (le_centralizer_of_ne hL hM' (Ne.symm e1))
          (le_centralizer_of_ne hL₂ hM' (Ne.symm e2))) (le_centralizer_of_ne hL₃ hM' (Ne.symm e3))
      have hbot := inf_eq_bot_of_le_centralizer hfree hM' hsupC
      have : ρ * (e₂ * e₃) * ρ⁻¹ ∈ (L ⊔ L₂ ⊔ L₃) ⊓ M' := mem_inf.mpr ⟨hQsup hwQ, hwM'⟩
      rw [hbot, mem_bot] at this
      exact hw1 this
    rcases hmem23 with h | h | h
    · exact key L hL h
    · exact key L₂ hL₂ h
    · exact key L₃ hL₃ h
  rcases hf.s_cases with hs | hs
  · have hwv : ρ * (e₂ * e₃) * ρ⁻¹ = qel q₁ q₂ q₃ ((b, c, a) + -(c, a, b)) := by
      rw [hw, hs, zpow_one, zpow_neg_one, Tri.qel_add tri, Tri.qel_neg tri, he₂v, he₃v]
    obtain ⟨n1, n2, n3⟩ := vec_diff_pos a b c hnc
    rw [hwv] at hwL
    rcases hwL with h | h | h
    · exact n1 ((hcoord _).1 h)
    · exact n2 ((hcoord _).2.1 h)
    · exact n3 ((hcoord _).2.2 h)
  · have hwv : ρ * (e₂ * e₃) * ρ⁻¹ = qel q₁ q₂ q₃ (-(b, c, a) + (c, a, b)) := by
      rw [hw, hs, zpow_neg_one, neg_neg, zpow_one, Tri.qel_add tri, Tri.qel_neg tri, he₂v, he₃v]
    obtain ⟨n1, n2, n3⟩ := vec_diff_neg a b c hnc
    rw [hwv] at hwL
    rcases hwL with h | h | h
    · exact n1 ((hcoord _).1 h)
    · exact n2 ((hcoord _).2.1 h)
    · exact n3 ((hcoord _).2.2 h)

end XData

end CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Layer
