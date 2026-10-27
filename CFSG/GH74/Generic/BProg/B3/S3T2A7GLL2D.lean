module

public import CFSG.GH74.Generic.BProg.B3.S3T2A7GLL2B
public import CFSG.GH74.Generic.BProg.B3.S3T2A7GLL2C

public section

namespace CFSG.GH74.Generic.BProg.B3.S3T2A7.GLR

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup

variable {Y : Type} [Group Y] [Finite Y] {L B X₀ : Subgroup Y} {z : Y}

omit [Finite Y] in
theorem exists_mul_of_mem (hs : Setting125 Y L B X₀ z) {D : Subgroup Y} (hDB : D ≤ B)
    (hDsup : D ⊔ zpowers z = B) {b : Y} (hb : b ∈ B) :
    ∃ d ∈ D, ∃ w ∈ zpowers z, b = d * w := by
  have hN : zpowers z ≤ normalizer (D : Set Y) :=
    le_normalizer_of_forall_comm fun g hg x hx =>
      ((C3.Layer1.Back.forall_of_isElementaryAbelian hs.B_el).1 g
        (zpowers_le.mpr hs.z_mem hg) x (hDB hx))
  have hb' : b ∈ ((D ⊔ zpowers z : Subgroup Y) : Set Y) := hDsup ▸ hb
  rw [Subgroup.coe_mul_of_right_le_normalizer_left D (zpowers z) hN] at hb'
  obtain ⟨d, hd, w, hw, rfl⟩ := Set.mem_mul.mp hb'
  exact ⟨d, hd, w, hw, rfl⟩

omit [Finite Y] in
@[expose] def goodSub (L X₀ : Subgroup Y) : Subgroup ↥L where
  carrier := {c | ∃ x ∈ normalizer (pPrimeCoreOf 2 X₀ : Set Y), x ∈ normalizer (L : Set Y) ∧
    ∀ y ∈ L, x * y * x⁻¹ = c * y * (c : Y)⁻¹}
  one_mem' := ⟨1, one_mem _, one_mem _, fun y _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨u, huW, huN, hu⟩ ⟨v, hvW, hvN, hv⟩
    refine ⟨u * v, mul_mem huW hvW, mul_mem huN hvN, fun y hy => ?_⟩
    calc u * v * y * (u * v)⁻¹ = u * (v * y * v⁻¹) * u⁻¹ := by group
      _ = u * ((b : Y) * y * (b : Y)⁻¹) * u⁻¹ := by rw [hv y hy]
      _ = (a : Y) * ((b : Y) * y * (b : Y)⁻¹) * (a : Y)⁻¹ :=
          hu _ (mul_mem (mul_mem b.2 hy) (inv_mem b.2))
      _ = ((a * b : ↥L) : Y) * y * ((a * b : ↥L) : Y)⁻¹ := by
          simp only [Subgroup.coe_mul]
          group
  inv_mem' := by
    rintro a ⟨u, huW, huN, hu⟩
    refine ⟨u⁻¹, inv_mem huW, inv_mem huN, fun y hy => ?_⟩
    have h := hu _ (mul_mem (mul_mem (inv_mem a.2) hy) a.2)
    calc u⁻¹ * y * u⁻¹⁻¹ = u⁻¹ * ((a : Y) * ((a : Y)⁻¹ * y * a) * (a : Y)⁻¹) * u := by group
      _ = u⁻¹ * (u * ((a : Y)⁻¹ * y * a) * u⁻¹) * u := by rw [h]
      _ = ((a⁻¹ : ↥L) : Y) * y * ((a⁻¹ : ↥L) : Y)⁻¹ := by
          simp only [Subgroup.coe_inv]
          group

omit [Finite Y] in
theorem exists_ne_one_of_one_le_pRank {G : Type} [Group G] [Finite G] (h : 1 ≤ pRank 2 G) :
    ∃ g : G, g ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have : Subsingleton G := ⟨fun a b => (hcon a).trans (hcon b).symm⟩
  have : CFSG.IsElementaryAbelian 2 G :=
    { toIsMulCommutative := ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun g => Subsingleton.elim _ _ }
  have h0 : pRank 2 G = 0 := CFSG.pRank_eq_of_card_eq_pow one_lt_two (by rw [Nat.card_unique]; rfl)
  omega

theorem false_of_orbit_two (hs : Setting125 Y L B X₀ z)
    (hsig : Sig125 L X₀) (hcut : Cut125 L B) {D : Subgroup Y} (hDB : D ≤ B)
    (hDz : D ⊓ zpowers z = ⊥) (hDsup : D ⊔ zpowers z = B) {s : Y} (hsD : s ∈ D)
    (hsN : s ∉ normalizer (L : Set Y))
    (horb : ∀ t ∈ D, t ∉ normalizer (L : Set Y) → s * t ∈ normalizer (L : Set Y))
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hT : LieModel (↥L ⧸ center ↥L) .PSL 2 p f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = p ^ f)
    (ψ : ↥L ≃* Matrix.SpecialLinearGroup (Fin 2) K) : False := by
  classical
  obtain ⟨hBc, hBsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hs.B_el
  obtain ⟨hDr, -⟩ := compl_facts hs hDB hDz hDsup
  have hDel : CFSG.IsElementaryAbelian 2 ↥D := Th2Sig6.isElementaryAbelian_of_le hs.B_el hDB
  have hDcard : Nat.card ↥D = 8 := by
    rw [C3.Layer1.Back.card_eq_two_pow_pRank hDel, hDr]
    norm_num
  set D₀ : Subgroup Y := D ⊓ normalizer (L : Set Y) with hD₀
  have hD₀el : CFSG.IsElementaryAbelian 2 ↥D₀ :=
    Th2Sig6.isElementaryAbelian_of_le hs.B_el (inf_le_left.trans hDB)
  have hD₀card : Nat.card ↥D₀ = 4 := by
    have hge : 8 ≤ 2 * Nat.card ↥D₀ := by
      let j : ↥D → ↥D₀ ⊕ ↥D₀ := fun d =>
        if hd : (d : Y) ∈ normalizer (L : Set Y) then Sum.inl ⟨d, d.2, hd⟩
        else Sum.inr ⟨s * d, mul_mem hsD d.2, horb d d.2 hd⟩
      have hj : Function.Injective j := by
        intro x y hxy
        by_cases hx : (x : Y) ∈ normalizer (L : Set Y) <;>
          by_cases hy : (y : Y) ∈ normalizer (L : Set Y)
        · simp only [j, hx, hy, ↓reduceDIte, Sum.inl.injEq] at hxy
          exact Subtype.ext (congrArg (fun w : ↥D₀ => (w : Y)) hxy)
        · simp [j, hx, hy] at hxy
        · simp [j, hx, hy] at hxy
        · simp only [j, hx, hy, ↓reduceDIte, Sum.inr.injEq] at hxy
          exact Subtype.ext (mul_left_cancel (congrArg (fun w : ↥D₀ => (w : Y)) hxy))
      have h1 := Nat.card_le_card_of_injective j hj
      rw [Nat.card_sum, hDcard] at h1
      omega
    have hdvd : Nat.card ↥D₀ ∣ 8 := hDcard ▸ Subgroup.card_dvd_of_le inf_le_left
    have hne : Nat.card ↥D₀ ≠ 8 := by
      intro h8
      have h1 := Subgroup.eq_of_le_of_card_ge (inf_le_left : D₀ ≤ D) (by rw [hDcard, h8])
      have h2 : s ∈ D ⊓ normalizer (L : Set Y) := by rw [h1]; exact hsD
      exact hsN h2.2
    have hle : Nat.card ↥D₀ ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
    set n := Nat.card ↥D₀ with hn
    obtain ⟨k, hk⟩ := hdvd
    interval_cases n <;> omega
  let α : ↥D₀ →* MulAut (Matrix.SpecialLinearGroup (Fin 2) K) :=
    (B2.actOn L ψ).comp (Subgroup.inclusion (inf_le_right : D₀ ≤ normalizer (L : Set Y)))
  have hα : ∀ (d : ↥D₀) (y : Matrix.SpecialLinearGroup (Fin 2) K),
      ((ψ.symm (α d y) : ↥L) : Y) = (d : Y) * (ψ.symm y : Y) * (d : Y)⁻¹ :=
    fun d y => B2.coe_symm_actOn L ψ _ y
  obtain ⟨-, -, -, hq3, -⟩ := CFSG.ComponentClassification.AutL2Facts.lieModel_psl2_data hT
  have h5 : 5 ≤ p ^ f := by
    have hf1 : 1 ≤ f := by
      rcases Nat.eq_zero_or_pos f with h0 | h0
      · exfalso
        obtain ⟨-, h1, -⟩ := CFSG.ComponentClassification.AutL2Facts.lieModel_psl2_data hT
        omega
      · exact h0
    have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    have h3 : 3 ≤ p ^ f := hp3.trans (Nat.le_self_pow (by omega) p)
    obtain ⟨m, hm⟩ := hodd
    omega
  have hC1 : ∀ {b : Y}, b ∉ normalizer (L : Set Y) → ∀ x ∈ L, ∀ y ∈ L,
      Commute x (b * y * b⁻¹) := fun hb x hx y hy => by
    have h := comm_conj hs.comp (a := 1) (by simpa using hb) hx hy
    simp only [one_mul, inv_one, mul_one] at h
    exact h
  rcases B2.GenLocL2SL.gammaAct_sl2_core hp hp2 hK h5 hD₀el hD₀card α with htop | ⟨hq, hinn⟩
  ·
    have hD₀r : pRank 2 ↥D₀ = 2 :=
      CFSG.pRank_eq_of_card_eq_pow one_lt_two (by rw [hD₀card]; norm_num)
    have hgood : ∀ e : ↥D₀, e ≠ 1 → ∀ c ∈ L, (e : Y) * c * (e : Y)⁻¹ = c →
        ∃ x ∈ normalizer (pPrimeCoreOf 2 X₀ : Set Y), x ∈ normalizer (L : Set Y) ∧
          ∀ y ∈ L, x * y * x⁻¹ = c * y * c⁻¹ := by
      intro e he1 c hc hec
      have heD : (e : Y) ∈ D := e.2.1
      have heN : (e : Y) ∈ normalizer (L : Set Y) := e.2.2
      have he1' : (e : Y) ≠ 1 := fun h => he1 (Subtype.ext h)
      have hs1 : s ≠ 1 := fun h => hsN (h ▸ one_mem _)
      have hes : (e : Y) ≠ s := fun h => hsN (h ▸ heN)
      obtain ⟨hED, hE2⟩ := two_le_pRank_sup hs hDB heD hsD he1' hs1 hes
      have hNW := centralizer_le_normalizer_W hs hDB hDz hDsup hED hE2
      have hs2 : s * s = 1 := hBsq s (hDB hsD)
      have hes' : (e : Y) * s = s * e := hBc _ (hDB heD) _ (hDB hsD)
      set b₀ := s * c * s⁻¹ with hb₀
      have hcb := hC1 hsN c hc c hc
      have hact : ∀ y ∈ L, c * b₀ * y * (c * b₀)⁻¹ = c * y * c⁻¹ := by
        intro y hy
        have h1 := hC1 hsN y hy c hc
        calc c * b₀ * y * (c * b₀)⁻¹ = c * (b₀ * y * b₀⁻¹) * c⁻¹ := by group
          _ = c * (y * b₀ * b₀⁻¹) * c⁻¹ := by rw [← h1.eq]
          _ = c * y * c⁻¹ := by group
      have hxs : s * (c * b₀) * s⁻¹ = c * b₀ := by
        have h1 : s * b₀ * s⁻¹ = c := by
          rw [hb₀]
          calc s * (s * c * s⁻¹) * s⁻¹ = (s * s) * c * (s * s)⁻¹ := by group
            _ = c := by rw [hs2]; group
        calc s * (c * b₀) * s⁻¹ = (s * c * s⁻¹) * (s * b₀ * s⁻¹) := by group
          _ = b₀ * c := by rw [h1]
          _ = c * b₀ := hcb.eq.symm
      have hxe : (e : Y) * (c * b₀) * (e : Y)⁻¹ = c * b₀ := by
        have h1 : (e : Y) * b₀ * (e : Y)⁻¹ = b₀ := by
          rw [hb₀]
          calc (e : Y) * (s * c * s⁻¹) * (e : Y)⁻¹ = ((e : Y) * s) * c * ((e : Y) * s)⁻¹ := by
                group
            _ = (s * e) * c * (s * e)⁻¹ := by rw [hes']
            _ = s * ((e : Y) * c * (e : Y)⁻¹) * s⁻¹ := by group
            _ = s * c * s⁻¹ := by rw [hec]
        calc (e : Y) * (c * b₀) * (e : Y)⁻¹ =
              ((e : Y) * c * (e : Y)⁻¹) * ((e : Y) * b₀ * (e : Y)⁻¹) := by group
          _ = c * b₀ := by rw [hec, h1]
      have hcomm : ∀ g : Y, g * (c * b₀) * g⁻¹ = c * b₀ →
          g ∈ centralizer ({c * b₀} : Set Y) := fun g hg =>
        mem_centralizer_singleton_iff.mpr (by
          calc g * (c * b₀) = (g * (c * b₀) * g⁻¹) * g := by group
            _ = c * b₀ * g := by rw [hg])
      have hle : zpowers (e : Y) ⊔ zpowers s ≤ centralizer ({c * b₀} : Set Y) :=
        sup_le (zpowers_le.mpr (hcomm _ hxe)) (zpowers_le.mpr (hcomm s hxs))
      have hxE : c * b₀ ∈ centralizer ((zpowers (e : Y) ⊔ zpowers s : Subgroup Y) : Set Y) :=
        Subgroup.mem_centralizer_iff.mpr fun g hg => mem_centralizer_singleton_iff.mp (hle hg)
      exact ⟨c * b₀, hNW hxE, mem_normalizer_of_act hc hact, hact⟩
    have hle : B2.gammaAct α ≤ (goodSub L X₀).map ψ.toMonoidHom := by
      refine iSup₂_le fun E hE => ?_
      intro g hg
      rw [hD₀r] at hE
      obtain ⟨e, he1⟩ := exists_ne_one_of_one_le_pRank (G := ↥E) (by omega)
      have he1' : (e : ↥D₀) ≠ 1 := fun h => he1 (Subtype.ext h)
      have hfix : α e g = g := (B2.mem_fixedIn.mp hg) (α e) ⟨e, e.2, rfl⟩
      have hec : ((e : ↥D₀) : Y) * ((ψ.symm g : ↥L) : Y) * ((e : ↥D₀) : Y)⁻¹ =
          ((ψ.symm g : ↥L) : Y) := by rw [← hα e g, hfix]
      obtain ⟨x, hxW, hxN, hx⟩ := hgood e he1' _ (ψ.symm g).2 hec
      exact ⟨ψ.symm g, ⟨x, hxW, hxN, hx⟩, by simp⟩
    refine false_of_sig_of_inner hs hsig fun c hc => ?_
    obtain ⟨c', hc', hcc'⟩ := hle (htop ▸ Subgroup.mem_top (ψ ⟨c, hc⟩))
    have h1 : c' = ⟨c, hc⟩ := ψ.injective hcc'
    rw [h1] at hc'
    exact hc'
  ·
    obtain ⟨f₀, hf₀B, hf₀N, hf₀C, n, hn, hnN, hnC⟩ := hcut
    obtain ⟨d, hdD, w, hw, rfl⟩ := exists_mul_of_mem hs hDB hDsup hf₀B
    have hwc : ∀ g : Y, g * w = w * g := fun g =>
      Subgroup.mem_center_iff.mp ((zpowers_le.mpr hs.z_cent) hw) g
    have hwN : w ∈ normalizer (L : Set Y) := mem_normalizer_iff.mpr fun h => by
      rw [← hwc h, mul_inv_cancel_right]
    have hdN : d ∈ normalizer (L : Set Y) := by
      have h1 : d = d * w * w⁻¹ := by group
      rw [h1]
      exact mul_mem hf₀N (inv_mem hwN)
    have hdD₀ : d ∈ D₀ := Subgroup.mem_inf.mpr ⟨hdD, hdN⟩
    obtain ⟨ŝ, hŝ⟩ := hinn ⟨⟨d, hdD₀⟩, rfl⟩
    have hact : ∀ x ∈ L, d * w * x * (d * w)⁻¹ =
        ((ψ.symm ŝ : ↥L) : Y) * x * ((ψ.symm ŝ : ↥L) : Y)⁻¹ := by
      intro x hx
      have h1 := hα ⟨d, hdD₀⟩ (ψ ⟨x, hx⟩)
      rw [← hŝ, MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply] at h1
      calc d * w * x * (d * w)⁻¹ = d * x * d⁻¹ := by
            rw [mul_assoc d w x, ← hwc x]
            group
        _ = ((ψ.symm ŝ : ↥L) : Y) * x * ((ψ.symm ŝ : ↥L) : Y)⁻¹ := by
            rw [← h1]
            simp
    exact hnC (mem_centralizer_of_inner_small hp hp2 hq hs.comp hT hf₀N (hBsq _ hf₀B)
      (ψ.symm ŝ).2 hact hf₀C hn hnN)

end CFSG.GH74.Generic.BProg.B3.S3T2A7.GLR
