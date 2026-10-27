module

public import CFSG.HardMathSupport.Cooperstein.StructureLie.OutTwoRank
import CFSG.HardMathSupport.Cooperstein.Coordinator.StarAux

public section

namespace CFSG.HardMathSupport.Cooperstein.StructureLie

open scoped commutatorElement

section Action

variable {K : Type} [Group K] (H L : Subgroup K)

private def conjAutL (hn : H ≤ Subgroup.normalizer (L : Set K)) (h : H) : L ≃* L where
  toFun x := ⟨h * x * h⁻¹, (Subgroup.mem_normalizer_iff.mp (hn h.2) x).mp x.2⟩
  invFun x := ⟨h⁻¹ * x * h, (Subgroup.mem_normalizer_iff.mp (hn h.2) (h⁻¹ * x * h)).mpr
    (by simp [mul_assoc])⟩
  left_inv x := by ext; simp [mul_assoc]
  right_inv x := by ext; simp [mul_assoc]
  map_mul' x y := by ext; simp [mul_assoc]

private def centerQuotAut (hn : H ≤ Subgroup.normalizer (L : Set K)) (h : H) :
    MulAut (L ⧸ Subgroup.center L) :=
  QuotientGroup.congr (Subgroup.center L) (Subgroup.center L) (conjAutL H L hn h)
    (Subgroup.map_center_eq (conjAutL H L hn h))

private theorem centerQuotAut_mk (hn : H ≤ Subgroup.normalizer (L : Set K)) (h : H) (x : L) :
    centerQuotAut H L hn h (x : L ⧸ Subgroup.center L) =
      ((⟨h * x * h⁻¹, (Subgroup.mem_normalizer_iff.mp (hn h.2) x).mp x.2⟩ : L) :
        L ⧸ Subgroup.center L) :=
  QuotientGroup.congr_mk _ _ _ _ x

private def centerQuotHom (hn : H ≤ Subgroup.normalizer (L : Set K)) :
    H →* MulAut (L ⧸ Subgroup.center L) where
  toFun := centerQuotAut H L hn
  map_one' := by
    ext q
    induction q using QuotientGroup.induction_on with
    | H x => simp [centerQuotAut_mk]
  map_mul' a b := by
    ext q
    induction q using QuotientGroup.induction_on with
    | H x =>
      simp only [MulAut.mul_apply, centerQuotAut_mk]
      congr 1
      ext
      simp [mul_assoc]

private theorem centerQuotHom_mk (hn : H ≤ Subgroup.normalizer (L : Set K)) (h : H) (x : L) :
    centerQuotHom H L hn h (x : L ⧸ Subgroup.center L) =
      ((⟨h * x * h⁻¹, (Subgroup.mem_normalizer_iff.mp (hn h.2) x).mp x.2⟩ : L) :
        L ⧸ Subgroup.center L) :=
  centerQuotAut_mk H L hn h x

private theorem centerQuotHom_of_mem (hn : H ≤ Subgroup.normalizer (L : Set K)) (hLH : L ≤ H)
    (l : L) : centerQuotHom H L hn ⟨l, hLH l.2⟩ = MulAut.conj (l : L ⧸ Subgroup.center L) := by
  ext q
  induction q using QuotientGroup.induction_on with
  | H x =>
    rw [centerQuotHom_mk]
    simp only [MulAut.conj_apply]
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    rfl

private theorem ker_le_of_centerQuot (hLL : ⁅L, L⁆ = L)
    (hn : H ≤ Subgroup.normalizer (L : Set K))
    (hcent : H ⊓ Subgroup.centralizer (L : Set K) ≤ L) (g : H)
    (hg : centerQuotHom H L hn g = 1) : (g : K) ∈ L := by
  set W : Subgroup K := (centerQuotHom H L hn).ker.map H.subtype with hW
  set T : Subgroup K := (Subgroup.center L).map L.subtype with hT
  have hWT : ⁅W, L⁆ ≤ T := by
    rw [Subgroup.commutator_le]
    rintro _ ⟨w, hw, rfl⟩ x hx
    have h1 : centerQuotHom H L hn w ((⟨x, hx⟩ : L) : L ⧸ Subgroup.center L) =
        ((⟨x, hx⟩ : L) : L ⧸ Subgroup.center L) := by
      rw [MonoidHom.mem_ker.mp hw]; rfl
    rw [centerQuotHom_mk, QuotientGroup.eq] at h1
    refine ⟨_, Subgroup.inv_mem _ h1, ?_⟩
    have hc := congrArg Subtype.val (Subgroup.mem_center_iff.mp h1 ⟨x, hx⟩)
    have key : ∀ y : K, x * (y⁻¹ * x) = y⁻¹ * x * x → x⁻¹ * y = y * x⁻¹ := by
      intro y hy
      have h : x * y⁻¹ = y⁻¹ * x := mul_right_cancel (by simpa [mul_assoc] using hy)
      have h' := congrArg (fun t => t⁻¹) h
      simpa using h'.symm
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hc ⊢
    rw [commutatorElement_def]
    simpa using key _ hc
  have hTC : T ≤ Subgroup.centralizer (L : Set K) := by
    rintro _ ⟨z, hz, rfl⟩ y hy
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨y, hy⟩)
  have hbot : ⁅⁅W, L⁆, L⁆ = ⊥ := by
    refine le_bot_iff.mp ?_
    calc ⁅⁅W, L⁆, L⁆ ≤ ⁅T, L⁆ := Subgroup.commutator_mono hWT le_rfl
      _ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hTC
  have hle := CFSG.HardMathSupport.Cooperstein.Coordinator.StarAux.le_centralizer_of_commutator_commutator_eq_bot
    hLL hbot
  exact hcent ⟨g.2, hle ⟨g, hg, rfl⟩⟩

end Action

theorem out_bound {K : Type} [Group K] (H L S : Subgroup K)
    (hLL : ⁅L, L⁆ = L) (hLH : L ≤ H) (hnorm : H ≤ Subgroup.normalizer (L : Set K))
    (hcent : H ⊓ Subgroup.centralizer (L : Set K) ≤ L)
    (hSH : S ≤ H) (hS2 : IsPGroup 2 S) (hSL : S ⊓ L = ⊥)
    (hout : OutTwoRank (↥L ⧸ Subgroup.center ↥L)) :
    (∀ a ∈ S, ∀ b ∈ S, a * b = b * a) ∧
    ∀ E : Subgroup K, E ≤ S → (∀ a ∈ E, a ^ 2 = 1) → Nat.card E ≤ 4 := by
  set c : H →* MulAut (L ⧸ Subgroup.center L) := centerQuotHom H L hnorm with hc
  set c' : S →* MulAut (L ⧸ Subgroup.center L) := c.comp (Subgroup.inclusion hSH) with hc'
  have KER : ∀ h : H, c h ∈ InnAut (L ⧸ Subgroup.center L) → (h : K) ∈ L := by
    rintro h ⟨y, hy⟩
    induction y using QuotientGroup.induction_on with
    | H l =>
      have hl : c ⟨l, hLH l.2⟩ = MulAut.conj (l : L ⧸ Subgroup.center L) :=
        centerQuotHom_of_mem H L hnorm hLH l
      have h1 : c (h * ⟨l, hLH l.2⟩⁻¹) = 1 := by
        rw [map_mul, map_inv, hl, ← hy]
        exact mul_inv_cancel _
      have h2 := ker_le_of_centerQuot H L hLL hnorm hcent _ h1
      have h3 : (h : K) = (h : K) * (l : K)⁻¹ * l := by group
      rw [h3]
      exact L.mul_mem (by simpa using h2) l.2
  have KER' : ∀ s : S, c' s ∈ InnAut (L ⧸ Subgroup.center L) → (s : K) = 1 := by
    intro s hs
    have h1 : (s : K) ∈ S ⊓ L := ⟨s.2, KER _ hs⟩
    rw [hSL] at h1
    exact h1
  have hinj : Function.Injective c' := by
    rw [injective_iff_map_eq_one]
    intro s hs
    exact Subtype.ext (KER' s (by rw [hs]; exact Subgroup.one_mem _))
  have hP : IsPGroup 2 c'.range := hS2.of_surjective c'.rangeRestrict c'.rangeRestrict_surjective
  obtain ⟨hcomm, hrank⟩ := hout c'.range hP
  refine ⟨fun a ha b hb => ?_, fun E hES hE2 => ?_⟩
  · have h1 : c' ⁅(⟨a, ha⟩ : S), ⟨b, hb⟩⁆ ∈ InnAut (L ⧸ Subgroup.center L) := by
      rw [map_commutatorElement]
      exact hcomm _ ⟨_, rfl⟩ _ ⟨_, rfl⟩
    have h2 := KER' _ h1
    exact commutatorElement_eq_one_iff_mul_comm.mp (show ⁅a, b⁆ = 1 from h2)
  · set E' : Subgroup (MulAut (L ⧸ Subgroup.center L)) := (E.subgroupOf S).map c' with hE'
    have hEP : E' ≤ c'.range := by
      rintro _ ⟨x, -, rfl⟩
      exact ⟨x, rfl⟩
    have hsq : ∀ a ∈ E', a ^ 2 ∈ InnAut (L ⧸ Subgroup.center L) := by
      rintro _ ⟨x, hx, rfl⟩
      have hx2 : x ^ 2 = 1 := Subtype.ext (hE2 _ hx)
      rw [← map_pow, hx2, map_one]
      exact Subgroup.one_mem _
    have hbot : E' ⊓ InnAut (L ⧸ Subgroup.center L) = ⊥ := by
      refine eq_bot_iff.mpr ?_
      rintro _ ⟨⟨x, -, rfl⟩, hin⟩
      have : x = 1 := Subtype.ext (KER' x hin)
      rw [this, map_one]
      exact Subgroup.one_mem _
    have h1 := hrank E' hEP hsq
    rw [hbot, Subgroup.relIndex_bot_left, hE', Subgroup.card_map_of_injective hinj] at h1
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hES).toEquiv]
    exact h1

end CFSG.HardMathSupport.Cooperstein.StructureLie
