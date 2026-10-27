module

public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2G3Defs
public import CFSG.ClassicalInvolution.Q3.TL4E3S3ODefs

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform

section TwinQuot

variable {W : Type} [Group W] {Φ : Set (Subgroup W)} {K K' : Subgroup W} {k k' : W}

theorem eq_one_or_eq_of_mem_zpowers_of_mul_self {c x : W} (hc : c * c = 1)
    (hx : x ∈ Subgroup.zpowers c) : x = 1 ∨ x = c := by
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h2 : c ^ (2 : ℤ) = 1 := by rw [zpow_two, hc]
  obtain ⟨q, rfl | rfl⟩ := Int.even_or_odd' j
  · left
    rw [zpow_mul, h2, one_zpow]
  · right
    rw [zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

theorem TwinBase3.commute_involutions (hT : TwinBase3 Φ K K' k k') : k' * k = k * k' := by
  have h1 : k * (k * k') = (k * k') * k := Subgroup.mem_center_iff.mp hT.center k
  calc k' * k = k⁻¹ * ((k * k') * k) := by group
    _ = k⁻¹ * (k * (k * k')) := by rw [h1]
    _ = k * k' := by group

theorem TwinBase3.mul_mul_self (hT : TwinBase3 Φ K K' k k') : k * k' * (k * k') = 1 := by
  calc k * k' * (k * k') = k * (k' * k) * k' := by group
    _ = k * (k * k') * k' := by rw [hT.commute_involutions]
    _ = (k * k) * (k' * k') := by group
    _ = 1 := by rw [hT.invK.sq, hT.invK'.sq, one_mul]

theorem TwinBase3.mul_ne_one (hT : TwinBase3 Φ K K' k k') : k * k' ≠ 1 := by
  intro h1
  apply hT.ne
  calc k = k * (k * k') := by rw [h1, mul_one]
    _ = (k * k) * k' := by group
    _ = k' := by rw [hT.invK.sq, one_mul]

theorem TwinBase3.eq_one_of_mem_zpowers (hT : TwinBase3 Φ K K' k k') {x : W} (hx : x ∈ K)
    (hxN : x ∈ Subgroup.zpowers (k * k')) : x = 1 := by
  rcases eq_one_or_eq_of_mem_zpowers_of_mul_self hT.mul_mul_self hxN with h | rfl
  · exact h
  · exfalso
    rcases hT.invK.unique _ hx hT.mul_mul_self with h1 | h1
    · exact hT.mul_ne_one h1
    · apply hT.invK'.ne_one
      calc k' = k * (k * k') := by rw [← mul_assoc, hT.invK.sq, one_mul]
        _ = 1 := by rw [h1, hT.invK.sq]

theorem TwinBase3.eq_one_of_mem_conjSub (hT : TwinBase3 Φ K K' k k') {N : Subgroup W}
    [hNn : N.Normal] (hN : N = Subgroup.zpowers (k * k')) {w z : W} (hz : z ∈ conjSub w K)
    (hzN : z ∈ N) : z = 1 := by
  have h1 : w⁻¹ * z * w ∈ K := mem_conjSub_iff.mp hz
  have h2 : w⁻¹ * z * w ∈ N := by
    have := hNn.conj_mem z hzN w⁻¹
    rwa [inv_inv] at this
  rw [hN] at h2
  have h3 := hT.eq_one_of_mem_zpowers h1 h2
  calc z = w * (w⁻¹ * z * w) * w⁻¹ := by group
    _ = 1 := by rw [h3]; group

theorem TwinBase3.commute_of_mk (hT : TwinBase3 Φ K K' k k') {N : Subgroup W} [N.Normal]
    (hN : N = Subgroup.zpowers (k * k')) {w x y : W} (hx : x ∈ conjSub w K)
    (hy : y ∈ conjSub w K)
    (h : QuotientGroup.mk' N x * QuotientGroup.mk' N y =
      QuotientGroup.mk' N y * QuotientGroup.mk' N x) :
    x * y = y * x := by
  have hmem : (y * x)⁻¹ * (x * y) ∈ conjSub w K :=
    (conjSub w K).mul_mem ((conjSub w K).inv_mem ((conjSub w K).mul_mem hy hx))
      ((conjSub w K).mul_mem hx hy)
  have hker : (y * x)⁻¹ * (x * y) ∈ N := by
    rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, h,
      inv_mul_cancel]
  have h1 := hT.eq_one_of_mem_conjSub hN hmem hker
  calc x * y = (y * x) * ((y * x)⁻¹ * (x * y)) := by group
    _ = y * x := by rw [h1, mul_one]

theorem TwinBase3.exists_ne_comm (hT : TwinBase3 Φ K K' k k') :
    ∃ x ∈ K, ∃ y ∈ K, x * y ≠ y * x := by
  obtain ⟨-, P, hP, hnc⟩ := hT.fam.hyp.omega1 K hT.memK
  by_contra hc
  apply hnc
  refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
  by_contra hab
  exact hc ⟨a, hP.1 a.2, b, hP.1 b.2, hab⟩

theorem TwinBase3.exists_ne_comm_quot (hT : TwinBase3 Φ K K' k k') {N : Subgroup W} [N.Normal]
    (hN : N = Subgroup.zpowers (k * k')) : ∃ a b : W ⧸ N, a * b ≠ b * a := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hT.exists_ne_comm
  refine ⟨QuotientGroup.mk' N x, QuotientGroup.mk' N y, fun h => hxy ?_⟩
  have hx' : x ∈ conjSub 1 K := by rw [conjSub_one]; exact hx
  have hy' : y ∈ conjSub 1 K := by rw [conjSub_one]; exact hy
  exact hT.commute_of_mk hN hx' hy' h

theorem TwinBase3.omegaGen_conjClass_eq_top (hT : TwinBase3 Φ K K' k k') {N : Subgroup W}
    [N.Normal] {M₀ : Subgroup (W ⧸ N)} (hle : K.map (QuotientGroup.mk' N) ≤ M₀) :
    omegaGen (CoreAssembly.conjClass M₀) = ⊤ := by
  refine eq_top_iff.mpr ?_
  calc (⊤ : Subgroup (W ⧸ N)) = (⨆ g : W, conjSub g K).map (QuotientGroup.mk' N) := by
        rw [hT.gen, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]
    _ = ⨆ g : W, (conjSub g K).map (QuotientGroup.mk' N) := Subgroup.map_iSup _ _
    _ ≤ omegaGen (CoreAssembly.conjClass M₀) := by
        refine iSup_le fun g => ?_
        rw [← conjSub_map]
        exact (Subgroup.map_mono hle).trans
          (le_omegaGen (Ω := CoreAssembly.conjClass M₀) ⟨QuotientGroup.mk' N g, rfl⟩)

end TwinQuot

end CFSG.ClassicalInvolution.Q3.TL4

namespace CFSG.ClassicalInvolution.Q3.TL4.Z2W

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform

section Cit3


theorem orthThreeCommuting_of_isOrthTag (h : OrthThreeCommutingFacts) {d : ℕ} {ε : Bool}
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {m : ℕ} (hOrth : IsOrthTag d ε t m)
    (hd : 9 ≤ d ∨ (d = 8 ∧ ε = true)) : OrthThreeCommuting t m := by
  rcases hOrth with ⟨rfl, -, -⟩ | ⟨rfl, -, -, -⟩ | ⟨rfl, -, -, -⟩ | ⟨-, hodd, rfl, hm⟩ |
      ⟨h8, -, -, rfl, hm⟩ | ⟨-, -, hε, rfl, hm⟩
  · rcases hd with hd | ⟨hd, -⟩ <;> omega
  · rcases hd with hd | ⟨hd, -⟩ <;> omega
  · rcases hd with hd | ⟨hd, -⟩ <;> omega
  · exact h.1 m (by rcases hd with hd | ⟨hd, -⟩ <;> omega)
  · exact h.2.1 m (by omega)
  · refine h.2.2 m ?_
    rcases hd with hd | ⟨-, hεt⟩
    · omega
    · exact absurd (hε.symm.trans hεt) Bool.false_ne_true

theorem gapOmegaLargeF_of (h : OrthThreeCommutingFacts) :
    ∀ (W : Type) [Group W] [Finite W] (Φ : Set (Subgroup W)) (K K' : Subgroup W) (k k' : W),
      TwinBase3 Φ K K' k k' → ∀ (N : Subgroup W) (_ : N.Normal), N = Subgroup.zpowers (k * k') →
        ∀ (d : ℕ) (ε : Bool), (9 ≤ d ∨ (d = 8 ∧ ε = true)) →
          OrthFundCover (W ⧸ N) (K.map (QuotientGroup.mk' N)) d ε →
            ∃ (P₂ : Subgroup W) (L₁ L₂ L₃ : Subgroup W), IsPGroup 2 ↥P₂ ∧ L₁ ∈ Φ ∧ L₂ ∈ Φ ∧
              L₃ ∈ Φ ∧ L₁ ≠ L₂ ∧ L₁ ≠ L₃ ∧ L₂ ≠ L₃ ∧ 2 < Nat.card ↥(L₁ ⊓ P₂) ∧
                2 < Nat.card ↥(L₂ ⊓ P₂) ∧ 2 < Nat.card ↥(L₃ ⊓ P₂) := by
  intro W _ _ Φ K K' k k' hT N hNn hN d ε hd hcov
  classical
  obtain ⟨M₀, hKM, t, m, hOrth, D, -, i, e, he, -, -, hc⟩ := hcov
  have he1 : e = 1 := by rcases he with h | ⟨-, h⟩ <;> omega
  subst he1
  have hOT : OrthThreeCommuting t m := orthThreeCommuting_of_isOrthTag h hOrth hd
  have hN2 : IsPGroup 2 ↥N := by
    rw [hN]
    exact Balance.isPGroup_zpowers_of_mul_self_eq_one hT.mul_mul_self
  obtain ⟨x₀, hx₀, y₀, hy₀, hxy₀⟩ := hT.exists_ne_comm
  obtain ⟨R, hR, hRΛ⟩ := D.meets i
  obtain ⟨c, hcR⟩ := hRΛ
  have hcR' : conjSub c M₀ = R.map (D.hom i) := hcR
  obtain ⟨R', hR', hR'R⟩ := exists_map_castHom hc (D.hom i) hR
  generalize castHom hc (D.hom i) = ψ at hR'R
  obtain ⟨g, hg⟩ := hOT R' hR'
  have hMa : ∀ a, conjSub (ψ (g a) * c) M₀ = (conjSub (g a) R').map ψ := by
    intro a
    rw [conjSub_mul, hcR', ← hR'R, conjSub_map]
  have hcommM : ∀ a b, a ≠ b → ∀ x ∈ conjSub (ψ (g a) * c) M₀,
      ∀ y ∈ conjSub (ψ (g b) * c) M₀, x * y = y * x := by
    intro a b hab x hx y hy
    rw [hMa] at hx hy
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    rw [← map_mul, ← map_mul, hg a b hab x' hx' y' hy']
  choose w hw using fun a : Fin 3 => QuotientGroup.mk'_surjective N (ψ (g a) * c)
  have hLΦ : ∀ a, conjSub (w a) K ∈ Φ := fun a => hT.fam.hyp.conjInvariant (w a) K hT.memK
  have hLM : ∀ a, (conjSub (w a) K).map (QuotientGroup.mk' N) ≤ conjSub (ψ (g a) * c) M₀ := by
    intro a
    rw [← conjSub_map, hw a]
    exact Subgroup.map_mono hKM
  have hne : ∀ a b, a ≠ b → conjSub (w a) K ≠ conjSub (w b) K := by
    intro a b hab heq
    apply hxy₀
    have hX : w a * x₀ * (w a)⁻¹ ∈ conjSub (w a) K := conj_mem_conjSub hx₀
    have hY : w a * y₀ * (w a)⁻¹ ∈ conjSub (w a) K := conj_mem_conjSub hy₀
    have hY' : w a * y₀ * (w a)⁻¹ ∈ conjSub (w b) K := by rw [← heq]; exact hY
    have hXM : QuotientGroup.mk' N (w a * x₀ * (w a)⁻¹) ∈ conjSub (ψ (g a) * c) M₀ :=
      hLM a ⟨_, hX, rfl⟩
    have hYM : QuotientGroup.mk' N (w a * y₀ * (w a)⁻¹) ∈ conjSub (ψ (g b) * c) M₀ :=
      hLM b ⟨_, hY', rfl⟩
    have h2 := hT.commute_of_mk hN hX hY (hcommM a b hab _ hXM _ hYM)
    have h3 : w a * (x₀ * y₀) * (w a)⁻¹ = w a * (y₀ * x₀) * (w a)⁻¹ := by
      calc w a * (x₀ * y₀) * (w a)⁻¹ = (w a * x₀ * (w a)⁻¹) * (w a * y₀ * (w a)⁻¹) := by group
        _ = (w a * y₀ * (w a)⁻¹) * (w a * x₀ * (w a)⁻¹) := h2
        _ = w a * (y₀ * x₀) * (w a)⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h3)
  obtain ⟨-, Q, hQ, -⟩ := hT.fam.hyp.omega1 K hT.memK
  obtain ⟨eQ⟩ : Nonempty (↥Q ≃* QuaternionGroup 2) := hT.fam.quat K hT.memK Q hQ
  have hQ8 : Nat.card ↥Q = 8 := by
    rw [Nat.card_congr eQ.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hQbar2 : ∀ a, IsPGroup 2 ↥((conjSub (w a) Q).map (QuotientGroup.mk' N)) :=
    fun a => (hQ.2.1.map (MulAut.conj (w a)).toMonoidHom).map _
  have hQbarM : ∀ a, (conjSub (w a) Q).map (QuotientGroup.mk' N) ≤ conjSub (ψ (g a) * c) M₀ :=
    fun a => (Subgroup.map_mono (Subgroup.map_mono hQ.1)).trans (hLM a)
  have hcent : ∀ a b, a ≠ b → (conjSub (w a) Q).map (QuotientGroup.mk' N) ≤
      Subgroup.centralizer (((conjSub (w b) Q).map (QuotientGroup.mk' N) : Subgroup (W ⧸ N)) :
        Set (W ⧸ N)) :=
    fun a b hab x hx => Subgroup.mem_centralizer_iff.mpr fun y hy =>
      (hcommM a b hab x (hQbarM a hx) y (hQbarM b hy)).symm
  have hQ01 : IsPGroup 2 ↥((conjSub (w 0) Q).map (QuotientGroup.mk' N) ⊔
      (conjSub (w 1) Q).map (QuotientGroup.mk' N)) :=
    IsPGroup.to_sup_of_normal_right' (hQbar2 0) (hQbar2 1)
      ((hcent 0 1 (by decide)).trans (Subgroup.centralizer_le_normalizer _))
  have hQall : IsPGroup 2 ↥((conjSub (w 0) Q).map (QuotientGroup.mk' N) ⊔
      (conjSub (w 1) Q).map (QuotientGroup.mk' N) ⊔
      (conjSub (w 2) Q).map (QuotientGroup.mk' N)) :=
    IsPGroup.to_sup_of_normal_right' hQ01 (hQbar2 2)
      ((sup_le (hcent 0 2 (by decide)) (hcent 1 2 (by decide))).trans
        (Subgroup.centralizer_le_normalizer _))
  set P₂ : Subgroup W := ((conjSub (w 0) Q).map (QuotientGroup.mk' N) ⊔
      (conjSub (w 1) Q).map (QuotientGroup.mk' N) ⊔
      (conjSub (w 2) Q).map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) with hP₂def
  have hP₂ : IsPGroup 2 ↥P₂ :=
    hQall.comap_of_ker_isPGroup _ (by rw [QuotientGroup.ker_mk']; exact hN2)
  have hQaP : ∀ a, conjSub (w a) Q ≤ P₂ := by
    intro a x hx
    have hx' : QuotientGroup.mk' N x ∈ (conjSub (w a) Q).map (QuotientGroup.mk' N) := ⟨x, hx, rfl⟩
    show QuotientGroup.mk' N x ∈ (conjSub (w 0) Q).map (QuotientGroup.mk' N) ⊔
      (conjSub (w 1) Q).map (QuotientGroup.mk' N) ⊔ (conjSub (w 2) Q).map (QuotientGroup.mk' N)
    fin_cases a
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left hx')
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right hx')
    · exact Subgroup.mem_sup_right hx'
  have hcard : ∀ a, 2 < Nat.card ↥(conjSub (w a) K ⊓ P₂) := by
    intro a
    have hle : conjSub (w a) Q ≤ conjSub (w a) K ⊓ P₂ :=
      le_inf (Subgroup.map_mono hQ.1) (hQaP a)
    have h8 : Nat.card ↥(conjSub (w a) Q) = 8 := by
      rw [conjSub, Subgroup.card_map_of_injective (MulAut.conj (w a)).injective, hQ8]
    have := Subgroup.card_le_of_le hle
    omega
  exact ⟨P₂, conjSub (w 0) K, conjSub (w 1) K, conjSub (w 2) K, hP₂, hLΦ 0, hLΦ 1, hLΦ 2,
    hne 0 1 (by decide), hne 0 2 (by decide), hne 1 2 (by decide), hcard 0, hcard 1, hcard 2⟩

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4.Z2W
