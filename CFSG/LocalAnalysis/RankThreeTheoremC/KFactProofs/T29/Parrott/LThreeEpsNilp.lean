module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.LThreeEpsThree
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.LThreeEpsGroup

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott

open CFSG.Open Subgroup
open CFSG.RankThree.PartTwo.Sec4 CFSG.Assembly.LowTwoRank
open CFSG.HardMathSupport.Solomon.Coordinator

section Criterion

variable {X : Type} [Group X] [Finite X]

theorem hasNormalPComplement_of_pair {x v : X} (hrank : CFSG.Open.pRank 3
    (centralizer ({x} : Set X)) = 2) (hx3 : x ^ 3 = 1) (hv3 : v ^ 3 = 1) (hv1 : v ≠ 1)
    (hvx : v * x = x * v) (hxv : x ∉ zpowers v) (hN : ∀ g ∈ centralizer ({x} : Set X),
      g ∈ normalizer ((zpowers v ⊔ zpowers x : Subgroup X) : Set X) → g * v * g⁻¹ = v) :
    CFSG.HasNormalPComplement 3 ↥(centralizer ({x} : Set X)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C := centralizer ({x} : Set X) with hCdef
  set Q : Subgroup X := zpowers v ⊔ zpowers x with hQdef
  have hel : ∀ c : X, c ^ 3 = 1 → IsElemAbelian 3 (zpowers c) := fun c hc => by
    rw [Subgroup.zpowers_eq_closure]
    refine IsElemAbelian.closure_of_commute (fun u hu w hw => ?_) (fun u hu => ?_)
    · rw [Set.mem_singleton_iff] at hu hw
      rw [hu, hw]
    · rw [Set.mem_singleton_iff] at hu
      rw [hu, hc]
  have hcomm : ∀ a ∈ zpowers v, ∀ b ∈ zpowers x, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact ((Commute.zpow_left hvx i).zpow_right j).eq
  have hQ : IsElemAbelian 3 Q := (hel v hv3).sup_of_commute (hel x hx3) hcomm
  have hQ9 : Nat.card Q = 9 := by
    rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers Nat.prime_three (zpowers v) hx3 hxv
      (fun a ha => hcomm a ha x (Subgroup.mem_zpowers x)), Nat.card_zpowers,
      orderOf_eq_prime hv3 hv1]
  have hQC : Q ≤ C := fun q hq => mem_centralizer_singleton_iff.2
    (hQ.comm hq (le_sup_right (a := zpowers v) (Subgroup.mem_zpowers x)))
  refine hasNormalPComplement_of_elemAbelian (G := ↥C) (Q := Q.subgroupOf C)
    (hQ.comap C.subtype_injective) ?_ ?_
  ·
    intro g hg3 hgQ
    by_contra hgQ'
    have hgQ'' : (g : X) ∉ Q := fun h => hgQ' (Subgroup.mem_subgroupOf.2 h)
    have hg3' : (g : X) ^ 3 = 1 := by rw [← Subgroup.coe_pow, hg3, Subgroup.coe_one]
    have hcg : ∀ q ∈ Q, q * (g : X) = (g : X) * q := fun q hq =>
      congrArg Subtype.val (hgQ ⟨q, hQC hq⟩ (Subgroup.mem_subgroupOf.2 hq))
    have hW : IsElemAbelian 3 (Q ⊔ zpowers (g : X)) := hQ.sup_of_commute (hel _ hg3')
      (fun a ha b hb => by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
        exact (Commute.zpow_right (hcg a ha) k).eq)
    have hW27 : Nat.card ↥(Q ⊔ zpowers (g : X)) = 3 ^ 3 := by
      rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers Nat.prime_three Q hg3' hgQ'' hcg, hQ9]
      norm_num
    have hWC : Q ⊔ zpowers (g : X) ≤ C := sup_le hQC (zpowers_le.2 g.2)
    have := CFSG.SectionRank.le_pRank (by norm_num) hWC hW hW27
    omega
  ·
    intro g hg q hq
    have hgX : (g : X) ∈ normalizer (Q : Set X) := by
      refine mem_normalizer_of_conj_mem fun q' hq' => ?_
      have h1 := (Subgroup.mem_normalizer_iff.1 hg ⟨q', hQC hq'⟩).1
        (Subgroup.mem_subgroupOf.2 hq')
      exact Subgroup.mem_subgroupOf.1 h1
    have hgv := hN g g.2 hgX
    have hgx : (g : X) * x * (g : X)⁻¹ = x := by
      have := mem_centralizer_singleton_iff.1 g.2
      rw [this, mul_inv_cancel_right]
    have hle : Q ≤ centralizer ({(g : X)} : Set X) := sup_le
      (zpowers_le.2 (mem_centralizer_singleton_iff.2 (by
        calc v * (g : X) = (g : X) * v * (g : X)⁻¹ * (g : X) := by rw [hgv]
          _ = (g : X) * v := by group)))
      (zpowers_le.2 (mem_centralizer_singleton_iff.2 (by
        calc x * (g : X) = (g : X) * x * (g : X)⁻¹ * (g : X) := by rw [hgx]
          _ = (g : X) * x := by group)))
    have hq' : (q : X) * (g : X) = (g : X) * q :=
      mem_centralizer_singleton_iff.1 (hle (Subgroup.mem_subgroupOf.1 hq))
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← hq', mul_inv_cancel_right]

end Criterion

section Matrix

variable {K : Type} [Field K]

theorem conj_commute_of_mem_centMod {S : Subgroup (GL (Fin 3) K)} {y w s : GL (Fin 3) K}
    (hw : w ∈ centMod S y) (hs : s * y = y * s) :
    w * s * w⁻¹ * y = y * (w * s * w⁻¹) := by
  obtain ⟨-, z, hz, hzy⟩ := mem_centMod_iff_scalar.1 hw
  have hc := commute_of_mem_statedScalars (inv_mem hz)
  have h1 : w⁻¹ * y * w = z⁻¹ * y := by
    calc w⁻¹ * y * w = w⁻¹ * (z⁻¹ * (z * y)) * w := by group
      _ = w⁻¹ * (z⁻¹ * (w * y * w⁻¹)) * w := by rw [hzy]
      _ = w⁻¹ * z⁻¹ * w * y := by group
      _ = z⁻¹ * w⁻¹ * w * y := by rw [← hc w⁻¹]
      _ = z⁻¹ * y := by group
  calc w * s * w⁻¹ * y = w * s * (w⁻¹ * y * w) * w⁻¹ := by group
    _ = w * s * (z⁻¹ * y) * w⁻¹ := by rw [h1]
    _ = w * (s * z⁻¹) * y * w⁻¹ := by group
    _ = w * (z⁻¹ * s) * y * w⁻¹ := by rw [hc s]
    _ = w * z⁻¹ * (s * y) * w⁻¹ := by group
    _ = w * z⁻¹ * (y * s) * w⁻¹ := by rw [hs]
    _ = z⁻¹ * w * y * s * w⁻¹ := by rw [← hc w]; group
    _ = z⁻¹ * (w * y * w⁻¹) * (w * s * w⁻¹) := by group
    _ = z⁻¹ * (z * y) * (w * s * w⁻¹) := by rw [hzy]
    _ = y * (w * s * w⁻¹) := by group

theorem exists_conj_eq_scalar_mul {S : Subgroup (GL (Fin 3) K)} {y w : GL (Fin 3) K}
    (hw : w ∈ centMod S y) : ∃ c ∈ StatedScalars (Fin 3) K, y * w * y⁻¹ = c * w := by
  obtain ⟨-, z, hz, hzy⟩ := mem_centMod_iff_scalar.1 hw
  refine ⟨z⁻¹, inv_mem hz, ?_⟩
  have hc := commute_of_mem_statedScalars (inv_mem hz)
  calc y * w * y⁻¹ = z⁻¹ * (z * y) * w * y⁻¹ := by group
    _ = z⁻¹ * (w * y * w⁻¹) * w * y⁻¹ := by rw [hzy]
    _ = z⁻¹ * w := by group

variable {π : Bool} {p f : ℕ}

theorem IsTypeThree.not_forall_conj_mem (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (h2 : 2 < p ^ f) {y : GL (Fin 3) K} (hT : IsTypeThree π (p ^ f) K y) {w : GL (Fin 3) K}
    (hw : w ∈ slPi π 3 (p ^ f) K)
    (hC3 : Nat.card ↥(slPi π 3 (p ^ f) K ⊓ centralizer ({y, w} : Set (GL (Fin 3) K))) = 3) :
    ¬ ∀ t ∈ slPi π 3 (p ^ f) K ⊓ centralizer ({y} : Set (GL (Fin 3) K)),
      w * t * w⁻¹ * t⁻¹ ∈ StatedScalars (Fin 3) K := by
  intro hall
  have hπ : π = false → CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K := fun h => by
    subst h; exact hK.unitary
  have := hK.finite
  set C := slPi π 3 (p ^ f) K ⊓ centralizer ({y} : Set (GL (Fin 3) K))
  haveI := hT.cyclic
  obtain ⟨t₀, ht₀⟩ := IsCyclic.exists_generator (α := ↥C)
  have hord : orderOf t₀ = Nat.card C := orderOf_eq_card_of_forall_mem_zpowers ht₀
  obtain ⟨m, hm, hm1, -⟩ := hT.card_eq hK hq h2
  obtain ⟨c, hc⟩ := hall t₀ t₀.2
  have hcL : Matrix.GeneralLinearGroup.scalar (Fin 3) c ∈ slPi π 3 (p ^ f) K := by
    rw [hc]
    exact mul_mem (mul_mem (mul_mem hw (Subgroup.mem_inf.1 t₀.2).1) (inv_mem hw))
      (inv_mem (Subgroup.mem_inf.1 t₀.2).1)
  have hc3 : (Matrix.GeneralLinearGroup.scalar (Fin 3) c) ^ 3 = 1 := by
    have h1 := ((mem_slPi_iff hπ).1 hcL).2
    rw [det_scalar] at h1
    rw [← map_pow]
    have : c ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, h1, Units.val_one])
    rw [this, map_one]
  have hcomm := commute_of_mem_statedScalars
    (z := Matrix.GeneralLinearGroup.scalar (Fin 3) c) ⟨c, rfl⟩
  have hwt : w * (t₀ : GL (Fin 3) K) * w⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin 3) c * t₀ := by rw [hc]; group
  have hwt3 : w * (t₀ : GL (Fin 3) K) ^ 3 * w⁻¹ = (t₀ : GL (Fin 3) K) ^ 3 := by
    rw [← conj_pow, hwt, (Commute.mul_pow (show Commute (Matrix.GeneralLinearGroup.scalar
      (Fin 3) c) (t₀ : GL (Fin 3) K) from (hcomm _).symm) 3), hc3, one_mul]
  have hmem : (t₀ : GL (Fin 3) K) ^ 3 ∈
      slPi π 3 (p ^ f) K ⊓ centralizer ({y, w} : Set (GL (Fin 3) K)) := by
    refine Subgroup.mem_inf.2 ⟨pow_mem (Subgroup.mem_inf.1 t₀.2).1 3, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    rcases hu with hu | hu
    · rw [hu]
      have := mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 t₀.2).2
      exact ((Commute.pow_left (show Commute (t₀ : GL (Fin 3) K) y from this) 3).symm).eq
    · rw [Set.mem_singleton_iff.1 hu]
      calc w * (t₀ : GL (Fin 3) K) ^ 3 = w * (t₀ : GL (Fin 3) K) ^ 3 * w⁻¹ * w := by group
        _ = (t₀ : GL (Fin 3) K) ^ 3 * w := by rw [hwt3]
  have h9 : orderOf t₀ ∣ 9 := by
    have h3 : orderOf ((t₀ : GL (Fin 3) K) ^ 3) ∣ 3 := by
      have := orderOf_dvd_natCard (⟨_, hmem⟩ :
        ↥(slPi π 3 (p ^ f) K ⊓ centralizer ({y, w} : Set (GL (Fin 3) K))))
      rw [hC3, Subgroup.orderOf_mk] at this
      exact this
    have h4 : (t₀ : GL (Fin 3) K) ^ 9 = 1 := by
      rw [show 9 = 3 * 3 from rfl, pow_mul]
      exact orderOf_dvd_iff_pow_eq_one.1 h3
    rw [← Subgroup.orderOf_coe]
    exact orderOf_dvd_of_pow_eq_one h4
  have h10 := Nat.le_of_dvd (by norm_num) h9
  have hm' : Nat.card C = 3 * m := hm
  rw [hord, hm'] at h10
  omega

end Matrix

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott
