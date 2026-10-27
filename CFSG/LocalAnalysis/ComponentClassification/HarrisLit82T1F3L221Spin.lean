module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3L221Diag
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3L57Aut
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1C3Tools
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3L221Bar
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3L221Cases

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup CFSG.LieType.HighestRoot
open scoped MatrixGroups Pointwise

namespace F3L221

variable {Y : Type} [Group Y] [Finite Y]

omit [Finite Y] in
theorem centralizer_le_normalizer_set (L : Subgroup Y) :
    centralizer (L : Set Y) ≤ normalizer (L : Set Y) := by
  intro c hc
  rw [mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have h1 : h * c = c * h := (mem_centralizer_iff.mp hc) h hh
    rw [show c * h * c⁻¹ = h by rw [← h1]; group]
    exact hh
  · intro hh
    have h1 : c * h * c⁻¹ * c = c * (c * h * c⁻¹) := (mem_centralizer_iff.mp hc) _ hh
    have h2 : h = c * h * c⁻¹ := by
      calc h = c⁻¹ * (c * h * c⁻¹ * c) := by group
        _ = c⁻¹ * (c * (c * h * c⁻¹)) := by rw [h1]
        _ = c * h * c⁻¹ := by group
    rw [h2]
    exact hh

omit [Finite Y] in
theorem isSubnormal_subgroupOf_mono {A D C : Subgroup Y} (hDC : D ≤ C)
    (h : (A.subgroupOf C).IsSubnormal) : (A.subgroupOf D).IsSubnormal := by
  have h1 := h.subgroupOf (K := D.subgroupOf C)
  have heq : A.subgroupOf D = ((A.subgroupOf C).subgroupOf (D.subgroupOf C)).comap
      (subgroupOfEquivOfLe hDC).symm.toMonoidHom := by
    ext x
    exact Iff.rfl
  rw [heq]
  exact h1.comap _

theorem mem_sup_centralizer_of_odd {L : Subgroup Y} (hcov : IsCoverOf .POmegaOdd 3 3 1 2 ↥L)
    {k : Y} (hkN : k ∈ normalizer (L : Set Y)) (hodd : Odd (orderOf k)) :
    k ∈ L ⊔ centralizer (L : Set Y) := by
  have hmap : L.map (MulAut.conj k).toMonoidHom = L := mem_normalizer_iff_map_conj_eq.mp hkN
  let α : MulAut ↥L := ((MulAut.conj k).subgroupMap L).trans (MulEquiv.subgroupCongr hmap)
  have hα : ∀ y : ↥L, ((α y : ↥L) : Y) = k * y * k⁻¹ := fun y => rfl
  have hαj : ∀ j : ℕ, ∀ y : ↥L, (((α ^ j) y : ↥L) : Y) = k ^ j * y * (k ^ j)⁻¹ := by
    intro j
    induction j with
    | zero => intro y; simp
    | succ j ih =>
      intro y
      rw [pow_succ', MulAut.mul_apply, hα, ih, pow_succ']
      group
  have hα1 : α ^ orderOf k = 1 := by
    ext y
    rw [hαj, pow_orderOf_eq_one, one_mul, inv_one, mul_one]
    rfl
  have hrange : α ^ orderOf k ∈ (MulAut.conj : ↥L →* MulAut ↥L).range := by
    rw [hα1]
    exact one_mem _
  obtain ⟨l, hl⟩ := mem_range_conj_of_pow_mem_three Nat.prime_three (by norm_num) hcov hodd hrange
  have hc : (l : Y)⁻¹ * k ∈ centralizer (L : Set Y) := by
    rw [mem_centralizer_iff]
    intro y hy
    have h1 : ((MulAut.conj l ⟨y, hy⟩ : ↥L) : Y) = ((α ⟨y, hy⟩ : ↥L) : Y) := by rw [hl]
    rw [MulAut.conj_apply, hα] at h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
    calc y * ((l : Y)⁻¹ * k) = (l : Y)⁻¹ * (l * y * (l : Y)⁻¹) * k := by group
      _ = (l : Y)⁻¹ * (k * y * k⁻¹) * k := by rw [h1]
      _ = (l : Y)⁻¹ * k * y := by group
  have hk : k = (l : Y) * ((l : Y)⁻¹ * k) := by group
  rw [hk]
  exact mul_mem (mem_sup_left l.2) (mem_sup_right hc)

theorem oPrimeResidualOf_le_of_spinThree {L K : Subgroup Y}
    (hcov : IsCoverOf .POmegaOdd 3 3 1 2 ↥L) {z : Y} (hz : orderOf z = 2)
    (hzL : ∃ l ∈ L, z * l ≠ l * z) (hK : IsSolvableTwoComponentIn K (centralizer {z}))
    (hzK : z ∈ K) (hKN : K ≤ normalizer (L : Set Y)) : GH74.GLS.oPrimeResidualOf 2 K ≤ L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({z} : Set Y) with hC
  set Z := centralizer (L : Set Y) with hZ
  have hzc : ∀ k ∈ K, k * z = z * k := fun k hk => mem_centralizer_singleton_iff.mp (hK.1 hk)
  have hZc : ∀ {d : Y}, d ∈ Z → ∀ m ∈ L, d * m = m * d :=
    fun {d} hd m hm => ((mem_centralizer_iff.mp hd) m hm).symm
  have hNL : ∀ {k : Y}, k ∈ normalizer (L : Set Y) → ∀ m ∈ L, k * m * k⁻¹ ∈ L :=
    fun {k} hk m hm => (mem_normalizer_iff.mp hk m).mp hm
  have hZL : ∀ ζ ∈ L, ζ ∈ Z → ζ * ζ = 1 := by
    intro ζ hζL hζZ
    have hζc : (⟨ζ, hζL⟩ : ↥L) ∈ center ↥L := by
      rw [mem_center_iff]
      intro g
      exact Subtype.ext ((mem_centralizer_iff.mp hζZ) g g.2)
    have h3 := pow_card_eq_one' (G := ↥(center ↥L)) (x := ⟨_, hζc⟩)
    rw [hcov.2.1] at h3
    have h4 := congrArg (fun w : ↥(center ↥L) => ((w : ↥L) : Y)) h3
    simpa only [sq, Subgroup.coe_mul, Subgroup.coe_one] using h4
  have hZN : Z ≤ normalizer (L : Set Y) := centralizer_le_normalizer_set L
  have hKW : K ≤ L ⊔ Z := le_of_forall_odd hK fun k hk hodd =>
    mem_sup_centralizer_of_odd hcov (hKN hk) hodd
  have hWmul : ∀ {w : Y}, w ∈ L ⊔ Z → ∃ l ∈ L, ∃ d ∈ Z, w = l * d := by
    intro w hw
    have hws : w ∈ ((L ⊔ Z : Subgroup Y) : Set Y) := hw
    rw [coe_mul_of_right_le_normalizer_left L Z hZN] at hws
    obtain ⟨l, hl, d, hd, h⟩ := hws
    exact ⟨l, hl, d, hd, h.symm⟩
  obtain ⟨x, hx, c, hc, hxc⟩ := hWmul (hKW hzK)
  set A := L ⊓ C with hA
  set B := Z ⊓ C with hB
  have hsq : ∀ y ∈ K, y * y ∈ A ⊔ B := by
    intro y hy
    obtain ⟨l, hl, d, hd, hyld⟩ := hWmul (hKW hy)
    have hyz := hzc y hy
    rw [hyld, hxc] at hyz
    have e1 : l * d * (x * c) = (l * x) * (d * c) := by
      calc l * d * (x * c) = l * (d * x) * c := by group
        _ = l * (x * d) * c := by rw [hZc hd x hx]
        _ = (l * x) * (d * c) := by group
    have e2 : x * c * (l * d) = (x * l) * (c * d) := by
      calc x * c * (l * d) = x * (c * l) * d := by group
        _ = x * (l * c) * d := by rw [hZc hc l hl]
        _ = (x * l) * (c * d) := by group
    rw [e1, e2] at hyz
    have hζ : (x * l)⁻¹ * (l * x) = (c * d) * (d * c)⁻¹ := by
      calc (x * l)⁻¹ * (l * x) = (x * l)⁻¹ * ((l * x) * (d * c)) * (d * c)⁻¹ := by group
        _ = (x * l)⁻¹ * ((x * l) * (c * d)) * (d * c)⁻¹ := by rw [hyz]
        _ = (c * d) * (d * c)⁻¹ := by group
    set ζ := (x * l)⁻¹ * (l * x) with hζdef
    have hζL : ζ ∈ L := mul_mem (inv_mem (mul_mem hx hl)) (mul_mem hl hx)
    have hζZ : ζ ∈ Z := by
      rw [hζ]
      exact mul_mem (mul_mem hc hd) (inv_mem (mul_mem hd hc))
    have hζζ := hZL ζ hζL hζZ
    have hlx : l * x = x * l * ζ := by rw [hζdef]; group
    have hl2x : l * l * x = x * (l * l) := by
      calc l * l * x = l * (l * x) := by group
        _ = l * (x * l * ζ) := by rw [hlx]
        _ = (l * x) * (l * ζ) := by group
        _ = (x * l * ζ) * (l * ζ) := by rw [hlx]
        _ = x * l * (ζ * l) * ζ := by group
        _ = x * l * (l * ζ) * ζ := by rw [hZc hζZ l hl]
        _ = x * (l * l) * (ζ * ζ) := by group
        _ = x * (l * l) := by rw [hζζ, mul_one]
    have hl2 : l * l ∈ A := by
      refine mem_inf.mpr ⟨mul_mem hl hl, ?_⟩
      rw [mem_centralizer_singleton_iff, hxc]
      have hcll : c * (l * l) = (l * l) * c := hZc hc _ (mul_mem hl hl)
      calc l * l * (x * c) = (l * l * x) * c := by group
        _ = x * (l * l) * c := by rw [hl2x]
        _ = x * ((l * l) * c) := by group
        _ = x * (c * (l * l)) := by rw [hcll]
        _ = x * c * (l * l) := by group
    have hdc : d * c = ζ⁻¹ * (c * d) := by
      rw [hζ]
      group
    have hdζ : d * ζ⁻¹ = ζ⁻¹ * d := hZc hd _ (inv_mem hζL)
    have hζinv : ζ⁻¹ * ζ⁻¹ = 1 := by
      rw [← mul_inv_rev, hζζ, inv_one]
    have hd2c : d * d * c = c * (d * d) := by
      calc d * d * c = d * (d * c) := by group
        _ = d * (ζ⁻¹ * (c * d)) := by rw [hdc]
        _ = (d * ζ⁻¹) * (c * d) := by group
        _ = (ζ⁻¹ * d) * (c * d) := by rw [hdζ]
        _ = ζ⁻¹ * (d * c) * d := by group
        _ = ζ⁻¹ * (ζ⁻¹ * (c * d)) * d := by rw [hdc]
        _ = (ζ⁻¹ * ζ⁻¹) * (c * (d * d)) := by group
        _ = c * (d * d) := by rw [hζinv, one_mul]
    have hd2 : d * d ∈ B := by
      refine mem_inf.mpr ⟨mul_mem hd hd, ?_⟩
      rw [mem_centralizer_singleton_iff, hxc]
      have hdx : (d * d) * x = x * (d * d) := hZc (mul_mem hd hd) x hx
      calc d * d * (x * c) = (d * d * x) * c := by group
        _ = x * (d * d) * c := by rw [hdx]
        _ = x * (d * d * c) := by group
        _ = x * (c * (d * d)) := by rw [hd2c]
        _ = x * c * (d * d) := by group
    have hyy : y * y = (l * l) * (d * d) := by
      rw [hyld]
      calc l * d * (l * d) = l * (d * l) * d := by group
        _ = l * (l * d) * d := by rw [hZc hd l hl]
        _ = (l * l) * (d * d) := by group
    rw [hyy]
    exact mul_mem (mem_sup_left hl2) (mem_sup_right hd2)
  have hKAB : K ≤ A ⊔ B := le_of_forall_odd hK fun k hk hodd => by
    obtain ⟨y, hy, hyk⟩ := exists_sq_eq_of_odd hk hodd
    rw [← hyk]
    exact hsq y hy
  have hzB : z ∉ B := by
    intro h
    obtain ⟨l, hl, hne⟩ := hzL
    exact hne (hZc (mem_inf.mp h).1 l hl)
  obtain ⟨e⟩ := nonempty_sl23_of_central hK hzK hz hzc
  set OK := (pPrimeCore 2 ↥K).map K.subtype with hOK
  have hKBn : ∀ k ∈ K, ∀ b ∈ B, k * b * k⁻¹ ∈ B := by
    intro k hk b hb
    obtain ⟨hbZ, hbC⟩ := mem_inf.mp hb
    refine mem_inf.mpr ⟨?_, mul_mem (mul_mem (hK.1 hk) hbC) (inv_mem (hK.1 hk))⟩
    rw [mem_centralizer_iff]
    intro m hm
    have hm' : k⁻¹ * m * k ∈ L := by
      have h1 := hNL (inv_mem (hKN hk)) m hm
      rwa [inv_inv] at h1
    have h2 : b * (k⁻¹ * m * k) = (k⁻¹ * m * k) * b := hZc hbZ _ hm'
    calc m * (k * b * k⁻¹) = k * ((k⁻¹ * m * k) * b) * k⁻¹ := by group
      _ = k * (b * (k⁻¹ * m * k)) * k⁻¹ := by rw [h2]
      _ = k * b * k⁻¹ * m := by group
  have hKB : K ⊓ B ≤ OK := le_pPrimeCore_of_not_mem e hzK hz hzc inf_le_left
    (fun k hk n hn => mem_inf.mpr ⟨mul_mem (mul_mem hk (mem_inf.mp hn).1) (inv_mem hk),
      hKBn k hk n (mem_inf.mp hn).2⟩) (fun h => hzB (mem_inf.mp h).2)
  set M := A ⊔ B with hM
  have hMC : M ≤ C := sup_le inf_le_right inf_le_right
  have hMN : M ≤ normalizer (L : Set Y) := sup_le (inf_le_left.trans le_normalizer)
    (inf_le_left.trans hZN)
  have hOKC : ∀ m ∈ C, ∀ o ∈ OK, m * o * m⁻¹ ∈ OK := by
    intro m hm o ho
    rw [hOK, hK.2.2.1] at ho ⊢
    obtain ⟨o', ho', hoo⟩ := ho
    refine ⟨⟨m, hm⟩ * o' * ⟨m, hm⟩⁻¹,
      (inferInstance : (pPrimeCore 2 ↥C).Normal).conj_mem o' ho' _, ?_⟩
    rw [← hoo]
    rfl
  have hAn : ∀ m ∈ M, ∀ a ∈ A ⊔ OK, m * a * m⁻¹ ∈ A ⊔ OK := by
    intro m hm a ha
    have hle : A ⊔ OK ≤ (A ⊔ OK).comap (MulAut.conj m).toMonoidHom := by
      refine sup_le (fun a' ha' => ?_) (fun o ho => ?_)
      · obtain ⟨ha'L, ha'C⟩ := mem_inf.mp ha'
        exact mem_sup_left (mem_inf.mpr ⟨hNL (hMN hm) a' ha'L,
          mul_mem (mul_mem (hMC hm) ha'C) (inv_mem (hMC hm))⟩)
      · exact mem_sup_right (hOKC m (hMC hm) o ho)
    exact hle ha
  have hKs : (K.subgroupOf M).IsSubnormal := isSubnormal_subgroupOf_mono hMC hK.2.1
  set D : Set Y := {q | ∃ hq : q ∈ K, e (QuotientGroup.mk ⟨q, hq⟩) ^ 4 = 1} with hD
  have hDB : ∀ q ∈ D, q ∈ (A ⊔ OK) ⊔ B := by
    rintro q ⟨hq, -⟩
    exact sup_le_sup_right le_sup_left B (hKAB hq)
  have hDc : ∀ q ∈ D, ∃ a ∈ D, ∃ g ∈ K, q * (a * g * a⁻¹ * g⁻¹)⁻¹ ∈ A ⊔ OK := by
    rintro q ⟨hq, hq4⟩
    obtain ⟨a₀, g₀, ha₀, hqa⟩ := sl23_commutator hq4
    obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (e.symm a₀)
    obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (e.symm g₀)
    have hea : e (QuotientGroup.mk a) = a₀ := by rw [ha, MulEquiv.apply_symm_apply]
    have heg : e (QuotientGroup.mk g) = g₀ := by rw [hg, MulEquiv.apply_symm_apply]
    refine ⟨(a : Y), ⟨a.2, ?_⟩, (g : Y), g.2, ?_⟩
    · show e (QuotientGroup.mk a) ^ 4 = 1
      rw [hea]
      exact ha₀
    · have h1 : (⟨q, hq⟩ : ↥K) * (a * g * a⁻¹ * g⁻¹)⁻¹ ∈ pPrimeCore 2 ↥K := by
        rw [← QuotientGroup.eq_one_iff, ← map_eq_one_iff e e.injective]
        simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_inv, hea, heg]
        rw [← hqa, mul_inv_cancel]
      exact mem_sup_right ⟨_, h1, rfl⟩
  have key := mem_sup_inf_of_isSubnormal (M := M) (A := A ⊔ OK) (B := B) (K := K)
    le_sup_right hKAB hAn hKBn hDB hDc hKs
  have hOKN : OK ≤ normalizer (A : Set Y) := by
    intro o ho
    have hoK : o ∈ K := by
      rw [hOK] at ho
      obtain ⟨o', -, rfl⟩ := ho
      exact o'.2
    rw [mem_normalizer_iff]
    intro a'
    constructor
    · intro ha'
      obtain ⟨ha'L, ha'C⟩ := mem_inf.mp ha'
      exact mem_inf.mpr ⟨hNL (hKN hoK) a' ha'L,
        mul_mem (mul_mem (hK.1 hoK) ha'C) (inv_mem (hK.1 hoK))⟩
    · intro ha'
      obtain ⟨ha'L, ha'C⟩ := mem_inf.mp ha'
      have h1 := hNL (inv_mem (hKN hoK)) _ ha'L
      have h2 : o⁻¹ * (o * a' * o⁻¹) * o⁻¹⁻¹ = a' := by group
      rw [h2] at h1
      refine mem_inf.mpr ⟨h1, ?_⟩
      have h3 := mul_mem (mul_mem (inv_mem (hK.1 hoK)) ha'C) (hK.1 hoK)
      rwa [show o⁻¹ * (o * a' * o⁻¹) * o = a' by group] at h3
  have hOKodd : Odd (Nat.card OK) := by
    rw [hOK, Subgroup.card_map_of_injective K.subtype_injective]
    exact odd_card_pPrimeCore_two ↥K
  unfold GH74.GLS.oPrimeResidualOf GH74.GLS.oPrimeResidual
  rw [MonoidHom.map_closure, closure_le]
  rintro _ ⟨x', ⟨n, hn⟩, rfl⟩
  have hxn : (x' : Y) ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have hxD : (x' : Y) ∈ D := by
    refine ⟨x'.2, ?_⟩
    set s := e (QuotientGroup.mk ⟨(x' : Y), x'.2⟩) with hs
    have h1 : s ^ 2 ^ n = 1 := by
      rw [hs, ← map_pow, ← QuotientGroup.mk_pow]
      rw [show (⟨(x' : Y), x'.2⟩ : ↥K) ^ 2 ^ n = 1 from hn, QuotientGroup.mk_one, map_one]
    have h2 : orderOf s ∣ 8 := by
      have h3 : orderOf s ∣ 8 * 3 := by
        have h4 := orderOf_dvd_natCard s
        rw [card_SL23] at h4
        exact h4
      have hcop : Nat.Coprime (orderOf s) 3 :=
        Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one h1)
          (Nat.Coprime.pow_left n (by norm_num))
      exact hcop.dvd_of_dvd_mul_right h3
    exact sl23_pow_four_of_pow_eight s (orderOf_dvd_iff_pow_eq_one.mp h2)
  have h1 := key _ hxD
  have h2 : (x' : Y) ∈ A ⊔ OK :=
    (sup_le le_rfl (hKB.trans le_sup_right) : (A ⊔ OK) ⊔ (K ⊓ B) ≤ A ⊔ OK) h1
  exact (mem_inf.mp (mem_of_mem_sup_of_odd hOKN hOKodd h2 hxn)).1

theorem orderOf_mk_pPrimeCore {X : Type} [Group X] [Finite X] {z : X} (hz : orderOf z = 2) :
    orderOf (QuotientGroup.mk z : X ⧸ pPrimeCore 2 X) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzO : z ∉ pPrimeCore 2 X := by
    intro h
    have h1 := orderOf_dvd_natCard (⟨z, h⟩ : ↥(pPrimeCore 2 X))
    have h2 : orderOf (⟨z, h⟩ : ↥(pPrimeCore 2 X)) = 2 := by
      rw [← Subgroup.orderOf_coe]
      exact hz
    rw [h2] at h1
    exact (Nat.not_even_iff_odd.mpr (odd_card_pPrimeCore_two X)) (even_iff_two_dvd.mpr h1)
  have hzz : z ^ 2 = 1 := by
    rw [← hz]
    exact pow_orderOf_eq_one z
  apply orderOf_eq_prime
  · rw [← QuotientGroup.mk_pow, hzz, QuotientGroup.mk_one]
  · intro h
    exact hzO ((QuotientGroup.eq_one_iff z).mp h)

theorem lemma221_spinThree {X : Type} [Group X] [Finite X] {z : X} (hz : orderOf z = 2)
    {L : Subgroup X} (hL : IsTwoComponentIn L ⊤)
    (hcov : IsCoverOf .POmegaOdd 3 3 1 2 (↥L ⧸ pPrimeCore 2 ↥L)) {K : Subgroup X}
    (hK : IsSolvableTwoComponentIn K (centralizer {z})) (hzK : z ∈ K)
    (hKN : K ≤ normalizer (L : Set X) ∨ ∀ l ∈ L, z * l * z⁻¹ * l⁻¹ ∈ pPrimeCore 2 X) :
    ⁅K, L⁆ ≤ (pPrimeCore 2 ↥L).map L.subtype ∨ GH74.GLS.oPrimeResidualOf 2 K ≤ L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (pPrimeCore 2 X) with hπ
  have hz' := orderOf_mk_pPrimeCore hz
  obtain ⟨hLb, ⟨eL⟩⟩ := isTwoComponentIn_map_mk hL
  have hcovb : IsCoverOf .POmegaOdd 3 3 1 2 ↥(L.map π) := isCoverOf_of_mulEquiv eL hcov
  have hLbs : (L.map π).IsSubnormal := by
    have h := hLb.2.1.map (f := (⊤ : Subgroup (X ⧸ pPrimeCore 2 X)).subtype)
      (fun x => ⟨⟨x, mem_top x⟩, rfl⟩)
    rwa [subgroupOf_map_subtype, inf_top_eq] at h
  have hKb := isSolvableTwoComponentIn_map_mk hz hK
  have hzKb : (QuotientGroup.mk z : X ⧸ pPrimeCore 2 X) ∈ K.map π := mem_map_of_mem _ hzK
  by_cases hc : ∀ l ∈ L.map π,
      (QuotientGroup.mk z : X ⧸ pPrimeCore 2 X) * l = l * QuotientGroup.mk z
  · left
    have h1 := commute_of_centralizes hLbs hcovb.1 hc hKb
    exact commutator_le_of_bar hL fun k hk l hl =>
      h1 _ (mem_map_of_mem _ hk) _ (mem_map_of_mem _ hl)
  · right
    push Not at hc
    have hKN' : K ≤ normalizer (L : Set X) := by
      rcases hKN with h | h
      · exact h
      · exfalso
        obtain ⟨_, ⟨l, hl, rfl⟩, hne⟩ := hc
        apply hne
        have h2 : (QuotientGroup.mk (z * l * z⁻¹ * l⁻¹) : X ⧸ pPrimeCore 2 X) = 1 :=
          (QuotientGroup.eq_one_iff _).mpr (h l hl)
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
          QuotientGroup.mk_inv] at h2
        show (QuotientGroup.mk z : X ⧸ pPrimeCore 2 X) * QuotientGroup.mk l =
          QuotientGroup.mk l * QuotientGroup.mk z
        calc (QuotientGroup.mk z : X ⧸ pPrimeCore 2 X) * QuotientGroup.mk l =
            ((QuotientGroup.mk z : X ⧸ pPrimeCore 2 X) * QuotientGroup.mk l *
              (QuotientGroup.mk z)⁻¹ * (QuotientGroup.mk l)⁻¹) *
              (QuotientGroup.mk l * QuotientGroup.mk z) := by group
          _ = QuotientGroup.mk l * QuotientGroup.mk z := by rw [h2, one_mul]
    have hKbN : K.map π ≤ normalizer ((L.map π : Subgroup (X ⧸ pPrimeCore 2 X)) :
        Set (X ⧸ pPrimeCore 2 X)) := by
      rintro _ ⟨k, hk, rfl⟩
      rw [mem_normalizer_iff_map_conj_eq]
      have h1 := mem_normalizer_iff_map_conj_eq.mp (hKN' hk)
      have h2 : (MulAut.conj (π k)).toMonoidHom.comp π = π.comp (MulAut.conj k).toMonoidHom := by
        ext y
        simp [MulAut.conj_apply]
      rw [map_map, h2, ← map_map, h1]
    exact oPrimeResidualOf_le_of_bar hL
      (oPrimeResidualOf_le_of_spinThree hcovb hz' hc hKb hzKb hKbN)

end F3L221

end CFSG.ComponentClassification.HarrisLit.T1
