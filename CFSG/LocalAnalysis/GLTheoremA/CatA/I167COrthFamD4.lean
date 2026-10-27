module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167COrth
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167COrthFamType
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172V2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentType
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitOmBlkFix
public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders
public import CFSG.RankThree.PartOne.KC.OrthogonalFixedDerived
public import CFSG.RankThree.PartOne.KC.OrthogonalComponentFacts
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnOrth
import CFSG.LocalAnalysis.GLTheoremA.CatA.I114Grp

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open Module QuadraticMap CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.GroupTheory.WeirSylow
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.Y10GField
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.StandardType (GGLabelRigidInput)
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.RankThree.PartOne.KCOrthogonal (fixedSpace supportedFixedDerived OddOrderIsometry
  oddOrderIsometry_of_orthDerived supportedFixedDerivedEquiv)

section SLevel

theorem i167COrth_v2_psimple_le {S : Type} [Group S] [Finite S] {p : ℕ} {J : Subgroup S}
    (hJp : Nonempty (↥J ⧸ Subgroup.center ↥J ≃* PSimple p J)) :
    padicValNat 2 (Nat.card (PSimple p J)) ≤ padicValNat 2 (Nat.card ↥J) := by
  obtain ⟨e⟩ := hJp
  have hcard : Nat.card (PSimple p J) = Nat.card (↥J ⧸ Subgroup.center ↥J) :=
    (Nat.card_congr e.toEquiv).symm
  rw [hcard]
  have hy : Nat.card ↥J ≠ 0 :=
    (Finite.card_pos (α := ↥J) (h := ⟨⟨1, J.one_mem⟩⟩)).ne'
  have hdvd : Nat.card (↥J ⧸ Subgroup.center ↥J) ∣ Nat.card ↥J :=
    Subgroup.card_quotient_dvd_card (Subgroup.center ↥J)
  exact (padicValNat_dvd_iff_le (p := 2) (a := Nat.card ↥J)
    (n := padicValNat 2 (Nat.card (↥J ⧸ Subgroup.center ↥J))) hy).1
    (dvd_trans (pow_padicValNat_dvd (p := 2) (n := Nat.card (↥J ⧸ Subgroup.center ↥J)))
      hdvd)

private theorem i167COrth_d4_lb_aux1 {a v : ℕ} (hv : 6 ≤ v) (ha : a ≤ 1) : 6 * a ≤ v := by
  omega

private theorem i167COrth_d4_lb_aux2 {a v n k : ℕ} (hn : 3 ≤ n)
    (hv : v = k * (n * (n - 1))) (ha : a ≤ k) : 6 * a ≤ v := by
  rw [hv]
  have hn6 : 6 ≤ n * (n - 1) := by
    have h : 3 * 2 ≤ n * (n - 1) := Nat.mul_le_mul hn (by omega)
    omega
  calc 6 * a ≤ 6 * k := Nat.mul_le_mul_left 6 ha
    _ = k * 6 := by ring
    _ ≤ k * (n * (n - 1)) := Nat.mul_le_mul_left k hn6

theorem i167COrth_d4_lb (hD : COrthLabelDict) (hRig : GGLabelRigidInput) (hb : CatDistinct.OrderBridge)
    {S : Type} [Group S] [Finite S] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hZ : Subgroup.center S = ⊥) {α : MulAut S} {labK : GLALabel} (hFam : FamOrth labK)
    (hInn : InnDiagKind S labK α) (hαp : α ^ p = 1) {J : Subgroup S}
    (hJc : GLAPComponent p (fixSubgroup α) J) (hJq : CFSG.Open.IsQuasisimple ↥J)
    (hJp : Nonempty (↥J ⧸ Subgroup.center ↥J ≃* PSimple p J)) (hJt : Type167J p J) :
    6 * (canonLabel labK).n ≤ padicValNat 2 (Nat.card ↥J) := by
  have hle := i167COrth_v2_psimple_le hJp
  obtain ⟨e⟩ := hJp
  have hdiv : ∀ labJ : GLALabel, Y10F.HasLabel ↥J (fun l : GLALabel => l = labJ) →
      (canonLabel labK).n ∣ (canonLabel labJ).n := fun labJ hl =>
    Y10GField.innDiagOrth_of_ggLabelRigidInput hRig S p α J labK labJ hFam hp hp2 hZ hInn hαp hl hJc
  rcases hJt with ⟨rfl, n, -, hn5, hc⟩ | ⟨rfl, n, -, hn6, hc⟩ | ⟨n, k, -, hn3, hk5, hk, hpk, hc⟩
  · obtain ⟨labJ, hl, hcan⟩ := hD.lnA hJq hn5 ((catalogIs_congr e).2 hc)
    have h1 : (canonLabel labK).n ∣ 1 := by simpa [hcan] using hdiv labJ hl
    obtain ⟨-, -, hv⟩ := S172.v2_isLnA hb (le_refl 1)
      (by simpa using hc : catalogIs _ (isLnA n (2 ^ 1)))
    have hv6 : 6 ≤ padicValNat 2 (Nat.card (PSimple 3 J)) := by
      have h : 5 * 4 ≤ n * (n - 1) := Nat.mul_le_mul hn5 (by omega)
      omega
    exact le_trans (i167COrth_d4_lb_aux1 hv6 (Nat.le_of_dvd (by norm_num) h1)) hle
  · obtain ⟨labJ, hl, hcan⟩ := hD.omM hJq (by omega) le_rfl
      (by simpa using (catalogIs_congr e).2 hc : catalogIs _ (isOmMA n (2 ^ 1)))
    have h1 : (canonLabel labK).n ∣ 1 := by simpa [hcan] using hdiv labJ hl
    obtain ⟨-, hv⟩ := S172.v2_isOmMA hb (le_refl 1)
      (by simpa using hc : catalogIs _ (isOmMA n (2 ^ 1)))
    have hv6 : 6 ≤ padicValNat 2 (Nat.card (PSimple 3 J)) := by
      have h : 6 * 5 ≤ n * (n - 1) := Nat.mul_le_mul hn6 (by omega)
      omega
    exact le_trans (i167COrth_d4_lb_aux1 hv6 (Nat.le_of_dvd (by norm_num) h1)) hle
  · obtain ⟨labJ, hl, hcan⟩ := hD.omP hJq hn3 hk (fun h3 => by omega)
      (by simpa using (catalogIs_congr e).2 hc : catalogIs _ (isOmPA n (2 ^ k)))
    have h1 : (canonLabel labK).n ∣ k := by
      have := hdiv labJ hl
      rw [hcan] at this
      split_ifs at this <;> exact this
    obtain ⟨-, hv⟩ := S172.v2_isOmPA hb hk hc
    exact le_trans (i167COrth_d4_lb_aux2 hn3 hv (Nat.le_of_dvd (by omega) h1)) hle

end SLevel

section Model

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {p : ℕ}

private theorem i167COrth_d4_ub_aux1 {W : Type} [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    {R : QuadraticForm F W} (hR : (QuadraticMap.polarBilin R).Nondegenerate) {a : ℕ}
    (hF : Nat.card F = 2 ^ a) (ha : 1 ≤ a)
    (hdim : Module.finrank F W = 2 * (0 + 1)) :
    padicValNat 2 (Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup R)) ≤ 2 * a + 1 := by
  by_cases hp : IsPlusType R
  · have hZ : (Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup R) : ℤ) =
        2 * ((Nat.card F : ℤ) - 1) := by
      have h := natCard_orthogonalGroup_of_type (K := F) (V := W) hR (m := 0) hdim
        (ε := 1) (Or.inl ⟨rfl, hp⟩)
      rw [Finset.Icc_eq_empty_of_lt (show 0 < 1 by omega), Finset.prod_empty] at h
      simpa using h
    have hNat : Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup R) = 2 * (Nat.card F - 1) := by
      have hq : 1 ≤ Nat.card F := by have h1 := Finite.one_lt_card (α := F); omega
      have hsub : ((Nat.card F - 1 : ℕ) : ℤ) = (Nat.card F : ℤ) - 1 := by
        rw [Nat.cast_sub hq]; ring
      refine Int.ofNat_inj.mp ?_
      rw [hZ]; push_cast; simp only [hsub]
    have hodd : Odd (Nat.card F - 1) := by
      rw [hF]; exact S172.odd_two_pow_sub_one ha
    have h := S172.v2_of_odd_mul (k := 1) (m := Nat.card F - 1) hodd
      (hNat.trans (by rw [pow_one]))
    rw [h]; omega
  · have hZ : (Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup R) : ℤ) =
        2 * ((Nat.card F : ℤ) + 1) := by
      have h := natCard_orthogonalGroup_of_type (K := F) (V := W) hR (m := 0) hdim
        (ε := -1) (Or.inr ⟨rfl, hp⟩)
      rw [Finset.Icc_eq_empty_of_lt (show 0 < 1 by omega), Finset.prod_empty] at h
      simpa using h
    have hNat : Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup R) = 2 * (Nat.card F + 1) := by
      refine Int.ofNat_inj.mp ?_
      rw [hZ]; push_cast; rfl
    have hodd : Odd (Nat.card F + 1) := by
      rw [hF]; exact S172.odd_two_pow_add_one ha
    have h := S172.v2_of_odd_mul (k := 1) (m := Nat.card F + 1) hodd
      (hNat.trans (by rw [pow_one]))
    rw [h]; omega

private theorem i167COrth_d4_ub_aux2 {W : Type} [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    {R : QuadraticForm F W} (hR : (QuadraticMap.polarBilin R).Nondegenerate) {a : ℕ}
    (hF : Nat.card F = 2 ^ a) (ha : 1 ≤ a)
    (hdim : Module.finrank F W = 2 * (1 + 1)) (hp : IsPlusType R) :
    padicValNat 2 (Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup R)) ≤ 2 * a + 1 := by
  have hq : 1 ≤ Nat.card F := by have h1 := Finite.one_lt_card (α := F); omega
  have hq2 : Nat.card F ^ 2 = 2 ^ (2 * a) := by rw [hF, ← pow_mul, Nat.mul_comm]
  have hpq : 2 * Nat.card F ^ 2 = 2 ^ (2 * a + 1) := by rw [hq2, ← pow_succ']
  have hZ : (Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup R) : ℤ) =
      2 * (Nat.card F : ℤ) ^ 2 * ((Nat.card F : ℤ) ^ 2 - 1) *
        ((Nat.card F : ℤ) ^ 2 - 1) := by
    have h := natCard_orthogonalGroup_of_type (K := F) (V := W) hR (m := 1) hdim
      (ε := 1) (Or.inl ⟨rfl, hp⟩)
    rw [Finset.Icc_self, Finset.prod_singleton] at h
    simpa using h
  have hNat : Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup R) =
      2 * Nat.card F ^ 2 * (Nat.card F ^ 2 - 1) * (Nat.card F ^ 2 - 1) := by
    have h1 : 1 ≤ Nat.card F ^ 2 := one_le_pow₀ hq
    have hsub : ((Nat.card F ^ 2 - 1 : ℕ) : ℤ) = (Nat.card F : ℤ) ^ 2 - 1 := by
      rw [Nat.cast_sub h1]; push_cast; ring
    refine Int.ofNat_inj.mp ?_
    rw [hZ]; push_cast; simp only [hsub]
  have hodd : Odd (Nat.card F ^ 2 - 1) := by
    have h := S172.odd_two_pow_sub_one (k := 2 * a) (by omega)
    simpa [hq2] using h
  have hmain : 2 * Nat.card F ^ 2 * (Nat.card F ^ 2 - 1) * (Nat.card F ^ 2 - 1) =
      2 ^ (2 * a + 1) * ((Nat.card F ^ 2 - 1) * (Nat.card F ^ 2 - 1)) := by
    rw [hpq]; ring
  have h := S172.v2_of_odd_mul (k := 2 * a + 1)
    (m := (Nat.card F ^ 2 - 1) * (Nat.card F ^ 2 - 1)) (hodd.mul hodd) (hNat.trans hmain)
  rw [h]

private theorem i167COrth_d4_ub_aux3 {W : Type} [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    {R : QuadraticForm F W} (hR : (QuadraticMap.polarBilin R).Nondegenerate) {a : ℕ}
    (hF : Nat.card F = 2 ^ a) (ha : 1 ≤ a)
    (hdim : Module.finrank F W = 2 * (1 + 1)) (hp : ¬ IsPlusType R) :
    padicValNat 2 (Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup R)) ≤ 2 * a + 1 := by
  have hq : 1 ≤ Nat.card F := by have h1 := Finite.one_lt_card (α := F); omega
  have hq2 : Nat.card F ^ 2 = 2 ^ (2 * a) := by rw [hF, ← pow_mul, Nat.mul_comm]
  have hpq : 2 * Nat.card F ^ 2 = 2 ^ (2 * a + 1) := by rw [hq2, ← pow_succ']
  have hZ : (Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup R) : ℤ) =
      2 * (Nat.card F : ℤ) ^ 2 * ((Nat.card F : ℤ) ^ 2 + 1) *
        ((Nat.card F : ℤ) ^ 2 - 1) := by
    have h := natCard_orthogonalGroup_of_type (K := F) (V := W) hR (m := 1) hdim
      (ε := -1) (Or.inr ⟨rfl, hp⟩)
    rw [Finset.Icc_self, Finset.prod_singleton] at h
    simpa using h
  have hNat : Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup R) =
      2 * Nat.card F ^ 2 * (Nat.card F ^ 2 + 1) * (Nat.card F ^ 2 - 1) := by
    have h1 : 1 ≤ Nat.card F ^ 2 := one_le_pow₀ hq
    have hsub : ((Nat.card F ^ 2 - 1 : ℕ) : ℤ) = (Nat.card F : ℤ) ^ 2 - 1 := by
      rw [Nat.cast_sub h1]; push_cast; ring
    refine Int.ofNat_inj.mp ?_
    rw [hZ]; push_cast; simp only [hsub]
  have hodd1 : Odd (Nat.card F ^ 2 + 1) := by
    have h := S172.odd_two_pow_add_one (k := 2 * a) (by omega)
    simpa [hq2] using h
  have hodd2 : Odd (Nat.card F ^ 2 - 1) := by
    have h := S172.odd_two_pow_sub_one (k := 2 * a) (by omega)
    simpa [hq2] using h
  have hmain : 2 * Nat.card F ^ 2 * (Nat.card F ^ 2 + 1) * (Nat.card F ^ 2 - 1) =
      2 ^ (2 * a + 1) * ((Nat.card F ^ 2 + 1) * (Nat.card F ^ 2 - 1)) := by
    rw [hpq]; ring
  have h := S172.v2_of_odd_mul (k := 2 * a + 1)
    (m := (Nat.card F ^ 2 + 1) * (Nat.card F ^ 2 - 1)) (hodd1.mul hodd2)
    (hNat.trans hmain)
  rw [h]

private theorem i167COrth_d4_ub_aux4 {W : Type} [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    {R : QuadraticForm F W} (hR : (QuadraticMap.polarBilin R).Nondegenerate) {a : ℕ}
    (hF : Nat.card F = 2 ^ a) (ha : 1 ≤ a)
    (hdim : Module.finrank F W = 2 * (1 + 1)) :
    padicValNat 2 (Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup R)) ≤ 2 * a + 1 := by
  by_cases hp : IsPlusType R
  · exact i167COrth_d4_ub_aux2 hR hF ha hdim hp
  · exact i167COrth_d4_ub_aux3 hR hF ha hdim hp

theorem i167COrth_d4_ub {W : Type} [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    {R : QuadraticForm F W} (hR : (QuadraticMap.polarBilin R).Nondegenerate) {a : ℕ}
    (hF : Nat.card F = 2 ^ a) (hW : Module.finrank F W ≤ 4) :
    padicValNat 2 (Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup R)) ≤ 2 * a + 1 := by
  obtain ⟨k, hk⟩ := CFSG.StandardType.WitOmBlk.even_finrank_of_nondeg hR
  have hk2 : k ≤ 2 := by omega
  have ha : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · rw [h, pow_zero] at hF
      have h1 := Finite.one_lt_card (α := F)
      omega
    · exact h
  interval_cases k
  · have hzero : ∀ x : W, x = 0 := finrank_zero_iff_forall_zero.mp (by omega)
    haveI : Subsingleton W := ⟨fun x y => by rw [hzero x, hzero y]⟩
    have hsub : Subsingleton ↥(TauCeti.QuadraticMap.orthogonalGroup R) :=
      ⟨fun x y => Subtype.ext (LinearEquiv.ext fun v => Subsingleton.elim _ _)⟩
    have hcard : Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup R) = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨1⟩⟩
    rw [hcard]; simp
  · exact i167COrth_d4_ub_aux1 hR hF ha (by omega)
  · exact i167COrth_d4_ub_aux4 hR hF ha (by omega)

theorem i167COrth_d4_card_dvd {x : ↥(orthDerived Q)} (hx : OddOrderIsometry Q p (x : V ≃ₗ[F] V))
    {J : Subgroup ↥(orthDerived Q)}
    (hJle : J ≤ (supportedFixedDerived Q (x : V ≃ₗ[F] V)).subgroupOf (orthDerived Q)) :
    Nat.card ↥J ∣ Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup
      (Q.comp (fixedSpace (x : V ≃ₗ[F] V)).subtype)) := by
  have h1 : Nat.card ↥J ∣
      Nat.card ↥((supportedFixedDerived Q (x : V ≃ₗ[F] V)).subgroupOf (orthDerived Q)) :=
    Subgroup.card_dvd_of_le hJle
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hx.supportedFixedDerived_le_orthDerived).toEquiv,
    Nat.card_congr (supportedFixedDerivedEquiv hx).toEquiv] at h1
  exact h1.trans (Subgroup.card_dvd_of_le
    CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup)

theorem i167COrth_d4_dim (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp : p.Prime)
    (hp2 : p ≠ 2) {a : ℕ} (hF : Nat.card F = 2 ^ a) (hdim : Module.finrank F V = 8)
    {g : ↥(orthDerived Q)} (hg : orderOf g = p) {J : Subgroup ↥(orthDerived Q)}
    (hJle : J ≤ (supportedFixedDerived Q (g : V ≃ₗ[F] V)).subgroupOf (orthDerived Q))
    (hv : 6 * a ≤ padicValNat 2 (Nat.card ↥J)) :
    Module.finrank F V = Module.finrank F (fixedSpace (g : V ≃ₗ[F] V)) + 2 := by
  classical
  have hpl : p ≠ ringChar F := by rw [ringChar.eq F 2]; exact hp2
  haveI : Finite V := Module.finite_of_finite F
  have hx : OddOrderIsometry Q p (g : V ≃ₗ[F] V) := oddOrderIsometry_of_orthDerived hp hpl hQ g hg
  have hR : (QuadraticMap.polarBilin (Q.comp (fixedSpace (g : V ≃ₗ[F] V)).subtype)).Nondegenerate :=
    hx.polarBilin_fixed_nondegenerate
  have hev : Even (Module.finrank F (fixedSpace (g : V ≃ₗ[F] V))) :=
    CFSG.StandardType.WitOmBlk.even_finrank_of_nondeg hR
  have hlt : Module.finrank F (fixedSpace (g : V ≃ₗ[F] V)) < 8 := by
    by_contra hge
    push Not at hge
    have htop : fixedSpace (g : V ≃ₗ[F] V) = ⊤ :=
      Submodule.eq_top_of_finrank_eq
        (le_antisymm (Submodule.finrank_le _) (by rw [hdim]; exact hge))
    have hg1 : (g : V ≃ₗ[F] V) = 1 := by
      refine LinearEquiv.ext fun v => ?_
      exact CFSG.RankThree.PartOne.KCOrthogonal.mem_fixedSpace.1
        (htop ▸ Submodule.mem_top)
    rw [show g = 1 from Subtype.ext hg1, orderOf_one] at hg
    exact hp.ne_one hg.symm
  have ha : 1 ≤ a := by
    have h2 : 2 ≤ Nat.card F := Finite.one_lt_card
    rw [hF] at h2
    rcases Nat.eq_zero_or_pos a with ha0 | hapos
    · rw [ha0, pow_zero] at h2; omega
    · exact hapos
  have hge5 : 5 ≤ Module.finrank F (fixedSpace (g : V ≃ₗ[F] V)) := by
    by_contra hlt5
    push Not at hlt5
    have hdvd : Nat.card ↥J ∣ Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup
        (Q.comp (fixedSpace (g : V ≃ₗ[F] V)).subtype)) :=
      i167COrth_d4_card_dvd (x := g) hx hJle
    have hub : padicValNat 2 (Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup
        (Q.comp (fixedSpace (g : V ≃ₗ[F] V)).subtype))) ≤ 2 * a + 1 :=
      i167COrth_d4_ub (W := ↥(fixedSpace (g : V ≃ₗ[F] V)))
        (R := Q.comp (fixedSpace (g : V ≃ₗ[F] V)).subtype) hR hF (by omega)
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hOne : Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace (g : V ≃ₗ[F] V)).subtype)) ≠ 0 := Nat.card_pos.ne'
    have hle : padicValNat 2 (Nat.card ↥J) ≤ padicValNat 2 (Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup
        (Q.comp (fixedSpace (g : V ≃ₗ[F] V)).subtype))) :=
      (padicValNat_dvd_iff_le hOne).1 (dvd_trans pow_padicValNat_dvd hdvd)
    omega
  obtain ⟨k, hk⟩ := hev
  omega

theorem i167COrth_d4_witt (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) {a : ℕ} (hF : Nat.card F = 2 ^ a)
    (hdim : Module.finrank F V = 8) {S : Type} [Group S] (e : S ≃* ↥(orthDerived Q)) {a₀ : S}
    (hg : orderOf (e a₀) = p) {J : Subgroup S} (hv : 6 * a ≤ padicValNat 2 (Nat.card ↥J)) :
    J.map e.toMonoidHom ≤
        (supportedFixedDerived Q ((e a₀ : ↥(orthDerived Q)) : V ≃ₗ[F] V)).subgroupOf
          (orthDerived Q) →
      Module.finrank F V = Module.finrank F (fixedSpace ((e a₀ : ↥(orthDerived Q)) : V ≃ₗ[F] V)) + 2 ∧
        (IsPlusType Q ↔ ¬ IsPlusType
          (Q.comp (fixedSpace ((e a₀ : ↥(orthDerived Q)) : V ≃ₗ[F] V)).subtype)) := by
  intro hJle
  have hv' : 6 * a ≤ padicValNat 2 (Nat.card ↥(J.map e.toMonoidHom)) := by
    rwa [Subgroup.card_map_of_injective e.injective]
  have hdimW := i167COrth_d4_dim hQ hp hp2 hF hdim hg hJle hv'
  refine ⟨hdimW, ?_⟩
  have hgpow : (e a₀) ^ p = 1 := hg ▸ pow_orderOf_eq_one (e a₀)
  exact i167COrth_type_of_dim hQ hp hp2 hpq (m := 4) (by omega) (by omega)
    (CFSG.LocalAnalysis.GLTheoremA.I114.isElemAbelian_zpowers p hgpow)
    (Subgroup.mem_zpowers _) hg hdimW

end Model

end CFSG.LocalAnalysis.GLTheoremA.I167

end
