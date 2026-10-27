module

public import CFSG.Assembly.OddCoreEliminationStatements
import CFSG.Assembly.OddCoreElimination.IsolatedFour
import CFSG.LocalAnalysis.RankTwoShapes.AlperinFusion
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.Helpers

public section

namespace CFSG.Assembly.Dichotomy

variable {G : Type*} [Group G] [Finite G]

private theorem exists_mem_conj_mem_of_coprime_relIndex {p : ℕ} [Fact p.Prime]
    {R A B : Subgroup G} (hAp : IsPGroup p A) (hA : Nat.Coprime p (A.relIndex R))
    (hBR : B ≤ R) (hBp : IsPGroup p B) :
    ∃ r ∈ R, ∀ y ∈ B, r⁻¹ * y * r ∈ A := by
  let SA : Sylow p R := (hAp.comap_subtype (K := R)).toSylow
    ((Nat.Prime.coprime_iff_not_dvd Fact.out).1 hA)
  obtain ⟨X, hX⟩ := (hBp.comap_subtype (K := R)).exists_le_sylow
  obtain ⟨r, hr⟩ := MulAction.exists_smul_eq R X SA
  refine ⟨((r⁻¹ : R) : G), (r⁻¹ : R).2, fun y hy => ?_⟩
  have hmem : MulAut.conj r • (⟨y, hBR hy⟩ : R) ∈ ((r • X : Sylow p R) : Subgroup R) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _
      (hX (show (⟨y, hBR hy⟩ : R) ∈ B.comap R.subtype from hy))
  rw [hr] at hmem
  have hA' : ((MulAut.conj r • (⟨y, hBR hy⟩ : R) : R) : G) ∈ A := hmem
  simpa [MulAut.smul_def, MulAut.conj_apply] using hA'

private theorem normalizer_le_of_centralizer_le {S U M D : Subgroup G} {z : G}
    (hS : IsPGroup 2 S) (hrank : 3 ≤ pRank 2 S) (hUS : U ≤ S)
    (hSU : S ≤ Subgroup.normalizer (U : Set G)) (hU : IsElemAbelian 2 U) (hU4 : Nat.card U = 4)
    (hz : z ∈ U ⊓ subgroupCenter S) (hz2 : orderOf z = 2)
    (hzM : Subgroup.centralizer ({z} : Set G) ≤ M)
    (hfour : ∀ V : Subgroup G, V ≤ S → IsElemAbelian 2 V → Nat.card V = 4 →
      3 ≤ pRank 2 (S ⊓ Subgroup.centralizer (V : Set G)) → Subgroup.normalizer (V : Set G) ≤ M)
    (hhigh : ∀ D : Subgroup G, D ≤ S → 3 ≤ pRank 2 D → Subgroup.normalizer (D : Set G) ≤ M)
    (hDS : D ≤ S) (hcent : Subgroup.centralizer (D : Set G) ⊓ S ≤ D) :
    Subgroup.normalizer (D : Set G) ≤ M := by
  classical
  intro n hn
  have hzS : z ∈ S := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hz).2).1
  have hzCS : z ∈ Subgroup.centralizer (S : Set G) :=
    (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hz).2).2
  have hzCD : z ∈ Subgroup.centralizer (D : Set G) := Subgroup.centralizer_le hDS hzCS
  have hzD : z ∈ D := hcent (Subgroup.mem_inf.mpr ⟨hzCD, hzS⟩)
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hz2
    exact absurd hz2 (by decide)
  have hzsq : z ^ 2 = 1 := hz2 ▸ pow_orderOf_eq_one z
  have hfix : n * z * n⁻¹ = z → n ∈ M := fun h => hzM
    (Subgroup.mem_centralizer_singleton_iff.mpr (by
      calc n * z = n * z * n⁻¹ * n := by group
        _ = z * n := by rw [h]))
  obtain ⟨V, hVmem⟩ : ∃ V : Subgroup G, ∀ x, x ∈ V ↔
      x ∈ D ∧ x ∈ Subgroup.centralizer (D : Set G) ∧ x ^ 2 = 1 :=
    ⟨{ carrier := {x | x ∈ D ∧ x ∈ Subgroup.centralizer (D : Set G) ∧ x ^ 2 = 1}
       mul_mem' := fun {x y} hx hy => ⟨D.mul_mem hx.1 hy.1, Subgroup.mul_mem _ hx.2.1 hy.2.1, by
         rw [Commute.mul_pow (Subgroup.mem_centralizer_iff.mp hy.2.1 x hx.1), hx.2.2, hy.2.2,
           one_mul]⟩
       one_mem' := ⟨D.one_mem, Subgroup.one_mem _, one_pow 2⟩
       inv_mem' := fun {x} hx => ⟨D.inv_mem hx.1, Subgroup.inv_mem _ hx.2.1, by
         rw [inv_pow, hx.2.2, inv_one]⟩ }, fun _ => Iff.rfl⟩
  have hVD : V ≤ D := fun x hx => ((hVmem x).mp hx).1
  have hVC : V ≤ Subgroup.centralizer (D : Set G) := fun x hx => ((hVmem x).mp hx).2.1
  have hV : IsElemAbelian 2 V := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ((hVmem x).mp hx).2.2⟩
    exact Subgroup.mem_centralizer_iff.mp (hVC b.2) a (hVD a.2)
  have hzV : z ∈ V := (hVmem z).mpr ⟨hzD, hzCD, hzsq⟩
  have hconj : ∀ m ∈ Subgroup.normalizer (D : Set G), ∀ x ∈ V, m * x * m⁻¹ ∈ V := by
    intro m hm x hx
    obtain ⟨hxD, hxC, hx2⟩ := (hVmem x).mp hx
    refine (hVmem _).mpr ⟨(Subgroup.mem_normalizer_iff.mp hm x).mp hxD, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro d hd
      have hcomm := Subgroup.mem_centralizer_iff.mp hxC _
        ((Subgroup.mem_normalizer_iff''.mp hm d).mp hd)
      calc d * (m * x * m⁻¹) = m * ((m⁻¹ * d * m) * x) * m⁻¹ := by group
        _ = m * (x * (m⁻¹ * d * m)) * m⁻¹ := by rw [hcomm]
        _ = m * x * m⁻¹ * d := by group
    · rw [conj_pow, hx2, mul_one, mul_inv_cancel]
  have hNV : Subgroup.normalizer (D : Set G) ≤ Subgroup.normalizer (V : Set G) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hconj m hm x, fun hx => ?_⟩
    have h := hconj m⁻¹ (inv_mem hm) _ hx
    rwa [show m⁻¹ * (m * x * m⁻¹) * m⁻¹⁻¹ = x by group] at h
  obtain ⟨k, hk⟩ := (CFSG.RankThreeCoreUniqueness.Helpers.elementary_isPGroup 2 V hV).exists_card_eq
  rcases Nat.lt_or_ge k 3 with hk3 | hk3
  swap
  ·
    exact hhigh D hDS (hk3.trans (le_csSup
      (CFSG.RankThreeCoreUniqueness.Helpers.pRank_set_bddAbove 2 (by decide) D)
      ⟨V, hVD, hV, hk⟩)) hn
  interval_cases k
  ·
    have hbot : V = ⊥ := Subgroup.card_eq_one.mp (by simpa using hk)
    rw [hbot] at hzV
    exact absurd (Subgroup.mem_bot.mp hzV) hz1
  ·
    obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : V)).mp (by simpa using hk)
    have h1 := hy ⟨z, hzV⟩ fun h => hz1 (congrArg Subtype.val h)
    have h2 := hy ⟨n * z * n⁻¹, hconj n hn z hzV⟩ fun h =>
      hz1 (conj_eq_one_iff.mp (congrArg Subtype.val h))
    exact hfix (congrArg Subtype.val (h2.trans h1.symm))
  have hV4 : Nat.card V = 4 := by rw [hk]; norm_num
  have hVS : V ≤ S := hVD.trans hDS
  by_cases hiso : 3 ≤ pRank 2 (S ⊓ Subgroup.centralizer (V : Set G))
  · exact hfour V hVS hV hV4 hiso (hNV hn)
  have hVself : V ≤ S ⊓ Subgroup.centralizer (V : Set G) := by
    refine le_inf hVS fun x hx => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_iff.mp (hVC hx) y (hVD hy)
  have hrank2 : pRank 2 (S ⊓ Subgroup.centralizer (V : Set G)) = 2 := by
    have hge : 2 ≤ pRank 2 (S ⊓ Subgroup.centralizer (V : Set G)) :=
      le_csSup (CFSG.RankThreeCoreUniqueness.Helpers.pRank_set_bddAbove 2 (by decide) _)
        ⟨V, hVself, hV, hk⟩
    omega
  obtain ⟨-, hVS₀, z₀, hz₀, hVS₀eq, h1z, hstruct⟩ :=
    isolated_four_centralizer_structure hS hrank hUS hSU hU hU4 hVS hV hV4 hrank2
  obtain ⟨v, hvV, hvS₀⟩ := IsConcreteLE.not_le_iff_exists.mp hVS₀
  obtain ⟨-, hCV, -, -, hsplit, hR4, hRinv, -⟩ := hstruct v hvV hvS₀ _ rfl
  set R := S ⊓ Subgroup.centralizer (U : Set G) ⊓ Subgroup.centralizer ({v} : Set G) with hR
  have hzCU : z ∈ Subgroup.centralizer (U : Set G) := Subgroup.centralizer_le hUS hzCS
  have hzz₀ : z = z₀ :=
    (h1z z (Subgroup.mem_inf.mpr ⟨hzV, Subgroup.mem_inf.mpr ⟨hzS, hzCU⟩⟩)).resolve_left hz1
  have hRz : ∀ x ∈ R, orderOf x = 2 → x = z := fun x hx hx2 => (hRinv x hx hx2).trans hzz₀.symm
  have hDCv : D ≤ S ⊓ Subgroup.centralizer ({v} : Set G) := by
    rw [← hCV]
    refine le_inf hDS fun d hd => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp (hVC hx) d hd).symm
  have hvsq : v ^ 2 = 1 := hV.2 v hvV
  have hvx : ∀ x ∈ S ⊓ Subgroup.centralizer ({v} : Set G), (v * x) ^ 2 = x ^ 2 := by
    intro x hx
    have hxv : x * v = v * x :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hx).2
    calc (v * x) ^ 2 = v * (x * v) * x := by rw [sq]; group
      _ = v * (v * x) * x := by rw [hxv]
      _ = v * v * (x * x) := by group
      _ = x ^ 2 := by rw [← sq v, hvsq, one_mul, sq]
  have hsq : ∀ x ∈ S ⊓ Subgroup.centralizer ({v} : Set G), x ^ 2 ∈ R := by
    intro x hx
    rcases hsplit x hx with hxR | hvxR
    · exact R.pow_mem hxR 2
    · exact hvx x hx ▸ R.pow_mem hvxR 2
  have hinvV : ∀ x ∈ S ⊓ Subgroup.centralizer ({v} : Set G), x ^ 2 = 1 → x ∈ V := by
    have hRV : ∀ y ∈ R, y ^ 2 = 1 → y ∈ V := by
      intro y hyR hy2
      by_cases hy1 : y = 1
      · rw [hy1]
        exact V.one_mem
      · rw [hRz y hyR (orderOf_eq_prime hy2 hy1)]
        exact hzV
    intro x hx hx2
    rcases hsplit x hx with hxR | hvxR
    · exact hRV x hxR hx2
    · have hmem := hRV _ hvxR ((hvx x hx).trans hx2)
      rw [show x = v⁻¹ * (v * x) by group]
      exact V.mul_mem (V.inv_mem hvV) hmem
  obtain ⟨d, hdD, hd2⟩ : ∃ d ∈ D, d ^ 2 ≠ 1 := by
    refine by_contra fun hall => ?_
    have hDV : D ≤ V := fun d hd =>
      hinvV d (hDCv hd) (by_contra fun h => hall ⟨d, hd, h⟩)
    have hRv : R ≤ S ⊓ Subgroup.centralizer ({v} : Set G) :=
      le_inf (inf_le_left.trans inf_le_left) inf_le_right
    have hRD : R ≤ D := by
      intro r hr
      have hrv := hRv hr
      rw [← hCV] at hrv
      exact hcent (Subgroup.mem_inf.mpr
        ⟨Subgroup.centralizer_le hDV (Subgroup.mem_inf.mp hrv).2, (Subgroup.mem_inf.mp hrv).1⟩)
    have hRle : R ≤ V ⊓ (S ⊓ Subgroup.centralizer (U : Set G)) :=
      le_inf (hRD.trans hDV) inf_le_left
    rw [hVS₀eq] at hRle
    have hcard := Subgroup.card_le_of_le hRle
    rw [Nat.card_zpowers, hz₀] at hcard
    omega
  obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp hS) ⟨d, hDS hdD⟩
  have hm' : orderOf d = 2 ^ m := (Subgroup.orderOf_coe _).trans hm
  obtain ⟨-, he⟩ := two_le_and_orderOf_sq_pow_eq_two hm' hd2
  set e := d ^ 2 ^ (m - 2) with he_def
  have heD : e ∈ D := D.pow_mem hdD _
  have hez : e ^ 2 = z := hRz _ (hsq e (hDCv heD)) he
  have hne : n * e * n⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp hn e).mp heD
  have hnz : n * z * n⁻¹ = (n * e * n⁻¹) ^ 2 := by rw [conj_pow, hez]
  apply hfix
  rw [hnz]
  apply hRz _ (hsq _ (hDCv hne))
  rw [← hnz]
  exact (MulEquiv.orderOf_eq (MulAut.conj n) z).trans hz2

theorem fusionControl : FusionControlStatement := by
  intro G _ _ S hrank U hUS hSU hU hU4 z hz hz2 M hSM hzM hfour hhigh P hPM hP g hPg
  have hcentric (D : Subgroup G) (hDS : D ≤ S)
      (hcent : Subgroup.centralizer (D : Set G) ⊓ S ≤ D) :
      Subgroup.normalizer (D : Set G) ≤ M :=
    normalizer_le_of_centralizer_le S.isPGroup' hrank hUS hSU hU hU4 hz hz2 hzM hfour hhigh hDS
      hcent
  have hdecomp {Q : Subgroup G} {c : G}
      (h : CFSG.RankTwoShapes.AlperinDecomposition 2 (S : Subgroup G) Q c) : c ∈ M := by
    induction h with
    | one => exact M.one_mem
    | step _ hQ _ hn ih => exact M.mul_mem ih (hcentric _ hQ.1 hQ.2.2.1 hn)
  have hSfus (Q : Subgroup G) (hQS : Q ≤ S) (c : G)
      (hQc : Q.map (MulAut.conj c⁻¹).toMonoidHom ≤ S) :
      ∃ m ∈ M, ∀ x ∈ Q, c⁻¹ * x * c = m⁻¹ * x * m := by
    obtain ⟨d, hd, hdc⟩ := CFSG.RankTwoShapes.alperin_centric_radical_fusion S hQS hQc
    exact ⟨d, hdecomp hd, fun x hx => (hdc x hx).symm⟩
  have hcop : Nat.Coprime 2 ((S : Subgroup G).relIndex M) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 fun h =>
      S.not_dvd_index (h.trans (Subgroup.relIndex_dvd_index_of_le hSM))
  obtain ⟨a, haM, ha⟩ := exists_mem_conj_mem_of_coprime_relIndex S.isPGroup' hcop hPM hP
  obtain ⟨b, hbM, hb⟩ :=
    exists_mem_conj_mem_of_coprime_relIndex S.isPGroup' hcop hPg (hP.map _)
  have hPa : P.map (MulAut.conj a⁻¹).toMonoidHom ≤ S := by
    rintro _ ⟨x, hx, rfl⟩
    simpa [MulAut.conj_apply] using ha x hx
  have hPab : (P.map (MulAut.conj a⁻¹).toMonoidHom).map
      (MulAut.conj (a⁻¹ * g * b)⁻¹).toMonoidHom ≤ S := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    have h := hb (g⁻¹ * x * g) ⟨x, hx, by simp⟩
    have heq : (MulAut.conj (a⁻¹ * g * b)⁻¹).toMonoidHom ((MulAut.conj a⁻¹).toMonoidHom x) =
        b⁻¹ * (g⁻¹ * x * g) * b := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [heq]
    exact h
  obtain ⟨m, hmM, hm⟩ := hSfus _ hPa (a⁻¹ * g * b) hPab
  refine ⟨a * m * b⁻¹, M.mul_mem (M.mul_mem haM hmM) (M.inv_mem hbM), fun x hx => ?_⟩
  have h := hm (a⁻¹ * x * a) ⟨x, hx, by simp⟩
  calc g⁻¹ * x * g = b * ((a⁻¹ * g * b)⁻¹ * (a⁻¹ * x * a) * (a⁻¹ * g * b)) * b⁻¹ := by group
    _ = b * (m⁻¹ * (a⁻¹ * x * a) * m) * b⁻¹ := by rw [h]
    _ = (a * m * b⁻¹)⁻¹ * x * (a * m * b⁻¹) := by group

end CFSG.Assembly.Dichotomy
