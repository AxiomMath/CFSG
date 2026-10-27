module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupSz32
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.SecondPointSz32
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.TypeIILemma45Gen
import CFSG.LocalAnalysis.RankThreeTheoremC.ObstructionElements
import CFSG.HardMathSupport.Timmesfeld.Proving.PRankCore
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Foundations
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Abstract
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.PointConfig
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.TypeIICommon
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.PSU3.Aut
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (u3T)

variable {G : Type} [Group G] [Finite G] {P : Sylow 5 G} {M : Subgroup G} {x : G} {J : Subgroup G}

theorem szz_gen_of_mem {H : Type*} [Group H] {e y : H} (he : orderOf e = 5) (hy : y ∈ zpowers e)
    (hy1 : y ≠ 1) : zpowers e ≤ zpowers y := by
  have h5 : y ^ 5 = 1 := by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← he, pow_orderOf_eq_one,
      one_zpow]
  have hord : orderOf y = 5 :=
    ((Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp (orderOf_dvd_of_pow_eq_one h5)).resolve_left
      (fun h => hy1 (orderOf_eq_one_iff.mp h))
  have hle : zpowers y ≤ zpowers e := zpowers_le.mpr hy
  haveI : Finite (zpowers e) :=
    Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, he]; norm_num)
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, he, hord])).ge

theorem szz_swap_le {H : Type*} [Group H] {A B L : Subgroup H} {g : H}
    (hg : A.map (MulAut.conj g).toMonoidHom = B) (hgL : g ∈ normalizer (L : Set H)) (hA : A ≤ L) :
    B ≤ L := by
  have h : L.map (MulAut.conj g).toMonoidHom = L := mem_normalizer_iff_map_conj_eq.mp hgL
  rw [← hg]
  calc A.map (MulAut.conj g).toMonoidHom ≤ L.map (MulAut.conj g).toMonoidHom := Subgroup.map_mono hA
    _ = L := h

theorem szz_mem_sup_of_commute {H : Type*} [Group H] {A B : Subgroup H}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {s : H} (hs : s ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, s = a * b := by
  have hr := MonoidHom.noncommCoprod_range A.subtype B.subtype (fun a b => h a a.2 b b.2)
  rw [Subgroup.range_subtype, Subgroup.range_subtype] at hr
  rw [← hr] at hs
  obtain ⟨⟨a, b⟩, rfl⟩ := hs
  exact ⟨a, a.2, b, b.2, rfl⟩

theorem szz_irr {H : Type*} [Group H] {e x m g : H} {L : Subgroup H}
    (he : orderOf e = 5) (hx : orderOf x = 5) (hex : e * x = x * e)
    (hme : m * e * m⁻¹ = e ^ 2) (hmx : m * x * m⁻¹ = x)
    (hgx : (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers e)
    (hge : (zpowers e).map (MulAut.conj g).toMonoidHom = zpowers x)
    (hLZ : L ≤ zpowers e ⊔ zpowers x)
    (hmL : m ∈ normalizer (L : Set H)) (hgL : g ∈ normalizer (L : Set H)) :
    L = ⊥ ∨ L = zpowers e ⊔ zpowers x := by
  rcases L.bot_or_exists_ne_one with hL | ⟨z, hzL, hz1⟩
  · exact Or.inl hL
  right
  have hcomm : ∀ u ∈ zpowers e, ∀ v ∈ zpowers x, u * v = v * u := by
    intro u hu v hv
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hu
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hv
    exact ((Commute.zpow_zpow (show Commute e x from hex) i j)).eq
  obtain ⟨u, hu, v, hv, rfl⟩ := szz_mem_sup_of_commute hcomm (hLZ hzL)
  have hmu : m * u * m⁻¹ = u ^ 2 := by
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hu
    rw [← conj_zpow, hme, ← zpow_natCast e 2, ← zpow_natCast (e ^ i) 2, ← zpow_mul, ← zpow_mul,
      mul_comm]
  have hmv : m * v * m⁻¹ = v := by
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hv
    rw [← conj_zpow, hmx]
  have huL : u ∈ L := by
    have h1 : m * (u * v) * m⁻¹ ∈ L := (mem_normalizer_iff.mp hmL _).mp hzL
    have h2 : (m * (u * v) * m⁻¹) * (u * v)⁻¹ = u := by
      have : m * (u * v) * m⁻¹ = (m * u * m⁻¹) * (m * v * m⁻¹) := by group
      rw [this, hmu, hmv]
      group
    rw [← h2]
    exact L.mul_mem h1 (L.inv_mem hzL)
  by_cases hu1 : u = 1
  ·
    subst hu1
    have hv1 : v ≠ 1 := by simpa using hz1
    have hvL : v ∈ L := by simpa using hzL
    have hB : zpowers x ≤ L := (szz_gen_of_mem hx hv hv1).trans (zpowers_le.mpr hvL)
    exact le_antisymm hLZ (sup_le (szz_swap_le hgx hgL hB) hB)
  · have hA : zpowers e ≤ L := (szz_gen_of_mem he hu hu1).trans (zpowers_le.mpr huL)
    exact le_antisymm hLZ (sup_le hA (szz_swap_le hge hgL hA))

theorem szz_map_conj_mul {H : Type*} [Group H] (A : Subgroup H) (h g : H) :
    (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj h).toMonoidHom =
      A.map (MulAut.conj (h * g)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext z
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

theorem szz_map_conj_inj {H : Type*} [Group H] {A B : Subgroup H} (g : H)
    (h : A.map (MulAut.conj g).toMonoidHom = B.map (MulAut.conj g).toMonoidHom) : A = B :=
  Subgroup.map_injective (MulAut.conj g).injective h

theorem szz_swap_back {H : Type*} [Group H] {P A B : Subgroup H} (hAB : A ≠ B) (hBP : B ≤ P)
    (hlines : ∀ g : H, A.map (MulAut.conj g).toMonoidHom ≤ P →
      A.map (MulAut.conj g).toMonoidHom = A ∨ A.map (MulAut.conj g).toMonoidHom = B)
    {g : H} (hgP : g ∈ normalizer (P : Set H)) (hgA : A.map (MulAut.conj g).toMonoidHom = B) :
    B.map (MulAut.conj g).toMonoidHom = A := by
  have hPg : P.map (MulAut.conj g).toMonoidHom = P := mem_normalizer_iff_map_conj_eq.mp hgP
  have h1 : B.map (MulAut.conj g).toMonoidHom ≤ P :=
    calc B.map (MulAut.conj g).toMonoidHom ≤ P.map (MulAut.conj g).toMonoidHom :=
          Subgroup.map_mono hBP
      _ = P := hPg
  have h2 := hlines (g * g) (by rw [← szz_map_conj_mul, hgA]; exact h1)
  rw [← szz_map_conj_mul, hgA] at h2
  rcases h2 with h2 | h2
  · exact h2
  · exact absurd (szz_map_conj_inj g (hgA.trans h2.symm)) hAB

theorem szz_wc_abs {H : Type*} [Group H] {P A B : Subgroup H} (hAB : A ≠ B) (hBP : B ≤ P)
    (hlines : ∀ g : H, A.map (MulAut.conj g).toMonoidHom ≤ P →
      A.map (MulAut.conj g).toMonoidHom = A ∨ A.map (MulAut.conj g).toMonoidHom = B)
    (hswap : ∃ g ∈ normalizer (P : Set H), A.map (MulAut.conj g).toMonoidHom = B) :
    ∀ h : H, (B ⊔ A).map (MulAut.conj h).toMonoidHom ≤ P →
      (B ⊔ A).map (MulAut.conj h).toMonoidHom = B ⊔ A := by
  obtain ⟨g, hgP, hgA⟩ := hswap
  have hBg := szz_swap_back hAB hBP hlines hgP hgA
  intro h hh
  have hAh : A.map (MulAut.conj h).toMonoidHom ≤ P :=
    (Subgroup.map_mono le_sup_right).trans hh
  have hBh : B.map (MulAut.conj h).toMonoidHom ≤ P :=
    (Subgroup.map_mono le_sup_left).trans hh
  have hne : A.map (MulAut.conj h).toMonoidHom ≠ B.map (MulAut.conj h).toMonoidHom :=
    fun h' => hAB (szz_map_conj_inj h h')
  have h1 := hlines h hAh
  have h2 := hlines (h * g) (by rw [← szz_map_conj_mul, hgA]; exact hBh)
  rw [← szz_map_conj_mul, hgA] at h2
  rw [Subgroup.map_sup]
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact absurd (h1.trans h2.symm) hne
  · rw [h1, h2]
  · rw [h1, h2, sup_comm]
  · exact absurd (h1.trans h2.symm) hne

theorem szz_swap_norm {H : Type*} [Group H] {A B : Subgroup H} {g : H}
    (hgA : A.map (MulAut.conj g).toMonoidHom = B) (hgB : B.map (MulAut.conj g).toMonoidHom = A) :
    g ∈ normalizer ((A ⊔ B : Subgroup H) : Set H) := by
  rw [mem_normalizer_iff_map_conj_eq]
  show (A ⊔ B).map (MulAut.conj g).toMonoidHom = A ⊔ B
  rw [Subgroup.map_sup, hgA, hgB, sup_comm]

theorem szz_torus_norm {H : Type*} [Group H] [Finite H] {e x m : H}
    (hme : m * e * m⁻¹ = e ^ 2) (hmx : m * x * m⁻¹ = x) :
    m ∈ normalizer ((zpowers e ⊔ zpowers x : Subgroup H) : Set H) := by
  have hle : (zpowers e ⊔ zpowers x).map (MulAut.conj m).toMonoidHom ≤ zpowers e ⊔ zpowers x := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    refine sup_le_sup ?_ ?_
    · have h : (MulAut.conj m).toMonoidHom e = e ^ 2 := by
        simpa [MulAut.conj_apply] using hme
      rw [h]
      exact zpowers_le.mpr (pow_mem (mem_zpowers e) 2)
    · have h : (MulAut.conj m).toMonoidHom x = x := by
        simpa [MulAut.conj_apply] using hmx
      rw [h]
  rw [mem_normalizer_iff_map_conj_eq]
  exact Subgroup.eq_of_le_of_card_ge hle
    (by rw [Subgroup.card_map_of_injective (MulAut.conj m).injective])

theorem szz_Z_eq {a c y : G} (hP : Sz32Struct P x J a c y) :
    zpowers (a ^ 5) ⊔ zpowers x = sz32Z a c := by
  rw [hP.facts.x_eq]
  rfl

theorem szz_ord_e {a c y : G} (hP : Sz32Struct P x J a c y) : orderOf (a ^ 5) = 5 := by
  rw [orderOf_pow_of_dvd (by norm_num) (by rw [hP.pres_P.ord_a]; norm_num), hP.pres_P.ord_a]

theorem szz_lines_ne {a c y : G} (hP : Sz32Struct P x J a c y) : zpowers x ≠ zpowers (a ^ 5) := by
  intro h
  have h1 := hP.facts.Z_card
  have h2 : sz32Z a c = zpowers (a ^ 5) := by
    rw [← szz_Z_eq hP, ← h, sup_idem]
  rw [h2, Nat.card_zpowers, szz_ord_e hP] at h1
  norm_num at h1

theorem szz_e_mem {a c y : G} (hP : Sz32Struct P x J a c y) : a ^ 5 ∈ (P : Subgroup G) :=
  (P : Subgroup G).pow_mem hP.pres_P.a_mem 5

theorem szz_x_mem {a c y : G} (hP : Sz32Struct P x J a c y) : x ∈ (P : Subgroup G) :=
  (zpowers_le.mpr hP.pres_P.c_mem) hP.pres_P.x_mem

theorem szz_Z_le_P {a c y : G} (hP : Sz32Struct P x J a c y) :
    zpowers (a ^ 5) ⊔ zpowers x ≤ (P : Subgroup G) :=
  sup_le (zpowers_le.mpr (szz_e_mem hP)) (zpowers_le.mpr (szz_x_mem hP))

theorem szz_comm {a c y : G} (hP : Sz32Struct P x J a c y) : a ^ 5 * x = x * a ^ 5 := by
  have hpres := hP.pres_P
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hpres.x_mem
  have hax : Commute a x := by
    rw [← hk]
    exact Commute.zpow_right (show Commute a c from hpres.ac) k
  exact (hax.pow_left 5).eq

theorem szz_wc {a c y : G} (hP : Sz32Struct P x J a c y) (hL : Sz32Lines P x (a ^ 5)) :
    ∀ h : G, (zpowers (a ^ 5) ⊔ zpowers x).map (MulAut.conj h).toMonoidHom ≤ (P : Subgroup G) →
      (zpowers (a ^ 5) ⊔ zpowers x).map (MulAut.conj h).toMonoidHom = zpowers (a ^ 5) ⊔ zpowers x :=
  szz_wc_abs (szz_lines_ne hP) (zpowers_le.mpr (szz_e_mem hP)) hL.lines hL.swap

theorem szz_NZ_le (hS : Setting G) (hU0 : FullCoreLocal G) (hc : PointConfig IsSz32Type G 5 P M x J)
    {a c y : G} (hP : Sz32Struct P x J a c y) :
    normalizer ((zpowers (a ^ 5) ⊔ zpowers x : Subgroup G) : Set G) ≤ M := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hZP := szz_Z_le_P hP
  have hPM : (P : Subgroup G) ≤ M := (sylow_le_of_isCoreMaxLocal hS hc.sigma hc.core).1
  have hZe := hP.facts.Z_elem
  have hZc := hP.facts.Z_card
  rw [← szz_Z_eq hP] at hZe hZc
  have h2 : 2 ≤ CFSG.Open.pRank 5 (zpowers (a ^ 5) ⊔ zpowers x : Subgroup G) :=
    CFSG.HardMathSupport.Timmesfeld.Proving.le_pRank_of_elemAbelian_card (by norm_num) le_rfl hZe
      hZc
  exact normalizer_le_of_le_of_two_le_pRank hS hU0 hc.sigma hc.core (P.isPGroup'.to_le hZP)
    (hZP.trans hPM) h2

theorem szz_exists_m (hSz' : Sz32OpenFacts) (hc : PointConfig IsSz32Type G 5 P M x J) {a c y : G}
    (hP : Sz32Struct P x J a c y) : ∃ m ∈ J, m * a ^ 5 * m⁻¹ = (a ^ 5) ^ 2 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hA := hP.decomp
  obtain ⟨Q, _, ψ, hψ, hker, hQ⟩ := hc.typ
  haveI : Finite Q := Finite.of_surjective _ hψ
  obtain ⟨Tsyl, hTsyl, hTinj⟩ := sps_sylow_data hc.generic hc.le_cent hc.cent_le ψ hker
  obtain ⟨Tb, hTb⟩ : ∃ Tb : Sylow 5 Q, (Tb : Subgroup Q) = (Tsyl : Subgroup ↥J).map ψ :=
    ⟨Tsyl.mapSurjective hψ, Sylow.coe_mapSurjective hψ Tsyl⟩
  have haT : a ∈ u3T P x J := hA.T_eq ▸ Subgroup.mem_zpowers a
  have heaT : a ^ 5 ∈ u3T P x J := (u3T P x J).pow_mem haT 5
  obtain ⟨ea, hea⟩ : ∃ ea : ↥J, (ea : G) = a ^ 5 := ⟨⟨a ^ 5, J.pow_mem hA.a_J 5⟩, rfl⟩
  have heaTsyl : ea ∈ (Tsyl : Subgroup ↥J) := by
    rw [hTsyl, Subgroup.mem_subgroupOf, hea]
    exact heaT
  have hea2Tsyl : ea ^ 2 ∈ (Tsyl : Subgroup ↥J) := (Tsyl : Subgroup ↥J).pow_mem heaTsyl 2
  have hfinj : Function.Injective (ψ.comp (Tsyl : Subgroup ↥J).subtype) :=
    (injective_iff_map_eq_one _).mpr fun t ht => Subtype.ext (hTinj t t.2 ht)
  have hordψ : ∀ t : ↥J, t ∈ (Tsyl : Subgroup ↥J) → orderOf (ψ t) = orderOf t := by
    intro t ht
    have h := orderOf_injective (ψ.comp (Tsyl : Subgroup ↥J).subtype) hfinj ⟨t, ht⟩
    simpa [Subgroup.orderOf_mk] using h
  have hordea : orderOf ea = 5 := by
    rw [← Subgroup.orderOf_coe, hea]
    exact szz_ord_e hP
  have hordea2 : orderOf (ea ^ 2) = 5 := by
    rw [orderOf_pow' _ (by norm_num), hordea]
    norm_num
  obtain ⟨nb, hnb, hnbe⟩ := hSz'.transOmega Q hQ Tb (ψ ea)
    (by rw [hTb]; exact Subgroup.mem_map_of_mem ψ heaTsyl) (by rw [hordψ ea heaTsyl, hordea])
    (ψ (ea ^ 2)) (by rw [hTb]; exact Subgroup.mem_map_of_mem ψ hea2Tsyl)
    (by rw [hordψ _ hea2Tsyl, hordea2])
  obtain ⟨n₀, hn₀⟩ := hψ nb
  have hkcop : Nat.Coprime 5 (Nat.card ψ.ker) := by
    rw [hker]
    have hOJ : rankThreePrimeCore 5 J ≤ J := CFSG.AGLEmbedding.glbPrimeCore_le 5 J
    have h : Nat.card ((rankThreePrimeCore 5 J).subgroupOf J) = Nat.card (rankThreePrimeCore 5 J) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOJ).toEquiv
    rw [h]
    exact CFSG.AGLEmbedding.glbPrimeCore_coprime 5 J
  have hnorm : ψ n₀ ∈ Subgroup.normalizer (((Tsyl : Subgroup ↥J).map ψ : Subgroup Q) : Set Q) := by
    rw [hn₀, ← hTb]
    exact hnb
  obtain ⟨n, hn, hψn⟩ := typeII_frattini_ker ψ hkcop Tsyl.isPGroup' hnorm
  have hnea : n * ea * n⁻¹ ∈ (Tsyl : Subgroup ↥J) :=
    (Subgroup.mem_normalizer_iff.mp hn ea).mp heaTsyl
  have hψeq : ψ (n * ea * n⁻¹) = ψ (ea ^ 2) := by
    rw [map_mul, map_mul, map_inv, hψn, hn₀]
    exact hnbe
  have heq : n * ea * n⁻¹ = ea ^ 2 := by
    have hmem : (n * ea * n⁻¹) * (ea ^ 2)⁻¹ ∈ (Tsyl : Subgroup ↥J) :=
      (Tsyl : Subgroup ↥J).mul_mem hnea ((Tsyl : Subgroup ↥J).inv_mem hea2Tsyl)
    have h1 : ψ ((n * ea * n⁻¹) * (ea ^ 2)⁻¹) = 1 := by
      rw [map_mul, map_inv, hψeq, mul_inv_cancel]
    exact mul_inv_eq_one.mp (hTinj _ hmem h1)
  refine ⟨(n : G), n.2, ?_⟩
  have h := congrArg Subtype.val heq
  simpa [hea] using h

theorem szz_Z_irr (hSz' : Sz32OpenFacts) (hc : PointConfig IsSz32Type G 5 P M x J) {a c y : G}
    (hP : Sz32Struct P x J a c y) (hL : Sz32Lines P x (a ^ 5)) :
    ∀ L : Subgroup G, L ≤ zpowers (a ^ 5) ⊔ zpowers x →
      normalizer ((zpowers (a ^ 5) ⊔ zpowers x : Subgroup G) : Set G) ≤ normalizer (L : Set G) →
      L = ⊥ ∨ L = zpowers (a ^ 5) ⊔ zpowers x := by
  intro L hLZ hN
  obtain ⟨m, hmJ, hme⟩ := szz_exists_m hSz' hc hP
  obtain ⟨g, hgP, hgx⟩ := hL.swap
  have hge : (zpowers (a ^ 5)).map (MulAut.conj g).toMonoidHom = zpowers x :=
    szz_swap_back (szz_lines_ne hP) (zpowers_le.mpr (szz_e_mem hP)) hL.lines hgP hgx
  have hcomm : Commute m x := Subgroup.mem_centralizer_singleton_iff.mp (hc.le_cent hmJ)
  have hmx : m * x * m⁻¹ = x := mul_inv_eq_iff_eq_mul.mpr hcomm.eq
  exact szz_irr (szz_ord_e hP) hP.pres_P.x_ord (szz_comm hP) hme hmx hgx hge hLZ
    (hN (szz_torus_norm hme hmx)) (hN (szz_swap_norm hge hgx))

theorem sz32_Z_facts' (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G)
    (hSz : Sz32Facts) (hSz' : Sz32OpenFacts) (hc : PointConfig IsSz32Type G 5 P M x J) {a c y : G}
    (hP : Sz32Struct P x J a c y) (hL : Sz32Lines P x (a ^ 5)) : Sz32ZFacts P M x (a ^ 5) :=
  ⟨szz_NZ_le hS hU0 hc hP, szz_wc hP hL, szz_Z_irr hSz' hc hP hL⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
