module

public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscapeAux
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNFGroup
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeInner
import CFSG.Assembly.ComponentTypeDefs
import CFSG.Assembly.RankThreeEvenDefs
import CFSG.LocalAnalysis.AGLEmbedding.ResidualFiveOddCore

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}

abbrev mbar (M : Subgroup G) (x : G) (hx : x ∈ M) : ↥M ⧸ CFSG.pCore 2 ↥M :=
  QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨x, hx⟩

omit [Finite G] in
theorem mbar_mul {x y : G} (hx : x ∈ M) (hy : y ∈ M) :
    mbar M (x * y) (M.mul_mem hx hy) = mbar M x hx * mbar M y hy := by
  rw [mbar, mbar, mbar, ← map_mul]; rfl

omit [Finite G] in
theorem mbar_inv {x : G} (hx : x ∈ M) : mbar M x⁻¹ (M.inv_mem hx) = (mbar M x hx)⁻¹ := by
  rw [mbar, mbar, ← map_inv]; rfl

omit [Finite G] in
theorem mbar_zpow {x : G} (hx : x ∈ M) (n : ℤ) :
    mbar M (x ^ n) (M.zpow_mem hx n) = (mbar M x hx) ^ n := by
  rw [mbar, mbar, ← map_zpow]; rfl

omit [Finite G] in
theorem mbar_pow {x : G} (hx : x ∈ M) (n : ℕ) :
    mbar M (x ^ n) (M.pow_mem hx n) = (mbar M x hx) ^ n := by
  rw [mbar, mbar, ← map_pow]; rfl

omit [Finite G] in
theorem mbar_conj {x y : G} (hx : x ∈ M) (hy : y ∈ M) :
    mbar M (y * x * y⁻¹) (M.mul_mem (M.mul_mem hy hx) (M.inv_mem hy)) =
      mbar M y hy * mbar M x hx * (mbar M y hy)⁻¹ := by
  rw [mbar, mbar, mbar, ← map_inv, ← map_mul, ← map_mul]; rfl

omit [Finite G] in
theorem mbar_one : mbar M (1 : G) M.one_mem = 1 := by rw [mbar]; exact map_one _

omit [Finite G] in
theorem eq_of_mbar_eq_p (hp : p.Prime) (hp2 : p ≠ 2) (hRM : R ≤ M) (hRp : IsPGroup p R)
    {a b : G} (ha : a ∈ R) (hb : b ∈ R) (hab : mbar M a (hRM ha) = mbar M b (hRM hb)) :
    a = b := by
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ((⟨a, hRM ha⟩ : M)⁻¹ * ⟨b, hRM hb⟩) = 1 := by
    rw [map_mul, map_inv, inv_mul_eq_one]; exact hab
  have h2 := eq_one_of_mem_pCoreOf_two hp hp2 hRp (R.mul_mem (R.inv_mem ha) hb)
    (coe_mem_pCoreOf_two_of_mk_eq_one _ h1)
  exact inv_mul_eq_one.mp h2

omit [Finite G] in
theorem commute_of_mbar_p (hp : p.Prime) (hp2 : p ≠ 2) (hRM : R ≤ M) (hRp : IsPGroup p R)
    {a b : G} (ha : a ∈ R) (hb : b ∈ R)
    (hab : Commute (mbar M a (hRM ha)) (mbar M b (hRM hb))) : a * b = b * a := by
  refine eq_of_mbar_eq_p hp hp2 hRM hRp (R.mul_mem ha hb) (R.mul_mem hb ha) ?_
  rw [mbar_mul (hRM ha) (hRM hb), mbar_mul (hRM hb) (hRM ha)]
  exact hab.eq

omit [Finite G] in
theorem barM_sup {A B : Subgroup G} (hA : A ≤ M) (hB : B ≤ M) :
    barM M (A ⊔ B) = barM M A ⊔ barM M B := by
  rw [barM, barM, barM, Subgroup.subgroupOf_sup hA hB, Subgroup.map_sup]

theorem D1PhaseThree.rep_conj (h : D1PhaseThree p P M H R) {z r g : G} (hzR : z ∈ R)
    (hrR : r ∈ R) (hgR : g ∈ R) (hgz : g * z = z * g) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) (hrL : mbar M r (h.le_M hrR) ∈ barM M L)
    (hrc : (mbar M r (h.le_M hrR))⁻¹ * mbar M z (h.le_M hzR) ∈
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :
    IsWeakSBlock M (pCoreOf 2 H) (L.map (MulAut.conj g).toMonoidHom) ∧
      mbar M (g * r * g⁻¹) (h.le_M (R.mul_mem (R.mul_mem hgR hrR) (R.inv_mem hgR))) ∈
        barM M (L.map (MulAut.conj g).toMonoidHom) ∧
      (mbar M (g * r * g⁻¹) (h.le_M (R.mul_mem (R.mul_mem hgR hrR) (R.inv_mem hgR))))⁻¹ *
          mbar M z (h.le_M hzR) ∈
        Subgroup.centralizer (barM M (L.map (MulAut.conj g).toMonoidHom) :
          Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  have hgM : g ∈ M := h.le_M hgR
  have hgS : g ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    localGroup_le_normalizer_pCoreOf 2 H (h.le_H hgR)
  have hbar : barM M (L.map (MulAut.conj g).toMonoidHom) =
      (barM M L).map (MulAut.conj (mbar M g hgM)).toMonoidHom := barM_map_conj hgM L
  have hzb : mbar M g hgM * mbar M z (h.le_M hzR) * (mbar M g hgM)⁻¹ = mbar M z (h.le_M hzR) := by
    rw [← mbar_conj (h.le_M hzR) hgM]
    congr 1
    rw [hgz, mul_inv_cancel_right]
  refine ⟨hL.map_conj hgM hgS, ?_, ?_⟩
  · rw [hbar, mbar_conj (h.le_M hrR) hgM]
    exact ⟨_, hrL, rfl⟩
  · rw [hbar, mbar_conj (h.le_M hrR) hgM]
    have e : (mbar M g hgM * mbar M r (h.le_M hrR) * (mbar M g hgM)⁻¹)⁻¹ *
        mbar M z (h.le_M hzR) = mbar M g hgM * ((mbar M r (h.le_M hrR))⁻¹ *
          mbar M z (h.le_M hzR)) * (mbar M g hgM)⁻¹ := by
      conv_lhs => rw [← hzb]
      group
    rw [e]
    exact conj_mem_centralizer_map hrc

theorem exists_pElt_of_mem_sup {X : Type*} [Group X] [Finite X] (hp : p.Prime)
    {L : Subgroup X} {u : X} (hu : u ∈ L ⊔ Subgroup.centralizer (L : Set X)) (hup : u ^ p = 1) :
    ∃ l ∈ L, (∃ k : ℕ, l ^ p ^ k = 1) ∧ l⁻¹ * u ∈ Subgroup.centralizer (L : Set X) := by
  have hLC : L ≤ Subgroup.normalizer (Subgroup.centralizer (L : Set X) : Set X) :=
    Subgroup.le_normalizer.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
        (Subgroup.normal_subgroupOf_centralizer_normalizer _))
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hLC] at hu
  obtain ⟨a, ha, c, hc, rfl⟩ := hu
  have hac : Commute a c := Subgroup.mem_centralizer_iff.mp hc a ha
  obtain ⟨n, e, hn, hfix⟩ := exists_pPart_pow hp ((a, c) : X × X)
  have hu' : (a * c) ^ n = a * c := by
    refine hfix (a * c) ?_ ⟨1, by simpa using hup⟩
    have h1 := pow_orderOf_eq_one ((a, c) : X × X)
    rw [Prod.pow_mk, Prod.mk_eq_one] at h1
    rw [hac.mul_pow, h1.1, h1.2, one_mul]
  refine ⟨a ^ n, L.pow_mem ha n, ⟨e, ?_⟩, ?_⟩
  · have := congrArg Prod.fst hn
    simpa [← pow_mul] using this
  · have h2 : (a ^ n)⁻¹ * (a * c) = c ^ n := by
      conv_lhs => rw [← hu', hac.mul_pow]
      group
    rw [h2]
    exact Subgroup.pow_mem _ hc n

theorem exists_rep_mem_R_p (hp : p.Prime) (hp2 : p ≠ 2) {z : G} (hzM : z ∈ M)
    (hzp : z ^ p = 1)
    (hsyl : ∃ S : Sylow p ↥(M ⊓ Subgroup.centralizer ({z} : Set G)),
      (S : Subgroup _).map (M ⊓ Subgroup.centralizer ({z} : Set G)).subtype = R)
    {L : Subgroup G}
    (hin : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩ ∈
      barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :
    ∃ y ∈ M ⊓ Subgroup.centralizer ({z} : Set G), ∃ r ∈ R, ∃ hrM : r ∈ M,
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨r, hrM⟩ ∈
        barM M (L.map (MulAut.conj y).toMonoidHom) ∧
      (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨r, hrM⟩)⁻¹ *
        QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩ ∈
        Subgroup.centralizer (barM M (L.map (MulAut.conj y).toMonoidHom) :
          Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  have : Fact p.Prime := ⟨hp⟩
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set zM : M := ⟨z, hzM⟩ with hzMdef
  set zb := mk zM with hzb
  have hzMp : zM ^ p = 1 := Subtype.ext (by simpa using hzp)
  have hzbp : zb ^ p = 1 := by rw [hzb, ← map_pow, hzMp, map_one]
  obtain ⟨l, hlL, ⟨k, hlk⟩, hlc⟩ := exists_pElt_of_mem_sup hp hin hzbp
  have hcl : l * (l⁻¹ * zb) = (l⁻¹ * zb) * l := Subgroup.mem_centralizer_iff.mp hlc l hlL
  have hlz : l ∈ Subgroup.centralizer ({zb} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc l * zb = l * (l * (l⁻¹ * zb)) := by group
      _ = l * ((l⁻¹ * zb) * l) := by rw [hcl]
      _ = zb * l := by group
  have hcop : Nat.Coprime p (Nat.card (CFSG.pCore 2 ↥M)) := by
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥M))
    rw [hj]
    exact Nat.Coprime.pow_right j ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have hzMp' : IsPGroup p (Subgroup.zpowers zM) :=
    isPGroup_zpowers_of_pow_eq_one (k := 1) (by simpa using hzMp)
  obtain ⟨g, hgC, hgl⟩ := exists_mem_centralizer_mk_eq hp (CFSG.pCore 2 ↥M) hcop hzMp' hlz
  obtain ⟨n, e, hn, hfix⟩ := exists_pPart_pow hp g
  have hl1 : l ^ orderOf g = 1 := by rw [← hgl, ← map_pow, pow_orderOf_eq_one, map_one]
  have hgpl : mk (g ^ n) = l := by rw [map_pow, hgl]; exact hfix l hl1 ⟨k, hlk⟩
  have hgpC : g ^ n ∈ Subgroup.centralizer ({zM} : Set M) := Subgroup.pow_mem _ hgC n
  have hgpK : ((g ^ n : M) : G) ∈ M ⊓ Subgroup.centralizer ({z} : Set G) := by
    refine ⟨(g ^ n).2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have := Subgroup.mem_centralizer_singleton_iff.mp hgpC
    exact congrArg Subtype.val this
  have hgpe : ((g ^ n : M) : G) ^ p ^ e = 1 := by
    have := congrArg Subtype.val hn
    simpa using this
  obtain ⟨S, hS⟩ := hsyl
  obtain ⟨y, hyK, hyR⟩ := exists_conj_mem_map_sylow S hgpK hgpe
  rw [hS] at hyR
  have hyM : y ∈ M := hyK.1
  have hyz : y * z = z * y := Subgroup.mem_centralizer_singleton_iff.mp hyK.2
  set yM : M := ⟨y, hyM⟩ with hyMdef
  set yb := mk yM with hyb
  have hybz : yb * zb = zb * yb := by
    rw [hyb, hzb, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hyz
  refine ⟨y, hyK, y * (g ^ n : M) * y⁻¹, hyR,
    M.mul_mem (M.mul_mem hyM (g ^ n).2) (M.inv_mem hyM), ?_⟩
  have hr : mk ⟨y * (g ^ n : M) * y⁻¹, M.mul_mem (M.mul_mem hyM (g ^ n).2) (M.inv_mem hyM)⟩ =
      yb * l * yb⁻¹ := by
    rw [← hgpl, hyb, ← map_inv, ← map_mul, ← map_mul]
    rfl
  rw [hr, barM_map_conj hyM]
  refine ⟨⟨l, hlL, rfl⟩, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨w, hw, rfl⟩
  have hcw := Subgroup.mem_centralizer_iff.mp hlc w hw
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have e1 : (yb * l * yb⁻¹)⁻¹ * zb = yb * (l⁻¹ * zb) * yb⁻¹ := by
    calc (yb * l * yb⁻¹)⁻¹ * zb = yb * l⁻¹ * (yb⁻¹ * zb * yb) * yb⁻¹ := by group
      _ = yb * l⁻¹ * zb * yb⁻¹ := by
        rw [show yb⁻¹ * zb * yb = zb by rw [mul_assoc, ← hybz, inv_mul_cancel_left]]
      _ = yb * (l⁻¹ * zb) * yb⁻¹ := by group
  rw [e1]
  calc yb * w * yb⁻¹ * (yb * (l⁻¹ * zb) * yb⁻¹) = yb * (w * (l⁻¹ * zb)) * yb⁻¹ := by group
    _ = yb * ((l⁻¹ * zb) * w) * yb⁻¹ := by rw [hcw]
    _ = yb * (l⁻¹ * zb) * yb⁻¹ * (yb * w * yb⁻¹) := by group

end CFSG.AGLEmbedding
