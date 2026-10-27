module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionCyclic
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoAutCard
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoReduced
import CFSG.Walter.JRFacts
import CFSG.LocalAnalysis.RankThreeTheoremC.InvariantTwoBalance

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding
open scoped MatrixGroups

variable {Y : Type} [Group Y] [Finite Y]

theorem add_le_pRank_local {p : ℕ} (hp : p.Prime) {G : Type*} [Group G] [Finite G]
    {E₁ E₂ H : Subgroup G} (hE₁ : CFSG.Open.IsElemAbelian p E₁)
    (hE₂ : CFSG.Open.IsElemAbelian p E₂) {r₁ r₂ : ℕ} (h₁ : Nat.card E₁ = p ^ r₁)
    (h₂ : Nat.card E₂ = p ^ r₂) (hc : ∀ x ∈ E₁, ∀ y ∈ E₂, Commute x y) (hdisj : E₁ ⊓ E₂ = ⊥)
    (h₁H : E₁ ≤ H) (h₂H : E₂ ≤ H) : r₁ + r₂ ≤ CFSG.Open.pRank p H := by
  let f : E₁ × E₂ →* G := MonoidHom.noncommCoprod E₁.subtype E₂.subtype
    (fun x y => hc x x.2 y y.2)
  have hf : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨x, y⟩ hxy
    have h : (x : G) * y = 1 := hxy
    have hx : (x : G) ∈ E₁ ⊓ E₂ := Subgroup.mem_inf.2 ⟨x.2, by
      rw [eq_inv_of_mul_eq_one_left h]
      exact E₂.inv_mem y.2⟩
    rw [hdisj, Subgroup.mem_bot] at hx
    have hy : (y : G) = 1 := by rw [hx, one_mul] at h; exact h
    rw [Subgroup.mem_bot, Prod.mk_eq_one]
    exact ⟨Subtype.ext hx, Subtype.ext hy⟩
  have hc₁ := hE₁.1
  have hc₂ := hE₂.1
  refine CFSG.SectionRank.le_pRank_of_injective hp.one_lt (A := E₁ × E₂) ?_ ?_ ?_ f hf ?_
  · rintro ⟨a, b⟩ ⟨c, d⟩
    exact Prod.ext (mul_comm' a c) (mul_comm' b d)
  · rintro ⟨a, b⟩
    exact Prod.ext (Subtype.ext (hE₁.2 a a.2)) (Subtype.ext (hE₂.2 b b.2))
  · rw [Nat.card_prod, h₁, h₂, pow_add]
  · rintro _ ⟨⟨a, b⟩, rfl⟩
    exact H.mul_mem (h₁H a.2) (h₂H b.2)

theorem psl2_second_sylow_abelian {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (S : Sylow p Y)
    (hS3 : CFSG.Open.pRank p (S : Subgroup Y) ≤ 3) (L : Subgroup Y) [L.Normal]
    (e : L ≃* PSL2GF p 2) : IsMulCommutative (S : Subgroup Y) := by
  have hp : p.Prime := Fact.out
  have hq4 : 4 ≤ Nat.card (GaloisField p 2) := by
    rw [GaloisField.card p 2 (by norm_num)]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ p ^ 2 := Nat.pow_le_pow_left hp.two_le 2
  haveI hsimpleP : IsSimpleGroup (PSL2GF p 2) := isSimpleGroup_psl2GF_of_two_le le_rfl
  haveI : IsSimpleGroup L := e.isSimpleGroup
  obtain ⟨a, b, hab⟩ := CFSG.Walter.exists_mul_ne_mul_of_mulEquiv_psl2 hq4 e
  have hZ : Subgroup.center L = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center L) with h | h
    · exact h
    · exfalso
      have ha : a ∈ Subgroup.center L := h ▸ Subgroup.mem_top a
      exact hab (Subgroup.mem_center_iff.mp ha b).symm
  have hLC : L ⊓ Subgroup.centralizer (L : Set Y) = ⊥ := inf_centralizer_eq_bot L hZ
  set C : Subgroup Y := Subgroup.centralizer (L : Set Y) with hC
  set π : Y →* Y ⧸ C := QuotientGroup.mk' C with hπ
  have hKn : (L.map π).Normal :=
    Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective C)
  have hKe : Nonempty (↥(L.map π) ≃* PSL2GF p 2) :=
    ⟨(mulEquivMapCentralizer L hZ).symm.trans e⟩
  have hKC : Subgroup.centralizer ((L.map π : Subgroup (Y ⧸ C)) : Set (Y ⧸ C)) = ⊥ :=
    centralizer_map_centralizer_eq_bot L hZ
  have hSπ : IsPGroup p ((S : Subgroup Y).map π) := S.isPGroup'.map π
  have hdvd := card_dvd_of_isPGroup_of_psl2GF kFactL2AutPCard hp2 (n := 2) (by norm_num) hKn hKe
    hKC _ hSπ
  have hle2 : Nat.card ((S : Subgroup Y).map π) ≤ p ^ 2 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hSπ
    rw [hk] at hdvd ⊢
    have hcop : Nat.Coprime (p ^ k) 2 :=
      Nat.Coprime.pow_left k ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
    exact Nat.le_of_dvd (pow_pos hp.pos 2) (hcop.dvd_of_dvd_mul_right hdvd)
  have hSylTop : CFSG.ABGLocalTools.IsSylowOf p (S : Subgroup Y) ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    exact ⟨le_top, S.isPGroup', by rw [Subgroup.relIndex_top_right]; exact S.not_dvd_index⟩
  have hSylL : CFSG.ABGLocalTools.IsSylowOf p ((S : Subgroup Y) ⊓ L) L :=
    hSylTop.inf_of_le_normalizer le_top (by rw [Subgroup.normalizer_eq_top])
  obtain ⟨T⟩ : Nonempty (Sylow p (PSL2GF p 2)) := inferInstance
  have hT := psl2GF_sylow p 2 (by norm_num) T
  have hfact : (Nat.card (PSL2GF p 2)).factorization p = 2 := by
    have h1 := Sylow.card_eq_multiplicity T
    rw [hT.2] at h1
    exact (Nat.pow_right_injective hp.two_le h1).symm
  have hAcard : Nat.card ((S : Subgroup Y) ⊓ L : Subgroup Y) = p ^ 2 := by
    rw [hSylL.card_eq, Nat.card_congr e.toEquiv, hfact]
  set A : Subgroup Y := (S : Subgroup Y) ⊓ L with hA
  have hAS : A ≤ (S : Subgroup Y) := inf_le_left
  have hAL : A ≤ L := inf_le_right
  have hAelem : IsElemAbelian p A := by
    set A' : Subgroup (PSL2GF p 2) := (A.subgroupOf L).map e.toMonoidHom with hA'
    have hA'card : Nat.card A' = p ^ (Nat.card (PSL2GF p 2)).factorization p := by
      rw [hfact, hA', Subgroup.card_map_of_injective e.injective,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv, hAcard]
    have hT' := (psl2GF_sylow p 2 (by norm_num) (Sylow.ofCard A' hA'card)).1
    rw [Sylow.coe_ofCard] at hT'
    have hmem : ∀ x : Y, ∀ hx : x ∈ A, e ⟨x, hAL hx⟩ ∈ A' := fun x hx =>
      ⟨⟨x, hAL hx⟩, hx, rfl⟩
    refine ⟨⟨⟨fun u v => ?_⟩⟩, fun x hx => ?_⟩
    · have hc := hT'.1.is_comm.comm ⟨e ⟨u.1, hAL u.2⟩, hmem _ u.2⟩ ⟨e ⟨v.1, hAL v.2⟩, hmem _ v.2⟩
      apply Subtype.ext
      have h2 : e (⟨u.1, hAL u.2⟩ * ⟨v.1, hAL v.2⟩) = e (⟨v.1, hAL v.2⟩ * ⟨u.1, hAL u.2⟩) := by
        rw [map_mul, map_mul]
        exact congrArg Subtype.val hc
      exact congrArg (Subtype.val : ↥L → Y) (e.injective h2)
    · have h1 := hT'.2 _ (hmem x hx)
      have h2 : e ((⟨x, hAL hx⟩ : L) ^ p) = e 1 := by rw [map_pow, map_one]; exact h1
      exact congrArg (Subtype.val : ↥L → Y) (e.injective h2)
  have hπL : Function.Injective (π.comp L.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    have h1 : (g : Y) ∈ C := by
      have : π (g : Y) = 1 := hg
      simpa [hπ, QuotientGroup.eq_one_iff] using this
    have h2 : (g : Y) ∈ L ⊓ C := ⟨g.2, h1⟩
    rw [hLC, Subgroup.mem_bot] at h2
    exact Subgroup.mem_bot.mpr (Subtype.ext h2)
  have hAmap : A.map π = (A.subgroupOf L).map (π.comp L.subtype) := by
    ext y
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, hAL ha⟩, ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a.1, ha, rfl⟩
  have hπAcard : Nat.card (A.map π) = p ^ 2 := by
    rw [hAmap, Subgroup.card_map_of_injective hπL,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv, hAcard]
  have hmapeq : A.map π = (S : Subgroup Y).map π :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.map_mono hAS) (hπAcard ▸ hle2)
  set B : Subgroup Y := (S : Subgroup Y) ⊓ C with hB
  have hBS : B ≤ (S : Subgroup Y) := inf_le_left
  have hdecomp : ∀ s ∈ (S : Subgroup Y), ∃ a ∈ A, ∃ b ∈ B, s = a * b := by
    intro s hs
    have hsπ : π s ∈ A.map π := hmapeq ▸ Subgroup.mem_map_of_mem π hs
    obtain ⟨a, ha, haπ⟩ := hsπ
    refine ⟨a, ha, a⁻¹ * s, ⟨(S : Subgroup Y).mul_mem ((S : Subgroup Y).inv_mem (hAS ha)) hs, ?_⟩,
      by group⟩
    have : π (a⁻¹ * s) = 1 := by rw [map_mul, map_inv, haπ, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff (a⁻¹ * s)).mp this
  have hAB : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.mp hy.2 x (hAL hx)
  have hBcomm : IsMulCommutative B := by
    by_contra hnc
    have hBp : IsPGroup p B := S.isPGroup'.to_le hBS
    haveI : Fact (IsPGroup p B) := ⟨hBp⟩
    have hncyc : ¬ IsCyclic B := fun hc => hnc (IsCyclic.isMulCommutative)
    obtain ⟨E, -, hEcard, hEel⟩ := CFSG.lemma_4_5_a hp2 hncyc
    haveI : CFSG.IsElementaryAbelian p (E.map B.subtype) := CFSG.IsElementaryAbelian.map_subtype
    set E' : Subgroup Y := E.map B.subtype with hE'
    have hE'card : Nat.card E' = p ^ 2 := by
      rw [hE', Subgroup.card_map_of_injective B.subtype_injective, hEcard]
    have hE'elem : IsElemAbelian p E' :=
      ⟨inferInstance, fun x hx => CFSG.elemPow_eq_one_of_isElementaryAbelian x hx⟩
    have hE'B : E' ≤ B := by
      rintro _ ⟨e', -, rfl⟩
      exact e'.2
    have hcomm : ∀ x ∈ A, ∀ y ∈ E', Commute x y := fun x hx y hy => hAB x hx y (hE'B hy)
    have hdisj : A ⊓ E' = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      have h1 : z ∈ L ⊓ C := ⟨hAL hz.1, (hE'B hz.2).2⟩
      rwa [hLC] at h1
    have h4 := add_le_pRank_local hp hAelem hE'elem hAcard hE'card hcomm hdisj hAS
      (hE'B.trans hBS)
    omega
  refine ⟨⟨fun s t => ?_⟩⟩
  obtain ⟨a, ha, b, hb, hs⟩ := hdecomp s.1 s.2
  obtain ⟨a', ha', b', hb', ht⟩ := hdecomp t.1 t.2
  apply Subtype.ext
  show (s : Y) * t = t * s
  have hAc := hAelem.1.is_comm.comm
  have hBc := hBcomm.is_comm.comm
  have e1 : a * a' = a' * a := congrArg Subtype.val (hAc ⟨a, ha⟩ ⟨a', ha'⟩)
  have e2 : b * b' = b' * b := congrArg Subtype.val (hBc ⟨b, hb⟩ ⟨b', hb'⟩)
  rw [hs, ht]
  calc a * b * (a' * b') = a * (b * a') * b' := by group
    _ = a * (a' * b) * b' := by rw [← hAB a' ha' b hb]
    _ = (a * a') * (b * b') := by group
    _ = (a' * a) * (b' * b) := by rw [e1, e2]
    _ = a' * (a * b') * b := by group
    _ = a' * (b' * a) * b := by rw [hAB a ha b' hb']
    _ = a' * b' * (a * b) := by group

variable {G : Type} [Group G] [Finite G]

theorem u3_psl2_second_false {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) {P : Sylow p G}
    (hP3 : CFSG.Open.pRank p (P : Subgroup G) = 3) (hPnab : ¬ IsMulCommutative (P : Subgroup G))
    {a : G} (hPa : (P : Subgroup G) ≤ Subgroup.centralizer ({a} : Set G))
    {Ja : Subgroup G} (hJa : Ja ≤ Subgroup.centralizer ({a} : Set G))
    (hCJa : Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (Ja : Set G))
    {Q : Type} [Group Q] (ψ : ↥Ja →* Q) (hψ : Function.Surjective ψ)
    (hker : ψ.ker = (rankThreePrimeCore p Ja).subgroupOf Ja)
    (hQ : Nonempty (Q ≃* PSL(2, GaloisField p 2))) : False := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  set C : Subgroup G := Subgroup.centralizer ({a} : Set G) with hC
  set O : Subgroup G := rankThreePrimeCore p Ja with hO
  have hOJ : O ≤ Ja := glbPrimeCore_le p Ja
  have hOC : O ≤ C := hOJ.trans hJa
  have hOcop : p.Coprime (Nat.card O) := glbPrimeCore_coprime p Ja
  have hOnorm : C ≤ Subgroup.normalizer (O : Set G) := by
    intro g hg
    have hgJ : Ja.map (MulAut.conj g).toMonoidHom = Ja :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hCJa hg)
    have h1 := glbPrimeCore_map_automorphism p Ja (MulAut.conj g)
    rw [hgJ] at h1
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h1
  let O' : Subgroup C := O.subgroupOf C
  haveI hO'n : O'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hOC).mpr hOnorm
  have hO'cop : p.Coprime (Nat.card O') := by
    have : Nat.card O' = Nat.card O := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOC).toEquiv
    rw [this]
    exact hOcop
  let π : C →* C ⧸ O' := QuotientGroup.mk' O'
  let J' : Subgroup C := Ja.subgroupOf C
  haveI hJ'n : J'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hJa).mpr hCJa
  let L : Subgroup (C ⧸ O') := J'.map π
  haveI hLn : L.Normal := Subgroup.Normal.map hJ'n π (QuotientGroup.mk'_surjective O')
  obtain ⟨eQ⟩ := hQ
  let eJ : J' ≃* Ja := Subgroup.subgroupOfEquivOfLe hJa
  let ψ' : J' →* Q := ψ.comp eJ.toMonoidHom
  have hψ' : Function.Surjective ψ' := hψ.comp eJ.surjective
  let πJ : J' →* L := (π.comp J'.subtype).codRestrict L (fun j => Subgroup.mem_map_of_mem π j.2)
  have hπJ : Function.Surjective πJ := by
    rintro ⟨_, j, hj, rfl⟩
    exact ⟨⟨j, hj⟩, rfl⟩
  have hkerEq : ψ'.ker = πJ.ker := by
    ext j
    have h1 : ψ' j = 1 ↔ ((j : C) : G) ∈ O := by
      have h : ψ (eJ j) = 1 ↔ eJ j ∈ ψ.ker := MonoidHom.mem_ker.symm
      rw [show ψ' j = ψ (eJ j) from rfl, h, hker, Subgroup.mem_subgroupOf]
      rfl
    have h2 : πJ j = 1 ↔ ((j : C) : G) ∈ O := by
      constructor
      · intro h
        have h' : π (j : C) = 1 := congrArg Subtype.val h
        exact (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff (j : C)).mp h'))
      · intro h
        apply Subtype.ext
        exact (QuotientGroup.eq_one_iff (j : C)).mpr (Subgroup.mem_subgroupOf.mpr h)
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, h1, h2]
  let e : L ≃* PSL(2, GaloisField p 2) :=
    ((QuotientGroup.quotientKerEquivOfSurjective πJ hπJ).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hkerEq.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective ψ' hψ'))).trans eQ
  let S₀ : Sylow p C := P.subtype hPa
  let S : Sylow p (C ⧸ O') := S₀.mapSurjective (QuotientGroup.mk'_surjective O')
  have hSco : (S : Subgroup (C ⧸ O')) = ((P : Subgroup G).subgroupOf C).map π := by
    rw [Sylow.coe_mapSurjective, Sylow.coe_subtype]
  have hrank : CFSG.Open.pRank p (S : Subgroup (C ⧸ O')) ≤ 3 := by
    rw [hSco, pRank_map_mk_eq_pRank_map_subtype hp O' hO'cop,
      Subgroup.map_subgroupOf_eq_of_le hPa, hP3]
  have hcomm := psl2_second_sylow_abelian hp2 S hrank L e
  have hPO : (P : Subgroup G) ⊓ O = ⊥ := by
    have hPp : IsPGroup p ↥((P : Subgroup G) ⊓ O) := P.isPGroup'.to_inf_left
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hPp
    have hdvd : Nat.card ((P : Subgroup G) ⊓ O : Subgroup G) ∣ Nat.card O :=
      Subgroup.card_dvd_of_le inf_le_right
    have hk0 : k = 0 := by
      by_contra hk0
      have : p ∣ Nat.card O := (dvd_pow_self p hk0).trans (hk ▸ hdvd)
      exact (hp.coprime_iff_not_dvd.mp hOcop) this
    rw [hk0, pow_zero] at hk
    exact Subgroup.eq_bot_of_card_eq _ hk
  apply hPnab
  refine ⟨⟨fun x y => ?_⟩⟩
  have hmemS : ∀ z : ↥(P : Subgroup G), π ⟨z.1, hPa z.2⟩ ∈ (S : Subgroup (C ⧸ O')) := by
    intro z
    rw [hSco]
    exact ⟨⟨z.1, hPa z.2⟩, Subgroup.mem_subgroupOf.mpr z.2, rfl⟩
  have hc := congrArg Subtype.val
    (hcomm.is_comm.comm ⟨π ⟨x.1, hPa x.2⟩, hmemS x⟩ ⟨π ⟨y.1, hPa y.2⟩, hmemS y⟩)
  have hc' : π (⟨x.1, hPa x.2⟩ * ⟨y.1, hPa y.2⟩) = π (⟨y.1, hPa y.2⟩ * ⟨x.1, hPa x.2⟩) := by
    rw [map_mul, map_mul]
    exact hc
  have hmem := (QuotientGroup.eq (s := O')).mp hc'.symm
  have hmemO : (y.1 * x.1)⁻¹ * (x.1 * y.1) ∈ O := Subgroup.mem_subgroupOf.mp hmem
  have hmemP : (y.1 * x.1)⁻¹ * (x.1 * y.1) ∈ (P : Subgroup G) :=
    (P : Subgroup G).mul_mem ((P : Subgroup G).inv_mem ((P : Subgroup G).mul_mem y.2 x.2))
      ((P : Subgroup G).mul_mem x.2 y.2)
  have h1 : (y.1 * x.1)⁻¹ * (x.1 * y.1) ∈ (P : Subgroup G) ⊓ O := ⟨hmemP, hmemO⟩
  rw [hPO, Subgroup.mem_bot, inv_mul_eq_one] at h1
  exact Subtype.ext h1.symm

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3
