module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CIURowsCom
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUXOdd

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup Assembly.LowTwoRank

namespace QPUJ6

theorem false_of_even {M : Type} [Group M] [Finite M] (hq : IsQuasisimple M)
    (hZ2 : IsPGroup 2 (center M)) {t : M} (ht2 : t * t = 1) (htZ : t ∉ center M)
    {J : Subgroup M} (hJC : J ≤ centralizer ({t} : Set M))
    (hJpc : IsPComponent 2 (J.subgroupOf (centralizer ({t} : Set M)))) {p f : ℕ}
    (h5 : 5 ≤ p ^ f) (hJLie : Blueprint.LieModel (↥J ⧸ pPrimeCore 2 ↥J) .PSL 2 p f)
    {τ : StatedLieTag} {n e : ℕ} (hM : StatedClassicalModel (M ⧸ center M) τ n 2 e) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup (M ⧸ center M) := hq.2.1
  obtain ⟨hcomp, hodd⟩ := QPUJ.Even.classical_facts hq.2.2 hM
  set ρ := QuotientGroup.mk' (center M)
  have hρ : Function.Surjective ρ := QuotientGroup.mk'_surjective _
  have ht1 : ρ t ≠ 1 := by
    intro h1
    apply htZ
    rw [← QuotientGroup.ker_mk' (center M)]
    exact h1
  have htt : orderOf (ρ t) = 2 :=
    orderOf_eq_prime (by rw [pow_two, ← map_mul, ht2, map_one]) ht1
  have hJp : Group.IsPerfect ↥J := B5a.isPerfect_of_isPComponent_subgroupOf hJC hJpc
  have hJZ : J ⊓ center M = ⊥ := by
    have := QPUJ.Even.isSimpleGroup_of_lieModel_psl_two h5 hJLie
    have : Group.IsPerfect (↥J ⧸ pPrimeCore 2 ↥J) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
    have hZq : center (↥J ⧸ pPrimeCore 2 ↥J) = ⊥ := Seven.center_eq_bot_of_isPerfect
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨hzJ, hzZ⟩ := mem_inf.mp hz
    set z' : ↥J := ⟨z, hzJ⟩
    have hz'c : QuotientGroup.mk' (pPrimeCore 2 ↥J) z' ∈ center (↥J ⧸ pPrimeCore 2 ↥J) := by
      rw [mem_center_iff]
      intro u
      obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥J) u
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (mem_center_iff.mp hzZ w)
    rw [hZq, mem_bot, ← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at hz'c
    have hR : IsPGroup 2 ((center M).subgroupOf J) := hZ2.comap_subtype
    have h1 : z' ∈ (center M).subgroupOf J ⊓ pPrimeCore 2 ↥J := mem_inf.mpr ⟨hzZ, hz'c⟩
    rw [OddQuot.inf_pPrimeCore_eq_bot hR, mem_bot] at h1
    exact mem_bot.mpr (congrArg Subtype.val h1)
  set C := centralizer ({t} : Set M)
  set Cb := centralizer ({ρ t} : Set (M ⧸ center M))
  set H := Cb.comap ρ
  have hCH : C ≤ H := fun c hc => by
    show ρ c ∈ Cb
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, mem_centralizer_singleton_iff.mp hc]
  have hCn : (C.subgroupOf H).Normal := by
    constructor
    intro c hc h
    rw [mem_subgroupOf] at hc ⊢
    have hh : ρ (h : M) * ρ t = ρ t * ρ (h : M) := mem_centralizer_singleton_iff.mp h.2
    set z := (h : M) * t * (h : M)⁻¹ * t⁻¹ with hzdef
    have hz1 : ρ z = 1 := by
      rw [hzdef, map_mul, map_mul, map_mul, map_inv, map_inv, hh]
      group
    have hz : z ∈ center M := by
      rw [← QuotientGroup.ker_mk' (center M)]
      exact hz1
    have hzc : ∀ g : M, g * z = z * g := mem_center_iff.mp hz
    have hzc' : ∀ g : M, g * z⁻¹ = z⁻¹ * g := mem_center_iff.mp (inv_mem hz)
    have h1 : (h : M) * t * (h : M)⁻¹ = z * t := by
      rw [hzdef]
      group
    have h2 : t = z * ((h : M)⁻¹ * t * h) := by
      calc t = (h : M)⁻¹ * ((h : M) * t * (h : M)⁻¹) * h := by group
        _ = (h : M)⁻¹ * (z * t) * h := by rw [h1]
        _ = (h : M)⁻¹ * z * (t * h) := by group
        _ = z * (h : M)⁻¹ * (t * h) := by rw [hzc (h : M)⁻¹]
        _ = z * ((h : M)⁻¹ * t * h) := by group
    have hu : (h : M)⁻¹ * t * h = z⁻¹ * t := by
      calc (h : M)⁻¹ * t * h = z⁻¹ * (z * ((h : M)⁻¹ * t * h)) := by group
        _ = z⁻¹ * t := by rw [← h2]
    have hct : (c : M) * t = t * c := mem_centralizer_singleton_iff.mp hc
    show (h : M) * c * (h : M)⁻¹ ∈ C
    rw [mem_centralizer_singleton_iff]
    calc (h : M) * c * (h : M)⁻¹ * t = h * c * ((h : M)⁻¹ * t * h) * (h : M)⁻¹ := by group
      _ = h * c * (z⁻¹ * t) * (h : M)⁻¹ := by rw [hu]
      _ = h * ((c : M) * z⁻¹) * t * (h : M)⁻¹ := by group
      _ = h * (z⁻¹ * c) * t * (h : M)⁻¹ := by rw [hzc' (c : M)]
      _ = h * z⁻¹ * ((c : M) * t) * (h : M)⁻¹ := by group
      _ = h * z⁻¹ * (t * c) * (h : M)⁻¹ := by rw [hct]
      _ = h * (z⁻¹ * t) * c * (h : M)⁻¹ := by group
      _ = h * ((h : M)⁻¹ * t * h) * c * (h : M)⁻¹ := by rw [hu]
      _ = t * (h * c * (h : M)⁻¹) := by group
  obtain ⟨-, -, hJs, -⟩ := id hJpc
  have hJH : J ≤ H := hJC.trans hCH
  have hJ1s : (J.subgroupOf H).IsSubnormal := by
    have hle : J.subgroupOf H ≤ C.subgroupOf H := fun x hx => hJC hx
    refine Subgroup.IsSubnormal.trans hle ?_ hCn.isSubnormal
    have heq : (J.subgroupOf C).map (subgroupOfEquivOfLe hCH).symm.toMonoidHom =
        (J.subgroupOf H).subgroupOf (C.subgroupOf H) := by
      ext x
      rw [mem_map]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨subgroupOfEquivOfLe hCH x, hx, (subgroupOfEquivOfLe hCH).symm_apply_apply x⟩
    rw [← heq]
    exact hJs.map (subgroupOfEquivOfLe hCH).symm.surjective
  let ρH : ↥H →* ↥Cb := (ρ.comp H.subtype).codRestrict Cb fun h => h.2
  have hρH : Function.Surjective ρH := by
    intro c
    obtain ⟨m, hm⟩ := hρ (c : M ⧸ center M)
    have hmH : m ∈ H := by
      show ρ m ∈ Cb
      rw [hm]
      exact c.2
    exact ⟨⟨m, hmH⟩, Subtype.ext hm⟩
  let g : ↥(J.subgroupOf H) →* ↥Cb := ρH.comp (J.subgroupOf H).subtype
  have hg : Function.Injective g := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : ((x : H) : M) ∈ J ⊓ center M := by
      refine mem_inf.mpr ⟨x.2, ?_⟩
      rw [← QuotientGroup.ker_mk' (center M), MonoidHom.mem_ker]
      exact congrArg Subtype.val hx
    rw [hJZ, mem_bot] at h1
    exact Subtype.ext (Subtype.ext h1)
  have hJbs : g.range.IsSubnormal := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact hJ1s.map hρH
  have hO : pPrimeCore 2 ↥g.range = ⊥ := by
    have hNs : ((pPrimeCore 2 ↥g.range).map g.range.subtype).IsSubnormal := by
      refine Subgroup.IsSubnormal.trans (map_subtype_le _) ?_ hJbs
      rw [show ((pPrimeCore 2 ↥g.range).map g.range.subtype).subgroupOf g.range =
          pPrimeCore 2 ↥g.range from comap_map_eq_self_of_injective g.range.subtype_injective _]
      exact (CFSG.pPrimeCore_normal (p := 2) (G := ↥g.range)).isSubnormal
    have hcop : Nat.Coprime 2 (Nat.card ↥((pPrimeCore 2 ↥g.range).map g.range.subtype)) := by
      rw [card_map_of_injective g.range.subtype_injective]
      exact CFSG.pPrimeCore_coprime_card
    have h1 := RankThree.PartOne.Sec1511.le_pPrimeCore_of_isSubnormal_p hNs hcop
    rw [hodd (ρ t) htt, le_bot_iff] at h1
    exact (map_eq_bot_iff_of_injective _ g.range.subtype_injective).mp h1
  have hq1 : IsQuasisimple (↥(J.subgroupOf C) ⧸ pPrimeCore 2 ↥(J.subgroupOf C)) :=
    ((CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 _).mp hJpc).2.2
  let e2 : ↥(J.subgroupOf C) ≃* ↥g.range :=
    ((subgroupOfEquivOfLe hJC).trans (subgroupOfEquivOfLe hJH).symm).trans
      (MonoidHom.ofInjective hg)
  have hO' : pPrimeCore 2 ↥(J.subgroupOf C) = ⊥ := by
    have h1 := pPrimeCore_map_iso 2 e2
    rw [hO] at h1
    exact (map_eq_bot_iff_of_injective _ e2.injective).mp h1
  have hqJb : IsQuasisimple ↥g.range :=
    (LocalAnalysis.ComponentInitial.isQuasisimple_congr
      (((QuotientGroup.quotientMulEquivOfEq hO').trans QuotientGroup.quotientBot).trans e2)).1 hq1
  exact hcomp (ρ t) htt g.range ⟨hqJb, hJbs⟩

theorem false_of_odd
    {M : Type} [Group M] [Finite M] (hq : IsQuasisimple M) (hZ2 : IsPGroup 2 (center M))
    {t : M} (ht2 : t * t = 1) (htZ : t ∉ center M) {J : Subgroup M}
    (hJC : J ≤ centralizer ({t} : Set M))
    (hJpc : IsPComponent 2 (J.subgroupOf (centralizer ({t} : Set M)))) {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f)
    (hJLie : Blueprint.LieModel (↥J ⧸ pPrimeCore 2 ↥J) .PSL 2 p f) {τ : StatedLieTag}
    {n r e : ℕ} (hr : r ≠ p) (hr2 : r ≠ 2) (hadm : StatedLieAdmissible τ n r e)
    (hLie : Blueprint.LieModel (M ⧸ center M) τ n r e)
    (hB : CatLeaf.FixedTwoComponentsQuasisimple (M ⧸ center M))
    (hG : CatLeafProof.GLS3OddFamilyInput τ) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup (M ⧸ center M) := hq.2.1
  have : Group.IsPerfect M := hq.1
  have : Group.IsPerfect (M ⧸ center M) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  have hZS : center (M ⧸ center M) = ⊥ := Seven.center_eq_bot_of_isPerfect
  obtain ⟨tb, htb⟩ : ∃ tb : M ⧸ center M, tb = t := ⟨_, rfl⟩
  have ht1 : tb ≠ 1 := by
    intro h1
    apply htZ
    rw [htb, QuotientGroup.eq_one_iff] at h1
    exact h1
  have htt : tb * tb = 1 := by
    rw [htb, ← QuotientGroup.mk_mul, ht2, QuotientGroup.mk_one]
  have hα2 : MulAut.conj tb * MulAut.conj tb = 1 := by rw [← map_mul, htt, map_one]
  have hα1 : MulAut.conj tb ≠ 1 := by
    intro h
    apply ht1
    have hcen : tb ∈ center (M ⧸ center M) := by
      rw [mem_center_iff]
      intro g
      have hg : tb * g * tb⁻¹ = g := by
        have := congrArg (fun β : MulAut (M ⧸ center M) => β g) h
        exact this
      calc g * tb = tb * g * tb⁻¹ * tb := by rw [hg]
        _ = tb * g := by group
    rw [hZS] at hcen
    exact mem_bot.mp hcen
  have hαo : orderOf (MulAut.conj tb) = 2 := orderOf_eq_prime (by rw [sq]; exact hα2) hα1
  obtain ⟨hJbC, hJbpc⟩ := QPUCl.isPComponent_map_centralizer t hJC hJpc
  rw [← htb, ← QPUJ.Odd.fixedSubgroup_conj tb] at hJbC hJbpc
  have hKq := hB (MulAut.conj tb) hα2 hα1 _ hJbpc
  obtain ⟨-, -, hKs, -⟩ := hJbpc
  rcases hG (M ⧸ center M) n r e hadm.1 hr2 hadm hLie (MulAut.conj tb) hαo _ ⟨hKq, hKs⟩ with
    hK | ⟨-, -, hαr, -⟩
  swap
  · exact hαr ⟨tb, rfl⟩
  have : Group.IsPerfect ↥J := B5a.isPerfect_of_isPComponent_subgroupOf hJC hJpc
  have hJZ : J ⊓ center M = ⊥ := QPUJ.Odd.inf_center_eq_bot hZ2 h5 hJLie
  have hinj : Function.Injective ((QuotientGroup.mk' (center M)).subgroupMap J) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : QuotientGroup.mk' (center M) (x : M) = 1 := congrArg Subtype.val hx
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have h2 : (x : M) ∈ J ⊓ center M := mem_inf.mpr ⟨x.2, h1⟩
    rw [hJZ, mem_bot] at h2
    exact Subtype.ext h2
  let eK := (MulEquiv.ofBijective ((QuotientGroup.mk' (center M)).subgroupMap J) ⟨hinj,
    (QuotientGroup.mk' (center M)).subgroupMap_surjective J⟩).trans (subgroupOfEquivOfLe hJbC).symm
  have hJq : IsQuasisimple ↥J := (LocalAnalysis.ComponentInitial.isQuasisimple_congr eK).mpr hKq
  have := QPUJ.Even.isSimpleGroup_of_lieModel_psl_two h5 hJLie
  have hX : Blueprint.LieModel (↥J ⧸ center ↥J) .PSL 2 p f :=
    LieType.CurtisTits.lieModel_of_mulEquiv
      (QuotientGroup.quotientMulEquivOfEq (QPUJ.Odd.pPrimeCore_eq_center hJq)) hJLie
  obtain ⟨τ', n', f'', -, hL⟩ := CatLeafProof.oddLieCentralQuotient_of_mulEquiv eK hK
  exact hr (HarrisLit.L35.char_eq_of_pslTwo hp hp2 h5 hr2 hX hL)

end QPUJ6

theorem cfQPUJ6CrossChar_holds :
    CFQPUJ6CrossChar := by
  intro M _ _ p f hc ⟨τ, n, r, f'', hr, hmod⟩
  obtain ⟨hq, hZ2, hp, hp2, hf, -, E, L, t, J, J₀, -, -, -, -, -, -, ht2, htZ, hJC, hJpc, hJLie,
    -⟩ := hc
  have h5 := QPUJ6.five_le_pow_two_mul hp hp2 hf
  by_cases hr2 : r = 2
  · subst hr2
    exact QPUJ6.false_of_even hq hZ2 ht2 htZ hJC hJpc h5 hJLie hmod
  · have : IsSimpleGroup (M ⧸ center M) := hq.2.1
    obtain ⟨hLie, hB, hG⟩ := QPUJ.Odd.family_facts (QPUJ.Odd.exists_mul_ne_quot hq) hr2 hmod
    exact QPUJ6.false_of_odd hq hZ2 ht2 htZ hJC hJpc hp hp2 h5 hJLie hr hr2 hmod.1 hLie hB hG

end CFSG.ComponentClassification.GSThmB
