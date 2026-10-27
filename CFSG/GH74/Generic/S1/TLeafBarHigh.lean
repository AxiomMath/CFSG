module

public import CFSG.GH74.Generic.S1.SymComp
public import CFSG.GH74.Generic.S1.CompIdent
public import CFSG.GH74.Generic.S1.SL2Facts
public import CFSG.GH74.KGroups.L3EpsOuterLin

public section

open CFSG CFSG.GH74 CFSG.GH74.L5U5 Subgroup CFSG.GH74.Generic CFSG.LocalCores CFSG.Assembly.LowTwoRank
  CFSG.GH74.Filter.ClassicalOdd
open scoped commutatorElement

namespace CFSG.GH74.Generic.S1

section Central

variable {G : Type} [Group G] [Finite G]

theorem central_of_mem_pPrimeCore {c : G} {L : Subgroup G} (hLq : IsQuasisimple ↥L)
    (hLC : L ≤ centralizer ({c} : Set G)) {w : G} (hwL : w ∈ L)
    (hwO : w ∈ CFSG.GH74.GLS.pPrimeCoreOf 2 (centralizer ({c} : Set G))) :
    ∀ l ∈ L, w * l = l * w := by
  set O : Subgroup G := CFSG.GH74.GLS.pPrimeCoreOf 2 (centralizer ({c} : Set G)) with hO
  have hOn : ∀ g ∈ centralizer ({c} : Set G), ∀ o ∈ O, g * o * g⁻¹ ∈ O := fun g hg o ho =>
    CFSG.GH74.GLS.TwoThin.pPrimeCoreOf_normalized _ hg ho
  have hOodd : Odd (Nat.card O) := CFSG.GH74.GLS.TwoThin.card_pPrimeCoreOf_odd _
  have hN : (O.subgroupOf L).Normal :=
    ⟨fun n hn g => mem_subgroupOf.2 (hOn g.1 (hLC g.2) n.1 (mem_subgroupOf.1 hn))⟩
  have hOsolv : Group.IsSolvable ↥O := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hOodd
  have hsolv : Group.IsSolvable ↥(O.subgroupOf L) := by
    let φ : ↥(O.subgroupOf L) →* ↥O :=
      ((L.subtype).comp (O.subgroupOf L).subtype).codRestrict O (fun x => x.2)
    have hφ : Function.Injective φ := by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : ↥O => (z : G)) hab
    exact Group.isSolvable_of_isSolvable_injective hφ
  rcases quasisimple_normal_subgroups hLq hN with htop | hcen
  · exfalso
    have : Group.IsSolvable ↥(⊤ : Subgroup ↥L) := by rw [← htop]; exact hsolv
    have hLs : Group.IsSolvable ↥L :=
      Group.isSolvable_of_surjective (f := (Subgroup.topEquiv : (⊤ : Subgroup ↥L) ≃* ↥L).toMonoidHom)
        Subgroup.topEquiv.surjective
    have : Nontrivial ↥L := isQuasisimple_nontrivial hLq
    have : Group.IsPerfect ↥L := hLq.1
    exact Group.IsPerfect.not_isSolvable ↥L hLs
  · intro l hl
    have hw : (⟨w, hwL⟩ : ↥L) ∈ O.subgroupOf L := mem_subgroupOf.2 hwO
    have := Subgroup.mem_center_iff.1 (hcen hw) ⟨l, hl⟩
    exact (congrArg Subtype.val this).symm

end Central

section Q8

variable {G : Type} [Group G] [Finite G]

theorem q8_barSub_of_sl2 {c : G} {J : Subgroup G} {q : ℕ} (hq : Odd q)
    (hJ : CFSG.GH74.GLS.HasSL2Model ↥J (fun q' => q' = q)) (hJc : ∀ a ∈ J, a * c = c * a) :
    ∃ ψ : Q8 →* CentralizerBar c, Function.Injective ψ ∧ ∀ g, ψ g ∈ S45.barSub c J := by
  obtain ⟨ψ₀, hψ₀, hψ₀J⟩ := exists_q8_of_hasSL2Model hq hJ
  have hψC : ∀ g, ψ₀ g ∈ centralizer ({c} : Set G) := fun g =>
    mem_centralizer_singleton_iff.2 (hJc _ (hψ₀J g))
  let ψ₁ : Q8 →* ↥(centralizer ({c} : Set G)) := ψ₀.codRestrict _ hψC
  have hg4 : ∀ g : Q8, g ^ 4 = 1 := by decide
  refine ⟨(proj c).comp ψ₁, ?_, fun g => ?_⟩
  · rw [injective_iff_map_eq_one]
    intro g hg
    have hg' : proj c (ψ₁ g) = 1 := hg
    have hodd := proj_odd c (ψ₁ g) hg'
    have h4 : (ψ₁ g) ^ 4 = 1 := by
      rw [← map_pow]
      rw [hg4 g, map_one]
    have h2 : orderOf (ψ₁ g) ∣ 4 := orderOf_dvd_of_pow_eq_one h4
    have h1 : orderOf (ψ₁ g) = 1 := by
      obtain ⟨k, hk⟩ := hodd
      have hle := Nat.le_of_dvd (by norm_num) h2
      rw [hk] at h2 hle ⊢
      have : k ≤ 1 := by omega
      interval_cases k
      · rfl
      · omega
    have : ψ₁ g = 1 := orderOf_eq_one_iff.1 h1
    apply hψ₀
    rw [map_one]
    exact congrArg Subtype.val this
  · exact S45.proj_mem_barSub (hψC g) (hψ₀J g)

end Q8

section Sl2

variable {G : Type} [Group G] [Finite G]

theorem barSub_hasSL2Model {c : G} {J : Subgroup G} {q : ℕ} (hq : Odd q) (h4 : 4 ≤ q)
    (hJ : CFSG.GH74.GLS.HasSL2Model ↥J (fun q' => q' = q)) (hJc : ∀ a ∈ J, a * c = c * a) :
    CFSG.GH74.GLS.HasSL2Model ↥(S45.barSub c J) (fun q' => q' = q) := by
  have hJq := isQuasisimple_of_sl2 h4 hJ
  obtain ⟨t, htJ, ht2, -, hcen⟩ := sl2_involution_facts hq hJ
  have hJC : J ≤ centralizer ({c} : Set G) := fun a ha =>
    mem_centralizer_singleton_iff.2 (hJc a ha)
  let g : ↥J →* CentralizerBar c := (proj c).comp (Subgroup.inclusion hJC)
  have hinj : Function.Injective g := by
    rw [injective_iff_map_eq_one]
    intro j hj
    have hj' : proj c (Subgroup.inclusion hJC j) = 1 := hj
    have hodd := proj_odd c (Subgroup.inclusion hJC j) hj'
    have hmem : (j : G) ∈ CFSG.GH74.GLS.pPrimeCoreOf 2 (centralizer ({c} : Set G)) :=
      ⟨Subgroup.inclusion hJC j, (QuotientGroup.eq_one_iff _).1 hj', rfl⟩
    have hc := central_of_mem_pPrimeCore hJq hJC j.2 hmem
    rcases hcen (j : G) j.2 hc with h | h
    · exact Subtype.ext h
    · exfalso
      have h1 : orderOf (Subgroup.inclusion hJC j) = orderOf (j : G) :=
        orderOf_injective (Subgroup.inclusion hJC) (Subgroup.inclusion_injective hJC) j |>.trans
          (Subgroup.orderOf_coe j).symm
      rw [h1, h, ht2] at hodd
      exact absurd hodd (by decide)
  have hrange : g.range = S45.barSub c J := by
    ext y
    constructor
    · rintro ⟨j, rfl⟩
      exact S45.proj_mem_barSub (hJC j.2) j.2
    · intro hy
      obtain ⟨x, hx, hxJ, rfl⟩ := S45.mem_barSub.1 hy
      exact ⟨⟨x, hxJ⟩, rfl⟩
  obtain ⟨F, _, _, hFq, ⟨e⟩⟩ := hJ
  exact ⟨F, inferInstance, inferInstance, hFq,
    ⟨(MulEquiv.subgroupCongr hrange.symm).trans ((MonoidHom.ofInjective hinj).symm.trans e)⟩⟩

end Sl2

section Bar

variable {G : Type} [Group G] [Finite G]

theorem sym_sl3Pair_bar (hExact : S1LiftExactProp) {x : G} {K : Subgroup (CentralizerBar x)}
    (hset : S1Setup G x K) (hfront : S1Front G x K) (hbigK : S1LargeModel K) {u : Fin 4 → G}
    {hu : ∀ i, u i ∈ centralizer ({x} : Set G)} (hf : S1Frame x K u hu) (hsym : S1SymFrame x u)
    {c : G} (hcJ : c ∈ symJ (symX x u) 3) (hcc : ∀ a ∈ symJ (symX x u) 3, a * c = c * a) :
    ∃ (ε : ℤ) (p f : ℕ),
      SL3Pair ε p f (S45.barSub c (symJ (symX x u) 0 ⊔ symJ (symX x u) 1))
        (S45.barSub c (symJ (symX x u) 1)) ∧
      (∃ ψ : Q8 →* CentralizerBar c, Function.Injective ψ ∧
        ∀ g, ψ g ∈ S45.barSub c (symJ (symX x u) 3)) ∧
      CFSG.GH74.GLS.HasSL2Model ↥(S45.barSub c (symJ (symX x u) 3)) (fun q' => q' = p ^ f) := by
  have hcomm := symJ_comm_high hExact hset hfront hbigK hf hsym
  have hLJ := sup_comm_three hcomm
  have hLC : symJ (symX x u) 0 ⊔ symJ (symX x u) 1 ≤ centralizer ({c} : Set G) := fun a ha =>
    mem_centralizer_singleton_iff.2 (hLJ a ha c hcJ)
  obtain ⟨-, -, hLq, -⟩ := sym_quasisimple hExact hset hfront hbigK hf hsym
  have hcentral : ∀ w ∈ (symJ (symX x u) 0 ⊔ symJ (symX x u) 1).subgroupOf (centralizer ({c} : Set G)),
      proj c w = 1 → ∀ w' ∈ (symJ (symX x u) 0 ⊔ symJ (symX x u) 1).subgroupOf
        (centralizer ({c} : Set G)), w * w' = w' * w := by
    intro w hw hw1 w' hw'
    have := central_of_mem_pPrimeCore hLq hLC (w := (w : G)) (mem_subgroupOf.1 hw)
      ⟨w, (QuotientGroup.eq_one_iff w).1 hw1, rfl⟩ (w' : G) (mem_subgroupOf.1 hw')
    exact Subtype.ext this
  rcases id hsym with ⟨F, _, _, hF, hlin⟩ | ⟨q, F, _, _, hF, hq, huni⟩
  · have h4 : 3 < Nat.card F := three_lt_card_of_largeModel hbigK hF (sym_model_four hfront hlin)
    have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card (Nat.odd_iff.2 (by omega))
    obtain ⟨p, f, hp, hf1, hFpf⟩ := exists_prime_pow_card F
    have hodd : Odd (p ^ f) := hFpf ▸ Nat.odd_iff.2 (by omega)
    have hp2 : p ≠ 2 := by
      intro h
      subst h
      exact (Nat.not_even_iff_odd.2 hodd) (Nat.even_pow.2 ⟨even_two, by omega⟩)
    have h5 : 5 ≤ p ^ f := by omega
    obtain ⟨⟨-, hpair⟩, -⟩ := sym_a4_lin hExact hset hf hF h4 hlin
    obtain ⟨W01, hW01⟩ := hpair 0 1 rfl
    obtain ⟨W23, hW23⟩ := hpair 2 3 rfl
    obtain ⟨hWe, -⟩ := lin_pair_fusion h2 hW01
    subst hWe
    have hpairY := CFSG.GH74.L5U5.linearBlockStandardPair_subgroupOf hW01 (centralizer ({c} : Set G))
      (le_sup_left.trans hLC) (le_sup_right.trans hLC)
    have hbar := linearBlockStandardPair_map_central hpairY (proj c) hcentral
    have hSL3 := lin_pair_sl3Pair hp hp2 hf1 hFpf h5 hbar
    have hSL3' := lin_pair_sl3Pair hp hp2 hf1 hFpf h5 hW23
    exact ⟨1, p, f, hSL3, q8_barSub_of_sl2 hodd hSL3'.sl2 hcc,
      barSub_hasSL2Model hodd (by omega) hSL3'.sl2 hcc⟩
  · obtain ⟨p, f, hud, hqpf, hp2⟩ := FrameUni.exists_unitaryFieldData hF hq
    have : Fact p.Prime := ⟨hud.prime⟩
    have : CharP F p := hud.charP
    subst hqpf
    have hodd : Odd (p ^ f) := Nat.odd_iff.2 (by omega)
    have hq5 : 5 ≤ p ^ f := by
      have h1 : 1 < Nat.card F := Finite.one_lt_card
      rw [hF] at h1
      have hq1 : 1 < p ^ f := by
        by_contra hle
        have hle' : p ^ f ≤ 1 := by omega
        interval_cases hpf : p ^ f <;> simp at h1
      omega
    have hq2 : p ^ f ≠ 2 := by omega
    obtain ⟨⟨-, hpair⟩, -⟩ := sym_a4_uni hExact hset hf hF hq huni p f hp2 rfl
    obtain ⟨W01, hW01⟩ := hpair 0 1 rfl
    obtain ⟨W23, hW23⟩ := hpair 2 3 rfl
    obtain ⟨hWe, -⟩ := uni_pair_fusion hF hodd hW01
    subst hWe
    have hpairY := CFSG.GH74.L5U5.unitaryBlockStandardPair_subgroupOf hF hq2 hW01
      (centralizer ({c} : Set G)) (le_sup_left.trans hLC) (le_sup_right.trans hLC)
    have hbar := unitaryBlockStandardPair_map_central hF hq2 hpairY (proj c) hcentral
    have hSL3 := uni_pair_sl3Pair hF hp2 hud.one_le hq5 hbar
    have hSL3' := uni_pair_sl3Pair hF hp2 hud.one_le hq5 hW23
    exact ⟨-1, p, f, hSL3, q8_barSub_of_sl2 hodd hSL3'.sl2 hcc,
      barSub_hasSL2Model hodd (by omega) hSL3'.sl2 hcc⟩

end Bar

section Normal

variable {G : Type} [Group G] [Finite G]

theorem sym_bar_normal (hExact : S1LiftExactProp) {x : G} {K : Subgroup (CentralizerBar x)}
    (hset : S1Setup G x K) (hfront : S1Front G x K) (hbigK : S1LargeModel K) {u : Fin 4 → G}
    {hu : ∀ i, u i ∈ centralizer ({x} : Set G)} (hf : S1Frame x K u hu) (hsym : S1SymFrame x u)
    {c : G} (hcJ : c ∈ symJ (symX x u) 3) (hc2 : orderOf c = 2)
    (hcc : ∀ a ∈ symJ (symX x u) 3, a * c = c * a) :
    ∃ y : CentralizerBar c, y ∈ S45.barSub c (symJ (symX x u) 1) ∧ y * y = 1 ∧
      ∀ g : CentralizerBar c, g * y = y * g → ∀ v ∈ S45.barSub c (symJ (symX x u) 1),
        g * v * g⁻¹ ∈ S45.barSub c (symJ (symX x u) 1) := by
  obtain ⟨hXconj, -, -, -, -⟩ := symX_facts hset.shape.2 hset.inv hf
  have hX2 : ∀ e, orderOf (symX x u e) = 2 := fun e =>
    (IsConj.orderOf_eq (hXconj e)).symm.trans hset.inv
  have hdata := sym_pairData hExact hset hfront hbigK hf hsym hcJ hc2 hcc
  obtain ⟨y, hyJ, hxy⟩ := hdata.xy4
  have hc2' : c * c = 1 := by rw [← sq, ← hc2]; exact pow_orderOf_eq_one c
  have hX4sq : symX x u 4 * symX x u 4 = 1 := by
    rw [← sq, ← hX2 4]; exact pow_orderOf_eq_one _
  have hc4 : symX x u 4 * c = c * symX x u 4 := mem_centralizer_singleton_iff.1 hdata.hc4
  have hyD : y ∈ centralizer ({symX x u 4} : Set G) ⊓ centralizer ({c} : Set G) := hdata.j1.1 hyJ
  have hyc : y ∈ centralizer ({c} : Set G) := (Subgroup.mem_inf.1 hyD).2
  have hccC : c ∈ centralizer ({c} : Set G) := mem_centralizer_singleton_iff.2 rfl
  have hyy : y = symX x u 4 * c := by
    calc y = y * c * c := by rw [mul_assoc, hc2', mul_one]
      _ = symX x u 4 * c := by rw [← hxy]
  have hy2 : y * y = 1 := by
    calc y * y = symX x u 4 * c * (symX x u 4 * c) := by rw [← hyy]
      _ = symX x u 4 * (c * symX x u 4) * c := by group
      _ = symX x u 4 * (symX x u 4 * c) * c := by rw [hc4]
      _ = symX x u 4 * symX x u 4 * (c * c) := by group
      _ = 1 := by rw [hX4sq, hc2', one_mul]
  refine ⟨proj c ⟨y, hyc⟩, S45.proj_mem_barSub hyc hyJ, ?_, ?_⟩
  · rw [← map_mul]
    have : (⟨y, hyc⟩ : ↥(centralizer ({c} : Set G))) * ⟨y, hyc⟩ = 1 := Subtype.ext hy2
    rw [this, map_one]
  · intro g hg v hv
    obtain ⟨w, hwc, hwJ, rfl⟩ := S45.mem_barSub.1 hv
    have hcbar : ∀ h : CentralizerBar c, h * proj c ⟨c, hccC⟩ = proj c ⟨c, hccC⟩ * h := by
      intro h
      obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective h
      show proj c k * proj c ⟨c, hccC⟩ = proj c ⟨c, hccC⟩ * proj c k
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (mem_centralizer_singleton_iff.1 k.2)
    have hs2 : orderOf (⟨symX x u 4, hdata.hc4⟩ : ↥(centralizer ({c} : Set G))) = 2 :=
      CFSG.GH74.GLS.TwoThin.orderOf_mk_centralizer hdata.hc4 (hX2 4)
    have hsx : proj c ⟨symX x u 4, hdata.hc4⟩ = proj c ⟨y, hyc⟩ * proj c ⟨c, hccC⟩ := by
      rw [← map_mul]
      congr 1
      exact Subtype.ext hxy
    have hgx : g ∈ centralizer ({proj c ⟨symX x u 4, hdata.hc4⟩} :
        Set (CentralizerBar c)) := by
      rw [Subgroup.mem_centralizer_singleton_iff, hsx, ← mul_assoc, hg, mul_assoc, hcbar g,
        ← mul_assoc]
    have hmap := CFSG.GH74.GLS.TwoThin.map_centralizer_barMk
      (Y := ↥(centralizer ({c} : Set G))) hs2
    have hgx' : g ∈ (centralizer ({(⟨symX x u 4, hdata.hc4⟩ : ↥(centralizer ({c} : Set G)))} :
        Set ↥(centralizer ({c} : Set G)))).map
          (CFSG.GH74.GLS.TwoThin.barMk ↥(centralizer ({c} : Set G))) := by
      rw [hmap]; exact hgx
    obtain ⟨d, hd, rfl⟩ := hgx'
    clear hgx
    have hdX : (d : G) * symX x u 4 = symX x u 4 * d := by
      have := Subgroup.mem_centralizer_singleton_iff.1 hd
      exact congrArg Subtype.val this
    have hdD : (d : G) ∈ centralizer ({symX x u 4} : Set G) ⊓ centralizer ({c} : Set G) :=
      Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 hdX, d.2⟩
    have hnorm := hdata.j1_norm d hdD w hwJ
    have hmem : (d : G) * w * (d : G)⁻¹ ∈ centralizer ({c} : Set G) :=
      (centralizer ({c} : Set G)).mul_mem ((centralizer ({c} : Set G)).mul_mem d.2 hwc)
        ((centralizer ({c} : Set G)).inv_mem d.2)
    have := S45.proj_mem_barSub hmem hnorm
    convert this using 1
    simp only [← map_inv]
    rfl

end Normal

end CFSG.GH74.Generic.S1
