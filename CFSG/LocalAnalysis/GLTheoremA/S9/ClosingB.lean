module

public import CFSG.LocalAnalysis.GLTheoremA.S9.ClosingA

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S9.Cl

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem center_ne_bot_of_isPGroup {q : ℕ} (hq : q.Prime) {Q : Subgroup G} (hQ : IsPGroup q Q)
    (hne : Q ≠ ⊥) : Q ⊓ Subgroup.centralizer (Q : Set G) ≠ ⊥ := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Nontrivial ↥Q := (Subgroup.nontrivial_iff_ne_bot Q).2 hne
  haveI : Nontrivial (Subgroup.center ↥Q) := hQ.center_nontrivial
  obtain ⟨c, hc1⟩ := exists_ne (1 : Subgroup.center ↥Q)
  intro hbot
  have hmem : ((c : ↥Q) : G) ∈ Q ⊓ Subgroup.centralizer (Q : Set G) := by
    refine ⟨(c : ↥Q).2, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
    have := Subgroup.mem_center_iff.1 c.2 ⟨h, hh⟩
    exact congrArg Subtype.val this
  rw [hbot, Subgroup.mem_bot] at hmem
  apply hc1
  apply Subtype.ext
  apply Subtype.ext
  exact hmem

theorem eq_sup_zpowers_of_card {D : Subgroup G} (hD : IsElemAbelian 3 D) (hDc : Nat.card D = 3 ^ 2)
    {a e : G} (haD : a ∈ D) (ha1 : a ≠ 1) (heD : e ∈ D) (hea : e ∉ Subgroup.zpowers a) :
    Subgroup.zpowers a ⊔ Subgroup.zpowers e = D := by
  have hp3 : Nat.Prime 3 := by norm_num
  haveI : Fact (Nat.Prime 3) := ⟨hp3⟩
  have he1 : e ≠ 1 := fun h => hea (h ▸ Subgroup.one_mem _)
  have hoa : orderOf a = 3 := orderOf_eq_prime (hD.2 a haD) ha1
  have hoe : orderOf e = 3 := orderOf_eq_prime (hD.2 e heD) he1
  have hcomm : Subgroup.zpowers a ≤ Subgroup.centralizer (Subgroup.zpowers e : Set G) := by
    rw [Subgroup.zpowers_le, S3.centralizer_zpowers, Subgroup.mem_centralizer_singleton_iff]
    exact isElemAbelian_commute hD haD heD
  have hnorm : Subgroup.zpowers e ≤ Subgroup.normalizer (Subgroup.zpowers a : Set G) :=
    (Subgroup.le_centralizer_iff.1 hcomm).trans (Subgroup.centralizer_le_normalizer _)
  have hinf : Nat.card (Subgroup.zpowers a ⊓ Subgroup.zpowers e : Subgroup G) = 1 := by
    have hdvd : Nat.card (Subgroup.zpowers a ⊓ Subgroup.zpowers e : Subgroup G) ∣ 3 := by
      have := Subgroup.card_dvd_of_le (inf_le_right : Subgroup.zpowers a ⊓ Subgroup.zpowers e ≤
        Subgroup.zpowers e)
      rwa [Nat.card_zpowers, hoe] at this
    rcases (Nat.dvd_prime hp3).1 hdvd with h | h
    · exact h
    · exfalso
      have heq := Subgroup.eq_of_le_of_card_ge
        (inf_le_right : Subgroup.zpowers a ⊓ Subgroup.zpowers e ≤ Subgroup.zpowers e)
        (by rw [h, Nat.card_zpowers, hoe])
      apply hea
      have : e ∈ Subgroup.zpowers a ⊓ Subgroup.zpowers e := by
        rw [heq]
        exact Subgroup.mem_zpowers e
      exact this.1
  have hsup : Nat.card (Subgroup.zpowers a ⊔ Subgroup.zpowers e : Subgroup G) = 3 ^ 2 := by
    have h := card_sup_mul_card_inf_of_le_normalizer hnorm
    rw [hinf, mul_one, Nat.card_zpowers, Nat.card_zpowers, hoa, hoe] at h
    rw [h]
    norm_num
  have hle : Subgroup.zpowers a ⊔ Subgroup.zpowers e ≤ D :=
    sup_le (Subgroup.zpowers_le.2 haD) (Subgroup.zpowers_le.2 heD)
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hsup, hDc])

theorem commutator_core_eq_bot {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {x z : G} {Z : Subgroup G}
    (hZM : Z ≤ cx z) (hZO : Z ≤ pCoreOf q (cx x)) :
    (⁅Z, pCoreOf 2 (cx z) ⊓ cx x⁆ : Subgroup G) = ⊥ := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdis : Disjoint (pCoreOf q (cx x)) (pCoreOf 2 (cx z)) :=
    IsPGroup.disjoint_of_ne q 2 hq2 _ _ (CFSG.LieType.BorelTits.pCoreOf_isPGroup q (cx x))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (cx z))
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro u hu r hr
  have hr1 : r ∈ pCoreOf 2 (cx z) := hr.1
  have hr2 : r ∈ cx x := hr.2
  have h1 : ⁅u, r⁆ ∈ pCoreOf q (cx x) := by
    have h : r * u⁻¹ * r⁻¹ ∈ pCoreOf q (cx x) :=
      (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf q (cx x) hr2) u⁻¹).1
        (Subgroup.inv_mem _ (hZO hu))
    have e : ⁅u, r⁆ = u * (r * u⁻¹ * r⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.mul_mem _ (hZO hu) h
  have h2 : ⁅u, r⁆ ∈ pCoreOf 2 (cx z) := by
    have h : u * r * u⁻¹ ∈ pCoreOf 2 (cx z) :=
      (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 (cx z) (hZM hu)) r).1 hr1
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ h (Subgroup.inv_mem _ hr1)
  exact hdis.le_bot ⟨h1, h2⟩

theorem exists_a_S (hc : S9Ctx G 3) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {x y z : G}
    {L Bs D J E₀ Z : Subgroup G} (hcfg : Cfg x y z L Bs D J E₀) (hx1 : x ≠ 1) (hZ : Z ≠ ⊥)
    (hZq : IsPGroup q Z) (hZM : Z ≤ cx z) (hZD : Z ≤ Subgroup.centralizer (D : Set G))
    (hZO : Z ≤ pCoreOf q (cx x)) :
    ∃ a ∈ D, a ≠ 1 ∧ Subgroup.zpowers x ⊔ Subgroup.zpowers a = D ∧ a ∉ Subgroup.zpowers x ∧
      (⁅Z, pCoreOf 2 (cx z) ⊓ cx a⁆ : Subgroup G) ≠ ⊥ := by
  have hp3 : Nat.Prime 3 := hc.ctx.prime
  haveI : Fact (Nat.Prime 3) := ⟨hp3⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := hcfg.D_el
  have hDc := hcfg.D_card
  have hxD : x ∈ D := by
    rw [hcfg.D_gen]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
  have hD1 : D ≠ ⊥ := by
    intro h
    have := hDc
    rw [h, Subgroup.card_bot] at this
    omega
  have hnot2 : ¬ IsPGroup 2 Z := fun h2 =>
    hZ (disjoint_self.1 (IsPGroup.disjoint_of_ne q 2 hq2 Z Z hZq h2))
  have hN : IsTwoLocal (cx z) := isTwoLocal_cx_of_sq hcfg.z_sq hcfg.z_ne
  have hDM : D ≤ cx z := hcfg.D_le.trans hcfg.Bs_z
  obtain ⟨A, hAD, hAidx, hAcomm⟩ := GL83.I_33_3_proved G hc.ctx.charTwo 3 hp3 (by norm_num) (cx z) D Z
    hN hD1 hD hDM (le_inf hZM hZD) hnot2
  have hAcard : Nat.card A = 3 := by
    have h1 := Subgroup.card_mul_index (A.subgroupOf D)
    rw [hAidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAD).toEquiv] at h1
    have h2 : Nat.card D = 3 ^ 2 := hDc
    omega
  have hAne : A ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hAcard
    omega
  obtain ⟨a', ha'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hAne
  set a : G := (a' : G) with hadef
  have haA : a ∈ A := a'.2
  have haD : a ∈ D := hAD haA
  have ha1 : a ≠ 1 := fun h => ha' (Subtype.ext h)
  have hoa : orderOf a = 3 := orderOf_eq_prime (hD.2 a haD) ha1
  have hAeq : A = Subgroup.zpowers a := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 haA) ?_).symm
    rw [Nat.card_zpowers, hoa, hAcard]
  rw [hAeq, S3.centralizer_zpowers] at hAcomm
  have hox : orderOf x = 3 := orderOf_eq_prime (hD.2 x hxD) hx1
  have hax : a ∉ Subgroup.zpowers x := by
    intro hmem
    apply hAcomm
    have hzz : Subgroup.zpowers a = Subgroup.zpowers x := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hmem) ?_
      rw [Nat.card_zpowers, Nat.card_zpowers, hoa, hox]
    have hcxx : Subgroup.centralizer ({a} : Set G) = Subgroup.centralizer ({x} : Set G) := by
      rw [← S3.centralizer_zpowers, hzz, S3.centralizer_zpowers]
    rw [hcxx]
    exact commutator_core_eq_bot hq hq2 hZM hZO
  refine ⟨a, haD, ha1, eq_sup_zpowers_of_card hD hDc hxD hx1 haD hax, hax, hAcomm⟩

theorem twoLocalRank_le_pRank_cl {p : ℕ} (hp : p.Prime) {B X : Subgroup G} (hB : GLAIsBmax p B)
    (hBX : B ≤ X) : GLATwoLocalRank p ↥X ≤ CFSG.Open.pRank p B := by
  refine le_trans ?_ (CFSG.SectionRank.le_pRank hp.one_lt le_rfl hB.1 hB.2.1)
  unfold GLATwoLocalRank CFSG.Open.twoLocalPrimeRank
  refine csSup_le' ?_
  rintro k ⟨H, ⟨P, hP1, hP2, rfl⟩, rfl⟩
  have hPG1 : P.map X.subtype ≠ ⊥ := fun h =>
    hP1 ((Subgroup.map_eq_bot_iff_of_injective P X.subtype_injective).1 h)
  have hPG2 : IsPGroup 2 (P.map X.subtype) := hP2.map X.subtype
  have hle : (Subgroup.normalizer (P : Set ↥X)).map X.subtype ≤
      Subgroup.normalizer ((P.map X.subtype : Subgroup G) : Set G) :=
    Subgroup.le_normalizer_map _
  exact (CFSG.SectionRank.pRank_le_map hp.one_lt X.subtype X.subtype_injective _).trans
    ((CFSG.SectionRank.pRank_mono hp.one_lt hle).trans (pRank_normalizer_le hp.one_lt hPG1 hPG2))

theorem orbit_contra_cl (hc : S9Ctx G 3) (h112 : I112RkAt G) {Bs D J J₁ : Subgroup G} {a e : G}
    (hBs : GLAIsBmax 3 Bs) (hDBs : D ≤ Bs) (hD : IsElemAbelian 3 D) (hDc : Nat.card D = 3 ^ 2)
    (haD : a ∈ D) (ha1 : a ≠ 1) (heD : e ∈ D)
    (hJ : GLAPComponent 3 (Subgroup.centralizer (D : Set G)) J)
    (hE : ∃ E : Subgroup G, E ≤ J ∧ IsElemAbelian 3 E ∧ 3 ^ 3 ≤ Nat.card E)
    (hJ₁ : GLAPComponent 3 (cx a) J₁) (hJJ₁ : J ≤ closureIn J₁ Bs)
    (heN : e ∉ Subgroup.normalizer (J₁ : Set G)) : False := by
  have hp := hc.ctx.prime
  obtain ⟨E, hEJ, hEel, hE3⟩ := hE
  have hBsa : Bs ≤ cx a := isElemAbelian_le_centralizer hBs.1 (hDBs haD)
  have hnot : ¬ Bs ≤ Subgroup.normalizer (J₁ : Set G) := fun h => heN (h (hDBs heD))
  have hea : e ∉ Subgroup.zpowers a := by
    intro h
    apply heN
    have hle : Subgroup.zpowers a ≤ Subgroup.centralizer (J₁ : Set G) := by
      rw [Subgroup.zpowers_le]
      refine Subgroup.mem_centralizer_iff.2 fun l hl => ?_
      exact Subgroup.mem_centralizer_singleton_iff.1 (hJ₁.1 hl)
    exact Subgroup.centralizer_le_normalizer _ (hle h)
  have hcen : Subgroup.centralizer (D : Set G) = cx a ⊓ cx e :=
    centralizer_eq_inf_of_gen (eq_sup_zpowers_of_card hD hDc haD ha1 heD hea).symm
  have hclo : closureIn J₁ Bs ≤ cx a := by
    unfold closureIn
    refine iSup₂_le fun b hb => ?_
    rintro _ ⟨l, hl, rfl⟩
    show b * l * b⁻¹ ∈ cx a
    exact (cx a).mul_mem ((cx a).mul_mem (hBsa hb) (hJ₁.1 hl)) ((cx a).inv_mem (hBsa hb))
  have hIcomp : GLAPComponent 3 (closureIn J₁ Bs ⊓ cx e) J := by
    refine glaPComponent_of_le hp hJ
      (le_inf hJJ₁ (hJ.1.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.2 heD)))) ?_
    rw [hcen]
    exact inf_le_inf_right _ hclo
  have hw := h112 (cx a) Bs J₁ (isKGroup_cx hc ha1) hBsa hBs.1
    (twoLocalRank_le_pRank_cl hp hBs hBsa) hJ₁ hnot e (hDBs heD) heN J hIcomp E hEJ hEel
  have : 3 ^ 3 ≤ 3 ^ 2 := hE3.trans hw
  norm_num at this

theorem le_closureIn_self (J H : Subgroup G) : J ≤ closureIn J H := by
  have h : J = J.map (MulAut.conj (1 : G)).toMonoidHom := by
    rw [map_one]
    exact (Subgroup.map_id J).symm
  conv_lhs => rw [h]
  exact le_iSup₂_of_le (1 : G) (Subgroup.one_mem _) le_rfl

theorem ja_single_cl (hc : S9Ctx G 3) (h183 : Input18_3_4) (h112 : I112RkAt G) {Bs D J : Subgroup G}
    {a : G} (hBs : GLAIsBmax 3 Bs) (hDBs : D ≤ Bs) (hD : IsElemAbelian 3 D) (hDc : Nat.card D = 3 ^ 2)
    (haD : a ∈ D) (ha1 : a ≠ 1) (hJ : GLAPComponent 3 (Subgroup.centralizer (D : Set G)) J)
    (hE : ∃ E : Subgroup G, E ≤ J ∧ IsElemAbelian 3 E ∧ 3 ^ 3 ≤ Nat.card E) :
    GLAPComponent 3 (cx a) (closureIn J (GLAPLayer 3 (cx a))) := by
  have hp := hc.ctx.prime
  have hDa : D ≤ cx a := isElemAbelian_le_centralizer hD haD
  have hX : cx a ⊓ Subgroup.centralizer (D : Set G) = Subgroup.centralizer (D : Set G) :=
    inf_eq_right.2 (Subgroup.centralizer_le (Set.singleton_subset_iff.2 haD))
  obtain ⟨𝒞, h𝒞c, h𝒞sup, -, h𝒞tr⟩ :=
    h183 G (cx a) (isKGroup_cx hc ha1) 3 hp D hDa hD J (by rw [hX]; exact hJ)
  have hJa : closureIn J (GLAPLayer 3 (cx a)) = ⨆ L' ∈ 𝒞, L' := by
    rw [h𝒞sup]
    exact closureIn_eq_iSup_gLBConj _ _
  have hIJ : J ≤ closureIn J (GLAPLayer 3 (cx a)) := le_closureIn_self _ _
  obtain ⟨L₁, hL₁⟩ : 𝒞.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have h0 : closureIn J (GLAPLayer 3 (cx a)) = ⊥ := by
      rw [hJa, hne]
      simp
    exact glaPComponent_ne_bot' hJ (le_bot_iff.1 (h0 ▸ hIJ))
  have hIL : J ≤ closureIn L₁ Bs := by
    refine hIJ.trans ?_
    rw [hJa]
    refine iSup₂_le fun L' hL' => ?_
    obtain ⟨e', he', rfl⟩ := h𝒞tr L₁ hL₁ L' hL'
    unfold GLBConj closureIn
    exact le_iSup₂_of_le e'⁻¹ (Bs.inv_mem (hDBs he')) le_rfl
  have hall : ∀ L' ∈ 𝒞, L' = L₁ := by
    intro L' hL'
    obtain ⟨e, he, rfl⟩ := h𝒞tr L₁ hL₁ L' hL'
    by_contra hne
    exact orbit_contra_cl hc h112 hBs hDBs hD hDc haD ha1 he hJ hE (h𝒞c L₁ hL₁) hIL
      (fun h => hne (mem_normalizer_iff_gLBConj_eq.1 h))
  have heq : closureIn J (GLAPLayer 3 (cx a)) = L₁ := by
    rw [hJa]
    exact le_antisymm (iSup₂_le fun L' hL' => (hall L' hL').le) (le_iSup₂_of_le L₁ hL₁ le_rfl)
  rw [heq]
  exact h𝒞c L₁ hL₁

theorem odd_core_ca (hc : S9Ctx G 3) (hrank : GLATwoLocalRank 3 G = 4) {x y z : G}
    {L Bs D J E₀ : Subgroup G} (hcfg : Cfg x y z L Bs D J E₀) {a : G} (haD : a ∈ D) :
    Odd (Nat.card (GLAPPrimeCoreOf 3 (cx a))) := by
  by_contra hev
  have hp := hc.ctx.prime
  have hp2 := hc.ctx.odd
  obtain ⟨N, hN, hcov⟩ := exists_covers_of_even hp hp2 (Nat.not_odd_iff_even.1 hev)
  have hmax := isMaxRankIn_of_covers hp hp2 hcfg.bs_bmax hN hcov
  have hE₀D : E₀ ≤ Subgroup.centralizer (D : Set G) :=
    hcfg.E₀_le.trans (Subgroup.le_centralizer_iff.1 hcfg.D_cJ)
  have hel : IsElemAbelian 3 (E₀ ⊔ D) := isElemAbelian_sup_of_commute hcfg.E₀_el hcfg.D_el hE₀D
  have hle : E₀ ⊔ D ≤ cx a :=
    sup_le (hE₀D.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.2 haD)))
      (isElemAbelian_le_centralizer hcfg.D_el haD)
  have hcard : Nat.card (E₀ ⊔ D : Subgroup G) = 3 ^ 5 := by
    have hDn : D ≤ Subgroup.normalizer (E₀ : Set G) :=
      (Subgroup.le_centralizer_iff.2 hE₀D).trans (Subgroup.centralizer_le_normalizer _)
    have hinf : E₀ ⊓ D = ⊥ := by
      rw [eq_bot_iff, ← hcfg.DJ]
      exact le_inf inf_le_right (inf_le_left.trans hcfg.E₀_le)
    have h := card_sup_mul_card_inf_of_le_normalizer hDn
    rw [hinf, Subgroup.card_bot, mul_one, hcfg.E₀_card, hcfg.D_card] at h
    rw [h]
    norm_num
  have hbs : Nat.card Bs = 3 ^ 4 := by rw [hcfg.bs_bmax.2.1, hrank]
  have h := hmax _ hle hel
  rw [hcard, hbs] at h
  norm_num at h

end CFSG.LocalAnalysis.GLTheoremA.S9.Cl
