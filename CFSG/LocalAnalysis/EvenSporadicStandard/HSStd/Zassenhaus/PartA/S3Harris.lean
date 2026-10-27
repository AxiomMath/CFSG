module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S3Catalog
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S3Shape
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.Toolbox
import CFSG.Adapters.StatedClassicalUnitaryOrders
import CFSG.Adapters.StatedClassicalSmallOrders

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Open
open scoped commutatorElement
open CFSG.EvenSporadicStandard.HSStd

theorem s3h_card_U43 {N : Type} [Group N] (h : LieModel N .PSU 4 3 1) : Nat.card N = 3265920 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_four_three (h.statedClassicalModel (by decide))

theorem s3h_card_L33 {N : Type} [Group N] (h : LieModel N .PSL 3 3 2) : Nat.card N = 42456960 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_nine (h.statedClassicalModel (by decide))

theorem s3h_card_L43 {N : Type} [Group N] (h : LieModel N .PSL 4 3 1) : Nat.card N = 6065280 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_four_three (h.statedClassicalModel (by decide))

theorem s3h_card_A6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  have h := two_mul_nat_card_alternatingGroup (α := Fin 6)
  rw [Nat.card_perm, Nat.card_eq_fintype_card (α := Fin 6), Fintype.card_fin] at h
  have h6 : Nat.factorial 6 = 720 := by decide
  omega

theorem s3h_nonab6 : ∃ a b : alternatingGroup (Fin 6), a * b ≠ b * a := by
  refine ⟨⟨Equiv.swap 0 1 * Equiv.swap 1 2, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩,
    ⟨Equiv.swap 1 2 * Equiv.swap 2 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩,
    fun h => ?_⟩
  have := congrArg Subtype.val h
  revert this
  decide

instance s3h_simple6 : IsSimpleGroup (alternatingGroup (Fin 6)) :=
  alternatingGroup.isSimpleGroup (by simp)

theorem s3h_perfect6 : commutator (alternatingGroup (Fin 6)) = ⊤ := by
  have h := IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator (alternatingGroup (Fin 6)))
  rcases h with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := s3h_nonab6
    apply hab
    have : ⁅a, b⁆ ∈ commutator (alternatingGroup (Fin 6)) := by
      rw [_root_.commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot, commutatorElement_def] at this
    calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
      _ = b * a := by rw [this, one_mul]
  · exact h

theorem s3h_two_elem (a b : Multiplicative (ZMod 2)) (ha : a ≠ 1) (hb : b ≠ 1) : a = b := by
  revert a b; decide

theorem s3h_cen_derived {X : Type} [Group X] [Finite X] (s : X) (hs : orderOf s = 2)
    (e : ↥(centralizer ({s} : Set X)) ≃*
      Multiplicative (ZMod 2) × MulAut (alternatingGroup (Fin 6))) :
    ∀ c ∈ centralizer ({s} : Set X), (∀ l ∈ centralizerDerived s, c * l = l * c) →
      c = 1 ∨ c = s := by
  intro c hc hcl
  set C := centralizer ({s} : Set X) with hC
  have hsC : s ∈ C := by
    rw [hC, mem_centralizer_iff]; intro h hh; rw [Set.mem_singleton_iff] at hh; rw [hh]
  set sC : C := ⟨s, hsC⟩ with hsCdef
  have hs1 : s ≠ 1 := fun h => by rw [h, orderOf_one] at hs; exact absurd hs (by norm_num)
  have hsC1 : sC ≠ 1 := fun h => hs1 (congrArg Subtype.val h)
  have hcent : ∀ g : C, g * sC = sC * g := by
    intro g
    apply Subtype.ext
    have := (mem_centralizer_iff.1 g.2) s rfl
    exact this.symm
  obtain ⟨a₀, m₀⟩ : Multiplicative (ZMod 2) × MulAut (alternatingGroup (Fin 6)) := e sC
  have hm₀ : (e sC).2 = 1 := by
    have hcen : (e sC).2 ∈ Subgroup.center (MulAut (alternatingGroup (Fin 6))) := by
      rw [Subgroup.mem_center_iff]
      intro m
      have := congrArg (fun z => (e z).2) (hcent (e.symm (1, m)))
      simpa using this
    rw [center_mulAut_eq_bot s3h_nonab6] at hcen
    simpa using hcen
  have ha₀ : (e sC).1 ≠ 1 := by
    intro h
    apply hsC1
    apply e.injective
    refine Prod.ext ?_ ?_
    · simpa using h
    · simpa using hm₀
  set c' : C := ⟨c, hc⟩ with hc'
  have hm : (e c').2 = 1 := by
    have hcomm : ∀ x : alternatingGroup (Fin 6),
        c' * e.symm (1, MulAut.conj x) = e.symm (1, MulAut.conj x) * c' := by
      intro x
      let f : alternatingGroup (Fin 6) →* C :=
        (e.symm : Multiplicative (ZMod 2) × MulAut (alternatingGroup (Fin 6)) →* C).comp
          ((MonoidHom.inr (Multiplicative (ZMod 2)) (MulAut (alternatingGroup (Fin 6)))).comp
            (MulAut.conj : alternatingGroup (Fin 6) →* MulAut (alternatingGroup (Fin 6))))
      have hfx : f x = e.symm (1, MulAut.conj x) := rfl
      have hmem : f x ∈ commutator C := by
        have h1 : f x ∈ (commutator (alternatingGroup (Fin 6))).map f :=
          ⟨x, by rw [s3h_perfect6]; trivial, rfl⟩
        rw [_root_.commutator_def, map_commutator] at h1
        exact commutator_mono le_top le_top h1
      have hmemL : ((f x : C) : X) ∈ centralizerDerived s :=
        ⟨f x, hmem, rfl⟩
      have := hcl _ hmemL
      rw [← hfx]
      exact Subtype.ext this
    apply eq_one_of_commute_conj s3h_nonab6
    intro x
    have := congrArg (fun z => (e z).2) (hcomm x)
    simpa using this
  have hcases : c' = 1 ∨ c' = sC := by
    by_cases h1 : (e c').1 = 1
    · left
      apply e.injective
      refine Prod.ext ?_ ?_
      · simpa using h1
      · simpa using hm
    · right
      apply e.injective
      refine Prod.ext ?_ ?_
      · exact s3h_two_elem _ _ h1 ha₀
      · simp [hm, hm₀]
  rcases hcases with h | h
  · left; exact congrArg Subtype.val h
  · right; exact congrArg Subtype.val h

theorem s3h_odd_complement {B : Type*} [Group B] [Finite B] (s : B) (hs : s * s = 1) (hs1 : s ≠ 1)
    (h : ∀ b : B, b * s = s * b → b = 1 ∨ b = s) :
    ∃ K : Subgroup B, K.Normal ∧ Odd (Nat.card K) ∧ Nat.card B = 2 * Nat.card K ∧
      ∀ g : B, Odd (orderOf g) → g ∈ K := by
  classical
  have := Fintype.ofFinite B
  have hord : orderOf s = 2 := orderOf_eq_prime (by rw [pow_two]; exact hs) hs1
  have hpg : IsPGroup 2 (Subgroup.zpowers s) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord]; simp)
  obtain ⟨P, hP⟩ := hpg.exists_le_sylow
  have hsP : s ∈ (P : Subgroup B) := hP (Subgroup.mem_zpowers s)
  have hPle : (P : Subgroup B) ≤ Subgroup.zpowers s := by
    have : Nontrivial (P : Subgroup B) := ⟨⟨⟨s, hsP⟩, 1, fun h' => hs1 (congrArg Subtype.val h')⟩⟩
    have hnt : Nontrivial (Subgroup.center ↥(P : Subgroup B)) := P.isPGroup'.center_nontrivial
    obtain ⟨z, hz1⟩ := exists_ne (1 : Subgroup.center ↥(P : Subgroup B))
    have hzc := z.2
    have hzne : (z : ↥(P : Subgroup B)) ≠ 1 := fun h' => hz1 (Subtype.ext h')
    have hzs : ((z : ↥(P : Subgroup B)) : B) * s = s * ((z : ↥(P : Subgroup B)) : B) := by
      have := Subgroup.mem_center_iff.1 hzc ⟨s, hsP⟩
      exact (congrArg Subtype.val this).symm
    have hzS : ((z : ↥(P : Subgroup B)) : B) = s := by
      rcases h _ hzs with h1 | h1
      · exact absurd (Subtype.ext h1) hzne
      · exact h1
    have hzeq : (z : ↥(P : Subgroup B)) = ⟨s, hsP⟩ := Subtype.ext hzS
    have hsc : (⟨s, hsP⟩ : ↥(P : Subgroup B)) ∈ Subgroup.center ↥(P : Subgroup B) := hzeq ▸ hzc
    intro p hp
    have hps : p * s = s * p := by
      have := Subgroup.mem_center_iff.1 hsc ⟨p, hp⟩
      exact congrArg Subtype.val this
    rcases h p hps with h1 | h1
    · rw [h1]; exact Subgroup.one_mem _
    · rw [h1]; exact Subgroup.mem_zpowers s
  have hPeq : (P : Subgroup B) = Subgroup.zpowers s := le_antisymm hPle hP
  have hPcard : Nat.card (P : Subgroup B) = 2 := by rw [hPeq, Nat.card_zpowers, hord]
  have hcyc : IsCyclic (P : Subgroup B) :=
    isCyclic_of_prime_card (p := 2) hPcard
  have hdvd : 2 ∣ Nat.card B := hPcard ▸ Subgroup.card_subgroup_dvd_card (P : Subgroup B)
  have hev : Even (Fintype.card B) := by
    rw [← Nat.card_eq_fintype_card]; exact even_iff_two_dvd.2 hdvd
  obtain ⟨hε, hsurj, hnorm, hidx⟩ := CFSG.LinearGroups.cyclic_sylow_index_two hev P hcyc
  set ε : B →* ℤˣ := Equiv.Perm.sign.comp (MulAction.toPermHom B B) with hεdef
  refine ⟨ε.ker, hnorm, ?_, ?_, ?_⟩
  · have h1 := Subgroup.card_mul_index (P : Subgroup B)
    have h2 := Subgroup.card_mul_index ε.ker
    have hodd : ¬ 2 ∣ (P : Subgroup B).index := P.not_dvd_index
    rw [hidx] at h2
    rw [hPcard] at h1
    have : Nat.card ε.ker = (P : Subgroup B).index := by omega
    rw [this]
    exact Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 hodd)
  · have h2 := Subgroup.card_mul_index ε.ker
    rw [hidx] at h2
    omega
  · intro g hg
    rw [MonoidHom.mem_ker]
    have h1 : (ε g) ^ orderOf g = 1 := by
      rw [← map_pow, pow_orderOf_eq_one, map_one]
    rcases Int.units_eq_one_or (ε g) with h' | h'
    · exact h'
    · rw [h', hg.neg_one_pow] at h1
      exact absurd h1 (by decide)

theorem s3h_le_oddCore {X : Type} [Group X] (M : Subgroup X) [M.Normal] (h : Odd (Nat.card M)) :
    M ≤ fusionOddCore X :=
  le_sSup ⟨inferInstance, h⟩

theorem s3h_ker_conjNormal {X : Type} [Group X] (N : Subgroup X) [N.Normal] :
    (MulAut.conjNormal : X →* MulAut N).ker = centralizer (N : Set X) := by
  ext x
  rw [MonoidHom.mem_ker, mem_centralizer_iff]
  constructor
  · intro h n hn
    have := congrArg (fun f : MulAut N => (f ⟨n, hn⟩ : N).1) h
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
    calc n * x = (x * n * x⁻¹) * x := by rw [this]
      _ = x * n := by group
  · intro h
    ext ⟨n, hn⟩
    simp only [MulAut.conjNormal_apply, MulAut.one_apply]
    rw [← h n hn, mul_inv_cancel_right]

theorem s3h_no_seven {X : Type} [Group X] [Finite X] (N : Subgroup X) [N.Normal]
    (hN : Nat.card (MulAut N) = 1440) (hB : Nat.card (centralizer (N : Set X)) ∣ 2) (y : X) :
    ¬ 7 ∣ Nat.card (centralizer ({y} : Set X)) := by
  intro h7
  have hX : 7 ∣ Nat.card X := h7.trans (Subgroup.card_subgroup_dvd_card _)
  set f : X →* MulAut N := MulAut.conjNormal with hf
  have hfin : Finite (MulAut N) := by
    have : Finite N := inferInstance
    exact Finite.of_injective (fun a : MulAut N => (a : N → N)) DFunLike.coe_injective
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, s3h_ker_conjNormal] at h1
  have hr : Nat.card f.range ∣ 1440 := hN ▸ Subgroup.card_subgroup_dvd_card f.range
  rw [h1] at hX
  rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 7)).1 hX with h | h
  · have := h.trans hr
    omega
  · have := h.trans hB
    omega

theorem harris_contra (hHs : Harris311)
    (h7 : ThreeCentralizer7) : HarrisContra := by
  intro X _ _ hK hO s hs e y hy h7y
  obtain ⟨φ⟩ := e
  have hss : s * s = 1 := by
    have := pow_orderOf_eq_one s
    rwa [hs, pow_two] at this
  have hs1 : s ≠ 1 := fun h => by rw [h, orderOf_one] at hs; exact absurd hs (by norm_num)
  have hNnorm : (normalClosureOf (centralizerDerived s)).Normal := Subgroup.normalClosure_normal
  have hLN : centralizerDerived s ≤ normalClosureOf (centralizerDerived s) :=
    Subgroup.subset_normalClosure
  set N : Subgroup X := normalClosureOf (centralizerDerived s) with hN
  have hBnorm : (centralizer (N : Set X)).Normal := inferInstance
  have hfix : ∀ b ∈ centralizer (N : Set X), b * s = s * b → b = 1 ∨ b = s := by
    intro b hb hbs
    refine s3h_cen_derived s hs φ b ?_ ?_
    · rw [mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]; exact hbs.symm
    · intro l hl
      exact ((mem_centralizer_iff.1 hb) l (hLN hl)).symm
  have hHarris := hHs X hK hO s hs ⟨φ⟩
  unfold HarrisOutcome at hHarris
  have hAut : ∀ _ : ↥N ≃* alternatingGroup (Fin 6), Nat.card (MulAut ↥N) = 1440 := fun eN => by
    rw [Nat.card_congr (MulAut.congr eN).toEquiv]
    exact CFSG.QuasithinUnique.Setup.X3Aut.card_mulAut_alt6
  by_cases hsB : s ∈ centralizer (N : Set X)
  ·
    have hNC : N ≤ centralizer ({s} : Set X) := by
      intro n hn
      rw [mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]; exact ((mem_centralizer_iff.1 hsB) n hn).symm
    have hCcard : Nat.card (centralizer ({s} : Set X)) = 2880 := by
      rw [Nat.card_congr φ.toEquiv, Nat.card_prod,
        CFSG.QuasithinUnique.Setup.X3Aut.card_mulAut_alt6]
      simp
    have hdvd : Nat.card N ∣ 2880 :=
      hCcard ▸ Subgroup.card_dvd_of_le hNC
    have hle : Nat.card N ≤ 2880 := Nat.le_of_dvd (by norm_num) hdvd
    have hNA6 : Nonempty (↥N ≃* alternatingGroup (Fin 6)) := by
      rcases hHarris with h | h1 | h | h2 | h | h
      · exact h
      · obtain ⟨eN⟩ := h1
        have : Nat.card N = 360 * 360 := by
          rw [Nat.card_congr eN.toEquiv, Nat.card_prod, s3h_card_A6]
        omega
      · have : Nat.card N = 3265920 := s3h_card_U43 h
        omega
      · obtain ⟨eN⟩ := h2
        have : Nat.card N = 44352000 := by
          rw [Nat.card_congr eN.toEquiv]
          exact CFSG.Sporadic.HS.card_HS
        omega
      · have : Nat.card N = 42456960 := s3h_card_L33 h
        omega
      · have : Nat.card N = 6065280 := s3h_card_L43 h
        omega
    obtain ⟨eN⟩ := hNA6
    let sB : ↥(centralizer (N : Set X)) := ⟨s, hsB⟩
    obtain ⟨K, hKn, hKodd, hcard, hKord⟩ := s3h_odd_complement sB (Subtype.ext hss)
      (fun h => hs1 (congrArg Subtype.val h)) (fun b hb => by
        rcases hfix b b.2 (congrArg Subtype.val hb) with h | h
        · exact Or.inl (Subtype.ext h)
        · exact Or.inr (Subtype.ext h))
    have hK'n : (K.map (centralizer (N : Set X)).subtype).Normal := by
      constructor
      intro n hn g
      obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hn
      have hgB : g * ((k : ↥(centralizer (N : Set X))) : X) * g⁻¹ ∈ centralizer (N : Set X) :=
        hBnorm.conj_mem _ k.2 g
      refine Subgroup.mem_map.2 ⟨⟨_, hgB⟩, hKord _ ?_, rfl⟩
      have h1 : orderOf (⟨_, hgB⟩ : ↥(centralizer (N : Set X))) =
          orderOf (k : ↥(centralizer (N : Set X))) := by
        rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe k]
        exact orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective _
      rw [h1]
      refine Odd.of_dvd_nat hKodd ?_
      have := orderOf_dvd_natCard (⟨k, hk⟩ : K)
      rw [← Subgroup.orderOf_coe] at this
      exact this
    have hK'odd : Odd (Nat.card (K.map (centralizer (N : Set X)).subtype)) := by
      rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
      exact hKodd
    have hK'le := s3h_le_oddCore _ hK'odd
    rw [hO, le_bot_iff] at hK'le
    have hK1 : Nat.card K = 1 := by
      rw [← Subgroup.card_map_of_injective (Subgroup.subtype_injective (centralizer (N : Set X))),
        hK'le, Subgroup.card_bot]
    exact s3h_no_seven N (hAut eN) (by rw [hcard, hK1]) y h7y
  ·
    have hodd : Odd (Nat.card (centralizer (N : Set X))) := by
      by_contra hne
      have h2 : 2 ∣ Nat.card (centralizer (N : Set X)) :=
        (Nat.not_odd_iff_even.1 hne).two_dvd
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' 2 h2
      have hfix' : ∀ o ∈ centralizer (N : Set X), s * o = o * s → o = 1 := by
        intro o ho hos
        rcases hfix o ho hos.symm with h | h
        · exact h
        · exact absurd (h ▸ ho) hsB
      have hinv := (inv_of_centralizer_eq_bot hss (fun o ho => hBnorm.conj_mem o ho s) hfix').1
        (b : X) b.2
      have hbb : (b : X) * b = 1 := by
        have := pow_orderOf_eq_one b
        rw [hb, pow_two] at this
        exact congrArg Subtype.val this
      have hbinv : (b : X)⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
      rw [hbinv] at hinv
      have hcomm : s * (b : X) = b * s := by
        calc s * (b : X) = s * b * s⁻¹ * s := by group
          _ = b * s := by rw [hinv]
      have h1 := hfix' b b.2 hcomm
      have : b = 1 := Subtype.ext h1
      rw [this, orderOf_one] at hb
      exact absurd hb (by norm_num)
    have hB1 : centralizer (N : Set X) = ⊥ := by
      have := s3h_le_oddCore (centralizer (N : Set X)) hodd
      rw [hO, le_bot_iff] at this
      exact this
    rcases hHarris with h0 | h | h | h | h | h
    · obtain ⟨eN⟩ := h0
      exact s3h_no_seven N (hAut eN) (by rw [hB1]; simp) y h7y
    · exact h7 X N hNnorm hB1 (Or.inl h) y hy h7y
    · exact h7 X N hNnorm hB1 (Or.inr (Or.inr (Or.inl h))) y hy h7y
    · exact h7 X N hNnorm hB1 (Or.inr (Or.inl h)) y hy h7y
    · exact h7 X N hNnorm hB1 (Or.inr (Or.inr (Or.inr (Or.inl h)))) y hy h7y
    · exact h7 X N hNnorm hB1 (Or.inr (Or.inr (Or.inr (Or.inr h)))) y hy h7y

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
