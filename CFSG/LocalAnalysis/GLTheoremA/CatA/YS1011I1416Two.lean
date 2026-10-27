module

public import CFSG.LocalAnalysis.GLTheoremA.S12.Inputs122
public import CFSG.LocalAnalysis.GLTheoremA.CatC.LieCompHolds
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS09I133Small
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I112DiagChev

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

open scoped commutatorElement

@[expose] def I1416TwoSpor (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) (X J K A : Subgroup G) (y : G), p.Prime → p ≠ 2 → CFSG.Open.IsKGroup ↥X → GLAPComponent p X J →
    y ∈ Subgroup.normalizer (J : Set G) → y ^ p = 1 → ¬ CentMod p J y →
    GLAPComponent p (J ⊓ Subgroup.centralizer ({y} : Set G)) K → IsChevSimple 2 (PSimple p K) →
    IsElemAbelian p A → InnDiagOn p A K → p ^ 2 * Nat.card ↥(A ⊓ centModSubgroup p K) ≤ Nat.card A →
    catalogIs (PSimple p J) (fun i => ∃ s : TauCeti.SporadicName, i = TauCeti.CFSGIndex.sporadic s) →
    p = 3 ∧ catalogIs (PSimple 3 K) (fun i => S10.isA6 i ∨ isA8 i ∨ isG2der i ∨ S9.isU4two i)

@[expose] def I1416TwoSmall (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) (Y K A : Subgroup G) (r : ℕ), p.Prime → p ≠ 2 → r.Prime → r ≠ 2 → CFSG.Open.IsKGroup ↥Y →
    GLAPComponent p Y K → IsChevSimple 2 (PSimple p K) → IsChevSimple r (PSimple p K) →
    IsElemAbelian p A → InnDiagOn p A K → p ^ 2 * Nat.card ↥(A ⊓ centModSubgroup p K) ≤ Nat.card A →
    p = 3 ∧ catalogIs (PSimple 3 K) (fun i => S10.isA6 i ∨ isA8 i ∨ isG2der i ∨ S9.isU4two i)

theorem card_range_dvd_of_inner {S H : Type} [Group S] [Finite S] [Group H] [Finite H]
    (hcen : Subgroup.center S = ⊥) (Φ : H →* MulAut S)
    (hinn : ∀ h : H, Φ h ∈ (MulAut.conj : S →* MulAut S).range) :
    Nat.card Φ.range ∣ Nat.card S := by
  let ψ : S →* MulAut S := MulAut.conj
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hc : g ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro x
      have h1 := congrArg (fun α : MulAut S => α x) hg
      simp only [ψ, MulAut.conj_apply, MulAut.one_apply] at h1
      calc x * g = g * x * g⁻¹ * g := by rw [h1]
        _ = g * x := by group
    rw [hcen, Subgroup.mem_bot] at hc
    exact hc
  have hsub : ∀ x ∈ Φ.range, ∃ s : S, ψ s = x := fun x hx => by
    obtain ⟨h, rfl⟩ := MonoidHom.mem_range.1 hx
    exact MonoidHom.mem_range.1 (hinn h)
  let T : Subgroup S := Φ.range.comap ψ
  have hT : Nat.card T = Nat.card Φ.range := by
    refine Nat.card_congr (Equiv.ofBijective (fun t : T => (⟨ψ t.1, t.2⟩ : Φ.range))
      ⟨fun a b hab => ?_, fun x => ?_⟩)
    · exact Subtype.ext (hinj (congrArg Subtype.val hab))
    · obtain ⟨s, hs⟩ := hsub x.1 x.2
      exact ⟨⟨s, by show ψ s ∈ Φ.range; rw [hs]; exact x.2⟩, Subtype.ext hs⟩
  rw [← hT]
  exact Subgroup.card_subgroup_dvd_card T

theorem sq_dvd_card_range {p : ℕ} (hp : p.Prime) {H S : Type} [Group H] [Finite H] [Group S] [Finite S]
    (Φ : H →* S) (m : ℕ) (hH : Nat.card H = p ^ m) (hcard : p ^ 2 * Nat.card Φ.ker ≤ Nat.card H) :
    p ^ 2 ∣ Nat.card Φ.range := by
  have hsplit : Nat.card H = Nat.card Φ.range * Nat.card Φ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange Φ).toEquiv]
  have hdvd : Nat.card Φ.range ∣ p ^ m := by
    rw [← hH, hsplit]
    exact dvd_mul_right _ _
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  have hpos : 0 < Nat.card Φ.ker := Nat.card_pos
  have hR : p ^ 2 ≤ Nat.card Φ.range := by
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    have hc := hcard
    rw [hsplit] at hc
    exact hc
  have hj2 : 2 ≤ j := by
    rw [hj] at hR
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 hR
  rw [hj]
  exact pow_dvd_pow p hj2

theorem natCard_alt_fin (m : ℕ) (hm : 2 ≤ m) :
    Nat.card (alternatingGroup (Fin m)) = m.factorial / 2 := by
  haveI : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.2 hm
  rw [nat_card_alternatingGroup, Nat.card_fin]

theorem not_sq_dvd_sixty {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : p ^ 2 ∣ 60) : False := by
  have hle : p ≤ 60 := Nat.le_of_dvd (by norm_num) ((dvd_pow_self p two_ne_zero).trans h)
  interval_cases p <;> first | omega | (norm_num at hp; done) | (norm_num at h; done)

theorem eq_three_of_sq_dvd_360 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : p ^ 2 ∣ 360) : p = 3 := by
  have hle : p ≤ 19 := by
    have : p ^ 2 ≤ 360 := Nat.le_of_dvd (by norm_num) h
    nlinarith [hp.two_le]
  interval_cases p <;> first | omega | (norm_num at hp; done) | (norm_num at h; done) | (norm_num at hp2; done)

theorem eq_three_of_sq_dvd_20160 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : p ^ 2 ∣ 20160) : p = 3 := by
  have hle : p ≤ 142 := by
    have : p ^ 2 ≤ 20160 := Nat.le_of_dvd (by norm_num) h
    nlinarith [hp.two_le]
  interval_cases p <;> first | omega | (norm_num at hp; done) | (norm_num at h; done) | (norm_num at hp2; done)

private theorem characteristic_prime' (d : TauCeti.LieTypeIndex) : d.characteristic.Prime := by
  cases d <;> simp <;> first | exact ‹TauCeti.PrimePower›.prime_p | exact Nat.prime_two | exact Nat.prime_three

theorem sq_dvd_pSimple_of_inner {G : Type} [Group G] [Finite G] {X K A : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hK : GLAPComponent p X K) (hA : IsElemAbelian p A) (hAN : A ≤ Subgroup.normalizer (K : Set G))
    (hinn : ∀ (a : G) (ha : a ∈ Subgroup.normalizer (K : Set G)), a ∈ A →
      chevAut p K ⟨a, ha⟩ ∈ (MulAut.conj : PSimple p K →* MulAut (PSimple p K)).range)
    (hcard : p ^ 2 * Nat.card ↥(A ⊓ centModSubgroup p K) ≤ Nat.card A) :
    p ^ 2 ∣ Nat.card (PSimple p K) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hs, hnc⟩ := chev_pSimple_simple_nonabelian hp hK
  haveI := hs
  have hcen : Subgroup.center (PSimple p K) = ⊥ := chev_center_eq_bot_of_simple_nonabelian hnc
  let N : Subgroup G := Subgroup.normalizer (K : Set G)
  let H : Subgroup N := A.subgroupOf N
  let ψ : H →* MulAut (PSimple p K) := (chevAut p K).comp H.subtype
  have hcardH : Nat.card H = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAN).toEquiv
  have hmap : ψ.ker.map (N.subtype.comp H.subtype) = A ⊓ centModSubgroup p K := by
    ext g
    simp only [Subgroup.mem_map, MonoidHom.mem_ker, Subgroup.mem_inf]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : chevAut p K x.1 = 1 := hx
      have hcent : CentMod p K (x.1 : G) := (chevAut_eq_one_iff hp hK x.1.2).1 hx'
      exact ⟨Subgroup.mem_subgroupOf.1 x.2, centMod_iff.1 hcent⟩
    · rintro ⟨hgA, hgC⟩
      have hgN : g ∈ N := (mem_centModSubgroup.1 hgC).1
      refine ⟨⟨⟨g, hgN⟩, Subgroup.mem_subgroupOf.2 hgA⟩, ?_, rfl⟩
      show chevAut p K ⟨g, hgN⟩ = 1
      exact (chevAut_eq_one_iff hp hK hgN).2 (centMod_iff.2 hgC)
  have hf : Function.Injective (N.subtype.comp H.subtype) :=
    Subtype.val_injective.comp Subtype.val_injective
  have hkerCard : Nat.card ψ.ker = Nat.card ↥(A ⊓ centModSubgroup p K) := by
    rw [← hmap, Subgroup.card_map_of_injective hf]
  obtain ⟨m, hm⟩ := exists_card_eq_pow_of_isElemAbelian hp hA
  have hHm : Nat.card H = p ^ m := by rw [hcardH, hm]
  have hcardψ : p ^ 2 * Nat.card ψ.ker ≤ Nat.card H := by
    rw [hkerCard, hcardH]
    exact hcard
  have hsq : p ^ 2 ∣ Nat.card ψ.range := sq_dvd_card_range hp ψ m hHm hcardψ
  have hdvd : Nat.card ψ.range ∣ Nat.card (PSimple p K) := by
    apply card_range_dvd_of_inner hcen ψ
    intro h
    exact hinn h.1.1 h.1.2 (Subgroup.mem_subgroupOf.1 h.2)
  exact hsq.trans hdvd

section Certs



theorem not_chev2_alt {m : ℕ} (hm5 : 5 ≤ m) (hne : m ≠ 5 ∧ m ≠ 6 ∧ m ≠ 8) {S : Type} [Group S]
    (e : S ≃* alternatingGroup (Fin m)) : ¬ IsChevSimple 2 S := by
  intro hC
  rcases (show m = 7 ∨ 9 ≤ m by omega) with h7 | h9
  · subst h7
    exact CFSG.LocalAnalysis.GLTheoremA.i112d_not_chev_alt7 e hC
  · rcases CFSG.LocalAnalysis.GLTheoremA.i112d_lie_or_card hC with ⟨t, n, f, hX⟩ | h360 | h6048
    · exact CFSG.OddStandard.AltStdSec.altNotLieType
        CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput h9
        ⟨t, n, 2, f, CFSG.Blueprint.LieModel.admissible hX, CFSG.Blueprint.LieModel.of_mulEquiv e hX⟩
    · have h1 : Nat.card S = m.factorial / 2 := (Nat.card_congr e.toEquiv).trans (natCard_alt_fin m (by omega))
      have h2 : (9 : ℕ).factorial ≤ m.factorial := Nat.factorial_le h9
      have h3 : (9 : ℕ).factorial / 2 ≤ m.factorial / 2 := Nat.div_le_div_right h2
      norm_num [Nat.factorial] at h3
      omega
    · have h1 : Nat.card S = m.factorial / 2 := (Nat.card_congr e.toEquiv).trans (natCard_alt_fin m (by omega))
      have h2 : (9 : ℕ).factorial ≤ m.factorial := Nat.factorial_le h9
      have h3 : (9 : ℕ).factorial / 2 ≤ m.factorial / 2 := Nat.div_le_div_right h2
      norm_num [Nat.factorial] at h3
      omega

theorem alt_branch {G : Type} [Group G] [Finite G] {p : ℕ} {X J K A : Subgroup G} {y : G} {n : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hJ : GLAPComponent p X J)
    (hyN : y ∈ Subgroup.normalizer (J : Set G)) (hyp : y ^ p = 1) (hncent : ¬ CentMod p J y)
    (hK : GLAPComponent p (J ⊓ Subgroup.centralizer ({y} : Set G)) K)
    (hKchev : IsChevSimple 2 (PSimple p K)) (hA : IsElemAbelian p A) (hinn : InnDiagOn p A K)
    (hcard : p ^ 2 * Nat.card ↥(A ⊓ centModSubgroup p K) ≤ Nat.card A)
    (hn : 5 ≤ n) (e : PSimple p J ≃* alternatingGroup (Fin n)) :
    p = 3 ∧ catalogIs (PSimple 3 K) (fun i => S10.isA6 i ∨ isA8 i ∨ isG2der i ∨ S9.isU4two i) := by
  have hyp' : IsPGroup p (Subgroup.zpowers y) := isPGroup_zpowers_of_pow_eq_one hyp
  have hK' := glaPComponent_chevTransfer hp hyN hyp' hK
  have hα : chevAut p J ⟨y, hyN⟩ ^ p = 1 := chevAut_pow_eq_one p J hyN hyp
  have hα1 : chevAut p J ⟨y, hyN⟩ ≠ 1 := fun h => hncent ((chevAut_eq_one_iff hp hJ hyN).1 h)
  obtain ⟨hβI, ⟨e₁⟩⟩ := chevQ_transport hp e hK'
  have hβ : MulAut.congr e (chevAut p J ⟨y, hyN⟩) ^ p = 1 := by
    rw [← map_pow, hα, map_one]
  have hβ1 : MulAut.congr e (chevAut p J ⟨y, hyN⟩) ≠ 1 := fun h =>
    hα1 ((MulAut.congr e).injective (h.trans (map_one _).symm))
  obtain ⟨m, hm, -, ⟨f⟩⟩ := kdAltDown_holds n p hn hp hp2 _ hβ hβ1 _ hβI
  obtain ⟨g₁⟩ := nonempty_pSimple_equiv_chevTransfer hp hyN hyp' hK
  have eK : PSimple p K ≃* alternatingGroup (Fin m) := g₁.trans (e₁.trans f)
  have hm5 : 5 ≤ m := (le_max_left 5 p).trans hm
  have hC2 : IsChevSimple 2 (alternatingGroup (Fin m)) := chev_isChevSimple_of_mulEquiv eK.symm hKchev
  have hm568 : m = 5 ∨ m = 6 ∨ m = 8 := by
    by_contra hne
    exact not_chev2_alt hm5 (by omega) (MulEquiv.refl _) hC2
  have hodd : ∀ φ : MulAut (PSimple p K), Odd (orderOf φ) → ∃ g : PSimple p K, φ = MulAut.conj g := by
    rcases hm568 with rfl | rfl | rfl
    · exact oddInner_transport eK oddInner_alt5
    · exact oddInner_transport eK oddInner_alt6
    · exact oddInner_transport eK oddInner_alt8
  have hinnA : ∀ (a : G) (ha : a ∈ Subgroup.normalizer (K : Set G)), a ∈ A →
      chevAut p K ⟨a, ha⟩ ∈ (MulAut.conj : PSimple p K →* MulAut (PSimple p K)).range := by
    intro a ha haA
    have h1 : chevAut p K ⟨a, ha⟩ ^ p = 1 := chevAut_pow_eq_one p K ha (hA.2 a haA)
    have hodd' : Odd (orderOf (chevAut p K ⟨a, ha⟩)) :=
      (hp.odd_of_ne_two hp2).of_dvd_nat (orderOf_dvd_of_pow_eq_one h1)
    obtain ⟨g, hg⟩ := hodd _ hodd'
    exact MonoidHom.mem_range.2 ⟨g, hg.symm⟩
  have hsq : p ^ 2 ∣ Nat.card (PSimple p K) :=
    sq_dvd_pSimple_of_inner hp hK hA hinn.1 hinnA hcard
  have hcardK : Nat.card (PSimple p K) = m.factorial / 2 := by
    rw [Nat.card_congr eK.toEquiv, natCard_alt_fin m (by omega)]
  rw [hcardK] at hsq
  rcases hm568 with rfl | rfl | rfl
  · norm_num [Nat.factorial] at hsq
    exact (not_sq_dvd_sixty hp hp2 hsq).elim
  · norm_num [Nat.factorial] at hsq
    have hp3 : p = 3 := eq_three_of_sq_dvd_360 hp hp2 hsq
    subst hp3
    refine ⟨rfl, TauCeti.CFSGIndex.alternating 6 (by norm_num), Or.inl (by simp [S10.isA6]), ⟨?_⟩⟩
    exact eK
  · norm_num [Nat.factorial] at hsq
    have hp3 : p = 3 := eq_three_of_sq_dvd_20160 hp hp2 hsq
    subst hp3
    refine ⟨rfl, TauCeti.CFSGIndex.alternating 8 (by norm_num), Or.inr (Or.inl (by simp [isA8])), ⟨?_⟩⟩
    exact eK

theorem i1416TwoAt_of {G : Type} [Group G] [Finite G]
    (hClo : ∀ p : ℕ, p.Prime → p ≠ 2 → ChevClosureQAt G p) (hSpor : I1416TwoSpor G) (hSmall : I1416TwoSmall G) :
    I1416TwoAt G := by
  intro p X J K A y hp hp2 hX hJ hyN hyp hncent hK hKchev hA hinn hcard
  have hcat : IsCatalogGroup (PSimple p J) :=
    CFSG.LocalAnalysis.GLTheoremA.I2611.isCatalogGroup_center_quotient' ((hX.of_le hJ.1).quotient _)
      (isQuasisimple_pQuot_of_glaPComponent hp hJ)
  obtain ⟨i, ⟨e⟩⟩ := hcat
  cases i with
  | cyclic r hr =>
    exfalso
    obtain ⟨a, b, hab⟩ := (chev_pSimple_simple_nonabelian hp hJ).2
    apply hab
    apply e.injective
    simp only [map_mul]
    exact mul_comm _ _
  | alternating n hn =>
    exact Or.inr (alt_branch hp hp2 hJ hyN hyp hncent hK hKchev hA hinn hcard hn e)
  | sporadic s =>
    exact Or.inr (hSpor p X J K A y hp hp2 hX hJ hyN hyp hncent hK hKchev hA hinn hcard
      ⟨TauCeti.CFSGIndex.sporadic s, ⟨s, rfl⟩, ⟨e⟩⟩)
  | lie d =>
    by_cases h2 : d.1.characteristic = 2
    · exact Or.inl (Or.inl ⟨TauCeti.CFSGIndex.lie d, by simpa [onLie] using h2, ⟨e⟩⟩)
    · have hr : d.1.characteristic.Prime := characteristic_prime' d.1
      have hJr : IsChevSimple d.1.characteristic (PSimple p J) :=
        Or.inl ⟨TauCeti.CFSGIndex.lie d, by simp [onLie], ⟨e⟩⟩
      have hyN' : Subgroup.zpowers y ≤ Subgroup.normalizer (J : Set G) := Subgroup.zpowers_le.2 hyN
      have hA' : IsElemAbelian p (Subgroup.zpowers y) := by
        refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
        · obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 a.2
          obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 b.2
          apply Subtype.ext
          show (a : G) * b = b * a
          rw [← hm, ← hn]
          exact (Commute.refl y).zpow_zpow m n |>.eq
        · obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hx
          rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hyp, one_zpow]
      have hcen : Subgroup.centralizer ((Subgroup.zpowers y : Subgroup G) : Set G) =
          Subgroup.centralizer ({y} : Set G) := by
        ext g
        simp only [Subgroup.mem_centralizer_iff, SetLike.mem_coe, Set.mem_singleton_iff, forall_eq]
        constructor
        · intro h
          exact h y (Subgroup.mem_zpowers y)
        · intro h z hz
          obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
          exact (Commute.zpow_left (show Commute y g from h) m).eq
      have hKr : IsChevSimple d.1.characteristic (PSimple p K) :=
        hClo p hp hp2 hp hp2 d.1.characteristic hr X J (Subgroup.zpowers y) hX hJ hJr hA' hyN' K
          (by rw [hcen]; exact hK)
      exact Or.inr (hSmall p (J ⊓ Subgroup.centralizer ({y} : Set G)) K A _ hp hp2 hr h2
        (hX.of_le (inf_le_left.trans hJ.1)) hK hKchev hKr hA hinn hcard)

theorem i1416TwoAt_holds {G : Type} [Group G] [Finite G] (hSpor : I1416TwoSpor G) (hSmall : I1416TwoSmall G) :
    I1416TwoAt G :=
  i1416TwoAt_of (fun _ hp hp2 => chevClosureQAt_of_lieComp_lieComps (G := G)
    lieComp_holds (fun _ hq h5 => lieCompsOn_holds hq h5) hp hp2) hSpor hSmall

end Certs


end CFSG.LocalAnalysis.GLTheoremA
