module

public import CFSG.LieType.Chevalley.LangFiniteNormalizerOddIndex
public import CFSG.LieType.Chevalley.TorusCoordinates
public import CFSG.LieType.Chevalley.CoordinateFieldBaseChange
public import CFSG.GH74.SectionalRankExtension
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitGen

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.GH74

theorem sectionalTwoRankLE_of_not_two_pow_dvd {X : Type*} [Group X] [Finite X] {r : ℕ}
    (h : ¬ 2 ^ (r + 1) ∣ Nat.card X) : SectionalTwoRankLE X r := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro P hP
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hdvd : 2 ^ k ∣ Nat.card X := hk ▸ Subgroup.card_subgroup_dvd_card P
  have hkr : k ≤ r := by
    by_contra hlt
    exact h ((pow_dvd_pow 2 (by omega)).trans hdvd)
  exact CFSG.ComponentClassification.HSFLit.exists_finset_closure_eq_of_card_le P
    (hk ▸ Nat.pow_le_pow_right (by norm_num) hkr)

theorem sectionalTwoRankLE_of_odd_index {X : Type*} [Group X] [Finite X] (N : Subgroup X)
    (hN : Odd N.index) {r : ℕ} (h : SectionalTwoRankLE N r) : SectionalTwoRankLE X r := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro P hP
  have hcard : ¬ 2 ∣ Nat.card (X ⧸ N) := by
    rw [← Subgroup.index_eq_card]
    exact Nat.two_dvd_ne_zero.2 (Nat.odd_iff.1 hN)
  obtain ⟨Q, hQ⟩ := hP.nonempty_fixed_point_of_prime_not_dvd_card (X ⧸ N) hcard
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective Q
  have hfix : ∀ p ∈ P, g⁻¹ * p * g ∈ N := by
    intro p hp
    have h1 := hQ ⟨p, hp⟩
    change ((p * g : X) : X ⧸ N) = (g : X ⧸ N) at h1
    rw [QuotientGroup.eq] at h1
    have h2 := inv_mem h1
    simpa [mul_assoc] using h2
  let f : N →* X := (MulAut.conj g).toMonoidHom.comp N.subtype
  have hf : Function.Injective f := (MulAut.conj g).injective.comp Subtype.val_injective
  have hrange : P ≤ f.range := by
    intro p hp
    refine ⟨⟨g⁻¹ * p * g, hfix p hp⟩, ?_⟩
    simp [f, mul_assoc]
  obtain ⟨s, hs, hsP⟩ := h (P.comap f) (hP.comap_of_injective f hf)
  refine ⟨s.image f, Finset.card_image_le.trans hs, ?_⟩
  rw [Finset.coe_image, ← MonoidHom.map_closure, hsP, Subgroup.map_comap_eq,
    inf_eq_right.mpr hrange]

theorem sectionalTwoRankLE_pi {G : Type*} [Group G] [Finite G] {a : ℕ}
    (hG : SectionalTwoRankLE G a) : ∀ n : ℕ, SectionalTwoRankLE (Fin n → G) (n * a)
  | 0 => sectionalTwoRankLE_of_not_two_pow_dvd (by simp)
  | n + 1 => by
    have h := hG.prod (sectionalTwoRankLE_pi hG n)
    let e : (Fin (n + 1) → G) →* G × (Fin n → G) :=
      (Pi.evalMonoidHom (fun _ => G) 0).prod
        (Pi.monoidHom fun i : Fin n => Pi.evalMonoidHom (fun _ => G) i.succ)
    have he : Function.Injective e := by
      intro x y hxy
      have h0 : x 0 = y 0 := congrArg Prod.fst hxy
      have hs : ∀ i : Fin n, x i.succ = y i.succ := fun i => congrFun (congrArg Prod.snd hxy) i
      funext i
      refine Fin.cases h0 (fun i => hs i) i
    rw [show (n + 1) * a = a + n * a by ring]
    exact SectionalTwoRankLE.of_injective e he h

theorem sectionalTwoRankLE_torusGroup
    (τ : Tag) (R : Type) [Field R] [Finite R] : SectionalTwoRankLE (torusGroup τ R) τ.rank := by
  have h := sectionalTwoRankLE_pi (SectionalTwoRankLE.units R) τ.rank
  rw [mul_one] at h
  exact SectionalTwoRankLE.of_surjective (torusCoordHom τ R) torusCoordHom_surjective h

theorem sectionalTwoRankLE_monomialSubgroup
    (τ : Tag) (R : Type) [Field R]
    [Finite R] {r : ℕ} (hW : SectionalTwoRankLE (WeylGroup τ) r) :
    SectionalTwoRankLE (monomialSubgroup τ R) (τ.rank + r) := by
  haveI := finite_modGL (τ := τ) (K := R)
  obtain ⟨-, ⟨ρ, hρs, -, -, -, hker⟩, -⟩ := Weyl_normalizer_quotient τ R
  have hle : torusGroup τ R ≤ monomialSubgroup τ R := le_sup_left
  have hN : SectionalTwoRankLE ρ.ker τ.rank := by
    rw [hker]
    exact SectionalTwoRankLE.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hle).symm
      (sectionalTwoRankLE_torusGroup τ R)
  have hQ : SectionalTwoRankLE (monomialSubgroup τ R ⧸ ρ.ker) r :=
    SectionalTwoRankLE.of_mulEquiv (QuotientGroup.quotientKerEquivOfSurjective ρ hρs).symm hW
  exact SectionalTwoRankLE.of_normal ρ.ker hN hQ

private theorem card_pow_totient_modEq {q : ℕ} (hq : Odd q) (M : ℕ) :
    q ^ Nat.totient (2 ^ M) ≡ 1 [MOD 2 ^ M] :=
  Nat.ModEq.pow_totient (Nat.Coprime.pow_right M (Nat.coprime_two_right.2 hq))

theorem sectionalTwoRankLE_adjointGroup
    (τ : Tag) {r : ℕ} (hW : SectionalTwoRankLE (WeylGroup τ) r) (K : Type) [Field K] [Finite K]
    (hK : Odd (Nat.card K)) : SectionalTwoRankLE (adjointGroup τ K) (τ.rank + r) := by
  classical
  haveI : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K (ringChar K)⟩
  set M := Nat.card (WeylGroup τ) with hMdef
  have hM : 1 ≤ M := Nat.card_pos
  haveI : NeZero (Nat.totient (2 ^ M)) :=
    ⟨(Nat.totient_pos.2 (pow_pos (by norm_num) M)).ne'⟩
  let L := FiniteField.Extension K (ringChar K) (Nat.totient (2 ^ M))
  have hL : Nat.card L = Nat.card K ^ Nat.totient (2 ^ M) := FiniteField.natCard_extension _ _ _
  have hLodd : Odd (Nat.card L) := hL ▸ hK.pow
  have hLM : Nat.card L ≡ 1 [MOD 2 ^ M] := hL ▸ card_pow_totient_modEq hK M
  have hWM : ¬ 2 ^ M ∣ Nat.card (WeylGroup τ) := fun h =>
    absurd (Nat.le_of_dvd Nat.card_pos h) (not_le.2 (Nat.lt_two_pow_self))
  have hodd := (exceptional_Lang_finite_normalizer_odd_index_involutions τ L hLodd hM hLM hWM).1
  haveI := finite_modGL (τ := τ) (K := L)
  have hNC : monomialSubgroup τ L ≤ adjointGroup τ L := monomialSubgroup_le_adjointGroup'
  have hCL : SectionalTwoRankLE (adjointGroup τ L) (τ.rank + r) :=
    sectionalTwoRankLE_of_odd_index ((monomialSubgroup τ L).subgroupOf (adjointGroup τ L)) hodd
      (SectionalTwoRankLE.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hNC).symm
        (sectionalTwoRankLE_monomialSubgroup τ L hW))
  have hmem : ∀ g ∈ adjointGroup τ K,
      baseChangeGL (algebraMap K L) g ∈ adjointGroup τ L := by
    intro g hg
    have hle : (adjointGroup τ K).map (baseChangeGL (algebraMap K L)) ≤ adjointGroup τ L := by
      rw [map_baseChangeGL_adjointGroup, Subgroup.closure_le]
      rintro _ ⟨i, c, rfl | rfl⟩
      exacts [xUnit_mem_adjointGroup i _, yUnit_mem_adjointGroup i _]
    exact hle (Subgroup.mem_map_of_mem _ hg)
  let f : adjointGroup τ K →* adjointGroup τ L :=
    ((baseChangeGL (algebraMap K L)).comp (adjointGroup τ K).subtype).codRestrict _
      fun g => hmem g g.2
  have hf : Function.Injective f := fun g g' h =>
    Subtype.ext (baseChangeGL_injective (algebraMap K L) (congrArg Subtype.val h))
  exact SectionalTwoRankLE.of_injective f hf hCL

theorem sectionalTwoRankLE_of_untwistedChevalleyModel
    {G : Type} [Group G] {τ : Tag} {q r : ℕ} (hW : SectionalTwoRankLE (WeylGroup τ) r)
    (hq : Odd q) (h : UntwistedChevalleyModel G τ q) : SectionalTwoRankLE G (τ.rank + r) := by
  obtain ⟨K, hfield, hfin, hcard, ⟨e⟩⟩ := h
  letI : Field K := hfield
  haveI : Finite K := hfin
  haveI := finite_modGL (τ := τ) (K := K)
  have hA := sectionalTwoRankLE_adjointGroup τ hW K (hcard ▸ hq)
  exact SectionalTwoRankLE.of_mulEquiv e.symm
    (SectionalTwoRankLE.quotient (Subgroup.center ↥(adjointGroup τ K)) hA)

theorem sectionalTwoRankLE_of_twistedChevalleyModel
    {G : Type} [Group G] {t : TwistTag} {q r : ℕ} (hW : SectionalTwoRankLE (WeylGroup t.tag) r)
    (hq : Odd q) (h : TwistedChevalleyModel G t q) : SectionalTwoRankLE G (t.tag.rank + r) := by
  obtain ⟨K, hfield, hfin, hcard, σ, -, ⟨e⟩⟩ := h
  letI : Field K := hfield
  haveI : Finite K := hfin
  haveI := finite_modGL (τ := t.tag) (K := K)
  have hA := sectionalTwoRankLE_adjointGroup t.tag hW K (hcard ▸ hq.pow)
  set H := twistedFixedGroup t K σ
  have hHH : ⁅H, H⁆ ≤ H := Subgroup.commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)
  have hle : ⁅H, H⁆ ≤ adjointGroup t.tag K := hHH.trans inf_le_left
  have hD : SectionalTwoRankLE ↥⁅H, H⁆ (t.tag.rank + r) :=
    SectionalTwoRankLE.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle) hA
  exact SectionalTwoRankLE.of_mulEquiv e.symm
    (SectionalTwoRankLE.quotient (Subgroup.center ↥⁅H, H⁆) hD)

end CFSG.LieType.Chevalley

end
