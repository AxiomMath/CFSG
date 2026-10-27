module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE7Three22
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE7Three17
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Rk2Six
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE6Three7
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE6Three

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE7Three

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KA5L CFSG.RankThree.Classical2 CFSG.Open
  CFSG.RankThree.PartOne.KLR CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.E6
  CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7
  CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE6Three
open scoped Matrix MatrixGroups Pointwise


private theorem exists_e7T3_conjugator {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    {L : Type} [Field L] [Algebra K L] [CharP L 2] {f : ℕ} {ε : ℤ}
    (F : E7ThreeFrame K L 2 f p ε)
    (A : Subgroup (adjointGroup Tag.E7 K)) (hA : IsElemAbelian p A) :
    ∃ c : adjointGroup Tag.E7 K, ∀ x ∈ A,
      F.g0⁻¹ * adjEmb Tag.E7 K L (c * x * c⁻¹) * F.g0 ∈
        twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L 2 f))) := by
  exact F.hconj A hA.isPGroup

private theorem concl165_e7_split (K : Type) [Field K] [Finite K] [CharP K 2]
    (n p q : ℕ) (hcard : Nat.card K = 2 ^ n) (hn : 1 ≤ n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : 3 < p)
    (hpf : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + (Nat.card K : ℤ) + 1)
    (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p)
    (hqdiv : q ∣ 2 ^ n - 1 ∨ n = 1 ∧ q = 3)
    (Ã : Subgroup (adjointGroup Tag.E7 K)) (hAe : IsElemAbelian p Ã)
    (hΩ : ∀ g ∈ Subgroup.centralizer (Ã : Set (adjointGroup Tag.E7 K)),
      orderOf g = p → g ∈ Ã)
    (hA3 : 3 ≤ CFSG.Open.pRank p Ã) :
    Concl165 (adjointGroup Tag.E7 K) p q Ã := by
  classical
  let L := AlgebraicClosure K
  haveI : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨F⟩ := exists_e7ThreeFrame (K := K) (ℓ := 2) (f := n) (p := p) (L := L)
    hn hcard hp hp3 (Or.inl rfl) (by simpa using hpf)
  have hpL : (p : L) ≠ 0 := by
    rw [ne_eq, CharP.cast_eq_zero_iff L 2]
    exact fun h => hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h).symm
  obtain ⟨ζ, hζord⟩ := CFSG.exists_unit_orderOf_eq_of_isAlgClosed (k := L) (n := p) hpL
  have hζ : IsPrimitiveRoot ζ p := IsPrimitiveRoot.iff_orderOf.2 hζord
  obtain ⟨c, hc⟩ := exists_e7T3_conjugator hp F Ã hAe
  let A' : Subgroup (adjointGroup Tag.E7 K) := Ã.map (MulAut.conj c).toMonoidHom
  have hAe' : IsElemAbelian p A' := hAe.map (MulAut.conj c).toMonoidHom
  have hAfix' : ∀ y ∈ A', F.g0⁻¹ * adjEmb Tag.E7 K L y * F.g0 ∈
      twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L 2 n))) := by
    rintro y hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hy
    exact hc a ha
  have hΩ' : ∀ g ∈ Subgroup.centralizer (A' : Set (adjointGroup Tag.E7 K)),
      orderOf g = p → g ∈ A' := by
    rintro g hg hgord
    have hg0C : c⁻¹ * g * c ∈ Subgroup.centralizer (Ã : Set (adjointGroup Tag.E7 K)) := by
      rw [Subgroup.mem_centralizer_iff] at hg ⊢
      intro a ha
      have ha' : c * a * c⁻¹ ∈ A' := Subgroup.mem_map.mpr ⟨a, ha, by rfl⟩
      have h := hg (c * a * c⁻¹) ha'
      apply (MulAut.conj c).injective
      calc c * (a * (c⁻¹ * g * c)) * c⁻¹ = (c * a * c⁻¹) * g := by group
        _ = g * (c * a * c⁻¹) := h
        _ = c * ((c⁻¹ * g * c) * a) * c⁻¹ := by group
    have hg0ord : orderOf (c⁻¹ * g * c) = p := by
      rw [show c⁻¹ * g * c = MulAut.conj c⁻¹ g by simp [MulAut.conj_apply]]
      exact (orderOf_injective (MulAut.conj c⁻¹).toMonoidHom
        (MulAut.conj c⁻¹).injective g).trans hgord
    have hg0A : c⁻¹ * g * c ∈ Ã := hΩ _ hg0C hg0ord
    have hg : g = c * (c⁻¹ * g * c) * c⁻¹ := by group
    rw [hg]
    exact Subgroup.mem_map.mpr ⟨c⁻¹ * g * c, hg0A, by simp [MulAut.conj_apply]⟩
  haveI : Finite ↥(adjointGroup Tag.E7 K) := inferInstance
  have hcardÃ : Nat.card Ã = p ^ CFSG.Open.pRank p Ã :=
    CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian hp hAe
  have hcardA' : Nat.card A' = Nat.card Ã :=
    Subgroup.card_map_of_injective (MulAut.conj c).injective
  have hAcard' : p ^ 3 ≤ Nat.card A' := by
    rw [hcardA', hcardÃ]
    exact Nat.pow_le_pow_right hp.pos hA3
  obtain ⟨x, hxA', hxord, hxpsi⟩ :=
    exists_mem_selection (F := F) (ℓ := 2) (f := n) (p := p) (ε := 1)
      hn hcard hp hp3 (Or.inl rfl) (by simpa using hpf) hζ hΩ'
      (c := 1) (fun y hy => by simpa using hAfix' y hy)
  have hxcol : F.g0⁻¹ * adjEmb Tag.E7 K L x * F.g0 =
      rootDiagUnit Tag.E7 (fun i => ζ ^
        (e7T3XColumn 1 (Nat.card K : ZMod p) i).val) := by
    simpa [psiC_apply] using hxpsi
  obtain ⟨z, hzA', hzx, hzframe, hker⟩ :=
    exists_selection_secondPoint_explicit (F := F) (ℓ := 2) (f := n) (p := p) (ε := 1)
      hn hcard hp hp3 (Or.inl rfl) (by simpa using hpf) hAe' hAcard' (by simpa using hAfix')
      hxA' hζ hxcol
  have hxz : Commute x z := hAe'.comm hxA' hzA'
  obtain ⟨J, Φ', Q, hJx, hJn, hJq, hpJ, ⟨H, hH⟩, ⟨ρ, hρs, hρc, hρk⟩,
    hQJ, hQz, hQn, hQq, hpQ⟩ :=
    exists_e7T3_JQ_split (F := F) (ℓ := 2) (f := n) (p := p) hn hcard hp hp3 hpf
      hxz hxord hζ hxcol hzframe hker
  obtain ⟨Fq, hFqel, hFqx, hFqJ, hFq3⟩ :=
    exists_elemAbelian_pRank_three_of_a5Layer_split_le (K := K) (L := L) (n := n)
      hH hcard hJx ρ hρs hρc hρk hq hq2 hqdiv
  have hx1 : x ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hxord
    exact hp.ne_one hxord.symm
  have hC : Concl165 (adjointGroup Tag.E7 K) p q A' :=
    concl165_of_layers hp hAe' hxA' hzA' hx1 hzx hJx hJn hJq hpJ hQJ hQz hQn hQq hpQ
      hFqel hFqx hFqJ hFq3
  exact concl165_of_conj hp hq c hC

theorem e7Model165At_three : E7Model165At 3 := by
  intro K hField hFinite hChar n p q hcard hn hp hp2 hrk hq hq2 hqp hqdiv Ã hAe hΩ hmax hA3
  letI : Field K := hField
  letI : Finite K := hFinite
  letI : CharP K 2 := hChar
  have hp3 : 3 < p := three_lt_of_card hcard hp hp2 hrk
  have hpf : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + (Nat.card K : ℤ) + 1 :=
    three_dvd_card_sq_add_int hcard hp hp2 hrk
  exact concl165_e7_split K n p q hcard hn hp hp2 hp3 hpf hq hq2 hqp hqdiv Ã hAe hΩ hA3

private theorem concl165_e7_unitary (K : Type) [Field K] [Finite K] [CharP K 2]
    (n p q : ℕ) (hcard : Nat.card K = 2 ^ n) (hn : 1 ≤ n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : 3 < p) (hn2 : 2 < 2 ^ n)
    (hpf : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + (-1) * (Nat.card K : ℤ) + 1)
    (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p)
    (hqdiv : q ∣ 2 ^ n - 1)
    (Ã : Subgroup (adjointGroup Tag.E7 K)) (hAe : IsElemAbelian p Ã)
    (hΩ : ∀ g ∈ Subgroup.centralizer (Ã : Set (adjointGroup Tag.E7 K)),
      orderOf g = p → g ∈ Ã)
    (hA3 : 3 ≤ CFSG.Open.pRank p Ã) :
    Concl165 (adjointGroup Tag.E7 K) p q Ã := by
  classical
  let L := AlgebraicClosure K
  haveI : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨F⟩ := exists_e7ThreeFrame (K := K) (ℓ := 2) (f := n) (p := p) (L := L)
    hn hcard hp hp3 (Or.inr rfl) (by simpa using hpf)
  have hpL : (p : L) ≠ 0 := by
    rw [ne_eq, CharP.cast_eq_zero_iff L 2]
    exact fun h => hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h).symm
  obtain ⟨ζ, hζord⟩ := CFSG.exists_unit_orderOf_eq_of_isAlgClosed (k := L) (n := p) hpL
  have hζ : IsPrimitiveRoot ζ p := IsPrimitiveRoot.iff_orderOf.2 hζord
  obtain ⟨c, hc⟩ := exists_e7T3_conjugator hp F Ã hAe
  let A' : Subgroup (adjointGroup Tag.E7 K) := Ã.map (MulAut.conj c).toMonoidHom
  have hAe' : IsElemAbelian p A' := hAe.map (MulAut.conj c).toMonoidHom
  have hAfix' : ∀ y ∈ A', F.g0⁻¹ * adjEmb Tag.E7 K L y * F.g0 ∈
      twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L 2 n))) := by
    rintro y hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hy
    exact hc a ha
  have hΩ' : ∀ g ∈ Subgroup.centralizer (A' : Set (adjointGroup Tag.E7 K)),
      orderOf g = p → g ∈ A' := by
    rintro g hg hgord
    have hg0C : c⁻¹ * g * c ∈ Subgroup.centralizer (Ã : Set (adjointGroup Tag.E7 K)) := by
      rw [Subgroup.mem_centralizer_iff] at hg ⊢
      intro a ha
      have ha' : c * a * c⁻¹ ∈ A' := Subgroup.mem_map.mpr ⟨a, ha, by rfl⟩
      have h := hg (c * a * c⁻¹) ha'
      apply (MulAut.conj c).injective
      calc c * (a * (c⁻¹ * g * c)) * c⁻¹ = (c * a * c⁻¹) * g := by group
        _ = g * (c * a * c⁻¹) := h
        _ = c * ((c⁻¹ * g * c) * a) * c⁻¹ := by group
    have hg0ord : orderOf (c⁻¹ * g * c) = p := by
      rw [show c⁻¹ * g * c = MulAut.conj c⁻¹ g by simp [MulAut.conj_apply]]
      exact (orderOf_injective (MulAut.conj c⁻¹).toMonoidHom
        (MulAut.conj c⁻¹).injective g).trans hgord
    have hg0A : c⁻¹ * g * c ∈ Ã := hΩ _ hg0C hg0ord
    have hg : g = c * (c⁻¹ * g * c) * c⁻¹ := by group
    rw [hg]
    exact Subgroup.mem_map.mpr ⟨c⁻¹ * g * c, hg0A, by simp [MulAut.conj_apply]⟩
  haveI : Finite ↥(adjointGroup Tag.E7 K) := inferInstance
  have hcardÃ : Nat.card Ã = p ^ CFSG.Open.pRank p Ã :=
    CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian hp hAe
  have hcardA' : Nat.card A' = Nat.card Ã :=
    Subgroup.card_map_of_injective (MulAut.conj c).injective
  have hAcard' : p ^ 3 ≤ Nat.card A' := by
    rw [hcardA', hcardÃ]
    exact Nat.pow_le_pow_right hp.pos hA3
  obtain ⟨x, hxA', hxord, hxpsi⟩ :=
    exists_mem_selection (F := F) (ℓ := 2) (f := n) (p := p) (ε := -1)
      hn hcard hp hp3 (Or.inr rfl) (by simpa using hpf) hζ hΩ'
      (c := 1) (fun y hy => by simpa using hAfix' y hy)
  have hxcol : F.g0⁻¹ * adjEmb Tag.E7 K L x * F.g0 =
      rootDiagUnit Tag.E7 (fun i => ζ ^
        (e7T3XColumn (-1) (Nat.card K : ZMod p) i).val) := by
    simpa [psiC_apply] using hxpsi
  obtain ⟨z, hzA', hzx, hzframe, hker⟩ :=
    exists_selection_secondPoint_explicit (F := F) (ℓ := 2) (f := n) (p := p) (ε := -1)
      hn hcard hp hp3 (Or.inr rfl) (by simpa using hpf) hAe' hAcard' (by simpa using hAfix')
      hxA' hζ hxcol
  have hxz : Commute x z := hAe'.comm hxA' hzA'
  obtain ⟨J, Φ', Q, hJx, hJn, hJq, hpJ, ⟨H, hH⟩, ⟨ρ, hρs, hρc, hρk⟩,
    hQJ, hQz, hQn, hQq, hpQ⟩ :=
    exists_e7T3_JQ_unitary (F := F) (ℓ := 2) (f := n) (p := p) hn hcard hp hp3 hn2
      (by simpa using hpf) hxz hxord hζ hxcol hzframe hker
  obtain ⟨Fq, hFqel, hFqx, hFqJ, hFq3⟩ :=
    exists_elemAbelian_pRank_three_of_a5Layer_unitary_le (K := K) (L := L) (ℓ := 2) (f := n)
      rfl hcard hH hcard hJx ρ hρs hρc hρk hq hq2 hqdiv
  have hx1 : x ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hxord
    exact hp.ne_one hxord.symm
  have hC : Concl165 (adjointGroup Tag.E7 K) p q A' :=
    concl165_of_layers hp hAe' hxA' hzA' hx1 hzx hJx hJn hJq hpJ hQJ hQz hQn hQq hpQ
      hFqel hFqx hFqJ hFq3
  exact concl165_of_conj hp hq c hC

theorem e7Model165At_six : E7Model165At 6 := by
  intro K hField hFinite hChar n p q hcard hn hp hp2 hrk hq hq2 hqp hqdiv Ã hAe hΩ hmax hA3
  letI : Field K := hField
  letI : Finite K := hFinite
  letI : CharP K 2 := hChar
  have hp3 : 3 < p := by
    have := seven_le_of_rk2Ord_six hp hp2 hrk
    omega
  have hn2 : 2 < 2 ^ n := two_lt_two_pow_of_rk2Ord_six hp hp2 hrk
  have hpf : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + (-1) * (Nat.card K : ℤ) + 1 := by
    have h : p ∣ (2 ^ n) ^ 2 - 2 ^ n + 1 := dvd_two_pow_sq_sub_of_rk2Ord_six hp hp2 hrk
    have hle : 2 ^ n ≤ (2 ^ n) ^ 2 := by
      have h2 : 2 ≤ 2 ^ n := by
        calc (2 : ℕ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      nlinarith
    have hcast : ((2 ^ n : ℤ) ^ 2 - (2 ^ n : ℤ) + 1) =
        ((2 ^ n) ^ 2 - 2 ^ n + 1 : ℕ) := by
      rw [Nat.cast_add, Nat.cast_sub hle]
      push_cast
      ring
    have h' : (p : ℤ) ∣ (2 ^ n : ℤ) ^ 2 - (2 ^ n : ℤ) + 1 := by
      rw [hcast]
      exact_mod_cast h
    rw [hcard]
    rwa [show (((2 ^ n : ℕ) : ℤ) ^ 2 + (-1) * (((2 ^ n : ℕ) : ℤ)) + 1) =
      (2 ^ n : ℤ) ^ 2 - (2 ^ n : ℤ) + 1 by push_cast; ring]
  have hqdiv' : q ∣ 2 ^ n - 1 := by
    rcases hqdiv with h | ⟨h1, h2⟩
    · exact h
    · exfalso
      rw [h1] at hn2
      norm_num at hn2
  exact concl165_e7_unitary K n p q hcard hn hp hp2 hp3 hn2 hpf hq hq2 hqp hqdiv' Ã hAe hΩ hA3

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE7Three
