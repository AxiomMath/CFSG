module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.I2611
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIAut

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace FP

open CFSG.LocalAnalysis.GLTheoremA.S10

@[expose] noncomputable def fixNum {R : Type*} [Group R] (α : MulAut R) : ℕ :=
  Nat.card {x : R // α x = x}

section Lift

variable {H : Type*} [Group H]

theorem exists_fixed_lift {Z : Subgroup H} (hZc : Z ≤ Subgroup.center H) [Z.Normal]
    (hZ : Odd (Nat.card Z)) [Finite Z] (α : MulAut H) {k : ℕ} (x : H)
    (hx : ((QuotientGroup.mk x : H ⧸ Z)) ^ (2 ^ k) = 1)
    (hfix : (QuotientGroup.mk (α x) : H ⧸ Z) = QuotientGroup.mk x) :
    ∃ x' : H, α x' = x' ∧ (QuotientGroup.mk x' : H ⧸ Z) = QuotientGroup.mk x := by
  set n : ℕ := 2 ^ k with hn
  have hn1 : 1 ≤ n := Nat.one_le_two_pow
  have hxn : x ^ n ∈ Z := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]; exact hx
  set z : Z := ⟨x ^ n, hxn⟩ with hz
  set d : ℕ := orderOf z with hd
  have hdodd : Odd d := Odd.of_dvd_nat hZ (orderOf_dvd_natCard z)
  have hcop : Nat.Coprime n d := Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hdodd)
  have hd1 : 1 ≤ d := orderOf_pos z
  set u : ℕ := d ^ Nat.totient n with hu
  have hmod : u ≡ 1 [MOD n] := Nat.ModEq.pow_totient hcop.symm
  have hu1 : 1 ≤ u := Nat.one_le_pow _ _ hd1
  have hdu : d ∣ u := dvd_pow_self d (Nat.totient_pos.2 hn1).ne'
  obtain ⟨m, hm⟩ : n ∣ u - 1 := (Nat.modEq_iff_dvd' hu1).1 hmod.symm
  have hum : u = n * m + 1 := by omega
  refine ⟨x ^ u, ?_, ?_⟩
  ·
    have hw : x⁻¹ * α x ∈ Z := QuotientGroup.eq.1 hfix.symm
    set w : H := x⁻¹ * α x with hw'
    have hαx : α x = x * w := by rw [hw']; group
    have hcomm : Commute x w := by
      exact (Subgroup.mem_center_iff.1 (hZc hw)) x
    have h1 : α (x ^ u) = x ^ u * w ^ u := by
      rw [map_pow, hαx, hcomm.mul_pow]
    have hxu : (x ^ u) ^ n = 1 := by
      have : (x ^ u) ^ n = (x ^ n) ^ u := by rw [← pow_mul, ← pow_mul, mul_comm]
      rw [this]
      have hz1 : (x ^ n) ^ d = 1 := by
        have := pow_orderOf_eq_one z
        have h2 := congrArg (fun y : Z => (y : H)) this
        simpa [hz, hd] using h2
      obtain ⟨c, hc⟩ := hdu
      rw [hc, pow_mul, hz1, one_pow]
    have hwu : (w ^ u) ^ n = 1 := by
      have h2 : (α (x ^ u)) ^ n = 1 := by rw [← map_pow, hxu, map_one]
      rw [h1] at h2
      have hc2 : Commute (x ^ u) (w ^ u) := hcomm.pow_pow u u
      rw [hc2.mul_pow, hxu, one_mul] at h2
      exact h2
    set w' : Z := ⟨w ^ u, Subgroup.pow_mem _ hw u⟩ with hw''
    have hw1 : w' = 1 := by
      have h3 : w' ^ n = 1 := Subtype.ext (by simpa [hw''] using hwu)
      have h4 : orderOf w' ∣ n := orderOf_dvd_of_pow_eq_one h3
      have h5 : orderOf w' ∣ Nat.card Z := orderOf_dvd_natCard w'
      have h6 : Nat.Coprime n (Nat.card Z) := by
        rw [hn]; exact Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hZ)
      exact orderOf_eq_one_iff.1 ((Nat.Coprime.coprime_dvd_left h4 h6).eq_one_of_dvd h5)
    have hw2 : w ^ u = 1 := by
      have := congrArg (fun y : Z => (y : H)) hw1
      simpa [hw''] using this
    rw [h1, hw2, mul_one]
  · rw [QuotientGroup.mk_pow, hum, pow_succ, pow_mul, hx, one_pow, one_mul]

end Lift

section Fix

@[expose] def fixSub {R : Type*} [Group R] (α : MulAut R) : Subgroup R :=
  MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id R)

theorem mem_fixSub {R : Type*} [Group R] {α : MulAut R} {x : R} : x ∈ fixSub α ↔ α x = x :=
  Iff.rfl

theorem fixNum_eq_card_fixSub {R : Type*} [Group R] (α : MulAut R) :
    fixNum α = Nat.card (fixSub α) :=
  Nat.card_congr (Equiv.subtypeEquivRight fun _ => mem_fixSub.symm)

open CFSG.ComponentClassification.PerfectAutomorphisms in
theorem twoPart_fixNum_centerQuot {H : Type*} [Group H] [Finite H]
    (hZ : Odd (Nat.card (Subgroup.center H))) (α : MulAut H) :
    twoPart (fixNum α) = twoPart (fixNum (onCenterQuotient α)) := by
  set Z := Subgroup.center H with hZdef
  set ᾱ := onCenterQuotient α with hᾱ
  have hmk : ∀ x : H, ᾱ (QuotientGroup.mk x) = QuotientGroup.mk (α x) := fun x =>
    onCenterQuotient_apply_mk α x
  set C : Subgroup H := fixSub α with hC
  set C' : Subgroup (H ⧸ Z) := fixSub ᾱ with hC'
  rw [fixNum_eq_card_fixSub, fixNum_eq_card_fixSub]
  set f : C →* H ⧸ Z := (QuotientGroup.mk' Z).comp C.subtype with hf
  set D : Subgroup (H ⧸ Z) := f.range with hD
  have hDC' : D ≤ C' := by
    rintro _ ⟨x, rfl⟩
    have hx : α x.1 = x.1 := x.2
    show ᾱ (QuotientGroup.mk x.1) = QuotientGroup.mk x.1
    rw [hmk, hx]
  have hker : Odd (Nat.card f.ker) := by
    have h1 : (f.ker.map C.subtype) ≤ Z := by
      rintro _ ⟨x, hx, rfl⟩
      exact (QuotientGroup.eq_one_iff _).1 hx
    have h2 : Nat.card f.ker ∣ Nat.card Z := by
      calc Nat.card f.ker = Nat.card (f.ker.map C.subtype) :=
            (Subgroup.card_map_of_injective C.subtype_injective).symm
        _ ∣ Nat.card Z := Subgroup.card_dvd_of_le h1
    exact Odd.of_dvd_nat hZ h2
  have hCD : Nat.card C = Nat.card f.ker * Nat.card D := (Subgroup.card_ker_mul_card_range f).symm
  have h2 : twoPart (Nat.card C) = twoPart (Nat.card D) := by
    rw [hCD]
    unfold twoPart
    rw [Nat.factorization_mul (Nat.card_pos (α := f.ker)).ne' (Nat.card_pos (α := D)).ne',
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd (by
        rintro ⟨c, hc⟩
        exact (Nat.not_even_iff_odd.2 hker) ⟨c, by omega⟩), zero_add]
  have h3 : twoPart (Nat.card C') = twoPart (Nat.card D) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨P⟩ : Nonempty (Sylow 2 C') := inferInstance
    have hPD : (P : Subgroup C') ≤ D.subgroupOf C' := by
      intro y hy
      obtain ⟨k, hk⟩ := P.isPGroup' (⟨y, hy⟩ : P)
      have hk' : (y : H ⧸ Z) ^ (2 ^ k) = 1 := by
        have := congrArg (fun t : P => ((t : C') : H ⧸ Z)) hk
        simpa using this
      obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (y : H ⧸ Z)
      have hfix : (QuotientGroup.mk (α x) : H ⧸ Z) = QuotientGroup.mk x := by
        have := mem_fixSub.1 y.2
        rw [← hmk, hx]
        exact this
      obtain ⟨x', hx', hxx'⟩ := exists_fixed_lift (Z := Z) le_rfl hZ α x (k := k) (by rw [hx]; exact hk') hfix
      rw [Subgroup.mem_subgroupOf]
      exact ⟨⟨x', mem_fixSub.2 hx'⟩, by rw [← hx, ← hxx']; rfl⟩
    have h4 : Nat.card P ∣ Nat.card D := by
      have := Subgroup.card_dvd_of_le hPD
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDC').toEquiv] at this
    have h5 : Nat.factorization (Nat.card C') 2 ≤ Nat.factorization (Nat.card D) 2 := by
      have hpow : 2 ^ Nat.factorization (Nat.card C') 2 ∣ Nat.card D := by
        rw [← Sylow.card_eq_multiplicity P]; exact h4
      exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (Nat.card_pos (α := D)).ne').1 hpow
    have h6 : Nat.factorization (Nat.card D) 2 ≤ Nat.factorization (Nat.card C') 2 :=
      (Nat.factorization_le_iff_dvd (Nat.card_pos (α := D)).ne' (Nat.card_pos (α := C')).ne').2
        (Subgroup.card_dvd_of_le hDC') 2
    unfold twoPart
    rw [le_antisymm h5 h6]
  rw [h2, h3]

end Fix

section Link

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.LocalAnalysis.GLTheoremA.MI (indAut)

variable {G : Type} [Group G] [Finite G]

theorem indRel_iff_barAut {p : ℕ} {L : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) (q q' : PQuot p L) :
    indRel p L g q q' ↔ barAut p L ⟨g⁻¹, Subgroup.inv_mem _ hg⟩ q = q' := by
  constructor
  · rintro ⟨l, l', rfl, rfl, hll'⟩
    rw [barAut_mk]
    congr 1
    apply Subtype.ext
    rw [hll']
    show (g⁻¹ : G) * (l : G) * (g⁻¹)⁻¹ = g⁻¹ * l * g
    simp
  · intro h
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    rw [barAut_mk] at h
    subst h
    refine ⟨l, L.normalizerMonoidHom ⟨g⁻¹, Subgroup.inv_mem _ hg⟩ l, rfl, rfl, ?_⟩
    show (g⁻¹ : G) * (l : G) * (g⁻¹)⁻¹ = g⁻¹ * l * g
    simp

theorem card_indRel_fixed_eq {p : ℕ} {L : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) :
    Nat.card {q : PQuot p L // indRel p L g q q} =
      fixNum (barAut p L ⟨g⁻¹, Subgroup.inv_mem _ hg⟩) :=
  Nat.card_congr (Equiv.subtypeEquivRight fun q => indRel_iff_barAut hg q q)

theorem centCard2_eq_twoPart_fixNum {p : ℕ} {L : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G))
    (hZ : Odd (Nat.card (Subgroup.center (PQuot p L)))) :
    centCard2 p L g = twoPart (fixNum (indAut p L g hg)) := by
  unfold centCard2
  rw [card_indRel_fixed_eq hg]
  exact twoPart_fixNum_centerQuot hZ _

theorem odd_card_center_pQuot {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (L : Subgroup G) :
    Odd (Nat.card (Subgroup.center (PQuot p L))) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 (I2611.isPGroup_center_pQuot' hp L)
  rw [hn]
  exact (hp.odd_of_ne_two hp2).pow

theorem twoPart_mul_odd {a b : ℕ} (ha : Odd a) (hb : b ≠ 0) : twoPart (a * b) = twoPart b := by
  unfold twoPart
  rw [Nat.factorization_mul ha.pos.ne' hb, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd (by
      rintro ⟨c, hc⟩
      exact (Nat.not_even_iff_odd.2 ha) ⟨c, by omega⟩), zero_add]

theorem card2_eq_twoPart_card_pSimple {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (L : Subgroup G) :
    card2 p L = twoPart (Nat.card (PSimple p L)) := by
  unfold card2
  have h := Subgroup.card_mul_index (Subgroup.center (PQuot p L))
  rw [Subgroup.index_eq_card] at h
  rw [← h]
  exact twoPart_mul_odd (odd_card_center_pQuot hp hp2 L) Nat.card_pos.ne'

end Link

section Cyclic

theorem mem_zpowers_of_orderOf_eq {M : Type*} [Group M] {f₀ f g : M} {p : ℕ} (hp : 0 < p)
    (hf : f ∈ Subgroup.zpowers f₀) (hg : g ∈ Subgroup.zpowers f₀) (hfo : orderOf f = p)
    (hgo : orderOf g = p) : g ∈ Subgroup.zpowers f := by
  set C : Subgroup M := Subgroup.zpowers f₀ with hC
  let f' : C := ⟨f, hf⟩
  let g' : C := ⟨g, hg⟩
  have hf'o : orderOf f' = p := by rw [← hfo]; exact Subgroup.orderOf_mk f hf
  have hg'o : orderOf g' = p := by rw [← hgo]; exact Subgroup.orderOf_mk g hg
  have hH : Finite (Subgroup.zpowers f') :=
    Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, hf'o]; exact hp.ne')
  have hK : Finite (Subgroup.zpowers g') :=
    Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, hg'o]; exact hp.ne')
  have hcyc : IsCyclic C := inferInstance
  have heq : Subgroup.zpowers f' = Subgroup.zpowers g' := by
    rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers, hf'o, hg'o]
  have hg'mem : g' ∈ Subgroup.zpowers f' := heq ▸ Subgroup.mem_zpowers g'
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hg'mem
  exact Subgroup.mem_zpowers_iff.2 ⟨j, congrArg Subtype.val hj⟩

theorem fix_of_mem_zpowers {R : Type*} [Group R] {f g : MulAut R}
    (hg : g ∈ Subgroup.zpowers f) {x : R} (hx : f x = x) : g x = x := by
  have h : f ∈ MulAction.stabilizer (MulAut R) x := hx
  exact (Subgroup.zpowers_le.2 h) hg

theorem fixNum_eq_of_zpowers {R : Type*} [Group R] {f g : MulAut R}
    (hg : g ∈ Subgroup.zpowers f) (hf : f ∈ Subgroup.zpowers g) : fixNum g = fixNum f :=
  Nat.card_congr (Equiv.subtypeEquivRight fun _ =>
    ⟨fun h => fix_of_mem_zpowers hf h, fun h => fix_of_mem_zpowers hg h⟩)

theorem fixNum_congr {R R' : Type*} [Group R] [Group R'] (σ : R ≃* R') (φ : MulAut R) :
    fixNum (MulAut.congr σ φ) = fixNum φ :=
  (Nat.card_congr (Equiv.subtypeEquiv σ.toEquiv fun x => by
    simp [MulAut.congr_apply])).symm

theorem fixNum_conj {R : Type*} [Group R] (u f : MulAut R) : fixNum (u * f * u⁻¹) = fixNum f :=
  (Nat.card_congr (Equiv.subtypeEquiv u.toEquiv fun x => by
    simp)).symm

theorem fixNum_eq_of_orderOf_eq {R : Type*} [Group R] {f₀ f g : MulAut R} {p : ℕ} (hp : 0 < p)
    (hf : f ∈ Subgroup.zpowers f₀) (hg : g ∈ Subgroup.zpowers f₀) (hfo : orderOf f = p)
    (hgo : orderOf g = p) : fixNum g = fixNum f :=
  fixNum_eq_of_zpowers (mem_zpowers_of_orderOf_eq hp hf hg hfo hgo)
    (mem_zpowers_of_orderOf_eq hp hg hf hgo hfo)

end Cyclic

end FP

end CFSG.LocalAnalysis.GLTheoremA
