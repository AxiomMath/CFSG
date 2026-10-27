module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MTailRed
import CFSG.GroupTheory.Frattini.PSubgroupLift
import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.FieldBonusIso

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

@[expose] def T158RankU6 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (n : ℕ), Odd n → 1 < n → CFSG.Open.IsQuasisimple Y →
    catalogIs (Y ⧸ Subgroup.center Y) (S10.isU6n n) →
      ∃ F : Subgroup Y, IsElemAbelian 3 F ∧ Nat.card F = 3 ^ 4 ∧ F ⊓ Subgroup.center Y = ⊥

@[expose] def T158RankTE6 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (n : ℕ), Odd n → 1 < n → CFSG.Open.IsQuasisimple Y →
    catalogIs (Y ⧸ Subgroup.center Y) (S10.isTE6n n) →
      ∃ F : Subgroup Y, IsElemAbelian 3 F ∧ Nat.card F = 3 ^ 5 ∧ F ⊓ Subgroup.center Y = ⊥

section Faith

variable {X : Type} [Group X] [Finite X]

private theorem core_le (K : Subgroup X) : GLAPPrimeCoreOf 3 K ≤ K :=
  Subgroup.map_subtype_le _

private theorem not_dvd_card_core (K : Subgroup X) : ¬ 3 ∣ Nat.card (GLAPPrimeCoreOf 3 K) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have e : Nat.card (GLAPPrimeCoreOf 3 K) = Nat.card (CFSG.pPrimeCore 3 ↥K) :=
    Nat.card_congr (Subgroup.equivMapOfInjective _ K.subtype K.subtype_injective).toEquiv.symm
  rw [e]
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥K))

private theorem le_normalizer_of_conj_mem {E T : Subgroup X}
    (h : ∀ e ∈ E, ∀ t ∈ T, e * t * e⁻¹ ∈ T) : E ≤ Subgroup.normalizer (T : Set X) := by
  intro e he
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => h e he x hx, fun hx => ?_⟩
  have := h e⁻¹ (E.inv_mem he) (e * x * e⁻¹) hx
  simpa [mul_assoc] using this

private theorem card_map_of_inf_ker {L H : Type*} [Group L] [Group H] {f : L →* H} {A : Subgroup L}
    (h : A ⊓ f.ker = ⊥) : Nat.card (A.map f) = Nat.card A := by
  have hinj : Function.Injective (f.comp A.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at ha
    have hmem : (a : L) ∈ A ⊓ f.ker := ⟨a.2, ha⟩
    rw [h] at hmem
    exact (Subgroup.mem_bot).2 (Subtype.ext hmem)
  have hr : (f.comp A.subtype).range = A.map f := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hr]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

private theorem conj_mem_sup {T O : Subgroup X} {g : X} (hT : ∀ t ∈ T, g * t * g⁻¹ ∈ T ⊔ O)
    (hO : ∀ o ∈ O, g * o * g⁻¹ ∈ T ⊔ O) : ∀ y ∈ T ⊔ O, g * y * g⁻¹ ∈ T ⊔ O := by
  intro y hy
  have hle : (T ⊔ O).map (MulAut.conj g).toMonoidHom ≤ T ⊔ O := by
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨t, ht, rfl⟩
      exact hT t ht
    · rintro _ ⟨o, ho, rfl⟩
      exact hO o ho
  exact hle ⟨y, hy, rfl⟩

theorem pow_mul_card_le_of_faith {K B T : Subgroup X} (hB : IsElemAbelian 3 B)
    (hBK : B ≤ Subgroup.normalizer (K : Set X)) (hT2 : IsPGroup 2 T) (hT1 : T ≠ ⊥)
    (hBT : B ≤ Subgroup.normalizer (T : Set X)) (hTc : T ≤ centModSubgroup 3 K) {e : ℕ}
    (hF : ∃ F : Subgroup (PQuot 3 K), IsElemAbelian 3 F ∧ Nat.card F = 3 ^ e ∧
      F ⊓ Subgroup.center (PQuot 3 K) = ⊥) :
    3 ^ e * Nat.card ↥(B ⊓ centModSubgroup 3 K) ≤ 3 ^ GLATwoLocalRank 3 X := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O : Subgroup X := GLAPPrimeCoreOf 3 K with hOdef
  set B₀ : Subgroup X := B ⊓ centModSubgroup 3 K with hB₀def
  have hOK : O ≤ K := core_le K
  have hO3 : ¬ 3 ∣ Nat.card O := not_dvd_card_core K
  have hNO : Subgroup.normalizer (K : Set X) ≤ Subgroup.normalizer (O : Set X) :=
    normalizer_le_normalizer_glaPPrimeCoreOf 3 K
  have hcentN : centModSubgroup 3 K ≤ Subgroup.normalizer (K : Set X) := fun g hg => hg.1
  have hTK : T ≤ Subgroup.normalizer (K : Set X) := hTc.trans hcentN
  have hTO : T ≤ Subgroup.normalizer (O : Set X) := hTK.trans hNO
  set Y : Subgroup X := T ⊔ O with hYdef
  have hT3 : ¬ 3 ∣ Nat.card T := by
    intro h
    obtain ⟨k, hk⟩ := hT2.exists_card_eq
    rw [hk] at h
    exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h)) (by norm_num)
  have hY3 : ¬ 3 ∣ Nat.card Y := by
    intro h
    have hmul :=
      CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf hTO
    have h3 : 3 ∣ Nat.card T * Nat.card O := by
      rw [← hmul]
      exact dvd_mul_of_dvd_left h _
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3 with h' | h'
    · exact hT3 h'
    · exact hO3 h'
  have hKY : K ≤ Subgroup.normalizer (Y : Set X) := by
    refine le_normalizer_of_conj_mem fun k hk y hy => ?_
    have hkO : k ∈ Subgroup.normalizer (O : Set X) := hNO (Subgroup.le_normalizer hk)
    refine conj_mem_sup (fun t ht => ?_) (fun o ho => ?_) y hy
    ·
      have hc : ⁅k, t⁆ ∈ O := (hTc ht).2 k hk
      have e : k * t * k⁻¹ = ⁅k, t⁆ * t := by rw [commutatorElement_def]; group
      rw [e]
      exact Y.mul_mem (Subgroup.mem_sup_right hc) (Subgroup.mem_sup_left ht)
    · exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp hkO o).mp ho)
  have hBY : B ≤ Subgroup.normalizer (Y : Set X) := by
    refine le_normalizer_of_conj_mem fun b hb y hy => ?_
    have hbO : b ∈ Subgroup.normalizer (O : Set X) := hNO (hBK hb)
    refine conj_mem_sup (fun t ht => ?_) (fun o ho => ?_) y hy
    · exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (hBT hb) t).mp ht)
    · exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp hbO o).mp ho)
  have hB₀N : B₀ ≤ Subgroup.normalizer (K : Set X) := inf_le_right.trans hcentN
  have hB₀3 : IsPGroup 3 B₀ := (hB.mono inf_le_left).isPGroup
  set C : Subgroup X := K ⊓ Subgroup.centralizer (B₀ : Set X) with hCdef
  let ι : ↥C →* ↥K := Subgroup.inclusion inf_le_left
  have hι : Function.Injective ι := Subgroup.inclusion_injective _
  let f : ↥C →* PQuot 3 K := (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K)).comp ι
  have hmemO : ∀ z : ↥K, (z : X) ∈ O ↔ z ∈ GLAPPrimeCore 3 ↥K := fun z =>
    Subgroup.mem_map_iff_mem K.subtype_injective
  have hfsurj : Function.Surjective f := by
    intro q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥K) q
    let α : ↥B₀ →* MulAut ↥K := (K.normalizerMonoidHom).comp (Subgroup.inclusion hB₀N)
    have hα : ∀ (a : ↥B₀) (x : ↥K), ((α a x : ↥K) : X) = (a : X) * x * (a : X)⁻¹ := fun _ _ => rfl
    have hcop : ¬ 3 ∣ Nat.card (GLAPPrimeCore 3 ↥K) := by
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
        (CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥K))
    obtain ⟨c, hc, hfix⟩ := (CFSG.Semidihedral.Principal.coprime_invariant_coset_fixed 3 hB₀3 α
      (GLAPPrimeCore 3 ↥K) hcop k).1 (by
        intro a x hx
        have hax : ((α a x * x⁻¹ : ↥K) : X) = ⁅(a : X), (x : X)⁆ := by
          rw [Subgroup.coe_mul, hα, Subgroup.coe_inv, commutatorElement_def]
        have hcomm : ⁅(a : X), (x : X)⁆ ∈ O := by
          have h1 : ⁅(x : X), (a : X)⁆ ∈ O := ((show B₀ ≤ centModSubgroup 3 K from inf_le_right) a.2).2 x x.2
          have e : ⁅(a : X), (x : X)⁆ = ⁅(x : X), (a : X)⁆⁻¹ := by
            rw [commutatorElement_inv]
          rw [e]
          exact O.inv_mem h1
        have h2 : α a x * x⁻¹ ∈ GLAPPrimeCore 3 ↥K := (hmemO _).1 (by rw [hax]; exact hcomm)
        have e2 : α a x * k⁻¹ = (α a x * x⁻¹) * (x * k⁻¹) := by group
        rw [e2]
        exact Subgroup.mul_mem _ h2 hx)
    have hcC : (c : X) ∈ C := by
      refine Subgroup.mem_inf.mpr ⟨c.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have h := congrArg (fun z : ↥K => (z : X)) (hfix ⟨b, hb⟩)
      simp only [hα] at h
      calc b * (c : X) = b * c * b⁻¹ * b := by group
        _ = c * b := by rw [h]
    refine ⟨⟨c, hcC⟩, ?_⟩
    change (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K)) (ι ⟨c, hcC⟩) = QuotientGroup.mk' _ k
    have hιc : ι ⟨c, hcC⟩ = c := rfl
    rw [hιc, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_iff_div_mem,
      div_eq_mul_inv]
    exact hc
  have hfker : ¬ 3 ∣ Nat.card f.ker := by
    intro h
    have hle : f.ker.map ι ≤ GLAPPrimeCore 3 ↥K := by
      rintro _ ⟨z, hz, rfl⟩
      have hz' : (QuotientGroup.mk (ι z) : PQuot 3 K) = 1 := hz
      exact (QuotientGroup.eq_one_iff (ι z)).mp hz'
    have hcard : Nat.card (f.ker.map ι) = Nat.card f.ker :=
      Nat.card_congr (Subgroup.equivMapOfInjective _ ι hι).toEquiv.symm
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [hcard] at hdvd
    have hcop : ¬ 3 ∣ Nat.card (GLAPPrimeCore 3 ↥K) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥K))
    exact hcop (h.trans hdvd)
  obtain ⟨Ft, hFtel, hFtcard, hFtZ⟩ := hF
  obtain ⟨A, -, -, hAmap, hAker⟩ :=
    CFSG.GroupTheory.exists_pSubgroup_map_eq_of_coprime_ker f hfsurj hfker hFtel.isPGroup
  have hAel : IsElemAbelian 3 A := by
    have hinj : ∀ a ∈ A, f a = 1 → a = 1 := by
      intro a ha hfa
      have : a ∈ A ⊓ f.ker := ⟨ha, hfa⟩
      rw [hAker] at this
      exact this
    have hFt := hFtel
    have hcommFt := hFtel.1
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun a ha => ?_⟩
    · have hfa : f a ∈ Ft := hAmap ▸ Subgroup.mem_map_of_mem f a.2
      have hfb : f b ∈ Ft := hAmap ▸ Subgroup.mem_map_of_mem f b.2
      have hc := congrArg Subtype.val (mul_comm' (⟨f a, hfa⟩ : Ft) ⟨f b, hfb⟩)
      simp only [Subgroup.coe_mul] at hc
      have h1 : (a : ↥C) * b * ((b : ↥C) * a)⁻¹ = 1 := by
        refine hinj _ (A.mul_mem (A.mul_mem a.2 b.2) (A.inv_mem (A.mul_mem b.2 a.2))) ?_
        rw [map_mul, map_inv, map_mul, map_mul, hc, mul_inv_cancel]
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      exact mul_inv_eq_one.mp h1
    · have hfa : f a ∈ Ft := hAmap ▸ Subgroup.mem_map_of_mem f ha
      refine hinj _ (A.pow_mem ha 3) ?_
      rw [map_pow]
      exact hFtel.2 _ hfa
  set F : Subgroup X := A.map C.subtype with hFdef
  have hFel : IsElemAbelian 3 F := hAel.map C.subtype
  have hFcard : Nat.card F = 3 ^ e := by
    rw [hFdef, Nat.card_congr (Subgroup.equivMapOfInjective A C.subtype C.subtype_injective).toEquiv.symm,
      ← card_map_of_inf_ker hAker, hAmap, hFtcard]
  have hFC : F ≤ C := Subgroup.map_subtype_le A
  have hFK : F ≤ K := hFC.trans inf_le_left
  have hFB₀ : ∀ a ∈ B₀, ∀ b ∈ F, a * b = b * a := by
    intro a ha b hb
    have hbc : b ∈ Subgroup.centralizer (B₀ : Set X) := (Subgroup.mem_inf.mp (hFC hb)).2
    rw [Subgroup.mem_centralizer_iff] at hbc
    exact hbc a ha
  have hFB₀inf : B₀ ⊓ F = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
    obtain ⟨hxB₀, hxF⟩ := hx
    obtain ⟨a, haA, rfl⟩ := hxF
    have hcen : f a ∈ Subgroup.center (PQuot 3 K) := by
      rw [Subgroup.mem_center_iff]
      intro q
      obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥K) q
      have hlc : ⁅(l : X), ((a : ↥C) : X)⁆ ∈ O := ((show B₀ ≤ centModSubgroup 3 K from inf_le_right) hxB₀).2 l l.2
      have hlc' : ⁅l, ι a⁆ ∈ GLAPPrimeCore 3 ↥K := (hmemO _).1 hlc
      change QuotientGroup.mk' _ l * QuotientGroup.mk' _ (ι a) = QuotientGroup.mk' _ (ι a) * QuotientGroup.mk' _ l
      rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_iff_div_mem]
      have e : l * ι a / (ι a * l) = ⁅l, ι a⁆ := by
        rw [commutatorElement_def, div_eq_mul_inv, mul_inv_rev]
        group
      rw [e]
      exact hlc'
    have hfa1 : f a = 1 := by
      have : f a ∈ Ft ⊓ Subgroup.center (PQuot 3 K) := ⟨hAmap ▸ Subgroup.mem_map_of_mem f haA, hcen⟩
      rw [hFtZ] at this
      exact this
    have : a ∈ A ⊓ f.ker := ⟨haA, hfa1⟩
    rw [hAker] at this
    rw [Subgroup.mem_bot.1 this]
    rfl
  set E : Subgroup X := B₀ ⊔ F with hEdef
  have hB₀el : IsElemAbelian 3 B₀ := hB.mono inf_le_left
  have hEel : IsElemAbelian 3 E := IsElemAbelian.sup_of_commute hB₀el hFel hFB₀
  have hB₀NF : B₀ ≤ Subgroup.normalizer (F : Set X) := by
    refine le_normalizer_of_conj_mem fun a ha b hb => ?_
    rw [hFB₀ a ha b hb, mul_inv_cancel_right]
    exact hb
  have hEcard : Nat.card E = Nat.card B₀ * 3 ^ e := by
    have h := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf hB₀NF
    rw [hFB₀inf, Subgroup.card_bot, mul_one, hFcard] at h
    exact h
  have hEY : E ≤ Subgroup.normalizer (Y : Set X) := sup_le (inf_le_left.trans hBY) (hFK.trans hKY)
  obtain ⟨S, hS⟩ := CFSG.GroupTheory.exists_sylow_le_normalizer_of_isPGroup Nat.prime_three
    Nat.prime_two hEel.isPGroup hEY hY3
  have hS2 : IsPGroup 2 ((S : Subgroup Y).map Y.subtype) := S.isPGroup'.map Y.subtype
  have hS1 : (S : Subgroup Y).map Y.subtype ≠ ⊥ := by
    intro h0
    have hSbot : (S : Subgroup Y) = ⊥ := by
      rw [← Subgroup.map_eq_bot_iff_of_injective _ Y.subtype_injective]
      exact h0
    have hTY : T ≤ Y := le_sup_left
    obtain ⟨Q, hQ⟩ := (hT2.comap_subtype (K := Y)).exists_le_sylow
    have hcardQ : Nat.card (Q : Subgroup Y) = Nat.card (S : Subgroup Y) := by
      rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
    rw [hSbot, Subgroup.card_bot] at hcardQ
    have hQbot : (Q : Subgroup Y) = ⊥ := Subgroup.eq_bot_of_card_eq _ hcardQ
    have hTbot : T.subgroupOf Y = ⊥ := le_bot_iff.mp (hQbot ▸ hQ)
    apply hT1
    rw [Subgroup.subgroupOf_eq_bot, disjoint_iff] at hTbot
    rw [← inf_eq_left.mpr hTY, hTbot]
  have hbound := card_le_pow_glaTwoLocalRank Nat.prime_three hEel hS1 hS2 hS
  rw [hEcard] at hbound
  rw [mul_comm]
  exact hbound

end Faith

theorem t158TailFaith_of {Q : TauCeti.CFSGIndex → Prop} (hN : T158NormConj Q) (hU : T158RankU6)
    (hE : T158RankTE6) : T158TailFaith Q := by
  intro X _ _ p K B x₁ x₂ L₁ L₂ hQ hh hc T hT2 hBT hTc
  by_contra hT1
  have hc0 := hc
  obtain ⟨hp3, n, hn, hn1, hcase⟩ := hc
  subst hp3
  have hBK : B ≤ Subgroup.normalizer (K : Set X) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have := hN X 3 K B x₁ x₂ L₁ L₂ hQ hh hc0 1 b hb y
    simpa using this
  have hBel : IsElemAbelian 3 B := hh.hyp.1.2.2.1
  have hqs : CFSG.Open.IsQuasisimple (PQuot 3 K) :=
    isQuasisimple_pQuot_of_glaPComponent hh.prime hh.hyp.1.2.1
  have hrk : 3 ^ GLATwoLocalRank 3 X ≤ Nat.card B := by
    have h1 : 3 ^ GLATwoLocalRank 3 ↥(⊤ : Subgroup X) ≤ Nat.card B := hh.hyp.1.2.2.2.2.1
    have h2 : GLATwoLocalRank 3 X ≤ GLATwoLocalRank 3 ↥(⊤ : Subgroup X) := by
      have e : GLATwoLocalRank 3 ↥(⊤ : Subgroup X) = GLATwoLocalRank 3 X :=
        CFSG.HardMathSupport.Timmesfeld.Tables.Census.glaTwoLocalRank_congr (by norm_num)
          Subgroup.topEquiv.symm
      rw [e]
    exact (Nat.pow_le_pow_right (by norm_num) h2).trans h1
  have hpos : 0 < Nat.card ↥(B ⊓ centModSubgroup 3 K) := Nat.card_pos
  rcases hcase with ⟨hKt, -, -, hcard⟩ | ⟨hKt, -, -, hcard⟩
  · obtain ⟨F, hF⟩ := hU (PQuot 3 K) n hn hn1 hqs hKt
    have h := pow_mul_card_le_of_faith hBel hBK hT2 hT1 hBT hTc ⟨F, hF⟩
    have h' := h.trans hrk
    rw [hcard] at h'
    omega
  · obtain ⟨F, hF⟩ := hE (PQuot 3 K) n hn hn1 hqs hKt
    have h := pow_mul_card_le_of_faith hBel hBK hT2 hT1 hBT hTc ⟨F, hF⟩
    have h' := h.trans hrk
    rw [hcard] at h'
    omega


end CFSG.LocalAnalysis.GLTheoremA.T158

end
