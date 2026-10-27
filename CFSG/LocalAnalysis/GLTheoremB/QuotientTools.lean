module

public import CFSG.LocalAnalysis.GLTheoremB.UniqInputs
public import CFSG.LocalAnalysis.GLTheoremB.BaseCase
public import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.LocalAnalysis.GLTheoremB

open CFSG.Open

section Solvable

variable {Q : Type*} [Group Q]

theorem isSolvable_sup (N W : Subgroup Q) (hW : W ≤ Subgroup.normalizer (N : Set Q))
    [Group.IsSolvable N] [Group.IsSolvable W] : Group.IsSolvable ↥(N ⊔ W) := by
  set Y := N ⊔ W with hY
  have hNY : N ≤ Y := le_sup_left
  have hWY : W ≤ Y := le_sup_right
  have hnorm : (N.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNY).2 (sup_le Subgroup.le_normalizer hW)
  have hNs : Group.IsSolvable ↥(N.subgroupOf Y) :=
    Group.isSolvable_of_isSolvable_injective (f := (Subgroup.subgroupOfEquivOfLe hNY).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hNY).injective
  have hsurj : Function.Surjective
      ((QuotientGroup.mk' (N.subgroupOf Y)).comp (Subgroup.inclusion hWY)) := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    have htop : y ∈ N.subgroupOf Y ⊔ W.subgroupOf Y := by
      rw [← Subgroup.subgroupOf_sup hNY hWY]
      exact (Subgroup.mem_subgroupOf).2 y.2
    obtain ⟨n, hn, w, hw, hnw⟩ := Subgroup.mem_sup_of_normal_left.1 htop
    have hwW : (w : Q) ∈ W := (Subgroup.mem_subgroupOf).1 hw
    have hwi : Subgroup.inclusion hWY ⟨w, hwW⟩ = w := rfl
    refine ⟨⟨w, hwW⟩, ?_⟩
    rw [← hnw]
    simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply, hwi]
    rw [QuotientGroup.eq]
    have := hnorm.conj_mem n hn w⁻¹
    simpa [mul_assoc] using this
  have hQs : Group.IsSolvable (↥Y ⧸ N.subgroupOf Y) :=
    Group.isSolvable_of_surjective hsurj
  exact Group.isSolvable_of_subgroup_quotient (N.subgroupOf Y)

theorem glaPLayer_top_eq_bot_of_isSolvable {Z : Type*} [Group Z] [Group.IsSolvable Z] (p : ℕ) :
    GLAPLayer p (⊤ : Subgroup Z) = ⊥ := by
  unfold GLAPLayer
  refine eq_bot_iff.2 (sSup_le fun L hL => ?_)
  exfalso
  obtain ⟨-, -, hcomp, -⟩ := hL
  have hq := hcomp.2.2
  have hsolv : Group.IsSolvable
      (↥(⊤ : Subgroup Z) ⧸ GLAPPrimeCore p ↥(⊤ : Subgroup Z)) := inferInstance
  have hA : Group.IsSolvable ↥((L.subgroupOf ⊤).map
      (QuotientGroup.mk' (GLAPPrimeCore p ↥(⊤ : Subgroup Z)))) := inferInstance
  have : Group.IsPerfect ↥((L.subgroupOf ⊤).map
      (QuotientGroup.mk' (GLAPPrimeCore p ↥(⊤ : Subgroup Z)))) := ⟨hq.1⟩
  have := CFSG.ComponentClassification.Quasisimple.nontrivial hq
  exact Group.IsPerfect.not_isSolvable _ hA

end Solvable

section Quotient

variable {Z : Type*} [Group Z] [Finite Z]

theorem glaPPrimeCore_quotient_eq_bot {p : ℕ} (hp : p.Prime) :
    GLAPPrimeCore p (Z ⧸ GLAPPrimeCore p Z) = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  set K := GLAPPrimeCore p Z with hK
  set Nb := GLAPPrimeCore p (Z ⧸ K) with hNb
  have hKc : Nat.Coprime p (Nat.card K) := CFSG.pPrimeCore_coprime_card
  have hNbc : Nat.Coprime p (Nat.card Nb) := CFSG.pPrimeCore_coprime_card
  have hcard : Nat.card (Nb.comap (QuotientGroup.mk' K)) = Nat.card K * Nat.card Nb :=
    QuotientGroup.card_preimage_mk K (Nb : Set (Z ⧸ K))
  have hNn : (Nb.comap (QuotientGroup.mk' K)).Normal := (GLAPPrimeCore.normal p _).comap _
  have hNp : Nat.Coprime p (Nat.card (Nb.comap (QuotientGroup.mk' K))) := by
    rw [hcard]
    exact Nat.Coprime.mul_right hKc hNbc
  have hNle : Nb.comap (QuotientGroup.mk' K) ≤ K := le_sSup ⟨hNn, hNp⟩
  refine eq_bot_iff.2 fun x hx => ?_
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective x
  have hz : z ∈ K := hNle hx
  exact (Subgroup.mem_bot).2 ((QuotientGroup.eq_one_iff z).2 hz)

theorem eq_bot_of_centralizes_pCore_components {p : ℕ} (hp : p.Prime)
    (hcore : GLAPPrimeCore p Z = ⊥) {S : Subgroup Z} (hS : Nat.Coprime p (Nat.card S))
    (h1 : S ≤ Subgroup.centralizer (CFSG.Open.pCore p Z : Set Z))
    (h2 : ∀ K : Subgroup Z, IsComponentOf K ⊤ → S ≤ Subgroup.centralizer (K : Set Z)) :
    S = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have hF : CFSG.fittingSubgroup Z = CFSG.pCore p Z := CFSG.Fitting_eq_pcore Z p hcore
  have hFle : CFSG.fittingSubgroup Z ≤ Subgroup.centralizer (S : Set Z) := by
    rw [hF]
    exact Subgroup.le_centralizer_iff.1 h1
  have hLle : CFSG.layer Z ≤ Subgroup.centralizer (S : Set Z) :=
    sSup_le fun K hK => Subgroup.le_centralizer_iff.1
      (h2 K ((CFSG.isComponent_iff_open K).1 hK))
  have hstar : CFSG.generalizedFitting Z ≤ Subgroup.centralizer (S : Set Z) := sup_le hFle hLle
  have hcent : Subgroup.centralizer (CFSG.generalizedFitting Z : Set Z) ≤
      CFSG.fittingSubgroup Z := by
    have := CFSG.ComponentClassification.GeneralizedFitting.centralizer_le_fitting Z
    rw [← CFSG.generalizedFitting_eq_componentClassification] at this
    exact this
  have hSF : S ≤ CFSG.pCore p Z := hF ▸ le_trans (Subgroup.le_centralizer_iff.2 hstar) hcent
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := p) (G := Z)).exists_card_eq
  have hdvd : Nat.card S ∣ p ^ k := hk ▸ Subgroup.card_dvd_of_le hSF
  have h1' : Nat.card S = 1 := (Nat.Coprime.pow_left k hS).symm.eq_one_of_dvd hdvd
  exact Subgroup.eq_bot_of_card_eq S h1'

end Quotient

theorem isSCp_subgroupOf {Z : Type*} [Group Z] {p : ℕ} {Y B : Subgroup Z} (hB : IsSCp p ⊤ B)
    (hBY : B ≤ Y) : IsSCp p ⊤ (B.subgroupOf Y) := by
  obtain ⟨-, hel, hmax⟩ := hB
  have := hel.1
  refine ⟨le_top, ⟨inferInstance, fun x hx => Subtype.ext (hel.2 x hx)⟩, ?_⟩
  intro E _ hE hBE
  have hE' : IsElemAbelian p (E.map Y.subtype) := CFSG.SectionRank.isElemAbelian_map hE _
  have hBE' : B ≤ E.map Y.subtype := fun x hx => ⟨⟨x, hBY hx⟩, hBE hx, rfl⟩
  have h := hmax _ le_top hE' hBE'
  calc E = (E.map Y.subtype).comap Y.subtype :=
        (Subgroup.comap_map_eq_self_of_injective Y.subtype_injective E).symm
    _ = B.subgroupOf Y := by rw [h]; rfl

theorem isSCp_map_quotient {Z : Type*} [Group Z] [Finite Z] {p : ℕ} [hp : Fact p.Prime]
    (N : Subgroup Z) [N.Normal]
    (hN : ¬ p ∣ Nat.card N) {B : Subgroup Z} (hB : IsSCp p ⊤ B) :
    IsSCp (G := Z ⧸ N) p ⊤ (B.map (QuotientGroup.mk' N)) := by
  obtain ⟨-, hel, hmax⟩ := hB
  refine ⟨le_top, CFSG.SectionRank.isElemAbelian_map hel _, ?_⟩
  intro E _ hE hBE
  refine le_antisymm ?_ hBE
  have hcop : ∀ {k : ℕ}, Nat.Coprime (p ^ k) (Nat.card N) := fun {k} =>
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hN)
  have hEp : IsPGroup p E := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hE.2 g.1 g.2)⟩
  obtain ⟨k, hcard⟩ := hEp.exists_card_eq
  set P : Subgroup Z := E.comap (QuotientGroup.mk' N) with hP
  have hPcard : Nat.card P = Nat.card N * p ^ k := by
    rw [← hcard]
    exact QuotientGroup.card_preimage_mk N (E : Set (Z ⧸ N))
  have hBP : B ≤ P := fun x hx => hBE ⟨x, hx, rfl⟩
  have hBpg : IsPGroup p ↥(B.subgroupOf P) := by
    intro g
    refine ⟨1, ?_⟩
    rw [pow_one]
    exact Subtype.ext (Subtype.ext (hel.2 g.1.1 g.2))
  obtain ⟨S, hS⟩ := hBpg.exists_le_sylow
  have hScard : Nat.card S = p ^ k := by
    rw [Sylow.card_eq_multiplicity, hPcard, Nat.factorization_mul (Nat.card_pos.ne')
      (pow_ne_zero _ hp.out.ne_zero), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hN, Nat.Prime.factorization_pow hp.out,
      Finsupp.single_eq_same, zero_add]
  set ι : S →* Z := P.subtype.comp (S : Subgroup P).subtype
  set φ : S →* E := ((QuotientGroup.mk' N).comp ι).codRestrict E fun s => s.1.2
  have hker : ∀ s : S, ι s ∈ N → s = 1 := by
    intro s hs
    have hdisj := Subgroup.disjoint_of_coprime_natCard (H := (S : Subgroup P).map P.subtype)
      (K := N) (by
        rw [Subgroup.card_map_of_injective Subtype.val_injective, hScard]
        exact hcop)
    have h1 : ι s ∈ (S : Subgroup P).map P.subtype ⊓ N := ⟨⟨s, s.2, rfl⟩, hs⟩
    rw [hdisj.eq_bot, Subgroup.mem_bot] at h1
    exact Subtype.ext (Subtype.ext h1)
  have hφ : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro s hs
    rw [MonoidHom.mem_ker] at hs
    have h2 : (QuotientGroup.mk' N) (ι s) = 1 := congrArg Subtype.val hs
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    exact (Subgroup.mem_bot).2 (hker s h2)
  have hιinj : Function.Injective ι := Subtype.val_injective.comp Subtype.val_injective
  have := hE.1
  have hA : IsElemAbelian p ι.range := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
    · obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 a.2
      obtain ⟨z, hz⟩ := MonoidHom.mem_range.1 b.2
      apply Subtype.ext
      change (a : Z) * b = b * a
      rw [← hx, ← hz, ← map_mul, ← map_mul]
      congr 1
      apply hφ
      rw [map_mul, map_mul]
      exact mul_comm' _ _
    · obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hy
      rw [← map_pow]
      have : x ^ p = 1 := by
        apply hφ
        rw [map_pow, map_one]
        exact Subtype.ext (by
          rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
          exact hE.2 _ (φ x).2)
      rw [this, map_one]
  have hBA : B ≤ ι.range := by
    intro x hx
    have hxP : x ∈ P := hBP hx
    have hxS : (⟨x, hxP⟩ : ↥P) ∈ (S : Subgroup P) := hS ((Subgroup.mem_subgroupOf).2 hx)
    exact ⟨⟨⟨x, hxP⟩, hxS⟩, rfl⟩
  have hAB : ι.range = B := hmax _ le_top hA hBA
  have hsurj : Function.Surjective φ :=
    (hφ.bijective_of_nat_card_le (by rw [hcard, hScard])).2
  intro e he
  obtain ⟨s, hs⟩ := hsurj ⟨e, he⟩
  have hsB : ι s ∈ B := hAB ▸ ⟨s, rfl⟩
  exact ⟨ι s, hsB, congrArg Subtype.val hs⟩


theorem commutator_eq_bot_of_normalizes {Q : Type*} [Group Q] [Finite Q] {K S : Subgroup Q}
    (hK : IsComponentOf K ⊤) (hS : IsPGroup 2 S) (hKS : K ≤ Subgroup.normalizer (S : Set Q)) :
    ⁅K, S⁆ = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSH : S ≤ S ⊔ K := le_sup_left
  have hKH : K ≤ S ⊔ K := le_sup_right
  have hnorm : (S.subgroupOf (S ⊔ K)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSH).2 (sup_le Subgroup.le_normalizer hKS)
  have hp2 : IsPGroup 2 ↥(S.subgroupOf (S ⊔ K)) :=
    hS.of_equiv (Subgroup.subgroupOfEquivOfLe hSH).symm
  have : Group.IsNilpotent ↥(S.subgroupOf (S ⊔ K)) := hp2.isNilpotent
  have hsub : IsSubnormal (S.subgroupOf (S ⊔ K)) ⊤ :=
    CFSG.ComponentClassification.Components.chain_of_mathlib_subnormal hnorm.isSubnormal
  have h := CFSG.ComponentClassification.LocalComponents.commutes_with_solvable_subnormal
    (K.subgroupOf (S ⊔ K)) (S.subgroupOf (S ⊔ K))
    (CFSG.ComponentClassification.LocalComponents.of_overgroup hK hKH) hsub
  have hmap := congrArg (Subgroup.map (S ⊔ K).subtype) h
  simpa only [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hKH,
    Subgroup.map_subgroupOf_eq_of_le hSH, Subgroup.map_bot] using hmap

theorem centralizes_pCore_of_isSCp (i20 : Input20_1) {Q : Type} [Group Q] [Finite Q] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {B X : Subgroup Q} (hB : IsSCp p ⊤ B) (hX : IsPGroup 2 X)
    (hBX : B ≤ Subgroup.normalizer (X : Set Q)) :
    X ≤ Subgroup.centralizer (CFSG.Open.pCore p Q : Set Q) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPn : (CFSG.Open.pCore p Q).Normal := CFSG.LieType.BorelTits.pCore_normal p
  have hPp : IsPGroup p (CFSG.Open.pCore p Q) := CFSG.LieType.BorelTits.pCore_isPGroup (G := Q) p
  have : Group.IsNilpotent ↥(CFSG.Open.pCore p Q) := hPp.isNilpotent
  have : Group.IsNilpotent ↥X := hX.isNilpotent
  have : IsMulCommutative ↥B := hB.2.1.1
  have hXB : Group.IsSolvable ↥(X ⊔ B) := isSolvable_sup X B hBX
  have hYs : Group.IsSolvable ↥(CFSG.Open.pCore p Q ⊔ (X ⊔ B)) :=
    isSolvable_sup (CFSG.Open.pCore p Q) (X ⊔ B)
      (fun x _ => (Subgroup.normalizer_eq_top_iff.2 hPn) ▸ Subgroup.mem_top x)
  set P := CFSG.Open.pCore p Q with hP
  set Y := P ⊔ (X ⊔ B) with hY
  have hPY : P ≤ Y := le_sup_left
  have hXY : X ≤ Y := le_sup_left.trans le_sup_right
  have hBY : B ≤ Y := le_sup_right.trans le_sup_right
  have hlayer : GLAPLayer p (⊤ : Subgroup ↥Y) = ⊥ := glaPLayer_top_eq_bot_of_isSolvable p
  have hB' : IsSCp p ⊤ (B.subgroupOf Y) := isSCp_subgroupOf hB hBY
  have hmain := i20 ↥Y p hp hp2 hlayer (B.subgroupOf Y) hB'
  have hXcop : Nat.Coprime p (Nat.card (X.subgroupOf Y)) := by
    obtain ⟨k, hk⟩ := hX.exists_card_eq
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXY).toEquiv, hk]
    exact Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have hXnorm : B.subgroupOf Y ≤ Subgroup.normalizer ((X.subgroupOf Y : Subgroup ↥Y) : Set ↥Y) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have := Subgroup.mem_normalizer_iff.1 (hBX ((Subgroup.mem_subgroupOf).1 hb)) (x : Q)
    simpa [Subgroup.mem_subgroupOf] using this
  have hXO : X.subgroupOf Y ≤ GLAPPrimeCoreOf p (⊤ : Subgroup ↥Y) :=
    hmain ▸ le_iSup_of_le (X.subgroupOf Y) (le_iSup_of_le hXcop (le_iSup_of_le hXnorm le_rfl))
  have hOn := le_normalizer_glaPPrimeCoreOf p (⊤ : Subgroup ↥Y)
  have hOcop := not_dvd_card_glaPPrimeCoreOf hp (⊤ : Subgroup ↥Y)
  intro x hx q hq
  set xY : ↥Y := ⟨x, hXY hx⟩
  set qY : ↥Y := ⟨q, hPY hq⟩
  have hxO : xY ∈ GLAPPrimeCoreOf p (⊤ : Subgroup ↥Y) := hXO ((Subgroup.mem_subgroupOf).2 hx)
  have hc1 : xY * (qY * xY⁻¹ * qY⁻¹) ∈ GLAPPrimeCoreOf p (⊤ : Subgroup ↥Y) := by
    refine Subgroup.mul_mem _ hxO ?_
    have := (Subgroup.mem_normalizer_iff.1 (hOn (Subgroup.mem_top qY)) xY⁻¹).1
      (Subgroup.inv_mem _ hxO)
    simpa using this
  have hc2 : (xY * (qY * xY⁻¹ * qY⁻¹) : ↥Y) ∈ P.subgroupOf Y := by
    rw [Subgroup.mem_subgroupOf]
    have h1 : x * q * x⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.1
      ((Subgroup.normalizer_eq_top_iff.2 hPn) ▸ Subgroup.mem_top x) q).1 hq
    have : ((xY * (qY * xY⁻¹ * qY⁻¹) : ↥Y) : Q) = (x * q * x⁻¹) * q⁻¹ := by
      simp [xY, qY, mul_assoc]
    rw [this]
    exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hq)
  set c : ↥Y := xY * (qY * xY⁻¹ * qY⁻¹) with hc
  have hcard := Subgroup.orderOf_dvd_natCard (GLAPPrimeCoreOf p (⊤ : Subgroup ↥Y)) hc1
  obtain ⟨n, hn⟩ := hPp ⟨(c : Q), (Subgroup.mem_subgroupOf).1 hc2⟩
  have hn' : c ^ (p ^ n) = 1 := Subtype.ext (by simpa using congrArg Subtype.val hn)
  have hcop : Nat.Coprime p (orderOf c) :=
    ((Nat.Prime.coprime_iff_not_dvd hp).2 hOcop).coprime_dvd_right hcard
  have h1 : orderOf c = 1 :=
    (Nat.Coprime.pow_left n hcop).symm.eq_one_of_dvd (orderOf_dvd_of_pow_eq_one hn')
  have hc1' : c = 1 := orderOf_eq_one_iff.1 h1
  have : (x * q * x⁻¹ * q⁻¹ : Q) = 1 := by
    have := congrArg Subtype.val hc1'
    simpa [c, xY, qY, mul_assoc] using this
  calc q * x = (x * q * x⁻¹ * q⁻¹) * (q * x) := by rw [this, one_mul]
    _ = x * q := by group

end CFSG.LocalAnalysis.GLTheoremB
