module

public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
public import CFSG.GroupTheory.LocalCores.PrimeSetCore
public import CFSG.Foundations.Basic

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup

variable {F : Type*} [Group F]

namespace TwoGroupAction

theorem exists_sylow_le_normalizer [Finite F] {p : ℕ} [Fact p.Prime] {N Q : Subgroup F}
    (hQ : IsPGroup p Q) (hQN : Q ≤ normalizer (N : Set F)) :
    ∃ P : Sylow p N, Q ≤ normalizer (((P : Subgroup N).map N.subtype : Subgroup F) : Set F) := by
  classical
  let Q' : Subgroup (normalizer (N : Set F)) := Q.subgroupOf (normalizer (N : Set F))
  have hQ' : IsPGroup p Q' := hQ.of_equiv (Subgroup.subgroupOfEquivOfLe hQN).symm
  obtain ⟨P, hP⟩ :=
    hQ'.nonempty_fixed_point_of_prime_not_dvd_card (Sylow p N) (not_dvd_card_sylow p N)
  refine ⟨P, fun q hq => ?_⟩
  have key : ∀ g : Q', ∀ y ∈ (P : Subgroup N).map N.subtype,
      ((g : normalizer (N : Set F)) : F) * y * ((g : normalizer (N : Set F)) : F)⁻¹ ∈
        (P : Subgroup N).map N.subtype := by
    rintro g _ ⟨n, hn, rfl⟩
    have hgP : g • P = P := hP g
    have hmem : (g : normalizer (N : Set F)) • n ∈ ((g • P : Sylow p N) : Subgroup N) := by
      rw [show (g • P : Sylow p N) = (g : normalizer (N : Set F)) • P from rfl,
        Sylow.pointwise_smul_def]
      exact Subgroup.smul_mem_pointwise_smul n _ _ hn
    rw [hgP] at hmem
    exact ⟨_, hmem, Subgroup.smul_coe N _ n⟩
  rw [mem_normalizer_iff]
  intro y
  refine ⟨key ⟨⟨q, hQN hq⟩, hq⟩ y, fun hy => ?_⟩
  simpa [mul_assoc] using key ⟨⟨q, hQN hq⟩, hq⟩⁻¹ _ hy

theorem sylow_map_eq_of_le {p : ℕ} {N X : Subgroup F} (P : Sylow p N) (hX : IsPGroup p X)
    (hXN : X ≤ N) (hPX : (P : Subgroup N).map N.subtype ≤ X) :
    X = (P : Subgroup N).map N.subtype := by
  have hX' : IsPGroup p (X.subgroupOf N) := hX.of_equiv (Subgroup.subgroupOfEquivOfLe hXN).symm
  have hle : (P : Subgroup N) ≤ X.subgroupOf N := fun n hn => hPX ⟨n, hn, rfl⟩
  rw [← P.is_maximal' hX' hle, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hXN]

theorem card_sylow_map [Finite F] {p : ℕ} [Fact p.Prime] {N : Subgroup F} (P : Sylow p N) :
    Nat.card ((P : Subgroup N).map N.subtype) = p ^ (Nat.card N).factorization p := by
  rw [Subgroup.card_map_of_injective N.subtype_injective, P.card_eq_multiplicity]

theorem sup_inf_eq_left_of_le_normalizer {X T A : Subgroup F} (hXA : X ≤ A)
    (hTX : T ≤ normalizer (X : Set F)) (hAT : A ⊓ T = ⊥) : (X ⊔ T) ⊓ A = X := by
  refine le_antisymm (fun y ⟨hy, hyA⟩ => ?_) (le_inf le_sup_left hXA)
  have hy' : y ∈ ((X ⊔ T : Subgroup F) : Set F) := hy
  rw [Subgroup.coe_mul_of_right_le_normalizer_left X T hTX] at hy'
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.1 hy'
  have hbA : b ∈ A := by simpa using A.mul_mem (A.inv_mem (hXA ha)) hyA
  have hb1 : b ∈ A ⊓ T := ⟨hbA, hb⟩
  rw [hAT, Subgroup.mem_bot] at hb1
  rwa [hb1, mul_one]

theorem exists_mem_normalizer_of_lt [Finite F] {p : ℕ} [Fact p.Prime] {X Y : Subgroup F}
    (hY : IsPGroup p Y) (hXY : X < Y) : ∃ w ∈ Y, w ∉ X ∧ w ∈ normalizer (X : Set F) := by
  have hlt : X.subgroupOf Y < ⊤ := by
    refine lt_top_iff_ne_top.2 fun h => hXY.not_ge ?_
    rwa [Subgroup.subgroupOf_eq_top] at h
  obtain ⟨V, hle, hnormal, hidx⟩ := p_group_normalizer_step hY hlt
  have hnot : ¬ V ≤ X.subgroupOf Y := fun h => by
    have h1 := Subgroup.relIndex_eq_one.2 h
    rw [hidx] at h1
    exact (Fact.out : p.Prime).one_lt.ne' h1
  obtain ⟨w, hwV, hwX⟩ := IsConcreteLE.not_le_iff_exists.1 hnot
  refine ⟨w, w.2, hwX, ?_⟩
  rw [mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have hmem : (⟨⟨h, hXY.le hh⟩, hle hh⟩ : V) ∈ (X.subgroupOf Y).subgroupOf V := hh
    exact hnormal.conj_mem _ hmem ⟨w, hwV⟩
  · intro hh
    have hY' : (w : F) * h * (w : F)⁻¹ ∈ Y := hXY.le hh
    have hhY : h ∈ Y := by
      simpa [mul_assoc] using Y.mul_mem (Y.mul_mem (Y.inv_mem w.2) hY') w.2
    have hwh : (⟨h, hhY⟩ : Y) = w⁻¹ * ⟨(w : F) * h * (w : F)⁻¹, hY'⟩ * w :=
      Subtype.ext (by simp [mul_assoc])
    have hmem : (⟨⟨(w : F) * h * (w : F)⁻¹, hY'⟩, hle hh⟩ : V) ∈
        (X.subgroupOf Y).subgroupOf V := hh
    have hconj := hnormal.conj_mem _ hmem ⟨w, hwV⟩⁻¹
    have h2 : ((⟨w, hwV⟩⁻¹ * ⟨⟨(w : F) * h * (w : F)⁻¹, hY'⟩, hle hh⟩ * (⟨w, hwV⟩⁻¹)⁻¹ : V) :
        Y) = ⟨h, hhY⟩ := by
      rw [hwh]
      simp
    change (((⟨w, hwV⟩⁻¹ * ⟨⟨(w : F) * h * (w : F)⁻¹, hY'⟩, hle hh⟩ * (⟨w, hwV⟩⁻¹)⁻¹ : V) :
      Y) : F) ∈ X at hconj
    rwa [h2] at hconj

theorem coprime_two_card_pPrimeCore (U : Type*) [Group U] [Finite U] :
    Nat.Coprime 2 (Nat.card (CFSG.pPrimeCore 2 U)) := by
  have h := (CFSG.LocalCores.prime_set_core_maximal (G := U) {q : Nat.Primes | q.val ≠ 2}).1
  rw [← CFSG.pPrimeCore_eq_piCore U 2] at h
  rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
  exact fun h2 => h ⟨2, Nat.prime_two⟩ h2 rfl

theorem commutator_eq_bot_of_le_coprime [Finite F] {T R O : Subgroup F} (hR : IsPGroup 2 R)
    (hTR : T ≤ normalizer (R : Set F)) (hO : Nat.Coprime 2 (Nat.card O)) (hle : ⁅T, R⁆ ≤ O) :
    ⁅T, R⁆ = ⊥ := by
  have hR' : ⁅T, R⁆ ≤ R := Subgroup.commutator_le.2 fun t ht r hr => by
    rw [commutatorElement_def]
    exact R.mul_mem ((mem_normalizer_iff.1 (hTR ht) r).1 hr) (R.inv_mem hr)
  obtain ⟨n, hn⟩ := hR.exists_card_eq
  have hcop : Nat.Coprime (Nat.card R) (Nat.card O) := hn ▸ Nat.Coprime.pow_left n hO
  exact le_bot_iff.1 ((le_inf hR' hle).trans (disjoint_iff.1
    (Subgroup.disjoint_of_coprime_natCard hcop)).le)

theorem exists_injective_hom_center {A T U R : Subgroup F} (hRA : R ≤ A)
    (hTA : T ≤ normalizer (A : Set F)) (hAT : A ⊓ T = ⊥)
    (hC : ∀ t ∈ T, t ≠ 1 → A ⊓ centralizer {t} ≤ U) (hTR : ⁅T, R⁆ = ⊥) {x : F} (hxA : x ∈ A)
    (hxN : x ∈ normalizer ((R ⊔ T : Subgroup F) : Set F)) (hxU : x ∉ U) :
    ∃ ι : T →* center R, Function.Injective ι ∧
      ∀ t : T, ((ι t : R) : F) = (t : F)⁻¹ * (x⁻¹ * t * x) := by
  have hTC : T ≤ centralizer (R : Set F) := commutator_eq_bot_iff_le_centralizer.1 hTR
  have hcent : ∀ t ∈ T, ∀ r ∈ R, r * t = t * r := fun t ht r hr =>
    mem_centralizer_iff.1 (hTC ht) r hr
  have hRTA : (R ⊔ T) ⊓ A = R :=
    sup_inf_eq_left_of_le_normalizer hRA (hTC.trans (centralizer_le_normalizer _)) hAT
  have hxR : ∀ r ∈ R, x * r * x⁻¹ ∈ R := fun r hr => by
    rw [← hRTA]
    exact ⟨(mem_normalizer_iff.1 hxN r).1 (le_sup_left (b := T) hr),
      A.mul_mem (A.mul_mem hxA (hRA hr)) (A.inv_mem hxA)⟩
  let c : F → F := fun t => t⁻¹ * (x⁻¹ * t * x)
  have hcR : ∀ t ∈ T, c t ∈ R := fun t ht => by
    rw [← hRTA]
    refine ⟨(R ⊔ T).mul_mem ((R ⊔ T).inv_mem (le_sup_right (a := R) ht)) ?_, ?_⟩
    · simpa [mul_assoc] using (mem_normalizer_iff''.1 hxN t).1 (le_sup_right (a := R) ht)
    · have h1 : t⁻¹ * x⁻¹ * t ∈ A := by
        simpa using (mem_normalizer_iff.1 (hTA (T.inv_mem ht)) x⁻¹).1 (A.inv_mem hxA)
      simpa [c, mul_assoc] using A.mul_mem h1 hxA
  have hcZ : ∀ t ∈ T, ∀ r ∈ R, r * c t = c t * r := fun t ht r hr => by
    have h1 : r * t⁻¹ = t⁻¹ * r := hcent t⁻¹ (T.inv_mem ht) r hr
    have h2 : r * (x⁻¹ * t * x) = (x⁻¹ * t * x) * r := by
      calc r * (x⁻¹ * t * x) = x⁻¹ * ((x * r * x⁻¹) * t) * x := by group
        _ = x⁻¹ * (t * (x * r * x⁻¹)) * x := by rw [hcent t ht _ (hxR r hr)]
        _ = (x⁻¹ * t * x) * r := by group
    simp only [c]
    rw [← mul_assoc, h1, mul_assoc, h2, ← mul_assoc]
  let ι : T →* center R :=
    { toFun := fun t => ⟨⟨c t, hcR t t.2⟩, mem_center_iff.2 fun r =>
        Subtype.ext (hcZ t t.2 r r.2)⟩
      map_one' := by
        refine Subtype.ext (Subtype.ext ?_)
        simp [c]
      map_mul' := fun s t => by
        refine Subtype.ext (Subtype.ext ?_)
        show c (s * t) = c s * c t
        have h1 : (t : F)⁻¹ * c s = c s * (t : F)⁻¹ :=
          (hcent (t : F)⁻¹ (T.inv_mem t.2) (c s) (hcR s s.2)).symm
        calc c (s * t) = (t : F)⁻¹ * c s * (x⁻¹ * t * x) := by simp only [c]; group
          _ = c s * c t := by rw [h1]; simp only [c]; group }
  refine ⟨ι, (injective_iff_map_eq_one ι).2 fun t ht => ?_, fun t => rfl⟩
  have hct : c t = 1 := congrArg (fun z : center R => ((z : R) : F)) ht
  have hxt : x ∈ centralizer {(t : F)} := by
    rw [mem_centralizer_singleton_iff]
    have hconj : x⁻¹ * t * x = t := by
      simp only [c] at hct
      rw [inv_mul_eq_one] at hct
      exact hct.symm
    calc x * t = x * (x⁻¹ * t * x) := by rw [hconj]
      _ = t * x := by group
  by_contra hne
  exact hxU (hC t t.2 (fun h => hne (Subtype.ext h)) ⟨hxA, hxt⟩)

theorem isMulCommutative_and_exists_mulEquiv_of_injective {T : Type*} [Group T] {R : Type*}
    [Group R] {ι : T →* center R} (hι : Function.Injective ι) :
    IsMulCommutative T ∧ ∃ V : Subgroup (center R), Nonempty (T ≃* V) :=
  ⟨⟨⟨fun a b => hι (by rw [map_mul, map_mul]; exact Subtype.ext (mem_center_iff.1 (ι b).2 (ι a)))⟩⟩,
    ⟨ι.range, ⟨MonoidHom.ofInjective hι⟩⟩⟩

end TwoGroupAction

open TwoGroupAction

theorem two_group_action_sylow_center_embedding_or_centralizing_residual [Finite F]
    {A T U : Subgroup F} (hUA : U ≤ A) (hT : IsPGroup 2 T) (hTA : T ≤ normalizer (A : Set F))
    (hTU : T ≤ normalizer (U : Set F)) (hAT : A ⊓ T = ⊥)
    (hC : ∀ t ∈ T, t ≠ 1 → A ⊓ centralizer {t} ≤ U)
    (hcomm : ⁅T, U⁆ ≤ (CFSG.pPrimeCore 2 U).map U.subtype) :
    ∃ R S : Subgroup F,
      (∃ P : Sylow 2 U, (P : Subgroup U).map U.subtype = R) ∧
      (∃ Q : Sylow 2 A, (Q : Subgroup A).map A.subtype = S) ∧
      R ≤ S ∧ U ⊓ S = R ∧ T ≤ normalizer (S : Set F) ∧ ⁅T, R⁆ = ⊥ ∧
      (∀ x ∈ A ⊓ normalizer ((R ⊔ T : Subgroup F) : Set F), x ∉ U →
        ∃ ι : T →* center R, Function.Injective ι ∧
          ∀ t : T, ((ι t : R) : F) = (t : F)⁻¹ * (x⁻¹ * t * x)) ∧
      (2 ^ (Nat.card U).factorization 2 < 2 ^ (Nat.card A).factorization 2 →
        (∃ x ∈ S, x ∉ R ∧ x ∈ A ⊓ normalizer ((R ⊔ T : Subgroup F) : Set F) ∧ x ∉ U) ∧
        IsMulCommutative T ∧ (∃ V : Subgroup (center R), Nonempty (T ≃* V)) ∧
        (center R).map R.subtype ≤ U) ∧
      (2 ^ (Nat.card U).factorization 2 = 2 ^ (Nat.card A).factorization 2 →
        R = S ∧ ⁅T, S⁆ = ⊥ ∧
        (¬ A ⊓ normalizer ((S ⊔ T : Subgroup F) : Set F) ≤ U →
          IsMulCommutative T ∧ ∃ V : Subgroup (center R), Nonempty (T ≃* V))) ∧
      ((¬ IsMulCommutative T ∨ ¬ ∃ V : Subgroup U, Nonempty (T ≃* V)) →
        2 ^ (Nat.card U).factorization 2 = 2 ^ (Nat.card A).factorization 2 ∧
        ⁅T, S⁆ = ⊥ ∧ A ⊓ normalizer ((S ⊔ T : Subgroup F) : Set F) ≤ U) := by
  classical
  obtain ⟨P, hTP⟩ := exists_sylow_le_normalizer (p := 2) hT hTU
  set R := (P : Subgroup U).map U.subtype
  have hRU : R ≤ U := Subgroup.map_subtype_le _
  have hRA : R ≤ A := hRU.trans hUA
  have hR2 : IsPGroup 2 R := P.isPGroup'.map U.subtype
  have hTR : ⁅T, R⁆ = ⊥ := by
    refine commutator_eq_bot_of_le_coprime hR2 hTP ?_
      ((Subgroup.commutator_mono le_rfl hRU).trans hcomm)
    rw [Subgroup.card_map_of_injective U.subtype_injective]
    exact coprime_two_card_pPrimeCore U
  have hRT2 : IsPGroup 2 (R ⊔ T : Subgroup F) := hR2.to_sup_of_normal_left' hT hTP
  obtain ⟨Q, hRTQ⟩ := exists_sylow_le_normalizer (p := 2) hRT2
    (sup_le (hRA.trans (Subgroup.le_normalizer)) hTA)
  set S := (Q : Subgroup A).map A.subtype
  have hSA : S ≤ A := Subgroup.map_subtype_le _
  have hS2 : IsPGroup 2 S := Q.isPGroup'.map A.subtype
  have hTS : T ≤ normalizer (S : Set F) := le_sup_right.trans hRTQ
  have hRS : R ≤ S := by
    have h2 : IsPGroup 2 (S ⊔ R : Subgroup F) :=
      hS2.to_sup_of_normal_left' hR2 (le_sup_left.trans hRTQ)
    exact le_sup_right.trans (sylow_map_eq_of_le Q h2 (sup_le hSA hRA) le_sup_left).le
  have hUS : U ⊓ S = R :=
    sylow_map_eq_of_le P hS2.to_inf_right inf_le_left (le_inf hRU hRS)
  have hembed : ∀ x ∈ A ⊓ normalizer ((R ⊔ T : Subgroup F) : Set F), x ∉ U →
      ∃ ι : T →* center R, Function.Injective ι ∧
        ∀ t : T, ((ι t : R) : F) = (t : F)⁻¹ * (x⁻¹ * t * x) :=
    fun x hx hxU => exists_injective_hom_center hRA hTA hAT hC hTR hx.1 hx.2 hxU
  have hconseq : ∀ x ∈ A ⊓ normalizer ((R ⊔ T : Subgroup F) : Set F), x ∉ U →
      IsMulCommutative T ∧ ∃ V : Subgroup (center R), Nonempty (T ≃* V) := fun x hx hxU => by
    obtain ⟨ι, hι, -⟩ := hembed x hx hxU
    exact isMulCommutative_and_exists_mulEquiv_of_injective hι
  have hembedU : ∀ x ∈ A ⊓ normalizer ((R ⊔ T : Subgroup F) : Set F), x ∉ U →
      ∃ V : Subgroup U, Nonempty (T ≃* V) := fun x hx hxU => by
    obtain ⟨ι, hι, -⟩ := hembed x hx hxU
    let f : T →* U := (Subgroup.inclusion hRU).comp ((center R).subtype.comp ι)
    have hf : Function.Injective f :=
      (Subgroup.inclusion_injective hRU).comp ((center R).subtype_injective.comp hι)
    exact ⟨f.range, ⟨MonoidHom.ofInjective hf⟩⟩
  have hRcard : Nat.card R = 2 ^ (Nat.card U).factorization 2 := card_sylow_map P
  have hScard : Nat.card S = 2 ^ (Nat.card A).factorization 2 := card_sylow_map Q
  have hstrict : 2 ^ (Nat.card U).factorization 2 < 2 ^ (Nat.card A).factorization 2 →
      ∃ x ∈ S, x ∉ R ∧ x ∈ A ⊓ normalizer ((R ⊔ T : Subgroup F) : Set F) ∧ x ∉ U := by
    intro hlt
    have hRT : (R ⊔ T) ⊓ A = R := sup_inf_eq_left_of_le_normalizer hRA hTP hAT
    have hST : (S ⊔ T) ⊓ A = S := sup_inf_eq_left_of_le_normalizer hSA hTS hAT
    have hRTlt : R ⊔ T < S ⊔ T := by
      refine lt_of_le_of_ne (sup_le_sup_right hRS T) fun h => ?_
      rw [h, hST] at hRT
      rw [← hRcard, ← hScard, hRT] at hlt
      exact lt_irrefl _ hlt
    obtain ⟨w, hwST, hwRT, hwN⟩ :=
      exists_mem_normalizer_of_lt (hS2.to_sup_of_normal_left' hT hTS) hRTlt
    have hw : w ∈ ((S ⊔ T : Subgroup F) : Set F) := hwST
    rw [Subgroup.coe_mul_of_right_le_normalizer_left S T hTS] at hw
    obtain ⟨s, hs, t, ht, rfl⟩ := Set.mem_mul.1 hw
    have hsN : s ∈ normalizer ((R ⊔ T : Subgroup F) : Set F) := by
      have := (normalizer ((R ⊔ T : Subgroup F) : Set F)).mul_mem hwN
        ((normalizer ((R ⊔ T : Subgroup F) : Set F)).inv_mem
          (Subgroup.le_normalizer (le_sup_right (a := R) ht)))
      simpa using this
    have hsR : s ∉ R := fun hsR => hwRT ((R ⊔ T).mul_mem (le_sup_left (b := T) hsR)
      (le_sup_right (a := R) ht))
    exact ⟨s, hs, hsR, ⟨hSA hs, hsN⟩, fun hsU => hsR (hUS ▸ ⟨hsU, hs⟩)⟩
  have hequal : 2 ^ (Nat.card U).factorization 2 = 2 ^ (Nat.card A).factorization 2 → R = S :=
    fun heq => Subgroup.eq_of_le_of_card_ge hRS (by rw [hRcard, hScard, heq])
  have hequalEmbed : 2 ^ (Nat.card U).factorization 2 = 2 ^ (Nat.card A).factorization 2 →
      ¬ A ⊓ normalizer ((S ⊔ T : Subgroup F) : Set F) ≤ U →
        ∃ x ∈ A ⊓ normalizer ((R ⊔ T : Subgroup F) : Set F), x ∉ U := fun heq hN => by
    obtain ⟨x, hx, hxU⟩ := IsConcreteLE.not_le_iff_exists.1 hN
    exact ⟨x, by rwa [hequal heq], hxU⟩
  have hle : 2 ^ (Nat.card U).factorization 2 ≤ 2 ^ (Nat.card A).factorization 2 := by
    rw [← hRcard, ← hScard]
    exact Subgroup.card_le_of_le hRS
  refine ⟨R, S, ⟨P, rfl⟩, ⟨Q, rfl⟩, hRS, hUS, hTS, hTR, hembed, fun hlt => ?_,
    fun heq => ⟨hequal heq, hequal heq ▸ hTR, fun hN => ?_⟩, fun hfail => ?_⟩
  · obtain ⟨x, hxS, hxR, hx, hxU⟩ := hstrict hlt
    exact ⟨⟨x, hxS, hxR, hx, hxU⟩, (hconseq x hx hxU).1, (hconseq x hx hxU).2,
      (Subgroup.map_subtype_le _).trans hRU⟩
  · obtain ⟨x, hx, hxU⟩ := hequalEmbed heq hN
    exact hconseq x hx hxU
  · have hnot : ∀ x ∈ A ⊓ normalizer ((R ⊔ T : Subgroup F) : Set F), x ∉ U → False :=
      fun x hx hxU => hfail.elim (fun h => h (hconseq x hx hxU).1)
        (fun h => h (hembedU x hx hxU))
    have heq : 2 ^ (Nat.card U).factorization 2 = 2 ^ (Nat.card A).factorization 2 := by
      refine le_antisymm hle (not_lt.1 fun hlt => ?_)
      obtain ⟨x, -, -, hx, hxU⟩ := hstrict hlt
      exact hnot x hx hxU
    refine ⟨heq, hequal heq ▸ hTR, fun x hx => ?_⟩
    by_contra hxU
    obtain ⟨y, hy, hyU⟩ := hequalEmbed heq (fun h => hxU (h hx))
    exact hnot y hy hyU

end CFSG.LocalAnalysis.ComponentInitial
