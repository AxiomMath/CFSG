module

public import CFSG.Walter.PSL2Facts.Even
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Basic

public section

namespace CFSG.ComponentClassification.AschbacherTheorem3.FourEight

open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools
open CFSG.Open
open scoped MatrixGroups Pointwise

variable {X : Type} [Group X] [Finite X]

theorem exists_torus {L P : Subgroup X} {n : ℕ} (hn : 2 ≤ n) (e : L ≃* PSL(2, GaloisField 2 n))
    (hP : IsSylowOf 2 P L) :
    IsElemAbelian 2 P ∧ Nat.card P = 2 ^ n ∧
    ∃ D : Subgroup X, D ≤ L ∧ D ≤ Subgroup.normalizer (P : Set X) ∧ Nat.card D = 2 ^ n - 1 ∧
      ∀ d ∈ D, ∀ p ∈ P, p ≠ 1 → d⁻¹ * p * d = p → d = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := hP
  set U : Sylow 2 PSL(2, GaloisField 2 n) := Q.mapSurjective (f := e.toMonoidHom) e.surjective
  have hU : (U : Subgroup PSL(2, GaloisField 2 n)) = (Q : Subgroup L).map e.toMonoidHom := rfl
  obtain ⟨hUel, hUcard⟩ := CFSG.Walter.psl2_even_sylow_two hn U
  obtain ⟨D₀, -, hD₀card, -, hsup, hreg⟩ := CFSG.Walter.psl2_even_normalizer_sylow_two hn U
  have hD₀N : D₀ ≤ Subgroup.normalizer ((U : Subgroup PSL(2, GaloisField 2 n)) :
      Set PSL(2, GaloisField 2 n)) := hsup ▸ le_sup_right
  have hPL : P ≤ L := by rw [← hQ]; exact Subgroup.map_subtype_le _
  have hmemP : ∀ l : L, (l : X) ∈ P ↔ e l ∈ (U : Subgroup PSL(2, GaloisField 2 n)) := by
    intro l
    rw [← hQ, hU]
    constructor
    · rintro ⟨l', hl', hll'⟩
      have : l' = l := Subtype.ext hll'
      rw [← this]
      exact ⟨l', hl', rfl⟩
    · rintro ⟨l', hl', hll'⟩
      have : l' = l := e.injective hll'
      rw [← this]
      exact ⟨l', hl', rfl⟩
  have hcardP : Nat.card P = 2 ^ n := by
    rw [← hUcard, hU, ← hQ, Subgroup.card_map_of_injective L.subtype_injective,
      Subgroup.card_map_of_injective e.injective]
  refine ⟨⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩, hcardP, ?_⟩
  ·
    have ha := (hmemP ⟨a, hPL a.2⟩).mp a.2
    have hb := (hmemP ⟨b, hPL b.2⟩).mp b.2
    have hc := congrArg Subtype.val
      (hUel.toIsMulCommutative.is_comm.comm ⟨_, ha⟩ ⟨_, hb⟩)
    simp only [Subgroup.coe_mul] at hc
    rw [← map_mul, ← map_mul] at hc
    have := congrArg Subtype.val (e.injective hc)
    exact Subtype.ext (by simpa using this)
  ·
    have hx' := (hmemP ⟨x, hPL hx⟩).mp hx
    have h2 := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2)
      (A := (U : Subgroup PSL(2, GaloisField 2 n))) _ hx'
    rw [← map_pow, ← map_one e] at h2
    have := congrArg Subtype.val (e.injective h2)
    simpa using this
  refine ⟨(D₀.comap e.toMonoidHom).map L.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · rintro _ ⟨l, hl, rfl⟩
    have hlD : e l ∈ D₀ := hl
    have hlN := hD₀N hlD
    rw [Subgroup.mem_normalizer_iff]
    intro p
    constructor
    · intro hp
      have hp' := (hmemP ⟨p, hPL hp⟩).mp hp
      have h1 := (Subgroup.mem_normalizer_iff.mp hlN _).mp hp'
      have heq : e l * e ⟨p, hPL hp⟩ * (e l)⁻¹ = e (l * ⟨p, hPL hp⟩ * l⁻¹) := by
        rw [map_mul, map_mul, map_inv]
      rw [heq] at h1
      have := (hmemP _).mpr h1
      simpa using this
    · intro hp
      have hpL : p ∈ L := by
        have h1 : (l : X) * p * (l : X)⁻¹ ∈ L := hPL (by simpa using hp)
        have h2 := L.mul_mem (L.mul_mem (L.inv_mem l.2) h1) l.2
        simpa [mul_assoc] using h2
      have hp' := (hmemP (l * ⟨p, hpL⟩ * l⁻¹)).mp (by simpa using hp)
      rw [map_mul, map_mul, map_inv] at hp'
      exact (hmemP ⟨p, hpL⟩).mpr ((Subgroup.mem_normalizer_iff.mp hlN _).mpr hp')
  · rw [Subgroup.card_map_of_injective L.subtype_injective, ← hD₀card]
    rw [Subgroup.comap_equiv_eq_map_symm']
    exact Subgroup.card_map_of_injective e.symm.injective
  · rintro _ ⟨l, hl, rfl⟩ p hp hp1 hfix
    have hlD : e l ∈ D₀ := hl
    have hp' := (hmemP ⟨p, hPL hp⟩).mp hp
    have hp1' : e ⟨p, hPL hp⟩ ≠ 1 := by
      intro h
      rw [← map_one e] at h
      exact hp1 (congrArg Subtype.val (e.injective h))
    obtain ⟨d, -, huniq⟩ := hreg _ hp' hp1' _ hp' hp1'
    have hl' : (e l)⁻¹ ∈ D₀ := D₀.inv_mem hlD
    have hfix' : (⟨(e l)⁻¹, hl'⟩ : D₀) * e ⟨p, hPL hp⟩ * ((⟨(e l)⁻¹, hl'⟩ : D₀) :
        PSL(2, GaloisField 2 n))⁻¹ = e ⟨p, hPL hp⟩ := by
      have h1 : (l : L)⁻¹ * ⟨p, hPL hp⟩ * l = ⟨p, hPL hp⟩ := Subtype.ext hfix
      calc ((e l)⁻¹ : PSL(2, GaloisField 2 n)) * e ⟨p, hPL hp⟩ * ((e l)⁻¹)⁻¹
          = e ((l : L)⁻¹ * ⟨p, hPL hp⟩ * l) := by rw [map_mul, map_mul, map_inv, inv_inv]
        _ = e ⟨p, hPL hp⟩ := by rw [h1]
    have h1 := huniq ⟨(e l)⁻¹, hl'⟩ hfix'
    have h2 := huniq 1 (by simp)
    have h3 : (e l)⁻¹ = 1 := by
      have := congrArg Subtype.val (h1.trans h2.symm)
      simpa using this
    rw [inv_eq_one, ← map_one e] at h3
    have := congrArg Subtype.val (e.injective h3)
    simpa using this

omit [Finite X] in
theorem card_ne_one (P : Subgroup X) :
    Nat.card {y : X | y ∈ P ∧ y ≠ 1} = Nat.card P - 1 := by
  have : {y : X | y ∈ P ∧ y ≠ 1} = (P : Set X) \ {1} := by
    ext
    simp
  rw [Nat.card_coe_set_eq, this, Set.ncard_sdiff_singleton_of_mem P.one_mem,
    ← Nat.card_coe_set_eq, SetLike.coe_sort_coe]

theorem exists_mem_rightConjugate {E P T D : Subgroup X} (hEP : E ⊓ P = ⊥)
    (hEC : E ≤ Subgroup.centralizer (P : Set X)) (hTle : T ≤ E ⊔ P) (hTP : T ⊓ P = ⊥)
    (hTE : T ⊓ E = ⊥) (hcardTE : Nat.card E ≤ Nat.card T)
    (hDE : D ≤ Subgroup.centralizer (E : Set X)) (hDP : D ≤ Subgroup.normalizer (P : Set X))
    (hcardD : Nat.card P - 1 ≤ Nat.card D)
    (hfree : ∀ d ∈ D, ∀ p ∈ P, p ≠ 1 → d⁻¹ * p * d = p → d = 1)
    {x : X} (hx : x ∈ E ⊔ P) (hxE : x ∉ E) (hxP : x ∉ P) :
    ∃ d ∈ D, x ∈ rightConjugate T d := by
  have hEN : E ≤ Subgroup.normalizer (P : Set X) :=
    hEC.trans (Subgroup.centralizer_le_normalizer _)
  have hPN : E ⊔ P ≤ Subgroup.normalizer (P : Set X) := sup_le hEN Subgroup.le_normalizer
  have hTN : T ≤ Subgroup.normalizer (P : Set X) := hTle.trans hPN
  have hcPT : Nat.card (P ⊔ T : Subgroup X) = Nat.card P * Nat.card T :=
    card_sup_of_le_normalizer hTN (by rw [inf_comm]; exact hTP)
  have hcEP : Nat.card (P ⊔ E : Subgroup X) = Nat.card P * Nat.card E :=
    card_sup_of_le_normalizer hEN (by rw [inf_comm]; exact hEP)
  have hPT : P ⊔ T = E ⊔ P := by
    apply Subgroup.eq_of_le_of_card_ge (sup_le le_sup_right hTle)
    rw [sup_comm E P, hcEP, hcPT]
    exact Nat.mul_le_mul_left _ hcardTE
  have hx1 : x ∈ (P : Set X) * (T : Set X) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left P T hTN, hPT]
    exact hx
  have hx2 : x ∈ (E : Set X) * (P : Set X) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right E P hEN]
    exact hx
  obtain ⟨p', hp', t, ht, hxt⟩ := Set.mem_mul.mp hx1
  obtain ⟨e, he, p, hp, hxe⟩ := Set.mem_mul.mp hx2
  set p₀ := p'⁻¹ * p with hp₀def
  have hp₀ : p₀ ∈ P := P.mul_mem (P.inv_mem hp') hp
  have hcomm : p'⁻¹ * e = e * p'⁻¹ := by
    have := Subgroup.mem_centralizer_iff.mp (hEC he) _ (P.inv_mem hp')
    exact this
  have hteq : t = e * p₀ := by
    calc t = p'⁻¹ * x := by rw [← hxt]; group
      _ = p'⁻¹ * e * p := by rw [← hxe]; group
      _ = e * p₀ := by rw [hcomm, hp₀def]; group
  have hp₀1 : p₀ ≠ 1 := by
    intro h
    rw [h, mul_one] at hteq
    have hmem : t ∈ T ⊓ E := ⟨ht, hteq ▸ he⟩
    rw [hTE, Subgroup.mem_bot] at hmem
    rw [hmem] at hteq
    apply hxP
    rw [← hxe, ← hteq, one_mul]
    exact hp
  have hp1 : p ≠ 1 := by
    intro h
    apply hxE
    rw [← hxe, h, mul_one]
    exact he
  let φ : D → {y : X | y ∈ P ∧ y ≠ 1} := fun d => ⟨(d : X)⁻¹ * p₀ * d, by
    refine ⟨?_, fun h => hp₀1 ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hDP d.2)) p₀).mp hp₀
      simpa using this
    · calc p₀ = (d : X) * ((d : X)⁻¹ * p₀ * d) * (d : X)⁻¹ := by group
        _ = 1 := by rw [h]; group⟩
  have hφ : Function.Injective φ := by
    intro d d' h
    have h' : (d : X)⁻¹ * p₀ * d = (d' : X)⁻¹ * p₀ * d' := congrArg Subtype.val h
    have hδ : (d' : X) * (d : X)⁻¹ ∈ D := D.mul_mem d'.2 (D.inv_mem d.2)
    have hfix : ((d' : X) * (d : X)⁻¹)⁻¹ * p₀ * ((d' : X) * (d : X)⁻¹) = p₀ := by
      calc ((d' : X) * (d : X)⁻¹)⁻¹ * p₀ * ((d' : X) * (d : X)⁻¹)
          = (d : X) * ((d' : X)⁻¹ * p₀ * d') * (d : X)⁻¹ := by group
        _ = (d : X) * ((d : X)⁻¹ * p₀ * d) * (d : X)⁻¹ := by rw [h']
        _ = p₀ := by group
    have h1 := hfree _ hδ p₀ hp₀ hp₀1 hfix
    rw [mul_inv_eq_one] at h1
    exact Subtype.ext h1.symm
  have hbij : Function.Bijective φ :=
    hφ.bijective_of_nat_card_le (by rw [card_ne_one]; exact hcardD)
  obtain ⟨d, hd⟩ := hbij.2 ⟨p, hp, hp1⟩
  have hd' : (d : X)⁻¹ * p₀ * d = p := congrArg Subtype.val hd
  refine ⟨d, d.2, ?_⟩
  rw [mem_rightConjugate_iff]
  have hde : (d : X)⁻¹ * e * d = e := by
    have := Subgroup.mem_centralizer_iff.mp (hDE d.2) e he
    calc (d : X)⁻¹ * e * d = (d : X)⁻¹ * (e * d) := by group
      _ = (d : X)⁻¹ * (d * e) := by rw [this]
      _ = e := by group
  have hxeq : (d : X) * x * (d : X)⁻¹ = t := by
    calc (d : X) * x * (d : X)⁻¹ = (d : X) * (e * p) * (d : X)⁻¹ := by rw [hxe]
      _ = (d : X) * (((d : X)⁻¹ * e * d) * ((d : X)⁻¹ * p₀ * d)) * (d : X)⁻¹ := by
          rw [hde, hd']
      _ = e * p₀ := by group
      _ = t := hteq.symm
  rw [hxeq]
  exact ht

omit [Finite X] in
theorem rightConjugate_injOn {E P T D : Subgroup X}
    (hEC : E ≤ Subgroup.centralizer (P : Set X)) (hTle : T ≤ E ⊔ P) (hTP : T ⊓ P = ⊥)
    (hTE : T ⊓ E = ⊥) (hT : T ≠ ⊥) (hDE : D ≤ Subgroup.centralizer (E : Set X))
    (hDP : D ≤ Subgroup.normalizer (P : Set X))
    (hfree : ∀ d ∈ D, ∀ p ∈ P, p ≠ 1 → d⁻¹ * p * d = p → d = 1)
    {d d' : X} (hd : d ∈ D) (hd' : d' ∈ D) (h : rightConjugate T d = rightConjugate T d') :
    d = d' := by
  have hEN : E ≤ Subgroup.normalizer (P : Set X) :=
    hEC.trans (Subgroup.centralizer_le_normalizer _)
  set δ := d * d'⁻¹ with hδdef
  have hδD : δ ∈ D := D.mul_mem hd (D.inv_mem hd')
  have hδN : δ ∈ Subgroup.normalizer (T : Set X) := by
    rw [← rightConjugate_eq_self_iff]
    calc rightConjugate T δ = rightConjugate (rightConjugate T d) d'⁻¹ := by
          rw [rightConjugate_mul]
      _ = rightConjugate (rightConjugate T d') d'⁻¹ := by rw [h]
      _ = T := by rw [rightConjugate_mul, mul_inv_cancel, rightConjugate_one]
  obtain ⟨t, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hT
  have htx : (t : X) ∈ (E : Set X) * (P : Set X) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right E P hEN]
    exact hTle t.2
  obtain ⟨e, he, p₀, hp₀, hte⟩ := Set.mem_mul.mp htx
  have hp₀1 : p₀ ≠ 1 := by
    intro h1
    rw [h1, mul_one] at hte
    have hmem : (t : X) ∈ T ⊓ E := ⟨t.2, hte ▸ he⟩
    rw [hTE, Subgroup.mem_bot] at hmem
    exact ht1 (Subtype.ext hmem)
  have hδe : δ⁻¹ * e * δ = e := by
    have := Subgroup.mem_centralizer_iff.mp (hDE hδD) e he
    calc δ⁻¹ * e * δ = δ⁻¹ * (e * δ) := by group
      _ = δ⁻¹ * (δ * e) := by rw [this]
      _ = e := by group
  have hconjT : δ⁻¹ * (t : X) * δ ∈ T := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hδN) t).mp t.2
    simpa using this
  have hmemTP : (t : X)⁻¹ * (δ⁻¹ * (t : X) * δ) ∈ T ⊓ P := by
    refine ⟨T.mul_mem (T.inv_mem t.2) hconjT, ?_⟩
    have hp₀δ : δ⁻¹ * p₀ * δ ∈ P := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hDP hδD)) p₀).mp hp₀
      simpa using this
    have heq : (t : X)⁻¹ * (δ⁻¹ * (t : X) * δ) = p₀⁻¹ * (δ⁻¹ * p₀ * δ) := by
      rw [← hte]
      calc (e * p₀)⁻¹ * (δ⁻¹ * (e * p₀) * δ)
          = p₀⁻¹ * e⁻¹ * ((δ⁻¹ * e * δ) * (δ⁻¹ * p₀ * δ)) := by group
        _ = p₀⁻¹ * (δ⁻¹ * p₀ * δ) := by rw [hδe]; group
    rw [heq]
    exact P.mul_mem (P.inv_mem hp₀) hp₀δ
  rw [hTP, Subgroup.mem_bot] at hmemTP
  have hfix : δ⁻¹ * p₀ * δ = p₀ := by
    have h1 : (t : X)⁻¹ * (δ⁻¹ * (t : X) * δ) = p₀⁻¹ * (δ⁻¹ * p₀ * δ) := by
      rw [← hte]
      calc (e * p₀)⁻¹ * (δ⁻¹ * (e * p₀) * δ)
          = p₀⁻¹ * e⁻¹ * ((δ⁻¹ * e * δ) * (δ⁻¹ * p₀ * δ)) := by group
        _ = p₀⁻¹ * (δ⁻¹ * p₀ * δ) := by rw [hδe]; group
    rw [h1] at hmemTP
    calc δ⁻¹ * p₀ * δ = p₀ * (p₀⁻¹ * (δ⁻¹ * p₀ * δ)) := by group
      _ = p₀ := by rw [hmemTP, mul_one]
  have h1 := hfree δ hδD p₀ hp₀ hp₀1 hfix
  rw [hδdef, mul_inv_eq_one] at h1
  exact h1

omit [Finite X] in
theorem exists_mem_normalizer_of_odd {P : Subgroup X} (hP : IsPGroup 2 P)
    (𝒞 : Set (Subgroup X)) (hinv : ∀ K ∈ 𝒞, ∀ s ∈ P, rightConjugate K s ∈ 𝒞)
    (hodd : Odd (Nat.card 𝒞)) :
    ∃ K ∈ 𝒞, P ≤ Subgroup.normalizer (K : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let act : MulAction P 𝒞 :=
    { smul := fun s K => ⟨rightConjugate (K : Subgroup X) (s : X)⁻¹,
        hinv K K.2 _ (P.inv_mem s.2)⟩
      one_smul := fun K => Subtype.ext (by
        change rightConjugate (K : Subgroup X) ((1 : P) : X)⁻¹ = K
        simp [rightConjugate_one])
      mul_smul := fun s s' K => Subtype.ext (by
        change rightConjugate (K : Subgroup X) ((s * s' : P) : X)⁻¹ =
          rightConjugate (rightConjugate (K : Subgroup X) (s' : X)⁻¹) (s : X)⁻¹
        rw [rightConjugate_mul, Subgroup.coe_mul, mul_inv_rev]) }
  have : Finite 𝒞 := Nat.finite_of_card_ne_zero (Nat.pos_of_ne_zero (by
    intro h
    rw [h] at hodd
    exact absurd hodd (by decide))).ne'
  have hmod := hP.card_modEq_card_fixedPoints 𝒞
  have hne : Nonempty (MulAction.fixedPoints P 𝒞) := by
    by_contra hcon
    rw [not_nonempty_iff] at hcon
    rw [@Nat.card_of_isEmpty (MulAction.fixedPoints P 𝒞) hcon] at hmod
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (Nat.modEq_zero_iff_dvd.mp hmod))
  obtain ⟨⟨K, hfix⟩⟩ := hne
  refine ⟨K, K.2, fun s hs => ?_⟩
  have h := congrArg Subtype.val (hfix ⟨s⁻¹, P.inv_mem hs⟩)
  change rightConjugate (K : Subgroup X) (s⁻¹)⁻¹ = K at h
  rw [inv_inv] at h
  exact (rightConjugate_eq_self_iff _ _).mp h

end CFSG.ComponentClassification.AschbacherTheorem3.FourEight
