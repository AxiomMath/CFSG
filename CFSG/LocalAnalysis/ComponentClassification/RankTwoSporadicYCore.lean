module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicDefs
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.ComponentClassification.RankTwoSporadic

open Subgroup CFSG.Open CFSG.ABGLocalTools
open scoped commutatorElement Pointwise

section Sylow

variable {G : Type*} [Group G] [Finite G]

theorem exists_conj_le_of_isSylowOf {P S M : Subgroup G} (hS : IsSylowOf 2 S M)
    (hP : IsPGroup 2 P) (hPM : P ≤ M) : ∃ m ∈ M, ∀ x ∈ P, m⁻¹ * x * m ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, rfl⟩ := hS
  obtain ⟨Q', hQ'⟩ := (hP.comap_subtype (K := M)).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M Q' Q
  refine ⟨(g : G)⁻¹, M.inv_mem g.2, fun x hx => ?_⟩
  have hx' : (⟨x, hPM hx⟩ : M) ∈ (Q' : Subgroup M) := hQ' hx
  have hmem : g * ⟨x, hPM hx⟩ * g⁻¹ ∈ (Q : Subgroup M) := by
    rw [← hg]
    change g * ⟨x, hPM hx⟩ * g⁻¹ ∈ ((g • Q' : Sylow 2 M) : Set M)
    rw [Sylow.coe_smul, Set.mem_smul_set_iff_inv_smul_mem, MulAut.smul_def,
      MulAut.conj_inv_apply]
    simpa [mul_assoc] using (show (⟨x, hPM hx⟩ : M) ∈ Q' from hx')
  exact ⟨_, hmem, by simp⟩

theorem IsSylowOf.map {H : Type*} [Group H] {p : ℕ} [Fact p.Prime] {T M : Subgroup G}
    (h : IsSylowOf p T M) (f : G →* H) : IsSylowOf p (T.map f) (M.map f) := by
  obtain ⟨Q, rfl⟩ := h
  refine ⟨Q.mapSurjective (f.subgroupMap_surjective M), ?_⟩
  rw [Sylow.coe_mapSurjective, Subgroup.map_map, Subgroup.map_map]
  rfl

end Sylow

section WSide

variable {W : Type*} [Group W] [Finite W]

theorem not_yWitness {X E M Y : Subgroup W} (hE : IsSylowOf 2 E M)
    (hEab : ∀ x ∈ E, x ^ 2 = 1) (hYX : Y ≤ X) (hYM : Y ≤ M)
    (hMY : M ≤ normalizer (Y : Set W)) (hN : nE X E ≤ Y) : ¬ YWitness X E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rintro (⟨w, hw, h4⟩ | ⟨P, hPN, hP, hcard⟩)
  ·
    obtain ⟨k, hk⟩ := h4
    have hwpos : orderOf w ≠ 0 := (orderOf_pos w).ne'
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hwpos (by simpa using hk)
    have hz : orderOf (w ^ k) = 4 := by
      rw [orderOf_pow_of_dvd hk0 ⟨4, by rw [hk]; ring⟩, hk]
      exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hk0)
    have hzY : w ^ k ∈ Y := Y.pow_mem (hN hw) k
    have hPz : IsPGroup 2 (zpowers (w ^ k)) := by
      refine IsPGroup.of_card (n := 2) ?_
      rw [Nat.card_zpowers, hz]
      norm_num
    obtain ⟨m, -, hm⟩ := exists_conj_le_of_isSylowOf hE hPz
      ((zpowers_le.mpr hzY).trans hYM)
    have hsq := hEab _ (hm _ (mem_zpowers (w ^ k)))
    have h2 : (w ^ k) ^ 2 = 1 := by
      have hc : (m⁻¹ * w ^ k * m) ^ 2 = m⁻¹ * (w ^ k) ^ 2 * m := by
        simpa using conj_pow (a := m⁻¹) (b := w ^ k) (i := 2)
      rw [hc] at hsq
      have := congrArg (fun y => m * y * m⁻¹) hsq
      simpa [mul_assoc] using this
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hz] at this
    norm_num at this
  ·
    obtain ⟨m, hm, hconj⟩ := exists_conj_le_of_isSylowOf hE hP ((hPN.trans hN).trans hYM)
    have hle : P.map (MulAut.conj m⁻¹).toMonoidHom ≤ E ⊓ X := by
      rintro _ ⟨x, hx, rfl⟩
      have hxY : x ∈ Y := hN (hPN hx)
      have hm' : m⁻¹ ∈ normalizer (Y : Set W) := hMY (M.inv_mem hm)
      have hconjY : m⁻¹ * x * m⁻¹⁻¹ ∈ Y := (mem_normalizer_iff.mp hm' x).mp hxY
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hconjY ⊢
      exact ⟨hconj x hx, hYX hconjY⟩
    have := Subgroup.card_le_of_le hle
    rw [Subgroup.card_map_of_injective (MulAut.conj m⁻¹).injective] at this
    omega

end WSide

section GSide

variable {G : Type*} [Group G]

theorem commutator_le_inf {A Q T : Subgroup G} (hTQ : T ≤ Q)
    (hTA : T ≤ normalizer (A : Set G)) :
    ⁅T, A ⊓ normalizer (Q : Set G)⁆ ≤ A ⊓ Q := by
  rw [commutator_le]
  intro v hv c hc
  rw [commutatorElement_def]
  refine ⟨A.mul_mem ((mem_normalizer_iff.mp (hTA hv) c).mp hc.1) (A.inv_mem hc.1), ?_⟩
  have h1 : c * v⁻¹ * c⁻¹ ∈ Q := (mem_normalizer_iff.mp hc.2 v⁻¹).mp (Q.inv_mem (hTQ hv))
  have h2 := Q.mul_mem (hTQ hv) h1
  simpa [mul_assoc] using h2

theorem iSup_inf_centralizer_le {A Q T : Subgroup G}
    (hQ : ∀ t ∈ T, t ≠ 1 → ∀ c ∈ A, c * t = t * c → c ∈ normalizer (Q : Set G)) :
    (⨆ t ∈ T, ⨆ (_ : t ≠ 1), A ⊓ centralizer ({t} : Set G)) ≤ A ⊓ normalizer (Q : Set G) := by
  refine iSup₂_le fun t ht => iSup_le fun ht1 => ?_
  rintro c ⟨hcA, hct⟩
  refine ⟨hcA, hQ t ht ht1 c hcA ?_⟩
  exact (mem_centralizer_iff.mp hct t rfl).symm

theorem inf_normalizer_le_normalizer_inf (A Q : Subgroup G) :
    Q ⊓ normalizer (A : Set G) ≤ normalizer ((A ⊓ Q : Subgroup G) : Set G) := by
  rintro n ⟨hnQ, hnA⟩
  rw [mem_normalizer_iff]
  intro y
  rw [mem_inf, mem_inf, ← mem_normalizer_iff.mp hnA y]
  constructor
  · rintro ⟨hyA, hyQ⟩
    exact ⟨hyA, Q.mul_mem (Q.mul_mem hnQ hyQ) (Q.inv_mem hnQ)⟩
  · rintro ⟨hyA, hyQ⟩
    refine ⟨hyA, ?_⟩
    have := Q.mul_mem (Q.mul_mem (Q.inv_mem hnQ) hyQ) hnQ
    simpa [mul_assoc] using this

theorem commutatorElement_mul_left_central {a b z z' : G} (hza : Commute z a) (hzb : Commute z b)
    (hz'a : Commute z' a) (hz'b : Commute z' b) (hzz' : Commute z z') :
    ⁅z * a, z' * b⁆ = ⁅a, b⁆ := by
  have hA : Commute (z * z') a := hza.mul_left hz'a
  have hB : Commute (z * z') b := hzb.mul_left hz'b
  have hc : Commute (z * z') ⁅a, b⁆ := by
    rw [commutatorElement_def]
    exact ((hA.mul_right hB).mul_right hA.inv_right).mul_right hB.inv_right
  have h1 : a * z' = z' * a := hz'a.eq.symm
  have h2 : z⁻¹ * b⁻¹ = b⁻¹ * z⁻¹ := hzb.inv_inv.eq
  have e : ⁅z * a, z' * b⁆ = z * z' * ⁅a, b⁆ * (z * z')⁻¹ := by
    simp only [commutatorElement_def, mul_inv_rev]
    calc z * a * (z' * b) * (a⁻¹ * z⁻¹) * (b⁻¹ * z'⁻¹)
        = z * (a * z') * b * a⁻¹ * (z⁻¹ * b⁻¹) * z'⁻¹ := by group
      _ = z * (z' * a) * b * a⁻¹ * (b⁻¹ * z⁻¹) * z'⁻¹ := by rw [h1, h2]
      _ = z * z' * (a * b * a⁻¹ * b⁻¹) * (z⁻¹ * z'⁻¹) := by group
      _ = z * z' * (a * b * a⁻¹ * b⁻¹) * (z'⁻¹ * z⁻¹) := by rw [hzz'.inv_inv.eq]
  rw [e, hc.eq, mul_inv_cancel_right]

end GSide

section Lift

variable {G W : Type*} [Group G] [Group W]

theorem centDer_le_map {A : Subgroup G} {X : Subgroup W} {ψ : normalizer (A : Set G) →* W}
    (hψ : IsActionHom A X ψ) (t : normalizer (A : Set G)) :
    centDer X (ψ t) ≤ ((A ⊓ centralizer ({(t : G)} : Set G)).subgroupOf
      (normalizer (A : Set G))).map ψ := by
  let P : Subgroup (normalizer (A : Set G)) :=
    A.subgroupOf (normalizer (A : Set G)) ⊓ (centralizer ({ψ t} : Set W)).comap ψ
  have hPmap : P.map ψ = X ⊓ centralizer ({ψ t} : Set W) := by
    apply le_antisymm
    · rintro _ ⟨p, ⟨hpA, hpC⟩, rfl⟩
      exact ⟨hψ.map_mem (p : G) hpA, hpC⟩
    · rintro x ⟨hxX, hxC⟩
      obtain ⟨a, ha, rfl⟩ := hψ.exists_eq x hxX
      exact ⟨⟨a, le_normalizer ha⟩, ⟨ha, hxC⟩, rfl⟩
  have hdisp : ∀ p ∈ P, ((t : G) * p * (t : G)⁻¹ * (p : G)⁻¹) ∈ A ∧
      ((t : G) * p * (t : G)⁻¹ * (p : G)⁻¹) ∈ centralizer (A : Set G) := by
    rintro p ⟨hpA, hpC⟩
    have hpA' : ((t : G) * p * (t : G)⁻¹) ∈ A :=
      (mem_normalizer_iff.mp t.2 (p : G)).mp hpA
    refine ⟨A.mul_mem hpA' (A.inv_mem hpA), ?_⟩
    have hcomm : ψ t * ψ p = ψ p * ψ t := mem_centralizer_iff.mp hpC (ψ t) rfl
    have hc : ψ (t * p * t⁻¹ * p⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [hcomm]
      group
    simpa using (hψ.eq_one_iff _).mp hc
  have hPP : ⁅P, P⁆ ≤ (A ⊓ centralizer ({(t : G)} : Set G)).subgroupOf
      (normalizer (A : Set G)) := by
    rw [commutator_le]
    intro p hp q hq
    have hpA : (p : G) ∈ A := hp.1
    have hqA : (q : G) ∈ A := hq.1
    have hcoe : ((⁅p, q⁆ : normalizer (A : Set G)) : G) = ⁅(p : G), (q : G)⁆ := by
      simp [commutatorElement_def]
    change ((⁅p, q⁆ : normalizer (A : Set G)) : G) ∈ A ⊓ centralizer ({(t : G)} : Set G)
    rw [hcoe]
    refine ⟨?_, ?_⟩
    · rw [commutatorElement_def]
      exact A.mul_mem (A.mul_mem (A.mul_mem hpA hqA) (A.inv_mem hpA)) (A.inv_mem hqA)
    · obtain ⟨hzpA, hzpC⟩ := hdisp p hp
      obtain ⟨hzqA, hzqC⟩ := hdisp q hq
      set zp := (t : G) * p * (t : G)⁻¹ * (p : G)⁻¹ with hzp
      set zq := (t : G) * q * (t : G)⁻¹ * (q : G)⁻¹ with hzq
      have hcomm : ∀ {z y : G}, z ∈ centralizer (A : Set G) → y ∈ A → Commute z y :=
        fun hz hy => (mem_centralizer_iff.mp hz _ hy).symm
      have hconj : (t : G) * ⁅(p : G), (q : G)⁆ * (t : G)⁻¹ = ⁅(p : G), (q : G)⁆ := by
        have e1 : (t : G) * p * (t : G)⁻¹ = zp * p := by rw [hzp]; group
        have e2 : (t : G) * q * (t : G)⁻¹ = zq * q := by rw [hzq]; group
        calc (t : G) * ⁅(p : G), (q : G)⁆ * (t : G)⁻¹
            = ⁅(t : G) * p * (t : G)⁻¹, (t : G) * q * (t : G)⁻¹⁆ := by
              simp only [commutatorElement_def]; group
          _ = ⁅zp * p, zq * q⁆ := by rw [e1, e2]
          _ = _ := commutatorElement_mul_left_central (hcomm hzpC hpA) (hcomm hzpC hqA)
              (hcomm hzqC hpA) (hcomm hzqC hqA) (hcomm hzpC hzqA)
      refine mem_centralizer_iff.mpr ?_
      rintro _ rfl
      calc (t : G) * ⁅(p : G), (q : G)⁆ = (t : G) * ⁅(p : G), (q : G)⁆ * (t : G)⁻¹ * t := by
            group
        _ = ⁅(p : G), (q : G)⁆ * t := by rw [hconj]
  calc centDer X (ψ t) = ⁅P.map ψ, P.map ψ⁆ := by rw [hPmap]; rfl
    _ = (⁅P, P⁆).map ψ := (Subgroup.map_commutator P P ψ).symm
    _ ≤ _ := Subgroup.map_mono hPP

end Lift

section Main

variable {G W : Type*} [Group G] [Group W] [Finite G] [Finite W]

theorem not_yWitness_map {A Q T : Subgroup G} {X : Subgroup W}
    {ψ : normalizer (A : Set G) →* W} (hψ : IsActionHom A X ψ)
    (hTsyl : IsSylowOf 2 T (Q ⊓ normalizer (A : Set G))) (hTab : ∀ x ∈ T, x ^ 2 = 1)
    (hQ : ∀ t ∈ T, t ≠ 1 → ∀ c ∈ A, c * t = t * c → c ∈ normalizer (Q : Set G)) :
    ¬ YWitness X ((T.subgroupOf (normalizer (A : Set G))).map ψ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTN : T ≤ normalizer (A : Set G) := hTsyl.le.trans inf_le_right
  have hTQ : T ≤ Q := hTsyl.le.trans inf_le_left
  have hMN : Q ⊓ normalizer (A : Set G) ≤ normalizer (A : Set G) := inf_le_right
  have hT' : IsSylowOf 2 (T.subgroupOf (normalizer (A : Set G)))
      ((Q ⊓ normalizer (A : Set G)).subgroupOf (normalizer (A : Set G))) := by
    rw [← isSylowOf_map_subtype_iff, subgroupOf_map_subtype, subgroupOf_map_subtype,
      inf_eq_left.mpr hTN, inf_eq_left.mpr hMN]
    exact hTsyl
  refine not_yWitness (M := ((Q ⊓ normalizer (A : Set G)).subgroupOf
      (normalizer (A : Set G))).map ψ)
    (Y := ((A ⊓ Q).subgroupOf (normalizer (A : Set G))).map ψ) (IsSylowOf.map hT' ψ) ?_ ?_ ?_ ?_ ?_
  ·
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_pow]
    have : y ^ 2 = 1 := Subtype.ext (by simpa using hTab _ hy)
    rw [this, map_one]
  ·
    rintro _ ⟨y, hy, rfl⟩
    exact hψ.map_mem (y : G) hy.1
  ·
    refine Subgroup.map_mono fun y hy => ?_
    exact ⟨hy.2, y.2⟩
  ·
    refine le_trans (Subgroup.map_mono ?_) (Subgroup.le_normalizer_map ψ)
    intro m hm
    rw [mem_normalizer_iff]
    intro y
    have h := mem_normalizer_iff.mp (inf_normalizer_le_normalizer_inf A Q hm) (y : G)
    exact h
  ·
    have hΓ : gammaE X ((T.subgroupOf (normalizer (A : Set G))).map ψ) ≤
        ((A ⊓ normalizer (Q : Set G)).subgroupOf (normalizer (A : Set G))).map ψ := by
      refine iSup₂_le fun e he => iSup_le fun he1 => ?_
      obtain ⟨t, ht, rfl⟩ := he
      have ht1 : (t : G) ≠ 1 := fun h => he1 (by rw [show t = 1 from Subtype.ext h, map_one])
      refine (centDer_le_map hψ t).trans (Subgroup.map_mono fun c hc => ?_)
      refine ⟨hc.1, hQ (t : G) ht ht1 (c : G) hc.1 ?_⟩
      exact (mem_centralizer_iff.mp hc.2 (t : G) rfl).symm
    have hcomm : ⁅T.subgroupOf (normalizer (A : Set G)),
        (A ⊓ normalizer (Q : Set G)).subgroupOf (normalizer (A : Set G))⁆ ≤
        (A ⊓ Q).subgroupOf (normalizer (A : Set G)) := by
      rw [commutator_le]
      intro v hv c hc
      have h := commutator_le_inf hTQ hTN
      rw [commutator_le] at h
      have hvc := h (v : G) hv (c : G) hc
      change ((⁅v, c⁆ : normalizer (A : Set G)) : G) ∈ A ⊓ Q
      simpa [commutatorElement_def] using hvc
    calc nE X ((T.subgroupOf (normalizer (A : Set G))).map ψ)
        ≤ ⁅(T.subgroupOf (normalizer (A : Set G))).map ψ,
            ((A ⊓ normalizer (Q : Set G)).subgroupOf (normalizer (A : Set G))).map ψ⁆ :=
          commutator_mono le_rfl hΓ
      _ = (⁅T.subgroupOf (normalizer (A : Set G)),
            (A ⊓ normalizer (Q : Set G)).subgroupOf (normalizer (A : Set G))⁆).map ψ :=
          (Subgroup.map_commutator _ _ ψ).symm
      _ ≤ _ := Subgroup.map_mono hcomm

end Main

end CFSG.ComponentClassification.RankTwoSporadic
