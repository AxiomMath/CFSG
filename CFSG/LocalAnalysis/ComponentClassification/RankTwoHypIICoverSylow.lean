module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo2Census
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutTables
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo2Roots

public section

namespace CFSG.ComponentClassification.RankTwoHypIICover

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.RankTwoSporadic.Cert
open CFSG.ComponentClassification.RankTwoSporadic.RootCensus
open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
  CFSG.Certificates.Native

section Abstract

variable {W : Type*} [Group W] [Finite W]

theorem exists_mem_of_not_four_dvd_index {X : Subgroup W} [X.Normal] (hXi : ¬ 4 ∣ X.index)
    {E : Subgroup W} (hE : IsElemAbelian 2 E) (hE4 : 4 ≤ Nat.card E) :
    ∃ a ∈ E, a ≠ 1 ∧ a ∈ X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (isPGroup_of_isElemAbelian hE).exists_card_eq
  have h1 : (X.subgroupOf E).index ∣ X.index := relIndex_dvd_index_of_normal X E
  have h2 : (X.subgroupOf E).index ∣ 2 ^ k := hk ▸ index_dvd_card _
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
  have hidx : (X.subgroupOf E).index ≤ 2 := by
    rcases Nat.lt_or_ge i 2 with hi2 | hi2
    · rw [hi]
      calc 2 ^ i ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 2 := by norm_num
    · exfalso
      apply hXi
      rw [hi] at h1
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
      exact (Nat.pow_dvd_pow 2 hi2).trans h1
  have hmul := (X.subgroupOf E).card_mul_index
  have hcard : 2 ≤ Nat.card (X.subgroupOf E) := by
    by_contra hlt
    push Not at hlt
    have : Nat.card E ≤ 2 := by
      rw [← hmul]
      calc Nat.card (X.subgroupOf E) * (X.subgroupOf E).index ≤ 1 * 2 :=
            Nat.mul_le_mul (by omega) hidx
        _ = 2 := by norm_num
    omega
  have hne : X.subgroupOf E ≠ ⊥ := (Subgroup.one_lt_card_iff_ne_bot _).mp (by omega)
  obtain ⟨⟨⟨a, haE⟩, haX⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  refine ⟨a, haE, fun h1 => ha1 (Subtype.ext (Subtype.ext h1)), ?_⟩
  rwa [mem_subgroupOf] at haX

theorem yCensusII_of_sylowReps {X : Subgroup W} (hX : X.Normal) (hXi : ¬ 4 ∣ X.index)
    (S : Sylow 2 W) {k : ℕ} (y : ℕ → W)
    (hrep : ∀ u ∈ (S : Subgroup W), u ^ 2 = 1 → u ≠ 1 →
      ∃ j < k, ∃ c ∈ (S : Subgroup W), u = c * y j * c⁻¹)
    (hw : ∀ j < k, y j ∈ X → ∀ b ∈ (S : Subgroup W), b ^ 2 = 1 → b ∉ X →
      b * y j = y j * b → MonoW X false (closure {y j, b})) :
    YCensus X (· ≤ X) := by
  intro E hE hE4 hEX
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨v, hvE, hvX⟩ : ∃ v ∈ E, v ∉ X := by
    by_contra hcon
    push Not at hcon
    exact hEX hcon
  obtain ⟨a, haE, ha1, haX⟩ := exists_mem_of_not_four_dvd_index (X := X) hXi hE hE4
  obtain ⟨Q, hQ⟩ := (isPGroup_of_isElemAbelian hE).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq W S Q
  have key : ∀ e ∈ E, g⁻¹ * e * g ∈ (S : Subgroup W) := by
    intro e he
    have h1 : e ∈ (Q : Subgroup W) := hQ he
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      MulAut.smul_def, MulAut.inv_def, MulAut.conj_symm_apply] at h1
    exact h1
  have hconj2 : ∀ (h z : W), z ^ 2 = 1 → (h * z * h⁻¹) ^ 2 = 1 := fun h z hz => by
    rw [conj_pow, hz, mul_one, mul_inv_cancel]
  have ha2 : (g⁻¹ * a * g) ^ 2 = 1 := by
    have := hconj2 g⁻¹ a (hE.2 a haE)
    rwa [inv_inv] at this
  have ha'1 : g⁻¹ * a * g ≠ 1 := fun h1 => ha1 (by
    have := congrArg (fun z => g * z * g⁻¹) h1
    simpa [mul_assoc] using this)
  obtain ⟨j, hj, c, hcS, hcj⟩ := hrep _ (key a haE) ha2 ha'1
  set h : W := c⁻¹ * g⁻¹ with hh
  have hxa : h * a * h⁻¹ = y j := by
    calc h * a * h⁻¹ = c⁻¹ * (g⁻¹ * a * g) * c := by rw [hh]; group
      _ = c⁻¹ * (c * y j * c⁻¹) * c := by rw [hcj]
      _ = y j := by group
  have hbS : h * v * h⁻¹ ∈ (S : Subgroup W) := by
    have e1 : h * v * h⁻¹ = c⁻¹ * (g⁻¹ * v * g) * c := by rw [hh]; group
    rw [e1]
    exact (S : Subgroup W).mul_mem ((S : Subgroup W).mul_mem ((S : Subgroup W).inv_mem hcS)
      (key v hvE)) hcS
  have hb2 : (h * v * h⁻¹) ^ 2 = 1 := hconj2 h v (hE.2 v hvE)
  have hbX : h * v * h⁻¹ ∉ X := fun hb => hvX (by
    have := hX.conj_mem _ hb h⁻¹
    simpa [mul_assoc] using this)
  have hyX : y j ∈ X := hxa ▸ hX.conj_mem a haX h
  have hcomm : h * v * h⁻¹ * y j = y j * (h * v * h⁻¹) := by
    rw [← hxa]
    have hva : v * a = a * v := congrArg Subtype.val (hE.1.is_comm.comm ⟨v, hvE⟩ ⟨a, haE⟩)
    calc h * v * h⁻¹ * (h * a * h⁻¹) = h * (v * a) * h⁻¹ := by group
      _ = h * (a * v) * h⁻¹ := by rw [hva]
      _ = h * a * h⁻¹ * (h * v * h⁻¹) := by group
  have hM := hw j hj hyX _ hbS hb2 hbX hcomm
  have hmap : closure ({y j, h * v * h⁻¹} : Set W) =
      (closure ({a, v} : Set W)).map (MulAut.conj h).toMonoidHom := by
    rw [MonoidHom.map_closure, Set.image_pair]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hxa]
  rw [hmap, monoW_map_conj_iff hX] at hM
  have hle : closure ({a, v} : Set W) ≤ E := by
    rw [closure_le]
    rintro z (rfl | rfl)
    · exact haE
    · exact hvE
  rcases monoW_mono hle hM with h' | ⟨h', -⟩
  · exact Or.inl h'
  · exact absurd h' (by decide)

end Abstract

structure PairWit where
  w : List NFac
  m : ℕ
deriving Inhabited

@[expose] def pairWitOK (n : ℕ) (inX : Array ℕ → Bool) (x b : Array ℕ) (pw : PairWit) : Bool :=
  let y := powA n (nA n #[x, b] pw.w) pw.m
  validA n x && validA n b && pw.w.all (NFac.ok n inX #[x, b]) &&
    !(eqA n (compA n y y) (idA n)) && eqA n (powA n y 4) (idA n)

variable {n : ℕ}

theorem permsA_pair (x b : Array ℕ) : permsA n #[x, b] = {permOfArr n x, permOfArr n b} := by
  ext g
  simp only [permsA, Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨k, hk, rfl⟩
    have hk' : k < 2 := by simpa using hk
    interval_cases k
    · exact Or.inl (by simp)
    · exact Or.inr (by simp)
  · rintro (rfl | rfl)
    · exact ⟨0, by simp, by simp⟩
    · exact ⟨1, by simp, by simp⟩

theorem pairWitOK_sound {inX : Array ℕ → Bool} {X : Subgroup (Equiv.Perm (Fin n))}
    (hin : ∀ a, validA n a = true → inX a = true → permOfArr n a ∈ X) {x b : Array ℕ}
    {pw : PairWit} (h : pairWitOK n inX x b pw = true) :
    MonoW X false (closure {permOfArr n x, permOfArr n b}) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  simp only [pairWitOK, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨hx, hb⟩, hw⟩, h2⟩, h4⟩ := h
  have hbas : ∀ k < (#[x, b] : Array (Array ℕ)).size,
      validA n (#[x, b] : Array (Array ℕ))[k]! = true := by
    intro k hk
    have hk' : k < 2 := by simpa using hk
    interval_cases k
    · simpa using hx
    · simpa using hb
  obtain ⟨y, hyN, hy⟩ := rep_nA hin hbas hw
  rw [permsA_pair] at hyN
  have hym := rep_powA hy pw.m
  have h2' : ¬ (y ^ pw.m) ^ 2 ^ 1 = 1 := by
    intro hc
    rw [pow_one, sq] at hc
    rw [(eqA_iff (rep_compA hym hym) rep_idA).2 hc] at h2
    exact Bool.noConfusion h2
  have h4' : (y ^ pw.m) ^ 2 ^ (1 + 1) = 1 := eq_of_eqA (rep_powA hym 4) rep_idA h4
  have hord := orderOf_eq_prime_pow h2' h4'
  refine Or.inl ⟨y ^ pw.m, pow_mem hyN _, ?_⟩
  rw [hord]
  norm_num

theorem exists_of_allProds {hn : 1 ≤ n} {S : Array (Array ℕ)} {k : ℕ} {hk : k ≤ S.size}
    {base : List (Fin n)} {hb : base.Nodup} {Wd : Array (List ℤ)} {chunks : ℕ} (hc : 0 < chunks)
    (h : rawChainOK n (S.extract 0 k) S (base.map Fin.val).toArray Wd chunks = true)
    {p : Array ℕ → Bool}
    (hp : allProds n (rawLevels n S (base.map Fin.val).toArray) p 0 (idA n) = true)
    {G : Equiv.Perm (Fin n)}
    (hG : G ∈ (RawSchreierDatum.ofArrays n hn S k hk base hb Wd).originalSubgroup) :
    ∃ a, Rep n a G ∧ p a = true := by
  have hF := chainCheckFacts h
  have hsift := (J2Cover.ofArrays_mem_iff hc h (rep_arrOf G)).mpr hG
  have hinv : ∀ i (hi : i < (rawLevels n S (base.map Fin.val).toArray).size),
      ∀ k' < (rawLevels n S (base.map Fin.val).toArray)[i].pts.size,
        isInvA n (rawLevels n S (base.map Fin.val).toArray)[i].tr[k']!
          (rawLevels n S (base.map Fin.val).toArray)[i].trInv[k']! = true := by
    intro i hi k' hk'
    have hi' : i < (base.map Fin.val).toArray.size := by
      rwa [CFSG.Sporadic.Schreier.Tits.size_rawLevels] at hi
    have hL := ChainArrays.levelFacts_of_levelOK (hF.level i hi')
    rw [← getElem!_pos (rawLevels n S (base.map Fin.val).toArray) i hi] at hk' ⊢
    exact hL.tr_inv k' hk'
  obtain ⟨a, ha, hpa⟩ := allProds_spec hinv (rawLevels n S (base.map Fin.val).toArray).size 0
    (by simp) _ _ rep_idA hp _ _ (rep_arrOf G) hsift
  exact ⟨a, by rwa [one_mul] at ha, hpa⟩

end CFSG.ComponentClassification.RankTwoHypIICover
