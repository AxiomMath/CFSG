module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicEndgame

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Endgame

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoSporadic CFSG.ComponentClassification.RankTwoSporadic.J2End
open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.RankThree.Native
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

theorem mem_normalizer_conj_of_commute' (hA : standardComponentIsStandard A) {g t c : G}
    (ht : t ∈ rightConjugate (centralizer (A : Set G)) g) (ht1 : t ≠ 1) (ht2 : t ^ 2 = 1)
    (hc : c * t = t * c) : c ∈ normalizer (rightConjugate A g : Set G) := by
  have hK := tightlyEmbedded_centralizer_of_standard hA
  have h := mem_normalizer_of_commute_of_tightlyEmbedded (tightlyEmbedded_rightConjugate' hK g)
    ht ht1 ht2 hc
  rw [mem_normalizer_conj_iff] at h ⊢
  rwa [hA.2.2.2.1] at h

omit [Finite G] in
theorem eq_one_of_mem_inf' (hA : standardComponentIsStandard A) {y z : G}
    (hy : y ∉ normalizer (A : Set G)) (hzK : z ∈ centralizer (A : Set G))
    (hzy : z ∈ rightConjugate (centralizer (A : Set G)) y) (hz2 : z ^ 2 = 1) : z = 1 := by
  have hK := tightlyEmbedded_centralizer_of_standard hA
  have hyK : y ∉ normalizer (centralizer (A : Set G) : Set G) := by
    rw [hA.2.2.2.1]
    exact hy
  have hodd := (hK.2 y hyK).of_dvd_nat (Subgroup.orderOf_dvd_natCard _ (mem_inf.mpr ⟨hzK, hzy⟩))
  rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hz2) with h | h
  · exact orderOf_eq_one_iff.mp h
  · rw [h] at hodd
    exact absurd hodd (by decide)

theorem inf_centralizer_eq_bot' (hA : standardComponentIsStandard A) {g : G}
    (hg : g ∉ normalizer (A : Set G)) {T : Subgroup G} (hT : IsPGroup 2 T)
    (hTK : T ≤ rightConjugate (centralizer (A : Set G)) g) :
    T ⊓ centralizer (A : Set G) = ⊥ := by
  have hK := tightlyEmbedded_centralizer_of_standard hA
  have hgK : g ∉ normalizer (centralizer (A : Set G) : Set G) := by
    rw [hA.2.2.2.1]
    exact hg
  exact two_subgroup_of_odd_eq_bot _ (centralizer (A : Set G) ⊓
    rightConjugate (centralizer (A : Set G)) g) hT.to_inf_left (hK.2 g hgK)
    (le_inf inf_le_right (inf_le_left.trans hTK))

theorem exc_of_overlap (hA : standardComponentIsStandard A) {W : Type*} [Group W] [Finite W]
    {X : Subgroup W} {ψ : normalizer (A : Set G) →* W} (hψ : IsActionHom A X ψ)
    {Exc : Subgroup W → Prop} (hc : YCensus X Exc) {g : G} (hg : g ∉ normalizer (A : Set G))
    {T : Subgroup G}
    (hT : IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g ⊓ normalizer (A : Set G)))
    (hTab : ∀ x ∈ T, x ^ 2 = 1) (hT4 : 4 ≤ Nat.card T) :
    Exc ((T.subgroupOf (normalizer (A : Set G))).map ψ) := by
  by_contra hExc
  have hK := tightlyEmbedded_centralizer_of_standard hA
  have hTK : T ≤ rightConjugate (centralizer (A : Set G)) g := hT.le.trans inf_le_left
  have hQ : ∀ t ∈ T, t ≠ 1 → ∀ c ∈ A, c * t = t * c →
      c ∈ normalizer (rightConjugate (centralizer (A : Set G)) g : Set G) :=
    fun t ht ht1 c _ hct => mem_normalizer_of_commute_of_tightlyEmbedded
      (tightlyEmbedded_rightConjugate' hK g) (hTK ht) ht1 (hTab t ht) hct
  refine not_yWitness_map hψ hT hTab hQ (hc _ ?_ ?_ hExc)
  · refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · rintro ⟨_, x, hx, rfl⟩ ⟨_, y, hy, rfl⟩
      apply Subtype.ext
      simp only [coe_mul]
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact commute_of_sq_eq_one hTab hx hy
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow]
      have : x ^ 2 = 1 := Subtype.ext (by simpa using hTab _ hx)
      rw [this, map_one]
  · have hTN : T ≤ normalizer (A : Set G) := hT.le.trans inf_le_right
    rw [card_map_eq_of_inf_centralizer hψ (inf_centralizer_eq_bot' hA hg hT.isPGroup hTK),
      Nat.card_congr (subgroupOfEquivOfLe hTN).toEquiv]
    exact hT4

theorem exc_of_overlap_conj (hA : standardComponentIsStandard A) {W : Type*} [Group W]
    [Finite W] {X : Subgroup W} {ψ : normalizer (A : Set G) →* W} (hψ : IsActionHom A X ψ)
    {Exc : Subgroup W → Prop} (hc : YCensus X Exc) {g y : G}
    (hne : rightConjugate (centralizer (A : Set G)) y ≠
      rightConjugate (centralizer (A : Set G)) g)
    {T' : Subgroup G} (hT' : IsSylowOf 2 T' (rightConjugate (centralizer (A : Set G)) y))
    (hTN : T' ≤ normalizer (rightConjugate A g : Set G)) (hTab : ∀ x ∈ T', x ^ 2 = 1)
    (hT4 : 4 ≤ Nat.card T') :
    Exc (((rightConjugate T' g⁻¹).subgroupOf (normalizer (A : Set G))).map ψ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : IsSylowOf 2 (rightConjugate T' g⁻¹)
      (rightConjugate (centralizer (A : Set G)) (y * g⁻¹)) := by
    rw [← rightConjugate_mul]
    exact isSylowOf_conj hT' g⁻¹
  have hyg : y * g⁻¹ ∉ normalizer (A : Set G) := by
    intro h
    rw [← hA.2.2.2.1, ← rightConjugate_eq_self_iff] at h
    apply hne
    rw [show y = y * g⁻¹ * g by group, ← rightConjugate_mul, h]
  have hN : rightConjugate T' g⁻¹ ≤ normalizer (A : Set G) := by
    intro x hx
    have hx' := hTN ((mem_rightConjugate_iff _ g⁻¹ x).mp hx)
    rw [mem_normalizer_conj_iff] at hx'
    simpa [mul_assoc] using hx'
  refine exc_of_overlap hA hψ hc hyg (hT2.of_le (le_inf hT2.le hN) inf_le_left) ?_ ?_
  · intro x hx
    have h1 := hTab _ ((mem_rightConjugate_iff _ g⁻¹ x).mp hx)
    have h2 : (g⁻¹ * x * g⁻¹⁻¹) ^ 2 = g⁻¹ * x ^ 2 * g⁻¹⁻¹ := conj_pow
    rw [h2] at h1
    have := congrArg (fun z => g * z * g⁻¹) h1
    simpa [mul_assoc] using this
  · rw [rightConjugate_card]
    exact hT4

structure EndFactsOut {n : ℕ} (R P E₀ : Subgroup (Equiv.Perm (Fin n)))
    (e₀ : Equiv.Perm (Fin n)) (Q : Equiv.Perm (Fin n) → Prop) : Prop where
  mem_P : e₀ ∈ P
  mem : e₀ ∈ E₀
  Q_of_mem : ∀ e ∈ E₀, e ≠ 1 → Q e
  Q_conj : ∀ g ∈ R, ∀ x, Q x → Q (g * x * g⁻¹)
  exists_conj : ∃ a₀ ∈ P,
    (∀ e ∈ E₀, ∀ e' ∈ E₀, e * (a₀⁻¹ * e' * a₀) = a₀⁻¹ * e' * a₀ * e) ∧
    a₀⁻¹ * e₀ * a₀ ∉ E₀ ∧
    ∃ x : Fin 8 → Equiv.Perm (Fin n), (∀ i, x i ∈ P ∧ ∀ e ∈ E₀, x i * e = e * x i) ∧
      tree3 x = e₀ * (a₀⁻¹ * e₀ * a₀)
  not_Q : ∀ z ∈ ⁅P ⊓ centralizer (E₀ : Set (Equiv.Perm (Fin n))),
    P ⊓ centralizer (E₀ : Set (Equiv.Perm (Fin n)))⁆, z ^ 2 = 1 → z ≠ 1 → ¬ Q z

theorem false_of_endgame_out (hA : standardComponentIsStandard A)
    (hZ : Odd (Nat.card (center ↥A))) {n : ℕ} {R P E₀ : Subgroup (Equiv.Perm (Fin n))}
    {e₀ : Equiv.Perm (Fin n)} {Q : Equiv.Perm (Fin n) → Prop} (hPR : P ≤ R)
    (hRN : R ≤ normalizer (P : Set (Equiv.Perm (Fin n))))
    (hcomm : ∀ x y : ↥R, ⁅x, y⁆ ∈ P.subgroupOf R) (hF : EndFactsOut R P E₀ e₀ Q)
    {ψ : normalizer (A : Set G) →* ↥R} (hψ : IsActionHom A (P.subgroupOf R) ψ)
    (hc : YCensus (P.subgroupOf R) (ExcClass R E₀))
    {g : G} (hg : g ∉ normalizer (A : Set G)) {RK T : Subgroup G}
    (hR : IsSylowOf 2 RK (centralizer (A : Set G))) (hRab : ∀ x ∈ RK, x ^ 2 = 1)
    (hR4 : 4 ≤ Nat.card RK)
    (hT : IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g)) (hTab : ∀ x ∈ T, x ^ 2 = 1)
    (hT4 : 4 ≤ Nat.card T) (hTN : T ≤ normalizer (A : Set G))
    (hRN' : RK ≤ normalizer (rightConjugate A g : Set G)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hmemP, he₀, hQE, hQc, ⟨a₀, ha₀P, hcomm₀, hnot₀, x, hx, htree⟩, hnotQ⟩ := hF
  set K := centralizer (A : Set G) with hK
  have hT1 : IsSylowOf 2 T (rightConjugate K g ⊓ normalizer (A : Set G)) :=
    hT.of_le (le_inf hT.le hTN) inf_le_left
  obtain ⟨w, hwR, hw⟩ := exc_of_overlap hA hψ hc hg hT1 hTab hT4
  have hconjP : ∀ {v y : Equiv.Perm (Fin n)}, v ∈ R → y ∈ P → v * y * v⁻¹ ∈ P :=
    fun hv hy => (mem_normalizer_iff.mp (hRN hv) _).mp hy
  have he₀1 : e₀ ≠ 1 := fun h1 => hnot₀ (by rw [h1, mul_one, inv_mul_cancel]; exact one_mem _)
  obtain ⟨t, htT, htψ⟩ := exists_of_excClass hw he₀
  have ht2 : (t : G) ^ 2 = 1 := hTab _ htT
  have htK : (t : G) ∈ rightConjugate K g := hT.le htT
  have htX : ψ t ∈ P.subgroupOf R := by
    change ((ψ t : ↥R) : Equiv.Perm (Fin n)) ∈ P
    rw [htψ]
    exact hconjP hwR hmemP
  have hψt1 : ((ψ t : ↥R) : Equiv.Perm (Fin n)) ≠ 1 := by
    rw [htψ]
    intro h1
    apply he₀1
    have := congrArg (fun y => w⁻¹ * y * w) h1
    simpa [mul_assoc] using this
  have ht1 : (t : G) ≠ 1 := by
    intro h1
    apply hψt1
    rw [show t = 1 from Subtype.ext h1, map_one, OneMemClass.coe_one]
  have hlift : ∀ y ∈ P, ∃ (b : G) (hb : b ∈ A),
      ((ψ ⟨b, le_normalizer hb⟩ : ↥R) : Equiv.Perm (Fin n)) = w * y * w⁻¹ := by
    intro y hy
    obtain ⟨b, hb, hbe⟩ := hψ.exists_eq (⟨w * y * w⁻¹, R.mul_mem (R.mul_mem hwR (hPR hy))
      (R.inv_mem hwR)⟩ : ↥R) (hconjP hwR hy)
    exact ⟨b, hb, by rw [hbe]⟩
  obtain ⟨a, haA, haψ⟩ := hlift a₀ ha₀P
  choose b hbA hbψ using fun i => hlift (x i) (hx i).1
  set aN : normalizer (A : Set G) := ⟨a, le_normalizer haA⟩ with haN
  set aN' : normalizer (A : Set G) := ⟨a⁻¹, le_normalizer (A.inv_mem haA)⟩ with haN'
  have hcommT : ∀ y ∈ T, (t : G) * (a⁻¹ * y * a) = a⁻¹ * y * a * t := by
    intro y hy
    obtain ⟨ey, hey, heyψ⟩ := mem_of_excClass hw (m := ⟨y, hTN hy⟩) hy
    refine commute_conj_of_map hψ hZ (s := t) (y := ⟨y, hTN hy⟩) haA
      (y' := aN⁻¹ * ⟨y, hTN hy⟩ * aN) rfl (commute_of_sq_eq_one hTab htT hy) ht2
      (hTab y hy) htX ?_
    apply Subtype.ext
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, htψ, heyψ, haψ]
    have hc' := hcomm₀ e₀ he₀ ey hey
    calc w * e₀ * w⁻¹ * ((w * a₀ * w⁻¹)⁻¹ * (w * ey * w⁻¹) * (w * a₀ * w⁻¹))
        = w * (e₀ * (a₀⁻¹ * ey * a₀)) * w⁻¹ := by group
      _ = w * (a₀⁻¹ * ey * a₀ * e₀) * w⁻¹ := by rw [hc']
      _ = (w * a₀ * w⁻¹)⁻¹ * (w * ey * w⁻¹) * (w * a₀ * w⁻¹) * (w * e₀ * w⁻¹) := by group
  have hcommT' : ∀ y ∈ T, (a⁻¹ * t * a) * y = y * (a⁻¹ * t * a) := by
    intro y hy
    obtain ⟨ey, hey, heyψ⟩ := mem_of_excClass hw (m := ⟨y, hTN hy⟩) hy
    have haψ' : ((ψ aN' : ↥R) : Equiv.Perm (Fin n)) = (w * a₀ * w⁻¹)⁻¹ := by
      rw [show aN' = aN⁻¹ from rfl, map_inv, Subgroup.coe_inv, haψ]
    have hc'' : (a₀ * ey * a₀⁻¹) * e₀ = e₀ * (a₀ * ey * a₀⁻¹) := by
      have hc' := hcomm₀ ey hey e₀ he₀
      calc (a₀ * ey * a₀⁻¹) * e₀ = a₀ * (ey * (a₀⁻¹ * e₀ * a₀)) * a₀⁻¹ := by group
        _ = a₀ * (a₀⁻¹ * e₀ * a₀ * ey) * a₀⁻¹ := by rw [hc']
        _ = e₀ * (a₀ * ey * a₀⁻¹) := by group
    have himg : ψ t * ψ (aN'⁻¹ * ⟨y, hTN hy⟩ * aN') =
        ψ (aN'⁻¹ * ⟨y, hTN hy⟩ * aN') * ψ t := by
      apply Subtype.ext
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, htψ, heyψ, haψ']
      calc w * e₀ * w⁻¹ * ((w * a₀ * w⁻¹)⁻¹⁻¹ * (w * ey * w⁻¹) * (w * a₀ * w⁻¹)⁻¹)
          = w * (e₀ * (a₀ * ey * a₀⁻¹)) * w⁻¹ := by group
        _ = w * ((a₀ * ey * a₀⁻¹) * e₀) * w⁻¹ := by rw [hc'']
        _ = (w * a₀ * w⁻¹)⁻¹⁻¹ * (w * ey * w⁻¹) * (w * a₀ * w⁻¹)⁻¹ * (w * e₀ * w⁻¹) := by
            group
    have h0 := commute_conj_of_map hψ hZ (s := t) (y := ⟨y, hTN hy⟩) (A.inv_mem haA)
      (y' := aN'⁻¹ * ⟨y, hTN hy⟩ * aN') (by simp [haN']) (commute_of_sq_eq_one hTab htT hy)
      ht2 (hTab y hy) htX himg
    have hy'G : ((aN'⁻¹ * ⟨y, hTN hy⟩ * aN' : normalizer (A : Set G)) : G) = a * y * a⁻¹ := by
      simp [haN']
    rw [hy'G] at h0
    calc (a⁻¹ * t * a) * y = a⁻¹ * ((t : G) * (a * y * a⁻¹)) * a := by group
      _ = a⁻¹ * (a * y * a⁻¹ * t) * a := by rw [h0]
      _ = y * (a⁻¹ * t * a) := by group
  have hcommTa : ∀ z ∈ rightConjugate T a, (t : G) * z = z * t := by
    intro z hz
    have hz' : a * z * a⁻¹ ∈ T := (mem_rightConjugate_iff T a z).mp hz
    have := hcommT _ hz'
    simpa [mul_assoc] using this
  set t' : normalizer (A : Set G) := aN⁻¹ * t * aN with ht'
  have ht'G : (t' : G) = a⁻¹ * t * a := rfl
  have ht'ψ : ((ψ t' : ↥R) : Equiv.Perm (Fin n)) = w * (a₀⁻¹ * e₀ * a₀) * w⁻¹ := by
    simp only [ht', map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, haψ, htψ]
    group
  have hct : (t : G) * t' = t' * t := by rw [ht'G]; exact hcommT _ htT
  have ht'2 : (t' : G) ^ 2 = 1 := by
    rw [ht'G, sq]
    calc a⁻¹ * (t : G) * a * (a⁻¹ * t * a) = a⁻¹ * ((t : G) ^ 2) * a := by rw [sq]; group
      _ = 1 := by rw [ht2]; group
  set u : normalizer (A : Set G) := t * t' with hu
  have huG : (u : G) = t * t' := rfl
  have hu2 : (u : G) ^ 2 = 1 := by
    rw [huG, Commute.mul_pow hct, ht2, ht'2, one_mul]
  have huA : (u : G) ∈ A := by
    have htinv : (t : G)⁻¹ = t := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact ht2)
    have h1 : (t : G) * a⁻¹ * (t : G)⁻¹ ∈ A :=
      (mem_normalizer_iff.mp t.2 a⁻¹).mp (A.inv_mem haA)
    have e1 : (u : G) = (t : G) * a⁻¹ * (t : G)⁻¹ * a := by
      rw [huG, ht'G, htinv]
      group
    rw [e1]
    exact A.mul_mem h1 haA
  have huψ : ((ψ u : ↥R) : Equiv.Perm (Fin n)) = w * tree3 x * w⁻¹ := by
    rw [hu, map_mul, Subgroup.coe_mul, htψ, ht'ψ, htree]
    group
  set bN : Fin 8 → normalizer (A : Set G) := fun i => ⟨b i, le_normalizer (hbA i)⟩ with hbN
  have hũG : ((tree3 bN : normalizer (A : Set G)) : G) = tree3 b :=
    map_tree3 (normalizer (A : Set G)).subtype bN
  have hũA : ((tree3 bN : normalizer (A : Set G)) : G) ∈ A := by
    rw [hũG]
    exact tree3_mem hbA
  have hũψ : ((ψ (tree3 bN) : ↥R) : Equiv.Perm (Fin n)) = w * tree3 x * w⁻¹ := by
    rw [map_tree3]
    change R.subtype (tree3 (ψ ∘ bN)) = _
    rw [map_tree3]
    have hfun : (R.subtype ∘ (ψ ∘ bN)) = (MulAut.conj w).toMonoidHom ∘ x := by
      funext i
      simp only [Function.comp_apply, Subgroup.subtype_apply, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply]
      exact hbψ i
    rw [hfun, ← map_tree3]
    simp [MulAut.conj_apply]
  have hk : ((tree3 bN : normalizer (A : Set G)) : G)⁻¹ * u ∈ K := by
    have h1 : ψ ((tree3 bN)⁻¹ * u) = 1 := by
      rw [map_mul, map_inv]
      have : ψ (tree3 bN) = ψ u := Subtype.ext (hũψ.trans huψ.symm)
      rw [this, inv_mul_cancel]
    simpa using (hψ.eq_one_iff _).mp h1
  obtain ⟨m, hm⟩ := exists_pow_eq hZ huA hũA hk hu2
  have hbs : ∀ i, ψ t * ψ (bN i) = ψ (bN i) * ψ t := by
    intro i
    apply Subtype.ext
    simp only [Subgroup.coe_mul, htψ]
    rw [show ((ψ (bN i) : ↥R) : Equiv.Perm (Fin n)) = w * x i * w⁻¹ from hbψ i]
    have hc' := (hx i).2 e₀ he₀
    calc w * e₀ * w⁻¹ * (w * x i * w⁻¹) = w * (e₀ * x i) * w⁻¹ := by group
      _ = w * (x i * e₀) * w⁻¹ := by rw [hc']
      _ = w * x i * w⁻¹ * (w * e₀ * w⁻¹) := by group
  have hlT : ∀ i j, (t : G) * ⁅b i, b j⁆ = ⁅b i, b j⁆ * t :=
    fun i j => commute_commutatorElement hψ (hbA i) (hbA j) (hbs i) (hbs j)
  have hnormT : ∀ {c : G}, c * t = t * c → c ∈ normalizer (rightConjugate A g : Set G) :=
    fun hc' => mem_normalizer_conj_of_commute' hA htK ht1 ht2 hc'
  have hlN : ∀ i j, ⁅b i, b j⁆ ∈ normalizer (rightConjugate A g : Set G) :=
    fun i j => hnormT (hlT i j).symm
  have hKg : rightConjugate K 1 ≠ rightConjugate K g := by
    rw [rightConjugate_one]
    intro h
    apply hg
    rw [← hA.2.2.2.1, ← rightConjugate_eq_self_iff]
    exact h.symm
  obtain ⟨w', hw'R, hw'⟩ :=
    exc_of_overlap_conj hA hψ hc hKg (by rwa [rightConjugate_one]) hRN' hRab hR4
  set φ : normalizer (rightConjugate A g : Set G) →* ↥R := ψ.comp (conjNorm A g) with hφ
  set L : Fin 8 → Fin 8 → normalizer (rightConjugate A g : Set G) :=
    fun i j => ⟨⁅b i, b j⁆, hlN i j⟩ with hL
  have hlR : ∀ i j (r₀ : normalizer (A : Set G)), (r₀ : G) ∈ rightConjugate RK g⁻¹ →
      φ (L i j) * ψ r₀ = ψ r₀ * φ (L i j) := by
    intro i j r₀ hr₀
    have hr : g⁻¹ * (r₀ : G) * g ∈ K :=
      hR.le (by simpa using (mem_rightConjugate_iff _ _ _).mp hr₀)
    change ψ (conjNorm A g (L i j)) * ψ r₀ = ψ r₀ * ψ (conjNorm A g (L i j))
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, conjNorm_apply, hL]
    have hlA : ⁅b i, b j⁆ ∈ A := commElem_mem (hbA i) (hbA j)
    have hc' : ⁅b i, b j⁆ * (g⁻¹ * r₀ * g) = (g⁻¹ * r₀ * g) * ⁅b i, b j⁆ :=
      mem_centralizer_iff.mp hr _ hlA
    calc g * ⁅b i, b j⁆ * g⁻¹ * r₀ = g * (⁅b i, b j⁆ * (g⁻¹ * r₀ * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * r₀ * g) * ⁅b i, b j⁆) * g⁻¹ := by rw [hc']
      _ = r₀ * (g * ⁅b i, b j⁆ * g⁻¹) := by group
  set Θ : normalizer (rightConjugate A g : Set G) →* Equiv.Perm (Fin n) :=
    (MulAut.conj w'⁻¹).toMonoidHom.comp (R.subtype.comp φ) with hΘ
  have hΘ' : ∀ y, Θ y = w'⁻¹ * ((φ y : ↥R) : Equiv.Perm (Fin n)) * w' := fun y => by
    simp [hΘ]
  have hΘL : ∀ i j, Θ (L i j) ∈ R ⊓ centralizer (E₀ : Set (Equiv.Perm (Fin n))) := by
    intro i j
    rw [hΘ']
    refine mem_inf.mpr ⟨R.mul_mem (R.mul_mem (R.inv_mem hw'R) (φ _).2) hw'R,
      mem_centralizer_iff.mpr fun e he => ?_⟩
    obtain ⟨r₀, hr₀, hr₀ψ⟩ := exists_of_excClass hw' he
    have h1 := congrArg Subtype.val (hlR i j r₀ hr₀)
    simp only [Subgroup.coe_mul] at h1
    rw [hr₀ψ] at h1
    calc e * (w'⁻¹ * ((φ (L i j) : ↥R) : Equiv.Perm (Fin n)) * w')
        = w'⁻¹ * ((w' * e * w'⁻¹) * ((φ (L i j) : ↥R) : Equiv.Perm (Fin n))) * w' := by group
      _ = w'⁻¹ * (((φ (L i j) : ↥R) : Equiv.Perm (Fin n)) * (w' * e * w'⁻¹)) * w' := by
          rw [h1]
      _ = w'⁻¹ * ((φ (L i j) : ↥R) : Equiv.Perm (Fin n)) * w' * e := by group
  have hMP : ∀ y z : normalizer (rightConjugate A g : Set G),
      Θ y ∈ R ⊓ centralizer (E₀ : Set (Equiv.Perm (Fin n))) →
      Θ z ∈ R ⊓ centralizer (E₀ : Set (Equiv.Perm (Fin n))) →
      Θ ⁅y, z⁆ ∈ P ⊓ centralizer (E₀ : Set (Equiv.Perm (Fin n))) := by
    intro y z hy hz
    have h1 : Θ ⁅y, z⁆ ∈ R ⊓ centralizer (E₀ : Set (Equiv.Perm (Fin n))) := by
      rw [map_commutatorElement]
      exact commElem_mem hy hz
    refine mem_inf.mpr ⟨?_, (mem_inf.mp h1).2⟩
    rw [hΘ', map_commutatorElement]
    have h2 : ((⁅φ y, φ z⁆ : ↥R) : Equiv.Perm (Fin n)) ∈ P := hcomm (φ y) (φ z)
    have := hconjP (R.inv_mem hw'R) h2
    rwa [inv_inv] at this
  set U' : normalizer (rightConjugate A g : Set G) :=
    ⁅⁅L 0 1, L 2 3⁆, ⁅L 4 5, L 6 7⁆⁆ with hU'
  have hΘU : Θ U' ∈ ⁅P ⊓ centralizer (E₀ : Set (Equiv.Perm (Fin n))),
      P ⊓ centralizer (E₀ : Set (Equiv.Perm (Fin n)))⁆ := by
    rw [hU', map_commutatorElement]
    exact commutator_mem_commutator (hMP _ _ (hΘL 0 1) (hΘL 2 3)) (hMP _ _ (hΘL 4 5) (hΘL 6 7))
  have htN : (t : G) ∈ normalizer (rightConjugate A g : Set G) := hnormT rfl
  have ht'N : (t' : G) ∈ normalizer (rightConjugate A g : Set G) := hnormT hct.symm
  set tG : normalizer (rightConjugate A g : Set G) := ⟨t, htN⟩ with htG
  set t'G : normalizer (rightConjugate A g : Set G) := ⟨t', ht'N⟩ with ht'G'
  have hUG : ((U' : normalizer (rightConjugate A g : Set G)) : G) =
      ((tree3 bN : normalizer (A : Set G)) : G) := by
    rw [hũG]
    rfl
  have huU : tG * t'G = U' ^ m := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, hUG, hm]
    rfl
  have hφt : φ tG = 1 := by
    rw [hφ, MonoidHom.comp_apply, hψ.eq_one_iff]
    exact (mem_rightConjugate_iff _ g _).mp htK
  have hφu : φ (U' ^ m) = φ t'G := by rw [← huU, map_mul, hφt, one_mul]
  have ht'c : ∀ y ∈ T, (t' : G) * y * (t' : G)⁻¹ = y := by
    intro y hy
    rw [ht'G, hcommT' y hy, mul_inv_cancel_right]
  have hne : rightConjugate K (g * a) ≠ rightConjugate K g := by
    intro heq
    have ht'K : (t' : G) ∈ rightConjugate K g := by
      rw [← heq, ← rightConjugate_mul]
      have h1 : (t' : G) ∈ rightConjugate T a := by
        rw [mem_rightConjugate_iff, ht'G]
        simpa [mul_assoc] using htT
      exact Subgroup.map_mono hT.le h1
    have ht'n : (t' : G) ∈ normalizer (T : Set G) := by
      rw [mem_normalizer_iff]
      intro z
      constructor
      · intro hz
        rw [ht'c z hz]
        exact hz
      · intro hz
        have e1 : z = (t' : G)⁻¹ * ((t' : G) * z * (t' : G)⁻¹) * t' := by group
        have e2 : (t' : G)⁻¹ * ((t' : G) * z * (t' : G)⁻¹) * t' = (t' : G) * z * (t' : G)⁻¹ := by
          have h3 := ht'c _ hz
          calc (t' : G)⁻¹ * ((t' : G) * z * (t' : G)⁻¹) * t'
              = (t' : G)⁻¹ * ((t' : G) * ((t' : G) * z * (t' : G)⁻¹) * (t' : G)⁻¹) * t' := by
                rw [h3]
            _ = (t' : G) * z * (t' : G)⁻¹ := by group
        rw [e1, e2]
        exact hz
    have hz2 : IsPGroup 2 (zpowers (t' : G)) :=
      IsPGroup.of_card (n := 1) (by
        rw [Nat.card_zpowers, pow_one]
        refine orderOf_eq_prime ht'2 fun h1 => ht1 ?_
        have e2 : (t : G) = a * t' * a⁻¹ := by rw [ht'G]; group
        rw [e2, h1, mul_one, mul_inv_cancel])
    have hV : IsPGroup 2 (zpowers (t' : G) ⊔ T : Subgroup G) :=
      IsPGroup.to_sup_of_normal_right' hz2 hT.isPGroup (zpowers_le.mpr ht'n)
    have hVT := hT.eq_of_le le_sup_right (sup_le (zpowers_le.mpr ht'K) hT.le) hV
    have ht'T : (t' : G) ∈ T := by
      rw [← hVT]
      exact mem_sup_left (mem_zpowers _)
    obtain ⟨e', he', he'ψ⟩ := mem_of_excClass hw ht'T
    apply hnot₀
    have h1 := ht'ψ.symm.trans he'ψ
    have : a₀⁻¹ * e₀ * a₀ = e' := by
      have := congrArg (fun y => w⁻¹ * y * w) h1
      simpa [mul_assoc] using this
    rw [this]
    exact he'
  have hgag : g * a * g⁻¹ ∉ normalizer (A : Set G) := by
    intro h
    rw [← hA.2.2.2.1, ← rightConjugate_eq_self_iff] at h
    apply hne
    rw [show g * a = g * a * g⁻¹ * g by group, ← rightConjugate_mul, h]
  have hTa : IsSylowOf 2 (rightConjugate T a) (rightConjugate K (g * a)) := by
    rw [← rightConjugate_mul]
    exact isSylowOf_conj hT a
  have hTaN : rightConjugate T a ≤ normalizer (rightConjugate A g : Set G) :=
    fun z hz => hnormT (hcommTa z hz).symm
  have hTaab : ∀ z ∈ rightConjugate T a, z ^ 2 = 1 := by
    intro z hz
    have h1 := hTab _ ((mem_rightConjugate_iff T a z).mp hz)
    have h2 : (a * z * a⁻¹) ^ 2 = a * z ^ 2 * a⁻¹ := conj_pow
    rw [h2] at h1
    have := congrArg (fun y => a⁻¹ * y * a) h1
    simpa [mul_assoc] using this
  obtain ⟨w₁, hw₁R, hw₁⟩ := exc_of_overlap_conj hA hψ hc hne hTa hTaN hTaab
    (by rw [rightConjugate_card]; exact hT4)
  have hmem₁ : ((conjNorm A g t'G : normalizer (A : Set G)) : G) ∈
      rightConjugate (rightConjugate T a) g⁻¹ := by
    rw [mem_rightConjugate_iff, mem_rightConjugate_iff, conjNorm_apply]
    have e1 : a * (g⁻¹ * (g * ((t'G : normalizer (rightConjugate A g : Set G)) : G) * g⁻¹) *
        g⁻¹⁻¹) * a⁻¹ = t := by
      rw [ht'G']
      change a * (g⁻¹ * (g * (t' : G) * g⁻¹) * g⁻¹⁻¹) * a⁻¹ = t
      rw [ht'G]
      group
    rw [e1]
    exact htT
  obtain ⟨e₁, he₁, he₁ψ⟩ := mem_of_excClass hw₁ hmem₁
  have hφt'1 : φ t'G ≠ 1 := by
    intro h1
    have hK1 : ((conjNorm A g t'G : normalizer (A : Set G)) : G) ∈ K :=
      (hψ.eq_one_iff _).mp h1
    have hzy : ((conjNorm A g t'G : normalizer (A : Set G)) : G) ∈
        rightConjugate K (g * a * g⁻¹) := by
      rw [mem_rightConjugate_iff, conjNorm_apply]
      have e1 : g * a * g⁻¹ * (g * ((t'G : normalizer (rightConjugate A g : Set G)) : G) *
          g⁻¹) * (g * a * g⁻¹)⁻¹ = g * t * g⁻¹ := by
        rw [ht'G']
        change g * a * g⁻¹ * (g * (t' : G) * g⁻¹) * (g * a * g⁻¹)⁻¹ = g * t * g⁻¹
        rw [ht'G]
        group
      rw [e1]
      exact (mem_rightConjugate_iff _ g _).mp htK
    have hz2 : ((conjNorm A g t'G : normalizer (A : Set G)) : G) ^ 2 = 1 := by
      rw [conjNorm_apply, conj_pow]
      change g * (t' : G) ^ 2 * g⁻¹ = 1
      rw [ht'2, mul_one, mul_inv_cancel]
    have h1' := eq_one_of_mem_inf' hA hgag hK1 hzy hz2
    rw [conjNorm_apply] at h1'
    apply ht1
    have h2 : (t' : G) = 1 := by
      have h3 : g⁻¹ * (g * (t' : G) * g⁻¹) * g = g⁻¹ * 1 * g :=
        congrArg (fun z => g⁻¹ * z * g) h1'
      rwa [show g⁻¹ * (g * (t' : G) * g⁻¹) * g = (t' : G) by group,
        show g⁻¹ * 1 * g = (1 : G) by group] at h3
    have e2 : (t : G) = a * t' * a⁻¹ := by rw [ht'G]; group
    rw [e2, h2, mul_one, mul_inv_cancel]
  have hQ1 : Q ((φ t'G : ↥R) : Equiv.Perm (Fin n)) := by
    change Q ((ψ (conjNorm A g t'G) : ↥R) : Equiv.Perm (Fin n))
    rw [he₁ψ]
    refine hQc w₁ hw₁R _ (hQE e₁ he₁ fun h1 => hφt'1 (Subtype.ext ?_))
    change ((ψ (conjNorm A g t'G) : ↥R) : Equiv.Perm (Fin n)) = 1
    rw [he₁ψ, h1, mul_one, mul_inv_cancel]
  have hΘu : Θ (U' ^ m) ∈ ⁅P ⊓ centralizer (E₀ : Set (Equiv.Perm (Fin n))),
      P ⊓ centralizer (E₀ : Set (Equiv.Perm (Fin n)))⁆ := by
    rw [map_pow]
    exact pow_mem hΘU m
  have hΘu2 : Θ (U' ^ m) ^ 2 = 1 := by
    rw [← map_pow, ← huU]
    have h1 : (tG * t'G) ^ 2 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, OneMemClass.coe_one]
      exact hu2
    rw [h1, map_one]
  have hΘu1 : Θ (U' ^ m) ≠ 1 := by
    rw [hΘ', hφu]
    intro h1
    apply hφt'1
    apply Subtype.ext
    have := congrArg (fun z => w' * z * w'⁻¹) h1
    simpa [mul_assoc] using this
  apply hnotQ _ hΘu hΘu2 hΘu1
  rw [hΘ', hφu]
  have e3 : w'⁻¹ * ((φ t'G : ↥R) : Equiv.Perm (Fin n)) * w' =
      w'⁻¹ * ((φ t'G : ↥R) : Equiv.Perm (Fin n)) * w'⁻¹⁻¹ := by rw [inv_inv]
  rw [e3]
  exact hQc _ (R.inv_mem hw'R) _ hQ1

end CFSG.ComponentClassification.RankTwoSporadic.Endgame
