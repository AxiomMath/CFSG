module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.X.ConjugationFamily

public section

namespace CFSG.RankTwoShapes

open scoped Pointwise

variable {G : Type*} [Group G]

@[expose] def IsAlperinSubgroup (p : ℕ) (S Q : Subgroup G) : Prop :=
  Q ≤ S ∧
  Nat.Coprime p ((S ⊓ (Subgroup.normalizer (Q : Set G))).subgroupOf (Subgroup.normalizer (Q : Set G))).index ∧
  Subgroup.centralizer (Q : Set G) ⊓ S ≤ Q ∧
  ∀ R : Subgroup G, Q ⊔ Subgroup.centralizer (Q : Set G) ≤ R → R ≤ (Subgroup.normalizer (Q : Set G)) →
    (Subgroup.normalizer (Q : Set G)) ≤ (Subgroup.normalizer (R : Set G)) →
    (∃ k : ℕ, ((Q ⊔ Subgroup.centralizer (Q : Set G)).subgroupOf R).index = p ^ k) →
    R = Q ⊔ Subgroup.centralizer (Q : Set G)

inductive AlperinDecomposition (p : ℕ) (S P : Subgroup G) : G → Prop
  | one : AlperinDecomposition p S P 1
  | step {c n : G} {Q : Subgroup G} : AlperinDecomposition p S P c → IsAlperinSubgroup p S Q →
      P.map (MulAut.conj c⁻¹).toMonoidHom ≤ Q → n ∈ (Subgroup.normalizer (Q : Set G)) →
      AlperinDecomposition p S P (c * n)

private theorem mem_map_conj_inv_iff {H : Subgroup G} {g y : G} :
    y ∈ H.map (MulAut.conj g⁻¹).toMonoidHom ↔ g * y * g⁻¹ ∈ H := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [mul_assoc] using hx
  · intro hy
    exact ⟨g * y * g⁻¹, hy, by simp [mul_assoc]⟩

private theorem conj_mem_map_conj_inv {H : Subgroup G} {x : G} (g : G) (hx : x ∈ H) :
    g⁻¹ * x * g ∈ H.map (MulAut.conj g⁻¹).toMonoidHom :=
  mem_map_conj_inv_iff.mpr (by simpa [mul_assoc] using hx)

private theorem map_conj_inv_eq_of_pointwise {P : Subgroup G} {a b : G}
    (hab : ∀ x ∈ P, a⁻¹ * x * a = b⁻¹ * x * b) :
    P.map (MulAut.conj a⁻¹).toMonoidHom = P.map (MulAut.conj b⁻¹).toMonoidHom := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, by simpa using (hab x hx).symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, by simpa using hab x hx⟩

namespace AlperinDecomposition

variable {p : ℕ} {S : Subgroup G}

theorem map_le {P : Subgroup G} {c : G} (h : AlperinDecomposition p S P c) (hP : P ≤ S) :
    P.map (MulAut.conj c⁻¹).toMonoidHom ≤ S := by
  induction h with
  | one =>
      intro y hy
      exact hP (by simpa using mem_map_conj_inv_iff.mp hy)
  | @step c n Q _ hQ hPQ hn _ =>
      intro y hy
      rw [mem_map_conj_inv_iff] at hy
      have hny : n * y * n⁻¹ ∈ Q :=
        hPQ (mem_map_conj_inv_iff.mpr (by simpa [mul_assoc] using hy))
      exact hQ.1 ((Subgroup.mem_normalizer_iff.mp hn y).mpr hny)

theorem mono {A B : Subgroup G} {c : G} (h : AlperinDecomposition p S A c) (hBA : B ≤ A) :
    AlperinDecomposition p S B c := by
  induction h with
  | one => exact .one
  | step _ hQ hAQ hn ih => exact .step ih hQ ((Subgroup.map_mono hBA).trans hAQ) hn

theorem trans {A : Subgroup G} {c d : G} (hc : AlperinDecomposition p S A c)
    (hd : AlperinDecomposition p S (A.map (MulAut.conj c⁻¹).toMonoidHom) d) :
    AlperinDecomposition p S A (c * d) := by
  induction hd with
  | one => simpa using hc
  | @step d n Q _ hQ hAQ hn ih =>
      have hle : A.map (MulAut.conj (c * d)⁻¹).toMonoidHom ≤ Q := by
        intro y hy
        apply hAQ
        rw [mem_map_conj_inv_iff, mem_map_conj_inv_iff]
        rw [mem_map_conj_inv_iff] at hy
        simpa [mul_assoc] using hy
      simpa [mul_assoc] using AlperinDecomposition.step ih hQ hle hn

theorem exists_moving_step {P : Subgroup G} {c x : G} (h : AlperinDecomposition p S P c)
    (hx : x ∈ P) (hcx : c⁻¹ * x * c ≠ x) :
    ∃ Q : Subgroup G, IsAlperinSubgroup p S Q ∧ x ∈ Q ∧
      ∃ n ∈ (Subgroup.normalizer (Q : Set G)), n⁻¹ * x * n ≠ x := by
  induction h with
  | one => exact absurd (by group) hcx
  | @step c n Q _ hQ hPQ hn ih =>
      by_cases hcx' : c⁻¹ * x * c = x
      · refine ⟨Q, hQ, ?_, n, hn, ?_⟩
        · have hmem := conj_mem_map_conj_inv c hx
          rw [hcx'] at hmem
          exact hPQ hmem
        · intro hnx
          apply hcx
          calc (c * n)⁻¹ * x * (c * n) = n⁻¹ * (c⁻¹ * x * c) * n := by group
            _ = x := by rw [hcx', hnx]
      · exact ih hcx'

end AlperinDecomposition

theorem isAlperinSubgroup_sylow [Finite G] {p : ℕ} [Fact p.Prime] (S : Sylow p G) :
    IsAlperinSubgroup p (S : Subgroup G) S := by
  have hSidx : Nat.Coprime p (S : Subgroup G).index :=
    (Nat.Prime.coprime_iff_not_dvd Fact.out).2 S.not_dvd_index
  refine ⟨le_rfl, ?_, inf_le_right, ?_⟩
  · rw [inf_eq_left.mpr Subgroup.le_normalizer]
    exact hSidx.coprime_dvd_right (Subgroup.relIndex_dvd_index_of_le Subgroup.le_normalizer)
  · rintro R hSR - - ⟨k, hk⟩
    have hdvd : ((S : Subgroup G) ⊔ Subgroup.centralizer ((S : Subgroup G) : Set G)).relIndex R ∣
        (S : Subgroup G).index :=
      (Subgroup.relIndex_dvd_of_le_left R le_sup_left).trans
        (Subgroup.relIndex_dvd_index_of_le (le_sup_left.trans hSR))
    have hone : ((S : Subgroup G) ⊔ Subgroup.centralizer ((S : Subgroup G) : Set G)).relIndex R
        = 1 :=
      Nat.Coprime.eq_one_of_dvd
        (Nat.Coprime.pow_left k (hSidx.coprime_dvd_right hdvd)).symm (hk ▸ dvd_rfl)
    exact le_antisymm (Subgroup.relIndex_eq_one.mp hone) hSR

private def Factored (p : ℕ) (S A : Subgroup G) (g : G) : Prop :=
  ∃ c : G, AlperinDecomposition p S A c ∧ ∀ x ∈ A, c⁻¹ * x * c = g⁻¹ * x * g

private theorem Factored.one {p : ℕ} {S A : Subgroup G} : Factored p S A 1 :=
  ⟨1, .one, fun _ _ => rfl⟩

private theorem Factored.mono {p : ℕ} {S A B : Subgroup G} {g : G} (h : Factored p S A g)
    (hBA : B ≤ A) : Factored p S B g := by
  obtain ⟨c, hc, hcg⟩ := h
  exact ⟨c, hc.mono hBA, fun x hx => hcg x (hBA hx)⟩

private theorem Factored.congr {p : ℕ} {S A : Subgroup G} {g g' : G} (h : Factored p S A g)
    (hgg' : ∀ x ∈ A, g⁻¹ * x * g = g'⁻¹ * x * g') : Factored p S A g' := by
  obtain ⟨c, hc, hcg⟩ := h
  exact ⟨c, hc, fun x hx => (hcg x hx).trans (hgg' x hx)⟩

private theorem Factored.trans {p : ℕ} {S A : Subgroup G} {g h : G} (hg : Factored p S A g)
    (hh : Factored p S (A.map (MulAut.conj g⁻¹).toMonoidHom) h) : Factored p S A (g * h) := by
  obtain ⟨c, hc, hcg⟩ := hg
  obtain ⟨d, hd, hdh⟩ := hh
  rw [← map_conj_inv_eq_of_pointwise hcg] at hd hdh
  refine ⟨c * d, hc.trans hd, fun x hx => ?_⟩
  calc (c * d)⁻¹ * x * (c * d) = d⁻¹ * (c⁻¹ * x * c) * d := by group
    _ = h⁻¹ * (c⁻¹ * x * c) * h := hdh _ (conj_mem_map_conj_inv c hx)
    _ = h⁻¹ * (g⁻¹ * x * g) * h := by rw [hcg x hx]
    _ = (g * h)⁻¹ * x * (g * h) := by group

private theorem Factored.of_isAlperinSubgroup {p : ℕ} {S Q A : Subgroup G} {n : G}
    (hQ : IsAlperinSubgroup p S Q) (hAQ : A ≤ Q) (hn : n ∈ (Subgroup.normalizer (Q : Set G))) :
    Factored p S A n :=
  ⟨1 * n, .step .one hQ (fun y hy => hAQ (by simpa using mem_map_conj_inv_iff.mp hy)) hn,
    fun x _ => by rw [one_mul]⟩

private theorem normalizer_le_normalizer_centralizer (U : Subgroup G) :
    (Subgroup.normalizer (U : Set G)) ≤ Subgroup.normalizer ((Subgroup.centralizer (U : Set G) : Subgroup G) : Set G) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro c
  simp only [Subgroup.mem_centralizer_iff]
  constructor
  · intro hc u hu
    have hcomm := hc _ ((Subgroup.mem_normalizer_iff''.mp hn u).mp hu)
    calc u * (n * c * n⁻¹) = n * ((n⁻¹ * u * n) * c) * n⁻¹ := by group
      _ = n * (c * (n⁻¹ * u * n)) * n⁻¹ := by rw [hcomm]
      _ = n * c * n⁻¹ * u := by group
  · intro hc u hu
    have hcomm := hc _ ((Subgroup.mem_normalizer_iff.mp hn u).mp hu)
    calc u * c = n⁻¹ * ((n * u * n⁻¹) * (n * c * n⁻¹)) * n := by group
      _ = n⁻¹ * ((n * c * n⁻¹) * (n * u * n⁻¹)) * n := by rw [hcomm]
      _ = c * u := by group

private theorem relIndex_dvd_relIndex_of_le_normalizer [Finite G] {T R N : Subgroup G}
    (hTN : T ≤ N) (hRN : R ≤ N) (hNR : N ≤ (Subgroup.normalizer (R : Set G))) :
    T.relIndex R ∣ T.relIndex N := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer (hTN.trans hNR)
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer (hTN.trans hNR)
  have hsecond : R.relIndex T = R.relIndex (T ⊔ R) :=
    Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient T R
      (hTN.trans hNR)).toEquiv
  have e1 := Subgroup.relIndex_mul_relIndex (R ⊓ T) T N inf_le_right hTN
  have e2 := Subgroup.relIndex_mul_relIndex (R ⊓ T) R N inf_le_left hRN
  have e3 := Subgroup.relIndex_mul_relIndex R (T ⊔ R) N le_sup_right (sup_le hTN hRN)
  rw [Subgroup.inf_relIndex_right] at e1
  rw [Subgroup.inf_relIndex_left] at e2
  have hne : R.relIndex T ≠ 0 := Subgroup.index_ne_zero_of_finite
  refine ⟨(T ⊔ R).relIndex N, Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne) ?_⟩
  rw [e1, ← e2, ← e3, hsecond]
  ring

private theorem coprime_index_of_huppertExtremal [Finite G] {p : ℕ} [Fact p.Prime]
    {S : Sylow p G} {U : Subgroup G} (hU : BenderSuzuki.External.HuppertExtremal S U) :
    Nat.Coprime p (((S : Subgroup G) ⊓ (Subgroup.normalizer (U : Set G))).subgroupOf (Subgroup.normalizer (U : Set G))).index := by
  have hmul := Subgroup.relIndex_mul_card (H := (S : Subgroup G) ⊓ (Subgroup.normalizer (U : Set G)))
    (K := (Subgroup.normalizer (U : Set G)))
  rw [inf_of_le_left inf_le_right] at hmul
  have hi0 : ((S : Subgroup G) ⊓ (Subgroup.normalizer (U : Set G))).relIndex (Subgroup.normalizer (U : Set G)) ≠ 0 :=
    Subgroup.index_ne_zero_of_finite
  have hfac := congrArg (fun n => n.factorization p) hmul
  simp only [Nat.factorization_mul hi0 Nat.card_pos.ne', Finsupp.add_apply] at hfac
  have hext := hU.2
  rw [Nat.Prime.coprime_iff_not_dvd Fact.out]
  intro hdvd
  have hle := (Nat.Prime.dvd_iff_one_le_factorization Fact.out hi0).1 hdvd
  change 1 ≤ (((S : Subgroup G) ⊓ (Subgroup.normalizer (U : Set G))).relIndex (Subgroup.normalizer (U : Set G))).factorization p at hle
  omega

private theorem exists_mem_conj_mem_of_coprime_relIndex [Finite G] {p : ℕ} [Fact p.Prime]
    {R A B : Subgroup G} (hAp : IsPGroup p A) (hA : Nat.Coprime p (A.relIndex R))
    (hBR : B ≤ R) (hBp : IsPGroup p B) :
    ∃ r ∈ R, ∀ y ∈ B, r⁻¹ * y * r ∈ A := by
  let SA : Sylow p R := (hAp.comap_subtype (K := R)).toSylow
    ((Nat.Prime.coprime_iff_not_dvd Fact.out).1 hA)
  obtain ⟨X, hX⟩ := (hBp.comap_subtype (K := R)).exists_le_sylow
  obtain ⟨r, hr⟩ := MulAction.exists_smul_eq R X SA
  refine ⟨((r⁻¹ : R) : G), (r⁻¹ : R).2, fun y hy => ?_⟩
  have hmem : MulAut.conj r • (⟨y, hBR hy⟩ : R) ∈ ((r • X : Sylow p R) : Subgroup R) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _
      (hX (show (⟨y, hBR hy⟩ : R) ∈ B.comap R.subtype from hy))
  rw [hr] at hmem
  have hA' : ((MulAut.conj r • (⟨y, hBR hy⟩ : R) : R) : G) ∈ A := hmem
  simpa [MulAut.smul_def, MulAut.conj_apply] using hA'

private theorem exists_extension_of_not_radical [Finite G] {p : ℕ} [Fact p.Prime]
    {S U R : Subgroup G} (hSp : IsPGroup p S) (hUS : U ≤ S)
    (hcop : Nat.Coprime p ((S ⊓ (Subgroup.normalizer (U : Set G))).subgroupOf (Subgroup.normalizer (U : Set G))).index)
    (hUCR : U ⊔ Subgroup.centralizer (U : Set G) ≤ R) (hRN : R ≤ (Subgroup.normalizer (U : Set G)))
    (hNR : (Subgroup.normalizer (U : Set G)) ≤ (Subgroup.normalizer (R : Set G)))
    (hk : ∃ k : ℕ, ((U ⊔ Subgroup.centralizer (U : Set G)).subgroupOf R).index = p ^ k)
    (hne : R ≠ U ⊔ Subgroup.centralizer (U : Set G)) :
    ∃ D : Subgroup G, U < D ∧ D ≤ S ∧ ∀ h ∈ (Subgroup.normalizer (U : Set G)), ∃ h' : G,
      D.map (MulAut.conj h'⁻¹).toMonoidHom ≤ S ∧ ∀ x ∈ U, h'⁻¹ * x * h' = h⁻¹ * x * h := by
  obtain ⟨k, hk⟩ := hk
  have hUD : U ≤ S ⊓ R := le_inf hUS (le_sup_left.trans hUCR)
  have hDp : IsPGroup p (S ⊓ R : Subgroup G) := hSp.to_le inf_le_left
  have hDcop : Nat.Coprime p ((S ⊓ R).relIndex R) := by
    have hdvd := relIndex_dvd_relIndex_of_le_normalizer
      (T := S ⊓ (Subgroup.normalizer (U : Set G))) inf_le_right hRN hNR
    have heq : (S ⊓ (Subgroup.normalizer (U : Set G))).relIndex R = (S ⊓ R).relIndex R := by
      rw [← Subgroup.inf_relIndex_right (S ⊓ (Subgroup.normalizer (U : Set G))) R,
        ← Subgroup.inf_relIndex_right (S ⊓ R) R, inf_assoc, inf_assoc,
        inf_of_le_right hRN, inf_idem]
    rw [← heq]
    exact hcop.coprime_dvd_right hdvd
  have hRCD : R ≤ Subgroup.centralizer (U : Set G) ⊔ (S ⊓ R) := by
    have h1 : (Subgroup.centralizer (U : Set G) ⊔ (S ⊓ R)).relIndex R ∣ (S ⊓ R).relIndex R :=
      Subgroup.relIndex_dvd_of_le_left R le_sup_right
    have h2 : (Subgroup.centralizer (U : Set G) ⊔ (S ⊓ R)).relIndex R ∣ p ^ k := by
      rw [← hk]
      exact Subgroup.relIndex_dvd_of_le_left R (sup_le (hUD.trans le_sup_right) le_sup_left)
    exact Subgroup.relIndex_eq_one.mp
      (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_left k (hDcop.coprime_dvd_right h1)).symm h2)
  refine ⟨S ⊓ R, lt_of_le_of_ne hUD ?_, inf_le_left, ?_⟩
  · intro hUeq
    apply hne
    refine le_antisymm ?_ hUCR
    rw [← hUeq] at hRCD
    exact hRCD.trans (sup_comm _ _).le
  · intro h hh
    have hhR : h ∈ (Subgroup.normalizer (R : Set G)) := hNR hh
    have hDhR : (S ⊓ R).map (MulAut.conj h⁻¹).toMonoidHom ≤ R := by
      intro y hy
      rw [mem_map_conj_inv_iff] at hy
      simpa [mul_assoc] using (Subgroup.mem_normalizer_iff''.mp hhR _).mp hy.2
    obtain ⟨r, hrR, hr⟩ :=
      exists_mem_conj_mem_of_coprime_relIndex hDp hDcop hDhR (hDp.map _)
    have hDnC : S ⊓ R ≤ Subgroup.normalizer ((Subgroup.centralizer (U : Set G) : Subgroup G) : Set G) :=
      inf_le_right.trans (hRN.trans (normalizer_le_normalizer_centralizer U))
    obtain ⟨c, hc, d, hd, rfl⟩ :
        r ∈ (Subgroup.centralizer (U : Set G) : Set G) * ((S ⊓ R : Subgroup G) : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ hDnC]
      exact hRCD hrR
    refine ⟨h * c, ?_, ?_⟩
    · intro y hy
      rw [mem_map_conj_inv_iff] at hy
      have h1 := hr _ (conj_mem_map_conj_inv h hy)
      have h2 : d * ((c * d)⁻¹ * (h⁻¹ * (h * c * y * (h * c)⁻¹) * h) * (c * d)) * d⁻¹ ∈
          S ⊓ R :=
        (S ⊓ R).mul_mem ((S ⊓ R).mul_mem hd h1) ((S ⊓ R).inv_mem hd)
      have h3 : d * ((c * d)⁻¹ * (h⁻¹ * (h * c * y * (h * c)⁻¹) * h) * (c * d)) * d⁻¹ = y := by
        group
      rw [h3] at h2
      exact h2.1
    · intro x hx
      have hcomm : (h⁻¹ * x * h) * c = c * (h⁻¹ * x * h) :=
        Subgroup.mem_centralizer_iff.mp hc _ ((Subgroup.mem_normalizer_iff''.mp hh x).mp hx)
      calc (h * c)⁻¹ * x * (h * c) = c⁻¹ * ((h⁻¹ * x * h) * c) := by group
        _ = h⁻¹ * x * h := by rw [hcomm]; group

private theorem factored_of_huppert [Finite G] {p : ℕ} [Fact p.Prime] (S : Sylow p G)
    {A : Subgroup G}
    (hlarger : ∀ B : Subgroup G, Nat.card A < Nat.card B → B ≤ S → ∀ z : G,
      B.map (MulAut.conj z⁻¹).toMonoidHom ≤ S → Factored p S B z)
    {g : G} (hdec : BenderSuzuki.External.HuppertCentricConjugationDecomposition
      (S : Subgroup G) (BenderSuzuki.External.HuppertExtremal S) A g) :
    Factored p S A g := by
  induction hdec with
  | one => exact Factored.one
  | @tail g₀ h U _ hUext hUS hcur hh hcent ih =>
      have hcur' : A.map (MulAut.conj g₀⁻¹).toMonoidHom ≤ U := hcur
      refine ih.trans (Factored.mono ?_ hcur')
      rcases hcent with hcent | hcent
      · by_cases hrad : ∀ R : Subgroup G, U ⊔ Subgroup.centralizer (U : Set G) ≤ R →
            R ≤ (Subgroup.normalizer (U : Set G)) → (Subgroup.normalizer (U : Set G)) ≤ (Subgroup.normalizer (R : Set G)) →
            (∃ k : ℕ, ((U ⊔ Subgroup.centralizer (U : Set G)).subgroupOf R).index = p ^ k) →
            R = U ⊔ Subgroup.centralizer (U : Set G)
        · exact Factored.of_isAlperinSubgroup
            ⟨hUS, coprime_index_of_huppertExtremal hUext, (inf_comm _ _).trans_le hcent, hrad⟩
            le_rfl hh
        · push Not at hrad
          obtain ⟨R, hUCR, hRN, hNR, hk, hne⟩ := hrad
          obtain ⟨D, hUD, hDS, hext⟩ := exists_extension_of_not_radical S.isPGroup' hUS
            (coprime_index_of_huppertExtremal hUext) hUCR hRN hNR hk hne
          obtain ⟨h', hh'S, hh'⟩ := hext h hh
          have hcard : Nat.card A < Nat.card D :=
            calc Nat.card A = Nat.card (A.map (MulAut.conj g₀⁻¹).toMonoidHom) :=
                  (Subgroup.card_map_of_injective (MulAut.conj g₀⁻¹).injective).symm
              _ ≤ Nat.card U := Subgroup.card_le_of_le hcur'
              _ < Nat.card D := Subgroup.card_lt_of_lt hUD
          exact ((hlarger D hcard hDS h' hh'S).mono hUD.le).congr hh'
      · refine Factored.one.congr fun x hx => ?_
        have hxh : x * h = h * x := Subgroup.mem_centralizer_iff.mp hcent x hx
        calc (1 : G)⁻¹ * x * 1 = h⁻¹ * (h * x) := by group
          _ = h⁻¹ * x * h := by rw [← hxh]; group

private theorem factored_of_le [Finite G] {p : ℕ} [Fact p.Prime] (S : Sylow p G) (n : ℕ) :
    ∀ A : Subgroup G, A ≤ S → Nat.card S - Nat.card A = n →
      ∀ g : G, A.map (MulAut.conj g⁻¹).toMonoidHom ≤ S → Factored p S A g := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro A hAS hn g hg
    refine factored_of_huppert S (fun B hAB hBS z hz => ?_)
      (BenderSuzuki.External.HuppertExtremal.centric_conjugation_decomposition S hAS hg)
    have hBS' := Subgroup.card_le_of_le hBS
    exact ih _ (by omega) B hBS rfl z hz

theorem alperin_centric_radical_fusion [Finite G] {p : ℕ} [Fact p.Prime] (S : Sylow p G)
    {P : Subgroup G} (hP : P ≤ S) {g : G} (hg : P.map (MulAut.conj g⁻¹).toMonoidHom ≤ S) :
    ∃ c : G, AlperinDecomposition p (S : Subgroup G) P c ∧ ∀ x ∈ P, c⁻¹ * x * c = g⁻¹ * x * g :=
  factored_of_le S _ P hP rfl g hg

theorem exists_alperinSubgroup_moving [Finite G] {p : ℕ} [Fact p.Prime] (S : Sylow p G)
    {x g : G} (hx : x ∈ (S : Subgroup G)) (hg : g⁻¹ * x * g ∈ (S : Subgroup G))
    (hmove : g⁻¹ * x * g ≠ x) :
    ∃ Q : Subgroup G, IsAlperinSubgroup p (S : Subgroup G) Q ∧ x ∈ Q ∧
      ∃ n ∈ (Subgroup.normalizer (Q : Set G)), n⁻¹ * x * n ≠ x := by
  have hP : Subgroup.zpowers x ≤ (S : Subgroup G) := Subgroup.zpowers_le.2 hx
  have hPg : (Subgroup.zpowers x).map (MulAut.conj g⁻¹).toMonoidHom ≤ (S : Subgroup G) := by
    rw [MonoidHom.map_zpowers]
    exact Subgroup.zpowers_le.2 (by simpa using hg)
  obtain ⟨c, hc, hcg⟩ := alperin_centric_radical_fusion S hP hPg
  have hcx : c⁻¹ * x * c ≠ x := by
    rw [hcg x (Subgroup.mem_zpowers x)]
    exact hmove
  exact hc.exists_moving_step (Subgroup.mem_zpowers x) hcx

end CFSG.RankTwoShapes
