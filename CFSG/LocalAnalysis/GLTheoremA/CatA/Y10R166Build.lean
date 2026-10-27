module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Glue

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

theorem inf_centralizer_eq_zpowers_of_le_sup {K : Type} [Group K] {B J S : Subgroup K} {x : K}
    (hJx : J ≤ Subgroup.centralizer ({x} : Set K)) (hBJ : B ≤ J ⊔ Subgroup.zpowers x) (hx : x ∈ B)
    (hSJ : S ≤ J) (hBJS : B ⊓ J ⊓ Subgroup.centralizer (S : Set K) ≤ Subgroup.zpowers x) :
    B ⊓ Subgroup.centralizer (S : Set K) = Subgroup.zpowers x := by
  have hxJ : ∀ j ∈ J, j * x = x * j := fun j hj =>
    Subgroup.mem_centralizer_singleton_iff.1 (hJx hj)
  have hxS : x ∈ Subgroup.centralizer (S : Set K) :=
    Subgroup.mem_centralizer_iff.2 fun s hs =>
      Subgroup.mem_centralizer_singleton_iff.1 (hJx (hSJ hs))
  refine le_antisymm ?_ (Subgroup.zpowers_le.2 ⟨hx, hxS⟩)
  rintro b ⟨hbB, hbS⟩
  obtain ⟨j, hjJ, k, rfl⟩ := exists_mul_zpow_eq_of_mem_sup_zpowers hxJ (hBJ hbB)
  have hxB : x ^ k ∈ B := Subgroup.zpow_mem B hx k
  have hjB : j ∈ B := by
    have h := Subgroup.mul_mem B hbB (Subgroup.inv_mem B hxB)
    rwa [show j * x ^ k * (x ^ k)⁻¹ = j by group] at h
  have hjS : j ∈ Subgroup.centralizer (S : Set K) := by
    have h2 : x ^ k ∈ Subgroup.centralizer (S : Set K) := Subgroup.zpow_mem _ hxS k
    have h := Subgroup.mul_mem _ hbS (Subgroup.inv_mem _ h2)
    rwa [show j * x ^ k * (x ^ k)⁻¹ = j by group] at h
  refine Subgroup.mul_mem _ (hBJS ⟨⟨hjB, hjJ⟩, hjS⟩) ?_
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) k

section Certs


theorem concl166S_of_witness_of_comp {K : Type} [Group K] [Finite K] {p q : ℕ}
    {B : Subgroup K} {x : K} {J : Subgroup K} (hq : q.Prime) (hq2 : q ≠ 2)
    (hB : IsElemAbelian q B) (hx : x ∈ B)
    (hx1 : x ≠ 1) (hrankB : Nat.card B = q ^ evenRank K) (he : 4 ≤ evenRank K)
    (hJx : J ≤ Subgroup.centralizer ({x} : Set K)) (hJq : CFSG.IsQuasisimple ↥J)
    (hcomp : IsComponentOf J (Subgroup.centralizer ({x} : Set K)) ∧
      GLALayer (Subgroup.centralizer ({x} : Set K)) = J)
    (labJ : GLALabel) (hJlab : HasLabel ↥J (fun l : GLALabel => l = labJ))
    (hshape : ∀ lab : GLALabel, HasLabel K (fun l : GLALabel => l = lab) →
      JShape lab (3 ∣ Nat.card (Subgroup.center K)) labJ)
    (hm2 : evenRank K + 2 ≤ twoRank ↥J) (hodd : Odd (Nat.card (Subgroup.center ↥J)))
    (hdvd : p * q ∣ Nat.card (↥J ⧸ Subgroup.center ↥J))
    (hsix : (Subgroup.center ↥J = ⊥ ∧ TrivialMultiplierT ↥J) ∨
      (evenRank K = 4 ∧ ∃ labJ : GLALabel, HasLabel ↥J (fun l : GLALabel => l = labJ) ∧
        labJ.tag = .twA ∧ labJ.rank = 4 ∧ Even labJ.n) ∨
      (J = ⊤ ∧ 3 ∣ Nat.card (Subgroup.center K) ∧ ∃ lab : GLALabel,
        HasLabel K (fun l : GLALabel => l = lab) ∧ Odd lab.n ∧
        ((lab.tag = .twA ∧ lab.rank = 5) ∨ lab.tag = .twE6)))
    (E : Subgroup K) (hEB : E ≤ B) (hE : IsElemAbelian q E) (hEcard : Nat.card E = q ^ 3)
    (hxE : x ∈ E) (he3 : GLAPLayer q (J ⊓ Subgroup.centralizer (E : Set K)) ≠ ⊥)
    (hBJ : B ≤ J ⊔ Subgroup.zpowers x)
    (hrankinf : evenRank K ≤ CFSG.Open.pRank q (B ⊓ J) + 2)
    (S : Subgroup K) (hSJ : S ≤ J) (hS2 : IsPGroup 2 S)
    (hBS : B ≤ Subgroup.normalizer (S : Set K))
    (hBJS : B ⊓ J ⊓ Subgroup.centralizer (S : Set K) ≤ Subgroup.zpowers x)
    (hsu : 3 ∣ Nat.card (Subgroup.center K) →
      (∃ lab : GLALabel, HasLabel K (fun l : GLALabel => l = lab) ∧
        ((lab.tag = .twA ∧ lab.rank = 5) ∨ lab.tag = .twE6)) →
      J = ⊤ ∧ q = 3 ∧ ∀ k : K, k * x = x * k) :
    Concl166S K p q B x J := by
  have h8 : B ⊓ Subgroup.centralizer (S : Set K) = Subgroup.zpowers x :=
    inf_centralizer_eq_zpowers_of_le_sup hJx hBJ hx hSJ hBJS
  have hSne : S ≠ ⊥ := by
    intro hbot
    have htop : Subgroup.centralizer (S : Set K) = ⊤ := by
      rw [hbot, Subgroup.centralizer_eq_top_iff_subset]
      intro y hy
      have hy1 : y = 1 := by simpa using hy
      rw [hy1]
      exact Subgroup.one_mem _
    have hBeq : B = Subgroup.zpowers x := by
      rw [htop, inf_top_eq] at h8
      exact h8
    have hdvdq : orderOf x ∣ q := orderOf_dvd_of_pow_eq_one (hB.2 x hx)
    have hle : orderOf x ≤ q := Nat.le_of_dvd hq.pos hdvdq
    have hge : q ^ 4 ≤ orderOf x := by
      have h' : q ^ 4 ≤ Nat.card B := by
        rw [hrankB]
        exact Nat.pow_le_pow_right hq.one_le he
      rwa [hBeq, Nat.card_zpowers] at h'
    have hlt : q < q ^ 4 := by
      simpa using Nat.pow_lt_pow_right hq.one_lt (show 1 < 4 by norm_num)
    omega
  exact
    { prime := hq
      odd := hq2
      elem := hB
      mem := hx
      ne_one := hx1
      rank_B := hrankB
      rank_K := twoLocalRank_eq_of_normalizes hq hq2 hB hrankB hSne hS2 hBS
      comp := hcomp
      chev2 := hasLabel_mono (fun _ _ => trivial) hJlab
      shape := fun lab hlab => ⟨labJ, hJlab, hshape lab hlab⟩
      m2 := hm2
      odd_center := hodd
      e3 := ⟨E, hEB, hE, hEcard, hxE, he3⟩
      dvd := hdvd
      six := hsix
      idiag := innerDiagMarking_of_le_sup (hasLabel_mono (fun _ _ => trivial) hJlab) hJx hBJ
      seven := Or.inl hBJ
      rank_inf := hrankinf
      eight := ⟨S, hSJ, hS2, hBS, h8⟩
      su_case := hsu }

theorem concl166S_of_witness {K : Type} [Group K] [Finite K] {p q : ℕ} {B : Subgroup K} {x : K}
    {J : Subgroup K} (hq : q.Prime) (hq2 : q ≠ 2) (hB : IsElemAbelian q B) (hx : x ∈ B)
    (hx1 : x ≠ 1) (hrankB : Nat.card B = q ^ evenRank K) (he : 4 ≤ evenRank K)
    (hJx : J ≤ Subgroup.centralizer ({x} : Set K)) (hJq : CFSG.IsQuasisimple ↥J)
    (hcomm : ∀ g ∈ Subgroup.centralizer ({x} : Set K),
      ∀ h ∈ Subgroup.centralizer ({x} : Set K), g * h * g⁻¹ * h⁻¹ ∈ J)
    (labJ : GLALabel) (hJlab : HasLabel ↥J (fun l : GLALabel => l = labJ))
    (hshape : ∀ lab : GLALabel, HasLabel K (fun l : GLALabel => l = lab) →
      JShape lab (3 ∣ Nat.card (Subgroup.center K)) labJ)
    (hm2 : evenRank K + 2 ≤ twoRank ↥J) (hodd : Odd (Nat.card (Subgroup.center ↥J)))
    (hdvd : p * q ∣ Nat.card (↥J ⧸ Subgroup.center ↥J))
    (hsix : (Subgroup.center ↥J = ⊥ ∧ TrivialMultiplierT ↥J) ∨
      (evenRank K = 4 ∧ ∃ labJ : GLALabel, HasLabel ↥J (fun l : GLALabel => l = labJ) ∧
        labJ.tag = .twA ∧ labJ.rank = 4 ∧ Even labJ.n) ∨
      (J = ⊤ ∧ 3 ∣ Nat.card (Subgroup.center K) ∧ ∃ lab : GLALabel,
        HasLabel K (fun l : GLALabel => l = lab) ∧ Odd lab.n ∧
        ((lab.tag = .twA ∧ lab.rank = 5) ∨ lab.tag = .twE6)))
    (E : Subgroup K) (hEB : E ≤ B) (hE : IsElemAbelian q E) (hEcard : Nat.card E = q ^ 3)
    (hxE : x ∈ E) (he3 : GLAPLayer q (J ⊓ Subgroup.centralizer (E : Set K)) ≠ ⊥)
    (hBJ : B ≤ J ⊔ Subgroup.zpowers x)
    (hrankinf : evenRank K ≤ CFSG.Open.pRank q (B ⊓ J) + 2)
    (S : Subgroup K) (hSJ : S ≤ J) (hS2 : IsPGroup 2 S)
    (hBS : B ≤ Subgroup.normalizer (S : Set K))
    (hBJS : B ⊓ J ⊓ Subgroup.centralizer (S : Set K) ≤ Subgroup.zpowers x)
    (hsu : 3 ∣ Nat.card (Subgroup.center K) →
      (∃ lab : GLALabel, HasLabel K (fun l : GLALabel => l = lab) ∧
        ((lab.tag = .twA ∧ lab.rank = 5) ∨ lab.tag = .twE6)) →
      J = ⊤ ∧ q = 3 ∧ ∀ k : K, k * x = x * k) :
    Concl166S K p q B x J :=
  concl166S_of_witness_of_comp hq hq2 hB hx hx1 hrankB he hJx hJq
    (isComponentOf_and_glaLayer_eq_of_commutator_mem hJx hcomm hJq) labJ hJlab hshape hm2 hodd
    hdvd hsix E hEB hE hEcard hxE he3 hBJ hrankinf S hSJ hS2 hBS hBJS hsu

end Certs

theorem concl166S_of_witness_idiag_of_comp {K : Type} [Group K] [Finite K] {p q : ℕ}
    {B : Subgroup K} {x : K} {J : Subgroup K} (hq : q.Prime) (hq2 : q ≠ 2)
    (hB : IsElemAbelian q B) (hx : x ∈ B)
    (hx1 : x ≠ 1) (hrankB : Nat.card B = q ^ evenRank K) (he : 4 ≤ evenRank K)
    (hJx : J ≤ Subgroup.centralizer ({x} : Set K)) (hJq : CFSG.IsQuasisimple ↥J)
    (hcomp : IsComponentOf J (Subgroup.centralizer ({x} : Set K)) ∧
      GLALayer (Subgroup.centralizer ({x} : Set K)) = J)
    (labJ : GLALabel) (hJlab : HasLabel ↥J (fun l : GLALabel => l = labJ))
    (hshape : ∀ lab : GLALabel, HasLabel K (fun l : GLALabel => l = lab) →
      JShape lab (3 ∣ Nat.card (Subgroup.center K)) labJ)
    (hm2 : evenRank K + 2 ≤ twoRank ↥J) (hodd : Odd (Nat.card (Subgroup.center ↥J)))
    (hdvd : p * q ∣ Nat.card (↥J ⧸ Subgroup.center ↥J))
    (hsix : (Subgroup.center ↥J = ⊥ ∧ TrivialMultiplierT ↥J) ∨
      (evenRank K = 4 ∧ ∃ labJ : GLALabel, HasLabel ↥J (fun l : GLALabel => l = labJ) ∧
        labJ.tag = .twA ∧ labJ.rank = 4 ∧ Even labJ.n) ∨
      (J = ⊤ ∧ 3 ∣ Nat.card (Subgroup.center K) ∧ ∃ lab : GLALabel,
        HasLabel K (fun l : GLALabel => l = lab) ∧ Odd lab.n ∧
        ((lab.tag = .twA ∧ lab.rank = 5) ∨ lab.tag = .twE6)))
    (E : Subgroup K) (hEB : E ≤ B) (hE : IsElemAbelian q E) (hEcard : Nat.card E = q ^ 3)
    (hxE : x ∈ E) (he3 : GLAPLayer q (J ⊓ Subgroup.centralizer (E : Set K)) ≠ ⊥)
    (hidiag : InnerDiagMarking B J)
    (hseven : B ≤ J ⊔ Subgroup.zpowers x ∨
      HasLabel K (fun l : GLALabel => l = ⟨.twA, 5, 2⟩))
    (hrankinf : evenRank K ≤ CFSG.Open.pRank q (B ⊓ J) + 2)
    (S : Subgroup K) (hSJ : S ≤ J) (hS2 : IsPGroup 2 S)
    (hBS : B ≤ Subgroup.normalizer (S : Set K))
    (h8 : B ⊓ Subgroup.centralizer (S : Set K) = Subgroup.zpowers x)
    (hsu : 3 ∣ Nat.card (Subgroup.center K) →
      (∃ lab : GLALabel, HasLabel K (fun l : GLALabel => l = lab) ∧
        ((lab.tag = .twA ∧ lab.rank = 5) ∨ lab.tag = .twE6)) →
      J = ⊤ ∧ q = 3 ∧ ∀ k : K, k * x = x * k) :
    Concl166S K p q B x J := by
  have hSne : S ≠ ⊥ := by
    intro hbot
    have htop : Subgroup.centralizer (S : Set K) = ⊤ := by
      rw [hbot, Subgroup.centralizer_eq_top_iff_subset]
      intro y hy
      have hy1 : y = 1 := by simpa using hy
      rw [hy1]
      exact Subgroup.one_mem _
    have hBeq : B = Subgroup.zpowers x := by
      rw [htop, inf_top_eq] at h8
      exact h8
    have hdvdq : orderOf x ∣ q := orderOf_dvd_of_pow_eq_one (hB.2 x hx)
    have hle : orderOf x ≤ q := Nat.le_of_dvd hq.pos hdvdq
    have hge : q ^ 4 ≤ orderOf x := by
      have h' : q ^ 4 ≤ Nat.card B := by
        rw [hrankB]
        exact Nat.pow_le_pow_right hq.one_le he
      rwa [hBeq, Nat.card_zpowers] at h'
    have hlt : q < q ^ 4 := by
      simpa using Nat.pow_lt_pow_right hq.one_lt (show 1 < 4 by norm_num)
    omega
  exact
    { prime := hq
      odd := hq2
      elem := hB
      mem := hx
      ne_one := hx1
      rank_B := hrankB
      rank_K := twoLocalRank_eq_of_normalizes hq hq2 hB hrankB hSne hS2 hBS
      comp := hcomp
      chev2 := hasLabel_mono (fun _ _ => trivial) hJlab
      shape := fun lab hlab => ⟨labJ, hJlab, hshape lab hlab⟩
      m2 := hm2
      odd_center := hodd
      e3 := ⟨E, hEB, hE, hEcard, hxE, he3⟩
      dvd := hdvd
      six := hsix
      idiag := hidiag
      seven := hseven
      rank_inf := hrankinf
      eight := ⟨S, hSJ, hS2, hBS, h8⟩
      su_case := hsu }

theorem concl166S_of_witness_idiag {K : Type} [Group K] [Finite K] {p q : ℕ}
    {B : Subgroup K} {x : K} {J : Subgroup K} (hq : q.Prime) (hq2 : q ≠ 2)
    (hB : IsElemAbelian q B) (hx : x ∈ B)
    (hx1 : x ≠ 1) (hrankB : Nat.card B = q ^ evenRank K) (he : 4 ≤ evenRank K)
    (hJx : J ≤ Subgroup.centralizer ({x} : Set K)) (hJq : CFSG.IsQuasisimple ↥J)
    (hcomm : ∀ g ∈ Subgroup.centralizer ({x} : Set K),
      ∀ h ∈ Subgroup.centralizer ({x} : Set K), g * h * g⁻¹ * h⁻¹ ∈ J)
    (labJ : GLALabel) (hJlab : HasLabel ↥J (fun l : GLALabel => l = labJ))
    (hshape : ∀ lab : GLALabel, HasLabel K (fun l : GLALabel => l = lab) →
      JShape lab (3 ∣ Nat.card (Subgroup.center K)) labJ)
    (hm2 : evenRank K + 2 ≤ twoRank ↥J) (hodd : Odd (Nat.card (Subgroup.center ↥J)))
    (hdvd : p * q ∣ Nat.card (↥J ⧸ Subgroup.center ↥J))
    (hsix : (Subgroup.center ↥J = ⊥ ∧ TrivialMultiplierT ↥J) ∨
      (evenRank K = 4 ∧ ∃ labJ : GLALabel, HasLabel ↥J (fun l : GLALabel => l = labJ) ∧
        labJ.tag = .twA ∧ labJ.rank = 4 ∧ Even labJ.n) ∨
      (J = ⊤ ∧ 3 ∣ Nat.card (Subgroup.center K) ∧ ∃ lab : GLALabel,
        HasLabel K (fun l : GLALabel => l = lab) ∧ Odd lab.n ∧
        ((lab.tag = .twA ∧ lab.rank = 5) ∨ lab.tag = .twE6)))
    (E : Subgroup K) (hEB : E ≤ B) (hE : IsElemAbelian q E) (hEcard : Nat.card E = q ^ 3)
    (hxE : x ∈ E) (he3 : GLAPLayer q (J ⊓ Subgroup.centralizer (E : Set K)) ≠ ⊥)
    (hidiag : InnerDiagMarking B J)
    (hseven : B ≤ J ⊔ Subgroup.zpowers x ∨
      HasLabel K (fun l : GLALabel => l = ⟨.twA, 5, 2⟩))
    (hrankinf : evenRank K ≤ CFSG.Open.pRank q (B ⊓ J) + 2)
    (S : Subgroup K) (hSJ : S ≤ J) (hS2 : IsPGroup 2 S)
    (hBS : B ≤ Subgroup.normalizer (S : Set K))
    (h8 : B ⊓ Subgroup.centralizer (S : Set K) = Subgroup.zpowers x)
    (hsu : 3 ∣ Nat.card (Subgroup.center K) →
      (∃ lab : GLALabel, HasLabel K (fun l : GLALabel => l = lab) ∧
        ((lab.tag = .twA ∧ lab.rank = 5) ∨ lab.tag = .twE6)) →
      J = ⊤ ∧ q = 3 ∧ ∀ k : K, k * x = x * k) :
    Concl166S K p q B x J :=
  concl166S_of_witness_idiag_of_comp hq hq2 hB hx hx1 hrankB he hJx hJq
    (isComponentOf_and_glaLayer_eq_of_commutator_mem hJx hcomm hJq) labJ hJlab hshape hm2 hodd
    hdvd hsix E hEB hE hEcard hxE he3 hidiag hseven hrankinf S hSJ hS2 hBS h8 hsu

end CFSG.LocalAnalysis.GLTheoremA.Y10F
