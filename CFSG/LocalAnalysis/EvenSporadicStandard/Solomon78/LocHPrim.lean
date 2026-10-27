module

public import CFSG.Open.MonsterDefs

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.Open

section Abstract

variable {X : Type*} [Group X]

theorem ncard_conj_orbit_mul_card_inf_centralizer (K : Subgroup X) (x : X) :
    {y : X | ∃ k ∈ K, k * x * k⁻¹ = y}.ncard * Nat.card ↥(K ⊓ centralizer ({x} : Set X)) =
      Nat.card K := by
  let _ : MulAction K X := MulAction.compHom X (MulAut.conj.comp K.subtype)
  have hsmul : ∀ (k : K) (y : X), k • y = (k : X) * y * (k : X)⁻¹ := fun k y => rfl
  have horb : MulAction.orbit K x = {y : X | ∃ k ∈ K, k * x * k⁻¹ = y} := by
    ext y
    simp only [MulAction.mem_orbit_iff, hsmul, Set.mem_ofPred_eq]
    exact ⟨fun ⟨k, hk⟩ => ⟨k, k.2, hk⟩, fun ⟨k, hk, h⟩ => ⟨⟨k, hk⟩, h⟩⟩
  have hstab : MulAction.stabilizer K x = (K ⊓ centralizer ({x} : Set X)).subgroupOf K := by
    ext k
    simp only [MulAction.mem_stabilizer_iff, hsmul, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]
    exact ⟨fun h => ⟨k.2, h⟩, fun h => h.2⟩
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup K x)
  rw [Nat.card_prod, horb, hstab,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv, Nat.card_coe_set_eq] at h
  exact h

theorem exists_card_eq_mul_sum_of_centralizer_le [Finite X] {ι : Type*} [Fintype ι]
    (a : X) (β : ι → X) (s : ι → ℕ) (i₀ : ι)
    (hβ : ∀ i, IsConj a (β i)) (hi₀ : β i₀ = a)
    (hinj : ∀ i j, IsConj (a * β i) (a * β j) → i = j)
    (hcov : ∀ γ, IsConj a γ → ∃ i, IsConj (a * γ) (a * β i))
    (horb : ∀ β', IsConj a β' → ∀ β'', IsConj a β'' → IsConj (a * β') (a * β'') →
      ∃ g ∈ centralizer ({a} : Set X), g * β' * g⁻¹ = β'')
    (hs : ∀ i, s i * Nat.card ↥(centralizer ({a} : Set X) ⊓ centralizer ({β i} : Set X)) =
      Nat.card ↥(centralizer ({a} : Set X)))
    {H : Subgroup X} (hH : centralizer ({a} : Set X) ≤ H) :
    ∃ I : Finset ι, i₀ ∈ I ∧
      Nat.card H = Nat.card ↥(centralizer ({a} : Set X)) * ∑ i ∈ I, s i := by
  classical
  have := Fintype.ofFinite X
  set C := centralizer ({a} : Set X) with hC
  have hCmem : ∀ g, g ∈ C ↔ g * a = a * g := fun g => Subgroup.mem_centralizer_singleton_iff
  have hex : ∀ x : X, ∃ i, IsConj a x → IsConj (a * x) (a * β i) := fun x =>
    if h : IsConj a x then (hcov x h).imp fun i hi _ => hi else ⟨i₀, fun h' => absurd h' h⟩
  choose lab hlab using hex
  have hlab_eq : ∀ x, IsConj a x → ∀ i, lab x = i ↔ IsConj (a * x) (a * β i) := by
    intro x hx i
    exact ⟨fun h => h ▸ hlab x hx, fun h => hinj _ _ ((hlab x hx).symm.trans h)⟩
  let B : Finset X := Finset.univ.filter (fun x => ∃ h ∈ H, h * a * h⁻¹ = x)
  have hmemB : ∀ x, x ∈ B ↔ ∃ h ∈ H, h * a * h⁻¹ = x := by
    intro x
    simp [B]
  have hBD : ∀ x ∈ B, IsConj a x := by
    intro x hx
    obtain ⟨h, -, rfl⟩ := (hmemB x).1 hx
    exact isConj_iff.2 ⟨h, rfl⟩
  have hBC : ∀ g ∈ C, ∀ x ∈ B, g * x * g⁻¹ ∈ B := by
    intro g hg x hx
    obtain ⟨h, hh, rfl⟩ := (hmemB x).1 hx
    exact (hmemB _).2 ⟨g * h, mul_mem (hH hg) hh, by simp [mul_assoc]⟩
  have hBcard : B.card * Nat.card C = Nat.card H := by
    have h1 := ncard_conj_orbit_mul_card_inf_centralizer H a
    rw [inf_eq_right.2 hH] at h1
    have h2 : {y : X | ∃ k ∈ H, k * a * k⁻¹ = y}.ncard = B.card := by
      rw [← Set.ncard_coe_finset]
      congr 1
      ext y
      simp [hmemB]
    rw [h2] at h1
    exact h1
  let I : Finset ι := Finset.univ.filter (fun i => ∃ x ∈ B, lab x = i)
  have hfib : ∀ i ∈ I, (B.filter (fun x => lab x = i)).card = s i := by
    intro i hi
    obtain ⟨x₀, hx₀, hlx₀⟩ := (Finset.mem_filter.1 hi).2
    have hx₀D := hBD x₀ hx₀
    have hx₀i : IsConj (a * x₀) (a * β i) := (hlab_eq x₀ hx₀D i).1 hlx₀
    obtain ⟨g, hg, hgx⟩ := horb x₀ hx₀D (β i) (hβ i) hx₀i
    have hβB : β i ∈ B := hgx ▸ hBC g hg x₀ hx₀
    have hset : {y : X | ∃ k ∈ C, k * β i * k⁻¹ = y} = ↑(B.filter (fun x => lab x = i)) := by
      ext y
      simp only [Set.mem_ofPred_eq, Finset.coe_filter]
      constructor
      · rintro ⟨k, hk, rfl⟩
        refine ⟨hBC k hk _ hβB, ?_⟩
        have hyD := hBD _ (hBC k hk _ hβB)
        rw [hlab_eq _ hyD i]
        refine (isConj_iff.2 ⟨k, ?_⟩).symm
        have hk' := (hCmem k).1 hk
        calc k * (a * β i) * k⁻¹ = (k * a) * β i * k⁻¹ := by simp [mul_assoc]
          _ = (a * k) * β i * k⁻¹ := by rw [hk']
          _ = a * (k * β i * k⁻¹) := by simp [mul_assoc]
      · rintro ⟨hyB, hly⟩
        have hyD := hBD y hyB
        have hyi : IsConj (a * y) (a * β i) := (hlab_eq y hyD i).1 hly
        obtain ⟨k, hk, hky⟩ := horb (β i) (hβ i) y hyD hyi.symm
        exact ⟨k, hk, hky⟩
    have hcard := ncard_conj_orbit_mul_card_inf_centralizer C (β i)
    rw [hset, Set.ncard_coe_finset] at hcard
    have hpos : 0 < Nat.card ↥(C ⊓ centralizer ({β i} : Set X)) := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos (hcard.trans (hs i).symm)
  have hsum : B.card = ∑ i ∈ I, s i := by
    rw [Finset.card_eq_sum_card_fiberwise (f := lab) (t := I) ?_]
    · exact Finset.sum_congr rfl hfib
    · intro x hx
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, x, hx, rfl⟩
  refine ⟨I, ?_, ?_⟩
  · have ha : a ∈ B := (hmemB a).2 ⟨1, one_mem _, by simp⟩
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, a, ha, ?_⟩
    rw [hlab_eq a (IsConj.refl a), hi₀]
  · rw [← hBcard, hsum, mul_comm]

end Abstract

section Arithmetic

@[expose] def monsterSuborbitSize : Fin 9 → ℕ :=
  ![1, 27143910000, 11707448673375, 2031941058560000, 91569524834304000, 1102935324621312000,
    1254793905192960000, 30434513446055706624, 64353605265653760000]

theorem monsterSuborbitSize_mul (i : Fin 9) :
    monsterSuborbitSize i * (monsterSuborbitSimpleOrder i * 2 ^ monsterSuborbitTwoExponent i) =
      monsterBabyOrder * 2 ^ 1 := by
  decide +revert

theorem sum_monsterSuborbitSize : ∑ i, monsterSuborbitSize i = 97239461142009186000 := by
  decide

theorem monsterOrder_eq_centralizer_mul_class :
    monsterOrder = monsterBabyOrder * 2 ^ 1 * 97239461142009186000 := by
  decide

set_option maxRecDepth 10000 in
theorem eq_singleton_or_eq_univ_of_dvd_sum_monsterSuborbitSize (I : Finset (Fin 9)) (h0 : 0 ∈ I)
    (hdvd : ∑ i ∈ I, monsterSuborbitSize i ∣ 97239461142009186000) :
    I = {0} ∨ I = Finset.univ := by
  revert I
  decide

end Arithmetic

theorem isCoatom_centralizer_of_monsterTwoAGraphData {X : Type} [Group X] [Finite X]
    (hord : Nat.card X = CFSG.Open.monsterOrder) {a z : X} (ha : orderOf a = 2)
    (hgraph : CFSG.Open.MonsterTwoAGraphData a z) :
    IsCoatom (Subgroup.centralizer ({a} : Set X)) := by
  obtain ⟨horb, β, hβ, hβ0, hinj, hcov, -, -, hel, hshape, -⟩ := hgraph
  have hcard : ∀ i, Nat.card ↥(monsterCent2 a (β i)) =
      monsterSuborbitSimpleOrder i * 2 ^ monsterSuborbitTwoExponent i := by
    intro i
    obtain ⟨N, -, hN, -, hQ⟩ := hshape i
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N, hN, hQ]
  have hC : Nat.card ↥(Subgroup.centralizer ({a} : Set X)) = monsterBabyOrder * 2 ^ 1 := by
    have h0 := hcard 0
    rw [hβ0, monsterCent2, inf_idem] at h0
    exact h0
  have hs : ∀ i, monsterSuborbitSize i * Nat.card ↥(Subgroup.centralizer ({a} : Set X) ⊓
      Subgroup.centralizer ({β i} : Set X)) = Nat.card ↥(Subgroup.centralizer ({a} : Set X)) := by
    intro i
    rw [hC]
    exact (hcard i ▸ monsterSuborbitSize_mul i : _)
  have hne : Subgroup.centralizer ({a} : Set X) ≠ ⊤ := by
    intro htop
    have hcomm : ∀ g : X, g * a = a * g := fun g =>
      Subgroup.mem_centralizer_singleton_iff.1 (htop ▸ Subgroup.mem_top g)
    have hβa : ∀ i, β i = a := by
      intro i
      obtain ⟨c, hc⟩ := isConj_iff.1 (hβ i)
      rw [← hc, hcomm c, mul_inv_cancel_right]
    have h1 : a * β 1 = 1 := by
      rw [hβa 1, ← sq]
      exact ha ▸ pow_orderOf_eq_one a
    have h2 := hel 1
    rw [h1, orderOf_one] at h2
    exact absurd h2 (by decide)
  refine ⟨hne, fun H hH => ?_⟩
  obtain ⟨I, h0I, hHcard⟩ := exists_card_eq_mul_sum_of_centralizer_le a β monsterSuborbitSize 0
    hβ hβ0 hinj hcov horb hs hH.le
  have hCpos : 0 < Nat.card ↥(Subgroup.centralizer ({a} : Set X)) := Nat.card_pos
  have hdvd : Nat.card ↥(Subgroup.centralizer ({a} : Set X)) * ∑ i ∈ I, monsterSuborbitSize i ∣
      Nat.card ↥(Subgroup.centralizer ({a} : Set X)) * 97239461142009186000 := by
    rw [← hHcard, hC, ← monsterOrder_eq_centralizer_mul_class, ← hord]
    exact Subgroup.card_subgroup_dvd_card H
  rcases eq_singleton_or_eq_univ_of_dvd_sum_monsterSuborbitSize I h0I
    (Nat.dvd_of_mul_dvd_mul_left hCpos hdvd) with rfl | rfl
  · refine absurd (Subgroup.eq_of_le_of_card_ge hH.le ?_) hH.ne
    rw [hHcard]
    simp [monsterSuborbitSize]
  · rw [sum_monsterSuborbitSize] at hHcard
    rw [← Subgroup.card_eq_iff_eq_top, hHcard, hC, ← monsterOrder_eq_centralizer_mul_class, hord]

end CFSG.EvenSporadicStandard.Solomon78
