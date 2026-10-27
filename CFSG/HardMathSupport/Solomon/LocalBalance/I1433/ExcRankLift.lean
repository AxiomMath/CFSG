module

public import CFSG.Assembly.RankThreeEvenDefs
import CFSG.RankThree.CentralCover.SteinbergBNCoverPairingCore
import CFSG.RankThree.PartTwo.Census.Criteria
import CFSG.RankThree.Theta.ThreeComponentOrbitCover

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.ExcRank

open CFSG.RankThree.CentralCover CFSG.RankThree.Classical2 CFSG.Assembly.RankThreeEven CFSG.Open

theorem eq_one_of_sq_eq_one_of_pow_eq_one' {G : Type*} [Group G] {x : G} {p : ℕ} (hp : Odd p)
    (h2 : x ^ 2 = 1) (hp1 : x ^ p = 1) : x = 1 := by
  obtain ⟨k, rfl⟩ := hp
  rw [pow_succ, pow_mul, h2, one_pow, one_mul] at hp1
  exact hp1

section Independence

theorem commute_of_commute_zpow' {G : Type*} [Group G] {g y : G} (hg : g ^ 3 = 1) {a : ℤ}
    (ha : ¬ (3 : ℤ) ∣ a) (h : Commute y (g ^ a)) : Commute y g := by
  have h3 : (3 : ℤ) ∣ a * a - 1 := by
    have : (3 : ℤ) ∣ a - 1 ∨ (3 : ℤ) ∣ a + 1 := by omega
    rcases this with h1 | h1
    · exact (h1.mul_right (a + 1)).trans (by rw [show (a - 1) * (a + 1) = a * a - 1 by ring])
    · exact (h1.mul_left (a - 1)).trans (by rw [show (a - 1) * (a + 1) = a * a - 1 by ring])
  obtain ⟨m, hm⟩ := h3
  have hg' : g ^ (3 : ℤ) = 1 := by rw [zpow_ofNat]; exact hg
  have e : (g ^ a) ^ a = g := by
    rw [← zpow_mul, show a * a = 1 + 3 * m by omega, zpow_add, zpow_one, zpow_mul, hg',
      one_zpow, mul_one]
  rw [← e]
  exact h.zpow_right a

theorem zpow_eq_one_of_three_dvd' {G : Type*} [Group G] {g : G} (hg : g ^ 3 = 1) {a : ℤ}
    (ha : (3 : ℤ) ∣ a) : g ^ a = 1 := by
  obtain ⟨m, rfl⟩ := ha
  rw [zpow_mul, zpow_ofNat, hg, one_zpow]

theorem eq_one_of_mem_closure' {G : Type*} [Group G] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι → G) (e₀ : G)
    (y : ι → G) (hee : ∀ i j, Commute (e i) (e j)) (he3 : ∀ i, e i ^ 3 = 1)
    (hy : ∀ i j, i ≠ j → Commute (y i) (e j)) (hy₀ : ∀ i, Commute (y i) e₀)
    (hyi : ∀ i, ¬ Commute (y i) (e i)) (h : e₀ ∈ Subgroup.closure (Set.range e)) : e₀ = 1 := by
  set H := Subgroup.closure (Set.range e)
  have hpair : (Set.range e).Pairwise Commute := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ -
    exact hee i j
  have hHc : IsMulCommutative H := Subgroup.isMulCommutative_closure hpair
  have hcomm : ∀ a b : H, a * b = b * a := fun a b => mul_comm' a b
  let : CommGroup H := { (inferInstance : Group H) with mul_comm := hcomm }
  let e' : ι → H := fun i => ⟨e i, Subgroup.subset_closure ⟨i, rfl⟩⟩
  have hgen : Subgroup.closure (Set.range e') = ⊤ := by
    rw [eq_top_iff, ← Subgroup.closure_closure_coe_preimage (k := Set.range e)]
    refine Subgroup.closure_mono ?_
    rintro x ⟨i, hi⟩
    exact ⟨i, Subtype.ext hi⟩
  obtain ⟨a, ha⟩ := Subgroup.exists_of_mem_closure_range e' ⟨e₀, h⟩
    (hgen ▸ Subgroup.mem_top _)
  have hfac : ∀ i, e' i ^ a i = 1 := by
    intro i
    set C : Subgroup H := (Subgroup.centralizer ({y i} : Set G)).subgroupOf H
    have hC : ∀ j, j ≠ i → e' j ^ a j ∈ C := fun j hj => by
      refine C.zpow_mem ?_ _
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
      exact ((hy i j (Ne.symm hj)).eq).symm
    have hC0 : (⟨e₀, h⟩ : H) ∈ C := by
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
      exact (hy₀ i).eq.symm
    have hprod : (∏ j ∈ Finset.univ.erase i, e' j ^ a j) ∈ C :=
      Subgroup.prod_mem C fun j hj => hC j (Finset.ne_of_mem_erase hj)
    have hsplit := Finset.mul_prod_erase Finset.univ (fun j => e' j ^ a j) (Finset.mem_univ i)
    have hi : e' i ^ a i ∈ C := by
      have e1 : e' i ^ a i = (⟨e₀, h⟩ : H) * (∏ j ∈ Finset.univ.erase i, e' j ^ a j)⁻¹ := by
        rw [ha, ← hsplit, mul_inv_cancel_right]
      rw [e1]
      exact C.mul_mem hC0 (C.inv_mem hprod)
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff] at hi
    by_cases h3 : (3 : ℤ) ∣ a i
    · exact Subtype.ext (by
        rw [Subgroup.coe_zpow, Subgroup.coe_one]
        exact zpow_eq_one_of_three_dvd' (he3 i) h3)
    · exfalso
      refine hyi i (commute_of_commute_zpow' (he3 i) h3 ?_)
      have : (((e' i ^ a i : H)) : G) = e i ^ a i := Subgroup.coe_zpow _ _ _
      rw [← this]
      exact hi.symm
  have : (⟨e₀, h⟩ : H) = 1 := by
    rw [ha]
    exact Finset.prod_eq_one fun i _ => hfac i
  exact congrArg Subtype.val this

end Independence

section Inversion

variable {G : Type*} [Group G]

theorem three_pow_le_card_closure [Finite G] {m : ℕ} (h w : Fin (m + 1) → G)
    (hcomm : ∀ i j, Commute (h i) (h j)) (hord : ∀ i, orderOf (h i) = 3)
    (hinv : ∀ i, w i * h i * (w i)⁻¹ = (h i)⁻¹)
    (hfix : ∀ i j, i ≠ j → i ≠ Fin.last m → w i * h j * (w i)⁻¹ = h j) :
    3 ^ (m + 1) ≤ Nat.card (Subgroup.closure (Set.range h)) := by
  classical
  have h3 : ∀ i, h i ^ 3 = 1 := fun i => (hord i) ▸ pow_orderOf_eq_one (h i)
  have hne1 : ∀ i, h i ≠ 1 := fun i hi => by
    have := hord i
    rw [hi, orderOf_one] at this
    omega
  have hwc : ∀ i j, i ≠ j → i ≠ Fin.last m → Commute (w i) (h j) := fun i j hij hi => by
    have e := hfix i j hij hi
    rw [mul_inv_eq_iff_eq_mul] at e
    exact e
  have hwi : ∀ i, ¬ Commute (w i) (h i) := fun i hc => by
    have e : w i * h i * (w i)⁻¹ = h i := by rw [hc.eq, mul_inv_cancel_right]
    rw [hinv i] at e
    have h2 : h i ^ 2 = 1 := by
      calc h i ^ 2 = h i * h i := sq _
        _ = (h i)⁻¹ * h i := by rw [e]
        _ = 1 := inv_mul_cancel _
    exact hne1 i (eq_one_of_sq_eq_one_of_pow_eq_one' (by decide) h2 (h3 i))
  set Y := Subgroup.closure (Set.range h) with hY
  have hpair : (Set.range h).Pairwise Commute := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ -
    exact hcomm i j
  have hYc : IsMulCommutative Y := Subgroup.isMulCommutative_closure hpair
  have hcomm' : ∀ a b : Y, a * b = b * a := fun a b => mul_comm' a b
  let : CommGroup Y := { (inferInstance : Group Y) with mul_comm := hcomm' }
  let f' : Fin (m + 1) → Y := fun i => ⟨h i, Subgroup.subset_closure ⟨i, rfl⟩⟩
  have hgen : Subgroup.closure (Set.range f') = ⊤ := by
    rw [eq_top_iff, ← Subgroup.closure_closure_coe_preimage (k := Set.range h)]
    refine Subgroup.closure_mono ?_
    rintro x ⟨i, hi⟩
    exact ⟨i, Subtype.ext hi⟩
  let S : Fin (m + 1) → Subgroup Y := fun i =>
    if i = Fin.last m then
      (Subgroup.closure (Set.range (fun j : Fin m => h j.castSucc))).subgroupOf Y
    else (Subgroup.centralizer ({w i} : Set G)).subgroupOf Y
  have hS_last : S (Fin.last m) =
      (Subgroup.closure (Set.range (fun j : Fin m => h j.castSucc))).subgroupOf Y := if_pos rfl
  have hS_ne : ∀ i, i ≠ Fin.last m →
      S i = (Subgroup.centralizer ({w i} : Set G)).subgroupOf Y := fun i hi => if_neg hi
  have hS : ∀ i j, i ≠ j → f' j ∈ S i := by
    intro i j hij
    by_cases hi : i = Fin.last m
    · rw [hi, hS_last]
      have hj : j ≠ Fin.last m := fun hj => hij (hi.trans hj.symm)
      obtain ⟨j', rfl⟩ := Fin.exists_castSucc_eq.2 hj
      exact Subgroup.mem_subgroupOf.2 (Subgroup.subset_closure ⟨j', rfl⟩)
    · rw [hS_ne i hi]
      exact Subgroup.mem_subgroupOf.2
        (Subgroup.mem_centralizer_singleton_iff.2 (hwc i j hij hi).eq.symm)
  have hSy : ∀ i, f' i ∉ S i := by
    intro i
    by_cases hi : i = Fin.last m
    · rw [hi, hS_last]
      intro hmem
      have hmem' := Subgroup.mem_subgroupOf.1 hmem
      refine hne1 (Fin.last m) (eq_one_of_mem_closure' (fun j : Fin m => h j.castSucc)
        (h (Fin.last m)) (fun j : Fin m => w j.castSucc) (fun i j => hcomm _ _)
        (fun i => h3 _) (fun i j hij => hwc _ _ (fun e => hij (Fin.castSucc_injective m e))
          (Fin.castSucc_ne_last i))
        (fun i => hwc _ _ (Fin.castSucc_lt_last i).ne (Fin.castSucc_ne_last i))
        (fun i => hwi _) hmem')
    · rw [hS_ne i hi]
      intro hmem
      exact hwi i (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_subgroupOf.1 hmem)).symm
  have hSy3 : ∀ i, f' i ^ 3 ∈ S i := fun i => by
    have : f' i ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact h3 i)
    rw [this]
    exact (S i).one_mem
  have hbound := CFSG.RankThree.Theta.three_pow_card_le_card_ker_pow f' hgen S hS hSy hSy3
  rw [Fintype.card_fin] at hbound
  exact hbound.trans (Subgroup.card_le_card_group _)

end Inversion

section Cover

variable {Y T : Type*} [Group Y] [Group T]

theorem exists_lift_pow_three_eq_one {φ : Y →* T} (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center Y) (hodd : Odd (Nat.card φ.ker)) {h w : T}
    (hord : orderOf h = 3) (hinv : w * h * w⁻¹ = h⁻¹) : ∃ y : Y, φ y = h ∧ y ^ 3 = 1 := by
  obtain ⟨y, hy⟩ := hφ h
  obtain ⟨g, hg⟩ := hφ w
  have hyp : y ^ 3 ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_pow, hy]
    exact hord ▸ pow_orderOf_eq_one h
  have hyc : y ^ 3 ∈ Subgroup.center Y := hker hyp
  set c : Y := g * y * g⁻¹ * y with hc
  have hcker : c ∈ φ.ker := by
    rw [MonoidHom.mem_ker, hc, map_mul, map_mul, map_mul, map_inv, hg, hy, hinv, inv_mul_cancel]
  have hcc : c ∈ Subgroup.center Y := hker hcker
  have hconj : g * y * g⁻¹ = c * y⁻¹ := by rw [hc]; group
  have h1 : g * y ^ 3 * g⁻¹ = y ^ 3 := by
    have := Subgroup.mem_center_iff.1 hyc g
    rw [this, mul_assoc, mul_inv_cancel, mul_one]
  have h2 : g * y ^ 3 * g⁻¹ = c ^ 3 * (y ^ 3)⁻¹ := by
    have e : g * y ^ 3 * g⁻¹ = (g * y * g⁻¹) ^ 3 := conj_pow.symm
    rw [e, hconj]
    have hcomm : Commute c y⁻¹ := ((Subgroup.mem_center_iff.1 hcc y⁻¹).symm : _)
    rw [hcomm.mul_pow, inv_pow]
  rw [h1] at h2
  have hsq : (y ^ 3) ^ 2 = c ^ 3 := by
    rw [pow_two]
    nth_rewrite 1 [h2]
    exact inv_mul_cancel_right _ _
  obtain ⟨n, hn⟩ := hodd
  have hu : (y ^ 3) ^ (2 * n + 1) = 1 := by
    have := pow_card_eq_one' (G := φ.ker) (x := ⟨y ^ 3, hyp⟩)
    rw [hn] at this
    exact congrArg Subtype.val this
  have hycube : y ^ 3 = (c ^ (n + 1)) ^ 3 := by
    have e1 : y ^ 3 = (y ^ 3) ^ (2 * (n + 1)) := by
      have : 2 * (n + 1) = (2 * n + 1) + 1 := by ring
      rw [this, pow_succ (y ^ 3) (2 * n + 1), hu, one_mul]
    rw [e1, pow_mul, hsq, pow_right_comm]
  have hzker : c ^ (n + 1) ∈ φ.ker := Subgroup.pow_mem _ hcker (n + 1)
  have hzcenter : c ^ (n + 1) ∈ Subgroup.center Y := hker hzker
  refine ⟨y * (c ^ (n + 1))⁻¹, ?_, ?_⟩
  · rw [map_mul, map_inv, hy, MonoidHom.mem_ker.1 hzker, inv_one, mul_one]
  · have hcomm : Commute y (c ^ (n + 1))⁻¹ :=
      (Subgroup.mem_center_iff.1 (inv_mem hzcenter) y : _)
    rw [hcomm.mul_pow, inv_pow, ← hycube, mul_inv_cancel]

theorem comap_closure_comm_of_inversions {φ : Y →* T} (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center Y) {m : ℕ} (h w : Fin (m + 1) → T)
    (hcomm : ∀ i j, Commute (h i) (h j)) (hpow : ∀ i, h i ^ 3 = 1)
    (hinv : ∀ i, w i * h i * (w i)⁻¹ = (h i)⁻¹)
    (hfix : ∀ i j, i ≠ j → i ≠ Fin.last m → w i * h j * (w i)⁻¹ = h j) :
    ∀ x ∈ (Subgroup.closure (Set.range h)).comap φ,
      ∀ y ∈ (Subgroup.closure (Set.range h)).comap φ, x * y = y * x := by
  have hS : ∀ s ∈ Set.range h, ∀ t ∈ Set.range h, Commute s t := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact hcomm i j
  have hodd : Odd 3 := by decide
  refine comap_closure_comm hφ hker hS ?_
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
  by_cases hij : i = j
  · rw [hij]
    exact liftComm_self hφ (h j)
  · by_cases hi : i = Fin.last m
    · have hj : j ≠ Fin.last m := fun hj => hij (hi.trans hj.symm)
      rw [liftComm_swap hφ, liftComm_eq_one_of_conj_inv hφ hker hodd (hcomm j i) (hpow j) (w j)
        (hinv j) (hfix j i (Ne.symm hij) hj), inv_one]
    · exact liftComm_eq_one_of_conj_inv hφ hker hodd (hcomm i j) (hpow i) (w i) (hinv i)
        (hfix i j hij hi)

end Cover

section Witness

variable {Y T : Type} [Group Y] [Finite Y] [Group T]

theorem central_cover_elem_witness {φ : Y →* T} (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center Y) {p : ℕ} (hp : p.Prime) {E : Subgroup Y}
    (hE : IsElemAbelian p E) {e : ℕ} (he : Nat.card E = p ^ e) {U : Subgroup T} (hU1 : U ≠ ⊥)
    (hU2 : IsPGroup 2 U) (hEU : ∀ x ∈ E, ∀ u ∈ U, φ x * u * (φ x)⁻¹ ∈ U) :
    e ≤ localRank p Y := by
  obtain ⟨R, hR1, hR2, hER⟩ := exists_two_subgroup_normalized_of_cover hφ hker hU1 hU2 (S := E) hEU
  exact CFSG.RankThree.PartTwo.Census.le_localRank_of_le_normalizer hp hR1 hR2 hE he hER

end Witness

@[expose] def LiftDatum (S : Type*) [Group S] (m : ℕ) : Prop :=
  ∃ (h w : Fin (m + 1) → S) (U : Subgroup S), (∀ i j, Commute (h i) (h j)) ∧
    (∀ i, orderOf (h i) = 3) ∧ (∀ i, w i * h i * (w i)⁻¹ = (h i)⁻¹) ∧
    (∀ i j, i ≠ j → i ≠ Fin.last m → w i * h j * (w i)⁻¹ = h j) ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧
    ∀ i, h i ∈ Subgroup.normalizer (U : Set S)

theorem LiftDatum.cover_localRank {K S : Type} [Group K] [Finite K] [Group S] {m : ℕ}
    (hL : LiftDatum S m) {π : K →* S} (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center K) (hodd : Odd (Nat.card π.ker)) {A : Subgroup K}
    (hAker : A ≤ π.ker) (hA3 : ∀ x ∈ A, x ^ 3 = 1) {k : ℕ} (hk : Nat.card A = 3 ^ k) :
    m + 1 + k ≤ localRank 3 K := by
  classical
  obtain ⟨h, w, U, hcomm, hord, hinv, hfix, hU1, hU2, hN⟩ := hL
  haveI : Finite S := Finite.of_surjective π hπ
  have hp3 : (3 : ℕ).Prime := Nat.prime_three
  have hpow : ∀ i, h i ^ 3 = 1 := fun i => (hord i) ▸ pow_orderOf_eq_one (h i)
  have hF := comap_closure_comm_of_inversions hπ hker h w hcomm hpow hinv hfix
  choose lift hlift hl3 using fun i =>
    exists_lift_pow_three_eq_one hπ hker hodd (hord i) (hinv i)
  set D := Subgroup.closure (Set.range h) with hD
  have hmemF : ∀ i, lift i ∈ D.comap π := fun i =>
    Subgroup.mem_comap.2 (by rw [hlift i]; exact Subgroup.subset_closure ⟨i, rfl⟩)
  have hAc : ∀ a ∈ A, ∀ y : K, a * y = y * a := fun a ha y =>
    (Subgroup.mem_center_iff.1 (hker (hAker ha)) y).symm
  set G : Set K := Set.range lift ∪ (A : Set K) with hG
  set E : Subgroup K := Subgroup.closure G with hE
  have hGc : ∀ s ∈ G, ∀ t ∈ G, Commute s t := by
    rintro s (⟨i, rfl⟩ | hs) t (⟨j, rfl⟩ | ht)
    · exact hF _ (hmemF i) _ (hmemF j)
    · exact (hAc _ ht _).symm
    · exact hAc _ hs _
    · exact hAc _ hs _
  have hG3 : ∀ s ∈ G, s ^ 3 = 1 := by
    rintro s (⟨i, rfl⟩ | hs)
    · exact hl3 i
    · exact hA3 s hs
  have hE3 : ∀ x ∈ E, x ^ 3 = 1 := fun x hx => pow_eq_one_of_mem_closure hGc hG3 hx
  have hpair : G.Pairwise Commute := fun s hs t ht _ => hGc s hs t ht
  have hEc : IsMulCommutative E := Subgroup.isMulCommutative_closure hpair
  have hEe : IsElemAbelian 3 E := ⟨hEc, hE3⟩
  have hEpg : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
    exact hE3 x x.2)⟩
  obtain ⟨e, he⟩ := IsPGroup.iff_card.mp hEpg
  let ψ : E →* S := π.comp E.subtype
  have hDle : D ≤ ψ.range := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨i, rfl⟩
    exact ⟨⟨lift i, Subgroup.subset_closure (Or.inl ⟨i, rfl⟩)⟩, hlift i⟩
  have hAE : A ≤ E := fun a ha => Subgroup.subset_closure (Or.inr ha)
  have hAle : A.subgroupOf E ≤ ψ.ker := by
    intro a ha
    rw [MonoidHom.mem_ker]
    exact MonoidHom.mem_ker.1 (hAker (Subgroup.mem_subgroupOf.1 ha))
  have hA' : Nat.card A ≤ Nat.card ψ.ker := by
    have : Nat.card (A.subgroupOf E) = Nat.card A :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAE).toEquiv
    rw [← this]
    exact Subgroup.card_le_of_le hAle
  have hD' : 3 ^ (m + 1) ≤ Nat.card ψ.range :=
    (three_pow_le_card_closure h w hcomm hord hinv hfix).trans (Subgroup.card_le_of_le hDle)
  have hcardE := Subgroup.card_ker_mul_card_range ψ
  have hre : m + 1 + k ≤ e := by
    have h1 : 3 ^ (m + 1 + k) ≤ 3 ^ e := by
      rw [← he, ← hcardE, pow_add]
      calc 3 ^ (m + 1) * 3 ^ k ≤ Nat.card ψ.range * Nat.card ψ.ker :=
            Nat.mul_le_mul hD' (hk ▸ hA')
        _ = Nat.card ψ.ker * Nat.card ψ.range := mul_comm _ _
    exact (Nat.pow_le_pow_iff_right hp3.one_lt).1 h1
  have hEF : E ≤ D.comap π := by
    refine (Subgroup.closure_le _).2 ?_
    rintro s (⟨i, rfl⟩ | hs)
    · exact hmemF i
    · exact Subgroup.mem_comap.2 (by rw [MonoidHom.mem_ker.1 (hAker hs)]; exact D.one_mem)
  have hDN : D ≤ Subgroup.normalizer (U : Set S) :=
    (Subgroup.closure_le _).2 (by rintro _ ⟨i, rfl⟩; exact hN i)
  exact hre.trans (central_cover_elem_witness hπ hker hp3 hEe he hU1 hU2
    (fun x hx u hu => (Subgroup.mem_normalizer_iff.1 (hDN (hEF hx)) u).1 hu))

end CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.ExcRank
