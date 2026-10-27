module

public import CFSG.LocalAnalysis.GLTheoremA.S8.Lemma84Inputs
public import CFSG.LocalAnalysis.GLTheoremB.InputPiGenProof
public import CFSG.GroupTheory.PCore.PrimeSetCore
public import CFSG.Adapters.LinearCatalog
public import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

namespace S8.L84

private theorem a6f_sig_mem : (Equiv.swap (0 : Fin 6) 1 * Equiv.swap 1 2) ∈ alternatingGroup (Fin 6) := by
  rw [Equiv.Perm.mem_alternatingGroup]; decide

private theorem a6f_tau_mem : (Equiv.swap (0 : Fin 6) 1 * Equiv.swap 3 4) ∈ alternatingGroup (Fin 6) := by
  rw [Equiv.Perm.mem_alternatingGroup]; decide

private theorem a6f_aa_mem : (Equiv.swap (0 : Fin 6) 1 * Equiv.swap 2 3) ∈ alternatingGroup (Fin 6) := by
  rw [Equiv.Perm.mem_alternatingGroup]; decide

private theorem a6f_bb_mem : (Equiv.swap (0 : Fin 6) 2 * Equiv.swap 1 3) ∈ alternatingGroup (Fin 6) := by
  rw [Equiv.Perm.mem_alternatingGroup]; decide

private theorem a6f_cc_mem : (Equiv.swap (0 : Fin 6) 3 * Equiv.swap 1 2) ∈ alternatingGroup (Fin 6) := by
  rw [Equiv.Perm.mem_alternatingGroup]; decide

private theorem a6f_gg_mem : (Equiv.swap (0 : Fin 6) 3 * Equiv.swap 1 4) ∈ alternatingGroup (Fin 6) := by
  rw [Equiv.Perm.mem_alternatingGroup]; decide

private def a6s : alternatingGroup (Fin 6) := ⟨Equiv.swap 0 1 * Equiv.swap 1 2, a6f_sig_mem⟩
private def a6t : alternatingGroup (Fin 6) := ⟨Equiv.swap 0 1 * Equiv.swap 3 4, a6f_tau_mem⟩
private def a6g : alternatingGroup (Fin 6) := ⟨Equiv.swap 0 3 * Equiv.swap 1 4, a6f_gg_mem⟩
private def a6A : alternatingGroup (Fin 6) := ⟨Equiv.swap 0 1 * Equiv.swap 2 3, a6f_aa_mem⟩
private def a6B : alternatingGroup (Fin 6) := ⟨Equiv.swap 0 2 * Equiv.swap 1 3, a6f_bb_mem⟩
private def a6C : alternatingGroup (Fin 6) := ⟨Equiv.swap 0 3 * Equiv.swap 1 2, a6f_cc_mem⟩

private theorem a6f_rel_inv : a6t * a6s * a6t⁻¹ = a6s⁻¹ := by decide
private theorem a6f_rel_noncentral : a6g * a6s ≠ a6s * a6g := by decide
private theorem a6f_conj_sAs : a6s * a6A * a6s⁻¹ = a6C := by decide
private theorem a6f_conj_sCs : a6s * a6C * a6s⁻¹ = a6B := by decide
private theorem a6f_conj_sBs : a6s * a6B * a6s⁻¹ = a6A := by decide
private theorem a6f_conj_s'As : a6s⁻¹ * a6A * a6s = a6B := by decide
private theorem a6f_conj_s'Bs : a6s⁻¹ * a6B * a6s = a6C := by decide
private theorem a6f_conj_s'Cs : a6s⁻¹ * a6C * a6s = a6A := by decide

private def a6W : Subgroup (alternatingGroup (Fin 6)) where
  carrier := {x | x = 1 ∨ x = a6A ∨ x = a6B ∨ x = a6C}
  mul_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at *
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;> decide
  one_mem' := Or.inl rfl
  inv_mem' := by
    intro x hx
    simp only [Set.mem_setOf_eq] at *
    rcases hx with rfl | rfl | rfl | rfl <;> decide

private theorem a6W_card : Nat.card a6W = 4 := by
  have h : (a6W : Set (alternatingGroup (Fin 6))) = {1, a6A, a6B, a6C} := by
    ext x; exact Iff.rfl
  show Nat.card (a6W : Set (alternatingGroup (Fin 6))) = 4
  rw [Nat.card_coe_set_eq, h]
  have h1 : a6A ∉ ({a6B, a6C} : Set (alternatingGroup (Fin 6))) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]; decide
  have h2 : a6B ∉ ({a6C} : Set (alternatingGroup (Fin 6))) := by
    simp only [Set.mem_singleton_iff]; decide
  have h3 : (1 : alternatingGroup (Fin 6)) ∉ ({a6A, a6B, a6C} : Set (alternatingGroup (Fin 6))) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]; decide
  rw [Set.ncard_insert_of_notMem h3, Set.ncard_insert_of_notMem h1, Set.ncard_insert_of_notMem h2,
    Set.ncard_singleton]

private theorem a6f_orderOf_dvd_sixty (σ : Equiv.Perm (Fin 6)) : orderOf σ ∣ 60 := by
  rw [← σ.lcm_cycleType, Multiset.lcm_dvd]
  intro m hm
  have h1 : m ≤ σ.cycleType.sum := Multiset.le_sum_of_mem hm
  have h2 : σ.cycleType.sum ≤ Fintype.card (Fin 6) := σ.sum_cycleType_le
  rw [Fintype.card_fin] at h2
  have h3 : m ≤ 6 := h1.trans h2
  have h4 : 1 ≤ m := by
    have := Equiv.Perm.two_le_of_mem_cycleType hm
    omega
  interval_cases m <;> norm_num

private theorem a6f_isElemAbelian_of_card_nine (H : Subgroup (alternatingGroup (Fin 6)))
    (hH : Nat.card H = 9) : IsElemAbelian 3 H := by
  have hcomm : IsMulCommutative H := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hH]; norm_num)
  refine ⟨hcomm, ?_⟩
  intro x hx
  have h9 : orderOf (⟨x, hx⟩ : H) ∣ 9 := by
    have := orderOf_dvd_natCard (⟨x, hx⟩ : H)
    rwa [hH] at this
  have h60 : orderOf x ∣ 60 := by
    rw [← Subgroup.orderOf_coe x]
    exact a6f_orderOf_dvd_sixty _
  have hsame : orderOf (⟨x, hx⟩ : H) = orderOf x := (Subgroup.orderOf_coe (⟨x, hx⟩ : H)).symm
  have hdiv : orderOf x ∣ 3 := by
    have : orderOf x ∣ Nat.gcd 9 60 := Nat.dvd_gcd (hsame ▸ h9) h60
    simpa using this
  exact orderOf_dvd_iff_pow_eq_one.1 hdiv

private theorem a6f_isElemAbelian_map_iff {A B : Type} [Group A] [Group B] (p : ℕ) (φ : A →* B)
    (hφ : Function.Injective φ) (E : Subgroup A) :
    IsElemAbelian p (E.map φ) ↔ IsElemAbelian p E := by
  constructor
  · rintro ⟨hc, hx⟩
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => hφ ?_⟩
    · apply Subtype.ext
      apply hφ
      have h := hc.is_comm.comm ⟨φ a, Subgroup.mem_map_of_mem φ a.2⟩
        ⟨φ b, Subgroup.mem_map_of_mem φ b.2⟩
      have h' := congrArg Subtype.val h
      simpa [map_mul] using h'
    · simpa using hx (φ a) (Subgroup.mem_map_of_mem φ ha)
  · rintro ⟨hc, hx⟩
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx' => ?_⟩
    · obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.1 x.2
      obtain ⟨b, hb, hby⟩ := Subgroup.mem_map.1 y.2
      apply Subtype.ext
      have hab : a * b = b * a := congrArg Subtype.val (hc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
      simp only [Subgroup.coe_mul, Submonoid.coe_mul]
      rw [← hax, ← hby, ← map_mul, ← map_mul, hab]
    · obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.1 hx'
      rw [← hax, ← map_pow, hx a ha, map_one]


private theorem a6f_s_cube : a6s ^ 3 = 1 := by decide
private theorem a6f_s_ne_one : a6s ≠ 1 := by decide

private theorem a6W_conj_mem (x : alternatingGroup (Fin 6)) (hx : x ∈ a6W) :
    a6s * x * a6s⁻¹ ∈ a6W := by
  have hx' : x = 1 ∨ x = a6A ∨ x = a6B ∨ x = a6C := hx
  show a6s * x * a6s⁻¹ = 1 ∨ _
  rcases hx' with rfl | rfl | rfl | rfl
  · exact Or.inl (by group)
  · rw [a6f_conj_sAs]; exact Or.inr (Or.inr (Or.inr rfl))
  · rw [a6f_conj_sBs]; exact Or.inr (Or.inl rfl)
  · rw [a6f_conj_sCs]; exact Or.inr (Or.inr (Or.inl rfl))

private theorem a6W_conj_inv_mem (x : alternatingGroup (Fin 6)) (hx : x ∈ a6W) :
    a6s⁻¹ * x * a6s ∈ a6W := by
  have hx' : x = 1 ∨ x = a6A ∨ x = a6B ∨ x = a6C := hx
  show a6s⁻¹ * x * a6s = 1 ∨ _
  rcases hx' with rfl | rfl | rfl | rfl
  · exact Or.inl (by group)
  · rw [a6f_conj_s'As]; exact Or.inr (Or.inr (Or.inl rfl))
  · rw [a6f_conj_s'Bs]; exact Or.inr (Or.inr (Or.inr rfl))
  · rw [a6f_conj_s'Cs]; exact Or.inr (Or.inl rfl)

private theorem a6W_conj_iff (x : alternatingGroup (Fin 6)) :
    a6s * x * a6s⁻¹ ∈ a6W ↔ x ∈ a6W := by
  constructor
  · intro hx
    have := a6W_conj_inv_mem _ hx
    simpa [mul_assoc] using this
  · exact a6W_conj_mem x

private theorem a6f_abstract_a {K : Type} [Group K] [Finite K]
    (π : K →* alternatingGroup (Fin 6)) (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center K) (hodd : Odd (Nat.card π.ker)) :
    ∃ n : K, orderOf n = 3 ∧ (∃ w : K, w * n ≠ n * w) ∧
      ∃ P : Subgroup K, Nat.card P = 4 ∧ n ∈ Subgroup.normalizer (P : Set K) := by
  classical
  have hZc : ∀ z ∈ π.ker, ∀ g : K, g * z = z * g := fun z hz g =>
    (Subgroup.mem_center_iff.1 (hcen hz)) g
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = Nat.card π.ker := ⟨_, rfl⟩
  rw [← hN] at hodd
  have hZpow : ∀ z ∈ π.ker, z ^ N = 1 := by
    intro z hz
    have h1 := congrArg Subtype.val (pow_card_eq_one' (x := (⟨z, hz⟩ : π.ker)))
    rw [← hN] at h1
    simpa using h1
  obtain ⟨k, hk⟩ := hodd
  have h2s : 2 * (k + 1) = N + 1 := by omega
  obtain ⟨σ, hσ⟩ := hπ a6s
  obtain ⟨h, hh⟩ := hπ a6t
  obtain ⟨z₀, hz₀def⟩ : ∃ z₀ : K, z₀ = σ * (h * σ * h⁻¹) := ⟨_, rfl⟩
  have hπz₀ : π z₀ = 1 := by
    rw [hz₀def]
    simp only [map_mul, map_inv, hσ, hh, a6f_rel_inv, mul_inv_cancel]
  have hz₀Z : z₀ ∈ π.ker := hπz₀
  have hR1 : h * σ * h⁻¹ = σ⁻¹ * z₀ := by
    rw [hz₀def]; group
  have hcZ : σ ^ 3 ∈ π.ker := by
    show π (σ ^ 3) = 1
    rw [map_pow, hσ, a6f_s_cube]
  have hc2 : σ ^ 3 * σ ^ 3 = z₀ ^ 3 := by
    have e1 : h * σ ^ 3 * h⁻¹ = σ ^ 3 := by
      rw [hZc _ hcZ h, mul_assoc, mul_inv_cancel, mul_one]
    have e2 : h * σ ^ 3 * h⁻¹ = (σ⁻¹ * z₀) ^ 3 := by
      rw [← hR1, conj_pow]
    have hcomm : Commute σ⁻¹ z₀ := hZc z₀ hz₀Z σ⁻¹
    have e3 : (σ⁻¹ * z₀) ^ 3 = (σ ^ 3)⁻¹ * z₀ ^ 3 := by
      rw [hcomm.mul_pow, inv_pow]
    have hfix : σ ^ 3 = (σ ^ 3)⁻¹ * z₀ ^ 3 := by
      calc σ ^ 3 = h * σ ^ 3 * h⁻¹ := e1.symm
        _ = (σ⁻¹ * z₀) ^ 3 := e2
        _ = (σ ^ 3)⁻¹ * z₀ ^ 3 := e3
    calc σ ^ 3 * σ ^ 3 = σ ^ 3 * ((σ ^ 3)⁻¹ * z₀ ^ 3) := by rw [← hfix]
      _ = z₀ ^ 3 := by group
  have hcpow : σ ^ 3 = z₀ ^ (3 * (k + 1)) := by
    have h1 : (σ ^ 3) ^ (N + 1) = σ ^ 3 := by rw [pow_succ, hZpow _ hcZ, one_mul]
    rw [← h1, ← h2s, pow_mul, pow_two, hc2, ← pow_mul]
  obtain ⟨u, hu⟩ : ∃ u : K, u = z₀⁻¹ ^ (k + 1) := ⟨_, rfl⟩
  have hu_comm : Commute σ u := by
    rw [hu]
    apply Commute.pow_right
    exact hZc z₀⁻¹ (π.ker.inv_mem hz₀Z) σ
  obtain ⟨n, hn⟩ : ∃ n : K, n = σ * u := ⟨_, rfl⟩
  have hπn : π n = a6s := by
    rw [hn, map_mul, hσ, hu, map_pow, map_inv, hπz₀, inv_one, one_pow, mul_one]
  have hn3 : n ^ 3 = 1 := by
    have hu3 : u ^ 3 = (z₀ ^ (3 * (k + 1)))⁻¹ := by
      rw [hu, ← pow_mul, mul_comm (k + 1) 3, inv_pow]
    rw [hn, hu_comm.mul_pow, hcpow, hu3, mul_inv_cancel]
  have hn1 : n ≠ 1 := by
    intro h1
    apply a6f_s_ne_one
    rw [← hπn, h1, map_one]
  have hord : orderOf n = 3 := orderOf_eq_prime hn3 hn1
  refine ⟨n, hord, ?_, ?_⟩
  · by_contra hcon
    push Not at hcon
    obtain ⟨w, hw⟩ := hπ a6g
    have hwn := congrArg π (hcon w)
    rw [map_mul, map_mul, hw, hπn] at hwn
    exact a6f_rel_noncentral hwn
  obtain ⟨V', hV'⟩ : ∃ V' : Subgroup K, V' = a6W.comap π := ⟨_, rfl⟩
  have hmemV' : ∀ x : K, x ∈ V' ↔ π x ∈ a6W := by
    intro x; rw [hV', Subgroup.mem_comap]
  have hV'card : 4 ∣ Nat.card V' := by
    have hsurj : Function.Surjective ((π.comp V'.subtype).codRestrict a6W
        (fun x => (hmemV' x).1 x.2)) := by
      intro w
      obtain ⟨x, hx⟩ := hπ w.1
      refine ⟨⟨x, (hmemV' x).2 (by rw [hx]; exact w.2)⟩, Subtype.ext ?_⟩
      exact hx
    have := Subgroup.card_dvd_of_surjective hsurj
    rwa [a6W_card] at this
  obtain ⟨P', hP'⟩ := Sylow.exists_subgroup_card_pow_prime 2 (n := 2)
    (by norm_num; exact hV'card)
  obtain ⟨P, hP⟩ : ∃ P : Subgroup K, P = P'.map V'.subtype := ⟨_, rfl⟩
  have hPV : P ≤ V' := by
    rw [hP]
    rintro _ ⟨x, _, rfl⟩
    exact x.2
  have hPcard : Nat.card P = 4 := by
    rw [hP, Subgroup.card_map_of_injective V'.subtype_injective, hP']
    norm_num
  have hP4 : ∀ x ∈ P, x ^ 4 = 1 := by
    intro x hx
    have h1 := congrArg Subtype.val (pow_card_eq_one' (x := (⟨x, hx⟩ : P)))
    rw [hPcard] at h1
    simpa using h1
  have hcop : Nat.gcd 4 N = 1 := by
    have : Nat.Coprime 2 N := Nat.coprime_two_left.2 ⟨k, hk⟩
    have h4 := Nat.Coprime.pow_left 2 this
    norm_num at h4
    exact h4
  have hinjOn : Set.InjOn π (P : Set K) := by
    intro x hx y hy hxy
    have hxy' : x⁻¹ * y ∈ P := P.mul_mem (P.inv_mem hx) hy
    have hz : π (x⁻¹ * y) = 1 := by
      rw [map_mul, map_inv, hxy, inv_mul_cancel]
    have hzZ : x⁻¹ * y ∈ π.ker := hz
    have h4 := hP4 _ hxy'
    have h1 := (pow_gcd_eq_one (a := x⁻¹ * y) (m := 4) (n := N)).2 ⟨h4, hZpow _ hzZ⟩
    rw [hcop, pow_one, inv_mul_eq_one] at h1
    exact h1
  have hcardmap : Nat.card ↥(P.map π) = Nat.card ↥P := by
    have h := Nat.card_image_of_injOn hinjOn
    rw [← Subgroup.coe_map] at h
    exact h
  have hPW : P.map π = a6W := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨x, hx, rfl⟩
      exact (hmemV' x).1 (hPV hx)
    · rw [hcardmap, hPcard, a6W_card]
  have hchar : ∀ x ∈ V', x ^ 4 = 1 → x ∈ P := by
    intro x hxV hx4
    have hx' : π x ∈ P.map π := by
      rw [hPW]; exact (hmemV' x).1 hxV
    obtain ⟨p, hp, hpx⟩ := Subgroup.mem_map.1 hx'
    obtain ⟨z, hz⟩ : ∃ z : K, z = p⁻¹ * x := ⟨_, rfl⟩
    have hπz : π z = 1 := by
      rw [hz, map_mul, map_inv, hpx, inv_mul_cancel]
    have hzZ : z ∈ π.ker := hπz
    have hxpz : x = p * z := by rw [hz]; group
    have hcomm : Commute p z := hZc z hzZ p
    have hz4 : z ^ 4 = 1 := by
      have h1 : x ^ 4 = (p * z) ^ 4 := by rw [hxpz]
      rw [hcomm.mul_pow, hP4 p hp, one_mul] at h1
      rw [← h1]; exact hx4
    have hz1 : z = 1 := by
      have := (pow_gcd_eq_one (a := z) (m := 4) (n := N)).2 ⟨hz4, hZpow z hzZ⟩
      rw [hcop, pow_one] at this
      exact this
    rw [hxpz, hz1, mul_one]
    exact hp
  refine ⟨P, hPcard, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro y
    have hmem : ∀ t : K, t ∈ P ↔ t ∈ V' ∧ t ^ 4 = 1 := by
      intro t
      constructor
      · intro ht
        exact ⟨hPV ht, hP4 t ht⟩
      · rintro ⟨htV, ht4⟩
        exact hchar t htV ht4
    have hconjV : n * y * n⁻¹ ∈ V' ↔ y ∈ V' := by
      rw [hmemV', hmemV', map_mul, map_mul, map_inv, hπn]
      exact a6W_conj_iff (π y)
    have hconj4 : (n * y * n⁻¹) ^ 4 = 1 ↔ y ^ 4 = 1 := by
      rw [conj_pow, conj_eq_one_iff]
    show y ∈ P ↔ n * y * n⁻¹ ∈ P
    rw [hmem y, hmem (n * y * n⁻¹), hconjV, hconj4]


private theorem a6f_lie_alt6 (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.A 1 q).Valid)
    (hq : q.card = 9) :
    Nonempty (TauCeti.ValidLieTypeIndex.Group ⟨TauCeti.LieTypeIndex.A 1 q, hv⟩ ≃*
      alternatingGroup (Fin 6)) := by
  haveI : Fact (Nat.Prime q.p) := ⟨q.prime_p⟩
  obtain ⟨e1⟩ : Nonempty (TauCeti.ValidLieTypeIndex.Group ⟨TauCeti.LieTypeIndex.A 1 q, hv⟩ ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField q.p q.exponent)) :=
    ⟨CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hv⟩
  have hcard : Nat.card (GaloisField q.p q.exponent) = 9 := by
    rw [GaloisField.card q.p q.exponent (Nat.pos_iff_ne_zero.1 q.exponent_pos)]
    rw [← hq, TauCeti.PrimePower.card_def]
  haveI : Fintype (GaloisField q.p q.exponent) := Fintype.ofFinite _
  obtain ⟨e2⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.unique_field_nine_projective_linear_alternating_six_isomorphism
      (GaloisField q.p q.exponent) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  exact ⟨e1.trans e2⟩

private theorem a6f_alt6_of_isA6 (i : TauCeti.CFSGIndex) (hi : isA6 i) :
    Nonempty (i.Group ≃* alternatingGroup (Fin 6)) := by
  rcases hi with hi | hi
  · cases i with
    | alternating n h =>
      have hn : n = 6 := hi
      subst hn
      exact ⟨MulEquiv.refl _⟩
    | _ => exact False.elim hi
  · cases i with
    | lie d =>
      obtain ⟨d₁, hv⟩ := d
      cases d₁ with
      | A r q =>
        match r, hv, hi with
        | 1, hv, hi => exact a6f_lie_alt6 q hv hi
        | 0, _, hi => exact False.elim hi
        | r + 2, _, hi => exact False.elim hi
      | _ => exact False.elim hi
    | _ => exact False.elim hi

noncomputable def a6f_iso {G : Type} [Group G] [Finite G] {X J : Subgroup G}
    (hJ : GLAPComponent 3 X J) : PQuot 3 J ≃* ↥(barX 3 X J) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_barMap_eq Nat.prime_three hJ.1 hJ.2.1).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (barMap_surjective hJ.1))

private theorem a6f_center_odd {G : Type} [Group G] [Finite G] (J : Subgroup G) :
    Odd (Nat.card (Subgroup.center (PQuot 3 J))) :=
  odd_card_center Nat.prime_three (by norm_num) (CFSG.pPrimeCore_quotient_eq_bot Nat.prime_three)

private theorem a6f_psimple {G : Type} [Group G] [Finite G] {J : Subgroup G}
    (hA : catalogIs (PSimple 3 J) isA6) : Nonempty (PSimple 3 J ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := hA
  obtain ⟨e'⟩ := a6f_alt6_of_isA6 i hi
  exact ⟨e.trans e'⟩

private theorem a6f_quot_hom {K : Type} [Group K] [Finite K]
    (eA : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin 6))
    (hodd : Odd (Nat.card (Subgroup.center K))) :
    ∃ ψ : K →* alternatingGroup (Fin 6), Function.Surjective ψ ∧ ψ.ker ≤ Subgroup.center K ∧
      Odd (Nat.card ψ.ker) := by
  have hker : (eA.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))).ker =
      Subgroup.center K := by
    ext z
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff _ eA.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  refine ⟨eA.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K)),
    eA.surjective.comp (QuotientGroup.mk'_surjective _), hker.le, ?_⟩
  rw [hker]
  exact hodd

private theorem a6f_partA {G : Type} [Group G] [Finite G] {X J : Subgroup G}
    (hJ : GLAPComponent 3 X J) (hA : catalogIs (PSimple 3 J) isA6) :
    ∃ y ∈ barX 3 X J, orderOf y = 3 ∧ (∃ z ∈ barX 3 X J, z * y ≠ y * z) ∧
      ∃ T : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X), T ≤ barX 3 X J ∧ T ≠ ⊥ ∧ IsPGroup 2 T ∧
        y ∈ Subgroup.normalizer (T : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) := by
  obtain ⟨eA⟩ := a6f_psimple hA
  obtain ⟨ψ, hψs, hψc, hψo⟩ := a6f_quot_hom eA (a6f_center_odd J)
  obtain ⟨n₀, hord₀, ⟨w₀, hw₀⟩, P₀, hP₀, hn₀⟩ := a6f_abstract_a ψ hψs hψc hψo
  set Φ := a6f_iso hJ
  set Ψ : PQuot 3 J →* (↥X ⧸ GLAPPrimeCore 3 ↥X) :=
    (barX 3 X J).subtype.comp Φ.toMonoidHom with hΨ
  have hΨinj : Function.Injective Ψ := fun a b hab => Φ.injective (Subtype.ext hab)
  refine ⟨Ψ n₀, (Φ n₀).2, ?_, ?_, ?_⟩
  · exact (orderOf_injective Ψ hΨinj n₀).trans hord₀
  · refine ⟨Ψ w₀, (Φ w₀).2, ?_⟩
    intro h
    apply hw₀
    apply hΨinj
    rw [map_mul, map_mul]
    exact h
  · refine ⟨P₀.map Ψ, ?_, ?_, ?_, ?_⟩
    · rintro _ ⟨t, _, rfl⟩
      exact (Φ t).2
    · intro hbot
      have h4 : Nat.card (P₀.map Ψ) = 4 := by
        rw [Subgroup.card_map_of_injective hΨinj, hP₀]
      rw [hbot, Subgroup.card_bot] at h4
      norm_num at h4
    · exact IsPGroup.of_card (n := 2) (by rw [Subgroup.card_map_of_injective hΨinj, hP₀]; norm_num)
    · rw [Subgroup.mem_normalizer_iff]
      intro q
      constructor
      · intro hq
        obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hq
        apply Subgroup.mem_map.2
        refine ⟨n₀ * t * n₀⁻¹, (Subgroup.mem_normalizer_iff.1 hn₀ t).1 ht, ?_⟩
        rw [map_mul, map_mul, map_inv]
      · intro hq
        obtain ⟨t, ht, htq⟩ := Subgroup.mem_map.1 hq
        apply Subgroup.mem_map.2
        refine ⟨n₀⁻¹ * t * n₀, ?_, ?_⟩
        · refine (Subgroup.mem_normalizer_iff.1 hn₀ (n₀⁻¹ * t * n₀)).2 ?_
          have e : n₀ * (n₀⁻¹ * t * n₀) * n₀⁻¹ = t := by group
          rw [e]
          exact ht
        · rw [map_mul, map_mul, map_inv, htq]
          group

private theorem a6f_elemAbelian_of_injOn {J B : Type} [Group J] [Group B] (p : ℕ)
    (f : J →* B) (P : Subgroup J) (hinj : Set.InjOn f (P : Set J))
    (h : IsElemAbelian p (P.map f)) : IsElemAbelian p P := by
  obtain ⟨hc, hx⟩ := h
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩
  · apply Subtype.ext
    apply hinj (P.mul_mem a.2 b.2) (P.mul_mem b.2 a.2)
    have h1 := hc.is_comm.comm ⟨f a, Subgroup.mem_map_of_mem f a.2⟩
      ⟨f b, Subgroup.mem_map_of_mem f b.2⟩
    have h2 := congrArg Subtype.val h1
    simpa [map_mul] using h2
  · apply hinj (P.pow_mem ha p) (P.one_mem)
    rw [map_pow, map_one]
    exact hx _ (Subgroup.mem_map_of_mem f ha)

private theorem a6f_elemAbelian_of_sup {J : Type} [Group J] [Finite J]
    (f : J →* alternatingGroup (Fin 6)) (hf : Function.Surjective f)
    (O : Subgroup J) [O.Normal] (hO : f.ker = O) (h3 : ¬ 3 ∣ Nat.card O)
    (S : Subgroup J) (hS : S ⊔ O = ⊤) :
    ∃ F : Subgroup J, F ≤ S ∧ IsElemAbelian 3 F ∧ Nat.card F = 3 ^ 2 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hgs : Function.Surjective (f.comp S.subtype) := by
    intro a
    obtain ⟨x, hx⟩ := hf a
    have hxS : x ∈ S ⊔ O := by rw [hS]; exact Subgroup.mem_top x
    obtain ⟨s, hs, o, ho, hso⟩ := (Subgroup.mem_sup_of_normal_right).1 hxS
    refine ⟨⟨s, hs⟩, ?_⟩
    have hfo : f o = 1 := by
      rw [← MonoidHom.mem_ker, hO]; exact ho
    show f s = a
    rw [← hx, ← hso, map_mul, hfo, mul_one]
  have hA6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have hcardS := Subgroup.card_ker_mul_card_of_surjective hgs
  rw [hA6] at hcardS
  have h9 : 3 ^ 2 ∣ Nat.card S := by
    rw [← hcardS]
    exact Dvd.dvd.mul_left (by norm_num) _
  obtain ⟨P', hP'⟩ := Sylow.exists_subgroup_card_pow_prime 3 (n := 2) h9
  obtain ⟨P, hP⟩ : ∃ P : Subgroup J, P = P'.map S.subtype := ⟨_, rfl⟩
  have hPS : P ≤ S := by
    rw [hP]
    rintro _ ⟨x, _, rfl⟩
    exact x.2
  have hPcard : Nat.card P = 3 ^ 2 := by
    rw [hP, Subgroup.card_map_of_injective S.subtype_injective, hP']
  have hP9 : ∀ x ∈ P, x ^ 3 ^ 2 = 1 := by
    intro x hx
    have h1 := congrArg Subtype.val (pow_card_eq_one' (x := (⟨x, hx⟩ : P)))
    rw [hPcard] at h1
    simpa using h1
  have hcop : Nat.gcd (3 ^ 2) (Nat.card O) = 1 := by
    have : Nat.Coprime 3 (Nat.card O) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3
    exact Nat.Coprime.pow_left 2 this
  have hinjOn : Set.InjOn f (P : Set J) := by
    intro x hx y hy hxy
    have hxy' : x⁻¹ * y ∈ P := P.mul_mem (P.inv_mem hx) hy
    have hf1 : f (x⁻¹ * y) = 1 := by rw [map_mul, map_inv, hxy, inv_mul_cancel]
    have hzO : x⁻¹ * y ∈ O := by
      rw [← hO]; exact hf1
    have hOpow : (x⁻¹ * y) ^ Nat.card O = 1 :=
      congrArg Subtype.val (pow_card_eq_one' (x := (⟨x⁻¹ * y, hzO⟩ : O)))
    have h1 := (pow_gcd_eq_one (a := x⁻¹ * y) (m := 3 ^ 2) (n := Nat.card O)).2
      ⟨hP9 _ hxy', hOpow⟩
    rw [hcop, pow_one, inv_mul_eq_one] at h1
    exact h1
  have hcardmap : Nat.card ↥(P.map f) = 3 ^ 2 := by
    have h := Nat.card_image_of_injOn hinjOn
    rw [← Subgroup.coe_map] at h
    exact h.trans hPcard
  have hPab : IsElemAbelian 3 (P.map f) := a6f_isElemAbelian_of_card_nine _ hcardmap
  exact ⟨P, hPS, a6f_elemAbelian_of_injOn 3 f P hinjOn hPab, hPcard⟩

private theorem a6f_partB {G : Type} [Group G] [Finite G] {X J : Subgroup G}
    (hJ : GLAPComponent 3 X J) (hA : catalogIs (PSimple 3 J) isA6) :
    Nat.card (Subgroup.center (PQuot 3 J)) = 1 → ∀ J₀ : Subgroup G, J₀ ≤ J →
      J₀ ⊔ GLAPPrimeCoreOf 3 J = J → ∃ F : Subgroup G, F ≤ J₀ ∧ IsElemAbelian 3 F ∧
        Nat.card F = 3 ^ 2 := by
  intro hc J₀ hJ₀ hsup
  obtain ⟨eA⟩ := a6f_psimple hA
  have hcb : Subgroup.center (PQuot 3 J) = ⊥ := Subgroup.eq_bot_of_card_eq _ hc
  let ec : PSimple 3 J ≃* PQuot 3 J :=
    (QuotientGroup.quotientMulEquivOfEq hcb).trans QuotientGroup.quotientBot
  let eK : PQuot 3 J ≃* alternatingGroup (Fin 6) := ec.symm.trans eA
  let f : ↥J →* alternatingGroup (Fin 6) :=
    eK.toMonoidHom.comp (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J))
  have hf : Function.Surjective f := eK.surjective.comp (QuotientGroup.mk'_surjective _)
  have hfker : f.ker = GLAPPrimeCore 3 ↥J := by
    ext x
    simp only [f, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff _ eK.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hO3 : ¬ 3 ∣ Nat.card (GLAPPrimeCore 3 ↥J) := by
    have h := not_dvd_card_glaPPrimeCoreOf Nat.prime_three J
    rw [GLAPPrimeCoreOf, Subgroup.card_map_of_injective J.subtype_injective] at h
    exact h
  have hSO : (J₀.subgroupOf J) ⊔ GLAPPrimeCore 3 ↥J = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : (x : G) ∈ J₀ ⊔ GLAPPrimeCoreOf 3 J := by rw [hsup]; exact x.2
    have key : J₀ ⊔ GLAPPrimeCoreOf 3 J ≤
        ((J₀.subgroupOf J) ⊔ GLAPPrimeCore 3 ↥J).map J.subtype := by
      apply sup_le
      · intro g hg
        exact ⟨⟨g, hJ₀ hg⟩, Subgroup.mem_sup_left ((Subgroup.mem_subgroupOf).2 hg), rfl⟩
      · rintro _ ⟨o, ho, rfl⟩
        exact ⟨o, Subgroup.mem_sup_right ho, rfl⟩
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 (key hx)
    have hyx' : y = x := Subtype.ext hyx
    rw [← hyx']
    exact hy
  obtain ⟨F', hF'S, hF'ab, hF'card⟩ :=
    a6f_elemAbelian_of_sup f hf (GLAPPrimeCore 3 ↥J) hfker hO3 (J₀.subgroupOf J) hSO
  refine ⟨F'.map J.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact (Subgroup.mem_subgroupOf).1 (hF'S hx)
  · exact (a6f_isElemAbelian_map_iff 3 J.subtype Subtype.val_injective F').2 hF'ab
  · rw [Subgroup.card_map_of_injective J.subtype_injective, hF'card]

theorem a6FactsAt_holds (G : Type) [Group G] [Finite G] : A6FactsAt G := by
  unfold A6FactsAt
  intro X J hJ hA
  exact ⟨a6f_partA hJ hA, a6f_partB hJ hA⟩


end S8.L84

end CFSG.LocalAnalysis.GLTheoremA

end
