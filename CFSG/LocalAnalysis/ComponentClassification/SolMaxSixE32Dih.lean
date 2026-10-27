module

public import CFSG.ClassicalInvolution.TwoGroupCase.FourGroupCentralizer

public section

namespace CFSG.ComponentClassification.SolMax.Sig36.E32

open Subgroup
open scoped Pointwise

variable {X : Type} [Group X] [Finite X]

private theorem isPGroup_zpowers_two {a : X} (ha : a * a = 1) : IsPGroup 2 (zpowers a) := by
  have hdvd : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact ha)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])

private theorem isPGroup_sup_zpowers_two {P : Subgroup X} {x : X} (hP : IsPGroup 2 P)
    (hx : IsPGroup 2 (zpowers x)) (hPx : P ≤ centralizer ({x} : Set X)) :
    IsPGroup 2 (P ⊔ zpowers x : Subgroup X) := by
  refine IsPGroup.to_sup_of_normal_right' hP hx
    (le_trans ?_ (Subgroup.centralizer_le_normalizer _))
  intro y hy
  rw [mem_centralizer_iff]
  intro h hh
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hh
  have hxy : Commute x y := (mem_centralizer_singleton_iff.mp (hPx hy)).symm
  exact (hxy.zpow_left k).eq

private theorem exists_conj_le_sylow {H Sc B : Subgroup X} (hSH : Sc ≤ H)
    (hScard : Nat.card Sc = 2 ^ (Nat.card H).factorization 2) (hBH : B ≤ H)
    (hB2 : IsPGroup 2 B) : ∃ h ∈ H, ∀ b ∈ B, h * b * h⁻¹ ∈ Sc := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS₁ : Nat.card (Sc.subgroupOf H) = 2 ^ (Nat.card H).factorization 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hSH).toEquiv, hScard]
  have hB₁ : IsPGroup 2 (B.subgroupOf H) := hB2.of_equiv (subgroupOfEquivOfLe hBH).symm
  obtain ⟨T, hT⟩ := hB₁.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq H T (Sylow.ofCard _ hS₁)
  refine ⟨h, h.2, fun b hb => ?_⟩
  have key : ((h • T : Sylow 2 H) : Subgroup H) = Sc.subgroupOf H := by
    rw [hh, Sylow.coe_ofCard]
  rw [Sylow.coe_subgroup_smul] at key
  have h1 : MulAut.conj h • (⟨b, hBH hb⟩ : H) ∈ MulAut.conj h • (T : Subgroup H) :=
    Subgroup.smul_mem_pointwise_smul _ _ _ (hT (show (⟨b, hBH hb⟩ : H) ∈ B.subgroupOf H from hb))
  rw [key] at h1
  simpa [MulAut.smul_def, MulAut.conj_apply, mem_subgroupOf] using h1

private theorem mem_sup_zpowers_iff {N : Subgroup X} {s : X} (hs2 : s * s = 1)
    (hsN : s ∈ normalizer (N : Set X)) (u : X) :
    u ∈ N ⊔ zpowers s ↔ u ∈ N ∨ u * s ∈ N := by
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have hc : ∀ n ∈ N, s * n * s ∈ N := by
    intro n hn
    have := (mem_normalizer_iff.mp hsN n).mp hn
    rwa [hsi] at this
  constructor
  · intro hu
    let T : Subgroup X :=
      { carrier := {u | u ∈ N ∨ u * s ∈ N}
        mul_mem' := by
          rintro a b (ha | ha) (hb | hb)
          · exact Or.inl (N.mul_mem ha hb)
          · exact Or.inr (by rw [mul_assoc]; exact N.mul_mem ha hb)
          · refine Or.inr ?_
            have e : (a * s) * (s * b * s) = a * b * s := by
              calc (a * s) * (s * b * s) = a * (s * s) * b * s := by simp only [mul_assoc]
                _ = a * b * s := by rw [hs2, mul_one]
            rw [← e]
            exact N.mul_mem ha (hc b hb)
          · refine Or.inl ?_
            have e : (a * s) * (s * (b * s) * s) = a * b := by
              calc (a * s) * (s * (b * s) * s) = a * (s * s) * b * (s * s) := by
                    simp only [mul_assoc]
                _ = a * b := by rw [hs2]; simp
            rw [← e]
            exact N.mul_mem ha (hc _ hb)
        one_mem' := Or.inl N.one_mem
        inv_mem' := by
          rintro a (ha | ha)
          · exact Or.inl (N.inv_mem ha)
          · refine Or.inr ?_
            have e : s * (a * s)⁻¹ * s = a⁻¹ * s := by group
            rw [← e]
            exact hc _ (N.inv_mem ha) }
    have hle : N ⊔ zpowers s ≤ T := by
      refine sup_le (fun n hn => Or.inl hn) (zpowers_le.mpr (Or.inr ?_))
      rw [hs2]
      exact N.one_mem
    exact hle hu
  · rintro (h | h)
    · exact mem_sup_left h
    · have : u = (u * s) * s := by rw [mul_assoc, hs2, mul_one]
      rw [this]
      exact mul_mem (mem_sup_left h) (mem_sup_right (mem_zpowers s))

private theorem index_subgroupOf_sup_zpowers {N : Subgroup X} {s : X} (hs2 : s * s = 1)
    (hsN : s ∈ normalizer (N : Set X)) (hsn : s ∉ N) :
    (N.subgroupOf (N ⊔ zpowers s)).index = 2 := by
  have hsG : s ∈ N ⊔ zpowers s := mem_sup_right (mem_zpowers s)
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨s, hsG⟩, fun b => ?_⟩
  have hb := (mem_sup_zpowers_iff hs2 hsN b.1).mp b.2
  simp only [mem_subgroupOf, Subgroup.coe_mul]
  rcases hb with hb | hb
  · refine Or.inr ⟨hb, fun h => hsn ?_⟩
    have := N.mul_mem (N.inv_mem hb) h
    simpa using this
  · refine Or.inl ⟨hb, fun h => hsn ?_⟩
    have := N.mul_mem (N.inv_mem h) hb
    simpa using this

private theorem card_sup_zpowers {N : Subgroup X} {s : X} (hs2 : s * s = 1)
    (hsN : s ∈ normalizer (N : Set X)) (hsn : s ∉ N) :
    Nat.card (N ⊔ zpowers s : Subgroup X) = 2 * Nat.card N := by
  have h := Subgroup.card_mul_index (N.subgroupOf (N ⊔ zpowers s))
  rw [index_subgroupOf_sup_zpowers hs2 hsN hsn,
    Nat.card_congr (subgroupOfEquivOfLe (le_sup_left (b := zpowers s))).toEquiv] at h
  omega

private theorem card_eq_pow_of_max {Y Q : Subgroup X} (hQY : Q ≤ Y) (hQ2 : IsPGroup 2 Q)
    (hQmax : ∀ P : Subgroup X, P ≤ Y → IsPGroup 2 P → Nat.card P ≤ Nat.card Q) :
    Nat.card Q = 2 ^ (Nat.card Y).factorization 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 Y) := inferInstance
  set P' : Subgroup X := (P : Subgroup Y).map Y.subtype with hP'
  have hP'le : P' ≤ Y := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hP'2 : IsPGroup 2 P' := P.isPGroup'.map Y.subtype
  have hP'card : Nat.card P' = 2 ^ (Nat.card Y).factorization 2 := by
    rw [hP', Subgroup.card_map_of_injective Y.subtype_injective, Sylow.card_eq_multiplicity]
  have h1 := hQmax P' hP'le hP'2
  rw [hP'card] at h1
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp hQ2
  have hdvd : 2 ^ k ∣ Nat.card Y := by
    rw [← hk]
    exact Subgroup.card_dvd_of_le hQY
  have hkle := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp hdvd
  have h2 : Nat.card Q ≤ 2 ^ (Nat.card Y).factorization 2 := by
    rw [hk]
    exact Nat.pow_le_pow_right (by norm_num) hkle
  exact le_antisymm h2 h1

private theorem factorization_two_mul {n : ℕ} (hn : n ≠ 0) :
    (2 * n).factorization 2 = n.factorization 2 + 1 := by
  rw [Nat.factorization_mul two_ne_zero hn, Finsupp.add_apply,
    Nat.Prime.factorization_self Nat.prime_two]
  ring

private theorem exists_conj_into {Y Q : Subgroup X} {s : X}
    (hs2 : s * s = 1) (hsY : s ∉ Y) (hYs : s ∈ normalizer (Y : Set X))
    (hQY : Q ≤ Y) (hQ2 : IsPGroup 2 Q) (hsQ : s ∈ normalizer (Q : Set X))
    (hQmax : ∀ P : Subgroup X, P ≤ Y → IsPGroup 2 P → Nat.card P ≤ Nat.card Q)
    {B : Subgroup X} (hBG : B ≤ Y ⊔ zpowers s) (hB2 : IsPGroup 2 B) :
    ∃ c ∈ Y ⊔ zpowers s, ∀ b ∈ B, c * b * c⁻¹ ∈ Q ⊔ zpowers s := by
  have hsQ' : s ∉ Q := fun h => hsY (hQY h)
  have hDG : Q ⊔ zpowers s ≤ Y ⊔ zpowers s := sup_le_sup_right hQY _
  have hQcard := card_eq_pow_of_max hQY hQ2 hQmax
  have hDcard : Nat.card (Q ⊔ zpowers s : Subgroup X) =
      2 ^ (Nat.card (Y ⊔ zpowers s : Subgroup X)).factorization 2 := by
    rw [card_sup_zpowers hs2 hsQ hsQ', card_sup_zpowers hs2 hYs hsY,
      factorization_two_mul Nat.card_pos.ne', hQcard, pow_succ]
    ring
  exact exists_conj_le_sylow hDG hDcard hBG hB2

theorem fusion_core {Y Q : Subgroup X} {s : X}
    (hs2 : s * s = 1) (hsY : s ∉ Y) (hYs : s ∈ normalizer (Y : Set X))
    (hQY : Q ≤ Y) (hQ2 : IsPGroup 2 Q) (hsQ : s ∈ normalizer (Q : Set X))
    (hQmax : ∀ P : Subgroup X, P ≤ Y → IsPGroup 2 P → Nat.card P ≤ Nat.card Q)
    (hB : ∀ u ∈ Q ⊔ zpowers s, u ∉ Q → u * u = 1 → ∃ d ∈ Q ⊔ zpowers s, d * s * d⁻¹ = u) :
    ∀ u ∈ Y ⊔ zpowers s, u ∉ Y → u * u = 1 → ∃ c ∈ Y ⊔ zpowers s, c * s * c⁻¹ = u := by
  intro u hu huY hu2
  have hGN : Y ⊔ zpowers s ≤ normalizer (Y : Set X) :=
    sup_le Subgroup.le_normalizer (zpowers_le.mpr hYs)
  have hDG : Q ⊔ zpowers s ≤ Y ⊔ zpowers s := sup_le_sup_right hQY _
  obtain ⟨c, hc, hcu⟩ := exists_conj_into hs2 hsY hYs hQY hQ2 hsQ hQmax
    (B := zpowers u) (zpowers_le.mpr hu) (isPGroup_zpowers_two hu2)
  have hv : c * u * c⁻¹ ∈ Q ⊔ zpowers s := hcu u (mem_zpowers u)
  have hvQ : c * u * c⁻¹ ∉ Q := fun h =>
    huY ((mem_normalizer_iff.mp (hGN hc) u).mpr (hQY h))
  have hv2 : (c * u * c⁻¹) * (c * u * c⁻¹) = 1 := by
    calc (c * u * c⁻¹) * (c * u * c⁻¹) = c * (u * u) * c⁻¹ := by group
      _ = 1 := by rw [hu2]; group
  obtain ⟨d, hd, hds⟩ := hB _ hv hvQ hv2
  refine ⟨c⁻¹ * d, mul_mem (inv_mem hc) (hDG hd), ?_⟩
  calc c⁻¹ * d * s * (c⁻¹ * d)⁻¹ = c⁻¹ * (d * s * d⁻¹) * c := by group
    _ = u := by rw [hds]; group

theorem kernel_two_bound {Y Q : Subgroup X} {s t : X}
    (hs2 : s * s = 1) (hsY : s ∉ Y) (hYs : s ∈ normalizer (Y : Set X))
    (hQY : Q ≤ Y) (hQ2 : IsPGroup 2 Q) (hsQ : s ∈ normalizer (Q : Set X))
    (hQmax : ∀ P : Subgroup X, P ≤ Y → IsPGroup 2 P → Nat.card P ≤ Nat.card Q)
    (hB : ∀ u ∈ Q ⊔ zpowers s, u ∉ Q → u * u = 1 → ∃ d ∈ Q ⊔ zpowers s, d * s * d⁻¹ = u)
    (ht2 : t * t = 1) (hR : Q ⊓ centralizer ({s} : Set X) ≤ zpowers t)
    {R : Subgroup X} (hRY : R ≤ Y) (hRs : R ≤ centralizer ({s} : Set X)) (hR2 : IsPGroup 2 R) :
    Nat.card R ≤ 2 := by
  have hGN : Y ⊔ zpowers s ≤ normalizer (Y : Set X) :=
    sup_le Subgroup.le_normalizer (zpowers_le.mpr hYs)
  have hDN : Q ⊔ zpowers s ≤ normalizer (Q : Set X) :=
    sup_le Subgroup.le_normalizer (zpowers_le.mpr hsQ)
  have hB2 : IsPGroup 2 (R ⊔ zpowers s : Subgroup X) :=
    isPGroup_sup_zpowers_two hR2 (isPGroup_zpowers_two hs2) hRs
  have hBG : R ⊔ zpowers s ≤ Y ⊔ zpowers s := sup_le_sup_right hRY _
  obtain ⟨c, hc, hcB⟩ := exists_conj_into hs2 hsY hYs hQY hQ2 hsQ hQmax hBG hB2
  have hs' : c * s * c⁻¹ ∈ Q ⊔ zpowers s :=
    hcB s (mem_sup_right (mem_zpowers s))
  have hs'Q : c * s * c⁻¹ ∉ Q := fun h =>
    hsY ((mem_normalizer_iff.mp (hGN hc) s).mpr (hQY h))
  have hs'2 : (c * s * c⁻¹) * (c * s * c⁻¹) = 1 := by
    calc (c * s * c⁻¹) * (c * s * c⁻¹) = c * (s * s) * c⁻¹ := by group
      _ = 1 := by rw [hs2]; group
  obtain ⟨d, hd, hds⟩ := hB _ hs' hs'Q hs'2
  set e : X := d⁻¹ * c with he
  have hes : e * s * e⁻¹ = s := by
    calc e * s * e⁻¹ = d⁻¹ * (c * s * c⁻¹) * d := by rw [he]; group
      _ = d⁻¹ * (d * s * d⁻¹) * d := by rw [hds]
      _ = s := by group
  have hmap : ∀ x ∈ R, e * x * e⁻¹ ∈ zpowers t := by
    intro x hx
    have hxY : x ∈ Y := hRY hx
    have hcxD : c * x * c⁻¹ ∈ Q ⊔ zpowers s := hcB x (mem_sup_left hx)
    have hcxY : c * x * c⁻¹ ∈ Y := (mem_normalizer_iff.mp (hGN hc) x).mp hxY
    have hcxQ : c * x * c⁻¹ ∈ Q := by
      rcases (mem_sup_zpowers_iff hs2 hsQ _).mp hcxD with h | h
      · exact h
      · exfalso
        apply hsY
        have := Y.mul_mem (Y.inv_mem hcxY) (hQY h)
        rwa [inv_mul_cancel_left] at this
    have hexQ : e * x * e⁻¹ ∈ Q := by
      have := (mem_normalizer_iff.mp (hDN (inv_mem hd)) _).mp hcxQ
      rw [he]
      simpa [mul_assoc] using this
    have hxs : x * s = s * x := mem_centralizer_singleton_iff.mp (hRs hx)
    have hcomm : (e * x * e⁻¹) * s = s * (e * x * e⁻¹) := by
      calc (e * x * e⁻¹) * s = (e * x * e⁻¹) * (e * s * e⁻¹) := by rw [hes]
        _ = e * (x * s) * e⁻¹ := by group
        _ = e * (s * x) * e⁻¹ := by rw [hxs]
        _ = (e * s * e⁻¹) * (e * x * e⁻¹) := by group
        _ = s * (e * x * e⁻¹) := by rw [hes]
    exact hR ⟨hexQ, mem_centralizer_singleton_iff.mpr hcomm⟩
  let f : R → zpowers t := fun x => ⟨e * x * e⁻¹, hmap x x.2⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have h1 : e * (x : X) * e⁻¹ = e * (y : X) * e⁻¹ := congrArg Subtype.val hxy
    apply Subtype.ext
    simpa using h1
  calc Nat.card R ≤ Nat.card (zpowers t) := Nat.card_le_card_of_injective f hf
    _ = orderOf t := Nat.card_zpowers t
    _ ≤ 2 := Nat.le_of_dvd two_pos (orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact ht2))

section Dihedral

open CFSG.ClassicalInvolution

private theorem conj_zpow_formula {S : Type} [Group S] {r a : S} {ε : ℤ} (hr2 : r * r = 1)
    (hra : r * a * r = a ^ ε) (k : ℤ) :
    a ^ k * r * (a ^ k)⁻¹ = a ^ (k + ε * (-k)) * r := by
  have hri : r⁻¹ = r := inv_eq_of_mul_eq_one_right hr2
  have h1 : r * a ^ (-k) * r = a ^ (ε * (-k)) := by
    calc r * a ^ (-k) * r = (r * a * r⁻¹) ^ (-k) := by rw [conj_zpow, hri]
      _ = (a ^ ε) ^ (-k) := by rw [hri, hra]
      _ = a ^ (ε * (-k)) := by rw [← zpow_mul]
  calc a ^ k * r * (a ^ k)⁻¹ = a ^ k * (r * a ^ (-k) * r) * r⁻¹ := by rw [zpow_neg]; group
    _ = a ^ k * a ^ (ε * (-k)) * r := by rw [h1, hri]
    _ = a ^ (k + ε * (-k)) * r := by rw [zpow_add]

private theorem exists_conj_exp {S : Type} [Group S] {r a : S} {m' : ℕ}
    (ha : orderOf a = 2 ^ (m' + 2)) (hrel : r * a * r = a⁻¹ ∨
      (1 ≤ m' ∧ r * a * r = a ^ (2 ^ (m' + 1) - 1))) (i' : ℤ) :
    ∃ (ε : ℤ), r * a * r = a ^ ε ∧ ∃ k : ℤ, a ^ (k + ε * (-k)) = a ^ (2 * i') := by
  rcases hrel with hrel | ⟨hm1, hrel⟩
  · refine ⟨-1, by rw [hrel, zpow_neg_one], i', ?_⟩
    ring_nf
  · have e1 : ((2 ^ (m' + 1) - 1 : ℕ) : ℤ) = 2 ^ (m' + 1) - 1 := by
      have := Nat.one_le_two_pow (n := m' + 1)
      push_cast [Nat.cast_sub this]
      ring
    refine ⟨2 ^ (m' + 1) - 1, by rw [hrel, ← e1, zpow_natCast], i' * (1 + 2 ^ m'), ?_⟩
    rw [zpow_eq_zpow_iff_modEq, ha, Int.modEq_iff_dvd]
    obtain ⟨n, rfl⟩ : ∃ n, m' = n + 1 := ⟨m' - 1, by omega⟩
    refine ⟨i' * 2 ^ n, ?_⟩
    push_cast
    ring

private theorem mul_mem_of_index_two {S : Type} [Group S] {H : Subgroup S} (hidx : H.index = 2)
    {x w : S} (hx : x ∉ H) (hw : w ∉ H) : x * w ∈ H := by
  obtain ⟨c, hc⟩ := Subgroup.index_eq_two_iff.mp hidx
  have key : ∀ b : S, b ∉ H → b * c ∈ H := by
    intro b hb
    rcases hc b with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact h1
    · exact absurd h1 hb
  have hw' : w⁻¹ ∉ H := fun h' => hw (by simpa using H.inv_mem h')
  have := H.mul_mem (key x hx) (H.inv_mem (key w⁻¹ hw'))
  simpa [mul_assoc] using this

private theorem dihedral_aux {S : Type} [Group S] [Finite S] {r z : S}
    (h : FourCentralizer S r z) {Q' : Subgroup S} (hidx : Q'.index = 2) (hrQ : r ∉ Q')
    (hzQ : z ∈ Q') {y : S} (hyQ : y ∈ Q') (hy2 : y * y = 1) (hy1 : y ≠ 1) (hyz : y ≠ z) :
    ∀ u : S, u ∉ Q' → u * u = 1 → ∃ d : S, d * r * d⁻¹ = u := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxor : ∀ x w : S, x ∉ Q' → w ∉ Q' → x * w ∈ Q' := fun x w => mul_mem_of_index_two hidx
  have hcardS : Nat.card S = 2 * Nat.card Q' := by
    have := Subgroup.card_mul_index Q'
    rw [hidx] at this
    omega
  have h3 : 3 ≤ Nat.card Q' := by
    have hsub : ({1, z, y} : Set S) ⊆ (Q' : Set S) := by
      intro x hx
      rcases hx with rfl | rfl | rfl
      · exact Q'.one_mem
      · exact hzQ
      · exact hyQ
    have h3' : ({1, z, y} : Set S).ncard = 3 :=
      Set.ncard_eq_three.mpr ⟨1, z, y, h.z_ne.symm, hy1.symm, hyz.symm, rfl⟩
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [h3'] at this
    exact this
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := 2)).mp h.two
  have hm3 : 3 ≤ m := by
    by_contra hlt
    push Not at hlt
    have : 2 ^ m ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨a, ha, hr⟩ := FourCentralizer.exists_cyclic_index_two m hm3 S r z h hm
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 3 := ⟨m - 3, by omega⟩
  have ha' : orderOf a = 2 ^ (m' + 2) := by simpa using ha
  obtain ⟨hz, hrel, hcover⟩ := h.cyclic_structure hm ha' hr
  have haQ : a ∉ Q' := by
    intro haQ
    have hle : zpowers a ≤ Q' := zpowers_le.mpr haQ
    have hcz : Nat.card (zpowers a) = 2 ^ (m' + 2) := by rw [Nat.card_zpowers, ha']
    have hcQ : Nat.card Q' = 2 ^ (m' + 2) := by
      have h1 : 2 ^ (m' + 3) = 2 * Nat.card Q' := by rw [← hm, hcardS]
      have h2 : 2 ^ (m' + 3) = 2 * 2 ^ (m' + 2) := by ring
      omega
    have heq : zpowers a = Q' := Subgroup.eq_of_le_of_card_ge hle (by rw [hcz, hcQ])
    have hyA : y ∈ zpowers a := heq ▸ hyQ
    rcases FourCentralizer.eq_one_or_eq_of_mul_self_eq_one_of_mem_zpowers (m' := m' + 1) ha' hyA
      hy2 with h1 | h1
    · exact hy1 h1
    · exact hyz (h1.trans hz.symm)
  have hodd : ∀ i : ℤ, a ^ i ∈ Q' → 2 ∣ i := by
    intro i hi
    by_contra hodd
    obtain ⟨j, hj⟩ : ∃ j : ℤ, i = 2 * j + 1 := ⟨i / 2, by omega⟩
    have haa : a * a ∈ Q' := hxor a a haQ haQ
    have e : a ^ i = (a * a) ^ j * a := by
      rw [hj, zpow_add, zpow_one, zpow_mul, zpow_two]
    apply haQ
    have h1 : ((a * a) ^ j)⁻¹ * a ^ i ∈ Q' :=
      Q'.mul_mem (Q'.inv_mem (Q'.zpow_mem haa j)) hi
    rwa [e, inv_mul_cancel_left] at h1
  intro u hu hu2
  rcases hcover u with huA | huA
  · exfalso
    rcases FourCentralizer.eq_one_or_eq_of_mul_self_eq_one_of_mem_zpowers (m' := m' + 1) ha' huA
      hu2 with h1 | h1
    · exact hu (h1 ▸ Q'.one_mem)
    · exact hu (by rw [h1, ← hz]; exact hzQ)
  · obtain ⟨i, hi⟩ := mem_zpowers_iff.mp huA
    have huQ : u * r ∈ Q' := hxor u r hu hrQ
    obtain ⟨i', rfl⟩ : 2 ∣ i := hodd i (hi ▸ huQ)
    have hu_eq : u = a ^ (2 * i') * r := by
      rw [hi, mul_assoc, h.r_sq, mul_one]
    obtain ⟨ε, hε, k, hk⟩ := exists_conj_exp ha' hrel i'
    refine ⟨a ^ k, ?_⟩
    rw [conj_zpow_formula h.r_sq hε k, hk, ← hu_eq]

private theorem fourCentralizer_sup {Q : Subgroup X} {s t : X}
    (hQ2 : IsPGroup 2 Q) (hsQ : s ∉ Q) (hsN : s ∈ normalizer (Q : Set X)) (hs2 : s * s = 1)
    (htQ : t ∈ Q) (ht2 : t * t = 1) (ht1 : t ≠ 1)
    (htc : ∀ q ∈ Q, q * t = t * q) (hts : s * t = t * s)
    (hR : Q ⊓ centralizer ({s} : Set X) ≤ zpowers t) :
    FourCentralizer ↥(Q ⊔ zpowers s) ⟨s, mem_sup_right (mem_zpowers s)⟩
      ⟨t, mem_sup_left htQ⟩ := by
  have hmem := mem_sup_zpowers_iff hs2 hsN
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have hcen : ∀ q : X, q ∈ Q → q * s = s * q → q = 1 ∨ q = t := by
    intro q hq hqs
    have : q ∈ zpowers t := hR ⟨hq, mem_centralizer_singleton_iff.mpr hqs⟩
    exact (FourCentralizer.mem_zpowers_iff_of_mul_self_eq_one ht2 ht1).mp this
  refine ⟨hQ2.to_sup_of_normal_left' (isPGroup_zpowers_two hs2) (zpowers_le.mpr hsN),
    Subtype.ext hs2, ?_, Subtype.ext ht2, ?_, ?_, ?_, ?_⟩
  · intro h1
    apply hsQ
    have : s = 1 := congrArg Subtype.val h1
    rw [this]
    exact Q.one_mem
  · intro h1
    exact ht1 (congrArg Subtype.val h1)
  · intro h1
    apply hsQ
    have : s = t := congrArg Subtype.val h1
    rw [this]
    exact htQ
  · intro x
    apply Subtype.ext
    show (x : X) * t = t * x
    rcases (hmem x).mp x.2 with hx | hx
    · exact htc _ hx
    · have h1 := htc _ hx
      apply mul_right_cancel (b := s)
      calc x * t * s = x * (t * s) := by rw [mul_assoc]
        _ = x * (s * t) := by rw [hts]
        _ = x * s * t := by rw [mul_assoc]
        _ = t * (x * s) := h1
        _ = t * x * s := by rw [mul_assoc]
  · intro x
    constructor
    · intro hx
      have hx' : (x : X) * s = s * x := congrArg Subtype.val hx
      rcases (hmem x).mp x.2 with hxQ | hxQ
      · rcases hcen x hxQ hx' with h1 | h1
        · exact Or.inl (Subtype.ext h1)
        · exact Or.inr (Or.inr (Or.inl (Subtype.ext h1)))
      · have hxs : ((x : X) * s) * s = s * ((x : X) * s) := by
          calc (x : X) * s * s = s * x * s := by rw [hx']
            _ = s * (x * s) := by rw [mul_assoc]
        rcases hcen _ hxQ hxs with h1 | h1
        · refine Or.inr (Or.inl (Subtype.ext ?_))
          show (x : X) = s
          calc (x : X) = x * s * s⁻¹ := by group
            _ = s := by rw [h1, hsi, one_mul]
        · refine Or.inr (Or.inr (Or.inr (Subtype.ext ?_)))
          show (x : X) = s * t
          calc (x : X) = x * s * s⁻¹ := by group
            _ = t * s := by rw [h1, hsi]
            _ = s * t := hts.symm
    · rintro (h1 | h1 | h1 | h1)
      · rw [h1]
        simp
      · rw [h1]
      · rw [h1]
        apply Subtype.ext
        show t * s = s * t
        exact hts.symm
      · rw [h1]
        apply Subtype.ext
        show s * t * s = s * (s * t)
        rw [mul_assoc, ← hts]

theorem dihedral_conj {Q : Subgroup X} {s t : X}
    (hQ2 : IsPGroup 2 Q) (hsQ : s ∉ Q) (hsN : s ∈ normalizer (Q : Set X)) (hs2 : s * s = 1)
    (htQ : t ∈ Q) (ht2 : t * t = 1) (ht1 : t ≠ 1)
    (htc : ∀ q ∈ Q, q * t = t * q) (hts : s * t = t * s)
    (hR : Q ⊓ centralizer ({s} : Set X) ≤ zpowers t)
    (hy : ∃ y ∈ Q, y * y = 1 ∧ y ≠ 1 ∧ y ≠ t) :
    ∀ u ∈ Q ⊔ zpowers s, u ∉ Q → u * u = 1 → ∃ d ∈ Q ⊔ zpowers s, d * s * d⁻¹ = u := by
  intro u hu huQ hu2
  obtain ⟨y, hyQ, hy2, hy1, hyt⟩ := hy
  have hF := fourCentralizer_sup hQ2 hsQ hsN hs2 htQ ht2 ht1 htc hts hR
  have hidx : (Q.subgroupOf (Q ⊔ zpowers s)).index = 2 :=
    index_subgroupOf_sup_zpowers hs2 hsN hsQ
  obtain ⟨d, hd⟩ := dihedral_aux hF hidx
    (r := ⟨s, mem_sup_right (mem_zpowers s)⟩) (z := ⟨t, mem_sup_left htQ⟩)
    (by rw [mem_subgroupOf]; exact hsQ) (by rw [mem_subgroupOf]; exact htQ)
    (y := ⟨y, mem_sup_left hyQ⟩) (by rw [mem_subgroupOf]; exact hyQ)
    (Subtype.ext hy2) (fun h => hy1 (congrArg Subtype.val h))
    (fun h => hyt (congrArg Subtype.val h)) ⟨u, hu⟩
    (by rw [mem_subgroupOf]; exact huQ) (Subtype.ext hu2)
  exact ⟨d, d.2, congrArg Subtype.val hd⟩

end Dihedral

end CFSG.ComponentClassification.SolMax.Sig36.E32
