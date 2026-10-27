module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19Min
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2pFacts
public import CFSG.Dihedral.Glauberman.DicksonMaxList

public section

open CFSG.QuasithinUnique CFSG.GorensteinWalter
open scoped MatrixGroups

namespace CFSG.QuasithinUnique.Unc25K1

section Cases

variable {K : Type} [Field K] [Finite K] {p : ℕ} [Fact p.Prime]

theorem psl2_subgroup_cases
    (hK : Nat.card K = p) (hp7 : 7 ≤ p) {n m : ℕ} (hm : 3 ≤ m)
    (hn : n = 2 ^ m) (hpn : p = n + 1 ∨ p + 1 = n) (W : Subgroup PSL(2, K))
    (hnW : n ∣ Nat.card W) :
    Nat.card W = n ∨ (n = 8 ∧ Nonempty (↥W ≃* Equiv.Perm (Fin 4))) ∨ W = ⊤ := by
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have hn8 : 8 ≤ n := by
    rw [hn]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have h8n : 8 ∣ n := by
    rw [hn]
    exact (pow_dvd_pow 2 hm : 2 ^ 3 ∣ 2 ^ m)
  have hF : Nat.card K = p ^ 1 := by rw [pow_one]; exact hK
  have hgcd : Nat.gcd 2 (p - 1) = 2 := by
    exact Nat.gcd_eq_left (by obtain ⟨k, hk⟩ := hpodd; exact ⟨k, by omega⟩)
  have hcardW : 0 < Nat.card W := Nat.card_pos
  have hcop : Nat.Coprime n p := by
    rw [hn]
    refine Nat.Coprime.pow_left m ?_
    exact (Nat.coprime_two_left).mpr hpodd
  rcases CFSG.Glauberman.Dickson.dickson_psl2_subgroup_list hF W with
    ⟨m', hm', hcard, hel⟩ | ⟨z, hz, hcard, hcyc⟩ | ⟨z, hz2, hz, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ |
      ⟨m', t, hm1, hm', htm, htq, E, C, hE, hEel, hEcard, hCcyc, hCcard, hdisj, hsup, hfaith, φ,
        hφ, ⟨e⟩⟩ | ⟨m', hm', ⟨e⟩⟩ | ⟨m', hm', ⟨e⟩⟩
  ·
    exfalso
    rw [hcard] at hnW
    have h2 : 2 ∣ n := (dvd_trans (by norm_num : 2 ∣ 8) h8n)
    have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_two (h2.trans hnW))
    exact (Nat.not_even_iff_odd.mpr hpodd) (even_iff_two_dvd.mpr this)
  ·
    exfalso
    have hz0 : 0 < z := hcard ▸ hcardW
    rw [hcard] at hnW
    have h1 := Nat.le_of_dvd hz0 hnW
    simp only [pow_one, hgcd] at hz
    rcases hz with hz | hz
    · have := Nat.le_of_dvd (by omega) hz
      omega
    · have := Nat.le_of_dvd (by omega) hz
      omega
  ·
    left
    have hc : Nat.card W = 2 * z := by
      rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    simp only [pow_one, hgcd] at hz
    have hz' : 2 * z ≤ p + 1 := by
      rcases hz with hz | hz
      · have := Nat.le_of_dvd (by omega) hz; omega
      · have := Nat.le_of_dvd (by omega) hz; omega
    obtain ⟨c, hc'⟩ := hnW
    rw [hc] at hc'
    rcases Nat.lt_or_ge c 2 with hc2 | hc2
    · interval_cases c
      · omega
      · omega
    · have := Nat.mul_le_mul_left n hc2
      omega
  ·
    exfalso
    have hc : Nat.card W = 12 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
      simp [Nat.factorial]
    rw [hc] at hnW
    have := h8n.trans hnW
    omega
  ·
    right; left
    have hc : Nat.card W = 24 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm,
        Fintype.card_fin]
      rfl
    rw [hc] at hnW
    refine ⟨?_, ⟨e⟩⟩
    have hn24 : n ≤ 24 := Nat.le_of_dvd (by norm_num) hnW
    have : n = 8 ∨ n = 16 ∨ n = 24 := by
      obtain ⟨c, hc⟩ := h8n
      have : c ≤ 3 := by omega
      interval_cases c <;> omega
    rcases this with h | h | h
    · exact h
    · rw [h] at hnW; omega
    · rw [h] at hnW
      have h3 : 3 ∣ 2 ^ m := by rw [← hn, h]; norm_num
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
      omega
  ·
    exfalso
    have hc : Nat.card W = 60 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
      simp [Nat.factorial]
    rw [hc] at hnW
    have := h8n.trans hnW
    omega
  ·
    exfalso
    have hm1' : m' = 1 := by omega
    subst hm1'
    have hc : Nat.card W = p * t := by
      rw [Nat.card_congr e.toEquiv, Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod,
        hEcard, hCcard, pow_one]
    rw [hc] at hnW
    have hnt : n ∣ t := hcop.dvd_of_dvd_mul_left hnW
    simp only [pow_one, hgcd] at htq
    have ht0 : 0 < t := hCcard ▸ Nat.card_pos
    have h1 := Nat.le_of_dvd ht0 hnt
    have h2 := Nat.le_of_dvd (by omega) htq
    omega
  ·
    right; right
    have hm1 : m' = 1 := Nat.dvd_one.mp hm'
    subst hm1
    have hodd' : IsOddPrimePower (Nat.card (GaloisField p 1)) :=
      ⟨p, 1, Fact.out, hpodd, le_rfl, by rw [GaloisField.card p 1 one_ne_zero]⟩
    have hodd : IsOddPrimePower (Nat.card K) :=
      ⟨p, 1, Fact.out, hpodd, le_rfl, by rw [hK, pow_one]⟩
    have h1 := psl2_card_formula (GaloisField p 1) hodd'
    have h2 := psl2_card_formula K hodd
    rw [GaloisField.card p 1 one_ne_zero, pow_one] at h1
    rw [hK] at h2
    rw [← Subgroup.card_eq_iff_eq_top]
    rw [Nat.card_congr e.toEquiv]
    exact h1.trans h2.symm
  ·
    exfalso
    have : 2 * m' = 1 := Nat.dvd_one.mp hm'
    omega

end Cases

section Gen

variable {K : Type} [Field K] [Finite K] {p : ℕ} [Fact p.Prime]

theorem exists_central_involution_of_isPGroup {Y : Type} [Group Y] [Finite Y] {D : Subgroup Y}
    (hD : IsPGroup 2 D) (hD1 : D ≠ ⊥) :
    ∃ z ∈ D, z ≠ 1 ∧ z ^ 2 = 1 ∧ ∀ y ∈ D, y * z = z * y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial ↥D := (Subgroup.nontrivial_iff_ne_bot D).mpr hD1
  have := hD.center_nontrivial
  obtain ⟨⟨c, hc⟩, hc1⟩ := exists_ne (1 : ↥(Subgroup.center ↥D))
  have hZ1 : (Subgroup.center ↥D).map D.subtype ≠ ⊥ := by
    intro h
    have : (c : Y) ∈ (Subgroup.center ↥D).map D.subtype := ⟨c, hc, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact hc1 (Subtype.ext (Subtype.ext this))
  have hZ2 : IsPGroup 2 ↥((Subgroup.center ↥D).map D.subtype) :=
    hD.to_le (by intro x ⟨y, _, hy⟩; rw [← hy]; exact y.2)
  obtain ⟨z, hzZ, hz1, hz2⟩ := exists_involution_of_isPGroup_ne_bot hZ2 hZ1
  obtain ⟨c', hc', rfl⟩ := Subgroup.mem_map.mp hzZ
  refine ⟨(c' : Y), c'.2, hz1, hz2, fun y hy => ?_⟩
  have := Subgroup.mem_center_iff.mp hc' ⟨y, hy⟩
  exact congrArg Subtype.val this

theorem dihedral_noncentral {k : ℕ} (hk : 2 ≤ k) :
    ∃ x y : DihedralGroup (2 ^ k), x * x = 1 ∧ x ≠ 1 ∧ x * y ≠ y * x := by
  refine ⟨DihedralGroup.sr 0, DihedralGroup.r 1, DihedralGroup.sr_mul_self _, ?_, ?_⟩
  · rw [DihedralGroup.one_def]
    intro h
    cases h
  · rw [DihedralGroup.sr_mul_r, DihedralGroup.r_mul_sr]
    intro h
    have h1 : (0 + 1 : ZMod (2 ^ k)) = 0 - 1 := by simpa using h
    have h2 : ((2 : ℕ) : ZMod (2 ^ k)) = 0 := by
      push_cast
      linear_combination h1
    rw [ZMod.natCast_eq_zero_iff] at h2
    have h3 := Nat.le_of_dvd (by norm_num) h2
    have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    omega

theorem psl2_gen (hp7 : 7 ≤ p) (hK : Nat.card K = p)
    (hpow : (p % 8 = 1 ∧ ∃ m : ℕ, p = 2 ^ m + 1) ∨ (p % 8 = 7 ∧ ∃ m : ℕ, p + 1 = 2 ^ m))
    {D W : Subgroup PSL(2, K)} (hD : IsSylowTwoOf D ⊤)
    (hW : ∀ a ∈ D, a ≠ 1 → a ^ 2 = 1 → Subgroup.centralizer ({a} : Set PSL(2, K)) ≤ W) :
    W = ⊤ := by
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have hodd : IsOddPrimePower (Nat.card K) := isOddPrimePower_of_card_prime hp7 hK
  obtain ⟨S, hS⟩ := exists_sylow_of_isSylowTwoOf_top hD
  subst hS
  obtain ⟨t₀, s₀, ht₀, -, -, -, ht1, -, -, -⟩ := exists_commuting_involutions_of_sylow hodd S
  have hD1 : (S : Subgroup PSL(2, K)) ≠ ⊥ := fun h => ht1 (by
    have := ht₀
    rw [h] at this
    exact Subgroup.mem_bot.mp this)
  obtain ⟨z, hzD, hz1, hz2, hzc⟩ := exists_central_involution_of_isPGroup hD.isPGroup hD1
  have hzo : orderOf z = 2 := orderOf_eq_prime hz2 hz1
  have hDle : (S : Subgroup PSL(2, K)) ≤ Subgroup.centralizer ({z} : Set PSL(2, K)) := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hzc y hy)
  have hCz : Subgroup.centralizer ({z} : Set PSL(2, K)) = S :=
    hD.eq_of_le hDle le_top (psl2_cent_two hp7 hK hpow z hzo)
  have hDW : (S : Subgroup PSL(2, K)) ≤ W := hCz ▸ hW z hzD hz1 hz2
  obtain ⟨n, m, hm, hn, hpn, hcc⟩ : ∃ n m : ℕ, 3 ≤ m ∧ n = 2 ^ m ∧ (p = n + 1 ∨ p + 1 = n) ∧
      ∀ a : PSL(2, K), orderOf a = 2 →
        Nat.card (Subgroup.centralizer ({a} : Set PSL(2, K))) = n := by
    have hcent := fun (a : PSL(2, K)) (ha : orderOf a = 2) =>
      CFSG.Walter.psl2_centralizer_involution K (p := p) (f := 1) (by rw [hK, pow_one]) hpodd
        one_pos ha
    rcases hpow with ⟨h8, m, hm⟩ | ⟨h8, m, hm⟩
    · refine ⟨2 ^ m, m, ?_, rfl, Or.inl hm, fun a ha => ?_⟩
      · by_contra hlt
        push Not at hlt
        interval_cases m <;> omega
      · obtain ⟨h1, -⟩ := hcent a ha
        simp only [pow_one] at h1
        rw [(h1 (by omega)).1]
        omega
    · refine ⟨2 ^ m, m, ?_, rfl, Or.inr hm, fun a ha => ?_⟩
      · by_contra hlt
        push Not at hlt
        interval_cases m <;> omega
      · obtain ⟨-, h3⟩ := hcent a ha
        simp only [pow_one] at h3
        rw [(h3 (by omega)).1]
        omega
  have hnD : Nat.card (S : Subgroup PSL(2, K)) = n := by
    rw [← hCz]
    exact hcc z hzo
  have hnW : n ∣ Nat.card W := hnD ▸ Subgroup.card_dvd_of_le hDW
  obtain ⟨k, hk1, ⟨eD⟩⟩ := psl2_odd_hasDihedralSylowTwo_model K hodd S
  have hcardD : 2 * 2 ^ k = n := by
    rw [← hnD, Nat.card_congr eD.toEquiv, DihedralGroup.nat_card]
  have hn8 : 8 ≤ n := by
    rw [hn]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hk2 : 2 ≤ k := by
    by_contra hlt
    push Not at hlt
    interval_cases k
    omega
  rcases psl2_subgroup_cases hK hp7 hm hn hpn W hnW with hc | ⟨h8, ⟨eW⟩⟩ | h
  ·
    exfalso
    have hWD : (S : Subgroup PSL(2, K)) = W :=
      Subgroup.eq_of_le_of_card_ge hDW (by rw [hc, hnD])
    obtain ⟨x, y, hx, hx1, hxy⟩ := dihedral_noncentral hk2
    set xa : ↥(S : Subgroup PSL(2, K)) := eD.symm x with hxa
    set ya : ↥(S : Subgroup PSL(2, K)) := eD.symm y with hya
    have hxa2 : (xa : PSL(2, K)) ^ 2 = 1 := by
      have : xa * xa = 1 := by rw [hxa, ← map_mul, hx, map_one]
      rw [pow_two]
      exact congrArg Subtype.val this
    have hxa1 : (xa : PSL(2, K)) ≠ 1 := by
      intro h
      apply hx1
      have : xa = 1 := Subtype.ext h
      simpa [hxa] using this
    have hxao : orderOf (xa : PSL(2, K)) = 2 := orderOf_eq_prime hxa2 hxa1
    have hCa : Subgroup.centralizer ({(xa : PSL(2, K))} : Set PSL(2, K)) ≤ S :=
      (hW _ xa.2 hxa1 hxa2).trans hWD.symm.le
    have hCa' : Subgroup.centralizer ({(xa : PSL(2, K))} : Set PSL(2, K)) = S :=
      Subgroup.eq_of_le_of_card_ge hCa (by rw [hcc _ hxao, hnD])
    have hya' : (ya : PSL(2, K)) ∈ Subgroup.centralizer ({(xa : PSL(2, K))} : Set PSL(2, K)) := by
      rw [hCa']
      exact ya.2
    have := Subgroup.mem_centralizer_singleton_iff.mp hya'
    apply hxy
    have h2 : xa * ya = ya * xa := Subtype.ext this.symm
    have h3 := congrArg eD h2
    simpa [hxa, hya] using h3
  ·
    exfalso
    have hk : k = 2 := by
      have h4 : 2 ^ k = 4 := by omega
      have : 2 ^ k = 2 ^ 2 := by rw [h4]; norm_num
      exact Nat.pow_right_injective (le_refl 2) this
    subst hk
    let xs : Fin 4 → ↥(S : Subgroup PSL(2, K)) := fun i =>
      eD.symm (DihedralGroup.sr ((i : ℕ) : ZMod (2 ^ 2)))
    have hxs_inj : Function.Injective xs := by
      intro i j h
      have h1 := eD.symm.injective h
      have h2 : ((i : ℕ) : ZMod (2 ^ 2)) = ((j : ℕ) : ZMod (2 ^ 2)) := by simpa using h1
      have key : ∀ i j : Fin 4, ((i : ℕ) : ZMod (2 ^ 2)) = ((j : ℕ) : ZMod (2 ^ 2)) → i = j := by
        decide
      exact key i j h2
    have hxs2 : ∀ i, (xs i : PSL(2, K)) ^ 2 = 1 := by
      intro i
      have : xs i * xs i = 1 := by
        show eD.symm _ * eD.symm _ = 1
        rw [← map_mul, DihedralGroup.sr_mul_self, map_one]
      rw [pow_two]
      exact congrArg Subtype.val this
    have hxs1 : ∀ i, (xs i : PSL(2, K)) ≠ 1 := by
      intro i h
      have h1 : xs i = 1 := Subtype.ext h
      have h2 : DihedralGroup.sr ((i : ℕ) : ZMod (2 ^ 2)) = 1 := by
        have := congrArg eD h1
        simpa [xs] using this
      rw [DihedralGroup.one_def] at h2
      cases h2
    let ys : Fin 4 → Equiv.Perm (Fin 4) := fun i =>
      eW ⟨(xs i : PSL(2, K)), hDW (xs i).2⟩
    have hys_inj : Function.Injective ys := by
      intro i j h
      have h1 := eW.injective h
      exact hxs_inj (Subtype.ext (Subtype.mk.inj h1))
    have hys2 : ∀ i, ys i * ys i = 1 := by
      intro i
      show eW _ * eW _ = 1
      rw [← map_mul]
      have : (⟨(xs i : PSL(2, K)), hDW (xs i).2⟩ : ↥W) * ⟨(xs i : PSL(2, K)), hDW (xs i).2⟩ = 1 := by
        apply Subtype.ext
        show (xs i : PSL(2, K)) * (xs i : PSL(2, K)) = 1
        rw [← pow_two]
        exact hxs2 i
      rw [this, map_one]
    have hys1 : ∀ i, ys i ≠ 1 := by
      intro i h
      have h1 := eW.injective (h.trans (map_one eW).symm)
      exact hxs1 i (congrArg Subtype.val h1)
    have hysC : ∀ i, 8 ≤
        (Finset.univ.filter fun ψ : Equiv.Perm (Fin 4) => ψ * ys i = ys i * ψ).card := by
      intro i
      have hCW := hW _ (xs i).2 (hxs1 i) (hxs2 i)
      have hxo : orderOf (xs i : PSL(2, K)) = 2 := orderOf_eq_prime (hxs2 i) (hxs1 i)
      have h8' : Nat.card ↥(Subgroup.centralizer ({(xs i : PSL(2, K))} : Set PSL(2, K))) = 8 := by
        rw [hcc _ hxo]
        exact h8
      let g : ↥(Subgroup.centralizer ({(xs i : PSL(2, K))} : Set PSL(2, K))) →
          ↥(Finset.univ.filter fun ψ : Equiv.Perm (Fin 4) => ψ * ys i = ys i * ψ) := fun y =>
        ⟨eW ⟨(y : PSL(2, K)), hCW y.2⟩, by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          have hy := Subgroup.mem_centralizer_singleton_iff.mp y.2
          show eW _ * eW _ = eW _ * eW _
          rw [← map_mul, ← map_mul]
          congr 1
          exact Subtype.ext hy⟩
      have hg : Function.Injective g := by
        intro y1 y2 h
        have h1 := eW.injective (congrArg Subtype.val h)
        exact Subtype.ext (Subtype.mk.inj h1)
      have := Nat.card_le_card_of_injective g hg
      rw [h8', Nat.card_eq_fintype_card, Fintype.card_coe] at this
      exact this
    have hdec : ∀ φ : Equiv.Perm (Fin 4), φ * φ = 1 → φ ≠ 1 →
        8 ≤ (Finset.univ.filter fun ψ : Equiv.Perm (Fin 4) => ψ * φ = φ * ψ).card →
        φ ∈ ({Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.swap 0 2 * Equiv.swap 1 3,
          Equiv.swap 0 3 * Equiv.swap 1 2} : Finset (Equiv.Perm (Fin 4))) := by decide
    have hcard3 : ({Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.swap 0 2 * Equiv.swap 1 3,
          Equiv.swap 0 3 * Equiv.swap 1 2} : Finset (Equiv.Perm (Fin 4))).card = 3 := by decide
    have hle := Finset.card_le_card_of_injOn ys (s := (Finset.univ : Finset (Fin 4)))
      (t := ({Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.swap 0 2 * Equiv.swap 1 3,
          Equiv.swap 0 3 * Equiv.swap 1 2} : Finset (Equiv.Perm (Fin 4))))
      (fun i _ => hdec (ys i) (hys2 i) (hys1 i) (hysC i)) hys_inj.injOn
    rw [hcard3] at hle
    simp at hle
  · exact h

end Gen

section Transport

theorem isSylowTwoOf_top_of_subgroupOf {X : Type} [Group X] {T H : Subgroup X}
    (hT : IsSylowTwoOf T H) : IsSylowTwoOf (T.subgroupOf H) (⊤ : Subgroup ↥H) := by
  refine ⟨le_top, ?_, ?_⟩
  · have e : ↥(T.subgroupOf H) ≃* ↥T := Subgroup.subgroupOfEquivOfLe hT.1
    exact hT.2.1.of_injective e.toMonoidHom e.injective
  · have h := hT.2.2
    have e : ((T.subgroupOf H).subgroupOf (⊤ : Subgroup ↥H)).index = (T.subgroupOf H).index :=
      Subgroup.index_comap_of_surjective (T.subgroupOf H) (f := (⊤ : Subgroup ↥H).subtype)
        (fun x => ⟨⟨x, Subgroup.mem_top x⟩, rfl⟩)
    rw [e]
    exact h

@[expose] def GenStmt (Y : Type) [Group Y] : Prop :=
  ∀ D W : Subgroup Y, IsSylowTwoOf D ⊤ →
    (∀ a ∈ D, a ≠ 1 → a ^ 2 = 1 → Subgroup.centralizer ({a} : Set Y) ≤ W) → W = ⊤

theorem genStmt_of_mulEquiv {X Y : Type} [Group X] [Group Y] [Finite X] (e : X ≃* Y)
    (h : GenStmt Y) : GenStmt X := by
  have : Finite Y := Finite.of_equiv X e.toEquiv
  intro D W hD hW
  have hD' : IsSylowTwoOf (D.map e.toMonoidHom) ⊤ := isSylowTwoOf_top_map e hD
  have h' := h (D.map e.toMonoidHom) (W.map e.toMonoidHom) hD' (by
    intro a ha ha1 ha2 y hy
    obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
    have hy' : e.symm y ∈ Subgroup.centralizer ({a₀} : Set X) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := Subgroup.mem_centralizer_singleton_iff.mp hy
      apply e.injective
      simpa using this
    have ha01 : a₀ ≠ 1 := fun h1 => ha1 (by simp [h1])
    have ha02 : a₀ ^ 2 = 1 := by
      apply e.injective
      simpa using ha2
    exact ⟨e.symm y, hW a₀ ha₀ ha01 ha02 hy', by simp⟩)
  rw [eq_top_iff]
  intro x _
  have hx : e x ∈ W.map e.toMonoidHom := by rw [h']; exact Subgroup.mem_top _
  obtain ⟨w, hw, hwx⟩ := Subgroup.mem_map.mp hx
  have : w = x := e.injective hwx
  rwa [← this]

end Transport

end CFSG.QuasithinUnique.Unc25K1

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin Unc25K1

theorem l2pGen : L2pGen := by
  intro G _ _ X D hX hD W hW
  have hgen : GenStmt ↥X := by
    rcases hX with ⟨p, hFM, h7, hmodel⟩ | hL32
    · have hp : p.Prime := hFM.1
      have : Fact p.Prime := ⟨hp⟩
      obtain ⟨K, _, _, _, e, hcard, -, -⟩ := K1.psl2_model_data (by omega) hmodel
      have hK : Nat.card K = p := by rw [Nat.card_eq_fintype_card, hcard, pow_one]
      exact genStmt_of_mulEquiv e fun D W hD hW =>
        psl2_gen (by omega) hK (fermat_or_mersenne_pow hFM h7) hD hW
    · obtain ⟨F, _, _, _, e, hq7, -, -⟩ := exists_psl2_seven hL32
      have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
      have hK : Nat.card F = 7 := by rw [Nat.card_eq_fintype_card, hq7]
      exact genStmt_of_mulEquiv e fun D W hD hW =>
        psl2_gen (p := 7) le_rfl hK (Or.inr ⟨by norm_num, 3, by norm_num⟩) hD hW
  have hD' := isSylowTwoOf_top_of_subgroupOf hD
  have hW' : ∀ a ∈ D.subgroupOf X, a ≠ 1 → a ^ 2 = 1 →
      Subgroup.centralizer ({a} : Set ↥X) ≤ W.comap X.subtype := by
    intro a ha ha1 ha2 y hy
    have hy' := Subgroup.mem_centralizer_singleton_iff.mp hy
    have hcomm : (y : G) ∈ X ⊓ Subgroup.centralizer ({(a : G)} : Set G) :=
      ⟨y.2, Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hy')⟩
    exact hW (a : G) (Subgroup.mem_subgroupOf.mp ha) (fun h => ha1 (Subtype.ext h))
      (by simpa using congrArg Subtype.val ha2) hcomm
  have htop := hgen (D.subgroupOf X) (W.comap X.subtype) hD' hW'
  intro x hx
  have : (⟨x, hx⟩ : ↥X) ∈ W.comap X.subtype := by
    rw [htop]
    exact Subgroup.mem_top _
  exact this

theorem part2_2519
    : Part2_2519 := part2_2519_of_inputs l2pFacts l2pGen

end CFSG.QuasithinUnique
