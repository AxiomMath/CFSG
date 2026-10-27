module

public import CFSG.CharacterTheory.Semidihedral.Local.OddSylowCentralizerDichotomySupport
public import CFSG.GroupTheory.BurnsideNormalComplement

public section

namespace CFSG.Semidihedral.Local

open CFSG.Open CFSG.Semidihedral.InvolutionFusion

universe u

theorem eq_of_card_eq_two {X : Type*} [Group X] {P : Subgroup X} (hP : Nat.card P = 2) {a b : X}
    (ha : a ∈ P) (hb : b ∈ P) (ha1 : a ≠ 1) (hb1 : b ≠ 1) : a = b := by
  obtain ⟨y, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : P)).mp hP
  have h1 : (⟨a, ha⟩ : P) = y := huniq _ fun h => ha1 (congrArg Subtype.val h)
  have h2 : (⟨b, hb⟩ : P) = y := huniq _ fun h => hb1 (congrArg Subtype.val h)
  exact congrArg Subtype.val (h1.trans h2.symm)

theorem normalizer_le_centralizer_of_card_eq_two {X : Type*} [Group X] {P : Subgroup X}
    (hP : Nat.card P = 2) : Subgroup.normalizer (P : Set X) ≤ Subgroup.centralizer (P : Set X) := by
  intro g hg
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  by_cases hx1 : x = 1
  · rw [hx1, one_mul, mul_one]
  · have hy : g * x * g⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hg x).mp hx
    have hy1 : g * x * g⁻¹ ≠ 1 := fun h => hx1 (by
      rw [mul_inv_eq_one, mul_eq_left] at h
      exact h)
    have h := eq_of_card_eq_two hP hy hx hy1 hx1
    calc x * g = (g * x * g⁻¹) * g := by rw [h]
      _ = g * x := by group

section Setting

variable {Q : Type u} [Group Q] [Finite Q]

omit [Finite Q] in
theorem eq_bot_of_normal_odd (hcore : CFSG.pPrimeCore 2 Q = ⊥) {K : Subgroup Q} (hK : K.Normal)
    (hodd : Odd (Nat.card K)) : K = ⊥ := by
  rw [eq_bot_iff, ← hcore]
  exact le_sSup ⟨hK, Nat.coprime_two_left.mpr hodd⟩

theorem exists_involution_of_normal (hcore : CFSG.pPrimeCore 2 Q = ⊥) {K : Subgroup Q}
    (hK : K.Normal) (hK1 : K ≠ ⊥) : ∃ k ∈ K, orderOf k = 2 := by
  have heven : 2 ∣ Nat.card K := by
    by_contra h
    exact hK1 (eq_bot_of_normal_odd hcore hK (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h)))
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := K) 2 heven
  exact ⟨x, x.2, by rw [Subgroup.orderOf_coe, hx]⟩

variable (hQ2 : ∀ U : Subgroup Q, U.index ≠ 2) {n : ℕ} (hn : 4 ≤ n) (SQ : Sylow 2 Q)
  (fQ : SemidihedralGroup n ≃* SQ)

include hQ2 hn SQ fQ in
theorem involution_mem_of_normal {L : Subgroup Q} (hL : L.Normal) {v : Q} (hvL : v ∈ L)
    (hv : orderOf v = 2) {u : Q} (hu : orderOf u = 2) : u ∈ L := by
  have h1 := ambient_involution_isConj_z n hn SQ fQ hQ2 u hu
  have h2 := ambient_involution_isConj_z n hn SQ fQ hQ2 v hv
  obtain ⟨g, hg⟩ := isConj_iff.mp (h2.trans h1.symm)
  rw [← hg]
  exact hL.conj_mem v hvL g

include fQ hn in
theorem factorization_two_card_quotient : (Nat.card Q).factorization 2 = n :=
  factorization_two_card_eq hn SQ fQ

include hQ2 hn SQ fQ in
theorem dvd_card_of_involution_mem {L : Subgroup Q} (hL : L.Normal) {v : Q} (hvL : v ∈ L)
    (hv : orderOf v = 2) : 2 ^ (n - 1) ∣ Nat.card L := by
  have hinv : ∀ x : SemidihedralGroup n, orderOf x = 2 → ((fQ x : SQ) : Q) ∈ L := by
    intro x hx
    refine involution_mem_of_normal hQ2 hn SQ fQ hL hvL hv ?_
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hx]
  have hs : orderOf (s n) = 2 := orderOf_s n (by omega)
  have hrs : orderOf (r n ^ 2 * s n) = 2 := by
    have hhalf : 1 < half n := by
      rw [half]
      calc 1 < 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (n - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    refine (involution_iff n (by omega) _).mpr (Or.inr ⟨⟨1, hhalf⟩, ?_⟩)
    simp
  have hr2 : ((fQ (r n ^ 2) : SQ) : Q) ∈ L := by
    have h1 := L.mul_mem (hinv _ hrs) (L.inv_mem (hinv _ hs))
    rwa [← Subgroup.coe_inv, ← Subgroup.coe_mul, ← map_inv, ← map_mul, mul_inv_cancel_right] at h1
  have hD : (dihedralSubgroup n).map ((SQ : Subgroup Q).subtype.comp fQ.toMonoidHom) ≤ L := by
    rw [dihedralSubgroup, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨x, hx, rfl⟩
    rcases hx with rfl | rfl
    · exact hr2
    · exact hinv _ hs
  have hcard : Nat.card ((dihedralSubgroup n).map ((SQ : Subgroup Q).subtype.comp
      fQ.toMonoidHom)) = 2 ^ (n - 1) := by
    have hinjD : Function.Injective ((SQ : Subgroup Q).subtype.comp fQ.toMonoidHom) :=
      fun a b h => fQ.injective (Subtype.ext h)
    rw [Subgroup.card_map_of_injective hinjD, dihedralSubgroup_card n hn, modulus]
  rw [← hcard]
  exact Subgroup.card_dvd_of_le hD

include hQ2 hn SQ fQ in
theorem odd_index_of_involution_mem {L : Subgroup Q} (hL : L.Normal) {v : Q} (hvL : v ∈ L)
    (hv : orderOf v = 2) : Odd L.index := by
  have hdvd := dvd_card_of_involution_mem hQ2 hn SQ fQ hL hvL hv
  have hQn := factorization_two_card_quotient hn SQ fQ
  have hL0 : Nat.card L ≠ 0 := Nat.card_pos.ne'
  have hi0 : L.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hfac : (Nat.card L).factorization 2 + L.index.factorization 2 = n := by
    rw [← Finsupp.add_apply, ← Nat.factorization_mul hL0 hi0, L.card_mul_index, hQn]
  have hge : n - 1 ≤ (Nat.card L).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hL0).mp hdvd
  by_contra heven
  rw [Nat.not_odd_iff_even] at heven
  have hi1 : 1 ≤ L.index.factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hi0).mp
      (by rw [pow_one]; exact even_iff_two_dvd.mp heven)
  have hi : L.index.factorization 2 = 1 := by omega
  have hL' : L.Normal := hL
  obtain ⟨P⟩ : Nonempty (Sylow 2 (Q ⧸ L)) := inferInstance
  have hP : Nat.card P = 2 := by
    rw [Sylow.card_eq_multiplicity, ← Subgroup.index_eq_card, hi, pow_one]
  obtain ⟨K, _, -, hKidx, -⟩ :=
    CFSG.GroupTheory.burnside_normal_complement P (normalizer_le_centralizer_of_card_eq_two hP)
  apply hQ2 (K.comap (QuotientGroup.mk' L))
  rw [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective L), hKidx, hP]

omit [Finite Q] in
theorem le_of_isPGroup_of_odd_index {L : Subgroup Q} [L.Normal] (hodd : Odd L.index)
    {P : Subgroup Q} (hP : IsPGroup 2 P) : P ≤ L := by
  have hmap := hP.map (QuotientGroup.mk' L)
  rcases hmap.card_eq_or_dvd with h1 | h2
  · have hbot : P.map (QuotientGroup.mk' L) = ⊥ := Subgroup.card_eq_one.mp h1
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
    exact hbot
  · exfalso
    have h3 : 2 ∣ L.index := by
      rw [Subgroup.index_eq_card]
      exact h2.trans (Subgroup.card_subgroup_dvd_card _)
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h3)

theorem factorization_two_card_of_odd_index {L : Subgroup Q} (hodd : Odd L.index) :
    (Nat.card L).factorization 2 = (Nat.card Q).factorization 2 := by
  rw [← L.card_mul_index, Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite,
    Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd
      (fun h => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)), add_zero]

@[expose] noncomputable def sylowOfOddIndex {L : Subgroup Q} (hodd : Odd L.index) (T : Sylow 2 Q)
    (hT : (T : Subgroup Q) ≤ L) : Sylow 2 L :=
  Sylow.ofCard ((T : Subgroup Q).subgroupOf L) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT).toEquiv, Sylow.card_eq_multiplicity,
      factorization_two_card_of_odd_index hodd])

theorem coe_sylowOfOddIndex {L : Subgroup Q} (hodd : Odd L.index) (T : Sylow 2 Q)
    (hT : (T : Subgroup Q) ≤ L) :
    (sylowOfOddIndex hodd T hT : Subgroup L) = (T : Subgroup Q).subgroupOf L :=
  Sylow.coe_ofCard _ _

include hQ2 hn SQ fQ in
theorem isSimpleGroup_of_minimal_normal (hcore : CFSG.pPrimeCore 2 Q = ⊥) {L : Subgroup Q}
    (hL : L.Normal) (hL1 : L ≠ ⊥) (hmin : ∀ K : Subgroup Q, K.Normal → K ≤ L → K = ⊥ ∨ K = L) :
    IsSimpleGroup L := by
  obtain ⟨v, hvL, hv⟩ := exists_involution_of_normal hcore hL hL1
  have hodd := odd_index_of_involution_mem hQ2 hn SQ fQ hL hvL hv
  have : Nontrivial L := (Subgroup.nontrivial_iff_ne_bot L).mpr hL1
  refine ⟨fun K hK => ?_⟩
  by_cases hK1 : K = ⊥
  · exact Or.inl hK1
  right
  have heven : 2 ∣ Nat.card K := by
    by_contra h
    have hKodd : Odd (Nat.card K) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h)
    have hle : K ≤ CFSG.pPrimeCore 2 L := le_sSup ⟨hK, Nat.coprime_two_left.mpr hKodd⟩
    have hcoreL : (CFSG.pPrimeCore 2 L).map L.subtype = ⊥ := by
      refine eq_bot_of_normal_odd hcore ConjAct.normal_of_characteristic_of_normal ?_
      rw [Subgroup.card_map_of_injective L.subtype_injective]
      exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := L))
    apply hK1
    rw [eq_bot_iff]
    intro x hx
    have h1 : (x : Q) ∈ (CFSG.pPrimeCore 2 L).map L.subtype := Subgroup.mem_map_of_mem _ (hle hx)
    rw [hcoreL, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.mpr (Subtype.ext h1)
  obtain ⟨k0, hk0⟩ := exists_prime_orderOf_dvd_card' (G := K) 2 heven
  have hk : orderOf (k0 : L) = 2 := by rw [Subgroup.orderOf_coe, hk0]
  have hall : ∀ u : Q, orderOf u = 2 → u ∈ K.map L.subtype := by
    intro u hu
    obtain ⟨Su, fu, hfu⟩ := exists_centered_semidihedral_sylow n hn SQ fQ hQ2 u hu
    have hSuL : (Su : Subgroup Q) ≤ L := le_of_isPGroup_of_odd_index hodd Su.isPGroup'
    have hk2 : IsPGroup 2 (Subgroup.zpowers (k0 : L)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hk, pow_one])
    obtain ⟨y, hky⟩ := exists_ambient_conjugate_mem_sylow (sylowOfOddIndex hodd Su hSuL) _ hk2
    obtain ⟨g, hg⟩ := isConj_iff.mp hky
    have hyK : (y : L) ∈ K := by
      rw [← hg]
      exact hK.conj_mem _ k0.2 g
    have hy1 : (y : L) ≠ 1 := by
      intro h
      rw [h, mul_inv_eq_one, mul_eq_left] at hg
      rw [hg, orderOf_one] at hk
      exact absurd hk (by norm_num)
    have hySu : ((y : L) : Q) ∈ (Su : Subgroup Q) := by
      have h1 : (y : L) ∈ (sylowOfOddIndex hodd Su hSuL : Subgroup L) := y.2
      rw [coe_sylowOfOddIndex] at h1
      exact h1
    have hMn : ((K.map L.subtype).subgroupOf (Su : Subgroup Q)).Normal := by
      constructor
      intro x hx s
      obtain ⟨k', hk', hk'x⟩ := hx
      refine ⟨⟨(s : Q), hSuL s.2⟩ * k' * ⟨(s : Q), hSuL s.2⟩⁻¹, hK.conj_mem k' hk' _, ?_⟩
      change (s : Q) * (k' : Q) * (s : Q)⁻¹ = (s : Q) * (x : Q) * (s : Q)⁻¹
      rw [show (k' : Q) = (x : Q) from hk'x]
    have hM1 : (K.map L.subtype).subgroupOf (Su : Subgroup Q) ≠ ⊥ := by
      intro h
      have hmem : (⟨((y : L) : Q), hySu⟩ : Su) ∈ (K.map L.subtype).subgroupOf (Su : Subgroup Q) :=
        ⟨(y : L), hyK, rfl⟩
      rw [h, Subgroup.mem_bot] at hmem
      have h2 : ((y : L) : Q) = 1 := congrArg (fun a : Su => (a : Q)) hmem
      exact hy1 (Subtype.ext h2)
    have hnil : Group.IsNilpotent Su := Su.isPGroup'.isNilpotent
    obtain ⟨w, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
      (Group.IsNilpotent.inf_center_ne_bot_of_normal hM1)
    have hZcard : Nat.card (Subgroup.center Su) = 2 := by
      rw [← Nat.card_congr (Subgroup.centerCongr fu).toEquiv, center_card n hn]
    have hzc : fu (z n) ∈ Subgroup.center Su := by
      rw [Subgroup.mem_center_iff]
      intro x
      obtain ⟨x', rfl⟩ := fu.surjective x
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp (z_mem_center n hn) x']
    have hz1 : fu (z n) ≠ 1 := fun h =>
      z_ne_one n (by omega) (fu.injective (h.trans (map_one fu).symm))
    have hweq : (w : Su) = fu (z n) :=
      eq_of_card_eq_two hZcard w.2.2 hzc (fun h => hw1 (Subtype.ext h)) hz1
    have hwM := w.2.1
    rw [hweq] at hwM
    rw [← hfu]
    exact hwM
  have hcoreK : (K.map L.subtype).normalCore = L := by
    rcases hmin _ (Subgroup.normalCore_normal _)
      ((Subgroup.normalCore_le _).trans (Subgroup.map_subtype_le K)) with h | h
    · exfalso
      have hv' : v ∈ (K.map L.subtype).normalCore := fun b =>
        hall _ (by rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hv])
      rw [h, Subgroup.mem_bot] at hv'
      rw [hv', orderOf_one] at hv
      exact absurd hv (by norm_num)
    · exact h
  rw [eq_top_iff]
  intro x _
  have h1 : (x : Q) ∈ (K.map L.subtype).normalCore := by
    rw [hcoreK]
    exact x.2
  obtain ⟨y, hy, hyx⟩ := (Subgroup.normalCore_le _) h1
  rw [← Subtype.ext hyx]
  exact hy

theorem exists_noncomm_of_simple {L : Type*} [Group L] [IsSimpleGroup L]
    (h4 : 4 ∣ Nat.card L) : ∃ a b : L, a * b ≠ b * a := by
  by_contra h
  have hcomm : ∀ a b : L, a * b = b * a := fun a b => not_not.mp fun hab => h ⟨a, b, hab⟩
  let _ : CommGroup L := { (inferInstance : Group L) with mul_comm := hcomm }
  have hp : (Nat.card L).Prime := IsSimpleGroup.prime_card
  rcases hp.eq_one_or_self_of_dvd 4 h4 with h1 | h1
  · norm_num at h1
  · rw [← h1] at hp
    norm_num at hp

include hQ2 hn SQ fQ in
theorem unique_minimal_normal_of_semidihedral (hcore : CFSG.pPrimeCore 2 Q = ⊥) :
    ∃ L : Subgroup Q, (L.Normal ∧ L ≠ ⊥ ∧ ∀ K : Subgroup Q, K.Normal → K ≤ L → K = ⊥ ∨ K = L) ∧
      (∀ L' : Subgroup Q,
        (L'.Normal ∧ L' ≠ ⊥ ∧ ∀ K : Subgroup Q, K.Normal → K ≤ L' → K = ⊥ ∨ K = L') → L' = L) ∧
      IsSimpleGroup L ∧ (∃ a b : L, a * b ≠ b * a) ∧ L.Characteristic ∧ Odd L.index ∧
      Subgroup.centralizer (L : Set Q) = ⊥ ∧
      (∀ T : Sylow 2 L, Nonempty (SemidihedralGroup n ≃* T)) := by
  have htop : (⊤ : Subgroup Q) ≠ ⊥ := by
    intro h
    have h1 := Nat.card_congr (Subgroup.topEquiv (G := Q)).toEquiv
    rw [h, Subgroup.card_bot] at h1
    have h2 := Sylow.card_eq_multiplicity SQ
    rw [← h1, Nat.factorization_one, Finsupp.zero_apply, pow_zero,
      ← Nat.card_congr fQ.toEquiv, card n (by omega)] at h2
    have h3 : 1 < 2 ^ n := Nat.one_lt_two_pow (by omega)
    omega
  obtain ⟨L, ⟨hL, hL1⟩, hLmin⟩ :=
    (Set.toFinite {M : Subgroup Q | M.Normal ∧ M ≠ ⊥}).exists_minimal ⟨⊤, inferInstance, htop⟩
  have hmin : ∀ K : Subgroup Q, K.Normal → K ≤ L → K = ⊥ ∨ K = L := fun K hK hle =>
    (em (K = ⊥)).imp id fun hK1 => le_antisymm hle (hLmin ⟨hK, hK1⟩ hle)
  obtain ⟨v, hvL, hv⟩ := exists_involution_of_normal hcore hL hL1
  have hodd := odd_index_of_involution_mem hQ2 hn SQ fQ hL hvL hv
  have hsimple := isSimpleGroup_of_minimal_normal hQ2 hn SQ fQ hcore hL hL1 hmin
  have hnc : ∃ a b : L, a * b ≠ b * a := by
    refine exists_noncomm_of_simple ((pow_dvd_pow 2 (by omega : 2 ≤ n - 1)).trans ?_)
    exact dvd_card_of_involution_mem hQ2 hn SQ fQ hL hvL hv
  have hC : Subgroup.centralizer (L : Set Q) = ⊥ := by
    have hZ : Subgroup.center L = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center L) with h | h
      · exact h
      · exfalso
        obtain ⟨a, b, hab⟩ := hnc
        have hb : b ∈ Subgroup.center L := by
          rw [h]
          exact Subgroup.mem_top b
        exact hab (Subgroup.mem_center_iff.mp hb a)
    have hinf : Subgroup.centralizer (L : Set Q) ⊓ L = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨hxC, hxL⟩
      have hx : (⟨x, hxL⟩ : L) ∈ Subgroup.center L := Subgroup.mem_center_iff.mpr fun y =>
        Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC y y.2)
      rw [hZ, Subgroup.mem_bot] at hx
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val hx)
    refine eq_bot_of_normal_odd hcore Subgroup.normal_centralizer ?_
    have h1 := Subgroup.relIndex_dvd_index_of_normal L (Subgroup.centralizer (L : Set Q))
    have h2 := Subgroup.relIndex_mul_card L (Subgroup.centralizer (L : Set Q))
    rw [inf_comm, hinf, Subgroup.card_bot, mul_one] at h2
    rw [h2] at h1
    exact Odd.of_dvd_nat hodd h1
  have huniq : ∀ L' : Subgroup Q,
      (L'.Normal ∧ L' ≠ ⊥ ∧ ∀ K : Subgroup Q, K.Normal → K ≤ L' → K = ⊥ ∨ K = L') → L' = L := by
    rintro L' ⟨hL'n, hL'1, hL'min⟩
    by_contra hne
    have hinf : L' ⊓ L = ⊥ := by
      rcases hL'min (L' ⊓ L) (Subgroup.normal_inf_normal _ _) inf_le_left with h | h
      · exact h
      · exfalso
        have hle : L' ≤ L := by
          rw [← h]
          exact inf_le_right
        rcases hmin L' hL'n hle with h' | h'
        · exact hL'1 h'
        · exact hne h'
    have hcomm : ⁅L', L⁆ = ⊥ := le_bot_iff.mp (hinf ▸ Subgroup.commutator_le_inf L' L)
    have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    rw [hC] at hle
    exact hL'1 (le_bot_iff.mp hle)
  have hchar : L.Characteristic := by
    rw [Subgroup.characteristic_iff_map_eq]
    intro φ
    apply huniq
    refine ⟨hL.map _ φ.surjective, fun h => hL1 ?_, fun K hK hKle => ?_⟩
    · rwa [Subgroup.map_eq_bot_iff_of_injective _ φ.injective] at h
    · have hle : K.map φ.symm.toMonoidHom ≤ L := by
        have h1 := Subgroup.map_mono (f := φ.symm.toMonoidHom) hKle
        rwa [CFSG.LocalCores.map_map_symm] at h1
      have hK' : K = (K.map φ.symm.toMonoidHom).map φ.toMonoidHom := by
        have h1 := CFSG.LocalCores.map_map_symm φ.symm K
        rw [MulEquiv.symm_symm] at h1
        exact h1.symm
      rcases hmin _ (hK.map _ φ.symm.surjective) hle with h | h
      · left
        rw [hK', h, Subgroup.map_bot]
      · right
        rw [hK', h]
  have hsyl : ∀ T : Sylow 2 L, Nonempty (SemidihedralGroup n ≃* T) := by
    intro T
    have hcard : Nat.card ((T : Subgroup L).map L.subtype) = 2 ^ (Nat.card Q).factorization 2 := by
      rw [Subgroup.card_map_of_injective L.subtype_injective, Sylow.card_eq_multiplicity,
        factorization_two_card_of_odd_index hodd]
    exact ⟨fQ.trans ((Sylow.equiv SQ (Sylow.ofCard _ hcard)).trans
      ((MulEquiv.subgroupCongr (Sylow.coe_ofCard _ hcard)).trans
        ((T : Subgroup L).equivMapOfInjective L.subtype L.subtype_injective).symm))⟩
  exact ⟨L, ⟨hL, hL1, hmin⟩, huniq, hsimple, hnc, hchar, hodd, hC, hsyl⟩

end Setting

end CFSG.Semidihedral.Local
